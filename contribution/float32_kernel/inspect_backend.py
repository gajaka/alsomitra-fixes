"""Observe this Mac's BLAS calls in a dedicated child; this is not a proof.

The diagnostic inputs establish dispatch and batch sensitivity, not Property2.
No upstream, system library, weights, or persistent environment is changed.
"""
import hashlib
import json
import os
from pathlib import Path
import platform
import subprocess
import sys

HERE = Path(__file__).resolve().parent
ROOT = HERE.parent
BUILD = ROOT/'.build'
PIN = 'd0f2af8b66b20da4baa50644c0cd3f887a2eae2e'


def probe():
    import torch
    sys.path.insert(0,str(ROOT))
    from torch_bridge import from_words, words
    m = json.loads((ROOT/'universal/model.json').read_text())
    state = {n:from_words(v['words']).reshape(v['shape']) for n,v in m['state'].items()}
    torch.set_num_threads(1)
    for batch in (1,2,128):
        x = torch.full((batch,6),.5,dtype=torch.float32,device='cpu')
        with torch.inference_mode(),torch.autocast('cpu',enabled=False):
            for i in (1,2,3):
                x = torch.nn.functional.linear(x,state[f'fc{i}.weight'],state[f'fc{i}.bias'])
                if i < 3:
                    x = torch.relu(x)
        print(json.dumps(dict(batch=batch,output_bits=words(x))))


def inspect():
    import torch
    if sys.platform != 'darwin' or platform.machine() != 'arm64':
        raise RuntimeError('This observation harness targets the existing Apple arm64 backend')
    if torch.version.git_version != PIN:
        raise RuntimeError('PyTorch differs from the pinned source inspection')
    sources = HERE/'sources'
    manifest = json.loads((sources/'manifest.json').read_text())
    for name,entry in manifest.items():
        if hashlib.sha256((sources/Path(name).name).read_bytes()).hexdigest() != entry['sha256']:
            raise RuntimeError('source checksum mismatch: '+name)
    dylib = BUILD/'trace_sgemm.dylib'
    clang = '/Library/Developer/CommandLineTools/usr/bin/clang'
    sdk = '/Library/Developer/CommandLineTools/SDKs/MacOSX26.5.sdk'
    subprocess.run([clang,'-dynamiclib','-O2','-Wall','-Wextra','-isysroot',sdk,
        str(HERE/'trace_sgemm.c'),'-framework','Accelerate','-o',str(dylib)],check=True,timeout=60)
    env = os.environ.copy()
    env.pop('DYLD_INSERT_LIBRARIES',None)
    plain = subprocess.run([sys.executable,'-B',str(Path(__file__).resolve()),'--probe'],
        env=env,text=True,capture_output=True,check=True,timeout=60)
    env['DYLD_INSERT_LIBRARIES'] = str(dylib)
    observed = subprocess.run([sys.executable,'-B',str(Path(__file__).resolve()),'--probe'],
        env=env,text=True,capture_output=True,check=True,timeout=60)
    if observed.stdout != plain.stdout:
        raise RuntimeError('interposition changed outputs')
    records = [line.split()[1:] for line in observed.stderr.splitlines() if line.startswith('PPG_SGEMM ')]
    images = [line.removeprefix('PPG_SGEMM_IMAGE ') for line in observed.stderr.splitlines()
        if line.startswith('PPG_SGEMM_IMAGE ')]
    if len(records) != 9 or len(images) != 1 or 'Accelerate.framework' not in images[0]:
        raise RuntimeError('unexpected backend trace: '+observed.stderr[:2000])
    for row,shape in zip(records,((64,1,6),(32,1,64),(1,1,32),(64,2,6),(32,2,64),(2,1,32),
                                  (64,128,6),(32,128,64),(128,1,32))):
        if row[:2] != ['T','N'] or tuple(map(int,row[2:5])) != shape or row[-2:] != ['1','1']:
            raise RuntimeError('unexpected SGEMM arguments')
    outputs = [json.loads(line) for line in plain.stdout.splitlines()]
    return dict(status='OBSERVED_NOT_FORMALLY_VERIFIED',torch_version=torch.__version__,
        torch_commit=torch.version.git_version,torch_build=torch.__config__.show(),
        platform=platform.platform(),threads=1,input='all six coordinates 0.5, diagnostic only',
        runtime_library=images[0],sgemm_arguments=records,
        instrumented_matches_plain=True,outputs=outputs,
        batch_sensitive=outputs[0]['output_bits'][0] != outputs[1]['output_bits'][0],
        sources=manifest,interposer_sha256=hashlib.sha256(dylib.read_bytes()).hexdigest(),
        universal_refinement='NOT_PROVED')


if __name__ == '__main__':
    if sys.argv[1:] == ['--probe']:
        probe()
    else:
        result = inspect()
        path = ROOT/'results/float32_backend_observation.json'
        path.write_text(json.dumps(result,indent=2,sort_keys=True)+'\n')
        print('Observed 9 Accelerate SGEMM calls; outputs unchanged by instrumentation')
        print('Batch-sensitive outputs:',result['batch_sensitive'])
