"""Replay the frozen parameters and measure (not universally prove) kernel error."""
from fractions import Fraction as Q
from itertools import product
import importlib.util
import json
from pathlib import Path
import sys

import torch

HERE=Path(__file__).resolve().parent
sys.path.insert(0,str(HERE.parent))
from torch_bridge import (LeanClient,Normalizer,Spec,canonical_hash,demo_model,from_words,
                          guarded_sample,infer_checked,observe,words,exact_word)
from generate import layers_from_manifest, EPS


def run(manifest,upstream):
    torch.set_num_threads(1)
    source=Path(upstream)/'examples/models.py'
    import hashlib
    if hashlib.sha256(source.read_bytes()).hexdigest()!=manifest['original_source_sha256']['examples/models.py']:
        raise ValueError('original model source changed')
    spec_mod=importlib.util.spec_from_file_location('original_universal_replay',source)
    mod=importlib.util.module_from_spec(spec_mod);spec_mod.loader.exec_module(mod)
    with torch.random.fork_rng(devices=[]):
        model=mod.AlsomitraNet().cpu().float().eval()
    state={name:from_words(value['words']).reshape(value['shape']) for name,value in manifest['state'].items()}
    model.load_state_dict(state,strict=True)
    actual={name:dict(shape=list(v.shape),words=words(v)) for name,v in model.state_dict().items()}
    if canonical_hash(actual)!=manifest['state_sha256']:raise ValueError('replay parameter mismatch')
    normalizer=Normalizer(tuple(manifest['normalizer']['offset_bits']),tuple(manifest['normalizer']['scale_bits']))
    spec=Spec(**manifest['spec'])
    generator=torch.Generator().manual_seed(20261105)
    unit=torch.cat((torch.tensor(list(product((0.,1.),repeat=6))),torch.rand((64,6),generator=generator)))
    checks=0
    def require(value,message):
        nonlocal checks
        checks+=1
        if not value:raise AssertionError(message)
    with LeanClient() as client:
        inputs=guarded_sample(client,spec,normalizer,unit)
        with torch.inference_mode(),torch.autocast('cpu',enabled=False):
            a=model.fc1(inputs);b=model.fc2(torch.relu(a));outputs=model.fc3(torch.relu(b))
            forward=model(inputs)
        require(words(forward)==words(outputs),'captured layers reproduce original forward')
        intervals=[]
        for values,observed,params in zip((inputs,torch.relu(a),torch.relu(b)),(a,b,outputs),layers_from_manifest(manifest)):
            largest=Q(0)
            for xs,ys in zip(values,observed):
                exact_x=list(map(exact_word,words(xs)))
                for yw,(ws,bias) in zip(words(ys),params):
                    exact=sum((w*x for w,x in zip(ws,exact_x)),bias)
                    error=abs(exact_word(yw)-exact)
                    largest=max(largest,error)
                    require(error<=EPS,'sampled affine kernel error exceeds certificate budget')
            intervals.append(dict(max_observed_absolute_error=str(largest),decimal=float(largest)))
        observed=observe(client,spec,normalizer,inputs,outputs)
        require(all(row['verdict']=='satisfied' for row in observed),'original network replay violates exact output contract')
        middle=guarded_sample(client,spec,normalizer,torch.full((1,6),.5))
        _,bad=infer_checked(client,spec,normalizer,demo_model(),middle)
        require(bad['payload']['observations'][0]['verdict']=='violated','different demo model must not inherit certificate')
    return dict(assertions=checks,input_count=len(inputs),affine_error_samples=len(inputs)*(64+32+1),
                max_observed_output=float(outputs.max()),min_observed_output=float(outputs.min()),
                per_layer=intervals,kernel_error_evidence='sampled only; NOT a universal PyTorch error proof',
                model_state_sha256=canonical_hash(actual),unrelated_demo_refuted=True)
