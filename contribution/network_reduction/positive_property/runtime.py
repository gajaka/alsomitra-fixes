"""Finite execution and descriptive dataset checks, separate from the proof."""
import argparse
from fractions import Fraction as F
import itertools
import json
from pathlib import Path
import platform

import numpy as np
import onnx
import onnxruntime as ort

import extract


def evaluate_exact(layers, point):
    xs = list(map(F,point))
    for j,(w,b) in enumerate(layers):
        xs = [bias+sum(a*x for a,x in zip(row,xs)) for row,bias in zip(w,b)]
        if j<2:
            xs = [max(F(0),x) for x in xs]
    return xs[0]


def session(path):
    options=ort.SessionOptions()
    options.intra_op_num_threads=options.inter_op_num_threads=1
    options.graph_optimization_level=ort.GraphOptimizationLevel.ORT_DISABLE_ALL
    return ort.InferenceSession(str(path),sess_options=options,providers=['CPUExecutionProvider'])


def run(upstream, generated):
    extract.pinned(upstream,extract.DATA,extract.DATA_SHA)
    data=np.loadtxt(upstream/extract.DATA,delimiter=',')
    if data.shape != (360,7) or not np.isfinite(data).all() or data.min()<0 or data.max()>1:
        raise ValueError('Unexpected evaluation data')
    rng=np.random.default_rng(20261106)
    x=rng.integers(1,1024,size=(2048,6)).astype(np.float32)/1024
    y=x+rng.integers(-1,2,size=x.shape).astype(np.float32)/1024
    if np.max(abs(x.astype(float)-y.astype(float))) > .001:
        raise ValueError('Perturbation outside proved radius')
    points=np.concatenate([data[:,:6].astype(np.float32),
        np.array(list(itertools.product([0.,1.],repeat=6)),dtype=np.float32),x,y])
    report={'status':'PASS','scope':'Finite CPU float32 execution and descriptive error on 360 published rows; no held-out/generalization or universal float32 claim',
        'versions':{'numpy':np.__version__,'onnx':onnx.__version__,'onnxruntime':ort.__version__,'platform':platform.platform()},
        'dataset':{'path':extract.DATA,'sha256':extract.DATA_SHA,'rows':360,'columns':7,
                   'holdout_status':'Unknown for these checkpoints; no train/test split is asserted',
                   'normalization':'As stored: six inputs and target in [0,1]; no additional normalization',
                   'best_constant_mse_on_same_rows':float(np.var(data[:,-1]))},
        'points_per_variant':len(points),'paired_perturbations':len(x),'models':{}}
    for name,(filename,digest,cap) in extract.MODELS.items():
        path=upstream/'vehicle_verification/property_verification_2'/filename
        _,layers=extract.inspect_model(path)
        original=session(path); reduced=session(generated/(name+'_reduced.onnx'))
        outputs={}
        for label,s in [('original',original),('reduced',reduced)]:
            # Both batch layouts are tested; neither is assumed bitwise identical.
            batched=s.run(None,{'input':points})[0].ravel()
            single=np.concatenate([s.run(None,{'input':p[None,:]})[0].ravel() for p in points])
            if not np.isfinite(batched).all() or not np.isfinite(single).all():
                raise ValueError('Nonfinite output')
            delta=np.max(abs(batched[-4096:-2048].astype(float)-batched[-2048:].astype(float)))
            if delta>.1:
                raise ValueError('Runtime violation of compared Property5 threshold')
            outputs[label]={'batched':batched,'single':single,'max_pair_change':float(delta)}
        o,r=outputs['original'],outputs['reduced']
        rec={'original_sha256':extract.sha(path),'reduced_sha256':extract.sha(generated/(name+'_reduced.onnx')),
             'mse_360':float(np.mean((o['batched'][:360].astype(float)-data[:,-1])**2)),
             'mae_360':float(np.mean(abs(o['batched'][:360].astype(float)-data[:,-1]))),
             'prediction_range_360':[float(o['batched'][:360].min()),float(o['batched'][:360].max())],
             'finite_original_reduced_comparison':{},'finite_robustness':{},'exact_spot_checks':[]}
        for layout in ['batched','single']:
            a,b=o[layout],r[layout]
            rec['finite_original_reduced_comparison'][layout]={
                'bitwise_different_outputs':int(np.count_nonzero(a.view(np.uint32)!=b.view(np.uint32))),
                'maximum_absolute_difference':float(np.max(abs(a.astype(float)-b.astype(float))))}
        for label,obs in outputs.items():
            rec['finite_robustness'][label]={'maximum_output_change_batched':obs['max_pair_change'],'threshold':.1}
        for point in [[F(0)]*6,[F(1,2)]*6,[F(1)]*6]:
            value=evaluate_exact(extract.rational_layers(layers),point)
            approx=float(original.run(None,{'input':np.array([point],dtype=np.float32)})[0][0,0])
            diff=abs(F(approx)-value)
            if float(diff)>1e-5:
                raise ValueError('Spot-check execution disagrees with exact model')
            rec['exact_spot_checks'].append({'input':list(map(str,point)),'real_output':str(value),
                'float32_output':approx,'absolute_error_exact':str(diff)})
        report['models'][name]=rec
    return report


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('--upstream',type=Path,required=True)
    p.add_argument('--generated',type=Path,required=True)
    p.add_argument('--output',type=Path,required=True)
    a=p.parse_args()
    result=run(a.upstream,a.generated)
    a.output.write_text(json.dumps(result,indent=2)+'\n')
    print('PASS: finite original/reduced execution and descriptive dataset checks')
