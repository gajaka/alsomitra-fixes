"""Reproduce the selected fitted core; formal verification uses frozen artifacts."""
from fractions import Fraction as F
import argparse
import hashlib
import json
from pathlib import Path
import re
import sys
import time

import numpy as np
import torch

HERE=Path(__file__).resolve().parent
CONTRIBUTION=HERE.parents[1]
torch.set_num_threads(1)
torch.set_default_dtype(torch.float64)
DX=np.array([0.,0.,0.,0.,41.232296222734604,45.878638794593570])
D0=.482420778264618-41.681405266088724


class Net(torch.nn.Module):
    def __init__(self,flat):
        super().__init__()
        self.layers=torch.nn.ModuleList()
        offset=0
        for ins,outs in [(6,4),(4,2),(2,1)]:
            layer=torch.nn.Linear(ins,outs)
            with torch.no_grad():
                layer.weight.copy_(torch.tensor(flat[offset:offset+ins*outs].reshape(outs,ins)))
                offset+=ins*outs
                layer.bias.copy_(torch.tensor(flat[offset:offset+outs]))
                offset+=outs
            self.layers.append(layer)
        assert offset==len(flat)==41

    def forward(self,x):
        for layer in self.layers:x=torch.relu(layer(x))
        return x[:,0]

    def flat(self):
        return np.concatenate([v for layer in self.layers for v in
                               (layer.weight.detach().numpy().ravel().copy(),
                                layer.bias.detach().numpy().copy())])


def project(z,x):
    d=x@torch.tensor(DX)+D0
    lower=torch.clamp(.5+64*(d-2),0.,.5)
    upper=torch.clamp(.5+64*(d+2),.5,1.)
    return torch.maximum(lower,torch.minimum(upper,z))


def split_units(net):
    with torch.no_grad():
        net.layers[0].weight[3].copy_(net.layers[0].weight[2])
        net.layers[0].bias[3].copy_(net.layers[0].bias[2]+.02)
        net.layers[1].weight[:,3]=0.
        net.layers[1].weight[0].copy_(net.layers[1].weight[1])
        net.layers[1].bias[0].copy_(net.layers[1].bias[1]+.02)
        old=net.layers[2].weight[0,1].clone()
        net.layers[2].weight[0,0]=old/2
        net.layers[2].weight[0,1]=old/2


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path,required=True)
    args=parser.parse_args();args.out.mkdir(parents=True,exist_ok=False)
    source=CONTRIBUTION/'network_reduction/Adversarial.lean'
    line=re.search(r'^def reducedRationals .*$',source.read_text(),re.M).group()
    initial=np.array([float(F(int(a),int(b))) for a,b in
                      re.findall(r'mkRat \((-?\d+)\) (\d+)',line)])
    data_path=HERE.parent/'inputs/Training_Data_Normalised.csv'
    assert hashlib.sha256(data_path.read_bytes()).hexdigest()=='d0b84c0e372a25f7934953ae8adac8db08b7a3b241892a1aa697834f583acbf7'
    a=np.loadtxt(data_path,delimiter=',');x,y=torch.tensor(a[:,:6]),torch.tensor(a[:,6])
    original_mse=float(torch.mean((Net(initial)(x)-y)**2).detach())
    torch.manual_seed(0)
    net=Net(initial);split_units(net)
    opt=torch.optim.Adam(net.parameters(),lr=.002)
    best=(float('inf'),None,-1);log=[];started=time.perf_counter()
    for step in range(16000):
        opt.zero_grad();loss=torch.mean((project(net(x),x)-y)**2)
        loss.backward();opt.step()
        if float(loss.detach())<best[0]:
            with torch.no_grad():score=float(torch.mean((project(net(x),x)-y)**2))
            if score<best[0]:best=(score,net.flat(),step)
        if (step+1)%2000==0:log.append({'step':step+1,'best_mse':best[0]})
        if (step+1)%4000==0:
            for group in opt.param_groups:group['lr']*=.5
    net=Net(best[1])
    opt=torch.optim.LBFGS(net.parameters(),lr=1.,max_iter=1000,tolerance_grad=1e-12,
                          tolerance_change=1e-15,history_size=50,line_search_fn='strong_wolfe')
    def closure():
        opt.zero_grad();loss=torch.mean((project(net(x),x)-y)**2);loss.backward();return loss
    opt.step(closure)
    with torch.no_grad():score=float(torch.mean((project(net(x),x)-y)**2))
    if score<best[0]:best=(score,net.flat(),17000)
    record={'k':64,'widths':[6,4,2,1],'initialization':'split','mse':best[0],
            'original_mse':original_mse,'quality_pass':best[0]<=original_mse,
            'parameters_float64':best[1].tolist(),'step':best[2],
            'max_core_parameter_change':float(np.max(np.abs(best[1]-initial))),
            'seconds':time.perf_counter()-started,'training_log':log,
            'scope':'Numerical fit; verification of a frozen candidate is separate'}
    (args.out/'FIT.json').write_text(json.dumps(record,indent=2)+'\n')
    expected=json.loads((HERE/'CANDIDATE.json').read_text())
    quantized=[str(F(round(F.from_float(v)*65536),65536)) for v in best[1]]
    check={'python':sys.version,'torch':torch.__version__,'numpy':np.__version__,
           'frozen_parameters_match':quantized==expected['core_parameters'],
           'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
           'dataset_sha256':hashlib.sha256(data_path.read_bytes()).hexdigest()}
    (args.out/'REPLAY.json').write_text(json.dumps(check,indent=2)+'\n')
    print(json.dumps({'mse':best[0],**check},indent=2))


if __name__=='__main__':main()
