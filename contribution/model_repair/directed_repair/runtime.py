"""Exact rational execution of the frozen core plus the six-ReLU repair block."""
import argparse
from fractions import Fraction as F
import json
from pathlib import Path

from freeze import layers, evaluate, displacement

HERE=Path(__file__).resolve().parent


def block_relu(d,z):
    relu=lambda v:max(F(0),v)
    rmax=lambda a,b:a+relu(b-a)
    rmin=lambda a,b:a-relu(a-b)
    lo=rmin(F(1,2),relu(F(1,2)+64*(d-2)))
    hi=rmax(F(1,2),rmin(F(1),F(1,2)+64*(d+2)))
    return rmax(lo,rmin(hi,z))


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('input',nargs=6,help='Six normalized rational or decimal coordinates')
    args=parser.parse_args()
    xs=list(map(F,args.input))
    if not all(0<=x<=1 for x in xs):parser.error('Inputs must belong to [0,1]^6')
    candidate=json.loads((HERE/'CANDIDATE.json').read_text())
    core=layers(list(map(F,candidate['core_parameters'])),candidate['core_widths'])
    d=displacement(xs);z=evaluate(core,xs);value=block_relu(d,z)
    print(json.dumps({'input':list(map(str,xs)),'physical_displacement':str(d),
                      'core_output':str(z),'repaired_output':str(value),'repaired_approx':float(value),
                      'region':'Above(2)' if d>=2 else 'Below(2)' if d<=-2 else 'gap',
                      'scope':'exact rational reference execution'},indent=2))


if __name__=='__main__':main()
