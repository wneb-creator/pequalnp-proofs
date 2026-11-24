import argparse
import sys
from pathlib import Path

parser=argparse.ArgumentParser()
parser.add_argument('--z3-python',required=True)
parser.add_argument('input')
parser.add_argument('output')
args=parser.parse_args()
sys.path.insert(0,args.z3_python)
import z3
g=z3.Goal()
g.add(*z3.parse_smt2_file(args.input))
print('input_assertions',len(g),flush=True)
t=z3.Then('simplify','bit-blast','pb2bv','bit-blast','tseitin-cnf')
result=t(g)
assert len(result)==1
print('cnf_assertions',len(result[0]),flush=True)
Path(args.output).write_text(result[0].dimacs())
print('bytes',Path(args.output).stat().st_size,flush=True)
