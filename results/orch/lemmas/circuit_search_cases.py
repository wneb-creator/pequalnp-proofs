"""Reproduce the initial bounded full-table first-gate SAT experiments."""
import argparse
import itertools
import pathlib
import subprocess
import sys

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--outdir',required=True)
    p.add_argument('--repo',default='/workspace/pequalnp-proofs')
    args=p.parse_args()
    outdir=pathlib.Path(args.outdir);outdir.mkdir(parents=True,exist_ok=True)
    base=outdir/'circuit_search_p19.cnf'
    generator=pathlib.Path(args.repo)/'notes/data/lrat-link/gennot.py'
    with (outdir/'circuit_search_p19_gen.log').open('w') as log:
        subprocess.run([sys.executable,str(generator),'10','19','01,12,23,34,40,05,16,27,38,49,57,79,96,68,85',str(base)],stdout=log,stderr=subprocess.STDOUT,check=True)
    header,body=base.read_text().split('\n',1)
    _,_,nv,nc=header.split();stride=1055
    extras=[[j*stride+4 for j in range(19)]]
    extras.extend([-(j*stride+4) for j in js] for js in itertools.combinations(range(19),4))
    for name,op,b in [('not0',3,0),('and01',0,1),('and02',0,2),('or01',1,1),('or02',1,2)]:
        clauses=extras+[[op+1],[20*stride+1],[40*stride+b+1]]
        out=outdir/('circuit_search_p19_'+name+'.cnf')
        out.write_text(f'p cnf {nv} {int(nc)+len(clauses)}\n'+body+''.join(' '.join(map(str,c))+' 0\n' for c in clauses))
        print(name,'vars',nv,'clauses',int(nc)+len(clauses))

if __name__=='__main__':main()
