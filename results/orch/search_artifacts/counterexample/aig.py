import argparse
import importlib.util
import json
import subprocess
from pathlib import Path
P=Path('/tmp/oec/pequalnp-pilot-99/counterexample')
sp=importlib.util.spec_from_file_location('synth',P/'synth.py');s=importlib.util.module_from_spec(sp);sp.loader.exec_module(s)
SOLVER=s.SOLVER

def encode(ng,rows):
    f=s.CNF();aa=[];bb=[]
    for j in range(ng):
        aa.append([f.var() for _ in range(2*(10+j))]);f.one(aa[-1])
        bb.append([f.var() for _ in range(2*(10+j))]);f.one(bb[-1])
        for a in range(2*(10+j)):
            for b in range(a+1):f.add(-aa[j][a],-bb[j][b])
    for j in range(ng-1):
        for a in range(2*(10+j)):
            for b in range(a):f.add(-bb[j][a],-bb[j+1][b])
        f.add(*[sel[2*(10+j)+sgn] for k in range(j+1,ng) for sel in [aa[k],bb[k]] for sgn in [0,1]])
    phase=f.var()
    for r in rows:
        vals=[f.var() for _ in range(ng)]
        for j in range(ng):
            a=f.var();b=f.var();v=vals[j]
            for dest,selectors in [(a,aa[j]),(b,bb[j])]:
                for k,sel in enumerate(selectors):
                    wire=k//2;neg=k%2
                    if wire<10:
                        bit=bool(r>>wire&1)^bool(neg);f.add(-sel,dest if bit else -dest)
                    else:
                        lit=vals[wire-10];lit=-lit if neg else lit
                        f.add(-sel,-dest,lit);f.add(-sel,dest,-lit)
            f.add(-v,a);f.add(-v,b);f.add(v,-a,-b)
        v=vals[-1]
        if s.target(r):f.add(v,phase);f.add(-v,-phase)
        else:f.add(-v,phase);f.add(v,-phase)
    return f,aa,bb,phase

def eval_circuit(gs,phase,r):
    w=[bool(r>>i&1) for i in range(10)]
    for a,b in gs:w.append((w[a//2]^bool(a%2)) and (w[b//2]^bool(b%2)))
    return w[-1]^phase

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--gates',type=int,default=17);ap.add_argument('--seconds',type=int,default=60);ap.add_argument('--name',default='');ap.add_argument('--first',default='');ap.add_argument('--retain',default='');ar=ap.parse_args()
    rows=sorted(set([r for r in range(1024) if not s.target(r)]+[(1<<a)|(1<<b) for a,b in s.EDGES]))
    for it in range(10):
        name=P/f'{ar.name or ("aig"+str(ar.gates))}-{it}';f,aa,bb,phase=encode(ar.gates,rows)
        if ar.first:
            fa,fb=map(int,ar.first.split(','));f.add(aa[0][fa]);f.add(bb[0][fb])
        if ar.retain:
            for pin in map(int,ar.retain.split(',')):
                f.add(*[sel[2*pin+sgn] for j in range(1,ar.gates) for sel in [aa[j],bb[j]] for sgn in [0,1]])
        f.save(name.with_suffix('.cnf'))
        name.with_suffix('.meta.json').write_text(json.dumps({'rows':rows,'a':aa,'b':bb,'phase':phase}))
        print('START',ar.gates,it,'vars',f.n,'clauses',len(f.cs),flush=True)
        with name.with_suffix('.stdout').open('w') as out,name.with_suffix('.stderr').open('w') as err:
            run=subprocess.run([SOLVER,'--sat','-t',str(ar.seconds),str(name.with_suffix('.cnf'))],stdout=out,stderr=err)
        print('END',run.returncode,flush=True)
        if run.returncode!=10:return
        model=set()
        for line in name.with_suffix('.stdout').read_text().splitlines():
            if line.startswith('v '):model.update(int(v) for v in line[2:].split() if int(v)>0)
        gs=[(next(k for k,v in enumerate(aa[j]) if v in model),next(k for k,v in enumerate(bb[j]) if v in model)) for j in range(ar.gates)]
        ph=phase in model;bad=[r for r in range(1024) if eval_circuit(gs,ph,r)!=s.target(r)]
        name.with_suffix('.circuit.json').write_text(json.dumps({'gates':gs,'phase':ph,'bad':bad},indent=2))
        print('MODEL',len(bad),'mismatches',flush=True)
        if not bad:print('VERIFIED FREE-COMPLEMENT WITNESS',ar.gates,flush=True);return
        rows=sorted(set(rows+bad))

if __name__=='__main__':main()
