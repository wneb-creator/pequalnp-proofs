import argparse
import importlib.util
import itertools
import json
import subprocess
from pathlib import Path

spec=importlib.util.spec_from_file_location('sat',str(Path(__file__).with_name('search_sat.py')))
m=importlib.util.module_from_spec(spec);spec.loader.exec_module(m)

def family(orientation):
    cover=[0,1,3,7,8,9]
    groups={i:[] for i in cover}
    bit=0
    for a,b in m.EDGES:
        if a in groups and b in groups:
            center,other=(a,b) if orientation>>bit&1 else (b,a)
            bit+=1
        elif a in groups:center,other=a,b
        else:center,other=b,a
        groups[center].append(other)
    return list(groups.values())

def encode(groups,samples,fixed_outputs=False,one_not=False):
    n,gates=10,8
    c=m.CNF()
    ops=[[c.var() for _ in range(3)] for _ in range(gates)]
    aa=[[c.var() for _ in range(n+j)] for j in range(gates)]
    bb=[[c.var() for _ in range(n+j)] for j in range(gates)]
    out=[[c.var() for _ in range(gates)] for _ in groups]
    for j in range(gates):
        c.one(ops[j]);c.one(aa[j]);c.one(bb[j]);c.add(-ops[j][2],bb[j][0])
        for a in range(n+j):
            for b in range(a+1):c.add(ops[j][2],-aa[j][a],-bb[j][b])
    if one_not:c.one([o[2] for o in ops])
    else:c.add(*(o[2] for o in ops))
    for r,os in enumerate(out):
        c.one(os)
        if fixed_outputs:c.add(os[2+r])
    for a,b in itertools.combinations(range(len(groups)),2):
        for j in range(gates):c.add(-out[a][j],-out[b][j])
    for j in range(gates):
        c.add(*(aa[k][n+j] for k in range(j+1,gates)),*(bb[k][n+j] for k in range(j+1,gates)),*(os[j] for os in out))
    for x in samples:
        v=[bool(x>>i&1) for i in range(n)]
        for j in range(gates):
            a,b,z=c.var(),c.var(),c.var()
            for av,bv,src in zip(aa[j],bb[j],v):
                c.add(-av,-a,src);c.add(-av,a,m.neg(src))
                c.add(-bv,-b,src);c.add(-bv,b,m.neg(src))
            op=ops[j]
            c.add(-op[0],-a,-b,z);c.add(-op[0],a,-z);c.add(-op[0],b,-z)
            c.add(-op[1],a,b,-z);c.add(-op[1],-a,z);c.add(-op[1],-b,z)
            c.add(-op[2],-a,-z);c.add(-op[2],a,z)
            v.append(z)
        for os,group in zip(out,groups):
            target=any(x>>i&1 for i in group)
            for j,o in enumerate(os):c.add(-o,v[n+j] if target else -v[n+j])
    return c,ops,aa,bb,out

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--out',required=True);ap.add_argument('--solver',required=True)
    ap.add_argument('--orientation',type=int,default=0);ap.add_argument('--seconds',type=int,default=120)
    ap.add_argument('--fixed-outputs',action='store_true');ap.add_argument('--one-not',action='store_true')
    args=ap.parse_args();root=Path(args.out);root.mkdir(parents=True,exist_ok=True)
    groups=family(args.orientation)
    samples=sorted({x for x in range(1024) if x.bit_count()<=2 or x.bit_count()>=8})
    print('groups',groups,flush=True)
    for k in range(20):
        c,ops,aa,bb,outs=encode(groups,samples,args.fixed_outputs,args.one_not)
        cnf=root/f'{k}.cnf';sol=root/f'{k}.sol';log=root/f'{k}.log';c.out(cnf)
        print('solve',k,'samples',len(samples),'vars',c.n,'clauses',len(c.clauses),flush=True)
        with log.open('w') as f:run=subprocess.run([args.solver,'-t',str(args.seconds),'-w',str(sol),str(cnf)],stdout=f,stderr=subprocess.STDOUT)
        print('exit',run.returncode,flush=True)
        if run.returncode!=10:return
        pos={int(x) for line in sol.read_text().splitlines() if line.startswith('v ') for x in line.split()[1:] if int(x)>0}
        model=[[next(k for k,v in enumerate(s) if v in pos) for s in (ops[j],aa[j],bb[j])] for j in range(8)]
        outputs=[10+next(k for k,v in enumerate(s) if v in pos) for s in outs]
        bad=[]
        for x in range(1024):
            v=[bool(x>>i&1) for i in range(10)]
            for op,a,b in model:v.append(v[a] and v[b] if op==0 else v[a] or v[b] if op==1 else not v[a])
            if any(v[o]!=any(x>>i&1 for i in group) for o,group in zip(outputs,groups)):bad.append(x)
        print('model',model,'outputs',outputs,'errors',len(bad),flush=True)
        (root/f'{k}-model.json').write_text(json.dumps({'gates':model,'outputs':outputs,'groups':groups}))
        if not bad:print('VERIFIED ALL1024',flush=True);return
        samples=sorted(set(samples+bad[:64]))

if __name__=='__main__':main()
