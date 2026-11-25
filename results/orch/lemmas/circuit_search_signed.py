"""SAT synthesis with binary gates and a budget of distinct complemented wires."""
import argparse
import importlib.util
import itertools
import json
import pathlib
import subprocess
import time

def emit(rows,path,budget,negations,target):
    n=10;ids={};f=[]
    def v(*key):
        if key not in ids:ids[key]=len(ids)+1
        return ids[key]
    def onehot(xs):
        f.append(xs);f.extend([-a,-b] for a,b in itertools.combinations(xs,2))
    flags=[v('negative',k) for k in range(n+budget)]
    if negations:f.append(flags)
    f.extend([-x for x in xs] for xs in itertools.combinations(flags,negations+1))
    for j in range(budget):
        v('and',j)
        for side in (0,1):
            pol=v('polarity',j,side)
            onehot([v('sel',j,side,k) for k in range(n+j)])
            for k in range(n+j):f.append([-v('sel',j,side,k),-pol,flags[k]])
        for a in range(n+j):
            for b in range(a):f.append([-v('sel',j,0,a),-v('sel',j,1,b)])
            f.append([-v('sel',j,0,a),-v('sel',j,1,a),-v('polarity',j,0),v('polarity',j,1)])
    for j in range(budget-1):
        f.append([v('sel',i,side,n+j) for i in range(j+1,budget) for side in (0,1)])
        dep=[v('sel',j+1,0,n+j),v('sel',j+1,1,n+j)]
        for a in range(n+j):
            for b in range(a):f.append([-v('sel',j,0,a),-v('sel',j+1,0,b)]+dep)
    outpol=v('outpol')
    f.append([-outpol,flags[-1]])
    for row in rows:
        for j in range(budget):
            args=[]
            for side in (0,1):
                raw=v('raw',row,j,side);pol=v('polarity',j,side);x=v('arg',row,j,side);args.append(x)
                for k in range(n+j):
                    sel=v('sel',j,side,k)
                    if k<n:f.append([-sel,raw if row>>k&1 else -raw])
                    else:
                        w=v('w',row,k-n);f.extend([[-sel,-raw,w],[-sel,raw,-w]])
                f.extend([[-x,raw,pol],[-x,-raw,-pol],[x,-raw,pol],[x,raw,-pol]])
            a,b=args;w=v('w',row,j);op=v('and',j)
            f.extend([[-op,-w,a],[-op,-w,b],[-op,w,-a,-b],[op,w,-a],[op,w,-b],[op,-w,a,b]])
        out=v('w',row,budget-1)
        if target(row):f.extend([[out,outpol],[-out,-outpol]])
        else:f.extend([[-out,outpol],[out,-outpol]])
    with path.open('w') as out:
        out.write(f'p cnf {len(ids)} {len(f)}\n')
        for c in f:out.write(' '.join(map(str,c))+' 0\n')
    return ids,len(f)

def concrete(ids,positive,budget):
    mapping={i:i for i in range(10)};complement={};gates=[]
    def get(k,neg):
        if not neg:return mapping[k]
        if k not in complement:
            complement[k]=10+len(gates);gates.append([2,mapping[k],mapping[k]])
        return complement[k]
    for j in range(budget):
        ins=[]
        for side in (0,1):
            k=next(k for k in range(10+j) if ids['sel',j,side,k] in positive)
            ins.append(get(k,ids['polarity',j,side] in positive))
        op=0 if ids['and',j] in positive else 1
        mapping[10+j]=10+len(gates);gates.append([op,*ins])
    out=get(10+budget-1,ids['outpol',] in positive)
    if not complement:gates.append([2,0,0])
    return gates,out

def evaluate(gates,out,target):
    bad=[]
    for row in range(1024):
        w=[bool(row>>i&1) for i in range(10)]
        for op,a,b in gates:w.append((w[a] and w[b]) if op==0 else (w[a] or w[b]) if op==1 else not w[a])
        if w[out]!=target(row):bad.append(row)
    return bad

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--solver',required=True);p.add_argument('--prefix',required=True)
    p.add_argument('--binary',type=int,default=18);p.add_argument('--negations',type=int,default=1)
    p.add_argument('--seconds',type=int,default=1200);p.add_argument('--per-solve',type=int,default=300)
    p.add_argument('--all-rows',action='store_true')
    args=p.parse_args();assert args.binary+args.negations<=19 and args.negations>=1
    sibling=pathlib.Path(__file__).with_name('circuit_search_cegis.py')
    spec=importlib.util.spec_from_file_location('cegis',sibling);enc=importlib.util.module_from_spec(spec);spec.loader.exec_module(enc)
    false=[r for r in range(1024) if not enc.target(r)]
    maximal=[r for r in false if not any(r!=q and r&q==r for q in false)]
    rows=set(range(1024)) if args.all_rows else set([0,1023]+[1<<i for i in range(10)]+[(1<<a)|(1<<b) for a,b in enc.EDGES]+maximal)
    start=time.monotonic();iteration=0
    while time.monotonic()-start<args.seconds:
        stem=args.prefix+'_'+str(iteration);cnf=pathlib.Path(stem+'.cnf');log=pathlib.Path(stem+'.log');sol=pathlib.Path(stem+'.sol')
        ids,nc=emit(sorted(rows),cnf,args.binary,args.negations,enc.target)
        print('iteration',iteration,'rows',len(rows),'vars',len(ids),'clauses',nc,flush=True)
        limit=max(1,min(args.per_solve,int(args.seconds-(time.monotonic()-start))))
        with log.open('w') as f:run=subprocess.run([args.solver,'-t',str(limit),'-w',str(sol),str(cnf)],stdout=f,stderr=subprocess.STDOUT)
        print('returncode',run.returncode,'elapsed',time.monotonic()-start,flush=True)
        if run.returncode!=10:
            print('STOP: UNSAT (not certified)' if run.returncode==20 else 'STOP: UNKNOWN',flush=True);return
        positive=set()
        for line in sol.read_text().splitlines():
            if line.startswith('v '):positive.update(int(x) for x in line[2:].split() if int(x)>0)
        gates,out=concrete(ids,positive,args.binary)
        assert len(gates)<=19 and any(op==2 for op,a,b in gates)
        bad=evaluate(gates,out,enc.target)
        record={'gates':gates,'output':out,'errors':bad,'rows':sorted(rows)}
        pathlib.Path(stem+'.json').write_text(json.dumps(record,indent=2)+'\n')
        print('candidate',len(gates),'gates',sum(op==2 for op,a,b in gates),'NOTs','errors',len(bad),flush=True)
        if not bad:
            pathlib.Path(args.prefix+'_witness.json').write_text(json.dumps(record,indent=2)+'\n');print('FOUND all1024 checked',flush=True);return
        assert not set(bad)&rows
        rows.update(bad);iteration+=1
    print('STOP: total time budget',flush=True)

if __name__=='__main__':main()
