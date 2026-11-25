"""Bounded counterexample search. No UNSAT here is a Lean proof."""
import argparse
import itertools
import json
import pathlib
import subprocess
import time

EDGES = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

def target(row):
    return any(row >> a & 1 and row >> b & 1 for a,b in EDGES)

def emit(rows, path, first, opcount, s=19, minnot=1, all_used=False):
    n = 10
    ids = {}
    def var(*key):
        if key not in ids: ids[key] = len(ids)+1
        return ids[key]
    f = []
    def onehot(vs):
        f.append(vs)
        f.extend([-a,-b] for a,b in itertools.combinations(vs,2))
    for j in range(s):
        onehot([var('op',j,k) for k in range(3)])
        for side in (0,1): onehot([var('sel',j,side,k) for k in range(n+j+1)])
        for a in range(n+j+1):
            for b in range(n+j+1):
                if a>b: f.append([-var('sel',j,0,a),-var('sel',j,1,b)])
                if a!=b: f.append([-var('op',j,2),-var('sel',j,0,a),-var('sel',j,1,b)])
        for i in range(j): f.append([-var('op',j,2),-var('op',i,2),-var('sel',j,0,n+i)])
    nots = [var('op',j,2) for j in range(s)]
    if minnot:
        f.extend(list(xs) for xs in itertools.combinations(nots,s-int(minnot)+1))
    f.extend([-x for x in xs] for xs in itertools.combinations(nots,opcount+1))
    if all_used:
        for j in range(s-1):
            f.append([var('sel',i,side,n+j) for i in range(j+1,s) for side in (0,1)])
    for j in range(s-1):
        dep = [var('sel',j+1,0,n+j),var('sel',j+1,1,n+j)]
        for a in range(n+j+1):
            for b in range(a): f.append([-var('sel',j,0,a),-var('sel',j+1,0,b)] + dep)
    if first != 'any':
        cases = {'not0':(2,0),'and01':(0,1),'and02':(0,2),'or01':(1,1),'or02':(1,2)}
        op,b = cases[first]
        f.extend([[var('op',0,op)],[var('sel',0,0,0)],[var('sel',0,1,b)]])
    for row in rows:
        for j in range(s):
            vals = []
            for side in (0,1):
                u = var('u',row,j,side); vals.append(u)
                for k in range(n+j+1):
                    sel = var('sel',j,side,k)
                    if k<n: f.append([-sel,u if row>>k&1 else -u])
                    elif k<n+j:
                        w = var('v',row,k-n)
                        f.extend([[-sel,-u,w],[-sel,u,-w]])
                    else: f.append([-sel,-u])
            a,b = vals; w=var('v',row,j)
            op = [var('op',j,k) for k in range(3)]
            f.extend([[-op[0],-w,a],[-op[0],-w,b],[-op[0],w,-a,-b]])
            f.extend([[-op[1],w,-a],[-op[1],w,-b],[-op[1],-w,a,b]])
            f.extend([[-op[2],w,a],[-op[2],-w,-a]])
        f.append([var('v',row,s-1) if target(row) else -var('v',row,s-1)])
    with path.open('w') as out:
        out.write(f'p cnf {len(ids)} {len(f)}\n')
        for clause in f: out.write(' '.join(map(str,clause))+' 0\n')
    return ids,len(f)

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--solver',required=True)
    p.add_argument('--prefix',required=True)
    p.add_argument('--seconds',type=int,default=600)
    p.add_argument('--per-solve',type=int,default=120)
    p.add_argument('--first',default='any')
    p.add_argument('--not-limit',type=int,default=3)
    p.add_argument('--gates',type=int,default=19)
    p.add_argument('--allow-no-not',action='store_true')
    p.add_argument('--not-min',type=int,default=1)
    p.add_argument('--all-used',action='store_true')
    args=p.parse_args()
    prefix=pathlib.Path(args.prefix)
    false=[r for r in range(1024) if not target(r)]
    maximal_false=[r for r in false if not any(r!=q and r&q==r for q in false)]
    rows=set([0,1023]+[1<<i for i in range(10)]+[(1<<a)|(1<<b) for a,b in EDGES]+maximal_false)
    start=time.monotonic(); iteration=0
    while time.monotonic()-start<args.seconds:
        stem=str(prefix)+'_'+str(iteration)
        cnf=pathlib.Path(stem+'.cnf'); log=pathlib.Path(stem+'.log'); sol=pathlib.Path(stem+'.sol')
        ids,nc=emit(sorted(rows),cnf,args.first,args.not_limit,args.gates,0 if args.allow_no_not else args.not_min,args.all_used)
        print(f'iteration={iteration} rows={len(rows)} vars={len(ids)} clauses={nc}',flush=True)
        limit=max(1,min(args.per_solve,int(args.seconds-(time.monotonic()-start))))
        with log.open('w') as out:
            run=subprocess.run([args.solver,'-t',str(limit),'-w',str(sol),str(cnf)],stdout=out,stderr=subprocess.STDOUT)
        print('returncode',run.returncode,'elapsed',time.monotonic()-start,flush=True)
        if run.returncode!=10:
            print('STOP: UNSAT (not certified)' if run.returncode==20 else 'STOP: UNKNOWN',flush=True)
            return
        positives=set()
        for line in sol.read_text().splitlines():
            if line.startswith('v '): positives.update(int(x) for x in line[2:].split() if int(x)>0)
        gates=[]
        for j in range(args.gates):
            op=next(k for k in range(3) if ids['op',j,k] in positives)
            ins=[next(k for k in range(11+j) if ids['sel',j,side,k] in positives) for side in (0,1)]
            gates.append([op,*ins])
        errors=[]
        for row in range(1024):
            w=[bool(row>>k&1) for k in range(10)]
            for op,a,b in gates:
                av=w[a] if a<len(w) else False; bv=w[b] if b<len(w) else False
                w.append((av and bv) if op==0 else (av or bv) if op==1 else not av)
            if w[-1]!=target(row): errors.append(row)
        record={'gates':gates,'errors':errors,'rows':sorted(rows)}
        pathlib.Path(stem+'.json').write_text(json.dumps(record,indent=2)+'\n')
        print('candidate errors',len(errors),'NOTs',sum(op==2 for op,a,b in gates),flush=True)
        if not errors:
            print('FOUND all1024 checked',flush=True)
            pathlib.Path(str(prefix)+'_witness.json').write_text(json.dumps(record,indent=2)+'\n')
            return
        assert not set(errors)&rows
        rows.update(errors)
        iteration+=1
    print('STOP: total time budget',flush=True)

if __name__=='__main__': main()
