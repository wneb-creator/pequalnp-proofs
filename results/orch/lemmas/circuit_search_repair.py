"""Exact SAT repairs of a near-miss circuit; heuristic subset selection only."""
import argparse
import importlib.util
import json
import pathlib
import random
import subprocess
import time

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--solver',required=True)
    p.add_argument('--seed-circuit',required=True)
    p.add_argument('--prefix',required=True)
    p.add_argument('--seconds',type=int,default=900)
    p.add_argument('--per-solve',type=int,default=10)
    p.add_argument('--free',type=int,default=8)
    p.add_argument('--seed',type=int,default=120)
    args=p.parse_args()
    sibling=pathlib.Path(__file__).with_name('circuit_search_cegis.py')
    spec=importlib.util.spec_from_file_location('cegis',sibling)
    enc=importlib.util.module_from_spec(spec);spec.loader.exec_module(enc)
    prefix=pathlib.Path(args.prefix)
    original=json.loads(pathlib.Path(args.seed_circuit).read_text())['gates']
    n=len(original); assert n==19
    mapping={i:i for i in range(10)}; pending=set(range(n)); gates=[]
    while pending:
        choices=[]
        for j in pending:
            op,a,b=original[j]
            if a in mapping and b in mapping:
                a,b=sorted([mapping[a],mapping[b]])
                choices.append((a,b,op,j))
        a,b,op,j=min(choices);pending.remove(j);mapping[10+j]=10+len(gates);gates.append([op,a,b])
    assert mapping[28]==28
    def errors(c):
        bad=[]
        for row in range(1024):
            w=[bool(row>>i&1) for i in range(10)]
            for op,a,b in c:
                av=w[a] if a<len(w) else False;bv=w[b] if b<len(w) else False
                w.append((av and bv) if op==0 else (av or bv) if op==1 else not av)
            if w[-1]!=enc.target(row):bad.append(row)
        return bad
    print('canonical near miss',len(errors(gates)),'errors',flush=True)
    base=pathlib.Path(str(prefix)+'_base.cnf')
    ids,nc=enc.emit(list(range(1024)),base,'any',3,n,1)
    text=base.read_text();header,body=text.split('\n',1)
    print('full CNF',len(ids),'vars',nc,'clauses',flush=True)
    rng=random.Random(args.seed);start=time.monotonic();iteration=0;seen=set();counts={10:0,20:0,0:0}
    while time.monotonic()-start<args.seconds:
        free=set(rng.sample(range(n),args.free))
        if iteration%2==0 and n-1 not in free:
            free.discard(min(free));free.add(n-1)
        key=tuple(sorted(free))
        if key in seen:continue
        seen.add(key)
        fixed=[]
        for j,(op,a,b) in enumerate(gates):
            if j not in free:fixed.extend([[ids['op',j,op]],[ids['sel',j,0,a]],[ids['sel',j,1,b]]])
        stem=str(prefix)+'_'+str(iteration)
        cnf=pathlib.Path(stem+'.cnf');log=pathlib.Path(stem+'.log');sol=pathlib.Path(stem+'.sol')
        cnf.write_text(f'p cnf {len(ids)} {nc+len(fixed)}\n'+body+''.join(str(c[0])+' 0\n' for c in fixed))
        limit=max(1,min(args.per_solve,int(args.seconds-(time.monotonic()-start))))
        with log.open('w') as out:
            run=subprocess.run([args.solver,'-t',str(limit),'-w',str(sol),str(cnf)],stdout=out,stderr=subprocess.STDOUT)
        counts[run.returncode]=counts.get(run.returncode,0)+1
        print('iteration',iteration,'free',key,'returncode',run.returncode,'elapsed',time.monotonic()-start,'counts',counts,flush=True)
        if run.returncode==10:
            positives=set()
            for line in sol.read_text().splitlines():
                if line.startswith('v '):positives.update(int(x) for x in line[2:].split() if int(x)>0)
            c=[]
            for j in range(n):
                op=next(k for k in range(3) if ids['op',j,k] in positives)
                ins=[next(k for k in range(11+j) if ids['sel',j,side,k] in positives) for side in (0,1)]
                c.append([op,*ins])
            bad=errors(c);assert not bad
            pathlib.Path(str(prefix)+'_witness.json').write_text(json.dumps({'gates':c,'errors':bad},indent=2)+'\n')
            print('FOUND all1024 checked',flush=True);return
        # Keep complete stdout/stderr and model result, but do not retain duplicate large CNFs.
        # Fixed subsets in the run log together with the base reproduce each exact CNF.
        cnf.unlink()
        iteration+=1
    print('DONE counts',counts,'iterations',iteration,flush=True)

if __name__=='__main__':main()
