import argparse
import json
import subprocess
from pathlib import Path
from fano_sat import CNF, SOLVER

P=Path('/tmp/oec/pequalnp-pilot-99/gap2583/counterexample')

def solve(n,edges,ng,name,dirty=True,seconds=30):
    target=lambda r:any((r>>a&1) and (r>>b&1) for a,b in edges)
    rows=[sum(1<<a for a in e) for e in edges]
    rows += [r for r in range(1<<n) if not target(r) and all(target(r|(1<<i)) for i in range(n) if not (r>>i&1))]
    rows=sorted(set(rows));f=CNF();ops=[];aa=[];bb=[]
    for j in range(ng):
        ops.append(f.var());aa.append([f.var() for _ in range(n+j)]);bb.append([f.var() for _ in range(n+j)])
        f.one(aa[-1]);f.one(bb[-1])
        for a in range(n+j):
            for b in range(a+1):f.add(-aa[j][a],-bb[j][b])
    for j in range(ng-1):
        f.add(*[sel[n+j] for k in range(j+1,ng) for sel in (aa[k],bb[k])])
    for i in range(n):f.add(*[sel[i] for j in range(ng) for sel in (aa[j],bb[j])])
    negatives=[[] for _ in range(ng)]
    for row in rows:
        vals=[f.var() for _ in range(ng)]
        if not target(row):
            for j in range(ng):negatives[j].append(vals[j])
        for j in range(ng):
            a=f.var();b=f.var();v=vals[j];op=ops[j]
            for dst,sels in ((a,aa[j]),(b,bb[j])):
                for k,sel in enumerate(sels):
                    if k<n:f.add(-sel,dst if row>>k&1 else -dst)
                    else:f.add(-sel,-dst,vals[k-n]);f.add(-sel,dst,-vals[k-n])
            f.add(op,-v,a);f.add(op,-v,b);f.add(op,v,-a,-b)
            f.add(-op,v,-a);f.add(-op,v,-b);f.add(-op,-v,a,b)
        f.add(vals[-1] if target(row) else -vals[-1])
    if dirty:
        choices=[f.var() for _ in range(ng)];f.one(choices)
        for j,c in enumerate(choices):
            f.add(-c,-ops[j]);f.add(-c,*negatives[j])
            for k in range(j):f.add(-c,ops[k])
    base=P/name;f.save(base.with_suffix('.cnf'))
    with base.with_suffix('.stdout').open('w') as out,base.with_suffix('.stderr').open('w') as err:
        run=subprocess.run([SOLVER,'--sat','-t',str(seconds),str(base.with_suffix('.cnf'))],stdout=out,stderr=err)
    print(name,'inputs',n,'gates',ng,'edges',edges,'rows',len(rows),'exit',run.returncode,flush=True)
    if run.returncode!=10:return
    model={int(x) for l in base.with_suffix('.stdout').read_text().splitlines() if l.startswith('v ') for x in l[2:].split() if int(x)>0}
    gs=[(int(ops[j] in model),next(k for k,v in enumerate(aa[j]) if v in model),next(k for k,v in enumerate(bb[j]) if v in model)) for j in range(ng)]
    bad=[];dirtyrow=None;first=next(j for j,g in enumerate(gs) if g[0]==0)
    for row in range(1<<n):
        w=[bool(row>>i&1) for i in range(n)]
        for op,a,b in gs:w.append((w[a] or w[b]) if op else (w[a] and w[b]))
        if w[-1]!=target(row):bad.append(row)
        if not target(row) and w[n+first]:dirtyrow=row
    result={'inputs':n,'edges':edges,'gates':gs,'bad':bad,'first_and':first,'dirty_row':dirtyrow}
    base.with_suffix('.circuit.json').write_text(json.dumps(result,indent=2));print(json.dumps(result),flush=True)

if __name__=='__main__':
    ap=argparse.ArgumentParser();ap.add_argument('--seconds',type=int,default=30);ar=ap.parse_args()
    for n in range(3,7):
        edges=[(i,i+1) for i in range(n-1)];ng=len(edges)+n//2-1
        solve(n,edges,ng,f'dirty-path{n}',seconds=ar.seconds)
    for n in (6,8):
        edges=[(i,(i+1)%n) for i in range(n)];ng=n+n//2-1
        solve(n,edges,ng,f'dirty-cycle{n}',seconds=ar.seconds)
