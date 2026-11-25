import argparse
import itertools
import json
import subprocess
from pathlib import Path
from and_count import CNF, SOLVER

P=Path(__file__).resolve().parent
def main():
    ap=argparse.ArgumentParser();ap.add_argument('--graph',choices=['c8','subk4'],required=True);ap.add_argument('--control',action='store_true');ap.add_argument('--seconds',type=int,default=30);ar=ap.parse_args()
    p=4;edges=[(i,4+i) for i in range(4)]+[(i,4+(i-1)%4) for i in range(4)] if ar.graph=='c8' else [(v,4+j) for j,e in enumerate(itertools.combinations(range(4),2)) for v in e]
    n=8 if ar.graph=='c8' else 10;bound=len(edges)+4-1;ng=bound if ar.control else bound-1;target=lambda r:any(r>>a&1 and r>>b&1 for a,b in edges)
    fixed=None
    if ar.control:
        gs=[];terms=[]
        for a in range(4):
            ns=[b for u,b in edges if u==a];w=ns[0]
            for b in ns[1:]:gs.append([1,w,b]);w=n+len(gs)-1
            gs.append([0,a,w]);terms.append(n+len(gs)-1)
        w=terms[0]
        for b in terms[1:]:gs.append([1,w,b]);w=n+len(gs)-1
        assert len(gs)==ng
        mapping={i:i for i in range(n)};todo=set(range(ng));fixed=[]
        while todo:
            ready=[j for j in todo if gs[j][1] in mapping and gs[j][2] in mapping]
            j=min(ready,key=lambda j:(max(mapping[gs[j][1]],mapping[gs[j][2]]),min(mapping[gs[j][1]],mapping[gs[j][2]]),j));op,a,b=gs[j];a,b=sorted((mapping[a],mapping[b]));mapping[n+j]=n+len(fixed);fixed.append([op,a,b]);todo.remove(j)
    f=CNF();ops=[];aa=[];bb=[]
    def one(vs):
        f.add(*vs)
        for a,b in itertools.combinations(vs,2):f.add(-a,-b)
    for j in range(ng):
        ops.append(f.var());aa.append([f.var() for _ in range(n+j)]);bb.append([f.var() for _ in range(n+j)]);one(aa[-1]);one(bb[-1])
        for a in range(n+j):
            for b in range(a+1):f.add(-aa[j][a],-bb[j][b])
    for j in range(ng-1):
        for a in range(n+j):
            for b in range(a):f.add(-bb[j][a],-bb[j+1][b])
        f.add(*[sel[n+j] for k in range(j+1,ng) for sel in (aa[k],bb[k])])
    for i in range(n):f.add(*[sel[i] for j in range(ng) for sel in (aa[j],bb[j])])
    if fixed:
        for j,(op,a,b) in enumerate(fixed):f.add(ops[j] if op else -ops[j]);f.add(aa[j][a]);f.add(bb[j][b])
    ind=[r for r in range(1<<n) if not target(r)];mis=[r for r in ind if all(target(r|(1<<i)) for i in range(n) if not r>>i&1)];rows=sorted(mis+[sum(1<<i for i in e) for e in edges])
    for row in rows:
        vals=[f.var() for j in range(ng)]
        for j in range(ng):
            a=f.var();b=f.var();v=vals[j];op=ops[j]
            for dst,sel in ((a,aa[j]),(b,bb[j])):
                for i,s in enumerate(sel):
                    if i<n:f.add(-s,dst if row>>i&1 else -dst)
                    else:f.add(-s,-dst,vals[i-n]);f.add(-s,dst,-vals[i-n])
            f.add(op,-v,a);f.add(op,-v,b);f.add(op,v,-a,-b);f.add(-op,v,-a);f.add(-op,v,-b);f.add(-op,-v,a,b)
        f.add(vals[-1] if target(row) else -vals[-1])
    name=ar.graph+('-control' if ar.control else '-lower');base=P/name
    with base.with_suffix('.cnf').open('w') as h:
        h.write(f'p cnf {f.n} {len(f.cs)}\n')
        for c in f.cs:h.write(' '.join(map(str,c))+' 0\n')
    base.with_suffix('.meta.json').write_text(json.dumps({'n':n,'gates':ng,'edges':edges,'rows':rows,'ops':ops,'a':aa,'b':bb,'note':'Exploratory connected/distinct/colex circuit model; no T0 or star-witness constraints.'},indent=2)+'\n');print('FORMULA',f.n,len(f.cs),'ROWS',len(rows),flush=True)
    with base.with_suffix('.stdout').open('w') as out,base.with_suffix('.stderr').open('w') as err:run=subprocess.run([SOLVER,'--sat','-t',str(ar.seconds),str(base.with_suffix('.cnf'))],stdout=out,stderr=err)
    print('EXIT',run.returncode,flush=True)
    if run.returncode==10:
        model={int(v) for l in base.with_suffix('.stdout').read_text().splitlines() if l.startswith('v ') for v in l[2:].split() if int(v)>0};gs=[[int(ops[j] in model),next(i for i,v in enumerate(aa[j]) if v in model),next(i for i,v in enumerate(bb[j]) if v in model)] for j in range(ng)]
        truth=[[bool(r>>i&1) for r in range(1<<n)] for i in range(n)];reach=[{i} for i in range(n)];mixed=[];stars=[]
        for j,(op,a,b) in enumerate(gs):
            truth.append([(x or y) if op else (x and y) for x,y in zip(truth[a],truth[b])]);reach.append(reach[a]|reach[b] if op else set())
            if op and any(i<p for i in reach[-1]) and any(i>=p for i in reach[-1]):mixed.append(j)
            q={i for i in range(n) if truth[-1][1<<i]}
            if op and len(q)>=2 and all(truth[-1][r]==any(r>>i&1 for i in q) for r in range(1<<n)):
                for v in range(n):
                    if (v<p and all(i>=p and (v,i) in edges for i in q)) or (v>=p and all(i<p and (i,v) in edges for i in q)):stars.append((j,v,sorted(q)))
        bad=[r for r in range(1<<n) if truth[-1][r]!=target(r)];served=all(any((v==a and b in q) or (v==b and a in q) for j,v,q in stars) for a,b in edges)
        result={'gates':gs,'output':n+ng-1,'bad':bad,'tCount':len(mixed),'stars':stars,'all_edges_served':served};base.with_suffix('.circuit.json').write_text(json.dumps(result,indent=2)+'\n');print('MODEL wrong',len(bad),'tCount',len(mixed),'all edges served',served,flush=True)

if __name__=='__main__':main()
