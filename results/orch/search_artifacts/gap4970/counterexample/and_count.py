import argparse
import itertools
import json
import subprocess
from pathlib import Path

P=Path(__file__).resolve().parent
SOLVER='/tmp/oec/pequalnp-pilot-99/lean-4.36.0-linux/bin/cadical'
class CNF:
    def __init__(self):self.n=0;self.cs=[]
    def var(self):self.n+=1;return self.n
    def add(self,*xs):self.cs.append(list(xs))
    def both(self,a,b):
        v=self.var();self.add(-v,a);self.add(-v,b);self.add(v,-a,-b);return v
    def either(self,xs):
        v=self.var()
        for x in xs:self.add(-x,v)
        self.add(-v,*xs);return v

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--graph',choices=['c6','fano'],default='c6');ap.add_argument('--gates',type=int,default=2);ap.add_argument('--seconds',type=int,default=30);ap.add_argument('--name',default='and-count');ap.add_argument('--fixed-star',action='store_true');ap.add_argument('--tzero',action='store_true');ar=ap.parse_args();k=ar.gates
    p=3 if ar.graph=='c6' else 7;n=2*p
    edges=[(0,3),(0,5),(1,3),(1,4),(2,4),(2,5)] if p==3 else [(v,p+l) for l in range(p) for v in range(p) if (v-l)%7 in (0,1,3)]
    target=lambda r:any(r>>a&1 and r>>b&1 for a,b in edges)
    f=CNF();sels=[[[f.var() for i in range(n+j)] for side in range(2)] for j in range(k)];outputs=[f.var() for j in range(k)]
    if ar.tzero:
        for j in range(k):
            for side in range(2):
                for a in range(p):
                    for b in range(p,n):f.add(-sels[j][side][a],-sels[j][side][b])
    if ar.fixed_star:
        assert k==p
        for j in range(k):
            fixed=[{j},{b for a,b in edges if a==j}]
            for side in range(2):
                for i,v in enumerate(sels[j][side]):f.add(v if i in fixed[side] else -v)
        for v in outputs:f.add(v)
    ind=[r for r in range(1<<n) if not target(r)];mis=[r for r in ind if all(target(r|(1<<i)) for i in range(n) if not r>>i&1)];rows=sorted(mis+[sum(1<<i for i in e) for e in edges])
    for row in rows:
        vals=[]
        for j in range(k):
            operands=[]
            for side in range(2):
                terms=[sels[j][side][i] for i in range(n) if row>>i&1]
                terms += [f.both(sels[j][side][n+i],vals[i]) for i in range(j)]
                operands.append(f.either(terms))
            vals.append(f.both(*operands))
        out=f.either([f.both(outputs[j],vals[j]) for j in range(k)]);f.add(out if target(row) else -out)
    base=P/ar.name
    with base.with_suffix('.cnf').open('w') as h:
        h.write(f'p cnf {f.n} {len(f.cs)}\n')
        for c in f.cs:h.write(' '.join(map(str,c))+' 0\n')
    base.with_suffix('.meta.json').write_text(json.dumps({'graph':ar.graph,'n':n,'gates':k,'rows':rows,'selectors':sels,'outputs':outputs,'clauses':len(f.cs),'tzero':ar.tzero},indent=2)+'\n');print('FORMULA',f.n,len(f.cs),'ROWS',len(rows),flush=True)
    with base.with_suffix('.stdout').open('w') as out,base.with_suffix('.stderr').open('w') as err:
        run=subprocess.run([SOLVER,'--lrat','--binary','-t',str(ar.seconds),str(base.with_suffix('.cnf')),str(base.with_suffix('.lrat'))],stdout=out,stderr=err)
    print('EXIT',run.returncode,flush=True)
    if run.returncode==10:
        model={int(v) for l in base.with_suffix('.stdout').read_text().splitlines() if l.startswith('v ') for v in l[2:].split() if int(v)>0}
        gs=[[[i for i,v in enumerate(sels[j][side]) if v in model] for side in range(2)] for j in range(k)];out=[j for j,v in enumerate(outputs) if v in model];bad=[]
        for row in range(1<<n):
            w=[bool(row>>i&1) for i in range(n)]
            for a,b in gs:w.append(any(w[i] for i in a) and any(w[i] for i in b))
            if any(w[n+j] for j in out)!=target(row):bad.append(row)
        cost=k+sum(max(0,len(side)-1) for pair in gs for side in pair)+max(0,len(out)-1)
        result={'graph':ar.graph,'gates':gs,'output':out,'bad':bad,'naive_binary_gate_cost':cost,'tzero':ar.tzero};base.with_suffix('.circuit.json').write_text(json.dumps(result,indent=2)+'\n');print('MODEL wrong rows',len(bad),'naive binary gates',cost,flush=True)

if __name__=='__main__':main()
