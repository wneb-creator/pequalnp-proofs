import argparse
import itertools
import json
import subprocess
from pathlib import Path
from encode import EDGES, SOLVER, target

P=Path(__file__).resolve().parent
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

def validate(gs,out):
    bad=[]
    for r in range(1024):
        w=[bool(r>>i&1) for i in range(10)]
        for a,b in gs:
            w.append(any(w[i] for i in a) and any(w[i] for i in b))
            if r.bit_count()==1:assert not w[-1]
        if any(w[10+i] for i in out)!=target(r):bad.append(r)
    return bad

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--gates',type=int,default=7);ap.add_argument('--reads',type=int,default=2);ap.add_argument('--seconds',type=int,default=30);ap.add_argument('--name',default='skeleton');ap.add_argument('--fix',default='');ar=ap.parse_args();k=ar.gates
    f=CNF();sels=[[[f.var() for i in range(10+j)] for side in range(2)] for j in range(k)];outputs=[f.var() for j in range(k)]
    for j in range(k):
        for v in range(10):f.add(-sels[j][0][v],-sels[j][1][v])
    for v in range(10):
        occurrences=[sels[j][side][v] for j in range(k) for side in range(2)]
        for xs in itertools.combinations(occurrences,ar.reads+1):f.add(*[-x for x in xs])
    if ar.fix:
        fixed=json.loads(Path(ar.fix).read_text());assert len(fixed['gates'])==k
        for j,pair in enumerate(fixed['gates']):
            for side,sources in enumerate(pair):
                for i,v in enumerate(sels[j][side]):f.add(v if i in sources else -v)
        for j,v in enumerate(outputs):f.add(v if j in fixed['output'] else -v)
    ind=[r for r in range(1024) if not target(r)];mis=[r for r in ind if all(target(r|(1<<i)) for i in range(10) if not r>>i&1)];rows=sorted(mis+[sum(1<<i for i in e) for e in EDGES])
    for row in rows:
        vals=[]
        for j in range(k):
            operands=[]
            for side in range(2):
                terms=[sels[j][side][i] for i in range(10) if row>>i&1]
                terms += [f.both(sels[j][side][10+i],vals[i]) for i in range(j)]
                operands.append(f.either(terms))
            vals.append(f.both(*operands))
        out=f.either([f.both(outputs[j],vals[j]) for j in range(k)]);f.add(out if target(row) else -out)
    base=P/ar.name
    with base.with_suffix('.cnf').open('w') as h:
        h.write(f'p cnf {f.n} {len(f.cs)}\n')
        for c in f.cs:h.write(' '.join(map(str,c))+' 0\n')
    base.with_suffix('.meta.json').write_text(json.dumps({'gates':k,'reads':ar.reads,'rows':rows,'selectors':sels,'outputs':outputs,'clauses':len(f.cs)},indent=2)+'\n');print('FORMULA',f.n,len(f.cs),flush=True)
    with base.with_suffix('.stdout').open('w') as out,base.with_suffix('.stderr').open('w') as err:
        run=subprocess.run([SOLVER,'--sat','--lrat','--binary','-t',str(ar.seconds),str(base.with_suffix('.cnf')),str(base.with_suffix('.lrat'))],stdout=out,stderr=err)
    print('EXIT',run.returncode,flush=True)
    if run.returncode==10:
        model={int(v) for l in base.with_suffix('.stdout').read_text().splitlines() if l.startswith('v ') for v in l[2:].split() if int(v)>0}
        gs=[[[i for i,v in enumerate(sels[j][side]) if v in model] for side in range(2)] for j in range(k)];out=[j for j,v in enumerate(outputs) if v in model];bad=validate(gs,out)
        reads=[sum(v in side for pair in gs for side in pair) for v in range(10)];or_cost=sum(max(0,len(side)-1) for pair in gs for side in pair)+max(0,len(out)-1)
        result={'gates':gs,'output':out,'raw_reads':reads,'bad':bad,'naive_binary_gate_cost':k+or_cost,'note':'Free OR-skeleton model; not a19-gate witness unless an explicit binary implementation is verified.'};base.with_suffix('.circuit.json').write_text(json.dumps(result,indent=2)+'\n');print('MODEL wrong rows',len(bad),'raw reads',reads,'naive gates',k+or_cost,flush=True)

if __name__=='__main__':main()
