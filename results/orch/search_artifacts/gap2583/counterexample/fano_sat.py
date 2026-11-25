import argparse
import json
import subprocess
from pathlib import Path
P=Path('/tmp/oec/pequalnp-pilot-99/gap2583/counterexample')
SOLVER='/tmp/oec/pequalnp-pilot-99/lean-4.36.0-linux/bin/cadical'
class CNF:
    def __init__(self):self.n=0;self.cs=[]
    def var(self):self.n+=1;return self.n
    def add(self,*ls):self.cs.append(tuple(ls))
    def one(self,vs):
        self.add(*vs)
        if len(vs)<2:return
        ps=[self.var() for _ in vs[:-1]];self.add(-vs[0],ps[0])
        for i in range(1,len(vs)-1):self.add(-vs[i],ps[i]);self.add(-ps[i-1],ps[i]);self.add(-vs[i],-ps[i-1])
        self.add(-vs[-1],-ps[-1])
    def save(self,path):
        with path.open('w') as f:
            f.write(f'p cnf {self.n} {len(self.cs)}\n')
            for c in self.cs:f.write(' '.join(map(str,c))+' 0\n')

def encode(ng,fix=None,edge_visible=False):
    data=json.loads((P/'fano.json').read_text());rows=data['rows'];edges=data['edges']
    target=lambda r:any((r>>a&1) and (r>>b&1) for a,b in edges)
    f=CNF();ops=[];aa=[];bb=[]
    for j in range(ng):
        ops.append(f.var());aa.append([f.var() for _ in range(14+j)]);bb.append([f.var() for _ in range(14+j)]);f.one(aa[-1]);f.one(bb[-1])
        for a in range(14+j):
            for b in range(a+1):f.add(-aa[j][a],-bb[j][b])
    for j in range(ng-1):
        for a in range(14+j):
            for b in range(a):f.add(-bb[j][a],-bb[j+1][b])
        f.add(*[sel[14+j] for k in range(j+1,ng) for sel in [aa[k],bb[k]]])
    for i in range(14):f.add(*[sel[i] for j in range(ng) for sel in [aa[j],bb[j]]])
    if fix:
        for j,(op,a,b) in fix.items():f.add(ops[j] if op else -ops[j]);f.add(aa[j][a]);f.add(bb[j][b])
    edge_values=[[] for _ in range(ng)]
    for row in rows:
        vals=[f.var() for _ in range(ng)]
        if target(row):
            for j in range(ng):edge_values[j].append(vals[j])
        for j in range(ng):
            a=f.var();b=f.var();v=vals[j];op=ops[j]
            for dest,selectors in [(a,aa[j]),(b,bb[j])]:
                for k,sel in enumerate(selectors):
                    if k<14:f.add(-sel,dest if row>>k&1 else -dest)
                    else:f.add(-sel,-dest,vals[k-14]);f.add(-sel,dest,-vals[k-14])
            f.add(op,-v,a);f.add(op,-v,b);f.add(op,v,-a,-b)
            f.add(-op,v,-a);f.add(-op,v,-b);f.add(-op,-v,a,b)
        f.add(vals[-1] if target(row) else -vals[-1])
    if edge_visible:
        for vs in edge_values:f.add(*vs)
        eset={tuple(sorted(e)) for e in edges}
        for j in range(ng):
            for a in range(14):
                for b in range(a+1,14):
                    if (a,b) not in eset:f.add(ops[j],-aa[j][a],-bb[j][b])
    return f,ops,aa,bb

def verify(gs):
    edges=json.loads((P/'fano.json').read_text())['edges'];bad=[]
    for row in range(1<<14):
        w=[bool(row>>i&1) for i in range(14)]
        for op,a,b in gs:w.append((w[a] and w[b]) if not op else (w[a] or w[b]))
        if w[-1]!=any((row>>a&1) and (row>>b&1) for a,b in edges):bad.append(row)
    return bad

def main():
    ap=argparse.ArgumentParser();ap.add_argument('--gates',type=int,default=26);ap.add_argument('--seconds',type=int,default=60);ap.add_argument('--name',default='fano26');ap.add_argument('--fix',default='');ap.add_argument('--generate-only',action='store_true');ap.add_argument('--edge-visible',action='store_true');ar=ap.parse_args()
    fix={int(k):v for k,v in json.loads(Path(ar.fix).read_text()).items()} if ar.fix else None
    f,ops,aa,bb=encode(ar.gates,fix,ar.edge_visible);path=P/ar.name;f.save(path.with_suffix('.cnf'))
    path.with_suffix('.meta.json').write_text(json.dumps({'ops':ops,'a':aa,'b':bb,'gates':ar.gates}))
    print('FORMULA',f.n,len(f.cs),flush=True)
    if ar.generate_only:return
    with path.with_suffix('.stdout').open('w') as out,path.with_suffix('.stderr').open('w') as err:
        run=subprocess.run([SOLVER,'--sat','-t',str(ar.seconds),str(path.with_suffix('.cnf'))],stdout=out,stderr=err)
    print('EXIT',run.returncode,flush=True)
    if run.returncode!=10:return
    model=set()
    for line in path.with_suffix('.stdout').read_text().splitlines():
        if line.startswith('v '):model.update(int(x) for x in line[2:].split() if int(x)>0)
    gs=[(int(ops[j] in model),next(k for k,v in enumerate(aa[j]) if v in model),next(k for k,v in enumerate(bb[j]) if v in model)) for j in range(ar.gates)]
    bad=verify(gs);path.with_suffix('.circuit.json').write_text(json.dumps({'gates':gs,'output':13+ar.gates,'bad':bad},indent=2));print('MODEL',len(bad),'wrong rows',flush=True)
    if not bad:print('VERIFIED WITNESS',ar.gates,flush=True)

if __name__=='__main__':main()
