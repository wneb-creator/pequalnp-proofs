import argparse,itertools,json,pathlib,subprocess,time

class CNF:
    def __init__(self): self.n=0; self.clauses=[]
    def var(self): self.n+=1; return self.n
    def add(self,*c): self.clauses.append(list(c))
    def conj(self,a,b):
        z=self.var(); self.add(-z,a); self.add(-z,b); self.add(z,-a,-b); return z
    def disj(self,z,terms):
        for t in terms: self.add(-t,z)
        self.add(-z,*terms)

def graph(name):
    if name.startswith('c'):
        n=int(name[1:]); return n,sorted({tuple(sorted((i,(i+1)%n))) for i in range(n)})
    if name=='petersen':
        return 10,sorted({tuple(sorted(e)) for e in
            [(i,(i+1)%5) for i in range(5)]+[(i,i+5) for i in range(5)]+
            [(i+5,((i+2)%5)+5) for i in range(5)]})
    raise ValueError(name)

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('graph'); ap.add_argument('ands',type=int)
    ap.add_argument('--seconds',type=int,default=120)
    ap.add_argument('--prefix',required=True)
    args=ap.parse_args(); n,edges=graph(args.graph); k=args.ands
    prefix=pathlib.Path(args.prefix); prefix.parent.mkdir(parents=True,exist_ok=True)
    target=lambda x:any((x>>a)&1 and (x>>b)&1 for a,b in edges)
    independent=[x for x in range(1<<n) if not target(x)]
    maximal=[x for x in independent if all((x>>i)&1 or target(x|(1<<i)) for i in range(n))]
    rows=[(sum(1<<a for a in e),1) for e in edges]+[(x,0) for x in maximal]
    tau=n-max(x.bit_count() for x in independent)
    cnf=CNF()
    select=[[[cnf.var() for _ in range(n+i)] for _ in range(2)] for i in range(k)]
    outselect=[cnf.var() for _ in range(k)]
    for sides in select:
        for left,right in zip(*sides): cnf.add(-left,-right)
    values=[]
    for x,answer in rows:
        vals=[]
        for i in range(k):
            sides=[]
            for side in range(2):
                terms=[]
                for j,s in enumerate(select[i][side]):
                    if j<n:
                        if (x>>j)&1: terms.append(s)
                    else:
                        terms.append(cnf.conj(s,vals[j-n]))
                value=cnf.var(); cnf.disj(value,terms); sides.append(value)
            vals.append(cnf.conj(*sides))
        if answer:
            terms=[cnf.conj(s,v) for s,v in zip(outselect,vals)]
            cnf.add(*terms)
        else:
            for s,v in zip(outselect,vals): cnf.add(-s,-v)
        values.append(vals)
    cnfpath=prefix.with_suffix('.cnf')
    with cnfpath.open('w') as f:
        f.write(f'p cnf {cnf.n} {len(cnf.clauses)}\n')
        for c in cnf.clauses: f.write(' '.join(map(str,c))+' 0\n')
    started=time.monotonic()
    with prefix.with_suffix('.solver.log').open('w') as log:
        cp=subprocess.run(['/tmp/oec/pequalnp-pilot-75/lean-tools/lean-4.36.0-linux/bin/cadical',
            '-t',str(args.seconds),str(cnfpath)],stdout=log,stderr=subprocess.STDOUT)
    elapsed=time.monotonic()-started
    lines=prefix.with_suffix('.solver.log').read_text().splitlines()
    statuses=[line for line in lines if line.startswith('s ')]
    result=dict(graph=args.graph,n=n,edges=edges,vertex_cover=tau,ands=k,critical_rows=len(rows),
        variables=cnf.n,clauses=len(cnf.clauses),seconds=elapsed,exit=cp.returncode,status=statuses)
    if cp.returncode==10:
        lits=[int(v) for line in lines if line.startswith('v ') for v in line[2:].split() if v!='0']
        assert len({abs(v) for v in lits})==cnf.n,'Incomplete model'
        positive={v for v in lits if v>0}
        assert all(any((lit>0)==(abs(lit) in positive) for lit in c) for c in cnf.clauses),'Invalid CNF model'
        choices=[[[j for j,v in enumerate(s) if v in positive] for s in g] for g in select]
        outs=[i for i,s in enumerate(outselect) if s in positive]
        for x in range(1<<n):
            vs=[bool((x>>i)&1) for i in range(n)]
            for left,right in choices: vs.append(any(vs[j] for j in left) and any(vs[j] for j in right))
            assert any(vs[n+i] for i in outs)==target(x),('Truth mismatch',x)
        result.update(choices=choices,outputs=outs,all_assignments_verified=1<<n)
        tables=[sum(1<<x for x in range(1<<n) if (x>>i)&1) for i in range(n)]
        gates=[]; bytable={v:i for i,v in enumerate(tables)}
        falsewire=n+1000000
        bytable[0]=falsewire
        def binary(op,a,b):
            va=0 if a==falsewire else tables[a]
            vb=0 if b==falsewire else tables[b]
            value=va&vb if op=='and' else va|vb
            if value in bytable: return bytable[value]
            j=n+len(gates); gates.append((op,a,b)); tables.append(value); bytable[value]=j; return j
        def disj(ws):
            ws=sorted(set(ws))
            if not ws: return falsewire
            v=ws[0]
            for w in ws[1:]: v=binary('or',v,w)
            return v
        collapsed=list(range(n))
        for left,right in choices:
            collapsed.append(binary('and',disj([collapsed[j] for j in left]),disj([collapsed[j] for j in right])))
        output=disj([collapsed[n+i] for i in outs])
        used=set()
        def visit(i):
            if i<n or i==falsewire or i in used: return
            used.add(i)
            _,a,b=gates[i-n]; visit(a); visit(b)
        visit(output)
        new=[]; remap={i:i for i in range(n)}; remap[falsewire]=falsewire
        for old,(op,a,b) in enumerate(gates,n):
            if old in used:
                remap[old]=n+len(new); new.append((op,remap[a],remap[b]))
        result.update(binary_gates=new,binary_output=remap[output],binary_size=len(new),
            binary_ands=sum(op=='and' for op,_,_ in new))
    prefix.with_suffix('.json').write_text(json.dumps(result,indent=2)+'\n')
    print(json.dumps(result))

if __name__=='__main__': main()
