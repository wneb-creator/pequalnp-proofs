import argparse, itertools, json, pathlib, subprocess, time

class CNF:
    def __init__(self): self.n = 0; self.cs = []
    def var(self): self.n += 1; return self.n
    def add(self, *lits): self.cs.append(list(lits))
    def eq_or(self, z, xs):
        self.add(-z, *xs)
        for x in xs: self.add(z, -x)
    def eq_and(self, z, x, y):
        self.add(-z, x); self.add(-z, y); self.add(z, -x, -y)
    def eq_and_list(self, z, xs):
        self.add(z, *[-x for x in xs])
        for x in xs: self.add(-z, x)
    def conjunction(self, x, y):
        z = self.var(); self.eq_and(z,x,y); return z

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('n', type=int)
    ap.add_argument('k', type=int)
    ap.add_argument('stem')
    ap.add_argument('--fixed', choices=['matching','cycle'])
    ap.add_argument('--dual', action='store_true')
    ap.add_argument('--min-edges', type=int, default=0)
    a=ap.parse_args(); n=a.n; k=a.k; inp=2*n
    c=CNF(); edge=[[c.var() for j in range(n)] for i in range(n)]
    for i in range(n): c.add(edge[i][i])
    if a.min_edges:
        for xs in itertools.combinations(sum(edge,[]),n*n-a.min_edges+1): c.add(*xs)
    for i,ii in itertools.combinations(range(n),2):
        for j,jj in itertools.combinations(range(n),2):
            c.add(-edge[i][j],-edge[i][jj],-edge[ii][j],-edge[ii][jj])
    if a.fixed:
        for i in range(n):
            for j in range(n):
                e=(i==j or (a.fixed=='cycle' and j==(i+1)%n))
                c.add(edge[i][j] if e else -edge[i][j])
    sel=[[[c.var() for h in range(inp+g)] for b in range(2)] for g in range(k)]
    outs=[c.var() for g in range(k)]
    for mask in range(1<<inp):
        vals=[]
        for g in range(k):
            operands=[]
            for b in range(2):
                terms=[sel[g][b][h] for h in range(inp) if mask>>h&1]
                terms += [c.conjunction(sel[g][b][inp+h], vals[h]) for h in range(g)]
                op=c.var(); c.eq_or(op,terms); operands.append(op)
            z=c.var(); c.eq_and(z,*operands); vals.append(z)
        result=c.var()
        c.eq_or(result,[c.conjunction(outs[g],vals[g]) for g in range(k)])
        if a.dual:
            c.eq_and_list(result,[-edge[i][j] for i in range(n) for j in range(n)
                                 if not(mask>>i&1) and not(mask>>(n+j)&1)])
        else:
            c.eq_or(result,[edge[i][j] for i in range(n) for j in range(n)
                           if mask>>i&1 and mask>>(n+j)&1])
    stem=pathlib.Path(a.stem)
    with stem.with_suffix('.cnf').open('w') as f:
        f.write(f'p cnf {c.n} {len(c.cs)}\n')
        for clause in c.cs: f.write(' '.join(map(str,clause))+' 0\n')
    stem.with_suffix('.map.json').write_text(json.dumps(dict(n=n,k=k,edge=edge,sel=sel,outs=outs,dual=a.dual)))
    print(json.dumps(dict(variables=c.n,clauses=len(c.cs),n=n,k=k)),flush=True)

if __name__=='__main__': main()
