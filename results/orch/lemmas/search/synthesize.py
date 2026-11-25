#!/usr/bin/env python3
"""Finite truth-table CEGIS for a 19-gate Petersen circuit with NOT.

This is a witness search, not a lower-bound certificate. We restrict attention
to circuits with every gate used and output at the final gate.
"""
import argparse
import itertools
import json
from pathlib import Path
import subprocess
import time

EDGES=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
def target(x):
    return any((x>>a&1) and (x>>b&1) for a,b in EDGES)
def critical():
    negatives=[x for x in range(1024) if not target(x)]
    maximal=[x for x in negatives if all(target(x|1<<i) for i in range(10) if not x>>i&1)]
    return sorted({0,1023,*maximal,*(1<<i for i in range(10)),*((1<<a)|(1<<b)for a,b in EDGES)})
class Encoder:
    def __init__(self,n,patterns,one_not=False,canonical=False,first=None,exact_nots=0,witness=None):
        self.n=n;self.count=0;self.clauses=[];self.operands={}
        if one_not:exact_nots=1
        one_not=exact_nots==1
        self.a=[[self.var()for j in range(10+i)]for i in range(n)]
        self.b=[[self.var()for j in range(10+i)]for i in range(n)]
        self.op=[[self.var()for _ in range(3)]for i in range(n)]
        for i in range(n):
            for group in (self.a[i],self.b[i],self.op[i]): self.exactly_one(group)
            # A strictly precedes B for binary gates; NOT has an unused B=0.
            neg=self.op[i][2]
            self.add(-neg,self.b[i][0])
            for j in range(10+i):
                for k in range(j+1):self.add(neg,-self.a[i][j],-self.b[i][k])
            # No repeated NOT, which could be removed from a least circuit.
            for j in range(i):self.add(-neg,-self.a[i][10+j],-self.op[j][2])
        self.add(*(o[2]for o in self.op))
        # At most 4 NOT gates, consistent with the checked 15 binary-gate bound.
        limit=exact_nots or 4
        for inds in itertools.combinations(range(n),limit+1):self.add(*(-self.op[i][2]for i in inds))
        if exact_nots>1:
            for inds in itertools.combinations(range(n),n-exact_nots+1):self.add(*(self.op[i][2]for i in inds))
        # Every node is used, except the final output gate. Inputs are essential.
        for w in range(10+n-1):
            self.add(*(s for i in range(max(0,w-9),n) for s in (self.a[i][w],self.b[i][w])))
        for x in patterns:self.add_pattern(x)
        if first:
            op,a,b=map(int,first.split(','))
            self.add(self.op[0][op]);self.add(self.a[0][a]);self.add(self.b[0][b])
        if canonical:
            # Adjacent independent gates are ordered by operation then first pin.
            for i in range(n-1):
                dep=(self.a[i+1][10+i],self.b[i+1][10+i])
                for a in range(3):
                    for b in range(a):self.add(*dep,-self.op[i][a],-self.op[i+1][b])
                    for j in range(10+i):
                        for k in range(j):self.add(*dep,-self.op[i][a],-self.op[i+1][a],-self.a[i][j],-self.a[i+1][k])
        if one_not:
            edge_masks=[(1<<a)|(1<<b)for a,b in EDGES]
            maximals=[x for x in range(1024)if not target(x) and all(target(x|1<<i)for i in range(10)if not x>>i&1)]
            for i in range(n):
                self.add(-self.op[i][2],*(-self.operands[x,i]for x in edge_masks))
                self.add(-self.op[i][2],*(self.operands[x,i]for x in maximals))
                if witness:
                    positive,negative=map(int,witness.split(','))
                    self.add(-self.op[i][2],-self.operands[positive,i])
                    self.add(-self.op[i][2],self.operands[negative,i])
                if i<n-1:
                    self.add(-self.op[i][2],-self.a[-1][10+i])
                    self.add(-self.op[i][2],-self.b[-1][10+i])
            self.add(-self.op[-1][2])
    def var(self):self.count+=1;return self.count
    def add(self,*lits):self.clauses.append(lits)
    def exactly_one(self,group):
        self.add(*group)
        for a,b in itertools.combinations(group,2):self.add(-a,-b)
    def add_pattern(self,x):
        values=[]
        for i in range(self.n):
            av,bv,ov=self.var(),self.var(),self.var()
            self.operands[x,i]=av
            for selset,v in ((self.a[i],av),(self.b[i],bv)):
                for j,sel in enumerate(selset):
                    if j<10:self.add(-sel,v if x>>j&1 else -v)
                    else:
                        q=values[j-10]
                        self.add(-sel,-q,v);self.add(-sel,q,-v)
            an,orr,no=self.op[i]
            self.add(-an,-av,-bv,ov);self.add(-an,av,-ov);self.add(-an,bv,-ov)
            self.add(-orr,av,bv,-ov);self.add(-orr,-av,ov);self.add(-orr,-bv,ov)
            self.add(-no,av,ov);self.add(-no,-av,-ov)
            values.append(ov)
        self.add(values[-1] if target(x) else -values[-1])
    def save(self,path):
        with path.open('w') as f:
            f.write(f'p cnf {self.count} {len(self.clauses)}\n')
            for c in self.clauses:f.write(' '.join(map(str,c))+' 0\n')
    def decode(self,model):
        return [(next(j for j,v in enumerate(self.op[i])if v in model),next(j for j,v in enumerate(self.a[i])if v in model),next(j for j,v in enumerate(self.b[i])if v in model))for i in range(self.n)]
def evaluate(c,x):
    vals=[bool(x>>i&1)for i in range(10)]
    for op,a,b in c:vals.append(vals[a] and vals[b] if op==0 else vals[a]or vals[b] if op==1 else not vals[a])
    return vals[-1]
def main():
    p=argparse.ArgumentParser();p.add_argument('--solver',required=True);p.add_argument('--out',required=True);p.add_argument('--gates',type=int,default=19);p.add_argument('--timeout',type=int,default=600);p.add_argument('--seconds',type=int,default=1800);p.add_argument('--all',action='store_true');p.add_argument('--one-not',action='store_true');p.add_argument('--canonical',action='store_true');p.add_argument('--first');p.add_argument('--negatives',action='store_true');p.add_argument('--exact-nots',type=int,default=0);p.add_argument('--witness');a=p.parse_args()
    out=Path(a.out);out.mkdir(parents=True,exist_ok=True)
    pats=list(range(1024))if a.all else critical()
    if a.negatives:pats=sorted(set(pats)|{x for x in range(1024)if not target(x)})
    start=time.time()
    for it in range(100):
        enc=Encoder(a.gates,pats,a.one_not,a.canonical,a.first,a.exact_nots,a.witness);cnf=out/f'iter-{it}.cnf';enc.save(cnf)
        print('iteration',it,'patterns',len(pats),'vars',enc.count,'clauses',len(enc.clauses),flush=True)
        log=out/f'iter-{it}.log'
        with log.open('w')as f:r=subprocess.run([a.solver,'-t',str(a.timeout),str(cnf)],stdout=f,stderr=subprocess.STDOUT)
        text=log.read_text()
        print('solver return',r.returncode,'elapsed',time.time()-start,flush=True)
        if r.returncode!=10:break
        model={int(v)for line in text.splitlines()if line.startswith('v ')for v in line[2:].split()if int(v)>0}
        c=enc.decode(model);wrong=[x for x in range(1024)if evaluate(c,x)!=target(x)]
        (out/f'candidate-{it}.json').write_text(json.dumps({'circuit':c,'counterexamples':wrong},indent=2))
        print('candidate',c,'wrong inputs',len(wrong),flush=True)
        if not wrong:
            print('FOUND VERIFIED COUNTEREXAMPLE',flush=True);break
        pats=sorted(set(pats)|set(wrong))
        if time.time()-start>a.seconds:break
if __name__=='__main__':main()
