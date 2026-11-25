#!/usr/bin/env python3
"""Petersen 15-binary-gate witness search with free edge negations."""
import argparse
import itertools
import json
from pathlib import Path
import subprocess
import time
from synthesize import target,critical

class AigEncoder:
    def __init__(self,n,patterns):
        self.n=n;self.count=0;self.clauses=[]
        self.a=[[self.var()for _ in range(10+i)]for i in range(n)]
        self.b=[[self.var()for _ in range(10+i)]for i in range(n)]
        self.neg=[[self.var(),self.var()]for _ in range(n)]
        self.outneg=self.var()
        for i in range(n):
            for group in (self.a[i],self.b[i]):self.exactly_one(group)
            for j in range(10+i):
                for k in range(j+1):self.add(-self.a[i][j],-self.b[i][k])
        for w in range(10+n-1):self.add(*(v for i in range(max(0,w-9),n)for v in (self.a[i][w],self.b[i][w])))
        for i in range(n-1):
            dep=(self.a[i+1][10+i],self.b[i+1][10+i])
            for j in range(10+i):
                for k in range(j):self.add(*dep,-self.a[i][j],-self.a[i+1][k])
        for x in patterns:self.add_pattern(x)
    def var(self):self.count+=1;return self.count
    def add(self,*c):self.clauses.append(c)
    def exactly_one(self,g):
        self.add(*g)
        for a,b in itertools.combinations(g,2):self.add(-a,-b)
    def xor(self,a,b,c):
        self.add(a,b,-c);self.add(-a,-b,-c);self.add(a,-b,c);self.add(-a,b,c)
    def add_pattern(self,x):
        vals=[]
        for i in range(self.n):
            av,bv,ap,bp,ov=[self.var()for _ in range(5)]
            for sels,v in ((self.a[i],av),(self.b[i],bv)):
                for j,s in enumerate(sels):
                    if j<10:self.add(-s,v if x>>j&1 else-v)
                    else:
                        q=vals[j-10];self.add(-s,-q,v);self.add(-s,q,-v)
            self.xor(av,self.neg[i][0],ap);self.xor(bv,self.neg[i][1],bp)
            self.add(-ap,-bp,ov);self.add(ap,-ov);self.add(bp,-ov)
            vals.append(ov)
        if target(x):self.add(vals[-1],self.outneg);self.add(-vals[-1],-self.outneg)
        else:self.add(vals[-1],-self.outneg);self.add(-vals[-1],self.outneg)
    def save(self,path):
        with path.open('w')as f:
            f.write(f'p cnf {self.count} {len(self.clauses)}\n')
            for c in self.clauses:f.write(' '.join(map(str,c))+' 0\n')
    def decode(self,model):
        return ([(next(j for j,v in enumerate(self.a[i])if v in model),next(j for j,v in enumerate(self.b[i])if v in model),self.neg[i][0]in model,self.neg[i][1]in model)for i in range(self.n)],self.outneg in model)
def evaluate(c,sgn,x):
    vals=[bool(x>>i&1)for i in range(10)]
    for a,b,sa,sb in c:vals.append((vals[a]^sa)and(vals[b]^sb))
    return vals[-1]^sgn
def optimize_phase(c,sgn):
    n=len(c);best=999;bestph=0
    for ph in range(1<<n):
        mask=0
        for i,(a,b,sa,sb)in enumerate(c):
            qi=ph>>i&1
            for w,s in ((a,sa),(b,sb)):
                qw=ph>>(w-10)&1 if w>=10 else 0
                if s^qw^qi:mask|=1<<w
        if (ph>>(n-1)&1)^sgn:mask|=1<<(n+9)
        score=mask.bit_count()
        if score<best:best,bestph=score,ph
    wire=list(range(10));negative={};gates=[]
    def flip(w):
        if w not in negative:
            negative[w]=10+len(gates);gates.append((2,wire[w],wire[w]))
        return negative[w]
    for i,(a,b,sa,sb)in enumerate(c):
        qi=bestph>>i&1;args=[]
        for w,s in ((a,sa),(b,sb)):
            qw=bestph>>(w-10)&1 if w>=10 else 0
            args.append(flip(w)if s^qw^qi else wire[w])
        wire.append(10+len(gates));gates.append((qi,*args))
    output=flip(n+9)if(bestph>>(n-1)&1)^sgn else wire[-1]
    return {'not_count':best,'phases':bestph,'circuit':gates,'output':output}
def main():
    p=argparse.ArgumentParser();p.add_argument('--solver',required=True);p.add_argument('--out',required=True);p.add_argument('--gates',type=int,default=15);p.add_argument('--timeout',type=int,default=1800);a=p.parse_args()
    out=Path(a.out);out.mkdir(parents=True,exist_ok=True)
    pats=sorted(set(critical())|{x for x in range(1024)if not target(x)})
    start=time.time()
    for it in range(100):
        enc=AigEncoder(a.gates,pats);cnf=out/f'iter-{it}.cnf';enc.save(cnf)
        print('iteration',it,'patterns',len(pats),'vars',enc.count,'clauses',len(enc.clauses),flush=True)
        log=out/f'iter-{it}.log'
        with log.open('w')as f:r=subprocess.run([a.solver,'-t',str(a.timeout),str(cnf)],stdout=f,stderr=subprocess.STDOUT)
        print('solver return',r.returncode,'elapsed',time.time()-start,flush=True)
        if r.returncode!=10:break
        text=log.read_text();model={int(v)for line in text.splitlines()if line.startswith('v ')for v in line[2:].split()if int(v)>0}
        c,sgn=enc.decode(model);wrong=[x for x in range(1024)if evaluate(c,sgn,x)!=target(x)]
        data={'aig':c,'outneg':sgn,'counterexamples':wrong}
        print('candidate',c,'output sign',sgn,'wrong',len(wrong),flush=True)
        if not wrong:
            data.update(optimize_phase(c,sgn));print('VERIFIED AIG','explicit NOT count',data['not_count'],flush=True)
        (out/f'candidate-{it}.json').write_text(json.dumps(data,indent=2)+'\n')
        if not wrong:break
        pats=sorted(set(pats)|set(wrong))
if __name__=='__main__':main()
