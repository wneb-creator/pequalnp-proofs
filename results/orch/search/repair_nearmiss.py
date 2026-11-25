from pathlib import Path
import argparse, itertools, json, subprocess, time
from and_count_search import graph_case, SOLVER, SCRATCH

class CNF:
    def __init__(self):
        self.n = 1
        self.cs = [[1]]

    def new(self):
        self.n += 1
        return self.n

    def add(self,*xs):
        if 1 in xs or any(-x in xs for x in xs): return
        self.cs.append(list(dict.fromkeys(x for x in xs if x != -1)))

    def land(self,a,b):
        if a == -1 or b == -1 or a == -b: return -1
        if a == 1: return b
        if b == 1 or a == b: return a
        c=self.new(); self.add(-c,a);self.add(-c,b);self.add(c,-a,-b)
        return c

    def lor(self,a,b): return -self.land(-a,-b)

    def op(self,op,a,b):
        if op == 1:return self.land(a,b)
        if op == -1:return self.lor(a,b)
        y=self.new()
        self.add(-op,-y,a);self.add(-op,-y,b);self.add(-op,y,-a,-b)
        self.add(op,y,-a);self.add(op,y,-b);self.add(op,-y,a,b)
        return y

    def choose(self,ls):
        self.add(*ls)
        prev=-1
        for x in ls:
            self.add(-prev,-x)
            prev=self.lor(prev,x)

    def mux(self,selectors,values):
        if all(v == values[0] for v in values):return values[0]
        out=self.new()
        for sel,v in zip(selectors,values):
            self.add(-sel,-out,v);self.add(-sel,out,-v)
        return out

    def write(self,path):
        with path.open('w') as f:
            f.write(f'p cnf {self.n} {len(self.cs)}\n')
            for c in self.cs:f.write(' '.join(map(str,c))+' 0\n')

def encode(gates,free,rows):
    c=CNF(); selections={};ops={}
    for g in free:
        ops[g]=c.new()
        selections[g]=[[c.new() for _ in range(26+g)] for _ in range(2)]
        a,b=selections[g]
        c.choose(a);c.choose(b)
        # Both gates are commutative. Enforce distinct, ascending operands.
        for i in range(26+g):
            for j in range(i+1):c.add(-a[i],-b[j])

    def evaluate(mask):
        wires=[1 if mask>>i&1 else -1 for i in range(26)]
        args={}
        for g,(op,a,b) in enumerate(gates):
            if g in selections:
                aa,bb=[c.mux(ss,wires) for ss in selections[g]]
                args[g]=(aa,bb)
                wires.append(c.op(ops[g],aa,bb))
            else:
                wires.append(c.op(1 if op else -1,wires[a],wires[b]))
        return wires,args

    def derivative(base,baseargs,seed):
        wires=[1 if i==seed else -1 for i in range(26)]
        for g,(op,a,b) in enumerate(gates):
            if g in selections:
                da,db=[c.mux(ss,wires) for ss in selections[g]]
                ba,bb=baseargs[g]
                andval=c.lor(c.land(ba,db),c.land(da,bb))
                orval=c.lor(da,db)
                val=c.new()
                c.add(-ops[g],-val,andval);c.add(-ops[g],val,-andval)
                c.add(ops[g],-val,orval);c.add(ops[g],val,-orval)
            elif op:
                val=c.lor(c.land(base[a],wires[b]),c.land(wires[a],base[b]))
            else:val=c.lor(wires[a],wires[b])
            wires.append(val)
        c.add(-wires[-1])

    for mask,result in rows:
        vals,_=evaluate(mask)
        c.add(vals[-1] if result else -vals[-1])
    v,a=evaluate(1);derivative(v,a,13)
    v,a=evaluate(1<<13);derivative(v,a,0)
    return c,selections,ops

def evaluate(gates,mask):
    w=[bool(mask>>i&1) for i in range(26)]
    for op,a,b in gates:w.append(w[a] and w[b] if op else w[a] or w[b])
    return w

def derivative(gates,seed,base):
    v=evaluate(gates,1<<base)
    d=[i==seed for i in range(26)]
    for op,a,b in gates:d.append((v[a] and d[b]) or (d[a] and v[b]) if op else d[a] or d[b])
    return d[-1]

def main():
    p=argparse.ArgumentParser()
    p.add_argument('--free',required=True)
    p.add_argument('--seconds',type=int,default=45)
    p.add_argument('--rounds',type=int,default=6)
    p.add_argument('--full',action='store_true')
    a=p.parse_args();free=sorted(set(map(int,a.free.split(','))))
    initial=json.loads((SCRATCH/'plane-nearmiss64.json').read_text())['gates']
    _,pos,neg=graph_case('plane3')
    rows=[(x,True) for x in pos]+[(x,False) for x in (neg if a.full else [neg[0],neg[-1]])]
    folder=SCRATCH/('repair-'+ '-'.join(map(str,free)))
    folder.mkdir(exist_ok=True)
    print(json.dumps({'free':free,'total_gates':len(initial),'positive_basis':len(pos),'negative_basis':len(neg)}),flush=True)
    for i in range(a.rounds):
        start=time.time();c,sels,ops=encode(initial,free,rows)
        stem=folder/('round-'+str(i));c.write(stem.with_suffix('.cnf'))
        with stem.with_suffix('.stdout').open('w') as out,stem.with_suffix('.stderr').open('w') as err:
            proc=subprocess.run([str(SOLVER),'-t',str(a.seconds),str(stem.with_suffix('.cnf'))],stdout=out,stderr=err)
        rec={'round':i,'rows':len(rows),'variables':c.n,'clauses':len(c.cs),'code':proc.returncode,'seconds':round(time.time()-start,2)}
        if proc.returncode != 10:
            print(json.dumps(rec),flush=True);return
        truth={int(t) for line in stem.with_suffix('.stdout').read_text().splitlines() if line.startswith('v ') for t in line[2:].split() if int(t)>0}
        cand=[list(g) for g in initial]
        for g in free:
            aa,bb=[[j for j,s in enumerate(ss) if s in truth] for ss in sels[g]]
            assert len(aa)==len(bb)==1
            cand[g]=[int(ops[g] in truth),aa[0],bb[0]]
        assert all(evaluate(cand,m)[-1]==val for m,val in rows)
        assert not derivative(cand,13,0) and not derivative(cand,0,13)
        bad=[x for x in neg if evaluate(cand,x)[-1]]
        rec['violated_negatives']=len(bad)
        data={'gates':cand,'free':free,'verified_positive_basis':len(pos),'verified_negative_basis':len(neg),'negative_errors':len(bad),'derivative_left':derivative(cand,13,0),'derivative_right':derivative(cand,0,13)}
        stem.with_suffix('.candidate.json').write_text(json.dumps(data,indent=2)+'\n')
        print(json.dumps(rec),flush=True)
        if not bad:
            print('EXACT 64 GATE COUNTEREXAMPLE FOUND',flush=True)
            (SCRATCH/'plane-counterexample64.json').write_text(json.dumps(data,indent=2)+'\n')
            return
        present={m for m,_ in rows}
        rows.extend((x,False) for x in bad if x not in present)

if __name__=='__main__':main()
