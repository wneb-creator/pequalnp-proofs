from pathlib import Path
import argparse,itertools,json,subprocess,time

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
        prefixes=[]
        for x in ls:
            self.add(-prev,-x)
            prev=self.lor(prev,x)
            prefixes.append(prev)
        return prefixes

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

SCRATCH=Path('/tmp/oec/pequalnp-pilot-64')
SOLVER=SCRATCH/'toolchain/lean-4.36.0-linux/bin/cadical'

def case(name):
 if name=='cycle6':n=6;edges=[(i,(i+1)%6) for i in range(6)]
 elif name=='cycle8':n=8;edges=[(i,(i+1)%8) for i in range(8)]
 elif name=='theta3':n=8;edges=[e for i in range(3) for e in [(0,2+i),(2+i,5+i),(5+i,1)]]
 elif name=='cycle6leaf':n=7;edges=[(i,(i+1)%6) for i in range(6)]+[(0,6)]
 else:raise ValueError(name)
 def target(m):return any(m>>a&1 and m>>b&1 for a,b in edges)
 zero=[m for m in range(1<<n) if not target(m)]
 maximal=[m for m in zero if all(m>>i&1 or target(m|(1<<i)) for i in range(n))]
 tau=min(m.bit_count() for m in range(1<<n) if all(m>>a&1 or m>>b&1 for a,b in edges))
 adj=[{b for a,b in edges if a==i}|{a for a,b in edges if b==i} for i in range(n)]
 assert all(len(adj[a]&adj[b])<=1 for a,b in itertools.combinations(range(n),2))
 assert all(target(m) or any(m&z==m for z in maximal) for m in range(1<<n))
 return n,edges,maximal,tau,target

def run(name,mode,seconds,edge_index,k_override):
 n,edges,negative,tau,target=case(name)
 claimed=len(edges)+tau-1
 k=claimed-(mode=='ordinary') if k_override is None else k_override
 c=CNF();sels=[];ops=[]
 for j in range(k):
  ops.append(c.new());a=[c.new() for _ in range(n+j)];b=[c.new() for _ in range(n+j)]
  c.choose(a);prefix=c.choose(b)
  for i in range(n+j):c.add(-a[i],-prefix[i])
  sels.append((a,b))
 def ev(mask):
  vals=[1 if mask>>i&1 else -1 for i in range(n)];args=[]
  for j in range(k):
   a,b=[c.mux(ss,vals) for ss in sels[j]];args.append((a,b));vals.append(c.op(ops[j],a,b))
  return vals,args
 positives=[(1<<a)|(1<<b) for a,b in edges]
 for mask in positives+negative:
  vals,_=ev(mask);c.add(vals[-1] if target(mask) else -vals[-1])
 if mode=='defect':
  p,l=edges[edge_index]
  for base,seed in [(p,l),(l,p)]:
   values,args=ev(1<<base);ds=[1 if i==seed else -1 for i in range(n)]
   for j in range(k):
    a,b=[c.mux(ss,ds) for ss in sels[j]];av,bv=args[j]
    avalue=c.lor(c.land(av,b),c.land(a,bv));ovalue=c.lor(a,b);v=c.new()
    c.add(-ops[j],-v,avalue);c.add(-ops[j],v,-avalue);c.add(ops[j],-v,ovalue);c.add(ops[j],v,-ovalue);ds.append(v)
   c.add(-ds[-1])
 stem=SCRATCH/f'cost-{name}-{mode}-edge{edge_index}'
 c.write(stem.with_suffix('.cnf'))
 started=time.monotonic()
 with stem.with_suffix('.stdout').open('w') as out,stem.with_suffix('.stderr').open('w') as err:
  proc=subprocess.run([str(SOLVER),'-t',str(seconds),str(stem.with_suffix('.cnf'))],stdout=out,stderr=err)
 rec=dict(case=name,n=n,edges=edges,m=len(edges),tau=tau,claimed_ordinary_bound=claimed,gates=k,mode=mode,edge_index=edge_index,boundary_rows=len(positives)+len(negative),variables=c.n,clauses=len(c.cs),code=proc.returncode,seconds=time.monotonic()-started)
 if proc.returncode==10:
  truth={int(t) for line in stem.with_suffix('.stdout').read_text().splitlines() if line.startswith('v ') for t in line[2:].split() if int(t)>0}
  gates=[]
  for j in range(k):
   a,b=[[i for i,v in enumerate(ss) if v in truth] for ss in sels[j]];assert len(a)==len(b)==1;gates.append((int(ops[j] in truth),a[0],b[0]))
  def scalar(mask):
   w=[bool(mask>>i&1) for i in range(n)]
   for op,a,b in gates:
    assert a<b<len(w)
    w.append((w[a] and w[b]) if op else (w[a] or w[b]))
   return w
  assert all(scalar(m)[-1]==target(m) for m in range(1<<n))
  if mode=='defect':
   p,l=edges[edge_index]
   for base,seed in [(p,l),(l,p)]:
    v=scalar(1<<base);d=[i==seed for i in range(n)]
    for op,a,b in gates:d.append(((v[a] and d[b]) or (d[a] and v[b])) if op else (d[a] or d[b]))
    assert not d[-1]
  rec['gates_list']=gates;rec['verified_all_assignments']=1<<n;rec['counterexample_to_proposed_bound']=(k<claimed if mode=='ordinary' else k<=claimed)
 stem.with_suffix('.result.json').write_text(json.dumps(rec,indent=2)+'\n')
 print(json.dumps(rec),flush=True)

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--case',choices=['cycle6','cycle8','theta3','cycle6leaf'],required=True);p.add_argument('--mode',choices=['ordinary','defect'],required=True);p.add_argument('--seconds',type=int,default=30);p.add_argument('--edge',type=int,default=0);p.add_argument('--gates',type=int)
 a=p.parse_args();run(a.case,a.mode,a.seconds,a.edge,a.gates)
