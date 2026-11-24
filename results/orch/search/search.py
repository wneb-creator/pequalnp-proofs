import itertools, json, random, time
from pathlib import Path
rng=random.Random(5324)

def prepare(n,m,edges):
 N=n+m; nt=1<<N; allmask=(1<<nt)-1
 inputs=tuple(sum(1<<a for a in range(nt) if (a>>i)&1) for i in range(N))
 f=0
 for a,b in edges:f |= inputs[a]&inputs[n+b]
 bad=allmask^f
 evals=[(1<<a)|(1<<(n+b)) for a,b in edges]
 q=len(edges)
 matching=[]
 for mask in range(1<<q):
  best=0
  def rec(i,used,c):
   nonlocal best
   if i==n: best=max(best,c);return
   rec(i+1,used,c)
   for k,(a,b) in enumerate(edges):
    if a==i and (mask>>k)&1 and not (used>>b)&1:rec(i+1,used|(1<<b),c+1)
  rec(0,0,0);matching.append(best)
 return inputs,bad,evals,matching

def score(wires,bad,evals,matching,need_witness=False):
 cover={}
 for i,u in enumerate(wires):
  for j in range(i+1,len(wires)):
   meet=u&wires[j]
   if meet&bad:continue
   edge=sum(1<<k for k,a in enumerate(evals) if (meet>>a)&1)
   if edge:cover[edge]=(i,j)
 q=len(evals); inf=999
 dp=[inf]*(1<<q);dp[0]=0;trace={}
 for cm,pair in cover.items():
  for s in range(1<<q):
   v=s|cm
   if dp[s]+1<dp[v]:dp[v]=dp[s]+1;trace[v]=(s,pair)
 val,s=max((s.bit_count()+matching[s]-2*c,s) for s,c in enumerate(dp) if c<inf)
 if need_witness:
  pairs=[]
  while s:p,s_pair=trace[s];pairs.append(s_pair);s=p
  return val,pairs
 return val

def c4free(edges):
 E=set(edges)
 return all(not all(e in E for e in [(a,c),(a,d),(b,c),(b,d)]) for a,b in itertools.combinations(sorted({x for x,y in E}),2) for c,d in itertools.combinations(sorted({y for x,y in E}),2))

def search(n,m,edges,trials,maxg):
 inputs,bad,evals,matching=prepare(n,m,edges)
 best=-100
 for t in range(trials):
  wires=list(inputs);gates=[]
  for k in range(maxg):
   opts=[]
   for tries in range(100):
    i=rng.randrange(len(wires));j=rng.randrange(len(wires));op=rng.randrange(2)
    v=wires[i]&wires[j] if op else wires[i]|wires[j]
    if v in wires or not v&bad:continue
    opts.append((v,op,i,j));break
   if not opts:break
   v,op,i,j=opts[0];wires.append(v);gates.append((op,i,j))
   if k<2 or k>=len(edges)+matching[-1]-2:continue
   sc=score(wires,bad,evals,matching)-len(gates)
   if sc>best:
    best=sc;print(json.dumps({'event':'best','n':n,'m':m,'edges':edges,'trial':t,'gates':len(gates),'margin':sc}),flush=True)
   if sc>0:
    out={'n':n,'m':m,'edges':edges,'gates':gates,'score':score(wires,bad,evals,matching,True)}
    print('COUNTEREXAMPLE',json.dumps(out),flush=True);return out
 print(json.dumps({'event':'done','n':n,'m':m,'edges':edges,'trials':trials,'best_margin':best}),flush=True)

if __name__=='__main__':
 cases=[(2,3,[(0,0),(0,1),(1,1),(1,2)]),
        (3,3,[(0,0),(0,1),(1,1),(1,2),(2,2),(2,0)]),
        (3,4,[(0,0),(0,1),(0,3),(1,1),(1,2),(2,2),(2,0)]),
        (4,4,[(0,0),(0,1),(1,1),(1,2),(2,2),(2,3),(3,3),(3,0)])]
 for n,m,E in cases:
  assert c4free(E)
  if search(n,m,E,10000,10):break
