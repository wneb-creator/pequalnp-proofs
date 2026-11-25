from itertools import combinations
from collections import Counter
from time import monotonic
import json

def join(a,b,op):
 if op==0:return (a[0]|b[0],a[1]|b[1],a[2]|b[2])
 return (a[0]&b[0],((a[0]>>1)&1&b[1])|(a[1]&(b[0]>>1)&1),((a[0]>>2)&1&b[2])|(a[2]&(b[0]>>2)&1))

def synth(n,edges,limit):
 inputs=tuple((sum(((m>>i)&1)<<m for m in range(1<<n)),int(i==1),int(i==0)) for i in range(n))
 target=(sum(int(any((m>>a)&(m>>b)&1 for a,b in edges))<<m for m in range(1<<n)),0,0)
 states={():()}; began=monotonic()
 for depth in range(1,limit+1):
  nxt={}
  for gs,program in states.items():
   wires=inputs+gs; counts=Counter(wires); seen=set()
   for a,b in combinations(range(len(wires)),2):
    for op in (0,1):
     s=join(wires[a],wires[b],op)
     if s in seen:continue
     seen.add(s); rec=(op,wires[a],wires[b],s)
     if s==target:
      return dict(n=n,edges=edges,minimum=depth,program=program+(rec,),seconds=monotonic()-began)
     if counts[s]>=2:continue
     key=tuple(sorted(gs+(s,)))
     if key not in nxt:nxt[key]=program+(rec,)
   if len(nxt)>150000:
    return dict(n=n,edges=edges,exhaustively_ruled_out_through=depth-1,aborted_states=len(nxt),seconds=monotonic()-began)
  print(json.dumps(dict(progress=True,n=n,edges=edges,depth=depth,states=len(nxt),seconds=monotonic()-began)),flush=True)
  states=nxt
 return dict(n=n,edges=edges,exhaustively_ruled_out_through=limit,seconds=monotonic()-began)

def covers(n,D):
 neigh=[sum(1<<l for l in range(n) if (p-l)%n in D) for p in range(n)]
 best=2*n; minimizers=[]
 for P in range(1<<n):
  L=0
  for p in range(n):
   if not (P>>p)&1:L|=neigh[p]
  cost=P.bit_count()+L.bit_count()
  if cost<best:best,minimizers=cost,[(P,L)]
  elif cost==best:minimizers.append((P,L))
 return dict(order=len(D)-1,vertices_each_side=n,edges=n*len(D),minimum_cover=best,minimizers=minimizers,star_partition_minimum_gates=n*len(D)+best-1)

if __name__=='__main__':
 for n,D in [(3,[0,1]),(7,[0,1,3]),(13,[0,1,3,9])]:print(json.dumps(covers(n,D)),flush=True)
 for n,edges,limit in [(2,[(0,1)],4),(3,[(0,1),(0,2)],6),(4,[(0,1),(0,2),(0,3)],6),(4,[(0,1),(1,2),(2,3)],7),(4,[(0,1),(2,3)],6),(4,[(0,1),(1,2),(2,3),(3,0)],6),(3,[(0,1),(1,2),(2,0)],6)]:
  print(json.dumps(synth(n,edges,limit)),flush=True)
