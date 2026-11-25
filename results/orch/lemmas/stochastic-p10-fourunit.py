from pathlib import Path
from itertools import combinations_with_replacement
from collections import Counter
import json,time
start=time.monotonic()
N=[11,69,98,49,88,44,22];T=N[:4]
allowed=[m for m in range(128) if m.bit_count()<=2 or m in T]
shared=[[any((s>>x&1) and (s>>t&1) for s in T) for t in range(7)]for x in range(7)]
need=[sum(s>>t&1 for s in T)+(t!=0)-2 for t in range(7)]
counts=Counter();hist=Counter();survivors=[]
for units in combinations_with_replacement(allowed,4):
 counts['all_multisets']+=1
 # Every retained pair inside a required triple must equal that triple's one selected parent pair.
 if any(len({m for m in units if m.bit_count()==2 and m&s==m})>1 for s in T):continue
 counts['pair_shape']+=1
 r=[sum(1<<j for j,m in enumerate(units) if m>>t&1)for t in range(7)]
 if any(r[t].bit_count()<need[t] for t in range(7)):continue
 counts['budget']+=1
 if any(r[x] and r[x]&r[t]==r[x] and not(s>>t&1) for s in T for x in range(7)if s>>x&1 for t in range(7)):continue
 counts['nonempty_colabel']+=1
 if any((r[x] or shared[x][t]) and r[x]&r[t]==r[x] and not(s>>t&1) for s in T for x in range(7)if s>>x&1 for t in range(7)):continue
 counts['shared_colabel']+=1
 center=r[0].bit_count()+sum(r[t]&r[0]==r[t] for t in range(1,7));hist[center]+=1
 if center>5:continue
 counts['center9']+=1
 costs=[r[t].bit_count()+sum(x!=t and(r[x] or shared[x][t]) and r[x]&r[t]==r[x] for x in range(7))for t in range(7)]
 if any(costs[t]>6 for t in range(1,7)):continue
 counts['all_center8']+=1
 survivors.append(dict(units=list(units),r=r,center=center,costs=costs))
res=dict(scope='Finite-only residual4 abstraction for canonical p10 I0123,Bplus14,Bzero0,missing456. Assumes exact 4triple+4pair family shape derived by separate parent/closure enumeration; actual-circuit transfer not yet formalized. Allcenter8 requires a freeeligiblepoint outsidechargedlineX; confirmed geometry has one for everyline.',triples=T,allowed_masks=allowed,need=need,counts=dict(counts),center_histogram=dict(hist),survivors=survivors,seconds=time.monotonic()-start)
Path('results/orch/lemmas/stochastic-p10-fourunit.json').write_text(json.dumps(res,indent=2)+'\n');print(json.dumps({k:v for k,v in res.items()if k!='survivors'}))
