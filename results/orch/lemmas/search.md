# Circuit search

2026-11-24T21:49:19.630030+00:00

Decoded 12 positive truth rows as subdivision-K4 incidence edges. Left inputs 0..3 have stars [4,8,9], [6,7,9], [5,6,8], [4,5,7]. Free vectors 10=4|6, 11=5|9, 12=7|8 pair opposite edges. Standard star circuit needs 15 new gates. Running C Cartesian genetic programming search for 14 gates; code and complete log in /tmp/oec/pequalnp-pilot-42/search/.

2026-11-24T21:51:31.948904+00:00 Additional exhaustive validation on all 1024 assignments of the ten raw variables: the encoded negative rows include all 12 maximal independent sets of the subdivision-K4 graph and no positive assignments. Exactly 12 minimal positive edge assignments occur. Thus 24 essential truth rows suffice for any monotone circuit search, and the problem is exactly the graph edge function, not a weaker partial truth table. Inputs 10/11/12 are opposite-edge pair ORs.

2026-11-24T21:56:30.844946+00:00 Formula DP result: minimum formula size is 15 under exact target-error dominance, after 577,940,081 candidate-pair evaluations; 14-gate frontier had 614 retained states. Dominance is sound for formulas because on target-positive rows more true values are preferable and on target-negative rows fewer true values are preferable, and AND/OR preserve this coordinatewise order. A lower-cost dominating function may replace any subtree. This is not a circuit lower bound because sharing changes costs.

A scan combining all retained target-subfunctions by OR and target-superfunctions by AND, merging equal semantic internal nodes, found no DAG below 15. Removing the two extreme independent-set constraints still gave formula minimum 15 (353,293,843 pairs).

Stopped the three stochastic searches after billions of candidates; no exact 14-gate witness. They found 14-gate circuits missing one positive edge and exact 15-gate circuits. Now testing one paid shared gate plus a <=13-gate formula, across automorphism classes, coordinated with structural agent.

2026-11-24T22:01:30.697410+00:00 One paid shared-gate census completed across all 8 nontrivial S4 symmetry classes: no remaining formula of size <=13. Structural agent covered point-pair OR and free-pair OR; this agent covered the other six. Two-gate prefixes: 214 symmetry classes generated, 41 with dependent second gate; all dependent classes have finished without a <=12 formula. Remaining independent prefixes continue.

Packed-64 dominance and an inline rejection path preserve all baseline layer counts and the577,940,081 pair total, while reducing baseline runtime from27seconds to7seconds. Source: dp_two_hotpath.c; orchestration: run_two.py; all under scratch search directory.

## Reproducibility and limits

The search results here are computed evidence, not Lean-certified refutations. Formula-cost dominance does not bound arbitrary circuits with sharing. The one/two-prefix searches allow arbitrary reuse of the paid prefix signals, but no extra sharing in the formula remainder.

For each semantic function, record its error mask relative to the target. Fewer error bits dominate more error bits under both AND and OR. At formula cost c, combine all retained functions with costs i and j satisfying i+j+1=c. If a function is dominated by an already retained function at no greater cost, any use of it in a formula can be replaced without increasing cost or errors. Functions false on every positive row may be replaced by zero and simplified out. This yields exact minimum formula cost.

The 24 coordinates are the 12 edge assignments and 12 maximal independent sets of the subdivided K4 graph. Every monotone circuit correct on these coordinates is correct on all 58 posted coordinates. S4 acts on the four degree3 vertices, permutes the six edge vertices, and also permutes the three free opposite-edge OR signals.

Sources recorded at 2026-11-24T22:03:56.341455+00:00:

### inputs.h

SHA256: 4da780cdf88cdfc01c8072430b6c3b4ac6f07695fab3f4def5d08abc127e7070

```c
uint32_t xs[13]={251137,817232,3224100,5542026,11018243,9060364,12746800,10682560,13370112,15731712,15376435,16403468,15664064};
```

### dp.c

SHA256: 08e632384e9d862031c926aa3d57c8ed2d39bbceb3c4b47ed4531ca7730741e7

```c
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "inputs.h"
#define BITS 24
#define SIZE (1<<BITS)
#define TGT 4095U
#define FULL (SIZE-1)
unsigned char dominated[SIZE];
uint32_t left[SIZE],right[SIZE];
unsigned char ops[SIZE],costs[SIZE];
typedef struct {uint32_t*a;unsigned n,cap;} Vec;
Vec layers[40];unsigned long long pairs=0, marks=0;int found=0;
void push(Vec*v,uint32_t x){if(v->n==v->cap){v->cap=v->cap?v->cap*2:128;v->a=realloc(v->a,v->cap*sizeof(uint32_t));}v->a[v->n++]=x;}
void show(uint32_t x){if(costs[x]==0){for(int i=0;i<13;i++)if(x==xs[i]){printf("x%d",i);return;}printf("BAD");return;}printf("(");show(left[x]);printf(ops[x]?" | ":" & ");show(right[x]);printf(")");}
int consider(uint32_t x,uint32_t a,uint32_t b,int op,int c){if(!(x&TGT))return 0;uint32_t e=x^TGT;if(dominated[e])return 0;costs[x]=c;left[x]=a;right[x]=b;ops[x]=op;push(&layers[c],x);if(x==TGT){printf("FOUND formula cost=%d pairs=%llu\n",c,pairs);show(x);printf("\n");fflush(stdout);FILE*f=fopen("/tmp/oec/pequalnp-pilot-42/search/dp-state.bin","wb");fwrite(costs,1,SIZE,f);fwrite(left,4,SIZE,f);fwrite(right,4,SIZE,f);fwrite(ops,1,SIZE,f);fclose(f);found=1;return 1;}uint32_t free=FULL^e,s=free;do{dominated[e|s]=1;marks++;s=(s-1)&free;}while(s!=free);return 0;}
int main(){time_t start=time(0);for(int i=0;i<13;i++)consider(xs[i],0,0,0,0);for(int c=1;c<=17;c++){for(int i=0;i<=(c-1)/2;i++){int j=c-1-i;Vec a=layers[i],b=layers[j];printf("start cost=%d split=%d,%d counts=%u,%u time=%ld\n",c,i,j,a.n,b.n,(long)(time(0)-start));fflush(stdout);for(unsigned ai=0;ai<a.n;ai++){uint32_t x=a.a[ai];unsigned lim=(i==j)?ai+1:b.n;for(unsigned bi=0;bi<lim;bi++){uint32_t y=b.a[bi];pairs++;if(consider(x&y,x,y,0,c)||consider(x|y,x,y,1,c))return 0;}}}printf("layer cost=%d count=%u pairs=%llu marks=%llu time=%ld\n",c,layers[c].n,pairs,marks,(long)(time(0)-start));fflush(stdout);}return 0;}
```

### inputs_two.h

SHA256: d57c348ec7dcfcf55a12da146b1f2741ae80e53b85cb99f216926f99adfaf1f4

```c
uint32_t xs[15]={251137,817232,3224100,5542026,11018243,9060364,12746800,10682560,13370112,15731712,15376435,16403468,15664064,0,0};
```

### dp_two_hotpath.c

SHA256: e7b6fcc5f341d037e3c35c1e08a22535b8788af4c864a22dd513f9a682bcb0c7

```c
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <time.h>
#include "inputs_two.h"
#define BITS 24
#define SIZE (1<<BITS)
#define TGT 4095U
#define FULL (SIZE-1)
uint64_t dominated[SIZE/64],supLow[64];
uint32_t left[SIZE],right[SIZE];
unsigned char ops[SIZE],costs[SIZE];
typedef struct {uint32_t*a;unsigned n,cap;} Vec;
Vec layers[40];unsigned long long pairs=0, marks=0;int found=0;
void push(Vec*v,uint32_t x){if(v->n==v->cap){v->cap=v->cap?v->cap*2:128;v->a=realloc(v->a,v->cap*sizeof(uint32_t));}v->a[v->n++]=x;}
void show(uint32_t x){if(costs[x]==0){for(int i=0;i<15;i++)if(x==xs[i]){printf("x%d",i);return;}printf("BAD");return;}printf("(");show(left[x]);printf(ops[x]?" | ":" & ");show(right[x]);printf(")");}
int consider(uint32_t x,uint32_t a,uint32_t b,int op,int c){if(!(x&TGT))return 0;uint32_t e=x^TGT;if((dominated[e>>6]>>(e&63))&1)return 0;costs[x]=c;left[x]=a;right[x]=b;ops[x]=op;push(&layers[c],x);if(x==TGT){printf("FOUND formula cost=%d pairs=%llu\n",c,pairs);show(x);printf("\n");fflush(stdout);found=1;return 1;}uint32_t hi=e>>6,free=((SIZE>>6)-1)^hi,s=free;uint64_t low=supLow[e&63];do{dominated[hi|s]|=low;marks++;s=(s-1)&free;}while(s!=free);return 0;}
int main(int argc,char**argv){xs[13]=strtoul(argv[1],0,10);xs[14]=strtoul(argv[2],0,10);printf("prefix values=%u,%u\n",xs[13],xs[14]);printf("packed64 dominance\n");for(unsigned e=0;e<64;e++){unsigned free=63^e,s=free;do{supLow[e]|=1ULL<<(e|s);s=(s-1)&free;}while(s!=free);}time_t start=time(0);for(int i=0;i<15;i++)consider(xs[i],0,0,0,0);for(int c=1;c<=12;c++){for(int i=0;i<=(c-1)/2;i++){int j=c-1-i;Vec a=layers[i],b=layers[j];printf("start cost=%d split=%d,%d counts=%u,%u time=%ld\n",c,i,j,a.n,b.n,(long)(time(0)-start));fflush(stdout);for(unsigned ai=0;ai<a.n;ai++){uint32_t x=a.a[ai];unsigned lim=(i==j)?ai+1:b.n;for(unsigned bi=0;bi<lim;bi++){uint32_t y=b.a[bi];pairs++;uint32_t z=x&y,e=z^TGT;if((z&TGT)&&!((dominated[e>>6]>>(e&63))&1))if(consider(z,x,y,0,c))return 0;z=x|y;e=z^TGT;if((z&TGT)&&!((dominated[e>>6]>>(e&63))&1))if(consider(z,x,y,1,c))return 0;}}}printf("layer cost=%d count=%u pairs=%llu marks=%llu time=%ld\n",c,layers[c].n,pairs,marks,(long)(time(0)-start));fflush(stdout);}return 0;}
```

### prefixes.py

SHA256: c78bece7d956d233f4a3633319555a83a2a26087eafe3d0c5650b534b018bec1

```python
from itertools import permutations,combinations_with_replacement
from pathlib import Path
import json
xs=[251137,817232,3224100,5542026,11018243,9060364,12746800,10682560,13370112,15731712,15376435,16403468,15664064]
T=4095
edge_neighbors=[(0,3),(2,3),(1,2),(1,3),(0,2),(0,1)]
rows=[sum((x>>k&1)<<i for i,x in enumerate(xs[:10])) for k in range(24)]
row_index={r:i for i,r in enumerate(rows)}
transforms=[]
for p in permutations(range(4)):
 perm=list(p)
 for a,b in edge_neighbors:
  perm.append(4+edge_neighbors.index(tuple(sorted((p[a],p[b])))))
 trans=[]
 for r in rows:
  r2=sum(((r>>i)&1)<<perm[i] for i in range(10))
  trans.append(row_index[r2])
 transforms.append(trans)
def transform(f,p):
 return sum(((f>>i)&1)<<p[i] for i in range(24))
def canonical_pair(a,b):
 return min(tuple(sorted((transform(a,p),transform(b,p)))) for p in transforms)
def candidates(values):
 witnesses={}
 for i,j in combinations_with_replacement(range(len(values)),2):
  for op in [False,True]:
   v=values[i]|values[j] if op else values[i]&values[j]
   if v&T and v not in values:
    witnesses.setdefault(v,(op,i,j))
 # Target error dominance is valid for the extra gate when all previous signals are fixed.
 known_errors=[x^T for x in values]
 candidates=list(witnesses)
 selected=[]
 for v in sorted(candidates,key=lambda x:(x^T).bit_count()):
  e=v^T
  if any(d&e==d for d in known_errors): continue
  selected.append(v)
  known_errors.append(e)
 return {v:witnesses[v] for v in selected}
first=candidates(xs)
orbits={}
for v,w in first.items():
 key=min(transform(v,p) for p in transforms)
 orbits.setdefault(key,(v,w))
print('first frontier',len(first),'first orbits',len(orbits),flush=True)
prefixes={}
for f1,g1 in orbits.values():
 seconds=candidates(xs+[f1])
 print('first',g1,'second count',len(seconds),flush=True)
 for f2,g2 in seconds.items():
  key=canonical_pair(f1,f2)
  prefixes.setdefault(key,{'gates':[g1,g2],'values':[f1,f2]})
print('prefix orbits',len(prefixes),flush=True)
Path('/tmp/oec/pequalnp-pilot-42/search/prefixes.json').write_text(json.dumps(list(prefixes.values()),indent=2))
```

### run_two.py

SHA256: 9ad3309cb2c107dd027612794264378cfad3d6559970ea34ea96c0a86277b180

```python
from concurrent.futures import ThreadPoolExecutor
from pathlib import Path
from datetime import datetime, timezone
import subprocess,json,threading
root=Path('/tmp/oec/pequalnp-pilot-42/search')
jobs=list(enumerate(json.loads((root/'prefixes.json').read_text())))
jobs.sort(key=lambda j:not(13 in j[1]['gates'][1][1:]))
print('jobs',len(jobs),'dependent',sum(13 in j[1]['gates'][1][1:] for j in jobs),flush=True)
stop=threading.Event()
def run(job):
 if stop.is_set(): return
 i,data=job
 path=root/('two-'+str(i)+'.log')
 with path.open('w') as f:
  r=subprocess.run([str(root/'dp_two'),*map(str,data['values'])],stdout=f,stderr=subprocess.STDOUT)
 found='FOUND' in path.read_text()
 print(datetime.now(timezone.utc).isoformat(),i,data['gates'],r.returncode,'FOUND' if found else 'none',flush=True)
 if found:stop.set()
with ThreadPoolExecutor(max_workers=3) as ex:
 list(ex.map(run,jobs))
```

### compress_validate.py

SHA256: edbc2c7f2b23564fdea3571452dc842db23e1702239ebb55cbe6615ee609d876

```python
from pathlib import Path
original=[256463372304,8521482511360,14003410187716736,55389823206179104,155696362464215096,218994303131713984,183565875465424384,229736628136996864,270286071508729856,288160007409369088,192860064594267704,288166778660192704,283797140973809664]
target=1764784
edges=[(0,4),(0,8),(0,9),(1,6),(1,7),(1,9),(2,5),(2,6),(2,8),(3,4),(3,5),(3,7)]
assert original[10]==original[4]|original[6]
assert original[11]==original[5]|original[9]
assert original[12]==original[7]|original[8]
patterns=[sum((x>>k&1)<<i for i,x in enumerate(original[:10])) for k in range(58)]
positives={patterns[k] for k in range(58) if target>>k&1}
assert positives=={(1<<a)|(1<<b) for a,b in edges}
independent=[m for m in range(1024) if not any(m>>a&1 and m>>b&1 for a,b in edges)]
maximal=[m for m in independent if not any(m!=n and m&n==m for n in independent)]
negatives={patterns[k] for k in range(58) if not(target>>k&1)}
assert set(maximal)<=negatives<=set(independent)
rows=[k for k in range(58) if target>>k&1]
rows.extend(patterns.index(m) for m in maximal)
compressed=[sum((x>>k&1)<<i for i,k in enumerate(rows)) for x in original]
expected=[251137,817232,3224100,5542026,11018243,9060364,12746800,10682560,13370112,15731712,15376435,16403468,15664064]
assert compressed==expected
assert len(positives)==len(maximal)==12
print('Validated: 12 positive edge rows, 12 maximal independent rows; all58rows are covered.')
print('Row indices:',rows)
```

## Final two-prefix census

Completed 2026-11-24T22:04:52.585765Z. All214 symmetry classes exhausted formula cost12 without a witness; all214 process exits were0. Every per-class log ends with a completed cost12 layer. Final validation performed 2026-11-24T22:05:13.055555+00:00.

Full run summary:

```text
jobs 214 dependent 41
2026-11-24T21:57:57.341893+00:00 5 [[False, 0, 4], [True, 1, 13]] 0 none
2026-11-24T21:57:59.225895+00:00 6 [[False, 0, 4], [True, 3, 13]] 0 none
2026-11-24T21:58:03.601483+00:00 7 [[False, 0, 4], [True, 5, 13]] 0 none
2026-11-24T21:58:08.733523+00:00 8 [[False, 0, 4], [True, 6, 13]] 0 none
2026-11-24T21:58:16.081257+00:00 9 [[False, 0, 4], [True, 8, 13]] 0 none
2026-11-24T21:58:16.765768+00:00 36 [[False, 0, 4], [True, 11, 13]] 0 none
2026-11-24T21:58:33.891170+00:00 50 [[True, 10, 11], [True, 12, 13]] 0 none
2026-11-24T21:58:34.159646+00:00 51 [[True, 10, 11], [True, 7, 13]] 0 none
2026-11-24T21:58:44.073730+00:00 68 [[True, 0, 1], [False, 9, 13]] 0 none
2026-11-24T21:58:44.879185+00:00 52 [[True, 10, 11], [False, 0, 13]] 0 none
2026-11-24T21:59:03.172226+00:00 58 [[True, 10, 11], [True, 0, 13]] 0 none
2026-11-24T21:59:07.953441+00:00 69 [[True, 0, 1], [True, 2, 13]] 0 none
2026-11-24T21:59:18.590803+00:00 70 [[True, 0, 1], [True, 5, 13]] 0 none
2026-11-24T21:59:25.950570+00:00 86 [[True, 0, 1], [True, 4, 13]] 0 none
2026-11-24T21:59:30.958487+00:00 85 [[True, 0, 1], [False, 10, 13]] 0 none
2026-11-24T21:59:33.778429+00:00 96 [[True, 0, 5], [True, 1, 13]] 0 none
2026-11-24T21:59:41.481795+00:00 98 [[True, 0, 5], [False, 11, 13]] 0 none
2026-11-24T21:59:48.626147+00:00 97 [[True, 0, 5], [True, 6, 13]] 0 none
2026-11-24T21:59:50.380454+00:00 117 [[True, 0, 5], [True, 10, 13]] 0 none
2026-11-24T21:59:53.625658+00:00 87 [[True, 0, 1], [True, 10, 13]] 0 none
2026-11-24T21:59:58.992616+00:00 132 [[True, 4, 5], [False, 3, 13]] 0 none
2026-11-24T22:00:02.289699+00:00 119 [[True, 0, 5], [True, 4, 13]] 0 none
2026-11-24T22:00:02.383131+00:00 118 [[True, 0, 5], [True, 2, 13]] 0 none
2026-11-24T22:00:08.979107+00:00 135 [[True, 4, 5], [True, 12, 13]] 0 none
2026-11-24T22:00:11.134796+00:00 133 [[True, 4, 5], [True, 1, 13]] 0 none
2026-11-24T22:00:11.198570+00:00 134 [[True, 4, 5], [True, 7, 13]] 0 none
2026-11-24T22:00:17.077569+00:00 148 [[True, 4, 5], [True, 0, 13]] 0 none
2026-11-24T22:00:18.225709+00:00 147 [[True, 4, 5], [True, 8, 13]] 0 none
2026-11-24T22:00:19.930903+00:00 162 [[True, 4, 5], [True, 3, 13]] 0 none
2026-11-24T22:00:21.502044+00:00 163 [[True, 4, 11], [False, 0, 13]] 0 none
2026-11-24T22:00:27.891646+00:00 166 [[True, 4, 11], [True, 1, 13]] 0 none
2026-11-24T22:00:28.425644+00:00 165 [[True, 4, 11], [True, 7, 13]] 0 none
2026-11-24T22:00:30.600094+00:00 164 [[True, 4, 11], [True, 12, 13]] 0 none
2026-11-24T22:00:33.946416+00:00 176 [[True, 4, 11], [True, 0, 13]] 0 none
2026-11-24T22:00:34.825698+00:00 187 [[True, 0, 10], [True, 5, 13]] 0 none
2026-11-24T22:00:35.802040+00:00 188 [[True, 0, 10], [True, 11, 13]] 0 none
2026-11-24T22:00:39.283165+00:00 195 [[True, 0, 10], [True, 3, 13]] 0 none
2026-11-24T22:00:40.700113+00:00 189 [[True, 0, 10], [True, 1, 13]] 0 none
2026-11-24T22:00:42.194513+00:00 206 [[True, 0, 4], [True, 1, 13]] 0 none
2026-11-24T22:00:42.430409+00:00 207 [[True, 0, 4], [True, 5, 13]] 0 none
2026-11-24T22:00:44.433143+00:00 1 [[False, 0, 4], [False, 1, 6]] 0 none
2026-11-24T22:00:45.730145+00:00 0 [[False, 0, 4], [False, 0, 8]] 0 none
2026-11-24T22:00:45.886677+00:00 208 [[True, 0, 4], [True, 11, 13]] 0 none
2026-11-24T22:00:46.439042+00:00 2 [[False, 0, 4], [False, 1, 7]] 0 none
2026-11-24T22:00:48.953424+00:00 3 [[False, 0, 4], [False, 1, 9]] 0 none
2026-11-24T22:00:49.185063+00:00 10 [[False, 0, 4], [True, 10, 11]] 0 none
2026-11-24T22:00:49.325593+00:00 4 [[False, 0, 4], [False, 3, 4]] 0 none
2026-11-24T22:00:51.766405+00:00 12 [[False, 0, 4], [True, 0, 1]] 0 none
2026-11-24T22:00:53.466819+00:00 11 [[False, 0, 4], [True, 11, 12]] 0 none
2026-11-24T22:00:54.567458+00:00 13 [[False, 0, 4], [True, 0, 3]] 0 none
2026-11-24T22:00:54.930335+00:00 14 [[False, 0, 4], [True, 0, 5]] 0 none
2026-11-24T22:00:58.130672+00:00 15 [[False, 0, 4], [True, 0, 6]] 0 none
2026-11-24T22:00:59.244328+00:00 16 [[False, 0, 4], [True, 1, 2]] 0 none
2026-11-24T22:01:00.881033+00:00 17 [[False, 0, 4], [True, 1, 3]] 0 none
2026-11-24T22:01:03.030887+00:00 18 [[False, 0, 4], [True, 1, 4]] 0 none
2026-11-24T22:01:03.158359+00:00 20 [[False, 0, 4], [True, 1, 8]] 0 none
2026-11-24T22:01:05.147754+00:00 22 [[False, 0, 4], [True, 3, 8]] 0 none
2026-11-24T22:01:05.796979+00:00 19 [[False, 0, 4], [True, 1, 5]] 0 none
2026-11-24T22:01:06.403492+00:00 23 [[False, 0, 4], [True, 4, 5]] 0 none
2026-11-24T22:01:08.125841+00:00 25 [[False, 0, 4], [True, 4, 11]] 0 none
2026-11-24T22:01:08.280663+00:00 21 [[False, 0, 4], [True, 3, 6]] 0 none
2026-11-24T22:01:09.668752+00:00 24 [[False, 0, 4], [True, 4, 8]] 0 none
2026-11-24T22:01:09.747891+00:00 26 [[False, 0, 4], [True, 5, 6]] 0 none
2026-11-24T22:01:11.868122+00:00 29 [[False, 0, 4], [True, 5, 10]] 0 none
2026-11-24T22:01:12.077593+00:00 27 [[False, 0, 4], [True, 5, 7]] 0 none
2026-11-24T22:01:13.283143+00:00 28 [[False, 0, 4], [True, 5, 8]] 0 none
2026-11-24T22:01:14.063742+00:00 30 [[False, 0, 4], [True, 5, 12]] 0 none
2026-11-24T22:01:16.126365+00:00 31 [[False, 0, 4], [True, 6, 8]] 0 none
2026-11-24T22:01:17.730935+00:00 32 [[False, 0, 4], [True, 6, 11]] 0 none
2026-11-24T22:01:20.030642+00:00 33 [[False, 0, 4], [True, 8, 9]] 0 none
2026-11-24T22:01:21.844300+00:00 34 [[False, 0, 4], [True, 8, 10]] 0 none
2026-11-24T22:01:23.534730+00:00 35 [[False, 0, 4], [True, 8, 11]] 0 none
2026-11-24T22:01:25.648989+00:00 37 [[False, 0, 4], [True, 0, 10]] 0 none
2026-11-24T22:01:26.425627+00:00 38 [[False, 0, 4], [True, 0, 11]] 0 none
2026-11-24T22:01:27.990838+00:00 39 [[False, 0, 4], [True, 1, 10]] 0 none
2026-11-24T22:01:30.906079+00:00 42 [[False, 0, 4], [True, 3, 10]] 0 none
2026-11-24T22:01:31.125578+00:00 40 [[False, 0, 4], [True, 1, 11]] 0 none
2026-11-24T22:01:32.862060+00:00 41 [[False, 0, 4], [True, 1, 12]] 0 none
2026-11-24T22:01:34.592444+00:00 43 [[False, 0, 4], [True, 3, 11]] 0 none
2026-11-24T22:01:35.130423+00:00 44 [[False, 0, 4], [True, 0, 4]] 0 none
2026-11-24T22:01:38.592293+00:00 45 [[False, 0, 4], [True, 0, 8]] 0 none
2026-11-24T22:01:40.461463+00:00 46 [[False, 0, 4], [True, 1, 6]] 0 none
2026-11-24T22:01:41.025670+00:00 47 [[False, 0, 4], [True, 1, 7]] 0 none
2026-11-24T22:01:44.174451+00:00 49 [[False, 0, 4], [True, 3, 5]] 0 none
2026-11-24T22:01:44.938754+00:00 48 [[False, 0, 4], [True, 1, 9]] 0 none
2026-11-24T22:01:48.454801+00:00 55 [[True, 10, 11], [True, 0, 2]] 0 none
2026-11-24T22:01:49.325650+00:00 53 [[True, 10, 11], [True, 10, 12]] 0 none
2026-11-24T22:01:52.234446+00:00 56 [[True, 10, 11], [True, 0, 5]] 0 none
2026-11-24T22:01:53.464731+00:00 54 [[True, 10, 11], [True, 0, 1]] 0 none
2026-11-24T22:01:55.534503+00:00 57 [[True, 10, 11], [True, 0, 7]] 0 none
2026-11-24T22:01:59.603087+00:00 59 [[True, 10, 11], [True, 4, 5]] 0 none
2026-11-24T22:02:01.345058+00:00 60 [[True, 10, 11], [True, 4, 7]] 0 none
2026-11-24T22:02:02.826100+00:00 61 [[True, 10, 11], [True, 4, 11]] 0 none
2026-11-24T22:02:06.264092+00:00 62 [[True, 10, 11], [True, 4, 12]] 0 none
2026-11-24T22:02:09.134844+00:00 63 [[True, 10, 11], [True, 7, 10]] 0 none
2026-11-24T22:02:09.364495+00:00 64 [[True, 10, 11], [True, 0, 10]] 0 none
2026-11-24T22:02:12.255285+00:00 65 [[True, 10, 11], [True, 0, 12]] 0 none
2026-11-24T22:02:14.600356+00:00 67 [[True, 10, 11], [True, 0, 8]] 0 none
2026-11-24T22:02:15.264728+00:00 66 [[True, 10, 11], [True, 0, 4]] 0 none
2026-11-24T22:02:17.299410+00:00 71 [[True, 0, 1], [True, 0, 2]] 0 none
2026-11-24T22:02:21.058723+00:00 72 [[True, 0, 1], [True, 0, 5]] 0 none
2026-11-24T22:02:22.094492+00:00 74 [[True, 0, 1], [True, 2, 3]] 0 none
2026-11-24T22:02:22.830412+00:00 73 [[True, 0, 1], [True, 0, 6]] 0 none
2026-11-24T22:02:27.525810+00:00 75 [[True, 0, 1], [True, 2, 4]] 0 none
2026-11-24T22:02:28.788595+00:00 76 [[True, 0, 1], [True, 2, 9]] 0 none
2026-11-24T22:02:29.282728+00:00 77 [[True, 0, 1], [True, 4, 5]] 0 none
2026-11-24T22:02:32.066084+00:00 78 [[True, 0, 1], [True, 4, 7]] 0 none
2026-11-24T22:02:34.086632+00:00 80 [[True, 0, 1], [True, 4, 9]] 0 none
2026-11-24T22:02:34.434571+00:00 79 [[True, 0, 1], [True, 4, 8]] 0 none
2026-11-24T22:02:38.034061+00:00 81 [[True, 0, 1], [True, 4, 11]] 0 none
2026-11-24T22:02:39.330878+00:00 83 [[True, 0, 1], [True, 5, 10]] 0 none
2026-11-24T22:02:42.363295+00:00 82 [[True, 0, 1], [True, 4, 12]] 0 none
2026-11-24T22:02:44.375606+00:00 88 [[True, 0, 1], [True, 0, 10]] 0 none
2026-11-24T22:02:44.576484+00:00 84 [[True, 0, 1], [True, 9, 10]] 0 none
2026-11-24T22:02:47.663232+00:00 91 [[True, 0, 1], [True, 2, 11]] 0 none
2026-11-24T22:02:49.290476+00:00 90 [[True, 0, 1], [True, 2, 10]] 0 none
2026-11-24T22:02:50.491067+00:00 92 [[True, 0, 1], [True, 0, 4]] 0 none
2026-11-24T22:02:50.854486+00:00 89 [[True, 0, 1], [True, 0, 11]] 0 none
2026-11-24T22:02:54.553924+00:00 95 [[True, 0, 1], [True, 2, 6]] 0 none
2026-11-24T22:02:54.846241+00:00 93 [[True, 0, 1], [True, 0, 9]] 0 none
2026-11-24T22:02:55.630735+00:00 94 [[True, 0, 1], [True, 2, 5]] 0 none
2026-11-24T22:03:00.196593+00:00 99 [[True, 0, 5], [True, 0, 6]] 0 none
2026-11-24T22:03:00.469837+00:00 101 [[True, 0, 5], [True, 1, 5]] 0 none
2026-11-24T22:03:02.782049+00:00 100 [[True, 0, 5], [True, 1, 4]] 0 none
2026-11-24T22:03:07.958940+00:00 104 [[True, 0, 5], [True, 4, 5]] 0 none
2026-11-24T22:03:10.931228+00:00 102 [[True, 0, 5], [True, 2, 4]] 0 none
2026-11-24T22:03:11.642825+00:00 105 [[True, 0, 5], [True, 4, 7]] 0 none
2026-11-24T22:03:11.698456+00:00 103 [[True, 0, 5], [True, 2, 9]] 0 none
2026-11-24T22:03:15.037230+00:00 107 [[True, 0, 5], [True, 4, 9]] 0 none
2026-11-24T22:03:16.059131+00:00 106 [[True, 0, 5], [True, 4, 8]] 0 none
2026-11-24T22:03:19.285964+00:00 108 [[True, 0, 5], [True, 4, 11]] 0 none
2026-11-24T22:03:22.230624+00:00 109 [[True, 0, 5], [True, 4, 12]] 0 none
2026-11-24T22:03:22.282171+00:00 110 [[True, 0, 5], [True, 5, 6]] 0 none
2026-11-24T22:03:25.986879+00:00 111 [[True, 0, 5], [True, 5, 10]] 0 none
2026-11-24T22:03:27.930897+00:00 113 [[True, 0, 5], [True, 6, 9]] 0 none
2026-11-24T22:03:27.970656+00:00 112 [[True, 0, 5], [True, 6, 7]] 0 none
2026-11-24T22:03:32.034880+00:00 114 [[True, 0, 5], [True, 6, 11]] 0 none
2026-11-24T22:03:34.430949+00:00 115 [[True, 0, 5], [True, 6, 12]] 0 none
2026-11-24T22:03:34.478370+00:00 116 [[True, 0, 5], [True, 9, 10]] 0 none
2026-11-24T22:03:37.390231+00:00 120 [[True, 0, 5], [True, 0, 11]] 0 none
2026-11-24T22:03:42.505357+00:00 121 [[True, 0, 5], [True, 1, 10]] 0 none
2026-11-24T22:03:42.626454+00:00 122 [[True, 0, 5], [True, 1, 11]] 0 none
2026-11-24T22:03:42.952503+00:00 123 [[True, 0, 5], [True, 2, 10]] 0 none
2026-11-24T22:03:47.166824+00:00 124 [[True, 0, 5], [True, 2, 11]] 0 none
2026-11-24T22:03:47.771751+00:00 126 [[True, 0, 5], [True, 0, 9]] 0 none
2026-11-24T22:03:49.965503+00:00 125 [[True, 0, 5], [True, 2, 12]] 0 none
2026-11-24T22:03:51.391902+00:00 127 [[True, 0, 5], [True, 1, 6]] 0 none
2026-11-24T22:03:51.855135+00:00 128 [[True, 0, 5], [True, 1, 9]] 0 none
2026-11-24T22:03:53.189289+00:00 129 [[True, 0, 5], [True, 2, 5]] 0 none
2026-11-24T22:03:54.554536+00:00 131 [[True, 0, 5], [True, 2, 8]] 0 none
2026-11-24T22:03:54.570523+00:00 130 [[True, 0, 5], [True, 2, 6]] 0 none
2026-11-24T22:03:55.475860+00:00 136 [[True, 4, 5], [True, 4, 7]] 0 none
2026-11-24T22:03:56.472724+00:00 137 [[True, 4, 5], [True, 4, 8]] 0 none
2026-11-24T22:03:56.825610+00:00 138 [[True, 4, 5], [True, 4, 9]] 0 none
2026-11-24T22:03:58.778535+00:00 140 [[True, 4, 5], [True, 4, 12]] 0 none
2026-11-24T22:03:58.939950+00:00 141 [[True, 4, 5], [True, 6, 7]] 0 none
2026-11-24T22:03:58.975614+00:00 139 [[True, 4, 5], [True, 4, 11]] 0 none
2026-11-24T22:04:00.960857+00:00 142 [[True, 4, 5], [True, 6, 9]] 0 none
2026-11-24T22:04:03.371916+00:00 145 [[True, 4, 5], [True, 7, 10]] 0 none
2026-11-24T22:04:03.473290+00:00 143 [[True, 4, 5], [True, 6, 11]] 0 none
2026-11-24T22:04:03.686265+00:00 144 [[True, 4, 5], [True, 6, 12]] 0 none
2026-11-24T22:04:05.595399+00:00 146 [[True, 4, 5], [True, 8, 10]] 0 none
2026-11-24T22:04:07.656628+00:00 149 [[True, 4, 5], [True, 0, 10]] 0 none
2026-11-24T22:04:07.992187+00:00 150 [[True, 4, 5], [True, 0, 11]] 0 none
2026-11-24T22:04:08.371102+00:00 151 [[True, 4, 5], [True, 0, 12]] 0 none
2026-11-24T22:04:10.325663+00:00 153 [[True, 4, 5], [True, 1, 12]] 0 none
2026-11-24T22:04:10.725610+00:00 154 [[True, 4, 5], [True, 3, 10]] 0 none
2026-11-24T22:04:10.767932+00:00 152 [[True, 4, 5], [True, 1, 10]] 0 none
2026-11-24T22:04:12.597938+00:00 155 [[True, 4, 5], [True, 3, 12]] 0 none
2026-11-24T22:04:13.091929+00:00 157 [[True, 4, 5], [True, 0, 9]] 0 none
2026-11-24T22:04:13.743179+00:00 156 [[True, 4, 5], [True, 0, 8]] 0 none
2026-11-24T22:04:14.938224+00:00 158 [[True, 4, 5], [True, 1, 6]] 0 none
2026-11-24T22:04:15.400299+00:00 159 [[True, 4, 5], [True, 1, 7]] 0 none
2026-11-24T22:04:17.226101+00:00 161 [[True, 4, 5], [True, 3, 7]] 0 none
2026-11-24T22:04:17.294990+00:00 160 [[True, 4, 5], [True, 3, 4]] 0 none
2026-11-24T22:04:18.087562+00:00 167 [[True, 4, 11], [True, 4, 12]] 0 none
2026-11-24T22:04:19.972755+00:00 169 [[True, 4, 11], [True, 5, 12]] 0 none
2026-11-24T22:04:20.562772+00:00 168 [[True, 4, 11], [True, 5, 10]] 0 none
2026-11-24T22:04:20.726340+00:00 170 [[True, 4, 11], [True, 6, 11]] 0 none
2026-11-24T22:04:22.787333+00:00 171 [[True, 4, 11], [True, 6, 12]] 0 none
2026-11-24T22:04:23.992110+00:00 173 [[True, 4, 11], [True, 0, 10]] 0 none
2026-11-24T22:04:25.075742+00:00 172 [[True, 4, 11], [True, 7, 11]] 0 none
2026-11-24T22:04:27.260281+00:00 174 [[True, 4, 11], [True, 0, 11]] 0 none
2026-11-24T22:04:27.867148+00:00 175 [[True, 4, 11], [True, 0, 12]] 0 none
2026-11-24T22:04:29.145992+00:00 177 [[True, 4, 11], [True, 1, 10]] 0 none
2026-11-24T22:04:29.953037+00:00 178 [[True, 4, 11], [True, 1, 12]] 0 none
2026-11-24T22:04:30.664155+00:00 179 [[True, 4, 11], [True, 0, 4]] 0 none
2026-11-24T22:04:31.726703+00:00 180 [[True, 4, 11], [True, 0, 8]] 0 none
2026-11-24T22:04:32.462530+00:00 181 [[True, 4, 11], [True, 0, 9]] 0 none
2026-11-24T22:04:33.282133+00:00 182 [[True, 4, 11], [True, 1, 6]] 0 none
2026-11-24T22:04:34.345232+00:00 183 [[True, 4, 11], [True, 1, 7]] 0 none
2026-11-24T22:04:34.825745+00:00 184 [[True, 4, 11], [True, 1, 9]] 0 none
2026-11-24T22:04:36.158505+00:00 185 [[True, 0, 10], [True, 0, 5]] 0 none
2026-11-24T22:04:36.763577+00:00 186 [[True, 0, 10], [True, 5, 10]] 0 none
2026-11-24T22:04:37.184993+00:00 190 [[True, 0, 10], [True, 0, 11]] 0 none
2026-11-24T22:04:38.480179+00:00 191 [[True, 0, 10], [True, 1, 10]] 0 none
2026-11-24T22:04:39.297485+00:00 192 [[True, 0, 10], [True, 1, 11]] 0 none
2026-11-24T22:04:39.726240+00:00 193 [[True, 0, 10], [True, 1, 12]] 0 none
2026-11-24T22:04:41.054141+00:00 194 [[True, 0, 10], [True, 3, 10]] 0 none
2026-11-24T22:04:41.735676+00:00 196 [[True, 0, 10], [True, 0, 4]] 0 none
2026-11-24T22:04:41.957618+00:00 197 [[True, 0, 10], [True, 0, 8]] 0 none
2026-11-24T22:04:43.367930+00:00 198 [[True, 0, 10], [True, 1, 6]] 0 none
2026-11-24T22:04:44.149702+00:00 199 [[True, 0, 10], [True, 1, 7]] 0 none
2026-11-24T22:04:44.353790+00:00 200 [[True, 0, 10], [True, 1, 9]] 0 none
2026-11-24T22:04:45.895309+00:00 201 [[True, 0, 10], [True, 3, 4]] 0 none
2026-11-24T22:04:46.298074+00:00 203 [[True, 0, 4], [False, 3, 4]] 0 none
2026-11-24T22:04:46.625621+00:00 202 [[True, 0, 10], [True, 3, 5]] 0 none
2026-11-24T22:04:48.474277+00:00 205 [[True, 0, 4], [True, 4, 5]] 0 none
2026-11-24T22:04:48.725609+00:00 204 [[True, 0, 4], [True, 0, 5]] 0 none
2026-11-24T22:04:48.900673+00:00 209 [[True, 0, 4], [True, 0, 8]] 0 none
2026-11-24T22:04:50.726398+00:00 210 [[True, 0, 4], [True, 1, 6]] 0 none
2026-11-24T22:04:51.084425+00:00 211 [[True, 0, 4], [True, 1, 7]] 0 none
2026-11-24T22:04:51.165380+00:00 212 [[True, 0, 4], [True, 1, 9]] 0 none
2026-11-24T22:04:52.585765+00:00 213 [[True, 0, 4], [True, 3, 4]] 0 none
```

Complete per-class stdout/stderr logs are in scratch search/two-<index>.log. SHA256 manifest:

```text
f84ada9971d331b6656bb50731acfb4041c79d19d8a46e839467d893ffc78bc4  two-0.log
7c74645f05dcbe4e432906f0fbeb48fb6eed64566fa92f035c15317163eed48c  two-1.log
3a6f9510375451d9eabf6fe016b9bc171dccb1dcbee2d4bd996920d95eafbf62  two-2.log
013d57a913bdb660396efb2be6e2296c87980c46b72dceba182cc1dbc853f634  two-3.log
a17ec58c484a32b73e454b07f335379907a1194a43c5eeac183e7010e1a97030  two-4.log
308e3187efe25c53f1aa0d1ebc933ff7ac1207d944ba7648c409fea06be609f3  two-5.log
497f3b55b184ffbaa90e4af3bf0c464e727c7cb5ccddc4f0205fa01a295620a7  two-6.log
f7e1780890232319acb08e006f5eb86d574736e99f60b3ef02bbf3ef5f27bf5d  two-7.log
52fe57e87bc89b44781d44bb5b43eeddede2f9fde73175c0d0834ea41da1089a  two-8.log
4a273c9350753d58a5984bde04707f9d4aa4871ce1ac1c3fa6bec7d27d5b1196  two-9.log
a27a1a686b47a4ad98d7e58668feadbf3363ef00d77beffa4deea36e6feeb3b4  two-10.log
b4c4abcfa07d049fd10b533deff8c42d85c5231f0f67870d80d6e07cdcf46603  two-11.log
0e4ace202233cea607233e0650b9612fc7d60bf407b16543ff517ee33ce64feb  two-12.log
3daf556d679d6df5fa7f2d191239320607dd14513ebc5a10e0d7dd5d1e854f5d  two-13.log
e51a2ecef56daa6f4da1ad7fa6fcf43d41f321e8bf5eab6325513720d87472f6  two-14.log
9e78340f93ed9a8bb9153c5e9db1121b0b49e465d6dc2854b1bc6a98ed0f639a  two-15.log
284557613cc9692188d5310fe92afd4802172a8b73e42007a298fcc43bed1483  two-16.log
a98cbf350e46ecd24c37f4863c28c9824375741d513f22e75191932e373d1302  two-17.log
fdb8d2bac74eabe29cb053186312271215f98905419f8db500ebd24f719016ae  two-18.log
c6c6b4d7b3bb5b569979183b7cecdbdaffcc4d403a8f5500e3eacb74ca90f1b6  two-19.log
9d58d62aa9d6e952aedb02251ea05993458a572a9a12a97eedbd7801d4de685f  two-20.log
2a46a6da5eaaa9563edc844b5806d9def27b8e268ff7d7b30fdc460b99fc4c1e  two-21.log
e1a09dae70cd01cb184805888d7e6cfa9a295a9d1d2d7781ccb71297f3db7d4b  two-22.log
8441da256778d1d65936c3b0bc05b00d12260f8f9c1f3e718c325d2394b0cdca  two-23.log
54046a070343e648792633c867922fa13209e97e9b4ddc6ff9bc18a8c0b77649  two-24.log
e9581131c7c12d9d820a7e6c72ca29900e04b7c8ad9ad22e9088ae782e2fba71  two-25.log
a61b210e2bb23b8576a2b3fde9c2b846d53bedff456182e7f49d69c63d91f53d  two-26.log
5c8718dba2cf1c0c4c08c6b73862c44168f5569ea695fee31e9635bb74717fd5  two-27.log
f2fb54e61d2dadff628d6435786e76f54274ef46386823222c13469f2a8f7345  two-28.log
cd5a854013863e0bc9f2909821ee3750c420536691211d673512e91e918a1afa  two-29.log
7150c7ba0386cef89c236ab2d4e0c2ba41f70c69692cb31395e693f207e16033  two-30.log
7a5f238d9a750ee307b6af9ab891157b01b4fefd912591532191299a018ddb4c  two-31.log
5a1d5714424cf8d9752653d0df240d48a65e34d944699a4ae926770b755e4756  two-32.log
f7c789a3f5430d33eb0b7130a36cfd1220ed680ea5ce457939493c53cfb2a497  two-33.log
386e7a3a3395f0afcaa1a7e42e4ff1e74c0c13eded8bfc44f5063937f87b84d1  two-34.log
9b174f3ed27e75967d0c9b149163d679e545f49776f11ab7b508f41f83957c67  two-35.log
5866e9d6443dbfa1884e3403c5f30754e6e1d4ae540d51cc942bcf3ea563fa3b  two-36.log
45696cdb575e1c09a547842d144c0188f9f5b96043be9e3edfbaeb88aadf67e8  two-37.log
4f11683fd3cc82e5a7a9d5b056ba4c37af61311153fe5eb4d78cbfeeda69450b  two-38.log
8adfed0cd253929c29c5803a7fc2cf4a70b89886b90e4c45bd3140185602109d  two-39.log
fa110611f182308cf7e86a6bb65686f51a699ee1358a8a36f3ce696571d771f5  two-40.log
03cb64b0533c9b4a19f0677f2f4078b44076897553c5d6f997fcb04b8e733595  two-41.log
bbdd21b276fd2201f099484d08f88a0384aee990bacb4f57c623323eda658c42  two-42.log
07401b0c3ccc240414d86e325a39b2ad1da778d9d8864c9526c1ac3df72b2f65  two-43.log
606e6f8a69806c02a92ec95b9e5a229598cbfb5471bbacf3985b925cbc40c24a  two-44.log
81f277e93a4529266f9097b4811e090a48eb22a478a08b708547c6c1d8141fe1  two-45.log
afbe93913dba46ae90eef312f9f7767f91c03649b0c20d2b3a6a267323182810  two-46.log
d33759c6212ad25dce24a3be1bebe231b06466f537a0fd4a52d8497541e898ea  two-47.log
b18e13fad54e3ba9f163a5b792c22e5bcd20ba805003dad22731c29169f8953e  two-48.log
8d4d2d75ed60de665074201cc30930c11c8322eaaa4ea71d4efb5c377ed7b42d  two-49.log
55961b15758f8189c9cb0dddce0c923e4d211b32ee11c42b25aa54c24f54937b  two-50.log
8710c8cea2d00cd89c0bbd1803a5305ca76cfc98a55b967349e5fde8cd525cc1  two-51.log
0fcf7f65e462f2a1157f9b24b9ae5cf74818ff1d228dd47f5421e540f725c42e  two-52.log
c4a99b3cdf9afd7bc5edb6c63eed4d778491bf1397b1f39686eb943678665a3b  two-53.log
f0bb08f70db63475edbb96dafafc719d952dd7a8c35f4ab0d44a26784f35d10c  two-54.log
6f7b7f73d2cbdf9b1e42b0e93e3b50dd669ab7b526d22def68c601ebe035f987  two-55.log
899e1fc63dfe627bf14c8dfa8173417bdc3810a5c490a1fac810e7691384b0d7  two-56.log
14a77b0fdc46e1ea300e3a6b65158a8f384fb7bc4618f7962e7e7f27fb2d6def  two-57.log
e71a779a7356d36c4112d90ab4e226ff75cfc53c87d67509c9370533cef69dbb  two-58.log
bd67479c8f3bf9e5cfbf95e229a3b2f802a21a324b4b84738dca88dc9881ac57  two-59.log
d5cf100e0f7a43bfbca0e05eeca71539a98492d44aa26b0ca1f4c630f5eb95d9  two-60.log
f4b838acef5f3476b3e53cb323c0ad1c8f55974df3242cca55ff23e17f8b0f6e  two-61.log
344bdc97e13f4ad7fd400f4f32eb059ced89c5f8f058a86c531cce3a956e5477  two-62.log
fb85f5cbc51f2a5fd65cafe3d596024e7c34ad34c2244748c6d59613bf754dce  two-63.log
2a02008ffe41b1b2723dcd4aeecb09b68bb9c057d1f070486aad3e60623fb4e3  two-64.log
7481b9d6de2a0148a68d1d0983436cbbf4bd30fd9cfe37c6638a10021a9d5c77  two-65.log
a64b7c76a5dc7959c8fa6552cdf13c0e8ba194810866b708df2702e03fafa797  two-66.log
a5253768cae9aa81c7d97b6c77cc210dc12ca763246838b7ff7f337cad6245f9  two-67.log
ac1985fe921da4bc93e3b9b4c1f121c870396827026d716347d15af8524081cd  two-68.log
bb7b20074d02e97a5b97db0636a932ca63e54590c71e364fc39c4391babc53ec  two-69.log
2b5d7f03176e0500b738a0bf0520dce18b52340b0887b085a251372aafb83826  two-70.log
9e97f7692185ff984c3c3582219eb50ca7dd83d4c3022255d26da041846652bd  two-71.log
66796eaa6f5e912e64bcb614bedd8a84fc88c2dcaadbaeb9a86509ee45e3ab54  two-72.log
65c4259e05e10dd3b95844b0027d0618b3b9f90188a87a3d71bbc23cc2da9f83  two-73.log
516814205ea825d6ca426925cc32f02e893f8f68e2cde998671bc12104e9c91c  two-74.log
d44a6a8b4821666f02538dfc030b2892b8c302415481477b6cdcfb171ee4a661  two-75.log
a1f733804dd2b71d8b94673b1706b5577cfe2d6586cee124d04ed51c80681ee5  two-76.log
b056627d40aba85a1be546d72d4fe325a5bceea9803a31f28705f403007842fe  two-77.log
a17770f981e61d02d5381287a0e2ce6d4633ab1f77ceadeb2d06d9352d535552  two-78.log
9cb6183a7a531bd8e757dc65a399e38637070fee1dc82fd313aa7c9d6e81f2b1  two-79.log
60ce829fd1bfccd0944892e58f810816cac07e9f5848f9514f01412686a4fb8e  two-80.log
545b4f724e56e3beff314a93f9399d4b4709962b6b7265f7dc24f65ffa5d0ec9  two-81.log
4a584a5f9940debab40d5a08b6a29b72cea575cc0fab38a02beb1a38e975293f  two-82.log
70cada27fa0959e83b65fa158c89c30e19bff8aff5e495192c5f24710e515439  two-83.log
8475af71d1e471987303334e41bc272bf772b160be1f42910f0af83175c4f3c9  two-84.log
ef6690e9cc9c09aac12ae2d16f58c6ca82d79d3d96dfe4ea1dbb6a7f120021a7  two-85.log
72115888fbcd07996d6f87db61b261c943d59ebbec598bf37efbe3c56e3104b7  two-86.log
3bae53a8240d2eb6c4d62c98a9fececfbe6f22d53260cbeac1813dcf2cc297e3  two-87.log
a1b0eb1d95fd19f5470c53ecb3bfe73c4e20de572ad6eefaaaf1c34e27f88a8c  two-88.log
b4fbf8e2d33aebee1e1b6f1a0f667b283393787151582a067c5cd2b250b7ea76  two-89.log
83407d192582e905efa51a2a3844b6e7e7a4fa308425982228cc8373574bffe9  two-90.log
e96a1df4a2ae5e175e2de2659b513543bbed57a2ccae9c033c063ba18fede4fc  two-91.log
88ba122349154ae7e4ba44a95d6d8f1b5e90bd8637fc33904e8fe97126407643  two-92.log
6cb1512672d57ba0981008498bfcc07e57e0d356aedac2c41ebb1859c123bb83  two-93.log
da1585d921f8e70fd71feb6f6304da9404a1e621acbf9bbdc84598d04fd828f9  two-94.log
75ee472c4c5c270bc1eb60d586e8f795aea6155909f55211e0221dbfb27d243f  two-95.log
6394af19d50efb04f825f6593d31dbd18ad8deaaf6e9994b32bbc197e4434268  two-96.log
af4f03244fd0a185629ea9d6054914fe2a4f5387e7fff6241b12cebb518e395c  two-97.log
73cda5dc42910e3f3f7006a70e3d2bd1e2fd3d3d57b147923439e30f747c7e26  two-98.log
6f08ed302b7dc9b1a44e49dd985ca84f9c66aaac71aecd5ecbd94e55fa3f1a3d  two-99.log
b4dc1bfbb6b863d1b2ff030331639768208e683e194a2305e40975957c14f8ba  two-100.log
2d2c160b042f52a223fab0cb81e9adb5af0d57c1e4c2a0be69bada5b58ba4cae  two-101.log
3469507d7191986f4c831187a9cf0522a9966de17d57a8bc2c5c8fd3d093c142  two-102.log
68ef9f55d26639419895198eb17f821f2f780b2474ba6ffea0abdfbdea9d9539  two-103.log
2cc0cf5ee6dce33ae94be5c9ae0a86901edead872c2d218d451dd483ec84ed1f  two-104.log
65cc03b1db0c9be200fde75fd57c2c8a5481f1a4cc1f2a116f07c9075c654955  two-105.log
44404ffb227bb89ab201866d6dae18d987f1173bbefa2f5e61f8a3a4d75fabe5  two-106.log
08bca83e131ef95aa8ca4a87f1483cedad7938695be71f1141df3fc815290738  two-107.log
2529f13f1f6b8560237c5ac55f4aa3756dcac3c977d695206e13f074c44f79ea  two-108.log
8bc3815760a96cf6f0a4de47824c7936f7fb847cba8ff6e7b82faf58a726f1d7  two-109.log
04e084ddb2ac56503ee4c092a925ad7c8d0adfd78181e51b1d2352537705ab4f  two-110.log
bdf2c530efebd70da25294a62a46153089511229ab6d25d51afde356587423ee  two-111.log
e8abdfa3174424a14afe57758427de683e1c25f31f75809a7a9e6946e1a72970  two-112.log
ecd1684d13ee81524e008986aa152d4052f11751f6320f78b3dfe303b384d387  two-113.log
88c86980da3de4e535a13e937b243fdf3e78a31e8ca2b2d85901e2285423a647  two-114.log
406a3eaa4bdbc75789f461ade01834d481b54bf096c2b0e9cd46ab1d5264684f  two-115.log
518189733060368ea3780f5e3d3e9189fc32711da1d4e2140150c7cd2101b153  two-116.log
12c998e8ae4d2a61e1bb138fd2eb3d385f9ead79a8e5876c1fb31c78b751e00b  two-117.log
8d7aa0bd323f4a6595439fd1b56526c72130782ebd7150ffcba248f343118a87  two-118.log
7a96c1ae1ba8e88f7554359b3d3a9a222b4924a1536a9b0ec5676a20b1a64767  two-119.log
6493ba6127577a9f5f8f02cc35e422fc30b78796be534363c9fe375c6593cacf  two-120.log
cc61b13be52efa3d0ac9e8c347cdcd7e057034a4a38a93523c7d0b98e872b720  two-121.log
3e269231a3de26d72a1a1e1e0fc6491c31b71d5697adbc41743272790523da83  two-122.log
295c1d87501e9d692e759776597f9715d29bc34a3960ccf6f4e8bfdfd1db94e1  two-123.log
f29a42911bdbd2fa6ba9bc72d9400fba09acff135cf6f61aedd93d5d7573f7a9  two-124.log
75f58d2f63852e8606c668ce92ae06cd70664a346cd50cc15fe131642d6223d9  two-125.log
570bb4c0fc7009bce74a3af142e3f4bd2143ed6f963207dd89ba24c5763ed686  two-126.log
1feaa8966154ab3a1b7f6073193dc7292d4191a3f566a8226aef3db23dbd8dcb  two-127.log
7418552175aa781057e84bcd61d78a8d7211e5f9d131cd52860e0325a5fbc2c7  two-128.log
e295b2b41afc0f5513d6a78db6741b736766b187cfaed5ef25212beb919c4c35  two-129.log
e83cf61a3b35b96d30636296d2adcc5b1c6b5f9bb1514c85e71d8d9176b4d2c7  two-130.log
7349328aa8ea1112a79167bd8a28d7a7223f6593da6ea0c221a684d40af49e1d  two-131.log
68a3bdd806f87bf774500b9b09b2f909e372e061b25e2978c5fadedd61d3949a  two-132.log
d753e0b44660f34a0f01bfa7fcb24bcd3da1917b3b2d2265c5206a53716c8a52  two-133.log
4745c7da0ae87e7a5e29ee973d04a9659d8fa15e571fe609ee9f36ac64cc53af  two-134.log
c13a3e4e9fe8ab69cdebb63d143eeaf7579a4da2857d3766281aa86d73e5c5ca  two-135.log
97506f53ed378b70188e8e792560750ef34684835728714a0a83b5397e481f37  two-136.log
573e16b02d144b42e1f5f4438d57e397c9970d5add7498b833ae8e2ee5f13769  two-137.log
6c98ed87dd84888955c59c891b836fe8e6b8f68aed6384ebb73bdeb5b38caaac  two-138.log
df38eff8a0da4e79df9bcb5e73a7263676869e78b929a25d8dd6b41916e2adf3  two-139.log
7b81501b80f706c67dc3c7b8be02bb8b1dc2ea40aa2eb530a4a98d1829998c4c  two-140.log
8c867fb4f6006ad5acb7a2ee89fdc673f2ab8611bddbfdaa1522ff4dab1a9f27  two-141.log
fc4f0dc95a1d49b20f9f4df058b4c5e2d15b8f6834d9459eb006cacdc9549214  two-142.log
2731fd357d43548689d386eb5f586ce19de6d4672a15858525f90cf08bb53caf  two-143.log
2bd1a7a608b7f124359da0607351f40ef32918bc90299bab20531ed6d4855bb2  two-144.log
bee9798107e24ef3503cdad1cd11ac490d8261201635e021494a9d92082d5668  two-145.log
9d48541083026957ee6b4b5987fa57c61d1d4ca9bb09058be69176e31ae3fda7  two-146.log
5b37d76f5bb72cf06ce3facfd177e2b277e2e2263d65589ce6b3ee33d36cf62f  two-147.log
ebca1f11c00afd9f304a99bc3bba9baeac08ede7fc7349a948a5aa032dd68c47  two-148.log
58b583916a95848051ddbf22d3e5b0def5bac8242ebdece4a3f87310fce796e7  two-149.log
a1e8f65c950621eee1b7579a4fcd292e10efc5add236658c098ead0973fe1788  two-150.log
4ffb0a0667f4b327d745289bf849340c6d3c1a2b28044d93f184b5c1b67e4be6  two-151.log
b684ce17f31bf8651c8fb0554932533ec79ca3d8ac86559a00e9778be8909d23  two-152.log
32725d95566235fa090c872e99ee042e8d54956575f3b701b3c14140e2fc8428  two-153.log
67791e480ca1e6504409e516c19bda558c7872e5e84bc63d2b218294ac34b3c9  two-154.log
9707583f2e7aaccf64e655b3e715bdf24378ee79ebbb74da8e4d0212d6e96290  two-155.log
aaff806aa0e040b29947127b3005a326b5878fb6dfd0ec7e09f59914eac12fd1  two-156.log
320bcca61732c769842db1ab815f4cecdad86cff0e4360b5e7c8903dc68b1aa9  two-157.log
46cb7d95ad2ad7b1052d9fdbaa5ad4ef17dac33bcbb7c1039e6900fe50eab689  two-158.log
1821381d3571b99ae563f59f0166a4aacea3923e30301532f185ab46df452af7  two-159.log
7083b8ac5673db3dcc08d7b220a96b6a21f8ce18d1623b392eb1e0b20220b50f  two-160.log
8b6d9eeb106a94b6549ef02d672fc2eb23a2283e33241594eec03dc6fd112bb4  two-161.log
0307c650eee63af833f5338624c423fd21b57c9e36bc93eb6b608beadbb5a5d5  two-162.log
8ba29d61243dd82c0f1ee5d844adc757a92e4af7010e783edbb9d3964ede0e30  two-163.log
37e9624e7bc00ea89b3f1d6075fe3c744a7c5e3276174da0f4e1216843801e27  two-164.log
12f09af34c154a8b187ec41d177d8adc88128ef0a2f06e9f83618442eed3fbfb  two-165.log
2f7cda19c2f8c69454cd4a025aacb7dbcb577bf1c3075a62454f6f863d2e4a45  two-166.log
dc2a1471e9bcdc8b36b0df945f366edb8da115c6d3075ad7df8c2e5620118339  two-167.log
0d54d0daa542b6046b2d608dbce4cf141c9227d665d1d3a53abdfdf5f0876456  two-168.log
58d8c75a0bab927a67a00fcd584196c3e63496abfd6cea328310f4bfbb86fd39  two-169.log
2434d006395eda8041beb10f0f500185df116b882037340271f1b01f54306da9  two-170.log
588e519b4452f37a7fe01c7f38bd55d598e2a7659ab2d8ef144d07e0ca3e5eff  two-171.log
d6b540328e61c68a465fafb36d4dd0b0d9b8db75d78a26ea1711dcc9715aa17d  two-172.log
f7e8770b58ef7bde009de30921cb24822cb02148bc806f4fe1ed4dbb99b74d1b  two-173.log
23a3b6df0c79e0a931050b2136d5366bb431f4841e3466780d5907b71f53eb53  two-174.log
190c474459a9cd932ea4636bf091b8c741e9ec1d56f67b9ce9ab30f4c52b12c1  two-175.log
2898ed3c68b71285b019e539404eab3aee4c065eeec57fb0966a0a9ba9817fd7  two-176.log
be2f839ba99b46a11c78499cc6ee9abafc1b600ccb35cb7669eb88ada43893ac  two-177.log
41661175de25e41f0f13cdc8a7c5ded294c22a68c3c36823b4c7d7f82f66962a  two-178.log
1f50eadcb9d864c496ac6279cd6dae6881733a213975e5f22bdb148a0c98bb63  two-179.log
505ec7ec3c33178007ccbd6b00f7eff72c09f7d4a92657c3c07f5fcce2a928c1  two-180.log
4565c5e048e62df8eba493e12cc4333bdcc7202ffcd2ffe6888c99140ae8d068  two-181.log
9a3a43f6c0428edf2b7cc677c76a95693d185a5f7c93086fd24a177f93c4c03c  two-182.log
20d86fc3cc1a164be5c4838742912dd5d74789ae2a5b24cdea8bc9ed82d43069  two-183.log
c79f1222c8b281da26a55d0504750a8f3fc97fed7ae8ed9be8d1e709d107aaa2  two-184.log
c2c24bb9de2bf5c584ea4bd3705a5d9e71fe0adb4d537684d7cc3474b184440c  two-185.log
1081eb488c786298e1c82436064eb1257a56801af656e2ea7563c534e776758a  two-186.log
55f695c0944b024b9548868af61bc9509ade173c5d92246840af5fcc86f593fe  two-187.log
be46065d69f2b2f23026f9d839d4c993b33f674c98e834f0e2810586e9008a6e  two-188.log
fc73e6728781435f090e30e134d35111a63aeac0ee198b5123d3b85e71a83e00  two-189.log
d7cfa83fddb8968d204a7913d5b7d4c1fc9b2b2c33494200336e1a479058fc63  two-190.log
aca7c23828305c0dd730adcfcfbf9f24647cf11ec97391cfe19363622cf264e3  two-191.log
5c82a9af5bfd1ee2aab607e1d6a21fcdbd2e29038ca3a309fa50d79e6c068392  two-192.log
ac9ae7338cd20760dc24ad383df2bfa0982c081053589031c1ae5ac6999e8b91  two-193.log
902a2f6d334614caaf771f9c50c4a771ef47af4f1336c4fcbab94857acf503f8  two-194.log
5cb38433f694b0e2469b8ba6c8b1bc3d834bad1413502175ebf0689702dc5741  two-195.log
63e6a558932e4636b740bd978ce20dbd48aeefc2949443147bc3236379abc130  two-196.log
0241cc9560665d08dd9d4c4f91af379f5dc63af2356056ebcf01370eef496f98  two-197.log
7981319fe5959e14922d96816ad23d52d7157a546d406711f0deffe99d93dfe0  two-198.log
ef78e7f35194a832d4f7098367228f4b5cc77e988b2bbcfe6f76299454c30630  two-199.log
fbed6e850a401ffde1d60ca3a1ec1ca485e79a495fcbbb3440f92d433fe32159  two-200.log
9bb5cc8c9a94bb65eab5aa5e44b2ae8692119104f63c427453672b5b8b786ea5  two-201.log
0850aa9f900f8d02b088f42e80b9977c0a9143666f435e36066ce4845f128c0a  two-202.log
4989b5af46f1289f92ab054f2d4612da40fb9309135bca8379c0cac5a06dec75  two-203.log
bb24c586e515799834dee2d262b7463250a9a5bb57789654b5842804b3b929fb  two-204.log
98416663981fc758bbbbd67e9ecc29810c63f06e09a4280bd26656f3054efd39  two-205.log
a4affeb6b0c02160ef851efd2a2ddc2ccf08de9dca0a36c5dd9c4544a167c99f  two-206.log
8e9973f9b0061d1c274c467ea18b7ac73edd0ae2ece30862a27d63be050f255a  two-207.log
3c6363588c0308f4c802d3f1a760819ce7fbd8e4bda7c283e9348cfae042c85c  two-208.log
15a6c399b12b53e8a02f6480836a24ef36dac8bfa130f515c3abb48aa9f30eb1  two-209.log
d50f4428823154fee088a24f62c5632a5c714e2ee02af6af0e163f92384f88c6  two-210.log
99834032459b209132d902c303292ac502e3c3004c1cf1386e99ad8a344006be  two-211.log
75f2abade0cc48e6c3972332039e3ad9e5d8b184dc9fcaad85c5e1e5a1818270  two-212.log
55ebfee50bd6921b516bae5934c2dd25dfc7c364b46681d633e54187bc97b762  two-213.log
```
