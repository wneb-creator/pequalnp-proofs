"""Build finite five-point incidence models and their point-permutation actions."""
from pathlib import Path
import functools,itertools,collections,ctypes,json,sys
job=Path(__file__).resolve().parent;cfg=int(sys.argv[1]);data=json.loads((job/'fresh-meta3773-five-point-types.json').read_text())[cfg];point_count=len(data['points']);raw_count=data['raw_count'];E=list(map(tuple,data['E']));P=[(1<<i)|(1<<j)for i,j in E];N=data['negative_maximal'];rows=P+N;NP=len(P);NT=len(rows);M=(1<<NT)-1;target=(1<<NP)-1;raw=[sum(1<<i for i,r in enumerate(rows) if r>>j&1)for j in range(raw_count)];support=[set(v)for v in data['free']];free=[sum(1<<i for i,r in enumerate(rows)if any(r>>j&1 for j in V))for V in support];Nbs=[{i for i,ell in E if ell==j} for j in range(point_count,raw_count)]
perms=[]
for q in itertools.permutations(range(point_count)):
 line_image=[{q[i] for i in B}for B in Nbs]
 if any(B not in Nbs for B in line_image):continue
 pi=tuple(q)+tuple(point_count+Nbs.index(B)for B in line_image);assert sorted(pi)==list(range(raw_count));
 if any({pi[j] for j in S} not in support for S in support):continue
 perms.append(pi)
@functools.lru_cache(maxsize=6000)
def trees(F):
 if len(F)==1:return frozenset(F)
 vals=set();n=len(F)
 for s in range(1,(1<<n)-1,2):
  l=tuple(f for i,f in enumerate(F)if s>>i&1);r=tuple(f for i,f in enumerate(F)if not s>>i&1)
  for a in trees(l):
   for b in trees(r):vals.add(a&b);vals.add(a|b)
 return frozenset(vals)
def monotone_outputs(F):
 known={0,(1<<(2*NT))-1,*F};current=known.copy()
 while current:
  nxt={x for a in current for b in known for x in (a|b,a&b)}-known;known|=nxt;current=nxt
 return known
shared=ctypes.CDLL(str(job/'fresh-meta3773-readonce-ext.so'));shared.feasible.argtypes=[ctypes.c_int,ctypes.POINTER(ctypes.c_uint64),ctypes.c_uint64,ctypes.c_uint64];shared.feasible.restype=ctypes.c_int
@functools.lru_cache(maxsize=12000)
def feasible(F,Pneed,Nneed):
 a=(ctypes.c_uint64*len(F))(*F);out=shared.feasible(len(F),a,Pneed,Nneed);assert out in (0,1);return bool(out)
