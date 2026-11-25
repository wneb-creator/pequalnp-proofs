#!/usr/bin/env python3
"""Exploratory live-wire lower-bound search. No result is a Lean certificate yet.

Operations track full 1024-row truth tables. Rejections use distinguished-row
coverage and restriction lower bounds inherited from checked small graph files.
The printed unresolved frontier is evidence of the remaining search, not a proof.
"""
import argparse, ast, collections, ctypes, functools, gzip, itertools, json, pickle, random, re, time
from pathlib import Path

P=argparse.ArgumentParser()
P.add_argument('--depth',type=int,default=2)
P.add_argument('--seconds',type=float,default=60)
P.add_argument('--limit',type=int,default=200000)
P.add_argument('--nine-lower',type=int,default=15)
P.add_argument('--seed-live',type=int,default=1)
P.add_argument('--pairs',type=int,default=225)
P.add_argument('--clip-seed',action='store_true')
P.add_argument('--cap',type=int,default=18)
P.add_argument('--examples',type=int,default=20)
P.add_argument('--exact-cover',action='store_true')
P.add_argument('--memo',action='store_true')
P.add_argument('--symmetry',action='store_true')
P.add_argument('--fast-cover',type=str)
P.add_argument('--checkpoint',type=str)
P.add_argument('--resume',type=str)
P.add_argument('--max-nots',type=int)
P.add_argument('--markov-one',action='store_true')
P.add_argument('--prune-restriction-dag',action='store_true')
P.add_argument('--chain-certificates',type=str)
A=P.parse_args()
if not 0 <= A.nine_lower <= 16:
 P.error('--nine-lower must be between0and16;16requires checkedminor theorem')
if A.clip_seed and A.seed_live:
 P.error('--clip-seed requires --seed-live0: a constant cannotbealive root')
if A.max_nots is not None and not 0<=A.max_nots<=A.cap:
 P.error('--max-nots must be nonnegativeandatmostcap')
if (A.checkpoint or A.resume) and (not A.memo or A.depth<A.cap):
 P.error('checkpoints require memoization and full depth at least thecap')
N=10; R=1<<N; ALL=(1<<R)-1
EDGES=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
E9=[(u,v) for u,v in EDGES if u!=9 and v!=9]
RAW=[sum(1<<r for r in range(R) if r>>i&1) for i in range(N)]
GOAL=functools.reduce(int.__or__,(RAW[u]&RAW[v] for u,v in EDGES))
SEED=RAW[0]&RAW[2]
CLIP=ALL^SEED if A.clip_seed else ALL
RAW=[w&CLIP for w in RAW]
GOAL&=CLIP
SEED&=CLIP
POS=[(1<<u)|(1<<v) for u,v in EDGES]
NEG=[r for r in range(R) if not(GOAL>>r&1) and all(GOAL>>(r|(1<<i))&1 for i in range(N) if not(r>>i&1))]
PAIRS=list(itertools.product(POS,NEG))
rng=random.Random(1890)
seen_pairs=set(PAIRS)
allpos=[r for r in range(R) if GOAL>>r&1]
allneg=[r for r in range(R) if not(GOAL>>r&1)]
while len(PAIRS)<A.pairs:
 pair=(rng.choice(allpos),rng.choice(allneg))
 if pair not in seen_pairs:
  seen_pairs.add(pair); PAIRS.append(pair)
FULL=(1<<len(PAIRS))-1
@functools.lru_cache(None)
def sig(w):
 p=sum(1<<i for i,(r,s) in enumerate(PAIRS) if w>>r&1)
 q=sum(1<<i for i,(r,s) in enumerate(PAIRS) if w>>s&1)
 return p,q

def graph(mask,edges):
 vs=[i for i in range(N) if mask>>i&1]
 return tuple(tuple(j for j in vs if (i,j) in edges or (j,i) in edges) for i in vs),vs

def key(mask,edges):
 adj,vs=graph(mask,edges)
 return (len(vs),len([1 for u,v in edges if mask>>u&1 and mask>>v&1]),tuple(sorted(map(len,adj))))

def iso(mask1,edges1,mask2,edges2):
 a,vs=graph(mask1,edges1); b,ws=graph(mask2,edges2)
 da=dict(zip(vs,map(set,a))); db=dict(zip(ws,map(set,b)))
 order=sorted(vs,key=lambda v:(-len(da[v]),v))
 def go(k,m,used):
  if k==len(vs): return True
  v=order[k]
  for w in ws:
   if w in used or len(db[w])!=len(da[v]): continue
   if any(((u in da[v])!=(m[u] in db[w])) for u in m): continue
   m[v]=w
   if go(k+1,m,used|{w}): return True
   del m[v]
  return False
 return go(0,{},set())

s=Path('lean/PEqualNP/Outside/L_meta_1668.lean').read_text()
small={}
for m in re.finditer(r'def known(\d+) := extendKnown \S+ (\d+) maps\1',s):
 rep,L=map(int,m.groups())
 maps=re.search(r'def maps'+str(rep)+r' : List \(Nat × List Nat\) := (\[[^\n]*\])',s)
 if maps:
  for a,swaps in ast.literal_eval(maps.group(1)): small[a]=max(L,small.get(a,0))
 # The proved representative exists even if not recorded in known for later use.
 small[rep]=max(L,small.get(rep,0))
classes=collections.defaultdict(list)
for m,L in small.items(): classes[key(m,E9)].append((m,L))
LOW={}
for m in range(1<<N):
 used={v for e in EDGES if all(m>>x&1 for x in e) for v in e}
 mm=sum(1<<v for v in used)
 if mm!=m:
  continue
 lb=max(0,len(used)-1)
 if len(used)==9: lb=max(lb,A.nine_lower)
 for k,L in classes.get(key(m,EDGES),[]):
  if L>lb and iso(m,EDGES,k,E9): lb=L
 LOW[m]=lb
for m in range(1<<N):
 used={v for e in EDGES if all(m>>x&1 for x in e) for v in e}
 LOW[m]=LOW.get(sum(1<<v for v in used),0)

# Subcube restrictions with up to two fixed coordinates. On a nonconstant
# restriction, vertices adjacent to a fixed1 become independent OR terms.
RESTR=[]
for fixed in range(1<<N):
 if fixed.bit_count() not in [1,2]: continue
 for ones in range(1<<N):
  if ones&~fixed: continue
  if any(ones>>u&1 and ones>>v&1 for u,v in EDGES): continue
  zero=fixed^ones
  if A.clip_seed and not(zero&5): continue
  free=((1<<N)-1)^fixed
  singles={v for u,v in EDGES if ones>>u&1 and free>>v&1}|{u for u,v in EDGES if ones>>v&1 and free>>u&1}
  residual=free^sum(1<<v for v in singles)
  lb=LOW[residual]+len(singles) if LOW[residual] else max(0,len(singles)-1)
  if lb<6: continue
  domain=sum(1<<r for r in range(R) if r&fixed==ones)
  # Root basis includes each unfixed input and constants. Original seed is paid
  # once if proper and not a root on this subcube.
  roots={0,domain}|{RAW[i]&domain for i in range(N)}
  seed=SEED&domain
  bank={r:0 for r in roots}; paid=0
  if A.seed_live and seed not in bank: bank[seed]=1; paid=1
  RESTR.append((domain,lb,bank,paid,fixed,ones))
RESTR.sort(key=lambda t:-t[1])
print(json.dumps({'rows':len(PAIRS),'positive':len(POS),'negative':len(NEG),'restrictions':len(RESTR),'known_graphs':len(small),'lower_histogram':dict(collections.Counter(LOW.values()))}),flush=True)

ADJ={i:{v for u,v in EDGES if u==i}|{u for u,v in EDGES if v==i} for i in range(N)}
AUTOS=[]
def auto_search(m,used):
 if len(m)==N:
  AUTOS.append(tuple(m[i] for i in range(N))); return
 i=next(v for v in [0,2,1,3,4,5,6,7,8,9] if v not in m)
 for j in range(N):
  if j in used or ((i in (0,2))!=(j in (0,2))): continue
  if any(((v in ADJ[i])!=(m[v] in ADJ[j])) for v in m): continue
  m[i]=j; auto_search(m,used|{j}); del m[i]
if A.symmetry: auto_search({},set())
LUTS=[]
for perm in AUTOS:
 if perm==tuple(range(N)): continue
 invrow=[0]*R
 for r in range(R):
  dest=sum(((r>>i)&1)<<perm[i] for i in range(N))
  invrow[r]=dest
 tables=[]
 for start in range(0,R,8):
  tab=[0]*256
  for v in range(1,256):
   bit=v&-v; ix=bit.bit_length()-1
   tab[v]=tab[v^bit]|(1<<invrow[start+ix])
  tables.append(tab)
 LUTS.append(tables)
@functools.lru_cache(maxsize=200000)
def permwords(w):
 ans=[]
 for tabs in LUTS:
  t=w; out=0
  for tab in tabs:
   out|=tab[t&255]; t>>=8
  ans.append(out)
 return ans

def canonical(ws):
 if not A.symmetry: return ws
 images=[[] for _ in LUTS]
 for w in ws:
  for j,v in enumerate(permwords(w)): images[j].append(v)
 return min([ws]+[tuple(sorted(v)) for v in images])

START=time.monotonic(); visited=set(); active=set()
if A.resume:
 with gzip.open(A.resume,'rb') as f:
  checkpoint=pickle.load(f)
 assert checkpoint['mode']==('budget-siblings-v2',A.clip_seed,A.seed_live,A.cap,A.nine_lower,A.symmetry,A.max_nots)
 visited=checkpoint['closed']
 print(json.dumps({'loaded_closed_states':len(visited)}),flush=True)
stats=collections.Counter(); depth_stats=collections.Counter(); frontier=[]; nodes=0
class FoundTarget(Exception):
 pass

# Each restriction bank includes only semantically distinct nonconstant gate
# values observed so far. Reusing equal restrictions saves a gate soundly.
CHAIN_WITNESSES=set()
CHAIN_CERTIFICATES=[]
FAST=None
CHAIN=None
if A.fast_cover:
 FAST=ctypes.CDLL(A.fast_cover).exact_cover
 FAST.argtypes=[ctypes.c_uint,ctypes.c_void_p,ctypes.c_void_p,ctypes.c_int]
 FAST.restype=ctypes.c_int
 GOAL_BYTES=GOAL.to_bytes(128,'little')
 if A.markov_one:
  CHAIN=ctypes.CDLL(A.fast_cover).one_not_chain
  CHAIN.argtypes=[ctypes.c_uint,ctypes.c_void_p,ctypes.c_void_p,ctypes.c_void_p]
  CHAIN.restype=ctypes.c_int

def exact_separation_python(ws,oriented):
 if oriented:
  for r in allneg:
   possible=GOAL
   for w in ws:
    if not(w>>r&1): possible&=ALL^w
    if not possible: break
   if possible: return False
  return True
 groups=[ALL]
 for w in ws:
  nxt=[]
  nw=ALL^w
  for g in groups:
   for h in [g&w,g&nw]:
    if h&GOAL and h&(ALL^GOAL): nxt.append(h)
  groups=nxt
  if not groups: return True
 return not groups

def exact_separation(ws,oriented):
 if FAST is not None:
  bank=b''.join(w.to_bytes(128,'little') for w in ws)
  return bool(FAST(len(ws),bank,GOAL_BYTES,int(oriented)))
 return exact_separation_python(ws,oriented)

def cuts(ws,cap,rs,z=None,force_oriented=False,one_not=False,parents=None):
 if GOAL in ws: return 'target',rs
 if len(ws)>cap+1: return 'count',rs
 p=0; oriented=len(ws)==cap+1 or force_oriented
 if A.exact_cover:
  if not exact_separation(ws,oriented): return 'cover',rs
 else:
  for w in ws:
   a,b=sig(w); p|=(a&~b) if oriented else (a^b)
  if p!=FULL: return 'cover',rs
 if one_not and CHAIN is not None:
  out=(ctypes.c_uint16*4)()
  bank=b''.join(w.to_bytes(128,'little') for w in ws)
  if CHAIN(len(ws),bank,GOAL_BYTES,out):
   rows=list(out)
   assert all(0<=r<R for r in rows)
   assert all((GOAL>>r&1)==int(i%2==0) for i,r in enumerate(rows))
   assert all(not(w>>rows[i]&1) or (w>>rows[i+1]&1) for w in ws for i in range(3))
   CHAIN_WITNESSES.add(tuple(rows))
   if len(CHAIN_CERTIFICATES)<10:
    CHAIN_CERTIFICATES.append({'target':hex(GOAL),'wires':[hex(w) for w in ws],'cap':cap,'rows':rows,'width_forced':cap<=len(ws)})
   return 'markov_one',rs
 next_rs=[]
 for domain,lb,bank,paid,fixed,ones in rs:
  if z is not None:
   zz=z&domain
   if zz not in bank:
    assert parents is not None
    ancestors=bank[parents[0]&domain]|bank[parents[1]&domain]|(1<<paid)
    bank=bank|{zz:ancestors}; paid+=1
  const=sum((w&domain) in (0,domain) for w in ws)
  if cap+paid<lb+const: return 'restriction',rs
  if A.prune_restriction_dag:
   ancestors=0
   for w in ws: ancestors|=bank[w&domain]
   if cap+ancestors.bit_count()<lb+const: return 'restriction_dag',rs
  next_rs.append((domain,lb,bank,paid,fixed,ones))
 return None,next_rs

def visit(ws,cap,rs,depth,path,z=None,used_nots=0,parents=None):
 global nodes
 nodes+=1
 depth_stats[depth]+=1
 if nodes%50000==0:
  print(json.dumps({'progress_nodes':nodes,'elapsed':time.monotonic()-START,'stats':dict(stats),'depths':dict(depth_stats),'path':path}),flush=True)
 if nodes>=A.limit or time.monotonic()-START>A.seconds: raise TimeoutError
 if A.max_nots is not None and used_nots>A.max_nots:
  stats['not_budget']+=1; return
 effective_not=cap+1-len(ws)
 if A.max_nots is not None: effective_not=min(effective_not,A.max_nots-used_nots)
 tag,rs=cuts(ws,cap,rs,z,effective_not==0,effective_not==1,parents)
 if tag:
  stats[tag]+=1
  if tag=='target':
   frontier.append({'path':path,'target':True})
   raise FoundTarget
  return
 if A.memo:
  key=(cap,None if A.max_nots is None else A.max_nots-used_nots,canonical(ws))
  if key in visited:
   stats['transposition']+=1; return
  visited.add(key)
  active.add(key)
 if depth==A.depth:
  stats['frontier']+=1
  if len(frontier)<A.examples: frontier.append({'path':path,'cap':cap,'live':len(ws)})
  return
 stats['expand']+=1
 seen=set()
 for i,a in enumerate(ws):
  ops=[('N',i,i,ALL^a)]
  for j,b in enumerate(ws[:i]): ops.extend([('A',i,j,a&b),('O',i,j,a|b)])
  for op,i,j,z in ops:
   if z in ws or z in (0,ALL): continue
   for ka,kb in ([(False,False),(True,False)] if op=='N' else itertools.product([False,True],repeat=2)):
    keep={i} if ka else set()
    if kb: keep.add(j)
    rem={i,j}-keep
    child=tuple(sorted([w for idx,w in enumerate(ws) if idx not in rem]+[z]))
    sibling_key=(child,used_nots+int(op=='N')) if A.max_nots is not None else child
    if sibling_key in seen: continue
    seen.add(sibling_key)
    # Restricted banks update lazily, after information-loss pruning.
    visit(child,cap-1,rs,depth+1,path+[(op,i,j,ka,kb)],z,used_nots+int(op=='N'),(ws[i],ws[j]))
 if A.memo: active.remove(key)

try: visit(tuple(sorted(RAW+([SEED] if A.seed_live else []))),A.cap,RESTR,0,[])
except TimeoutError: stats['interrupted']+=1
except FoundTarget: stats['target_found']+=1
if A.chain_certificates:
 Path(A.chain_certificates).write_text(json.dumps(CHAIN_CERTIFICATES)+'\n')
if A.checkpoint:
 with gzip.open(A.checkpoint,'wb') as f:
  pickle.dump({'mode':('budget-siblings-v2',A.clip_seed,A.seed_live,A.cap,A.nine_lower,A.symmetry,A.max_nots),'closed':visited-active},f,protocol=5)
print(json.dumps({'elapsed':time.monotonic()-START,'nodes':nodes,'stats':dict(stats),'frontier_examples':frontier,'memo_states':len(visited),'closed_states':len(visited-active),'automorphisms':len(AUTOS),'depths':dict(depth_stats),'markov_witnesses':len(CHAIN_WITNESSES),'markov_examples':sorted(CHAIN_WITNESSES)[:5]}),flush=True)
