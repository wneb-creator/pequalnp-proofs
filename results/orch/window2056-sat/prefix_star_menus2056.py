import functools,itertools,json
from pathlib import Path
p=Path('/tmp/oec/pequalnp-pilot-121/window2056-sat')
d=json.loads((p/'reused32-prefix12-2056.data.json').read_text());n=d['n'];edges=d['edges'];rows=d['rows'];base=d['ordered_gates'][:12]
@functools.lru_cache(None)
def trees(leaves):
 if len(leaves)==1:return (leaves[0],)
 ans=[]
 for mask in range(1,(1<<len(leaves))-1):
  if not mask&1:continue
  a=tuple(v for i,v in enumerate(leaves) if mask>>i&1);b=tuple(v for i,v in enumerate(leaves) if not mask>>i&1)
  ans.extend((x,y) for x in trees(a) for y in trees(b))
 return tuple(ans)
menus=[]
for point in [2,4]:
 neighbors=tuple(sorted(v for u,v in edges if u==point));assert len(neighbors)==4
 menu=trees(neighbors);assert len(menu)==15;menus.append(menu)
N=1<<n;iv=[]
for i in range(n):
 step=1<<i;iv.append((((1<<step)-1)<<step)*((1<<N)-1)//((1<<(2*step))-1))
def evaluate(net):
 vals=iv.copy()
 for j,(op,a,b) in enumerate(net):
  assert op in(0,1) and 0<=a<n+j and 0<=b<n+j
  vals.append(vals[a]&vals[b] if op==0 else vals[a]|vals[b])
 return vals
expected=evaluate(base)[-1];variants=[]
for ta,tb in itertools.product(*menus):
 net=[x.copy() for x in base[:3]]
 def emit(t):
  if isinstance(t,int):return t
  a,b=sorted((emit(t[0]),emit(t[1])));net.append([1,a,b]);return n+len(net)-1
 star=[]
 for point,t in [(2,ta),(4,tb)]:
  wire=emit(t);net.append([0,point,wire]);star.append(n+len(net)-1)
 net.append([1,min(star),max(star)])
 assert len(net)==12 and evaluate(net)[-1]==expected
 variants.append(net)
assert len(variants)==225 and len({json.dumps(x) for x in variants})==225
assert base in variants
out={'n':n,'rows':rows,'edges':edges,'prefix_size':12,'fixed_dirty_gates':3,'points':d['points'],'lines':d['lines'],'star_points':[2,4],'variants':variants,'original_variant':variants.index(base),'full_assignments_verified_per_variant':N,'full_prefix_output_mismatches':0}
(p/'reused28-prefix-star-menus-2056.json').write_text(json.dumps(out,indent=2))
print(json.dumps({k:v for k,v in out.items() if k not in ['rows','edges','variants']}))
