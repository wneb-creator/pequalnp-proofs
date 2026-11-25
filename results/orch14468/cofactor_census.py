from pathlib import Path
import re,json,ast
E=[(0,4),(1,5),(0,6),(2,6),(0,7),(1,7),(2,7),(3,7),(5,7)]
def adj(ed):
 a=[set()for _ in range(7)]
 for u,v in ed:a[u].add(v);a[v].add(u)
 return a
def iso(a,b):
 if sorted(map(len,a))!=sorted(map(len,b)):return None
 order=sorted(range(7),key=lambda x:-len(a[x]));m={};used=set()
 def go(j):
  if j==7:return dict(m)
  x=order[j]
  for y in range(7):
   if y in used or len(a[x])!=len(b[y]):continue
   if any((z in a[x])!=(m[z]in b[y])for z in m):continue
   m[x]=y;used.add(y);r=go(j+1)
   if r is not None:return r
   del m[x];used.remove(y)
  return None
 return go(0)
def Gdel(v):
 keep=[x for x in range(8)if x!=v];return adj([(keep.index(a),keep.index(b))for a,b in E if v not in[a,b]])
Ts={v:Gdel(v)for v in range(8)};matches=[];cand=0
files=Path('/tmp/oec/pequalnp-pilot-103/14468-seven-files.txt').read_text().splitlines()
for name in files:
 s=Path(name).read_text();tail=s[-14000:]
 pats=re.findall(r'\[\s*\d+[\d\s,]*\]\s*:\s*List (?:ℕ|Nat)',tail)
 pats+=re.findall(r'\[\s*\(\s*\d+\s*,\s*\d+\s*\)[\d\s,()]*\]\s*:\s*List \((?:ℕ|Nat) × (?:ℕ|Nat)\)',tail)
 seen=set()
 for pat in pats:
  a=ast.literal_eval(pat.split(']')[0]+']')
  if not a:continue
  if isinstance(a[0],int):
   if len(a)%2:continue
   ed=list(zip(a[::2],a[1::2]))
  else:ed=a
  if not ed or max(max(e)for e in ed)>6 or min(min(e)for e in ed)<0:continue
  if len(ed)not in[4,5,6,7,8,9]:continue
  key=tuple(sorted(ed))
  if key in seen:continue
  seen.add(key);cand+=1;g=adj(ed)
  for v,t in Ts.items():
   m=iso(g,t)
   if m is not None:matches.append({'file':name,'deleted_vertex':v,'edges':ed,'mapping_to_cofactor':m})
Path('results/orch14468/seven-cofactor-census.json').write_text(json.dumps({'selected_files':len(files),'graph_candidates':cand,'matches':matches},indent=2)+'\n');print('candidates',cand,'matches',matches)
