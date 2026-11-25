from pathlib import Path
import ast,re,itertools, collections
job=Path('/tmp/oec/pequalnp-pilot-79');seen={};counts=collections.Counter()
for name in (job/'fresh-meta3773-eight-catalog-files.txt').read_text().splitlines():
 for idx,line in enumerate(Path(name).read_text().splitlines()):
  if 'size =' not in line or 'Fin 8 → Bool' not in line:continue
  for m in re.finditer(r'size = (\d+).*?\∈ \((\[\(\d+, \d+\).*?\]) : List \(ℕ × ℕ\)\)',line):
   try:edges=tuple(sorted(ast.literal_eval(m[2])))
   except Exception:continue
   g=int(m[1]);seen[edges]=min((g,name,idx+1),seen.get(edges,(10000,None,None)))
print('catalog',len(seen),'files',len((job/'fresh-meta3773-eight-catalog-files.txt').read_text().splitlines()))
for edges,(g,name,ln) in seen.items():
 nei={i:set()for i in range(8)}
 for a,b in edges:nei[a].add(b);nei[b].add(a)
 if any(len(nei[i]&nei[j])>=2 for i,j in itertools.combinations(range(8),2)): continue
 if not any(all(((mask>>i)^(mask>>j))&1 for i,j in edges) for mask in range(256)): continue
 cover=min(mask.bit_count() for mask in range(256) if all(mask&(1<<i|1<<j) for i,j in edges)); baseline=len(edges)+cover-1
 counts[g-baseline]+=1
 if g<baseline:print('IMPROVED',g,baseline,name,ln,edges)
print('C4-free bipartite sizes relative to optimal flat star cover',dict(counts))
