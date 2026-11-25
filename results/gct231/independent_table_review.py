"""Parse the frozen Lean table and independently check every injective triple."""
import ast
from collections import Counter
import hashlib
from pathlib import Path
import re


base=Path('/tmp/oec/pequalnp-pilot-75/gct231')
source=base/'EdgeOrbitsTable.lean'
text=source.read_text()
sha=hashlib.sha256(source.read_bytes()).hexdigest()
assert sha=='c3ddd441498587ace5f3e636d6ee7e9dd31acfa231af71dcac061b3bbe0d1680'
vertices=[ast.literal_eval('['+t+']') for t in re.findall(r'Equiv\.ofBijective \(!\[([^\]]*)\] : Fin 4 → Fin 4\)',text)]
coordinates=[ast.literal_eval('['+t+']') for t in re.findall(r'Equiv\.ofBijective \(!\[([^\]]*)\] : Fin 3 → Fin 3\)',text)]
assert len(vertices)==24 and len({tuple(p) for p in vertices})==24
assert all(sorted(p)==list(range(4)) for p in vertices)
assert len(coordinates)==6 and len({tuple(p) for p in coordinates})==6
assert all(sorted(p)==list(range(3)) for p in coordinates)
chunk=text.split('def orbitWitness :',1)[1].split(':=',1)[1].split('set_option',1)[0].strip()
table=ast.literal_eval(chunk.replace('![','['))
assert len(table)==6 and all(len(a)==6 and all(len(b)==6 for b in a) for a in table)
edges=[(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]
canonical=[[0,1,2],[0,1,3],[0,3,5]]
assert ' ![(0,1), (0,2), (0,3), (1,2), (1,3), (2,3)]' in text
assert ' ![![0,1,2], ![0,1,3], ![0,3,5]]' in text
counts=Counter()
checked=0
for a in range(6):
 for b in range(6):
  for c in range(6):
   pi,qi,kind=table[a][b][c]
   assert 0<=pi<24 and 0<=qi<6 and 0<=kind<3
   if len({a,b,c})<3:continue
   p,q=vertices[pi],coordinates[qi]
   for k in range(3):
    edge=edges[[a,b,c][q[k]]]
    image=tuple(sorted((p[edge[0]],p[edge[1]])))
    assert image==edges[canonical[kind][k]],(a,b,c,k,image)
   counts[kind]+=1
   checked+=1
assert checked==120 and counts=={0:24,1:24,2:72}
print('Source SHA256',sha)
print('24 vertex permutations and 6 coordinate permutations checked')
print('All216 table entries have valid indices')
print('All120 injective triples checked at all3 coordinates')
print('Orbit counts:',dict(sorted(counts.items())))
print('PASS')
