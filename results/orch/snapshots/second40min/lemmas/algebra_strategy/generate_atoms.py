import json,random,itertools
from pathlib import Path
rng=random.Random(65057)
base=Path("results/orch/lemmas")
d=json.loads((base/"circuit_search/subsets/k6_p3.json").read_text())
neighbors={r:[b for a,b in d["edges"] if a==r] for r in range(6)}
edgeatoms=[(0,a,b) for a,b in d["edges"]]
lineatoms=list(dict.fromkeys((1,a,b) for r in range(6) for a,b in itertools.combinations(neighbors[r],2)))
pointatoms=[(1,a,b) for a,b in itertools.combinations(range(6),2)]
mixedatoms=[(1,a,b) for a in range(6) for b in range(6,17)]
seeds=[]
for mode in range(4):
 for repetition in range(60):
  if mode==0: atoms=edgeatoms+rng.sample(pointatoms,6)+rng.sample(mixedatoms,4)
  elif mode==1: atoms=rng.sample(lineatoms,30)+rng.sample(pointatoms,2)+rng.sample(mixedatoms,2)
  elif mode==2: atoms=rng.sample(lineatoms,18)+rng.sample(edgeatoms,12)+rng.sample(pointatoms,4)
  else: atoms=rng.sample(lineatoms,12)+rng.sample(edgeatoms,12)+rng.sample(pointatoms,5)+rng.sample(mixedatoms,5)
  rng.shuffle(atoms)
  gates=[]; known={}
  def gate(op,a,b):
   key=(op,min(a,b),max(a,b))
   if key not in known:
    known[key]=17+len(gates); gates.append(list(key))
   return known[key]
  for op,a,b in atoms: gate(op,a,b)
  rows=list(range(6));rng.shuffle(rows);stars=[]
  for row in rows:
   ns=neighbors[row].copy();rng.shuffle(ns)
   if rng.randrange(2): val=gate(1,gate(1,ns[0],ns[1]),gate(1,ns[2],ns[3]))
   else: val=gate(1,gate(1,gate(1,ns[0],ns[1]),ns[2]),ns[3])
   stars.append(gate(0,row,val))
  while len(stars)>1:
   i=rng.randrange(len(stars));a=stars.pop(i);j=rng.randrange(len(stars));b=stars.pop(j)
   stars.append(gate(1,a,b))
  output=stars[0]
  assert output==17+len(gates)-1
  assert len(gates)<=63
  for mask,target in d["tests"]:
   values=[bool(mask>>i&1) for i in range(17)]
   for op,a,b in gates:values.append(values[a] or values[b] if op else values[a] and values[b])
   assert values[output]==bool(target)
  seeds.append({"mode":mode,"gates":gates,"output":output})
out=base/"algebra_strategy/k6_p3_atom_rich_seeds.json"
out.write_text(json.dumps(seeds))
print(f"{len(seeds)} exact seeds, gate range {min(len(s['gates']) for s in seeds)}..{max(len(s['gates']) for s in seeds)}; all76tests pass")
