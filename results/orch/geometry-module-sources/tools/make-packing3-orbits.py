import json
from pathlib import Path
p=Path('/tmp/oec/pequalnp-pilot-62')
d=json.loads((p/'packing-capacity3-compact-orbits.json').read_text())
coords=[(u,v) for u in range(26) for v in range(u+1,26)]
masks=[(1<<u)|(1<<v) for u,v in coords]
labels=d['labels']; cursor=0; rowwords=[]
for i in range(325):
 word=0
 for j in range(i+1,325):
  label=63
  if not masks[i]&masks[j]: label=labels[cursor]; cursor+=1
  word|=label<<(6*(j-i-1))
 rowwords.append(word)
assert cursor==44850

def nested(values,render):
 return '[\n    '+',\n    '.join('['+', '.join(render(v) for v in values[i:i+25])+']' for i in range(0,len(values),25))+']'
inv=d['inverse_generators']
perm=[]
for g in inv:
 perm.append([coords.index(tuple(sorted((g[u],g[v])))) for u,v in coords])
s='import PEqualNP.Defs\n\nnamespace PEqualNP.Outside.L_meta_1896_aux.PackingOrbits\n\n'
s+='def pairEnds (i : Fin 325) : Fin 26 × Fin 26 :=\n  (('+nested(coords,lambda uv:'('+str(uv[0])+', '+str(uv[1])+')')+' : List (List (Fin 26 × Fin 26))).getD (i.val / 25) []).getD (i.val % 25) (0, 0)\n\n'
s+='def pairMask (i : Fin 325) : Nat :=\n  (('+nested(masks,str)+' : List (List Nat)).getD (i.val / 25) []).getD (i.val % 25) 0\n\n'
s+='def vertexPerm (g : Fin 4) (v : Fin 26) : Fin 26 :=\n  (('+str(inv)+' : List (List (Fin 26))).getD g.val []).getD v.val 0\n\n'
s+='def pairPerm (g : Fin 4) (i : Fin 325) : Fin 325 :=\n  ((([\n    '+',\n    '.join(nested(pg,str) for pg in perm)+'] : List (List (List (Fin 325)))).getD g.val []).getD (i.val / 25) []).getD (i.val % 25) 0\n\n'
s+='def labelWord (i : Fin 325) : Nat :=\n  (('+nested(rowwords,hex)+' : List (List Nat)).getD (i.val / 25) []).getD (i.val % 25) 0\n\n'
s+="""def label (i j : Fin 325) : Nat :=
  (labelWord i >>> (6 * (j.val - i.val - 1))) &&& 63

def depth (i j : Fin 325) : Nat := label i j / 4

def selector (i j : Fin 325) : Fin 4 := ⟨label i j % 4, Nat.mod_lt _ (by decide)⟩

def parent (i j : Fin 325) : Fin 325 × Fin 325 :=
  let a := pairPerm (selector i j) i
  let b := pairPerm (selector i j) j
  (min a b, max a b)

def valid (i j : Fin 325) : Prop := i.val < j.val ∧ pairMask i &&& pairMask j = 0

"""
s+='def roots : List (Fin 325 × Fin 325) := ['+', '.join('('+str(i)+', '+str(j)+')' for i,j in d['roots'])+']\n\n'
s+="""def localCheck (i j : Fin 325) : Bool :=
  if valid i j then
    if depth i j = 0 then decide ((i, j) ∈ roots)
    else decide (valid (parent i j).1 (parent i j).2 ∧
      depth (parent i j).1 (parent i j).2 < depth i j)
  else true

end PEqualNP.Outside.L_meta_1896_aux.PackingOrbits
"""
Path('/workspace/pequalnp-proofs/results/orch/lemmas/PackingThreeOrbits.lean').write_text(s)
(p/'packing3-orbits-repacked.json').write_text(json.dumps({'rowwords':rowwords,'inverse_pair_permutations':perm,'roots':d['roots']}))
print('SOURCE_BYTES',len(s.encode()),'ROWS',len(rowwords),'LABELS',cursor)
