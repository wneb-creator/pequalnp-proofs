from pathlib import Path
import hashlib,itertools,json
ROOT=Path('/tmp/oec/pequalnp-pilot-87/counterexample/independent-orbits')
reported=Path('/tmp/oec/pequalnp-pilot-87/root_structural/petersen-independent-orbits.json')
data=json.loads(reported.read_text());assert isinstance(data,dict) and isinstance(data['orbits'],list)
edges=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
adj=[[False]*10 for _ in range(10)]
for a,b in edges:adj[a][b]=adj[b][a]=True
autos=[]
def extend(p,unused):
 n=len(p)
 if n==10:autos.append(tuple(p));return
 for v in sorted(unused):
  if all(adj[n][j]==adj[v][w]for j,w in enumerate(p)):extend(p+[v],unused-{v})
extend([],set(range(10)))
assert len(autos)==len(set(autos))==120
ind=[m for m in range(1024)if not any((m>>a&1)and(m>>b&1)for a,b in edges)]
assert len(ind)==76
reps=[sum(1<<v for v in r['representative'])for r in data['orbits']]
def move(m,p):return sum(1<<p[i]for i in range(10)if m>>i&1)
orbits=[{move(rep,p)for p in autos}for rep in reps]
assert set.union(*orbits)==set(ind) and sum(map(len,orbits))==76
assert data['automorphisms']==120 and data['independent_sets']==76
for r,orbit in zip(data['orbits'],orbits):
 assert r['orbit_size']==len(orbit)
 eligible=set(range(10))-set(r['representative'])
 assert r['eligible']==sorted(eligible)
 assert r['edges_inside_eligible']==[[a,b]for a,b in edges if a in eligible and b in eligible]
 assert r['ineligible_neighbors']=={str(v):[w for w in range(10)if adj[v][w]]for v in r['representative']}
 assert r['surplus_if_size19']==19+1-10==10
 assert r['reserved_pure_units']==len(eligible) and r['residual_upper']==10-len(eligible)
perms=[];classes=[]
for m in ind:
 k=next(k for k,o in enumerate(orbits)if m in o);classes.append(k)
 perms.append(next(p for p in autos if move(m,p)==reps[k]))
unique=list(dict.fromkeys(perms));indices=[unique.index(p)for p in perms]
cert={'edges':edges,'independent_masks':ind,'representative_masks':reps,'orbit_sizes':list(map(len,orbits)),'automorphisms':autos,'witness_permutations':unique,'witness_indices':indices,'classes':classes}
(ROOT/'certificate.json').write_text(json.dumps(cert,indent=2)+'\n')
def fs(m):return '{'+', '.join(str(i)for i in range(10)if m>>i&1)+'}'
def vec(x):return '!['+', '.join(vec(y)if isinstance(y,(list,tuple))else str(y)for y in x)+']'
s=f'''import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2373.IndependentOrbits

def adjacent (a b : Fin 10) : Bool :=
  ({repr(edges)} : List (Fin 10 × Fin 10)).any
    (fun e => (a == e.1 && b == e.2) || (a == e.2 && b == e.1))

abbrev independent (I : Finset (Fin 10)) : Prop := ∀ a ∈ I, ∀ b ∈ I, adjacent a b = false

def representative : Fin 6 → Finset (Fin 10) := ![{', '.join(fs(m)for m in reps)}]
def knownSet : Fin 76 → Finset (Fin 10) := ![{', '.join(fs(m)for m in ind)}]
def classOf : Fin 76 → Fin 6 := {vec(classes)}
def permutationTable : Fin {len(unique)} → Fin 10 → Fin 10 := {vec(unique)}
def permutationIndex : Fin 76 → Fin {len(unique)} := {vec(indices)}
def permutation (i : Fin 76) : Fin 10 → Fin 10 := permutationTable (permutationIndex i)

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma coverage : ∀ I : Finset (Fin 10), independent I → ∃ i : Fin 76, knownSet i = I := by
  decide +kernel

set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
lemma witness_facts : ∀ i : Fin 76,
    Function.Bijective (permutation i) ∧
    (∀ a b, adjacent (permutation i a) (permutation i b) = adjacent a b) ∧
    (knownSet i).image (permutation i) = representative (classOf i) := by
  intro i
  fin_cases i <;> decide +kernel

lemma canonicalize (I : Finset (Fin 10)) (h : independent I) :
    ∃ (k : Fin 6) (f : Fin 10 → Fin 10), Function.Bijective f ∧
      (∀ a b, adjacent (f a) (f b) = adjacent a b) ∧
      I.image f = representative k := by
  obtain ⟨i, rfl⟩ := coverage I h
  exact ⟨classOf i, permutation i, witness_facts i⟩

lemma nonempty_canonicalize (I : Finset (Fin 10)) (h : independent I) (hne : I.Nonempty) :
    ∃ (k : Fin 5) (f : Fin 10 → Fin 10), Function.Bijective f ∧
      (∀ a b, adjacent (f a) (f b) = adjacent a b) ∧
      I.image f = representative k.succ := by
  obtain ⟨k, f, hf, ha, hi⟩ := canonicalize I h
  cases k using Fin.cases with
  | zero =>
    obtain ⟨v, hv⟩ := hne
    have member := Finset.mem_image_of_mem f hv
    rw [hi] at member
    simp [representative] at member
  | succ k => exact ⟨k, f, hf, ha, hi⟩

lemma empty_representative : representative 0 = ∅ := rfl

end PEqualNP.Outside.L_meta_2373.IndependentOrbits
'''
s=s.replace('[(', '[(').replace('), (', '), (')
(ROOT/'IndependentOrbits.lean').write_text(s)
print('PASS independent enumeration:120automorphisms,76independentsets,6orbits',list(map(len,orbits)))
print('PASS eligible-complement, induced-edge and neighbor fields; arithmetic fields match definitions only.')
print('Representatives', [r['representative']for r in data['orbits']])
print('Unique witness permutations',len(unique),'Lean bytes',len(s.encode()))
print('Input SHA256',hashlib.sha256(reported.read_bytes()).hexdigest())
