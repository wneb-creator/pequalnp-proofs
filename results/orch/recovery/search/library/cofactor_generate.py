from pathlib import Path
from itertools import combinations
E=[(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]
adj=lambda a,b:(a,b) in E or (b,a) in E
f=lambda mask:any((mask>>a)&1 and (mask>>b)&1 for a,b in E)
def table(a,b,c,S):
    return sum(f(S|sum(((x>>j)&1)<<v for j,v in enumerate((a,b,c))))<<x for x in range(8))
records=[]
for b in range(10):
    for a,c in combinations([a for a in range(10) if adj(a,b)],2):
        assert not adj(a,c)
        assert table(a,b,c,0)==200
        values={}
        for S in range(1024):
            if any((S>>v)&1 for v in (a,b,c)): continue
            values.setdefault(table(a,b,c,S),S)
        assert 234 in values and 254 in values
        records.append((a,b,c,values[234],values[254]))
assert len(records)==30
for a,b in combinations(range(10),2): assert any(a in r[:3] and b in r[:3] for r in records)
fs=lambda S:'{'+','.join(str(v) for v in range(10) if (S>>v)&1)+'}'
rows=',\n    '.join('⟨'+','.join(map(str,r[:3]))+','+fs(r[3])+','+fs(r[4])+'⟩' for r in records)
source='''import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.PetersenCofactors

structure Record where
  a : Fin 10
  b : Fin 10
  c : Fin 10
  one : Finset (Fin 10)
  all : Finset (Fin 10)

def edges : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
   (5,7),(7,9),(9,6),(6,8),(8,5)]

def graph (x : Fin 10 → Bool) : Bool := edges.any (fun e => x e.1 && x e.2)

def extend (r : Record) (S : Finset (Fin 10)) (x : Fin 3 → Bool) (v : Fin 10) : Bool :=
  if v = r.a then x 0 else if v = r.b then x 1 else if v = r.c then x 2 else decide (v ∈ S)

def records : List Record :=
  ['''+rows+''']

def valid (r : Record) : Prop :=
  r.a ≠ r.b ∧ r.a ≠ r.c ∧ r.b ≠ r.c ∧
  ∀ x : Fin 3 → Bool,
    graph (extend r ∅ x) = ((x 0 && x 1) || (x 1 && x 2)) ∧
    graph (extend r r.one x) = (x 0 || (x 1 && x 2)) ∧
    graph (extend r r.all x) = ((x 0 || x 1) || x 2)

def validDecidable (r : Record) : Decidable (valid r) := by
  unfold valid
  infer_instance

def contains (r : Record) (u v : Fin 10) : Prop :=
  (u = r.a ∨ u = r.b ∨ u = r.c) ∧ (v = r.a ∨ v = r.b ∨ v = r.c)

def containsDecidable (r : Record) (u v : Fin 10) : Decidable (contains r u v) := by
  unfold contains
  infer_instance

set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
lemma records_valid : records.all (fun r => @decide (valid r) (validDecidable r)) = true := by
  decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 20000000 in
lemma pair_coverage : ∀ u v : Fin 10, u ≠ v →
    records.any (fun r => @decide (contains r u v) (containsDecidable r u v)) = true := by
  decide +kernel

lemma pair_has_three_cofactors (u v : Fin 10) (different : u ≠ v) :
    ∃ r : Record, contains r u v ∧ valid r := by
  obtain ⟨r, member, covered⟩ := List.any_eq_true.mp (pair_coverage u v different)
  refine ⟨r, @of_decide_eq_true _ (containsDecidable r u v) covered, ?_⟩
  exact @of_decide_eq_true _ (validDecidable r) (List.all_eq_true.mp records_valid r member)

end PEqualNP.Outside.L_meta_2592_aux.PetersenCofactors
'''
Path('/tmp/oec/pequalnp-pilot-109/library/PetersenCofactors.lean').write_text(source)
print('Generated',len(records),'records; all45 unordered pairs covered; all90 cofactor truth tables validated.')
