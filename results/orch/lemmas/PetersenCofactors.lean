import PEqualNP.Defs

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
  [⟨1,0,4,{2},{3,5,6}⟩,
    ⟨1,0,5,{2},{4,6,7}⟩,
    ⟨4,0,5,{3},{1,3,7}⟩,
    ⟨0,1,2,{4},{3,5,6}⟩,
    ⟨0,1,6,{4},{2,4,8}⟩,
    ⟨2,1,6,{3},{0,7,8}⟩,
    ⟨1,2,3,{0},{4,6,7}⟩,
    ⟨1,2,7,{0},{3,5,6}⟩,
    ⟨3,2,7,{4},{1,4,5}⟩,
    ⟨2,3,4,{1},{0,7,8}⟩,
    ⟨2,3,8,{1},{1,4,5}⟩,
    ⟨4,3,8,{0},{0,2,6}⟩,
    ⟨0,4,3,{1},{2,5,9}⟩,
    ⟨0,4,9,{1},{3,5,6}⟩,
    ⟨3,4,9,{2},{0,2,6}⟩,
    ⟨0,5,7,{1},{2,4,8}⟩,
    ⟨0,5,8,{1},{1,3,7}⟩,
    ⟨7,5,8,{2},{0,2,6}⟩,
    ⟨1,6,8,{0},{0,3,9}⟩,
    ⟨1,6,9,{0},{2,4,8}⟩,
    ⟨8,6,9,{3},{1,4,5}⟩,
    ⟨2,7,5,{1},{0,3,9}⟩,
    ⟨2,7,9,{1},{1,4,5}⟩,
    ⟨5,7,9,{0},{0,2,6}⟩,
    ⟨3,8,5,{2},{0,2,6}⟩,
    ⟨3,8,6,{2},{1,4,5}⟩,
    ⟨5,8,6,{0},{1,3,7}⟩,
    ⟨4,9,6,{0},{1,3,7}⟩,
    ⟨4,9,7,{0},{0,2,6}⟩,
    ⟨6,9,7,{1},{1,4,5}⟩]

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
