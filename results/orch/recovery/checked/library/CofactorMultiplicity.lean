import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_2592_aux.PetersenCofactors

abbrev Record := Fin 10 × Fin 10 × Fin 10 × Finset (Fin 10) × Finset (Fin 10)

def Record.a (r : Record) : Fin 10 := r.1
def Record.b (r : Record) : Fin 10 := r.2.1
def Record.c (r : Record) : Fin 10 := r.2.2.1
def Record.one (r : Record) : Finset (Fin 10) := r.2.2.2.1
def Record.all (r : Record) : Finset (Fin 10) := r.2.2.2.2

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

namespace PEqualNP.Outside.L_meta_2592_aux.PetersenCofactors

lemma every_vertex_nine_times : ∀ i : Fin 10,
    (records.map (fun r =>
      (if r.a = i then 1 else 0) + (if r.b = i then 1 else 0) +
        (if r.c = i then 1 else 0))).sum = 9 := by
  decide +kernel

lemma weighted_record_sum (c : Fin 10 → Nat) :
    (records.map (fun r => c r.a + c r.b + c r.c)).sum = 9 * ∑ i, c i := by
  simp only [records, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    Record.a, Record.b, Record.c, Fin.sum_univ_succ, Fin.sum_univ_zero, Nat.add_zero]
  change _ = 9 * (c 0 + (c 1 + (c 2 + (c 3 + (c 4 + (c 5 + (c 6 + (c 7 + (c 8 + c 9)))))))))
  omega

lemma record_sum_ge_one_fifty (c : Fin 10 → Nat)
    (bound : ∀ r ∈ records, 5 ≤ c r.a + c r.b + c r.c) :
    150 ≤ 9 * ∑ i, c i := by
  rw [← weighted_record_sum]
  have lower : ∀ L : List Record, (∀ r ∈ L, 5 ≤ c r.a + c r.b + c r.c) →
      5 * L.length ≤ (L.map (fun r => c r.a + c r.b + c r.c)).sum := by
    intro L
    induction L with
    | nil => simp
    | cons r L ih =>
      intro h
      have hr := h r (by simp)
      have hl := ih (fun q hq => h q (by simp [hq]))
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega
  have result := lower records bound
  have length : records.length = 30 := by rfl
  rw [length] at result
  exact result

end PEqualNP.Outside.L_meta_2592_aux.PetersenCofactors
