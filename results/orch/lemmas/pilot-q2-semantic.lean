import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6659_aux

def q2_bit (m : Fin 128) (t : Fin 7) : Bool :=
  ![![false,false,false,false,false,false,false],![true,false,false,false,false,false,false],![false,true,false,false,false,false,false],![true,true,false,false,false,false,false],![false,false,true,false,false,false,false],![true,false,true,false,false,false,false],![false,true,true,false,false,false,false],![true,true,true,false,false,false,false],![false,false,false,true,false,false,false],![true,false,false,true,false,false,false],![false,true,false,true,false,false,false],![true,true,false,true,false,false,false],![false,false,true,true,false,false,false],![true,false,true,true,false,false,false],![false,true,true,true,false,false,false],![true,true,true,true,false,false,false],![false,false,false,false,true,false,false],![true,false,false,false,true,false,false],![false,true,false,false,true,false,false],![true,true,false,false,true,false,false],![false,false,true,false,true,false,false],![true,false,true,false,true,false,false],![false,true,true,false,true,false,false],![true,true,true,false,true,false,false],![false,false,false,true,true,false,false],![true,false,false,true,true,false,false],![false,true,false,true,true,false,false],![true,true,false,true,true,false,false],![false,false,true,true,true,false,false],![true,false,true,true,true,false,false],![false,true,true,true,true,false,false],![true,true,true,true,true,false,false],![false,false,false,false,false,true,false],![true,false,false,false,false,true,false],![false,true,false,false,false,true,false],![true,true,false,false,false,true,false],![false,false,true,false,false,true,false],![true,false,true,false,false,true,false],![false,true,true,false,false,true,false],![true,true,true,false,false,true,false],![false,false,false,true,false,true,false],![true,false,false,true,false,true,false],![false,true,false,true,false,true,false],![true,true,false,true,false,true,false],![false,false,true,true,false,true,false],![true,false,true,true,false,true,false],![false,true,true,true,false,true,false],![true,true,true,true,false,true,false],![false,false,false,false,true,true,false],![true,false,false,false,true,true,false],![false,true,false,false,true,true,false],![true,true,false,false,true,true,false],![false,false,true,false,true,true,false],![true,false,true,false,true,true,false],![false,true,true,false,true,true,false],![true,true,true,false,true,true,false],![false,false,false,true,true,true,false],![true,false,false,true,true,true,false],![false,true,false,true,true,true,false],![true,true,false,true,true,true,false],![false,false,true,true,true,true,false],![true,false,true,true,true,true,false],![false,true,true,true,true,true,false],![true,true,true,true,true,true,false],![false,false,false,false,false,false,true],![true,false,false,false,false,false,true],![false,true,false,false,false,false,true],![true,true,false,false,false,false,true],![false,false,true,false,false,false,true],![true,false,true,false,false,false,true],![false,true,true,false,false,false,true],![true,true,true,false,false,false,true],![false,false,false,true,false,false,true],![true,false,false,true,false,false,true],![false,true,false,true,false,false,true],![true,true,false,true,false,false,true],![false,false,true,true,false,false,true],![true,false,true,true,false,false,true],![false,true,true,true,false,false,true],![true,true,true,true,false,false,true],![false,false,false,false,true,false,true],![true,false,false,false,true,false,true],![false,true,false,false,true,false,true],![true,true,false,false,true,false,true],![false,false,true,false,true,false,true],![true,false,true,false,true,false,true],![false,true,true,false,true,false,true],![true,true,true,false,true,false,true],![false,false,false,true,true,false,true],![true,false,false,true,true,false,true],![false,true,false,true,true,false,true],![true,true,false,true,true,false,true],![false,false,true,true,true,false,true],![true,false,true,true,true,false,true],![false,true,true,true,true,false,true],![true,true,true,true,true,false,true],![false,false,false,false,false,true,true],![true,false,false,false,false,true,true],![false,true,false,false,false,true,true],![true,true,false,false,false,true,true],![false,false,true,false,false,true,true],![true,false,true,false,false,true,true],![false,true,true,false,false,true,true],![true,true,true,false,false,true,true],![false,false,false,true,false,true,true],![true,false,false,true,false,true,true],![false,true,false,true,false,true,true],![true,true,false,true,false,true,true],![false,false,true,true,false,true,true],![true,false,true,true,false,true,true],![false,true,true,true,false,true,true],![true,true,true,true,false,true,true],![false,false,false,false,true,true,true],![true,false,false,false,true,true,true],![false,true,false,false,true,true,true],![true,true,false,false,true,true,true],![false,false,true,false,true,true,true],![true,false,true,false,true,true,true],![false,true,true,false,true,true,true],![true,true,true,false,true,true,true],![false,false,false,true,true,true,true],![true,false,false,true,true,true,true],![false,true,false,true,true,true,true],![true,true,false,true,true,true,true],![false,false,true,true,true,true,true],![true,false,true,true,true,true,true],![false,true,true,true,true,true,true],![true,true,true,true,true,true,true]] m t

def q2_ctx (c : Fin 34) (i : Fin 5) : Fin 128 :=
  ![![99,11,69,99,49],![102,11,69,102,49],![103,11,69,103,49],![103,11,103,103,49],![106,11,69,106,49],![107,11,69,107,49],![107,107,69,107,49],![110,11,69,110,49],![111,11,69,111,49],![111,11,111,111,49],![111,111,69,111,49],![111,111,111,111,49],![114,11,69,114,49],![115,11,69,115,49],![115,11,69,115,115],![118,11,69,118,49],![119,11,69,119,49],![119,11,69,119,119],![119,11,119,119,49],![119,11,119,119,119],![122,11,69,122,49],![123,11,69,123,49],![123,11,69,123,123],![123,123,69,123,49],![123,123,69,123,123],![126,11,69,126,49],![127,11,69,127,49],![127,11,69,127,127],![127,11,127,127,49],![127,11,127,127,127],![127,127,69,127,49],![127,127,69,127,127],![127,127,127,127,49],![127,127,127,127,127]] c i

def q2_unit (c : Fin 34) (k : Fin 33) : Fin 128 :=
  ![0,1,2,3,4,5,6,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48,64,65,66,68,72,80,96,11,69,49,q2_ctx c 0] k

def q2_nb (i : Fin 4) : Fin 128 := ![11,69,98,49] i

def q2_shared (x t : Fin 7) : Bool :=
  ![![true,true,true,true,true,true,true],![true,true,false,true,false,false,false],![true,false,true,false,false,false,true],![true,true,false,true,false,false,false],![true,false,false,false,true,true,false],![true,false,false,false,true,true,false],![true,false,true,false,false,false,true]] x t

def q2_count (u v w : Fin 128) (t : Fin 7) : ℕ :=
  (q2_bit u t).toNat + (q2_bit v t).toNat + (q2_bit w t).toNat

def q2_sub (u v w : Fin 128) (x t : Fin 7) : Bool :=
  (!q2_bit u x || q2_bit u t) && (!q2_bit v x || q2_bit v t) &&
    (!q2_bit w x || q2_bit w t)

def q2_empty (u v w : Fin 128) (x : Fin 7) : Bool :=
  !q2_bit u x && !q2_bit v x && !q2_bit w x

def q2_force (u v w : Fin 128) (x t : Fin 7) : Bool :=
  q2_sub u v w x t && (!q2_empty u v w x || q2_shared x t)

def q2_row (u v w : Fin 128) (i : Fin 4) (t : Fin 7) : Bool :=
  ![q2_force u v w 0 t || q2_force u v w 1 t || q2_force u v w 3 t,q2_force u v w 0 t || q2_force u v w 2 t || q2_force u v w 6 t,q2_force u v w 1 t || q2_force u v w 5 t || q2_force u v w 6 t,q2_force u v w 0 t || q2_force u v w 4 t || q2_force u v w 5 t] i

def q2_budget_at (c : Fin 34) (u v w : Fin 128) (t : Fin 7) : Bool :=
  decide ((q2_bit (q2_ctx c 1) t).toNat + (q2_bit (q2_ctx c 2) t).toNat +
    (q2_bit (q2_ctx c 3) t).toNat + (q2_bit (q2_ctx c 4) t).toNat +
    (if t = 0 then 0 else 1) ≤ 2 + q2_count u v w t)

def q2_budget (c : Fin 34) (u v w : Fin 128) : Bool :=
  q2_budget_at c u v w 0 && q2_budget_at c u v w 1 && q2_budget_at c u v w 2 && q2_budget_at c u v w 3 && q2_budget_at c u v w 4 && q2_budget_at c u v w 5 && q2_budget_at c u v w 6

def q2_center (u v w : Fin 128) : Bool :=
  decide (q2_count u v w 0 + (q2_sub u v w 1 0).toNat + (q2_sub u v w 2 0).toNat + (q2_sub u v w 3 0).toNat + (q2_sub u v w 4 0).toNat + (q2_sub u v w 5 0).toNat + (q2_sub u v w 6 0).toNat ≤ 5)

def q2_labels (c : Fin 34) (u v w : Fin 128) : Bool :=
  (!q2_row u v w 0 0 || q2_bit (q2_ctx c 1) 0) &&
    (!q2_row u v w 0 1 || q2_bit (q2_ctx c 1) 1) &&
    (!q2_row u v w 0 2 || q2_bit (q2_ctx c 1) 2) &&
    (!q2_row u v w 0 3 || q2_bit (q2_ctx c 1) 3) &&
    (!q2_row u v w 0 4 || q2_bit (q2_ctx c 1) 4) &&
    (!q2_row u v w 0 5 || q2_bit (q2_ctx c 1) 5) &&
    (!q2_row u v w 0 6 || q2_bit (q2_ctx c 1) 6) &&
    (!q2_row u v w 1 0 || q2_bit (q2_ctx c 2) 0) &&
    (!q2_row u v w 1 1 || q2_bit (q2_ctx c 2) 1) &&
    (!q2_row u v w 1 2 || q2_bit (q2_ctx c 2) 2) &&
    (!q2_row u v w 1 3 || q2_bit (q2_ctx c 2) 3) &&
    (!q2_row u v w 1 4 || q2_bit (q2_ctx c 2) 4) &&
    (!q2_row u v w 1 5 || q2_bit (q2_ctx c 2) 5) &&
    (!q2_row u v w 1 6 || q2_bit (q2_ctx c 2) 6) &&
    (!q2_row u v w 2 0 || q2_bit (q2_ctx c 3) 0) &&
    (!q2_row u v w 2 1 || q2_bit (q2_ctx c 3) 1) &&
    (!q2_row u v w 2 2 || q2_bit (q2_ctx c 3) 2) &&
    (!q2_row u v w 2 3 || q2_bit (q2_ctx c 3) 3) &&
    (!q2_row u v w 2 4 || q2_bit (q2_ctx c 3) 4) &&
    (!q2_row u v w 2 5 || q2_bit (q2_ctx c 3) 5) &&
    (!q2_row u v w 2 6 || q2_bit (q2_ctx c 3) 6) &&
    (!q2_row u v w 3 0 || q2_bit (q2_ctx c 4) 0) &&
    (!q2_row u v w 3 1 || q2_bit (q2_ctx c 4) 1) &&
    (!q2_row u v w 3 2 || q2_bit (q2_ctx c 4) 2) &&
    (!q2_row u v w 3 3 || q2_bit (q2_ctx c 4) 3) &&
    (!q2_row u v w 3 4 || q2_bit (q2_ctx c 4) 4) &&
    (!q2_row u v w 3 5 || q2_bit (q2_ctx c 4) 5) &&
    (!q2_row u v w 3 6 || q2_bit (q2_ctx c 4) 6)

def q2_bad (c : Fin 34) (a b d : Fin 33) : Bool :=
  let u := q2_unit c a
  let v := q2_unit c b
  let w := q2_unit c d
  q2_budget c u v w && q2_center u v w && q2_labels c u v w

def q2_index (g : Fin 11) (r : Fin 3) : Fin 33 :=
  ⟨3*g.val+r.val, by omega⟩

def q2_ordered_bad (c : Fin 34) (a b d : Fin 33) : Bool :=
  decide (a ≤ b ∧ b ≤ d) && q2_bad c a b d

lemma q2_count_swap (u v w : Fin 128) (t : Fin 7) :
    q2_count u v w t = q2_count v u w t := by
  simp only [q2_count, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

lemma q2_count_rotate (u v w : Fin 128) (t : Fin 7) :
    q2_count u v w t = q2_count v w u t := by
  simp only [q2_count, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc]

lemma q2_sub_swap (u v w : Fin 128) (x t : Fin 7) :
    q2_sub u v w x t = q2_sub v u w x t := by
  simp only [q2_sub, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]

lemma q2_sub_rotate (u v w : Fin 128) (x t : Fin 7) :
    q2_sub u v w x t = q2_sub v w u x t := by
  simp only [q2_sub, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]

lemma q2_empty_swap (u v w : Fin 128) (x : Fin 7) :
    q2_empty u v w x = q2_empty v u w x := by
  simp only [q2_empty, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]

lemma q2_empty_rotate (u v w : Fin 128) (x : Fin 7) :
    q2_empty u v w x = q2_empty v w u x := by
  simp only [q2_empty, Bool.and_comm, Bool.and_left_comm, Bool.and_assoc]

lemma q2_force_swap (u v w : Fin 128) (x t : Fin 7) :
    q2_force u v w x t = q2_force v u w x t := by
  simp only [q2_force, q2_sub_swap u v w, q2_empty_swap u v w]

lemma q2_row_swap (u v w : Fin 128) (i : Fin 4) (t : Fin 7) :
    q2_row u v w i t = q2_row v u w i t := by
  simp only [q2_row, q2_force_swap u v w]

lemma q2_budget_at_swap (c : Fin 34) (u v w : Fin 128) (t : Fin 7) :
    q2_budget_at c u v w t = q2_budget_at c v u w t := by
  simp only [q2_budget_at, q2_count_swap u v w]

lemma q2_budget_swap (c : Fin 34) (u v w : Fin 128)  :
    q2_budget c u v w = q2_budget c v u w := by
  simp only [q2_budget, q2_budget_at_swap c u v w]

lemma q2_center_swap (u v w : Fin 128)  :
    q2_center u v w = q2_center v u w := by
  simp only [q2_center, q2_count_swap u v w, q2_sub_swap u v w]

lemma q2_labels_swap (c : Fin 34) (u v w : Fin 128)  :
    q2_labels c u v w = q2_labels c v u w := by
  simp only [q2_labels, q2_row_swap u v w]

lemma q2_bad_swap (c : Fin 34) (a b d : Fin 33) :
    q2_bad c a b d = q2_bad c b a d := by
  simp only [q2_bad, q2_budget_swap c (q2_unit c a) (q2_unit c b) (q2_unit c d),
    q2_center_swap (q2_unit c a) (q2_unit c b) (q2_unit c d), q2_labels_swap c (q2_unit c a) (q2_unit c b) (q2_unit c d)]

lemma q2_force_rotate (u v w : Fin 128) (x t : Fin 7) :
    q2_force u v w x t = q2_force v w u x t := by
  simp only [q2_force, q2_sub_rotate u v w, q2_empty_rotate u v w]

lemma q2_row_rotate (u v w : Fin 128) (i : Fin 4) (t : Fin 7) :
    q2_row u v w i t = q2_row v w u i t := by
  simp only [q2_row, q2_force_rotate u v w]

lemma q2_budget_at_rotate (c : Fin 34) (u v w : Fin 128) (t : Fin 7) :
    q2_budget_at c u v w t = q2_budget_at c v w u t := by
  simp only [q2_budget_at, q2_count_rotate u v w]

lemma q2_budget_rotate (c : Fin 34) (u v w : Fin 128)  :
    q2_budget c u v w = q2_budget c v w u := by
  simp only [q2_budget, q2_budget_at_rotate c u v w]

lemma q2_center_rotate (u v w : Fin 128)  :
    q2_center u v w = q2_center v w u := by
  simp only [q2_center, q2_count_rotate u v w, q2_sub_rotate u v w]

lemma q2_labels_rotate (c : Fin 34) (u v w : Fin 128)  :
    q2_labels c u v w = q2_labels c v w u := by
  simp only [q2_labels, q2_row_rotate u v w]

lemma q2_bad_rotate (c : Fin 34) (a b d : Fin 33) :
    q2_bad c a b d = q2_bad c b d a := by
  simp only [q2_bad, q2_budget_rotate c (q2_unit c a) (q2_unit c b) (q2_unit c d),
    q2_center_rotate (q2_unit c a) (q2_unit c b) (q2_unit c d), q2_labels_rotate c (q2_unit c a) (q2_unit c b) (q2_unit c d)]

def q2_decode (m : Fin 128) : Finset (Fin 7) :=
  Finset.univ.filter (fun t => q2_bit m t = true)

def q2_sum (S : Finset (Fin 7)) : ℕ := S.sum (fun i => 2^i.val)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_sum_bound : ∀ S : Finset (Fin 7), q2_sum S < 128 := by decide +kernel

def q2_encode (S : Finset (Fin 7)) : Fin 128 := ⟨q2_sum S,q2_sum_bound S⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_encode_decode : ∀ m : Fin 128, q2_encode (q2_decode m) = m := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_decode_encode : ∀ S : Finset (Fin 7), q2_decode (q2_encode S) = S := by decide +kernel

def q2_super (s : Fin 15) : Fin 128 := ![99,102,103,106,107,110,111,114,115,118,119,122,123,126,127] s

def q2_small (k : Fin 29) : Fin 128 := ![0,1,2,3,4,5,6,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48,64,65,66,68,72,80,96] k

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_super_complete : ∀ m : Fin 128, q2_decode 98 ⊂ q2_decode m →
    ∃ s : Fin 15, q2_super s = m := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_small_complete : ∀ m : Fin 128, (q2_decode m).card ≤ 2 →
    ∃ k : Fin 29, q2_small k = m := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_small_unit : ∀ c : Fin 34, ∀ k : Fin 29,
    q2_unit c ⟨k.val, by omega⟩ = q2_small k := by decide +kernel

lemma q2_unit_complete (c : Fin 34) (U : Finset (Fin 7))
    (h : U.card ≤ 2 ∨ U = q2_decode 11 ∨ U = q2_decode 69 ∨
      U = q2_decode 49 ∨ U = q2_decode (q2_ctx c 0)) :
    ∃ k : Fin 33, q2_decode (q2_unit c k) = U := by
  rcases h with h|h|h|h|h
  · obtain ⟨k,hk⟩ := q2_small_complete (q2_encode U) (by simpa only [q2_decode_encode] using h)
    refine ⟨⟨k.val,by omega⟩, ?_⟩
    rw [q2_small_unit, hk, q2_decode_encode]
  · exact ⟨29,h.symm⟩
  · exact ⟨30,h.symm⟩
  · exact ⟨31,h.symm⟩
  · exact ⟨32,h.symm⟩

def q2_choices (s : Fin 15) (a b d : Fin 2) : Fin 4 → Fin 128 :=
  ![if a = 0 then 11 else q2_super s, if b = 0 then 69 else q2_super s,
    q2_super s, if d = 0 then 49 else q2_super s]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_context_complete : ∀ s : Fin 15, ∀ a b d : Fin 2,
    (∀ i : Fin 4, q2_decode (q2_nb i) ⊆ q2_decode (q2_choices s a b d i)) →
      ∃ c : Fin 34, q2_ctx c 0 = q2_super s ∧
        ∀ i : Fin 4, q2_ctx c i.succ = q2_choices s a b d i := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_required_choices : ∀ i : Fin 3, ∀ j : Fin 3,
    q2_decode (![11,69,49] i) ⊆ q2_decode (![11,69,49] j) → i = j := by decide +kernel

lemma q2_bit_mem (m : Fin 128) (t : Fin 7) :
    q2_bit m t = true ↔ t ∈ q2_decode m := by simp [q2_decode]

def q2_res (u v w : Fin 128) (t : Fin 7) : Finset (Fin 3) :=
  Finset.univ.filter (fun j => (![q2_bit u t,q2_bit v t,q2_bit w t] j) = true)

lemma q2_count_card (u v w : Fin 128) (t : Fin 7) :
    q2_count u v w t = (q2_res u v w t).card := by
  have h : ∀ a b d : Bool, a.toNat+b.toNat+d.toNat =
      (Finset.univ.filter (fun j : Fin 3 => (![a,b,d] j) = true)).card := by decide +kernel
  exact h (q2_bit u t) (q2_bit v t) (q2_bit w t)

lemma q2_sub_iff (u v w : Fin 128) (x t : Fin 7) :
    q2_sub u v w x t = true ↔ q2_res u v w x ⊆ q2_res u v w t := by
  have h : ∀ a b d e f g : Bool,
      ((!a || e) && (!b || f) && (!d || g)) = true ↔
      (Finset.univ.filter (fun j : Fin 3 => (![a,b,d] j) = true)) ⊆
      (Finset.univ.filter (fun j : Fin 3 => (![e,f,g] j) = true)) := by decide +kernel
  exact h (q2_bit u x) (q2_bit v x) (q2_bit w x)
    (q2_bit u t) (q2_bit v t) (q2_bit w t)

lemma q2_empty_iff (u v w : Fin 128) (x : Fin 7) :
    q2_empty u v w x = true ↔ q2_res u v w x = ∅ := by
  have h : ∀ a b d : Bool, (!a && !b && !d) = true ↔
      (Finset.univ.filter (fun j : Fin 3 => (![a,b,d] j) = true)) = ∅ := by decide +kernel
  exact h (q2_bit u x) (q2_bit v x) (q2_bit w x)


lemma q2_semantic_contradiction
    (certificate : ∀ c : Fin 34, ∀ a b d : Fin 33, q2_bad c a b d = false)
    (c : Fin 34) (a b d : Fin 33)
    (budget : ∀ t : Fin 7,
      (q2_bit (q2_ctx c 1) t).toNat + (q2_bit (q2_ctx c 2) t).toNat +
      (q2_bit (q2_ctx c 3) t).toNat + (q2_bit (q2_ctx c 4) t).toNat +
      (if t = 0 then 0 else 1) ≤
        2 + (q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) t).card)
    (labels : ∀ i : Fin 4, ∀ x t : Fin 7,
      x ∈ q2_decode (q2_nb i) →
      q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) x ⊆
        q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) t →
      ((q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) x).Nonempty ∨
        q2_shared x t = true) → t ∈ q2_decode (q2_ctx c i.succ))
    (center :
      (q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 0).card +
      (if q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 1 ⊆
        q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 0 then 1 else 0) +
      (if q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 2 ⊆
        q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 0 then 1 else 0) +
      (if q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 3 ⊆
        q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 0 then 1 else 0) +
      (if q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 4 ⊆
        q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 0 then 1 else 0) +
      (if q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 5 ⊆
        q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 0 then 1 else 0) +
      (if q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 6 ⊆
        q2_res (q2_unit c a) (q2_unit c b) (q2_unit c d) 0 then 1 else 0) ≤ 5) :
    False := by
  classical
  let u := q2_unit c a
  let v := q2_unit c b
  let w := q2_unit c d
  have hb (t : Fin 7) : q2_budget_at c u v w t = true := by
    simpa only [q2_budget_at, decide_eq_true_eq, q2_count_card] using budget t
  have budgetB : q2_budget c u v w = true := by
    simp only [q2_budget, hb, Bool.and_true]
  have or_split (x y : Bool) (h : (x || y) = true) : x = true ∨ y = true := by
    simpa only [Bool.or_eq_true] using h
  have force (i : Fin 4) (x t : Fin 7) (hx : x ∈ q2_decode (q2_nb i))
      (hf : q2_force u v w x t = true) : q2_bit (q2_ctx c i.succ) t = true := by
    apply (q2_bit_mem _ _).mpr
    have hf' : q2_sub u v w x t = true ∧
        (!q2_empty u v w x || q2_shared x t) = true := by
      simpa only [q2_force, Bool.and_eq_true] using hf
    have hs := (q2_sub_iff u v w x t).mp hf'.1
    apply labels i x t hx hs
    rcases or_split _ _ hf'.2 with hn | hshared
    · left
      apply Finset.nonempty_iff_ne_empty.mpr
      intro he
      have he' := (q2_empty_iff u v w x).mpr he
      simp only [he', Bool.not_true, Bool.false_eq_true] at hn
    · exact Or.inr hshared
  have row (i : Fin 4) (t : Fin 7) (hr : q2_row u v w i t = true) :
      q2_bit (q2_ctx c i.succ) t = true := by
    fin_cases i
    · change (q2_force u v w 0 t || q2_force u v w 1 t || q2_force u v w 3 t) = true at hr
      rcases or_split _ _ hr with hr | hr
      · rcases or_split _ _ hr with hr | hr
        · exact force 0 0 t (by decide +kernel) hr
        · exact force 0 1 t (by decide +kernel) hr
      · exact force 0 3 t (by decide +kernel) hr
    · change (q2_force u v w 0 t || q2_force u v w 2 t || q2_force u v w 6 t) = true at hr
      rcases or_split _ _ hr with hr | hr
      · rcases or_split _ _ hr with hr | hr
        · exact force 1 0 t (by decide +kernel) hr
        · exact force 1 2 t (by decide +kernel) hr
      · exact force 1 6 t (by decide +kernel) hr
    · change (q2_force u v w 1 t || q2_force u v w 5 t || q2_force u v w 6 t) = true at hr
      rcases or_split _ _ hr with hr | hr
      · rcases or_split _ _ hr with hr | hr
        · exact force 2 1 t (by decide +kernel) hr
        · exact force 2 5 t (by decide +kernel) hr
      · exact force 2 6 t (by decide +kernel) hr
    · change (q2_force u v w 0 t || q2_force u v w 4 t || q2_force u v w 5 t) = true at hr
      rcases or_split _ _ hr with hr | hr
      · rcases or_split _ _ hr with hr | hr
        · exact force 3 0 t (by decide +kernel) hr
        · exact force 3 4 t (by decide +kernel) hr
      · exact force 3 5 t (by decide +kernel) hr
  have entry (i : Fin 4) (t : Fin 7) :
      (!q2_row u v w i t || q2_bit (q2_ctx c i.succ) t) = true := by
    cases hrow : q2_row u v w i t
    · simp only [Bool.not_false, Bool.true_or]
    · simpa only [Bool.not_true, Bool.false_or] using row i t hrow
  have labelsB : q2_labels c u v w = true := by
    have e0 : ∀ t : Fin 7, (!q2_row u v w 0 t || q2_bit (q2_ctx c 1) t) = true := entry 0
    have e1 : ∀ t : Fin 7, (!q2_row u v w 1 t || q2_bit (q2_ctx c 2) t) = true := entry 1
    have e2 : ∀ t : Fin 7, (!q2_row u v w 2 t || q2_bit (q2_ctx c 3) t) = true := entry 2
    have e3 : ∀ t : Fin 7, (!q2_row u v w 3 t || q2_bit (q2_ctx c 4) t) = true := entry 3
    simp only [q2_labels, e0, e1, e2, e3, Bool.and_true]
  have subcount (x t : Fin 7) : (q2_sub u v w x t).toNat =
      if q2_res u v w x ⊆ q2_res u v w t then 1 else 0 := by
    cases hs : q2_sub u v w x t
    · have hn : ¬ q2_res u v w x ⊆ q2_res u v w t := by
        intro hh
        have htrue := (q2_sub_iff u v w x t).mpr hh
        simp only [hs, Bool.false_eq_true] at htrue
      simp only [hn, ite_false, Bool.toNat_false]
    · simp only [(q2_sub_iff u v w x t).mp hs, ite_true, Bool.toNat_true]
  have centerB : q2_center u v w = true := by
    simpa only [q2_center, decide_eq_true_eq, q2_count_card, subcount] using center
  have bad : q2_bad c a b d = true := by
    change q2_budget c u v w && q2_center u v w && q2_labels c u v w = true
    simp only [budgetB, centerB, labelsB, Bool.and_true, Bool.true_and, decide_true]
  have impossible := certificate c a b d
  rw [bad] at impossible
  exact Bool.noConfusion impossible

end PEqualNP.Outside.L_meta_6659_aux
