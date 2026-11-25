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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_0_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 0 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_0_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 0 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_0_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 0 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_0_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 0 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_0_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 0 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_0_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 0 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_0_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 0 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_0_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 0 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_0_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 0 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_0_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 0 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_0_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 0 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_1_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 1 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_1_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 1 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_1_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 1 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_1_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 1 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_1_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 1 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_1_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 1 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_1_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 1 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_1_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 1 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_1_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 1 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_1_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 1 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_1_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 1 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_2_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 2 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_2_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 2 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_2_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 2 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_2_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 2 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_2_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 2 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_2_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 2 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_2_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 2 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_2_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 2 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_2_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 2 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_2_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 2 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_2_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 2 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_3_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 3 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_3_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 3 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_3_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 3 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_3_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 3 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_3_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 3 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_3_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 3 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_3_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 3 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_3_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 3 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_3_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 3 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_3_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 3 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_3_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 3 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_4_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 4 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_4_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 4 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_4_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 4 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_4_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 4 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_4_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 4 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_4_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 4 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_4_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 4 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_4_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 4 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_4_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 4 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_4_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 4 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_4_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 4 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_5_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 5 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_5_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 5 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_5_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 5 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_5_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 5 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_5_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 5 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_5_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 5 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_5_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 5 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_5_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 5 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_5_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 5 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_5_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 5 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_5_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 5 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_6_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 6 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_6_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 6 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_6_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 6 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_6_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 6 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_6_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 6 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_6_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 6 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_6_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 6 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_6_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 6 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_6_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 6 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_6_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 6 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_6_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 6 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_7_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 7 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_7_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 7 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_7_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 7 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_7_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 7 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_7_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 7 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_7_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 7 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_7_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 7 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_7_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 7 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_7_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 7 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_7_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 7 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_7_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 7 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_8_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 8 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_8_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 8 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_8_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 8 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_8_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 8 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_8_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 8 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_8_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 8 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_8_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 8 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_8_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 8 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_8_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 8 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_8_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 8 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_8_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 8 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_9_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 9 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_9_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 9 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_9_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 9 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_9_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 9 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_9_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 9 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_9_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 9 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_9_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 9 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_9_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 9 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_9_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 9 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_9_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 9 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_9_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 9 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_10_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 10 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_10_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 10 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_10_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 10 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_10_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 10 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_10_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 10 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_10_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 10 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_10_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 10 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_10_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 10 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_10_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 10 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_10_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 10 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_10_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 10 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_11_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 11 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_11_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 11 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_11_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 11 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_11_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 11 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_11_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 11 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_11_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 11 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_11_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 11 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_11_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 11 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_11_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 11 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_11_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 11 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_11_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 11 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_12_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 12 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_12_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 12 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_12_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 12 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_12_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 12 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_12_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 12 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_12_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 12 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_12_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 12 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_12_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 12 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_12_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 12 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_12_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 12 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_12_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 12 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_13_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 13 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_13_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 13 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_13_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 13 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_13_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 13 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_13_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 13 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_13_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 13 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_13_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 13 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_13_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 13 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_13_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 13 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_13_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 13 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_13_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 13 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_14_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 14 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_14_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 14 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_14_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 14 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_14_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 14 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_14_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 14 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_14_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 14 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_14_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 14 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_14_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 14 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_14_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 14 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_14_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 14 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_14_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 14 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_15_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 15 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_15_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 15 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_15_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 15 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_15_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 15 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_15_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 15 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_15_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 15 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_15_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 15 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_15_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 15 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_15_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 15 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_15_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 15 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_15_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 15 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_16_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 16 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_16_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 16 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_16_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 16 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_16_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 16 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_16_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 16 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_16_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 16 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_16_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 16 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_16_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 16 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_16_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 16 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_16_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 16 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_16_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 16 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_17_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 17 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_17_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 17 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_17_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 17 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_17_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 17 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_17_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 17 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_17_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 17 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_17_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 17 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_17_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 17 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_17_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 17 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_17_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 17 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_17_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 17 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_18_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 18 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_18_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 18 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_18_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 18 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_18_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 18 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_18_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 18 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_18_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 18 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_18_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 18 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_18_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 18 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_18_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 18 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_18_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 18 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_18_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 18 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_19_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 19 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_19_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 19 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_19_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 19 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_19_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 19 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_19_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 19 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_19_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 19 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_19_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 19 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_19_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 19 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_19_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 19 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_19_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 19 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_19_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 19 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_20_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 20 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_20_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 20 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_20_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 20 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_20_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 20 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_20_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 20 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_20_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 20 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_20_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 20 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_20_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 20 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_20_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 20 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_20_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 20 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_20_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 20 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_21_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 21 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_21_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 21 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_21_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 21 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_21_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 21 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_21_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 21 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_21_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 21 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_21_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 21 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_21_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 21 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_21_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 21 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_21_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 21 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_21_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 21 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_22_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 22 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_22_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 22 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_22_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 22 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_22_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 22 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_22_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 22 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_22_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 22 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_22_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 22 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_22_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 22 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_22_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 22 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_22_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 22 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_22_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 22 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_23_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 23 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_23_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 23 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_23_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 23 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_23_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 23 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_23_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 23 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_23_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 23 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_23_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 23 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_23_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 23 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_23_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 23 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_23_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 23 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_23_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 23 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_24_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 24 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_24_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 24 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_24_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 24 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_24_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 24 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_24_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 24 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_24_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 24 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_24_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 24 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_24_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 24 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_24_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 24 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_24_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 24 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_24_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 24 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_25_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 25 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_25_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 25 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_25_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 25 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_25_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 25 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_25_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 25 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_25_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 25 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_25_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 25 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_25_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 25 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_25_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 25 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_25_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 25 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_25_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 25 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_26_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 26 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_26_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 26 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_26_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 26 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_26_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 26 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_26_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 26 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_26_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 26 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_26_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 26 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_26_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 26 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_26_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 26 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_26_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 26 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_26_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 26 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_27_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 27 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_27_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 27 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_27_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 27 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_27_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 27 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_27_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 27 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_27_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 27 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_27_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 27 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_27_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 27 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_27_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 27 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_27_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 27 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_27_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 27 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_28_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 28 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_28_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 28 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_28_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 28 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_28_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 28 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_28_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 28 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_28_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 28 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_28_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 28 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_28_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 28 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_28_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 28 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_28_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 28 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_28_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 28 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_29_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 29 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_29_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 29 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_29_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 29 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_29_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 29 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_29_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 29 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_29_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 29 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_29_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 29 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_29_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 29 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_29_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 29 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_29_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 29 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_29_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 29 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_30_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 30 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_30_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 30 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_30_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 30 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_30_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 30 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_30_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 30 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_30_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 30 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_30_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 30 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_30_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 30 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_30_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 30 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_30_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 30 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_30_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 30 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_31_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 31 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_31_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 31 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_31_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 31 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_31_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 31 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_31_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 31 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_31_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 31 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_31_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 31 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_31_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 31 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_31_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 31 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_31_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 31 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_31_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 31 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_32_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 32 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_32_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 32 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_32_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 32 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_32_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 32 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_32_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 32 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_32_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 32 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_32_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 32 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_32_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 32 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_32_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 32 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_32_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 32 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_32_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 32 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_33_0 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 33 (q2_index 0 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_33_1 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 33 (q2_index 1 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_33_2 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 33 (q2_index 2 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_33_3 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 33 (q2_index 3 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_33_4 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 33 (q2_index 4 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_33_5 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 33 (q2_index 5 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_33_6 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 33 (q2_index 6 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_33_7 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 33 (q2_index 7 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_33_8 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 33 (q2_index 8 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_33_9 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 33 (q2_index 9 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_cert_33_10 : ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad 33 (q2_index 10 r) b d = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_all_blocks : ∀ c : Fin 34, ∀ g : Fin 11, ∀ r : Fin 3, ∀ b d : Fin 33,
    q2_ordered_bad c (q2_index g r) b d = false := by
  intro c g
  fin_cases c
  · fin_cases g
    · exact q2_cert_0_0
    · exact q2_cert_0_1
    · exact q2_cert_0_2
    · exact q2_cert_0_3
    · exact q2_cert_0_4
    · exact q2_cert_0_5
    · exact q2_cert_0_6
    · exact q2_cert_0_7
    · exact q2_cert_0_8
    · exact q2_cert_0_9
    · exact q2_cert_0_10
  · fin_cases g
    · exact q2_cert_1_0
    · exact q2_cert_1_1
    · exact q2_cert_1_2
    · exact q2_cert_1_3
    · exact q2_cert_1_4
    · exact q2_cert_1_5
    · exact q2_cert_1_6
    · exact q2_cert_1_7
    · exact q2_cert_1_8
    · exact q2_cert_1_9
    · exact q2_cert_1_10
  · fin_cases g
    · exact q2_cert_2_0
    · exact q2_cert_2_1
    · exact q2_cert_2_2
    · exact q2_cert_2_3
    · exact q2_cert_2_4
    · exact q2_cert_2_5
    · exact q2_cert_2_6
    · exact q2_cert_2_7
    · exact q2_cert_2_8
    · exact q2_cert_2_9
    · exact q2_cert_2_10
  · fin_cases g
    · exact q2_cert_3_0
    · exact q2_cert_3_1
    · exact q2_cert_3_2
    · exact q2_cert_3_3
    · exact q2_cert_3_4
    · exact q2_cert_3_5
    · exact q2_cert_3_6
    · exact q2_cert_3_7
    · exact q2_cert_3_8
    · exact q2_cert_3_9
    · exact q2_cert_3_10
  · fin_cases g
    · exact q2_cert_4_0
    · exact q2_cert_4_1
    · exact q2_cert_4_2
    · exact q2_cert_4_3
    · exact q2_cert_4_4
    · exact q2_cert_4_5
    · exact q2_cert_4_6
    · exact q2_cert_4_7
    · exact q2_cert_4_8
    · exact q2_cert_4_9
    · exact q2_cert_4_10
  · fin_cases g
    · exact q2_cert_5_0
    · exact q2_cert_5_1
    · exact q2_cert_5_2
    · exact q2_cert_5_3
    · exact q2_cert_5_4
    · exact q2_cert_5_5
    · exact q2_cert_5_6
    · exact q2_cert_5_7
    · exact q2_cert_5_8
    · exact q2_cert_5_9
    · exact q2_cert_5_10
  · fin_cases g
    · exact q2_cert_6_0
    · exact q2_cert_6_1
    · exact q2_cert_6_2
    · exact q2_cert_6_3
    · exact q2_cert_6_4
    · exact q2_cert_6_5
    · exact q2_cert_6_6
    · exact q2_cert_6_7
    · exact q2_cert_6_8
    · exact q2_cert_6_9
    · exact q2_cert_6_10
  · fin_cases g
    · exact q2_cert_7_0
    · exact q2_cert_7_1
    · exact q2_cert_7_2
    · exact q2_cert_7_3
    · exact q2_cert_7_4
    · exact q2_cert_7_5
    · exact q2_cert_7_6
    · exact q2_cert_7_7
    · exact q2_cert_7_8
    · exact q2_cert_7_9
    · exact q2_cert_7_10
  · fin_cases g
    · exact q2_cert_8_0
    · exact q2_cert_8_1
    · exact q2_cert_8_2
    · exact q2_cert_8_3
    · exact q2_cert_8_4
    · exact q2_cert_8_5
    · exact q2_cert_8_6
    · exact q2_cert_8_7
    · exact q2_cert_8_8
    · exact q2_cert_8_9
    · exact q2_cert_8_10
  · fin_cases g
    · exact q2_cert_9_0
    · exact q2_cert_9_1
    · exact q2_cert_9_2
    · exact q2_cert_9_3
    · exact q2_cert_9_4
    · exact q2_cert_9_5
    · exact q2_cert_9_6
    · exact q2_cert_9_7
    · exact q2_cert_9_8
    · exact q2_cert_9_9
    · exact q2_cert_9_10
  · fin_cases g
    · exact q2_cert_10_0
    · exact q2_cert_10_1
    · exact q2_cert_10_2
    · exact q2_cert_10_3
    · exact q2_cert_10_4
    · exact q2_cert_10_5
    · exact q2_cert_10_6
    · exact q2_cert_10_7
    · exact q2_cert_10_8
    · exact q2_cert_10_9
    · exact q2_cert_10_10
  · fin_cases g
    · exact q2_cert_11_0
    · exact q2_cert_11_1
    · exact q2_cert_11_2
    · exact q2_cert_11_3
    · exact q2_cert_11_4
    · exact q2_cert_11_5
    · exact q2_cert_11_6
    · exact q2_cert_11_7
    · exact q2_cert_11_8
    · exact q2_cert_11_9
    · exact q2_cert_11_10
  · fin_cases g
    · exact q2_cert_12_0
    · exact q2_cert_12_1
    · exact q2_cert_12_2
    · exact q2_cert_12_3
    · exact q2_cert_12_4
    · exact q2_cert_12_5
    · exact q2_cert_12_6
    · exact q2_cert_12_7
    · exact q2_cert_12_8
    · exact q2_cert_12_9
    · exact q2_cert_12_10
  · fin_cases g
    · exact q2_cert_13_0
    · exact q2_cert_13_1
    · exact q2_cert_13_2
    · exact q2_cert_13_3
    · exact q2_cert_13_4
    · exact q2_cert_13_5
    · exact q2_cert_13_6
    · exact q2_cert_13_7
    · exact q2_cert_13_8
    · exact q2_cert_13_9
    · exact q2_cert_13_10
  · fin_cases g
    · exact q2_cert_14_0
    · exact q2_cert_14_1
    · exact q2_cert_14_2
    · exact q2_cert_14_3
    · exact q2_cert_14_4
    · exact q2_cert_14_5
    · exact q2_cert_14_6
    · exact q2_cert_14_7
    · exact q2_cert_14_8
    · exact q2_cert_14_9
    · exact q2_cert_14_10
  · fin_cases g
    · exact q2_cert_15_0
    · exact q2_cert_15_1
    · exact q2_cert_15_2
    · exact q2_cert_15_3
    · exact q2_cert_15_4
    · exact q2_cert_15_5
    · exact q2_cert_15_6
    · exact q2_cert_15_7
    · exact q2_cert_15_8
    · exact q2_cert_15_9
    · exact q2_cert_15_10
  · fin_cases g
    · exact q2_cert_16_0
    · exact q2_cert_16_1
    · exact q2_cert_16_2
    · exact q2_cert_16_3
    · exact q2_cert_16_4
    · exact q2_cert_16_5
    · exact q2_cert_16_6
    · exact q2_cert_16_7
    · exact q2_cert_16_8
    · exact q2_cert_16_9
    · exact q2_cert_16_10
  · fin_cases g
    · exact q2_cert_17_0
    · exact q2_cert_17_1
    · exact q2_cert_17_2
    · exact q2_cert_17_3
    · exact q2_cert_17_4
    · exact q2_cert_17_5
    · exact q2_cert_17_6
    · exact q2_cert_17_7
    · exact q2_cert_17_8
    · exact q2_cert_17_9
    · exact q2_cert_17_10
  · fin_cases g
    · exact q2_cert_18_0
    · exact q2_cert_18_1
    · exact q2_cert_18_2
    · exact q2_cert_18_3
    · exact q2_cert_18_4
    · exact q2_cert_18_5
    · exact q2_cert_18_6
    · exact q2_cert_18_7
    · exact q2_cert_18_8
    · exact q2_cert_18_9
    · exact q2_cert_18_10
  · fin_cases g
    · exact q2_cert_19_0
    · exact q2_cert_19_1
    · exact q2_cert_19_2
    · exact q2_cert_19_3
    · exact q2_cert_19_4
    · exact q2_cert_19_5
    · exact q2_cert_19_6
    · exact q2_cert_19_7
    · exact q2_cert_19_8
    · exact q2_cert_19_9
    · exact q2_cert_19_10
  · fin_cases g
    · exact q2_cert_20_0
    · exact q2_cert_20_1
    · exact q2_cert_20_2
    · exact q2_cert_20_3
    · exact q2_cert_20_4
    · exact q2_cert_20_5
    · exact q2_cert_20_6
    · exact q2_cert_20_7
    · exact q2_cert_20_8
    · exact q2_cert_20_9
    · exact q2_cert_20_10
  · fin_cases g
    · exact q2_cert_21_0
    · exact q2_cert_21_1
    · exact q2_cert_21_2
    · exact q2_cert_21_3
    · exact q2_cert_21_4
    · exact q2_cert_21_5
    · exact q2_cert_21_6
    · exact q2_cert_21_7
    · exact q2_cert_21_8
    · exact q2_cert_21_9
    · exact q2_cert_21_10
  · fin_cases g
    · exact q2_cert_22_0
    · exact q2_cert_22_1
    · exact q2_cert_22_2
    · exact q2_cert_22_3
    · exact q2_cert_22_4
    · exact q2_cert_22_5
    · exact q2_cert_22_6
    · exact q2_cert_22_7
    · exact q2_cert_22_8
    · exact q2_cert_22_9
    · exact q2_cert_22_10
  · fin_cases g
    · exact q2_cert_23_0
    · exact q2_cert_23_1
    · exact q2_cert_23_2
    · exact q2_cert_23_3
    · exact q2_cert_23_4
    · exact q2_cert_23_5
    · exact q2_cert_23_6
    · exact q2_cert_23_7
    · exact q2_cert_23_8
    · exact q2_cert_23_9
    · exact q2_cert_23_10
  · fin_cases g
    · exact q2_cert_24_0
    · exact q2_cert_24_1
    · exact q2_cert_24_2
    · exact q2_cert_24_3
    · exact q2_cert_24_4
    · exact q2_cert_24_5
    · exact q2_cert_24_6
    · exact q2_cert_24_7
    · exact q2_cert_24_8
    · exact q2_cert_24_9
    · exact q2_cert_24_10
  · fin_cases g
    · exact q2_cert_25_0
    · exact q2_cert_25_1
    · exact q2_cert_25_2
    · exact q2_cert_25_3
    · exact q2_cert_25_4
    · exact q2_cert_25_5
    · exact q2_cert_25_6
    · exact q2_cert_25_7
    · exact q2_cert_25_8
    · exact q2_cert_25_9
    · exact q2_cert_25_10
  · fin_cases g
    · exact q2_cert_26_0
    · exact q2_cert_26_1
    · exact q2_cert_26_2
    · exact q2_cert_26_3
    · exact q2_cert_26_4
    · exact q2_cert_26_5
    · exact q2_cert_26_6
    · exact q2_cert_26_7
    · exact q2_cert_26_8
    · exact q2_cert_26_9
    · exact q2_cert_26_10
  · fin_cases g
    · exact q2_cert_27_0
    · exact q2_cert_27_1
    · exact q2_cert_27_2
    · exact q2_cert_27_3
    · exact q2_cert_27_4
    · exact q2_cert_27_5
    · exact q2_cert_27_6
    · exact q2_cert_27_7
    · exact q2_cert_27_8
    · exact q2_cert_27_9
    · exact q2_cert_27_10
  · fin_cases g
    · exact q2_cert_28_0
    · exact q2_cert_28_1
    · exact q2_cert_28_2
    · exact q2_cert_28_3
    · exact q2_cert_28_4
    · exact q2_cert_28_5
    · exact q2_cert_28_6
    · exact q2_cert_28_7
    · exact q2_cert_28_8
    · exact q2_cert_28_9
    · exact q2_cert_28_10
  · fin_cases g
    · exact q2_cert_29_0
    · exact q2_cert_29_1
    · exact q2_cert_29_2
    · exact q2_cert_29_3
    · exact q2_cert_29_4
    · exact q2_cert_29_5
    · exact q2_cert_29_6
    · exact q2_cert_29_7
    · exact q2_cert_29_8
    · exact q2_cert_29_9
    · exact q2_cert_29_10
  · fin_cases g
    · exact q2_cert_30_0
    · exact q2_cert_30_1
    · exact q2_cert_30_2
    · exact q2_cert_30_3
    · exact q2_cert_30_4
    · exact q2_cert_30_5
    · exact q2_cert_30_6
    · exact q2_cert_30_7
    · exact q2_cert_30_8
    · exact q2_cert_30_9
    · exact q2_cert_30_10
  · fin_cases g
    · exact q2_cert_31_0
    · exact q2_cert_31_1
    · exact q2_cert_31_2
    · exact q2_cert_31_3
    · exact q2_cert_31_4
    · exact q2_cert_31_5
    · exact q2_cert_31_6
    · exact q2_cert_31_7
    · exact q2_cert_31_8
    · exact q2_cert_31_9
    · exact q2_cert_31_10
  · fin_cases g
    · exact q2_cert_32_0
    · exact q2_cert_32_1
    · exact q2_cert_32_2
    · exact q2_cert_32_3
    · exact q2_cert_32_4
    · exact q2_cert_32_5
    · exact q2_cert_32_6
    · exact q2_cert_32_7
    · exact q2_cert_32_8
    · exact q2_cert_32_9
    · exact q2_cert_32_10
  · fin_cases g
    · exact q2_cert_33_0
    · exact q2_cert_33_1
    · exact q2_cert_33_2
    · exact q2_cert_33_3
    · exact q2_cert_33_4
    · exact q2_cert_33_5
    · exact q2_cert_33_6
    · exact q2_cert_33_7
    · exact q2_cert_33_8
    · exact q2_cert_33_9
    · exact q2_cert_33_10

lemma q2_ordered_impossible (c : Fin 34) (a b d : Fin 33)
    (hab : a ≤ b) (hbd : b ≤ d) : q2_bad c a b d = false := by
  let g : Fin 11 := ⟨a.val / 3, by omega⟩
  let r : Fin 3 := ⟨a.val % 3, by omega⟩
  have ha : q2_index g r = a := by
    apply Fin.ext
    simp only [q2_index, g, r]
    omega
  have h := q2_all_blocks c g r b d
  rw [ha] at h
  simpa only [q2_ordered_bad, hab, hbd, and_self, decide_true, Bool.true_and] using h

lemma q2_impossible (c : Fin 34) (a b d : Fin 33) : q2_bad c a b d = false := by
  by_cases hab : a ≤ b
  · by_cases hbd : b ≤ d
    · exact q2_ordered_impossible c a b d hab hbd
    · by_cases had : a ≤ d
      · have h := q2_ordered_impossible c a d b had (by omega)
        rw [q2_bad_swap, q2_bad_rotate] at h
        exact h
      · have h := q2_ordered_impossible c d a b (by omega) hab
        rw [q2_bad_rotate] at h
        exact h
  · by_cases had : a ≤ d
    · have h := q2_ordered_impossible c b a d (by omega) had
      rw [q2_bad_swap] at h
      exact h
    · by_cases hbd : b ≤ d
      · have h := q2_ordered_impossible c b d a hbd (by omega)
        rw [← q2_bad_rotate] at h
        exact h
      · have h := q2_ordered_impossible c d b a (by omega) (by omega)
        rw [q2_bad_swap, ← q2_bad_rotate] at h
        exact h

end PEqualNP.Outside.L_meta_6659_aux
