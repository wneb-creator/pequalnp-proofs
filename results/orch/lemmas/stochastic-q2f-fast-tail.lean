def q2f_list_card : List (Fin 128) → Nat
  | [] => 0
  | x :: xs => q2f_list_card xs + if x ∈ xs then 0 else 1

lemma q2f_list_card_correct (xs : List (Fin 128)) :
    q2f_list_card xs = xs.toFinset.card := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [q2f_list_card,ih,List.toFinset_cons]
    by_cases member : x ∈ xs
    · have hm : x ∈ xs.toFinset := List.mem_toFinset.mpr member
      rw [if_pos member,Finset.insert_eq_of_mem hm,Nat.add_zero]
    · have hm : x ∉ xs.toFinset := by simpa only [List.mem_toFinset] using member
      rw [if_neg member,Finset.card_insert_of_notMem hm]
def q2f_fast_card (m : Fin 128) : Nat :=
  (m.val / 1 % 2) + (m.val / 2 % 2) + (m.val / 4 % 2) + (m.val / 8 % 2) + (m.val / 16 % 2) + (m.val / 32 % 2) + (m.val / 64 % 2)

lemma q2f_fast_card_correct : ∀ m : Fin 128, q2f_fast_card m = cap7_card m := by
  decide +kernel

def q2f_fast_size (s : Fin 15) (a b c : Fin 10) : Nat :=
  q2f_list_card [q2f_raw s a b c 0,q2f_raw s a b c 1,q2f_raw s a b c 2,q2f_raw s a b c 3,q2f_raw s a b c 4,q2f_raw s a b c 5,q2f_raw s a b c 6,q2f_raw s a b c 7,q2f_raw s a b c 8,q2f_raw s a b c 9]

lemma q2f_fast_size_eq (s : Fin 15) (a b c : Fin 10) :
    q2f_fast_size s a b c = (q2f_codes s a b c).card := by
  unfold q2f_fast_size
  rw [q2f_list_card_correct]
  apply congrArg Finset.card
  ext m
  simp [q2f_codes]

def q2f_fast_small (s : Fin 15) (a b c : Fin 10) (m : Fin 128) : Bool :=
  decide (q2f_fast_card m ≤ 1) || (decide (q2f_fast_card m = 2) && (q2f_outside m || q2f_mem s a b c m))

def q2f_fast_allowed (s : Fin 15) (a b c : Fin 10) (m : Fin 128) : Bool :=
  q2f_fast_small s a b c m || q2f_mem s a b c m

def q2f_fast_closed (s : Fin 15) (a b c : Fin 10) (m : Fin 128) : Bool :=
  q2f_fast_small s a b c m || decide (m = q2f_known s a b c 0) || decide (m = q2f_known s a b c 1) || decide (m = q2f_known s a b c 2)

def q2f_fast_seed (s : Fin 15) (a b c : Fin 10) (m : Fin 128) : Bool :=
  decide (q2f_fast_card m = 3 ∨ q2f_fast_card m = 4) &&
    ((q2f_fast_small s a b c (q2f_cut m 0 0) && q2f_fast_small s a b c (q2f_cut m 0 1)) || (q2f_fast_small s a b c (q2f_cut m 1 0) && q2f_fast_small s a b c (q2f_cut m 1 1)) || (q2f_fast_small s a b c (q2f_cut m 2 0) && q2f_fast_small s a b c (q2f_cut m 2 1)))

def q2f_fast_grow (s : Fin 15) (a b c : Fin 10) (x m : Fin 128) : Bool :=
  q2f_sub x m && q2f_fast_small s a b c (q2f_diff m x)

def q2f_fast_node (s : Fin 15) (a b c : Fin 10) (i : Fin 10) : Bool :=
  let m := q2f_raw s a b c i
  q2f_fast_closed s a b c m ||
    (!q2f_fast_seed s a b c m && !q2f_fast_grow s a b c (q2f_known s a b c 0) m &&
    !q2f_fast_grow s a b c (q2f_known s a b c 1) m &&
    !q2f_fast_grow s a b c (q2f_known s a b c 2) m)

def q2f_fast_pair (s : Fin 15) (a b c : Fin 10) (i j : Fin 3) : Bool :=
  let u := q2f_union (q2f_known s a b c i) (q2f_known s a b c j)
  let v := q2f_inter (q2f_known s a b c i) (q2f_known s a b c j)
  (!q2f_fast_allowed s a b c u || q2f_fast_closed s a b c u) &&
    (!q2f_fast_allowed s a b c v || q2f_fast_closed s a b c v)

def q2f_fast_generators (s : Fin 15) (a b c : Fin 10) : Bool :=
  q2f_fast_node s a b c 0 &&
    q2f_fast_node s a b c 1 &&
    q2f_fast_node s a b c 2 &&
    q2f_fast_node s a b c 3 &&
    q2f_fast_node s a b c 4 &&
    q2f_fast_node s a b c 5 &&
    q2f_fast_node s a b c 6 &&
    q2f_fast_node s a b c 7 &&
    q2f_fast_node s a b c 8 &&
    q2f_fast_node s a b c 9 &&
    q2f_fast_pair s a b c 0 1 &&
    q2f_fast_pair s a b c 0 2 &&
    q2f_fast_pair s a b c 1 2

def q2f_fast_shape (s : Fin 15) (a b c : Fin 10) : Bool :=
  (decide (q2f_fast_card (q2f_raw s a b c 0) ≤ 2) || decide (q2f_raw s a b c 0 = 11) || decide (q2f_raw s a b c 0 = 69) || decide (q2f_raw s a b c 0 = 49) || decide (q2f_raw s a b c 0 = q2f_superCode s)) &&
    (decide (q2f_fast_card (q2f_raw s a b c 1) ≤ 2) || decide (q2f_raw s a b c 1 = 11) || decide (q2f_raw s a b c 1 = 69) || decide (q2f_raw s a b c 1 = 49) || decide (q2f_raw s a b c 1 = q2f_superCode s)) &&
    (decide (q2f_fast_card (q2f_raw s a b c 2) ≤ 2) || decide (q2f_raw s a b c 2 = 11) || decide (q2f_raw s a b c 2 = 69) || decide (q2f_raw s a b c 2 = 49) || decide (q2f_raw s a b c 2 = q2f_superCode s)) &&
    (decide (q2f_fast_card (q2f_raw s a b c 3) ≤ 2) || decide (q2f_raw s a b c 3 = 11) || decide (q2f_raw s a b c 3 = 69) || decide (q2f_raw s a b c 3 = 49) || decide (q2f_raw s a b c 3 = q2f_superCode s)) &&
    (decide (q2f_fast_card (q2f_raw s a b c 4) ≤ 2) || decide (q2f_raw s a b c 4 = 11) || decide (q2f_raw s a b c 4 = 69) || decide (q2f_raw s a b c 4 = 49) || decide (q2f_raw s a b c 4 = q2f_superCode s)) &&
    (decide (q2f_fast_card (q2f_raw s a b c 5) ≤ 2) || decide (q2f_raw s a b c 5 = 11) || decide (q2f_raw s a b c 5 = 69) || decide (q2f_raw s a b c 5 = 49) || decide (q2f_raw s a b c 5 = q2f_superCode s)) &&
    (decide (q2f_fast_card (q2f_raw s a b c 6) ≤ 2) || decide (q2f_raw s a b c 6 = 11) || decide (q2f_raw s a b c 6 = 69) || decide (q2f_raw s a b c 6 = 49) || decide (q2f_raw s a b c 6 = q2f_superCode s)) &&
    (decide (q2f_fast_card (q2f_raw s a b c 7) ≤ 2) || decide (q2f_raw s a b c 7 = 11) || decide (q2f_raw s a b c 7 = 69) || decide (q2f_raw s a b c 7 = 49) || decide (q2f_raw s a b c 7 = q2f_superCode s)) &&
    (decide (q2f_fast_card (q2f_raw s a b c 8) ≤ 2) || decide (q2f_raw s a b c 8 = 11) || decide (q2f_raw s a b c 8 = 69) || decide (q2f_raw s a b c 8 = 49) || decide (q2f_raw s a b c 8 = q2f_superCode s)) &&
    (decide (q2f_fast_card (q2f_raw s a b c 9) ≤ 2) || decide (q2f_raw s a b c 9 = 11) || decide (q2f_raw s a b c 9 = 69) || decide (q2f_raw s a b c 9 = 49) || decide (q2f_raw s a b c 9 = q2f_superCode s))

def q2f_fast_certificate (s : Fin 15) (a b c : Fin 10) : Bool :=
  decide (7 ≤ q2f_fast_size s a b c) &&
    (decide (8 ≤ q2f_fast_size s a b c) || q2f_fast_shape s a b c ||
      (q2f_fast_generators s a b c && !q2f_fast_closed s a b c (q2f_missing s a b c)))

lemma q2f_fast_small_eq (s : Fin 15) (a b c : Fin 10) (m : Fin 128) :
    q2f_fast_small s a b c m = q2f_small s a b c m := by
  simp only [q2f_fast_small,q2f_small,q2f_fast_card_correct,q2f_fast_size_eq]

lemma q2f_fast_allowed_eq (s : Fin 15) (a b c : Fin 10) (m : Fin 128) :
    q2f_fast_allowed s a b c m = q2f_allowed s a b c m := by
  simp only [q2f_fast_allowed,q2f_allowed,q2f_fast_card_correct,q2f_fast_size_eq,q2f_fast_small_eq]

lemma q2f_fast_closed_eq (s : Fin 15) (a b c : Fin 10) (m : Fin 128) :
    q2f_fast_closed s a b c m = q2f_closed s a b c m := by
  simp only [q2f_fast_closed,q2f_closed,q2f_fast_card_correct,q2f_fast_size_eq,q2f_fast_small_eq,q2f_fast_allowed_eq]

lemma q2f_fast_seed_eq (s : Fin 15) (a b c : Fin 10) (m : Fin 128) :
    q2f_fast_seed s a b c m = q2f_seed s a b c m := by
  simp only [q2f_fast_seed,q2f_seed,q2f_fast_card_correct,q2f_fast_size_eq,q2f_fast_small_eq,q2f_fast_allowed_eq,q2f_fast_closed_eq]

lemma q2f_fast_grow_eq (s : Fin 15) (a b c : Fin 10) (x m : Fin 128) :
    q2f_fast_grow s a b c x m = q2f_grow s a b c x m := by
  simp only [q2f_fast_grow,q2f_grow,q2f_fast_card_correct,q2f_fast_size_eq,q2f_fast_small_eq,q2f_fast_allowed_eq,q2f_fast_closed_eq,q2f_fast_seed_eq]

lemma q2f_fast_node_eq (s : Fin 15) (a b c : Fin 10) (i : Fin 10) :
    q2f_fast_node s a b c i = q2f_node s a b c i := by
  simp only [q2f_fast_node,q2f_node,q2f_fast_card_correct,q2f_fast_size_eq,q2f_fast_small_eq,q2f_fast_allowed_eq,q2f_fast_closed_eq,q2f_fast_seed_eq,q2f_fast_grow_eq]

lemma q2f_fast_pair_eq (s : Fin 15) (a b c : Fin 10) (i j : Fin 3) :
    q2f_fast_pair s a b c i j = q2f_pair s a b c i j := by
  simp only [q2f_fast_pair,q2f_pair,q2f_fast_card_correct,q2f_fast_size_eq,q2f_fast_small_eq,q2f_fast_allowed_eq,q2f_fast_closed_eq,q2f_fast_seed_eq,q2f_fast_grow_eq,q2f_fast_node_eq]

lemma q2f_fast_generators_eq (s : Fin 15) (a b c : Fin 10) :
    q2f_fast_generators s a b c = q2f_generators s a b c := by
  simp only [q2f_fast_generators,q2f_generators,q2f_fast_card_correct,q2f_fast_size_eq,q2f_fast_small_eq,q2f_fast_allowed_eq,q2f_fast_closed_eq,q2f_fast_seed_eq,q2f_fast_grow_eq,q2f_fast_node_eq,q2f_fast_pair_eq]

lemma q2f_fast_shape_eq (s : Fin 15) (a b c : Fin 10) :
    q2f_fast_shape s a b c = q2f_shape s a b c := by
  simp only [q2f_fast_shape,q2f_shape,q2f_fast_card_correct,q2f_fast_size_eq,q2f_fast_small_eq,q2f_fast_allowed_eq,q2f_fast_closed_eq,q2f_fast_seed_eq,q2f_fast_grow_eq,q2f_fast_node_eq,q2f_fast_pair_eq,q2f_fast_generators_eq]

lemma q2f_fast_certificate_eq (s : Fin 15) (a b c : Fin 10) :
    q2f_fast_certificate s a b c = q2f_certificate s a b c := by
  simp only [q2f_fast_certificate,q2f_certificate,q2f_fast_card_correct,q2f_fast_size_eq,q2f_fast_small_eq,q2f_fast_allowed_eq,q2f_fast_closed_eq,q2f_fast_seed_eq,q2f_fast_grow_eq,q2f_fast_node_eq,q2f_fast_pair_eq,q2f_fast_generators_eq,q2f_fast_shape_eq]
