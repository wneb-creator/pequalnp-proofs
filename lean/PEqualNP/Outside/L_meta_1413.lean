import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1413

open PEqualNP.CircuitLowerBounds

/-! ## 1. Basic evaluation lemmas for Circuit.wires -/

def stepWires (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_step_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl stepWires acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, List.length_cons]
    rw [ih (stepWires acc g)]
    simp [stepWires]
    omega

lemma foldl_step_getD_prefix (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl stepWires acc).getD i false = acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hi' : i < (stepWires acc g).length := by simp [stepWires]; omega
    rw [ih (stepWires acc g) hi']
    simp only [stepWires, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_step_getD_gate (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWires acc).getD (acc.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < acc.length + j then (gs.foldl stepWires acc).getD i false else false) := by
  induction gs generalizing acc j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero]
      have hlen : acc.length < (stepWires acc g).length := by simp [stepWires]
      rw [foldl_step_getD_prefix gs (stepWires acc g) acc.length hlen]
      have hval : (stepWires acc g).getD acc.length false =
          g.op.eval (g.inputs.map fun i => acc.getD i false) := by
        simp [stepWires, List.getD_eq_getElem?_getD]
      rw [hval]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < acc.length
      · simp only [hi, ↓reduceIte]
        have hi' : i < (stepWires acc g).length := by simp [stepWires]; omega
        rw [foldl_step_getD_prefix gs (stepWires acc g) i hi']
        simp only [stepWires, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · simp only [hi, ↓reduceIte]
        simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_lt hi),
          Option.getD_none]
    | succ j' =>
      have hj' : j' < gs.length := Nat.lt_of_succ_lt_succ hj
      simp only [List.foldl_cons, List.getElem_cons_succ]
      have heq : acc.length + (j' + 1) = (stepWires acc g).length + j' := by
        simp [stepWires]; omega
      rw [heq]
      exact ih (stepWires acc g) j' hj'

def wireVal {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq_foldl {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    C.wires (List.ofFn x) = C.gates.foldl stepWires (List.ofFn x) := rfl

lemma wireVal_length {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.size := by
  rw [wires_eq_foldl, foldl_step_length, List.length_ofFn]; rfl

lemma wireVal_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    wireVal C x i.val = x i := by
  unfold wireVal
  rw [wires_eq_foldl]
  have hi : i.val < (List.ofFn x).length := by simp
  rw [foldl_step_getD_prefix C.gates (List.ofFn x) i.val hi]
  simp [List.getD_eq_getElem?_getD]

lemma wireVal_gate {n G : ℕ} (C : Circuit) (hsize : C.size = G) (x : Fin n → Bool) (j : Fin G) :
    wireVal C x (n + j.val) =
      (C.gates[j.val]'(by have := j.isLt; unfold Circuit.size at hsize; omega)).op.eval
        ((C.gates[j.val]'(by have := j.isLt; unfold Circuit.size at hsize; omega)).inputs.map fun i =>
          if i < n + j.val then wireVal C x i else false) := by
  unfold wireVal
  rw [wires_eq_foldl]
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hj : j.val < C.gates.length := by have := j.isLt; unfold Circuit.size at hsize; omega
  have h := foldl_step_getD_gate C.gates (List.ofFn x) j.val hj
  simpa [hlen] using h

lemma wireVal_out_of_range {n G : ℕ} (C : Circuit) (hsize : C.size = G)
    (x : Fin n → Bool) (w : ℕ) (hw : n + G ≤ w) :
    wireVal C x w = false := by
  unfold wireVal
  have hlen : (C.wires (List.ofFn x)).length ≤ w := by
    rw [wireVal_length, hsize]; exact hw
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hlen]

/-! ## 2. Properties of the cycle edge function on Fin n (for 5 <= n) -/

def cycleEdge (n : ℕ) [NeZero n] (x : Fin n → Bool) : Prop :=
  ∃ i : Fin n, x i = true ∧ x (i + 1) = true

lemma fin_add_k_ne_self {n : ℕ} [NeZero n] (k : ℕ) (hk0 : 0 < k) (hkn : k < n) (p : Fin n) :
    p + (⟨k, hkn⟩ : Fin n) ≠ p := by
  intro h
  have hv := congrArg Fin.val h
  have hp := p.isLt
  simp [Fin.val_add] at hv
  by_cases hlt : p.val + k < n
  · rw [Nat.mod_eq_of_lt hlt] at hv; omega
  · have hmod : (p.val + k) % n = p.val + k - n := by
      rw [Nat.mod_eq_sub_mod (by omega), Nat.mod_eq_of_lt (by omega)]
    rw [hmod] at hv; omega

lemma fin_add1_ne_self {n : ℕ} [NeZero n] (hn : 5 ≤ n) (p : Fin n) : p + 1 ≠ p := by
  have h1 : (1 : Fin n) = ⟨1, by omega⟩ := by ext; simp [Nat.mod_eq_of_lt (by omega : 1 < n)]
  rw [h1]; exact fin_add_k_ne_self 1 (by omega) (by omega) p

lemma fin_add2_ne_self {n : ℕ} [NeZero n] (hn : 5 ≤ n) (p : Fin n) : p + 1 + 1 ≠ p := by
  have h2 : p + 1 + 1 = p + ⟨2, by omega⟩ := by
    ext; simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n)]
  rw [h2]; exact fin_add_k_ne_self 2 (by omega) (by omega) p

lemma fin_add3_ne_self {n : ℕ} [NeZero n] (hn : 5 ≤ n) (p : Fin n) : p + 1 + 1 + 1 ≠ p := by
  have h3 : p + 1 + 1 + 1 = p + ⟨3, by omega⟩ := by
    ext; simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n)]
  rw [h3]; exact fin_add_k_ne_self 3 (by omega) (by omega) p

lemma fin_add4_ne_self {n : ℕ} [NeZero n] (hn : 5 ≤ n) (p : Fin n) : p + 1 + 1 + 1 + 1 ≠ p := by
  have h4 : p + 1 + 1 + 1 + 1 = p + ⟨4, by omega⟩ := by
    ext; simp [Fin.val_add, Nat.mod_eq_of_lt (by omega : 1 < n)]
  rw [h4]; exact fin_add_k_ne_self 4 (by omega) (by omega) p

lemma cycleEdge_not_const_restrict {n : ℕ} [NeZero n] (hn : 5 ≤ n) (p : Fin n) (b : Bool) :
    ∃ y z : Fin n → Bool, y p = b ∧ z p = b ∧ (cycleEdge n y ↔ ¬ cycleEdge n z) := by
  let y : Fin n → Bool := fun i => if i = p then b else false
  let z : Fin n → Bool := fun i => if i = p then b else decide (i = p + 1 ∨ i = p + 1 + 1)
  refine ⟨y, z, by simp [y], by simp [z], ?_⟩
  have h1 : p + 1 ≠ p := fin_add1_ne_self hn p
  have h2 : p + 1 + 1 ≠ p := fin_add2_ne_self hn p
  have hy : ¬ cycleEdge n y := by
    rintro ⟨i, hi1, hi2⟩
    have h1' : i = p := by by_contra hne; simp [y, hne] at hi1
    have h2' : i + 1 = p := by by_contra hne; simp [y, hne] at hi2
    subst h1'; exact h1 h2'
  have hz : cycleEdge n z := by
    refine ⟨p + 1, by simp [z, h1], by simp [z, h2]⟩
  tauto

lemma cycleEdge_not_const {n : ℕ} [NeZero n] (hn : 5 ≤ n) :
    ∃ y z : Fin n → Bool, cycleEdge n y ↔ ¬ cycleEdge n z := by
  rcases cycleEdge_not_const_restrict hn 0 false with ⟨y, z, _, _, h⟩
  exact ⟨y, z, h⟩

lemma cycleEdge_not_eq_input {n : ℕ} [NeZero n] (hn : 5 ≤ n) (p : Fin n) :
    ¬ (∀ x : Fin n → Bool, cycleEdge n x ↔ x p = true) := by
  intro h
  let x : Fin n → Bool := fun i => decide (i = p)
  have hx : cycleEdge n x := (h x).mpr (by simp [x])
  rcases hx with ⟨i, hi1, hi2⟩
  simp [x] at hi1 hi2
  subst hi1
  exact fin_add1_ne_self hn i hi2

lemma cycleEdge_not_eq_not_input {n : ℕ} [NeZero n] (p : Fin n) :
    ¬ (∀ x : Fin n → Bool, cycleEdge n x ↔ x p = false) := by
  intro h
  have hx : cycleEdge n (fun _ => false) := (h (fun _ => false)).mpr rfl
  rcases hx with ⟨i, hi1, _⟩
  simp at hi1

lemma cycleEdge_two_bits_false {n : ℕ} [NeZero n] (hn : 5 ≤ n) (a b : Fin n) (x : Fin n → Bool)
    (hx : ∀ i, x i = true → i = a ∨ i = b) (hab : a + 1 ≠ b) (hba : b + 1 ≠ a) :
    ¬ cycleEdge n x := by
  rintro ⟨i, hi1, hi2⟩
  rcases hx i hi1 with rfl | rfl <;> rcases hx (i + 1) hi2 with h | h
  · exact fin_add1_ne_self hn i h
  · exact hab h
  · exact hba h
  · exact fin_add1_ne_self hn i h

lemma exists_private_nbr {n : ℕ} [NeZero n] (hn : 5 ≤ n) (u v : Fin n)
    (huv : u ≠ v) (h1 : u + 1 ≠ v) (_h2 : v + 1 ≠ u) :
    ∃ w : Fin n, (w + 1 = u ∨ u + 1 = w) ∧ w ≠ u ∧ w ≠ v ∧ w + 1 ≠ v ∧ v + 1 ≠ w := by
  by_cases hcase : u + 1 + 1 = v
  · refine ⟨u - 1, Or.inl (by abel), ?_, ?_, ?_, ?_⟩
    · intro h; exact fin_add1_ne_self hn (u - 1) (by rw [sub_add_cancel]; exact h.symm)
    · intro h
      have h3 : (u - 1) + 1 + 1 + 1 = u - 1 := by
        rw [sub_add_cancel, hcase]; exact h.symm
      exact fin_add3_ne_self hn (u - 1) h3
    · intro h; rw [sub_add_cancel] at h; exact huv h
    · intro h
      have h4 : (u - 1) + 1 + 1 + 1 + 1 = u - 1 := by
        rw [sub_add_cancel, hcase]; exact h
      exact fin_add4_ne_self hn (u - 1) h4
  · refine ⟨u + 1, Or.inr rfl, fin_add1_ne_self hn u, h1, hcase, ?_⟩
    intro h; exact huv (add_right_cancel h).symm

lemma bool_three_not_distinct {a b c : Bool} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : b ≠ c) : False := by
  cases a <;> cases b <;> cases c <;> simp at h1 h2 h3

lemma cycleEdge_three_subfunctions {n : ℕ} [NeZero n] (hn : 5 ≤ n)
    (u v : Fin n) (huv : u ≠ v) (h : Bool → Bool → Bool) :
    ¬ (∀ x y : Fin n → Bool,
        (∀ i, i ≠ u → i ≠ v → x i = y i) →
        h (x u) (x v) = h (y u) (y v) →
        (cycleEdge n x ↔ cycleEdge n y)) := by
  intro hbot
  let mk (a b : Bool) (w : Option (Fin n)) : Fin n → Bool :=
    fun i => if i = u then a else if i = v then b else
      match w with | none => false | some z => decide (i = z)
  have hsep : ∀ (a1 b1 a2 b2 : Bool) (w : Option (Fin n)),
      (cycleEdge n (mk a1 b1 w) ↔ ¬ cycleEdge n (mk a2 b2 w)) →
      h a1 b1 ≠ h a2 b2 := by
    intro a1 b1 a2 b2 w hdiff heq
    have hrest : ∀ i, i ≠ u → i ≠ v → mk a1 b1 w i = mk a2 b2 w i := by
      intro i hi1 hi2; simp [mk, hi1, hi2]
    have heq' : h (mk a1 b1 w u) (mk a1 b1 w v) = h (mk a2 b2 w u) (mk a2 b2 w v) := by
      simp [mk, Ne.symm huv, heq]
    have hiff := hbot (mk a1 b1 w) (mk a2 b2 w) hrest heq'
    tauto
  have h_adj_case : ∀ (p q : Fin n), p ≠ q → q = p + 1 →
      ∀ (hpq : (p = u ∧ q = v) ∨ (p = v ∧ q = u)), False := by
    intro p q hpq_ne hq hpq
    have h11_10 : h true true ≠ h true false := by
      apply hsep true true true false none
      have ht : cycleEdge n (mk true true none) := by
        refine ⟨p, ?_, ?_⟩
        · rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [mk, huv, Ne.symm huv]
        · rw [← hq]; rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [mk, huv, Ne.symm huv]
      have hf : ¬ cycleEdge n (mk true false none) := by
        apply cycleEdge_two_bits_false hn u u _ _ (fin_add1_ne_self hn u) (fin_add1_ne_self hn u)
        intro i hi; simp only [mk] at hi
        by_cases hiu : i = u
        · left; exact hiu
        · by_cases hiv : i = v
          · simp [hiv] at hi; exact absurd hi.symm huv
          · simp [hiu, hiv] at hi
      tauto
    have h11_01 : h true true ≠ h false true := by
      apply hsep true true false true none
      have ht : cycleEdge n (mk true true none) := by
        refine ⟨p, ?_, ?_⟩
        · rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [mk, huv, Ne.symm huv]
        · rw [← hq]; rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [mk, huv, Ne.symm huv]
      have hf : ¬ cycleEdge n (mk false true none) := by
        apply cycleEdge_two_bits_false hn v v _ _ (fin_add1_ne_self hn v) (fin_add1_ne_self hn v)
        intro i hi; simp only [mk] at hi
        by_cases hiu : i = u
        · simp [hiu] at hi
        · by_cases hiv : i = v
          · left; exact hiv
          · simp [hiu, hiv] at hi
      tauto
    have h10_01 : h true false ≠ h false true := by
      apply hsep true false false true (some (p - 1))
      have hp1_ne_p : p - 1 ≠ p := by
        intro heq; exact fin_add1_ne_self hn (p - 1) (by rw [sub_add_cancel]; exact heq.symm)
      have hp1_ne_q : p - 1 ≠ q := by
        intro heq; rw [hq] at heq
        exact fin_add2_ne_self hn (p - 1) (by rw [sub_add_cancel]; exact heq.symm)
      have hq_ne_pm1_plus1 : (p - 1) + 1 ≠ q := by
        rw [sub_add_cancel, hq]; exact (fin_add1_ne_self hn p).symm
      have hq_plus1_ne_pm1 : q + 1 ≠ p - 1 := by
        rw [hq]; intro heq
        exact fin_add3_ne_self hn (p - 1) (by rw [sub_add_cancel]; exact heq)
      rcases hpq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have ht : cycleEdge n (mk true false (some (p - 1))) := by
          refine ⟨p - 1, ?_, ?_⟩
          · simp [mk, hp1_ne_p, hp1_ne_q]
          · rw [sub_add_cancel]; simp [mk]
        have hf : ¬ cycleEdge n (mk false true (some (p - 1))) := by
          apply cycleEdge_two_bits_false hn (p - 1) q _ _ hq_ne_pm1_plus1 hq_plus1_ne_pm1
          intro i hi; simp only [mk] at hi
          by_cases h1 : i = p
          · simp [h1] at hi
          · by_cases h2 : i = q
            · right; exact h2
            · simp [h1, h2] at hi; left; exact hi
        tauto
      · have hf : ¬ cycleEdge n (mk true false (some (p - 1))) := by
          apply cycleEdge_two_bits_false hn (p - 1) q _ _ hq_ne_pm1_plus1 hq_plus1_ne_pm1
          intro i hi; simp only [mk] at hi
          by_cases h1 : i = q
          · right; exact h1
          · by_cases h2 : i = p
            · simp [h2] at hi; exact absurd hi hpq_ne
            · simp [h1, h2] at hi; left; exact hi
        have ht : cycleEdge n (mk false true (some (p - 1))) := by
          refine ⟨p - 1, ?_, ?_⟩
          · simp [mk, hp1_ne_p, hp1_ne_q]
          · rw [sub_add_cancel]; simp [mk, hpq_ne]
        tauto
    exact bool_three_not_distinct h11_10 h11_01 h10_01
  by_cases huv1 : u + 1 = v
  · exact h_adj_case u v huv huv1.symm (Or.inl ⟨rfl, rfl⟩)
  · by_cases hvu1 : v + 1 = u
    · exact h_adj_case v u (Ne.symm huv) hvu1.symm (Or.inr ⟨rfl, rfl⟩)
    · rcases exists_private_nbr hn u v huv huv1 hvu1 with ⟨w1, hw1adj, hw1u, hw1v, hw1v1, hw1v2⟩
      rcases exists_private_nbr hn v u (Ne.symm huv) hvu1 huv1 with ⟨w2, hw2adj, hw2v, hw2u, hw2u1, hw2u2⟩
      have ht_10_w1 : cycleEdge n (mk true false (some w1)) := by
        rcases hw1adj with h' | h'
        · refine ⟨w1, by simp [mk, hw1u, hw1v], by rw [h']; simp [mk]⟩
        · refine ⟨u, by simp [mk], by rw [h']; simp [mk, hw1u, hw1v]⟩
      have hf_00_w1 : ¬ cycleEdge n (mk false false (some w1)) := by
        apply cycleEdge_two_bits_false hn w1 w1 _ _ (fin_add1_ne_self hn w1) (fin_add1_ne_self hn w1)
        intro i hi; simp only [mk] at hi
        by_cases h1 : i = u
        · simp [h1] at hi
        · by_cases h2 : i = v
          · simp [h2] at hi
          · simp [h1, h2] at hi; left; exact hi
      have hf_01_w1 : ¬ cycleEdge n (mk false true (some w1)) := by
        apply cycleEdge_two_bits_false hn w1 v _ _ hw1v1 hw1v2
        intro i hi; simp only [mk] at hi
        by_cases h1 : i = u
        · simp [h1] at hi
        · by_cases h2 : i = v
          · right; exact h2
          · simp [h1, h2] at hi; left; exact hi
      have ht_01_w2 : cycleEdge n (mk false true (some w2)) := by
        rcases hw2adj with h' | h'
        · refine ⟨w2, by simp [mk, hw2u, hw2v], by rw [h']; simp [mk, Ne.symm huv]⟩
        · refine ⟨v, by simp [mk, Ne.symm huv], by rw [h']; simp [mk, hw2u, hw2v]⟩
      have hf_00_w2 : ¬ cycleEdge n (mk false false (some w2)) := by
        apply cycleEdge_two_bits_false hn w2 w2 _ _ (fin_add1_ne_self hn w2) (fin_add1_ne_self hn w2)
        intro i hi; simp only [mk] at hi
        by_cases h1 : i = u
        · simp [h1] at hi
        · by_cases h2 : i = v
          · simp [h2] at hi
          · simp [h1, h2] at hi; left; exact hi
      have h10_00 : h true false ≠ h false false := hsep true false false false (some w1) (by tauto)
      have h10_01 : h true false ≠ h false true := hsep true false false true (some w1) (by tauto)
      have h01_00 : h false true ≠ h false false := hsep false true false false (some w2) (by tauto)
      exact bool_three_not_distinct h10_01 h10_00 h01_00

/-! ## 3. Canonical irredundant live subcircuit & gate elimination -/

def Collapses {n G : ℕ} (C : Circuit) (p : Fin n) (b : Bool) (j : Fin G) : Prop :=
  (∀ y z : Fin n → Bool, y p = b → z p = b →
      wireVal C y (n + j.val) = wireVal C z (n + j.val)) ∨
  ∃ w < n + j.val, ∀ u : Fin n → Bool, u p = b →
      wireVal C u (n + j.val) = wireVal C u w

def ConstUnder {n : ℕ} (C : Circuit) (p : Fin n) (b : Bool) (w : ℕ) : Prop :=
  ∀ y z : Fin n → Bool, y p = b → z p = b → wireVal C y w = wireVal C z w

def ConstValUnder {n : ℕ} (C : Circuit) (p : Fin n) (b : Bool) (w : ℕ) (c : Bool) : Prop :=
  ∀ u : Fin n → Bool, u p = b → wireVal C u w = c

lemma constUnder_iff_exists {n : ℕ} (C : Circuit) (p : Fin n) (b : Bool) (w : ℕ) :
    ConstUnder C p b w ↔ ∃ c : Bool, ConstValUnder C p b w c := by
  constructor
  · intro h
    let u0 : Fin n → Bool := fun _ => b
    refine ⟨wireVal C u0 w, fun u hu => h u u0 hu rfl⟩
  · rintro ⟨c, hc⟩ y z hy hz
    rw [hc y hy, hc z hz]

def IsConst {n : ℕ} (C : Circuit) (w : ℕ) : Prop :=
  ∀ y z : Fin n → Bool, wireVal C y w = wireVal C z w

def IsRed {n G : ℕ} (C : Circuit) (j : Fin G) : Prop :=
  IsConst (n := n) C (n + j.val) ∨
  ∃ w < n + j.val, ∀ u : Fin n → Bool, wireVal C u (n + j.val) = wireVal C u w

noncomputable def canon {n : ℕ} (C : Circuit) (w : ℕ) : ℕ :=
  open Classical in
  Nat.find (⟨w, fun _ => rfl⟩ : ∃ w', ∀ u : Fin n → Bool, wireVal C u w' = wireVal C u w)

lemma canon_le {n : ℕ} (C : Circuit) (w : ℕ) : canon (n := n) C w ≤ w := by
  classical
  exact Nat.find_min' _ (fun _ => rfl)

lemma canon_eq {n : ℕ} (C : Circuit) (w : ℕ) (u : Fin n → Bool) :
    wireVal C u (canon (n := n) C w) = wireVal C u w := by
  classical
  exact Nat.find_spec (⟨w, fun _ => rfl⟩ : ∃ w', ∀ u : Fin n → Bool, wireVal C u w' = wireVal C u w) u

lemma canon_min {n : ℕ} (C : Circuit) (w w' : ℕ) (hlt : w' < canon (n := n) C w) :
    ¬ (∀ u : Fin n → Bool, wireVal C u w' = wireVal C u w) := by
  classical
  exact Nat.find_min (⟨w, fun _ => rfl⟩ : ∃ w', ∀ u : Fin n → Bool, wireVal C u w' = wireVal C u w) hlt

lemma canon_le_of_eq {n : ℕ} (C : Circuit) (w w' : ℕ)
    (heq : ∀ u : Fin n → Bool, wireVal C u w' = wireVal C u w) :
    canon (n := n) C w ≤ w' := by
  classical
  exact Nat.find_min' _ heq

lemma canon_idem {n : ℕ} (C : Circuit) (w : ℕ) :
    canon (n := n) C (canon (n := n) C w) = canon (n := n) C w := by
  apply le_antisymm (canon_le C _)
  by_contra hlt
  push Not at hlt
  have hspec := canon_eq (n := n) C (canon (n := n) C w)
  have hspec2 : ∀ u : Fin n → Bool,
      wireVal C u (canon (n := n) C (canon (n := n) C w)) = wireVal C u w := by
    intro u; rw [hspec u, canon_eq C w u]
  exact canon_min C w _ hlt hspec2

lemma canon_not_red {n G : ℕ} (C : Circuit) (w : ℕ) (j : Fin G)
    (hnc : ¬ IsConst (n := n) C w) (hcan : canon (n := n) C w = n + j.val) :
    ¬ IsRed (n := n) C j := by
  rintro (hc | ⟨w', hw', heq⟩)
  · apply hnc; intro y z
    rw [← canon_eq C w y, ← canon_eq C w z, hcan]; exact hc y z
  · have hlt : w' < canon (n := n) C w := by omega
    apply canon_min C w w' hlt
    intro u
    rw [← heq u, ← hcan, canon_eq C w u]

inductive EffGate (n G : ℕ) (j : Fin G) where
  | gnot (u : ℕ) : EffGate n G j
  | gand (u v : ℕ) : EffGate n G j
  | gor (u v : ℕ) : EffGate n G j

def EffGate.inputs {n G : ℕ} {j : Fin G} : EffGate n G j → Finset ℕ
  | .gnot u => {u}
  | .gand u v => {u, v}
  | .gor u v => {u, v}

def EffGate.Valid {n G : ℕ} (C : Circuit) {j : Fin G} : EffGate n G j → Prop
  | .gnot u =>
      u < n + j.val ∧ ¬ IsConst (n := n) C u ∧ canon (n := n) C u = u ∧
      ∀ x : Fin n → Bool, wireVal C x (n + j.val) = !(wireVal C x u)
  | .gand u v =>
      u < n + j.val ∧ v < n + j.val ∧ u ≠ v ∧
      ¬ IsConst (n := n) C u ∧ ¬ IsConst (n := n) C v ∧
      canon (n := n) C u = u ∧ canon (n := n) C v = v ∧
      ∀ x : Fin n → Bool, wireVal C x (n + j.val) = (wireVal C x u && wireVal C x v)
  | .gor u v =>
      u < n + j.val ∧ v < n + j.val ∧ u ≠ v ∧
      ¬ IsConst (n := n) C u ∧ ¬ IsConst (n := n) C v ∧
      canon (n := n) C u = u ∧ canon (n := n) C v = v ∧
      ∀ x : Fin n → Bool, wireVal C x (n + j.val) = (wireVal C x u || wireVal C x v)

lemma exists_effGate {n G : ℕ} (C : Circuit) (hsize : C.size = G)
    (hgates : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (j : Fin G) (hjr : ¬ IsRed (n := n) C j) :
    ∃ eg : EffGate n G j, eg.Valid C := by
  have hjlt : j.val < C.gates.length := by have := j.isLt; unfold Circuit.size at hsize; omega
  set g := C.gates[j.val]'hjlt
  have hgmem : g ∈ C.gates := List.getElem_mem hjlt
  have ⟨hop, hlen⟩ := hgates g hgmem
  have hval : ∀ x : Fin n → Bool,
      wireVal C x (n + j.val) =
        g.op.eval (g.inputs.map fun i => if i < n + j.val then wireVal C x i else false) :=
    fun x => wireVal_gate C hsize x j
  have h_not_const : ¬ IsConst (n := n) C (n + j.val) := fun h => hjr (Or.inl h)
  have h_not_dup : ∀ w < n + j.val, ¬ (∀ u : Fin n → Bool, wireVal C u (n + j.val) = wireVal C u w) :=
    fun w hw heq => hjr (Or.inr ⟨w, hw, heq⟩)
  rcases hop with hand | hor | hnot
  · -- AND
    match h_in : g.inputs with
    | [] =>
      exfalso; apply h_not_const; intro y z
      simp [hval, hand, h_in, GateOp.eval]
    | [a] =>
      exfalso
      by_cases ha : a < n + j.val
      · apply h_not_dup a ha; intro x
        simp [hval, hand, h_in, ha, GateOp.eval]
      · apply h_not_const; intro y z
        simp [hval, hand, h_in, ha, GateOp.eval]
    | [a, b] =>
      have ha : a < n + j.val := by
        by_contra hna; apply h_not_const; intro y z
        simp [hval, hand, h_in, hna, GateOp.eval]
      have hb : b < n + j.val := by
        by_contra hnb; apply h_not_const; intro y z
        simp [hval, hand, h_in, hnb, GateOp.eval]
      have heval_ab : ∀ x : Fin n → Bool,
          wireVal C x (n + j.val) = (wireVal C x a && wireVal C x b) := by
        intro x; simp [hval, hand, h_in, ha, hb, GateOp.eval]
      have hnca : ¬ IsConst (n := n) C a := by
        intro hca
        let x0 : Fin n → Bool := fun _ => false
        cases h0 : wireVal C x0 a
        · apply h_not_const; intro y z
          have hy : wireVal C y a = false := by rw [hca y x0, h0]
          have hz : wireVal C z a = false := by rw [hca z x0, h0]
          simp [heval_ab, hy, hz]
        · apply h_not_dup b hb; intro x
          have hx : wireVal C x a = true := by rw [hca x x0, h0]
          simp [heval_ab, hx]
      have hncb : ¬ IsConst (n := n) C b := by
        intro hcb
        let x0 : Fin n → Bool := fun _ => false
        cases h0 : wireVal C x0 b
        · apply h_not_const; intro y z
          have hy : wireVal C y b = false := by rw [hcb y x0, h0]
          have hz : wireVal C z b = false := by rw [hcb z x0, h0]
          simp [heval_ab, hy, hz]
        · apply h_not_dup a ha; intro x
          have hx : wireVal C x b = true := by rw [hcb x x0, h0]
          simp [heval_ab, hx]
      set ca := canon (n := n) C a
      set cb := canon (n := n) C b
      have hca_lt : ca < n + j.val := lt_of_le_of_lt (canon_le C a) ha
      have hcb_lt : cb < n + j.val := lt_of_le_of_lt (canon_le C b) hb
      have heval_c : ∀ x : Fin n → Bool,
          wireVal C x (n + j.val) = (wireVal C x ca && wireVal C x cb) := by
        intro x; rw [heval_ab, canon_eq C a x, canon_eq C b x]
      have hne : ca ≠ cb := by
        intro heq; apply h_not_dup ca hca_lt; intro x
        rw [heval_c, heq, Bool.and_self]
      refine ⟨.gand ca cb, hca_lt, hcb_lt, hne, ?_, ?_, canon_idem C a, canon_idem C b, heval_c⟩
      · intro hc; apply hnca; intro y z; rw [← canon_eq C a y, ← canon_eq C a z]; exact hc y z
      · intro hc; apply hncb; intro y z; rw [← canon_eq C b y, ← canon_eq C b z]; exact hc y z
    | _ :: _ :: _ :: _ => simp [h_in] at hlen
  · -- OR
    match h_in : g.inputs with
    | [] =>
      exfalso; apply h_not_const; intro y z
      simp [hval, hor, h_in, GateOp.eval]
    | [a] =>
      exfalso
      by_cases ha : a < n + j.val
      · apply h_not_dup a ha; intro x
        simp [hval, hor, h_in, ha, GateOp.eval]
      · apply h_not_const; intro y z
        simp [hval, hor, h_in, ha, GateOp.eval]
    | [a, b] =>
      have ha : a < n + j.val := by
        by_contra hna
        by_cases hb : b < n + j.val
        · apply h_not_dup b hb; intro x
          simp [hval, hor, h_in, hna, hb, GateOp.eval]
        · apply h_not_const; intro y z
          simp [hval, hor, h_in, hna, hb, GateOp.eval]
      have hb : b < n + j.val := by
        by_contra hnb
        apply h_not_dup a ha; intro x
        simp [hval, hor, h_in, ha, hnb, GateOp.eval]
      have heval_ab : ∀ x : Fin n → Bool,
          wireVal C x (n + j.val) = (wireVal C x a || wireVal C x b) := by
        intro x; simp [hval, hor, h_in, ha, hb, GateOp.eval]
      have hnca : ¬ IsConst (n := n) C a := by
        intro hca
        let x0 : Fin n → Bool := fun _ => false
        cases h0 : wireVal C x0 a
        · apply h_not_dup b hb; intro x
          have hx : wireVal C x a = false := by rw [hca x x0, h0]
          simp [heval_ab, hx]
        · apply h_not_const; intro y z
          have hy : wireVal C y a = true := by rw [hca y x0, h0]
          have hz : wireVal C z a = true := by rw [hca z x0, h0]
          simp [heval_ab, hy, hz]
      have hncb : ¬ IsConst (n := n) C b := by
        intro hcb
        let x0 : Fin n → Bool := fun _ => false
        cases h0 : wireVal C x0 b
        · apply h_not_dup a ha; intro x
          have hx : wireVal C x b = false := by rw [hcb x x0, h0]
          simp [heval_ab, hx]
        · apply h_not_const; intro y z
          have hy : wireVal C y b = true := by rw [hcb y x0, h0]
          have hz : wireVal C z b = true := by rw [hcb z x0, h0]
          simp [heval_ab, hy, hz]
      set ca := canon (n := n) C a
      set cb := canon (n := n) C b
      have hca_lt : ca < n + j.val := lt_of_le_of_lt (canon_le C a) ha
      have hcb_lt : cb < n + j.val := lt_of_le_of_lt (canon_le C b) hb
      have heval_c : ∀ x : Fin n → Bool,
          wireVal C x (n + j.val) = (wireVal C x ca || wireVal C x cb) := by
        intro x; rw [heval_ab, canon_eq C a x, canon_eq C b x]
      have hne : ca ≠ cb := by
        intro heq; apply h_not_dup ca hca_lt; intro x
        rw [heval_c, heq, Bool.or_self]
      refine ⟨.gor ca cb, hca_lt, hcb_lt, hne, ?_, ?_, canon_idem C a, canon_idem C b, heval_c⟩
      · intro hc; apply hnca; intro y z; rw [← canon_eq C a y, ← canon_eq C a z]; exact hc y z
      · intro hc; apply hncb; intro y z; rw [← canon_eq C b y, ← canon_eq C b z]; exact hc y z
    | _ :: _ :: _ :: _ => simp [h_in] at hlen
  · -- NOT
    match h_in : g.inputs with
    | [] =>
      exfalso; apply h_not_const; intro y z
      simp [hval, hnot, h_in, GateOp.eval]
    | a :: _ =>
      have ha : a < n + j.val := by
        by_contra hna; apply h_not_const; intro y z
        simp [hval, hnot, h_in, hna, GateOp.eval]
      have heval_a : ∀ x : Fin n → Bool, wireVal C x (n + j.val) = !(wireVal C x a) := by
        intro x; simp [hval, hnot, h_in, ha, GateOp.eval]
      have hnca : ¬ IsConst (n := n) C a := by
        intro hca; apply h_not_const; intro y z
        simp [heval_a, hca y z]
      set ca := canon (n := n) C a
      have hca_lt : ca < n + j.val := lt_of_le_of_lt (canon_le C a) ha
      have heval_c : ∀ x : Fin n → Bool, wireVal C x (n + j.val) = !(wireVal C x ca) := by
        intro x; rw [heval_a, canon_eq C a x]
      refine ⟨.gnot ca, hca_lt, ?_, canon_idem C a, heval_c⟩
      intro hc; apply hnca; intro y z; rw [← canon_eq C a y, ← canon_eq C a z]; exact hc y z

lemma EffGate.inputs_lt {n G : ℕ} {C : Circuit} {j : Fin G} {eg : EffGate n G j}
    (hv : eg.Valid C) {w : ℕ} (hw : w ∈ eg.inputs) : w < n + j.val := by
  cases eg with
  | gnot u => simp [EffGate.inputs] at hw; subst hw; exact hv.1
  | gand u v => simp [EffGate.inputs] at hw; rcases hw with rfl | rfl; exact hv.1; exact hv.2.1
  | gor u v => simp [EffGate.inputs] at hw; rcases hw with rfl | rfl; exact hv.1; exact hv.2.1

lemma EffGate.inputs_not_const {n G : ℕ} {C : Circuit} {j : Fin G} {eg : EffGate n G j}
    (hv : eg.Valid C) {w : ℕ} (hw : w ∈ eg.inputs) : ¬ IsConst (n := n) C w := by
  cases eg with
  | gnot u => simp [EffGate.inputs] at hw; subst hw; exact hv.2.1
  | gand u v => simp [EffGate.inputs] at hw; rcases hw with rfl | rfl; exact hv.2.2.2.1; exact hv.2.2.2.2.1
  | gor u v => simp [EffGate.inputs] at hw; rcases hw with rfl | rfl; exact hv.2.2.2.1; exact hv.2.2.2.2.1

lemma EffGate.inputs_canon {n G : ℕ} {C : Circuit} {j : Fin G} {eg : EffGate n G j}
    (hv : eg.Valid C) {w : ℕ} (hw : w ∈ eg.inputs) : canon (n := n) C w = w := by
  cases eg with
  | gnot u => simp [EffGate.inputs] at hw; subst hw; exact hv.2.2.1
  | gand u v => simp [EffGate.inputs] at hw; rcases hw with rfl | rfl; exact hv.2.2.2.2.2.1; exact hv.2.2.2.2.2.2.1
  | gor u v => simp [EffGate.inputs] at hw; rcases hw with rfl | rfl; exact hv.2.2.2.2.2.1; exact hv.2.2.2.2.2.2.1

lemma EffGate.collapse_of_const {n G : ℕ} {C : Circuit} {j : Fin G} {eg : EffGate n G j}
    (hv : eg.Valid C) {p : Fin n} {b : Bool} {w : ℕ}
    (hw : w ∈ eg.inputs) (hc : ConstUnder C p b w) :
    Collapses C p b j := by
  rcases (constUnder_iff_exists C p b w).mp hc with ⟨c, hcval⟩
  cases eg with
  | gnot u =>
    simp [EffGate.inputs] at hw; subst hw
    left; intro y z hy hz
    rw [hv.2.2.2 y, hv.2.2.2 z, hcval y hy, hcval z hz]
  | gand u v =>
    rcases hv with ⟨hu, hv', _, _, _, _, _, hev⟩
    simp [EffGate.inputs] at hw
    rcases hw with rfl | rfl
    · cases c
      · left; intro y z hy hz; rw [hev y, hev z, hcval y hy, hcval z hz]; simp
      · right; refine ⟨v, hv', fun x hx => ?_⟩; rw [hev x, hcval x hx]; simp
    · cases c
      · left; intro y z hy hz; rw [hev y, hev z, hcval y hy, hcval z hz]; simp
      · right; refine ⟨u, hu, fun x hx => ?_⟩; rw [hev x, hcval x hx]; simp
  | gor u v =>
    rcases hv with ⟨hu, hv', _, _, _, _, _, hev⟩
    simp [EffGate.inputs] at hw
    rcases hw with rfl | rfl
    · cases c
      · right; refine ⟨v, hv', fun x hx => ?_⟩; rw [hev x, hcval x hx]; simp
      · left; intro y z hy hz; rw [hev y, hev z, hcval y hy, hcval z hz]; simp
    · cases c
      · right; refine ⟨u, hu, fun x hx => ?_⟩; rw [hev x, hcval x hx]; simp
      · left; intro y z hy hz; rw [hev y, hev z, hcval y hy, hcval z hz]; simp

lemma EffGate.const_of_all_const {n G : ℕ} {C : Circuit} {j : Fin G} {eg : EffGate n G j}
    (hv : eg.Valid C) {p : Fin n} {b : Bool}
    (hall : ∀ w ∈ eg.inputs, ConstUnder C p b w) :
    ConstUnder C p b (n + j.val) := by
  cases eg with
  | gnot u =>
    have hu := hall u (by simp [EffGate.inputs])
    intro y z hy hz; rw [hv.2.2.2 y, hv.2.2.2 z, hu y z hy hz]
  | gand u v =>
    have hu := hall u (by simp [EffGate.inputs])
    have hv' := hall v (by simp [EffGate.inputs])
    intro y z hy hz; rw [hv.2.2.2.2.2.2.2 y, hv.2.2.2.2.2.2.2 z, hu y z hy hz, hv' y z hy hz]
  | gor u v =>
    have hu := hall u (by simp [EffGate.inputs])
    have hv' := hall v (by simp [EffGate.inputs])
    intro y z hy hz; rw [hv.2.2.2.2.2.2.2 y, hv.2.2.2.2.2.2.2 z, hu y z hy hz, hv' y z hy hz]

lemma EffGate.eval_congr {n G : ℕ} {C : Circuit} {j : Fin G} {eg : EffGate n G j}
    (hv : eg.Valid C) {x y : Fin n → Bool}
    (h : ∀ w ∈ eg.inputs, wireVal C x w = wireVal C y w) :
    wireVal C x (n + j.val) = wireVal C y (n + j.val) := by
  cases eg with
  | gnot u =>
    rw [hv.2.2.2 x, hv.2.2.2 y, h u (by simp [EffGate.inputs])]
  | gand u v =>
    rw [hv.2.2.2.2.2.2.2 x, hv.2.2.2.2.2.2.2 y,
      h u (by simp [EffGate.inputs]), h v (by simp [EffGate.inputs])]
  | gor u v =>
    rw [hv.2.2.2.2.2.2.2 x, hv.2.2.2.2.2.2.2 y,
      h u (by simp [EffGate.inputs]), h v (by simp [EffGate.inputs])]

/-! ## 4. Main theorem for ANY cycle C_n (n >= 5) and ANY size G -/

theorem tight_sub_of_cycle {n G : ℕ} [NeZero n] (hn : 5 ≤ n) (C : Circuit)
    (hgates : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hsize : C.size = G)
    (heval : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔ cycleEdge n x) :
    ∃ (p : Fin n) (b : Bool) (S : Finset (Fin G)),
      (if b = true then 4 else 3) ≤ S.card ∧ ∀ j ∈ S, Collapses C p b j := by
  classical
  -- Step 1: Identify canonical output gate jOut
  have hOut_nc : ¬ IsConst (n := n) C C.output := by
    intro hc
    rcases cycleEdge_not_const hn with ⟨y, z, hdiff⟩
    have hyz : C.eval (List.ofFn y) = C.eval (List.ofFn z) := hc y z
    have h1 := heval y
    have h2 := heval z
    rw [hyz] at h1
    tauto
  have hOut_lt : C.output < n + G := by
    by_contra hge; push Not at hge
    apply hOut_nc; intro y z
    rw [wireVal_out_of_range C hsize y C.output hge,
        wireVal_out_of_range C hsize z C.output hge]
  set outW := canon (n := n) C C.output
  have houtW_lt : outW < n + G := lt_of_le_of_lt (canon_le C C.output) hOut_lt
  have houtW_eq : ∀ x : Fin n → Bool, wireVal C x outW = true ↔ cycleEdge n x := by
    intro x; rw [canon_eq C C.output x]; exact heval x
  have houtW_ge : n ≤ outW := by
    by_contra hlt; push Not at hlt
    let p : Fin n := ⟨outW, hlt⟩
    apply cycleEdge_not_eq_input hn p
    intro x
    rw [← houtW_eq x, wireVal_input C x p]
  let jOut : Fin G := ⟨outW - n, by omega⟩
  have hjOut_eq : n + jOut.val = outW := by simp [jOut]; omega
  have hjOut_nred : ¬ IsRed (n := n) C jOut :=
    canon_not_red C C.output jOut hOut_nc hjOut_eq.symm

  -- Step 2: Attach canonical EffGate to every non-redundant gate
  let eff : (j : Fin G) → ¬ IsRed (n := n) C j → EffGate n G j :=
    fun j hj => Classical.choose (exists_effGate C hsize hgates j hj)
  have heff_valid : ∀ (j : Fin G) (hj : ¬ IsRed (n := n) C j), (eff j hj).Valid C :=
    fun j hj => Classical.choose_spec (exists_effGate C hsize hgates j hj)

  -- Define effective inputs for any gate (empty if redundant)
  let effIn : Fin G → Finset ℕ := fun j =>
    if hj : ¬ IsRed (n := n) C j then (eff j hj).inputs else ∅

  -- Step 3: Live gates reachable backwards from jOut
  let ReachStep : Fin G → Fin G → Prop := fun j k => n + j.val ∈ effIn k
  let Reach : Fin G → Prop := fun j => Relation.ReflTransGen ReachStep j jOut
  let L : Finset (Fin G) := Finset.univ.filter (fun j => Reach j)

  have hjOut_L : jOut ∈ L := by
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Relation.ReflTransGen.refl

  have hL_nred : ∀ j ∈ L, ¬ IsRed (n := n) C j := by
    intro j hj
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hgen : ∀ a b, Relation.ReflTransGen ReachStep a b → ¬ IsRed (n := n) C b → ¬ IsRed (n := n) C a := by
      intro a b hab
      induction hab using Relation.ReflTransGen.head_induction_on with
      | refl => exact id
      | @head x y hxy _ ih =>
        intro hb
        have hynr : ¬ IsRed (n := n) C y := ih hb
        have hmem : n + x.val ∈ (eff y hynr).inputs := by
          simpa [ReachStep, effIn, hynr] using hxy
        have hnc := EffGate.inputs_not_const (heff_valid y hynr) hmem
        have hcan := EffGate.inputs_canon (heff_valid y hynr) hmem
        exact canon_not_red C (n + x.val) x hnc hcan
    exact hgen j jOut hj hjOut_nred

  have hL_effIn : ∀ j (hj : j ∈ L), effIn j = (eff j (hL_nred j hj)).inputs := by
    intro j hj; simp [effIn, hL_nred j hj]

  have hL_step_pred : ∀ k ∈ L, ∀ j : Fin G, n + j.val ∈ effIn k → j ∈ L := by
    intro k hk j hjk
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
    exact Relation.ReflTransGen.head hjk hk

  have hL_has_succ : ∀ j ∈ L, j ≠ jOut → ∃ k ∈ L, n + j.val ∈ effIn k ∧ j.val < k.val := by
    intro j hj hne
    simp only [L, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    rcases Relation.ReflTransGen.cases_head hj with rfl | ⟨b, hjb, hbo⟩
    · exact absurd rfl hne
    · have hbL : b ∈ L := by
        simp only [L, Finset.mem_filter, Finset.mem_univ, true_and]; exact hbo
      have hbnr := hL_nred b hbL
      have hmem : n + j.val ∈ (eff b hbnr).inputs := by
        simpa [ReachStep, effIn, hbnr] using hjb
      have hlt := EffGate.inputs_lt (heff_valid b hbnr) hmem
      exact ⟨b, hbL, hjb, by omega⟩

  -- No live gate that becomes constant under (p, b) can be jOut!
  have hconst_ne_out : ∀ (p : Fin n) (b : Bool) (j : Fin G),
      ConstUnder C p b (n + j.val) → j ≠ jOut := by
    intro p b j hc heq; subst heq
    rcases cycleEdge_not_const_restrict hn p b with ⟨y, z, hy, hz, hdiff⟩
    have h1 := hc y z hy hz
    rw [hjOut_eq] at h1
    have hy' := houtW_eq y
    have hz' := houtW_eq z
    rw [h1] at hy'
    tauto

  -- Any live gate j that becomes constant under (p, b) has a successor k ∈ L (j < k) that collapses!
  have hconst_has_succ_collapse : ∀ (p : Fin n) (b : Bool) (j : Fin G),
      j ∈ L → ConstUnder C p b (n + j.val) →
      ∃ k ∈ L, n + j.val ∈ effIn k ∧ j.val < k.val ∧ Collapses C p b k := by
    intro p b j hj hc
    rcases hL_has_succ j hj (hconst_ne_out p b j hc) with ⟨k, hkL, hjk, hlt⟩
    have hknr := hL_nred k hkL
    rw [hL_effIn k hkL] at hjk
    exact ⟨k, hkL, by rw [hL_effIn k hkL]; exact hjk, hlt,
      EffGate.collapse_of_const (heff_valid k hknr) hjk hc⟩

  -- Helper: input wire p is constant under (p, b)
  have hInput_constVal : ∀ (p : Fin n) (b : Bool), ConstValUnder C p b p.val b :=
    fun p b u hu => by rw [wireVal_input C u p]; exact hu
  have hInput_const : ∀ (p : Fin n) (b : Bool), ConstUnder C p b p.val :=
    fun p b => (constUnder_iff_exists C p b p.val).mpr ⟨b, hInput_constVal p b⟩

  -- Live out-neighborhood of a wire w
  let outL : ℕ → Finset (Fin G) := fun w => L.filter (fun k => w ∈ effIn k)

  -- Case A: some input p has |outL p| >= 3 -> set b = false, all gates in outL p collapse!
  by_cases hCaseA : ∃ p : Fin n, 3 ≤ (outL p.val).card
  · rcases hCaseA with ⟨p, hcard⟩
    refine ⟨p, false, outL p.val, by simpa using hcard, ?_⟩
    intro j hj
    simp only [outL, Finset.mem_filter] at hj
    rcases hj with ⟨hjL, hpj⟩
    have hjnr := hL_nred j hjL
    rw [hL_effIn j hjL] at hpj
    exact EffGate.collapse_of_const (heff_valid j hjnr) hpj (hInput_const p false)

  push Not at hCaseA

  -- Case B & C: some input p has |outL p| = 2!
  by_cases hCaseBC : ∃ p : Fin n, (outL p.val).card = 2
  · rcases hCaseBC with ⟨p, hcard2⟩
    rcases Finset.card_eq_two.mp hcard2 with ⟨j1, j2, hne12, hEq12⟩
    -- WLOG j1.val < j2.val
    wlog hlt12 : j1.val < j2.val generalizing j1 j2
    · exact this j2 j1 (Ne.symm hne12) (by rw [hEq12, Finset.pair_comm]) (by omega)
    have hj1_mem : j1 ∈ outL p.val := by rw [hEq12]; simp
    have hj2_mem : j2 ∈ outL p.val := by rw [hEq12]; simp
    simp only [outL, Finset.mem_filter] at hj1_mem hj2_mem
    rcases hj1_mem with ⟨hj1L, hp1⟩
    rcases hj2_mem with ⟨hj2L, hp2⟩
    have hj1nr := hL_nred j1 hj1L
    have hj2nr := hL_nred j2 hj2L
    have hp1' : p.val ∈ (eff j1 hj1nr).inputs := by rwa [← hL_effIn j1 hj1L]
    have hp2' : p.val ∈ (eff j2 hj2nr).inputs := by rwa [← hL_effIn j2 hj2L]

    -- Helper for Case B: if either j1 or j2 becomes constant under (p, false), we get 3 gates!
    have hCaseB_of_const : ∀ (ja jb : Fin G) (hjaL : ja ∈ L) (hjbL : jb ∈ L),
        ja ≠ jb → p.val ∈ effIn jb → ConstUnder C p false (n + ja.val) →
        ∃ S : Finset (Fin G), 3 ≤ S.card ∧ ∀ j ∈ S, Collapses C p false j := by
      intro ja jb hjaL hjbL hne_ab hpb hc_ja
      have hcol_ja : Collapses C p false ja := Or.inl hc_ja
      have hcol_jb : Collapses C p false jb := by
        have hpb' : p.val ∈ (eff jb (hL_nred jb hjbL)).inputs := by rwa [← hL_effIn jb hjbL]
        exact EffGate.collapse_of_const (heff_valid jb (hL_nred jb hjbL)) hpb' (hInput_const p false)
      rcases hconst_has_succ_collapse p false ja hjaL hc_ja with ⟨k, hkL, hjak, hlt_ak, hcol_k⟩
      by_cases hkb : k = jb
      · -- jb reads BOTH p and n+ja -> ALL inputs of jb are constant under (p, false)!
        subst k
        have hjb_const : ConstUnder C p false (n + jb.val) := by
          apply EffGate.const_of_all_const (heff_valid jb (hL_nred jb hjbL))
          intro w hw
          have hpb' : p.val ∈ (eff jb (hL_nred jb hjbL)).inputs := by rwa [← hL_effIn jb hjbL]
          have hjak' : n + ja.val ∈ (eff jb (hL_nred jb hjbL)).inputs := by rwa [← hL_effIn jb hjbL]
          cases heg : eff jb (hL_nred jb hjbL) with
          | gnot u =>
            rw [heg] at hw hpb'
            simp [EffGate.inputs] at hw hpb'; subst hw; subst hpb'; exact hInput_const p false
          | gand u v =>
            rw [heg] at hw hpb' hjak'
            simp [EffGate.inputs] at hw hpb' hjak'
            have hne_pja : p.val ≠ n + ja.val := by omega
            rcases hpb' with rfl | rfl <;> rcases hjak' with h' | h'
            · exact absurd h'.symm hne_pja
            · subst h'; rcases hw with rfl | rfl; exact hInput_const p false; exact hc_ja
            · subst h'; rcases hw with rfl | rfl; exact hc_ja; exact hInput_const p false
            · exact absurd h'.symm hne_pja
          | gor u v =>
            rw [heg] at hw hpb' hjak'
            simp [EffGate.inputs] at hw hpb' hjak'
            have hne_pja : p.val ≠ n + ja.val := by omega
            rcases hpb' with rfl | rfl <;> rcases hjak' with h' | h'
            · exact absurd h'.symm hne_pja
            · subst h'; rcases hw with rfl | rfl; exact hInput_const p false; exact hc_ja
            · subst h'; rcases hw with rfl | rfl; exact hc_ja; exact hInput_const p false
            · exact absurd h'.symm hne_pja
        rcases hconst_has_succ_collapse p false jb hjbL hjb_const with ⟨m, _, _, hlt_bm, hcol_m⟩
        refine ⟨{ja, jb, m}, ?_, ?_⟩
        · have h1 : ja ≠ m := fun h => by subst h; omega
          have h2 : jb ≠ m := fun h => by subst h; omega
          rw [Finset.card_insert_of_notMem, Finset.card_pair h2]
          simp [hne_ab, h1]
        · intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
          rcases hj with rfl | rfl | rfl <;> assumption
      · refine ⟨{ja, jb, k}, ?_, ?_⟩
        · have h1 : ja ≠ k := fun h => by subst h; omega
          rw [Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hkb)]
          simp [hne_ab, h1]
        · intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
          rcases hj with rfl | rfl | rfl <;> assumption

    -- Check if j1 is NOT/AND or j2 is NOT/AND!
    by_cases hc1 : ConstUnder C p false (n + j1.val)
    · rcases hCaseB_of_const j1 j2 hj1L hj2L hne12 hp2 hc1 with ⟨S, hScard, hS⟩
      exact ⟨p, false, S, by simpa using hScard, hS⟩
    · by_cases hc2 : ConstUnder C p false (n + j2.val)
      · rcases hCaseB_of_const j2 j1 hj2L hj1L (Ne.symm hne12) hp1 hc2 with ⟨S, hScard, hS⟩
        exact ⟨p, false, S, by simpa using hScard, hS⟩
      · -- Neither j1 nor j2 is constant under (p, false) -> BOTH MUST BE OR GATES!
        have h1_or : ∃ u1 v1, eff j1 hj1nr = .gor u1 v1 := by
          have hv1 := heff_valid j1 hj1nr
          cases heg1 : eff j1 hj1nr with
          | gnot u =>
            exfalso; apply hc1
            rw [heg1] at hv1 hp1'; simp [EffGate.inputs] at hp1'; subst hp1'
            intro y z hy hz; rw [hv1.2.2.2 y, hv1.2.2.2 z, wireVal_input C y p, wireVal_input C z p, hy, hz]
          | gand u v =>
            exfalso; apply hc1
            rw [heg1] at hv1 hp1'; simp [EffGate.inputs] at hp1'
            intro y z hy hz
            rcases hp1' with rfl | rfl
            · rw [hv1.2.2.2.2.2.2.2 y, hv1.2.2.2.2.2.2.2 z, wireVal_input C y p, wireVal_input C z p, hy, hz]; simp
            · rw [hv1.2.2.2.2.2.2.2 y, hv1.2.2.2.2.2.2.2 z, wireVal_input C y p, wireVal_input C z p, hy, hz]; simp
          | gor u v => exact ⟨u, v, rfl⟩
        have h2_or : ∃ u2 v2, eff j2 hj2nr = .gor u2 v2 := by
          have hv2 := heff_valid j2 hj2nr
          cases heg2 : eff j2 hj2nr with
          | gnot u =>
            exfalso; apply hc2
            rw [heg2] at hv2 hp2'; simp [EffGate.inputs] at hp2'; subst hp2'
            intro y z hy hz; rw [hv2.2.2.2 y, hv2.2.2.2 z, wireVal_input C y p, wireVal_input C z p, hy, hz]
          | gand u v =>
            exfalso; apply hc2
            rw [heg2] at hv2 hp2'; simp [EffGate.inputs] at hp2'
            intro y z hy hz
            rcases hp2' with rfl | rfl
            · rw [hv2.2.2.2.2.2.2.2 y, hv2.2.2.2.2.2.2.2 z, wireVal_input C y p, wireVal_input C z p, hy, hz]; simp
            · rw [hv2.2.2.2.2.2.2.2 y, hv2.2.2.2.2.2.2.2 z, wireVal_input C y p, wireVal_input C z p, hy, hz]; simp
          | gor u v => exact ⟨u, v, rfl⟩
        rcases h1_or with ⟨u1, v1, heg1⟩
        rcases h2_or with ⟨u2, v2, heg2⟩
        -- Under (p, true), BOTH j1 and j2 become CONSTANT true!
        have hc1_t : ConstUnder C p true (n + j1.val) := by
          have hv1 := heff_valid j1 hj1nr
          rw [heg1] at hv1 hp1'; simp [EffGate.inputs] at hp1'
          intro y z hy hz
          rcases hp1' with rfl | rfl
          · rw [hv1.2.2.2.2.2.2.2 y, hv1.2.2.2.2.2.2.2 z, wireVal_input C y p, wireVal_input C z p, hy, hz]; simp
          · rw [hv1.2.2.2.2.2.2.2 y, hv1.2.2.2.2.2.2.2 z, wireVal_input C y p, wireVal_input C z p, hy, hz]; simp
        have hc2_t : ConstUnder C p true (n + j2.val) := by
          have hv2 := heff_valid j2 hj2nr
          rw [heg2] at hv2 hp2'; simp [EffGate.inputs] at hp2'
          intro y z hy hz
          rcases hp2' with rfl | rfl
          · rw [hv2.2.2.2.2.2.2.2 y, hv2.2.2.2.2.2.2.2 z, wireVal_input C y p, wireVal_input C z p, hy, hz]; simp
          · rw [hv2.2.2.2.2.2.2.2 y, hv2.2.2.2.2.2.2.2 z, wireVal_input C y p, wireVal_input C z p, hy, hz]; simp
        -- Moreover, n + j1.val CANNOT be in effIn j2 (else j2 = OR(p, j1) = j1, contradicting ¬IsRed j2!)
        have hj1_not_in_j2 : n + j1.val ∉ effIn j2 := by
          intro hmem
          rw [hL_effIn j2 hj2L, heg2] at hmem
          have hv1 := heff_valid j1 hj1nr
          have hv2 := heff_valid j2 hj2nr
          rw [heg1] at hv1 hp1'
          rw [heg2] at hv2 hp2'
          simp [EffGate.inputs] at hmem hp1' hp2'
          have hne_pj1 : p.val ≠ n + j1.val := by omega
          apply hj2nr; right; refine ⟨n + j1.val, by omega, fun x => ?_⟩
          have hev1 := hv1.2.2.2.2.2.2.2 x
          have hev2 := hv2.2.2.2.2.2.2.2 x
          rcases hp2' with rfl | rfl <;> rcases hmem with h' | h'
          · exact absurd h'.symm hne_pj1
          · subst h'; rw [hev2, hev1]
            rcases hp1' with rfl | rfl <;> cases wireVal C x p.val <;> simp
          · subst h'; rw [hev2, hev1]
            rcases hp1' with rfl | rfl <;> cases wireVal C x p.val <;> simp
          · exact absurd h'.symm hne_pj1
        -- Get successors k1 of j1 and k2 of j2
        rcases hconst_has_succ_collapse p true j1 hj1L hc1_t with ⟨k1, hk1L, hj1k1, hlt_1k1, hcol_k1⟩
        rcases hconst_has_succ_collapse p true j2 hj2L hc2_t with ⟨k2, hk2L, hj2k2, hlt_2k2, hcol_k2⟩
        have hk1_ne_j2 : k1 ≠ j2 := fun h => by subst h; exact hj1_not_in_j2 hj1k1
        have hk1_ne_j1 : k1 ≠ j1 := fun h => by subst h; omega
        have hk2_ne_j2 : k2 ≠ j2 := fun h => by subst h; omega
        have hk2_ne_j1 : k2 ≠ j1 := fun h => by subst h; omega
        by_cases hk12 : k1 = k2
        · -- k1 reads BOTH n+j1 and n+j2 -> k1 becomes constant under (p, true) -> successor m!
          subst k2
          have hk1_const : ConstUnder C p true (n + k1.val) := by
            apply EffGate.const_of_all_const (heff_valid k1 (hL_nred k1 hk1L))
            intro w hw
            have h1' : n + j1.val ∈ (eff k1 (hL_nred k1 hk1L)).inputs := by rwa [← hL_effIn k1 hk1L]
            have h2' : n + j2.val ∈ (eff k1 (hL_nred k1 hk1L)).inputs := by rwa [← hL_effIn k1 hk1L]
            have hne_w : n + j1.val ≠ n + j2.val := by omega
            cases hegk : eff k1 (hL_nred k1 hk1L) with
            | gnot u =>
              rw [hegk] at hw h1'; simp [EffGate.inputs] at hw h1'; subst hw; subst h1'; exact hc1_t
            | gand u v =>
              rw [hegk] at hw h1' h2'; simp [EffGate.inputs] at hw h1' h2'
              rcases h1' with rfl | rfl <;> rcases h2' with h' | h'
              · exact absurd h'.symm hne_w
              · subst h'; rcases hw with rfl | rfl; exact hc1_t; exact hc2_t
              · subst h'; rcases hw with rfl | rfl; exact hc2_t; exact hc1_t
              · exact absurd h'.symm hne_w
            | gor u v =>
              rw [hegk] at hw h1' h2'; simp [EffGate.inputs] at hw h1' h2'
              rcases h1' with rfl | rfl <;> rcases h2' with h' | h'
              · exact absurd h'.symm hne_w
              · subst h'; rcases hw with rfl | rfl; exact hc1_t; exact hc2_t
              · subst h'; rcases hw with rfl | rfl; exact hc2_t; exact hc1_t
              · exact absurd h'.symm hne_w
          rcases hconst_has_succ_collapse p true k1 hk1L hk1_const with ⟨m, _, _, hlt_k1m, hcol_m⟩
          have hm1 : m ≠ j1 := fun h => by subst h; omega
          have hm2 : m ≠ j2 := fun h => by subst h; omega
          have hmk : m ≠ k1 := fun h => by subst h; omega
          refine ⟨p, true, {j1, j2, k1, m}, ?_, ?_⟩
          · simp only [↓reduceIte]
            rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair (Ne.symm hmk)]
            · simp [Ne.symm hk1_ne_j2, Ne.symm hm2]
            · simp [hne12, Ne.symm hk1_ne_j1, Ne.symm hm1]
          · intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
            rcases hj with rfl | rfl | rfl | rfl
            · exact Or.inl hc1_t
            · exact Or.inl hc2_t
            · exact hcol_k1
            · exact hcol_m
        · -- k1 ≠ k2 -> {j1, j2, k1, k2} are 4 distinct gates!
          refine ⟨p, true, {j1, j2, k1, k2}, ?_, ?_⟩
          · simp only [↓reduceIte]
            rw [Finset.card_insert_of_notMem, Finset.card_insert_of_notMem, Finset.card_pair hk12]
            · simp [Ne.symm hk1_ne_j2, Ne.symm hk2_ne_j2]
            · simp [hne12, Ne.symm hk1_ne_j1, Ne.symm hk2_ne_j1]
          · intro j hj; simp only [Finset.mem_insert, Finset.mem_singleton] at hj
            rcases hj with rfl | rfl | rfl | rfl
            · exact Or.inl hc1_t
            · exact Or.inl hc2_t
            · exact hcol_k1
            · exact hcol_k2

  push Not at hCaseBC

  -- Now EVERY input p has |outL p| <= 1!
  have hout_le1 : ∀ p : Fin n, (outL p.val).card ≤ 1 := by
    intro p
    have hlt3 := hCaseA p
    have hne2 := hCaseBC p
    omega

  -- Subcase D1a: some NOT gate j ∈ L reading an input p has |outL (n + j)| >= 2!
  by_cases hCaseD1a : ∃ (p : Fin n) (j : Fin G) (hjL : j ∈ L),
      eff j (hL_nred j hjL) = .gnot p.val ∧ 2 ≤ (outL (n + j.val)).card
  · rcases hCaseD1a with ⟨p, j, hjL, heg, hcard2⟩
    rcases Finset.one_lt_card.mp (by omega : 1 < (outL (n + j.val)).card) with ⟨k1, hk1, k2, hk2, hne12⟩
    simp only [outL, Finset.mem_filter] at hk1 hk2
    have hcj : ConstUnder C p false (n + j.val) := by
      have hvj := heff_valid j (hL_nred j hjL)
      rw [heg] at hvj
      intro y z hy hz; rw [hvj.2.2.2 y, hvj.2.2.2 z, wireVal_input C y p, wireVal_input C z p, hy, hz]
    have hcol1 : Collapses C p false k1 := by
      have h1' : n + j.val ∈ (eff k1 (hL_nred k1 hk1.1)).inputs := by
        rw [← hL_effIn k1 hk1.1]; exact hk1.2
      exact EffGate.collapse_of_const (heff_valid k1 (hL_nred k1 hk1.1)) h1' hcj
    have hcol2 : Collapses C p false k2 := by
      have h2' : n + j.val ∈ (eff k2 (hL_nred k2 hk2.1)).inputs := by
        rw [← hL_effIn k2 hk2.1]; exact hk2.2
      exact EffGate.collapse_of_const (heff_valid k2 (hL_nred k2 hk2.1)) h2' hcj
    have hlt1 : j.val < k1.val := by
      have h1' : n + j.val ∈ (eff k1 (hL_nred k1 hk1.1)).inputs := by
        rw [← hL_effIn k1 hk1.1]; exact hk1.2
      have := EffGate.inputs_lt (heff_valid k1 (hL_nred k1 hk1.1)) h1'; omega
    have hlt2 : j.val < k2.val := by
      have h2' : n + j.val ∈ (eff k2 (hL_nred k2 hk2.1)).inputs := by
        rw [← hL_effIn k2 hk2.1]; exact hk2.2
      have := EffGate.inputs_lt (heff_valid k2 (hL_nred k2 hk2.1)) h2'; omega
    have hj_ne1 : j ≠ k1 := fun h => by subst h; omega
    have hj_ne2 : j ≠ k2 := fun h => by subst h; omega
    refine ⟨p, false, {j, k1, k2}, ?_, ?_⟩
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [Finset.card_insert_of_notMem, Finset.card_pair hne12]
      simp [hj_ne1, hj_ne2]
    · intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl
      · exact Or.inl hcj
      · exact hcol1
      · exact hcol2

  push Not at hCaseD1a

  -- Case D (final): derive contradiction via the first binary gate in L!
  exfalso
  let IsBin : Fin G → Prop := fun j =>
    ∃ (hjL : j ∈ L), match eff j (hL_nred j hjL) with | .gnot _ => False | _ => True

  -- First show a binary gate exists in L!
  have hexBin : ∃ j : Fin G, IsBin j := by
    by_contra hnoBin
    push Not at hnoBin
    -- If all gates in L are NOT gates, then every j ∈ L computes some input or !input!
    have h_all_unary : ∀ k : ℕ, ∀ (j : Fin G) (hjL : j ∈ L), j.val = k →
        ∃ (p : Fin n) (neg : Bool), ∀ x : Fin n → Bool,
          wireVal C x (n + j.val) = xor (x p) neg := by
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro j hjL hjk
        have hnb := hnoBin j
        simp only [IsBin, not_exists] at hnb
        have hnotj := hnb hjL
        cases heg : eff j (hL_nred j hjL) with
        | gand u v => rw [heg] at hnotj; exact False.elim (hnotj trivial)
        | gor u v => rw [heg] at hnotj; exact False.elim (hnotj trivial)
        | gnot u =>
          have hvj := heff_valid j (hL_nred j hjL)
          rw [heg] at hvj
          by_cases hu : u < n
          · refine ⟨⟨u, hu⟩, true, fun x => ?_⟩
            rw [hvj.2.2.2 x, wireVal_input C x ⟨u, hu⟩]; cases x ⟨u, hu⟩ <;> rfl
          · push Not at hu
            let j' : Fin G := ⟨u - n, by have := hvj.1; omega⟩
            have hj'eq : n + j'.val = u := by simp [j']; omega
            have hj'L : j' ∈ L := hL_step_pred j hjL j' (by
              rw [hL_effIn j hjL, heg]; simp [EffGate.inputs, hj'eq])
            have hj'lt : j'.val < k := by have := hvj.1; omega
            rcases ih j'.val hj'lt j' hj'L rfl with ⟨p, neg, hpx⟩
            refine ⟨p, !neg, fun x => ?_⟩
            rw [hvj.2.2.2 x, ← hj'eq, hpx x]
            cases x p <;> cases neg <;> rfl
    rcases h_all_unary jOut.val jOut hjOut_L rfl with ⟨p, neg, hpx⟩
    cases neg
    · apply cycleEdge_not_eq_input hn p
      intro x; rw [← houtW_eq x, ← hjOut_eq, hpx x]; simp
    · apply cycleEdge_not_eq_not_input p
      intro x; rw [← houtW_eq x, ← hjOut_eq, hpx x]; cases x p <;> simp

  -- Take the MINIMUM binary gate gStar in L
  let binSet : Finset (Fin G) := Finset.univ.filter IsBin
  have hbinNE : binSet.Nonempty := by
    rcases hexBin with ⟨j, hj⟩
    exact ⟨j, by simp [binSet, hj]⟩
  let gStar : Fin G := binSet.min' hbinNE
  have hgStar_bin : IsBin gStar := by
    have := Finset.min'_mem binSet hbinNE
    simp [binSet] at this; exact this
  have hgStar_min : ∀ j : Fin G, IsBin j → gStar.val ≤ j.val := by
    intro j hj
    have hmem : j ∈ binSet := by simp [binSet, hj]
    exact Finset.min'_le binSet j hmem
  rcases hgStar_bin with ⟨hgStarL, hgStar_not_not⟩

  -- Helper: any input wire w of gStar is either an input p < n, or a NOT gate of an input p < n
  have classify_input : ∀ w ∈ (eff gStar (hL_nred gStar hgStarL)).inputs,
      ∃ (p : Fin n) (neg : Bool),
        (∀ x : Fin n → Bool, wireVal C x w = xor (x p) neg) ∧
        (w = p.val ∨ ∃ j : Fin G, ∃ hjL : j ∈ L, w = n + j.val ∧ eff j (hL_nred j hjL) = .gnot p.val) := by
    intro w hw
    have hwlt := EffGate.inputs_lt (heff_valid gStar (hL_nred gStar hgStarL)) hw
    by_cases hwn : w < n
    · refine ⟨⟨w, hwn⟩, false, fun x => ?_, Or.inl rfl⟩
      rw [wireVal_input C x ⟨w, hwn⟩]; simp
    · push Not at hwn
      let j : Fin G := ⟨w - n, by omega⟩
      have hjeq : n + j.val = w := by simp [j]; omega
      have hjL : j ∈ L := hL_step_pred gStar hgStarL j (by
        rw [hL_effIn gStar hgStarL, hjeq]; exact hw)
      have hjlt : j.val < gStar.val := by omega
      have hjnotbin : ¬ IsBin j := fun h => by have := hgStar_min j h; omega
      cases heg : eff j (hL_nred j hjL) with
      | gand a b => exact absurd ⟨hjL, by rw [heg]; trivial⟩ hjnotbin
      | gor a b => exact absurd ⟨hjL, by rw [heg]; trivial⟩ hjnotbin
      | gnot a =>
        have hvj := heff_valid j (hL_nred j hjL)
        rw [heg] at hvj
        have han : a < n := by
          by_contra hage; push Not at hage
          let j' : Fin G := ⟨a - n, by have := hvj.1; omega⟩
          have hj'eq : n + j'.val = a := by simp [j']; omega
          have hj'L : j' ∈ L := hL_step_pred j hjL j' (by
            rw [hL_effIn j hjL, heg]; simp [EffGate.inputs, hj'eq])
          have hj'notbin : ¬ IsBin j' := fun h => by
            have := hgStar_min j' h; have := hvj.1; omega
          cases heg' : eff j' (hL_nred j' hj'L) with
          | gand x y => exact absurd ⟨hj'L, by rw [heg']; trivial⟩ hj'notbin
          | gor x y => exact absurd ⟨hj'L, by rw [heg']; trivial⟩ hj'notbin
          | gnot b =>
            have hvj' := heff_valid j' (hL_nred j' hj'L)
            rw [heg'] at hvj'
            -- Then j = NOT(NOT(b)) = b, contradicting ¬IsRed j!
            apply hL_nred j hjL
            right; refine ⟨b, by have := hvj.1; have := hvj'.1; omega, fun x => ?_⟩
            rw [hvj.2.2.2 x, ← hj'eq, hvj'.2.2.2 x, Bool.not_not]
        refine ⟨⟨a, han⟩, true, fun x => ?_, Or.inr ⟨j, hjL, hjeq.symm, heg⟩⟩
        rw [← hjeq, hvj.2.2.2 x, wireVal_input C x ⟨a, han⟩]
        cases x ⟨a, han⟩ <;> rfl

  -- Extract the two inputs w1, w2 of gStar and the binary op (and / or)
  have hbin_inputs : ∃ (w1 w2 : ℕ) (op : Bool → Bool → Bool),
      w1 ≠ w2 ∧ (∀ a b, op a b = op b a) ∧
      (eff gStar (hL_nred gStar hgStarL)).inputs = {w1, w2} ∧
      ∀ x : Fin n → Bool, wireVal C x (n + gStar.val) = op (wireVal C x w1) (wireVal C x w2) := by
    have hv := heff_valid gStar (hL_nred gStar hgStarL)
    cases heg : eff gStar (hL_nred gStar hgStarL) with
    | gnot u => rw [heg] at hgStar_not_not; exact False.elim hgStar_not_not
    | gand u v =>
      rw [heg] at hv
      exact ⟨u, v, and, hv.2.2.1, Bool.and_comm, rfl, hv.2.2.2.2.2.2.2⟩
    | gor u v =>
      rw [heg] at hv
      exact ⟨u, v, or, hv.2.2.1, Bool.or_comm, rfl, hv.2.2.2.2.2.2.2⟩

  rcases hbin_inputs with ⟨w1, w2, op, hw12, hop_comm, hgin, hgeval⟩
  have hw1_mem : w1 ∈ (eff gStar (hL_nred gStar hgStarL)).inputs := by rw [hgin]; simp
  have hw2_mem : w2 ∈ (eff gStar (hL_nred gStar hgStarL)).inputs := by rw [hgin]; simp
  rcases classify_input w1 hw1_mem with ⟨u, neg1, hw1_eval, hw1_shape⟩
  rcases classify_input w2 hw2_mem with ⟨v, neg2, hw2_eval, hw2_shape⟩

  -- Show u ≠ v!
  have huv : u ≠ v := by
    intro heq; subst heq
    cases neg1 <;> cases neg2
    · have hv := heff_valid gStar (hL_nred gStar hgStarL)
      have hc1 := EffGate.inputs_canon hv hw1_mem
      have hc2 := EffGate.inputs_canon hv hw2_mem
      have hsame : ∀ x : Fin n → Bool, wireVal C x w1 = wireVal C x w2 := by
        intro x; rw [hw1_eval x, hw2_eval x]
      have hle1 : w1 ≤ w2 := by
        rw [← hc1]; exact canon_le_of_eq C w1 w2 (fun x => (hsame x).symm)
      have hle2 : w2 ≤ w1 := by
        rw [← hc2]; exact canon_le_of_eq C w2 w1 hsame
      exact hw12 (le_antisymm hle1 hle2)
    · apply hL_nred gStar hgStarL; left; intro y z
      rw [hgeval y, hgeval z, hw1_eval y, hw2_eval y, hw1_eval z, hw2_eval z]
      cases y u <;> cases z u <;> simp [hop_comm]
    · apply hL_nred gStar hgStarL; left; intro y z
      rw [hgeval y, hgeval z, hw1_eval y, hw2_eval y, hw1_eval z, hw2_eval z]
      cases y u <;> cases z u <;> simp [hop_comm]
    · have hv := heff_valid gStar (hL_nred gStar hgStarL)
      have hc1 := EffGate.inputs_canon hv hw1_mem
      have hc2 := EffGate.inputs_canon hv hw2_mem
      have hsame : ∀ x : Fin n → Bool, wireVal C x w1 = wireVal C x w2 := by
        intro x; rw [hw1_eval x, hw2_eval x]
      have hle1 : w1 ≤ w2 := by
        rw [← hc1]; exact canon_le_of_eq C w1 w2 (fun x => (hsame x).symm)
      have hle2 : w2 ≤ w1 := by
        rw [← hc2]; exact canon_le_of_eq C w2 w1 hsame
      exact hw12 (le_antisymm hle1 hle2)

  -- Helper: show neither w1 nor w2 (nor u, v) is used by any gate in L other than gStar (and its NOT gate)!
  have hno_leak : ∀ (p : Fin n) (w : ℕ),
      w ∈ effIn gStar →
      (w = p.val ∨ ∃ j : Fin G, ∃ hjL : j ∈ L, w = n + j.val ∧ eff j (hL_nred j hjL) = .gnot p.val) →
      ∀ k ∈ L, k ≠ gStar → (n + k.val ≠ w) → p.val ∉ effIn k ∧ w ∉ effIn k := by
    intro p w hw_in hshape k hkL hkg hkw
    rcases hshape with rfl | ⟨j, hjL, rfl, hegj⟩
    · -- w = p.val: gStar ∈ outL p.val, and |outL p.val| ≤ 1 -> k ∉ outL p.val!
      have hnot : p.val ∉ effIn k := by
        intro hk_in
        have hg_mem : gStar ∈ outL p.val := by simp [outL, hgStarL, hw_in]
        have hk_mem : k ∈ outL p.val := by simp [outL, hkL, hk_in]
        have h2 : 2 ≤ (outL p.val).card := by
          have hsub : ({gStar, k} : Finset (Fin G)) ⊆ outL p.val := by
            intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
          calc 2 = ({gStar, k} : Finset (Fin G)).card := (Finset.card_pair (Ne.symm hkg)).symm
            _ ≤ (outL p.val).card := Finset.card_le_card hsub
        have := hout_le1 p; omega
      exact ⟨hnot, hnot⟩
    · -- w = n + j.val where j = NOT(p):
      -- j ∈ outL p.val and |outL p.val| ≤ 1 -> k ≠ j implies p.val ∉ effIn k!
      have hkj : k ≠ j := fun h => hkw (by rw [h])
      have hnot_p : p.val ∉ effIn k := by
        intro hk_in
        have hj_mem : j ∈ outL p.val := by
          simp [outL, hjL, hL_effIn j hjL, hegj, EffGate.inputs]
        have hk_mem : k ∈ outL p.val := by simp [outL, hkL, hk_in]
        have h2 : 2 ≤ (outL p.val).card := by
          have hsub : ({j, k} : Finset (Fin G)) ⊆ outL p.val := by
            intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
          calc 2 = ({j, k} : Finset (Fin G)).card := (Finset.card_pair (Ne.symm hkj)).symm
            _ ≤ (outL p.val).card := Finset.card_le_card hsub
        have := hout_le1 p; omega
      -- gStar ∈ outL (n + j.val) and |outL (n + j.val)| < 2 (from ¬CaseD1a) -> k ∉ outL (n + j.val)!
      have hnot_w : n + j.val ∉ effIn k := by
        intro hk_in
        have hg_mem : gStar ∈ outL (n + j.val) := by simp [outL, hgStarL, hw_in]
        have hk_mem : k ∈ outL (n + j.val) := by simp [outL, hkL, hk_in]
        have h2 : 2 ≤ (outL (n + j.val)).card := by
          have hsub : ({gStar, k} : Finset (Fin G)) ⊆ outL (n + j.val) := by
            intro x hx; simp at hx; rcases hx with rfl | rfl <;> assumption
          calc 2 = ({gStar, k} : Finset (Fin G)).card := (Finset.card_pair (Ne.symm hkg)).symm
            _ ≤ (outL (n + j.val)).card := Finset.card_le_card hsub
        have hlt2 := hCaseD1a p j hjL hegj
        omega
      exact ⟨hnot_p, hnot_w⟩

  -- Strong induction: every live gate k with n+k ≠ w1, n+k ≠ w2 depends on (x u, x v) ONLY via gStar!
  let hfn : Bool → Bool → Bool := fun a b => op (xor a neg1) (xor b neg2)
  have hgStar_eq_hfn : ∀ x : Fin n → Bool, wireVal C x (n + gStar.val) = hfn (x u) (x v) := by
    intro x; rw [hgeval x, hw1_eval x, hw2_eval x]

  have h_bottleneck : ∀ m : ℕ, ∀ k : Fin G, k.val = m → k ∈ L →
      n + k.val ≠ w1 → n + k.val ≠ w2 →
      ∀ x y : Fin n → Bool,
        (∀ i : Fin n, i ≠ u → i ≠ v → x i = y i) →
        hfn (x u) (x v) = hfn (y u) (y v) →
        wireVal C x (n + k.val) = wireVal C y (n + k.val) := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro k hkm hkL hkw1 hkw2 x y hrest hhfn
      by_cases hkg : k = gStar
      · subst hkg; rw [hgStar_eq_hfn x, hgStar_eq_hfn y, hhfn]
      · have hknr := hL_nred k hkL
        apply EffGate.eval_congr (heff_valid k hknr)
        intro w hw
        have hw_in_k : w ∈ effIn k := by rw [hL_effIn k hkL]; exact hw
        have ⟨hu_not, hw1_not⟩ := hno_leak u w1 (by rw [hL_effIn gStar hgStarL]; exact hw1_mem)
          hw1_shape k hkL hkg hkw1
        have ⟨hv_not, hw2_not⟩ := hno_leak v w2 (by rw [hL_effIn gStar hgStarL]; exact hw2_mem)
          hw2_shape k hkL hkg hkw2
        have hw_ne_u : w ≠ u.val := fun h => hu_not (h ▸ hw_in_k)
        have hw_ne_v : w ≠ v.val := fun h => hv_not (h ▸ hw_in_k)
        have hw_ne_w1 : w ≠ w1 := fun h => hw1_not (h ▸ hw_in_k)
        have hw_ne_w2 : w ≠ w2 := fun h => hw2_not (h ▸ hw_in_k)
        by_cases hwn : w < n
        · let i : Fin n := ⟨w, hwn⟩
          have hiu : i ≠ u := fun h => hw_ne_u (congrArg Fin.val h)
          have hiv : i ≠ v := fun h => hw_ne_v (congrArg Fin.val h)
          rw [wireVal_input C x i, wireVal_input C y i]
          exact hrest i hiu hiv
        · push Not at hwn
          have hwlt := EffGate.inputs_lt (heff_valid k hknr) hw
          let k' : Fin G := ⟨w - n, by omega⟩
          have hk'eq : n + k'.val = w := by simp [k']; omega
          have hk'L : k' ∈ L := hL_step_pred k hkL k' (by rw [hk'eq]; exact hw_in_k)
          have hk'lt : k'.val < m := by omega
          rw [← hk'eq]
          exact ih k'.val hk'lt k' rfl hk'L (by rw [hk'eq]; exact hw_ne_w1)
            (by rw [hk'eq]; exact hw_ne_w2) x y hrest hhfn

  -- Check jOut is neither w1 nor w2 (since C_n is not x_p or !x_p)
  have hjOut_ne_w1 : n + jOut.val ≠ w1 := by
    intro h
    cases neg1
    · apply cycleEdge_not_eq_input hn u
      intro x; rw [← houtW_eq x, ← hjOut_eq, h, hw1_eval x]; simp
    · apply cycleEdge_not_eq_not_input u
      intro x; rw [← houtW_eq x, ← hjOut_eq, h, hw1_eval x]; cases x u <;> simp
  have hjOut_ne_w2 : n + jOut.val ≠ w2 := by
    intro h
    cases neg2
    · apply cycleEdge_not_eq_input hn v
      intro x; rw [← houtW_eq x, ← hjOut_eq, h, hw2_eval x]; simp
    · apply cycleEdge_not_eq_not_input v
      intro x; rw [← houtW_eq x, ← hjOut_eq, h, hw2_eval x]; cases x v <;> simp

  -- Apply cycleEdge_three_subfunctions to get contradiction!
  apply cycleEdge_three_subfunctions hn u v huv hfn
  intro x y hrest hhfn
  have hval := h_bottleneck jOut.val jOut rfl hjOut_L hjOut_ne_w1 hjOut_ne_w2 x y hrest hhfn
  rw [← houtW_eq x, ← houtW_eq y, ← hjOut_eq, hval]

end PEqualNP.Outside.L_meta_1413

theorem PEqualNP.Outside.L_meta_1413 : ∀ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → C.size = 10 → (∀ x : Fin 7 → Bool, C.eval (List.ofFn x) = true ↔ ∃ i : Fin 7, x i = true ∧ x (i + 1) = true) → ∃ (p : Fin 7) (b : Bool) (S : Finset (Fin 10)), (if b = true then 4 else 3) ≤ S.card ∧ ∀ j ∈ S, (∀ y z : Fin 7 → Bool, y p = b → z p = b → (C.wires (List.ofFn y)).getD (7 + ((j : Fin 10) : ℕ)) false = (C.wires (List.ofFn z)).getD (7 + ((j : Fin 10) : ℕ)) false) ∨ ∃ w < 7 + ((j : Fin 10) : ℕ), ∀ u : Fin 7 → Bool, u p = b → (C.wires (List.ofFn u)).getD (7 + ((j : Fin 10) : ℕ)) false = (C.wires (List.ofFn u)).getD w false := by
  intro C hgates hsize heval
  exact PEqualNP.Outside.L_meta_1413.tight_sub_of_cycle (n := 7) (G := 10) (by omega) C hgates hsize heval
