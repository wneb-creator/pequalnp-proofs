import PEqualNP.MetaComplexity.Helpers.Deg3Subst

/-!
# The guard lemma (L-meta-965), circuit pieces; conjecture until checked
-/

namespace PEqualNP.MetaComplexity.Guard965

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Deg3
open PEqualNP.MetaComplexity.LineDegTest

/-- Renumbering of a wire for a copy placed after `s` more gates: inputs stay, gate wires move. -/
def shIdx (n s i : ℕ) : ℕ := if i < n then i else i + s

/-- A gate of the moved copy. -/
def shGate (n s : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shIdx n s)⟩

theorem fold_append {α : Type} (δ : α) (Φ : GateOp → List α → α) (a b : List Gate)
    (init : List α) : d3r1Fold δ Φ (a ++ b) init = d3r1Fold δ Φ b (d3r1Fold δ Φ a init) := by
  simp [d3r1Fold, List.foldl_append]

theorem fold_shift {α : Type} (δ : α) (Φ : GateOp → List α → α) (F init : List α) (n s : ℕ)
    (hinit : init.length = n) (hF : F.length = n + s) (hFi : ∀ i < n, F.getD i δ = init.getD i δ)
    (H : List Gate) : ∀ u, (d3r1Fold δ Φ (H.map (shGate n s)) F).getD (shIdx n s u) δ =
      (d3r1Fold δ Φ H init).getD u δ := by
  induction H using List.reverseRecOn with
  | nil =>
    intro u
    simp only [List.map_nil, d3r1Fold, List.foldl_nil]
    unfold shIdx
    split_ifs with h
    · exact hFi u h
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
  | append_singleton H g ih =>
    intro u
    rw [List.map_append, List.map_singleton, d3r1Fold_snoc, d3r1Fold_snoc]
    have hA := d3r1Fold_length δ Φ (H.map (shGate n s)) F
    have hB := d3r1Fold_length δ Φ H init
    simp only [List.length_map] at hA
    have ihu := ih u
    unfold shIdx at ihu ⊢
    split_ifs with hu
    · rw [if_pos hu] at ihu
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      exact ihu
    · rw [if_neg hu] at ihu
      rcases lt_trichotomy u (n + H.length) with h | h | h
      · rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
        exact ihu
      · rw [List.getD_append_right _ _ _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
        rw [hA, hB, show u + s - (F.length + H.length) = 0 by omega,
          show u - (init.length + H.length) = 0 by omega]
        simp only [List.getD_cons_zero, shGate, List.map_map]
        congr 1
        apply List.map_congr_left
        intro i _
        exact ih i
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem foldr_max_zero (l : List ℕ) (h : ∀ x ∈ l, x = 0) : l.foldr max 0 = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    simp only [List.foldr_cons]
    rw [h a (by simp), ih (fun x hx => h x (by simp [hx]))]
    rfl

theorem foldr_max_le (l : List ℕ) (d : ℕ) (h : ∀ x ∈ l, x ≤ d) : l.foldr max 0 ≤ d := by
  induction l with
  | nil => exact Nat.zero_le _
  | cons a l ih =>
    simp only [List.foldr_cons]
    exact max_le (h a (by simp)) (ih (fun x hx => h x (by simp [hx])))

theorem gate_deg_zero (fv : ℕ → Option Bool) (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (f : ℕ → ℕ) (hf : ∀ i, fv i = none → f i = 0) :
    d3r1DegOp (d3sGate fv g).op ((d3sGate fv g).inputs.map f) = 0 := by
  obtain ⟨op, ins⟩ := g
  have hfil : ∀ x ∈ (ins.filter (fun i => (fv i).isNone)).map f, x = 0 := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
    have := (List.mem_filter.1 hi).2
    exact hf i (by simpa using this)
  simp only at hop
  rcases hop with rfl | rfl
  · simp only [d3sGate]
    split_ifs
    · simp [d3r1DegOp]
    · simp only [d3r1DegOp, if_pos rfl]
      exact List.sum_eq_zero hfil
  · simp only [d3sGate]
    split_ifs
    · simp [d3r1DegOp]
    · simp only [d3r1DegOp]
      simp only [reduceCtorEq, if_false]
      exact foldr_max_zero _ hfil

theorem fold_deg_zero (fv : ℕ → Option Bool) (init : List ℕ)
    (hinit : ∀ i, fv i = none → init.getD i 0 = 0) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ t, fv t = none → (d3r1Fold 0 d3r1DegOp (gs.map (d3sGate fv)) init).getD t 0 = 0 := by
  induction gs using List.reverseRecOn with
  | nil => intro t ht; simpa [d3r1Fold] using hinit t ht
  | append_singleton gs g ih =>
    intro t ht
    have ih' := ih (fun g hg => hgs g (List.mem_append_left _ hg))
    rw [List.map_append, List.map_singleton, d3r1Fold_snoc]
    rcases lt_trichotomy t (d3r1Fold 0 d3r1DegOp (gs.map (d3sGate fv)) init).length with h | h | h
    · rw [List.getD_append _ _ _ _ h]; exact ih' t ht
    · rw [List.getD_append_right _ _ _ _ (le_of_eq h.symm), h, Nat.sub_self, List.getD_cons_zero]
      exact gate_deg_zero fv g (hgs g (by simp)) _ ih'
    · rw [List.getD_eq_default _ _ (by simp; omega)]


/-! ## The tail: one AND per product, then an OR chain -/

/-- What the guard copy reads at wire `a`: `some c` if it is a constant `c` there. -/
def gA (n s : ℕ) (fv : ℕ → Option Bool) (a : ℕ) : Option Bool :=
  if n + s ≤ a then some false else fv a

/-- The product gate: the guard copy at `a` and the original circuit at `b`. -/
def termGate (n s : ℕ) (fv : ℕ → Option Bool) (a b : ℕ) : Gate :=
  if gA n s fv a = some false ∨ n + s ≤ b then ⟨GateOp.or, []⟩
  else ⟨GateOp.and, (if gA n s fv a = some true then [] else [shIdx n s a]) ++ [b]⟩

/-- The OR chain gate number `k`, after the base of `N0` wires. -/
def orGate (N0 k : ℕ) : Gate :=
  if k = 0 then ⟨GateOp.or, [N0]⟩ else ⟨GateOp.or, [N0 + 2 * k - 1, N0 + 2 * k]⟩

/-- The tail of `k` products. -/
def tailG (n s : ℕ) (fv : ℕ → Option Bool) (fa fb : ℕ → ℕ) : ℕ → List Gate
  | 0 => []
  | k + 1 => tailG n s fv fa fb k ++ [termGate n s fv (fa k) (fb k), orGate (n + s + s) k]

theorem tailG_length (n s : ℕ) (fv : ℕ → Option Bool) (fa fb : ℕ → ℕ) (k : ℕ) :
    (tailG n s fv fa fb k).length = 2 * k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [tailG, ih]; omega

theorem termGate_inputs_lt (n s : ℕ) (fv : ℕ → Option Bool) (a b : ℕ) :
    ∀ i ∈ (termGate n s fv a b).inputs, i < n + s + s := by
  intro i hi
  unfold termGate at hi
  split_ifs at hi with hc hd
  · simp at hi
  · simp only [List.nil_append, List.mem_singleton] at hi
    push_neg at hc; omega
  · simp only [List.singleton_append, List.mem_cons, List.mem_singleton, List.not_mem_nil,
      or_false] at hi
    push_neg at hc
    have ha : ¬ n + s ≤ a := by
      intro h; apply hc.1; simp [gA, h]
    rcases hi with rfl | rfl
    · unfold shIdx; split_ifs <;> omega
    · omega

theorem termGate_mono (n s : ℕ) (fv : ℕ → Option Bool) (a b : ℕ) :
    (termGate n s fv a b).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
      (termGate n s fv a b).inputs.length ≤ 2 := by
  unfold termGate
  split_ifs <;> simp

theorem orGate_mono (N0 k : ℕ) :
    (orGate N0 k).op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ (orGate N0 k).inputs.length ≤ 2 := by
  unfold orGate
  split_ifs <;> simp

theorem fold_two {α : Type} (δ : α) (Φ : GateOp → List α → α) (g1 g2 : Gate) (F : List α) :
    d3r1Fold δ Φ [g1, g2] F = (F ++ [Φ g1.op (g1.inputs.map fun i => F.getD i δ)]) ++
      [Φ g2.op (g2.inputs.map fun i => (F ++ [Φ g1.op (g1.inputs.map fun i => F.getD i δ)]).getD i δ)] :=
  rfl

/-- The value of the tail: the OR chain reads the OR of the product values. -/
theorem tail_val (n s : ℕ) (fv : ℕ → Option Bool) (fa fb : ℕ → ℕ) (B : List Bool)
    (hB : B.length = n + s + s) (tv : ℕ → Bool)
    (htv : ∀ k, (termGate n s fv (fa k) (fb k)).op.eval
      ((termGate n s fv (fa k) (fb k)).inputs.map fun i => B.getD i false) = tv k) :
    ∀ k, (d3r1Fold false GateOp.eval (tailG n s fv fa fb k) B).length = n + s + s + 2 * k ∧
      (∀ i < n + s + s, (d3r1Fold false GateOp.eval (tailG n s fv fa fb k) B).getD i false =
        B.getD i false) ∧
      (0 < k → (d3r1Fold false GateOp.eval (tailG n s fv fa fb k) B).getD (n + s + s + 2 * k - 1)
        false = decide (∃ j < k, tv j = true)) := by
  intro k
  induction k with
  | zero => exact ⟨by simp [tailG, d3r1Fold, hB], fun i _ => by simp [tailG, d3r1Fold], by simp⟩
  | succ k ih =>
    obtain ⟨hl, hpre, hlast⟩ := ih
    set F := d3r1Fold false GateOp.eval (tailG n s fv fa fb k) B with hFdef
    have hstep : d3r1Fold false GateOp.eval (tailG n s fv fa fb (k + 1)) B =
        d3r1Fold false GateOp.eval [termGate n s fv (fa k) (fb k), orGate (n + s + s) k] F := by
      simp only [tailG]; rw [fold_append]
    rw [hstep, fold_two]
    have hread : ∀ i ∈ (termGate n s fv (fa k) (fb k)).inputs, F.getD i false = B.getD i false :=
      fun i hi => hpre i (termGate_inputs_lt n s fv _ _ i hi)
    have hvt : (termGate n s fv (fa k) (fb k)).op.eval
        ((termGate n s fv (fa k) (fb k)).inputs.map fun i => F.getD i false) = tv k := by
      rw [← htv k]; congr 1; exact List.map_congr_left hread
    rw [hvt]
    refine ⟨by simp [hl]; omega, ?_, ?_⟩
    · intro i hi
      rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]
      exact hpre i hi
    · intro _
      rw [List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_append, List.length_singleton, hl,
        show n + s + s + 2 * (k + 1) - 1 - (n + s + s + 2 * k + 1) = 0 by omega,
        List.getD_cons_zero]
      unfold orGate
      split_ifs with hk
      · subst hk
        simp only [List.map_cons, List.map_nil, GateOp.eval]
        rw [List.getD_append_right _ _ _ _ (by omega)]
        simp only [hl, Nat.mul_zero, Nat.add_zero, Nat.sub_self, List.getD_cons_zero]
        cases h : tv 0 <;> simp [h]
      · simp only [List.map_cons, List.map_nil, GateOp.eval]
        rw [List.getD_append _ _ _ _ (by omega), hlast (by omega),
          List.getD_append_right _ _ _ _ (by omega)]
        simp only [hl, Nat.sub_self, List.getD_cons_zero]
        have hiff : (∃ j < k + 1, tv j = true) ↔ ((∃ j < k, tv j = true) ∨ tv k = true) := by
          constructor
          · rintro ⟨j, hj, h⟩
            rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
            · exact Or.inl ⟨j, hj, h⟩
            · exact Or.inr h
          · rintro (⟨j, hj, h⟩ | h)
            · exact ⟨j, by omega, h⟩
            · exact ⟨k, by omega, h⟩
        rw [Bool.eq_iff_iff]
        simp only [Bool.or_eq_true, List.all_cons, List.any_cons, List.any_nil, Bool.or_false,
          id, decide_eq_true_eq]
        rw [hiff]

/-- The degrees of the tail: at most one. -/
theorem tail_deg (n s : ℕ) (fv : ℕ → Option Bool) (fa fb : ℕ → ℕ) (B : List ℕ)
    (hB : B.length = n + s + s) (K : ℕ)
    (htd : ∀ k < K, d3r1DegOp (termGate n s fv (fa k) (fb k)).op
      ((termGate n s fv (fa k) (fb k)).inputs.map fun i => B.getD i 0) ≤ 1) :
    ∀ k ≤ K, (d3r1Fold 0 d3r1DegOp (tailG n s fv fa fb k) B).length = n + s + s + 2 * k ∧
      (∀ i < n + s + s, (d3r1Fold 0 d3r1DegOp (tailG n s fv fa fb k) B).getD i 0 = B.getD i 0) ∧
      (∀ i, n + s + s ≤ i → (d3r1Fold 0 d3r1DegOp (tailG n s fv fa fb k) B).getD i 0 ≤ 1) := by
  intro k
  induction k with
  | zero =>
    intro _
    refine ⟨by simp [tailG, d3r1Fold, hB], fun i _ => by simp [tailG, d3r1Fold], fun i hi => ?_⟩
    simp only [tailG, d3r1Fold, List.foldl_nil]
    rw [List.getD_eq_default _ _ (by omega)]; exact Nat.zero_le _
  | succ k ih =>
    intro hkK
    obtain ⟨hl, hpre, hhi⟩ := ih (by omega)
    set F := d3r1Fold 0 d3r1DegOp (tailG n s fv fa fb k) B with hFdef
    have hstep : d3r1Fold 0 d3r1DegOp (tailG n s fv fa fb (k + 1)) B =
        d3r1Fold 0 d3r1DegOp [termGate n s fv (fa k) (fb k), orGate (n + s + s) k] F := by
      simp only [tailG]; rw [fold_append]
    rw [hstep, fold_two]
    have hread : ∀ i ∈ (termGate n s fv (fa k) (fb k)).inputs, F.getD i 0 = B.getD i 0 :=
      fun i hi => hpre i (termGate_inputs_lt n s fv _ _ i hi)
    set vt := d3r1DegOp (termGate n s fv (fa k) (fb k)).op
        ((termGate n s fv (fa k) (fb k)).inputs.map fun i => F.getD i 0) with hvtdef
    have hvt : vt ≤ 1 := by
      rw [hvtdef]
      have := htd k (by omega)
      rwa [List.map_congr_left hread]
    have hF1 : ∀ i, n + s + s ≤ i → (F ++ [vt]).getD i 0 ≤ 1 := by
      intro i hi
      rcases lt_trichotomy i F.length with h | h | h
      · rw [List.getD_append _ _ _ _ h]; exact hhi i hi
      · rw [List.getD_append_right _ _ _ _ (by omega), h, Nat.sub_self]; exact hvt
      · rw [List.getD_eq_default _ _ (by simp; omega)]; exact Nat.zero_le _
    have hor : d3r1DegOp (orGate (n + s + s) k).op
        ((orGate (n + s + s) k).inputs.map fun i => (F ++ [vt]).getD i 0) ≤ 1 := by
      have hge : ∀ i ∈ (orGate (n + s + s) k).inputs, n + s + s ≤ i := by
        intro i hi; unfold orGate at hi; split_ifs at hi <;> simp at hi <;> omega
      have hop : (orGate (n + s + s) k).op = GateOp.or := by unfold orGate; split_ifs <;> rfl
      rw [hop]
      simp only [d3r1DegOp, reduceCtorEq, if_false]
      apply foldr_max_le
      intro x hx
      obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
      exact hF1 i (hge i hi)
    refine ⟨by simp [hl]; omega, ?_, ?_⟩
    · intro i hi
      rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append _ _ _ _ (by omega)]
      exact hpre i hi
    · intro i hi
      rcases lt_trichotomy i (F ++ [vt]).length with h | h | h
      · rw [List.getD_append _ _ _ _ h]; exact hF1 i hi
      · rw [List.getD_append_right _ _ _ _ (by omega), h, Nat.sub_self]; exact hor
      · rw [List.getD_eq_default _ _ (by simp at h ⊢; omega)]; exact Nat.zero_le _


theorem gA_none (n s : ℕ) (fv : ℕ → Option Bool) (a : ℕ) (h1 : gA n s fv a ≠ some false)
    (h2 : gA n s fv a ≠ some true) : a < n + s ∧ fv a = none := by
  have hnone : gA n s fv a = none := by
    cases h : gA n s fv a with
    | none => rfl
    | some c => cases c <;> simp_all
  have ha : ¬ n + s ≤ a := by intro h; simp [gA, h] at hnone
  exact ⟨by omega, by simpa [gA, ha] using hnone⟩

theorem termGate_eval (n s : ℕ) (fv : ℕ → Option Bool) (a b : ℕ) (B : List Bool)
    (A0 V0 : ℕ → Bool)
    (h1 : ∀ t < n + s, B.getD t false = V0 t)
    (h2 : ∀ t, fv t = none → t < n + s → B.getD (shIdx n s t) false = A0 t)
    (h3 : ∀ t c, gA n s fv t = some c → A0 t = c)
    (h4 : ∀ t, n + s ≤ t → V0 t = false) :
    (termGate n s fv a b).op.eval ((termGate n s fv a b).inputs.map fun i => B.getD i false) =
      (A0 a && V0 b) := by
  unfold termGate
  split_ifs with hc hd
  · simp only [GateOp.eval, List.map_nil, List.any_nil]
    rcases hc with hc | hc
    · rw [h3 a false hc]; rfl
    · rw [h4 b hc, Bool.and_false]
  · push_neg at hc
    simp only [List.nil_append, List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
      List.all_nil, id, Bool.and_true]
    rw [h1 b (by omega), h3 a true hd, Bool.true_and]
  · push_neg at hc
    obtain ⟨ha, hfv⟩ := gA_none n s fv a hc.1 hd
    simp only [List.singleton_append, List.map_cons, List.map_nil, GateOp.eval, List.all_cons,
      List.all_nil, id, Bool.and_true]
    rw [h2 a hfv ha, h1 b (by omega)]

theorem termGate_deg (n s : ℕ) (fv : ℕ → Option Bool) (a b : ℕ) (B : List ℕ)
    (h2 : ∀ t, fv t = none → t < n + s → B.getD (shIdx n s t) 0 = 0)
    (hb : b < n + s → B.getD b 0 ≤ 1) :
    d3r1DegOp (termGate n s fv a b).op ((termGate n s fv a b).inputs.map fun i => B.getD i 0) ≤ 1 := by
  unfold termGate
  split_ifs with hc hd
  · simp [d3r1DegOp]
  · push_neg at hc
    simp only [List.nil_append, List.map_cons, List.map_nil, d3r1DegOp, if_pos rfl, List.sum_cons,
      List.sum_nil, Nat.add_zero]
    exact hb (by omega)
  · push_neg at hc
    obtain ⟨ha, hfv⟩ := gA_none n s fv a hc.1 hd
    have hb1 := hb (by omega)
    simp only [List.singleton_append, List.map_cons, List.map_nil, h2 a hfv ha]
    unfold d3r1DegOp
    split_ifs with hh <;> simp_all

theorem tailG_mono (n s : ℕ) (fv : ℕ → Option Bool) (fa fb : ℕ → ℕ) (k : ℕ) :
    ∀ g ∈ tailG n s fv fa fb k, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction k with
  | zero => intro g hg; simp [tailG] at hg
  | succ k ih =>
    intro g hg
    simp only [tailG, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact ih g hg
    · exact termGate_mono _ _ _ _ _
    · exact orGate_mono _ _

/-! ## The guard circuit -/

/-- The guard circuit: the original gates, the guard copy with every fixed input substituted,
then the tail of `J` products. -/
def guardCkt (n : ℕ) (C : Circuit) (fv : ℕ → Option Bool) (fa fb : ℕ → ℕ) (J : ℕ) : Circuit :=
  ⟨(C.gates ++ (C.gates.map (d3sGate fv)).map (shGate n C.gates.length)) ++
      tailG n C.gates.length fv fa fb J, n + C.gates.length + C.gates.length + 2 * J - 1⟩

theorem guardCkt_size (n : ℕ) (C : Circuit) (fv : ℕ → Option Bool) (fa fb : ℕ → ℕ) (J : ℕ) :
    (guardCkt n C fv fa fb J).size = C.size + C.size + 2 * J := by
  simp [guardCkt, Circuit.size, tailG_length]; omega

theorem guardCkt_mono (n : ℕ) (C : Circuit) (fv : ℕ → Option Bool) (fa fb : ℕ → ℕ) (J : ℕ)
    (hm : Monotone2 C) : Monotone2 (guardCkt n C fv fa fb J) := by
  intro g hg
  simp only [guardCkt, List.mem_append, List.mem_map] at hg
  rcases hg with (hg | ⟨g1, ⟨g0, hg0, rfl⟩, rfl⟩) | hg
  · exact hm g hg
  · simpa [shGate] using d3s_gate_mono fv g0 (hm g0 hg0)
  · exact tailG_mono _ _ _ _ _ _ g hg

theorem guardCkt_val (n : ℕ) (C : Circuit) (hG : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (fx : Fin n → Option Bool) (fa fb : ℕ → ℕ) (J : ℕ) (hJ : 0 < J) (z : Fin n → Bool) :
    (guardCkt n C (d3sFv n fx) fa fb J).eval (List.ofFn z) = decide (∃ j < J,
      (C.wires (List.ofFn (fun i => (fx i).getD (z i)))).getD (fa j) false = true ∧
      (C.wires (List.ofFn z)).getD (fb j) false = true) := by
  set s := C.gates.length with hs
  set fv := d3sFv n fx with hfv
  unfold Circuit.eval
  rw [d3r1_wires_eq, d3r1_wires_eq, d3r1_wires_eq]
  simp only [guardCkt]
  rw [fold_append, fold_append]
  set F0 := d3r1Fold false GateOp.eval C.gates (List.ofFn z) with hF0
  set B := d3r1Fold false GateOp.eval ((C.gates.map (d3sGate fv)).map (shGate n s)) F0 with hBdef
  have hF0l : F0.length = n + s := by simp [hF0, d3r1Fold_length, hs]
  have hBl : B.length = n + s + s := by simp [hBdef, d3r1Fold_length, hF0l, hs]
  have h1 : ∀ t < n + s, B.getD t false = F0.getD t false := fun t ht =>
    d3r1Fold_lt _ _ _ _ _ (by omega)
  have h2 : ∀ t, fv t = none → t < n + s → B.getD (shIdx n s t) false =
      (d3r1Fold false GateOp.eval C.gates (List.ofFn (fun i => (fx i).getD (z i)))).getD t false := by
    intro t ht _
    rw [hBdef, fold_shift false GateOp.eval F0 (List.ofFn z) n s (by simp) hF0l
      (fun i hi => d3r1Fold_lt _ _ _ _ _ (by simp; omega))]
    exact (d3s_inv n fx z (List.range 0) C.gates hG).1 t ht
  have h3 : ∀ t c, gA n s fv t = some c →
      (d3r1Fold false GateOp.eval C.gates (List.ofFn (fun i => (fx i).getD (z i)))).getD t false = c := by
    intro t c htc
    unfold gA at htc
    split_ifs at htc with hts
    · cases htc
      exact d3r1Fold_ge _ _ _ _ _ (by simp; omega)
    · rw [hfv] at htc
      unfold d3sFv at htc
      split_ifs at htc with htn
      rw [d3r1Fold_lt _ _ _ _ _ (by simp [htn]), ofFn_getD, dif_pos htn, htc]
      rfl
  have h4 : ∀ t, n + s ≤ t → F0.getD t false = false := fun t ht =>
    d3r1Fold_ge _ _ _ _ _ (by simp; omega)
  have htv := fun k => termGate_eval n s fv (fa k) (fb k) B _ _ h1 h2 h3 h4
  obtain ⟨_, _, hlast⟩ := tail_val n s fv fa fb B hBl _ htv J
  rw [hlast hJ]
  simp only [Bool.and_eq_true]

theorem guardCkt_deg (n : ℕ) (C : Circuit) (hG : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (fx : Fin n → Option Bool) (fa fb : ℕ → ℕ) (J : ℕ) (hJ : 0 < J) (marked : Finset ℕ)
    (hmk : ∀ i < n, d3sFv n fx i = none → i ∉ marked)
    (hb : ∀ j < J, (C.lineDegrees n marked).getD (fb j) 0 ≤ 1) :
    HasLineDegree n marked (guardCkt n C (d3sFv n fx) fa fb J) 1 := by
  set s := C.gates.length with hs
  set fv := d3sFv n fx with hfv
  unfold HasLineDegree Circuit.lineDeg
  rw [d3r1_lineDegrees_eq]
  have hC := d3r1_lineDegrees_eq C n marked
  simp only [guardCkt]
  rw [fold_append, fold_append]
  set init := (List.range n).map fun i => if i ∈ marked then 1 else 0 with hinit
  have hil : init.length = n := by simp [hinit]
  set F0 := d3r1Fold 0 d3r1DegOp C.gates init with hF0
  set B := d3r1Fold 0 d3r1DegOp ((C.gates.map (d3sGate fv)).map (shGate n s)) F0 with hBdef
  have hF0l : F0.length = n + s := by simp [hF0, d3r1Fold_length, hil, hs]
  have hBl : B.length = n + s + s := by simp [hBdef, d3r1Fold_length, hF0l, hs]
  have h2 : ∀ t, fv t = none → t < n + s → B.getD (shIdx n s t) 0 = 0 := by
    intro t ht _
    rw [hBdef, fold_shift 0 d3r1DegOp F0 init n s hil hF0l
      (fun i hi => d3r1Fold_lt _ _ _ _ _ (by omega))]
    refine fold_deg_zero fv init ?_ C.gates hG t ht
    intro i hi
    by_cases hin : i < n
    · rw [hinit, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hin]
      simp [hmk i hin hi]
    · exact List.getD_eq_default _ _ (by omega)
  have htd : ∀ k < J, d3r1DegOp (termGate n s fv (fa k) (fb k)).op
      ((termGate n s fv (fa k) (fb k)).inputs.map fun i => B.getD i 0) ≤ 1 := by
    intro k hk
    apply termGate_deg n s fv (fa k) (fb k) B h2
    intro hbk
    rw [d3r1Fold_lt _ _ _ _ _ (by omega)]
    have := hb k hk
    rw [hC] at this
    exact this
  obtain ⟨_, _, hhi⟩ := tail_deg n s fv fa fb B hBl J htd J le_rfl
  exact hhi _ (by omega)

end PEqualNP.MetaComplexity.Guard965
