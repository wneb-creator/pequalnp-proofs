import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_109

open Finset

def IsLeaf {n : ℕ} (A : Fin n → Fin n → Prop) (t : ℕ) (ρ : Fin n → Option Bool) : Prop :=
  (∃ u v : Fin n, A u v ∧ ρ u = some false ∧ ρ v = some false) ∨
  (∃ S : Finset (Fin n), S.card = t ∧ ∀ x ∈ S, ρ x = some true)

def IsValidN {n : ℕ} (A : Fin n → Fin n → Prop) (t : ℕ) (N : (Fin n → Option Bool) → ℕ) : Prop :=
  ∀ ρ : Fin n → Option Bool,
    (IsLeaf A t ρ ∧ 1 ≤ N ρ) ∨
    ∃ y : Fin n, ρ y = none ∧
      N (Function.update ρ y (some false)) + N (Function.update ρ y (some true)) ≤ N ρ

inductive DT (n : ℕ) where
  | leaf : DT n
  | branch : Fin n → DT n → DT n → DT n

def DT.leaves {n : ℕ} : DT n → ℕ
  | .leaf => 1
  | .branch _ f t => f.leaves + t.leaves

def DT.restrictAll {n : ℕ} (ρ : Fin n → Option Bool) : DT n → DT n
  | .leaf => .leaf
  | .branch u f t =>
    match ρ u with
    | none => .branch u (f.restrictAll ρ) (t.restrictAll ρ)
    | some false => f.restrictAll ρ
    | some true => t.restrictAll ρ

def DT.Valid {n : ℕ} (A : Fin n → Fin n → Prop) (t : ℕ) :
    (Fin n → Option Bool) → DT n → Prop
  | ρ, .leaf => IsLeaf A t ρ
  | ρ, .branch u f t' =>
    DT.Valid A t (Function.update ρ u (some false)) f ∧
    DT.Valid A t (Function.update ρ u (some true)) t'

def Extends {n : ℕ} (ρ₀ ρ : Fin n → Option Bool) : Prop :=
  ∀ x b, ρ₀ x = some b → ρ x = some b

lemma extends_refl {n : ℕ} (ρ : Fin n → Option Bool) : Extends ρ ρ :=
  fun _ _ h => h

lemma extends_update_none {n : ℕ} (ρ : Fin n → Option Bool) (y : Fin n) (b : Bool)
    (hy : ρ y = none) : Extends ρ (Function.update ρ y (some b)) := by
  intro x c hx
  by_cases hxy : x = y
  · subst hxy; rw [hy] at hx; cases hx
  · rw [Function.update_of_ne hxy]; exact hx

lemma extends_update_eq {n : ℕ} {ρ₀ ρ : Fin n → Option Bool} (h : Extends ρ₀ ρ)
    (u : Fin n) (b : Bool) (hu : ρ u = some b) :
    Extends (Function.update ρ₀ u (some b)) ρ := by
  intro x c hx
  by_cases hxu : x = u
  · subst hxu
    rw [Function.update_self] at hx
    rw [hu]; exact hx
  · rw [Function.update_of_ne hxu] at hx
    exact h x c hx

lemma isLeaf_mono {n : ℕ} {A : Fin n → Fin n → Prop} {t : ℕ} {ρ₀ ρ : Fin n → Option Bool}
    (he : Extends ρ₀ ρ) (hl : IsLeaf A t ρ₀) : IsLeaf A t ρ := by
  rcases hl with ⟨u, v, huv, hu, hv⟩ | ⟨S, hSc, hS⟩
  · exact Or.inl ⟨u, v, huv, he u false hu, he v false hv⟩
  · exact Or.inr ⟨S, hSc, fun x hx => he x true (hS x hx)⟩

lemma restrictAll_none {n : ℕ} (T : DT n) :
    T.restrictAll (fun _ => none) = T := by
  induction T with
  | leaf => rfl
  | branch u f t ihf iht => simp [DT.restrictAll, ihf, iht]

lemma restrictAll_leaves_mono {n : ℕ} (T : DT n) {ρ ρ' : Fin n → Option Bool}
    (he : Extends ρ ρ') : (T.restrictAll ρ').leaves ≤ (T.restrictAll ρ).leaves := by
  induction T with
  | leaf => simp [DT.restrictAll, DT.leaves]
  | branch u f t ihf iht =>
    simp only [DT.restrictAll]
    cases hu : ρ u with
    | none =>
      cases hu' : ρ' u with
      | none =>
        simp only [DT.leaves]
        omega
      | some b =>
        cases b with
        | false =>
          simp only [DT.leaves]
          omega
        | true =>
          simp only [DT.leaves]
          omega
    | some b =>
      have hu' : ρ' u = some b := he u b hu
      rw [hu']
      cases b with
      | false => exact ihf
      | true => exact iht

lemma restrictAll_leaves_pos {n : ℕ} (T : DT n) (ρ : Fin n → Option Bool) :
    1 ≤ (T.restrictAll ρ).leaves := by
  induction T with
  | leaf => simp [DT.restrictAll, DT.leaves]
  | branch u f t ihf iht =>
    simp only [DT.restrictAll]
    cases ρ u with
    | none => simp only [DT.leaves]; omega
    | some b => cases b <;> assumption

lemma valid_restrictAll_step {n : ℕ} {A : Fin n → Fin n → Prop} {t : ℕ}
    (T : DT n) :
    ∀ {ρ₀ ρ : Fin n → Option Bool}, Extends ρ₀ ρ → T.Valid A t ρ₀ →
      (IsLeaf A t ρ ∧ 1 ≤ (T.restrictAll ρ).leaves) ∨
      ∃ y : Fin n, ρ y = none ∧
        (T.restrictAll (Function.update ρ y (some false))).leaves +
        (T.restrictAll (Function.update ρ y (some true))).leaves ≤
        (T.restrictAll ρ).leaves := by
  induction T with
  | leaf =>
    intro ρ₀ ρ he hv
    exact Or.inl ⟨isLeaf_mono he hv, by simp [DT.restrictAll, DT.leaves]⟩
  | branch u f t' ihf iht =>
    intro ρ₀ ρ he ⟨hvf, hvt⟩
    cases hu : ρ u with
    | none =>
      refine Or.inr ⟨u, hu, ?_⟩
      simp only [DT.restrictAll, hu, Function.update_self, DT.leaves]
      have h1 := restrictAll_leaves_mono f (extends_update_none ρ u false hu)
      have h2 := restrictAll_leaves_mono t' (extends_update_none ρ u true hu)
      omega
    | some b =>
      cases b with
      | false =>
        have hstep := ihf (extends_update_eq he u false hu) hvf
        rcases hstep with ⟨hl, hpos⟩ | ⟨y, hy, hle⟩
        · exact Or.inl ⟨hl, by simp [DT.restrictAll, hu, hpos]⟩
        · have hyu : u ≠ y := by intro h; subst h; rw [hy] at hu; cases hu
          refine Or.inr ⟨y, hy, ?_⟩
          simp only [DT.restrictAll, Function.update_of_ne hyu, hu]
          exact hle
      | true =>
        have hstep := iht (extends_update_eq he u true hu) hvt
        rcases hstep with ⟨hl, hpos⟩ | ⟨y, hy, hle⟩
        · exact Or.inl ⟨hl, by simp [DT.restrictAll, hu, hpos]⟩
        · have hyu : u ≠ y := by intro h; subst h; rw [hy] at hu; cases hu
          refine Or.inr ⟨y, hy, ?_⟩
          simp only [DT.restrictAll, Function.update_of_ne hyu, hu]
          exact hle

lemma valid_dt_gives_N {n : ℕ} {A : Fin n → Fin n → Prop} {t : ℕ} (T : DT n)
    (hv : T.Valid A t (fun _ => none)) :
    ∃ N : (Fin n → Option Bool) → ℕ,
      N (fun _ => none) ≤ T.leaves ∧ IsValidN A t N := by
  refine ⟨fun ρ => (T.restrictAll ρ).leaves, ?_, ?_⟩
  · dsimp only; rw [restrictAll_none]
  · intro ρ
    exact valid_restrictAll_step T (fun _ _ h => by cases h) hv

def noneCount {n : ℕ} (ρ : Fin n → Option Bool) : ℕ :=
  (Finset.univ.filter (fun x : Fin n => ρ x = none)).card

def trueSet {n : ℕ} (ρ : Fin n → Option Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun x : Fin n => ρ x = some true)

def falseSet {n : ℕ} (ρ : Fin n → Option Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun x : Fin n => ρ x = some false)

lemma noneCount_update_lt {n : ℕ} (ρ : Fin n → Option Bool) (y : Fin n) (b : Bool)
    (hy : ρ y = none) :
    noneCount (Function.update ρ y (some b)) < noneCount ρ := by
  unfold noneCount
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    by_cases hxy : x = y
    · subst hxy; rw [Function.update_self] at hx; cases hx
    · rwa [Function.update_of_ne hxy] at hx
  · intro heq
    have hy1 : y ∈ Finset.univ.filter (fun x => ρ x = none) := by simp [hy]
    rw [← heq] at hy1
    simp [Function.update_self] at hy1

lemma trueSet_update_true {n : ℕ} (ρ : Fin n → Option Bool) (y : Fin n)
    (hy : ρ y ≠ some true) :
    trueSet (Function.update ρ y (some true)) = insert y (trueSet ρ) := by
  ext x
  simp only [trueSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  by_cases hxy : x = y
  · subst hxy; simp [Function.update_self]
  · simp [hxy]

lemma trueSet_update_true_card {n : ℕ} (ρ : Fin n → Option Bool) (y : Fin n)
    (hy : ρ y ≠ some true) :
    (trueSet (Function.update ρ y (some true))).card = (trueSet ρ).card + 1 := by
  rw [trueSet_update_true ρ y hy, Finset.card_insert_of_notMem]
  simp [trueSet, hy]

lemma trueSet_update_false {n : ℕ} (ρ : Fin n → Option Bool) (y : Fin n)
    (hy : ρ y ≠ some true) :
    trueSet (Function.update ρ y (some false)) = trueSet ρ := by
  ext x
  simp only [trueSet, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hxy : x = y
  · subst hxy; simp [Function.update_self, hy]
  · simp [Function.update_of_ne hxy]

lemma falseSet_update_true {n : ℕ} (ρ : Fin n → Option Bool) (y : Fin n)
    (hy : ρ y ≠ some false) :
    falseSet (Function.update ρ y (some true)) = falseSet ρ := by
  ext x
  simp only [falseSet, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hxy : x = y
  · subst hxy; simp [Function.update_self, hy]
  · simp [Function.update_of_ne hxy]

lemma falseSet_update_false {n : ℕ} (ρ : Fin n → Option Bool) (y : Fin n) :
    falseSet (Function.update ρ y (some false)) = insert y (falseSet ρ) := by
  ext x
  simp only [falseSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
  by_cases hxy : x = y
  · subst hxy; simp [Function.update_self]
  · simp [hxy]

lemma validN_pos {n : ℕ} {A : Fin n → Fin n → Prop} {t : ℕ}
    {N : (Fin n → Option Bool) → ℕ} (hN : IsValidN A t N) :
    ∀ ρ : Fin n → Option Bool, 1 ≤ N ρ := by
  intro ρ
  induction h : noneCount ρ using Nat.strong_induction_on generalizing ρ with
  | ind k ih =>
    rcases hN ρ with ⟨_, h1⟩ | ⟨y, hy, hle⟩
    · exact h1
    · have hlt := noneCount_update_lt ρ y false hy
      rw [h] at hlt
      have hf := ih _ hlt (Function.update ρ y (some false)) rfl
      omega

lemma validN_isLeaf_of_le_one {n : ℕ} {A : Fin n → Fin n → Prop} {t : ℕ}
    {N : (Fin n → Option Bool) → ℕ} (hN : IsValidN A t N)
    {ρ : Fin n → Option Bool} (h1 : N ρ ≤ 1) : IsLeaf A t ρ := by
  rcases hN ρ with ⟨hl, _⟩ | ⟨y, hy, hle⟩
  · exact hl
  · have hf := validN_pos hN (Function.update ρ y (some false))
    have ht := validN_pos hN (Function.update ρ y (some true))
    omega

lemma not_isLeaf_of_lt_true_no_edge {n : ℕ} {G : SimpleGraph (Fin n)} {t : ℕ}
    {ρ : Fin n → Option Bool}
    (hlt : (trueSet ρ).card < t)
    (hne : ∀ u v : Fin n, G.Adj u v → ¬ (ρ u = some false ∧ ρ v = some false)) :
    ¬ IsLeaf G.Adj t ρ := by
  intro hl
  rcases hl with ⟨u, v, huv, hu, hv⟩ | ⟨S, hSc, hS⟩
  · exact hne u v huv ⟨hu, hv⟩
  · have hsub : S ⊆ trueSet ρ := by
      intro x hx
      simp [trueSet, hS x hx]
    have hc := Finset.card_le_card hsub
    omega

lemma single_false_lower {n : ℕ} {G : SimpleGraph (Fin n)} {t : ℕ}
    {N : (Fin n → Option Bool) → ℕ} (hN : IsValidN G.Adj t N) :
    ∀ r : ℕ, ∀ ρ : Fin n → Option Bool, ∀ w : Fin n,
      (trueSet ρ).card + r = t →
      falseSet ρ = {w} →
      r + 1 ≤ N ρ ∧
      (N ρ = r + 1 →
        ∃ A : Finset (Fin n), A.card = r ∧
          ∀ y ∈ A, G.Adj w y ∧ ρ y = none) := by
  intro r
  induction r with
  | zero =>
    intro ρ w _ _
    refine ⟨validN_pos hN ρ, fun _ => ⟨∅, by simp, by simp⟩⟩
  | succ r ih =>
    intro ρ w hcard hfalse
    have hlt : (trueSet ρ).card < t := by omega
    have hne : ∀ u v : Fin n, G.Adj u v → ¬ (ρ u = some false ∧ ρ v = some false) := by
      intro u v huv ⟨hu, hv⟩
      have hu' : u ∈ falseSet ρ := by simp [falseSet, hu]
      have hv' : v ∈ falseSet ρ := by simp [falseSet, hv]
      rw [hfalse, Finset.mem_singleton] at hu' hv'
      subst hu'; subst hv'
      exact G.loopless.irrefl _ huv
    have hnl := not_isLeaf_of_lt_true_no_edge hlt hne
    rcases hN ρ with ⟨hl, _⟩ | ⟨y, hy, hle⟩
    · exact absurd hl hnl
    · have hyT : ρ y ≠ some true := by rw [hy]; decide
      have hyF : ρ y ≠ some false := by rw [hy]; decide
      have hcard' : (trueSet (Function.update ρ y (some true))).card + r = t := by
        rw [trueSet_update_true_card ρ y hyT]; omega
      have hfalse' : falseSet (Function.update ρ y (some true)) = {w} := by
        rw [falseSet_update_true ρ y hyF]; exact hfalse
      obtain ⟨hih_lb, hih_eq⟩ := ih (Function.update ρ y (some true)) w hcard' hfalse'
      have hf_pos := validN_pos hN (Function.update ρ y (some false))
      refine ⟨by omega, fun heq => ?_⟩
      have hf_eq : N (Function.update ρ y (some false)) ≤ 1 := by omega
      have ht_eq : N (Function.update ρ y (some true)) = r + 1 := by omega
      have hf_leaf := validN_isLeaf_of_le_one hN hf_eq
      have hadj : G.Adj w y := by
        rcases hf_leaf with ⟨u, v, huv, hu, hv⟩ | ⟨S, hSc, hS⟩
        · have hu' : u ∈ falseSet (Function.update ρ y (some false)) := by simp [falseSet, hu]
          have hv' : v ∈ falseSet (Function.update ρ y (some false)) := by simp [falseSet, hv]
          rw [falseSet_update_false, hfalse, Finset.mem_insert, Finset.mem_singleton] at hu' hv'
          have hne_uv : u ≠ v := G.ne_of_adj huv
          rcases hu' with rfl | rfl <;> rcases hv' with rfl | rfl
          · exact absurd rfl hne_uv
          · exact huv.symm
          · exact huv
          · exact absurd rfl hne_uv
        · have hsub : S ⊆ trueSet (Function.update ρ y (some false)) := by
            intro x hx; simp [trueSet, hS x hx]
          rw [trueSet_update_false ρ y hyT] at hsub
          have hc := Finset.card_le_card hsub
          omega
      obtain ⟨A, hAc, hA⟩ := hih_eq ht_eq
      have hyA : y ∉ A := by
        intro hyin
        have hyn := (hA y hyin).2
        rw [Function.update_self] at hyn
        cases hyn
      refine ⟨insert y A, by rw [Finset.card_insert_of_notMem hyA, hAc], ?_⟩
      intro z hz
      rw [Finset.mem_insert] at hz
      rcases hz with rfl | hzA
      · exact ⟨hadj, hy⟩
      · obtain ⟨hzadj, hzn⟩ := hA z hzA
        have hzy : z ≠ y := by intro h; subst h; exact hyA hzA
        rw [Function.update_of_ne hzy] at hzn
        exact ⟨hzadj, hzn⟩

lemma empty_false_lower {n : ℕ} {G : SimpleGraph (Fin n)} {t : ℕ}
    {N : (Fin n → Option Bool) → ℕ} (hN : IsValidN G.Adj t N) :
    ∀ r : ℕ, ∀ ρ : Fin n → Option Bool,
      (trueSet ρ).card + r = t →
      falseSet ρ = ∅ →
      (r + 1) * (r + 2) ≤ 2 * N ρ ∧
      (2 * N ρ = (r + 1) * (r + 2) →
        ∃ (w : Fin r → Fin n), Function.Injective w ∧
          (∀ j : Fin r, ρ (w j) = none) ∧
          ∀ j : Fin r, ∃ A : Finset (Fin n),
            r ≤ j.val + A.card ∧
            ∀ y ∈ A, G.Adj (w j) y ∧ ρ y = none ∧ ∀ i : Fin r, i < j → y ≠ w i) := by
  intro r
  induction r with
  | zero =>
    intro ρ _ _
    have h1 := validN_pos hN ρ
    refine ⟨by omega, fun _ => ⟨Fin.elim0, fun a => Fin.elim0 a, fun a => Fin.elim0 a, fun a => Fin.elim0 a⟩⟩
  | succ r ih =>
    intro ρ hcard hfalse
    have hlt : (trueSet ρ).card < t := by omega
    have hne : ∀ u v : Fin n, G.Adj u v → ¬ (ρ u = some false ∧ ρ v = some false) := by
      intro u v _ ⟨hu, _⟩
      have hu' : u ∈ falseSet ρ := by simp [falseSet, hu]
      rw [hfalse] at hu'; exact absurd hu' (Finset.notMem_empty u)
    have hnl := not_isLeaf_of_lt_true_no_edge hlt hne
    rcases hN ρ with ⟨hl, _⟩ | ⟨w0, hw0, hle⟩
    · exact absurd hl hnl
    · have hw0T : ρ w0 ≠ some true := by rw [hw0]; decide
      have hw0F : ρ w0 ≠ some false := by rw [hw0]; decide
      have hcardF : (trueSet (Function.update ρ w0 (some false))).card + (r + 1) = t := by
        rw [trueSet_update_false ρ w0 hw0T]; exact hcard
      have hfalseF : falseSet (Function.update ρ w0 (some false)) = {w0} := by
        rw [falseSet_update_false, hfalse]; rfl
      obtain ⟨hF_lb, hF_eq⟩ := single_false_lower hN (r + 1) (Function.update ρ w0 (some false)) w0 hcardF hfalseF
      have hcardT : (trueSet (Function.update ρ w0 (some true))).card + r = t := by
        rw [trueSet_update_true_card ρ w0 hw0T]; omega
      have hfalseT : falseSet (Function.update ρ w0 (some true)) = ∅ := by
        rw [falseSet_update_true ρ w0 hw0F]; exact hfalse
      obtain ⟨hT_lb, hT_eq⟩ := ih (Function.update ρ w0 (some true)) hcardT hfalseT
      have hmul : (r + 1 + 1) * (r + 1 + 2) = (r + 1) * (r + 2) + 2 * (r + 2) := by ring
      refine ⟨by omega, fun heq => ?_⟩
      have hF_exact : N (Function.update ρ w0 (some false)) = r + 2 := by omega
      have hT_exact : 2 * N (Function.update ρ w0 (some true)) = (r + 1) * (r + 2) := by omega
      obtain ⟨A0, hA0c, hA0⟩ := hF_eq hF_exact
      obtain ⟨w', hw'_inj, hw'_none, hw'_A⟩ := hT_eq hT_exact
      let w : Fin (r + 1) → Fin n := Fin.cons w0 w'
      have hw_none : ∀ j : Fin (r + 1), ρ (w j) = none := by
        intro j
        refine Fin.cases ?_ ?_ j
        · exact hw0
        · intro k
          have hk := hw'_none k
          have hne0 : w' k ≠ w0 := by
            intro he; rw [he, Function.update_self] at hk; cases hk
          rwa [Function.update_of_ne hne0] at hk
      have hw_inj : Function.Injective w := by
        intro a b hab
        revert hab
        refine Fin.cases ?_ ?_ a
        · refine Fin.cases ?_ ?_ b
          · intro _; rfl
          · intro k hk
            simp only [w, Fin.cons_zero, Fin.cons_succ] at hk
            have hkn := hw'_none k
            rw [← hk, Function.update_self] at hkn; cases hkn
        · intro j
          refine Fin.cases ?_ ?_ b
          · intro hk
            simp only [w, Fin.cons_zero, Fin.cons_succ] at hk
            have hjn := hw'_none j
            rw [hk, Function.update_self] at hjn; cases hjn
          · intro k hk
            simp only [w, Fin.cons_succ] at hk
            exact congrArg Fin.succ (hw'_inj hk)
      refine ⟨w, hw_inj, hw_none, ?_⟩
      intro j
      refine Fin.cases ?_ ?_ j
      · refine ⟨A0, by simp [hA0c], ?_⟩
        intro y hy
        obtain ⟨hyadj, hyn⟩ := hA0 y hy
        have hyne : y ≠ w0 := (G.ne_of_adj hyadj).symm
        rw [Function.update_of_ne hyne] at hyn
        exact ⟨hyadj, hyn, fun i hi => absurd hi (Fin.not_lt_zero i)⟩
      · intro k
        obtain ⟨Ak, hAkc, hAk⟩ := hw'_A k
        refine ⟨Ak, by simp only [Fin.val_succ]; omega, ?_⟩
        intro y hy
        obtain ⟨hyadj, hyn, hyprev⟩ := hAk y hy
        have hyne0 : y ≠ w0 := by
          intro he; rw [he, Function.update_self] at hyn; cases hyn
        rw [Function.update_of_ne hyne0] at hyn
        refine ⟨hyadj, hyn, ?_⟩
        intro i hi
        revert hi
        refine Fin.cases ?_ ?_ i
        · intro _; exact hyne0
        · intro i' hi'
          exact hyprev i' (Fin.succ_lt_succ_iff.mp hi')

def chainFalse {n : ℕ} : List (Fin n) → DT n
  | [] => .leaf
  | y :: ys => .branch y .leaf (chainFalse ys)

lemma chainFalse_leaves {n : ℕ} (L : List (Fin n)) :
    (chainFalse L).leaves = L.length + 1 := by
  induction L with
  | nil => rfl
  | cons y ys ih => simp [chainFalse, DT.leaves, ih]; omega

lemma chainFalse_valid {n : ℕ} {G : SimpleGraph (Fin n)} {t : ℕ} (w : Fin n) :
    ∀ (L : List (Fin n)) (ρ : Fin n → Option Bool),
      L.Nodup →
      ρ w = some false →
      (∀ y ∈ L, G.Adj w y ∧ ρ y = none) →
      (trueSet ρ).card + L.length = t →
      (chainFalse L).Valid G.Adj t ρ := by
  intro L
  induction L with
  | nil =>
    intro ρ _ _ _ hcard
    simp only [List.length_nil, add_zero] at hcard
    exact Or.inr ⟨trueSet ρ, hcard, fun x hx => (Finset.mem_filter.mp hx).2⟩
  | cons y ys ih =>
    intro ρ hnd hw hL hcard
    rw [List.nodup_cons] at hnd
    obtain ⟨hyys, hnd'⟩ := hnd
    obtain ⟨hyadj, hyn⟩ := hL y (List.mem_cons_self ..)
    have hyw : w ≠ y := G.ne_of_adj hyadj
    constructor
    · refine Or.inl ⟨w, y, hyadj, ?_, ?_⟩
      · rw [Function.update_of_ne hyw]; exact hw
      · rw [Function.update_self]
    · apply ih (Function.update ρ y (some true)) hnd'
      · rw [Function.update_of_ne hyw]; exact hw
      · intro z hz
        obtain ⟨hzadj, hzn⟩ := hL z (List.mem_cons_of_mem y hz)
        have hzy : z ≠ y := fun h => hyys (h ▸ hz)
        exact ⟨hzadj, by rw [Function.update_of_ne hzy]; exact hzn⟩
      · have hyT : ρ y ≠ some true := by rw [hyn]; decide
        rw [trueSet_update_true_card ρ y hyT]
        simp only [List.length_cons] at hcard
        omega

lemma lower_eq_build {n t : ℕ} (G : SimpleGraph (Fin n))
    (w : Fin t → Fin n) (hw_inj : Function.Injective w)
    (hA : ∀ j : Fin t, ∃ A : Finset (Fin n), t ≤ j.val + A.card ∧
      ∀ y ∈ A, G.Adj (w j) y ∧ ∀ i : Fin t, i < j → y ≠ w i) :
    ∃ T : DT n, T.Valid G.Adj t (fun _ => none) ∧ 2 * T.leaves = (t + 1) * (t + 2) := by
  suffices h : ∀ r : ℕ, ∀ (hr : r ≤ t),
      ∃ T : DT n,
        T.Valid G.Adj t (fun x => if ∃ i : Fin t, i.val < t - r ∧ w i = x then some true else none) ∧
        2 * T.leaves = (r + 1) * (r + 2) by
    obtain ⟨T, hTv, hTl⟩ := h t le_rfl
    have heq : (fun x : Fin n => if ∃ i : Fin t, i.val < t - t ∧ w i = x then some true else none) =
        (fun _ => none) := by
      funext x; simp
    rw [heq] at hTv
    exact ⟨T, hTv, hTl⟩
  intro r
  induction r with
  | zero =>
    intro _
    refine ⟨.leaf, ?_, by simp [DT.leaves]⟩
    refine Or.inr ⟨Finset.univ.image w, ?_, ?_⟩
    · rw [Finset.card_image_of_injective _ hw_inj, Finset.card_fin]
    · intro x hx
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx
      simp
  | succ r ih =>
    intro hr
    let j : Fin t := ⟨t - (r + 1), by omega⟩
    let ρ : Fin n → Option Bool :=
      fun x => if ∃ i : Fin t, i.val < t - (r + 1) ∧ w i = x then some true else none
    obtain ⟨T', hT'v, hT'l⟩ := ih (by omega)
    obtain ⟨A, hAc, hAprop⟩ := hA j
    let L : List (Fin n) := A.toList.take (r + 1)
    have hLlen : L.length = r + 1 := by
      rw [List.length_take, Finset.length_toList]
      have : r + 1 ≤ A.card := by
        change t ≤ (t - (r + 1)) + A.card at hAc
        omega
      omega
    have hLnd : L.Nodup := (Finset.nodup_toList A).sublist (List.take_sublist _ _)
    have htrue_card : (trueSet ρ).card = t - (r + 1) := by
      have hset : trueSet ρ = (Finset.univ.filter (fun i : Fin t => i.val < t - (r + 1))).image w := by
        ext x
        simp only [trueSet, ρ, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
        constructor
        · intro hx
          split_ifs at hx with h
          exact h
        · rintro ⟨i, hi, rfl⟩
          exact ite_eq_left_iff.mpr (fun h => absurd ⟨i, hi, rfl⟩ h)
      rw [hset, Finset.card_image_of_injective _ hw_inj]
      have hfilt : (Finset.univ.filter (fun i : Fin t => i.val < t - (r + 1))).card = t - (r + 1) := by
        let f : Fin (t - (r + 1)) → Fin t := fun k => ⟨k.val, by omega⟩
        have hfim : Finset.univ.filter (fun i : Fin t => i.val < t - (r + 1)) = Finset.univ.image f := by
          ext i
          simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
          constructor
          · intro hi; exact ⟨⟨i.val, hi⟩, rfl⟩
          · rintro ⟨k, rfl⟩; exact k.isLt
        rw [hfim, Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa [f] using congrArg Fin.val h)),
          Finset.card_fin]
      exact hfilt
    have hρwj : ρ (w j) = none := by
      simp only [ρ]
      rw [ite_eq_right_iff]
      rintro ⟨i, hi, hwi⟩
      have hij : i = j := hw_inj hwi
      subst hij
      dsimp only [j] at hi
      omega
    have hT_eq : Function.update ρ (w j) (some true) =
        (fun x => if ∃ i : Fin t, i.val < t - r ∧ w i = x then some true else none) := by
      funext x
      by_cases hxw : x = w j
      · subst hxw
        rw [Function.update_self, if_pos ⟨j, by show t - (r + 1) < t - r; omega, rfl⟩]
      · rw [Function.update_of_ne hxw]
        simp only [ρ]
        by_cases h1 : ∃ i : Fin t, i.val < t - (r + 1) ∧ w i = x
        · obtain ⟨i, hi, hwi⟩ := h1
          rw [if_pos ⟨i, hi, hwi⟩, if_pos ⟨i, by omega, hwi⟩]
        · rw [if_neg h1, if_neg]
          rintro ⟨i, hi, hwi⟩
          by_cases hij : i.val = t - (r + 1)
          · have : i = j := Fin.ext hij
            subst this; exact hxw hwi.symm
          · exact h1 ⟨i, by omega, hwi⟩
    have hCF : (chainFalse L).Valid G.Adj t (Function.update ρ (w j) (some false)) := by
      apply chainFalse_valid (w j) L (Function.update ρ (w j) (some false)) hLnd
      · rw [Function.update_self]
      · intro y hy
        have hyA : y ∈ A := Finset.mem_toList.mp (List.mem_of_mem_take hy)
        obtain ⟨hyadj, hyprev⟩ := hAprop y hyA
        have hyne : y ≠ w j := (G.ne_of_adj hyadj).symm
        refine ⟨hyadj, ?_⟩
        rw [Function.update_of_ne hyne]
        simp only [ρ]
        rw [if_neg]
        rintro ⟨i, hi, hwi⟩
        exact hyprev i (show i < j from hi) hwi.symm
      · have hwT : ρ (w j) ≠ some true := by rw [hρwj]; decide
        rw [trueSet_update_false ρ (w j) hwT, htrue_card, hLlen]
        omega
    refine ⟨DT.branch (w j) (chainFalse L) T', ⟨hCF, ?_⟩, ?_⟩
    · rw [hT_eq]; exact hT'v
    · simp only [DT.leaves, chainFalse_leaves, hLlen]
      have : (r + 1 + 1) * (r + 1 + 2) = (r + 1) * (r + 2) + 2 * (r + 2) := by ring
      omega

lemma upper_tree {n t : ℕ} (G : SimpleGraph (Fin n))
    (hmin : ∀ R : Finset (Fin n), (∀ p q : Fin n, G.Adj p q → p ∈ R ∨ q ∈ R) → t ≤ R.card) :
    ∀ r : ℕ, ∀ ρ : Fin n → Option Bool,
      (trueSet ρ).card + r = t →
      ∃ T : DT n, T.Valid G.Adj t ρ ∧ T.leaves + 1 ≤ 2 ^ (r + 1) := by
  intro r
  induction r with
  | zero =>
    intro ρ hcard
    simp only [add_zero] at hcard
    refine ⟨.leaf, Or.inr ⟨trueSet ρ, hcard, fun x hx => (Finset.mem_filter.mp hx).2⟩, by simp [DT.leaves]⟩
  | succ r ih =>
    intro ρ hcard
    have hnotvc : ¬ (∀ p q : Fin n, G.Adj p q → p ∈ trueSet ρ ∨ q ∈ trueSet ρ) := by
      intro hvc
      have hc := hmin (trueSet ρ) hvc
      omega
    push Not at hnotvc
    obtain ⟨u, v, huv, hu, hv⟩ := hnotvc
    have hne : u ≠ v := G.ne_of_adj huv
    have huT : ρ u ≠ some true := by intro h; exact hu (by simp [trueSet, h])
    have hvT : ρ v ≠ some true := by intro h; exact hv (by simp [trueSet, h])
    have hcard_u : (trueSet (Function.update ρ u (some true))).card + r = t := by
      rw [trueSet_update_true_card ρ u huT]; omega
    obtain ⟨Tu, hTuv, hTul⟩ := ih (Function.update ρ u (some true)) hcard_u
    have hvT' : Function.update ρ u (some false) v ≠ some true := by
      rw [Function.update_of_ne hne.symm]; exact hvT
    have hcard_v : (trueSet (Function.update (Function.update ρ u (some false)) v (some true))).card + r = t := by
      rw [trueSet_update_true_card _ v hvT', trueSet_update_false ρ u huT]; omega
    obtain ⟨Tv, hTvv, hTvl⟩ := ih (Function.update (Function.update ρ u (some false)) v (some true)) hcard_v
    refine ⟨.branch u (.branch v .leaf Tv) Tu, ⟨⟨?_, hTvv⟩, hTuv⟩, ?_⟩
    · refine Or.inl ⟨u, v, huv, ?_, ?_⟩
      · rw [Function.update_of_ne hne, Function.update_self]
      · rw [Function.update_self]
    · simp only [DT.leaves]
      have hpow : 2 ^ (r + 1 + 1) = 2 ^ (r + 1) + 2 ^ (r + 1) := by ring
      omega

lemma strict_upper_of_not_star_not_matching {n t : ℕ} (G : SimpleGraph (Fin n))
    (hmin : ∀ R : Finset (Fin n), (∀ p q : Fin n, G.Adj p q → p ∈ R ∨ q ∈ R) → t ≤ R.card)
    (ht2 : 2 ≤ t)
    (hnm : ¬ ∀ a b d : Fin n, G.Adj a b → G.Adj a d → b = d) :
    ∃ T : DT n, T.Valid G.Adj t (fun _ => none) ∧ T.leaves + 1 < 2 ^ (t + 1) := by
  push Not at hnm
  obtain ⟨a, b, d, hab, had, hbd⟩ := hnm
  have hba : b ≠ a := (G.ne_of_adj hab).symm
  have hda : d ≠ a := (G.ne_of_adj had).symm
  let ρ0 : Fin n → Option Bool := fun _ => none
  have hcard_a : (trueSet (Function.update ρ0 a (some true))).card + (t - 1) = t := by
    rw [trueSet_update_true_card ρ0 a (by simp [ρ0])]
    have : (trueSet ρ0).card = 0 := by simp [trueSet, ρ0]
    omega
  obtain ⟨Ta, hTav, hTal⟩ := upper_tree G hmin (t - 1) (Function.update ρ0 a (some true)) hcard_a
  let ρ_ab := Function.update (Function.update ρ0 a (some false)) b (some true)
  let ρ_abd := Function.update ρ_ab d (some true)
  have hcard_abd : (trueSet ρ_abd).card + (t - 2) = t := by
    have hd_ne : ρ_ab d ≠ some true := by
      simp [ρ_ab, Function.update_of_ne hbd.symm, Function.update_of_ne hda, ρ0]
    have hb_ne : Function.update ρ0 a (some false) b ≠ some true := by
      simp [Function.update_of_ne hba, ρ0]
    rw [trueSet_update_true_card ρ_ab d hd_ne,
        trueSet_update_true_card (Function.update ρ0 a (some false)) b hb_ne,
        trueSet_update_false ρ0 a (by simp [ρ0])]
    have : (trueSet ρ0).card = 0 := by simp [trueSet, ρ0]
    omega
  obtain ⟨Tabd, hTabdv, hTabdl⟩ := upper_tree G hmin (t - 2) ρ_abd hcard_abd
  refine ⟨.branch a (.branch b .leaf (.branch d .leaf Tabd)) Ta, ⟨⟨?_, ⟨?_, hTabdv⟩⟩, hTav⟩, ?_⟩
  · refine Or.inl ⟨a, b, hab, ?_, ?_⟩
    · rw [Function.update_of_ne hba.symm, Function.update_self]
    · rw [Function.update_self]
  · refine Or.inl ⟨a, d, had, ?_, ?_⟩
    · rw [Function.update_of_ne hda.symm]
      simp only [Function.update_of_ne hba.symm, Function.update_self]
    · rw [Function.update_self]
  · simp only [DT.leaves]
    have hpow1 : 2 ^ (t + 1) = 2 * 2 ^ t := by ring
    have hpow2 : 2 ^ t = 2 * 2 ^ (t - 1) := by
      cases t with
      | zero => omega
      | succ k => simp [pow_succ]; ring
    have ht1 : t - 1 + 1 = t := by omega
    have ht2' : t - 2 + 1 = t - 1 := by omega
    rw [ht1] at hTal
    rw [ht2'] at hTabdl
    have h2ge : 2 ≤ 2 ^ (t - 1) := by
      have : 1 ≤ t - 1 := by omega
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (t - 1) := Nat.pow_le_pow_right (by norm_num) this
    omega

def matchPot (b r : ℕ) : ℕ :=
  if b < r then 2 ^ (r - b + 1) - 1 + b else r + 1

lemma matchPot_pos (b r : ℕ) : 1 ≤ matchPot b r := by
  unfold matchPot
  split_ifs with h
  · have : 1 ≤ 2 ^ (r - b + 1) := Nat.one_le_pow _ _ (by norm_num)
    have : 2 ≤ 2 ^ (r - b + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (r - b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · omega

lemma matchPot_step_false_nbr (b r : ℕ) (hb : 1 ≤ b) (hr : 1 ≤ r) :
    matchPot b r ≤ 1 + matchPot (b - 1) (r - 1) := by
  unfold matchPot
  split_ifs with h1 h2
  · have heq : r - 1 - (b - 1) + 1 = r - b + 1 := by omega
    rw [heq]
    have h2le : 2 ≤ 2 ^ (r - b + 1) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (r - b + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · omega
  · omega
  · omega

lemma matchPot_step_none_nbr (b r : ℕ) (hr : 1 ≤ r) :
    matchPot b r ≤ matchPot b (r - 1) + matchPot (b + 1) r := by
  unfold matchPot
  split_ifs with h1 h2 h3
  · have heq1 : r - 1 - b + 1 = r - b := by omega
    have heq2 : r - (b + 1) + 1 = r - b := by omega
    have hpow : 2 ^ (r - b + 1) = 2 ^ (r - b) + 2 ^ (r - b) := by ring
    rw [heq1, heq2, hpow]
    have : 1 ≤ 2 ^ (r - b) := Nat.one_le_pow _ _ (by norm_num)
    omega
  · omega
  · omega
  · have : r - b = 1 := by omega
    rw [this]
    norm_num
    omega
  · omega
  · omega
  · omega
  · omega

noncomputable def halfFalseSet {n : ℕ} (G : SimpleGraph (Fin n)) (ρ : Fin n → Option Bool) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun v : Fin n => ρ v = none ∧ ∃ u : Fin n, G.Adj u v ∧ ρ u = some false)

lemma matching_lower {n t : ℕ} {G : SimpleGraph (Fin n)}
    (hmatch : ∀ a b d : Fin n, G.Adj a b → G.Adj a d → b = d)
    {N : (Fin n → Option Bool) → ℕ} (hN : IsValidN G.Adj t N) :
    ∀ ρ : Fin n → Option Bool,
      (∀ u v : Fin n, G.Adj u v → ¬ (ρ u = some false ∧ ρ v = some false)) →
      matchPot (halfFalseSet G ρ).card (t - (trueSet ρ).card) ≤ N ρ := by
  intro ρ
  induction hk : noneCount ρ using Nat.strong_induction_on generalizing ρ with
  | ind k ih =>
    intro hne
    by_cases hr : t ≤ (trueSet ρ).card
    · have hzero : t - (trueSet ρ).card = 0 := by omega
      rw [hzero]
      have h1 : matchPot (halfFalseSet G ρ).card 0 = 1 := by simp [matchPot]
      rw [h1]
      exact validN_pos hN ρ
    · have hlt : (trueSet ρ).card < t := by omega
      have hnl := not_isLeaf_of_lt_true_no_edge hlt hne
      rcases hN ρ with ⟨hl, _⟩ | ⟨y, hy, hle⟩
      · exact absurd hl hnl
      · have hyT : ρ y ≠ some true := by rw [hy]; decide
        have hyF : ρ y ≠ some false := by rw [hy]; decide
        have hltF := noneCount_update_lt ρ y false hy
        have hltT := noneCount_update_lt ρ y true hy
        rw [hk] at hltF hltT
        have hneT : ∀ u v : Fin n, G.Adj u v →
            ¬ (Function.update ρ y (some true) u = some false ∧
               Function.update ρ y (some true) v = some false) := by
          intro u v huv ⟨hu, hv⟩
          have huy : u ≠ y := by intro h; subst h; rw [Function.update_self] at hu; cases hu
          have hvy : v ≠ y := by intro h; subst h; rw [Function.update_self] at hv; cases hv
          rw [Function.update_of_ne huy] at hu
          rw [Function.update_of_ne hvy] at hv
          exact hne u v huv ⟨hu, hv⟩
        have hT_ih := ih _ hltT (Function.update ρ y (some true)) rfl hneT
        rw [trueSet_update_true_card ρ y hyT] at hT_ih
        have hr_eq : t - ((trueSet ρ).card + 1) = (t - (trueSet ρ).card) - 1 := by omega
        rw [hr_eq] at hT_ih
        by_cases hfn : ∃ u : Fin n, G.Adj u y ∧ ρ u = some false
        · obtain ⟨u, huy, huf⟩ := hfn
          have hyin : y ∈ halfFalseSet G ρ := by
            simp only [halfFalseSet, Finset.mem_filter, Finset.mem_univ, true_and]
            exact ⟨hy, u, huy, huf⟩
          have hsetT : halfFalseSet G (Function.update ρ y (some true)) =
              (halfFalseSet G ρ).erase y := by
            ext v
            simp only [halfFalseSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
            constructor
            · rintro ⟨hv, w, hwv, hwf⟩
              have hvy : v ≠ y := by intro h; subst h; rw [Function.update_self] at hv; cases hv
              have hwy : w ≠ y := by intro h; subst h; rw [Function.update_self] at hwf; cases hwf
              rw [Function.update_of_ne hvy] at hv
              rw [Function.update_of_ne hwy] at hwf
              exact ⟨hvy, hv, w, hwv, hwf⟩
            · rintro ⟨hvy, hv, w, hwv, hwf⟩
              have hwy : w ≠ y := by intro h; subst h; rw [hy] at hwf; cases hwf
              exact ⟨by rw [Function.update_of_ne hvy]; exact hv, w, hwv,
                     by rw [Function.update_of_ne hwy]; exact hwf⟩
          rw [hsetT, Finset.card_erase_of_mem hyin] at hT_ih
          have hb1 : 1 ≤ (halfFalseSet G ρ).card := Finset.card_pos.mpr ⟨y, hyin⟩
          have hf1 := validN_pos hN (Function.update ρ y (some false))
          have hstep := matchPot_step_false_nbr (halfFalseSet G ρ).card (t - (trueSet ρ).card) hb1 (by omega)
          omega
        · have hneF : ∀ u v : Fin n, G.Adj u v →
              ¬ (Function.update ρ y (some false) u = some false ∧
                 Function.update ρ y (some false) v = some false) := by
            intro u v huv ⟨hu, hv⟩
            by_cases huy : u = y
            · subst huy
              have hvy : v ≠ u := (G.ne_of_adj huv).symm
              rw [Function.update_of_ne hvy] at hv
              exact hfn ⟨v, huv.symm, hv⟩
            · by_cases hvy : v = y
              · subst hvy
                rw [Function.update_of_ne huy] at hu
                exact hfn ⟨u, huv, hu⟩
              · rw [Function.update_of_ne huy] at hu
                rw [Function.update_of_ne hvy] at hv
                exact hne u v huv ⟨hu, hv⟩
          have hF_ih := ih _ hltF (Function.update ρ y (some false)) rfl hneF
          rw [trueSet_update_false ρ y hyT] at hF_ih
          have hsetT : halfFalseSet G (Function.update ρ y (some true)) = halfFalseSet G ρ := by
            ext v
            simp only [halfFalseSet, Finset.mem_filter, Finset.mem_univ, true_and]
            constructor
            · rintro ⟨hv, w, hwv, hwf⟩
              have hvy : v ≠ y := by intro h; subst h; rw [Function.update_self] at hv; cases hv
              have hwy : w ≠ y := by intro h; subst h; rw [Function.update_self] at hwf; cases hwf
              rw [Function.update_of_ne hvy] at hv
              rw [Function.update_of_ne hwy] at hwf
              exact ⟨hv, w, hwv, hwf⟩
            · rintro ⟨hv, w, hwv, hwf⟩
              have hvy : v ≠ y := by intro h; subst h; exact hfn ⟨w, hwv, hwf⟩
              have hwy : w ≠ y := by intro h; subst h; rw [hy] at hwf; cases hwf
              exact ⟨by rw [Function.update_of_ne hvy]; exact hv, w, hwv,
                     by rw [Function.update_of_ne hwy]; exact hwf⟩
          rw [hsetT] at hT_ih
          by_cases hnn : ∃ u : Fin n, G.Adj y u ∧ ρ u = none
          · obtain ⟨u, hyu, hun⟩ := hnn
            have huy : u ≠ y := (G.ne_of_adj hyu).symm
            have hunot : u ∉ halfFalseSet G ρ := by
              intro huin
              simp only [halfFalseSet, Finset.mem_filter, Finset.mem_univ, true_and] at huin
              obtain ⟨_, w, hwu, hwf⟩ := huin
              have hwy : w = y := hmatch u w y hwu.symm hyu.symm
              subst hwy; rw [hy] at hwf; cases hwf
            have hsetF : halfFalseSet G (Function.update ρ y (some false)) =
                insert u (halfFalseSet G ρ) := by
              ext v
              simp only [halfFalseSet, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
              constructor
              · rintro ⟨hv, w, hwv, hwf⟩
                have hvy : v ≠ y := by intro h; subst h; rw [Function.update_self] at hv; cases hv
                rw [Function.update_of_ne hvy] at hv
                by_cases hwy : w = y
                · subst hwy
                  exact Or.inl (hmatch w v u hwv hyu)
                · rw [Function.update_of_ne hwy] at hwf
                  exact Or.inr ⟨hv, w, hwv, hwf⟩
              · rintro (rfl | ⟨hv, w, hwv, hwf⟩)
                · exact ⟨by rw [Function.update_of_ne huy]; exact hun, y, hyu, Function.update_self ..⟩
                · have hvy : v ≠ y := by intro h; subst h; exact hfn ⟨w, hwv, hwf⟩
                  have hwy : w ≠ y := by intro h; subst h; rw [hy] at hwf; cases hwf
                  exact ⟨by rw [Function.update_of_ne hvy]; exact hv, w, hwv,
                         by rw [Function.update_of_ne hwy]; exact hwf⟩
            rw [hsetF, Finset.card_insert_of_notMem hunot] at hF_ih
            have hstep := matchPot_step_none_nbr (halfFalseSet G ρ).card (t - (trueSet ρ).card) (by omega)
            omega
          · have hsetF : halfFalseSet G (Function.update ρ y (some false)) = halfFalseSet G ρ := by
              ext v
              simp only [halfFalseSet, Finset.mem_filter, Finset.mem_univ, true_and]
              constructor
              · rintro ⟨hv, w, hwv, hwf⟩
                have hvy : v ≠ y := by intro h; subst h; rw [Function.update_self] at hv; cases hv
                rw [Function.update_of_ne hvy] at hv
                by_cases hwy : w = y
                · subst hwy; exact absurd ⟨v, hwv, hv⟩ hnn
                · rw [Function.update_of_ne hwy] at hwf
                  exact ⟨hv, w, hwv, hwf⟩
              · rintro ⟨hv, w, hwv, hwf⟩
                have hvy : v ≠ y := by intro h; subst h; exact hfn ⟨w, hwv, hwf⟩
                have hwy : w ≠ y := by intro h; subst h; rw [hy] at hwf; cases hwf
                exact ⟨by rw [Function.update_of_ne hvy]; exact hv, w, hwv,
                       by rw [Function.update_of_ne hwy]; exact hwf⟩
            rw [hsetF] at hF_ih
            have hpos := matchPot_pos (halfFalseSet G ρ).card (t - (trueSet ρ).card - 1)
            omega

theorem main
    (Tr : (n0 : ℕ) → (Fin n0 → Fin n0 → Prop) → ℕ → ℕ → Prop)
    (hTr : ∀ (n1 : ℕ) (A1 : Fin n1 → Fin n1 → Prop) (t1 k1 : ℕ),
      Tr n1 A1 t1 k1 ↔
        ∃ N1 : (Fin n1 → Option Bool) → ℕ,
          N1 (fun _ : Fin n1 => none) ≤ k1 ∧
          ∀ ρ1 : Fin n1 → Option Bool,
            ((((∃ u1 v1 : Fin n1, A1 u1 v1 ∧ ρ1 u1 = some false ∧ ρ1 v1 = some false) ∨
              ∃ S1 : Finset (Fin n1), S1.card = t1 ∧ ∀ x1 ∈ S1, ρ1 x1 = some true) ∧
              1 ≤ N1 ρ1) ∨
             ∃ y1 : Fin n1, ρ1 y1 = none ∧
               N1 (Function.update ρ1 y1 (some false)) + N1 (Function.update ρ1 y1 (some true)) ≤ N1 ρ1))
    (n2 : ℕ) (G2 : SimpleGraph (Fin n2)) (t2 : ℕ)
    (hedge : ∃ u2 v2 : Fin n2, G2.Adj u2 v2)
    (hvc_ex : ∃ T2 : Finset (Fin n2), T2.card = t2 ∧ ∀ p2 q2 : Fin n2, G2.Adj p2 q2 → p2 ∈ T2 ∨ q2 ∈ T2)
    (hvc_min : ∀ R2 : Finset (Fin n2), (∀ p3 q3 : Fin n2, G2.Adj p3 q3 → p3 ∈ R2 ∨ q3 ∈ R2) → t2 ≤ R2.card) :
    ∃ L2 : ℕ,
      Tr n2 G2.Adj t2 L2 ∧
      (∀ m2 : ℕ, Tr n2 G2.Adj t2 m2 → L2 ≤ m2) ∧
      (t2 + 1) * (t2 + 2) ≤ 2 * L2 ∧
      (2 * L2 = (t2 + 1) * (t2 + 2) ↔
        ∃ w2 : Fin t2 → Fin n2, Function.Injective w2 ∧
          ∀ j2 : Fin t2, ∃ A2 : Finset (Fin n2), t2 ≤ j2.val + A2.card ∧
            ∀ y2 ∈ A2, G2.Adj (w2 j2) y2 ∧ ∀ i2 : Fin t2, i2 < j2 → y2 ≠ w2 i2) ∧
      L2 + 1 ≤ 2 ^ (t2 + 1) ∧
      (L2 + 1 = 2 ^ (t2 + 1) ↔
        (∃ c2 : Fin n2, ∀ a2 b2 : Fin n2, G2.Adj a2 b2 → a2 = c2 ∨ b2 = c2) ∨
        ∀ a3 b3 d3 : Fin n2, G2.Adj a3 b3 → G2.Adj a3 d3 → b3 = d3) := by
  classical
  have hTr_iff : ∀ k, Tr n2 G2.Adj t2 k ↔
      ∃ N : (Fin n2 → Option Bool) → ℕ, N (fun _ => none) ≤ k ∧ IsValidN G2.Adj t2 N :=
    fun k => hTr n2 G2.Adj t2 k
  have ht_pos : 1 ≤ t2 := by
    obtain ⟨u, v, huv⟩ := hedge
    obtain ⟨T2, hTc, hT⟩ := hvc_ex
    rcases hT u v huv with hu | hv
    · have := Finset.card_pos.mpr ⟨u, hu⟩; omega
    · have := Finset.card_pos.mpr ⟨v, hv⟩; omega
  have hcard0 : (trueSet (fun _ : Fin n2 => (none : Option Bool))).card + t2 = t2 := by
    simp [trueSet]
  obtain ⟨Tup, hTupv, hTupl⟩ := upper_tree G2 hvc_min t2 (fun _ => none) hcard0
  obtain ⟨Nup, hNupl, hNupv⟩ := valid_dt_gives_N Tup hTupv
  have hex : ∃ k, Tr n2 G2.Adj t2 k := ⟨Tup.leaves, (hTr_iff _).mpr ⟨Nup, hNupl, hNupv⟩⟩
  let L2 := Nat.find hex
  have hL2_tr : Tr n2 G2.Adj t2 L2 := Nat.find_spec hex
  have hL2_min : ∀ m2, Tr n2 G2.Adj t2 m2 → L2 ≤ m2 := fun m2 hm2 => Nat.find_min' hex hm2
  obtain ⟨N0, hN0le, hN0v⟩ := (hTr_iff L2).mp hL2_tr
  have hN0eq : N0 (fun _ => none) = L2 := by
    have hle' : L2 ≤ N0 (fun _ => none) := hL2_min _ ((hTr_iff _).mpr ⟨N0, le_rfl, hN0v⟩)
    omega
  have hfalse0 : falseSet (fun _ : Fin n2 => (none : Option Bool)) = ∅ := by simp [falseSet]
  obtain ⟨hlb_N0, hlb_eq_N0⟩ := empty_false_lower hN0v t2 (fun _ => none) hcard0 hfalse0
  have hlb : (t2 + 1) * (t2 + 2) ≤ 2 * L2 := by omega
  have hub : L2 + 1 ≤ 2 ^ (t2 + 1) := by
    have hle := hL2_min Tup.leaves ((hTr_iff _).mpr ⟨Nup, hNupl, hNupv⟩)
    omega
  refine ⟨L2, hL2_tr, hL2_min, hlb, ?_, hub, ?_⟩
  · constructor
    · intro heq
      obtain ⟨w, hwinj, _, hwA⟩ := hlb_eq_N0 (by omega)
      refine ⟨w, hwinj, fun j => ?_⟩
      obtain ⟨A, hAc, hA⟩ := hwA j
      exact ⟨A, hAc, fun y hy => ⟨(hA y hy).1, (hA y hy).2.2⟩⟩
    · rintro ⟨w, hwinj, hwA⟩
      obtain ⟨Tlo, hTlov, hTlol⟩ := lower_eq_build G2 w hwinj hwA
      obtain ⟨Nlo, hNlol, hNlov⟩ := valid_dt_gives_N Tlo hTlov
      have hle := hL2_min Tlo.leaves ((hTr_iff _).mpr ⟨Nlo, hNlol, hNlov⟩)
      omega
  · constructor
    · intro heq
      by_contra hneither
      push Not at hneither
      obtain ⟨hnstar, hnmatch⟩ := hneither
      have ht2 : 2 ≤ t2 := by
        by_contra hlt2
        have ht1 : t2 = 1 := by omega
        obtain ⟨T2, hTc, hT⟩ := hvc_ex
        rw [ht1, Finset.card_eq_one] at hTc
        obtain ⟨c, rfl⟩ := hTc
        obtain ⟨a2, b2, hab, ha, hb⟩ := hnstar c
        rcases hT a2 b2 hab with h | h
        · exact ha (Finset.mem_singleton.mp h)
        · exact hb (Finset.mem_singleton.mp h)
      obtain ⟨a3, b3, d3, hab, had, hbd⟩ := hnmatch
      have hnm' : ¬ ∀ a b d : Fin n2, G2.Adj a b → G2.Adj a d → b = d :=
        fun h => hbd (h a3 b3 d3 hab had)
      obtain ⟨Tst, hTstv, hTstl⟩ := strict_upper_of_not_star_not_matching G2 hvc_min ht2 hnm'
      obtain ⟨Nst, hNstl, hNstv⟩ := valid_dt_gives_N Tst hTstv
      have hle := hL2_min Tst.leaves ((hTr_iff _).mpr ⟨Nst, hNstl, hNstv⟩)
      omega
    · rintro (⟨c, hc⟩ | hmatch)
      · have ht1 : t2 = 1 := by
          have hle1 : t2 ≤ ({c} : Finset (Fin n2)).card := by
            apply hvc_min {c}
            intro p q hpq
            simpa using hc p q hpq
          simp only [Finset.card_singleton] at hle1
          omega
        rw [ht1] at hlb hub ⊢
        omega
      · have hne0 : ∀ u v : Fin n2, G2.Adj u v →
            ¬ ((fun _ : Fin n2 => (none : Option Bool)) u = some false ∧
               (fun _ : Fin n2 => (none : Option Bool)) v = some false) := by
          intro u v _ ⟨hu, _⟩; cases hu
        have hml := matching_lower hmatch hN0v (fun _ => none) hne0
        have hhf0 : (halfFalseSet G2 (fun _ : Fin n2 => (none : Option Bool))).card = 0 := by
          simp [halfFalseSet]
        have hts0 : (trueSet (fun _ : Fin n2 => (none : Option Bool))).card = 0 := by
          simp [trueSet]
        rw [hhf0, hts0, Nat.sub_zero] at hml
        have hmp : matchPot 0 t2 = 2 ^ (t2 + 1) - 1 := by
          unfold matchPot
          simp [show 0 < t2 by omega]
        rw [hmp, hN0eq] at hml
        have hpow_pos : 1 ≤ 2 ^ (t2 + 1) := Nat.one_le_pow _ _ (by norm_num)
        omega

end PEqualNP.Outside.L_pcx_109

theorem PEqualNP.Outside.L_pcx_109 :
    ∀ Tr : (n0 : ℕ) → (Fin n0 → Fin n0 → Prop) → ℕ → ℕ → Prop, (∀ (n1 : ℕ) (A1 : Fin n1 → Fin n1 → Prop) (t1 k1 : ℕ), Tr n1 A1 t1 k1 ↔ ∃ N1 : (Fin n1 → Option Bool) → ℕ, N1 (fun w1 : Fin n1 => none) ≤ k1 ∧ ∀ ρ1 : Fin n1 → Option Bool, ((((∃ u1 v1 : Fin n1, A1 u1 v1 ∧ ρ1 u1 = some false ∧ ρ1 v1 = some false) ∨ ∃ S1 : Finset (Fin n1), S1.card = t1 ∧ ∀ x1 ∈ S1, ρ1 x1 = some true) ∧ 1 ≤ N1 ρ1) ∨ ∃ y1 : Fin n1, ρ1 y1 = none ∧ N1 (Function.update ρ1 y1 (some false)) + N1 (Function.update ρ1 y1 (some true)) ≤ N1 ρ1)) → ∀ (n2 : ℕ) (G2 : SimpleGraph (Fin n2)) (t2 : ℕ), (∃ u2 v2 : Fin n2, G2.Adj u2 v2) → (∃ T2 : Finset (Fin n2), T2.card = t2 ∧ ∀ p2 q2 : Fin n2, G2.Adj p2 q2 → p2 ∈ T2 ∨ q2 ∈ T2) → (∀ R2 : Finset (Fin n2), (∀ p3 q3 : Fin n2, G2.Adj p3 q3 → p3 ∈ R2 ∨ q3 ∈ R2) → t2 ≤ R2.card) → ∃ L2 : ℕ, Tr n2 G2.Adj t2 L2 ∧ (∀ m2 : ℕ, Tr n2 G2.Adj t2 m2 → L2 ≤ m2) ∧ (t2 + 1) * (t2 + 2) ≤ 2 * L2 ∧ (2 * L2 = (t2 + 1) * (t2 + 2) ↔ ∃ w2 : Fin t2 → Fin n2, Function.Injective w2 ∧ ∀ j2 : Fin t2, ∃ A2 : Finset (Fin n2), t2 ≤ j2.val + A2.card ∧ ∀ y2 ∈ A2, G2.Adj (w2 j2) y2 ∧ ∀ i2 : Fin t2, i2 < j2 → y2 ≠ w2 i2) ∧ L2 + 1 ≤ 2 ^ (t2 + 1) ∧ (L2 + 1 = 2 ^ (t2 + 1) ↔ (∃ c2 : Fin n2, ∀ a2 b2 : Fin n2, G2.Adj a2 b2 → a2 = c2 ∨ b2 = c2) ∨ ∀ a3 b3 d3 : Fin n2, G2.Adj a3 b3 → G2.Adj a3 d3 → b3 = d3) :=
  PEqualNP.Outside.L_pcx_109.main
