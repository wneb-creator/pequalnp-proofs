import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_162

open PEqualNP.ProofComplexity

abbrev Row := Fin 5
abbrev Hole := Fin 4
abbrev V := Row × Hole
abbrev C := Clause V
abbrev LiteralSat (a : V → Bool) (l : Literal V) : Prop := a l.1 = l.2

def rowAx (i : Row) (J : Finset Hole) : C := J.image (fun j => ((i, j), true))

def colAx (i k : Row) (j : Hole) : C := {((i, j), false), ((k, j), false)}

theorem colAx_comm (i k : Row) (j : Hole) : colAx i k j = colAx k i j :=
  Finset.pair_comm ((i, j), false) ((k, j), false)

def Collision (I : Finset Row) (J : Finset Hole) (N : C) : Prop :=
  ∃ i ∈ I, ∃ k ∈ I, ∃ j ∈ J, i ≠ k ∧ N = colAx i k j

abbrev Coll (N : C) : Prop := Collision Finset.univ Finset.univ N

def SatOn (a : V → Bool) (A : Finset C) : Prop :=
  ∀ R ∈ A, R ∈ PHP 5 4 → ClauseSat a R

def Absorbs (π : List C) (A : Finset C) : Prop :=
  ∀ a : V → Bool, SatOn a A → ∀ R ∈ π, ClauseSat a R

theorem satResolve {a : V → Bool} {P N R : C} {v : V}
    (hR : R = P.erase (v, true) ∪ N.erase (v, false))
    (hP : ClauseSat a P) (hN : ClauseSat a N) : ClauseSat a R := by
  obtain ⟨p, hp, hpa⟩ := hP
  by_cases h : p = (v, true)
  · subst p
    obtain ⟨n, hn, hna⟩ := hN
    have hn' : n ≠ (v, false) := by
      intro e
      subst n
      change a v = false at hna
      change a v = true at hpa
      simp [hpa] at hna
    refine ⟨n, ?_, hna⟩
    rw [hR]
    exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hn', hn⟩)
  · refine ⟨p, ?_, hpa⟩
    rw [hR]
    exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨h, hp⟩)

theorem collisionNoPos {N : C} (hN : Coll N) (v : V) : (v, true) ∉ N := by
  obtain ⟨i, _, k, _, j, _, _, rfl⟩ := hN
  simp [colAx]

theorem collisionOther {N : C} {v : V} (hN : Coll N) (hv : (v, false) ∈ N) :
    ∃ u : V, u ≠ v ∧ (u, false) ∈ N := by
  obtain ⟨i, _, k, _, j, _, hik, rfl⟩ := hN
  have hv' : v = (i, j) ∨ v = (k, j) := by simpa [colAx] using hv
  rcases hv' with rfl | rfl
  · exact ⟨(k, j), fun e => hik (congrArg Prod.fst e).symm, by simp [colAx]⟩
  · exact ⟨(i, j), fun e => hik (congrArg Prod.fst e), by simp [colAx]⟩

theorem collisionNonempty {N : C} (hN : Coll N) : N ≠ ∅ := by
  obtain ⟨i, _, k, _, j, _, _, rfl⟩ := hN
  simp [colAx]

theorem col_same_hole {N : C} {v u : V} (hN : Coll N)
    (hv : (v, false) ∈ N) (hu : (u, false) ∈ N) : v.2 = u.2 := by
  obtain ⟨i, _, k, _, j, _, _, rfl⟩ := hN
  have hv' : v = (i, j) ∨ v = (k, j) := by simpa [colAx] using hv
  have hu' : u = (i, j) ∨ u = (k, j) := by simpa [colAx] using hu
  rcases hv' with rfl | rfl <;> rcases hu' with rfl | rfl <;> rfl

theorem col_eq_colAx {N : C} {v u : V} (hN : Coll N)
    (hv : (v, false) ∈ N) (hu : (u, false) ∈ N) (huv : u ≠ v) :
    v.1 ≠ u.1 ∧ v.2 = u.2 ∧ N = colAx v.1 u.1 u.2 := by
  obtain ⟨i, _, k, _, j, _, hik, rfl⟩ := hN
  have hv' : v = (i, j) ∨ v = (k, j) := by simpa [colAx] using hv
  have hu' : u = (i, j) ∨ u = (k, j) := by simpa [colAx] using hu
  rcases hv' with rfl | rfl <;> rcases hu' with rfl | rfl
  · exact (huv rfl).elim
  · exact ⟨hik, rfl, rfl⟩
  · exact ⟨hik.symm, rfl, colAx_comm i k j⟩
  · exact (huv rfl).elim

theorem negLeft {v : V} {P N R : C}
    (hR : R = P.erase (v, true) ∪ N.erase (v, false)) {u : V} (hu : (u, false) ∈ P) :
    (u, false) ∈ R := by
  rw [hR]
  exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by simp, hu⟩)

theorem negRight {v : V} {P N R : C}
    (hR : R = P.erase (v, true) ∪ N.erase (v, false)) {u : V} (hu : (u, false) ∈ N)
    (hne : u ≠ v) : (u, false) ∈ R := by
  rw [hR]
  exact Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by simpa using hne, hu⟩)

theorem collisionPHP {B : C} (hB : Coll B) : B ∈ PHP 5 4 := by
  obtain ⟨i, _, k, _, j, _, hik, rfl⟩ := hB
  exact Or.inr ⟨i, k, j, hik, rfl⟩

theorem emptyUnsat (a : V → Bool) : ¬ ClauseSat a (∅ : C) := by
  rintro ⟨l, hl, _⟩
  simp at hl

theorem indispensablePHP {B : C} : B ∈ PHP 5 4 ↔
    (∃ r : Row, B = rowAx r Finset.univ) ∨ Collision Finset.univ Finset.univ B := by
  change ((∃ r : Row, B = rowAx r Finset.univ) ∨
    (∃ i k : Row, ∃ j : Hole, i ≠ k ∧ B = colAx i k j)) ↔ _
  constructor
  · rintro (hr | ⟨i, k, j, hik, he⟩)
    · exact Or.inl hr
    · exact Or.inr ⟨i, Finset.mem_univ _, k, Finset.mem_univ _, j, Finset.mem_univ _, hik, he⟩
  · rintro (hr | ⟨i, _, k, _, j, _, hik, he⟩)
    · exact Or.inl hr
    · exact Or.inr ⟨i, k, j, hik, he⟩

theorem indispensableSatRow {a : V → Bool} {J : Finset Hole} {r : Row} {j : Hole}
    (hj : j ∈ J) (h : a (r, j) = true) : ClauseSat a (rowAx r J) :=
  ⟨((r, j), true), Finset.mem_image.mpr ⟨j, hj, rfl⟩, h⟩

theorem indispensableSatCol {a : V → Bool} {r s : Row} {j : Hole}
    (h : ¬ (a (r, j) = true ∧ a (s, j) = true)) : ClauseSat a (colAx r s j) := by
  by_cases hr : a (r, j) = true
  · by_cases hs : a (s, j) = true
    · exact (h ⟨hr, hs⟩).elim
    · exact ⟨((s, j), false), by simp [colAx], Bool.eq_false_iff.mpr hs⟩
  · exact ⟨((r, j), false), by simp [colAx], Bool.eq_false_iff.mpr hr⟩

def ValidMatch (i k : Row) (j : Hole) (f : Row → Hole) : Prop :=
  (∀ r, r ≠ i → r ≠ k → f r ≠ j) ∧
  (∀ r₁ r₂, r₁ ≠ i → r₁ ≠ k → r₂ ≠ i → r₂ ≠ k → f r₁ = f r₂ → r₁ = r₂)

def validMatchB (i k : Row) (j : Hole) (f : Row → Hole) : Bool :=
  ((List.finRange 5).all fun r => decide (r = i) || decide (r = k) || decide (f r ≠ j)) &&
  ((List.finRange 5).all fun r₁ => (List.finRange 5).all fun r₂ =>
    decide (r₁ = i) || decide (r₁ = k) || decide (r₂ = i) || decide (r₂ = k) ||
    decide (f r₁ ≠ f r₂) || decide (r₁ = r₂))

theorem validMatch_of_bool {i k : Row} {j : Hole} {f : Row → Hole}
    (h : validMatchB i k j f = true) : ValidMatch i k j f := by
  unfold validMatchB at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_true_left,
    Bool.or_eq_true, decide_eq_true_eq] at h
  refine ⟨?_, ?_⟩
  · intro r hri hrk
    rcases h.1 r with (h1 | h2) | h3
    · exact (hri h1).elim
    · exact (hrk h2).elim
    · exact h3
  · intro r₁ r₂ h1i h1k h2i h2k heq
    rcases h.2 r₁ r₂ with (((((h1 | h2) | h3) | h4) | h5) | h6)
    · exact (h1i h1).elim
    · exact (h1k h2).elim
    · exact (h2i h3).elim
    · exact (h2k h4).elim
    · exact (h5 heq).elim
    · exact h6

def colModel (i k : Row) (j : Hole) (f : Row → Hole) : V → Bool :=
  fun w => if w.1 = i ∨ w.1 = k then decide (w.2 = j) else decide (f w.1 = w.2)

theorem colModel_unsat {i k : Row} {j : Hole} {f : Row → Hole} :
    ¬ ClauseSat (colModel i k j f) (colAx i k j) := by
  rintro ⟨l, hl, hal⟩
  simp only [colAx, Finset.mem_insert, Finset.mem_singleton] at hl
  rcases hl with rfl | rfl <;> simp [colModel] at hal

theorem colModel_sat_other {i k : Row} {j : Hole} {f : Row → Hole}
    (hf : ValidMatch i k j f) :
    ∀ D ∈ PHP 5 4, D ≠ colAx i k j → ClauseSat (colModel i k j f) D := by
  intro D hD hne
  rcases indispensablePHP.mp hD with ⟨r, rfl⟩ | ⟨r, _, s, _, q, _, hrs, rfl⟩
  · by_cases h : r = i ∨ r = k
    · exact indispensableSatRow (Finset.mem_univ j) (by simp [colModel, h])
    · exact indispensableSatRow (Finset.mem_univ (f r)) (by simp [colModel, h])
  · apply indispensableSatCol
    rintro ⟨hr, hs⟩
    by_cases hri : r = i ∨ r = k <;> by_cases hsi : s = i ∨ s = k
    · simp only [colModel, hri, hsi, ↓reduceIte, decide_eq_true_eq] at hr hs
      subst hr
      apply hne
      rcases hri with hri' | hri' <;> rcases hsi with hsi' | hsi'
      · exact (hrs (hri'.trans hsi'.symm)).elim
      · rw [hri', hsi']
      · rw [hri', hsi']; exact colAx_comm k i q
      · exact (hrs (hri'.trans hsi'.symm)).elim
    · simp only [colModel, hri, hsi, ↓reduceIte, decide_eq_true_eq] at hr hs
      push Not at hsi
      exact hf.1 s hsi.1 hsi.2 (hs.trans hr)
    · simp only [colModel, hri, hsi, ↓reduceIte, decide_eq_true_eq] at hr hs
      push Not at hri
      exact hf.1 r hri.1 hri.2 (hr.trans hs)
    · simp only [colModel, hri, hsi, ↓reduceIte, decide_eq_true_eq] at hr hs
      push Not at hri hsi
      exact hrs (hf.2 r s hri.1 hri.2 hsi.1 hsi.2 (hr.trans hs.symm))

theorem colModel_sat_rows {i k : Row} {j : Hole} {f : Row → Hole}
    (_hf : ValidMatch i k j f) :
    ∀ D ∈ PHP 5 4, ¬ Coll D → ClauseSat (colModel i k j f) D := by
  intro D hD hnc
  rcases indispensablePHP.mp hD with ⟨r, rfl⟩ | hc
  · by_cases h : r = i ∨ r = k
    · exact indispensableSatRow (Finset.mem_univ j) (by simp [colModel, h])
    · exact indispensableSatRow (Finset.mem_univ (f r)) (by simp [colModel, h])
  · exact (hnc hc).elim

theorem colModel_sat_cols {i k : Row} {j : Hole} {f : Row → Hole}
    (hf : ValidMatch i k j f) :
    ∀ D, Coll D → D ≠ colAx i k j → ClauseSat (colModel i k j f) D :=
  fun D hD hne => colModel_sat_other hf D (collisionPHP hD) hne

theorem exists_validMatch (i k : Row) (hik : i ≠ k) (j : Hole) :
    ∃ f : Row → Hole, ValidMatch i k j f := by
  have hkm : k ∈ (Finset.univ : Finset Row).erase i :=
    Finset.mem_erase.mpr ⟨Ne.symm hik, Finset.mem_univ _⟩
  have hc : (((Finset.univ : Finset Row).erase i).erase k).card =
      ((Finset.univ : Finset Hole).erase j).card := by
    rw [Finset.card_erase_of_mem hkm, Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_erase_of_mem (Finset.mem_univ j)]; decide +kernel
  let e : ↥(((Finset.univ : Finset Row).erase i).erase k) ≃
      ↥((Finset.univ : Finset Hole).erase j) :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using hc)
  refine ⟨fun r => if hr : r ∈ ((Finset.univ : Finset Row).erase i).erase k
      then (e ⟨r, hr⟩).1 else 0, ?_, ?_⟩
  · intro r hri hrk
    have hr : r ∈ ((Finset.univ : Finset Row).erase i).erase k :=
      Finset.mem_erase.mpr ⟨hrk, Finset.mem_erase.mpr ⟨hri, Finset.mem_univ _⟩⟩
    simp only [hr, ↓reduceDIte]
    exact (Finset.mem_erase.mp (e ⟨r, hr⟩).2).1
  · intro r₁ r₂ hr₁i hr₁k hr₂i hr₂k heq
    have hr₁ : r₁ ∈ ((Finset.univ : Finset Row).erase i).erase k :=
      Finset.mem_erase.mpr ⟨hr₁k, Finset.mem_erase.mpr ⟨hr₁i, Finset.mem_univ _⟩⟩
    have hr₂ : r₂ ∈ ((Finset.univ : Finset Row).erase i).erase k :=
      Finset.mem_erase.mpr ⟨hr₂k, Finset.mem_erase.mpr ⟨hr₂i, Finset.mem_univ _⟩⟩
    simp only [hr₁, hr₂, ↓reduceDIte] at heq
    exact congrArg Subtype.val (e.injective (Subtype.ext heq))

theorem exists_validMatch_map (i k r₀ : Row) (hik : i ≠ k) (hri : r₀ ≠ i) (hrk : r₀ ≠ k)
    (j q₀ : Hole) (hqj : q₀ ≠ j) :
    ∃ f : Row → Hole, ValidMatch i k j f ∧ f r₀ = q₀ := by
  let A : Finset Row := (((Finset.univ : Finset Row).erase i).erase k).erase r₀
  let B : Finset Hole := ((Finset.univ : Finset Hole).erase j).erase q₀
  have hkm : k ∈ (Finset.univ : Finset Row).erase i :=
    Finset.mem_erase.mpr ⟨Ne.symm hik, Finset.mem_univ _⟩
  have hrm : r₀ ∈ ((Finset.univ : Finset Row).erase i).erase k :=
    Finset.mem_erase.mpr ⟨hrk, Finset.mem_erase.mpr ⟨hri, Finset.mem_univ _⟩⟩
  have hqm : q₀ ∈ (Finset.univ : Finset Hole).erase j :=
    Finset.mem_erase.mpr ⟨hqj, Finset.mem_univ _⟩
  have hc : A.card = B.card := by
    dsimp only [A, B]
    rw [Finset.card_erase_of_mem hrm, Finset.card_erase_of_mem hkm,
      Finset.card_erase_of_mem (Finset.mem_univ i),
      Finset.card_erase_of_mem hqm, Finset.card_erase_of_mem (Finset.mem_univ j)]
    decide +kernel
  let e : ↥A ≃ ↥B := Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using hc)
  let f : Row → Hole := fun r =>
    if r = r₀ then q₀ else if hr : r ∈ A then (e ⟨r, hr⟩).1 else 0
  refine ⟨f, ⟨?_, ?_⟩, by simp [f]⟩
  · intro r hri' hrk'
    by_cases hr0 : r = r₀
    · simp [f, hr0, hqj]
    · have hrA : r ∈ A := Finset.mem_erase.mpr
        ⟨hr0, Finset.mem_erase.mpr ⟨hrk', Finset.mem_erase.mpr ⟨hri', Finset.mem_univ _⟩⟩⟩
      simp only [f, hr0, hrA, ↓reduceIte, ↓reduceDIte]
      exact (Finset.mem_erase.mp (Finset.mem_erase.mp (e ⟨r, hrA⟩).2).2).1
  · intro r₁ r₂ hr₁i hr₁k hr₂i hr₂k heq
    by_cases h1 : r₁ = r₀ <;> by_cases h2 : r₂ = r₀
    · exact h1.trans h2.symm
    · have hr₂A : r₂ ∈ A := Finset.mem_erase.mpr
        ⟨h2, Finset.mem_erase.mpr ⟨hr₂k, Finset.mem_erase.mpr ⟨hr₂i, Finset.mem_univ _⟩⟩⟩
      simp only [f, h1, h2, hr₂A, ↓reduceIte, ↓reduceDIte] at heq
      exact ((Finset.mem_erase.mp (e ⟨r₂, hr₂A⟩).2).1 heq.symm).elim
    · have hr₁A : r₁ ∈ A := Finset.mem_erase.mpr
        ⟨h1, Finset.mem_erase.mpr ⟨hr₁k, Finset.mem_erase.mpr ⟨hr₁i, Finset.mem_univ _⟩⟩⟩
      simp only [f, h1, h2, hr₁A, ↓reduceIte, ↓reduceDIte] at heq
      exact ((Finset.mem_erase.mp (e ⟨r₁, hr₁A⟩).2).1 heq).elim
    · have hr₁A : r₁ ∈ A := Finset.mem_erase.mpr
        ⟨h1, Finset.mem_erase.mpr ⟨hr₁k, Finset.mem_erase.mpr ⟨hr₁i, Finset.mem_univ _⟩⟩⟩
      have hr₂A : r₂ ∈ A := Finset.mem_erase.mpr
        ⟨h2, Finset.mem_erase.mpr ⟨hr₂k, Finset.mem_erase.mpr ⟨hr₂i, Finset.mem_univ _⟩⟩⟩
      simp only [f, h1, h2, hr₁A, hr₂A, ↓reduceIte, ↓reduceDIte] at heq
      exact congrArg Subtype.val (e.injective (Subtype.ext heq))

theorem exists_validMatch_avoid (i k r₀ : Row) (hik : i ≠ k) (hri : r₀ ≠ i) (hrk : r₀ ≠ k)
    (j q₀ : Hole) : ∃ f : Row → Hole, ValidMatch i k j f ∧ f r₀ ≠ q₀ := by
  have hne : (((Finset.univ : Finset Hole).erase j).erase q₀).Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    have hc : (((Finset.univ : Finset Hole).erase j).erase q₀).card = 0 := by simp [he]
    have h1 : ((Finset.univ : Finset Hole).erase j).card = 3 := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ j)]; decide +kernel
    have h2 : (((Finset.univ : Finset Hole).erase j).erase q₀).card ≥ 2 := by
      have := Finset.card_erase_le (a := q₀) (s := (Finset.univ : Finset Hole).erase j)
      by_cases hqm : q₀ ∈ (Finset.univ : Finset Hole).erase j
      · rw [Finset.card_erase_of_mem hqm, h1]
      · rw [Finset.erase_eq_of_notMem hqm, h1]; omega
    omega
  obtain ⟨q₁, hq₁⟩ := hne
  have hq₁q₀ : q₁ ≠ q₀ := (Finset.mem_erase.mp hq₁).1
  have hq₁j : q₁ ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hq₁).2).1
  obtain ⟨f, hf, hfr⟩ := exists_validMatch_map i k r₀ hik hri hrk j q₁ hq₁j
  exact ⟨f, hf, hfr.symm ▸ hq₁q₀⟩

theorem indispensableRowModel (i : Row) :
    ∃ a : V → Bool, ¬ ClauseSat a (rowAx i Finset.univ) ∧
      ∀ R ∈ PHP 5 4, R ≠ rowAx i Finset.univ → ClauseSat a R := by
  have hc : ((Finset.univ : Finset Row).erase i).card = (Finset.univ : Finset Hole).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i)]; decide +kernel
  let e : ↥((Finset.univ : Finset Row).erase i) ≃ ↥(Finset.univ : Finset Hole) :=
    Fintype.equivOfCardEq (by simpa only [Fintype.card_coe] using hc)
  let a : V → Bool := fun w =>
    if hr : w.1 ∈ (Finset.univ : Finset Row).erase i then decide ((e ⟨w.1, hr⟩ : Hole) = w.2)
    else false
  refine ⟨a, ?_, ?_⟩
  · rintro ⟨l, hl, hal⟩
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hl
    have hnot : i ∉ (Finset.univ : Finset Row).erase i := Finset.notMem_erase i Finset.univ
    simp only [a, hnot, ↓reduceDIte] at hal
    cases hal
  · intro R hR hne
    rcases indispensablePHP.mp hR with ⟨r, rfl⟩ | ⟨r, _, s, _, j, _, hrs, rfl⟩
    · have hri : r ≠ i := fun he => hne (congrArg (fun r => rowAx r Finset.univ) he)
      have hr : r ∈ (Finset.univ : Finset Row).erase i := Finset.mem_erase.mpr ⟨hri, Finset.mem_univ _⟩
      exact indispensableSatRow (Finset.mem_univ (e ⟨r, hr⟩).1) (by simp only [a, hr, ↓reduceDIte, decide_true])
    · apply indispensableSatCol
      rintro ⟨hr, hs⟩
      by_cases hri : r ∈ (Finset.univ : Finset Row).erase i <;>
        by_cases hsi : s ∈ (Finset.univ : Finset Row).erase i
      · simp only [a, hri, hsi, ↓reduceDIte, decide_eq_true_eq] at hr hs
        exact hrs (congrArg Subtype.val (e.injective (Subtype.ext (hr.trans hs.symm))))
      · simp only [a, hsi, ↓reduceDIte] at hs; cases hs
      · simp only [a, hri, ↓reduceDIte] at hr; cases hr
      · simp only [a, hri, ↓reduceDIte] at hr; cases hr

theorem critical {B : C} (hB : B ∈ PHP 5 4) :
    ∃ a : V → Bool, ¬ ClauseSat a B ∧ ∀ D ∈ PHP 5 4, D ≠ B → ClauseSat a D := by
  rcases indispensablePHP.mp hB with ⟨i, rfl⟩ | ⟨i, _, k, _, j, _, hik, rfl⟩
  · exact indispensableRowModel i
  · obtain ⟨f, hf⟩ := exists_validMatch i k hik j
    exact ⟨colModel i k j f, colModel_unsat, colModel_sat_other hf⟩

def holeColBank (j : Hole) : Finset C :=
  ((Finset.univ : Finset (Row × Row)).filter (fun p => p.1 < p.2)).image
    (fun p => colAx p.1 p.2 j)

theorem mem_holeColBank {j : Hole} {B : C} :
    B ∈ holeColBank j ↔ ∃ i k : Row, i ≠ k ∧ B = colAx i k j := by
  unfold holeColBank
  constructor
  · intro hB
    obtain ⟨⟨i, k⟩, hp, he⟩ := Finset.mem_image.mp hB
    exact ⟨i, k, ne_of_lt (Finset.mem_filter.mp hp).2, he.symm⟩
  · rintro ⟨i, k, hik, rfl⟩
    rcases lt_or_gt_of_ne hik with hlt | hgt
    · exact Finset.mem_image.mpr ⟨(i, k), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨(k, i), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩,
        colAx_comm k i j⟩

theorem holeColBank_card (j : Hole) : (holeColBank j).card = 10 := by
  have hinj : Set.InjOn (fun p : Row × Row => colAx p.1 p.2 j)
      (((Finset.univ : Finset (Row × Row)).filter (fun p => p.1 < p.2)) : Set _) := by
    intro ⟨i1, k1⟩ h1 ⟨i2, k2⟩ h2 heq
    dsimp only at heq
    have hlt1 : i1 < k1 := (Finset.mem_filter.mp (Finset.mem_coe.mp h1)).2
    have hlt2 : i2 < k2 := (Finset.mem_filter.mp (Finset.mem_coe.mp h2)).2
    have m1 : ((i1, j), false) ∈ colAx i2 k2 j := heq ▸ by simp [colAx]
    have m2 : ((k1, j), false) ∈ colAx i2 k2 j := heq ▸ by simp [colAx]
    simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at m1 m2
    rcases m1 with rfl | rfl <;> rcases m2 with h3 | h3
    · exact (ne_of_lt hlt1 h3.symm).elim
    · rw [h3]
    · rw [h3] at hlt1; exact (lt_asymm hlt1 hlt2).elim
    · exact (ne_of_lt hlt1 h3.symm).elim
  unfold holeColBank
  rw [Finset.card_image_of_injOn hinj]
  decide +kernel

def collisionBank : Finset C :=
  ((Finset.univ : Finset (Row × Row × Hole)).filter (fun p => p.1 < p.2.1)).image
    (fun p => colAx p.1 p.2.1 p.2.2)

theorem mem_collisionBank (B : C) : B ∈ collisionBank ↔ Coll B := by
  unfold collisionBank
  constructor
  · intro hB
    obtain ⟨⟨i, k, j⟩, hp, he⟩ := Finset.mem_image.mp hB
    exact ⟨i, Finset.mem_univ _, k, Finset.mem_univ _, j, Finset.mem_univ _,
      ne_of_lt (Finset.mem_filter.mp hp).2, he.symm⟩
  · rintro ⟨i, _, k, _, j, _, hik, rfl⟩
    rcases lt_or_gt_of_ne hik with hlt | hgt
    · exact Finset.mem_image.mpr ⟨(i, k, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩, rfl⟩
    · exact Finset.mem_image.mpr ⟨(k, i, j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, hgt⟩,
        colAx_comm k i j⟩

theorem collisionBank_card : collisionBank.card = 40 := by
  have hinj : Set.InjOn (fun p : Row × Row × Hole => colAx p.1 p.2.1 p.2.2)
      (((Finset.univ : Finset (Row × Row × Hole)).filter (fun p => p.1 < p.2.1)) : Set _) := by
    intro ⟨i1, k1, j1⟩ h1 ⟨i2, k2, j2⟩ h2 heq
    dsimp only at heq
    have hlt1 : i1 < k1 := (Finset.mem_filter.mp (Finset.mem_coe.mp h1)).2
    have hlt2 : i2 < k2 := (Finset.mem_filter.mp (Finset.mem_coe.mp h2)).2
    have m1 : ((i1, j1), false) ∈ colAx i2 k2 j2 := heq ▸ by simp [colAx]
    have m2 : ((k1, j1), false) ∈ colAx i2 k2 j2 := heq ▸ by simp [colAx]
    simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at m1 m2
    rcases m1 with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> rcases m2 with ⟨h3, _⟩ | ⟨h3, _⟩
    · exact (ne_of_lt hlt1 h3.symm).elim
    · rw [h3]
    · rw [h3] at hlt1; exact (lt_asymm hlt1 hlt2).elim
    · exact (ne_of_lt hlt1 h3.symm).elim
  unfold collisionBank
  rw [Finset.card_image_of_injOn hinj]
  decide +kernel

def axiomBank : Finset C :=
  (Finset.univ.image (fun r : Row => rowAx r Finset.univ)) ∪ collisionBank

theorem mem_axiomBank (B : C) : B ∈ axiomBank ↔ B ∈ PHP 5 4 := by
  rw [indispensablePHP]
  simp only [axiomBank, Finset.mem_union, mem_collisionBank, Finset.mem_image, Finset.mem_univ,
    true_and]
  constructor
  · rintro (⟨r, he⟩ | h)
    · exact Or.inl ⟨r, he.symm⟩
    · exact Or.inr h
  · rintro (⟨r, he⟩ | h)
    · exact Or.inl ⟨r, he.symm⟩
    · exact Or.inr h

theorem axiomBank_card : axiomBank.card = 45 := by
  have hdisj : Disjoint (Finset.univ.image (fun r : Row => rowAx r Finset.univ)) collisionBank := by
    rw [Finset.disjoint_left]
    intro B hB1 hB2
    obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hB1
    have hc : Coll (rowAx r Finset.univ) := (mem_collisionBank _).mp hB2
    exact collisionNoPos hc (r, 0) (Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩)
  have hrow : (Finset.univ.image (fun r : Row => rowAx r Finset.univ)).card = 5 := by
    have hinj : Function.Injective (fun r : Row => rowAx r Finset.univ) := by
      intro r1 r2 heq
      dsimp only at heq
      have hm : ((r1, (0 : Hole)), true) ∈ rowAx r2 Finset.univ :=
        heq ▸ Finset.mem_image.mpr ⟨0, Finset.mem_univ _, rfl⟩
      obtain ⟨_, _, he⟩ := Finset.mem_image.mp hm
      exact (Prod.mk.inj (Prod.mk.inj he).1).1.symm
    rw [Finset.card_image_of_injective _ hinj]
    decide +kernel
  unfold axiomBank
  rw [Finset.card_union_of_disjoint hdisj, hrow, collisionBank_card]

theorem requiredAxioms {π : List C} {A : Finset C} (hs : Absorbs π A)
    (he : (∅ : C) ∈ π) : axiomBank ⊆ A := by
  classical
  intro B hB
  by_contra hm
  obtain ⟨a, _, hrest⟩ := critical ((mem_axiomBank B).mp hB)
  apply emptyUnsat a (hs a ?_ ∅ he)
  intro D hDA hDP
  exact hrest D hDP (fun e => hm (e ▸ hDA))

inductive Step where
  | ax (R : C)
  | col (N : C) (v u : V) (R : C)
  | non (v : V) (R : C)
  deriving DecidableEq

def clauseOf : Step → C
  | Step.ax R => R
  | Step.col _ _ _ R => R
  | Step.non _ R => R

inductive ValidTrace : List Step → Prop
  | nil : ValidTrace []
  | ax {tr : List Step} {R : C} :
      ValidTrace tr → R ∈ PHP 5 4 → ValidTrace (Step.ax R :: tr)
  | col {tr : List Step} {P N R : C} {v u : V} :
      ValidTrace tr →
      P ∈ tr.map clauseOf → N ∈ tr.map clauseOf →
      Coll N → (v, true) ∈ P → (v, false) ∈ N →
      u ≠ v → (u, false) ∈ N →
      R = P.erase (v, true) ∪ N.erase (v, false) →
      ValidTrace (Step.col N v u R :: tr)
  | non {tr : List Step} {P N R : C} {v : V} :
      ValidTrace tr →
      P ∈ tr.map clauseOf → N ∈ tr.map clauseOf →
      ¬ Coll N → (v, true) ∈ P → (v, false) ∈ N →
      R = P.erase (v, true) ∪ N.erase (v, false) →
      ValidTrace (Step.non v R :: tr)

theorem of_isDerivation {π : List C} (h : IsDerivation (PHP 5 4) π) :
    ∃ tr : List Step, tr.map clauseOf = π ∧ ValidTrace tr := by
  classical
  induction h with
  | nil => exact ⟨[], rfl, ValidTrace.nil⟩
  | @ax π R _ hR ih =>
    obtain ⟨tr, hmap, htr⟩ := ih
    exact ⟨Step.ax R :: tr, by simp [clauseOf, hmap], ValidTrace.ax htr hR⟩
  | @res π P N R _ hP hN hR ih =>
    obtain ⟨tr, hmap, htr⟩ := ih
    obtain ⟨v, hp, hn, heq⟩ := hR
    by_cases hcol : Coll N
    · obtain ⟨u, huv, hu⟩ := collisionOther hcol hn
      exact ⟨Step.col N v u R :: tr, by simp [clauseOf, hmap],
        ValidTrace.col htr (hmap ▸ hP) (hmap ▸ hN) hcol hp hn huv hu heq⟩
    · exact ⟨Step.non v R :: tr, by simp [clauseOf, hmap],
        ValidTrace.non htr (hmap ▸ hP) (hmap ▸ hN) hcol hp hn heq⟩

theorem ValidTrace.tail {s : Step} {tr : List Step} (h : ValidTrace (s :: tr)) : ValidTrace tr := by
  cases h <;> assumption

theorem ValidTrace.drop {tr : List Step} (h : ValidTrace tr) : ∀ k : ℕ, ValidTrace (tr.drop k) := by
  induction tr with
  | nil => intro k; simp [ValidTrace.nil]
  | cons s tl ih =>
    intro k
    cases k with
    | zero => exact h
    | succ k' => exact ih h.tail k'

theorem ValidTrace.col_mem_info {tr : List Step} (h : ValidTrace tr) {N : C} {v u : V} {R : C}
    (hm : Step.col N v u R ∈ tr) :
    Coll N ∧ (v, false) ∈ N ∧ (u, false) ∈ N ∧ u ≠ v ∧ N ∈ holeColBank u.2 := by
  induction h with
  | nil => cases hm
  | ax _ _ ih =>
    rcases List.mem_cons.mp hm with hEq | hm'
    · cases hEq
    · exact ih hm'
  | @col tr' P N' R' v' u' _ _ _ hcol _ hn huv hu _ ih =>
    rcases List.mem_cons.mp hm with hEq | hm'
    · cases hEq
      obtain ⟨hne, hhole, hax⟩ := col_eq_colAx hcol hn hu huv
      exact ⟨hcol, hn, hu, huv, mem_holeColBank.mpr ⟨v.1, u.1, hne, hax⟩⟩
    · exact ih hm'
  | non _ _ _ _ _ _ _ ih =>
    rcases List.mem_cons.mp hm with hEq | hm'
    · cases hEq
    · exact ih hm'

theorem masterControl {tr : List Step} (h : ValidTrace tr)
    (a : V → Bool) (B₀ : C) (T : Finset V)
    (hrows : ∀ D ∈ PHP 5 4, ¬ Coll D → ClauseSat a D)
    (hcols : ∀ D, Coll D → D ≠ B₀ → ClauseSat a D)
    (h1 : ∀ v u R, Step.col B₀ v u R ∈ tr → u ∈ T)
    (h2 : ∀ v R, Step.non v R ∈ tr → v ∈ T → (∀ w ∈ T, (w, false) ∉ R) → ClauseSat a R) :
    ∀ Q ∈ tr.map clauseOf, ¬ Coll Q → (∀ w ∈ T, (w, false) ∉ Q) → ClauseSat a Q := by
  induction h with
  | nil => intro Q hQ; simp at hQ
  | @ax tr R _ hR ih =>
    intro Q hQ hnc hT
    have ih' := ih (fun v u R' hm => h1 v u R' (List.mem_cons_of_mem _ hm))
                   (fun v R' hm => h2 v R' (List.mem_cons_of_mem _ hm))
    rcases List.mem_cons.mp hQ with hEq | hQ
    · rw [hEq] at hnc ⊢; exact hrows R hR hnc
    · exact ih' Q hQ hnc hT
  | @col tr P N R v u _ hP hN hcol hp hn huv hu hR ih =>
    intro Q hQ hnc hT
    have ih' := ih (fun v' u' R' hm => h1 v' u' R' (List.mem_cons_of_mem _ hm))
                   (fun v' R' hm => h2 v' R' (List.mem_cons_of_mem _ hm))
    rcases List.mem_cons.mp hQ with hEq | hQ
    · rw [hEq] at hT ⊢
      have sP : ClauseSat a P :=
        ih' P hP (fun hc => collisionNoPos hc v hp) (fun w hw hwf => hT w hw (negLeft hR hwf))
      have hne : N ≠ B₀ := by
        intro heq
        subst heq
        have huT : u ∈ T := h1 v u R (by simp)
        exact hT u huT (negRight hR hu huv)
      exact satResolve hR sP (hcols N hcol hne)
    · exact ih' Q hQ hnc hT
  | @non tr P N R v _ hP hN hncN hp hn hR ih =>
    intro Q hQ hnc hT
    have ih' := ih (fun v' u' R' hm => h1 v' u' R' (List.mem_cons_of_mem _ hm))
                   (fun v' R' hm => h2 v' R' (List.mem_cons_of_mem _ hm))
    rcases List.mem_cons.mp hQ with hEq | hQ
    · rw [hEq] at hT ⊢
      by_cases hv : v ∈ T
      · exact h2 v R (by simp) hv hT
      · have sP : ClauseSat a P :=
          ih' P hP (fun hc => collisionNoPos hc v hp) (fun w hw hwf => hT w hw (negLeft hR hwf))
        have sN : ClauseSat a N :=
          ih' N hN hncN (fun w hw hwf =>
            hT w hw (negRight hR hwf (fun heq => hv (heq ▸ hw))))
        exact satResolve hR sP sN
    · exact ih' Q hQ hnc hT

def isAxStep : Step → Bool
  | Step.ax _ => true
  | _ => false

def isColHole (j : Hole) : Step → Bool
  | Step.col _ _ u _ => decide (u.2 = j)
  | _ => false

def isNonHole (j : Hole) : Step → Bool
  | Step.non v _ => decide (v.2 = j)
  | _ => false

def isColOf (B : C) : Step → Bool
  | Step.col N _ _ _ => decide (N = B)
  | _ => false

def isNonOf (v₀ : V) : Step → Bool
  | Step.non v _ => decide (v = v₀)
  | _ => false

def colCount (tr : List Step) (B : C) : ℕ := tr.countP (isColOf B)
def nonCount (tr : List Step) (v : V) : ℕ := tr.countP (isNonOf v)

def holeCost (tr : List Step) (j : Hole) : ℕ :=
  tr.countP (isColHole j) + tr.countP (isNonHole j)

theorem length_decomp (tr : List Step) :
    tr.length = tr.countP isAxStep + ∑ j : Hole, holeCost tr j := by
  induction tr with
  | nil => simp [holeCost]
  | cons s tl ih =>
    unfold holeCost at ih ⊢
    simp only [List.length_cons, List.countP_cons]
    cases s with
    | ax R =>
      simp only [isAxStep, isColHole, isNonHole, ↓reduceIte, Bool.false_eq_true, add_zero]
      omega
    | col N v u R =>
      have hax : isAxStep (Step.col N v u R) = false := rfl
      have h1 : ∀ j : Hole,
          (tl.countP (isColHole j) + if isColHole j (Step.col N v u R) = true then 1 else 0) +
            (tl.countP (isNonHole j) + if isNonHole j (Step.col N v u R) = true then 1 else 0) =
          (tl.countP (isColHole j) + tl.countP (isNonHole j)) +
            (if u.2 = j then 1 else 0) := by
        intro j; by_cases h : u.2 = j <;> simp [isColHole, isNonHole, h]; omega
      simp only [hax, Bool.false_eq_true, ↓reduceIte, add_zero]
      simp_rw [h1]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      omega
    | non v R =>
      have hax : isAxStep (Step.non v R) = false := rfl
      have h1 : ∀ j : Hole,
          (tl.countP (isColHole j) + if isColHole j (Step.non v R) = true then 1 else 0) +
            (tl.countP (isNonHole j) + if isNonHole j (Step.non v R) = true then 1 else 0) =
          (tl.countP (isColHole j) + tl.countP (isNonHole j)) +
            (if v.2 = j then 1 else 0) := by
        intro j; by_cases h : v.2 = j <;> simp [isColHole, isNonHole, h]; omega
      simp only [hax, Bool.false_eq_true, ↓reduceIte, add_zero]
      simp_rw [h1]
      rw [Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
      omega

def axFinset : List Step → Finset C
  | [] => ∅
  | Step.ax R :: tl => insert R (axFinset tl)
  | _ :: tl => axFinset tl

theorem axFinset_card_le (tr : List Step) : (axFinset tr).card ≤ tr.countP isAxStep := by
  induction tr with
  | nil => simp [axFinset]
  | cons s tl ih =>
    cases s with
    | ax R =>
      simp only [axFinset, List.countP_cons, isAxStep, ↓reduceIte]
      have := Finset.card_insert_le R (axFinset tl)
      omega
    | col _ _ _ _ => simp only [axFinset, List.countP_cons, isAxStep, Bool.false_eq_true, ↓reduceIte, add_zero]; exact ih
    | non _ _ => simp only [axFinset, List.countP_cons, isAxStep, Bool.false_eq_true, ↓reduceIte, add_zero]; exact ih

theorem absorbs_axFinset {tr : List Step} (h : ValidTrace tr) :
    Absorbs (tr.map clauseOf) (axFinset tr) := by
  induction h with
  | nil => intro a _ Q hQ; simp at hQ
  | @ax tr R _ hR ih =>
    intro a ha Q hQ
    rcases List.mem_cons.mp hQ with hEq | hQ
    · rw [hEq]; exact ha R (Finset.mem_insert_self _ _) hR
    · exact ih a (fun B hB hB' => ha B (Finset.mem_insert_of_mem hB) hB') Q hQ
  | @col tr P N R v u _ hP hN _ _ _ _ _ hR ih =>
    intro a ha Q hQ
    rcases List.mem_cons.mp hQ with rfl | hQ
    · exact satResolve hR (ih a ha P hP) (ih a ha N hN)
    · exact ih a ha Q hQ
  | @non tr P N R v _ hP hN _ _ _ hR ih =>
    intro a ha Q hQ
    rcases List.mem_cons.mp hQ with rfl | hQ
    · exact satResolve hR (ih a ha P hP) (ih a ha N hN)
    · exact ih a ha Q hQ

theorem ax_lower {tr : List Step} (h : ValidTrace tr) (he : (∅ : C) ∈ tr.map clauseOf) :
    45 ≤ tr.countP isAxStep := by
  have hsub := requiredAxioms (absorbs_axFinset h) he
  have h1 := Finset.card_le_card hsub
  rw [axiomBank_card] at h1
  have h2 := axFinset_card_le tr
  omega

theorem sum_colCount_hole {tr : List Step} (h : ValidTrace tr) (j : Hole) :
    ∑ B ∈ holeColBank j, colCount tr B = tr.countP (isColHole j) := by
  induction h with
  | nil => simp [colCount]
  | ax _ _ ih =>
    simp only [colCount, List.countP_cons, isColOf, isColHole, Bool.false_eq_true, ↓reduceIte, add_zero]
    exact ih
  | @col tr' P N R v u htr' _ _ hcol _ hn huv hu _ ih =>
    simp only [colCount] at ih ⊢
    simp only [List.countP_cons]
    rw [Finset.sum_add_distrib, ih]
    have hdelta : (∑ B ∈ holeColBank j, if isColOf B (Step.col N v u R) = true then 1 else 0) =
        (if isColHole j (Step.col N v u R) = true then 1 else 0) := by
      have hmem : N ∈ holeColBank u.2 := by
        obtain ⟨hne, _, hax⟩ := col_eq_colAx hcol hn hu huv
        exact mem_holeColBank.mpr ⟨v.1, u.1, hne, hax⟩
      by_cases hj : u.2 = j
      · subst hj
        have hrh : (if isColHole u.2 (Step.col N v u R) = true then 1 else 0) = 1 := by
          simp [isColHole]
        rw [hrh, Finset.sum_eq_single N]
        · simp [isColOf]
        · intro B _ hBN
          simp [isColOf, hBN.symm]
        · intro hNmem; exact (hNmem hmem).elim
      · have hrh : (if isColHole j (Step.col N v u R) = true then 1 else 0) = 0 := by
          simp [isColHole, hj]
        rw [hrh]
        apply Finset.sum_eq_zero
        intro B hB
        have hne : N ≠ B := by
          intro heq
          subst heq
          obtain ⟨i, k, _, hax⟩ := mem_holeColBank.mp hB
          have hu' : (u, false) ∈ colAx i k j := hax ▸ hu
          simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at hu'
          rcases hu' with h' | h' <;> exact hj (congrArg Prod.snd h')
        simp [isColOf, hne]
    rw [hdelta]
  | non _ _ _ _ _ _ _ ih =>
    simp only [colCount, List.countP_cons, isColOf, isColHole, Bool.false_eq_true, ↓reduceIte, add_zero]
    exact ih

theorem sum_nonCount_hole (tr : List Step) (j : Hole) :
    ∑ k : Row, nonCount tr (k, j) = tr.countP (isNonHole j) := by
  induction tr with
  | nil => simp [nonCount]
  | cons s tl ih =>
    cases s with
    | ax _ => simp only [nonCount, List.countP_cons, isNonOf, isNonHole, Bool.false_eq_true, ↓reduceIte, add_zero]; exact ih
    | col _ _ _ _ => simp only [nonCount, List.countP_cons, isNonOf, isNonHole, Bool.false_eq_true, ↓reduceIte, add_zero]; exact ih
    | non v R =>
      simp only [nonCount] at ih ⊢
      simp only [List.countP_cons]
      rw [Finset.sum_add_distrib, ih]
      congr 1
      by_cases hj : v.2 = j
      · subst hj
        have hrh : (if isNonHole v.2 (Step.non v R) = true then 1 else 0) = 1 := by
          simp [isNonHole]
        rw [hrh, Finset.sum_eq_single v.1]
        · simp [isNonOf]
        · intro k _ hkv
          have hne : v ≠ (k, v.2) := fun h => hkv (congrArg Prod.fst h).symm
          simp [isNonOf, hne]
        · intro hm; exact (hm (Finset.mem_univ _)).elim
      · have hrh : (if isNonHole j (Step.non v R) = true then 1 else 0) = 0 := by
          simp [isNonHole, hj]
        rw [hrh]
        apply Finset.sum_eq_zero
        intro k _
        have hne : v ≠ (k, j) := fun h => hj (congrArg Prod.snd h)
        simp [isNonOf, hne]

theorem getElem_eq_of_fin_eq {α : Type*} {l : List α} {j : ℕ} {hj : j < l.length}
    {i : Fin l.length} (heq : (⟨j, hj⟩ : Fin l.length) = i) : l[j]'hj = l[i] := by
  cases heq; rfl

theorem mem_drop_iff {α : Type*} (l : List α) (k : ℕ) (x : α) :
    x ∈ l.drop k ↔ ∃ i : Fin l.length, k ≤ i.1 ∧ l[i] = x := by
  constructor
  · intro hx
    obtain ⟨j, hjlt, hj⟩ := List.getElem_of_mem hx
    rw [List.length_drop] at hjlt
    have hlt : k + j < l.length := by omega
    refine ⟨⟨k + j, hlt⟩, Nat.le_add_right k j, ?_⟩
    simpa [List.getElem_drop] using hj
  · rintro ⟨i, hki, rfl⟩
    have hlt : i.1 - k < (l.drop k).length := by rw [List.length_drop]; omega
    have hidx : k + (i.1 - k) = i.1 := by omega
    have hget : (l.drop k)[i.1 - k]'hlt = l[i] := by
      simp only [List.getElem_drop, hidx]
      rfl
    rw [← hget]
    exact List.getElem_mem hlt

theorem mem_of_mem_drop {α : Type*} {l : List α} {k : ℕ} {x : α} (h : x ∈ l.drop k) : x ∈ l := by
  obtain ⟨i, _, rfl⟩ := (mem_drop_iff l k x).mp h
  exact List.getElem_mem i.2

theorem countP_eq_one_unique_idx {α : Type*} (l : List α) (p : α → Bool) (h : l.countP p = 1) :
    ∃ i : Fin l.length, p l[i] = true ∧ ∀ j : Fin l.length, p l[j] = true → j = i := by
  induction l with
  | nil => simp at h
  | cons a tl ih =>
    simp only [List.countP_cons] at h
    by_cases ha : p a = true
    · simp only [ha, ↓reduceIte] at h
      have h0 : tl.countP p = 0 := by omega
      refine ⟨⟨0, by simp⟩, ha, ?_⟩
      intro j hj
      cases j using Fin.cases with
      | zero => rfl
      | succ j' =>
        have hm : tl[j'] ∈ tl := List.getElem_mem j'.2
        have hp0 := List.countP_eq_zero.mp h0 tl[j'] hm
        exact (hp0 hj).elim
    · have haf : p a = false := Bool.eq_false_iff.mpr ha
      simp only [haf, Bool.false_eq_true, ↓reduceIte, add_zero] at h
      obtain ⟨i, hi, huniq⟩ := ih h
      refine ⟨i.succ, hi, ?_⟩
      intro j hj
      cases j using Fin.cases with
      | zero => exact (ha hj).elim
      | succ j' => exact congrArg Fin.succ (huniq j' hj)

theorem countP_eq_two_unique_idx {α : Type*} (l : List α) (p : α → Bool) (h : l.countP p = 2) :
    ∃ i₁ i₂ : Fin l.length, i₂.1 < i₁.1 ∧ p l[i₁] = true ∧ p l[i₂] = true ∧
      ∀ j : Fin l.length, p l[j] = true → j = i₁ ∨ j = i₂ := by
  induction l with
  | nil => simp at h
  | cons a tl ih =>
    simp only [List.countP_cons] at h
    by_cases ha : p a = true
    · simp only [ha, ↓reduceIte] at h
      have h1 : tl.countP p = 1 := by omega
      obtain ⟨i, hi, huniq⟩ := countP_eq_one_unique_idx tl p h1
      refine ⟨i.succ, ⟨0, by simp⟩, Nat.zero_lt_succ i.1, hi, ha, ?_⟩
      intro j hj
      cases j using Fin.cases with
      | zero => exact Or.inr rfl
      | succ j' => exact Or.inl (congrArg Fin.succ (huniq j' hj))
    · have haf : p a = false := Bool.eq_false_iff.mpr ha
      simp only [haf, Bool.false_eq_true, ↓reduceIte, add_zero] at h
      obtain ⟨i₁, i₂, hlt, h1, h2, huniq⟩ := ih h
      refine ⟨i₁.succ, i₂.succ, Nat.succ_lt_succ hlt, h1, h2, ?_⟩
      intro j hj
      cases j using Fin.cases with
      | zero => exact (ha hj).elim
      | succ j' =>
        rcases huniq j' hj with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr rfl

theorem countP_pos_of_mem {α : Type*} {l : List α} {p : α → Bool} {x : α}
    (hx : x ∈ l) (hp : p x = true) : 1 ≤ l.countP p := by
  have : 0 < l.countP p := List.countP_pos_iff.mpr ⟨x, hx, hp⟩
  omega

def G1 (tr : List Step) (j : Hole) : Finset C :=
  (holeColBank j).filter (fun B => colCount tr B = 1)

def S (tr : List Step) (j : Hole) : Finset Row :=
  Finset.univ.filter (fun k => 1 ≤ nonCount tr (k, j))

def M1 (tr : List Step) (j : Hole) : Finset Row :=
  Finset.univ.filter (fun k => nonCount tr (k, j) = 1)

def colLeaves (tr : List Step) (B : C) (u₀ : V) : Prop :=
  ∃ v R, Step.col B v u₀ R ∈ tr

noncomputable def inEdges (tr : List Step) (j : Hole) (k : Row) : Finset C := by
  classical
  exact (G1 tr j).filter (fun B => colLeaves tr B (k, j))

noncomputable def Z2 (tr : List Step) (j : Hole) : Finset Row :=
  (M1 tr j).filter (fun k => 2 ≤ (inEdges tr j k).card)

theorem colCount_pos {tr : List Step} (h : ValidTrace tr) (he : (∅ : C) ∈ tr.map clauseOf)
    {j : Hole} {B : C} (hB : B ∈ holeColBank j) : 1 ≤ colCount tr B := by
  obtain ⟨i, k, hik, rfl⟩ := mem_holeColBank.mp hB
  obtain ⟨f, hf⟩ := exists_validMatch i k hik j
  by_contra hlt
  have h0 : colCount tr (colAx i k j) = 0 := by omega
  have hsat := masterControl h (colModel i k j f) (colAx i k j) ∅
    (colModel_sat_rows hf) (colModel_sat_cols hf)
    (fun v u R hm => by
      have hp := countP_pos_of_mem hm (by simp [isColOf] : isColOf (colAx i k j) (Step.col (colAx i k j) v u R) = true)
      change 1 ≤ colCount tr (colAx i k j) at hp
      omega)
    (fun v R _ hv => by simp at hv)
    ∅ he (fun hc => collisionNonempty hc rfl) (fun w hw => by simp at hw)
  exact emptyUnsat _ hsat

theorem exists_col_leaving_in_S {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf) {j : Hole} {B : C} (hB : B ∈ holeColBank j) :
    ∃ k ∈ S tr j, colLeaves tr B (k, j) := by
  obtain ⟨i, k, hik, rfl⟩ := mem_holeColBank.mp hB
  obtain ⟨f, hf⟩ := exists_validMatch i k hik j
  let T : Finset V := Finset.univ.filter (fun w => nonCount tr w = 0)
  by_contra hnone
  push Not at hnone
  have h1 : ∀ v u R, Step.col (colAx i k j) v u R ∈ tr → u ∈ T := by
    intro v u R hm
    have hinfo := h.col_mem_info hm
    have hu_hole : u.2 = j := by
      have hu' : (u, false) ∈ colAx i k j := hinfo.2.2.1
      simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at hu'
      rcases hu' with h' | h' <;> exact congrArg Prod.snd h'
    have hu_eq : u = (u.1, j) := Prod.ext rfl hu_hole
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    by_contra hnz
    have huS : u.1 ∈ S tr j := by
      refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
      rw [← hu_eq]; omega
    exact hnone u.1 huS ⟨v, R, hu_eq ▸ hm⟩
  have h2 : ∀ v R, Step.non v R ∈ tr → v ∈ T → (∀ w ∈ T, (w, false) ∉ R) →
      ClauseSat (colModel i k j f) R := by
    intro v R hm hv _
    have hv0 : nonCount tr v = 0 := (Finset.mem_filter.mp hv).2
    have hp := countP_pos_of_mem hm (by simp [isNonOf] : isNonOf v (Step.non v R) = true)
    change 1 ≤ nonCount tr v at hp
    omega
  have hsat := masterControl h (colModel i k j f) (colAx i k j) T
    (colModel_sat_rows hf) (colModel_sat_cols hf) h1 h2
    ∅ he (fun hc => collisionNonempty hc rfl) (fun w _ hwf => by simp at hwf)
  exact emptyUnsat _ hsat

theorem four_le_S_card {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf) (j : Hole) : 4 ≤ (S tr j).card := by
  have hcompl : ((S tr j)ᶜ).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro k₁ hk₁ k₂ hk₂
    by_contra hne
    have hB : colAx k₁ k₂ j ∈ holeColBank j := mem_holeColBank.mpr ⟨k₁, k₂, hne, rfl⟩
    obtain ⟨k, hkS, v, R, hm⟩ := exists_col_leaving_in_S h he hB
    have hu : ((k, j), false) ∈ colAx k₁ k₂ j := (h.col_mem_info hm).2.2.1
    simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at hu
    rcases hu with ⟨rfl, _⟩ | ⟨rfl, _⟩
    · exact (Finset.mem_compl.mp hk₁) hkS
    · exact (Finset.mem_compl.mp hk₂) hkS
  have hsum := Finset.card_add_card_compl (S tr j)
  have hR : Fintype.card Row = 5 := by decide +kernel
  omega

theorem g1_unique_step {tr : List Step} {j : Hole} {B : C} (hG : B ∈ G1 tr j) :
    ∀ {v₁ u₁ R₁ v₂ u₂ R₂}, Step.col B v₁ u₁ R₁ ∈ tr → Step.col B v₂ u₂ R₂ ∈ tr →
      v₁ = v₂ ∧ u₁ = u₂ ∧ R₁ = R₂ := by
  have h1 : colCount tr B = 1 := (Finset.mem_filter.mp hG).2
  obtain ⟨i, hi, huniq⟩ := countP_eq_one_unique_idx tr (isColOf B) h1
  intro v₁ u₁ R₁ v₂ u₂ R₂ hm₁ hm₂
  obtain ⟨j₁, hj₁lt, hj₁⟩ := List.getElem_of_mem hm₁
  obtain ⟨j₂, hj₂lt, hj₂⟩ := List.getElem_of_mem hm₂
  have e1 : (⟨j₁, hj₁lt⟩ : Fin tr.length) = i := huniq ⟨j₁, hj₁lt⟩ (by simp [hj₁, isColOf])
  have e2 : (⟨j₂, hj₂lt⟩ : Fin tr.length) = i := huniq ⟨j₂, hj₂lt⟩ (by simp [hj₂, isColOf])
  have heq : Step.col B v₁ u₁ R₁ = Step.col B v₂ u₂ R₂ := by
    rw [← hj₁, ← hj₂, getElem_eq_of_fin_eq e1, getElem_eq_of_fin_eq e2]
  cases heq
  exact ⟨rfl, rfl, rfl⟩

theorem inEdges_mem_iff_unique {tr : List Step} {j : Hole} {k : Row} {B : C}
    (hE : B ∈ inEdges tr j k) :
    B ∈ G1 tr j ∧ ∀ v u R, Step.col B v u R ∈ tr → u = (k, j) := by
  classical
  have hG : B ∈ G1 tr j := (Finset.mem_filter.mp hE).1
  obtain ⟨v₀, R₀, hm₀⟩ := (Finset.mem_filter.mp hE).2
  exact ⟨hG, fun v u R hm => (g1_unique_step hG hm hm₀).2.1⟩

theorem inEdges_mem_colAx {tr : List Step} (h : ValidTrace tr) {j : Hole} {k : Row} {B : C}
    (hE : B ∈ inEdges tr j k) :
    ∃ i : Row, i ≠ k ∧ B = colAx i k j := by
  classical
  obtain ⟨v, R, hm⟩ := (Finset.mem_filter.mp hE).2
  obtain ⟨hne, _, hax⟩ := col_eq_colAx (h.col_mem_info hm).1 (h.col_mem_info hm).2.1
    (h.col_mem_info hm).2.2.1 (h.col_mem_info hm).2.2.2.1
  exact ⟨v.1, hne, hax⟩

theorem inEdges_disjoint {tr : List Step} {j : Hole} {k₁ k₂ : Row} (hne : k₁ ≠ k₂) :
    Disjoint (inEdges tr j k₁) (inEdges tr j k₂) := by
  classical
  rw [Finset.disjoint_left]
  intro B h1 h2
  obtain ⟨hG, _⟩ := inEdges_mem_iff_unique h1
  obtain ⟨v₁, R₁, hm₁⟩ := (Finset.mem_filter.mp h1).2
  obtain ⟨v₂, R₂, hm₂⟩ := (Finset.mem_filter.mp h2).2
  have hu := (g1_unique_step hG hm₁ hm₂).2.1
  exact hne (congrArg Prod.fst hu)

theorem biUnion_inEdges_eq_G1 {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf) (j : Hole) :
    (S tr j).biUnion (inEdges tr j) = G1 tr j := by
  classical
  ext B
  simp only [Finset.mem_biUnion]
  constructor
  · rintro ⟨k, _, hE⟩
    exact (Finset.mem_filter.mp hE).1
  · intro hG
    have hB : B ∈ holeColBank j := (Finset.mem_filter.mp hG).1
    obtain ⟨k, hkS, hL⟩ := exists_col_leaving_in_S h he hB
    exact ⟨k, hkS, Finset.mem_filter.mpr ⟨hG, hL⟩⟩

theorem sum_inEdges_card {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf) (j : Hole) :
    ∑ k ∈ S tr j, (inEdges tr j k).card = (G1 tr j).card := by
  rw [← Finset.card_biUnion (fun k₁ _ k₂ _ hne => inEdges_disjoint hne),
    biUnion_inEdges_eq_G1 h he j]

theorem col_hole_lower {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf) (j : Hole) :
    20 ≤ tr.countP (isColHole j) + (G1 tr j).card := by
  rw [← sum_colCount_hole h j]
  have hcard : (G1 tr j).card = ∑ B ∈ holeColBank j, if colCount tr B = 1 then 1 else 0 := by
    unfold G1
    rw [Finset.card_filter]
  rw [hcard, ← Finset.sum_add_distrib]
  have hle : ∑ B ∈ holeColBank j, 2 ≤
      ∑ B ∈ holeColBank j, (colCount tr B + if colCount tr B = 1 then 1 else 0) := by
    apply Finset.sum_le_sum
    intro B hB
    have hpos := colCount_pos h he hB
    by_cases h1 : colCount tr B = 1
    · simp [h1]
    · simp [h1]; omega
  rw [Finset.sum_const, holeColBank_card j] at hle
  simpa using hle

theorem non_hole_lower {tr : List Step} (j : Hole) :
    2 * (S tr j).card ≤ tr.countP (isNonHole j) + (M1 tr j).card := by
  rw [← sum_nonCount_hole tr j]
  have hM : (M1 tr j).card = ∑ k : Row, if k ∈ M1 tr j then 1 else 0 := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul, mul_one]
    congr 1; ext k; simp
  have hS : 2 * (S tr j).card = ∑ k : Row, if k ∈ S tr j then 2 else 0 := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul, mul_comm]
    congr 2; ext k; simp
  rw [hM, hS, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  by_cases hS' : k ∈ S tr j
  · have hpos : 1 ≤ nonCount tr (k, j) := (Finset.mem_filter.mp hS').2
    by_cases hM' : k ∈ M1 tr j
    · have h1 : nonCount tr (k, j) = 1 := (Finset.mem_filter.mp hM').2
      simp [hS', hM', h1]
    · have hne : nonCount tr (k, j) ≠ 1 := fun he => hM' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
      simp [hS', hM']
      omega
  · simp [hS']

theorem non_hole_lower_ge3 {tr : List Step} {j : Hole} {k₀ : Row}
    (hk₀ : 3 ≤ nonCount tr (k₀, j)) :
    2 * (S tr j).card + 1 ≤ tr.countP (isNonHole j) + (M1 tr j).card := by
  rw [← sum_nonCount_hole tr j]
  have hM : (M1 tr j).card = ∑ k : Row, if k ∈ M1 tr j then 1 else 0 := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul, mul_one]
    congr 1; ext k; simp
  have hS : 2 * (S tr j).card = ∑ k : Row, if k ∈ S tr j then 2 else 0 := by
    rw [Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, smul_eq_mul, mul_comm]
    congr 2; ext k; simp
  have h1 : (1 : ℕ) = ∑ k : Row, if k = k₀ then 1 else 0 := by simp
  rw [hM, hS, h1, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro k _
  by_cases heq : k = k₀
  · subst heq
    have hS' : k ∈ S tr j := Finset.mem_filter.mpr ⟨Finset.mem_univ _, by omega⟩
    have hM' : k ∉ M1 tr j := fun hm => by
      have := (Finset.mem_filter.mp hm).2; omega
    simp [hS', hM']
    omega
  · simp only [heq, ↓reduceIte, add_zero]
    by_cases hS' : k ∈ S tr j
    · have hpos : 1 ≤ nonCount tr (k, j) := (Finset.mem_filter.mp hS').2
      by_cases hM' : k ∈ M1 tr j
      · have h1' : nonCount tr (k, j) = 1 := (Finset.mem_filter.mp hM').2
        simp [hS', hM', h1']
      · have hne : nonCount tr (k, j) ≠ 1 := fun he => hM' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩)
        simp [hS', hM']; omega
    · simp [hS']

theorem holeCost_ge_14 {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf) (j : Hole) : 14 ≤ holeCost tr j := by
  have hc := col_hole_lower h he j
  have hn := non_hole_lower (tr := tr) j
  have hS := four_le_S_card h he j
  have hG : (G1 tr j).card ≤ 10 := by
    rw [← holeColBank_card j]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hM : (M1 tr j).card ≤ (S tr j).card :=
    Finset.card_le_card (fun k hk => Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by have := (Finset.mem_filter.mp hk).2; omega⟩)
  unfold holeCost
  omega

def edgesIn (A : Finset Row) (j : Hole) : Finset C :=
  ((A ×ˢ A).filter (fun p => p.1 < p.2)).image (fun p => colAx p.1 p.2 j)

theorem edgesIn_subset_holeColBank (A : Finset Row) (j : Hole) :
    edgesIn A j ⊆ holeColBank j := by
  intro B hB
  obtain ⟨⟨i, k⟩, hp, rfl⟩ := Finset.mem_image.mp hB
  exact mem_holeColBank.mpr ⟨i, k, ne_of_lt (Finset.mem_filter.mp hp).2, rfl⟩

theorem edgesIn_card (A : Finset Row) (j : Hole) :
    (edgesIn A j).card = A.card.choose 2 := by
  have hinj : Set.InjOn (fun p : Row × Row => colAx p.1 p.2 j)
      (((A ×ˢ A).filter (fun p => p.1 < p.2)) : Set _) := by
    intro ⟨i1, k1⟩ h1 ⟨i2, k2⟩ h2 heq
    dsimp only at heq
    have hlt1 : i1 < k1 := (Finset.mem_filter.mp (Finset.mem_coe.mp h1)).2
    have hlt2 : i2 < k2 := (Finset.mem_filter.mp (Finset.mem_coe.mp h2)).2
    have m1 : ((i1, j), false) ∈ colAx i2 k2 j := heq ▸ by simp [colAx]
    have m2 : ((k1, j), false) ∈ colAx i2 k2 j := heq ▸ by simp [colAx]
    simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at m1 m2
    rcases m1 with rfl | rfl <;> rcases m2 with h3 | h3
    · exact (ne_of_lt hlt1 h3.symm).elim
    · rw [h3]
    · rw [h3] at hlt1; exact (lt_asymm hlt1 hlt2).elim
    · exact (ne_of_lt hlt1 h3.symm).elim
  unfold edgesIn
  rw [Finset.card_image_of_injOn hinj]
  have hbij : ((A ×ˢ A).filter (fun p => p.1 < p.2)).card = (A.powersetCard 2).card := by
    refine Finset.card_bij (fun p _ => ({p.1, p.2} : Finset Row)) ?_ ?_ ?_
    · intro ⟨i, k⟩ hp
      have hmem := (Finset.mem_filter.mp hp).1
      have hlt : i < k := (Finset.mem_filter.mp hp).2
      rw [Finset.mem_powersetCard]
      refine ⟨?_, Finset.card_pair (ne_of_lt hlt)⟩
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · exact (Finset.mem_product.mp hmem).1
      · exact (Finset.mem_product.mp hmem).2
    · intro ⟨i1, k1⟩ h1 ⟨i2, k2⟩ h2 heq
      have hlt1 : i1 < k1 := (Finset.mem_filter.mp h1).2
      have hlt2 : i2 < k2 := (Finset.mem_filter.mp h2).2
      have m1 : i1 ∈ ({i2, k2} : Finset Row) := heq ▸ by simp
      have m2 : k1 ∈ ({i2, k2} : Finset Row) := heq ▸ by simp
      simp only [Finset.mem_insert, Finset.mem_singleton] at m1 m2
      rcases m1 with rfl | rfl <;> rcases m2 with h3 | h3
      · exact (ne_of_lt hlt1 h3.symm).elim
      · rw [h3]
      · rw [h3] at hlt1; exact (lt_asymm hlt1 hlt2).elim
      · exact (ne_of_lt hlt1 h3.symm).elim
    · intro s hs
      rw [Finset.mem_powersetCard] at hs
      obtain ⟨a, b, hab, rfl⟩ := Finset.card_eq_two.mp hs.2
      have ha : a ∈ A := hs.1 (by simp)
      have hb : b ∈ A := hs.1 (by simp)
      rcases lt_or_gt_of_ne hab with hlt | hgt
      · exact ⟨(a, b), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, hb⟩, hlt⟩, rfl⟩
      · exact ⟨(b, a), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hb, ha⟩, hgt⟩,
          Finset.pair_comm b a⟩
  rw [hbij, Finset.card_powersetCard]

theorem inEdges_biUnion_subset_sdiff {tr : List Step} (h : ValidTrace tr)
    (j : Hole) (A : Finset Row) :
    A.biUnion (inEdges tr j) ⊆ holeColBank j \ edgesIn Aᶜ j := by
  classical
  intro B hB
  obtain ⟨k, hkA, hE⟩ := Finset.mem_biUnion.mp hB
  have hG : B ∈ G1 tr j := (Finset.mem_filter.mp hE).1
  have hBk : B ∈ holeColBank j := (Finset.mem_filter.mp hG).1
  refine Finset.mem_sdiff.mpr ⟨hBk, ?_⟩
  intro hIn
  obtain ⟨⟨r, s⟩, hrs, rfl⟩ := Finset.mem_image.mp hIn
  have hr : r ∉ A := Finset.mem_compl.mp (Finset.mem_product.mp (Finset.mem_filter.mp hrs).1).1
  have hs : s ∉ A := Finset.mem_compl.mp (Finset.mem_product.mp (Finset.mem_filter.mp hrs).1).2
  obtain ⟨v, R, hm⟩ := (Finset.mem_filter.mp hE).2
  have hu : ((k, j), false) ∈ colAx r s j := (h.col_mem_info hm).2.2.1
  simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at hu
  rcases hu with ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact hr hkA
  · exact hs hkA

theorem sum_inEdges_subset_bound {tr : List Step} (h : ValidTrace tr)
    (j : Hole) (A : Finset Row) :
    ∑ k ∈ A, (inEdges tr j k).card ≤ 10 - (5 - A.card).choose 2 := by
  rw [← Finset.card_biUnion (fun k₁ _ k₂ _ hne => inEdges_disjoint hne)]
  have hsub := Finset.card_le_card (inEdges_biUnion_subset_sdiff h j A)
  have hsdiff := Finset.card_sdiff_add_card_eq_card (edgesIn_subset_holeColBank Aᶜ j)
  rw [holeColBank_card j, edgesIn_card] at hsdiff
  have hc : Aᶜ.card = 5 - A.card := by
    have := Finset.card_add_card_compl A
    have hR : Fintype.card Row = 5 := by decide +kernel
    omega
  rw [hc] at hsdiff
  calc (A.biUnion (inEdges tr j)).card
      ≤ (holeColBank j \ edgesIn Aᶜ j).card := hsub
    _ = 10 - (5 - A.card).choose 2 := by omega

theorem choose2_bound (n : ℕ) (hn : n ≤ 5) :
    n = 0 ∧ n.choose 2 = 0 ∨ n = 1 ∧ n.choose 2 = 0 ∨ n = 2 ∧ n.choose 2 = 1 ∨
    n = 3 ∧ n.choose 2 = 3 ∨ n = 4 ∧ n.choose 2 = 6 ∨ n = 5 ∧ n.choose 2 = 10 := by
  interval_cases n <;> decide +kernel

theorem holeCost_ge_17_of_Z2_empty {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf) {j : Hole} (hZ : Z2 tr j = ∅) :
    17 ≤ holeCost tr j := by
  classical
  have hc := col_hole_lower h he j
  have hn := non_hole_lower (tr := tr) j
  have hS := four_le_S_card h he j
  have hMsub : M1 tr j ⊆ S tr j := fun k hk =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by have := (Finset.mem_filter.mp hk).2; omega⟩
  let F : Finset Row := S tr j \ M1 tr j
  have hcard : F.card + (M1 tr j).card = (S tr j).card := Finset.card_sdiff_add_card_eq_card hMsub
  have hScard5 : (S tr j).card ≤ 5 := by
    have := Finset.card_le_univ (S tr j)
    have hR : Fintype.card Row = 5 := by decide +kernel
    omega
  have hG10 : (G1 tr j).card ≤ 10 := by
    rw [← holeColBank_card j]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  have hGsum : (G1 tr j).card = ∑ k ∈ F, (inEdges tr j k).card + ∑ k ∈ M1 tr j, (inEdges tr j k).card := by
    rw [← sum_inEdges_card h he j, ← Finset.sum_union Finset.sdiff_disjoint,
      Finset.sdiff_union_of_subset hMsub]
  have hMsum : ∑ k ∈ M1 tr j, (inEdges tr j k).card ≤ (M1 tr j).card := by
    calc ∑ k ∈ M1 tr j, (inEdges tr j k).card
        ≤ ∑ _k ∈ M1 tr j, 1 := by
          apply Finset.sum_le_sum
          intro k hkM
          by_contra hgt
          have h2 : 2 ≤ (inEdges tr j k).card := by omega
          have hmem : k ∈ Z2 tr j := Finset.mem_filter.mpr ⟨hkM, h2⟩
          rw [hZ] at hmem; simp at hmem
      _ = (M1 tr j).card := by simp
  have hFsum := sum_inEdges_subset_bound h j F
  have hFc5 : F.card ≤ 5 := by omega
  have hch := choose2_bound (5 - F.card) (by omega)
  unfold holeCost
  rcases hch with ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ <;> omega

theorem holeCost_of_Z2_singleton {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf) {j : Hole} {k₀ : Row} (hZ : Z2 tr j = {k₀}) :
    16 ≤ holeCost tr j ∧
      (holeCost tr j = 16 →
        ∃ b : Row, b ≠ k₀ ∧ nonCount tr (b, j) = 2 ∧
          ∀ i : Row, i ≠ k₀ → i ≠ b → colAx i b j ∈ inEdges tr j b) := by
  classical
  have hc := col_hole_lower h he j
  have hn := non_hole_lower (tr := tr) j
  have hS := four_le_S_card h he j
  have hMsub : M1 tr j ⊆ S tr j := fun k hk =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, by have := (Finset.mem_filter.mp hk).2; omega⟩
  have hk₀M : k₀ ∈ M1 tr j := by
    have : k₀ ∈ Z2 tr j := hZ ▸ Finset.mem_singleton_self k₀
    exact (Finset.mem_filter.mp this).1
  let F : Finset Row := S tr j \ M1 tr j
  have hcard : F.card + (M1 tr j).card = (S tr j).card := Finset.card_sdiff_add_card_eq_card hMsub
  have hScard5 : (S tr j).card ≤ 5 := by
    have := Finset.card_le_univ (S tr j)
    have hR : Fintype.card Row = 5 := by decide +kernel
    omega
  have hMpos : 1 ≤ (M1 tr j).card := Finset.card_pos.mpr ⟨k₀, hk₀M⟩
  have hG10 : (G1 tr j).card ≤ 10 := by
    rw [← holeColBank_card j]
    exact Finset.card_le_card (Finset.filter_subset _ _)
  let F' : Finset Row := insert k₀ F
  let M' : Finset Row := (M1 tr j).erase k₀
  have hk₀F : k₀ ∉ F := fun hm => (Finset.mem_sdiff.mp hm).2 hk₀M
  have hF'card : F'.card = F.card + 1 := Finset.card_insert_of_notMem hk₀F
  have hM'card : M'.card = (M1 tr j).card - 1 := Finset.card_erase_of_mem hk₀M
  have hdisj' : Disjoint F' M' := by
    rw [Finset.disjoint_left]
    intro x hx hx'
    rcases Finset.mem_insert.mp hx with rfl | hxF
    · exact (Finset.mem_erase.mp hx').1 rfl
    · exact (Finset.mem_sdiff.mp hxF).2 (Finset.mem_erase.mp hx').2
  have hunion' : F' ∪ M' = S tr j := by
    ext x
    simp only [F', M', F, Finset.mem_union, Finset.mem_insert, Finset.mem_sdiff, Finset.mem_erase]
    constructor
    · rintro ((rfl | ⟨hxS, _⟩) | ⟨_, hxM⟩)
      · exact hMsub hk₀M
      · exact hxS
      · exact hMsub hxM
    · intro hxS
      by_cases hxM : x ∈ M1 tr j
      · by_cases hxk : x = k₀
        · exact Or.inl (Or.inl hxk)
        · exact Or.inr ⟨hxk, hxM⟩
      · exact Or.inl (Or.inr ⟨hxS, hxM⟩)
  have hGsum' : (G1 tr j).card =
      ∑ k ∈ F', (inEdges tr j k).card + ∑ k ∈ M', (inEdges tr j k).card := by
    rw [← sum_inEdges_card h he j, ← hunion', Finset.sum_union hdisj']
  have hM'le1 : ∀ k ∈ M', (inEdges tr j k).card ≤ 1 := by
    intro k hkM'
    have hkne : k ≠ k₀ := (Finset.mem_erase.mp hkM').1
    have hkM : k ∈ M1 tr j := (Finset.mem_erase.mp hkM').2
    by_contra hgt
    have hmem : k ∈ Z2 tr j := Finset.mem_filter.mpr ⟨hkM, by omega⟩
    rw [hZ, Finset.mem_singleton] at hmem
    exact hkne hmem
  have hM'sum : ∑ k ∈ M', (inEdges tr j k).card ≤ M'.card := by
    calc ∑ k ∈ M', (inEdges tr j k).card
        ≤ ∑ _k ∈ M', 1 := Finset.sum_le_sum (fun k hk => hM'le1 k hk)
      _ = M'.card := by simp
  have hF'sum := sum_inEdges_subset_bound h j F'
  have hF'c5 : F'.card ≤ 5 := by omega
  have hch := choose2_bound (5 - F'.card) (by omega)
  have hge16 : 16 ≤ holeCost tr j := by
    unfold holeCost
    rcases hch with ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ <;> omega
  refine ⟨hge16, ?_⟩
  intro heq16
  have hno_ge3 : ∀ k : Row, nonCount tr (k, j) ≤ 2 := by
    intro k
    by_contra hgt
    have hn3 := non_hole_lower_ge3 (tr := tr) (j := j) (k₀ := k) (by omega)
    unfold holeCost at heq16
    rcases hch with ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ <;> omega
  have hF_cases : F.card = 1 ∨ F.card = 2 := by
    unfold holeCost at heq16
    rcases hch with ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ | ⟨_, h0⟩ <;> omega
  rcases hF_cases with hF1 | hF2
  · obtain ⟨b, hb⟩ := Finset.card_eq_one.mp hF1
    have hbF : b ∈ F := hb ▸ Finset.mem_singleton_self b
    have hbk : b ≠ k₀ := fun heq => hk₀F (heq ▸ hbF)
    have hb2 : nonCount tr (b, j) = 2 := by
      have hpos : 1 ≤ nonCount tr (b, j) := (Finset.mem_filter.mp (Finset.mem_sdiff.mp hbF).1).2
      have hne1 : nonCount tr (b, j) ≠ 1 := fun h1 =>
        (Finset.mem_sdiff.mp hbF).2 (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
      have hle2 := hno_ge3 b
      omega
    have hF'eq : F' = {k₀, b} := by simp [F', hb]
    have hF'sum_eq : ∑ k ∈ F', (inEdges tr j k).card = 7 := by
      have h3 : (5 - F'.card).choose 2 = 3 := by
        rw [hF'card, hF1]; decide +kernel
      rw [h3] at hF'sum
      unfold holeCost at heq16
      omega
    have hbiUnion_eq : F'.biUnion (inEdges tr j) = holeColBank j \ edgesIn F'ᶜ j := by
      apply Finset.eq_of_subset_of_card_le (inEdges_biUnion_subset_sdiff h j F')
      have hsdiff := Finset.card_sdiff_add_card_eq_card (edgesIn_subset_holeColBank F'ᶜ j)
      rw [holeColBank_card j, edgesIn_card] at hsdiff
      have hc' : F'ᶜ.card = 3 := by
        have := Finset.card_add_card_compl F'
        have hR : Fintype.card Row = 5 := by decide +kernel
        omega
      have h3 : (3 : ℕ).choose 2 = 3 := by decide +kernel
      rw [hc', h3] at hsdiff
      rw [Finset.card_biUnion (fun k₁ _ k₂ _ hne => inEdges_disjoint hne), hF'sum_eq]
      omega
    refine ⟨b, hbk, hb2, ?_⟩
    intro i hik hib
    have hBbank : colAx i b j ∈ holeColBank j := mem_holeColBank.mpr ⟨i, b, hib, rfl⟩
    have hBnotIn : colAx i b j ∉ edgesIn F'ᶜ j := by
      intro hIn
      obtain ⟨⟨r, s⟩, hrs, heq⟩ := Finset.mem_image.mp hIn
      have hr : r ∉ F' := Finset.mem_compl.mp (Finset.mem_product.mp (Finset.mem_filter.mp hrs).1).1
      have hs : s ∉ F' := Finset.mem_compl.mp (Finset.mem_product.mp (Finset.mem_filter.mp hrs).1).2
      have hm : ((b, j), false) ∈ colAx r s j := heq ▸ by simp [colAx]
      simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at hm
      have hbF' : b ∈ F' := by rw [hF'eq]; simp
      rcases hm with rfl | rfl
      · exact hr hbF'
      · exact hs hbF'
    have hBmem : colAx i b j ∈ F'.biUnion (inEdges tr j) :=
      hbiUnion_eq ▸ Finset.mem_sdiff.mpr ⟨hBbank, hBnotIn⟩
    obtain ⟨k, hkF', hEk⟩ := Finset.mem_biUnion.mp hBmem
    rw [hF'eq, Finset.mem_insert, Finset.mem_singleton] at hkF'
    rcases hkF' with hkk | hkb
    · subst hkk
      exfalso
      obtain ⟨v, R, hm⟩ := (Finset.mem_filter.mp hEk).2
      have hu : ((k, j), false) ∈ colAx i b j := (h.col_mem_info hm).2.2.1
      simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at hu
      rcases hu with h1 | h1
      · exact hik h1.symm
      · exact hbk h1.symm
    · subst hkb; exact hEk
  ·
    have hM2 : (M1 tr j).card = 2 := by unfold holeCost at heq16; omega
    have hS4 : (S tr j).card = 4 := by omega
    have hG10eq : (G1 tr j).card = 10 := by unfold holeCost at heq16; omega
    have hGeq : G1 tr j = holeColBank j :=
      Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        (by rw [hG10eq, holeColBank_card j])
    have hSc1 : ((S tr j)ᶜ).card = 1 := by
      have := Finset.card_add_card_compl (S tr j)
      have hR : Fintype.card Row = 5 := by decide +kernel
      omega
    obtain ⟨u₀, hu₀eq⟩ := Finset.card_eq_one.mp hSc1
    have hu₀notS : u₀ ∉ S tr j := Finset.mem_compl.mp (hu₀eq ▸ Finset.mem_singleton_self u₀)
    have hM'1 : M'.card = 1 := by omega
    obtain ⟨r₁, hr₁eq⟩ := Finset.card_eq_one.mp hM'1
    have hr₁M' : r₁ ∈ M' := hr₁eq ▸ Finset.mem_singleton_self r₁
    have hr₁k₀ : r₁ ≠ k₀ := (Finset.mem_erase.mp hr₁M').1
    have hr₁S : r₁ ∈ S tr j := hMsub (Finset.mem_erase.mp hr₁M').2
    have hu₀r₁ : u₀ ≠ r₁ := fun heq => hu₀notS (heq ▸ hr₁S)

    have edge_owner : ∀ x y : Row, x ≠ y →
        colAx x y j ∈ inEdges tr j x ∨ colAx x y j ∈ inEdges tr j y := by
      intro x y hxy
      have hG : colAx x y j ∈ G1 tr j := hGeq ▸ mem_holeColBank.mpr ⟨x, y, hxy, rfl⟩
      have hmem : colAx x y j ∈ (S tr j).biUnion (inEdges tr j) :=
        (biUnion_inEdges_eq_G1 h he j).symm ▸ hG
      obtain ⟨k, _, hEk⟩ := Finset.mem_biUnion.mp hmem
      obtain ⟨v, R, hm⟩ := (Finset.mem_filter.mp hEk).2
      have hu : ((k, j), false) ∈ colAx x y j := (h.col_mem_info hm).2.2.1
      simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at hu
      rcases hu with ⟨rfl, _⟩ | ⟨rfl, _⟩
      · exact Or.inl hEk
      · exact Or.inr hEk

    have inEdges_u₀_empty : ∀ B, B ∉ inEdges tr j u₀ := by
      intro B hE
      have hG : B ∈ G1 tr j := (Finset.mem_filter.mp hE).1
      have hmem : B ∈ (S tr j).biUnion (inEdges tr j) := (biUnion_inEdges_eq_G1 h he j).symm ▸ hG
      obtain ⟨k, hkS, hEk⟩ := Finset.mem_biUnion.mp hmem
      have hne : k ≠ u₀ := fun heq => hu₀notS (heq ▸ hkS)
      exact Finset.disjoint_left.mp (inEdges_disjoint hne) hEk hE

    have hr₁_edge : colAx u₀ r₁ j ∈ inEdges tr j r₁ := by
      rcases edge_owner u₀ r₁ hu₀r₁ with h1 | h2
      · exact (inEdges_u₀_empty _ h1).elim
      · exact h2
    have hr₁_only : ∀ B ∈ inEdges tr j r₁, B = colAx u₀ r₁ j := by
      intro B hB
      have hle1 := hM'le1 r₁ hr₁M'
      exact Finset.card_le_one.mp hle1 B hB (colAx u₀ r₁ j) hr₁_edge
    obtain ⟨b₁, b₂, hbne, hFeq⟩ := Finset.card_eq_two.mp hF2
    have hb₁F : b₁ ∈ F := hFeq ▸ by simp
    have hb₂F : b₂ ∈ F := hFeq ▸ by simp
    have hb_props : ∀ b ∈ F, b ≠ k₀ ∧ b ≠ u₀ ∧ b ≠ r₁ ∧ nonCount tr (b, j) = 2 ∧
        colAx u₀ b j ∈ inEdges tr j b ∧ colAx r₁ b j ∈ inEdges tr j b := by
      intro b hbF
      have hbS : b ∈ S tr j := (Finset.mem_sdiff.mp hbF).1
      have hbnotM : b ∉ M1 tr j := (Finset.mem_sdiff.mp hbF).2
      have hbk : b ≠ k₀ := fun heq => hbnotM (heq ▸ hk₀M)
      have hbu : b ≠ u₀ := fun heq => hu₀notS (heq ▸ hbS)
      have hbr : b ≠ r₁ := fun heq => hbnotM (heq ▸ (Finset.mem_erase.mp hr₁M').2)
      have hb2 : nonCount tr (b, j) = 2 := by
        have hpos : 1 ≤ nonCount tr (b, j) := (Finset.mem_filter.mp hbS).2
        have hne1 : nonCount tr (b, j) ≠ 1 := fun h1 =>
          hbnotM (Finset.mem_filter.mpr ⟨Finset.mem_univ _, h1⟩)
        have hle2 := hno_ge3 b
        omega
      have heu : colAx u₀ b j ∈ inEdges tr j b := by
        rcases edge_owner u₀ b hbu.symm with h1 | h2
        · exact (inEdges_u₀_empty _ h1).elim
        · exact h2
      have her : colAx r₁ b j ∈ inEdges tr j b := by
        rcases edge_owner r₁ b hbr.symm with h1 | h2
        · exfalso
          have heq := hr₁_only _ h1
          have hm : ((b, j), false) ∈ colAx u₀ r₁ j := heq ▸ by simp [colAx]
          simp only [colAx, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq, and_true] at hm
          rcases hm with h1' | h1'
          · exact hbu h1'
          · exact hbr h1'
        · exact h2
      exact ⟨hbk, hbu, hbr, hb2, heu, her⟩
    have row_decomp : ∀ i : Row, i = u₀ ∨ i = k₀ ∨ i = r₁ ∨ i = b₁ ∨ i = b₂ := by
      intro i
      by_cases hiS : i ∈ S tr j
      · by_cases hiM : i ∈ M1 tr j
        · by_cases hik : i = k₀
          · exact Or.inr (Or.inl hik)
          · have hiM' : i ∈ M' := Finset.mem_erase.mpr ⟨hik, hiM⟩
            rw [hr₁eq, Finset.mem_singleton] at hiM'
            exact Or.inr (Or.inr (Or.inl hiM'))
        · have hiF : i ∈ F := Finset.mem_sdiff.mpr ⟨hiS, hiM⟩
          rw [hFeq, Finset.mem_insert, Finset.mem_singleton] at hiF
          rcases hiF with rfl | rfl
          · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      · have hic : i ∈ (S tr j)ᶜ := Finset.mem_compl.mpr hiS
        rw [hu₀eq, Finset.mem_singleton] at hic
        exact Or.inl hic
    rcases edge_owner b₁ b₂ hbne with hb12 | hb21
    · obtain ⟨hbk, _, _, hb2, heu, her⟩ := hb_props b₁ hb₁F
      refine ⟨b₁, hbk, hb2, ?_⟩
      intro i hik hib
      rcases row_decomp i with rfl | rfl | rfl | rfl | rfl
      · exact heu
      · exact (hik rfl).elim
      · exact her
      · exact (hib rfl).elim
      · rw [colAx_comm]; exact hb12
    · obtain ⟨hbk, _, _, hb2, heu, her⟩ := hb_props b₂ hb₂F
      refine ⟨b₂, hbk, hb2, ?_⟩
      intro i hik hib
      rcases row_decomp i with rfl | rfl | rfl | rfl | rfl
      · exact heu
      · exact (hik rfl).elim
      · exact her
      · exact hb21
      · exact (hib rfl).elim

theorem z2_unique_non {tr : List Step} {j : Hole} {k : Row} (hk : k ∈ Z2 tr j) :
    ∃ (idx : Fin tr.length) (R : C),
      tr[idx] = Step.non (k, j) R ∧
      ∀ j' : Fin tr.length, isNonOf (k, j) tr[j'] = true → j' = idx := by
  have h1 : nonCount tr (k, j) = 1 := (Finset.mem_filter.mp (Finset.mem_filter.mp hk).1).2
  obtain ⟨idx, hi, huniq⟩ := countP_eq_one_unique_idx tr (isNonOf (k, j)) h1
  cases hstep : tr[idx] with
  | ax _ => simp [hstep, isNonOf] at hi
  | col _ _ _ _ => simp [hstep, isNonOf] at hi
  | non v R =>
    simp only [hstep, isNonOf, decide_eq_true_eq] at hi
    subst hi
    exact ⟨idx, R, hstep, huniq⟩

theorem z2_clause_unsat_edge {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf) {j : Hole} {k : Row}
    {idx : Fin tr.length} {R : C}
    (hstep : tr[idx] = Step.non (k, j) R)
    (huniq : ∀ j' : Fin tr.length, isNonOf (k, j) tr[j'] = true → j' = idx)
    {i : Row} (hi : colAx i k j ∈ inEdges tr j k)
    {f : Row → Hole} (hf : ValidMatch i k j f) :
    ((k, j), false) ∉ R ∧ ¬ ClauseSat (colModel i k j f) R := by
  by_contra hbad
  have h1 : ∀ v u R', Step.col (colAx i k j) v u R' ∈ tr → u ∈ ({(k, j)} : Finset V) := by
    intro v u R' hm
    rw [Finset.mem_singleton]
    exact (inEdges_mem_iff_unique hi).2 v u R' hm
  have h2 : ∀ v R', Step.non v R' ∈ tr → v ∈ ({(k, j)} : Finset V) →
      (∀ w ∈ ({(k, j)} : Finset V), (w, false) ∉ R') → ClauseSat (colModel i k j f) R' := by
    intro v R' hm hv hnotf
    rw [Finset.mem_singleton] at hv
    subst hv
    obtain ⟨j', hj'lt, hj'⟩ := List.getElem_of_mem hm
    have heq : (⟨j', hj'lt⟩ : Fin tr.length) = idx := huniq ⟨j', hj'lt⟩ (by simp [hj', isNonOf])
    have hj'step : tr[idx] = Step.non (k, j) R' := (getElem_eq_of_fin_eq heq).symm.trans hj'
    rw [hstep] at hj'step
    cases hj'step
    have hnot : ((k, j), false) ∉ R := hnotf (k, j) (Finset.mem_singleton_self _)
    by_contra hns
    exact hbad ⟨hnot, hns⟩
  have hsat := masterControl h (colModel i k j f) (colAx i k j) {(k, j)}
    (colModel_sat_rows hf) (colModel_sat_cols hf) h1 h2
    ∅ he (fun hc => collisionNonempty hc rfl) (fun w _ hwf => by simp at hwf)
  exact emptyUnsat _ hsat

theorem z2_clause_shape {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf) {j : Hole} {k : Row} (hk : k ∈ Z2 tr j)
    {idx : Fin tr.length} {R : C}
    (hstep : tr[idx] = Step.non (k, j) R)
    (huniq : ∀ j' : Fin tr.length, isNonOf (k, j) tr[j'] = true → j' = idx) :
    (∀ v : V, (v, false) ∉ R) ∧
    (∀ r : Row, ∀ q : Hole, ((r, q), true) ∈ R → (r = k ∨ q = j) ∧ (r, q) ≠ (k, j)) := by
  have h2card : 2 ≤ (inEdges tr j k).card := (Finset.mem_filter.mp hk).2
  obtain ⟨B₁, hB₁, B₂, hB₂, hBne⟩ := Finset.one_lt_card.mp (by omega : 1 < (inEdges tr j k).card)
  obtain ⟨i₁, hi₁k, rfl⟩ := inEdges_mem_colAx h hB₁
  obtain ⟨i₂, hi₂k, rfl⟩ := inEdges_mem_colAx h hB₂
  have hi₁₂ : i₁ ≠ i₂ := fun heq => hBne (heq ▸ rfl)
  obtain ⟨f₁, hf₁⟩ := exists_validMatch i₁ k hi₁k j
  have hunsat1 := z2_clause_unsat_edge h he hstep huniq hB₁ hf₁
  constructor
  · intro ⟨r, q⟩ hmem
    by_cases hrk : r = k
    · subst hrk
      by_cases hqj : q = j
      · subst hqj; exact hunsat1.1 hmem
      · exact hunsat1.2 ⟨((r, q), false), hmem, by simp [colModel, hqj]⟩
    · have hpick : ∃ i : Row, i ≠ k ∧ i ≠ r ∧ colAx i k j ∈ inEdges tr j k := by
        by_cases h1 : r = i₁
        · exact ⟨i₂, hi₂k, h1 ▸ hi₁₂.symm, hB₂⟩
        · exact ⟨i₁, hi₁k, Ne.symm h1, hB₁⟩
      obtain ⟨i, hik, hir, hiE⟩ := hpick
      obtain ⟨f, hf, hfr⟩ := exists_validMatch_avoid i k r hik hir.symm hrk j q
      have huns := (z2_clause_unsat_edge h he hstep huniq hiE hf).2
      exact huns ⟨((r, q), false), hmem, by simp [colModel, hir.symm, hrk, hfr]⟩
  · intro r q hmem
    refine ⟨?_, ?_⟩
    · by_contra hneither
      push Not at hneither
      obtain ⟨hrk, hqj⟩ := hneither
      have hpick : ∃ i : Row, i ≠ k ∧ i ≠ r ∧ colAx i k j ∈ inEdges tr j k := by
        by_cases h1 : r = i₁
        · exact ⟨i₂, hi₂k, h1 ▸ hi₁₂.symm, hB₂⟩
        · exact ⟨i₁, hi₁k, Ne.symm h1, hB₁⟩
      obtain ⟨i, hik, hir, hiE⟩ := hpick
      obtain ⟨f, hf, hfr⟩ := exists_validMatch_map i k r hik hir.symm hrk j q hqj
      have huns := (z2_clause_unsat_edge h he hstep huniq hiE hf).2
      exact huns ⟨((r, q), true), hmem, by simp [colModel, hir.symm, hrk, hfr]⟩
    · intro heq
      rcases Prod.mk.inj heq with ⟨rfl, rfl⟩
      exact hunsat1.2 ⟨((r, q), true), hmem, by simp [colModel]⟩

theorem z2_not_coll {R : C} (hnoNeg : ∀ v : V, (v, false) ∉ R) : ¬ Coll R := by
  rintro ⟨i, _, k, _, j, _, _, rfl⟩
  exact hnoNeg (i, j) (by simp [colAx])

theorem z2_unsat_colModel {j : Hole} {k : Row} {R : C}
    (hshape : (∀ v : V, (v, false) ∉ R) ∧
      (∀ r : Row, ∀ q : Hole, ((r, q), true) ∈ R → (r = k ∨ q = j) ∧ (r, q) ≠ (k, j)))
    {i' k' : Row} {j' : Hole} {f : Row → Hole} (hf : ValidMatch i' k' j' f)
    (hjj : j' ≠ j) (hi' : i' ≠ k) (hk' : k' ≠ k) (hfk : f k = j) :
    ¬ ClauseSat (colModel i' k' j' f) R := by
  rintro ⟨⟨⟨r, q⟩, pol⟩, hmem, hsat⟩
  cases pol with
  | false => exact hshape.1 (r, q) hmem
  | true =>
    obtain ⟨hor, hne⟩ := hshape.2 r q hmem
    change colModel i' k' j' f (r, q) = true at hsat
    rcases hor with rfl | rfl
    · have hqj : q ≠ j := fun hq => hne (Prod.ext rfl hq)
      simp only [colModel, hi'.symm, hk'.symm, or_self, ↓reduceIte, decide_eq_true_eq, hfk] at hsat
      exact hqj hsat.symm
    · have hrk : r ≠ k := fun hr => hne (Prod.ext hr rfl)
      by_cases hri : r = i' ∨ r = k'
      · simp only [colModel, hri, ↓reduceIte, decide_eq_true_eq] at hsat
        exact hjj hsat.symm
      · push Not at hri
        simp only [colModel, hri.1, hri.2, or_self, ↓reduceIte, decide_eq_true_eq] at hsat
        exact hrk (hf.2 r k hri.1 hri.2 hi'.symm hk'.symm (hsat.trans hfk.symm))

theorem z2_not_earlier {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf)
    {j₁ j₂ : Hole} {k₁ k₂ : Row} (hk₁ : k₁ ∈ Z2 tr j₁) (hk₂ : k₂ ∈ Z2 tr j₂)
    (hkne : k₁ ≠ k₂) (hjne : j₁ ≠ j₂)
    {idx₁ idx₂ : Fin tr.length} {R₁ R₂ : C}
    (hs₁ : tr[idx₁] = Step.non (k₁, j₁) R₁)
    (hu₁ : ∀ j' : Fin tr.length, isNonOf (k₁, j₁) tr[j'] = true → j' = idx₁)
    (_hs₂ : tr[idx₂] = Step.non (k₂, j₂) R₂)
    (hu₂ : ∀ j' : Fin tr.length, isNonOf (k₂, j₂) tr[j'] = true → j' = idx₂)
    (hlt : idx₂.1 < idx₁.1) : False := by
  have hshape₁ := z2_clause_shape h he hk₁ hs₁ hu₁
  have h2card : 2 ≤ (inEdges tr j₂ k₂).card := (Finset.mem_filter.mp hk₂).2
  obtain ⟨B₁, hB₁, B₂, hB₂, hBne⟩ := Finset.one_lt_card.mp (by omega : 1 < (inEdges tr j₂ k₂).card)
  obtain ⟨i₁, hi₁k, rfl⟩ := inEdges_mem_colAx h hB₁
  obtain ⟨i₂, hi₂k, rfl⟩ := inEdges_mem_colAx h hB₂
  have hi₁₂ : i₁ ≠ i₂ := fun heq => hBne (heq ▸ rfl)
  have hpick : ∃ i : Row, i ≠ k₂ ∧ i ≠ k₁ ∧ colAx i k₂ j₂ ∈ inEdges tr j₂ k₂ := by
    by_cases h1 : k₁ = i₁
    · exact ⟨i₂, hi₂k, h1 ▸ hi₁₂.symm, hB₂⟩
    · exact ⟨i₁, hi₁k, Ne.symm h1, hB₁⟩
  obtain ⟨i, hik₂, hik₁, hiE⟩ := hpick
  obtain ⟨f, hf, hfk₁⟩ := exists_validMatch_map i k₂ k₁ hik₂ hik₁.symm hkne j₂ j₁ hjne
  have hR₁mem : R₁ ∈ (tr.drop idx₁.1).map clauseOf := by
    refine List.mem_map.mpr ⟨Step.non (k₁, j₁) R₁, ?_, rfl⟩
    exact (mem_drop_iff tr idx₁.1 _).mpr ⟨idx₁, le_rfl, hs₁⟩
  have hsat := masterControl (h.drop idx₁.1) (colModel i k₂ j₂ f) (colAx i k₂ j₂) {(k₂, j₂)}
    (colModel_sat_rows hf) (colModel_sat_cols hf)
    (fun v u R' hm => Finset.mem_singleton.mpr ((inEdges_mem_iff_unique hiE).2 v u R' (mem_of_mem_drop hm)))
    (fun v R' hm hv _ => by
      rw [Finset.mem_singleton] at hv
      subst hv
      obtain ⟨m, hmle, hget⟩ := (mem_drop_iff tr idx₁.1 _).mp hm
      have heq := hu₂ m (by rw [hget]; simp [isNonOf])
      omega)
    R₁ hR₁mem (z2_not_coll hshape₁.1) (fun w _ => hshape₁.1 w)
  exact z2_unsat_colModel hshape₁ hf hjne.symm hik₁ hkne.symm hfk₁ hsat

theorem z2_line {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf)
    {j₁ j₂ : Hole} {k₁ k₂ : Row} (hk₁ : k₁ ∈ Z2 tr j₁) (hk₂ : k₂ ∈ Z2 tr j₂) :
    k₁ = k₂ ∨ j₁ = j₂ := by
  by_contra hneither
  push Not at hneither
  obtain ⟨hkne, hjne⟩ := hneither
  obtain ⟨idx₁, R₁, hs₁, hu₁⟩ := z2_unique_non hk₁
  obtain ⟨idx₂, R₂, hs₂, hu₂⟩ := z2_unique_non hk₂
  have hne : idx₁ ≠ idx₂ := by
    intro heq
    subst heq
    rw [hs₁] at hs₂
    cases hs₂
    exact hkne rfl
  rcases lt_or_gt_of_ne (Fin.val_ne_of_ne hne) with hlt | hgt
  · exact z2_not_earlier h he hk₂ hk₁ hkne.symm hjne.symm hs₂ hu₂ hs₁ hu₁ hlt
  · exact z2_not_earlier h he hk₁ hk₂ hkne hjne hs₁ hu₁ hs₂ hu₂ hgt

def subMask (x y : Nat) : Bool := (x &&& y) == x

theorem subMask_iff_testBit (x y : Nat) :
    subMask x y = true ↔ ∀ i : Nat, x.testBit i = true → y.testBit i = true := by
  simp only [subMask, beq_iff_eq]
  constructor
  · intro h i hxi
    have ht := congrArg (fun n => n.testBit i) h
    rw [Nat.testBit_and, hxi, Bool.true_and] at ht
    exact ht
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hx : x.testBit i
    · simp
    · simp [h i hx]

theorem subMask_refl (x : Nat) : subMask x x = true :=
  (subMask_iff_testBit x x).mpr (fun _ h => h)

theorem subMask_trans {x y z : Nat} (h1 : subMask x y = true) (h2 : subMask y z = true) :
    subMask x z = true :=
  (subMask_iff_testBit x z).mpr (fun i hi =>
    (subMask_iff_testBit y z).mp h2 i ((subMask_iff_testBit x y).mp h1 i hi))

theorem subMask_land_mono {a b c d : Nat} (h1 : subMask a c = true) (h2 : subMask b d = true) :
    subMask (a &&& b) (c &&& d) = true := by
  rw [subMask_iff_testBit]
  intro i hi
  rw [Nat.testBit_and, Bool.and_eq_true] at hi ⊢
  exact ⟨(subMask_iff_testBit a c).mp h1 i hi.1, (subMask_iff_testBit b d).mp h2 i hi.2⟩

theorem subMask_lor_mono {a b c d : Nat} (h1 : subMask a c = true) (h2 : subMask b d = true) :
    subMask (a ||| b) (c ||| d) = true := by
  rw [subMask_iff_testBit]
  intro i hi
  rw [Nat.testBit_or, Bool.or_eq_true] at hi ⊢
  rcases hi with h | h
  · exact Or.inl ((subMask_iff_testBit a c).mp h1 i h)
  · exact Or.inr ((subMask_iff_testBit b d).mp h2 i h)

def insertMax (x : Nat) (acc : List Nat) : List Nat :=
  if acc.any (fun y => subMask x y) then acc
  else x :: acc.filter (fun y => !(subMask y x))

def pruneMax (xs : List Nat) : List Nat :=
  xs.foldl (fun acc x => insertMax x acc) []

theorem insertMax_covers_old {x : Nat} {acc : List Nat} {z : Nat}
    (hz : ∃ w ∈ acc, subMask z w = true) :
    ∃ w ∈ insertMax x acc, subMask z w = true := by
  unfold insertMax
  split
  · exact hz
  · obtain ⟨w, hw, hzw⟩ := hz
    by_cases hwx : subMask w x = true
    · exact ⟨x, List.mem_cons_self, subMask_trans hzw hwx⟩
    · refine ⟨w, List.mem_cons_of_mem _ (List.mem_filter.mpr ⟨hw, ?_⟩), hzw⟩
      cases h : subMask w x <;> simp_all

theorem insertMax_covers_new (x : Nat) (acc : List Nat) :
    ∃ w ∈ insertMax x acc, subMask x w = true := by
  unfold insertMax
  split
  · rename_i h
    obtain ⟨y, hy, hxy⟩ := List.any_eq_true.mp h
    exact ⟨y, hy, hxy⟩
  · exact ⟨x, List.mem_cons_self, subMask_refl x⟩

theorem foldl_insertMax_covers (xs acc : List Nat) :
    (∀ z ∈ acc, ∃ w ∈ xs.foldl (fun a x => insertMax x a) acc, subMask z w = true) ∧
    (∀ x ∈ xs, ∃ w ∈ xs.foldl (fun a x => insertMax x a) acc, subMask x w = true) := by
  induction xs generalizing acc with
  | nil =>
    exact ⟨fun z hz => ⟨z, hz, subMask_refl z⟩, fun x hx => by cases hx⟩
  | cons a tl ih =>
    simp only [List.foldl_cons]
    obtain ⟨hold, hnew⟩ := ih (insertMax a acc)
    constructor
    · intro z hz
      obtain ⟨w₁, hw₁, hzw₁⟩ := insertMax_covers_old (x := a) ⟨z, hz, subMask_refl z⟩
      obtain ⟨w₂, hw₂, hw₁₂⟩ := hold w₁ hw₁
      exact ⟨w₂, hw₂, subMask_trans hzw₁ hw₁₂⟩
    · intro x hx
      rcases List.mem_cons.mp hx with rfl | hx'
      · obtain ⟨w₁, hw₁, hxw₁⟩ := insertMax_covers_new x acc
        obtain ⟨w₂, hw₂, hw₁₂⟩ := hold w₁ hw₁
        exact ⟨w₂, hw₂, subMask_trans hxw₁ hw₁₂⟩
      · exact hnew x hx'

theorem pruneMax_covers (xs : List Nat) {x : Nat} (hx : x ∈ xs) :
    ∃ y ∈ pruneMax xs, subMask x y = true :=
  (foldl_insertMax_covers xs []).2 x hx

def perm3 (p : Fin 6) (i : Fin 3) : Fin 3 :=
  match p.val, i.val with
  | 0, 0 => 0 | 0, 1 => 1 | 0, 2 => 2
  | 1, 0 => 0 | 1, 1 => 2 | 1, 2 => 1
  | 2, 0 => 1 | 2, 1 => 0 | 2, 2 => 2
  | 3, 0 => 1 | 3, 1 => 2 | 3, 2 => 0
  | 4, 0 => 2 | 4, 1 => 0 | 4, 2 => 1
  | _, 0 => 2 | _, 1 => 1 | _, _ => 0

def bHole (c : Fin 3) (p : Fin 6) (r : Fin 5) : Fin 4 :=
  match c.val, r.val with
  | 0, 0 => 0 | 0, 1 => (perm3 p 0).succ | 0, 2 => (perm3 p 1).succ | 0, 3 => 0 | 0, _ => (perm3 p 2).succ
  | 1, 0 => (perm3 p 0).succ | 1, 1 => 0 | 1, 2 => (perm3 p 1).succ | 1, 3 => 0 | 1, _ => (perm3 p 2).succ
  | _, 0 => (perm3 p 0).succ | _, 1 => (perm3 p 1).succ | _, 2 => 0 | _, 3 => 0 | _, _ => (perm3 p 2).succ

def otherHoles (m : Fin 3) : Fin 4 × Fin 4 :=
  match m.val with
  | 0 => (2, 3)
  | 1 => (1, 3)
  | _ => (1, 2)

def oneMustHole (m ic : Fin 3) (r : Fin 5) : Fin 4 :=
  let (h1, h2) := otherHoles m
  match ic.val, r.val with
  | 0, 0 => m.succ | 0, 1 => h1 | 0, 2 => h2 | 0, 3 => 0 | 0, _ => m.succ
  | 1, 0 => h1 | 1, 1 => m.succ | 1, 2 => h2 | 1, 3 => 0 | 1, _ => m.succ
  | _, 0 => h1 | _, 1 => h2 | _, 2 => m.succ | _, 3 => 0 | _, _ => m.succ

def fin3ToRow (c : Fin 3) : Row := ⟨c.val, by omega⟩

theorem bHole_valid : ∀ (c : Fin 3) (p : Fin 6), ValidMatch (fin3ToRow c) 3 0 (bHole c p) := by
  intro c p
  apply validMatch_of_bool
  have h : (List.finRange 3).all (fun c => (List.finRange 6).all (fun p => validMatchB (fin3ToRow c) 3 0 (bHole c p))) = true := by
    decide +kernel
  exact List.all_eq_true.mp (List.all_eq_true.mp h c (List.mem_finRange _)) p (List.mem_finRange _)

theorem bHole_colModel_eq :
    ∀ (c : Fin 3) (p : Fin 6) (r : Row) (q : Hole),
      colModel (fin3ToRow c) 3 0 (bHole c p) (r, q) = decide (bHole c p r = q) := by
  decide +kernel

theorem oneMustHole_valid :
    ∀ (m ic : Fin 3), ValidMatch (fin3ToRow ic) 4 m.succ (oneMustHole m ic) := by
  intro m ic
  apply validMatch_of_bool
  have h : (List.finRange 3).all (fun m => (List.finRange 3).all (fun ic => validMatchB (fin3ToRow ic) 4 m.succ (oneMustHole m ic))) = true := by
    decide +kernel
  exact List.all_eq_true.mp (List.all_eq_true.mp h m (List.mem_finRange _)) ic (List.mem_finRange _)

theorem oneMustHole_colModel_eq :
    ∀ (m ic : Fin 3) (r : Row) (q : Hole),
      colModel (fin3ToRow ic) 4 m.succ (oneMustHole m ic) (r, q) = decide (oneMustHole m ic r = q) := by
  decide +kernel

def idxC (idx : Fin 18) : Fin 3 := ⟨idx.val / 6, by omega⟩
def idxP (idx : Fin 18) : Fin 6 := ⟨idx.val % 6, by omega⟩

def evalLitHole (h : Row → Hole) (l : Literal V) : Bool :=
  if l.2 then decide (h l.1.1 = l.1.2) else !decide (h l.1.1 = l.1.2)

def fmaskList (l : Literal V) : Nat :=
  (List.finRange 18).foldl
    (fun acc idx => if evalLitHole (bHole (idxC idx) (idxP idx)) l then acc else acc ||| (1 <<< idx.val))
    0

def allLits39 : List (Literal V) :=
  ((List.finRange 5).flatMap fun r =>
    (List.finRange 4).flatMap fun q =>
      [((r, q), false), ((r, q), true)]).filter (fun l => l != ((3, 0), false))

def isWitnessLit (m ic : Fin 3) (l : Literal V) : Bool :=
  (l == ((4, m.succ), false)) || evalLitHole (oneMustHole m ic) l

def witsList (m ic : Fin 3) : List Nat :=
  (allLits39.filter (isWitnessLit m ic)).map fmaskList

def req1Mask (pos : Nat) : Nat :=
  (List.finRange 18).foldl
    (fun acc idx =>
      if decide ((bHole (idxC idx) (idxP idx) 4).val - 1 < pos) then acc ||| (1 <<< idx.val) else acc)
    0

def pairLand (xs ys : List Nat) : List Nat :=
  pruneMax (xs.flatMap (fun a => ys.map (fun b => a &&& b)))

def checkCase (ic0 ic1 ic2 : Fin 3) : Bool :=
  let w0 := pruneMax (witsList 0 ic0)
  let w1 := pruneMax (witsList 1 ic1)
  let w2 := pruneMax (witsList 2 ic2)
  let c01 := pairLand w0 w1
  let c012 := pairLand c01 w2
  let c12 := pairLand w1 w2
  let ok0 := c012.all (fun x => c012.all (fun y => !(subMask 262143 (x ||| y))))
  let ok1 := (c012.filter (fun x => subMask (req1Mask 1) x)).all
    (fun x => c12.all (fun y => !(subMask 262143 (x ||| y))))
  let ok2 := (c012.filter (fun x => subMask (req1Mask 2) x)).all
    (fun x => w2.all (fun y => !(subMask 262143 (x ||| y))))
  let ok3 := c012.all (fun x => !(subMask 262143 x))
  ok0 && ok1 && ok2 && ok3

def checkAll : Bool :=
  (List.finRange 3).all (fun ic0 =>
    (List.finRange 3).all (fun ic1 =>
      (List.finRange 3).all (fun ic2 => checkCase ic0 ic1 ic2)))

theorem checkAll_eq_true : checkAll = true := by decide +kernel

theorem foldl_lor_testBit (p : Fin 18 → Bool) (i : Fin 18) :
    ((List.finRange 18).foldl
      (fun acc idx => if p idx then acc ||| (1 <<< idx.val) else acc) 0).testBit i.val = p i := by
  have hgen : ∀ (l : List (Fin 18)) (acc : Nat),
      (l.foldl (fun a idx => if p idx then a ||| (1 <<< idx.val) else a) acc).testBit i.val =
        (acc.testBit i.val || (i ∈ l && p i)) := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons a tl ih =>
      intro acc
      simp only [List.foldl_cons, ih]
      by_cases hpa : p a = true
      · simp only [hpa, ↓reduceIte, Nat.testBit_or, Nat.testBit_shiftLeft]
        by_cases hia : i = a
        · subst hia; simp [hpa]
        · have hne : i.val ≠ a.val := Fin.val_ne_of_ne hia
          have hbit : (decide (i.val ≥ a.val) && Nat.testBit 1 (i.val - a.val)) = false := by
            by_cases hle : a.val ≤ i.val
            · have hnz : i.val - a.val ≠ 0 := by omega
              have hnt : Nat.testBit 1 (i.val - a.val) = false :=
                Bool.eq_false_iff.mpr (fun ht => hnz (Nat.testBit_one_eq_true_iff_self_eq_zero.mp ht))
              simp [hle, hnt]
            · simp [hle]
          rw [hbit]
          simp [hia]
      · simp only [hpa]
        by_cases hia : i = a
        · subst hia; simp [hpa]
        · simp [hia]
  rw [hgen]
  simp [List.mem_finRange]

theorem fmaskList_testBit (l : Literal V) (idx : Fin 18) :
    (fmaskList l).testBit idx.val = !evalLitHole (bHole (idxC idx) (idxP idx)) l := by
  have h := foldl_lor_testBit (fun idx => !evalLitHole (bHole (idxC idx) (idxP idx)) l) idx
  have heq : fmaskList l = (List.finRange 18).foldl
      (fun acc idx => if !evalLitHole (bHole (idxC idx) (idxP idx)) l then acc ||| (1 <<< idx.val) else acc) 0 := by
    unfold fmaskList
    congr 1
    funext acc i
    cases evalLitHole (bHole (idxC i) (idxP i)) l <;> rfl
  rw [heq, h]

theorem req1Mask_testBit (pos : Nat) (idx : Fin 18) :
    (req1Mask pos).testBit idx.val = decide ((bHole (idxC idx) (idxP idx) 4).val - 1 < pos) :=
  foldl_lor_testBit (fun idx => decide ((bHole (idxC idx) (idxP idx) 4).val - 1 < pos)) idx

theorem all18_testBit (i : Nat) : (262143 : Nat).testBit i = decide (i < 18) := by
  by_cases hi : i < 18
  · interval_cases i <;> decide +kernel
  · have hlt : (262143 : Nat) < 2 ^ i := by
      have h1 : (262143 : Nat) < 2 ^ 18 := by decide +kernel
      have h2 : 2 ^ 18 ≤ 2 ^ i := Nat.pow_le_pow_right (by omega) (by omega)
      omega
    simp [hi, Nat.testBit_lt_two_pow hlt]

theorem mem_allLits39 {l : Literal V} (hne : l ≠ ((3, 0), false)) : l ∈ allLits39 := by
  unfold allLits39
  rw [List.mem_filter]
  refine ⟨?_, by simp [hne]⟩
  rw [List.mem_flatMap]
  refine ⟨l.1.1, List.mem_finRange _, ?_⟩
  rw [List.mem_flatMap]
  refine ⟨l.1.2, List.mem_finRange _, ?_⟩
  rcases l with ⟨⟨r, q⟩, pol⟩
  cases pol <;> simp

theorem pairLand_covers {xs ys xs' ys' : List Nat}
    (hx : ∀ x ∈ xs, ∃ x' ∈ xs', subMask x x' = true)
    (hy : ∀ y ∈ ys, ∃ y' ∈ ys', subMask y y' = true)
    {a b : Nat} (ha : a ∈ xs) (hb : b ∈ ys) :
    ∃ z ∈ pairLand xs' ys', subMask (a &&& b) z = true := by
  obtain ⟨a', ha', haa'⟩ := hx a ha
  obtain ⟨b', hb', hbb'⟩ := hy b hb
  have hmem : (a' &&& b') ∈ xs'.flatMap (fun u => ys'.map (fun v => u &&& v)) := by
    rw [List.mem_flatMap]
    exact ⟨a', ha', List.mem_map.mpr ⟨b', hb', rfl⟩⟩
  obtain ⟨z, hz, hsub⟩ := pruneMax_covers _ hmem
  exact ⟨z, hz, subMask_trans (subMask_land_mono haa' hbb') hsub⟩

theorem killer_masks_impossible (ic0 ic1 ic2 : Fin 3) (pos : Fin 4)
    (m1 m2 : Nat)
    (hm1_0 : ∃ x ∈ witsList 0 ic0, subMask m1 x = true)
    (hm1_1 : ∃ x ∈ witsList 1 ic1, subMask m1 x = true)
    (hm1_2 : ∃ x ∈ witsList 2 ic2, subMask m1 x = true)
    (hreq : subMask (req1Mask pos.val) m1 = true)
    (hm2_0 : pos.val = 0 → ∃ x ∈ witsList 0 ic0, subMask m2 x = true)
    (hm2_1 : pos.val ≤ 1 → ∃ x ∈ witsList 1 ic1, subMask m2 x = true)
    (hm2_2 : pos.val ≤ 2 → ∃ x ∈ witsList 2 ic2, subMask m2 x = true)
    (hcov : subMask 262143 (m1 ||| m2) = true) : False := by
  have hcase : checkCase ic0 ic1 ic2 = true := by
    have h0 := List.all_eq_true.mp checkAll_eq_true ic0 (List.mem_finRange _)
    have h1 := List.all_eq_true.mp h0 ic1 (List.mem_finRange _)
    exact List.all_eq_true.mp h1 ic2 (List.mem_finRange _)
  unfold checkCase at hcase
  simp only [Bool.and_eq_true] at hcase
  obtain ⟨⟨⟨hok0, hok1⟩, hok2⟩, hok3⟩ := hcase
  let w0 := pruneMax (witsList 0 ic0)
  let w1 := pruneMax (witsList 1 ic1)
  let w2 := pruneMax (witsList 2 ic2)
  let c01 := pairLand w0 w1
  let c012 := pairLand c01 w2
  let c12 := pairLand w1 w2
  have hw0 : ∀ x ∈ witsList 0 ic0, ∃ y ∈ w0, subMask x y = true := fun _ hx => pruneMax_covers _ hx
  have hw1 : ∀ x ∈ witsList 1 ic1, ∃ y ∈ w1, subMask x y = true := fun _ hx => pruneMax_covers _ hx
  have hw2 : ∀ x ∈ witsList 2 ic2, ∃ y ∈ w2, subMask x y = true := fun _ hx => pruneMax_covers _ hx
  have hcov_m1 : ∃ z1 ∈ c012, subMask m1 z1 = true := by
    obtain ⟨x0, hx0, hmx0⟩ := hm1_0
    obtain ⟨x1, hx1, hmx1⟩ := hm1_1
    obtain ⟨x2, hx2, hmx2⟩ := hm1_2
    obtain ⟨u01, hu01, h01⟩ := pairLand_covers hw0 hw1 hx0 hx1
    obtain ⟨y2, hy2, h2⟩ := hw2 x2 hx2
    have hmem : (u01 &&& y2) ∈ c01.flatMap (fun a => w2.map (fun b => a &&& b)) :=
      List.mem_flatMap.mpr ⟨u01, hu01, List.mem_map.mpr ⟨y2, hy2, rfl⟩⟩
    obtain ⟨z1, hz1, hz1sub⟩ := pruneMax_covers _ hmem
    have hm01 : subMask m1 (x0 &&& x1) = true := by
      have := subMask_land_mono hmx0 hmx1
      simpa [Nat.and_self] using this
    have hm012 : subMask m1 (u01 &&& y2) = true := by
      have := subMask_land_mono (subMask_trans hm01 h01) (subMask_trans hmx2 h2)
      simpa [Nat.and_self] using this
    exact ⟨z1, hz1, subMask_trans hm012 hz1sub⟩
  obtain ⟨z1, hz1, hmz1⟩ := hcov_m1
  fin_cases pos
  ·
    obtain ⟨x0, hx0, hmx0⟩ := hm2_0 rfl
    obtain ⟨x1, hx1, hmx1⟩ := hm2_1 (by decide)
    obtain ⟨x2, hx2, hmx2⟩ := hm2_2 (by decide)
    obtain ⟨u01, hu01, h01⟩ := pairLand_covers hw0 hw1 hx0 hx1
    obtain ⟨y2, hy2, h2⟩ := hw2 x2 hx2
    have hmem : (u01 &&& y2) ∈ c01.flatMap (fun a => w2.map (fun b => a &&& b)) :=
      List.mem_flatMap.mpr ⟨u01, hu01, List.mem_map.mpr ⟨y2, hy2, rfl⟩⟩
    obtain ⟨z2, hz2, hz2sub⟩ := pruneMax_covers _ hmem
    have hm01 : subMask m2 (x0 &&& x1) = true := by
      simpa [Nat.and_self] using subMask_land_mono hmx0 hmx1
    have hmz2 : subMask m2 z2 = true := subMask_trans
      (by simpa [Nat.and_self] using subMask_land_mono (subMask_trans hm01 h01) (subMask_trans hmx2 h2))
      hz2sub
    have hfull : subMask 262143 (z1 ||| z2) = true :=
      subMask_trans hcov (subMask_lor_mono hmz1 hmz2)
    have hbad := List.all_eq_true.mp (List.all_eq_true.mp hok0 z1 hz1) z2 hz2
    simp [hfull] at hbad
  ·
    obtain ⟨x1, hx1, hmx1⟩ := hm2_1 (by decide)
    obtain ⟨x2, hx2, hmx2⟩ := hm2_2 (by decide)
    obtain ⟨z2, hz2, h12⟩ := pairLand_covers hw1 hw2 hx1 hx2
    have hmz2 : subMask m2 z2 = true := subMask_trans
      (by simpa [Nat.and_self] using subMask_land_mono hmx1 hmx2) h12
    have hfull : subMask 262143 (z1 ||| z2) = true :=
      subMask_trans hcov (subMask_lor_mono hmz1 hmz2)
    have hz1f : z1 ∈ c012.filter (fun x => subMask (req1Mask 1) x) :=
      List.mem_filter.mpr ⟨hz1, subMask_trans hreq hmz1⟩
    have hbad := List.all_eq_true.mp (List.all_eq_true.mp hok1 z1 hz1f) z2 hz2
    simp [hfull] at hbad
  ·
    obtain ⟨x2, hx2, hmx2⟩ := hm2_2 (by decide)
    obtain ⟨z2, hz2, h2⟩ := hw2 x2 hx2
    have hmz2 : subMask m2 z2 = true := subMask_trans hmx2 h2
    have hfull : subMask 262143 (z1 ||| z2) = true :=
      subMask_trans hcov (subMask_lor_mono hmz1 hmz2)
    have hz1f : z1 ∈ c012.filter (fun x => subMask (req1Mask 2) x) :=
      List.mem_filter.mpr ⟨hz1, subMask_trans hreq hmz1⟩
    have hbad := List.all_eq_true.mp (List.all_eq_true.mp hok2 z1 hz1f) z2 hz2
    simp [hfull] at hbad
  ·
    have hreq3 : req1Mask 3 = 262143 := by decide +kernel
    rw [hreq3] at hreq
    have hfull : subMask 262143 z1 = true := subMask_trans hreq hmz1
    have hbad := List.all_eq_true.mp hok3 z1 hz1
    simp [hfull] at hbad

def transportF (er : Row ≃ Row) (eh : Hole ≃ Hole) (g : Row → Hole) : Row → Hole :=
  fun r => eh (g (er.symm r))

theorem transport_validMatch (er : Row ≃ Row) (eh : Hole ≃ Hole)
    {i k : Row} {j : Hole} {g : Row → Hole} (hg : ValidMatch i k j g) :
    ValidMatch (er i) (er k) (eh j) (transportF er eh g) := by
  refine ⟨?_, ?_⟩
  · intro r hri hrk heq
    have h1 : er.symm r ≠ i := fun h => hri (by rw [← h, er.apply_symm_apply])
    have h2 : er.symm r ≠ k := fun h => hrk (by rw [← h, er.apply_symm_apply])
    exact hg.1 (er.symm r) h1 h2 (eh.injective heq)
  · intro r₁ r₂ hr₁i hr₁k hr₂i hr₂k heq
    have h1i : er.symm r₁ ≠ i := fun h => hr₁i (by rw [← h, er.apply_symm_apply])
    have h1k : er.symm r₁ ≠ k := fun h => hr₁k (by rw [← h, er.apply_symm_apply])
    have h2i : er.symm r₂ ≠ i := fun h => hr₂i (by rw [← h, er.apply_symm_apply])
    have h2k : er.symm r₂ ≠ k := fun h => hr₂k (by rw [← h, er.apply_symm_apply])
    exact er.symm.injective (hg.2 _ _ h1i h1k h2i h2k (eh.injective heq))

theorem transport_colModel (er : Row ≃ Row) (eh : Hole ≃ Hole)
    {i k : Row} {j : Hole} {g : Row → Hole} (r : Row) (q : Hole) :
    colModel (er i) (er k) (eh j) (transportF er eh g) (er r, eh q) =
      colModel i k j g (r, q) := by
  simp only [colModel, transportF, er.symm_apply_apply, er.injective.eq_iff, eh.injective.eq_iff]

def pullLit (er : Row ≃ Row) (eh : Hole ≃ Hole) (l : Literal V) : Literal V :=
  ((er.symm l.1.1, eh.symm l.1.2), l.2)

theorem literalSat_transport_bHole (er : Row ≃ Row) (eh : Hole ≃ Hole)
    (c : Fin 3) (p : Fin 6) (l : Literal V) :
    LiteralSat (colModel (er (fin3ToRow c)) (er 3) (eh 0) (transportF er eh (bHole c p))) l ↔
      evalLitHole (bHole c p) (pullLit er eh l) = true := by
  rcases l with ⟨⟨r, q⟩, pol⟩
  have hr : r = er (er.symm r) := (er.apply_symm_apply r).symm
  have hq : q = eh (eh.symm q) := (eh.apply_symm_apply q).symm
  conv_lhs => rw [hr, hq]
  simp only [LiteralSat, transport_colModel, bHole_colModel_eq, evalLitHole, pullLit]
  cases pol <;> by_cases h : bHole c p (er.symm r) = eh.symm q <;> simp [h]

theorem literalSat_transport_oneMust (er : Row ≃ Row) (eh : Hole ≃ Hole)
    (m ic : Fin 3) (l : Literal V) :
    LiteralSat (colModel (er (fin3ToRow ic)) (er 4) (eh m.succ) (transportF er eh (oneMustHole m ic))) l ↔
      evalLitHole (oneMustHole m ic) (pullLit er eh l) = true := by
  rcases l with ⟨⟨r, q⟩, pol⟩
  have hr : r = er (er.symm r) := (er.apply_symm_apply r).symm
  have hq : q = eh (eh.symm q) := (eh.apply_symm_apply q).symm
  conv_lhs => rw [hr, hq]
  simp only [LiteralSat, transport_colModel, oneMustHole_colModel_eq, evalLitHole, pullLit]
  cases pol <;> by_cases h : oneMustHole m ic (er.symm r) = eh.symm q <;> simp [h]

theorem exists_row_equiv (k₀ b : Row) (hbk : b ≠ k₀) :
    ∃ er : Row ≃ Row, er 4 = k₀ ∧ er 3 = b := by
  let A : Finset Row := ((Finset.univ : Finset Row).erase k₀).erase b
  have hbm : b ∈ (Finset.univ : Finset Row).erase k₀ :=
    Finset.mem_erase.mpr ⟨hbk, Finset.mem_univ _⟩
  have hAcard : A.card = 3 := by
    dsimp only [A]
    rw [Finset.card_erase_of_mem hbm, Finset.card_erase_of_mem (Finset.mem_univ k₀)]
    decide +kernel
  let e3 : Fin 3 ≃ ↥A :=
    Fintype.equivOfCardEq (by simp [Fintype.card_coe, hAcard])
  let f : Row → Row := fun r =>
    if h0 : r.val < 3 then (e3 ⟨r.val, h0⟩).1
    else if r = 3 then b else k₀
  have hinj : Function.Injective f := by
    intro r₁ r₂ heq
    have hmem : ∀ i : Fin 3, (e3 i).1 ≠ b ∧ (e3 i).1 ≠ k₀ := fun i =>
      ⟨(Finset.mem_erase.mp (e3 i).2).1, (Finset.mem_erase.mp (Finset.mem_erase.mp (e3 i).2).2).1⟩
    by_cases h1 : r₁.val < 3 <;> by_cases h2 : r₂.val < 3
    · simp only [f, h1, h2, ↓reduceDIte] at heq
      have hv : r₁.val = r₂.val := congrArg (fun x : Fin 3 => x.val) (e3.injective (Subtype.ext heq))
      exact Fin.ext hv
    · simp only [f, h1, h2, ↓reduceDIte] at heq
      split_ifs at heq
      · exact ((hmem _).1 heq).elim
      · exact ((hmem _).2 heq).elim
    · simp only [f, h1, h2, ↓reduceDIte] at heq
      split_ifs at heq
      · exact ((hmem _).1 heq.symm).elim
      · exact ((hmem _).2 heq.symm).elim
    · simp only [f, h1, h2, ↓reduceDIte] at heq
      have hr1 : r₁ = 3 ∨ r₁ = 4 := by fin_cases r₁ <;> simp_all
      have hr2 : r₂ = 3 ∨ r₂ = 4 := by fin_cases r₂ <;> simp_all
      rcases hr1 with rfl | rfl <;> rcases hr2 with rfl | rfl
      · rfl
      · simp at heq; exact (hbk heq).elim
      · simp at heq; exact (hbk heq.symm).elim
      · rfl
  refine ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hinj), ?_, ?_⟩
  · simp [f]
  · simp [f]

theorem exists_hole_equiv_sorted (score : Hole → ℕ)
    (hinj : ∀ j₁ j₂ : Hole, j₁ ≠ 0 → j₂ ≠ 0 → j₁ ≠ j₂ → score j₁ ≠ score j₂) :
    ∃ eh : Hole ≃ Hole, eh 0 = 0 ∧
      score (eh 3) < score (eh 2) ∧ score (eh 2) < score (eh 1) := by
  have h12 : score 1 ≠ score 2 := hinj 1 2 (by decide) (by decide) (by decide)
  have h13 : score 1 ≠ score 3 := hinj 1 3 (by decide) (by decide) (by decide)
  have h23 : score 2 ≠ score 3 := hinj 2 3 (by decide) (by decide) (by decide)
  have mkEquiv : ∀ (a b c : Hole), a ≠ 0 → b ≠ 0 → c ≠ 0 → a ≠ b → a ≠ c → b ≠ c →
      ∃ eh : Hole ≃ Hole, eh 0 = 0 ∧ eh 1 = a ∧ eh 2 = b ∧ eh 3 = c := by
    intro a b c ha0 hb0 hc0 hab hac hbc
    let f : Hole → Hole := fun q =>
      match q.val with | 0 => 0 | 1 => a | 2 => b | _ => c
    have hfi : Function.Injective f := by
      intro x y hxy
      fin_cases x <;> fin_cases y <;> simp [f] at hxy ⊢
      all_goals first | exact ha0 hxy.symm | exact hb0 hxy.symm | exact hc0 hxy.symm |
        exact ha0 hxy | exact hb0 hxy | exact hc0 hxy | exact hab hxy | exact hab hxy.symm |
        exact hac hxy | exact hac hxy.symm | exact hbc hxy | exact hbc hxy.symm
    exact ⟨Equiv.ofBijective f (Finite.injective_iff_bijective.mp hfi), rfl, rfl, rfl, rfl⟩
  rcases lt_or_gt_of_ne h12 with h12' | h21' <;>
    rcases lt_or_gt_of_ne h13 with h13' | h31' <;>
    rcases lt_or_gt_of_ne h23 with h23' | h32'
  ·
    obtain ⟨eh, h0, h1, h2, h3⟩ := mkEquiv 3 2 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ⟨eh, h0, by rw [h3, h2]; exact h12', by rw [h2, h1]; exact h23'⟩
  ·
    obtain ⟨eh, h0, h1, h2, h3⟩ := mkEquiv 2 3 1 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ⟨eh, h0, by rw [h3, h2]; exact h13', by rw [h2, h1]; exact h32'⟩
  · omega
  ·
    obtain ⟨eh, h0, h1, h2, h3⟩ := mkEquiv 2 1 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ⟨eh, h0, by rw [h3, h2]; exact h31', by rw [h2, h1]; exact h12'⟩
  ·
    obtain ⟨eh, h0, h1, h2, h3⟩ := mkEquiv 3 1 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ⟨eh, h0, by rw [h3, h2]; exact h21', by rw [h2, h1]; exact h13'⟩
  · omega
  ·
    obtain ⟨eh, h0, h1, h2, h3⟩ := mkEquiv 1 3 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ⟨eh, h0, by rw [h3, h2]; exact h23', by rw [h2, h1]; exact h31'⟩
  ·
    obtain ⟨eh, h0, h1, h2, h3⟩ := mkEquiv 1 2 3 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    exact ⟨eh, h0, by rw [h3, h2]; exact h32', by rw [h2, h1]; exact h21'⟩

theorem caseA_impossible {tr : List Step} (h : ValidTrace tr)
    (he : (∅ : C) ∈ tr.map clauseOf) (k₀ : Row)
    (hZ : ∀ j : Hole, Z2 tr j = {k₀})
    (hcost : ∀ j : Hole, holeCost tr j = 16) : False := by
  classical

  obtain ⟨b, hbk, hb2, hbEdges⟩ := (holeCost_of_Z2_singleton h he (hZ 0)).2 (hcost 0)
  obtain ⟨er, her4, her3⟩ := exists_row_equiv k₀ b hbk

  have hzk : ∀ j : Hole, k₀ ∈ Z2 tr j := fun j => (hZ j) ▸ Finset.mem_singleton_self k₀
  choose p Rk hpstep hpuniq using fun j : Hole => z2_unique_non (hzk j)
  have hpinj : ∀ j₁ j₂ : Hole, j₁ ≠ 0 → j₂ ≠ 0 → j₁ ≠ j₂ → (p j₁).1 ≠ (p j₂).1 := by
    intro j₁ j₂ _ _ hjne heq
    have hidx : p j₁ = p j₂ := Fin.ext heq
    have hs := (hpstep j₁).symm.trans (hidx ▸ hpstep j₂)
    cases hs
    exact hjne rfl
  obtain ⟨eh, heh0, hord32, hord21⟩ := exists_hole_equiv_sorted (fun j => (p j).1) hpinj

  obtain ⟨i₁, i₂, hi₂₁, hi₁p, hi₂p, hiuniq⟩ := countP_eq_two_unique_idx tr (isNonOf (b, 0)) hb2
  have hextract : ∀ (i : Fin tr.length), isNonOf (b, 0) tr[i] = true → ∃ R, tr[i] = Step.non (b, 0) R := by
    intro i hi
    cases hs : tr[i] with
    | ax _ => simp [hs, isNonOf] at hi
    | col _ _ _ _ => simp [hs, isNonOf] at hi
    | non v R =>
      simp only [hs, isNonOf, decide_eq_true_eq] at hi
      subst hi
      exact ⟨R, rfl⟩
  obtain ⟨R₁, hR₁step⟩ := hextract i₁ hi₁p
  obtain ⟨R₂, hR₂step⟩ := hextract i₂ hi₂p

  let aB : Fin 18 → (V → Bool) := fun idx =>
    colModel (er (fin3ToRow (idxC idx))) b 0 (transportF er eh (bHole (idxC idx) (idxP idx)))
  have haB_valid : ∀ idx : Fin 18,
      ValidMatch (er (fin3ToRow (idxC idx))) b 0 (transportF er eh (bHole (idxC idx) (idxP idx))) := by
    intro idx
    rw [← her3, ← heh0]
    exact transport_validMatch er eh (bHole_valid (idxC idx) (idxP idx))
  have haB_edge : ∀ idx : Fin 18, colAx (er (fin3ToRow (idxC idx))) b 0 ∈ inEdges tr 0 b := by
    intro idx
    apply hbEdges
    · rw [← her4]; exact fun heq => by
        have := er.injective heq
        have : (idxC idx).val = 4 := congrArg Fin.val this
        omega
    · rw [← her3]; exact fun heq => by
        have := er.injective heq
        have : (idxC idx).val = 3 := congrArg Fin.val this
        omega

  have hp1_lt_i₁ : (p (eh 1)).1 < i₁.1 := by
    by_contra hge
    have hne : p (eh 1) ≠ i₁ := by
      intro heq
      have hs := (hpstep (eh 1)).symm.trans (heq ▸ hR₁step)
      have hv : (k₀, eh 1) = (b, 0) := by injection hs
      exact hbk (congrArg Prod.fst hv).symm
    have hlt : i₁.1 < (p (eh 1)).1 := by
      have := Fin.val_ne_of_ne hne
      omega
    have hslot : bHole (idxC 3) (idxP 3) 4 = 1 := by decide +kernel
    have hshape := z2_clause_shape h he (hzk (eh 1)) (hpstep (eh 1)) (hpuniq (eh 1))
    have hRkmem : Rk (eh 1) ∈ (tr.drop (p (eh 1)).1).map clauseOf := by
      refine List.mem_map.mpr ⟨Step.non (k₀, eh 1) (Rk (eh 1)), ?_, rfl⟩
      exact (mem_drop_iff tr (p (eh 1)).1 _).mpr ⟨p (eh 1), le_rfl, hpstep (eh 1)⟩
    have hsat := masterControl (h.drop (p (eh 1)).1) (aB 3) (colAx (er (fin3ToRow (idxC 3))) b 0) {(b, 0)}
      (colModel_sat_rows (haB_valid 3)) (colModel_sat_cols (haB_valid 3))
      (fun v u R' hm => Finset.mem_singleton.mpr ((inEdges_mem_iff_unique (haB_edge 3)).2 v u R' (mem_of_mem_drop hm)))
      (fun v R' hm hv _ => by
        rw [Finset.mem_singleton] at hv; subst hv
        obtain ⟨m, hmle, hget⟩ := (mem_drop_iff tr (p (eh 1)).1 _).mp hm
        rcases hiuniq m (by rw [hget]; simp [isNonOf]) with rfl | rfl <;> omega)
      (Rk (eh 1)) hRkmem (z2_not_coll hshape.1) (fun w _ => hshape.1 w)
    have hfk : transportF er eh (bHole (idxC 3) (idxP 3)) k₀ = eh 1 := by
      simp [transportF, ← her4, hslot]
    have hne01 : (0 : Hole) ≠ eh 1 := by
      rw [← heh0]; exact fun heq => by have := eh.injective heq; cases this
    have hicne : er (fin3ToRow (idxC 3)) ≠ k₀ := by
      rw [← her4]; exact fun heq => by have : (idxC 3).val = 4 := congrArg Fin.val (er.injective heq); omega
    exact z2_unsat_colModel hshape (haB_valid 3) hne01 hicne hbk hfk hsat

  have hex_ic : ∀ m : Fin 3, ∃ ic : Fin 3,
      colAx (er (fin3ToRow ic)) k₀ (eh m.succ) ∈ inEdges tr (eh m.succ) k₀ := by
    intro m
    have h2card : 2 ≤ (inEdges tr (eh m.succ) k₀).card := (Finset.mem_filter.mp (hzk (eh m.succ))).2
    obtain ⟨B₁, hB₁, B₂, hB₂, hBne⟩ := Finset.one_lt_card.mp (by omega : 1 < (inEdges tr (eh m.succ) k₀).card)
    obtain ⟨x₁, hx₁k, rfl⟩ := inEdges_mem_colAx h hB₁
    obtain ⟨x₂, hx₂k, rfl⟩ := inEdges_mem_colAx h hB₂
    have hx₁₂ : x₁ ≠ x₂ := fun heq => hBne (heq ▸ rfl)
    have hpick : ∃ x : Row, x ≠ k₀ ∧ x ≠ b ∧ colAx x k₀ (eh m.succ) ∈ inEdges tr (eh m.succ) k₀ := by
      by_cases hb1 : x₁ = b
      · exact ⟨x₂, hx₂k, hb1 ▸ hx₁₂.symm, hB₂⟩
      · exact ⟨x₁, hx₁k, hb1, hB₁⟩
    obtain ⟨x, hxk, hxb, hxE⟩ := hpick
    let y : Row := er.symm x
    have hyx : er y = x := er.apply_symm_apply x
    have hy4 : y ≠ 4 := fun h => hxk (by rw [← hyx, h, her4])
    have hy3 : y ≠ 3 := fun h => hxb (by rw [← hyx, h, her3])
    have hylt : y.val < 3 := by
      have hy5 := y.2
      have h3 : y.val ≠ 3 := fun h => hy3 (Fin.ext h)
      have h4 : y.val ≠ 4 := fun h => hy4 (Fin.ext h)
      omega
    refine ⟨⟨y.val, hylt⟩, ?_⟩
    have hy_eq : er (fin3ToRow ⟨y.val, hylt⟩) = x := by
      have : fin3ToRow ⟨y.val, hylt⟩ = y := Fin.ext rfl
      rw [this, hyx]
    rwa [hy_eq]
  choose ic hicE using hex_ic

  have hi₂_ne_p : ∀ m : Fin 3, i₂.1 ≠ (p (eh m.succ)).1 := by
    intro m heq
    have hidx : i₂ = p (eh m.succ) := Fin.ext heq
    have hs := hR₂step.symm.trans (hidx ▸ hpstep (eh m.succ))
    have hv : (b, 0) = (k₀, eh m.succ) := by injection hs
    exact hbk (congrArg Prod.fst hv)
  let pos : Fin 4 :=
    if (p (eh 1)).1 < i₂.1 then 0
    else if (p (eh 2)).1 < i₂.1 then 1
    else if (p (eh 3)).1 < i₂.1 then 2
    else 3
  have hpos_lt : ∀ m : Fin 3, m.val < pos.val → i₂.1 < (p (eh m.succ)).1 := by
    intro m hm
    have h1 := hi₂_ne_p 0
    have h2 := hi₂_ne_p 1
    have h3 := hi₂_ne_p 2
    dsimp only [pos] at hm
    split_ifs at hm with c1 c2 c3
    · exfalso; simp at hm
    · fin_cases m
      · exact lt_of_le_of_ne (Nat.le_of_not_lt c1) h1
      · exfalso; simp at hm
      · exfalso; simp at hm
    · fin_cases m
      · exact lt_of_le_of_ne (Nat.le_of_not_lt c1) h1
      · exact lt_of_le_of_ne (Nat.le_of_not_lt c2) h2
      · exfalso; simp at hm
    · fin_cases m
      · exact lt_of_le_of_ne (Nat.le_of_not_lt c1) h1
      · exact lt_of_le_of_ne (Nat.le_of_not_lt c2) h2
      · exact lt_of_le_of_ne (Nat.le_of_not_lt c3) h3
  have hpos_ge : ∀ m : Fin 3, pos.val ≤ m.val → (p (eh m.succ)).1 < i₂.1 := by
    intro m hm
    dsimp only [pos] at hm
    split_ifs at hm with c1 c2 c3
    · fin_cases m
      · exact c1
      · exact lt_trans hord21 c1
      · exact lt_trans hord32 (lt_trans hord21 c1)
    · fin_cases m
      · exfalso; simp at hm
      · exact c2
      · exact lt_trans hord32 c2
    · fin_cases m
      · exfalso; simp at hm
      · exfalso; simp at hm
      · exact c3
    · exfalso; fin_cases m <;> simp at hm

  let okR : C → Prop := fun R => ((b, 0), false) ∉ R ∧ ¬ Coll R
  let p1 : Fin 18 → Bool := fun idx => decide (okR R₁ ∧ ¬ ClauseSat (aB idx) R₁)
  let p2 : Fin 18 → Bool := fun idx => decide (okR R₂ ∧ ¬ ClauseSat (aB idx) R₂)
  let m1 : Nat := (List.finRange 18).foldl (fun acc idx => if p1 idx then acc ||| (1 <<< idx.val) else acc) 0
  let m2 : Nat := (List.finRange 18).foldl (fun acc idx => if p2 idx then acc ||| (1 <<< idx.val) else acc) 0
  have hm1_bit : ∀ idx : Fin 18, m1.testBit idx.val = p1 idx := foldl_lor_testBit p1
  have hm2_bit : ∀ idx : Fin 18, m2.testBit idx.val = p2 idx := foldl_lor_testBit p2

  have auto_not_coll : ∀ (R : C) (idx : Fin 18), ((b, 0), false) ∉ R → ¬ ClauseSat (aB idx) R → ¬ Coll R := by
    intro R idx hnotf hns hcol
    apply hns
    apply colModel_sat_cols (haB_valid idx) R hcol
    intro heq
    exact hnotf (heq ▸ by simp [colAx])

  have hcov : subMask 262143 (m1 ||| m2) = true := by
    rw [subMask_iff_testBit]
    intro i hi
    rw [all18_testBit, decide_eq_true_eq] at hi
    let idx : Fin 18 := ⟨i, hi⟩
    rw [Nat.testBit_or, Bool.or_eq_true, hm1_bit idx, hm2_bit idx]
    by_contra hneither
    push Not at hneither
    have hsat := masterControl h (aB idx) (colAx (er (fin3ToRow (idxC idx))) b 0) {(b, 0)}
      (colModel_sat_rows (haB_valid idx)) (colModel_sat_cols (haB_valid idx))
      (fun v u R' hm => Finset.mem_singleton.mpr ((inEdges_mem_iff_unique (haB_edge idx)).2 v u R' hm))
      (fun v R' hm hv hnotf => by
        rw [Finset.mem_singleton] at hv; subst hv
        have hnf : ((b, 0), false) ∉ R' := hnotf (b, 0) (Finset.mem_singleton_self _)
        obtain ⟨j', hj'lt, hj'⟩ := List.getElem_of_mem hm
        rcases hiuniq ⟨j', hj'lt⟩ (by simp [hj', isNonOf]) with heq | heq
        · have hj'step : tr[i₁] = Step.non (b, 0) R' := (getElem_eq_of_fin_eq heq).symm.trans hj'
          rw [hR₁step] at hj'step; cases hj'step
          by_contra hns
          have htrue : p1 idx = true := decide_eq_true ⟨⟨hnf, auto_not_coll R₁ idx hnf hns⟩, hns⟩
          exact hneither.1 htrue
        · have hj'step : tr[i₂] = Step.non (b, 0) R' := (getElem_eq_of_fin_eq heq).symm.trans hj'
          rw [hR₂step] at hj'step; cases hj'step
          by_contra hns
          have htrue : p2 idx = true := decide_eq_true ⟨⟨hnf, auto_not_coll R₂ idx hnf hns⟩, hns⟩
          exact hneither.2 htrue)
      ∅ he (fun hc => collisionNonempty hc rfl) (fun w _ hwf => by simp at hwf)
    exact emptyUnsat _ hsat

  have foldl_lt18 : ∀ (q : Fin 18 → Bool) (k : Nat),
      ((List.finRange 18).foldl (fun acc idx => if q idx then acc ||| (1 <<< idx.val) else acc) 0).testBit k = true →
      k < 18 := by
    intro q k hk
    by_contra hge
    have hgen : ∀ (l : List (Fin 18)) (acc : Nat),
        (∀ j, acc.testBit j = true → j < 18) →
        (l.foldl (fun a idx => if q idx then a ||| (1 <<< idx.val) else a) acc).testBit k = false := by
      intro l
      induction l with
      | nil =>
        intro acc hacc
        simp only [List.foldl_nil]
        cases htk : acc.testBit k
        · rfl
        · exact (hge (hacc k htk)).elim
      | cons a tl ih =>
        intro acc hacc
        simp only [List.foldl_cons]
        apply ih
        intro j hj
        split_ifs at hj
        · rw [Nat.testBit_or, Bool.or_eq_true] at hj
          rcases hj with hj1 | hj2
          · exact hacc j hj1
          · rw [Nat.testBit_shiftLeft, Bool.and_eq_true, decide_eq_true_eq,
              Nat.testBit_one_eq_true_iff_self_eq_zero] at hj2
            omega
        · exact hacc j hj
    rw [hgen (List.finRange 18) 0 (by simp)] at hk
    cases hk

  have hreq : subMask (req1Mask pos.val) m1 = true := by
    rw [subMask_iff_testBit]
    intro i hi
    have hilt : i < 18 := foldl_lt18 (fun idx => decide ((bHole (idxC idx) (idxP idx) 4).val - 1 < pos.val)) i hi
    let idx : Fin 18 := ⟨i, hilt⟩
    rw [req1Mask_testBit pos.val idx, decide_eq_true_eq] at hi
    rw [hm1_bit idx]
    have h4pos : 0 < (bHole (idxC idx) (idxP idx) 4).val := by
      have : ∀ (c : Fin 3) (p : Fin 6), 0 < (bHole c p 4).val := by decide +kernel
      exact this (idxC idx) (idxP idx)
    let m : Fin 3 := ⟨(bHole (idxC idx) (idxP idx) 4).val - 1, by omega⟩
    have hm_succ : m.succ = bHole (idxC idx) (idxP idx) 4 := Fin.ext (by dsimp [m]; omega)
    have hmlt : m.val < pos.val := hi
    have hi₂_lt_pm : i₂.1 < (p (eh m.succ)).1 := hpos_lt m hmlt
    have hshape := z2_clause_shape h he (hzk (eh m.succ)) (hpstep (eh m.succ)) (hpuniq (eh m.succ))
    have hRkmem : Rk (eh m.succ) ∈ (tr.drop (p (eh m.succ)).1).map clauseOf := by
      refine List.mem_map.mpr ⟨Step.non (k₀, eh m.succ) (Rk (eh m.succ)), ?_, rfl⟩
      exact (mem_drop_iff tr (p (eh m.succ)).1 _).mpr ⟨p (eh m.succ), le_rfl, hpstep (eh m.succ)⟩
    by_contra hp1f
    have hsat := masterControl (h.drop (p (eh m.succ)).1) (aB idx)
      (colAx (er (fin3ToRow (idxC idx))) b 0) {(b, 0)}
      (colModel_sat_rows (haB_valid idx)) (colModel_sat_cols (haB_valid idx))
      (fun v u R' hm => Finset.mem_singleton.mpr ((inEdges_mem_iff_unique (haB_edge idx)).2 v u R' (mem_of_mem_drop hm)))
      (fun v R' hm hv hnotf => by
        rw [Finset.mem_singleton] at hv; subst hv
        have hnf : ((b, 0), false) ∉ R' := hnotf (b, 0) (Finset.mem_singleton_self _)
        obtain ⟨j', hj'le, hj'⟩ := (mem_drop_iff tr (p (eh m.succ)).1 _).mp hm
        rcases hiuniq j' (by rw [hj']; simp [isNonOf]) with rfl | rfl
        · rw [hR₁step] at hj'; cases hj'
          by_contra hns
          have htrue : p1 idx = true := decide_eq_true ⟨⟨hnf, auto_not_coll R₁ idx hnf hns⟩, hns⟩
          exact hp1f htrue
        · omega)
      (Rk (eh m.succ)) hRkmem (z2_not_coll hshape.1) (fun w _ => hshape.1 w)
    have hfk : transportF er eh (bHole (idxC idx) (idxP idx)) k₀ = eh m.succ := by
      simp [transportF, ← her4, hm_succ]
    have hne0m : (0 : Hole) ≠ eh m.succ := by
      rw [← heh0]; exact fun heq => by have := eh.injective heq; exact Fin.succ_ne_zero m this.symm
    have hicne : er (fin3ToRow (idxC idx)) ≠ k₀ := by
      rw [← her4]; exact fun heq => by have : (idxC idx).val = 4 := congrArg Fin.val (er.injective heq); omega
    exact z2_unsat_colModel hshape (haB_valid idx) hne0m hicne hbk hfk hsat

  have cor3_witness : ∀ (i : Fin tr.length) (R : C) (m : Fin 3) (mask : Nat),
      clauseOf tr[i] = R →
      (p (eh m.succ)).1 < i.1 →
      (∀ idx : Fin 18, mask.testBit idx.val = true → okR R ∧ ¬ ClauseSat (aB idx) R) →
      (∀ k, mask.testBit k = true → k < 18) →
      ∃ x ∈ witsList m (ic m), subMask mask x = true := by
    intro i R m mask hcl hlt hmask hmask18
    by_cases hok : okR R
    · let aM := colModel (er (fin3ToRow (ic m))) k₀ (eh m.succ)
        (transportF er eh (oneMustHole m (ic m)))
      have haM_valid : ValidMatch (er (fin3ToRow (ic m))) k₀ (eh m.succ)
          (transportF er eh (oneMustHole m (ic m))) := by
        rw [← her4]
        exact transport_validMatch er eh (oneMustHole_valid m (ic m))
      have hRmem : R ∈ (tr.drop i.1).map clauseOf := by
        refine List.mem_map.mpr ⟨tr[i], ?_, hcl⟩
        exact (mem_drop_iff tr i.1 _).mpr ⟨i, le_rfl, rfl⟩
      have hex_lit : ∃ l ∈ R, isWitnessLit m (ic m) (pullLit er eh l) = true := by
        by_cases hneg : ((k₀, eh m.succ), false) ∈ R
        · refine ⟨((k₀, eh m.succ), false), hneg, ?_⟩
          simp [isWitnessLit, pullLit, ← her4]
        · have hsat := masterControl (h.drop i.1) aM
            (colAx (er (fin3ToRow (ic m))) k₀ (eh m.succ)) {(k₀, eh m.succ)}
            (colModel_sat_rows haM_valid) (colModel_sat_cols haM_valid)
            (fun v u R' hm => Finset.mem_singleton.mpr ((inEdges_mem_iff_unique (hicE m)).2 v u R' (mem_of_mem_drop hm)))
            (fun v R' hm hv _ => by
              rw [Finset.mem_singleton] at hv; subst hv
              obtain ⟨j', hj'le, hj'⟩ := (mem_drop_iff tr i.1 _).mp hm
              have heq := hpuniq (eh m.succ) j' (by rw [hj']; simp [isNonOf])
              omega)
            R hRmem hok.2 (fun w hw => by rw [Finset.mem_singleton] at hw; subst hw; exact hneg)
          obtain ⟨l, hlR, hlsat⟩ := hsat
          have heval : evalLitHole (oneMustHole m (ic m)) (pullLit er eh l) = true := by
            have h' : LiteralSat (colModel (er (fin3ToRow (ic m))) (er 4) (eh m.succ)
                (transportF er eh (oneMustHole m (ic m)))) l := by
              simpa [aM, her4] using hlsat
            exact (literalSat_transport_oneMust er eh m (ic m) l).mp h'
          exact ⟨l, hlR, by simp [isWitnessLit, heval]⟩
      obtain ⟨l, hlR, hlwit⟩ := hex_lit
      have hlne : pullLit er eh l ≠ ((3, 0), false) := by
        intro heq
        have h1 : l = ((b, 0), false) := by
          rcases l with ⟨⟨r, q⟩, pol⟩
          simp only [pullLit, Prod.mk.injEq] at heq
          obtain ⟨⟨hr, hq⟩, rfl⟩ := heq
          have hr' : r = b := by rw [← er.apply_symm_apply r, hr, her3]
          have hq' : q = 0 := by rw [← eh.apply_symm_apply q, hq, heh0]
          rw [hr', hq']
        exact hok.1 (h1 ▸ hlR)
      refine ⟨fmaskList (pullLit er eh l),
        List.mem_map.mpr ⟨pullLit er eh l, List.mem_filter.mpr ⟨mem_allLits39 hlne, hlwit⟩, rfl⟩, ?_⟩
      rw [subMask_iff_testBit]
      intro k hk
      have hk18 := hmask18 k hk
      let idx : Fin 18 := ⟨k, hk18⟩
      rw [fmaskList_testBit (pullLit er eh l) idx]
      have hns := (hmask idx hk).2
      have hnl : ¬ LiteralSat (aB idx) l := fun hs => hns ⟨l, hlR, hs⟩
      have hneval : evalLitHole (bHole (idxC idx) (idxP idx)) (pullLit er eh l) ≠ true := by
        intro hev
        apply hnl
        have h' := (literalSat_transport_bHole er eh (idxC idx) (idxP idx) l).mpr hev
        simpa [aB, her3, heh0] using h'
      cases hev : evalLitHole (bHole (idxC idx) (idxP idx)) (pullLit er eh l)
      · rfl
      · exact (hneval hev).elim
    ·
      have h0 : ∀ k, mask.testBit k = false := by
        intro k
        cases hk : mask.testBit k
        · rfl
        · exfalso
          exact hok (hmask ⟨k, hmask18 k hk⟩ hk).1
      let l₀ : Literal V := ((4, m.succ), false)
      have hl₀ne : l₀ ≠ ((3, 0), false) := by intro h; dsimp only [l₀] at h; cases h
      have hl₀wit : isWitnessLit m (ic m) l₀ = true := by simp [isWitnessLit, l₀]
      refine ⟨fmaskList l₀,
        List.mem_map.mpr ⟨l₀, List.mem_filter.mpr ⟨mem_allLits39 hl₀ne, hl₀wit⟩, rfl⟩, ?_⟩
      rw [subMask_iff_testBit]
      intro k hk
      rw [h0 k] at hk; cases hk

  have hm1_prop : ∀ idx : Fin 18, m1.testBit idx.val = true → okR R₁ ∧ ¬ ClauseSat (aB idx) R₁ := by
    intro idx hbit
    rw [hm1_bit idx] at hbit
    exact of_decide_eq_true hbit
  have hm2_prop : ∀ idx : Fin 18, m2.testBit idx.val = true → okR R₂ ∧ ¬ ClauseSat (aB idx) R₂ := by
    intro idx hbit
    rw [hm2_bit idx] at hbit
    exact of_decide_eq_true hbit
  have hcl1 : clauseOf tr[i₁] = R₁ := by rw [hR₁step]; rfl
  have hcl2 : clauseOf tr[i₂] = R₂ := by rw [hR₂step]; rfl
  exact killer_masks_impossible (ic 0) (ic 1) (ic 2) pos m1 m2
    (cor3_witness i₁ R₁ 0 m1 hcl1 hp1_lt_i₁ hm1_prop (foldl_lt18 p1))
    (cor3_witness i₁ R₁ 1 m1 hcl1 (lt_trans hord21 hp1_lt_i₁) hm1_prop (foldl_lt18 p1))
    (cor3_witness i₁ R₁ 2 m1 hcl1 (lt_trans hord32 (lt_trans hord21 hp1_lt_i₁)) hm1_prop (foldl_lt18 p1))
    hreq
    (fun h0 => cor3_witness i₂ R₂ 0 m2 hcl2 (hpos_ge 0 (by omega)) hm2_prop (foldl_lt18 p2))
    (fun h1 => cor3_witness i₂ R₂ 1 m2 hcl2 (hpos_ge 1 (by omega)) hm2_prop (foldl_lt18 p2))
    (fun h2 => cor3_witness i₂ R₂ 2 m2 hcl2 (hpos_ge 2 (by omega)) hm2_prop (foldl_lt18 p2))
    hcov

theorem refutationLower {π : List C} (hπ : IsRefutation (PHP 5 4) π) :
    110 ≤ π.length := by
  classical
  obtain ⟨tr, hmap, htr⟩ := of_isDerivation hπ.1
  have hlen : tr.length = π.length := by rw [← hmap, List.length_map]
  have he : (∅ : C) ∈ tr.map clauseOf := hmap ▸ hπ.2
  have hax := ax_lower htr he
  have hdec := length_decomp tr
  rw [← hlen, hdec]
  by_cases hex : ∃ j : Hole, ∃ k : Row, k ∈ Z2 tr j
  · obtain ⟨j₀, k₀, hk₀⟩ := hex
    by_cases htwo : ∃ k₁ : Row, k₁ ∈ Z2 tr j₀ ∧ k₁ ≠ k₀
    ·
      obtain ⟨k₁, hk₁, hne10⟩ := htwo
      have hother : ∀ j : Hole, j ≠ j₀ → 17 ≤ holeCost tr j := by
        intro j hne
        apply holeCost_ge_17_of_Z2_empty htr he
        ext k
        simp only [Finset.notMem_empty, iff_false]
        intro hk
        have e0 := z2_line htr he hk hk₀
        have e1 := z2_line htr he hk hk₁
        rcases e0 with rfl | h0
        · rcases e1 with h1 | h1
          · exact hne10 h1.symm
          · exact hne h1
        · exact hne h0
      have hsum : 65 ≤ ∑ j : Hole, holeCost tr j := by
        have hsplit := Finset.add_sum_erase Finset.univ (holeCost tr) (Finset.mem_univ j₀)
        have h14 := holeCost_ge_14 htr he j₀
        have hrest : 51 ≤ ∑ j ∈ Finset.univ.erase j₀, holeCost tr j := by
          calc 51 = ∑ _j ∈ (Finset.univ : Finset Hole).erase j₀, 17 := by
                rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j₀)]
                have h4 : (Finset.univ : Finset Hole).card = 4 := by decide +kernel
                rw [h4]; decide +kernel
            _ ≤ ∑ j ∈ Finset.univ.erase j₀, holeCost tr j :=
                Finset.sum_le_sum (fun j hj => hother j (Finset.mem_erase.mp hj).1)
        omega
      omega
    ·
      push Not at htwo
      have hsub : ∀ j : Hole, Z2 tr j = ∅ ∨ Z2 tr j = {k₀} := by
        intro j
        by_cases hemp : Z2 tr j = ∅
        · exact Or.inl hemp
        · right
          obtain ⟨k, hk⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
          have hkeq : k = k₀ := by
            by_cases hjj : j = j₀
            · subst hjj; exact htwo k hk
            · rcases z2_line htr he hk hk₀ with h1 | h2
              · exact h1
              · exact (hjj h2).elim
          ext x
          simp only [Finset.mem_singleton]
          constructor
          · intro hx
            by_cases hjj : j = j₀
            · subst hjj; exact htwo x hx
            · rcases z2_line htr he hx hk₀ with h1 | h2
              · exact h1
              · exact (hjj h2).elim
          · rintro rfl; exact hkeq ▸ hk
      have hall16 : ∀ j : Hole, 16 ≤ holeCost tr j := by
        intro j
        rcases hsub j with h0 | h1
        · have := holeCost_ge_17_of_Z2_empty htr he h0; omega
        · exact (holeCost_of_Z2_singleton htr he h1).1
      by_cases hex17 : ∃ j₁ : Hole, 17 ≤ holeCost tr j₁
      · obtain ⟨j₁, hj₁⟩ := hex17
        have hsum : 65 ≤ ∑ j : Hole, holeCost tr j := by
          have hsplit := Finset.add_sum_erase Finset.univ (holeCost tr) (Finset.mem_univ j₁)
          have hrest : 48 ≤ ∑ j ∈ Finset.univ.erase j₁, holeCost tr j := by
            calc 48 = ∑ _j ∈ (Finset.univ : Finset Hole).erase j₁, 16 := by
                  rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ j₁)]
                  have h4 : (Finset.univ : Finset Hole).card = 4 := by decide +kernel
                  rw [h4]; decide +kernel
              _ ≤ ∑ j ∈ Finset.univ.erase j₁, holeCost tr j :=
                  Finset.sum_le_sum (fun j _ => hall16 j)
          omega
        omega
      · push Not at hex17
        have hall_eq16 : ∀ j : Hole, holeCost tr j = 16 := fun j => by
          have h1 := hall16 j; have h2 := hex17 j; omega
        have hall_Z : ∀ j : Hole, Z2 tr j = {k₀} := by
          intro j
          rcases hsub j with h0 | h1
          · exfalso
            have := holeCost_ge_17_of_Z2_empty htr he h0
            have := hall_eq16 j
            omega
          · exact h1
        exact (caseA_impossible htr he k₀ hall_Z hall_eq16).elim
  ·
    push Not at hex
    have hsum : 68 ≤ ∑ j : Hole, holeCost tr j := by
      calc 68 = ∑ _j : Hole, 17 := by decide +kernel
        _ ≤ ∑ j : Hole, holeCost tr j := by
          apply Finset.sum_le_sum
          intro j _
          apply holeCost_ge_17_of_Z2_empty htr he
          ext k
          simp [hex j k]
    omega

end PEqualNP.Outside.L_pcx_162

theorem PEqualNP.Outside.L_pcx_162 : ¬ (∃ π : List (PEqualNP.ProofComplexity.Clause (Fin 5 × Fin 4)), PEqualNP.ProofComplexity.IsRefutation (PEqualNP.ProofComplexity.PHP 5 4) π ∧ π.length ≤ 109) := by
  rintro ⟨π, hπ, hlen⟩
  have := PEqualNP.Outside.L_pcx_162.refutationLower hπ
  omega
