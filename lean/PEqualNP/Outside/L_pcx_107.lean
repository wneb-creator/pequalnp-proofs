import PEqualNP.Defs
import Mathlib.Data.Nat.Fib.Basic

namespace PEqualNP.Outside.L_pcx_107

def IsFalsified {n : ℕ} (A : Fin n → Fin n → Prop) (ρ : Fin n → Option Bool) : Prop :=
  ∃ u v : Fin n, A u v ∧ ρ u = some false ∧ ρ v = some false

def HasTrues {n : ℕ} (t : ℕ) (ρ : Fin n → Option Bool) : Prop :=
  ∃ S : Finset (Fin n), S.card = t ∧ ∀ x ∈ S, ρ x = some true

def ValidN (n : ℕ) (A : Fin n → Fin n → Prop) (t : ℕ) (N : (Fin n → Option Bool) → ℕ) : Prop :=
  ∀ ρ : Fin n → Option Bool,
    (((IsFalsified A ρ ∨ HasTrues t ρ) ∧ 1 ≤ N ρ) ∨
      ∃ y : Fin n, ρ y = none ∧
        N (Function.update ρ y (some false)) + N (Function.update ρ y (some true)) ≤ N ρ)

def VCGe {n : ℕ} (A : Fin n → Fin n → Prop) (t : ℕ) : Prop :=
  ∀ R : Finset (Fin n), (∀ u v : Fin n, A u v → u ∈ R ∨ v ∈ R) → t ≤ R.card

def noneCount {n : ℕ} (ρ : Fin n → Option Bool) : ℕ :=
  (Finset.univ.filter (fun x => ρ x = none)).card

def trueCount {n : ℕ} (ρ : Fin n → Option Bool) : ℕ :=
  (Finset.univ.filter (fun x => ρ x = some true)).card

lemma noneCount_update_some {n : ℕ} (ρ : Fin n → Option Bool) (y : Fin n) (b : Bool)
    (hy : ρ y = none) :
    noneCount (Function.update ρ y (some b)) + 1 = noneCount ρ := by
  unfold noneCount
  have h1 :
      Finset.univ.filter (fun x => Function.update ρ y (some b) x = none) =
        (Finset.univ.filter (fun x => ρ x = none)).erase y := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    by_cases hxy : x = y
    · subst hxy
      simp
    · simp [hxy]
  rw [h1]
  have hmem : y ∈ Finset.univ.filter (fun x => ρ x = none) := by
    simp [hy]
  exact Finset.card_erase_add_one hmem

lemma trueCount_update_true {n : ℕ} (ρ : Fin n → Option Bool) (y : Fin n) (hy : ρ y = none) :
    trueCount (Function.update ρ y (some true)) = trueCount ρ + 1 := by
  unfold trueCount
  have h1 :
      Finset.univ.filter (fun x => Function.update ρ y (some true) x = some true) =
        insert y (Finset.univ.filter (fun x => ρ x = some true)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
    by_cases hxy : x = y
    · subst hxy
      simp
    · simp [hxy]
  rw [h1, Finset.card_insert_of_notMem]
  simp [hy]

lemma trueCount_update_false {n : ℕ} (ρ : Fin n → Option Bool) (y : Fin n) (hy : ρ y = none) :
    trueCount (Function.update ρ y (some false)) = trueCount ρ := by
  unfold trueCount
  congr 1
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hxy : x = y
  · subst hxy
    simp [hy]
  · simp [hxy]

lemma trueCount_none (n : ℕ) : trueCount (fun _ : Fin n => (none : Option Bool)) = 0 := by
  unfold trueCount
  simp

lemma hasTrues_iff_le_trueCount {n t : ℕ} {ρ : Fin n → Option Bool} :
    HasTrues t ρ ↔ t ≤ trueCount ρ := by
  unfold HasTrues trueCount
  constructor
  · rintro ⟨S, hcard, hS⟩
    have hsub : S ⊆ Finset.univ.filter (fun x => ρ x = some true) := by
      intro x hx
      simp [hS x hx]
    calc t = S.card := hcard.symm
      _ ≤ (Finset.univ.filter (fun x => ρ x = some true)).card := Finset.card_le_card hsub
  · intro hle
    obtain ⟨S, hsub, hcard⟩ := Finset.exists_subset_card_eq hle
    refine ⟨S, hcard, fun x hx => ?_⟩
    have := hsub hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at this
    exact this

lemma not_isFalsified_update_true {n : ℕ} {A : Fin n → Fin n → Prop}
    {ρ : Fin n → Option Bool} {y : Fin n} (hf : ¬ IsFalsified A ρ) :
    ¬ IsFalsified A (Function.update ρ y (some true)) := by
  rintro ⟨u, v, huv, hu, hv⟩
  apply hf
  have huy : u ≠ y := by
    intro h; subst h; simp at hu
  have hvy : v ≠ y := by
    intro h; subst h; simp at hv
  rw [Function.update_of_ne huy] at hu
  rw [Function.update_of_ne hvy] at hv
  exact ⟨u, v, huv, hu, hv⟩

lemma validN_pos {n t : ℕ} {A : Fin n → Fin n → Prop} {N : (Fin n → Option Bool) → ℕ}
    (hN : ValidN n A t N) : ∀ ρ, 1 ≤ N ρ := by
  intro ρ
  suffices ∀ m ρ, noneCount ρ = m → 1 ≤ N ρ from this (noneCount ρ) ρ rfl
  intro m
  induction m with
  | zero =>
    intro ρ h0
    rcases hN ρ with ⟨_, h1⟩ | ⟨y, hy, _⟩
    · exact h1
    · have := noneCount_update_some ρ y false hy
      omega
  | succ m ih =>
    intro ρ hm
    rcases hN ρ with ⟨_, h1⟩ | ⟨y, hy, hsum⟩
    · exact h1
    · have h0 := ih (Function.update ρ y (some false)) (by
        have := noneCount_update_some ρ y false hy; omega)
      have h1 := ih (Function.update ρ y (some true)) (by
        have := noneCount_update_some ρ y true hy; omega)
      omega

-- Universal lower bound: if not falsified, at least (t - trueCount ρ) + 1 leaves.
lemma validN_ge_rem_add_one {n t : ℕ} {A : Fin n → Fin n → Prop} {N : (Fin n → Option Bool) → ℕ}
    (hN : ValidN n A t N) :
    ∀ ρ, ¬ IsFalsified A ρ → (t - trueCount ρ) + 1 ≤ N ρ := by
  intro ρ
  suffices ∀ m ρ, noneCount ρ = m → ¬ IsFalsified A ρ → (t - trueCount ρ) + 1 ≤ N ρ from
    this (noneCount ρ) ρ rfl
  intro m
  induction m with
  | zero =>
    intro ρ hm hnf
    rcases hN ρ with ⟨hf | ht, h1⟩ | ⟨y, hy, _⟩
    · exact absurd hf hnf
    · have hle := hasTrues_iff_le_trueCount.mp ht
      omega
    · have := noneCount_update_some ρ y false hy
      omega
  | succ m ih =>
    intro ρ hm hnf
    rcases hN ρ with ⟨hf | ht, h1⟩ | ⟨y, hy, hsum⟩
    · exact absurd hf hnf
    · have hle := hasTrues_iff_le_trueCount.mp ht
      omega
    · have hpos : 1 ≤ N (Function.update ρ y (some false)) := validN_pos hN _
      have h1 := ih (Function.update ρ y (some true))
        (by have := noneCount_update_some ρ y true hy; omega)
        (not_isFalsified_update_true hnf)
      rw [trueCount_update_true ρ y hy] at h1
      omega

-- Inductive upper bound predicate and conversion to ValidN.
inductive HasBound {n : ℕ} (A : Fin n → Fin n → Prop) (t : ℕ) : (Fin n → Option Bool) → ℕ → Prop
  | leaf_false {ρ k} : IsFalsified A ρ → 1 ≤ k → HasBound A t ρ k
  | leaf_true {ρ k} : HasTrues t ρ → 1 ≤ k → HasBound A t ρ k
  | branch {ρ y k0 k1 k} :
      ρ y = none →
      HasBound A t (Function.update ρ y (some false)) k0 →
      HasBound A t (Function.update ρ y (some true)) k1 →
      k0 + k1 ≤ k →
      HasBound A t ρ k

lemma exists_hasBound {n t : ℕ} {A : Fin n → Fin n → Prop} (hτ : VCGe A t) :
    ∀ ρ : Fin n → Option Bool, ∃ k : ℕ, HasBound A t ρ k := by
  intro ρ
  suffices ∀ m ρ, noneCount ρ = m → ∃ k, HasBound A t ρ k from this (noneCount ρ) ρ rfl
  intro m
  induction m with
  | zero =>
    intro ρ h0
    have hne_none : ∀ x : Fin n, ρ x ≠ none := by
      intro x hx
      have := noneCount_update_some ρ x false hx
      omega
    let R : Finset (Fin n) := Finset.univ.filter (fun x => ρ x = some true)
    by_cases hcov : ∀ u v : Fin n, A u v → u ∈ R ∨ v ∈ R
    · have hle : t ≤ R.card := hτ R hcov
      have ht : HasTrues t ρ := hasTrues_iff_le_trueCount.mpr hle
      exact ⟨1, HasBound.leaf_true ht le_rfl⟩
    · push Not at hcov
      obtain ⟨u, v, huv, hu, hv⟩ := hcov
      have huf : ρ u = some false := by
        cases h : ρ u with
        | none => exact absurd h (hne_none u)
        | some b =>
          cases b
          · rfl
          · exfalso; apply hu; simp [R, h]
      have hvf : ρ v = some false := by
        cases h : ρ v with
        | none => exact absurd h (hne_none v)
        | some b =>
          cases b
          · rfl
          · exfalso; apply hv; simp [R, h]
      exact ⟨1, HasBound.leaf_false ⟨u, v, huv, huf, hvf⟩ le_rfl⟩
  | succ m ih =>
    intro ρ hm
    have hpos : 0 < (Finset.univ.filter (fun x => ρ x = none)).card := by
      unfold noneCount at hm; omega
    obtain ⟨y, hy_mem⟩ := Finset.card_pos.mp hpos
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy_mem
    obtain ⟨k0, h0⟩ := ih (Function.update ρ y (some false)) (by
      have := noneCount_update_some ρ y false hy_mem; omega)
    obtain ⟨k1, h1⟩ := ih (Function.update ρ y (some true)) (by
      have := noneCount_update_some ρ y true hy_mem; omega)
    exact ⟨k0 + k1, HasBound.branch hy_mem h0 h1 le_rfl⟩

theorem hasBound_to_validN {n t k : ℕ} {A : Fin n → Fin n → Prop}
    (hτ : VCGe A t) (hb : HasBound A t (fun _ => none) k) :
    ∃ N : (Fin n → Option Bool) → ℕ, N (fun _ => none) ≤ k ∧ ValidN n A t N := by
  classical
  let hex := fun ρ => exists_hasBound hτ ρ
  let N : (Fin n → Option Bool) → ℕ := fun ρ => Nat.find (hex ρ)
  refine ⟨N, Nat.find_min' (hex _) hb, fun ρ => ?_⟩
  have hspec : HasBound A t ρ (N ρ) := Nat.find_spec (hex ρ)
  cases hspec with
  | leaf_false hf h1 => exact Or.inl ⟨Or.inl hf, h1⟩
  | leaf_true ht h1 => exact Or.inl ⟨Or.inr ht, h1⟩
  | branch hy h0 h1 hsum =>
    right
    refine ⟨_, hy, ?_⟩
    have h0' : N _ ≤ _ := Nat.find_min' (hex _) h0
    have h1' : N _ ≤ _ := Nat.find_min' (hex _) h1
    omega

-- ============================================================
-- PART 4 (and upper bound for Part 5 and Part 3): General upper bound <= 2^(r+1) - 1
-- ============================================================

lemma pow2_ge_one (r : ℕ) : 1 ≤ 2 ^ r := Nat.one_le_pow r 2 (by omega)

lemma hasBound_general {n t : ℕ} {A : Fin n → Fin n → Prop}
    (hirr : ∀ u, ¬ A u u) (hτ : VCGe A t) :
    ∀ r (ρ : Fin n → Option Bool), t - trueCount ρ ≤ r →
      HasBound A t ρ (2 ^ (r + 1) - 1) := by
  intro r
  induction r with
  | zero =>
    intro ρ hr
    have ht : HasTrues t ρ := hasTrues_iff_le_trueCount.mpr (by omega)
    exact HasBound.leaf_true ht (by norm_num)
  | succ r ih =>
    intro ρ hr
    by_cases ht : t ≤ trueCount ρ
    · exact HasBound.leaf_true (hasTrues_iff_le_trueCount.mpr ht)
        (by have := pow2_ge_one (r + 1); omega)
    · by_cases hf : IsFalsified A ρ
      · exact HasBound.leaf_false hf (by have := pow2_ge_one (r + 1); omega)
      · let R : Finset (Fin n) := Finset.univ.filter (fun x => ρ x = some true)
        have hRcard : R.card < t := by
          unfold trueCount at ht; exact lt_of_not_ge ht
        have hncov : ¬ ∀ u v : Fin n, A u v → u ∈ R ∨ v ∈ R := by
          intro hcov
          have := hτ R hcov
          omega
        push Not at hncov
        obtain ⟨u, v, huv, hu, hv⟩ := hncov
        have hu_nt : ρ u ≠ some true := by
          intro h; apply hu; simp [R, h]
        have hv_nt : ρ v ≠ some true := by
          intro h; apply hv; simp [R, h]
        have huv_ne : u ≠ v := by
          intro h; subst h; exact hirr u huv
        cases hru : ρ u with
        | some bu =>
          cases bu with
          | true => exact absurd hru hu_nt
          | false =>
            cases hrv : ρ v with
            | some bv =>
              cases bv with
              | true => exact absurd hrv hv_nt
              | false => exact absurd ⟨u, v, huv, hru, hrv⟩ hf
            | none =>
              have h0 : HasBound A t (Function.update ρ v (some false)) 1 :=
                HasBound.leaf_false
                  ⟨u, v, huv, by rw [Function.update_of_ne huv_ne]; exact hru, by simp⟩ le_rfl
              have h1 : HasBound A t (Function.update ρ v (some true)) (2 ^ (r + 1) - 1) :=
                ih _ (by rw [trueCount_update_true ρ v hrv]; omega)
              refine HasBound.branch hrv h0 h1 ?_
              have hp : 1 ≤ 2 ^ (r + 1) := pow2_ge_one (r + 1)
              have : 2 ^ (r + 2) = 2 * 2 ^ (r + 1) := by ring
              omega
        | none =>
          cases hrv : ρ v with
          | some bv =>
            cases bv with
            | true => exact absurd hrv hv_nt
            | false =>
              have h0 : HasBound A t (Function.update ρ u (some false)) 1 :=
                HasBound.leaf_false
                  ⟨u, v, huv, by simp, by rw [Function.update_of_ne huv_ne.symm]; exact hrv⟩ le_rfl
              have h1 : HasBound A t (Function.update ρ u (some true)) (2 ^ (r + 1) - 1) :=
                ih _ (by rw [trueCount_update_true ρ u hru]; omega)
              refine HasBound.branch hru h0 h1 ?_
              have hp : 1 ≤ 2 ^ (r + 1) := pow2_ge_one (r + 1)
              have : 2 ^ (r + 2) = 2 * 2 ^ (r + 1) := by ring
              omega
          | none =>
            let ρ0 := Function.update ρ u (some false)
            have hρ0v : ρ0 v = none := by
              show Function.update ρ u (some false) v = none
              rw [Function.update_of_ne huv_ne.symm, hrv]
            have h00 : HasBound A t (Function.update ρ0 v (some false)) 1 :=
              HasBound.leaf_false
                ⟨u, v, huv,
                  by rw [Function.update_of_ne huv_ne]; simp [ρ0],
                  by simp⟩ le_rfl
            have h01 : HasBound A t (Function.update ρ0 v (some true)) (2 ^ (r + 1) - 1) := by
              apply ih
              rw [trueCount_update_true ρ0 v hρ0v, trueCount_update_false ρ u hru]
              omega
            have h0 : HasBound A t ρ0 (1 + (2 ^ (r + 1) - 1)) :=
              HasBound.branch hρ0v h00 h01 le_rfl
            have h1 : HasBound A t (Function.update ρ u (some true)) (2 ^ (r + 1) - 1) :=
              ih _ (by rw [trueCount_update_true ρ u hru]; omega)
            refine HasBound.branch hru h0 h1 ?_
            have hp : 1 ≤ 2 ^ (r + 1) := pow2_ge_one (r + 1)
            have : 2 ^ (r + 2) = 2 * 2 ^ (r + 1) := by ring
            omega

-- ============================================================
-- SHARED LOWER BOUND ENGINE FOR FORCED VERTICES (max degree <= 1 and <= 2)
-- ============================================================

noncomputable def forcedSet {n : ℕ} (A : Fin n → Fin n → Prop) (ρ : Fin n → Option Bool) :
    Finset (Fin n) :=
  letI := Classical.decPred (fun x : Fin n => ρ x = none ∧ ∃ u : Fin n, A x u ∧ ρ u = some false)
  Finset.univ.filter (fun x => ρ x = none ∧ ∃ u : Fin n, A x u ∧ ρ u = some false)

lemma forcedSet_none {n : ℕ} (A : Fin n → Fin n → Prop) :
    (forcedSet A (fun _ => none)).card = 0 := by
  classical
  unfold forcedSet
  simp

lemma forcedSet_update_true_of_mem {n : ℕ} (A : Fin n → Fin n → Prop)
    (ρ : Fin n → Option Bool) (y : Fin n) (hy : y ∈ forcedSet A ρ) :
    (forcedSet A (Function.update ρ y (some true))).card + 1 = (forcedSet A ρ).card := by
  classical
  have heq : forcedSet A (Function.update ρ y (some true)) = (forcedSet A ρ).erase y := by
    ext x
    unfold forcedSet
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase]
    by_cases hxy : x = y
    · subst hxy
      simp
    · constructor
      · rintro ⟨hx, u, hxu, hu⟩
        have huy : u ≠ y := by intro h; subst h; simp at hu
        rw [Function.update_of_ne hxy] at hx
        rw [Function.update_of_ne huy] at hu
        exact ⟨hxy, hx, u, hxu, hu⟩
      · rintro ⟨_, hx, u, hxu, hu⟩
        have huy : u ≠ y := by
          intro h; subst h
          unfold forcedSet at hy
          simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
          rw [hy.1] at hu
          simp at hu
        refine ⟨by rw [Function.update_of_ne hxy]; exact hx, u, hxu, ?_⟩
        rw [Function.update_of_ne huy]
        exact hu
  rw [heq]
  exact Finset.card_erase_add_one hy

lemma forcedSet_update_true_of_notMem {n : ℕ} (A : Fin n → Fin n → Prop)
    (ρ : Fin n → Option Bool) (y : Fin n) (hy_none : ρ y = none) (hy : y ∉ forcedSet A ρ) :
    (forcedSet A (Function.update ρ y (some true))).card = (forcedSet A ρ).card := by
  classical
  congr 1
  ext x
  unfold forcedSet
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hxy : x = y
  · subst hxy
    simp only [Function.update_self, reduceCtorEq, false_and, false_iff]
    intro h
    apply hy
    unfold forcedSet
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact h
  · constructor
    · rintro ⟨hx, u, hxu, hu⟩
      have huy : u ≠ y := by intro h; subst h; simp at hu
      rw [Function.update_of_ne hxy] at hx
      rw [Function.update_of_ne huy] at hu
      exact ⟨hx, u, hxu, hu⟩
    · rintro ⟨hx, u, hxu, hu⟩
      have huy : u ≠ y := by intro h; subst h; rw [hy_none] at hu; simp at hu
      refine ⟨by rw [Function.update_of_ne hxy]; exact hx, u, hxu, ?_⟩
      rw [Function.update_of_ne huy]
      exact hu

lemma forcedSet_update_false_card_le {n d : ℕ} (A : Fin n → Fin n → Prop)
    (hsym : ∀ u v, A u v → A v u)
    (hdeg : ∀ u, (letI := Classical.decPred (A u); (Finset.univ.filter (A u)).card ≤ d))
    (ρ : Fin n → Option Bool) (y : Fin n) :
    (forcedSet A (Function.update ρ y (some false))).card ≤ (forcedSet A ρ).card + d := by
  classical
  have hsub : forcedSet A (Function.update ρ y (some false)) ⊆
      forcedSet A ρ ∪ Finset.univ.filter (A y) := by
    intro x hx
    unfold forcedSet at hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
    obtain ⟨hx_none, u, hxu, hu⟩ := hx
    have hxy : x ≠ y := by intro h; subst h; simp at hx_none
    rw [Function.update_of_ne hxy] at hx_none
    by_cases huy : u = y
    · subst huy
      apply Finset.mem_union_right
      simp [hsym x u hxu]
    · apply Finset.mem_union_left
      unfold forcedSet
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [Function.update_of_ne huy] at hu
      exact ⟨hx_none, u, hxu, hu⟩
  calc (forcedSet A (Function.update ρ y (some false))).card
      ≤ (forcedSet A ρ ∪ Finset.univ.filter (A y)).card := Finset.card_le_card hsub
    _ ≤ (forcedSet A ρ).card + (Finset.univ.filter (A y)).card := Finset.card_union_le _ _
    _ ≤ (forcedSet A ρ).card + d := Nat.add_le_add_left (by convert hdeg y) _

lemma not_isFalsified_update_false_of_notMem {n : ℕ} {A : Fin n → Fin n → Prop}
    (hsym : ∀ u v, A u v → A v u) (hirr : ∀ u, ¬ A u u)
    {ρ : Fin n → Option Bool} {y : Fin n} (hnf : ¬ IsFalsified A ρ)
    (hy_none : ρ y = none) (hy : y ∉ forcedSet A ρ) :
    ¬ IsFalsified A (Function.update ρ y (some false)) := by
  rintro ⟨u, v, huv, hu, hv⟩
  by_cases huy : u = y
  · subst huy
    have hvy : v ≠ u := by intro h; subst h; exact hirr v huv
    rw [Function.update_of_ne hvy] at hv
    apply hy
    classical
    unfold forcedSet
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hy_none, v, huv, hv⟩
  · by_cases hvy : v = y
    · subst hvy
      rw [Function.update_of_ne huy] at hu
      apply hy
      classical
      unfold forcedSet
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hy_none, u, hsym u v huv, hu⟩
    · rw [Function.update_of_ne huy] at hu
      rw [Function.update_of_ne hvy] at hv
      exact hnf ⟨u, v, huv, hu, hv⟩

-- ============================================================
-- LOWER BOUND FOR MAX DEGREE <= 1 (Matchings)
-- ============================================================

def fMatch (s r : ℕ) : ℕ := min s r + (2 ^ (r - s + 1) - 1)

lemma fMatch_zero_r (s : ℕ) : fMatch s 0 = 1 := by
  simp [fMatch]

lemma fMatch_zero_s (r : ℕ) : fMatch 0 r = 2 ^ (r + 1) - 1 := by
  simp [fMatch]

lemma fMatch_step_forced (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    fMatch s r = 1 + fMatch (s - 1) (r - 1) := by
  unfold fMatch
  have h1 : min s r = min (s - 1) (r - 1) + 1 := by omega
  have h2 : r - 1 - (s - 1) = r - s := by omega
  rw [h1, h2]
  omega

lemma fMatch_anti (s1 s2 r : ℕ) (h : s1 ≤ s2) : fMatch s2 r ≤ fMatch s1 r := by
  suffices ∀ s r, fMatch (s + 1) r ≤ fMatch s r by
    induction h with
    | refl => exact le_rfl
    | step _ ih => exact le_trans (this _ r) ih
  intro s r
  unfold fMatch
  by_cases hsr : s < r
  · have hm1 : min (s + 1) r = s + 1 := by omega
    have hm2 : min s r = s := by omega
    have hd : r - s = (r - (s + 1)) + 1 := by omega
    rw [hm1, hm2, hd]
    have hp : 1 ≤ 2 ^ (r - (s + 1) + 1) := pow2_ge_one _
    have hpow : 2 ^ (r - (s + 1) + 1 + 1) = 2 * 2 ^ (r - (s + 1) + 1) := by ring
    omega
  · have hm1 : min (s + 1) r = r := by omega
    have hm2 : min s r = r := by omega
    have hd1 : r - (s + 1) = 0 := by omega
    have hd2 : r - s = 0 := by omega
    rw [hm1, hm2, hd1, hd2]

lemma fMatch_branch (s r : ℕ) (hr : 1 ≤ r) :
    fMatch s r ≤ fMatch (s + 1) r + fMatch s (r - 1) := by
  unfold fMatch
  by_cases hsr : s < r
  · have hm0 : min s r = s := by omega
    have hm1 : min (s + 1) r = s + 1 := by omega
    have hm2 : min s (r - 1) = s := by omega
    have hd1 : r - (s + 1) + 1 = r - s := by omega
    have hd2 : r - 1 - s + 1 = r - s := by omega
    rw [hm0, hm1, hm2, hd1, hd2]
    have hp : 1 ≤ 2 ^ (r - s) := pow2_ge_one _
    have hpow : 2 ^ (r - s + 1) = 2 * 2 ^ (r - s) := by ring
    omega
  · have hm0 : min s r = r := by omega
    have hm1 : min (s + 1) r = r := by omega
    have hm2 : min s (r - 1) = r - 1 := by omega
    have hd0 : r - s = 0 := by omega
    have hd1 : r - (s + 1) = 0 := by omega
    have hd2 : r - 1 - s = 0 := by omega
    rw [hm0, hm1, hm2, hd0, hd1, hd2]
    omega

theorem max_deg_one_lower_bound {n t : ℕ} {A : Fin n → Fin n → Prop}
    {N : (Fin n → Option Bool) → ℕ}
    (hN : ValidN n A t N)
    (hsym : ∀ u v, A u v → A v u)
    (hirr : ∀ u, ¬ A u u)
    (hdeg : ∀ u, (letI := Classical.decPred (A u); (Finset.univ.filter (A u)).card ≤ 1)) :
    ∀ ρ, ¬ IsFalsified A ρ → fMatch (forcedSet A ρ).card (t - trueCount ρ) ≤ N ρ := by
  intro ρ
  suffices ∀ m ρ, noneCount ρ = m → ¬ IsFalsified A ρ →
      fMatch (forcedSet A ρ).card (t - trueCount ρ) ≤ N ρ from
    this (noneCount ρ) ρ rfl
  intro m
  induction m with
  | zero =>
    intro ρ h0 hnf
    rcases hN ρ with ⟨hf | ht, h1⟩ | ⟨y, hy, _⟩
    · exact absurd hf hnf
    · have hle := hasTrues_iff_le_trueCount.mp ht
      have hr0 : t - trueCount ρ = 0 := by omega
      rw [hr0, fMatch_zero_r]
      exact h1
    · have := noneCount_update_some ρ y false hy
      omega
  | succ m ih =>
    intro ρ hm hnf
    by_cases hr0 : t - trueCount ρ = 0
    · rw [hr0, fMatch_zero_r]
      exact validN_pos hN ρ
    · have hr : 1 ≤ t - trueCount ρ := by omega
      rcases hN ρ with ⟨hf | ht, h1⟩ | ⟨y, hy, hsum⟩
      · exact absurd hf hnf
      · have hle := hasTrues_iff_le_trueCount.mp ht
        omega
      · by_cases hyf : y ∈ forcedSet A ρ
        · have hpos : 1 ≤ N (Function.update ρ y (some false)) := validN_pos hN _
          have h1 := ih (Function.update ρ y (some true))
            (by have := noneCount_update_some ρ y true hy; omega)
            (not_isFalsified_update_true hnf)
          have hs1 := forcedSet_update_true_of_mem A ρ y hyf
          have ht1 := trueCount_update_true ρ y hy
          have hs_pos : 1 ≤ (forcedSet A ρ).card := by omega
          have hstep := fMatch_step_forced (forcedSet A ρ).card (t - trueCount ρ) hs_pos hr
          have hs1' : (forcedSet A (Function.update ρ y (some true))).card =
              (forcedSet A ρ).card - 1 := by omega
          have hr1' : t - trueCount (Function.update ρ y (some true)) =
              t - trueCount ρ - 1 := by omega
          rw [hs1', hr1'] at h1
          omega
        · have hnf0 := not_isFalsified_update_false_of_notMem hsym hirr hnf hy hyf
          have h0 := ih (Function.update ρ y (some false))
            (by have := noneCount_update_some ρ y false hy; omega)
            hnf0
          have h1 := ih (Function.update ρ y (some true))
            (by have := noneCount_update_some ρ y true hy; omega)
            (not_isFalsified_update_true hnf)
          have hs0 := forcedSet_update_false_card_le A hsym hdeg ρ y
          have hs1 := forcedSet_update_true_of_notMem A ρ y hy hyf
          have ht0 := trueCount_update_false ρ y hy
          have ht1 := trueCount_update_true ρ y hy
          rw [ht0] at h0
          rw [hs1, ht1] at h1
          have h0' : fMatch ((forcedSet A ρ).card + 1) (t - trueCount ρ) ≤
              N (Function.update ρ y (some false)) :=
            le_trans (fMatch_anti _ _ _ hs0) h0
          have hbr := fMatch_branch (forcedSet A ρ).card (t - trueCount ρ) hr
          have hr1' : t - (trueCount ρ + 1) = t - trueCount ρ - 1 := by omega
          rw [hr1'] at h1
          omega

-- ============================================================
-- LOWER BOUND FOR MAX DEGREE <= 2 (Paths and Cycles!)
-- ============================================================

lemma fib_add_four_ge_three (k : ℕ) : 3 ≤ Nat.fib (k + 4) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have : Nat.fib (k + 1 + 4) = Nat.fib (k + 3) + Nat.fib (k + 4) := by
      have h := Nat.fib_add_two (n := k + 3)
      simpa [Nat.add_assoc] using h
    omega

lemma fib_add_three_ge_two (k : ℕ) : 2 ≤ Nat.fib (k + 3) := by
  induction k with
  | zero => decide
  | succ k ih =>
    have h := Nat.fib_add_two (n := k + 2)
    have : Nat.fib (k + 1 + 3) = Nat.fib (k + 2) + Nat.fib (k + 3) := by
      simpa [Nat.add_assoc] using h
    omega

lemma fib_add_five_sub_four (k : ℕ) : Nat.fib (k + 4) + 2 ≤ Nat.fib (k + 5) := by
  have h1 : Nat.fib (k + 5) = Nat.fib (k + 3) + Nat.fib (k + 4) := by
    have h := Nat.fib_add_two (n := k + 3)
    simpa [Nat.add_assoc] using h
  have h2 := fib_add_three_ge_two k
  omega

def hDeg2 (s r : ℕ) : ℕ := min s r + (Nat.fib (r - s + 4) - 2)

lemma hDeg2_zero_r (s : ℕ) : hDeg2 s 0 = 1 := by
  simp [hDeg2]
  decide

lemma hDeg2_zero_s (r : ℕ) : hDeg2 0 r = Nat.fib (r + 4) - 2 := by
  simp [hDeg2]

lemma hDeg2_step_forced (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    hDeg2 s r = 1 + hDeg2 (s - 1) (r - 1) := by
  unfold hDeg2
  have h1 : min s r = min (s - 1) (r - 1) + 1 := by omega
  have h2 : r - 1 - (s - 1) = r - s := by omega
  rw [h1, h2]
  omega

lemma hDeg2_anti (s1 s2 r : ℕ) (h : s1 ≤ s2) : hDeg2 s2 r ≤ hDeg2 s1 r := by
  suffices ∀ s r, hDeg2 (s + 1) r ≤ hDeg2 s r by
    induction h with
    | refl => exact le_rfl
    | step _ ih => exact le_trans (this _ r) ih
  intro s r
  unfold hDeg2
  by_cases hsr : s < r
  · have hm1 : min (s + 1) r = s + 1 := by omega
    have hm2 : min s r = s := by omega
    have hd : r - s + 4 = (r - (s + 1)) + 5 := by omega
    rw [hm1, hm2, hd]
    have hfib := fib_add_five_sub_four (r - (s + 1))
    have hge := fib_add_four_ge_three (r - (s + 1))
    omega
  · have hm1 : min (s + 1) r = r := by omega
    have hm2 : min s r = r := by omega
    have hd1 : r - (s + 1) = 0 := by omega
    have hd2 : r - s = 0 := by omega
    rw [hm1, hm2, hd1, hd2]

lemma hDeg2_branch (s r : ℕ) (hr : 1 ≤ r) :
    hDeg2 s r ≤ hDeg2 (s + 2) r + hDeg2 s (r - 1) := by
  unfold hDeg2
  by_cases h1 : r ≤ s
  · have hm0 : min s r = r := by omega
    have hm1 : min (s + 2) r = r := by omega
    have hm2 : min s (r - 1) = r - 1 := by omega
    have hd0 : r - s = 0 := by omega
    have hd1 : r - (s + 2) = 0 := by omega
    have hd2 : r - 1 - s = 0 := by omega
    rw [hm0, hm1, hm2, hd0, hd1, hd2]
    have h4 : Nat.fib 4 = 3 := by decide
    omega
  · by_cases h2 : s + 1 = r
    · subst h2
      have hm0 : min s (s + 1) = s := by omega
      have hm1 : min (s + 2) (s + 1) = s + 1 := by omega
      have hm2 : min s (s + 1 - 1) = s := by omega
      have hd0 : s + 1 - s = 1 := by omega
      have hd1 : s + 1 - (s + 2) = 0 := by omega
      have hd2 : s + 1 - 1 - s = 0 := by omega
      rw [hm0, hm1, hm2, hd0, hd1, hd2]
      have h4 : Nat.fib (0 + 4) = 3 := by decide
      have h5 : Nat.fib (1 + 4) = 5 := by decide
      omega
    · have hlt : s + 2 ≤ r := by omega
      have hm0 : min s r = s := by omega
      have hm1 : min (s + 2) r = s + 2 := by omega
      have hm2 : min s (r - 1) = s := by omega
      rw [hm0, hm1, hm2]
      set d := r - (s + 2)
      have he0 : r - s + 4 = d + 6 := by omega
      have he1 : r - (s + 2) + 4 = d + 4 := by omega
      have he2 : r - 1 - s + 4 = d + 5 := by omega
      rw [he0, he1, he2]
      have hfib : Nat.fib (d + 6) = Nat.fib (d + 4) + Nat.fib (d + 5) := by
        have h := Nat.fib_add_two (n := d + 4)
        simpa [Nat.add_assoc] using h
      have hge1 := fib_add_four_ge_three d
      have hge2 := fib_add_four_ge_three (d + 1)
      have hge2' : 3 ≤ Nat.fib (d + 5) := by simpa [Nat.add_assoc] using hge2
      omega

theorem max_deg_two_lower_bound {n t : ℕ} {A : Fin n → Fin n → Prop}
    {N : (Fin n → Option Bool) → ℕ}
    (hN : ValidN n A t N)
    (hsym : ∀ u v, A u v → A v u)
    (hirr : ∀ u, ¬ A u u)
    (hdeg : ∀ u, (letI := Classical.decPred (A u); (Finset.univ.filter (A u)).card ≤ 2)) :
    ∀ ρ, ¬ IsFalsified A ρ → hDeg2 (forcedSet A ρ).card (t - trueCount ρ) ≤ N ρ := by
  intro ρ
  suffices ∀ m ρ, noneCount ρ = m → ¬ IsFalsified A ρ →
      hDeg2 (forcedSet A ρ).card (t - trueCount ρ) ≤ N ρ from
    this (noneCount ρ) ρ rfl
  intro m
  induction m with
  | zero =>
    intro ρ h0 hnf
    rcases hN ρ with ⟨hf | ht, h1⟩ | ⟨y, hy, _⟩
    · exact absurd hf hnf
    · have hle := hasTrues_iff_le_trueCount.mp ht
      have hr0 : t - trueCount ρ = 0 := by omega
      rw [hr0, hDeg2_zero_r]
      exact h1
    · have := noneCount_update_some ρ y false hy
      omega
  | succ m ih =>
    intro ρ hm hnf
    by_cases hr0 : t - trueCount ρ = 0
    · rw [hr0, hDeg2_zero_r]
      exact validN_pos hN ρ
    · have hr : 1 ≤ t - trueCount ρ := by omega
      rcases hN ρ with ⟨hf | ht, h1⟩ | ⟨y, hy, hsum⟩
      · exact absurd hf hnf
      · have hle := hasTrues_iff_le_trueCount.mp ht
        omega
      · by_cases hyf : y ∈ forcedSet A ρ
        · have hpos : 1 ≤ N (Function.update ρ y (some false)) := validN_pos hN _
          have h1 := ih (Function.update ρ y (some true))
            (by have := noneCount_update_some ρ y true hy; omega)
            (not_isFalsified_update_true hnf)
          have hs1 := forcedSet_update_true_of_mem A ρ y hyf
          have ht1 := trueCount_update_true ρ y hy
          have hs_pos : 1 ≤ (forcedSet A ρ).card := by omega
          have hstep := hDeg2_step_forced (forcedSet A ρ).card (t - trueCount ρ) hs_pos hr
          have hs1' : (forcedSet A (Function.update ρ y (some true))).card =
              (forcedSet A ρ).card - 1 := by omega
          have hr1' : t - trueCount (Function.update ρ y (some true)) =
              t - trueCount ρ - 1 := by omega
          rw [hs1', hr1'] at h1
          omega
        · have hnf0 := not_isFalsified_update_false_of_notMem hsym hirr hnf hy hyf
          have h0 := ih (Function.update ρ y (some false))
            (by have := noneCount_update_some ρ y false hy; omega)
            hnf0
          have h1 := ih (Function.update ρ y (some true))
            (by have := noneCount_update_some ρ y true hy; omega)
            (not_isFalsified_update_true hnf)
          have hs0 := forcedSet_update_false_card_le A hsym hdeg ρ y
          have hs1 := forcedSet_update_true_of_notMem A ρ y hy hyf
          have ht0 := trueCount_update_false ρ y hy
          have ht1 := trueCount_update_true ρ y hy
          rw [ht0] at h0
          rw [hs1, ht1] at h1
          have h0' : hDeg2 ((forcedSet A ρ).card + 2) (t - trueCount ρ) ≤
              N (Function.update ρ y (some false)) :=
            le_trans (hDeg2_anti _ _ _ hs0) h0
          have hbr := hDeg2_branch (forcedSet A ρ).card (t - trueCount ρ) hr
          have hr1' : t - (trueCount ρ + 1) = t - trueCount ρ - 1 := by omega
          rw [hr1'] at h1
          omega

-- ============================================================
-- PATH EMBEDDING UPPER BOUND (for BOTH Paths and Cycles!)
-- ============================================================

lemma hasBound_of_path_embed {n t : ℕ} {A : Fin n → Fin n → Prop} :
    ∀ r (ρ : Fin n → Option Bool) (v : Fin (2 * r) → Fin n),
      Function.Injective v →
      (∀ i, ρ (v i) = none) →
      (∀ i (hi : i + 1 < 2 * r), A (v ⟨i, by omega⟩) (v ⟨i + 1, hi⟩)) →
      t - trueCount ρ ≤ r →
      HasBound A t ρ (Nat.fib (r + 4) - 2) := by
  intro r
  induction r using Nat.strongRecOn with
  | ind r ih =>
    intro ρ v hv_inj hv_none hv_adj hr
    match r with
    | 0 =>
      have ht : HasTrues t ρ := hasTrues_iff_le_trueCount.mpr (by omega)
      have h4 : Nat.fib 4 - 2 = 1 := by decide
      rw [h4]
      exact HasBound.leaf_true ht le_rfl
    | 1 =>
      let v0 := v ⟨0, by omega⟩
      let v1 := v ⟨1, by omega⟩
      have hne : v0 ≠ v1 := by
        intro h; have := hv_inj h; simp at this
      have h0_none : ρ v0 = none := hv_none ⟨0, by omega⟩
      have h1_none : ρ v1 = none := hv_none ⟨1, by omega⟩
      have hadj01 : A v0 v1 := hv_adj 0 (by omega)
      have htrue0 : HasBound A t (Function.update ρ v0 (some true)) 1 := by
        apply HasBound.leaf_true _ le_rfl
        rw [hasTrues_iff_le_trueCount, trueCount_update_true ρ v0 h0_none]
        omega
      let ρ0 := Function.update ρ v0 (some false)
      have hρ0_v1 : ρ0 v1 = none := by
        show Function.update ρ v0 (some false) v1 = none
        rw [Function.update_of_ne hne.symm, h1_none]
      have h00 : HasBound A t (Function.update ρ0 v1 (some false)) 1 :=
        HasBound.leaf_false
          ⟨v0, v1, hadj01, by rw [Function.update_of_ne hne]; simp [ρ0], by simp⟩ le_rfl
      have h01 : HasBound A t (Function.update ρ0 v1 (some true)) 1 := by
        apply HasBound.leaf_true _ le_rfl
        rw [hasTrues_iff_le_trueCount, trueCount_update_true ρ0 v1 hρ0_v1,
          trueCount_update_false ρ v0 h0_none]
        omega
      have hfalse0 : HasBound A t ρ0 2 := HasBound.branch hρ0_v1 h00 h01 le_rfl
      have h5 : Nat.fib (1 + 4) - 2 = 3 := by decide
      rw [h5]
      exact HasBound.branch h0_none hfalse0 htrue0 le_rfl
    | r' + 2 =>
      let v0 := v ⟨0, by omega⟩
      let v1 := v ⟨1, by omega⟩
      let v2 := v ⟨2, by omega⟩
      have hne01 : v0 ≠ v1 := fun h => by have := hv_inj h; simp at this
      have hne02 : v0 ≠ v2 := fun h => by have := hv_inj h; simp at this
      have hne12 : v1 ≠ v2 := fun h => by have := hv_inj h; simp at this
      have h0_none : ρ v0 = none := hv_none ⟨0, by omega⟩
      have h1_none : ρ v1 = none := hv_none ⟨1, by omega⟩
      have h2_none : ρ v2 = none := hv_none ⟨2, by omega⟩
      have hadj01 : A v0 v1 := hv_adj 0 (by omega)
      have hadj12 : A v1 v2 := hv_adj 1 (by omega)
      -- Branch v1 = true
      let ρ_t1 := Function.update ρ v1 (some true)
      let v_t1 : Fin (2 * (r' + 1)) → Fin n := fun i => v ⟨i.val + 2, by omega⟩
      have h_t1 : HasBound A t ρ_t1 (Nat.fib (r' + 1 + 4) - 2) := by
        apply ih (r' + 1) (by omega) ρ_t1 v_t1
        · intro i j hij
          have := hv_inj hij
          ext
          have := congrArg Fin.val this
          simp at this
          omega
        · intro i
          have hne : v_t1 i ≠ v1 := by
            intro h
            have := hv_inj h
            have := congrArg Fin.val this
            simp at this
          show Function.update ρ v1 (some true) (v_t1 i) = none
          rw [Function.update_of_ne hne]
          exact hv_none _
        · intro i hi
          exact hv_adj (i + 2) (by omega)
        · rw [trueCount_update_true ρ v1 h1_none]; omega
      -- Branch v1 = false
      let ρ_f1 := Function.update ρ v1 (some false)
      have h_f1_v0 : ρ_f1 v0 = none := by
        show Function.update ρ v1 (some false) v0 = none
        rw [Function.update_of_ne hne01, h0_none]
      have h_f1_f0 : HasBound A t (Function.update ρ_f1 v0 (some false)) 1 :=
        HasBound.leaf_false
          ⟨v0, v1, hadj01, by simp, by rw [Function.update_of_ne hne01.symm]; simp [ρ_f1]⟩ le_rfl
      let ρ_f1_t0 := Function.update ρ_f1 v0 (some true)
      have h_f1_t0_v2 : ρ_f1_t0 v2 = none := by
        show Function.update ρ_f1 v0 (some true) v2 = none
        rw [Function.update_of_ne hne02.symm]
        show Function.update ρ v1 (some false) v2 = none
        rw [Function.update_of_ne hne12.symm, h2_none]
      have h_f1_t0_f2 : HasBound A t (Function.update ρ_f1_t0 v2 (some false)) 1 :=
        HasBound.leaf_false
          ⟨v1, v2, hadj12,
            by
              rw [Function.update_of_ne hne12]
              show Function.update ρ_f1 v0 (some true) v1 = some false
              rw [Function.update_of_ne hne01.symm]
              simp [ρ_f1],
            by simp⟩ le_rfl
      let ρ_f1_t0_t2 := Function.update ρ_f1_t0 v2 (some true)
      let v_r : Fin (2 * r') → Fin n := fun i => v ⟨i.val + 3, by omega⟩
      have h_f1_t0_t2 : HasBound A t ρ_f1_t0_t2 (Nat.fib (r' + 4) - 2) := by
        apply ih r' (by omega) ρ_f1_t0_t2 v_r
        · intro i j hij
          have := hv_inj hij
          ext
          have := congrArg Fin.val this
          simp at this
          omega
        · intro i
          have hne0 : v_r i ≠ v0 := fun h => by
            have := congrArg Fin.val (hv_inj h); simp at this
          have hne1 : v_r i ≠ v1 := fun h => by
            have := congrArg Fin.val (hv_inj h); simp at this
          have hne2 : v_r i ≠ v2 := fun h => by
            have := congrArg Fin.val (hv_inj h); simp at this
          show Function.update ρ_f1_t0 v2 (some true) (v_r i) = none
          rw [Function.update_of_ne hne2]
          show Function.update ρ_f1 v0 (some true) (v_r i) = none
          rw [Function.update_of_ne hne0]
          show Function.update ρ v1 (some false) (v_r i) = none
          rw [Function.update_of_ne hne1]
          exact hv_none _
        · intro i hi
          exact hv_adj (i + 3) (by omega)
        · rw [trueCount_update_true ρ_f1_t0 v2 h_f1_t0_v2,
              trueCount_update_true ρ_f1 v0 h_f1_v0,
              trueCount_update_false ρ v1 h1_none]
          omega
      have h_f1_t0 : HasBound A t ρ_f1_t0 (1 + (Nat.fib (r' + 4) - 2)) :=
        HasBound.branch h_f1_t0_v2 h_f1_t0_f2 h_f1_t0_t2 le_rfl
      have h_f1 : HasBound A t ρ_f1 (1 + (1 + (Nat.fib (r' + 4) - 2))) :=
        HasBound.branch h_f1_v0 h_f1_f0 h_f1_t0 le_rfl
      refine HasBound.branch h1_none h_f1 h_t1 ?_
      have hfib : Nat.fib (r' + 2 + 4) = Nat.fib (r' + 4) + Nat.fib (r' + 1 + 4) := by
        have h := Nat.fib_add_two (n := r' + 4)
        simpa [Nat.add_assoc] using h
      have hge1 := fib_add_four_ge_three r'
      have hge2 := fib_add_four_ge_three (r' + 1)
      omega

-- ============================================================
-- PART 1: CYCLES C_n (n >= 4, t = (n + 1) / 2)
-- ============================================================

def cycleAdj (n : ℕ) (a b : Fin n) : Prop :=
  (a.val + 1) % n = b.val ∨ (b.val + 1) % n = a.val

lemma cycleAdj_symm (n : ℕ) (u v : Fin n) : cycleAdj n u v → cycleAdj n v u := by
  unfold cycleAdj; tauto

lemma cycleAdj_irrefl (n : ℕ) (hn : 4 ≤ n) (u : Fin n) : ¬ cycleAdj n u u := by
  unfold cycleAdj
  rintro (h | h) <;>
  · by_cases hu : u.val + 1 < n
    · rw [Nat.mod_eq_of_lt hu] at h; omega
    · have : u.val + 1 = n := by omega
      rw [this, Nat.mod_self] at h; omega

lemma cycleAdj_deg_le_two (n : ℕ) (hn : 4 ≤ n) (u : Fin n) :
    (letI := Classical.decPred (cycleAdj n u); (Finset.univ.filter (cycleAdj n u)).card ≤ 2) := by
  classical
  let b1 : Fin n := ⟨(u.val + 1) % n, Nat.mod_lt _ (by omega)⟩
  let b2 : Fin n := ⟨(u.val + n - 1) % n, Nat.mod_lt _ (by omega)⟩
  have hsub : Finset.univ.filter (cycleAdj n u) ⊆ {b1, b2} := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton] at hv ⊢
    rcases hv with h | h
    · left; ext; exact h.symm
    · right; ext
      show v.val = (u.val + n - 1) % n
      by_cases hv1 : v.val + 1 < n
      · rw [Nat.mod_eq_of_lt hv1] at h
        have : u.val + n - 1 = v.val + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt v.isLt]
      · have hv_eq : v.val + 1 = n := by omega
        rw [hv_eq, Nat.mod_self] at h
        have hu0 : u.val = 0 := h.symm
        rw [hu0]
        have : 0 + n - 1 = n - 1 := by omega
        rw [this, Nat.mod_eq_of_lt (by omega)]
        omega
  calc (Finset.univ.filter (cycleAdj n u)).card
      ≤ ({b1, b2} : Finset (Fin n)).card := Finset.card_le_card hsub
    _ ≤ 2 := Finset.card_le_two

lemma cycleAdj_vcGe (n : ℕ) (hn : 4 ≤ n) : VCGe (cycleAdj n) ((n + 1) / 2) := by
  intro R hcov
  classical
  let prev : Fin n → Fin n := fun i => ⟨(i.val + n - 1) % n, Nat.mod_lt _ (by omega)⟩
  have hsub : (Finset.univ : Finset (Fin n)) ⊆ R ∪ R.image prev := by
    intro i _
    let nxt : Fin n := ⟨(i.val + 1) % n, Nat.mod_lt _ (by omega)⟩
    have hadj : cycleAdj n i nxt := Or.inl rfl
    rcases hcov i nxt hadj with hi | hnxt
    · exact Finset.mem_union_left _ hi
    · apply Finset.mem_union_right
      rw [Finset.mem_image]
      refine ⟨nxt, hnxt, ?_⟩
      ext
      show ((i.val + 1) % n + n - 1) % n = i.val
      by_cases hi1 : i.val + 1 < n
      · rw [Nat.mod_eq_of_lt hi1]
        have : i.val + 1 + n - 1 = i.val + n := by omega
        rw [this, Nat.add_mod_right, Nat.mod_eq_of_lt i.isLt]
      · have hi_eq : i.val + 1 = n := by omega
        rw [hi_eq, Nat.mod_self]
        have : 0 + n - 1 = n - 1 := by omega
        rw [this, Nat.mod_eq_of_lt (by omega)]
        omega
  have hcard : n ≤ 2 * R.card := by
    calc n = (Finset.univ : Finset (Fin n)).card := by simp
      _ ≤ (R ∪ R.image prev).card := Finset.card_le_card hsub
      _ ≤ R.card + (R.image prev).card := Finset.card_union_le _ _
      _ ≤ R.card + R.card := Nat.add_le_add_left Finset.card_image_le _
      _ = 2 * R.card := by omega
  omega

lemma cycle_upper (n : ℕ) (hn : 4 ≤ n) :
    HasBound (cycleAdj n) ((n + 1) / 2) (fun _ => none) (Nat.fib ((n + 1) / 2 + 4) - 2) := by
  let t := (n + 1) / 2
  have ht2 : 2 ≤ t := by omega
  let v0 : Fin n := ⟨0, by omega⟩
  let v1 : Fin n := ⟨1, by omega⟩
  let vn : Fin n := ⟨n - 1, by omega⟩
  have hne01 : v0 ≠ v1 := by intro h; have := congrArg Fin.val h; simp [v0, v1] at this
  have hne0n : v0 ≠ vn := by intro h; have := congrArg Fin.val h; simp [v0, vn] at this; omega
  have hne1n : v1 ≠ vn := by intro h; have := congrArg Fin.val h; simp [v1, vn] at this; omega
  have hadj01 : cycleAdj n v0 v1 := Or.inl (by simp [v0, v1, Nat.mod_eq_of_lt (by omega : 1 < n)])
  have hadjn0 : cycleAdj n vn v0 := Or.inl (by
    simp [vn, v0]
    have : n - 1 + 1 = n := by omega
    rw [this, Nat.mod_self])
  -- Branch 0 = true: remaining path on 1..n-1 with r = t - 1
  let ρ_t0 := Function.update (fun _ : Fin n => (none : Option Bool)) v0 (some true)
  let emb1 : Fin (2 * (t - 1)) → Fin n := fun i => ⟨i.val + 1, by omega⟩
  have h_t0 : HasBound (cycleAdj n) t ρ_t0 (Nat.fib (t - 1 + 4) - 2) := by
    apply hasBound_of_path_embed (t - 1) ρ_t0 emb1
    · intro i j hij
      ext
      have := congrArg Fin.val hij
      simp [emb1] at this
      omega
    · intro i
      have hne : emb1 i ≠ v0 := by
        intro h; have := congrArg Fin.val h; simp [emb1, v0] at this
      show Function.update (fun _ => none) v0 (some true) (emb1 i) = none
      rw [Function.update_of_ne hne]
    · intro i hi
      left
      simp [emb1]
      rw [Nat.mod_eq_of_lt (by omega)]
    · rw [trueCount_update_true _ v0 rfl, trueCount_none]
  -- Branch 0 = false
  let ρ_f0 := Function.update (fun _ : Fin n => (none : Option Bool)) v0 (some false)
  have h_f0_v1 : ρ_f0 v1 = none := by
    show Function.update (fun _ => none) v0 (some false) v1 = none
    rw [Function.update_of_ne hne01.symm]
  have h_f0_f1 : HasBound (cycleAdj n) t (Function.update ρ_f0 v1 (some false)) 1 :=
    HasBound.leaf_false
      ⟨v0, v1, hadj01, by rw [Function.update_of_ne hne01]; simp [ρ_f0], by simp⟩ le_rfl
  let ρ_f0_t1 := Function.update ρ_f0 v1 (some true)
  have h_f0_t1_vn : ρ_f0_t1 vn = none := by
    show Function.update ρ_f0 v1 (some true) vn = none
    rw [Function.update_of_ne hne1n.symm]
    show Function.update (fun _ => none) v0 (some false) vn = none
    rw [Function.update_of_ne hne0n.symm]
  have h_f0_t1_fn : HasBound (cycleAdj n) t (Function.update ρ_f0_t1 vn (some false)) 1 :=
    HasBound.leaf_false
      ⟨vn, v0, hadjn0,
        by simp,
        by
          rw [Function.update_of_ne hne0n]
          show Function.update ρ_f0 v1 (some true) v0 = some false
          rw [Function.update_of_ne hne01]
          simp [ρ_f0]⟩ le_rfl
  let ρ_f0_t1_tn := Function.update ρ_f0_t1 vn (some true)
  let emb2 : Fin (2 * (t - 2)) → Fin n := fun i => ⟨i.val + 2, by omega⟩
  have h_f0_t1_tn : HasBound (cycleAdj n) t ρ_f0_t1_tn (Nat.fib (t - 2 + 4) - 2) := by
    apply hasBound_of_path_embed (t - 2) ρ_f0_t1_tn emb2
    · intro i j hij
      ext
      have := congrArg Fin.val hij
      simp [emb2] at this
      omega
    · intro i
      have hne0 : emb2 i ≠ v0 := by
        intro h; have := congrArg Fin.val h; simp [emb2, v0] at this
      have hne1 : emb2 i ≠ v1 := by
        intro h; have := congrArg Fin.val h; simp [emb2, v1] at this
      have hnen : emb2 i ≠ vn := by
        intro h; have := congrArg Fin.val h; simp [emb2, vn] at this; omega
      show Function.update ρ_f0_t1 vn (some true) (emb2 i) = none
      rw [Function.update_of_ne hnen]
      show Function.update ρ_f0 v1 (some true) (emb2 i) = none
      rw [Function.update_of_ne hne1]
      show Function.update (fun _ => none) v0 (some false) (emb2 i) = none
      rw [Function.update_of_ne hne0]
    · intro i hi
      left
      simp [emb2]
      rw [Nat.mod_eq_of_lt (by omega)]
    · rw [trueCount_update_true ρ_f0_t1 vn h_f0_t1_vn,
          trueCount_update_true ρ_f0 v1 h_f0_v1,
          trueCount_update_false _ v0 rfl,
          trueCount_none]
  have h_f0_t1 : HasBound (cycleAdj n) t ρ_f0_t1 (1 + (Nat.fib (t - 2 + 4) - 2)) :=
    HasBound.branch h_f0_t1_vn h_f0_t1_fn h_f0_t1_tn le_rfl
  have h_f0 : HasBound (cycleAdj n) t ρ_f0 (1 + (1 + (Nat.fib (t - 2 + 4) - 2))) :=
    HasBound.branch h_f0_v1 h_f0_f1 h_f0_t1 le_rfl
  refine HasBound.branch (y := v0) rfl h_f0 h_t0 ?_
  have hfib : Nat.fib (t + 4) = Nat.fib (t - 2 + 4) + Nat.fib (t - 1 + 4) := by
    have h := Nat.fib_add_two (n := t - 2 + 4)
    have h1 : t - 2 + 4 + 2 = t + 4 := by omega
    have h2 : t - 2 + 4 + 1 = t - 1 + 4 := by omega
    rw [h1, h2] at h
    exact h
  have hge1 := fib_add_four_ge_three (t - 2)
  have hge2 := fib_add_four_ge_three (t - 1)
  change 1 + (1 + (Nat.fib (t - 2 + 4) - 2)) + (Nat.fib (t - 1 + 4) - 2) ≤ Nat.fib (t + 4) - 2
  omega

-- ============================================================
-- PART 2: PATHS P_n (n >= 2, t = n / 2)
-- ============================================================

def pathAdj (n : ℕ) (a b : Fin n) : Prop :=
  a.val + 1 = b.val ∨ b.val + 1 = a.val

lemma pathAdj_symm (n : ℕ) (u v : Fin n) : pathAdj n u v → pathAdj n v u := by
  unfold pathAdj; tauto

lemma pathAdj_irrefl (n : ℕ) (u : Fin n) : ¬ pathAdj n u u := by
  unfold pathAdj; omega

lemma pathAdj_deg_le_two (n : ℕ) (u : Fin n) :
    (letI := Classical.decPred (pathAdj n u); (Finset.univ.filter (pathAdj n u)).card ≤ 2) := by
  classical
  let s1 : Finset (Fin n) := Finset.univ.filter (fun v => u.val + 1 = v.val)
  let s2 : Finset (Fin n) := Finset.univ.filter (fun v => v.val + 1 = u.val)
  have hsub : Finset.univ.filter (pathAdj n u) ⊆ s1 ∪ s2 := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, pathAdj, Finset.mem_union, s1, s2]
      at hv ⊢
    exact hv
  have hc1 : s1.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb => by
    simp only [s1, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    ext; omega
  have hc2 : s2.card ≤ 1 := Finset.card_le_one.mpr fun a ha b hb => by
    simp only [s2, Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
    ext; omega
  calc (Finset.univ.filter (pathAdj n u)).card
      ≤ (s1 ∪ s2).card := Finset.card_le_card hsub
    _ ≤ s1.card + s2.card := Finset.card_union_le _ _
    _ ≤ 1 + 1 := Nat.add_le_add hc1 hc2

lemma pathAdj_vcGe (n : ℕ) : VCGe (pathAdj n) (n / 2) := by
  intro R hcov
  classical
  let f : Fin (n / 2) → Fin n := fun i =>
    if (⟨2 * i.val, by omega⟩ : Fin n) ∈ R then ⟨2 * i.val, by omega⟩ else ⟨2 * i.val + 1, by omega⟩
  have hf_mem : ∀ i ∈ (Finset.univ : Finset (Fin (n / 2))), f i ∈ R := by
    intro i _
    dsimp only [f]
    split_ifs with h
    · exact h
    · have hadj : pathAdj n ⟨2 * i.val, by omega⟩ ⟨2 * i.val + 1, by omega⟩ := Or.inl rfl
      rcases hcov _ _ hadj with h1 | h2
      · exact absurd h1 h
      · exact h2
  have hf_inj : Set.InjOn f (Finset.univ : Finset (Fin (n / 2))) := by
    intro i _ j _ hij
    have hdiv : ∀ k : Fin (n / 2), (f k).val / 2 = k.val := by
      intro k
      dsimp only [f]
      split_ifs
      · simp
      · simp; omega
    ext
    rw [← hdiv i, ← hdiv j, hij]
  calc n / 2 = (Finset.univ : Finset (Fin (n / 2))).card := by simp
    _ ≤ R.card := Finset.card_le_card_of_injOn f hf_mem hf_inj

lemma path_upper (n : ℕ) :
    HasBound (pathAdj n) (n / 2) (fun _ => none) (Nat.fib (n / 2 + 4) - 2) := by
  let emb : Fin (2 * (n / 2)) → Fin n := fun i => ⟨i.val, by omega⟩
  apply hasBound_of_path_embed (n / 2) (fun _ => none) emb
  · intro i j hij
    have hval := congrArg Fin.val hij
    exact Fin.ext hval
  · intro i; rfl
  · intro i hi; left; rfl
  · rw [trueCount_none]; omega

-- ============================================================
-- PART 5: MATCHINGS t * K_2 (t >= 1)
-- ============================================================

def matchAdj (t : ℕ) (a b : Fin (2 * t)) : Prop :=
  a ≠ b ∧ a.val / 2 = b.val / 2

lemma matchAdj_symm (t : ℕ) (u v : Fin (2 * t)) : matchAdj t u v → matchAdj t v u := by
  rintro ⟨hne, hdiv⟩; exact ⟨hne.symm, hdiv.symm⟩

lemma matchAdj_irrefl (t : ℕ) (u : Fin (2 * t)) : ¬ matchAdj t u u := by
  rintro ⟨hne, _⟩; exact hne rfl

lemma matchAdj_deg_le_one (t : ℕ) (u : Fin (2 * t)) :
    (letI := Classical.decPred (matchAdj t u); (Finset.univ.filter (matchAdj t u)).card ≤ 1) := by
  classical
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, matchAdj] at ha hb
  have hau : a.val ≠ u.val := fun h => ha.1 (Fin.ext h.symm)
  have hbu : b.val ≠ u.val := fun h => hb.1 (Fin.ext h.symm)
  ext
  omega

lemma matchAdj_vcGe (t : ℕ) : VCGe (matchAdj t) t := by
  intro R hcov
  classical
  let f : Fin t → Fin (2 * t) := fun i =>
    if (⟨2 * i.val, by omega⟩ : Fin (2 * t)) ∈ R
    then ⟨2 * i.val, by omega⟩
    else ⟨2 * i.val + 1, by omega⟩
  have hf_mem : ∀ i ∈ (Finset.univ : Finset (Fin t)), f i ∈ R := by
    intro i _
    dsimp only [f]
    split_ifs with h
    · exact h
    · have hadj : matchAdj t ⟨2 * i.val, by omega⟩ ⟨2 * i.val + 1, by omega⟩ := by
        refine ⟨?_, ?_⟩
        · intro heq; have := congrArg Fin.val heq; simp at this
        · simp; omega
      rcases hcov _ _ hadj with h1 | h2
      · exact absurd h1 h
      · exact h2
  have hf_inj : Set.InjOn f (Finset.univ : Finset (Fin t)) := by
    intro i _ j _ hij
    have hdiv : ∀ k : Fin t, (f k).val / 2 = k.val := by
      intro k
      dsimp only [f]
      split_ifs
      · simp
      · simp; omega
    ext
    rw [← hdiv i, ← hdiv j, hij]
  calc t = (Finset.univ : Finset (Fin t)).card := by simp
    _ ≤ R.card := Finset.card_le_card_of_injOn f hf_mem hf_inj

-- ============================================================
-- PART 3: SPIDERS S_k (k >= 1, 2k + 1 vertices, exact 2^k + k)
-- ============================================================

def zeroFin (k : ℕ) : Fin (2 * k + 1) := ⟨0, Nat.zero_lt_succ (2 * k)⟩

def spiderAdj (k : ℕ) (a b : Fin (2 * k + 1)) : Prop :=
  (a.val = 0 ∧ 1 ≤ b.val ∧ b.val ≤ k) ∨
  (b.val = 0 ∧ 1 ≤ a.val ∧ a.val ≤ k) ∨
  (1 ≤ a.val ∧ a.val ≤ k ∧ b.val = a.val + k) ∨
  (1 ≤ b.val ∧ b.val ≤ k ∧ a.val = b.val + k)

lemma spiderAdj_symm (k : ℕ) (u v : Fin (2 * k + 1)) :
    spiderAdj k u v → spiderAdj k v u := by
  unfold spiderAdj; tauto

lemma spiderAdj_irrefl (k : ℕ) (u : Fin (2 * k + 1)) : ¬ spiderAdj k u u := by
  unfold spiderAdj; omega

lemma spiderAdj_vcGe (k : ℕ) : VCGe (spiderAdj k) k := by
  intro R hcov
  classical
  let f : Fin k → Fin (2 * k + 1) := fun i =>
    if (⟨i.val + 1, by omega⟩ : Fin (2 * k + 1)) ∈ R
    then ⟨i.val + 1, by omega⟩
    else ⟨i.val + 1 + k, by omega⟩
  have hf_mem : ∀ i ∈ (Finset.univ : Finset (Fin k)), f i ∈ R := by
    intro i _
    dsimp only [f]
    split_ifs with h
    · exact h
    · have hadj : spiderAdj k ⟨i.val + 1, by omega⟩ ⟨i.val + 1 + k, by omega⟩ := by
        right; right; left; simp
      rcases hcov _ _ hadj with h1 | h2
      · exact absurd h1 h
      · exact h2
  have hf_inj : Set.InjOn f (Finset.univ : Finset (Fin k)) := by
    intro i _ j _ hij
    have hmod : ∀ x : Fin k, ((f x).val - 1) % k = x.val := by
      intro x
      dsimp only [f]
      split_ifs with h
      · simp [Nat.mod_eq_of_lt x.isLt]
      · simp [Nat.mod_eq_of_lt x.isLt]
    ext
    rw [← hmod i, ← hmod j, hij]
  calc k = (Finset.univ : Finset (Fin k)).card := by simp
    _ ≤ R.card := Finset.card_le_card_of_injOn f hf_mem hf_inj

-- Spider upper bound: 2^k + k
lemma spider_false_zero_bound (k : ℕ) (hk : 1 ≤ k) :
    ∀ m (hm : m ≤ k) (ρ : Fin (2 * k + 1) → Option Bool),
      ρ (zeroFin k) = some false →
      (∀ j : ℕ, (hj : j < k - m) → ρ ⟨j + 1, by omega⟩ = some true) →
      (∀ j : ℕ, k - m ≤ j → (hj : j < k) → ρ ⟨j + 1, by omega⟩ = none) →
      HasBound (spiderAdj k) k ρ (m + 1) := by
  intro m
  induction m with
  | zero =>
    intro _ ρ _ htrue _
    apply HasBound.leaf_true _ le_rfl
    let S : Finset (Fin (2 * k + 1)) :=
      (Finset.univ : Finset (Fin k)).image (fun i => ⟨i.val + 1, by omega⟩)
    refine ⟨S, ?_, ?_⟩
    · rw [Finset.card_image_of_injective]
      · simp
      · intro a b hab; ext; have := congrArg Fin.val hab; simp at this; omega
    · intro x hx
      rw [Finset.mem_image] at hx
      obtain ⟨i, _, rfl⟩ := hx
      exact htrue i.val (by omega)
  | succ m ih =>
    intro hm ρ h0 htrue hnone
    let idx : ℕ := k - (m + 1)
    let y : Fin (2 * k + 1) := ⟨idx + 1, by omega⟩
    have hy_none : ρ y = none := hnone idx (by omega) (by omega)
    have hy0_ne : zeroFin k ≠ y := by
      intro h; have := congrArg Fin.val h; simp [zeroFin, y] at this
    have h0_bound : HasBound (spiderAdj k) k (Function.update ρ y (some false)) 1 :=
      HasBound.leaf_false
        ⟨zeroFin k, y,
          Or.inl ⟨rfl, by simp [y], by simp [y]; omega⟩,
          by rw [Function.update_of_ne hy0_ne]; exact h0,
          by simp⟩ le_rfl
    have h1_bound : HasBound (spiderAdj k) k (Function.update ρ y (some true)) (m + 1) := by
      apply ih (by omega)
      · rw [Function.update_of_ne hy0_ne]; exact h0
      · intro j hj
        by_cases hj_eq : j = idx
        · subst hj_eq; simp [y]
        · have hne : (⟨j + 1, by omega⟩ : Fin (2 * k + 1)) ≠ y := by
            intro h; have := congrArg Fin.val h; simp [y] at this; omega
          rw [Function.update_of_ne hne]
          exact htrue j (by omega)
      · intro j hj1 hj2
        have hne : (⟨j + 1, by omega⟩ : Fin (2 * k + 1)) ≠ y := by
          intro h; have := congrArg Fin.val h; simp [y] at this; omega
        rw [Function.update_of_ne hne]
        exact hnone j (by omega) hj2
    exact HasBound.branch hy_none h0_bound h1_bound (by omega)

lemma spider_upper (k : ℕ) (hk : 1 ≤ k) :
    HasBound (spiderAdj k) k (fun _ => none) (2 ^ k + k) := by
  let v0 : Fin (2 * k + 1) := zeroFin k
  have h0 : HasBound (spiderAdj k) k (Function.update (fun _ => none) v0 (some false)) (k + 1) := by
    apply spider_false_zero_bound k hk k le_rfl
    · simp [v0]
    · intro j hj; omega
    · intro j _ hj
      have hne : (⟨j + 1, by omega⟩ : Fin (2 * k + 1)) ≠ v0 := by
        intro h; have := congrArg Fin.val h; simp [v0, zeroFin] at this
      rw [Function.update_of_ne hne]
  have h1 : HasBound (spiderAdj k) k (Function.update (fun _ => none) v0 (some true)) (2 ^ k - 1) := by
    have hgen := hasBound_general (spiderAdj_irrefl k) (spiderAdj_vcGe k) (k - 1)
      (Function.update (fun _ => none) v0 (some true))
      (by rw [trueCount_update_true _ v0 rfl, trueCount_none])
    have heq : k - 1 + 1 = k := by omega
    rw [heq] at hgen
    exact hgen
  refine HasBound.branch (y := v0) rfl h0 h1 ?_
  have hp : 1 ≤ 2 ^ k := pow2_ge_one k
  omega

-- Spider lower bound: 2^k + k
def spiderLegAdj (k : ℕ) (a b : Fin (2 * k + 1)) : Prop :=
  (1 ≤ a.val ∧ a.val ≤ k ∧ b.val = a.val + k) ∨
  (1 ≤ b.val ∧ b.val ≤ k ∧ a.val = b.val + k)

lemma spiderLegAdj_symm (k : ℕ) (u v : Fin (2 * k + 1)) :
    spiderLegAdj k u v → spiderLegAdj k v u := by
  unfold spiderLegAdj; tauto

lemma spiderLegAdj_deg_le_one (k : ℕ) (u : Fin (2 * k + 1)) :
    (letI := Classical.decPred (spiderLegAdj k u);
      (Finset.univ.filter (spiderLegAdj k u)).card ≤ 1) := by
  classical
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, spiderLegAdj] at ha hb
  ext
  omega

lemma spiderLegAdj_no_zero_left (k : ℕ) (v : Fin (2 * k + 1)) :
    ¬ spiderLegAdj k (zeroFin k) v := by
  unfold spiderLegAdj zeroFin; simp; omega

def centerForced (k : ℕ) (ρ : Fin (2 * k + 1) → Option Bool) : Prop :=
  ∃ i : Fin (2 * k + 1), 1 ≤ i.val ∧ i.val ≤ k ∧ ρ i = some false

def gTrue (s r : ℕ) : ℕ := if r = 0 then 1 else 1 + fMatch s (r - 1)

def gFalse (s r : ℕ) : ℕ := r + 2 ^ (r - s)

lemma gTrue_anti (s1 s2 r : ℕ) (h : s1 ≤ s2) : gTrue s2 r ≤ gTrue s1 r := by
  unfold gTrue
  split_ifs
  · exact le_rfl
  · exact Nat.add_le_add_left (fMatch_anti s1 s2 (r - 1) h) 1

lemma gTrue_step_forced (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    gTrue s r = 1 + gTrue (s - 1) (r - 1) := by
  unfold gTrue
  by_cases hr1 : r = 1
  · subst hr1
    simp [fMatch]
  · have hr2 : 1 ≤ r - 1 := by omega
    have hr0 : r ≠ 0 := by omega
    have hr10 : r - 1 ≠ 0 := by omega
    simp only [hr0, hr10, ↓reduceIte]
    have hstep := fMatch_step_forced s (r - 1) hs hr2
    omega

lemma gTrue_branch (s r : ℕ) (hr : 1 ≤ r) :
    gTrue s r ≤ gTrue (s + 1) r + gTrue s (r - 1) := by
  unfold gTrue
  by_cases hr1 : r = 1
  · subst hr1
    simp [fMatch]
  · have hr2 : 1 ≤ r - 1 := by omega
    have hr0 : r ≠ 0 := by omega
    have hr10 : r - 1 ≠ 0 := by omega
    simp only [hr0, hr10, ↓reduceIte]
    have hbr := fMatch_branch s (r - 1) hr2
    omega

lemma gFalse_step_forced (s r : ℕ) (hs : 1 ≤ s) (hr : 1 ≤ r) :
    gFalse s r = 1 + gFalse (s - 1) (r - 1) := by
  unfold gFalse
  have h1 : r - 1 - (s - 1) = r - s := by omega
  rw [h1]
  omega

lemma gFalse_query_center (s r : ℕ) :
    gFalse s r ≤ (r + 1) + fMatch s (r - 1) := by
  unfold gFalse fMatch
  by_cases hsr : s < r
  · have hd : r - 1 - s + 1 = r - s := by omega
    rw [hd]
    have hp : 1 ≤ 2 ^ (r - s) := pow2_ge_one _
    omega
  · have hd0 : r - s = 0 := by omega
    have hd1 : r - 1 - s = 0 := by omega
    rw [hd0, hd1]
    omega

lemma gFalse_branch_inner (s r : ℕ) (hr : 1 ≤ r) :
    gFalse s r ≤ gTrue (s + 1) r + gFalse s (r - 1) := by
  unfold gFalse gTrue fMatch
  have hr0 : r ≠ 0 := by omega
  simp only [hr0, ↓reduceIte]
  by_cases h1 : r ≤ s
  · have hd0 : r - s = 0 := by omega
    have hd1 : r - 1 - (s + 1) = 0 := by omega
    have hd2 : r - 1 - s = 0 := by omega
    rw [hd0, hd1, hd2]
    omega
  · by_cases h2 : s + 1 = r
    · subst h2
      have hd0 : s + 1 - s = 1 := by omega
      have hd1 : s + 1 - 1 - (s + 1) = 0 := by omega
      have hd2 : s + 1 - 1 - s = 0 := by omega
      have hm1 : min (s + 1) (s + 1 - 1) = s := by omega
      rw [hd0, hd1, hd2, hm1]
      omega
    · have hlt : s + 2 ≤ r := by omega
      have hm1 : min (s + 1) (r - 1) = s + 1 := by omega
      have hd1 : r - 1 - (s + 1) + 1 = r - s - 1 := by omega
      have hd2 : r - 1 - s = r - s - 1 := by omega
      rw [hm1, hd1, hd2]
      have hpow : 2 ^ (r - s) = 2 * 2 ^ (r - s - 1) := by
        rw [← Nat.pow_succ']; congr 1; omega
      have hp : 1 ≤ 2 ^ (r - s - 1) := pow2_ge_one _
      omega

lemma spider_not_isFalsified_update_false_leg {k : ℕ} {ρ : Fin (2 * k + 1) → Option Bool}
    {y : Fin (2 * k + 1)} (hnf : ¬ IsFalsified (spiderAdj k) ρ)
    (h0_nf : ρ (zeroFin k) ≠ some false)
    (hy0 : y ≠ zeroFin k)
    (hy_none : ρ y = none) (hy_leg : y ∉ forcedSet (spiderLegAdj k) ρ) :
    ¬ IsFalsified (spiderAdj k) (Function.update ρ y (some false)) := by
  rintro ⟨u, v, huv, hu, hv⟩
  by_cases huy : u = y
  · subst huy
    have hvy : v ≠ u := fun h => by subst h; exact spiderAdj_irrefl k v huv
    rw [Function.update_of_ne hvy] at hv
    rcases huv with ⟨h0, _, _⟩ | ⟨h0, _, _⟩ | hleg | hleg
    · exact hy0 (Fin.ext h0)
    · have hv0 : v = zeroFin k := Fin.ext h0
      rw [hv0] at hv
      exact h0_nf hv
    · apply hy_leg
      classical
      unfold forcedSet
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hy_none, v, Or.inl hleg, hv⟩
    · apply hy_leg
      classical
      unfold forcedSet
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hy_none, v, Or.inr hleg, hv⟩
  · by_cases hvy : v = y
    · subst hvy
      rw [Function.update_of_ne huy] at hu
      rcases huv with ⟨h0, _, _⟩ | ⟨h0, _, _⟩ | hleg | hleg
      · have hu0 : u = zeroFin k := Fin.ext h0
        rw [hu0] at hu
        exact h0_nf hu
      · exact hy0 (Fin.ext h0)
      · apply hy_leg
        classical
        unfold forcedSet
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hy_none, u, Or.inr hleg, hu⟩
      · apply hy_leg
        classical
        unfold forcedSet
        simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨hy_none, u, Or.inl hleg, hu⟩
    · rw [Function.update_of_ne huy] at hu
      rw [Function.update_of_ne hvy] at hv
      exact hnf ⟨u, v, huv, hu, hv⟩

lemma spider_not_isFalsified_update_false_center {k : ℕ} {ρ : Fin (2 * k + 1) → Option Bool}
    (hnf : ¬ IsFalsified (spiderAdj k) ρ)
    (hncf : ¬ centerForced k ρ) :
    ¬ IsFalsified (spiderAdj k) (Function.update ρ (zeroFin k) (some false)) := by
  rintro ⟨u, v, huv, hu, hv⟩
  by_cases hu0 : u = zeroFin k
  · subst hu0
    have hv0 : v ≠ zeroFin k := fun h => by subst h; exact spiderAdj_irrefl k (zeroFin k) huv
    rw [Function.update_of_ne hv0] at hv
    rcases huv with ⟨_, h1, h2⟩ | ⟨h0, _, _⟩ | ⟨h1, _, _⟩ | ⟨_, _, h1⟩
    · exact hncf ⟨v, h1, h2, hv⟩
    · exact hv0 (Fin.ext h0)
    · simp [zeroFin] at h1
    · simp [zeroFin] at h1; omega
  · by_cases hv0 : v = zeroFin k
    · subst hv0
      rw [Function.update_of_ne hu0] at hu
      rcases huv with ⟨h0, _, _⟩ | ⟨_, h1, h2⟩ | ⟨_, _, h1⟩ | ⟨h1, _, _⟩
      · exact hu0 (Fin.ext h0)
      · exact hncf ⟨u, h1, h2, hu⟩
      · simp [zeroFin] at h1; omega
      · simp [zeroFin] at h1
    · rw [Function.update_of_ne hu0] at hu
      rw [Function.update_of_ne hv0] at hv
      exact hnf ⟨u, v, huv, hu, hv⟩

lemma spider_lower_center_true {k : ℕ} {N : (Fin (2 * k + 1) → Option Bool) → ℕ}
    (hN : ValidN (2 * k + 1) (spiderAdj k) k N) :
    ∀ ρ, ¬ IsFalsified (spiderAdj k) ρ → ρ (zeroFin k) = some true →
      fMatch (forcedSet (spiderLegAdj k) ρ).card (k - trueCount ρ) ≤ N ρ := by
  intro ρ
  suffices ∀ m ρ, noneCount ρ = m → ¬ IsFalsified (spiderAdj k) ρ →
      ρ (zeroFin k) = some true →
      fMatch (forcedSet (spiderLegAdj k) ρ).card (k - trueCount ρ) ≤ N ρ from
    this (noneCount ρ) ρ rfl
  intro m
  induction m with
  | zero =>
    intro ρ _ hnf _
    rcases hN ρ with ⟨hf | ht, h1⟩ | ⟨y, hy, _⟩
    · exact absurd hf hnf
    · have hle := hasTrues_iff_le_trueCount.mp ht
      have hr0 : k - trueCount ρ = 0 := by omega
      rw [hr0, fMatch_zero_r]
      exact h1
    · have := noneCount_update_some ρ y false hy
      omega
  | succ m ih =>
    intro ρ hm hnf h0t
    by_cases hr0 : k - trueCount ρ = 0
    · rw [hr0, fMatch_zero_r]
      exact validN_pos hN ρ
    · have hr : 1 ≤ k - trueCount ρ := by omega
      rcases hN ρ with ⟨hf | ht, h1⟩ | ⟨y, hy, hsum⟩
      · exact absurd hf hnf
      · have hle := hasTrues_iff_le_trueCount.mp ht
        omega
      · have hy0 : y ≠ zeroFin k := by
          intro h; rw [h, h0t] at hy; simp at hy
        have h0t_f : Function.update ρ y (some false) (zeroFin k) = some true := by
          rw [Function.update_of_ne hy0.symm]; exact h0t
        have h0t_t : Function.update ρ y (some true) (zeroFin k) = some true := by
          rw [Function.update_of_ne hy0.symm]; exact h0t
        by_cases hyf : y ∈ forcedSet (spiderLegAdj k) ρ
        · have hpos : 1 ≤ N (Function.update ρ y (some false)) := validN_pos hN _
          have h1 := ih (Function.update ρ y (some true))
            (by have := noneCount_update_some ρ y true hy; omega)
            (not_isFalsified_update_true hnf) h0t_t
          have hs1 := forcedSet_update_true_of_mem (spiderLegAdj k) ρ y hyf
          have ht1 := trueCount_update_true ρ y hy
          have hs_pos : 1 ≤ (forcedSet (spiderLegAdj k) ρ).card := by omega
          have hstep := fMatch_step_forced (forcedSet (spiderLegAdj k) ρ).card
            (k - trueCount ρ) hs_pos hr
          have hs1' : (forcedSet (spiderLegAdj k) (Function.update ρ y (some true))).card =
              (forcedSet (spiderLegAdj k) ρ).card - 1 := by omega
          have hr1' : k - trueCount (Function.update ρ y (some true)) =
              k - trueCount ρ - 1 := by omega
          rw [hs1', hr1'] at h1
          omega
        · have hnf0 := spider_not_isFalsified_update_false_leg hnf (by rw [h0t]; simp) hy0 hy hyf
          have h0 := ih (Function.update ρ y (some false))
            (by have := noneCount_update_some ρ y false hy; omega)
            hnf0 h0t_f
          have h1 := ih (Function.update ρ y (some true))
            (by have := noneCount_update_some ρ y true hy; omega)
            (not_isFalsified_update_true hnf) h0t_t
          have hs0 := forcedSet_update_false_card_le (spiderLegAdj k)
            (spiderLegAdj_symm k) (spiderLegAdj_deg_le_one k) ρ y
          have hs1 := forcedSet_update_true_of_notMem (spiderLegAdj k) ρ y hy hyf
          have ht0 := trueCount_update_false ρ y hy
          have ht1 := trueCount_update_true ρ y hy
          rw [ht0] at h0
          rw [hs1, ht1] at h1
          have h0' : fMatch ((forcedSet (spiderLegAdj k) ρ).card + 1) (k - trueCount ρ) ≤
              N (Function.update ρ y (some false)) :=
            le_trans (fMatch_anti _ _ _ hs0) h0
          have hbr := fMatch_branch (forcedSet (spiderLegAdj k) ρ).card (k - trueCount ρ) hr
          have hr1' : k - (trueCount ρ + 1) = k - trueCount ρ - 1 := by omega
          rw [hr1'] at h1
          omega

lemma spider_lower_center_none_forced {k : ℕ} {N : (Fin (2 * k + 1) → Option Bool) → ℕ}
    (hN : ValidN (2 * k + 1) (spiderAdj k) k N) :
    ∀ ρ, ¬ IsFalsified (spiderAdj k) ρ → ρ (zeroFin k) = none →
      gTrue (forcedSet (spiderLegAdj k) ρ).card (k - trueCount ρ) ≤ N ρ := by
  intro ρ
  suffices ∀ m ρ, noneCount ρ = m → ¬ IsFalsified (spiderAdj k) ρ →
      ρ (zeroFin k) = none →
      gTrue (forcedSet (spiderLegAdj k) ρ).card (k - trueCount ρ) ≤ N ρ from
    this (noneCount ρ) ρ rfl
  intro m
  induction m with
  | zero =>
    intro ρ h0 _ h0n
    have := noneCount_update_some ρ (zeroFin k) false h0n
    omega
  | succ m ih =>
    intro ρ hm hnf h0n
    by_cases hr0 : k - trueCount ρ = 0
    · rw [hr0]; simp [gTrue]; exact validN_pos hN ρ
    · have hr : 1 ≤ k - trueCount ρ := by omega
      rcases hN ρ with ⟨hf | ht, h1⟩ | ⟨y, hy, hsum⟩
      · exact absurd hf hnf
      · have hle := hasTrues_iff_le_trueCount.mp ht
        omega
      · by_cases hy0 : y = zeroFin k
        · subst hy0
          have hpos : 1 ≤ N (Function.update ρ (zeroFin k) (some false)) := validN_pos hN _
          have h1 := spider_lower_center_true hN (Function.update ρ (zeroFin k) (some true))
            (not_isFalsified_update_true hnf) (by simp)
          have h0_nf : zeroFin k ∉ forcedSet (spiderLegAdj k) ρ := by
            classical
            unfold forcedSet
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_exists]
            intro _ u hu
            exact absurd hu (spiderLegAdj_no_zero_left k u)
          have hs1 := forcedSet_update_true_of_notMem (spiderLegAdj k) ρ (zeroFin k) h0n h0_nf
          have ht1 := trueCount_update_true ρ (zeroFin k) h0n
          rw [hs1, ht1] at h1
          have hr1' : k - (trueCount ρ + 1) = k - trueCount ρ - 1 := by omega
          rw [hr1'] at h1
          unfold gTrue
          simp only [hr0, ↓reduceIte]
          omega
        · have h0n_f : Function.update ρ y (some false) (zeroFin k) = none := by
            rw [Function.update_of_ne (Ne.symm hy0)]; exact h0n
          have h0n_t : Function.update ρ y (some true) (zeroFin k) = none := by
            rw [Function.update_of_ne (Ne.symm hy0)]; exact h0n
          by_cases hyf : y ∈ forcedSet (spiderLegAdj k) ρ
          · have hpos : 1 ≤ N (Function.update ρ y (some false)) := validN_pos hN _
            have h1 := ih (Function.update ρ y (some true))
              (by have := noneCount_update_some ρ y true hy; omega)
              (not_isFalsified_update_true hnf) h0n_t
            have hs1 := forcedSet_update_true_of_mem (spiderLegAdj k) ρ y hyf
            have ht1 := trueCount_update_true ρ y hy
            have hs_pos : 1 ≤ (forcedSet (spiderLegAdj k) ρ).card := by omega
            have hstep := gTrue_step_forced (forcedSet (spiderLegAdj k) ρ).card
              (k - trueCount ρ) hs_pos hr
            have hs1' : (forcedSet (spiderLegAdj k) (Function.update ρ y (some true))).card =
                (forcedSet (spiderLegAdj k) ρ).card - 1 := by omega
            have hr1' : k - trueCount (Function.update ρ y (some true)) =
                k - trueCount ρ - 1 := by omega
            rw [hs1', hr1'] at h1
            omega
          · have hnf0 := spider_not_isFalsified_update_false_leg hnf (by rw [h0n]; simp) hy0 hy hyf
            have h0 := ih (Function.update ρ y (some false))
              (by have := noneCount_update_some ρ y false hy; omega)
              hnf0 h0n_f
            have h1 := ih (Function.update ρ y (some true))
              (by have := noneCount_update_some ρ y true hy; omega)
              (not_isFalsified_update_true hnf) h0n_t
            have hs0 := forcedSet_update_false_card_le (spiderLegAdj k)
              (spiderLegAdj_symm k) (spiderLegAdj_deg_le_one k) ρ y
            have hs1 := forcedSet_update_true_of_notMem (spiderLegAdj k) ρ y hy hyf
            have ht0 := trueCount_update_false ρ y hy
            have ht1 := trueCount_update_true ρ y hy
            rw [ht0] at h0
            rw [hs1, ht1] at h1
            have h0' : gTrue ((forcedSet (spiderLegAdj k) ρ).card + 1) (k - trueCount ρ) ≤
                N (Function.update ρ y (some false)) :=
              le_trans (gTrue_anti _ _ _ hs0) h0
            have hbr := gTrue_branch (forcedSet (spiderLegAdj k) ρ).card (k - trueCount ρ) hr
            have hr1' : k - (trueCount ρ + 1) = k - trueCount ρ - 1 := by omega
            rw [hr1'] at h1
            omega

lemma spider_lower_center_none_unforced {k : ℕ} {N : (Fin (2 * k + 1) → Option Bool) → ℕ}
    (hN : ValidN (2 * k + 1) (spiderAdj k) k N) :
    ∀ ρ, ¬ IsFalsified (spiderAdj k) ρ → ρ (zeroFin k) = none → ¬ centerForced k ρ →
      gFalse (forcedSet (spiderLegAdj k) ρ).card (k - trueCount ρ) ≤ N ρ := by
  intro ρ
  suffices ∀ m ρ, noneCount ρ = m → ¬ IsFalsified (spiderAdj k) ρ →
      ρ (zeroFin k) = none → ¬ centerForced k ρ →
      gFalse (forcedSet (spiderLegAdj k) ρ).card (k - trueCount ρ) ≤ N ρ from
    this (noneCount ρ) ρ rfl
  intro m
  induction m with
  | zero =>
    intro ρ h0 _ h0n _
    have := noneCount_update_some ρ (zeroFin k) false h0n
    omega
  | succ m ih =>
    intro ρ hm hnf h0n hncf
    by_cases hr0 : k - trueCount ρ = 0
    · rw [hr0]; simp [gFalse]; exact validN_pos hN ρ
    · have hr : 1 ≤ k - trueCount ρ := by omega
      rcases hN ρ with ⟨hf | ht, h1⟩ | ⟨y, hy, hsum⟩
      · exact absurd hf hnf
      · have hle := hasTrues_iff_le_trueCount.mp ht
        omega
      · by_cases hy0 : y = zeroFin k
        · subst hy0
          have hnf0 := spider_not_isFalsified_update_false_center hnf hncf
          have h0 := validN_ge_rem_add_one hN (Function.update ρ (zeroFin k) (some false)) hnf0
          rw [trueCount_update_false ρ (zeroFin k) h0n] at h0
          have h1 := spider_lower_center_true hN (Function.update ρ (zeroFin k) (some true))
            (not_isFalsified_update_true hnf) (by simp)
          have h0_nf : zeroFin k ∉ forcedSet (spiderLegAdj k) ρ := by
            classical
            unfold forcedSet
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_and, not_exists]
            intro _ u hu
            exact absurd hu (spiderLegAdj_no_zero_left k u)
          have hs1 := forcedSet_update_true_of_notMem (spiderLegAdj k) ρ (zeroFin k) h0n h0_nf
          have ht1 := trueCount_update_true ρ (zeroFin k) h0n
          rw [hs1, ht1] at h1
          have hr1' : k - (trueCount ρ + 1) = k - trueCount ρ - 1 := by omega
          rw [hr1'] at h1
          have hqc := gFalse_query_center (forcedSet (spiderLegAdj k) ρ).card (k - trueCount ρ)
          omega
        · have h0n_f : Function.update ρ y (some false) (zeroFin k) = none := by
            rw [Function.update_of_ne (Ne.symm hy0)]; exact h0n
          have h0n_t : Function.update ρ y (some true) (zeroFin k) = none := by
            rw [Function.update_of_ne (Ne.symm hy0)]; exact h0n
          have hncf_t : ¬ centerForced k (Function.update ρ y (some true)) := by
            rintro ⟨i, hi1, hi2, hif⟩
            have hiy : i ≠ y := by intro h; subst h; simp at hif
            rw [Function.update_of_ne hiy] at hif
            exact hncf ⟨i, hi1, hi2, hif⟩
          by_cases hyf : y ∈ forcedSet (spiderLegAdj k) ρ
          · have hpos : 1 ≤ N (Function.update ρ y (some false)) := validN_pos hN _
            have h1 := ih (Function.update ρ y (some true))
              (by have := noneCount_update_some ρ y true hy; omega)
              (not_isFalsified_update_true hnf) h0n_t hncf_t
            have hs1 := forcedSet_update_true_of_mem (spiderLegAdj k) ρ y hyf
            have ht1 := trueCount_update_true ρ y hy
            have hs_pos : 1 ≤ (forcedSet (spiderLegAdj k) ρ).card := by omega
            have hstep := gFalse_step_forced (forcedSet (spiderLegAdj k) ρ).card
              (k - trueCount ρ) hs_pos hr
            have hs1' : (forcedSet (spiderLegAdj k) (Function.update ρ y (some true))).card =
                (forcedSet (spiderLegAdj k) ρ).card - 1 := by omega
            have hr1' : k - trueCount (Function.update ρ y (some true)) =
                k - trueCount ρ - 1 := by omega
            rw [hs1', hr1'] at h1
            omega
          · have hnf0 := spider_not_isFalsified_update_false_leg hnf (by rw [h0n]; simp) hy0 hy hyf
            have h1 := ih (Function.update ρ y (some true))
              (by have := noneCount_update_some ρ y true hy; omega)
              (not_isFalsified_update_true hnf) h0n_t hncf_t
            have hs0 := forcedSet_update_false_card_le (spiderLegAdj k)
              (spiderLegAdj_symm k) (spiderLegAdj_deg_le_one k) ρ y
            have hs1 := forcedSet_update_true_of_notMem (spiderLegAdj k) ρ y hy hyf
            have ht0 := trueCount_update_false ρ y hy
            have ht1 := trueCount_update_true ρ y hy
            rw [hs1, ht1] at h1
            have hr1' : k - (trueCount ρ + 1) = k - trueCount ρ - 1 := by omega
            rw [hr1'] at h1
            have h0 := spider_lower_center_none_forced hN
              (Function.update ρ y (some false)) hnf0 h0n_f
            rw [ht0] at h0
            have h0' : gTrue ((forcedSet (spiderLegAdj k) ρ).card + 1) (k - trueCount ρ) ≤
                N (Function.update ρ y (some false)) :=
              le_trans (gTrue_anti _ _ _ hs0) h0
            have hbr := gFalse_branch_inner (forcedSet (spiderLegAdj k) ρ).card
              (k - trueCount ρ) hr
            omega

end PEqualNP.Outside.L_pcx_107

theorem PEqualNP.Outside.L_pcx_107 :
    ∀ Tr : (n0 : ℕ) → (Fin n0 → Fin n0 → Prop) → ℕ → ℕ → Prop, (∀ (n1 : ℕ) (A1 : Fin n1 → Fin n1 → Prop) (t1 k1 : ℕ), Tr n1 A1 t1 k1 ↔ ∃ N1 : (Fin n1 → Option Bool) → ℕ, N1 (fun w1 : Fin n1 => none) ≤ k1 ∧ ∀ ρ1 : Fin n1 → Option Bool, ((((∃ u1 v1 : Fin n1, A1 u1 v1 ∧ ρ1 u1 = some false ∧ ρ1 v1 = some false) ∨ ∃ S1 : Finset (Fin n1), S1.card = t1 ∧ ∀ x1 ∈ S1, ρ1 x1 = some true) ∧ 1 ≤ N1 ρ1) ∨ ∃ y1 : Fin n1, ρ1 y1 = none ∧ N1 (Function.update ρ1 y1 (some false)) + N1 (Function.update ρ1 y1 (some true)) ≤ N1 ρ1)) → (∀ n2 : ℕ, 4 ≤ n2 → ∃ L2 : ℕ, L2 + 2 = Nat.fib ((n2 + 1) / 2 + 4) ∧ (Tr n2 (fun a2 b2 : Fin n2 => (a2.val + 1) % n2 = b2.val ∨ (b2.val + 1) % n2 = a2.val) ((n2 + 1) / 2) (L2) ∧ ∀ m2 : ℕ, Tr n2 (fun a2 b2 : Fin n2 => (a2.val + 1) % n2 = b2.val ∨ (b2.val + 1) % n2 = a2.val) ((n2 + 1) / 2) m2 → L2 ≤ m2)) ∧ (∀ n3 : ℕ, 2 ≤ n3 → ∃ L3 : ℕ, L3 + 2 = Nat.fib (n3 / 2 + 4) ∧ (Tr n3 (fun a3 b3 : Fin n3 => a3.val + 1 = b3.val ∨ b3.val + 1 = a3.val) (n3 / 2) (L3) ∧ ∀ m3 : ℕ, Tr n3 (fun a3 b3 : Fin n3 => a3.val + 1 = b3.val ∨ b3.val + 1 = a3.val) (n3 / 2) m3 → L3 ≤ m3)) ∧ (∀ k4 : ℕ, 1 ≤ k4 → (Tr (2 * k4 + 1) (fun a4 b4 : Fin (2 * k4 + 1) => (a4.val = 0 ∧ 1 ≤ b4.val ∧ b4.val ≤ k4) ∨ (b4.val = 0 ∧ 1 ≤ a4.val ∧ a4.val ≤ k4) ∨ (1 ≤ a4.val ∧ a4.val ≤ k4 ∧ b4.val = a4.val + k4) ∨ (1 ≤ b4.val ∧ b4.val ≤ k4 ∧ a4.val = b4.val + k4)) k4 (2 ^ k4 + k4) ∧ ∀ m4 : ℕ, Tr (2 * k4 + 1) (fun a4 b4 : Fin (2 * k4 + 1) => (a4.val = 0 ∧ 1 ≤ b4.val ∧ b4.val ≤ k4) ∨ (b4.val = 0 ∧ 1 ≤ a4.val ∧ a4.val ≤ k4) ∨ (1 ≤ a4.val ∧ a4.val ≤ k4 ∧ b4.val = a4.val + k4) ∨ (1 ≤ b4.val ∧ b4.val ≤ k4 ∧ a4.val = b4.val + k4)) k4 m4 → 2 ^ k4 + k4 ≤ m4)) ∧ (∀ (n5 : ℕ) (G5 : SimpleGraph (Fin n5)) (t5 : ℕ), (∃ u5 v5 : Fin n5, G5.Adj u5 v5) → (∃ T5 : Finset (Fin n5), T5.card = t5 ∧ ∀ p5 q5 : Fin n5, G5.Adj p5 q5 → p5 ∈ T5 ∨ q5 ∈ T5) → (∀ R5 : Finset (Fin n5), (∀ p6 q6 : Fin n5, G5.Adj p6 q6 → p6 ∈ R5 ∨ q6 ∈ R5) → t5 ≤ R5.card) → ∃ k5 : ℕ, k5 + 1 ≤ 2 ^ (t5 + 1) ∧ Tr n5 G5.Adj t5 k5) ∧ (∀ t6 : ℕ, 1 ≤ t6 → ∃ L6 : ℕ, L6 + 1 = 2 ^ (t6 + 1) ∧ (Tr (2 * t6) (fun a6 b6 : Fin (2 * t6) => a6 ≠ b6 ∧ a6.val / 2 = b6.val / 2) t6 (L6) ∧ ∀ m6 : ℕ, Tr (2 * t6) (fun a6 b6 : Fin (2 * t6) => a6 ≠ b6 ∧ a6.val / 2 = b6.val / 2) t6 m6 → L6 ≤ m6)) := by
  open PEqualNP.Outside.L_pcx_107 in
  intro Tr hTr
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- Part 1: Cycles C_n
    intro n2 hn2
    refine ⟨Nat.fib ((n2 + 1) / 2 + 4) - 2, ?_, ?_, ?_⟩
    · have := fib_add_four_ge_three ((n2 + 1) / 2); omega
    · rw [hTr]
      exact hasBound_to_validN (cycleAdj_vcGe n2 hn2) (cycle_upper n2 hn2)
    · intro m2 hm2
      rw [hTr] at hm2
      obtain ⟨N, hN0, hN⟩ := hm2
      have hlb := max_deg_two_lower_bound hN (cycleAdj_symm n2) (cycleAdj_irrefl n2 hn2)
        (cycleAdj_deg_le_two n2 hn2) (fun _ => none) (by rintro ⟨u, v, _, hu, _⟩; simp at hu)
      rw [forcedSet_none, trueCount_none, Nat.sub_zero, hDeg2_zero_s] at hlb
      omega
  · -- Part 2: Paths P_n
    intro n3 hn3
    refine ⟨Nat.fib (n3 / 2 + 4) - 2, ?_, ?_, ?_⟩
    · have := fib_add_four_ge_three (n3 / 2); omega
    · rw [hTr]
      exact hasBound_to_validN (pathAdj_vcGe n3) (path_upper n3)
    · intro m3 hm3
      rw [hTr] at hm3
      obtain ⟨N, hN0, hN⟩ := hm3
      have hlb := max_deg_two_lower_bound hN (pathAdj_symm n3) (pathAdj_irrefl n3)
        (pathAdj_deg_le_two n3) (fun _ => none) (by rintro ⟨u, v, _, hu, _⟩; simp at hu)
      rw [forcedSet_none, trueCount_none, Nat.sub_zero, hDeg2_zero_s] at hlb
      omega
  · -- Part 3: Spiders S_k
    intro k4 hk4
    refine ⟨?_, ?_⟩
    · rw [hTr]
      exact hasBound_to_validN (spiderAdj_vcGe k4) (spider_upper k4 hk4)
    · intro m4 hm4
      rw [hTr] at hm4
      obtain ⟨N, hN0, hN⟩ := hm4
      have hlb := spider_lower_center_none_unforced hN (fun _ => none)
        (by rintro ⟨u, v, _, hu, _⟩; simp at hu) rfl (by rintro ⟨i, _, _, hi⟩; simp at hi)
      rw [forcedSet_none, trueCount_none, Nat.sub_zero] at hlb
      unfold gFalse at hlb
      simp only [Nat.sub_zero] at hlb
      omega
  · -- Part 4: General upper bound
    intro n5 G5 t5 _ _ hτ5
    refine ⟨2 ^ (t5 + 1) - 1, ?_, ?_⟩
    · have := pow2_ge_one (t5 + 1); omega
    · rw [hTr]
      have hhb := hasBound_general (fun u => G5.loopless.irrefl u) hτ5 t5 (fun _ => none)
        (by rw [trueCount_none]; omega)
      exact hasBound_to_validN hτ5 hhb
  · -- Part 5: Matchings t * K_2
    intro t6 ht6
    refine ⟨2 ^ (t6 + 1) - 1, ?_, ?_, ?_⟩
    · have := pow2_ge_one (t6 + 1); omega
    · rw [hTr]
      have hhb := hasBound_general (matchAdj_irrefl t6) (matchAdj_vcGe t6) t6 (fun _ => none)
        (by rw [trueCount_none]; omega)
      exact hasBound_to_validN (matchAdj_vcGe t6) hhb
    · intro m6 hm6
      rw [hTr] at hm6
      obtain ⟨N, hN0, hN⟩ := hm6
      have hlb := max_deg_one_lower_bound hN (matchAdj_symm t6) (matchAdj_irrefl t6)
        (matchAdj_deg_le_one t6) (fun _ => none) (by rintro ⟨u, v, _, hu, _⟩; simp at hu)
      rw [forcedSet_none, trueCount_none, Nat.sub_zero, fMatch_zero_s] at hlb
      omega
