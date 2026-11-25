import Mathlib

namespace PEqualNP.Outside.L_meta_4970

def starDisjunction {α : Type*} [DecidableEq α] (Q : Finset α) (x : α → Bool) : Bool :=
  decide (∃ i ∈ Q, x i = true)

lemma monotone_factor_eq_star {α : Type*} [DecidableEq α]
    (Q : Finset α) (f : (α → Bool) → Bool) (hf : Monotone f)
    (hz : f (fun i => decide (i ∉ Q)) = false)
    (hcontains : ∀ x, starDisjunction Q x = true → f x = true) :
    ∀ x, f x = starDisjunction Q x := by
  intro x
  cases hx : starDisjunction Q x with
  | false =>
      have hzero : ∀ i ∈ Q, x i = false := by
        intro i hi
        cases hxi : x i with
        | false => rfl
        | true =>
            have : starDisjunction Q x = true := by
              simp only [starDisjunction, decide_eq_true_eq]
              exact ⟨i, hi, hxi⟩
            simp [hx] at this
      have hle : x ≤ fun i => decide (i ∉ Q) := by
        intro i
        by_cases hi : i ∈ Q
        · simp [hi, hzero i hi]
        · simp [hi]
      have hfx := hf hle
      rw [hz] at hfx
      exact le_antisymm hfx (by cases f x <;> decide)
  | true => exact hcontains x hx

lemma monotone_and_eq_star {α : Type*} [DecidableEq α]
    (Q : Finset α) (f g : (α → Bool) → Bool)
    (hf : Monotone f) (hg : Monotone g)
    (h : ∀ x, (f x && g x) = starDisjunction Q x) :
    (∀ x, f x = starDisjunction Q x) ∨
      (∀ x, g x = starDisjunction Q x) := by
  have hcontains : ∀ x, starDisjunction Q x = true → f x = true ∧ g x = true := by
    intro x hx
    have hh := h x
    rw [hx] at hh
    simpa only [Bool.and_eq_true] using hh
  have hz : starDisjunction Q (fun i => decide (i ∉ Q)) = false := by
    simp [starDisjunction]
  have hzfg : f (fun i => decide (i ∉ Q)) = false ∨
      g (fun i => decide (i ∉ Q)) = false := by
    have hh := h (fun i => decide (i ∉ Q))
    rw [hz] at hh
    simpa only [Bool.and_eq_false_iff] using hh
  rcases hzfg with hzf | hzg
  · exact Or.inl (monotone_factor_eq_star Q f hf hzf fun x hx => (hcontains x hx).1)
  · exact Or.inr (monotone_factor_eq_star Q g hg hzg fun x hx => (hcontains x hx).2)

namespace SparseTests

def singletonInput {α : Type*} [DecidableEq α] (i : α) : α → Bool :=
  fun j => decide (j = i)

def starFun {α : Type*} [DecidableEq α] (Q : Finset α) (x : α → Bool) : Bool :=
  decide (∃ i ∈ Q, x i = true)

lemma star_eq_of_sparse_tests {α : Type*} [DecidableEq α]
    (Q : Finset α) (f : (α → Bool) → Bool) (hf : Monotone f)
    (hpos : ∀ i ∈ Q, f (singletonInput i) = true)
    (hneg : f (fun i => decide (i ∉ Q)) = false) :
    ∀ x, f x = starFun Q x := by
  intro x
  cases hx : starFun Q x with
  | false =>
      have hn : ¬ ∃ i ∈ Q, x i = true := by
        simpa only [starFun, decide_eq_false_iff_not] using hx
      have hle : x ≤ fun i => decide (i ∉ Q) := by
        intro i
        by_cases hi : i ∈ Q
        · have hxi : x i = false := by
            cases hxi : x i with
            | false => rfl
            | true => exact False.elim (hn ⟨i, hi, hxi⟩)
          simp [hi, hxi]
        · simp [hi]
      have hfx := hf hle
      rw [hneg] at hfx
      exact le_antisymm hfx (by cases f x <;> decide)
  | true =>
      have hp : ∃ i ∈ Q, x i = true := by
        simpa only [starFun, decide_eq_true_eq] using hx
      obtain ⟨i, hi, hxi⟩ := hp
      have hle : singletonInput i ≤ x := by
        intro j
        by_cases hji : j = i
        · subst j
          simp [singletonInput, hxi]
        · simp [singletonInput, hji]
      have hfx := hf hle
      rw [hpos i hi] at hfx
      exact le_antisymm (by cases f x <;> decide) hfx

def edgeInput {p l : ℕ} (a : Fin p) (b : Fin l) : Fin p ⊕ Fin l → Bool
  | Sum.inl a' => decide (a' = a)
  | Sum.inr b' => decide (b' = b)

def edgeFun {p l : ℕ} (E : Finset (Fin p × Fin l)) (x : Fin p ⊕ Fin l → Bool) : Bool :=
  decide (∃ a b, (a, b) ∈ E ∧ x (Sum.inl a) = true ∧ x (Sum.inr b) = true)

def saturatedIndependentInput {p l : ℕ} (E : Finset (Fin p × Fin l))
    (A : Finset (Fin p)) : Fin p ⊕ Fin l → Bool
  | Sum.inl a => decide (a ∈ A)
  | Sum.inr b => decide (∀ a ∈ A, (a, b) ∉ E)

lemma graph_eq_of_sparse_tests {p l : ℕ} (E : Finset (Fin p × Fin l))
    (f : (Fin p ⊕ Fin l → Bool) → Bool) (hf : Monotone f)
    (hpos : ∀ a b, (a, b) ∈ E → f (edgeInput a b) = true)
    (hneg : ∀ A, f (saturatedIndependentInput E A) = false) :
    ∀ x, f x = edgeFun E x := by
  intro x
  cases hx : edgeFun E x with
  | false =>
      have hn : ¬ ∃ a b, (a, b) ∈ E ∧ x (Sum.inl a) = true ∧ x (Sum.inr b) = true := by
        simpa only [edgeFun, decide_eq_false_iff_not] using hx
      let A : Finset (Fin p) := Finset.univ.filter fun a => x (Sum.inl a) = true
      have hle : x ≤ saturatedIndependentInput E A := by
        intro i
        cases i with
        | inl a =>
            cases ha : x (Sum.inl a) <;> simp [saturatedIndependentInput, A, ha]
        | inr b =>
            cases hb : x (Sum.inr b) with
            | false => simp
            | true =>
                have hcompat : ∀ a ∈ A, (a, b) ∉ E := by
                  intro a ha hab
                  have hax : x (Sum.inl a) = true := (Finset.mem_filter.mp ha).2
                  exact hn ⟨a, b, hab, hax, hb⟩
                change true ≤ decide (∀ a ∈ A, (a, b) ∉ E)
                rw [decide_eq_true hcompat]
      have hfx := hf hle
      rw [hneg A] at hfx
      exact le_antisymm hfx (by cases f x <;> decide)
  | true =>
      have hp : ∃ a b, (a, b) ∈ E ∧ x (Sum.inl a) = true ∧ x (Sum.inr b) = true := by
        simpa only [edgeFun, decide_eq_true_eq] using hx
      obtain ⟨a, b, hab, ha, hb⟩ := hp
      have hle : edgeInput a b ≤ x := by
        intro i
        cases i with
        | inl a' =>
            by_cases haa : a' = a
            · subst a'
              simp [edgeInput, ha]
            · simp [edgeInput, haa]
        | inr b' =>
            by_cases hbb : b' = b
            · subst b'
              simp [edgeInput, hb]
            · simp [edgeInput, hbb]
      have hfx := hf hle
      rw [hpos a b hab] at hfx
      exact le_antisymm (by cases f x <;> decide) hfx

def conjunctionFun {α : Type*} [DecidableEq α] (Q : Finset α) (x : α → Bool) : Bool :=
  decide (∀ i ∈ Q, x i = true)

lemma conjunction_eq_of_sparse_tests {α : Type*} [DecidableEq α]
    (Q : Finset α) (f : (α → Bool) → Bool) (hf : Monotone f)
    (hpos : f (fun i => decide (i ∈ Q)) = true)
    (hneg : ∀ i ∈ Q, f (fun j => decide (j ≠ i)) = false) :
    ∀ x, f x = conjunctionFun Q x := by
  intro x
  cases hx : conjunctionFun Q x with
  | false =>
      have hn : ¬ ∀ i ∈ Q, x i = true := by
        simpa only [conjunctionFun, decide_eq_false_iff_not] using hx
      push Not at hn
      obtain ⟨i, hi, hxi⟩ := hn
      have hfalse : x i = false := by
        cases h : x i with
        | false => rfl
        | true => exact False.elim (hxi h)
      have hle : x ≤ fun j => decide (j ≠ i) := by
        intro j
        by_cases hji : j = i
        · subst j
          simp [hfalse]
        · simp [hji]
      have hfx := hf hle
      rw [hneg i hi] at hfx
      exact le_antisymm hfx (by cases f x <;> decide)
  | true =>
      have hp : ∀ i ∈ Q, x i = true := by
        simpa only [conjunctionFun, decide_eq_true_eq] using hx
      have hle : (fun i => decide (i ∈ Q)) ≤ x := by
        intro i
        by_cases hi : i ∈ Q
        · simp [hi, hp i hi]
        · simp [hi]
      have hfx := hf hle
      rw [hpos] at hfx
      exact le_antisymm (by cases f x <;> decide) hfx

end SparseTests

lemma off_diagonal_factorization {α : Type*} (P Q : α → Prop) :
    (∃ a b, a ≠ b ∧ P a ∧ Q b) ↔
      (∃ a, P a) ∧ (∃ b, Q b) ∧
        ∃ a b, a ≠ b ∧ (P a ∨ Q a) ∧ (P b ∨ Q b) := by
  classical
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, a, b, hab, Or.inl ha, Or.inr hb⟩
  · rintro ⟨⟨p, hp⟩, ⟨q, hq⟩, a, b, hab, ha, hb⟩
    by_cases hpq : p = q
    · subst q
      have hdiff : a ≠ p ∨ b ≠ p := by
        by_cases hap : a = p
        · right
          intro hbp
          exact hab (hap.trans hbp.symm)
        · exact Or.inl hap
      rcases hdiff with hap | hbp
      · rcases ha with hpa | hqa
        · exact ⟨a, p, hap, hpa, hq⟩
        · exact ⟨p, a, Ne.symm hap, hp, hqa⟩
      · rcases hb with hpb | hqb
        · exact ⟨b, p, hbp, hpb, hq⟩
        · exact ⟨p, b, Ne.symm hbp, hp, hqb⟩
    · exact ⟨p, q, hpq, hp, hq⟩

lemma threshold_two_bit_cuts {α β : Type*} (code : α → β → Bool)
    (hinj : Function.Injective code) (P : α → Prop) :
    (∃ a b, a ≠ b ∧ P a ∧ P b) ↔
      ∃ t, (∃ a, P a ∧ code a t = false) ∧ (∃ b, P b ∧ code b t = true) := by
  classical
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    have hcodes : code a ≠ code b := fun h => hab (hinj h)
    have ht : ∃ t, code a t ≠ code b t := by
      by_contra hh
      push Not at hh
      exact hcodes (funext hh)
    obtain ⟨t, ht⟩ := ht
    cases hat : code a t <;> cases hbt : code b t
    · exact False.elim (ht (hat.trans hbt.symm))
    · exact ⟨t, ⟨a, ha, hat⟩, ⟨b, hb, hbt⟩⟩
    · exact ⟨t, ⟨b, hb, hbt⟩, ⟨a, ha, hat⟩⟩
    · exact False.elim (ht (hat.trans hbt.symm))
  · rintro ⟨t, ⟨a, ha, hat⟩, ⟨b, hb, hbt⟩⟩
    refine ⟨a, b, ?_, ha, hb⟩
    intro hab
    subst b
    simp [hat] at hbt

lemma off_diagonal_rectangle_bound (n k : ℕ)
    (A B : Fin k → Finset (Fin n))
    (hdiag : ∀ t, Disjoint (A t) (B t))
    (hcover : ∀ i j, i ≠ j → ∃ t, i ∈ A t ∧ j ∈ B t) :
    n ≤ k.choose (k / 2) := by
  classical
  let S : Fin n → Finset (Fin k) := fun i => Finset.univ.filter fun t => i ∈ A t
  have hnon : ∀ i j, i ≠ j → ¬ S i ⊆ S j := by
    intro i j hij hs
    obtain ⟨t, hi, hj⟩ := hcover i j hij
    have hti : t ∈ S i := by simp [S, hi]
    have htj : j ∈ A t := by simpa [S] using hs hti
    exact Finset.disjoint_left.mp (hdiag t) htj hj
  have hinj : Function.Injective S := by
    intro i j hij
    by_contra hne
    exact hnon i j hne (hij ▸ Finset.Subset.refl _)
  let family : Finset (Finset (Fin k)) := Finset.univ.image S
  have ha : IsAntichain (· ⊆ ·) (family : Set (Finset (Fin k))) := by
    intro s hs t ht hst hsub
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp ht
    exact hnon i j (fun hij => hst (congrArg S hij)) hsub
  have hc : family.card = n := by
    dsimp [family]
    rw [Finset.card_image_of_injective _ hinj]
    simp
  simpa [hc] using ha.sperner

lemma off_diagonal_seven_cuts (P Q : (Fin 7 → Bool) → Prop) :
    (∃ a b, a ≠ b ∧ P a ∧ Q b) ↔
      (∃ a, P a) ∧ (∃ b, Q b) ∧
        ∃ t : Fin 7,
          (∃ a, (P a ∨ Q a) ∧ a t = false) ∧
            (∃ b, (P b ∨ Q b) ∧ b t = true) := by
  rw [off_diagonal_factorization]
  rw [threshold_two_bit_cuts (fun a : Fin 7 → Bool => a) Function.injective_id]

lemma seven_bit_card : Fintype.card (Fin 7 → Bool) = 128 := by simp

lemma no_nine_rectangle_cover_128 :
    ¬ ∃ A B : Fin 9 → Finset (Fin 128),
      (∀ t, Disjoint (A t) (B t)) ∧
        ∀ i j, i ≠ j → ∃ t, i ∈ A t ∧ j ∈ B t := by
  rintro ⟨A, B, hdiag, hcover⟩
  have h := off_diagonal_rectangle_bound 128 9 A B hdiag hcover
  exact (by decide : ¬ 128 ≤ Nat.choose 9 (9 / 2)) h

namespace MandatoryInputs

-- These identities do not assert an OR-count lower bound.
-- The ordered pair domain includes diagonal pairs, which record singleton deletions.
-- For arbitrary functions the pair set records evaluations; its implicate meaning uses monotonicity.

def Mandatory {α : Type*} (f : (α → Bool) → Bool) (a : α) : Prop :=
  ∀ x, f x = true → x a = true

def core {α : Type*} (f : (α → Bool) → Bool) : Set α :=
  {a | Mandatory f a}


lemma core_or {α : Type*} (f g : (α → Bool) → Bool) :
    core (fun x => f x || g x) = core f ∩ core g := by
  ext a
  change Mandatory (fun x => f x || g x) a ↔ Mandatory f a ∧ Mandatory g a
  constructor
  · intro h
    constructor
    · intro x hx
      exact h x (by simp [hx])
    · intro x hx
      exact h x (by simp [hx])
  · rintro ⟨hf, hg⟩ x hx
    have hh : f x = true ∨ g x = true := by simpa using hx
    rcases hh with h | h
    · exact hf x h
    · exact hg x h

lemma core_and {α : Type*} (f g : (α → Bool) → Bool)
    (hf : Monotone f) (hg : Monotone g) :
    core (fun x => f x && g x) = core f ∪ core g := by
  ext a
  change Mandatory (fun x => f x && g x) a ↔ Mandatory f a ∨ Mandatory g a
  classical
  constructor
  · intro h
    by_contra hn
    have hnf : ¬ Mandatory f a := fun hc => hn (Or.inl hc)
    have hng : ¬ Mandatory g a := fun hc => hn (Or.inr hc)
    simp only [Mandatory, not_forall] at hnf hng
    obtain ⟨x, hfx, hxa⟩ := hnf
    obtain ⟨y, hgy, hya⟩ := hng
    let z : α → Bool := fun i => x i || y i
    have hxz : x ≤ z := by
      intro i
      dsimp [z]
      cases x i <;> cases y i <;> first | exact le_rfl | exact Bool.false_le true
    have hyz : y ≤ z := by
      intro i
      dsimp [z]
      cases x i <;> cases y i <;> first | exact le_rfl | exact Bool.false_le true
    have hfz : f z = true := by
      have hh := hf hxz
      rw [hfx] at hh
      exact le_antisymm (Bool.le_true _) hh
    have hgz : g z = true := by
      have hh := hg hyz
      rw [hgy] at hh
      exact le_antisymm (Bool.le_true _) hh
    have hza : z a ≠ true := by
      dsimp [z]
      cases hx : x a <;> cases hy : y a <;> simp_all
    exact hza (h z (by simp [hfz, hgz]))
  · intro h x hx
    have hh : f x = true ∧ g x = true := by simpa using hx
    rcases h with h | h
    · exact h x hh.1
    · exact h x hh.2

def conjunction {α : Type*} (Q : Finset α) (x : α → Bool) : Bool :=
  decide (∀ a ∈ Q, x a = true)

lemma core_conjunction {α : Type*} [DecidableEq α] (Q : Finset α) :
    core (conjunction Q) = (Q : Set α) := by
  ext a
  constructor
  · intro h
    by_contra ha
    have ht : conjunction Q (fun i => decide (i ∈ Q)) = true := by
      simp [conjunction]
    have := h (fun i => decide (i ∈ Q)) ht
    apply ha
    change a ∈ Q
    simpa only [decide_eq_true_eq] using this
  · intro ha x hx
    have hh : ∀ i ∈ Q, x i = true := by
      simpa only [conjunction, decide_eq_true_eq] using hx
    exact hh a ha

def fullMinusPair {α : Type*} [DecidableEq α] (a b : α) : α → Bool :=
  fun i => decide (i ≠ a ∧ i ≠ b)

def pairImplicates {α : Type*} [DecidableEq α] (f : (α → Bool) → Bool) : Set (α × α) :=
  {pair | f (fullMinusPair pair.1 pair.2) = false}

lemma pairImplicates_and {α : Type*} [DecidableEq α] (f g : (α → Bool) → Bool) :
    pairImplicates (fun x => f x && g x) = pairImplicates f ∪ pairImplicates g := by
  ext pair
  change (f (fullMinusPair pair.1 pair.2) && g (fullMinusPair pair.1 pair.2)) = false ↔
    f (fullMinusPair pair.1 pair.2) = false ∨ g (fullMinusPair pair.1 pair.2) = false
  cases f (fullMinusPair pair.1 pair.2) <;> cases g (fullMinusPair pair.1 pair.2) <;> simp

lemma pairImplicates_or {α : Type*} [DecidableEq α] (f g : (α → Bool) → Bool) :
    pairImplicates (fun x => f x || g x) = pairImplicates f ∩ pairImplicates g := by
  ext pair
  simp [pairImplicates]

lemma pairImplicates_input {α : Type*} [DecidableEq α] (i : α) :
    pairImplicates (fun x => x i) = {pair | i = pair.1 ∨ i = pair.2} := by
  ext pair
  by_cases ha : i = pair.1 <;> by_cases hb : i = pair.2 <;>
    simp [pairImplicates, fullMinusPair, ha, hb]


end MandatoryInputs

end PEqualNP.Outside.L_meta_4970
