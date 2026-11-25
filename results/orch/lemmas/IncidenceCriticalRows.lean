import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.IncidenceCriticalRows

def Below {n : ℕ} (x y : Fin n → Bool) : Prop :=
  ∀ i, x i = true → y i = true

def MonotoneFun {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, Below x y → f x = true → f y = true

def target {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (x : Fin (n + m) → Bool) : Bool :=
  decide (∃ p l, I p l ∧ x (Fin.castAdd m p) = true ∧ x (Fin.natAdd n l) = true)

def pairInput {n m : ℕ} (p : Fin n) (l : Fin m) (i : Fin (n + m)) : Bool :=
  decide (i = Fin.castAdd m p ∨ i = Fin.natAdd n l)

def closedInput {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (s : Fin n → Bool) : Fin (n + m) → Bool :=
  Fin.append s (fun l => decide (∀ p, I p l → s p = false))

theorem pair_true {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (p : Fin n) (l : Fin m) (hp : I p l) : target I (pairInput p l) = true := by
  apply decide_eq_true
  exact ⟨p, l, hp, by simp [pairInput], by simp [pairInput]⟩

theorem closure_false {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (s : Fin n → Bool) : target I (closedInput I s) = false := by
  cases ht : target I (closedInput I s) with
  | false => rfl
  | true =>
    obtain ⟨p, l, hp, hleft, hright⟩ := of_decide_eq_true ht
    simp only [closedInput, Fin.append_left] at hleft
    simp only [closedInput, Fin.append_right, decide_eq_true_eq] at hright
    exact Bool.noConfusion ((hright p hp).symm.trans hleft)

theorem true_above_pair {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (x : Fin (n + m) → Bool) (hx : target I x = true) :
    ∃ p l, I p l ∧ Below (pairInput p l) x := by
  obtain ⟨p, l, hp, hxp, hxl⟩ := of_decide_eq_true hx
  refine ⟨p, l, hp, fun i hi => ?_⟩
  rcases of_decide_eq_true hi with rfl | rfl
  · exact hxp
  · exact hxl

theorem false_below_closure {n m : ℕ} (I : Fin n → Fin m → Prop) [DecidableRel I]
    (x : Fin (n + m) → Bool) (hx : target I x = false) :
    Below x (closedInput I (fun p => x (Fin.castAdd m p))) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro p hp
    simpa only [closedInput, Fin.append_left] using hp
  · intro l hl
    simp only [closedInput, Fin.append_right, decide_eq_true_eq]
    intro p hp
    cases hxp : x (Fin.castAdd m p) with
    | false => rfl
    | true =>
      have htrue : target I x = true := by
        apply decide_eq_true
        exact ⟨p, l, hp, hxp, hl⟩
      exact Bool.noConfusion (hx.symm.trans htrue)

theorem correct_of_critical_rows {n m : ℕ} (I : Fin n → Fin m → Prop)
    [DecidableRel I] (f : (Fin (n + m) → Bool) → Bool)
    (mono : MonotoneFun f)
    (positive : ∀ p l, I p l → f (pairInput p l) = true)
    (negative : ∀ s : Fin n → Bool, f (closedInput I s) = false) :
    ∀ x, f x = target I x := by
  intro x
  cases hx : target I x with
  | false =>
    cases hf : f x with
    | false => rfl
    | true =>
      have h := mono x _ (false_below_closure I x hx) hf
      exact Bool.noConfusion ((negative _).symm.trans h)
  | true =>
    obtain ⟨p, l, hp, hpx⟩ := true_above_pair I x hx
    exact mono _ x hpx (positive p l hp)

theorem correct_of_negative_cover {n m : ℕ} (I : Fin n → Fin m → Prop)
    [DecidableRel I] (f : (Fin (n + m) → Bool) → Bool)
    (tests : List (Fin (n + m) → Bool))
    (cover : ∀ s : Fin n → Bool, ∃ y ∈ tests, Below (closedInput I s) y)
    (mono : MonotoneFun f)
    (positive : ∀ p l, I p l → f (pairInput p l) = true)
    (negative : ∀ y ∈ tests, f y = false) :
    ∀ x, f x = target I x := by
  apply correct_of_critical_rows I f mono positive
  intro s
  obtain ⟨y, hy, hsy⟩ := cover s
  cases hf : f (closedInput I s) with
  | false => rfl
  | true => exact Bool.noConfusion ((negative y hy).symm.trans (mono _ y hsy hf))

end PEqualNP.Outside.L_meta_2583.IncidenceCriticalRows
