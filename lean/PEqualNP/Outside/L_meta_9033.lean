import Mathlib.Data.Fin.Basic

namespace PEqualNP.Outside.L_meta_9033_aux

def boundaryGate (op a b : Bool) : Bool :=
  if op then a && b else a || b

def boundaryRowRel (expected a b : Bool) : Prop :=
  a = expected → b = expected

lemma boundaryRowRel_refl (expected a : Bool) :
    boundaryRowRel expected a a := by
  intro h
  exact h

lemma boundaryRowRel_trans {expected a b c : Bool}
    (hab : boundaryRowRel expected a b)
    (hbc : boundaryRowRel expected b c) :
    boundaryRowRel expected a c := by
  intro h
  exact hbc (hab h)

lemma boundaryRowRel_gate (expected op a b a' b' : Bool)
    (ha : boundaryRowRel expected a a')
    (hb : boundaryRowRel expected b b') :
    boundaryRowRel expected (boundaryGate op a b) (boundaryGate op a' b') := by
  cases expected <;> cases op <;> cases a <;> cases b <;>
    cases a' <;> cases b' <;> simp_all [boundaryRowRel, boundaryGate]

lemma boundaryReplacement (expected : Bool)
    (n k pivot source output : ℕ)
    (op : ℕ → Bool) (a b : ℕ → ℕ) (before after : ℕ → Bool)
    (hcausal : ∀ i < k, a i < n + i ∧ b i < n + i)
    (hpivot : pivot < k)
    (hsource : source < n + pivot)
    (hout : output < n + k)
    (hraw : ∀ j < n, after j = before j)
    (hbefore : ∀ i < k,
      before (n + i) = boundaryGate (op i) (before (a i)) (before (b i)))
    (hafter : ∀ i < k, i ≠ pivot →
      after (n + i) = boundaryGate (op i) (after (a i)) (after (b i)))
    (halias : after (n + pivot) = after source)
    (hdominance : boundaryRowRel expected (before (n + pivot)) (before source))
    (houtput : before output = expected) :
    after output = expected := by
  have hrel : ∀ j, j < n + k → boundaryRowRel expected (before j) (after j) := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj
      by_cases hinput : j < n
      · rw [hraw j hinput]
        exact boundaryRowRel_refl expected (before j)
      · obtain ⟨i, rfl⟩ : ∃ i, j = n + i := by
          exact ⟨j - n, by omega⟩
        have hi : i < k := by omega
        by_cases heq : i = pivot
        · subst i
          rw [halias]
          exact boundaryRowRel_trans hdominance
            (ih source hsource (Nat.lt_trans hsource (Nat.add_lt_add_left hpivot n)))
        · rw [hbefore i hi, hafter i hi heq]
          exact boundaryRowRel_gate expected (op i) _ _ _ _
            (ih (a i) (hcausal i hi).1 (Nat.lt_trans (hcausal i hi).1 hj))
            (ih (b i) (hcausal i hi).2 (Nat.lt_trans (hcausal i hi).2 hj))
  exact hrel output hout houtput

def boundaryGraph8 (x : Fin 8 → Bool) : Bool :=
  (x 0 && x 6) || (x 0 && x 7) || (x 1 && x 3) ||
  (x 1 && x 5) || (x 2 && x 4) || (x 2 && x 7) ||
  (x 3 && x 5) || (x 3 && x 7) || (x 4 && x 5) ||
  (x 4 && x 6) || (x 5 && x 6)

def boundaryRaise (v : Fin 8) (x : Fin 8 → Bool) : Fin 8 → Bool :=
  fun i => if i = v then true else x i

def boundarySingleton (v : Fin 8) : Fin 8 → Bool :=
  boundaryRaise v (fun _ => false)

def boundaryDerivativeMask (v a : Fin 8) : ℕ :=
  match v.val, a.val with
  | 0, 1 => 66 | 0, 2 => 68 | 0, 3 => 72 | 0, 4 => 144
  | 0, 5 => 160 | 0, 6 => 64 | 0, 7 => 128
  | 1, 0 => 9 | 1, 2 => 12 | 1, 3 => 8 | 1, 4 => 24
  | 1, 5 => 32 | 1, 6 => 72 | 1, 7 => 160
  | 2, 0 => 17 | 2, 1 => 18 | 2, 3 => 24 | 2, 4 => 16
  | 2, 5 => 160 | 2, 6 => 192 | 2, 7 => 128
  | _, _ => 0

def boundaryDerivativeRow (v a : Fin 8) : Fin 8 → Bool :=
  fun i => (boundaryDerivativeMask v a).testBit i.val

lemma boundaryDerivativeRow_spec :
    ∀ v a : Fin 8, v.val < 3 → a ≠ v →
      boundaryDerivativeRow v a a = true ∧
      boundaryGraph8 (boundaryDerivativeRow v a) = false ∧
      boundaryGraph8 (boundaryRaise v (boundaryDerivativeRow v a)) = true := by
  decide

lemma boundaryNeutral_zeroOnDerivative {α : Type*}
    (G S M : α → Bool) (x y : α)
    (hmono : M x = true → M y = true)
    (hcut : (S x || M x) = (S y || M y) → G x = G y)
    (hdiff : G x ≠ G y) : M x = false := by
  cases hx : M x with
  | false => rfl
  | true =>
      have hy := hmono hx
      exact False.elim (hdiff (hcut (by simp [hx, hy])))

lemma boundaryMonotone_false_of_le
    (M : (Fin 8 → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → M x = true → M y = true)
    (x y : Fin 8 → Bool)
    (hle : ∀ i, x i = true → y i = true)
    (hy : M y = false) : M x = false := by
  cases hx : M x with
  | false => rfl
  | true =>
      have h := hmono x y hle hx
      simp [hy] at h

lemma boundaryNeutral_singleton_zero
    (v : Fin 8) (hv : v.val < 3)
    (S M : (Fin 8 → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → M x = true → M y = true)
    (hindependent : ∀ x, M (boundaryRaise v x) = M x)
    (hcut : ∀ x,
      (S x || M x) = (S (boundaryRaise v x) || M (boundaryRaise v x)) →
      boundaryGraph8 x = boundaryGraph8 (boundaryRaise v x)) :
    ∀ a : Fin 8, M (boundarySingleton a) = false := by
  have hrow : ∀ a : Fin 8, a ≠ v → M (boundaryDerivativeRow v a) = false := by
    intro a ha
    obtain ⟨_, hfalse, htrue⟩ := boundaryDerivativeRow_spec v a hv ha
    apply boundaryNeutral_zeroOnDerivative boundaryGraph8 S M
      (boundaryDerivativeRow v a) (boundaryRaise v (boundaryDerivativeRow v a))
    · intro h
      rw [hindependent]
      exact h
    · exact hcut _
    · rw [hfalse, htrue]
      decide
  have hseven : (7 : Fin 8) ≠ v := by
    intro h
    have hval := congrArg Fin.val h
    change 7 = v.val at hval
    omega
  have hempty : M (fun _ => false) = false := by
    apply boundaryMonotone_false_of_le M hmono (fun _ => false)
      (boundaryDerivativeRow v 7)
    · intro i h
      cases h
    · exact hrow 7 hseven
  intro a
  by_cases ha : a = v
  · subst a
    change M (boundaryRaise v (fun _ => false)) = false
    rw [hindependent, hempty]
  · apply boundaryMonotone_false_of_le M hmono (boundarySingleton a)
      (boundaryDerivativeRow v a)
    · intro i hi
      by_cases heq : i = a
      · subst i
        exact (boundaryDerivativeRow_spec v a hv ha).1
      · simp [boundarySingleton, boundaryRaise, heq] at hi
    · exact hrow a ha

end PEqualNP.Outside.L_meta_9033_aux
