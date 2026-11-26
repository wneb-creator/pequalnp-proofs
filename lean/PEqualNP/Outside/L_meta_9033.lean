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

def boundaryClear (v : Fin 8) (x : Fin 8 → Bool) : Fin 8 → Bool :=
  fun i => if i = v then false else x i

lemma boundaryRaise_clear (v : Fin 8) (x : Fin 8 → Bool) :
    boundaryRaise v (boundaryClear v x) = boundaryRaise v x := by
  funext i
  by_cases h : i = v <;> simp [boundaryRaise, boundaryClear, h]

lemma boundaryClear_invariant (v : Fin 8) (M : (Fin 8 → Bool) → Bool)
    (hindependent : ∀ x, M (boundaryRaise v x) = M x)
    (x : Fin 8 → Bool) : M (boundaryClear v x) = M x := by
  have h := hindependent (boundaryClear v x)
  rw [boundaryRaise_clear, hindependent x] at h
  exact h.symm

def boundaryNegativeMask (r : Fin 10) : ℕ :=
  match r.val with
  | 0 => 7 | 1 => 13 | 2 => 19 | 3 => 25 | 4 => 37
  | 5 => 70 | 6 => 76 | 7 => 146 | 8 => 160 | 9 => 194
  | _ => 0

def boundaryNegativeRow (r : Fin 10) : Fin 8 → Bool :=
  fun i => (boundaryNegativeMask r).testBit i.val

lemma boundaryNegativeRow_false :
    ∀ r : Fin 10, boundaryGraph8 (boundaryNegativeRow r) = false := by
  decide

lemma boundaryNegativeRow_maximal :
    ∀ (r : Fin 10) (v : Fin 8), boundaryNegativeRow r v = false →
      boundaryGraph8 (boundaryRaise v (boundaryNegativeRow r)) = true := by
  decide

lemma boundaryNeutral_negative_support
    (v : Fin 8) (S M : (Fin 8 → Bool) → Bool)
    (hindependent : ∀ x, M (boundaryRaise v x) = M x)
    (hcut : ∀ x,
      (S x || M x) = (S (boundaryRaise v x) || M (boundaryRaise v x)) →
      boundaryGraph8 x = boundaryGraph8 (boundaryRaise v x)) :
    ∀ r : Fin 10, M (boundaryNegativeRow r) = true →
      boundaryNegativeRow r v = true := by
  intro r hM
  cases hv : boundaryNegativeRow r v with
  | true => rfl
  | false =>
      have hz := boundaryNeutral_zeroOnDerivative boundaryGraph8 S M
        (boundaryNegativeRow r) (boundaryRaise v (boundaryNegativeRow r))
        (by intro h; rw [hindependent]; exact h) (hcut _)
        (by rw [boundaryNegativeRow_false r, boundaryNegativeRow_maximal r v hv]; decide)
      rw [hM] at hz
      cases hz

lemma boundaryNegative_remainder :
    ∀ (r : Fin 10) (u v : Fin 8), u.val < 3 → v.val < 3 → u ≠ v →
      boundaryNegativeRow r u = true → boundaryNegativeRow r v = true →
      ∃ a : Fin 8, ∀ i : Fin 8,
        boundaryClear u (boundaryClear v (boundaryNegativeRow r)) i = true →
          boundarySingleton a i = true := by
  decide

lemma boundaryNeutral_negative_disjoint
    (u v : Fin 8) (hu : u.val < 3) (hv : v.val < 3) (hne : u ≠ v)
    (M N : (Fin 8 → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → M x = true → M y = true)
    (huindependent : ∀ x, M (boundaryRaise u x) = M x)
    (hvindependent : ∀ x, M (boundaryRaise v x) = M x)
    (hsingleton : ∀ a : Fin 8, M (boundarySingleton a) = false)
    (husupport : ∀ r : Fin 10,
      M (boundaryNegativeRow r) = true → boundaryNegativeRow r u = true)
    (hvsupport : ∀ r : Fin 10,
      N (boundaryNegativeRow r) = true → boundaryNegativeRow r v = true) :
    ∀ r : Fin 10, M (boundaryNegativeRow r) = true →
      N (boundaryNegativeRow r) = false := by
  intro r hM
  cases hN : N (boundaryNegativeRow r) with
  | false => rfl
  | true =>
      obtain ⟨a, hle⟩ := boundaryNegative_remainder r u v hu hv hne
        (husupport r hM) (hvsupport r hN)
      have hcleared :
          M (boundaryClear u (boundaryClear v (boundaryNegativeRow r))) = true := by
        rw [boundaryClear_invariant u M huindependent,
          boundaryClear_invariant v M hvindependent]
        exact hM
      have h := hmono _ _ hle hcleared
      rw [hsingleton a] at h
      cases h

lemma boundaryNeutral_pair_disjoint
    (u v : Fin 8) (hu : u.val < 3) (hv : v.val < 3) (hne : u ≠ v)
    (S M T N : (Fin 8 → Bool) → Bool)
    (hmono : ∀ x y, (∀ i, x i = true → y i = true) → M x = true → M y = true)
    (huindependent : ∀ x, M (boundaryRaise u x) = M x)
    (hvindependent : ∀ x, M (boundaryRaise v x) = M x)
    (hNindependent : ∀ x, N (boundaryRaise v x) = N x)
    (hMcut : ∀ x,
      (S x || M x) = (S (boundaryRaise u x) || M (boundaryRaise u x)) →
      boundaryGraph8 x = boundaryGraph8 (boundaryRaise u x))
    (hNcut : ∀ x,
      (T x || N x) = (T (boundaryRaise v x) || N (boundaryRaise v x)) →
      boundaryGraph8 x = boundaryGraph8 (boundaryRaise v x)) :
    ∀ r : Fin 10, M (boundaryNegativeRow r) = true →
      N (boundaryNegativeRow r) = false := by
  exact boundaryNeutral_negative_disjoint u v hu hv hne M N hmono
    huindependent hvindependent
    (boundaryNeutral_singleton_zero u hu S M hmono huindependent hMcut)
    (boundaryNeutral_negative_support u S M huindependent hMcut)
    (boundaryNeutral_negative_support v T N hNindependent hNcut)

end PEqualNP.Outside.L_meta_9033_aux
