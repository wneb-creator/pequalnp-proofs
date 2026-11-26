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

def boundaryA1RawMasks : List ℕ :=
  [0, 1, 2, 4, 8, 16, 32, 64, 128]

def boundaryA1Pool (family : List ℕ) : List ℕ :=
  family ++ boundaryA1RawMasks

def boundaryA1Family (i : Fin 112) : List ℕ :=
  match i.val with
  | 0 => [9, 40, 160, 177]
  | 1 => [9, 40, 176, 224]
  | 2 => [9, 40, 177, 224]
  | 3 => [12, 40, 160, 228]
  | 4 => [12, 40, 176, 224]
  | 5 => [12, 40, 176, 228]
  | 6 => [18, 176, 192, 226]
  | 7 => [26, 176, 192, 194]
  | 8 => [26, 176, 192, 226]
  | 9 => [66, 144, 178, 224]
  | 10 => [74, 144, 146, 224]
  | 11 => [74, 144, 178, 224]
  | 12 => [82, 144, 178, 224]
  | 13 => [82, 144, 178, 226]
  | 14 => [82, 144, 178, 232]
  | 15 => [82, 144, 178, 234]
  | 16 => [82, 144, 178, 240]
  | 17 => [82, 144, 178, 242]
  | 18 => [82, 144, 178, 248]
  | 19 => [82, 144, 178, 250]
  | 20 => [82, 176, 192, 226]
  | 21 => [82, 178, 192, 226]
  | 22 => [82, 184, 192, 226]
  | 23 => [82, 186, 192, 226]
  | 24 => [82, 192, 226, 240]
  | 25 => [82, 192, 226, 242]
  | 26 => [82, 192, 226, 248]
  | 27 => [82, 192, 226, 250]
  | 28 => [90, 144, 146, 224]
  | 29 => [90, 144, 146, 226]
  | 30 => [90, 144, 146, 232]
  | 31 => [90, 144, 146, 234]
  | 32 => [90, 144, 146, 240]
  | 33 => [90, 144, 146, 242]
  | 34 => [90, 144, 146, 248]
  | 35 => [90, 144, 146, 250]
  | 36 => [90, 144, 178, 224]
  | 37 => [90, 144, 178, 226]
  | 38 => [90, 144, 178, 232]
  | 39 => [90, 144, 178, 234]
  | 40 => [90, 144, 178, 240]
  | 41 => [90, 144, 178, 242]
  | 42 => [90, 144, 178, 248]
  | 43 => [90, 144, 178, 250]
  | 44 => [90, 176, 192, 194]
  | 45 => [90, 176, 192, 226]
  | 46 => [90, 178, 192, 194]
  | 47 => [90, 178, 192, 226]
  | 48 => [90, 184, 192, 194]
  | 49 => [90, 184, 192, 226]
  | 50 => [90, 186, 192, 194]
  | 51 => [90, 186, 192, 226]
  | 52 => [90, 192, 194, 240]
  | 53 => [90, 192, 194, 242]
  | 54 => [90, 192, 194, 248]
  | 55 => [90, 192, 194, 250]
  | 56 => [90, 192, 226, 240]
  | 57 => [90, 192, 226, 242]
  | 58 => [90, 192, 226, 248]
  | 59 => [90, 192, 226, 250]
  | 60 => [9, 18, 40, 176, 224]
  | 61 => [12, 40, 66, 176, 224]
  | 62 => [9, 18, 40, 145, 176, 224]
  | 63 => [9, 18, 40, 146, 176, 224]
  | 64 => [9, 18, 40, 147, 176, 224]
  | 65 => [9, 18, 40, 153, 176, 224]
  | 66 => [9, 18, 40, 154, 176, 224]
  | 67 => [9, 18, 40, 155, 176, 224]
  | 68 => [9, 18, 40, 176, 177, 224]
  | 69 => [9, 18, 40, 176, 178, 224]
  | 70 => [9, 18, 40, 176, 179, 224]
  | 71 => [9, 18, 40, 176, 185, 224]
  | 72 => [9, 18, 40, 176, 186, 224]
  | 73 => [9, 18, 40, 176, 187, 224]
  | 74 => [9, 18, 40, 176, 209, 224]
  | 75 => [9, 18, 40, 176, 210, 224]
  | 76 => [9, 18, 40, 176, 211, 224]
  | 77 => [9, 18, 40, 176, 217, 224]
  | 78 => [9, 18, 40, 176, 218, 224]
  | 79 => [9, 18, 40, 176, 219, 224]
  | 80 => [9, 18, 40, 176, 224, 241]
  | 81 => [9, 18, 40, 176, 224, 242]
  | 82 => [9, 18, 40, 176, 224, 243]
  | 83 => [9, 18, 40, 176, 224, 248]
  | 84 => [9, 18, 40, 176, 224, 249]
  | 85 => [9, 18, 40, 176, 224, 250]
  | 86 => [9, 18, 40, 176, 224, 251]
  | 87 => [12, 40, 66, 176, 194, 224]
  | 88 => [12, 40, 66, 176, 196, 224]
  | 89 => [12, 40, 66, 176, 198, 224]
  | 90 => [12, 40, 66, 176, 202, 224]
  | 91 => [12, 40, 66, 176, 204, 224]
  | 92 => [12, 40, 66, 176, 206, 224]
  | 93 => [12, 40, 66, 176, 210, 224]
  | 94 => [12, 40, 66, 176, 212, 224]
  | 95 => [12, 40, 66, 176, 214, 224]
  | 96 => [12, 40, 66, 176, 218, 224]
  | 97 => [12, 40, 66, 176, 220, 224]
  | 98 => [12, 40, 66, 176, 222, 224]
  | 99 => [12, 40, 66, 176, 224, 226]
  | 100 => [12, 40, 66, 176, 224, 228]
  | 101 => [12, 40, 66, 176, 224, 230]
  | 102 => [12, 40, 66, 176, 224, 234]
  | 103 => [12, 40, 66, 176, 224, 236]
  | 104 => [12, 40, 66, 176, 224, 238]
  | 105 => [12, 40, 66, 176, 224, 242]
  | 106 => [12, 40, 66, 176, 224, 244]
  | 107 => [12, 40, 66, 176, 224, 246]
  | 108 => [12, 40, 66, 176, 224, 248]
  | 109 => [12, 40, 66, 176, 224, 250]
  | 110 => [12, 40, 66, 176, 224, 252]
  | 111 => [12, 40, 66, 176, 224, 254]
  | _ => []

def boundaryA1Witness (i : Fin 112) : ℕ :=
  match i.val with
  | 0 => 177
  | 1 => 176
  | 2 => 177
  | 3 => 228
  | 4 => 176
  | 5 => 176
  | 6 => 176
  | 7 => 26
  | 8 => 26
  | 9 => 178
  | 10 => 74
  | 11 => 74
  | 12 => 82
  | 13 => 82
  | 14 => 82
  | 15 => 82
  | 16 => 82
  | 17 => 82
  | 18 => 82
  | 19 => 82
  | 20 => 82
  | 21 => 82
  | 22 => 82
  | 23 => 82
  | 24 => 82
  | 25 => 82
  | 26 => 82
  | 27 => 82
  | 28 => 90
  | 29 => 90
  | 30 => 90
  | 31 => 90
  | 32 => 90
  | 33 => 90
  | 34 => 90
  | 35 => 90
  | 36 => 90
  | 37 => 90
  | 38 => 90
  | 39 => 90
  | 40 => 90
  | 41 => 90
  | 42 => 90
  | 43 => 90
  | 44 => 90
  | 45 => 90
  | 46 => 90
  | 47 => 90
  | 48 => 90
  | 49 => 90
  | 50 => 90
  | 51 => 90
  | 52 => 90
  | 53 => 90
  | 54 => 90
  | 55 => 90
  | 56 => 90
  | 57 => 90
  | 58 => 90
  | 59 => 90
  | 60 => 176
  | 61 => 176
  | 62 => 145
  | 63 => 176
  | 64 => 147
  | 65 => 153
  | 66 => 154
  | 67 => 155
  | 68 => 176
  | 69 => 176
  | 70 => 176
  | 71 => 176
  | 72 => 176
  | 73 => 176
  | 74 => 176
  | 75 => 176
  | 76 => 176
  | 77 => 176
  | 78 => 176
  | 79 => 176
  | 80 => 176
  | 81 => 176
  | 82 => 176
  | 83 => 176
  | 84 => 176
  | 85 => 176
  | 86 => 176
  | 87 => 176
  | 88 => 176
  | 89 => 176
  | 90 => 176
  | 91 => 176
  | 92 => 176
  | 93 => 176
  | 94 => 176
  | 95 => 176
  | 96 => 176
  | 97 => 176
  | 98 => 176
  | 99 => 176
  | 100 => 176
  | 101 => 176
  | 102 => 176
  | 103 => 176
  | 104 => 176
  | 105 => 176
  | 106 => 176
  | 107 => 176
  | 108 => 176
  | 109 => 176
  | 110 => 176
  | 111 => 176
  | _ => 0

def boundaryA1Blocked (family : List ℕ) (m : ℕ) : Prop :=
  m ∈ family ∧ m ∉ boundaryA1RawMasks ∧
    ∀ a ∈ boundaryA1Pool family, ∀ b ∈ boundaryA1Pool family,
      a < m → b < m → Nat.lor a b ≠ m

def boundaryA1BlockedB (family : List ℕ) (m : ℕ) : Bool :=
  decide (m ∈ family) &&
    (decide (m ∉ boundaryA1RawMasks) &&
      (boundaryA1Pool family).all (fun a =>
        (boundaryA1Pool family).all (fun b =>
          decide (a < m → b < m → Nat.lor a b ≠ m))))

lemma boundaryA1BlockedB_iff (family : List ℕ) (m : ℕ) :
    boundaryA1BlockedB family m = true ↔ boundaryA1Blocked family m := by
  simp only [boundaryA1BlockedB, boundaryA1Blocked, Bool.and_eq_true,
    List.all_eq_true, decide_eq_true_eq]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma boundaryA1Catalog_checked :
    ∀ i : Fin 112, boundaryA1BlockedB (boundaryA1Family i) (boundaryA1Witness i) = true := by
  decide

lemma boundaryA1Catalog_obstruction (i : Fin 112) :
    ∃ m ∈ boundaryA1Family i, m ∉ boundaryA1RawMasks ∧
      ∀ a ∈ boundaryA1Pool (boundaryA1Family i),
      ∀ b ∈ boundaryA1Pool (boundaryA1Family i),
        a < m → b < m → Nat.lor a b ≠ m := by
  exact ⟨boundaryA1Witness i,
    ((boundaryA1BlockedB_iff _ _).mp (boundaryA1Catalog_checked i)).1,
    ((boundaryA1BlockedB_iff _ _).mp (boundaryA1Catalog_checked i)).2⟩

lemma boundaryA1Catalog_notLocallyClosed (i : Fin 112) :
    ¬ (∀ m ∈ boundaryA1Family i, m ∈ boundaryA1RawMasks ∨
      ∃ a ∈ boundaryA1Pool (boundaryA1Family i),
      ∃ b ∈ boundaryA1Pool (boundaryA1Family i),
        a < m ∧ b < m ∧ Nat.lor a b = m) := by
  intro h
  obtain ⟨m, hm, hnonraw, hblocked⟩ := boundaryA1Catalog_obstruction i
  rcases h m hm with hraw | hpair
  · exact hnonraw hraw
  · obtain ⟨a, ha, b, hb, ham, hbm, hab⟩ := hpair
    exact hblocked a ha b hb ham hbm hab

def boundaryOrSequence (base outputs : List ℕ) : Prop :=
  ∀ j (hj : j < outputs.length),
    ∃ a ∈ base ++ outputs.take j, ∃ b ∈ base ++ outputs.take j,
      Nat.lor a b = outputs[j]

lemma boundaryNotMem_take_idxOf (m : ℕ) (outputs : List ℕ) :
    m ∉ outputs.take (outputs.idxOf m) := by
  induction outputs with
  | nil => simp
  | cons x xs ih =>
      by_cases h : x = m
      · subst x
        simp
      · simp [List.idxOf_cons, h, Ne.symm h, ih]

lemma boundaryOrSequence_first_nonraw
    (base outputs pool : List ℕ)
    (hseq : boundaryOrSequence base outputs)
    (hbase : ∀ x ∈ base, x ∈ pool)
    (hpool : ∀ x ∈ outputs, x ∈ pool)
    (m : ℕ) (hm : m ∈ outputs) (hnonraw : m ∉ base) :
    ∃ a ∈ pool, ∃ b ∈ pool, a < m ∧ b < m ∧ Nat.lor a b = m := by
  have hj := List.idxOf_lt_length_of_mem hm
  obtain ⟨a, ha, b, hb, hab⟩ := hseq (outputs.idxOf m) hj
  have habm : Nat.lor a b = m := hab.trans (List.getElem_idxOf hj)
  have hbefore : ∀ x ∈ base ++ outputs.take (outputs.idxOf m),
      x ∈ pool ∧ x ≠ m := by
    intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · refine ⟨hbase x hx, ?_⟩
      intro h
      exact hnonraw (h ▸ hx)
    · refine ⟨hpool x (List.mem_of_mem_take hx), ?_⟩
      intro h
      exact boundaryNotMem_take_idxOf m outputs (h ▸ hx)
  have hane := (hbefore a ha).2
  have hbne := (hbefore b hb).2
  have hale : a ≤ m := by
    rw [← habm]
    exact Nat.left_le_or
  have hble : b ≤ m := by
    rw [← habm]
    exact Nat.right_le_or
  exact ⟨a, (hbefore a ha).1, b, (hbefore b hb).1,
    by omega, by omega, habm⟩

lemma boundaryA1Catalog_no_orSequence (i : Fin 112) (outputs : List ℕ)
    (hseq : boundaryOrSequence boundaryA1RawMasks outputs)
    (hrequired : ∀ m ∈ boundaryA1Family i, m ∈ outputs)
    (hnoaux : ∀ m ∈ outputs, m ∈ boundaryA1Pool (boundaryA1Family i)) :
    False := by
  obtain ⟨m, hm, hnonraw, hblocked⟩ := boundaryA1Catalog_obstruction i
  obtain ⟨a, ha, b, hb, ham, hbm, hab⟩ :=
    boundaryOrSequence_first_nonraw boundaryA1RawMasks outputs
      (boundaryA1Pool (boundaryA1Family i)) hseq
      (fun x hx => List.mem_append.mpr (Or.inr hx)) hnoaux
      m (hrequired m hm) hnonraw
  exact hblocked a ha b hb ham hbm hab

lemma boundaryList_noAux_of_length (family outputs : List ℕ)
    (hnodup : family.Nodup)
    (hrequired : ∀ m ∈ family, m ∈ outputs)
    (hlength : outputs.length ≤ family.length) :
    ∀ m ∈ outputs, m ∈ family := by
  intro m hm
  by_contra hnot
  have hnodup' : (m :: family).Nodup := List.nodup_cons.mpr ⟨hnot, hnodup⟩
  have hsubset : m :: family ⊆ outputs := by
    intro x hx
    rcases List.mem_cons.mp hx with h | h
    · exact h ▸ hm
    · exact hrequired x h
  have hle := hnodup'.length_le_of_subset hsubset
  simp only [List.length_cons] at hle
  omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
lemma boundaryA1Catalog_nodup :
    ∀ i : Fin 112, (boundaryA1Family i).Nodup := by
  decide

lemma boundaryA1Catalog_no_short_orSequence (i : Fin 112) (outputs : List ℕ)
    (hseq : boundaryOrSequence boundaryA1RawMasks outputs)
    (hrequired : ∀ m ∈ boundaryA1Family i, m ∈ outputs)
    (hlength : outputs.length ≤ (boundaryA1Family i).length) :
    False := by
  apply boundaryA1Catalog_no_orSequence i outputs hseq hrequired
  intro m hm
  exact List.mem_append.mpr (Or.inl
    (boundaryList_noAux_of_length (boundaryA1Family i) outputs
      (boundaryA1Catalog_nodup i) hrequired hlength m hm))

end PEqualNP.Outside.L_meta_9033_aux
