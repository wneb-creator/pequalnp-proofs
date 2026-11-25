import Mathlib
import PEqualNP.Outside.L_meta_267

namespace PEqualNP.Outside.L_meta_650_aux.SixCoreOrEncodedAndBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_267

def orEncode {r n : ℕ} (supports : Fin n → Finset (Fin r))
    (x : Fin r → Bool) : Fin n → Bool :=
  fun j => decide (∃ i ∈ supports j, x i = true)

theorem orEncode_join {r n : ℕ} (supports : Fin n → Finset (Fin r))
    (x y : Fin r → Bool) :
    orEncode supports (jn x y) = jn (orEncode supports x) (orEncode supports y) := by
  funext j
  apply Bool.eq_iff_iff.mpr
  simp only [orEncode, jn, decide_eq_true_eq, Bool.or_eq_true]
  aesop

theorem encoded_negative_family_bound {r n : ℕ} {ι : Type} [DecidableEq ι]
    (E : (Fin r → Bool) → Fin n → Bool)
    (hjoin : ∀ x y, E (jn x y) = jn (E x) (E y))
    (f : (Fin r → Bool) → Bool) (C : Circuit) (hm : Monotone2 C)
    (heval : ∀ x, C.eval (List.ofFn (E x)) = f x)
    (Z : ι → Fin r → Bool) (S : Finset ι)
    (hz : ∀ s ∈ S, f (Z s) = false)
    (hj : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → f (jn (Z s) (Z t)) = true)
    (k : ℕ) (hk : C.gates.countP realAnd ≤ k) : S.card ≤ 2 ^ k := by
  apply bound (fun s => E (Z s)) C.output k C.gates hm hk S
  · intro s hs
    change C.eval (List.ofFn (E (Z s))) = false
    rw [heval]
    exact hz s hs
  · intro s hs t ht hne
    rw [← hjoin]
    change C.eval (List.ofFn (E (jn (Z s) (Z t)))) = true
    rw [heval]
    exact hj s hs t ht hne

theorem or_encoded_negative_family_bound {r n : ℕ} {ι : Type} [DecidableEq ι]
    (supports : Fin n → Finset (Fin r)) (f : (Fin r → Bool) → Bool)
    (C : Circuit) (hm : Monotone2 C)
    (heval : ∀ x, C.eval (List.ofFn (orEncode supports x)) = f x)
    (Z : ι → Fin r → Bool) (S : Finset ι)
    (hz : ∀ s ∈ S, f (Z s) = false)
    (hj : ∀ s ∈ S, ∀ t ∈ S, s ≠ t → f (jn (Z s) (Z t)) = true)
    (k : ℕ) (hk : C.gates.countP realAnd ≤ k) : S.card ≤ 2 ^ k :=
  encoded_negative_family_bound (orEncode supports) (orEncode_join supports)
    f C hm heval Z S hz hj k hk

theorem fiftytwo_requires_six (k : ℕ) (h : 52 ≤ 2 ^ k) : 6 ≤ k := by
  by_contra hk
  have : k ≤ 5 := by omega
  interval_cases k <;> norm_num at h

theorem twohundredtwentyeight_requires_eight (k : ℕ) (h : 228 ≤ 2 ^ k) : 8 ≤ k := by
  by_contra hk
  have : k ≤ 7 := by omega
  interval_cases k <;> norm_num at h

theorem sevenhundredfour_requires_ten (k : ℕ) (h : 704 ≤ 2 ^ k) : 10 ≤ k := by
  by_contra hk
  have : k ≤ 9 := by omega
  interval_cases k <;> norm_num at h

end PEqualNP.Outside.L_meta_650_aux.SixCoreOrEncodedAndBound

namespace PEqualNP.Outside.L_meta_650_aux.SixCoreOrEncodedAndBound.SixCore

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_267

def f (x : Fin 17 → Bool) : Bool :=
  (x 0 && (x 6 || x 7 || x 9 || x 13)) ||
  (x 1 && (x 6 || x 8 || x 12 || x 16)) ||
  (x 2 && (x 7 || x 11 || x 15 || x 16)) ||
  (x 3 && (x 6 || x 10 || x 14 || x 15)) ||
  (x 4 && (x 9 || x 11 || x 12 || x 14)) ||
  (x 5 && (x 8 || x 10 || x 11 || x 13))

def masks : Fin 52 → ℕ :=
  ![131008, 122113, 61058, 52227, 30532, 21765, 26118, 17415, 80776, 71945, 10890, 2059, 13068, 4365, 8718, 107984, 99601, 42130, 33811, 9556, 1301, 9238, 1047, 74136, 65817, 8346, 8476, 285, 8222, 119520, 118817, 49826, 49187, 21092, 20517, 16934, 16423, 70312, 69673, 682, 4652, 4141, 558, 98544, 98353, 32946, 32819, 116, 65720, 65593, 186, 63]

def zeros (i : Fin 52) : Fin 17 → Bool := fun j => (masks i).testBit j.val

theorem zeros_false : ∀ i : Fin 52, f (zeros i) = false := by
  decide +kernel

theorem distinct_joins_true : ∀ i j : Fin 52, i ≠ j → f (jn (zeros i) (zeros j)) = true := by
  decide +kernel

theorem at_least_six_paid_ands (n : ℕ) (supports : Fin n → Finset (Fin 17))
    (C : Circuit) (hm : Monotone2 C)
    (heval : ∀ x, C.eval (List.ofFn (orEncode supports x)) = f x) :
    6 ≤ C.gates.countP realAnd := by
  have hb := or_encoded_negative_family_bound supports f C hm heval zeros Finset.univ
    (fun i _ => zeros_false i) (fun i _ j _ hij => distinct_joins_true i j hij)
    (C.gates.countP realAnd) le_rfl
  have h52 : 52 ≤ 2 ^ C.gates.countP realAnd := by simpa using hb
  exact fiftytwo_requires_six _ h52

end PEqualNP.Outside.L_meta_650_aux.SixCoreOrEncodedAndBound.SixCore
