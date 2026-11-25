import Mathlib
import PEqualNP.Outside.L_meta_267

namespace PEqualNP.Outside.L_meta_650_aux.OrEncodedAndBound

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

end PEqualNP.Outside.L_meta_650_aux.OrEncodedAndBound
