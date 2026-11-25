import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012

def threeByThreeCode (E : Fin 3 → Fin 3 → Bool) : Fin 512 :=
  (if E 0 0 then 1 else 0) + (if E 0 1 then 2 else 0) + (if E 0 2 then 4 else 0) +
  (if E 1 0 then 8 else 0) + (if E 1 1 then 16 else 0) + (if E 1 2 then 32 else 0) +
  (if E 2 0 then 64 else 0) + (if E 2 1 then 128 else 0) + (if E 2 2 then 256 else 0)

def fiveIndependentMasks (E : Fin 3 → Fin 3 → Bool) : List ℕ :=
  match (threeByThreeCode E).val with
  | 273 => [7, 14, 21, 28, 35]
  | 275 => [7, 14, 28, 35, 42]
  | 277 => [7, 14, 21, 28, 42]
  | 279 => [7, 14, 28, 42, 56]
  | 281 => [7, 21, 28, 35, 49]
  | 285 => [7, 21, 28, 34, 56]
  | 305 => [7, 14, 21, 28, 49]
  | 307 => [7, 14, 28, 33, 56]
  | 309 => [7, 14, 21, 28, 56]
  | 313 => [7, 21, 28, 49, 56]
  | 337 => [7, 21, 35, 42, 49]
  | 339 => [7, 20, 35, 42, 56]
  | 345 => [7, 21, 35, 49, 56]
  | 369 => [7, 10, 21, 49, 56]
  | 371 => [7, 10, 20, 33, 56]
  | 401 => [7, 14, 35, 42, 49]
  | 403 => [7, 14, 35, 42, 56]
  | 405 => [7, 14, 17, 42, 56]
  | 409 => [7, 12, 35, 49, 56]
  | 413 => [7, 12, 17, 34, 56]
  | 465 => [7, 35, 42, 49, 56]
  | _ => []

def fiveIndependentWitness (E : Fin 3 → Fin 3 → Bool)
    (r : Fin 5) (v : Fin 6) : Bool :=
  ((fiveIndependentMasks E).getD r.val 0).testBit v.val

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
lemma finiteFiveCertificates :
    ∀ E : Fin 3 → Fin 3 → Bool,
      (∀ i : Fin 3, E i i = true) →
      (∀ i j a b : Fin 3, i ≠ j → a ≠ b →
        ¬ (E i a = true ∧ E i b = true ∧ E j a = true ∧ E j b = true)) →
      (∀ r : Fin 5, ∀ i j : Fin 3, E i j = true →
        ¬ (fiveIndependentWitness E r (Fin.castAdd 3 i) = true ∧
          fiveIndependentWitness E r (Fin.natAdd 3 j) = true)) ∧
      (∀ r s : Fin 5, r ≠ s → ∃ i : Fin 3,
        (fiveIndependentWitness E r (Fin.castAdd 3 i) = true ∧
          fiveIndependentWitness E s (Fin.natAdd 3 i) = true) ∨
        (fiveIndependentWitness E s (Fin.castAdd 3 i) = true ∧
          fiveIndependentWitness E r (Fin.natAdd 3 i) = true)) := by
  decide

lemma fiveIndependentCertificate (E : Fin 3 → Fin 3 → Bool)
    (hd : ∀ i : Fin 3, E i i = true)
    (h4 : ∀ i j a b : Fin 3, i ≠ j → a ≠ b →
      ¬ (E i a = true ∧ E i b = true ∧ E j a = true ∧ E j b = true)) :
    ∃ t : Fin 5 → Fin 6 → Bool,
      (∀ r : Fin 5, ∀ i j : Fin 3, E i j = true →
        ¬ (t r (Fin.castAdd 3 i) = true ∧ t r (Fin.natAdd 3 j) = true)) ∧
      (∀ r s : Fin 5, r ≠ s → ∃ i : Fin 3,
        (t r (Fin.castAdd 3 i) = true ∧ t s (Fin.natAdd 3 i) = true) ∨
        (t s (Fin.castAdd 3 i) = true ∧ t r (Fin.natAdd 3 i) = true)) := by
  exact ⟨fiveIndependentWitness E, finiteFiveCertificates E hd h4⟩

end PEqualNP.Outside.L_meta_5012
