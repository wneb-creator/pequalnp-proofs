import monotone_circuit_banks
import mode_floor

namespace PEqualNP.Outside.L_meta_1886_aux.MonotoneCircuitFloor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux.Stronger
open Extended CanonicalBank

lemma raw_lower {L : ℕ} (floor : Lower false inputs graph L)
    (C : Circuit) (p : Fin 10 → Fin 10) (mono : Monotone2 C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ p)) = f10 x) :
    L + 2 ≤ C.size := by
  obtain ⟨k,S,hk,run,raw⟩ := MonotoneCircuitBanks.realize_raw C p mono computes
  exact (ModeFloor.raw_lower floor run raw).trans hk

lemma supplied_lower {L : ℕ} (floor : Lower false inputs graph L)
    (C : Circuit) (p : Fin 10 → Fin 10) (choice : Bool) (mono : Monotone2 C)
    (computes : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ p) ++ [if choice = true then x 0 && x 1 else x 0 || x 1]) = f10 x) :
    (if choice = true then L + 2 else L + 1) ≤ C.size := by
  obtain ⟨k,S,hk,run,raw⟩ := MonotoneCircuitBanks.realize_supplied C p choice mono computes
  cases choice with
  | false =>
    have bound : L + 1 ≤ k := ModeFloor.or_bank_lower floor 0 1 (by decide) run (by
      simpa [bank,extra] using raw)
    simpa using bound.trans hk
  | true =>
    have bound : L + 2 ≤ k := ModeFloor.and_bank_lower floor 0 1 (by decide) run (by
      simpa [bank,extra] using raw)
    simpa using bound.trans hk

lemma and_lower {L : ℕ} (floor : Lower false inputs graph L)
    (C : Circuit) (p : Fin 10 → Fin 10) (mono : Monotone2 C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ p) ++ [x 0 && x 1]) = f10 x) :
    L + 2 ≤ C.size := by
  exact supplied_lower floor C p true mono computes

lemma or_lower {L : ℕ} (floor : Lower false inputs graph L)
    (C : Circuit) (p : Fin 10 → Fin 10) (mono : Monotone2 C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ p) ++ [x 0 || x 1]) = f10 x) :
    L + 1 ≤ C.size := by
  exact supplied_lower floor C p false mono computes

end PEqualNP.Outside.L_meta_1886_aux.MonotoneCircuitFloor
