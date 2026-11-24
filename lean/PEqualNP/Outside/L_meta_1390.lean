import PEqualNP.Outside.L_meta_669
import PEqualNP.Outside.L_meta_738
import PEqualNP.Outside.L_meta_782
import PEqualNP.Outside.L_meta_1020
import PEqualNP.MetaComplexity.L1341

theorem PEqualNP.Outside.L_meta_1390 : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (Ckt : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 Ckt → PEqualNP.CircuitLowerBounds.HasLineDegree (N + N) (Finset.Ico N (N + N)) Ckt 3 → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) Ckt z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → (Finset.univ.filter (fun e : Fin N × Fin N => I e.1 e.2)).card ≤ 888 * Ckt.size + 9 * N + 444 :=
  PEqualNP.MetaComplexity.L1341 PEqualNP.Outside.L_meta_669 PEqualNP.Outside.L_meta_738 PEqualNP.Outside.L_meta_782 PEqualNP.Outside.L_meta_1020
