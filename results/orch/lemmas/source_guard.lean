import prefix_monotone
import independent_guard

namespace PEqualNP.Outside.L_meta_1886_aux.SourceGuard

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended
open IndependentGuard

lemma maximal_independent_input (p : Fin 10 → Fin 10) (pre suffix : List Gate)
    (source outIdx : ℕ) (rest : List ℕ)
    (legal : FanInTwo (Circuit.mk (pre ++ ⟨.not,source :: rest⟩ :: suffix) outIdx))
    (prefixMono : Monotone2 (Circuit.mk pre source))
    (suffixMono : Monotone2 (Circuit.mk suffix outIdx))
    (used : ∃ q ∈ suffix, 11 + pre.length ∈ q.inputs)
    (budget : (Circuit.mk (pre ++ ⟨.not,source :: rest⟩ :: suffix) outIdx).size ≤ 18)
    (correct : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨.not,source :: rest⟩ :: suffix) outIdx).eval
        (List.ofFn (x ∘ p) ++ [x 0 && x 1]) = f10 x) :
    ∃ m ∈ maximalMasks,
      (Circuit.mk pre source).eval (List.ofFn (row m ∘ p) ++ [row m 0 && row m 1]) = true ∧
        f10 (row m) = false := by
  let g : (Fin 10 → Bool) → Bool := fun x =>
    (Circuit.mk pre source).eval (List.ofFn (x ∘ p) ++ [x 0 && x 1])
  have mono : ∀ x y, (∀ i, x i ≤ y i) → g x ≤ g y :=
    PrefixMonotone.source_monotone p pre source prefixMono
  have notDominated : ¬ ∀ x, g x ≤ MapRigidity.edge10 x := by
    intro below
    have bound := DominatedSourceWitness.lower p pre suffix source outIdx rest
      legal suffixMono used below correct
    omega
  exact maximal_guard_witness g mono notDominated

end PEqualNP.Outside.L_meta_1886_aux.SourceGuard
