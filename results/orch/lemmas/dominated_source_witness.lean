import dominated_source

namespace PEqualNP.Outside.L_meta_1886_aux.DominatedSourceWitness

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended

lemma lower (p : Fin 10 → Fin 10) (pre suffix : List Gate) (source outIdx : ℕ) (rest : List ℕ)
    (legal : FanInTwo (Circuit.mk (pre ++ ⟨.not,source :: rest⟩ :: suffix) outIdx))
    (mono : Monotone2 (Circuit.mk suffix outIdx))
    (used : ∃ q ∈ suffix, 11 + pre.length ∈ q.inputs)
    (below : ∀ x : Fin 10 → Bool,
      (Circuit.mk pre source).eval (List.ofFn (x ∘ p) ++ [x 0 && x 1]) ≤ f10 x)
    (correct : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨.not,source :: rest⟩ :: suffix) outIdx).eval
        (List.ofFn (x ∘ p) ++ [x 0 && x 1]) = f10 x) :
    19 ≤ (Circuit.mk (pre ++ ⟨.not,source :: rest⟩ :: suffix) outIdx).size := by
  have legalNormalized : FanInTwo (Circuit.mk (pre ++ ⟨.not,[source]⟩ :: suffix) outIdx) := by
    intro q hq
    rcases List.mem_append.mp hq with hp | ht
    · exact legal q (List.mem_append_left _ hp)
    · rcases List.mem_cons.mp ht with rfl | hs
      · simp
      · exact legal q (List.mem_append_right _ (List.mem_cons_of_mem _ hs))
  have correctNormalized : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨.not,[source]⟩ :: suffix) outIdx).eval
        (List.ofFn (x ∘ p) ++ [x 0 && x 1]) = f10 x := by
    intro x
    rw [SeedNotOperands.ignore_not_tail pre suffix source outIdx rest]
    exact correct x
  have bound := DominatedSource.arbitrary_map_lower p pre suffix source outIdx
    legalNormalized mono used below correctNormalized
  simpa only [Circuit.size,List.length_append,List.length_cons] using bound

lemma independent_input (p : Fin 10 → Fin 10) (pre suffix : List Gate)
    (source outIdx : ℕ) (rest : List ℕ)
    (legal : FanInTwo (Circuit.mk (pre ++ ⟨.not,source :: rest⟩ :: suffix) outIdx))
    (mono : Monotone2 (Circuit.mk suffix outIdx))
    (used : ∃ q ∈ suffix, 11 + pre.length ∈ q.inputs)
    (budget : (Circuit.mk (pre ++ ⟨.not,source :: rest⟩ :: suffix) outIdx).size ≤ 18)
    (correct : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨.not,source :: rest⟩ :: suffix) outIdx).eval
        (List.ofFn (x ∘ p) ++ [x 0 && x 1]) = f10 x) :
    ∃ x : Fin 10 → Bool,
      (Circuit.mk pre source).eval (List.ofFn (x ∘ p) ++ [x 0 && x 1]) = true ∧ f10 x = false := by
  have bad : ¬ ∀ x : Fin 10 → Bool,
      (Circuit.mk pre source).eval (List.ofFn (x ∘ p) ++ [x 0 && x 1]) ≤ f10 x := by
    intro below
    have bound := lower p pre suffix source outIdx rest legal mono used below correct
    omega
  obtain ⟨x,hx⟩ := not_forall.mp bad
  refine ⟨x,?_,?_⟩ <;>
    cases hg : (Circuit.mk pre source).eval (List.ofFn (x ∘ p) ++ [x 0 && x 1]) <;>
    cases hf : f10 x <;> simp_all [Bool.le_iff_imp]

end PEqualNP.Outside.L_meta_1886_aux.DominatedSourceWitness
