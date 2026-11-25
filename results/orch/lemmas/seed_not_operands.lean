import arbitrary_map_seed_not

namespace PEqualNP.Outside.L_meta_1886_aux.SeedNotOperands

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended

lemma ignore_not_tail (pre suffix : List Gate) (source outIdx : ℕ) (rest : List ℕ) (w : List Bool) :
    (Circuit.mk (pre ++ ⟨.not,[source]⟩ :: suffix) outIdx).eval w =
      (Circuit.mk (pre ++ ⟨.not,source :: rest⟩ :: suffix) outIdx).eval w := by
  simp only [Circuit.eval,Circuit.wires,List.foldl_append,List.foldl_cons]
  rfl

lemma consumed_seed_not_lower (p : Fin 10 → Fin 10) (pre suffix : List Gate)
    (outIdx : ℕ) (rest : List ℕ)
    (legal : FanInTwo (Circuit.mk (pre ++ ⟨.not,10 :: rest⟩ :: suffix) outIdx))
    (mono : Monotone2 (Circuit.mk suffix outIdx))
    (used : ∃ q ∈ suffix, 11 + pre.length ∈ q.inputs)
    (correct : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨.not,10 :: rest⟩ :: suffix) outIdx).eval
        (List.ofFn (x ∘ p) ++ [x 0 && x 1]) = f10 x) :
    19 ≤ (Circuit.mk (pre ++ ⟨.not,10 :: rest⟩ :: suffix) outIdx).size := by
  have legalNormalized : FanInTwo (Circuit.mk (pre ++ ⟨.not,[10]⟩ :: suffix) outIdx) := by
    intro q hq
    rcases List.mem_append.mp hq with hp | ht
    · exact legal q (List.mem_append_left _ hp)
    · rcases List.mem_cons.mp ht with rfl | hs
      · simp
      · exact legal q (List.mem_append_right _ (List.mem_cons_of_mem _ hs))
  have correctNormalized : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨.not,[10]⟩ :: suffix) outIdx).eval
        (List.ofFn (x ∘ p) ++ [x 0 && x 1]) = f10 x := by
    intro x
    rw [ignore_not_tail pre suffix 10 outIdx rest]
    exact correct x
  have lower := ArbitraryMapSeedNot.consumed_seed_not_lower p pre suffix outIdx
    legalNormalized mono used correctNormalized
  simpa only [Circuit.size,List.length_append,List.length_cons] using lower

lemma consumed_seed_not_exclusion (p : Fin 10 → Fin 10) (pre suffix : List Gate)
    (outIdx : ℕ) (rest : List ℕ)
    (legal : FanInTwo (Circuit.mk (pre ++ ⟨.not,10 :: rest⟩ :: suffix) outIdx))
    (mono : Monotone2 (Circuit.mk suffix outIdx))
    (used : ∃ q ∈ suffix, 11 + pre.length ∈ q.inputs)
    (budget : (Circuit.mk (pre ++ ⟨.not,10 :: rest⟩ :: suffix) outIdx).size ≤ 18) :
    ∃ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨.not,10 :: rest⟩ :: suffix) outIdx).eval
        (List.ofFn (x ∘ p) ++ [x 0 && x 1]) ≠ f10 x := by
  by_contra! correct
  have lower := consumed_seed_not_lower p pre suffix outIdx rest legal mono used correct
  omega

end PEqualNP.Outside.L_meta_1886_aux.SeedNotOperands
