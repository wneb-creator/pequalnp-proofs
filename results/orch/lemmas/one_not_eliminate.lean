import one_not_compile

namespace PEqualNP.Outside.L_meta_2592_aux.OneNotEliminate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open ConstantSweep OneNotCompile

lemma touched_count {m : ℕ} {suffix : List Gate} {outIdx : ℕ}
    (hs : Monotone2 (Circuit.mk suffix outIdx))
    (used : ∃ q ∈ suffix, m ∈ q.inputs) :
    1 ≤ (suffix.filter (touched {m})).length := by
  obtain ⟨q,hq,hi⟩ := used
  have hg := hs q hq
  have hw : width q.op = 2 := by
    rcases hg.1 with h | h
    · rw [h]
      decide
    · rw [h]
      decide
  have ht : touched {m} q = true := by
    unfold touched
    rw [hw, List.take_of_length_le hg.2]
    exact List.any_eq_true.mpr ⟨m,hi,by simp⟩
  have hm : q ∈ suffix.filter (touched {m}) := List.mem_filter.mpr ⟨hq,ht⟩
  exact List.length_pos_iff.mpr (List.ne_nil_of_mem hm)

lemma eliminate_consumed_dominated_not {n : ℕ} (F : (Fin n → Bool) → Bool)
    (pre suffix : List Gate) (source outIdx : ℕ)
    (hp : ∀ q ∈ pre, good q)
    (hs : Monotone2 (Circuit.mk suffix outIdx))
    (correct : ∀ x, (Circuit.mk (pre ++ ⟨.not,[source]⟩ :: suffix) outIdx).eval
      (List.ofFn x) = F x)
    (below : ∀ x, (run pre (List.ofFn x)).getD source false ≤ F x)
    (used : ∃ q ∈ suffix, n + pre.length ∈ q.inputs)
    (nonconstant : ∃ x y, F x ≠ F y) :
    ∃ (out : List Gate) (j : ℕ),
      FanInTwo (Circuit.mk (pre ++ out) j) ∧
      (Circuit.mk (pre ++ out) j).size + 2 ≤
        (Circuit.mk (pre ++ ⟨.not,[source]⟩ :: suffix) outIdx).size ∧
      ∀ x, (Circuit.mk (pre ++ out) j).eval (List.ofFn x) = F x := by
  have split : ∀ x, F x = (Circuit.mk suffix outIdx).eval
      (run pre (List.ofFn x) ++ [!((run pre (List.ofFn x)).getD source false)]) := by
    intro x
    have hc := (correct x).symm
    change F x = (run (pre ++ ⟨.not,[source]⟩ :: suffix) (List.ofFn x)).getD outIdx false at hc
    rw [run_append] at hc
    exact hc
  obtain ⟨out,j,hout,hsize,hcorrect⟩ :=
    eliminate_dominated_not F (fun x => (run pre (List.ofFn x)).getD source false)
      pre suffix outIdx hs split below nonconstant
  refine ⟨out,j,?_,?_,hcorrect⟩
  · intro q hq
    exact (List.mem_append.mp hq).elim (hp q) (hout q)
  · have hcount := touched_count hs used
    simp only [Circuit.size, List.length_append, List.length_cons]
    omega

end PEqualNP.Outside.L_meta_2592_aux.OneNotEliminate
