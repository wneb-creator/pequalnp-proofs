import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def graph (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def adjacent (i j : Fin 10) : Bool :=
  (([50,69,138,276,521,385,770,548,104,208] : List ℕ).getD i.val 0).testBit j.val

def pinned (j k v : Fin 10) (a b : Bool) (w : Fin 10) : Bool :=
  if w = j then a else if w = k then b else decide (w = v)

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
lemma pivotal_probes :
    ∀ (i j k : Fin 10) (a b : Bool), i ≠ j → i ≠ k → j ≠ k →
      ¬ (a = true ∧ b = true ∧ adjacent j k = true) →
      ∃ v : Fin 10, ∀ z : Bool,
        graph (Function.update (pinned j k v a b) i z) = z := by
  decide +kernel

lemma pivotal : ∀ (i j k : Fin 10) (a b : Bool), i ≠ j → i ≠ k → j ≠ k →
    ¬ (a = true ∧ b = true ∧ adjacent j k = true) →
    ∃ x : Fin 10 → Bool, x j = a ∧ x k = b ∧
      ∀ z : Bool, graph (Function.update x i z) = z := by
  intro i j k a b hij hik hjk hpin
  obtain ⟨v,hv⟩ := pivotal_probes i j k a b hij hik hjk hpin
  exact ⟨pinned j k v a b, by simp [pinned], by simp [pinned,Ne.symm hjk], hv⟩

end PEqualNP.Outside.L_meta_1884
