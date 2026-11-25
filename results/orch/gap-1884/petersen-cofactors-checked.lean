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


set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4000 in
lemma graph_eq_adjacent : ∀ x : Fin 10 → Bool,
    graph x = decide (∃ i j : Fin 10, x i = true ∧ x j = true ∧ adjacent i j = true) := by
  decide +kernel

lemma pivotal_adjacent : ∀ (i j k : Fin 10) (a b : Bool), i ≠ j → i ≠ k → j ≠ k →
    ¬ (a = true ∧ b = true ∧ adjacent j k = true) →
    ∃ x : Fin 10 → Bool, x j = a ∧ x k = b ∧ ∀ z : Bool,
      decide (∃ p l : Fin 10, Function.update x i z p = true ∧
        Function.update x i z l = true ∧ adjacent p l = true) = z := by
  intro i j k a b hij hik hjk hpin
  obtain ⟨x,hxj,hxk,hx⟩ := pivotal i j k a b hij hik hjk hpin
  exact ⟨x,hxj,hxk,fun z => (graph_eq_adjacent _).symm.trans (hx z)⟩

def vertexDeleted (x : Fin 9 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 ||
  x 5 && x 7 || x 6 && x 8 || x 8 && x 5

def extendNine (x : Fin 9 → Bool) (i : Fin 10) : Bool :=
  if h : i.val < 9 then x ⟨i.val,h⟩ else false

lemma cofactor_nine (x : Fin 9 → Bool) : graph (extendNine x) = vertexDeleted x := by
  simp [graph,vertexDeleted,extendNine]

set_option maxHeartbeats 1000000 in
lemma cofactor_zero_true : ∀ x : Fin 10 → Bool,
    graph (Function.update x 0 true) =
      (x 1 || x 4 || x 5 ||
        (x 2 && x 3 || x 3 && x 8 || x 8 && x 6 ||
          x 6 && x 9 || x 9 && x 7 || x 7 && x 2)) := by
  decide +kernel

lemma degree_three : ∀ i : Fin 10,
    (Finset.univ.filter fun j => adjacent i j = true).card = 3 := by
  decide +kernel

lemma no_triangles : ∀ i j k : Fin 10,
    adjacent i j = true → adjacent i k = true → adjacent j k = false := by
  decide +kernel

lemma common_neighbors : ∀ i j : Fin 10, i ≠ j →
    (Finset.univ.filter fun k => adjacent i k = true ∧ adjacent j k = true).card =
      if adjacent i j then 0 else 1 := by
  decide +kernel

lemma essential_probe : ∀ i : Fin 10, ∃ v : Fin 10, ∀ z : Bool,
    graph (Function.update (fun w => decide (w = v)) i z) = z := by
  decide +kernel

end PEqualNP.Outside.L_meta_1884
