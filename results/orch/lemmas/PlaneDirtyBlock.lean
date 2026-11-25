import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583_aux

open CircuitLowerBounds MetaComplexity

def dirtyBlock : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.and, [4, 5]⟩,
    ⟨.or, [0, 1]⟩, ⟨.and, [6, 7]⟩], 8⟩

def cleanBlock : Circuit :=
  ⟨[⟨.or, [1, 3]⟩, ⟨.and, [0, 4]⟩,
    ⟨.and, [2, 1]⟩, ⟨.or, [5, 6]⟩], 7⟩

def blockTarget (z : Fin 4 → Bool) : Bool :=
  (z 0 && z 1) || (z 0 && z 3) || (z 2 && z 1)

abbrev blockGraph : SimpleGraph (Fin 4) where
  Adj i j :=
    (i = 0 ∧ j = 1) ∨ (i = 1 ∧ j = 0) ∨
    (i = 0 ∧ j = 3) ∨ (i = 3 ∧ j = 0) ∨
    (i = 2 ∧ j = 1) ∨ (i = 1 ∧ j = 2)
  symm := ⟨by decide⟩
  loopless := ⟨by decide⟩

lemma dirtyBlock_ao : TopForm.IsAO2 4 dirtyBlock := by decide

lemma dirtyBlock_computes : ∀ z, circuitFun 4 dirtyBlock z = blockTarget z := by
  decide

lemma dirtyBlock_no_four_cycle : TopForm.NoFourCycle blockGraph := by decide

lemma dirtyBlock_graph_target :
    ∀ z, NestedCover.graphFun blockGraph ∅ z = blockTarget z := by decide

lemma dirtyBlock_top_form : TopForm.TopForm blockGraph dirtyBlock := by decide

lemma dirtyBlock_centreless : TopForm.centreless blockGraph dirtyBlock = {4} := by
  decide

lemma dirtyBlock_junk : TopForm.junk blockGraph dirtyBlock = {2} := by decide

lemma dirtyBlock_no_cross_edges : TopForm.starEdges blockGraph dirtyBlock = ∅ := by
  decide

lemma dirtyBlock_size : dirtyBlock.size = 5 := rfl

lemma dirtyBlock_edge_prime : ReadK.IsPrimeImplicant 4 dirtyBlock {0, 1} := by
  decide

lemma dirtyBlock_edge_repeats :
    ReadK.readsAtMost dirtyBlock 4 (ReadK.setList ({0, 1} : Finset (Fin 4))) 1 = false := by
  decide

lemma dirtyBlock_not_read_one : ¬ ReadK.IsReadK 4 dirtyBlock 1 := by
  intro h
  have hread := h {0, 1} dirtyBlock_edge_prime
  rw [dirtyBlock_edge_repeats] at hread
  cases hread

lemma cleanBlock_ao : TopForm.IsAO2 4 cleanBlock := by decide

lemma cleanBlock_computes : ∀ z, circuitFun 4 cleanBlock z = blockTarget z := by
  decide

lemma cleanBlock_read_one : ReadK.IsReadK 4 cleanBlock 1 := by
  unfold ReadK.IsReadK
  decide

lemma cleanBlock_size : cleanBlock.size = 4 := rfl

end PEqualNP.Outside.L_meta_2583_aux
