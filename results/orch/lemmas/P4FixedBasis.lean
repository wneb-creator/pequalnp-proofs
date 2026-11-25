import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1772_aux.P4FixedBasis

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership

abbrev graph : SimpleGraph (Fin 4) := edgeGraph 4 [(0, 2), (0, 3), (1, 2)]

def basis : List Gate :=
  [⟨GateOp.or, [0, 1]⟩, ⟨GateOp.or, [2, 3]⟩, ⟨GateOp.or, [0, 2]⟩]

def monoOp (conjunction : Bool) : GateOp := if conjunction then GateOp.and else GateOp.or

def extension (conj1 : Bool) (a b : Fin 7) (conj2 : Bool) (c d : Fin 8) : Circuit :=
  ⟨basis ++ [⟨monoOp conj1, [a.val, b.val]⟩, ⟨monoOp conj2, [c.val, d.val]⟩], 8⟩

abbrev dirty : Circuit := extension true 4 5 true 7 6

lemma no_triangles : ∀ a b c : Fin 4, graph.Adj a b → graph.Adj b c → ¬ graph.Adj c a := by
  decide

lemma no_four_cycle : PEqualNP.TopForm.NoFourCycle graph := by decide

lemma dirty_computes : circuitFun 4 dirty = graphFun graph ∅ := by decide

lemma dirty_unowned : ∀ u v : Fin 4, graph.Adj u v → ¬ Owns 4 dirty 4 u v := by decide

def clean : Circuit :=
  ⟨[⟨GateOp.or, [0, 1]⟩, ⟨GateOp.and, [2, 4]⟩,
    ⟨GateOp.and, [0, 3]⟩, ⟨GateOp.or, [5, 6]⟩], 7⟩

lemma clean_computes : circuitFun 4 clean = graphFun graph ∅ := by decide

lemma clean_and_owners : Owns 4 clean 1 0 2 ∧ Owns 4 clean 2 0 3 := by decide

lemma gate_counts : dirty.size = 5 ∧ clean.size = 4 := by decide

end PEqualNP.Outside.L_meta_1772_aux.P4FixedBasis
