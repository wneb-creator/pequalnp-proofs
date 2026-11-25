import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

open PEqualNP.CircuitLowerBounds

lemma p4_identity (a b c d : Bool) :
    (((a || c) && (b || d)) && (b || c)) =
      ((a && b) || (b && c) || (c && d)) := by
  cases a <;> cases b <;> cases c <;> cases d <;> rfl

def p4Block : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.or, [1, 3]⟩, ⟨.or, [1, 2]⟩,
    ⟨.and, [4, 5]⟩, ⟨.and, [7, 6]⟩], 8⟩

def p4Stars : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [1, 4]⟩,
    ⟨.and, [2, 3]⟩, ⟨.or, [5, 6]⟩], 7⟩

def p4Fun (z : Fin 4 → Bool) : Bool :=
  (z 0 && z 1) || (z 1 && z 2) || (z 2 && z 3)

def p4Graph : SimpleGraph (Fin 4) :=
  SimpleGraph.fromRel fun u v =>
    (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 3)

abbrev p4GraphDec : DecidableRel p4Graph.Adj := by
  unfold p4Graph
  infer_instance

lemma p4Graph_noFourCycle : @PEqualNP.TopForm.NoFourCycle 4 p4Graph p4GraphDec := by
  decide

lemma p4Graph_bipartite : ∀ u v : Fin 4, p4Graph.Adj u v →
    decide (u = 0 ∨ u = 2) ≠ decide (v = 0 ∨ v = 2) := by
  let := p4GraphDec
  decide

lemma p4Fun_graph : ∀ z : Fin 4 → Bool,
    @PEqualNP.MetaComplexity.NestedCover.graphFun 4 p4Graph p4GraphDec ∅ z = p4Fun z := by
  decide

lemma p4Block_ao2 : PEqualNP.TopForm.IsAO2 4 p4Block := by
  decide

lemma p4Stars_ao2 : PEqualNP.TopForm.IsAO2 4 p4Stars := by
  decide

lemma p4Block_eval : ∀ z : Fin 4 → Bool,
    PEqualNP.MetaComplexity.circuitFun 4 p4Block z = p4Fun z := by
  decide

lemma p4Stars_eval : ∀ z : Fin 4 → Bool,
    PEqualNP.MetaComplexity.circuitFun 4 p4Stars z = p4Fun z := by
  decide

lemma p4Block_not_readOne : ¬ PEqualNP.ReadK.IsReadK 4 p4Block 1 := by
  decide

lemma p4Stars_readOne : PEqualNP.ReadK.IsReadK 4 p4Stars 1 := by
  decide

lemma p4Block_size : p4Block.size = 5 := rfl

lemma p4Stars_size : p4Stars.size = 4 := rfl

lemma p4Block_internal_not_below : ∀ j : Fin 4, ∃ z : Fin 4 → Bool,
    PEqualNP.EdgeOwnership.gateVal 4 p4Block j z = true ∧ p4Fun z = false := by
  decide

def p4Bypass (j : Fin 5) (b : Fin 2) : Circuit :=
  let w := (p4Block.gates.getD j ⟨.or, []⟩).inputs.getD b 0
  ⟨p4Block.gates.set j ⟨.or, [w, w]⟩, p4Block.output⟩

lemma p4Block_no_bypass : ∀ j : Fin 5, ∀ b : Fin 2,
    ∃ z : Fin 4 → Bool,
      PEqualNP.MetaComplexity.circuitFun 4 (p4Bypass j b) z ≠ p4Fun z := by
  decide


namespace Additional

open PEqualNP.CircuitLowerBounds

def p4Mixed : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [2, 3]⟩,
    ⟨.or, [1, 5]⟩, ⟨.and, [4, 6]⟩], 7⟩

def p4Fun (z : Fin 4 → Bool) : Bool :=
  (z 0 && z 1) || (z 1 && z 2) || (z 2 && z 3)

lemma p4Mixed_ao2 : PEqualNP.TopForm.IsAO2 4 p4Mixed := by
  decide

lemma p4Mixed_eval : ∀ z : Fin 4 → Bool,
    PEqualNP.MetaComplexity.circuitFun 4 p4Mixed z = p4Fun z := by
  decide

lemma p4Mixed_not_readOne : ¬ PEqualNP.ReadK.IsReadK 4 p4Mixed 1 := by
  decide

lemma p4Mixed_size : p4Mixed.size = 4 := rfl

lemma p4Mixed_internal_below : ∀ z : Fin 4 → Bool,
    PEqualNP.EdgeOwnership.gateVal 4 p4Mixed 1 z = true → p4Fun z = true := by
  decide

lemma p4Mixed_internal_term : ∀ z : Fin 4 → Bool,
    PEqualNP.EdgeOwnership.gateVal 4 p4Mixed 1 z = (z 2 && z 3) := by
  decide

end Additional

namespace DoubleStar

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [1, 2]⟩, ⟨.or, [4, 5]⟩, ⟨.or, [3, 6]⟩,
    ⟨.and, [1, 7]⟩, ⟨.or, [0, 9]⟩, ⟨.and, [8, 10]⟩], 11⟩

def disabled : Circuit :=
  ⟨circuit.gates.set 0 ⟨.or, []⟩, circuit.output⟩

def edgeFun (z : Fin 6 → Bool) : Bool :=
  (z 0 && z 1) || (z 0 && z 2) || (z 0 && z 3) ||
    (z 1 && z 4) || (z 1 && z 5)

def changedFun (z : Fin 6 → Bool) : Bool :=
  z 3 && (z 0 || (z 1 && (z 4 || z 5)))

lemma circuit_ao2 : PEqualNP.TopForm.IsAO2 6 circuit := by
  decide

lemma circuit_size : circuit.size = 6 := rfl

lemma circuit_eval : ∀ z : Fin 6 → Bool,
    PEqualNP.MetaComplexity.circuitFun 6 circuit z = edgeFun z := by
  decide

lemma disabled_eval : ∀ z : Fin 6 → Bool,
    PEqualNP.MetaComplexity.circuitFun 6 disabled z = changedFun z := by
  decide

lemma circuit_prime_iff : ∀ S : Finset (Fin 6),
    PEqualNP.ReadK.IsPrimeImplicant 6 circuit S ↔
      S = {0, 1} ∨ S = {0, 2} ∨ S = {0, 3} ∨ S = {1, 4} ∨ S = {1, 5} := by
  decide

lemma disabled_new_triple :
    PEqualNP.ReadK.IsPrimeImplicant 6 disabled {1, 3, 4} := by
  decide

lemma circuit_triple_not_prime :
    ¬ PEqualNP.ReadK.IsPrimeImplicant 6 circuit {1, 3, 4} := by
  decide

lemma disabled_prime_iff : ∀ S : Finset (Fin 6),
    PEqualNP.ReadK.IsPrimeImplicant 6 disabled S ↔
      S = {0, 3} ∨ S = {1, 3, 4} ∨ S = {1, 3, 5} := by
  decide

def pruned : Circuit :=
  ⟨[⟨.or, [4, 5]⟩, ⟨.and, [1, 6]⟩,
    ⟨.or, [0, 7]⟩, ⟨.and, [3, 8]⟩], 9⟩

lemma pruned_ao2 : PEqualNP.TopForm.IsAO2 6 pruned := by
  decide

lemma pruned_size : pruned.size = 4 := rfl

lemma pruned_eval : ∀ z : Fin 6 → Bool,
    PEqualNP.MetaComplexity.circuitFun 6 pruned z = changedFun z := by
  decide

lemma pruned_triple_prime :
    PEqualNP.ReadK.IsPrimeImplicant 6 pruned {1, 3, 4} := by
  decide

end DoubleStar

namespace PathDeletion

open PEqualNP.CircuitLowerBounds

def circuit : Circuit :=
  ⟨[⟨.or, [0, 2]⟩, ⟨.and, [5, 1]⟩, ⟨.or, [3, 6]⟩,
    ⟨.or, [4, 0]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [4, 2]⟩,
    ⟨.or, [9, 10]⟩], 11⟩

def disabled : Circuit :=
  ⟨circuit.gates.set 5 ⟨.or, []⟩, circuit.output⟩

def edgeFun (z : Fin 5 → Bool) : Bool :=
  (z 0 && z 1) || (z 0 && z 3) || (z 3 && z 4) || (z 4 && z 2)

def changedFun (z : Fin 5 → Bool) : Bool :=
  (z 0 && z 1) || (z 0 && z 3) || (z 3 && z 4) || (z 1 && z 2 && z 4)

def graph : SimpleGraph (Fin 5) :=
  SimpleGraph.fromRel fun u v =>
    (u = 0 ∧ v = 1) ∨ (u = 0 ∧ v = 3) ∨ (u = 3 ∧ v = 4) ∨ (u = 4 ∧ v = 2)

abbrev graphDec : DecidableRel graph.Adj := by
  unfold graph
  infer_instance

lemma graph_noFourCycle : @PEqualNP.TopForm.NoFourCycle 5 graph graphDec := by
  decide

lemma graph_bipartite : ∀ u v : Fin 5, graph.Adj u v →
    decide (u = 0 ∨ u = 4) ≠ decide (v = 0 ∨ v = 4) := by
  let := graphDec
  decide

lemma circuit_ao2 : PEqualNP.TopForm.IsAO2 5 circuit := by
  decide

lemma circuit_size : circuit.size = 7 := rfl

lemma circuit_eval : ∀ z : Fin 5 → Bool,
    PEqualNP.MetaComplexity.circuitFun 5 circuit z = edgeFun z := by
  decide

lemma disabled_eval : ∀ z : Fin 5 → Bool,
    PEqualNP.MetaComplexity.circuitFun 5 disabled z = changedFun z := by
  decide

lemma graph_eval : ∀ z : Fin 5 → Bool,
    @PEqualNP.MetaComplexity.NestedCover.graphFun 5 graph graphDec ∅ z = edgeFun z := by
  decide

lemma circuit_topForm : @PEqualNP.TopForm.TopForm 5 graph graphDec circuit := by
  decide

lemma circuit_prime_iff : ∀ S : Finset (Fin 5),
    PEqualNP.ReadK.IsPrimeImplicant 5 circuit S ↔
      S = {0, 1} ∨ S = {0, 3} ∨ S = {3, 4} ∨ S = {2, 4} := by
  decide

lemma disabled_prime_iff : ∀ S : Finset (Fin 5),
    PEqualNP.ReadK.IsPrimeImplicant 5 disabled S ↔
      S = {0, 1} ∨ S = {0, 3} ∨ S = {3, 4} ∨ S = {1, 2, 4} := by
  decide

lemma disabled_new_triple :
    PEqualNP.ReadK.IsPrimeImplicant 5 disabled {1, 2, 4} := by
  decide

lemma circuit_triple_not_prime :
    ¬ PEqualNP.ReadK.IsPrimeImplicant 5 circuit {1, 2, 4} := by
  decide

def pruned : Circuit := ⟨circuit.gates.take 5, 9⟩

lemma pruned_ao2 : PEqualNP.TopForm.IsAO2 5 pruned := by
  decide

lemma pruned_size : pruned.size = 5 := rfl

lemma pruned_eval : ∀ z : Fin 5 → Bool,
    PEqualNP.MetaComplexity.circuitFun 5 pruned z = changedFun z := by
  decide

lemma pruned_triple_prime :
    PEqualNP.ReadK.IsPrimeImplicant 5 pruned {1, 2, 4} := by
  decide

end PathDeletion

lemma p4Mixed_not_topForm :
    ¬ @PEqualNP.TopForm.TopForm 4 p4Graph p4GraphDec Additional.p4Mixed := by
  decide

end PEqualNP.Outside.L_meta_2583
