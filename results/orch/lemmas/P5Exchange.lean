import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.P5Exchange

open PEqualNP.CircuitLowerBounds PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma common_center {V : Type*} (G : SimpleGraph V)
    (h4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    {a b c z : V} (hac : a ≠ c) (hab : G.Adj a b) (hbc : G.Adj b c)
    (hza : G.Adj z a) (hzc : G.Adj z c) : z = b :=
  ((h4 a b c z hab hbc hzc.symm hza).resolve_left hac).symm

lemma prefix_sharing_constraints {V : Type*} (G : SimpleGraph V)
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (h4 : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    {a b c d e : V} (hac : a ≠ c) (hce : c ≠ e) (hbd : b ≠ d)
    (hab : G.Adj a b) (hbc : G.Adj b c) (hcd : G.Adj c d) (hde : G.Adj d e) :
    (∀ z, G.Adj z b → G.Adj z d → z = c) ∧
      (∀ z, ¬ (G.Adj z b ∧ G.Adj z c)) ∧
      (∀ z, ¬ (G.Adj z b ∧ G.Adj z c ∧ G.Adj z e)) ∧
      (∀ z, ¬ (G.Adj z a ∧ G.Adj z c ∧ G.Adj z e)) ∧
      (∀ z, ¬ (G.Adj z a ∧ G.Adj z c ∧ G.Adj z d)) := by
  refine ⟨fun z hzb hzd => common_center G h4 hbd hbc hcd hzb hzd, ?_, ?_, ?_, ?_⟩
  · rintro z ⟨hzb, hzc⟩
    exact htri z b c hzb hbc hzc.symm
  · rintro z ⟨hzb, hzc, _⟩
    exact htri z b c hzb hbc hzc.symm
  · rintro z ⟨hza, hzc, hze⟩
    have hzb := common_center G h4 hac hab hbc hza hzc
    have hzd := common_center G h4 hce hcd hde hzc hze
    exact hbd (hzb.symm.trans hzd)
  · rintro z ⟨_, hzc, hzd⟩
    exact htri z c d hzc hcd hzd.symm

abbrev pathFive : SimpleGraph (Fin 5) := edgeGraph 5 [(0, 1), (1, 2), (2, 3), (3, 4)]

def oldCore : Circuit :=
  ⟨[⟨.or, [1, 3]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [6, 4]⟩,
    ⟨.or, [0, 4]⟩, ⟨.or, [8, 2]⟩, ⟨.or, [0, 3]⟩,
    ⟨.or, [10, 2]⟩, ⟨.and, [5, 7]⟩, ⟨.and, [9, 11]⟩,
    ⟨.and, [12, 13]⟩], 14⟩

def newCore : Circuit :=
  ⟨[⟨.or, [1, 3]⟩, ⟨.or, [0, 4]⟩, ⟨.or, [0, 3]⟩,
    ⟨.or, [0, 2]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [2, 4]⟩,
    ⟨.and, [3, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩

lemma oldCore_correct : circuitFun 5 oldCore = graphFun pathFive ∅ := by
  funext x
  revert x
  decide

lemma newCore_correct : circuitFun 5 newCore = graphFun pathFive ∅ := by
  funext x
  revert x
  decide

lemma oldCore_two_junk : PEqualNP.TopForm.junk pathFive oldCore = {7, 8} := by decide

lemma oldCore_top : PEqualNP.TopForm.TopForm pathFive oldCore := by decide

lemma newCore_preserves_shared_ports : ∀ x : Fin 5 → Bool,
    (oldCore.wires (List.ofFn x)).getD 5 false = (newCore.wires (List.ofFn x)).getD 5 false ∧
    (oldCore.wires (List.ofFn x)).getD 8 false = (newCore.wires (List.ofFn x)).getD 6 false ∧
    (oldCore.wires (List.ofFn x)).getD 10 false = (newCore.wires (List.ofFn x)).getD 7 false ∧
    oldCore.eval (List.ofFn x) = newCore.eval (List.ofFn x) := by
  decide

lemma newCore_legal : PEqualNP.TopForm.IsAO2 5 newCore := by decide

lemma newCore_nonempty_star_owners : ∀ j < newCore.gates.length,
    (gateAt newCore j).op = GateOp.and → ∃ c : Fin 5,
      (∃ u v : Fin 5, pathFive.Adj u v ∧ Owns 5 newCore j u v) ∧
      ∀ u v : Fin 5, pathFive.Adj u v → Owns 5 newCore j u v → u = c ∨ v = c := by
  intro j hj hop
  have hj8 : j < 8 := hj
  interval_cases j <;> norm_num [newCore, gateAt] at hop
  all_goals decide

lemma newCore_size_drop : newCore.size + 2 = oldCore.size := rfl

end PEqualNP.Outside.L_meta_1031.P5Exchange
