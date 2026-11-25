import GraphRepair
import ForcedEval

namespace PEqualNP.Outside.L_meta_2448_aux.ConcreteGraphRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_2448_aux.ReaderDeletion
open PEqualNP.Outside.L_meta_2448_aux.RepairAssembly
open PEqualNP.Outside.L_meta_2448_aux.LinearCleanup
open PEqualNP.Outside.L_meta_2448_aux.TwoCenterRepair
open PEqualNP.Outside.L_meta_2448_aux.EdgePruning

open PEqualNP.Outside.L_meta_2448_aux.GraphRepair
open PEqualNP.Outside.L_meta_2448_aux.ForcedEval

theorem pure_product_repair_circuit (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (pre post : List Gate) (g : Gate) (a b : ℕ)
    (A B : Set (Fin n)) (c d : Fin n)
    (hC : C.gates = pre ++ g :: post) (hmono : Monotone2 C)
    (ha : a < n + pre.length) (hb : b < n + pre.length)
    (htri : ∀ u v w, G.Adj u v → G.Adj v w → ¬G.Adj w u)
    (hfour : ∀ u v w z, G.Adj u v → G.Adj v w → G.Adj w z →
      G.Adj z u → u = w ∨ v = z)
    (hc : c ∈ Centers G A B) (hd : d ∈ Centers G B A)
    (hA : ∀ x : Fin n → Bool, (wiresFrom pre (List.ofFn x)).getD a false = true ↔
      Hit A (fun v => x v = true))
    (hB : ∀ x : Fin n → Bool, (wiresFrom pre (List.ofFn x)).getD b false = true ↔
      Hit B (fun v => x v = true))
    (hexact : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x)
    (hgop : g.op = GateOp.and) (hginputs : g.inputs = [a, b]) :
    ∃ E : Circuit, Monotone2 E ∧
      E.size + readerCount (n + pre.length) post ≤ C.size + 3 ∧
      ∀ x : Fin n → Bool, E.eval (List.ofFn x) = graphFun G ∅ x := by
  have hpre : ∀ h ∈ pre, MonoGate h := by
    intro h hh
    exact hmono h (hC ▸ List.mem_append_left _ hh)
  have hpost : ∀ h ∈ post, MonoGate h := by
    intro h hh
    exact hmono h (hC ▸ List.mem_append_right _ (List.mem_cons_of_mem _ hh))
  apply graph_repair_circuit n G C pre post g a b A B c d hC hmono ha hb
    htri hfour hc hd hA hB hexact
  · exact forced_mono n pre post C.output hpre hpost
  · exact forced_le n C pre post g hC hpost
  · intro x hprod
    apply forced_eq_of_gate_false n C pre post g hC x
    rw [hgop, hginputs]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true]
    cases hv : ((wiresFrom pre (List.ofFn x)).getD a false &&
      (wiresFrom pre (List.ofFn x)).getD b false) with
    | false => rfl
    | true =>
      have hh : (wiresFrom pre (List.ofFn x)).getD a false = true ∧
          (wiresFrom pre (List.ofFn x)).getD b false = true := by simpa using hv
      exact (hprod ⟨(hA x).mp hh.1, (hB x).mp hh.2⟩).elim

end PEqualNP.Outside.L_meta_2448_aux.ConcreteGraphRepair
