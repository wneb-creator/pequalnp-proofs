import Mathlib

namespace PEqualNP.Outside.L_meta_1477.GraphRootCharge

lemma card_le_edges_add_roots {V : Type*} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (m : ℕ) (r : Fin m → V)
    (hreach : ∀ v : V, ∃ i : Fin m, K.Reachable v (r i)) :
    Fintype.card V ≤ K.edgeFinset.card + m := by
  classical
  let A : Finset (Sym2 (Option V)) := K.edgeFinset.image (Sym2.map Option.some)
  let B : Finset (Sym2 (Option V)) := Finset.univ.image (fun i : Fin m => s(none, some (r i)))
  let S := A ∪ B
  let H : SimpleGraph (Option V) := SimpleGraph.fromEdgeSet (S : Set (Sym2 (Option V)))
  have hmap (u v : V) (huv : K.Adj u v) : H.Adj (some u) (some v) := by
    apply (SimpleGraph.fromEdgeSet_adj (S : Set (Sym2 (Option V)))).mpr
    refine ⟨?_, fun he => K.ne_of_adj huv (Option.some.inj he)⟩
    apply Finset.mem_union_left
    apply Finset.mem_image.mpr
    exact ⟨s(u, v), by simpa using huv, rfl⟩
  let hom : K →g H := ⟨Option.some, fun hu => hmap _ _ hu⟩
  have hstar (i : Fin m) : H.Adj none (some (r i)) := by
    apply (SimpleGraph.fromEdgeSet_adj (S : Set (Sym2 (Option V)))).mpr
    refine ⟨?_, by simp⟩
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hconnected : H.Connected := by
    apply (SimpleGraph.connected_iff_exists_forall_reachable H).mpr
    refine ⟨none, ?_⟩
    intro w
    cases w with
    | none => exact ⟨.nil⟩
    | some v =>
      obtain ⟨i, hi⟩ := hreach v
      exact (hstar i).reachable.trans (hi.map hom).symm
  have hsub : H.edgeFinset ⊆ S := by
    intro e he
    have hh : e ∈ H.edgeSet := SimpleGraph.mem_edgeFinset.mp he
    dsimp only [H] at hh
    rw [SimpleGraph.edgeSet_fromEdgeSet] at hh
    exact hh.1
  have hA : A.card ≤ K.edgeFinset.card := Finset.card_image_le
  have hB : B.card ≤ m := by
    simpa only [Finset.card_univ, Fintype.card_fin] using
      (Finset.card_image_le (s := Finset.univ) (f := fun i : Fin m => s(none, some (r i))))
  have hS : S.card ≤ A.card + B.card := Finset.card_union_le _ _
  have hH : H.edgeFinset.card ≤ S.card := Finset.card_le_card hsub
  have hEuler := hconnected.card_vert_le_card_edgeSet_add_one
  have hEuler' : Fintype.card V + 1 ≤ H.edgeFinset.card + 1 := by
    simpa only [Nat.card_eq_fintype_card, Fintype.card_option, SimpleGraph.edgeFinset_card] using hEuler
  omega

lemma label_charge {V : Type*} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (m : ℕ) (r : Fin m → V)
    (hreach : ∀ v : V, ∃ i : Fin m, K.Reachable v (r i))
    (labels gates : ℕ) (hvertices : Fintype.card V = labels + gates)
    (hedges : K.edgeFinset.card ≤ 2 * gates) : labels ≤ gates + m := by
  have h := card_le_edges_add_roots K m r hreach
  omega

end PEqualNP.Outside.L_meta_1477.GraphRootCharge

namespace PEqualNP.Outside.L_meta_1477.GraphComponentCharge

lemma card_le_edges_add_components {V : Type*} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj] :
    Fintype.card V ≤ K.edgeFinset.card + Nat.card K.ConnectedComponent := by
  classical
  letI : Fintype K.ConnectedComponent := Fintype.ofFinite _
  have hex : ∀ c : K.ConnectedComponent, ∃ v : V, K.connectedComponentMk v = c := by
    intro c
    induction c using SimpleGraph.ConnectedComponent.ind with
    | h v => exact ⟨v, rfl⟩
  let e := Fintype.equivFin K.ConnectedComponent
  let r : Fin (Fintype.card K.ConnectedComponent) → V :=
    fun i => Classical.choose (hex (e.symm i))
  have hr : ∀ v : V, ∃ i, K.Reachable v (r i) := by
    intro v
    refine ⟨e (K.connectedComponentMk v), ?_⟩
    apply SimpleGraph.ConnectedComponent.exact
    have h := Classical.choose_spec (hex (e.symm (e (K.connectedComponentMk v))))
    simpa only [r, Equiv.symm_apply_apply] using h.symm
  simpa only [Nat.card_eq_fintype_card] using
    GraphRootCharge.card_le_edges_add_roots K (Fintype.card K.ConnectedComponent) r hr

end PEqualNP.Outside.L_meta_1477.GraphComponentCharge

namespace PEqualNP.Outside.L_meta_1477.GraphPartitionCharge

open Finset

def crossEdges {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) : Finset (Sym2 V) :=
  G.edgeFinset \ (P.sym2 ∪ (Finset.univ \ P).sym2)

lemma induced_edge_card {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) :
    (G.induce (P : Set V)).edgeFinset.card = (G.edgeFinset ∩ P.sym2).card := by
  classical
  have h := congrArg Finset.card (SimpleGraph.map_edgeFinset_induce (G := G) (s := (P : Set V)))
  simp only [Finset.card_map, SimpleGraph.edgeFinset_card, ← Nat.card_eq_fintype_card] at h ⊢
  refine h.trans ?_
  congr 1
  ext e
  induction e using Sym2.inductionOn with
  | hf a b => simp

lemma edge_partition {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) :
    (G.induce (P : Set V)).edgeFinset.card +
      (G.induce ((Finset.univ \ P : Finset V) : Set V)).edgeFinset.card +
      (crossEdges G P).card = G.edgeFinset.card := by
  classical
  let Q := (Finset.univ : Finset V) \ P
  have hd : Disjoint (G.edgeFinset ∩ P.sym2) (G.edgeFinset ∩ Q.sym2) := by
    apply Finset.disjoint_left.mpr
    intro e heP heQ
    induction e using Sym2.inductionOn with
    | hf a b =>
      have haP := (Finset.mk_mem_sym2_iff.mp (Finset.mem_inter.mp heP).2).1
      have haQ := (Finset.mk_mem_sym2_iff.mp (Finset.mem_inter.mp heQ).2).1
      exact (Finset.mem_sdiff.mp haQ).2 haP
  have heq : (G.edgeFinset ∩ P.sym2) ∪ (G.edgeFinset ∩ Q.sym2) =
      G.edgeFinset ∩ (P.sym2 ∪ Q.sym2) := by
    ext e
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto
  have hc := Finset.card_sdiff_add_card_inter G.edgeFinset (P.sym2 ∪ Q.sym2)
  rw [← heq, Finset.card_union_of_disjoint hd] at hc
  rw [induced_edge_card, induced_edge_card]
  change (G.edgeFinset ∩ P.sym2).card + (G.edgeFinset ∩ Q.sym2).card +
    (G.edgeFinset \ (P.sym2 ∪ Q.sym2)).card = G.edgeFinset.card
  omega

lemma vertex_partition {V : Type*} [Fintype V] [DecidableEq V] (P : Finset V) :
    P.card + (Finset.univ \ P).card = Fintype.card V := by
  have h := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ P)
  simpa only [Finset.card_univ, Nat.add_comm] using h

lemma partition_budget {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (P : Finset V) (m : ℕ)
    (hprivate : P.card ≤ (G.induce (P : Set V)).edgeFinset.card + m)
    (hcross : 2 * Nat.card
      (G.induce ((Finset.univ \ P : Finset V) : Set V)).ConnectedComponent ≤ (crossEdges G P).card) :
    Fintype.card V + Nat.card
      (G.induce ((Finset.univ \ P : Finset V) : Set V)).ConnectedComponent ≤ G.edgeFinset.card + m := by
  classical
  have hs := GraphComponentCharge.card_le_edges_add_components
    (G.induce ((Finset.univ \ P : Finset V) : Set V))
  have hs' : (Finset.univ \ P).card ≤
      (G.induce ((Finset.univ \ P : Finset V) : Set V)).edgeFinset.card +
        Nat.card (G.induce ((Finset.univ \ P : Finset V) : Set V)).ConnectedComponent := by
    have hq : Fintype.card ↥((Finset.univ \ P : Finset V) : Set V) = (Finset.univ \ P).card :=
      Fintype.card_of_finset' (Finset.univ \ P) (fun _ => Iff.rfl)
    rw [hq] at hs
    exact hs
  have he := edge_partition G P
  have hv := vertex_partition P
  omega

end PEqualNP.Outside.L_meta_1477.GraphPartitionCharge
