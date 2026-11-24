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
