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


namespace PEqualNP.Outside.L_meta_1477.GraphRootCharge

lemma card_le_edges_add_groups {V : Type*} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (s m : ℕ)
    (r : Fin s → V) (grp : Fin s → Fin m)
    (hreach : ∀ v : V, ∃ i : Fin s, K.Reachable v (r i))
    (hgroup : ∀ i j : Fin s, grp i = grp j → K.Reachable (r i) (r j)) :
    Fintype.card V ≤ K.edgeFinset.card + m := by
  classical
  by_cases hV : Nonempty V
  · let representative (a : Fin m) : V :=
      if h : ∃ i : Fin s, grp i = a then r h.choose else Classical.choice hV
    apply card_le_edges_add_roots K m representative
    intro v
    obtain ⟨i, hi⟩ := hreach v
    refine ⟨grp i, ?_⟩
    have hex : ∃ j : Fin s, grp j = grp i := ⟨i, rfl⟩
    dsimp only [representative]
    rw [dif_pos hex]
    exact hi.trans (hgroup i hex.choose hex.choose_spec.symm)
  · have hcard : Fintype.card V = 0 :=
      Fintype.card_eq_zero_iff.mpr (not_nonempty_iff.mp hV)
    omega

lemma grouped_label_charge {V : Type*} [Fintype V]
    (K : SimpleGraph V) [DecidableRel K.Adj] (s m : ℕ)
    (r : Fin s → V) (grp : Fin s → Fin m)
    (hreach : ∀ v : V, ∃ i : Fin s, K.Reachable v (r i))
    (hgroup : ∀ i j : Fin s, grp i = grp j → K.Reachable (r i) (r j))
    (labels gates : ℕ) (hvertices : Fintype.card V = labels + gates)
    (hedges : K.edgeFinset.card ≤ 2 * gates) : labels ≤ gates + m := by
  have h := card_le_edges_add_groups K s m r grp hreach hgroup
  omega

end PEqualNP.Outside.L_meta_1477.GraphRootCharge


namespace PEqualNP.Outside.L_meta_1477.GraphRootCharge

lemma boundary_grouped_label_charge {L D : Type*} [Fintype L] [Fintype D]
    (K : SimpleGraph (Option (L ⊕ D))) [DecidableRel K.Adj] (s m : ℕ)
    (r : Fin s → Option (L ⊕ D)) (grp : Fin s → Fin m)
    (hreach : ∀ v : L ⊕ D, ∃ i : Fin s, K.Reachable (some v) (r i))
    (hgroup : ∀ i j : Fin s, grp i = grp j → K.Reachable (r i) (r j))
    (hedges : K.edgeFinset.card ≤ 2 * Fintype.card D) :
    Fintype.card L ≤ Fintype.card D + m := by
  classical
  let roots : Fin (s + 1) → Option (L ⊕ D) := Fin.cases none r
  let groups : Fin (s + 1) → Fin (m + 1) := Fin.cases 0 (fun i => (grp i).succ)
  have hreach' : ∀ v : Option (L ⊕ D), ∃ i : Fin (s + 1), K.Reachable v (roots i) := by
    intro v
    cases v with
    | none => exact ⟨0, by simp only [roots, Fin.cases_zero]; exact ⟨.nil⟩⟩
    | some v =>
      obtain ⟨i, hi⟩ := hreach v
      exact ⟨i.succ, by simpa only [roots, Fin.cases_succ] using hi⟩
  have hgroup' : ∀ i j : Fin (s + 1), groups i = groups j →
      K.Reachable (roots i) (roots j) := by
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro _
        exact ⟨.nil⟩
      · intro h
        simp only [groups, Fin.cases_zero, Fin.cases_succ] at h
        exact False.elim (Fin.succ_ne_zero _ h.symm)
    · refine Fin.cases ?_ (fun j => ?_) j
      · intro h
        simp only [groups, Fin.cases_zero, Fin.cases_succ, Fin.succ_ne_zero] at h
      · intro h
        have hij : grp i = grp j := by
          simpa only [groups, Fin.cases_succ, Fin.succ_inj] using h
        simpa only [roots, Fin.cases_succ] using hgroup i j hij
  have h := card_le_edges_add_groups K (s + 1) (m + 1) roots groups hreach' hgroup'
  simp only [Fintype.card_option, Fintype.card_sum] at h
  omega

end PEqualNP.Outside.L_meta_1477.GraphRootCharge
