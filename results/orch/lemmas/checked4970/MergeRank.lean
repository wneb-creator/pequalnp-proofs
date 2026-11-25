import Mathlib

namespace PEqualNP.Outside.L_meta_4970.SupportRank

open SimpleGraph

def graphOf {α : Type*} (F : Finset (Sym2 α)) : SimpleGraph α :=
  SimpleGraph.fromEdgeSet (F : Set (Sym2 α))

lemma graphOf_mono {α : Type*} {F T : Finset (Sym2 α)} (h : F ⊆ T) :
    graphOf F ≤ graphOf T := by
  intro a b hab
  exact ⟨h hab.1, hab.2⟩

lemma graphOf_insert_reachable {α : Type*} [DecidableEq α]
    (F : Finset (Sym2 α)) (a b : α) :
    (graphOf (insert s(a, b) F)).Reachable a b := by
  by_cases hab : a = b
  · subst b
    exact SimpleGraph.Reachable.refl a
  · apply SimpleGraph.Adj.reachable
    exact ⟨Finset.mem_insert_self _ _, hab⟩

lemma union_connected_insert {α : Type*} [DecidableEq α]
    (F : Finset (Sym2 α)) (A B : Finset α) (a b : α)
    (ha : a ∈ A) (hb : b ∈ B)
    (hA : ∀ x ∈ A, ∀ y ∈ A, (graphOf F).Reachable x y)
    (hB : ∀ x ∈ B, ∀ y ∈ B, (graphOf F).Reachable x y) :
    ∀ x ∈ A ∪ B, ∀ y ∈ A ∪ B,
      (graphOf (insert s(a, b) F)).Reachable x y := by
  have hmono : graphOf F ≤ graphOf (insert s(a, b) F) :=
    graphOf_mono (Finset.subset_insert _ _)
  have hab := graphOf_insert_reachable F a b
  have hreach : ∀ x ∈ A ∪ B, (graphOf (insert s(a, b) F)).Reachable x a := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxA | hxB
    · exact (hA x hxA a ha).mono hmono
    · exact ((hB x hxB b hb).mono hmono).trans hab.symm
  intro x hx y hy
  exact (hreach x hx).trans (hreach y hy).symm

lemma merge_graph {α : Type*} [DecidableEq α]
    (f : ℕ → Finset α) (M : Finset ℕ)
    (hBase : ∀ w, w ∉ M → (f w).card ≤ 1 ∨ ∃ a < w, f w ⊆ f a)
    (hStep : ∀ m ∈ M, f m = ∅ ∨ (∃ a < m, f m ⊆ f a) ∨
      (∃ a < m, ∃ b < m, f m ⊆ f a ∪ f b)) :
    ∀ B : ℕ, ∃ F : Finset (Sym2 α), F.card ≤ (M.filter (· < B)).card ∧
      ∀ w < B, ∀ x ∈ f w, ∀ y ∈ f w, (graphOf F).Reachable x y := by
  intro B
  induction B with
  | zero =>
    exact ⟨∅, by simp, by omega⟩
  | succ B ih =>
    obtain ⟨F, hF, hconn⟩ := ih
    have hMsub : (M.filter (· < B)).card ≤ (M.filter (· < B + 1)).card := by
      apply Finset.card_le_card
      intro m hm
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hm).1,
        by have := (Finset.mem_filter.mp hm).2; omega⟩
    have hfinish : ∀ F' : Finset (Sym2 α), F ⊆ F' →
        F'.card ≤ (M.filter (· < B + 1)).card →
        (∀ x ∈ f B, ∀ y ∈ f B, (graphOf F').Reachable x y) →
        ∃ F' : Finset (Sym2 α), F'.card ≤ (M.filter (· < B + 1)).card ∧
          ∀ w < B + 1, ∀ x ∈ f w, ∀ y ∈ f w, (graphOf F').Reachable x y := by
      intro F' hsub hcard hnew
      refine ⟨F', hcard, ?_⟩
      intro w hw x hx y hy
      by_cases heq : w = B
      · subst w
        exact hnew x hx y hy
      · exact (hconn w (by omega) x hx y hy).mono (graphOf_mono hsub)
    have hpass : (∃ a < B, f B ⊆ f a) →
        ∃ F' : Finset (Sym2 α), F'.card ≤ (M.filter (· < B + 1)).card ∧
          ∀ w < B + 1, ∀ x ∈ f w, ∀ y ∈ f w, (graphOf F').Reachable x y := by
      rintro ⟨a, ha, hsub⟩
      apply hfinish F (Finset.Subset.refl _) (hF.trans hMsub)
      intro x hx y hy
      exact hconn a ha x (hsub hx) y (hsub hy)
    by_cases hBM : B ∈ M
    · have hcharge : (M.filter (· < B)).card + 1 ≤ (M.filter (· < B + 1)).card := by
        have hnot : B ∉ M.filter (· < B) := by simp
        rw [← Finset.card_insert_of_notMem hnot]
        apply Finset.card_le_card
        intro m hm
        rcases Finset.mem_insert.mp hm with rfl | hm
        · exact Finset.mem_filter.mpr ⟨hBM, by omega⟩
        · exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hm).1,
            by have := (Finset.mem_filter.mp hm).2; omega⟩
      rcases hStep B hBM with he | hp | ⟨a, ha, b, hb, hsub⟩
      · apply hfinish F (Finset.Subset.refl _) (hF.trans hMsub)
        simp [he]
      · exact hpass hp
      · by_cases hfa : (f a).Nonempty
        · by_cases hfb : (f b).Nonempty
          · obtain ⟨u, hu⟩ := hfa
            obtain ⟨v, hv⟩ := hfb
            apply hfinish (insert s(u, v) F) (Finset.subset_insert _ _)
            · have hi := Finset.card_insert_le s(u, v) F
              omega
            · intro x hx y hy
              exact union_connected_insert F (f a) (f b) u v hu hv (hconn a ha) (hconn b hb)
                x (hsub hx) y (hsub hy)
          · apply hpass
            refine ⟨a, ha, ?_⟩
            have he : f b = ∅ := Finset.not_nonempty_iff_eq_empty.mp hfb
            simpa [he] using hsub
        · apply hpass
          refine ⟨b, hb, ?_⟩
          have he : f a = ∅ := Finset.not_nonempty_iff_eq_empty.mp hfa
          simpa [he] using hsub
    · rcases hBase B hBM with hsmall | hp
      · apply hfinish F (Finset.Subset.refl _) (hF.trans hMsub)
        intro x hx y hy
        have heq : x = y := Finset.card_le_one.mp hsmall x hx y hy
        subst y
        exact SimpleGraph.Reachable.refl x
      · exact hpass hp


lemma vertices_le_edges_components {α : Type*} [Finite α] (G : SimpleGraph α) :
    Nat.card α ≤ G.edgeSet.ncard + Nat.card G.ConnectedComponent := by
  classical
  letI : Fintype G.ConnectedComponent := Fintype.ofFinite _
  have hc : ∀ c : G.ConnectedComponent,
      c.supp.ncard ≤ c.toSimpleGraph.edgeSet.ncard + 1 := by
    intro c
    simpa only [c.ncard_supp, Nat.card_coe_set_eq] using
      c.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one
  calc
    _ = ∑ c : G.ConnectedComponent, c.supp.ncard := G.sum_connectedComponent_ncard_supp.symm
    _ ≤ ∑ c : G.ConnectedComponent, (c.toSimpleGraph.edgeSet.ncard + 1) := by
      exact Finset.sum_le_sum (fun c _ => hc c)
    _ = G.edgeSet.ncard + Nat.card G.ConnectedComponent := by
      rw [Finset.sum_add_distrib, G.sum_connectedComponent_ncard_edgeSet]
      simp [Nat.card_eq_fintype_card]

lemma component_card_le_of_adj_reachable {α : Type*} [Finite α]
    (G H : SimpleGraph α) (h : ∀ ⦃x y⦄, H.Adj x y → G.Reachable x y) :
    Nat.card G.ConnectedComponent ≤ Nat.card H.ConnectedComponent := by
  have hreach : ∀ ⦃x y⦄, H.Reachable x y → G.Reachable x y := by
    intro x y hxy
    obtain ⟨p⟩ := hxy
    induction p with
    | @nil u => exact SimpleGraph.Reachable.refl u
    | @cons u v w huv p ih => exact (h huv).trans ih
  let map : H.ConnectedComponent → G.ConnectedComponent :=
    Quot.map id (fun x y hxy => hreach hxy)
  have hsurj : Function.Surjective map := by
    intro c
    refine Quot.inductionOn c ?_
    intro v
    exact ⟨H.connectedComponentMk v, rfl⟩
  exact Nat.card_le_card_of_surjective map hsurj

lemma graphOf_edge_count {α : Type*} (F : Finset (Sym2 α)) :
    (graphOf F).edgeSet.ncard ≤ F.card := by
  have hsub : (graphOf F).edgeSet ⊆ (F : Set (Sym2 α)) := by
    rw [graphOf, SimpleGraph.edgeSet_fromEdgeSet]
    exact Set.sdiff_subset
  simpa using Set.ncard_le_ncard hsub F.finite_toSet

def overlapGraph {α : Type*} (f : ℕ → Finset α) (R : Finset ℕ) : SimpleGraph α :=
  SimpleGraph.fromRel fun x y => ∃ w ∈ R, x ∈ f w ∧ y ∈ f w

lemma overlap_adj {α : Type*} (f : ℕ → Finset α) (R : Finset ℕ) {x y : α}
    (h : (overlapGraph f R).Adj x y) : ∃ w ∈ R, x ∈ f w ∧ y ∈ f w := by
  rcases h.2 with ⟨w, hw, hx, hy⟩ | ⟨w, hw, hy, hx⟩
  · exact ⟨w, hw, hx, hy⟩
  · exact ⟨w, hw, hx, hy⟩

lemma merge_rank_bound {α : Type*} [Finite α] [DecidableEq α]
    (f : ℕ → Finset α) (M : Finset ℕ)
    (hBase : ∀ w, w ∉ M → (f w).card ≤ 1 ∨ ∃ a < w, f w ⊆ f a)
    (hStep : ∀ m ∈ M, f m = ∅ ∨ (∃ a < m, f m ⊆ f a) ∨
      (∃ a < m, ∃ b < m, f m ⊆ f a ∪ f b))
    (B : ℕ) (R : Finset ℕ) (hR : ∀ w ∈ R, w < B) :
    Nat.card α ≤ (M.filter (· < B)).card +
      Nat.card (overlapGraph f R).ConnectedComponent := by
  obtain ⟨F, hF, hconn⟩ := merge_graph f M hBase hStep B
  have hle := component_card_le_of_adj_reachable (graphOf F) (overlapGraph f R) (by
    intro x y hxy
    obtain ⟨w, hw, hx, hy⟩ := overlap_adj f R hxy
    exact hconn w (hR w hw) x hx y hy)
  have hvertices := vertices_le_edges_components (graphOf F)
  have hedges := graphOf_edge_count F
  omega

end PEqualNP.Outside.L_meta_4970.SupportRank
