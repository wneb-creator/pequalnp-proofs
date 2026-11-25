import Mathlib

namespace PEqualNP.Outside.L_meta_4970.IncidenceBudget

lemma vertices_le_edges_add_components {V : Type*} [Finite V]
    (G : SimpleGraph V) :
    Nat.card V ≤ G.edgeSet.ncard + Nat.card G.ConnectedComponent := by
  classical
  let := Fintype.ofFinite G.ConnectedComponent
  rw [← G.sum_connectedComponent_ncard_supp,
    ← G.sum_connectedComponent_ncard_edgeSet,
    ← Fintype.card_eq_nat_card, Fintype.card_eq_sum_ones,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro c _
  exact c.connected_toSimpleGraph.card_vert_le_card_edgeSet_add_one

def incidenceGraph {ι α : Type*} (R : ι → α → Prop) : SimpleGraph (ι ⊕ α) where
  Adj u v := match u, v with
    | .inl i, .inr a => R i a
    | .inr a, .inl i => R i a
    | _, _ => False
  symm := ⟨by
    intro u v
    cases u <;> cases v <;> simp_all⟩
  loopless := ⟨by
    intro u
    cases u <;> simp⟩

lemma incidence_edges {ι α : Type*} [Fintype ι] [Fintype α]
    (R : ι → α → Prop) [∀ i a, Decidable (R i a)] :
    (incidenceGraph R).edgeSet.ncard =
      ∑ i : ι, ((Finset.univ : Finset α).filter (R i)).card := by
  classical
  let S := (Finset.univ : Finset (ι × α)).filter fun z => R z.1 z.2
  let f : ι × α → Sym2 (ι ⊕ α) := fun z => s(Sum.inl z.1, Sum.inr z.2)
  have hf : Function.Injective f := by
    intro u v huv
    simp only [f, Sym2.eq_iff, Sum.inl.injEq, Sum.inr.injEq,
      Sum.inl_ne_inr, false_and, or_false] at huv
    exact Prod.ext huv.1 huv.2
  have he : (incidenceGraph R).edgeFinset = S.image f := by
    ext e
    induction e using Sym2.inductionOn with
    | hf u v =>
      rw [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
      cases u <;> cases v <;>
        simp [incidenceGraph, S, f]
  have hn : (incidenceGraph R).edgeSet.ncard =
      (incidenceGraph R).edgeFinset.card := by
    simp [SimpleGraph.edgeFinset, Set.ncard_eq_toFinset_card']
  rw [hn, he, Finset.card_image_of_injective _ hf]
  simp only [S, Finset.card_eq_sum_ones, Finset.sum_filter, Fintype.sum_prod_type]

lemma incidence_budget {ι α : Type*} [Fintype ι] [Fintype α]
    (R : ι → α → Prop) [∀ i a, Decidable (R i a)] (budget : ℕ)
    (hbudget : (∑ i : ι, ((Finset.univ : Finset α).filter (R i)).card) ≤
      Fintype.card ι + budget) :
    Fintype.card α ≤ budget + Nat.card (incidenceGraph R).ConnectedComponent := by
  have h := vertices_le_edges_add_components (incidenceGraph R)
  rw [Nat.card_eq_fintype_card, Fintype.card_sum, incidence_edges] at h
  omega

lemma connected_incidence_budget {ι α : Type*} [Fintype ι] [Fintype α]
    (R : ι → α → Prop) [∀ i a, Decidable (R i a)] (budget : ℕ)
    (hbudget : (∑ i : ι, ((Finset.univ : Finset α).filter (R i)).card) ≤
      Fintype.card ι + budget)
    (hconn : (incidenceGraph R).Connected) :
    Fintype.card α ≤ budget + 1 := by
  have h := hconn.card_vert_le_card_edgeSet_add_one
  change Nat.card (ι ⊕ α) ≤ (incidenceGraph R).edgeSet.ncard + 1 at h
  rw [Nat.card_eq_fintype_card, Fintype.card_sum, incidence_edges] at h
  omega

end PEqualNP.Outside.L_meta_4970.IncidenceBudget
