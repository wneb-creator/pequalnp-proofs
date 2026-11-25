import Mathlib

namespace PEqualNP.Outside.L_meta_4970.Components

def Joined {α : Type*} (H : SimpleGraph α) (A : Finset α) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, H.Reachable a b

lemma joined_small {α : Type*} (H : SimpleGraph α) (A : Finset α)
    (hA : A.card ≤ 1) : Joined H A := by
  intro a ha b hb
  have hab := Finset.card_le_one.mp hA a ha b hb
  subst b
  exact SimpleGraph.Reachable.refl _

lemma joined_subset {α : Type*} (H : SimpleGraph α) {A B : Finset α}
    (hA : A ⊆ B) (hB : Joined H B) : Joined H A := by
  intro a ha b hb
  exact hB a (hA ha) b (hA hb)

lemma joined_mono {α : Type*} {H H' : SimpleGraph α} (hH : H ≤ H')
    {A : Finset α} (hA : Joined H A) : Joined H' A := by
  intro a ha b hb
  exact (hA a ha b hb).mono hH

lemma join_two {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) (A B : Finset α) (hA : Joined H A) (hB : Joined H B) :
    ∃ H' : SimpleGraph α, H ≤ H' ∧
      H'.edgeSet.ncard ≤ H.edgeSet.ncard + 1 ∧ Joined H' (A ∪ B) := by
  classical
  by_cases ha : A.Nonempty
  · by_cases hb : B.Nonempty
    · obtain ⟨a, ha⟩ := ha
      obtain ⟨b, hb⟩ := hb
      let J : SimpleGraph α := SimpleGraph.fromEdgeSet {s(a, b)}
      have hJsub : J.edgeFinset ⊆ {s(a, b)} := by
        intro e he
        have he' : e ∈ J.edgeSet := by simpa using he
        dsimp only [J] at he'
        rw [SimpleGraph.edgeSet_fromEdgeSet] at he'
        simpa using he'.1
      have hJcard : J.edgeFinset.card ≤ 1 := by
        simpa using Finset.card_le_card hJsub
      have hab : (H ⊔ J).Reachable a b := by
        by_cases h : a = b
        · subst b
          exact SimpleGraph.Reachable.refl _
        · apply SimpleGraph.Adj.reachable
          exact Or.inr ((SimpleGraph.fromEdgeSet_adj
            (s := ({s(a, b)} : Set (Sym2 α)))).mpr ⟨by simp, h⟩)
      refine ⟨H ⊔ J, le_sup_left, ?_, ?_⟩
      · simp only [Set.ncard_eq_toFinset_card']
        change (H ⊔ J).edgeFinset.card ≤ H.edgeFinset.card + 1
        rw [SimpleGraph.edgeFinset_sup]
        exact (Finset.card_union_le _ _).trans (Nat.add_le_add_left hJcard _)
      · intro u hu v hv
        rcases Finset.mem_union.mp hu with hu | hu
        · rcases Finset.mem_union.mp hv with hv | hv
          · exact (hA u hu v hv).mono le_sup_left
          · exact ((hA u hu a ha).mono le_sup_left).trans
              (hab.trans ((hB b hb v hv).mono le_sup_left))
        · rcases Finset.mem_union.mp hv with hv | hv
          · exact ((hB u hu b hb).mono le_sup_left).trans
              (hab.symm.trans ((hA a ha v hv).mono le_sup_left))
          · exact (hB u hu v hv).mono le_sup_left
    · have hb : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hb
      refine ⟨H, le_rfl, Nat.le_add_right .., ?_⟩
      simpa [hb] using hA
  · have ha : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    refine ⟨H, le_rfl, Nat.le_add_right .., ?_⟩
    simpa [ha] using hB

lemma joined_biUnion_one {α : Type*} [DecidableEq α]
    (H : SimpleGraph α) (P : Finset ℕ) (supp : ℕ → Finset α)
    (hP : P.card ≤ 1) (hj : ∀ w ∈ P, Joined H (supp w)) :
    Joined H (P.biUnion supp) := by
  intro a ha b hb
  obtain ⟨u, hu, hau⟩ := Finset.mem_biUnion.mp ha
  obtain ⟨v, hv, hbv⟩ := Finset.mem_biUnion.mp hb
  have huv := Finset.card_le_one.mp hP u hu v hv
  subst v
  exact hj u hu a hau b hbv

lemma join_family {α : Type*} [Fintype α] [DecidableEq α]
    (H : SimpleGraph α) (P : Finset ℕ) (supp : ℕ → Finset α) (charge : Bool)
    (hP : P.card ≤ 1 + (if charge then 1 else 0))
    (hj : ∀ w ∈ P, Joined H (supp w)) :
    ∃ H' : SimpleGraph α, H ≤ H' ∧
      H'.edgeSet.ncard ≤ H.edgeSet.ncard + (if charge then 1 else 0) ∧
      Joined H' (P.biUnion supp) := by
  classical
  by_cases hP1 : P.card ≤ 1
  · exact ⟨H, le_rfl, Nat.le_add_right .., joined_biUnion_one H P supp hP1 hj⟩
  · have hcharge : charge = true := by
      cases charge
      · exact False.elim (hP1 (by simpa using hP))
      · rfl
    have hP2 : P.card = 2 := by simp [hcharge] at hP; omega
    obtain ⟨u, v, _, hPuv⟩ := Finset.card_eq_two.mp hP2
    have hu : u ∈ P := by simp [hPuv]
    have hv : v ∈ P := by simp [hPuv]
    obtain ⟨H', hle, hc, hjoin⟩ := join_two H (supp u) (supp v) (hj u hu) (hj v hv)
    refine ⟨H', hle, by simpa [hcharge] using hc, ?_⟩
    simpa [hPuv] using hjoin

lemma filter_lt_succ_card (K : Finset ℕ) (t : ℕ) :
    (K.filter (· < t + 1)).card = (K.filter (· < t)).card +
      (if t ∈ K then 1 else 0) := by
  by_cases ht : t ∈ K
  · have heq : K.filter (· < t + 1) = insert t (K.filter (· < t)) := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hw, hlt⟩
        by_cases h : w = t
        · exact Or.inl h
        · exact Or.inr ⟨hw, by omega⟩
      · rintro (rfl | ⟨hw, hlt⟩)
        · exact ⟨ht, by omega⟩
        · exact ⟨hw, by omega⟩
    rw [heq, Finset.card_insert_of_notMem (by simp)]
    simp [ht]
  · have heq : K.filter (· < t + 1) = K.filter (· < t) := by
      ext w
      simp only [Finset.mem_filter]
      constructor
      · rintro ⟨hw, hlt⟩
        have hne : w ≠ t := fun h => ht (h ▸ hw)
        exact ⟨hw, by omega⟩
      · rintro ⟨hw, hlt⟩
        exact ⟨hw, by omega⟩
    rw [heq]
    simp [ht]

lemma build_support_graph {α : Type*} [Fintype α] [DecidableEq α]
    (supp : ℕ → Finset α) (neg : ℕ → Prop) (K : Finset ℕ)
    (hstep : ∀ w, neg w → 2 ≤ (supp w).card → ∃ P : Finset ℕ,
      P.card ≤ 1 + (if w ∈ K then 1 else 0) ∧
      (∀ r ∈ P, r < w) ∧ (∀ r ∈ P, neg r) ∧
      supp w ⊆ P.biUnion supp)
    (t : ℕ) :
    ∃ H : SimpleGraph α, H.edgeSet.ncard ≤ (K.filter (· < t)).card ∧
      ∀ w < t, neg w → Joined H (supp w) := by
  classical
  induction t with
  | zero =>
    refine ⟨⊥, by simp, ?_⟩
    intro w hw
    omega
  | succ t ih =>
    obtain ⟨H, hHcard, hHjoin⟩ := ih
    have hfilter := filter_lt_succ_card K t
    by_cases ht : neg t ∧ 2 ≤ (supp t).card
    · obtain ⟨P, hPc, hPt, hPn, hPs⟩ := hstep t ht.1 ht.2
      have hj : ∀ w ∈ P, Joined H (supp w) :=
        fun w hw => hHjoin w (hPt w hw) (hPn w hw)
      obtain ⟨H', hle, hc, hjoin⟩ := join_family H P supp (decide (t ∈ K))
        (by simpa only [decide_eq_true_eq] using hPc) hj
      simp only [decide_eq_true_eq] at hc
      refine ⟨H', by omega, ?_⟩
      intro w hw hn
      by_cases hwt : w = t
      · subst w
        exact joined_subset H' hPs hjoin
      · exact joined_mono hle (hHjoin w (by omega) hn)
    · refine ⟨H, by omega, ?_⟩
      intro w hw hn
      by_cases hwt : w = t
      · subst w
        have hsmall : (supp t).card ≤ 1 := by
          have : ¬ 2 ≤ (supp t).card := fun h => ht ⟨hn, h⟩
          omega
        exact joined_small H (supp t) hsmall
      · exact hHjoin w (by omega) hn

lemma component_card_antitone {α : Type*} [Finite α] (G H : SimpleGraph α)
    (hreach : ∀ a b, G.Reachable a b → H.Reachable a b) :
    Nat.card H.ConnectedComponent ≤ Nat.card G.ConnectedComponent := by
  let f : G.ConnectedComponent → H.ConnectedComponent :=
    Quot.map id (fun a b hab => hreach a b hab)
  have hf : Function.Surjective f := by
    intro c
    refine Quot.inductionOn c ?_
    intro a
    exact ⟨G.connectedComponentMk a, rfl⟩
  exact Nat.card_le_card_of_surjective f hf

lemma vertex_card_le_edges_components {α : Type*} [Finite α] (G : SimpleGraph α) :
    Nat.card α ≤ G.edgeSet.ncard + Nat.card G.ConnectedComponent := by
  obtain ⟨T, hTG, hT, hreach⟩ := G.exists_isAcyclic_reachable_eq_le
  have heq := hT.ncard_edgeSet_add_card_connectedComponent
  have he : T.edgeSet.ncard ≤ G.edgeSet.ncard :=
    Set.ncard_le_ncard (SimpleGraph.edgeSet_mono hTG)
  have hc := component_card_antitone G T (by intro a b hab; rwa [hreach])
  omega

def familyGraph {α : Type*} (supp : ℕ → Finset α) (F : Finset ℕ) : SimpleGraph α where
  Adj a b := a ≠ b ∧ ∃ w ∈ F, a ∈ supp w ∧ b ∈ supp w
  symm := ⟨by
    intro a b hab
    obtain ⟨hne, w, hw, ha, hb⟩ := hab
    exact ⟨hne.symm, w, hw, hb, ha⟩⟩
  loopless := ⟨by
    intro a ha
    exact ha.1 rfl⟩

lemma family_reachable {α : Type*} (H : SimpleGraph α)
    (supp : ℕ → Finset α) (F : Finset ℕ) (hj : ∀ w ∈ F, Joined H (supp w)) :
    ∀ a b, (familyGraph supp F).Reachable a b → H.Reachable a b := by
  intro a b hab
  obtain ⟨walk⟩ := hab
  induction walk with
  | nil => exact SimpleGraph.Reachable.refl _
  | cons hab _ ih =>
    obtain ⟨_, w, hw, ha, hb⟩ := hab
    exact (hj w hw _ ha _ hb).trans ih

lemma frontier_component_bound {α : Type*} [Fintype α] [DecidableEq α]
    (supp : ℕ → Finset α) (neg : ℕ → Prop) (K : Finset ℕ)
    (hstep : ∀ w, neg w → 2 ≤ (supp w).card → ∃ P : Finset ℕ,
      P.card ≤ 1 + (if w ∈ K then 1 else 0) ∧
      (∀ r ∈ P, r < w) ∧ (∀ r ∈ P, neg r) ∧ supp w ⊆ P.biUnion supp)
    (t : ℕ) (F : Finset ℕ) (hFt : ∀ w ∈ F, w < t) (hFn : ∀ w ∈ F, neg w) :
    Nat.card α ≤ (K.filter (· < t)).card +
      Nat.card (familyGraph supp F).ConnectedComponent := by
  obtain ⟨H, hHc, hHj⟩ := build_support_graph supp neg K hstep t
  have hj : ∀ w ∈ F, Joined H (supp w) := fun w hw => hHj w (hFt w hw) (hFn w hw)
  have hcc := component_card_antitone (familyGraph supp F) H (family_reachable H supp F hj)
  have hv := vertex_card_le_edges_components H
  omega

end PEqualNP.Outside.L_meta_4970.Components
