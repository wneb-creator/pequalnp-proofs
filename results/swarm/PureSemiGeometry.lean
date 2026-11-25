import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012.PureSemiGeometry

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm

def raw {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  decide (∃ v ∈ S, x v = true)

def product {n : ℕ} (P Q : Finset (Fin n)) (x : Fin n → Bool) : Bool :=
  raw P x && raw Q x

def Safe {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (w : Fin n) : Prop :=
  ∀ x : Fin n → Bool, product P Q x = true → x w = true → graphFun G ∅ x = true

def leftCenters {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) : Finset (Fin n) :=
  P.filter fun p => ∀ q ∈ Q, G.Adj p q

def rightCenters {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) : Finset (Fin n) :=
  Q.filter fun q => ∀ p ∈ P, G.Adj p q

def centers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) : Finset (Fin n) :=
  leftCenters G P Q ∪ rightCenters G P Q

lemma raw_true {n : ℕ} (S : Finset (Fin n)) (x : Fin n → Bool) :
    raw S x = true ↔ ∃ v ∈ S, x v = true := by
  simp [raw]

lemma product_true {n : ℕ} (P Q : Finset (Fin n)) (x : Fin n → Bool) :
    product P Q x = true ↔ (∃ p ∈ P, x p = true) ∧ ∃ q ∈ Q, x q = true := by
  simp [product, raw]

lemma graph_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) : graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

lemma safe_left {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) {z : Fin n} (hz : z ∈ P) (hs : Safe G P Q z) :
    ∀ q ∈ Q, G.Adj z q := by
  intro q hq
  apply (graph_pair G z q).mp
  apply hs
  · exact (product_true P Q _).mpr
      ⟨⟨z, hz, by simp [pairInput]⟩, q, hq, by simp [pairInput]⟩
  · simp [pairInput]

lemma safe_right {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) {z : Fin n} (hz : z ∈ Q) (hs : Safe G P Q z) :
    ∀ p ∈ P, G.Adj p z := by
  intro p hp
  apply (graph_pair G p z).mp
  apply hs
  · exact (product_true P Q _).mpr
      ⟨⟨p, hp, by simp [pairInput]⟩, z, hz, by simp [pairInput]⟩
  · simp [pairInput]

lemma pair_cross {n : ℕ} (P Q : Finset (Fin n)) (hdis : Disjoint P Q)
    (u v : Fin n) (hprod : product P Q (pairInput u v) = true) :
    (u ∈ P ∧ v ∈ Q) ∨ (v ∈ P ∧ u ∈ Q) := by
  obtain ⟨⟨p, hp, hxp⟩, q, hq, hxq⟩ := (product_true P Q _).mp hprod
  simp only [pairInput, decide_eq_true_eq] at hxp hxq
  rcases hxp with rfl | rfl <;> rcases hxq with rfl | rfl
  · exact (Finset.disjoint_left.mp hdis hp hq).elim
  · exact Or.inl ⟨hp, hq⟩
  · exact Or.inr ⟨hp, hq⟩
  · exact (Finset.disjoint_left.mp hdis hp hq).elim

lemma active_safe_mem_centers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (hdis : Disjoint P Q) (u v w : Fin n)
    (hprod : product P Q (pairInput u v) = true) (hw : pairInput u v w = true)
    (hsafe : Safe G P Q w) : w ∈ centers G P Q := by
  have hwuv : w = u ∨ w = v := by simpa [pairInput] using hw
  have hwPQ : w ∈ P ∨ w ∈ Q := by
    rcases pair_cross P Q hdis u v hprod with ⟨huP, hvQ⟩ | ⟨hvP, huQ⟩
    · rcases hwuv with rfl | rfl
      · exact Or.inl huP
      · exact Or.inr hvQ
    · rcases hwuv with rfl | rfl
      · exact Or.inr huQ
      · exact Or.inl hvP
  rcases hwPQ with hwP | hwQ
  · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
      ⟨hwP, safe_left G P Q hwP hsafe⟩)
  · exact Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨hwQ, safe_right G P Q hwQ hsafe⟩)

lemma filter_to_centers_on_pairs {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q S : Finset (Fin n)) (hdis : Disjoint P Q)
    (hsafe : ∀ w ∈ S, Safe G P Q w) (u v : Fin n) :
    (product P Q (pairInput u v) && raw (S ∩ centers G P Q) (pairInput u v)) =
      (product P Q (pairInput u v) && raw S (pairInput u v)) := by
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.and_eq_true]
  constructor
  · rintro ⟨hp, hr⟩
    obtain ⟨w, hw, hx⟩ := (raw_true _ _).mp hr
    exact ⟨hp, (raw_true _ _).mpr ⟨w, (Finset.mem_inter.mp hw).1, hx⟩⟩
  · rintro ⟨hp, hr⟩
    obtain ⟨w, hw, hx⟩ := (raw_true _ _).mp hr
    exact ⟨hp, (raw_true _ _).mpr ⟨w, Finset.mem_inter.mpr
      ⟨hw, active_safe_mem_centers G P Q hdis u v w hp hx (hsafe w hw)⟩, hx⟩⟩

lemma raw_centers_under {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q S : Finset (Fin n)) (x : Fin n → Bool) :
    raw (S ∩ centers G P Q) x = true → raw S x = true := by
  intro h
  obtain ⟨w, hw, hx⟩ := (raw_true _ _).mp h
  exact (raw_true _ _).mpr ⟨w, (Finset.mem_inter.mp hw).1, hx⟩

lemma left_centers_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (h4 : NoFourCycle G) (hQ : 2 ≤ Q.card) :
    (leftCenters G P Q).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  by_contra hne
  obtain ⟨_, huQ⟩ := Finset.mem_filter.mp hu
  obtain ⟨_, hvQ⟩ := Finset.mem_filter.mp hv
  have hsub : Q ⊆ Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, huQ w hw, hvQ w hw⟩
  have hc := (Finset.card_le_card hsub).trans (h4 u v hne)
  omega

lemma right_centers_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (h4 : NoFourCycle G) (hP : 2 ≤ P.card) :
    (rightCenters G P Q).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro u hu v hv
  by_contra hne
  obtain ⟨_, huP⟩ := Finset.mem_filter.mp hu
  obtain ⟨_, hvP⟩ := Finset.mem_filter.mp hv
  have hsub : P ⊆ Finset.univ.filter fun w => G.Adj u w ∧ G.Adj v w := by
    intro w hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (huP w hw).symm, (hvP w hw).symm⟩
  have hc := (Finset.card_le_card hsub).trans (h4 u v hne)
  omega

lemma centers_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (P Q : Finset (Fin n)) (h4 : NoFourCycle G) (hP : 2 ≤ P.card) (hQ : 2 ≤ Q.card) :
    (centers G P Q).card ≤ 2 := by
  have hL := left_centers_card G P Q h4 hQ
  have hR := right_centers_card G P Q h4 hP
  have hu := Finset.card_union_le (leftCenters G P Q) (rightCenters G P Q)
  unfold centers
  omega

lemma filter_kind {α : Type*} [DecidableEq α] (Z S : Finset α) (hZ : Z.card ≤ 2) :
    S ∩ Z = ∅ ∨ (∃ v, S ∩ Z = {v}) ∨ (S ∩ Z = Z ∧ Z.card = 2) := by
  by_cases he : S ∩ Z = ∅
  · exact Or.inl he
  have hp : 0 < (S ∩ Z).card := Finset.card_pos.mpr
    (Finset.nonempty_iff_ne_empty.mpr he)
  by_cases h1 : (S ∩ Z).card = 1
  · exact Or.inr (Or.inl (Finset.card_eq_one.mp h1))
  have hc : (S ∩ Z).card ≤ Z.card := Finset.card_le_card Finset.inter_subset_right
  have h2 : (S ∩ Z).card = 2 := by omega
  have hz2 : Z.card = 2 := by omega
  exact Or.inr (Or.inr ⟨Finset.eq_of_subset_of_card_le Finset.inter_subset_right
    (by omega), hz2⟩)

lemma shared_center_projection_budget {α : Type*} [DecidableEq α]
    (good bad : Finset α) (removed : ℕ) (hdis : Disjoint good bad)
    (hgood : good.Nonempty) (hbad : bad.Nonempty)
    (hcut : (good ∪ bad).card ≤ removed + 1) :
    (good.card - 1) + 1 ≤ removed := by
  have hg := Finset.card_pos.mpr hgood
  have hb := Finset.card_pos.mpr hbad
  have hu := Finset.card_union_of_disjoint hdis
  omega

lemma projected_network_and_centers_budget {α β : Type*} [DecidableEq α]
    (good bad : Finset α) (Z : Finset β) (removed : ℕ) (hdis : Disjoint good bad)
    (hgood : good.Nonempty) (hbad : bad.Nonempty) (hZ : Z.card ≤ 2)
    (hcut : (good ∪ bad).card ≤ removed + 1) :
    (good.card - 1) + (Z.card - 1) ≤ removed := by
  have hc := shared_center_projection_budget good bad removed hdis hgood hbad hcut
  omega

end PEqualNP.Outside.L_meta_5012.PureSemiGeometry
