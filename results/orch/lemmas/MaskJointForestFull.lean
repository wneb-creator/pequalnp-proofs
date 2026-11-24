import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.MaskJointForest

open PEqualNP.TopForm

lemma no_rectangle {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (a b c d : Fin n) (hab : a ≠ b)
    (hac : G.Adj a c) (had : G.Adj a d) (hbc : G.Adj b c) (hbd : G.Adj b d) : c = d := by
  by_contra hcd
  have hs : ({c,d} : Finset (Fin n)) ⊆ Finset.univ.filter (fun v => G.Adj a v ∧ G.Adj b v) := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hac, hbc⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, had, hbd⟩
  have hcard := (Finset.card_le_card hs).trans (hG a b hab)
  simp [hcd] at hcard

lemma row_universal_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (E : Finset (Fin n × Fin n))
    (hE : ∀ e ∈ E, G.Adj e.1 e.2) (hEn : E.Nonempty) (a : Fin n)
    (ha : ∀ b ∈ E.image Prod.snd, (a,b) ∈ E) :
    E.card + 1 ≤ (E.image Prod.fst).card + (E.image Prod.snd).card := by
  classical
  let F := E.filter fun e => e.1 = a
  let R := E.filter fun e => e.1 ≠ a
  have hF : F.card ≤ (E.image Prod.snd).card := by
    have hinj : Set.InjOn Prod.snd (↑F : Set (Fin n × Fin n)) := by
      intro e he f hf hef
      exact Prod.ext ((Finset.mem_filter.mp he).2.trans (Finset.mem_filter.mp hf).2.symm) hef
    rw [← Finset.card_image_of_injOn hinj]
    apply Finset.card_le_card
    intro b hb
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_image.mpr ⟨e, (Finset.mem_filter.mp he).1, rfl⟩
  have hR : R.card ≤ ((E.image Prod.fst).erase a).card := by
    have hinj : Set.InjOn Prod.fst (↑R : Set (Fin n × Fin n)) := by
      intro e he f hf hef
      have heE := (Finset.mem_filter.mp he).1
      have hfE := (Finset.mem_filter.mp hf).1
      have hne : a ≠ e.1 := ((Finset.mem_filter.mp he).2).symm
      have hfirst : (a,e.2) ∈ E := ha _ (Finset.mem_image.mpr ⟨e, heE, rfl⟩)
      have hsecond : (a,f.2) ∈ E := ha _ (Finset.mem_image.mpr ⟨f, hfE, rfl⟩)
      have hsnd := no_rectangle G hG a e.1 e.2 f.2 hne
        (hE _ hfirst) (hE _ hsecond) (hE _ heE) (by simpa only [hef] using hE _ hfE)
      exact Prod.ext hef hsnd
    rw [← Finset.card_image_of_injOn hinj]
    apply Finset.card_le_card
    intro b hb
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hb
    exact Finset.mem_erase.mpr ⟨(Finset.mem_filter.mp he).2,
      Finset.mem_image.mpr ⟨e, (Finset.mem_filter.mp he).1, rfl⟩⟩
  have haE : a ∈ E.image Prod.fst := by
    obtain ⟨e, he⟩ := hEn
    exact Finset.mem_image.mpr ⟨(a,e.2), ha _ (Finset.mem_image.mpr ⟨e, he, rfl⟩), rfl⟩
  have hdis : Disjoint F R := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact (Finset.mem_filter.mp hf).2 (Finset.mem_filter.mp he).2
  have hun : F ∪ R = E := by
    ext e
    simp only [F, R, Finset.mem_union, Finset.mem_filter]
    tauto
  have hsum : F.card + R.card = E.card := by
    rw [← Finset.card_union_of_disjoint hdis, hun]
  have herase := Finset.card_erase_add_one haE
  omega

lemma column_universal_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (E : Finset (Fin n × Fin n))
    (hE : ∀ e ∈ E, G.Adj e.1 e.2) (hEn : E.Nonempty) (b : Fin n)
    (hb : ∀ a ∈ E.image Prod.fst, (a,b) ∈ E) :
    E.card + 1 ≤ (E.image Prod.fst).card + (E.image Prod.snd).card := by
  classical
  let T := E.image Prod.swap
  have hT : ∀ e ∈ T, G.Adj e.1 e.2 := by
    intro e he
    obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp he
    exact (hE f hf).symm
  have hTsnd : T.image Prod.snd = E.image Prod.fst := by
    simp [T, Finset.image_image, Function.comp_def]
  have hTfst : T.image Prod.fst = E.image Prod.snd := by
    simp [T, Finset.image_image, Function.comp_def]
  have hTcard : T.card = E.card := Finset.card_image_of_injective _ Prod.swap_injective
  have hbb : ∀ a ∈ T.image Prod.snd, (b,a) ∈ T := by
    intro a ha
    rw [hTsnd] at ha
    exact Finset.mem_image.mpr ⟨(a,b), hb a ha, rfl⟩
  have hh := row_universal_bound G hG T hT (hEn.image _) b hbb
  rw [hTcard, hTfst, hTsnd] at hh
  omega

end PEqualNP.Outside.L_meta_1477.MaskJointForest

namespace PEqualNP.Outside.L_meta_1477.MaskJointForest

open PEqualNP.TopForm

lemma rectangle_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (X Y : Finset (Fin n))
    (hXY : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b) (hN : (X ×ˢ Y).Nonempty) :
    (X ×ˢ Y).card + 1 ≤ ((X ×ˢ Y).image Prod.fst).card + ((X ×ˢ Y).image Prod.snd).card := by
  obtain ⟨e, he⟩ := hN
  have hXe := (Finset.mem_product.mp he).1
  apply row_universal_bound G hG (X ×ˢ Y)
    (fun f hf => hXY f.1 (Finset.mem_product.mp hf).1 f.2 (Finset.mem_product.mp hf).2)
    ⟨e, he⟩ e.1
  intro b hb
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hb
  exact Finset.mem_product.mpr ⟨hXe, (Finset.mem_product.mp hf).2⟩

lemma disjoint_union_bound {n : ℕ} (E F : Finset (Fin n × Fin n))
    (hleft : Disjoint (E.image Prod.fst) (F.image Prod.fst))
    (hright : Disjoint (E.image Prod.snd) (F.image Prod.snd))
    (hE : E.Nonempty → E.card + 1 ≤ (E.image Prod.fst).card + (E.image Prod.snd).card)
    (hF : F.Nonempty → F.card + 1 ≤ (F.image Prod.fst).card + (F.image Prod.snd).card)
    (hN : (E ∪ F).Nonempty) :
    (E ∪ F).card + 1 ≤ ((E ∪ F).image Prod.fst).card + ((E ∪ F).image Prod.snd).card := by
  by_cases he : E = ∅
  · simpa only [he, Finset.empty_union] using hF (by simpa only [he, Finset.empty_union] using hN)
  by_cases hf : F = ∅
  · simpa only [hf, Finset.union_empty] using hE (by simpa only [hf, Finset.union_empty] using hN)
  have hdis : Disjoint E F := by
    apply Finset.disjoint_left.mpr
    intro e he hf
    exact Finset.disjoint_left.mp hleft (Finset.mem_image.mpr ⟨e, he, rfl⟩)
      (Finset.mem_image.mpr ⟨e, hf, rfl⟩)
  rw [Finset.card_union_of_disjoint hdis, Finset.image_union, Finset.image_union,
    Finset.card_union_of_disjoint hleft, Finset.card_union_of_disjoint hright]
  have hhE := hE (Finset.nonempty_iff_ne_empty.mpr he)
  have hhF := hF (Finset.nonempty_iff_ne_empty.mpr hf)
  omega

lemma two_rectangles_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (X Y Z W : Finset (Fin n))
    (hXZ : Disjoint X Z) (hYW : Disjoint Y W)
    (hXY : ∀ a ∈ X, ∀ b ∈ Y, G.Adj a b)
    (hZW : ∀ a ∈ Z, ∀ b ∈ W, G.Adj a b)
    (hN : ((X ×ˢ Y) ∪ (Z ×ˢ W)).Nonempty) :
    ((X ×ˢ Y) ∪ (Z ×ˢ W)).card + 1 ≤
      (((X ×ˢ Y) ∪ (Z ×ˢ W)).image Prod.fst).card +
        (((X ×ˢ Y) ∪ (Z ×ˢ W)).image Prod.snd).card := by
  apply disjoint_union_bound (X ×ˢ Y) (Z ×ˢ W) ?_ ?_
    (rectangle_bound G hG X Y hXY) (rectangle_bound G hG Z W hZW) hN
  · apply Finset.disjoint_left.mpr
    intro a ha hb
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨f, hf, hef⟩ := Finset.mem_image.mp hb
    exact Finset.disjoint_left.mp hXZ (Finset.mem_product.mp he).1
      (hef ▸ (Finset.mem_product.mp hf).1)
  · apply Finset.disjoint_left.mpr
    intro b hb hc
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hb
    obtain ⟨f, hf, hef⟩ := Finset.mem_image.mp hc
    exact Finset.disjoint_left.mp hYW (Finset.mem_product.mp he).2
      (hef ▸ (Finset.mem_product.mp hf).2)

def maskJointEdges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (A B C D : Finset (Fin n)) : Finset (Fin n × Fin n) :=
  (A ×ˢ B).filter fun e =>
    (∀ b ∈ B, G.Adj e.1 b) ∨ (∀ a ∈ A, G.Adj e.2 a) ∨
      ((e.1 ∈ C ∨ e.2 ∈ C) ∧ (e.1 ∈ D ∨ e.2 ∈ D))

lemma maskJointEdges_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (A B C D : Finset (Fin n)) (hCD : Disjoint C D)
    (hjoint : ∀ a ∈ A, ∀ b ∈ B,
      (a ∈ C ∨ b ∈ C) → (a ∈ D ∨ b ∈ D) → G.Adj a b)
    (hN : (maskJointEdges G A B C D).Nonempty) :
    (maskJointEdges G A B C D).card + 1 ≤
      ((maskJointEdges G A B C D).image Prod.fst).card +
        ((maskJointEdges G A B C D).image Prod.snd).card := by
  classical
  let E := maskJointEdges G A B C D
  have hE : ∀ e ∈ E, G.Adj e.1 e.2 := by
    intro e he
    obtain ⟨heAB, heJ⟩ := Finset.mem_filter.mp he
    obtain ⟨heA, heB⟩ := Finset.mem_product.mp heAB
    rcases heJ with hrow | hcol | ⟨hC, hD⟩
    · exact hrow _ heB
    · exact (hcol _ heA).symm
    · exact hjoint _ heA _ heB hC hD
  by_cases hrow : ∃ a ∈ A, ∀ b ∈ B, G.Adj a b
  · obtain ⟨a, ha, hab⟩ := hrow
    apply row_universal_bound G hG E hE hN a
    intro b hb
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp hb
    have heB := (Finset.mem_product.mp (Finset.mem_filter.mp he).1).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨ha, heB⟩, Or.inl hab⟩
  by_cases hcol : ∃ b ∈ B, ∀ a ∈ A, G.Adj b a
  · obtain ⟨b, hb, hba⟩ := hcol
    apply column_universal_bound G hG E hE hN b
    intro a ha
    obtain ⟨e, he, rfl⟩ := Finset.mem_image.mp ha
    have heA := (Finset.mem_product.mp (Finset.mem_filter.mp he).1).1
    exact Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨heA, hb⟩, Or.inr (Or.inl hba)⟩
  have heq : E = ((A ∩ C) ×ˢ (B ∩ D)) ∪ ((A ∩ D) ×ˢ (B ∩ C)) := by
    ext e
    simp only [E, maskJointEdges, Finset.mem_filter, Finset.mem_product, Finset.mem_inter, Finset.mem_union]
    constructor
    · rintro ⟨⟨ha, hb⟩, hr | hc | ⟨hC, hD⟩⟩
      · exact (hrow ⟨e.1, ha, hr⟩).elim
      · exact (hcol ⟨e.2, hb, hc⟩).elim
      · rcases hC with hc | hc <;> rcases hD with hd | hd
        · exact (Finset.disjoint_left.mp hCD hc hd).elim
        · exact Or.inl ⟨⟨ha, hc⟩, ⟨hb, hd⟩⟩
        · exact Or.inr ⟨⟨ha, hd⟩, ⟨hb, hc⟩⟩
        · exact (Finset.disjoint_left.mp hCD hc hd).elim
    · rintro (⟨⟨ha, hc⟩, ⟨hb, hd⟩⟩ | ⟨⟨ha, hd⟩, ⟨hb, hc⟩⟩)
      · exact ⟨⟨ha, hb⟩, Or.inr (Or.inr ⟨Or.inl hc, Or.inr hd⟩)⟩
      · exact ⟨⟨ha, hb⟩, Or.inr (Or.inr ⟨Or.inr hc, Or.inl hd⟩)⟩
  change E.card + 1 ≤ (E.image Prod.fst).card + (E.image Prod.snd).card
  rw [heq]
  apply two_rectangles_bound G hG (A ∩ C) (B ∩ D) (A ∩ D) (B ∩ C)
  · exact Finset.disjoint_left.mpr fun a ha hb =>
      Finset.disjoint_left.mp hCD (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2
  · exact Finset.disjoint_left.mpr fun b hb hc =>
      Finset.disjoint_left.mp hCD (Finset.mem_inter.mp hc).2 (Finset.mem_inter.mp hb).2
  · intro a ha b hb
    exact hjoint a (Finset.mem_inter.mp ha).1 b (Finset.mem_inter.mp hb).1
      (Or.inl (Finset.mem_inter.mp ha).2) (Or.inr (Finset.mem_inter.mp hb).2)
  · intro a ha b hb
    exact hjoint a (Finset.mem_inter.mp ha).1 b (Finset.mem_inter.mp hb).1
      (Or.inr (Finset.mem_inter.mp hb).2) (Or.inl (Finset.mem_inter.mp ha).2)
  · simpa only [← heq] using hN

end PEqualNP.Outside.L_meta_1477.MaskJointForest
