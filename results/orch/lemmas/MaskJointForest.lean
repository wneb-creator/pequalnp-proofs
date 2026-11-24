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
