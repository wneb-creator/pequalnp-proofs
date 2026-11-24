import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1477.SingletonPairSpokes

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
  PEqualNP.EdgeOwnership

noncomputable def spokes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : Fin n) (S : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) : Finset (Sym2 (Fin n)) := by
  classical
  exact ((S.filter (G.Adj a)).image (fun u => s(a,u))) \ E

lemma mem_spokes {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : Fin n) (S : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) :
    e∈spokes G a S E ↔ e∉E ∧ ∃u∈S,G.Adj a u ∧ s(a,u)=e := by
  classical
  simp only [spokes,Finset.mem_sdiff,Finset.mem_image,Finset.mem_filter]
  aesop

lemma spokes_card_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a : Fin n) (S : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) : (spokes G a S E).card≤S.card := by
  classical
  exact (Finset.card_le_card Finset.sdiff_subset).trans
    ((Finset.card_image_le).trans (Finset.card_filter_le _ _))

lemma spokes_small_cleaner {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (a z : Fin n) (S : Finset (Fin n)) (E : Finset (Sym2 (Fin n)))
    (hadj : ∀u∈S,G.Adj z u) (howned : ∀u∈S,s(z,u)∈E) : (spokes G a S E).card≤1 := by
  classical
  by_cases he : a=z
  · subst a
    have hemp : spokes G z S E=∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro e he
      obtain ⟨hn,u,hu,_,rfl⟩ := (mem_spokes G z S E e).mp he
      exact hn (howned u hu)
    simp [hemp]
  · have hsub : S.filter (G.Adj a) ⊆ Finset.univ.filter (fun u=>G.Adj a u ∧ G.Adj z u) := by
      intro u hu
      obtain ⟨hu,ha⟩ := Finset.mem_filter.mp hu
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,ha,hadj u hu⟩
    have hc := (Finset.card_le_card hsub).trans (hG a z he)
    exact (Finset.card_le_card Finset.sdiff_subset).trans ((Finset.card_image_le).trans hc)

lemma union_small_uniform {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n→Fin 2) (hcolor : ∀u v,G.Adj u v→color u≠color v)
    (a b : Fin n) (hab : a=b ∨ G.Adj a b) (S : Finset (Fin n)) (E : Finset (Sym2 (Fin n)))
    (huniform : ∀u∈S,∀v∈S,color u=color v)
    (hA : (spokes G a S E).card≤1) (hB : (spokes G b S E).card≤1) :
    (spokes G a S E ∪ spokes G b S E).card≤1 := by
  classical
  rcases hab with rfl | hab
  · simpa only [Finset.union_self] using hA
  by_cases he : spokes G a S E=∅
  · simpa only [he,Finset.empty_union] using hB
  obtain ⟨e,he⟩ := Finset.nonempty_iff_ne_empty.mpr he
  obtain ⟨_,u,hu,hau,_⟩ := (mem_spokes G a S E e).mp he
  have hemp : spokes G b S E=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro f hf
    obtain ⟨_,v,hv,hbv,_⟩ := (mem_spokes G b S E f).mp hf
    have h1 := hcolor a b hab
    have h2 := hcolor a u hau
    have h3 := hcolor b v hbv
    have h4 := huniform u hu v hv
    have haLt := (color a).isLt
    have hbLt := (color b).isLt
    have huLt := (color u).isLt
    have hvLt := (color v).isLt
    omega
  simpa only [hemp,Finset.union_empty] using hA

end PEqualNP.Outside.L_meta_1477.SingletonPairSpokes

namespace PEqualNP.Outside.L_meta_1477.SingletonSameColorDrop

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  SingletonPairSpokes PEqualNP.TopForm

noncomputable def drop {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : Fin n) : Finset (Sym2 (Fin n)) := by
  classical
  exact (Finset.univ.filter (fun q => G.Adj a q ∧ G.Adj b q)).image (fun q => s(a,q))

lemma drop_card_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (a b : Fin n) (hab : a ≠ b) : (drop G a b).card ≤ 1 := by
  classical
  exact Finset.card_image_le.trans (hG a b hab)

lemma spokes_subset_drop {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Fin 2) (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (a b : Fin n) (hab : color a = color b) (S B : Finset (Fin n))
    (E : Finset (Sym2 (Fin n))) (hSB : S ⊆ B)
    (hB : ∀ u ∈ B, color u ≠ color b → G.Adj b u) :
    spokes G a S E ⊆ drop G a b := by
  classical
  intro e he
  obtain ⟨_,u,hu,hau,rfl⟩ := (mem_spokes G a S E e).mp he
  have hub : color u ≠ color b := by
    intro h
    exact hcolor a u hau (hab.trans h.symm)
  exact Finset.mem_image.mpr ⟨u, Finset.mem_filter.mpr
    ⟨Finset.mem_univ _,hau,hB u (hSB hu) hub⟩,rfl⟩

lemma same_color_support_spokes_empty {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (a d : Fin n) (had : color a = color d) (S : Finset (Fin n))
    (E : Finset (Sym2 (Fin n))) (hd : d ∈ S)
    (huniform : ∀ u ∈ S, ∀ v ∈ S, color u = color v) : spokes G a S E = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro e he
  obtain ⟨_,u,hu,hau,_⟩ := (mem_spokes G a S E e).mp he
  exact hcolor a u hau (had.trans (huniform d hd u hu))

lemma enriched_spokes_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (color : Fin n → Fin 2) (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (b d : Fin n) (hbd : color b = color d) (S : Finset (Fin n))
    (E : Finset (Sym2 (Fin n))) (huniform : ∀ u ∈ S, ∀ v ∈ S, color u = color v)
    (hsmall : (spokes G b S E).card ≤ 1) :
    (spokes G b S E ∪ (if d ∈ S then {s(d,d)} else ∅)).card ≤ 1 := by
  classical
  by_cases hd : d ∈ S
  · have hemp := same_color_support_spokes_empty G color hcolor b d hbd S E hd huniform
    simp [hd,hemp]
  · simpa only [if_neg hd,Finset.union_empty] using hsmall

lemma diagonal_union_small {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hG : NoFourCycle G) (color : Fin n → Fin 2)
    (hcolor : ∀ u v, G.Adj u v → color u ≠ color v)
    (a b d z : Fin n) (hab : color a = color b) (had : color a = color d)
    (S B : Finset (Fin n)) (E : Finset (Sym2 (Fin n))) (hSB : S ⊆ B)
    (hB : ∀ u ∈ B, color u ≠ color b → G.Adj b u)
    (hadj : ∀ u ∈ S, G.Adj z u) (howned : ∀ u ∈ S, s(z,u) ∈ E) :
    ((spokes G a S E \ drop G a b) ∪ spokes G b S E ∪
      (if d ∈ S then {s(d,d)} else ∅)).card ≤ 1 := by
  classical
  have hdrop : spokes G a S E \ drop G a b = ∅ :=
    Finset.sdiff_eq_empty_iff_subset.mpr (spokes_subset_drop G color hcolor a b hab S B E hSB hB)
  rw [hdrop,Finset.empty_union]
  by_cases hd : d ∈ S
  · have huniform : ∀ u ∈ S, ∀ v ∈ S, color u = color v := by
      intro u hu v hv
      have h1 := hcolor z u (hadj u hu)
      have h2 := hcolor z v (hadj v hv)
      have hz := (color z).isLt
      have hu' := (color u).isLt
      have hv' := (color v).isLt
      omega
    have hemp := same_color_support_spokes_empty G color hcolor b d
      (hab.symm.trans had) S E hd huniform
    simp [hd,hemp]
  · simpa only [if_neg hd,Finset.union_empty] using spokes_small_cleaner G hG b z S E hadj howned

end PEqualNP.Outside.L_meta_1477.SingletonSameColorDrop
