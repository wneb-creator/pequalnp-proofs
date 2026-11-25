import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.Centres
open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

lemma hit_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (a : Fin n) (Z S : Finset (Fin n))
    (ha : a ∉ S) (hcentres : ∀ z∈Z, G.Adj a z)
    (hhit : ∀ z∈Z, ∃ u∈S, G.Adj z u) : Z.card ≤ S.card := by
  classical
  let f : Fin n → Fin n := fun z => if hz : z∈Z then (hhit z hz).choose else a
  have hf (z : Fin n) (hz : z∈Z) : f z∈S ∧ G.Adj z (f z) := by
    simp only [f,hz,dif_pos]
    exact (hhit z hz).choose_spec
  apply Finset.card_le_card_of_injOn f
  · intro z hz
    exact (hf z hz).1
  · intro z hz z' hz' heq
    by_contra hzz
    have hau : a ≠ f z := by intro he; exact ha (he ▸ (hf z hz).1)
    have hsub : ({z,z'} : Finset (Fin n)) ⊆
        Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj (f z) w) := by
      intro w hw
      simp only [Finset.mem_insert,Finset.mem_singleton] at hw
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      rcases hw with hw | hw
      · subst w
        exact ⟨hcentres z hz,(hf z hz).2.symm⟩
      · subst w
        exact ⟨hcentres z' hz',by rw [heq]; exact (hf z' hz').2.symm⟩
    have hc := (Finset.card_le_card hsub).trans (h4 a (f z) hau)
    rw [Finset.card_pair hzz] at hc
    omega

lemma extension_neighbour {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) (hno : graphFun G ∅ x = false) (z : Fin n)
    (hext : graphFun G ∅ (Function.update x z true) = true) :
    ∃ u, x u = true ∧ G.Adj z u := by
  have hf : ∃ u v, G.Adj u v ∧ Function.update x z true u = true ∧
      Function.update x z true v = true := by simpa [graphFun] using hext
  obtain ⟨u,v,huv,hu,hv⟩ := hf
  by_cases huz : u=z
  · subst u
    have hvz : v≠z := G.ne_of_adj huv.symm
    rw [Function.update_of_ne hvz] at hv
    exact ⟨v,hv,huv⟩
  · rw [Function.update_of_ne huz] at hu
    by_cases hvz : v=z
    · subst v
      exact ⟨u,hu,huv.symm⟩
    · rw [Function.update_of_ne hvz] at hv
      have hyes : graphFun G ∅ x = true := by
        simp only [graphFun,Bool.or_eq_true,decide_eq_true_eq]
        exact Or.inr ⟨u,v,huv,hu,hv⟩
      rw [hno] at hyes
      cases hyes

lemma independent_payload_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (a : Fin n) (Z : Finset (Fin n))
    (hcentres : ∀ z∈Z, G.Adj a z)
    (f : (Fin n → Bool) → Bool)
    (hmono : ∀ x y, (∀ u, x u = true → y u = true) → f x = true → f y = true)
    (hclean : ∀ z∈Z, ∀ y, f y = true → y z = true → graphFun G ∅ y = true)
    (x : Fin n → Bool) (hf : f x = true) (ha : x a = false)
    (hno : graphFun G ∅ x = false) :
    Z.card ≤ (Finset.univ.filter (fun u => x u = true)).card := by
  classical
  apply hit_bound G h4 a Z (Finset.univ.filter (fun u => x u = true))
  · simp [ha]
  · exact hcentres
  · intro z hz
    have hxy : ∀ u, x u = true → Function.update x z true u = true := by
      intro u hu
      by_cases huz : u=z
      · subst u; simp
      · rw [Function.update_of_ne huz]; exact hu
    have hext := hclean z hz (Function.update x z true) (hmono x _ hxy hf) (by simp)
    obtain ⟨u,hu,hzu⟩ := extension_neighbour G x hno z hext
    exact ⟨u,by simp [hu],hzu⟩

end PEqualNP.Outside.L_meta_4675.Centres
