import PetersenGeometry

namespace PEqualNP.Outside.L_meta_1884_aux.EligibleEdgeSlots

open PEqualNP.Outside.L_meta_2590_aux.Surplus

lemma ineligible_chosen_support {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {i : Fin n} (hi : i ∈ ineligSet n D) {e : ℕ × Bool}
    (he : sem_W n D i = {e}) : supp n D (src D e) = {i} := by
  obtain ⟨e0, -, -, hs, -, -, hw, -⟩ := sem_inelig_consumer hG h hC hi
  have same : e = e0 := Finset.singleton_injective (he.symm.trans hw)
  exact same ▸ hs

lemma eligible_edge_private_pair {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    (I : Finset (Fin n)) (hI : I ⊆ ineligSet n D) (pos : Fin n → ℕ × Bool)
    (hp : ∀ i ∈ I, sem_W n D i = {sem_bar (pos i)})
    {x y : Fin n} (hx : x ∈ eligSet n D) (hy : y ∈ eligSet n D) (hxy : G x y) :
    ∃ e, e ∈ sem_W n D x ∧ sem_bar e ∈ sem_W n D y ∧
      e ∉ I.image pos ∧ sem_bar e ∉ I.image pos ∧
      y ∈ supp n D (src D (sem_bar e)) ∧ x ∈ supp n D (src D e) := by
  classical
  obtain ⟨e, he, hf, -, -, -⟩ := sem_edge_slots hG h.1 hC hxy
  have xe := (sem_mem_W.mp he).2.1
  have yf := (sem_mem_W.mp hf).2.1
  have avoid (z : Fin n) (hz : z ∈ eligSet n D) (a : ℕ × Bool)
      (ha : z ∈ supp n D (src D (sem_bar a))) : a ∉ I.image pos := by
    intro ham
    obtain ⟨i, hi, hai⟩ := Finset.mem_image.mp ham
    have hs := ineligible_chosen_support hG h hC (hI hi) (hp i hi)
    rw [← hai, hs, Finset.mem_singleton] at ha
    exact sem_mem_inelig.mp (hI hi) (ha ▸ hz)
  refine ⟨e, he, hf, avoid y hy e yf, ?_, yf, xe⟩
  apply avoid x hx (sem_bar e)
  simpa only [sem_bar_bar] using xe

end PEqualNP.Outside.L_meta_1884_aux.EligibleEdgeSlots
