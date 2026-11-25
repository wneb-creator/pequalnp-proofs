import PetersenGeometry

namespace PEqualNP.Outside.L_meta_1884_aux.MatchingPrivate

open PEqualNP.Outside.L_meta_2590_aux.Surplus

lemma eligible_edge_private_pair {n : ℕ} {G : Fin n → Fin n → Prop} {D : Dag}
    (hG : sem_Gr G) (h : StrictLive n D) (hC : sem_Comp n G D)
    {pos : Fin n → ℕ × Bool} (hp : k4_Pos n G D pos)
    {x y : Fin n} (hx : x ∈ eligSet n D) (hy : y ∈ eligSet n D) (hxy : G x y) :
    ∃ e, e ∈ sem_W n D x ∧ sem_bar e ∈ sem_W n D y ∧
      e ∉ (ineligSet n D).image pos ∧ sem_bar e ∉ (ineligSet n D).image pos ∧
      y ∈ supp n D (src D (sem_bar e)) ∧ x ∈ supp n D (src D e) := by
  classical
  obtain ⟨e, he, hf, -, -, -⟩ := sem_edge_slots hG h.1 hC hxy
  have xe := (sem_mem_W.mp he).2.1
  have yf := (sem_mem_W.mp hf).2.1
  have avoid (z : Fin n) (hz : z ∈ eligSet n D) (a : ℕ × Bool)
      (ha : z ∈ supp n D (src D (sem_bar a))) :
      a ∉ (ineligSet n D).image pos := by
    intro ham
    obtain ⟨i, hi, hai⟩ := Finset.mem_image.mp ham
    have hs : supp n D (src D (sem_bar (pos i))) = {i} := (hp.1 i hi).2.2.2
    rw [← hai, hs, Finset.mem_singleton] at ha
    exact sem_mem_inelig.mp hi (ha ▸ hz)
  refine ⟨e, he, hf, avoid y hy e yf, ?_, yf, xe⟩
  apply avoid x hx (sem_bar e)
  simpa only [sem_bar_bar] using xe

end PEqualNP.Outside.L_meta_1884_aux.MatchingPrivate
