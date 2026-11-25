import ComputationalRoot13
import ComputationalLiveBound

namespace PEqualNP.Outside.L_meta_10760_aux

lemma root_one_not_exclusion
    (hcheck : chk [] rootSeeds 0 13 1 FF 1 = false)
    {S : Finset ℕ} (hS : (S : Set ℕ) ⊆ C (mz 0) (WZ [] 0))
    (hl : Live Z0 (mz 0) (tz 0) 13 1 S) : False := by
  apply live_chk_false (E := []) (Q := rootSeeds) (Z := 0) (L := 14)
    (Or.inl rfl) (by decide +kernel) (by omega) rootSeeds_sound (by omega)
    hS hl root13 ffull
  intro p hp
  simp only [List.mem_singleton] at hp
  subst p
  exact hcheck

end PEqualNP.Outside.L_meta_10760_aux
