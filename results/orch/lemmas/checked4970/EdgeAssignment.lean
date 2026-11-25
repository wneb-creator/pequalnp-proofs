import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux

open Finset

theorem serving_edge_assignment {p l : Nat} (E : Finset (Fin p × Fin l))
    (pointServes lineServes : Fin p × Fin l → Prop)
    (hserve : ∀ e ∈ E, pointServes e ∨ lineServes e) :
    ∃ owner : Fin p × Fin l → Fin (p + l),
      (∀ e ∈ E,
        (owner e = Fin.castAdd l e.1 ∧ pointServes e) ∨
        (owner e = Fin.natAdd p e.2 ∧ lineServes e)) ∧
      (∀ a b, (a,b) ∈ E →
        Fin.castAdd l a ∈ E.image owner ∨ Fin.natAdd p b ∈ E.image owner) ∧
      (∀ v ∈ E.image owner, (E.filter (fun e => owner e = v)).Nonempty) ∧
      E.card + (E.image owner).card =
        ∑ v ∈ E.image owner, ((E.filter (fun e => owner e = v)).card + 1) := by
  classical
  let owner : Fin p × Fin l → Fin (p + l) :=
    fun e => if pointServes e then Fin.castAdd l e.1 else Fin.natAdd p e.2
  have ho : ∀ e ∈ E,
      (owner e = Fin.castAdd l e.1 ∧ pointServes e) ∨
      (owner e = Fin.natAdd p e.2 ∧ lineServes e) := by
    intro e he
    by_cases hs : pointServes e
    · exact Or.inl ⟨by simp [owner, hs], hs⟩
    · exact Or.inr ⟨by simp [owner, hs], (hserve e he).resolve_left hs⟩
  refine ⟨owner, ho, ?_, ?_, ?_⟩
  · intro a b he
    have hm : owner (a,b) ∈ E.image owner := Finset.mem_image.mpr ⟨(a,b), he, rfl⟩
    rcases ho (a,b) he with ⟨hh, _⟩ | ⟨hh, _⟩
    · exact Or.inl (hh ▸ hm)
    · exact Or.inr (hh ▸ hm)
  · intro v hv
    obtain ⟨e, he, hev⟩ := Finset.mem_image.mp hv
    exact ⟨e, Finset.mem_filter.mpr ⟨he, hev⟩⟩
  · have hcard := Finset.card_eq_sum_card_image owner E
    rw [Finset.sum_add_distrib]
    simpa only [Finset.sum_const_nat, Nat.mul_one] using
      congrArg (fun k => k + (E.image owner).card) hcard

end PEqualNP.Outside.L_meta_4970_aux
