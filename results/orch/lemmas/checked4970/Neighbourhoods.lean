import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux

def neighbours {p l : Nat} (E : Finset (Fin p × Fin l)) (v : Fin (p + l)) :
    Finset (Fin (p + l)) :=
  Fin.addCases
    (fun a => (Finset.univ.filter fun b => (a, b) ∈ E).image (Fin.natAdd p))
    (fun b => (Finset.univ.filter fun a => (a, b) ∈ E).image (Fin.castAdd l)) v

theorem neighbours_left {p l : Nat} (E : Finset (Fin p × Fin l)) (a : Fin p) :
    neighbours E (Fin.castAdd l a) =
      (Finset.univ.filter fun b => (a, b) ∈ E).image (Fin.natAdd p) := by
  simp [neighbours]

theorem neighbours_right {p l : Nat} (E : Finset (Fin p × Fin l)) (b : Fin l) :
    neighbours E (Fin.natAdd p b) =
      (Finset.univ.filter fun a => (a, b) ∈ E).image (Fin.castAdd l) := by
  simp [neighbours]

theorem left_right_ne {p l : Nat} (a : Fin p) (b : Fin l) :
    Fin.castAdd l a ≠ Fin.natAdd p b := by
  intro h
  have he := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at he
  omega

theorem neighbours_inter_card {p l : Nat} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (u v : Fin (p + l)) (hne : u ≠ v) :
    (neighbours E u ∩ neighbours E v).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro x hx y hy
  obtain ⟨hxu, hxv⟩ := Finset.mem_inter.mp hx
  obtain ⟨hyu, hyv⟩ := Finset.mem_inter.mp hy
  revert hne hxu hxv hyu hyv
  refine Fin.addCases (fun a => ?_) (fun b => ?_) u
  · refine Fin.addCases (fun a' => ?_) (fun b' => ?_) v
    · intro hne hxu hxv hyu hyv
      rw [neighbours_left] at hxu hxv hyu hyv
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hxu
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hyu
      obtain ⟨c', hc', hec⟩ := Finset.mem_image.mp hxv
      obtain ⟨d', hd', hed⟩ := Finset.mem_image.mp hyv
      have ec : c' = c := by
        apply Fin.ext
        have h := congrArg Fin.val hec
        simp only [Fin.val_natAdd] at h
        omega
      have ed : d' = d := by
        apply Fin.ext
        have h := congrArg Fin.val hed
        simp only [Fin.val_natAdd] at h
        omega
      subst c' d'
      have e : c = d := by
        by_contra hcd
        exact hfour a a' c d (fun h => hne (congrArg (Fin.castAdd l) h)) hcd
          ⟨(Finset.mem_filter.mp hc).2, (Finset.mem_filter.mp hd).2,
            (Finset.mem_filter.mp hc').2, (Finset.mem_filter.mp hd').2⟩
      exact congrArg (Fin.natAdd p) e
    · intro _ hxu hxv _ _
      rw [neighbours_left] at hxu
      rw [neighbours_right] at hxv
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hxu
      obtain ⟨d, -, hd⟩ := Finset.mem_image.mp hxv
      exact (left_right_ne d c hd).elim
  · refine Fin.addCases (fun a' => ?_) (fun b' => ?_) v
    · intro _ hxu hxv _ _
      rw [neighbours_right] at hxu
      rw [neighbours_left] at hxv
      obtain ⟨c, -, rfl⟩ := Finset.mem_image.mp hxu
      obtain ⟨d, -, hd⟩ := Finset.mem_image.mp hxv
      exact (left_right_ne c d hd.symm).elim
    · intro hne hxu hxv hyu hyv
      rw [neighbours_right] at hxu hxv hyu hyv
      obtain ⟨c, hc, rfl⟩ := Finset.mem_image.mp hxu
      obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp hyu
      obtain ⟨c', hc', hec⟩ := Finset.mem_image.mp hxv
      obtain ⟨d', hd', hed⟩ := Finset.mem_image.mp hyv
      have ec : c' = c := Fin.ext (congrArg (fun z : Fin (p + l) => z.val) hec)
      have ed : d' = d := Fin.ext (congrArg (fun z : Fin (p + l) => z.val) hed)
      subst c' d'
      have e : c = d := by
        by_contra hcd
        exact hfour c d b b' hcd (fun h => hne (congrArg (Fin.natAdd p) h))
          ⟨(Finset.mem_filter.mp hc).2, (Finset.mem_filter.mp hc').2,
            (Finset.mem_filter.mp hd).2, (Finset.mem_filter.mp hd').2⟩
      exact congrArg (Fin.castAdd l) e

end PEqualNP.Outside.L_meta_4970_aux
