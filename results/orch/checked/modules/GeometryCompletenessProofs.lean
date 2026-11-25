import GeometryMaskCore

namespace PEqualNP.Outside.L_meta_1896_aux.GeometryComplete

lemma classified_of_chunks (rowFor : Fin 8192 → AllRows.R)
    (h : ∀ g : Fin 64, ∀ i : Fin 128,
      let m : Fin 8192 := ⟨128 * g.val + i.val, by omega⟩
      AllRows.admissible (decode m) → AllRows.points (rowFor m) = decode m) :
    ∀ m : Fin 8192,
      AllRows.admissible (decode m) → AllRows.points (rowFor m) = decode m := by
  intro m
  have hm := h ⟨m.val / 128, by omega⟩ ⟨m.val % 128, Nat.mod_lt _ (by decide)⟩
  have heq : (⟨128 * (m.val / 128) + m.val % 128, by omega⟩ : Fin 8192) = m := by
    apply Fin.ext
    change 128 * (m.val / 128) + m.val % 128 = m.val
    omega
  simpa only [heq] using hm

lemma complete_of_classified (rowFor : Fin 8192 → AllRows.R)
    (classified : ∀ m : Fin 8192,
      AllRows.admissible (decode m) → AllRows.points (rowFor m) = decode m)
    (X : Finset (Fin 13)) (hX : AllRows.admissible X) :
    ∃ r : AllRows.R, AllRows.points r = X := by
  obtain ⟨m, hm⟩ := decode_surjective X
  refine ⟨rowFor m, ?_⟩
  have hc := classified m (hm.symm ▸ hX)
  exact hc.trans hm

end PEqualNP.Outside.L_meta_1896_aux.GeometryComplete
