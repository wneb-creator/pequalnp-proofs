namespace PEqualNP.Outside.L_meta_6659_aux

theorem ke_p4_mask_certificate : ∀ M : Fin 4 → Finset (Fin 3),
    (∀ x, (M x).Nonempty) →
    ∃ t : Fin 4, 2 + (M t).card <
      (Finset.univ.filter (fun e : Fin 6 =>
        ∃ x : Fin 4,
          k4_Adj (Fin.castLE (by decide : 4 ≤ 10) x) (Fin.natAdd 4 e) ∧
          M x ⊆ M t)).card := by
  decide +kernel

theorem ke_p5_mask_certificate : ∀ omitted : Fin 6,
    ∀ M : Fin 4 → Finset (Fin 3),
    (∀ x, (M x).Nonempty) →
    (Finset.univ.biUnion M).card ≤ 2 →
    ∃ t : Fin 4, 2 + (M t).card <
      (Finset.univ.filter (fun e : Fin 6 =>
        e ≠ omitted ∧ ∃ x : Fin 4,
          k4_Adj (Fin.castLE (by decide : 4 ≤ 10) x) (Fin.natAdd 4 e) ∧
          M x ⊆ M t)).card := by
  decide +kernel

end PEqualNP.Outside.L_meta_6659_aux
