import DeepContinuationSplit

namespace PEqualNP.Outside.L_meta_10760_aux

def deepMaskPick (mask : ℕ) : ℕ → ℕ → ℕ → List W → Bool :=
  fun _ _ _ r => mask.testBit ((r.foldl (fun h w => h * 17 + w.s) 0) % 127)

lemma chkDeepSel_false_of_masks (masks : List ℕ) (hne : masks ≠ [])
    (cover : ∀ i : Fin 127, masks.any (fun mask => mask.testBit i.val) = true)
    (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ)
    (h : ∀ mask ∈ masks, chkDeepSel (deepMaskPick mask) E Q Z K t H ph = false) :
    chk E Q Z K t H ph = false := by
  apply chkDeepSel_false_of_cover (masks.map deepMaskPick)
  · simpa using hne
  · intro k t z r
    rw [List.any_map]
    change masks.any (fun mask =>
      mask.testBit ((r.foldl (fun h w => h * 17 + w.s) 0) % 127)) = true
    exact cover ⟨(r.foldl (fun h w => h * 17 + w.s) 0) % 127,
      Nat.mod_lt _ (by decide)⟩
  · intro p hp
    obtain ⟨mask, hm, rfl⟩ := List.mem_map.mp hp
    exact h mask hm

lemma chkDeepSel_false_of_mask_indices (masks : List ℕ) (hne : masks ≠ [])
    (cover : ∀ i : Fin 127, masks.any (fun mask => mask.testBit i.val) = true)
    (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ)
    (h : ∀ i : Fin masks.length,
      chkDeepSel (deepMaskPick (masks.get i)) E Q Z K t H ph = false) :
    chk E Q Z K t H ph = false := by
  apply chkDeepSel_false_of_masks masks hne cover E Q Z K t H ph
  intro mask hm
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hm
  exact h ⟨i, hi⟩

end PEqualNP.Outside.L_meta_10760_aux
