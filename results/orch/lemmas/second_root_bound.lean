import conjunction_bound

namespace PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma edge_or_ne_nonOr : ∀ (d : Fin 4) (a b : Fin 10), d.val ≠ 1 → a ≠ b →
    bin 1 (pins.getD 0 zero) (pins.getD 1 zero) ≠
      bin d.val (pins.getD a.val zero) (pins.getD b.val zero) := by
  decide +kernel

lemma second_root_nonOr_lower (d : Fin 4) (notOr : d.val ≠ 1)
    (a b : Fin 10) (hab : a ≠ b) {k S}
    (run : Live true target k S)
    (used : bin d.val (pins.getD a.val zero) (pins.getD b.val zero) ∈ S)
    (raw : ∀ v ∈ S, v ∈ pins ++
      [bin 1 (pins.getD 0 zero) (pins.getD 1 zero),
        bin d.val (pins.getD a.val zero) (pins.getD b.val zero)]) : 16 ≤ k := by
  classical
  let u := bin 1 (pins.getD 0 zero) (pins.getD 1 zero)
  let v := bin d.val (pins.getD a.val zero) (pins.getD b.val zero)
  have huv : u ≠ v := edge_or_ne_nonOr d a b notOr hab
  have pin0 : pins.getD 0 zero ∈ pins := by decide +kernel
  have pin1 : pins.getD 1 zero ∈ pins := by decide +kernel
  have u0 : u ≠ pins.getD 0 zero := by decide +kernel
  have u1 : u ≠ pins.getD 1 zero := by decide +kernel
  have reducedRaw : ∀ c ∈ S, c ≠ u → c ∈ pins ++ [v] := by
    intro c hc hcu
    have hh := raw c hc
    change c ∈ pins ++ [u,v] at hh
    simp only [List.mem_append,List.mem_cons,List.mem_singleton] at hh ⊢
    rcases hh with hp | hu | hv
    · exact Or.inl hp
    · exact False.elim (hcu hu)
    · exact Or.inr hv
  by_cases usedU : u ∈ S
  · let U := S.erase u
    have tail : Live true target k (insert u U) := by
      simpa only [U,Finset.insert_erase usedU] using run
    have proper0 : proper (pins.getD 0 zero) := by unfold proper; decide +kernel
    have proper1 : proper (pins.getD 1 zero) := by unfold proper; decide +kernel
    have distinct : pins.getD 0 zero ≠ pins.getD 1 zero := by decide +kernel
    have fresh : u ∉ insert (pins.getD 0 zero) (insert (pins.getD 1 zero) U) := by
      simp only [Finset.mem_insert]
      rintro (h | h | h)
      · exact u0 h
      · exact u1 h
      · exact (Finset.mem_erase.mp h).1 rfl
    have headRun := Live.binary (u:=true) (d:=1) (Or.inl (by decide))
      proper0 proper1 distinct fresh tail
    have headUsed : v ∈ insert (pins.getD 0 zero) (insert (pins.getD 1 zero) U) := by
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨huv.symm,used⟩))
    have headRaw : ∀ c ∈ insert (pins.getD 0 zero) (insert (pins.getD 1 zero) U),
        c ∈ pins ++ [v] := by
      intro c hc
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact List.mem_append_left _ pin0
      rcases Finset.mem_insert.mp hc with rfl | hc
      · exact List.mem_append_left _ pin1
      obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hc
      exact reducedRaw c hm hne
    have lower := conjunction_tail_lower d notOr a b hab headRun headUsed headRaw
    omega
  · have headRaw : ∀ c ∈ S, c ∈ pins ++ [v] := by
      intro c hc
      exact reducedRaw c hc (fun eq => usedU (eq ▸ hc))
    have lower := conjunction_tail_lower d notOr a b hab run used headRaw
    omega

end PEqualNP.Outside.L_meta_2592_aux.Stronger.Extended
