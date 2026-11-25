lemma commute_primary_live_step {u : Bool} {T : Extended.Sig} {k : ℕ}
    (R V : Finset Extended.Sig) (a b c d : Extended.Sig) (op1 op2 : ℕ)
    (hallowed : Extended.allowed u op1)
    (ha : Extended.proper a) (hb : Extended.proper b) (hab : a ≠ b)
    (haraw : a ∈ R) (hbraw : b ∈ R) (hcraw : c ∈ R) (hdraw : d ∈ R)
    (hfresh1 : Extended.bin op1 a b ∉ R)
    (hstate : insert c (insert d V) = insert (Extended.bin op1 a b) R)
    (hfresh2 : Extended.bin op2 c d ∉ insert (Extended.bin op1 a b) R)
    (tail : Extended.Live u T k (insert (Extended.bin op2 c d) V)) :
    ∃ U : Finset Extended.Sig,
      Extended.Live u T (k + 1) (insert (Extended.bin op2 c d) U) ∧ U ⊆ R := by
  let z1 := Extended.bin op1 a b
  let z2 := Extended.bin op2 c d
  have hzc : z1 ≠ c := by
    intro he
    apply hfresh1
    change z1 ∈ R
    rw [he]
    exact hcraw
  have hzd : z1 ≠ d := by
    intro he
    apply hfresh1
    change z1 ∈ R
    rw [he]
    exact hdraw
  have hzV : z1 ∈ V := by
    have hm : z1 ∈ insert c (insert d V) := by rw [hstate]; simp [z1]
    simpa only [Finset.mem_insert, hzc, hzd, false_or] using hm
  let W := V.erase z1
  have hW : W ⊆ R := by
    intro v hv
    obtain ⟨hne, hmem⟩ := Finset.mem_erase.mp hv
    have hm : v ∈ insert (Extended.bin op1 a b) R := by
      rw [← hstate]
      exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hmem)
    exact (Finset.mem_insert.mp hm).resolve_left hne
  have hz2 : z1 ≠ z2 := by
    intro he
    apply hfresh2
    change z2 ∈ insert z1 R
    rw [← he]
    exact Finset.mem_insert_self _ _
  have fresh : Extended.bin op1 a b ∉ insert a (insert b (insert z2 W)) := by
    intro hm
    rcases Finset.mem_insert.mp hm with he | hm
    · exact hfresh1 (he.symm ▸ haraw)
    rcases Finset.mem_insert.mp hm with he | hm
    · exact hfresh1 (he.symm ▸ hbraw)
    rcases Finset.mem_insert.mp hm with he | hm
    · exact hz2 he
    · exact hfresh1 (hW hm)
  have hafter : insert z1 (insert z2 W) = insert z2 V := by
    ext v
    by_cases h1 : v = z1 <;> by_cases h2 : v = z2 <;>
      simp_all [W]
  have tail' : Extended.Live u T k (insert (Extended.bin op1 a b) (insert z2 W)) := by
    rw [show insert (Extended.bin op1 a b) (insert z2 W) = insert z2 V from hafter]
    exact tail
  have swapped := Extended.Live.binary hallowed ha hb hab fresh tail'
  let U := insert a (insert b W)
  have heq : insert a (insert b (insert z2 W)) = insert z2 U := by
    ext v
    simp only [U, Finset.mem_insert]
    tauto
  refine ⟨U, ?_, ?_⟩
  · rw [← heq]
    exact swapped
  · intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact haraw
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hbraw
    exact hW hv
