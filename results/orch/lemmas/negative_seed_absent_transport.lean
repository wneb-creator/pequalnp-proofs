import negative_seed_absent

namespace PEqualNP.Outside.L_meta_2592_aux.Stronger.NegativeSeedTransport

open Extended PEqualNP.Outside.L_meta_2592_aux.Subgraphs

lemma lower_seed_absent (p : Fin 10) {k S} (run : Extended.Live true Extended.target k S)
    (raw : ∀ a ∈ S, a ∈ originalBank p) (used : originalExtra p ∈ S) (absent : originalSeed ∉ S) : 17 ≤ k := by
  classical
  have needed := pin_needed p run raw
  let t := pairPerm p p
  let q := t.symm
  have tzero : t 0 = p := pairMap_zero p p
  have ht : ∀ a b, adjacent (t a) (t b) = adjacent a b := pairMap_adjacent p p
  have hqp : q p = 0 := by
    dsimp only [q]
    rw [←tzero,Equiv.symm_apply_apply]
  have hq : ∀ a b, adjacent (q a) (q b) = adjacent a b := by
    intro a b
    simpa only [q,Equiv.apply_symm_apply] using (ht (t.symm a) (t.symm b)).symm
  have seedRename : renameVertices q originalSeed = NegativeSeed.seed (q 0) (q 1) := by
    unfold originalSeed NegativeSeed.seed
    rw [renameVertices_bin]
    exact congrArg₂ (Extended.bin 1) (renameVertices_pin q 0) (renameVertices_pin q 1)
  have extraRename : renameVertices q (originalExtra p) = NegativeSeed.extra (q 0) (q 1) := by
    unfold originalExtra NegativeSeed.extra
    rw [renameVertices_bin,renameVertices_pin q p,seedRename,hqp]
    rfl
  have run' : Extended.Live true Extended.target k (S.image (renameVertices q)) := by
    simpa only [renameVertices_target q hq] using live_renameVertices run q
  have raw' : ∀ a ∈ S.image (renameVertices q), a ∈ Extended.pins ++ [NegativeSeed.extra (q 0) (q 1)] := by
    intro a ha
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ha
    have hh := raw v hv
    simp only [originalBank,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hh
    simp only [List.mem_append,List.mem_singleton]
    rcases hh with hp | rfl | rfl
    · exact Or.inl (renameVertices_mem_pins q hp)
    · exact (absent hv).elim
    · exact Or.inr extraRename
  have needed' : Extended.pins.getD 0 Extended.zero ∈ S.image (renameVertices q) := by
    refine Finset.mem_image.mpr ⟨Extended.pins.getD p.val Extended.zero,needed,?_⟩
    rw [renameVertices_pin q p,hqp]
    rfl
  have used' : NegativeSeed.extra (q 0) (q 1) ∈ S.image (renameVertices q) :=
    Finset.mem_image.mpr ⟨originalExtra p,used,extraRename⟩
  exact NegativeSeed.lower_without_seed (q 0) (q 1) run' raw' needed' used'


end PEqualNP.Outside.L_meta_2592_aux.Stronger.NegativeSeedTransport
