import PackingThreeDefs

namespace PEqualNP.Outside.L_meta_1896_aux

namespace PackingThree

lemma and_zero_of_or_left (a b c : Nat) (h : (a ||| b) &&& c = 0) : a &&& c = 0 := by
  apply Nat.eq_of_testBit_eq
  intro i
  have hi := congrArg (fun n : Nat => n.testBit i) h
  rw [Nat.testBit_land, Nat.testBit_lor] at hi
  rw [Nat.testBit_land]
  cases ha : a.testBit i <;> cases hc : c.testBit i <;> simp_all

lemma ok_antitone (s : State) (b c : Block) (h : ok (step s b) c = true) :
    ok s c = true := by
  simp only [ok, step, Bool.and_eq_true, beq_iff_eq] at h ⊢
  exact ⟨and_zero_of_or_left _ _ _ h.1, and_zero_of_or_left _ _ _ h.2⟩

lemma flagCount_mono (a b : Nat)
    (h : ∀ i : Nat, a.testBit i = true → b.testBit i = true) : flagCount a ≤ flagCount b := by
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, h i.val (Finset.mem_filter.mp hi).2⟩

lemma edgeFold_testBit (mask : Nat) (bs : List Block) (i : Nat) :
    (bs.foldl (fun m b => m ||| b.edges) mask).testBit i = true ↔
      mask.testBit i = true ∨ ∃ b ∈ bs, b.edges.testBit i = true := by
  induction bs generalizing mask with
  | nil => simp
  | cons b bs ih =>
    simp [List.foldl_cons, ih, Nat.testBit_lor, Bool.or_eq_true, or_assoc]

lemma upperEdges_testBit (s : State) (bs : List Block) (i : Nat) :
    (upperEdges s bs).testBit i = true ↔
      s.covered.testBit i = true ∨ ∃ b ∈ bs, b.edges.testBit i = true :=
  edgeFold_testBit s.covered bs i

lemma upperEdges_sublist (s : State) (chosen candidates : List Block)
    (hsub : chosen.Sublist candidates) (i : Nat)
    (h : (upperEdges s chosen).testBit i = true) :
    (upperEdges s candidates).testBit i = true := by
  rw [upperEdges_testBit] at h ⊢
  rcases h with h | ⟨b, hb, he⟩
  · exact Or.inl h
  · exact Or.inr ⟨b, hsub.subset hb, he⟩

lemma fold_covered (s : State) (bs : List Block) :
    (bs.foldl step s).covered = upperEdges s bs := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih =>
    simpa [upperEdges, List.foldl_cons, step] using ih (step s b)

lemma fold_count (s : State) (bs : List Block) :
    (bs.foldl step s).count = s.count + bs.length := by
  induction bs generalizing s with
  | nil => simp
  | cons b bs ih =>
    simpa [List.foldl_cons, step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (step s b)

lemma prune_sound (s : State) (candidates chosen : List Block)
    (hsub : chosen.Sublist candidates) (hp : prune s candidates = true) :
    good (chosen.foldl step s) = true := by
  have hp : flagCount (upperEdges s candidates) ≤ 29 + s.count := of_decide_eq_true hp
  apply decide_eq_true
  change flagCount (chosen.foldl step s).covered ≤ 29 + (chosen.foldl step s).count
  rw [fold_covered, fold_count]
  have hm := flagCount_mono (upperEdges s chosen) (upperEdges s candidates)
    (upperEdges_sublist s chosen candidates hsub)
  omega

end PackingThree
end PEqualNP.Outside.L_meta_1896_aux
