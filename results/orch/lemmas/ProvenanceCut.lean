import ResidualPartition

namespace PEqualNP.Outside.L_meta_2373.Live1024

lemma compressed_bank_perm {α : Type} [DecidableEq α]
    (roots A : Finset α) (raw : α → Sig) (v : Sig) :
    ((compressRoots roots A).toList.map (fun r => observe (duplicateRaw raw v r))).Perm
      (observe v :: (roots \ A).toList.map (fun r => observe (raw r))) := by
  classical
  have labels : ((Sum.inr false : Sum α Bool) :: (roots \ A).toList.map Sum.inl).Perm
      (compressRoots roots A).toList := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · apply List.nodup_cons.mpr
      refine ⟨by simp, ?_⟩
      exact (Finset.nodup_toList _).map Sum.inl_injective
    · exact Finset.nodup_toList _
    · ext r
      simp [compressRoots, liftLabels, or_comm]
  have moved := labels.symm.map (fun r => observe (duplicateRaw raw v r))
  simpa only [List.map_cons, List.map_map, Function.comp_def, duplicateRaw,
    Sum.elim_inl, Sum.elim_inr] using moved

lemma compress_card {α : Type} [DecidableEq α] (roots A : Finset α) :
    (compressRoots roots A).card = (roots \ A).card + 1 := by
  have count := (compressed_bank_perm roots A (fun _ => zero) zero).length_eq
  simpa only [List.length_map, Finset.length_toList, List.length_cons] using count

lemma compressed_cut_extend_left {α : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (u : Bool) (T : Sig) (depth : Nat)
    {A B : Finset α} {a b : Sig} (subB : B ⊆ roots) (disjoint : Disjoint A B)
    (sibling : ReadOnce raw u B b) (d : Nat) (legal : allowed u d)
    (blocked : BudgetRunCut (compressRoots roots A) (duplicateRaw raw a) u T depth) :
    BudgetRunCut (compressRoots roots (A ∪ B)) (duplicateRaw raw (bin d a b)) u T depth := by
  intro k cap run
  have partition := residual_partition_perm roots A B subB disjoint
  have count : B.card + (roots \ (A ∪ B)).card = (roots \ A).card := by
    simpa only [List.length_append, Finset.length_toList] using partition.length_eq
  have parent := Run.perm (compressed_bank_perm roots (A ∪ B) raw (bin d a b)) run
  have built := Run.combine_traces (Run.stop (u := u) (goal := observe a)) sibling.2 d legal
  have siblingPositive := Finset.card_pos.mpr sibling.1
  have cost : 0 + (B.card - 1) + 1 = B.card := by omega
  have formula : Run u (observe (bin d a b)) B.card
      (observe a :: B.toList.map (fun r => observe (raw r))) := by
    simpa only [obs_bin, cost, List.singleton_append] using built
  have expanded := Run.substitute formula parent
  have moved : Run u (observe T) (B.card + k)
      (observe a :: (roots \ A).toList.map (fun r => observe (raw r))) := by
    have perm := List.Perm.cons (observe a) (partition.map (fun r => observe (raw r)))
    apply Run.perm perm
    simpa only [List.map_append, List.cons_append] using expanded
  have final := Run.perm (compressed_bank_perm roots A raw a).symm moved
  apply blocked (B.card + k) ?_ final
  rw [compress_card] at cap ⊢
  omega

lemma compressed_cut_extend_right {α : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (u : Bool) (T : Sig) (depth : Nat)
    {A B : Finset α} {a b : Sig} (subA : A ⊆ roots) (disjoint : Disjoint A B)
    (sibling : ReadOnce raw u A a) (d : Nat) (legal : allowed u d)
    (blocked : BudgetRunCut (compressRoots roots B) (duplicateRaw raw b) u T depth) :
    BudgetRunCut (compressRoots roots (A ∪ B)) (duplicateRaw raw (bin d a b)) u T depth := by
  have next := compressed_cut_extend_left roots raw u T depth subA disjoint.symm sibling
    (flipOp d) (flip_flip legal).1 blocked
  rw [Finset.union_comm B A, ← bin_flip legal a b] at next
  exact next

end PEqualNP.Outside.L_meta_2373.Live1024
