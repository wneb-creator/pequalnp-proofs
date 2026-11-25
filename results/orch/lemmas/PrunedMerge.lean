import PrunedBridgeResolve

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem pruned_closed_live {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (u : Bool) (T : Sig) (depth : Nat)
    (rowCover : ∀ k S, Live u T k S → ∀ o ∈ need, ∃ v ∈ S, o ∈ col v)
    (closed : PrunedGateClosed roots raw col need Cert u T depth)
    {k : Nat} {S : Finset Sig} (run : Live u T k S) (cap : k + 1 ≤ S.card + depth)
    (label : Sig → Finset α) (part : LabelPartition roots S label)
    (traces : ∀ v ∈ S, ReadOnce raw u (label v) v)
    (supports : ∀ v ∈ S, ColumnSupport raw col (label v) v)
    (A B : Finset α) (a b : Sig) (d : Nat)
    (disjoint : Disjoint A B) (hd : allowed u d) (hab : a ≠ b)
    (hza : bin d a b ≠ a) (hzb : bin d a b ≠ b)
    (ca : Cert A a) (cb : Cert B b) (hz : bin d a b ∈ S)
    (labels : label (bin d a b) = A ∪ B) : Cert (A ∪ B) (bin d a b) := by
  have admissible := partition_admissible roots raw col need part supports
    (rowCover k S run) (bin d a b) hz
  rw [labels] at admissible
  rcases closed A B a b d disjoint hd hab hza hzb
    (live_all_proper run _ hz) ca cb admissible with found | cut
  · exact found
  · exfalso
    apply compressed_wire_forest_exclusion roots raw u T depth run cap
      label part traces (bin d a b) hz
    simpa only [labels] using cut

theorem pruned_merge_transfer {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (u : Bool) (T : Sig) (depth : Nat)
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (rowCover : ∀ k S, Live u T k S → ∀ o ∈ need, ∃ v ∈ S, o ∈ col v)
    (closed : PrunedGateClosed roots raw col need Cert u T depth)
    (U : Finset Sig) (a b : Sig) (d k : Nat) (label : Sig → Finset α)
    (hd : allowed u d) (hab : a ≠ b)
    (fresh : bin d a b ∉ insert a (insert b U)) (ha : a ∉ U) (hb : b ∉ U)
    (tail : Live u T k (insert (bin d a b) U))
    (cap : k + 1 ≤ (insert (bin d a b) U).card + depth)
    (part : LabelPartition roots (insert a (insert b U)) label)
    (entries : ∀ v ∈ insert a (insert b U), Cert (label v) v)
    (traces : ∀ v ∈ insert a (insert b U), ReadOnce raw u (label v) v)
    (supports : ∀ v ∈ insert a (insert b U), ColumnSupport raw col (label v) v) :
    ∃ next : Sig → Finset α,
      LabelPartition roots (insert (bin d a b) U) next ∧
      (∀ v ∈ insert (bin d a b) U, Cert (next v) v) ∧
      (∀ v ∈ insert (bin d a b) U, ReadOnce raw u (next v) v) ∧
      (∀ v ∈ insert (bin d a b) U, ColumnSupport raw col (next v) v) := by
  obtain ⟨next, pn, sn, nz, nu⟩ := merge_partition_frame roots raw col u gateCol
    U a b d hd hab fresh ha hb label part supports
  have ma : a ∈ insert a (insert b U) := by simp
  have mb : b ∈ insert a (insert b U) := by simp
  have disjoint := part.2.1 a ma b mb hab
  have tn : ∀ v ∈ insert (bin d a b) U, ReadOnce raw u (next v) v := by
    intro v hv
    rcases Finset.mem_insert.mp hv with eq | old
    · subst v
      rw [nz]
      exact ReadOnce.combine raw u (traces a ma) (traces b mb) disjoint d hd
    · rw [nu v old]
      exact traces v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem old))
  have za : bin d a b ≠ a := fun eq => fresh (by simp [eq])
  have zb : bin d a b ≠ b := fun eq => fresh (by simp [eq])
  have generated := pruned_closed_live roots raw col need Cert u T depth rowCover closed
    tail cap next pn tn sn (label a) (label b) a b d disjoint hd hab za zb
    (entries a ma) (entries b mb) (by simp) nz
  refine ⟨next, pn, ?_, tn, sn⟩
  intro v hv
  rcases Finset.mem_insert.mp hv with eq | old
  · subst v
    simpa only [nz] using generated
  · rw [nu v old]
    exact entries v (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem old))

end PEqualNP.Outside.L_meta_2373.Live1024
