import PrunedDouble
import PrunedSingleTransfer

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem PrunedNode.initial {α Ω : Type} [DecidableEq α]
    {col : Sig → Set Ω} {need : Set Ω} {u : Bool} {T : Sig}
    {depth : Nat} {roots : Finset α} {raw : α → Sig} {Cert : Finset α → Sig → Prop}
    (node : PrunedNode col need u T depth α roots raw Cert) :
    ∀ r ∈ roots, Cert {r} (raw r) := by
  cases depth <;> exact node.1

theorem PrunedNode.closed {α Ω : Type} [DecidableEq α]
    {col : Sig → Set Ω} {need : Set Ω} {u : Bool} {T : Sig}
    {depth : Nat} {roots : Finset α} {raw : α → Sig} {Cert : Finset α → Sig → Prop}
    (node : PrunedNode col need u T depth α roots raw Cert) :
    PrunedGateClosed roots raw col need Cert u T depth := by
  cases depth <;> exact node.2.1

theorem PrunedNode.missing {α Ω : Type} [DecidableEq α]
    {col : Sig → Set Ω} {need : Set Ω} {u : Bool} {T : Sig}
    {depth : Nat} {roots : Finset α} {raw : α → Sig} {Cert : Finset α → Sig → Prop}
    (node : PrunedNode col need u T depth α roots raw Cert) : ¬ Cert roots T := by
  cases depth <;> exact node.2.2.1

theorem PrunedNode.copies {α Ω : Type} [DecidableEq α]
    {col : Sig → Set Ω} {need : Set Ω} {u : Bool} {T : Sig}
    {depth : Nat} {roots : Finset α} {raw : α → Sig} {Cert : Finset α → Sig → Prop}
    (node : PrunedNode col need u T (depth + 1) α roots raw Cert) :
    ∀ A w, A ⊆ roots → proper w → Cert A w →
      BudgetRunCut (duplicateRoots roots A) (duplicateRaw raw w) u T depth ∨
      ∃ Cert2 : Finset (Sum α Bool) → Sig → Prop,
        PrunedBridge roots raw col need Cert Cert2 u T depth A w ∧
        PrunedNode col need u T depth (Sum α Bool)
          (duplicateRoots roots A) (duplicateRaw raw w) Cert2 := node.2.2.2

theorem pruned_node_exclusion_state {Ω : Type}
    (col : Sig → Set Ω) (need : Set Ω) (u : Bool) (T : Sig)
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (rowCover : ∀ k S, Live u T k S → ∀ o ∈ need, ∃ v ∈ S, o ∈ col v)
    (k : Nat) :
    ∀ (α : Type) [DecidableEq α] (roots : Finset α) (raw : α → Sig)
      (Cert : Finset α → Sig → Prop) (depth : Nat),
      PrunedNode col need u T depth α roots raw Cert →
      ∀ (S : Finset Sig), Live u T k S → k + 1 ≤ S.card + depth →
      ∀ (label : Sig → Finset α), LabelPartition roots S label →
      (∀ v ∈ S, Cert (label v) v) →
      (∀ v ∈ S, ReadOnce raw u (label v) v) →
      (∀ v ∈ S, ColumnSupport raw col (label v) v) → False := by
  induction k with
  | zero =>
    intro α inst roots raw Cert depth node S run cap label part entries traces supports
    obtain ⟨rfl, hp⟩ := run
    have labels : label T = roots := by
      apply Finset.Subset.antisymm (part.1 T (by simp))
      intro r hr
      obtain ⟨v, hv, hrv⟩ := part.2.2 r hr
      have eq : v = T := by simpa using hv
      simpa only [eq] using hrv
    exact node.missing (labels ▸ entries T (by simp))
  | succ k ih =>
    intro α inst roots raw Cert depth node S run cap label part entries traces supports
    have retained : ∀ (U : Finset Sig) (a b : Sig) (d : Nat),
        allowed u d → proper a → proper b → a ≠ b →
        bin d a b ∉ insert a (insert b U) → a ∈ U →
        Live u T k (insert (bin d a b) U) →
        k + 2 ≤ (insert a (insert b U)).card + depth →
        LabelPartition roots (insert a (insert b U)) label →
        (∀ v ∈ insert a (insert b U), Cert (label v) v) →
        (∀ v ∈ insert a (insert b U), ReadOnce raw u (label v) v) →
        (∀ v ∈ insert a (insert b U), ColumnSupport raw col (label v) v) → False := by
      intro U a b d hd pa pb hab fresh ha tail cap part entries traces supports
      have notU : bin d a b ∉ U := fun h =>
        fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
      have ma : a ∈ insert a (insert b U) := by simp
      have mb : b ∈ insert a (insert b U) := by simp
      have oldEq : insert a (insert b U) = insert b U :=
        Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha)
      have bound := live_card_bound tail
      rw [Finset.card_insert_of_notMem notU] at bound
      have oldBound : (insert a (insert b U)).card ≤ U.card + 1 := by
        rw [oldEq]
        exact Finset.card_insert_le b U
      cases depth with
      | zero => omega
      | succ n =>
        have children := node.copies
        rcases children (label a) a (part.1 a ma) pa (entries a ma) with cut | next
        · by_cases hb : b ∈ U
          · have oldU : insert a (insert b U) = U := by simp [ha, hb]
            apply first_copy_forest_exclusion roots raw u T n tail hd ha hb notU
              (by rw [oldU] at cap; omega) label
              (by simpa only [oldU] using part)
              (by simpa only [oldU] using traces) cut
          · have pn := sharing_partition roots U a b (bin d a b) label hab fresh ha hb part
            have tn := sharing_readOnce raw u U a b d hd fresh label traces
            apply readOnce_forest_exclusion_state _ _ u T n cut tail ?_
              (sharingLabels label a b (bin d a b)) pn tn
            rw [Finset.card_insert_of_notMem notU]
            rw [oldEq, Finset.card_insert_of_notMem hb] at cap
            omega
        · obtain ⟨Cert2, bridge1, node2⟩ := next
          have lifted := pruned_bridge_live_copy roots raw col need Cert Cert2 u T n
            rowCover U a b d k label hd pa pb hab fresh ha tail cap part entries traces supports bridge1
          by_cases hb : b ∈ U
          · have oldU : insert a (insert b U) = U := by simp [ha, hb]
            rw [oldU] at cap
            cases n with
            | zero => omega
            | succ m =>
              have certB := lifted b mb hab.symm
              have subB : liftLabels (label b) ⊆ duplicateRoots roots (label a) :=
                liftLabels_subset_duplicate (part.1 b mb) (part.2.1 a ma b mb hab)
              rcases node2.copies (liftLabels (label b)) b subB pb certB with cut | next
              · have pn := double_sharing_partition roots U a b (bin d a b) label hab fresh ha hb part
                have tn := double_sharing_readOnce raw u U a b d hd fresh label traces
                apply readOnce_forest_exclusion_state _ _ u T m cut tail ?_
                  (doubleSharingLabels label a b (bin d a b)) pn tn
                rw [Finset.card_insert_of_notMem notU]
                omega
              · obtain ⟨Cert3, bridge2, node3⟩ := next
                have cap3 : k + 1 ≤ (insert (bin d a b) U).card + m := by
                  rw [Finset.card_insert_of_notMem notU]
                  omega
                obtain ⟨pn, en, tn, sn⟩ := pruned_double_transfer roots raw col need Cert2 Cert3
                  u T m gateCol rowCover U a b d k label hd hab fresh ha hb tail cap3
                  part lifted traces supports node3.initial node3.closed bridge2
                exact ih (Sum (Sum α Bool) Bool)
                  (duplicateRoots (duplicateRoots roots (label a)) (liftLabels (label b)))
                  (duplicateRaw (duplicateRaw raw a) b) Cert3 m node3 _ tail cap3
                  (doubleSharingLabels label a b (bin d a b)) pn en tn sn
          · have cap2 : k + 1 ≤ (insert (bin d a b) U).card + n := by
              rw [Finset.card_insert_of_notMem notU]
              rw [oldEq, Finset.card_insert_of_notMem hb] at cap
              omega
            obtain ⟨nextLabel, pn, en, tn, sn⟩ := pruned_single_transfer roots raw col need Cert Cert2
              u T n gateCol rowCover U a b d k label hd pa pb hab fresh ha hb tail cap2
              part entries traces supports bridge1 node2.initial node2.closed
            exact ih (Sum α Bool) (duplicateRoots roots (label a))
              (duplicateRaw raw a) Cert2 n node2 _ tail cap2
              nextLabel pn en tn sn
    obtain ⟨U, a, b, d, hd, rfl, pa, pb, hab, fresh, tail⟩ := run
    by_cases ha : a ∈ U
    · exact retained U a b d hd pa pb hab fresh ha tail cap part entries traces supports
    by_cases hb : b ∈ U
    · have swapped : bin (flipOp d) b a = bin d a b := (bin_flip hd a b).symm
      apply retained U b a (flipOp d) (flip_flip hd).1 pb pa hab.symm
        (by simpa only [swapped, Finset.insert_comm] using fresh) hb
        (by simpa only [swapped] using tail)
        (by simpa only [Finset.insert_comm] using cap)
        (by simpa only [Finset.insert_comm] using part)
        (by simpa only [Finset.insert_comm] using entries)
        (by simpa only [Finset.insert_comm] using traces)
        (by simpa only [Finset.insert_comm] using supports)
    · have notU : bin d a b ∉ U := fun h =>
        fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem h))
      have notB : a ∉ insert b U := by simp [hab, ha]
      have cap2 : k + 1 ≤ (insert (bin d a b) U).card + depth := by
        rw [Finset.card_insert_of_notMem notU]
        rw [Finset.card_insert_of_notMem notB, Finset.card_insert_of_notMem hb] at cap
        omega
      obtain ⟨next, pn, en, tn, sn⟩ := pruned_merge_transfer roots raw col need Cert
        u T depth gateCol rowCover node.closed U a b d k label hd hab fresh ha hb
        tail cap2 part entries traces supports
      exact ih α roots raw Cert depth node _ tail cap2 next pn en tn sn

end PEqualNP.Outside.L_meta_2373.Live1024
