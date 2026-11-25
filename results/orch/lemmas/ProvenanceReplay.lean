import ProvenanceBridge

namespace PEqualNP.Outside.L_meta_2373.Live1024

theorem provenance_replay {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (u : Bool) (T : Sig) (depth : Nat)
    (initial : ∀ r ∈ roots, Cert {r} (raw r))
    (closed : PrunedGateClosed roots raw col need Cert u T depth)
    (gateCol : ∀ d a b, allowed u d → col (bin d a b) ⊆ col a ∪ col b)
    (P : Nat → Finset α → Sig → Prop)
    (steps : ∀ i A v, P i A v →
      (∃ r, A = {r} ∧ v = raw r) ∨
      ∃ j k B C b c d, j < i ∧ k < i ∧ P j B b ∧ P k C c ∧
        A = B ∪ C ∧ v = bin d b c ∧ Disjoint B C ∧ allowed u d ∧
        b ≠ c ∧ bin d b c ≠ b ∧ bin d b c ≠ c ∧ proper (bin d b c)) :
    ∀ i A v, P i A v → A ⊆ roots →
      ReadOnce raw u A v ∧ ColumnSupport raw col A v ∧
      ProvenanceBridge roots raw col need Cert u T depth A v := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro A v entry sub
    rcases steps i A v entry with leaf | binary
    · obtain ⟨r, rfl, rfl⟩ := leaf
      have hr : r ∈ roots := sub (Finset.mem_singleton_self r)
      refine ⟨ReadOnce.leaf raw u r, ?_, provenance_bridge_leaf roots raw col need Cert u T depth
        initial r hr⟩
      intro o ho
      exact ⟨r, Finset.mem_singleton_self r, ho⟩
    · obtain ⟨j, k, B, C, b, c, d, jlt, klt, left, right, rfl, rfl,
        disjoint, legal, distinct, freshLeft, freshRight, properOut⟩ := binary
      have subB : B ⊆ roots := fun r hr => sub (Finset.mem_union_left C hr)
      have subC : C ⊆ roots := fun r hr => sub (Finset.mem_union_right B hr)
      obtain ⟨leftTrace, leftSupport, leftBridge⟩ := ih j jlt B b left subB
      obtain ⟨rightTrace, rightSupport, rightBridge⟩ := ih k klt C c right subC
      have support : ColumnSupport raw col (B ∪ C) (bin d b c) := by
        intro o ho
        rcases gateCol d b c legal ho with hb | hc
        · obtain ⟨r, hr, covered⟩ := leftSupport o hb
          exact ⟨r, Finset.mem_union_left C hr, covered⟩
        · obtain ⟨r, hr, covered⟩ := rightSupport o hc
          exact ⟨r, Finset.mem_union_right B hr, covered⟩
      exact ⟨ReadOnce.combine raw u leftTrace rightTrace disjoint d legal, support,
        provenance_bridge_combine roots raw col need Cert u T depth closed subB subC disjoint
          leftTrace rightTrace leftSupport rightSupport d legal distinct freshLeft freshRight
          properOut (gateCol d b c legal) leftBridge rightBridge⟩

end PEqualNP.Outside.L_meta_2373.Live1024
