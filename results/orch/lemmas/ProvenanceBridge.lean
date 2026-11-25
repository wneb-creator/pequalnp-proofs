import ProvenanceCut

namespace PEqualNP.Outside.L_meta_2373.Live1024

abbrev ProvenanceBridge {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (u : Bool) (T : Sig) (depth : Nat)
    (A : Finset α) (v : Sig) : Prop :=
  ColumnAdmissible roots raw col need A v →
    Cert A v ∨ BudgetRunCut (compressRoots roots A) (duplicateRaw raw v) u T depth

lemma provenance_bridge_leaf {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (u : Bool) (T : Sig) (depth : Nat)
    (initial : ∀ r ∈ roots, Cert {r} (raw r)) (r : α) (hr : r ∈ roots) :
    ProvenanceBridge roots raw col need Cert u T depth {r} (raw r) := by
  intro _
  exact Or.inl (initial r hr)

lemma provenance_bridge_combine {α Ω : Type} [DecidableEq α]
    (roots : Finset α) (raw : α → Sig) (col : Sig → Set Ω) (need : Set Ω)
    (Cert : Finset α → Sig → Prop) (u : Bool) (T : Sig) (depth : Nat)
    (closed : PrunedGateClosed roots raw col need Cert u T depth)
    {A B : Finset α} {a b : Sig} (subA : A ⊆ roots) (subB : B ⊆ roots)
    (disjoint : Disjoint A B) (leftTrace : ReadOnce raw u A a) (rightTrace : ReadOnce raw u B b)
    (leftSupport : ColumnSupport raw col A a) (rightSupport : ColumnSupport raw col B b)
    (d : Nat) (legal : allowed u d) (distinct : a ≠ b)
    (freshLeft : bin d a b ≠ a) (freshRight : bin d a b ≠ b) (properOut : proper (bin d a b))
    (gate : col (bin d a b) ⊆ col a ∪ col b)
    (leftBridge : ProvenanceBridge roots raw col need Cert u T depth A a)
    (rightBridge : ProvenanceBridge roots raw col need Cert u T depth B b) :
    ProvenanceBridge roots raw col need Cert u T depth (A ∪ B) (bin d a b) := by
  intro admissible
  have leftAdmissible := admissible_left_of_union roots raw col need subB disjoint
    gate rightSupport admissible
  have swappedGate : col (bin d a b) ⊆ col b ∪ col a := by
    simpa only [Set.union_comm] using gate
  have swappedAdmissible : ColumnAdmissible roots raw col need (B ∪ A) (bin d a b) := by
    simpa only [Finset.union_comm] using admissible
  have rightAdmissible := admissible_left_of_union roots raw col need subA disjoint.symm
    swappedGate leftSupport swappedAdmissible
  rcases leftBridge leftAdmissible with leftEntry | leftCut
  · rcases rightBridge rightAdmissible with rightEntry | rightCut
    · exact closed A B a b d disjoint legal distinct freshLeft freshRight properOut
        leftEntry rightEntry admissible
    · exact Or.inr (compressed_cut_extend_right roots raw u T depth subA disjoint leftTrace
        d legal rightCut)
  · exact Or.inr (compressed_cut_extend_left roots raw u T depth subB disjoint rightTrace
      d legal leftCut)

end PEqualNP.Outside.L_meta_2373.Live1024
