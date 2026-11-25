import Mathlib

namespace PEqualNP.Outside.L_meta_4675.ReaderSemantics

def pointsOn {α β : Type*} (A : Finset α) (x : α ⊕ β → Bool) : Prop :=
  ∃ a ∈ A, x (Sum.inl a) = true

def linesOn {α β : Type*} (B : Finset β) (x : α ⊕ β → Bool) : Prop :=
  ∃ b ∈ B, x (Sum.inr b) = true

def graphValue {α β : Type*} (E : Finset (α × β)) (x : α ⊕ β → Bool) : Prop :=
  ∃ a b, (a, b) ∈ E ∧ x (Sum.inl a) = true ∧ x (Sum.inr b) = true

def readerValue {α β : Type*} (A Q : Finset α) (B P : Finset β)
    (x : α ⊕ β → Bool) : Prop :=
  (pointsOn A x ∧ linesOn B x ∨ linesOn P x) ∧ pointsOn Q x

def testInput {α β : Type*} [DecidableEq α] [DecidableEq β]
    (S : Finset α) (b : β) : α ⊕ β → Bool
  | Sum.inl a => decide (a ∈ S)
  | Sum.inr c => decide (c = b)

lemma graphValue_test {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (S : Finset α) (b : β) :
    graphValue E (testInput S b) ↔ ∃ a ∈ S, (a, b) ∈ E := by
  simp only [graphValue, testInput, decide_eq_true_eq]
  aesop

lemma reader_below_iff {α β : Type*} [DecidableEq α] [DecidableEq β]
    (E : Finset (α × β)) (A Q : Finset α) (B P : Finset β) :
    (∀ x, readerValue A Q B P x → graphValue E x) ↔
      (∀ q ∈ Q, ∀ b ∈ P, (q, b) ∈ E) ∧
      (∀ a ∈ A, ∀ b ∈ B, ∀ q ∈ Q, (a, b) ∈ E ∨ (q, b) ∈ E) := by
  constructor
  · intro h
    constructor
    · intro q hq b hb
      have hr : readerValue A Q B P (testInput {q} b) := by
        refine ⟨Or.inr ⟨b, hb, ?_⟩, q, hq, ?_⟩ <;> simp [testInput]
      obtain ⟨a, ha, hab⟩ := (graphValue_test E {q} b).mp (h _ hr)
      simpa only [Finset.mem_singleton.mp ha] using hab
    · intro a ha b hb q hq
      have hr : readerValue A Q B P (testInput {a, q} b) := by
        refine ⟨Or.inl ⟨⟨a, ha, ?_⟩, b, hb, ?_⟩, q, hq, ?_⟩ <;>
          simp [testInput]
      obtain ⟨c, hc, hcb⟩ := (graphValue_test E {a, q} b).mp (h _ hr)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hc
      rcases hc with hca | hcq
      · exact Or.inl (hca ▸ hcb)
      · exact Or.inr (hcq ▸ hcb)
  · rintro ⟨hbase, hprod⟩ x ⟨hg, q, hq, hxq⟩
    rcases hg with ⟨⟨a, ha, hxa⟩, b, hb, hxb⟩ | ⟨b, hb, hxb⟩
    · rcases hprod a ha b hb q hq with hab | hqb
      · exact ⟨a, b, hab, hxa, hxb⟩
      · exact ⟨q, b, hqb, hxq, hxb⟩
    · exact ⟨q, b, hbase q hq b hb, hxq, hxb⟩

lemma reader_pair_iff {α β : Type*} [DecidableEq α] [DecidableEq β]
    (A Q : Finset α) (B P : Finset β) (a : α) (b : β) :
    readerValue A Q B P (testInput {a} b) ↔
      a ∈ Q ∧ (b ∈ P ∨ a ∈ A ∧ b ∈ B) := by
  simp [readerValue, pointsOn, linesOn, testInput, and_comm, or_comm]

end PEqualNP.Outside.L_meta_4675.ReaderSemantics
