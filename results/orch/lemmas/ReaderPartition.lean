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

namespace PEqualNP.Outside.L_meta_4675.ReaderPartition

open PEqualNP.Outside.L_meta_4675.ReaderSemantics

def pointSide (p l : ℕ) (S : Finset (Fin (p+l))) : Finset (Fin p) :=
  Finset.univ.filter fun a => Fin.castAdd l a ∈ S

def lineSide (p l : ℕ) (S : Finset (Fin (p+l))) : Finset (Fin l) :=
  Finset.univ.filter fun b => Fin.natAdd p b ∈ S

def splitInput {p l : ℕ} (y : Fin p ⊕ Fin l → Bool) (u : Fin (p+l)) : Bool :=
  y (finSumFinEquiv.symm u)

lemma pointSide_on (p l : ℕ) (S : Finset (Fin (p+l)))
    (hs : ∀ u ∈ S, (u : ℕ) < p) (y : Fin p ⊕ Fin l → Bool) :
    (∃ u ∈ S, splitInput y u = true) ↔ pointsOn (pointSide p l S) y := by
  constructor
  · rintro ⟨u, hu, hxu⟩
    let a : Fin p := ⟨u.val, hs u hu⟩
    have he : Fin.castAdd l a = u := Fin.ext rfl
    refine ⟨a, ?_, ?_⟩
    · simpa [pointSide, he] using hu
    · rw [← he] at hxu
      simpa [splitInput] using hxu
  · rintro ⟨a, ha, hya⟩
    refine ⟨Fin.castAdd l a, ?_, ?_⟩
    · simpa [pointSide] using ha
    · simpa [splitInput] using hya

lemma lineSide_on (p l : ℕ) (S : Finset (Fin (p+l)))
    (hs : ∀ u ∈ S, p ≤ (u : ℕ)) (y : Fin p ⊕ Fin l → Bool) :
    (∃ u ∈ S, splitInput y u = true) ↔ linesOn (lineSide p l S) y := by
  constructor
  · rintro ⟨u, hu, hxu⟩
    have hup := hs u hu
    let b : Fin l := ⟨u.val-p, by have := u.isLt; omega⟩
    have he : Fin.natAdd p b = u := by
      apply Fin.ext
      change p + (u.val-p) = u.val
      omega
    refine ⟨b, ?_, ?_⟩
    · simpa [lineSide, he] using hu
    · rw [← he] at hxu
      simpa [splitInput] using hxu
  · rintro ⟨b, hb, hyb⟩
    refine ⟨Fin.natAdd p b, ?_, ?_⟩
    · simpa [lineSide] using hb
    · simpa [splitInput] using hyb

lemma reader_conditions (p l : ℕ) (E : Finset (Fin p × Fin l))
    (A Q B P : Finset (Fin (p+l)))
    (hA : ∀ u ∈ A, (u : ℕ) < p) (hQ : ∀ u ∈ Q, (u : ℕ) < p)
    (hB : ∀ u ∈ B, p ≤ (u : ℕ)) (hP : ∀ u ∈ P, p ≤ (u : ℕ))
    (hreader : ∀ x : Fin (p+l) → Bool,
      (((∃ a ∈ A, x a = true) ∧ (∃ b ∈ B, x b = true)) ∨
        (∃ b ∈ P, x b = true)) ∧ (∃ q ∈ Q, x q = true) →
      ∃ a b, (a,b) ∈ E ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true) :
    (∀ q ∈ pointSide p l Q, ∀ b ∈ lineSide p l P, (q,b) ∈ E) ∧
    (∀ a ∈ pointSide p l A, ∀ b ∈ lineSide p l B, ∀ q ∈ pointSide p l Q,
      (a,b) ∈ E ∨ (q,b) ∈ E) := by
  apply (reader_below_iff E (pointSide p l A) (pointSide p l Q)
    (lineSide p l B) (lineSide p l P)).mp
  intro y hy
  have hi : (((∃ a ∈ A, splitInput y a = true) ∧ (∃ b ∈ B, splitInput y b = true)) ∨
        (∃ b ∈ P, splitInput y b = true)) ∧ (∃ q ∈ Q, splitInput y q = true) := by
    rw [pointSide_on p l A hA, pointSide_on p l Q hQ,
      lineSide_on p l B hB, lineSide_on p l P hP]
    exact hy
  obtain ⟨a,b,hab,hxa,hxb⟩ := hreader (splitInput y) hi
  exact ⟨a,b,hab,by simpa [splitInput] using hxa,by simpa [splitInput] using hxb⟩

end PEqualNP.Outside.L_meta_4675.ReaderPartition
