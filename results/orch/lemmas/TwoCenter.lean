import Mathlib

namespace PEqualNP.Outside.L_meta_2448_aux

lemma twoCenter_guard_adjacent {α : Type*} [DecidableEq α] (G : SimpleGraph α)
    (noFour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (P Q : Finset α) (p q w : α) (hpq : G.Adj p q)
    (leftEdges : ∀ a ∈ P, G.Adj a q) (rightEdges : ∀ b ∈ Q, G.Adj p b)
    (largeP : 3 ≤ P.card) (hwq : w ≠ q)
    (guard : ∀ a ∈ P, ∀ b ∈ Q, G.Adj a b ∨ G.Adj a w ∨ G.Adj b w) :
    ∀ v ∈ Q, v ≠ q → G.Adj v w := by
  have largeP' : 1 < (P.erase p).card := by
    by_cases hp : p ∈ P
    · rw [Finset.card_erase_of_mem hp]
      omega
    · rw [Finset.erase_eq_of_notMem hp]
      omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp largeP'
  obtain ⟨hap, haP⟩ := Finset.mem_erase.mp ha
  obtain ⟨hbp, hbP⟩ := Finset.mem_erase.mp hb
  intro v hv hvq
  have cross {u : α} (hu : u ∈ P) (hup : u ≠ p) : ¬ G.Adj u v := by
    intro huv
    exact (noFour u q p v (leftEdges u hu) hpq.symm
      (rightEdges v hv) huv.symm).elim hup (Ne.symm hvq)
  have separate : ¬ (G.Adj a w ∧ G.Adj b w) := by
    rintro ⟨haw, hbw⟩
    exact (noFour a q b w (leftEdges a haP) (leftEdges b hbP).symm hbw haw.symm).elim
      hab (Ne.symm hwq)
  have hav := (guard a haP v hv).resolve_left (cross haP hap)
  have hbv := (guard b hbP v hv).resolve_left (cross hbP hbp)
  tauto

end PEqualNP.Outside.L_meta_2448_aux
