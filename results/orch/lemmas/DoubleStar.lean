import Mathlib

namespace PEqualNP.Outside.L_meta_2448_aux

lemma doubleStar_guards {α : Type*} [DecidableEq α] (G : SimpleGraph α)
    (noFour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (P Q : Finset α) (p q w : α) (hp : p ∈ P) (hq : q ∈ Q)
    (leftEdges : ∀ a ∈ P, G.Adj a q) (rightEdges : ∀ b ∈ Q, G.Adj p b)
    (largeP : 3 ≤ P.card) (largeQ : 3 ≤ Q.card)
    (guard : ∀ a ∈ P, ∀ b ∈ Q, G.Adj a b ∨ G.Adj a w ∨ G.Adj b w) :
    w = p ∨ w = q := by
  by_contra hn
  obtain ⟨hwp, hwq⟩ := not_or.mp hn
  have largeP' : 1 < (P.erase p).card := by
    rw [Finset.card_erase_of_mem hp]
    omega
  have largeQ' : 1 < (Q.erase q).card := by
    rw [Finset.card_erase_of_mem hq]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp largeP'
  obtain ⟨c, hc, d, hd, hcd⟩ := Finset.one_lt_card.mp largeQ'
  obtain ⟨hap, haP⟩ := Finset.mem_erase.mp ha
  obtain ⟨hbp, hbP⟩ := Finset.mem_erase.mp hb
  obtain ⟨hcq, hcQ⟩ := Finset.mem_erase.mp hc
  obtain ⟨hdq, hdQ⟩ := Finset.mem_erase.mp hd
  have cross {u v : α} (hu : u ∈ P) (hv : v ∈ Q) (hup : u ≠ p) (hvq : v ≠ q) :
      ¬ G.Adj u v := by
    intro huv
    exact (noFour u q p v (leftEdges u hu) (leftEdges p hp).symm
      (rightEdges v hv) huv.symm).elim hup (Ne.symm hvq)
  have pSeparate : ¬ (G.Adj a w ∧ G.Adj b w) := by
    rintro ⟨haw, hbw⟩
    exact (noFour a q b w (leftEdges a haP) (leftEdges b hbP).symm hbw haw.symm).elim
      hab (Ne.symm hwq)
  have qSeparate : ¬ (G.Adj c w ∧ G.Adj d w) := by
    rintro ⟨hcw, hdw⟩
    exact (noFour c p d w (rightEdges c hcQ).symm (rightEdges d hdQ) hdw hcw.symm).elim
      hcd (Ne.symm hwp)
  have hac := (guard a haP c hcQ).resolve_left (cross haP hcQ hap hcq)
  have had := (guard a haP d hdQ).resolve_left (cross haP hdQ hap hdq)
  have hbc := (guard b hbP c hcQ).resolve_left (cross hbP hcQ hbp hcq)
  have hbd := (guard b hbP d hdQ).resolve_left (cross hbP hdQ hbp hdq)
  tauto

lemma doubleStar_guard_adjacent {α : Type*} [DecidableEq α] (G : SimpleGraph α)
    (noFour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (P Q : Finset α) (p q w : α) (hp : p ∈ P)
    (leftEdges : ∀ a ∈ P, G.Adj a q) (rightEdges : ∀ b ∈ Q, G.Adj p b)
    (largeP : 3 ≤ P.card) (hwq : w ≠ q)
    (guard : ∀ a ∈ P, ∀ b ∈ Q, G.Adj a b ∨ G.Adj a w ∨ G.Adj b w) :
    ∀ v ∈ Q, v ≠ q → G.Adj v w := by
  have largeP' : 1 < (P.erase p).card := by
    rw [Finset.card_erase_of_mem hp]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ := Finset.one_lt_card.mp largeP'
  obtain ⟨hap, haP⟩ := Finset.mem_erase.mp ha
  obtain ⟨hbp, hbP⟩ := Finset.mem_erase.mp hb
  intro v hv hvq
  have cross {u : α} (hu : u ∈ P) (hup : u ≠ p) : ¬ G.Adj u v := by
    intro huv
    exact (noFour u q p v (leftEdges u hu) (leftEdges p hp).symm
      (rightEdges v hv) huv.symm).elim hup (Ne.symm hvq)
  have separate : ¬ (G.Adj a w ∧ G.Adj b w) := by
    rintro ⟨haw, hbw⟩
    exact (noFour a q b w (leftEdges a haP) (leftEdges b hbP).symm hbw haw.symm).elim
      hab (Ne.symm hwq)
  have hav := (guard a haP v hv).resolve_left (cross haP hap)
  have hbv := (guard b hbP v hv).resolve_left (cross hbP hbp)
  tauto

end PEqualNP.Outside.L_meta_2448_aux
