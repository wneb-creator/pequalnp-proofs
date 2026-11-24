import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1530

theorem core (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hno : ∀ s t w w' : Fin n, s ≠ t → w ≠ w' → G.Adj s w → G.Adj t w → G.Adj s w' →
      G.Adj t w' → False)
    (P Q W : Finset (Fin n))
    (hW : ∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) :
    (2 ≤ Q.card → (W ∩ P).card ≤ 1) ∧ (2 ≤ P.card → (W ∩ Q).card ≤ 1) ∧
    (∀ a b : Fin n, G.Adj a b → (a ∈ P ∨ b ∈ P) → (a ∈ Q ∨ b ∈ Q) → a ∈ W →
      (a ∈ P → b ∈ Q) ∧ (a ∈ Q → b ∈ P) ∧ (a ∉ P → a ∉ Q → b ∈ P ∩ Q)) ∧
    (∀ s, P ∩ Q = {s} → ∀ u, u ≠ s → ((Finset.univ.filter fun w => G.Adj u w) ∩ W).card ≤ 1) := by
  have kP : ∀ w ∈ W, w ∈ P → ∀ q ∈ Q, G.Adj w q := by
    intro w hw hwP q hq
    rcases (hW w).1 hw w hwP q hq with h | h | h
    · exact h
    · exact absurd h (G.loopless.irrefl w)
    · exact h.symm
  have kQ : ∀ w ∈ W, w ∈ Q → ∀ p ∈ P, G.Adj w p := by
    intro w hw hwQ p hp
    rcases (hW w).1 hw p hp w hwQ with h | h | h
    · exact h.symm
    · exact h.symm
    · exact absurd h (G.loopless.irrefl w)
  have h3 : ∀ s ∈ P ∩ Q, ∀ w ∈ W, G.Adj s w := by
    intro s hs w hw
    obtain ⟨hsP, hsQ⟩ := Finset.mem_inter.1 hs
    rcases (hW w).1 hw s hsP s hsQ with h | h | h
    · exact absurd h (G.loopless.irrefl s)
    · exact h
    · exact h
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h2
    obtain ⟨q, hq, q', hq', hqq⟩ := Finset.one_lt_card.1 h2
    apply Finset.card_le_one.2
    intro w hw w' hw'
    rw [Finset.mem_inter] at hw hw'
    by_contra hne
    exact hno w w' q q' hne hqq (kP w hw.1 hw.2 q hq) (kP w' hw'.1 hw'.2 q hq)
      (kP w hw.1 hw.2 q' hq') (kP w' hw'.1 hw'.2 q' hq')
  · intro h2
    obtain ⟨p, hp, p', hp', hpp⟩ := Finset.one_lt_card.1 h2
    apply Finset.card_le_one.2
    intro w hw w' hw'
    rw [Finset.mem_inter] at hw hw'
    by_contra hne
    exact hno w w' p p' hne hpp (kQ w hw.1 hw.2 p hp) (kQ w' hw'.1 hw'.2 p hp)
      (kQ w hw.1 hw.2 p' hp') (kQ w' hw'.1 hw'.2 p' hp')
  · intro a b _ hP hQ haW
    have nPQ : a ∈ P → a ∉ Q := fun haP haQ => G.loopless.irrefl a (kP a haW haP a haQ)
    refine ⟨fun haP => ?_, fun haQ => ?_, fun haP haQ => ?_⟩
    · rcases hQ with h | h
      · exact absurd h (nPQ haP)
      · exact h
    · rcases hP with h | h
      · exact absurd haQ (nPQ h)
      · exact h
    · rcases hP with h | h
      · exact absurd h haP
      · rcases hQ with h' | h'
        · exact absurd h' haQ
        · exact Finset.mem_inter.2 ⟨h, h'⟩
  · intro s hs u hus
    have hsm : s ∈ P ∩ Q := by rw [hs]; simp
    apply Finset.card_le_one.2
    intro w hw w' hw'
    simp only [Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and] at hw hw'
    by_contra hne
    exact hno s u w w' (Ne.symm hus) hne (h3 s hsm w hw.2) hw.1 (h3 s hsm w' hw'.2) hw'.1

end PEqualNP.Outside.L_meta_1530

theorem PEqualNP.Outside.L_meta_1530 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], PEqualNP.TopForm.NoFourCycle G → ∀ (P Q W : Finset (Fin n)),
    (∀ w, w ∈ W ↔ ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q ∨ G.Adj p w ∨ G.Adj q w) →
    (2 ≤ Q.card → (W ∩ P).card ≤ 1) ∧ (2 ≤ P.card → (W ∩ Q).card ≤ 1) ∧
    (∀ a b : Fin n, G.Adj a b → (a ∈ P ∨ b ∈ P) → (a ∈ Q ∨ b ∈ Q) → a ∈ W →
      (a ∈ P → b ∈ Q) ∧ (a ∈ Q → b ∈ P) ∧ (a ∉ P → a ∉ Q → b ∈ P ∩ Q)) ∧
    (∀ s, P ∩ Q = {s} → ∀ u, u ≠ s → ((Finset.univ.filter fun w => G.Adj u w) ∩ W).card ≤ 1) := by
  intro n G _ hnf P Q W hW
  have hno : ∀ s t w w' : Fin n, s ≠ t → w ≠ w' → G.Adj s w → G.Adj t w → G.Adj s w' →
      G.Adj t w' → False := by
    intro s t w w' hst hww h1 h2 h3 h4
    exact hww (Finset.card_le_one.1 (hnf s t hst) w (by simp [h1, h2]) w' (by simp [h3, h4]))
  exact PEqualNP.Outside.L_meta_1530.core n G hno P Q W hW
