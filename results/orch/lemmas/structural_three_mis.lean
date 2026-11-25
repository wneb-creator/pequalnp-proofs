import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto

namespace PEqualNP.Outside.L_meta_949_aux

lemma cover_from_three_sets {n : ℕ} (G : SimpleGraph (Fin n))
    (A B C : Finset (Fin n))
    (hindA : ∀ a ∈ A, ∀ b ∈ A, ¬ G.Adj a b)
    (hindB : ∀ a ∈ B, ∀ b ∈ B, ¬ G.Adj a b)
    (hindC : ∀ a ∈ C, ∀ b ∈ C, ¬ G.Adj a b)
    (hpairs : ∀ a b, ¬ G.Adj a b →
      (a ∈ A ∧ b ∈ A) ∨ (a ∈ B ∧ b ∈ B) ∨ (a ∈ C ∧ b ∈ C))
    (hmiss : ∀ a, a ∈ A → a ∈ B → a ∈ C) :
    ∃ X Y : Fin 2 → Finset (Fin n),
      (∀ i, ∀ a ∈ X i, ∀ b ∈ Y i, G.Adj a b) ∧
      (∀ a b, G.Adj a b → ∃ i,
        (a ∈ X i ∧ b ∈ Y i) ∨ (b ∈ X i ∧ a ∈ Y i)) := by
  classical
  let X : Fin 2 → Finset (Fin n) := fun i => if i = 0 then A \ (B ∪ C) else B \ C
  let Y : Fin 2 → Finset (Fin n) := fun i => if i = 0 then Finset.univ \ A else C \ B
  refine ⟨X, Y, ?_, ?_⟩
  · intro i a ha b hb
    by_contra hnot
    have hp := hpairs a b hnot
    fin_cases i
    · change a ∈ A \ (B ∪ C) at ha
      change b ∈ Finset.univ \ A at hb
      simp only [Finset.mem_sdiff, Finset.mem_union] at ha
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and] at hb
      rcases hp with hp | hp | hp
      · exact hb hp.2
      · exact ha.2 (Or.inl hp.1)
      · exact ha.2 (Or.inr hp.1)
    · change a ∈ B \ C at ha
      change b ∈ C \ B at hb
      simp only [Finset.mem_sdiff] at ha hb
      rcases hp with hp | hp | hp
      · exact ha.2 (hmiss a hp.1 ha.1)
      · exact hb.2 hp.2
      · exact ha.2 hp.1
  · intro a b hab
    have ha := hpairs a a G.irrefl
    have hb := hpairs b b G.irrefl
    have hAA : ¬ (a ∈ A ∧ b ∈ A) := fun h => hindA a h.1 b h.2 hab
    have hBB : ¬ (a ∈ B ∧ b ∈ B) := fun h => hindB a h.1 b h.2 hab
    have hCC : ¬ (a ∈ C ∧ b ∈ C) := fun h => hindC a h.1 b h.2 hab
    have hmA := hmiss a
    have hmB := hmiss b
    have hcases :
        ((a ∈ A ∧ ¬ (a ∈ B ∨ a ∈ C)) ∧ ¬ b ∈ A) ∨
        ((b ∈ A ∧ ¬ (b ∈ B ∨ b ∈ C)) ∧ ¬ a ∈ A) ∨
        ((a ∈ B ∧ ¬ a ∈ C) ∧ b ∈ C ∧ ¬ b ∈ B) ∨
        ((b ∈ B ∧ ¬ b ∈ C) ∧ a ∈ C ∧ ¬ a ∈ B) := by
      by_cases ha0 : a ∈ A ∧ ¬ (a ∈ B ∨ a ∈ C)
      · exact Or.inl ⟨ha0, fun h => hAA ⟨ha0.1, h⟩⟩
      by_cases hb0 : b ∈ A ∧ ¬ (b ∈ B ∨ b ∈ C)
      · exact Or.inr (Or.inl ⟨hb0, fun h => hAA ⟨h, hb0.1⟩⟩)
      have haBC : a ∈ B ∨ a ∈ C := by
        rcases ha with ha | ha | ha
        · by_contra hn
          exact ha0 ⟨ha.1, hn⟩
        · exact Or.inl ha.1
        · exact Or.inr ha.1
      have hbBC : b ∈ B ∨ b ∈ C := by
        rcases hb with hb | hb | hb
        · by_contra hn
          exact hb0 ⟨hb.1, hn⟩
        · exact Or.inl hb.1
        · exact Or.inr hb.1
      rcases haBC with haB | haC
      · have hnB : b ∉ B := fun h => hBB ⟨haB, h⟩
        have hbC := hbBC.resolve_left hnB
        have hnC : a ∉ C := fun h => hCC ⟨h, hbC⟩
        exact Or.inr (Or.inr (Or.inl ⟨⟨haB, hnC⟩, hbC, hnB⟩))
      · have hnC : b ∉ C := fun h => hCC ⟨haC, h⟩
        have hbB := hbBC.resolve_right hnC
        have hnB : a ∉ B := fun h => hBB ⟨h, hbB⟩
        exact Or.inr (Or.inr (Or.inr ⟨⟨hbB, hnC⟩, haC, hnB⟩))
    rcases hcases with h | h | h | h
    · exact ⟨0, Or.inl (by simpa [X, Y] using h)⟩
    · exact ⟨0, Or.inr (by simpa [X, Y] using h)⟩
    · exact ⟨1, Or.inl (by simpa [X, Y] using h)⟩
    · exact ⟨1, Or.inr (by simpa [X, Y] using h)⟩

lemma missing_pair_class {n : ℕ} (G : SimpleGraph (Fin n))
    (I : Fin 3 → Finset (Fin n))
    (hind : ∀ i, ∀ a ∈ I i, ∀ b ∈ I i, ¬ G.Adj a b)
    (hcover : ∀ S : Finset (Fin n),
      (∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b) → ∃ i, S ⊆ I i) :
    ∃ i, ∀ a, (∀ j, j ≠ i → a ∈ I j) → a ∈ I i := by
  classical
  by_contra h
  push_neg at h
  choose a ha hnot using h
  let S : Finset (Fin n) := Finset.univ.image a
  have hS : ∀ v ∈ S, ∀ w ∈ S, ¬ G.Adj v w := by
    intro v hv w hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨k, hki, hkj⟩ : ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by
      fin_cases i <;> fin_cases j <;> decide
    exact hind k (a i) (ha i k hki) (a j) (ha j k hkj)
  obtain ⟨i, hi⟩ := hcover S hS
  exact hnot i (hi (by simp [S]))

lemma biclique_cover_of_three_independent_sets {n : ℕ} (G : SimpleGraph (Fin n))
    (I : Fin 3 → Finset (Fin n))
    (hind : ∀ i, ∀ a ∈ I i, ∀ b ∈ I i, ¬ G.Adj a b)
    (hcover : ∀ S : Finset (Fin n),
      (∀ a ∈ S, ∀ b ∈ S, ¬ G.Adj a b) → ∃ i, S ⊆ I i) :
    ∃ X Y : Fin 2 → Finset (Fin n),
      (∀ i, ∀ a ∈ X i, ∀ b ∈ Y i, G.Adj a b) ∧
      (∀ a b, G.Adj a b → ∃ i,
        (a ∈ X i ∧ b ∈ Y i) ∨ (b ∈ X i ∧ a ∈ Y i)) := by
  classical
  have hpairs : ∀ a b, ¬ G.Adj a b → ∃ i, a ∈ I i ∧ b ∈ I i := by
    intro a b hab
    have hInd : ∀ v ∈ ({a, b} : Finset (Fin n)),
        ∀ w ∈ ({a, b} : Finset (Fin n)), ¬ G.Adj v w := by
      intro v hv w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv hw
      rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
      · exact G.irrefl
      · exact hab
      · exact fun h => hab h.symm
      · exact G.irrefl
    obtain ⟨i, hi⟩ := hcover {a, b} hInd
    exact ⟨i, hi (by simp), hi (by simp)⟩
  obtain ⟨i, hi⟩ := missing_pair_class G I hind hcover
  fin_cases i
  · apply cover_from_three_sets G (I 1) (I 2) (I 0) (hind 1) (hind 2) (hind 0)
    · intro a b hab
      obtain ⟨j, hj⟩ := hpairs a b hab
      fin_cases j <;> tauto
    · intro a ha hb
      apply hi a
      intro j hj
      fin_cases j <;> simp_all
  · apply cover_from_three_sets G (I 0) (I 2) (I 1) (hind 0) (hind 2) (hind 1)
    · intro a b hab
      obtain ⟨j, hj⟩ := hpairs a b hab
      fin_cases j <;> tauto
    · intro a ha hb
      apply hi a
      intro j hj
      fin_cases j <;> simp_all
  · apply cover_from_three_sets G (I 0) (I 1) (I 2) (hind 0) (hind 1) (hind 2)
    · intro a b hab
      obtain ⟨j, hj⟩ := hpairs a b hab
      fin_cases j <;> tauto
    · intro a ha hb
      apply hi a
      intro j hj
      fin_cases j <;> simp_all

end PEqualNP.Outside.L_meta_949_aux
