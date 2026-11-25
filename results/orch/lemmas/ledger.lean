import Mathlib.Data.Finset.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace PEqualNP.Outside.L_meta_4970

lemma star_centre_unique {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} {Q : Finset (Fin l)} (hQ : 2 ≤ Q.card)
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ Q, (a', b) ∈ E) : a = a' := by
  by_cases h : a = a'
  · exact h
  · obtain ⟨b, hb, b', hb', hbb'⟩ := Finset.one_lt_card.mp
      (lt_of_lt_of_le (by decide : 1 < 2) hQ)
    exact False.elim (hE a a' b b' h hbb' ⟨ha b hb, ha b' hb', ha' b hb, ha' b' hb'⟩)

lemma distinct_centres_intersection_card {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hE : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    {a a' : Fin p} {Q Q' : Finset (Fin l)} (haa' : a ≠ a')
    (ha : ∀ b ∈ Q, (a, b) ∈ E) (ha' : ∀ b ∈ Q', (a', b) ∈ E) :
    (Q ∩ Q').card ≤ 1 := by
  by_cases h : (Q ∩ Q').card ≤ 1
  · exact h
  · have hQ : 2 ≤ (Q ∩ Q').card := Nat.lt_of_not_ge h
    exact False.elim (haa' (star_centre_unique E hE hQ
      (fun b hb => ha b (Finset.mem_inter.mp hb).1)
      (fun b hb => ha' b (Finset.mem_inter.mp hb).2)))

lemma or_function_determines_leaves {α : Type*} [DecidableEq α]
    (Q R : Finset α)
    (h : ∀ x : α → Bool, decide (∃ b ∈ Q, x b = true) =
      decide (∃ b ∈ R, x b = true)) : Q = R := by
  ext b
  have hb := h (fun a => decide (a = b))
  simpa using hb

lemma line_or_function_determines_leaves {p l : ℕ} (Q R : Finset (Fin l))
    (h : ∀ x : Fin (p + l) → Bool,
      decide (∃ b ∈ Q, x (Fin.natAdd p b) = true) =
        decide (∃ b ∈ R, x (Fin.natAdd p b) = true)) : Q = R := by
  apply or_function_determines_leaves
  intro x
  simpa using h (Fin.addCases (fun _ => false) x)

lemma point_or_function_determines_leaves {p l : ℕ} (P R : Finset (Fin p))
    (h : ∀ x : Fin (p + l) → Bool,
      decide (∃ a ∈ P, x (Fin.castAdd l a) = true) =
        decide (∃ a ∈ R, x (Fin.castAdd l a) = true)) : P = R := by
  apply or_function_determines_leaves
  intro x
  simpa using h (Fin.addCases x (fun _ => false))

lemma point_or_ne_line_or {p l : ℕ} (P : Finset (Fin p)) (Q : Finset (Fin l))
    (hP : P.Nonempty) :
    ¬ (∀ x : Fin (p + l) → Bool,
      decide (∃ a ∈ P, x (Fin.castAdd l a) = true) =
        decide (∃ b ∈ Q, x (Fin.natAdd p b) = true)) := by
  intro h
  have heq := h (Fin.addCases (fun _ => true) (fun _ => false))
  have hnot : ∀ a, a ∉ P := by simpa using heq
  obtain ⟨a, ha⟩ := hP
  exact hnot a ha

lemma star_family_cover_card {p l : ℕ} {ι : Type*} [DecidableEq ι]
    (E : Finset (Fin p × Fin l)) (I : Finset ι)
    (B : ι → Finset (Fin p × Fin l)) (c : ι → Fin (p + l))
    (hcover : ∀ e ∈ E, ∃ i ∈ I, e ∈ B i)
    (hstar : ∀ i ∈ I, ∀ e ∈ B i, Fin.castAdd l e.1 = c i ∨ Fin.natAdd p e.2 = c i) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      S.card ≤ I.card ∧ E.card ≤ ∑ i ∈ I, (B i).card := by
  refine ⟨I.image c, ?_, Finset.card_image_le, ?_⟩
  · intro a b hab
    obtain ⟨i, hi, hib⟩ := hcover (a, b) hab
    have hci : c i ∈ I.image c := Finset.mem_image_of_mem c hi
    rcases hstar i hi (a, b) hib with h | h
    · exact Or.inl (h ▸ hci)
    · exact Or.inr (h ▸ hci)
  · have hsub : E ⊆ I.biUnion B := by
      intro e he
      obtain ⟨i, hi, hib⟩ := hcover e he
      exact Finset.mem_biUnion.mpr ⟨i, hi, hib⟩
    exact (Finset.card_le_card hsub).trans Finset.card_biUnion_le

lemma star_family_ledger {p l s : ℕ} {ι : Type*} [DecidableEq ι]
    (E : Finset (Fin p × Fin l)) (I : Finset ι)
    (B : ι → Finset (Fin p × Fin l)) (c : ι → Fin (p + l))
    (hcover : ∀ e ∈ E, ∃ i ∈ I, e ∈ B i)
    (hstar : ∀ i ∈ I, ∀ e ∈ B i, Fin.castAdd l e.1 = c i ∨ Fin.natAdd p e.2 = c i)
    (hsize : (∑ i ∈ I, (B i).card) + I.card ≤ s + 1) :
    ∃ S : Finset (Fin (p + l)),
      (∀ (a : Fin p) (b : Fin l), (a, b) ∈ E →
        Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧ E.card + S.card ≤ s + 1 := by
  obtain ⟨S, hS, hScard, hEcard⟩ := star_family_cover_card E I B c hcover hstar
  exact ⟨S, hS, (Nat.add_le_add hEcard hScard).trans hsize⟩

end PEqualNP.Outside.L_meta_4970
