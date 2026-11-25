import Mathlib

namespace PEqualNP.Outside.L_meta_4675.SameColourCharge

lemma same_colour_reader_family {p l : ℕ} {ι : Type*}
    (E : Finset (Fin p × Fin l))
    (hC4 : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (A B : Finset (Fin p)) (Q : ι → Finset (Fin l))
    (hI : 1 < (A ∩ B).card) (hne : ∃ r, (Q r).Nonempty)
    (hprod : ∀ r, ∀ a ∈ A, ∀ c ∈ B, ∀ q ∈ Q r,
      (a, q) ∈ E ∨ (c, q) ∈ E) :
    ∃ b : Fin l, (∀ r, Q r ⊆ {b}) ∧
      ((∀ a ∈ A, (a, b) ∈ E) ∨ (∀ c ∈ B, (c, b) ∈ E)) := by
  classical
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp hI
  obtain ⟨huA, huB⟩ := Finset.mem_inter.mp hu
  obtain ⟨hvA, hvB⟩ := Finset.mem_inter.mp hv
  obtain ⟨r0, b, hb⟩ := hne
  have hrowu : ∀ r, ∀ q ∈ Q r, (u, q) ∈ E := by
    intro r q hq
    exact (hprod r u huA u huB q hq).elim id id
  have hrowv : ∀ r, ∀ q ∈ Q r, (v, q) ∈ E := by
    intro r q hq
    exact (hprod r v hvA v hvB q hq).elim id id
  refine ⟨b, ?_, ?_⟩
  · intro r q hq
    apply Finset.mem_singleton.mpr
    by_contra hqb
    exact hC4 u v q b huv hqb
      ⟨hrowu r q hq, hrowu r0 b hb, hrowv r q hq, hrowv r0 b hb⟩
  · by_cases hA : ∀ a ∈ A, (a, b) ∈ E
    · exact Or.inl hA
    · push_neg at hA
      obtain ⟨a, ha, hbad⟩ := hA
      exact Or.inr (fun c hc => (hprod r0 a ha c hc b hb).resolve_left hbad)

end PEqualNP.Outside.L_meta_4675.SameColourCharge
