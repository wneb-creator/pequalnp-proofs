import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2584

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma exists_least_circuit (n : ℕ) (f : (Fin n → Bool) → Bool)
    (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hf : circuitFun n C = f) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = f ∧
      D.size ≤ C.size ∧
      ∀ E : Circuit, PEqualNP.TopForm.IsAO2 n E → circuitFun n E = f →
        D.size ≤ E.size := by
  classical
  let p : ℕ → Prop := fun s =>
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = f ∧ D.size = s
  have hp : ∃ s, p s := ⟨C.size, C, hC, hf, rfl⟩
  obtain ⟨D, hD, hDf, hsize⟩ := Nat.find_spec hp
  refine ⟨D, hD, hDf, ?_, ?_⟩
  · rw [hsize]
    exact Nat.find_min' hp ⟨C, hC, hf, rfl⟩
  · intro E hE hEf
    rw [hsize]
    exact Nat.find_min' hp ⟨E, hE, hEf, rfl⟩

lemma false_circuit_read (n k : ℕ) (C : Circuit)
    (hC : ∀ x : Fin n → Bool, circuitFun n C x = false) :
    PEqualNP.ReadK.IsReadK n C k := by
  intro S hS
  have htrue := hS.1
  rw [hC] at htrue
  cases htrue

lemma normalize_of_least_read (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hread : ∀ D : Circuit, PEqualNP.TopForm.IsAO2 n D → circuitFun n D = f →
      (∀ E : Circuit, PEqualNP.TopForm.IsAO2 n E → circuitFun n E = f →
        D.size ≤ E.size) → PEqualNP.ReadK.IsReadK n D 2)
    (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C)
    (hf : circuitFun n C = f) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ circuitFun n D = f ∧
      D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK n D 2 := by
  obtain ⟨D, hD, hDf, hsize, hleast⟩ := exists_least_circuit n f C hC hf
  exact ⟨D, hD, hDf, hsize, hread D hD hDf hleast⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

lemma point_ne_line {P L : ℕ} (p : Fin P) (l : Fin L) :
    Fin.castAdd L p ≠ Fin.natAdd P l := by
  intro h
  have hval := congrArg Fin.val h
  change p.val = P + l.val at hval
  omega

lemma incidence_pair_prime {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit)
    (hC : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true))
    {p : Fin P} {l : Fin L} (hi : I p l) :
    IsPrimeImplicant (P + L) C {Fin.castAdd L p, Fin.natAdd P l} := by
  classical
  constructor
  · rw [hC, decide_eq_true_eq]
    exact ⟨p, l, hi, by simp [setInput], by simp [setInput]⟩
  · intro T hT
    have hT' := Finset.mem_ssubsets.mp hT
    rw [hC, decide_eq_false_iff_not]
    rintro ⟨p', l', _, hp, hl⟩
    have hp' : Fin.castAdd L p' ∈ T := of_decide_eq_true hp
    have hl' : Fin.natAdd P l' ∈ T := of_decide_eq_true hl
    have pe : Fin.castAdd L p' = Fin.castAdd L p := by
      have := Finset.mem_insert.mp (hT'.subset hp')
      exact this.resolve_right (fun hm => point_ne_line p' l (Finset.mem_singleton.mp hm))
    have le : Fin.natAdd P l' = Fin.natAdd P l := by
      have := Finset.mem_insert.mp (hT'.subset hl')
      exact Finset.mem_singleton.mp (this.resolve_left (fun e => point_ne_line p l' e.symm))
    exact hT'.not_ge (by
      intro w hw
      rcases Finset.mem_insert.mp hw with rfl | hw
      · simpa only [pe] using hp'
      · rw [Finset.mem_singleton.mp hw, ← le]
        exact hl')

lemma incidence_prime_iff {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit)
    (hC : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true))
    (S : Finset (Fin (P + L))) :
    IsPrimeImplicant (P + L) C S ↔
      ∃ p : Fin P, ∃ l : Fin L, I p l ∧ S = {Fin.castAdd L p, Fin.natAdd P l} := by
  classical
  constructor
  · intro hS
    have hTrue := hS.1
    rw [hC, decide_eq_true_eq] at hTrue
    obtain ⟨p, l, hi, hp, hl⟩ := hTrue
    have hp' : Fin.castAdd L p ∈ S := of_decide_eq_true hp
    have hl' : Fin.natAdd P l ∈ S := of_decide_eq_true hl
    have hsub : ({Fin.castAdd L p, Fin.natAdd P l} : Finset (Fin (P + L))) ⊆ S := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw
      rcases hw with rfl | rfl
      · exact hp'
      · exact hl'
    refine ⟨p, l, hi, ?_⟩
    by_contra hne
    have hss : ({Fin.castAdd L p, Fin.natAdd P l} : Finset (Fin (P + L))) ⊂ S :=
      lt_of_le_of_ne hsub (Ne.symm hne)
    have hFalse := hS.2 _ (Finset.mem_ssubsets.mpr hss)
    have hPair := (incidence_pair_prime I C hC hi).1
    exact Bool.noConfusion (hPair.symm.trans hFalse)
  · rintro ⟨p, l, hi, rfl⟩
    exact incidence_pair_prime I C hC hi

lemma incidence_prime_card {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit)
    (hC : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true))
    (S : Finset (Fin (P + L))) (hS : IsPrimeImplicant (P + L) C S) : S.card = 2 := by
  obtain ⟨p, l, _, rfl⟩ := (incidence_prime_iff I C hC S).mp hS
  exact Finset.card_pair (point_ne_line p l)

lemma incidence_read_iff {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (C : Circuit)
    (hC : ∀ z : Fin (P + L) → Bool, circuitFun (P + L) C z =
      decide (∃ p : Fin P, ∃ l : Fin L, I p l ∧
        z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)) (k : ℕ) :
    IsReadK (P + L) C k ↔
      ∀ p : Fin P, ∀ l : Fin L, I p l →
        readsAtMost C (P + L) (setList {Fin.castAdd L p, Fin.natAdd P l}) k = true := by
  constructor
  · intro h p l hi
    exact h _ (incidence_pair_prime I C hC hi)
  · intro h S hS
    obtain ⟨p, l, hi, rfl⟩ := (incidence_prime_iff I C hC S).mp hS
    exact h p l hi

lemma incidence_biclique_star {P L : ℕ} (I : Fin P → Fin L → Prop)
    (h4 : ∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (A : Finset (Fin P)) (B : Finset (Fin L))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : ∀ p ∈ A, ∀ l ∈ B, I p l) : A.card = 1 ∨ B.card = 1 := by
  by_contra h
  obtain ⟨hAn, hBn⟩ := not_or.mp h
  have hAc : 1 < A.card := by have := Finset.card_pos.mpr hA; omega
  have hBc : 1 < B.card := by have := Finset.card_pos.mpr hB; omega
  obtain ⟨p, hp, p', hp', hpp⟩ := Finset.one_lt_card.mp hAc
  obtain ⟨l, hl, l', hl', hll⟩ := Finset.one_lt_card.mp hBc
  exact h4 p p' l l' hpp hll ⟨hAB p hp l hl, hAB p hp l' hl',
    hAB p' hp' l hl, hAB p' hp' l' hl'⟩

lemma incidence_biclique_cost {P L : ℕ} (I : Fin P → Fin L → Prop)
    (h4 : ∀ p p' : Fin P, ∀ l l' : Fin L, p ≠ p' → l ≠ l' →
      ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l'))
    (A : Finset (Fin P)) (B : Finset (Fin L))
    (hA : A.Nonempty) (hB : B.Nonempty)
    (hAB : ∀ p ∈ A, ∀ l ∈ B, I p l) :
    A.card * B.card = A.card + B.card - 1 := by
  rcases incidence_biclique_star I h4 A B hA hB hAB with h | h
  · rw [h]
    omega
  · rw [h]
    omega

end PEqualNP.Outside.L_meta_2584
