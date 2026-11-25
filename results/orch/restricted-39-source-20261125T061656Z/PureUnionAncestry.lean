import GuardCharging

namespace PEqualNP.Outside.L_meta_1896_aux.PureUnionAncestry

def Source {V : Type*} {k : Nat} (supports : Fin k → Finset V)
    (j : Fin k) (A : Finset V) : Prop :=
  A.card ≤ 1 ∨ ∃ i : Fin k, i.val < j.val ∧ supports i = A

def Scheme {V : Type*} [DecidableEq V] {k : Nat}
    (supports : Fin k → Finset V) : Prop :=
  ∀ j : Fin k, ∃ A B : Finset V,
    Source supports j A ∧ Source supports j B ∧ supports j = A ∪ B

def relevant {V : Type*} [DecidableEq V] {k : Nat}
    (supports : Fin k → Finset V) (target : Finset V) : Finset (Fin k) :=
  Finset.univ.filter fun j => 2 ≤ (supports j).card ∧ supports j ⊆ target

lemma source_large {V : Type*} {k : Nat} (supports : Fin k → Finset V)
    (j : Fin k) (A : Finset V) (hsource : Source supports j A) (hlarge : 2 ≤ A.card) :
    ∃ i : Fin k, i.val < j.val ∧ supports i = A := by
  rcases hsource with hsmall | hprior
  · omega
  · exact hprior

lemma large_predecessor {V : Type*} [DecidableEq V] {k : Nat}
    (supports : Fin k → Finset V) (scheme : Scheme supports)
    (j : Fin k) (hlarge : 3 ≤ (supports j).card) :
    ∃ i : Fin k, i.val < j.val ∧ 2 ≤ (supports i).card ∧ supports i ⊆ supports j := by
  obtain ⟨A, B, hA, hB, heq⟩ := scheme j
  have hcard := Finset.card_union_le A B
  rw [← heq] at hcard
  by_cases ha : 2 ≤ A.card
  · obtain ⟨i, hij, hi⟩ := source_large supports j A hA ha
    refine ⟨i, hij, ?_, ?_⟩
    · simpa [hi] using ha
    · rw [hi, heq]
      intro v hv
      exact Finset.mem_union.mpr (Or.inl hv)
  · have hb : 2 ≤ B.card := by omega
    obtain ⟨i, hij, hi⟩ := source_large supports j B hB hb
    refine ⟨i, hij, ?_, ?_⟩
    · simpa [hi] using hb
    · rw [hi, heq]
      intro v hv
      exact Finset.mem_union.mpr (Or.inr hv)

lemma three_members_card {J : Type*} [DecidableEq J]
    (M : Finset J) (a b c : J) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ M) (hb : b ∈ M) (hc : c ∈ M) : 3 ≤ M.card := by
  have hsub : ({a, b, c} : Finset J) ⊆ M := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hcard : ({a, b, c} : Finset J).card = 3 := by
    simp [hab, hac, hbc]
  have h := Finset.card_le_card hsub
  omega

lemma large_source_has_three_nodes {V : Type*} [DecidableEq V] {k : Nat}
    (supports : Fin k → Finset V) (scheme : Scheme supports)
    (j : Fin k) (A target : Finset V)
    (hsource : Source supports j A) (hlarge : 3 ≤ A.card)
    (hAsub : A ⊆ supports j) (hjcard : 2 ≤ (supports j).card)
    (hjsub : supports j ⊆ target) :
    3 ≤ (relevant supports target).card := by
  obtain ⟨i, hij, hi⟩ := source_large supports j A hsource (by omega)
  have hicard : 3 ≤ (supports i).card := by simpa [hi] using hlarge
  obtain ⟨a, hai, hacard, hasub⟩ := large_predecessor supports scheme i hicard
  have ha_ne_i : a ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have ha_ne_j : a ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have hi_ne_j : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have hisub : supports i ⊆ supports j := by simpa [hi] using hAsub
  apply three_members_card (relevant supports target) a i j ha_ne_i ha_ne_j hi_ne_j
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hacard, hasub.trans (hisub.trans hjsub)⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, by omega, hisub.trans hjsub⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjcard, hjsub⟩

lemma four_support_has_three_nodes {V : Type*} [DecidableEq V] {k : Nat}
    (supports : Fin k → Finset V) (scheme : Scheme supports)
    (j : Fin k) (hcard : 4 ≤ (supports j).card) :
    3 ≤ (relevant supports (supports j)).card := by
  obtain ⟨A, B, hA, hB, heq⟩ := scheme j
  have hAsub : A ⊆ supports j := by
    rw [heq]
    intro v hv
    exact Finset.mem_union.mpr (Or.inl hv)
  have hBsub : B ⊆ supports j := by
    rw [heq]
    intro v hv
    exact Finset.mem_union.mpr (Or.inr hv)
  by_cases ha : 3 ≤ A.card
  · exact large_source_has_three_nodes supports scheme j A (supports j)
      hA ha hAsub (by omega) (fun _ hv => hv)
  · by_cases hb : 3 ≤ B.card
    · exact large_source_has_three_nodes supports scheme j B (supports j)
        hB hb hBsub (by omega) (fun _ hv => hv)
    · have hsum := Finset.card_union_le A B
      rw [← heq] at hsum
      have ha2 : A.card = 2 := by omega
      have hb2 : B.card = 2 := by omega
      obtain ⟨i, hij, hi⟩ := source_large supports j A hA (by omega)
      obtain ⟨a, haj, haS⟩ := source_large supports j B hB (by omega)
      have hia : i ≠ a := by
        intro h
        have hab : A = B := hi.symm.trans ((congrArg supports h).trans haS)
        have hj : supports j = A := by simpa [hab] using heq
        rw [hj] at hcard
        omega
      have hij_ne : i ≠ j := by
        intro h
        have hv := congrArg Fin.val h
        omega
      have haj_ne : a ≠ j := by
        intro h
        have hv := congrArg Fin.val h
        omega
      apply three_members_card (relevant supports (supports j)) i a j hia hij_ne haj_ne
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ i, ?_, ?_⟩
        · simpa [hi] using (show 2 ≤ A.card by omega)
        · simpa [hi] using hAsub
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ a, ?_, ?_⟩
        · simpa [haS] using (show 2 ≤ B.card by omega)
        · simpa [haS] using hBsub
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, by omega, fun _ hv => hv⟩

lemma exact_pencil_ancestry {P V : Type*} [DecidableEq V] {k : Nat}
    (pencils : P → Finset V) (supports : Fin k → Finset V)
    (scheme : Scheme supports) (p : P) (hsize : (pencils p).card = 4)
    (hexact : ∃ j : Fin k, supports j = pencils p) :
    3 ≤ (GuardCharging.interior pencils supports p).card := by
  obtain ⟨j, hj⟩ := hexact
  have hc : 4 ≤ (supports j).card := by simp [hj, hsize]
  have h := four_support_has_three_nodes supports scheme j hc
  simpa only [relevant, GuardCharging.interior, hj] using h

end PEqualNP.Outside.L_meta_1896_aux.PureUnionAncestry
