import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17891_aux

private def edges11 : List (ℕ × ℕ) :=
  [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
   (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

private def edgesFin : List (Fin 11 × Fin 11) :=
  [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
   (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

private def pop11 (m : ℕ) : ℕ :=
  (List.finRange 11).countP fun i => m.testBit i.val

private def uncov (m : ℕ) : ℕ :=
  edgesFin.countP fun p => !m.testBit p.1.val && !m.testBit p.2.val

private def allPow2 : ℕ → ℕ → (ℕ → Bool) → Bool
  | 0, base, f => f base
  | k + 1, base, f => allPow2 k base f && allPow2 k (base + 2 ^ k) f

private lemma allPow2_true : ∀ k base (f : ℕ → Bool),
    allPow2 k base f = true → ∀ m, base ≤ m → m < base + 2 ^ k → f m = true := by
  intro k
  induction k with
  | zero =>
    intro base f hf m h1 h2
    have heq : m = base := by omega
    subst heq; exact hf
  | succ k ih =>
    intro base f hf m h1 h2
    simp only [allPow2, Bool.and_eq_true] at hf
    by_cases hlt : m < base + 2 ^ k
    · exact ih base f hf.1 m h1 hlt
    · exact ih (base + 2 ^ k) f hf.2 m (by omega) (by rw [Nat.pow_succ] at h2; omega)

private def maskOf (S : Finset (Fin 11)) : ℕ :=
  ∑ i ∈ S, 2 ^ i.val

private lemma sum_pow2_lt (n : ℕ) : ∀ (T : Finset ℕ), (∀ x ∈ T, x < n) → ∑ x ∈ T, 2 ^ x < 2 ^ n := by
  induction n with
  | zero =>
    intro T hT
    have hE : T = ∅ := Finset.eq_empty_of_forall_notMem fun x hx => Nat.not_lt_zero x (hT x hx)
    simp [hE]
  | succ n ih =>
    intro T hT
    by_cases hn : n ∈ T
    · have hsub : ∀ x ∈ T.erase n, x < n := by
        intro x hx
        have h1 := (Finset.mem_erase.mp hx).1
        have h2 := hT x (Finset.mem_erase.mp hx).2
        omega
      have h1 := ih (T.erase n) hsub
      have h2 := Finset.add_sum_erase T (fun x => 2 ^ x) hn
      rw [Nat.pow_succ]
      omega
    · have hsub : ∀ x ∈ T, x < n := by
        intro x hx
        have h2 := hT x hx
        have hne : x ≠ n := fun heq => hn (heq ▸ hx)
        omega
      have h1 := ih T hsub
      rw [Nat.pow_succ]
      omega

private lemma maskOf_lt (S : Finset (Fin 11)) : maskOf S < 2048 := by
  unfold maskOf
  have h1 : ∑ i ∈ S, 2 ^ i.val = ∑ x ∈ S.image Fin.val, 2 ^ x := by
    rw [Finset.sum_image (fun a _ b _ h => Fin.ext h)]
  rw [h1]
  have h2 := sum_pow2_lt 11 (S.image Fin.val) (fun x hx => by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hx; exact i.isLt)
  simpa using h2

private lemma testBit_add_of_disj : ∀ (k x y : ℕ),
    (∀ j, x.testBit j = true → y.testBit j = false) →
    (x + y).testBit k = (x.testBit k || y.testBit k) := by
  intro k
  induction k with
  | zero =>
    intro x y h
    have h0 := h 0
    simp only [Nat.testBit_zero, decide_eq_true_eq, decide_eq_false_iff_not] at h0 ⊢
    by_cases hx : x % 2 = 1
    · have hy : y % 2 ≠ 1 := h0 hx
      have hxy : (x + y) % 2 = 1 := by omega
      simp [hx, hxy]
    · by_cases hy : y % 2 = 1
      · have hxy : (x + y) % 2 = 1 := by omega
        simp [hx, hy, hxy]
      · have hxy : (x + y) % 2 ≠ 1 := by omega
        simp [hx, hy, hxy]
  | succ k ih =>
    intro x y h
    have h0 := h 0
    simp only [Nat.testBit_zero, decide_eq_true_eq, decide_eq_false_iff_not] at h0
    have hdiv : (x + y) / 2 = x / 2 + y / 2 := by omega
    rw [Nat.testBit_succ, hdiv, Nat.testBit_succ, Nat.testBit_succ]
    exact ih (x / 2) (y / 2) fun j hj => by
      have h1 := h (j + 1)
      rw [Nat.testBit_succ, Nat.testBit_succ] at h1
      exact h1 hj

private lemma testBit_sum_pow2 (T : Finset ℕ) : ∀ j : ℕ,
    (∑ x ∈ T, 2 ^ x).testBit j = decide (j ∈ T) := by
  induction T using Finset.induction_on with
  | empty => intro j; simp
  | insert a s ha ih =>
    intro j
    rw [Finset.sum_insert ha]
    have hdisj : ∀ k, (2 ^ a).testBit k = true → (∑ x ∈ s, 2 ^ x).testBit k = false := by
      intro k hk
      rw [Nat.testBit_two_pow] at hk
      simp only [decide_eq_true_eq] at hk
      subst hk
      rw [ih a]
      simp [ha]
    rw [testBit_add_of_disj j _ _ hdisj, Nat.testBit_two_pow, ih j]
    by_cases hja : a = j
    · subst hja; simp
    · simp [hja, Ne.symm hja]

private lemma maskOf_testBit (S : Finset (Fin 11)) (i : Fin 11) :
    (maskOf S).testBit i.val = decide (i ∈ S) := by
  unfold maskOf
  have h1 : ∑ j ∈ S, 2 ^ j.val = ∑ x ∈ S.image Fin.val, 2 ^ x := by
    rw [Finset.sum_image (fun a _ b _ h => Fin.ext h)]
  rw [h1, testBit_sum_pow2]
  simp only [Finset.mem_image]
  by_cases hi : i ∈ S
  · have hex : ∃ x ∈ S, x.val = i.val := ⟨i, hi, rfl⟩
    simp [hi, hex]
  · have hne : ¬ ∃ x ∈ S, x.val = i.val := by
      rintro ⟨x, hx, hxv⟩
      exact hi (Fin.ext hxv ▸ hx)
    simp [hi, hne]

private lemma pop11_maskOf (S : Finset (Fin 11)) : pop11 (maskOf S) = S.card := by
  unfold pop11
  have h1 : ((List.finRange 11).countP fun i => (maskOf S).testBit i.val) =
      ((List.finRange 11).filter fun i => decide (i ∈ S)).length := by
    rw [List.countP_eq_length_filter]
    congr 1
    exact List.filter_congr fun i _ => maskOf_testBit S i
  rw [h1]
  have hnd : ((List.finRange 11).filter fun i => decide (i ∈ S)).Nodup :=
    (List.nodup_finRange 11).filter _
  rw [← List.toFinset_card_of_nodup hnd]
  congr 1
  ext i
  simp

private lemma edgesFin_adj : ∀ p ∈ edgesFin,
    (PEqualNP.EdgeOwnership.edgeGraph 11 edges11).Adj p.1 p.2 := by
  have h : edgesFin.all (fun p => decide (p.1 ≠ p.2 ∧ ((p.1.val, p.2.val) ∈ edges11 ∨ (p.2.val, p.1.val) ∈ edges11))) = true := by
    decide
  intro p hp
  exact of_decide_eq_true (List.all_eq_true.mp h p hp)

private lemma edgesFin_sym_nodup : (edgesFin.map fun p => s(p.1, p.2)).Nodup := by
  decide

private lemma uncov_le_card (x4 : Finset (Sym2 (Fin 11))) (x6 : Finset (Fin 11))
    (hcov : ∀ u v : Fin 11,
      ((PEqualNP.EdgeOwnership.edgeGraph 11 edges11).deleteEdges ↑x4).Adj u v → u ∈ x6 ∨ v ∈ x6) :
    uncov (maskOf x6) ≤ x4.card := by
  unfold uncov
  rw [List.countP_eq_length_filter]
  let flt := edgesFin.filter fun p => !(maskOf x6).testBit p.1.val && !(maskOf x6).testBit p.2.val
  have hsub_map : flt.map (fun p => s(p.1, p.2)) ⊆ x4.toList := by
    intro e he
    rw [List.mem_map] at he
    rcases he with ⟨p, hp, rfl⟩
    simp only [flt, List.mem_filter, Bool.and_eq_true, Bool.not_eq_true'] at hp
    rcases hp with ⟨hp_mem, hp1, hp2⟩
    rw [maskOf_testBit] at hp1 hp2
    simp only [decide_eq_false_iff_not] at hp1 hp2
    rw [Finset.mem_toList]
    by_contra hnot
    have hadj : ((PEqualNP.EdgeOwnership.edgeGraph 11 edges11).deleteEdges ↑x4).Adj p.1 p.2 := by
      rw [SimpleGraph.deleteEdges_adj]
      exact ⟨edgesFin_adj p hp_mem, hnot⟩
    rcases hcov p.1 p.2 hadj with h1 | h2
    · exact hp1 h1
    · exact hp2 h2
  have hnd : (flt.map fun p => s(p.1, p.2)).Nodup :=
    edgesFin_sym_nodup.sublist ((List.filter_sublist).map _)
  have hlen : flt.length = (flt.map fun p => s(p.1, p.2)).toFinset.card := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [hlen]
  refine Finset.card_le_card fun e he => ?_
  have := hsub_map (List.mem_toFinset.mp he)
  rwa [Finset.mem_toList] at this

private def sufficient (m : Nat) : Bool := decide (7 ≤ pop11 m + uncov m)

private theorem exhaustive : allPow2 11 0 sufficient = true := by decide +kernel

end PEqualNP.Outside.L_meta_17891_aux

open PEqualNP.Outside.L_meta_17891_aux in
theorem PEqualNP.Outside.L_meta_17891 : have x1 : SimpleGraph (Fin (11 : ℕ)) := PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))]; ∀ (x2 : Finset (Sym2 (Fin (11 : ℕ)))) (x3 : Finset (Fin (11 : ℕ))), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover (x1.deleteEdges ↑x2) x3 → (7 : ℕ) ≤ x3.card + x2.card := by
  dsimp only
  intro removed vertices cover
  have bound := uncov_le_card removed vertices cover
  have h := allPow2_true _ _ _ exhaustive (maskOf vertices) (Nat.zero_le _) (maskOf_lt vertices)
  have score : 7 ≤ pop11 (maskOf vertices) + uncov (maskOf vertices) := of_decide_eq_true h
  rw [pop11_maskOf] at score
  omega
