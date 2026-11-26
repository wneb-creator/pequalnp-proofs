import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17665_aux

private def edges11 : List (ℕ × ℕ) :=
  [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
   (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

private def edgesFin : List (Fin 11 × Fin 11) :=
  [(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7),
   (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)]

private def tbl : List ℕ :=
  [0, 0, 2, 4, 5, 7, 8, 9, 11, 12, 13, 14, 16, 17, 18, 19, 21]

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

private def minReq : List ℕ :=
  [6, 6, 5, 4, 4, 3, 3, 3, 2, 2, 2, 2, 1, 1, 1, 1, 0]

private lemma minReq_sound (u k : ℕ) (hu : u ≤ 16) (hk : k ≤ 16) (huk : u ≤ k) :
    5 + k ≤ minReq.getD u 0 + tbl.getD k 0 := by
  have h : (List.range 17).all (fun u =>
      (List.range 17).all (fun k =>
        !decide (u ≤ k) || decide (5 + k ≤ minReq.getD u 0 + tbl.getD k 0))) = true := by
    decide
  have h1 := List.all_eq_true.mp h u (List.mem_range.mpr (by omega))
  have h2 := List.all_eq_true.mp h1 k (List.mem_range.mpr (by omega))
  simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at h2
  exact h2.resolve_left (not_not.mpr huk)

private def checkMask (m : ℕ) : Bool :=
  decide (minReq.getD (uncov m) 0 ≤ pop11 m)

private lemma checkAll_true : allPow2 11 0 checkMask = true := by decide

private lemma checkMask_sound (m k : ℕ) (hm : m < 2048) (hk : k ≤ 16) (huk : uncov m ≤ k) :
    5 + k ≤ pop11 m + tbl.getD k 0 := by
  have h1 := allPow2_true 11 0 checkMask checkAll_true m (Nat.zero_le m) (by simpa using hm)
  have h2 : minReq.getD (uncov m) 0 ≤ pop11 m := of_decide_eq_true h1
  have h3 := minReq_sound (uncov m) k (by omega) hk huk
  omega

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

private lemma edgeFinset_subset_edgesFin (G : SimpleGraph (Fin 11)) [DecidableRel G.Adj]
    (hG : G = PEqualNP.EdgeOwnership.edgeGraph 11 edges11) :
    G.edgeFinset ⊆ (edgesFin.map fun p => s(p.1, p.2)).toFinset := by
  intro e he
  subst hG
  rw [SimpleGraph.mem_edgeFinset] at he
  induction e using Sym2.ind with
  | _ a b =>
    rw [SimpleGraph.mem_edgeSet] at he
    change a ≠ b ∧ ((a.val, b.val) ∈ edges11 ∨ (b.val, a.val) ∈ edges11) at he
    have hdec : ∀ (a b : Fin 11), ((a.val, b.val) ∈ edges11 ∨ (b.val, a.val) ∈ edges11) →
        s(a, b) ∈ edgesFin.map fun p => s(p.1, p.2) := by decide
    exact List.mem_toFinset.mpr (hdec a b he.2)

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

private lemma main (x1 : SimpleGraph (Fin 11)) [DecidableRel x1.Adj]
    (hx1 : x1 = PEqualNP.EdgeOwnership.edgeGraph 11 edges11)
    (x4 : Finset (Sym2 (Fin 11))) (hx4 : x4 ⊆ x1.edgeFinset)
    (x6 : Finset (Fin 11))
    (hcov : ∀ x7 x8 : Fin 11, (x1.deleteEdges ↑x4).Adj x7 x8 → x7 ∈ x6 ∨ x8 ∈ x6) :
    5 + x4.card ≤ x6.card + tbl.getD x4.card 0 := by
  have hx4_le : x4.card ≤ 16 := by
    have h1 := Finset.card_le_card (hx4.trans (edgeFinset_subset_edgesFin x1 hx1))
    have h2 : (edgesFin.map fun p => s(p.1, p.2)).toFinset.card = 16 := by decide
    omega
  subst hx1
  have huk := uncov_le_card x4 x6 hcov
  have hchk := checkMask_sound (maskOf x6) x4.card (maskOf_lt x6) hx4_le huk
  rwa [pop11_maskOf] at hchk

end PEqualNP.Outside.L_meta_17665_aux

theorem PEqualNP.Outside.L_meta_17665 : ∀ (x1 : SimpleGraph (Fin (11 : ℕ))) [x2 : DecidableRel x1.Adj], x1 = PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) [((0 : ℕ), (9 : ℕ)), ((0 : ℕ), (10 : ℕ)), ((1 : ℕ), (4 : ℕ)), ((1 : ℕ), (8 : ℕ)), ((2 : ℕ), (5 : ℕ)), ((2 : ℕ), (10 : ℕ)), ((3 : ℕ), (6 : ℕ)), ((3 : ℕ), (7 : ℕ)), ((4 : ℕ), (8 : ℕ)), ((4 : ℕ), (10 : ℕ)), ((5 : ℕ), (8 : ℕ)), ((5 : ℕ), (9 : ℕ)), ((6 : ℕ), (7 : ℕ)), ((6 : ℕ), (10 : ℕ)), ((7 : ℕ), (9 : ℕ)), ((8 : ℕ), (9 : ℕ))] → ∀ x4 ⊆ x1.edgeFinset, ∀ (x6 : Finset (Fin (11 : ℕ))), (x1.deleteEdges ↑x4).IsVertexCover ↑x6 → (5 : ℕ) + x4.card ≤ x6.card + [(0 : ℕ), (0 : ℕ), (2 : ℕ), (4 : ℕ), (5 : ℕ), (7 : ℕ), (8 : ℕ), (9 : ℕ), (11 : ℕ), (12 : ℕ), (13 : ℕ), (14 : ℕ), (16 : ℕ), (17 : ℕ), (18 : ℕ), (19 : ℕ), (21 : ℕ)].getD x4.card (0 : ℕ) := by
  intro G inst hG removed hsub vertices cover
  exact PEqualNP.Outside.L_meta_17665_aux.main G hG removed hsub vertices (fun _ _ h => cover h)
