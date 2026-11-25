import PEqualNP.Defs
import PEqualNP.Outside.L_meta_4970

set_option maxRecDepth 4096
set_option maxHeartbeats 1200000

namespace PEqualNP.Outside.L_meta_4970.Global

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open Semantics

lemma or_only_wire_pure (n : ℕ) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 n C)
    (hor : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or)
    (w : ℕ) (hw : w < n + C.gates.length) :
    ∃ S : Finset (Fin n), S.Nonempty ∧ ∀ x : Fin n → Bool,
      val C (List.ofFn x) w = decide (∃ i ∈ S, x i = true) := by
  classical
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hn : w < n
    · refine ⟨{⟨w, hn⟩}, Finset.singleton_nonempty _, ?_⟩
      intro x
      simp [val_ofFn_lt C x w hn]
    · let j := w - n
      have hj : j < C.gates.length := by omega
      have hwj : w = n + j := by omega
      have hlen := hC.2.2 (gateAt C j) (gateAt_mem hj)
      obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
      have ha : a < w := by
        rw [hwj]
        exact hC.2.1 j hj a (by simp [hab])
      have hb : b < w := by
        rw [hwj]
        exact hC.2.1 j hj b (by simp [hab])
      obtain ⟨A, hA, hFA⟩ := ih a ha (by omega)
      obtain ⟨B, hB, hFB⟩ := ih b hb (by omega)
      refine ⟨A ∪ B, hA.mono Finset.subset_union_left, ?_⟩
      intro x
      rw [hwj, or_val n C hC (List.ofFn x) (by simp) j hj (hor j hj)]
      simp only [hab, List.getD_cons_zero, List.getD_cons_succ, hFA, hFB]
      apply Bool.eq_iff_iff.mpr
      simp only [Bool.or_eq_true, decide_eq_true_eq, Finset.mem_union, or_and_right,
        exists_or]

lemma star_family_budget {p l : ℕ} {κ : Type} [Fintype κ]
    (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 (p + l) C)
    (centre : κ → Fin (p + l)) (leaves : κ → Finset (Fin (p + l)))
    (wire : κ → ℕ)
    (hne : ∀ k, (leaves k).Nonempty)
    (hsub : ∀ k, leaves k ⊆ neighbourSet E (centre k))
    (hpure : ∀ k x, val C (List.ofFn x) (wire k) =
      decide (∃ i ∈ leaves k, x i = true))
    (hcover : ∀ a b, (a, b) ∈ E → ∃ k,
      (centre k = Fin.castAdd l a ∧ Fin.natAdd p b ∈ leaves k) ∨
      (centre k = Fin.natAdd p b ∧ Fin.castAdd l a ∈ leaves k)) :
    E.card ≤ (eligibleOrBudget E C).card + Fintype.card κ := by
  classical
  let F : Fin (p + l) → Finset κ := fun c => Finset.univ.filter (centre · = c)
  let U : Fin (p + l) → Finset (Fin (p + l)) := fun c => (F c).biUnion leaves
  let repr : κ → Fin (p + l) := fun k => (hne k).choose
  have hrepr : ∀ k, repr k ∈ leaves k := fun k => (hne k).choose_spec
  let R : Fin (p + l) → Finset (Fin (p + l)) := fun c => (F c).image repr
  have hh := bipartite_family_ledger E hfour C hC F
    (fun _ k => leaves k) (fun _ k => wire k) (by
      intro c k hk
      have he : centre k = c := (Finset.mem_filter.mp hk).2
      simpa only [← he] using hsub k) (by
      intro c k hk x
      exact hpure k x) U R (by
      intro c u hu
      obtain ⟨k, hk, huk⟩ := Finset.mem_biUnion.mp hu
      refine ⟨repr k, Finset.mem_image.mpr ⟨k, hk, rfl⟩, ?_⟩
      exact Relation.EqvGen.rel _ _ ⟨k, hk, huk, hrepr k⟩) (by
      intro a b hab
      obtain ⟨k, hk⟩ := hcover a b hab
      rcases hk with ⟨hc, hl⟩ | ⟨hc, hl⟩
      · exact Or.inl (Finset.mem_biUnion.mpr ⟨k, by simp [F, hc], hl⟩)
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨k, by simp [F, hc], hl⟩))
  have hr : ∑ c, (R c).card ≤ Fintype.card κ := by
    calc
      ∑ c, (R c).card ≤ ∑ c, (F c).card :=
        Finset.sum_le_sum fun c _ => Finset.card_image_le
      _ = Fintype.card κ := by
        simpa [F] using Finset.sum_card_fiberwise_eq_card_filter
          (Finset.univ : Finset κ) (Finset.univ : Finset (Fin (p + l))) centre
  exact hh.trans (Nat.add_le_add_left hr _)

lemma star_pair_assignment_serves {p l : ℕ} (E : Finset (Fin p × Fin l))
    (c : Fin (p + l)) (Q : Finset (Fin (p + l)))
    (hsub : Q ⊆ neighbourSet E c) (a : Fin p) (b : Fin l)
    (hc : CleanRoots.pairAssignment (Fin.castAdd l a) (Fin.natAdd p b) c = true)
    (hq : ∃ i ∈ Q,
      CleanRoots.pairAssignment (Fin.castAdd l a) (Fin.natAdd p b) i = true) :
    (c = Fin.castAdd l a ∧ Fin.natAdd p b ∈ Q) ∨
    (c = Fin.natAdd p b ∧ Fin.castAdd l a ∈ Q) := by
  obtain ⟨v, hv, hxv⟩ := hq
  have hcv := (mem_neighbourSet E c v).mp (hsub hv)
  have hc' : c = Fin.castAdd l a ∨ c = Fin.natAdd p b := by
    simpa [CleanRoots.pairAssignment] using hc
  have hv' : v = Fin.castAdd l a ∨ v = Fin.natAdd p b := by
    simpa [CleanRoots.pairAssignment] using hxv
  rcases hc' with hc' | hc' <;> rcases hv' with hv' | hv'
  · rw [hc', hv'] at hcv
    exact (bipartiteRel_irrefl E _ hcv).elim
  · exact Or.inl ⟨hc', hv' ▸ hv⟩
  · exact Or.inr ⟨hc', hv' ▸ hv⟩
  · rw [hc', hv'] at hcv
    exact (bipartiteRel_irrefl E _ hcv).elim

lemma pure_sound_pair_star {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 (p + l) C)
    (u v : ℕ) (A B : Finset (Fin (p + l))) (hA : A.Nonempty) (hB : B.Nonempty)
    (hu : ∀ x, val C (List.ofFn x) u = decide (∃ i ∈ A, x i = true))
    (hv : ∀ x, val C (List.ofFn x) v = decide (∃ i ∈ B, x i = true))
    (hsound : ∀ x, val C (List.ofFn x) u = true → val C (List.ofFn x) v = true →
      bipartiteFun E x = true) :
    ∃ c Q w, Q.Nonempty ∧ Q ⊆ neighbourSet E c ∧
      (∀ x, val C (List.ofFn x) w = decide (∃ i ∈ Q, x i = true)) ∧
      ∀ x, val C (List.ofFn x) u = true → val C (List.ofFn x) v = true →
        x c = true ∧ ∃ i ∈ Q, x i = true := by
  classical
  have hshape := clean_and_support_star (bipartiteRel E) (bipartiteRel_irrefl E)
    (bipartiteRel_symm E) (bipartiteRel_no_four E hfour)
    (fun x => val C (List.ofFn x) u) (fun x => val C (List.ofFn x) v)
    (by intro x y hxy; exact mono (p + l) C hC.1 x y hxy u)
    (by intro x y hxy; exact mono (p + l) C hC.1 x y hxy v)
    (by
      intro x hxu hxv
      apply (bipartiteRel_witness_iff E x).mpr
      simpa [bipartiteFun] using hsound x hxu hxv)
    A B hA hB (by
      intro a ha
      rw [hu]
      simp only [decide_eq_true_eq]
      exact ⟨a, ha, by simp⟩) (by
      intro b hb
      rw [hv]
      simp only [decide_eq_true_eq]
      exact ⟨b, hb, by simp⟩)
  rcases hshape with ⟨a, ha, hab⟩ | ⟨b, hb, hab⟩
  · refine ⟨a, B, v, hB, ?_, hv, ?_⟩
    · intro b hb
      exact (mem_neighbourSet E a b).mpr (hab b hb)
    · intro x hxu hxv
      rw [hu, ha] at hxu
      rw [hv] at hxv
      exact ⟨by simpa using hxu, of_decide_eq_true hxv⟩
  · refine ⟨b, A, u, hA, ?_, hu, ?_⟩
    · intro a ha
      exact (mem_neighbourSet E b a).mpr (bipartiteRel_symm E a b (hab a ha))
    · intro x hxu hxv
      rw [hu] at hxu
      rw [hv, hb] at hxv
      exact ⟨by simpa using hxv, of_decide_eq_true hxu⟩

lemma or_only_pair_budget {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 (p + l) C)
    (hor : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or)
    (U : Finset (ℕ × ℕ))
    (hvalid : ∀ z ∈ U, z.1 < p + l + C.gates.length ∧
      z.2 < p + l + C.gates.length)
    (hsound : ∀ z ∈ U, ∀ x, val C (List.ofFn x) z.1 = true →
      val C (List.ofFn x) z.2 = true → bipartiteFun E x = true)
    (hcover : ∀ a b, (a, b) ∈ E → ∃ z ∈ U,
      val C (List.ofFn (CleanRoots.pairAssignment (Fin.castAdd l a) (Fin.natAdd p b)))
        z.1 = true ∧
      val C (List.ofFn (CleanRoots.pairAssignment (Fin.castAdd l a) (Fin.natAdd p b)))
        z.2 = true) :
    E.card ≤ (eligibleOrBudget E C).card + U.card ∧
    ∃ S : Finset (Fin (p + l)), S.card ≤ U.card ∧
      ∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S := by
  classical
  let κ := {z // z ∈ U}
  have hex : ∀ k : κ, ∃ c Q w, Q.Nonempty ∧ Q ⊆ neighbourSet E c ∧
      (∀ x, val C (List.ofFn x) w = decide (∃ i ∈ Q, x i = true)) ∧
      ∀ x, val C (List.ofFn x) k.val.1 = true → val C (List.ofFn x) k.val.2 = true →
        x c = true ∧ ∃ i ∈ Q, x i = true := by
    intro k
    obtain ⟨A, hA, hu⟩ := or_only_wire_pure (p + l) C hC hor k.val.1
      (hvalid k.val k.property).1
    obtain ⟨B, hB, hv⟩ := or_only_wire_pure (p + l) C hC hor k.val.2
      (hvalid k.val k.property).2
    exact pure_sound_pair_star E hfour C hC k.val.1 k.val.2 A B hA hB hu hv
      (hsound k.val k.property)
  choose centre leaves wire hne hsub hpure htruth using hex
  have hserve : ∀ a b, (a, b) ∈ E → ∃ k : κ,
      (centre k = Fin.castAdd l a ∧ Fin.natAdd p b ∈ leaves k) ∨
      (centre k = Fin.natAdd p b ∧ Fin.castAdd l a ∈ leaves k) := by
    intro a b hab
    obtain ⟨z, hz, hzu, hzv⟩ := hcover a b hab
    let k : κ := ⟨z, hz⟩
    have ht := htruth k _ hzu hzv
    exact ⟨k, star_pair_assignment_serves E (centre k) (leaves k) (hsub k) a b
      ht.1 ht.2⟩
  have hc : Fintype.card κ = U.card := Fintype.card_coe U
  constructor
  · simpa only [hc] using star_family_budget E hfour C hC centre leaves wire hne hsub
      hpure hserve
  · refine ⟨Finset.univ.image centre, ?_, ?_⟩
    · calc
        (Finset.univ.image centre).card ≤ (Finset.univ : Finset κ).card :=
          Finset.card_image_le
        _ = U.card := by simpa using hc
    · intro a b hab
      obtain ⟨k, hk⟩ := hserve a b hab
      rcases hk with ⟨hk, _⟩ | ⟨hk, _⟩
      · exact Or.inl (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩)
      · exact Or.inr (Finset.mem_image.mpr ⟨k, Finset.mem_univ _, hk⟩)

lemma or_only_pairs_lower_bound {p l : ℕ} (E : Finset (Fin p × Fin l))
    (hfour : ∀ (a a' : Fin p) (b b' : Fin l), a ≠ a' → b ≠ b' →
      ¬ ((a, b) ∈ E ∧ (a, b') ∈ E ∧ (a', b) ∈ E ∧ (a', b') ∈ E))
    (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 (p + l) C)
    (hor : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or)
    (U : Finset (ℕ × ℕ))
    (hvalid : ∀ z ∈ U, z.1 < p + l + C.gates.length ∧
      z.2 < p + l + C.gates.length)
    (hsound : ∀ z ∈ U, ∀ x, val C (List.ofFn x) z.1 = true →
      val C (List.ofFn x) z.2 = true → bipartiteFun E x = true)
    (hcover : ∀ a b, (a, b) ∈ E → ∃ z ∈ U,
      val C (List.ofFn (CleanRoots.pairAssignment (Fin.castAdd l a) (Fin.natAdd p b)))
        z.1 = true ∧
      val C (List.ofFn (CleanRoots.pairAssignment (Fin.castAdd l a) (Fin.natAdd p b)))
        z.2 = true)
    (s : ℕ) (hsize : C.size + 2 * U.card ≤ s + 1) :
    ∃ S : Finset (Fin (p + l)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd l a ∈ S ∨ Fin.natAdd p b ∈ S) ∧
      E.card + S.card ≤ s + 1 := by
  classical
  obtain ⟨he, S, hs, hS⟩ := or_only_pair_budget E hfour C hC hor U hvalid hsound hcover
  have hsub : eligibleGateBudget E C ⊆ Finset.range C.gates.length := by
    intro j hj
    exact Finset.mem_range.mpr (eligibleGateBudget_spec E C j hj).1
  have ha : (eligibleOrBudget E C).card ≤ C.size := by
    rw [← eligibleGateBudget_card E C]
    simpa only [Finset.card_range, Circuit.size] using Finset.card_le_card hsub
  exact ⟨S, hS, by omega⟩

end PEqualNP.Outside.L_meta_4970.Global
