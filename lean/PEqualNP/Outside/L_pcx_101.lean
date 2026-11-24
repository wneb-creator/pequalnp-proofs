import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_pcx_101

open PEqualNP.ProofComplexity

-- A clause has a derivation of width at most k from F.
def Der {V : Type} [DecidableEq V] (F : Set (Clause V)) (k : ℕ) (C : Clause V) : Prop :=
  ∃ π, IsDerivation F π ∧ C ∈ π ∧ ∀ D ∈ π, D.card ≤ k

theorem append {V : Type} [DecidableEq V] {F : Set (Clause V)} {π1 π2 : List (Clause V)}
    (h1 : IsDerivation F π1) (h2 : IsDerivation F π2) : IsDerivation F (π1 ++ π2) := by
  induction h1 with
  | nil => simpa using h2
  | ax _ hC ih => exact IsDerivation.ax ih hC
  | res _ hC hD hR ih =>
    exact IsDerivation.res ih (List.mem_append_left _ hC) (List.mem_append_left _ hD) hR

theorem der_ax {V : Type} [DecidableEq V] {F : Set (Clause V)} {k : ℕ} {C : Clause V}
    (hC : C ∈ F) (hk : C.card ≤ k) : Der F k C :=
  ⟨[C], IsDerivation.ax IsDerivation.nil hC, by simp, by simpa using hk⟩

theorem der_res {V : Type} [DecidableEq V] {F : Set (Clause V)} {k : ℕ} {C D R : Clause V}
    (hC : Der F k C) (hD : Der F k D) (hR : IsResolvent C D R) (hk : R.card ≤ k) :
    Der F k R := by
  obtain ⟨π1, d1, m1, w1⟩ := hC
  obtain ⟨π2, d2, m2, w2⟩ := hD
  refine ⟨R :: (π1 ++ π2), IsDerivation.res (append d1 d2) (List.mem_append_left _ m1)
    (List.mem_append_right _ m2) hR, by simp, ?_⟩
  intro X hX
  rcases List.mem_cons.mp hX with rfl | hX
  · exact hk
  · rcases List.mem_append.mp hX with h | h
    · exact w1 _ h
    · exact w2 _ h

-- Branching on an uncovered edge: the negative clause of every set of at most k vertices
-- is derivable in width k.
theorem upper {V : Type} [DecidableEq V] (F : Set (Clause V)) (E : List (V × V)) (k : ℕ)
    (hk : 2 ≤ k)
    (hE : ∀ e ∈ E, ({(e.1, true), (e.2, true)} : Clause V) ∈ F)
    (hN : ∀ S : Finset V, S.card = k → S.image (fun v : V => (v, false)) ∈ F)
    (hU : ∀ T : Finset V, T.card < k → ∃ e ∈ E, e.1 ∉ T ∧ e.2 ∉ T ∧ e.1 ≠ e.2) :
    ∀ n, ∀ T : Finset V, T.card + n = k → Der F k (T.image (fun v : V => (v, false))) := by
  intro n
  induction n with
  | zero =>
    intro T hT
    exact der_ax (hN T (by omega)) (le_trans Finset.card_image_le (by omega))
  | succ n ih =>
    intro T hT
    obtain ⟨e, he, hu, hv, huv⟩ := hU T (by omega)
    have hA := ih (insert e.1 T) (by rw [Finset.card_insert_of_notMem hu]; omega)
    have hB := ih (insert e.2 T) (by rw [Finset.card_insert_of_notMem hv]; omega)
    have hEd : Der F k ({(e.1, true), (e.2, true)} : Clause V) :=
      der_ax (hE e he) (le_trans Finset.card_le_two (by omega))
    have hc := Finset.card_image_le (s := T) (f := fun v : V => (v, false))
    have h1 : Der F k (insert (e.2, true) (T.image (fun v : V => (v, false)))) := by
      refine der_res hEd hA ⟨e.1, by simp, by simp, ?_⟩ ?_
      · ext ⟨x, b⟩
        simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_union, Finset.mem_erase,
          Finset.mem_singleton, Prod.mk.injEq]
        constructor
        · rintro (⟨rfl, rfl⟩ | ⟨a, ha, rfl, rfl⟩)
          · exact Or.inl ⟨fun h => huv (Prod.mk.inj h).1.symm, Or.inr ⟨rfl, rfl⟩⟩
          · exact Or.inr ⟨fun h => hu ((Prod.mk.inj h).1 ▸ ha), a, Or.inr ha, rfl, rfl⟩
        · rintro (⟨h, (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)⟩ | ⟨h, a, (rfl | ha), rfl, rfl⟩)
          · exact absurd rfl h
          · exact Or.inl ⟨rfl, rfl⟩
          · exact absurd rfl h
          · exact Or.inr ⟨a, ha, rfl, rfl⟩
      · exact le_trans (Finset.card_insert_le _ _) (by omega)
    refine der_res h1 hB ⟨e.2, by simp, by simp, ?_⟩ (by omega)
    ext ⟨x, b⟩
    simp only [Finset.mem_insert, Finset.mem_image, Finset.mem_union, Finset.mem_erase,
      Prod.mk.injEq]
    constructor
    · rintro ⟨a, ha, rfl, rfl⟩
      exact Or.inr ⟨fun h => hv ((Prod.mk.inj h).1 ▸ ha), a, Or.inr ha, rfl, rfl⟩
    · rintro (⟨h, (⟨rfl, rfl⟩ | ⟨a, ha, rfl, rfl⟩)⟩ | ⟨h, a, (rfl | ha), rfl, rfl⟩)
      · exact absurd rfl h
      · exact ⟨a, ha, rfl, rfl⟩
      · exact absurd rfl h
      · exact ⟨a, ha, rfl, rfl⟩

-- Every clause of a narrow derivation holds under the all-true assignment.
theorem lower {V : Type} [DecidableEq V] (F : Set (Clause V)) (k : ℕ)
    (hF : ∀ C ∈ F, C.card < k → ∃ w, (w, true) ∈ C) :
    ∀ π, IsDerivation F π → (∀ D ∈ π, D.card < k) → ∀ D ∈ π, ∃ w, (w, true) ∈ D := by
  intro π h
  induction h with
  | nil => simp
  | ax _ hC ih =>
    intro hw X hX
    rcases List.mem_cons.mp hX with rfl | hX
    · exact hF _ hC (hw _ (by simp))
    · exact ih (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) X hX
  | @res π C D R _ hC hD hR ih =>
    intro hw X hX
    rcases List.mem_cons.mp hX with rfl | hX
    · obtain ⟨v, _, _, rfl⟩ := hR
      obtain ⟨w, hm⟩ := ih (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) D hD
      exact ⟨w, Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨by simp, hm⟩)⟩
    · exact ih (fun Y hY => hw Y (List.mem_cons_of_mem _ hY)) X hX

theorem spec {n : ℕ} (E : List (Fin n × Fin n)) (k : ℕ) (hk : 2 ≤ k)
    (hU : ∀ T : Finset (Fin n), T.card < k → ∃ e ∈ E, e.1 ∉ T ∧ e.2 ∉ T ∧ e.1 ≠ e.2)
    (F : Set (Clause (Fin n)))
    (hF : F = {C | ∃ e ∈ E, C = {(e.1, true), (e.2, true)}} ∪
      {C | ∃ S : Finset (Fin n), S.card = k ∧ C = S.image (fun v : Fin n => (v, false))}) :
    (∃ π, IsRefutation F π ∧ ∀ D ∈ π, D.card ≤ k) ∧
      ¬ ∃ π, IsRefutation F π ∧ ∀ D ∈ π, D.card < k := by
  have hE : ∀ e ∈ E, ({(e.1, true), (e.2, true)} : Clause (Fin n)) ∈ F := by
    intro e he
    rw [hF]
    exact Or.inl ⟨e, he, rfl⟩
  have hN : ∀ S : Finset (Fin n), S.card = k →
      S.image (fun v : Fin n => (v, false)) ∈ F := by
    intro S hS
    rw [hF]
    exact Or.inr ⟨S, hS, rfl⟩
  constructor
  · obtain ⟨π, hd, hm, hw⟩ := upper F E k hk hE hN hU k ∅ (by simp)
    exact ⟨π, ⟨hd, by simpa using hm⟩, hw⟩
  · rintro ⟨π, ⟨hd, hm⟩, hw⟩
    refine absurd (lower F k ?_ π hd hw ∅ hm) (by simp)
    rw [hF]
    rintro C (⟨e, _, rfl⟩ | ⟨S, hS, rfl⟩) hC
    · exact ⟨e.1, by simp⟩
    · rw [Finset.card_image_of_injective _ (fun a b h => (Prod.mk.inj h).1)] at hC
      omega

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16000 in
theorem petersen : ∀ T : Finset (Fin 10), T.card < 6 → ∃ e ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10)), e.1 ∉ T ∧ e.2 ∉ T ∧ e.1 ≠ e.2 := by
  decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 16000 in
theorem graphW : ∀ T : Finset (Fin 11), T.card < 7 → ∃ e ∈ ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] : List (Fin 11 × Fin 11)), e.1 ∉ T ∧ e.2 ∉ T ∧ e.1 ≠ e.2 := by
  decide +kernel

end PEqualNP.Outside.L_pcx_101

theorem PEqualNP.Outside.L_pcx_101 : (∀ F1 : Set (PEqualNP.ProofComplexity.Clause (Fin 10)), F1 = {Ca1 | ∃ ea1 ∈ ([(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)] : List (Fin 10 × Fin 10)), Ca1 = {(ea1.1, true), (ea1.2, true)}} ∪ {Cb1 | ∃ Sb1 : Finset (Fin 10), Sb1.card = 6 ∧ Cb1 = Sb1.image (fun vb1 : Fin 10 => (vb1, false))} → (∃ πa1, PEqualNP.ProofComplexity.IsRefutation F1 πa1 ∧ ∀ Da1 ∈ πa1, Da1.card ≤ 6) ∧ ¬ ∃ πb1, PEqualNP.ProofComplexity.IsRefutation F1 πb1 ∧ ∀ Db1 ∈ πb1, Db1.card ≤ 5) ∧ (∀ F2 : Set (PEqualNP.ProofComplexity.Clause (Fin 11)), F2 = {Ca2 | ∃ ea2 ∈ ([(0, 9), (0, 10), (1, 4), (1, 8), (2, 5), (2, 10), (3, 6), (3, 7), (4, 8), (4, 10), (5, 8), (5, 9), (6, 7), (6, 10), (7, 9), (8, 9)] : List (Fin 11 × Fin 11)), Ca2 = {(ea2.1, true), (ea2.2, true)}} ∪ {Cb2 | ∃ Sb2 : Finset (Fin 11), Sb2.card = 7 ∧ Cb2 = Sb2.image (fun vb2 : Fin 11 => (vb2, false))} → (∃ πa2, PEqualNP.ProofComplexity.IsRefutation F2 πa2 ∧ ∀ Da2 ∈ πa2, Da2.card ≤ 7) ∧ ¬ ∃ πb2, PEqualNP.ProofComplexity.IsRefutation F2 πb2 ∧ ∀ Db2 ∈ πb2, Db2.card ≤ 6) := by
  refine ⟨fun F1 h1 => ?_, fun F2 h2 => ?_⟩
  · have h := PEqualNP.Outside.L_pcx_101.spec _ 6 (by decide) PEqualNP.Outside.L_pcx_101.petersen F1 h1
    exact ⟨h.1, fun ⟨π, hr, hw⟩ => h.2 ⟨π, hr, fun D hD => Nat.lt_succ_of_le (hw D hD)⟩⟩
  · have h := PEqualNP.Outside.L_pcx_101.spec _ 7 (by decide) PEqualNP.Outside.L_pcx_101.graphW F2 h2
    exact ⟨h.1, fun ⟨π, hr, hw⟩ => h.2 ⟨π, hr, fun D hD => Nat.lt_succ_of_le (hw D hD)⟩⟩
