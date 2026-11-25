import PetersenOrbits

namespace PEqualNP.Outside.L_meta_2590_aux.Surplus

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem pg_edge_aut (σ : Equiv.Perm (Fin 10)) (hσ : IsAut σ) (x : Fin 10 → Bool) :
    sem_Edge Adj (fun i => x (σ i)) ↔ sem_Edge Adj x := by
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    exact ⟨σ u, σ v, (hσ u v).mpr huv, hu, hv⟩
  · rintro ⟨u, v, huv, hu, hv⟩
    refine ⟨σ.symm u, σ.symm v, ?_, by simpa using hu, by simpa using hv⟩
    apply (hσ _ _).mp
    simpa using huv

theorem pg_essential (i : Fin 10) : ∃ x y : Fin 10 → Bool,
    (∀ k, k ≠ i → x k = y k) ∧ ¬ sem_Edge Adj x ∧ sem_Edge Adj y := by
  obtain ⟨a, ha, _⟩ := sem_petersen_gr.2.2.2 i i
  exact ⟨single a, sem_two i a, fun k hk => by simp [single, sem_two, hk],
    sem_single_no_edge sem_petersen_gr a, sem_two_edge ha⟩

theorem pg_normalize (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = true ↔ sem_Edge Adj x) :
    ∃ D : Dag, StrictLive 10 D ∧ D.length ≤ C.size ∧ Correct D := by
  have h01 : Adj (0 : Fin 10) 1 := by decide
  obtain ⟨D, hD, hlen, hval⟩ := normalize_strictLive (n := 10) C hmono
    (by
      intro b
      cases b
      · exact ⟨_, by rw [Ne, Bool.not_eq_false]; exact (hC _).2 (sem_two_edge h01)⟩
      · refine ⟨fun _ => false, fun h => ?_⟩
        simpa [sem_Edge] using (hC _).1 h)
    (by
      intro i
      refine ⟨single i, fun h => sem_single_no_edge sem_petersen_gr i ((hC _).1 ?_)⟩
      rw [h]; simp [single])
    (by
      intro i
      obtain ⟨x, y, hxy, hx, hy⟩ := pg_essential i
      refine ⟨x, y, hxy, fun h => hx ((hC x).1 ?_)⟩
      rw [h]; exact (hC y).2 hy)
  exact ⟨D, hD, hlen, fun x => by rw [hval x]; exact hC x⟩

theorem pg_relabel (σ : Equiv.Perm (Fin 10)) (hσ : IsAut σ) {D : Dag}
    (h : StrictLive 10 D) (hD : Correct D) : Correct (relabel σ D) := by
  intro x
  rw [relabel_out σ h.1 h.2.2 x, hD]
  exact pg_edge_aut σ hσ x

theorem pg_six_cases (C : Circuit) (hmono : Monotone2 C)
    (hC : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = true ↔ sem_Edge Adj x)
    (hsize : C.size ≤ 19) :
    ∃ D : Dag, StrictLive 10 D ∧ Correct D ∧ D.length ≤ 19 ∧
      totalSurplus 10 D ≤ 10 ∧ 6 ≤ (eligSet 10 D).card ∧
      (ineligSet 10 D = ∅ ∨ ineligSet 10 D ∈ canonI) := by
  obtain ⟨D, h, hlen, hD⟩ := pg_normalize C hmono hC
  have hs : D.length ≤ 19 := by omega
  have hbudget := pg_budget h hD hs
  rcases pg_class (ineligSet 10 D) (elig_independent h hD) with hempty | ⟨σ, hσ, hrep⟩
  · exact ⟨D, h, hD, hs, hbudget.1, hbudget.2.1, Or.inl hempty⟩
  · refine ⟨relabel σ D, relabel_strictLive σ h, pg_relabel σ hσ h hD, ?_, ?_, ?_, ?_⟩
    · simpa only [relabel_length] using hs
    · simpa only [relabel_totalSurplus] using hbudget.1
    · rw [relabel_eligSet σ h.1, Finset.card_image_of_injective _ σ.injective]
      exact hbudget.2.1
    · rw [relabel_ineligSet σ h.1]
      exact Or.inr hrep

end PEqualNP.Outside.L_meta_2590_aux.Surplus
