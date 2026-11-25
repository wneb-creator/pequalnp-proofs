namespace PEqualNP.Outside.L_meta_2592_aux.Overlap

open PEqualNP.Outside.L_meta_2592.Signed
open PEqualNP.Outside.L_meta_2592_aux.PairSeparation
open PEqualNP.Outside.L_meta_2592_aux.FirstGateCases

lemma no_overlap_shape (floor : ZeroFloor) (D : U2Circuit) (hmin : IsMinU2 pet D)
    (small : D.gates.length ≤ 17) (h0 : 0 < D.gates.length)
    (v u : Nat) (hv : v < 10) (hu : u < 10)
    (huFirst : D.gates[0].a = u ∨ D.gates[0].b = u)
    (hg0 : ∀ x : Fin 10 → Bool,
      u2Val D.gates x 10 = ((u2Val D.gates x v != true) &&
        (u2Val D.gates x u != true)))
    (j : Nat) (hj : j < D.gates.length) (positive : 0 < j) (q : Bool)
    (hgj : ∀ x : Fin 10 → Bool,
      u2Val D.gates x (10 + j) = ((u2Val D.gates x v != true) &&
        (u2Val D.gates x 10 != q))) : False := by
  have interaction := min_gate0_interact hmin h0 v u true true hv hu hg0
    j hj positive true q hgj
  have hq : q = true := interaction.2.1
  let g : U2Gate := ⟨v, u, true, false⟩
  have replacement := replaceGateAt_spec D hmin.1 j hj g
    (by dsimp [g, U2Gate.a]; omega) (by dsimp [g, U2Gate.b]; omega)
    (fun x => by
      dsimp [g, U2Gate.a, U2Gate.b, U2Gate.pa, U2Gate.pb]
      rw [hgj x, hq, hg0 x]
      cases u2Val D.gates x v <;> cases u2Val D.gates x u <;> rfl)
  let E := replaceGateAt D j g
  have heLength : E.gates.length = D.gates.length := replacement.2.1
  have heMin : IsMinU2 pet E :=
    ⟨replacement.1, fun x => (replacement.2.2 x).trans (hmin.2.1 x),
      fun D' hwf hc => by rw [heLength]; exact hmin.2.2 D' hwf hc⟩
  have he0 : 0 < E.gates.length := by omega
  have hej : j < E.gates.length := by omega
  have hz : E.gates[0] = D.gates[0] := by
    simp [E, replaceGateAt, U2Circuit.gates, List.getElem_set_ne (by omega : j ≠ 0)]
  have hjg : E.gates[j] = g := by
    simp [E, replaceGateAt, U2Circuit.gates]
  have phases := (first_sources_negative_everywhere floor E heMin (by omega) he0).2.2 j hej
  rcases huFirst with ha | hb
  · have h := phases.2.1 (by rw [hz, hjg]; exact ha.symm)
    rw [hjg] at h
    change false = true at h
    cases h
  · have h := phases.2.2.2 (by rw [hz, hjg]; exact hb.symm)
    rw [hjg] at h
    change false = true at h
    cases h

lemma no_first_source_overlap (floor : ZeroFloor) (D : U2Circuit) (hmin : IsMinU2 pet D)
    (small : D.gates.length ≤ 17) (h0 : 0 < D.gates.length)
    (j : Nat) (hj : j < D.gates.length) (positive : 0 < j) :
    ¬ ((D.gates[j].a = 10 ∨ D.gates[j].b = 10) ∧
      (D.gates[j].a = D.gates[0].a ∨ D.gates[j].b = D.gates[0].a ∨
        D.gates[j].a = D.gates[0].b ∨ D.gates[j].b = D.gates[0].b)) := by
  obtain ⟨pa, pb, allPhases⟩ := first_sources_negative_everywhere floor D hmin small h0
  have ha := (hmin.1.1 0 h0).1
  have hb := (hmin.1.1 0 h0).2
  have gate0 : ∀ x : Fin 10 → Bool,
      u2Val D.gates x 10 = ((u2Val D.gates x D.gates[0].a != true) &&
        (u2Val D.gates x D.gates[0].b != true)) := by
    intro x
    have h := u2Val_gate D.gates x 0 h0 ha hb
    simpa [pa, pb] using h
  have gate0swap : ∀ x : Fin 10 → Bool,
      u2Val D.gates x 10 = ((u2Val D.gates x D.gates[0].b != true) &&
        (u2Val D.gates x D.gates[0].a != true)) := by
    intro x
    rw [gate0 x, Bool.and_comm]
  have gatej := fun x => u2Val_gate D.gates x j hj (hmin.1.1 j hj).1 (hmin.1.1 j hj).2
  rintro ⟨hg | hg, hr | hr | hr | hr⟩
  · omega
  · apply no_overlap_shape floor D hmin small h0 _ _ ha hb (Or.inr rfl) gate0
      j hj positive D.gates[j].pa
    intro x
    rw [gatej x, hg, hr, (allPhases j hj).2.1 hr, Bool.and_comm]
  · omega
  · apply no_overlap_shape floor D hmin small h0 _ _ hb ha (Or.inl rfl) gate0swap
      j hj positive D.gates[j].pa
    intro x
    rw [gatej x, hg, hr, (allPhases j hj).2.2.2 hr, Bool.and_comm]
  · apply no_overlap_shape floor D hmin small h0 _ _ ha hb (Or.inr rfl) gate0
      j hj positive D.gates[j].pb
    intro x
    rw [gatej x, hg, hr, (allPhases j hj).1 hr]
  · omega
  · apply no_overlap_shape floor D hmin small h0 _ _ hb ha (Or.inl rfl) gate0swap
      j hj positive D.gates[j].pb
    intro x
    rw [gatej x, hg, hr, (allPhases j hj).2.2.1 hr]
  · omega

end PEqualNP.Outside.L_meta_2592_aux.Overlap
