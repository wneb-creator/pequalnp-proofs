namespace PEqualNP.Outside.L_meta_3451_aux.Star

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def NormalForm (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit) : Prop :=
  ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
    (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
    (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
      ∀ p l : Fin N, ¬ I p l →
        (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD
            (N + N + j) false = false) ∧
    (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
      (∀ p : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
        decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
      ∀ l : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
        decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false)

lemma complete (N : ℕ) (I : Fin N → Fin N → Prop) (C D : Circuit)
    (hm : Monotone2 D) (hb : NestedCover.ReadsBack (N + N) D) (hs : D.size ≤ C.size)
    (sem : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (below : ∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
      ∀ z : Fin (N + N) → Bool, PEqualNP.EdgeOwnership.gateVal (N + N) D j z = true →
        circuitFun (N + N) D z = true) : NormalForm N I C := by
  refine ⟨D, hm, hb, hs, sem, ?_, ?_⟩
  · intro j hj hand p l hn
    apply Bool.eq_false_iff.mpr
    intro hv
    have ho := below j hj hand _ hv
    rw [incidence_nonedge_false N I D sem p l hn] at ho
    cases ho
  · intro j hj hand
    constructor
    · intro p
      apply Bool.eq_false_iff.mpr
      intro hv
      have ho := below j hj hand _ hv
      rw [incidence_point_false N I D sem p] at ho
      cases ho
    · intro l
      apply Bool.eq_false_iff.mpr
      intro hv
      have ho := below j hj hand _ hv
      rw [incidence_line_false N I D sem l] at ho
      cases ho

lemma point_star (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (sem : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (p0 : Fin N) (center : ∀ p l, I p l → p = p0) : NormalForm N I C := by
  let S := Dependency.activeLines N I
  let xs := S.toList.map (Fin.natAdd N)
  obtain ⟨D, dm, db, ds, de, below⟩ := construct (N + N) (Fin.castAdd N p0) xs
  have size : D.size ≤ C.size := ds.trans (by
    simpa [xs, S] using (Dependency.active_sides_bound N I C hfan sem).2)
  have semantics : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
    intro z
    rw [de, Bool.and_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨hp, k, hk, hzk⟩
      obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hk
      have hl' : l ∈ Dependency.activeLines N I := Finset.mem_toList.mp hl
      obtain ⟨p, hip⟩ := (Finset.mem_filter.mp hl').2
      have hip0 : I p0 l := (center p l hip) ▸ hip
      exact ⟨p0, l, hip0, hp, hzk⟩
    · rintro ⟨p, l, hip, hp, hl⟩
      refine ⟨?_, Fin.natAdd N l, ?_, hl⟩
      · simpa only [center p l hip] using hp
      · exact List.mem_map.mpr ⟨l,
          Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨p, hip⟩⟩), rfl⟩
  exact complete N I C D dm db size semantics below

lemma line_star (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (sem : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
    (l0 : Fin N) (center : ∀ p l, I p l → l = l0) : NormalForm N I C := by
  let S := Dependency.activePoints N I
  let xs := S.toList.map (Fin.castAdd N)
  obtain ⟨D, dm, db, ds, de, below⟩ := construct (N + N) (Fin.natAdd N l0) xs
  have size : D.size ≤ C.size := ds.trans (by
    simpa [xs, S] using (Dependency.active_sides_bound N I C hfan sem).1)
  have semantics : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
    intro z
    rw [de, Bool.and_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨hl, k, hk, hzk⟩
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hk
      have hp' : p ∈ Dependency.activePoints N I := Finset.mem_toList.mp hp
      obtain ⟨l, hip⟩ := (Finset.mem_filter.mp hp').2
      have hil0 : I p l0 := (center p l hip) ▸ hip
      exact ⟨p, l0, hil0, hzk, hl⟩
    · rintro ⟨p, l, hip, hp, hl⟩
      refine ⟨?_, Fin.castAdd N p, ?_, hp⟩
      · simpa only [center p l hip] using hl
      · exact List.mem_map.mpr ⟨p,
          Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨l, hip⟩⟩), rfl⟩
  exact complete N I C D dm db size semantics below

end PEqualNP.Outside.L_meta_3451_aux.Star
