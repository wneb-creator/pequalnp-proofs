import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

-- Check the first AND whose operand OR-cones span a nonedge. The earlier AND gates
-- already have adjacent cross pairs. The two local checks concern the size of a cone
-- and adjacency to its single input when both cones are nonempty.
set_option maxHeartbeats 2400000 in
theorem PEqualNP.Outside.R_meta_6394_572
    (badOrigins : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit),
    G = SimpleGraph.fromRel (fun u v : Fin 26 => u.val < 13 ∧ 13 ≤ v.val ∧
      (u.val + 26 - v.val) % 13 ∈ ([0,1,3,9] : List ℕ)) → IsLeastAO G C → junk G C ≠ ∅ →
    ∃ D : Circuit, IsLeastAO G D ∧ PEqualNP.TopForm.TopForm G D ∧ D.size ≤ C.size ∧
      ∃ j < D.size, (gateAt D j).op = GateOp.and ∧
       ∃ u ∈ side (n:=26) D j 0, ∃ v ∈ side (n:=26) D j 1, ¬ G.Adj u v)
    (narrow : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit),
    G = SimpleGraph.fromRel (fun u v : Fin 26 => u.val < 13 ∧ 13 ≤ v.val ∧
      (u.val + 26 - v.val) % 13 ∈ ([0,1,3,9] : List ℕ)) → IsLeastAO G C → PEqualNP.TopForm.TopForm G C → C.size ≤ 64 → ∀ j < C.size,
      (∀ h < j, (fun h : ℕ => (gateAt C h).op = GateOp.and →
      ∀ u ∈ side (n:=26) C h 0, ∀ v ∈ side (n:=26) C h 1, G.Adj u v) h) → (gateAt C j).op = GateOp.and → ∀ A B : Finset (Fin 26), A = side (n:=26) C j 0 → B = side (n:=26) C j 1 → A.card ≤ 1 ∨ B.card ≤ 1)
    (centered : ∀ (G : SimpleGraph (Fin 26)) [DecidableRel G.Adj] (C : Circuit),
    G = SimpleGraph.fromRel (fun u v : Fin 26 => u.val < 13 ∧ 13 ≤ v.val ∧
      (u.val + 26 - v.val) % 13 ∈ ([0,1,3,9] : List ℕ)) → IsLeastAO G C → PEqualNP.TopForm.TopForm G C → C.size ≤ 64 → ∀ j < C.size,
      (∀ h < j, (fun h : ℕ => (gateAt C h).op = GateOp.and →
      ∀ u ∈ side (n:=26) C h 0, ∀ v ∈ side (n:=26) C h 1, G.Adj u v) h) → (gateAt C j).op = GateOp.and → ∀ (b : Fin 2) (u : Fin 26), side (n:=26) C j b = {u} →
        ∀ v ∈ side (n:=26) C j (1-b), G.Adj u v)
    : ∀ (x1 : SimpleGraph (Fin (26 : ℕ))) [x2 : DecidableRel x1.Adj] (x3 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x4 x5 : Fin (26 : ℕ)), x1.Adj x4 x5 ↔ ∃ (x6 : Fin (13 : ℕ)) (x7 : Fin (13 : ℕ)), (x6 = x7 ∨ x6 = x7 + (1 : Fin (13 : ℕ)) ∨ x6 = x7 + (3 : Fin (13 : ℕ)) ∨ x6 = x7 + (9 : Fin (13 : ℕ))) ∧ (x4 = Fin.castAdd (13 : ℕ) x6 ∧ x5 = Fin.natAdd (13 : ℕ) x7 ∨ x5 = Fin.castAdd (13 : ℕ) x6 ∧ x4 = Fin.natAdd (13 : ℕ) x7)) → PEqualNP.TopForm.IsLeastAO x1 x3 → PEqualNP.TopForm.junk x1 x3 ≠ ∅ → ∃ (x7 : Finset (Fin (26 : ℕ))), (∀ (x8 x9 : Fin (26 : ℕ)), x1.Adj x8 x9 → x8 ∈ x7 ∨ x9 ∈ x7) ∧ (∃ (x8 : Fin (13 : ℕ)), Fin.castAdd (13 : ℕ) x8 ∈ x7) ∧ (∃ (x8 : Fin (13 : ℕ)), Fin.natAdd (13 : ℕ) x8 ∈ x7) ∧ (52 : ℕ) + x7.card ≤ x3.size + (1 : ℕ) := by
  intro G inst C graph least dirty
  classical
  let G0 := SimpleGraph.fromRel (fun u v : Fin 26 => u.val < 13 ∧ 13 ≤ v.val ∧
      (u.val + 26 - v.val) % 13 ∈ ([0,1,3,9] : List ℕ))
  have geometry (u v : Fin 26) : G0.Adj u v ↔ ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
    ((u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l) ∨ (v = Fin.castAdd 13 p ∧ u = Fin.natAdd 13 l)) := by
    exact (by decide +kernel : ∀ u v : Fin 26, G0.Adj u v ↔ ∃ p l : Fin 13, (p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9) ∧
    ((u = Fin.castAdd 13 p ∧ v = Fin.natAdd 13 l) ∨ (v = Fin.castAdd 13 p ∧ u = Fin.natAdd 13 l))) u v
  have same : G = G0 := SimpleGraph.ext (funext fun u => funext fun v => propext ((graph u v).trans (geometry u v).symm))
  by_cases small : C.size ≤ 64
  · obtain ⟨D,minD,form,le,j,hj,op,u,hu,v,hv,no⟩ := badOrigins G C same least dirty
    have limit : D.size ≤ 64 := le.trans small
    let good := fun h : ℕ => (gateAt D h).op = GateOp.and →
      ∀ u ∈ side (n:=26) D h 0, ∀ v ∈ side (n:=26) D h 1, G.Adj u v
    have law : ∀ i : ℕ, i < D.size → good i := by
      intro i
      induction i using Nat.strong_induction_on with
      | ind i ih =>
        intro hi hop a ha b hb
        have prev : ∀ k < i, good k := fun k hlt => ih k hlt (by omega)
        have thin := narrow G D same minD form limit i hi prev hop _ _ rfl rfl
        have cn := centered G D same minD form limit i hi prev hop
        rcases thin with left | right
        · have eq : side (n:=26) D i 0 = {a} :=
            Finset.eq_singleton_iff_unique_mem.mpr ⟨ha,fun z hz => Finset.card_le_one.mp left z hz a ha⟩
          exact cn 0 a eq b (by simpa using hb)
        · have eq : side (n:=26) D i 1 = {b} :=
            Finset.eq_singleton_iff_unique_mem.mpr ⟨hb,fun z hz => Finset.card_le_one.mp right z hz b hb⟩
          exact (cn 1 b eq a (by simpa using ha)).symm
    exact False.elim (no (law j hj op u hu v hv))
  · let pts := (Finset.univ : Finset (Fin 13)).image (Fin.castAdd 13)
    let K := insert (Fin.natAdd 13 (0 : Fin 13)) pts
    have points (p : Fin 13) : Fin.castAdd 13 p ∈ K :=
      Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨p,Finset.mem_univ _,rfl⟩)
    refine ⟨K,?_,⟨0,points 0⟩,⟨0,Finset.mem_insert_self ..⟩,?_⟩
    · intro u v h
      obtain ⟨p,l,_,orient⟩ := (graph u v).mp h
      rcases orient with ⟨rfl,_⟩ | ⟨rfl,_⟩
      · exact Or.inl (points p)
      · exact Or.inr (points p)
    · have count : K.card = 14 := by decide +kernel
      omega
