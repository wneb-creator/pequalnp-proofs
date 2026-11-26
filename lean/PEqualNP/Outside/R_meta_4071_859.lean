import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.HeptadCover PEqualNP.GenericRejection

-- Eliminate reads of future wires. The non-nested case has the ordinary
-- order-three two-level lower bound. A fixed quadrangle gives an independent
-- OR budget even for a circuit with nested AND gates.
set_option maxRecDepth 12000 in
set_option maxHeartbeats 1500000 in
theorem PEqualNP.Outside.R_meta_4071_859
  (clean : ∀ C : Circuit, Monotone2 C →
     ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ D.size ≤ C.size ∧
       circuitFun 26 D = circuitFun 26 C)
  (flat : ∀ C : Circuit, Monotone2 C → ReadsBack 26 C → RightOnIncidentPairs singerLines3 C →
     (∀ Q, IsQuadrangle singerLines3 Q → C.eval (incidenceInput Q (missLines singerLines3 Q)) = false) →
     (¬ ∃ i j : ℕ, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j) →
     64 ≤ C.size)
  (orFloor : ∀ C : Circuit, Monotone2 C → ReadsBack 26 C → C.output < 26 + C.size →
     RightOnIncidentPairs singerLines3 C →
     C.eval (incidenceInput ({0,1,2,5} : Finset (Fin 13)) ({3,7,8} : Finset (Fin 13))) = false →
     18 ≤ C.gates.countP (fun g => g.op.eval [true,false]))
  (nested : let S := singerLines3
    let T := fun p : Fin 13 => Finset.univ.filter (fun l => p ∈ S l)
    ∀ C : Circuit, Monotone2 C → ReadsBack 26 C → C.size ≤ 63 →
    (∃ i j : ℕ, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j) →
    18 ≤ C.gates.countP (fun g => g.op.eval [true,false]) →
    RightOnIncidentPairs S C →
    (∀ Q, IsQuadrangle S Q → C.eval (incidenceInput Q (missLines S Q)) = false) →
    (∀ L, IsQuadrangle T L → C.eval (incidenceInput (missLines T L) L) = false) →
    False) :
let x1 : Fin (13 : ℕ) → Fin (13 : ℕ) → Prop := fun (x1 x2 : Fin (13 : ℕ)) => x1 = x2 ∨ x1 = x2 + (1 : Fin (13 : ℕ)) ∨ x1 = x2 + (3 : Fin (13 : ℕ)) ∨ x1 = x2 + (9 : Fin (13 : ℕ)); have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x2 : Finset (Fin (13 : ℕ))) => {x3 : Fin (13 : ℕ) | ∀ x4 ∈ x2, ¬x1 x4 x3}; have x3 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) := fun (x3 : Finset (Fin (13 : ℕ))) => {x4 : Fin (13 : ℕ) | ∀ x5 ∈ x3, ¬x1 x4 x5}; have x4 : Finset (Fin (13 : ℕ)) → Prop := fun (x4 : Finset (Fin (13 : ℕ))) => ∀ (x5 : Fin (13 : ℕ)), {x6 ∈ x4 | x1 x6 x5}.card ≤ (2 : ℕ); have x5 : Finset (Fin (13 : ℕ)) → Prop := fun (x5 : Finset (Fin (13 : ℕ))) => ∀ (x6 : Fin (13 : ℕ)), (Finset.filter (x1 x6) x5).card ≤ (2 : ℕ); have x6 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Fin (26 : ℕ) → Bool := fun (x6 x7 : Finset (Fin (13 : ℕ))) (x8 : Fin (26 : ℕ)) => Fin.addCases (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x6)) (fun (x9 : Fin (13 : ℕ)) => Decidable.decide (x9 ∈ x7)) x8; ∀ (x7 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x7 → x7.size ≤ (63 : ℕ) → (∀ (x10 x11 : Fin (13 : ℕ)), x1 x10 x11 → (PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 fun (x13 : Fin (26 : ℕ)) => Decidable.decide (x13 = Fin.castAdd (13 : ℕ) x10 ∨ x13 = Fin.natAdd (13 : ℕ) x11)) = Bool.true) → (∃ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) ∧ x4 x11 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 x11 (x2 x11)) = Bool.true) ∨ ∃ (x11 : Finset (Fin (13 : ℕ))), x11.card = (4 : ℕ) ∧ x5 x11 ∧ PEqualNP.MetaComplexity.circuitFun (26 : ℕ) x7 (x6 (x3 x11) x11) = Bool.true := by
  classical
  intro I M N P L row C mono size yes
  obtain ⟨D, dm, back, ds, sem⟩ := clean C mono
  let S := singerLines3
  let T := fun p : Fin 13 => Finset.univ.filter (fun l => p ∈ S l)
  have inc : ∀ p l : Fin 13, p ∈ S l ↔ I p l := by decide +kernel
  have transInc (p l : Fin 13) : l ∈ T p ↔ I p l := by simp [T,inc]
  have rowList (X Y : Finset (Fin 13)) : List.ofFn (row X Y) = incidenceInput X Y := by
    exact List.ofFn_fin_append (fun p : Fin 13 => decide (p ∈ X)) (fun l : Fin 13 => decide (l ∈ Y))
  have flagRows : ∀ (p l : Fin 13) (i : Fin 26),
      decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l) = row {p} {l} i := by decide +kernel
  have flag (p l : Fin 13) :
     (fun i : Fin 26 => decide (i = Fin.castAdd 13 p ∨ i = Fin.natAdd 13 l)) =
       row {p} {l} := funext (flagRows p l)
  have right : RightOnIncidentPairs S D := by
    intro l p h
    rw [← rowList]
    change circuitFun 26 D (row {p} {l}) = true
    rw [sem,← flag]
    exact yes p l ((inc p l).mp h)
  have extP (Q : Finset (Fin 13)) : missLines S Q = M Q := by
    ext l
    change l ∈ Finset.univ.filter (fun k => Disjoint (S k) Q) ↔
      l ∈ Finset.univ.filter (fun k => ∀ p ∈ Q, ¬ I p k)
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_right,inc]
  have extL (Q : Finset (Fin 13)) : missLines T Q = N Q := by
    ext p
    change p ∈ Finset.univ.filter (fun k => Disjoint (T k) Q) ↔
      p ∈ Finset.univ.filter (fun k => ∀ l ∈ Q, ¬ I k l)
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.disjoint_right,transInc]
  have quadP (Q : Finset (Fin 13)) : IsQuadrangle S Q ↔ Q.card = 4 ∧ P Q := by
    have eq (l : Fin 13) : Q ∩ S l = Q.filter (fun p => I p l) := by
      ext p
      simp only [Finset.mem_inter,Finset.mem_filter,inc]
    change (Q.card = 4 ∧ ∀ l, (Q ∩ S l).card ≤ 2) ↔ _
    simp only [P,eq]
  have quadL (Q : Finset (Fin 13)) : IsQuadrangle T Q ↔ Q.card = 4 ∧ L Q := by
    have eq (p : Fin 13) : Q ∩ T p = Q.filter (fun l => I p l) := by
      ext l
      simp only [Finset.mem_inter,Finset.mem_filter,transInc]
    change (Q.card = 4 ∧ ∀ p, (Q ∩ T p).card ≤ 2) ↔ _
    simp only [L,eq]
  by_cases hitP : ∃ Q, Q.card = 4 ∧ P Q ∧ circuitFun 26 C (row Q (M Q)) = true
  · exact Or.inl hitP
  by_cases hitL : ∃ Q, Q.card = 4 ∧ L Q ∧ circuitFun 26 C (row (N Q) Q) = true
  · exact Or.inr hitL
  have rejectP : ∀ Q, IsQuadrangle S Q → D.eval (incidenceInput Q (missLines S Q)) = false := by
    intro Q h
    rw [extP Q,← rowList]
    change circuitFun 26 D _ = false
    rw [sem]
    apply Bool.eq_false_iff.mpr
    intro accepted
    have q := (quadP Q).mp h
    exact hitP ⟨Q,q.1,q.2,accepted⟩
  have rejectL : ∀ Q, IsQuadrangle T Q → D.eval (incidenceInput (missLines T Q) Q) = false := by
    intro Q h
    rw [extL Q,← rowList]
    change circuitFun 26 D _ = false
    rw [sem]
    apply Bool.eq_false_iff.mpr
    intro accepted
    have q := (quadL Q).mp h
    exact hitL ⟨Q,q.1,q.2,accepted⟩
  have dsize : D.size ≤ 63 := ds.trans size
  by_cases deep : ∃ i j : ℕ, (gateAt D i).op = .and ∧ (gateAt D j).op = .and ∧ InCone 26 D i j
  · have bankLength (gates : List Gate) (x : List Bool) :
      (gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).length =
        x.length+gates.length := by
      induction gates generalizing x with
      | nil => simp
      | cons g gs ih => rw [List.foldl_cons,ih]; simp; omega
    have oi : D.output < 26+D.size := by
      by_contra invalid
      have flag00 := right 0 0 (by decide)
      unfold Circuit.eval Circuit.wires at flag00
      have iLen : (incidenceInput ({0} : Finset (Fin 13)) ({0} : Finset (Fin 13))).length=26 := by
        change ((List.ofFn (fun p : Fin 13 => decide (p ∈ ({0} : Finset (Fin 13))))) ++
          (List.ofFn (fun l : Fin 13 => decide (l ∈ ({0} : Finset (Fin 13)))))).length = 26
        simp only [List.length_append,List.length_ofFn]
      rw [List.getD_eq_default _ _ (by
        rw [bankLength,iLen]; exact Nat.le_of_not_gt invalid)] at flag00
      cases flag00
    have one : IsQuadrangle S ({0,1,2,5} : Finset (Fin 13)) := by decide +kernel
    have extOne : missLines S ({0,1,2,5} : Finset (Fin 13)) = {3,7,8} := by decide +kernel
    have fixed := rejectP _ one
    rw [extOne] at fixed
    have ors := orFloor D dm back oi right fixed
    exact False.elim (nested D dm back dsize deep ors right rejectP rejectL)
  · have lb := flat D dm back right rejectP deep
    omega
