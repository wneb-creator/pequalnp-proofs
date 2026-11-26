import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.ReadK PEqualNP.TopForm PEqualNP.ReadTwo

-- The stabilizer of the marked flag gives fourteen unordered first-gate input pairs.
-- The suffix sees that gate as a twenty-seventh wire. Its search checks the
-- extremal rows and asks for a proof tree reading at least one marked endpoint once.
set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_4021_584
    (canonical : let f := fpl 13 (fun (p l : Fin 13) => p-l ∈ ([0,1,3,9] : List (Fin 13)))
    let ok := fun C : Circuit => IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      (∀ x : Fin 26 → Bool, (∀ i, x i = f x → f (Function.update x i (!x i)) ≠ f x) →
        circuitFun 26 C x = f x) ∧ 0 < andPairs 26 C ∧
      ∃ j < C.size, (gateAt C j).op = GateOp.and ∧
        ∃ y : Fin 26 → Bool, wval C y (26+j) = true ∧ circuitFun 26 C y = false
    let win := fun C : Circuit => ∃ v ∈ ([0,13] : List ℕ),
      (scalarMults C 26 [0,13] v).getD C.output none = some 1
    ∀ C, C.size ≤ 64 → ok C → ∃ (D : Circuit) (a b : Fin 26) (t : Bool),
      let E : Circuit := ⟨⟨if t then GateOp.or else GateOp.and,[a.val,b.val]⟩::D.gates,D.output⟩
      D.size ≤ 63 ∧ 26*min a.val b.val + max a.val b.val ∈ ([1,2,13,14,17,28,29,40,41,43,56,60,66,68] : List ℕ) ∧ ok E ∧ (win E → win C))
    (search : let f := fpl 13 (fun (p l : Fin 13) => p-l ∈ ([0,1,3,9] : List (Fin 13)))
    let ok := fun C : Circuit => IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      (∀ x : Fin 26 → Bool, (∀ i, x i = f x → f (Function.update x i (!x i)) ≠ f x) →
        circuitFun 26 C x = f x) ∧ 0 < andPairs 26 C ∧
      ∃ j < C.size, (gateAt C j).op = GateOp.and ∧
        ∃ y : Fin 26 → Bool, wval C y (26+j) = true ∧ circuitFun 26 C y = false
    let win := fun C : Circuit => ∃ v ∈ ([0,13] : List ℕ),
      (scalarMults C 26 [0,13] v).getD C.output none = some 1
    ∀ (D : Circuit) (a b : Fin 26) (t : Bool), D.size ≤ 63 → 26*min a.val b.val + max a.val b.val ∈ ([1,2,13,14,17,28,29,40,41,43,56,60,66,68] : List ℕ) →
      let E : Circuit := ⟨⟨if t then GateOp.or else GateOp.and,[a.val,b.val]⟩::D.gates,D.output⟩
      ok E → win E)
    (bridge : ∀ (n : ℕ) (C : Circuit) (a b : Fin n) (S : List ℕ),
     IsAO2 n C → a ≠ b → (∀ i : ℕ, i ∈ S ↔ i=a.val ∨ i=b.val) →
     (scalarMults C n S b.val).getD C.output none = some 1 →
     Relation.ReflTransGen (fun u w : ℕ => ∃ (j : ℕ) (g : Gate) (q : ℕ), w = n+j ∧ C.gates[j]? = some g ∧
      (g.inputs = [u,q] ∨ g.inputs = [q,u]) ∧
      (g.op = GateOp.or ∨ g.op = GateOp.and ∧ wval C (fun i => decide (i=a)) q = true)) b.val C.output)
    : have x1 : PEqualNP.CircuitLowerBounds.Circuit → Fin (26 : ℕ) → ℕ → ℕ → Prop := fun (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (26 : ℕ)) (x3 x4 : ℕ) => ∃ (x5 : ℕ) (x6 : PEqualNP.CircuitLowerBounds.Gate) (x7 : ℕ), x4 = (26 : ℕ) + x5 ∧ x1.gates[x5]? = Option.some x6 ∧ (x6.inputs = [x3, x7] ∨ x6.inputs = [x7, x3]) ∧ (x6.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ x6.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ (x1.wires (List.ofFn fun (x8 : Fin (26 : ℕ)) => Decidable.decide (x8 = x2))).getD x7 Bool.false = Bool.true); have x2 : Finset (Fin (13 : ℕ)) := {(0 : Fin (13 : ℕ)), (1 : Fin (13 : ℕ)), (3 : Fin (13 : ℕ)), (9 : Fin (13 : ℕ))}; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => x3.size ≤ (64 : ℕ) ∧ PEqualNP.TopForm.IsAO2 (26 : ℕ) x3 ∧ (∀ x4 ∈ x3.gates, x4.inputs.Nodup) ∧ (∀ (x4 : Fin (26 : ℕ) → Bool), x3.eval (List.ofFn x4) = Bool.true ↔ ∃ (x5 : Fin (13 : ℕ)) (x6 : Fin (13 : ℕ)), x5 - x6 ∈ x2 ∧ x4 (Fin.castAdd (13 : ℕ) x5) = Bool.true ∧ x4 (Fin.natAdd (13 : ℕ) x6) = Bool.true) ∧ (0 : ℕ) < PEqualNP.TopForm.andPairs (26 : ℕ) x3 ∧ ∃ x4 < x3.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x3 x4).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ∃ (x5 : Fin (26 : ℕ) → Bool), (x3.wires (List.ofFn x5)).getD ((26 : ℕ) + x4) Bool.false = Bool.true ∧ x3.eval (List.ofFn x5) = Bool.false; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), x3 x4 → Relation.ReflTransGen (x1 x4 (0 : Fin (26 : ℕ))) (13 : ℕ) x4.output ∨ Relation.ReflTransGen (x1 x4 (13 : Fin (26 : ℕ))) (0 : ℕ) x4.output := by
  dsimp only
  intro C hyp
  obtain ⟨size,ao,distinct,computes,nested,dirty⟩ := hyp
  let f := fpl 13 (fun (p l : Fin 13) => p-l ∈ ([0,1,3,9] : List (Fin 13)))
  let ok := fun C : Circuit => IsAO2 26 C ∧ (∀ g ∈ C.gates, g.inputs.Nodup) ∧
      (∀ x : Fin 26 → Bool, (∀ i, x i = f x → f (Function.update x i (!x i)) ≠ f x) →
        circuitFun 26 C x = f x) ∧ 0 < andPairs 26 C ∧
      ∃ j < C.size, (gateAt C j).op = GateOp.and ∧
        ∃ y : Fin 26 → Bool, wval C y (26+j) = true ∧ circuitFun 26 C y = false
  have full (x) : circuitFun 26 C x = f x := by
    rw [Bool.eq_iff_iff]
    change (C.eval (List.ofFn x) = true ↔ decide (∃ p l : Fin 13,
      p-l ∈ ([0,1,3,9] : List (Fin 13)) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true) = true)
    rw [decide_eq_true_iff]
    simpa only [List.mem_cons,List.not_mem_nil,or_false,Finset.mem_insert,Finset.mem_singleton] using computes x
  have good : ok C := ⟨ao,distinct,fun x _ => full x,nested,dirty⟩
  obtain ⟨D,a,b,t,sz,rep,core,back⟩ := canonical C size good
  obtain ⟨v,mem,reading⟩ := back (search D a b t sz rep core)
  simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
  rcases mem with rfl | rfl
  · right
    exact bridge 26 C 13 0 [0,13] ao (by decide) (by intro i; simp [or_comm]) reading
  · left
    exact bridge 26 C 0 13 [0,13] ao (by decide) (by intro i; simp) reading
