import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.BlindGate PEqualNP.HeptadCover

-- Specialize one variable to false. A gate may be deleted if the value of an earlier wire
-- agrees on the whole slice. The first child is independent of the incidence graph.
theorem PEqualNP.Outside.R_meta_6230_271
    (compress : ∀ (n : ℕ) (v : Fin n) (C : Circuit), IsAO2 n C →
      let saved := (Finset.univ : Finset (Fin C.size)).filter fun j =>
        ∃ i : Fin (n + j.val), ∀ x : Fin n → Bool, x v = false →
          wireValue C n x (n + j.val) = wireValue C n x i.val
      ∃ D : Circuit, IsAO2 n D ∧ D.size + saved.card ≤ C.size ∧
        ∀ x : Fin n → Bool, x v = false → D.eval (List.ofFn x) = C.eval (List.ofFn x))
    (four :
      let hit (x : Fin 26 → Bool) := ∃ p l : Fin 13, p ∈ singerLines3 l ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
      ∀ C : Circuit, IsAO2 26 C → (∀ x, C.eval (List.ofFn x) = true ↔ hit x) →
      (∀ g, C.gates.head? = some g → g.inputs.head? = some 0) →
      (∀ a b : Fin 26, a ≠ b → ∃ g ∈ C.gates, a.val ∈ g.inputs ∧ b.val ∉ g.inputs) →
      ∃ v : Fin 26,
        let saved : Finset (Fin C.size) := (Finset.univ : Finset (Fin C.size)).filter fun j =>
        ∃ i : Fin (26 + j.val), ∀ x : Fin 26 → Bool, x v = false →
          wireValue C 26 x (26 + j.val) = wireValue C 26 x i.val
        4 ≤ saved.card)
    (minor :
      let hit (x : Fin 26 → Bool) := ∃ p l : Fin 13, p ∈ singerLines3 l ∧
        x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true
      ∀ (v : Fin 26) (D : Circuit), IsAO2 26 D →
        (∀ x, x v = false → (D.eval (List.ofFn x) = true ↔ hit x)) → 59 ≤ D.size) :
have x1 : (Fin (26 : ℕ) → Bool) → Prop := fun (x1 : Fin (26 : ℕ) → Bool) => ∃ (x2 : Fin (13 : ℕ)) (x3 : Fin (13 : ℕ)), (x2 = x3 ∨ x2 = x3 + (1 : Fin (13 : ℕ)) ∨ x2 = x3 + (3 : Fin (13 : ℕ)) ∨ x2 = x3 + (9 : Fin (13 : ℕ))) ∧ x1 (Fin.castAdd (13 : ℕ) x2) = Bool.true ∧ x1 (Fin.natAdd (13 : ℕ) x3) = Bool.true; have x2 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x2 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x3 : ℕ) (x4 : PEqualNP.CircuitLowerBounds.Gate), x2.gates[x3]? = Option.some x4 → (x4.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ x4.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ ∃ (x6 : ℕ) (x7 : ℕ), x4.inputs = [x6, x7] ∧ x6 ≠ x7 ∧ x6 < (26 : ℕ) + x3 ∧ x7 < (26 : ℕ) + x3; have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => ∀ (x4 : Fin (26 : ℕ) → Bool), x3.eval (List.ofFn x4) = Bool.true ↔ x1 x4; have x4 : PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Gate) => x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.and, inputs := [(0 : ℕ), (13 : ℕ)] : PEqualNP.CircuitLowerBounds.Gate } ∨ ∃ x5 ∈ [(1 : ℕ), (13 : ℕ), (14 : ℕ)], x4 = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [(0 : ℕ), x5] : PEqualNP.CircuitLowerBounds.Gate }; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), x2 x5 → x3 x5 → (∀ (x8 : PEqualNP.CircuitLowerBounds.Gate), x5.gates.head? = Option.some x8 → x4 x8) → (∀ (x9 x10 : Fin (26 : ℕ)), x9 ≠ x10 → ∃ x12 ∈ x5.gates, ↑x9 ∈ x12.inputs ∧ ↑x10 ∉ x12.inputs) → (63 : ℕ) ≤ x5.size := by
  classical
  dsimp only at four minor ⊢
  intro C legal computes fstG sep
  have ao : IsAO2 26 C := by
    refine ⟨?_,?_,?_⟩
    · intro g hg
      obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
      exact (legal j g hj).1
    · intro j hj i hi
      have eq : C.gates[j]? = some C.gates[j] := List.getElem?_eq_getElem hj
      obtain ⟨a,b,he,_,ha,hb⟩ := (legal j _ eq).2
      have hgate : PEqualNP.MetaComplexity.NestedCover.gateAt C j = C.gates[j] := by
        change C.gates.getD j ⟨.or, []⟩ = _
        rw [List.getD_eq_getElem?_getD,eq]
        rfl
      rw [hgate] at hi
      change i ∈ C.gates[j].inputs at hi
      rw [he] at hi
      rcases List.mem_cons.mp hi with rfl | hi
      · exact ha
      · obtain rfl := List.mem_singleton.mp hi
        exact hb
    · intro g hg
      obtain ⟨j,hj⟩ := List.mem_iff_getElem?.mp hg
      obtain ⟨a,b,e,_⟩ := (legal j g hj).2
      simp [e]
  have incid : ∀ p l : Fin 13, p ∈ singerLines3 l ↔
      (p = l ∨ p = l+1 ∨ p = l+3 ∨ p = l+9) := by decide +kernel
  have hhit : ∀ x : Fin 26 → Bool, C.eval (List.ofFn x) = true ↔
      ∃ p l : Fin 13, p ∈ singerLines3 l ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 l) = true := by
    simpa only [incid] using computes
  have hf : ∀ g, C.gates.head? = some g → g.inputs.head? = some 0 := by
    intro g e
    rcases fstG g e with rfl | ⟨t,_,rfl⟩ <;> rfl
  obtain ⟨v,hv⟩ := four C ao hhit hf sep
  obtain ⟨D,hD,hcost,hsame⟩ := compress 26 v C ao
  have h59 := minor v D hD (fun x hx => (hsame x hx).symm ▸ hhit x)
  omega
