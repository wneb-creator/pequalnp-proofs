import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem PEqualNP.Outside.R_meta_2870_34
    (compile : ∀ (n : ℕ) (C : Circuit), Monotone2 C →
      (∀ j g, C.gates[j]? = some g → ∃ a b, g.inputs = [a,b] ∧ a < b ∧ b < n+j) →
      ∃ F : ℕ → Finset (Finset (Fin n)),
      (∀ i : Fin n, F i = {{i}}) ∧
      (∀ j (hj : j < C.size), ∃ a b, C.gates[j].inputs = [a,b] ∧ a < b ∧ b < n+j ∧
        F (n+j) = (if C.gates[j].op.eval [false,true] then F a ∪ F b else
          (F a).biUnion (fun u => (F b).image (u ∪ ·)))) ∧
      (∀ xs : List Bool, xs.length = n → ∀ w, (C.wires xs).getD w false = true ↔
        ∃ t ∈ F w, ∀ i ∈ t, xs.getD i.val false = true))
    (bound : ∀ (q n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I],
      100 < q → n = q^2+q+1 → (∀ l, Fintype.card {p // I p l} = q+1) →
      (∀ p r, p ≠ r → ∃! l, I p l ∧ I r l) →
      ∀ (s o : ℕ) (F : ℕ → Finset (Finset (Fin (n+n)))), o < n+n+s →
      (∀ i : Fin (n+n), F i = {{i}}) →
      (∀ j < s, ∃ a b, a < b ∧ b < n+n+j ∧
        (F (n+n+j) = F a ∪ F b ∨ F (n+n+j) = (F a).biUnion (fun u => (F b).image (u ∪ ·)))) →
      (∀ p l, I p l → ∃ t ∈ F o, t ⊆ {Fin.castAdd n p, Fin.natAdd n l}) →
      (∀ t ∈ F o, Fintype.card {l : Fin n // Fin.natAdd n l ∈ t} ≤ q →
        ∃ p l, I p l ∧ Fin.castAdd n p ∈ t ∧ Fin.natAdd n l ∈ t) → n*q ≤ 100*s) :
    have x1 : ℕ → PEqualNP.CircuitLowerBounds.Circuit → PEqualNP.CircuitLowerBounds.Gate → Prop := fun (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : PEqualNP.CircuitLowerBounds.Gate) => x3.op = PEqualNP.CircuitLowerBounds.GateOp.and ∧ ((∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.false)).getD x4 Bool.false ≠ (x2.wires (List.ofFn x6 ++ List.replicate x1 Bool.true)).getD x4 Bool.false) ∨ ∀ x4 ∈ x3.inputs, ∃ (x6 : Fin x1 → Bool), (x2.wires (List.replicate x1 Bool.false ++ List.ofFn x6)).getD x4 Bool.false ≠ (x2.wires (List.replicate x1 Bool.true ++ List.ofFn x6)).getD x4 Bool.false); ∀ (x2 x3 : ℕ) (x4 : Fin x3 → Fin x3 → Prop) [x5 : DecidableRel x4] (x6 : PEqualNP.CircuitLowerBounds.Circuit), (100 : ℕ) < x2 → x3 = x2 ^ (2 : ℕ) + x2 + (1 : ℕ) → (∀ (x9 : Fin x3), Fintype.card { x10 : Fin x3 // x4 x10 x9 } = x2 + (1 : ℕ)) → (∀ (x10 x11 : Fin x3), x10 ≠ x11 → ∃! x13 : Fin x3, x4 x10 x13 ∧ x4 x11 x13) → PEqualNP.MetaComplexity.Monotone2 x6 → x6.output < x3 + x3 + x6.size → (∀ (x13 : ℕ) (x14 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x13]? = Option.some x14 → ∃ (x16 : ℕ) (x17 : ℕ), x14.inputs = [x16, x17] ∧ x16 < x17 ∧ x17 < x3 + x3 + x13) → (∀ (x14 x15 : Fin x3), x4 x14 x15 → (PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 fun (x17 : Fin (x3 + x3)) => Decidable.decide (x17 = Fin.castAdd x3 x14 ∨ x17 = Fin.natAdd x3 x15)) = Bool.true) → (∀ (x15 : Fin (x3 + x3) → Bool), Fintype.card { x16 : Fin x3 // x15 (Fin.natAdd x3 x16) = Bool.true } ≤ x2 → (¬∃ (x17 : Fin x3) (x18 : Fin x3), x4 x17 x18 ∧ x15 (Fin.castAdd x3 x17) = Bool.true ∧ x15 (Fin.natAdd x3 x18) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x3 + x3) x6 x15 = Bool.false) → ∀ x16 ⊆ Finset.range x6.size, (1 : ℕ) ≤ x16.card → (∀ (x19 : ℕ) (x20 : PEqualNP.CircuitLowerBounds.Gate), x6.gates[x19]? = Option.some x20 → (x19 ∈ x16 ↔ x1 x3 x6 x20)) → (100 : ℕ) * x16.card < x3 * x2 → x3 * x2 ≤ (100 : ℕ) * x6.size := by
  dsimp only
  intro q n I dec C hq hn hdeg hline mono out order yes no marks sub nonempty marked few
  classical
  obtain ⟨F, atoms, steps, semantics⟩ := compile (n+n) C mono order
  have computes (x : Fin (n+n) → Bool) : C.eval (List.ofFn x) = true ↔
      ∃ t ∈ F C.output, ∀ i ∈ t, x i = true := by
    change (C.wires (List.ofFn x)).getD C.output false = true ↔ _
    simpa using semantics (List.ofFn x) List.length_ofFn C.output
  refine bound q n I hq hn hdeg hline C.size C.output F out atoms ?_ ?_ ?_
  · intro j hj
    obtain ⟨a,b,_,ab,bj,eq⟩ := steps j hj
    refine ⟨a,b,ab,bj,?_⟩
    split at eq <;> tauto
  · intro p l inc
    obtain ⟨t, ht, hit⟩ := (computes _).mp (yes p l inc)
    refine ⟨t, ht, ?_⟩
    intro i hi
    simpa only [Finset.mem_insert, Finset.mem_singleton] using of_decide_eq_true (hit i hi)
  · intro t ht small
    by_contra missing
    let x : Fin (n+n) → Bool := fun i => decide (i ∈ t)
    have falseOnTerm := no x (by simpa only [x, decide_eq_true_eq] using small)
      (by simpa only [x, decide_eq_true_eq] using missing)
    have trueOnTerm :=
      (computes x).mpr ⟨t, ht, fun i hi => decide_eq_true hi⟩
    exact Bool.noConfusion (trueOnTerm.symm.trans falseOnTerm)
