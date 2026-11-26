import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17955

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open Classical

private lemma wires_foldl_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (gs.foldl (fun acc g => acc ++ [g.op.eval (g.inputs.map fun i => acc.getD i false)]) w).getD k false =
      w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlen : k < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length := by
      simp [List.length_append]
      omega
    rw [ih _ hlen]
    rw [List.getD_eq_getElem?_getD, List.getElem?_append_left hk, ← List.getD_eq_getElem?_getD]

private lemma wires_head_getD (o : ℕ) (g₀ : Gate) (gs : List Gate) (x : List Bool) :
    (({ gates := g₀ :: gs, output := o : Circuit }).wires x).getD x.length false =
      g₀.op.eval (g₀.inputs.map fun i => x.getD i false) := by
  unfold Circuit.wires
  simp only [List.foldl_cons]
  have hlen : x.length < (x ++ [g₀.op.eval (g₀.inputs.map fun i => x.getD i false)]).length := by
    simp [List.length_append]
  rw [wires_foldl_getD_lt gs _ x.length hlen]
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _)]
  simp

private lemma getD_ofFn_ge {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : n ≤ i) :
    (List.ofFn x).getD i false = false := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp [List.length_ofFn]; omega)]
  rfl

private lemma getD_ofFn_lt {n : ℕ} (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp [hi]

private lemma nonconst_fn :
    ∃ x y : Fin 9 → Bool, (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) x ≠ (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) y := by
  refine ⟨fun _ => false, fun _ => true, ?_⟩
  decide

private lemma nonproj_fn (k : Fin 9) :
    ∃ x : Fin 9 → Bool, (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) x ≠ x k := by
  have h : ∀ m : Fin 9, (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) (fun i => decide (i = m)) ≠ (fun i => decide (i = m)) m := by
    decide
  exact ⟨fun i => decide (i = k), h k⟩

end PEqualNP.Outside.L_meta_17955

theorem PEqualNP.Outside.L_meta_17955 :
    (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit n C → (∃ x y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x ≠ PEqualNP.MetaComplexity.circuitFun n C y) → (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧ (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false) ∧ (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧ (∀ j : ℕ, j + 1 < C.gates.length → ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧ (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (n + j) = true)) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) ∨ (∃ j : Fin 9, (0 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y j)) ∨ (∃ j : Fin 9, (0 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 1)) ∨ (∃ j : Fin 9, (1 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 1 && y j)) ∨ (∃ j : Fin 9, (1 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 1 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 2)) ∨ (∃ j : Fin 9, (2 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 2 && y j)) ∨ (∃ j : Fin 9, (2 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 2 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 3)) ∨ (∃ j : Fin 9, (3 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 3 && y j)) ∨ (∃ j : Fin 9, (3 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 3 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) ∨ (∃ j : Fin 9, (4 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y j)) ∨ (∃ j : Fin 9, (4 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 5)) ∨ (∃ j : Fin 9, (5 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 5 && y j)) ∨ (∃ j : Fin 9, (5 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 5 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 6)) ∨ (∃ j : Fin 9, (6 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 6 && y j)) ∨ (∃ j : Fin 9, (6 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 6 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 7)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 && y j)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 8)) ∨ (∃ j : Fin 9, (8 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 8 && y j)) ∨ (∃ j : Fin 9, (8 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 8 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) → 16 ≤ C.size) → ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) t → 16 ≤ t := by
  intro hred h_0 h_1 h_2 h_3 h_4 h_5 h_6 h_7 h_8 t ht
  rcases ht with ⟨C₀, hC₀_fit, hC₀_size, hC₀_eval⟩
  have hC₀_fun : PEqualNP.MetaComplexity.circuitFun 9 C₀ = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) := by
    funext x
    exact hC₀_eval x
  let P : ℕ → Prop := fun s =>
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.FanInTwo C ∧
      C.size ≤ s ∧
      PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8))
  have hPt : P t := ⟨C₀, hC₀_fit, hC₀_size, hC₀_fun⟩
  have hEx : ∃ s, P s := ⟨t, hPt⟩
  classical
  let s₀ := Nat.find hEx
  have hs₀_le : s₀ ≤ t := Nat.find_min' hEx hPt
  rcases Nat.find_spec hEx with ⟨C, hC_fit, hC_size, hC_fun⟩
  have hC_min : PEqualNP.MetaComplexity.IsMinimalCircuit 9 C := by
    refine ⟨hC_fit, ?_⟩
    intro D hD_fit hD_fun
    have hPD : P D.size := ⟨D, hD_fit, le_refl _, hD_fun.trans hC_fun⟩
    exact le_trans hC_size (Nat.find_min' hEx hPD)
  have hC_nonconst :
      ∃ x y : Fin 9 → Bool,
        PEqualNP.MetaComplexity.circuitFun 9 C x ≠
        PEqualNP.MetaComplexity.circuitFun 9 C y := by
    rcases PEqualNP.Outside.L_meta_17955.nonconst_fn with ⟨x, y, hxy⟩
    refine ⟨x, y, ?_⟩
    rw [hC_fun]
    exact hxy
  have hredC := hred 9 C hC_min hC_nonconst
  have h_nc_gate := hredC.1
  have h_dist := hredC.2.1
  have h_nonempty : C.gates ≠ [] := by
    intro h_empty
    by_cases h_out : C.output < 9
    · rcases PEqualNP.Outside.L_meta_17955.nonproj_fn ⟨C.output, h_out⟩ with ⟨x, hx⟩
      have h1 : PEqualNP.MetaComplexity.circuitFun 9 C x = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 1 && x 6) || (x 2 && x 6) || (x 1 && x 7) || (x 3 && x 7) || (x 4 && x 7) || (x 0 && x 8) || (x 2 && x 8) || (x 3 && x 8) || (x 6 && x 8)) x := by
        rw [hC_fun]
      have h2 : PEqualNP.MetaComplexity.circuitFun 9 C x = x ⟨C.output, h_out⟩ := by
        unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
          PEqualNP.CircuitLowerBounds.Circuit.wires
        rw [h_empty]
        simp only [List.foldl_nil]
        exact PEqualNP.Outside.L_meta_17955.getD_ofFn_lt x C.output h_out
      exact hx (h1.symm.trans h2)
    · rcases PEqualNP.Outside.L_meta_17955.nonconst_fn with ⟨x, y, hxy⟩
      have hx0 : PEqualNP.MetaComplexity.circuitFun 9 C x = false := by
        unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
          PEqualNP.CircuitLowerBounds.Circuit.wires
        rw [h_empty]
        simp only [List.foldl_nil]
        exact PEqualNP.Outside.L_meta_17955.getD_ofFn_ge x C.output (by omega)
      have hy0 : PEqualNP.MetaComplexity.circuitFun 9 C y = false := by
        unfold PEqualNP.MetaComplexity.circuitFun PEqualNP.CircuitLowerBounds.Circuit.eval
          PEqualNP.CircuitLowerBounds.Circuit.wires
        rw [h_empty]
        simp only [List.foldl_nil]
        exact PEqualNP.Outside.L_meta_17955.getD_ofFn_ge y C.output (by omega)
      rw [hC_fun] at hx0 hy0
      exact hxy (hx0.trans hy0.symm)
  cases hC_gates : C.gates with
  | nil => exact absurd hC_gates h_nonempty
  | cons g₀ gs =>
    have hg₀_fit := hC_fit g₀ (by rw [hC_gates]; simp)
    have h0_lt : 0 < C.gates.length := by rw [hC_gates]; simp
    have h0_nc : ∃ x y : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD 9 false ≠
        (C.wires (List.ofFn y)).getD 9 false := by
      simpa using h_nc_gate 0 h0_lt
    have h0_dist : ∀ i : ℕ, i < 9 → ∃ x : Fin 9 → Bool,
        (C.wires (List.ofFn x)).getD i false ≠
        (C.wires (List.ofFn x)).getD 9 false := by
      intro i hi
      simpa using h_dist i 0 (by omega) h0_lt
    have h_wire0 : ∀ y : Fin 9 → Bool,
        (C.wires (List.ofFn y)).getD 9 false =
          g₀.op.eval (g₀.inputs.map fun i => (List.ofFn y).getD i false) := by
      intro y
      have hlen : (List.ofFn y).length = 9 := List.length_ofFn
      have hw : C = { gates := g₀ :: gs, output := C.output } := by
        cases C
        dsimp at hC_gates ⊢
        rw [hC_gates]
      conv_lhs =>
        rw [hw]
        arg 2
        rw [← hlen]
      exact PEqualNP.Outside.L_meta_17955.wires_head_getD C.output g₀ gs (List.ofFn y)
    have h_dispatch : ∀ (i : Fin 9),
        ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y i)) ∨
         (∃ j : Fin 9, i < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y i && y j)) ∨
         (∃ j : Fin 9, i < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y i || y j))) →
        16 ≤ C.size := by
      intro i hcase
      rcases i with ⟨iv, hiv⟩
      match iv with
      | 0 => exact h_0 C hC_fit hcase hC_fun
      | 1 => exact h_1 C hC_fit hcase hC_fun
      | 2 => exact h_2 C hC_fit hcase hC_fun
      | 3 => exact h_3 C hC_fit hcase hC_fun
      | 4 => exact h_4 C hC_fit hcase hC_fun
      | 5 => exact h_5 C hC_fit hcase hC_fun
      | 6 => exact h_6 C hC_fit hcase hC_fun
      | 7 => exact h_7 C hC_fit hcase hC_fun
      | 8 => exact h_8 C hC_fit hcase hC_fun
    have hC_lb : 16 ≤ C.size := by
      rcases hg₀_fit with ⟨hop, hlen⟩
      have h_no_const : ∀ b : Bool,
          ¬ (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = b) := by
        intro b hb
        rcases h0_nc with ⟨x, y, hxy⟩
        exact hxy ((hb x).trans (hb y).symm)
      have h_no_copy : ∀ (k : ℕ) (hk : k < 9),
          ¬ (∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = y ⟨k, hk⟩) := by
        intro k hk hcopy
        rcases h0_dist k hk with ⟨x, hx⟩
        have hx1 : (C.wires (List.ofFn x)).getD k false = x ⟨k, hk⟩ := by
          unfold PEqualNP.CircuitLowerBounds.Circuit.wires
          rw [hC_gates]
          simp only [List.foldl_cons]
          have hlen1 : (List.ofFn x).length = 9 := List.length_ofFn
          have hk1 : k < (List.ofFn x ++ [g₀.op.eval (g₀.inputs.map fun i => (List.ofFn x).getD i false)]).length := by
            simp; omega
          rw [PEqualNP.Outside.L_meta_17955.wires_foldl_getD_lt gs _ k hk1]
          rw [List.getD_eq_getElem?_getD, List.getElem?_append_left (by omega), ← List.getD_eq_getElem?_getD]
          exact PEqualNP.Outside.L_meta_17955.getD_ofFn_lt x k hk
        exact hx (hx1.trans (hcopy x).symm)
      rcases hop with h_op | h_op | h_op
      · -- GateOp.and
        match hin : g₀.inputs with
        | [] =>
          exfalso
          apply h_no_const true
          intro y
          rw [h_wire0 y, hin, h_op]
          rfl
        | [a] =>
          by_cases ha : a < 9
          · exfalso
            apply h_no_copy a ha
            intro y
            rw [h_wire0 y, hin, h_op]
            change ([((List.ofFn y).getD a false)]).all id = y ⟨a, ha⟩
            rw [PEqualNP.Outside.L_meta_17955.getD_ofFn_lt y a ha]
            simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true]
          · exfalso
            apply h_no_const false
            intro y
            rw [h_wire0 y, hin, h_op]
            change ([((List.ofFn y).getD a false)]).all id = false
            rw [PEqualNP.Outside.L_meta_17955.getD_ofFn_ge y a (by omega)]
            rfl
        | [a, b] =>
          by_cases ha : a < 9
          · by_cases hb : b < 9
            · rcases lt_trichotomy a b with hab | rfl | hba
              · exact h_dispatch ⟨a, ha⟩ (Or.inr (Or.inl ⟨⟨b, hb⟩, hab, fun y => by
                  rw [h_wire0 y, hin, h_op]
                  change ([(List.ofFn y).getD a false, (List.ofFn y).getD b false]).all id = (y ⟨a, ha⟩ && y ⟨b, hb⟩)
                  rw [PEqualNP.Outside.L_meta_17955.getD_ofFn_lt y a ha, PEqualNP.Outside.L_meta_17955.getD_ofFn_lt y b hb]
                  simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true]⟩))
              · exfalso
                apply h_no_copy a ha
                intro y
                rw [h_wire0 y, hin, h_op]
                change ([(List.ofFn y).getD a false, (List.ofFn y).getD a false]).all id = y ⟨a, ha⟩
                rw [PEqualNP.Outside.L_meta_17955.getD_ofFn_lt y a ha]
                simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_self]
              · exact h_dispatch ⟨b, hb⟩ (Or.inr (Or.inl ⟨⟨a, ha⟩, hba, fun y => by
                  rw [h_wire0 y, hin, h_op]
                  change ([(List.ofFn y).getD a false, (List.ofFn y).getD b false]).all id = (y ⟨b, hb⟩ && y ⟨a, ha⟩)
                  rw [PEqualNP.Outside.L_meta_17955.getD_ofFn_lt y a ha, PEqualNP.Outside.L_meta_17955.getD_ofFn_lt y b hb]
                  simp only [List.all_cons, List.all_nil, id_eq, Bool.true_and, Bool.and_comm]⟩))
            · exfalso
              apply h_no_const false
              intro y
              rw [h_wire0 y, hin, h_op]
              change ([(List.ofFn y).getD a false, (List.ofFn y).getD b false]).all id = false
              rw [PEqualNP.Outside.L_meta_17955.getD_ofFn_ge y b (by omega)]
              simp only [List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_false]
          · exfalso
            apply h_no_const false
            intro y
            rw [h_wire0 y, hin, h_op]
            change ([(List.ofFn y).getD a false, (List.ofFn y).getD b false]).all id = false
            rw [PEqualNP.Outside.L_meta_17955.getD_ofFn_ge y a (by omega)]
            rfl
        | _ :: _ :: _ :: _ =>
          rw [hin] at hlen
          simp at hlen
      · -- GateOp.or
        match hin : g₀.inputs with
        | [] =>
          exfalso
          apply h_no_const false
          intro y
          rw [h_wire0 y, hin, h_op]
          rfl
        | [a] =>
          by_cases ha : a < 9
          · exfalso
            apply h_no_copy a ha
            intro y
            rw [h_wire0 y, hin, h_op]
            change ([(List.ofFn y).getD a false]).any id = y ⟨a, ha⟩
            rw [PEqualNP.Outside.L_meta_17955.getD_ofFn_lt y a ha]
            simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false]
          · exfalso
            apply h_no_const false
            intro y
            rw [h_wire0 y, hin, h_op]
            change ([(List.ofFn y).getD a false]).any id = false
            rw [PEqualNP.Outside.L_meta_17955.getD_ofFn_ge y a (by omega)]
            rfl
        | [a, b] =>
          by_cases ha : a < 9
          · by_cases hb : b < 9
            · rcases lt_trichotomy a b with hab | rfl | hba
              · exact h_dispatch ⟨a, ha⟩ (Or.inr (Or.inr ⟨⟨b, hb⟩, hab, fun y => by
                  rw [h_wire0 y, hin, h_op]
                  change ([(List.ofFn y).getD a false, (List.ofFn y).getD b false]).any id = (y ⟨a, ha⟩ || y ⟨b, hb⟩)
                  rw [PEqualNP.Outside.L_meta_17955.getD_ofFn_lt y a ha, PEqualNP.Outside.L_meta_17955.getD_ofFn_lt y b hb]
                  simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false]⟩))
              · exfalso
                apply h_no_copy a ha
                intro y
                rw [h_wire0 y, hin, h_op]
                change ([(List.ofFn y).getD a false, (List.ofFn y).getD a false]).any id = y ⟨a, ha⟩
                rw [PEqualNP.Outside.L_meta_17955.getD_ofFn_lt y a ha]
                simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false, Bool.or_self]
              · exact h_dispatch ⟨b, hb⟩ (Or.inr (Or.inr ⟨⟨a, ha⟩, hba, fun y => by
                  rw [h_wire0 y, hin, h_op]
                  change ([(List.ofFn y).getD a false, (List.ofFn y).getD b false]).any id = (y ⟨b, hb⟩ || y ⟨a, ha⟩)
                  rw [PEqualNP.Outside.L_meta_17955.getD_ofFn_lt y a ha, PEqualNP.Outside.L_meta_17955.getD_ofFn_lt y b hb]
                  simp only [List.any_cons, List.any_nil, id_eq, Bool.false_or, Bool.or_comm]⟩))
            · exfalso
              apply h_no_copy a ha
              intro y
              rw [h_wire0 y, hin, h_op]
              change ([(List.ofFn y).getD a false, (List.ofFn y).getD b false]).any id = y ⟨a, ha⟩
              rw [PEqualNP.Outside.L_meta_17955.getD_ofFn_lt y a ha, PEqualNP.Outside.L_meta_17955.getD_ofFn_ge y b (by omega)]
              simp only [List.any_cons, List.any_nil, id_eq, Bool.or_false]
          · by_cases hb : b < 9
            · exfalso
              apply h_no_copy b hb
              intro y
              rw [h_wire0 y, hin, h_op]
              change ([(List.ofFn y).getD a false, (List.ofFn y).getD b false]).any id = y ⟨b, hb⟩
              rw [PEqualNP.Outside.L_meta_17955.getD_ofFn_ge y a (by omega), PEqualNP.Outside.L_meta_17955.getD_ofFn_lt y b hb]
              simp only [List.any_cons, List.any_nil, id_eq, Bool.false_or, Bool.or_false]
            · exfalso
              apply h_no_const false
              intro y
              rw [h_wire0 y, hin, h_op]
              change ([(List.ofFn y).getD a false, (List.ofFn y).getD b false]).any id = false
              rw [PEqualNP.Outside.L_meta_17955.getD_ofFn_ge y a (by omega), PEqualNP.Outside.L_meta_17955.getD_ofFn_ge y b (by omega)]
              rfl
        | _ :: _ :: _ :: _ =>
          rw [hin] at hlen
          simp at hlen
      · -- GateOp.not
        match hin : g₀.inputs with
        | [] =>
          exfalso
          apply h_no_const true
          intro y
          rw [h_wire0 y, hin, h_op]
          rfl
        | a :: rest =>
          by_cases ha : a < 9
          · exact h_dispatch ⟨a, ha⟩ (Or.inl (fun y => by
              rw [h_wire0 y, hin, h_op]
              change (!(((List.ofFn y).getD a false :: rest.map fun i => (List.ofFn y).getD i false).headD false)) = !(y ⟨a, ha⟩)
              rw [List.headD_cons, PEqualNP.Outside.L_meta_17955.getD_ofFn_lt y a ha]))
          · exfalso
            apply h_no_const true
            intro y
            rw [h_wire0 y, hin, h_op]
            change (!(((List.ofFn y).getD a false :: rest.map fun i => (List.ofFn y).getD i false).headD false)) = true
            rw [List.headD_cons, PEqualNP.Outside.L_meta_17955.getD_ofFn_ge y a (by omega)]
            rfl
    exact le_trans hC_lb (le_trans hC_size hs₀_le)
