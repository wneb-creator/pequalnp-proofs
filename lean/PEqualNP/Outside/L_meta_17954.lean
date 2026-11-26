import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17954_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- Later gates do not change the wires that already exist. -/
theorem getD_foldl (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i false
      = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [List.foldl_cons, ih _ i (by simp; omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

/-- The first gate wire is the first gate applied to the input wires. -/
theorem wire_first (C : Circuit) (g : Gate) (rest : List Gate) (hC : C.gates = g :: rest)
    (x : List Bool) :
    (C.wires x).getD x.length false = g.op.eval (g.inputs.map fun i => x.getD i false) := by
  unfold Circuit.wires
  rw [hC, List.foldl_cons, getD_foldl _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD]

/-- An input wire carries its input bit. -/
theorem val_lt {n : ℕ} (y : Fin n → Bool) (a : ℕ) (h : a < n) :
    (List.ofFn y).getD a false = y ⟨a, h⟩ := by
  simp [List.getD_eq_getElem?_getD, h]

/-- A wire beyond the inputs reads false when there is no gate before it. -/
theorem val_ge {n : ℕ} (y : Fin n → Bool) (a : ℕ) (h : ¬ a < n) :
    (List.ofFn y).getD a false = false := by
  simp [List.getD_eq_getElem?_getD, h]

/-- A non-constant first gate that differs from every input is a NOT of an input, or an AND or
an OR of two different inputs. -/
theorem classify (n : ℕ) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp)) (hlen : g.inputs.length ≤ 2)
    (W : (Fin n → Bool) → Bool)
    (hW : ∀ y, W y = g.op.eval (g.inputs.map fun i => (List.ofFn y).getD i false))
    (hnc : ∃ x y, W x ≠ W y)
    (hne : ∀ i, i < n → ∃ x : Fin n → Bool, (List.ofFn x).getD i false ≠ W x) :
    ∃ i : Fin n, (∀ y, W y = !(y i)) ∨ (∃ j, i < j ∧ ∀ y, W y = (y i && y j)) ∨
      (∃ j, i < j ∧ ∀ y, W y = (y i || y j)) := by
  have hconst : ∀ c : Bool, (∀ y, W y = c) → False := by
    intro c hc
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((hc x).trans (hc y).symm)
  have hwire : ∀ a, a < n → (∀ y, W y = (List.ofFn y).getD a false) → False := by
    intro a ha h
    obtain ⟨x, hx⟩ := hne a ha
    exact hx (h x).symm
  have hnot : ∀ a, (∀ y, W y = !((List.ofFn y).getD a false)) →
      ∃ i : Fin n, (∀ y, W y = !(y i)) ∨ (∃ j, i < j ∧ ∀ y, W y = (y i && y j)) ∨
      (∃ j, i < j ∧ ∀ y, W y = (y i || y j)) := by
    intro a h
    by_cases ha : a < n
    · exact ⟨⟨a, ha⟩, Or.inl fun y => by rw [h y, val_lt y a ha]⟩
    · exact (hconst true fun y => by rw [h y, val_ge y a ha]; rfl).elim
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hW hlen
  match ins, hlen, hW with
  | [], _, hW =>
    rcases hop with rfl | rfl | rfl
    · exact (hconst true fun y => by rw [hW y]; rfl).elim
    · exact (hconst false fun y => by rw [hW y]; rfl).elim
    · exact (hconst true fun y => by rw [hW y]; rfl).elim
  | [a], _, hW =>
    rcases hop with rfl | rfl | rfl
    · by_cases ha : a < n
      · exact (hwire a ha fun y => by rw [hW y]; simp [GateOp.eval]).elim
      · exact (hconst false fun y => by rw [hW y]; simp [GateOp.eval, ha]).elim
    · by_cases ha : a < n
      · exact (hwire a ha fun y => by rw [hW y]; simp [GateOp.eval]).elim
      · exact (hconst false fun y => by rw [hW y]; simp [GateOp.eval, ha]).elim
    · exact hnot a fun y => by rw [hW y]; simp [GateOp.eval]
  | [a, b], _, hW =>
    rcases hop with rfl | rfl | rfl
    · by_cases ha : a < n
      · by_cases hb : b < n
        · rcases lt_trichotomy a b with h | h | h
          · exact ⟨⟨a, ha⟩, Or.inr (Or.inl ⟨⟨b, hb⟩, h, fun y => by
              rw [hW y]; simp [GateOp.eval, ha, hb]⟩)⟩
          · subst h
            exact (hwire a ha fun y => by rw [hW y]; simp [GateOp.eval]).elim
          · exact ⟨⟨b, hb⟩, Or.inr (Or.inl ⟨⟨a, ha⟩, h, fun y => by
              rw [hW y]; simp [GateOp.eval, ha, hb, Bool.and_comm]⟩)⟩
        · exact (hconst false fun y => by rw [hW y]; simp [GateOp.eval, hb]).elim
      · exact (hconst false fun y => by rw [hW y]; simp [GateOp.eval, ha]).elim
    · by_cases ha : a < n
      · by_cases hb : b < n
        · rcases lt_trichotomy a b with h | h | h
          · exact ⟨⟨a, ha⟩, Or.inr (Or.inr ⟨⟨b, hb⟩, h, fun y => by
              rw [hW y]; simp [GateOp.eval, ha, hb]⟩)⟩
          · subst h
            exact (hwire a ha fun y => by rw [hW y]; simp [GateOp.eval]).elim
          · exact ⟨⟨b, hb⟩, Or.inr (Or.inr ⟨⟨a, ha⟩, h, fun y => by
              rw [hW y]; simp [GateOp.eval, ha, hb, Bool.or_comm]⟩)⟩
        · exact (hwire a ha fun y => by rw [hW y]; simp [GateOp.eval, hb]).elim
      · by_cases hb : b < n
        · exact (hwire b hb fun y => by rw [hW y]; simp [GateOp.eval, ha]).elim
        · exact (hconst false fun y => by
            rw [hW y]; simp [GateOp.eval, ha, hb]).elim
    · exact hnot a fun y => by rw [hW y]; simp [GateOp.eval]
  | _ :: _ :: _ :: _, hlen, _ => simp at hlen

/-- Among the fan-in-two circuits of a function there is one of least size. -/
theorem exists_min (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit) (hC : FanInTwo C)
    (hf : circuitFun n C = f) :
    ∃ D, IsMinimalCircuit n D ∧ circuitFun n D = f ∧ D.size ≤ C.size := by
  classical
  have hP : ∃ s, ∃ D, FanInTwo D ∧ circuitFun n D = f ∧ D.size = s := ⟨C.size, C, hC, hf, rfl⟩
  obtain ⟨D, hD, hDf, hDs⟩ := Nat.find_spec hP
  refine ⟨D, ⟨hD, fun E hE hEf => ?_⟩, hDf, ?_⟩
  · rw [hDs]; exact Nat.find_min' hP ⟨E, hE, hEf.trans hDf, rfl⟩
  · rw [hDs]; exact Nat.find_min' hP ⟨C, hC, hf, rfl⟩

/-- The reduction: if least circuits are reduced and every first-gate case gives the bound,
the bound holds for every circuit of the function. -/
theorem core (n : ℕ) (f : (Fin n → Bool) → Bool) (b : ℕ)
    (hnc : ∃ x y, f x ≠ f y)
    (hproj : ∀ o : ℕ, ¬ ∀ x : Fin n → Bool, (List.ofFn x).getD o false = f x)
    (H1 : ∀ C : Circuit, IsMinimalCircuit n C →
      (∃ x y : Fin n → Bool, circuitFun n C x ≠ circuitFun n C y) →
      (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool,
        (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧
      (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool,
        (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false))
    (H2 : ∀ i : Fin n, ∀ C : Circuit, FanInTwo C →
      ((∀ y : Fin n → Bool, (C.wires (List.ofFn y)).getD n false = !(y i)) ∨
        (∃ j : Fin n, i < j ∧ ∀ y : Fin n → Bool,
          (C.wires (List.ofFn y)).getD n false = (y i && y j)) ∨
        (∃ j : Fin n, i < j ∧ ∀ y : Fin n → Bool,
          (C.wires (List.ofFn y)).getD n false = (y i || y j))) →
      circuitFun n C = f → b ≤ C.size) :
    ∀ t : ℕ, HasCircuitSize n f t → b ≤ t := by
  rintro t ⟨C, hC, hsz, hev⟩
  obtain ⟨D, hmin, hDf, hDs⟩ := exists_min n f C hC (funext hev)
  obtain ⟨hA, hB⟩ := H1 D hmin (by rw [hDf]; exact hnc)
  refine le_trans ?_ (le_trans hDs hsz)
  rcases hg : D.gates with _ | ⟨g, rest⟩
  · exfalso
    refine hproj D.output fun x => ?_
    have h := congrFun hDf x
    simpa [circuitFun, Circuit.eval, Circuit.wires, hg] using h
  · have hlen : 0 < D.gates.length := by rw [hg]; simp
    have hgm := hmin.1 g (by rw [hg]; simp)
    have hw : ∀ y : Fin n → Bool, (D.wires (List.ofFn y)).getD n false
        = g.op.eval (g.inputs.map fun i => (List.ofFn y).getD i false) := by
      intro y
      have h := wire_first D g rest hg (List.ofFn y)
      simpa using h
    have hA0 := hA 0 hlen
    have hB0 : ∀ i, i < n → ∃ x : Fin n → Bool,
        (List.ofFn x).getD i false ≠ (D.wires (List.ofFn x)).getD n false := by
      intro i hi
      obtain ⟨x, hx⟩ := hB i 0 (by omega) hlen
      refine ⟨x, ?_⟩
      have h1 : (D.wires (List.ofFn x)).getD i false = (List.ofFn x).getD i false :=
        getD_foldl D.gates (List.ofFn x) i (by simpa using hi)
      rw [h1] at hx
      simpa using hx
    obtain ⟨i, hi⟩ := classify n g hgm.1 hgm.2
      (fun y => (D.wires (List.ofFn y)).getD n false) hw (by simpa using hA0) hB0
    exact H2 i D hmin.1 hi hDf

end PEqualNP.Outside.L_meta_17954_aux

theorem PEqualNP.Outside.L_meta_17954 : (∀ (n : ℕ) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.IsMinimalCircuit n C → (∃ x y : Fin n → Bool, PEqualNP.MetaComplexity.circuitFun n C x ≠ PEqualNP.MetaComplexity.circuitFun n C y) → (∀ j : ℕ, j < C.gates.length → ∃ x y : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false ≠ (C.wires (List.ofFn y)).getD (n + j) false) ∧ (∀ i j : ℕ, i < n + j → j < C.gates.length → ∃ x : Fin n → Bool, (C.wires (List.ofFn x)).getD i false ≠ (C.wires (List.ofFn x)).getD (n + j) false) ∧ (C.gates ≠ [] → C.output + 1 = n + C.gates.length) ∧ (∀ j : ℕ, j + 1 < C.gates.length → ∃ p ∈ C.gates.zipIdx, n + j < n + p.2 ∧ (PEqualNP.CircuitLowerBounds.GateOp.casesOn (motive := fun _ => List ℕ) p.1.op p.1.inputs p.1.inputs (p.1.inputs.take 1) (fun _ => p.1.inputs) p.1.inputs).contains (n + j) = true)) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 0)) ∨ (∃ j : Fin 9, (0 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 && y j)) ∨ (∃ j : Fin 9, (0 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 0 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 5 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 1)) ∨ (∃ j : Fin 9, (1 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 1 && y j)) ∨ (∃ j : Fin 9, (1 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 1 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 5 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 2)) ∨ (∃ j : Fin 9, (2 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 2 && y j)) ∨ (∃ j : Fin 9, (2 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 2 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 5 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 3)) ∨ (∃ j : Fin 9, (3 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 3 && y j)) ∨ (∃ j : Fin 9, (3 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 3 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 5 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 4)) ∨ (∃ j : Fin 9, (4 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 && y j)) ∨ (∃ j : Fin 9, (4 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 4 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 5 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 5)) ∨ (∃ j : Fin 9, (5 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 5 && y j)) ∨ (∃ j : Fin 9, (5 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 5 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 5 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 6)) ∨ (∃ j : Fin 9, (6 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 6 && y j)) ∨ (∃ j : Fin 9, (6 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 6 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 5 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 7)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 && y j)) ∨ (∃ j : Fin 9, (7 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 7 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 5 && x 8)) → 16 ≤ C.size) → (∀ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo C → ((∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = !(y 8)) ∨ (∃ j : Fin 9, (8 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 8 && y j)) ∨ (∃ j : Fin 9, (8 : Fin 9) < j ∧ ∀ y : Fin 9 → Bool, (C.wires (List.ofFn y)).getD 9 false = (y 8 || y j))) → PEqualNP.MetaComplexity.circuitFun 9 C = (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 5 && x 8)) → 16 ≤ C.size) → ∀ t : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 9 (fun x : Fin 9 → Bool => (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 1 && x 7) || (x 2 && x 7) || (x 4 && x 7) || (x 1 && x 8) || (x 3 && x 8) || (x 5 && x 8)) t → 16 ≤ t := by
  intro H1 h0 h1 h2 h3 h4 h5 h6 h7 h8
  refine PEqualNP.Outside.L_meta_17954_aux.core 9 _ 16 ⟨fun _ => true, fun _ => false, by decide⟩
    ?_ (fun C hmin hnc => ⟨(H1 9 C hmin hnc).1, (H1 9 C hmin hnc).2.1⟩) ?_
  · intro o h
    by_cases ho : o < 9
    · have h9 := h (fun k => decide (k.val = o))
      rw [PEqualNP.Outside.L_meta_17954_aux.val_lt _ o ho] at h9
      interval_cases o <;> simp at h9
    · have h9 := h (fun _ => true)
      rw [PEqualNP.Outside.L_meta_17954_aux.val_ge _ o ho] at h9
      simp at h9
  · intro i
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
    · exact h3
    · exact h4
    · exact h5
    · exact h6
    · exact h7
    · exact h8
