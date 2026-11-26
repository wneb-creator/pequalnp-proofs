import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxRecDepth 6000 in
set_option maxHeartbeats 3000000 in
theorem PEqualNP.Outside.R_meta_6083_2
    (hAnd : ∀ (D : Circuit) (a b : Nat), FanInTwo D → D.size ≤ 17 →
      11 ≤ a → a < b → b < 11 + D.size → ¬ ∀ x : Fin 10 → Bool,
        let w := D.wires (List.ofFn x ++ [!x 0])
        (w.getD a false && w.getD b false) = decide (∃ i j : Fin 10,
          x i = true ∧ x j = true ∧ (([50,69,138,276,521,385,770,548,104,208] : List Nat).getD i.val 0).testBit j.val = true))
    (hOr : ∀ (D : Circuit) (a b : Nat), FanInTwo D → D.size ≤ 17 →
      11 ≤ a → a < b → b < 11 + D.size → ¬ ∀ x : Fin 10 → Bool,
        let w := D.wires (List.ofFn x ++ [!x 0])
        (w.getD a false || w.getD b false) = decide (∃ i j : Fin 10,
          x i = true ∧ x j = true ∧ (([50,69,138,276,521,385,770,548,104,208] : List Nat).getD i.val 0).testBit j.val = true))
    (hNot : ∀ (D : Circuit) (a : Nat), FanInTwo D → D.size ≤ 17 →
      11 ≤ a → a < 11 + D.size → ¬ ∀ x : Fin 10 → Bool,
        (!(D.wires (List.ofFn x ++ [!x 0])).getD a false) = decide (∃ i j : Fin 10,
          x i = true ∧ x j = true ∧ (([50,69,138,276,521,385,770,548,104,208] : List Nat).getD i.val 0).testBit j.val = true)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)) (x3 : Bool → Bool),   PEqualNP.MetaComplexity.FanInTwo x1 →     x1.size ≤ (18 : ℕ) →       have x6 : (Fin (10 : ℕ) → Bool) → Bool := fun (x6 : Fin (10 : ℕ) → Bool) => x1.eval (List.ofFn (x6 ∘ x2) ++ [x3 (x6 (0 : Fin (10 : ℕ)))]);       have x7 : Fin (10 : ℕ) → Fin (10 : ℕ) → Bool := fun (x7 x8 : Fin (10 : ℕ)) => ([(50 : ℕ), (69 : ℕ), (138 : ℕ), (276 : ℕ), (521 : ℕ), (385 : ℕ), (770 : ℕ), (548 : ℕ), (104 : ℕ), (208 : ℕ)].getD ↑x7 (0 : ℕ)).testBit ↑x8;       Monotone x6 → (∀ (x9 : Fin (10 : ℕ) ≃ Fin (10 : ℕ)), (∀ (x10 x11 : Fin (10 : ℕ)), x7 (x9 x10) (x9 x11) = x7 x10 x11) → ∀ (x11 : Fin (10 : ℕ) → Bool), x6 (x11 ∘ ⇑x9) = x6 x11) → (∀ (x10 x11 x12 : Fin (10 : ℕ)) (x13 x14 : Bool), x10 ≠ x11 → x10 ≠ x12 → x11 ≠ x12 → ¬(x13 = Bool.true ∧ x14 = Bool.true ∧ x7 x11 x12 = Bool.true) → ∃ (x19 : Fin (10 : ℕ) → Bool), x19 x11 = x13 ∧ x19 x12 = x14 ∧ ∀ (x20 : Bool), x6 (Function.update x19 x10 x20) = x20) → ∃ (x11 : Fin (3 : ℕ)), (x6 fun (x12 : Fin (10 : ℕ)) => ([(3 : ℕ), (50 : ℕ), (116 : ℕ)].getD ↑x11 (0 : ℕ)).testBit ↑x12) ≠ Decidable.decide (↑x11 = (0 : ℕ)) := by
  intro C σ u fan budget
  dsimp only
  intro mono sym _pivotal
  by_contra absent
  let F := fun x : Fin 10 → Bool => C.eval (List.ofFn (x ∘ σ) ++ [u (x 0)])
  change Monotone F at mono
  have agree : ∀ k : Fin 3, F (fun i => (([3,50,116] : List Nat).getD k.val 0).testBit i.val) = decide (k.val = 0) := by
    intro k
    by_contra different
    exact absent ⟨k, different⟩
  -- The three probes come from R_meta_1884_412 by Elias Munk.
  -- The mask table records one automorphism from a probe to each edge or maximal independent set.
  let adj (i j : Fin 10) := (([50,69,138,276,521,385,770,548,104,208] : List Nat).getD i.val 0).testBit j.val
  let row (m : Nat) (i : Fin 10) := m.testBit i.val
  let edge (x : Fin 10 → Bool) := decide (∃ i j : Fin 10, x i = true ∧ x j = true ∧ adj i j = true)
  let chart : List (Nat × Nat × List (Fin 10)) := [
    (3, 3, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
    (17, 3, [0, 4, 3, 2, 1, 5, 9, 8, 7, 6]),
    (33, 3, [0, 5, 7, 2, 1, 4, 8, 9, 3, 6]),
    (6, 3, [1, 2, 3, 4, 0, 6, 7, 8, 9, 5]),
    (66, 3, [1, 6, 8, 3, 2, 0, 9, 5, 4, 7]),
    (12, 3, [2, 3, 4, 0, 1, 7, 8, 9, 5, 6]),
    (132, 3, [2, 7, 5, 0, 1, 3, 9, 8, 4, 6]),
    (24, 3, [3, 4, 0, 1, 2, 8, 9, 5, 6, 7]),
    (264, 3, [3, 8, 5, 0, 4, 2, 6, 7, 1, 9]),
    (528, 3, [4, 9, 6, 1, 0, 3, 7, 8, 2, 5]),
    (160, 3, [5, 7, 2, 1, 0, 8, 9, 3, 6, 4]),
    (288, 3, [5, 8, 3, 2, 7, 0, 6, 4, 1, 9]),
    (320, 3, [6, 8, 3, 2, 1, 9, 5, 4, 7, 0]),
    (576, 3, [6, 9, 4, 0, 1, 8, 7, 3, 5, 2]),
    (640, 3, [7, 9, 4, 0, 5, 2, 6, 3, 1, 8]),
    (50, 50, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
    (69, 50, [1, 0, 4, 3, 2, 6, 5, 9, 8, 7]),
    (104, 50, [8, 3, 2, 1, 6, 5, 4, 7, 0, 9]),
    (116, 116, [0, 1, 2, 3, 4, 5, 6, 7, 8, 9]),
    (138, 50, [2, 1, 0, 4, 3, 7, 6, 5, 9, 8]),
    (201, 116, [1, 2, 3, 4, 0, 6, 7, 8, 9, 5]),
    (208, 50, [9, 4, 0, 1, 6, 7, 3, 5, 2, 8]),
    (276, 50, [3, 2, 1, 0, 4, 8, 7, 6, 5, 9]),
    (385, 50, [5, 0, 1, 2, 7, 8, 4, 6, 3, 9]),
    (402, 116, [0, 5, 7, 2, 1, 4, 8, 9, 3, 6]),
    (521, 50, [4, 0, 1, 2, 3, 9, 5, 6, 7, 8]),
    (548, 50, [7, 2, 1, 0, 5, 9, 3, 6, 4, 8]),
    (554, 116, [0, 4, 3, 2, 1, 5, 9, 8, 7, 6]),
    (770, 50, [6, 1, 0, 4, 9, 8, 2, 5, 3, 7]),
    (773, 116, [1, 6, 8, 3, 2, 0, 9, 5, 4, 7])]
  let record (k : Fin 30) := chart.getD k.val (0, 0, [])
  let target (k : Fin 30) := (record k).1
  let seed (k : Fin 30) := (record k).2.1
  let perm (k : Fin 30) (i : Fin 10) := (record k).2.2.getD i.val 0
  let hits (z : Nat) (k : Fin 30) : Bool :=
    if seed k = 3 then decide (z &&& target k = target k) else decide (z &&& target k = z)
  have chartOk : ∀ k : Fin 30,
      (∀ i j, perm k i = perm k j → i = j) ∧
      (∀ i j, adj (perm k i) (perm k j) = adj i j) ∧
      (∀ i, row (target k) (perm k i) = row (seed k) i) ∧
      (seed k = 3 ∨ seed k = 50 ∨ seed k = 116) ∧
      edge (row (target k)) = decide (seed k = 3) := by
    intro k
    fin_cases k <;> decide +kernel
  have cover : ∀ b : Fin 32, ((List.range 32).all fun j =>
      (List.finRange 30).any (hits (b.val * 32 + j))) = true := by
    intro b
    fin_cases b <;> decide +kernel
  have seedValue : ∀ k : Fin 30, F (row (seed k)) = decide (seed k = 3) := by
    intro k
    rcases (chartOk k).2.2.2.1 with h | h | h
    · rw [h]; exact agree 0
    · rw [h]; exact agree 1
    · rw [h]; exact agree 2
  have chartValue (k : Fin 30) : F (row (target k)) = decide (seed k = 3) := by
    obtain ⟨inj, aut, sends, _, _⟩ := chartOk k
    let e : Fin 10 ≃ Fin 10 := Equiv.ofBijective (perm k) ⟨inj, Finite.surjective_of_injective inj⟩
    have h := sym e aut (row (target k))
    rw [show row (target k) ∘ e = row (seed k) from funext sends] at h
    exact h.symm.trans (seedValue k)
  have edgeMono : Monotone edge := by
    intro x y hxy
    apply Bool.le_iff_imp.mpr
    intro hx
    obtain ⟨i, j, hi, hj, hij⟩ := of_decide_eq_true hx
    exact decide_eq_true ⟨i, j, Bool.le_iff_imp.mp (hxy i) hi, Bool.le_iff_imp.mp (hxy j) hj, hij⟩
  have decode (x : Fin 10 → Bool) : ∃ z : Nat, z < 1024 ∧ row z = x := by
    let v := BitVec.ofBoolListLE (List.ofFn x)
    have bound : v.toNat < 1024 := by
      calc v.toNat < 2 ^ (List.ofFn x).length := v.isLt
           _ = 1024 := by rw [List.length_ofFn]; rfl
    refine ⟨v.toNat, bound, funext fun i => ?_⟩
    change v.getLsbD i.val = x i
    rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
  have classify : ∀ x, F x = edge x := by
    intro x
    obtain ⟨z, hz, rfl⟩ := decode x
    have h := List.all_eq_true.mp (cover ⟨z / 32, by omega⟩) (z % 32) (by simp; omega)
    change (List.finRange 30).any (hits (z / 32 * 32 + z % 32)) = true at h
    rw [show z / 32 * 32 + z % 32 = z by omega] at h
    obtain ⟨k, _, hk⟩ := List.any_eq_true.mp h
    have val := chartValue k
    have ref := (chartOk k).2.2.2.2
    by_cases pos : seed k = 3
    · have sub : z &&& target k = target k := by simpa [hits, pos] using hk
      have le : row (target k) ≤ row z := by
        intro i
        have hb := congrArg (fun n : Nat => n.testBit i.val) sub
        simpa [row, Bool.le_iff_imp, Bool.and_eq_right_iff_imp] using hb.symm
      simp only [pos, decide_true] at val ref
      have hF := mono le
      have hE := edgeMono le
      rw [val] at hF
      rw [ref] at hE
      exact (Bool.le_iff_imp.mp hF rfl).trans (Bool.le_iff_imp.mp hE rfl).symm
    · have sub : z &&& target k = z := by simpa [hits, pos] using hk
      have le : row z ≤ row (target k) := by
        intro i
        have hb := congrArg (fun n : Nat => n.testBit i.val) sub
        simpa [row, Bool.le_iff_imp, Bool.and_eq_left_iff_imp] using hb.symm
      simp only [pos, decide_false] at val ref
      have hF := mono le
      have hE := edgeMono le
      rw [val] at hF
      rw [ref] at hE
      have bot (b : Bool) (hb : b ≤ false) : b = false := by
        cases b
        · rfl
        · exact (Bool.false_ne_true (Bool.le_iff_imp.mp hb rfl)).elim
      exact (bot _ hF).trans (bot _ hE).symm
  let input (x : Fin 10 → Bool) := List.ofFn x ++ [!x 0]
  let step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have inputLen (x : Fin 10 → Bool) : (input x).length = 11 := by simp [input]
  have wireLen (gs : List Gate) (w : List Bool) : (gs.foldl step w).length = w.length + gs.length := by
    induction gs generalizing w with
    | nil => simp
    | cons g gs ih => rw [List.foldl_cons, ih]; simp [step]; omega
  have inputWire (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
      (gs.foldl step w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      rw [List.foldl_cons, ih _ (by simp [step]; omega)]
      exact List.getD_append _ _ _ _ hi
  have zeroEdge : edge (row 0) = false := by decide +kernel
  have oneEdge : edge (row 3) = true := by decide +kernel
  have witnesses : ∀ i : Fin 11,
      let off := if i.val = 10 then 0 else 2 ^ i.val
      let on := if i.val = 10 then 3 else if i.val < 2 then 12 else 3
      edge (row off) = false ∧ (input (row off)).getD i.val false = true ∧
        edge (row on) = true ∧ (input (row on)).getD i.val false = false := by
    decide +kernel

  -- Each old input denotes a canonical wire or a constant. Keep the gate indices unchanged.
  -- The semantically equivalent input normalization was posed in R_meta_1884_773 by m-simonelli.
  let m (i : Nat) : Bool ⊕ Nat :=
    if h : i < 10 then Sum.inr (σ ⟨i, h⟩).val else
    if i = 10 then
      if u false = u true then Sum.inl (u false) else if u false then Sum.inr 10 else Sum.inr 0
    else Sum.inr i
  let val (w : List Bool) : Bool ⊕ Nat → Bool := Sum.elim id (fun i => w.getD i false)
  let pick : Bool ⊕ Nat → Option Nat := Sum.elim (fun _ => none) some
  let lowerGate (op : GateOp) (as : List (Bool ⊕ Nat)) : Gate :=
    GateOp.casesOn op
      (if Sum.inl false ∈ as then ⟨.or, []⟩ else ⟨.and, as.filterMap pick⟩)
      (if Sum.inl true ∈ as then ⟨.and, []⟩ else ⟨.or, as.filterMap pick⟩)
      (as.head?.elim ⟨.and, []⟩ (Sum.elim (fun b => ⟨if b then .or else .and, []⟩) (fun i => ⟨.not, [i]⟩)))
      (fun _ => ⟨.or, []⟩)
      ⟨.or, []⟩
  let adapt (g : Gate) := lowerGate g.op (g.inputs.map m)
  let valid (g : Gate) := g.op ∈ ({GateOp.and, .or, .not} : Set GateOp) ∧ g.inputs.length ≤ 2
  -- Use definitional equations without generating equations for the underlying definitions.
  have evalAnd (w : List Bool) : GateOp.and.eval w = w.all id := rfl
  have evalOr (w : List Bool) : GateOp.or.eval w = w.any id := rfl
  have evalNot (w : List Bool) : GateOp.not.eval w = !(w.headD false) := rfl
  have lowerAnd (as : List (Bool ⊕ Nat)) :
      lowerGate .and as = if Sum.inl false ∈ as then ⟨.or, []⟩ else ⟨.and, as.filterMap pick⟩ := rfl
  have lowerOr (as : List (Bool ⊕ Nat)) :
      lowerGate .or as = if Sum.inl true ∈ as then ⟨.and, []⟩ else ⟨.or, as.filterMap pick⟩ := rfl
  have dropRef (b : Bool) (as : List (Bool ⊕ Nat)) :
      (Sum.inl b :: as).filterMap pick = as.filterMap pick := rfl
  have keepRef (i : Nat) (as : List (Bool ⊕ Nat)) :
      (Sum.inr i :: as).filterMap pick = i :: as.filterMap pick := rfl
  have lowerValid (op : GateOp) (as : List (Bool ⊕ Nat)) (hlen : as.length ≤ 2) :
      valid (lowerGate op as) := by
    have cnt := (List.length_filterMap_le (f := pick) (l := as)).trans hlen
    cases op with
    | and => by_cases q : Sum.inl false ∈ as <;> simp [lowerGate, valid, q, cnt]
    | or => by_cases q : Sum.inl true ∈ as <;> simp [lowerGate, valid, q, cnt]
    | not =>
      cases as with
      | nil => simp [lowerGate, valid]
      | cons a as =>
        rcases a with b | i
        · cases b <;> simp [lowerGate, valid]
        · simp [lowerGate, valid]
    | mod _ => simp [lowerGate, valid]
    | maj => simp [lowerGate, valid]
  have allSound (w : List Bool) (as : List (Bool ⊕ Nat)) :
      (as.map (val w)).all id =
        if Sum.inl false ∈ as then false else ((as.filterMap pick).map fun i => w.getD i false).all id := by
    induction as with
    | nil => rfl
    | cons a as ih =>
      rw [List.map_cons, List.all_cons, ih]
      rcases a with b | i
      · rw [dropRef]
        cases b <;> by_cases q : Sum.inl false ∈ as <;> simp (config := { iota := false }) [val, q]
      · rw [keepRef]
        by_cases q : Sum.inl false ∈ as <;> simp (config := { iota := false }) [val, q]
  have anySound (w : List Bool) (as : List (Bool ⊕ Nat)) :
      (as.map (val w)).any id =
        if Sum.inl true ∈ as then true else ((as.filterMap pick).map fun i => w.getD i false).any id := by
    induction as with
    | nil => rfl
    | cons a as ih =>
      rw [List.map_cons, List.any_cons, ih]
      rcases a with b | i
      · rw [dropRef]
        cases b <;> by_cases q : Sum.inl true ∈ as <;> simp (config := { iota := false }) [val, q]
      · rw [keepRef]
        by_cases q : Sum.inl true ∈ as <;> simp (config := { iota := false }) [val, q]
  have lowerSound (w : List Bool) (op : GateOp) (as : List (Bool ⊕ Nat))
      (hop : op ∈ ({GateOp.and, .or, .not} : Set GateOp)) :
      op.eval (as.map (val w)) = (lowerGate op as).op.eval
        ((lowerGate op as).inputs.map fun i => w.getD i false) := by
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with rfl | rfl | rfl
    · rw [evalAnd, allSound, lowerAnd]
      by_cases q : Sum.inl false ∈ as
      · simp (config := { iota := false }) only [ite_eq_left q] <;> rfl
      · simp (config := { iota := false }) only [ite_eq_right q] <;> rfl
    · rw [evalOr, anySound, lowerOr]
      by_cases q : Sum.inl true ∈ as
      · simp (config := { iota := false }) only [ite_eq_left q] <;> rfl
      · simp (config := { iota := false }) only [ite_eq_right q] <;> rfl
    · cases as with
      | nil => rfl
      | cons a as =>
        rcases a with b | i
        · cases b <;> rfl
        · rfl
  have mHigh (i : Nat) (hi : 11 ≤ i) : m i = Sum.inr i := by
    simp [m, show ¬i < 10 by omega, show i ≠ 10 by omega]
  have mLow (i j : Nat) (hi : i < 11) (e : m i = Sum.inr j) : j < 11 := by
    by_cases h : i < 10
    · have eq : (σ ⟨i,h⟩).val = j := by simpa [m, h] using e
      rw [← eq]; exact (σ ⟨i,h⟩).isLt.trans (by decide)
    · have h' : i = 10 := by omega
      subst i
      have fixed : m 10 = (if u false = u true then Sum.inl (u false)
          else if u false then Sum.inr 10 else Sum.inr 0) := by simp [m]
      rw [fixed] at e
      by_cases same : u false = u true
      · rw [ite_eq_left same] at e
        cases e
      · rw [ite_eq_right same] at e
        by_cases bit : u false = true
        · rw [ite_eq_left bit] at e
          have eq := Sum.inr.inj e
          omega
        · rw [ite_eq_right bit] at e
          have eq := Sum.inr.inj e
          omega
  have initial (x : Fin 10 → Bool) (i : Nat) :
      (List.ofFn (x ∘ σ) ++ [u (x 0)]).getD i false = val (input x) (m i) := by
    by_cases hi : i < 10
    · rw [List.getD_append _ _ _ _ (by simpa using hi)]
      simp only [m, dite_eq_left hi, val, Sum.elim_inr, input]
      rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem (List.ofFn (x ∘ σ)) _ (by simpa using hi),
        List.getD_eq_getElem (List.ofFn x) _ (by simp), List.getElem_ofFn, List.getElem_ofFn]
      rfl
    · by_cases hj : i = 10
      · subst i
        have og : (List.ofFn (x ∘ σ) ++ [u (x 0)]).getD 10 false = u (x 0) := by simp
        have new10 : (input x).getD 10 false = !x 0 := by simp [input]
        have new0 : (input x).getD 0 false = x 0 := by
          change (List.ofFn x ++ [!x 0]).getD 0 false = x 0
          rw [List.getD_append _ _ _ _ (by simp), List.getD_eq_getElem _ _ (by simp), List.getElem_ofFn]
          rfl
        rw [og]
        cases a : u false <;> cases b : u true <;> cases c : x 0 <;>
          simp [m, val, a, b, c, new10, new0, -List.getD_eq_getElem?_getD]
      · have ge : 11 ≤ i := by omega
        rw [mHigh _ ge]
        change (List.ofFn (x ∘ σ) ++ [u (x 0)]).getD i false = (input x).getD i false
        rw [List.getD_eq_default (List.ofFn (x ∘ σ) ++ [u (x 0)]) _ (by simpa using ge),
          List.getD_eq_default (input x) _ (by simpa [input] using ge)]
  let related (w v : List Bool) := w.length = v.length ∧ 11 ≤ w.length ∧
    ∀ i, w.getD i false = val v (m i)
  have stepRel (w v : List Bool) (h : related w v) (b : Bool) : related (w ++ [b]) (v ++ [b]) := by
    obtain ⟨len, lo, eq⟩ := h
    refine ⟨by simp [len], by simp; omega, fun i => ?_⟩
    by_cases hi : i < 11
    · rw [List.getD_append _ _ _ _ (by omega : i < w.length), eq]
      cases mi : m i with
      | inl c => simp [val]
      | inr j =>
        have jlt := mLow i j hi mi
        simp only [val, Sum.elim_inr]
        exact (List.getD_append _ _ _ _ (by omega : j < v.length)).symm
    · have read := eq i
      rw [mHigh i (by omega)] at read ⊢
      change w.getD i false = v.getD i false at read
      change (w ++ [b]).getD i false = (v ++ [b]).getD i false
      by_cases hw : i < w.length
      · rw [List.getD_append _ _ _ _ hw, List.getD_append _ _ _ _ (by omega : i < v.length), read]
      · rw [List.getD_append_right _ _ _ _ (by omega : w.length ≤ i),
          List.getD_append_right _ _ _ _ (by omega : v.length ≤ i), len]
  have simFold (gs : List Gate) (hv : ∀ g ∈ gs, valid g) (w v : List Bool) (h : related w v) :
      related (gs.foldl step w) ((gs.map adapt).foldl step v) := by
    induction gs generalizing w v with
    | nil => exact h
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons]
      apply ih (fun g₁ hg => hv g₁ (List.mem_cons_of_mem _ hg))
      have coherence : g.inputs.map (fun i => w.getD i false) = (g.inputs.map m).map (val v) := by
        rw [List.map_map]; exact List.map_congr_left fun i _ => h.2.2 i
      have outputEq := lowerSound v g.op (g.inputs.map m) (hv g (by simp)).1
      unfold step adapt
      rw [coherence, outputEq]
      exact stepRel w v h _
  let D : Circuit := ⟨C.gates.map adapt, C.output⟩
  have newFan : FanInTwo D := by
    intro g hg
    obtain ⟨g₀, hg₀, rfl⟩ := List.mem_map.mp hg
    exact lowerValid g₀.op (g₀.inputs.map m) (by simpa using (fan g₀ hg₀).2)
  have newSize : D.size ≤ 18 := by
    change (C.gates.map adapt).length ≤ 18
    rw [List.length_map]
    exact budget
  have implements : ∀ x : Fin 10 → Bool, D.eval (input x) = edge x := by
    intro x
    have simulation (y : Fin 10 → Bool) := (simFold C.gates fan (List.ofFn (y ∘ σ) ++ [u (y 0)]) (input y)
      ⟨by simp [input], by simp, initial y⟩).2.2 C.output
    have goalEq (y : Fin 10 → Bool) : edge y = val (D.wires (input y)) (m C.output) :=
      (classify y).symm.trans (simulation y)
    by_cases small : C.output < 11
    · cases v : m C.output with
      | inl b =>
        have h₀ := goalEq (row 0)
        have h₁ := goalEq (row 3)
        rw [v, zeroEdge] at h₀
        rw [v, oneEdge] at h₁
        exact False.elim (Bool.false_ne_true (h₀.trans h₁.symm))
      | inr i =>
        have hi := mLow _ _ small v
        obtain ⟨ho, ho', _, _⟩ := witnesses ⟨i, hi⟩
        let y := row (if i = 10 then 0 else 2 ^ i)
        have h := goalEq y
        rw [v] at h
        change edge y = (D.gates.foldl step (input y)).getD i false at h
        rw [inputWire _ _ _ (by rw [inputLen]; exact hi)] at h
        exact False.elim (Bool.false_ne_true (ho.symm.trans (h.trans ho')))
    · have h := goalEq x
      rw [mHigh _ (by omega)] at h
      exact h.symm
  -- The output can only be a genuine binary gate or a NOT of an internal wire.
  -- R_meta_4031_1 by CptCaptain also splits by the output wire; here aliases and raw inputs are eliminated.
  let wire (gs : List Gate) (x : Fin 10 → Bool) (i : Nat) := (gs.foldl step (input x)).getD i false
  have oob (gs : List Gate) (x : Fin 10 → Bool) (i : Nat) (hi : 11 + gs.length ≤ i) :
      wire gs x i = false := by
    apply List.getD_eq_default
    rwa [wireLen, inputLen]
  have raw (gs : List Gate) (x : Fin 10 → Bool) (i : Fin 11) :
      wire gs x i.val = (input x).getD i.val false :=
    inputWire _ _ _ (by rw [inputLen]; exact i.isLt)
  have noConst (b : Bool) (eq : ∀ x, b = edge x) : False := by
    have h := (eq (row 0)).symm.trans (eq (row 3))
    rw [zeroEdge, oneEdge] at h
    exact Bool.false_ne_true h
  have noRaw (gs : List Gate) (i : Fin 11) (eq : ∀ x, wire gs x i.val = edge x) : False := by
    obtain ⟨hoff, hoff', _, _⟩ := witnesses i
    let x := row (if i.val = 10 then 0 else 2 ^ i.val)
    exact Bool.false_ne_true (hoff.symm.trans ((eq x).symm.trans ((raw gs x i).trans hoff')))
  have noRawNot (gs : List Gate) (i : Fin 11) (eq : ∀ x, (!wire gs x i.val) = edge x) : False := by
    have test : ∀ t : Fin 11, let x := row (if t.val = 10 then 1 else 0)
        edge x = false ∧ (input x).getD t.val false = false := by decide +kernel
    obtain ⟨ef, wf⟩ := test i
    let x := row (if i.val = 10 then 1 else 0)
    have h := eq x
    rw [raw gs x i, wf, ef] at h
    exact Bool.false_ne_true h.symm
  have tailDiff (w : List Bool) (b : Bool) (i : Nat) (hn : i ≠ w.length) :
      (w ++ [b]).getD i false = w.getD i false := by
    by_cases lo : i < w.length
    · exact List.getD_append _ _ _ _ lo
    · rw [List.getD_eq_default (w ++ [b]) _ (by simp; omega), List.getD_eq_default w _ (by omega)]
  have impossible (gs : List Gate) : ∀ o : Nat, (∀ g ∈ gs, valid g) → gs.length ≤ 18 →
      (∀ x, wire gs x o = edge x) → False := by
    induction gs using List.reverseRecOn with
    | nil =>
      intro o _ _ eq
      by_cases h : o < 11
      · exact noRaw [] ⟨o,h⟩ eq
      · apply noConst false
        intro x
        rw [← oob [] x o (by simp; omega)]
        exact eq x
    | append_singleton gs g ih =>
      intro o legal len eq
      have pref : ∀ g' ∈ gs, valid g' := fun g' hg' => legal g' (List.mem_append_left _ hg')
      have prefSize : gs.length ≤ 17 := by simp at len; omega
      have aliasOf (i : Nat) (h : ∀ x, wire gs x i = edge x) : False := ih i pref (by omega) h
      have add (x : Fin 10 → Bool) : (gs.foldl step (input x)).length = 11 + gs.length := by rw [wireLen, inputLen]
      have after (x : Fin 10 → Bool) : wire (gs ++ [g]) x o =
          (gs.foldl step (input x) ++ [g.op.eval (g.inputs.map fun i => wire gs x i)]).getD o false := by
        simp [wire, List.foldl_append, step]
      by_cases last : o = 11 + gs.length
      swap
      · apply aliasOf o
        intro x
        have h := eq x
        rw [after, tailDiff _ _ _ (by rw [add]; exact last)] at h
        exact h
      have value (x : Fin 10 → Bool) : g.op.eval (g.inputs.map fun i => wire gs x i) = edge x := by
        have h := eq x
        rw [after, last, ← add x, List.getD_append_right _ _ _ _ (Nat.le_refl _)] at h
        simpa using h
      let coreCircuit : Circuit := ⟨gs, 0⟩
      have binary (isAnd : Bool) (a b : Nat)
          (rep : ∀ x, (if isAnd then wire gs x a && wire gs x b else wire gs x a || wire gs x b) = edge x) : False := by
        have symm (p q : Nat) (h : ∀ x,
            (if isAnd then wire gs x p && wire gs x q else wire gs x p || wire gs x q) = edge x) :
            ∀ x, (if isAnd then wire gs x q && wire gs x p else wire gs x q || wire gs x p) = edge x := by
          intro x
          simpa only [Bool.and_comm, Bool.or_comm] using h x
        have bounds (p q : Nat) (h : ∀ x,
            (if isAnd then wire gs x p && wire gs x q else wire gs x p || wire gs x q) = edge x) :
            11 ≤ p ∧ p < 11 + gs.length := by
          constructor
          · by_contra! low
            let i : Fin 11 := ⟨p,low⟩
            obtain ⟨off, offBit, on, onBit⟩ := witnesses i
            cases isAnd
            · let x := row (if i.val = 10 then 0 else 2 ^ i.val)
              have eq := h x
              have r := (raw gs x i).trans offBit
              change wire gs x p = true at r
              simp [r] at eq
              exact Bool.false_ne_true (off.symm.trans eq)
            · let x := row (if i.val = 10 then 3 else if i.val < 2 then 12 else 3)
              have eq := h x
              have r := (raw gs x i).trans onBit
              change wire gs x p = false at r
              simp [r] at eq
              exact Bool.false_ne_true (eq.symm.trans on)
          · by_contra! high
            cases isAnd
            · apply aliasOf q
              intro x
              simpa [oob gs x p high] using h x
            · apply noConst false
              intro x
              simpa [oob gs x p high] using h x
        have swapRep := symm a b rep
        have ha := bounds a b rep
        have hb := bounds b a swapRep
        rcases lt_trichotomy a b with ab | rfl | ba
        · cases isAnd
          · exact hOr coreCircuit a b pref prefSize ha.1 ab hb.2 rep
          · exact hAnd coreCircuit a b pref prefSize ha.1 ab hb.2 rep
        · cases isAnd <;> exact aliasOf a (by simpa using rep)
        · cases isAnd
          · exact hOr coreCircuit b a pref prefSize hb.1 ba ha.2 swapRep
          · exact hAnd coreCircuit b a pref prefSize hb.1 ba ha.2 swapRep
      obtain ⟨op, arity⟩ := legal g (by simp)
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at op
      have few : g.inputs = [] ∨ (∃ a, g.inputs = [a]) ∨ (∃ a b, g.inputs = [a,b]) := by
        cases hs : g.inputs with
        | nil => exact Or.inl rfl
        | cons a t =>
          cases t with
          | nil => exact Or.inr (Or.inl ⟨a, rfl⟩)
          | cons b t =>
            cases t with
            | nil => exact Or.inr (Or.inr ⟨a, b, rfl⟩)
            | cons c t => rw [hs] at arity; simp at arity
      rcases op with op | op | op
      · rcases few with e | ⟨a,e⟩ | ⟨a,b,e⟩
        · exact noConst true (by simpa [op, e, evalAnd] using value)
        · exact aliasOf a (by simpa [op, e, evalAnd] using value)
        · exact binary true a b (by simpa [op, e, evalAnd] using value)
      · rcases few with e | ⟨a,e⟩ | ⟨a,b,e⟩
        · exact noConst false (by simpa [op, e, evalOr] using value)
        · exact aliasOf a (by simpa [op, e, evalOr] using value)
        · exact binary false a b (by simpa [op, e, evalOr] using value)
      · have notCase (i : Nat) (h : ∀ x, (!wire gs x i) = edge x) : False := by
          by_cases low : i < 11
          · exact noRawNot gs ⟨i,low⟩ h
          by_cases high : 11 + gs.length ≤ i
          · apply noConst true
            intro x
            simpa [oob gs x i high] using h x
          exact hNot coreCircuit i pref prefSize (by omega) (by change i < 11 + gs.length; omega) h
        rcases few with e | ⟨a,e⟩ | ⟨a,b,e⟩
        · exact noConst true (by simpa [op, e, evalNot] using value)
        · exact notCase a (by simpa [op, e, evalNot] using value)
        · exact notCase a (by simpa [op, e, evalNot] using value)
  exact impossible D.gates D.output newFan newSize implements
