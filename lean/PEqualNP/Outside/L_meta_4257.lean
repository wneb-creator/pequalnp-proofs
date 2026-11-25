import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4257

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def cap24 (k : ℕ) : Fin 25 :=
  if h : k < 24 then ⟨k, by omega⟩ else ⟨24, by omega⟩

theorem cap24_eq49 (k : ℕ) :
    ((cap24 k).val == 4 || (cap24 k).val == 9) = (k == 4 || k == 9) := by
  unfold cap24
  split_ifs with h
  · rfl
  · have h1 : k ≠ 4 := by omega
    have h2 : k ≠ 9 := by omega
    simp [h1, h2]

theorem getD_cap24 (w : List Bool) (hw : w.length ≤ 24) (k : ℕ) :
    w.getD (cap24 k).val false = w.getD k false := by
  unfold cap24
  split_ifs with h
  · rfl
  · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]

def opOfFin : Fin 3 → GateOp
  | ⟨0, _⟩ => GateOp.and
  | ⟨1, _⟩ => GateOp.or
  | ⟨2, _⟩ => GateOp.not

theorem opOfFin_eq (x : Fin 3) :
    (if x = 0 then GateOp.and else if x = 1 then GateOp.or else GateOp.not) = opOfFin x := by
  rcases x with ⟨v, hv⟩
  interval_cases v <;> rfl

def encGate (g : Gate) : Fin 3 × Fin 25 × Fin 25 :=
  match g.op, g.inputs with
  | GateOp.and, [] => (2, 24, 24)
  | GateOp.and, [a] => (0, cap24 a, cap24 a)
  | GateOp.and, a :: b :: _ => (0, cap24 a, cap24 b)
  | GateOp.or, [] => (1, 24, 24)
  | GateOp.or, [a] => (1, cap24 a, cap24 a)
  | GateOp.or, a :: b :: _ => (1, cap24 a, cap24 b)
  | GateOp.not, [] => (2, 24, 24)
  | GateOp.not, a :: _ => (2, cap24 a, 24)
  | _, _ => (0, 24, 24)

def gatePred (g : Gate) : Bool :=
  (if g.op.eval [false, false] = true then g.inputs.take 1 else g.inputs).any
    fun x => x == 4 || x == 9

def encPred (e : Fin 3 × Fin 25 × Fin 25) : Bool :=
  [e.2.1, e.2.2].any fun x => x.val == 4 || x.val == 9

theorem encPred_encodeGate (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    encPred (encGate g) = gatePred g := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  rcases hop with h | h | h <;> simp only at h <;> subst op
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp [encGate, encPred, gatePred, GateOp.eval]
    · simp [encGate, encPred, gatePred, GateOp.eval, cap24_eq49]
    · simp [encGate, encPred, gatePred, GateOp.eval, cap24_eq49]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp [encGate, encPred, gatePred, GateOp.eval]
    · simp [encGate, encPred, gatePred, GateOp.eval, cap24_eq49]
    · simp [encGate, encPred, gatePred, GateOp.eval, cap24_eq49]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp [encGate, encPred, gatePred, GateOp.eval]
    · simp [encGate, encPred, gatePred, GateOp.eval, cap24_eq49]
    · simp [encGate, encPred, gatePred, GateOp.eval, cap24_eq49]
    · simp at hlen

theorem encodeGate_eval (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (w : List Bool) (hw : w.length ≤ 24) :
    (opOfFin (encGate g).1).eval
        [w.getD (encGate g).2.1.val false, w.getD (encGate g).2.2.val false] =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  have h24 : w[24]?.getD false = false := by
    rw [← List.getD_eq_getElem?_getD, List.getD_eq_default _ _ hw]
  have hcap (k : ℕ) : w[(cap24 k).val]?.getD false = w[k]?.getD false := by
    rw [← List.getD_eq_getElem?_getD, ← List.getD_eq_getElem?_getD, getD_cap24 w hw k]
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  rcases hop with h | h | h <;> simp only at h <;> subst op
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp [encGate, opOfFin, GateOp.eval, h24]
    · simp [encGate, opOfFin, GateOp.eval, hcap a]
    · simp [encGate, opOfFin, GateOp.eval, hcap a, hcap b]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp [encGate, opOfFin, GateOp.eval, h24]
    · simp [encGate, opOfFin, GateOp.eval, hcap a]
    · simp [encGate, opOfFin, GateOp.eval, hcap a, hcap b]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
    · simp [encGate, opOfFin, GateOp.eval, h24]
    · simp [encGate, opOfFin, GateOp.eval, hcap a]
    · simp [encGate, opOfFin, GateOp.eval, hcap a]
    · simp at hlen

theorem foldl_encode_eq (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ (w : List Bool), w.length + gs.length ≤ 24 →
      List.foldl (fun w' e => w' ++ [(opOfFin e.1).eval [w'.getD e.2.1.val false, w'.getD e.2.2.val false]])
        w (gs.map encGate) =
      List.foldl (fun w' g => w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)]) w gs := by
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w hlen
    have hg := hgs g (by simp)
    have hev := encodeGate_eval g hg w (by omega)
    simp only [List.map_cons, List.foldl_cons, hev]
    apply ih (fun g' hg' => hgs g' (by simp [hg']))
    simp at hlen ⊢
    omega

theorem countP_encode (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    List.countP encPred (gs.map encGate) = List.countP gatePred gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.map_cons, List.countP_cons, encPred_encodeGate g (hgs g (by simp)),
      ih (fun g' hg' => hgs g' (by simp [hg']))]

end PEqualNP.Outside.L_meta_4257

open PEqualNP.Outside.L_meta_4257 PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity in
theorem PEqualNP.Outside.L_meta_4257 : have x1 : PEqualNP.CircuitLowerBounds.Gate → Bool := fun (x1 : PEqualNP.CircuitLowerBounds.Gate) => (if x1.op.eval [Bool.false, Bool.false] = Bool.true then List.take (1 : ℕ) x1.inputs else x1.inputs).any fun (x2 : ℕ) => x2 == (4 : ℕ) || x2 == (9 : ℕ); have x2 : Fin (3 : ℕ) × Fin (25 : ℕ) × Fin (25 : ℕ) → Bool := fun (x2 : Fin (3 : ℕ) × Fin (25 : ℕ) × Fin (25 : ℕ)) => [x2.2.1, x2.2.2].any fun (x3 : Fin (25 : ℕ)) => ↑x3 == (4 : ℕ) || ↑x3 == (9 : ℕ); have x3 : Fin (3 : ℕ) → PEqualNP.CircuitLowerBounds.GateOp := fun (x3 : Fin (3 : ℕ)) => if x3 = (0 : Fin (3 : ℕ)) then PEqualNP.CircuitLowerBounds.GateOp.and else if x3 = (1 : Fin (3 : ℕ)) then PEqualNP.CircuitLowerBounds.GateOp.or else PEqualNP.CircuitLowerBounds.GateOp.not; ∀ (x4 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.FanInTwo x4 → x4.size ≤ (14 : ℕ) → ∃ (x7 : List (Fin (3 : ℕ) × Fin (25 : ℕ) × Fin (25 : ℕ))) (x8 : Fin (25 : ℕ)), x7.length = x4.size ∧ List.countP x2 x7 = List.countP x1 x4.gates ∧ ∀ (x9 : List Bool), x9.length = (10 : ℕ) → (List.foldl (fun (x11 : List Bool) (x12 : Fin (3 : ℕ) × Fin (25 : ℕ) × Fin (25 : ℕ)) => x11 ++ [(x3 x12.1).eval [x11.getD (↑x12.2.1) Bool.false, x11.getD (↑x12.2.2) Bool.false]]) x9 x7).getD (↑x8) Bool.false = x4.eval x9 := by
  dsimp only
  intro C hC hsize
  refine ⟨C.gates.map encGate, cap24 C.output, by simp [Circuit.size], ?_, ?_⟩
  · exact countP_encode C.gates hC
  · intro x9 hx9
    have hfold_eq :
        List.foldl (fun x11 x12 => x11 ++ [(if x12.1 = 0 then GateOp.and else if x12.1 = 1 then GateOp.or else GateOp.not).eval [x11.getD (↑x12.2.1) false, x11.getD (↑x12.2.2) false]])
          x9 (C.gates.map encGate) =
        C.wires x9 := by
      have hfn : (fun (x11 : List Bool) (x12 : Fin 3 × Fin 25 × Fin 25) =>
          x11 ++ [(if x12.1 = 0 then GateOp.and else if x12.1 = 1 then GateOp.or else GateOp.not).eval [x11.getD (↑x12.2.1) false, x11.getD (↑x12.2.2) false]]) =
          (fun w' e => w' ++ [(opOfFin e.1).eval [w'.getD e.2.1.val false, w'.getD e.2.2.val false]]) := by
        funext w' e
        rw [opOfFin_eq]
      rw [hfn]
      exact foldl_encode_eq C.gates hC x9 (by change x9.length + C.size ≤ 24; omega)
    rw [hfold_eq]
    unfold Circuit.eval
    apply getD_cap24
    have hlen : (C.wires x9).length = x9.length + C.gates.length := by
      unfold Circuit.wires
      clear hfold_eq hx9
      induction C.gates generalizing x9 with
      | nil => simp
      | cons g gs ih =>
        simp only [List.foldl_cons, List.length_cons]
        rw [ih]
        simp; omega
    change (C.wires x9).length ≤ 24
    rw [hlen]
    change x9.length + C.size ≤ 24
    omega
