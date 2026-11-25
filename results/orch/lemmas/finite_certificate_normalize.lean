import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def runGates (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w

lemma length_runGates (gs : List Gate) (w : List Bool) :
    (runGates gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (runGates gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
    rw [ih]
    simp
    omega

def capGate (B : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (fun i => min i B)⟩

lemma getD_min_of_length_le (w : List Bool) (B i : ℕ) (h : w.length ≤ B) :
    w.getD (min i B) false = w.getD i false := by
  by_cases hi : i ≤ B
  · rw [min_eq_left hi]
  · rw [min_eq_right (by omega), List.getD_eq_default _ _ (by omega),
      List.getD_eq_default _ _ (by omega)]

lemma runGates_capGate (B : ℕ) (gs : List Gate) : ∀ w : List Bool,
    w.length + gs.length ≤ B → runGates (gs.map (capGate B)) w = runGates gs w := by
  induction gs with
  | nil => intro w _; rfl
  | cons g gs ih =>
    intro w h
    simp only [List.length_cons] at h
    have e : (capGate B g).op.eval ((capGate B g).inputs.map fun i => w.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [capGate, List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact getD_min_of_length_le w B i (by omega)
    have step : runGates ((g :: gs).map (capGate B)) w
        = runGates (gs.map (capGate B))
            (w ++ [(capGate B g).op.eval ((capGate B g).inputs.map fun i => w.getD i false)]) :=
      rfl
    have step' : runGates (g :: gs) w
        = runGates gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [step, step', e]
    exact ih _ (by simp; omega)

def capCircuit (B : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (capGate B), min C.output B⟩

lemma capCircuit_size (B : ℕ) (C : Circuit) : (capCircuit B C).size = C.size := by
  simp [capCircuit, Circuit.size]

lemma capCircuit_eval (B : ℕ) (C : Circuit) (x : List Bool)
    (h : x.length + C.size ≤ B) : (capCircuit B C).eval x = C.eval x := by
  change (runGates (C.gates.map (capGate B)) x).getD (min C.output B) false =
    (runGates C.gates x).getD C.output false
  rw [runGates_capGate B C.gates x h]
  exact getD_min_of_length_le _ _ _ (by rw [length_runGates]; exact h)

lemma capCircuit_fan (B : ℕ) (C : Circuit) (h : FanInTwo C) :
    FanInTwo (capCircuit B C) := by
  intro g hg
  change g ∈ C.gates.map (capGate B) at hg
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
  obtain ⟨hop, hlen⟩ := h u hu
  exact ⟨hop, by simpa [capGate] using hlen⟩

lemma capCircuit_not (B : ℕ) (C : Circuit) :
    (∃ g ∈ (capCircuit B C).gates, g.op = GateOp.not) ↔
      ∃ g ∈ C.gates, g.op = GateOp.not := by
  constructor
  · rintro ⟨g, hg, hop⟩
    change g ∈ C.gates.map (capGate B) at hg
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hg
    exact ⟨u, hu, hop⟩
  · rintro ⟨g, hg, hop⟩
    exact ⟨capGate B g, List.mem_map.mpr ⟨g, hg, rfl⟩, hop⟩

lemma capCircuit_bounded (B : ℕ) (C : Circuit) :
    (capCircuit B C).output ≤ B ∧
      ∀ g ∈ (capCircuit B C).gates, ∀ i ∈ g.inputs, i ≤ B := by
  refine ⟨Nat.min_le_right _ _, ?_⟩
  intro g hg i hi
  obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hg
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hi
  exact Nat.min_le_right _ _

lemma finite_normalization (n s : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hsize : C.size ≤ s) (hnot : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ D : Circuit, FanInTwo D ∧ D.size = C.size ∧ D.output ≤ n + s ∧
      (∀ g ∈ D.gates, ∀ i ∈ g.inputs, i ≤ n + s) ∧
      (∃ g ∈ D.gates, g.op = GateOp.not) ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  refine ⟨capCircuit (n + s) C, capCircuit_fan _ _ hfan,
    capCircuit_size _ _, (capCircuit_bounded _ _).1, (capCircuit_bounded _ _).2,
    (capCircuit_not _ _).mpr hnot, ?_⟩
  intro x
  exact capCircuit_eval _ _ _ (by simpa using Nat.add_le_add_left hsize n)

abbrev GateCode (B : ℕ) := Fin 3 × Option (Fin (B + 1)) × Option (Fin (B + 1))

def decodeOp (i : Fin 3) : GateOp :=
  if i = 0 then GateOp.and else if i = 1 then GateOp.or else GateOp.not

def decodeGate (B : ℕ) (c : GateCode B) : Gate :=
  ⟨decodeOp c.1, (c.2.1.toList ++ c.2.2.toList).map Fin.val⟩

lemma exists_gateCode (B : ℕ) (g : Gate)
    (h : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2) : ∃ c : GateCode B, decodeGate B c = capGate B g := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  have hop' : ∃ i : Fin 3, decodeOp i = op := by
    rcases hop with h | h | h
    · exact ⟨0, by simp only [decodeOp]; exact (h : op = GateOp.and).symm⟩
    · exact ⟨1, by simp only [decodeOp]; exact (h : op = GateOp.or).symm⟩
    · exact ⟨2, by simp only [decodeOp]; exact (h : op = GateOp.not).symm⟩
  obtain ⟨i, hi⟩ := hop'
  have lt : ∀ a : ℕ, min a B < B + 1 := fun a => by omega
  match inputs, hlen with
  | [], _ => exact ⟨(i, none, none), by simp [decodeGate, capGate, hi]⟩
  | [a], _ => exact ⟨(i, some ⟨min a B, lt a⟩, none), by simp [decodeGate, capGate, hi]⟩
  | [a, b], _ =>
    exact ⟨(i, some ⟨min a B, lt a⟩, some ⟨min b B, lt b⟩),
      by simp [decodeGate, capGate, hi]⟩
  | _ :: _ :: _ :: _, h => simp at h

abbrev CircuitCode (B t : ℕ) := (Fin t → GateCode B) × Fin (B + 1)

def decodeCircuit {B t : ℕ} (c : CircuitCode B t) : Circuit :=
  ⟨List.ofFn (fun i => decodeGate B (c.1 i)), c.2⟩

lemma exists_circuitCode (n s : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hsize : C.size ≤ s) :
    ∃ t : Fin (s + 1), ∃ c : CircuitCode (n + s) t,
      decodeCircuit c = capCircuit (n + s) C := by
  have hsize' : C.gates.length ≤ s := hsize
  choose! enc henc using exists_gateCode (n + s)
  refine ⟨⟨C.gates.length, by omega⟩,
    (fun i => enc (C.gates[(i : ℕ)]'i.isLt), ⟨min C.output (n + s), by omega⟩), ?_⟩
  have hg : List.ofFn
      (fun i : Fin C.gates.length => decodeGate (n + s) (enc (C.gates[(i : ℕ)]'i.isLt)))
      = C.gates.map (capGate (n + s)) := by
    apply List.ext_getElem
    · simp
    · intro i h1 h2
      simp only [List.getElem_ofFn, List.getElem_map]
      exact henc _ (hfan _ (List.getElem_mem _))
  unfold decodeCircuit capCircuit
  rw [hg]

lemma exclusion_of_finite_exclusion (n s : ℕ) (f : (Fin n → Bool) → Bool)
    (hfinite : ∀ t : Fin (s + 1), ∀ c : CircuitCode (n + s) t,
      (∃ g ∈ (decodeCircuit c).gates, g.op = GateOp.not) →
      ¬ ∀ x : Fin n → Bool, (decodeCircuit c).eval (List.ofFn x) = f x) :
    ∀ C : Circuit, FanInTwo C → C.size ≤ s →
      (∃ g ∈ C.gates, g.op = GateOp.not) →
      ¬ ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x := by
  intro C hfan hsize hnot hcompute
  obtain ⟨t, c, hc⟩ := exists_circuitCode n s C hfan hsize
  apply hfinite t c
  · rw [hc]
    exact (capCircuit_not _ _).mpr hnot
  · intro x
    rw [hc, capCircuit_eval _ _ _ (by simpa using Nat.add_le_add_left hsize n)]
    exact hcompute x

end PEqualNP.Outside.L_meta_2592_aux
