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


open PEqualNP.CircuitLowerBounds

def wireBelow (a b : List Bool) : Prop :=
  a.length = b.length ∧ ∀ i, a.getD i false = true → b.getD i false = true

lemma wireBelow_snoc {a b : List Bool} {x y : Bool}
    (h : wireBelow a b) (hxy : x = true → y = true) :
    wireBelow (a ++ [x]) (b ++ [y]) := by
  have hlen := h.1
  refine ⟨by simp [h.1], ?_⟩
  intro i
  by_cases hi : i < a.length
  · rw [List.getD_append _ _ _ _ hi,
      List.getD_append _ _ _ _ (by omega)]
    exact h.2 i
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), h.1]
    cases i - b.length with
    | zero => simpa using hxy
    | succ k => simp

lemma gate_preserves_below (g : Gate) (hop : g.op = .and ∨ g.op = .or)
    {a b : List Bool} (hab : wireBelow a b) :
    g.op.eval (g.inputs.map fun i => a.getD i false) = true →
      g.op.eval (g.inputs.map fun i => b.getD i false) = true := by
  rcases hop with h | h
  · simp only [h, GateOp.eval, List.all_eq_true, id_eq]
    intro ha v hv
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hv
    exact hab.2 i (ha _ (List.mem_map.mpr ⟨i, hi, rfl⟩))
  · simp only [h, GateOp.eval, List.any_eq_true, id_eq]
    intro ha
    obtain ⟨v, hv, rfl⟩ := ha
    obtain ⟨i, hi, he⟩ := List.mem_map.mp hv
    exact ⟨_, List.mem_map.mpr ⟨i, hi, rfl⟩, hab.2 i he⟩

lemma gates_preserve_below (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    {a b : List Bool} (hab : wireBelow a b) :
    wireBelow ((⟨gs, 0⟩ : Circuit).wires a) ((⟨gs, 0⟩ : Circuit).wires b) := by
  induction gs generalizing a b with
  | nil => exact hab
  | cons g gs ih =>
    change wireBelow ((⟨gs, 0⟩ : Circuit).wires
      (a ++ [g.op.eval (g.inputs.map fun i => a.getD i false)]))
      ((⟨gs, 0⟩ : Circuit).wires
      (b ++ [g.op.eval (g.inputs.map fun i => b.getD i false)]))
    exact ih (fun g hg => hgs g (List.mem_cons_of_mem _ hg))
      (wireBelow_snoc hab (gate_preserves_below g (hgs g List.mem_cons_self) hab))

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.size := by
  obtain ⟨gs, o⟩ := C
  induction gs generalizing x with
  | nil => simp [Circuit.wires, Circuit.size]
  | cons g gs ih =>
    change (((⟨gs, o⟩ : Circuit).wires
      (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]))).length = _
    rw [ih]
    simp [Circuit.size]
    omega

lemma append_not_eval (C : Circuit) (x : List Bool) (i : ℕ) :
    (⟨C.gates ++ [⟨.not, [i]⟩], x.length + C.size⟩ : Circuit).eval x =
      !(C.wires x).getD i false := by
  simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons,
    List.foldl_nil, List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
  change ((C.wires x) ++ [!(C.wires x).getD i false]).getD
    (x.length + C.size) false = _
  rw [← wires_length C x, List.getD_append_right _ _ _ _ (by omega)]
  simp only [Nat.sub_self, List.getD_cons_zero]
  rfl

lemma final_not_cannot_rise (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or)
    {a b : List Bool} (hab : wireBelow a b) (i : ℕ)
    (ha : (⟨C.gates ++ [⟨.not, [i]⟩], a.length + C.size⟩ : Circuit).eval a = false) :
    (⟨C.gates ++ [⟨.not, [i]⟩], b.length + C.size⟩ : Circuit).eval b = false := by
  rw [append_not_eval] at ha ⊢
  have hm := (gates_preserve_below C.gates hC hab).2 i
  have ha' : (C.wires a).getD i false = true := by simpa using ha
  have hb' : (C.wires b).getD i false = true := hm ha'
  rw [hb']
  rfl


lemma polarized_repair_bool (G : Bool → Bool → Bool)
    (hG : ∀ p, Monotone (G p)) (a b : Bool) (hba : b ≤ a)
    (hmono : G a b ≤ G true false) (x : Bool) :
    G (x || a) ((!x) && b) = G (x || a) b := by
  have hUp : G true false ≤ G true true := hG true (by decide)
  cases a <;> cases b <;> cases x
  all_goals try rfl
  all_goals try exact False.elim ((by decide : ¬ (true : Bool) ≤ false) hba)
  exact le_antisymm hUp hmono

lemma polarized_repair {Y : Type*} (G : Y → Bool → Bool → Bool)
    (A B : Y → Bool) (hG : ∀ y p, Monotone (G y p))
    (hBA : ∀ y, B y ≤ A y)
    (hmono : ∀ y, G y (A y) (B y) ≤ G y true false) :
    ∀ y x, G y (x || A y) ((!x) && B y) = G y (x || A y) (B y) := by
  intro y x
  exact polarized_repair_bool (G y) (hG y) (A y) (B y) (hBA y) (hmono y) x

lemma nested_positive_repair (G : Bool → Bool → Bool)
    (hG : ∀ p, Monotone (G p)) (a : Bool)
    (hmono : G a a ≤ G true false) (x : Bool) :
    G (x || a) ((!x) && (x || a)) = G (x || a) a := by
  have hEq : ((!x) && (x || a)) = ((!x) && a) := by
    cases x <;> cases a <;> rfl
  rw [hEq]
  exact polarized_repair_bool G hG a a (le_refl a) hmono x

lemma nested_negative_repair (G : Bool → Bool → Bool)
    (hG : ∀ p, Monotone (G p)) (b : Bool)
    (hmono : G b b ≤ G true false) (x : Bool) :
    G (x || ((!x) && b)) ((!x) && b) = G (x || b) b := by
  have hEq : (x || ((!x) && b)) = (x || b) := by
    cases x <;> cases b <;> rfl
  rw [hEq]
  exact polarized_repair_bool G hG b b (le_refl b) hmono x

end PEqualNP.Outside.L_meta_2592_aux
