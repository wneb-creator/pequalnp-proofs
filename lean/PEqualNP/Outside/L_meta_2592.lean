import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.Normalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def shift (n i : ℕ) : ℕ := if i < n then i else i + 1

def read (n j i : ℕ) : ℕ := if i < n + j then shift n i else n

def canonicalGate (n j : ℕ) (g : Gate) : Gate :=
  match g.op, g.inputs with
  | .and, [] => ⟨.not, [n]⟩
  | .or, [] => ⟨.or, [n, n]⟩
  | .not, [] => ⟨.not, [n]⟩
  | .and, [i] => ⟨.and, [read n j i, read n j i]⟩
  | .or, [i] => ⟨.or, [read n j i, read n j i]⟩
  | .not, i :: _ => ⟨.not, [read n j i]⟩
  | .and, i :: k :: _ => ⟨.and, [read n j i, read n j k]⟩
  | .or, i :: k :: _ => ⟨.or, [read n j i, read n j k]⟩
  | _, _ => ⟨.or, [n, n]⟩

def canonicalGates (n : ℕ) : ℕ → List Gate → List Gate
  | _, [] => []
  | j, g :: gs => canonicalGate n j g :: canonicalGates n (j + 1) gs

def Related (n j : ℕ) (w z : List Bool) : Prop :=
  w.length = n + j ∧ z.length = n + j + 1 ∧ z.getD n false = false ∧
    ∀ i, z.getD (shift n i) false = w.getD i false

lemma relatedInitial (n : ℕ) (x : Fin n → Bool) :
    Related n 0 (List.ofFn x) (List.ofFn x ++ [false]) := by
  refine ⟨by simp, by simp, ?_, ?_⟩
  · rw [List.getD_append_right _ _ _ _ (by simp)]
    simp
  · intro i
    by_cases hi : i < n
    · simp only [shift, ite_eq_left hi]
      exact List.getD_append _ _ _ _ (by simpa)
    · simp only [shift, ite_eq_right hi]
      rw [List.getD_eq_default _ _ (by simp; omega)]
      rw [List.getD_eq_default _ _ (by simp; omega)]

lemma readBound (n j i : ℕ) : read n j i < n + j + 1 := by
  unfold read shift
  split_ifs <;> omega

lemma readBoundLE (n j i : ℕ) : read n j i ≤ n + j := by
  have := readBound n j i
  omega

lemma readValue {n j : ℕ} {w z : List Bool} (h : Related n j w z) (i : ℕ) :
    z.getD (read n j i) false = w.getD i false := by
  unfold read
  split_ifs with hi
  · exact h.2.2.2 i
  · have hw := h.1
    rw [h.2.2.1, List.getD_eq_default _ _ (by omega)]

lemma relatedAppend {n j : ℕ} {w z : List Bool} (h : Related n j w z) (b : Bool) :
    Related n (j + 1) (w ++ [b]) (z ++ [b]) := by
  obtain ⟨hw, hz, zero, same⟩ := h
  refine ⟨by simp [hw]; omega, by simp [hz]; omega, ?_, ?_⟩
  · rw [List.getD_append _ _ _ _ (by omega)]
    exact zero
  · intro i
    by_cases hi : i < n + j
    · rw [List.getD_append _ _ _ _ (by unfold shift; split_ifs <;> omega)]
      rw [List.getD_append _ _ _ _ (by omega)]
      exact same i
    · by_cases he : i = n + j
      · subst i
        have hs : shift n (n + j) = n + j + 1 := by simp [shift]
        rw [hs, List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega)]
        simp [hw, hz]
      · rw [List.getD_eq_default _ _ (by simp [hz]; unfold shift; split_ifs <;> omega)]
        rw [List.getD_eq_default _ _ (by simp [hw]; omega)]

lemma canonicalGateValue {n j : ℕ} {w z : List Bool} (h : Related n j w z)
    (g : Gate) (hg : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    (canonicalGate n j g).op.eval
      ((canonicalGate n j g).inputs.map fun i => z.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  rcases hop with rfl | rfl | rfl
  all_goals
    cases ins with
    | nil => simp only [canonicalGate, GateOp.eval, List.map_cons, List.map_nil, List.all_nil, List.any_cons, List.any_nil, List.headD_cons, List.headD_nil, h.2.2.1, id_eq, Bool.false_or, Bool.not_false]
    | cons i rest =>
      cases rest with
      | nil => simp only [canonicalGate, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.headD_cons, readValue h, Bool.and_true, Bool.or_false, Bool.and_self, Bool.or_self]
      | cons k tail =>
        cases tail with
        | nil => simp only [canonicalGate, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, List.headD_cons, readValue h, Bool.and_true, Bool.or_false, Bool.and_self, Bool.or_self]
        | cons l tail => simp at hlen

lemma canonicalGateNot (n j : ℕ) (g : Gate) (h : g.op = .not) :
    (canonicalGate n j g).op = .not := by
  obtain ⟨op, ins⟩ := g
  cases h
  cases ins <;> rfl

lemma canonicalGatesLength (n j : ℕ) (gs : List Gate) :
    (canonicalGates n j gs).length = gs.length := by
  induction gs generalizing j with
  | nil => rfl
  | cons g gs ih => simp [canonicalGates, ih]

lemma canonicalGatesNot (n j : ℕ) (gs : List Gate)
    (h : ∃ g ∈ gs, g.op = .not) :
    ∃ g ∈ canonicalGates n j gs, g.op = .not := by
  induction gs generalizing j with
  | nil => simp at h
  | cons g gs ih =>
    obtain ⟨a, ha, hop⟩ := h
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨canonicalGate n j _, List.mem_cons_self, canonicalGateNot n j _ hop⟩
    · obtain ⟨a, ha, hop⟩ := ih (j + 1) ⟨a, ha, hop⟩
      exact ⟨a, List.mem_cons_of_mem _ ha, hop⟩

lemma canonicalGatesRelated (n j : ℕ) (gs : List Gate) (w z : List Bool)
    (h : Related n j w z)
    (fan : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧
      g.inputs.length ≤ 2) :
    Related n (j + gs.length)
      (Circuit.wires ⟨gs, 0⟩ w) (Circuit.wires ⟨canonicalGates n j gs, 0⟩ z) := by
  induction gs generalizing j w z with
  | nil => simpa [Circuit.wires, canonicalGates] using h
  | cons g gs ih =>
    have hv := canonicalGateValue h g (fan g List.mem_cons_self)
    have hr := relatedAppend h (g.op.eval (g.inputs.map fun i => w.getD i false))
    have ht := ih (j + 1)
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (z ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) hr
      (fun a ha => fan a (List.mem_cons_of_mem _ ha))
    simp only [canonicalGates, Circuit.wires, List.foldl_cons, hv]
    simpa only [Circuit.wires, List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ht


def SatGate (n j : ℕ) (g : Gate) : Prop :=
  (((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
    (g.op = .not ∧ g.inputs.length = 1)) ∧
  ∀ i ∈ g.inputs, i < n + j + 1

def SatGates (n : ℕ) : ℕ → List Gate → Prop
  | _, [] => True
  | j, g :: gs => SatGate n j g ∧ SatGates n (j + 1) gs

lemma canonicalGateSat (n j : ℕ) (g : Gate) : SatGate n j (canonicalGate n j g) := by
  obtain ⟨op, ins⟩ := g
  cases op <;> cases ins with
  | nil => simp [canonicalGate, SatGate]
  | cons i rest =>
    cases rest with
    | nil => simp [canonicalGate, SatGate, readBoundLE]
    | cons k tail => simp [canonicalGate, SatGate, readBoundLE]

lemma canonicalGatesSat (n j : ℕ) (gs : List Gate) :
    SatGates n j (canonicalGates n j gs) := by
  induction gs generalizing j with
  | nil => trivial
  | cons g gs ih => exact ⟨canonicalGateSat n j g, ih (j + 1)⟩

lemma normalizedCircuit (n : ℕ) (C : Circuit) (fan : FanInTwo C)
    (hasNot : ∃ g ∈ C.gates, g.op = .not) :
    ∃ D : Circuit, D.size = C.size ∧ SatGates n 0 D.gates ∧
      (∃ g ∈ D.gates, g.op = .not) ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x ++ [false]) = C.eval (List.ofFn x) := by
  let D : Circuit := ⟨canonicalGates n 0 C.gates, shift n C.output⟩
  refine ⟨D, canonicalGatesLength n 0 C.gates, canonicalGatesSat n 0 C.gates,
    canonicalGatesNot n 0 C.gates hasNot, ?_⟩
  intro x
  have hfan : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using fan g hg
  have h := canonicalGatesRelated n 0 C.gates (List.ofFn x)
    (List.ofFn x ++ [false]) (relatedInitial n x) hfan
  exact h.2.2.2 C.output

end PEqualNP.Outside.L_meta_2592_aux.Normalize

namespace PEqualNP.Outside.L_meta_2592_aux.Truncate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma runLength (gs : List Gate) (w : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, 0⟩
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
    rw [ih]
    simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma runExtends (gs : List Gate) (w : List Bool) :
    ∃ tail : List Bool, Circuit.wires ⟨gs, 0⟩ w = w ++ tail := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [Circuit.wires]⟩
  | cons g gs ih =>
    obtain ⟨tail, ht⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    exact ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: tail, by
      simpa only [Circuit.wires, List.foldl_cons, List.append_assoc,
        List.singleton_append] using ht⟩

lemma evalAppend {pre post : List Gate} {out : ℕ} {w : List Bool}
    (ho : out < w.length + pre.length) :
    Circuit.eval ⟨pre ++ post, out⟩ w = Circuit.eval ⟨pre, out⟩ w := by
  obtain ⟨tail, ht⟩ := runExtends post (Circuit.wires ⟨pre, 0⟩ w)
  unfold Circuit.eval Circuit.wires
  rw [List.foldl_append]
  change (Circuit.wires ⟨post, 0⟩ (Circuit.wires ⟨pre, 0⟩ w)).getD out false = _
  rw [ht, List.getD_append _ _ _ _ (by rw [runLength]; exact ho)]
  rfl

lemma evalTake (C : Circuit) (k : ℕ) (w : List Bool)
    (ho : C.output < w.length + (C.gates.take k).length) :
    C.eval w = Circuit.eval ⟨C.gates.take k, C.output⟩ w := by
  have h := evalAppend (post := C.gates.drop k) ho
  simpa only [List.take_append_drop] using h


lemma evalInput (C : Circuit) (w : List Bool) (ho : C.output < w.length) :
    C.eval w = w.getD C.output false := by
  obtain ⟨tail, ht⟩ := runExtends C.gates w
  change (Circuit.wires ⟨C.gates, 0⟩ w).getD C.output false = _
  rw [ht, List.getD_append _ _ _ _ ho]

lemma evalBeyond (C : Circuit) (w : List Bool) (ho : w.length + C.size ≤ C.output) :
    C.eval w = false := by
  change (Circuit.wires ⟨C.gates, 0⟩ w).getD C.output false = _
  apply List.getD_eq_default
  rw [runLength]
  exact ho

lemma outputBounds (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit)
    (correct : ∀ x, C.eval (List.ofFn x) = f x)
    (nonzero : ∃ x, f x = true)
    (notInput : ∀ i : Fin n, ∃ x, f x ≠ x i) :
    n ≤ C.output ∧ C.output < n + C.size := by
  constructor
  · by_contra! ho
    obtain ⟨x, hx⟩ := notInput ⟨C.output, ho⟩
    apply hx
    rw [← correct x, evalInput C _ (by simpa)]
    rw [List.getD_eq_getElem _ _ (by simpa)]
    simp
  · by_contra! ho
    obtain ⟨x, hx⟩ := nonzero
    have he := evalBeyond C (List.ofFn x) (by simpa using ho)
    rw [correct x, hx] at he
    contradiction

lemma truncateOutput (n : ℕ) (C : Circuit) (fan : FanInTwo C)
    (hasNot : ∃ g ∈ C.gates, g.op = .not)
    (lower : n ≤ C.output) (upper : C.output < n + C.size) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧
      D.output + 1 = n + D.size ∧
      ((∃ g ∈ D.gates, g.op = .not) ∨ D.size < C.size) ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let k := C.output + 1 - n
  have hk : k ≤ C.gates.length := by change k ≤ C.size; unfold k; omega
  let D : Circuit := ⟨C.gates.take k, C.output⟩
  have dlen : D.size = k := by simp [D, Circuit.size, Nat.min_eq_left hk]
  refine ⟨D, ?_, ?_, ?_, ?_, ?_⟩
  · intro g hg
    apply fan g
    exact List.mem_of_mem_take hg
  · rw [dlen]
    exact hk
  · change C.output + 1 = n + D.size
    rw [dlen]
    unfold k
    omega
  · by_cases hnot : ∃ g ∈ D.gates, g.op = .not
    · exact Or.inl hnot
    · right
      rw [dlen]
      by_contra! hle
      have he : k = C.gates.length := by change C.gates.length ≤ k at hle; omega
      have same : D.gates = C.gates := by simp [D, he]
      exact hnot (same.symm ▸ hasNot)
  · intro x
    apply (evalTake C k (List.ofFn x) ?_).symm
    simp only [List.length_ofFn, List.length_take]
    rw [Nat.min_eq_left hk]
    unfold k
    omega

end PEqualNP.Outside.L_meta_2592_aux.Truncate

namespace PEqualNP.Outside.L_meta_2592_aux.Pad

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def shiftWire (n i : ℕ) : ℕ := if i < n then i else i + 1

def shiftGate (n : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (shiftWire n)⟩

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

def padNot (n : ℕ) (C : Circuit) : Circuit :=
  ⟨⟨GateOp.not, []⟩ :: C.gates.map (shiftGate n), shiftWire n C.output⟩

lemma readShift (xs ys : List Bool) (i : ℕ) :
    (xs ++ true :: ys).getD (shiftWire xs.length i) false =
      (xs ++ ys).getD i false := by
  induction xs generalizing i with
  | nil => simp [shiftWire]
  | cons a xs ih =>
    cases i with
    | zero => simp [shiftWire]
    | succ i =>
      by_cases h : i < xs.length
      · simpa [shiftWire, h, Nat.succ_lt_succ_iff] using ih i
      · simpa [shiftWire, h, Nat.succ_lt_succ_iff, Nat.add_assoc] using ih i

lemma runShift (gs : List Gate) (xs ys : List Bool) :
    ∃ zs, run gs (xs ++ ys) = xs ++ zs ∧
      run (gs.map (shiftGate xs.length)) (xs ++ true :: ys) = xs ++ true :: zs := by
  induction gs generalizing ys with
  | nil => exact ⟨ys, rfl, rfl⟩
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => (xs ++ ys).getD i false)
    obtain ⟨zs, orig, shifted⟩ := ih (ys ++ [v])
    have value : (shiftGate xs.length g).op.eval
        ((shiftGate xs.length g).inputs.map fun i => (xs ++ true :: ys).getD i false) = v := by
      dsimp [shiftGate, v]
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact readShift xs ys i
    refine ⟨zs, ?_, ?_⟩
    · simpa only [run, List.foldl_cons, v, List.append_assoc] using orig
    · change run (gs.map (shiftGate xs.length))
        ((xs ++ true :: ys) ++ [(shiftGate xs.length g).op.eval
          ((shiftGate xs.length g).inputs.map fun i => (xs ++ true :: ys).getD i false)]) = _
      rw [value]
      simpa only [List.append_assoc, List.cons_append] using shifted

lemma padNot_eval (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (padNot n C).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  let xs := List.ofFn x
  have len : xs.length = n := List.length_ofFn
  obtain ⟨zs, orig, shifted⟩ := runShift C.gates xs []
  have orig' : run C.gates xs = xs ++ zs := by simpa using orig
  have shifted' : run (C.gates.map (shiftGate n)) (xs ++ [true]) = xs ++ true :: zs := by
    simpa only [len, List.append_nil] using shifted
  change (run (C.gates.map (shiftGate n)) (xs ++ [true])).getD
    (shiftWire n C.output) false = (run C.gates xs).getD C.output false
  rw [orig', shifted']
  simpa only [len] using readShift xs zs C.output

lemma padNot_size (n : ℕ) (C : Circuit) : (padNot n C).size = C.size + 1 := by
  simp [padNot, Circuit.size]

lemma padNot_hasNot (n : ℕ) (C : Circuit) :
    ∃ g ∈ (padNot n C).gates, g.op = GateOp.not :=
  ⟨⟨GateOp.not, []⟩, List.mem_cons_self, rfl⟩

lemma padNot_fan (n : ℕ) (C : Circuit) (fan : FanInTwo C) : FanInTwo (padNot n C) := by
  intro g mem
  rcases List.mem_cons.mp mem with rfl | mem
  · simp
  · obtain ⟨h, hm, he⟩ := List.mem_map.mp mem
    subst g
    obtain ⟨basis, arity⟩ := fan h hm
    exact ⟨basis, by simpa [shiftGate] using arity⟩

lemma padNot_last (n : ℕ) (C : Circuit) (positive : 0 < C.size)
    (last : C.output + 1 = n + C.size) :
    (padNot n C).output + 1 = n + (padNot n C).size := by
  have after : ¬ C.output < n := by omega
  rw [padNot_size]
  simp only [padNot, shiftWire, ite_eq_right after]
  omega

end PEqualNP.Outside.L_meta_2592_aux.Pad

namespace PEqualNP.Outside.L_meta_2592_aux.NormalForm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux.Normalize
open PEqualNP.Outside.L_meta_2592_aux.Truncate
open PEqualNP.Outside.L_meta_2592_aux.Pad

lemma canonicalLastCircuit (n : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit)
    (fan : FanInTwo C) (hasNot : ∃ g ∈ C.gates, g.op = .not)
    (correct : ∀ x, C.eval (List.ofFn x) = f x)
    (nonzero : ∃ x, f x = true)
    (notInput : ∀ i : Fin n, ∃ x, f x ≠ x i) :
    ∃ D : Circuit, D.size ≤ C.size ∧ SatGates n 0 D.gates ∧
      D.output + 1 = n + 1 + D.size ∧
      (∃ g ∈ D.gates, g.op = .not) ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x ++ [false]) = f x := by
  have bounds := outputBounds n f C correct nonzero notInput
  obtain ⟨P, pfan, pcost, plast, pcase, peval⟩ :=
    truncateOutput n C fan hasNot bounds.1 bounds.2
  have pcorrect : ∀ x, P.eval (List.ofFn x) = f x :=
    fun x => (peval x).trans (correct x)
  have pbounds := outputBounds n f P pcorrect nonzero notInput
  have ppos : 0 < P.size := by omega
  have chooseE : ∃ E : Circuit, FanInTwo E ∧ E.size ≤ C.size ∧ 0 < E.size ∧
      E.output + 1 = n + E.size ∧ (∃ g ∈ E.gates, g.op = .not) ∧
      ∀ x, E.eval (List.ofFn x) = f x := by
    rcases pcase with pnot | psmall
    · exact ⟨P, pfan, pcost, ppos, plast, pnot, pcorrect⟩
    · refine ⟨padNot n P, padNot_fan n P pfan, ?_, ?_,
        padNot_last n P ppos plast, padNot_hasNot n P, ?_⟩
      · rw [padNot_size]
        omega
      · rw [padNot_size]
        omega
      · intro x
        exact (padNot_eval n P x).trans (pcorrect x)
  obtain ⟨E, efan, ecost, epos, elast, enot, eeval⟩ := chooseE
  let D : Circuit := ⟨canonicalGates n 0 E.gates, shift n E.output⟩
  have dsize : D.size = E.size := canonicalGatesLength n 0 E.gates
  refine ⟨D, by rw [dsize]; exact ecost, canonicalGatesSat n 0 E.gates,
    ?_, canonicalGatesNot n 0 E.gates enot, ?_⟩
  · change shift n E.output + 1 = n + 1 + D.size
    rw [dsize]
    have after : ¬ E.output < n := by omega
    simp only [shift, ite_eq_right after]
    omega
  · intro x
    have efan' : ∀ g ∈ E.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧
        g.inputs.length ≤ 2 := by
      intro g hg
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using efan g hg
    have h := canonicalGatesRelated n 0 E.gates (List.ofFn x)
      (List.ofFn x ++ [false]) (relatedInitial n x) efan'
    exact (h.2.2.2 E.output).trans (eeval x)

end PEqualNP.Outside.L_meta_2592_aux.NormalForm


namespace PEqualNP.Outside.L_meta_2592_aux.IdentityPad

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def SatGate (n j : ℕ) (g : Gate) : Prop :=
  (((g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2) ∨
    (g.op = .not ∧ g.inputs.length = 1)) ∧
  ∀ i ∈ g.inputs, i < n + j + 1

def SatGates (n : ℕ) : ℕ → List Gate → Prop
  | _, [] => True
  | j, g :: gs => SatGate n j g ∧ SatGates n (j + 1) gs

def appendCopy (n : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates ++ [⟨.or, [C.output, C.output]⟩], n + C.size + 1⟩

def padCopies (n : ℕ) (C : Circuit) : ℕ → Circuit
  | 0 => C
  | k + 1 => appendCopy n (padCopies n C k)

lemma wiresLength (C : Circuit) (xs : List Bool) :
    (C.wires xs).length = xs.length + C.size := by
  obtain ⟨gs, out⟩ := C
  induction gs generalizing xs with
  | nil => simp [Circuit.wires, Circuit.size]
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, out⟩
      (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)])).length =
      xs.length + (g :: gs).length
    rw [ih]
    simp [Circuit.size, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma appendCopySize (n : ℕ) (C : Circuit) :
    (appendCopy n C).size = C.size + 1 := by
  simp [appendCopy, Circuit.size]

lemma appendCopyEval (n : ℕ) (C : Circuit) (xs : List Bool)
    (length : xs.length = n + 1) :
    (appendCopy n C).eval xs = C.eval xs := by
  have wires : (C.wires xs).length = n + C.size + 1 := by
    rw [wiresLength, length]
    omega
  simp only [Circuit.eval, appendCopy, Circuit.wires, List.foldl_append,
    List.foldl_cons, List.foldl_nil]
  change ((C.wires xs) ++ [GateOp.or.eval
    ([C.output, C.output].map fun i => (C.wires xs).getD i false)]).getD
      (n + C.size + 1) false = C.eval xs
  rw [← wires, List.getD_append_right _ _ _ _ (by omega)]
  simp [Circuit.eval, GateOp.eval]

lemma appendCopyValid (n : ℕ) (C : Circuit) :
    (appendCopy n C).output < n + (appendCopy n C).size + 1 := by
  rw [appendCopySize]
  simp only [appendCopy]
  omega

lemma appendCopyLast (n : ℕ) (C : Circuit) :
    (appendCopy n C).output + 1 = n + 1 + (appendCopy n C).size := by
  rw [appendCopySize]
  simp only [appendCopy]
  omega

lemma satAppend (n j : ℕ) (gs qs : List Gate)
    (left : SatGates n j gs) (right : SatGates n (j + gs.length) qs) :
    SatGates n j (gs ++ qs) := by
  induction gs generalizing j with
  | nil => simpa using right
  | cons g gs ih =>
    refine ⟨left.1, ih (j + 1) left.2 ?_⟩
    simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using right

lemma appendCopySat (n : ℕ) (C : Circuit)
    (sat : SatGates n 0 C.gates) (valid : C.output < n + C.size + 1) :
    SatGates n 0 (appendCopy n C).gates := by
  apply satAppend n 0 C.gates _ sat
  refine ⟨?_, trivial⟩
  refine ⟨Or.inl ⟨Or.inr rfl, rfl⟩, ?_⟩
  intro i hi
  have eq : i = C.output := by simpa using hi
  subst i
  simpa only [Nat.zero_add, Circuit.size] using valid

lemma appendCopyHasNot (n : ℕ) (C : Circuit)
    (hasNot : ∃ g ∈ C.gates, g.op = .not) :
    ∃ g ∈ (appendCopy n C).gates, g.op = .not := by
  obtain ⟨g, mem, op⟩ := hasNot
  exact ⟨g, List.mem_append_left _ mem, op⟩

lemma padCopiesSize (n : ℕ) (C : Circuit) (k : ℕ) :
    (padCopies n C k).size = C.size + k := by
  induction k with
  | zero => rfl
  | succ k ih => rw [padCopies, appendCopySize, ih]; omega

lemma padCopiesValid (n : ℕ) (C : Circuit) (k : ℕ)
    (valid : C.output < n + C.size + 1) :
    (padCopies n C k).output < n + (padCopies n C k).size + 1 := by
  cases k with
  | zero => exact valid
  | succ k => exact appendCopyValid n (padCopies n C k)

lemma padCopiesLast (n : ℕ) (C : Circuit) (k : ℕ)
    (last : C.output + 1 = n + 1 + C.size) :
    (padCopies n C k).output + 1 = n + 1 + (padCopies n C k).size := by
  cases k with
  | zero => exact last
  | succ k => exact appendCopyLast n (padCopies n C k)

lemma padCopiesEval (n : ℕ) (C : Circuit) (k : ℕ) (xs : List Bool)
    (length : xs.length = n + 1) :
    (padCopies n C k).eval xs = C.eval xs := by
  induction k with
  | zero => rfl
  | succ k ih => rw [padCopies, appendCopyEval n _ xs length, ih]

lemma padCopiesSat (n : ℕ) (C : Circuit) (k : ℕ)
    (sat : SatGates n 0 C.gates) (valid : C.output < n + C.size + 1) :
    SatGates n 0 (padCopies n C k).gates := by
  induction k with
  | zero => exact sat
  | succ k ih => exact appendCopySat n _ ih (padCopiesValid n C k valid)

lemma padCopiesHasNot (n : ℕ) (C : Circuit) (k : ℕ)
    (hasNot : ∃ g ∈ C.gates, g.op = .not) :
    ∃ g ∈ (padCopies n C k).gates, g.op = .not := by
  induction k with
  | zero => exact hasNot
  | succ k ih => exact appendCopyHasNot n _ ih

lemma padToBudget (n budget : ℕ) (C : Circuit)
    (small : C.size ≤ budget) (sat : SatGates n 0 C.gates)
    (last : C.output + 1 = n + 1 + C.size)
    (hasNot : ∃ g ∈ C.gates, g.op = .not) :
    ∃ D : Circuit, D.size = budget ∧ SatGates n 0 D.gates ∧
      D.output + 1 = n + 1 + D.size ∧
      (∃ g ∈ D.gates, g.op = .not) ∧
      ∀ xs : List Bool, xs.length = n + 1 → D.eval xs = C.eval xs := by
  refine ⟨padCopies n C (budget - C.size), ?_, ?_, ?_, ?_, ?_⟩
  · rw [padCopiesSize]
    omega
  · exact padCopiesSat n C _ sat (by omega)
  · exact padCopiesLast n C _ last
  · exact padCopiesHasNot n C _ hasNot
  · exact padCopiesEval n C _

end PEqualNP.Outside.L_meta_2592_aux.IdentityPad

namespace PEqualNP.Outside.L_meta_2592_aux.NormalForm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma satGatesIff (n j : ℕ) (gs : List Gate) :
    Normalize.SatGates n j gs ↔ IdentityPad.SatGates n j gs := by
  induction gs generalizing j with
  | nil => rfl
  | cons g gs ih =>
    exact and_congr Iff.rfl (ih (j + 1))

lemma canonicalExactCircuit (n budget : ℕ) (f : (Fin n → Bool) → Bool) (C : Circuit)
    (fan : FanInTwo C) (small : C.size ≤ budget)
    (hasNot : ∃ g ∈ C.gates, g.op = .not)
    (correct : ∀ x, C.eval (List.ofFn x) = f x)
    (nonzero : ∃ x, f x = true)
    (notInput : ∀ i : Fin n, ∃ x, f x ≠ x i) :
    ∃ D : Circuit, D.size = budget ∧ Normalize.SatGates n 0 D.gates ∧
      D.output + 1 = n + 1 + D.size ∧
      (∃ g ∈ D.gates, g.op = .not) ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x ++ [false]) = f x := by
  obtain ⟨D, dsmall, dsat, dlast, dnot, dcorrect⟩ :=
    canonicalLastCircuit n f C fan hasNot correct nonzero notInput
  have dsat' : IdentityPad.SatGates n 0 D.gates := (satGatesIff n 0 D.gates).mp dsat
  obtain ⟨E, esize, esat, elast, enot, eeval⟩ :=
    IdentityPad.padToBudget n budget D (dsmall.trans small) dsat' dlast dnot
  refine ⟨E, esize, (satGatesIff n 0 E.gates).mpr esat, elast, enot, ?_⟩
  intro x
  exact (eeval (List.ofFn x ++ [false]) (by simp)).trans (dcorrect x)

end PEqualNP.Outside.L_meta_2592_aux.NormalForm

namespace PEqualNP.Outside.L_meta_2592_aux.NormalForm

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def petersen (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
  (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

lemma petersenSingleton : ∀ i : Fin 10,
    petersen (fun j => decide (j = i)) = false := by decide

lemma petersenNotInput : ∀ i : Fin 10, ∃ x : Fin 10 → Bool, petersen x ≠ x i := by
  intro i
  refine ⟨fun j => decide (j = i), ?_⟩
  rw [petersenSingleton]
  simp

lemma petersenCanonical19 (C : Circuit) (fan : FanInTwo C) (small : C.size ≤ 19)
    (hasNot : ∃ g ∈ C.gates, g.op = .not)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) :
    ∃ D : Circuit, D.size = 19 ∧ Normalize.SatGates 10 0 D.gates ∧
      D.output + 1 = 11 + D.size ∧
      (∃ g ∈ D.gates, g.op = .not) ∧
      ∀ x : Fin 10 → Bool, D.eval (List.ofFn x ++ [false]) = petersen x := by
  exact canonicalExactCircuit 10 19 petersen C fan small hasNot correct
    ⟨fun _ => true, by decide⟩ petersenNotInput

end PEqualNP.Outside.L_meta_2592_aux.NormalForm
