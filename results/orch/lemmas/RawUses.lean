import Restriction

namespace PEqualNP.Outside.L_meta_2592_aux.SignedFloor

open PEqualNP.CircuitLowerBounds

def wireRead {R} (ws : List (Wire R)) (i : Nat) : Wire R := ws.getD i (fun _ => false)

def wireGate {R} (ws : List (Wire R)) (g : Gate) : Wire R :=
  fun r => g.op.eval (g.inputs.map (fun i => wireRead ws i r))

def wireExecute {R} (gs : List Gate) (ws : List (Wire R)) : List (Wire R) :=
  gs.foldl (fun ws g => ws ++ [wireGate ws g]) ws

def binaryReads (j : Nat) (g : Gate) : Bool := !isNot g && g.inputs.contains j

lemma wireRead_available {R} {bank ws : List (Wire R)} (hs : supply true bank ws) (i : Nat) :
    Available true bank (wireRead ws i) := by
  unfold wireRead
  rw [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => exact Or.inr (Or.inl ⟨false, rfl⟩)
  | some a => exact hs a (List.mem_of_getElem? h)

lemma wireGate_two {R} (ws : List (Wire R)) (i j : Nat) (op : Bool) :
    wireGate ws ⟨if op then .or else .and, [i, j]⟩ =
      combine op (wireRead ws i) (wireRead ws j) := by
  funext r
  cases op <;> simp [wireGate, GateOp.eval, combine]

lemma wireGate_one {R} (ws : List (Wire R)) (i : Nat) (op : Bool) :
    wireGate ws ⟨if op then .or else .and, [i]⟩ = wireRead ws i := by
  funext r
  cases op <;> simp [wireGate, GateOp.eval]

lemma wireGate_not {R} (ws : List (Wire R)) (is : List Nat) :
    wireGate ws ⟨.not, is⟩ = inv (wireRead ws (is.headD ws.length)) := by
  cases is with
  | nil =>
    funext r
    simp [wireGate, GateOp.eval, inv, wireRead]
  | cons i is => rfl

lemma wireGate_paid {R} {roots bank ws : List (Wire R)} {p j} (g : Gate)
    (legal : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hp : Reach true roots p bank) (hs : supply true bank ws)
    (hc : Constant (wireRead ws j)) :
    ∃ q next, Reach true roots q next ∧ Available true next (wireGate ws g) ∧
      (∀ v, Available true bank v → Available true next v) ∧
      q + (if binaryReads j g then 1 else 0) ≤ p + (if isNot g then 0 else 1) := by
  classical
  obtain ⟨op, is⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at legal
  have bin (op : Bool) :
      ∃ q next, Reach true roots q next ∧
        Available true next (wireGate ws ⟨if op then .or else .and, is⟩) ∧
        (∀ v, Available true bank v → Available true next v) ∧
        q + (if is.contains j then 1 else 0) ≤ p + 1 := by
    cases is with
    | nil =>
      refine ⟨p, bank, hp, Or.inr (Or.inl ?_), fun _ h => h, by simp⟩
      cases op
      · exact ⟨true, rfl⟩
      · exact ⟨false, rfl⟩
    | cons a is =>
      cases is with
      | nil =>
        refine ⟨p, bank, hp, ?_, fun _ h => h, ?_⟩
        · rw [wireGate_one]
          exact wireRead_available hs a
        · split <;> omega
      | cons b is =>
        have hn : is = [] := by
          have hlen := legal.2
          change (a :: b :: is).length ≤ 2 at hlen
          simp only [List.length_cons] at hlen
          exact List.eq_nil_of_length_eq_zero (by omega)
        subst is
        have ha := wireRead_available hs a
        have hb := wireRead_available hs b
        by_cases hit : j ∈ [a, b]
        · have hconst : Constant (wireRead ws a) ∨ Constant (wireRead ws b) := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
            rcases hit with rfl | rfl
            · exact Or.inl hc
            · exact Or.inr hc
          refine ⟨p, bank, hp, ?_, fun _ h => h, ?_⟩
          · rw [wireGate_two]
            exact from_constant op hconst ha hb
          · simp [hit]
        · refine ⟨p + 1, combine op (wireRead ws a) (wireRead ws b) :: bank,
            Reach.two op hp ha hb, ?_, fun _ h => available_cons _ h, ?_⟩
          · rw [wireGate_two]
            exact Or.inl (by simp)
          · simp [hit]
  rcases legal.1 with rfl | rfl | rfl
  · simpa [isNot, binaryReads] using bin false
  · simpa [isNot, binaryReads] using bin true
  · refine ⟨p, bank, hp, ?_, fun _ h => h, ?_⟩
    · rw [wireGate_not]
      exact avail_inv rfl (wireRead_available hs _)
    · simp [isNot, binaryReads]

lemma execute_read_count {R} {roots bank ws : List (Wire R)} {p j} (gs : List Gate)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hp : Reach true roots p bank) (hs : supply true bank ws)
    (hj : j < ws.length) (hc : Constant (wireRead ws j)) :
    ∃ q next, Reach true roots q next ∧ supply true next (wireExecute gs ws) ∧
      q + gs.countP (binaryReads j) ≤ p + gs.countP (fun g => !isNot g) := by
  induction gs generalizing p bank ws with
  | nil => exact ⟨p, bank, hp, hs, by simp⟩
  | cons g gs ih =>
    obtain ⟨r, mid, hr, hg, inc, hbound⟩ := wireGate_paid g (legal g (by simp)) hp hs hc
    have hsNext : supply true mid (ws ++ [wireGate ws g]) := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact inc v (hs v hv)
      · simpa using List.mem_singleton.mp hv ▸ hg
    have hcNext : Constant (wireRead (ws ++ [wireGate ws g]) j) := by
      unfold wireRead
      rw [List.getD_append _ _ _ _ hj]
      exact hc
    obtain ⟨q, next, hq, hnext, htail⟩ := ih
      (fun h hh => legal h (by simp [hh])) hr hsNext (by simp; omega) hcNext
    refine ⟨q, next, hq, hnext, ?_⟩
    simp only [List.countP_cons] at htail ⊢
    cases hn : isNot g <;> cases hb : binaryReads j g <;> simp [hn, hb] at hbound ⊢ <;> omega

lemma wireRead_values {R} (ws : List (Wire R)) (r : R) (i : Nat) :
    wireRead ws i r = (ws.map (fun w => w r)).getD i false := by
  simp only [wireRead, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[i]? <;> rfl

lemma wireGate_values {R} (ws : List (Wire R)) (r : R) (g : Gate) :
    wireGate ws g r = g.op.eval (g.inputs.map (fun i =>
      (ws.map (fun w => w r)).getD i false)) := by
  simp only [wireGate, wireRead_values]

lemma wireExecute_values {R} (gs : List Gate) (ws : List (Wire R)) (r : R) :
    (wireExecute gs ws).map (fun w => w r) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))])
        (ws.map (fun w => w r)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    rw [wireExecute, List.foldl_cons]
    change (wireExecute gs (ws ++ [wireGate ws g])).map (fun w => w r) = _
    rw [ih]
    simp only [List.map_append, List.map_cons, List.map_nil, wireGate_values, List.foldl_cons]

lemma circuit_read_lower {R} {roots bank ws : List (Wire R)} {p j L} (C : Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (hp : Reach true roots p bank) (hs : supply true bank ws)
    (hj : j < ws.length) (hc : Constant (wireRead ws j))
    {goal : Wire R} (computes : ∀ r, C.eval (ws.map (fun w => w r)) = goal r)
    (hl : ∀ q bs, Reach true roots q bs → Available true bs goal → L ≤ q) :
    L + C.gates.countP (binaryReads j) ≤ p + C.gates.countP (fun g => !isNot g) := by
  obtain ⟨q, next, hq, hsNext, hbound⟩ := execute_read_count C.gates legal hp hs hj hc
  have hread := wireRead_available hsNext C.output
  have he : wireRead (wireExecute C.gates ws) C.output = goal := by
    funext r
    rw [wireRead_values, wireExecute_values]
    exact computes r
  rw [he] at hread
  have hlow := hl q next hq hread
  omega

def rawInitial (j : Fin 10) : List (Wire Row) :=
  Extended.pins.map (fun a => restrictRows (rowsFor j) (Extended.observe a))

lemma rawInitial_read (j : Fin 10) :
    wireRead (rawInitial j) j.val =
      restrictRows (rowsFor j)
        (Extended.observe (Extended.pins.getD j.val Extended.zero)) := by
  have hz : restrictRows (rowsFor j) (Extended.observe Extended.zero) = fun _ => false := by
    funext r
    simp [restrictRows, Extended.observe, Extended.bit, Extended.zero]
  simp only [wireRead, rawInitial, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases Extended.pins[j.val]? <;> simp [hz]

lemma rawInitial_values (j : Fin 10) (r : Row) :
    (rawInitial j).map (fun w => w r) = List.ofFn (Extended.assign (rowsFor j r)) := by
  have hp : Extended.pins = List.ofFn (fun i : Fin 10 =>
      Extended.pins.getD i.val Extended.zero) := by decide +kernel
  unfold rawInitial
  rw [hp]
  simp only [List.map_ofFn]
  rfl

lemma petersen_read_floor (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x)
    (j : Fin 10) :
    15 + C.gates.countP (binaryReads j.val) ≤ C.gates.countP (fun g => !isNot g) := by
  have supplyRoots : supply true (inputs.map observe) (rawInitial j) := by
    intro a ha
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp ha
    exact restriction_of_pin_is_available j v hv
  have hj : j.val < (rawInitial j).length := by
    simpa [rawInitial, Extended.pins] using j.isLt
  have hc : Constant (wireRead (rawInitial j) j.val) := by
    rw [rawInitial_read]
    exact restriction_of_selected_pin j
  have same : ∀ r, C.eval ((rawInitial j).map (fun w => w r)) = observe graph r := by
    intro r
    rw [rawInitial_values, computes]
    have he := congrFun (restriction_of_goal j) r
    exact (Extended.rowTarget (rowsFor j r)).symm.trans he
  have bound := circuit_read_lower C legal Reach.start supplyRoots hj hc same nineFloor
  simpa using bound

lemma twoNot_raw_reads (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x)
    (budget : C.size ≤ 19) (many : 2 ≤ PEqualNP.NotBracket.notCount C) (j : Fin 10) :
    C.gates.countP (binaryReads j.val) ≤ 2 := by
  have bound := petersen_read_floor C legal computes j
  have sameNot :
      (fun g : Gate => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)) =
        isNot := by
    funext g
    obtain ⟨op, operands⟩ := g
    cases op <;> rfl
  rw [PEqualNP.NotBracket.notCount, sameNot, ← List.countP_eq_length_filter] at many
  have negSame : (fun g : Gate => decide (¬ isNot g = true)) =
      (fun g => !isNot g) := by
    funext g
    cases isNot g <;> rfl
  have count := List.length_eq_countP_add_countP isNot (l := C.gates)
  rw [negSame] at count
  change C.gates.length ≤ 19 at budget
  omega

end PEqualNP.Outside.L_meta_2592_aux.SignedFloor
