import PEqualNP.Defs
import Mathlib.Data.List.GetD

namespace PEqualNP.Outside.L_meta_2373_aux

namespace Repair


def base : List Nat := [0, 28, 41, 50, 74, 81, 91, 94, 100, 109, 115, 127]

def gate (s : List Nat) (t : Nat) : Bool :=
  s.contains t || s.any (fun a => (a ^^^ 127 == t) ||
    s.any (fun b => (a &&& b == t) || (a ||| b == t)))

def found : Bool :=
  (List.range 128).any fun a => gate base a &&
    (List.range 128).any fun b => gate (a :: base) b && gate (b :: a :: base) 7

lemma gate_iff (s : List Nat) (t : Nat) : gate s t = true ↔
    t ∈ s ∨ ∃ a ∈ s, a ^^^ 127 = t ∨
      ∃ b ∈ s, a &&& b = t ∨ a ||| b = t := by
  simp only [gate, Bool.or_eq_true, List.contains_iff_mem, List.any_eq_true, beq_iff_eq]

def newGate (s : List Nat) (a t : Nat) : Bool :=
  (a == t) || (a ^^^ 127 == t) ||
    s.any (fun b => (a &&& b == t) || (a ||| b == t))

lemma any_or (s : List Nat) (f g : Nat → Bool) :
    s.any (fun x => f x || g x) = (s.any f || s.any g) := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    simp only [List.any_cons, ih]
    simp only [Bool.or_assoc, Bool.or_left_comm]

lemma gate_cons (s : List Nat) (a t : Nat) :
    gate (a :: s) t = (gate s t || newGate s a t) := by
  simp only [gate, newGate, List.contains_cons, List.any_cons, any_or,
    Nat.and_self, Nat.or_self, Nat.and_comm, Nat.or_comm,
    Bool.or_assoc, Bool.or_left_comm, Bool.or_comm,
    Bool.or_self_left, Bool.beq_comm]

def baseMask : Nat := 338833231531871374419584398226125820695

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma baseMask_correct (a : Fin 128) : gate base a.val = baseMask.testBit a.val := by
  revert a
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma newGate_target (a : Fin 128) :
    newGate base a.val 7 = ((a.val == 7) || (a.val == 120)) := by
  revert a
  decide +kernel

def targetFast (a b : Nat) : Bool :=
  (a == 7) || (a == 120) || (b == 7) || (b == 120) ||
    (a &&& b == 7) || (a ||| b == 7)

lemma pair_target (a b : Fin 128) :
    gate (b.val :: a.val :: base) 7 = targetFast a.val b.val := by
  have hb : newGate (a.val :: base) b.val 7 =
      (newGate base b.val 7 || (b.val &&& a.val == 7) || (b.val ||| a.val == 7)) := by
    simp only [newGate, List.any_cons, Bool.or_assoc, Bool.or_left_comm, Bool.or_comm]
  rw [gate_cons, gate_cons, show gate base 7 = false from by decide, hb,
    newGate_target a, newGate_target b]
  simp only [targetFast, Bool.false_or, Nat.and_comm, Nat.or_comm,
    Bool.or_left_comm, Bool.or_comm]

def fastFound : Bool :=
  (List.range 128).any fun a => baseMask.testBit a &&
    (List.range 128).any fun b =>
      (baseMask.testBit b || newGate base a b) && targetFast a b

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma fastFound_false : fastFound = false := by decide +kernel

lemma found_false : found = false := by
  cases hf : found with
  | false => rfl
  | true =>
    have hf' := hf
    simp only [found, List.any_eq_true, List.mem_range, Bool.and_eq_true] at hf'
    obtain ⟨a, ha, hga, b, hb, hgb, hgt⟩ := hf'
    have ha' := baseMask_correct ⟨a, ha⟩
    have hb' := baseMask_correct ⟨b, hb⟩
    have ht' := pair_target ⟨a, ha⟩ ⟨b, hb⟩
    rw [ha'] at hga
    rw [gate_cons, hb'] at hgb
    rw [ht'] at hgt
    have hfast : fastFound = true := by
      simp only [fastFound, List.any_eq_true, List.mem_range, Bool.and_eq_true]
      exact ⟨a, ha, hga, b, hb, hgb, hgt⟩
    rw [fastFound_false] at hfast
    cases hfast

lemma cannot_repair (a b : Fin 128) (ha : gate base a.val = true)
    (hb : gate (a.val :: base) b.val = true) :
    gate (b.val :: a.val :: base) 7 = false := by
  cases hc : gate (b.val :: a.val :: base) 7 with
  | false => rfl
  | true =>
    have h : found = true := by
      simp only [found, List.any_eq_true, List.mem_range, Bool.and_eq_true]
      exact ⟨a.val, a.isLt, ha, b.val, b.isLt, hb, hc⟩
    rw [found_false] at h
    contradiction

lemma cannot_repair_three (a b c : Fin 128) (ha : gate base a.val = true)
    (hb : gate (a.val :: base) b.val = true)
    (hc : gate (b.val :: a.val :: base) c.val = true) : c.val ≠ 7 := by
  intro h
  rw [h, cannot_repair a b ha hb] at hc
  contradiction

def inputProfiles : List Nat := [41, 0, 74, 50, 0, 81, 28, 0, 0, 100]

lemma constant_profiles_available : 0 ∈ base ∧ 127 ∈ base := by decide



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def profileOp (op : GateOp) (l : List Nat) : Nat :=
  match op with
  | .and => l.foldr (· &&& ·) 127
  | .or => l.foldr (· ||| ·) 0
  | .not => l.headD 0 ^^^ 127
  | _ => 0

def profileStep (s : List Nat) (g : Gate) : List Nat :=
  s ++ [profileOp g.op (g.inputs.map (fun i => s.getD i 0))]

def profileWires (gs : List Gate) (s : List Nat) : List Nat :=
  gs.foldl profileStep s

lemma true_profile (r : Fin 7) : (127 : Nat).testBit r.val = true := by
  revert r
  decide

lemma profile_and (l : List Nat) (r : Fin 7) :
    (l.foldr (· &&& ·) 127).testBit r.val =
      (l.map (fun n => n.testBit r.val)).all id := by
  induction l with
  | nil => simp [true_profile]
  | cons a l ih => simp [Nat.testBit_and, ih]

lemma profile_or (l : List Nat) (r : Fin 7) :
    (l.foldr (· ||| ·) 0).testBit r.val =
      (l.map (fun n => n.testBit r.val)).any id := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Nat.testBit_or, ih]

lemma profile_op_correct (op : GateOp) (l : List Nat) (r : Fin 7)
    (hop : op = .and ∨ op = .or ∨ op = .not) :
    (profileOp op l).testBit r.val =
      op.eval (l.map (fun n => n.testBit r.val)) := by
  rcases hop with rfl | rfl | rfl
  · exact profile_and l r
  · exact profile_or l r
  · cases l <;> simp [profileOp, GateOp.eval, Nat.testBit_xor, true_profile]

lemma profile_step_correct (s : List Nat) (g : Gate) (r : Fin 7)
    (hop : g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    (profileStep s g).map (fun n => n.testBit r.val) =
      s.map (fun n => n.testBit r.val) ++
        [g.op.eval (g.inputs.map (fun i =>
          (s.map (fun n => n.testBit r.val)).getD i false))] := by
  simp only [profileStep, List.map_append, List.map_cons, List.map_nil,
    profile_op_correct _ _ r hop]
  congr 2
  rw [List.map_map]
  apply congrArg g.op.eval
  apply List.map_congr_left
  intro i hi
  simpa using (List.getD_map (l := s) (d := 0) (n := i) (fun n => n.testBit r.val)).symm

lemma profile_wires_correct (gs : List Gate) (s : List Nat) (r : Fin 7)
    (hops : ∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not) :
    (profileWires gs s).map (fun n => n.testBit r.val) =
      ({ gates := gs, output := 0 } : Circuit).wires
        (s.map (fun n => n.testBit r.val)) := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    simp only [profileWires, List.foldl_cons]
    rw [show gs.foldl profileStep (profileStep s g) =
      profileWires gs (profileStep s g) from rfl]
    rw [ih _ (fun q hq => hops q (List.mem_cons_of_mem g hq))]
    rw [profile_step_correct s g r (hops g (by simp))]
    rfl

lemma and_mask (a : Nat) (ha : a < 128) : a &&& 127 = a := by
  simpa [Nat.mod_eq_of_lt ha] using Nat.and_two_pow_sub_one_eq_mod a 7

lemma generated_mem (s : List Nat) (a : Nat) (ha : a ∈ s) : gate s a = true :=
  (gate_iff s a).2 (Or.inl ha)

lemma generated_not (s : List Nat) (a : Nat) (ha : a ∈ s) :
    gate s (a ^^^ 127) = true :=
  (gate_iff s _).2 (Or.inr ⟨a, ha, Or.inl rfl⟩)

lemma generated_and (s : List Nat) (a b : Nat) (ha : a ∈ s) (hb : b ∈ s) :
    gate s (a &&& b) = true :=
  (gate_iff s _).2 (Or.inr ⟨a, ha, Or.inr ⟨b, hb, Or.inl rfl⟩⟩)

lemma generated_or (s : List Nat) (a b : Nat) (ha : a ∈ s) (hb : b ∈ s) :
    gate s (a ||| b) = true :=
  (gate_iff s _).2 (Or.inr ⟨a, ha, Or.inr ⟨b, hb, Or.inr rfl⟩⟩)

lemma profile_op_generated (s l : List Nat) (op : GateOp)
    (h0 : 0 ∈ s) (h127 : 127 ∈ s)
    (hop : op = .and ∨ op = .or ∨ op = .not)
    (hlen : l.length ≤ 2) (hin : ∀ a ∈ l, a ∈ s ∧ a < 128) :
    gate s (profileOp op l) = true ∧ profileOp op l < 128 := by
  cases l with
  | nil =>
    rcases hop with rfl | rfl | rfl <;>
      simp only [profileOp, List.foldr_nil, List.headD_nil, Nat.zero_xor]
    · exact ⟨generated_mem s 127 h127, by decide⟩
    · exact ⟨generated_mem s 0 h0, by decide⟩
    · exact ⟨generated_mem s 127 h127, by decide⟩
  | cons a l =>
    have ha := hin a (by simp)
    cases l with
    | nil =>
      rcases hop with rfl | rfl | rfl <;>
        simp only [profileOp, List.foldr_cons, List.foldr_nil, List.headD_cons,
          Nat.or_zero, and_mask a ha.2]
      · exact ⟨generated_mem s a ha.1, ha.2⟩
      · exact ⟨generated_mem s a ha.1, ha.2⟩
      · exact ⟨generated_not s a ha.1, Nat.xor_lt_two_pow (n := 7) ha.2 (by decide)⟩
    | cons b l =>
      have hb := hin b (by simp)
      have hl : l = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hlen; omega)
      subst l
      rcases hop with rfl | rfl | rfl <;>
        simp only [profileOp, List.foldr_cons, List.foldr_nil, List.headD_cons,
          Nat.or_zero, and_mask b hb.2]
      · exact ⟨generated_and s a b ha.1 hb.1, Nat.and_lt_two_pow (n := 7) a hb.2⟩
      · exact ⟨generated_or s a b ha.1 hb.1, Nat.or_lt_two_pow (n := 7) ha.2 hb.2⟩
      · exact ⟨generated_not s a ha.1, Nat.xor_lt_two_pow (n := 7) ha.2 (by decide)⟩

def supported (w s : List Nat) : Prop := ∀ a ∈ w, a ∈ s ∧ a < 128

def profileValue (w : List Nat) (g : Gate) : Nat :=
  profileOp g.op (g.inputs.map (fun i => w.getD i 0))

lemma getD_supported (w s : List Nat) (hw : supported w s) (h0 : 0 ∈ s) (i : Nat) :
    w.getD i 0 ∈ s ∧ w.getD i 0 < 128 := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem w 0 hi]
    exact hw _ (List.getElem_mem hi)
  · rw [List.getD_eq_default w 0 (by omega)]
    exact ⟨h0, by decide⟩

lemma profile_step_generated (w s : List Nat) (g : Gate)
    (hw : supported w s) (h0 : 0 ∈ s) (h127 : 127 ∈ s)
    (hg : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    gate s (profileValue w g) = true ∧ profileValue w g < 128 ∧
      supported (profileStep w g) (profileValue w g :: s) := by
  have h := profile_op_generated s (g.inputs.map (fun i => w.getD i 0)) g.op
    h0 h127 hg.1 (by simpa using hg.2) (by
      intro a ha
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
      exact getD_supported w s hw h0 i)
  refine ⟨h.1, h.2, ?_⟩
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact ⟨List.mem_cons_of_mem _ (hw a ha).1, (hw a ha).2⟩
  · have heq : a = profileValue w g := by simpa [profileValue] using ha
    subst a
    exact ⟨List.mem_cons_self, h.2⟩

lemma three_profiles_no_target (w : List Nat) (g h k : Gate)
    (hw : supported w base)
    (hg : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hh : (h.op = .and ∨ h.op = .or ∨ h.op = .not) ∧ h.inputs.length ≤ 2)
    (hk : (k.op = .and ∨ k.op = .or ∨ k.op = .not) ∧ k.inputs.length ≤ 2) :
    ∀ z ∈ profileWires [g, h, k] w, z ≠ 7 := by
  let a := profileValue w g
  let b := profileValue (profileStep w g) h
  let c := profileValue (profileStep (profileStep w g) h) k
  have ha := profile_step_generated w base g hw (by decide) (by decide) hg
  have hb := profile_step_generated (profileStep w g) (a :: base) h ha.2.2
    (by simp [base]) (by simp [base]) hh
  have hc := profile_step_generated (profileStep (profileStep w g) h) (b :: a :: base) k
    hb.2.2 (by simp [base]) (by simp [base]) hk
  have hcheck := cannot_repair ⟨a, ha.2.1⟩ ⟨b, hb.2.1⟩ ha.1 hb.1
  intro z hz hz7
  have hz' : z ∈ c :: b :: a :: base := (hc.2.2 z hz).1
  rcases List.mem_cons.mp hz' with hzc | hz'
  · have heq : c = 7 := hzc.symm.trans hz7
    have hcg : gate (b :: a :: base) c = true := hc.1
    rw [heq, hcheck] at hcg
    contradiction
  · have hgate := generated_mem (b :: a :: base) z hz'
    rw [hz7, hcheck] at hgate
    contradiction

lemma mem_profile_wires (gs : List Gate) (w : List Nat) (z : Nat) (hz : z ∈ w) :
    z ∈ profileWires gs w := by
  induction gs generalizing w with
  | nil => exact hz
  | cons g gs ih =>
    apply ih (profileStep w g)
    exact List.mem_append_left _ hz

lemma profiles_no_target (C : Circuit) (w : List Nat)
    (hfan : FanInTwo C) (hsize : C.size ≤ 3) (hw : supported w base) :
    ∀ z ∈ profileWires C.gates w, z ≠ 7 := by
  let emptyOr : Gate := ⟨.or, []⟩
  let extra := List.replicate (3 - C.gates.length) emptyOr
  have hlen : (C.gates ++ extra).length = 3 := by
    simp only [List.length_append, extra, List.length_replicate]
    change C.gates.length ≤ 3 at hsize
    omega
  have hgood : ∀ q ∈ C.gates ++ extra,
      (q.op = .and ∨ q.op = .or ∨ q.op = .not) ∧ q.inputs.length ≤ 2 := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hfan q hq
    · obtain ⟨_, rfl⟩ := List.mem_replicate.mp hq
      exact ⟨Or.inr (Or.inl rfl), by decide⟩
  obtain ⟨g, h, k, heq⟩ := List.length_eq_three.mp hlen
  have hgood' : ∀ q ∈ [g, h, k],
      (q.op = .and ∨ q.op = .or ∨ q.op = .not) ∧ q.inputs.length ≤ 2 := by
    simpa only [heq] using hgood
  have H := three_profiles_no_target w g h k hw
    (hgood' g (by simp)) (hgood' h (by simp)) (hgood' k (by simp))
  intro z hz
  apply H z
  rw [← heq]
  simpa only [profileWires, List.foldl_append] using
    mem_profile_wires extra (profileWires C.gates w) z hz

lemma output_profile_no_target (C : Circuit) (w : List Nat)
    (hfan : FanInTwo C) (hsize : C.size ≤ 3) (hw : supported w base) :
    (profileWires C.gates w).getD C.output 0 ≠ 7 := by
  by_cases hi : C.output < (profileWires C.gates w).length
  · rw [List.getD_eq_getElem _ 0 hi]
    exact profiles_no_target C w hfan hsize hw _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ 0 (by omega)]
    decide

lemma profile_wires_bounded (gs : List Gate) (w : List Nat)
    (hgood : ∀ g ∈ gs,
      (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (hw : ∀ a ∈ w, a < 128) : ∀ a ∈ profileWires gs w, a < 128 := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    have h := profile_step_generated w (0 :: 127 :: w) g
      (fun a ha => ⟨by simp [ha], hw a ha⟩) (by simp) (by simp)
      (hgood g (by simp))
    exact ih (profileStep w g) (fun q hq => hgood q (by simp [hq]))
      (fun a ha => (h.2.2 a ha).2)

lemma seven_bits_determine (m : Nat) (hm : m < 128)
    (h : ∀ r : Fin 7, m.testBit r.val = (7 : Nat).testBit r.val) : m = 7 := by
  have H : ∀ v : Fin 128,
      (∀ r : Fin 7, v.val.testBit r.val = (7 : Nat).testBit r.val) → v.val = 7 := by
    decide
  exact H ⟨m, hm⟩ h

lemma no_three_gate_separator (C : Circuit) (w : List Nat)
    (hfan : FanInTwo C) (hsize : C.size ≤ 3) (hw : supported w base) :
    ¬ ∀ r : Fin 7, C.eval (w.map (fun n => n.testBit r.val)) = decide (r.val < 3) := by
  intro heval
  have hgood : ∀ g ∈ C.gates,
      (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hfan g hg
  let out := (profileWires C.gates w).getD C.output 0
  have hout : out < 128 := by
    by_cases hi : C.output < (profileWires C.gates w).length
    · rw [show out = (profileWires C.gates w).getD C.output 0 from rfl,
        List.getD_eq_getElem _ 0 hi]
      exact profile_wires_bounded C.gates w hgood (fun a ha => (hw a ha).2)
        _ (List.getElem_mem hi)
    · rw [show out = (profileWires C.gates w).getD C.output 0 from rfl,
        List.getD_eq_default _ 0 (by omega)]
      decide
  apply output_profile_no_target C w hfan hsize hw
  apply seven_bits_determine out hout
  intro r
  have ht : (7 : Nat).testBit r.val = decide (r.val < 3) := by
    revert r
    decide
  have H := heval r
  unfold Circuit.eval at H
  have hwire := profile_wires_correct C.gates w r (fun g hg => (hgood g hg).1)
  change (profileWires C.gates w).map (fun n => n.testBit r.val) =
    C.wires (w.map (fun n => n.testBit r.val)) at hwire
  rw [← hwire] at H
  have hget := List.getD_map (l := profileWires C.gates w) (d := 0)
    (n := C.output) (fun n => n.testBit r.val)
  simp only [Nat.zero_testBit] at hget
  rw [hget] at H
  exact H.trans ht.symm

def criticalInput (r : Fin 7) (i : Fin 10) : Bool :=
  ([33, 12, 576, 69, 104, 521, 548].getD r.val 0).testBit i.val

def nearMiss : Circuit :=
  ⟨[⟨.or, [5, 3]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [2, 5]⟩,
    ⟨.or, [10, 6]⟩, ⟨.or, [11, 3]⟩, ⟨.or, [13, 9]⟩, ⟨.or, [12, 0]⟩,
    ⟨.and, [17, 14]⟩, ⟨.and, [4, 15]⟩, ⟨.and, [18, 15]⟩, ⟨.or, [20, 7]⟩,
    ⟨.and, [17, 1]⟩, ⟨.or, [19, 22]⟩, ⟨.and, [14, 8]⟩,
    ⟨.and, [21, 16]⟩, ⟨.or, [25, 24]⟩, ⟨.or, [26, 23]⟩], 27⟩

lemma nearMiss_fanInTwo : FanInTwo nearMiss := by
  simp [FanInTwo, nearMiss]

lemma nearMiss_size : nearMiss.size = 18 := by decide

lemma input_profiles_correct (r : Fin 7) :
    inputProfiles.map (fun n => n.testBit r.val) = List.ofFn (criticalInput r) := by
  revert r
  decide

lemma nearMiss_profiles_supported :
    supported (profileWires nearMiss.gates inputProfiles) base := by
  unfold supported
  decide

lemma nearMiss_unrepairable (C : Circuit) (hfan : FanInTwo C) (hsize : C.size ≤ 3) :
    ¬ ∀ r : Fin 7,
      C.eval (nearMiss.wires (List.ofFn (criticalInput r))) = decide (r.val < 3) := by
  intro h
  apply no_three_gate_separator C (profileWires nearMiss.gates inputProfiles)
    hfan hsize nearMiss_profiles_supported
  intro r
  rw [profile_wires_correct]
  · rw [input_profiles_correct]
    exact h r
  · intro g hg
    have hg' := (nearMiss_fanInTwo g hg).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hg'

def petersen (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

lemma critical_target (r : Fin 7) : petersen (criticalInput r) = decide (r.val < 3) := by
  revert r
  decide

lemma nearMiss_no_repair (C : Circuit) (hfan : FanInTwo C) (hsize : C.size ≤ 3) :
    ¬ ∀ x : Fin 10 → Bool,
      C.eval (nearMiss.wires (List.ofFn x)) = petersen x := by
  intro h
  apply nearMiss_unrepairable C hfan hsize
  intro r
  exact (h (criticalInput r)).trans (critical_target r)


end Repair


namespace Factor

def boolVectors : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (boolVectors n).flatMap (fun bs => [false :: bs, true :: bs])

lemma mem_boolVectors (bs : List Bool) : bs ∈ boolVectors bs.length := by
  induction bs with
  | nil => simp [boolVectors]
  | cons b bs ih =>
    apply List.mem_flatMap.mpr
    refine ⟨bs, ih, ?_⟩
    cases b <;> simp

def factorRules (bs : List Bool) (ps : List (Nat × Nat))
    (hs : List (Nat × Nat × Nat)) : Bool :=
  ps.all (fun p => bs.getD p.1 false != bs.getD p.2 false) &&
    hs.all (fun h => !(bs.getD h.1 false) || !(bs.getD h.2.1 false) ||
      bs.getD h.2.2 false)

def factorUnsat (n : Nat) (ps : List (Nat × Nat))
    (hs : List (Nat × Nat × Nat)) : Bool :=
  (boolVectors n).all (fun bs => !(factorRules bs ps hs))

lemma factorUnsat_sound (n : Nat) (ps : List (Nat × Nat))
    (hs : List (Nat × Nat × Nat)) (A : Nat → Prop)
    (hp : ∀ p ∈ ps, p.1 < n ∧ p.2 < n ∧
      (((A p.1 ∧ A p.2) ∨ (¬ A p.1 ∧ ¬ A p.2)) → False))
    (hh : ∀ h ∈ hs, h.1 < n ∧ h.2.1 < n ∧ h.2.2 < n ∧
      (A h.1 → A h.2.1 → A h.2.2))
    (checked : factorUnsat n ps hs = true) : False := by
  classical
  let bs := List.ofFn (fun i : Fin n => decide (A i.val))
  have member : bs ∈ boolVectors n := by
    simpa [bs] using mem_boolVectors bs
  have get (i : Nat) (hi : i < n) : bs.getD i false = decide (A i) := by
    simp [bs, List.getD_eq_getElem?_getD, hi]
  have satisfied : factorRules bs ps hs = true := by
    simp only [factorRules, Bool.and_eq_true]
    constructor
    · apply List.all_eq_true.mpr
      intro p mem
      obtain ⟨ha, hb, h⟩ := hp p mem
      rw [get _ ha, get _ hb]
      by_cases pa : A p.1 <;> by_cases pb : A p.2 <;> simp_all
    · apply List.all_eq_true.mpr
      intro p mem
      obtain ⟨ha, hb, hc, h⟩ := hh p mem
      rw [get _ ha, get _ hb, get _ hc]
      by_cases pa : A p.1 <;> by_cases pb : A p.2.1 <;>
        by_cases pc : A p.2.2 <;> simp_all
  have rejected := List.all_eq_true.mp checked bs member
  rw [satisfied] at rejected
  contradiction

lemma eightVariableCore : factorUnsat 8 [(0, 1), (2, 7)]
    [(0, 2, 4), (0, 7, 4), (1, 2, 5), (1, 7, 2), (2, 4, 7),
      (2, 5, 6), (3, 6, 7), (4, 7, 2), (5, 6, 3)] = true := by
  decide +kernel

end Factor

end PEqualNP.Outside.L_meta_2373_aux
