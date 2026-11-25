import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031_aux.CompactOr

open PEqualNP.CircuitLowerBounds

def meet (values : List Bool) (atoms : List ℕ) : Bool :=
  atoms.all (fun i => values.getD i false)

def step (values : List Bool) (g : List ℕ × List ℕ) : List Bool :=
  values ++ [meet values g.1 || meet values g.2]

def wires (program : List (List ℕ × List ℕ)) (x : List Bool) : List Bool :=
  program.foldl step x

def eval (program : List (List ℕ × List ℕ)) (output : List ℕ) (x : List Bool) : Bool :=
  meet (wires program x) output

def bounded (bound : ℕ) (atoms : List ℕ) : Prop := ∀ i ∈ atoms, i < bound

def wellFormed (n : ℕ) (program : List (List ℕ × List ℕ)) : Prop :=
  ∀ j < program.length,
    bounded (n + j) (program.getD j ([], [])).1 ∧
    bounded (n + j) (program.getD j ([], [])).2

def isOr (g : Gate) : Bool := match g.op with
  | GateOp.or => true
  | _ => false

def orCount (gs : List Gate) : ℕ := gs.countP isOr

lemma meet_append (values : List Bool) (a b : List ℕ) :
    meet values (a ++ b) = (meet values a && meet values b) := by
  simp [meet]

lemma meet_singleton (values : List Bool) (i : ℕ) :
    meet values [i] = values.getD i false := by
  simp [meet]

lemma meet_congr {a b : List Bool} {atoms : List ℕ}
    (h : ∀ i ∈ atoms, a.getD i false = b.getD i false) : meet a atoms = meet b atoms := by
  induction atoms with
  | nil => rfl
  | cons i atoms ih =>
    change (a.getD i false && meet a atoms) = (b.getD i false && meet b atoms)
    rw [h i (by simp), ih (fun j hj => h j (by simp [hj]))]

lemma meet_extend (values suffix : List Bool) (atoms : List ℕ)
    (h : bounded values.length atoms) : meet (values ++ suffix) atoms = meet values atoms := by
  apply meet_congr
  intro i hi
  exact List.getD_append values suffix false i (h i hi)

lemma wires_length (program : List (List ℕ × List ℕ)) (x : List Bool) :
    (wires program x).length = x.length + program.length := by
  induction program generalizing x with
  | nil => simp [wires]
  | cons g gs ih =>
    change (wires gs (step x g)).length = _
    rw [ih]
    simp [step]
    omega

lemma wires_append (program : List (List ℕ × List ℕ)) (g : List ℕ × List ℕ)
    (x : List Bool) : wires (program ++ [g]) x = step (wires program x) g := by
  simp [wires, List.foldl_append]

lemma original_wires_length (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, 0⟩ (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)])).length = _
    rw [ih]
    simp
    omega

lemma original_wires_append (gs : List Gate) (g : Gate) (x : List Bool) :
    Circuit.wires ⟨gs ++ [g], 0⟩ x =
      Circuit.wires ⟨gs, 0⟩ x ++
        [g.op.eval (g.inputs.map fun i => (Circuit.wires ⟨gs, 0⟩ x).getD i false)] := by
  simp [Circuit.wires, List.foldl_append]


def Represents (n : ℕ) (gs : List Gate) (program : List (List ℕ × List ℕ))
    (reps : List (List ℕ)) : Prop :=
  wellFormed n program ∧ reps.length = n + gs.length ∧
  (∀ r ∈ reps, bounded (n + program.length) r) ∧
  ∀ x : List Bool, x.length = n →
    reps.map (meet (wires program x)) = Circuit.wires ⟨gs, 0⟩ x

lemma getD_mem {α : Type} (xs : List α) (d : α) {i : ℕ} (hi : i < xs.length) :
    xs.getD i d ∈ xs := by
  simp [hi]

lemma rep_value {values old : List Bool} {reps : List (List ℕ)} {i : ℕ}
    (hrep : reps.map (meet values) = old) (hi : i < reps.length) :
    meet values (reps.getD i []) = old.getD i false := by
  rw [← hrep]
  simp [hi]

lemma getD_snoc {α : Type} (xs : List α) (a d : α) :
    (xs ++ [a]).getD xs.length d = a := by
  simp [List.getD_eq_getElem?_getD]

lemma represents_nil (n : ℕ) :
    Represents n [] [] ((List.range n).map (fun i => [i])) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro j hj
    simp at hj
  · simp
  · intro r hr
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hr
    intro j hj
    have : j = i := by simpa using hj
    subst j
    simpa using List.mem_range.mp hi
  · intro x hx
    simp only [wires, List.foldl_nil, List.map_map, Circuit.wires]
    apply List.ext_getElem
    · simpa using hx.symm
    · intro i hi hx'
      simp only [List.length_map, List.length_range] at hi
      simp [hx, hi, meet]

lemma represents_and {n : ℕ} {gs : List Gate} {program : List (List ℕ × List ℕ)}
    {reps : List (List ℕ)} (hrep : Represents n gs program reps)
    (a b : ℕ) (ha : a < reps.length) (hb : b < reps.length) :
    Represents n (gs ++ [⟨GateOp.and, [a, b]⟩]) program
      (reps ++ [reps.getD a [] ++ reps.getD b []]) := by
  rcases hrep with ⟨hwf, hlen, hbound, hvalues⟩
  refine ⟨hwf, ?_, ?_, ?_⟩
  · simp [hlen, Nat.add_assoc]
  · intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · exact hbound r hr
    · have heq : r = reps.getD a [] ++ reps.getD b [] := by simpa using hr
      subst r
      intro i hi
      rcases List.mem_append.mp hi with hi | hi
      · exact hbound _ (getD_mem reps [] ha) i hi
      · exact hbound _ (getD_mem reps [] hb) i hi
  · intro x hx
    rw [List.map_append]
    simp only [List.map_singleton, meet_append, original_wires_append]
    rw [hvalues x hx, rep_value (hvalues x hx) ha, rep_value (hvalues x hx) hb]
    simp [GateOp.eval]


lemma wellFormed_append {n : ℕ} {program : List (List ℕ × List ℕ)}
    (hwf : wellFormed n program) (a b : List ℕ)
    (ha : bounded (n + program.length) a) (hb : bounded (n + program.length) b) :
    wellFormed n (program ++ [(a, b)]) := by
  intro j hj
  by_cases hlt : j < program.length
  · rw [List.getD_append program [(a, b)] ([], []) j hlt]
    exact hwf j hlt
  · have heq : j = program.length := by simp only [List.length_append, List.length_singleton] at hj; omega
    subst j
    rw [getD_snoc]
    exact ⟨ha, hb⟩

lemma represents_or {n : ℕ} {gs : List Gate} {program : List (List ℕ × List ℕ)}
    {reps : List (List ℕ)} (hrep : Represents n gs program reps)
    (a b : ℕ) (ha : a < reps.length) (hb : b < reps.length) :
    Represents n (gs ++ [⟨GateOp.or, [a, b]⟩])
      (program ++ [(reps.getD a [], reps.getD b [])])
      (reps ++ [[n + program.length]]) := by
  rcases hrep with ⟨hwf, hlen, hbound, hvalues⟩
  refine ⟨wellFormed_append hwf _ _ (hbound _ (getD_mem reps [] ha))
    (hbound _ (getD_mem reps [] hb)), ?_, ?_, ?_⟩
  · simp [hlen, Nat.add_assoc]
  · intro r hr i hi
    rcases List.mem_append.mp hr with hr | hr
    · have hbnd := hbound r hr i hi
      simp only [List.length_append, List.length_singleton]
      omega
    · have heq : r = [n + program.length] := by simpa using hr
      subst r
      have hieq : i = n + program.length := by simpa using hi
      simp [hieq]
  · intro x hx
    have hmaps : reps.map (meet (wires (program ++ [(reps.getD a [], reps.getD b [])]) x)) =
        reps.map (meet (wires program x)) := by
      apply List.map_congr_left
      intro r hr
      rw [wires_append]
      apply meet_extend
      simpa [wires_length, hx] using hbound r hr
    rw [List.map_append]
    simp only [List.map_singleton, meet_singleton]
    rw [hmaps, hvalues x hx, wires_append]
    change Circuit.wires ⟨gs, 0⟩ x ++
      [(wires program x ++ [meet (wires program x) (reps.getD a []) ||
        meet (wires program x) (reps.getD b [])]).getD (n + program.length) false] = _
    have hwlen : n + program.length = (wires program x).length := by simp [wires_length, hx]
    rw [hwlen, getD_snoc, rep_value (hvalues x hx) ha, rep_value (hvalues x hx) hb]
    simp [original_wires_append, GateOp.eval]


def normalized (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ a b : ℕ,
    gs[j].inputs = [a, b] ∧ a < n + j ∧ b < n + j ∧
      (gs[j].op = GateOp.and ∨ gs[j].op = GateOp.or)

theorem compile (n : ℕ) (gs : List Gate) (hnorm : normalized n gs) :
    ∃ program reps, Represents n gs program reps ∧ program.length = orCount gs := by
  induction gs using List.reverseRecOn with
  | nil =>
    exact ⟨[], (List.range n).map (fun i => [i]), represents_nil n, rfl⟩
  | append_singleton gs g ih =>
    have hprefix : normalized n gs := by
      intro j hj
      obtain ⟨a, b, hp, ha, hb, hop⟩ := hnorm j (by simp; omega)
      exact ⟨a, b, by simpa [List.getElem_append_left hj] using hp, ha, hb,
        by simpa [List.getElem_append_left hj] using hop⟩
    obtain ⟨program, reps, hrep, hcount⟩ := ih hprefix
    obtain ⟨a, b, hp, ha, hb, hop⟩ := hnorm gs.length (by simp)
    have hlast : (gs ++ [g])[gs.length] = g := by simp
    rw [hlast] at hp hop
    have harep : a < reps.length := by rw [hrep.2.1]; exact ha
    have hbrep : b < reps.length := by rw [hrep.2.1]; exact hb
    rcases hop with hand | hor
    · have hg : g = ⟨GateOp.and, [a, b]⟩ := by cases g; simp_all
      subst g
      refine ⟨program, reps ++ [reps.getD a [] ++ reps.getD b []],
        represents_and hrep a b harep hbrep, ?_⟩
      simpa [orCount, isOr] using hcount
    · have hg : g = ⟨GateOp.or, [a, b]⟩ := by cases g; simp_all
      subst g
      refine ⟨program ++ [(reps.getD a [], reps.getD b [])],
        reps ++ [[n + program.length]], represents_or hrep a b harep hbrep, ?_⟩
      simpa [orCount, isOr] using hcount

theorem circuit_translation (n : ℕ) (C : Circuit) (hnorm : normalized n C.gates)
    (hout : C.output < n + C.gates.length) :
    ∃ program output, program.length = orCount C.gates ∧ wellFormed n program ∧
      bounded (n + program.length) output ∧
      ∀ x : List Bool, x.length = n → eval program output x = C.eval x := by
  obtain ⟨program, reps, hrep, hcount⟩ := compile n C.gates hnorm
  have ho : C.output < reps.length := by rw [hrep.2.1]; exact hout
  refine ⟨program, reps.getD C.output [], hcount, hrep.1,
    hrep.2.2.1 _ (getD_mem reps [] ho), ?_⟩
  intro x hx
  exact rep_value (hrep.2.2.2 x hx) ho


lemma meet_wires (program : List (List ℕ × List ℕ)) (x : List Bool) (atoms : List ℕ)
    (hbound : bounded x.length atoms) : meet (wires program x) atoms = meet x atoms := by
  induction program generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change meet (wires gs (step x g)) atoms = meet x atoms
    rw [ih]
    · exact meet_extend x _ atoms hbound
    · intro i hi
      have hb := hbound i hi
      simp only [step, List.length_append, List.length_singleton]
      omega

lemma eval_append (n : ℕ) (program suffix : List (List ℕ × List ℕ)) (output : List ℕ)
    (hbound : bounded (n + program.length) output) (x : List Bool) (hx : x.length = n) :
    eval (program ++ suffix) output x = eval program output x := by
  unfold eval
  have heq : wires (program ++ suffix) x = wires suffix (wires program x) := by
    simp [wires, List.foldl_append]
  rw [heq]
  apply meet_wires
  simpa [wires_length, hx] using hbound

theorem pad_by (n : ℕ) (program : List (List ℕ × List ℕ)) (output : List ℕ)
    (hn : 0 < n) (hwf : wellFormed n program)
    (hbound : bounded (n + program.length) output) (extra : ℕ) :
    ∃ padded, padded.length = program.length + extra ∧ wellFormed n padded ∧
      bounded (n + padded.length) output ∧
      ∀ x : List Bool, x.length = n → eval padded output x = eval program output x := by
  induction extra generalizing program with
  | zero => exact ⟨program, by simp, hwf, hbound, fun _ _ => rfl⟩
  | succ extra ih =>
    let next := program ++ [([0], [0])]
    have hzero : bounded (n + program.length) [0] := by
      intro i hi
      have : i = 0 := by simpa using hi
      omega
    have hnext : wellFormed n next := wellFormed_append hwf [0] [0] hzero hzero
    have hbnext : bounded (n + next.length) output := by
      intro i hi
      have hb := hbound i hi
      simp only [next, List.length_append, List.length_singleton]
      omega
    obtain ⟨padded, hlen, hpwf, hpbound, hpeval⟩ := ih next hnext hbnext
    refine ⟨padded, ?_, hpwf, hpbound, ?_⟩
    · simp only [next, List.length_append, List.length_singleton] at hlen
      omega
    · intro x hx
      exact (hpeval x hx).trans (eval_append n program [([0], [0])] output hbound x hx)

theorem pad_to (n : ℕ) (program : List (List ℕ × List ℕ)) (output : List ℕ)
    (hn : 0 < n) (hwf : wellFormed n program)
    (hbound : bounded (n + program.length) output) (k : ℕ) (hk : program.length ≤ k) :
    ∃ padded, padded.length = k ∧ wellFormed n padded ∧ bounded (n + k) output ∧
      ∀ x : List Bool, x.length = n → eval padded output x = eval program output x := by
  obtain ⟨padded, hlen, hpwf, hpbound, hpeval⟩ := pad_by n program output hn hwf hbound (k - program.length)
  have heq : padded.length = k := by omega
  exact ⟨padded, heq, hpwf, heq ▸ hpbound, hpeval⟩


lemma meet_eq_selection (values : List Bool) (atoms : List ℕ) (bound : ℕ)
    (hbound : bounded bound atoms) :
    meet values atoms = (List.range bound).all
      (fun i => if i ∈ atoms then values.getD i false else true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [meet, List.all_eq_true]
  constructor
  · intro h i hi
    by_cases hm : i ∈ atoms
    · simpa [hm] using h i hm
    · simp [hm]
  · intro h i hi
    have hv := h i (List.mem_range.mpr (hbound i hi))
    simpa [hi] using hv


def mask8 (atoms : List ℕ) : BitVec 8 :=
  BitVec.ofBool (decide (7 ∈ atoms)) ++ BitVec.ofBool (decide (6 ∈ atoms)) ++
  BitVec.ofBool (decide (5 ∈ atoms)) ++ BitVec.ofBool (decide (4 ∈ atoms)) ++
  BitVec.ofBool (decide (3 ∈ atoms)) ++ BitVec.ofBool (decide (2 ∈ atoms)) ++
  BitVec.ofBool (decide (1 ∈ atoms)) ++ BitVec.ofBool (decide (0 ∈ atoms))

lemma mask8_get (atoms : List ℕ) (i : ℕ) (hi : i < 8) :
    (mask8 atoms).getLsbD i = decide (i ∈ atoms) := by
  have hcases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [mask8, BitVec.getLsbD_append] <;> simp

lemma meet_eq_mask8 (values : List Bool) (atoms : List ℕ) (bound : ℕ)
    (hbound : bounded bound atoms) (hsmall : bound ≤ 8) :
    meet values atoms = (List.range bound).all
      (fun i => if (mask8 atoms).getLsbD i then values.getD i false else true) := by
  apply Bool.eq_iff_iff.mpr
  simp only [meet, List.all_eq_true]
  constructor
  · intro h i hi
    rw [mask8_get atoms i (by have := List.mem_range.mp hi; omega)]
    by_cases hm : i ∈ atoms
    · simpa [hm] using h i hm
    · simp [hm]
  · intro h i hi
    have hv := h i (List.mem_range.mpr (hbound i hi))
    rw [mask8_get atoms i (by have := hbound i hi; omega)] at hv
    simpa [hi] using hv


def vmeet (values : List (BitVec 10)) (atoms : List ℕ) : BitVec 10 :=
  atoms.foldr (fun i rest => values.getD i 0 &&& rest) (BitVec.allOnes 10)

def vstep (values : List (BitVec 10)) (g : List ℕ × List ℕ) : List (BitVec 10) :=
  values ++ [vmeet values g.1 ||| vmeet values g.2]

def vwires (program : List (List ℕ × List ℕ)) (x : List (BitVec 10)) : List (BitVec 10) :=
  program.foldl vstep x

def veval (program : List (List ℕ × List ℕ)) (output : List ℕ) (x : List (BitVec 10)) : BitVec 10 :=
  vmeet (vwires program x) output

lemma band_bits (atoms : List ℕ) (f : ℕ → BitVec 10) (i : ℕ) (hi : i < 10) :
    (atoms.foldr (fun a rest => f a &&& rest) (BitVec.allOnes 10)).getLsbD i =
      atoms.all (fun a => (f a).getLsbD i) := by
  induction atoms with
  | nil =>
    change (BitVec.allOnes 10).getLsbD i = true
    rw [BitVec.getLsbD_allOnes]
    simp [hi]
  | cons a atoms ih =>
    simp only [List.foldr_cons, BitVec.getLsbD_and, List.all_cons]
    rw [ih]

lemma vmeet_bits (values : List (BitVec 10)) (atoms : List ℕ) (i : ℕ) (hi : i < 10) :
    (vmeet values atoms).getLsbD i = meet (values.map (fun v => v.getLsbD i)) atoms := by
  rw [vmeet, band_bits atoms _ i hi]
  unfold meet
  apply congrArg (fun f : ℕ → Bool => atoms.all f)
  funext a
  simpa using (List.getD_map values (0 : BitVec 10) (n := a) (fun v => v.getLsbD i)).symm

lemma vwires_bits (program : List (List ℕ × List ℕ)) (values : List (BitVec 10))
    (i : ℕ) (hi : i < 10) :
    (vwires program values).map (fun v => v.getLsbD i) =
      wires program (values.map (fun v => v.getLsbD i)) := by
  induction program generalizing values with
  | nil => rfl
  | cons g gs ih =>
    change (vwires gs (vstep values g)).map (fun v => v.getLsbD i) =
      wires gs (step (values.map (fun v => v.getLsbD i)) g)
    rw [ih]
    apply congrArg (wires gs)
    simp only [vstep, step, List.map_append, List.map_singleton,
      BitVec.getLsbD_or, vmeet_bits values g.1 i hi, vmeet_bits values g.2 i hi]

lemma veval_bits (program : List (List ℕ × List ℕ)) (output : List ℕ)
    (values : List (BitVec 10)) (i : ℕ) (hi : i < 10) :
    (veval program output values).getLsbD i =
      eval program output (values.map (fun v => v.getLsbD i)) := by
  rw [veval, vmeet_bits _ output i hi, vwires_bits program values i hi]
  rfl

def vselect (values : List (BitVec 10)) (bound : ℕ) (p : BitVec 8) : BitVec 10 :=
  (List.range bound).foldr (fun i rest =>
    (if p.getLsbD i then values.getD i 0 else BitVec.allOnes 10) &&& rest) (BitVec.allOnes 10)

lemma vmeet_eq_mask8 (values : List (BitVec 10)) (atoms : List ℕ) (bound : ℕ)
    (hbound : bounded bound atoms) (hsmall : bound ≤ 8) :
    vmeet values atoms = vselect values bound (mask8 atoms) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [vmeet_bits values atoms i hi, meet_eq_mask8 _ atoms bound hbound hsmall]
  rw [vselect, band_bits _ _ i hi]
  apply congrArg (fun f : ℕ → Bool => (List.range bound).all f)
  funext a
  cases hmask : (mask8 atoms).getLsbD a with
  | false =>
    change true = (BitVec.allOnes 10).getLsbD i
    rw [BitVec.getLsbD_allOnes]
    simp [hi]
  | true =>
    simpa [hmask] using List.getD_map values (0 : BitVec 10) (n := a) (fun v => v.getLsbD i)


def cycleInputs : List (BitVec 10) := [113, 387, 550, 204, 792]

def FiniteObstruction : Prop := ∀ a b c d e f o : BitVec 8,
  let v := vselect cycleInputs 5 a ||| vselect cycleInputs 5 b
  let w := vselect (cycleInputs ++ [v]) 6 c ||| vselect (cycleInputs ++ [v]) 6 d
  let z := vselect (cycleInputs ++ [v] ++ [w]) 7 e ||| vselect (cycleInputs ++ [v] ++ [w]) 7 f
  vselect (cycleInputs ++ [v] ++ [w] ++ [z]) 8 o ≠ 31

lemma list_three {α : Type} (l : List α) (hlen : l.length = 3) :
    ∃ a b c, l = [a, b, c] := by
  cases l with
  | nil => simp at hlen
  | cons a l =>
    cases l with
    | nil => simp at hlen
    | cons b l =>
      cases l with
      | nil => simp at hlen
      | cons c l =>
        have hempty : l = [] := by
          cases l with
          | nil => rfl
          | cons d l => simp only [List.length_cons] at hlen; omega
        subst l
        exact ⟨a, b, c, rfl⟩

theorem three_program_obstruction (hfinite : FiniteObstruction)
    (program : List (List ℕ × List ℕ)) (output : List ℕ)
    (hlen : program.length = 3) (hwf : wellFormed 5 program) (houtput : bounded 8 output) :
    veval program output cycleInputs ≠ 31 := by
  obtain ⟨g0, g1, g2, rfl⟩ := list_three program hlen
  have h0 : bounded 5 g0.1 ∧ bounded 5 g0.2 := by simpa using hwf 0 (by simp)
  have h1 : bounded 6 g1.1 ∧ bounded 6 g1.2 := by simpa using hwf 1 (by simp)
  have h2 : bounded 7 g2.1 ∧ bounded 7 g2.2 := by simpa using hwf 2 (by simp)
  let v := vselect cycleInputs 5 (mask8 g0.1) ||| vselect cycleInputs 5 (mask8 g0.2)
  let w := vselect (cycleInputs ++ [v]) 6 (mask8 g1.1) ||| vselect (cycleInputs ++ [v]) 6 (mask8 g1.2)
  let z := vselect (cycleInputs ++ [v] ++ [w]) 7 (mask8 g2.1) |||
    vselect (cycleInputs ++ [v] ++ [w]) 7 (mask8 g2.2)
  have heval : veval [g0, g1, g2] output cycleInputs =
      vselect (cycleInputs ++ [v] ++ [w] ++ [z]) 8 (mask8 output) := by
    simp only [veval, vwires, List.foldl_cons, List.foldl_nil, vstep]
    rw [vmeet_eq_mask8 cycleInputs g0.1 5 h0.1 (by decide),
      vmeet_eq_mask8 cycleInputs g0.2 5 h0.2 (by decide)]
    change vmeet (cycleInputs ++ [v] ++
      [vmeet (cycleInputs ++ [v]) g1.1 ||| vmeet (cycleInputs ++ [v]) g1.2] ++
      [vmeet (cycleInputs ++ [v] ++
        [vmeet (cycleInputs ++ [v]) g1.1 ||| vmeet (cycleInputs ++ [v]) g1.2]) g2.1 |||
       vmeet (cycleInputs ++ [v] ++
        [vmeet (cycleInputs ++ [v]) g1.1 ||| vmeet (cycleInputs ++ [v]) g1.2]) g2.2]) output = _
    rw [vmeet_eq_mask8 (cycleInputs ++ [v]) g1.1 6 h1.1 (by decide),
      vmeet_eq_mask8 (cycleInputs ++ [v]) g1.2 6 h1.2 (by decide)]
    change vmeet (cycleInputs ++ [v] ++ [w] ++
      [vmeet (cycleInputs ++ [v] ++ [w]) g2.1 ||| vmeet (cycleInputs ++ [v] ++ [w]) g2.2]) output = _
    rw [vmeet_eq_mask8 (cycleInputs ++ [v] ++ [w]) g2.1 7 h2.1 (by decide),
      vmeet_eq_mask8 (cycleInputs ++ [v] ++ [w]) g2.2 7 h2.2 (by decide)]
    exact vmeet_eq_mask8 (cycleInputs ++ [v] ++ [w] ++ [z]) output 8 houtput le_rfl
  rw [heval]
  exact hfinite (mask8 g0.1) (mask8 g0.2) (mask8 g1.1) (mask8 g1.2)
    (mask8 g2.1) (mask8 g2.2) (mask8 output)

theorem circuit_four_ors (hfinite : FiniteObstruction) (C : Circuit)
    (hnorm : normalized 5 C.gates) (hout : C.output < 5 + C.gates.length)
    (hvalues : ∀ i : Fin 10,
      C.eval (cycleInputs.map (fun v => v.getLsbD i.val)) = (31 : BitVec 10).getLsbD i.val) :
    4 ≤ orCount C.gates := by
  by_contra hlt
  have hcount : orCount C.gates ≤ 3 := by omega
  obtain ⟨program, output, hlen, hwf, hbound, heval⟩ := circuit_translation 5 C hnorm hout
  obtain ⟨padded, hpadlen, hpadwf, hpadbound, hpadeval⟩ :=
    pad_to 5 program output (by decide) hwf hbound 3 (by omega)
  have hvec : veval padded output cycleInputs = 31 := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    rw [veval_bits padded output cycleInputs i hi]
    have hsize : (cycleInputs.map (fun v => v.getLsbD i)).length = 5 := by simp [cycleInputs]
    rw [hpadeval _ hsize, heval _ hsize]
    exact hvalues ⟨i, hi⟩
  exact three_program_obstruction hfinite padded output hpadlen hpadwf hpadbound hvec


def select8 (p : BitVec 8) (i : Nat) (v : BitVec 10) : BitVec 10 :=
  if p.getLsbD i then v else 1023

def expr0 (p : BitVec 8) : BitVec 10 :=
  select8 p 0 113 &&& select8 p 1 387 &&& select8 p 2 550 &&&
    select8 p 3 204 &&& select8 p 4 792

def expr1 (p : BitVec 8) (v : BitVec 10) : BitVec 10 := expr0 p &&& select8 p 5 v

def expr2 (p : BitVec 8) (v w : BitVec 10) : BitVec 10 := expr1 p v &&& select8 p 6 w

def expr3 (p : BitVec 8) (v w z : BitVec 10) : BitVec 10 := expr2 p v w &&& select8 p 7 z

lemma and1023 (v : BitVec 10) : BitVec.and v (BitVec.ofNat 10 1023) = v := BitVec.and_allOnes

lemma vselect_five (p : BitVec 8) : vselect cycleInputs 5 p = expr0 p := by
  simp [vselect, cycleInputs, List.range_succ, expr0, select8, BitVec.and_assoc]
  simp only [← BitVec.and_assoc]
  exact BitVec.and_allOnes

lemma vselect_six (p : BitVec 8) (v : BitVec 10) :
    vselect (cycleInputs ++ [v]) 6 p = expr1 p v := by
  simp [vselect, cycleInputs, List.range_succ, expr1, expr0, select8, BitVec.and_assoc]
  simp only [← BitVec.and_assoc]
  exact BitVec.and_allOnes

lemma vselect_seven (p : BitVec 8) (v w : BitVec 10) :
    vselect (cycleInputs ++ [v] ++ [w]) 7 p = expr2 p v w := by
  simp [vselect, cycleInputs, List.range_succ, expr2, expr1, expr0, select8, BitVec.and_assoc]
  simp only [← BitVec.and_assoc]
  exact BitVec.and_allOnes

lemma vselect_eight (p : BitVec 8) (v w z : BitVec 10) :
    vselect (cycleInputs ++ [v] ++ [w] ++ [z]) 8 p = expr3 p v w z := by
  simp [vselect, cycleInputs, List.range_succ, expr3, expr2, expr1, expr0, select8, BitVec.and_assoc]
  simp only [← BitVec.and_assoc]
  exact BitVec.and_allOnes

lemma finiteObstruction_of_expanded
    (h : ∀ a b c d e f o : BitVec 8,
      let v := expr0 a ||| expr0 b
      let w := expr1 c v ||| expr1 d v
      let z := expr2 e v w ||| expr2 f v w
      expr3 o v w z ≠ 31) : FiniteObstruction := by
  intro a b c d e f o
  simp only [vselect_five, vselect_six, vselect_seven, vselect_eight]
  exact h a b c d e f o


def cycleTruth (x : Fin 5 → Bool) : Bool :=
  decide (∃ u v : Fin 5, (u + 1 = v ∨ v + 1 = u) ∧ x u = true ∧ x v = true)

lemma cycle_columns : ∀ i : Fin 10,
    cycleTruth (fun j : Fin 5 => (cycleInputs.getD j.val 0).getLsbD i.val) =
      (31 : BitVec 10).getLsbD i.val := by decide

lemma cycle_test_lists : ∀ i : Fin 10,
    List.ofFn (fun j : Fin 5 => (cycleInputs.getD j.val 0).getLsbD i.val) =
      cycleInputs.map (fun v => v.getLsbD i.val) := by decide

theorem cycle_four_ors (hfinite : FiniteObstruction) (C : Circuit)
    (hnorm : normalized 5 C.gates)
    (hcomputes : ∀ x : Fin 5 → Bool, C.eval (List.ofFn x) = cycleTruth x) :
    4 ≤ orCount C.gates := by
  have hvalues : ∀ i : Fin 10,
      C.eval (cycleInputs.map (fun v => v.getLsbD i.val)) = (31 : BitVec 10).getLsbD i.val := by
    intro i
    rw [← cycle_test_lists i, hcomputes]
    exact cycle_columns i
  have hout : C.output < 5 + C.gates.length := by
    by_contra hbad
    have htest := hvalues (0 : Fin 10)
    have htrue : (31 : BitVec 10).getLsbD (0 : Fin 10).val = true := by decide
    rw [htrue] at htest
    have hfalse : C.eval (cycleInputs.map (fun v => v.getLsbD 0)) = false := by
      apply List.getD_eq_default
      change (Circuit.wires ⟨C.gates, 0⟩ (cycleInputs.map (fun v => v.getLsbD 0))).length ≤ C.output
      rw [original_wires_length]
      simp only [List.length_map, cycleInputs, List.length_cons, List.length_nil] at *
      omega
    exact Bool.noConfusion (hfalse.symm.trans htest)
  exact circuit_four_ors hfinite C hnorm hout hvalues

end PEqualNP.Outside.L_meta_1031_aux.CompactOr
