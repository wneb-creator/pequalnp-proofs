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

end PEqualNP.Outside.L_meta_1031_aux.CompactOr
