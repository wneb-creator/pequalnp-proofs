import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592.Restriction
open PEqualNP.CircuitLowerBounds

abbrev Signal (R : Type) := R → Bool

def read {R} (w : List (Signal R)) (i : Nat) : Signal R :=
  w.getD i (fun _ => false)

def gateSignal {R} (w : List (Signal R)) (g : Gate) : Signal R :=
  fun x => g.op.eval (g.inputs.map (fun i => read w i x))

def execute {R} : List Gate → List (Signal R) → List (Signal R)
  | [], w => w
  | g :: gs, w => execute gs (w ++ [gateSignal w g])

def WireConstant {R} (a : Signal R) : Prop := ∃ b, a = fun _ => b

def KilledNot {R} (gs : List Gate) (w : List (Signal R)) : Prop :=
  ∀ pre g post, gs = pre ++ g :: post → g.op = .not →
    WireConstant (gateSignal (execute pre w) g)

lemma read_mono {R : Type} [Preorder R] {w : List (Signal R)}
    (hw : ∀ a ∈ w, Monotone a) (i : Nat) : Monotone (read w i) := by
  by_cases h : i < w.length
  · rw [read, List.getD_eq_getElem _ _ h]
    exact hw _ (List.getElem_mem h)
  · have he : read w i = fun _ => false := by simp [read, h]
    rw [he]
    exact monotone_const

private lemma and_mono {a b c d : Bool} (h : a ≤ b) (j : c ≤ d) :
    (a && c) ≤ (b && d) := by cases a <;> cases b <;> cases c <;> cases d <;> simp_all

private lemma or_mono {a b c d : Bool} (h : a ≤ b) (j : c ≤ d) :
    (a || c) ≤ (b || d) := by cases a <;> cases b <;> cases c <;> cases d <;> simp_all

lemma all_mono {R : Type} [Preorder R] {w : List (Signal R)}
    (hw : ∀ a ∈ w, Monotone a) (is : List Nat) :
    Monotone (fun x => (is.map (fun i => read w i x)).all id) := by
  induction is with
  | nil => exact monotone_const
  | cons i is ih =>
    intro x y hxy
    simpa only [List.map_cons, List.all_cons, id_eq] using and_mono (read_mono hw i hxy) (ih hxy)

lemma any_mono {R : Type} [Preorder R] {w : List (Signal R)}
    (hw : ∀ a ∈ w, Monotone a) (is : List Nat) :
    Monotone (fun x => (is.map (fun i => read w i x)).any id) := by
  induction is with
  | nil => exact monotone_const
  | cons i is ih =>
    intro x y hxy
    simpa only [List.map_cons, List.any_cons, id_eq] using or_mono (read_mono hw i hxy) (ih hxy)

lemma gate_mono {R : Type} [Preorder R] {w : List (Signal R)} {g : Gate}
    (hw : ∀ a ∈ w, Monotone a) (hg : g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (hn : g.op = .not → WireConstant (gateSignal w g)) : Monotone (gateSignal w g) := by
  rcases hg with hg | hg | hg
  · change Monotone (fun x => g.op.eval (g.inputs.map (fun i => read w i x)))
    rw [hg]
    exact all_mono hw g.inputs
  · change Monotone (fun x => g.op.eval (g.inputs.map (fun i => read w i x)))
    rw [hg]
    exact any_mono hw g.inputs
  · obtain ⟨b, hb⟩ := hn hg
    rw [hb]
    exact monotone_const

lemma execute_mono {R : Type} [Preorder R] (gs : List Gate) (w : List (Signal R))
    (hw : ∀ a ∈ w, Monotone a)
    (basis : ∀ g ∈ gs, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (killed : KilledNot gs w) : ∀ a ∈ execute gs w, Monotone a := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih
    · intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · exact hw a ha
      · simp only [List.mem_singleton] at ha
        rw [ha]
        apply gate_mono hw (basis g (by simp))
        exact killed [] g gs rfl
    · intro q hq
      exact basis q (by simp [hq])
    · intro pre q post he hnot
      exact killed (g :: pre) q post (by simp [he]) hnot

lemma read_apply {R} (w : List (Signal R)) (i : Nat) (x : R) :
    read w i x = (w.map (fun a => a x)).getD i false := by
  simp only [read, List.getD, List.getElem?_map]
  cases w[i]? <;> rfl

lemma execute_apply {R} (gs : List Gate) (w : List (Signal R)) (x : R) :
    (execute gs w).map (fun a => a x) =
      gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map (fun i => v.getD i false))])
        (w.map (fun a => a x)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [execute, List.foldl_cons, ih, List.map_append, List.map_singleton]
    congr 1
    congr 1
    simp only [gateSignal, read_apply]

lemma circuit_mono {R : Type} [Preorder R] (C : Circuit) (w : List (Signal R))
    (hw : ∀ a ∈ w, Monotone a)
    (basis : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or ∨ g.op = .not)
    (killed : KilledNot C.gates w) :
    Monotone (fun x => C.eval (w.map (fun a => a x))) := by
  have hm := read_mono (execute_mono C.gates w hw basis killed) C.output
  intro x y hxy
  simpa only [read_apply, execute_apply, Circuit.eval, Circuit.wires] using hm hxy


lemma mixed_monotone {R : Type} [Preorder R] [OrderTop R] (a b : Signal R)
    (hb : Monotone b) (hm : Monotone (fun x => a x && !(b x))) :
    b = (fun _ => false) ∨ (fun x => a x && !(b x)) = (fun _ => false) := by
  cases htop : b ⊤ with
  | false =>
    apply Or.inl
    funext x
    apply Bool.eq_false_of_le_false
    simpa only [htop] using hb (show x ≤ ⊤ from le_top)
  | true =>
    apply Or.inr
    funext x
    apply Bool.eq_false_of_le_false
    simpa only [htop, Bool.not_true, Bool.and_false] using hm (show x ≤ ⊤ from le_top)

lemma execute_append {R} (a b : List Gate) (w : List (Signal R)) :
    execute (a ++ b) w = execute b (execute a w) := by
  induction a generalizing w with
  | nil => rfl
  | cons g a ih => exact ih _

lemma execute_mono_binary {R : Type} [Preorder R] (gs : List Gate) (w : List (Signal R))
    (hw : ∀ a ∈ w, Monotone a)
    (basis : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    ∀ a ∈ execute gs w, Monotone a := by
  apply execute_mono gs w hw
  · intro g hg
    exact (basis g hg).imp_right Or.inl
  · intro pre g post he hnot
    have hm : g ∈ gs := by rw [he]; simp
    rcases basis g hm with h | h <;> simp_all

lemma one_killed_not_mono {R : Type} [Preorder R]
    (before after : List Gate) (w : List (Signal R)) (i : Nat)
    (hw : ∀ a ∈ w, Monotone a)
    (preBasis : ∀ g ∈ before, g.op = .and ∨ g.op = .or)
    (postBasis : ∀ g ∈ after, g.op = .and ∨ g.op = .or)
    (sourceZero : read (execute before w) i = fun _ => false) :
    ∀ a ∈ execute (before ++ { op := .not, inputs := [i] } :: after) w, Monotone a := by
  rw [execute_append]
  change ∀ a ∈ execute after (execute before w ++
    [gateSignal (execute before w) { op := .not, inputs := [i] }]), Monotone a
  apply execute_mono_binary after _ _ postBasis
  intro a ha
  rcases List.mem_append.mp ha with ha | ha
  · exact execute_mono_binary before w hw preBasis a ha
  · simp only [List.mem_singleton] at ha
    rw [ha]
    change Monotone (fun x => !(read (execute before w) i x))
    rw [sourceZero]
    exact monotone_const

end PEqualNP.Outside.L_meta_2592.Restriction
