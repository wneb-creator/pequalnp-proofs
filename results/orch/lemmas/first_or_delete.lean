import Mathlib.Data.List.GetD

namespace PEqualNP.Outside.L_meta_1031_aux.FirstOrDeletion

def meet (values : List Bool) (atoms : List Nat) : Bool :=
  atoms.all (fun i => values.getD i false)

def step (values : List Bool) (g : List Nat × List Nat) : List Bool :=
  values ++ [meet values g.1 || meet values g.2]

def wires (program : List (List Nat × List Nat)) (values : List Bool) : List Bool :=
  program.foldl step values

def eval (program : List (List Nat × List Nat)) (output : List Nat) (x : List Bool) : Bool :=
  meet (wires program x) output

def bounded (n : Nat) (atoms : List Nat) : Prop := ∀ i ∈ atoms, i < n

def atom (n : Nat) (replacement : List Nat) (i : Nat) : List Nat :=
  if i < n then [i] else if i = n then replacement else [i - 1]

def rewrite (n : Nat) (replacement atoms : List Nat) : List Nat :=
  atoms.flatMap (atom n replacement)

def rewriteGate (n : Nat) (replacement : List Nat) (g : List Nat × List Nat) : List Nat × List Nat :=
  (rewrite n replacement g.1, rewrite n replacement g.2)

def Rel (n : Nat) (replacement : List Nat) (old fresh : List Bool) : Prop :=
  ∀ i, old.getD i false = meet fresh (atom n replacement i)

theorem meet_append (values : List Bool) (a b : List Nat) :
    meet values (a ++ b) = (meet values a && meet values b) := by
  simp [meet]

theorem meet_singleton (values : List Bool) (i : Nat) :
    meet values [i] = values.getD i false := by simp [meet]

theorem meet_extend (values suffix : List Bool) (atoms : List Nat)
    (h : bounded values.length atoms) : meet (values ++ suffix) atoms = meet values atoms := by
  induction atoms with
  | nil => rfl
  | cons i atoms ih =>
    have hi := h i (by simp)
    have ht : bounded values.length atoms := fun j hj => h j (by simp [hj])
    change ((values ++ suffix).getD i false && meet (values ++ suffix) atoms) =
      (values.getD i false && meet values atoms)
    rw [List.getD_append values suffix false i hi, ih ht]

theorem getD_append_one (values : List Bool) (v : Bool) (i : Nat) :
    (values ++ [v]).getD i false =
      if i < values.length then values.getD i false else if i = values.length then v else false := by
  by_cases hi : i < values.length
  · simp only [hi, ite_true]
    exact List.getD_append values [v] false i hi
  · by_cases he : i = values.length
    · subst i
      simp [List.getD_eq_getElem?_getD]
    · simp only [hi, he, ite_false]
      apply List.getD_eq_default
      simp only [List.length_append, List.length_singleton]
      omega

theorem rel_initial (n : Nat) (replacement : List Nat) (x : List Bool) (hx : x.length = n) :
    Rel n replacement (x ++ [meet x replacement]) x := by
  intro i
  rw [getD_append_one, hx]
  by_cases hi : i < n
  · simp [atom, hi, meet_singleton]
  · by_cases he : i = n
    · simp [atom, he]
    · simp only [atom, hi, he, ite_false, meet_singleton]
      symm
      apply List.getD_eq_default
      omega

theorem meet_rewrite {n : Nat} {replacement : List Nat} {old fresh : List Bool}
    (hr : Rel n replacement old fresh) (atoms : List Nat) :
    meet fresh (rewrite n replacement atoms) = meet old atoms := by
  induction atoms with
  | nil => rfl
  | cons i atoms ih =>
    change meet fresh (atom n replacement i ++ rewrite n replacement atoms) =
      (old.getD i false && meet old atoms)
    rw [meet_append, ← hr i, ih]

theorem rel_append {n : Nat} {replacement : List Nat} {old fresh : List Bool}
    (hr : Rel n replacement old fresh) (hlen : old.length = fresh.length + 1)
    (hn : n ≤ fresh.length) (hb : bounded n replacement) (v : Bool) :
    Rel n replacement (old ++ [v]) (fresh ++ [v]) := by
  intro i
  by_cases hi : i < n
  · have hio : i < old.length := by omega
    have hif : i < fresh.length := by omega
    simp only [atom, hi, ite_true, meet_singleton]
    rw [List.getD_append old [v] false i hio, List.getD_append fresh [v] false i hif]
    simpa only [atom, hi, ite_true, meet_singleton] using hr i
  · by_cases he : i = n
    · subst i
      have hno : n < old.length := by omega
      have hbf : bounded fresh.length replacement := fun j hj => Nat.lt_of_lt_of_le (hb j hj) hn
      simp only [atom, Nat.lt_irrefl, ite_false, ite_true]
      rw [List.getD_append old [v] false n hno, meet_extend fresh [v] replacement hbf]
      simpa only [atom, Nat.lt_irrefl, ite_false, ite_true] using hr n
    · simp only [atom, hi, he, ite_false, meet_singleton]
      rw [getD_append_one, getD_append_one]
      by_cases hio : i < old.length
      · have hif : i - 1 < fresh.length := by omega
        simp only [hio, hif, ite_true]
        simpa only [atom, hi, he, ite_false, meet_singleton] using hr i
      · by_cases hioeq : i = old.length
        · subst i
          have hifeq : old.length - 1 = fresh.length := by omega
          simp [hifeq]
        · have hif : ¬ i - 1 < fresh.length := by omega
          have hifeq : i - 1 ≠ fresh.length := by omega
          simp [hio, hioeq, hif, hifeq]

theorem wires_length (program : List (List Nat × List Nat)) (values : List Bool) :
    (wires program values).length = values.length + program.length := by
  induction program generalizing values with
  | nil => simp [wires]
  | cons g gs ih =>
    change (wires gs (step values g)).length = _
    rw [ih]
    simp [step]
    omega

theorem rel_wires {n : Nat} {replacement : List Nat} (program : List (List Nat × List Nat))
    (old fresh : List Bool) (hr : Rel n replacement old fresh)
    (hlen : old.length = fresh.length + 1) (hn : n ≤ fresh.length)
    (hb : bounded n replacement) :
    Rel n replacement (wires program old)
      (wires (program.map (rewriteGate n replacement)) fresh) := by
  induction program generalizing old fresh with
  | nil => exact hr
  | cons g gs ih =>
    change Rel n replacement (wires gs (step old g))
      (wires (gs.map (rewriteGate n replacement)) (step fresh (rewriteGate n replacement g)))
    have hstep : step fresh (rewriteGate n replacement g) =
        fresh ++ [meet old g.1 || meet old g.2] := by
      simp only [step, rewriteGate, meet_rewrite hr]
    rw [hstep]
    apply ih
    · exact rel_append hr hlen hn hb _
    · simp [step, hlen]
    · simp only [List.length_append, List.length_singleton]
      omega

theorem delete_first_eval (n : Nat) (b output : List Nat)
    (program : List (List Nat × List Nat)) (x : List Bool) (hx : x.length = n)
    (hb : bounded n b) :
    eval (program.map (rewriteGate n b)) (rewrite n b output) x =
      meet (wires program (x ++ [meet x b])) output := by
  apply meet_rewrite
  apply rel_wires program (x ++ [meet x b]) x (rel_initial n b x hx)
  · simp
  · omega
  · exact hb

theorem meet_mono {a b : List Bool} (h : ∀ i, a.getD i false = true → b.getD i false = true)
    (atoms : List Nat) : meet a atoms = true → meet b atoms = true := by
  simp only [meet, List.all_eq_true]
  intro ha i hi
  exact h i (ha i hi)

theorem append_mono {a b : List Bool} (hlen : a.length = b.length)
    (h : ∀ i, a.getD i false = true → b.getD i false = true)
    {u v : Bool} (huv : u = true → v = true) :
    ∀ i, (a ++ [u]).getD i false = true → (b ++ [v]).getD i false = true := by
  intro i
  rw [getD_append_one, getD_append_one, ← hlen]
  by_cases hi : i < a.length
  · simpa only [hi, ite_true] using h i
  · by_cases he : i = a.length
    · subst i
      simpa using huv
    · simp [hi, he]

theorem wires_mono (program : List (List Nat × List Nat)) (a b : List Bool)
    (hlen : a.length = b.length)
    (h : ∀ i, a.getD i false = true → b.getD i false = true) :
    ∀ i, (wires program a).getD i false = true → (wires program b).getD i false = true := by
  induction program generalizing a b with
  | nil => exact h
  | cons g gs ih =>
    change ∀ i, (wires gs (step a g)).getD i false = true →
      (wires gs (step b g)).getD i false = true
    apply ih
    · simp [step, hlen]
    · apply append_mono hlen h
      simp only [Bool.or_eq_true]
      intro hg
      exact hg.imp (meet_mono h g.1) (meet_mono h g.2)

theorem delete_first_below (n : Nat) (a b output : List Nat)
    (program : List (List Nat × List Nat)) (x : List Bool) (hx : x.length = n)
    (hb : bounded n b) :
    eval (program.map (rewriteGate n b)) (rewrite n b output) x = true →
      eval ((a,b) :: program) output x = true := by
  rw [delete_first_eval n b output program x hx hb]
  change meet (wires program (x ++ [meet x b])) output = true →
    meet (wires program (x ++ [meet x a || meet x b])) output = true
  apply meet_mono
  apply wires_mono program _ _ (by simp)
  apply append_mono rfl (fun _ h => h)
  intro h
  simp [h]

theorem delete_first_agrees (n : Nat) (a b output : List Nat)
    (program : List (List Nat × List Nat)) (x : List Bool) (hx : x.length = n)
    (hb : bounded n b) (ha : meet x a = false) :
    eval (program.map (rewriteGate n b)) (rewrite n b output) x =
      eval ((a,b) :: program) output x := by
  rw [delete_first_eval n b output program x hx hb]
  change meet (wires program (x ++ [meet x b])) output =
    meet (wires program (x ++ [meet x a || meet x b])) output
  simp [ha]

theorem rewrite_bounded {n k : Nat} {replacement atoms : List Nat}
    (hb : bounded n replacement) (ha : bounded (n + 1 + k) atoms) :
    bounded (n + k) (rewrite n replacement atoms) := by
  intro i hi
  obtain ⟨j, hj, hij⟩ := List.mem_flatMap.mp hi
  have hjb := ha j hj
  by_cases hjn : j < n
  · have heq : i = j := by simpa [atom, hjn] using hij
    omega
  · by_cases he : j = n
    · have hbmem : i ∈ replacement := by simpa [atom, hjn, he] using hij
      have := hb i hbmem
      omega
    · have heq : i = j - 1 := by simpa [atom, hjn, he] using hij
      omega

theorem rewrite_length (n : Nat) (replacement : List Nat) (program : List (List Nat × List Nat)) :
    (program.map (rewriteGate n replacement)).length = program.length := by simp

def wellFormed (n : Nat) (program : List (List Nat × List Nat)) : Prop :=
  ∀ j < program.length,
    bounded (n + j) (program.getD j ([], [])).1 ∧
    bounded (n + j) (program.getD j ([], [])).2

theorem rewrite_wellFormed {n : Nat} {replacement : List Nat}
    (program : List (List Nat × List Nat)) (hb : bounded n replacement)
    (hwf : wellFormed (n + 1) program) :
    wellFormed n (program.map (rewriteGate n replacement)) := by
  intro j hj
  have hjold : j < program.length := by simpa using hj
  obtain ⟨ha, hc⟩ := hwf j hjold
  have hget : (program.map (rewriteGate n replacement)).getD j ([], []) =
      rewriteGate n replacement (program.getD j ([], [])) := by
    simpa [rewriteGate, rewrite] using
      List.getD_map program ([], []) (n := j) (rewriteGate n replacement)
  rw [hget]
  exact ⟨rewrite_bounded hb ha, rewrite_bounded hb hc⟩

theorem deleted_positive_requires_branch (n : Nat) (a b output : List Nat)
    (program : List (List Nat × List Nat)) (x : List Bool) (hx : x.length = n)
    (hb : bounded n b)
    (hold : eval ((a,b) :: program) output x = true)
    (hnew : eval (program.map (rewriteGate n b)) (rewrite n b output) x = false) :
    meet x a = true := by
  cases ha : meet x a with
  | true => rfl
  | false =>
    have h := delete_first_agrees n a b output program x hx hb ha
    rw [hold, hnew] at h
    exact Bool.noConfusion h

def pairInput {n : Nat} (u v : Fin n) : List Bool :=
  List.ofFn (fun w : Fin n => decide (w = u ∨ w = v))

theorem branch_pair_unique {n : Nat} (a : List Nat) (i j u v : Fin n)
    (hi : i.val ∈ a) (hj : j.val ∈ a) (hne : i ≠ j)
    (ha : meet (pairInput u v) a = true) :
    (u = i ∧ v = j) ∨ (u = j ∧ v = i) := by
  have hival := List.all_eq_true.mp ha i.val hi
  have hjval := List.all_eq_true.mp ha j.val hj
  have hipair : i = u ∨ i = v := by
    simpa [pairInput, List.getD_eq_getElem?_getD] using hival
  have hjpair : j = u ∨ j = v := by
    simpa [pairInput, List.getD_eq_getElem?_getD] using hjval
  rcases hipair with hiu | hiv <;> rcases hjpair with hju | hjv
  · exact False.elim (hne (hiu.trans hju.symm))
  · exact Or.inl ⟨hiu.symm, hjv.symm⟩
  · exact Or.inr ⟨hju.symm, hiv.symm⟩
  · exact False.elim (hne (hiv.trans hjv.symm))

theorem lost_pair_unique (n : Nat) (a b output : List Nat)
    (program : List (List Nat × List Nat)) (hb : bounded n b)
    (i j : Fin n) (hi : i.val ∈ a) (hj : j.val ∈ a) (hne : i ≠ j)
    (u v : Fin n)
    (hold : eval ((a,b) :: program) output (pairInput u v) = true)
    (hnew : eval (program.map (rewriteGate n b)) (rewrite n b output) (pairInput u v) = false) :
    (u = i ∧ v = j) ∨ (u = j ∧ v = i) := by
  exact branch_pair_unique a i j u v hi hj hne
    (deleted_positive_requires_branch n a b output program (pairInput u v)
      (by simp [pairInput]) hb hold hnew)

end PEqualNP.Outside.L_meta_1031_aux.FirstOrDeletion
