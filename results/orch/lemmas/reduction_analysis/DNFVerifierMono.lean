import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650_aux.DNF

open PEqualNP.CircuitLowerBounds

abbrev Monomial := List ℕ
abbrev Form := List Monomial

def evalMonomial (m : Monomial) (x : List Bool) : Bool :=
  m.all (fun i => x.getD i false)

def eval (D : Form) (x : List Bool) : Bool :=
  D.any (fun m => evalMonomial m x)

def subsetCheck (a b : Monomial) : Bool := a.all (fun i => b.contains i)

def coverCheck (R N : Form) : Bool :=
  R.all (fun r => N.any (fun n => subsetCheck n r))

def normalizeCheck (R N : Form) : Bool := coverCheck R N && coverCheck N R

lemma subsetCheck_sound (a b : Monomial) (h : subsetCheck a b = true) :
    ∀ i ∈ a, i ∈ b := by
  intro i hi
  have hm := List.all_eq_true.mp h i hi
  simpa using hm

lemma evalMonomial_subset (a b : Monomial) (x : List Bool)
    (h : subsetCheck a b = true) (hb : evalMonomial b x = true) :
    evalMonomial a x = true := by
  apply List.all_eq_true.mpr
  intro i hi
  exact List.all_eq_true.mp hb i (subsetCheck_sound a b h i hi)

lemma coverCheck_sound (R N : Form) (x : List Bool) (h : coverCheck R N = true)
    (hR : eval R x = true) : eval N x = true := by
  obtain ⟨r, hr, hv⟩ := List.any_eq_true.mp hR
  obtain ⟨n, hn, hs⟩ := List.any_eq_true.mp (List.all_eq_true.mp h r hr)
  exact List.any_eq_true.mpr ⟨n, hn, evalMonomial_subset n r x hs hv⟩

theorem normalizeCheck_sound (R N : Form) (x : List Bool)
    (h : normalizeCheck R N = true) : eval R x = eval N x := by
  have hh : coverCheck R N = true ∧ coverCheck N R = true := by
    simpa [normalizeCheck] using h
  obtain ⟨hRN, hNR⟩ := hh
  apply Bool.eq_iff_iff.mpr
  exact ⟨coverCheck_sound R N x hRN, coverCheck_sound N R x hNR⟩

def product (A B : Form) : Form := A.flatMap (fun a => B.map (fun b => a ++ b))

lemma evalMonomial_append (a b : Monomial) (x : List Bool) :
    evalMonomial (a ++ b) x = (evalMonomial a x && evalMonomial b x) := by
  simp [evalMonomial]

lemma eval_append (A B : Form) (x : List Bool) :
    eval (A ++ B) x = (eval A x || eval B x) := by
  simp [eval]

lemma eval_product (A B : Form) (x : List Bool) :
    eval (product A B) x = (eval A x && eval B x) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro h
    obtain ⟨m, hm, hv⟩ := List.any_eq_true.mp h
    obtain ⟨a, ha, hmB⟩ := List.mem_flatMap.mp hm
    obtain ⟨b, hb, rfl⟩ := List.mem_map.mp hmB
    rw [evalMonomial_append] at hv
    have hh : evalMonomial a x = true ∧ evalMonomial b x = true := by simpa using hv
    obtain ⟨hva, hvb⟩ := hh
    have hA : eval A x = true := List.any_eq_true.mpr ⟨a, ha, hva⟩
    have hB : eval B x = true := List.any_eq_true.mpr ⟨b, hb, hvb⟩
    simp [hA, hB]
  · intro h
    have hh : eval A x = true ∧ eval B x = true := by simpa using h
    obtain ⟨hA, hB⟩ := hh
    obtain ⟨a, ha, hva⟩ := List.any_eq_true.mp hA
    obtain ⟨b, hb, hvb⟩ := List.any_eq_true.mp hB
    apply List.any_eq_true.mpr
    refine ⟨a ++ b, List.mem_flatMap.mpr ⟨a, ha, List.mem_map.mpr ⟨b, hb, rfl⟩⟩, ?_⟩
    rw [evalMonomial_append, hva, hvb]
    rfl

def rawGate (env : List Form) (g : Gate) : Option Form :=
  match g.op, g.inputs with
  | .and, [a, b] => some (product (env.getD a []) (env.getD b []))
  | .or, [a, b] => some (env.getD a [] ++ env.getD b [])
  | _, _ => none

lemma rawGate_sound (env : List Form) (w x : List Bool) (g : Gate) (R : Form)
    (rel : ∀ i, eval (env.getD i []) x = w.getD i false)
    (h : rawGate env g = some R) :
    eval R x = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [List.getD_eq_getElem?_getD] at rel
  rcases g with ⟨op, ins⟩
  cases ins with
  | nil => cases op <;> simp [rawGate] at h
  | cons a ins =>
    cases ins with
    | nil => cases op <;> simp [rawGate] at h
    | cons b ins =>
      cases ins with
      | nil =>
        cases op <;> simp [rawGate] at h
        · subst R
          rw [eval_product, rel, rel]
          simp [GateOp.eval, List.getD_eq_getElem?_getD]
        · subst R
          rw [eval_append, rel, rel]
          simp [GateOp.eval, List.getD_eq_getElem?_getD]
      | cons c ins => cases op <;> simp [rawGate] at h

def initial (n : ℕ) : List Form := (List.range n).map (fun i => [[i]])

def checkGates : List Form → List Gate → List Form → Bool
  | _, [], [] => true
  | env, g :: gs, N :: Ns =>
    match rawGate env g with
    | none => false
    | some R => normalizeCheck R N && checkGates (env ++ [N]) gs Ns
  | _, _, _ => false

def checkCircuit (n : ℕ) (C : Circuit) (cert : List Form) : Bool :=
  checkGates (initial n) C.gates cert

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma getD_snoc {α : Type*} (w : List α) (v d : α) (i : ℕ) :
    (w ++ [v]).getD i d = if i = w.length then v else w.getD i d := by
  induction w generalizing i with
  | nil => cases i <;> rfl
  | cons a w ih =>
    cases i with
    | zero => rfl
    | succ i => simpa using ih i

lemma initial_length (n : ℕ) : (initial n).length = n := by simp [initial]

lemma initial_sound (n : ℕ) (x : List Bool) (hlen : x.length = n) (i : ℕ) :
    eval ((initial n).getD i []) x = x.getD i false := by
  by_cases hi : i < n
  · simp [initial, List.getD_eq_getElem?_getD, hi, eval, evalMonomial]
  · simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by rw [initial_length]; omega),
      List.getElem?_eq_none (by rw [hlen]; omega)]
    rfl

theorem checkGates_sound (env : List Form) (gs : List Gate) (cert : List Form)
    (w x : List Bool) (checked : checkGates env gs cert = true)
    (hlen : env.length = w.length)
    (rel : ∀ i, eval (env.getD i []) x = w.getD i false) :
    ∀ i, eval ((env ++ cert).getD i []) x = (run gs w).getD i false := by
  induction gs generalizing env cert w with
  | nil =>
    cases cert with
    | nil => simpa [run] using rel
    | cons N Ns => simp [checkGates] at checked
  | cons g gs ih =>
    cases cert with
    | nil => simp [checkGates] at checked
    | cons N Ns =>
      cases hr : rawGate env g with
      | none => simp [checkGates, hr] at checked
      | some R =>
        have hs : normalizeCheck R N = true ∧ checkGates (env ++ [N]) gs Ns = true := by
          simpa [checkGates, hr] using checked
        let v := g.op.eval (g.inputs.map fun i => w.getD i false)
        have hv : eval N x = v :=
          (normalizeCheck_sound R N x hs.1).symm.trans (rawGate_sound env w x g R rel hr)
        have next : ∀ i, eval ((env ++ [N]).getD i []) x = (w ++ [v]).getD i false := by
          intro i
          simp only [getD_snoc, hlen]
          by_cases hi : i = w.length
          · simp [hi, hv]
          · simp only [if_neg hi]
            exact rel i
        have result := ih (env ++ [N]) Ns (w ++ [v]) hs.2 (by simp [hlen]) next
        simpa only [List.append_assoc, List.singleton_append, run, List.foldl_cons] using result

theorem checkCircuit_sound (n : ℕ) (C : Circuit) (cert : List Form)
    (checked : checkCircuit n C cert = true) (x : List Bool) (hlen : x.length = n) :
    ∀ i, (C.wires x).getD i false = eval ((initial n ++ cert).getD i []) x := by
  intro i
  exact (checkGates_sound (initial n) C.gates cert x x checked
    (by rw [initial_length, hlen]) (initial_sound n x hlen) i).symm

theorem checkCircuit_eval (n : ℕ) (C : Circuit) (cert : List Form)
    (checked : checkCircuit n C cert = true) (x : List Bool) (hlen : x.length = n) :
    C.eval x = eval ((initial n ++ cert).getD C.output []) x :=
  checkCircuit_sound n C cert checked x hlen C.output

lemma rawGate_monotone (env : List Form) (g : Gate) (R : Form)
    (h : rawGate env g = some R) :
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  rcases g with ⟨op, ins⟩
  cases ins with
  | nil => cases op <;> simp [rawGate] at h
  | cons a ins =>
    cases ins with
    | nil => cases op <;> simp [rawGate] at h
    | cons b ins =>
      cases ins with
      | nil => cases op <;> simp_all [rawGate]
      | cons c ins => cases op <;> simp [rawGate] at h

theorem checkGates_monotone (env : List Form) (gs : List Gate) (cert : List Form)
    (checked : checkGates env gs cert = true) :
    ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing env cert with
  | nil => simp
  | cons g gs ih =>
    cases cert with
    | nil => simp [checkGates] at checked
    | cons N Ns =>
      cases hr : rawGate env g with
      | none => simp [checkGates, hr] at checked
      | some R =>
        have hs : normalizeCheck R N = true ∧ checkGates (env ++ [N]) gs Ns = true := by
          simpa [checkGates, hr] using checked
        intro a ha
        rcases List.mem_cons.mp ha with rfl | ha
        · exact rawGate_monotone env a R hr
        · exact ih (env ++ [N]) Ns hs.2 a ha

theorem checkCircuit_monotone (n : ℕ) (C : Circuit) (cert : List Form)
    (checked : checkCircuit n C cert = true) : PEqualNP.MetaComplexity.Monotone2 C :=
  checkGates_monotone (initial n) C.gates cert checked

end PEqualNP.Outside.L_meta_650_aux.DNF

