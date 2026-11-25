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


namespace PEqualNP.Outside.L_meta_650_aux.Submission

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_650_aux.DNF

def circuit : Circuit :=
  ⟨[
    ⟨GateOp.or, [13, 14]⟩,
    ⟨GateOp.or, [26, 16]⟩,
    ⟨GateOp.or, [27, 22]⟩,
    ⟨GateOp.and, [0, 28]⟩,
    ⟨GateOp.or, [13, 15]⟩,
    ⟨GateOp.or, [30, 21]⟩,
    ⟨GateOp.or, [31, 25]⟩,
    ⟨GateOp.and, [1, 32]⟩,
    ⟨GateOp.or, [14, 20]⟩,
    ⟨GateOp.or, [34, 24]⟩,
    ⟨GateOp.or, [35, 25]⟩,
    ⟨GateOp.and, [2, 36]⟩,
    ⟨GateOp.or, [13, 19]⟩,
    ⟨GateOp.or, [38, 23]⟩,
    ⟨GateOp.or, [39, 24]⟩,
    ⟨GateOp.and, [3, 40]⟩,
    ⟨GateOp.or, [18, 22]⟩,
    ⟨GateOp.or, [42, 23]⟩,
    ⟨GateOp.or, [43, 25]⟩,
    ⟨GateOp.and, [4, 44]⟩,
    ⟨GateOp.or, [17, 21]⟩,
    ⟨GateOp.or, [46, 22]⟩,
    ⟨GateOp.or, [47, 24]⟩,
    ⟨GateOp.and, [5, 48]⟩,
    ⟨GateOp.or, [16, 20]⟩,
    ⟨GateOp.or, [50, 21]⟩,
    ⟨GateOp.or, [51, 23]⟩,
    ⟨GateOp.and, [6, 52]⟩,
    ⟨GateOp.or, [15, 19]⟩,
    ⟨GateOp.or, [54, 20]⟩,
    ⟨GateOp.or, [55, 22]⟩,
    ⟨GateOp.and, [7, 56]⟩,
    ⟨GateOp.or, [14, 18]⟩,
    ⟨GateOp.or, [58, 19]⟩,
    ⟨GateOp.or, [59, 21]⟩,
    ⟨GateOp.and, [8, 60]⟩,
    ⟨GateOp.or, [13, 17]⟩,
    ⟨GateOp.or, [62, 18]⟩,
    ⟨GateOp.or, [63, 20]⟩,
    ⟨GateOp.and, [9, 64]⟩,
    ⟨GateOp.or, [16, 17]⟩,
    ⟨GateOp.or, [66, 19]⟩,
    ⟨GateOp.or, [67, 25]⟩,
    ⟨GateOp.and, [10, 68]⟩,
    ⟨GateOp.or, [15, 16]⟩,
    ⟨GateOp.or, [70, 18]⟩,
    ⟨GateOp.or, [71, 24]⟩,
    ⟨GateOp.and, [11, 72]⟩,
    ⟨GateOp.or, [14, 15]⟩,
    ⟨GateOp.or, [74, 17]⟩,
    ⟨GateOp.or, [75, 23]⟩,
    ⟨GateOp.and, [12, 76]⟩,
    ⟨GateOp.or, [29, 33]⟩,
    ⟨GateOp.or, [78, 37]⟩,
    ⟨GateOp.or, [79, 41]⟩,
    ⟨GateOp.or, [80, 45]⟩,
    ⟨GateOp.or, [81, 49]⟩,
    ⟨GateOp.or, [82, 53]⟩,
    ⟨GateOp.or, [83, 57]⟩,
    ⟨GateOp.or, [84, 61]⟩,
    ⟨GateOp.or, [85, 65]⟩,
    ⟨GateOp.or, [86, 69]⟩,
    ⟨GateOp.or, [87, 73]⟩,
    ⟨GateOp.or, [88, 77]⟩
  ], 89⟩

def certificate : List Form :=
  [[[13],[14]],[[13],[14],[16]],[[13],[14],[16],[22]],[[0,13],[0,14],[0,16],[0,22]],[[13],[15]],[[13],[15],[21]],[[13],[15],[21],[25]],[[1,13],[1,15],[1,21],[1,25]],[[14],[20]],[[14],[20],[24]],[[14],[20],[24],[25]],[[2,14],[2,20],[2,24],[2,25]],[[13],[19]],[[13],[19],[23]],[[13],[19],[23],[24]],[[3,13],[3,19],[3,23],[3,24]],[[18],[22]],[[18],[22],[23]],[[18],[22],[23],[25]],[[4,18],[4,22],[4,23],[4,25]],[[17],[21]],[[17],[21],[22]],[[17],[21],[22],[24]],[[5,17],[5,21],[5,22],[5,24]],[[16],[20]],[[16],[20],[21]],[[16],[20],[21],[23]],[[6,16],[6,20],[6,21],[6,23]],[[15],[19]],[[15],[19],[20]],[[15],[19],[20],[22]],[[7,15],[7,19],[7,20],[7,22]],[[14],[18]],[[14],[18],[19]],[[14],[18],[19],[21]],[[8,14],[8,18],[8,19],[8,21]],[[13],[17]],[[13],[17],[18]],[[13],[17],[18],[20]],[[9,13],[9,17],[9,18],[9,20]],[[16],[17]],[[16],[17],[19]],[[16],[17],[19],[25]],[[10,16],[10,17],[10,19],[10,25]],[[15],[16]],[[15],[16],[18]],[[15],[16],[18],[24]],[[11,15],[11,16],[11,18],[11,24]],[[14],[15]],[[14],[15],[17]],[[14],[15],[17],[23]],[[12,14],[12,15],[12,17],[12,23]],[[0,13],[0,14],[0,16],[0,22],[1,13],[1,15],[1,21],[1,25]],[[0,13],[0,14],[0,16],[0,22],[1,13],[1,15],[1,21],[1,25],[2,14],[2,20],[2,24],[2,25]],[[0,13],[0,14],[0,16],[0,22],[1,13],[1,15],[1,21],[1,25],[2,14],[2,20],[2,24],[2,25],[3,13],[3,19],[3,23],[3,24]],[[0,13],[0,14],[0,16],[0,22],[1,13],[1,15],[1,21],[1,25],[2,14],[2,20],[2,24],[2,25],[3,13],[3,19],[3,23],[3,24],[4,18],[4,22],[4,23],[4,25]],[[0,13],[0,14],[0,16],[0,22],[1,13],[1,15],[1,21],[1,25],[2,14],[2,20],[2,24],[2,25],[3,13],[3,19],[3,23],[3,24],[4,18],[4,22],[4,23],[4,25],[5,17],[5,21],[5,22],[5,24]],[[0,13],[0,14],[0,16],[0,22],[1,13],[1,15],[1,21],[1,25],[2,14],[2,20],[2,24],[2,25],[3,13],[3,19],[3,23],[3,24],[4,18],[4,22],[4,23],[4,25],[5,17],[5,21],[5,22],[5,24],[6,16],[6,20],[6,21],[6,23]],[[0,13],[0,14],[0,16],[0,22],[1,13],[1,15],[1,21],[1,25],[2,14],[2,20],[2,24],[2,25],[3,13],[3,19],[3,23],[3,24],[4,18],[4,22],[4,23],[4,25],[5,17],[5,21],[5,22],[5,24],[6,16],[6,20],[6,21],[6,23],[7,15],[7,19],[7,20],[7,22]],[[0,13],[0,14],[0,16],[0,22],[1,13],[1,15],[1,21],[1,25],[2,14],[2,20],[2,24],[2,25],[3,13],[3,19],[3,23],[3,24],[4,18],[4,22],[4,23],[4,25],[5,17],[5,21],[5,22],[5,24],[6,16],[6,20],[6,21],[6,23],[7,15],[7,19],[7,20],[7,22],[8,14],[8,18],[8,19],[8,21]],[[0,13],[0,14],[0,16],[0,22],[1,13],[1,15],[1,21],[1,25],[2,14],[2,20],[2,24],[2,25],[3,13],[3,19],[3,23],[3,24],[4,18],[4,22],[4,23],[4,25],[5,17],[5,21],[5,22],[5,24],[6,16],[6,20],[6,21],[6,23],[7,15],[7,19],[7,20],[7,22],[8,14],[8,18],[8,19],[8,21],[9,13],[9,17],[9,18],[9,20]],[[0,13],[0,14],[0,16],[0,22],[1,13],[1,15],[1,21],[1,25],[2,14],[2,20],[2,24],[2,25],[3,13],[3,19],[3,23],[3,24],[4,18],[4,22],[4,23],[4,25],[5,17],[5,21],[5,22],[5,24],[6,16],[6,20],[6,21],[6,23],[7,15],[7,19],[7,20],[7,22],[8,14],[8,18],[8,19],[8,21],[9,13],[9,17],[9,18],[9,20],[10,16],[10,17],[10,19],[10,25]],[[0,13],[0,14],[0,16],[0,22],[1,13],[1,15],[1,21],[1,25],[2,14],[2,20],[2,24],[2,25],[3,13],[3,19],[3,23],[3,24],[4,18],[4,22],[4,23],[4,25],[5,17],[5,21],[5,22],[5,24],[6,16],[6,20],[6,21],[6,23],[7,15],[7,19],[7,20],[7,22],[8,14],[8,18],[8,19],[8,21],[9,13],[9,17],[9,18],[9,20],[10,16],[10,17],[10,19],[10,25],[11,15],[11,16],[11,18],[11,24]],[[0,13],[0,14],[0,16],[0,22],[1,13],[1,15],[1,21],[1,25],[2,14],[2,20],[2,24],[2,25],[3,13],[3,19],[3,23],[3,24],[4,18],[4,22],[4,23],[4,25],[5,17],[5,21],[5,22],[5,24],[6,16],[6,20],[6,21],[6,23],[7,15],[7,19],[7,20],[7,22],[8,14],[8,18],[8,19],[8,21],[9,13],[9,17],[9,18],[9,20],[10,16],[10,17],[10,19],[10,25],[11,15],[11,16],[11,18],[11,24],[12,14],[12,15],[12,17],[12,23]]]

def outputTerms : Form :=
  [[0,13],[0,14],[0,16],[0,22],[1,13],[1,15],[1,21],[1,25],[2,14],[2,20],[2,24],[2,25],[3,13],[3,19],[3,23],[3,24],[4,18],[4,22],[4,23],[4,25],[5,17],[5,21],[5,22],[5,24],[6,16],[6,20],[6,21],[6,23],[7,15],[7,19],[7,20],[7,22],[8,14],[8,18],[8,19],[8,21],[9,13],[9,17],[9,18],[9,20],[10,16],[10,17],[10,19],[10,25],[11,15],[11,16],[11,18],[11,24],[12,14],[12,15],[12,17],[12,23]]

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem certificate_valid : checkCircuit 26 circuit certificate = true := by
  decide +kernel

theorem output_terms : (initial 26 ++ certificate).getD circuit.output [] = outputTerms := by
  rfl

end PEqualNP.Outside.L_meta_650_aux.Submission

set_option maxRecDepth 65536 in
set_option maxHeartbeats 0 in
theorem PEqualNP.Outside.L_meta_650_aux.Calibration64 : ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ 64 ∧ (∀ x : Fin 26 → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin 26, (u.val, v.val) ∈ ([(0, 13), (0, 14), (0, 16), (0, 22), (1, 13), (1, 15), (1, 21), (1, 25), (2, 14), (2, 20), (2, 24), (2, 25), (3, 13), (3, 19), (3, 23), (3, 24), (4, 18), (4, 22), (4, 23), (4, 25), (5, 17), (5, 21), (5, 22), (5, 24), (6, 16), (6, 20), (6, 21), (6, 23), (7, 15), (7, 19), (7, 20), (7, 22), (8, 14), (8, 18), (8, 19), (8, 21), (9, 13), (9, 17), (9, 18), (9, 20), (10, 16), (10, 17), (10, 19), (10, 25), (11, 15), (11, 16), (11, 18), (11, 24), (12, 14), (12, 15), (12, 17), (12, 23)] : List (ℕ × ℕ)) ∧ x u = true ∧ x v = true)) := by
  let C := PEqualNP.Outside.L_meta_650_aux.Submission.circuit
  have checked := PEqualNP.Outside.L_meta_650_aux.Submission.certificate_valid
  refine ⟨C, PEqualNP.Outside.L_meta_650_aux.DNF.checkCircuit_monotone 26 C _ checked, ?_, ?_⟩
  · decide
  · intro x
    rw [PEqualNP.Outside.L_meta_650_aux.DNF.checkCircuit_eval 26 C _ checked
      (List.ofFn x) (by simp)]
    change PEqualNP.Outside.L_meta_650_aux.DNF.eval
      ((PEqualNP.Outside.L_meta_650_aux.DNF.initial 26 ++
        PEqualNP.Outside.L_meta_650_aux.Submission.certificate).getD
        PEqualNP.Outside.L_meta_650_aux.Submission.circuit.output []) (List.ofFn x) = true ↔ _
    rw [PEqualNP.Outside.L_meta_650_aux.Submission.output_terms]
    simp [PEqualNP.Outside.L_meta_650_aux.DNF.eval,
      PEqualNP.Outside.L_meta_650_aux.DNF.evalMonomial,
      PEqualNP.Outside.L_meta_650_aux.Submission.outputTerms, List.ofFn_succ,
      Fin.exists_iff, Prod.mk.injEq, or_and_right, exists_or, and_assoc,
      and_or_left, or_assoc]
