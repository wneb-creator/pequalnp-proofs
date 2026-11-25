import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.Compiler

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    rw [run, List.foldl_cons]
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step]
    omega

lemma run_keep (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = _
    rw [ih _ (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

def rename (m n : ℕ) (pick : ℕ → ℕ) (i : ℕ) : ℕ :=
  if i < m then pick i else n + (i - m)

def renameGate (m n : ℕ) (pick : ℕ → ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (rename m n pick)⟩

lemma read_rename (x y s : List Bool) (pick : ℕ → ℕ)
    (hp : ∀ i < x.length, pick i < y.length)
    (hv : ∀ i < x.length, y.getD (pick i) false = x.getD i false) (i : ℕ) :
    (y ++ s).getD (rename x.length y.length pick i) false = (x ++ s).getD i false := by
  by_cases hi : i < x.length
  · rw [rename, ite_eq_left hi, List.getD_append _ _ _ _ (hp i hi),
      List.getD_append _ _ _ _ hi, hv i hi]
  · simp only [rename, ite_eq_right hi, List.getD_eq_getElem?_getD,
      List.getElem?_append_right (by omega : x.length ≤ i),
      List.getElem?_append_right (by omega : y.length ≤ y.length + (i - x.length)),
      Nat.add_sub_cancel_left]

lemma run_rename (gs : List Gate) (x y s : List Bool) (pick : ℕ → ℕ)
    (hp : ∀ i < x.length, pick i < y.length)
    (hv : ∀ i < x.length, y.getD (pick i) false = x.getD i false) (o : ℕ) :
    (run (gs.map (renameGate x.length y.length pick)) (y ++ s)).getD
        (rename x.length y.length pick o) false =
      (run gs (x ++ s)).getD o false := by
  induction gs generalizing s with
  | nil => exact read_rename x y s pick hp hv o
  | cons g gs ih =>
    let v := g.op.eval (g.inputs.map fun i => (x ++ s).getD i false)
    have heq : (renameGate x.length y.length pick g).op.eval
        ((renameGate x.length y.length pick g).inputs.map fun i => (y ++ s).getD i false) = v := by
      simp only [renameGate, List.map_map]
      congr 1
      exact List.map_congr_left (fun i _ => read_rename x y s pick hp hv i)
    simp only [List.map_cons, run, List.foldl_cons, step, heq]
    change (run (gs.map (renameGate x.length y.length pick)) ((y ++ s) ++ [v])).getD
      (rename x.length y.length pick o) false =
      (run gs ((x ++ s) ++ [v])).getD o false
    simpa only [List.append_assoc] using ih (s ++ [v])

lemma rename_mono (m n : ℕ) (pick : ℕ → ℕ) (B : Circuit) (hb : Monotone2 B) (o : ℕ) :
    Monotone2 ⟨B.gates.map (renameGate m n pick), o⟩ := by
  intro g hg
  change g ∈ B.gates.map (renameGate m n pick) at hg
  obtain ⟨orig, horig, heq⟩ := List.mem_map.mp hg
  subst g
  simpa only [renameGate, List.length_map] using hb orig horig

def boundary : Circuit :=
  ⟨[⟨GateOp.or, [15, 17]⟩,
    ⟨GateOp.or, [26, 18]⟩,
    ⟨GateOp.or, [27, 22]⟩,
    ⟨GateOp.and, [5, 28]⟩,
    ⟨GateOp.or, [16, 18]⟩,
    ⟨GateOp.or, [30, 19]⟩,
    ⟨GateOp.or, [31, 23]⟩,
    ⟨GateOp.and, [6, 32]⟩,
    ⟨GateOp.or, [17, 19]⟩,
    ⟨GateOp.or, [34, 20]⟩,
    ⟨GateOp.or, [35, 24]⟩,
    ⟨GateOp.and, [7, 36]⟩,
    ⟨GateOp.or, [18, 20]⟩,
    ⟨GateOp.or, [38, 21]⟩,
    ⟨GateOp.or, [39, 25]⟩,
    ⟨GateOp.and, [8, 40]⟩,
    ⟨GateOp.or, [15, 21]⟩,
    ⟨GateOp.or, [42, 23]⟩,
    ⟨GateOp.or, [43, 24]⟩,
    ⟨GateOp.and, [11, 44]⟩,
    ⟨GateOp.or, [16, 22]⟩,
    ⟨GateOp.or, [46, 24]⟩,
    ⟨GateOp.or, [47, 25]⟩,
    ⟨GateOp.and, [12, 48]⟩,
    ⟨GateOp.or, [29, 33]⟩,
    ⟨GateOp.or, [50, 37]⟩,
    ⟨GateOp.or, [51, 41]⟩,
    ⟨GateOp.or, [52, 45]⟩,
    ⟨GateOp.or, [53, 49]⟩], 54⟩

lemma boundary_size : boundary.size = 29 := rfl

lemma boundary_mono : Monotone2 boundary := by
  simp [Monotone2, boundary]

def hit (x : Fin 26 → Bool) : Bool := decide (∃ p ∈ ({5,6,7,8,11,12} : Finset (Fin 13)), ∃ w : Fin 13,
  p - w ∈ ({0,1,3,9} : Finset (Fin 13)) ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 12000000 in
lemma boundary_eval (x : Fin 26 → Bool) : circuitFun 26 boundary x =
  ((((((x 5 && (((x 15 || x 17) || x 18) || x 22)) || (x 6 && (((x 16 || x 18) || x 19) || x 23))) || (x 7 && (((x 17 || x 19) || x 20) || x 24))) || (x 8 && (((x 18 || x 20) || x 21) || x 25))) || (x 11 && (((x 15 || x 21) || x 23) || x 24))) || (x 12 && (((x 16 || x 22) || x 24) || x 25))) := by
  simp [circuitFun, boundary, Circuit.eval, Circuit.wires, GateOp.eval, List.ofFn_succ]

set_option maxRecDepth 100000 in
lemma hit_eval (x : Fin 26 → Bool) : hit x =
  ((((((x 5 && (((x 15 || x 17) || x 18) || x 22)) || (x 6 && (((x 16 || x 18) || x 19) || x 23))) || (x 7 && (((x 17 || x 19) || x 20) || x 24))) || (x 8 && (((x 18 || x 20) || x 21) || x 25))) || (x 11 && (((x 15 || x 21) || x 23) || x 24))) || (x 12 && (((x 16 || x 22) || x 24) || x 25))) := by
  rw [Bool.eq_iff_iff]
  simp [hit, Fin.exists_fin_succ, Bool.or_eq_true, Bool.and_eq_true, and_or_left, or_assoc]


def inp : List (Fin 26) :=
  (List.finRange 26).filter (fun i => i.val ∉ ([5, 6, 7, 8, 11, 12] : List ℕ))

lemma inp_length : inp.length = 20 := by decide

def pick (i : ℕ) : ℕ := (inp.getD i 0).val

lemma pick_lt (i : ℕ) : pick i < 26 := (inp.getD i 0).isLt

lemma inp_read (x : Fin 26 → Bool) (i : ℕ) (hi : i < 20) :
    (inp.map x).getD i false = x (inp.getD i 0) := by
  have hlt : i < inp.length := by simpa only [inp_length] using hi
  simp [List.getD_eq_getElem?_getD, hlt]

lemma boundary_correct (x : Fin 26 → Bool) : circuitFun 26 boundary x = hit x := by
  rw [boundary_eval, hit_eval]

def complete (B : Circuit) : Circuit :=
  ⟨boundary.gates ++ B.gates.map (renameGate 20 55 pick) ++
    [⟨GateOp.or, [rename 20 55 pick B.output, 54]⟩], 55 + B.size⟩

lemma complete_size (B : Circuit) : (complete B).size = B.size + 30 := by
  simp [complete, Circuit.size, boundary]

lemma complete_mono (B : Circuit) (hm : Monotone2 B) : Monotone2 (complete B) := by
  intro g hg
  change g ∈ (boundary.gates ++ B.gates.map (renameGate 20 55 pick)) ++
    [⟨GateOp.or, [rename 20 55 pick B.output, 54]⟩] at hg
  rcases List.mem_append.mp hg with hpre | hlast
  · rcases List.mem_append.mp hpre with hb | hmapped
    · exact boundary_mono g hb
    · exact rename_mono 20 55 pick B hm 0 g hmapped
  · simpa using List.mem_singleton.mp hlast ▸
      (show (GateOp.or ∈ ({GateOp.and, GateOp.or} : Set GateOp)) ∧
        ([rename 20 55 pick B.output, 54] : List ℕ).length ≤ 2 by simp)

set_option maxHeartbeats 2000000 in
lemma complete_eval (B : Circuit) (x : Fin 26 → Bool) :
    circuitFun 26 (complete B) x = (B.eval (inp.map x) || hit x) := by
  let w := run boundary.gates (List.ofFn x)
  have hw : w.length = 55 := by
    rw [show w = run boundary.gates (List.ofFn x) from rfl, run_length]
    simp [boundary]
  have hp : ∀ i < (inp.map x).length, pick i < w.length := by
    intro i hi
    rw [hw]
    exact (pick_lt i).trans (by decide)
  have hv : ∀ i < (inp.map x).length,
      w.getD (pick i) false = (inp.map x).getD i false := by
    intro i hi
    rw [show w = run boundary.gates (List.ofFn x) from rfl,
      run_keep _ _ _ (by simpa using pick_lt i)]
    rw [inp_read x i (by simpa only [List.length_map, inp_length] using hi)]
    have hi : pick i < (List.ofFn x).length := by simpa using pick_lt i
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    simp only [Option.getD_some, List.getElem_ofFn]
    rfl
  have hrun := run_rename B.gates (inp.map x) w [] pick hp hv B.output
  simp only [List.length_map, inp_length, hw, List.append_nil] at hrun
  change (run (B.gates.map (renameGate 20 55 pick)) w).getD
    (rename 20 55 pick B.output) false = B.eval (inp.map x) at hrun
  let v := run (B.gates.map (renameGate 20 55 pick)) w
  have hvlen : v.length = 55 + B.size := by
    rw [show v = run (B.gates.map (renameGate 20 55 pick)) w from rfl, run_length]
    simp only [hw, List.length_map, Circuit.size]
  have hboundary : v.getD 54 false = hit x := by
    rw [show v = run (B.gates.map (renameGate 20 55 pick)) w from rfl,
      run_keep _ _ _ (by omega)]
    exact boundary_correct x
  have convert (D : Circuit) : circuitFun 26 D x = (run D.gates (List.ofFn x)).getD D.output false := rfl
  rw [convert]
  simp only [complete, run_append]
  change (run [⟨GateOp.or, [rename 20 55 pick B.output, 54]⟩] v).getD (55 + B.size) false = _
  simp only [run, List.foldl_cons, List.foldl_nil, step, List.map_cons, List.map_nil,
    GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rw [← hvlen]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  change (v.getD (rename 20 55 pick B.output) false || v.getD 54 false) = _
  rw [hrun, hboundary]

end PEqualNP.Outside.Compiler

theorem PEqualNP.Outside.Compiler_complete :
      let D : Finset (Fin 13) := {0, 1, 3, 9}
      let outside : Finset (Fin 13) := {5, 6, 7, 8, 11, 12}
      let inp := (List.finRange 26).filter (fun i => i.val ∉ ([5, 6, 7, 8, 11, 12] : List ℕ))
      let hit := fun (x : Fin 26 → Bool) => decide (∃ p ∈ outside, ∃ w : Fin 13,
        p - w ∈ D ∧ x (Fin.castAdd 13 p) = true ∧ x (Fin.natAdd 13 w) = true)
      ∀ B : Circuit, Monotone2 B → B.output < 20 + B.size →
        ∃ C : Circuit, Monotone2 C ∧ C.size ≤ B.size + 30 ∧
          ∀ x : Fin 26 → Bool, circuitFun 26 C x = (B.eval (inp.map x) || hit x) := by
  dsimp only
  intro B hm _
  refine ⟨PEqualNP.Outside.Compiler.complete B,
    PEqualNP.Outside.Compiler.complete_mono B hm, ?_, ?_⟩
  · exact (PEqualNP.Outside.Compiler.complete_size B).le
  · intro x
    exact PEqualNP.Outside.Compiler.complete_eval B x
