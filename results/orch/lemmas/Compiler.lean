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

end PEqualNP.Outside.Compiler
