import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.FirstMerge

open PEqualNP.CircuitLowerBounds

def isNotGate (op : GateOp) : Bool := match op with | .not => true | _ => false

def gateOrigin (origins : List (Option ℕ)) (g : Gate) : Option ℕ :=
  match g.op, g.inputs with
  | .not, i :: _ => origins.getD i none
  | _, _ => none

def originStep (origins : List (Option ℕ)) (g : Gate) : List (Option ℕ) :=
  origins ++ [gateOrigin origins g]

def readsOrigin (origins : List (Option ℕ)) (v : ℕ) (g : Gate) : Bool :=
  g.inputs.any fun i => decide (origins.getD i none = some v)

def cutCharge (origins : List (Option ℕ)) (v : ℕ) (g : Gate) : ℕ :=
  if isNotGate g.op then 0 else if readsOrigin origins v g then 1 else 0

def cutCost (origins : List (Option ℕ)) (v : ℕ) : List Gate → ℕ
  | [] => 0
  | g :: gs => cutCharge origins v g + cutCost (originStep origins g) v gs

def gateStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def AgreeOutside (origins : List (Option ℕ)) (u v : ℕ) (a b : List Bool) : Prop :=
  origins.length = a.length ∧ origins.length = b.length ∧
    ∀ i, origins.getD i none ≠ some u → origins.getD i none ≠ some v →
      a.getD i false = b.getD i false

lemma charge_zero_no_reads (origins : List (Option ℕ)) (u : ℕ) (g : Gate)
    (notFlag : isNotGate g.op = false) (charge : cutCharge origins u g = 0) :
    ∀ i ∈ g.inputs, origins.getD i none ≠ some u := by
  have hr : readsOrigin origins u g = false := by
    cases h : readsOrigin origins u g
    · rfl
    · simp [cutCharge, notFlag, h] at charge
  intro i hi eq
  have yes : readsOrigin origins u g = true := by
    exact List.any_eq_true.mpr ⟨i, hi, decide_eq_true eq⟩
  rw [yes] at hr
  cases hr

lemma new_gate_agrees (origins : List (Option ℕ)) (u v : ℕ) (a b : List Bool) (g : Gate)
    (agree : AgreeOutside origins u v a b)
    (costU : cutCharge origins u g = 0) (costV : cutCharge origins v g = 0)
    (newU : gateOrigin origins g ≠ some u) (newV : gateOrigin origins g ≠ some v) :
    g.op.eval (g.inputs.map fun i => a.getD i false) =
      g.op.eval (g.inputs.map fun i => b.getD i false) := by
  by_cases hn : g.op = .not
  · cases hi : g.inputs with
    | nil => rfl
    | cons i is =>
      have hu : origins.getD i none ≠ some u := by simpa [gateOrigin, hn, hi] using newU
      have hv : origins.getD i none ≠ some v := by simpa [gateOrigin, hn, hi] using newV
      rw [hn]
      change (!(a.getD i false)) = (!(b.getD i false))
      rw [agree.2.2 i hu hv]
  · have flag : isNotGate g.op = false := by
      cases ho : g.op <;> simp [isNotGate]
      exact (hn ho).elim
    have same : g.inputs.map (fun i => a.getD i false) = g.inputs.map (fun i => b.getD i false) := by
      apply List.map_congr_left
      intro i hi
      exact agree.2.2 i (charge_zero_no_reads origins u g flag costU i hi)
        (charge_zero_no_reads origins v g flag costV i hi)
    rw [same]

lemma agree_step (origins : List (Option ℕ)) (u v : ℕ) (a b : List Bool) (g : Gate)
    (agree : AgreeOutside origins u v a b)
    (costU : cutCharge origins u g = 0) (costV : cutCharge origins v g = 0) :
    AgreeOutside (originStep origins g) u v (gateStep a g) (gateStep b g) := by
  refine ⟨by simp [originStep, gateStep, agree.1], by simp [originStep, gateStep, agree.2.1], ?_⟩
  intro i hu hv
  have la := agree.1
  have lb := agree.2.1
  by_cases hi : i < origins.length
  · have ai : i < a.length := by omega
    have bi : i < b.length := by omega
    have hu' : origins.getD i none ≠ some u := by
      simpa only [originStep, List.getD_append _ _ _ _ hi] using hu
    have hv' : origins.getD i none ≠ some v := by
      simpa only [originStep, List.getD_append _ _ _ _ hi] using hv
    simpa only [gateStep, List.getD_append _ _ _ _ ai, List.getD_append _ _ _ _ bi]
      using agree.2.2 i hu' hv'
  · by_cases he : i = origins.length
    · subst i
      have hu' : gateOrigin origins g ≠ some u := by simpa [originStep] using hu
      have hv' : gateOrigin origins g ≠ some v := by simpa [originStep] using hv
      have eq := new_gate_agrees origins u v a b g agree costU costV hu' hv'
      simp only [gateStep]
      rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega)]
      have ha : origins.length - a.length = 0 := by omega
      have hb : origins.length - b.length = 0 := by omega
      simpa only [ha, hb, List.getD_cons_zero] using eq
    · rw [List.getD_eq_default _ _ (by simp [gateStep]; omega),
          List.getD_eq_default _ _ (by simp [gateStep]; omega)]

lemma agree_tail (origins : List (Option ℕ)) (u v : ℕ) (a b : List Bool) (gs : List Gate)
    (agree : AgreeOutside origins u v a b)
    (costU : cutCost origins u gs = 0) (costV : cutCost origins v gs = 0) :
    AgreeOutside (gs.foldl originStep origins) u v
      (gs.foldl gateStep a) (gs.foldl gateStep b) := by
  induction gs generalizing origins a b with
  | nil => exact agree
  | cons g gs ih =>
    simp only [cutCost] at costU costV
    exact ih _ _ _ (agree_step origins u v a b g agree (by omega) (by omega)) (by omega) (by omega)

end PEqualNP.Outside.L_meta_2592_aux.FirstMerge
