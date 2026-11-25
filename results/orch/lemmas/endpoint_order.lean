import constant_sweep
import one_not_semantics
import map_rigidity

namespace PEqualNP.Outside.L_meta_1886_aux.EndpointOrder

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux
open ConstantSweep

def awayLE (r : Nat) (w v : List Bool) : Prop :=
  ∀ i, i ≠ r → w.getD i false ≤ v.getD i false

lemma and_false (l : List Nat) (f : Nat → Bool) (i : Nat) (hi : i ∈ l) (hf : f i = false) :
    GateOp.and.eval (l.map f) = false := by
  cases he : GateOp.and.eval (l.map f) with
  | false => rfl
  | true =>
    have h := List.all_eq_true.mp he (f i) (List.mem_map.mpr ⟨i,hi,rfl⟩)
    simp only [id_eq,hf] at h
    cases h

lemma or_true (l : List Nat) (f : Nat → Bool) (i : Nat) (hi : i ∈ l) (hf : f i = true) :
    GateOp.or.eval (l.map f) = true := by
  exact List.any_eq_true.mpr ⟨f i,List.mem_map.mpr ⟨i,hi,rfl⟩,hf⟩

lemma gate_away (r : Nat) (g : Gate) (mono : g.op = .and ∨ g.op = .or)
    (absent : r ∉ g.inputs) {w v : List Bool} (order : awayLE r w v) :
    g.op.eval (g.inputs.map fun i => w.getD i false) ≤
      g.op.eval (g.inputs.map fun i => v.getD i false) := by
  rw [Bool.le_iff_imp]
  apply OneNot.eval_true_mono g.op mono g.inputs
  intro i hi hv
  have h := order i (fun eq => absent (eq ▸ hi))
  exact (Bool.le_iff_imp.mp h) hv

lemma gate_paired (r z : Nat) (g : Gate) (mono : g.op = .and ∨ g.op = .or)
    (paired : r ∈ g.inputs → z ∈ g.inputs) {w v : List Bool}
    (wr : w.getD r false = true) (vr : v.getD r false = false)
    (wz : w.getD z false = false) (vz : v.getD z false = true)
    (order : awayLE r w v) :
    g.op.eval (g.inputs.map fun i => w.getD i false) ≤
      g.op.eval (g.inputs.map fun i => v.getD i false) := by
  by_cases hr : r ∈ g.inputs
  · have hz := paired hr
    rcases mono with hm | hm
    · rw [hm,and_false g.inputs _ z hz wz,and_false g.inputs _ r hr vr]
    · rw [hm,or_true g.inputs _ r hr wr,or_true g.inputs _ z hz vz]
  · exact gate_away r g mono hr order

lemma append_away (r : Nat) {w v : List Bool} (len : w.length = v.length)
    (order : awayLE r w v) {a b : Bool} (hab : a ≤ b) :
    awayLE r (w ++ [a]) (v ++ [b]) := by
  intro i hi
  by_cases hlt : i < w.length
  · rw [List.getD_append _ _ _ _ hlt,List.getD_append _ _ _ _ (by omega)]
    exact order i hi
  · have hw : w.length ≤ i := by omega
    have hv : v.length ≤ i := by omega
    rw [List.getD_append_right _ _ _ _ hw,List.getD_append_right _ _ _ _ hv,←len]
    cases e : i - w.length with
    | zero => simpa using hab
    | succ n => simp

lemma run_away (r : Nat) (gs : List Gate)
    (mono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (absent : ∀ g ∈ gs, r ∉ g.inputs)
    {w v : List Bool} (len : w.length = v.length) (order : awayLE r w v) :
    awayLE r (run gs w) (run gs v) := by
  induction gs generalizing w v with
  | nil => exact order
  | cons g gs ih =>
    change awayLE r (run gs (step w g)) (run gs (step v g))
    apply ih (fun q hq => mono q (by simp [hq])) (fun q hq => absent q (by simp [hq]))
    · simp [step,len]
    · exact append_away r len order (gate_away r g (mono g (by simp)) (absent g (by simp)) order)

lemma run_paired (r z : Nat) (gs : List Gate)
    (mono : ∀ g ∈ gs, g.op = .and ∨ g.op = .or)
    (paired : ∀ g ∈ gs, r ∈ g.inputs → z ∈ g.inputs)
    {w v : List Bool} (len : w.length = v.length) (hr : r < w.length) (hz : z < w.length)
    (wr : w.getD r false = true) (vr : v.getD r false = false)
    (wz : w.getD z false = false) (vz : v.getD z false = true)
    (order : awayLE r w v) : awayLE r (run gs w) (run gs v) := by
  induction gs generalizing w v with
  | nil => exact order
  | cons g gs ih =>
    change awayLE r (run gs (step w g)) (run gs (step v g))
    apply ih (fun q hq => mono q (by simp [hq])) (fun q hq => paired q (by simp [hq]))
    · simp [step,len]
    · simp [step]; omega
    · simp [step]; omega
    · rw [step,List.getD_append _ _ _ _ hr]; exact wr
    · rw [step,List.getD_append _ _ _ _ (by omega)]; exact vr
    · rw [step,List.getD_append _ _ _ _ hz]; exact wz
    · rw [step,List.getD_append _ _ _ _ (by omega)]; exact vz
    · exact append_away r len order (gate_paired r z g (mono g (by simp)) (paired g (by simp)) wr vr wz vz order)

end PEqualNP.Outside.L_meta_1886_aux.EndpointOrder
