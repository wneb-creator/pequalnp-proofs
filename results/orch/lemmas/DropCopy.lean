import Mathlib.Tactic.SplitIfs
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592

open PEqualNP.CircuitLowerBounds

def eraseWire (n a i : ℕ) : ℕ :=
  if i < n then i else if i = n then a else i - 1

def eraseGate (n a : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (eraseWire n a)⟩

def eraseRelated (n a : ℕ) (w v : List Bool) : Prop :=
  ∀ i : ℕ, v.getD (eraseWire n a i) false = w.getD i false

lemma erase_start (n a : ℕ) (x : List Bool) (hx : x.length = n) :
    eraseRelated n a (x ++ [x.getD a false]) x := by
  intro i
  by_cases hi : i < n
  · simp only [eraseWire, hi, ite_true]
    exact (List.getD_append _ _ _ _ (by omega)).symm
  · by_cases he : i = n
    · subst i
      simp only [eraseWire, Nat.lt_irrefl, ite_false, ite_true]
      rw [← hx]
      simp
    · simp only [eraseWire, hi, he, ite_false]
      rw [List.getD_eq_default _ _ (by omega),
        List.getD_eq_default _ _ (by simp; omega)]

lemma erase_append (n a : ℕ) (ha : a < n) (w v : List Bool)
    (hr : eraseRelated n a w v) (hl : w.length = v.length + 1)
    (hn : n ≤ v.length) (b : Bool) :
    eraseRelated n a (w ++ [b]) (v ++ [b]) := by
  intro i
  by_cases hi : i < w.length
  · have hj : eraseWire n a i < v.length := by
      unfold eraseWire
      split_ifs <;> omega
    rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ hi]
    exact hr i
  · have his : ¬ i < n := by omega
    have hie : i ≠ n := by omega
    simp only [eraseWire, his, hie, ite_false]
    by_cases he : i = w.length
    · have hv : i - 1 = v.length := by omega
      rw [hv, he]
      simp
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]

lemma erased_gate_value (n a : ℕ) (w v : List Bool)
    (hr : eraseRelated n a w v) (g : Gate) :
    (eraseGate n a g).op.eval ((eraseGate n a g).inputs.map (fun i => v.getD i false)) =
      g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
  simp only [eraseGate, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact hr i

lemma erase_fold (n a : ℕ) (ha : a < n) (gs : List Gate) :
    ∀ w v : List Bool, eraseRelated n a w v → w.length = v.length + 1 → n ≤ v.length →
    eraseRelated n a
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
      ((gs.map (eraseGate n a)).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v) := by
  induction gs with
  | nil => intro w v hr hl hn; exact hr
  | cons g gs ih =>
    intro w v hr hl hn
    simp only [List.map_cons, List.foldl_cons]
    rw [erased_gate_value n a w v hr g]
    apply ih
    · exact erase_append n a ha w v hr hl hn _
    · simp only [List.length_append, List.length_singleton]
      omega
    · simp only [List.length_append, List.length_singleton]
      omega

lemma erase_first_eval (n a : ℕ) (ha : a < n) (g : Gate) (gs : List Gate)
    (out : ℕ) (x : List Bool) (hx : x.length = n)
    (hc : g.op.eval (g.inputs.map fun i => x.getD i false) = x.getD a false) :
    (⟨gs.map (eraseGate n a), eraseWire n a out⟩ : Circuit).eval x =
      (⟨g :: gs, out⟩ : Circuit).eval x := by
  change ((gs.map (eraseGate n a)).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD
      (eraseWire n a out) false =
    ((g :: gs).foldl
      (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x).getD out false
  rw [List.foldl_cons, hc]
  exact erase_fold n a ha gs _ x (erase_start n a x hx) (by simp) (by omega) out

lemma copy_gate_value (g : Gate) (a : ℕ)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hin : g.inputs = [a] ∨ g.inputs = [a, a]) (x : List Bool) :
    g.op.eval (g.inputs.map fun i => x.getD i false) = x.getD a false := by
  rcases hop with hop | hop <;> rcases hin with hin | hin <;>
    simp [hop, hin, GateOp.eval]

lemma delete_copy_first (n a : ℕ) (ha : a < n) (g : Gate) (gs : List Gate) (out : ℕ)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hin : g.inputs = [a] ∨ g.inputs = [a, a])
    (hf : PEqualNP.MetaComplexity.FanInTwo (⟨g :: gs, out⟩ : Circuit))
    (hn : ∃ h ∈ g :: gs, h.op = GateOp.not) :
    ∃ D : Circuit, D.size + 1 = (⟨g :: gs, out⟩ : Circuit).size ∧
      PEqualNP.MetaComplexity.FanInTwo D ∧
      (∃ h ∈ D.gates, h.op = GateOp.not) ∧
      ∀ x : List Bool, x.length = n → D.eval x = (⟨g :: gs, out⟩ : Circuit).eval x := by
  refine ⟨⟨gs.map (eraseGate n a), eraseWire n a out⟩, ?_, ?_, ?_, ?_⟩
  · simp [Circuit.size]
  · intro h hh
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hh
    simpa [eraseGate] using hf q (List.mem_cons_of_mem g hq)
  · obtain ⟨h, hh, hn⟩ := hn
    have hng : g.op ≠ GateOp.not := by rcases hop with hop | hop <;> simp [hop]
    have hmem : h ∈ gs := by
      rcases List.mem_cons.mp hh with he | ht
      · subst h
        exact False.elim (hng hn)
      · exact ht
    exact ⟨eraseGate n a h, List.mem_map.mpr ⟨h, hmem, rfl⟩, hn⟩
  · intro x hx
    exact erase_first_eval n a ha g gs out x hx (copy_gate_value g a hop hin x)

end PEqualNP.Outside.L_meta_2592
