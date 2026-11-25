import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590_aux.OutputLast

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

lemma output_last (n : ℕ) (C : Circuit) (hao : PEqualNP.TopForm.IsAO2 n C)
    (hlo : n ≤ C.output) (hhi : C.output < n + C.size) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size ≤ C.size ∧
      circuitFun n D = circuitFun n C ∧ D.output + 1 = n + D.size := by
  let k := C.output - n + 1
  have hk : k ≤ C.gates.length := by change k ≤ C.size; dsimp [k]; omega
  let D : Circuit := ⟨C.gates.take k, C.output⟩
  have hlen : D.gates.length = k := by simp only [D, List.length_take, Nat.min_eq_left hk]
  have same (j : ℕ) (hj : j < D.gates.length) :
      PEqualNP.MetaComplexity.NestedCover.gateAt D j =
        PEqualNP.MetaComplexity.NestedCover.gateAt C j := by
    have hjk : j < k := by omega
    have hjC : j < C.gates.length := by omega
    simp only [PEqualNP.MetaComplexity.NestedCover.gateAt]
    rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ hjC]
    simp only [D, List.getElem_take]
  refine ⟨D, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro g hg
    exact hao.1 g (List.mem_of_mem_take hg)
  · intro j hj i hi
    have hjC : j < C.gates.length := by omega
    rw [same j hj] at hi
    exact hao.2.1 j hjC i hi
  · intro g hg
    exact hao.2.2 g (List.mem_of_mem_take hg)
  · change D.gates.length ≤ C.gates.length
    omega
  · funext x
    change (run (C.gates.take k) (List.ofFn x)).getD C.output false =
      (run C.gates (List.ofFn x)).getD C.output false
    symm
    have hb : C.output < (List.ofFn x).length + (C.gates.take k).length := by
      rw [List.length_ofFn, List.length_take, Nat.min_eq_left hk]
      dsimp [k]
      omega
    simpa only [List.take_append_drop] using run_prefix
      (C.gates.take k) (C.gates.drop k) (List.ofFn x) C.output hb
  · change C.output + 1 = n + D.gates.length
    rw [hlen]
    dsimp [k]
    omega

end PEqualNP.Outside.L_meta_2590_aux.OutputLast

