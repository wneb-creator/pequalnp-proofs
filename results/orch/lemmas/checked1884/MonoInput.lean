import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884.MonoInput

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def xr (n r : ℕ) : List Bool := List.ofFn fun i : Fin n => r.testBit i

def freeRows : List ℕ := [3, 1030, 1036, 13, 17, 1048, 33, 1074, 1090, 69, 1128, 1140, 1156, 133, 1162, 1184, 1224, 201, 1232, 1288, 265, 1300, 1312, 1344, 321, 385, 1426, 521, 1552, 1572, 1578, 1600, 577, 1664, 641, 1794, 1796, 773]

def target (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
  (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def rowValue (r : ℕ) : Bool := target (fun i => r.testBit i)

lemma freeRows_lt : ∀ r ∈ freeRows, r < 2 ^ 11 := by decide +kernel

lemma freeRows_correlated : ∀ r ∈ freeRows,
    xr 11 r = List.ofFn (fun i : Fin 10 => r.testBit i) ++ [!(r.testBit 0)] := by
  decide +kernel

lemma monotone_of_zero_not (C : Circuit) (hC : FanInTwo C)
    (hn : PEqualNP.NotBracket.notCount C = 0) : Monotone2 C := by
  classical
  have he : (C.gates.filter fun (g : Gate) => decide (g.op = GateOp.not)) = [] :=
    List.length_eq_zero_iff.mp (by simpa [PEqualNP.NotBracket.notCount] using hn)
  intro g hg
  obtain ⟨hop, hlen⟩ := hC g hg
  have hnot : g.op ≠ GateOp.not := by
    intro h
    have hm : g ∈ C.gates.filter (fun (g : Gate) => decide (g.op = GateOp.not)) := by
      exact List.mem_filter.mpr ⟨hg, by simp [h]⟩
    rw [he] at hm
    simp at hm
  exact ⟨by simpa [hnot] using hop, hlen⟩

lemma canonical_rows (C : Circuit)
    (correct : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x ++ [!(x 0)]) = target x) :
    ∀ r ∈ freeRows, C.eval (xr 11 r) = rowValue r := by
  intro r hr
  rw [freeRows_correlated r hr]
  exact correct (fun i => r.testBit i)

end PEqualNP.Outside.L_meta_1884.MonoInput
