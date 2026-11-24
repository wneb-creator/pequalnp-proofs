import Mathlib.Data.List.OfFn
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fintype.Pi

namespace PEqualNP.Outside.L_meta_3821_aux

def graph (x : Fin 10 → Bool) : Bool :=
  (List.finRange 5).any fun i =>
    (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
    (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
    (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))

def zeroRow (i : Fin 10) (v : Bool) (j : Fin 10) : Bool :=
  v && decide (j = i)

def oneRow (i : Fin 10) (v : Bool) (j : Fin 10) : Bool :=
  if v then decide (j = i ∨ j = i + 5)
  else if i.val < 2 then decide (j = 2 ∨ j = 3)
  else decide (j = 0 ∨ j = 1)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma cofactor_rows : ∀ (i : Fin 10) (v : Bool),
    zeroRow i v i = v ∧ oneRow i v i = v ∧
    graph (zeroRow i v) = false ∧ graph (oneRow i v) = true ∧
    (List.ofFn (zeroRow i v)).count true ≤ 2 ∧
    (List.ofFn (oneRow i v)).count true ≤ 2 := by
  decide +kernel

lemma cofactor_nonconstant
    (U : (Fin 10 → Bool) → Bool)
    (h : ∀ x, graph x = false ∨ (List.ofFn x).count true ≤ 2 → U x = graph x)
    (i : Fin 10) (v : Bool) :
    ∃ x y : Fin 10 → Bool,
      U (Function.update x i v) ≠ U (Function.update y i v) := by
  obtain ⟨hz, ho, hgz, hgo, hcz, hco⟩ := cofactor_rows i v
  have ez : Function.update (zeroRow i v) i v = zeroRow i v := by
    exact Function.update_eq_self_iff.mpr hz.symm
  have eo : Function.update (oneRow i v) i v = oneRow i v := by
    exact Function.update_eq_self_iff.mpr ho.symm
  refine ⟨zeroRow i v, oneRow i v, ?_⟩
  rw [ez, eo, h _ (Or.inl hgz), h _ (Or.inr hco), hgz, hgo]
  decide

end PEqualNP.Outside.L_meta_3821_aux
