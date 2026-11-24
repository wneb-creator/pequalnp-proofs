import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2028

lemma size_pos_of_nonempty_edge_function (n : ℕ) (G : SimpleGraph (Fin n))
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hedge : ∃ u v : Fin n, G.Adj u v)
    (hcomp : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) :
    0 < C.size := by
  classical
  by_contra hpos
  have hsize : C.size = 0 := Nat.eq_zero_of_not_pos hpos
  have hnil : C.gates = [] := List.eq_nil_of_length_eq_zero hsize
  by_cases hout : C.output < n
  · let i : Fin n := ⟨C.output, hout⟩
    let x : Fin n → Bool := fun j => decide (j = i)
    have heval : C.eval (List.ofFn x) = true := by
      simp [PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.CircuitLowerBounds.Circuit.wires, hnil,
        List.getD_eq_getElem?_getD, List.getElem?_ofFn, hout, x, i]
    obtain ⟨u, v, huv, hu, hv⟩ := (hcomp x).mp heval
    have hui : u = i := by simpa [x] using hu
    have hvi : v = i := by simpa [x] using hv
    subst u
    subst v
    exact G.loopless.irrefl _ huv
  · have heval : C.eval (List.ofFn fun _ : Fin n => true) = true := by
      apply (hcomp _).mpr
      obtain ⟨u, v, huv⟩ := hedge
      exact ⟨u, v, huv, rfl, rfl⟩
    simp [PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, hnil,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn, hout] at heval

end PEqualNP.Outside.L_meta_2028
