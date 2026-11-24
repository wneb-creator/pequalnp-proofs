import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3451

lemma edgeless (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hI : ∀ p l, ¬ I p l) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  refine ⟨⟨[], N + N⟩, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [PEqualNP.MetaComplexity.Monotone2]
  · simp [PEqualNP.MetaComplexity.NestedCover.ReadsBack]
  · simp [PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro z
    simp [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, List.getD_eq_getElem?_getD, hI]
  · simp
  · simp

lemma positive_size (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hI : ∃ p l, I p l)
    (hfun : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    0 < C.size := by
  by_contra! hsize
  have hnil : C.gates = [] := by
    simpa [PEqualNP.CircuitLowerBounds.Circuit.size] using Nat.eq_zero_of_le_zero hsize
  obtain ⟨p, l, hpl⟩ := hI
  have hall : PEqualNP.MetaComplexity.circuitFun (N + N) C (fun _ => true) = true :=
    (hfun _).mpr ⟨p, l, hpl, rfl, rfl⟩
  have hout : C.output < N + N := by
    by_contra! hbound
    simp only [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, hnil, List.foldl_nil] at hall
    rw [List.getD_eq_default _ _ (by simpa using hbound)] at hall
    cases hall
  let i : Fin (N + N) := ⟨C.output, hout⟩
  let z : Fin (N + N) → Bool := fun k => decide (k = i)
  have hz : PEqualNP.MetaComplexity.circuitFun (N + N) C z = true := by
    simp [PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
      PEqualNP.CircuitLowerBounds.Circuit.wires, hnil, List.getD_eq_getElem?_getD, hout, z, i]
  obtain ⟨p', l', _, hp', hl'⟩ := (hfun z).mp hz
  simp only [z, decide_eq_true_eq] at hp' hl'
  have heq := congrArg Fin.val (hp'.trans hl'.symm)
  simp only [Fin.val_castAdd, Fin.val_natAdd] at heq
  have hpbound := p'.isLt
  omega

lemma one_point (I : Fin 1 → Fin 1 → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit)
    (hfun : ∀ z : Fin (1 + 1) → Bool,
      PEqualNP.MetaComplexity.circuitFun (1 + 1) C z = true ↔
      ∃ p l : Fin 1, I p l ∧ z (Fin.castAdd 1 p) = true ∧ z (Fin.natAdd 1 l) = true) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (1 + 1) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (1 + 1) → Bool, PEqualNP.MetaComplexity.circuitFun (1 + 1) D z = true ↔ ∃ p l : Fin 1, I p l ∧ z (Fin.castAdd 1 p) = true ∧ z (Fin.natAdd 1 l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin 1, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (1 + 1) => decide (ke = Fin.castAdd 1 p0 ∨ ke = Fin.natAdd 1 l0)))).getD (1 + 1 + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin 1, (D.wires (List.ofFn (fun kc : Fin (1 + 1) => decide (kc = Fin.castAdd 1 p)))).getD (1 + 1 + j) false = false) ∧ ∀ l : Fin 1, (D.wires (List.ofFn (fun kd : Fin (1 + 1) => decide (kd = Fin.natAdd 1 l)))).getD (1 + 1 + j) false = false) := by
  by_cases hI : I 0 0
  · let D : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩], 2⟩
    have hIall (p l : Fin 1) : I p l := by
      have hp : p = 0 := Subsingleton.elim _ _
      have hl : l = 0 := Subsingleton.elim _ _
      simpa [hp, hl] using hI
    refine ⟨D, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [PEqualNP.MetaComplexity.Monotone2, D]
    · decide
    · have hsize := positive_size 1 I C ⟨0, 0, hI⟩ hfun
      change 1 ≤ C.size
      omega
    · intro z
      simp [D, PEqualNP.MetaComplexity.circuitFun, PEqualNP.CircuitLowerBounds.Circuit.eval,
        PEqualNP.CircuitLowerBounds.Circuit.wires, PEqualNP.CircuitLowerBounds.GateOp.eval,
        List.ofFn_succ, Fin.exists_fin_one, hIall]
    · intro j hj hop p l hn
      exact (hn (hIall p l)).elim
    · intro j hj _
      have hj0 : j = 0 := by simpa [D] using hj
      subst j
      constructor <;> intro p <;> fin_cases p <;> decide
  · apply edgeless 1 I C
    intro p l
    have hp : p = 0 := Subsingleton.elim _ _
    have hl : l = 0 := Subsingleton.elim _ _
    simpa [hp, hl] using hI

end PEqualNP.Outside.L_meta_3451
