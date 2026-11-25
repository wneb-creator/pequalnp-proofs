import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_3451

lemma no_incidence (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hI : ∀ p l, ¬ I p l) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  let D : PEqualNP.CircuitLowerBounds.Circuit := ⟨[], N + N⟩
  refine ⟨D, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [D, PEqualNP.MetaComplexity.Monotone2]
  · simp [D, PEqualNP.MetaComplexity.NestedCover.ReadsBack]
  · simp [D, PEqualNP.CircuitLowerBounds.Circuit.size]
  · intro z
    simp [D, PEqualNP.MetaComplexity.circuitFun,
      PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      hI]
  · simp [D]
  · simp [D]

lemma positive_size (N : ℕ) (I : Fin N → Fin N → Prop)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hI : ∃ p l, I p l)
    (hfun : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    0 < C.size := by
  by_contra hsize
  have hg : C.gates = [] := by
    apply List.length_eq_zero_iff.mp
    exact Nat.eq_zero_of_not_pos hsize
  by_cases hout : C.output < N + N
  · let k : Fin (N + N) := ⟨C.output, hout⟩
    have hone : PEqualNP.MetaComplexity.circuitFun (N + N) C
        (fun v => decide (v = k)) = true := by
      simp [PEqualNP.MetaComplexity.circuitFun,
        PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
        hg, List.getD_eq_getElem?_getD, hout, k]
    obtain ⟨p, l, _, hp, hl⟩ := (hfun _).mp hone
    have he : Fin.castAdd N p = Fin.natAdd N l :=
      (of_decide_eq_true hp).trans (of_decide_eq_true hl).symm
    have hv := congrArg Fin.val he
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  · have hall : PEqualNP.MetaComplexity.circuitFun (N + N) C (fun _ => true) = true := by
      apply (hfun _).mpr
      obtain ⟨p, l, hpl⟩ := hI
      exact ⟨p, l, hpl, rfl, rfl⟩
    simp [PEqualNP.MetaComplexity.circuitFun,
      PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
      hg, List.getD_eq_getElem?_getD, hout] at hall

lemma one_input_each (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hN : N = 1)
    (hfun : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  subst N
  by_cases hI : I 0 0
  · have hsize := positive_size 1 I C ⟨0, 0, hI⟩ hfun
    let D : PEqualNP.CircuitLowerBounds.Circuit :=
      ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩], 2⟩
    refine ⟨D, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [D, PEqualNP.MetaComplexity.Monotone2]
    · norm_num [D, PEqualNP.MetaComplexity.NestedCover.ReadsBack,
        PEqualNP.MetaComplexity.NestedCover.gateAt]
    · exact hsize
    · intro z
      simp [D, PEqualNP.MetaComplexity.circuitFun,
        PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
        PEqualNP.CircuitLowerBounds.GateOp.eval, List.ofFn_succ, hI]
    · simp [hI]
    · norm_num [D, PEqualNP.MetaComplexity.NestedCover.gateAt,
        PEqualNP.CircuitLowerBounds.Circuit.wires,
        PEqualNP.CircuitLowerBounds.GateOp.eval, List.ofFn_succ]
  · exact no_incidence 1 I C (by simpa using hI)

lemma cast_point_ne_line {N : ℕ} (p l : Fin N) :
    Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

def edgeCircuit {N : ℕ} (p l : Fin N) : PEqualNP.CircuitLowerBounds.Circuit :=
  ⟨[⟨PEqualNP.CircuitLowerBounds.GateOp.and, [p.val, N + l.val]⟩], N + N⟩

lemma edgeCircuit_value {N : ℕ} (p l : Fin N) (z : Fin (N + N) → Bool) :
    PEqualNP.MetaComplexity.circuitFun (N + N) (edgeCircuit p l) z =
      (z (Fin.castAdd N p) && z (Fin.natAdd N l)) := by
  have hp : p.val < N + N := by omega
  have hl : N + l.val < N + N := by omega
  simp [edgeCircuit, PEqualNP.MetaComplexity.circuitFun,
    PEqualNP.CircuitLowerBounds.Circuit.eval, PEqualNP.CircuitLowerBounds.Circuit.wires,
    PEqualNP.CircuitLowerBounds.GateOp.eval, List.getD_eq_getElem?_getD,
    List.getElem?_ofFn, hp, hl]
  congr 2
  apply Fin.ext
  simp [Nat.add_comm]

lemma single_incidence (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit) (p0 l0 : Fin N)
    (hI : ∀ p l, I p l ↔ p = p0 ∧ l = l0)
    (hfun : ∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  have hsize := positive_size N I C ⟨p0, l0, (hI p0 l0).mpr ⟨rfl, rfl⟩⟩ hfun
  refine ⟨edgeCircuit p0 l0, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [edgeCircuit, PEqualNP.MetaComplexity.Monotone2]
  · intro j hj i hi
    have hj0 : j = 0 := by simpa [edgeCircuit] using hj
    subst j
    simp only [edgeCircuit, PEqualNP.MetaComplexity.NestedCover.gateAt,
      List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl <;> omega
  · exact hsize
  · intro z
    simp [edgeCircuit_value, hI]
  · intro j hj hand p l hnot
    have hj0 : j = 0 := by simpa [edgeCircuit] using hj
    subst j
    change PEqualNP.MetaComplexity.circuitFun (N + N) (edgeCircuit p0 l0)
      (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = false
    rw [edgeCircuit_value]
    have hpl : ¬ (p = p0 ∧ l = l0) := by simpa only [hI] using hnot
    simp [Fin.ext_iff] at hpl ⊢
    omega
  · intro j hj hand
    have hj0 : j = 0 := by simpa [edgeCircuit] using hj
    subst j
    constructor
    · intro p
      change PEqualNP.MetaComplexity.circuitFun (N + N) (edgeCircuit p0 l0)
        (fun k => decide (k = Fin.castAdd N p)) = false
      rw [edgeCircuit_value]
      simp [Fin.ext_iff]
      omega
    · intro l
      change PEqualNP.MetaComplexity.circuitFun (N + N) (edgeCircuit p0 l0)
        (fun k => decide (k = Fin.natAdd N l)) = false
      rw [edgeCircuit_value]
      simp [Fin.ext_iff]
      omega

end PEqualNP.Outside.L_meta_3451
