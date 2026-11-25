namespace PEqualNP.Outside.L_meta_3451_aux.Prune

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def andFlag : GateOp → ℕ
  | .and => 1
  | _ => 0

def ands : List Gate → ℕ
  | [] => 0
  | g :: gs => (andFlag g.op) + ands gs

lemma ands_zero_le (bad : ℕ → Bool) (gs : List Gate) (j : ℕ) :
    ands (zeroGates bad j gs) ≤ ands gs := by
  induction gs generalizing j with
  | nil => exact Nat.le_refl _
  | cons g gs ih =>
    have ht := ih (j + 1)
    cases hb : bad j with
    | false => simpa [zeroGates, ands, zeroGate, hb] using
        Nat.add_le_add_left ht (andFlag g.op)
    | true =>
      simp only [zeroGates, ands, zeroGate, hb, ite_true, andFlag, Nat.zero_add]
      omega

lemma ands_zero_lt (bad : ℕ → Bool) (gs : List Gate) (j r : ℕ)
    (hr : r < gs.length) (hb : bad (j + r) = true)
    (hop : (gs.getD r ⟨.or, []⟩).op = GateOp.and) :
    ands (zeroGates bad j gs) < ands gs := by
  induction gs generalizing j r with
  | nil => simp at hr
  | cons g gs ih =>
    cases r with
    | zero =>
      have ht := ands_zero_le bad gs (j + 1)
      simp only [Nat.add_zero] at hb
      simp only [List.getD_cons_zero] at hop
      simp only [zeroGates, ands, zeroGate, hb, ite_true, hop, andFlag, Nat.zero_add]
      omega
    | succ r =>
      have ht := ih (j + 1) r (by simpa using hr)
        (by simpa [Nat.add_assoc, Nat.add_comm 1] using hb)
        (by simpa only [List.getD_cons_succ] using hop)
      cases hb0 : bad j with
      | false => simpa [zeroGates, ands, zeroGate, hb0] using
          Nat.add_lt_add_left ht (andFlag g.op)
      | true =>
        simp only [zeroGates, ands, zeroGate, hb0, ite_true, andFlag, Nat.zero_add]
        omega

lemma edge_sensitive_normalization (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hC : Monotone2 C) (hback : ReadsBack (N + N) C)
    (hsem : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ D : Circuit, D.size ≤ C.size ∧ Monotone2 D ∧ ReadsBack (N + N) D ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ E : Circuit, Monotone2 E → ReadsBack (N + N) E →
        (∀ z : Fin (N + N) → Bool, circuitFun (N + N) E z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
        D.size ≤ E.size) ∧
      (∀ j : ℕ, j < D.gates.length → (gateAt D j).op = GateOp.and →
        ∃ p l : Fin N, I p l ∧ circuitFun (N + N)
          (zeroCircuit D (fun k => decide (k = j)))
          (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = false) := by
  classical
  let Model := fun D : Circuit => Monotone2 D ∧ ReadsBack (N + N) D ∧
    (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)
  have hsizeEx : ∃ k : ℕ, ∃ D : Circuit, Model D ∧ D.size = k :=
    ⟨C.size, C, ⟨hC, hback, hsem⟩, rfl⟩
  let sz := Nat.find hsizeEx
  let Good := fun D : Circuit => D.size = sz ∧ Model D
  obtain ⟨B, hB, hBsize⟩ := Nat.find_spec hsizeEx
  have hex : ∃ k : ℕ, ∃ D : Circuit, Good D ∧ ands D.gates = k :=
    ⟨ands B.gates, B, ⟨hBsize, hB⟩, rfl⟩
  obtain ⟨D, hD, hmin⟩ := Nat.find_spec hex
  obtain ⟨hsizeEq, hmono, hread, hfun⟩ := hD
  have hglobalmin : ∀ E : Circuit, Model E → D.size ≤ E.size := by
    intro E hE
    exact hsizeEq.trans_le (Nat.find_min' hsizeEx ⟨E, hE, rfl⟩)
  have hsize : D.size ≤ C.size := hglobalmin C ⟨hC, hback, hsem⟩
  refine ⟨D, hsize, hmono, hread, hfun,
    (fun E hm hr hf => hglobalmin E ⟨hm, hr, hf⟩), ?_⟩
  intro j hj hand
  by_contra hnone
  let bad := fun k : ℕ => decide (k = j)
  let E := zeroCircuit D bad
  have hEmono : Monotone2 E := zero_monotone D bad hmono
  have hedge : ∀ p l : Fin N, I p l → circuitFun (N + N) E
      (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = true := by
    intro p l hpl
    cases hv : circuitFun (N + N) E
        (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) with
    | false => exact (hnone ⟨p, l, hpl, hv⟩).elim
    | true => rfl
  have hEfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) E z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
    intro z
    constructor
    · intro hz
      apply (hfun z).mp
      exact zero_fold_le bad D.gates (fun g hg => (hmono g hg).1) 0 (List.ofFn z) D.output hz
    · rintro ⟨p, l, hpl, hp, hl⟩
      apply wires_mono (N + N) E hEmono
        (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) z _ E.output (hedge p l hpl)
      intro k hk
      rcases of_decide_eq_true hk with rfl | rfl
      · exact hp
      · exact hl
  have hEgood : Good E := by
    refine ⟨?_, hEmono, zero_back _ D bad hread, hEfun⟩
    exact (zero_length bad D.gates 0).trans hsizeEq
  have hlo : Nat.find hex ≤ ands E.gates := Nat.find_min' hex ⟨E, hEgood, rfl⟩
  have hlt : ands E.gates < ands D.gates :=
    ands_zero_lt bad D.gates 0 j hj (by simp [bad]) hand
  omega

end PEqualNP.Outside.L_meta_3451_aux.Prune
