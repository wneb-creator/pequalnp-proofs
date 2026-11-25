namespace PEqualNP.Outside.L_meta_3451_aux.Bridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3451_aux.Padding

def inputMap (N : ℕ) : Fin ((N + 1) + (N + 1)) → Option (Fin (N + N)) :=
  Fin.addCases
    (fun p : Fin (N + 1) => if h : p.val < N then some (Fin.castAdd N ⟨p.val, h⟩) else none)
    (fun l : Fin (N + 1) => if h : l.val < N then some (Fin.natAdd N ⟨l.val, h⟩) else none)

def embedInput (N : ℕ) : Fin (N + N) → Fin ((N + 1) + (N + 1)) :=
  Fin.addCases (fun p => Fin.castAdd (N + 1) p.castSucc)
    (fun l => Fin.natAdd (N + 1) l.castSucc)

lemma inputMap_embed (N : ℕ) (i : Fin (N + N)) :
    inputMap N (embedInput N i) = some i := by
  refine Fin.addCases (fun p => ?_) (fun l => ?_) i
  · rw [embedInput, Fin.addCases_left, inputMap, Fin.addCases_left]
    simp only [Fin.val_castSucc]
    rw [dite_eq_left p.isLt]
  · rw [embedInput, Fin.addCases_right, inputMap, Fin.addCases_right]
    simp only [Fin.val_castSucc]
    rw [dite_eq_left l.isLt]

lemma inputMap_some (N : ℕ) (k : Fin ((N + 1) + (N + 1))) (i : Fin (N + N))
    (h : inputMap N k = some i) : embedInput N i = k := by
  revert h
  refine Fin.addCases (fun p => ?_) (fun l => ?_) k
  · intro h
    simp only [inputMap, Fin.addCases_left] at h
    split_ifs at h with hp
    cases Option.some.inj h
    rw [embedInput, Fin.addCases_left]
    rfl
  · intro h
    simp only [inputMap, Fin.addCases_right] at h
    split_ifs at h with hl
    cases Option.some.inj h
    rw [embedInput, Fin.addCases_right]
    rfl

lemma inputMap_iff (N : ℕ) (k : Fin ((N + 1) + (N + 1))) (i : Fin (N + N)) :
    inputMap N k = some i ↔ k = embedInput N i := by
  constructor
  · exact fun h => (inputMap_some N k i h).symm
  · rintro rfl
    exact inputMap_embed N i

lemma lifted_singleton (N : ℕ) (i : Fin (N + N)) :
    PEqualNP.Outside.L_meta_3451_aux.Restriction.input (inputMap N) (fun k => decide (k = i)) =
      fun k => decide (k = embedInput N i) := by
  funext k
  unfold PEqualNP.Outside.L_meta_3451_aux.Restriction.input
  cases h : inputMap N k with
  | none =>
    have hn : k ≠ embedInput N i := by
      intro he
      have := (inputMap_iff N k i).mpr he
      rw [h] at this
      cases this
    simp [hn]
  | some j =>
    simp only [Option.map_some, Option.getD_some]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    constructor
    · intro he
      subst j
      exact (inputMap_iff N k i).mp h
    · intro he
      have hh := (inputMap_iff N k i).mpr he
      rw [h] at hh
      exact Option.some.inj hh

lemma lifted_pair (N : ℕ) (i j : Fin (N + N)) :
    PEqualNP.Outside.L_meta_3451_aux.Restriction.input (inputMap N)
      (fun k => decide (k = i ∨ k = j)) =
      fun k => decide (k = embedInput N i ∨ k = embedInput N j) := by
  funext k
  have hi := congrFun (lifted_singleton N i) k
  have hj := congrFun (lifted_singleton N j) k
  unfold PEqualNP.Outside.L_meta_3451_aux.Restriction.input at hi hj ⊢
  cases h : inputMap N k <;> simp_all

open PEqualNP.Outside.L_meta_3451_aux

lemma computes_restrict (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hC : Monotone2 C)
    (sem : ∀ z : Fin ((N + 1) + (N + 1)) → Bool,
      circuitFun ((N + 1) + (N + 1)) C z = true ↔
      ∃ p l : Fin (N + 1), padIncidence N I p l ∧
        z (Fin.castAdd (N + 1) p) = true ∧ z (Fin.natAdd (N + 1) l) = true) :
    ∀ z : Fin (N + N) → Bool,
      circuitFun (N + N) (Restriction.circuit (inputMap N) C) z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  intro z
  rw [Restriction.eval (inputMap N) C hC z, sem]
  constructor
  · rintro ⟨p, l, ⟨hp, hl, hi⟩, hz, hw⟩
    refine ⟨⟨p.val, hp⟩, ⟨l.val, hl⟩, hi, ?_, ?_⟩
    · simpa only [Restriction.input, inputMap, Fin.addCases_left, dite_eq_left hp,
        Option.map_some, Option.getD_some] using hz
    · simpa only [Restriction.input, inputMap, Fin.addCases_right, dite_eq_left hl,
        Option.map_some, Option.getD_some] using hw
  · rintro ⟨p, l, hi, hp, hl⟩
    refine ⟨p.castSucc, l.castSucc, ⟨p.isLt, l.isLt, hi⟩, ?_, ?_⟩
    · simpa only [Restriction.input, inputMap, Fin.addCases_left, Fin.val_castSucc,
        dite_eq_left p.isLt, Option.map_some, Option.getD_some] using hp
    · simpa only [Restriction.input, inputMap, Fin.addCases_right, Fin.val_castSucc,
        dite_eq_left l.isLt, Option.map_some, Option.getD_some] using hl

def PairNormalizes : Prop :=
  ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
    (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
    Monotone2 C → NestedCover.ReadsBack (N + N) C →
    (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
    ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        ∀ p l : Fin N, ¬ I p l →
          (D.wires (List.ofFn (fun k : Fin (N + N) =>
            decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD
              (N + N + j) false = false)

lemma full_of_pair (hyp : PairNormalizes) :
    ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      Monotone2 C → NestedCover.ReadsBack (N + N) C →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
        (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
        (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
          ∀ p l : Fin N, ¬ I p l →
            (D.wires (List.ofFn (fun k : Fin (N + N) =>
              decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD
                (N + N + j) false = false) ∧
        (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
          (∀ p : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
            decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
          ∀ l : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) =>
            decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  classical
  intro N I _ C hfour hmono hback sem
  obtain ⟨D, dm, db, ds, de, dp⟩ := hyp (N + 1) (padIncidence N I) (padCircuit N C)
    (noFourCycle_pad N I hfour) (monotone_pad N C hmono) (readsBack_pad N C hback)
    (computes_pad N I C sem)
  have dz := singleton_clean_of_nonedge (N + 1) (padIncidence N I) D dm
    (point_misses N I) (line_misses N I) dp
  refine ⟨Restriction.circuit (inputMap N) D, Restriction.mono _ D dm,
    Restriction.readsBack _ D db, ?_, computes_restrict N I D dm de, ?_, ?_⟩
  · rw [Restriction.size]
    simpa only [size_pad] using ds
  · intro j hj hand p l hn
    change PEqualNP.EdgeOwnership.gateVal (N + N)
      (Restriction.circuit (inputMap N) D) j
      (fun k => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)) = false
    rw [Restriction.gate_value_at _ D dm, lifted_pair]
    simp only [embedInput, Fin.addCases_left, Fin.addCases_right]
    apply dp j (by simpa only [Restriction.circuit, List.length_map] using hj)
      (Restriction.and_origin _ D j hand) p.castSucc l.castSucc
    rintro ⟨_, _, hi⟩
    exact hn hi
  · intro j hj hand
    have hj' : j < D.gates.length := by
      simpa only [Restriction.circuit, List.length_map] using hj
    have hand' := Restriction.and_origin _ D j hand
    constructor
    · intro p
      change PEqualNP.EdgeOwnership.gateVal (N + N)
        (Restriction.circuit (inputMap N) D) j
        (fun k => decide (k = Fin.castAdd N p)) = false
      rw [Restriction.gate_value_at _ D dm, lifted_singleton]
      simp only [embedInput, Fin.addCases_left]
      exact (dz j hj' hand').1 p.castSucc
    · intro l
      change PEqualNP.EdgeOwnership.gateVal (N + N)
        (Restriction.circuit (inputMap N) D) j
        (fun k => decide (k = Fin.natAdd N l)) = false
      rw [Restriction.gate_value_at _ D dm, lifted_singleton]
      simp only [embedInput, Fin.addCases_right]
      exact (dz j hj' hand').2 l.castSucc

lemma pair_iff_full : PairNormalizes ↔ (∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) → PEqualNP.MetaComplexity.Monotone2 C → PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧ (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔ ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ p0 l0 : Fin N, ¬ I p0 l0 → (D.wires (List.ofFn (fun ke : Fin (N + N) => decide (ke = Fin.castAdd N p0 ∨ ke = Fin.natAdd N l0)))).getD (N + N + j) false = false) ∧ (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ p : Fin N, (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧ ∀ l : Fin N, (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false)) := by
  constructor
  · exact full_of_pair
  · intro h N I _ C hfour hm hb hs
    obtain ⟨D, dm, db, ds, de, dp, _⟩ := h N I C hfour hm hb hs
    exact ⟨D, dm, db, ds, de, dp⟩

end PEqualNP.Outside.L_meta_3451_aux.Bridge
