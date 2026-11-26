import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 5000000 in
theorem PEqualNP.Outside.R_meta_6028_3
    (minorBound :
      ∀ (D : Circuit) (a b : Fin 9), (a,b) ∈ ([(0,2),(0,3),(0,6),(4,6)] : List (Fin 9 × Fin 9)) →
        FanInTwo D → (∀ x : Fin 9 → Bool, (D.wires (List.ofFn x)).getD 9 false = (x a && x b)) →
        circuitFun 9 D = (fun x : Fin 9 → Bool => (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)) → 16 ≤ D.size)
    (eliminate :
      let edge := fun x : Fin 10 → Bool =>
        ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any
          (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
      let wires := fun (p : Fin 10 → Fin 10) (x : Fin 10 → Bool) =>
        List.ofFn (x ∘ p) ++ [x 0 && x 2]
      ∀ (C : Circuit) (p : Fin 10 → Fin 10), FanInTwo C → C.size ≤ 18 →
        (∃ (g : Gate) (gs : List Gate), C.gates = g :: gs ∧ g.op = GateOp.or) →
        (∀ x, C.eval (wires p x)=edge x) →
        ∃ (v : Fin 10) (D : Circuit), FanInTwo D ∧ D.size+4 ≤ C.size ∧
          ∀ x, x v=false → D.eval (wires p x)=C.eval (wires p x)) :
    ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 : Fin (10 : ℕ) → Fin (10 : ℕ)), PEqualNP.MetaComplexity.FanInTwo x1 → x1.size ≤ (18 : ℕ) → (∃ (x5 : PEqualNP.CircuitLowerBounds.Gate) (x6 : List PEqualNP.CircuitLowerBounds.Gate), x1.gates = x5 :: x6 ∧ x5.op = PEqualNP.CircuitLowerBounds.GateOp.or) → ∃ (x6 : Fin (10 : ℕ) → Bool), x1.eval (List.ofFn (x6 ∘ x2) ++ [x6 (0 : Fin (10 : ℕ)) && x6 (2 : Fin (10 : ℕ))]) ≠ (fun (x7 : Fin (10 : ℕ) → Bool) => x7 (0 : Fin (10 : ℕ)) && x7 (1 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (2 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (3 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (4 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (0 : Fin (10 : ℕ)) || x7 (0 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ)) || x7 (1 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (2 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (3 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (4 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (5 : Fin (10 : ℕ)) && x7 (7 : Fin (10 : ℕ)) || x7 (7 : Fin (10 : ℕ)) && x7 (9 : Fin (10 : ℕ)) || x7 (9 : Fin (10 : ℕ)) && x7 (6 : Fin (10 : ℕ)) || x7 (6 : Fin (10 : ℕ)) && x7 (8 : Fin (10 : ℕ)) || x7 (8 : Fin (10 : ℕ)) && x7 (5 : Fin (10 : ℕ))) x6 := by

  let rewire (rho : Nat → Nat) (g : Gate) : Gate := ⟨g.op,g.inputs.map rho⟩

  have rewire_fan {C : Circuit} (ok : FanInTwo C) (rho : Nat → Nat) (out : Nat) :
      FanInTwo ⟨C.gates.map (rewire rho),out⟩ := by
    intro g h
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp h
    exact ⟨(ok u hu).1,by simpa [rewire] using (ok u hu).2⟩

  have run {n m B : Nat} (rho : Nat → Nat)
      (early : ∀ i, i < n → rho i < m ∨ B ≤ rho i) (late : ∀ i, n ≤ i → rho i = m+(i-n))
      (gs : List Gate) (u w : List Bool) (base : n ≤ u.length) (lens : u.length + m = w.length + n)
      (past : w.length + gs.length ≤ B) (agree : ∀ i, w.getD (rho i) false = u.getD i false) :
      ∀ i, ((⟨gs.map (rewire rho),0⟩ : Circuit).wires w).getD (rho i) false =
        ((⟨gs,0⟩ : Circuit).wires u).getD i false := by
    induction gs generalizing u w with
    | nil => exact agree
    | cons g gs ih =>
      let val := g.op.eval (g.inputs.map fun i => u.getD i false)
      have step : (rewire rho g).op.eval ((rewire rho g).inputs.map fun i => w.getD i false) = val := by
        simp only [rewire,List.map_map,Function.comp_def,agree,val]
      change ∀ i, ((⟨gs.map (rewire rho),0⟩ : Circuit).wires (w++[_])).getD (rho i) false =
        ((⟨gs,0⟩ : Circuit).wires (u++[val])).getD i false
      rw [step]
      simp only [List.length_cons] at past
      apply ih _ _ (by simp; omega) (by simp; omega) (by simp; omega)
      intro i
      by_cases hi : i < u.length
      · rw [List.getD_append _ _ _ _ hi,←agree i]
        by_cases hh : rho i < w.length
        · exact List.getD_append _ _ _ _ hh
        · have hr : B ≤ rho i := by
            by_cases hn : i < n
            · rcases early i hn with h|h <;> omega
            · rw [late i (by omega)] at hh; omega
          rw [List.getD_eq_default (w++[val]) false (by simp; omega),
              List.getD_eq_default w false (by omega)]
      · have eq := late i (by omega)
        rw [List.getD_append_right _ _ _ _ (by omega),List.getD_append_right _ _ _ _ (by omega)]
        congr 1 <;> omega

  have keep (gs : List Gate) (w : List Bool) (i : Nat) (h : i < w.length) :
      ((⟨gs,0⟩ : Circuit).wires w).getD i false = w.getD i false := by
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      change ((⟨gs,0⟩ : Circuit).wires (w++[_])).getD i false = _
      rw [ih _ (by simp; omega),List.getD_append _ _ _ _ h]

  let graph (x : Fin 10 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
  let minor (x : Fin 9 → Bool) := (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)
  -- Row v sends the deleted vertex to 9. Each row preserves all fifteen edges.
  let labels : Fin 10 → Fin 10 → Fin 10 := ![![9, 4, 0, 1, 6, 7, 3, 5, 2, 8], ![4, 9, 6, 1, 0, 3, 7, 8, 2, 5], ![0, 4, 9, 6, 1, 5, 3, 7, 8, 2], ![0, 1, 6, 9, 4, 5, 2, 8, 7, 3], ![6, 1, 0, 4, 9, 8, 2, 5, 3, 7], ![6, 1, 0, 5, 8, 9, 2, 4, 7, 3], ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6], ![0, 1, 6, 8, 5, 4, 2, 9, 3, 7], ![0, 1, 2, 7, 5, 4, 6, 3, 9, 8], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]
  let pair : Fin 10 → Fin 9 × Fin 9 := ![(0,2), (4,6), (0,2), (0,6), (0,6), (0,6), (0,3), (0,6), (0,2), (0,2)]
  let killed (v : Fin 10) := v==0 || v==2
  let lift (v : Fin 10) (x : Fin 9 → Bool) (i : Fin 10) : Bool :=
    (List.ofFn x).getD (labels v i).val false

  have deleted : ∀ (v : Fin 10) (x : Fin 9 → Bool), lift v x v=false := by
    intro v x
    fin_cases v <;> rfl

  have seed_image (v : Fin 10) (x : Fin 9 → Bool) :
      (lift v x 0 && lift v x 2) =
        (if killed v then false else x (pair v).1 && x (pair v).2) := by
    fin_cases v
    · change (false && x 0) = false
      simp [Bool.and_comm]
    · change (x 4 && x 6) = (x 4 && x 6)
      simp [Bool.and_comm]
    · change (x 0 && false) = false
      simp [Bool.and_comm]
    · change (x 0 && x 6) = (x 0 && x 6)
      simp [Bool.and_comm]
    · change (x 6 && x 0) = (x 0 && x 6)
      simp [Bool.and_comm]
    · change (x 6 && x 0) = (x 0 && x 6)
      simp [Bool.and_comm]
    · change (x 0 && x 3) = (x 0 && x 3)
      simp [Bool.and_comm]
    · change (x 0 && x 6) = (x 0 && x 6)
      simp [Bool.and_comm]
    · change (x 0 && x 2) = (x 0 && x 2)
      simp [Bool.and_comm]
    · change (x 0 && x 2) = (x 0 && x 2)
      simp [Bool.and_comm]

  have graph_image (v : Fin 10) (x : Fin 9 → Bool) : graph (lift v x)=minor x := by
    fin_cases v
    · change ((false && x 4) || (x 4 && x 0) || (x 0 && x 1) || (x 1 && x 6) || (x 6 && false) || (false && x 7) || (x 4 && x 3) || (x 0 && x 5) || (x 1 && x 2) || (x 6 && x 8) || (x 7 && x 5) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 2) || (x 2 && x 7)) = minor x
      simp only [minor,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false] <;> ac_rfl
    · change ((x 4 && false) || (false && x 6) || (x 6 && x 1) || (x 1 && x 0) || (x 0 && x 4) || (x 4 && x 3) || (false && x 7) || (x 6 && x 8) || (x 1 && x 2) || (x 0 && x 5) || (x 3 && x 8) || (x 8 && x 5) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 3)) = minor x
      simp only [minor,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false] <;> ac_rfl
    · change ((x 0 && x 4) || (x 4 && false) || (false && x 6) || (x 6 && x 1) || (x 1 && x 0) || (x 0 && x 5) || (x 4 && x 3) || (false && x 7) || (x 6 && x 8) || (x 1 && x 2) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 3) || (x 3 && x 8) || (x 8 && x 5)) = minor x
      simp only [minor,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false] <;> ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 6) || (x 6 && false) || (false && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 2) || (x 6 && x 8) || (false && x 7) || (x 4 && x 3) || (x 5 && x 8) || (x 8 && x 3) || (x 3 && x 2) || (x 2 && x 7) || (x 7 && x 5)) = minor x
      simp only [minor,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false] <;> ac_rfl
    · change ((x 6 && x 1) || (x 1 && x 0) || (x 0 && x 4) || (x 4 && false) || (false && x 6) || (x 6 && x 8) || (x 1 && x 2) || (x 0 && x 5) || (x 4 && x 3) || (false && x 7) || (x 8 && x 5) || (x 5 && x 7) || (x 7 && x 2) || (x 2 && x 3) || (x 3 && x 8)) = minor x
      simp only [minor,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false] <;> ac_rfl
    · change ((x 6 && x 1) || (x 1 && x 0) || (x 0 && x 5) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && false) || (x 1 && x 2) || (x 0 && x 4) || (x 5 && x 7) || (x 8 && x 3) || (false && x 4) || (x 4 && x 3) || (x 3 && x 2) || (x 2 && x 7) || (x 7 && false)) = minor x
      simp only [minor,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false] <;> ac_rfl
    · change ((x 0 && x 4) || (x 4 && x 3) || (x 3 && x 2) || (x 2 && x 1) || (x 1 && x 0) || (x 0 && x 5) || (x 4 && false) || (x 3 && x 8) || (x 2 && x 7) || (x 1 && x 6) || (x 5 && x 8) || (x 8 && x 6) || (x 6 && false) || (false && x 7) || (x 7 && x 5)) = minor x
      simp only [minor,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false] <;> ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 6) || (x 6 && x 8) || (x 8 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 1 && x 2) || (x 6 && false) || (x 8 && x 3) || (x 5 && x 7) || (x 4 && false) || (false && x 7) || (x 7 && x 2) || (x 2 && x 3) || (x 3 && x 4)) = minor x
      simp only [minor,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false] <;> ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 7) || (x 7 && x 5) || (x 5 && x 0) || (x 0 && x 4) || (x 1 && x 6) || (x 2 && x 3) || (x 7 && false) || (x 5 && x 8) || (x 4 && x 3) || (x 3 && x 8) || (x 8 && x 6) || (x 6 && false) || (false && x 4)) = minor x
      simp only [minor,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false] <;> ac_rfl
    · change ((x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && false) || (x 5 && x 7) || (x 7 && false) || (false && x 6) || (x 6 && x 8) || (x 8 && x 5)) = minor x
      simp only [minor,Bool.false_and,Bool.and_false,Bool.false_or,Bool.or_false] <;> ac_rfl

  have pair_cases (v : Fin 10) : pair v=(0,2) ∨ pair v=(0,3) ∨ pair v=(0,6) ∨ pair v=(4,6) := by
    revert v
    unfold pair
    decide +kernel

  let seed (p : Fin 10 → Fin 10) (x : Fin 10 → Bool) := List.ofFn (x ∘ p) ++ [x 0 && x 2]
  let front (v : Fin 10) : Gate := ⟨.and,[(pair v).1.val,(pair v).2.val]⟩
  let pin (v : Fin 10) (x : Fin 9 → Bool) := x (pair v).1 && x (pair v).2
  -- References to a deleted input point beyond even the last wire.
  let B (C : Circuit) := 10 + C.size
  let addr (C : Circuit) (v : Fin 10) (p : Fin 10 → Fin 10) (i : Nat) :=
    if h : i < 10 then
      let j := (labels v (p ⟨i,h⟩)).val
      if j < 9 then j else B C
    else if i=10 then (if killed v then B C else 9) else 10+(i-11)

  have read_input {n} (x : Fin n → Bool) (i : Fin n) :
      (List.ofFn x).getD i.val false=x i := by
    simp [List.getD_eq_getElem?_getD,i.isLt]

  have first (v : Fin 10) (x : Fin 9 → Bool) :
      (front v).op.eval ((front v).inputs.map fun i => (List.ofFn x).getD i false)=pin v x := by
    change ((List.ofFn x).getD (pair v).1.val false && ((List.ofFn x).getD (pair v).2.val false && true)) = _
    rw [read_input,read_input,Bool.and_true]

  have addr_early (C : Circuit) (v : Fin 10) (p : Fin 10 → Fin 10) (i : Nat) (hi : i < 11) :
      addr C v p i < 10 ∨ B C ≤ addr C v p i := by
    by_cases h : i < 10
    · simp only [addr,dite_eq_left h]
      split <;> omega
    · have eq : i=10 := by omega
      subst i
      change (if killed v then B C else 9) < 10 ∨ B C ≤ (if killed v then B C else 9)
      cases killed v <;> simp

  have initial (C : Circuit) (v : Fin 10) (p : Fin 10 → Fin 10) (x : Fin 9 → Bool) (i : Nat) :
      (List.ofFn x ++ [pin v x]).getD (addr C v p i) false=(seed p (lift v x)).getD i false := by
    let w := List.ofFn x ++ [pin v x]
    have big : w.getD (B C) false = false :=
      List.getD_eq_default _ _ (by simp [w,B])
    by_cases h : i < 10
    · let j := labels v (p ⟨i,h⟩)
      have orig : (seed p (lift v x)).getD i false = lift v x (p ⟨i,h⟩) := by
        unfold seed
        rw [List.getD_append _ _ _ _ (by simpa using h)]
        exact read_input _ ⟨i,h⟩
      rw [orig]
      simp only [addr,dite_eq_left h]
      change w.getD (if j.val < 9 then j.val else B C) false = (List.ofFn x).getD j.val false
      by_cases hj : j.val < 9
      · rw [ite_eq_left hj,List.getD_append _ _ _ _ (by simpa using hj)]
      · rw [ite_eq_right hj,big,List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hj)]
    · by_cases eq : i=10
      · subst i
        have extra : (seed p (lift v x)).getD 10 false=(lift v x 0 && lift v x 2) := by
          unfold seed
          rw [List.getD_append_right _ _ _ _ (by simp)]
          simp
        rw [extra,seed_image]
        change w.getD (if killed v then B C else 9) false=_
        split
        · exact big
        · rw [List.getD_append_right _ _ _ _ (by simp)]
          simp [pin]
      · have high : 11 ≤ i := by omega
        rw [show addr C v p i=10+(i-11) by simp [addr,h,eq],
            List.getD_eq_default _ _ (by simp <;> omega),List.getD_eq_default _ _ (by simp [seed] <;> omega)]

  let compiled (C : Circuit) (p : Fin 10 → Fin 10) (v : Fin 10) : Circuit :=
    ⟨front v :: C.gates.map (rewire (addr C v p)),addr C v p C.output⟩

  -- Prepending the representative AND increases the size by exactly one.
  have slice_compile (C : Circuit) (p : Fin 10 → Fin 10) (v : Fin 10) (hf : FanInTwo C)
      (correct : ∀ x, x v=false → C.eval (seed p x)=graph x) :
      let D := compiled C p v
      FanInTwo D ∧ D.size=C.size+1 ∧
      (∀ x : Fin 9 → Bool,(D.wires (List.ofFn x)).getD 9 false=pin v x) ∧ circuitFun 9 D=minor := by
    dsimp only
    refine ⟨?_,by change (_ :: C.gates.map _).length = C.gates.length+1; simp,?_,?_⟩
    · intro g hg
      change g∈front v :: _ at hg
      rcases List.mem_cons.mp hg with rfl|h
      · simp [front]
      · exact rewire_fan hf _ 0 g h
    · intro x
      change ((⟨C.gates.map _,0⟩ : Circuit).wires (List.ofFn x ++ [_])).getD 9 false=_
      rw [first,keep _ _ _ (by simp),List.getD_append_right _ _ _ _ (by simp)]
      simp
    · funext x
      change ((⟨C.gates.map _,0⟩ : Circuit).wires (List.ofFn x ++ [_])).getD (addr C v p C.output) false=_
      rw [first]
      have sim := run (addr C v p) (addr_early C v p)
        (fun i (h : 11 ≤ i) => show addr C v p i=10+(i-11) by
          simp [addr,show ¬ i < 10 by omega,show i ≠ 10 by omega])
        C.gates (seed p (lift v x)) (List.ofFn x ++ [pin v x]) (by simp [seed]) (by simp [seed])
        (by change (List.ofFn x ++ [pin v x]).length + C.gates.length ≤ 10+C.gates.length; simp) (initial C v p x) C.output
      exact sim.trans ((correct _ (deleted v x)).trans (graph_image v x))
  intro C p legal budget hor
  by_contra! correct
  let edge := fun x : Fin 10 → Bool =>
    ([1,12,23,34,40,5,16,27,38,49,57,79,96,68,85] : List Nat).any
      (fun e => x (Fin.ofNat 10 (e / 10)) && x (Fin.ofNat 10 (e % 10)))
  have eq (x : Fin 10 → Bool) : graph x = edge x := by
    simp only [graph,edge,List.any_cons,List.any_nil,Bool.or_false,Bool.or_assoc]
    rfl
  have full (x : Fin 10 → Bool) := (correct x).trans (eq x)
  obtain ⟨v,D,hD,drop,agree⟩ := eliminate C p legal budget hor full
  obtain ⟨fan,sz,fst,out⟩ := slice_compile D p v hD (fun x hx => (agree x hx).trans (correct x))
  have member : pair v ∈ ([(0,2),(0,3),(0,6),(4,6)] : List (Fin 9 × Fin 9)) := by
    simpa only [List.mem_cons,List.not_mem_nil,or_false] using pair_cases v
  have lower := minorBound (compiled D p v) (pair v).1 (pair v).2 member fan fst out
  omega
