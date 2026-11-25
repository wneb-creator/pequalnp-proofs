import Mathlib.Logic.Relation
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583.Normalization

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def evalGates (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma evalGates_length (gs : List Gate) (w : List Bool) :
    (evalGates gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [evalGates]
  | cons g gs ih =>
    simp only [evalGates, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

lemma evalGates_append (gs1 gs2 : List Gate) (w : List Bool) :
    evalGates (gs1 ++ gs2) w = evalGates gs2 (evalGates gs1 w) := by
  simp [evalGates, List.foldl_append]

lemma evalGates_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (evalGates gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [evalGates, List.foldl_cons] at ih ⊢
    have hk' : k < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length := by
      simp
      omega
    rw [ih _ hk']
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma evalGates_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (evalGates gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (evalGates (gs.take j) w).getD i false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp
  conv_lhs => rw [hsplit]
  rw [evalGates_append, evalGates_append]
  set w1 := evalGates (gs.take j) w
  have hw1 : w1.length = w.length + j := by
    rw [evalGates_length, List.length_take]
    omega
  have hlt : w.length + j < (evalGates [gs[j]] w1).length := by
    rw [evalGates_length, hw1]
    simp
  rw [evalGates_getD_lt _ _ _ hlt]
  simp only [evalGates, List.foldl_cons, List.foldl_nil]
  rw [← hw1]
  simp [List.getD_eq_getElem?_getD]

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma wires_getD_gate (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (x : List Bool) (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (n + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => (C.wires x).getD i false) := by
  change (evalGates C.gates x).getD (n + j) false = _
  have h1 := evalGates_getD_gate C.gates x j hj
  rw [hx] at h1
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi_lt : i < n + j := by
    have := hRB j hj i
    rw [gateAt_eq_getElem C j hj] at this
    exact this hi
  have hlen : (evalGates (C.gates.take j) x).length = n + j := by
    rw [evalGates_length, hx, List.length_take]
    omega
  have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  symm
  change (evalGates C.gates x).getD i false = (evalGates (C.gates.take j) x).getD i false
  conv_lhs => rw [hsplit, evalGates_append]
  exact evalGates_getD_lt (C.gates.drop j) (evalGates (C.gates.take j) x) i (by omega)

end PEqualNP.Outside.L_meta_2583.Normalization

namespace PEqualNP.Outside.L_meta_2583.PairClean

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Outside.L_meta_2583.Normalization

abbrev wire (n : ℕ) (C : Circuit) (w : ℕ) (x : Fin n → Bool) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wire_input (n : ℕ) (C : Circuit) (i : Fin n) (x : Fin n → Bool) :
    wire n C i.val x = x i := by
  have hi : i.val < (List.ofFn x).length := by simp
  change (evalGates C.gates (List.ofFn x)).getD i.val false = x i
  rw [evalGates_getD_lt _ _ _ hi, List.getD_eq_getElem _ _ hi]
  simp

lemma literal_on_independent (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C)
    (hClean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ u v : Fin n, ¬ G.Adj u v → gateVal n C j (pairInput u v) = false)
    (x : Fin n → Bool) (hx : graphFun G ∅ x = false) :
    ∀ w < n + C.gates.length, wire n C w x = true →
      ∃ u : Fin n, x u = true ∧ ∀ y : Fin n → Bool, y u = true → wire n C w y = true := by
  have hBad : ¬ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
    simpa [graphFun] using hx
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw htrue
    by_cases hInput : w < n
    · let u : Fin n := ⟨w, hInput⟩
      have hv (y : Fin n → Bool) : wire n C w y = y u := wire_input n C u y
      exact ⟨u, (hv x).symm.trans htrue, fun y hy => (hv y).trans hy⟩
    · let j := w - n
      have hwj : w = n + j := by omega
      have hj : j < C.gates.length := by omega
      have hg : gateAt C j = C.gates[j] := gateAt_eq_getElem C j hj
      obtain ⟨a, b, hInputs⟩ := List.length_eq_two.mp
        (hAO.2.2 (C.gates[j]) (List.getElem_mem hj))
      have ha : a < w := by
        have h := hAO.2.1 j hj a
        rw [hg, hInputs] at h
        exact (h (by simp)).trans_le (by omega)
      have hb : b < w := by
        have h := hAO.2.1 j hj b
        rw [hg, hInputs] at h
        exact (h (by simp)).trans_le (by omega)
      have hVal (y : Fin n → Bool) : wire n C (n + j) y =
          (C.gates[j]).op.eval [wire n C a y, wire n C b y] := by
        change (C.wires (List.ofFn y)).getD (n + j) false = _
        rw [wires_getD_gate n C hAO.2.1 (List.ofFn y) List.length_ofFn j hj, hInputs]
        rfl
      rw [hwj] at htrue ⊢
      rcases hAO.1 _ (List.getElem_mem hj) with hAnd | hOr
      · have ht : wire n C a x = true ∧ wire n C b x = true := by
          rw [hVal x, hAnd] at htrue
          simpa only [GateOp.eval, List.all_cons, List.all_nil, id_eq,
            Bool.and_true, Bool.and_eq_true] using htrue
        obtain ⟨u, hu, hU⟩ := ih a ha (by omega) ht.1
        obtain ⟨v, hv, hV⟩ := ih b hb (by omega) ht.2
        have huv : ¬ G.Adj u v := fun huv => hBad ⟨u, v, huv, hu, hv⟩
        have hFalse := hClean j hj (by simpa only [hg] using hAnd) u v huv
        have hPair : wire n C (n + j) (pairInput u v) = true := by
          rw [hVal _, hAnd]
          have hA := hU (pairInput u v) (by simp [pairInput])
          have hB := hV (pairInput u v) (by simp [pairInput])
          simpa only [GateOp.eval, List.all_cons, List.all_nil, id_eq,
            Bool.and_true, Bool.and_eq_true] using And.intro hA hB
        change wire n C (n + j) (pairInput u v) = false at hFalse
        rw [hPair] at hFalse
        cases hFalse
      · have ht : wire n C a x = true ∨ wire n C b x = true := by
          rw [hVal x, hOr] at htrue
          simpa only [GateOp.eval, List.any_cons, List.any_nil, id_eq,
            Bool.or_false, Bool.or_eq_true_iff] using htrue
        rcases ht with ht | ht
        · obtain ⟨u, hu, hU⟩ := ih a ha (by omega) ht
          refine ⟨u, hu, fun y hy => ?_⟩
          rw [hVal y, hOr]
          simpa only [GateOp.eval, List.any_cons, List.any_nil, id_eq,
            Bool.or_false, Bool.or_eq_true_iff] using
            (Or.inl (hU y hy) : wire n C a y = true ∨ wire n C b y = true)
        · obtain ⟨u, hu, hU⟩ := ih b hb (by omega) ht
          refine ⟨u, hu, fun y hy => ?_⟩
          rw [hVal y, hOr]
          simpa only [GateOp.eval, List.any_cons, List.any_nil, id_eq,
            Bool.or_false, Bool.or_eq_true_iff] using
            (Or.inr (hU y hy) : wire n C a y = true ∨ wire n C b y = true)

lemma pair_clean_implies_below (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C)
    (hClean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ u v : Fin n, ¬ G.Adj u v → gateVal n C j (pairInput u v) = false) :
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j := by
  intro j hj hAnd x htrue
  by_cases hFx : graphFun G ∅ x = true
  · exact hFx
  have hx : graphFun G ∅ x = false := Bool.eq_false_of_not_eq_true hFx
  obtain ⟨u, _, hU⟩ := literal_on_independent n G C hAO hClean x hx
    (n + j) (by omega) htrue
  have hPair := hU (pairInput u u) (by simp [pairInput])
  have hFalse := hClean j hj hAnd u u (by simp)
  change wire n C (n + j) (pairInput u u) = false at hFalse
  rw [hPair] at hFalse
  cases hFalse

lemma pair_clean_iff_all_below (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) :
    (∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ∀ u v : Fin n, ¬ G.Adj u v → gateVal n C j (pairInput u v) = false) ↔
    (∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) := by
  constructor
  · exact pair_clean_implies_below n G C hAO
  · intro hBelow j hj hAnd u v huv
    by_contra hFalse
    have hTrue := Bool.eq_true_of_not_eq_false hFalse
    have hF := hBelow j hj hAnd (pairInput u v) hTrue
    have hvu : ¬ G.Adj v u := fun h => huv (G.symm.symm v u h)
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq, pairInput] at hF
    obtain ⟨a, b, hab, ha, hb⟩ := hF
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl <;> simp_all

end PEqualNP.Outside.L_meta_2583.PairClean
