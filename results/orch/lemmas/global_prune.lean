import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3451_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def wireLE (a b : List Bool) : Prop :=
  ∀ i, a.getD i false = true → b.getD i false = true

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

lemma fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length → wireLE a b →
      wireLE (gs.foldl wireStep a) (gs.foldl wireStep b) := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [wireStep, hl]
    · intro i hi
      unfold wireStep at hi ⊢
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [← hl]
        by_cases he : i - a.length = 0
        · rw [he] at hi ⊢
          simp only [List.getD_cons_zero] at hi ⊢
          exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi
          simp at hi

lemma wires_mono (n : ℕ) (C : Circuit) (hC : Monotone2 C)
    (a b : Fin n → Bool) (h : ∀ i, a i = true → b i = true) :
    wireLE (C.wires (List.ofFn a)) (C.wires (List.ofFn b)) := by
  apply fold_mono C.gates (fun g hg => by simpa using (hC g hg).1)
  · simp
  · intro i hi
    by_cases hin : i < n
    · simpa [List.getD_eq_getElem?_getD, hin] using
        h ⟨i, hin⟩ (by simpa [List.getD_eq_getElem?_getD, hin] using hi)
    · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hin)] at hi
      cases hi

end PEqualNP.Outside.L_meta_3451_aux

namespace PEqualNP.Outside.L_meta_3451_aux.Prune

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def zeroGate (b : Bool) (g : Gate) : Gate := if b then ⟨.or, []⟩ else g

def zeroGates (bad : ℕ → Bool) : ℕ → List Gate → List Gate
  | _, [] => []
  | j, g :: gs => zeroGate (bad j) g :: zeroGates bad (j + 1) gs

def zeroCircuit (C : Circuit) (bad : ℕ → Bool) : Circuit :=
  ⟨zeroGates bad 0 C.gates, C.output⟩

lemma zero_length (bad : ℕ → Bool) (gs : List Gate) (j : ℕ) :
    (zeroGates bad j gs).length = gs.length := by
  induction gs generalizing j with
  | nil => rfl
  | cons g gs ih => simp only [zeroGates, List.length_cons, ih]

lemma zero_getD (bad : ℕ → Bool) (gs : List Gate) (j r : ℕ) (hr : r < gs.length) :
    (zeroGates bad j gs).getD r ⟨.or, []⟩ =
      zeroGate (bad (j + r)) (gs.getD r ⟨.or, []⟩) := by
  induction gs generalizing j r with
  | nil => simp at hr
  | cons g gs ih =>
    cases r with
    | zero => simp only [zeroGates, List.getD_cons_zero, Nat.add_zero]
    | succ r =>
      simp only [List.length_cons, Nat.succ_lt_succ_iff] at hr
      simpa only [zeroGates, List.getD_cons_succ, Nat.succ_eq_add_one,
        Nat.add_assoc, Nat.add_comm 1] using ih (j + 1) r hr

lemma step_zero_le (b : Bool) (g : Gate) (w : List Bool) :
    wireLE (wireStep w (zeroGate b g)) (wireStep w g) := by
  intro i hi
  cases b with
  | false => exact hi
  | true =>
    change (w ++ [false]).getD i false = true at hi
    change (w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]).getD i false = true
    by_cases hlt : i < w.length
    · rw [List.getD_append _ _ _ _ hlt] at hi ⊢
      exact hi
    · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
      have hz : ([false] : List Bool).getD (i - w.length) false = false := by
        cases i - w.length <;> rfl
      rw [hz] at hi
      cases hi

lemma zero_fold_le (bad : ℕ → Bool) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) (j : ℕ) (w : List Bool) :
    wireLE ((zeroGates bad j gs).foldl wireStep w) (gs.foldl wireStep w) := by
  induction gs generalizing j w with
  | nil => intro i hi; exact hi
  | cons g gs ih =>
    simp only [zeroGates, List.foldl_cons]
    intro i hi
    have htail := fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
    have hz := ih htail (j + 1) (wireStep w (zeroGate (bad j) g)) i hi
    exact fold_mono gs htail _ _ (by simp [wireStep]) (step_zero_le _ _ _) i hz

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl wireStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [wireStep]
    omega

lemma fold_early (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl wireStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (wireStep w g) (by simp [wireStep]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma zero_fold_eq (bad : ℕ → Bool) (gs : List Gate) (j : ℕ) (w : List Bool)
    (hz : ∀ r, r < gs.length → bad (j + r) = true →
      (gs.foldl wireStep w).getD (w.length + r) false = false) :
    (zeroGates bad j gs).foldl wireStep w = gs.foldl wireStep w := by
  induction gs generalizing j w with
  | nil => rfl
  | cons g gs ih =>
    have hs : wireStep w (zeroGate (bad j) g) = wireStep w g := by
      cases hb : bad j with
      | false => rfl
      | true =>
        have hzero := hz 0 (by simp) (by simpa using hb)
        simp only [List.foldl_cons, Nat.add_zero] at hzero
        rw [fold_early gs (wireStep w g) w.length (by simp [wireStep])] at hzero
        have hv : g.op.eval (g.inputs.map fun i => w.getD i false) = false := by
          simpa [wireStep, List.getD_eq_getElem?_getD] using hzero
        change w ++ [false] = w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
        rw [hv]
    simp only [zeroGates, List.foldl_cons, hs]
    apply ih
    intro r hr hb
    have hzero := hz (r + 1) (by simpa using Nat.succ_lt_succ hr)
      (by simpa [Nat.add_assoc, Nat.add_comm 1] using hb)
    simpa [List.foldl_cons, wireStep, Nat.add_assoc, Nat.add_comm 1] using hzero

lemma zero_monotone (C : Circuit) (bad : ℕ → Bool) (hC : Monotone2 C) :
    Monotone2 (zeroCircuit C bad) := by
  intro g hg
  have hm : ∀ gs : List Gate, (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2) → ∀ j, ∀ g ∈ zeroGates bad j gs,
        (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro gs
    induction gs with
    | nil => simp [zeroGates]
    | cons g gs ih =>
      intro h j g' hg'
      simp only [zeroGates, List.mem_cons] at hg'
      rcases hg' with rfl | hg'
      · cases hb : bad j with
        | false => simpa [zeroGate] using h g List.mem_cons_self
        | true => simp [zeroGate]
      · exact ih (fun g'' hg'' => h g'' (List.mem_cons_of_mem _ hg'')) (j + 1) g' hg'
  exact hm C.gates hC 0 g hg

lemma zero_back (n : ℕ) (C : Circuit) (bad : ℕ → Bool) (hC : ReadsBack n C) :
    ReadsBack n (zeroCircuit C bad) := by
  intro j hj i hi
  have hj' : j < C.gates.length := by simpa only [zeroCircuit, zero_length] using hj
  have he : gateAt (zeroCircuit C bad) j = zeroGate (bad j) (gateAt C j) := by
    simpa only [zeroCircuit, gateAt, Nat.zero_add] using zero_getD bad C.gates 0 j hj'
  rw [he] at hi
  cases hb : bad j with
  | false => exact hC j hj' i (by simpa [zeroGate, hb] using hi)
  | true => simp [zeroGate, hb] at hi

lemma edge_active_normalization (N : ℕ) (I : Fin N → Fin N → Prop) (C : Circuit)
    (hC : Monotone2 C) (hback : ReadsBack (N + N) C)
    (hsem : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ D : Circuit, D.size = C.size ∧ Monotone2 D ∧ ReadsBack (N + N) D ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j : ℕ, j < D.gates.length → (gateAt D j).op = GateOp.and →
        ∃ p l : Fin N, I p l ∧ (D.wires (List.ofFn (fun k : Fin (N + N) =>
          decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD (N + N + j) false = true) := by
  classical
  let pair := fun p l : Fin N => fun k : Fin (N + N) =>
    decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)
  let bad := fun j : ℕ => decide ((gateAt C j).op = GateOp.and ∧
    ∀ p l : Fin N, I p l → (C.wires (List.ofFn (pair p l))).getD (N + N + j) false = false)
  let D := zeroCircuit C bad
  have hm : Monotone2 D := zero_monotone C bad hC
  have heq : ∀ p l : Fin N, I p l → D.wires (List.ofFn (pair p l)) =
      C.wires (List.ofFn (pair p l)) := by
    intro p l hpl
    apply zero_fold_eq bad C.gates 0 (List.ofFn (pair p l))
    intro j hj hbad
    have hb := of_decide_eq_true hbad
    rw [List.length_ofFn]
    change (C.wires (List.ofFn (pair p l))).getD (N + N + j) false = false
    simpa only [Nat.zero_add] using hb.2 p l hpl
  have hsemD : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
    intro z
    constructor
    · intro hz
      apply (hsem z).mp
      exact zero_fold_le bad C.gates (fun g hg => (hC g hg).1) 0 (List.ofFn z) C.output hz
    · rintro ⟨p, l, hpl, hp, hl⟩
      have hold : circuitFun (N + N) C (pair p l) = true :=
        (hsem _).mpr ⟨p, l, hpl, by simp [pair], by simp [pair]⟩
      have hnew : circuitFun (N + N) D (pair p l) = true := by
        change (D.wires (List.ofFn (pair p l))).getD C.output false = true
        rw [heq p l hpl]
        exact hold
      apply wires_mono (N + N) D hm (pair p l) z _ D.output hnew
      intro k hk
      rcases of_decide_eq_true hk with rfl | rfl
      · exact hp
      · exact hl
  refine ⟨D, ?_, hm, zero_back _ C bad hback, hsemD, ?_⟩
  · exact zero_length bad C.gates 0
  · intro j hj hand
    have hj' : j < C.gates.length := by simpa only [D, zeroCircuit, zero_length] using hj
    have hgate : gateAt D j = zeroGate (bad j) (gateAt C j) := by
      simpa only [D, zeroCircuit, gateAt, Nat.zero_add] using zero_getD bad C.gates 0 j hj'
    have hb : bad j = false := by
      cases h : bad j with
      | false => rfl
      | true => simp [hgate, zeroGate, h] at hand
    have hop : (gateAt C j).op = GateOp.and := by simpa [hgate, zeroGate, hb] using hand
    by_contra hnone
    have hall : ∀ p l : Fin N, I p l →
        (C.wires (List.ofFn (pair p l))).getD (N + N + j) false = false := by
      intro p l hpl
      cases hv : (C.wires (List.ofFn (pair p l))).getD (N + N + j) false with
      | false => rfl
      | true =>
        apply False.elim
        apply hnone
        refine ⟨p, l, hpl, ?_⟩
        change (D.wires (List.ofFn (pair p l))).getD (N + N + j) false = true
        rw [heq p l hpl]
        exact hv
    have htrue : bad j = true := by exact decide_eq_true ⟨hop, hall⟩
    rw [hb] at htrue
    cases htrue

end PEqualNP.Outside.L_meta_3451_aux.Prune
