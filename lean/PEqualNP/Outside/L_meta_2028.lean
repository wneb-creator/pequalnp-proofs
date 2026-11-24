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

namespace AndGate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def JoinLists (a b c : List Bool) : Prop :=
  a.length = b.length ∧ a.length = c.length ∧
    ∀ i, c.getD i false = (a.getD i false || b.getD i false)

lemma joinLists_append {a b c : List Bool} (h : JoinLists a b c)
    (u v w : Bool) (hw : w = (u || v)) :
    JoinLists (a ++ [u]) (b ++ [v]) (c ++ [w]) := by
  obtain ⟨hab, hac, h⟩ := h
  refine ⟨by simp [hab], by simp [hac], ?_⟩
  intro i
  by_cases hi : i < a.length
  · rw [List.getD_append c [w] false i (by omega),
      List.getD_append a [u] false i hi,
      List.getD_append b [v] false i (by omega)]
    exact h i
  · rw [List.getD_append_right c [w] false i (by omega),
      List.getD_append_right a [u] false i (by omega),
      List.getD_append_right b [v] false i (by omega), ← hac, ← hab]
    cases hd : i - a.length with
    | zero => simpa using hw
    | succ k => simp

lemma any_join (is : List ℕ) (f g : ℕ → Bool) :
    is.any (fun i => f i || g i) = (is.any f || is.any g) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.any_cons, ih]
    cases f i <;> cases g i <;> simp

lemma or_gate_join {a b c : List Bool} (h : JoinLists a b c) (g : Gate)
    (hop : g.op = GateOp.or) :
    g.op.eval (g.inputs.map fun i => c.getD i false) =
      (g.op.eval (g.inputs.map fun i => a.getD i false) ||
       g.op.eval (g.inputs.map fun i => b.getD i false)) := by
  simp only [hop, GateOp.eval, List.any_map, Function.comp_def, id_eq]
  calc
    g.inputs.any (fun i => c.getD i false) =
        g.inputs.any (fun i => a.getD i false || b.getD i false) := by
      congr 1
      funext i
      exact h.2.2 i
    _ = _ := any_join _ _ _

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma fold_join (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.or)
    (a b c : List Bool) (h : JoinLists a b c) :
    JoinLists (gs.foldl step a) (gs.foldl step b) (gs.foldl step c) := by
  induction gs generalizing a b c with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun q hq => hgs q (List.mem_cons_of_mem _ hq))
    exact joinLists_append h _ _ _ (or_gate_join h g (hgs g (by simp)))

lemma or_only_eval_join (n : ℕ) (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.or) (x y : Fin n → Bool) :
    C.eval (List.ofFn fun i => x i || y i) =
      (C.eval (List.ofFn x) || C.eval (List.ofFn y)) := by
  have hin : JoinLists (List.ofFn x) (List.ofFn y)
      (List.ofFn fun i => x i || y i) := by
    refine ⟨by simp, by simp, ?_⟩
    intro i
    by_cases hi : i < n <;>
      simp [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi]
  exact (fold_join C.gates hC _ _ _ hin).2.2 C.output

lemma has_and_of_nonempty_edge_function (n : ℕ) (G : SimpleGraph (Fin n))
    (C : Circuit) (hedge : ∃ u v : Fin n, G.Adj u v) (hmono : Monotone2 C)
    (hcomp : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) :
    ∃ g ∈ C.gates, g.op = GateOp.and := by
  classical
  by_contra hnot
  have hor : ∀ g ∈ C.gates, g.op = GateOp.or := by
    intro g hg
    have hop := (hmono g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with ha | ho
    · exact False.elim (hnot ⟨g, hg, ha⟩)
    · exact ho
  have hsingle (i : Fin n) :
      C.eval (List.ofFn fun j : Fin n => decide (j = i)) = false := by
    cases heval : C.eval (List.ofFn fun j : Fin n => decide (j = i)) with
    | false => rfl
    | true =>
      obtain ⟨u, v, huv, hu, hv⟩ := (hcomp _).mp heval
      have hui : u = i := by simpa using hu
      have hvi : v = i := by simpa using hv
      subst u
      subst v
      exact False.elim (G.loopless.irrefl _ huv)
  obtain ⟨u, v, huv⟩ := hedge
  have hpair : C.eval (List.ofFn fun i : Fin n => decide (i = u) || decide (i = v)) = true := by
    apply (hcomp _).mpr
    exact ⟨u, v, huv, by simp, by simp⟩
  rw [or_only_eval_join n C hor, hsingle u, hsingle v] at hpair
  cases hpair

end AndGate

end PEqualNP.Outside.L_meta_2028
