import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2028.OrGate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def MeetLists (a b c : List Bool) : Prop :=
  a.length = b.length ∧ a.length = c.length ∧
    ∀ i, c.getD i false = (a.getD i false && b.getD i false)

lemma meetLists_append {a b c : List Bool} (h : MeetLists a b c)
    (u v w : Bool) (hw : w = (u && v)) :
    MeetLists (a ++ [u]) (b ++ [v]) (c ++ [w]) := by
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

lemma all_meet (is : List ℕ) (f g : ℕ → Bool) :
    is.all (fun i => f i && g i) = (is.all f && is.all g) := by
  induction is with
  | nil => rfl
  | cons i is ih =>
    simp only [List.all_cons, ih]
    cases f i <;> cases g i <;> simp

lemma and_gate_meet {a b c : List Bool} (h : MeetLists a b c) (g : Gate)
    (hop : g.op = GateOp.and) :
    g.op.eval (g.inputs.map fun i => c.getD i false) =
      (g.op.eval (g.inputs.map fun i => a.getD i false) &&
       g.op.eval (g.inputs.map fun i => b.getD i false)) := by
  simp only [hop, GateOp.eval, List.all_map, Function.comp_def, id_eq]
  calc
    g.inputs.all (fun i => c.getD i false) =
        g.inputs.all (fun i => a.getD i false && b.getD i false) := by
      congr 1
      funext i
      exact h.2.2 i
    _ = _ := all_meet _ _ _

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma fold_meet (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and)
    (a b c : List Bool) (h : MeetLists a b c) :
    MeetLists (gs.foldl step a) (gs.foldl step b) (gs.foldl step c) := by
  induction gs generalizing a b c with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih (fun q hq => hgs q (List.mem_cons_of_mem _ hq))
    exact meetLists_append h _ _ _ (and_gate_meet h g (hgs g (by simp)))

lemma and_only_eval_meet (n : ℕ) (C : Circuit)
    (hC : ∀ g ∈ C.gates, g.op = GateOp.and) (x y : Fin n → Bool) :
    C.eval (List.ofFn fun i => x i && y i) =
      (C.eval (List.ofFn x) && C.eval (List.ofFn y)) := by
  have hin : MeetLists (List.ofFn x) (List.ofFn y)
      (List.ofFn fun i => x i && y i) := by
    refine ⟨by simp, by simp, ?_⟩
    intro i
    by_cases hi : i < n <;> simp [List.getD_eq_getElem?_getD, hi]
  exact (fold_meet C.gates hC _ _ _ hin).2.2 C.output

lemma pair_eq_of_mem {n : ℕ} (u v a b : Fin n) (hne : u ≠ v)
    (hu : u = a ∨ u = b) (hv : v = a ∨ v = b) : s(u, v) = s(a, b) := by
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · contradiction
  · rfl
  · exact Sym2.eq_swap
  · contradiction

lemma has_or_of_distinct_edges (n : ℕ) (G : SimpleGraph (Fin n))
    (C : Circuit) (a b c d : Fin n) (hab : G.Adj a b) (hcd : G.Adj c d)
    (hne : s(a, b) ≠ s(c, d)) (hmono : Monotone2 C)
    (hcomp : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) :
    ∃ g ∈ C.gates, g.op = GateOp.or := by
  classical
  by_contra hnot
  have hand : ∀ g ∈ C.gates, g.op = GateOp.and := by
    intro g hg
    have hop := (hmono g hg).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    rcases hop with ha | ho
    · exact ha
    · exact False.elim (hnot ⟨g, hg, ho⟩)
  let x : Fin n → Bool := fun i => decide (i = a ∨ i = b)
  let y : Fin n → Bool := fun i => decide (i = c ∨ i = d)
  have hx : C.eval (List.ofFn x) = true :=
    (hcomp x).mpr ⟨a, b, hab, by simp [x], by simp [x]⟩
  have hy : C.eval (List.ofFn y) = true :=
    (hcomp y).mpr ⟨c, d, hcd, by simp [y], by simp [y]⟩
  have hxy : C.eval (List.ofFn fun i => x i && y i) = true := by
    rw [and_only_eval_meet n C hand, hx, hy]
    rfl
  obtain ⟨u, v, huv, hu, hv⟩ := (hcomp _).mp hxy
  have huvne : u ≠ v := by
    intro heq
    subst v
    exact G.loopless.irrefl _ huv
  have hu' : (u = a ∨ u = b) ∧ (u = c ∨ u = d) := by simpa [x, y] using hu
  have hv' : (v = a ∨ v = b) ∧ (v = c ∨ v = d) := by simpa [x, y] using hv
  exact hne ((pair_eq_of_mem u v a b huvne hu'.1 hv'.1).symm.trans
    (pair_eq_of_mem u v c d huvne hu'.2 hv'.2))

end PEqualNP.Outside.L_meta_2028.OrGate
