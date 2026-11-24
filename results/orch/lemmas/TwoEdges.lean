import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2028.AndGate

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

end PEqualNP.Outside.L_meta_2028.AndGate

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

namespace PEqualNP.Outside.L_meta_2028

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma size_ge_two_of_and_or (C : Circuit)
    (hand : ∃ g ∈ C.gates, g.op = GateOp.and)
    (hor : ∃ g ∈ C.gates, g.op = GateOp.or) : 2 ≤ C.size := by
  obtain ⟨a, ha, hopa⟩ := hand
  obtain ⟨o, ho, hopo⟩ := hor
  by_contra hsize
  have hlen : C.gates.length ≤ 1 := by
    change ¬ 2 ≤ C.gates.length at hsize
    omega
  cases hgs : C.gates with
  | nil => simpa [hgs] using ha
  | cons g gs =>
    have hlen' : gs.length = 0 := by
      rw [hgs, List.length_cons] at hlen
      omega
    have hnil : gs = [] := List.eq_nil_of_length_eq_zero hlen'
    subst gs
    have hae : a = g := by simpa [hgs] using ha
    have hoe : o = g := by simpa [hgs] using ho
    subst a
    subst o
    rw [hopa] at hopo
    cases hopo

lemma size_ge_two_of_distinct_edges (n : ℕ) (G : SimpleGraph (Fin n))
    (C : Circuit) (a b c d : Fin n) (hab : G.Adj a b) (hcd : G.Adj c d)
    (hne : s(a, b) ≠ s(c, d)) (hmono : Monotone2 C)
    (hcomp : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = true ↔
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) :
    2 ≤ C.size := by
  apply size_ge_two_of_and_or C
  · exact AndGate.has_and_of_nonempty_edge_function n G C ⟨a, b, hab⟩ hmono hcomp
  · exact OrGate.has_or_of_distinct_edges n G C a b c d hab hcd hne hmono hcomp

end PEqualNP.Outside.L_meta_2028
