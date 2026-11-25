import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_2056

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def SameExcept (u : ℕ) (w z : List Bool) : Prop :=
  w.length = z.length ∧ ∀ i, i ≠ u → w.getD i false = z.getD i false

lemma sameExcept_append (u : ℕ) (w z : List Bool) (b : Bool)
    (h : SameExcept u w z) : SameExcept u (w ++ [b]) (z ++ [b]) := by
  refine ⟨by simpa using h.1, ?_⟩
  have hlen := h.1
  intro i hi
  by_cases hlt : i < w.length
  · rw [List.getD_append w [b] false i hlt,
      List.getD_append z [b] false i (by omega)]
    exact h.2 i hi
  · rw [List.getD_append_right w [b] false i (by omega),
      List.getD_append_right z [b] false i (by omega), h.1]

lemma step_sameExcept (u : ℕ) (w z : List Bool) (g : Gate)
    (h : SameExcept u w z) (hg : u ∉ g.inputs) : SameExcept u (step w g) (step z g) := by
  have he : g.inputs.map (fun i => w.getD i false) =
      g.inputs.map (fun i => z.getD i false) := by
    apply List.map_congr_left
    intro i hi
    exact h.2 i (by intro e; subst i; exact hg hi)
  unfold step
  rw [he]
  exact sameExcept_append u w z _ h

lemma fold_sameExcept (u : ℕ) (gs : List Gate) (w z : List Bool)
    (h : SameExcept u w z) (hg : ∀ g ∈ gs, u ∉ g.inputs) :
    SameExcept u (gs.foldl step w) (gs.foldl step z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    exact ih (step w g) (step z g) (step_sameExcept u w z g h (hg g (by simp)))
      (by intro g hg'; exact hg g (by simp [hg']))

lemma eval_first_indistinguishable (u : ℕ) (first : Gate) (tail : List Gate)
    (output : ℕ) (x y : List Bool)
    (hxy : SameExcept u x y)
    (hfirst : first.op.eval (first.inputs.map fun i => x.getD i false) =
      first.op.eval (first.inputs.map fun i => y.getD i false))
    (htail : ∀ g ∈ tail, u ∉ g.inputs) (hout : output ≠ u) :
    (Circuit.mk (first :: tail) output).eval x =
      (Circuit.mk (first :: tail) output).eval y := by
  have hstep : SameExcept u (step x first) (step y first) := by
    unfold step
    rw [hfirst]
    exact sameExcept_append u x y _ hxy
  exact (fold_sameExcept u tail _ _ hstep htail).2 output hout

lemma exists_reread_of_distinguished (u : ℕ) (first : Gate) (tail : List Gate)
    (output : ℕ) (x y : List Bool)
    (hxy : SameExcept u x y)
    (hfirst : first.op.eval (first.inputs.map fun i => x.getD i false) =
      first.op.eval (first.inputs.map fun i => y.getD i false))
    (hdiff : (Circuit.mk (first :: tail) output).eval x ≠
      (Circuit.mk (first :: tail) output).eval y) :
    output = u ∨ ∃ g ∈ tail, u ∈ g.inputs := by
  by_contra hn
  push Not at hn
  exact hdiff (eval_first_indistinguishable u first tail output x y hxy hfirst hn.2 hn.1)

lemma sameExcept_ofFn {n : ℕ} (u : Fin n) (x y : Fin n → Bool)
    (h : ∀ i, i ≠ u → x i = y i) :
    SameExcept u.val (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hin : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hin),
      List.getD_eq_getElem _ _ (by simpa using hin)]
    simpa using h ⟨i, hin⟩ (by intro e; exact hi (congrArg Fin.val e))
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hin),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hin)]

lemma getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem _ _ (by simp)]
  simp

lemma and_first_requires_reread {n : ℕ} (u v : Fin n) (tail : List Gate)
    (output : ℕ) (x y : Fin n → Bool)
    (hxy : ∀ i, i ≠ u → x i = y i) (hxv : x v = false) (hyv : y v = false)
    (hout : output ≠ u.val)
    (hdiff : (Circuit.mk (⟨GateOp.and, [u.val, v.val]⟩ :: tail) output).eval (List.ofFn x) ≠
      (Circuit.mk (⟨GateOp.and, [u.val, v.val]⟩ :: tail) output).eval (List.ofFn y)) :
    ∃ g ∈ tail, u.val ∈ g.inputs := by
  have hfirst : GateOp.and.eval ([u.val, v.val].map fun i => (List.ofFn x).getD i false) =
      GateOp.and.eval ([u.val, v.val].map fun i => (List.ofFn y).getD i false) := by
    simp [GateOp.eval, hxv, hyv]
  exact (exists_reread_of_distinguished u.val _ tail output _ _
    (sameExcept_ofFn u x y hxy) hfirst hdiff).resolve_left hout

lemma or_first_requires_reread {n : ℕ} (u v : Fin n) (tail : List Gate)
    (output : ℕ) (x y : Fin n → Bool)
    (hxy : ∀ i, i ≠ u → x i = y i) (hxv : x v = true) (hyv : y v = true)
    (hout : output ≠ u.val)
    (hdiff : (Circuit.mk (⟨GateOp.or, [u.val, v.val]⟩ :: tail) output).eval (List.ofFn x) ≠
      (Circuit.mk (⟨GateOp.or, [u.val, v.val]⟩ :: tail) output).eval (List.ofFn y)) :
    ∃ g ∈ tail, u.val ∈ g.inputs := by
  have hfirst : GateOp.or.eval ([u.val, v.val].map fun i => (List.ofFn x).getD i false) =
      GateOp.or.eval ([u.val, v.val].map fun i => (List.ofFn y).getD i false) := by
    simp [GateOp.eval, hxv, hyv]
  exact (exists_reread_of_distinguished u.val _ tail output _ _
    (sameExcept_ofFn u x y hxy) hfirst hdiff).resolve_left hout

lemma graphFun_singleton {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (w : Fin n) :
    PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (fun i => decide (i = w)) = false := by
  simp [PEqualNP.MetaComplexity.NestedCover.graphFun]

lemma graphFun_pair_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (v w : Fin n) (hn : ¬ G.Adj v w) :
    PEqualNP.MetaComplexity.NestedCover.graphFun G ∅
      (fun i => decide (i = v ∨ i = w)) = false := by
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty,
    false_and, exists_false, decide_false, Bool.false_or, decide_eq_false_iff_not]
  rintro ⟨a, b, hab, ha, hb⟩
  have ha' : a = v ∨ a = w := of_decide_eq_true ha
  have hb' : b = v ∨ b = w := of_decide_eq_true hb
  rcases ha' with rfl | rfl <;> rcases hb' with rfl | rfl
  · simp at hab
  · exact hn hab
  · exact hn (by simpa only [G.adj_comm] using hab)
  · simp at hab

lemma graphFun_true_of_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) (u w : Fin n) (hu : G.Adj u w) (hxu : x u = true)
    (hxw : x w = true) :
    PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true := by
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty,
    false_and, exists_false, decide_false, Bool.false_or, decide_eq_true_eq]
  exact ⟨u, w, hu, hxu, hxw⟩

lemma fold_getD_input (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl step (step w g)).getD i false = _
    rw [ih (step w g) (by simp [step]; omega)]
    exact List.getD_append w [_] false i hi

lemma graph_output_ne_input {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit)
    (hc : ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
      PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x) (u : Fin n) :
    C.output ≠ u.val := by
  intro hout
  let x : Fin n → Bool := fun i => decide (i = u)
  have heval : C.eval (List.ofFn x) = true := by
    change (C.gates.foldl step (List.ofFn x)).getD C.output false = true
    rw [hout, fold_getD_input C.gates _ u.val (by simp)]
    simp [x]
  have hneg := graphFun_singleton G u
  rw [hc] at heval
  change PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = false at hneg
  rw [hneg] at heval
  contradiction

lemma and_first_graph_reread {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v w : Fin n) (huv : u ≠ v) (hwv : w ≠ v) (huw : G.Adj u w)
    (tail : List Gate) (output : ℕ)
    (hc : ∀ x : Fin n → Bool,
      (Circuit.mk (⟨GateOp.and, [u.val, v.val]⟩ :: tail) output).eval (List.ofFn x) =
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x) :
    ∃ g ∈ tail, u.val ∈ g.inputs := by
  let x : Fin n → Bool := fun i => decide (i = w)
  let y : Fin n → Bool := fun i => decide (i = u ∨ i = w)
  apply and_first_requires_reread u v tail output x y
  · intro i hi
    simp [x, y, hi]
  · simp [x, Ne.symm hwv]
  · simp [y, Ne.symm huv, Ne.symm hwv]
  · exact graph_output_ne_input G _ hc u
  · rw [hc, hc]
    have hx : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = false :=
      graphFun_singleton G w
    have hy : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y = true :=
      graphFun_true_of_edge G y u w huw (by simp [y]) (by simp [y])
    rw [hx, hy]
    decide

lemma or_first_graph_reread_of_edge {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (u v : Fin n) (huv : G.Adj u v)
    (tail : List Gate) (output : ℕ)
    (hc : ∀ x : Fin n → Bool,
      (Circuit.mk (⟨GateOp.or, [u.val, v.val]⟩ :: tail) output).eval (List.ofFn x) =
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x) :
    ∃ g ∈ tail, u.val ∈ g.inputs := by
  let x : Fin n → Bool := fun i => decide (i = v)
  let y : Fin n → Bool := fun i => decide (i = u ∨ i = v)
  apply or_first_requires_reread u v tail output x y
  · intro i hi
    simp [x, y, hi]
  · simp [x]
  · simp [y]
  · exact graph_output_ne_input G _ hc u
  · rw [hc, hc]
    have hx : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = false :=
      graphFun_singleton G v
    have hy : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y = true :=
      graphFun_true_of_edge G y u v huv (by simp [y]) (by simp [y])
    rw [hx, hy]
    decide

lemma or_first_graph_reread_of_separated {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (u v w : Fin n) (huw : G.Adj u w) (hnvw : ¬ G.Adj v w)
    (tail : List Gate) (output : ℕ)
    (hc : ∀ x : Fin n → Bool,
      (Circuit.mk (⟨GateOp.or, [u.val, v.val]⟩ :: tail) output).eval (List.ofFn x) =
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x) :
    ∃ g ∈ tail, u.val ∈ g.inputs := by
  let x : Fin n → Bool := fun i => decide (i = v ∨ i = w)
  let y : Fin n → Bool := fun i => decide (i = u ∨ i = v ∨ i = w)
  apply or_first_requires_reread u v tail output x y
  · intro i hi
    simp [x, y, hi]
  · simp [x]
  · simp [y]
  · exact graph_output_ne_input G _ hc u
  · rw [hc, hc]
    have hx : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = false :=
      graphFun_pair_false G v w hnvw
    have hy : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y = true :=
      graphFun_true_of_edge G y u w huw (by simp [y]) (by simp [y])
    rw [hx, hy]
    decide


def near (p l : Fin 13) : Prop :=
  (p.val + l.val) % 13 ∈ ([0, 1, 3, 9] : List ℕ)

def pointGuard (T : Finset (Fin 13)) (x : Fin 13 → Bool) : Bool :=
  decide (∀ p ∈ T, x p = true)

def augment (u : Fin 13) (T : Finset (Fin 13)) (x : Fin 13 → Bool) : Fin 13 → Bool :=
  fun p => if p = u then x p || pointGuard T x else x p

lemma guard_absorption (u : Fin 13) (T : Finset (Fin 13))
    (cover : ∀ l, near u l → ∃ p ∈ T, near p l) (x y : Fin 13 → Bool) :
    (∃ p l, near p l ∧ augment u T x p = true ∧ y l = true) ↔
      ∃ p l, near p l ∧ x p = true ∧ y l = true := by
  constructor
  · rintro ⟨p, l, hp, hx, hy⟩
    by_cases hpu : p = u
    · subst p
      cases hxu : x u with
      | false =>
        have ht : pointGuard T x = true := by simpa [augment, hxu] using hx
        obtain ⟨q, hq, hnear⟩ := cover l hp
        exact ⟨q, l, hnear, (of_decide_eq_true ht) q hq, hy⟩
      | true => exact ⟨u, l, hp, hxu, hy⟩
    · exact ⟨p, l, hp, by simpa [augment, hpu] using hx, hy⟩
  · rintro ⟨p, l, hp, hx, hy⟩
    exact ⟨p, l, hp, by simp [augment, hx], hy⟩

lemma four_point_guard_cover :
    ∀ l : Fin 13, near 0 l → ∃ p ∈ ({1, 2, 4, 6} : Finset (Fin 13)), near p l := by
  unfold near
  decide +kernel

lemma four_point_guard_absorption (x y : Fin 13 → Bool) :
    (∃ p l, near p l ∧ augment 0 {1, 2, 4, 6} x p = true ∧ y l = true) ↔
      ∃ p l, near p l ∧ x p = true ∧ y l = true :=
  guard_absorption 0 {1, 2, 4, 6} four_point_guard_cover x y

lemma four_point_guard_is_not_an_edge :
    let x : Fin 13 → Bool := fun p => decide (p ∈ ({1, 2, 4, 6} : Finset (Fin 13)))
    pointGuard {1, 2, 4, 6} x = true ∧
      ¬ ∃ p l, near p l ∧ x p = true ∧ (fun _ : Fin 13 => false) l = true := by
  unfold near
  decide +kernel

end PEqualNP.Outside.L_meta_2056
