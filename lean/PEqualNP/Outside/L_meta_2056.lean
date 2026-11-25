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


def WireLe (w z : List Bool) : Prop :=
  w.length = z.length ∧ ∀ i, w.getD i false = true → z.getD i false = true

lemma wireLe_append (w z : List Bool) (b c : Bool) (h : WireLe w z)
    (hbc : b = true → c = true) : WireLe (w ++ [b]) (z ++ [c]) := by
  have hlen := h.1
  refine ⟨by simpa using hlen, ?_⟩
  intro i hi
  by_cases hlt : i < w.length
  · rw [List.getD_append w [b] false i hlt] at hi
    rw [List.getD_append z [c] false i (by omega)]
    exact h.2 i hi
  · rw [List.getD_append_right w [b] false i (by omega), hlen] at hi
    rw [List.getD_append_right z [c] false i (by omega)]
    cases hn : i - z.length <;> simp_all

lemma gate_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f g : ℕ → Bool) (h : ∀ i ∈ l, f i = true → g i = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi
    exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩
    exact ⟨i, hi, h i hi h1⟩

lemma fold_wireLe (gs : List Gate) (w z : List Bool) (h : WireLe w z)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    WireLe (gs.foldl step w) (gs.foldl step z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    apply ih (step w g) (step z g)
    · apply wireLe_append w z _ _ h
      exact gate_eval_mono g.op (hgs g (by simp)) g.inputs _ _ (by intro i _; exact h.2 i)
    · intro g hg
      exact hgs g (by simp [hg])

lemma wireLe_ofFn {n : ℕ} (x y : Fin n → Bool)
    (h : ∀ i, x i = true → y i = true) : WireLe (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hin : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hin)] at hi ⊢
    simpa using h ⟨i, hin⟩ (by simpa using hi)
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hin)] at hi
    contradiction

lemma eval_split_or_indistinguishable (u sibling : ℕ) (pre tail : List Gate)
    (output : ℕ) (x y : List Bool)
    (hxy : SameExcept u x y) (hpre : ∀ g ∈ pre, u ∉ g.inputs)
    (htail : ∀ g ∈ tail, u ∉ g.inputs) (hout : output ≠ u)
    (hxs : (pre.foldl step x).getD sibling false = true)
    (hys : (pre.foldl step y).getD sibling false = true) :
    (Circuit.mk (pre ++ ⟨GateOp.or, [u, sibling]⟩ :: tail) output).eval x =
      (Circuit.mk (pre ++ ⟨GateOp.or, [u, sibling]⟩ :: tail) output).eval y := by
  have hfirst : GateOp.or.eval ([u, sibling].map fun i => (pre.foldl step x).getD i false) =
      GateOp.or.eval ([u, sibling].map fun i => (pre.foldl step y).getD i false) := by
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
      id_eq, Bool.or_false]
    rw [hxs, hys]
    simp
  change ((pre ++ ⟨GateOp.or, [u, sibling]⟩ :: tail).foldl step x).getD output false =
    ((pre ++ ⟨GateOp.or, [u, sibling]⟩ :: tail).foldl step y).getD output false
  rw [List.foldl_append, List.foldl_append]
  exact eval_first_indistinguishable u _ tail output _ _
    (fold_sameExcept u pre x y hxy hpre) hfirst htail hout

lemma graphFun_set_true_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) (v : Fin n)
    (hx : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = false)
    (hv : ¬ ∃ t, x t = true ∧ G.Adj t v) :
    PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ (fun i => if i = v then true else x i) =
      false := by
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Finset.notMem_empty,
    false_and, exists_false, decide_false, Bool.false_or, decide_eq_false_iff_not]
  rintro ⟨a, b, hab, ha, hb⟩
  by_cases hav : a = v
  · subst a
    by_cases hbv : b = v
    · subst b
      simp at hab
    · exact hv ⟨b, by simpa [hbv] using hb, by simpa only [G.adj_comm] using hab⟩
  · by_cases hbv : b = v
    · subst b
      exact hv ⟨a, by simpa [hav] using ha, hab⟩
    · have hf := graphFun_true_of_edge G x a b hab
        (by simpa [hav] using ha) (by simpa [hbv] using hb)
      rw [hx] at hf
      contradiction

lemma sole_or_reader_blocks_neighbors {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (u : Fin n) (sibling : ℕ) (pre tail : List Gate) (output : ℕ)
    (hpre : ∀ g ∈ pre, u.val ∉ g.inputs) (htail : ∀ g ∈ tail, u.val ∉ g.inputs)
    (hsib : sibling ≠ u.val)
    (hmono : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hc : ∀ x : Fin n → Bool,
      (Circuit.mk (pre ++ ⟨GateOp.or, [u.val, sibling]⟩ :: tail) output).eval (List.ofFn x) =
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x)
    (x : Fin n → Bool)
    (hx : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = false)
    (hxs : (pre.foldl step (List.ofFn x)).getD sibling false = true) :
    ∀ v, G.Adj u v → ∃ t, x t = true ∧ G.Adj t v := by
  intro v huv
  by_contra hv
  let y : Fin n → Bool := fun i => if i = v then true else x i
  let z : Fin n → Bool := fun i => if i = u then true else y i
  have hyneg : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y = false :=
    graphFun_set_true_false G x v hx hv
  have hzy : SameExcept u.val (List.ofFn y) (List.ofFn z) := by
    apply sameExcept_ofFn
    intro i hi
    simp [z, hi]
  have hys : (pre.foldl step (List.ofFn y)).getD sibling false = true := by
    apply (fold_wireLe pre _ _ (wireLe_ofFn x y ?_) hmono).2 sibling hxs
    intro i hi
    simp only [y]
    split_ifs <;> simp_all
  have hzs : (pre.foldl step (List.ofFn z)).getD sibling false = true := by
    rw [← (fold_sameExcept u.val pre _ _ hzy hpre).2 sibling hsib]
    exact hys
  have heq := eval_split_or_indistinguishable u.val sibling pre tail output
    (List.ofFn y) (List.ofFn z) hzy hpre htail (graph_output_ne_input G _ hc u) hys hzs
  rw [hc, hc, hyneg] at heq
  have hzpos : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ z = true := by
    apply graphFun_true_of_edge G z u v huv
    · simp [z]
    · simp [z, y]
  rw [hzpos] at heq
  contradiction

lemma neighbor_card_le_active_cover {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (u : Fin n) (A : Finset (Fin n)) (x : Fin n → Bool)
    (hxu : x u = false)
    (hcover : ∀ v, G.Adj u v → ∃ t, x t = true ∧ G.Adj t v)
    (hside : ∀ v t, G.Adj u v → G.Adj t v → t ∈ A)
    (hunique : ∀ t, t ≠ u → ∀ v w, G.Adj u v → G.Adj t v →
      G.Adj u w → G.Adj t w → v = w) :
    (Finset.univ.filter fun v => G.Adj u v).card ≤ (A.filter fun t => x t = true).card := by
  classical
  let N := Finset.univ.filter fun v => G.Adj u v
  let S := A.filter fun t => x t = true
  have hchoose : ∀ v : ↥N, ∃ t : ↥S, G.Adj t.val v.val := by
    intro v
    have hv : G.Adj u v.val := (Finset.mem_filter.mp v.property).2
    obtain ⟨t, ht, htv⟩ := hcover v.val hv
    refine ⟨⟨t, ?_⟩, htv⟩
    exact Finset.mem_filter.mpr ⟨hside v.val t hv htv, ht⟩
  choose f hf using hchoose
  have hinj : Function.Injective f := by
    intro v w hfw
    apply Subtype.ext
    have hne : (f v).val ≠ u := by
      intro heq
      have ht : x (f v).val = true := (Finset.mem_filter.mp (f v).property).2
      rw [heq, hxu] at ht
      contradiction
    exact hunique (f v).val hne v.val w.val (Finset.mem_filter.mp v.property).2 (hf v)
      (Finset.mem_filter.mp w.property).2 (by simpa [hfw] using hf w)
  change N.card ≤ S.card
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective f hinj

lemma sole_or_reader_support_bound {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (u : Fin n) (A : Finset (Fin n))
    (sibling : ℕ) (pre tail : List Gate) (output : ℕ)
    (hpre : ∀ g ∈ pre, u.val ∉ g.inputs) (htail : ∀ g ∈ tail, u.val ∉ g.inputs)
    (hsib : sibling ≠ u.val)
    (hmono : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hc : ∀ x : Fin n → Bool,
      (Circuit.mk (pre ++ ⟨GateOp.or, [u.val, sibling]⟩ :: tail) output).eval (List.ofFn x) =
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x)
    (x : Fin n → Bool) (hxu : x u = false)
    (hx : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = false)
    (hxs : (pre.foldl step (List.ofFn x)).getD sibling false = true)
    (hside : ∀ v t, G.Adj u v → G.Adj t v → t ∈ A)
    (hunique : ∀ t, t ≠ u → ∀ v w, G.Adj u v → G.Adj t v →
      G.Adj u w → G.Adj t w → v = w) :
    (Finset.univ.filter fun v => G.Adj u v).card ≤ (A.filter fun t => x t = true).card := by
  exact neighbor_card_le_active_cover G u A x hxu
    (sole_or_reader_blocks_neighbors G u sibling pre tail output hpre htail hsib hmono hc x hx hxs)
    hside hunique


lemma sole_and_reader_accepts_neighbors {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (u : Fin n) (sibling : ℕ) (pre tail : List Gate) (output : ℕ)
    (hpre : ∀ g ∈ pre, u.val ∉ g.inputs) (htail : ∀ g ∈ tail, u.val ∉ g.inputs)
    (hsib : sibling ≠ u.val)
    (hc : ∀ x : Fin n → Bool,
      (Circuit.mk (pre ++ ⟨GateOp.and, [u.val, sibling]⟩ :: tail) output).eval (List.ofFn x) =
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x) :
    ∀ v, G.Adj u v →
      (pre.foldl step (List.ofFn (fun i : Fin n => decide (i = v)))).getD sibling false =
        true := by
  intro v huv
  cases hxs : (pre.foldl step (List.ofFn (fun i : Fin n => decide (i = v)))).getD
      sibling false with
  | true => rfl
  | false =>
    exfalso
    let x : Fin n → Bool := fun i => decide (i = v)
    let y : Fin n → Bool := fun i => decide (i = u ∨ i = v)
    have hxy : SameExcept u.val (List.ofFn x) (List.ofFn y) := by
      apply sameExcept_ofFn
      intro i hi
      simp [x, y, hi]
    change (pre.foldl step (List.ofFn x)).getD sibling false = false at hxs
    have hprefix := fold_sameExcept u.val pre _ _ hxy hpre
    have hys : (pre.foldl step (List.ofFn y)).getD sibling false = false := by
      rw [← hprefix.2 sibling hsib]
      exact hxs
    have hfirst : GateOp.and.eval ([u.val, sibling].map fun i =>
        (pre.foldl step (List.ofFn x)).getD i false) =
        GateOp.and.eval ([u.val, sibling].map fun i =>
          (pre.foldl step (List.ofFn y)).getD i false) := by
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        id_eq, Bool.and_true]
      rw [hxs, hys]
      simp
    have heq := eval_first_indistinguishable u.val ⟨GateOp.and, [u.val, sibling]⟩
      tail output _ _ hprefix hfirst htail (graph_output_ne_input G _ hc u)
    have hfull :
        (Circuit.mk (pre ++ ⟨GateOp.and, [u.val, sibling]⟩ :: tail) output).eval
            (List.ofFn x) =
          (Circuit.mk (pre ++ ⟨GateOp.and, [u.val, sibling]⟩ :: tail) output).eval
            (List.ofFn y) := by
      change ((pre ++ ⟨GateOp.and, [u.val, sibling]⟩ :: tail).foldl step
          (List.ofFn x)).getD output false =
        ((pre ++ ⟨GateOp.and, [u.val, sibling]⟩ :: tail).foldl step
          (List.ofFn y)).getD output false
      rw [List.foldl_append, List.foldl_append]
      exact heq
    rw [hc, hc] at hfull
    have hx : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = false :=
      graphFun_singleton G v
    have hy : PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ y = true :=
      graphFun_true_of_edge G y u v huv (by simp [y]) (by simp [y])
    rw [hx, hy] at hfull
    contradiction

lemma sole_and_reader_accepts_neighbor_support {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (u : Fin n) (sibling : ℕ) (pre tail : List Gate) (output : ℕ)
    (hpre : ∀ g ∈ pre, u.val ∉ g.inputs) (htail : ∀ g ∈ tail, u.val ∉ g.inputs)
    (hsib : sibling ≠ u.val)
    (hmono : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hc : ∀ x : Fin n → Bool,
      (Circuit.mk (pre ++ ⟨GateOp.and, [u.val, sibling]⟩ :: tail) output).eval (List.ofFn x) =
        PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x)
    (x : Fin n → Bool) (hv : ∃ v, G.Adj u v ∧ x v = true) :
    (pre.foldl step (List.ofFn x)).getD sibling false = true := by
  obtain ⟨v, huv, hxv⟩ := hv
  have hsingle := sole_and_reader_accepts_neighbors G u sibling pre tail output
    hpre htail hsib hc v huv
  apply (fold_wireLe pre _ _ (wireLe_ofFn (fun i : Fin n => decide (i = v)) x ?_) hmono).2
    sibling hsingle
  intro i hi
  have hiv : i = v := of_decide_eq_true hi
  simpa [hiv] using hxv


end PEqualNP.Outside.L_meta_2056
