import PEqualNP.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic.FinCases

namespace PEqualNP.Outside.L_meta_10760

open PEqualNP.CircuitLowerBounds

def cutLE (a b : Bool) : Prop := a = true → b = true

def cutRel (u v : List Bool) : Prop := List.Forall₂ cutLE u v

def cutRun (gates : List Gate) (w : List Bool) : List Bool :=
  gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma cutRel_self (w : List Bool) : cutRel w w := by
  induction w with
  | nil => exact .nil
  | cons b w ih => exact .cons (fun h => h) ih

lemma cutRel_getD {u v : List Bool} (h : cutRel u v) (i : ℕ) :
    cutLE (u.getD i false) (v.getD i false) := by
  induction h generalizing i with
  | nil => exact fun h => h
  | @cons a b u v hab huv ih =>
    cases i with
    | zero => simpa only [List.getD_cons_zero] using hab
    | succ i => simpa only [List.getD_cons_succ] using ih i

lemma cutRel_append {u v s t : List Bool} (h : cutRel u v) (h' : cutRel s t) :
    cutRel (u ++ s) (v ++ t) := List.rel_append h h'

lemma cutRel_map {u v : List Bool} (h : cutRel u v) (is : List ℕ) :
    cutRel (is.map fun i => u.getD i false) (is.map fun i => v.getD i false) := by
  induction is with
  | nil => exact .nil
  | cons i is ih => exact .cons (cutRel_getD h i) ih

lemma cutAll_mono {u v : List Bool} (h : cutRel u v) : cutLE (u.all id) (v.all id) := by
  induction h with
  | nil => exact fun h => h
  | @cons a b u v hab huv ih =>
    intro h
    change a && u.all id = true at h
    change b && v.all id = true
    exact Bool.and_eq_true_iff.mpr ⟨hab (Bool.and_eq_true_iff.mp h).1,
      ih (Bool.and_eq_true_iff.mp h).2⟩

lemma cutAny_mono {u v : List Bool} (h : cutRel u v) : cutLE (u.any id) (v.any id) := by
  induction h with
  | nil => exact fun h => h
  | @cons a b u v hab huv ih =>
    intro h
    change a || u.any id = true at h
    change b || v.any id = true
    rcases Bool.or_eq_true_iff.mp h with h | h
    · exact Bool.or_eq_true_iff.mpr (Or.inl (hab h))
    · exact Bool.or_eq_true_iff.mpr (Or.inr (ih h))

lemma cutGate_mono {u v : List Bool} (h : cutRel u v) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) :
    cutLE (g.op.eval (g.inputs.map fun i => u.getD i false))
      (g.op.eval (g.inputs.map fun i => v.getD i false)) := by
  rcases hg with hg | hg
  · rw [hg]
    exact cutAll_mono (cutRel_map h g.inputs)
  · rw [hg]
    exact cutAny_mono (cutRel_map h g.inputs)

lemma cutRun_mono (gates : List Gate)
    (hg : ∀ g ∈ gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    {u v : List Bool} (h : cutRel u v) : cutRel (cutRun gates u) (cutRun gates v) := by
  induction gates generalizing u v with
  | nil => exact h
  | cons g gates ih =>
    have hg' : ∀ k ∈ gates, k.op = GateOp.and ∨ k.op = GateOp.or :=
      fun k hk => hg k (List.mem_cons_of_mem g hk)
    exact ih hg' (cutRel_append h (.cons (cutGate_mono h g (hg g List.mem_cons_self)) .nil))

lemma cutRel_ofFn {n : ℕ} {x y : Fin n → Bool} (h : ∀ i, cutLE (x i) (y i)) :
    cutRel (List.ofFn x) (List.ofFn y) := by
  apply List.forall₂_of_length_eq_of_get (by simp)
  intro i hi hj
  simpa using h ⟨i, by simpa using hi⟩

lemma cutRun_input (gates : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (cutRun gates w).getD i false = w.getD i false := by
  induction gates generalizing w with
  | nil => rfl
  | cons g gates ih =>
    change (cutRun gates (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)])).getD i false = _
    rw [ih _ (by simp; omega)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

def cutInput (pre : List Gate) (inputs : List ℕ) (x : List Bool) : Bool :=
  (inputs.map fun i => (cutRun pre x).getD i false).headD false

lemma cutInput_mono (pre : List Gate) (inputs : List ℕ)
    (hp : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    {x y : List Bool} (hxy : cutRel x y) :
    cutLE (cutInput pre inputs x) (cutInput pre inputs y) := by
  cases inputs with
  | nil => exact fun h => h
  | cons i inputs =>
    simpa only [cutInput, List.map_cons, List.headD_cons] using
      cutRel_getD (cutRun_mono pre hp hxy) i

def cutOutput (pre suffix : List Gate) (o : ℕ) (x : List Bool) (z : Bool) : Bool :=
  (cutRun suffix (cutRun pre x ++ [z])).getD o false

lemma cutOutput_mono (pre suffix : List Gate) (o : ℕ) (x : List Bool)
    (hs : ∀ g ∈ suffix, g.op = GateOp.and ∨ g.op = GateOp.or)
    {a b : Bool} (hab : cutLE a b) :
    cutLE (cutOutput pre suffix o x a) (cutOutput pre suffix o x b) :=
  cutRel_getD (cutRun_mono suffix hs
    (cutRel_append (cutRel_self _) (.cons hab .nil))) o

lemma cutOutput_inputs_mono (pre suffix : List Gate) (o : ℕ)
    (hp : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hs : ∀ g ∈ suffix, g.op = GateOp.and ∨ g.op = GateOp.or)
    {x y : List Bool} (hxy : cutRel x y) {a b : Bool} (hab : cutLE a b) :
    cutLE (cutOutput pre suffix o x a) (cutOutput pre suffix o y b) :=
  cutRel_getD (cutRun_mono suffix hs
    (cutRel_append (cutRun_mono pre hp hxy) (.cons hab .nil))) o

lemma cut_gate_eval (pre suffix : List Gate) (g : Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨pre ++ g :: suffix, o⟩ x =
      cutOutput pre suffix o x (g.op.eval (g.inputs.map fun i => (cutRun pre x).getD i false)) := by
  simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons,
    cutOutput, cutRun]

lemma cut_not_eval (pre suffix : List Gate) (inputs : List ℕ) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, o⟩ x =
      cutOutput pre suffix o x (!(cutInput pre inputs x)) := by
  simp only [cut_gate_eval, cutInput, GateOp.eval]

lemma cut_true_eval (pre suffix : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨pre ++ ⟨GateOp.and, []⟩ :: suffix, o⟩ x =
      cutOutput pre suffix o x true := by
  simp only [cut_gate_eval, GateOp.eval, List.map_nil, List.all_nil]

lemma cut_false_eval (pre suffix : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨pre ++ ⟨GateOp.or, []⟩ :: suffix, o⟩ x =
      cutOutput pre suffix o x false := by
  simp only [cut_gate_eval, GateOp.eval, List.map_nil, List.any_nil]

lemma cut_and_inputs_eval (pre suffix : List Gate) (o : ℕ) (x : List Bool)
    (i j : ℕ) (hi : i < x.length) (hj : j < x.length) :
    Circuit.eval ⟨pre ++ ⟨GateOp.and, [i, j]⟩ :: suffix, o⟩ x =
      cutOutput pre suffix o x (x.getD i false && x.getD j false) := by
  simp only [cut_gate_eval, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, id_eq, Bool.and_true, cutRun_input pre x i hi, cutRun_input pre x j hj]

lemma cut_or_inputs_eval (pre suffix : List Gate) (o : ℕ) (x : List Bool)
    (i j : ℕ) (hi : i < x.length) (hj : j < x.length) :
    Circuit.eval ⟨pre ++ ⟨GateOp.or, [i, j]⟩ :: suffix, o⟩ x =
      cutOutput pre suffix o x (x.getD i false || x.getD j false) := by
  simp only [cut_gate_eval, GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
    List.any_nil, id_eq, Bool.or_false, cutRun_input pre x i hi, cutRun_input pre x j hj]

lemma cut_replace_true (pre suffix : List Gate) (inputs : List ℕ) (o : ℕ) (x : List Bool)
    (hs : ∀ g ∈ suffix, g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : cutLE (cutInput pre inputs x)
      (Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, o⟩ x)) :
    Circuit.eval ⟨pre ++ ⟨GateOp.and, []⟩ :: suffix, o⟩ x =
      Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, o⟩ x := by
  rw [cut_not_eval] at h ⊢
  rw [cut_true_eval]
  cases he : cutInput pre inputs x with
  | false => simp
  | true =>
    have hf := h he
    have ht := cutOutput_mono pre suffix o x hs (a := false) (b := true)
      (by intro h; cases h)
    have hf' : cutOutput pre suffix o x false = true := by simpa [he] using hf
    simpa [he] using (ht hf').trans hf'.symm

lemma cut_replace_false (pre suffix : List Gate) (inputs : List ℕ) (o : ℕ) (x : List Bool)
    (hs : ∀ g ∈ suffix, g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : cutLE (Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, o⟩ x)
      (cutInput pre inputs x)) :
    Circuit.eval ⟨pre ++ ⟨GateOp.or, []⟩ :: suffix, o⟩ x =
      Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, o⟩ x := by
  rw [cut_not_eval] at h ⊢
  rw [cut_false_eval]
  cases he : cutInput pre inputs x with
  | true => simp
  | false =>
    have ht := cutOutput_mono pre suffix o x hs (a := false) (b := true)
      (by intro h; cases h)
    cases hl : cutOutput pre suffix o x false with
    | false =>
      cases hr : cutOutput pre suffix o x true with
      | false => simp [hr]
      | true => have := h (by simpa [he] using hr); simp [he] at this
    | true => have := h (by simpa [he] using ht hl); simp [he] at this

lemma cut_replace_mono_basis (pre suffix : List Gate) (g : Gate)
    (hp : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hs : ∀ g ∈ suffix, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ k ∈ pre ++ g :: suffix,
      (k.op = GateOp.and ∨ k.op = GateOp.or) ∧ k.inputs.length ≤ 2 := by
  intro k hk
  rcases List.mem_append.mp hk with hk | hk
  · exact hp k hk
  · rcases List.mem_cons.mp hk with rfl | hk
    · exact hg
    · exact hs k hk

lemma cut_replace_length (pre suffix : List Gate) (g g' : Gate) :
    (pre ++ g :: suffix).length = (pre ++ g' :: suffix).length := by simp

lemma cut_one_not_split (gates : List Gate)
    (hb : ∀ g ∈ gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i j : Fin gates.length, (gates.get i).op = GateOp.not →
      (gates.get j).op = GateOp.not → i = j) :
    (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∨
    ∃ (pre suffix : List Gate) (inputs : List ℕ),
      gates = pre ++ ⟨GateOp.not, inputs⟩ :: suffix ∧
      (∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ g ∈ suffix, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      inputs.length ≤ 2 := by
  induction gates with
  | nil => exact Or.inl (by simp)
  | cons g gates ih =>
    have hhead := hb g List.mem_cons_self
    have hb' : ∀ k ∈ gates,
        (k.op = GateOp.and ∨ k.op = GateOp.or ∨ k.op = GateOp.not) ∧ k.inputs.length ≤ 2 :=
      fun k hk => hb k (List.mem_cons_of_mem g hk)
    by_cases hn : g.op = GateOp.not
    · refine Or.inr ⟨[], gates, g.inputs, ?_, by simp, ?_, hhead.2⟩
      · cases g with
        | mk op inputs => simp only at hn; subst op; rfl
      · intro k hk
        refine ⟨?_, (hb' k hk).2⟩
        rcases (hb' k hk).1 with ha | ho | hn'
        · exact Or.inl ha
        · exact Or.inr ho
        · obtain ⟨j, hj, he⟩ := List.mem_iff_getElem.mp hk
          have hi : (0 : ℕ) < (g :: gates).length := by simp
          have hj' : j + 1 < (g :: gates).length := by simpa using hj
          have heq := hu ⟨0, hi⟩ ⟨j + 1, hj'⟩ (by simpa using hn)
            (by simpa [he] using hn')
          have hev := congrArg Fin.val heq
          simp at hev
    · have hm : g.op = GateOp.and ∨ g.op = GateOp.or := by
        rcases hhead.1 with ha | ho | hn'
        · exact Or.inl ha
        · exact Or.inr ho
        · exact (hn hn').elim
      have hu' : ∀ i j : Fin gates.length, (gates.get i).op = GateOp.not →
          (gates.get j).op = GateOp.not → i = j := by
        intro i j hi hj
        have heq := hu ⟨i.val + 1, by simp⟩
          ⟨j.val + 1, by simp⟩ (by simpa using hi) (by simpa using hj)
        apply Fin.ext
        have hev := congrArg Fin.val heq
        simpa using hev
      rcases ih hb' hu' with hmono | ⟨pre, suffix, inputs, heq, hp, hs, hi⟩
      · exact Or.inl (fun k hk => by
          rcases List.mem_cons.mp hk with rfl | hk
          · exact ⟨hm, hhead.2⟩
          · exact hmono k hk)
      · refine Or.inr ⟨g :: pre, suffix, inputs, ?_, ?_, hs, hi⟩
        · simp [heq]
        · intro k hk
          rcases List.mem_cons.mp hk with rfl | hk
          · exact ⟨hm, hhead.2⟩
          · exact hp k hk

lemma eq_false_of_le_false : ∀ {b : Bool}, b ≤ false → b = false := by decide

lemma eq_true_of_true_le : ∀ {b : Bool}, true ≤ b → b = true := by decide

lemma and_mono : ∀ {a b c d : Bool}, a ≤ c → b ≤ d → (a && b) ≤ (c && d) := by
  decide

def edgeFun (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) ||
  (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) ||
  (x 1 && x 5) || (x 3 && x 5) || (x 0 && x 6) ||
  (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6)

def edgePairs : List (Fin 7 × Fin 7) :=
  [(0, 2), (1, 3), (0, 4), (1, 4), (2, 4), (0, 5),
   (1, 5), (3, 5), (0, 6), (2, 6), (3, 6), (5, 6)]

def nonedgePairs : List (Fin 7 × Fin 7) :=
  [(0, 1), (0, 3), (1, 2), (1, 6), (2, 3), (2, 5), (3, 4), (4, 5), (4, 6)]

def pairPoint (p : Fin 7 × Fin 7) : Fin 7 → Bool :=
  fun i => decide (i = p.1 ∨ i = p.2)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma true_iff_contains_edge : ∀ x : Fin 7 → Bool,
    edgeFun x = true ↔ ∃ p ∈ edgePairs, pairPoint p ≤ x := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma false_iff_below_nonedge : ∀ x : Fin 7 → Bool,
    edgeFun x = false ↔ ∃ p ∈ nonedgePairs, x ≤ pairPoint p := by
  decide

lemma edgePoint_true : ∀ p ∈ edgePairs, edgeFun (pairPoint p) = true := by
  decide

lemma nonedgePoint_false : ∀ p ∈ nonedgePairs, edgeFun (pairPoint p) = false := by
  decide

lemma edgeFun_mono : Monotone edgeFun := by
  intro x y hxy
  cases hx : edgeFun x with
  | false => simp
  | true =>
    obtain ⟨p, hp, hpx⟩ := (true_iff_contains_edge x).1 hx
    have hy := (true_iff_contains_edge y).2 ⟨p, hp, le_trans hpx hxy⟩
    simp [hy]

lemma mono_eq_edgeFun_of_pairs (g : (Fin 7 → Bool) → Bool) (hg : Monotone g)
    (he : ∀ p ∈ edgePairs, g (pairPoint p) = true)
    (hn : ∀ p ∈ nonedgePairs, g (pairPoint p) = false) : g = edgeFun := by
  funext x
  cases hx : edgeFun x with
  | false =>
    obtain ⟨p, hp, hxp⟩ := (false_iff_below_nonedge x).1 hx
    have hle := hg hxp
    exact eq_false_of_le_false (by simpa [hn p hp] using hle)
  | true =>
    obtain ⟨p, hp, hpx⟩ := (true_iff_contains_edge x).1 hx
    have hle := hg hpx
    exact eq_true_of_true_le (by simpa [he p hp] using hle)

lemma mono_le_edgeFun_iff (h : (Fin 7 → Bool) → Bool) (hm : Monotone h) :
    h ≤ edgeFun ↔ ∀ p ∈ nonedgePairs, h (pairPoint p) = false := by
  constructor
  · intro hh p hp
    have := hh (pairPoint p)
    exact eq_false_of_le_false (by simpa [nonedgePoint_false p hp] using this)
  · intro hh x
    cases hx : edgeFun x with
    | true => simp
    | false =>
      obtain ⟨p, hp, hxp⟩ := (false_iff_below_nonedge x).1 hx
      have := hm hxp
      simpa [hh p hp] using this

lemma edgeFun_le_mono_iff (h : (Fin 7 → Bool) → Bool) (hm : Monotone h) :
    edgeFun ≤ h ↔ ∀ p ∈ edgePairs, h (pairPoint p) = true := by
  constructor
  · intro hh p hp
    have := hh (pairPoint p)
    exact eq_true_of_true_le (by simpa [edgePoint_true p hp] using this)
  · intro hh x
    cases hx : edgeFun x with
    | false => simp
    | true =>
      obtain ⟨p, hp, hpx⟩ := (true_iff_contains_edge x).1 hx
      have := hm hpx
      simpa [hh p hp] using this

lemma monotone_cut_replacement
    (F : (Fin 7 → Bool) → Bool → Bool) (h r : (Fin 7 → Bool) → Bool)
    (hFx : ∀ z, Monotone (fun x => F x z))
    (hFz : ∀ x, Monotone (F x)) (hr : Monotone r)
    (hdiag : ∀ x, F x (!h x) = edgeFun x)
    (he : ∀ p ∈ edgePairs, F (pairPoint p) false = false → r (pairPoint p) = true)
    (hn : ∀ p ∈ nonedgePairs, F (pairPoint p) true = true → r (pairPoint p) = false) :
    ∀ x, F x (r x) = edgeFun x := by
  have hmono : Monotone (fun x => F x (r x)) := by
    intro x y hxy
    exact le_trans (hFx (r x) hxy) (hFz y (hr hxy))
  have hh := mono_eq_edgeFun_of_pairs (fun x => F x (r x)) hmono ?_ ?_
  · exact fun x => congrFun hh x
  · intro p hp
    have hd := hdiag (pairPoint p)
    rw [edgePoint_true p hp] at hd
    have hz := hFz (pairPoint p)
    cases ha : F (pairPoint p) false with
    | false =>
      rw [he p hp ha]
      have hle := hz (show (!h (pairPoint p)) ≤ true by simp)
      exact eq_true_of_true_le (by simpa [hd] using hle)
    | true =>
      have hle := hz (show false ≤ r (pairPoint p) by simp)
      exact eq_true_of_true_le (by simpa [ha] using hle)
  · intro p hp
    have hd := hdiag (pairPoint p)
    rw [nonedgePoint_false p hp] at hd
    have hz := hFz (pairPoint p)
    cases hb : F (pairPoint p) true with
    | false =>
      have hle := hz (show r (pairPoint p) ≤ true by simp)
      exact eq_false_of_le_false (by simpa [hb] using hle)
    | true =>
      rw [hn p hp hb]
      have hle := hz (show false ≤ !h (pairPoint p) by simp)
      exact eq_false_of_le_false (by simpa [hd] using hle)

lemma pair_product_false_on_nonedge : ∀ e ∈ edgePairs, ∀ p ∈ nonedgePairs,
    (pairPoint p e.1 && pairPoint p e.2) = false := by
  decide

lemma pair_product_self : ∀ e ∈ edgePairs,
    (pairPoint e e.1 && pairPoint e e.2) = true := by
  decide

lemma single_missing_edge_replacement
    (F : (Fin 7 → Bool) → Bool → Bool) (h : (Fin 7 → Bool) → Bool)
    (hFx : ∀ z, Monotone (fun x => F x z))
    (hFz : ∀ x, Monotone (F x))
    (hdiag : ∀ x, F x (!h x) = edgeFun x)
    (e : Fin 7 × Fin 7) (he : e ∈ edgePairs)
    (hmiss : ∀ p ∈ edgePairs, F (pairPoint p) false = false → p = e) :
    ∀ x, F x (x e.1 && x e.2) = edgeFun x := by
  apply monotone_cut_replacement F h (fun x => x e.1 && x e.2) hFx hFz
  · intro x y hxy
    exact and_mono (hxy e.1) (hxy e.2)
  · exact hdiag
  · intro p hp hf
    rw [hmiss p hp hf]
    exact pair_product_self e he
  · intro p hp _
    exact pair_product_false_on_nonedge e he p hp

lemma cut_replacement_necessary
    (F : (Fin 7 → Bool) → Bool → Bool) (r : (Fin 7 → Bool) → Bool)
    (hvalid : ∀ x, F x (r x) = edgeFun x) :
    (∀ p ∈ edgePairs, F (pairPoint p) false = false → r (pairPoint p) = true) ∧
    (∀ p ∈ nonedgePairs, F (pairPoint p) true = true → r (pairPoint p) = false) := by
  constructor
  · intro p hp hf
    have hv := hvalid (pairPoint p)
    have ht := edgePoint_true p hp
    cases hr : r (pairPoint p) <;> simp_all
  · intro p hp hf
    have hv := hvalid (pairPoint p)
    have ht := nonedgePoint_false p hp
    cases hr : r (pairPoint p) <;> simp_all

lemma cut_replacement_iff
    (F : (Fin 7 → Bool) → Bool → Bool) (h r : (Fin 7 → Bool) → Bool)
    (hFx : ∀ z, Monotone (fun x => F x z))
    (hFz : ∀ x, Monotone (F x)) (hr : Monotone r)
    (hdiag : ∀ x, F x (!h x) = edgeFun x) :
    (∀ x, F x (r x) = edgeFun x) ↔
    (∀ p ∈ edgePairs, F (pairPoint p) false = false → r (pairPoint p) = true) ∧
    (∀ p ∈ nonedgePairs, F (pairPoint p) true = true → r (pairPoint p) = false) := by
  constructor
  · exact cut_replacement_necessary F r
  · rintro ⟨he, hn⟩
    exact monotone_cut_replacement F h r hFx hFz hr hdiag he hn

def postedEdgeFun (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2,
    (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
lemma edgeFun_eq_posted : ∀ x : Fin 7 → Bool, edgeFun x = postedEdgeFun x := by
  decide

lemma cutLE_iff_bool_le (a b : Bool) : cutLE a b ↔ a ≤ b := by
  unfold cutLE
  cases a <;> cases b <;> decide

lemma cutOutput_fn_x_mono (pre suffix : List Gate) (o : ℕ)
    (hp : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hs : ∀ g ∈ suffix, g.op = GateOp.and ∨ g.op = GateOp.or) (z : Bool) :
    Monotone (fun x : Fin 7 → Bool => cutOutput pre suffix o (List.ofFn x) z) := by
  intro x y hxy
  apply (cutLE_iff_bool_le _ _).1
  exact cutOutput_inputs_mono pre suffix o hp hs
    (cutRel_ofFn (fun i => (cutLE_iff_bool_le _ _).2 (hxy i))) (fun h => h)

lemma cutOutput_fn_z_mono (pre suffix : List Gate) (o : ℕ)
    (hs : ∀ g ∈ suffix, g.op = GateOp.and ∨ g.op = GateOp.or) (x : Fin 7 → Bool) :
    Monotone (cutOutput pre suffix o (List.ofFn x)) := by
  intro a b hab
  exact (cutLE_iff_bool_le _ _).1
    (cutOutput_mono pre suffix o (List.ofFn x) hs ((cutLE_iff_bool_le _ _).2 hab))

lemma cut_replace_one_missing (pre suffix : List Gate) (inputs : List ℕ) (o : ℕ)
    (hp : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hs : ∀ g ∈ suffix, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hf : ∀ x : Fin 7 → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, o⟩ (List.ofFn x) = edgeFun x)
    (e : Fin 7 × Fin 7) (he : e ∈ edgePairs)
    (hmiss : ∀ p ∈ edgePairs,
      Circuit.eval ⟨pre ++ ⟨GateOp.or, []⟩ :: suffix, o⟩ (List.ofFn (pairPoint p)) = false →
      p = e) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ (pre ++ ⟨GateOp.not, inputs⟩ :: suffix).length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = edgeFun x := by
  have hp' := fun g hg => (hp g hg).1
  have hs' := fun g hg => (hs g hg).1
  have hrep := single_missing_edge_replacement
    (fun x => cutOutput pre suffix o (List.ofFn x))
    (fun x => cutInput pre inputs (List.ofFn x))
    (cutOutput_fn_x_mono pre suffix o hp' hs')
    (cutOutput_fn_z_mono pre suffix o hs')
    (fun x => by simpa only [cut_not_eval] using hf x) e he
    (fun p hp hf => hmiss p hp (by simpa only [cut_false_eval] using hf))
  refine ⟨pre ++ ⟨GateOp.and, [e.1.val, e.2.val]⟩ :: suffix, o,
    cut_replace_mono_basis pre suffix _ hp hs ⟨Or.inl rfl, by simp⟩, ?_, ?_⟩
  · simp
  · intro x
    rw [cut_and_inputs_eval pre suffix o (List.ofFn x) e.1.val e.2.val
      (by simp) (by simp)]
    have hx (i : Fin 7) : (List.ofFn x).getD i.val false = x i := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp)]
      simp only [Option.getD_some, List.getElem_ofFn]
    rw [hx e.1, hx e.2]
    exact hrep x

lemma cut_replace_at_most_one_missing (gates : List Gate) (o : ℕ)
    (hb : ∀ g ∈ gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i j : Fin gates.length, (gates.get i).op = GateOp.not →
      (gates.get j).op = GateOp.not → i = j)
    (hf : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = edgeFun x)
    (hlocal : ∀ (pre suffix : List Gate) (inputs : List ℕ),
      gates = pre ++ ⟨GateOp.not, inputs⟩ :: suffix →
      ∃ e ∈ edgePairs, ∀ p ∈ edgePairs,
        Circuit.eval ⟨pre ++ ⟨GateOp.or, []⟩ :: suffix, o⟩ (List.ofFn (pairPoint p)) = false →
        p = e) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = edgeFun x := by
  rcases cut_one_not_split gates hb hu with hm | ⟨pre, suffix, inputs, heq, hp, hs, _⟩
  · exact ⟨gates, o, hm, le_rfl, hf⟩
  · obtain ⟨e, he, hm⟩ := hlocal pre suffix inputs heq
    subst gates
    exact cut_replace_one_missing pre suffix inputs o hp hs hf e he hm

lemma cut_replace_at_most_one_missing_posted (gates : List Gate) (o : ℕ)
    (hb : ∀ g ∈ gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i j : Fin gates.length, (gates.get i).op = GateOp.not →
      (gates.get j).op = GateOp.not → i = j)
    (hf : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = postedEdgeFun x)
    (hlocal : ∀ (pre suffix : List Gate) (inputs : List ℕ),
      gates = pre ++ ⟨GateOp.not, inputs⟩ :: suffix →
      ∃ e ∈ edgePairs, ∀ p ∈ edgePairs,
        Circuit.eval ⟨pre ++ ⟨GateOp.or, []⟩ :: suffix, o⟩ (List.ofFn (pairPoint p)) = false →
        p = e) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = postedEdgeFun x := by
  have hf' : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = edgeFun x :=
    fun x => (hf x).trans (edgeFun_eq_posted x).symm
  obtain ⟨gates', o', hb', hl', hf'⟩ := cut_replace_at_most_one_missing gates o hb hu hf' hlocal
  exact ⟨gates', o', hb', hl', fun x => (hf' x).trans (edgeFun_eq_posted x)⟩

lemma cutGateFn_mono (pre : List Gate) (g : Gate)
    (hp : ∀ k ∈ pre, k.op = GateOp.and ∨ k.op = GateOp.or)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or) :
    Monotone (fun x : Fin 7 → Bool =>
      g.op.eval (g.inputs.map fun i => (cutRun pre (List.ofFn x)).getD i false)) := by
  intro x y hxy
  exact (cutLE_iff_bool_le _ _).1
    (cutGate_mono (cutRun_mono pre hp
      (cutRel_ofFn (fun i => (cutLE_iff_bool_le _ _).2 (hxy i)))) g hg)

lemma cut_replace_gate_separator (pre suffix : List Gate) (inputs : List ℕ) (o : ℕ)
    (g : Gate)
    (hp : ∀ k ∈ pre, (k.op = GateOp.and ∨ k.op = GateOp.or) ∧ k.inputs.length ≤ 2)
    (hs : ∀ k ∈ suffix, (k.op = GateOp.and ∨ k.op = GateOp.or) ∧ k.inputs.length ≤ 2)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hf : ∀ x : Fin 7 → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, o⟩ (List.ofFn x) = postedEdgeFun x)
    (he : ∀ p ∈ edgePairs,
      Circuit.eval ⟨pre ++ ⟨GateOp.or, []⟩ :: suffix, o⟩ (List.ofFn (pairPoint p)) = false →
      g.op.eval (g.inputs.map fun i =>
        (cutRun pre (List.ofFn (pairPoint p))).getD i false) = true)
    (hn : ∀ p ∈ nonedgePairs,
      Circuit.eval ⟨pre ++ ⟨GateOp.and, []⟩ :: suffix, o⟩ (List.ofFn (pairPoint p)) = true →
      g.op.eval (g.inputs.map fun i =>
        (cutRun pre (List.ofFn (pairPoint p))).getD i false) = false) :
    (∀ k ∈ pre ++ g :: suffix,
      (k.op = GateOp.and ∨ k.op = GateOp.or) ∧ k.inputs.length ≤ 2) ∧
    (pre ++ g :: suffix).length = (pre ++ ⟨GateOp.not, inputs⟩ :: suffix).length ∧
    ∀ x : Fin 7 → Bool,
      Circuit.eval ⟨pre ++ g :: suffix, o⟩ (List.ofFn x) = postedEdgeFun x := by
  have hp' := fun k hk => (hp k hk).1
  have hs' := fun k hk => (hs k hk).1
  have hrep := monotone_cut_replacement
    (fun x => cutOutput pre suffix o (List.ofFn x))
    (fun x => cutInput pre inputs (List.ofFn x))
    (fun x => g.op.eval (g.inputs.map fun i => (cutRun pre (List.ofFn x)).getD i false))
    (cutOutput_fn_x_mono pre suffix o hp' hs')
    (cutOutput_fn_z_mono pre suffix o hs')
    (cutGateFn_mono pre g hp' hg.1)
    (fun x => by simpa only [cut_not_eval] using (hf x).trans (edgeFun_eq_posted x).symm)
    (fun p hp hf => he p hp (by simpa only [cut_false_eval] using hf))
    (fun p hp hf => hn p hp (by simpa only [cut_true_eval] using hf))
  refine ⟨cut_replace_mono_basis pre suffix g hp hs hg,
    cut_replace_length pre suffix g ⟨GateOp.not, inputs⟩, ?_⟩
  intro x
  rw [cut_gate_eval]
  exact (hrep x).trans (edgeFun_eq_posted x)

lemma one_not_drop_forces {α : Type*} [Preorder α]
    (h : α → Bool) (F : α → Bool → Bool)
    (hFx : ∀ z, Monotone (fun x => F x z))
    (hFz : ∀ x, Monotone (F x))
    {p q : α} (hpq : p ≤ q)
    (hp : F p (!h p) = true) (hq : F q (!h q) = false) :
    h p = false ∧ h q = true := by
  have hn : ¬ ((!h p) ≤ (!h q)) := by
    intro hab
    have hle := le_trans (hFx (!h p) hpq) (hFz q hab)
    have hbad : (true : Bool) ≤ false := by simpa [hp, hq] using hle
    exact (by decide : ¬ ((true : Bool) ≤ false)) hbad
  cases ha : h p <;> cases hb : h q <;> simp_all

lemma one_not_no_two_decreases {α : Type*} [Preorder α]
    (h : α → Bool) (F : α → Bool → Bool)
    (hh : Monotone h)
    (hFx : ∀ z, Monotone (fun x => F x z))
    (hFz : ∀ x, Monotone (F x))
    {p q r s : α} (hpq : p ≤ q) (hqr : q ≤ r) (hrs : r ≤ s) :
    ¬ (F p (!h p) = true ∧ F q (!h q) = false ∧
      F r (!h r) = true ∧ F s (!h s) = false) := by
  rintro ⟨hp, hq, hr, hs⟩
  have hfirst := one_not_drop_forces h F hFx hFz hpq hp hq
  have hsecond := one_not_drop_forces h F hFx hFz hrs hr hs
  have hm := hh hqr
  have hbad : (true : Bool) ≤ false := by simpa [hfirst.2, hsecond.1] using hm
  exact (by decide : ¬ ((true : Bool) ≤ false)) hbad

lemma cutInput_fn_mono {n : ℕ} (pre : List Gate) (inputs : List ℕ)
    (hp : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or) :
    Monotone (fun x : Fin n → Bool => cutInput pre inputs (List.ofFn x)) := by
  intro x y hxy
  exact (cutLE_iff_bool_le _ _).1
    (cutInput_mono pre inputs hp
      (cutRel_ofFn (fun i => (cutLE_iff_bool_le _ _).2 (hxy i))))

lemma cut_circuit_no_two_decreases {n : ℕ} (gates : List Gate) (o : ℕ)
    (hb : ∀ g ∈ gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i j : Fin gates.length, (gates.get i).op = GateOp.not →
      (gates.get j).op = GateOp.not → i = j)
    {p q r s : Fin n → Bool} (hpq : p ≤ q) (hqr : q ≤ r) (hrs : r ≤ s) :
    ¬ (Circuit.eval ⟨gates, o⟩ (List.ofFn p) = true ∧
      Circuit.eval ⟨gates, o⟩ (List.ofFn q) = false ∧
      Circuit.eval ⟨gates, o⟩ (List.ofFn r) = true ∧
      Circuit.eval ⟨gates, o⟩ (List.ofFn s) = false) := by
  rintro ⟨hp, hq, hr, hs⟩
  rcases cut_one_not_split gates hb hu with hm | ⟨pre, suffix, inputs, heq, hpre, hsuffix, _⟩
  · have hmono := cutRel_getD (cutRun_mono gates (fun g hg => (hm g hg).1)
      (cutRel_ofFn (fun i => (cutLE_iff_bool_le _ _).2 (hpq i)))) o
    have hmono' : cutLE (Circuit.eval ⟨gates, o⟩ (List.ofFn p))
        (Circuit.eval ⟨gates, o⟩ (List.ofFn q)) := by
      simpa only [Circuit.eval, Circuit.wires, cutRun] using hmono
    have he := hmono' hp
    simp [hq] at he
  · subst gates
    have hpre' := fun g hg => (hpre g hg).1
    have hsuffix' := fun g hg => (hsuffix g hg).1
    have hFx : ∀ z, Monotone
        (fun x : Fin n → Bool => cutOutput pre suffix o (List.ofFn x) z) := by
      intro z x y hxy
      exact (cutLE_iff_bool_le _ _).1
        (cutOutput_inputs_mono pre suffix o hpre' hsuffix'
          (cutRel_ofFn (fun i => (cutLE_iff_bool_le _ _).2 (hxy i))) (fun h => h))
    have hFz : ∀ x : Fin n → Bool, Monotone (cutOutput pre suffix o (List.ofFn x)) := by
      intro x a b hab
      exact (cutLE_iff_bool_le _ _).1
        (cutOutput_mono pre suffix o (List.ofFn x) hsuffix' ((cutLE_iff_bool_le _ _).2 hab))
    apply one_not_no_two_decreases
      (fun x : Fin n → Bool => cutInput pre inputs (List.ofFn x))
      (fun x : Fin n → Bool => cutOutput pre suffix o (List.ofFn x))
      (cutInput_fn_mono pre inputs hpre') hFx hFz hpq hqr hrs
    simpa only [cut_not_eval] using And.intro hp (And.intro hq (And.intro hr hs))

def fourRowLE {w : ℕ} (ws : List (BitVec w)) (i j : Fin w) : Prop :=
  ∀ v ∈ ws, v.getLsbD i.val ≤ v.getLsbD j.val

def fourLow {w : ℕ} (ws : List (BitVec w)) (t : BitVec w) (q : Fin w) : BitVec w :=
  ws.foldl (fun acc v => if v.getLsbD q.val then acc else acc &&& ~~~v) t

def fourUp {w : ℕ} (ws : List (BitVec w)) (t : BitVec w) (q : Fin w) : BitVec w :=
  ws.foldl (fun acc v => if v.getLsbD q.val then acc &&& v else acc) t

def fourDropPos {w : ℕ} (ws : List (BitVec w)) (t : BitVec w) : BitVec w :=
  (List.finRange w).foldl
    (fun acc q => acc ||| (if t.getLsbD q.val then 0 else fourLow ws t q)) 0

def fourBlocked {w : ℕ} (ws : List (BitVec w)) (t : BitVec w) : Bool :=
  let dp := fourDropPos ws t
  (List.finRange w).any (fun q => !t.getLsbD q.val &&
    decide (fourLow ws t q ≠ 0) && decide (fourUp ws t q &&& dp ≠ 0))

lemma fourLow_bit_iff {w : ℕ} (ws : List (BitVec w)) (t : BitVec w) (q i : Fin w) :
    (fourLow ws t q).getLsbD i.val = true ↔
      t.getLsbD i.val = true ∧ fourRowLE ws i q := by
  induction ws generalizing t with
  | nil => simp [fourLow, fourRowLE]
  | cons v ws ih =>
    change (fourLow ws (if v.getLsbD q.val then t else t &&& ~~~v) q).getLsbD i.val = true ↔ _
    rw [ih]
    cases hq : v.getLsbD q.val <;> cases hi : v.getLsbD i.val <;>
      simp only [fourRowLE, List.forall_mem_cons, hq, hi,
        Bool.false_eq_true, ite_false, ite_true,
        BitVec.getLsbD_and, BitVec.getLsbD_not, i.isLt, decide_true, Bool.true_and] <;>
      simp

lemma fourUp_bit_iff {w : ℕ} (ws : List (BitVec w)) (t : BitVec w) (q i : Fin w) :
    (fourUp ws t q).getLsbD i.val = true ↔
      t.getLsbD i.val = true ∧ fourRowLE ws q i := by
  induction ws generalizing t with
  | nil => simp [fourUp, fourRowLE]
  | cons v ws ih =>
    change (fourUp ws (if v.getLsbD q.val then t &&& v else t) q).getLsbD i.val = true ↔ _
    rw [ih]
    cases hq : v.getLsbD q.val <;> cases hi : v.getLsbD i.val <;>
      simp only [fourRowLE, List.forall_mem_cons, hq, hi,
        Bool.false_eq_true, ite_false, ite_true, BitVec.getLsbD_and] <;>
      simp

lemma fourOrFold_bit_iff {w : ℕ} (qs : List (Fin w)) (f : Fin w → BitVec w)
    (acc : BitVec w) (i : Fin w) :
    (qs.foldl (fun acc q => acc ||| f q) acc).getLsbD i.val = true ↔
      acc.getLsbD i.val = true ∨ ∃ q ∈ qs, (f q).getLsbD i.val = true := by
  induction qs generalizing acc with
  | nil => simp
  | cons q qs ih =>
    rw [List.foldl_cons, ih]
    simp [or_assoc]

lemma fourDropPos_bit_iff {w : ℕ} (ws : List (BitVec w)) (t : BitVec w) (i : Fin w) :
    (fourDropPos ws t).getLsbD i.val = true ↔
      ∃ s : Fin w, t.getLsbD s.val = false ∧
        t.getLsbD i.val = true ∧ fourRowLE ws i s := by
  rw [fourDropPos, fourOrFold_bit_iff]
  simp only [BitVec.ofNat_eq_ofNat, BitVec.getLsbD_zero, Bool.false_eq_true, false_or,
    List.mem_finRange, true_and]
  apply exists_congr
  intro s
  cases hs : t.getLsbD s.val <;>
    simp only [Bool.false_eq_true,
      Bool.true_eq_false, ite_false, ite_true, BitVec.getLsbD_zero, fourLow_bit_iff, true_and, false_and]

lemma four_exists_bit_of_ne_zero {w : ℕ} (v : BitVec w) (hv : v ≠ 0) :
    ∃ i : Fin w, v.getLsbD i.val = true := by
  by_contra hn
  apply hv
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hb : v.getLsbD i ≠ true := fun h => hn ⟨⟨i, hi⟩, h⟩
  cases he : v.getLsbD i <;> simp_all

lemma fourBlocked_chain {w : ℕ} (ws : List (BitVec w)) (t : BitVec w)
    (hb : fourBlocked ws t = true) :
    ∃ p q r s : Fin w,
      fourRowLE ws p q ∧ fourRowLE ws q r ∧ fourRowLE ws r s ∧
      t.getLsbD p.val = true ∧ t.getLsbD q.val = false ∧
      t.getLsbD r.val = true ∧ t.getLsbD s.val = false := by
  simp only [fourBlocked, List.any_eq_true, Bool.and_eq_true, Bool.not_eq_true',
    decide_eq_true_eq] at hb
  obtain ⟨q, _, ⟨hq, hl⟩, hu⟩ := hb
  obtain ⟨p, hp⟩ := four_exists_bit_of_ne_zero (fourLow ws t q) hl
  obtain ⟨r, hr⟩ := four_exists_bit_of_ne_zero (fourUp ws t q &&& fourDropPos ws t) hu
  have hlow := (fourLow_bit_iff ws t q p).1 hp
  rw [BitVec.getLsbD_and, Bool.and_eq_true] at hr
  have hup := (fourUp_bit_iff ws t q r).1 hr.1
  obtain ⟨s, hs, _, hrs⟩ := (fourDropPos_bit_iff ws t r).1 hr.2
  exact ⟨p, q, r, s, hlow.2, hup.2, hrs, hlow.1, hq, hup.1, hs⟩

def fourPattern {w : ℕ} (ws : List (BitVec w)) (q : Fin w) : Fin ws.length → Bool :=
  fun i => (ws.get i).getLsbD q.val

lemma fourPattern_mono {w : ℕ} (ws : List (BitVec w)) {p q : Fin w}
    (h : fourRowLE ws p q) : fourPattern ws p ≤ fourPattern ws q := by
  intro i
  exact h (ws.get i) (List.get_mem ws i)

lemma fourBlocked_no_continuation {w : ℕ} (ws : List (BitVec w)) (t : BitVec w)
    (hblocked : fourBlocked ws t = true) (gates : List Gate) (o : ℕ)
    (hb : ∀ g ∈ gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (hu : ∀ i j : Fin gates.length, (gates.get i).op = GateOp.not →
      (gates.get j).op = GateOp.not → i = j)
    (hf : ∀ q : Fin w, Circuit.eval ⟨gates, o⟩ (List.ofFn (fourPattern ws q)) =
      t.getLsbD q.val) : False := by
  obtain ⟨p, q, r, s, hpq, hqr, hrs, hp, hq, hr, hs⟩ := fourBlocked_chain ws t hblocked
  exact cut_circuit_no_two_decreases gates o hb hu
    (fourPattern_mono ws hpq) (fourPattern_mono ws hqr) (fourPattern_mono ws hrs)
    ⟨(hf p).trans hp, (hf q).trans hq, (hf r).trans hr, (hf s).trans hs⟩

lemma suffix_cutRun_length (gates : List Gate) (w : List Bool) :
    (cutRun gates w).length = w.length + gates.length := by
  induction gates generalizing w with
  | nil => simp [cutRun]
  | cons g gates ih =>
    change (cutRun gates (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma suffix_append_last (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

lemma suffix_append_irrel (w : List Bool) (a b : Bool) (i : ℕ) (hi : i ≠ w.length) :
    (w ++ [a]).getD i false = (w ++ [b]).getD i false := by
  by_cases hlt : i < w.length
  · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hlt]
  · have hla : (w ++ [a]).length ≤ i := by simp; omega
    have hlb : (w ++ [b]).length ≤ i := by simp; omega
    rw [List.getD_eq_default _ _ hla, List.getD_eq_default _ _ hlb]

lemma suffix_cutOutput_nil (pre : List Gate) (x : List Bool) (z : Bool) :
    cutOutput pre [] (x.length + pre.length) x z = z := by
  change (cutRun pre x ++ [z]).getD (x.length + pre.length) false = z
  rw [← suffix_cutRun_length pre x]
  exact suffix_append_last _ _

lemma suffix_cutOutput_last (pre : List Gate) (g : Gate) (x : List Bool) (z : Bool) :
    cutOutput pre [g] (x.length + pre.length + 1) x z =
      g.op.eval (g.inputs.map fun i => (cutRun pre x ++ [z]).getD i false) := by
  change ((cutRun pre x ++ [z]) ++
    [g.op.eval (g.inputs.map fun i => (cutRun pre x ++ [z]).getD i false)]).getD
    (x.length + pre.length + 1) false = _
  have hl : (cutRun pre x ++ [z]).length = x.length + pre.length + 1 := by
    simp [suffix_cutRun_length]
  rw [← hl]
  exact suffix_append_last _ _

lemma suffix_cutOutput_unread (pre : List Gate) (g : Gate) (x : List Bool) (a b : Bool)
    (hn : x.length + pre.length ∉ g.inputs) :
    cutOutput pre [g] (x.length + pre.length + 1) x a =
      cutOutput pre [g] (x.length + pre.length + 1) x b := by
  rw [suffix_cutOutput_last, suffix_cutOutput_last]
  apply congrArg g.op.eval
  apply List.map_congr_left
  intro i hi
  apply suffix_append_irrel
  rw [suffix_cutRun_length]
  intro heq
  exact hn (heq ▸ hi)

lemma suffix_cutOutput_and_read (pre : List Gate) (g : Gate) (x : List Bool) (z : Bool)
    (hg : g.op = GateOp.and) (hm : x.length + pre.length ∈ g.inputs)
    (he : cutOutput pre [g] (x.length + pre.length + 1) x z = true) : z = true := by
  rw [suffix_cutOutput_last, hg] at he
  change (g.inputs.map fun i => (cutRun pre x ++ [z]).getD i false).all id = true at he
  have hh := List.all_eq_true.mp he
  apply hh z
  apply List.mem_map.mpr
  refine ⟨x.length + pre.length, hm, ?_⟩
  rw [← suffix_cutRun_length pre x]
  exact suffix_append_last _ _

lemma suffix_cutOutput_or_read (pre : List Gate) (g : Gate) (x : List Bool) (z : Bool)
    (hg : g.op = GateOp.or) (hm : x.length + pre.length ∈ g.inputs)
    (he : cutOutput pre [g] (x.length + pre.length + 1) x z = false) : z = false := by
  rw [suffix_cutOutput_last, hg] at he
  change (g.inputs.map fun i => (cutRun pre x ++ [z]).getD i false).any id = false at he
  cases hz : z with
  | false => rfl
  | true =>
    have hmem : true ∈ g.inputs.map (fun i => (cutRun pre x ++ [z]).getD i false) := by
      apply List.mem_map.mpr
      refine ⟨x.length + pre.length, hm, ?_⟩
      rw [← suffix_cutRun_length pre x, suffix_append_last, hz]
    have ht : (g.inputs.map fun i => (cutRun pre x ++ [z]).getD i false).any id = true :=
      List.any_eq_true.mpr ⟨true, hmem, rfl⟩
    have hbad : false = true := he.symm.trans ht
    cases hbad

lemma suffix_cutInput_false_of_top {n : ℕ} (pre : List Gate) (inputs : List ℕ)
    (hp : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (ht : cutInput pre inputs (List.ofFn (fun _ : Fin n => true)) = false) :
    ∀ x : Fin n → Bool, cutInput pre inputs (List.ofFn x) = false := by
  intro x
  cases hx : cutInput pre inputs (List.ofFn x) with
  | false => rfl
  | true =>
    have hmono := cutInput_mono pre inputs hp
      (cutRel_ofFn (x := x) (y := fun _ : Fin n => true) (fun i _ => rfl))
    have he := hmono hx
    have hbad : false = true := ht.symm.trans he
    cases hbad

lemma suffix_cutInput_true_of_bottom {n : ℕ} (pre : List Gate) (inputs : List ℕ)
    (hp : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hb : cutInput pre inputs (List.ofFn (fun _ : Fin n => false)) = true) :
    ∀ x : Fin n → Bool, cutInput pre inputs (List.ofFn x) = true := by
  intro x
  have hmono := cutInput_mono pre inputs hp
    (cutRel_ofFn (x := fun _ : Fin n => false) (y := x) (fun i he => by cases he))
  exact hmono hb

lemma suffix_one_replace_last {n : ℕ} (pre : List Gate) (inputs : List ℕ) (g : Gate)
    (hp : ∀ k ∈ pre, k.op = GateOp.and ∨ k.op = GateOp.or)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hf0 : Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: [g], n + pre.length + 1⟩
      (List.ofFn (fun _ : Fin n => false)) = false)
    (hf1 : Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: [g], n + pre.length + 1⟩
      (List.ofFn (fun _ : Fin n => true)) = true) :
    (∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.and, []⟩ :: [g], n + pre.length + 1⟩ (List.ofFn x) =
      Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: [g], n + pre.length + 1⟩ (List.ofFn x)) ∨
    (∀ x : Fin n → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.or, []⟩ :: [g], n + pre.length + 1⟩ (List.ofFn x) =
      Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: [g], n + pre.length + 1⟩ (List.ofFn x)) := by
  by_cases hn : n + pre.length ∈ g.inputs
  · rcases hg with hg | hg
    · have he := suffix_cutOutput_and_read pre g (List.ofFn (fun _ : Fin n => true))
        (!(cutInput pre inputs (List.ofFn (fun _ : Fin n => true)))) hg
        (by simpa using hn) (by simpa only [List.length_ofFn, cut_not_eval] using hf1)
      have ht : cutInput pre inputs (List.ofFn (fun _ : Fin n => true)) = false := by
        cases hh : cutInput pre inputs (List.ofFn (fun _ : Fin n => true)) <;> simp_all
      have hc := suffix_cutInput_false_of_top pre inputs hp ht
      exact Or.inl (fun x => by rw [cut_true_eval, cut_not_eval]; simp [hc x])
    · have he := suffix_cutOutput_or_read pre g (List.ofFn (fun _ : Fin n => false))
        (!(cutInput pre inputs (List.ofFn (fun _ : Fin n => false)))) hg
        (by simpa using hn) (by simpa only [List.length_ofFn, cut_not_eval] using hf0)
      have hb : cutInput pre inputs (List.ofFn (fun _ : Fin n => false)) = true := by
        cases hh : cutInput pre inputs (List.ofFn (fun _ : Fin n => false)) <;> simp_all
      have hc := suffix_cutInput_true_of_bottom pre inputs hp hb
      exact Or.inr (fun x => by rw [cut_false_eval, cut_not_eval]; simp [hc x])
  · right
    intro x
    rw [cut_false_eval, cut_not_eval]
    simpa only [List.length_ofFn] using suffix_cutOutput_unread pre g (List.ofFn x)
      false (!(cutInput pre inputs (List.ofFn x))) (by simpa using hn)

lemma suffix_cutOutput_nil_fn {n : ℕ} (pre : List Gate) (x : Fin n → Bool) (z : Bool) :
    cutOutput pre [] (n + pre.length) (List.ofFn x) z = z := by
  simpa only [List.length_ofFn] using suffix_cutOutput_nil pre (List.ofFn x) z

lemma suffix_zero_last_impossible {n : ℕ} (pre : List Gate) (inputs : List ℕ)
    (hp : ∀ k ∈ pre, k.op = GateOp.and ∨ k.op = GateOp.or)
    (hf0 : Circuit.eval ⟨pre ++ [⟨GateOp.not, inputs⟩], n + pre.length⟩
      (List.ofFn (fun _ : Fin n => false)) = false)
    (hf1 : Circuit.eval ⟨pre ++ [⟨GateOp.not, inputs⟩], n + pre.length⟩
      (List.ofFn (fun _ : Fin n => true)) = true) : False := by
  rw [cut_not_eval, suffix_cutOutput_nil_fn] at hf0 hf1
  have hb : cutInput pre inputs (List.ofFn (fun _ : Fin n => false)) = true := by
    cases hh : cutInput pre inputs (List.ofFn (fun _ : Fin n => false)) <;> simp_all
  have hc := suffix_cutInput_true_of_bottom pre inputs hp hb (fun _ : Fin n => true)
  rw [hc] at hf1
  cases hf1

lemma suffix_short_replace_last {n : ℕ} (pre suffix : List Gate) (inputs : List ℕ)
    (hp : ∀ k ∈ pre, (k.op = GateOp.and ∨ k.op = GateOp.or) ∧ k.inputs.length ≤ 2)
    (hs : ∀ k ∈ suffix, (k.op = GateOp.and ∨ k.op = GateOp.or) ∧ k.inputs.length ≤ 2)
    (hl : suffix.length ≤ 1)
    (hf0 : Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix,
      n + pre.length + suffix.length⟩ (List.ofFn (fun _ : Fin n => false)) = false)
    (hf1 : Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix,
      n + pre.length + suffix.length⟩ (List.ofFn (fun _ : Fin n => true)) = true) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length = (pre ++ ⟨GateOp.not, inputs⟩ :: suffix).length ∧
      ∀ x : Fin n → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) =
        Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix,
          n + pre.length + suffix.length⟩ (List.ofFn x) := by
  cases suffix with
  | nil =>
    exact False.elim (suffix_zero_last_impossible pre inputs (fun g hg => (hp g hg).1)
      (by simpa only [List.length_nil, Nat.add_zero] using hf0)
      (by simpa only [List.length_nil, Nat.add_zero] using hf1))
  | cons g suffix =>
    cases suffix with
    | nil =>
      have hg := hs g List.mem_cons_self
      rcases suffix_one_replace_last pre inputs g (fun k hk => (hp k hk).1) hg.1
        (by simpa only [List.length_cons, List.length_nil] using hf0)
        (by simpa only [List.length_cons, List.length_nil] using hf1) with ht | hf
      · refine ⟨pre ++ ⟨GateOp.and, []⟩ :: [g], n + pre.length + 1,
          cut_replace_mono_basis pre [g] _ hp hs ⟨Or.inl rfl, by simp⟩, by simp, ?_⟩
        simpa only [List.length_cons, List.length_nil] using ht
      · refine ⟨pre ++ ⟨GateOp.or, []⟩ :: [g], n + pre.length + 1,
          cut_replace_mono_basis pre [g] _ hp hs ⟨Or.inr rfl, by simp⟩, by simp, ?_⟩
        simpa only [List.length_cons, List.length_nil] using hf
    | cons k suffix => simp at hl

lemma suffix_cutOutput_old (pre suffix : List Gate) (x : List Bool) (z : Bool)
    (o : ℕ) (ho : o < x.length + pre.length) :
    cutOutput pre suffix o x z = (cutRun pre x).getD o false := by
  unfold cutOutput
  rw [cutRun_input suffix _ o (by simp [suffix_cutRun_length]; omega)]
  rw [List.getD_append _ _ _ _ (by simpa only [suffix_cutRun_length] using ho)]

lemma suffix_cutOutput_slot (pre suffix : List Gate) (x : List Bool) (z : Bool) :
    cutOutput pre suffix (x.length + pre.length) x z = z := by
  unfold cutOutput
  rw [cutRun_input suffix _ _ (by simp [suffix_cutRun_length])]
  rw [← suffix_cutRun_length pre x]
  exact suffix_append_last _ _

lemma suffix_cutOutput_slot_fn {n : ℕ} (pre suffix : List Gate) (x : Fin n → Bool) (z : Bool) :
    cutOutput pre suffix (n + pre.length) (List.ofFn x) z = z := by
  simpa only [List.length_ofFn] using suffix_cutOutput_slot pre suffix (List.ofFn x) z

lemma suffix_cutOutput_past (pre suffix : List Gate) (x : List Bool) (z : Bool)
    (o : ℕ) (ho : x.length + pre.length + 1 + suffix.length ≤ o) :
    cutOutput pre suffix o x z = false := by
  unfold cutOutput
  apply List.getD_eq_default
  simpa only [suffix_cutRun_length, List.length_append, List.length_singleton] using ho

lemma suffix_not_slot_impossible {n : ℕ} (pre suffix : List Gate) (inputs : List ℕ)
    (hp : ∀ k ∈ pre, k.op = GateOp.and ∨ k.op = GateOp.or)
    (hf0 : Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, n + pre.length⟩
      (List.ofFn (fun _ : Fin n => false)) = false)
    (hf1 : Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, n + pre.length⟩
      (List.ofFn (fun _ : Fin n => true)) = true) : False := by
  rw [cut_not_eval, suffix_cutOutput_slot_fn] at hf0 hf1
  have hb : cutInput pre inputs (List.ofFn (fun _ : Fin n => false)) = true := by
    cases hh : cutInput pre inputs (List.ofFn (fun _ : Fin n => false)) <;> simp_all
  have hc := suffix_cutInput_true_of_bottom pre inputs hp hb (fun _ : Fin n => true)
  rw [hc] at hf1
  cases hf1

lemma suffix_short_replace_any_output {n : ℕ} (pre suffix : List Gate) (inputs : List ℕ)
    (o : ℕ)
    (hp : ∀ k ∈ pre, (k.op = GateOp.and ∨ k.op = GateOp.or) ∧ k.inputs.length ≤ 2)
    (hs : ∀ k ∈ suffix, (k.op = GateOp.and ∨ k.op = GateOp.or) ∧ k.inputs.length ≤ 2)
    (hl : suffix.length ≤ 1)
    (hf0 : Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, o⟩
      (List.ofFn (fun _ : Fin n => false)) = false)
    (hf1 : Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, o⟩
      (List.ofFn (fun _ : Fin n => true)) = true) :
    ∃ (gates' : List Gate) (o' : ℕ),
      (∀ g ∈ gates', (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length = (pre ++ ⟨GateOp.not, inputs⟩ :: suffix).length ∧
      ∀ x : Fin n → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) =
        Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, o⟩ (List.ofFn x) := by
  by_cases hbefore : o < n + pre.length
  · refine ⟨pre ++ ⟨GateOp.or, []⟩ :: suffix, o,
      cut_replace_mono_basis pre suffix _ hp hs ⟨Or.inr rfl, by simp⟩, by simp, ?_⟩
    intro x
    rw [cut_false_eval, cut_not_eval]
    rw [suffix_cutOutput_old pre suffix (List.ofFn x) false o (by simpa only [List.length_ofFn] using hbefore),
      suffix_cutOutput_old pre suffix (List.ofFn x) _ o (by simpa only [List.length_ofFn] using hbefore)]
  · by_cases hat : o = n + pre.length
    · subst o
      exact False.elim (suffix_not_slot_impossible pre suffix inputs
        (fun g hg => (hp g hg).1) hf0 hf1)
    · have hbound : o < n + pre.length + 1 + suffix.length := by
        by_contra hb
        have he := suffix_cutOutput_past pre suffix (List.ofFn (fun _ : Fin n => true))
          (!(cutInput pre inputs (List.ofFn (fun _ : Fin n => true)))) o
          (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hb)
        have ht : cutOutput pre suffix o (List.ofFn (fun _ : Fin n => true))
            (!(cutInput pre inputs (List.ofFn (fun _ : Fin n => true)))) = true := by
          simpa only [cut_not_eval] using hf1
        have hbad : false = true := he.symm.trans ht
        cases hbad
      have hlast : o = n + pre.length + suffix.length := by omega
      subst o
      exact suffix_short_replace_last pre suffix inputs hp hs hl hf0 hf1

def sampleCutCover {α : Type*} [Preorder α] (f h : α → Bool) (rows : List α) : Prop :=
  (∀ x, f x = true → ∃ y ∈ rows, y ≤ x ∧ (!h y) ≤ (!h x) ∧ f y = true) ∧
  (∀ x, f x = false → ∃ y ∈ rows, x ≤ y ∧ (!h x) ≤ (!h y) ∧ f y = false)

lemma sample_cut_lift {α : Type*} [Preorder α]
    (f h : α → Bool) (rows : List α) (F : α → Bool → Bool)
    (hFx : ∀ z, Monotone (fun x => F x z))
    (hFz : ∀ x, Monotone (F x))
    (hcover : sampleCutCover f h rows)
    (hrows : ∀ x ∈ rows, F x (!h x) = f x) :
    ∀ x, F x (!h x) = f x := by
  intro x
  cases hx : f x with
  | false =>
    obtain ⟨y, hy, hxy, hn, hf⟩ := hcover.2 x hx
    have hle := le_trans (hFx (!h x) hxy) (hFz y hn)
    exact eq_false_of_le_false (by simpa only [hrows y hy, hf] using hle)
  | true =>
    obtain ⟨y, hy, hyx, hn, hf⟩ := hcover.1 x hx
    have hle := le_trans (hFx (!h y) hyx) (hFz x hn)
    exact eq_true_of_true_le (by simpa only [hrows y hy, hf] using hle)

lemma sample_cut_correct_iff {α : Type*} [Preorder α]
    (f h : α → Bool) (rows : List α) (F : α → Bool → Bool)
    (hFx : ∀ z, Monotone (fun x => F x z))
    (hFz : ∀ x, Monotone (F x))
    (hcover : sampleCutCover f h rows) :
    (∀ x, F x (!h x) = f x) ↔ (∀ x ∈ rows, F x (!h x) = f x) := by
  constructor
  · exact fun hh x _ => hh x
  · exact sample_cut_lift f h rows F hFx hFz hcover

def pairAndInput (p : Fin 7 × Fin 7) (x : Fin 7 → Bool) : Bool :=
  x p.1 && x p.2

def triplePoint (p : Fin 7 × Fin 7) (k : Fin 7) : Fin 7 → Bool :=
  fun i => pairPoint p i || decide (i = k)

def pairAndSamples (p : Fin 7 × Fin 7) : List (Fin 7 → Bool) :=
  ((edgePairs ++ nonedgePairs).map pairPoint) ++
    ((List.finRange 7).filter (fun k => decide (k ≠ p.1 ∧ k ≠ p.2))).map (triplePoint p)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 32000000 in
lemma pairAndSamples_cover : ∀ p ∈ nonedgePairs,
    sampleCutCover edgeFun (pairAndInput p) (pairAndSamples p) := by
  unfold sampleCutCover
  decide

lemma pairAndSamples_length : ∀ p ∈ nonedgePairs, (pairAndSamples p).length = 26 := by
  decide

lemma pairAndSamples_correct_iff (p : Fin 7 × Fin 7) (hp : p ∈ nonedgePairs)
    (F : (Fin 7 → Bool) → Bool → Bool)
    (hFx : ∀ z, Monotone (fun x => F x z))
    (hFz : ∀ x, Monotone (F x)) :
    (∀ x, F x (!(x p.1 && x p.2)) = edgeFun x) ↔
      (∀ x ∈ pairAndSamples p, F x (!(x p.1 && x p.2)) = edgeFun x) :=
  sample_cut_correct_iff edgeFun (pairAndInput p) (pairAndSamples p) F hFx hFz
    (pairAndSamples_cover p hp)

def or14Input (x : Fin 7 → Bool) : Bool := x 1 || x 4

def or14Samples : List (Fin 7 → Bool) :=
  ((edgePairs ++ nonedgePairs).map pairPoint) ++
    [(fun i => decide (i = 6)), triplePoint (0, 1) 2, triplePoint (0, 1) 6,
      triplePoint (1, 2) 6, triplePoint (3, 4) 5, triplePoint (3, 4) 6, triplePoint (4, 5) 6]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
lemma or14Samples_cover : sampleCutCover edgeFun or14Input or14Samples := by
  unfold sampleCutCover
  decide

lemma or14Samples_length : or14Samples.length = 28 := by
  decide

lemma or14Samples_correct_iff (F : (Fin 7 → Bool) → Bool → Bool)
    (hFx : ∀ z, Monotone (fun x => F x z))
    (hFz : ∀ x, Monotone (F x)) :
    (∀ x, F x (!(x 1 || x 4)) = edgeFun x) ↔
      (∀ x ∈ or14Samples, F x (!(x 1 || x 4)) = edgeFun x) :=
  sample_cut_correct_iff edgeFun or14Input or14Samples F hFx hFz or14Samples_cover

lemma cover_pairAnd_nonedge : ∀ p ∈ nonedgePairs, ∀ q ∈ nonedgePairs,
    pairAndInput p (pairPoint q) = true → q = p := by
  decide

lemma cover_bad_nonedge_eq (p : Fin 7 × Fin 7) (hp : p ∈ nonedgePairs)
    (F : (Fin 7 → Bool) → Bool → Bool)
    (hdiag : ∀ x, F x (!(pairAndInput p x)) = edgeFun x)
    (q : Fin 7 × Fin 7) (hq : q ∈ nonedgePairs)
    (hbad : F (pairPoint q) true = true) : q = p := by
  apply cover_pairAnd_nonedge p hp q hq
  have hd := hdiag (pairPoint q)
  rw [nonedgePoint_false q hq] at hd
  cases hh : pairAndInput p (pairPoint q) with
  | false =>
    simp only [hh, Bool.not_false] at hd
    have he : false = true := hd.symm.trans hbad
    cases he
  | true => rfl

lemma cover_true_replacement (p : Fin 7 × Fin 7) (hp : p ∈ nonedgePairs)
    (F : (Fin 7 → Bool) → Bool → Bool)
    (hFx : ∀ z, Monotone (fun x => F x z))
    (hFz : ∀ x, Monotone (F x))
    (hdiag : ∀ x, F x (!(pairAndInput p x)) = edgeFun x)
    (hb : F (pairPoint p) true = false) :
    ∀ x, F x true = edgeFun x := by
  apply monotone_cut_replacement F (pairAndInput p) (fun _ => true) hFx hFz
  · exact fun _ _ _ => le_rfl
  · exact hdiag
  · intro e he hm
    rfl
  · intro q hq hbad
    have heq := cover_bad_nonedge_eq p hp F hdiag q hq hbad
    subst q
    rw [hb] at hbad
    cases hbad

lemma cover_or_mono : ∀ {a b c d : Bool}, a ≤ c → b ≤ d → (a || b) ≤ (c || d) := by
  decide

lemma cover_point_outside (p : Fin 7 × Fin 7) (u : Fin 7)
    (hu1 : u ≠ p.1) (hu2 : u ≠ p.2) : pairPoint p u = false := by
  simp [pairPoint, hu1, hu2]

lemma cover_or_replacement (p : Fin 7 × Fin 7) (hp : p ∈ nonedgePairs)
    (F : (Fin 7 → Bool) → Bool → Bool)
    (hFx : ∀ z, Monotone (fun x => F x z))
    (hFz : ∀ x, Monotone (F x))
    (hdiag : ∀ x, F x (!(pairAndInput p x)) = edgeFun x)
    (u v : Fin 7) (hu1 : u ≠ p.1) (hu2 : u ≠ p.2)
    (hv1 : v ≠ p.1) (hv2 : v ≠ p.2)
    (hcover : ∀ e ∈ edgePairs, F (pairPoint e) false = false →
      (pairPoint e u || pairPoint e v) = true) :
    ∀ x, F x (x u || x v) = edgeFun x := by
  apply monotone_cut_replacement F (pairAndInput p) (fun x => x u || x v) hFx hFz
  · intro x y hxy
    exact cover_or_mono (hxy u) (hxy v)
  · exact hdiag
  · exact hcover
  · intro q hq hbad
    have heq := cover_bad_nonedge_eq p hp F hdiag q hq hbad
    subst q
    rw [cover_point_outside p u hu1 hu2, cover_point_outside p v hv1 hv2]
    rfl

lemma cover_pruning_constraints (p : Fin 7 × Fin 7) (hp : p ∈ nonedgePairs)
    (F : (Fin 7 → Bool) → Bool → Bool)
    (hFx : ∀ z, Monotone (fun x => F x z))
    (hFz : ∀ x, Monotone (F x))
    (hdiag : ∀ x, F x (!(pairAndInput p x)) = edgeFun x)
    (htrue : ¬ ∀ x, F x true = edgeFun x)
    (hor : ∀ u v : Fin 7, u ≠ p.1 → u ≠ p.2 → v ≠ p.1 → v ≠ p.2 →
      ¬ ∀ x, F x (x u || x v) = edgeFun x) :
    F (pairPoint p) true = true ∧
    ∀ u v : Fin 7, u ≠ p.1 → u ≠ p.2 → v ≠ p.1 → v ≠ p.2 →
      ∃ e ∈ edgePairs, F (pairPoint e) false = false ∧
        pairPoint e u = false ∧ pairPoint e v = false := by
  classical
  constructor
  · cases hb : F (pairPoint p) true with
    | false => exact (htrue (cover_true_replacement p hp F hFx hFz hdiag hb)).elim
    | true => rfl
  · intro u v hu1 hu2 hv1 hv2
    by_contra hn
    have hc : ∀ e ∈ edgePairs, F (pairPoint e) false = false →
        (pairPoint e u || pairPoint e v) = true := by
      intro e he hm
      cases hu : pairPoint e u <;> cases hv : pairPoint e v
      · exact (hn ⟨e, he, hm, hu, hv⟩).elim
      all_goals rfl
    exact hor u v hu1 hu2 hv1 hv2 (cover_or_replacement p hp F hFx hFz hdiag
      u v hu1 hu2 hv1 hv2 hc)

lemma cover_getD_ofFn (x : Fin 7 → Bool) (i : Fin 7) :
    (List.ofFn x).getD i.val false = x i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp)]
  simp only [Option.getD_some, List.getElem_ofFn]

lemma cover_circuit_pruning_constraints (pre suffix : List Gate) (inputs : List ℕ) (o : ℕ)
    (p : Fin 7 × Fin 7) (hp : p ∈ nonedgePairs)
    (hpre : ∀ g ∈ pre, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hsuf : ∀ g ∈ suffix, g.op = GateOp.and ∨ g.op = GateOp.or)
    (hc : ∀ x : Fin 7 → Bool, cutInput pre inputs (List.ofFn x) = pairAndInput p x)
    (hf : ∀ x : Fin 7 → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, o⟩ (List.ofFn x) = postedEdgeFun x)
    (hno : ∀ g : Gate, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 →
      ¬ ∀ x : Fin 7 → Bool,
        Circuit.eval ⟨pre ++ g :: suffix, o⟩ (List.ofFn x) = postedEdgeFun x) :
    Circuit.eval ⟨pre ++ ⟨GateOp.and, []⟩ :: suffix, o⟩ (List.ofFn (pairPoint p)) = true ∧
    ∀ u v : Fin 7, u ≠ p.1 → u ≠ p.2 → v ≠ p.1 → v ≠ p.2 →
      ∃ e ∈ edgePairs,
        Circuit.eval ⟨pre ++ ⟨GateOp.or, []⟩ :: suffix, o⟩ (List.ofFn (pairPoint e)) = false ∧
        pairPoint e u = false ∧ pairPoint e v = false := by
  have hdiag : ∀ x : Fin 7 → Bool,
      cutOutput pre suffix o (List.ofFn x) (!(pairAndInput p x)) = edgeFun x := by
    intro x
    simpa only [cut_not_eval, hc x] using (hf x).trans (edgeFun_eq_posted x).symm
  have ht : ¬ ∀ x : Fin 7 → Bool,
      cutOutput pre suffix o (List.ofFn x) true = edgeFun x := by
    intro ht
    apply hno ⟨GateOp.and, []⟩ ⟨Or.inl rfl, by simp⟩
    intro x
    rw [cut_true_eval]
    exact (ht x).trans (edgeFun_eq_posted x)
  have ho : ∀ u v : Fin 7, u ≠ p.1 → u ≠ p.2 → v ≠ p.1 → v ≠ p.2 →
      ¬ ∀ x : Fin 7 → Bool,
        cutOutput pre suffix o (List.ofFn x) (x u || x v) = edgeFun x := by
    intro u v _ _ _ _ hor
    apply hno ⟨GateOp.or, [u.val, v.val]⟩ ⟨Or.inr rfl, by simp⟩
    intro x
    rw [cut_or_inputs_eval pre suffix o (List.ofFn x) u.val v.val (by simp) (by simp),
      cover_getD_ofFn x u, cover_getD_ofFn x v]
    exact (hor x).trans (edgeFun_eq_posted x)
  have hh := cover_pruning_constraints p hp
    (fun x => cutOutput pre suffix o (List.ofFn x))
    (cutOutput_fn_x_mono pre suffix o hpre hsuf)
    (cutOutput_fn_z_mono pre suffix o hsuf) hdiag ht ho
  simpa only [cut_true_eval, cut_false_eval] using hh

lemma cover_pairAnd_point_le (p : Fin 7 × Fin 7) (x : Fin 7 → Bool)
    (hh : pairAndInput p x = true) : pairPoint p ≤ x := by
  have ha := (Bool.and_eq_true_iff.mp hh).1
  have hb := (Bool.and_eq_true_iff.mp hh).2
  intro i
  by_cases hi : i = p.1 ∨ i = p.2
  · rcases hi with rfl | rfl <;> simp [pairPoint, ha, hb]
  · simp [pairPoint, hi]

lemma cover_false_input_eq_pair (p : Fin 7 × Fin 7) (hp : p ∈ nonedgePairs)
    (x : Fin 7 → Bool) (hf : edgeFun x = false) (hh : pairAndInput p x = true) :
    x = pairPoint p := by
  obtain ⟨q, hq, hxq⟩ := (false_iff_below_nonedge x).1 hf
  have hle : pairAndInput p x ≤ pairAndInput p (pairPoint q) :=
    and_mono (hxq p.1) (hxq p.2)
  have hhq : pairAndInput p (pairPoint q) = true :=
    eq_true_of_true_le (by simpa only [hh] using hle)
  have heq := cover_pairAnd_nonedge p hp q hq hhq
  subst q
  exact le_antisymm hxq (cover_pairAnd_point_le p x hh)

lemma cover_true_completion (p : Fin 7 × Fin 7) (hp : p ∈ nonedgePairs)
    (F : (Fin 7 → Bool) → Bool → Bool)
    (hFz : ∀ x, Monotone (F x))
    (hdiag : ∀ x, F x (!(pairAndInput p x)) = edgeFun x) :
    ∀ x, F x true = edgeFun x || (pairAndInput p x && F (pairPoint p) true) := by
  intro x
  cases hf : edgeFun x with
  | true =>
    have hd := hdiag x
    have hle := hFz x (show (!(pairAndInput p x)) ≤ true by simp)
    have hb : F x true = true := eq_true_of_true_le (by simpa only [hd, hf] using hle)
    simp [hb]
  | false =>
    cases hh : pairAndInput p x with
    | false =>
      have hd := hdiag x
      simp only [hh, Bool.not_false, hf] at hd
      simp [hd]
    | true =>
      have heq := cover_false_input_eq_pair p hp x hf hh
      subst x
      simp

lemma cover_true_completion_bad (p : Fin 7 × Fin 7) (hp : p ∈ nonedgePairs)
    (F : (Fin 7 → Bool) → Bool → Bool)
    (hFz : ∀ x, Monotone (F x))
    (hdiag : ∀ x, F x (!(pairAndInput p x)) = edgeFun x)
    (hb : F (pairPoint p) true = true) :
    ∀ x, F x true = edgeFun x || pairAndInput p x := by
  intro x
  simpa only [hb, Bool.and_true] using cover_true_completion p hp F hFz hdiag x

end PEqualNP.Outside.L_meta_10760
