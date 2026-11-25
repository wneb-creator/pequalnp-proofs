import PEqualNP.Defs
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.List.GetD
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
    ∀ x, F x true = (edgeFun x || (pairAndInput p x && F (pairPoint p) true)) := by
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
    ∀ x, F x true = (edgeFun x || pairAndInput p x) := by
  intro x
  simpa only [hb, Bool.and_true] using cover_true_completion p hp F hFz hdiag x

namespace ForceCompiler

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w

def Ok (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

lemma getD_snoc_eq {α : Type} (L : List α) (a d : α) :
    (L ++ [a]).getD L.length d = a := by
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

lemma getD_snoc_ne {α : Type} (L : List α) (a d : α) (i : ℕ) (hi : i ≠ L.length) :
    (L ++ [a]).getD i d = L.getD i d := by
  by_cases hlt : i < L.length
  · exact List.getD_append _ _ _ _ hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [wiresFrom]
  | cons g gs ih =>
    change (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma wiresFrom_append (gs hs : List Gate) (w : List Bool) :
    wiresFrom (gs ++ hs) w = wiresFrom hs (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) (w : List Bool) :
    ∃ t, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht, List.append_assoc]
    rfl

abbrev Stat := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)


def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

lemma simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

lemma simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]


def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

lemma elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

lemma toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

lemma elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega


lemma elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

lemma Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

lemma Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj


def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

lemma inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2


def MonoGate (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma monoGate_ok (g : Gate) (hg : MonoGate g) : Ok g :=
  ⟨hg.1.elim Or.inl (fun h => Or.inr (Or.inl h)), hg.2⟩

lemma monoGate_nok (g : Gate) (hg : MonoGate g) : NOk g := by
  refine ⟨monoGate_ok g hg, ?_⟩
  intro hn
  rcases hg.1 with ha | ho <;> rw [hn] at * <;> contradiction

lemma simplify_mono (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or) :
    ∀ g ∈ (simplify op m ins).1, MonoGate g := by
  intro g hg
  rcases hop with rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplify, simpAnd] at hg <;> (subst hg; simp [MonoGate])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simplify, simpOr] at hg <;> (subst hg; simp [MonoGate])

lemma elim_mono (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (hgs : ∀ g ∈ gs, MonoGate g) (hacc : ∀ g ∈ acc.2, MonoGate g) :
    ∀ g ∈ (elim n gs acc).2, MonoGate g := by
  induction gs generalizing acc with
  | nil => exact hacc
  | cons g gs ih =>
    apply ih (elimStep n acc g) (fun k hk => hgs k (List.mem_cons_of_mem _ hk))
    intro k hk
    rcases List.mem_append.mp hk with hk | hk
    · exact hacc k hk
    · exact simplify_mono _ _ _ (hgs g List.mem_cons_self).1 k (by simpa using hk)

lemma elim_append (n : ℕ) (pre suffix : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ suffix) acc = elim n suffix (elim n pre acc) := by
  simp [elim, List.foldl_append]

lemma elim_fst_length (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    change (elim n gs (elimStep n acc g)).1.length = _
    rw [ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Sum.inr i.val)

lemma inv_id (n : ℕ) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (List.ofFn x) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩

lemma elim_true_step (n : ℕ) (acc : List Stat × List Gate) :
    elimStep n acc ⟨GateOp.and, []⟩ = (acc.1 ++ [Sum.inl true], acc.2) := by
  simp [elimStep, simplify, simpAnd]

lemma force_used_constant_saves_two {n : ℕ} (pre suffix : List Gate) (o : ℕ)
    (hp : ∀ g ∈ pre, MonoGate g) (hs : ∀ g ∈ suffix, MonoGate g)
    (hreader : ∃ g ∈ suffix, n + pre.length ∈ g.inputs)
    (x0 : Fin n → Bool)
    (hfalse : Circuit.eval ⟨pre ++ ⟨GateOp.and, []⟩ :: suffix, o⟩ (List.ofFn x0) = false) :
    ∃ (gs : List Gate) (out : ℕ),
      (∀ g ∈ gs, MonoGate g) ∧
      gs.length + 2 ≤ (pre ++ ⟨GateOp.and, []⟩ :: suffix).length ∧
      ∀ x : Fin n → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) =
        Circuit.eval ⟨pre ++ ⟨GateOp.and, []⟩ :: suffix, o⟩ (List.ofFn x) := by
  let init : List Stat × List Gate := (idStats n, [])
  let acc := elim n pre init
  let final := elim n (pre ++ ⟨GateOp.and, []⟩ :: suffix) init
  have hmono : ∀ g ∈ pre ++ ⟨GateOp.and, []⟩ :: suffix, MonoGate g := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hp g hg
    · rcases List.mem_cons.mp hg with rfl | hg
      · simp [MonoGate]
      · exact hs g hg
  have hfinal : final = elim n suffix (acc.1 ++ [Sum.inl true], acc.2) := by
    dsimp [final, acc]
    rw [elim_append]
    change elim n suffix (elimStep n (elim n pre init) ⟨GateOp.and, []⟩) = _
    rw [elim_true_step]
  have hacc1 : acc.1.length = n + pre.length := by
    simp [acc, init, elim_fst_length, idStats]
  have hacc2 : acc.2.length ≤ pre.length := by
    simpa only [init, List.length_nil, Nat.zero_add] using elim_len n pre init
  have hsave : final.2.length + 2 ≤ (pre ++ ⟨GateOp.and, []⟩ :: suffix).length := by
    have hh := elim_len_lt n (n + pre.length) suffix
      (acc.1 ++ [Sum.inl true], acc.2) (fun g hg => monoGate_nok g (hs g hg))
      (by simp [hacc1]) ⟨true, getD_snoc_len _ _ _ _ hacc1⟩ hreader
    rw [hfinal]
    simp only [List.length_append, List.length_cons] at *
    omega
  have hok : ∀ g ∈ final.2, MonoGate g :=
    elim_mono n _ init hmono (by simp [init])
  have hval (x : Fin n → Bool) :
      (final.1.getD o (Sum.inl false)).val (wiresFrom final.2 (List.ofFn x)) =
        Circuit.eval ⟨pre ++ ⟨GateOp.and, []⟩ :: suffix, o⟩ (List.ofFn x) := by
    exact (inv_elim n (List.ofFn x) (by simp) _ _ init
      (fun g hg => monoGate_ok g (hmono g hg)) (inv_id n x)).2 o |>.2
  cases hst : final.1.getD o (Sum.inl false) with
  | inl b =>
    cases b with
    | false =>
      refine ⟨final.2, n + final.2.length, hok, hsave, ?_⟩
      intro x
      have hv := hval x
      rw [hst] at hv
      change false = _ at hv
      change (wiresFrom final.2 (List.ofFn x)).getD (n + final.2.length) false = _
      rw [List.getD_eq_default _ _ (by simp [length_wiresFrom])]
      exact hv
    | true =>
      have hv := hval x0
      rw [hst] at hv
      change true = _ at hv
      rw [hfalse] at hv
      cases hv
  | inr j =>
    refine ⟨final.2, j, hok, hsave, ?_⟩
    intro x
    have hv := hval x
    rw [hst] at hv
    exact hv

end ForceCompiler

lemma fixedAnd_true_completion_saves_two
    (pre suffix : List Gate) (inputs : List ℕ) (o : ℕ)
    (p : Fin 7 × Fin 7) (hp : p ∈ nonedgePairs)
    (hpre : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsuf : ∀ g ∈ suffix, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hc : ∀ x : Fin 7 → Bool, cutInput pre inputs (List.ofFn x) = pairAndInput p x)
    (hf : ∀ x : Fin 7 → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, o⟩ (List.ofFn x) = postedEdgeFun x)
    (hBbad : Circuit.eval ⟨pre ++ ⟨GateOp.and, []⟩ :: suffix, o⟩
      (List.ofFn (pairPoint p)) = true)
    (hreader : ∃ g ∈ suffix, 7 + pre.length ∈ g.inputs) :
    ∃ (gs : List Gate) (out : ℕ),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs.length + 2 ≤ (pre ++ ⟨GateOp.not, inputs⟩ :: suffix).length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) =
        (postedEdgeFun x || pairAndInput p x) := by
  have hdiag : ∀ x : Fin 7 → Bool,
      cutOutput pre suffix o (List.ofFn x) (!(pairAndInput p x)) = edgeFun x := by
    intro x
    simpa only [cut_not_eval, hc x] using (hf x).trans (edgeFun_eq_posted x).symm
  have hcompletion := cover_true_completion_bad p hp
    (fun x => cutOutput pre suffix o (List.ofFn x))
    (cutOutput_fn_z_mono pre suffix o (fun g hg => (hsuf g hg).1)) hdiag
    (by simpa only [cut_true_eval] using hBbad)
  have hfalse : Circuit.eval ⟨pre ++ ⟨GateOp.and, []⟩ :: suffix, o⟩
      (List.ofFn (fun _ : Fin 7 => false)) = false := by
    rw [cut_true_eval, hcompletion]
    rfl
  obtain ⟨gs, out, hgs, hlen, heval⟩ := ForceCompiler.force_used_constant_saves_two
    pre suffix o hpre hsuf hreader (fun _ : Fin 7 => false) hfalse
  refine ⟨gs, out, hgs, ?_, ?_⟩
  · simpa only [List.length_append, List.length_cons] using hlen
  · intro x
    rw [heval x, cut_true_eval, hcompletion, edgeFun_eq_posted]

lemma cut_reduce_input {α : Type*} (f h h0 : α → Bool)
    (F : α → Bool → Bool) (hFz : ∀ x, Monotone (F x))
    (hdiag : ∀ x, F x (!h x) = f x)
    (hle : ∀ x, h0 x ≤ h x)
    (hzero : ∀ x, f x = false → h0 x = h x) :
    ∀ x, F x (!h0 x) = f x := by
  intro x
  cases hf : f x with
  | false => simpa only [hzero x hf, hf] using hdiag x
  | true =>
    have hnot : ∀ a b : Bool, a ≤ b → (!b) ≤ (!a) := by decide
    have hn : (!h x) ≤ (!h0 x) := hnot _ _ (hle x)
    have hz := hFz x hn
    exact eq_true_of_true_le (by simpa only [hdiag x, hf] using hz)

lemma cut_reduce_pair_input (p : Fin 7 × Fin 7) (hp : p ∈ nonedgePairs)
    (h : (Fin 7 → Bool) → Bool) (hh : Monotone h)
    (F : (Fin 7 → Bool) → Bool → Bool) (hFz : ∀ x, Monotone (F x))
    (hdiag : ∀ x, F x (!h x) = edgeFun x)
    (hzero : ∀ x, edgeFun x = false → h x = pairAndInput p x) :
    ∀ x, F x (!(pairAndInput p x)) = edgeFun x := by
  apply cut_reduce_input edgeFun h (pairAndInput p) F hFz hdiag
  · intro x
    cases hx : pairAndInput p x with
    | false => simp
    | true =>
      have hptrue : pairAndInput p (pairPoint p) = true := by
        simp [pairAndInput, pairPoint]
      have hbase : h (pairPoint p) = true :=
        (hzero (pairPoint p) (nonedgePoint_false p hp)).trans hptrue
      have hmono := hh (cover_pairAnd_point_le p x hx)
      simpa only [hbase] using hmono
  · intro x hx
    exact (hzero x hx).symm

lemma fixedAnd_zero_agreement_completion_saves_two
    (pre suffix : List Gate) (inputs : List ℕ) (o : ℕ)
    (p : Fin 7 × Fin 7) (hp : p ∈ nonedgePairs)
    (hpre : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsuf : ∀ g ∈ suffix, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hzero : ∀ x : Fin 7 → Bool, edgeFun x = false →
      cutInput pre inputs (List.ofFn x) = pairAndInput p x)
    (hf : ∀ x : Fin 7 → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, o⟩ (List.ofFn x) = postedEdgeFun x)
    (hBbad : Circuit.eval ⟨pre ++ ⟨GateOp.and, []⟩ :: suffix, o⟩
      (List.ofFn (pairPoint p)) = true)
    (hreader : ∃ g ∈ suffix, 7 + pre.length ∈ g.inputs) :
    ∃ (gs : List Gate) (out : ℕ),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs.length + 2 ≤ (pre ++ ⟨GateOp.not, inputs⟩ :: suffix).length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) =
        (postedEdgeFun x || pairAndInput p x) := by
  have hold : ∀ x : Fin 7 → Bool,
      cutOutput pre suffix o (List.ofFn x) (!(cutInput pre inputs (List.ofFn x))) = edgeFun x := by
    intro x
    simpa only [cut_not_eval] using (hf x).trans (edgeFun_eq_posted x).symm
  have hdiag := cut_reduce_pair_input p hp
    (fun x => cutInput pre inputs (List.ofFn x))
    (cutInput_fn_mono pre inputs (fun g hg => (hpre g hg).1))
    (fun x => cutOutput pre suffix o (List.ofFn x))
    (cutOutput_fn_z_mono pre suffix o (fun g hg => (hsuf g hg).1)) hold hzero
  have hcompletion := cover_true_completion_bad p hp
    (fun x => cutOutput pre suffix o (List.ofFn x))
    (cutOutput_fn_z_mono pre suffix o (fun g hg => (hsuf g hg).1)) hdiag
    (by simpa only [cut_true_eval] using hBbad)
  have hfalse : Circuit.eval ⟨pre ++ ⟨GateOp.and, []⟩ :: suffix, o⟩
      (List.ofFn (fun _ : Fin 7 => false)) = false := by
    rw [cut_true_eval, hcompletion]
    rfl
  obtain ⟨gs, out, hgs, hlen, heval⟩ := ForceCompiler.force_used_constant_saves_two
    pre suffix o hpre hsuf hreader (fun _ : Fin 7 => false) hfalse
  refine ⟨gs, out, hgs, ?_, ?_⟩
  · simpa only [List.length_append, List.length_cons] using hlen
  · intro x
    rw [heval x, cut_true_eval, hcompletion, edgeFun_eq_posted]

def completedEdgeFun (p : Fin 7 × Fin 7) (x : Fin 7 → Bool) : Bool :=
  edgeFun x || pairAndInput p x

def completedEdgeSamples : List (Fin 7 → Bool) :=
  (edgePairs ++ nonedgePairs).map pairPoint

set_option maxRecDepth 10000 in
set_option maxHeartbeats 32000000 in
lemma completedEdgeSamples_cover : ∀ p ∈ nonedgePairs,
    sampleCutCover (completedEdgeFun p) (fun _ => false) completedEdgeSamples := by
  unfold sampleCutCover
  decide

lemma completedEdgeSamples_length : completedEdgeSamples.length = 21 := by
  decide

lemma completedEdgeSamples_correct_iff (p : Fin 7 × Fin 7) (hp : p ∈ nonedgePairs)
    (g : (Fin 7 → Bool) → Bool) (hg : Monotone g) :
    (∀ x, g x = completedEdgeFun p x) ↔
      (∀ x ∈ completedEdgeSamples, g x = completedEdgeFun p x) := by
  exact sample_cut_correct_iff (completedEdgeFun p) (fun _ => false)
    completedEdgeSamples (fun x _ => g x) (fun _ => hg)
    (fun _ _ _ _ => le_rfl) (completedEdgeSamples_cover p hp)

lemma reader_append_agrees (u v : List Bool) (a b : Bool) (k : ℕ)
    (hlen : u.length = v.length) (hab : a = b)
    (heq : ∀ i, i ≠ k → u.getD i false = v.getD i false) :
    ∀ i, i ≠ k → (u ++ [a]).getD i false = (v ++ [b]).getD i false := by
  intro i hik
  by_cases hi : i < u.length
  · rw [List.getD_append _ _ _ _ hi,
      List.getD_append _ _ _ _ (by omega)]
    exact heq i hik
  · by_cases hil : i = u.length
    · subst i
      rw [suffix_append_last, hlen, suffix_append_last, hab]
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]

lemma reader_cutRun_agrees (gs : List Gate) (k : ℕ)
    (hunread : ∀ g ∈ gs, k ∉ g.inputs)
    (u v : List Bool) (hlen : u.length = v.length)
    (heq : ∀ i, i ≠ k → u.getD i false = v.getD i false) :
    ∀ i, i ≠ k → (cutRun gs u).getD i false = (cutRun gs v).getD i false := by
  induction gs generalizing u v with
  | nil => exact heq
  | cons g gs ih =>
    have hg : k ∉ g.inputs := hunread g List.mem_cons_self
    have hgates : ∀ g' ∈ gs, k ∉ g'.inputs :=
      fun g' hg' => hunread g' (List.mem_cons_of_mem g hg')
    have hv : g.op.eval (g.inputs.map fun i => u.getD i false) =
        g.op.eval (g.inputs.map fun i => v.getD i false) := by
      apply congrArg g.op.eval
      apply List.map_congr_left
      intro i hi
      apply heq i
      intro hik
      exact hg (hik ▸ hi)
    exact ih hgates _ _ (by simpa using hlen)
      (reader_append_agrees u v _ _ k hlen hv heq)

lemma reader_cutOutput_unread (pre suffix : List Gate) (x : List Bool) (o : ℕ)
    (a b : Bool) (hunread : ∀ g ∈ suffix, x.length + pre.length ∉ g.inputs)
    (ho : o ≠ x.length + pre.length) :
    cutOutput pre suffix o x a = cutOutput pre suffix o x b := by
  apply reader_cutRun_agrees suffix (x.length + pre.length) hunread
    (cutRun pre x ++ [a]) (cutRun pre x ++ [b]) (by simp)
  · intro i hi
    exact suffix_append_irrel _ _ _ i (by simpa only [suffix_cutRun_length] using hi)
  · exact ho

lemma reader_exists_of_cut_difference {n : ℕ} (pre suffix : List Gate) (o : ℕ)
    (x : Fin n → Bool) (a b : Bool)
    (ho : o ≠ n + pre.length)
    (hdiff : cutOutput pre suffix o (List.ofFn x) a ≠
      cutOutput pre suffix o (List.ofFn x) b) :
    ∃ g ∈ suffix, n + pre.length ∈ g.inputs := by
  by_contra hnone
  have hunread : ∀ g ∈ suffix, n + pre.length ∉ g.inputs := by
    simpa only [not_exists, not_and] using hnone
  apply hdiff
  exact reader_cutOutput_unread pre suffix (List.ofFn x) o a b
    (by simpa only [List.length_ofFn] using hunread)
    (by simpa only [List.length_ofFn] using ho)

lemma reader_exists_of_cut_values {n : ℕ} (pre suffix : List Gate) (o : ℕ)
    (x0 x : Fin n → Bool)
    (hzero : cutOutput pre suffix o (List.ofFn x0) true = false)
    (hfalse : cutOutput pre suffix o (List.ofFn x) false = false)
    (htrue : cutOutput pre suffix o (List.ofFn x) true = true) :
    ∃ g ∈ suffix, n + pre.length ∈ g.inputs := by
  apply reader_exists_of_cut_difference pre suffix o x false true
  · intro ho
    subst o
    rw [suffix_cutOutput_slot_fn] at hzero
    cases hzero
  · rw [hfalse, htrue]
    decide

lemma reader_fixedAnd_zero_agreement (pre suffix : List Gate) (inputs : List ℕ) (o : ℕ)
    (p : Fin 7 × Fin 7) (hp : p ∈ nonedgePairs)
    (hzero : ∀ x : Fin 7 → Bool, edgeFun x = false →
      cutInput pre inputs (List.ofFn x) = pairAndInput p x)
    (hf : ∀ x : Fin 7 → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, o⟩ (List.ofFn x) = postedEdgeFun x)
    (hBbad : Circuit.eval ⟨pre ++ ⟨GateOp.and, []⟩ :: suffix, o⟩
      (List.ofFn (pairPoint p)) = true) :
    ∃ g ∈ suffix, 7 + pre.length ∈ g.inputs := by
  have hdiag : ∀ x : Fin 7 → Bool,
      cutOutput pre suffix o (List.ofFn x) (!(cutInput pre inputs (List.ofFn x))) = edgeFun x := by
    intro x
    simpa only [cut_not_eval] using (hf x).trans (edgeFun_eq_posted x).symm
  apply reader_exists_of_cut_values pre suffix o (fun _ : Fin 7 => false) (pairPoint p)
  · have hd := hdiag (fun _ : Fin 7 => false)
    have hb : edgeFun (fun _ : Fin 7 => false) = false := rfl
    rw [hzero _ hb, hb] at hd
    simpa only [pairAndInput, Bool.false_and, Bool.not_false] using hd
  · have hpfalse := nonedgePoint_false p hp
    have hpinput : pairAndInput p (pairPoint p) = true := by
      simp [pairAndInput, pairPoint]
    have hd := hdiag (pairPoint p)
    rw [hzero _ hpfalse, hpinput, Bool.not_true] at hd
    exact hd.trans hpfalse
  · simpa only [cut_true_eval] using hBbad

lemma fixedAnd_zero_agreement_eliminate_not
    (pre suffix : List Gate) (inputs : List ℕ) (o : ℕ)
    (p : Fin 7 × Fin 7) (hp : p ∈ nonedgePairs)
    (hpre : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsuf : ∀ g ∈ suffix, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hzero : ∀ x : Fin 7 → Bool, edgeFun x = false →
      cutInput pre inputs (List.ofFn x) = pairAndInput p x)
    (hf : ∀ x : Fin 7 → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, o⟩ (List.ofFn x) = postedEdgeFun x)
    (hBbad : Circuit.eval ⟨pre ++ ⟨GateOp.and, []⟩ :: suffix, o⟩
      (List.ofFn (pairPoint p)) = true) :
    ∃ (gs : List Gate) (out : ℕ),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs.length + 2 ≤ (pre ++ ⟨GateOp.not, inputs⟩ :: suffix).length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) =
        (postedEdgeFun x || pairAndInput p x) :=
  fixedAnd_zero_agreement_completion_saves_two pre suffix inputs o p hp hpre hsuf
    hzero hf hBbad (reader_fixedAnd_zero_agreement pre suffix inputs o p hp hzero hf hBbad)

lemma fixedAnd_zero_agreement_dichotomy
    (pre suffix : List Gate) (inputs : List ℕ) (o : ℕ)
    (p : Fin 7 × Fin 7) (hp : p ∈ nonedgePairs)
    (hpre : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsuf : ∀ g ∈ suffix, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hzero : ∀ x : Fin 7 → Bool, edgeFun x = false →
      cutInput pre inputs (List.ofFn x) = pairAndInput p x)
    (hf : ∀ x : Fin 7 → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, o⟩ (List.ofFn x) = postedEdgeFun x) :
    (∃ (gs : List Gate) (out : ℕ),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs.length ≤ (pre ++ ⟨GateOp.not, inputs⟩ :: suffix).length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) = postedEdgeFun x) ∨
    (∃ (gs : List Gate) (out : ℕ),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs.length + 2 ≤ (pre ++ ⟨GateOp.not, inputs⟩ :: suffix).length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) =
        (postedEdgeFun x || pairAndInput p x)) := by
  cases hb : Circuit.eval ⟨pre ++ ⟨GateOp.and, []⟩ :: suffix, o⟩
      (List.ofFn (pairPoint p)) with
  | false =>
    have hold : ∀ x : Fin 7 → Bool,
        cutOutput pre suffix o (List.ofFn x) (!(cutInput pre inputs (List.ofFn x))) = edgeFun x := by
      intro x
      simpa only [cut_not_eval] using (hf x).trans (edgeFun_eq_posted x).symm
    have hdiag := cut_reduce_pair_input p hp
      (fun x => cutInput pre inputs (List.ofFn x))
      (cutInput_fn_mono pre inputs (fun g hg => (hpre g hg).1))
      (fun x => cutOutput pre suffix o (List.ofFn x))
      (cutOutput_fn_z_mono pre suffix o (fun g hg => (hsuf g hg).1)) hold hzero
    have hcompletion := cover_true_completion p hp
      (fun x => cutOutput pre suffix o (List.ofFn x))
      (cutOutput_fn_z_mono pre suffix o (fun g hg => (hsuf g hg).1)) hdiag
    have hBfalse : cutOutput pre suffix o (List.ofFn (pairPoint p)) true = false := by
      simpa only [cut_true_eval] using hb
    refine Or.inl ⟨pre ++ ⟨GateOp.and, []⟩ :: suffix, o,
      cut_replace_mono_basis pre suffix _ hpre hsuf ⟨Or.inl rfl, by simp⟩,
      by simp, ?_⟩
    intro x
    rw [cut_true_eval, hcompletion, hBfalse, Bool.and_false, Bool.or_false, edgeFun_eq_posted]
  | true =>
    exact Or.inr (fixedAnd_zero_agreement_eliminate_not pre suffix inputs o p hp
      hpre hsuf hzero hf hb)

lemma fixedAnd_reduce_to_positive_bound
    (pre suffix : List Gate) (inputs : List ℕ) (o : ℕ)
    (p : Fin 7 × Fin 7) (hp : p ∈ nonedgePairs)
    (hpre : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsuf : ∀ g ∈ suffix, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hzero : ∀ x : Fin 7 → Bool, edgeFun x = false →
      cutInput pre inputs (List.ofFn x) = pairAndInput p x)
    (hf : ∀ x : Fin 7 → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, o⟩ (List.ofFn x) = postedEdgeFun x)
    (hsmall : (pre ++ ⟨GateOp.not, inputs⟩ :: suffix).length ≤ 13)
    (hbound : ∀ (gs : List Gate) (out : ℕ),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      (∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) =
        (postedEdgeFun x || pairAndInput p x)) → 12 ≤ gs.length) :
    ∃ (gs : List Gate) (out : ℕ),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs.length ≤ (pre ++ ⟨GateOp.not, inputs⟩ :: suffix).length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) = postedEdgeFun x := by
  rcases fixedAnd_zero_agreement_dichotomy pre suffix inputs o p hp hpre hsuf hzero hf with
    hmono | ⟨gs, out, hgs, hlen, heval⟩
  · exact hmono
  · have hlower := hbound gs out hgs heval
    omega

lemma cover_pair_agreement_zero (p : Fin 7 × Fin 7) (hp : p ∈ nonedgePairs)
    (h : (Fin 7 → Bool) → Bool) (hh : Monotone h)
    (hpair : ∀ q ∈ nonedgePairs, h (pairPoint q) = pairAndInput p (pairPoint q)) :
    ∀ x, edgeFun x = false → h x = pairAndInput p x := by
  intro x hx
  cases ha : pairAndInput p x with
  | true =>
    have heq := cover_false_input_eq_pair p hp x hx ha
    subst x
    exact (hpair p hp).trans ha
  | false =>
    have hcompleted : completedEdgeFun p x = false := by
      simp only [completedEdgeFun, hx, ha, Bool.or_false]
    obtain ⟨y, hy, hxy, _, hcy⟩ := (completedEdgeSamples_cover p hp).2 x hcompleted
    change y ∈ (edgePairs ++ nonedgePairs).map pairPoint at hy
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hy
    change (edgeFun (pairPoint q) || pairAndInput p (pairPoint q)) = false at hcy
    have hparts := Bool.or_eq_false_iff.mp hcy
    have hqn : q ∈ nonedgePairs := by
      rcases List.mem_append.mp hq with hqe | hqn
      · have he := edgePoint_true q hqe
        exact False.elim (Bool.false_ne_true (hparts.1.symm.trans he))
      · exact hqn
    apply eq_false_of_le_false
    simpa only [hpair q hqn, hparts.2] using hh hxy

lemma fixedAnd_pair_agreement_dichotomy
    (pre suffix : List Gate) (inputs : List ℕ) (o : ℕ)
    (p : Fin 7 × Fin 7) (hp : p ∈ nonedgePairs)
    (hpre : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsuf : ∀ g ∈ suffix, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hpair : ∀ q ∈ nonedgePairs,
      cutInput pre inputs (List.ofFn (pairPoint q)) = pairAndInput p (pairPoint q))
    (hf : ∀ x : Fin 7 → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, o⟩ (List.ofFn x) = postedEdgeFun x) :
    (∃ (gs : List Gate) (out : ℕ),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs.length ≤ (pre ++ ⟨GateOp.not, inputs⟩ :: suffix).length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) = postedEdgeFun x) ∨
    (∃ (gs : List Gate) (out : ℕ),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs.length + 2 ≤ (pre ++ ⟨GateOp.not, inputs⟩ :: suffix).length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) =
        (postedEdgeFun x || pairAndInput p x)) :=
  fixedAnd_zero_agreement_dichotomy pre suffix inputs o p hp hpre hsuf
    (cover_pair_agreement_zero p hp (fun x => cutInput pre inputs (List.ofFn x))
      (cutInput_fn_mono pre inputs (fun g hg => (hpre g hg).1)) hpair) hf

lemma fixedAnd_pair_reduce_to_positive_bound
    (pre suffix : List Gate) (inputs : List ℕ) (o : ℕ)
    (p : Fin 7 × Fin 7) (hp : p ∈ nonedgePairs)
    (hpre : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsuf : ∀ g ∈ suffix, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hpair : ∀ q ∈ nonedgePairs,
      cutInput pre inputs (List.ofFn (pairPoint q)) = pairAndInput p (pairPoint q))
    (hf : ∀ x : Fin 7 → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, o⟩ (List.ofFn x) = postedEdgeFun x)
    (hsmall : (pre ++ ⟨GateOp.not, inputs⟩ :: suffix).length ≤ 13)
    (hbound : ∀ (gs : List Gate) (out : ℕ),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      (∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) =
        (postedEdgeFun x || pairAndInput p x)) → 12 ≤ gs.length) :
    ∃ (gs : List Gate) (out : ℕ),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs.length ≤ (pre ++ ⟨GateOp.not, inputs⟩ :: suffix).length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) = postedEdgeFun x :=
  fixedAnd_reduce_to_positive_bound pre suffix inputs o p hp hpre hsuf
    (cover_pair_agreement_zero p hp (fun x => cutInput pre inputs (List.ofFn x))
      (cutInput_fn_mono pre inputs (fun g hg => (hpre g hg).1)) hpair) hf hsmall hbound

lemma cover_mono_pair_completion (p : Fin 7 × Fin 7) (hp : p ∈ nonedgePairs)
    (B : (Fin 7 → Bool) → Bool) (hB : Monotone B)
    (hdom : ∀ x, edgeFun x ≤ B x)
    (hpair : ∀ q ∈ nonedgePairs, B (pairPoint q) = pairAndInput p (pairPoint q)) :
    ∀ x, B x = completedEdgeFun p x := by
  apply (completedEdgeSamples_correct_iff p hp B hB).2
  intro x hx
  change x ∈ (edgePairs ++ nonedgePairs).map pairPoint at hx
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hx
  rcases List.mem_append.mp hq with hqe | hqn
  · have he := edgePoint_true q hqe
    have hb : B (pairPoint q) = true :=
      eq_true_of_true_le (by simpa only [he] using hdom (pairPoint q))
    simp only [completedEdgeFun, he, Bool.true_or, hb]
  · simp only [completedEdgeFun, nonedgePoint_false q hqn, Bool.false_or, hpair q hqn]

lemma forced_pair_completion_saves_two
    (pre suffix : List Gate) (inputs : List ℕ) (o : ℕ)
    (p : Fin 7 × Fin 7) (hp : p ∈ nonedgePairs)
    (hpre : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsuf : ∀ g ∈ suffix, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hf : ∀ x : Fin 7 → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, o⟩ (List.ofFn x) = postedEdgeFun x)
    (hpair : ∀ q ∈ nonedgePairs,
      Circuit.eval ⟨pre ++ ⟨GateOp.and, []⟩ :: suffix, o⟩ (List.ofFn (pairPoint q)) =
        pairAndInput p (pairPoint q)) :
    ∃ (gs : List Gate) (out : ℕ),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs.length + 2 ≤ (pre ++ ⟨GateOp.not, inputs⟩ :: suffix).length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) =
        (postedEdgeFun x || pairAndInput p x) := by
  have hdiag : ∀ x : Fin 7 → Bool,
      cutOutput pre suffix o (List.ofFn x) (!(cutInput pre inputs (List.ofFn x))) = edgeFun x := by
    intro x
    simpa only [cut_not_eval] using (hf x).trans (edgeFun_eq_posted x).symm
  have hz := cutOutput_fn_z_mono pre suffix o (fun g hg => (hsuf g hg).1)
  have hdom : ∀ x : Fin 7 → Bool, edgeFun x ≤ cutOutput pre suffix o (List.ofFn x) true := by
    intro x
    have ht : (!(cutInput pre inputs (List.ofFn x))) ≤ true := by simp
    simpa only [hdiag x] using hz x ht
  have hcompletion := cover_mono_pair_completion p hp
    (fun x => cutOutput pre suffix o (List.ofFn x) true)
    (cutOutput_fn_x_mono pre suffix o (fun g hg => (hpre g hg).1)
      (fun g hg => (hsuf g hg).1) true) hdom
    (fun q hq => by simpa only [cut_true_eval] using hpair q hq)
  have hzero : cutOutput pre suffix o (List.ofFn (fun _ : Fin 7 => false)) true = false := by
    rw [hcompletion]
    rfl
  have hfalse : cutOutput pre suffix o (List.ofFn (pairPoint p)) false = false := by
    have ht : false ≤ (!(cutInput pre inputs (List.ofFn (pairPoint p)))) := by simp
    apply eq_false_of_le_false
    simpa only [hdiag (pairPoint p), nonedgePoint_false p hp] using hz (pairPoint p) ht
  have htrue : cutOutput pre suffix o (List.ofFn (pairPoint p)) true = true := by
    rw [hcompletion]
    simp [completedEdgeFun, pairAndInput, pairPoint]
  have hreader := reader_exists_of_cut_values pre suffix o
    (fun _ : Fin 7 => false) (pairPoint p) hzero hfalse htrue
  obtain ⟨gs, out, hgs, hlen, heval⟩ := ForceCompiler.force_used_constant_saves_two
    pre suffix o hpre hsuf hreader (fun _ : Fin 7 => false)
    (by simpa only [cut_true_eval] using hzero)
  refine ⟨gs, out, hgs, ?_, ?_⟩
  · simpa only [List.length_append, List.length_cons] using hlen
  · intro x
    rw [heval x, cut_true_eval, hcompletion, completedEdgeFun, edgeFun_eq_posted]

lemma forced_pair_completion_size_lower_bound
    (pre suffix : List Gate) (inputs : List ℕ) (o : ℕ)
    (p : Fin 7 × Fin 7) (hp : p ∈ nonedgePairs)
    (hpre : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsuf : ∀ g ∈ suffix, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hf : ∀ x : Fin 7 → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, o⟩ (List.ofFn x) = postedEdgeFun x)
    (hpair : ∀ q ∈ nonedgePairs,
      Circuit.eval ⟨pre ++ ⟨GateOp.and, []⟩ :: suffix, o⟩ (List.ofFn (pairPoint q)) =
        pairAndInput p (pairPoint q))
    (hbound : ∀ (gs : List Gate) (out : ℕ),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      (∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) =
        (postedEdgeFun x || pairAndInput p x)) → 12 ≤ gs.length) :
    14 ≤ (pre ++ ⟨GateOp.not, inputs⟩ :: suffix).length := by
  obtain ⟨gs, out, hgs, hlen, heval⟩ := forced_pair_completion_saves_two
    pre suffix inputs o p hp hpre hsuf hf hpair
  have hlower := hbound gs out hgs heval
  omega

open PEqualNP.CircuitLowerBounds

def primaryRenameIndex {n : ℕ} (ρ : Fin n → Fin n) (i : ℕ) : ℕ :=
  if hi : i < n then (ρ ⟨i, hi⟩).val else i

def primaryRenameGate {n : ℕ} (ρ : Fin n → Fin n) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (primaryRenameIndex ρ)⟩

def primaryRename {n : ℕ} (ρ : Fin n → Fin n) (C : Circuit) : Circuit :=
  ⟨C.gates.map (primaryRenameGate ρ), primaryRenameIndex ρ C.output⟩

def primaryRenameStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def primaryRenameRel {n : ℕ} (ρ : Fin n → Fin n) (w w' : List Bool) : Prop :=
  n ≤ w.length ∧ w'.length = w.length ∧
    ∀ i : ℕ, w'.getD (primaryRenameIndex ρ i) false = w.getD i false

lemma primaryRenameRel_step {n : ℕ} (ρ : Fin n → Fin n) (w w' : List Bool) (g : Gate)
    (h : primaryRenameRel ρ w w') :
    primaryRenameRel ρ (primaryRenameStep w g)
      (primaryRenameStep w' (primaryRenameGate ρ g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (primaryRenameGate ρ g).op.eval
      ((primaryRenameGate ρ g).inputs.map fun i => w'.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
    simp only [primaryRenameGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact h3 i
  refine ⟨by simp [primaryRenameStep]; omega, by simp [primaryRenameStep, h2], ?_⟩
  intro i
  simp only [primaryRenameStep, hv]
  rcases Nat.lt_trichotomy i w.length with hi | hi | hi
  · have hlt : primaryRenameIndex ρ i < w'.length := by
      unfold primaryRenameIndex
      split
      · have := (ρ ⟨i, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hi]
    exact h3 i
  · have he : primaryRenameIndex ρ i = w'.length := by
      unfold primaryRenameIndex
      split <;> omega
    rw [he, hi]
    simp
  · have hge : w'.length + 1 ≤ primaryRenameIndex ρ i := by
      unfold primaryRenameIndex
      split <;> omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma primaryRenameRel_fold {n : ℕ} (ρ : Fin n → Fin n) (gates : List Gate) :
    ∀ w w', primaryRenameRel ρ w w' →
      primaryRenameRel ρ (gates.foldl primaryRenameStep w)
        ((gates.map (primaryRenameGate ρ)).foldl primaryRenameStep w') := by
  induction gates with
  | nil => intro w w' h; exact h
  | cons g gates ih =>
    intro w w' h
    exact ih _ _ (primaryRenameRel_step ρ w w' g h)

lemma primaryRenameRel_init {n : ℕ} (ρ : Fin n → Fin n) (x : Fin n → Bool) :
    primaryRenameRel ρ (List.ofFn (x ∘ ρ)) (List.ofFn x) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i
  unfold primaryRenameIndex
  split
  · rename_i hi
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hi)]
    simp
  · rename_i hi
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma primaryRename_eval {n : ℕ} (ρ : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) :
    (primaryRename ρ C).eval (List.ofFn x) = C.eval (List.ofFn (x ∘ ρ)) :=
  (primaryRenameRel_fold ρ C.gates _ _ (primaryRenameRel_init ρ x)).2.2 C.output

lemma primaryRename_length {n : ℕ} (ρ : Fin n → Fin n) (C : Circuit) :
    (primaryRename ρ C).gates.length = C.gates.length := by simp [primaryRename]

lemma primaryRename_operations {n : ℕ} (ρ : Fin n → Fin n) (C : Circuit) :
    (primaryRename ρ C).gates.map Gate.op = C.gates.map Gate.op := by
  simp [primaryRename, primaryRenameGate, List.map_map]

lemma primaryRename_basis {n : ℕ} (ρ : Fin n → Fin n) (C : Circuit) (P : GateOp → Prop)
    (h : ∀ g ∈ C.gates, P g.op ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ (primaryRename ρ C).gates, P g.op ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  exact ⟨(h g0 hg0).1, by simpa [primaryRenameGate] using (h g0 hg0).2⟩

lemma primaryRename_not_unique {n : ℕ} (ρ : Fin n → Fin n) (C : Circuit)
    (h : ∀ i j : Fin C.gates.length, (C.gates.get i).op = GateOp.not →
      (C.gates.get j).op = GateOp.not → i = j) :
    ∀ i j : Fin (primaryRename ρ C).gates.length,
      ((primaryRename ρ C).gates.get i).op = GateOp.not →
      ((primaryRename ρ C).gates.get j).op = GateOp.not → i = j := by
  dsimp only [primaryRename]
  intro i j hi hj
  let i' : Fin C.gates.length := ⟨i.val, by simpa [primaryRename] using i.isLt⟩
  let j' : Fin C.gates.length := ⟨j.val, by simpa [primaryRename] using j.isLt⟩
  have hi' : (C.gates.get i').op = GateOp.not := by
    change ((C.gates.map (primaryRenameGate ρ)).get i).op = GateOp.not at hi
    rw [List.get_eq_getElem, List.getElem_map] at hi
    exact hi
  have hj' : (C.gates.get j').op = GateOp.not := by
    change ((C.gates.map (primaryRenameGate ρ)).get j).op = GateOp.not at hj
    rw [List.get_eq_getElem, List.getElem_map] at hj
    exact hj
  have hv : i'.val = j'.val := congrArg Fin.val (h i' j' hi' hj')
  exact Fin.ext hv


-- Adapted from L_meta_10538.lean; retains its live-set and restriction certificate.
namespace Completion01Proof
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 128
def zero : Sig := 0
def one : Sig := BitVec.allOnes 128
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
lemma allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
lemma bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
lemma flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
lemma Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
lemma Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
lemma Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 128) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
lemma bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
lemma nrm_false (a : Sig) : nrm false a = a := rfl
lemma nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
lemma nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
lemma neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
lemma nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
lemma proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
lemma proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
lemma bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
lemma nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

lemma norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
lemma prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
lemma repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
lemma repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

-- Remove a last computed signal from a backward derivation. A gate whose value
-- is already available, or is unused by the suffix, needs no entry in the plan.
private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
lemma Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
lemma Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
lemma Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
lemma Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
lemma Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
lemma Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
lemma Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

lemma mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

lemma mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

lemma inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

lemma inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
lemma cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
lemma avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
lemma both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

lemma from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

lemma available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

lemma extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
lemma comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
lemma extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

lemma mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

lemma contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

lemma restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

lemma restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
lemma restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

lemma projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 128
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

lemma bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

lemma table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

lemma observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

lemma obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

lemma obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

lemma map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

lemma kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

lemma kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

lemma list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)


lemma table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

lemma table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

lemma available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

lemma reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
lemma nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
lemma reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

lemma live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

lemma raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
lemma bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
lemma observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
lemma rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

lemma rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
lemma rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
lemma live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

lemma mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
lemma reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
lemma lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

lemma lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

lemma observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

lemma mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
lemma mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

lemma lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

lemma erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

lemma enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

lemma covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

lemma cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

lemma cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

lemma masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

lemma masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

lemma masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

lemma availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h


-- Natural-number words, and a search table checked level by level.
def W (a : Nat) : Sig := BitVec.ofNat 128 a
def full : Nat := 0xffffffffffffffffffffffffffffffff
def xN : Nat → Nat
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | _ => 0xffffffffffffffff0000000000000000
def nb (o a b : Nat) : Nat :=
  bif Nat.beq o 0 then Nat.land a b else bif Nat.beq o 1 then Nat.lor a b else
    bif Nat.beq o 2 then Nat.xor a (Nat.land a b) else Nat.xor b (Nat.land a b)
lemma bit_W (r : Row) (a : Nat) : bit r (W a) = a.testBit r.val := by
  unfold bit W
  rw [BitVec.getLsbD_ofNat]
  simp [r.isLt]
lemma tb_land (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) := Nat.testBit_and ..
lemma tb_lor (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) := Nat.testBit_or ..
lemma tb_xor (a b i : Nat) : (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) := Nat.testBit_xor ..
lemma nbeq {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h
lemma W_nb (o a b : Nat) : W (nb o a b) = bin o (W a) (W b) := by
  apply bit_ext
  intro r
  rw [bit_bin,bit_W,bit_W,bit_W]
  by_cases h0 : o = 0
  · subst h0
    exact tb_land a b _
  by_cases h1 : o = 1
  · subst h1
    exact tb_lor a b _
  by_cases h2 : o = 2
  · subst h2
    change (Nat.xor a (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
  · unfold nb
    rw [nbeq h0,nbeq h1,nbeq h2,if_neg h0,if_neg h1,if_neg h2]
    change (Nat.xor b (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
lemma bin_four (o : Nat) : ∃ e, e < 4 ∧ ∀ a b, bin o a b = bin e a b := by
  by_cases h : o < 4
  · exact ⟨o,h,fun _ _ => rfl⟩
  · refine ⟨3,by omega,fun a b => ?_⟩
    have h0 : o ≠ 0 := by omega
    have h1 : o ≠ 1 := by omega
    have h2 : o ≠ 2 := by omega
    simp [bin,h0,h1,h2]
lemma W_zero : W 0 = zero := rfl
lemma W_full : W full = one := by
  apply bit_ext
  intro r
  rw [bit_W,bit_one]
  revert r
  decide +kernel
lemma W_inj {a b : Nat} (ha : a < 2^128) (hb : b < 2^128) (h : W a = W b) : a = b := by
  have := congrArg BitVec.toNat h
  simpa only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using this

def rootsW (R : List Nat) : List Sig := R.map fun i => W (xN i)
def LowN (R : List Nat) (T L : Nat) : Prop := Lower true (rootsW R) (W T) L
abbrev SliceD := Nat × Nat × List Nat
def SliceN (R : List Nat) (T : Nat) (s : SliceD) : Prop :=
  Slice true (rootsW R) (W T) (W s.1) s.2.1 ∧ ∀ v ∈ s.2.2, v ∈ R

def baseOK (T : Nat) (R : List Nat) (E : List (Nat × Nat × Nat)) : Bool :=
  decide (T < 2^128) && !(T.testBit 0) && (E.map Prod.fst == R) && !R.isEmpty && decide (rootsW R).Nodup &&
  R.all (fun i => !((xN i).testBit 0)) &&
  E.all (fun e => decide (e.2.1 < 128) && decide (e.2.2 < 128) && (T.testBit e.2.1 != T.testBit e.2.2) &&
    R.all (fun i => i == e.1 || (xN i).testBit e.2.1 == (xN i).testBit e.2.2))

def BaseP (T : Nat) (R : List Nat) : Prop :=
  T < 2^128 ∧ plainWord (W T) = true ∧ (rootsW R).Nodup ∧
  (rootsW R).all plainWord = true ∧
  (∀ a ∈ rootsW R, Essential (W T) (rootsW R) a) ∧ proper (W T)
namespace BaseP
lemma lt {T R} (h : BaseP T R) : T < 2^128 := h.1
lemma plain {T R} (h : BaseP T R) : plainWord (W T) = true := h.2.1
lemma nodup {T R} (h : BaseP T R) : (rootsW R).Nodup := h.2.2.1
lemma plainR {T R} (h : BaseP T R) : (rootsW R).all plainWord = true := h.2.2.2.1
lemma ess {T R} (h : BaseP T R) : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := h.2.2.2.2.1
lemma prop {T R} (h : BaseP T R) : proper (W T) := h.2.2.2.2.2
end BaseP

lemma baseOK_ok {T R E} (h : baseOK T R E = true) : BaseP T R := by
  simp only [baseOK,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hT,h0⟩,hE⟩,hne⟩,nd⟩,pr⟩,he⟩ := h
  have ess : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rw [←hE] at hi
    obtain ⟨e,hem,rfl⟩ := List.mem_map.mp hi
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := he e hem
    refine ⟨⟨e.2.1,h1⟩,⟨e.2.2,h2⟩,?_,?_⟩
    · rw [bit_W,bit_W]
      simpa using h3
    · intro v hv hne
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
      rw [bit_W,bit_W]
      have := h4 j hj
      simp only [Bool.or_eq_true,beq_iff_eq] at this
      rcases this with rfl | this
      · exact absurd rfl hne
      · exact this
  refine ⟨hT,?_,nd,?_,ess,?_⟩
  · have : bit 0 (W T) = false := (bit_W 0 T).trans h0
    simp [plainWord,this]
  · rw [List.all_eq_true]
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    have : bit 0 (W (xN i)) = false := (bit_W 0 _).trans (by simpa using pr i hi)
    simp [plainWord,this]
  · cases R with
    | nil => simp at hne
    | cons i R =>
      obtain ⟨r,s,hd,_⟩ := ess (W (xN i)) (by simp [rootsW])
      constructor
      · intro hh
        rw [hh,bit_zero,bit_zero] at hd
        exact hd rfl
      · intro hh
        rw [hh,bit_one,bit_one] at hd
        exact hd rfl

lemma lowOf {T R E K} (hB : baseOK T R E = true) (h : Impossible true (W T) K (rootsW R).toFinset) :
    LowN R T (K+1) := by
  have b := baseOK_ok hB
  exact lower_impossible b.prop b.plain b.plainR b.ess h
lemma lowCount {T R E K} (hB : baseOK T R E = true) (h : K + 2 ≤ R.length) : LowN R T (K+1) := by
  apply lowOf hB
  intro k hk run
  have b := baseOK_ok hB
  have := live_size run
  rw [List.toFinset_card_of_nodup b.nodup,rootsW,List.length_map] at this
  omega

def rowOf : List Nat → Nat → Nat → Nat
  | [],w,_ => w
  | v::vs,w,r => rowOf vs (w + ((r % 2) <<< v)) (r / 2)
def sliceChk (R : List Nat) (T : Nat) (R' : List Nat) (G d : Nat) (vs : List Nat) (w : Nat) : Bool :=
  vs.all (fun v => R.contains v) &&
  (List.range 128).all (fun r => let q := rowOf vs w r
    Nat.blt q 128 && d.testBit q && (T.testBit q == G.testBit r)) &&
  R.all (fun i => (List.range 128).all (fun r => !((xN i).testBit (rowOf vs w r))) ||
    (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r)) ||
    R'.any (fun j => (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r) == (xN j).testBit r)))

lemma mkSlice {R T E R' G E' d L vs w} (_hB : baseOK T R E = true) (hB' : baseOK G R' E' = true)
    (hL : LowN R' G L) (h : sliceChk R T R' G d vs w = true) : SliceN R T (d,L,vs) := by
  have b' := baseOK_ok hB'
  simp only [sliceChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,Bool.or_eq_true,beq_iff_eq,
    Bool.not_eq_true',List.any_eq_true,Nat.blt_eq,List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨⟨hv,hr⟩,hR⟩ := h
  let f : Row → Row := fun r => ⟨rowOf vs w r.val,(hr r.val r.isLt).1.1⟩
  have fe (r : Row) (a : Nat) : bit (f r) (W a) = a.testBit (rowOf vs w r.val) := bit_W _ _
  have obs : restrictRows f (observe (W T)) = observe (W G) := by
    funext r
    change bit (f r) (W T) = bit r (W G)
    rw [fe,bit_W]
    exact (hr r.val r.isLt).2
  refine ⟨⟨f,rootsW R',?_,?_,?_,?_⟩,hv⟩
  · intro r
    rw [fe]
    exact (hr r.val r.isLt).1.2
  · intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rcases hR i hi with (h | h) | ⟨j,hj,h⟩
    · refine Or.inr (Or.inl ⟨false,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · refine Or.inr (Or.inl ⟨true,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · have e : restrictRows f (observe (W (xN i))) = observe (W (xN j)) := by
        funext r
        exact (fe r _).trans ((h r.val r.isLt).trans (bit_W r _).symm)
      rw [e]
      exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hj))
  · rw [obs]
    exact observe_proper b'.prop
  · rw [obs]
    exact hL

def av (d : Nat) (P : List Nat) (v : Nat) : Bool :=
  let m := Nat.land v d
  Nat.beq m 0 || Nat.beq m d || P.any (fun x => Nat.beq x m || Nat.beq x (Nat.xor d m))
def cn (d v : Nat) : Nat :=
  let m := Nat.land v d
  bif Nat.beq m 0 || Nat.beq m d then 1 else 0
def sumc (d : Nat) : List Nat → Nat
  | [] => 0
  | v::l => Nat.add (cn d v) (sumc d l)
def mkPool (P : List Nat) : List (Nat × Nat × Nat) → List Nat
  | [] => P
  | c::cs => mkPool (P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)]) cs
def initPool (d : Nat) (vs : List Nat) : List Nat := vs.map fun v => Nat.land (xN v) d

abbrev RF (f : Row → Row) (v : Nat) : Wire Row := restrictRows f (observe (W v))
def PS (f : Row → Row) (bank : List (Wire Row)) (P : List Nat) : Prop :=
  ∀ v ∈ P, Available true bank (RF f v)
lemma rf_apply (f : Row → Row) (v : Nat) (r : Row) : RF f v r = v.testBit (f r).val := bit_W _ _
lemma rf_land {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) :
    RF f (Nat.land v d) = RF f v := by
  funext r
  have h := dom r
  rw [bit_W] at h
  rw [rf_apply,rf_apply]
  have : (Nat.land v d).testBit (f r).val = (v.testBit (f r).val && d.testBit (f r).val) := Nat.testBit_and ..
  rw [this,h,Bool.and_true]
lemma rf_zero {f : Row → Row} : RF f 0 = fun _ => false := by
  funext r
  rw [rf_apply]
  exact Nat.zero_testBit _
lemma rf_dom {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) : RF f d = fun _ => true := by
  funext r
  exact dom r
lemma rf_xor {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (m : Nat) :
    RF f (Nat.xor d m) = inv (RF f m) := by
  funext r
  have h := dom r
  rw [bit_W] at h
  change RF f (Nat.xor d m) r = !(RF f m r)
  rw [rf_apply,rf_apply]
  have : (Nat.xor d m).testBit (f r).val = ((d.testBit (f r).val) ^^ (m.testBit (f r).val)) := Nat.testBit_xor ..
  rw [this,h,Bool.true_xor]
lemma cn_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) : cn d v ≤ cost (RF f v) := by
  change (bif (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d) then 1 else 0) ≤ _
  cases h : (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d)
  · exact Nat.zero_le _
  · have c : Constant (RF f v) := by
      rw [←rf_land dom v]
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Nat.eq_of_beq_eq_true h,rf_zero]
        exact ⟨false,rfl⟩
      · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
        exact ⟨true,rfl⟩
    rw [cost,if_pos c]
    exact Nat.le_refl 1
lemma av_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) {bank P v} (hP : PS f bank P)
    (h : av d P v = true) : Available true bank (RF f v) := by
  simp only [av,Bool.or_eq_true,List.any_eq_true] at h
  rw [←rf_land dom v]
  rcases h with (h | h) | ⟨x,hx,h | h⟩
  · rw [Nat.eq_of_beq_eq_true h,rf_zero]
    exact Or.inr (Or.inl ⟨false,rfl⟩)
  · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
    exact Or.inr (Or.inl ⟨true,rfl⟩)
  · rw [←Nat.eq_of_beq_eq_true h]
    exact hP x hx
  · have e := hP x hx
    rw [Nat.eq_of_beq_eq_true h,rf_xor dom] at e
    have e' := avail_inv rfl e
    rwa [inv_inv'] at e'
lemma rf_nb (f : Row → Row) (o a b : Nat) : RF f (nb o a b) = comb o (RF f a) (RF f b) := by
  unfold RF
  rw [W_nb,obs_bin,restrict_comb]
lemma pay_nb {f : Row → Row} {roots bank p P} (o a b : Nat) (hr : Reach true roots p bank) (hP : PS f bank P)
    (ha : Available true bank (RF f a)) (hb : Available true bank (RF f b)) :
    ∃ next, Reach true roots (p+1) next ∧ PS f next P ∧ Available true next (RF f (nb o a b)) ∧
      ∀ v, Available true bank v → Available true next v := by
  obtain ⟨e,he,heq⟩ := bin_four o
  have hn : RF f (nb o a b) = comb e (RF f a) (RF f b) := by
    unfold RF
    rw [W_nb,heq,obs_bin,restrict_comb]
  obtain ⟨op,x,y,e1,hx,hy,_,_⟩ := comb_prime (d:=e) (Or.inr ⟨rfl,he⟩) ha hb
  refine ⟨_,Reach.two op hr hx hy,fun v hv => available_cons _ (hP v hv),?_,fun v hv => available_cons _ hv⟩
  rw [hn,e1]
  exact Or.inl (by simp)
lemma getD_ps {f : Row → Row} {bank P} (hP : PS f bank P) (i : Nat) : Available true bank (RF f (P.getD i 0)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : P[i]? with
  | none => exact Or.inr (Or.inl ⟨false,rf_zero⟩)
  | some a => exact hP a (List.mem_of_getElem? h)
lemma mkPool_ok {f : Row → Row} {roots} (cs : List (Nat × Nat × Nat)) {bank p P} (hr : Reach true roots p bank)
    (hP : PS f bank P) : ∃ next, Reach true roots (p+cs.length) next ∧ PS f next (mkPool P cs) := by
  induction cs generalizing bank p P with
  | nil => exact ⟨bank,hr,hP⟩
  | cons c cs ih =>
    obtain ⟨next,h1,h2,h3,_⟩ := pay_nb c.1 _ _ hr hP (getD_ps hP c.2.1) (getD_ps hP c.2.2)
    have : PS f next (P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)]) := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact h2 v hv
      · rw [List.mem_singleton.mp hv]
        exact h3
    obtain ⟨out,o1,o2⟩ := ih h1 this
    exact ⟨out,by rw [List.length_cons,show p+(cs.length+1) = p+1+cs.length by omega]; exact o1,o2⟩

abbrev CutV := Nat × Nat × Nat × List Nat
def keepB (d : Nat) (P : List Nat) (ka : Bool) (a : Nat) : Bool := bif ka then av d P a else true
def keepC (d : Nat) (ka : Bool) (a : Nat) : Nat := bif ka then cn d a else 0
def cutEval (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (c : CutV) : Bool :=
  rest.all (av c.1 c.2.2.2) && keepB c.1 c.2.2.2 ka a && keepB c.1 c.2.2.2 kb b &&
  (bif av c.1 c.2.2.2 z then
    Nat.blt (Nat.add k c.2.2.1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b))))
  else av c.1 c.2.2.2 a && av c.1 c.2.2.2 b &&
    Nat.blt (Nat.add (Nat.add k c.2.2.1) 1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b)))))
def sepEval (rest : List Nat) (a b z : Nat) (ka kb : Bool) (p : Nat × Nat) : Bool :=
  let e := fun v => (Nat.testBit v p.1 == Nat.testBit v p.2)
  e z && (!ka || e a) && (!kb || e b) && rest.all e
def sepOK (T : Nat) (p : Nat × Nat) : Bool := Nat.blt p.1 128 && Nat.blt p.2 128 && (T.testBit p.1 != T.testBit p.2)

def kidW (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Sig :=
  W z :: kept ka (W a) (kept kb (W b) (rest.map W))
lemma sumc_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (l : List Nat) :
    sumc d l ≤ mass (l.map (RF f)) := by
  induction l with
  | nil => simp [sumc]
  | cons v l ih =>
    rw [List.map_cons,mass_cons]
    exact Nat.add_le_add (cn_ok dom v) ih
lemma mass_keep {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (ka : Bool) (a : Nat) (l : List (Wire Row)) :
    keepC d ka a + mass l ≤ mass (kept ka (RF f a) l) := by
  cases ka
  · simp [keepC,kept]
  · rw [kept,if_pos rfl,mass_cons]
    exact Nat.add_le_add_right (cn_ok dom a) _
lemma kid_map (f : Row → Row) (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidW rest a b z ka kb).map observe).map (restrictRows f) =
      RF f z :: kept ka (RF f a) (kept kb (RF f b) (rest.map (RF f))) := by
  cases ka <;> cases kb <;> simp [kidW,kept,List.map_map,Function.comp_def,RF]

def CutP (R : List Nat) (T : Nat) (c : CutV) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)), (∀ r, bit (f r) (W c.1) = true) ∧
    ¬Constant (restrictRows f (observe (W T))) ∧ Reach true (roots.map observe) c.2.2.1 bank ∧ PS f bank c.2.2.2 ∧
    ∀ p bank, Reach true (roots.map observe) p bank → Available true bank (restrictRows f (observe (W T))) → c.2.1 ≤ p

lemma cut_sound {R T c k rest a b o ka kb} (hc : CutP R T c)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : cutEval k rest a b (nb o a b) ka kb c = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  obtain ⟨f,roots,bank,dom,nc,hr,hP,lo⟩ := hc
  simp only [cutEval,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have key : ∃ q bank', Reach true (roots.map observe) q bank' ∧ PS f bank' c.2.2.2 ∧ Available true bank' (RF f (nb o a b)) ∧
      k + q < c.2.1 + ((sumc c.1 rest + cn c.1 (nb o a b)) + (keepC c.1 ka a + keepC c.1 kb b)) := by
    cases hz : av c.1 c.2.2.2 (nb o a b)
    · rw [hz,cond_false,Bool.and_eq_true,Bool.and_eq_true,Nat.blt_eq] at h4
      obtain ⟨next,n1,n2,n3,_⟩ := pay_nb o a b hr hP (av_ok dom hP h4.1.1) (av_ok dom hP h4.1.2)
      refine ⟨_,next,n1,n2,n3,?_⟩
      have := h4.2
      exact this
    · rw [hz,cond_true,Nat.blt_eq] at h4
      exact ⟨_,bank,hr,hP,av_ok dom hP hz,h4⟩
  obtain ⟨q,bank',r1,r2,r3,r4⟩ := key
  intro k' hk run
  have supp : supply true bank' (((kidW rest a b (nb o a b) ka kb).map observe).map (restrictRows f)) := by
    rw [kid_map]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact r3
    have kb' : ∀ v ∈ kept kb (RF f b) (rest.map (RF f)), Available true bank' v := by
      intro v hv
      cases kb
      · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
        exact av_ok dom r2 (h1 x hx)
      · rcases List.mem_cons.mp hv with rfl | hv
        · exact av_ok dom r2 h3
        · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
          exact av_ok dom r2 (h1 x hx)
    cases ka
    · exact kb' v hv
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact av_ok dom r2 h2
      · exact kb' v hv
  have bound := projected_bound f (list_run run _ nd rfl) nc r1 supp lo
  rw [kid_map,mass_cons] at bound
  have m1 := mass_keep dom ka a (kept kb (RF f b) (rest.map (RF f)))
  have m2 := mass_keep dom kb b (rest.map (RF f))
  have m3 := sumc_ok dom rest
  have m4 := cn_ok dom (nb o a b)
  omega

lemma sep_sound {T k rest a b o ka kb p} (hT : sepOK T p = true)
    (h : sepEval rest a b (nb o a b) ka kb p = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  simp only [sepOK,Bool.and_eq_true,Nat.blt_eq,bne_iff_ne] at hT
  obtain ⟨⟨p1,p2⟩,hd⟩ := hT
  simp only [sepEval,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',beq_iff_eq,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  intro k' _ run
  obtain ⟨v,hv,hne⟩ := live_row_difference run (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W,bit_W]; exact hd)
  apply hne
  rw [List.mem_toFinset] at hv
  rcases List.mem_cons.mp hv with rfl | hv
  · rw [bit_W,bit_W]; exact h1
  rcases mem_kept hv with rfl | hv'
  · cases ka
    · cases kb
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        rw [←e,bit_W,bit_W]; exact h4 x hx
      · rcases List.mem_cons.mp hv with e | hv
        · rw [e,bit_W,bit_W]; exact h3.resolve_left (by simp)
        · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
          rw [←e,bit_W,bit_W]; exact h4 x hx
    · rw [bit_W,bit_W]; exact h2.resolve_left (by simp)
  · cases kb
    · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv'
      rw [←e,bit_W,bit_W]; exact h4 x hx
    · rcases List.mem_cons.mp hv' with e | hv
      · rw [e,bit_W,bit_W]; exact h3.resolve_left (by simp)
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        rw [←e,bit_W,bit_W]; exact h4 x hx

abbrev StD := List Nat × List (Nat × List (Nat × Nat × Nat)) × List (Nat × Nat) × List (List Nat)
def dupD (l : List StD) : List StD := l.map fun st => (st.1.map (Nat.mul 0x10000000000000001),st.2)
def picks : List Nat → List (Nat × List Nat)
  | [] => []
  | x::xs => (x,xs) :: (picks xs).map fun p => (p.1,x::p.2)
def pairs : List Nat → List (Nat × Nat × List Nat)
  | [] => []
  | x::xs => ((picks xs).map fun p => (x,p.1,p.2)) ++ (pairs xs).map fun p => (p.1,p.2.1,x::p.2.2)
lemma picks_ok {l : List Nat} {a : Nat} (h : a ∈ l) : ∃ p ∈ picks l, p.1 = a ∧ (a::p.2).Perm l := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨(a,xs),by simp [picks],rfl,List.Perm.refl _⟩
    · obtain ⟨p,hp,rfl,q⟩ := ih h
      refine ⟨(p.1,x::p.2),?_,rfl,?_⟩
      · simp only [picks,List.mem_cons,List.mem_map]
        exact Or.inr ⟨p,hp,rfl⟩
      · exact (List.Perm.swap x p.1 p.2).trans (q.cons x)
lemma pairs_ok {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    ∃ p ∈ pairs l, (p.1::p.2.1::p.2.2).Perm l ∧ ((p.1 = a ∧ p.2.1 = b) ∨ (p.1 = b ∧ p.2.1 = a)) := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    have first (c : Nat) (hc : c ∈ xs) : ∃ p ∈ pairs (x::xs), (p.1::p.2.1::p.2.2).Perm (x::xs) ∧ p.1 = x ∧ p.2.1 = c := by
      obtain ⟨p,hp,rfl,q⟩ := picks_ok hc
      refine ⟨(x,p.1,p.2),?_,q.cons x,rfl,rfl⟩
      simp only [pairs,List.mem_append,List.mem_map]
      exact Or.inl ⟨p,hp,rfl⟩
    rcases List.mem_cons.mp ha with rfl | ha2
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd rfl hab
      · obtain ⟨p,h1,h2,h3,h4⟩ := first b hb
        exact ⟨p,h1,h2,Or.inl ⟨h3,h4⟩⟩
    · rcases List.mem_cons.mp hb with e | hb
      · subst e
        obtain ⟨p,h1,h2,h3,h4⟩ := first a ha2
        exact ⟨p,h1,h2,Or.inr ⟨h3,h4⟩⟩
      · obtain ⟨p,hp,q,e⟩ := ih ha2 hb
        refine ⟨(p.1,p.2.1,x::p.2.2),?_,?_,e⟩
        · simp only [pairs,List.mem_append,List.mem_map]
          exact Or.inr ⟨p,hp,rfl⟩
        · exact ((List.Perm.swap x p.2.1 p.2.2).cons p.1).trans ((List.Perm.swap x p.1 _).trans (q.cons x))

def mem1 (z : Nat) (l : List Nat) : Bool := l.any fun x => Nat.beq x z
def beqL : List Nat → List Nat → Bool
  | [],[] => true
  | x::xs,y::ys => Nat.beq x y && beqL xs ys
  | _,_ => false
lemma beqL_ok {a b : List Nat} (h : beqL a b = true) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons => simp [beqL] at h
  | cons x xs ih => cases b with
    | nil => simp [beqL] at h
    | cons y ys =>
      simp only [beqL,Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1,ih h.2]
def ins (z : Nat) : List Nat → List Nat
  | [] => [z]
  | x::xs => bif Nat.ble z x then z::x::xs else x :: ins z xs
lemma mem_ins {z v : Nat} {l : List Nat} : v ∈ ins z l ↔ v = z ∨ v ∈ l := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    unfold ins
    cases Nat.ble z x
    · simp only [cond_false,List.mem_cons,ih]
      tauto
    · simp
def kidN (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Nat :=
  ins z (bif ka then ins a (bif kb then ins b rest else rest) else bif kb then ins b rest else rest)
lemma kid_fin (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidN rest a b z ka kb).map W).toFinset = (kidW rest a b z ka kb).toFinset := by
  ext v
  cases ka <;> cases kb <;> simp [kidN,kidW,kept,mem_ins] <;> aesop

def keeps : List (Bool × Bool) := [(true,true),(true,false),(false,true),(false,false)]
def bl (b : Bool) : Nat := bif b then 1 else 0
def mkCut (Z : List SliceD) (c : Nat × List (Nat × Nat × Nat)) : CutV :=
  let s := Z.getD c.1 (0,0,[])
  (s.1,s.2.1,c.2.length,mkPool (initPool s.1 s.2.2) c.2)
def hintOK (k : Nat) (cuts : List CutV) (seps : List (Nat × Nat)) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  bif Nat.blt i 1000 then (match cuts[i]? with
    | some c => cutEval k rest a b z ka kb c
    | none => false)
  else (match seps[i-1000]? with
    | some q => sepEval rest a b z ka kb q
    | none => false)
def kidOK (k : Nat) (next : List (List Nat)) (cuts : List CutV) (seps : List (Nat × Nat)) (rest : List Nat) (hints : List Nat)
    (a b z : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add rest.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
  hints.any (hintOK k cuts seps rest a b z kk.1 kk.2) ||
  next.any (beqL (kidN rest a b z kk.1 kk.2))
def pairOK (k : Nat) (next : List (List Nat)) (cuts : List CutV) (seps : List (Nat × Nat)) (s : List Nat)
    (p : Nat × Nat × List Nat) (hints : List Nat) : Bool :=
  [0,1,2,3].all fun o =>
    let z := nb o p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      keeps.all (kidOK k next cuts seps p.2.2 hints p.1 p.2.1 z)
def allZip (f : Nat × Nat × List Nat → List Nat → Bool) : List (Nat × Nat × List Nat) → List (List Nat) → Bool
  | [],_ => true
  | p::ps,[] => f p [] && allZip f ps []
  | p::ps,h::hs => f p h && allZip f ps hs
lemma allZip_ok {f ps hs} (h : allZip f ps hs = true) : ∀ p ∈ ps, ∃ x, f p x = true := by
  induction ps generalizing hs with
  | nil => intro p hp; cases hp
  | cons q ps ih =>
    intro p hp
    cases hs with
    | nil =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
    | cons x hs =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
def asc : List Nat → Bool
  | [] => true
  | [x] => Nat.blt x (2^128)
  | x::y::l => Nat.blt x y && asc (y::l)
lemma asc_ok {l : List Nat} (h : asc l = true) : l.Pairwise (· < ·) ∧ ∀ x ∈ l, x < 2^128 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases l with
    | nil =>
      simp only [asc,Nat.blt_eq] at h
      simpa using h
    | cons y l =>
      simp only [asc,Bool.and_eq_true,Nat.blt_eq] at h
      obtain ⟨i1,i2⟩ := ih h.2
      have hy := List.pairwise_cons.mp i1
      refine ⟨List.pairwise_cons.mpr ⟨?_,i1⟩,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1
        · exact h.1.trans (hy.1 v hv)
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1.trans (i2 y (by simp))
        · exact i2 v hv
lemma asc_nodup {l : List Nat} (h : asc l = true) : l.Nodup ∧ (l.map W).Nodup := by
  obtain ⟨h1,h2⟩ := asc_ok h
  have nd : l.Nodup := h1.imp (fun h => Nat.ne_of_lt h)
  refine ⟨nd,?_⟩
  refine nd.map_on ?_
  intro x hx y hy e
  exact W_inj (h2 x hx) (h2 y hy) e
def stOK (T : Nat) (Z : List SliceD) (k : Nat) (next : List (List Nat)) (st : StD) : Bool :=
  asc st.1 && !(mem1 T st.1) && st.2.2.1.all (sepOK T) && st.2.1.all (fun c => Nat.blt c.1 Z.length) &&
  allZip (pairOK k next (st.2.1.map (mkCut Z)) st.2.2.1 st.1) (pairs st.1) st.2.2.2
def levelOK (T : Nat) (Z : List SliceD) (k : Nat) (next : List (List Nat)) (D : List StD) : Bool :=
  D.all (stOK T Z k next)
def LevelN (R : List Nat) (T k : Nat) (D : List StD) : Prop :=
  ∀ st ∈ D, Impossible true (W T) k (st.1.map W).toFinset

lemma stStep {R T E Z k next st} (hB : baseOK T R E = true) (hZ : ∀ s ∈ Z, SliceN R T s)
    (hn : ∀ s ∈ next, Impossible true (W T) k (s.map W).toFinset)
    (h : stOK T Z k next st = true) : Impossible true (W T) (k+1) (st.1.map W).toFinset := by
  have b := baseOK_ok hB
  simp only [stOK,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨⟨ha,hT⟩,hs⟩,hcut⟩,hz⟩ := h
  obtain ⟨nd,ndW⟩ := asc_nodup ha
  have lt := (asc_ok ha).2
  have hTm : W T ∉ st.1.map W := by
    intro hm
    obtain ⟨x,hx,e⟩ := List.mem_map.mp hm
    have := W_inj (lt x hx) b.lt e
    subst this
    have : mem1 x st.1 = true := List.any_eq_true.mpr ⟨x,hx,Nat.beq_refl x⟩
    rw [hT] at this
    exact Bool.noConfusion this
  have good : ∀ c ∈ st.2.1.map (mkCut Z), CutP R T c := by
    intro c hc
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
    have hi : q.1 < Z.length := by simpa only [Nat.blt_eq] using hcut q hq
    have hm : Z.getD q.1 (0,0,[]) ∈ Z := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
      exact List.getElem_mem hi
    obtain ⟨⟨f,roots,dom,base,nc,lo⟩,hv⟩ := hZ _ hm
    have ps : PS f (roots.map observe) (initPool (Z.getD q.1 (0,0,[])).1 (Z.getD q.1 (0,0,[])).2.2) := by
      intro v hv'
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv'
      rw [rf_land dom]
      exact base _ (List.mem_map_of_mem (hv j hj))
    obtain ⟨bank,b1,b2⟩ := mkPool_ok q.2 (Reach.start (u:=true) (roots:=roots.map observe)) ps
    refine ⟨f,roots,bank,dom,nc,?_,b2,lo⟩
    simpa [mkCut] using b1
  apply enum_step ndW hTm
  intro a' ha' b' hb' d hd ka kb hab fresh hprop hlen
  obtain ⟨a,ham,rfl⟩ := List.mem_map.mp ha'
  obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hb'
  have hac : a ≠ c := fun h => hab (by rw [h])
  have hd4 : d < 4 := by
    rcases hd with h | ⟨_,h⟩ <;> omega
  obtain ⟨p,hp,perm,ho⟩ := pairs_ok ham hcm hac
  obtain ⟨x,hx⟩ := allZip_ok hz p hp
  -- one unordered pair serves both orders
  have core : ∀ (o : Nat) (ja jb : Bool), o < 4 → W (nb o p.1 p.2.1) = bin d (W a) (W c) →
      (p.2.2.length + (bl ja + bl jb) ≤ k) →
      Impossible true (W T) k (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).toFinset := by
    intro o ja jb ho4 hW hl
    have hf := List.all_eq_true.mp hx o (by
      have : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by omega
      simpa using this)
    simp only [Bool.or_eq_true] at hf
    have pm (v : Nat) : v ∈ st.1 ↔ v = p.1 ∨ v = p.2.1 ∨ v ∈ p.2.2 := by
      rw [←perm.mem_iff]
      simp
    rcases hf with ((hf | hf) | hf) | hf
    · exfalso
      obtain ⟨y,hy,e⟩ := List.any_eq_true.mp hf
      apply fresh
      rw [←hW,←Nat.eq_of_beq_eq_true e]
      exact List.mem_map_of_mem hy
    · exfalso
      apply hprop.1
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      rfl
    · exfalso
      apply hprop.2
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      exact W_full
    have hk := List.all_eq_true.mp hf (ja,jb) (by cases ja <;> cases jb <;> simp [keeps])
    simp only [kidOK,Bool.or_eq_true] at hk
    have ndp : ((p.1::p.2.1::p.2.2).map W).Nodup := (perm.map W).nodup_iff.mpr ndW
    simp only [List.map_cons,List.nodup_cons,List.mem_cons,not_or] at ndp
    have nk : (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).Nodup := by
      have n1 := kept_nd jb (W p.2.1) _ ndp.2.2 ndp.2.1
      have n2 : W p.1 ∉ kept jb (W p.2.1) (p.2.2.map W) := by
        cases jb
        · exact ndp.1.2
        · simp only [kept,if_true,List.mem_cons,not_or]
          exact ndp.1
      refine List.nodup_cons.mpr ⟨?_,kept_nd ja _ _ n1 n2⟩
      intro hm
      apply fresh
      rw [←hW]
      have sub : W (nb o p.1 p.2.1) ∈ (p.1::p.2.1::p.2.2).map W := by
        rcases mem_kept hm with h | h
        · rw [h]; simp
        · rcases mem_kept h with h | h
          · rw [h]; simp
          · simp [h]
      exact (perm.map W).mem_iff.mp sub
    rcases hk with (hk | hk) | hk
    · exfalso
      rw [Nat.blt_eq] at hk
      have : k < p.2.2.length + (bl ja + bl jb) + 0 := hk
      omega
    · obtain ⟨i,_,hi⟩ := List.any_eq_true.mp hk
      unfold hintOK at hi
      cases hb : Nat.blt i 1000
      · rw [hb,cond_false] at hi
        cases hg : st.2.2.1[i-1000]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact sep_sound (hs q (List.mem_of_getElem? hg)) hi
      · rw [hb,cond_true] at hi
        cases hg : (st.2.1.map (mkCut Z))[i]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact cut_sound (good q (List.mem_of_getElem? hg)) nk hi
    · obtain ⟨s,hs',e⟩ := List.any_eq_true.mp hk
      rw [←kid_fin]
      rw [beqL_ok e]
      exact hn s hs'
  have rp : (((st.1.map W).erase (W a)).erase (W c)).Perm (p.2.2.map W) := by
    have e : (W a :: W c :: p.2.2.map W).Perm (st.1.map W) := by
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact perm.map W
      · exact (List.Perm.swap _ _ _).trans (perm.map W)
    have e1 := e.erase (W a)
    rw [List.erase_cons_head] at e1
    have e2 := e1.erase (W c)
    rw [List.erase_cons_head] at e2
    exact e2.symm
  have lenr : (((st.1.map W).erase (W a)).erase (W c)).length = p.2.2.length := by
    rw [rp.length_eq,List.length_map]
  have fits : p.2.2.length + (bl ka + bl kb) ≤ k := by
    have h := hlen
    unfold childTwo at h
    cases ka <;> cases kb <;> simp [kept,lenr] at h <;> simp [bl] <;> omega
  rw [Nat.add_sub_cancel]
  rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have r := core d ka kb hd4 (W_nb _ _ _) fits
    have e : (childTwo (st.1.map W) (W p.1) (W p.2.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb d p.1 p.2.1) ka kb).toFinset := by
      unfold childTwo kidW
      rw [W_nb]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff]
    rw [e]
    exact r
  · have hfl := flip_flip hd
    have f4 : flipOp d < 4 := by
      rcases hfl.1 with h | ⟨_,h⟩ <;> omega
    have r := core (flipOp d) kb ka f4 (by rw [W_nb]; exact (bin_flip hd _ _).symm) (by omega)
    have e : (childTwo (st.1.map W) (W p.2.1) (W p.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb (flipOp d) p.1 p.2.1) kb ka).toFinset := by
      unfold childTwo kidW
      rw [W_nb,bin_flip hd]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff] <;> tauto
    rw [e]
    exact r

lemma levelStep {R T E Z k D' D} (hB : baseOK T R E = true) (hZ : ∀ s ∈ Z, SliceN R T s)
    (hI : LevelN R T k D') (h : levelOK T Z k (D'.map Prod.fst) D = true) : LevelN R T (k+1) D := by
  intro st hst
  refine stStep hB hZ ?_ (List.all_eq_true.mp h st hst)
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hI q hq
lemma chunks {T : Nat} {Z : List SliceD} {k : Nat} {next : List (List Nat)} (c : Nat) (D : List StD) (n : Nat) (hc : 0 < c)
    (hl : Nat.ble D.length (n*c) = true)
    (h : ∀ i, i < n → levelOK T Z k next ((D.drop (i*c)).take c) = true) : levelOK T Z k next D = true := by
  rw [levelOK,List.all_eq_true]
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
  have hl' := Nat.le_of_ble_eq_true hl
  have hi : j / c < n := by
    rw [Nat.div_lt_iff_lt_mul hc]
    omega
  refine List.all_eq_true.mp (h _ hi) _ ?_
  have hm : j / c * c + j % c = j := by rw [Nat.mul_comm]; exact Nat.div_add_mod j c
  have hmod := Nat.mod_lt j hc
  refine List.mem_of_getElem? (i := j % c) ?_
  rw [List.getElem?_take_of_lt hmod,List.getElem?_drop,hm]
  exact List.getElem?_eq_getElem hj
lemma lowSearch {R T E K D} (hB : baseOK T R E = true) (hI : LevelN R T K D)
    (h : (D.map Prod.fst).contains (R.map xN) = true) : LowN R T (K+1) := by
  apply lowOf hB
  simp only [List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨q,hq,e⟩ := List.mem_map.mp h
  have := hI q hq
  rw [e] at this
  simpa only [rootsW,List.map_map,Function.comp_def] using this


def target (x : Fin 7 → Bool) : Bool := decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).length / 2, (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧ (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 2, 5, 3, 5, 0, 6, 1, 6, 3, 6, 4, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)
abbrev c0 : Nat := 0xcccccccccccccccc
abbrev c1 : Nat := 0xaaaaaaaaaaaaaaaa
abbrev c2 : Nat := 0xf0f0f0f0f0f0f0f0
abbrev c3 : Nat := 0xff00ff00ff00ff00
abbrev c4 : Nat := 0xffffffff00000000
abbrev c5 : Nat := 0xffff0000ffff0000
abbrev c6 : Nat := 0xfafafafafafafafa
abbrev c7 : Nat := 0xffffff00ffffff00
abbrev c8 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
abbrev c9 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00
abbrev c10 : Nat := 0xffff0000ffff0000ffff0000ffff0000
abbrev c11 : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
abbrev c12 : Nat := 0xcccccccccccccccccccccccccccccccc
abbrev c13 : Nat := 0xffffffff00000000ffffffff00000000
abbrev c14 : Nat := 0xffaaffaaffaaffaa
abbrev c15 : Nat := 0xffffffffffffffff0000000000000000
abbrev c16 : Nat := 0xfff0fff0fff0fff0
abbrev c17 : Nat := 0xffffaaaaffffaaaa
abbrev c18 : Nat := 0xffccffccffccffcc
abbrev c19 : Nat := 0xfcfcfcfcfcfcfcfc
abbrev c20 : Nat := 0xfffff0f0fffff0f0
abbrev c21 : Nat := 0xeeeeeeeeeeeeeeee
abbrev c22 : Nat := 0xeeeeeeee
abbrev c23 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
abbrev c24 : Nat := 0x33333333333333333333333333333333
abbrev c25 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
abbrev c26 : Nat := 0xfffffffff0f0f0f0
abbrev c27 : Nat := 0xfa00fa00fa00fa
abbrev c28 : Nat := 0x55555555555555555555555555555555
abbrev c29 : Nat := 0xfffafffafffafffa
abbrev c30 : Nat := 0xfff00000fff0
abbrev c31 : Nat := 0xffff0000ffff0000ffff0000ffff
abbrev c32 : Nat := 0x5555000055550000555500005555
abbrev c33 : Nat := 0xfffffafafffffafa
abbrev c34 : Nat := 0xfafa0000fafa
abbrev c35 : Nat := 0x3030303030303030303030303030303
abbrev c36 : Nat := 0x550055005500550055005500550055
abbrev c37 : Nat := 0xffeeffeeffeeffee
abbrev c38 : Nat := 0x3333333330303030
abbrev c39 : Nat := 0xfffcfffcfffcfffc
abbrev c40 : Nat := 0xcccc0000cccc0000cccc0000cccc
abbrev c41 : Nat := 0x30003000300030003000300030003
abbrev c42 : Nat := 0xcccc0000cccc0000cccc0000cccc0000
abbrev c43 : Nat := 0xffffffff00000000ffffffff
abbrev c44 : Nat := 0x3333000033330000333300003333
abbrev c45 : Nat := 0xffffffffaaaaaaaa
abbrev c46 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
abbrev c47 : Nat := 0x30303030303030303030303030303030
abbrev c48 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
abbrev c49 : Nat := 0x3232323232323232
abbrev c50 : Nat := 0xff000000ff000000
abbrev c51 : Nat := 0xfffa0000fffa
abbrev c52 : Nat := 0xff00fa00ff00fa
abbrev c53 : Nat := 0xf0f00000f0f00000f0f00000f0f0
abbrev c54 : Nat := 0xcc000000cc000000cc000000cc
abbrev c55 : Nat := 0xf0f00000f0f00000f0f00000f0f00000
abbrev c56 : Nat := 0xfc00fc00fc00fc
abbrev c57 : Nat := 0xf0f0f0f00000000
abbrev c58 : Nat := 0xf000f000f000f000f000f000f000f
abbrev c59 : Nat := 0x555555550000000055555555
abbrev c60 : Nat := 0x330033003300330033003300330033
abbrev c61 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc00
abbrev c62 : Nat := 0xfefefefefefefefe
abbrev c63 : Nat := 0xf0a0f0a0f0a0f0a
abbrev c64 : Nat := 0xff000000ff00
abbrev c65 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa
abbrev c66 : Nat := 0xffaaaaaaffaaaaaa
abbrev c67 : Nat := 0xfff0f0f0fff0f0f0
abbrev c68 : Nat := 0xffaaffaaffaaffaaffaaffaaffaaffaa
abbrev c69 : Nat := 0x88888888888888888888888888888888
abbrev c70 : Nat := 0xf0c0f0c0f0c0f0c
abbrev c71 : Nat := 0x5555000055550000
abbrev c72 : Nat := 0xffffccccffffcccc
abbrev c73 : Nat := 0xffffffffcccccccc
abbrev c74 : Nat := 0xf000f000f000f000f000f000f000f0
abbrev c75 : Nat := 0x5555550055555500
abbrev c76 : Nat := 0xffffffaaffffffaa
abbrev c77 : Nat := 0xff00aa00ff00aa
abbrev c78 : Nat := 0xfffffff0fffffff0
abbrev c79 : Nat := 0xff00f000ff00f0
abbrev c80 : Nat := 0xff000000ff0000
abbrev c81 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
abbrev c82 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa00
abbrev c83 : Nat := 0x33003300330033003300330033003300
abbrev c84 : Nat := 0x33333333000000003333333300000000
abbrev c85 : Nat := 0x55555555000000005555555500000000
abbrev c86 : Nat := 0x111111110000000011111111
abbrev c87 : Nat := 0x11111111000000001111111100000000
abbrev c88 : Nat := 0xff000000ff000000ff000000ff0000
abbrev c89 : Nat := 0xf0000000f0000000f0000000f0000
abbrev c90 : Nat := 0xf0000000f0000000f0000000f
abbrev c91 : Nat := 0xf0f00000f0f00000f0f00000f0f
abbrev c92 : Nat := 0xff00ff0000000000ff00ff
abbrev c93 : Nat := 0x4040404040404040404040404040404
abbrev c94 : Nat := 0xc000c000c000c000c000c000c000c00
abbrev c95 : Nat := 0xaa000000aa000000aa000000aa
abbrev c96 : Nat := 0x1100110000000000110011
abbrev c97 : Nat := 0x5000500050005000500050005000500
abbrev c98 : Nat := 0x5050000050500000505000005050000
abbrev c99 : Nat := 0xf0f0f0f000000000f0f0f0f000000000
abbrev c100 : Nat := 0xff00ff0000000000ff00ff0000000000
abbrev c101 : Nat := 0x202000002020000020200000202
abbrev c102 : Nat := 0x5000500000000000500050
abbrev c103 : Nat := 0x44000000440000004400000044
abbrev c104 : Nat := 0xff000000ff000000ff000000ff00
abbrev c105 : Nat := 0xcccccccc00000000cccccccc
abbrev c106 : Nat := 0xf000f00000000000f000f000000000
abbrev c107 : Nat := 0xf000f00000000000f000f0000000000
abbrev c108 : Nat := 0xf0f0000000000000f0f000000000
abbrev c109 : Nat := 0xcc000000cc000000cc000000cc00
abbrev c110 : Nat := 0x1111000011110000111100001111
abbrev c111 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
abbrev c112 : Nat := 0x50005000500050005000500050005
abbrev c113 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa
abbrev c114 : Nat := 0x55000000550000005500000055
abbrev c115 : Nat := 0x333333330000000033333333
abbrev c116 : Nat := 0xfcfcfcfcfcfcfcfcfcfcfcfcfcfcfcfc
abbrev c117 : Nat := 0xfff0fff0fff0fff0fff0fff0fff0fff0
abbrev c118 : Nat := 0x50505050505050505050505050505050
abbrev c119 : Nat := 0xffccffccffccffccffccffccffccffcc
abbrev l0 : List Nat := [0, 1, 2, 3, 4]
abbrev l1 : List Nat := [0,1,1000,2,1001]
abbrev l2 : List Nat := [0,1,1000,1001,1002]
abbrev l3 : List Nat := [c1,c0,c2,c3,c5]
abbrev l4 : List Nat := [0,1,1000,2,3,1001,1002]
abbrev l5 : List Nat := [c1,c0,c2,c3]
abbrev l6 : List Nat := [c1,c0,c2,c3,c5,c4]
abbrev l7 : List Nat := [c1,c0,c2,c19,c3,c5]
abbrev l8 : List Nat := [c1,c0,c2,c3,c5,c4,0xffffffffff00ff00]
abbrev l9 : List Nat := [c1,c0,c2,c3,c5,c4,0xffffffffffff0000]
abbrev l10 : List Nat := [0x5544554455445544,c1,c0,c2,c3,c5,c4]
def d0 : Nat := c69
def d1 : List Nat := [0, 1]
def d2 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3)]
lemma d3 : baseOK d0 d1 d2 = true := by decide +kernel
lemma d4 : LowN d1 d0 1 := lowCount d3 (by decide +kernel)
def d5 : Nat := c46
def d6 : List Nat := [0, 1]
def d7 : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2)]
lemma d8 : baseOK d5 d6 d7 = true := by decide +kernel
lemma d9 : LowN d6 d5 1 := lowCount d8 (by decide +kernel)
def d10 : Nat := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
def d11 : List Nat := [0, 1, 2]
def d12 : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6)]
lemma d13 : baseOK d10 d11 d12 = true := by decide +kernel
lemma d14 : LowN d11 d10 2 := lowCount d13 (by decide +kernel)
def d15 : Nat := 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8
def d16 : List Nat := [0, 1, 2]
def d17 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
lemma d18 : baseOK d15 d16 d17 = true := by decide +kernel
lemma d19 : LowN d16 d15 2 := lowCount d18 (by decide +kernel)
def d20 : Nat := 0xeac8eac8eac8eac8eac8eac8eac8eac8
def d21 : List Nat := [0, 1, 2, 3]
def d22 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9)]
lemma d23 : baseOK d20 d21 d22 = true := by decide +kernel
lemma d24 : SliceN d21 d20 (c35,1,[0, 3]) := mkSlice (w:=0) d23 d3 d4 (by decide +kernel)
lemma d25 : SliceN d21 d20 (c81,1,[1, 3]) := mkSlice (w:=1) d23 d8 d9 (by decide +kernel)
lemma d26 : SliceN d21 d20 (c36,1,[1, 2]) := mkSlice (w:=0) d23 d3 d4 (by decide +kernel)
lemma d27 : SliceN d21 d20 (c8,2,[1, 0, 3]) := mkSlice (w:=4) d23 d13 d14 (by decide +kernel)
lemma d28 : SliceN d21 d20 (c23,2,[1, 0, 2]) := mkSlice (w:=0) d23 d18 d19 (by decide +kernel)
lemma d29 : SliceN d21 d20 (c9,2,[0, 1, 2]) := mkSlice (w:=8) d23 d13 d14 (by decide +kernel)
def d30 : List SliceD := [(c35,1,[0, 3]),(c81,1,[1, 3]),(c36,1,[1, 2]),(c8,2,[1, 0, 3]),(c23,2,[1, 0, 2]),(c9,2,[0, 1, 2])]
lemma d31 : ∀ s ∈ d30, SliceN d21 d20 s := by
  unfold d30
  simp only [List.forall_mem_cons]
  exact ⟨d24,d25,d26,d27,d28,d29,by simp⟩
def d32 : List StD := dupD [
 (l5,[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])],[],[[0,1,2],[0,3],[4,1,5],[1,3],[0,5,2],[0,3]])]
def d33 : List StD := []
lemma d34 : LevelN d21 d20 2 d33 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d35 : levelOK d20 d30 2 (d33.map Prod.fst) ((d32.drop (0*8)).take 8) = true := by decide +kernel
lemma d36 : LevelN d21 d20 3 d32 := levelStep d23 d31 d34 (chunks 8 d32 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d35
  ))
lemma d37 : LowN d21 d20 4 := lowSearch d23 d36 (by decide +kernel)
def d38 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def d39 : List Nat := [0, 1, 2]
def d40 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
lemma d41 : baseOK d38 d39 d40 = true := by decide +kernel
lemma d42 : SliceN d39 d38 (c24,1,[0, 2]) := mkSlice (w:=0) d41 d3 d4 (by decide +kernel)
lemma d43 : SliceN d39 d38 (c28,1,[1, 2]) := mkSlice (w:=0) d41 d3 d4 (by decide +kernel)
lemma d44 : SliceN d39 d38 (c12,1,[0, 2]) := mkSlice (w:=2) d41 d8 d9 (by decide +kernel)
lemma d45 : SliceN d39 d38 (c11,1,[1, 2]) := mkSlice (w:=1) d41 d8 d9 (by decide +kernel)
lemma d46 : SliceN d39 d38 (c25,1,[0, 1]) := mkSlice (w:=0) d41 d3 d4 (by decide +kernel)
lemma d47 : SliceN d39 d38 (c8,1,[0, 1]) := mkSlice (w:=4) d41 d8 d9 (by decide +kernel)
def d48 : List SliceD := [(c24,1,[0, 2]),(c28,1,[1, 2]),(c12,1,[0, 2]),(c11,1,[1, 2]),(c25,1,[0, 1]),(c8,1,[0, 1])]
lemma d49 : ∀ s ∈ d48, SliceN d39 d38 s := by
  unfold d48
  simp only [List.forall_mem_cons]
  exact ⟨d42,d43,d44,d45,d46,d47,by simp⟩
def d50 : List StD := dupD [
 ([c1,c0,c2],[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])],[(4,5),(1,3),(0,3),(2,3),(2,6),(1,5)],[l4,[4,1,1003,5,3,1000],[4,0,1001,5,2,1004,1005]])]
def d51 : List StD := []
lemma d52 : LevelN d39 d38 2 d51 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d53 : levelOK d38 d48 2 (d51.map Prod.fst) ((d50.drop (0*8)).take 8) = true := by decide +kernel
lemma d54 : LevelN d39 d38 3 d50 := levelStep d41 d49 d52 (chunks 8 d50 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d53
  ))
lemma d55 : LowN d39 d38 4 := lowSearch d41 d54 (by decide +kernel)
def d56 : Nat := 0xeae8eae8eae8eae8eae8eae8eae8eae8
def d57 : List Nat := [0, 1, 2, 3]
def d58 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
lemma d59 : baseOK d56 d57 d58 = true := by decide +kernel
lemma d60 : SliceN d57 d56 (c23,4,[0, 1, 2]) := mkSlice (w:=0) d59 d41 d55 (by decide +kernel)
def d61 : List SliceD := [(c23,4,[0, 1, 2])]
lemma d62 : ∀ s ∈ d61, SliceN d57 d56 s := by
  unfold d61
  simp only [List.forall_mem_cons]
  exact ⟨d60,by simp⟩
def d63 : List StD := dupD [
 (l5,[(0,[])],[],[[0],[0],[0],[0],[0],[0]])]
def d64 : List StD := []
lemma d65 : LevelN d57 d56 3 d64 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d66 : levelOK d56 d61 3 (d64.map Prod.fst) ((d63.drop (0*8)).take 8) = true := by decide +kernel
lemma d67 : LevelN d57 d56 4 d63 := levelStep d59 d62 d65 (chunks 8 d63 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d66
  ))
lemma d68 : LowN d57 d56 5 := lowSearch d59 d67 (by decide +kernel)
def d69 : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8
def d70 : List Nat := [0, 1, 2, 3]
def d71 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
lemma d72 : baseOK d69 d70 d71 = true := by decide +kernel
lemma d73 : SliceN d70 d69 (c25,4,[0, 1, 3]) := mkSlice (w:=0) d72 d41 d55 (by decide +kernel)
def d74 : List SliceD := [(c25,4,[0, 1, 3])]
lemma d75 : ∀ s ∈ d74, SliceN d70 d69 s := by
  unfold d74
  simp only [List.forall_mem_cons]
  exact ⟨d73,by simp⟩
def d76 : List StD := dupD [
 (l5,[(0,[])],[],[[0],[0],[0],[0],[0],[0]])]
def d77 : List StD := []
lemma d78 : LevelN d70 d69 3 d77 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d79 : levelOK d69 d74 3 (d77.map Prod.fst) ((d76.drop (0*8)).take 8) = true := by decide +kernel
lemma d80 : LevelN d70 d69 4 d76 := levelStep d72 d75 d78 (chunks 8 d76 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d79
  ))
lemma d81 : LowN d70 d69 5 := lowSearch d72 d80 (by decide +kernel)
def d82 : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeea
def d83 : List Nat := [0, 1, 2, 3]
def d84 : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10)]
lemma d85 : baseOK d82 d83 d84 = true := by decide +kernel
lemma d86 : SliceN d83 d82 (c28,4,[1, 2, 3]) := mkSlice (w:=0) d85 d41 d55 (by decide +kernel)
def d87 : List SliceD := [(c28,4,[1, 2, 3])]
lemma d88 : ∀ s ∈ d87, SliceN d83 d82 s := by
  unfold d87
  simp only [List.forall_mem_cons]
  exact ⟨d86,by simp⟩
def d89 : List StD := dupD [
 (l5,[(0,[])],[],[[0],[0],[0],[0],[0],[0]])]
def d90 : List StD := []
lemma d91 : LevelN d83 d82 3 d90 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d92 : levelOK d82 d87 3 (d90.map Prod.fst) ((d89.drop (0*8)).take 8) = true := by decide +kernel
lemma d93 : LevelN d83 d82 4 d89 := levelStep d85 d88 d91 (chunks 8 d89 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d92
  ))
lemma d94 : LowN d83 d82 5 := lowSearch d85 d93 (by decide +kernel)
def d95 : Nat := 0xfefefefefefefefefefefefefefefefe
def d96 : List Nat := [0, 1, 2]
def d97 : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4)]
lemma d98 : baseOK d95 d96 d97 = true := by decide +kernel
lemma d99 : LowN d96 d95 2 := lowCount d98 (by decide +kernel)
def d100 : Nat := 0xfeeefeeefeeefeeefeeefeeefeeefeee
def d101 : List Nat := [0, 1, 2, 3]
def d102 : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,8,12),(3,4,12)]
lemma d103 : baseOK d100 d101 d102 = true := by decide +kernel
lemma d104 : LowN d101 d100 3 := lowCount d103 (by decide +kernel)
def d105 : Nat := 0xfeeafce8feeafce8feeafce8feeafce8
def d106 : List Nat := l0
def d107 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,2,10),(4,1,17)]
lemma d108 : baseOK d105 d106 d107 = true := by decide +kernel
lemma d109 : SliceN d106 d105 (c24,4,[0, 2, 3, 4]) := mkSlice (w:=0) d108 d23 d37 (by decide +kernel)
lemma d110 : SliceN d106 d105 (c32,4,[1, 2, 3]) := mkSlice (w:=0) d108 d41 d55 (by decide +kernel)
lemma d111 : SliceN d106 d105 (c25,4,[0, 1, 3, 4]) := mkSlice (w:=0) d108 d23 d37 (by decide +kernel)
lemma d112 : SliceN d106 d105 (c23,5,[0, 1, 2, 4]) := mkSlice (w:=0) d108 d59 d68 (by decide +kernel)
lemma d113 : SliceN d106 d105 (c31,5,[1, 2, 0, 3]) := mkSlice (w:=0) d108 d72 d81 (by decide +kernel)
lemma d114 : SliceN d106 d105 (c10,5,[0, 1, 2, 3]) := mkSlice (w:=16) d108 d85 d94 (by decide +kernel)
lemma d115 : SliceN d106 d105 (c40,2,[0, 2, 3]) := mkSlice (w:=2) d108 d98 d99 (by decide +kernel)
lemma d116 : SliceN d106 d105 (c53,2,[0, 1, 3]) := mkSlice (w:=4) d108 d98 d99 (by decide +kernel)
lemma d117 : SliceN d106 d105 (c41,1,[0, 4]) := mkSlice (w:=0) d108 d3 d4 (by decide +kernel)
lemma d118 : SliceN d106 d105 (0x3000300030003000300030003000300,1,[0, 4]) := mkSlice (w:=8) d108 d3 d4 (by decide +kernel)
lemma d119 : SliceN d106 d105 (c54,1,[0, 2]) := mkSlice (w:=2) d108 d8 d9 (by decide +kernel)
lemma d120 : SliceN d106 d105 (c9,3,[1, 2, 0, 4]) := mkSlice (w:=8) d108 d103 d104 (by decide +kernel)
lemma d121 : SliceN d106 d105 (c82,2,[1, 2, 4]) := mkSlice (w:=9) d108 d98 d99 (by decide +kernel)
lemma d122 : SliceN d106 d105 (c42,2,[0, 2, 3]) := mkSlice (w:=18) d108 d98 d99 (by decide +kernel)
lemma d123 : SliceN d106 d105 (c55,2,[0, 1, 3]) := mkSlice (w:=20) d108 d98 d99 (by decide +kernel)
def d124 : List SliceD := [(c24,4,[0, 2, 3, 4]),(c32,4,[1, 2, 3]),(c25,4,[0, 1, 3, 4]),(c23,5,[0, 1, 2, 4]),(c31,5,[1, 2, 0, 3]),(c10,5,[0, 1, 2, 3]),(c40,2,[0, 2, 3]),(c53,2,[0, 1, 3]),(c41,1,[0, 4]),(0x3000300030003000300030003000300,1,[0, 4]),(c54,1,[0, 2]),(c9,3,[1, 2, 0, 4]),(c82,2,[1, 2, 4]),(c42,2,[0, 2, 3]),(c55,2,[0, 1, 3])]
lemma d125 : ∀ s ∈ d124, SliceN d106 d105 s := by
  unfold d124
  simp only [List.forall_mem_cons]
  exact ⟨d109,d110,d111,d112,d113,d114,d115,d116,d117,d118,d119,d120,d121,d122,d123,by simp⟩
def d126 : List StD := dupD [
 (l3,[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])],[(2,3),(0,3),(4,5),(17,24),(1,3),(4,6),(2,6),(2,10),(0,10),(4,12)],[[0,1,1000,1001],[1,1002,2,1000],[1,3,1003],[1,4,5],[0,2,1004,1005,1006],[0,3,1007,1008],[0,1,5],[2,3,1009,1007],[1,5],[1,3,5]])]
def d127 : List StD := dupD [
 (l7,[(0,[]),(6,[]),(2,[]),(7,[]),(1,[]),(8,[]),(9,[]),(5,[(1,1,2)]),(3,[])],[],[[0,1],[2,3],[4,1,5],[5,6],[1,7],[0,1],[2],[0,1],[0,7,3],[0],[2,3],[1,7],[8,1],[4,7],[1,6,5]])]
def d128 : List StD := dupD [
 ([c56,c1,c0,c2,c5],[(1,[]),(10,[]),(11,[]),(3,[(1,1,2)]),(5,[]),(0,[(2,1,2)]),(2,[(2,1,2)]),(7,[]),(12,[]),(13,[]),(14,[])],[],[[0,1,2],[2,3],[2,1],[0,4],[5,1],[6,7],[1,8,9],[5,1],[5,10,7],[1,9]])]
def d129 : List StD := []
lemma d130 : LevelN d106 d105 3 d129 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d131 : levelOK d105 d124 3 (d129.map Prod.fst) ((d128.drop (0*8)).take 8) = true := by decide +kernel
lemma d132 : LevelN d106 d105 4 d128 := levelStep d108 d125 d130 (chunks 8 d128 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d131
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d133 : levelOK d105 d124 4 (d128.map Prod.fst) ((d127.drop (0*8)).take 8) = true := by decide +kernel
lemma d134 : LevelN d106 d105 5 d127 := levelStep d108 d125 d132 (chunks 8 d127 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d133
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d135 : levelOK d105 d124 5 (d127.map Prod.fst) ((d126.drop (0*8)).take 8) = true := by decide +kernel
lemma d136 : LevelN d106 d105 6 d126 := levelStep d108 d125 d134 (chunks 8 d126 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d135
  ))
lemma d137 : LowN d106 d105 7 := lowSearch d108 d136 (by decide +kernel)
def d138 : Nat := 0xfeeefac8feeefac8feeefac8feeefac8
def d139 : List Nat := l0
def d140 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9),(4,1,17)]
lemma d141 : baseOK d138 d139 d140 = true := by decide +kernel
lemma d142 : SliceN d139 d138 (c25,5,[0, 1, 4, 3]) := mkSlice (w:=0) d141 d59 d68 (by decide +kernel)
def d143 : List SliceD := [(c25,5,[0, 1, 4, 3])]
lemma d144 : ∀ s ∈ d143, SliceN d139 d138 s := by
  unfold d143
  simp only [List.forall_mem_cons]
  exact ⟨d142,by simp⟩
def d145 : List StD := dupD [
 (l3,[(0,[])],[],[[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]])]
def d146 : List StD := []
lemma d147 : LevelN d139 d138 4 d146 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d148 : levelOK d138 d143 4 (d146.map Prod.fst) ((d145.drop (0*8)).take 8) = true := by decide +kernel
lemma d149 : LevelN d139 d138 5 d145 := levelStep d141 d144 d147 (chunks 8 d145 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d148
  ))
lemma d150 : LowN d139 d138 6 := lowSearch d141 d149 (by decide +kernel)
def d151 : Nat := 0xfeeefae8feeefae8feeefae8feeefae8
def d152 : List Nat := l0
def d153 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
lemma d154 : baseOK d151 d152 d153 = true := by decide +kernel
lemma d155 : SliceN d152 d151 (c24,5,[0, 2, 3, 4]) := mkSlice (w:=0) d154 d59 d68 (by decide +kernel)
lemma d156 : SliceN d152 d151 (c28,4,[1, 2, 3, 4]) := mkSlice (w:=0) d154 d23 d37 (by decide +kernel)
lemma d157 : SliceN d152 d151 (c25,5,[0, 1, 4, 3]) := mkSlice (w:=0) d154 d59 d68 (by decide +kernel)
lemma d158 : SliceN d152 d151 (c23,5,[0, 1, 2, 4]) := mkSlice (w:=0) d154 d72 d81 (by decide +kernel)
lemma d159 : SliceN d152 d151 (c31,5,[0, 2, 1, 3]) := mkSlice (w:=0) d154 d72 d81 (by decide +kernel)
def d160 : List SliceD := [(c24,5,[0, 2, 3, 4]),(c28,4,[1, 2, 3, 4]),(c25,5,[0, 1, 4, 3]),(c23,5,[0, 1, 2, 4]),(c31,5,[0, 2, 1, 3])]
lemma d161 : ∀ s ∈ d160, SliceN d152 d151 s := by
  unfold d160
  simp only [List.forall_mem_cons]
  exact ⟨d155,d156,d157,d158,d159,by simp⟩
def d162 : List StD := dupD [
 (l3,[(0,[]),(1,[]),(2,[]),(3,[]),(4,[])],[(1,3),(0,3),(1,5),(0,5),(1,9),(0,9),(1,17),(0,17),(2,6),(18,24),(2,18),(6,10),(12,24),(10,18)],[[0,1000,1,1001],[1,2,1002,1003],[1,3,1004,1005],[1,4,1006,1007],[0,2,1008],[0,3,1009],[0,4,1010],[2,3,1011],[2,4,1012],[3,4,1013]])]
def d163 : List StD := []
lemma d164 : LevelN d152 d151 5 d163 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d165 : levelOK d151 d160 5 (d163.map Prod.fst) ((d162.drop (0*8)).take 8) = true := by decide +kernel
lemma d166 : LevelN d152 d151 6 d162 := levelStep d154 d161 d164 (chunks 8 d162 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d165
  ))
lemma d167 : LowN d152 d151 7 := lowSearch d154 d166 (by decide +kernel)
def d168 : Nat := 0xfffefeeefffefeeefffefeeefffefeee
def d169 : List Nat := l0
def d170 : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,8,12),(3,4,12),(4,4,20)]
lemma d171 : baseOK d168 d169 d170 = true := by decide +kernel
lemma d172 : SliceN d169 d168 (c28,5,[1, 2, 3, 4]) := mkSlice (w:=0) d171 d85 d94 (by decide +kernel)
def d173 : List SliceD := [(c28,5,[1, 2, 3, 4])]
lemma d174 : ∀ s ∈ d173, SliceN d169 d168 s := by
  unfold d173
  simp only [List.forall_mem_cons]
  exact ⟨d172,by simp⟩
def d175 : List StD := dupD [
 (l3,[(0,[])],[],[[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]])]
def d176 : List StD := []
lemma d177 : LevelN d169 d168 4 d176 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d178 : levelOK d168 d173 4 (d176.map Prod.fst) ((d175.drop (0*8)).take 8) = true := by decide +kernel
lemma d179 : LevelN d169 d168 5 d175 := levelStep d171 d174 d177 (chunks 8 d175 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d178
  ))
lemma d180 : LowN d169 d168 6 := lowSearch d171 d179 (by decide +kernel)
def d181 : Nat := 0xfefefea8fefefea8fefefea8fefefea8
def d182 : List Nat := l0
def d183 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
lemma d184 : baseOK d181 d182 d183 = true := by decide +kernel
lemma d185 : SliceN d182 d181 (c24,5,[0, 2, 3, 4]) := mkSlice (w:=0) d184 d72 d81 (by decide +kernel)
def d186 : List SliceD := [(c24,5,[0, 2, 3, 4])]
lemma d187 : ∀ s ∈ d186, SliceN d182 d181 s := by
  unfold d186
  simp only [List.forall_mem_cons]
  exact ⟨d185,by simp⟩
def d188 : List StD := dupD [
 (l3,[(0,[])],[],[[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]])]
def d189 : List StD := []
lemma d190 : LevelN d182 d181 4 d189 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d191 : levelOK d181 d186 4 (d189.map Prod.fst) ((d188.drop (0*8)).take 8) = true := by decide +kernel
lemma d192 : LevelN d182 d181 5 d188 := levelStep d184 d187 d190 (chunks 8 d188 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d191
  ))
lemma d193 : LowN d182 d181 6 := lowSearch d184 d192 (by decide +kernel)
def d194 : Nat := 0xfffefeeefffafce8fffefeeefffafce8
def d195 : List Nat := [0, 1, 2, 3, 4, 5]
def d196 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,2,10),(4,1,17),(5,1,33)]
lemma d197 : baseOK d194 d195 d196 = true := by decide +kernel
lemma d198 : SliceN d195 d194 (c28,7,[1, 2, 3, 4, 5]) := mkSlice (w:=0) d197 d108 d137 (by decide +kernel)
lemma d199 : SliceN d195 d194 (c24,7,[0, 2, 4, 3, 5]) := mkSlice (w:=0) d197 d108 d137 (by decide +kernel)
lemma d200 : SliceN d195 d194 (c25,6,[0, 1, 3, 4, 5]) := mkSlice (w:=0) d197 d141 d150 (by decide +kernel)
lemma d201 : SliceN d195 d194 (c23,7,[0, 1, 2, 4, 5]) := mkSlice (w:=0) d197 d154 d167 (by decide +kernel)
lemma d202 : SliceN d195 d194 (c31,7,[1, 0, 2, 3, 5]) := mkSlice (w:=0) d197 d154 d167 (by decide +kernel)
lemma d203 : SliceN d195 d194 (c13,6,l0) := mkSlice (w:=32) d197 d171 d180 (by decide +kernel)
lemma d204 : SliceN d195 d194 (c43,6,[2, 1, 4, 3, 0]) := mkSlice (w:=0) d197 d184 d193 (by decide +kernel)
def d205 : List SliceD := [(c28,7,[1, 2, 3, 4, 5]),(c24,7,[0, 2, 4, 3, 5]),(c25,6,[0, 1, 3, 4, 5]),(c23,7,[0, 1, 2, 4, 5]),(c31,7,[1, 0, 2, 3, 5]),(c13,6,l0),(c43,6,[2, 1, 4, 3, 0])]
lemma d206 : ∀ s ∈ d205, SliceN d195 d194 s := by
  unfold d205
  simp only [List.forall_mem_cons]
  exact ⟨d198,d199,d200,d201,d202,d203,d204,by simp⟩
def d207 : List StD := dupD [
 (l6,[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[])],[(1,3),(4,5),(2,3),(33,40),(1,17),(1,33),(4,6),(3,9),(34,48),(2,34),(4,12),(2,10),(4,20),(12,40),(1,5),(9,17),(9,33),(18,34)],[[0,1,1000],[0,1001,2,1002],[0,3,1003],[0,4,1004],[0,5,1005,6],[1,1006,2,1000],[1,3,1007],[1,4,1008],[1,5,1009,6],[2,3,1010,1011],[2,4,1012,1004],[2,6,1005,5,1013,1014],[3,4,1015],[3,5,1016,6,1010],[4,5,1017,6,1004]])]
def d208 : List StD := dupD [
 ([c1,c0,c2,c3,c5,c26],[(0,[(1,1,4)]),(1,[(1,1,4)]),(2,[]),(3,[(1,2,4)]),(4,[(1,2,4)]),(5,[]),(0,[(3,1,4)])],[(1,3),(4,5),(33,40),(1,17),(2,3),(4,6),(3,9),(34,48),(4,12),(4,20),(9,17),(2,10)],[[0,1,1000],[0,2,1001],[0,3,1002],[0,4,1003],[0,5,1004],[1,2,1005],[1,3,1006],[1,4,1007],[1,5,1000],[2,3,1008],[2,4,1009],[2,5,6],[3,4,1010],[3,5,1011],[4,5,1003]]),
 ([c57,c1,c0,c2,c3,c5],[(0,[(3,1,4)]),(6,[]),(1,[(3,1,4)]),(0,[(1,1,4)]),(3,[(3,2,4)]),(4,[(3,2,4)]),(2,[])],[(1,33),(2,34),(9,33),(18,34),(1,3),(1,5),(33,40),(1,17),(2,6),(3,9),(34,48),(5,9),(6,18),(9,17)],[[0,1,1000],[1,2,1001],[1,3],[1,4,1002],[1,5,1003],[0,2,1004],[0,6,1005],[0,4,1006],[0,5,1007],[2,6,1008],[2,4,1009],[2,5,1010],[4,6,1011],[5,6,1012],[4,5,1013]])]
def d209 : List StD := []
lemma d210 : LevelN d195 d194 6 d209 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d211 : levelOK d194 d205 6 (d209.map Prod.fst) ((d208.drop (0*8)).take 8) = true := by decide +kernel
lemma d212 : LevelN d195 d194 7 d208 := levelStep d197 d206 d210 (chunks 8 d208 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d211
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d213 : levelOK d194 d205 7 (d208.map Prod.fst) ((d207.drop (0*8)).take 8) = true := by decide +kernel
lemma d214 : LevelN d195 d194 8 d207 := levelStep d197 d206 d212 (chunks 8 d207 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d213
  ))
lemma d215 : LowN d195 d194 9 := lowSearch d197 d214 (by decide +kernel)
def d216 : Nat := 0xeac0eac0eac0eac0eac0eac0eac0eac0
def d217 : List Nat := [0, 1, 2, 3]
def d218 : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9)]
lemma d219 : baseOK d216 d217 d218 = true := by decide +kernel
lemma d220 : LowN d217 d216 3 := lowCount d219 (by decide +kernel)
def d221 : Nat := 0xfeeafcc8feeafcc8feeafcc8feeafcc8
def d222 : List Nat := l0
def d223 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,2,10),(4,1,17)]
lemma d224 : baseOK d221 d222 d223 = true := by decide +kernel
lemma d225 : SliceN d222 d221 (c32,4,[1, 2, 3]) := mkSlice (w:=0) d224 d41 d55 (by decide +kernel)
lemma d226 : SliceN d222 d221 (c25,4,[0, 1, 3, 4]) := mkSlice (w:=0) d224 d23 d37 (by decide +kernel)
lemma d227 : SliceN d222 d221 (c23,4,[0, 1, 2, 4]) := mkSlice (w:=0) d224 d23 d37 (by decide +kernel)
lemma d228 : SliceN d222 d221 (c31,5,[1, 2, 3, 0]) := mkSlice (w:=0) d224 d59 d68 (by decide +kernel)
lemma d229 : SliceN d222 d221 (c10,5,[0, 1, 2, 3]) := mkSlice (w:=16) d224 d85 d94 (by decide +kernel)
lemma d230 : SliceN d222 d221 (c40,2,[0, 2, 3]) := mkSlice (w:=2) d224 d98 d99 (by decide +kernel)
lemma d231 : SliceN d222 d221 (c47,2,[3, 0, 4]) := mkSlice (w:=4) d224 d13 d14 (by decide +kernel)
lemma d232 : SliceN d222 d221 (c41,1,[0, 4]) := mkSlice (w:=0) d224 d3 d4 (by decide +kernel)
lemma d233 : SliceN d222 d221 (c48,2,[1, 3, 4]) := mkSlice (w:=5) d224 d98 d99 (by decide +kernel)
lemma d234 : SliceN d222 d221 (0xc0c00000c0c00000c0c00000c0c,1,[0, 3]) := mkSlice (w:=2) d224 d8 d9 (by decide +kernel)
lemma d235 : SliceN d222 d221 (c24,3,[0, 2, 3, 4]) := mkSlice (w:=0) d224 d219 d220 (by decide +kernel)
lemma d236 : SliceN d222 d221 (c82,2,[1, 2, 4]) := mkSlice (w:=9) d224 d98 d99 (by decide +kernel)
lemma d237 : SliceN d222 d221 (c9,3,[1, 2, 0, 4]) := mkSlice (w:=8) d224 d103 d104 (by decide +kernel)
lemma d238 : SliceN d222 d221 (c83,2,[2, 0, 4]) := mkSlice (w:=8) d224 d13 d14 (by decide +kernel)
lemma d239 : SliceN d222 d221 (c54,1,[0, 2]) := mkSlice (w:=2) d224 d8 d9 (by decide +kernel)
lemma d240 : SliceN d222 d221 (c58,2,[0, 1, 4]) := mkSlice (w:=0) d224 d18 d19 (by decide +kernel)
lemma d241 : SliceN d222 d221 (c42,2,[0, 2, 3]) := mkSlice (w:=18) d224 d98 d99 (by decide +kernel)
lemma d242 : SliceN d222 d221 (c55,2,[0, 1, 3]) := mkSlice (w:=20) d224 d98 d99 (by decide +kernel)
lemma d243 : SliceN d222 d221 (0x5050000050500000505000005050,1,[1, 3]) := mkSlice (w:=4) d224 d8 d9 (by decide +kernel)
lemma d244 : SliceN d222 d221 (c11,3,[1, 4, 3, 2]) := mkSlice (w:=1) d224 d103 d104 (by decide +kernel)
def d245 : List SliceD := [(c32,4,[1, 2, 3]),(c25,4,[0, 1, 3, 4]),(c23,4,[0, 1, 2, 4]),(c31,5,[1, 2, 3, 0]),(c10,5,[0, 1, 2, 3]),(c40,2,[0, 2, 3]),(c47,2,[3, 0, 4]),(c41,1,[0, 4]),(c48,2,[1, 3, 4]),(0xc0c00000c0c00000c0c00000c0c,1,[0, 3]),(c24,3,[0, 2, 3, 4]),(c82,2,[1, 2, 4]),(c9,3,[1, 2, 0, 4]),(c83,2,[2, 0, 4]),(c54,1,[0, 2]),(c58,2,[0, 1, 4]),(c42,2,[0, 2, 3]),(c55,2,[0, 1, 3]),(0x5050000050500000505000005050,1,[1, 3]),(c11,3,[1, 4, 3, 2])]
lemma d246 : ∀ s ∈ d245, SliceN d222 d221 s := by
  unfold d245
  simp only [List.forall_mem_cons]
  exact ⟨d225,d226,d227,d228,d229,d230,d231,d232,d233,d234,d235,d236,d237,d238,d239,d240,d241,d242,d243,d244,by simp⟩
def d247 : List StD := dupD [
 (l3,[(0,[]),(1,[]),(2,[]),(3,[]),(4,[])],[(2,3),(16,17),(20,21),(24,25),(8,12),(4,6),(2,6),(4,12),(8,10),(2,10)],[[0,1000,1001],[0,1002,1,1000],[0,1003,2,1000],[0,3,4],[1,1004,1005,1006],[2,1007,1008,1009],[0,4],[1,2,1006,1004,1007],[0,4],[0,4]])]
def d248 : List StD := dupD [
 (l7,[(0,[(1,0,1)]),(5,[]),(6,[]),(1,[]),(7,[]),(8,[]),(4,[(1,1,2)]),(3,[(2,0,1)]),(2,[])],[],[[0,1,2],[0,2,3],[0,1,4],[0,5],[1,5,6],[3,5],[3],[2,1],[0,6],[7],[3,2],[0,2,3],[8,1],[0,2,4],[0,6]]),
 ([0xc0c0c0c0c0c0c0c,c1,c0,c2,c3,c5],[(0,[]),(9,[]),(10,[]),(3,[(0,0,1)]),(3,[(1,0,1)]),(4,[]),(6,[]),(0,[(2,0,1)]),(8,[]),(4,[(2,1,2)]),(1,[])],[],[[0,1,2],[3],[4],[2,1],[0,5],[2,1],[1,6],[7,8],[1,8,9],[2,8,10],[2,1],[2,9,7],[1,6],[7,6,9],[1,9]]),
 ([c1,c0,c2,c3,c18,c5],[(0,[(1,0,2)]),(5,[]),(7,[]),(11,[]),(12,[]),(4,[(1,1,3)]),(13,[]),(2,[]),(1,[]),(3,[(2,0,2)])],[],[[0,1,2],[0,3],[0,4,2],[0,1,2],[1,3,5],[6,1],[7,3],[7],[0,5],[7,3],[8,1],[0,5],[9],[0,3,2],[0,3,2]]),
 ([0xcc00cc00cc00cc,c1,c0,c2,c3,c5],[(0,[]),(14,[]),(6,[]),(3,[(0,0,2)]),(1,[]),(10,[]),(3,[(1,0,2)]),(4,[]),(0,[(2,0,2)]),(7,[]),(12,[]),(4,[(2,1,3)]),(2,[])],[],[[0,1,2],[3],[4,1,5],[6],[0,7],[2,1],[8,2,9],[1,10],[1,11],[5,1],[2,10,12],[2,11,8],[1,2,10],[1,2,9],[8,10,9]]),
 ([c1,c0,c2,c3,c16,c5],[(0,[(1,1,2)]),(8,[]),(6,[]),(1,[]),(7,[]),(3,[(1,1,2)]),(4,[(1,2,3)]),(12,[]),(2,[]),(15,[])],[],[[0,1],[0,2,3],[0,1],[0,2,4],[5,1,6],[3,1],[2,7,8],[9,1],[0,6],[3,1],[8],[0,1,3],[3],[0,6],[0,1,4]])]
def d249 : List StD := dupD [
 ([c56,c1,c0,c2,c5],[(0,[]),(8,[]),(3,[(2,0,2)]),(1,[]),(3,[(0,0,2)]),(4,[]),(7,[]),(5,[]),(6,[]),(16,[]),(1,[(2,1,2)]),(17,[]),(18,[])],[],[[0,1],[2,3,4],[3,1],[0,5],[6,1,7],[6,8],[7,1,9],[10,1],[6,11,12],[6,1]]),
 ([c70,c1,c0,c3,c5],[(7,[]),(19,[]),(0,[]),(3,[(2,0,1)]),(5,[]),(3,[(0,0,1)]),(3,[(3,1,2)]),(12,[]),(3,[(0,1,2)]),(4,[]),(8,[]),(17,[]),(6,[]),(18,[])],[],[[0,1,2],[3,4,5],[6,7,8],[0,9,2],[0,4],[0,7],[4,10,11],[12,4],[0,11,13],[0,7]])]
def d250 : List StD := []
lemma d251 : LevelN d222 d221 3 d250 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d252 : levelOK d221 d245 3 (d250.map Prod.fst) ((d249.drop (0*8)).take 8) = true := by decide +kernel
lemma d253 : LevelN d222 d221 4 d249 := levelStep d224 d246 d251 (chunks 8 d249 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d252
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d254 : levelOK d221 d245 4 (d249.map Prod.fst) ((d248.drop (0*8)).take 8) = true := by decide +kernel
lemma d255 : LevelN d222 d221 5 d248 := levelStep d224 d246 d253 (chunks 8 d248 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d254
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d256 : levelOK d221 d245 5 (d248.map Prod.fst) ((d247.drop (0*8)).take 8) = true := by decide +kernel
lemma d257 : LevelN d222 d221 6 d247 := levelStep d224 d246 d255 (chunks 8 d247 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d256
  ))
lemma d258 : LowN d222 d221 7 := lowSearch d224 d257 (by decide +kernel)
def d259 : Nat := 0xfffefffefffefffefffefffefffefffe
def d260 : List Nat := [0, 1, 2, 3]
def d261 : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4),(3,0,8)]
lemma d262 : baseOK d259 d260 d261 = true := by decide +kernel
lemma d263 : LowN d260 d259 3 := lowCount d262 (by decide +kernel)
def d264 : Nat := 0xfffefeeefff8fae8fffefeeefff8fae8
def d265 : List Nat := [0, 1, 2, 3, 4, 5]
def d266 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,4,20),(5,1,33)]
lemma d267 : baseOK d264 d265 d266 = true := by decide +kernel
lemma d268 : SliceN d265 d264 (c28,7,[1, 2, 3, 4, 5]) := mkSlice (w:=0) d267 d224 d258 (by decide +kernel)
lemma d269 : SliceN d265 d264 (c24,7,[0, 2, 3, 4, 5]) := mkSlice (w:=0) d267 d108 d137 (by decide +kernel)
lemma d270 : SliceN d265 d264 (c25,7,[3, 0, 1, 5, 4]) := mkSlice (w:=0) d267 d224 d258 (by decide +kernel)
lemma d271 : SliceN d265 d264 (c23,7,[2, 1, 0, 5, 4]) := mkSlice (w:=0) d267 d108 d137 (by decide +kernel)
lemma d272 : SliceN d265 d264 (c31,7,[0, 1, 2, 3, 5]) := mkSlice (w:=0) d267 d154 d167 (by decide +kernel)
lemma d273 : SliceN d265 d264 (c43,7,[2, 0, 3, 4, 1]) := mkSlice (w:=0) d267 d154 d167 (by decide +kernel)
lemma d274 : SliceN d265 d264 (c84,5,[0, 2, 3, 4]) := mkSlice (w:=32) d267 d85 d94 (by decide +kernel)
lemma d275 : SliceN d265 d264 (c85,5,[1, 2, 3, 4]) := mkSlice (w:=32) d267 d85 d94 (by decide +kernel)
lemma d276 : SliceN d265 d264 (c86,4,[2, 3, 4]) := mkSlice (w:=0) d267 d41 d55 (by decide +kernel)
lemma d277 : SliceN d265 d264 (c10,6,[2, 3, 0, 1, 5]) := mkSlice (w:=16) d267 d171 d180 (by decide +kernel)
lemma d278 : SliceN d265 d264 (c87,4,[2, 3, 4]) := mkSlice (w:=32) d267 d41 d55 (by decide +kernel)
lemma d279 : SliceN d265 d264 (0xf0f00000f0f00000f0f00000f0f0000,5,[3, 1, 0, 5]) := mkSlice (w:=16) d267 d85 d94 (by decide +kernel)
lemma d280 : SliceN d265 d264 (c88,5,[2, 1, 0, 5]) := mkSlice (w:=16) d267 d85 d94 (by decide +kernel)
lemma d281 : SliceN d265 d264 (c36,4,[1, 2, 4, 5]) := mkSlice (w:=0) d267 d23 d37 (by decide +kernel)
lemma d282 : SliceN d265 d264 (c89,4,[0, 1, 5]) := mkSlice (w:=16) d267 d41 d55 (by decide +kernel)
lemma d283 : SliceN d265 d264 (c90,4,[0, 1, 5]) := mkSlice (w:=0) d267 d41 d55 (by decide +kernel)
lemma d284 : SliceN d265 d264 (c59,5,[2, 3, 4, 1]) := mkSlice (w:=0) d267 d59 d68 (by decide +kernel)
lemma d285 : SliceN d265 d264 (0xff00000000000000ff,4,[0, 1, 2]) := mkSlice (w:=0) d267 d41 d55 (by decide +kernel)
lemma d286 : SliceN d265 d264 (c35,4,[0, 3, 4, 5]) := mkSlice (w:=0) d267 d23 d37 (by decide +kernel)
lemma d287 : SliceN d265 d264 (c60,4,[0, 2, 4, 5]) := mkSlice (w:=0) d267 d23 d37 (by decide +kernel)
lemma d288 : SliceN d265 d264 (c44,5,[0, 2, 3, 5]) := mkSlice (w:=0) d267 d59 d68 (by decide +kernel)
lemma d289 : SliceN d265 d264 (0x33330000000000003333,4,[0, 2, 3]) := mkSlice (w:=0) d267 d41 d55 (by decide +kernel)
lemma d290 : SliceN d265 d264 (c91,5,[0, 1, 5, 3]) := mkSlice (w:=0) d267 d59 d68 (by decide +kernel)
lemma d291 : SliceN d265 d264 (c92,5,[2, 1, 0, 4]) := mkSlice (w:=0) d267 d59 d68 (by decide +kernel)
lemma d292 : SliceN d265 d264 (0xaaaa0000aaaa0000aaaa0000aaaa0000,3,[1, 2, 3, 5]) := mkSlice (w:=17) d267 d262 d263 (by decide +kernel)
lemma d293 : SliceN d265 d264 (c93,2,[5, 4, 3]) := mkSlice (w:=2) d267 d13 d14 (by decide +kernel)
lemma d294 : SliceN d265 d264 (c61,3,[0, 2, 4, 5]) := mkSlice (w:=10) d267 d262 d263 (by decide +kernel)
lemma d295 : SliceN d265 d264 (0x303030300000000030303030,2,[0, 3, 4]) := mkSlice (w:=4) d267 d98 d99 (by decide +kernel)
lemma d296 : SliceN d265 d264 (c94,2,[0, 4, 5]) := mkSlice (w:=10) d267 d98 d99 (by decide +kernel)
lemma d297 : SliceN d265 d264 (c42,3,[0, 2, 3, 5]) := mkSlice (w:=18) d267 d262 d263 (by decide +kernel)
lemma d298 : SliceN d265 d264 (c95,2,[1, 2, 5]) := mkSlice (w:=1) d267 d98 d99 (by decide +kernel)
lemma d299 : SliceN d265 d264 (0x10101010000000001010101,1,[3, 4]) := mkSlice (w:=0) d267 d3 d4 (by decide +kernel)
lemma d300 : SliceN d265 d264 (0xf000f00000000000f000f0,2,[0, 1, 4]) := mkSlice (w:=4) d267 d98 d99 (by decide +kernel)
lemma d301 : SliceN d265 d264 (c96,1,[2, 4]) := mkSlice (w:=0) d267 d3 d4 (by decide +kernel)
lemma d302 : SliceN d265 d264 (0xa0000000a0000000a0000000a,1,[1, 5]) := mkSlice (w:=1) d267 d8 d9 (by decide +kernel)
lemma d303 : SliceN d265 d264 (0x101010100000000010101010,1,[3, 4]) := mkSlice (w:=4) d267 d8 d9 (by decide +kernel)
lemma d304 : SliceN d265 d264 (c97,2,[4, 1, 5]) := mkSlice (w:=8) d267 d13 d14 (by decide +kernel)
lemma d305 : SliceN d265 d264 (0x44004400440044004400440044004400,2,[2, 4, 5]) := mkSlice (w:=10) d267 d98 d99 (by decide +kernel)
lemma d306 : SliceN d265 d264 (0xf0f0000000000000f0f0,2,[0, 1, 3]) := mkSlice (w:=4) d267 d98 d99 (by decide +kernel)
lemma d307 : SliceN d265 d264 (0x2222000022220000222200002222,2,[2, 3, 5]) := mkSlice (w:=1) d267 d98 d99 (by decide +kernel)
lemma d308 : SliceN d265 d264 (0x30300000000000003030,1,[0, 3]) := mkSlice (w:=4) d267 d8 d9 (by decide +kernel)
lemma d309 : SliceN d265 d264 (c98,2,[3, 1, 5]) := mkSlice (w:=16) d267 d13 d14 (by decide +kernel)
lemma d310 : SliceN d265 d264 (c54,2,[0, 2, 5]) := mkSlice (w:=2) d267 d98 d99 (by decide +kernel)
lemma d311 : SliceN d265 d264 (0x3000300000000000300030,1,[0, 4]) := mkSlice (w:=4) d267 d8 d9 (by decide +kernel)
lemma d312 : SliceN d265 d264 (0x22000000220000002200000022,1,[2, 5]) := mkSlice (w:=1) d267 d8 d9 (by decide +kernel)
lemma d313 : SliceN d265 d264 (c99,3,[0, 1, 3, 4]) := mkSlice (w:=36) d267 d262 d263 (by decide +kernel)
lemma d314 : SliceN d265 d264 (0x5000000050000000500000005,1,[1, 5]) := mkSlice (w:=0) d267 d3 d4 (by decide +kernel)
lemma d315 : SliceN d265 d264 (0xaaaa000000000000aaaa,2,[1, 2, 3]) := mkSlice (w:=1) d267 d98 d99 (by decide +kernel)
lemma d316 : SliceN d265 d264 (0xaa00000000000000aa,1,[1, 2]) := mkSlice (w:=1) d267 d8 d9 (by decide +kernel)
lemma d317 : SliceN d265 d264 (c100,3,[0, 1, 2, 4]) := mkSlice (w:=40) d267 d262 d263 (by decide +kernel)
lemma d318 : SliceN d265 d264 (0x30003000000000003000300,1,[0, 4]) := mkSlice (w:=8) d267 d8 d9 (by decide +kernel)
lemma d319 : SliceN d265 d264 (c101,1,[3, 5]) := mkSlice (w:=1) d267 d8 d9 (by decide +kernel)
lemma d320 : SliceN d265 d264 (c102,1,[1, 4]) := mkSlice (w:=4) d267 d8 d9 (by decide +kernel)
lemma d321 : SliceN d265 d264 (c103,1,[2, 5]) := mkSlice (w:=2) d267 d8 d9 (by decide +kernel)
lemma d322 : SliceN d265 d264 (c104,3,[0, 2, 1, 5]) := mkSlice (w:=8) d267 d103 d104 (by decide +kernel)
lemma d323 : SliceN d265 d264 (c32,4,[1, 2, 3, 5]) := mkSlice (w:=0) d267 d23 d37 (by decide +kernel)
lemma d324 : SliceN d265 d264 (0x444400000000000044440000,1,[2, 3]) := mkSlice (w:=18) d267 d8 d9 (by decide +kernel)
lemma d325 : SliceN d265 d264 (0x3000000030000000300000003,1,[0, 5]) := mkSlice (w:=0) d267 d3 d4 (by decide +kernel)
lemma d326 : SliceN d265 d264 (c105,3,[0, 2, 3, 4]) := mkSlice (w:=2) d267 d103 d104 (by decide +kernel)
lemma d327 : SliceN d265 d264 (0xf0f0f0f000000000f0f0f0f,4,[0, 3, 4, 1]) := mkSlice (w:=0) d267 d23 d37 (by decide +kernel)
lemma d328 : SliceN d265 d264 (c106,2,[0, 1, 4]) := mkSlice (w:=36) d267 d98 d99 (by decide +kernel)
lemma d329 : SliceN d265 d264 (0xc0c00000c0c00000c0c00000c0c0000,2,[0, 3, 5]) := mkSlice (w:=18) d267 d98 d99 (by decide +kernel)
lemma d330 : SliceN d265 d264 (0xf0f0f0f000000000f0f0f0f00000000,3,[0, 1, 3, 4]) := mkSlice (w:=32) d267 d103 d104 (by decide +kernel)
lemma d331 : SliceN d265 d264 (c107,2,[0, 1, 4]) := mkSlice (w:=40) d267 d98 d99 (by decide +kernel)
lemma d332 : SliceN d265 d264 (0xa0a00000a0a00000a0a00000a0a0000,2,[1, 3, 5]) := mkSlice (w:=17) d267 d98 d99 (by decide +kernel)
lemma d333 : SliceN d265 d264 (0xcc00cc0000000000cc00cc00,2,[0, 2, 4]) := mkSlice (w:=10) d267 d98 d99 (by decide +kernel)
lemma d334 : SliceN d265 d264 (0xc0000000c0000000c0000000c,1,[0, 5]) := mkSlice (w:=2) d267 d8 d9 (by decide +kernel)
lemma d335 : SliceN d265 d264 (0xc0000000c0000000c0000000c0000,1,[0, 5]) := mkSlice (w:=18) d267 d8 d9 (by decide +kernel)
lemma d336 : SliceN d265 d264 (c108,2,[0, 1, 3]) := mkSlice (w:=36) d267 d98 d99 (by decide +kernel)
lemma d337 : SliceN d265 d264 (c109,2,[0, 2, 5]) := mkSlice (w:=10) d267 d98 d99 (by decide +kernel)
lemma d338 : SliceN d265 d264 (0xff00000000000000ff0000000000,2,[0, 1, 2]) := mkSlice (w:=40) d267 d98 d99 (by decide +kernel)
lemma d339 : SliceN d265 d264 (0x22220000222200002222000022220000,2,[2, 3, 5]) := mkSlice (w:=17) d267 d98 d99 (by decide +kernel)
lemma d340 : SliceN d265 d264 (0x110011000000000011001100,1,[2, 4]) := mkSlice (w:=8) d267 d8 d9 (by decide +kernel)
lemma d341 : SliceN d265 d264 (0x11001100000000001100110000000000,1,[2, 4]) := mkSlice (w:=40) d267 d8 d9 (by decide +kernel)
lemma d342 : SliceN d265 d264 (0xaaaa000000000000aaaa0000,2,[1, 2, 3]) := mkSlice (w:=17) d267 d98 d99 (by decide +kernel)
lemma d343 : SliceN d265 d264 (0x50505050000000005050505000000000,2,[1, 3, 4]) := mkSlice (w:=36) d267 d98 d99 (by decide +kernel)
def d344 : List SliceD := [(c28,7,[1, 2, 3, 4, 5]),(c24,7,[0, 2, 3, 4, 5]),(c25,7,[3, 0, 1, 5, 4]),(c23,7,[2, 1, 0, 5, 4]),(c31,7,[0, 1, 2, 3, 5]),(c43,7,[2, 0, 3, 4, 1]),(c84,5,[0, 2, 3, 4]),(c85,5,[1, 2, 3, 4]),(c86,4,[2, 3, 4]),(c10,6,[2, 3, 0, 1, 5]),(c87,4,[2, 3, 4]),(0xf0f00000f0f00000f0f00000f0f0000,5,[3, 1, 0, 5]),(c88,5,[2, 1, 0, 5]),(c36,4,[1, 2, 4, 5]),(c89,4,[0, 1, 5]),(c90,4,[0, 1, 5]),(c59,5,[2, 3, 4, 1]),(0xff00000000000000ff,4,[0, 1, 2]),(c35,4,[0, 3, 4, 5]),(c60,4,[0, 2, 4, 5]),(c44,5,[0, 2, 3, 5]),(0x33330000000000003333,4,[0, 2, 3]),(c91,5,[0, 1, 5, 3]),(c92,5,[2, 1, 0, 4]),(0xaaaa0000aaaa0000aaaa0000aaaa0000,3,[1, 2, 3, 5]),(c93,2,[5, 4, 3]),(c61,3,[0, 2, 4, 5]),(0x303030300000000030303030,2,[0, 3, 4]),(c94,2,[0, 4, 5]),(c42,3,[0, 2, 3, 5]),(c95,2,[1, 2, 5]),(0x10101010000000001010101,1,[3, 4]),(0xf000f00000000000f000f0,2,[0, 1, 4]),(c96,1,[2, 4]),(0xa0000000a0000000a0000000a,1,[1, 5]),(0x101010100000000010101010,1,[3, 4]),(c97,2,[4, 1, 5]),(0x44004400440044004400440044004400,2,[2, 4, 5]),(0xf0f0000000000000f0f0,2,[0, 1, 3]),(0x2222000022220000222200002222,2,[2, 3, 5]),(0x30300000000000003030,1,[0, 3]),(c98,2,[3, 1, 5]),(c54,2,[0, 2, 5]),(0x3000300000000000300030,1,[0, 4]),(0x22000000220000002200000022,1,[2, 5]),(c99,3,[0, 1, 3, 4]),(0x5000000050000000500000005,1,[1, 5]),(0xaaaa000000000000aaaa,2,[1, 2, 3]),(0xaa00000000000000aa,1,[1, 2]),(c100,3,[0, 1, 2, 4]),(0x30003000000000003000300,1,[0, 4]),(c101,1,[3, 5]),(c102,1,[1, 4]),(c103,1,[2, 5]),(c104,3,[0, 2, 1, 5]),(c32,4,[1, 2, 3, 5]),(0x444400000000000044440000,1,[2, 3]),(0x3000000030000000300000003,1,[0, 5]),(c105,3,[0, 2, 3, 4]),(0xf0f0f0f000000000f0f0f0f,4,[0, 3, 4, 1]),(c106,2,[0, 1, 4]),(0xc0c00000c0c00000c0c00000c0c0000,2,[0, 3, 5]),(0xf0f0f0f000000000f0f0f0f00000000,3,[0, 1, 3, 4]),(c107,2,[0, 1, 4]),(0xa0a00000a0a00000a0a00000a0a0000,2,[1, 3, 5]),(0xcc00cc0000000000cc00cc00,2,[0, 2, 4]),(0xc0000000c0000000c0000000c,1,[0, 5]),(0xc0000000c0000000c0000000c0000,1,[0, 5]),(c108,2,[0, 1, 3]),(c109,2,[0, 2, 5]),(0xff00000000000000ff0000000000,2,[0, 1, 2]),(0x22220000222200002222000022220000,2,[2, 3, 5]),(0x110011000000000011001100,1,[2, 4]),(0x11001100000000001100110000000000,1,[2, 4]),(0xaaaa000000000000aaaa0000,2,[1, 2, 3]),(0x50505050000000005050505000000000,2,[1, 3, 4])]
lemma d345 : ∀ s ∈ d344, SliceN d265 d264 s := by
  unfold d344
  simp only [List.forall_mem_cons]
  exact ⟨d268,d269,d270,d271,d272,d273,d274,d275,d276,d277,d278,d279,d280,d281,d282,d283,d284,d285,d286,d287,d288,d289,d290,d291,d292,d293,d294,d295,d296,d297,d298,d299,d300,d301,d302,d303,d304,d305,d306,d307,d308,d309,d310,d311,d312,d313,d314,d315,d316,d317,d318,d319,d320,d321,d322,d323,d324,d325,d326,d327,d328,d329,d330,d331,d332,d333,d334,d335,d336,d337,d338,d339,d340,d341,d342,d343,by simp⟩
def d346 : List StD := dupD [
 (l6,[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])],[(4,5),(2,3),(1,3),(1,5),(8,9),(1,9),(18,19),(32,33),(1,33),(4,6),(2,6),(40,42),(18,26),(17,19),(10,26),(2,34),(8,12),(4,12),(16,20),(4,20),(40,44),(36,44),(10,42),(36,52),(17,49)],[l2,[0,2,1001,1000,1003],[0,3,1000,1004,1005],[0,4,1000,1006],[0,5,1000,1007,1008],[1,2,1002,1009,1010],[1,3,1002,1011,1012],[1,4,1002,1013,1014],[1,5,1002,1011,1015],[2,3,1003,1016,1017],[2,4,1003,1018,1019],[2,5,1003,1020],[3,4,1005,1012,1014],[3,5,1005,1021,1022],[4,5,1008,1023,1024]])]
def d347 : List StD := dupD [
 ([c1,c0,c21,c2,c3,c5,c4],[(0,[]),(1,[]),(2,[(1,1,2)]),(3,[(1,1,2)]),(4,[(1,0,1)]),(6,[]),(5,[(1,1,4)]),(7,[]),(8,[]),(9,[]),(5,[]),(10,[])],[(1,5),(10,11),(2,3),(18,19),(1,33),(2,6),(18,26),(17,19),(1,3),(2,34),(10,26),(8,12),(4,12),(16,20),(4,20)],[[0,1],[0,1],[0,1000,2],[0,1001,3,1002],[0,1003,4,1001],[0,5,1004,6],[0],[1,1005,2],[1,1006,3],[1,1007,4,1008],[1,7,1009,6],[2,8,1000],[3,8,1006],[4,8,9,1010],[6,8,10,1004],[2,3,1000,1011,1012],[2,4,1000,1013,1014],[2,6,8,11],[3,4,1012,1006,1010],[3,6,8,11],[4,6,8,11]]),
 ([c1,c0,c2,c6,c3,c5,c4],[(0,[]),(1,[(1,0,1)]),(2,[]),(3,[(1,0,2)]),(11,[]),(4,[(1,0,2)]),(5,[(1,0,1)]),(7,[])],[(1,3),(1,9),(4,5),(36,37),(4,6),(32,34),(40,42),(18,26),(10,26),(1,19),(2,34),(4,12),(17,21),(1,5),(4,20),(1,33),(10,42),(17,33)],[[0,1000,1],[0,2],[0,2],[0,1001,3],[0,4,5,1002],[0,1003,6,1002],[1,2,1004],[1,1005,1000],[1,3,1000,1006,1007],[1,5,1000,4,1008,1009],[1,6,1000,7,1010,1005],[0],[2,1011,3],[2,1012,5,1013],[2,7,6,1012],[3,1007,1001],[5,1008,4,1014],[6,1010,7,1015],[3,5,1001,4,1008,1007],[3,6,1001,7,1016,1010],[5,6,1008,4,7,1017,1010]]),
 ([c1,c0,c2,c3,c14,c5,c4],[(0,[]),(1,[(1,0,2)]),(2,[(1,0,1)]),(3,[]),(12,[]),(4,[(1,0,3)]),(5,[(1,1,2)]),(13,[]),(1,[]),(7,[]),(2,[]),(4,[]),(5,[])],[(10,11),(1,3),(1,5),(40,41),(4,6),(2,6),(40,42),(10,26),(1,19),(2,34),(8,12),(4,20),(12,40),(17,25),(10,42),(17,33)],[[0,1000,1,1001],[0,1002,2],[0,3],[0,3],[0,4,5,1000],[0,1003,6,1000],[1,2,1001,1004,1005],[1,3,1006],[1,7,8,1001,1004],[1,5,1001,4,1007,1008],[1,6,1001,9,1009,1006],[2,3,1010],[2,7,10,1002,1005],[2,5,1002,4,1011,1007],[2,6,1002,9,1012,1009],[0],[3,1013,5,1007],[3,9,1014,6],[5,7,11,4,1007,1011],[6,7,12,9,1014,1009],[5,6,1007,4,9,1015,1009]]),
 ([c1,c0,c2,c3,c5,c17,c4],[(0,[]),(1,[(1,0,3)]),(11,[]),(12,[]),(4,[]),(5,[(1,1,3)]),(1,[]),(7,[]),(2,[]),(3,[]),(5,[])],[(18,19),(1,3),(1,5),(1,9),(48,49),(2,6),(18,26),(4,6),(2,34),(1,33),(6,10),(12,40),(4,12),(10,34)],[[0,1000,1,1001],[0,2,1002],[0,3,1003],[0,2,4],[0,2,4],[0,1004,5,1000],[1,2,1005,1002],[1,3,1006,1003],[1,2,4],[1,2,6,1007],[1,5,1001,7,1008,1009],[2,3,1010],[2,4,3],[2,8,3,1005],[2,7,1011,5,1002],[2,3,4],[2,3,9,1012],[3,7,1013,5,1003],[0],[2,4],[2,5,10,7,1008]]),
 ([c1,c0,c2,c3,c17,c4],[(0,[]),(1,[(1,0,3)]),(2,[(1,1,4)]),(3,[(1,2,4)]),(4,[]),(5,[(1,1,3)]),(12,[]),(1,[]),(7,[]),(14,[]),(2,[]),(11,[]),(3,[])],[(3,18),(1,3),(1,5),(1,9),(33,48),(4,6),(2,6),(40,42),(18,26),(10,26),(2,34),(8,12),(4,12),(4,20),(12,40),(10,42),(1,33)],[[0,1000,1,1001],[0,1002,2],[0,1003,3],[0,4],[0,1004,5,1000],[1,2,1001,1005,1006],[1,3,1001,1007,1008],[1,1005,6,1009,7],[1,5,1001,8,1010,1007],[2,3,1002,9,1011,1012],[2,1006,6,1013,10,9],[2,5,1002,8,1014,1010],[3,1012,6,11,1009,12],[3,5,1003,8,1015,1010],[5,1010,6,8,1016]]),
 ([c71,c1,c0,c2,c3,c4],[(0,[]),(4,[]),(1,[]),(2,[]),(3,[]),(7,[]),(5,[]),(1,[(3,0,3)]),(2,[(3,1,4)]),(3,[(3,2,4)]),(5,[(3,1,3)]),(15,[])],[(3,18),(10,26),(4,20),(18,34),(2,3),(0,3),(4,5),(8,9),(32,33),(1,3),(4,6),(2,6),(40,42),(18,26),(2,34),(8,12),(4,12),(12,40),(10,42)],[[0,1,1000],[1,1001,2],[1,1002,3],[1,1001,4],[1,5,1003,6],[0,1004,7,1005],[0,1006,8,1004],[0,1007,9,1004],[0,1008,10,1004],[7,8,1009,1010,1011],[7,9,1009,1012,1013],[7,10,1009,5,1014,1012],[8,9,1011,11,1015,1016],[8,10,1011,5,1017,1014],[9,10,1013,5,1018,1014]]),
 ([c1,c0,c2,c3,c5,c4,c45],[(0,[]),(6,[]),(2,[(1,1,3)]),(3,[(1,2,3)]),(4,[(1,0,4)]),(5,[]),(7,[]),(1,[]),(16,[]),(17,[])],[(1,3),(36,37),(1,5),(40,41),(48,49),(4,6),(40,42),(17,19),(8,12),(4,12),(16,20),(4,20),(16,24),(8,24)],[[0,1,1000],[0,1001,2,1002],[0,1003,3,1001],[0,1004,4,1001],[0,1,5],[0,1,5],[1,1005,2,1000],[1,1006,3,1000],[1,1007,4,1000],[1,5,6],[1,7,6,8],[2,3,1002,1008,1009],[2,4,1002,1010,1011],[1,2,5],[1,2,8],[3,4,1009,9,1012,1013],[1,3,5],[1,3,8],[1,4,5],[1,4,8],[0]]),
 ([c1,c0,c2,c19,c3,c5,c4],[(0,[(1,0,1)]),(1,[]),(2,[]),(18,[]),(0,[]),(3,[(1,0,1)]),(4,[(1,1,2)]),(11,[]),(5,[(1,0,4)]),(6,[]),(3,[]),(4,[]),(5,[])],[(2,3),(4,5),(8,9),(1,9),(3,18),(2,19),(1,33),(0,33),(18,26),(10,26),(36,38),(4,6),(10,14),(2,6),(18,22),(8,24),(2,34),(10,42),(17,33)],[[0,1,1000],[0,2,1001],[0,3,4,1000,1002],[0,5,1000,1002,1003],[0,6,1000,7,1004,1005],[0,8,1000,9,1006,1007],[1,2],[1,2],[1,1008,5],[1,7,1009,6],[1,1010,8,1011],[1],[2,1012,5,1013],[2,1014,6,1012],[2,9,8,1012],[3,5,10,1008,1003],[3,6,11,7,1009,1015],[3,8,12,9,1016,1006],[5,6,1003,7,1009,1008],[5,8,1003,9,1017,1006],[6,8,1006,7,9,1018,1009]]),
 ([c1,c0,c2,c3,c18,c5,c4],[(0,[(1,0,2)]),(1,[]),(2,[(1,0,2)]),(3,[]),(19,[]),(0,[]),(4,[(1,1,3)]),(12,[]),(5,[(1,2,4)]),(6,[]),(2,[]),(4,[]),(5,[])],[(2,3),(4,5),(1,5),(8,9),(3,18),(2,19),(1,33),(0,33),(2,6),(10,24),(8,26),(40,42),(2,34),(6,10),(8,12),(4,20),(0,20),(12,40),(18,26),(8,24),(10,34),(17,33)],[[0,1,1000],[0,2,1000,1001,1002],[0,3,1003],[0,4,5,1000,1001],[0,6,1000,7,1004,1005],[0,8,1000,9,1006,1007],[1,1008,2],[1,3],[1,3],[1,7,1009,6,1010],[1,1011,8,1012],[2,3,1013,1014],[2,4,10,1008,1002],[2,6,1002,7,1015,1016],[2,8,1002,9,1017,1006],[1],[3,1018,6,1019],[3,9,1020,8,1018],[4,6,11,7,1019,1015],[4,8,12,9,1012,1006],[6,8,1006,7,9,1021,1015]]),
 ([c1,c0,c2,c3,c5,c72,c4],[(0,[(1,0,3)]),(1,[]),(2,[(1,2,4)]),(11,[]),(3,[(1,1,4)]),(12,[]),(4,[]),(0,[]),(20,[]),(5,[(1,3,4)]),(21,[])],[(17,19),(2,3),(1,5),(0,5),(1,9),(0,9),(1,33),(0,33),(2,6),(18,24),(2,34),(6,10),(12,40),(10,34)],[[0,1,1000,1001],[0,2,3,1002,1003],[0,4,5,1004,1005],[0,3,6],[0,3,7,8],[0,9,10,1006,1007],[1,3,1008],[1,5,1009],[1,3,6],[1,3,6],[1,10,1010],[2,3,5,1011],[2,3,6,5],[2,3,8,5],[2,3,10,1012],[3,4,6],[3,4,8],[4,5,10,1013],[1],[3,6],[3,8]]),
 ([c1,c0,c2,c3,c5,c4,c73],[(0,[(1,0,4)]),(1,[]),(7,[]),(2,[(1,2,3)]),(3,[(1,1,3)]),(21,[]),(6,[]),(5,[]),(4,[]),(8,[])],[(2,3),(4,5),(8,9),(3,18),(36,38),(2,6),(40,42),(10,26),(8,12),(4,12),(4,20)],[[0,1,2,1000],[0,2,1001,3,1000],[0,2,1002,4,1000],[0,2,5,1003],[0,2,5,6],[0,2,5,6],[1,1004,3,1005],[1,1006,4,1004],[1,5,1007],[1,2,7],[1,2,7],[3,4,1005,1008,1009],[3,5,1010,1007],[2,3,5],[2,3,5],[4,5,1007,1010],[2,4,5],[2,4,5],[2,5,7],[2,5,8,9],[1]]),
 ([c1,c0,c2,c3,c16,c5,c4],[(0,[(1,1,2)]),(1,[(1,1,2)]),(2,[]),(3,[]),(15,[]),(14,[]),(5,[(1,0,2)]),(4,[]),(6,[])],[(4,5),(2,3),(1,3),(8,9),(32,33),(1,33),(10,14),(4,6),(40,42),(2,34),(4,20),(40,44),(8,24),(36,44),(4,12),(10,42)],[l2,[0,2,1000],[0,3,1003],[0,4,1000],[0,4,5],[0,6,1000,1004,1005],[1,2,1006,1007],[1,3,1008],[1,4,1007],[1,4,5],[1,6,1002,1008,1009],[2,3],[2,3],[2,4,1010],[2,1011,6,1006],[2],[3,4,1012],[3,1013,6,1014],[4,7,1010],[4,8,1015,6],[4,5]]),
 ([c1,c0,c2,c3,c5,c20,c4],[(0,[(1,1,3)]),(1,[(1,1,3)]),(2,[]),(3,[(1,0,4)]),(12,[]),(4,[]),(0,[]),(15,[]),(5,[(1,0,3)]),(21,[]),(11,[]),(3,[]),(22,[])],[(4,5),(2,3),(1,3),(17,21),(1,9),(0,9),(32,33),(1,33),(18,22),(18,26),(32,34),(2,34),(4,12),(48,52),(36,44)],[l2,[0,2,1003,1000],[0,3,4,1004,1005],[0,4,5],[0,4,6,7],[0,8,1000,1006,1007],[1,2,1008,1003],[1,3,4,1009,1004],[1,4,5],[1,4,7],[1,8,1002,9,1010,1011],[2,4,1012],[2,4,5],[2,4,5],[2,1013,8,1003],[3,4,5,10],[3,4,11,10,12],[3,4,1014,8,1004],[2],[4,5],[4,7]]),
 ([c1,c0,c2,c3,c5,c4,c26],[(0,[(1,1,4)]),(21,[]),(6,[]),(7,[]),(2,[]),(3,[(1,0,3)]),(11,[]),(5,[]),(0,[]),(4,[(1,2,4)]),(1,[]),(3,[]),(4,[])],[(1,3),(4,5),(8,9),(3,18),(4,6),(40,42),(3,17),(40,44),(4,12),(48,52),(8,24),(4,20),(1,9)],[[0,1,2,3,1000],[0,3,4,1001],[0,3,1002,5,1001],[0,1,3,6,1003,1001],[0,1,7,2],[0,2,8,3,1002],[1,2,4,1004],[1,2,1005,5,1000],[1,2,6,1006,9,1000],[1,2,7,3],[1,2,10,3,1000],[4,1007,5,1008],[1,4,1009,1007],[1,4,7],[1],[1,5,1008,6,1010,1011],[1,5,7,2],[2,5,11,1012],[1,2,7],[1,2,12,6,1010],[2,4]]),
 ([c1,c0,c2,c3,c5,c26],[(0,[(1,1,4)]),(1,[(1,1,4)]),(10,[]),(11,[]),(2,[]),(3,[(1,0,3)]),(4,[(1,2,4)]),(6,[]),(0,[]),(7,[]),(1,[]),(5,[]),(3,[])],[(4,5),(2,3),(1,3),(8,9),(1,9),(3,18),(2,19),(1,33),(4,6),(40,42),(18,26),(10,26),(1,19),(2,34),(12,40),(4,12),(20,48),(10,42),(4,20)],[[0,1,1000,2,1001,1002],[0,3,4,1000],[0,5,1000,1003,1004],[0,6,1000,3,1005,1006],[0,1001,2,7,1007,8],[1,3,4,1008],[1,5,1002,1009,1010],[1,6,1002,3,1011,1012],[1,1002,2,9,1013,10],[3,4,1014,5,1015],[3,4,1016,6,1014],[4,11],[5,6,1004,3,1011,1010],[5,1004,2,1017,12],[6,1011,2,3,1018]]),
 ([c57,c1,c0,c2,c3,c5],[(0,[(3,1,4)]),(5,[]),(0,[]),(1,[]),(2,[]),(3,[]),(11,[]),(4,[]),(1,[(3,1,4)]),(8,[]),(3,[(3,0,3)]),(4,[(3,2,4)])],[(1,33),(2,34),(12,40),(10,42),(17,33),(4,5),(2,3),(1,3),(1,5),(8,9),(1,9),(3,18),(2,19),(2,6),(40,42),(18,26),(10,26),(1,19),(8,12),(16,20)],[[0,1,1000,2],[1,1001,3],[1,4,1002],[1,1003,5],[1,6,1004,7],[0,8,1005,9,1006,1007],[0,4,1008,1005],[0,10,1005,1009,1010],[0,11,1005,6,1011,1012],[4,1013,8,1008],[8,10,1007,1014,1015],[8,11,1007,6,1016,1017],[4,1018,10,1008],[4,1019,11,1008],[10,11,1010,6,1016,1015]]),
 ([c1,c0,c2,c3,c5,c7,c4],[(0,[(1,2,3)]),(1,[(1,2,3)]),(2,[(1,0,4)]),(11,[]),(3,[]),(4,[]),(0,[]),(15,[]),(5,[(1,2,3)]),(17,[]),(12,[])],[(4,5),(2,3),(1,3),(1,5),(17,25),(8,9),(1,33),(0,33),(2,6),(18,26),(2,34),(8,12),(12,40),(10,42)],[l2,[0,2,3,1003,1000],[0,4,1004,1005],[0,3,5],[0,3,6,7],[0,8,9,1006,1007],[1,2,3,1008,1003],[1,4,1009,1004],[1,3,5],[1,3,7],[1,8,9,1010,1006],[2,3,4,1011],[2,3,5,10],[2,3,9,10],[2,3,9,1012],[3,4,5],[3,4,5],[4,9,1013],[3,4],[3,5],[3,7]]),
 (l8,[(0,[(1,2,4)]),(1,[(1,2,4)]),(7,[]),(6,[]),(15,[]),(3,[]),(12,[]),(17,[]),(2,[(1,0,3)]),(5,[]),(4,[]),(23,[])],[(1,3),(4,5),(2,3),(8,9),(3,18),(4,6),(34,40),(3,17),(36,44),(8,12),(4,20),(0,20),(8,24)],[[0,1,2,3,1000],[0,2,1001,4,1002],[0,2,5,1003],[0,2,6,1004,4,7],[0,2,7,3],[0,2,7,3],[1,3,1005,4,1000],[1,3,5,1006],[1,3,6,1007,4,7],[1,2,7],[1,2,7],[4,5,1008,8,1009],[4,7,1010,8,1011],[2,4,7],[2,4,7],[4,5,7,1012],[2,4,5,9],[2,5,9],[2,4,9],[2,4,10,6,11],[2,4]]),
 (l9,[(0,[(1,3,4)]),(1,[(1,3,4)]),(7,[]),(6,[]),(11,[]),(12,[]),(4,[]),(5,[]),(0,[]),(17,[]),(3,[]),(21,[])],[(1,3),(1,5),(1,9),(2,6),(18,24),(6,10)],[[0,1,2,3,1000],[0,2,4,1001],[0,2,5,1002],[0,2,4,6],[0,2,7,3],[0,2,8,3,9],[1,3,4,1003],[1,3,5,1004],[1,3,4,6],[1,2,7],[1,2,9],[4,5,1005],[4,6,5],[2,4,7],[2,4,9],[4,5,6],[2,5,7],[2,5,10,11],[2,4,6],[2,4,7],[2,6]])]
def d348 : List StD := dupD [
 ([c0,c21,c2,c6,c3,c5,c4],[(0,[]),(1,[(1,0,1)]),(2,[(1,1,2)]),(3,[(1,1,2),(1,0,2)]),(11,[(1,1,2)]),(4,[(1,0,1),(1,0,2)]),(7,[]),(5,[(1,1,4),(1,0,1)]),(8,[]),(11,[]),(4,[(1,0,2)]),(5,[(1,0,1)]),(24,[]),(10,[]),(25,[]),(3,[(1,1,2)]),(26,[]),(4,[(1,0,1)]),(27,[]),(28,[])],[(2,3),(18,26),(3,17),(1,3),(2,34),(4,37),(4,12),(5,17),(1,5),(3,18),(2,19)],[[0],[1,2],[1,2,1000],[1,1001,3],[1,4,1002,5,1003],[1,6,1004,7],[2,1,8],[1,2],[3,8,1001],[5,8,4,9,10],[7,8,11,1004,1005],[0],[2,1006,3],[2,12,1007,5,1008],[2,6,13,8],[3,14,15,16,12,1006,1001],[5,14,17,4,18,1009,1010],[7,8,12,13],[5,3,1006,4,19,1001],[7,3,8,13],[7,5,8,4,13]]),
 ([c1,c21,c2,c19,c3,c5,c4],[(1,[]),(0,[(1,0,1)]),(2,[(1,1,2)]),(18,[]),(26,[]),(3,[(1,1,2),(1,0,1)]),(11,[(1,1,2)]),(4,[(1,0,1),(1,1,2)]),(10,[]),(11,[]),(4,[(1,1,2)]),(5,[(1,0,4)]),(29,[]),(8,[]),(3,[(1,1,2)]),(4,[(1,0,1)])],[(1,3),(1,9),(3,18),(2,3),(1,33),(4,38),(6,10),(2,6),(6,18),(4,12),(3,17),(1,19),(9,17),(4,20)],[[0],[1,2],[1,2,3,1000],[1,4,1001,5],[1,6,1002,7,1003],[1,8,1004],[2,1,8],[1,2],[5,8,1001],[7,8,6,9,10],[8,11,1004,1005],[0],[2,4,1006,5,1007],[2,12,1008,7,1007],[2,8,13],[5,3,14,12,1009,1001],[7,3,15,6,4,1010,1011],[8,3,13],[7,5,1001,6,4,1012,1013],[8,5,13],[8,7,13]]),
 ([c1,c21,c2,c3,c18,c5,c4],[(8,[]),(3,[(2,1,2)]),(2,[(1,1,2),(1,0,2)]),(3,[(1,1,2)]),(19,[]),(12,[(1,1,2)]),(4,[(1,0,1),(1,1,3)]),(0,[(1,0,2)]),(12,[]),(4,[(1,1,3)]),(5,[(1,2,4)]),(2,[(1,1,2)]),(26,[]),(10,[]),(29,[]),(4,[(1,0,1)])],[(1,5),(3,10),(1,3),(3,18),(2,3),(1,33),(8,42),(6,10),(8,12),(4,20),(0,20),(8,24)],[[0,1],[0,1000,2],[0,3,1001],[0,3,4,1002],[0,5,1003,6,1004],[0,7,1005],[0,1000,2],[0,3,7],[0,3],[0,5,8,6,9],[0,10,1005,1006],[3,1007,2,1008],[4,2,11,12,1008,1000],[6,2,1000,5,1009,1010],[0,13],[0],[3,14,1011,6],[0,3,13],[6,4,15,5,12,1011,1009],[0,12,13],[0,5,13]]),
 ([c1,c0,c2,c62,c3,c5,c4],[(0,[(1,0,1)]),(2,[(1,1,2)]),(10,[]),(1,[(1,0,1)]),(18,[]),(26,[]),(15,[(1,0,1)]),(11,[(1,1,2)]),(0,[(3,0,1)]),(30,[]),(29,[]),(8,[]),(31,[]),(3,[]),(4,[]),(11,[]),(21,[(1,0,1)]),(32,[])],[(1,9),(3,18),(2,3),(1,33),(18,26),(3,17),(1,3),(2,34),(6,10),(1,5),(5,17),(16,24)],[[0,1,2,3],[0,1,3],[4],[0,5,1000,6],[0,7,1001,6,1002],[0,2,1003],[1,0,2],[2,8],[2,1004,6],[2,7,1005,6,1006],[2,3,1007],[2],[1,5,1008,9,1009],[1,10,1010,9,1009],[1,2,11],[6,12,13,10,1000,1011],[6,12,14,7,5,15],[2,11],[16,17,1000,7,5,1004],[2,6,11],[2,6,11]]),
 ([c1,c0,c2,c3,c37,c5,c4],[(0,[(1,0,2)]),(3,[(1,1,2)]),(10,[]),(1,[(1,0,2)]),(15,[(1,0,1)]),(19,[]),(29,[]),(13,[]),(12,[(1,1,2)]),(25,[]),(33,[]),(2,[]),(21,[(1,0,2)]),(8,[]),(4,[]),(12,[])],[(1,5),(3,18),(2,3),(1,33),(2,6),(3,17),(1,3),(2,34),(6,10),(1,9),(16,20),(4,20),(9,17)],[[0,1,2,3],[0,1000,4],[0,1,3],[5],[0,6,1001,4,1002],[0,2,1003],[2,1004,4],[1,0,2],[7],[2,8,1005,4,1006],[2,3,1007],[1,1008,9,1009],[10,4,11,6,1000,1010],[12,9,1000,6,1011,1010],[2,4,13],[2],[1,6,1012,12,1009],[1,2,13],[4,10,14,8,9,15],[2,13],[2,4,13]]),
 ([c22,c1,c0,c2,c3,c5],[(0,[(2,0,4)]),(10,[]),(1,[]),(2,[]),(3,[]),(12,[]),(4,[]),(21,[])],[(1,5),(10,42),(1,3),(4,37),(2,3),(10,11),(18,19),(4,38),(8,42),(17,19),(1,9),(8,12),(4,12),(8,24),(16,20),(4,20),(16,24)],[[0,1,2],[0,1,2],[1,1000,3],[1,1001,4],[1,5,6],[0,1,1002],[0,1003,1004],[0,1005,1003],[0,1006,7,1003],[1,1007,1002],[1,1008,1002],[1,1009,1002],[1000,1010,1011,1012],[7,1013,1014,1015],[7,1015,1016,1013]]),
 ([c1,c0,c21,c2,c3,c16,c5,c4],[(0,[(1,1,2)]),(1,[(1,1,2)]),(2,[(1,1,2)]),(26,[]),(3,[(1,1,2)]),(15,[(1,0,1)]),(14,[(1,0,1)]),(34,[]),(10,[(1,0,1)]),(5,[(1,0,2)]),(35,[]),(8,[(1,0,1)]),(4,[(1,0,1)])],[],[[0,1],[1],[0,2],[0,3,4],[0,3,5],[0,6,5],[0,7],[0],[1,3],[1,4],[1,5],[1,3],[1,3],[2,3,8],[4,8],[5,8],[5,3,6],[9,3],[2,4],[4],[2,10],[2,8,11],[2],[4,3],[4,3],[12,3],[5,3],[5,6]]),
 ([c1,c0,c21,c2,c3,c5,c20,c4],[(0,[(1,1,3)]),(1,[(1,1,3)]),(24,[]),(12,[(1,1,2)]),(4,[(1,0,1)]),(15,[(1,0,1)]),(29,[]),(10,[(1,0,2)]),(21,[]),(35,[]),(2,[(1,1,2)]),(3,[(1,1,2)]),(22,[(1,0,1)])],[],[[0,1],[1],[0,2],[0,2],[0,3,4],[0,3,5],[0,2],[0],[1,6],[1,6],[1,2,4],[1,2,5],[1,6],[5,2,7],[3,2,7],[4,3],[5,3],[8,2],[3,9,10],[4,2],[4],[5,7,8],[4,2],[11,2,12],[3,7,8],[10],[4,2],[5,2]]),
 ([c1,c0,c21,c2,c3,c5,c7,c4],[(0,[(1,2,3)]),(1,[(1,2,3)]),(24,[]),(29,[]),(4,[(1,0,1)]),(15,[(1,0,1)]),(10,[(1,1,2)]),(12,[]),(21,[]),(12,[(1,1,2)]),(26,[]),(2,[(1,1,2)]),(17,[(1,0,1)]),(0,[(2,2,3)])],[],[[0,1],[1],[0,2],[0,2],[0,3,4],[0,3,5],[0,2],[0],[1,3],[1,3],[1,2,4],[1,2,5],[1,3],[5,2,6],[5,2,6],[4,7],[5,7],[8,2],[9,10],[4,2],[11,2,12],[5,6,8],[4,2],[4],[5,6,8],[13],[4,2],[5,2]]),
 ([c0,c2,c6,c3,c14,c5,c4],[(15,[]),(10,[]),(36,[]),(1,[(1,0,2)]),(24,[]),(26,[]),(13,[]),(1,[(1,0,1)]),(14,[]),(17,[(1,0,2)]),(1,[(1,0,1),(1,0,2)]),(7,[]),(28,[]),(2,[(1,0,1)]),(3,[(1,0,2)]),(17,[]),(8,[]),(5,[(1,0,1)])],[(4,6),(8,11),(40,42),(4,5),(5,17),(1,5),(8,9),(1,33),(2,34),(9,17),(1,9),(10,42)],[[0,1000,1],[2,1,3,4,5,1000,1001],[0,1002,1],[6,1,7,2,1002,1000],[0,8],[9,10,1000,11,12,1002],[1],[0,13,14],[0,4,14,6,1003],[0,13,1004,1005],[0,1,9,1005],[0,4,13,1006],[0],[0,8],[9,2,15,1,4,1007,1008],[1],[0,14,1009,1010],[0,1,1011,16],[0,2,8],[9,6,17,1,2,1007,1008],[0,1,8]]),
 ([c0,c2,c6,c3,c17,c4],[(1,[(1,0,1),(1,0,3)]),(2,[(1,1,4)]),(15,[]),(14,[]),(1,[(1,0,1)]),(5,[(1,0,1),(1,1,3)]),(10,[]),(7,[]),(3,[(1,0,2)]),(11,[]),(5,[(1,0,1)])],[(4,6),(32,34),(3,18),(18,26),(1,9),(10,26),(2,34),(4,12),(1,5),(4,5),(1,33),(10,34)],[[0,1,1000],[0,1001,1000,1002],[0,2,3,1003,1004],[0,3,4,1005],[0,5,1000,6,7,1006,1001],[1,6],[1,3,1007],[1,3,1008,1009],[1,6,5,1008],[2,3,1004,1003],[1,2],[5,1006,6,1010],[2,3,8,9,1005],[2,3,6,1011,5,1003],[3,5,10,6,1006]]),
 ([c1,c0,c6,c19,c3,c5,c4],[(0,[(1,0,1)]),(1,[(1,0,1)]),(15,[]),(18,[]),(11,[]),(10,[]),(25,[]),(3,[(1,0,1)]),(26,[]),(35,[]),(4,[(1,1,2)]),(5,[(1,0,4)]),(8,[]),(3,[(1,0,2)]),(4,[(1,0,2)]),(4,[(1,0,2),(1,1,2)]),(3,[(1,0,2),(1,0,1)]),(37,[])],[(1,5),(1,9),(4,5),(1,33),(2,6),(18,26),(10,26),(2,34),(6,18),(1,21)],[[0,1],[2],[0,1,3,1000],[0,1001,2],[0,4,2,1002],[0,5,1003],[1,0,1004],[2],[1,1005,2],[1,4,1006,2],[1,5,1007],[0,1],[2,6,7,8,9,1001,1005],[2,6,10,4,9,1008,1006],[5,6,11,12],[2,3,13,6,1005,1001],[2,3,14,4,6,1006,1009],[5,3,12],[15,16,1001,4,17,1005],[5,2,12],[5,2,12]]),
 ([c1,c0,c2,c6,c62,c3,c5,c4],[(0,[(1,0,1)]),(2,[(1,1,2)]),(1,[(1,0,1)]),(2,[(3,1,2)]),(24,[]),(38,[]),(0,[(3,0,1)]),(25,[]),(0,[(2,0,1)]),(35,[]),(10,[]),(8,[]),(3,[(1,0,2)]),(31,[])],[],[[0,1,2],[0,1],[1],[3],[0,4],[0,5],[0,4],[1,0,2],[2],[6],[2,7],[2,4,5],[2,7],[0],[8],[1,5],[1,4,9],[1,10,11],[2],[7,4],[7,9],[7,4],[12,4,13],[13,7],[11,4,10],[5,4],[5,10],[9,4,10]]),
 ([c49,c1,c0,c2,c6,c3,c5,c4],[(0,[]),(2,[]),(0,[(1,0,1)]),(0,[(0,0,1)]),(3,[(1,0,2)]),(35,[]),(25,[]),(10,[]),(8,[]),(0,[(3,0,1)]),(1,[(1,0,1)]),(2,[(2,1,2)]),(39,[]),(40,[]),(36,[]),(41,[])],[],[[0,1],[2],[1,0],[3],[4,5,6],[6,5],[6,7,8],[9,10],[7,11],[11],[5,12],[5,13],[6,12],[7,9],[7],[5,6],[5,6],[10,6],[7],[6,5],[6,5],[6,7,8],[6,5],[6,5],[6,7,8],[12,14,15],[5,7],[5,7]]),
 ([c49,c1,c0,c2,c3,c5,c4],[(0,[]),(0,[(3,0,1)]),(2,[(2,1,2)]),(0,[(1,0,1)]),(3,[]),(25,[]),(35,[]),(4,[]),(11,[]),(10,[]),(8,[]),(1,[(1,0,1)]),(26,[]),(15,[(2,0,1)]),(11,[(3,1,2)]),(36,[]),(42,[]),(29,[]),(21,[(1,0,1)]),(43,[])],[(1,9),(16,24),(2,3),(3,18),(1,33),(2,6),(18,24),(16,26),(10,24),(8,26),(2,34),(6,10),(5,17)],[[0,1,2],[3],[1,2],[4,5,6,1000,1001],[7,5,8,6],[9,5,10],[1,9,1002,11],[1,2,11],[1,12,1000,13],[1,14,1003,13,1002],[1,9,1004],[2,9,1005],[9,15,1006,13,1007],[9,14,1008,13,1009],[9,11,1010],[2,12,1011,16,1005],[2,17,1012,16,1005],[2,9,10],[18,19,1000,14,12,1001],[6,10,9],[6,10,9]]),
 ([c1,c0,c2,c6,c3,c18,c5,c4],[(0,[(1,0,2)]),(1,[(1,0,1)]),(15,[]),(43,[]),(14,[]),(44,[]),(36,[]),(25,[]),(10,[]),(8,[]),(19,[])],[],[[0,1],[0,2],[2],[0,2],[0,3],[0,4,2],[0,5],[1,2],[1,6],[1,2],[2],[1,4,2],[1,7],[0],[5,7],[2,5],[5,3,6],[2,8,9],[2,7],[10],[2,3,4],[6,5],[1],[3,6],[2,6],[2,4],[5,6],[2,4]]),
 ([c1,c0,c6,c3,c16,c5,c4],[(0,[(1,1,2)]),(1,[(1,0,1),(1,1,2)]),(15,[]),(3,[(1,0,2)]),(14,[]),(45,[]),(5,[(1,0,1),(1,0,2)]),(36,[]),(1,[(1,1,2)]),(26,[]),(37,[]),(5,[(1,0,2)]),(10,[(1,0,1)]),(30,[]),(0,[(2,1,2)]),(4,[(1,0,2)]),(10,[]),(5,[(1,0,1)])],[(1,3),(1,33),(8,14),(40,42),(8,12),(2,34),(8,24),(12,36),(4,12),(1,21)],[[0,1000,1],[2],[0,2],[0,2,3],[0,2,4],[0,5,1001,6],[7,1,8,5,9,1000,1002],[2,1003,1],[2,1003,1],[2,4],[6,1,1000,5,10,1003],[2,0,1004],[0,2],[2,4],[6,7,11,12,13,1001,1005],[2,14],[2,3,1006],[2,5,1007,6,1008],[2,15,1006,1009],[2,12,16,6,17],[2,4]]),
 ([c1,c0,c6,c3,c5,c26],[(0,[(1,1,4)]),(10,[]),(15,[]),(14,[]),(1,[(1,0,1)]),(7,[]),(0,[(3,1,4)]),(4,[(1,0,2),(1,2,4)]),(3,[(1,0,2),(1,0,3)]),(11,[]),(3,[(1,0,2)]),(4,[(1,0,2)])],[(1,3),(1,9),(4,5),(1,5),(32,34),(40,42),(3,17),(16,24),(12,40),(8,24),(4,20),(10,42)],[[0,1,1000],[0,2],[0,1001,2],[0,3,2,1002],[0,1,1002,1003],[1,1000,1004],[1,1005,2,1000],[1,3,1006,2,1000],[1,4,5,1000],[2,1007,1008,1001],[2,1009,3,1010],[0,1,6],[2,7,8,1001,9,1009,1007],[1,2,10,1011],[1,2,11,3,1009]]),
 ([c1,c0,c2,c6,c3,c29,c5,c4],[(0,[(1,1,2)]),(24,[]),(15,[]),(14,[]),(45,[]),(36,[]),(1,[(1,0,1)]),(46,[]),(39,[]),(32,[]),(3,[(1,0,2)]),(2,[(1,0,1)]),(0,[(3,1,2)]),(47,[]),(0,[(2,1,2)])],[],[[0,1],[0,1],[2],[0,1],[2],[0,3,2],[0,1],[2,4],[5,1],[2,5],[6,1,7],[2,1],[8,4,9],[0],[10,0,11],[12],[5,1,4],[2,13],[2],[2],[2,3],[5,1],[14],[8,1],[2,4,5],[2,3],[7,1],[2,1]]),
 ([c1,c0,c2,c3,c29,c5,c4],[(0,[(1,1,2)]),(26,[]),(43,[]),(3,[(1,0,2)]),(15,[]),(2,[(1,0,1)]),(14,[]),(45,[]),(10,[(1,0,1)]),(46,[]),(1,[]),(32,[]),(39,[]),(13,[]),(8,[(1,0,1)]),(0,[(2,1,2)]),(8,[]),(10,[])],[(1,3),(1,33),(4,6),(40,42),(32,34),(5,17),(1,5),(12,40),(9,17),(1,9),(12,36)],[[0,1,1000,2],[0,2,3,4],[0,1,5,2,3],[4],[0,4,6],[0,7,1001,2],[4,1,1002,8],[3,1003,8],[9,8,10,7,1000,1004],[4,1,6],[11,12,1000,7,1,1003],[3,0,4,5],[13],[4,5,1005,1006],[4,8,1007,14,1006],[3,15],[3,4,1008,1009],[3,7,1010,14,1009],[4,1,6],[14,9,16,8,1,17],[2,4,6]]),
 ([c27,c1,c0,c2,c6,c3,c5,c4],[(0,[]),(15,[]),(1,[(1,0,1)]),(32,[]),(36,[]),(0,[(1,1,2)]),(10,[]),(8,[]),(30,[]),(0,[(2,1,2)]),(14,[]),(25,[]),(44,[]),(48,[])],[],[[0,1],[2,3,4],[1,0],[1],[5],[1,3,4],[4,6,7],[4,8],[1,3],[1],[1,9],[1,10],[3,8,4],[1,3],[4,3],[1,4],[1,10],[3,11,12],[9],[8,9],[4,3],[1,13],[1],[1,3,4],[4,8],[3,4],[1,4],[1,10]]),
 ([c27,c1,c0,c2,c3,c5,c4],[(0,[]),(0,[(2,1,2)]),(15,[]),(10,[]),(36,[]),(32,[]),(0,[(1,1,2)]),(14,[]),(8,[]),(30,[]),(26,[]),(43,[]),(3,[(1,0,2)]),(49,[]),(10,[(2,0,1)]),(25,[]),(44,[]),(2,[(3,0,1)]),(8,[(2,0,1)])],[(1,3),(32,34),(8,9),(1,33),(4,6),(18,24),(16,24),(8,12),(5,17),(12,40),(0,24),(10,34)],[[0,1,2],[3,4,5,1000,1001],[1,2],[2,6],[2,5,7],[8,4,3,9],[1,10,1000,11],[1,2,12],[1,2,1002],[1,2,7],[1,13,1003,5],[2,10,1004,14],[2,15,1005,14,1006],[2,7],[5,16,1000,13,10,1001],[2,12,1007],[2,17,1008,1007],[2,13,1009,18,1007],[2,12,1006,1010],[2,14,1011,18,1006],[2,7]]),
 ([c0,c2,c3,c14,c17,c4],[(8,[]),(14,[]),(13,[]),(1,[(1,0,3)]),(1,[(1,0,2)]),(26,[]),(5,[(1,1,2),(1,1,3)]),(1,[(1,0,2),(1,0,3)]),(7,[]),(3,[(1,2,4)]),(2,[(1,0,1)]),(12,[]),(3,[(3,2,4)]),(5,[(1,1,3)]),(5,[(1,1,2)])],[(2,6),(1,5),(40,42),(3,18),(1,3),(2,34),(8,12),(12,40),(1,9),(8,9),(10,42)],[[0,1,1000,1001],[0,1,1002],[0,2,3,1002,1003],[0,1,4,5,1002],[0,6,7,1004,8,1005,1002],[1,9,1006],[1,1001,2,1000],[1,10,11,1000],[0,1,8,1007,1000],[0],[1,9,1008,1009],[0,1,8,1010],[1,2,9,5,12],[0,2,13,8,1010,1005],[0,1,14,8,1005]]),
 ([c1,c0,c2,c19,c3,c14,c5,c4],[(0,[(1,0,1)]),(26,[]),(1,[(1,0,2)]),(14,[]),(50,[]),(15,[]),(51,[]),(52,[]),(3,[(1,0,1)]),(53,[]),(10,[]),(8,[]),(13,[]),(18,[])],[],[[0,1,2],[0,3],[0,1,4],[0,3],[3],[0,3,5],[0,6],[2,1],[3],[2,3],[2,7],[2,1],[2,1],[2],[6,1,8],[3,1,9],[4,7],[3,10,11],[3,6],[12,13],[4,1],[6,1],[0],[6,1,7],[3,1],[5,1,3],[9,1],[4,3,5]]),
 ([c1,c0,c2,c14,c18,c5,c4],[(0,[(1,0,2)]),(1,[(1,0,2)]),(14,[]),(19,[]),(15,[]),(8,[]),(13,[]),(2,[(1,0,2)]),(26,[]),(2,[(1,0,1)]),(4,[(1,0,3),(1,1,3)]),(2,[(1,0,1),(1,0,2)]),(12,[]),(10,[]),(4,[(1,1,3)]),(4,[(1,0,3)])],[(3,10),(1,5),(1,9),(1,33),(2,6),(18,26),(10,24),(8,26),(2,34),(4,20),(0,20),(9,17)],[[0,1,1000],[0,1001,2],[2],[0,1,3,1002],[0,2,4,1000],[0,5,1003],[1,1004,2],[1,0,6,1005],[2],[1,2,1006,4,1007],[1,5,1008],[6,2,7,8,1001,1004],[3,2,9,8,1004,1001],[10,11,1001,12,1009,1010],[5,13],[0,1],[4,6,14,2,8,1005],[5,8,13],[4,3,15,2,8,1011,1009],[5,8,13],[5,2,13]]),
 ([c1,c0,c2,c3,c14,c37,c5,c4],[(0,[(1,0,2)]),(3,[(1,1,2)]),(1,[(1,0,2)]),(30,[]),(3,[(2,1,2)]),(54,[]),(26,[]),(13,[]),(2,[(1,0,1)]),(33,[]),(24,[]),(10,[]),(8,[])],[],[[0,1,2],[0,3],[0,1],[1],[4],[0,5],[0,3],[2,6],[1,0,2],[2,7],[7],[2,6],[2,6],[1,5],[7,3],[8,3,9],[3,10],[9,11],[0],[11],[1,6],[1,5],[2],[7,6],[7,3],[9,6],[12,3,11],[3,10]]),
 ([0x3322332233223322,c1,c0,c2,c3,c5,c4],[(0,[]),(0,[(3,0,2)]),(3,[(3,1,2)]),(0,[(1,0,2)]),(13,[]),(2,[]),(14,[]),(4,[]),(8,[]),(10,[]),(1,[(1,0,2)]),(14,[(2,0,1)]),(15,[(2,0,1)]),(52,[]),(25,[]),(44,[]),(12,[(3,1,2)]),(29,[]),(39,[])],[(1,5),(2,3),(3,18),(1,33),(2,6),(18,26),(10,26),(2,34),(6,10),(5,17)],[[0,1,2],[3,4],[4,1000,5],[1,2],[4,6,7],[4,8,9],[1,8,1001,10],[1,1000,11],[1,2,10],[1,11,1002,12,1001],[1,8,1003],[8,13,1004,11],[2,8,1005],[8,11,1006,12],[8,10,1007],[2,1008,14,1005],[15,14,1000,16,13,1009,1006],[8,9],[2,17,1005,18,1006],[2,8,9],[8,9]]),
 ([c1,c0,c2,c14,c16,c5,c4],[(0,[(1,1,2)]),(26,[]),(1,[(1,0,2),(1,1,2)]),(14,[]),(2,[(1,0,1)]),(15,[]),(49,[]),(5,[(1,1,2),(1,0,2)]),(13,[]),(1,[(1,1,2)]),(5,[(1,0,2)]),(10,[(1,0,1)]),(4,[(1,0,3)]),(10,[]),(5,[(1,1,2)])],[(1,3),(1,33),(4,6),(2,34),(4,12),(4,20),(12,40),(8,12),(1,25)],[[0,1,1000,2],[0,3],[3],[0,1,4,3],[0,3,5],[0,6,1001,7],[3,1,1002,2],[8,2,9,6,1000,1002],[3,1002,2],[3,2,5],[7,2,1000,6,1,1003,1001],[3,0,8,1004],[3,8],[3,4,1005],[3,6,1006,7,1007],[0,3],[3,5],[7,8,10,11,1,1001,1003],[3,12,1005,1008],[3,11,13,7,14],[5,3]]),
 ([c1,c0,c2,c3,c14,c29,c5,c4],[(0,[(1,1,2)]),(26,[]),(30,[]),(3,[(1,0,2)]),(3,[(2,0,2)]),(14,[]),(15,[]),(39,[]),(49,[]),(13,[]),(10,[]),(46,[]),(24,[]),(47,[]),(0,[(2,1,2)])],[],[[0,1,2],[0,2],[0,3],[3],[4],[0,5,6],[0,2],[5,1,7],[2,8],[9,2],[10,2,11],[2,1,5],[7,1],[2,0,1],[5,9],[9],[2,12],[5,8,13],[0],[14],[3,1],[2,1],[4],[6,1,5],[9,1],[6,1,5],[11,1],[2,5]]),
 ([c63,c1,c0,c2,c3,c5,c4],[(0,[]),(0,[(3,1,2)]),(3,[(3,0,2)]),(10,[]),(13,[]),(0,[(1,1,2)]),(14,[]),(15,[]),(5,[]),(28,[]),(43,[]),(2,[(1,0,1)]),(45,[]),(53,[]),(10,[(3,0,1)]),(32,[]),(51,[]),(8,[(3,0,1)])],[(1,3),(4,5),(1,33),(2,6),(0,6),(40,42),(4,12),(6,18),(20,48),(9,17),(12,36)],[[0,1,2],[3,4,1000],[5,4],[1,2],[4,6,7],[4,3,8],[1,9,1000,10],[1,6,1001],[1,2,11],[1,6,7],[1,12,1002,10],[6,13,1003,14,1004],[2,1005,14],[6,7],[15,16,1000,12,9,1005],[2,6,1006,11],[6,11,1007,1003],[6,14,1008,17,1003],[2,6,1009,1006],[2,12,1010,17,1006],[7,6]]),
 ([c1,c0,c2,c3,c14,c5,c26],[(0,[(1,1,4)]),(10,[]),(15,[]),(14,[]),(49,[]),(13,[(1,1,3)]),(1,[(1,0,2)]),(7,[]),(3,[(1,0,3)]),(2,[(1,0,1)]),(0,[(3,1,4)]),(13,[]),(39,[])],[(1,3),(1,33),(4,6),(40,42),(12,40),(20,48),(9,17),(1,9)],[[0,1,1000],[0,2],[0,2],[2],[0,2,3],[0,1,1001],[1,2,1002],[1,2,1003],[1,4,1000,5,1002],[1,2,3],[1,6,7,1000],[2,8,1004],[2,4,1004,5,1005],[2,9,1005,1004],[1,2,10],[0],[2,8,1006,1007],[1,2,1007],[2,3],[1,5,11,12,1001],[1,2,3]]),
 ([c57,c1,c0,c2,c3,c14,c5],[(0,[]),(0,[(3,1,4)]),(5,[(1,1,2)]),(8,[]),(1,[(1,0,2)]),(0,[(1,1,4)]),(15,[]),(39,[]),(13,[]),(14,[]),(36,[]),(13,[(3,1,3)]),(3,[(3,0,3)]),(47,[]),(2,[(1,0,1)]),(17,[])],[(1,33),(2,34),(10,42),(1,3),(1,5),(2,6),(40,42),(4,6),(8,12),(5,17),(9,17),(1,9)],[[0,1,2,1000],[2,3,1001,4],[5,2],[2,6,1002],[2,7,1000,8],[2,6,9],[1,3,1003],[1,6,1004],[1,6],[6],[1,6,9],[3,6,1005],[3,6,1006],[3,10,1003,11,1007],[3,6,9],[6,12,1008],[6,13,1004,11,1005],[6,14,1009,15],[1],[6,12,1010,1011],[6,9]]),
 ([0x3333222233332222,c1,c0,c2,c3,c5,c4],[(0,[]),(0,[(3,0,3)]),(1,[(1,0,3)]),(15,[(2,0,1)]),(14,[]),(39,[]),(26,[]),(55,[]),(8,[]),(10,[]),(4,[(2,0,1)]),(12,[]),(11,[])],[(1,5),(1,9),(2,3),(1,33),(2,6),(18,26),(2,34),(6,10)],[[0,1,2,3],[2,4],[3,4,5,1000,6,7],[3,4,5,1001,7],[1,2],[7,8,9],[1,2,1002],[1,4,1000],[1,4,1001],[1,2,3,10],[1,8,1003],[2,4,1004],[2,4,1005],[2,4,1],[2,8,1006],[4,11,1007,12],[4,7,11],[4,8,9],[4,7,12],[4,8,9],[7,4]]),
 ([c1,c0,c2,c19,c3,c17,c4],[(0,[(1,0,1)]),(10,[]),(1,[(1,0,3)]),(14,[]),(29,[]),(18,[(1,0,2)]),(1,[(3,0,3)]),(2,[(1,1,4)]),(8,[]),(18,[]),(26,[]),(3,[(1,0,1)]),(11,[])],[(3,18),(33,48),(1,9),(18,26),(4,6),(2,34),(6,10),(2,6),(6,18),(4,20),(4,12)],[[0,1,1000,2],[0,3],[0,4,1000,5,1001],[0,3,1002],[3,0,6],[0,1,1001,1000],[1,3],[3],[1,3,1003],[1,3,1004],[1,2,1005],[1],[3,7,1006,1007],[3,7,1008,1007],[1,3,8],[3,4,1003,5,1002],[3,5,9,10,1009],[1,5,8],[3,11,12,1010],[1,3,8],[1,3,8]]),
 ([c1,c0,c2,c3,c18,c17,c4],[(0,[(1,0,2)]),(1,[(1,0,3)]),(14,[]),(29,[]),(19,[(1,0,2)]),(3,[(3,2,4)]),(10,[]),(3,[(1,2,4)]),(2,[(1,0,2)]),(12,[]),(8,[]),(19,[]),(26,[])],[(3,18),(1,5),(33,48),(2,6),(8,26),(2,34),(6,10),(8,12),(8,24)],[[0,1,1000],[0,2,1001],[0,2],[0,3,1000,4,1002],[2,0,5],[0,6,1002,1000],[1,2,1003],[1,2],[2],[1,2,1004],[1,6,1005],[2,7,1006,1007],[2,3,1003,4,1001],[2,8,9,1003],[2,6,10],[1],[2,5,1008],[2,6,10],[2,4,11,12,1008],[6,4,10],[6,2,10]]),
 ([0x3333222233332222,c1,c0,c2,c3,c17,c4],[(0,[]),(0,[(3,0,3)]),(1,[(1,0,3)]),(29,[]),(15,[]),(14,[]),(39,[]),(55,[]),(10,[]),(8,[]),(4,[(2,0,1)]),(12,[]),(11,[])],[(1,5),(1,9),(3,18),(1,33),(2,6),(18,26),(2,34),(6,10)],[[0,1,2,3,4],[2,5],[4,3,5,6,1000,7],[4,3,5,6,1001,7],[2],[7,8,9],[1,2,1002],[1,5,1000],[1,5,1001],[5,1,10],[1,8,1003],[2,5,1004],[2,5,1005],[2,5],[2,8,1006],[5,11,1007,12],[5,7,11],[5,8,9],[5,7,12],[5,8,9],[7,5]]),
 ([c1,c0,c2,c3,c17,c26],[(0,[(1,1,4)]),(10,[]),(14,[]),(15,[]),(1,[(1,0,3)]),(7,[]),(11,[]),(2,[]),(0,[(3,1,4)]),(3,[(1,0,3)])],[(1,3),(1,9),(1,33),(4,6),(18,24),(4,12),(4,20),(8,24)],[[0,1,1000],[0,2],[0,2,1001],[0,2,3],[0,1,1002],[1,2,1003],[1,2,1004],[1,2,1003],[1,4,5,1000],[2,6,1005],[2,7,1006],[1,2,8],[2,9,6,1005],[1,2,1001],[1,2,1007]]),
 ([c57,c1,c0,c2,c3,c17],[(0,[(3,1,4)]),(8,[]),(1,[(1,0,3)]),(0,[(1,1,4)]),(14,[]),(15,[]),(11,[]),(2,[]),(3,[(3,0,3)])],[(1,33),(2,34),(10,34),(1,3),(1,5),(1,9),(2,6),(18,24),(4,6),(6,10),(4,12)],[[0,1,1000],[1,2,1001],[1,3],[1,4,1002],[1,4,1001],[0,1,1003],[0,4,1004],[0,4,1005],[0,4,5],[1,4,1006],[1,4,1007],[1,4,1008],[4,6,1009,1004],[4,7,1004,1006],[4,8,6,1010]]),
 ([c71,c1,c0,c2,c19,c3,c4],[(0,[(1,0,1)]),(14,[]),(10,[]),(15,[]),(2,[]),(4,[(1,1,2)]),(26,[]),(18,[]),(3,[(1,0,1)]),(8,[]),(1,[(3,0,3)]),(42,[]),(18,[(3,0,2)]),(2,[(3,1,4)]),(25,[])],[(10,26),(6,18),(2,3),(4,5),(8,9),(1,33),(18,26),(2,34),(6,10),(2,6),(1,9)],[[0,1],[2,3,1000],[1,3,4,1001,5],[3,6,1000,7],[1,3,5,1000,8],[2,3,9],[0,2,1002,10],[0,3,1003],[0,11,1002,12,1004],[0,3,1004],[0,2,1005],[1,2,3],[1],[1,2,3,1006],[2,10,1007],[2],[3,13,1008,1009],[2,1,3,9],[1,3,14,1006,12,1010],[2,9],[2,1,3,9]]),
 ([c71,c1,c0,c2,c3,c18,c4],[(0,[(1,0,2)]),(14,[]),(10,[]),(15,[]),(2,[(1,0,2)]),(4,[(1,1,3)]),(3,[]),(26,[]),(19,[]),(8,[]),(1,[(3,0,3)]),(42,[]),(19,[(3,0,2)]),(3,[(3,2,4)])],[(10,24),(6,18),(8,24),(2,3),(1,5),(8,9),(4,5),(1,33),(2,6),(2,34),(6,10),(8,12)],[[0,1],[2,3,1000],[1,3,4,1001,5],[1,3,5,1002,6],[3,7,1002,8],[2,3,9],[0,2,1003,10],[0,3,1004],[0,3,1005],[0,11,1003,12,1006],[0,2,1007],[1,2,3,1008],[1,2,3],[1],[2,10,1009],[3,13,1010,1011],[3,11,1008,12,1004],[2,1,3,9],[2],[2,1,3,9],[2,9]]),
 ([c71,c1,c0,c2,c3,c26],[(0,[(1,1,4)]),(14,[]),(10,[]),(4,[(1,2,4)]),(2,[(3,1,4)]),(15,[]),(3,[(1,0,3)]),(1,[(3,0,3)]),(7,[]),(0,[(3,1,4)])],[(10,24),(4,20),(8,24),(1,3),(4,5),(1,9),(2,3),(4,6),(18,24),(4,12)],[[0,1],[2,3,1000],[1,3,4,1001],[1,3,5,1002,6],[2,3,1002],[0,2,1003],[0,4,1004],[0,5,1005],[0,2,1004,1006],[1,2,4,1007],[1,2,5,1008],[2,7,8,1003],[1,4,5,1009],[2,4,9],[1,2,5,1005]]),
 ([c57,c71,c1,c0,c2,c3],[(15,[]),(8,[]),(0,[]),(1,[(3,0,3)]),(0,[(1,1,4)]),(2,[(1,1,4)]),(4,[(3,2,4)]),(3,[(3,0,3)]),(0,[(3,1,4)]),(2,[(3,1,4)]),(17,[])],[(18,34),(1,33),(2,34),(10,34),(10,24),(6,18),(8,24),(1,3),(1,5),(1,9),(2,6),(18,24),(6,10)],[[0,1,1000],[1,2,1001],[1,3,1002],[0,1,4],[0,1,1003],[0,1,5],[0,1,1004],[0,5,1005,6],[0,6,1006,7],[1,8,1007],[0,1,1008],[0,1,1009],[0,1,1010],[0,1,1011],[0,9,1012,10]]),
 ([c1,c0,c2,c3,c16,c5,c4,c45],[(0,[(1,1,2)]),(34,[]),(45,[]),(2,[(1,1,3)]),(49,[]),(3,[(1,2,3)]),(15,[(1,0,2)]),(14,[(1,0,2)]),(3,[(3,2,3)]),(17,[]),(1,[(1,1,2)]),(52,[]),(8,[(1,0,1)]),(10,[])],[],[[0,1],[0,2,3],[0,4,5],[0,2,6],[0,7,6],[0,1],[8],[1,2],[1,4],[1,2],[1,7],[9,2],[10,1,11],[3,2],[5],[3,2],[1,4,9],[3,4,12],[3],[5,4],[1,2,12],[5,2,12],[9,2],[1,13,9],[6,13,12],[1,2,7],[6,2,7],[0]]),
 ([c1,c0,c2,c3,c5,c20,c4,c45],[(0,[(1,1,3)]),(24,[]),(14,[(1,0,2)]),(15,[(1,0,2)]),(15,[(3,0,2)]),(45,[]),(56,[]),(10,[(1,0,2)]),(17,[]),(1,[(1,1,3)]),(52,[]),(2,[(1,1,3)]),(4,[(1,0,4)]),(51,[])],[],[[0,1],[0,1],[0,1],[0,2,3],[0,2,3],[0,1],[4],[2,5],[2,6,7],[3,1],[3,1],[8,5],[9,1,10],[8,5,11],[8,1],[8],[2,7,6],[2,1,6],[10,1,12],[8,1,13],[2,5,6],[2,1,6],[11],[3,1],[3,2],[3,1],[3,2],[0]]),
 ([c1,c0,c2,c19,c62,c3,c5,c4],[(0,[(1,0,1)]),(2,[(1,1,2)]),(1,[(1,0,1)]),(18,[]),(26,[]),(51,[]),(29,[]),(42,[]),(2,[(2,1,2)]),(1,[(2,0,1)]),(10,[]),(8,[]),(3,[(1,0,1)]),(31,[])],[],[[0,1,2],[0,2,1],[0,3],[3],[0,4,5],[0,6,7],[0,5],[1,2],[1],[8],[2,6],[2,4],[2,4],[2],[9],[1,4,7],[1,6,7],[1,10,11],[0],[3,6],[3,4],[3,4],[12,5,13],[13,4],[11,4,10],[5,4,6],[7,4],[5,6]]),
 ([0x5454545454545454,c1,c0,c2,c3,c5,c4],[(0,[(1,0,1)]),(18,[]),(2,[(1,1,2)]),(0,[(2,0,1)]),(3,[]),(14,[]),(4,[]),(10,[]),(8,[]),(50,[]),(14,[(3,0,1)]),(15,[(3,0,1)]),(2,[(3,1,2)]),(37,[]),(30,[]),(24,[]),(51,[]),(52,[])],[(4,12),(1,3),(1,5),(1,9),(33,48),(8,9),(1,33),(18,26),(3,17),(2,34),(5,17)],[[0,1,2],[0,1,2],[0,1,3],[1,1000,4],[1,5,6],[1,7,8],[0,1,1001],[0,1,1002],[0,9,1003,10],[0,10,1004,11,1005],[0,7,1006],[1,7,0,12],[1,1007,10],[1,10,1008,11,1001],[1,7,1009],[1,13,1000,14],[1,15,1010,14,1002],[1,7,8],[16,17,1000,15,9,1007],[7,8],[7,8]]),
 ([c1,c2,c19,c3,c18,c5,c4],[(2,[(1,0,2)]),(0,[(1,0,1),(1,0,2)]),(18,[]),(0,[(1,0,2)]),(26,[]),(14,[]),(19,[]),(0,[(1,0,1)]),(15,[]),(17,[(1,1,2)]),(6,[]),(3,[(1,0,1)]),(17,[]),(8,[]),(5,[(1,0,4)])],[(4,5),(8,9),(1,33),(0,33),(6,10),(4,6),(6,18),(2,6),(40,42),(8,24),(10,34),(18,26),(2,34)],[[0,1000,1],[2,1,3,4,1000,1001],[5,1001,1],[6,1,7,4,1001,1000],[5,1,8],[9,1,1000,10,1002,1003],[6],[0,4,1004,5,11],[0,4,11,6,1005],[0,5,1006,1007],[0,10,9,1007],[5,0,2,1008],[0,5],[5,2,8],[9,2,12,10,4,1008],[2],[5,11,1009],[5,10,1010,13,1011],[5,6,8],[9,6,14,10,4,1012,1002],[8,5]]),
 ([c1,c0,c19,c3,c5,c26],[(0,[(1,0,1),(1,1,4)]),(10,[]),(1,[(1,1,4)]),(18,[]),(14,[]),(15,[]),(0,[(1,0,1)]),(6,[]),(3,[(1,0,3)]),(4,[(1,2,4)]),(8,[]),(4,[(1,1,2),(1,2,4)]),(3,[(1,0,1),(1,0,3)]),(11,[]),(3,[(1,0,1)]),(26,[]),(4,[(1,1,2)])],[(2,3),(8,9),(3,18),(18,26),(10,26),(2,6),(12,40),(8,24),(1,9)],[[0,1,2,1000],[0,1,1000,3,1001],[0,1,1001,4,1000],[0,1,4,1002,5,1000],[0,1,6,7,1000],[1,4],[1,1003,4],[1,4,1004,5],[1,2,1005],[3,4,8,1006,1003],[3,5,9,4,1004,1007],[1,2,10],[4,11,12,1008,13,1004,1003],[1,4,14,15,1003],[1,5,16,4,1004]]),
 ([c1,c0,c2,c19,c3,c39,c5,c4],[(18,[]),(26,[]),(45,[]),(3,[(1,0,1)]),(0,[(1,0,1)]),(57,[]),(14,[]),(37,[]),(32,[]),(2,[(1,0,2)]),(10,[(1,0,1)]),(1,[(3,1,2)]),(58,[]),(4,[(1,1,2)])],[],[[0,1],[0,2],[0,1],[3,1],[4,1,5],[5,6],[7,2,8],[6,2],[6],[0,9,3],[6],[0,1],[0,1],[10],[0,1,2],[11],[0,2],[0,12],[0,2],[3],[0,1],[0,1],[0],[3,1],[3,1],[13,1,6],[5,1],[5,2,6]]),
 ([c1,c0,c2,c3,c39,c5,c4],[(1,[(1,1,2)]),(52,[]),(14,[]),(10,[(1,0,1)]),(57,[]),(0,[]),(26,[]),(15,[]),(17,[(1,1,2)]),(37,[]),(45,[]),(3,[(1,0,1)]),(2,[(1,0,2)]),(19,[]),(18,[]),(8,[(1,0,1)]),(8,[]),(10,[])],[(2,3),(4,5),(8,9),(32,33),(1,33),(2,34),(6,18),(2,6),(12,40),(8,24),(10,34),(4,12)],[[0,1000,1],[2,1001,3],[2,1002,3],[4,3,5,6,1000,1003],[2,1,7],[8,9,1000,10,1004,1003],[0,1,11,2],[0,2,12],[2],[0,2,7],[0,10,1005,1],[2,11,0,12],[13],[2,12,1006,1007],[2,3,1008,8,1007],[14],[2,11,1009],[2,3,1010,15,1011],[2,7],[8,4,16,3,6,17],[1,2,7]]),
 ([c56,c1,c0,c2,c3,c5,c4],[(0,[]),(26,[]),(18,[]),(0,[(2,0,2)]),(3,[(1,0,1)]),(3,[(2,0,1)]),(3,[(3,0,1)]),(2,[(1,0,2)]),(14,[]),(4,[]),(10,[]),(8,[]),(52,[]),(10,[(2,0,1)]),(51,[]),(15,[]),(17,[(1,1,2)]),(37,[]),(6,[(2,1,2)]),(1,[(2,1,2)]),(49,[]),(8,[(2,0,1)])],[(2,3),(4,5),(1,9),(0,9),(1,33),(0,33),(40,42),(4,6),(8,12),(6,18),(12,40),(9,17),(10,42)],[[0,1,2,1000],[2,3,4,5],[2,4,6],[4,2,7],[2,8,9],[2,10,11],[2,1000,12],[2,1001,13],[4,14,1002,13,1003],[8,12,15],[16,17,1000,18,14,1004,1005],[2,8,4,19],[2,4,1006],[2,8,15],[2,20,1006,12,1007],[2,1,1008,4],[2,8,1009,1008],[2,13,1010,16,1008],[4,8,1011,1002],[4,13,1012,21],[12,8,15]]),
 ([c1,c0,c2,c3,c18,c37,c5,c4],[(0,[(1,0,2)]),(3,[(1,1,2)]),(1,[(1,0,2)]),(44,[]),(19,[]),(29,[]),(42,[]),(3,[(3,1,2)]),(37,[]),(15,[]),(33,[]),(10,[]),(8,[])],[],[[0,1,2],[0,3],[0,2,1],[0,4],[4],[0,5,6],[0,3],[2,5],[1,2],[1],[7],[2,8],[2,5],[1,8],[3,5],[9,3,10],[3,5],[10,11],[2],[11],[1,5,8],[1,8],[0],[4,8],[3,5],[9,8,10],[12,3,11],[3,5]]),
 (l10,[(0,[(1,0,2)]),(19,[]),(3,[(1,1,2)]),(15,[]),(0,[(2,0,2)]),(14,[]),(8,[]),(10,[]),(43,[]),(15,[(3,0,1)]),(14,[(3,0,1)]),(3,[(2,1,2)]),(51,[]),(17,[(3,0,1)]),(25,[]),(24,[])],[(2,6),(1,3),(1,5),(1,9),(33,48),(4,5),(1,33),(3,17),(2,34),(6,10),(5,17),(0,20),(9,17)],[[0,1,2],[0,1,2],[1,1000,3],[0,1,4],[1,5,3],[1,6,7],[0,1,1001],[0,8,1002,9],[0,1,1003],[0,10,1004,9,1005],[0,6,1006],[1,1000,9],[1,6,0,11],[1,10,1007,9,1001],[1,6,1008],[1,1009,12,1003],[13,14,1000,15,8,1010,1011],[6,7],[1,15,1012,12,1003],[1,6,7],[6,7]]),
 ([c1,c0,c2,c18,c16,c5,c4],[(19,[]),(0,[(1,0,2),(1,1,2)]),(1,[(1,1,2)]),(15,[]),(0,[(1,1,2)]),(49,[]),(14,[]),(17,[]),(2,[(1,0,2)]),(5,[(1,0,2)]),(10,[(1,0,1)]),(37,[]),(4,[(1,1,3)]),(10,[]),(8,[])],[(2,3),(4,5),(1,33),(0,33),(6,10),(2,34),(4,12),(4,20),(12,40),(2,26)],[[0,1,2,1000],[3,1001,1],[0,1,4,5,1000,1001],[3,1001,1],[3,6],[7,1,1000,5,1002,1003],[2,3,1004],[3],[2,3,8],[2,3,6],[2,5,1005,7],[0,3,2,1006],[0],[3,8,1007],[3,5,1008,7,1004],[2,3],[3,5,6],[7,0,9,10,11,1005,1002],[3,12,1007,1009],[3,10,13,7,14],[3,5,6]]),
 ([c1,c0,c2,c3,c18,c39,c5,c4],[(19,[]),(42,[]),(15,[]),(43,[]),(49,[]),(0,[(1,0,2)]),(57,[]),(14,[]),(2,[(1,0,2)]),(58,[]),(8,[(1,0,1)]),(1,[(2,1,2)]),(37,[])],[],[[0,1],[2,3],[0,4],[0,1],[5,1,6],[1,7],[3,4],[0,1],[2,4],[2],[2],[0,7,2],[0,1],[0,4],[0,1],[0],[1,3,8],[2,4,9],[10],[11],[0,4],[0,12],[2],[0,4],[0,1],[2,3,7],[6,1],[1,4,3]]),
 ([c70,c1,c0,c2,c3,c5,c4],[(0,[]),(19,[]),(0,[(2,0,1)]),(15,[]),(1,[(1,1,2)]),(14,[]),(10,[]),(8,[]),(52,[]),(44,[]),(8,[(3,0,1)]),(17,[(2,1,2)]),(25,[]),(6,[(3,1,2)]),(2,[(1,0,2)]),(1,[(3,1,2)]),(45,[])],[(2,3),(1,5),(0,5),(8,9),(1,33),(0,33),(4,6),(2,34),(4,12),(5,17),(20,48),(8,24),(10,34)],[[0,1,1000],[1,2,3],[3,1,4],[1,3,4],[1,3,5],[1,6,7],[1,1000,8],[3,9,1001,10,1002],[1,1003,10],[3,5],[11,12,1000,13,9,1004,1005],[1,3,1006],[1,3,14,15],[1,3,5],[1,16,1007,8],[1,3,1008,14],[3,14,1009,1001],[3,13,1010,10,1001],[1,3,1011],[1,13,1012,10,1008],[3,5]]),
 ([c1,c0,c2,c3,c18,c5,c26],[(10,[]),(1,[(1,1,4)]),(15,[]),(49,[]),(19,[(1,1,3)]),(14,[]),(0,[(1,0,2)]),(6,[]),(2,[(1,0,2)]),(3,[(1,0,3)]),(1,[(3,1,4)]),(19,[]),(37,[])],[(2,3),(4,5),(8,9),(2,34),(12,40),(20,48),(8,24),(18,26)],[[0,1,1000],[0,2,1001],[0,2,1002],[0,3,1000,4,1001],[0,2,5],[0,6,7,1000],[0,2],[0,2],[2],[0,2,5],[0,1,1003],[2,8,1004,9],[2,3,1004,4,1005],[2,8,1005,1004],[0,2,10],[0],[2,9,1006],[0,2,1007],[2,3,5],[0,4,11,12,1003],[0,2,5]]),
 ([c57,c1,c0,c2,c3,c18,c5],[(0,[(1,0,2)]),(8,[]),(1,[]),(1,[(1,1,4)]),(15,[]),(37,[]),(19,[]),(14,[]),(1,[(3,1,4)]),(58,[]),(19,[(3,1,3)]),(2,[(1,0,2)]),(3,[(3,0,3)]),(17,[])],[(1,33),(2,34),(10,34),(2,3),(1,5),(8,9),(4,5),(2,6),(6,10),(5,17),(8,24)],[[0,1,1000],[1,2,1001],[3,1],[1,4,1002],[1,5,1001,6],[1,4,7],[1,8,1003],[1,4,1004],[1,4,1005],[1,9,1003,10,1006],[1,4,7],[1,4,1007],[1,4],[4],[1,4,7],[4,11,1008,12],[4,9,1007,10,1004],[4,11,1009,13],[1],[4,12,1010],[4,7]]),
 ([c1,c0,c2,c3,c16,c5,c4,c73],[(1,[(1,1,2)]),(26,[]),(15,[(1,1,2)]),(45,[]),(14,[(1,1,2)]),(17,[]),(0,[(1,1,2)]),(43,[]),(49,[]),(2,[(1,2,3)]),(8,[(1,0,1)]),(6,[])],[],[[0,1],[2,3],[2,1],[2,1],[2,4],[5,3],[6,1,7],[0,1],[0,8,2],[0,3,2],[0,1],[0,1],[5],[5,1],[5],[5,3,9],[2,8,5],[2,1,10],[9],[7,1],[2,1],[2,3,10],[5,1],[2,1],[2,11,10],[2,3,4],[2,1,4],[0]]),
 ([c30,c1,c0,c2,c3,c4],[(15,[]),(0,[]),(19,[]),(6,[]),(0,[(2,1,3)]),(3,[]),(0,[(0,1,3)]),(2,[]),(17,[]),(8,[]),(2,[(2,0,4)]),(3,[(2,0,4)])],[(4,5),(10,26),(4,6),(2,3),(1,3),(1,21),(8,12),(1,25),(4,12),(2,34),(32,33),(1,33),(10,14),(2,26),(32,34),(40,44),(36,44)],[[0,1000,1],[0,1001,2,3],[0,4,5,6],[0,5,7],[0,3,8,9],[1000,1002,1003,1004],[0,1005,1006],[0,1007,1008],[8,1009,1010,1011],[0,1012,1005],[0,1013,1007],[8,1011,1014,1009],[0,10,1006,11],[0,1015,8,1005],[0,1016,1007]]),
 ([0xff00ff00f000f0,c1,c0,c2,c3,c5,c4],[(0,[]),(49,[]),(10,[]),(43,[]),(59,[]),(0,[(2,1,2)]),(3,[(1,0,3)]),(3,[(3,0,3)]),(15,[]),(14,[]),(6,[]),(7,[]),(17,[])],[(4,5),(4,6),(1,3),(1,9),(18,24),(8,12),(4,20),(9,17)],[[0,1,2,3,1000,4],[2,4,1001],[4,5,6,7],[2],[4,8,9],[2,4,6],[2,10,1002,11],[2,3,1000,4],[2,1,1003,3],[2,8,9],[2,4,10],[2,4,1001],[2,1,1004,6],[2,8,9],[2,4,11],[4,1,1005,6],[4,8,1006],[2,4,8,12],[6,8,1007,1003],[2,4],[2,4]]),
 ([0xff00ff00f000f0,c1,c0,c2,c3,c5,c26],[(0,[(1,1,4)]),(49,[]),(10,[]),(43,[]),(59,[]),(3,[(1,0,3)]),(17,[]),(15,[]),(14,[]),(6,[]),(7,[])],[(4,5),(4,6),(1,3),(1,9),(18,24),(12,40),(4,20),(9,17)],[[0,1,2,3,1000,4],[2,4,1001],[4,5,6],[2],[4,7,8],[2,4,5],[2,9,1002,10],[2,3,1000,4],[2,1,1003,3],[2,7,8],[2,4,9],[2,4,1001],[2,1,1004,5],[2,7,8],[2,4,10],[4,1,1005,5],[4,7,1006],[2,4,6],[5,7,1007,1003],[2,4],[2,4]])]
def d349 : List StD := dupD [
 ([c21,c6,c19,c3,c5,c4],[(15,[]),(6,[]),(0,[(1,0,1)]),(6,[(1,0,1)]),(15,[(1,0,1)]),(10,[]),(14,[]),(5,[(1,0,1),(1,0,4)]),(45,[]),(25,[]),(3,[(1,1,2),(1,0,1)]),(37,[]),(45,[(1,0,1)]),(26,[]),(4,[(1,0,1),(1,1,2)]),(14,[(1,0,1)]),(29,[]),(8,[]),(51,[]),(3,[(1,1,2),(1,0,2)]),(18,[]),(4,[(1,0,1),(1,0,2)]),(24,[]),(3,[(1,1,2),(1,0,2),(1,0,1)]),(24,[(1,0,1)])],[(1,9),(4,12),(9,17),(4,20)],[[0,1,2,3,4],[0,2,4],[0,5,1000],[0,5,6],[5,7,8],[1,2,3],[4,9,10,11,12,13],[4,9,14,15,12,16],[5,9,17],[4,18,19,9,1001,1000],[4,20,21,15,9,22],[5,17],[18,23,1000,24,11,1002,1003],[5,4,17],[5,4,17]]),
 ([c49,c21,c2,c6,c3,c5,c4],[(0,[]),(0,[(1,0,1)]),(0,[(3,0,1)]),(0,[(0,0,1)]),(3,[(1,1,2),(1,0,2)]),(51,[]),(25,[]),(14,[(1,0,1)]),(15,[(1,0,1)]),(15,[(2,0,1)]),(45,[]),(10,[]),(43,[]),(35,[]),(8,[]),(24,[])],[],[[0,1,2],[2,3],[3],[4,5,6],[6,7,8],[6,5],[9,10],[9,10],[9,5,11],[9,6,11],[12,5,10],[2],[5,13],[6,12],[5,11,14],[6,5],[6,12],[6,5],[5,15],[13,11],[5,11,12]]),
 ([c21,c2,c6,c3,c18,c5,c4],[(15,[]),(3,[(1,0,2),(1,1,5)]),(10,[]),(0,[(1,0,2)]),(14,[]),(43,[]),(25,[]),(60,[]),(3,[(1,1,2),(1,0,2)]),(15,[(1,0,1)]),(44,[]),(8,[]),(26,[]),(19,[]),(36,[])],[],[[0,1,2],[0,1,2],[0,3,2],[0,3],[0,4],[5,6,7],[2],[6,8],[9,10],[6,5],[6,2,11],[6,12,8],[13,9,12],[6,5],[6,2,10],[2],[5,14],[8,2,11],[5,6],[10,2,6],[5,2]]),
 ([c0,c2,c6,c3,c37,c5,c4],[(15,[(1,0,1)]),(8,[]),(26,[]),(0,[(1,0,2)]),(0,[(3,0,2)]),(14,[(1,0,1)]),(51,[]),(25,[]),(3,[(1,0,2),(1,1,2)]),(3,[(1,0,2),(1,1,5)]),(43,[]),(10,[]),(24,[])],[],[[0,1],[1,0,2],[0,3,1],[4],[0,5],[6,7],[1],[6,8],[0,9,10],[7,10],[0,11,1],[0,2],[0,10],[0,5],[1,6,7],[1],[6,12],[0,11,1],[0,5],[1,6,11],[0,5]]),
 ([c0,c21,c6,c3,c16,c5,c4],[(0,[(1,1,2)]),(10,[(1,0,1)]),(15,[(1,0,1)]),(26,[]),(26,[(1,0,1)]),(44,[]),(43,[]),(45,[]),(14,[(1,0,1)]),(8,[(1,0,1)]),(0,[(2,1,2)]),(24,[])],[],[[0],[1,2,3],[1,2],[1,2],[1,4],[5,4],[1,2],[1,2],[1,5],[1,4],[6,4,7],[2,0,3],[0,2],[2,6,8],[9,1],[10],[6,4],[2,1,4],[5,4,11],[2,1,4],[2,1,6]]),
 ([c1,c2,c19,c3,c37,c5,c4],[(0,[(1,0,1),(1,0,2)]),(15,[(1,0,1)]),(24,[]),(26,[]),(15,[(3,0,1)]),(14,[(1,0,1)]),(51,[]),(0,[(1,0,2),(2,0,1)]),(3,[(1,0,1),(1,1,2)]),(45,[]),(25,[]),(29,[]),(52,[]),(10,[]),(8,[])],[],[[0,1],[0,1,2],[0,3,1],[4],[0,5,1],[0,6],[7],[6,3,8],[1,3,9],[10,11,12],[1,13,14],[1,10,6],[1,9],[1,2],[6,3],[13],[6,3,8],[1,3],[1,3,5],[12,3,9],[1,5]]),
 ([c1,c21,c2,c3,c39,c5,c4],[(14,[(3,0,1)]),(14,[(1,0,1)]),(8,[(1,0,1)]),(26,[]),(24,[]),(15,[(1,0,1)]),(25,[]),(34,[]),(52,[]),(45,[]),(3,[(1,1,2),(1,0,1)]),(3,[(1,1,2),(3,0,1)]),(10,[(1,0,1)]),(10,[(2,0,1)])],[],[[0],[1,2],[1,3],[2,1,4],[2,1,5],[6,7],[0,3,2],[0,6,2],[0,1,2],[2,0,3],[8,3,9],[6,2,10],[11],[6,8],[1,12,2],[13],[8,3],[1,3],[5,1],[2,3,12],[2,1,5]]),
 ([c56,c1,c21,c2,c3,c5,c4],[(0,[]),(3,[(1,1,2),(1,0,5)]),(26,[]),(0,[(2,0,2)]),(15,[]),(0,[(0,0,2)]),(3,[(1,1,2),(1,0,1)]),(10,[(1,0,1)]),(14,[(1,0,1)]),(15,[(1,0,1)]),(8,[]),(3,[(1,0,1),(2,1,2)]),(8,[(2,0,1)]),(37,[]),(51,[]),(52,[]),(49,[]),(18,[]),(10,[(2,0,1)])],[],[[0,1,2],[3,1,4,5],[1,6,2],[7],[2,8,9],[2,7,10],[11],[8,12],[6,2],[9,8],[13,14],[4,2,12],[4,14,12],[4,2,8],[15,2,16],[6,2],[17,15],[8,18,12],[6,2],[6,2],[9,8]]),
 ([c1,c2,c62,c3,c18,c5,c4],[(0,[(1,0,1),(1,0,2)]),(3,[(1,0,2),(1,1,5)]),(15,[(1,0,1)]),(15,[(3,0,1)]),(26,[]),(24,[]),(14,[(1,0,1)]),(44,[]),(0,[(1,0,2),(2,0,1)]),(52,[]),(25,[]),(10,[]),(8,[]),(49,[])],[],[[0,1,2],[3],[0,4,1],[0,2,5],[0,6,2],[0,7],[8],[1,4],[2,4,7],[7,9,10],[2,11,12],[1,10,13],[1,13],[2,4,6],[12,4,11],[11],[1,4],[1,4],[2,4,5],[7,4],[2,6]]),
 ([c1,c21,c2,c18,c16,c5,c4],[(3,[(2,1,2)]),(0,[(1,0,2),(1,1,2)]),(15,[(1,0,1)]),(34,[]),(26,[]),(14,[(1,0,1)]),(10,[(1,0,1)]),(0,[(1,0,2),(1,1,5)]),(17,[]),(49,[]),(35,[]),(0,[(1,0,2),(3,1,2)]),(25,[]),(8,[(1,0,1)]),(4,[(1,0,1),(1,1,3)]),(29,[])],[],[[0],[1,2],[1,2,3],[1,4,2],[1,5,2],[1,3],[2,4,6],[0,1],[2,7,6],[2,4,5],[8,3,9],[2,4,10],[11],[12,10],[2,6,13],[2,6],[2,4,5],[10,4,6],[14,4,15],[2,4],[2,5]]),
 ([c70,c1,c21,c2,c3,c5,c4],[(0,[]),(15,[(1,0,1)]),(24,[]),(0,[(0,0,1)]),(10,[(1,0,1)]),(8,[]),(15,[(3,0,1)]),(44,[]),(8,[(3,0,1)]),(28,[]),(14,[(1,0,1)]),(25,[]),(52,[]),(45,[]),(35,[]),(10,[(3,0,1)])],[],[[0,1,2],[1,3],[4],[1,4],[1,2],[5,4],[6],[1,7,8],[1,9],[1,10],[11,7],[1,7,8],[1,11,8],[1,9,8],[12,7,13],[7,14,11],[7,12,9],[1,15,8],[12,9],[1,9],[1,10]]),
 ([c49,c1,c2,c62,c3,c5,c4],[(0,[(1,0,1)]),(15,[(1,0,1)]),(35,[]),(25,[]),(10,[]),(8,[]),(24,[]),(18,[]),(29,[]),(42,[]),(15,[(2,0,1)]),(36,[]),(14,[(2,0,1)]),(52,[])],[],[[0,1],[1,0],[0],[1,2,3],[1,2,3],[3,4,5],[4,6],[7],[2,6],[2,8,9],[3,6],[4],[3,2],[3,2],[3,4,5],[10,2,11],[10,2,12],[5,3,4],[13,6,11],[2,4],[2,4]]),
 ([c1,c0,c2,c3,0xfffefffefffefffe,c5,c4],[(52,[]),(15,[(1,0,1)]),(24,[]),(10,[(1,0,1)]),(15,[(3,0,1)]),(14,[(1,0,1)]),(25,[]),(15,[(2,0,1)]),(45,[]),(10,[(3,0,1)]),(8,[(1,0,1)]),(10,[(2,0,1)]),(36,[])],[],[[0,1,2],[1,2,3],[1,2,3],[4],[0,5,1],[6,2],[1,0],[0,6,3],[7],[1,2],[0,6,8],[6,3,8],[9],[6,0],[1,3,10],[11],[0,2,12],[1,3,10],[1,0,5],[10,2,3],[0,2,1]]),
 ([0xfe00fe00fe00fe,c1,c0,c2,c3,c5,c4],[(0,[]),(15,[(1,0,1)]),(15,[(3,0,1)]),(15,[(2,0,1)]),(10,[]),(10,[(1,0,1)]),(14,[]),(8,[]),(36,[]),(34,[]),(3,[(1,0,2),(1,1,5)]),(8,[(2,0,1)]),(49,[]),(14,[(1,0,1)]),(0,[(1,0,1),(3,2,5)]),(52,[])],[],[[0,1,2],[1,3],[1,4],[5],[1,6],[7,4],[8,1,9],[1,10,11],[1,12],[1,13],[8,9],[1,14,11],[1,8],[1,13],[15,12],[10,12],[8,15],[1,12,11],[10,8],[1,8],[1,12,11]]),
 ([c1,c0,c2,c37,c16,c5,c4],[(0,[(1,0,2),(1,1,2)]),(15,[(1,0,1)]),(34,[]),(15,[(3,0,1)]),(49,[]),(14,[(1,0,1)]),(26,[]),(8,[(1,0,1)]),(0,[(1,1,2),(3,0,2)]),(51,[]),(45,[]),(0,[(1,0,2),(3,1,2)]),(36,[]),(35,[]),(24,[])],[],[[0,1,2],[0,1],[3],[0,4,1],[0,5,1],[0,2],[1,6,7],[8],[1,4],[1,5],[9,4,6],[1,4,10],[11],[12,13],[1,4,7],[1,7],[1,4,5],[7,2,10],[9,4,14],[1,6],[1,4,5]]),
 ([0xf0e0f0e0f0e0f0e,c1,c0,c2,c3,c5,c4],[(0,[]),(15,[(1,0,1)]),(15,[(3,0,1)]),(15,[(2,0,1)]),(8,[(1,0,1)]),(36,[]),(14,[]),(10,[]),(34,[]),(45,[]),(51,[]),(8,[(3,0,1)]),(14,[(1,0,1)]),(52,[]),(10,[(3,0,1)])],[],[[0,1,2],[1,3],[4],[1,4],[1,5,6],[4,5,7],[5,1,8],[1,9],[1,10,11],[1,12],[5,8],[1,9],[1,5],[1,12],[10,9,13],[10,9],[5,9],[1,14,11],[10,5,13],[1,5],[1,9,11]]),
 ([c1,c0,c2,0xf0f0f0f0fefefefe,c3,c5],[(8,[]),(6,[]),(2,[(1,1,2),(3,3,5)]),(7,[]),(45,[]),(18,[]),(18,[(2,0,3)]),(28,[]),(43,[]),(61,[]),(21,[(1,0,1)]),(0,[(1,0,1)]),(62,[]),(0,[(3,0,1)]),(63,[]),(52,[]),(64,[]),(34,[]),(65,[]),(48,[]),(56,[]),(14,[]),(15,[])],[(1,5),(1,9),(3,18),(2,3),(2,6),(18,26),(3,17),(1,3),(6,10),(5,17),(16,24)],[[0,1,2,3],[0,2,1000],[0,4,5,6],[0,7,1001,8],[0,9,1002,10,1003],[0,2,1004],[0,4,11,12,13],[0,14,1005,15],[0,16,1006,17,1007],[0],[2,18,1008,19,1000],[2,20,1009,10,1000],[17,12,21,7,4,1001,1010],[10,12,22,9,4,21],[10,8,1001,9,7,1005]]),
 ([c22,c1,c0,0xf000f000f000f000,c2,c3,c5],[(0,[(0,1,2)]),(34,[]),(0,[(0,1,2),(2,0,4)]),(0,[(0,1,2),(0,0,4)]),(8,[]),(48,[]),(8,[(0,0,1)]),(36,[]),(14,[]),(18,[(2,0,3)]),(51,[]),(61,[]),(42,[]),(28,[]),(0,[(2,0,4),(2,1,2)]),(0,[(2,0,4),(3,1,2)]),(21,[]),(60,[])],[(6,10)],[[0,1],[2,3],[1,4],[1,5,6],[1,7],[1,8],[2,1],[2,9],[2,5],[2,10],[2,11,12],[1,4],[1,12,6],[1,11,6],[1,13,6],[14],[15],[9,16],[1000,9,5],[5,17,9],[10,11]]),
 ([c22,c1,c0,c2,c3,c16,c5],[(0,[(1,1,2)]),(18,[]),(65,[]),(8,[(1,0,1)]),(36,[]),(14,[]),(0,[(2,0,4),(1,1,2)]),(34,[]),(45,[]),(28,[]),(60,[]),(66,[]),(67,[]),(49,[]),(0,[(2,0,4),(3,1,2)]),(0,[(2,0,4),(2,1,2)]),(21,[])],[(6,10)],[[0,1],[1,0],[1,2,3],[3,4,5],[3,4,5],[3,2],[6,2,7],[3,8,9],[3,2,10],[3,2,11],[3,12,11],[3,2],[3,13,7],[3,8,7],[3,2],[1000,2,8],[14],[9,8],[15],[10,2],[16,2]]),
 ([c22,0xf000f000f000f0,c1,c0,c2,c3,c5],[(14,[]),(8,[]),(0,[(2,1,2)]),(34,[]),(0,[(2,1,2),(2,0,4)]),(0,[(2,1,2),(0,0,4)]),(65,[]),(8,[(2,0,1)]),(28,[]),(60,[]),(0,[(2,0,4),(0,1,2)]),(0,[(2,0,4),(1,1,2)]),(61,[]),(66,[])],[(0,12)],[[0,1],[2,3],[4,5],[0,6,7],[0,8],[3,0],[1,9,6],[1,9,3],[10],[11],[6,9],[4,3],[4,9,8],[4,6,9],[4,12,13],[3,6,7],[3,12,7],[3,6,7],[12,6,1000],[8,9],[9,6]]),
 ([c22,0xf000f000f000f00,c1,c0,c2,c3,c5],[(8,[]),(28,[]),(34,[]),(0,[(3,1,2)]),(0,[(3,1,2),(2,0,4)]),(0,[(3,1,2),(0,0,4)]),(48,[]),(8,[(3,0,1)]),(14,[]),(45,[]),(63,[]),(0,[(2,0,4),(1,1,2)]),(0,[(2,0,4),(0,1,2)]),(60,[]),(67,[]),(42,[])],[(0,12)],[[0,1,2],[3,2],[4,5],[1,6,7],[2,1],[2,8],[0,1,9],[0,10,2],[11],[12],[9,1],[4,1,2],[1,6,4],[4,1,13],[4,14,15],[2,9],[2,10],[2,1,7],[6,9,1000],[1,9],[13,1]]),
 ([c22,c1,c0,c2,c3,c5,c20],[(0,[(1,1,3)]),(34,[]),(0,[(1,1,3),(2,0,4)]),(0,[(1,1,3),(0,0,4)]),(56,[]),(8,[(1,0,2)]),(14,[]),(60,[]),(24,[]),(61,[]),(21,[]),(66,[]),(45,[]),(51,[]),(0,[(2,0,4),(2,1,3)])],[],[[0,1],[2,3],[1,4,5],[1,4,5],[1,6],[1,6],[2,1],[2,7,8],[2,8],[2,9,10],[2,7,11],[1,4,5],[1,4,5],[1,8],[1,7],[9,12],[10,4],[10],[7,4,10],[13,4],[14]]),
 ([c22,0xf0f00000f0f0,c1,c0,c2,c3,c5],[(14,[]),(8,[]),(0,[(2,1,3)]),(34,[]),(0,[(2,1,3),(2,0,4)]),(0,[(2,1,3),(0,0,4)]),(56,[]),(8,[(2,0,2)]),(68,[]),(28,[]),(0,[(2,0,4),(0,1,3)]),(0,[(2,0,4),(1,1,3)]),(51,[]),(61,[]),(21,[])],[],[[0,1],[2,3],[4,5],[0,6,7],[0,6,7],[3,0],[1,8,9],[1,8,3],[10],[6,8],[11],[4,3],[4,8,9],[4,9,12],[4,13,8],[3,6,7],[3,6,7],[3,9,7],[12,8],[9,6,14],[8,6]]),
 ([c22,c1,c0,c2,c3,c5,c7],[(0,[(1,2,3)]),(34,[]),(0,[(1,2,3),(2,0,4)]),(0,[(1,2,3),(0,0,4)]),(56,[]),(8,[(1,1,2)]),(14,[]),(24,[]),(61,[]),(21,[]),(42,[]),(49,[]),(0,[(2,0,4),(2,2,3)])],[],[[0,1],[2,3],[1,4,5],[1,4,5],[1,6],[1,6],[2,1],[2,7],[2,7],[2,8,9],[2,8,10],[1,4,5],[1,4,5],[1,7],[1,7],[8,11,10],[9,4],[10,4],[9,4],[9],[12]]),
 ([c22,c64,c1,c0,c2,c3,c5],[(14,[]),(54,[]),(0,[(2,2,3)]),(21,[]),(56,[]),(8,[(2,1,2)]),(69,[]),(61,[]),(70,[]),(34,[]),(0,[(2,0,4),(1,2,3)]),(24,[]),(42,[])],[],[[0,1],[2,3],[3,2],[0,4,5],[0,1],[1,0],[5,6,7],[3,8,9],[4,6],[3],[10],[3,6],[4,11],[4,6,11],[3,7],[3,4],[3,4],[5,11,8],[7,6,12],[3,4],[3,4]]),
 ([c30,c1,c0,c21,c2,c3,c4],[(0,[]),(69,[]),(14,[(1,0,1)]),(28,[]),(8,[]),(42,[]),(0,[(2,2,3)]),(0,[(0,2,3)]),(34,[]),(14,[(3,0,1)]),(24,[]),(56,[]),(65,[]),(37,[]),(14,[(2,0,1)]),(71,[]),(72,[]),(35,[]),(17,[]),(61,[]),(73,[])],[(9,10)],[[0,1,2],[2,3,4],[2,3,4],[3,1,5],[6,3,7],[2,1],[1000,1,8],[9],[2,10,11],[2,1],[12,8,13],[14],[2,1,15],[2,11,15],[15,1],[2,1,16],[2,10,17],[18,1],[19,1,17],[2,20,11],[2,1]]),
 ([c0,c6,c19,c3,c14,c5,c4],[(8,[]),(0,[(1,0,1)]),(42,[]),(0,[(3,0,1)]),(14,[]),(52,[]),(28,[]),(51,[]),(10,[]),(18,[]),(24,[]),(60,[]),(17,[(1,0,2)])],[],[[0,1,2],[3],[0,4],[0,5],[0,4,6],[5,6,7],[0],[2,6],[2,4],[2,4],[0,7,8],[4,7],[9,10,11],[12,4],[0,6,7],[0],[5,6],[0,6,4],[5,4,6],[0,6,8],[0,4,7]]),
 ([c0,c2,c6,c14,c18,c5,c4],[(8,[]),(14,[]),(28,[]),(0,[(1,0,2)]),(61,[]),(51,[]),(43,[]),(44,[]),(10,[]),(19,[]),(17,[]),(21,[(1,0,1)])],[],[[0,1],[0,2],[0,3,4],[1],[0,1,2],[5,2],[0],[1,6],[1,7],[2,6],[0,8],[1],[9,2],[10,1],[0,5,8],[0],[11,1],[0,2,8],[5,1],[0,2,7],[0,1,5]]),
 ([0x3322332233223322,c0,c2,c6,c3,c5,c4],[(0,[(1,0,2)]),(14,[]),(60,[]),(14,[(2,0,1)]),(14,[(0,0,1)]),(28,[]),(17,[(1,0,2)]),(52,[]),(8,[]),(61,[]),(51,[]),(44,[]),(10,[]),(17,[(2,0,1)])],[],[[0],[1,2],[3,4],[1,0],[5,1,6],[5,2,6],[3,7],[8,5],[3,9,8],[8,3,5],[7,5,10],[8],[9,11],[5,7],[3,12,8],[3,5],[13,3],[8,10,12],[7,5],[3,5],[7,3,10]]),
 ([c0,c6,c14,c16,c5,c4],[(36,[]),(8,[(1,0,1)]),(1,[(1,0,2),(1,1,2)]),(60,[]),(28,[]),(65,[]),(52,[]),(1,[(1,0,1),(1,1,2)]),(14,[]),(15,[]),(51,[]),(10,[(1,0,1)]),(49,[]),(0,[(1,1,2)]),(13,[]),(5,[(1,0,1),(1,0,2)]),(45,[]),(4,[(1,0,2),(1,0,3)]),(24,[]),(10,[]),(8,[])],[(1,3),(4,6),(2,34),(1,33)],[[0,1,2,3,4,5],[6,1,7,0,1000,1001],[8,1001,1],[8,1,9],[6,10,1000,3,4,1002,1003],[8],[8,10,5,1],[8,0,9],[1,0,5,11,10,12],[8,10,13],[8,6,9],[1,14,15,3,0,16],[8,17,18],[1,8,11,19,20],[1,8,9]]),
 ([c0,c6,c3,c14,c5,c26],[(10,[]),(60,[]),(36,[]),(14,[]),(52,[]),(15,[]),(1,[(1,0,1),(1,0,2)]),(7,[]),(51,[]),(49,[]),(0,[]),(0,[(3,1,4)]),(3,[(1,0,2),(1,0,3)]),(13,[]),(24,[])],[(1,3),(8,11),(40,42),(4,6),(9,17),(1,9)],[l1,[0,2,1002,1,3],[0,2,1000,4,1003],[0,3,5],[0,6,7,1000],[3,8,9],[3],[3,2,5],[0,2,10,8,11],[0],[3,12,1004,1005],[0,3,1005],[3,4,5],[0,13,2,14],[0,3,5]]),
 ([c27,c0,c2,c6,c14,c5,c4],[(10,[]),(52,[]),(36,[]),(0,[(2,1,2)]),(0,[(0,1,2)]),(0,[(1,1,2)]),(8,[]),(15,[]),(14,[]),(60,[]),(48,[]),(51,[]),(5,[(1,0,1),(3,2,5)])],[],[[0,1,2],[3,4],[4],[0,5,3],[2,1],[2,0,6],[2,1],[2,1],[1,2],[7,8],[1,9],[3],[7,9],[2,1],[2,10],[7],[2,1],[2,11],[1,2],[12,2,9],[1,8,7]]),
 ([c0,c6,c19,c3,c17,c4],[(10,[]),(0,[(1,0,1)]),(29,[]),(14,[]),(1,[(1,0,1),(1,0,3)]),(51,[]),(25,[]),(21,[]),(52,[]),(18,[]),(60,[]),(8,[]),(11,[])],[(18,26),(3,4),(2,34),(1,9),(4,12)],[[0,1,2],[3],[0,3,1000],[0,3,1001],[0,4,1002],[0],[3,5,1003,6,1000],[3,6,7,8],[0,6,7,5],[3,6,1000,5,1003],[3,9,6,10],[0,5,11],[3,10,12,1004],[0,3,11],[0,3,11]]),
 ([c0,c2,c6,c62,c3,c17,c4],[(14,[(1,0,1)]),(0,[(1,0,1)]),(52,[]),(8,[]),(61,[]),(0,[(3,0,1)]),(28,[]),(60,[(1,0,2)]),(45,[(1,0,3)]),(10,[]),(25,[]),(31,[])],[],[[0,1,2],[3,4],[5],[0,4,3],[3,0,6],[2,4,7],[1],[3],[4,8],[6,2],[0,9,3],[3],[0,8,10],[6,0,2],[3,9],[0,4,11],[11,0,2],[3,4,9],[2,4,6],[0,8,3],[2,0,7]]),
 ([c49,c0,c2,c6,c3,c17,c4],[(0,[(1,0,1)]),(0,[(3,0,1)]),(0,[(0,0,1)]),(14,[]),(51,[]),(61,[]),(28,[]),(1,[(1,0,1),(2,3,5)]),(8,[]),(35,[]),(10,[]),(14,[(2,0,1)]),(25,[]),(60,[])],[],[[0],[1,2],[2],[3,4,5],[6,3,7],[5,4],[8,1],[8,5],[4,5],[7,6],[4,5],[1],[4,9],[6,9],[4,10,8],[11,4,12],[6,5,7],[8,4,10],[13,4,6],[8,10],[8,4,10]]),
 ([c0,c6,c3,c17,c26],[(8,[]),(10,[]),(14,[]),(1,[(1,0,1),(1,0,3)]),(7,[]),(2,[]),(60,[]),(15,[]),(0,[]),(3,[(1,0,2),(1,0,3)]),(11,[])],[(1,3),(32,34),(18,24),(1,9),(16,24),(4,12),(8,24)],[[0,1,1000,1001],[0,1,2,1002],[0,1,2,1001],[0,1,3,4,1000],[2,1003,1004],[2,5,6,7],[1,8,0],[2,9,10,1005],[1,2,1003],[1,2,1006]]),
 ([c49,c1,c6,c19,c3,c5,c4],[(0,[(1,0,1)]),(14,[]),(0,[(1,0,1),(0,0,1)]),(51,[]),(25,[]),(15,[]),(14,[(2,0,1)]),(0,[(3,0,1)]),(60,[]),(24,[]),(68,[]),(48,[]),(36,[]),(8,[])],[],[[0,1],[2],[1,0],[1,3,4],[4,1,5],[4,3],[6],[7,8,9],[4,3],[4,10],[4,3],[7,9],[4,3],[4,8],[4,3],[3,4],[11,4,9],[3,4],[3,12,8],[13,10],[3,8,13]]),
 ([c1,c6,c19,c3,c18,c5,c4],[(14,[]),(0,[(1,0,2)]),(60,[]),(48,[]),(0,[(1,0,1),(1,0,2)]),(43,[]),(15,[]),(65,[]),(19,[]),(10,[]),(0,[(1,0,2),(1,1,5)]),(36,[]),(8,[])],[],[[0],[1,2,3],[0,4],[4,5],[4,0,6],[4,2,5],[1,3],[0,7],[8,2,7],[6,0],[7,9],[0,10,11],[0],[3,0],[3,9],[9],[2,11],[0,9,11],[5,0,6],[12,2],[5,0,2]]),
 ([c1,c0,c6,c3,c39,c5,c4],[(36,[]),(1,[(1,0,1),(1,1,2)]),(15,[]),(8,[(1,0,1)]),(60,[]),(48,[]),(14,[]),(43,[]),(25,[]),(10,[(1,0,1)]),(8,[(2,0,1)])],[],[[0,1],[2],[2,3],[3,4,5],[0,6,2],[0,4,7],[0,4],[1,0,2],[2],[1,6,2],[1,4,8],[2,3,8],[3,5],[0,4],[0,9,3],[10],[4,0],[2,0],[2,0,6],[3,0,9],[2,4,3]]),
 ([c56,c1,c0,c6,c3,c5,c4],[(0,[]),(60,[]),(48,[]),(14,[]),(0,[(2,1,2)]),(0,[(0,1,2)]),(8,[(1,0,1)]),(10,[]),(36,[]),(1,[(2,1,2),(1,0,1)]),(51,[]),(8,[(2,0,1)]),(15,[]),(52,[])],[],[[0,1,2],[2,1,3],[4,2,5],[6],[2,1,3],[2,7],[8,9],[3],[1,10,11],[8,3,12],[8,1,10],[8,1],[1,8],[9,3,12],[9,1,13],[3,10,11],[8,1],[8,10],[1,8],[3,8],[10,1,3]]),
 ([c1,c0,c2,c3,0xff32ff32ff32ff32,c5,c4],[(36,[]),(28,[]),(43,[]),(0,[]),(15,[]),(14,[(2,0,1)]),(15,[(2,0,1)]),(51,[]),(65,[]),(8,[(1,0,1)]),(35,[]),(0,[(3,1,2)]),(10,[(1,0,1)]),(10,[(2,0,1)])],[],[[0,1,2],[1,2],[2,1],[3,1,4],[0,5,6],[0,7],[0,8,9],[5,0],[4,0,5],[2,1],[7,1],[7,8,10],[4,8,11],[0,2],[0,12,8],[13],[2,0],[5,0],[4,0,5],[9,0,12],[2,5,6]]),
 ([0x32003200320032,c1,c0,c2,c3,c5,c4],[(0,[]),(15,[]),(15,[(1,0,1)]),(10,[(1,0,1)]),(14,[]),(8,[]),(36,[]),(65,[]),(43,[]),(15,[(2,0,1)]),(14,[(2,0,1)]),(49,[]),(8,[(2,0,1)]),(44,[]),(28,[])],[],[[0,1],[2],[1,0],[3],[1,4],[5,3],[6,7,8],[9,8],[8,7],[6,10,9],[6,11,7],[6,7,12],[9,6],[8,7],[13,11,14],[13,7],[6,8],[6,11,7],[8,6],[9,6],[7,10,9]]),
 ([c1,c0,c6,c18,c16,c5,c4],[(0,[(1,0,2),(1,1,2)]),(43,[]),(15,[]),(14,[]),(44,[]),(8,[(1,0,1)]),(65,[]),(0,[(1,0,2),(1,1,5)]),(25,[]),(19,[]),(56,[]),(36,[])],[],[[0,1],[2],[0,1],[0,1,2],[0,3,2],[0,4],[5,6],[2],[2,7,4],[1,3,2],[4,8],[9,5,6],[0,2],[2,1,3],[5,4,8],[2,5],[1,3,2],[4,8],[4,1,10],[2,11],[1,3,2]]),
 ([c1,c0,c2,c18,c29,c5,c4],[(0,[(1,0,2),(1,1,2)]),(65,[]),(43,[]),(15,[]),(14,[]),(44,[]),(8,[]),(0,[(1,0,2),(1,1,5)]),(25,[]),(0,[(1,0,2),(3,1,2)]),(10,[(1,0,1)])],[],[[0,1,2],[0,2,3],[0,1,2],[3],[0,4,3],[0,5],[3,1,5],[3],[6,7,8],[2,1],[5,8],[3,1,5],[9],[5,2,8],[1,10],[6,7,8],[2,1],[5,8],[3,1,4],[6,5,10],[1,4,3]]),
 ([c27,c1,c0,c6,c16,c5,c4],[(0,[(1,1,2)]),(15,[]),(8,[(1,0,1)]),(60,[]),(36,[]),(10,[(1,0,1)]),(48,[]),(14,[]),(44,[]),(0,[(2,1,2)]),(24,[])],[],[[0,1],[2,3,4],[1],[1,0],[1,3,4],[2,5],[4,6],[1],[1,3],[1,7],[4,3,8],[4,3],[1,3],[1,7],[6,3],[1,6,9],[1,3,4],[4,8],[6,3,10],[1,4],[1,3,7]]),
 ([c1,c0,c6,c3,c29,c5,c26],[(0,[(1,1,2),(1,1,4)]),(24,[(1,1,3)]),(15,[]),(14,[]),(10,[(1,0,1)]),(36,[]),(46,[]),(44,[]),(60,[]),(37,[]),(49,[]),(0,[(1,1,4),(2,1,2)])],[],[[0,1],[2],[0,1],[2],[0,3,2],[0,1],[4,1,5],[2,5],[4,1,6],[2,1],[7,8,9],[2,10],[2],[2,3],[0,1],[11],[8,1,5],[2,4,5],[2,3],[6,1],[2,1]]),
 ([c27,c1,c0,c6,c3,c5,c26],[(0,[(1,1,4)]),(14,[]),(8,[]),(60,[]),(36,[]),(0,[(1,1,4),(1,1,2)]),(44,[]),(48,[]),(0,[(2,1,2),(1,1,4)]),(15,[]),(25,[]),(49,[])],[],[[0,1],[2,3,4],[1],[5],[4,1,3],[4,0,6],[4,7],[1],[1,8],[4,1,9],[4,3,6],[4,3],[1,4],[7,1],[6,3,10],[1,11],[4,1,3],[4,6],[3,4],[1,4],[6,1]]),
 ([c27,c1,c0,c2,c29,c5,c4],[(0,[(1,1,2)]),(60,[]),(15,[]),(8,[(1,0,1)]),(49,[]),(44,[]),(36,[]),(48,[]),(14,[]),(8,[(2,0,1)]),(25,[]),(0,[(2,1,2),(3,1,2)]),(10,[(2,0,1)])],[],[[0,1,2],[3,1,4],[2,0],[0],[2,1,4],[3,5,6],[6,7],[2,1],[2],[2,8],[6,1,5],[2,1],[9,1,10],[2,8],[5,1,7],[11],[5,1,6],[2,4,7],[2,1,8],[9,5,12],[2,1,8]]),
 ([0x3332333233323332,c1,c0,c2,c3,c5,c4],[(0,[]),(14,[]),(14,[(1,0,1)]),(8,[(1,0,1)]),(8,[(3,0,1)]),(8,[(2,0,1)]),(25,[]),(15,[]),(44,[]),(43,[]),(65,[]),(14,[(2,0,1)]),(15,[(2,0,1)]),(10,[(1,0,1)])],[],[[0,1],[2],[1,3,4],[1,3,5],[6,1,7],[3,8,6],[9,10],[3,8],[3,10,9],[3,11,12],[6,8],[3,10],[3,6],[3,6],[8,6],[6,3,8],[6,9],[3,13],[9,10],[3,13],[3,11,8]]),
 ([c1,c0,0xccfeccfeccfeccfe,c2,c3,c5,c4],[(43,[]),(14,[(1,0,1)]),(65,[]),(14,[(3,0,1)]),(15,[(1,0,1)]),(44,[]),(25,[]),(14,[(2,0,1)]),(10,[(2,0,1)]),(8,[]),(8,[(2,0,1)])],[],[[0,1,2],[1,3],[1,0],[0,2],[4,1],[0,5,6],[7],[1,2,5],[1,6,8],[0,1,2],[5,6],[1,2,8],[1,6,8],[4,0,1],[9,5,8],[5,2],[5,0,6],[1,8,2],[0,2],[1,8,10],[0,1,4]]),
 ([c0,c2,c14,c18,c17,c4],[(8,[]),(14,[]),(0,[(1,0,2)]),(13,[]),(61,[]),(65,[]),(1,[(1,0,2),(1,0,3)]),(44,[]),(65,[(1,0,2)]),(28,[]),(12,[]),(10,[]),(19,[])],[(2,6),(2,34),(1,5)],[[0,1,1000],[0,2,3,4],[1],[0,1,5],[0,6,1001],[1,7,1002,3,1000],[1,8,1000,7,1002],[1,9,10,1000],[0,1,11],[0],[1,3,12,5],[0,7,11],[1,12,5],[0,11],[0,1,11]]),
 ([c0,c2,c3,c14,c37,c17,c4],[(10,[]),(65,[(1,0,2)]),(0,[(1,0,2)]),(14,[(1,0,1)]),(61,[]),(0,[(3,0,2)]),(44,[]),(28,[(1,0,1)]),(13,[]),(33,[]),(53,[]),(8,[])],[],[[0,1],[0,2,3],[0,4],[5],[0,1],[6,7],[6,1],[3,1,8],[3,1,9],[7,6,10],[1,0],[0],[0],[8,1],[3,0,7],[0],[8,1],[8,0,6],[9,1],[11,0],[1,0]]),
 ([c1,c2,c19,c14,c18,c5,c4],[(0,[(1,0,1),(1,0,2)]),(14,[]),(65,[]),(50,[]),(51,[]),(15,[]),(0,[(1,0,2),(2,0,1)]),(53,[]),(52,[]),(10,[]),(13,[]),(0,[(1,0,2),(1,1,5)]),(36,[])],[],[[0,1],[0,2,3],[1],[0,2,4],[0,1,5],[0,4],[6],[1,2,7],[1,2,8],[3,8],[1,9,2],[10,11,12],[1],[3,1,2],[4,7],[0,4],[5,1],[7,4],[4,1],[8,7,9],[2,1,4]]),
 ([c1,c0,c2,c14,c39,c5,c4],[(36,[]),(65,[]),(1,[(1,0,2),(1,1,2)]),(14,[]),(10,[(1,0,1)]),(51,[]),(15,[]),(25,[]),(53,[]),(10,[(3,0,1)]),(52,[]),(8,[])],[],[[0,1,2],[3,4],[3],[4,1,5],[0,3,6],[0,5],[0,1,2],[2,0,7],[3],[2,1],[2,7],[3,1,8],[9],[0,10],[0,4,1],[4,5],[6,0,3],[8,0],[5,0,3],[11,0,4],[1,3,4]]),
 ([c63,c1,c0,c2,c18,c5,c4],[(0,[(1,0,2)]),(14,[]),(10,[]),(36,[]),(25,[]),(0,[(1,0,2),(1,1,2)]),(0,[(3,1,2)]),(10,[(0,0,1)]),(15,[]),(8,[]),(28,[]),(43,[]),(51,[]),(53,[]),(10,[(3,0,1)]),(8,[(3,0,1)])],[],[[0,1],[2,3,4],[5],[6,0,7],[8,1],[9,2],[3,10,11],[1,11],[6,10,11],[3,1,8],[3,12],[1,13,14],[1],[8,1],[12,4],[1,13,14],[3,11],[1,14,15],[8,1],[15,3,14],[8,1]]),
 ([c70,c1,c0,c2,c14,c5,c4],[(0,[]),(51,[]),(36,[]),(15,[]),(8,[(1,0,1)]),(0,[(3,1,2)]),(0,[(0,1,2)]),(14,[]),(10,[]),(28,[]),(1,[(3,1,2),(1,0,2)]),(44,[]),(8,[(3,0,1)]),(52,[]),(10,[(3,0,1)])],[],[[0,1],[1,2,3],[4],[5,1,6],[1,2,7],[4,2,8],[2,9,10],[3,11,12],[3],[2,7,3],[2,1],[2,13],[10,2,13],[3,7],[1,9],[3,11,12],[2,13],[1,14,12],[3,2,7],[12,1,14],[1,7]]),
 ([c1,c0,c2,0xf3f2f3f2f3f2f3f2,c3,c5,c4],[(52,[]),(28,[]),(43,[]),(14,[(2,0,1)]),(15,[(2,0,1)]),(44,[]),(25,[]),(8,[(1,0,1)]),(8,[(3,0,1)]),(10,[(1,0,1)])],[],[[0,1,2],[1,2],[1,2],[2,1],[0,3,4],[2,5,6],[3,0],[3,0],[0,6,7],[2,1],[0,1,5],[8],[5,7,6],[1,0],[1,9,7],[3,7,6],[1,0],[1,5],[0,1],[3,1],[0,3,4]]),
 ([0x3322332233223322,c1,c0,c2,c16,c5,c4],[(0,[(1,1,2)]),(15,[]),(0,[(1,1,2),(1,0,2)]),(8,[(1,0,1)]),(65,[]),(14,[]),(10,[(1,0,1)]),(0,[(3,0,2),(1,1,2)]),(1,[(1,0,2),(1,1,2)]),(15,[(2,0,1)]),(14,[(2,0,1)]),(51,[]),(25,[]),(0,[(3,0,2),(3,1,2)]),(52,[]),(61,[])],[],[[0,1],[2],[1,3,4],[1,0],[1,5],[3,6],[7,4,8],[3,9],[3,4,9],[3,10,9],[4,11,7],[3,4],[3,12],[3,4],[8,12],[13],[12,14],[3,6],[11,4,15],[3,6],[3,6]]),
 ([c1,c0,0xcfcecfcecfcecfce,c2,c3,c5,c4],[(43,[]),(15,[(1,0,1)]),(28,[]),(14,[(1,0,1)]),(51,[]),(25,[]),(15,[(2,0,1)]),(65,[]),(10,[(3,0,1)]),(8,[])],[],[[0,1,2],[0,1],[1,0],[0,2],[1,3],[0,4,5],[6],[1,7,8],[1,5,4],[0,2],[4,2],[1,7,8],[1,4,8],[0,2],[9,2,8],[4,7,8],[2,0],[1,8,7],[0,2],[1,2],[0,3,1]]),
 ([c30,c1,c0,c2,c3,c4,c45],[(0,[]),(68,[]),(15,[(1,0,2)]),(0,[(2,1,3)]),(52,[]),(0,[(0,1,3)]),(25,[]),(10,[]),(24,[]),(49,[]),(17,[]),(56,[]),(15,[(2,0,2)])],[],[[0,1,2],[2,1],[3,4,5],[4,1,6],[2,7,4],[2,7,4],[4,8],[2,1],[2,8,9],[10,1],[10],[2,1],[2,9],[4,1],[4,1],[10,1,9],[2,9,10],[2,8,11],[2,1,11],[2,1,11],[12]]),
 ([c1,c0,c2,c3,0xff54ff54ff54ff54,c5,c4],[(52,[]),(28,[]),(15,[(3,0,1)]),(44,[]),(10,[(1,0,1)]),(14,[(3,0,1)]),(25,[]),(8,[(1,0,1)]),(10,[(2,0,1)])],[],[[0,1,2],[1,3,4],[2,1],[2,1],[0,5,2],[6,3],[2,0],[0,6,4],[2,0],[2,1,4],[0,1,3],[3,4,6],[2,4,3],[1,0],[1,4,7],[8],[0,1],[2,1],[2,0,5],[3,1],[0,4]]),
 ([0x5454545454545454,c1,c2,c3,c18,c5,c4],[(15,[(1,0,1)]),(0,[(1,0,2),(1,0,1)]),(0,[(1,0,2),(2,0,1)]),(0,[(1,0,2),(1,1,5)]),(49,[]),(15,[(3,0,1)]),(15,[(0,0,1)]),(25,[]),(14,[]),(8,[]),(44,[]),(50,[]),(14,[(3,0,1)]),(37,[]),(52,[]),(10,[])],[],[[0],[0,1,2],[0,3,4],[5,6],[0,7,8],[9,4],[1,10],[1,11,5],[1,11,5],[1,12,5],[1,10],[7,13,10],[5,13,10],[7,14],[5,15,9],[9],[14,11],[5,13],[5,7,12],[9,7,10],[5,12]]),
 ([0x5544554455445544,c1,c2,c19,c3,c5,c4],[(14,[(1,0,1)]),(0,[(1,0,1),(1,2,5)]),(52,[]),(14,[(3,0,1)]),(14,[(0,0,1)]),(0,[(1,0,1),(1,0,2)]),(0,[(1,0,1),(2,0,2)]),(15,[]),(10,[]),(43,[]),(51,[]),(15,[(3,0,1)]),(37,[]),(53,[]),(25,[]),(8,[])],[],[[0],[0,1,2],[3,4],[0,5,6],[7,0],[2,8],[3,9],[5,9,3],[3,10,5],[2,3,11],[5,10],[8],[10,12,13],[13,2,14],[3,8,15],[3,14,10],[11,2,3],[10,8,12],[2,12],[3,8,12],[2,3,8]]),
 ([c1,c19,c3,c18,c5,c26],[(10,[]),(43,[]),(50,[]),(15,[]),(14,[]),(0,[(1,0,1),(1,0,2)]),(6,[]),(25,[]),(49,[]),(18,[]),(1,[]),(8,[]),(3,[(1,0,1),(1,0,3)]),(37,[]),(44,[]),(19,[])],[(2,3),(8,9),(4,5),(8,24)],[l1,[0,2,1001,1,3],[0,2,1000,1,1002],[0,3,4],[0,5,6,1000],[3,7,8,9],[3],[3,1,4],[0,9,10,7,11],[0],[3,12,1003],[0,3,13],[3,2,4],[0,14,15,7,13],[0,3,4]]),
 ([c1,c0,c19,c3,c39,c5,c26],[(43,[]),(28,[]),(10,[(1,0,1)]),(50,[]),(57,[]),(14,[]),(25,[]),(49,[]),(10,[(2,0,1)]),(15,[])],[],[[0,1],[2,0,3],[0,1],[2,0,4],[2,5,4],[3,0],[5],[2,6],[5],[0,1],[4,1],[5,7],[5],[3,0],[4,1],[8],[0,1],[4,1],[9,0,5],[4,1],[3,0]]),
 ([0x5554555455545554,c1,c0,c2,c3,c5,c4],[(15,[(1,0,1)]),(0,[]),(10,[(1,0,1)]),(10,[(3,0,1)]),(10,[(2,0,1)]),(14,[]),(8,[]),(52,[]),(24,[]),(14,[(3,0,1)]),(15,[(3,0,1)]),(25,[]),(44,[]),(8,[(1,0,1)]),(37,[])],[],[[0],[1,0],[0,2,3],[0,2,4],[0,5],[6,2],[7,8],[2,8],[2,8],[2,9,10],[11,8],[2,7,9],[2,11],[2,8,10],[7,11,12],[11,2,12],[11,7],[9,2,13],[7,8,14],[9,2,13],[7,2]]),
 ([c1,0xaafeaafeaafeaafe,c0,c2,c3,c5,c4],[(14,[(3,0,1)]),(52,[]),(14,[(1,0,1)]),(43,[]),(24,[]),(8,[(2,0,1)]),(15,[(1,0,1)]),(37,[]),(14,[(2,0,1)]),(36,[]),(44,[]),(10,[(2,0,1)])],[],[[0],[1,2,3],[2,3],[2,4,5],[1,2,6],[3,4,7],[0,1,8],[0,4,5],[0,4,5],[6,0],[5,4,7],[2,1],[1,9],[3,2,6],[1,7,10],[10,7],[9,1],[2,11,5],[1,4,7],[2,7],[1,2,6]]),
 ([c1,c0,c2,0xf5f4f5f4f5f4f5f4,c3,c5,c4],[(52,[]),(34,[]),(14,[(3,0,1)]),(43,[]),(51,[]),(8,[(1,0,1)]),(15,[(3,0,1)]),(37,[]),(0,[(1,0,2),(1,1,5)]),(8,[(3,0,1)]),(19,[]),(25,[]),(10,[(1,0,1)])],[],[[0,1],[2,3],[2,3],[2,4,5],[0,2,6],[3,1,7],[1,0],[1,0],[0,8,4],[1,2],[0,7,4],[9],[4,5,10],[11,0],[1,12,5],[2,5,4],[6,0,2],[1,7],[0,7],[1,7],[0,2,1]]),
 ([0x5544554455445544,c1,c0,c2,c16,c5,c4],[(15,[(1,0,1)]),(0,[(1,1,2)]),(0,[(1,1,2),(1,0,5)]),(19,[]),(14,[]),(10,[(1,0,1)]),(8,[(1,0,1)]),(34,[]),(0,[(1,0,2),(1,1,2)]),(43,[]),(14,[(3,0,1)]),(15,[(3,0,1)]),(37,[]),(0,[(1,0,2),(1,1,5)]),(25,[]),(51,[]),(24,[])],[],[[0],[1,0],[0,2,3],[0,2,3],[0,4],[3,5,6],[3,7,8],[5,9,10],[5,9,10],[5,10,11],[8,7],[3,12],[3,13,7],[3,10,7],[3,12],[3],[14,9],[6,5],[15,9,16],[6,5],[6,5]]),
 ([c1,0xafaeafaeafaeafae,c0,c2,c3,c5,c4],[(14,[(3,0,1)]),(19,[]),(14,[(1,0,1)]),(52,[]),(24,[]),(8,[(3,0,1)]),(15,[(1,0,1)]),(25,[]),(10,[]),(35,[]),(10,[(3,0,1)]),(51,[])],[],[[0],[1,2,3],[2,4,5],[1,4,5],[3,2,6],[7,4],[0,2,3],[0,4,5],[0,4,5],[3,0,6],[5,4,8],[1,3,2],[2,7,5],[1,2,6],[1,7],[1,9,7],[7,3],[2,10,5],[1,4,11],[1,10,5],[3,2,6]]),
 ([c30,c1,c0,c2,c3,c4,c73],[(0,[(1,0,4)]),(68,[]),(14,[(1,1,2)]),(0,[(1,0,4),(2,1,3)]),(19,[]),(0,[(1,0,4),(0,1,3)]),(25,[]),(10,[]),(8,[]),(43,[]),(28,[]),(49,[]),(17,[]),(21,[(1,1,2)]),(14,[(2,1,2)])],[],[[0,1,2],[2,1],[3,4,5],[4,1,6],[2,7,8],[2,6,8],[9,10],[2,1],[2,10],[9,1],[9,1],[2,1],[2,11],[12,1],[12],[12,1,11],[2,11,12],[2,11,13],[2,1,10],[2,1,13],[14]]),
 ([c1,0xaaaafffaaaaafffa,c0,c2,c3,c4],[(14,[]),(40,[]),(52,[]),(69,[]),(24,[]),(37,[]),(35,[]),(68,[]),(46,[]),(10,[]),(3,[(1,0,2)]),(56,[]),(3,[(3,0,2)]),(2,[(1,0,1)]),(25,[]),(8,[]),(44,[]),(11,[]),(0,[(1,1,2),(3,3,5)]),(12,[]),(70,[])],[(4,5),(1,3),(4,6),(1,9),(8,9),(1,33),(2,34),(10,24),(2,24),(20,32),(1,5),(24,32)],[[0],[1,2,1000,3,4,1001,1002],[0,4,1000,5],[0,4,1003,6,1004],[1,5,1000,7,4,1005,1006],[6,8,9,5,4,1001,1007],[0,3,10,11,12],[0,1,13,11,14],[2,8,15,9,3],[0,3,1002,16],[0,11,1008,1,1003],[2,16,1001,7,3,1006,1005],[0,17,18,19],[0,20,1009,11,1010],[0,7,1011,1,1003]]),
 ([c30,0x8888888888888888,c1,c0,c2,c3,c4],[(0,[]),(14,[]),(40,[]),(14,[(0,0,1)]),(25,[]),(8,[]),(43,[]),(10,[]),(14,[(2,0,1)]),(14,[(3,0,1)]),(37,[]),(17,[]),(52,[]),(50,[]),(71,[]),(56,[]),(3,[(2,0,4),(0,1,2)]),(73,[])],[(9,10)],[[0,1],[0,2,3],[3,4,5],[4,6],[6,2,4],[3,7,5],[8],[9],[1,10],[1,2],[10,11],[1000,12,2],[3,2],[3,13],[2,14,10],[3,10,12],[2,15],[12,10,14],[16,2,10],[3,17,15],[2,10,3]]),
 ([c30,0x2222222222222222,c1,c0,c2,c3,c4],[(0,[]),(14,[]),(69,[]),(14,[(2,0,1)]),(37,[]),(8,[]),(0,[(2,1,3)]),(3,[(3,1,2)]),(3,[(2,0,4),(0,1,2)]),(3,[(2,0,4),(1,1,2)]),(71,[]),(56,[]),(52,[]),(3,[(2,0,4),(3,1,2)]),(73,[])],[(0,3)],[[0,1],[0,2,3],[3,4,5],[6,2,7],[7,4],[3,2],[8],[9],[1,10,2],[1,10,11],[2,10],[12,2,1000],[3,10,4],[3,2],[4,10],[3,2,10],[3,11,10],[10,2],[13,2],[3,14,11],[3,2]]),
 ([c30,0x4444444444444444,c1,c0,c2,c3,c4],[(8,[]),(37,[]),(40,[]),(14,[(3,0,1)]),(0,[(2,1,3)]),(3,[(2,1,2)]),(0,[(0,1,3)]),(10,[]),(3,[(2,0,4),(1,1,2)]),(3,[(2,0,4),(0,1,2)]),(24,[]),(56,[]),(71,[]),(3,[(2,0,4),(2,1,2)]),(73,[])],[(0,3)],[[0,1],[0,2,3],[0,1],[4,5,6],[5,1],[0,7],[8],[9],[3,1,10],[2,11],[10,1],[2,10,1000],[1,2,3],[3,10,11],[1,10],[3,1,12],[2,11],[12,1],[13,1],[3,14,11],[2,1,3]]),
 ([0xaaaaaaaa,c30,c1,c0,c2,c3,c4],[(0,[]),(14,[]),(3,[(2,0,4),(0,2,3)]),(52,[]),(74,[]),(37,[]),(56,[]),(3,[(2,0,4),(1,2,3)]),(68,[]),(14,[(2,0,2)]),(0,[(0,1,3)]),(10,[]),(17,[]),(35,[]),(73,[])],[],[[0,1],[2],[3,4],[1,4,5],[1,4,6],[7],[0,8,9],[4,5,8],[4,3,10],[3,5],[3,11],[3,4],[5,4],[6,4],[5,8,12],[9,3],[3,6,13],[3,5,8],[12,5],[4,14],[4,5,8]]),
 ([0xcccccccc,c30,c1,c0,c2,c3,c4],[(14,[]),(65,[]),(10,[]),(68,[]),(14,[(0,1,2)]),(73,[]),(56,[]),(14,[(1,1,2)]),(14,[(2,1,2)]),(3,[(2,1,3)]),(0,[(2,0,4),(0,1,3)]),(43,[]),(35,[]),(17,[])],[],[[0,1,2],[3,1],[4],[0,1,5],[0,6,3],[7],[2,3,8],[2,1],[6,9,10],[6,1,3],[1,2],[11,1],[5,3,8],[6,1,8],[1,3],[5,1],[8,6,12],[13,3],[13,1],[1,5],[6,3]])]
def d350 : List StD := dupD [
 ([c6,c19,c3,c37,c5,c4],[(0,[(1,0,2)]),(0,[(1,0,2),(1,0,1)]),(0,[(1,0,2),(2,0,1)]),(14,[(1,0,1)]),(37,[]),(14,[(3,0,1)]),(17,[(1,1,2),(1,0,1)]),(10,[]),(0,[(1,0,2),(1,1,5)]),(49,[(1,0,2)]),(14,[(2,0,1)]),(17,[(1,0,2),(1,0,1)]),(3,[(1,0,2),(1,0,1),(1,1,2)]),(17,[(1,0,2),(1,1,2)]),(43,[])],[],[[0,1,2],[3,4],[3,5],[6,3],[6,7],[3,8,9],[3,10],[11,3],[11,4,7],[7],[12,4],[3,4],[13,3],[13,4,7],[14,3,7]]),
 ([c21,c6,c3,c39,c5,c4],[(14,[]),(0,[(1,0,1),(1,2,5)]),(14,[(3,0,1)]),(0,[(1,0,2),(1,1,5)]),(10,[(1,0,1)]),(17,[(1,0,2),(1,1,2)]),(37,[]),(68,[]),(17,[(1,0,1),(1,1,2)]),(10,[(3,0,1)]),(14,[(1,0,1)]),(10,[(2,0,1)]),(68,[(1,0,1)]),(3,[(1,1,2),(1,0,2),(1,0,1)]),(17,[(1,0,1),(1,0,2)]),(43,[])],[],[[0,1,2],[0,3,4],[0,1],[4,0,5],[5,6,7],[8,4,6],[1,9],[8,10],[8,4],[11],[12,6,13],[10,4,6],[14,6,10],[14,4],[15,4]]),
 ([c56,c21,c6,c3,c5,c4],[(0,[(2,0,2)]),(17,[(1,0,2),(1,1,3)]),(14,[]),(0,[(0,0,2)]),(0,[(2,1,2)]),(10,[]),(0,[(0,1,2)]),(10,[(1,0,1)]),(17,[(1,0,1),(1,0,2)]),(14,[(1,0,1)]),(14,[(3,0,1)]),(49,[(1,0,2)]),(10,[(2,0,1)]),(17,[(1,1,2),(1,0,2)]),(49,[(1,0,1)]),(17,[(1,1,2),(1,0,1)]),(43,[]),(37,[])],[],[[0,1,2,3],[4,5,6],[7],[8,9],[8,5],[2,9,10],[2,11],[12,2,13],[13,11],[9,14],[15,9],[15,12],[16,17],[9,12,17],[16,9,12]]),
 ([c21,c6,c18,c16,c5,c4],[(14,[]),(14,[(1,0,1)]),(14,[(3,0,1)]),(0,[(1,1,2)]),(0,[(1,0,2),(1,1,5)]),(43,[]),(17,[(1,0,2)]),(49,[(1,0,2)]),(19,[]),(49,[(1,0,1)]),(17,[(1,0,1)]),(10,[]),(37,[]),(35,[]),(10,[(1,0,1)]),(44,[]),(56,[])],[],[[0,1,2],[0,1,3],[0,4,5],[6,0],[5,7],[8,1,9],[1,9],[10,1],[10,9],[1,4,11],[5,1,12],[13,12,14],[15,5,16],[1,11,12],[5,1,14]]),
 ([c0,c6,c37,c16,c5,c4],[(10,[(1,0,1)]),(37,[]),(0,[(1,1,2),(3,0,2)]),(0,[(1,0,2),(1,1,5)]),(56,[]),(44,[]),(14,[]),(14,[(3,0,1)]),(17,[(1,0,1)]),(14,[(1,0,1)]),(17,[(1,0,2)])],[],[[0,1],[2],[0,3,4],[0,1],[5,1],[6,0,7],[0,5],[8,9],[8,0],[0,4],[10,1,6],[10,0],[5,1,4],[4,0],[5,0,9]]),
 ([c1,c0,0xf000f000feeefeee,c2,c3,c5],[(19,[(2,0,3)]),(17,[(1,0,1)]),(65,[]),(56,[]),(44,[]),(61,[]),(10,[(0,0,1)])],[],[[0,1,2],[0,1],[3,4],[0,2],[1,5],[0,1,5],[0,2],[1,3,6],[0,2],[5,2,6],[0,3,6],[1,2,5],[0,2],[1,3],[0,2]]),
 ([c22,c0,c2,0xfaaafaaafaaafaaa,c3,c5],[(0,[(0,1,2),(2,0,4)]),(0,[(0,1,2),(0,0,4)]),(10,[(0,0,1)]),(48,[]),(17,[(1,0,1)]),(28,[]),(14,[]),(53,[]),(61,[]),(24,[]),(19,[(2,0,3)])],[(6,10)],[[0,1],[2,3],[2,4],[2,5,4],[2,6,4],[2,7],[2,3,5],[2,8],[2,5],[0,3],[0,1000,8,3],[3,9],[0,4],[4,8],[10,5]]),
 ([c22,c1,c2,0xfcccfcccfcccfccc,c3,c5],[(17,[]),(17,[(1,0,1)]),(17,[(3,0,1)]),(14,[]),(56,[]),(10,[(0,0,1)]),(44,[]),(19,[(2,0,3)]),(65,[]),(61,[])],[],[[0,1,2],[3,4,5],[0,1,5],[0,4,5],[0,3],[4,6],[5,1,7],[1,8],[1,9],[5,4],[1,8],[1,4],[1,4,5],[1,8,7],[7,4,8]]),
 ([c22,c1,c0,c2,c3,0xfffff000fffff000],[(17,[]),(17,[(1,0,1)]),(17,[(3,0,1)]),(17,[(2,0,1)]),(61,[]),(56,[]),(33,[]),(28,[]),(19,[(2,0,3)]),(44,[]),(71,[])],[(6,10)],[[0,1,2],[0,1,3],[4,5,6],[0,5,7],[0,4],[8,1,4],[4,9,5],[1,7],[1,4],[6,5],[1,4,10],[1,7,6],[1,1000,4],[1,5],[6,4,7]]),
 ([c22,c30,c1,c0,c2,c3],[(61,[]),(65,[]),(10,[]),(17,[]),(19,[(2,1,2)]),(49,[]),(56,[]),(28,[]),(68,[]),(19,[(2,0,3)]),(75,[]),(24,[]),(71,[])],[],[[0,1,2],[3,1,4],[3,0],[0,1,5],[3,6,7],[0,8],[2,1],[6,9,7],[0,1,8],[10,0,11],[0,8],[6,1,11],[12,1],[12,0],[0,1,8]]),
 ([0xf000f0eefeeefe,c1,c0,c2,c3,c5],[(0,[]),(19,[(1,0,1)]),(19,[(3,0,1)]),(61,[]),(56,[]),(10,[]),(10,[(2,0,1)]),(17,[]),(43,[]),(28,[]),(69,[]),(48,[])],[],[[0,1,2],[1,3],[1,4,5],[1,4,6],[7,3],[8,3],[3,8],[4,9,8],[6,3,10],[6,4],[6,3],[6,9],[3,10,11],[9,4,8],[8,3,9]]),
 ([0xf0f0eeeefefe,c1,c0,c2,c3,c5],[(0,[]),(71,[]),(28,[]),(10,[]),(17,[]),(40,[]),(10,[(2,0,2)]),(61,[]),(56,[]),(48,[])],[],[[0,1],[1,2],[2,3],[4,2],[3,1],[5,2],[2,1,5],[6,1],[5,7],[1,8],[1,7],[6,2],[7,5],[2,1,9],[5,1]]),
 ([c6,c19,c14,c18,c5,c4],[(0,[(1,0,2)]),(0,[(1,0,2),(1,0,1)]),(0,[(1,0,2),(2,0,1)]),(61,[]),(28,[]),(17,[(1,1,2)]),(19,[]),(56,[]),(10,[]),(18,[]),(17,[(1,0,2)]),(68,[(1,0,2)]),(49,[(1,0,2)]),(71,[]),(68,[(1,1,2)]),(44,[])],[],[[0,1,2],[3,4,5],[6,4],[5,7],[5,8],[9,3],[10,11,12],[10,4,13],[10,4,8],[1,8],[14,3],[7,4,8],[11,4,13],[15,4],[15,8,13]]),
 ([c0,c6,c14,c39,c5,c4],[(10,[(1,0,1)]),(0,[(1,0,1),(1,2,5)]),(56,[]),(14,[]),(68,[(1,0,2)]),(71,[(1,0,1)]),(28,[]),(17,[(1,1,2)]),(17,[(1,0,2)]),(44,[])],[],[[0,1,2],[0,2],[3],[0,3,4],[5,4,6],[3],[0,5],[7,2],[2,0],[0,5],[4,2],[2,0],[8,3],[8,0],[9,0,3]]),
 ([0x3322332233223322,c0,c6,c16,c5,c4],[(0,[(1,1,2),(1,0,2)]),(17,[(2,0,1)]),(17,[(1,0,2)]),(14,[(0,0,1)]),(10,[(1,0,1)]),(28,[]),(56,[]),(44,[]),(14,[(2,0,1)])],[],[[0],[1,2,3],[3,0],[2,3],[2,4],[4,5],[4,6],[4,5],[7,5],[1,4],[1,8],[1,4],[7,5,6],[6,4],[7,4,8]]),
 ([c27,c0,c6,c14,c5,c26],[(10,[]),(48,[]),(49,[(1,0,2)]),(0,[(1,1,4),(0,1,2)]),(0,[(1,1,4),(1,1,2)]),(0,[(1,1,4),(2,1,2)]),(14,[]),(43,[]),(10,[(2,0,1)]),(28,[]),(52,[]),(44,[]),(69,[(1,1,2)]),(46,[])],[],[[0,1,2],[3],[0,4,5],[2,6,7],[5,1],[8,1,9],[7,1,10],[1,6],[11,2,9],[6],[12,6],[5,1],[10,2],[13,1],[1,2,6]]),
 ([c49,c6,c19,c3,c17,c4],[(0,[(1,0,1),(0,0,1)]),(0,[(3,0,1)]),(14,[]),(71,[]),(56,[]),(28,[]),(43,[]),(52,[]),(10,[]),(14,[(2,0,1)]),(69,[]),(51,[]),(46,[]),(48,[])],[],[[0],[1,0],[2,3,4],[5,2,6],[7,3,8],[1,3],[9,3,10],[5,4,6],[4,3,8],[9,4,11],[12,3],[11,8,13],[6,3,5],[4,8],[6,3,8]]),
 ([0x8888fff88888fff8,c1,c0,c2,c3,c4],[(0,[]),(14,[]),(10,[]),(43,[]),(28,[]),(69,[]),(14,[(0,0,1)]),(71,[]),(46,[]),(56,[]),(19,[(2,1,2)]),(73,[])],[],[[0,1],[2,1],[1,3],[1,4],[3,2],[3,5],[6,3],[3,5],[3,7,8],[6,5,7],[6,9,7],[7,5],[10,5],[6,11,9],[6,5]]),
 ([c30,c1,c0,0xf8f8f8f8f8f8f8f8,c3,c4],[(0,[]),(68,[]),(14,[(0,0,1)]),(69,[]),(0,[(2,2,3)]),(56,[]),(10,[]),(43,[]),(46,[]),(71,[]),(52,[]),(73,[])],[(9,10)],[[0,1,2],[2,1],[2,3],[4,1,5],[2,6,7],[2,1000,8,7],[2,1],[2,9,5],[7,1],[2,1],[2,5,9],[9,1,10],[2,1,3],[5,11],[2,1,5]]),
 ([c30,c1,c0,c2,0xff88ff88ff88ff88,c4],[(0,[]),(69,[]),(14,[(0,0,1)]),(28,[]),(10,[]),(56,[]),(0,[(0,2,3)]),(43,[]),(71,[]),(46,[]),(19,[(2,1,2)]),(73,[])],[],[[0,1,2],[2,3,4],[3,1,5],[2,3,6],[2,1],[2,1,7],[2,7],[2,1],[7,8,9],[2,1,8],[2,8],[8,1],[2,1,10],[2,11,5],[5,1,9]]),
 ([c30,c1,c0,c2,c3,0xffffffff88888888],[(0,[]),(68,[]),(57,[]),(10,[]),(46,[]),(0,[(2,1,3)]),(19,[]),(0,[(0,1,3)]),(56,[]),(69,[]),(71,[]),(19,[(2,1,2)]),(73,[])],[(9,10)],[[0,1,2],[3,1,4],[5,6,7],[6,1,8],[2,3,9],[2,1000,4],[2,1],[2,10,8],[4,1,10],[4,1],[4,8,10],[2,1,9],[11,1,12],[2,12,8],[2,1,8]]),
 ([0x2222fff22222fff2,c1,c0,c2,c3,c4],[(0,[]),(69,[]),(14,[]),(14,[(1,0,1)]),(46,[]),(19,[(2,0,1)]),(73,[]),(40,[]),(14,[(2,0,1)]),(71,[]),(56,[]),(44,[])],[],[[0,1,2],[2,3,4],[2,1,5],[2,6],[4,1],[4,1,7],[6,7,8],[8,1],[4,9],[4,1,6],[4,10,7],[9,1],[11,1],[4,6,10],[4,1]]),
 ([0xfff0aaaafffa,c1,c0,c2,c3,c4],[(0,[]),(14,[]),(46,[]),(68,[]),(69,[]),(56,[]),(40,[]),(14,[(2,0,2)]),(52,[]),(48,[]),(73,[])],[],[[0,1],[2,3],[1,4,5],[1,3,5],[1,4,2],[2,4,6],[5,3,7],[5,4,7],[2,3,6],[2,3],[2,5,6],[8,3],[9,3,4],[2,10,5],[2,3,4]])]
def d351 : List StD := []
lemma d352 : LevelN d265 d264 4 d351 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d353 : levelOK d264 d344 4 (d351.map Prod.fst) ((d350.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d354 : levelOK d264 d344 4 (d351.map Prod.fst) ((d350.drop (1*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d355 : levelOK d264 d344 4 (d351.map Prod.fst) ((d350.drop (2*8)).take 8) = true := by decide +kernel
lemma d356 : LevelN d265 d264 5 d350 := levelStep d267 d345 d352 (chunks 8 d350 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d353
  · exact d354
  · exact d355
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d357 : levelOK d264 d344 5 (d350.map Prod.fst) ((d349.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d358 : levelOK d264 d344 5 (d350.map Prod.fst) ((d349.drop (1*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d359 : levelOK d264 d344 5 (d350.map Prod.fst) ((d349.drop (2*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d360 : levelOK d264 d344 5 (d350.map Prod.fst) ((d349.drop (3*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d361 : levelOK d264 d344 5 (d350.map Prod.fst) ((d349.drop (4*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d362 : levelOK d264 d344 5 (d350.map Prod.fst) ((d349.drop (5*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d363 : levelOK d264 d344 5 (d350.map Prod.fst) ((d349.drop (6*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d364 : levelOK d264 d344 5 (d350.map Prod.fst) ((d349.drop (7*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d365 : levelOK d264 d344 5 (d350.map Prod.fst) ((d349.drop (8*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d366 : levelOK d264 d344 5 (d350.map Prod.fst) ((d349.drop (9*8)).take 8) = true := by decide +kernel
lemma d367 : LevelN d265 d264 6 d349 := levelStep d267 d345 d356 (chunks 8 d349 10 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d357
  · exact d358
  · exact d359
  · exact d360
  · exact d361
  · exact d362
  · exact d363
  · exact d364
  · exact d365
  · exact d366
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d368 : levelOK d264 d344 6 (d349.map Prod.fst) ((d348.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d369 : levelOK d264 d344 6 (d349.map Prod.fst) ((d348.drop (1*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d370 : levelOK d264 d344 6 (d349.map Prod.fst) ((d348.drop (2*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d371 : levelOK d264 d344 6 (d349.map Prod.fst) ((d348.drop (3*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d372 : levelOK d264 d344 6 (d349.map Prod.fst) ((d348.drop (4*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d373 : levelOK d264 d344 6 (d349.map Prod.fst) ((d348.drop (5*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d374 : levelOK d264 d344 6 (d349.map Prod.fst) ((d348.drop (6*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d375 : levelOK d264 d344 6 (d349.map Prod.fst) ((d348.drop (7*8)).take 8) = true := by decide +kernel
lemma d376 : LevelN d265 d264 7 d348 := levelStep d267 d345 d367 (chunks 8 d348 8 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d368
  · exact d369
  · exact d370
  · exact d371
  · exact d372
  · exact d373
  · exact d374
  · exact d375
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d377 : levelOK d264 d344 7 (d348.map Prod.fst) ((d347.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d378 : levelOK d264 d344 7 (d348.map Prod.fst) ((d347.drop (1*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d379 : levelOK d264 d344 7 (d348.map Prod.fst) ((d347.drop (2*8)).take 8) = true := by decide +kernel
lemma d380 : LevelN d265 d264 8 d347 := levelStep d267 d345 d376 (chunks 8 d347 3 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d377
  · exact d378
  · exact d379
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d381 : levelOK d264 d344 8 (d347.map Prod.fst) ((d346.drop (0*8)).take 8) = true := by decide +kernel
lemma d382 : LevelN d265 d264 9 d346 := levelStep d267 d345 d380 (chunks 8 d346 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d381
  ))
lemma d383 : LowN d265 d264 10 := lowSearch d267 d382 (by decide +kernel)
def d384 : Nat := 0xfeeefac0feeefac0feeefac0feeefac0
def d385 : List Nat := l0
def d386 : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9),(4,1,17)]
lemma d387 : baseOK d384 d385 d386 = true := by decide +kernel
lemma d388 : SliceN d385 d384 (c28,4,[1, 2, 3, 4]) := mkSlice (w:=0) d387 d23 d37 (by decide +kernel)
lemma d389 : SliceN d385 d384 (c24,4,[0, 3, 2, 4]) := mkSlice (w:=0) d387 d23 d37 (by decide +kernel)
lemma d390 : SliceN d385 d384 (c25,4,[0, 4, 1, 3]) := mkSlice (w:=0) d387 d23 d37 (by decide +kernel)
lemma d391 : SliceN d385 d384 (c23,4,[1, 4, 0, 2]) := mkSlice (w:=0) d387 d23 d37 (by decide +kernel)
lemma d392 : SliceN d385 d384 (c31,4,[2, 3, 0, 1]) := mkSlice (w:=0) d387 d23 d37 (by decide +kernel)
lemma d393 : SliceN d385 d384 (c11,3,[3, 4, 1, 2]) := mkSlice (w:=1) d387 d103 d104 (by decide +kernel)
lemma d394 : SliceN d385 d384 (c12,3,[2, 4, 3, 0]) := mkSlice (w:=2) d387 d103 d104 (by decide +kernel)
lemma d395 : SliceN d385 d384 (c110,1,[2, 3]) := mkSlice (w:=0) d387 d3 d4 (by decide +kernel)
lemma d396 : SliceN d385 d384 (c111,2,[4, 3, 0]) := mkSlice (w:=2) d387 d13 d14 (by decide +kernel)
lemma d397 : SliceN d385 d384 (c48,2,[1, 3, 4]) := mkSlice (w:=5) d387 d98 d99 (by decide +kernel)
lemma d398 : SliceN d385 d384 (c61,2,[0, 2, 4]) := mkSlice (w:=10) d387 d98 d99 (by decide +kernel)
lemma d399 : SliceN d385 d384 (c65,2,[4, 2, 1]) := mkSlice (w:=1) d387 d13 d14 (by decide +kernel)
lemma d400 : SliceN d385 d384 (c8,3,[1, 3, 0, 4]) := mkSlice (w:=4) d387 d103 d104 (by decide +kernel)
lemma d401 : SliceN d385 d384 (c112,1,[1, 4]) := mkSlice (w:=0) d387 d3 d4 (by decide +kernel)
lemma d402 : SliceN d385 d384 (c69,2,[2, 3, 4]) := mkSlice (w:=3) d387 d98 d99 (by decide +kernel)
lemma d403 : SliceN d385 d384 (c47,2,[3, 0, 4]) := mkSlice (w:=4) d387 d13 d14 (by decide +kernel)
lemma d404 : SliceN d385 d384 (c55,2,[0, 1, 3]) := mkSlice (w:=20) d387 d98 d99 (by decide +kernel)
lemma d405 : SliceN d385 d384 (c113,2,[3, 2, 1]) := mkSlice (w:=1) d387 d13 d14 (by decide +kernel)
lemma d406 : SliceN d385 d384 (c9,3,[0, 2, 1, 4]) := mkSlice (w:=8) d387 d103 d104 (by decide +kernel)
lemma d407 : SliceN d385 d384 (0xff000000ff000000ff000000ff000000,2,[0, 1, 2]) := mkSlice (w:=24) d387 d98 d99 (by decide +kernel)
lemma d408 : SliceN d385 d384 (c36,2,[1, 2, 4]) := mkSlice (w:=0) d387 d18 d19 (by decide +kernel)
lemma d409 : SliceN d385 d384 (c32,2,[2, 1, 3]) := mkSlice (w:=0) d387 d18 d19 (by decide +kernel)
lemma d410 : SliceN d385 d384 (c10,3,[0, 1, 2, 3]) := mkSlice (w:=16) d387 d103 d104 (by decide +kernel)
lemma d411 : SliceN d385 d384 (c35,2,[0, 3, 4]) := mkSlice (w:=0) d387 d18 d19 (by decide +kernel)
lemma d412 : SliceN d385 d384 (c74,2,[1, 0, 4]) := mkSlice (w:=4) d387 d13 d14 (by decide +kernel)
lemma d413 : SliceN d385 d384 (c40,2,[2, 0, 3]) := mkSlice (w:=2) d387 d13 d14 (by decide +kernel)
lemma d414 : SliceN d385 d384 (0x55005500550055005500550055005500,2,[2, 1, 4]) := mkSlice (w:=8) d387 d13 d14 (by decide +kernel)
lemma d415 : SliceN d385 d384 (c41,1,[0, 4]) := mkSlice (w:=0) d387 d3 d4 (by decide +kernel)
lemma d416 : SliceN d385 d384 (c44,2,[3, 2, 0]) := mkSlice (w:=0) d387 d18 d19 (by decide +kernel)
lemma d417 : SliceN d385 d384 (0x55550000555500005555000055550000,2,[1, 2, 3]) := mkSlice (w:=16) d387 d13 d14 (by decide +kernel)
lemma d418 : SliceN d385 d384 (0x303000003030000030300000303,1,[0, 3]) := mkSlice (w:=0) d387 d3 d4 (by decide +kernel)
lemma d419 : SliceN d385 d384 (0x33330000333300003333000033330000,2,[0, 2, 3]) := mkSlice (w:=16) d387 d13 d14 (by decide +kernel)
lemma d420 : SliceN d385 d384 (0xf000f000f000f000f000f000f000f00,2,[0, 1, 4]) := mkSlice (w:=8) d387 d13 d14 (by decide +kernel)
lemma d421 : SliceN d385 d384 (c114,1,[1, 2]) := mkSlice (w:=0) d387 d3 d4 (by decide +kernel)
def d422 : List SliceD := [(c28,4,[1, 2, 3, 4]),(c24,4,[0, 3, 2, 4]),(c25,4,[0, 4, 1, 3]),(c23,4,[1, 4, 0, 2]),(c31,4,[2, 3, 0, 1]),(c11,3,[3, 4, 1, 2]),(c12,3,[2, 4, 3, 0]),(c110,1,[2, 3]),(c111,2,[4, 3, 0]),(c48,2,[1, 3, 4]),(c61,2,[0, 2, 4]),(c65,2,[4, 2, 1]),(c8,3,[1, 3, 0, 4]),(c112,1,[1, 4]),(c69,2,[2, 3, 4]),(c47,2,[3, 0, 4]),(c55,2,[0, 1, 3]),(c113,2,[3, 2, 1]),(c9,3,[0, 2, 1, 4]),(0xff000000ff000000ff000000ff000000,2,[0, 1, 2]),(c36,2,[1, 2, 4]),(c32,2,[2, 1, 3]),(c10,3,[0, 1, 2, 3]),(c35,2,[0, 3, 4]),(c74,2,[1, 0, 4]),(c40,2,[2, 0, 3]),(0x55005500550055005500550055005500,2,[2, 1, 4]),(c41,1,[0, 4]),(c44,2,[3, 2, 0]),(0x55550000555500005555000055550000,2,[1, 2, 3]),(0x303000003030000030300000303,1,[0, 3]),(0x33330000333300003333000033330000,2,[0, 2, 3]),(0xf000f000f000f000f000f000f000f00,2,[0, 1, 4]),(c114,1,[1, 2])]
lemma d423 : ∀ s ∈ d422, SliceN d385 d384 s := by
  unfold d422
  simp only [List.forall_mem_cons]
  exact ⟨d388,d389,d390,d391,d392,d393,d394,d395,d396,d397,d398,d399,d400,d401,d402,d403,d404,d405,d406,d407,d408,d409,d410,d411,d412,d413,d414,d415,d416,d417,d418,d419,d420,d421,by simp⟩
def d424 : List StD := dupD [
 (l3,[(0,[]),(1,[]),(2,[]),(3,[]),(4,[])],[(4,6),(10,11),(5,7),(20,21),(3,7),(1,9),(1,17),(8,12),(24,26),(3,11),(2,18),(4,12),(24,28),(5,21),(20,28),(10,26)],[l2,[0,2,1001,1003,1004],[0,3,1003,1001,1005],[0,4,1001,1003,1006],[1,2,1007,1000,1004],[1,3,1000,1008,1009],[1,4,1000,1008,1010],[2,3,1004,1007,1011],[2,4,1004,1012,1013],[3,4,1005,1014,1015]])]
def d425 : List StD := dupD [
 ([c1,c0,c21,c2,c3,c5],[(0,[]),(1,[]),(5,[]),(6,[]),(2,[]),(7,[]),(4,[]),(8,[]),(9,[]),(10,[]),(11,[])],[],[[0,1],[1],[0,2],[0,2],[0,2],[0],[1,3],[1,3],[1,3],[4,2,5],[5,2],[6,2],[7,8],[5,8,7],[5,9,10]]),
 ([c1,c0,c2,c6,c3,c5],[(0,[]),(5,[]),(2,[]),(12,[]),(1,[]),(13,[]),(14,[]),(15,[]),(3,[]),(16,[]),(17,[])],[],[[0,1],[0,1],[2],[0,1],[0,1],[2,3],[4,1,5],[5,6,7],[7,6],[0],[2,3],[2,3],[8,1],[5,1],[5,9,10]]),
 ([c1,c0,c2,c3,c14,c5],[(0,[]),(5,[]),(3,[]),(13,[]),(14,[]),(9,[]),(18,[]),(17,[]),(19,[]),(2,[]),(20,[])],[],[[0,1],[0,1],[0,1],[2],[0,1],[3,4,5],[2,4,6],[3,1],[7,4,8],[2,5,6],[9,1,10],[3,5],[0],[2,6],[3,1]]),
 ([c1,c0,c2,c3,c5,c17],[(0,[]),(5,[]),(4,[]),(7,[]),(9,[]),(14,[]),(19,[]),(1,[]),(21,[]),(11,[]),(22,[])],[],[[0,1],[0,1],[0,1],[0,1],[2],[3,4,5],[3,5],[2,5,6],[7,1,8],[9,4,6],[2,4,6],[3,1],[2,10],[3,1],[0]]),
 (l7,[(1,[]),(9,[]),(6,[]),(2,[]),(14,[]),(12,[]),(0,[]),(23,[]),(24,[]),(10,[]),(25,[]),(16,[])],[],[[0,1,2],[3,4,5],[6,2,7],[8,1,9],[10,1,11],[0,2],[3],[0,2],[0,2],[0],[3,1],[3,1],[7,1],[7,1],[8,9]]),
 ([c1,c0,c2,c3,c18,c5],[(1,[]),(6,[]),(8,[]),(14,[]),(26,[]),(3,[]),(19,[]),(0,[]),(27,[]),(2,[]),(25,[])],[],[[0,1],[2,3,4],[5,3,6],[7,1,8],[4,3],[0,1],[0,1],[5],[0,1],[2,4,5],[9,1],[2,6,10],[0],[5,4],[8,1]]),
 ([c1,c0,c2,c3,c5,c72],[(1,[]),(6,[]),(8,[]),(14,[]),(16,[]),(7,[]),(25,[]),(0,[]),(28,[]),(4,[]),(19,[])],[],[[0,1],[2,3,4],[5,3],[6,3,4],[7,1,8],[0,1],[0,1],[0,1],[9],[2,4],[2,10,5],[5,1],[5,4],[5,1],[0]]),
 ([c1,c0,c2,c3,c16,c5],[(26,[]),(9,[]),(16,[]),(2,[]),(3,[]),(19,[]),(0,[]),(27,[]),(1,[]),(13,[]),(10,[])],[],[[0,1],[0,2,3],[4,1,5],[6,2,7],[0,1],[3,1],[4,0],[8,0,9],[7,2,10],[3,1],[4],[3,1],[3],[4,0],[7,0]]),
 ([c1,c0,c2,c3,c5,c20],[(15,[]),(9,[]),(29,[]),(2,[]),(4,[]),(19,[]),(0,[]),(30,[]),(24,[]),(1,[])],[],[[0,1,2],[2,0,3],[2,1],[4,1,5],[6,0,7],[3,1],[0,5,8],[0,2,4],[9,1],[3,0],[3,0],[4],[4,2],[7,0],[3]]),
 ([c1,c0,c2,c3,c5,c7],[(26,[]),(10,[]),(31,[]),(16,[]),(32,[]),(3,[]),(4,[]),(0,[]),(1,[]),(33,[])],[],[[0,1,2],[0,3,4],[5,1],[0,2,6],[7,1],[2,1],[2,0,5],[6,1,3],[8,0,9],[5,0],[4,2,6],[9,0],[5,0],[6],[5]])]
def d426 : List StD := dupD [
 ([0xeeee0000eeee,c1,c0,c2,c3],[(0,[]),(1,[]),(19,[]),(9,[]),(2,[]),(3,[]),(10,[]),(0,[(2,0,3)]),(16,[]),(14,[]),(1,[(2,0,3)]),(8,[])],[],[[0,1],[1,0],[2,3,4],[5,6],[7,3],[7,8,9],[7,2,3],[10,3,6],[10,2,9],[11,2,3]]),
 ([c27,c1,c0,c2,c5],[(0,[]),(2,[]),(19,[]),(14,[]),(1,[]),(10,[]),(16,[]),(4,[]),(0,[(2,1,2)]),(9,[]),(2,[(2,0,3)]),(15,[])],[],[[0,1],[2,3,4],[1,0],[5,6,7],[8,5,9],[8,3],[8,2,3],[10,3,6],[11,2,3],[10,2,9]]),
 ([c70,c1,c0,c3,c5],[(0,[]),(14,[]),(0,[(2,0,1)]),(0,[(0,0,1)]),(0,[(3,1,2)]),(19,[]),(0,[(0,1,2)]),(9,[]),(4,[]),(1,[(2,1,2)]),(10,[]),(3,[(2,0,3)]),(26,[])],[],[[0,1],[2,1,3],[4,5,6],[7,5,8],[9,7,10],[11,1,5],[12,1],[9,1],[9,1],[11,10]]),
 ([0x3333303033333030,c1,c2,c3,c5],[(0,[]),(9,[]),(0,[(3,0,1)]),(0,[(0,0,1)]),(3,[]),(19,[]),(0,[(3,0,3)]),(0,[(0,0,3)]),(2,[(2,1,2)]),(16,[]),(24,[]),(4,[(2,0,3)])],[],[[0,1],[2,1,3],[4,5],[6,5,7],[8,9],[10,1,5],[11,1,5],[8,1],[8,1],[10,9,11]]),
 ([c75,c0,c2,c3,c5],[(1,[]),(10,[]),(2,[]),(16,[]),(0,[]),(32,[]),(3,[(2,1,2)]),(4,[(2,1,2)]),(19,[])],[],[[0,1],[2,3],[4,1],[4,3],[5,1,3],[6,5],[7,1,3],[6,1],[5,8,7],[6,1]])]
def d427 : List StD := []
lemma d428 : LevelN d385 d384 3 d427 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d429 : levelOK d384 d422 3 (d427.map Prod.fst) ((d426.drop (0*8)).take 8) = true := by decide +kernel
lemma d430 : LevelN d385 d384 4 d426 := levelStep d387 d423 d428 (chunks 8 d426 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d429
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d431 : levelOK d384 d422 4 (d426.map Prod.fst) ((d425.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d432 : levelOK d384 d422 4 (d426.map Prod.fst) ((d425.drop (1*8)).take 8) = true := by decide +kernel
lemma d433 : LevelN d385 d384 5 d425 := levelStep d387 d423 d430 (chunks 8 d425 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d431
  · exact d432
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d434 : levelOK d384 d422 5 (d425.map Prod.fst) ((d424.drop (0*8)).take 8) = true := by decide +kernel
lemma d435 : LevelN d385 d384 6 d424 := levelStep d387 d423 d433 (chunks 8 d424 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d434
  ))
lemma d436 : LowN d385 d384 7 := lowSearch d387 d435 (by decide +kernel)
def d437 : Nat := 0xfffefefefffefefefffefefefffefefe
def d438 : List Nat := l0
def d439 : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4),(3,16,24),(4,8,24)]
lemma d440 : baseOK d437 d438 d439 = true := by decide +kernel
lemma d441 : LowN d438 d437 4 := lowCount d440 (by decide +kernel)
def d442 : Nat := 0xfffefeeefffafac0fffefeeefffafac0
def d443 : List Nat := [0, 1, 2, 3, 4, 5]
def d444 : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9),(4,1,17),(5,1,33)]
lemma d445 : baseOK d442 d443 d444 = true := by decide +kernel
lemma d446 : SliceN d443 d442 (c28,7,[1, 2, 3, 4, 5]) := mkSlice (w:=0) d445 d224 d258 (by decide +kernel)
lemma d447 : SliceN d443 d442 (c24,7,[0, 3, 4, 2, 5]) := mkSlice (w:=0) d445 d108 d137 (by decide +kernel)
lemma d448 : SliceN d443 d442 (c25,7,[5, 0, 3, 4, 1]) := mkSlice (w:=0) d445 d224 d258 (by decide +kernel)
lemma d449 : SliceN d443 d442 (c23,7,[0, 1, 2, 4, 5]) := mkSlice (w:=0) d445 d387 d436 (by decide +kernel)
lemma d450 : SliceN d443 d442 (c31,7,[0, 1, 2, 3, 5]) := mkSlice (w:=0) d445 d387 d436 (by decide +kernel)
lemma d451 : SliceN d443 d442 (c43,7,[2, 3, 4, 0, 1]) := mkSlice (w:=0) d445 d108 d137 (by decide +kernel)
lemma d452 : SliceN d443 d442 (c111,5,[5, 3, 4, 0]) := mkSlice (w:=2) d445 d85 d94 (by decide +kernel)
lemma d453 : SliceN d443 d442 (c105,5,[2, 0, 3, 4]) := mkSlice (w:=2) d445 d85 d94 (by decide +kernel)
lemma d454 : SliceN d443 d442 (c86,4,[2, 3, 4]) := mkSlice (w:=0) d445 d41 d55 (by decide +kernel)
lemma d455 : SliceN d443 d442 (c87,4,[2, 3, 4]) := mkSlice (w:=32) d445 d41 d55 (by decide +kernel)
lemma d456 : SliceN d443 d442 (c85,5,[1, 2, 3, 4]) := mkSlice (w:=32) d445 d85 d94 (by decide +kernel)
lemma d457 : SliceN d443 d442 (c36,4,[1, 2, 4, 5]) := mkSlice (w:=0) d445 d23 d37 (by decide +kernel)
lemma d458 : SliceN d443 d442 (c32,4,[1, 2, 3, 5]) := mkSlice (w:=0) d445 d23 d37 (by decide +kernel)
lemma d459 : SliceN d443 d442 (c59,5,[2, 3, 4, 1]) := mkSlice (w:=0) d445 d59 d68 (by decide +kernel)
lemma d460 : SliceN d443 d442 (c35,5,[0, 3, 4, 5]) := mkSlice (w:=0) d445 d59 d68 (by decide +kernel)
lemma d461 : SliceN d443 d442 (c13,6,l0) := mkSlice (w:=32) d445 d171 d180 (by decide +kernel)
lemma d462 : SliceN d443 d442 (c115,5,[3, 4, 0, 2]) := mkSlice (w:=0) d445 d72 d81 (by decide +kernel)
lemma d463 : SliceN d443 d442 (c58,4,[0, 5, 1, 4]) := mkSlice (w:=0) d445 d23 d37 (by decide +kernel)
lemma d464 : SliceN d443 d442 (c91,4,[0, 5, 1, 3]) := mkSlice (w:=0) d445 d23 d37 (by decide +kernel)
lemma d465 : SliceN d443 d442 (0xc0c0c0c000000000c0c0c0c,4,[0, 3, 4]) := mkSlice (w:=2) d445 d41 d55 (by decide +kernel)
lemma d466 : SliceN d443 d442 (c84,5,[0, 2, 3, 4]) := mkSlice (w:=32) d445 d85 d94 (by decide +kernel)
lemma d467 : SliceN d443 d442 (0xff000000ff000000ff000000ff,4,[1, 5, 0, 2]) := mkSlice (w:=0) d445 d23 d37 (by decide +kernel)
lemma d468 : SliceN d443 d442 (c95,2,[5, 2, 1]) := mkSlice (w:=1) d445 d13 d14 (by decide +kernel)
lemma d469 : SliceN d443 d442 (c61,3,[0, 2, 4, 5]) := mkSlice (w:=10) d445 d262 d263 (by decide +kernel)
lemma d470 : SliceN d443 d442 (c42,3,[0, 2, 3, 5]) := mkSlice (w:=18) d445 d262 d263 (by decide +kernel)
lemma d471 : SliceN d443 d442 (c69,3,[2, 3, 4, 5]) := mkSlice (w:=3) d445 d262 d263 (by decide +kernel)
lemma d472 : SliceN d443 d442 (c97,2,[4, 1, 5]) := mkSlice (w:=8) d445 d13 d14 (by decide +kernel)
lemma d473 : SliceN d443 d442 (c11,4,[3, 4, 5, 2, 1]) := mkSlice (w:=1) d445 d440 d441 (by decide +kernel)
lemma d474 : SliceN d443 d442 (0x50000000500000005000000050000,1,[1, 5]) := mkSlice (w:=16) d445 d3 d4 (by decide +kernel)
lemma d475 : SliceN d443 d442 (0x500000005000000050000000500,1,[1, 5]) := mkSlice (w:=8) d445 d3 d4 (by decide +kernel)
lemma d476 : SliceN d443 d442 (c98,2,[3, 1, 5]) := mkSlice (w:=16) d445 d13 d14 (by decide +kernel)
lemma d477 : SliceN d443 d442 (c99,3,[0, 1, 3, 4]) := mkSlice (w:=36) d445 d262 d263 (by decide +kernel)
lemma d478 : SliceN d443 d442 (c8,4,[1, 3, 4, 0, 5]) := mkSlice (w:=4) d445 d440 d441 (by decide +kernel)
lemma d479 : SliceN d443 d442 (c47,3,[3, 4, 0, 5]) := mkSlice (w:=4) d445 d103 d104 (by decide +kernel)
lemma d480 : SliceN d443 d442 (c53,3,[1, 3, 0, 5]) := mkSlice (w:=4) d445 d103 d104 (by decide +kernel)
lemma d481 : SliceN d443 d442 (c65,3,[4, 5, 1, 2]) := mkSlice (w:=1) d445 d103 d104 (by decide +kernel)
lemma d482 : SliceN d443 d442 (c74,3,[1, 4, 0, 5]) := mkSlice (w:=4) d445 d103 d104 (by decide +kernel)
lemma d483 : SliceN d443 d442 (0x300030003000300030003000300030,2,[4, 0, 5]) := mkSlice (w:=4) d445 d13 d14 (by decide +kernel)
lemma d484 : SliceN d443 d442 (c93,2,[5, 4, 3]) := mkSlice (w:=2) d445 d13 d14 (by decide +kernel)
lemma d485 : SliceN d443 d442 (c104,3,[0, 2, 1, 5]) := mkSlice (w:=8) d445 d103 d104 (by decide +kernel)
lemma d486 : SliceN d443 d442 (c100,3,[0, 1, 2, 4]) := mkSlice (w:=40) d445 d262 d263 (by decide +kernel)
lemma d487 : SliceN d443 d442 (c113,3,[3, 5, 1, 2]) := mkSlice (w:=1) d445 d103 d104 (by decide +kernel)
lemma d488 : SliceN d443 d442 (0x3030000030300000303000003030,2,[3, 0, 5]) := mkSlice (w:=4) d445 d13 d14 (by decide +kernel)
lemma d489 : SliceN d443 d442 (c88,3,[0, 2, 1, 5]) := mkSlice (w:=16) d445 d103 d104 (by decide +kernel)
lemma d490 : SliceN d443 d442 (0xffff000000000000ffff000000000000,3,[0, 1, 2, 3]) := mkSlice (w:=48) d445 d262 d263 (by decide +kernel)
lemma d491 : SliceN d443 d442 (0xf0000000f0000000f0000000f0,2,[1, 0, 5]) := mkSlice (w:=4) d445 d13 d14 (by decide +kernel)
lemma d492 : SliceN d443 d442 (0x30000000300000003000000030,1,[0, 5]) := mkSlice (w:=4) d445 d3 d4 (by decide +kernel)
lemma d493 : SliceN d443 d442 (0x4000400040004000400040004000400,1,[4, 5]) := mkSlice (w:=10) d445 d8 d9 (by decide +kernel)
lemma d494 : SliceN d443 d442 (c48,3,[1, 3, 4, 5]) := mkSlice (w:=5) d445 d262 d263 (by decide +kernel)
lemma d495 : SliceN d443 d442 (c103,1,[2, 5]) := mkSlice (w:=2) d445 d8 d9 (by decide +kernel)
lemma d496 : SliceN d443 d442 (c102,1,[1, 4]) := mkSlice (w:=4) d445 d8 d9 (by decide +kernel)
lemma d497 : SliceN d443 d442 (c96,1,[2, 4]) := mkSlice (w:=0) d445 d3 d4 (by decide +kernel)
lemma d498 : SliceN d443 d442 (0x33000000000000003300,1,[0, 2]) := mkSlice (w:=8) d445 d8 d9 (by decide +kernel)
lemma d499 : SliceN d443 d442 (0x550000005500000055000000550000,2,[2, 1, 5]) := mkSlice (w:=16) d445 d13 d14 (by decide +kernel)
lemma d500 : SliceN d443 d442 (c101,1,[3, 5]) := mkSlice (w:=1) d445 d8 d9 (by decide +kernel)
lemma d501 : SliceN d443 d442 (c44,4,[0, 3, 2, 5]) := mkSlice (w:=0) d445 d23 d37 (by decide +kernel)
lemma d502 : SliceN d443 d442 (0xaaaaaaaa00000000aaaaaaaa,3,[3, 4, 1, 2]) := mkSlice (w:=1) d445 d103 d104 (by decide +kernel)
lemma d503 : SliceN d443 d442 (0xf0000000f0000000f0000000f00,2,[0, 1, 5]) := mkSlice (w:=8) d445 d13 d14 (by decide +kernel)
lemma d504 : SliceN d443 d442 (0x808000008080000080800000808,1,[3, 5]) := mkSlice (w:=3) d445 d8 d9 (by decide +kernel)
lemma d505 : SliceN d443 d442 (0xa0a00000a0a00000a0a00000a0a0,2,[1, 3, 5]) := mkSlice (w:=5) d445 d98 d99 (by decide +kernel)
lemma d506 : SliceN d443 d442 (c114,2,[1, 2, 5]) := mkSlice (w:=0) d445 d18 d19 (by decide +kernel)
lemma d507 : SliceN d443 d442 (0x50500000000000005050,1,[1, 3]) := mkSlice (w:=4) d445 d8 d9 (by decide +kernel)
lemma d508 : SliceN d443 d442 (0x3300000000000000330000,1,[0, 2]) := mkSlice (w:=16) d445 d8 d9 (by decide +kernel)
lemma d509 : SliceN d443 d442 (0x5500000055000000550000005500,2,[2, 1, 5]) := mkSlice (w:=8) d445 d13 d14 (by decide +kernel)
lemma d510 : SliceN d443 d442 (0x20002000200020002000200020002,1,[4, 5]) := mkSlice (w:=1) d445 d8 d9 (by decide +kernel)
lemma d511 : SliceN d443 d442 (c60,4,[0, 4, 2, 5]) := mkSlice (w:=0) d445 d23 d37 (by decide +kernel)
lemma d512 : SliceN d443 d442 (0x11110000000000001111,1,[2, 3]) := mkSlice (w:=0) d445 d3 d4 (by decide +kernel)
lemma d513 : SliceN d443 d442 (c89,2,[0, 1, 5]) := mkSlice (w:=16) d445 d13 d14 (by decide +kernel)
lemma d514 : SliceN d443 d442 (0x80008000800080008000800080008,1,[4, 5]) := mkSlice (w:=3) d445 d8 d9 (by decide +kernel)
lemma d515 : SliceN d443 d442 (0xa000a000a000a000a000a000a000a0,2,[1, 4, 5]) := mkSlice (w:=5) d445 d98 d99 (by decide +kernel)
lemma d516 : SliceN d443 d442 (0xf000000000000000f00000000,1,[0, 1]) := mkSlice (w:=32) d445 d8 d9 (by decide +kernel)
lemma d517 : SliceN d443 d442 (0x88000000880000008800000088,1,[2, 5]) := mkSlice (w:=3) d445 d8 d9 (by decide +kernel)
lemma d518 : SliceN d443 d442 (0x44440000444400004444000044440000,2,[2, 3, 5]) := mkSlice (w:=18) d445 d98 d99 (by decide +kernel)
lemma d519 : SliceN d443 d442 (c90,2,[5, 1, 0]) := mkSlice (w:=0) d445 d18 d19 (by decide +kernel)
lemma d520 : SliceN d443 d442 (0x300030000000000030003,1,[0, 4]) := mkSlice (w:=0) d445 d3 d4 (by decide +kernel)
lemma d521 : SliceN d443 d442 (0xffff000000000000ffff,4,[2, 3, 0, 1]) := mkSlice (w:=0) d445 d23 d37 (by decide +kernel)
lemma d522 : SliceN d443 d442 (c92,4,[2, 4, 0, 1]) := mkSlice (w:=0) d445 d23 d37 (by decide +kernel)
lemma d523 : SliceN d443 d442 (0x3030000000000000303,1,[0, 3]) := mkSlice (w:=0) d445 d3 d4 (by decide +kernel)
lemma d524 : SliceN d443 d442 (0x550000000000000055,1,[1, 2]) := mkSlice (w:=0) d445 d3 d4 (by decide +kernel)
lemma d525 : SliceN d443 d442 (0xaa00000000000000aa,1,[1, 2]) := mkSlice (w:=1) d445 d3 d4 (by decide +kernel)
lemma d526 : SliceN d443 d442 (0xf0f0000000000000f0f000000000000,2,[0, 1, 3]) := mkSlice (w:=48) d445 d98 d99 (by decide +kernel)
lemma d527 : SliceN d443 d442 (c108,2,[0, 1, 3]) := mkSlice (w:=36) d445 d98 d99 (by decide +kernel)
lemma d528 : SliceN d443 d442 (c107,2,[0, 1, 4]) := mkSlice (w:=40) d445 d98 d99 (by decide +kernel)
lemma d529 : SliceN d443 d442 (c106,2,[0, 1, 4]) := mkSlice (w:=36) d445 d98 d99 (by decide +kernel)
lemma d530 : SliceN d443 d442 (c109,2,[0, 2, 5]) := mkSlice (w:=10) d445 d98 d99 (by decide +kernel)
lemma d531 : SliceN d443 d442 (0xcc000000cc000000cc000000cc0000,2,[0, 2, 5]) := mkSlice (w:=18) d445 d98 d99 (by decide +kernel)
lemma d532 : SliceN d443 d442 (0x55005500000000005500550000000000,2,[1, 2, 4]) := mkSlice (w:=40) d445 d98 d99 (by decide +kernel)
lemma d533 : SliceN d443 d442 (c94,2,[0, 4, 5]) := mkSlice (w:=10) d445 d98 d99 (by decide +kernel)
lemma d534 : SliceN d443 d442 (0x330033000000000033003300,2,[0, 2, 4]) := mkSlice (w:=8) d445 d98 d99 (by decide +kernel)
def d535 : List SliceD := [(c28,7,[1, 2, 3, 4, 5]),(c24,7,[0, 3, 4, 2, 5]),(c25,7,[5, 0, 3, 4, 1]),(c23,7,[0, 1, 2, 4, 5]),(c31,7,[0, 1, 2, 3, 5]),(c43,7,[2, 3, 4, 0, 1]),(c111,5,[5, 3, 4, 0]),(c105,5,[2, 0, 3, 4]),(c86,4,[2, 3, 4]),(c87,4,[2, 3, 4]),(c85,5,[1, 2, 3, 4]),(c36,4,[1, 2, 4, 5]),(c32,4,[1, 2, 3, 5]),(c59,5,[2, 3, 4, 1]),(c35,5,[0, 3, 4, 5]),(c13,6,l0),(c115,5,[3, 4, 0, 2]),(c58,4,[0, 5, 1, 4]),(c91,4,[0, 5, 1, 3]),(0xc0c0c0c000000000c0c0c0c,4,[0, 3, 4]),(c84,5,[0, 2, 3, 4]),(0xff000000ff000000ff000000ff,4,[1, 5, 0, 2]),(c95,2,[5, 2, 1]),(c61,3,[0, 2, 4, 5]),(c42,3,[0, 2, 3, 5]),(c69,3,[2, 3, 4, 5]),(c97,2,[4, 1, 5]),(c11,4,[3, 4, 5, 2, 1]),(0x50000000500000005000000050000,1,[1, 5]),(0x500000005000000050000000500,1,[1, 5]),(c98,2,[3, 1, 5]),(c99,3,[0, 1, 3, 4]),(c8,4,[1, 3, 4, 0, 5]),(c47,3,[3, 4, 0, 5]),(c53,3,[1, 3, 0, 5]),(c65,3,[4, 5, 1, 2]),(c74,3,[1, 4, 0, 5]),(0x300030003000300030003000300030,2,[4, 0, 5]),(c93,2,[5, 4, 3]),(c104,3,[0, 2, 1, 5]),(c100,3,[0, 1, 2, 4]),(c113,3,[3, 5, 1, 2]),(0x3030000030300000303000003030,2,[3, 0, 5]),(c88,3,[0, 2, 1, 5]),(0xffff000000000000ffff000000000000,3,[0, 1, 2, 3]),(0xf0000000f0000000f0000000f0,2,[1, 0, 5]),(0x30000000300000003000000030,1,[0, 5]),(0x4000400040004000400040004000400,1,[4, 5]),(c48,3,[1, 3, 4, 5]),(c103,1,[2, 5]),(c102,1,[1, 4]),(c96,1,[2, 4]),(0x33000000000000003300,1,[0, 2]),(0x550000005500000055000000550000,2,[2, 1, 5]),(c101,1,[3, 5]),(c44,4,[0, 3, 2, 5]),(0xaaaaaaaa00000000aaaaaaaa,3,[3, 4, 1, 2]),(0xf0000000f0000000f0000000f00,2,[0, 1, 5]),(0x808000008080000080800000808,1,[3, 5]),(0xa0a00000a0a00000a0a00000a0a0,2,[1, 3, 5]),(c114,2,[1, 2, 5]),(0x50500000000000005050,1,[1, 3]),(0x3300000000000000330000,1,[0, 2]),(0x5500000055000000550000005500,2,[2, 1, 5]),(0x20002000200020002000200020002,1,[4, 5]),(c60,4,[0, 4, 2, 5]),(0x11110000000000001111,1,[2, 3]),(c89,2,[0, 1, 5]),(0x80008000800080008000800080008,1,[4, 5]),(0xa000a000a000a000a000a000a000a0,2,[1, 4, 5]),(0xf000000000000000f00000000,1,[0, 1]),(0x88000000880000008800000088,1,[2, 5]),(0x44440000444400004444000044440000,2,[2, 3, 5]),(c90,2,[5, 1, 0]),(0x300030000000000030003,1,[0, 4]),(0xffff000000000000ffff,4,[2, 3, 0, 1]),(c92,4,[2, 4, 0, 1]),(0x3030000000000000303,1,[0, 3]),(0x550000000000000055,1,[1, 2]),(0xaa00000000000000aa,1,[1, 2]),(0xf0f0000000000000f0f000000000000,2,[0, 1, 3]),(c108,2,[0, 1, 3]),(c107,2,[0, 1, 4]),(c106,2,[0, 1, 4]),(c109,2,[0, 2, 5]),(0xcc000000cc000000cc000000cc0000,2,[0, 2, 5]),(0x55005500000000005500550000000000,2,[1, 2, 4]),(c94,2,[0, 4, 5]),(0x330033000000000033003300,2,[0, 2, 4])]
lemma d536 : ∀ s ∈ d535, SliceN d443 d442 s := by
  unfold d535
  simp only [List.forall_mem_cons]
  exact ⟨d446,d447,d448,d449,d450,d451,d452,d453,d454,d455,d456,d457,d458,d459,d460,d461,d462,d463,d464,d465,d466,d467,d468,d469,d470,d471,d472,d473,d474,d475,d476,d477,d478,d479,d480,d481,d482,d483,d484,d485,d486,d487,d488,d489,d490,d491,d492,d493,d494,d495,d496,d497,d498,d499,d500,d501,d502,d503,d504,d505,d506,d507,d508,d509,d510,d511,d512,d513,d514,d515,d516,d517,d518,d519,d520,d521,d522,d523,d524,d525,d526,d527,d528,d529,d530,d531,d532,d533,d534,by simp⟩
def d537 : List StD := dupD [
 (l6,[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])],[(4,6),(10,11),(5,7),(36,37),(3,7),(1,9),(16,17),(1,17),(1,33),(8,12),(40,42),(3,11),(48,50),(3,19),(2,34),(4,12),(16,20),(4,20),(40,44),(5,37),(16,24),(8,24),(36,44),(10,42),(36,52),(18,50)],[l2,[0,2,1001,1003,1004],[0,3,1003,1001,1005],[0,4,1001,1006,1007],[0,5,1001,1003,1008],[1,2,1009,1000,1004],[1,3,1000,1010,1011],[1,4,1000,1012,1013],[1,5,1000,1010,1014],[2,3,1004,1009,1015],[2,4,1004,1016,1017],[2,5,1004,1018,1019],[3,4,1005,1020,1021],[3,5,1005,1022,1023],[4,5,1007,1024,1025]])]
def d538 : List StD := dupD [
 ([c1,c0,c21,c2,c3,c5,c4],[(0,[]),(1,[]),(6,[]),(3,[(1,0,1)]),(4,[(1,0,1)]),(7,[]),(2,[]),(8,[]),(5,[]),(9,[])],[(3,6),(10,11),(1,9),(18,19),(1,33),(8,12),(2,6),(16,20),(16,24),(8,24)],[[0,1],[0,1],[0,2,1000],[0,1001,3,1002],[0,1003,4,1001],[0,5,1004],[0],[1,2,5],[1,2],[1,2],[1,2],[2,6,5,7],[2,3,7],[2,4,7],[2,5,8],[2,1005,3,1006],[2,1007,4,1005],[2,5,9],[3,4,1002,1008,1009],[3,5,9],[4,5,9]]),
 ([c1,c0,c2,c6,c3,c5,c4],[(0,[]),(6,[]),(1,[(1,0,3)]),(2,[]),(3,[(1,0,2)]),(4,[(1,0,2)]),(5,[(1,0,3)]),(10,[])],[(5,6),(4,7),(1,9),(1,17),(36,37),(1,33),(3,7),(4,6),(32,34),(40,42),(48,50),(5,9),(5,17),(5,33),(16,24),(8,24),(2,34),(10,42),(18,50)],[l1,[0,1,3],[0,1],[0,1002,4],[0,1003,5],[0,1004,6,1005],[1,3,1006,2,1007],[2,1008,1,1007],[2,4,1002,1,1009,1007],[2,5,1003,1,1010,1007],[2,6,1005,1,7,1008,1007],[0],[1,3,1011,4,1006],[1,3,1012,5,1006],[1,3,7,1013,6,1006],[4,1014,1002],[5,1015,1003],[6,1016,7,1005],[4,5,1002,1014,1015],[4,6,1002,7,1017,1005],[5,6,1003,7,1018,1005]]),
 ([c1,c0,c2,c3,c14,c5,c4],[(0,[]),(1,[(1,0,1)]),(2,[(1,1,2)]),(3,[]),(4,[(1,0,3)]),(5,[(1,1,3)]),(11,[]),(1,[]),(6,[]),(10,[]),(2,[]),(4,[]),(5,[])],[(10,11),(5,7),(3,7),(1,17),(40,41),(8,12),(3,11),(1,9),(4,6),(48,50),(3,19),(2,34),(5,13),(2,6),(16,20),(4,20),(5,37),(8,24),(10,42),(18,50)],[[0,1000,1,1001],[0,1002,2],[0,3],[0,3],[0,1003,4],[0,1004,5,1000],[1,2,1005,1001,1002],[1,3,1006,1007],[1,6,7,1001,8,1008],[1,4,1001,1009,1010],[1,5,1001,9,1011,1009],[2,3,1012,1005],[2,6,10,1002,1013],[2,4,1002,1014,1015],[2,5,1002,9,1016,1011],[0],[3,1017,4],[3,9,1018,5],[4,6,11,1003,1015],[5,6,12,9,1016,1011],[4,5,1003,9,1019,1011]]),
 ([c1,c0,c2,c3,c5,c17,c4],[(0,[]),(1,[(1,0,2)]),(2,[(1,1,3)]),(3,[(1,0,3)]),(4,[]),(5,[(1,2,3)]),(12,[]),(1,[]),(6,[]),(10,[]),(2,[]),(3,[]),(5,[])],[(18,19),(5,7),(3,7),(1,9),(48,49),(8,12),(40,42),(3,11),(3,19),(1,17),(2,34),(4,12),(5,21),(5,37),(16,24),(10,42),(18,50)],[[0,1000,1,1001],[0,1002,2],[0,1003,3],[0,4],[0,4],[0,1004,5,1000],[1,2,1005,1001,1002],[1,3,1001,1006,1007],[1,4,1008,1009],[1,6,7,1001,8,1006],[1,5,1001,9,1010,1006],[2,3,1002,1005,1011],[2,4,1012,1008],[2,6,10,1002,1005],[2,5,1002,9,1013,1010],[3,4,1014],[3,6,11,1003,1011],[3,5,1003,9,1015,1010],[0],[4,9,1016,5],[5,6,12,9,1013,1010]]),
 ([c1,c0,c2,c3,c5,c4,c45],[(0,[]),(7,[]),(1,[(1,0,4)]),(2,[(1,0,1)]),(3,[(1,0,4)]),(4,[(1,0,4)]),(5,[]),(8,[]),(10,[]),(1,[]),(13,[])],[(5,7),(36,37),(3,7),(40,41),(48,49),(40,42),(48,50),(8,12),(4,12),(16,20),(4,20),(16,24),(8,24)],[[0,1,1000,2],[0,1001,3,1002],[0,1003,4,1001],[0,1004,5,1001],[0,1,6],[0,1],[2,3,7,1000,1002],[2,4,7,1005,1000],[2,5,7,1006,1000],[1,6,7,8],[2,7,9,8,10],[3,4,1002,1007,1008],[3,5,1002,1009,1010],[1,3,6,8],[3,7,8],[4,5,1008,1011,1012],[1,4,6,8],[4,7,8],[1,5,6,8],[5,7,8],[0]]),
 ([c1,c0,c2,c19,c3,c5,c4],[(0,[(1,0,1)]),(1,[]),(7,[]),(2,[]),(0,[]),(14,[]),(3,[(1,1,2)]),(4,[(1,1,2)]),(6,[])],[(3,7),(2,6),(4,12),(8,9),(1,9),(16,17),(1,17),(1,33),(0,33),(10,14),(18,22),(5,37),(16,24),(8,24),(10,42),(18,50)],[[0,1,2],[0,3,1000,1001],[0,2,4,5],[0,6,1002,1003,1004],[0,7,1003,1005,1006],[0,2,1007,1008],[1,2],[1,2,3],[1,2],[1,2],[1,2,8],[1],[3,1009,6,1000],[3,1010,7,1000],[2,3,1011],[2,5],[2,5],[2,5,8],[6,7,1002,1012,1013],[2,1014,6,1007],[2,1015,7,1007]]),
 ([c1,c0,c2,c3,c18,c5,c4],[(0,[(1,0,2)]),(1,[]),(6,[]),(3,[]),(0,[]),(4,[(1,1,3)]),(5,[(1,1,4)]),(7,[]),(2,[]),(4,[]),(5,[])],[(3,7),(2,6),(3,11),(8,9),(16,17),(1,17),(1,33),(0,33),(6,10),(16,20),(5,33),(18,26),(10,34),(18,50)],[[0,1,2],[0,2,1000,1001],[0,3,1002,1003],[0,2,4,1004],[0,5,1003,1004,1005],[0,6,7,1006,1007],[1,2,7],[1,2],[1,2,3],[1,2],[1,2],[2,3,1008],[2,8,7,1009],[2,1009,5,1000],[2,7,1010],[1],[3,1011,5,1002],[3,7,1012],[2,5,9,1005],[2,6,10,7,1006],[5,6,7,1013,1006]]),
 ([c1,c0,c2,c3,c5,c72,c4],[(0,[(1,0,3)]),(7,[]),(1,[]),(2,[(1,3,4)]),(6,[]),(3,[(1,1,3)]),(4,[]),(0,[]),(2,[]),(3,[]),(5,[])],[(3,7),(2,6),(4,12),(8,9),(1,9),(3,19),(16,17),(1,33),(0,33),(8,12),(6,18),(5,33),(10,26),(10,42),(18,34)],[[0,1,2],[0,3,4,1000,1001],[0,5,1002,1003,1004],[0,6,1005,1006],[0,1,7,1003],[0,1,1007,1008],[1,2],[1,2],[1,2],[1,6],[1,2,4],[3,4,1009,5,1000],[3,4,6,1010],[1,3,8,4,1009],[1,4,1011],[5,6,1012,1005],[1,5,9,1002],[1,1013,5,1007],[1,2],[1,6,1014],[1,10,4,1007]]),
 ([c1,c0,c2,c3,c5,c4,c73],[(0,[(1,0,4)]),(7,[]),(1,[]),(2,[(1,0,4)]),(6,[]),(10,[]),(3,[(1,1,4)]),(4,[(1,1,4)]),(15,[]),(0,[]),(16,[]),(5,[])],[(3,6),(8,9),(0,9),(16,17),(8,12),(2,6),(16,20),(1,9),(16,24),(8,24)],[[0,1,2],[0,3,4,5,1000],[0,5,1001,6,1002],[0,5,1003,7,1001],[0,1,5,8],[0,1,9,5,10],[1,2],[1,2],[1,2],[1,2,4],[1,11],[3,4,1004,6,1005],[3,4,1006,7,1004],[1,4,5],[1,3,10],[6,7,1007,1008,1009],[1,5],[1,6,10],[1,5],[1,7,10],[1,2]]),
 ([c1,c0,c2,c3,c16,c5,c4],[(0,[(1,1,2)]),(1,[(1,1,3)]),(6,[]),(2,[]),(3,[]),(17,[]),(0,[]),(4,[(1,2,3)]),(5,[(1,0,1)]),(1,[]),(4,[]),(5,[]),(10,[])],[(4,6),(5,7),(36,37),(5,13),(8,9),(16,17),(1,17),(1,33),(10,14),(40,42),(32,34),(48,50),(4,20),(40,44),(8,24),(36,44),(5,37),(36,52),(18,50)],[l1,[0,2,3,1002],[0,4,1003,1004],[0,5,6,1002,1005],[0,7,1002,1005,1006],[0,8,1004,1002,1007],[1,3,1008,1000],[1,4,2,1009],[1,5,9,2,1000,1010],[1,7,1000,2,1011],[1,8,1000,2,1009],[2,3,4],[3,4],[2,3,1012,7],[2,3,1013,8,1008],[2],[4,1014,7],[4,1015,8,1003],[5,7,10,1012,1006],[5,8,11,12,1016,1007],[7,8,1006,1017,1018]]),
 ([c1,c0,c2,c3,c5,c20,c4],[(0,[(1,1,3)]),(1,[(1,2,3)]),(6,[]),(2,[]),(3,[(1,2,3)]),(4,[]),(18,[]),(0,[]),(5,[(1,0,2)]),(1,[]),(3,[]),(5,[]),(10,[])],[(4,6),(5,7),(36,37),(8,9),(1,9),(5,21),(16,17),(1,33),(18,22),(40,42),(48,50),(4,12),(48,52),(16,24),(36,44),(10,42),(36,52),(5,37)],[l1,[0,2,3,1002],[0,4,1002,1003,1004],[0,5,1005,1006],[0,6,7,1002,1003],[0,8,1003,1002,1007],[1,3,1008,1000],[1,4,1000,2,1009],[1,5,2,1010],[1,6,9,2,1000,1009],[1,8,1000,2,1009],[2,3,1011,4],[2,3,5],[3,5],[2,3,1012,8,1008],[4,5,1013],[4,6,10,1011,1004],[4,8,1004,1014,1015],[2],[5,1016,8,1005],[6,8,11,12,1017,1007]]),
 ([c1,c0,c2,c3,c5,c4,c26],[(0,[(1,1,4)]),(10,[]),(6,[]),(19,[]),(20,[]),(3,[(1,2,4)]),(4,[(1,2,4)]),(2,[]),(5,[]),(1,[])],[(33,36),(8,9),(0,9),(16,17),(4,6),(40,44),(4,12),(48,52),(16,24),(8,24)],[[0,1,2,3,4],[0,1,3,1000],[0,1,1001,5,1002],[0,1,1003,6,1001],[0,1,3,4],[0,1,3,4],[2,3,4,1004,7],[3,4],[3,4],[1,3,8],[1,3,9],[2,3,1005,5,1006],[2,3,1007,6,1005],[1,2,7,8],[1,3,8],[5,6,1006,1008,1009],[1,3],[1,3],[1,3],[1,3],[1,2]]),
 ([c1,c0,c2,c3,c5,c7,c4],[(0,[(1,2,3)]),(1,[(1,1,2)]),(2,[(1,2,3)]),(3,[]),(4,[]),(21,[]),(0,[]),(5,[(1,1,2)]),(1,[]),(6,[]),(2,[]),(5,[]),(10,[])],[(4,6),(10,11),(5,7),(36,37),(3,7),(16,17),(1,33),(8,12),(18,26),(16,24),(10,26),(8,24),(40,42),(2,34),(16,20),(40,44),(5,37),(48,56),(40,56),(10,42)],[l2,[0,2,1001,1003,1004],[0,3,1001],[0,4,1005],[0,5,6,1001,1003],[0,7,1001,1003,1006],[1,2,1007,1000,1004],[1,3,1008,1009],[1,4,1010,1011],[1,5,8,1012,9,1000],[1,7,1000,1012,1013],[2,3,1007],[2,4,1014],[2,5,10,1007,1004],[2,7,1004,1015,1016],[3,4],[3,4],[3,1017,7,1008],[3],[4,1018,7,1010],[5,7,11,12,1019,1006]]),
 (l8,[(0,[(1,2,4)]),(1,[(1,1,4)]),(10,[]),(7,[]),(20,[]),(2,[(1,0,2)]),(3,[]),(4,[(1,3,4)]),(5,[]),(0,[]),(1,[]),(2,[]),(4,[])],[(5,6),(36,37),(2,7),(8,9),(16,17),(4,6),(0,6),(34,40),(48,50),(36,44),(8,12),(16,20),(4,20),(48,56)],[[0,1,2,3,1000,4],[0,2,1001,5,1002],[0,2,6,1003],[0,2,1004,7,1001],[0,2,8,4],[0,2,9,4,1004],[1,4,1005,5,1006],[1,4,6,1007],[1,4,1008,7,1005],[1,2,8],[1,2,10,3,1005],[5,6,1009,1010],[5,7,1010,1011,1012],[2,5,8],[2,5,11,1011],[6,1013,7,1009],[2,6,8],[2,3],[2,7,8],[2,7,12,1012],[2,6]]),
 (l9,[(0,[(1,3,4)]),(10,[]),(7,[]),(1,[(1,2,4)]),(20,[]),(2,[(1,0,3)]),(3,[(1,3,4)]),(4,[]),(5,[]),(0,[]),(1,[]),(2,[]),(3,[])],[(5,6),(36,37),(2,7),(8,9),(16,17),(4,6),(0,6),(40,42),(34,48),(2,6),(8,12),(4,12),(36,52),(16,20),(40,56)],[[0,1,2,1000,3,4],[0,1,1001,5,1002],[0,1,1003,6,1001],[0,1,7,1004],[0,1,8,4],[0,1,9,4,1003],[3,4,1005,5,1006],[3,4,1007,6,1005],[3,4,7,1008],[1,3,8],[1,3,10,2,1005],[5,6,1009,1010,1011],[5,7,1012,1013],[1,5,8],[1,5,11,1009],[6,7,1014,1012],[1,6,8],[1,6,12,1011],[1,7,8],[1,2],[1,7]])]
def d539 : List StD := dupD [
 ([c22,c1,c0,c2,c3,c5],[(0,[(2,0,4)]),(10,[]),(1,[]),(7,[]),(1,[(2,0,4)]),(6,[])],[(3,6),(10,11),(18,19),(8,12),(2,6),(16,20),(1,9),(1,17),(16,24),(8,24)],[[0,1,2],[0,1,2],[1,3],[1,3],[1,3],[0,3,4],[0,5,1000],[0,1001,1002],[0,1002,1001],[3,4],[3,4],[3,4],[5,1003,1004],[5,1005,1003],[1006,1007,1008,1009]]),
 ([c1,c0,c21,c2,c3,c5,c7,c4],[(0,[(1,2,3)]),(1,[(1,1,2)]),(22,[]),(23,[]),(3,[(1,0,1)]),(24,[]),(4,[(1,0,1)]),(7,[]),(2,[(1,2,3)]),(8,[(1,1,2)]),(5,[(1,1,2)]),(9,[(1,1,2)])],[],[[0,1],[1],[0,2],[0,3,4],[0,5,6],[0,3],[0,2],[0],[1,3],[1,5],[1,3],[1,7],[1,3],[8,2,9],[4,5,9],[6,3,9],[9,7],[10,2],[2,3],[2,5],[2,3],[9,11],[4,3],[6],[2,3],[4],[2,5],[2,3]]),
 ([c0,c2,c6,c3,c14,c5,c4],[(2,[(1,1,2)]),(25,[]),(1,[(1,0,3),(1,0,1)]),(26,[]),(1,[(1,0,1)]),(27,[]),(7,[(1,1,2)]),(3,[(1,0,2)]),(11,[]),(1,[(1,0,3)]),(7,[(1,0,1)]),(6,[]),(4,[(1,0,2),(1,0,3)]),(28,[]),(5,[(1,0,3),(1,1,3)]),(10,[]),(4,[(1,0,3)]),(5,[(1,1,3)]),(4,[(1,0,2)]),(5,[(1,0,3)])],[(4,6),(8,11),(3,9),(1,9),(3,17),(1,17),(3,33),(1,33),(5,9),(36,37),(5,17),(3,7),(5,33),(8,9),(8,24),(2,34),(10,42),(4,20),(18,34)],[[0,1,1000,2],[3,2,4,5,6,1000,1001],[7,1,1002,2,1003],[8,2,9,3,10,11],[12,2,1000,13,1,1004,1005],[14,2,1000,15,1,1006,1007],[8],[0,7,1008],[0,1,7,8,1009],[0,1010,12,1011],[0,15,1012,14,1011],[7,0,1013],[0,7],[12,3,16,1,1005,1014],[6,3,17,15,1,1007,1015],[15],[7,1014,12],[7,15,1016,14],[12,8,18,1,1005,1017],[10,8,19,15,1,1007,1009],[14,12,1005,15,13,1018,1007]]),
 ([c0,c2,c6,c3,c5,c17,c4],[(2,[(1,1,3)]),(25,[]),(1,[(1,0,3),(1,0,2)]),(28,[]),(1,[(1,0,2)]),(27,[]),(7,[(1,1,3)]),(29,[]),(4,[(1,0,2)]),(1,[(1,0,3)]),(7,[(1,0,1)]),(6,[]),(5,[(1,0,3),(1,2,3)]),(10,[]),(3,[(1,0,2),(1,0,3)]),(12,[]),(30,[]),(3,[(1,0,3)]),(5,[(1,2,3)]),(3,[(1,0,2)]),(5,[(1,0,3)])],[(4,6),(16,19),(3,9),(1,9),(3,17),(1,17),(3,33),(1,33),(5,9),(3,7),(5,17),(36,37),(5,33),(16,24),(16,17),(2,34),(4,12),(10,34),(18,50)],[[0,1,1000,2],[3,2,4,5,6,1000,1001],[3,2,1000,7,1,1002,1003],[7,2,8,1,1004,1005],[7,2,9,3,10,11],[12,2,1000,13,1,1006,1007],[13],[0,1008,14,1009],[0,8,1010],[0,1,8,15,1011],[0,13,1012,12,1009],[14,16,17,1,1003,1013],[8,0,1014],[0,8],[6,3,18,13,1,1007,1015],[8,1013,14],[15,14,19,1,1003,1016],[12,3,1003,13,7,1017,1007],[13],[8,13,1018,12],[10,7,20,13,1,1007,1011]]),
 ([c1,c0,c6,c3,c16,c5,c4],[(0,[(1,1,2)]),(6,[]),(1,[(1,0,3),(1,1,3)]),(3,[(1,0,2)]),(17,[]),(4,[(1,0,2),(1,2,3)]),(31,[]),(5,[(1,0,3),(1,0,1)]),(28,[]),(1,[(1,1,3)]),(1,[(1,0,3)]),(26,[]),(4,[(1,2,3)]),(5,[(1,0,1)]),(10,[(1,1,2)]),(32,[]),(4,[(1,0,2)]),(5,[(1,0,3)]),(10,[])],[(5,6),(4,7),(5,9),(3,7),(1,17),(1,33),(4,6),(8,14),(40,42),(3,17),(8,12),(8,24),(2,34),(12,36),(18,34)],[l1,[1],[0,3,1002],[0,3,4,1003],[0,1004,5],[0,6,1005,7],[8,2,9,6,1,1006,1007],[3,1,1008,2],[4,2,10,6,1,1003],[5,2,1004,8,1,1009,1006],[7,2,1005,6,1,1008,1006],[3,0,1010],[0,3],[5,11,12,6,1004,1011],[7,8,13,14,15,1005,1012],[1],[3,1011,5],[3,6,1013,7,1002],[5,4,16,6,1011,1004],[7,4,17,14,11,18],[7,5,1004,6,8,1014,1005]]),
 ([c1,c0,c6,c3,c5,c20,c4],[(0,[(1,1,3)]),(6,[]),(1,[(1,0,3),(1,2,3)]),(3,[(1,0,2),(1,2,3)]),(4,[(1,0,2)]),(18,[]),(31,[]),(5,[(1,0,3),(1,0,2)]),(28,[]),(1,[(1,2,3)]),(29,[]),(1,[(1,0,3)]),(30,[]),(3,[(1,2,3)]),(5,[(1,0,2)]),(10,[(1,1,3)]),(32,[]),(3,[(1,0,2)]),(5,[(1,0,3)]),(10,[])],[(5,6),(4,7),(1,9),(5,17),(3,7),(1,33),(4,6),(16,22),(3,9),(48,50),(16,24),(16,20),(2,34),(10,34),(20,36)],[l1,[1],[0,1002,3],[0,4,1003],[0,4,5,1004],[0,6,1005,7],[8,2,9,6,1,1006,1007],[3,2,1002,10,1,1008,1006],[4,1,1009,2],[5,2,11,6,1,1004],[7,2,1005,6,1,1009,1006],[3,12,13,6,1002,1010],[4,0,1011],[0,4],[7,8,14,15,16,1005,1012],[4,1010,3],[5,3,17,6,1010,1002],[7,3,1002,6,10,1013,1005],[1],[4,6,1014,7,1003],[7,5,18,15,8,19]]),
 ([c1,c0,c2,c6,c3,c29,c5,c4],[(0,[(1,1,2)]),(27,[]),(6,[(1,1,3)]),(17,[]),(2,[(1,1,2)]),(32,[]),(28,[]),(26,[]),(29,[]),(33,[]),(31,[]),(25,[]),(0,[(3,1,2)]),(3,[(1,0,2)]),(0,[(2,1,2)]),(4,[(1,0,2)])],[],[[0,1],[0,1],[2],[0,1],[3],[0,1],[0,1],[4,5],[6,1],[6,7],[6,1],[8,6],[9,10,11],[0],[4,0,5],[12],[4,5],[4,5],[13],[3],[7,1],[6,1],[14],[13,7],[6,7],[15,1],[6,1],[8,6]]),
 ([c1,c0,c2,c3,c29,c5,c4],[(0,[(1,1,2)]),(6,[(1,1,3)]),(33,[]),(3,[(1,0,2)]),(2,[(1,1,2)]),(17,[]),(34,[]),(31,[]),(19,[(1,0,1)]),(25,[]),(8,[(1,0,1)]),(28,[]),(8,[]),(6,[]),(13,[(1,0,1)]),(11,[]),(22,[]),(10,[(1,1,2)]),(0,[(2,1,2)]),(4,[]),(10,[])],[(5,6),(4,7),(1,17),(1,33),(4,6),(3,9),(1,9),(3,17),(3,33),(5,17),(3,7),(5,33),(8,24),(12,36),(18,34)],[l1,[0,2,3,1,4],[0,3,4],[5],[0,1002,6],[0,7,1003,8],[4,9,1004,10],[3,1,1005,2,1006],[11,10,12,6,1,13],[6,2,1002,11,1,1007,1004],[14,2,1003,7,1,1008,1004],[3,0,1,4],[15],[4,1009,16,1010],[4,17,1011,10,1010],[3,18],[3,1012,6],[3,7,1013,8,1006],[19,2,1002],[8,11,12,17,2,20],[8,6,1002,7,11,1014,1003]]),
 ([c27,c1,c0,c2,c6,c3,c5,c4],[(0,[]),(6,[]),(8,[]),(0,[(0,1,2)]),(0,[(1,1,2)]),(4,[(1,0,2)]),(35,[]),(26,[]),(0,[(2,1,2)]),(6,[(3,1,3)]),(3,[(1,0,2)]),(36,[]),(22,[]),(28,[]),(37,[]),(38,[])],[],[[0,1],[2,1],[1,0],[3],[4],[5,6,7],[2,6,7],[7,6],[8,6],[9],[8,10],[7,6],[7,6],[7,11],[7,6],[6,7],[12,13],[14,15],[8],[6,8],[7,11],[7,11],[10],[7,6],[7,6],[6,7],[6,7],[12,13]]),
 ([c27,c1,c0,c2,c3,c5,c4],[(0,[]),(0,[(2,1,2)]),(3,[(1,0,2)]),(6,[(3,1,3)]),(8,[]),(28,[]),(22,[]),(6,[]),(0,[(1,1,2)]),(4,[]),(26,[]),(35,[]),(10,[]),(14,[(2,0,1)]),(2,[(2,1,2)]),(39,[]),(40,[]),(19,[(2,0,1)]),(23,[]),(8,[(2,0,1)]),(13,[(2,0,1)]),(30,[]),(10,[(2,1,2)])],[(1,17),(8,24),(5,6),(4,7),(8,9),(1,33),(4,6),(18,24),(16,24),(3,17),(3,33),(8,12),(5,17),(5,33),(10,34),(18,34)],[[0,1,2,3],[4,5,3,6,7],[1,2],[2,8],[9,10,11,1000,1001],[4,5,12,6],[1,3,1002,13,1003],[1,2,3,14],[1,2,1004],[1,1000,15],[1,16,1005,17],[5,14,18,1006,19],[2,3,1007,13,1008],[6,13,1000,5,3,1009,1006],[20,13,1005,16,3,1010,1006],[2,14,1011],[6,3,14,1012,1011],[14,16,1013,19,1011],[2,21,1001],[2,22,1014,17,1008],[17,6,1000,16,5,1015,1005]]),
 ([c1,c0,c2,c6,c3,c5,c33,c4],[(0,[(1,1,3)]),(22,[]),(6,[(1,2,3)]),(25,[]),(2,[(3,1,3)]),(2,[(1,1,3)]),(31,[]),(28,[]),(33,[]),(8,[]),(6,[]),(0,[(3,1,3)]),(30,[]),(4,[(1,0,2)]),(3,[(1,0,2)]),(29,[]),(0,[(2,1,3)])],[],[[0,1],[0,1],[2],[0,3],[0,3],[4],[0,1],[5,3,6],[7,1],[1,3,8],[1,3,7],[9,1,10],[8,3],[0],[1,6,5],[1,0,5],[11],[5,8],[12,3],[13],[4],[7,1],[13,12],[14,3],[1,6,15],[16],[1,6,7],[9,1,15]]),
 ([c1,c0,c2,c3,c5,c33,c4],[(0,[(1,1,3)]),(6,[(1,2,3)]),(33,[]),(4,[(1,0,2)]),(2,[(1,1,3)]),(36,[]),(18,[]),(31,[]),(19,[(1,0,2)]),(25,[]),(8,[(1,0,2)]),(29,[]),(8,[]),(6,[]),(13,[(1,0,2)]),(22,[]),(12,[]),(10,[(1,1,3)]),(3,[]),(0,[(2,1,3)]),(10,[])],[(5,6),(4,7),(1,9),(1,33),(4,6),(3,9),(3,17),(1,17),(3,33),(5,9),(3,7),(5,33),(16,24),(10,34),(20,36)],[l1,[0,2,3,1,4],[0,1002,5],[0,3,4],[6],[0,7,1003,8],[4,9,1004,10],[5,2,1002,11,1,1005,1004],[3,1,1006,2,1007],[11,10,12,5,1,13],[14,2,1003,7,1,1008,1004],[4,1009,15,1010],[3,0,1,4],[16],[4,17,1011,10,1010],[3,1012,5],[18,2,1002],[8,5,1002,7,11,1013,1003],[3,19],[3,7,1014,8,1007],[8,11,12,17,2,20]]),
 ([c34,c1,c0,c2,c6,c3,c5,c4],[(0,[]),(4,[(1,0,2)]),(6,[]),(8,[]),(3,[(1,0,2)]),(34,[]),(30,[]),(0,[(1,1,3)]),(22,[]),(0,[(2,1,3)]),(6,[(3,2,3)]),(41,[]),(29,[]),(42,[]),(38,[])],[],[[0,1,2],[3,2],[1,0],[1],[4,5,6],[7],[3,5,6],[6,8],[9,8],[10],[6,11],[1,9],[6,8],[6,5],[6,5],[8,12],[1,6],[13,14],[9],[6,5],[1,9],[6,5],[6,5],[1],[6,5],[1,6],[8,12],[1,6]]),
 ([c34,c1,c0,c2,c3,c5,c4],[(0,[]),(0,[(2,1,3)]),(4,[(1,0,2)]),(6,[(3,2,3)]),(8,[]),(29,[]),(22,[]),(6,[]),(3,[]),(30,[]),(34,[]),(0,[(1,1,3)]),(10,[]),(14,[(2,0,2)]),(2,[(2,1,3)]),(43,[]),(44,[]),(19,[(2,0,2)]),(24,[]),(8,[(2,0,2)]),(13,[(2,0,2)]),(26,[]),(10,[(2,1,3)])],[(1,9),(16,24),(5,6),(4,7),(16,17),(1,33),(4,6),(3,9),(10,24),(8,24),(3,33),(5,9),(3,7),(16,20),(5,33),(10,34),(18,34)],[[0,1,2,3],[4,5,3,6,7],[1,2],[8,9,10,1000,1001],[2,11],[4,5,12,6],[1,3,1002,13,1003],[1,2,3,14],[1,1000,15],[1,2,1004],[1,16,1005,17],[5,14,18,1006,19],[6,13,1000,5,3,1007,1006],[2,3,1008,13,1009],[20,13,1005,16,3,1010,1006],[6,3,14,1011,1012],[2,14,1013],[14,16,1014,19,1012],[2,21,1001],[17,6,1000,16,5,1015,1005],[2,22,1016,17,1009]]),
 ([c1,c0,c2,c6,c3,c5,c7,c4],[(0,[(1,2,3)]),(22,[]),(6,[(1,1,2)]),(3,[(1,0,2)]),(4,[(1,0,2)]),(45,[]),(2,[(1,2,3)]),(30,[]),(26,[]),(46,[]),(47,[]),(21,[])],[],[[0,1],[0,1],[2],[0,3],[0,4],[0,5],[0,1],[6,5],[7,1],[1,8],[1,7],[1,7],[9,10],[0],[1,6],[1,6],[1,6],[6,5],[3,7],[4,8],[11],[7,1],[3,4],[4],[1,8],[3],[1,7],[1,7]]),
 ([c0,c2,c3,c14,c5,c17,c4],[(2,[(1,1,2),(1,1,3)]),(8,[]),(48,[]),(25,[]),(3,[(1,0,3)]),(28,[]),(1,[(1,0,2)]),(6,[(1,2,3)]),(22,[]),(4,[(1,0,3)]),(29,[]),(1,[(1,0,1)]),(6,[(1,1,3)]),(13,[]),(1,[(1,0,1),(1,0,2)]),(10,[]),(11,[]),(2,[(1,1,3)]),(12,[]),(2,[(1,1,2)]),(5,[(1,2,3)]),(5,[(1,1,3)])],[(8,12),(2,6),(3,9),(1,9),(5,7),(4,6),(3,17),(1,17),(3,33),(1,33),(5,17),(3,7),(5,33),(8,9),(10,42),(16,17),(2,34),(18,50)],[[0,1,1000,2,3,1001],[4,3,1002,1,1003],[5,1,6,2,7,1004,1005],[8,1,9,3,1006,1007],[10,1,11,2,12,1004,1005],[13,14,1004,15,3,1008,1009],[4,2,1000,0],[16,0,17,3,1000,1001],[8,0,9,2,1010,1007],[18,0,19,3,1011,1000],[1,0,1000,15,2,1012,1009],[1],[4,9],[4,2,9,18,1013],[1,4,15,1014],[9,2,4,16,1015],[4,9],[1,5,20,15,2,1009,1016],[1],[1,8,9,15,1017],[1,10,21,15,2,1009,1014]]),
 ([c1,c0,c2,c19,c3,c14,c5,c4],[(0,[(1,0,1)]),(6,[(1,1,3)]),(1,[(1,0,1)]),(25,[]),(14,[(1,0,1)]),(2,[(3,1,2)]),(0,[(3,0,1)]),(48,[]),(49,[]),(3,[(1,1,2)]),(23,[]),(4,[(1,1,2)]),(50,[]),(9,[])],[],[[0,1,2],[0,3],[0,1,4],[0,3],[5],[0,3],[0,3],[2,3],[6],[2,1],[2,1],[2,1],[2,1],[2],[1,7],[1,3,8],[1,7],[1,7],[4,1],[4,1],[4,1],[4,1],[0],[9,10],[8,10],[11,3,12],[8,3],[8,13,12]]),
 ([c1,c0,c2,c3,c14,c37,c5,c4],[(0,[(1,0,2)]),(3,[(1,0,1)]),(1,[(1,0,1)]),(25,[]),(3,[(3,0,1)]),(6,[]),(0,[(3,0,2)]),(48,[]),(6,[(1,1,3)]),(11,[]),(2,[(1,1,2)]),(51,[]),(0,[(2,0,2)]),(23,[]),(8,[]),(10,[]),(9,[])],[],[[0,1,2],[0,3],[0,1],[1],[4],[0,3],[0,3],[2,3],[1,0,2],[2,5],[6],[2,3],[2,3],[1,7,8],[5,3,9],[10,3,11],[8,7],[8,7],[0],[12],[1,13],[1,13],[2],[9,3],[9,3],[11,3],[14,3,15],[11,16]]),
 ([c1,c0,c2,c3,c14,c5,c72,c4],[(0,[(1,0,3)]),(6,[(1,1,3)]),(1,[(1,0,1)]),(25,[]),(6,[(2,1,3)]),(52,[]),(0,[(3,0,3)]),(3,[(1,1,3)]),(49,[]),(53,[]),(9,[]),(23,[]),(54,[]),(4,[]),(11,[]),(55,[])],[],[[0,1,2],[0,3],[0,3],[4],[0,3],[0,1,5],[0,3],[2,3],[2,1],[2,1],[2,1],[6],[2,1],[1,5,7],[1,3,8],[1,9,5],[5,3],[1,10,5],[0],[7,11],[7,1,12],[7,10,11],[13,3],[14,1,15],[8,3],[2],[8,9],[12,1]]),
 ([c1,c0,c2,c3,c14,c29,c5,c4],[(0,[(1,1,2)]),(23,[]),(48,[]),(3,[(1,0,2)]),(25,[]),(3,[(3,0,2)]),(2,[(1,1,2)]),(29,[]),(11,[]),(1,[(1,0,1)]),(28,[]),(56,[]),(40,[]),(0,[(2,1,2)]),(4,[(1,0,3)])],[],[[0,1,2],[0,3,4],[0,2],[3],[5],[0,2],[0,2],[6,1,2],[3,4,7],[8,2],[9,2,10],[7,1,10],[11,1,12],[3,0,1],[6,8],[8],[6,2],[6,2],[0],[13],[3,1],[3,1],[5],[8,1],[8,1],[14,1],[10,1],[7,10]]),
 ([c63,c1,c0,c2,c3,c5,c4],[(0,[]),(0,[(3,1,2)]),(3,[(2,0,2)]),(1,[]),(11,[]),(6,[]),(0,[(1,1,2)]),(4,[]),(9,[]),(8,[]),(6,[(1,1,3)]),(14,[(1,0,1)]),(2,[(1,1,2)]),(34,[]),(31,[]),(19,[(1,0,1)]),(49,[]),(8,[(3,0,1)]),(28,[]),(13,[(3,0,1)]),(53,[]),(9,[(3,0,1)])],[(1,17),(5,6),(4,7),(36,37),(8,9),(2,6),(0,6),(3,9),(1,9),(3,17),(4,6),(3,33),(1,33),(4,12),(6,18),(5,37),(8,24),(12,36),(18,34)],[[0,1,2],[3,4,5],[6,4],[1,2],[4,1000,7],[4,8,9],[1,10,1001,11,1002],[1,12,1003],[1,2,12],[1,1000,13],[1,14,1003,15,1004],[12,16,1005,17,1006],[2,10,1007,11,1008],[13,11,1000,18,10,1009,1010],[19,11,1010,14,10,1011,1012],[2,12,1013],[12,20,1014,16,1005],[12,21,1015,17],[2,1016,13],[2,14,1017,15,1008],[15,13,1000,14,18,1018,1012]]),
 ([c1,c0,c2,c3,c14,c5,c20,c4],[(0,[(1,1,3)]),(48,[]),(2,[(1,1,2)]),(3,[(1,2,3)]),(57,[]),(1,[(1,2,3)]),(6,[]),(28,[]),(54,[]),(58,[]),(53,[]),(0,[(3,1,3)]),(4,[]),(50,[]),(11,[]),(18,[])],[],[[0,1],[0,2],[0,1],[3],[0,1],[0,4],[0,1],[2,1],[3,4],[5,1,6],[4,7],[4,1],[8,9],[2,1],[2,10],[2,1],[11],[2,1],[0],[3,8],[3,1,8],[3,4],[12,1,13],[14,15],[7,1],[2],[4,7],[4,1]]),
 ([c1,c0,c2,c14,c5,c7,c4],[(0,[(1,2,3)]),(23,[]),(1,[(1,0,1),(1,1,2)]),(2,[(1,1,2),(1,2,3)]),(3,[]),(4,[(1,0,3)]),(21,[]),(40,[]),(5,[(1,1,3),(1,1,2)]),(59,[]),(11,[]),(1,[(1,1,2)]),(6,[(1,1,2)]),(1,[(1,0,1)]),(6,[(1,1,3)]),(2,[(1,2,3)]),(2,[(1,1,2)]),(5,[(1,1,2)]),(9,[(1,1,2)]),(5,[(1,1,3)]),(9,[])],[(5,7),(3,7),(1,9),(1,33),(8,12),(4,6),(10,24),(8,24),(3,9),(3,33),(2,6),(16,20),(5,33),(16,24),(2,34),(24,40)],[[0,1,1000,2],[0,1001,3],[4],[0,5],[0,1,5,6,1002],[0,7,1003,8],[3,2,1004,9,1,1000,1001],[10,2,11,7,12,1000,1005],[5,1,1006,2,1007],[6,2,13,7,14,1008,1000],[8,2,1000,7,1,1009,1003],[10,3,15,1,1001,1010],[5,1011,3],[6,3,16,1,9,1004,1001],[8,3,1001,7,9,1012,1003],[5,0,10,1013],[0,5],[8,10,17,18,1,1003,1014],[4],[5,7,1015,8,1007],[8,6,19,18,1,20]]),
 ([c1,c0,c2,c3,c14,c5,c76,c4],[(0,[(1,2,3)]),(23,[]),(48,[]),(25,[]),(3,[(1,0,3)]),(3,[(3,0,3)]),(28,[]),(40,[]),(4,[(1,0,3)]),(1,[(1,0,1)]),(60,[]),(54,[]),(53,[]),(0,[(3,2,3)]),(11,[])],[],[[0,1,2],[0,3],[0,2],[4],[0,2],[5],[0,2],[6,1,2],[4,3,7],[6,2],[8,1,6],[9,2,10],[11,1],[4,1],[10,1],[8,2,12],[10,1],[6,2],[0],[4,0,1],[13],[4,1],[8,14],[5],[6,1],[14],[8,6],[10,1]]),
 ([c1,c0,c2,c3,c5,c76,c4],[(0,[(1,2,3)]),(23,[]),(52,[]),(57,[]),(4,[(1,0,3)]),(3,[(1,0,3)]),(21,[]),(40,[]),(48,[]),(25,[]),(9,[(1,1,2)]),(60,[]),(1,[]),(6,[]),(13,[(1,1,2)]),(54,[]),(26,[]),(12,[]),(11,[]),(13,[]),(9,[])],[(5,7),(3,7),(1,33),(8,12),(3,9),(1,9),(3,17),(1,17),(3,33),(5,17),(2,6),(5,33),(10,42),(24,40)],[[0,1,1000,2],[0,1001,3],[0,1,4,5],[0,4,5],[6],[0,7,1002,2],[3,2,1003,8,1,1000,1001],[5,9,1004,10,1005],[3,4,1,1006,10,1007],[11,10,12,3,13],[14,15,1000,7,1,1008,1002],[5,8,1003,15],[2,4,8,1009,16,1007],[11,13,1,1001,1010],[2,3,1001,7,8,1011,1002],[4,0,5],[17],[5,10,1012,14],[18],[4,7,1013,14,1007],[14,11,19,10,1,20]]),
 ([0xffaa0000ffaa,c1,c0,c2,c3,c5,c4],[(0,[]),(0,[(2,2,3)]),(3,[(2,0,3)]),(1,[]),(11,[]),(6,[]),(0,[(1,2,3)]),(9,[]),(13,[]),(24,[]),(52,[]),(57,[]),(4,[(1,0,3)]),(44,[]),(50,[]),(9,[(2,1,2)]),(54,[]),(59,[]),(13,[(2,1,2)])],[(3,7),(5,7),(16,17),(1,33),(8,12),(3,9),(1,9),(34,48),(4,20),(3,33),(0,20),(5,33),(16,24),(10,42),(18,34)],[[0,1,2],[3,4,5],[4,1000,5],[1,2],[6,4],[4,7,8],[1,9,1001,10],[1,1000,11],[1,2,12],[1,9,1002,10,12],[1,13,1003,10],[11,10,1004,14,9,1000],[2,9,1005,15,1006],[11,12,1007,15,1008],[14,16,1001,13,9,1009,1003],[2,17,1004,16],[10,12,14,1008,1010],[10,11,1000,13,17,1011,1003],[2,9,1012,12],[2,13,1013,18],[12,15,1014,14,1008]]),
 ([c1,c0,c2,c19,c3,c5,c17,c4],[(0,[(1,0,1)]),(6,[(1,2,3)]),(1,[(1,0,2)]),(25,[]),(14,[(1,0,2)]),(1,[(3,0,2)]),(0,[(3,0,1)]),(48,[]),(49,[]),(4,[(1,1,2)]),(24,[]),(3,[(1,1,2)]),(61,[]),(9,[])],[],[[0,1,2],[0,3],[0,1,4],[0,3],[0,3],[5],[0,3],[2,3],[6],[2,1],[2,1],[2,1],[2,1],[2],[1,7],[1,7],[1,3,8],[1,7],[4,1],[4,1],[4,1],[4,1],[9,10],[11,3,12],[8,13,12],[0],[8,10],[8,3]]),
 ([c1,c0,c2,c3,c18,c5,c17,c4],[(0,[(1,0,2)]),(6,[(1,2,3)]),(1,[(1,0,2)]),(25,[]),(62,[]),(1,[(3,0,2)]),(0,[(3,0,2)]),(63,[]),(9,[]),(3,[(1,0,3)]),(24,[]),(4,[(1,1,3)]),(64,[]),(12,[]),(65,[])],[],[[0,1,2],[0,3],[0,3],[0,1,4],[0,3],[5],[0,3],[2,3],[2,1],[6],[2,1],[2,1],[2,1],[1,7,4],[4,3],[1,4,7],[1,3,7],[1,8,4],[2],[9,10,11],[9,3],[9,7],[11,1,12],[13,1,14],[12,1],[0],[7,8,10],[7,3]]),
 ([c1,c0,c2,c3,c5,c17,0xffffeeeeffffeeee,c4],[(0,[(1,0,3)]),(4,[(1,0,1)]),(1,[(1,0,2)]),(25,[]),(4,[(3,0,1)]),(6,[]),(0,[(3,0,3)]),(6,[(1,2,3)]),(48,[]),(12,[]),(2,[(1,1,3)]),(66,[]),(24,[]),(9,[]),(13,[])],[],[[0,1,2],[0,3],[0,3],[0,1],[1],[4],[0,3],[2,3],[2,3],[1,0,2],[2,5],[6],[2,3],[7,8],[1,8,7],[5,3,9],[10,3,11],[7,8],[1,12],[9,3],[11,3],[11,13],[0],[13],[1,12],[2],[9,3],[14,3,13]]),
 ([c1,c0,c2,c3,c16,c5,c17,c4],[(0,[(1,1,2)]),(48,[]),(2,[(1,1,3)]),(67,[]),(2,[(3,1,3)]),(29,[]),(64,[]),(68,[]),(0,[(3,1,2)]),(63,[]),(4,[(1,2,3)]),(3,[]),(61,[]),(12,[]),(17,[])],[],[[0,1],[0,2],[0,1],[0,3],[0,1],[4],[0,1],[2,1],[3,5],[3,1],[5,3],[5,1],[6,7],[2,1],[8],[2,1],[2,9],[2,1],[2],[6,10],[11,1,12],[3,5],[6,1],[13,14],[3,1],[0],[5,3],[5,1]]),
 ([c1,c0,c2,c3,c5,c17,c33,c4],[(0,[(1,1,3)]),(48,[]),(4,[(1,0,2)]),(2,[(1,1,3)]),(4,[(3,0,2)]),(54,[]),(24,[]),(25,[]),(53,[]),(12,[]),(9,[]),(29,[]),(3,[(1,0,3)]),(0,[(2,1,3)])],[],[[0,1],[0,2,3],[0,1],[0,1],[2],[4],[0,1],[3,1],[5,6],[2,7,8],[9,1],[10,1,11],[5,6],[3,1],[2,0,3],[3,9],[9],[3,1],[2,6],[9,1],[12,1],[8,11],[0],[13],[2,6],[3],[9,1],[11,1]]),
 ([0xf0f0a0a0f0f0a0a,c1,c0,c2,c3,c5,c4],[(0,[]),(0,[(3,1,3)]),(2,[(1,1,3)]),(4,[(2,0,2)]),(9,[]),(12,[]),(6,[]),(0,[(1,1,3)]),(3,[]),(13,[]),(6,[(1,2,3)]),(14,[(1,0,2)]),(36,[]),(31,[]),(19,[(1,0,2)]),(49,[]),(9,[(3,0,2)]),(29,[]),(13,[(3,0,2)]),(63,[])],[(1,9),(5,6),(4,7),(36,37),(16,17),(2,6),(0,6),(3,9),(4,6),(3,17),(1,17),(3,33),(1,33),(6,10),(4,20),(5,37),(16,24),(10,34),(20,36)],[[0,1,2,3],[4,5,6],[2,5,7],[5,1000,8],[1,2],[5,4,9],[1,10,1001,11,1002],[1,2,1003],[1,1000,12],[1,2,3],[1,13,1003,14,1004],[2,15,1005,16,1006],[12,11,1000,17,10,1007,1008],[3,10,1009,11,1010],[18,11,1008,13,10,1011,1012],[2,19,1013,15,1005],[2,3,1014],[2,16,1015,18],[3,1016,12],[14,12,1000,13,17,1017,1012],[3,13,1018,14,1010]]),
 ([c1,c0,c2,c3,c17,c7,c4],[(0,[(1,2,3)]),(24,[]),(1,[(1,0,2),(1,1,2)]),(2,[(1,1,3),(1,2,3)]),(3,[(1,0,3)]),(4,[]),(21,[]),(44,[]),(5,[(1,2,3),(1,1,2)]),(69,[]),(12,[]),(1,[(1,1,2)]),(6,[(1,1,2)]),(9,[]),(6,[(1,2,3)]),(2,[(1,2,3)]),(2,[(1,1,3)]),(5,[(1,1,2)]),(9,[(1,1,2)]),(5,[(1,2,3)])],[(5,7),(3,7),(1,17),(1,33),(8,12),(18,24),(16,24),(4,6),(3,17),(3,33),(5,33),(8,24),(10,42)],[[0,1,1000,2],[0,1001,3],[0,4],[5],[0,1,4,6,1002],[0,7,1003,8],[3,2,1004,9,1,1000,1001],[4,1,1005,2,1006],[10,2,11,7,12,1000,1007],[6,2,13,7,14,1008,1000],[8,2,1000,7,1,1009,1003],[4,1004,3],[10,3,15,1,1001,1004],[6,3,16,1,9,1004,1001],[8,3,1001,7,9,1010,1003],[4,0,10,1011],[5],[4,7,1012,8],[0,4],[8,10,17,18,1,1003,1012],[8,6,19,13,1]]),
 ([c1,c0,c2,c3,c5,c17,c76,c4],[(0,[(1,2,3)]),(24,[]),(48,[]),(25,[]),(4,[(1,0,3)]),(4,[(3,0,3)]),(29,[]),(3,[(1,0,3)]),(44,[]),(9,[]),(60,[]),(54,[]),(12,[]),(0,[(2,2,3)])],[],[[0,1,2],[0,3],[0,2],[0,2],[4],[5],[0,2],[6,1,2],[7,1,6],[4,3,8],[6,2],[9,2,10],[11,1],[7,2,11],[4,1],[10,1],[10,1],[6,2],[4,0,1],[7,12],[12],[7,6],[0],[13],[4,1],[5],[6,1],[10,1]]),
 ([c77,c1,c0,c2,c3,c5,c4],[(0,[]),(0,[(3,2,3)]),(4,[(2,0,3)]),(9,[]),(12,[]),(6,[]),(0,[(1,2,3)]),(5,[]),(23,[]),(52,[]),(57,[]),(3,[(1,0,3)]),(40,[]),(61,[]),(9,[(3,1,2)]),(64,[]),(69,[]),(13,[(3,1,2)])],[(3,7),(5,7),(8,9),(1,33),(8,12),(34,40),(4,12),(3,17),(1,17),(3,33),(5,17),(5,33),(8,24),(10,34),(24,40)],[[0,1,2],[3,4,5],[4,1000,5],[6,4],[1,2],[4,3,7],[1,8,1001,9],[1,1000,10],[1,8,1002,11],[1,2,11],[1,12,1003,9],[10,9,1004,13,8,1000],[11,1005,14,1006],[2,8,1007,14,1008],[13,15,1001,12,8,1009,1003],[11,13,1004],[2,16,1010,15,1008],[9,10,1000,12,16,1011,1003],[2,8,1012,11],[11,14,1013,13,1006],[2,12,1014,17,1008]]),
 ([c1,c0,c2,c3,c16,c5,c4,c45],[(0,[(1,1,2)]),(48,[]),(31,[]),(2,[(1,0,1)]),(70,[]),(3,[(3,0,4)]),(40,[]),(19,[]),(9,[(1,0,1)]),(5,[(1,0,1)]),(13,[(1,0,1)]),(0,[(3,1,2)]),(3,[(1,0,4)]),(4,[(1,0,4)]),(64,[])],[],[[0,1],[0,2,3],[0,1],[0,2,4],[0,1],[0,1],[5],[3,1],[4,6],[4,1],[4,7,8],[9,2],[10,1],[3,1],[11],[3,1],[3,1],[3,6,10],[3],[12,6],[7,2],[5,1,10],[13,1,14],[7,1,8],[10,8],[7,2],[10,1],[0]]),
 ([c1,c0,c2,c3,c5,c20,c4,c45],[(0,[(1,1,3)]),(48,[]),(31,[]),(2,[(1,0,1)]),(70,[]),(5,[(1,0,2)]),(19,[]),(9,[(1,0,2)]),(13,[(1,0,2)]),(0,[(3,1,3)]),(4,[(1,0,4)]),(44,[]),(3,[(1,0,4)]),(54,[])],[],[[0,1],[0,2,3],[0,1],[0,1],[0,2,4],[0,1],[5],[3,1],[4,6,7],[4,6,7],[4,1],[5,2],[8,1],[3,1],[3,1],[9],[3,1],[3,7,8],[10,11],[12,1,13],[5,2],[8,1],[3],[5,2],[8,1],[5,1,7],[8,7],[0]]),
 ([c1,c0,c2,c3,c5,c7,c4,c45],[(0,[(1,2,3)]),(22,[]),(40,[]),(3,[(1,0,4)]),(44,[]),(4,[(1,0,4)]),(70,[]),(3,[(3,0,4)]),(71,[]),(9,[(1,1,2)]),(5,[(1,1,2)]),(13,[(1,1,2)])],[],[[0,1],[0,1],[0,2,3],[0,4,5],[0,2,6],[0,1],[7],[6,8,9],[1,2],[1,4],[1,2],[10,2],[11,1],[1,2],[1,4],[1,2],[10,2],[11,1],[3,2],[5],[1,4,10],[3,4,11],[3],[1,2,10],[5,2,11],[1,9,10],[11,9],[0]]),
 ([c1,c0,c2,c19,c3,c5,c7,c4],[(1,[(1,1,2)]),(6,[(1,1,2)]),(45,[]),(0,[(1,2,3)]),(14,[(1,1,2)]),(23,[]),(24,[]),(19,[(1,1,2)]),(71,[]),(49,[]),(3,[(3,1,2)]),(3,[(1,1,2)]),(4,[(1,1,2)])],[],[[0,1],[1,2],[3,1,4],[2,5],[2,6],[2,5],[7,8,9],[0,5],[10],[0,1],[0,1],[0,1],[0,1],[0],[1,5,8],[1,6,8],[1,5,8],[1,2],[4,1],[4,1],[4,1],[4,1],[11,5],[12],[2,5],[11],[2,6],[2,5]]),
 (l10,[(0,[(1,0,2)]),(6,[]),(49,[]),(25,[]),(65,[]),(0,[(2,0,2)]),(4,[]),(9,[]),(5,[]),(62,[]),(46,[]),(7,[]),(72,[]),(54,[])],[(2,6),(8,24),(3,7),(1,9),(1,17),(1,33),(5,9),(5,17)],[[0,1],[0,1],[1,2,1000,3,4],[0,4,5],[4,1001,6],[4,7,8],[0,1,4],[0,1,1002],[0,4,1003],[0,9,1004,10],[0,7,1005],[1,4,11],[4,7,0,1],[4,1],[4,1],[1,4,1006],[1,9,1007,2,1000],[1,7,11],[4,12,1001,13],[4,7,11],[7,2,11]]),
 ([0xffcc0000ffcc,c1,c0,c2,c3,c5,c4],[(0,[]),(44,[]),(65,[]),(0,[(2,0,3)]),(3,[]),(0,[(0,0,3)]),(6,[]),(4,[(1,1,3)]),(4,[(2,1,3)]),(9,[]),(5,[]),(71,[]),(9,[(2,1,2)]),(58,[]),(64,[]),(19,[]),(49,[]),(7,[]),(3,[(2,1,3)]),(1,[(2,1,2)])],[(8,9),(2,6),(3,6),(1,17),(0,17),(1,33),(0,33),(6,10),(5,17),(5,33),(16,24),(10,34),(20,36)],[[0,1,2,1000],[2,3,4,5],[2,6,1001],[2,4,7,8],[6],[2,9,10],[2,6],[6,11,1002,12,1001],[2,13,1000,12],[7,14,1003,12,1004],[15,11,1005,16,1006],[2,6,17],[2,18,6,19],[2,1,6],[2,1,6],[2,6,1007],[6,1,1008,7],[6,1,1009,15,17],[2,1,1010,7],[2,1,1011,15],[7,12,1012,15]]),
 ([0x5555444455554444,c1,c0,c2,c3,c5,c4],[(0,[(1,0,3)]),(6,[]),(49,[]),(25,[]),(55,[]),(3,[]),(0,[(2,0,3)]),(9,[]),(5,[]),(52,[]),(46,[]),(7,[]),(47,[]),(64,[])],[(2,6),(16,24),(3,7),(1,9),(1,17),(1,33),(5,9),(5,17)],[[0,1],[0,1],[1,2,1000,3,4],[4,1001,5],[0,4,6],[4,7,8],[0,1,4],[0,1,1002],[0,9,1003,10],[0,4,1004],[0,7,1005],[1,4,11],[4,1],[4,7,0,1],[4,1],[1,9,1006,2,1000],[1,4,1007],[1,7,11],[4,12,1001,13],[7,2,11],[4,7,11]]),
 ([0xff00cc00ff00cc,c1,c0,c2,c3,c5,c4],[(0,[]),(52,[]),(55,[]),(0,[(2,0,2)]),(3,[(1,1,3)]),(3,[(3,1,3)]),(6,[]),(3,[(2,1,3)]),(9,[]),(5,[]),(71,[]),(9,[(3,1,2)]),(54,[]),(68,[]),(49,[]),(19,[]),(7,[]),(4,[(2,1,3)]),(1,[(3,1,2)])],[(16,17),(2,6),(3,6),(1,9),(0,9),(1,33),(0,33),(5,9),(6,18),(5,33),(8,24),(12,36),(18,34)],[[0,1,2,1000],[2,3,4,5],[2,6,1001],[4,2,6],[2,4,7],[2,8,9],[1,2,6],[6,10,1002,11,1001],[4,12,1003,11,1004],[1,2,13,1000,11],[1,14,15,10,1005,1006],[2,6,16],[2,4,6],[2,17,4,18],[2,6],[4,6,1007],[1,2,6,1008],[1,6,11,1009,16],[2,4,1010],[4,11,1011,15],[2,11,1012,15]]),
 ([c1,c0,c2,c3,c5,c7,c4,c73],[(1,[(1,1,2)]),(19,[(1,1,2)]),(71,[]),(9,[(1,1,2)]),(52,[]),(3,[(1,1,4)]),(44,[]),(70,[]),(3,[(3,1,4)]),(4,[(1,1,4)]),(8,[(1,1,2)])],[],[[0,1],[1,2,3],[3,4,5],[3,6,4],[3,4,7],[1,2,6],[4,1],[0,2],[0,1],[0,1],[0,1],[0,2],[8],[1,4,2],[1,6,2],[1,4,2],[4,3],[4,2],[5,9],[9],[1,3],[5,1,10],[5],[1,3],[9,1,10],[1,3],[10,1],[0]]),
 ([c1,c0,c2,c3,c16,c29,c5,c4],[(0,[(1,1,2)]),(23,[]),(52,[]),(3,[(1,0,2)]),(2,[(1,1,2)]),(17,[]),(64,[]),(40,[]),(1,[(1,1,3)]),(19,[]),(3,[(2,0,2)]),(48,[]),(2,[(2,1,2)]),(4,[(1,2,3)]),(28,[]),(46,[])],[],[[0,1,2],[0,3,4],[0,1,3],[0,5],[5],[0,6],[0,6],[2,1],[3,7],[5,7],[8,7,9],[6,1],[6,1],[3,1],[3],[10],[2,11,4],[2,7],[4],[12],[3,1],[3,1],[0],[5,1],[5,1],[13,1],[9,1,14],[15,7,14]]),
 ([0x5550555055505550,c1,c0,c2,c3,c5,c4],[(0,[(1,1,2)]),(17,[]),(3,[(1,0,2)]),(19,[]),(9,[]),(4,[]),(19,[(3,0,1)]),(14,[(3,0,1)]),(67,[]),(70,[]),(71,[]),(9,[(1,0,1)]),(13,[(1,0,1)]),(3,[(3,0,2)]),(2,[(3,1,2)]),(54,[])],[(4,20),(5,7),(3,7),(1,9),(1,17),(1,33),(3,9),(3,17),(3,33),(5,33),(8,24),(12,36),(18,34)],[[0,1,2],[1,3,4],[0,1,2],[0,1,3],[1,1000,5],[1,4,3],[0,6,1001,7],[0,1,1002],[0,1,1003],[0,8,1004,9],[0,9,1005,6],[1,10,1001,11],[1,6,1006,7,1003],[9,7,1000,8,6,1007,1001],[12,7,1001,9,10,1008,1005],[1,13,0,14],[1,1000,10],[1,11,1009,12,1002],[1,1010,15],[1,11,1011,6,1003],[6,10,1000,11,8,1012,1005]]),
 ([c1,c0,c3,c16,c5,c20,c4],[(52,[]),(0,[(1,1,2),(1,1,3)]),(19,[]),(48,[]),(3,[(1,2,3)]),(70,[]),(0,[(1,1,3)]),(4,[(1,2,3)]),(0,[(1,1,2)]),(46,[]),(1,[(1,1,3),(1,2,3)]),(1,[(1,2,3)]),(1,[(1,1,3)]),(5,[(1,0,1),(1,0,2)]),(6,[]),(18,[]),(31,[]),(17,[]),(5,[(1,0,2)]),(9,[(1,0,2)]),(5,[(1,0,1)]),(9,[(1,0,1)])],[(4,6),(5,6),(4,7),(8,9),(16,17),(1,33),(0,33),(40,42),(16,22),(48,50),(8,12),(12,36),(4,12),(16,20),(5,37),(20,36),(4,20)],[l4,[4,3,1003,1],[5,1,6,0,1003,1004],[0,1,7,3,1004],[5,1,8,9,1004,1003],[0,1,1003,5,3,1005,1006],[4,2,1007,10],[5,10,11,3,2,1000,1008],[5,7,2,1009,10],[5,0,12,3,2,1000,1007],[13,9,1000,5,14,1007],[2],[4,7],[4,3,7,15,1010],[2,4,16,1011,1012],[7,3,4,17,1013],[4,7],[2,17,18,19,3,1014,1005],[2],[2,7,16,1015,1016],[0,15,20,21,3,1014,1005]]),
 ([c1,c0,c2,c16,c5,c7,c4],[(1,[(1,1,3),(1,1,2)]),(0,[(1,1,2),(1,2,3)]),(19,[(1,1,2)]),(59,[]),(2,[(1,2,3)]),(70,[]),(0,[(1,2,3)]),(52,[]),(4,[(1,2,3)]),(0,[(1,1,2)]),(23,[]),(1,[(1,1,2)]),(1,[(1,1,3)]),(40,[]),(19,[]),(5,[(1,0,1),(1,1,2)]),(3,[]),(21,[]),(17,[]),(5,[(1,1,2)]),(9,[(1,1,2)]),(9,[(1,0,1)])],[(4,6),(5,6),(4,7),(36,37),(16,17),(16,26),(10,24),(8,24),(3,33),(1,33),(4,12),(5,37),(16,24),(24,40),(12,36)],[l4,[2,1,4,1003],[5,1,6,7,1003,1004],[5,1,8,1004],[5,1,9,7,3,1004,1003],[2,1,1004,5,3,1003],[4,10,1000,0],[5,0,11,3,2,1000,1005],[3,0,8,2,1006,1007],[5,0,12,13,2,14],[15,0,1000,5,10,1008,1009],[16],[4,8],[4,7,8,17,1010],[4,13,1011,7],[8,4,18,1012],[4,8],[2,18,19,20,3,1011,1009],[16],[2,3,8,13,1013,1007],[2,17,14,21,10,1014,1009]]),
 ([c1,c0,c2,c3,c16,c5,c78,c4],[(52,[]),(23,[]),(17,[]),(46,[]),(48,[]),(67,[]),(0,[(1,1,2)]),(70,[]),(40,[]),(3,[(1,2,3)]),(3,[(3,2,3)]),(19,[(1,1,2)]),(2,[(3,2,3)]),(19,[]),(73,[])],[],[[0,1],[2,3],[2,0],[2,0],[0,4,5],[6,0,7],[0,4,7],[0,1],[2,8],[2,4],[7,1,5],[7,4],[3,1],[9,0],[9],[0,4,2],[10],[0,3,2],[11],[2,1],[12],[2,1],[2,1],[10],[2,1],[2],[3,5],[13,1,14]]),
 ([c1,c0,c2,c3,c5,c78,c4],[(52,[]),(28,[]),(19,[(1,1,2)]),(48,[]),(2,[(1,2,3)]),(63,[]),(3,[(1,2,3)]),(61,[]),(4,[(1,2,3)]),(26,[]),(70,[]),(0,[]),(23,[]),(14,[(1,1,2)]),(9,[]),(19,[]),(21,[]),(40,[]),(18,[]),(31,[]),(17,[]),(73,[])],[(4,6),(5,6),(4,7),(36,37),(8,9),(16,17),(32,33),(18,24),(4,12),(10,24),(4,20),(3,33),(1,33),(5,37),(12,36),(20,36)],[l4,[2,4,1003,5],[6,3,1004,7],[0,8,3,1005,9],[10,11,0,1003,1006],[0,1,1004,10,3,1003],[1,0,4,12,1000],[1,6,2,1007,13,1008],[5,8,2,1009,13,1010],[10,13,14,1,2,15],[7,13,1000,10,12,1011,1012],[4,0,8,6],[0,2,4,6,8],[16],[0,1,4,17,1013],[6,4,7,8],[18],[2,1,6,19,1014,1008],[20],[2,5,8,17,1015,1010],[2,21,15,14,1]]),
 ([c30,c1,c0,c2,c3,c5,c4],[(0,[]),(70,[]),(52,[]),(17,[]),(19,[]),(9,[]),(3,[]),(3,[(1,2,3)]),(28,[]),(19,[(2,1,2)]),(59,[]),(63,[]),(61,[]),(4,[(1,2,3)]),(64,[]),(24,[]),(14,[(2,1,2)]),(3,[(2,2,3)]),(2,[(2,2,3)]),(44,[])],[(8,9),(5,6),(4,6),(36,37),(1,17),(0,17),(18,24),(4,12),(3,17),(3,33),(1,33),(16,20),(5,37),(16,24),(12,36),(18,34)],[[0,1,2,1000,3],[3,4,5],[3,4,6],[3,6,4],[7,3],[3,5,4],[2,8,1000,9,10,1001,1002],[1,3,1003,11],[1,3,10,1000,12],[1,13,14,1004,1005],[2,8,1000,1,10,1003],[1,2,3,15,1002],[1,3,9,1006,16,1007],[1,13,9,1008,14,1004],[12,14,1002,1,15,1009,1010],[3,17,13,18],[2,3,13,1011],[2,3,19,1012],[3,13,1013],[3,19,1014,9,1007],[9,10,13,1015,1004]]),
 ([c1,c0,c2,c3,c16,c5,c4,0xfffffffffff0fff0],[(52,[]),(19,[]),(31,[]),(3,[(1,2,4)]),(9,[]),(17,[]),(48,[]),(9,[(1,0,1)]),(0,[(1,1,2)]),(74,[]),(5,[(1,0,1)]),(14,[]),(3,[(3,2,4)]),(40,[])],[],[[0,1],[1,2],[3,0],[4,0,5],[0,6,7],[0,2],[8,0,9],[0,2,5],[3,1,7],[4,1],[7,1],[10,2],[11,1],[1,2],[3],[0,2,1],[0,3,5],[12],[1],[3,13],[1,2],[1],[5,2],[1,4],[1],[1,2],[9,2],[5]]),
 ([c1,c0,c2,c3,c16,c5,c4,0xffffffffffff0000],[(52,[]),(19,[]),(31,[]),(3,[(1,3,4)]),(0,[(1,3,4)]),(70,[]),(67,[]),(9,[(1,0,1)]),(5,[(1,0,1)]),(14,[]),(40,[]),(61,[]),(4,[]),(17,[]),(75,[]),(3,[(2,3,4)])],[],[[0,1],[1,2],[3,0],[4,0,5],[0,6],[0,2],[0,2],[0,2,5],[3,1,7],[5,1,2],[5,1,6],[8,2],[9,1],[1,2],[3],[0,2,1],[0,7],[0,7],[1],[3,10],[1,2],[3,2,11],[12,2],[1,7],[13,7,14],[1,2],[1],[15]]),
 ([c1,c0,c2,c3,c5,c20,c33,c4],[(0,[(1,1,3)]),(48,[]),(4,[(1,0,2)]),(2,[(1,1,3)]),(18,[]),(67,[]),(24,[]),(54,[]),(14,[]),(19,[]),(4,[(2,0,2)]),(3,[(1,2,3)]),(31,[]),(61,[]),(2,[(2,1,3)]),(29,[])],[],[[0,1],[0,2,3],[0,1],[0,1],[0,4],[4],[0,1],[3,1],[5,6,7],[2,5],[4,1],[8,1,9],[7,6],[3,1],[2,3],[2],[10],[3,1],[2,6],[4,1],[11,1],[5,12,13],[3],[14],[2,5],[0],[4,1],[9,1,15]]),
 ([0x5555505055555050,c1,c0,c2,c3,c5,c4],[(0,[(1,1,3)]),(18,[]),(4,[(1,0,2)]),(19,[]),(9,[]),(3,[]),(19,[(3,0,2)]),(14,[(3,0,2)]),(57,[]),(70,[]),(71,[]),(9,[(1,0,2)]),(61,[]),(4,[(3,0,2)]),(2,[(3,1,3)]),(13,[(1,0,2)]),(64,[])],[(4,12),(5,7),(3,7),(1,9),(1,17),(1,33),(3,9),(3,17),(3,33),(5,33),(16,24),(10,34),(20,36)],[[0,1,2],[1,3,4],[0,1,2],[1,1000,5],[0,1,3],[1,4,3],[0,6,1001,7],[0,1,1002],[0,8,1003,9],[0,1,1004],[0,9,1005,6],[1,10,1001,11],[9,7,1000,8,6,1006,1001],[1,6,1007,7,1004],[12,7,1001,9,10,1008,1005],[1,1000,10],[1,13,0,14],[1,11,1009,15,1002],[1,1010,16],[6,10,1000,11,8,1011,1005],[1,11,1012,6,1004]]),
 ([c1,c0,c2,c3,c20,c7,c4],[(14,[(1,1,2)]),(0,[(1,1,3),(1,2,3)]),(19,[(1,1,2)]),(69,[]),(2,[(1,2,3)]),(3,[(1,2,3)]),(18,[]),(0,[(1,2,3)]),(67,[]),(70,[]),(0,[(1,1,3)]),(24,[]),(1,[(1,2,3),(1,1,2)]),(1,[(1,1,2)]),(1,[(1,2,3)]),(19,[]),(5,[(1,0,2),(1,1,2)]),(4,[]),(21,[]),(44,[]),(5,[(1,1,2)]),(9,[(1,1,2)]),(9,[(1,0,2)])],[(4,6),(5,6),(4,7),(36,37),(8,9),(18,24),(16,24),(8,26),(3,33),(1,33),(4,20),(5,37),(8,24),(10,42)],[l4,[0,1,4,1003],[5,1004,1],[6,1,7,8,1003,1004],[9,1,10,8,3,1004,1003],[2,1,1004,9,3,1003],[4,11,1000,12],[3,0,5,2,1005,1006],[6,0,13,3,2,1000,1007],[9,0,14,8,2,15],[16,0,1000,9,11,1008,1009],[4,5],[17],[4,5,18,1010],[4,19,1011,16],[5,4,6,1012],[6],[2,3,5,19,1013],[4,5],[2,6,20,21,3,1011,1009],[2,18,15,22,8,1013,1009]]),
 ([c1,c0,c2,c3,c5,c20,c78,c4],[(61,[]),(24,[]),(48,[]),(2,[(1,2,3)]),(31,[]),(18,[]),(0,[(1,1,3)]),(70,[]),(28,[]),(29,[]),(4,[(1,2,3)]),(4,[(3,2,3)]),(2,[(2,2,3)]),(19,[]),(73,[])],[],[[0,1,2],[3,4],[0,2],[5,1],[5,1],[6,1,7],[8,2],[3,0],[7,1,9],[0,8],[5,0],[7,0],[0,1,4],[3,0],[3,2],[10],[11],[3,2],[0,1],[5,0],[5],[0,4],[3],[12],[5,1],[11],[5,1],[13,1,14]]),
 ([c79,c1,c0,c2,c3,c5,c4],[(0,[]),(18,[]),(19,[]),(9,[]),(4,[]),(4,[(1,2,3)]),(14,[(3,1,2)]),(28,[]),(19,[(3,1,2)]),(69,[]),(63,[]),(70,[]),(3,[(1,2,3)]),(54,[]),(26,[]),(23,[]),(52,[]),(50,[]),(4,[(2,2,3)]),(2,[(3,2,3)]),(40,[])],[(16,17),(5,6),(4,6),(36,37),(1,9),(0,9),(3,9),(10,24),(4,20),(3,33),(1,33),(8,12),(5,37),(8,24),(10,34),(20,36)],[[0,1,1000],[1,2,3],[1,2,4],[5,1],[1,4,2],[1,3,2],[6,7,1000,8,9,1001,1002],[1,1003,10],[11,12,13,1004,1005],[1,9,1000,14],[8,7,1000,11,9,1003],[1,15,1002,16],[7,6,12,8,1006,1004],[1,8,1007,6,1008],[17,6,1002,11,15,1009,1010],[1,10,1011,12],[1,18,12,19],[1,20,1012,16],[1,12,1013],[8,7,12,1014,1004],[1,20,1015,8,1008]]),
 ([c1,c0,c2,c3,c5,c20,c4,0xffffffffff00ff00],[(29,[]),(19,[]),(62,[]),(31,[]),(57,[]),(9,[(1,0,2)]),(5,[(1,0,2)]),(1,[(1,2,3)]),(9,[(3,0,2)]),(4,[(1,3,4)]),(44,[]),(3,[]),(50,[]),(18,[]),(76,[]),(4,[(2,3,4)])],[],[[0,1,2],[1,3],[2,4],[4,2],[4,2],[0,3,1],[2,3],[0,3],[5,0,1],[0,1,5],[0,1,3],[6,3],[7,0,1],[1,3],[1,3],[8],[0,5,2],[1,5,2],[9,10],[11,3],[1,3],[1],[1],[0,3,1],[9,3,12],[0,5,1],[13,5,14],[15]]),
 ([c1,c0,c2,c3,c5,c20,c4,0xfffffffffffff0f0],[(28,[]),(19,[]),(69,[]),(31,[]),(9,[(1,0,2)]),(48,[]),(18,[]),(0,[(1,1,3)]),(77,[]),(5,[(1,0,2)]),(1,[(1,2,3)]),(4,[(1,2,4)]),(4,[(3,2,4)]),(44,[])],[],[[0,1,2],[1,3],[4,5],[4,2],[4,3,6],[0,2],[7,3,8],[0,2],[0,1,4],[4,0,1],[4,0,1],[9,3],[10,0,1],[1,3],[1,2],[11],[0,2],[12],[2,13,6],[6,3],[0,3,1],[8,3],[1],[1,0,3],[1],[1,4],[1],[6]]),
 ([c38,c1,c2,c3,c5,c4],[(19,[]),(9,[]),(20,[]),(0,[(3,0,1)]),(5,[]),(2,[]),(5,[(2,0,4)])],[(1,6),(8,9),(16,17),(8,14),(0,6),(16,22),(1,9),(1,17),(16,24),(8,24)],[[0,1,2],[0,3,1,4],[0,1],[0,1],[0,4,5],[0,1,1000],[1,1001,1002],[1,1002,1001],[0,1,2],[0,1003,1004],[0,1005,1003],[0,6,1],[1006,1007,1008,1009],[0,1],[0,1]]),
 ([c1,c0,c2,c3,c5,c7,c4,c26],[(20,[(1,2,3)]),(19,[(1,1,2)]),(46,[]),(40,[]),(44,[]),(45,[]),(2,[(1,2,3)]),(5,[(1,1,2)]),(1,[(1,1,2)]),(3,[(1,2,4)]),(4,[(1,2,4)])],[],[[0,1],[1,2],[2,3],[2,4],[2,3],[1,0],[1,0],[0,5,6],[0,1],[0,1],[0,1],[2,3,7],[8,3],[1,3,9],[1,4,10],[1,3],[6,2],[7],[9,3],[10],[1,0],[1,0],[9],[1,0],[1,0],[1,0],[1,0],[6]]),
 ([c1,c0,c2,c3,c5,c7,c76,c4],[(0,[(1,2,3)]),(24,[]),(52,[]),(71,[]),(3,[(1,0,3)]),(21,[]),(40,[]),(44,[]),(1,[(1,1,2)]),(60,[]),(78,[]),(4,[(1,0,3)]),(4,[(2,0,3)]),(29,[]),(3,[(2,0,3)])],[],[[0,1,2],[0,3],[0,2,4],[0,1,2],[0,5],[5],[0,3],[2,1],[4,1,6],[5,7],[5,6],[8,6,9],[10,1,6],[3,2],[2,1],[3,1],[9,1],[2,6],[4,6],[11],[12],[3,7,13],[4],[14],[3,1],[0],[3,1],[9,1]]),
 ([c75,c1,c0,c2,c3,c5,c4],[(0,[(1,2,3)]),(21,[]),(3,[(1,0,3)]),(19,[]),(1,[]),(0,[(3,2,3)]),(9,[]),(46,[]),(70,[]),(9,[(1,1,2)]),(69,[]),(71,[]),(25,[]),(13,[(1,1,2)]),(48,[]),(54,[]),(26,[]),(3,[(3,0,3)]),(4,[(3,0,3)])],[(8,12),(5,6),(4,7),(3,6),(2,7),(1,9),(1,17),(1,33),(2,6),(3,9),(3,17),(3,33),(4,6),(5,17),(5,33),(10,42),(24,40)],[[0,1,2],[1,3,4],[1,1000,3],[0,1,5],[0,1,2],[1,6,3],[0,1001,7,1002],[0,7,1003,8,1004],[0,1,1005],[0,1,1006],[0,8,1007],[8,9,1000,10,11,1008],[1,12,1009,9,1005],[1,12,1010,9,1006],[13,7,1007,8,11,1011,1012],[1,14,1000,15],[1,10,1013,16,1006],[13,15,1000,9,7,1014,1007],[1,17,0,18],[1,9,1015,13],[1,9,1016,13,1006]]),
 ([c1,c0,c2,c3,c5,c7,0xffffffccffffffcc,c4],[(1,[(1,1,2)]),(19,[(1,1,2)]),(71,[]),(46,[]),(40,[]),(44,[]),(3,[(3,1,3)]),(2,[(1,2,3)]),(26,[]),(3,[(1,1,3)]),(19,[(3,1,2)]),(4,[(2,1,3)]),(3,[(2,1,3)])],[],[[0,1],[1,2,3],[3,4],[3,5],[3,4],[3,1],[1,2,4],[0,2],[0,1],[0,1],[0,1],[6],[0,2],[1,4,2],[1,5,2],[1,4,2],[7,2],[8,3],[9,4],[10],[11],[1,5],[9],[12],[1,4],[0],[1,8,2],[3,2]]),
 ([c1,c0,c2,c3,c5,c7,c78,c4],[(26,[]),(24,[]),(46,[]),(2,[(1,2,3)]),(40,[]),(0,[(1,2,3)]),(70,[]),(52,[]),(44,[]),(3,[(1,2,3)]),(21,[]),(4,[(1,2,3)]),(4,[(2,2,3)]),(3,[(2,2,3)]),(5,[(1,1,2)]),(73,[])],[],[[0,1,2],[3,2],[2,4],[0,1,2],[2,1],[5,1,6],[0,4,7],[0,1,7],[6,0],[6,8],[6,0],[6,0],[2,1],[3,4,9],[0,1,7],[3,10],[10],[0,2],[9,0],[11],[12],[2,0],[9],[13],[2,1],[3],[2,0],[14,0,15]]),
 ([0xf0f0f000f0f0f00,c1,c0,c2,c3,c5,c4],[(0,[]),(21,[]),(19,[]),(1,[]),(3,[(1,2,3)]),(4,[]),(9,[]),(46,[]),(26,[]),(19,[(1,1,2)]),(69,[]),(2,[(1,2,3)]),(71,[]),(60,[]),(48,[]),(61,[]),(70,[]),(14,[(1,1,2)]),(78,[]),(4,[(3,2,3)]),(3,[(3,2,3)]),(31,[])],[(8,9),(5,6),(4,6),(3,6),(2,6),(16,17),(1,33),(0,33),(18,24),(4,12),(10,24),(4,20),(3,33),(5,33),(12,36),(20,36)],[[0,1,1000],[1,2,3],[4,1],[1,2,5],[1,2,4],[1,6,2],[7,8,1000,9,10,1001,1002],[9,11,12,1003,13,1004],[1,14,1000,15],[1,10,1005,8],[9,8,1000,16,10,1006,1007],[8,11,12,1002],[1,9,1008,17,1009],[1,9,1010,17,1011],[15,7,1002,16,12,1012,1006],[1,11,1009],[1,10,1011,8,11],[11,1013,18,1004],[1,19,11,20],[1,21,1014,9,1009],[1,21,1015,9,1011]]),
 ([c1,c0,c2,c3,c5,c7,c4,0xffffffffffffff00],[(26,[]),(24,[]),(52,[]),(70,[]),(79,[]),(9,[(1,1,2)]),(0,[(1,2,3)]),(44,[]),(4,[(1,3,4)]),(3,[(1,3,4)]),(4,[(3,3,4)]),(3,[(3,3,4)]),(21,[])],[],[[0,1,2],[3,4,5],[3,2],[0,1,2],[3,1],[0,3,2],[6,1],[0,1,2],[3,0],[3,7],[3,0],[4,1,3],[4,0],[4,2],[0,1,2],[4,1],[0,5,2],[4,1],[8,1],[8],[9,0],[10],[9],[8,1],[11],[12,0],[10],[12]]),
 ([0xf0f0f0f0f000f00,c1,c0,c2,c3,c5,c4],[(0,[]),(9,[]),(70,[]),(46,[]),(76,[]),(19,[]),(4,[]),(20,[]),(62,[]),(10,[]),(78,[]),(80,[]),(61,[])],[(8,9),(8,24),(3,6),(1,17),(2,6),(4,12),(5,17)],[[0,1,2,1000,3,4],[1,2,5],[1],[4,5],[4,1001,6],[1,3,5],[1,7,5],[1,3,1002,2,5],[1,4,1000],[1,8,1003,2],[1,4,7],[1,5,1004],[1,4,5],[1,5],[1,4,9],[4,5,1005],[5,8,1006,10,1004],[1,4],[4,11,1001,12],[1,3,5],[1,3,4]]),
 ([0xffff0000ff00,c1,c0,c2,c3,c5,c4],[(0,[]),(9,[]),(70,[]),(44,[]),(76,[]),(19,[]),(0,[(2,2,3)]),(0,[(0,2,3)]),(20,[]),(10,[]),(81,[]),(4,[(1,3,4)]),(19,[(2,1,2)]),(50,[]),(3,[(3,3,4)]),(5,[(2,1,2)])],[(8,9),(8,12),(5,6),(3,6),(1,17),(2,6),(18,24),(3,17),(5,17),(16,24)],[[0,1,2,1000,3,4],[1,2,5,3],[4,1001,5],[4,6,5,7],[1],[1,4,5],[1,8,1002,9],[1,10,1003,2,1000],[1,4,1000],[1,3,1004,2],[1,4,8],[1,10,1005,2],[1,4,1006],[1,3,1007,2,11],[1,4,9],[4,10,1001,12],[11,13,1008,12,1004],[1,4],[4,3,1009,10,11],[1,4,14,15],[1,4]]),
 ([0xf0f0f0f0f0f0000,c1,c0,c2,c3,c5,c4],[(0,[]),(9,[]),(70,[]),(46,[]),(75,[]),(19,[]),(3,[]),(20,[]),(52,[]),(10,[]),(78,[]),(82,[]),(50,[])],[(16,17),(16,24),(3,6),(1,9),(2,6),(5,9),(4,20)],[[0,1,2,1000,3,4],[1,2,5],[1],[4,1001,6],[4,5],[1,3,5],[1,7,5],[1,3,1002,2,5],[1,8,1003,2],[1,4,1000],[1,4,7],[1,5,1004],[1,5],[1,4,5],[1,4,9],[5,8,1005,10,1004],[4,5,1006],[1,4],[4,11,1001,12],[1,3,4],[1,3,5]]),
 ([0xff00ff00ff0000,c1,c0,c2,c3,c5,c4],[(0,[]),(9,[]),(70,[]),(52,[]),(75,[]),(19,[]),(0,[(3,2,3)]),(0,[(0,2,3)]),(20,[]),(10,[]),(83,[]),(3,[(1,3,4)]),(61,[]),(19,[(3,1,2)]),(4,[(3,3,4)]),(5,[(3,1,2)])],[(16,17),(16,20),(5,6),(3,6),(1,9),(2,6),(3,9),(10,24),(5,9),(8,24)],[[0,1,2,1000,3,4],[1,2,5,4],[4,1001,5],[1],[4,6,5,7],[1,4,5],[1,8,1002,9],[1,10,1003,2,1000],[1,3,1004,2],[1,4,1000],[1,4,8],[1,10,1005,2],[1,11,1006],[1,4,1007],[1,4,9],[11,12,1008,13,1004],[3,4,10,1001,13],[1,4],[4,11,1009],[1,4],[1,4,14,15]])]
def d540 : List StD := dupD [
 ([c22,c1,c0,c2,c50,c3,c5],[(0,[(0,2,3)]),(19,[(0,1,2)]),(70,[]),(0,[(0,2,3),(0,0,4)]),(20,[(0,2,3)]),(46,[]),(2,[(0,2,3)]),(71,[]),(0,[(2,0,4),(0,2,3)]),(54,[]),(69,[]),(59,[]),(0,[(2,0,4),(2,2,3)]),(0,[(2,0,4),(3,2,3)])],[],[[0,1,2],[2,0,3],[4,5,6],[4,1],[4,1],[4,1],[4,1],[1,7,8],[2,8],[2,9,8],[2,10,8],[2,7,4],[2,1,4],[2,1,4],[2,1,4],[1,7],[1,11],[1,10],[12],[13],[10,9]]),
 ([c22,c1,c0,c2,c3,c5,c7],[(0,[(1,2,3)]),(19,[(1,1,2)]),(20,[(1,2,3)]),(0,[(1,2,3),(2,0,4)]),(0,[(1,2,3),(0,0,4)]),(46,[]),(2,[(1,2,3)]),(71,[]),(40,[]),(70,[]),(44,[]),(0,[(2,0,4),(3,2,3)]),(0,[(2,0,4),(2,2,3)])],[],[[0,1,2],[3,4],[2,5,6],[2,1],[2,1],[2,1],[2,1],[1,7,3],[3,8,9],[3,10,9],[3,8,9],[2,7],[2,1],[2,1],[2,1],[1,8,7],[1,10,7],[1,8,7],[10,8],[11],[12]]),
 ([c22,c64,c1,c0,c2,c3,c5],[(46,[]),(19,[]),(20,[]),(0,[(2,2,3)]),(20,[(2,2,3)]),(2,[(2,2,3)]),(19,[(2,1,2)]),(0,[(2,0,4)]),(84,[]),(70,[]),(71,[]),(0,[(2,0,4),(0,2,3)]),(0,[(2,0,4),(1,2,3)]),(0,[(2,0,4),(2,2,3)]),(44,[]),(69,[])],[(0,24)],[[0,1,2],[3,0],[0,3],[4,0,5],[0,6,4],[0,6,4],[7,8,9],[2,1],[1,8,10],[11],[12],[4,6],[6,10,13],[9,8],[8,14],[4,8],[4,6],[4,6],[6,8,10],[6,14,8],[15,14,1000]]),
 ([c22,c80,c1,c0,c2,c3,c5],[(71,[]),(19,[]),(20,[]),(0,[(3,2,3)]),(0,[(3,2,3),(2,0,4)]),(0,[(3,2,3),(0,0,4)]),(20,[(3,2,3)]),(46,[]),(2,[(3,2,3)]),(19,[(3,1,2)]),(85,[]),(70,[]),(0,[(2,0,4),(1,2,3)]),(0,[(2,0,4),(0,2,3)]),(40,[]),(54,[])],[(0,24)],[[0,1,2],[3,0],[4,5],[6,7,8],[0,9,6],[0,9,6],[4,10,11],[2,1],[0,10],[12],[13],[4,9,6],[4,0],[4,14,10],[4,10,11],[6,0],[6,9],[6,9],[0,14],[0,10],[15,14,1000]]),
 ([c75,c0,c21,c2,c3,c5,c4],[(20,[]),(19,[]),(72,[]),(71,[]),(0,[]),(0,[(3,2,3)]),(0,[(1,2,3)]),(0,[(2,2,3)]),(9,[(1,1,2)]),(25,[]),(46,[]),(70,[]),(59,[]),(54,[]),(23,[])],[],[[0,1],[0,1],[1,2,3],[4,2,5],[4,6,7],[1,0],[6],[8,2],[8,2],[8,9],[10,2],[8,2],[8,2],[8,9],[2,11],[3,12,13],[3,2],[13,8,10],[12,2],[3,8,14],[3,2]]),
 ([c0,c6,c3,c14,c5,c20,c4],[(52,[]),(69,[]),(29,[]),(46,[]),(19,[]),(28,[]),(71,[]),(3,[(1,2,3)]),(62,[]),(0,[(1,1,3)]),(54,[]),(59,[]),(50,[]),(18,[]),(0,[(2,1,3)])],[],[[0,1,2],[1,2],[3,1,4],[2,5],[2,1],[3,6],[7,0],[4,0,3],[0,1,8],[0,6,8],[0,1,2],[9],[1,10],[6,11,10],[1,2],[3,1,12],[13,3],[4,1,5],[14],[2,5],[2,1]]),
 ([c27,c0,c2,c6,c14,c5,c4],[(54,[]),(19,[(1,0,1)]),(0,[]),(0,[(0,1,2)]),(69,[]),(26,[]),(46,[]),(19,[(2,0,1)]),(59,[]),(28,[]),(71,[]),(0,[(2,1,2)]),(50,[])],[],[[0,1],[0,2],[3],[2,0],[0,4,5],[1,4,5],[5,4],[5,4],[6,4,7],[8,9],[0,10],[11],[7,6],[5,4],[0,4],[7,6],[5,4],[5,0],[6,4,12],[7,0,9],[0,9]]),
 ([c0,c2,c3,c14,c5,c33,c4],[(2,[(1,1,2),(1,1,3)]),(71,[]),(59,[]),(54,[]),(29,[]),(50,[]),(28,[]),(46,[]),(0,[(3,1,3)]),(0,[(1,1,3)]),(3,[]),(52,[]),(3,[(1,0,3),(1,2,5)]),(0,[(2,1,3)])],[],[[0,1,2],[3,4,5],[5,2],[2,6],[4,2],[3,1],[0,2],[0,1,7],[0,5],[8],[0,2],[9],[2,5],[10,2,11],[1,4],[5,12,7],[10,7,11],[6,1],[13],[1,6],[4,1]]),
 ([c34,c0,c2,c3,c14,c5,c4],[(52,[]),(59,[]),(19,[(1,0,1)]),(0,[]),(3,[]),(3,[(2,0,3)]),(3,[(0,0,3)]),(0,[(1,1,3)]),(28,[]),(29,[]),(54,[]),(71,[]),(19,[(2,0,2)]),(46,[]),(62,[]),(0,[(2,1,3)]),(26,[])],[],[[0,1,2],[0,3],[4,0],[5,0,6],[7],[0,1,8],[8,1],[8,9],[8,1],[1,8],[10,11],[10,1],[12,11,13],[11,14],[8,1],[15],[1,16],[8,9],[13,14],[8,1],[1,8]]),
 ([c0,c2,c6,c14,c5,c7,c4],[(28,[]),(71,[]),(59,[]),(54,[]),(19,[(1,0,1)]),(0,[(1,2,3)]),(19,[(1,1,2)]),(46,[]),(26,[]),(52,[]),(21,[]),(30,[]),(0,[(2,2,3)])],[],[[0,1,2],[0,2],[0,2],[2,0],[3,0,4],[3,1],[5],[6,1,7],[1,8],[1,2,3],[0,2],[6,7],[8,9],[10,2,9],[0,1],[7,5,11],[5,2],[0,1],[12],[1,0],[1,0]]),
 ([c0,c2,c6,c3,c5,c76,c4],[(26,[]),(71,[]),(59,[]),(54,[]),(28,[]),(46,[]),(19,[]),(0,[(1,2,3)]),(69,[]),(3,[(1,0,3)]),(52,[]),(0,[(3,2,3)]),(0,[(2,2,3)]),(20,[(1,0,1)])],[],[[0,1,2],[0,2],[3,0,4],[2,4],[5,0,6],[3,1],[7],[1,2,3],[0,8],[6,1,5],[0,2],[9,2,10],[0,8],[6,5],[0,1],[2,0,8],[11],[1,0],[12],[1,4],[6,0,13]]),
 ([0xffaa0000ffaa,c0,c2,c6,c3,c5,c4],[(46,[]),(19,[]),(19,[(2,0,2)]),(19,[(0,0,2)]),(0,[]),(0,[(1,2,3)]),(71,[]),(20,[(1,0,1)]),(28,[]),(59,[]),(29,[]),(0,[(2,2,3)]),(54,[]),(50,[]),(3,[(2,0,3)]),(52,[]),(62,[]),(30,[])],[],[[0,1],[1,0],[2,0,3],[0,4],[5],[1,6,7],[8,6,9],[8,9],[8,10],[9,8],[0,6],[11],[6,9,12],[6,13],[8,0],[14,9,15],[15,13,16],[8,0],[9,17],[0,10],[0,8]]),
 ([c0,c6,c3,c16,c5,c17,c4],[(28,[]),(59,[]),(29,[]),(46,[]),(71,[]),(62,[]),(52,[]),(0,[(2,1,2)]),(3,[(1,0,2),(1,0,3)]),(61,[]),(69,[]),(64,[]),(17,[]),(0,[(1,1,2)])],[],[[0,1],[0,2],[0,1],[1,0],[2,0],[3,4],[5,1,6],[5,4,6],[6,5],[6,3,5],[0,1],[7],[1,8],[3,1,9],[0,2],[4,10,11],[12,3],[0,1],[13],[1,0],[2,0]]),
 ([c0,c2,c3,c29,c5,c17,c4],[(28,[]),(71,[]),(52,[]),(29,[]),(46,[]),(0,[(3,1,2)]),(69,[]),(2,[(1,1,2),(1,1,3)]),(0,[(2,1,2)]),(59,[]),(21,[]),(62,[]),(0,[(1,1,2)])],[],[[0,1,2],[0,3],[0,3],[3,0],[2,0,3],[4,1],[1,2],[5],[1,6,7],[7,1,4],[0,4],[8],[6,9],[4,2],[0,3],[10,6,11],[10,2,11],[0,1],[12],[1,0],[2,0,3]]),
 ([c27,c0,c2,c3,c5,c17,c4],[(62,[]),(69,[]),(28,[]),(0,[]),(0,[(1,1,2)]),(21,[]),(29,[]),(46,[]),(71,[]),(52,[]),(2,[(2,1,2),(1,1,3)]),(30,[]),(0,[(2,1,2)])],[],[[0,1,2],[0,3],[4],[5,0],[5,0],[0,1,2],[2,1],[1,6],[6,2],[6,1],[7,8],[8,9],[8,1,10],[10,7],[2,1],[1,11],[7,9],[1,6],[12],[6,2],[6,1]]),
 ([c34,c0,c2,c6,c3,c17,c4],[(28,[]),(59,[]),(0,[(2,1,3)]),(0,[(0,1,3)]),(69,[]),(30,[]),(29,[]),(46,[]),(71,[]),(2,[(2,1,3)]),(61,[])],[],[[0,1],[2,3],[3],[4,1,5],[2,4],[0,1],[0,1],[0,1],[0,6],[6,0],[7,8],[2],[5,1],[9,7],[0,1],[5,1],[9,7],[0,1],[7,1,10],[0,6],[6,0]]),
 ([c0,c2,c6,c3,c17,c7,c4],[(2,[(1,1,3),(1,2,3)]),(71,[]),(69,[]),(28,[]),(29,[]),(9,[]),(19,[(1,0,2)]),(46,[]),(0,[(1,2,3)]),(30,[]),(62,[]),(21,[]),(26,[]),(0,[(3,2,3)])],[],[[0,1,2],[3,2],[2,4],[4,2],[5,3,6],[7,1],[8],[0,1],[0,1,7],[0,2],[0,2],[9,10],[0,7],[11,2,10],[3,1],[7,8,12],[13],[1,4],[5,2],[4,1],[1,3]]),
 ([c77,c0,c2,c6,c3,c5,c4],[(46,[]),(28,[]),(29,[]),(2,[]),(2,[(2,1,2)]),(2,[(0,1,2)]),(0,[(1,2,3)]),(71,[]),(69,[]),(0,[(3,2,3)]),(61,[]),(26,[]),(62,[]),(52,[])],[],[[0,1,2],[3,0],[4,0,5],[6],[0,6],[2,1],[1,7,8],[1,8],[1,2],[2,1],[0,7],[9],[7,10],[7,8,11],[1,0],[12,10,13],[11,8],[1,0],[8,11],[0,2],[0,1]]),
 ([c27,c1,c0,c6,c16,c5,c4],[(0,[(1,1,2)]),(2,[]),(28,[]),(69,[]),(0,[(1,1,2),(0,1,2)]),(26,[]),(2,[(2,1,2)]),(0,[(2,1,2)]),(71,[]),(29,[]),(61,[]),(46,[]),(30,[])],[],[[0,1],[2,3],[4],[1,0],[5,3],[2,3],[2,3],[6],[7,8],[5,3],[2,3],[2,3],[2,3],[9,2],[10,8,11],[7,8],[5,3],[2,3],[8,3,12],[2,3],[8,2]]),
 ([c1,c0,c3,c16,c5,c33,c4],[(0,[(1,1,2),(1,1,3)]),(69,[]),(59,[]),(71,[]),(2,[(3,1,3)]),(29,[]),(28,[]),(61,[]),(46,[]),(0,[(1,1,3),(2,1,2)]),(21,[]),(52,[]),(62,[]),(0,[(1,1,2),(2,1,3)])],[],[[0,1],[0,2],[0,3],[0,1],[4],[0,1],[1,5],[6,1],[2,6],[5,1],[7,3,8],[9],[1,2],[10,2,11],[1,5],[3,1,12],[10,3,11],[6,1],[13],[2,6],[5,1]]),
 ([c34,c1,c0,c3,c16,c5,c4],[(0,[(1,1,2)]),(2,[]),(52,[]),(61,[]),(29,[]),(21,[]),(0,[(1,1,2),(1,1,3)]),(71,[]),(59,[]),(0,[(2,1,3)]),(0,[(2,1,3),(1,1,2)]),(62,[]),(46,[]),(28,[]),(0,[(2,1,3),(2,1,2)]),(26,[])],[],[[0,1],[2,3,4],[5,2],[5,0],[6],[2,7,4],[3,8],[3,8],[9,7],[10,11,12],[4,7],[13,4],[11,3,7],[3,13],[3,7,12],[14],[3,15],[3,4,7],[7,11],[11,4,13],[4,13]]),
 ([c1,c0,c6,c16,c5,c7,c4],[(0,[(1,1,2),(1,2,3)]),(59,[]),(2,[(1,2,3)]),(71,[]),(46,[]),(28,[]),(9,[(1,0,1)]),(19,[]),(26,[]),(21,[]),(52,[]),(30,[]),(0,[(1,1,2),(2,2,3)])],[],[[0,1],[2],[0,3],[0,4],[0,1],[0,1],[5,1],[5,1],[1,5],[6,5,7],[4,3],[0,3],[8,9],[9,1,10],[5,1],[3,2,11],[2,1],[5,1],[12],[1,5],[3,5]]),
 ([c1,c0,c6,c3,c5,c78,c4],[(46,[]),(59,[]),(28,[]),(2,[(1,2,3)]),(30,[]),(69,[]),(26,[]),(0,[]),(71,[]),(9,[]),(2,[(3,2,3)]),(2,[(2,2,3)]),(19,[])],[],[[0,1,2],[3],[0,1,4],[0,5,6],[7,0,8],[2,1],[2,1],[2,6],[1,2],[9,1,8],[0,8],[4,1],[6,5],[7,8],[2,0],[1,3,4],[10],[0,6],[11],[0,2],[12,0,9]]),
 ([c30,c1,c0,c6,c3,c5,c4],[(0,[]),(71,[]),(28,[]),(9,[]),(0,[(2,1,3)]),(0,[(0,1,3)]),(2,[]),(2,[(1,2,3)]),(46,[]),(59,[]),(2,[(2,2,3)]),(30,[]),(64,[]),(29,[]),(21,[]),(62,[])],[],[[0,1],[2,1,3],[4,1,5],[1,6],[7],[2,3,8],[2,9],[10],[8,9,11],[8,12],[2,1],[2,9],[2,13],[9,2],[8,1],[11,9],[14,12,15],[2,1],[9,11],[1,13],[1,2]]),
 ([c1,c0,c3,c29,c5,c20,c4],[(0,[(1,1,2),(1,1,3)]),(59,[]),(2,[(3,1,2)]),(69,[]),(46,[]),(71,[]),(29,[]),(28,[]),(0,[(1,1,3),(2,1,2)]),(52,[]),(21,[]),(62,[]),(0,[(1,1,2),(2,1,3)])],[],[[0,1],[0,1],[2],[0,3],[0,4,5],[0,1],[3,6],[7,1],[1,7],[6,1],[4,5],[8],[1,3],[5,1,9],[3,6],[10,3,11],[10,5,11],[7,1],[12],[1,7],[6,1]]),
 ([c27,c1,c0,c3,c5,c20,c4],[(0,[(1,1,3)]),(2,[]),(28,[]),(69,[]),(0,[(1,1,3),(1,1,2)]),(21,[]),(62,[]),(0,[(2,1,2),(1,1,3)]),(52,[]),(46,[]),(71,[]),(29,[]),(30,[]),(0,[(2,1,2),(2,1,3)])],[],[[0,1],[2,3],[4],[5,3,6],[5,0],[2,3],[2,3],[7,8,9],[7,3],[7,9,10],[2,3],[2,11],[11,2],[8,2,10],[9,10],[3,12],[10,8],[2,11],[13],[9,2],[8,2,11]]),
 ([c34,c1,c0,c6,c3,c20,c4],[(0,[(1,1,3)]),(2,[]),(28,[]),(59,[]),(0,[(1,1,3),(0,1,3)]),(30,[]),(2,[(2,1,3)]),(0,[(2,1,3)]),(71,[]),(29,[]),(46,[]),(26,[])],[],[[0,1],[2,3],[4],[5,3],[1,0],[2,3],[2,3],[6],[5,3],[7,8],[2,3],[2,3],[2,9],[9,2],[10,8],[5,3],[7,8],[2,3],[8,3,11],[2,9],[9,2]]),
 ([c1,c0,c6,c3,c20,c7,c4],[(0,[(1,1,3),(1,2,3)]),(69,[]),(2,[(1,2,3)]),(46,[]),(71,[]),(29,[]),(9,[(1,0,2)]),(19,[]),(30,[]),(62,[]),(21,[]),(26,[]),(0,[(1,1,3),(3,2,3)])],[],[[0,1],[2],[0,3],[0,3,4],[0,1],[0,1],[5,1],[1,5],[5,1],[6,5,7],[3,4],[8,9],[0,4],[10,1,9],[5,1],[4,2,11],[12],[1,5],[2,1],[5,1],[3,5]]),
 ([c79,c1,c0,c6,c3,c5,c4],[(0,[]),(46,[]),(71,[]),(29,[]),(28,[]),(0,[(2,1,2)]),(0,[(0,1,2)]),(2,[(1,2,3)]),(69,[]),(2,[(3,2,3)]),(54,[]),(26,[]),(21,[]),(52,[])],[],[[0,1,2],[3,2,4],[5,2,6],[7],[2,7],[3,1],[1,8,3],[9],[1,10],[1,8,11],[3,2],[3,8],[4,3],[3,4],[1,2],[12,10,13],[11,8],[3,1],[8,11],[1,3],[1,4]]),
 ([c27,c1,c0,c2,c29,c5,c4],[(0,[(1,1,2)]),(2,[(1,1,2)]),(29,[]),(69,[]),(26,[]),(0,[(2,1,2),(1,1,2)]),(71,[]),(2,[(2,1,2),(3,1,2)]),(28,[]),(46,[]),(0,[(2,1,2),(3,1,2)]),(30,[])],[],[[0,1],[2,3],[1,0],[0],[4,3],[2,3],[2,3],[5,6],[7],[4,3],[2,3],[2,3],[8,2],[2,8],[9,6],[10],[4,3],[2,3],[3,11],[8,2],[2,8]]),
 ([c51,c1,c0,c2,c6,c3,c4],[(0,[]),(46,[]),(69,[]),(30,[]),(29,[]),(0,[(2,1,3)]),(0,[(0,1,3)]),(26,[]),(71,[]),(17,[(2,0,3)]),(2,[(1,1,2),(3,3,5)]),(72,[]),(0,[(1,1,2),(3,3,5)]),(54,[])],[(3,6)],[[0,1,2],[3,4],[5,2,6],[5,2,6],[2,7],[3,1],[1,2,3],[1000,1,8],[9],[1,10,3],[3,2],[3,2],[3,2],[2,4],[1,8],[11],[3,12,8],[3,1],[3,10,13],[3,1],[1,4]]),
 ([c1,c0,c2,c29,c5,c7,c4],[(0,[(1,1,2),(1,2,3)]),(59,[]),(46,[]),(2,[(1,1,2),(1,2,3)]),(2,[(1,2,3),(3,1,2)]),(28,[]),(54,[]),(19,[(1,0,1)]),(71,[]),(0,[(1,2,3),(3,1,2)]),(21,[]),(0,[(1,2,3),(1,1,5)]),(30,[]),(0,[(1,1,2),(2,2,3)])],[],[[0,1],[0,2,3],[4],[0,2],[0,1],[0,1],[3,1],[5,1],[1,5],[6,5,7],[2,8],[9],[3,8],[3,1],[3,1],[10,11,12],[10,1,12],[5,1],[13],[1,5],[2,5]]),
 ([c1,c0,c2,c3,0xfffa0000fffa0000,c29,c4],[(0,[(1,1,2),(0,3,5)]),(59,[]),(71,[]),(69,[]),(17,[(0,0,3)]),(2,[(1,1,2),(0,3,5)]),(29,[]),(19,[(1,0,1)]),(9,[(1,0,1)]),(28,[]),(54,[]),(78,[]),(26,[])],[],[[0,1],[0,2],[0,1],[0,3],[4],[0,1],[5,1],[3,6],[1,7,8],[9,1],[10,2],[2,0,5],[2,3,5],[11],[5,1],[1,12,3],[],[2,6],[],[1,8,7],[9,1]]),
 ([c1,c0,c2,c3,c5,0xfffffffafffffffa,c4],[(29,[]),(59,[]),(72,[]),(71,[]),(26,[]),(2,[(1,1,3),(1,2,5)]),(69,[]),(70,[]),(30,[]),(9,[]),(19,[]),(54,[]),(78,[])],[],[[0,1],[2,3],[2,1],[4,5,6],[7],[0,1],[0,1],[6,0],[0,8],[9,0,10],[11,2],[3,1,5],[3,2],[12],[0,1],[1,2],[],[3,0],[],[0,2],[10,0,9]]),
 ([c51,c1,c0,c2,c3,c5,c4],[(0,[]),(17,[]),(30,[]),(29,[]),(71,[]),(78,[]),(54,[]),(26,[]),(59,[]),(72,[]),(46,[]),(62,[])],[],[[0,1],[2,3],[1,4,5],[1,6,2],[7],[2,3],[2,8],[9,4],[2,6],[10,11],[2,4],[2,4,8],[6,3,9],[3,2],[6,4],[2,8],[4,9],[2,8],[6,2],[4,3],[3,2]]),
 ([c51,c1,c0,c2,c3,c29,c4],[(0,[(1,1,2)]),(46,[]),(17,[]),(9,[(1,0,1)]),(29,[]),(19,[(1,0,1)]),(71,[]),(69,[]),(54,[]),(26,[]),(21,[]),(0,[(1,1,2),(3,3,5)]),(17,[(2,0,3)]),(28,[]),(53,[]),(30,[])],[],[[0,1,2],[3,4,5],[2,6,7],[2,8,9],[10],[5,1,3],[1,7,4],[11,1,6],[1,8,11],[12],[4,6],[4,6,7],[7,4],[13,4],[1,6],[6,11,8],[14],[4,1],[15],[1,4],[13,1]]),
 ([c51,c1,c0,c2,c3,c4],[(0,[]),(62,[]),(17,[]),(46,[]),(9,[]),(30,[]),(19,[]),(29,[]),(69,[]),(71,[]),(11,[]),(26,[]),(54,[]),(38,[]),(23,[]),(17,[(2,0,3)]),(72,[]),(2,[(1,1,2),(3,3,5)]),(44,[]),(61,[]),(0,[(1,1,2),(3,3,5)])],[(1,9),(4,6),(5,6),(4,7),(3,6),(8,12),(3,7),(4,12),(8,9),(17,32),(2,34),(3,9),(1,33),(20,32),(24,32)],[[0,1,2,3],[4,5,6,7],[2,1,8,9,10],[2,5,11,12,1000,13],[6,5,4,3],[1,5,1001,14,8,1002,1003],[15,16,1004,3,9,1005,1006],[1,5,1007,14,12,17,1000],[1,5,1008,18,8,1009,1010],[5,1,17,9,1001],[8,12,1000,7,16,1011,1001],[19,3,1001,18,9,1010,1012],[1,5,17,14,20,1006],[1,5,17,18,1013,1005],[19,3,1000,18,7,1014,1010]]),
 ([c1,c0,c2,c3,c5,0xffff00faffff00fa,c4],[(30,[]),(69,[]),(72,[]),(71,[]),(52,[]),(46,[]),(44,[]),(29,[]),(0,[(0,2,3)]),(26,[])],[(1,25)],[[0,1],[2,3],[0,4,5],[4,1,6],[4,5],[0,1],[0,1],[1,2,7],[7,0],[7,0],[5,2],[0,4,3],[3,1,2],[4,2],[0,1],[1,0,1000],[8,0],[1,6,7],[9],[3,0],[7,0]]),
 ([0xfa000000fa,c1,c0,c2,c3,c5,c4],[(0,[]),(17,[]),(30,[]),(19,[]),(9,[]),(54,[]),(69,[]),(23,[]),(46,[]),(72,[]),(71,[]),(44,[]),(52,[]),(28,[]),(26,[]),(29,[])],[],[[0,1],[2,3,4],[1,0],[5],[6],[2,4,3],[2,7,8],[9,8,10],[2,7,8],[8,11],[2,10],[2,7,12],[13,9,14],[15,2],[8,7],[2,7,10],[10,9],[2,8],[2,7],[8,7],[8,2]]),
 ([c27,c80,c1,c0,c2,c5,c4],[(54,[]),(30,[]),(0,[(3,2,3)]),(19,[(3,1,2)]),(26,[]),(71,[]),(52,[]),(19,[(2,0,1)]),(28,[]),(0,[(2,1,2),(0,2,3)]),(23,[]),(0,[(2,1,2),(3,2,3)]),(29,[]),(46,[])],[(1,25),(16,25),(16,28)],[[0,1],[2,0],[0,3],[0,2],[0,1000,4],[1,5],[1,1001,6],[4,7,8],[1,1002,5],[9],[0,8],[1,10,6],[11,5],[4,6],[1,0],[1,5,6],[12,1],[0,5],[4,5],[0,13],[0,1]]),
 ([c34,c1,c0,c2,c3,c33,c4],[(0,[(1,1,3)]),(19,[(1,0,2)]),(26,[]),(9,[(1,0,2)]),(30,[]),(54,[]),(69,[]),(0,[(2,1,3),(1,1,3)]),(71,[]),(2,[(2,1,3),(3,1,3)]),(29,[]),(61,[]),(0,[(2,1,3),(3,1,3)])],[],[[0,1],[2,1,3],[1,0],[4,5],[0],[1,3],[2,6],[7,8],[4,5],[9],[2,5],[2,6],[5,2,6],[10,4],[5,8],[4,11],[12],[2,6],[2,4],[6,2],[10,4]]),
 ([c52,c1,c0,c2,c6,c5,c4],[(0,[]),(54,[]),(19,[]),(71,[]),(61,[]),(0,[(2,1,2)]),(0,[(0,1,2)]),(30,[]),(26,[]),(69,[]),(46,[]),(18,[(2,0,3)]),(72,[])],[(3,6)],[[0,1],[1,2],[1,3,4],[5,1,6],[1,7],[2,3,8],[4,9],[1000,10,3],[11],[8,9],[7,1],[7,3,4],[7,4],[4,7],[1,3],[12],[3,9,8],[1,9],[8,9],[7,1],[1,7]]),
 ([c1,c0,c2,c3,c33,c7,c4],[(0,[(1,1,3),(1,2,3)]),(69,[]),(71,[]),(46,[]),(2,[(1,2,3),(3,1,3)]),(26,[]),(29,[]),(9,[(1,0,2)]),(19,[(1,0,2)]),(2,[(1,1,3),(1,2,3)]),(0,[(1,2,3),(3,1,3)]),(17,[]),(0,[(1,1,3),(3,2,3)])],[],[[0,1],[0,2],[0,3],[4],[0,1],[0,1],[5,1],[1,5],[6,1],[7,5,8],[3,2],[2,9],[10],[2,1,8],[5,1],[11,5],[12],[1,5],[11,1,5],[6,1],[2,5]]),
 ([c1,c0,c2,0xff00fa00ff00fa00,c5,c33,c4],[(0,[(1,1,3),(0,2,5)]),(69,[]),(71,[]),(54,[]),(18,[(0,0,3)]),(2,[(1,1,3),(0,2,5)]),(19,[(1,0,2)]),(29,[]),(30,[]),(61,[]),(78,[]),(9,[(1,0,2)])],[],[[0,1],[0,2],[0,3],[0,1],[4],[0,1],[5,1],[1,6,3],[7,8],[7,1],[3,2],[2,9,3],[2,0,5],[10],[3,1],[1,8,3],[],[1,11,6],[],[2,8],[7,1]]),
 ([c52,c1,c0,c2,c5,c33,c4],[(0,[(1,1,3)]),(46,[]),(54,[]),(19,[(1,0,2)]),(71,[]),(61,[]),(30,[]),(17,[]),(29,[]),(69,[]),(0,[(1,1,3),(3,2,5)]),(18,[(2,0,3)]),(2,[(1,1,3),(3,2,5)]),(63,[]),(26,[])],[],[[0,1,2],[2,3],[2,4,5],[2,6],[7],[3,1,8],[1,9,5],[10,1,4],[1,9,10],[11],[6,2],[6,4,5],[5,6],[8,5],[1,4],[4,9,12],[13],[2,1],[14],[1,6],[8,1]]),
 ([c52,c1,c0,c2,c3,c5,c4],[(0,[]),(18,[]),(26,[]),(19,[]),(69,[]),(71,[]),(78,[]),(61,[]),(63,[]),(46,[]),(52,[]),(28,[])],[],[[0,1],[2,3,4],[1,5,6],[7],[1,4,2],[2,4],[2,4],[8,5],[9,10],[2,4],[2,4],[2,4],[4,2],[8,11],[9,5],[5,8],[2,4],[2,4],[4,2],[4,2],[5,11]]),
 ([c52,c1,c0,c2,c5,c4],[(0,[]),(52,[]),(18,[]),(46,[]),(54,[]),(26,[]),(9,[]),(19,[]),(69,[]),(61,[]),(71,[]),(12,[]),(30,[]),(38,[]),(23,[]),(18,[(2,0,3)]),(63,[]),(2,[(1,1,3),(3,2,5)]),(44,[]),(64,[]),(0,[(1,1,3),(3,2,5)]),(50,[]),(40,[])],[(1,17),(4,6),(5,6),(4,7),(3,6),(0,12),(3,7),(0,9),(16,17),(9,32),(2,34),(3,17),(1,33),(12,32),(24,32)],[[0,1,2,3],[4,5,6,7,8],[2,1,9,10,11],[2,5,12,8,1000,13],[7,5,6,3],[1,5,1001,14,8,1002,1003],[15,16,1004,3,10,1005,1006],[1,5,1007,17,18,1008,8],[1,5,1007,18,4,1009,1010],[5,1,17,10,1001],[9,19,1000,12,14,1011,1001],[9,3,1001,18,10,1010,1012],[1,5,17,18,20,1005],[1,4,17,18,1013,1005],[21,3,1000,22,12,1014,1010]]),
 ([c1,c0,c2,c3,0xff00fffaff00fffa,c5,c4],[(61,[]),(23,[]),(46,[]),(63,[]),(71,[]),(0,[]),(19,[(3,0,1)]),(62,[]),(54,[]),(28,[]),(30,[]),(0,[(0,2,3)])],[(1,25)],[[0,1,2],[3,2,4],[0,1,2],[5,1,6],[2,7],[3,4],[7,0,1],[8,3,9],[9,0],[0,1,9],[0,1,2],[4,0,1],[6,1,7],[3,7],[7,2,8],[10],[0,1,1000],[0,1,2],[11,1],[6,1,9],[2,9]]),
 ([c34,c64,c1,c0,c2,c3,c4],[(26,[]),(69,[]),(0,[(2,2,3)]),(19,[(2,1,2)]),(64,[]),(30,[]),(71,[]),(46,[]),(19,[(2,0,2)]),(9,[(2,0,2)]),(0,[(2,1,3),(0,2,3)]),(0,[(2,1,3),(2,2,3)])],[(1,25),(8,25),(8,28)],[[0,1],[2,1],[0,3,4],[3,1],[1,1000,5],[0,6],[0,1001,7],[1,8,9],[0,1002,6],[10],[1,9,8],[0,1],[11,6],[5,7],[0,1],[0,1],[1,0],[4,6],[5,6],[0,1],[1,0]]),
 ([c63,c0,c2,c3,c5,c17,c4],[(61,[]),(19,[(1,0,2)]),(9,[]),(0,[(1,1,2)]),(69,[]),(64,[]),(46,[]),(62,[]),(18,[]),(28,[]),(29,[]),(49,[]),(54,[]),(19,[(1,0,1)]),(0,[(3,1,2)])],[],[[0,1,2],[3],[0,2,1],[4,5],[6,7,8],[1,2],[9,0],[4,10],[0,9],[0,4],[0,11,5],[11,0,12],[5,4],[11,6,13],[5,4],[0,4],[0,12],[0,10,4],[14],[6,9],[10,4]]),
 ([0xf0f0a0a0f0f0a0a,c0,c2,c3,c14,c5,c4],[(69,[]),(19,[(1,0,1)]),(28,[]),(0,[(1,1,3)]),(17,[]),(54,[]),(23,[]),(29,[]),(49,[]),(63,[]),(64,[]),(0,[(3,1,3)]),(46,[]),(50,[])],[],[[0,1,2],[3],[4,5,6],[4,6],[0,3,1],[0,2],[2,0],[0,7],[2,0],[7,2],[5,8],[5,9,8],[8,9],[8,0,10],[2,0],[11],[0,5],[0,7],[12,0,13],[2,0],[5,2]]),
 ([c0,c2,c14,c17,c7,c4],[(28,[]),(9,[(1,1,2)]),(69,[]),(71,[]),(1,[(1,0,2),(1,1,2)]),(19,[(1,0,2),(1,1,2)]),(24,[]),(29,[]),(1,[(1,0,1),(1,1,2)]),(19,[(1,0,1),(1,1,2)]),(23,[]),(78,[]),(9,[]),(19,[(1,0,1),(1,0,2)]),(25,[]),(54,[]),(44,[(1,0,3)]),(2,[(1,1,3),(1,2,3)]),(2,[(1,1,2),(1,2,3)]),(2,[(1,1,2),(1,1,3)]),(48,[]),(3,[(1,0,3)]),(18,[]),(0,[(1,2,3)]),(5,[(1,2,3),(1,1,2)]),(44,[]),(5,[(1,1,3),(1,1,2)]),(40,[]),(5,[(1,1,3),(1,2,3)])],[(8,12),(2,6),(4,6),(3,33),(1,33),(3,7),(5,33)],[[0,1,1000,2,3,1001],[0,1,4,2,5,6],[7,1,8,0,9,10],[11,1,12,0,13,14],[11,15,1002,16,3,1003,1004],[11,5,17,3,1000,1001],[11,9,18,3,1005,1000],[3,13,19,16,2,20],[11,0,1000,1,2,1006,1004],[21,22,10],[23,22,2],[5,0,24,1,2,25],[21,1],[9,7,26,1,0,27],[13,3,28,1,0,12]]),
 ([0xffaa0000ffaa,c1,c0,c2,c3,c72,c4],[(0,[(1,0,3)]),(3,[(1,1,3)]),(28,[]),(19,[]),(9,[]),(71,[]),(44,[]),(23,[]),(62,[]),(0,[(2,2,3),(1,0,3)]),(52,[]),(25,[]),(9,[(2,1,2)]),(0,[(2,2,3),(3,0,3)]),(54,[])],[],[[0,1],[2,3,4],[3,5,6],[1,0],[4,3],[2,4,3],[2,7,8],[9,5],[8,7],[9,6,10],[2,5],[2,5,8],[2,11,12],[13],[14,5],[5,7],[10,5],[2,6,8],[14,6],[2,6,7],[14,2]]),
 ([c51,c1,c0,c2,c3,c14,c4],[(0,[]),(69,[]),(9,[]),(19,[(1,0,1)]),(54,[]),(23,[]),(0,[(2,2,3)]),(0,[(0,2,3)]),(28,[]),(2,[(1,1,2),(3,3,5)]),(71,[]),(63,[]),(62,[]),(53,[]),(61,[])],[(5,12)],[[0,1],[2,3],[3,1],[1,4,5],[6,1,7],[3,2],[8,1],[9,10,11],[1000,5,4],[12],[8,1],[8,1],[1,11],[8,1],[4,5],[4,5,10],[9,5,13],[4,1],[14],[1,5],[8,1]]),
 ([c1,c0,c2,c3,c5,0xffff0f0affff0f0a,c4],[(28,[]),(24,[]),(62,[]),(53,[]),(46,[]),(57,[]),(54,[]),(9,[]),(61,[]),(64,[]),(78,[]),(69,[])],[],[[0,1,2],[3,4,5],[2,5],[4,1],[4,1],[0,6],[0,1,2],[0,1,5],[5,0],[7,0,8],[4,1],[2,8,6],[9,1,10],[10,1],[0,4],[6,1],[8,1],[0,5],[11],[4,0],[4,0]]),
 ([c63,c1,c0,c2,c5,c7,c4],[(0,[(1,2,3)]),(2,[(1,2,3),(1,1,2)]),(2,[(1,2,3),(3,1,2)]),(9,[(1,1,2)]),(19,[(1,1,2)]),(0,[(1,2,3),(1,1,2)]),(18,[]),(2,[(1,2,3),(1,1,5)]),(44,[]),(0,[(3,1,2),(1,2,3)]),(59,[]),(46,[]),(28,[]),(9,[(3,0,1)]),(19,[(1,0,1)]),(49,[]),(53,[]),(0,[(3,1,2),(2,2,3)])],[],[[0,1,2],[3,4],[5],[6,7,8],[6,0],[4,3],[9,10],[1,11],[9,11],[9,10],[9,10],[1,10],[10,12],[13,12,14],[11,15],[1,16,15],[1,10],[1,10],[17],[10,12],[11,12]]),
 ([c1,c0,c2,c14,c20,c7,c4],[(0,[(1,1,3),(1,2,3)]),(69,[]),(2,[(1,1,2),(1,2,3)]),(2,[(1,2,3),(3,1,2)]),(57,[]),(28,[]),(9,[(1,0,2)]),(19,[(1,0,1)]),(54,[]),(72,[]),(53,[]),(0,[(1,2,3),(3,1,3)]),(18,[])],[],[[0,1],[0,2],[3],[0,4],[0,1],[0,1],[2,1],[5,1],[4,1],[6,4,7],[8,9],[2,10],[11],[2,1],[2,1],[12,9],[0,1],[5,1],[2,1],[4,1],[7,4,6]]),
 ([0xf0f0f0a0f0f0f0a,c1,c0,c2,c3,c5,c4],[(0,[]),(57,[]),(46,[]),(9,[]),(19,[]),(53,[]),(54,[]),(61,[]),(64,[]),(69,[]),(50,[]),(28,[]),(49,[]),(0,[(1,2,3),(3,1,5)])],[],[[0,1,2],[3,1,4],[5],[4,6,7],[4,8,9],[2,1],[2,9,7],[1,2],[2,1],[1,8,10],[11,6],[1,7],[6,1,9],[1,11],[2,12],[6,7],[8,9],[1,2],[6,13,8],[2,1],[1,11]]),
 ([c1,c0,c2,0xf0f0fffaf0f0fffa,c3,c5,c4],[(61,[]),(69,[]),(57,[]),(46,[]),(0,[]),(3,[(3,0,2)]),(3,[(2,0,3),(1,2,5)]),(28,[]),(71,[]),(53,[]),(54,[]),(0,[(2,1,2)]),(0,[(0,1,3)]),(30,[])],[(1,21)],[[0,1],[2,3],[4,2,5],[0,2,3],[2,1,6],[7,1],[2,0],[7,0],[1,2],[0,7],[0,8,3],[9],[6,0,10],[8,1,1000],[2,1],[5,0,11],[12,1],[7,1],[0,13],[0,2,1],[2,7]]),
 ([0xf0f00000f0f0,0xffaa0000ffaa,c1,c0,c2,c3,c4],[(2,[]),(69,[]),(0,[(2,2,3)]),(57,[]),(59,[]),(0,[(2,2,3),(0,1,3)]),(0,[(2,2,3),(0,1,5)]),(54,[]),(0,[(2,1,3)]),(46,[]),(53,[]),(0,[(2,1,3),(2,2,3)]),(44,[]),(50,[])],[(4,21),(1,21)],[[0,1],[2,1000,3],[3,4],[5],[6,4,7],[3,4],[8,3,9],[10,3],[0,1001,10],[11,4],[10,3],[10,4],[3,10],[11,3,4],[10,4],[3,4],[7,3,10],[7,12,13],[7,4],[3,4],[10,3]]),
 ([c77,c1,c0,c2,c18,c5,c4],[(0,[(1,0,2)]),(3,[(1,0,3)]),(3,[(3,0,3)]),(57,[]),(19,[]),(9,[]),(71,[]),(49,[]),(0,[(3,2,3),(1,0,2)]),(23,[]),(62,[]),(9,[(3,1,2)]),(64,[]),(72,[])],[],[[0,1,2],[3,4,5],[4,6,7],[5,4],[1,0],[3,5,4],[8,9,10],[3,6,7],[8,3,10],[3,1,8],[7,6],[3,6,10],[1],[3,9,11],[12,6],[10,6],[6,10],[3,11,10],[12,9],[12,3],[3,11,13]]),
 ([c1,c0,c2,c16,c17,c7,c4],[(0,[(1,1,2),(1,2,3)]),(69,[]),(2,[(1,1,3),(1,2,3)]),(67,[]),(2,[(1,2,3),(3,1,3)]),(61,[]),(9,[(1,0,1)]),(19,[(1,0,2)]),(68,[]),(64,[]),(0,[(1,2,3),(3,1,2)]),(63,[]),(17,[]),(0,[(1,2,3),(1,1,5)]),(23,[])],[],[[0,1],[0,2],[0,3],[4],[0,1],[0,1],[2,1],[3,1],[5,1],[6,3,7],[5,8,9],[10],[2,11],[2,1],[2,1],[12,13,14],[2,1],[3,1],[0,1],[11,1],[5,3,6]]),
 ([c52,c1,c0,c2,c5,c17,c4],[(0,[]),(54,[]),(19,[(1,0,2)]),(53,[]),(61,[]),(64,[]),(72,[]),(9,[]),(69,[]),(71,[]),(62,[]),(57,[]),(63,[]),(50,[])],[(5,20)],[[0,1],[1,2],[1,3,4],[1,5,6],[4,1],[2,3,7],[3,8],[3,9],[1000,10,5],[11],[3,1],[10,4,6],[4,3],[4,3],[1,6],[5,3,8],[12,3],[1,8],[13],[1,3],[12,1]]),
 ([c1,c0,c2,c3,0xff0fff0aff0fff0a,c5,c4],[(63,[]),(69,[]),(46,[]),(57,[]),(50,[]),(23,[]),(64,[]),(54,[]),(49,[]),(61,[]),(28,[])],[],[[0,1],[0,2,3],[2,3],[2,3],[2,1,4],[0,1],[3,1],[1,0],[1,0],[0,5,6],[2,5],[7,0,8],[8,0],[0,1,6],[3,1],[9],[1,5],[1,0],[1,5],[1,0],[0,10]]),
 ([0xf0f0a0a0f0f0a0a,c1,c0,c2,c3,c7,c4],[(0,[(1,2,3)]),(2,[(1,2,3),(1,1,3)]),(2,[(1,2,3),(3,1,3)]),(63,[]),(19,[(1,1,2)]),(28,[]),(0,[(1,2,3),(1,1,3)]),(3,[]),(2,[(1,2,3),(1,1,5)]),(23,[]),(0,[(3,1,3)]),(64,[]),(69,[]),(46,[]),(0,[(3,1,3),(1,2,3)]),(19,[(1,0,2)]),(49,[]),(0,[(3,1,3),(3,2,3)])],[],[[0,1,2],[3,4,5],[6],[7,8,9],[10,0,11],[3,5],[3,12],[1,13],[13,14],[10,11],[3,11],[1,12],[5,3],[11,3,15],[11,16],[1,3,16],[1,3,12],[1,12],[17],[5,3],[13,3]]),
 ([c1,c0,c2,0xf0fff0faf0fff0fa,c3,c5,c4],[(46,[]),(69,[]),(28,[]),(57,[]),(50,[]),(71,[]),(63,[]),(61,[]),(64,[]),(0,[(0,1,2)]),(19,[(3,1,2)]),(0,[(2,1,3)]),(26,[])],[(1,13)],[[0,1,2],[3,0],[3,0],[0,3],[0,1,4],[2,1],[2,1],[3,1],[1,3],[3,2],[0,5],[6],[5,7,1000],[5,1,8],[2,0],[9,7],[10,1,11],[3,0],[1,12],[0,3],[0,2]]),
 ([0xf000f000f000f0,c77,c1,c0,c2,c5,c4],[(19,[]),(61,[]),(57,[]),(69,[]),(0,[(3,2,3),(0,1,2)]),(64,[]),(54,[]),(0,[(2,1,2)]),(63,[]),(0,[(2,1,2),(3,2,3)]),(28,[]),(23,[])],[(4,13),(1,13)],[[0,1],[1,1000,2],[2,3],[4],[1,3,5],[1,3,2],[2,6,7],[1,0,3],[0,1001,8],[6,3,7],[0,3,2],[1,3],[2,8],[2,3,9],[8,3],[2,1],[1,10],[1,11,5],[5,3],[2,3],[2,10]]),
 ([c1,c0,c2,c3,c5,0xffff5544ffff5544,c4],[(28,[]),(19,[(2,0,2)]),(46,[]),(54,[]),(9,[(1,1,2)]),(62,[]),(71,[]),(63,[]),(72,[]),(19,[(1,0,2)])],[],[[0,1,2],[1,2],[2,3,4],[2,5],[2,1],[0,3],[0,6,4],[0,1,3],[4,0,1],[4,0,1],[2,6],[1,7,5],[1,5,6],[1,5,6],[0,2],[3,4,8],[3,4],[0,4,1],[9],[1,0,2],[1,0,2]]),
 ([c1,0xaaaaffeeaaaaffee,c0,c2,c3,c5,c4],[(19,[(1,0,2)]),(63,[]),(19,[(3,0,2)]),(69,[]),(71,[]),(72,[]),(54,[]),(9,[(2,1,2)])],[],[[0],[1,2,3],[1,4],[5,6],[7,3],[1,3],[7,0],[0,1,5],[5,6],[7,0],[0,1,5],[7,3,4],[3,1],[1,2,7],[6,4],[2,1,4],[1,3,2],[6,3],[3,5,6],[2,1,3],[1,5]]),
 ([c1,c0,c2,c3,0xff55ff44ff55ff44,c5,c4],[(63,[]),(69,[]),(71,[]),(9,[(1,1,2)]),(23,[]),(46,[]),(19,[(2,0,1)]),(28,[]),(9,[(3,1,2)])],[],[[0,1],[0,2],[3,4,5],[3,4,5],[3,1],[0,1],[3,1,2],[1,0],[1,0],[0,4,3],[5,2],[2,0],[2,0],[0,1,6],[7,1],[8],[1,3,4],[1,0],[1,3],[1,0],[0,3,6]]),
 ([c1,0xaaffaaeeaaffaaee,c0,c2,c3,c5,c4],[(19,[(1,0,1)]),(63,[]),(19,[(3,0,1)]),(69,[]),(71,[]),(9,[(3,1,2)]),(54,[]),(26,[])],[],[[0],[1,2,3],[1,4],[5,6],[5,3],[1,3],[1,0,3],[0,4,1],[5,0],[5,3],[0,3,1],[5,3,4],[3,1],[1,2,5],[6,4],[2,1,4],[1,3,2],[6,3],[3,7],[2,1,3],[1,5,2]]),
 ([c51,c1,c0,c2,c3,c16,c4],[(0,[(1,1,2)]),(69,[]),(9,[(1,0,1)]),(63,[]),(19,[]),(26,[]),(19,[(2,1,2)]),(19,[(0,1,2)]),(46,[]),(57,[]),(17,[(2,0,3)]),(23,[]),(61,[]),(71,[]),(54,[])],[(5,9)],[[0,1],[2,3,4],[4,1],[1,5],[6,0,7],[4,2],[3,1],[3,8,9],[8,9],[10,8],[3,1],[5,1],[1,3],[10,1],[8,11],[1000,3,12],[13],[5,1],[14],[1,3],[10,1]]),
 ([c1,c0,c2,c3,c5,0xffff5550ffff5550,c4],[(63,[]),(59,[]),(71,[]),(61,[]),(26,[]),(62,[]),(70,[]),(28,[]),(17,[])],[],[[0,1],[0,2],[3,1],[4,5,6],[6,5],[0,1],[4,1],[6,0],[0,7],[1,0],[3,2,6],[2,0],[0,5],[2,0],[4,1],[1,4,8],[1,3],[2,0],[8],[0,7],[1,0]]),
 ([0x5550555055505550,c1,c0,c3,c5,c20,c4],[(46,[]),(9,[(1,0,2)]),(19,[]),(17,[]),(0,[(1,1,3),(1,2,5)]),(50,[]),(63,[]),(69,[]),(54,[]),(0,[(1,1,2),(1,1,3)]),(71,[]),(28,[]),(9,[(1,0,1)])],[],[[0],[1,2],[1,2],[3,4,5],[3,4,6],[2,1],[5,7],[3,8,9],[5,7],[6,10],[6,7],[3,6],[6,11],[12,5,10],[5,10,8],[3,8],[3,6],[3,6],[3],[5,11,6],[8,7]]),
 ([0x5550555055505550,c1,c0,c2,c5,c7,c4],[(46,[]),(9,[(1,1,2)]),(19,[(1,1,2)]),(0,[(1,2,3),(1,1,2)]),(0,[(1,2,3),(3,1,2)]),(17,[]),(0,[(1,2,3),(1,1,5)]),(26,[]),(61,[]),(59,[]),(71,[]),(67,[]),(70,[])],[],[[0],[1,2],[1,3,4],[5,6,7],[5,2,8],[2,1],[3,9],[3,10],[3,11,12],[3,9],[3,9],[5,8],[8,11],[12,7],[8,10,12],[5,10],[5,8],[5,9],[5],[9,11],[8,7,10]]),
 ([0x5555505055555050,c1,c0,c3,c16,c5,c4],[(46,[]),(9,[(1,0,1)]),(19,[]),(17,[]),(0,[(1,1,2),(1,3,5)]),(59,[]),(71,[]),(0,[(1,1,3),(1,1,2)]),(69,[]),(63,[]),(9,[(1,0,2)]),(28,[]),(61,[]),(70,[]),(0,[(1,1,3),(2,1,2)]),(72,[])],[],[[0],[1,2],[3,4,5],[3,4,6],[1,2],[2,1],[7,5],[7,5],[7,6],[7,8],[7,5],[8,9],[10,5,6],[5,11],[12,6,13],[14],[5,8],[6,9],[6,8,15],[11,5],[5,11]]),
 ([c1,c0,c16,c20,c7,c4],[(46,[]),(0,[(1,1,2),(1,1,3),(1,2,3)]),(19,[(1,1,2)]),(59,[]),(17,[]),(0,[(1,1,3),(1,2,3)]),(70,[]),(0,[(1,1,2),(1,2,3)]),(0,[(1,1,2),(1,1,3)]),(67,[]),(48,[]),(9,[(1,0,2),(1,1,2)]),(1,[(1,2,3),(1,1,2)]),(72,[]),(9,[(1,0,1),(1,1,2)]),(1,[(1,1,3),(1,1,2)]),(23,[]),(9,[(1,0,1),(1,0,2)]),(1,[(1,1,3),(1,2,3)]),(19,[]),(61,[]),(72,[(1,0,1)]),(3,[(1,2,3)]),(18,[]),(2,[(1,2,3)]),(5,[(1,0,2),(1,1,2)]),(44,[]),(5,[(1,0,1),(1,1,2)]),(40,[]),(31,[])],[(4,6),(5,6),(4,7),(8,9),(13,16),(16,17),(1,33),(0,33),(3,33)],[l4,[4,1,5,0,1003,1004],[6,1,7,0,1005,1003],[0,1,8,9,3,10],[2,1,1003,6,3,1006,1007],[4,11,12,3,2,13],[6,14,15,3,2,16],[6,17,18,9,2,19],[20,0,1000,6,21,1008,1006],[22,23,16],[24,23],[2,4,25,11,0,26],[22,2],[2,23,27,14,0,28],[2,0,19,17,9,29]]),
 ([0x5555555055555550,c1,c0,c2,c3,c5,c4],[(23,[]),(9,[]),(19,[]),(72,[]),(71,[]),(59,[]),(17,[]),(61,[]),(70,[]),(69,[]),(26,[]),(28,[]),(63,[])],[],[[0],[1,2],[1,3,4],[1,3,5],[1,6],[2,1],[7,5],[3,4],[3,5],[8,9,10],[3,4],[8,3,5],[8,3,10],[5,11],[7,3,8],[4,5,12],[4,3],[10,5],[5,3],[4,10],[4,3]]),
 ([c1,0xaaaafffaaaaafffa,c0,c2,c3,c5,c4],[(17,[]),(61,[]),(59,[]),(71,[]),(72,[]),(46,[]),(69,[]),(9,[]),(19,[]),(63,[]),(28,[])],[(4,21)],[[0],[1,2],[0,3,4],[0,2,1],[5,6,1000],[4,2],[7,1,8],[0,3,4],[0,1,4],[7,6],[4,2],[0,1],[0,4,9],[1,10],[1,3,5],[3,1,9],[0,4,3],[0,2],[0,4,1],[0,9],[2,4]]),
 ([0xaaaa0000aaaa,c30,c1,c0,c2,c3,c4],[(0,[]),(69,[]),(17,[(0,0,3)]),(61,[]),(19,[(2,1,2)]),(59,[]),(72,[]),(17,[(2,0,3)]),(63,[]),(44,[]),(2,[(2,1,3),(2,2,3)])],[(1,21),(4,21)],[[0,1],[2],[3,4,5],[2,1000,6],[2,5,3],[4,5,6],[0,1001,7],[7,3],[6,8],[6,3],[6,5],[3,5],[6,7],[3,5],[6,5],[7,3],[7,6,8],[3,6,9],[10,3],[7,5],[3,8,7]]),
 ([c30,c1,c0,c2,c3,c4,0xffffffffffff0000],[(0,[(1,3,4)]),(52,[]),(17,[(1,1,3)]),(19,[]),(61,[]),(72,[]),(9,[]),(19,[(2,1,2)]),(31,[]),(40,[]),(17,[(3,1,3)])],[],[[0,1,2],[2,3,4],[3,1,5],[5,3,4],[2,6,3],[2,6,3],[1,7],[2,8],[2,1],[1,8],[1,8],[1,4,2],[2,5,9],[4,5,8],[4,7,8],[7,1,4],[1,9],[1,5],[2,8,4],[2,5,4],[10]]),
 ([c52,c1,c0,c2,c5,c20,c4],[(0,[(1,1,3)]),(59,[]),(9,[(1,0,2)]),(19,[]),(72,[]),(19,[(3,1,2)]),(19,[(0,1,2)]),(0,[(1,1,3),(3,2,5)]),(31,[]),(67,[]),(69,[]),(18,[(2,0,3)]),(61,[]),(63,[]),(26,[])],[(5,17)],[[0,1],[2,3],[3,1],[1,4],[5,0,6],[3,2],[7,1],[4,8,9],[7,9,10],[7,8,11],[4,1],[9,1],[1,9],[11,1],[12,4,8],[1000,4,8],[13],[9,1],[14],[1,4],[11,1]]),
 ([c1,c0,c2,c3,0xff55ff50ff55ff50,c5,c4],[(63,[]),(69,[]),(71,[]),(72,[]),(40,[]),(70,[]),(26,[]),(28,[]),(61,[]),(59,[])],[],[[0,1],[0,2],[3,4,5],[5,4],[5,1,6],[0,1],[5,1],[1,0],[1,0],[0,7],[8,2,4],[2,0],[2,0],[0,1,3],[6,1],[9],[1,3,4],[1,0],[1,4],[1,0],[0,3]]),
 ([0x5555505055555050,c1,c0,c2,c3,c7,c4],[(2,[(1,2,3),(1,1,3)]),(69,[]),(19,[(1,1,2)]),(28,[]),(0,[(1,2,3),(1,1,3)]),(0,[(1,2,3),(3,1,3)]),(17,[]),(0,[(1,2,3),(1,1,5)]),(26,[]),(3,[(0,0,3)]),(71,[]),(57,[]),(70,[]),(50,[]),(2,[(3,1,3),(1,2,3)]),(0,[(1,1,3),(3,2,3)])],[],[[0],[1,2,3],[0,4,5],[6,7,8],[1,0,9],[1,3],[3,1],[4,10],[4,11,12],[4,1],[3,1],[3,1],[1,8],[12,3],[13,10,12],[10,14],[10,1,14],[3,1],[15],[1,8],[10,3]]),
 ([c1,0xaaffaafaaaffaafa,c0,c2,c3,c5,c4],[(70,[]),(26,[]),(69,[]),(63,[]),(71,[]),(67,[]),(59,[]),(0,[]),(50,[]),(46,[])],[(4,13)],[[0],[1,2],[3,4],[5,6,1000],[1,2],[1,2],[1,2],[3,4],[7,6],[1,2],[1,2],[1,2],[2,1],[3,5],[8,4,9],[4,3],[1,2],[1,2],[2,1],[2,1],[3,5]]),
 ([0xaa00aa00aa00aa,c79,c1,c0,c2,c5,c4],[(0,[]),(59,[]),(70,[]),(26,[]),(19,[(3,1,2)]),(69,[]),(72,[]),(57,[]),(0,[(2,1,2)]),(61,[]),(0,[(0,1,2)]),(28,[]),(40,[])],[(1,13),(4,13)],[[0,1],[2],[3,4,5],[4,1000,6],[3,5],[3,5],[0,1001,7],[3,5],[8,9,10],[3,5],[3,5],[3,5],[6,7],[3,5],[3,5],[3,5],[7,11],[9,6,12],[3,5],[3,5],[7,6]]),
 ([c79,c1,c0,c2,c5,c4,0xffffffffff00ff00],[(0,[(1,2,4)]),(62,[]),(70,[]),(19,[]),(50,[]),(40,[]),(9,[]),(19,[(3,1,2)]),(31,[]),(44,[]),(69,[])],[],[[0,1,2],[2,3,4],[3,1,5],[5,3,4],[3,6],[3,6],[1,7],[2,8],[2,1],[1,2],[1,2],[1,4,2],[2,7,9],[4,2],[4,2],[7,1,4],[1,5],[1,5],[4,5],[4,5],[10]]),
 ([c38,c1,c2,c50,c3,c5,c4],[(0,[(0,2,3)]),(69,[]),(0,[(0,2,3),(3,0,1)]),(0,[(0,2,3),(0,0,1)]),(9,[]),(19,[]),(9,[(0,1,2)]),(19,[(0,1,2)]),(0,[(0,2,3),(3,0,4)]),(70,[]),(0,[(0,2,3),(0,0,4)]),(71,[]),(59,[]),(17,[(2,1,2)]),(19,[(2,1,2)]),(19,[(3,1,2)])],[],[[0,1],[2,1,3],[1,4,5],[1,6,7],[7,6],[8,9,10],[6,11],[4,9],[6,12],[6,1],[7,1,9],[5,11],[7,12],[7,1],[13,1],[14],[15],[1,4,5],[1,12],[1,6,7],[7,6]]),
 ([c38,c1,c2,c3,c5,c7,c4],[(0,[(1,2,3)]),(46,[]),(19,[(1,1,2)]),(0,[(1,2,3),(3,0,1)]),(9,[(1,1,2)]),(72,[]),(40,[]),(44,[]),(71,[]),(2,[(2,0,4),(1,2,3)]),(19,[(3,1,2)]),(19,[(2,1,2)])],[],[[0,1,2],[3,4,5],[2,4],[2,4],[2,4],[5,1],[2,1],[1,6],[1,7],[1,6],[2,6],[2,6,8],[2,5,8],[2,5,8],[9,1],[5,6],[10],[1,4,2],[11],[1,4,2],[1,4,2]]),
 ([c64,c38,c1,c2,c3,c5,c4],[(19,[]),(9,[]),(84,[]),(70,[]),(71,[]),(19,[(0,1,2)]),(19,[(1,1,2)]),(69,[]),(0,[(2,2,3)]),(9,[(2,1,2)]),(19,[(2,1,2)]),(0,[(2,2,3),(0,0,4)]),(2,[(2,2,3),(2,0,4)]),(72,[])],[(0,24)],[[0,1],[1,2,3],[0,2,4],[5],[6],[0,1],[2,7,8],[2,7,3],[3,9,10],[3,9,10],[2,3,11],[3,4,9],[3,2],[2,7,9],[10,3],[4,2],[2,7,10],[12,7],[7,13,1000],[4,2],[2,9,10]]),
 ([c80,c38,c1,c2,c3,c5,c4],[(19,[]),(9,[]),(85,[]),(70,[]),(71,[]),(19,[(1,1,2)]),(19,[(0,1,2)]),(59,[]),(0,[(3,2,3)]),(9,[(3,1,2)]),(19,[(3,1,2)]),(0,[(3,2,3),(0,0,4)]),(2,[(3,2,3),(2,0,4)]),(40,[])],[(0,24)],[[0,1],[1,2,3],[0,2,4],[5],[6],[0,1],[2,7,8],[2,7,3],[3,9,10],[3,9,10],[2,3,11],[3,4,9],[2,7,9],[3,2],[10,3],[2,7,10],[4,2],[12,7],[7,13,1000],[2,9,10],[4,2]]),
 ([0xf0f0f000f0f0f00,c1,c0,c3,c5,c4,c26],[(0,[(1,1,4)]),(82,[]),(70,[]),(0,[(1,1,4),(3,1,2)]),(19,[(1,1,2)]),(19,[(3,1,2)]),(19,[(2,1,2)]),(9,[]),(46,[]),(69,[]),(44,[]),(50,[]),(71,[]),(2,[(1,2,3)])],[],[[0,1,2],[2,1],[3,4,5],[4,6],[4,7],[4,7],[8,4],[2,1],[2,9,10],[4,1],[4,1],[2,1],[2,4,10],[8,1,11],[1,12],[9,1],[4,10],[4,10],[4,1],[4,1],[13]]),
 ([c1,c0,c2,0xf5f5f5f0f5f5f5f0,c3,c5,c4],[(50,[]),(69,[]),(70,[]),(46,[]),(59,[]),(72,[]),(26,[]),(28,[]),(71,[]),(54,[]),(0,[]),(17,[])],[],[[0,1],[2,3],[2,3],[2,4,5],[0,1],[5,1],[2,0],[2,0],[0,5,6],[2,7],[0,2],[8],[9,4],[6,0],[6,1],[9,4],[10,0,11],[9,1],[0,5,4],[1,6],[0,5,3]]),
 ([c75,0x5555555500000000,c0,c2,c3,c5,c4],[(70,[]),(9,[]),(19,[]),(86,[]),(71,[]),(0,[(1,2,3)]),(0,[(3,2,3)]),(0,[(2,2,3)]),(46,[]),(59,[]),(9,[(1,1,2)]),(69,[]),(25,[]),(54,[]),(62,[]),(75,[(2,1,2)]),(76,[(2,1,2)])],[],[[0,1,2],[0,2,1],[2,3,4],[1,5,6],[1,3,7],[2,1],[8,3,9],[0,3,4],[0,10,9],[0,3,11],[5],[0,4,9],[0,3],[0,12,10],[13,0,4],[4,3],[4,11,14],[13,3,9],[9,3,11],[4,10,15],[4,3,16]]),
 ([0xf0f0f0c0f0f0f0c,c1,c0,c3,c5,c7,c4],[(0,[(1,2,3)]),(71,[]),(0,[(1,2,3),(2,0,1)]),(0,[(1,2,3),(0,0,1)]),(19,[(1,1,2)]),(40,[]),(72,[]),(46,[]),(26,[]),(62,[]),(28,[]),(57,[]),(21,[(2,0,3)]),(59,[]),(19,[(2,1,2)])],[],[[0,1],[2,1,3],[1,4,5],[1,4,6],[1,4,5],[7,5,8],[7,4],[6,5,7],[7,9],[7,5],[4,1,5],[10,4,5],[11,4,10],[12,4,5],[7,1],[6,5],[13],[1,8],[14],[1,5,4],[1,6]]),
 ([c1,0xafafafaaafafafaa,c0,c2,c3,c5,c4],[(46,[]),(26,[]),(59,[]),(57,[]),(71,[]),(49,[]),(61,[]),(69,[]),(0,[(3,1,3)]),(50,[]),(28,[]),(54,[])],[],[[0],[1,2],[3,4,5],[6,2],[1,7],[1,2],[6,1],[5,4],[6,2],[8,1,9],[5,1],[1,2],[7,1],[2,10],[6,4,11],[4,2,11],[1,7],[1,2],[2,1,7],[4,1],[2,10]]),
 ([0xc0c0c0c0c0c0c0c,0xf0f0f000f0f0f00,c1,c0,c3,c5,c4],[(71,[]),(19,[]),(9,[]),(46,[]),(19,[(1,1,2)]),(26,[]),(59,[]),(69,[]),(6,[(1,1,2)]),(87,[]),(50,[]),(49,[]),(14,[(1,1,2)]),(31,[])],[],[[0,1,2],[3,0,4],[5],[0,4,6],[0,4,7],[3,8],[2,9,3],[2,1],[1,4,6],[1,4,7],[0,2,1],[3,4],[3,6,9],[3,7,10],[4,0,11],[7,4,12],[6,4,12],[3,0],[6,4,7],[0,9],[0,13,4]]),
 ([0x5555555555555500,c0,c2,c3,c5,c7,c4],[(46,[]),(26,[]),(19,[(1,1,2)]),(9,[(1,1,2)]),(57,[]),(62,[]),(71,[]),(28,[]),(70,[]),(5,[(1,1,2),(3,3,5)]),(40,[]),(72,[]),(9,[(3,1,2)]),(9,[(2,1,2)])],[],[[0,1,2],[2,0],[0,3,4],[0,1,5],[0,2],[2,0],[1,6,3],[3,1,7],[3,7,4],[3,1,8],[9,6,8],[5,10],[1,5,6],[6,5],[1,3,5],[11,1],[12],[6,1],[13],[4,3,7],[6,1]]),
 ([c1,c0,c2,c3,c5,0xffff0f0fffff0f00,c4],[(26,[]),(19,[(1,1,2)]),(46,[]),(59,[]),(9,[(2,0,2)]),(62,[]),(70,[]),(72,[]),(78,[]),(9,[(1,0,2)])],[],[[0,1,2],[1,2],[2,3,4],[0,5,2],[2,5],[0,3],[0,3],[4,0,1],[3,1,4],[3,0],[2,6,7],[1,3],[0,5,8],[1,4],[0,2],[3,0,7],[1,3],[1,0,2],[9],[1,4],[1,0,2]]),
 ([c1,c0,c2,0xf0f0fffff0f0fff0,c3,c5,c4],[(46,[]),(59,[]),(19,[(2,1,2)]),(0,[]),(67,[]),(9,[(3,0,2)]),(70,[]),(50,[]),(9,[(1,0,2)]),(30,[])],[],[[0,1,2],[2,0],[3,0,4],[0,1,5],[0,4],[2,1,6],[4,1],[4,1],[4,2,5],[1,2,4],[0,6,7],[8],[2,1],[2,7],[4,0],[2,1],[2,5],[2,0,4],[1,9],[0,5,2],[0,4]]),
 ([c1,c0,c2,c3,0xff0fff0fff0fff00,c5,c4],[(46,[]),(19,[(1,1,2)]),(40,[]),(67,[]),(50,[]),(9,[(2,0,1)]),(78,[]),(9,[(1,0,1)])],[],[[0,1],[1,0],[0,2],[0,2],[0,3],[1,2],[3,4],[3,1,2],[4,1,2],[5,1],[0,2,4],[1,2,6],[1,2,5],[1,4],[3,0],[7],[4,1,2],[0,5,1],[1,4],[0,3],[0,2,1]]),
 ([c1,c0,c2,0xf0fff0fff0fff0f0,c3,c5,c4],[(46,[]),(19,[(3,1,2)]),(0,[]),(57,[]),(67,[]),(70,[]),(50,[]),(9,[(1,0,1)]),(59,[]),(26,[])],[],[[0,1],[1,0],[2,0,3],[0,3],[0,4],[1,5],[3,6],[3,1,4],[4,1,3],[3,1,4],[0,5,6],[7],[1,8],[1,6],[3,0],[1,7],[1,6],[1,0,3],[6,9],[0,3],[0,4]])]
def d541 : List StD := dupD [
 ([c22,c0,c2,c3,c66,c5],[(0,[(0,2,3),(2,0,4)]),(0,[(0,2,3),(0,0,4)]),(9,[(0,1,2)]),(59,[]),(67,[]),(57,[]),(19,[]),(70,[]),(25,[]),(71,[]),(54,[]),(49,[]),(69,[]),(64,[])],[],[[0,1],[2,3,4],[2,5,4],[2,3,6],[2,4,3],[2,3,7],[2,8],[2,3,6],[2,8],[9,3,10],[6,8,11],[9,12,13],[0,3],[0,12,3],[0,7]]),
 ([c22,c1,c0,c3,c67,c5],[(70,[]),(19,[(0,1,2)]),(71,[]),(50,[]),(57,[]),(9,[]),(67,[]),(12,[(2,0,3)]),(59,[]),(69,[]),(85,[]),(54,[]),(64,[])],[],[[0,1],[0,2,3],[2,1,4],[4,1,5],[2,1,6],[7,1,8],[0,8,7],[0,2,5],[0,9,10],[0,1,11],[0,1,5],[0,1,12],[1,2],[1,9,7],[1,2]]),
 ([c22,c1,c0,c2,c50,c7],[(0,[(0,2,3),(1,2,3)]),(19,[(0,1,2),(1,1,2)]),(70,[]),(0,[(0,2,3),(1,2,3),(0,0,4)]),(9,[(0,1,2),(1,1,2)]),(69,[]),(54,[]),(0,[(2,0,4),(0,2,3),(1,2,3)]),(71,[])],[(0,24)],[[0,1,2],[2,0,3],[4,5,6],[4,1],[4,1],[7,1,5],[1,8,4],[2,4],[2,5,4],[2,5],[2,1,4],[2,1,4],[1,8],[1,5],[1000]]),
 ([c75,c0,0xeeeeeeee00000000,c2,c3,c5],[(9,[]),(19,[]),(26,[]),(69,[]),(72,[]),(71,[]),(0,[(0,0,4),(3,2,3)]),(0,[(0,0,4),(1,2,3)]),(0,[(1,2,3),(2,0,4)]),(9,[(1,1,2)]),(25,[]),(59,[]),(54,[])],[],[[0,1],[0,2,3],[1,4,5],[0,4,6],[0,7,3],[7,8],[9,3,4],[3,4,9],[9,10],[2,3],[3,2],[5,4],[5,11,12],[5,3,4],[3,4,11]]),
 ([c0,c6,c14,c20,c7,c4],[(26,[]),(69,[]),(50,[]),(9,[(1,1,2)]),(71,[]),(9,[(1,0,2)]),(19,[(1,0,1)]),(54,[]),(19,[(1,1,2)]),(57,[]),(70,[]),(21,[]),(18,[]),(72,[]),(28,[])],[],[[0,1],[2,0],[3,1,4],[5,0,6],[2,4,7],[8,9,10],[0,4],[11,1,9],[0,1],[12,0,13],[2,1],[8,0,14],[4,0],[7,1],[2,0,4]]),
 ([c0,c2,c14,c33,c7,c4],[(57,[]),(71,[]),(69,[]),(50,[]),(9,[(1,1,2)]),(19,[(1,0,1),(1,1,2)]),(9,[(1,0,2)]),(19,[(1,0,1),(1,0,2)]),(54,[]),(19,[(1,0,2),(1,1,2)]),(46,[]),(0,[(1,2,3),(3,1,3)]),(21,[]),(28,[])],[],[[0,1,2],[3,0],[4,2,5],[6,0,7],[3,1,8],[9,1,10],[11],[1,2,7],[0,2],[12,0],[3,2],[9,0,13],[12,0],[5,1,4],[1,0]]),
 ([c34,c64,c0,c2,c14,c4],[(69,[]),(19,[(1,0,1),(3,2,3)]),(57,[]),(9,[(2,1,2)]),(19,[(2,1,2),(1,0,1)]),(0,[(2,2,3),(0,1,5)]),(50,[]),(0,[(2,1,3),(0,2,5)]),(59,[]),(19,[(2,0,2),(1,0,1)]),(0,[(2,1,3),(0,2,3)]),(71,[]),(54,[]),(19,[(2,0,2),(2,1,2)]),(46,[]),(28,[])],[],[[0,1,2],[3,4],[2,0],[5,0,6],[4,3],[0,2],[7,8,9],[10],[0,2],[2,0],[6,0],[6,11,12],[13,11,14],[2,0],[13,0,15]]),
 ([0xf0f00000f0f0,0xffaa0000ffaa,c0,c6,c3,c4],[(19,[]),(71,[]),(69,[]),(9,[(2,1,2)]),(0,[(2,2,3),(0,1,3)]),(59,[]),(54,[]),(9,[(2,0,2)]),(0,[(2,1,3),(0,2,5)]),(46,[]),(19,[(0,0,2)]),(28,[]),(57,[]),(21,[])],[],[[0,1,2],[3,1],[4],[1,5,6],[6,3,5],[7,0],[8,9,10],[9,5,7],[0,1,7],[11,5],[6,12,11],[6,1],[13,5,12],[11,1],[1,12]]),
 ([c0,c6,c16,c17,c7,c4],[(28,[]),(69,[]),(46,[]),(19,[(1,1,2)]),(9,[(1,0,1)]),(19,[(1,0,2)]),(71,[]),(0,[(1,2,3)]),(21,[]),(67,[]),(12,[]),(40,[(1,0,2)])],[],[[0,1],[0,1],[2,0,3],[4,0,5],[2,6],[7,6],[3,2],[8,1,9],[0,1],[10,2,6],[5,1],[0,1],[2,1,4],[3,0,11],[2,0]]),
 ([c0,c2,c29,c17,c7,c4],[(28,[]),(71,[]),(69,[]),(46,[]),(19,[(1,0,1),(1,1,2)]),(9,[(1,0,1)]),(19,[(1,0,1),(1,0,2)]),(0,[(1,2,3),(3,1,2)]),(21,[]),(67,[]),(40,[])],[],[[0,1,2],[0,2],[3,0,4],[5,0,6],[3,1],[7],[4,1,3],[1,2,6],[0,2],[8,3,9],[8,2,9],[0,1],[3,2,5],[4,0,10],[1,0]]),
 ([c27,c80,c0,c2,c17,c4],[(21,[]),(19,[(1,0,2),(3,1,3)]),(67,[]),(28,[]),(19,[(3,1,2),(1,0,2)]),(9,[(3,1,2)]),(9,[(2,0,1)]),(19,[(2,0,1),(1,0,2)]),(69,[]),(0,[(2,1,2),(0,2,3)]),(46,[]),(19,[(2,0,1),(3,1,2)]),(40,[(1,0,3)]),(71,[])],[],[[0,1,2],[3,4,5],[0,5],[0,2],[3,5,4],[6,2,7],[7,8],[9],[7,2,6],[2,8],[10,2,11],[10,12,13],[11,10],[2,8],[11,2,12]]),
 ([0xf000f000f000f0,c77,c0,c6,c5,c4],[(19,[]),(71,[]),(46,[]),(9,[(3,1,2)]),(0,[(3,2,3),(0,1,2)]),(69,[]),(40,[(1,0,2)]),(28,[]),(19,[(0,0,1)]),(9,[(2,0,1)]),(57,[]),(67,[])],[],[[0,1,2],[3,1],[4],[1,5,6],[7,2],[2,0],[6,2,8],[2,5,6],[0,1,9],[7,5],[10,7],[2,1],[10,5,11],[7,1],[1,6,7]]),
 ([c1,c0,c16,c33,c7,c4],[(0,[(1,1,2),(1,1,3),(1,2,3)]),(69,[]),(71,[]),(57,[]),(9,[(1,0,2),(1,1,2)]),(9,[(1,0,1),(1,1,2)]),(19,[(1,1,2)]),(9,[(1,0,1),(1,0,2)]),(19,[(1,0,2)]),(46,[]),(21,[]),(40,[]),(67,[])],[],[[0,1],[0,2],[3],[0,1],[0,1],[4,1,2],[5,1,6],[7,8],[9,2],[10,2,11],[2,1,8],[12,1],[10,1,11],[6,1,5],[2,7,8]]),
 ([c34,c64,c1,c0,c16,c4],[(21,[]),(0,[(1,1,2),(3,3,5)]),(40,[]),(19,[(2,1,2)]),(9,[(2,1,2),(1,0,1)]),(0,[(2,1,3),(1,1,2)]),(59,[]),(9,[(2,0,2),(1,0,1)]),(19,[(2,0,2)]),(54,[]),(0,[(2,1,3),(2,2,3),(1,1,2)]),(71,[]),(9,[(2,0,2),(2,1,2)]),(46,[]),(67,[])],[],[[0,1,2],[0,3],[4,3],[0,2],[3,2],[5,6],[7,8],[9],[8,7],[10,6],[10,11],[10,6],[12,6,11],[13,11],[14,6]]),
 ([0xaaaa0000aaaa,c30,c0,c6,c3,c4],[(0,[]),(71,[]),(67,[]),(19,[(2,1,2)]),(46,[]),(57,[]),(59,[]),(72,[]),(0,[(0,1,3)]),(28,[]),(26,[]),(30,[])],[],[[0,1],[2,3,4],[5],[4,6,7],[2,1],[2,1,6],[2,1,8],[1,6,7],[2,4],[9,6],[2,7,10],[4,1],[2,6,11],[9,1],[1,10]]),
 ([c1,c0,c29,c20,c7,c4],[(0,[(1,1,2),(1,1,3),(1,2,3)]),(59,[]),(67,[]),(46,[]),(57,[]),(9,[(1,0,2),(1,1,2)]),(19,[(1,1,2)]),(9,[(1,0,1),(1,0,2)]),(19,[(1,0,1)]),(72,[(1,0,1)]),(21,[])],[],[[0,1],[2],[0,3,4],[0,1],[0,1],[5,1,6],[4,1],[7,4,8],[3,9],[10,9],[10,1,9],[6,1,5],[8,1],[4,1],[3,4]]),
 ([c27,c80,c1,c0,c20,c4],[(21,[]),(0,[(1,1,3),(3,2,5)]),(72,[]),(19,[(3,1,2)]),(9,[(3,1,2),(1,0,2)]),(0,[(2,1,2),(1,1,3)]),(69,[]),(9,[(2,0,1),(1,0,2)]),(19,[(2,0,1)]),(64,[]),(0,[(2,1,2),(3,2,3),(1,1,3)]),(46,[]),(57,[]),(71,[])],[],[[0,1,2],[0,3],[4,2],[0,2],[3,4],[5,6],[7,8],[9],[8,7],[10,6],[10,11,12],[10,6],[12,6],[11,13],[12,6]]),
 ([0xaa00aa00aa00aa,c79,c0,c6,c5,c4],[(0,[]),(46,[]),(71,[]),(19,[(3,1,2)]),(67,[]),(69,[]),(26,[]),(0,[(2,1,2)]),(0,[(0,1,2)]),(57,[]),(28,[])],[],[[0,1,2],[1,3],[4],[1,5,6],[3,2,6],[6,2,5],[7,2,8],[2,5,6],[6,1],[6,5],[9,10],[1,2],[6,5],[6,1],[1,10]]),
 ([c27,c1,c0,c2,0xfffa0000fffa0000,c4],[(57,[]),(46,[]),(69,[]),(21,[]),(71,[]),(59,[]),(26,[]),(19,[(2,0,1)]),(9,[(2,0,1)])],[],[[0,1],[0,2],[3,4,5],[3,2,6],[0,1],[1,2,6],[0,1],[0,2,6],[6,2],[0,2],[0,7,8],[1,4],[4,2,6],[0,1],[0,8,7]]),
 ([c51,c1,c0,c2,c3,c4],[(0,[]),(69,[]),(9,[]),(19,[]),(26,[]),(57,[]),(46,[]),(71,[]),(0,[(1,1,2),(3,3,5)])],[],[[0,1],[2,3],[3,1],[1,4],[3,2],[4,1],[5,6],[6,5],[4,1],[4,1],[1,4],[6,7],[7,8],[4,1],[1,4]]),
 ([c52,c1,c0,c2,c5,c4],[(0,[]),(46,[]),(57,[]),(19,[]),(9,[]),(71,[]),(59,[]),(69,[]),(26,[]),(28,[])],[],[[0,1,2],[2,3,4],[3,5,6],[6,7,8],[2,1],[1,6,8],[2,1],[1,7,8],[8,5],[2,5,6],[2,9],[1,5],[5,7,8],[2,1],[1,9]]),
 ([0xfa000000fa,c1,c0,c2,c50,c4],[(0,[(0,2,3)]),(19,[(0,1,2)]),(9,[(0,1,2)]),(26,[]),(69,[]),(57,[]),(71,[]),(46,[]),(72,[]),(88,[]),(40,[])],[(1,25)],[[0,1],[2,1],[1,0],[1000],[1,2],[3,4],[5,6,7],[3,5],[3,4],[3,4],[4,8,9],[7,6],[3,6],[3,4],[4,10,9]]),
 ([c34,c1,c0,c2,0xff00fa00ff00fa00,c4],[(21,[]),(46,[]),(69,[]),(26,[]),(59,[]),(72,[]),(71,[]),(9,[(2,0,2)]),(19,[(2,0,2)])],[],[[0,1,2],[3,4],[0,2],[0,4,3],[3,1],[1,2,3],[5,1,6],[1,4,3],[3,2],[3,2],[2,5,7],[1,5],[3,4],[3,1],[1,7,8]]),
 ([c63,c0,c2,c17,c7,c4],[(69,[]),(19,[(1,0,2),(1,1,2)]),(26,[]),(0,[(1,2,3),(1,1,2)]),(46,[]),(21,[]),(19,[(1,0,1),(1,1,2)]),(9,[(3,0,1)]),(19,[(1,0,1),(1,0,2)]),(49,[])],[],[[0,1,2],[3],[4,2],[0,3,5],[0,2],[2,0],[4,0,6],[7,2,8],[4,9],[2,4],[8,0],[2,0],[4,0,2],[6,0,9],[4,2]]),
 ([0xf0f0a0a0f0f0a0a,c0,c2,c14,c7,c4],[(9,[(1,1,2)]),(19,[(1,0,1),(1,1,2)]),(0,[(1,2,3),(1,1,3)]),(46,[]),(19,[(1,1,2),(1,0,3)]),(67,[]),(0,[(3,1,3)]),(21,[]),(69,[]),(19,[(1,0,2),(1,1,2)]),(9,[(3,0,2)]),(19,[(1,0,2),(1,0,1)]),(49,[])],[],[[0,1],[2],[3,4,5],[6,0,7],[1,0],[5,8],[3,8,9],[10,5,11],[3,12],[5,3],[11,8],[5,3],[3,5],[9,8,12],[3,5]]),
 ([0x5550555055505550,c1,c0,c20,c7,c4],[(46,[]),(9,[(1,0,2),(1,1,2)]),(19,[(1,1,2)]),(71,[]),(0,[(1,2,3),(1,1,5)]),(49,[]),(19,[(3,0,1)]),(21,[]),(0,[(1,1,2),(1,1,3),(1,2,3)]),(69,[]),(9,[(1,0,1),(1,1,2)]),(9,[(1,0,1),(1,0,2)]),(54,[])],[],[[0],[1,2],[3,4,5],[6,2,7],[2,1],[8,9],[8,3],[8,9],[8,3],[10,3],[11,6],[12,3],[3,9,6],[12,9],[3,11,6]]),
 ([0x5555505055555050,c1,c0,c16,c7,c4],[(46,[]),(9,[(1,0,1),(1,1,2)]),(19,[(1,1,2)]),(71,[]),(0,[(1,2,3),(1,1,5)]),(49,[]),(19,[(3,0,2)]),(21,[]),(0,[(1,1,3),(1,1,2),(1,2,3)]),(69,[]),(9,[(1,0,2),(1,1,2)]),(9,[(1,0,2),(1,0,1)]),(64,[])],[],[[0],[1,2],[3,4,5],[6,2,7],[2,1],[8,9],[8,3],[8,9],[8,3],[10,3],[11,6],[12,3],[3,9,6],[12,9],[3,11,6]]),
 ([c38,c2,c3,c66,c5,c4],[(0,[(0,2,3),(3,0,1)]),(9,[(0,1,2)]),(69,[]),(57,[]),(19,[]),(67,[]),(0,[(0,2,3),(3,0,4)]),(0,[(0,2,3),(0,0,4)]),(49,[]),(59,[]),(18,[(2,1,2)]),(71,[]),(85,[]),(61,[])],[],[[0,1,2],[2,1,3],[4,1],[3,1,5],[6,3,7],[8,9,10],[4,11,8],[8,2,12],[10,1,2],[1,9],[1,2,9],[2,1,13],[1,2],[4,1],[8,1,12]]),
 ([c38,c1,c3,c67,c5,c4],[(19,[(0,1,2)]),(69,[]),(46,[]),(57,[]),(67,[]),(49,[]),(59,[]),(61,[]),(71,[]),(85,[]),(31,[]),(9,[])],[],[[0,1,2],[0,3,1],[0,1,3],[0,4,3],[5,2],[2,6,7],[5,2,8],[2,1,9],[0,1,5],[0,5],[0,1,6],[0,10],[0,1],[0,1,11],[0,9,2]]),
 ([c38,c1,c2,c50,c7,c4],[(0,[(0,2,3),(1,2,3)]),(69,[]),(0,[(0,2,3),(1,2,3),(3,0,1)]),(0,[(0,2,3),(1,2,3),(0,0,1)]),(9,[(1,1,2)]),(19,[(1,1,2)]),(19,[(0,1,2)]),(9,[(0,1,2)]),(0,[(0,2,3),(1,2,3),(3,0,4)]),(67,[]),(0,[(0,2,3),(1,2,3),(0,0,4)]),(9,[(0,1,2),(1,1,2)]),(71,[]),(85,[]),(49,[]),(18,[(2,1,2)])],[(0,24)],[[0,1],[2,1,3],[1,4,5],[6,7],[8,9,10],[11,12],[4,13],[7,1],[14,1],[5,12],[6,1],[15,1],[1000],[1,4,5],[6,7]]),
 ([0xf0f0f000f0f0f00,c1,0xccccccccc0c0c0c0,c3,c5,c4],[(9,[]),(82,[]),(46,[]),(49,[]),(9,[(3,0,1)]),(19,[(1,1,2)]),(19,[(3,1,2)]),(19,[(2,1,2)]),(71,[]),(69,[]),(50,[]),(67,[]),(31,[])],[],[[0,1,2],[0,1,3],[4,5,6],[5,7],[2,0,5],[2,8,3],[2,1],[2,9,10],[5,1],[3,1],[3,11],[2,1,3],[9,1],[2,12,5],[2,1,5]]),
 ([0xf0f0f0c0f0f0f0c,c1,c0,c50,c7,c4],[(0,[(0,2,3),(1,2,3)]),(19,[(0,1,2),(1,1,2)]),(71,[]),(0,[(0,2,3),(1,2,3),(2,0,1)]),(0,[(0,2,3),(1,2,3),(0,0,1)]),(9,[(0,1,2)]),(69,[]),(9,[(0,1,2),(1,1,2)]),(67,[]),(46,[]),(9,[(1,1,2),(3,0,3)]),(49,[]),(21,[(2,0,3)])],[(2,26)],[[0,1,2],[3,2,4],[2,1],[2,1,5],[6,7,8],[9,1],[8,10],[9,6,8],[1,2,11],[6,1,10],[12,1,8],[9,2],[1000],[1,10],[1,8,2]]),
 ([0x5555555555555500,c0,c2,c50,c7,c4],[(46,[]),(19,[(0,1,2),(1,1,2)]),(0,[(1,2,3),(1,4,5)]),(9,[(0,1,2),(1,1,2)]),(69,[]),(67,[]),(19,[(1,1,2),(3,0,3)]),(21,[(2,1,2)]),(64,[]),(71,[])],[(0,25)],[[0,1],[1,0],[0,2],[0,1],[1,0],[3,4,5],[3,6],[3,5,7],[8,9],[6,7],[7,4,8],[5,3,4],[1000],[4,3,6],[7,3,5]])]
def d542 : List StD := dupD [
 ([c22,c0,c2,c66,c7],[(0,[(0,2,3),(1,2,3),(2,0,4)]),(0,[(0,2,3),(1,2,3),(0,0,4)]),(9,[(0,1,2),(1,1,2)]),(69,[]),(67,[]),(19,[(1,1,2)]),(21,[]),(71,[]),(40,[(1,0,3)]),(70,[]),(49,[])],[],[[0,1],[2,3,4],[2,3,5],[2,4,6],[2,3,7],[2,3,5],[2,8,9],[5,7,10],[7,3,8],[0,3]]),
 ([c22,c1,c0,c67,c7],[(21,[(3,1,2)]),(19,[(0,1,2),(1,1,2)]),(71,[]),(21,[(2,0,1)]),(21,[(0,0,1)]),(9,[(1,1,2)]),(67,[]),(12,[(2,0,3)]),(69,[]),(64,[])],[],[[0,1,2],[3,2,4],[5,1],[0,1,6],[7,1,8],[5,2],[7,8],[5,1],[9,1],[1,2]]),
 ([0xfa000000fa,c0,c2,c66,c4],[(9,[(0,1,2)]),(25,[]),(21,[]),(67,[]),(71,[]),(69,[]),(46,[]),(12,[(2,1,2)])],[],[[0,1],[2,0],[0,1],[3,0,4],[3,4,5],[6,5,7],[6,4],[3,4,6],[3,5],[7,4]]),
 ([0xfa000000fa,c1,c0,c67,c4],[(21,[]),(69,[]),(67,[]),(19,[(0,1,2)]),(64,[]),(46,[]),(12,[(2,1,2)]),(71,[])],[],[[0,1],[2,3,4],[0,1],[2,5],[5,1,6],[2,5],[6,1],[2,1],[4,7],[2,1]]),
 ([c38,c2,c66,c7,c4],[(0,[(0,2,3),(1,2,3),(3,0,1)]),(69,[]),(0,[(0,2,3),(1,2,3),(0,0,1)]),(12,[]),(21,[]),(67,[]),(0,[(0,2,3),(1,2,3),(3,0,4)]),(0,[(0,2,3),(1,2,3),(0,0,4)]),(19,[(1,1,2)]),(46,[]),(71,[]),(40,[(1,0,3)]),(18,[(2,1,2)]),(9,[(0,1,2)]),(85,[])],[],[[0,1,2],[3,1],[4,5],[6,5,7],[8,9],[10,1,11],[12,1],[9,1,11],[8,1,11],[9,13,14]]),
 ([c38,c1,c67,c7,c4],[(12,[]),(46,[]),(85,[]),(9,[(1,1,2)]),(21,[]),(67,[]),(71,[]),(19,[(0,1,2),(1,1,2)]),(40,[(1,2,3)])],[],[[0,1,2],[2,3],[4,5],[2,1],[3,1,6],[1,2],[7,6,8],[6,2],[7,1,3],[1,2]]),
 ([0xf0f0c000f0f0c,c1,c0,c7,c4],[(0,[(1,2,3)]),(67,[]),(71,[]),(21,[(2,0,3)]),(40,[]),(19,[(1,1,2)]),(46,[]),(19,[(0,1,2),(1,1,2)]),(40,[(1,2,3)])],[],[[0,1,2],[3,1],[2,4],[5,1,4],[6,7],[3,1],[7,2,8],[3,1],[6,2],[2,1]]),
 ([0xf0f0f0c0f0f0f0c,c0,c66,c7,c4],[(0,[(0,2,3),(1,2,3),(2,0,1)]),(21,[]),(0,[(0,2,3),(1,2,3),(0,0,1)]),(46,[]),(19,[(1,1,2)]),(40,[(1,0,3)]),(67,[]),(21,[(2,0,3)]),(71,[])],[],[[0,1,2],[3,4],[1,5],[3,5,6],[3,4],[7,5],[3,5,8],[3,5],[4,5],[3,6]]),
 ([0x55555500555500,c0,c2,c7,c4],[(46,[]),(19,[(1,1,2)]),(67,[]),(71,[]),(9,[(0,1,2),(1,1,2)]),(21,[(2,1,2)]),(64,[]),(40,[(1,0,3)]),(69,[])],[],[[0,1],[1,0],[0,1],[1,0],[2,3,4],[4,2,5],[6,3],[3,7],[2,4,8],[3,2]]),
 ([0x5555555555555500,c0,c67,c7,c4],[(69,[]),(19,[(0,1,2),(1,1,2)]),(46,[]),(71,[]),(9,[(1,1,2)]),(21,[(2,1,2)]),(40,[(1,2,3)]),(64,[]),(67,[])],[],[[0,1,2],[3,2,4],[0,1,2],[0,2,1],[4,0,3],[5,6],[7,3],[3,0,6],[7,0],[3,8]])]
def d543 : List StD := []
lemma d544 : LevelN d443 d442 3 d543 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d545 : levelOK d442 d535 3 (d543.map Prod.fst) ((d542.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d546 : levelOK d442 d535 3 (d543.map Prod.fst) ((d542.drop (1*8)).take 8) = true := by decide +kernel
lemma d547 : LevelN d443 d442 4 d542 := levelStep d445 d536 d544 (chunks 8 d542 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d545
  · exact d546
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d548 : levelOK d442 d535 4 (d542.map Prod.fst) ((d541.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d549 : levelOK d442 d535 4 (d542.map Prod.fst) ((d541.drop (1*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d550 : levelOK d442 d535 4 (d542.map Prod.fst) ((d541.drop (2*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d551 : levelOK d442 d535 4 (d542.map Prod.fst) ((d541.drop (3*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d552 : levelOK d442 d535 4 (d542.map Prod.fst) ((d541.drop (4*8)).take 8) = true := by decide +kernel
lemma d553 : LevelN d443 d442 5 d541 := levelStep d445 d536 d547 (chunks 8 d541 5 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d548
  · exact d549
  · exact d550
  · exact d551
  · exact d552
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d554 : levelOK d442 d535 5 (d541.map Prod.fst) ((d540.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d555 : levelOK d442 d535 5 (d541.map Prod.fst) ((d540.drop (1*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d556 : levelOK d442 d535 5 (d541.map Prod.fst) ((d540.drop (2*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d557 : levelOK d442 d535 5 (d541.map Prod.fst) ((d540.drop (3*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d558 : levelOK d442 d535 5 (d541.map Prod.fst) ((d540.drop (4*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d559 : levelOK d442 d535 5 (d541.map Prod.fst) ((d540.drop (5*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d560 : levelOK d442 d535 5 (d541.map Prod.fst) ((d540.drop (6*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d561 : levelOK d442 d535 5 (d541.map Prod.fst) ((d540.drop (7*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d562 : levelOK d442 d535 5 (d541.map Prod.fst) ((d540.drop (8*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d563 : levelOK d442 d535 5 (d541.map Prod.fst) ((d540.drop (9*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d564 : levelOK d442 d535 5 (d541.map Prod.fst) ((d540.drop (10*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d565 : levelOK d442 d535 5 (d541.map Prod.fst) ((d540.drop (11*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d566 : levelOK d442 d535 5 (d541.map Prod.fst) ((d540.drop (12*8)).take 8) = true := by decide +kernel
lemma d567 : LevelN d443 d442 6 d540 := levelStep d445 d536 d553 (chunks 8 d540 13 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d554
  · exact d555
  · exact d556
  · exact d557
  · exact d558
  · exact d559
  · exact d560
  · exact d561
  · exact d562
  · exact d563
  · exact d564
  · exact d565
  · exact d566
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d568 : levelOK d442 d535 6 (d540.map Prod.fst) ((d539.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d569 : levelOK d442 d535 6 (d540.map Prod.fst) ((d539.drop (1*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d570 : levelOK d442 d535 6 (d540.map Prod.fst) ((d539.drop (2*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d571 : levelOK d442 d535 6 (d540.map Prod.fst) ((d539.drop (3*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d572 : levelOK d442 d535 6 (d540.map Prod.fst) ((d539.drop (4*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d573 : levelOK d442 d535 6 (d540.map Prod.fst) ((d539.drop (5*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d574 : levelOK d442 d535 6 (d540.map Prod.fst) ((d539.drop (6*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d575 : levelOK d442 d535 6 (d540.map Prod.fst) ((d539.drop (7*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d576 : levelOK d442 d535 6 (d540.map Prod.fst) ((d539.drop (8*8)).take 8) = true := by decide +kernel
lemma d577 : LevelN d443 d442 7 d539 := levelStep d445 d536 d567 (chunks 8 d539 9 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d568
  · exact d569
  · exact d570
  · exact d571
  · exact d572
  · exact d573
  · exact d574
  · exact d575
  · exact d576
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d578 : levelOK d442 d535 7 (d539.map Prod.fst) ((d538.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d579 : levelOK d442 d535 7 (d539.map Prod.fst) ((d538.drop (1*8)).take 8) = true := by decide +kernel
lemma d580 : LevelN d443 d442 8 d538 := levelStep d445 d536 d577 (chunks 8 d538 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d578
  · exact d579
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d581 : levelOK d442 d535 8 (d538.map Prod.fst) ((d537.drop (0*8)).take 8) = true := by decide +kernel
lemma d582 : LevelN d443 d442 9 d537 := levelStep d445 d536 d580 (chunks 8 d537 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d581
  ))
lemma d583 : LowN d443 d442 10 := lowSearch d445 d582 (by decide +kernel)
def d584 : Nat := 0xfffffffefffefefefffffffefffefefe
def d585 : List Nat := [0, 1, 2, 3, 4, 5]
def d586 : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4),(3,16,24),(4,8,24),(5,8,40)]
lemma d587 : baseOK d584 d585 d586 = true := by decide +kernel
lemma d588 : SliceN d585 d584 (c28,6,[1, 2, 3, 4, 5]) := mkSlice (w:=0) d587 d171 d180 (by decide +kernel)
def d589 : List SliceD := [(c28,6,[1, 2, 3, 4, 5])]
lemma d590 : ∀ s ∈ d589, SliceN d585 d584 s := by
  unfold d589
  simp only [List.forall_mem_cons]
  exact ⟨d588,by simp⟩
def d591 : List StD := dupD [
 (l6,[(0,[])],[],[[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]])]
def d592 : List StD := []
lemma d593 : LevelN d585 d584 5 d592 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d594 : levelOK d584 d589 5 (d592.map Prod.fst) ((d591.drop (0*8)).take 8) = true := by decide +kernel
lemma d595 : LevelN d585 d584 6 d591 := levelStep d587 d590 d593 (chunks 8 d591 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d594
  ))
lemma d596 : LowN d585 d584 7 := lowSearch d587 d595 (by decide +kernel)
def d597 : Nat := 0xffffffffffffffeefffefffafefeeca0
def d598 : List Nat := [0, 1, 2, 3, 4, 5, 6]
def d599 : List (Nat × Nat × Nat) := [(0,4,5),(1,8,10),(2,1,5),(3,2,10),(4,1,17),(5,1,33),(6,1,65)]
lemma d600 : baseOK d597 d598 d599 = true := by decide +kernel
lemma d601 : SliceN d598 d597 (c24,9,[5, 6, 0, 4, 2, 3]) := mkSlice (w:=0) d600 d197 d215 (by decide +kernel)
lemma d602 : SliceN d598 d597 (c23,9,[4, 6, 0, 5, 2, 1]) := mkSlice (w:=0) d600 d197 d215 (by decide +kernel)
lemma d603 : SliceN d598 d597 (c31,10,[5, 0, 6, 3, 1, 2]) := mkSlice (w:=0) d600 d267 d383 (by decide +kernel)
lemma d604 : SliceN d598 d597 (c43,10,[4, 0, 6, 1, 3, 2]) := mkSlice (w:=0) d600 d267 d383 (by decide +kernel)
lemma d605 : SliceN d598 d597 (0xffffffffffffffff,10,[4, 3, 5, 0, 2, 1]) := mkSlice (w:=0) d600 d445 d583 (by decide +kernel)
lemma d606 : SliceN d598 d597 (0x5050505050505050505050505050505,7,[6, 3, 1, 4, 5]) := mkSlice (w:=0) d600 d154 d167 (by decide +kernel)
lemma d607 : SliceN d598 d597 (c35,7,[6, 5, 0, 4, 3]) := mkSlice (w:=0) d600 d154 d167 (by decide +kernel)
lemma d608 : SliceN d598 d597 (c32,7,[5, 3, 6, 1, 2]) := mkSlice (w:=0) d600 d108 d137 (by decide +kernel)
lemma d609 : SliceN d598 d597 (0x11111111111111111111111111111111,6,[5, 6, 4, 2, 3]) := mkSlice (w:=0) d600 d141 d150 (by decide +kernel)
lemma d610 : SliceN d598 d597 (c12,7,[3, 4, 6, 2, 5, 0]) := mkSlice (w:=2) d600 d587 d596 (by decide +kernel)
lemma d611 : SliceN d598 d597 (c58,7,[6, 4, 0, 5, 1]) := mkSlice (w:=0) d600 d154 d167 (by decide +kernel)
lemma d612 : SliceN d598 d597 (c36,6,[4, 6, 5, 2, 1]) := mkSlice (w:=0) d600 d141 d150 (by decide +kernel)
lemma d613 : SliceN d598 d597 (c9,7,[1, 5, 6, 4, 0, 2]) := mkSlice (w:=8) d600 d587 d596 (by decide +kernel)
lemma d614 : SliceN d598 d597 (c60,6,[0, 2, 6, 5, 4]) := mkSlice (w:=0) d600 d184 d193 (by decide +kernel)
lemma d615 : SliceN d598 d597 (0xcc00cc00cc00cc00cc00cc00cc00cc,6,[4, 6, 0, 5, 2]) := mkSlice (w:=2) d600 d171 d180 (by decide +kernel)
lemma d616 : SliceN d598 d597 (c83,6,[5, 6, 4, 0, 2]) := mkSlice (w:=8) d600 d171 d180 (by decide +kernel)
lemma d617 : SliceN d598 d597 (c8,7,[0, 4, 5, 1, 3, 6]) := mkSlice (w:=4) d600 d587 d596 (by decide +kernel)
lemma d618 : SliceN d598 d597 (0x1010101010101010101010101010101,5,[6, 5, 3, 4]) := mkSlice (w:=0) d600 d59 d68 (by decide +kernel)
lemma d619 : SliceN d598 d597 (c118,6,[4, 5, 1, 3, 6]) := mkSlice (w:=4) d600 d171 d180 (by decide +kernel)
lemma d620 : SliceN d598 d597 (0xf0f0f0f000000000f0f0f0f0,6,[0, 4, 3, 1, 6]) := mkSlice (w:=4) d600 d171 d180 (by decide +kernel)
lemma d621 : SliceN d598 d597 (c0,6,[3, 4, 0, 2, 5]) := mkSlice (w:=2) d600 d171 d180 (by decide +kernel)
lemma d622 : SliceN d598 d597 (c53,6,[0, 5, 3, 1, 6]) := mkSlice (w:=4) d600 d171 d180 (by decide +kernel)
lemma d623 : SliceN d598 d597 (0x5555555555555555,7,[1, 2, 5, 3, 4]) := mkSlice (w:=0) d600 d387 d436 (by decide +kernel)
lemma d624 : SliceN d598 d597 (0xcc00cc00cc00cc,5,[4, 2, 0, 5]) := mkSlice (w:=2) d600 d85 d94 (by decide +kernel)
lemma d625 : SliceN d598 d597 (c44,7,[5, 0, 6, 3, 2]) := mkSlice (w:=0) d600 d154 d167 (by decide +kernel)
lemma d626 : SliceN d598 d597 (c40,6,[3, 6, 0, 5, 2]) := mkSlice (w:=2) d600 d171 d180 (by decide +kernel)
lemma d627 : SliceN d598 d597 (c115,7,[6, 4, 0, 2, 3]) := mkSlice (w:=0) d600 d108 d137 (by decide +kernel)
lemma d628 : SliceN d598 d597 (0xff00ff0000000000ff00ff00,6,[1, 6, 2, 4, 0]) := mkSlice (w:=8) d600 d171 d180 (by decide +kernel)
lemma d629 : SliceN d598 d597 (c110,5,[5, 3, 6, 2]) := mkSlice (w:=0) d600 d59 d68 (by decide +kernel)
lemma d630 : SliceN d598 d597 (c59,7,[4, 1, 6, 3, 2]) := mkSlice (w:=0) d600 d108 d137 (by decide +kernel)
lemma d631 : SliceN d598 d597 (c41,5,[0, 6, 5, 4]) := mkSlice (w:=0) d600 d72 d81 (by decide +kernel)
lemma d632 : SliceN d598 d597 (c3,6,[1, 5, 2, 4, 0]) := mkSlice (w:=8) d600 d171 d180 (by decide +kernel)
lemma d633 : SliceN d598 d597 (c112,5,[6, 4, 1, 5]) := mkSlice (w:=0) d600 d59 d68 (by decide +kernel)
lemma d634 : SliceN d598 d597 (0x5500550000000000550055,5,[4, 1, 6, 2]) := mkSlice (w:=0) d600 d59 d68 (by decide +kernel)
lemma d635 : SliceN d598 d597 (0x3300330033003300,5,[5, 2, 4, 0]) := mkSlice (w:=8) d600 d85 d94 (by decide +kernel)
lemma d636 : SliceN d598 d597 (0x33000000330000003300000033,5,[0, 5, 2, 6]) := mkSlice (w:=0) d600 d72 d81 (by decide +kernel)
lemma d637 : SliceN d598 d597 (0x3300330000000000330033,5,[0, 4, 2, 6]) := mkSlice (w:=0) d600 d72 d81 (by decide +kernel)
lemma d638 : SliceN d598 d597 (0x33003300330033,5,[0, 2, 4, 5]) := mkSlice (w:=0) d600 d72 d81 (by decide +kernel)
lemma d639 : SliceN d598 d597 (0x55005500550055,4,[2, 4, 1, 5]) := mkSlice (w:=0) d600 d23 d37 (by decide +kernel)
def d640 : List SliceD := [(c24,9,[5, 6, 0, 4, 2, 3]),(c23,9,[4, 6, 0, 5, 2, 1]),(c31,10,[5, 0, 6, 3, 1, 2]),(c43,10,[4, 0, 6, 1, 3, 2]),(0xffffffffffffffff,10,[4, 3, 5, 0, 2, 1]),(0x5050505050505050505050505050505,7,[6, 3, 1, 4, 5]),(c35,7,[6, 5, 0, 4, 3]),(c32,7,[5, 3, 6, 1, 2]),(0x11111111111111111111111111111111,6,[5, 6, 4, 2, 3]),(c12,7,[3, 4, 6, 2, 5, 0]),(c58,7,[6, 4, 0, 5, 1]),(c36,6,[4, 6, 5, 2, 1]),(c9,7,[1, 5, 6, 4, 0, 2]),(c60,6,[0, 2, 6, 5, 4]),(0xcc00cc00cc00cc00cc00cc00cc00cc,6,[4, 6, 0, 5, 2]),(c83,6,[5, 6, 4, 0, 2]),(c8,7,[0, 4, 5, 1, 3, 6]),(0x1010101010101010101010101010101,5,[6, 5, 3, 4]),(c118,6,[4, 5, 1, 3, 6]),(0xf0f0f0f000000000f0f0f0f0,6,[0, 4, 3, 1, 6]),(c0,6,[3, 4, 0, 2, 5]),(c53,6,[0, 5, 3, 1, 6]),(0x5555555555555555,7,[1, 2, 5, 3, 4]),(0xcc00cc00cc00cc,5,[4, 2, 0, 5]),(c44,7,[5, 0, 6, 3, 2]),(c40,6,[3, 6, 0, 5, 2]),(c115,7,[6, 4, 0, 2, 3]),(0xff00ff0000000000ff00ff00,6,[1, 6, 2, 4, 0]),(c110,5,[5, 3, 6, 2]),(c59,7,[4, 1, 6, 3, 2]),(c41,5,[0, 6, 5, 4]),(c3,6,[1, 5, 2, 4, 0]),(c112,5,[6, 4, 1, 5]),(0x5500550000000000550055,5,[4, 1, 6, 2]),(0x3300330033003300,5,[5, 2, 4, 0]),(0x33000000330000003300000033,5,[0, 5, 2, 6]),(0x3300330000000000330033,5,[0, 4, 2, 6]),(0x33003300330033,5,[0, 2, 4, 5]),(0x55005500550055,4,[2, 4, 1, 5])]
lemma d641 : ∀ s ∈ d640, SliceN d598 d597 s := by
  unfold d640
  simp only [List.forall_mem_cons]
  exact ⟨d601,d602,d603,d604,d605,d606,d607,d608,d609,d610,d611,d612,d613,d614,d615,d616,d617,d618,d619,d620,d621,d622,d623,d624,d625,d626,d627,d628,d629,d630,d631,d632,d633,d634,d635,d636,d637,d638,d639,by simp⟩
def d642 : List StD := [
 ([c11,c12,c8,c9,c10,c13,c15],[(0,[]),(1,[]),(2,[]),(3,[]),(4,[])],[(8,10),(6,7),(9,11),(16,17),(16,20),(1,5),(2,10),(12,13),(3,11),(1,17),(2,18),(1,33),(4,36),(1,65),(2,66),(12,14),(3,7),(16,18),(3,35),(9,13),(6,14),(4,20),(6,70),(9,25),(8,40),(8,72),(18,34),(20,68),(34,66)],[[0,1000,1001,1002],[1003,1004,1001,1005],[1,1006,1007,1008],[2,1009,1010],[3,1011,1012],[4,1013,1014],[0,1000,1015,1016],[0,1,1017,1000,1006],[0,2,1010,1009],[0,3,1018,1011],[0,4,1014,1013],[1,1006,1019,1020],[2,1021,1009],[3,1012,1011],[4,1022,1013],[1,2,1023,1009],[1,3,1024,1011],[1,4,1025,1013],[2,3,1026],[2,4,1027],[3,4,1028]])]
def d643 : List StD := [
 ([c11,c12,c46,c8,c9,c10,c13,c15],[(0,[]),(5,[]),(6,[]),(7,[]),(1,[(1,2,5)]),(2,[(1,1,4)]),(3,[(1,1,3)]),(4,[(1,3,5)]),(8,[]),(9,[]),(1,[])],[(6,7),(16,20),(1,5),(3,11),(2,10),(1,17),(2,18),(1,33),(2,35),(1,65),(2,66),(3,5),(1,7),(9,11),(3,33),(32,40),(4,20),(4,36),(8,72),(9,13),(6,14),(6,70),(9,25),(8,40),(18,34),(20,68),(34,66)],[[0,1,1000],[0],[1,2,3,1001,1000,1002],[1,4,1000,1003,1004],[1,5,1005,1006],[1,6,1007,1008],[1,7,1009,1010],[0,1],[0,1011,1,1012],[0,1013,4,1003],[0,5,1006],[0,6,1014],[0,7,1010],[1,8,1001,9,1002],[4,8,10,9,1003,1015],[3,5,9,1005,8,1016],[6,9,1007,8,1017],[7,9,1009,8,1018],[1,4,1001,1019,1020],[1,3,5,1016,1001],[1,6,1017,1007],[1,7,1021,1009],[3,4,5,1022,1005],[4,6,1023,1007],[4,7,1018,1009],[3,5,6,1024],[3,5,7,1025],[6,7,1026]]),
 ([0x22222222222222222222222222222222,c11,c12,c8,c9,c10,c13,c15],[(0,[]),(5,[]),(2,[(1,1,4)]),(7,[]),(1,[]),(3,[(2,1,3)]),(4,[(2,3,5)]),(1,[(2,2,5)])],[(1,5),(1,17),(1,33),(1,65),(6,7),(3,10),(3,7),(8,10),(0,10),(2,18),(3,35),(2,66),(9,13),(6,18),(4,36),(6,66),(9,25),(8,40),(8,72),(18,34),(20,68),(34,66)],[[0],[0,1,2],[1,3,1000],[1,4],[1,3,1001],[1,5,1002],[1,6,1003],[0,1,1004],[1,3,1000],[1,1005,7,1004],[1,3,1001],[1,5,1002],[1,6,1003],[0,1,1006],[0,1007,7,1008],[0,3,1009],[0,5,1010],[0,6,1011],[1,1012,7,1000],[1,3,1013],[1,5,1014],[1,6,1015],[3,1016,7,1001],[5,1017,7,1002],[6,1018,7,1003],[3,5,1019],[3,6,1020],[5,6,1021]]),
 ([c48,c11,c12,c8,c9,c10,c13,c15],[(5,[]),(2,[(2,1,5)]),(6,[]),(0,[]),(2,[(3,1,5)]),(10,[]),(1,[]),(2,[(0,1,5)]),(3,[(0,1,5)]),(4,[(0,3,4)]),(7,[])],[(9,10),(65,68),(3,10),(1,17),(1,33),(1,65),(10,12),(8,14),(2,10),(3,17),(3,33),(3,65),(6,10),(2,14),(6,18),(4,36),(6,66),(9,17),(9,33),(9,65),(18,34),(20,68),(34,66)],[[0,1],[0,2,3],[0,4],[0,5,6],[0,7],[0,8],[0,9],[0,2,1000],[0,1001,10,2],[0,5,1002],[0,7,1003],[0,8,1004],[0,9,1005],[0,2,1006,1007],[2,5,1008],[2,7,1009],[2,8,1010],[2,9,1011],[0,5,1012,1013],[0,7,1014],[0,8,1015],[0,9,1016],[5,7,1017],[5,8,1018],[5,9,1019],[7,8,1020],[7,9,1021],[8,9,1022]]),
 ([c11,c12,c8,0xfafafafafafafafafafafafafafafafa,c9,c10,c13,c15],[(5,[]),(0,[(1,2,4)]),(2,[(3,1,5)]),(1,[(1,2,4)]),(2,[(1,1,5)]),(3,[(1,1,5)]),(4,[(1,3,4)]),(2,[(2,1,5)])],[(6,7),(4,5),(65,68),(1,5),(12,13),(1,17),(1,33),(1,65),(3,7),(9,11),(16,18),(2,10),(2,18),(3,35),(2,66),(9,13),(4,20),(4,36),(6,70),(3,11),(9,25),(8,40),(8,72),(18,34),(20,68),(34,66)],[[0,1000,1,1001],[0,1002,1000,1003],[0,2],[0,1004,3,1000],[0,4,1005],[0,5,1006],[0,6,1007],[0,1008,1,1003],[0,1009,1],[1,3,1010,1009,1011],[1,4,1012,1005],[1,5,1013,1006],[1,6,1014,1007],[0,7],[0,1015,3,1003],[0,4,1016],[0,5,1017],[0,6,1018],[0,1019,3],[0,4,1005],[0,5,1006],[0,6,1007],[3,4,1020,1005],[3,5,1021,1006],[3,6,1022,1007],[4,5,1023],[4,6,1024],[5,6,1025]]),
 ([c81,c11,c12,c8,c9,c10,c13,c15],[(5,[]),(2,[(0,1,5)]),(0,[]),(2,[(1,1,5)]),(1,[]),(2,[(2,1,5)]),(3,[(2,1,5)]),(4,[(2,3,4)]),(0,[(2,2,4)]),(7,[]),(1,[(2,2,4)])],[(9,11),(3,11),(1,17),(1,33),(1,65),(6,7),(0,5),(12,13),(34,38),(8,14),(16,18),(2,18),(3,35),(2,66),(24,28),(6,66),(9,25),(8,40),(8,72),(18,34),(20,68),(34,66)],[[0,1],[0,1000,2],[0,3],[0,1001,4],[0,5,1002],[0,6,1003],[0,7,1004],[0,1005,8,1000],[0,9,1005,1006],[0,1007,10,1001],[0,5,1002],[0,6,1003],[0,7,1004],[0,1008,8,1009],[8,10,1010,1000,1001],[5,1011,8,1002],[6,1012,8,1003],[7,1013,8,1004],[0,1014,10,1008],[0,5,1014],[0,6,1008],[0,7,1015],[5,1016,10,1002],[6,1017,10,1003],[7,1018,10,1004],[5,6,1019],[5,7,1020],[6,7,1021]]),
 ([c118,c11,c12,c8,c9,c10,c13,c15],[(5,[]),(2,[(1,1,5)]),(6,[]),(2,[(0,1,5)]),(10,[]),(2,[(3,1,5)]),(3,[(3,1,5)]),(4,[(3,3,4)])],[(12,14),(6,14),(4,20),(4,36),(6,70),(9,10),(1,5),(0,5),(3,10),(1,17),(1,33),(1,65),(3,17),(3,33),(9,17),(9,33),(9,65),(18,34),(20,68),(34,66)],[[0,1],[0,2,1000],[0,3],[0,4,1001],[0,5,1002],[0,6,1003],[0,7,1004],[0,2,1005],[0,2,1006,1007],[0,4,1008],[0,5,1009],[0,6,1010],[0,7,1011],[0,2,1000],[2,4,1000],[2,5,1012],[2,6,1013],[2,7,1004],[0,4,1001],[0,5,1002],[0,6,1003],[0,7,1004],[4,5,1014],[4,6,1015],[4,7,1016],[5,6,1017],[5,7,1018],[6,7,1019]]),
 ([c11,c12,c8,c9,c68,c10,c13,c15],[(5,[]),(0,[(1,2,5)]),(10,[]),(7,[]),(1,[]),(2,[(1,1,3)]),(3,[(1,1,4)]),(4,[(1,1,3)]),(11,[]),(0,[]),(12,[])],[(8,10),(9,11),(16,20),(12,13),(1,5),(1,17),(2,18),(1,33),(4,36),(1,65),(2,66),(12,14),(3,7),(3,11),(16,18),(3,35),(5,9),(4,20),(6,70),(9,17),(9,33),(9,65),(18,34),(20,68),(34,66)],[[0,1,1000,1001],[0,2,3,1002,1003,1004],[0,2,4,1003],[2],[0,5,1005,1006],[0,6,1007,1008],[0,7,1009,1010],[0,1,1000,1011,1012],[1,2,4,1013,1000],[1,8,9,10,1000,1014],[1,3,5,1006,1005],[1,6,1015,1007],[1,7,1010,1009],[0,4,1016,1013],[0,8,1002,10,1004],[0,3,5,1017,1002],[0,6,1008,1007],[0,7,1018,1009],[0],[2,3,4,5,1019],[2,4,6,1020],[2,4,7,1021],[3,5,10,1005,8,1006],[6,10,1007,8,1008],[7,10,1009,8,1010],[3,5,6,1022],[3,5,7,1023],[6,7,1024]]),
 ([c65,c11,c12,c8,c9,c10,c13,c15],[(5,[]),(2,[(0,1,3)]),(0,[]),(7,[]),(2,[(1,1,3)]),(3,[(2,1,4)]),(4,[(3,1,3)]),(0,[(2,2,5)]),(1,[])],[(1,5),(1,17),(1,33),(1,65),(9,10),(8,11),(12,13),(3,7),(2,10),(0,10),(2,18),(3,35),(2,66),(6,10),(6,18),(4,36),(6,66),(12,20),(10,34),(8,72),(18,34),(20,68),(34,66)],[[0,1],[0,2],[0,3,1000],[0,4],[0,3,1001],[0,5,1002],[0,6,1003],[0,1004,7,1005],[0,3,1000],[0,8,1006],[0,3,1001],[0,5,1002],[0,6,1003],[0,1007,7,1000],[7,8,1008,1009],[3,1010,7,1001],[5,1011,7,1002],[6,1012,7,1003],[0,8,1013],[0,3,1014],[0,5,1015],[0,6,1016],[3,8,1017],[5,8,1018],[6,8,1019],[3,5,1020],[3,6,1021],[5,6,1022]]),
 ([c11,c12,c8,c116,c9,c10,c13,c15],[(5,[]),(0,[]),(10,[]),(6,[]),(2,[(1,4,5)]),(3,[(1,3,5)]),(4,[(1,4,5)]),(1,[(1,4,5)])],[(5,6),(4,7),(3,7),(34,38),(4,5),(12,13),(3,11),(1,17),(0,17),(1,33),(0,33),(1,65),(0,65),(12,14),(2,18),(3,35),(2,66),(6,10),(6,18),(6,66),(9,25),(8,40),(8,72),(18,34),(20,68),(34,66)],[[0,1,1000,1001],[0,2,3,1002,1003],[0,3,1004],[0,2,1004,1005,1006],[0,4,1007,1008],[0,5,1009,1010],[0,6,1011,1012],[0,1,1002],[0],[1,1013,2,1006],[1,4,1014],[1,5,1015],[1,6,1016],[1],[0,3,1017,7,1002],[0,3,4,1018],[0,3,5,1003],[0,3,6,1019],[2,3,1006],[3,4,1014],[3,5,1015],[3,6,1016],[2,4,1020,1007],[2,5,1021,1009],[2,6,1022,1011],[4,5,1023],[4,6,1024],[5,6,1025]]),
 ([c47,c11,c12,c8,c9,c10,c13,c15],[(5,[]),(10,[]),(2,[(1,4,5)]),(2,[(0,4,5)]),(2,[(3,4,5)]),(3,[(3,3,5)]),(4,[(2,4,5)]),(0,[])],[(4,5),(68,76),(4,20),(4,36),(12,76),(6,7),(3,10),(1,17),(1,33),(1,65),(3,7),(2,10),(3,17),(3,33),(3,65),(9,17),(9,33),(18,34),(20,68),(34,66)],[[0,1,1000],[0,2],[0,3],[0,1,1001],[0,4,1002],[0,5,1003],[0,6,1004],[0,7,1005],[0,1,1000],[0,1,1006],[0,4,1007],[0,5,1008],[0,6,1009],[0,7,1010],[1,7,1011],[4,7,1012],[5,7,1013],[6,7,1014],[0,1,1001],[0,4,1002],[0,5,1003],[0,6,1004],[1,4,1015],[1,5,1016],[1,6,1001],[4,5,1017],[4,6,1018],[5,6,1019]]),
 ([c11,c12,c8,c9,c119,c10,c13,c15],[(0,[]),(10,[]),(1,[]),(13,[]),(5,[]),(9,[]),(2,[(1,3,4)]),(3,[(1,3,4)]),(4,[(1,1,5)]),(6,[])],[(9,11),(8,10),(16,20),(4,5),(1,5),(3,11),(2,10),(6,7),(1,17),(2,18),(1,33),(4,36),(1,65),(2,66),(12,14),(3,35),(6,14),(3,7),(4,20),(6,70),(9,25),(10,34),(8,72),(18,34),(20,68),(34,66)],[[0,1000,1001],[1,1002,1003,1004],[1,2,1005,1006],[3,4,1003,5,1007],[6,1008,1009],[7,1010,1011],[8,1012,1013],[0,1014,1,1000],[0,1,2],[0,1],[0,6,1009],[0,7,1015],[0,8,1013],[1,2,1016,9,1005],[1,3,1002,5,1017],[1,6,1018,1002],[1,7,1011,1010],[1,8,1019,1012],[0],[1,2,6,1020],[1,2,7,1021],[1,2,8,1022],[3,6,5,1009,1008],[3,7,5,1015,1010],[3,8,5,1013,1012],[6,7,1023],[6,8,1024],[7,8,1025]]),
 ([c11,c12,c8,c9,c117,c10,c13,c15],[(5,[]),(6,[]),(10,[]),(2,[(1,3,5)]),(3,[(1,4,5)]),(4,[(1,1,4)]),(0,[(1,4,5)]),(1,[])],[(4,5),(6,7),(9,11),(9,13),(24,28),(5,12),(4,13),(1,17),(0,17),(1,33),(0,33),(1,65),(0,65),(10,12),(6,14),(2,18),(3,35),(2,66),(4,36),(6,70),(12,20),(12,36),(8,72),(4,20),(18,34),(20,68),(34,66)],[l2,[0,1,2,1003,1004],[0,2,1005,1006],[0,2,1000],[0,3,1007,1008],[0,4,1009,1010],[0,5,1011,1012],[0,2,1013,6,1003],[1,2,1014,1002],[1,2,1002],[1,3,1015,1007],[1,4,1016,1009],[1,5,1017,1011],[0,2,7,1003],[2,7],[0,2,3,1004],[0,2,4,1018],[0,2,5,1019],[0],[2,3,1020],[2,4,1021],[2,5,1022],[2,3,1023],[2,4,1018],[2,5,1019],[3,4,1024],[3,5,1025],[4,5,1026]]),
 ([c74,c11,c12,c8,c9,c10,c13,c15],[(10,[]),(5,[]),(6,[]),(2,[(0,3,5)]),(2,[(1,3,5)]),(2,[(3,3,5)]),(3,[(3,4,5)]),(4,[(3,1,4)]),(1,[])],[(4,5),(68,70),(4,20),(4,36),(6,70),(5,6),(3,10),(1,17),(1,33),(1,65),(2,10),(3,17),(3,33),(9,13),(9,17),(9,33),(9,65),(18,34),(20,68),(34,66)],[[0,1,1000],[0,2,1001],[0,3],[0,4],[0,5,1002],[0,6,1003],[0,7,1004],[1,2,1005],[0,1,1000],[0,1,1006],[1,5,1007],[1,6,1008],[1,7,1009],[0,2,1001],[0,2,1010],[2,5,1011],[2,6,1012],[2,7,1001],[0,1,1013,8],[0,5,1002],[0,6,1003],[0,7,1004],[0,5,1014],[0,6,1015],[0,7,1016],[5,6,1017],[5,7,1018],[6,7,1019]])]
def d644 : List StD := [
 ([c11,c12,c46,c8,c9,c68,c10,c13,c15],[(6,[(1,2,4)]),(5,[]),(0,[(1,2,5)]),(7,[]),(10,[(1,2,4)]),(1,[(1,2,5)]),(3,[(1,1,3),(1,1,4)]),(4,[(1,3,5),(1,1,3)]),(14,[]),(8,[]),(15,[]),(11,[])],[(1,5),(1,17),(1,33),(1,65),(3,11),(6,18),(4,36),(6,66),(18,34),(20,68),(34,66)],[[0,1,2],[0],[0,1,3,1000],[1,4,5],[4],[1,3,1001],[1,6,1002],[1,7,1003],[1],[1,2,8],[2,5,1004],[2,5,8],[2,3,8],[2,6,8],[2,7,8],[0,1,8,9],[4,5,2,8,9],[2,4],[3,8,9],[6,8,9],[7,8,9],[1,5,10],[1,10,11],[1,3,1005],[1,6,1006],[1,7,1007],[1],[3,5,10],[5,6,10],[5,7,10],[3,10,11],[6,10,11],[7,10,11],[3,6,1008],[3,7,1009],[6,7,1010]]),
 ([c12,c46,c8,c9,c68,c10,c13,c15],[(0,[(1,2,5)]),(7,[]),(14,[]),(10,[]),(12,[]),(2,[(1,1,3)]),(2,[(1,1,3),(1,1,4)]),(3,[(1,1,4)]),(3,[(1,1,4),(1,1,3)]),(4,[(1,1,3)]),(4,[(1,1,3),(1,3,5)]),(15,[]),(10,[(1,2,4)]),(6,[])],[(3,10),(12,13),(4,20),(4,36),(8,72),(6,7),(1,17),(1,33),(6,70),(18,34),(20,68),(34,66)],[[0,1],[0,2],[0,2,1000],[0,2],[0,2],[0,2],[0,2],[2,3,1001],[2,3,0,4],[0,2],[1,2,5,6,1002],[2,7,8,1003],[2,9,10,1004],[2,11],[11,12,13,1005],[1,6,1002,12,1006],[8,1003,12,1007],[10,1008,12,1004],[1],[1,2,6,11],[2,8,11],[2,10,11],[1,6,11,1002],[8,11,1003],[10,11,1008],[1,6,8,1009],[1,6,10,1010],[8,10,1011]]),
 ([c65,c12,c46,c8,c9,c10,c13,c15],[(6,[(2,2,4)]),(7,[]),(0,[(2,2,5)]),(1,[(1,2,5)]),(0,[(0,2,5)]),(5,[]),(2,[(1,1,4),(1,1,3)]),(3,[(1,1,3),(2,1,4)]),(4,[(1,3,5),(3,1,3)]),(14,[]),(8,[]),(15,[])],[(1,5),(1,17),(1,33),(1,65),(2,10),(6,18),(4,36),(6,66),(18,34),(20,68),(34,66)],[[0,1,2,3],[1,4],[0,1,5,1000],[1,3,6],[1,5,1001],[1,7,1002],[1,8,1003],[1],[0,2,5,9],[0,2,3,1004],[0,1,2,9],[0,2,7,9],[0,2,8,9],[0,5,9,10],[3,9,11],[1,9,10],[7,9,10],[8,9,10],[0,3,5,11],[0,1,5,1005],[0,5,7,1006],[0,5,8,1007],[1,3,11],[3,7,11],[3,8,11],[1,7,1008],[1,8,1009],[7,8,1010]]),
 ([c11,c46,c8,c116,c9,c10,c13,c15],[(0,[]),(10,[(1,2,4)]),(7,[(1,3,4)]),(6,[]),(5,[]),(2,[(1,1,4),(1,5,6)]),(14,[]),(2,[(1,1,4),(1,4,5)]),(3,[(1,1,3),(1,3,5)]),(4,[(1,3,5),(1,4,5)]),(16,[]),(10,[]),(9,[]),(17,[]),(18,[])],[(3,5),(2,5),(3,10),(1,17),(1,33),(1,65),(9,17),(9,33),(9,65),(18,34),(20,68),(34,66)],[[0],[1,2,3,4,1000,1001],[2,3,4,5],[1,2,4,6,1002],[2,4,7,1003],[2,4,8,1004],[2,4,9,1005],[1,3,6,10],[3,4],[1,6,11,12,13],[2,6,7,13],[6,8,13],[6,9,13],[0],[1,3,6,14],[1,2,3,7,14],[1,3,8,14],[1,3,9,14],[1,3,6,12],[2,3,6],[3,6],[3,6],[1,2,6,7,1006],[1,6,8,1007],[1,6,9,1008],[2,7,8,1009],[2,7,9,1010],[8,9,1011]]),
 ([c11,c12,c8,0xfefefefefefefefefefefefefefefefe,c9,c10,c13,c15],[(7,[(1,3,4)]),(0,[(1,2,4)]),(2,[(1,1,4),(1,5,6)]),(14,[]),(10,[(1,2,4)]),(6,[]),(16,[]),(5,[]),(19,[]),(20,[]),(0,[(2,2,4)]),(10,[]),(17,[])],[(3,10),(1,17),(1,33),(1,65),(9,17),(9,33),(9,65),(18,34),(20,68),(34,66)],[[0,1,2,3],[0,4,5,1,6],[3,5],[0,3,7,1000],[0,2,7,1001],[0,7,8,1002],[0,7,9,1003],[1,3],[1,3,7],[1,3,9],[0,1,2,3],[1,3],[1,3],[3,5,10],[3,5,6],[0,2,5,6],[4,5,6],[4,5,6],[3,11,6,12],[0,2,3,12],[3,8,12],[3,9,12],[0,2,3,1004],[3,8,1005],[3,9,1006],[0,2,8,1007],[0,2,9,1008],[8,9,1009]]),
 ([0xe0e0e0e0e0e0e0e0e0e0e0e0e0e0e0e,c11,c12,c8,c9,c10,c13,c15],[(7,[(2,3,4)]),(0,[(2,2,4)]),(10,[(1,2,4)]),(5,[]),(14,[]),(16,[]),(15,[]),(21,[]),(19,[]),(4,[]),(2,[(1,1,4),(3,5,6)]),(6,[]),(20,[]),(22,[(2,0,1)]),(23,[])],[(2,10),(1,17),(1,33),(1,65),(12,13),(4,5),(68,69),(9,11),(3,17),(3,33),(68,70),(9,25),(8,40),(64,72),(8,72),(18,34),(64,80),(64,96)],[[0,1,2],[1,3],[3,4],[2,5,6,1000],[0,5,7,1001],[5,8,1002],[5,1003,9],[0,1,3,10],[0,2,11,3,5],[0,2,3,1004,1005],[0,3,7,1001],[0,3,8,1002],[0,3,1006,12,1003],[1,3,5],[1,1007,2,1000],[0,1,7,1008],[1,8,1009],[1,1010,13,1007],[2,3,5],[0,2,3,5],[2,3,5],[2,3,5],[0,2,7,1011,1001],[2,8,1012,1002],[2,12,1000,14,1013,1014],[0,7,8,1015],[0,7,1016,12,1001],[8,1017,12,1002]]),
 ([c11,c12,c8,c9,0xffeeffeeffeeffeeffeeffeeffeeffee,c10,c13,c15],[(14,[]),(0,[(1,2,5)]),(10,[(1,2,4)]),(7,[(1,1,3)]),(5,[(1,1,2)]),(15,[]),(0,[(3,2,5)]),(24,[(1,1,3)]),(25,[]),(26,[(1,2,4)]),(27,[]),(20,[]),(1,[(2,2,5)]),(10,[]),(16,[]),(0,[(2,2,5)]),(2,[]),(3,[]),(4,[])],[(16,20),(6,7),(1,5),(1,17),(2,18),(1,33),(2,35),(1,65),(2,66),(4,20),(4,36),(6,70),(16,80),(18,34),(34,66)],[[0,1],[2,3,1000,4,1001,1002],[0,1,3,5],[0,6],[3,7,4,8,1003,1004],[3,9,10,1005,1006],[3,11,1007,1008],[0,1],[0,1,8],[0,12],[0,1],[0,1],[0,1],[0,5],[0,2,13,14,1000],[2,3,8,1009,1000],[2,9,10,1010,1005],[2,11,1011,1007],[0,15],[0,5],[0,5],[0,5],[0,3,16,8,1009],[0,9,17,10,1010],[0,11,18,1012],[3,8,10,1013],[3,8,11,1012],[9,10,11,1014]]),
 ([0xee00ee00ee00ee00ee00ee00ee00ee,c11,c12,c8,c9,c10,c13,c15],[(0,[(2,2,5)]),(10,[(1,2,4)]),(14,[]),(5,[]),(16,[]),(15,[]),(0,[(1,2,5)]),(7,[(3,1,3)]),(8,[]),(17,[]),(28,[]),(27,[]),(23,[]),(1,[(1,2,5)])],[(1,5),(1,17),(1,33),(1,65),(6,18),(4,36),(6,66),(18,34),(20,68),(34,66)],[[0,1],[0,2,3],[1,2,3,4,5],[2,6],[2,5],[2,5],[2,5],[0,2],[1,7,8,9,1000],[1,2,5],[7,8,10,1001],[7,8,11,1002],[7,8,12,1003],[0,2],[0,2,11,13],[0,2],[0,2],[0,2],[1,2,5],[1,7,9,10,1004],[1,9,11,1005],[1,9,12,1006],[1,2,5],[1,2,5],[1,2,5],[7,10,11,1007],[7,10,12,1008],[11,12,1009]]),
 ([c11,c12,c46,c8,c9,c117,c10,c13,c15],[(14,[]),(0,[(1,4,5)]),(10,[(1,2,4)]),(5,[]),(15,[]),(2,[(1,1,4),(1,3,5)]),(3,[(1,1,3),(1,4,5)]),(4,[(1,3,5),(1,1,4)]),(16,[]),(17,[]),(18,[])],[(6,7),(1,17),(1,33),(1,65),(9,11),(18,34),(20,68),(34,66)],[[0,1],[0,1],[2,3,1000],[0,3,4],[2,3,4],[3,5,1001],[3,6,1002],[3,7,1003],[0,3],[1,0],[0,1,1004,2],[1,0],[1,0],[1,0],[1,0],[2,0,8],[0,2,4],[2,0,4],[5,0,9],[6,0,9],[7,0,9],[0,2,3],[0],[2,5,10],[2,6,10],[2,7,10],[2,3],[0,4],[0,4],[0,4],[2,4],[2,4],[2,4],[5,6,1005],[5,7,1006],[6,7,1007]]),
 ([c11,c12,c8,c9,0xff22ff22ff22ff22ff22ff22ff22ff22,c10,c13,c15],[(14,[]),(0,[(1,2,5)]),(17,[]),(10,[(2,2,4)]),(5,[]),(7,[]),(27,[]),(23,[]),(1,[(2,2,5)]),(15,[])],[(1,5),(1,17),(1,33),(1,65),(6,18),(4,36),(6,66),(18,34),(20,68),(34,66)],[[0,1],[2,3,4,5,1000],[0,1,2,4],[0,1],[2,4,5,1001],[2,4,6,1002],[2,4,7,1003],[0,1],[0,1,6,8],[0,1,6,8],[0,1],[0,1],[0,1],[0,4,6],[0,4,6],[2,4,5,1004],[2,4,6,1005],[2,4,7,1006],[0,2],[0,5,6],[0,6,9],[0,6],[0,5,6],[0,6,9],[0,6],[5,6,1007],[5,7,1008],[6,7,1009]]),
 ([c11,c12,c8,0xff22ff22ff22ff22ff22ff22ff22ff22,c10,c13,c15],[(17,[]),(5,[]),(14,[]),(15,[]),(0,[(1,2,5)]),(7,[]),(2,[(3,1,3)]),(29,[]),(22,[]),(27,[]),(11,[])],[(6,7),(1,5),(1,17),(1,33),(1,65),(3,7),(2,10),(2,18),(3,35),(2,66),(6,18),(4,36),(6,66),(18,34),(20,68),(34,66)],[[0,1,2,1000,3,4],[0,1,5,1000,1001],[0,1,3,4,2,6],[0,1,5,1002],[0,1,7,1003],[0,1,8,1004],[0,1,2,1005,3,4],[0,4,9,1006,10],[0,4,5,1007],[0,4,7,1008],[0,4,8,1009],[0,1,3,1001,2,1005],[0,1,5,1010],[0,1,7,1011],[0,1,8,1012],[2,5,3,1002,1007],[2,7,3,1003,1008],[2,8,3,1004,1009],[5,7,1013],[5,8,1014],[7,8,1015]]),
 ([0x22222222222222222222222222222222,c12,c8,c9,c68,c10,c13,c15],[(14,[]),(2,[(1,1,3),(1,1,4)]),(5,[]),(15,[]),(10,[]),(0,[(3,2,5)]),(2,[(1,1,3),(2,1,4)]),(3,[(1,1,4),(2,1,3)]),(22,[]),(0,[(1,2,5)]),(11,[])],[(1,5),(1,17),(1,33),(1,65),(3,10),(6,18),(4,36),(6,66),(18,34),(20,68),(34,66)],[[0,1],[0,2,1000],[0,2,3,4],[0,3,5],[0,6,1001],[0,7,1002],[0,8,1003],[0,2,3],[0,9,1004],[0,3,5],[0,3],[0,3],[0,3],[0,2,3],[2,3,10],[2,6,1005],[2,7,1006],[2,8,1007],[0,2],[0,3],[0,3],[0,3],[3,6,10],[3,7,10],[3,8,10],[6,7,1008],[6,8,1009],[7,8,1010]]),
 ([c11,0xecececececececececececececececec,c8,c9,c10,c13,c15],[(5,[]),(14,[]),(2,[(1,1,4)]),(0,[(0,2,4)]),(2,[(0,1,5),(1,4,6)]),(22,[]),(10,[]),(29,[]),(2,[(1,4,5)]),(20,[]),(17,[]),(6,[])],[(3,5),(3,10),(1,17),(1,33),(1,65),(2,10),(3,17),(3,33),(3,65),(6,10),(6,18),(4,36),(6,66),(9,17),(9,33),(9,65),(18,34),(20,68),(34,66)],[[0,1,2,3],[0,4,1000,5],[0,6,1001],[0,4,1002],[0,7,1003],[0,5,1004],[0,1,8,3],[1,6,9,1005,10,11],[4,1,1006,10,11],[7,1,1007,10,11],[5,1,1008,10,11],[0,6,1009,1000],[0,4,1010],[0,7,1011],[0,5,1012],[1,4,6,1013],[1,6,7,1014],[1,5,6,1015],[4,7,1016],[4,5,1017],[5,7,1018]]),
 ([c11,c12,c8,0xffa0ffa0ffa0ffa0ffa0ffa0ffa0ffa0,c10,c13,c15],[(22,[]),(6,[]),(10,[]),(2,[(1,1,3)]),(7,[]),(29,[]),(2,[(1,3,5)]),(2,[(2,3,5)])],[(9,10),(5,9),(1,17),(1,33),(1,65),(10,12),(2,10),(3,17),(3,33),(3,65),(6,18),(4,36),(6,66),(9,17),(9,33),(9,65),(18,34),(20,68),(34,66)],[[0,1,1000],[0,1,1001],[0,2,3],[0,4,1002],[0,5,1003],[0,4,1004],[1,2,1005,1001],[1,2,1006],[1,4,1007],[1,5,1008],[0,1,1009],[1,2,6,7],[1,4,1010],[1,5,1011],[0,1,1012],[2,4,1013],[2,5,1014],[0,2,1015],[4,5,1016],[0,4,1017],[0,5,1018]]),
 ([c11,c12,c8,c9,0xffffa0a0ffffa0a0ffffa0a0ffffa0a0,c13,c15],[(22,[]),(6,[]),(10,[]),(2,[(0,1,5)]),(29,[]),(7,[])],[(9,10),(65,68),(3,10),(1,33),(1,65),(10,12),(8,14),(2,10),(3,17),(3,33),(3,65),(6,10),(2,14),(4,36),(6,66),(9,17),(9,33),(9,65),(18,34),(20,68),(34,66)],[[0,1,1000],[0,1,1001],[0,2,1002],[0,3],[0,4,1003],[0,4,1004],[1,2,1005,1006],[1,2,1007],[1,5,1008],[1,4,1009],[0,1,1010],[1,2,1011,1012],[1,3],[1,4,1013],[0,1,1014],[2,5,1015],[2,4,1016],[0,2,1017],[4,5,1018],[0,5,1019],[0,4,1020]]),
 ([c11,c12,c8,c9,c10,0xffffffffa0a0a0a0ffffffffa0a0a0a0,c15],[(22,[]),(6,[]),(10,[]),(7,[]),(29,[]),(2,[(1,0,1)]),(2,[(2,0,1)]),(2,[(1,0,5)])],[(9,10),(65,68),(3,10),(1,17),(1,65),(10,12),(8,14),(2,10),(3,17),(3,33),(3,65),(6,10),(2,14),(6,18),(6,66),(9,17),(9,33),(9,65),(18,34),(20,68),(34,66)],[[0,1,1000],[0,1,1001],[0,2,1002],[0,3,1003],[0,4,5,6],[0,3,1004],[1,2,1005,1006],[1,2,1007],[1,3,1008],[1,4,1009],[0,1,1010],[1,2,1011,1012],[1,3,1013],[1,4,7],[0,1,1014],[2,3,1015],[2,4,1016],[0,2,1017],[3,4,1018],[0,3,1019],[0,4,1020]]),
 ([c11,c12,c8,c9,c10,c13,0xffffffffffffffffa0a0a0a0a0a0a0a0],[(22,[]),(6,[]),(10,[]),(7,[]),(29,[]),(2,[(1,1,2)]),(2,[(3,1,2)]),(2,[(1,2,5)])],[(9,10),(5,68),(3,10),(1,17),(1,33),(10,12),(8,14),(2,10),(3,17),(3,33),(3,65),(6,10),(2,14),(6,18),(4,36),(9,17),(9,33),(9,65),(18,34),(20,68),(34,66)],[[0,1,1000],[0,1,1001],[0,2,1002],[0,3,1003],[0,4,1004],[0,3,5,6],[1,2,1005,1006],[1,2,1007],[1,3,1008],[1,4,1009],[0,1,1010],[1,2,1011,1012],[1,3,1013],[1,4,1014],[0,1,7],[2,3,1015],[2,4,1016],[0,2,1017],[3,4,1018],[0,3,1019],[0,4,1020]]),
 ([c11,c12,c8,0xfafafafafafafafafafafafafafafafa,c9,c119,c10,c13,c15],[(6,[]),(5,[(1,1,2)]),(10,[]),(14,[(1,2,4)]),(13,[(1,0,1)]),(30,[]),(2,[(1,1,5),(1,3,4)]),(3,[(1,1,5),(1,3,4)]),(4,[(1,3,4),(1,1,5)]),(0,[(1,2,4)]),(14,[]),(2,[(1,3,4),(2,1,5)]),(1,[(1,2,4)]),(16,[]),(15,[])],[(6,7),(3,11),(1,17),(1,33),(1,65),(3,7),(2,18),(3,35),(2,66),(9,13),(4,20),(4,36),(6,70),(9,25),(10,34),(8,72),(18,34),(20,68),(34,66)],[[0,1,1000],[0,1,1000],[0],[1,2,1001],[1,3,1000,4,5],[1,6,1002],[1,7,1003],[1,8,1004],[0,1,1005,9],[0,1,10],[0,2],[2],[0,6,1006],[0,7,1007],[0,8,1008],[1,11],[0,2,1009,12],[0,3,13,4],[0,6,1010],[0,7,1011],[0,8,1012],[1,2,14],[1,3,10,4,5],[1,6,1002],[1,7,1003],[1,8,1004],[0],[2,6,1013],[2,7,1014],[2,8,1015],[5,6,1006],[5,7,1007],[5,8,1008],[6,7,1016],[6,8,1017],[7,8,1018]]),
 ([c11,c12,c8,c9,0xfffafffafffafffafffafffafffafffa,c10,c13,c15],[(22,[(1,1,3)]),(6,[(1,2,4)]),(15,[]),(5,[]),(10,[]),(2,[(1,1,5),(1,3,6)]),(16,[]),(27,[]),(31,[]),(6,[]),(32,[]),(1,[(2,2,4)])],[(5,6),(1,17),(1,33),(1,65),(3,17),(3,33),(3,65),(18,34),(20,68),(34,66)],[[0,1,2,3,1000],[0,1,4,3,5,6],[0,2,3,4],[2,3,4],[0,3,5,1001],[0,3,7,1002],[0,3,8,1003],[1,2,3,6],[1,2,4,7],[1,2,9,6,10],[1,2,5,1004],[1,2,7,1005],[0,1,2,8,1006],[1,2,3,6],[2,3,11],[1,3,5,6],[1,3,6],[0,1,3,6],[2,3],[2,4],[2,4],[0,2,4],[2,5,10],[2,7,10],[0,2,10],[5,7,1007],[0,5,8,1008],[0,7,8,1009]]),
 ([c11,c12,0xcececececececececececececececece,c8,c9,c10,c13,c15],[(6,[]),(22,[]),(14,[]),(7,[]),(29,[]),(5,[]),(0,[(2,2,4)]),(20,[]),(10,[]),(17,[])],[(4,5),(3,10),(1,17),(1,33),(1,65),(6,10),(6,18),(4,36),(6,66),(9,17),(9,33),(9,65),(18,34),(20,68),(34,66)],[[0,1,2],[0],[0,1,1000],[1,2,1001],[1,3,1002],[1,4,1003],[1,3,1004],[0,1],[0,5,2,6],[0,2,7],[0,2],[0,2],[0,1,2],[0,2,6],[2,8,7,9],[2,3,9],[2,4,9],[1,2,9],[0,2,1005],[0,3,1006],[0,4,1007],[0,1,1008],[2,3,1009],[2,4,1010],[1,2,1011],[3,4,1012],[1,3,1013],[1,4,1014]]),
 ([c11,c12,c8,c9,0xff0aff0aff0aff0aff0aff0aff0aff0a,c10,c13,c15],[(6,[(1,2,4)]),(22,[]),(15,[]),(10,[]),(7,[]),(29,[]),(27,[]),(6,[]),(11,[])],[(5,6),(4,5),(1,17),(1,33),(1,65),(10,12),(3,17),(3,33),(3,65),(6,18),(4,36),(6,66),(18,34),(20,68),(34,66)],[[0,1,2,1000],[0,1,3,1001],[1,2,3],[1,2,3],[1,4,1002],[1,5,1003],[1,4,1004],[0,2,3,1005],[0,2,3,6],[0,2,7,6,8],[0,2,4,1006],[0,2,5,1007],[0,1,2,1008],[0,2,8],[0,2,3,8],[0,3,4,1009],[0,3,5,1010],[0,1,3,1011],[1],[2,3],[2,3],[1,2,3],[2,4,8],[2,5,8],[1,2,8],[4,5,1012],[1,4,1013],[1,5,1014]]),
 ([c81,c11,c12,c8,c9,c119,c10,c13,c15],[(2,[(1,3,4),(0,1,5)]),(6,[]),(22,[(1,0,3)]),(14,[]),(2,[(1,3,4),(1,1,5)]),(10,[]),(15,[]),(13,[]),(2,[(1,3,4),(2,1,5)]),(29,[(1,1,3)]),(15,[(2,3,4)]),(13,[(2,0,1)]),(30,[]),(0,[(2,2,4)]),(11,[]),(16,[])],[(1,17),(1,33),(1,65),(6,7),(3,11),(10,12),(2,18),(3,35),(2,66),(6,10),(6,18),(4,36),(6,66),(9,25),(10,34),(8,72),(18,34),(20,68),(34,66)],[[0,1],[1,2,3],[1,2,4],[2,5,6],[2,3,7],[0,2,8,1000],[2,9,1001],[2,9,1002],[1,2,1003],[1,2,1003],[2,5,1004],[2,10,1003,11,12],[2,8,1000],[2,9,1001],[2,9,1002],[1,5,1005,13],[1,5],[5],[1,8,1006],[1,9,1007],[1,2,1008],[1,5,1009,14],[1,10,15,11],[1,8,1010],[1,9,1011],[1,2,1012],[1],[5,8,1013],[5,9,1014],[2,5,1015],[8,10,1006,11,12],[9,10,1007,11,12],[2,10,1008,11,12],[8,9,1016],[2,8,1017],[2,9,1018]]),
 ([c11,c12,c8,c116,c9,c68,c10,c13,c15],[(15,[]),(14,[]),(10,[]),(5,[]),(6,[(1,2,4)]),(2,[(1,4,5),(1,1,3)]),(3,[(1,3,5),(1,1,4)]),(4,[(1,4,5),(1,1,3)]),(16,[]),(18,[]),(32,[])],[(3,7),(12,13),(1,17),(1,33),(1,65),(3,11),(18,34),(20,68),(34,66)],[[0,1],[2,3,1000,1001],[1,3,4],[0,1],[0,1],[3,5,1002],[3,6,1003],[3,7,1004],[0,1],[1,2],[0,2,1005,4],[0,4,1],[0,1],[0,1],[0,1],[0],[0,1],[0,2,8],[2,5,9],[2,6,9],[2,7,9],[0,1,2],[0,1,4],[4,1],[4,1],[4,1],[0,3],[1,0],[1,0],[1,0],[5,0,10],[6,0,10],[7,0,10],[5,6,1006],[5,7,1007],[6,7,1008]]),
 ([0x33223322332233223322332233223322,c11,c12,c8,c9,c10,c13,c15],[(15,[]),(2,[(2,1,4)]),(10,[]),(27,[]),(16,[]),(14,[]),(29,[]),(10,[(2,2,4)]),(29,[(3,1,3)]),(11,[]),(32,[]),(25,[]),(33,[]),(20,[]),(0,[(1,2,5)])],[(1,5),(1,17),(1,33),(1,65),(6,18),(4,36),(6,66),(18,34),(20,68),(34,66)],[[0,1,2],[0,3],[0,2,4,5],[0,2,6],[0,1,5],[0,3,5],[0,5],[0,5],[7,8,9,10,1000],[0,5],[8,9,11,1001],[3,9,12,1002],[8,9,13,1003],[0,5],[0,9,11,14],[0,5],[0,5],[0,5],[0,5],[7,10,11,1004],[3,7,10,12,1005],[7,10,13,1006],[0,5],[0,5],[0,5],[3,11,12,1007],[11,13,1008],[3,12,13,1009]]),
 ([c11,c12,c8,c68,c117,c10,c13,c15],[(29,[(1,3,4)]),(15,[]),(32,[]),(10,[]),(2,[(1,1,3),(1,3,5)]),(27,[]),(4,[(1,1,3),(1,1,4)]),(18,[]),(2,[(1,1,3),(2,3,5)])],[(9,10),(5,9),(5,8),(1,17),(1,33),(1,65),(3,17),(3,33),(3,65),(18,34),(20,68),(34,66)],[[0,1,2,1000],[0,2,3,1001,1002],[1,2,3],[0,1,3],[0,2,4,1003],[0,2,5,1004],[0,2,6,1005],[1,2,7],[1,2,5],[1,2,5],[1,4,1006],[0,1,5,1007],[1,6,1008],[1,2,3,7],[1,2,8],[2,4,7],[0,2,5,7],[2,6,7],[1,3,7],[1,2],[0,1,2],[1,2],[1,2],[0,1,2],[1,2],[0,4,5,1009],[4,6,1010],[0,5,6,1011]]),
 ([0xf0a0f0a0f0a0f0a0f0a0f0a0f0a0f0a,c11,c12,c8,c9,c10,c13,c15],[(10,[]),(15,[]),(32,[]),(14,[]),(29,[]),(21,[]),(33,[]),(4,[]),(2,[(1,1,3),(3,5,6)]),(18,[]),(31,[]),(6,[(1,2,4)]),(34,[]),(5,[]),(19,[]),(22,[(3,1,3)])],[(8,10),(1,17),(1,33),(1,65),(6,7),(4,5),(68,69),(3,11),(2,18),(3,35),(64,66),(2,66),(9,17),(9,33),(68,76),(18,34),(64,80),(64,96)],[[0],[1,2,3,1000],[0,1],[0,2,4],[2,5,1001],[2,6,1002],[2,1003,7],[1,2,1004,1005],[0,2,5],[0,2,8,9],[2,5,1001],[2,6,1002],[2,1006,10,1003],[0,5],[0,1007,11,1000],[1,5,1008,1001],[1,6,1009,1002],[1,10,1000,12,1010,1011],[0,6,5,13],[0,5,9],[0,5],[0,5],[0,5,1012],[0,6,1013,14],[0,1014,15,1007],[5,6,1015],[5,1016,10,1001],[6,1017,10,1002]]),
 ([c11,c12,0xcceecceecceecceecceecceecceeccee,c8,c9,c10,c13,c15],[(32,[]),(29,[]),(15,[]),(14,[]),(5,[]),(25,[]),(22,[]),(0,[(2,2,5)])],[(1,5),(1,17),(1,33),(1,65),(6,18),(4,36),(6,66),(18,34),(20,68),(34,66)],[[0,1,2,3],[0,1,2,3],[0,1,4,1000],[0,1,2,3],[0,1,5,1001],[0,1,4,1002],[0,1,6,1003],[0],[0,2,3],[0,2,7,5],[2,3],[1,2,3],[2,3],[0,2,3],[0,2,7,5],[2,3],[1,2,3],[2,3],[0,2,3],[0,4,5,1004],[0,1,4,1005],[0,4,6,1006],[0,3,2],[0,1,2,3],[0,3,2],[1,5,1007],[5,6,1008],[1,6,1009]]),
 ([c11,0xcceecceecceecceecceecceecceeccee,c8,c9,c10,c13,c15],[(15,[]),(32,[]),(29,[]),(14,[]),(2,[(1,1,4)]),(2,[(3,1,4)]),(5,[]),(1,[(1,2,5)]),(7,[]),(22,[]),(25,[]),(17,[])],[(1,5),(1,10),(1,17),(1,33),(1,65),(9,13),(2,10),(0,10),(0,18),(4,36),(0,66),(6,18),(6,66),(12,20),(10,34),(8,72),(18,34),(20,68),(34,66)],[[0,1,2,3,4,5],[1,2,6,1000],[1,2,0,1001,3,7],[1,2,8,1002],[1,2,6,1003],[1,2,9,1004],[0,1,6,3,1000,1005],[0,1,7,10,1006,11,1007],[0,4,3,8,1002,1008],[0,2,3,1003,1009],[0,9,3,1004,1010],[1,3,6,0,1005,7],[1,6,8,1011],[1,2,6,1009],[1,6,9,1012],[1,7,8,1013],[1,2,0,1014,7],[1,7,9,1015],[2,8,1016],[8,9,1017],[2,9,1018]]),
 ([c11,c12,c116,c9,c117,c10,c13,c15],[(5,[]),(14,[]),(15,[]),(6,[]),(10,[]),(2,[(1,4,5),(1,3,5)]),(18,[]),(19,[]),(4,[(1,4,5),(1,1,4)])],[(1,17),(1,33),(1,65),(6,10),(18,34),(20,68),(34,66)],[[0,1,2],[0,1,3],[0,1,2],[0,2,4],[0,5,6,1000],[0,6,7,1001],[0,6,8,1002],[0],[1,3,1003],[1,2,3],[1,2],[1,2],[1,2],[1,3,2,4],[1,2,3],[1,3],[1,3],[1,3],[0],[1,2],[1,2],[1,2],[2,4],[2,4],[2,4],[5,7,1004],[5,8,1005],[7,8,1006]]),
 ([c11,c12,c8,c9,0xfffcfffcfffcfffcfffcfffcfffcfffc,c10,c13,c15],[(15,[]),(14,[]),(5,[(1,1,2)]),(18,[]),(10,[]),(19,[]),(5,[]),(30,[]),(25,[]),(31,[]),(0,[(3,4,5)]),(0,[(2,4,5)])],[(1,17),(1,33),(1,65),(18,34),(20,68),(34,66)],[[0,1],[2,3,4,5],[0,1],[0,2,6,3,7],[2,3,8,1000],[2,3,5,1001],[2,3,9,1002],[0,1],[0,4,8,9],[0,4],[0,1],[0,1],[0,1],[0,1],[0,3,10],[2,4,3],[2,4,3],[2,4,3],[0,11],[0,1],[0,1],[0,1],[0,7],[0,5,7],[0,7],[5,8,1003],[8,9,1004],[5,9,1005]]),
 ([0x55445544554455445544554455445544,c11,c12,c8,c9,c10,c13,c15],[(14,[]),(0,[(3,2,5)]),(30,[]),(10,[]),(13,[]),(35,[]),(36,[]),(37,[]),(5,[(1,1,2)]),(29,[(1,1,3)]),(2,[(1,3,4),(3,1,6)]),(1,[(3,2,5)])],[(24,28),(2,18),(6,38),(2,66),(9,11),(4,7),(1,5),(3,11),(2,10),(1,17),(1,33),(1,65),(3,5),(6,66),(9,17),(9,33),(9,65),(18,34),(20,68),(34,66)],[[0],[1,2,3],[2,3,1000,4],[0,1,2,3],[2,5,1001],[2,6,1002],[2,7,1003],[1,1004,8,1005],[2,1006,9,1000],[0,2,1007,8,1008],[5,1009,8,1001],[6,1010,8,1002],[7,1011,8,1003],[1,2,1012,1004],[0,1,2,10,11],[1,5,1001],[1,6,1002],[1,7,1003],[0,2,4,1000],[2,5,1000],[2,6,1002],[2,7,1013],[0,2,5,1014,10],[0,2,6,1015,1007],[0,2,7,1016,1007],[5,6,1017],[5,7,1018],[6,7,1019]]),
 ([0xf0c0f0c0f0c0f0c0f0c0f0c0f0c0f0c,c11,c12,c8,c9,c10,c13,c15],[(5,[(1,1,2)]),(18,[]),(5,[]),(19,[]),(0,[(3,4,5)]),(10,[]),(0,[(1,4,5)]),(35,[]),(37,[]),(2,[(1,3,4),(3,5,6)]),(6,[])],[(24,25),(2,18),(3,35),(2,66),(5,6),(1,65),(12,20),(10,34),(8,72),(18,34),(20,68),(34,66)],[[0,1,2,1000,3],[1,4,5],[1,6],[1,4,0],[1,7,1001],[1,3,1002],[1,8,1003],[0,1,4,1004],[0,1,5,3],[0,1,5,1000],[0,1,7,1000],[0,1,3,1002],[0,1,8,1005],[0,4,1,5],[4,5,9],[4,7,1001],[3,4,1002],[4,8,1003],[0,5,7,1,10],[0,5,1],[0,3,5,1],[0,5,1],[5,7,1006,9],[3,5,1007],[5,8,1008],[3,7,1009],[7,8,1010],[3,8,1011]])]
def d645 : List StD := [
 ([c11,c12,c8,c9,c10,c13,c15,0xffffffffffffffff0e0e0e0e0e0e0e0e],[(5,[(1,0,2)]),(14,[(3,1,4)]),(4,[(1,3,5),(3,4,6)])],[],[[0,1,2],[0,2],[0,2],[0,2],[0,2],[0,2],[0,2],[0,1,2],[2],[2],[2],[2],[0,2],[0,2],[0,2],[0,2],[0,2],[0,1,2],[2],[2],[2],[2],[2],[2],[2],[2],[2],[2]]),
 ([c11,c12,c8,c9,c10,c13,c15,0xffffffffffffffff0f0a0f0a0f0a0f0a],[(5,[(1,0,1)]),(23,[(3,1,2)]),(30,[(1,0,1)]),(34,[]),(10,[(1,0,2)]),(19,[]),(21,[]),(31,[]),(38,[]),(14,[]),(22,[(3,1,3)])],[(5,6),(1,17),(1,33),(3,17),(3,33),(3,65),(1,65),(18,34),(24,72),(64,96)],[[0,1,1000,2,3],[0,4,5],[0,3,4],[0,6,1001],[0,5,1002],[0,3,4],[0,4,1],[0,1,5],[3,4,7],[3,6,1003],[3,5,1004],[3,7,1005,1006],[3,8,9],[0,3,5],[0,5],[0,5,6],[0,3,5],[0,3],[4,3],[4,3],[3,4,0,10],[0,3],[5,6,1007],[1,3,6,1008],[6,8,1001],[1,3,5,1009],[5,8,1002],[5]])]
def d646 : List StD := []
lemma d647 : LevelN d598 d597 7 d646 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d648 : levelOK d597 d640 7 (d646.map Prod.fst) ((d645.drop (0*8)).take 8) = true := by decide +kernel
lemma d649 : LevelN d598 d597 8 d645 := levelStep d600 d641 d647 (chunks 8 d645 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d648
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d650 : levelOK d597 d640 8 (d645.map Prod.fst) ((d644.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d651 : levelOK d597 d640 8 (d645.map Prod.fst) ((d644.drop (1*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d652 : levelOK d597 d640 8 (d645.map Prod.fst) ((d644.drop (2*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d653 : levelOK d597 d640 8 (d645.map Prod.fst) ((d644.drop (3*8)).take 8) = true := by decide +kernel
lemma d654 : LevelN d598 d597 9 d644 := levelStep d600 d641 d649 (chunks 8 d644 4 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d650
  · exact d651
  · exact d652
  · exact d653
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d655 : levelOK d597 d640 9 (d644.map Prod.fst) ((d643.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d656 : levelOK d597 d640 9 (d644.map Prod.fst) ((d643.drop (1*8)).take 8) = true := by decide +kernel
lemma d657 : LevelN d598 d597 10 d643 := levelStep d600 d641 d654 (chunks 8 d643 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d655
  · exact d656
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d658 : levelOK d597 d640 10 (d643.map Prod.fst) ((d642.drop (0*8)).take 8) = true := by decide +kernel
lemma d659 : LevelN d598 d597 11 d642 := levelStep d600 d641 d657 (chunks 8 d642 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d658
  ))
lemma d660 : LowN d598 d597 12 := lowSearch d600 d659 (by decide +kernel)

def sevenInputs : List Sig := rootsW [0,1,2,3,4,5,6]
def graph : Sig := W d597
lemma graph_proper : proper graph := (baseOK_ok d600).prop
def sampleSeven (r : Row) (i : Fin 7) : Bool := bit r (sevenInputs.getD i.val zero)
lemma sevenList : List.ofFn (fun i : Fin 7 => sevenInputs.getD i.val zero) = sevenInputs := rfl
lemma sevenSampled (r : Row) : List.ofFn (sampleSeven r) = sevenInputs.map (bit r) := by
  rw [←sevenList,List.map_ofFn]
  rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 0 in
lemma sevenTable : ∀ r : Row, bit r graph = target (sampleSeven r) := by decide +kernel

lemma sevenEval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates sevenInputs).getD i zero) =
      (C.wires (List.ofFn (sampleSeven r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sevenSampled]
  rfl


def lowRow (i : Fin 7) : Row := Fin.ofNat 128 (([4, 8, 1, 2, 1, 1, 1] : List Nat).getD i.val 0)
def highRow (i : Fin 7) : Row := Fin.ofNat 128 ((1 <<< i.val) ||| (([4, 8, 1, 2, 1, 1, 1] : List Nat).getD i.val 0))

set_option maxHeartbeats 1000000 in
lemma allSevenRequired :
    (∀ i : Fin 7, bit (lowRow i) graph ≠ bit (highRow i) graph) ∧
    (∀ i j : Fin 7, i ≠ j →
      bit (lowRow i) (sevenInputs.getD j.val zero) =
      bit (highRow i) (sevenInputs.getD j.val zero)) := by decide +kernel

lemma physicalSigned (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 7 → Bool, C.eval (List.ofFn x)=target x) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k sevenInputs.toFinset := by
  have goalEq : (execute C.gates sevenInputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (sevenEval C legal C.output r).trans ((computes (sampleSeven r)).trans (sevenTable r).symm)
  have out := get_rep (u:=true) (execute C.gates sevenInputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract (u:=true) C.gates sevenInputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : sevenInputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ sevenInputs) : ∃ i : Fin 7, sevenInputs.getD i.val zero = a := by
    rw [←sevenList] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = sevenInputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run sevenInputs (sevenInputs.getD i.val zero) sub (lowRow i) (highRow i)
        (allSevenRequired.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply allSevenRequired.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k,hk,eq ▸ run⟩

lemma excludes : Impossible true graph 11 sevenInputs.toFinset := by
  intro k small run
  have steps := list_run run sevenInputs (by decide +kernel) rfl
  obtain ⟨q, bank, built, hit, limit⟩ := contraction (observe_proper graph_proper)
    steps (sevenInputs.map observe) Reach.start (fun _ h => Or.inl h)
  have bound := d660 q bank built hit
  omega

lemma gates_lower (gs : List Gate) (out : Nat)
    (legal : PEqualNP.MetaComplexity.FanInTwo (Circuit.mk gs out))
    (computes : ∀ x : Fin 7 → Bool, (Circuit.mk gs out).eval (List.ofFn x) = target x) :
    12 ≤ gs.length := by
  obtain ⟨k, hk, hr⟩ := physicalSigned (Circuit.mk gs out) legal computes
  have hc : gs.countP (fun g => !isNot g) ≤ gs.length := List.countP_le_length
  change k ≤ gs.countP (fun g => !isNot g) at hk
  by_contra hn
  exact excludes k (by omega) hr

end Completion01Proof

def completion01Perm : Fin 7 → Fin 7 := ![6, 4, 3, 2, 1, 0, 5]

def completion45Perm : Fin 7 → Fin 7 := ![0, 1, 2, 3, 4, 6, 5]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma completion01_target_iso : ∀ x : Fin 7 → Bool,
    completedEdgeFun (0, 1) (fun i => x (completion01Perm i)) = Completion01Proof.target x := by
  decide

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma completion45_target_iso : ∀ x : Fin 7 → Bool,
    completedEdgeFun (4, 5) (fun i => x (completion45Perm i)) = Completion01Proof.target x := by
  decide

lemma completion01_posted_iso (x : Fin 7 → Bool) :
    (postedEdgeFun (fun i => x (completion01Perm i)) ||
      pairAndInput (0, 1) (fun i => x (completion01Perm i))) = Completion01Proof.target x := by
  simpa only [completedEdgeFun, edgeFun_eq_posted] using completion01_target_iso x

lemma completion45_posted_iso (x : Fin 7 → Bool) :
    (postedEdgeFun (fun i => x (completion45Perm i)) ||
      pairAndInput (4, 5) (fun i => x (completion45Perm i))) = Completion01Proof.target x := by
  simpa only [completedEdgeFun, edgeFun_eq_posted] using completion45_target_iso x

lemma completion_lower_of_iso (p : Fin 7 × Fin 7) (ρ : Fin 7 → Fin 7)
    (hiso : ∀ x : Fin 7 → Bool, (postedEdgeFun (fun i => x (ρ i)) ||
      pairAndInput p (fun i => x (ρ i))) = Completion01Proof.target x)
    (gs : List Gate) (out : ℕ)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hf : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) =
      (postedEdgeFun x || pairAndInput p x)) : 12 ≤ gs.length := by
  have hb := primaryRename_basis ρ ⟨gs, out⟩
    (fun op => op = GateOp.and ∨ op = GateOp.or) hgs
  have hlower := Completion01Proof.gates_lower (primaryRename ρ ⟨gs, out⟩).gates
    (primaryRename ρ ⟨gs, out⟩).output
    (by
      intro g hg
      refine ⟨?_, (hb g hg).2⟩
      rcases (hb g hg).1 with he | he <;> simp [he])
    (by
      intro x
      change (primaryRename ρ ⟨gs, out⟩).eval (List.ofFn x) = _
      rw [primaryRename_eval, hf]
      exact hiso x)
  simpa only [primaryRename_length] using hlower

lemma completion01_lower (gs : List Gate) (out : ℕ)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hf : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) =
      (postedEdgeFun x || pairAndInput (0, 1) x)) : 12 ≤ gs.length :=
  completion_lower_of_iso (0, 1) completion01Perm completion01_posted_iso gs out hgs hf

lemma completion45_lower (gs : List Gate) (out : ℕ)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hf : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) =
      (postedEdgeFun x || pairAndInput (4, 5) x)) : 12 ≤ gs.length :=
  completion_lower_of_iso (4, 5) completion45Perm completion45_posted_iso gs out hgs hf

lemma completion01_45_lower (p : Fin 7 × Fin 7) (hp : p = (0, 1) ∨ p = (4, 5))
    (gs : List Gate) (out : ℕ)
    (hgs : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hf : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) =
      (postedEdgeFun x || pairAndInput p x)) : 12 ≤ gs.length := by
  rcases hp with rfl | rfl
  · exact completion01_lower gs out hgs hf
  · exact completion45_lower gs out hgs hf

lemma forced_pair01_45_size_lower_bound
    (pre suffix : List Gate) (inputs : List ℕ) (o : ℕ)
    (p : Fin 7 × Fin 7) (hp : p = (0, 1) ∨ p = (4, 5))
    (hpre : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsuf : ∀ g ∈ suffix, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hf : ∀ x : Fin 7 → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, o⟩ (List.ofFn x) = postedEdgeFun x)
    (hpair : ∀ q ∈ nonedgePairs,
      Circuit.eval ⟨pre ++ ⟨GateOp.and, []⟩ :: suffix, o⟩ (List.ofFn (pairPoint q)) =
        pairAndInput p (pairPoint q)) :
    14 ≤ (pre ++ ⟨GateOp.not, inputs⟩ :: suffix).length :=
  forced_pair_completion_size_lower_bound pre suffix inputs o p
    (by rcases hp with rfl | rfl <;> decide) hpre hsuf hf hpair (completion01_45_lower p hp)

lemma fixedAnd_pair01_45_replacement
    (pre suffix : List Gate) (inputs : List ℕ) (o : ℕ)
    (p : Fin 7 × Fin 7) (hp : p = (0, 1) ∨ p = (4, 5))
    (hpre : ∀ g ∈ pre, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hsuf : ∀ g ∈ suffix, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hpair : ∀ q ∈ nonedgePairs,
      cutInput pre inputs (List.ofFn (pairPoint q)) = pairAndInput p (pairPoint q))
    (hf : ∀ x : Fin 7 → Bool,
      Circuit.eval ⟨pre ++ ⟨GateOp.not, inputs⟩ :: suffix, o⟩ (List.ofFn x) = postedEdgeFun x)
    (hsmall : (pre ++ ⟨GateOp.not, inputs⟩ :: suffix).length ≤ 13) :
    ∃ (gs : List Gate) (out : ℕ),
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gs.length ≤ (pre ++ ⟨GateOp.not, inputs⟩ :: suffix).length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) = postedEdgeFun x :=
  fixedAnd_pair_reduce_to_positive_bound pre suffix inputs o p
    (by rcases hp with rfl | rfl <;> decide) hpre hsuf hpair hf hsmall (completion01_45_lower p hp)

end PEqualNP.Outside.L_meta_10760
