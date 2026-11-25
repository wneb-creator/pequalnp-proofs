import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1884.SoleReader

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

def agree (t : Nat) (w z : List Bool) : Prop :=
  w.length = z.length ∧ t < w.length ∧
    ∀ i, i ≠ t → w.getD i false = z.getD i false

lemma append_agree {t : Nat} {w z : List Bool} {a b : Bool}
    (h : agree t w z) (hab : a = b) : agree t (w ++ [a]) (z ++ [b]) := by
  have ht : t < w.length := h.2.1
  refine ⟨by simp [h.1], by simp; omega, ?_⟩
  intro i hit
  by_cases hi : i < w.length
  · rw [List.getD_append _ _ _ _ hi,
      List.getD_append _ _ _ _ (h.1 ▸ hi)]
    exact h.2.2 i hit
  · by_cases he : i = w.length
    · subst i
      simpa [List.getD_eq_getElem?_getD, h.1] using hab
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp [← h.1]; omega)]

lemma gate_agree {t : Nat} {w z : List Bool} (h : agree t w z)
    (g : Gate) (ht : t ∉ g.inputs) :
    g.op.eval (g.inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => z.getD i false) := by
  congr 1
  apply List.map_congr_left
  intro i hi
  exact h.2.2 i (fun he => ht (he ▸ hi))

lemma run_agree (gs : List Gate) {t : Nat} (w z : List Bool) (h : agree t w z)
    (away : ∀ g ∈ gs, t ∉ g.inputs) : agree t (run gs w) (run gs z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    apply ih (step w g) (step z g)
    · exact append_agree h (gate_agree h g (away g (by simp)))
    · intro g' hg'
      exact away g' (by simp [hg'])

lemma partner_independent (pre : List Gate) {t a : Nat} (w z : List Bool)
    (h : agree t w z) (away : ∀ g ∈ pre, t ∉ g.inputs) (hat : a ≠ t) :
    (run pre w).getD a false = (run pre z).getD a false :=
  (run_agree pre w z h away).2.2 a hat

lemma factor (pre post : List Gate) (g : Gate) {t out : Nat} (w z : List Bool)
    (h : agree t w z) (pre_away : ∀ g ∈ pre, t ∉ g.inputs)
    (post_away : ∀ g ∈ post, t ∉ g.inputs) (hout : out ≠ t)
    (same : g.op.eval (g.inputs.map fun i => (run pre w).getD i false) =
      g.op.eval (g.inputs.map fun i => (run pre z).getD i false)) :
    (Circuit.mk (pre ++ g :: post) out).eval w =
      (Circuit.mk (pre ++ g :: post) out).eval z := by
  have hp := run_agree pre w z h pre_away
  have hs := append_agree hp same
  have hf := (run_agree post _ _ hs post_away).2.2 out hout
  simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons]
  exact hf

lemma ofFn_agree {n : Nat} (t : Fin n) (x y : Fin n → Bool)
    (h : ∀ i, i ≠ t → x i = y i) : agree t.val (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i hit
  by_cases hi : i < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
    simp only [hi, dite_true, Option.getD_some]
    exact h ⟨i, hi⟩ (fun he => hit (congrArg Fin.val he))
  · rw [List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]

lemma run_input (gs : List Gate) (w : List Bool) (i : Nat) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (step w g)).getD i false = w.getD i false
    rw [ih (step w g) (by simp [step]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma factor_or {n : Nat} (pre post : List Gate) (t : Fin n) (a out : Nat)
    (x y : Fin n → Bool) (off : ∀ i, i ≠ t → x i = y i)
    (pre_away : ∀ g ∈ pre, t.val ∉ g.inputs)
    (post_away : ∀ g ∈ post, t.val ∉ g.inputs) (hout : out ≠ t.val)
    (same : (x t || (run pre (List.ofFn x)).getD a false) =
      (y t || (run pre (List.ofFn y)).getD a false)) :
    (Circuit.mk (pre ++ Gate.mk .or [t.val, a] :: post) out).eval (List.ofFn x) =
      (Circuit.mk (pre ++ Gate.mk .or [t.val, a] :: post) out).eval (List.ofFn y) := by
  apply factor pre post _ _ _ (ofFn_agree t x y off) pre_away post_away hout
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    List.all_cons, List.all_nil, Bool.or_false, Bool.and_true, id]
  rw [run_input pre (List.ofFn x) t.val (by simp),
      run_input pre (List.ofFn y) t.val (by simp)]
  simpa [List.getD_eq_getElem?_getD] using same

lemma factor_and {n : Nat} (pre post : List Gate) (t : Fin n) (a out : Nat)
    (x y : Fin n → Bool) (off : ∀ i, i ≠ t → x i = y i)
    (pre_away : ∀ g ∈ pre, t.val ∉ g.inputs)
    (post_away : ∀ g ∈ post, t.val ∉ g.inputs) (hout : out ≠ t.val)
    (same : (x t && (run pre (List.ofFn x)).getD a false) =
      (y t && (run pre (List.ofFn y)).getD a false)) :
    (Circuit.mk (pre ++ Gate.mk .and [t.val, a] :: post) out).eval (List.ofFn x) =
      (Circuit.mk (pre ++ Gate.mk .and [t.val, a] :: post) out).eval (List.ofFn y) := by
  apply factor pre post _ _ _ (ofFn_agree t x y off) pre_away post_away hout
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    List.all_cons, List.all_nil, Bool.or_false, Bool.and_true, id]
  rw [run_input pre (List.ofFn x) t.val (by simp),
      run_input pre (List.ofFn y) t.val (by simp)]
  simpa [List.getD_eq_getElem?_getD] using same


lemma free_input_agree (t : Fin 10) (ht0 : t ≠ 0) (x y : Fin 10 → Bool)
    (h : ∀ i, i ≠ t → x i = y i) :
    agree t.val (List.ofFn x ++ [!x 0]) (List.ofFn y ++ [!y 0]) := by
  have hbase := ofFn_agree t x y h
  have hzero : x 0 = y 0 := h 0 (Ne.symm ht0)
  exact append_agree hbase (by rw [hzero])

lemma free_input_pin (x : Fin 10 → Bool) (t : Fin 10) :
    (List.ofFn x ++ [!x 0]).getD t.val false = x t := by
  rw [List.getD_append _ _ _ _ (by simp)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, Fin.is_lt, dite_true,
    Option.getD_some]

lemma free_partner_independent (pre : List Gate) (t : Fin 10) (ht0 : t ≠ 0)
    (a : Nat) (hat : a ≠ t.val) (away : ∀ g ∈ pre, t.val ∉ g.inputs)
    (x y : Fin 10 → Bool) (h : ∀ i, i ≠ t → x i = y i) :
    (run pre (List.ofFn x ++ [!x 0])).getD a false =
      (run pre (List.ofFn y ++ [!y 0])).getD a false :=
  partner_independent pre _ _ (free_input_agree t ht0 x y h) away hat

lemma free_factor_or (pre post : List Gate) (t : Fin 10) (ht0 : t ≠ 0) (a out : Nat)
    (x y : Fin 10 → Bool) (off : ∀ i, i ≠ t → x i = y i)
    (pre_away : ∀ g ∈ pre, t.val ∉ g.inputs)
    (post_away : ∀ g ∈ post, t.val ∉ g.inputs) (hout : out ≠ t.val)
    (same : (x t || (run pre (List.ofFn x ++ [!x 0])).getD a false) =
      (y t || (run pre (List.ofFn y ++ [!y 0])).getD a false)) :
    (Circuit.mk (pre ++ Gate.mk .or [t.val, a] :: post) out).eval (List.ofFn x ++ [!x 0]) =
      (Circuit.mk (pre ++ Gate.mk .or [t.val, a] :: post) out).eval
        (List.ofFn y ++ [!y 0]) := by
  apply factor pre post _ _ _ (free_input_agree t ht0 x y off) pre_away post_away hout
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    Bool.or_false, id]
  rw [run_input pre _ t.val (by simp; omega),
      run_input pre _ t.val (by simp; omega), free_input_pin, free_input_pin]
  exact same

lemma free_factor_and (pre post : List Gate) (t : Fin 10) (ht0 : t ≠ 0) (a out : Nat)
    (x y : Fin 10 → Bool) (off : ∀ i, i ≠ t → x i = y i)
    (pre_away : ∀ g ∈ pre, t.val ∉ g.inputs)
    (post_away : ∀ g ∈ post, t.val ∉ g.inputs) (hout : out ≠ t.val)
    (same : (x t && (run pre (List.ofFn x ++ [!x 0])).getD a false) =
      (y t && (run pre (List.ofFn y ++ [!y 0])).getD a false)) :
    (Circuit.mk (pre ++ Gate.mk .and [t.val, a] :: post) out).eval (List.ofFn x ++ [!x 0]) =
      (Circuit.mk (pre ++ Gate.mk .and [t.val, a] :: post) out).eval
        (List.ofFn y ++ [!y 0]) := by
  apply factor pre post _ _ _ (free_input_agree t ht0 x y off) pre_away post_away hout
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
    Bool.and_true, id]
  rw [run_input pre _ t.val (by simp; omega),
      run_input pre _ t.val (by simp; omega), free_input_pin, free_input_pin]
  exact same

end PEqualNP.Outside.L_meta_1884.SoleReader

namespace PEqualNP.Outside.L_meta_1884.SafeNot

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

def above (w z : List Bool) : Prop :=
  w.length = z.length ∧ ∀ i, w.getD i false ≤ z.getD i false

lemma eval_mono (g : Gate) (hg : g.op = .and ∨ g.op = .or)
    (w z : List Bool)
    (h : ∀ i ∈ g.inputs, w.getD i false ≤ z.getD i false) :
    g.op.eval (g.inputs.map (fun i => w.getD i false)) ≤
      g.op.eval (g.inputs.map (fun i => z.getD i false)) := by
  apply Bool.le_iff_imp.mpr
  intro hw
  rcases hg with hg | hg
  · rw [hg] at hw ⊢
    change (g.inputs.map (fun i => z.getD i false)).all id = true
    apply List.all_eq_true.mpr
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    apply Bool.le_iff_imp.mp (h i hi)
    exact List.all_eq_true.mp hw _ (List.mem_map.mpr ⟨i, hi, rfl⟩)
  · rw [hg] at hw ⊢
    obtain ⟨b, hb, ht⟩ := List.any_eq_true.mp hw
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    apply List.any_eq_true.mpr
    exact ⟨z.getD i false, List.mem_map.mpr ⟨i, hi, rfl⟩,
      Bool.le_iff_imp.mp (h i hi) ht⟩

lemma append_above {w z : List Bool} {a b : Bool} (h : above w z) (hab : a ≤ b) :
    above (w ++ [a]) (z ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i
  by_cases hi : i < w.length
  · rw [List.getD_append _ _ _ _ hi,
      List.getD_append _ _ _ _ (h.1 ▸ hi)]
    exact h.2 i
  · by_cases he : i = w.length
    · subst i
      simpa [List.getD_eq_getElem?_getD, h.1] using hab
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp [← h.1]; omega)]

lemma run_above (gs : List Gate) (w z : List Bool) (h : above w z)
    (allowed : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    above (run gs w) (run gs z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    apply ih (step w g) (step z g)
    · exact append_above h (eval_mono g (allowed g (by simp)) w z (fun i _ => h.2 i))
    · intro g' hg'
      exact allowed g' (by simp [hg'])

lemma replace_safe_not (pre post : List Gate) (ins : List Nat) (out : Nat)
    (input : List Bool)
    (allowed : ∀ g ∈ post, g.op = .and ∨ g.op = .or)
    (safe : ((ins.map fun i => (run pre input).getD i false).headD false) = true →
      (Circuit.mk (pre ++ Gate.mk .not ins :: post) out).eval input = true) :
    (Circuit.mk (pre ++ Gate.mk .and [] :: post) out).eval input =
      (Circuit.mk (pre ++ Gate.mk .not ins :: post) out).eval input := by
  have run_form (op : GateOp) (is : List Nat) :
      (Circuit.mk (pre ++ Gate.mk op is :: post) out).eval input =
        (run post (run pre input ++
          [op.eval (is.map fun i => (run pre input).getD i false)])).getD out false := by
    simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons, run]
    rfl
  cases hh : (ins.map fun i => (run pre input).getD i false).headD false with
  | false => simp only [run_form, GateOp.eval, List.map_nil, List.all_nil, hh, Bool.not_false]
  | true =>
    have ht := safe hh
    have hraise :
        (Circuit.mk (pre ++ Gate.mk .not ins :: post) out).eval input ≤
          (Circuit.mk (pre ++ Gate.mk .and [] :: post) out).eval input := by
      rw [run_form, run_form]
      apply (run_above post _ _ ?_ allowed).2 out
      exact append_above ⟨rfl, fun _ => le_rfl⟩ (by simp [GateOp.eval])
    rw [ht] at hraise ⊢
    exact Bool.le_iff_imp.mp hraise rfl

lemma replace_safe_not_function {α : Type} (pre post : List Gate) (ins : List Nat)
    (out : Nat) (input : α → List Bool) (f : α → Bool)
    (allowed : ∀ g ∈ post, g.op = .and ∨ g.op = .or)
    (computes : ∀ x, (Circuit.mk (pre ++ Gate.mk .not ins :: post) out).eval (input x) = f x)
    (safe : ∀ x, (ins.map fun i => (run pre (input x)).getD i false).headD false = true →
      f x = true) :
    ∀ x, (Circuit.mk (pre ++ Gate.mk .and [] :: post) out).eval (input x) = f x := by
  intro x
  rw [replace_safe_not pre post ins out (input x) allowed (by
    intro h; rw [computes]; exact safe x h), computes]


lemma replace_not_le (pre post : List Gate) (ins : List Nat) (out : Nat)
    (input : List Bool) (allowed : ∀ g ∈ post, g.op = .and ∨ g.op = .or) :
    (Circuit.mk (pre ++ Gate.mk .not ins :: post) out).eval input ≤
      (Circuit.mk (pre ++ Gate.mk .and [] :: post) out).eval input := by
  have h := (run_above post
    (run pre input ++ [GateOp.not.eval (ins.map fun i => (run pre input).getD i false)])
    (run pre input ++ [true])
    (append_above ⟨rfl, fun _ => le_rfl⟩ (Bool.le_true _)) allowed).2 out
  simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons,
    List.map_nil, GateOp.eval, List.all_nil]
  exact h

lemma replace_not_false (pre post : List Gate) (ins : List Nat) (out : Nat)
    (input : List Bool)
    (hfalse : (ins.map fun i => (run pre input).getD i false).headD false = false) :
    (Circuit.mk (pre ++ Gate.mk .and [] :: post) out).eval input =
      (Circuit.mk (pre ++ Gate.mk .not ins :: post) out).eval input := by
  change (run (pre ++ Gate.mk .and [] :: post) input).getD out false =
    (run (pre ++ Gate.mk .not ins :: post) input).getD out false
  simp only [run, List.foldl_append, List.foldl_cons]
  change (run post (run pre input ++ [true])).getD out false =
    (run post (run pre input ++
      [!(ins.map fun i => (run pre input).getD i false).headD false])).getD out false
  rw [hfalse]
  rfl

end PEqualNP.Outside.L_meta_1884.SafeNot

namespace PEqualNP.Outside.L_meta_1884.DirectFilter

open PEqualNP.CircuitLowerBounds
open SoleReader

def seed (x : Fin 10 → Bool) : List Bool := List.ofFn x ++ [!x 0]

def operand (pre : List Gate) (ins : List Nat) (x : Fin 10 → Bool) : Bool :=
  (ins.map fun i => (run pre (seed x)).getD i false).headD false

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (step w g)).length = _
    rw [ih]
    simp [step, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma operand_independent (pre : List Gate) (ins : List Nat) (t : Fin 10)
    (ht0 : t ≠ 0) (away : ∀ g ∈ pre, t.val ∉ g.inputs) (hi : t.val ∉ ins)
    (x y : Fin 10 → Bool) (off : ∀ i, i ≠ t → x i = y i) :
    operand pre ins x = operand pre ins y := by
  apply congrArg (fun bs : List Bool => bs.headD false)
  apply List.map_congr_left
  intro i his
  exact partner_independent pre _ _ (free_input_agree t ht0 x y off) away
    (fun he => hi (he ▸ his))

lemma operand_fiber_mono (pre : List Gate) (ins : List Nat)
    (allowed : ∀ g ∈ pre, g.op = .and ∨ g.op = .or)
    (x y : Fin 10 → Bool) (hzero : x 0 = y 0)
    (hxy : ∀ i, x i = true → y i = true) :
    operand pre ins x = true → operand pre ins y = true := by
  have hi : SafeNot.above (List.ofFn x) (List.ofFn y) := by
    refine ⟨by simp, ?_⟩
    intro i
    by_cases hlt : i < 10
    · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hlt, dite_true,
        Option.getD_some]
      exact Bool.le_iff_imp.mpr (hxy ⟨i, hlt⟩)
    · rw [List.getD_eq_default _ _ (by simp; omega),
        List.getD_eq_default _ _ (by simp; omega)]
  have hs : SafeNot.above (seed x) (seed y) :=
    SafeNot.append_above hi (by rw [hzero])
  have hr := SafeNot.run_above pre _ _ hs allowed
  cases ins with
  | nil => simp [operand]
  | cons i is => exact Bool.le_iff_imp.mp (hr.2 i)

lemma not_value (pre mid : List Gate) (ins : List Nat) (x : Fin 10 → Bool) :
    (run (pre ++ Gate.mk .not ins :: mid) (seed x)).getD (11 + pre.length) false =
      !operand pre ins x := by
  have hl : (run pre (seed x)).length = 11 + pre.length := by
    rw [run_length]; simp [seed]
  simp only [run, List.foldl_append, List.foldl_cons]
  change (run mid (run pre (seed x) ++ [!operand pre ins x])).getD
    (11 + pre.length) false = !operand pre ins x
  rw [run_input mid _ _ (by simp [hl])]
  rw [← hl]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append, lt_self_iff_false,
    if_false, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

lemma filter_boolean (a b h : Bool) (hh : (a || h) = (b || h)) :
    (a && !h) = (b && !h) := by
  cases h <;> simpa using hh

lemma factor (pre mid post : List Gate) (ins : List Nat) (t : Fin 10) (ht0 : t ≠ 0)
    (out : Nat) (f : (Fin 10 → Bool) → Bool)
    (hp : ∀ g ∈ pre, t.val ∉ g.inputs) (hi : t.val ∉ ins)
    (hm : ∀ g ∈ mid, t.val ∉ g.inputs) (hs : ∀ g ∈ post, t.val ∉ g.inputs)
    (ho : out ≠ t.val)
    (computes : ∀ x, (Circuit.mk
      ((pre ++ Gate.mk .not ins :: mid) ++ Gate.mk .and [t.val, 11 + pre.length] :: post)
      out).eval (seed x) = f x)
    (x y : Fin 10 → Bool) (off : ∀ i, i ≠ t → x i = y i)
    (hgate : (x t || operand pre ins x) = (y t || operand pre ins y)) : f x = f y := by
  have hH := operand_independent pre ins t ht0 hp hi x y off
  have he := free_factor_and (pre ++ Gate.mk .not ins :: mid) post t ht0
    (11 + pre.length) out x y off (by
      intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hp g hg
      · rcases List.mem_cons.mp hg with rfl | hg
        · exact hi
        · exact hm g hg) hs ho
  have hh : (x t && (run (pre ++ Gate.mk .not ins :: mid) (seed x)).getD
      (11 + pre.length) false) =
      (y t && (run (pre ++ Gate.mk .not ins :: mid) (seed y)).getD
        (11 + pre.length) false) := by
    rw [not_value, not_value, ← hH]
    rw [← hH] at hgate
    exact filter_boolean _ _ _ hgate
  exact (computes x).symm.trans ((he hh).trans (computes y))

end PEqualNP.Outside.L_meta_1884.DirectFilter
