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
