import SoleReaderFactor

namespace PEqualNP.Outside.L_meta_1884.SoleReader

open PEqualNP.CircuitLowerBounds

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
