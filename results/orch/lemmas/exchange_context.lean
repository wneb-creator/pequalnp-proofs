import PEqualNP.Defs.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1031_aux.ExchangeContext

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (w : List Bool) : List Bool :=
  Circuit.wires ⟨gs, 0⟩ w

lemma snoc_agree (bad : List ℕ) (xs ys : List Bool) (p q : Bool)
    (hlen : xs.length = ys.length)
    (hxy : ∀ i, i ∉ bad → xs.getD i false = ys.getD i false)
    (hpq : p = q) :
    ∀ i, i ∉ bad → (xs ++ [p]).getD i false = (ys ++ [q]).getD i false := by
  intro i hi
  by_cases hlt : i < xs.length
  · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
    exact hxy i hi
  · by_cases heq : i = xs.length
    · subst i
      simp [List.getD_eq_getElem?_getD, hlen, hpq]
    · rw [List.getD_eq_default, List.getD_eq_default] <;>
        simp only [List.length_append, List.length_singleton] <;> omega

lemma gate_agree (bad : List ℕ) (g : Gate) (xs ys : List Bool)
    (hread : ∀ i ∈ g.inputs, i ∉ bad)
    (hxy : ∀ i, i ∉ bad → xs.getD i false = ys.getD i false) :
    g.op.eval (g.inputs.map fun i => xs.getD i false) =
      g.op.eval (g.inputs.map fun i => ys.getD i false) := by
  congr 1
  apply List.map_congr_left
  intro i hi
  exact hxy i (hread i hi)

lemma run_agree (bad : List ℕ) (gs : List Gate)
    (hread : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ∉ bad)
    (xs ys : List Bool) (hlen : xs.length = ys.length)
    (hxy : ∀ i, i ∉ bad → xs.getD i false = ys.getD i false) :
    ∀ i, i ∉ bad → (run gs xs).getD i false = (run gs ys).getD i false := by
  induction gs generalizing xs ys with
  | nil => exact hxy
  | cons g gs ih =>
    have hg : ∀ i ∈ g.inputs, i ∉ bad := hread g (by simp)
    have hs : ∀ h ∈ gs, ∀ i ∈ h.inputs, i ∉ bad := by
      intro h hh
      exact hread h (by simp [hh])
    exact ih hs _ _ (by simp [hlen])
      (snoc_agree bad xs ys _ _ hlen hxy (gate_agree bad g xs ys hg hxy))

lemma run_append (as bs : List Gate) (w : List Bool) :
    run (as ++ bs) w = run bs (run as w) := by
  simp [run, Circuit.wires, List.foldl_append]

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).length = _
    rw [ih]
    simp
    omega

lemma getD_snoc_eq (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_twosnoc_first (w : List Bool) (p q : Bool) :
    ((w ++ [p]) ++ [q]).getD w.length false = p := by
  rw [List.getD_append _ _ _ _ (by simp), getD_snoc_eq]

lemma getD_twosnoc_last (w : List Bool) (p q : Bool) :
    ((w ++ [p]) ++ [q]).getD (w.length + 1) false = q := by
  have h : w.length + 1 = (w ++ [p]).length := by simp
  rw [h, getD_snoc_eq]

def before (n A B a d : ℕ) : List Gate :=
  [⟨GateOp.and, [A, B]⟩, ⟨GateOp.or, [a, d]⟩, ⟨GateOp.and, [n, n + 1]⟩]

def after (n A B a d : ℕ) : List Gate :=
  [⟨GateOp.and, [a, B]⟩, ⟨GateOp.and, [d, A]⟩, ⟨GateOp.or, [n, n + 1]⟩]

lemma run_before (w : List Bool) (A B a d : ℕ)
    (ha : a < w.length) (hd : d < w.length) :
    run (before w.length A B a d) w = w ++
      [w.getD A false && w.getD B false,
        w.getD a false || w.getD d false,
        (w.getD A false && w.getD B false) && (w.getD a false || w.getD d false)] := by
  simp only [before, run, Circuit.wires, List.foldl_cons, List.foldl_nil,
    List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
    List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
  rw [List.getD_append _ _ _ _ ha, List.getD_append _ _ _ _ hd]
  rw [getD_twosnoc_first, getD_twosnoc_last]
  simp [List.append_assoc]

lemma run_after (w : List Bool) (A B a d : ℕ)
    (hA : A < w.length) (hd : d < w.length) :
    run (after w.length A B a d) w = w ++
      [w.getD a false && w.getD B false,
        w.getD d false && w.getD A false,
        (w.getD a false && w.getD B false) || (w.getD d false && w.getD A false)] := by
  simp only [after, run, Circuit.wires, List.foldl_cons, List.foldl_nil,
    List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
    List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
  rw [List.getD_append _ _ _ _ hd, List.getD_append _ _ _ _ hA]
  rw [getD_twosnoc_first, getD_twosnoc_last]
  simp [List.append_assoc]

lemma three_agree (w : List Bool) (p q p' q' r : Bool) :
    ∀ i, i ≠ w.length → i ≠ w.length + 1 →
      (w ++ [p, q, r]).getD i false = (w ++ [p', q', r]).getD i false := by
  intro i hi hi'
  by_cases hlt : i < w.length
  · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hlt]
  · by_cases heq : i = w.length + 2
    · subst i
      simp [List.getD_eq_getElem?_getD]
    · rw [List.getD_eq_default, List.getD_eq_default] <;>
        simp only [List.length_append, List.length_cons, List.length_nil] <;> omega

lemma double_star (A B a d : Bool)
    (ha : a = true → A = true) (hd : d = true → B = true) :
    ((A && B) && (a || d)) = ((a && B) || (d && A)) := by
  cases A <;> cases B <;> cases a <;> cases d <;>
    first | rfl | exact Bool.noConfusion (ha rfl) | exact Bool.noConfusion (hd rfl)

lemma fragment_agree (w : List Bool) (A B a d : ℕ)
    (valid : ∀ i ∈ [A, B, a, d], i < w.length)
    (ha : w.getD a false = true → w.getD A false = true)
    (hd : w.getD d false = true → w.getD B false = true) :
    ∀ i, i ∉ [w.length, w.length + 1] →
      (run (before w.length A B a d) w).getD i false =
        (run (after w.length A B a d) w).getD i false := by
  intro i hi
  rw [run_before w A B a d (valid a (by simp)) (valid d (by simp)),
    run_after w A B a d (valid A (by simp)) (valid d (by simp)),
    double_star _ _ _ _ ha hd]
  apply three_agree
  · intro h
    exact hi (by simp [h])
  · intro h
    exact hi (by simp [h])

lemma exchange_suffix (w : List Bool) (A B a d : ℕ)
    (valid : ∀ i ∈ [A, B, a, d], i < w.length)
    (ha : w.getD a false = true → w.getD A false = true)
    (hd : w.getD d false = true → w.getD B false = true)
    (post : List Gate)
    (private_wires : ∀ g ∈ post, ∀ i ∈ g.inputs, i ∉ [w.length, w.length + 1])
    (o : ℕ) (ho : o ∉ [w.length, w.length + 1]) :
    (run post (run (before w.length A B a d) w)).getD o false =
      (run post (run (after w.length A B a d) w)).getD o false := by
  apply run_agree [w.length, w.length + 1] post private_wires _ _ _
    (fragment_agree w A B a d valid ha hd) o ho
  simp [run_length, before, after]

lemma exchange_context (pre post : List Gate) (x : List Bool) (A B a d o : ℕ)
    (valid : ∀ i ∈ [A, B, a, d], i < (run pre x).length)
    (ha : (run pre x).getD a false = true → (run pre x).getD A false = true)
    (hd : (run pre x).getD d false = true → (run pre x).getD B false = true)
    (private_wires : ∀ g ∈ post, ∀ i ∈ g.inputs,
      i ∉ [x.length + pre.length, x.length + pre.length + 1])
    (ho : o ∉ [x.length + pre.length, x.length + pre.length + 1]) :
    Circuit.eval ⟨(pre ++ before (x.length + pre.length) A B a d) ++ post, o⟩ x =
      Circuit.eval ⟨(pre ++ after (x.length + pre.length) A B a d) ++ post, o⟩ x := by
  change (run ((pre ++ before (x.length + pre.length) A B a d) ++ post) x).getD o false =
    (run ((pre ++ after (x.length + pre.length) A B a d) ++ post) x).getD o false
  rw [run_append, run_append, run_append, run_append]
  simpa only [run_length] using exchange_suffix (run pre x) A B a d valid ha hd post
    (by simpa only [run_length] using private_wires) o (by simpa only [run_length] using ho)

lemma exchange_size (pre post : List Gate) (n A B a d o : ℕ) :
    (Circuit.mk ((pre ++ before n A B a d) ++ post) o).size =
      (Circuit.mk ((pre ++ after n A B a d) ++ post) o).size := by
  simp [Circuit.size, before, after]

end PEqualNP.Outside.L_meta_1031_aux.ExchangeContext
