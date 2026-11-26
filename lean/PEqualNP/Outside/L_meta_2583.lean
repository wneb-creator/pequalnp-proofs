import Mathlib.Order.Preorder.Finite
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CircuitMoves

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def W (gs : List Gate) (w : List Bool) : List Bool := gs.foldl step w

lemma W_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    W (g :: gs) w = W gs (step w g) := rfl

lemma W_append (a b : List Gate) (w : List Bool) : W (a ++ b) w = W b (W a w) := by
  simp [W, List.foldl_append]

lemma W_split (gs : List Gate) (w : List Bool) (j : ℕ) :
    W gs w = W (gs.drop j) (W (gs.take j) w) := by
  rw [← W_append, List.take_append_drop]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma W_length (gs : List Gate) :
    ∀ w : List Bool, (W gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [W]
  | cons g gs ih =>
    intro w
    rw [W_cons, ih, step_len, List.length_cons]
    omega

lemma getD_app_lt (l l2 : List Bool) (i : ℕ) (h : i < l.length) :
    (l ++ l2).getD i false = l.getD i false := by
  simp [List.getD, List.getElem?_append_left h]

lemma getD_app_len (l : List Bool) (v : Bool) : (l ++ [v]).getD l.length false = v := by
  simp [List.getD]

lemma getD_ge (l : List Bool) (i : ℕ) (h : l.length ≤ i) : l.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (h : i < w.length) :
    (step w g).getD i false = w.getD i false := getD_app_lt w _ i h

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk; exact getD_app_len w _

lemma W_prefix (gs : List Gate) :
    ∀ (w : List Bool) (i : ℕ), i < w.length → (W gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    rw [W_cons, ih (step w g) i (by rw [step_len]; omega)]
    exact getD_app_lt w _ i hi

lemma W_ge (gs : List Gate) (w : List Bool) (i : ℕ) (h : w.length + gs.length ≤ i) :
    (W gs w).getD i false = false := getD_ge _ _ (by rw [W_length]; exact h)

lemma W_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (W gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (W gs w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [W_cons]
    cases j with
    | zero =>
      have h1 : w.length < (step w g).length := by simp [step]
      rw [Nat.add_zero, W_prefix gs (step w g) w.length h1]
      simp only [List.getElem_cons_zero]
      rw [step_last w g w.length rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [if_pos hi, W_prefix gs (step w g) i (by simp [step]; omega)]
        exact (step_lt w g i hi).symm
      · rw [if_neg hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (step w g) j hj'
      have hl : (step w g).length = w.length + 1 := step_len w g
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

lemma W_gate_pre (gs pre post : List Gate) (g : Gate) (w : List Bool)
    (h : gs = pre ++ g :: post) :
    (W gs w).getD (w.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => (W pre w).getD i false) := by
  subst h
  rw [W_append, W_cons, W_prefix _ _ _ (by rw [step_len, W_length]; omega)]
  exact step_last _ _ _ (by rw [W_length])

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := W_prefix _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := W_ge _ _ _ (by omega)

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact W_gate C.gates x j hj

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

def OpMono (R : Bool → Bool → Prop) : Prop :=
  ∀ (op : GateOp), (op = GateOp.and ∨ op = GateOp.or) → ∀ (l : List ℕ) (f g : ℕ → Bool),
    (∀ i ∈ l, R (f i) (g i)) → R (op.eval (l.map f)) (op.eval (l.map g))

lemma opMono_imp : OpMono (fun a b => a = true → b = true) := by
  intro op hop l f g h
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    intro h1 i hi; exact h i hi (h1 i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, h1⟩; exact ⟨i, hi, h i hi h1⟩

lemma mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · have e1 : val C (List.ofFn x) w = x ⟨w, hw⟩ := val_ofFn C x ⟨w, hw⟩
      have e2 : val C (List.ofFn y) w = y ⟨w, hw⟩ := val_ofFn C y ⟨w, hw⟩
      rw [e2]
      rw [e1] at hv
      exact hxy _ hv
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge (n := n) (by simp) hlen] at hv
        cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        rw [val_gate (n := n) (by simp) hk] at hv ⊢
        have h : ∀ i ∈ (gateAt C k).inputs,
            ((if i < n + k then val C (List.ofFn x) i else false) = true →
              (if i < n + k then val C (List.ofFn y) i else false) = true) := by
          intro i _
          by_cases hi : i < n + k
          · rw [if_pos hi, if_pos hi]
            exact ih i hi
          · rw [if_neg hi, if_neg hi]
            exact id
        exact opMono_imp (gateAt C k).op (hAO _ (gateAt_mem hk)) (gateAt C k).inputs
          (fun i => if i < n + k then val C (List.ofFn x) i else false)
          (fun i => if i < n + k then val C (List.ofFn y) i else false) h hv

lemma circuitFun_mono (n : ℕ) (C : Circuit) (hAO : PEqualNP.EdgeOwnership.AndOrOnly C)
    (x y : Fin n → Bool) (hxy : ∀ i : Fin n, x i = true → y i = true)
    (h : circuitFun n C x = true) : circuitFun n C y = true :=
  mono n C hAO x y hxy C.output h

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def erase_rg (r : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map r⟩

lemma erase_redirect_lt (n m p i : ℕ) (h : i < n + m) : eraseRedirect n m p i = i := by
  unfold eraseRedirect
  rw [if_neg (by omega), if_neg (by omega)]

lemma erase_redirect_self (n m p : ℕ) : eraseRedirect n m p (n + m) = p := by
  unfold eraseRedirect
  rw [if_pos rfl]

lemma erase_redirect_gt (n m p i : ℕ) (h : n + m < i) : eraseRedirect n m p i = i - 1 := by
  unfold eraseRedirect
  rw [if_neg (by omega), if_pos h]

lemma erase_snoc_eq (a : List Bool) (v : Bool) (i : ℕ) (h : i = a.length) :
    (a ++ [v]).getD i false = v := by
  subst h
  exact getD_app_len a v

lemma erase_snoc_gt (a : List Bool) (v : Bool) (i : ℕ) (h : a.length < i) :
    (a ++ [v]).getD i false = false :=
  getD_ge _ _ (by rw [List.length_append, List.length_singleton]; omega)

lemma erase_step_rel (rel : Bool → Bool → Prop) (h00 : rel false false) (n m p : ℕ)
    (hp : p < n + m) (a b : List Bool) (va vb : Bool) (hl : a.length = b.length + 1)
    (hn : n + m < a.length)
    (h : ∀ i, rel (a.getD i false) (b.getD (eraseRedirect n m p i) false)) (hv : rel va vb) :
    ∀ i, rel ((a ++ [va]).getD i false) ((b ++ [vb]).getD (eraseRedirect n m p i) false) := by
  intro i
  by_cases hi : i < a.length
  · have hri : eraseRedirect n m p i < b.length := by
      unfold eraseRedirect
      split_ifs <;> omega
    rw [getD_app_lt a [va] i hi, getD_app_lt b [vb] _ hri]
    exact h i
  · rw [erase_redirect_gt n m p i (by omega)]
    by_cases hi2 : i = a.length
    · rw [erase_snoc_eq a va i hi2, erase_snoc_eq b vb (i - 1) (by omega)]
      exact hv
    · rw [erase_snoc_gt a va i (by omega), erase_snoc_gt b vb (i - 1) (by omega)]
      exact h00

lemma erase_W_rel (Q : GateOp → Prop) (rel : Bool → Bool → Prop) (h00 : rel false false)
    (n m p : ℕ) (hp : p < n + m)
    (hop : ∀ (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool), Q op →
      (∀ i, rel (f i) (f' (eraseRedirect n m p i))) →
      rel (op.eval (l.map f)) (op.eval ((l.map (eraseRedirect n m p)).map f')))
    (gs : List Gate) : ∀ (a b : List Bool), (∀ g ∈ gs, Q g.op) →
      a.length = b.length + 1 → n + m < a.length →
      (∀ i, rel (a.getD i false) (b.getD (eraseRedirect n m p i) false)) →
      ∀ i, rel ((W gs a).getD i false)
        ((W (gs.map (erase_rg (eraseRedirect n m p))) b).getD (eraseRedirect n m p i) false) := by
  induction gs with
  | nil => intro a b _ _ _ h i; exact h i
  | cons g gs ih =>
    intro a b hg hl hn h i
    rw [List.map_cons, W_cons, W_cons]
    refine ih (step a g) (step b (erase_rg (eraseRedirect n m p) g)) ?_ ?_ ?_ ?_ i
    · intro g' hg'
      exact hg g' (List.mem_cons_of_mem _ hg')
    · rw [step_len, step_len, hl]
    · rw [step_len]
      omega
    · exact erase_step_rel rel h00 n m p hp a b
        (g.op.eval (g.inputs.map fun i => a.getD i false))
        (g.op.eval ((g.inputs.map (eraseRedirect n m p)).map fun i => b.getD i false))
        hl hn h
        (hop g.op g.inputs (fun i => a.getD i false) (fun i => b.getD i false)
          (hg g (by simp)) h)

lemma erase_sem (Q : GateOp → Prop) (rel : Bool → Bool → Prop) (hrefl : ∀ b, rel b b)
    (n m p : ℕ) (hp : p < n + m)
    (hop : ∀ (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool), Q op →
      (∀ i, rel (f i) (f' (eraseRedirect n m p i))) →
      rel (op.eval (l.map f)) (op.eval ((l.map (eraseRedirect n m p)).map f')))
    (pre post : List Gate) (gm : Gate) (x : List Bool) (hx : x.length = n)
    (hpre : pre.length = m)
    (hpost : ∀ g ∈ post, Q g.op)
    (hbase : rel (gm.op.eval (gm.inputs.map fun i => (W pre x).getD i false))
      ((W pre x).getD p false)) :
    ∀ i, rel ((W (pre ++ gm :: post) x).getD i false)
      ((W (pre ++ post.map (erase_rg (eraseRedirect n m p))) x).getD
        (eraseRedirect n m p i) false) := by
  have hA : (W pre x).length = n + m := by rw [W_length, hx, hpre]
  rw [W_append, W_append, W_cons]
  refine erase_W_rel Q rel (hrefl false) n m p hp hop post (step (W pre x) gm) (W pre x)
    hpost ?_ ?_ ?_
  · exact step_len _ _
  · rw [step_len, hA]
    omega
  · intro i
    show rel ((W pre x ++ [gm.op.eval (gm.inputs.map fun i => (W pre x).getD i false)]).getD i
      false) ((W pre x).getD (eraseRedirect n m p i) false)
    by_cases hi : i < n + m
    · rw [erase_redirect_lt n m p i hi, getD_app_lt (W pre x) _ i (by omega)]
      exact hrefl _
    · by_cases hi2 : i = n + m
      · rw [hi2, erase_redirect_self n m p, erase_snoc_eq (W pre x) _ (n + m) hA.symm]
        exact hbase
      · rw [erase_redirect_gt n m p i (by omega), erase_snoc_gt (W pre x) _ i (by omega),
          getD_ge (W pre x) (i - 1) (by omega)]
        exact hrefl false

lemma erase_eq (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    eraseGate n C m p = Circuit.mk
      (C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p)))
      (eraseRedirect n m p C.output) := if_pos hm

lemma erase_gates (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates
      = C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p)) :=
  congrArg Circuit.gates (erase_eq n C m p hm)

lemma erase_output (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).output = eraseRedirect n m p C.output :=
  congrArg Circuit.output (erase_eq n C m p hm)

lemma erase_length (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates.length + 1 = C.gates.length := by
  rw [erase_gates n C m p hm, List.length_append, List.length_take, List.length_map,
    List.length_drop]
  omega

lemma erase_size (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).size + 1 = C.size := by
  show (eraseGate n C m p).gates.length + 1 = C.gates.length
  exact erase_length n C m p hm

lemma erase_getD (l : List Gate) (f : Gate → Gate) (d : Gate) (m j : ℕ) (hm : m < l.length)
    (hj : j + 1 < l.length) :
    (l.take m ++ (l.drop (m + 1)).map f).getD j d
      = if j < m then l.getD j d else f (l.getD (j + 1) d) := by
  have hlt : (l.take m).length = m := by
    rw [List.length_take]
    omega
  by_cases h : j < m
  · rw [if_pos h, List.getD_append _ _ _ _ (by omega)]
    rw [List.getD_eq_getElem (l.take m) d (by omega), List.getD_eq_getElem l d (by omega),
      List.getElem_take]
  · rw [if_neg h, List.getD_append_right _ _ _ _ (by omega), hlt]
    have e : m + 1 + (j - m) = j + 1 := by omega
    rw [List.getD_eq_getElem (List.map f (l.drop (m + 1))) d
        (by rw [List.length_map, List.length_drop]; omega),
      List.getD_eq_getElem l d hj, List.getElem_map, List.getElem_drop]
    simp only [e]

lemma erase_gateAt (n : ℕ) (C : Circuit) (m p j : ℕ) (hm : m < C.gates.length)
    (hj : j + 1 < C.gates.length) :
    gateAt (eraseGate n C m p) j
      = if j < m then gateAt C j else erase_rg (eraseRedirect n m p) (gateAt C (j + 1)) := by
  have h0 : gateAt (eraseGate n C m p) j
      = (C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p))).getD j
        (Gate.mk GateOp.or []) :=
    congrArg (fun gs : List Gate => gs.getD j (Gate.mk GateOp.or [])) (erase_gates n C m p hm)
  rw [h0]
  exact erase_getD C.gates (erase_rg (eraseRedirect n m p)) (Gate.mk GateOp.or []) m j hm hj

lemma erase_andOrOnly (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (hA : PEqualNP.EdgeOwnership.AndOrOnly C) :
    PEqualNP.EdgeOwnership.AndOrOnly (eraseGate n C m p) := by
  intro g hg
  rw [erase_gates n C m p hm] at hg
  rcases List.mem_append.1 hg with h | h
  · exact hA g (List.mem_of_mem_take h)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
    exact hA g0 (List.mem_of_mem_drop hg0)

lemma erase_readsBack (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length)
    (hp : p < n + m) (hR : ReadsBack n C) : ReadsBack n (eraseGate n C m p) := by
  have hElen := erase_length n C m p hm
  intro j hj i hi
  rw [erase_gateAt n C m p j hm (by omega)] at hi
  by_cases hjm : j < m
  · rw [if_pos hjm] at hi
    exact hR j (by omega) i hi
  · rw [if_neg hjm] at hi
    have hi' : i ∈ (gateAt C (j + 1)).inputs.map (eraseRedirect n m p) := hi
    obtain ⟨i0, hi0, rfl⟩ := List.mem_map.1 hi'
    have h2 := hR (j + 1) (by omega) i0 hi0
    unfold eraseRedirect
    split_ifs <;> omega

lemma erase_val_rel (Q : GateOp → Prop) (rel : Bool → Bool → Prop) (hrefl : ∀ b, rel b b)
    {n : ℕ} {C : Circuit} {m p : ℕ} (hm : m < C.gates.length) (hp : p < n + m)
    (hop : ∀ (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool), Q op →
      (∀ i, rel (f i) (f' (eraseRedirect n m p i))) →
      rel (op.eval (l.map f)) (op.eval ((l.map (eraseRedirect n m p)).map f')))
    (hQ : ∀ g ∈ C.gates.drop (m + 1), Q g.op)
    {x : List Bool} (hx : x.length = n) (hv : rel (val C x (n + m)) (val C x p)) :
    ∀ i, rel (val C x i) (val (eraseGate n C m p) x (eraseRedirect n m p i)) := by
  have hsplit : C.gates.take m ++ gateAt C m :: C.gates.drop (m + 1) = C.gates := by
    rw [gateAt_eq hm, ← List.drop_eq_getElem_cons hm, List.take_append_drop]
  have hpre : (C.gates.take m).length = m := by
    rw [List.length_take]
    omega
  have hA : (W (C.gates.take m) x).length = n + m := by rw [W_length, hx, hpre]
  have e1 : val C x (n + m) = (gateAt C m).op.eval
      ((gateAt C m).inputs.map fun i => (W (C.gates.take m) x).getD i false) := by
    have h1 := W_gate_pre C.gates (C.gates.take m) (C.gates.drop (m + 1)) (gateAt C m) x
      hsplit.symm
    rw [hx, hpre] at h1
    exact h1
  have e2 : val C x p = (W (C.gates.take m) x).getD p false := by
    show (W C.gates x).getD p false = _
    rw [W_split C.gates x m]
    exact W_prefix _ _ _ (by omega)
  rw [e1, e2] at hv
  have key := erase_sem Q rel hrefl n m p hp hop (C.gates.take m) (C.gates.drop (m + 1))
    (gateAt C m) x hx hpre hQ hv
  have hW : ∀ i, val C x i
      = (W (C.gates.take m ++ gateAt C m :: C.gates.drop (m + 1)) x).getD i false :=
    fun i => congrArg (fun gs : List Gate => (W gs x).getD i false) hsplit.symm
  have hWD : ∀ i, val (eraseGate n C m p) x i
      = (W (C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p))) x).getD
        i false :=
    fun i => congrArg (fun gs : List Gate => (W gs x).getD i false) (erase_gates n C m p hm)
  intro i
  rw [hW i, hWD (eraseRedirect n m p i)]
  exact key i

lemma erase_isAO2 (n : ℕ) (C : Circuit) (g v : ℕ) (hg : g < C.gates.length) (hv : v < n + g)
    (hAO : PEqualNP.TopForm.IsAO2 n C) : PEqualNP.TopForm.IsAO2 n (eraseGate n C g v) := by
  refine ⟨erase_andOrOnly n C g v hg hAO.1, erase_readsBack n C g v hg hv hAO.2.1, ?_⟩
  intro gt hgt
  rw [erase_gates n C g v hg] at hgt
  rcases List.mem_append.1 hgt with h | h
  · exact hAO.2.2 _ (List.mem_of_mem_take h)
  · obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 h
    show (g0.inputs.map _).length = 2
    rw [List.length_map]
    exact hAO.2.2 g0 (List.mem_of_mem_drop hg0)

lemma eq_graphFun_of_boundary {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (D : Circuit) (hAO : PEqualNP.TopForm.IsAO2 n D)
    (hpos : ∀ u v : Fin n, G.Adj u v →
      circuitFun n D (PEqualNP.EdgeOwnership.pairInput u v) = true)
    (hneg : ∀ x : Fin n → Bool, Maximal (fun y => graphFun G ∅ y = false) x →
      circuitFun n D x = false) : circuitFun n D = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    by_contra hfalse
    have hFx : graphFun G ∅ x = false := Bool.eq_false_iff.mpr hfalse
    obtain ⟨y, hxy, hy⟩ := Finite.exists_le_maximal
      (p := fun y : Fin n → Bool => graphFun G ∅ y = false) (a := x) hFx
    have hytrue : circuitFun n D y = true := by
      apply circuitFun_mono n D hAO.1 x y ?_ hx
      intro i hi
      have hle := hxy i
      exact (Bool.le_iff_imp.mp hle) hi
    rw [hneg y hy] at hytrue
    contradiction
  · intro hx
    obtain ⟨u, v, huv, hxu, hxv⟩ : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
      simpa [graphFun] using hx
    apply circuitFun_mono n D hAO.1 (PEqualNP.EdgeOwnership.pairInput u v) x ?_ (hpos u v huv)
    intro i hi
    have hiuv : i = u ∨ i = v := by simpa [PEqualNP.EdgeOwnership.pairInput] using hi
    rcases hiuv with rfl | rfl
    · exact hxu
    · exact hxv

namespace Frontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma orStep_up {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') (hv : val C x w' = true) :
    val C x w = true := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (val_or hx hk hop).mpr ⟨_, hin, hlt, ih⟩

lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma orStep_le {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') : w' ≤ w := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact le_rfl
  | head hstep _ ih =>
    obtain ⟨k, _, rfl, _, _, hlt⟩ := hstep
    omega

lemma orStep_cone {n : ℕ} {C : Circuit} {w w' : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w') :
    ∀ k h', w = n + k → w' = n + h' → h' = k ∨ InCone n C h' k := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => intro k h' h1 h2; left; omega
  | @head a c hstep hrest ih =>
    intro k h' h1 h2
    obtain ⟨k0, hk0, e, _, hin, hlt⟩ := hstep
    have hk : k0 = k := by omega
    subst hk
    have hle := orStep_le hrest
    obtain ⟨k1, hk1⟩ : ∃ k1, c = n + k1 := ⟨c - n, by omega⟩
    subst hk1
    right
    rw [inCone_iff]
    exact ⟨hk0, k1, by omega, hin, ih k1 h' rfl h2⟩

lemma operand_cone {n : ℕ} {C : Circuit} {a p h : ℕ} (ha : a < C.gates.length)
    (hin : p ∈ (gateAt C a).inputs) (hp : p < n + a)
    (hr : Relation.ReflTransGen (OrStep n C) p (n + h)) : InCone n C h a := by
  have hle := orStep_le hr
  obtain ⟨k1, rfl⟩ : ∃ k1, p = n + k1 := ⟨p - n, by omega⟩
  rw [inCone_iff]
  exact ⟨ha, k1, by omega, hin, orStep_cone hr k1 h rfl rfl⟩

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (orStep n (gs.foldl (orStep n) []) g).getD k [] =
          (gs.foldl (orStep n) []).getD k [] := by
      intro k hk
      simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (orStep n) []).getD (w - n) []) := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (orStep n (gs.foldl (orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (orStep n (gs.foldl (orStep n) []) g).getD j [] = [] := by
        simp only [orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    OrReaches n C (n + k) g ↔ k < C.gates.length ∧ (g = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold OrReaches orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma reach_orReaches {n : ℕ} {C : Circuit} {w w2 : ℕ}
    (h : Relation.ReflTransGen (OrStep n C) w w2) :
    ∀ g, w2 = n + g → g < C.gates.length → OrReaches n C w g := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl =>
    intro g h1 hg
    subst h1
    exact (orReaches_iff n C g g).mpr ⟨hg, Or.inl rfl⟩
  | @head a c hstep hrest ih =>
    intro g h1 hg
    obtain ⟨k, hk, rfl, hop, hin, hlt⟩ := hstep
    exact (orReaches_iff n C k g).mpr ⟨hk, Or.inr ⟨hop, c, hin, hlt, ih g h1 hg⟩⟩

lemma orReaches_reach {n : ℕ} {C : Circuit} (g : ℕ) :
    ∀ w, OrReaches n C w g →
      Relation.ReflTransGen (OrStep n C) w (n + g) ∧ g < C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro h
    have hnw : n ≤ w := h.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp h
    rcases h3 with rfl | ⟨hop, i, hi, hlt, hr⟩
    · exact ⟨Relation.ReflTransGen.refl, hk⟩
    · obtain ⟨hr2, hg⟩ := ih i hlt hr
      exact ⟨Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hi, hlt⟩ hr2, hg⟩

lemma reach_mem_orIn {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p u.val) :
    u ∈ PEqualNP.TopForm.orIn n C p := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases Relation.ReflTransGen.cases_tail hr with h | ⟨c, hpc, hstep⟩
  · exact Or.inl h
  · obtain ⟨k, hk, rfl, hop, hin, _⟩ := hstep
    exact Or.inr ⟨k, hk, reach_orReaches hpc k rfl hk, hop, hin⟩

lemma topData {a : ℕ} (ha : a ∈ tops G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧ BelowF G C a := by
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha

lemma junkData {a : ℕ} (ha : a ∈ junk G C) :
    a < C.gates.length ∧ (gateAt C a).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C a x = true ∧ graphFun G ∅ x = false := by
  rcases Finset.mem_filter.mp ha with ⟨hr, hop, hal, hd⟩
  exact ⟨hal, hop, hd⟩

lemma binaryInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) :
    ∃ p q, (gateAt C a).inputs = [p, q] :=
  List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem ha))

lemma opndMem (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
  fin_cases b <;> simp [opnd, hpq]

lemma opndBound (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a :=
  hAO.2.1 a ha _ (opndMem hAO ha b)

lemma andValBoth (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔
      val C (List.ofFn x) (opnd C a 0) = true ∧
      val C (List.ofFn x) (opnd C a 1) = true := by
  rw [gateVal_eq_val, val_and (n := n) (by simp) ha hop]
  constructor
  · intro h
    exact ⟨(h _ (opndMem hAO ha 0)).2, (h _ (opndMem hAO ha 1)).2⟩
  · intro h i hi
    refine ⟨hAO.2.1 a ha i hi, ?_⟩
    obtain ⟨p, q, hpq⟩ := binaryInputs hAO ha
    rcases List.mem_cons.mp (hpq ▸ hi) with rfl | hq
    · simpa [opnd, hpq] using h.1
    · have e : i = q := List.mem_singleton.mp hq
      subst i
      simpa [opnd, hpq] using h.2

lemma operandReachCone (hAO : IsAO2 n C) {a h : ℕ} (ha : a < C.gates.length)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h) :
    InCone n C h a :=
  operand_cone ha (opndMem hAO ha b) (opndBound hAO ha b)
    (orReaches_reach h _ hr).1

lemma operandOrAndJunk (hAO : IsAO2 n C) (hT : TopForm G C) {a h : ℕ}
    (ha : a < C.gates.length) (hop : (gateAt C a).op = GateOp.and)
    {b : Fin 2} (hr : OrReaches n C (opnd C a b) h)
    (hh : (gateAt C h).op = GateOp.and) : h ∈ junk G C := by
  have hlen := (orReaches_reach h _ hr).2
  have hnb : ¬ BelowF G C h :=
    fun hb => hT h hlen a ha hh hb hop (operandReachCone hAO ha hr)
  have hdirty : ∃ x : Fin n → Bool, gateVal n C h x = true ∧ graphFun G ∅ x = false := by
    by_contra hne
    apply hnb
    intro x hx
    by_contra hf
    exact hne ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlen, hh, hlen, hdirty⟩

lemma graphFun_pair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq, pairInput_true]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, Or.inl rfl, Or.inr rfl⟩

lemma pairInput_right {n : ℕ} (u v : Fin n) : pairInput u v v = true := by
  simp [pairInput]


lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩


lemma sideVal {a : ℕ} {b : Fin 2} {x : Fin n → Bool} {t : Fin n}
    (ht : t ∈ side (n := n) C a b) (hx : x t = true) :
    val C (List.ofFn x) (opnd C a b) = true :=
  reach_var_val x _ t (mem_orIn_reach t ht) hx

lemma andFromInputs (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) {x : Fin n → Bool}
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1)
    (xu : x u = true) (xv : x v = true) : gateVal n C a x = true :=
  (andValBoth hAO ha hop x).mpr ⟨sideVal hu xu, sideVal hv xv⟩

lemma topAdj (hAO : IsAO2 n C) {a : ℕ} (ha : a ∈ tops G C)
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) :
    G.Adj u v := by
  obtain ⟨hl, ho, hb⟩ := topData ha
  exact (graphFun_pair G u v).mp
    (hb _ (andFromInputs hAO hl ho hu hv (pairInput_left u v) (pairInput_right u v)))

end Frontier


namespace Repair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gate_op {C : Circuit} (hm : Monotone2 C) {k : ℕ} (hk : k < C.gates.length) :
    (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
  simpa using (hm _ (gateAt_mem hk)).1

lemma pair_mono {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {x y : Fin n → Bool} (hxy : ∀ u, x u = true → y u = true) :
    ∀ w, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hinput : w < n
    · let u : Fin n := ⟨w, hinput⟩
      change val C (List.ofFn x) u.val = true at hw
      change val C (List.ofFn y) u.val = true
      rw [val_ofFn] at *
      exact hxy u hw
    · have hwlt : w < n + C.gates.length := by
        by_contra! h
        rw [val_ge (by simp : (List.ofFn x).length = n) h] at hw
        cases hw
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      rcases gate_op hm hk with hop | hop
      · apply (val_and (by simp) hk hop).2
        intro i hi
        obtain ⟨hlt, ht⟩ := (val_and (by simp) hk hop).1 hw i hi
        exact ⟨hlt, ih i hlt ht⟩
      · obtain ⟨i, hi, hlt, ht⟩ := (val_or (by simp) hk hop).1 hw
        exact (val_or (by simp) hk hop).2 ⟨i, hi, hlt, ih i hlt ht⟩

def edgeTrue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

lemma graph_true {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x : Fin n → Bool} : graphFun G ∅ x = true ↔ edgeTrue G x := by
  simp [graphFun, edgeTrue]

def dirty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) : Prop :=
  (gateAt C j).op = GateOp.and ∧ ¬ BelowF G C j

end Repair

namespace Labeling

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma junk_is_dirty {j : ℕ} (hj : j ∈ junk G C) : Repair.dirty G C j := by
  obtain ⟨_, hop, x, hx, hFx⟩ := Frontier.junkData hj
  refine ⟨hop, ?_⟩
  intro hbelow
  have h := hbelow x hx
  rw [hFx] at h
  cases h

end Labeling

namespace Duplicate

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CircuitMoves PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma erase_equal_wires {n : ℕ} {C : Circuit} {k p : ℕ}
    (hk : k < C.gates.length) (hp : p < n + k) {x : Fin n → Bool}
    (heq : val C (List.ofFn x) p = val C (List.ofFn x) (n + k)) (w : ℕ) :
    val (eraseGate n C k p) (List.ofFn x) (eraseRedirect n k p w) = val C (List.ofFn x) w := by
  apply Eq.symm
  apply erase_val_rel (fun _ => True) (@Eq Bool) (fun _ => rfl) hk hp ?_
    (fun _ _ => trivial) (by simp) heq.symm w
  intro op l f f' _ h
  rw [List.map_map]
  congr 1
  exact List.map_congr_left (fun i _ => h i)

lemma erase_lower_value {n : ℕ} {C : Circuit} {m p : ℕ} (hm : m < C.gates.length)
    {x : List Bool} (hx : x.length = n) {i : ℕ} (hi : i < n + m) :
    val (eraseGate n C m p) x i = val C x i := by
  have hpre : (C.gates.take m).length = m := by
    rw [List.length_take]
    omega
  have hA : (W (C.gates.take m) x).length = n + m := by rw [W_length, hx, hpre]
  have e1 : val (eraseGate n C m p) x i
      = (W (C.gates.take m ++ (C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p))) x).getD
        i false :=
    congrArg (fun gs : List Gate => (W gs x).getD i false) (erase_gates n C m p hm)
  have e2 : val C x i = (W (C.gates.take m ++ C.gates.drop m) x).getD i false :=
    congrArg (fun gs : List Gate => (W gs x).getD i false) (List.take_append_drop m C.gates).symm
  rw [e1, e2, W_append, W_append,
    W_prefix ((C.gates.drop (m + 1)).map (erase_rg (eraseRedirect n m p)))
      (W (C.gates.take m) x) i (by omega),
    W_prefix (C.gates.drop m) (W (C.gates.take m) x) i (by omega)]

lemma minimum_label_representatives {α : Type*} [DecidableEq α]
    (T : Finset ℕ) (f : ℕ → α) :
    ∃ R : Finset ℕ, R ⊆ T ∧ R.card = (T.image f).card ∧
      ∀ k ∈ T \ R, ∃ j ∈ T, j < k ∧ f j = f k := by
  classical
  let R := T.filter fun k => ∀ j ∈ T, f j = f k → k ≤ j
  have hRT : R ⊆ T := Finset.filter_subset _ _
  have hinj : Set.InjOn f (R : Set ℕ) := by
    intro j hj k hk heq
    have hj' := Finset.mem_filter.mp hj
    have hk' := Finset.mem_filter.mp hk
    exact Nat.le_antisymm (hj'.2 k hk'.1 heq.symm) (hk'.2 j hj'.1 heq)
  have himage : R.image f = T.image f := by
    apply Finset.Subset.antisymm (Finset.image_subset_image hRT)
    intro z hz
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hz
    let F := T.filter fun j => f j = f k
    have hF : F.Nonempty := ⟨k, Finset.mem_filter.mpr ⟨hk, rfl⟩⟩
    let j := F.min' hF
    have hj : j ∈ F := F.min'_mem hF
    have hjT : j ∈ T := (Finset.mem_filter.mp hj).1
    have hjeq : f j = f k := (Finset.mem_filter.mp hj).2
    have hjR : j ∈ R := by
      apply Finset.mem_filter.mpr
      refine ⟨hjT, ?_⟩
      intro l hl heq
      exact Finset.min'_le F l (Finset.mem_filter.mpr ⟨hl, heq.trans hjeq⟩)
    exact Finset.mem_image.mpr ⟨j, hjR, hjeq⟩
  refine ⟨R, hRT, ?_, ?_⟩
  · calc
      R.card = (R.image f).card := (Finset.card_image_of_injOn hinj).symm
      _ = (T.image f).card := congrArg Finset.card himage
  · intro k hk
    obtain ⟨hkT, hkR⟩ := Finset.mem_sdiff.mp hk
    by_contra hno
    apply hkR
    apply Finset.mem_filter.mpr
    refine ⟨hkT, ?_⟩
    intro j hj heq
    by_contra hle
    exact hno ⟨j, hj, by omega, heq⟩

end Duplicate


namespace Completion
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma ao2_all_true {n : ℕ} (C : Circuit) (hAO : IsAO2 n C) :
    ∀ w < n + C.gates.length, val C (List.ofFn (fun _ : Fin n => true)) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hinput : w < n
    · exact val_ofFn C (fun _ : Fin n => true) ⟨w, hinput⟩
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w-n, by omega⟩
      have hj : j < C.gates.length := by omega
      obtain ⟨p, q, hpq⟩ := Frontier.binaryInputs hAO hj
      have hp : p < n + j := hAO.2.1 j hj p (by simp [hpq])
      have hq : q < n + j := hAO.2.1 j hj q (by simp [hpq])
      have hvp := ih p hp (by omega)
      have hvq := ih q hq (by omega)
      rw [val_gate (by simp) hj, hpq]
      rcases hAO.1 _ (gateAt_mem hj) with hop | hop <;>
        simp only [hop, List.map_cons, List.map_nil, ite_eq_left hp, ite_eq_left hq, hvp, hvq] <;> rfl

lemma output_valid_of_true {n : ℕ} (C : Circuit) (x : Fin n → Bool)
    (hx : circuitFun n C x = true) : C.output < n + C.gates.length := by
  by_contra! h
  have hv := val_ge (C := C) (x := List.ofFn x) (by simp) h
  change circuitFun n C x = false at hv
  rw [hv] at hx
  cases hx

end Completion


namespace StarCompletion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

def appendBinary (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op, [a, b]⟩], n + C.gates.length⟩

lemma appendBinary_size (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    (appendBinary n C op a b).size = C.size + 1 := by simp [appendBinary, Circuit.size]

lemma appendBinary_gate_old (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ)
    {j : ℕ} (hj : j < C.gates.length) : gateAt (appendBinary n C op a b) j = gateAt C j := by
  simp [gateAt, appendBinary, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

lemma appendBinary_gate_new (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    gateAt (appendBinary n C op a b) C.gates.length = ⟨op, [a, b]⟩ := by
  simp [gateAt, appendBinary, List.getD_eq_getElem?_getD]

lemma appendBinary_ao (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ)
    (hAO : IsAO2 n C) (hop : op = GateOp.and ∨ op = GateOp.or)
    (ha : a < n + C.gates.length) (hb : b < n + C.gates.length) :
    IsAO2 n (appendBinary n C op a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [appendBinary, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO.1 g hg
    · exact hop
  · intro j hj i hi
    have hj' : j < C.gates.length + 1 := by simpa [appendBinary] using hj
    by_cases hlt : j < C.gates.length
    · rw [appendBinary_gate_old n C op a b hlt] at hi
      exact hAO.2.1 j hlt i hi
    · have heq : j = C.gates.length := by omega
      subst j
      rw [appendBinary_gate_new] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · exact ha
      · exact hb
  · intro g hg
    simp only [appendBinary, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO.2.2 g hg
    · rfl

lemma appendBinary_val_old {n : ℕ} (C : Circuit) (op : GateOp) (a b : ℕ)
    (x : Fin n → Bool) {i : ℕ} (hi : i < n + C.gates.length) :
    val (appendBinary n C op a b) (List.ofFn x) i = val C (List.ofFn x) i := by
  change (W (C.gates ++ _) (List.ofFn x)).getD i false = _
  rw [W_append, W_prefix]
  · rfl
  · simpa [W_length] using hi

lemma appendBinary_fun {n : ℕ} (C : Circuit) (op : GateOp) (a b : ℕ)
    (ha : a < n + C.gates.length) (hb : b < n + C.gates.length) (x : Fin n → Bool) :
    circuitFun n (appendBinary n C op a b) x =
      op.eval [val C (List.ofFn x) a, val C (List.ofFn x) b] := by
  have hj : C.gates.length < (appendBinary n C op a b).gates.length := by simp [appendBinary]
  change val (appendBinary n C op a b) (List.ofFn x) (n + C.gates.length) = _
  rw [val_gate (by simp) hj, appendBinary_gate_new]
  simp only [List.map_cons, List.map_nil, ite_eq_left ha, ite_eq_left hb]
  rw [appendBinary_val_old C op a b x ha, appendBinary_val_old C op a b x hb]

lemma appendBinary_clean {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (op : GateOp) (a b : ℕ)
    (ha : a < n + C.gates.length) (hb : b < n + C.gates.length)
    (hc : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j)
    (hnew : op = GateOp.and → ∀ x : Fin n → Bool,
      op.eval [val C (List.ofFn x) a, val C (List.ofFn x) b] = true → graphFun G ∅ x = true) :
    ∀ j < (appendBinary n C op a b).gates.length,
      (gateAt (appendBinary n C op a b) j).op = GateOp.and → BelowF G (appendBinary n C op a b) j := by
  intro j hj hop x hx
  have hj' : j < C.gates.length + 1 := by simpa [appendBinary] using hj
  by_cases hlt : j < C.gates.length
  · rw [appendBinary_gate_old n C op a b hlt] at hop
    apply hc j hlt hop x
    change val C (List.ofFn x) (n + j) = true
    change val (appendBinary n C op a b) (List.ofFn x) (n + j) = true at hx
    rwa [appendBinary_val_old C op a b x (by omega)] at hx
  · have heq : j = C.gates.length := by omega
    subst j
    rw [appendBinary_gate_new] at hop
    apply hnew hop x
    rw [← appendBinary_fun C op a b ha hb]
    exact hx

end StarCompletion


namespace SharedRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CircuitMoves PEqualNP.CleanedNonEdge

def shiftWire (n m w : ℕ) : ℕ := if w < n then w else w + m

lemma shift_input (n m w : ℕ) (hw : w < n) : shiftWire n m w = w := by simp [shiftWire, hw]

lemma shift_gate (n m j : ℕ) : shiftWire n m (n + j) = n + (m + j) := by
  simp [shiftWire]
  omega

lemma shift_bound {n m w j : ℕ} (hw : w < n + j) : shiftWire n m w < n + (m + j) := by
  unfold shiftWire
  split_ifs <;> omega

noncomputable def patchedGate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (j : ℕ) : Gate := by
  classical
  exact if Repair.dirty G C j then ⟨GateOp.and, [B.output, B.output]⟩
    else ⟨(gateAt C j).op, (gateAt C j).inputs.map (shiftWire n B.gates.length)⟩

noncomputable def shared {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) : Circuit :=
  ⟨B.gates ++ (List.range C.gates.length).map (patchedGate G B C),
    shiftWire n B.gates.length C.output⟩

lemma shared_length {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (B C : Circuit) :
    (shared G B C).gates.length = B.gates.length + C.gates.length := by simp [shared]

lemma shared_size {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (B C : Circuit) :
    (shared G B C).size = B.size + C.size := shared_length G B C

lemma shared_gate_prefix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) {j : ℕ} (hj : j < B.gates.length) :
    gateAt (shared G B C) j = gateAt B j := by
  simp [gateAt, shared, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

lemma shared_gate_old {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    gateAt (shared G B C) (B.gates.length + j) = patchedGate G B C j := by
  simp only [gateAt, shared, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega)]
  simp [hj]

lemma shared_ao {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C)
    (hBo : B.output < n + B.gates.length) : IsAO2 n (shared G B C) := by
  classical
  have hgate (j : ℕ) (hj : j < (shared G B C).gates.length) :
      ((gateAt (shared G B C) j).op = GateOp.and ∨ (gateAt (shared G B C) j).op = GateOp.or) ∧
      (gateAt (shared G B C) j).inputs.length = 2 ∧
      ∀ w ∈ (gateAt (shared G B C) j).inputs, w < n + j := by
    rw [shared_length] at hj
    by_cases hjB : j < B.gates.length
    · rw [shared_gate_prefix G B C hjB]
      exact ⟨hB.1 _ (gateAt_mem hjB), hB.2.2 _ (gateAt_mem hjB), hB.2.1 j hjB⟩
    · obtain ⟨k, rfl⟩ : ∃ k, j = B.gates.length + k := ⟨j - B.gates.length, by omega⟩
      have hk : k < C.gates.length := by omega
      rw [shared_gate_old G B C hk]
      unfold patchedGate
      split_ifs with hd
      · refine ⟨Or.inl rfl, rfl, ?_⟩
        intro w hw
        have hw' : w = B.output := by simpa using hw
        subst w
        omega
      · refine ⟨hC.1 (gateAt C k) (gateAt_mem hk), ?_, ?_⟩
        · simpa using hC.2.2 _ (gateAt_mem hk)
        · intro w hw
          obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
          exact shift_bound (hC.2.1 k hk i hi)
  refine ⟨?_, fun j hj => (hgate j hj).2.2, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    rw [← gateAt_eq hj]
    exact (hgate j hj).1
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    rw [← gateAt_eq hj]
    exact (hgate j hj).2.1

lemma shared_output_valid {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (ho : C.output < n + C.gates.length) :
    (shared G B C).output < n + (shared G B C).gates.length := by
  rw [shared_length]
  exact shift_bound ho

lemma prefix_value {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : w < n + B.gates.length) :
    val (shared G B C) (List.ofFn x) w = val B (List.ofFn x) w := by
  change (W (B.gates ++ _) (List.ofFn x)).getD w false = _
  rw [W_append, W_prefix]
  · rfl
  · simpa [W_length] using hw

lemma copied_value {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hBo : B.output < n + B.gates.length)
    {j : ℕ} (hj : j < C.gates.length) (hd : Repair.dirty G C j) (x : Fin n → Bool) :
    val (shared G B C) (List.ofFn x) (n + (B.gates.length + j)) = circuitFun n B x := by
  classical
  have hj' : B.gates.length + j < (shared G B C).gates.length := by rw [shared_length]; omega
  have hb : B.output < n + (B.gates.length + j) := by omega
  rw [val_gate (by simp) hj', shared_gate_old G B C hj]
  simp only [patchedGate, ite_eq_left hd, List.map_cons, List.map_nil, ite_eq_left hb,
    GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, Bool.and_self]
  exact prefix_value G B C x hBo

lemma kept_value {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hC : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hd : ¬ Repair.dirty G C j) (x : Fin n → Bool) :
    val (shared G B C) (List.ofFn x) (n + (B.gates.length + j)) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun w =>
        val (shared G B C) (List.ofFn x) (shiftWire n B.gates.length w)) := by
  classical
  have hj' : B.gates.length + j < (shared G B C).gates.length := by rw [shared_length]; omega
  rw [val_gate (by simp) hj', shared_gate_old G B C hj]
  simp only [patchedGate, ite_eq_right hd, List.map_map, Function.comp_def]
  congr 1
  apply List.map_congr_left
  intro w hw
  rw [ite_eq_left (shift_bound (hC.2.1 j hj w hw))]

lemma old_value {n : ℕ} (C : Circuit) (hC : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (x : Fin n → Bool) :
    val C (List.ofFn x) (n + j) =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun w => val C (List.ofFn x) w) := by
  rw [val_gate (by simp) hj]
  congr 1
  apply List.map_congr_left
  intro w hw
  rw [ite_eq_left (hC.2.1 j hj w hw)]

lemma shared_compare {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hC : IsAO2 n C) (rel : Bool → Bool → Prop)
    (hrefl : ∀ b, rel b b) (hmono : OpMono rel) (x : Fin n → Bool)
    (hcopy : ∀ j < C.gates.length, Repair.dirty G C j →
      rel (val C (List.ofFn x) (n + j))
        (val (shared G B C) (List.ofFn x) (n + (B.gates.length + j)))) :
    ∀ w : ℕ, rel (val C (List.ofFn x) w)
      (val (shared G B C) (List.ofFn x) (shiftWire n B.gates.length w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hw : w < n
    · rw [shift_input n B.gates.length w hw, val_input (n := n) (by simp) hw,
        val_input (n := n) (by simp) hw]
      exact hrefl _
    by_cases hge : n + C.gates.length ≤ w
    · have hnew : n + (shared G B C).gates.length ≤ shiftWire n B.gates.length w := by
        rw [shared_length]
        unfold shiftWire
        rw [ite_eq_right hw]
        omega
      rw [val_ge (n := n) (by simp) hge, val_ge (n := n) (by simp) hnew]
      exact hrefl false
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    rw [shift_gate]
    by_cases hd : Repair.dirty G C j
    · exact hcopy j hj hd
    rw [old_value C hC hj x, kept_value G B C hC hj hd x]
    apply hmono (gateAt C j).op (hC.1 _ (gateAt_mem hj)) (gateAt C j).inputs
    intro i hi
    exact ih i (hC.2.1 j hj i hi)

lemma opMono_reverse : OpMono (fun a b => b = true → a = true) := by
  intro op hop l f g h
  exact opMono_imp op hop l g f (fun i hi => h i hi)

lemma shared_reflect_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hC : IsAO2 n C) (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (x : Fin n → Bool) (hFx : graphFun G ∅ x = false) :
    ∀ w, val (shared G B C) (List.ofFn x) (shiftWire n B.gates.length w) = true →
      val C (List.ofFn x) w = true := by
  apply shared_compare G B C hC (fun a b => b = true → a = true)
    (fun _ h => h) opMono_reverse x
  intro j hj hd hcopy
  rw [copied_value G B C hBo hj hd x] at hcopy
  have h := hBsafe x hcopy
  rw [hFx] at h
  cases h

lemma shared_forward_of_B_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hC : IsAO2 n C) (hBo : B.output < n + B.gates.length)
    (x : Fin n → Bool) (hBx : circuitFun n B x = true) :
    circuitFun n C x = true → circuitFun n (shared G B C) x = true := by
  apply shared_compare G B C hC (fun a b => a = true → b = true)
    (fun _ h => h) opMono_imp x ?_ C.output
  intro j hj hd _
  rw [copied_value G B C hBo hj hd x]
  exact hBx

lemma shared_safe_clean {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C)
    (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hCsafe : ∀ x, circuitFun n C x = true → graphFun G ∅ x = true)
    (hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j) :
    IsAO2 n (shared G B C) ∧ (shared G B C).size = B.size + C.size ∧
      (∀ x, circuitFun n (shared G B C) x = true → graphFun G ∅ x = true) ∧
      (∀ j < (shared G B C).gates.length,
        (gateAt (shared G B C) j).op = GateOp.and → BelowF G (shared G B C) j) := by
  classical
  refine ⟨shared_ao G B C hB hC hBo, shared_size G B C, ?_, ?_⟩
  · intro x hx
    by_contra hn
    have h := shared_reflect_false G B C hC hBo hBsafe x (Bool.eq_false_iff.mpr hn) C.output hx
    exact hn (hCsafe x h)
  · intro k hk hop x hx
    rw [shared_length] at hk
    by_cases hkB : k < B.gates.length
    · rw [shared_gate_prefix G B C hkB] at hop
      apply hBclean k hkB hop x
      change val (shared G B C) (List.ofFn x) (n + k) = true at hx
      rwa [prefix_value G B C x (by omega)] at hx
    · obtain ⟨j, rfl⟩ : ∃ j, k = B.gates.length + j := ⟨k - B.gates.length, by omega⟩
      have hj : j < C.gates.length := by omega
      by_cases hd : Repair.dirty G C j
      · change val (shared G B C) (List.ofFn x) (n + (B.gates.length + j)) = true at hx
        rw [copied_value G B C hBo hj hd x] at hx
        exact hBsafe x hx
      · have hop' : (gateAt C j).op = GateOp.and := by
          rw [shared_gate_old G B C hj] at hop
          simpa only [patchedGate, ite_eq_right hd] using hop
        have hbelow : BelowF G C j := by
          by_contra hn
          exact hd ⟨hop', hn⟩
        by_contra hn
        have href := shared_reflect_false G B C hC hBo hBsafe x (Bool.eq_false_iff.mpr hn) (n + j)
        rw [shift_gate] at href
        exact hn (hbelow x (href hx))

lemma shifted_or_path_value {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) {w w' : ℕ}
    (hr : Relation.ReflTransGen (Frontier.OrStep n C) w w')
    (hv : val (shared G B C) (List.ofFn x) (shiftWire n B.gates.length w') = true) :
    val (shared G B C) (List.ofFn x) (shiftWire n B.gates.length w) = true := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact hv
  | head hstep _ ih =>
    obtain ⟨j, hj, rfl, hop, hin, _⟩ := hstep
    have hd : ¬ Repair.dirty G C j := fun h => by cases hop.symm.trans h.1
    rw [shift_gate, kept_value G B C hC hj hd x, hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    exact ⟨_, hin, ih⟩

lemma shifted_raw_side_value {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) {a : ℕ} {b : Fin 2}
    {t : Fin n} (ht : t ∈ side (n := n) C a b) (hxt : x t = true) :
    val (shared G B C) (List.ofFn x) (shiftWire n B.gates.length (opnd C a b)) = true := by
  apply shifted_or_path_value G B C hC x (Frontier.mem_orIn_reach t ht)
  rw [shift_input n B.gates.length t.val t.isLt, val_ofFn]
  exact hxt

lemma shared_accepts_raw_top {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) {a : ℕ}
    (ha : a ∈ tops G C) (hr : OrReaches n C C.output a)
    {u v : Fin n} (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1)
    (hxu : x u = true) (hxv : x v = true) : circuitFun n (shared G B C) x = true := by
  obtain ⟨haLen, haOp, haBelow⟩ := Frontier.topData ha
  have hd : ¬ Repair.dirty G C a := fun h => h.2 haBelow
  have hLeft := shifted_raw_side_value G B C hC x hu hxu
  have hRight := shifted_raw_side_value G B C hC x hv hxv
  obtain ⟨p, q, hpq⟩ := Frontier.binaryInputs hC haLen
  have he0 : opnd C a 0 = p := by simp [opnd, hpq]
  have he1 : opnd C a 1 = q := by simp [opnd, hpq]
  rw [he0] at hLeft
  rw [he1] at hRight
  apply shifted_or_path_value G B C hC x (Frontier.orReaches_reach a C.output hr).1
  rw [shift_gate, kept_value G B C hC haLen hd x, haOp, hpq]
  simp [GateOp.eval, hLeft, hRight]

end SharedRepair

namespace SharedRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge PEqualNP.CircuitMoves

lemma shared_or_trace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hC : IsAO2 n C) (x : Fin n → Bool) :
    ∀ w, val (shared G B C) (List.ofFn x) (shiftWire n B.gates.length w) = true →
      (∃ t ∈ orIn n C w, x t = true) ∨
      ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ OrReaches n C w j ∧
        val (shared G B C) (List.ofFn x) (n + (B.gates.length + j)) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · rw [shift_input n B.gates.length w hw] at hv
      refine Or.inl ⟨⟨w, hw⟩, Frontier.reach_mem_orIn _ Relation.ReflTransGen.refl, ?_⟩
      exact (val_ofFn (shared G B C) x ⟨w, hw⟩).symm.trans hv
    · by_cases hge : n + C.gates.length ≤ w
      · have hg : n + (shared G B C).gates.length ≤ shiftWire n B.gates.length w := by
          rw [shared_length]
          simp only [shiftWire, ite_eq_right hw]
          omega
        rw [val_ge (n := n) (by simp) hg] at hv
        cases hv
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < C.gates.length := by omega
        rw [shift_gate] at hv
        rcases hC.1 _ (gateAt_mem hj) with hand | hor
        · refine Or.inr ⟨j, hj, hand, ?_, hv⟩
          exact (Frontier.orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩
        · have hd : ¬ Repair.dirty G C j := fun h => by cases hor.symm.trans h.1
          rw [kept_value G B C hC hj hd x, hor] at hv
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hv
          obtain ⟨v, hin, hv⟩ := hv
          have hlt := hC.2.1 j hj v hin
          rcases ih v hlt hv with ⟨t, ht, hxt⟩ | ⟨g, hg, hga, hvg, hgv⟩
          · apply Or.inl
            refine ⟨t, ?_, hxt⟩
            apply Frontier.reach_mem_orIn
            exact Relation.ReflTransGen.head ⟨j, hj, rfl, hor, hin, hlt⟩
              (Frontier.mem_orIn_reach t ht)
          · apply Or.inr
            refine ⟨g, hg, hga, ?_, hgv⟩
            exact (Frontier.orReaches_iff n C j g).mpr ⟨hj, Or.inr ⟨hor, v, hin, hlt, hvg⟩⟩

lemma shared_operand_raw_when_B_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hC : IsAO2 n C) (hT : TopForm G C)
    (hBo : B.output < n + B.gates.length) {a : ℕ} (ha : a ∈ tops G C)
    (b : Fin 2) (x : Fin n → Bool) (hBx : circuitFun n B x = false)
    (hv : val (shared G B C) (List.ofFn x)
      (shiftWire n B.gates.length (opnd C a b)) = true) :
    ∃ t ∈ side (n := n) C a b, x t = true := by
  rcases shared_or_trace G B C hC x _ hv with hraw | ⟨j, hj, hand, hr, hvj⟩
  · exact hraw
  · have hd := Frontier.operandOrAndJunk hC hT (Frontier.topData ha).1
      (Frontier.topData ha).2.1 hr hand
    rw [copied_value G B C hBo hj (Labeling.junk_is_dirty hd) x, hBx] at hvj
    cases hvj

lemma shared_top_dominated_by_B {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C) (hT : TopForm G C)
    (hBo : B.output < n + B.gates.length) {a : ℕ} (ha : a ∈ tops G C)
    (hcover : ∀ u ∈ side (n := n) C a 0, ∀ v ∈ side (n := n) C a 1,
      circuitFun n B (pairInput u v) = true) :
    ∀ x : Fin n → Bool,
      val (shared G B C) (List.ofFn x) (n + (B.gates.length + a)) = true →
        circuitFun n B x = true := by
  intro x hx
  by_contra hn
  have hBx : circuitFun n B x = false := Bool.eq_false_iff.mpr hn
  obtain ⟨haLen, haOp, haBelow⟩ := Frontier.topData ha
  have hd : ¬ Repair.dirty G C a := fun h => h.2 haBelow
  obtain ⟨p, q, hpq⟩ := Frontier.binaryInputs hC haLen
  rw [kept_value G B C hC haLen hd x, haOp, hpq] at hx
  have hpqv : val (shared G B C) (List.ofFn x) (shiftWire n B.gates.length p) = true ∧
      val (shared G B C) (List.ofFn x) (shiftWire n B.gates.length q) = true := by
    simpa [GateOp.eval] using hx
  have h0 : val (shared G B C) (List.ofFn x)
      (shiftWire n B.gates.length (opnd C a 0)) = true := by
    simpa [opnd, hpq] using hpqv.1
  have h1 : val (shared G B C) (List.ofFn x)
      (shiftWire n B.gates.length (opnd C a 1)) = true := by
    simpa [opnd, hpq] using hpqv.2
  obtain ⟨u, hu, hxu⟩ := shared_operand_raw_when_B_false G B C hC hT hBo ha 0 x hBx h0
  obtain ⟨v, hv, hxv⟩ := shared_operand_raw_when_B_false G B C hC hT hBo ha 1 x hBx h1
  apply hn
  apply circuitFun_mono n B hB.1 (pairInput u v) x ?_ (hcover u hu v hv)
  intro t ht
  rcases (Frontier.pairInput_true u v t).mp ht with rfl | rfl
  · exact hxu
  · exact hxv

lemma shared_centreless_dominated_by_B {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C) (hT : TopForm G C)
    (hBo : B.output < n + B.gates.length) {a : ℕ} (ha : a ∈ centreless G C) :
    ∀ x : Fin n → Bool,
      val (shared G B C) (List.ofFn x) (n + (B.gates.length + a)) = true →
        circuitFun n B x = true := by
  obtain ⟨hatop, hside⟩ := Finset.mem_filter.mp ha
  apply shared_top_dominated_by_B G B C hB hC hT hBo hatop
  intro u hu v hv
  rcases hside with h0 | h1
  · rw [h0] at hu
    exact False.elim (Finset.notMem_empty u hu)
  · rw [h1] at hv
    exact False.elim (Finset.notMem_empty v hv)

end SharedRepair

namespace SourcePool
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge SharedRepair

lemma shared_accepts_edges_of_ustar {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hC : IsAO2 n C) (hBo : B.output < n + B.gates.length)
    (hfun : circuitFun n C = graphFun G ∅)
    (hlive : ∀ a ∈ tops G C, OrReaches n C C.output a)
    (hU : ∀ u v : Fin n, s(u, v) ∈ Ustar G C → circuitFun n B (pairInput u v) = true) :
    ∀ u v : Fin n, G.Adj u v → circuitFun n (shared G B C) (pairInput u v) = true := by
  intro u v huv
  by_cases hbad : s(u, v) ∈ Ustar G C
  · apply shared_forward_of_B_true G B C hC hBo _ (hU u v hbad)
    rw [hfun]
    exact Repair.graph_true.mpr ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
  · have he : s(u, v) ∈ G.edgeFinset := by simpa using huv
    have hraw : s(u, v) ∈ starEdges G C := by
      by_contra hn
      exact hbad (Finset.mem_sdiff.mpr ⟨he, hn⟩)
    obtain ⟨a, ha, hcross⟩ := Finset.mem_biUnion.mp hraw
    obtain ⟨⟨p, q⟩, hpq, hpqe⟩ := Finset.mem_image.mp hcross
    obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
    have hv : pairInput u v p = true ∧ pairInput u v q = true := by
      rcases Sym2.eq_iff.mp hpqe with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
        dsimp only at h₁ h₂ <;> simp [h₁, h₂, pairInput]
    exact shared_accepts_raw_top G B C hC _ ha (hlive a ha) hp hq hv.1 hv.2

end SourcePool

namespace CleanBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.ReadK

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma eval_eq_val (C : Circuit) (x : List Bool) : C.eval x = val C x C.output := rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_ge {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ}
    (hu : n + C.gates.length ≤ u) : val C x u = false := by
  unfold val; apply getD_ge; rw [wires_eq_foldl, foldl_length]; omega

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma gateVal_eq_val (n : ℕ) (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    PEqualNP.EdgeOwnership.gateVal n C j x = val C (List.ofFn x) (n + j) := rfl

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3


lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩


def reachable (n : ℕ) (C : Circuit) (k : ℕ) : Prop :=
  k < C.gates.length ∧ (n + k = C.output ∨ InCone n C k (C.output - n))


lemma reachable_child {n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    {k j : ℕ} (hk : reachable n C k) (hj : n + j ∈ (gateAt C k).inputs) :
    reachable n C j := by
  have hlt := rb k hk.1 (n + j) hj
  have hbound := hk.1
  refine ⟨by omega, Or.inr ?_⟩
  have hcone : InCone n C j k := (inCone_iff n C j k).2
    ⟨hk.1, j, by omega, hj, Or.inl rfl⟩
  rcases hk.2 with h | h
  · rwa [show C.output - n = k by omega]
  · exact inCone_trans n C j k hcone _ h


lemma cone_reader {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) :
    ∃ k, k < C.gates.length ∧ (k = j ∨ InCone n C k j) ∧
      n + i ∈ (gateAt C k).inputs := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    obtain ⟨hj, k, hkj, hin, rfl | hc⟩ := (inCone_iff n C i j).1 h
    · exact ⟨j, hj, Or.inl rfl, hin⟩
    · obtain ⟨l, hl, rfl | hlc, hread⟩ := ih k hkj hc
      · exact ⟨l, hl, Or.inr ((inCone_iff n C l j).2
          ⟨hj, l, hkj, hin, Or.inl rfl⟩), hread⟩
      · exact ⟨l, hl, Or.inr ((inCone_iff n C l j).2
          ⟨hj, k, hkj, hin, Or.inr hlc⟩), hread⟩


lemma reachable_reader {n : ℕ} {C : Circuit} {i : ℕ}
    (hi : reachable n C i) (hne : i ≠ C.output - n) :
    ∃ k, reachable n C k ∧ n + i ∈ (gateAt C k).inputs := by
  rcases hi.2 with he | hc
  · omega
  · obtain ⟨k, hk, hr | hr, hin⟩ := cone_reader hc
    · have hn : n ≤ C.output := by
        by_contra h
        obtain ⟨_, j, hj, _, _⟩ := (inCone_iff n C i (C.output - n)).1 hc
        omega
      exact ⟨k, ⟨hk, Or.inl (by omega)⟩, hin⟩
    · exact ⟨k, ⟨hk, Or.inr hr⟩, hin⟩


def singletonSupport (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun u => val C (List.ofFn (pairInput u u)) w = true


lemma mem_support {n : ℕ} {C : Circuit} {w : ℕ} {u : Fin n} :
    u ∈ singletonSupport n C w ↔ val C (List.ofFn (pairInput u u)) w = true := by
  simp [singletonSupport]


lemma support_input {n : ℕ} {C : Circuit} (u : Fin n) :
    singletonSupport n C u.val = {u} := by
  ext v
  rw [mem_support, val_ofFn]
  simp [pairInput, eq_comm]


lemma support_or {n : ℕ} {C : Circuit} (rb : ReadsBack n C)
    {k : ℕ} (hk : k < C.gates.length) (hop : (gateAt C k).op = GateOp.or) (u : Fin n) :
    u ∈ singletonSupport n C (n + k) ↔
      ∃ w ∈ (gateAt C k).inputs, u ∈ singletonSupport n C w := by
  simp only [mem_support, val_or (by simp : (List.ofFn (pairInput u u)).length = n) hk hop]
  exact ⟨fun ⟨w, hw, _, ht⟩ => ⟨w, hw, ht⟩, fun ⟨w, hw, ht⟩ => ⟨w, hw, rb k hk w hw, ht⟩⟩


lemma gate_op {C : Circuit} (hm : Monotone2 C) {k : ℕ} (hk : k < C.gates.length) :
    (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or := by
  simpa using (hm _ (gateAt_mem hk)).1


lemma input_card {C : Circuit} (hm : Monotone2 C) {k : ℕ} (hk : k < C.gates.length) :
    (gateAt C k).inputs.toFinset.card ≤ 2 :=
  (List.toFinset_card_le _).trans (hm _ (gateAt_mem hk)).2


noncomputable def births (n : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun k =>
    reachable n C k ∧ (gateAt C k).op = GateOp.and ∧
      ∃ a b, (gateAt C k).inputs = [a, b] ∧
        (singletonSupport n C a).Nonempty ∧ (singletonSupport n C b).Nonempty


lemma mem_births {n : ℕ} {C : Circuit} {k : ℕ} :
    k ∈ births n C ↔ reachable n C k ∧ (gateAt C k).op = GateOp.and ∧
      ∃ a b, (gateAt C k).inputs = [a, b] ∧
        (singletonSupport n C a).Nonempty ∧ (singletonSupport n C b).Nonempty := by
  classical
  simp only [births, Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨h.1.1, h⟩⟩


def positiveInputs (n : ℕ) (C : Circuit) (k : ℕ) : Finset ℕ := by
  classical
  exact (gateAt C k).inputs.toFinset.filter fun w => (singletonSupport n C w).Nonempty


lemma mem_positiveInputs {n : ℕ} {C : Circuit} {k w : ℕ} :
    w ∈ positiveInputs n C k ↔ w ∈ (gateAt C k).inputs ∧ (singletonSupport n C w).Nonempty := by
  classical
  simp [positiveInputs]


noncomputable def merges (n : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun k =>
    reachable n C k ∧ (gateAt C k).op = GateOp.or ∧
      1 < (singletonSupport n C (n + k)).card ∧ 1 < (positiveInputs n C k).card


lemma mem_merges {n : ℕ} {C : Circuit} {k : ℕ} :
    k ∈ merges n C ↔ reachable n C k ∧ (gateAt C k).op = GateOp.or ∧
      1 < (singletonSupport n C (n + k)).card ∧ 1 < (positiveInputs n C k).card := by
  classical
  simp only [merges, Finset.mem_filter, Finset.mem_range]
  exact ⟨And.right, fun h => ⟨h.1.1, h⟩⟩

-- Each reachable wire with empty singleton support other than the output
-- is read by some reachable gate. Counting these reads pays for connecting
-- the edge-producing AND gates, even when the circuit shares subcircuits.

noncomputable def mergePool {n : ℕ} (C : Circuit) (G : SimpleGraph (Fin n))
    (c : Fin n) (m : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range m).filter fun k => k ∈ merges n C ∧
    ∀ v ∈ singletonSupport n C (n + k), G.Adj c v


lemma mem_mergePool {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} {c : Fin n}
    {m k : ℕ} : k ∈ mergePool C G c m ↔ k < m ∧ k ∈ merges n C ∧
      ∀ v ∈ singletonSupport n C (n + k), G.Adj c v := by
  classical
  simp [mergePool]

-- Expand the largest root with wide singleton support into its positive inputs.
-- A two-input expansion can add one root and is charged to that OR gate.

lemma pair_mono {n : ℕ} {C : Circuit} (hm : Monotone2 C)
    {x y : Fin n → Bool} (hxy : ∀ u, x u = true → y u = true) :
    ∀ w, val C (List.ofFn x) w = true → val C (List.ofFn y) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hinput : w < n
    · let u : Fin n := ⟨w, hinput⟩
      change val C (List.ofFn x) u.val = true at hw
      change val C (List.ofFn y) u.val = true
      rw [val_ofFn] at *
      exact hxy u hw
    · have hwlt : w < n + C.gates.length := by
        by_contra! h
        rw [val_ge (by simp : (List.ofFn x).length = n) h] at hw
        cases hw
      obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      rcases gate_op hm hk with hop | hop
      · apply (val_and (by simp) hk hop).2
        intro i hi
        obtain ⟨hlt, ht⟩ := (val_and (by simp) hk hop).1 hw i hi
        exact ⟨hlt, ih i hlt ht⟩
      · obtain ⟨i, hi, hlt, ht⟩ := (val_or (by simp) hk hop).1 hw
        exact (val_or (by simp) hk hop).2 ⟨i, hi, hlt, ih i hlt ht⟩


lemma crossing {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (hsafe : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      ∀ u v, gateVal n C k (pairInput u v) = true → G.Adj u v)
    {k a b : ℕ} (hk : reachable n C k) (hop : (gateAt C k).op = GateOp.and)
    (hab : (gateAt C k).inputs = [a,b]) :
    ∀ u ∈ singletonSupport n C a, ∀ v ∈ singletonSupport n C b, G.Adj u v := by
  intro u hu v hv
  apply hsafe k hk hop u v
  rw [gateVal_eq_val]
  apply (val_and (by simp) hk.1 hop).2
  intro w hw
  refine ⟨rb k hk.1 w hw, ?_⟩
  have hw' : w = a ∨ w = b := by simpa [hab] using hw
  rcases hw' with rfl | rfl
  · exact pair_mono hm (by intro i; simp [pairInput]; exact Or.inl) _ (mem_support.1 hu)
  · exact pair_mono hm (by intro i; simp [pairInput]; exact Or.inr) _ (mem_support.1 hv)


lemma birth_route {n : ℕ} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (hclean : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      singletonSupport n C (n + k) = ∅)
    (hempty : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      gateVal n C k (fun _ => false) = false)
    (u v : Fin n) :
    ∀ w, (w < n ∨ reachable n C (w - n)) → val C (List.ofFn (pairInput u v)) w = true →
      (∃ k ∈ births n C, ∀ a ∈ (gateAt C k).inputs,
        u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a) ∨
      u ∈ singletonSupport n C w ∨ v ∈ singletonSupport n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw ht
    by_cases hi : w < n
    · let t : Fin n := ⟨w, hi⟩
      change val C (List.ofFn (pairInput u v)) t.val = true at ht
      change _ ∨ u ∈ singletonSupport n C t.val ∨ v ∈ singletonSupport n C t.val
      rw [val_ofFn] at ht
      rw [support_input]
      have he : t = u ∨ t = v := of_decide_eq_true ht
      exact Or.inr (he.imp (fun h => Finset.mem_singleton.2 h.symm) (fun h => Finset.mem_singleton.2 h.symm))
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : reachable n C k := by simpa using hw.resolve_left hi
      have sub (a) (ha : a ∈ (gateAt C k).inputs)
          (ht' : val C (List.ofFn (pairInput u v)) a = true) := by
        apply ih a (rb k hk.1 a ha) _ ht'
        by_cases hn : a < n
        · exact Or.inl hn
        · exact Or.inr (reachable_child rb hk (by rwa [show n + (a - n) = a by omega]))
      rcases gate_op hm hk.1 with hop | hop
      · by_cases hborn : ∃ k ∈ births n C, ∀ a ∈ (gateAt C k).inputs,
            u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a
        · exact Or.inl hborn
        · have hone : ∀ a ∈ (gateAt C k).inputs,
              u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a :=
            fun a ha => (sub a ha ((val_and (by simp) hk.1 hop).1 ht a ha).2).resolve_left hborn
          have hno (t : Fin n) : ¬ ∀ a ∈ (gateAt C k).inputs, t ∈ singletonSupport n C a := by
            intro h
            have hh := (val_and (by simp) hk.1 hop).2 (fun a ha => ⟨rb k hk.1 a ha,
              mem_support.1 (h a ha)⟩ : ∀ a ∈ (gateAt C k).inputs,
                a < n + k ∧ val C (List.ofFn (pairInput t t)) a = true)
            have hs := mem_support.2 hh
            simp [hclean k hk hop] at hs
          have hlen := (hm _ (gateAt_mem hk.1)).2
          generalize he : (gateAt C k).inputs = l at hlen
          cases l with
          | nil =>
            have hz := hempty k hk hop
            rw [gateVal_eq_val, (show val C (List.ofFn (fun _ : Fin n => false)) (n + k) = true from
              (val_and (by simp) hk.1 hop).2 (by simp [he]))] at hz
            cases hz
          | cons a as =>
            cases as with
            | nil =>
              rcases hone a (by simp [he]) with ha | ha
              · exact (hno u (by simpa [he] using ha)).elim
              · exact (hno v (by simpa [he] using ha)).elim
            | cons b bs =>
              have hb0 : bs = [] := List.length_eq_zero_iff.1 (by simp only [List.length_cons] at hlen; omega)
              subst bs
              have nonemp (a) (ha : a ∈ (gateAt C k).inputs) :
                  (singletonSupport n C a).Nonempty := by
                rcases hone a ha with hu | hv
                · exact ⟨u, hu⟩
                · exact ⟨v, hv⟩
              exact Or.inl ⟨k, mem_births.2 ⟨hk, hop, a, b, he,
                nonemp a (by simp [he]), nonemp b (by simp [he])⟩, hone⟩
      · obtain ⟨a, ha, _, ht'⟩ := (val_or (by simp) hk.1 hop).1 ht
        rcases sub a ha ht' with h | h | h
        · exact Or.inl h
        · exact Or.inr (Or.inl ((support_or rb hk.1 hop u).2 ⟨a, ha, h⟩))
        · exact Or.inr (Or.inr ((support_or rb hk.1 hop v).2 ⟨a, ha, h⟩))


lemma birth_star {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (hsafe : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      ∀ u v, gateVal n C k (pairInput u v) = true → G.Adj u v)
    (hcommon : ∀ c d v w : Fin n, c ≠ d → v ≠ w →
      G.Adj c v → G.Adj c w → G.Adj d v → G.Adj d w → False)
    {k : ℕ} (hk : k ∈ births n C) :
    ∃ (c : Fin n) (w : ℕ), w ∈ (gateAt C k).inputs ∧
      (∀ v ∈ singletonSupport n C w, G.Adj c v) ∧
      ∀ u v : Fin n, (∀ a ∈ (gateAt C k).inputs,
        u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a) →
        (u = c ∧ v ∈ singletonSupport n C w) ∨ (v = c ∧ u ∈ singletonSupport n C w) := by
  obtain ⟨hr, hop, a, b, hab, ha, hb⟩ := mem_births.1 hk
  have hex := crossing hm rb hsafe hr hop hab
  have hsmall : (singletonSupport n C a).card ≤ 1 ∨ (singletonSupport n C b).card ≤ 1 := by
    by_contra! h
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 h.1
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.1 h.2
    exact hcommon u v x y huv hxy (hex u hu x hx) (hex u hu y hy) (hex v hv x hx) (hex v hv y hy)
  have star (s w : ℕ) (hs : (singletonSupport n C s).Nonempty)
      (hcard : (singletonSupport n C s).card ≤ 1)
      (hsin : s ∈ (gateAt C k).inputs) (hwin : w ∈ (gateAt C k).inputs)
      (hcross : ∀ u ∈ singletonSupport n C s, ∀ v ∈ singletonSupport n C w, G.Adj u v) :
      ∃ (c : Fin n) (w : ℕ), w ∈ (gateAt C k).inputs ∧
        (∀ v ∈ singletonSupport n C w, G.Adj c v) ∧
        ∀ u v : Fin n, (∀ a ∈ (gateAt C k).inputs,
          u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a) →
          (u = c ∧ v ∈ singletonSupport n C w) ∨ (v = c ∧ u ∈ singletonSupport n C w) := by
    obtain ⟨c, hc⟩ := hs
    have heq : ∀ t ∈ singletonSupport n C s, t = c :=
      fun t ht => Finset.card_le_one.1 hcard t ht c hc
    refine ⟨c, w, hwin, hcross c hc, ?_⟩
    intro u v h
    rcases h s hsin with hu | hv
    · left
      refine ⟨heq u hu, (h w hwin).resolve_left fun hw => ?_⟩
      exact G.irrefl (hcross u hu u hw)
    · right
      refine ⟨heq v hv, (h w hwin).resolve_right fun hw => ?_⟩
      exact G.irrefl (hcross v hv v hw)
  rcases hsmall with h | h
  · exact star a b ha h (by simp [hab]) (by simp [hab]) hex
  · exact star b a hb h (by simp [hab]) (by simp [hab]) (fun u hu v hv => (hex v hv u hu).symm)


def edgeKey {n : ℕ} (c v : Fin n) : Fin n × Fin n := (min c v, max c v)


lemma edgeKey_comm {n : ℕ} (c v : Fin n) : edgeKey c v = edgeKey v c := by
  simp only [edgeKey, min_comm c v, max_comm c v]


private lemma no_four_cycle {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hNoC4 : NoFourCycle G) {a b w1 w2 : Fin n} (hab : a ≠ b) (hw : w1 ≠ w2)
    (haw1 : G.Adj a w1) (haw2 : G.Adj a w2) (hbw1 : G.Adj b w1) (hbw2 : G.Adj b w2) : False := by
  have hle : (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card ≤ 1 := hNoC4 a b hab
  have h1 : w1 ∈ Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w := by
    simp [haw1, hbw1]
  have h2 : w2 ∈ Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w := by
    simp [haw2, hbw2]
  have hgt : 1 < (Finset.univ.filter fun w => G.Adj a w ∧ G.Adj b w).card :=
    Finset.one_lt_card.mpr ⟨w1, h1, w2, h2, hw⟩
  omega

private def edgeTrue {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

private lemma graph_true {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {x : Fin n → Bool} : graphFun G ∅ x = true ↔ edgeTrue G x := by
  simp [graphFun, edgeTrue]

private lemma edge_true_pair {n : ℕ} {G : SimpleGraph (Fin n)} {u v : Fin n} :
    edgeTrue G (pairInput u v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [pairInput, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro h
    exact ⟨u, v, h, by simp [pairInput], by simp [pairInput]⟩

private lemma sorted_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ E : Finset (Fin n × Fin n), E.card = G.edgeFinset.card ∧
      ∀ p ∈ E, G.Adj p.1 p.2 ∧ p.1 ≤ p.2 := by
  let E := Finset.univ.filter fun p : Fin n × Fin n => G.Adj p.1 p.2 ∧ p.1 ≤ p.2
  refine ⟨E, ?_, fun p hp => (Finset.mem_filter.1 hp).2⟩
  apply Finset.card_bij (fun p _ => s(p.1, p.2))
  · exact fun p hp => SimpleGraph.mem_edgeFinset.2 (Finset.mem_filter.1 hp).2.1
  · intro a ha b hb hab
    rcases Sym2.eq_iff.1 hab with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
    · exact Prod.ext h₁ h₂
    · have hle₁ := (Finset.mem_filter.1 ha).2.2
      have hle₂ := (Finset.mem_filter.1 hb).2.2
      have he : b.1 = b.2 := le_antisymm hle₂ (by rwa [h₁, h₂] at hle₁)
      exact Prod.ext (h₁.trans he.symm) (h₂.trans he)
  · intro e he
    induction e using Sym2.ind with
    | _ u v =>
      have h := SimpleGraph.mem_edgeFinset.1 he
      rcases le_total u v with huv | hvu
      · exact ⟨(u, v), Finset.mem_filter.2 ⟨Finset.mem_univ _, h, huv⟩, rfl⟩
      · exact ⟨(v, u), Finset.mem_filter.2 ⟨Finset.mem_univ _, h.symm, hvu⟩, Sym2.eq_swap⟩

end CleanBudget

end PEqualNP.Outside.L_meta_2583

/-! Target-relative clean-circuit bounds. Productive merge gates whose target support
is too small are counted separately; old lambda-source clones give a geometric
instance. These bounds do not prove the full normalization statement. -/

namespace PEqualNP.Outside.L_meta_2583.CleanBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

def restrictedSupport (n : ℕ) (C : Circuit) (W : Finset (Fin n)) (w : ℕ) : Finset (Fin n) :=
  singletonSupport n C w ∩ W

noncomputable def restrictedMergePool {n : ℕ} (C : Circuit) (G : SimpleGraph (Fin n))
    (c : Fin n) (W : Finset (Fin n)) (m : ℕ) : Finset ℕ := by
  classical
  exact (mergePool C G c m).filter fun k => 1 < (restrictedSupport n C W (n + k)).card

lemma mem_restrictedMergePool {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)}
    {c : Fin n} {W : Finset (Fin n)} {m k : ℕ} :
    k ∈ restrictedMergePool C G c W m ↔ k ∈ mergePool C G c m ∧
      1 < (restrictedSupport n C W (n + k)).card := by
  classical
  simp [restrictedMergePool]

lemma restrictedSupport_card_le {n : ℕ} {C : Circuit} {W : Finset (Fin n)} {w : ℕ} :
    (restrictedSupport n C W w).card ≤ (singletonSupport n C w).card :=
  Finset.card_le_card Finset.inter_subset_left

lemma restricted_leaf_budget {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} {c : Fin n}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (hclean : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      singletonSupport n C (n + k) = ∅)
    (W : Finset (Fin n)) (m : ℕ) (roots : Finset ℕ)
    (hvalid : ∀ w ∈ roots, w < n ∨ reachable n C (w - n))
    (hadj : ∀ w ∈ roots, ∀ v ∈ singletonSupport n C w, G.Adj c v)
    (hbound : ∀ w ∈ roots, 1 < (restrictedSupport n C W w).card → w < n + m) :
    (roots.biUnion (restrictedSupport n C W)).card ≤
      roots.card + (restrictedMergePool C G c W m).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have hsmall : ∀ w ∈ roots, (restrictedSupport n C W w).card ≤ 1 := by
      intro w hw
      by_contra! hb
      have hw' := hbound w hw hb
      have hs := support_input (C := C) (⟨w, by omega⟩ : Fin n)
      have hc := restrictedSupport_card_le (C := C) (W := W) (w := w)
      rw [hs] at hc
      simpa using (Nat.lt_of_lt_of_le hb hc)
    calc
      _ ≤ ∑ w ∈ roots, (restrictedSupport n C W w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ roots, 1 := Finset.sum_le_sum hsmall
      _ = _ := by simp [restrictedMergePool, mergePool]
  | succ m ih =>
    have hpool : restrictedMergePool C G c W m ⊆ restrictedMergePool C G c W (m + 1) := by
      intro k hk
      obtain ⟨hkpool, hklarge⟩ := mem_restrictedMergePool.mp hk
      obtain ⟨hk, hh⟩ := mem_mergePool.mp hkpool
      exact mem_restrictedMergePool.mpr ⟨mem_mergePool.mpr ⟨by omega, hh⟩, hklarge⟩
    by_cases htop : n + m ∈ roots ∧ 1 < (restrictedSupport n C W (n + m)).card
    · obtain ⟨hmem, hlarge⟩ := htop
      have hfull : 1 < (singletonSupport n C (n + m)).card :=
        lt_of_lt_of_le hlarge restrictedSupport_card_le
      have hr : reachable n C m := by
        rcases hvalid _ hmem with h | h
        · omega
        · simpa using h
      have hor : (gateAt C m).op = GateOp.or := (gate_op hm hr.1).resolve_left fun h => by
        simp [hclean m hr h] at hfull
      let P := positiveInputs n C m
      let T := roots.erase (n + m) ∪ P
      have hback : ∀ w ∈ P, w < n + m :=
        fun w hw => rb m hr.1 w (mem_positiveInputs.mp hw).1
      have hup : ∀ w ∈ P, singletonSupport n C w ⊆ singletonSupport n C (n + m) := by
        intro w hw u hu
        exact (support_or rb hr.1 hor u).mpr ⟨w, (mem_positiveInputs.mp hw).1, hu⟩
      have hTvalid : ∀ w ∈ T, w < n ∨ reachable n C (w - n) := by
        intro w hw
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hvalid _ (Finset.mem_of_mem_erase hw)
        · by_cases hn : w < n
          · exact Or.inl hn
          · exact Or.inr (reachable_child rb hr (by
              rw [show n + (w - n) = w by omega]
              exact (mem_positiveInputs.mp hw).1))
      have hTadj : ∀ w ∈ T, ∀ v ∈ singletonSupport n C w, G.Adj c v := by
        intro w hw v hv
        rcases Finset.mem_union.mp hw with hw | hw
        · exact hadj _ (Finset.mem_of_mem_erase hw) v hv
        · exact hadj _ hmem v (hup _ hw hv)
      have hTbound : ∀ w ∈ T, 1 < (restrictedSupport n C W w).card → w < n + m := by
        intro w hw hcard
        rcases Finset.mem_union.mp hw with hw | hw
        · have hlt := hbound w (Finset.mem_of_mem_erase hw) hcard
          have hne := (Finset.mem_erase.mp hw).1
          omega
        · exact hback w hw
      have hsub : roots.biUnion (restrictedSupport n C W) ⊆
          T.biUnion (restrictedSupport n C W) := by
        intro u hu
        obtain ⟨w, hw, huw⟩ := Finset.mem_biUnion.mp hu
        by_cases he : w = n + m
        · subst w
          obtain ⟨huold, huW⟩ := Finset.mem_inter.mp huw
          obtain ⟨a, ha, hua⟩ := (support_or rb hr.1 hor u).mp huold
          exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_union_right _
            (mem_positiveInputs.mpr ⟨ha, u, hua⟩), Finset.mem_inter.mpr ⟨hua, huW⟩⟩
        · exact Finset.mem_biUnion.mpr ⟨w,
            Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨he, hw⟩), huw⟩
      have hfirst := (Finset.card_le_card hsub).trans (ih T hTvalid hTadj hTbound)
      have hTcard := Finset.card_union_le (roots.erase (n + m)) P
      have herase := Finset.card_erase_add_one hmem
      have hPc : P.card ≤ 2 := (Finset.card_filter_le _ _).trans (input_card hm hr.1)
      by_cases hp : 1 < P.card
      · have hnew : m ∈ restrictedMergePool C G c W (m + 1) :=
          mem_restrictedMergePool.mpr ⟨mem_mergePool.mpr
            ⟨by omega, mem_merges.mpr ⟨hr, hor, hfull, hp⟩, hadj _ hmem⟩, hlarge⟩
        have hn : m ∉ restrictedMergePool C G c W m := fun h =>
          (Nat.lt_irrefl m) (mem_mergePool.mp (mem_restrictedMergePool.mp h).1).1
        have hsubpool : insert m (restrictedMergePool C G c W m) ⊆
            restrictedMergePool C G c W (m + 1) := Finset.insert_subset_iff.mpr ⟨hnew, hpool⟩
        have hinc := Finset.card_le_card hsubpool
        rw [Finset.card_insert_of_notMem hn] at hinc
        change T.card ≤ (roots.erase (n + m)).card + P.card at hTcard
        omega
      · have hinc := Finset.card_le_card hpool
        change T.card ≤ (roots.erase (n + m)).card + P.card at hTcard
        omega
    · have hnew : ∀ w ∈ roots, 1 < (restrictedSupport n C W w).card → w < n + m := by
        intro w hw hw'
        have hlt := hbound w hw hw'
        have hne : w ≠ n + m := fun he => htop ⟨he ▸ hw, he ▸ hw'⟩
        omega
      have hfirst := ih roots hvalid hadj hnew
      have hinc := Finset.card_le_card hpool
      omega

end PEqualNP.Outside.L_meta_2583.CleanBudget

namespace PEqualNP.Outside.L_meta_2583.CleanBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma lambda_raw_anchor {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j ∈ lam G C) :
    ∃ a : Fin n, ∀ v ∈ orIn n C (n + j), G.Adj a v ∧ s(a, v) ∈ starEdges G C := by
  classical
  obtain ⟨_, _, _, t, ht, b, hother, hr⟩ := Finset.mem_filter.mp hj
  have hne : (side (n := n) C t (1 - b)).Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨a, ha⟩ := hne
  refine ⟨a, ?_⟩
  intro v hv
  have hvs : v ∈ side (n := n) C t b := by
    apply Frontier.reach_mem_orIn
    exact (Frontier.orReaches_reach j _ hr).1.trans (Frontier.mem_orIn_reach v hv)
  fin_cases b
  · have ha1 : a ∈ side (n := n) C t 1 := by simpa using ha
    have hv0 : v ∈ side (n := n) C t 0 := by simpa using hvs
    refine ⟨(Frontier.topAdj hC ht hv0 ha1).symm, ?_⟩
    exact Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_image.mpr
      ⟨(v, a), Finset.mem_product.mpr ⟨hv0, ha1⟩, Sym2.eq_swap⟩⟩
  · have ha0 : a ∈ side (n := n) C t 0 := by simpa using ha
    have hv1 : v ∈ side (n := n) C t 1 := by simpa using hvs
    refine ⟨Frontier.topAdj hC ht ha0 hv1, ?_⟩
    exact Finset.mem_biUnion.mpr ⟨t, ht, Finset.mem_image.mpr
      ⟨(a, v), Finset.mem_product.mpr ⟨ha0, hv1⟩, rfl⟩⟩

end PEqualNP.Outside.L_meta_2583.CleanBudget

/-! Copy accounting without reachability assumptions, followed by exact collapse
of lambda-source signatures after the shared repair. The pure-source lower bound
uses minimum size of the original circuit; the signature collapse is constructive. -/

namespace PEqualNP.Outside.L_meta_2583.CleanBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

noncomputable def reachableGates (n : ℕ) (C : Circuit) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter (reachable n C)

lemma gate_budget_reachable {n : ℕ} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (hclean : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      singletonSupport n C (n + k) = ∅) :
    2 * (births n C).card + (merges n C).card ≤
      (reachableGates n C).card + 1 := by
  classical
  let R := (Finset.range C.gates.length).filter (reachable n C)
  let Z := R.filter fun k => singletonSupport n C (n + k) = ∅
  let D := fun k => (gateAt C k).inputs.toFinset.filter fun w =>
    n ≤ w ∧ singletonSupport n C w = ∅
  let E := fun k => (D k).image fun w => w - n
  have hR (k) : k ∈ R ↔ reachable n C k := by
    simp only [R, Finset.mem_filter, Finset.mem_range]
    exact ⟨And.right, fun h => ⟨h.1, h⟩⟩
  have hZ (k) : k ∈ Z ↔ k ∈ R ∧ singletonSupport n C (n + k) = ∅ := Finset.mem_filter
  have hread : Z.erase (C.output - n) ⊆ R.biUnion E := by
    intro j hj
    obtain ⟨hne, hz⟩ := Finset.mem_erase.1 hj
    obtain ⟨k, hk, hin⟩ := reachable_reader ((hR j).1 ((hZ j).1 hz).1) hne
    refine Finset.mem_biUnion.2 ⟨k, (hR k).2 hk, Finset.mem_image.2 ⟨n + j, ?_, by omega⟩⟩
    exact Finset.mem_filter.2 ⟨List.mem_toFinset.2 hin, by omega, ((hZ j).1 hz).2⟩
  have hsum : Z.card ≤ (∑ k ∈ R, (D k).card) + 1 := by
    calc
      Z.card ≤ (Z.erase (C.output - n)).card + 1 := by
        by_cases h : C.output - n ∈ Z
        · exact Nat.le_of_eq (Finset.card_erase_add_one h).symm
        · rw [Finset.erase_eq_of_notMem h]; omega
      _ ≤ (R.biUnion E).card + 1 := Nat.add_le_add_right (Finset.card_le_card hread) _
      _ ≤ (∑ k ∈ R, (E k).card) + 1 := Nat.add_le_add_right Finset.card_biUnion_le _
      _ ≤ _ := Nat.add_le_add_right (Finset.sum_le_sum fun _ _ => Finset.card_image_le) _
  have hlocal : ∀ k ∈ R, (D k).card + 2 * (if k ∈ births n C then 1 else 0) +
      (if k ∈ merges n C then 1 else 0) ≤ 1 + (if k ∈ Z then 1 else 0) := by
    intro k hk
    have hr := (hR k).1 hk
    have hdp : Disjoint (D k) (positiveInputs n C k) := by
      rw [Finset.disjoint_left]
      intro w hd hp
      have he := (Finset.mem_filter.1 hd).2.2
      simpa [he] using (mem_positiveInputs.1 hp).2
    have hcap : (D k).card + (positiveInputs n C k).card ≤ 2 := by
      rw [← Finset.card_union_of_disjoint hdp]
      exact (Finset.card_le_card (Finset.union_subset
        (Finset.filter_subset _ _) (Finset.filter_subset _ _))).trans (input_card hm hr.1)
    by_cases hb : k ∈ births n C
    · obtain ⟨_, hop, a, b, hab, ha, hb'⟩ := mem_births.1 hb
      have hz := (hZ k).2 ⟨hk, hclean k hr hop⟩
      have hl : k ∉ merges n C := by
        intro h
        have hh := (mem_merges.1 h).2.1
        rw [hop] at hh
        cases hh
      have hd : D k = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.2
        intro w hw
        have hw' := Finset.mem_filter.1 hw
        have hh : w = a ∨ w = b := by simpa [hab] using hw'.1
        rcases hh with rfl | rfl
        · simp [hw'.2.2] at ha
        · simp [hw'.2.2] at hb'
      simp [hb, hz, hl, hd]
    · by_cases hl : k ∈ merges n C
      · have hpos := (mem_merges.1 hl).2.2.2
        simp only [hb, hl, ite_false, ite_true, Nat.mul_zero, Nat.add_zero]
        split_ifs <;> omega
      · by_cases hz : k ∈ Z
        · simp only [hb, hl, hz, ite_false, ite_true, Nat.mul_zero, Nat.add_zero]
          omega
        · have hs : (singletonSupport n C (n + k)).Nonempty :=
            Finset.nonempty_iff_ne_empty.2 fun h => hz ((hZ k).2 ⟨hk, h⟩)
          have hop : (gateAt C k).op = GateOp.or :=
            (gate_op hm hr.1).resolve_left fun h => hs.ne_empty (hclean k hr h)
          obtain ⟨u, hu⟩ := hs
          obtain ⟨w, hw, huw⟩ := (support_or rb hr.1 hop u).1 hu
          have hpos := Finset.card_pos.2 ⟨w, mem_positiveInputs.2 ⟨hw, u, huw⟩⟩
          simp only [hb, hl, hz, ite_false, Nat.mul_zero, Nat.add_zero]
          omega
  have count (T : Finset ℕ) (hT : T ⊆ R) :
      (∑ k ∈ R, if k ∈ T then 1 else 0) = T.card := by
    rw [← Finset.card_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter]
    exact ⟨And.right, fun h => ⟨hT h, h⟩⟩
  have hB : births n C ⊆ R := fun _ h => (hR _).2 (mem_births.1 h).1
  have hL : merges n C ⊆ R := fun _ h => (hR _).2 (mem_merges.1 h).1
  have h := Finset.sum_le_sum hlocal
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum,
    count _ hB, count _ hL, Finset.sum_add_distrib,
    count Z (Finset.filter_subset _ _)] at h
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h
  change 2 * (births n C).card + (merges n C).card ≤ R.card + 1
  omega

lemma large_support_has_merge {n : ℕ} {C : Circuit}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (hclean : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      singletonSupport n C (n + k) = ∅) :
    ∀ w, (w < n ∨ reachable n C (w - n)) → 1 < (singletonSupport n C w).card →
      ∃ k ∈ merges n C, singletonSupport n C (n + k) = singletonSupport n C w := by
  classical
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hvalid hlarge
    by_cases hn : w < n
    · have hs := support_input (C := C) (⟨w, hn⟩ : Fin n)
      rw [hs] at hlarge
      simp at hlarge
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hr : reachable n C j := by simpa using hvalid.resolve_left hn
    have hor : (gateAt C j).op = GateOp.or := (gate_op hm hr.1).resolve_left fun h => by
      simp [hclean j hr h] at hlarge
    by_cases hp : 1 < (positiveInputs n C j).card
    · exact ⟨j, mem_merges.mpr ⟨hr, hor, hlarge, hp⟩, rfl⟩
    obtain ⟨u, hu⟩ := Finset.card_pos.mp (show 0 < (singletonSupport n C (n + j)).card by omega)
    obtain ⟨a, ha, hua⟩ := (support_or rb hr.1 hor u).mp hu
    have haP : a ∈ positiveInputs n C j := mem_positiveInputs.mpr ⟨ha, u, hua⟩
    have heq : singletonSupport n C a = singletonSupport n C (n + j) := by
      ext v
      constructor
      · exact fun hv => (support_or rb hr.1 hor v).mpr ⟨a, ha, hv⟩
      · intro hv
        obtain ⟨b, hb, hvb⟩ := (support_or rb hr.1 hor v).mp hv
        have hbP : b ∈ positiveInputs n C j := mem_positiveInputs.mpr ⟨hb, v, hvb⟩
        have hba : b = a := Finset.card_le_one.mp (by omega) b hbP a haP
        rwa [hba] at hvb
    have havalid : a < n ∨ reachable n C (a - n) := by
      by_cases han : a < n
      · exact Or.inl han
      · exact Or.inr (reachable_child rb hr (by rwa [show n + (a - n) = a by omega]))
    obtain ⟨k, hk, hs⟩ := ih a (rb j hr.1 a ha) havalid (by rw [heq]; exact hlarge)
    exact ⟨k, hk, hs.trans heq⟩

lemma graph_budget_excluded_merges_reachable {n : ℕ} {C : Circuit} (G H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (seed : Fin n)
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (hsafe : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      ∀ u v, gateVal n C k (pairInput u v) = true → G.Adj u v)
    (hempty : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      gateVal n C k (fun _ => false) = false)
    (hcommon : ∀ c d v w : Fin n, c ≠ d → v ≠ w →
      G.Adj c v → G.Adj c w → G.Adj d v → G.Adj d w → False)
    (hout : singletonSupport n C C.output = ∅)
    (hpair : ∀ u v, H.Adj u v → C.eval (List.ofFn (pairInput u v)) = true)
    (E : Finset (Fin n × Fin n))
    (hE : ∀ p ∈ E, H.Adj p.1 p.2 ∧ p.1 ≤ p.2)
    (S : Finset ℕ) (hS : S ⊆ merges n C)
    (hskip : ∀ k ∈ S, ∀ c : Fin n,
      (∀ v ∈ singletonSupport n C (n + k), G.Adj c v) →
      (restrictedSupport n C (Finset.univ.filter (H.Adj c)) (n + k)).card ≤ 1) :
    ∃ T : Finset (Fin n), (∀ u v, H.Adj u v → u ∈ T ∨ v ∈ T) ∧
      T.card ≤ (births n C).card ∧ E.card + (births n C).card + S.card ≤
        (reachableGates n C).card + 1 := by
  classical
  have hclean (k) (hk : reachable n C k) (hop : (gateAt C k).op = GateOp.and) :
      singletonSupport n C (n + k) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro u hu
    exact G.irrefl (hsafe k hk hop u u (mem_support.1 hu))
  let B := births n C
  let star (k : ℕ) (hk : k ∈ B) := birth_star hm rb hsafe hcommon hk
  let c (k : ℕ) := if hk : k ∈ B then (star k hk).choose else seed
  let w (k : ℕ) := if hk : k ∈ B then (star k hk).choose_spec.choose else 0
  have choose_spec (k) (hk : k ∈ B) :
    w k ∈ (gateAt C k).inputs ∧
      (∀ v ∈ singletonSupport n C (w k), G.Adj (c k) v) ∧
      ∀ u v : Fin n, (∀ a ∈ (gateAt C k).inputs,
        u ∈ singletonSupport n C a ∨ v ∈ singletonSupport n C a) →
        (u = c k ∧ v ∈ singletonSupport n C (w k)) ∨ (v = c k ∧ u ∈ singletonSupport n C (w k)) := by
    simpa only [c, w, dite_eq_left hk] using (star k hk).choose_spec.choose_spec
  have cover (u v) (huv : H.Adj u v) :
      ∃ k ∈ B, (u = c k ∧ v ∈ singletonSupport n C (w k)) ∨
        (v = c k ∧ u ∈ singletonSupport n C (w k)) := by
    have hv := hpair u v huv
    rw [eval_eq_val] at hv
    have hl : C.output < n + C.gates.length := by
      by_contra! hh
      rw [val_ge (by simp : (List.ofFn (pairInput u v)).length = n) hh] at hv
      cases hv
    have hn : n ≤ C.output := by
      by_contra! hh
      have he := support_input (C := C) (⟨C.output, hh⟩ : Fin n)
      rw [hout] at he
      exact (Finset.singleton_nonempty _).ne_empty he.symm
    have hr : reachable n C (C.output - n) := ⟨by omega, Or.inl (by omega)⟩
    rcases birth_route hm rb hclean hempty u v C.output (Or.inr hr) hv with h | h
    · obtain ⟨k, hk, ha⟩ := h
      exact ⟨k, hk, (choose_spec k hk).2.2 u v ha⟩
    · simp [hout] at h
  let T := B.image c
  let fiber (u : Fin n) := B.filter fun k => c k = u
  let roots (u : Fin n) := (fiber u).image w
  let W (u : Fin n) := Finset.univ.filter (H.Adj u)
  let leaves (u : Fin n) := (roots u).biUnion (restrictedSupport n C (W u))
  have hcov : ∀ u v, H.Adj u v → u ∈ T ∨ v ∈ T := by
    intro u v huv
    obtain ⟨k, hk, ⟨rfl, _⟩ | ⟨rfl, _⟩⟩ := cover u v huv
    · exact Or.inl (Finset.mem_image_of_mem c hk)
    · exact Or.inr (Finset.mem_image_of_mem c hk)
  have hEsub : E ⊆ T.biUnion (fun t => (leaves t).image (edgeKey t)) := by
    rintro ⟨u, v⟩ hp
    obtain ⟨huv, huv'⟩ := hE _ hp
    obtain ⟨k, hk, h⟩ := cover u v huv
    have hroot : w k ∈ roots (c k) := Finset.mem_image_of_mem w (Finset.mem_filter.2 ⟨hk, rfl⟩)
    refine Finset.mem_biUnion.2 ⟨c k, Finset.mem_image_of_mem c hk, ?_⟩
    have hkey : edgeKey u v = (u, v) := by simp [edgeKey, min_eq_left huv', max_eq_right huv']
    rcases h with ⟨he, h⟩ | ⟨he, h⟩
    · exact Finset.mem_image.2 ⟨v, Finset.mem_biUnion.2 ⟨w k, hroot, Finset.mem_inter.mpr ⟨h, by simpa [W, ← he] using huv⟩⟩, by rwa [← he]⟩
    · exact Finset.mem_image.2 ⟨u, Finset.mem_biUnion.2 ⟨w k, hroot, Finset.mem_inter.mpr ⟨h, by simpa [W, ← he] using huv.symm⟩⟩, by rwa [← he, edgeKey_comm]⟩
  have hleaf (t : Fin n) : (leaves t).card ≤ (fiber t).card +
      (restrictedMergePool C G t (W t) C.gates.length).card := by
    have hr (a) (ha : a ∈ roots t) : ∃ k ∈ B, c k = t ∧ w k = a := by
      obtain ⟨k, hk, he⟩ := Finset.mem_image.1 ha
      exact ⟨k, (Finset.mem_filter.1 hk).1, (Finset.mem_filter.1 hk).2, he⟩
    have h := restricted_leaf_budget (G := G) (c := t) hm rb hclean (W t) C.gates.length (roots t) (by
      intro a ha
      obtain ⟨k, hk, _, rfl⟩ := hr a ha
      by_cases hn : w k < n
      · exact Or.inl hn
      · apply Or.inr
        exact reachable_child rb (mem_births.1 hk).1 (by
          rw [show n + (w k - n) = w k by omega]
          exact (choose_spec k hk).1)) (by
      intro a ha v hv
      obtain ⟨k, hk, rfl, rfl⟩ := hr a ha
      exact (choose_spec k hk).2.1 v hv) (by
      intro a ha _
      obtain ⟨k, hk, _, rfl⟩ := hr a ha
      have hk' := (mem_births.1 hk).1.1
      have := rb k hk' (w k) (choose_spec k hk).1
      omega)
    exact h.trans (Nat.add_le_add_right Finset.card_image_le _)
  have hdisjFib : (T : Set (Fin n)).PairwiseDisjoint fiber := by
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro k hka hkb
    exact hab ((Finset.mem_filter.1 hka).2.symm.trans (Finset.mem_filter.1 hkb).2)
  have hsumB : (∑ t ∈ T, (fiber t).card) = B.card := by
    rw [← Finset.card_biUnion hdisjFib]
    congr 1
    ext k
    constructor
    · intro hk
      obtain ⟨_, _, hf⟩ := Finset.mem_biUnion.1 hk
      exact (Finset.mem_filter.1 hf).1
    · intro hk
      exact Finset.mem_biUnion.2 ⟨c k, Finset.mem_image_of_mem c hk, Finset.mem_filter.2 ⟨hk, rfl⟩⟩
  have hdisjPool : (T : Set (Fin n)).PairwiseDisjoint (fun t => restrictedMergePool C G t (W t) C.gates.length) := by
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro k hka hkb
    obtain ⟨_, hk, ha⟩ := mem_mergePool.1 (Finset.mem_filter.mp hka).1
    have hb := (mem_mergePool.1 (Finset.mem_filter.mp hkb).1).2.2
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 (mem_merges.1 hk).2.2.1
    exact hcommon a b u v hab huv (ha u hu) (ha v hv) (hb u hu) (hb v hv)
  have hsumL : (∑ t ∈ T, (restrictedMergePool C G t (W t) C.gates.length).card) + S.card ≤
      (merges n C).card := by
    rw [← Finset.card_biUnion hdisjPool]
    have hdis : Disjoint (T.biUnion fun t => restrictedMergePool C G t (W t) C.gates.length) S := by
      apply Finset.disjoint_left.mpr
      intro k hk hkS
      obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.mp hk
      obtain ⟨hp, hlarge⟩ := Finset.mem_filter.mp ht
      have hsmall := hskip k hkS t (mem_mergePool.mp hp).2.2
      change 1 < (restrictedSupport n C (Finset.univ.filter (H.Adj t)) (n + k)).card at hlarge
      omega
    rw [← Finset.card_union_of_disjoint hdis]
    apply Finset.card_le_card
    intro k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.mp hk
      exact (mem_mergePool.mp (Finset.mem_filter.mp ht).1).2.1
    · exact hS hk
  have hEL : E.card ≤ B.card + (∑ t ∈ T, (restrictedMergePool C G t (W t) C.gates.length).card) := by
    calc
      _ ≤ (T.biUnion fun t => (leaves t).image (edgeKey t)).card := Finset.card_le_card hEsub
      _ ≤ ∑ t ∈ T, ((leaves t).image (edgeKey t)).card := Finset.card_biUnion_le
      _ ≤ ∑ t ∈ T, (leaves t).card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
      _ ≤ ∑ t ∈ T, ((fiber t).card + (restrictedMergePool C G t (W t) C.gates.length).card) :=
        Finset.sum_le_sum fun t _ => hleaf t
      _ = _ := by rw [Finset.sum_add_distrib, hsumB]
  have hgate := gate_budget_reachable hm rb hclean
  change 2 * B.card + (merges n C).card ≤
    (reachableGates n C).card + 1 at hgate
  refine ⟨T, hcov, Finset.card_image_le, ?_⟩
  change E.card + B.card + S.card ≤ (reachableGates n C).card + 1
  omega



lemma relative_clean_graph_budget_distinct_sources {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (C : Circuit)
    (hfour : NoFourCycle G) (hC : IsAO2 n C)
    (hsafe : ∀ x, circuitFun n C x = true → graphFun G ∅ x = true)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j)
    (hpair : ∀ u v, H.Adj u v → circuitFun n C (pairInput u v) = true)
    (S : Finset ℕ) (hbound : ∀ k ∈ S, k < C.gates.length)
    (hlarge : ∀ k ∈ S, 1 < (singletonSupport n C (n + k)).card)
    (hinj : Set.InjOn (fun k => singletonSupport n C (n + k)) (S : Set ℕ))
    (hanchor : ∀ k ∈ S, ∃ a : Fin n,
      (∀ v ∈ singletonSupport n C (n + k), G.Adj a v) ∧
      (∀ v ∈ singletonSupport n C (n + k), ¬ H.Adj a v)) :
    ∃ T : Finset (Fin n), H.IsVertexCover ↑T ∧
      H.edgeFinset.card + T.card + S.card ≤ C.size + 1 := by
  classical
  have hm : Monotone2 C := by
    intro g hg
    exact ⟨by simpa using hC.1 g hg, (hC.2.2 g hg).le⟩
  have hclean0 : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      singletonSupport n C (n + k) = ∅ := by
    intro k hk hop
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    exact G.irrefl (edge_true_pair.mp (graph_true.mp (hclean k hk.1 hop _ (mem_support.mp hu))))
  let R := (Finset.range C.gates.length).filter (reachable n C)
  let SR := S.filter (reachable n C)
  have hSR : SR ⊆ S := Finset.filter_subset _ _
  have hreps : ∀ k ∈ SR, ∃ j ∈ merges n C,
      singletonSupport n C (n + j) = singletonSupport n C (n + k) := by
    intro k hk
    apply large_support_has_merge hm hC.2.1 hclean0 (n + k)
    · exact Or.inr (by simpa using (Finset.mem_filter.mp hk).2)
    · exact hlarge k (hSR hk)
  let f (k : ℕ) := if hk : k ∈ SR then (hreps k hk).choose else 0
  have hf (k : ℕ) (hk : k ∈ SR) : f k ∈ merges n C ∧
      singletonSupport n C (n + f k) = singletonSupport n C (n + k) := by
    simpa only [f, dite_eq_left hk] using (hreps k hk).choose_spec
  have hfinj : Set.InjOn f (SR : Set ℕ) := by
    intro a ha b hb heq
    apply hinj (hSR ha) (hSR hb)
    change singletonSupport n C (n + a) = singletonSupport n C (n + b)
    rw [← (hf a ha).2, ← (hf b hb).2, heq]
  let M := SR.image f
  have hMcard : M.card = SR.card := Finset.card_image_of_injOn hfinj
  have hM : M ⊆ merges n C := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    exact (hf a ha).1
  have hskip : ∀ k ∈ M, ∀ c : Fin n,
      (∀ v ∈ singletonSupport n C (n + k), G.Adj c v) →
      (restrictedSupport n C (Finset.univ.filter (H.Adj c)) (n + k)).card ≤ 1 := by
    intro k hk c hc
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨d, hd, hnot⟩ := hanchor a (hSR ha)
    have heq := (hf a ha).2
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (hlarge a (hSR ha))
    have hcd : c = d := by
      by_contra hne
      exact no_four_cycle hfour hne huv (hc u (by rwa [heq])) (hc v (by rwa [heq])) (hd u hu) (hd v hv)
    subst c
    have hz : restrictedSupport n C (Finset.univ.filter (H.Adj d)) (n + f a) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨hvs, hvn⟩ := Finset.mem_inter.mp hv
      rw [heq] at hvs
      exact hnot v hvs (Finset.mem_filter.mp hvn).2
    rw [hz]
    simp
  have hdeadcount : R.card + (S \ SR).card ≤ C.size := by
    have hdis : Disjoint R (S \ SR) := by
      apply Finset.disjoint_left.mpr
      intro k hkR hkD
      obtain ⟨hkS, hnkSR⟩ := Finset.mem_sdiff.mp hkD
      exact hnkSR (Finset.mem_filter.mpr ⟨hkS, (Finset.mem_filter.mp hkR).2⟩)
    rw [← Finset.card_union_of_disjoint hdis]
    change (R ∪ (S \ SR)).card ≤ C.gates.length
    rw [← Finset.card_range C.gates.length]
    apply Finset.card_le_card
    intro k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · exact (Finset.mem_filter.mp hk).1
    · exact Finset.mem_range.mpr (hbound k (Finset.mem_sdiff.mp hk).1)
  have hScard := Finset.card_sdiff_add_card_eq_card hSR
  by_cases hne : H.edgeFinset.Nonempty
  · obtain ⟨e, he⟩ := hne
    induction e using Sym2.ind with
    | _ u v =>
      obtain ⟨E, hcard, hE⟩ := sorted_edges H
      obtain ⟨T, hcover, hT, htotal⟩ := graph_budget_excluded_merges_reachable
        (C := C) G H u hm hC.2.1
        (fun j hj hop a b ht => edge_true_pair.mp (graph_true.mp (hclean j hj.1 hop _ ht)))
        (by
          intro j hj hop
          cases h : gateVal n C j (fun _ => false)
          · rfl
          · obtain ⟨a, b, hab, ha, hb⟩ := graph_true.mp (hclean j hj.1 hop _ h)
            cases ha)
        (fun _ _ _ _ => no_four_cycle hfour)
        (by
          apply Finset.eq_empty_iff_forall_notMem.mpr
          intro a ha
          exact G.irrefl (edge_true_pair.mp (graph_true.mp (hsafe _ (mem_support.mp ha)))))
        hpair E hE M hM hskip
      change E.card + (births n C).card + M.card ≤ R.card + 1 at htotal
      refine ⟨T, hcover, ?_⟩
      omega
  · have hempty : H.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    refine ⟨∅, ?_, ?_⟩
    · intro u v huv
      have he : s(u, v) ∈ H.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
      rw [hempty] at he
      exact False.elim (Finset.notMem_empty _ he)
    · have hSrange : S ⊆ Finset.range C.gates.length := by
        intro k hk
        exact Finset.mem_range.mpr (hbound k hk)
      have hc : S.card ≤ C.size := by
        change S.card ≤ C.gates.length
        simpa only [Finset.card_range] using Finset.card_le_card hSrange
      simpa only [hempty, Finset.card_empty, Nat.zero_add] using hc.trans (Nat.le_succ _)

end PEqualNP.Outside.L_meta_2583.CleanBudget

namespace PEqualNP.Outside.L_meta_2583.SharedRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma shared_or_signature {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hC : IsAO2 n C) (hBo : B.output < n + B.gates.length)
    (w : ℕ)
    (hboundary : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      OrReaches n C w j → Repair.dirty G C j)
    (x : Fin n → Bool) :
    val (shared G B C) (List.ofFn x) (shiftWire n B.gates.length w) = true ↔
      (∃ t ∈ orIn n C w, x t = true) ∨
      (circuitFun n B x = true ∧
        ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ OrReaches n C w j) := by
  constructor
  · intro hv
    rcases shared_or_trace G B C hC x w hv with hraw | ⟨j, hj, hop, hr, hvj⟩
    · exact Or.inl hraw
    · rw [copied_value G B C hBo hj (hboundary j hj hop hr) x] at hvj
      exact Or.inr ⟨hvj, j, hj, hop, hr⟩
  · rintro (⟨t, ht, hxt⟩ | ⟨hBx, j, hj, hop, hr⟩)
    · apply shifted_or_path_value G B C hC x (Frontier.mem_orIn_reach t ht)
      rw [shift_input n B.gates.length t.val t.isLt, val_ofFn]
      exact hxt
    · apply shifted_or_path_value G B C hC x (Frontier.orReaches_reach j w hr).1
      rw [shift_gate, copied_value G B C hBo hj (hboundary j hj hop hr) x]
      exact hBx

lemma lambda_or_boundaries_dirty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hC : IsAO2 n C) (hT : TopForm G C) {k : ℕ} (hk : k ∈ lam G C) :
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      OrReaches n C (n + k) j → Repair.dirty G C j := by
  classical
  obtain ⟨_, _, _, a, ha, b, _, hr⟩ := Finset.mem_filter.mp hk
  intro j hj hop hrj
  have hpath := (Frontier.orReaches_reach k _ hr).1.trans
    (Frontier.orReaches_reach j _ hrj).1
  have hor := Frontier.reach_orReaches hpath j rfl hj
  exact Labeling.junk_is_dirty (Frontier.operandOrAndJunk hC hT
    (Frontier.topData ha).1 (Frontier.topData ha).2.1 hor hop)

end PEqualNP.Outside.L_meta_2583.SharedRepair

namespace PEqualNP.Outside.L_meta_2583.CleanBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma shared_lambda_singleton_support {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hC : IsAO2 n C) (hT : TopForm G C)
    (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    {j : ℕ} (hj : j ∈ lam G C) :
    singletonSupport n (SharedRepair.shared G B C) (n + (B.gates.length + j)) =
      orIn n C (n + j) := by
  classical
  ext u
  rw [mem_support]
  have hfalse : circuitFun n B (pairInput u u) = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    exact G.irrefl ((Frontier.graphFun_pair G u u).mp (hBsafe _ ht))
  have hs := SharedRepair.shared_or_signature G B C hC hBo (n + j)
    (SharedRepair.lambda_or_boundaries_dirty G C hC hT hj) (pairInput u u)
  rw [SharedRepair.shift_gate, hfalse] at hs
  simpa [pairInput, val, PEqualNP.Outside.L_meta_2583.val] using hs

end PEqualNP.Outside.L_meta_2583.CleanBudget

namespace PEqualNP.Outside.L_meta_2583.CleanBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm SharedRepair

lemma shared_lambda_distinct_raw_cancellation {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (B C : Circuit)
    (hfour : NoFourCycle G) (hB : IsAO2 n B) (hC : IsAO2 n C) (hTop : TopForm G C)
    (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hBclean : ∀ k < B.gates.length, (gateAt B k).op = GateOp.and → BelowF G B k)
    (hpair : ∀ u v, H.Adj u v → circuitFun n B (pairInput u v) = true)
    (hHU : ∀ u v, H.Adj u v → s(u, v) ∈ Ustar G C)
    (S : Finset ℕ) (hS : S ⊆ lam G C)
    (hcopy : ∀ j ∈ S, ∃ q < n + B.gates.length, ∀ x : Fin n → Bool,
      val B (List.ofFn x) q = val (shared G B C) (List.ofFn x) (n + (B.gates.length + j))) :
    ∃ T : Finset (Fin n), H.IsVertexCover ↑T ∧
      H.edgeFinset.card + T.card +
        ((S.filter fun j => 1 < (orIn n C (n + j)).card).image fun j => orIn n C (n + j)).card
          ≤ B.size + 1 := by
  classical
  let L := S.filter fun j => 1 < (orIn n C (n + j)).card
  let A := L.image fun j => orIn n C (n + j)
  have hlarge (a : Finset (Fin n)) (ha : a ∈ A) : 1 < a.card := by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    exact (Finset.mem_filter.mp hj).2
  have hex : ∀ a ∈ A, ∃ k < B.gates.length, singletonSupport n B (n + k) = a := by
    intro a ha
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp ha
    have hjS := (Finset.mem_filter.mp hj).1
    obtain ⟨q, hq, heq⟩ := hcopy j hjS
    have hs : singletonSupport n B q = orIn n C (n + j) := by
      rw [← shared_lambda_singleton_support G B C hC hTop hBo hBsafe (hS hjS)]
      ext v
      rw [mem_support, mem_support, heq]
    have hqn : n ≤ q := by
      by_contra hn
      have hinput := support_input (C := B) (⟨q, by omega⟩ : Fin n)
      have hc := (Finset.mem_filter.mp hj).2
      rw [← hs, hinput] at hc
      simp at hc
    refine ⟨q - n, by omega, ?_⟩
    simpa only [show n + (q - n) = q by omega] using hs
  let f (a : Finset (Fin n)) := if ha : a ∈ A then (hex a ha).choose else 0
  have hf (a : Finset (Fin n)) (ha : a ∈ A) : f a < B.gates.length ∧
      singletonSupport n B (n + f a) = a := by
    simpa only [f, dite_eq_left ha] using (hex a ha).choose_spec
  have hfinj : Set.InjOn f (A : Set (Finset (Fin n))) := by
    intro a ha b hb heq
    rw [← (hf a ha).2, ← (hf b hb).2, heq]
  let M := A.image f
  have hMcard : M.card = A.card := Finset.card_image_of_injOn hfinj
  have hMbound : ∀ k ∈ M, k < B.gates.length := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    exact (hf a ha).1
  have hMlarge : ∀ k ∈ M, 1 < (singletonSupport n B (n + k)).card := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    rw [(hf a ha).2]
    exact hlarge a ha
  have hMinj : Set.InjOn (fun k => singletonSupport n B (n + k)) (M : Set ℕ) := by
    intro k hk l hl heq
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hl
    change singletonSupport n B (n + f a) = singletonSupport n B (n + f b) at heq
    rw [(hf a ha).2, (hf b hb).2] at heq
    exact congrArg f heq
  have hanchor : ∀ k ∈ M, ∃ c : Fin n,
      (∀ v ∈ singletonSupport n B (n + k), G.Adj c v) ∧
      (∀ v ∈ singletonSupport n B (n + k), ¬ H.Adj c v) := by
    intro k hk
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨j, hj, hja⟩ := Finset.mem_image.mp ha
    obtain ⟨c, hc⟩ := lambda_raw_anchor hC (hS (Finset.mem_filter.mp hj).1)
    refine ⟨c, ?_, ?_⟩
    · intro v hv
      rw [(hf a ha).2, ← hja] at hv
      exact (hc v hv).1
    · intro v hv hadj
      rw [(hf a ha).2, ← hja] at hv
      exact (Finset.mem_sdiff.mp (hHU c v hadj)).2 (hc v hv).2
  obtain ⟨T, hT, hbudget⟩ := relative_clean_graph_budget_distinct_sources G H B hfour hB
    hBsafe hBclean hpair M hMbound hMlarge hMinj hanchor
  refine ⟨T, hT, ?_⟩
  change H.edgeFinset.card + T.card + A.card ≤ B.size + 1
  rwa [hMcard] at hbudget

end PEqualNP.Outside.L_meta_2583.CleanBudget

namespace PEqualNP.Outside.L_meta_2583.ConditionalCopy

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CircuitMoves PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma erase_conditional_clean {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {k p q : ℕ} (_hAO : IsAO2 n C)
    (hk : k < C.gates.length) (hq : q < n + k) (_hp : p < n + k)
    (hpsafe : ∀ x : Fin n → Bool, val C (List.ofFn x) p = true → graphFun G ∅ x = true)
    (heq : ∀ x : Fin n → Bool, val C (List.ofFn x) p = false →
      val C (List.ofFn x) q = val C (List.ofFn x) (n + k))
    (hclean : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → BelowF G C i) :
    ∀ i < (eraseGate n C k q).gates.length, (gateAt (eraseGate n C k q) i).op = GateOp.and →
      BelowF G (eraseGate n C k q) i := by
  have hlen := erase_length n C k q hk
  intro i hi hop x hx
  by_contra hfalse
  have hpfalse : val C (List.ofFn x) p = false := by
    apply Bool.eq_false_iff.mpr
    intro hptrue
    exact hfalse (hpsafe x hptrue)
  apply hfalse
  have hi' : i + 1 < C.gates.length := by omega
  by_cases hik : i < k
  · have hg : gateAt (eraseGate n C k q) i = gateAt C i := by
      rw [erase_gateAt n C k q i hk hi', ite_eq_left hik]
    have hop' : (gateAt C i).op = GateOp.and := by rwa [hg] at hop
    apply hclean i (by omega) hop' x
    have hwire := Duplicate.erase_equal_wires hk hq (heq x hpfalse) (n + i)
    rw [erase_redirect_lt n k q (n + i) (by omega)] at hwire
    change val C (List.ofFn x) (n + i) = true
    rw [← hwire]
    exact hx
  · have hg : gateAt (eraseGate n C k q) i =
        erase_rg (eraseRedirect n k q) (gateAt C (i + 1)) := by
      rw [erase_gateAt n C k q i hk hi', ite_eq_right hik]
    have hop' : (gateAt C (i + 1)).op = GateOp.and := by
      rw [hg] at hop
      exact hop
    apply hclean (i + 1) hi' hop' x
    have hwire := Duplicate.erase_equal_wires hk hq (heq x hpfalse) (n + (i + 1))
    have hr : eraseRedirect n k q (n + (i + 1)) = n + i := by
      rw [erase_redirect_gt n k q (n + (i + 1)) (by omega)]
      omega
    rw [hr] at hwire
    change val C (List.ofFn x) (n + (i + 1)) = true
    rw [← hwire]
    exact hx

lemma erase_output_valid {n : ℕ} {C : Circuit} {k q : ℕ}
    (hk : k < C.gates.length) (hq : q < n + k)
    (hout : C.output < n + C.gates.length) :
    (eraseGate n C k q).output < n + (eraseGate n C k q).gates.length := by
  have hlen := erase_length n C k q hk
  rw [erase_output n C k q hk]
  by_cases hlt : C.output < n + k
  · rw [erase_redirect_lt n k q C.output hlt]
    omega
  · by_cases heq : C.output = n + k
    · rw [heq, erase_redirect_self n k q]
      omega
    · rw [erase_redirect_gt n k q C.output (by omega)]
      omega

end PEqualNP.Outside.L_meta_2583.ConditionalCopy

namespace PEqualNP.Outside.L_meta_2583.ConditionalCopy

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CircuitMoves

lemma collapse_conditional_copies {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset ℕ) (b p : ℕ) : ∀ C : Circuit, IsAO2 n C →
    (∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) →
    C.output < n + C.gates.length → p < b → b ≤ n + C.gates.length →
    (∀ x : Fin n → Bool, val C (List.ofFn x) p = true → graphFun G ∅ x = true) →
    (∀ k ∈ S, k < C.gates.length) → (∀ k ∈ S, b ≤ n + k) →
    (∀ k ∈ S, ∃ q < n + k, ∀ x : Fin n → Bool,
      val C (List.ofFn x) p = false → val C (List.ofFn x) q = val C (List.ofFn x) (n + k)) →
    ∃ D : Circuit, IsAO2 n D ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.output < n + D.gates.length ∧ b ≤ n + D.gates.length ∧
      D.size + S.card = C.size ∧
      (∀ x : Fin n → Bool, ∀ q < b, val D (List.ofFn x) q = val C (List.ofFn x) q) ∧
      (∀ x : Fin n → Bool, val C (List.ofFn x) p = false →
        circuitFun n D x = circuitFun n C x) := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro C hAO hclean hout hp hbnd hpsafe hbound hcut hred
    by_cases hzero : S = ∅
    · exact ⟨C, hAO, hclean, hout, hbnd, by simp [hzero],
        fun _ _ _ => rfl, fun _ _ => rfl⟩
    have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hzero
    let k := S.max' hne
    have hkS : k ∈ S := S.max'_mem hne
    have hk : k < C.gates.length := hbound k hkS
    have hb : b ≤ n + k := hcut k hkS
    obtain ⟨q, hq, heq⟩ := hred k hkS
    let E := eraseGate n C k q
    have hEAO : IsAO2 n E := erase_isAO2 n C k q hk hq hAO
    have hEclean : ∀ j < E.gates.length, (gateAt E j).op = GateOp.and → BelowF G E j :=
      erase_conditional_clean hAO hk hq (by omega : p < n + k) hpsafe heq hclean
    have hEout : E.output < n + E.gates.length := erase_output_valid hk hq hout
    have hlen : E.gates.length + 1 = C.gates.length := erase_length n C k q hk
    have hbndE : b ≤ n + E.gates.length := by omega
    have hlower (x : Fin n → Bool) (w : ℕ) (hw : w < n + k) :
        val E (List.ofFn x) w = val C (List.ofFn x) w :=
      Duplicate.erase_lower_value hk (by simp) hw
    have hprefixE (x : Fin n → Bool) (w : ℕ) (hw : w < b) :
        val E (List.ofFn x) w = val C (List.ofFn x) w := hlower x w (by omega)
    have hpsafeE : ∀ x : Fin n → Bool, val E (List.ofFn x) p = true → graphFun G ∅ x = true := by
      intro x hx
      apply hpsafe x
      rwa [hprefixE x p hp] at hx
    have hsmall : ∀ i ∈ S.erase k, i < k := by
      intro i hi
      obtain ⟨hne, hiS⟩ := Finset.mem_erase.mp hi
      have hmax := S.le_max' i hiS
      omega
    have hboundE : ∀ i ∈ S.erase k, i < E.gates.length := by
      intro i hi
      have hiK := hsmall i hi
      omega
    have hcutE : ∀ i ∈ S.erase k, b ≤ n + i :=
      fun i hi => hcut i (Finset.mem_of_mem_erase hi)
    have hredE : ∀ i ∈ S.erase k, ∃ r < n + i, ∀ x : Fin n → Bool,
        val E (List.ofFn x) p = false → val E (List.ofFn x) r = val E (List.ofFn x) (n + i) := by
      intro i hi
      have hiK := hsmall i hi
      obtain ⟨r, hr, her⟩ := hred i (Finset.mem_of_mem_erase hi)
      refine ⟨r, hr, ?_⟩
      intro x hx
      rw [hlower x r (by omega), hlower x (n + i) (by omega)]
      apply her x
      rwa [hprefixE x p hp] at hx
    have hEfun : ∀ x : Fin n → Bool, val C (List.ofFn x) p = false →
        circuitFun n E x = circuitFun n C x := by
      intro x hx
      change val (eraseGate n C k q) (List.ofFn x) (eraseGate n C k q).output =
        val C (List.ofFn x) C.output
      rw [erase_output n C k q hk]
      exact Duplicate.erase_equal_wires hk hq (heq x hx) C.output
    obtain ⟨D, hDAO, hDclean, hDout, hbndD, hDsize, hDprefix, hDfun⟩ :=
      ih (S.erase k) (Finset.erase_ssubset hkS) E hEAO hEclean hEout hp hbndE hpsafeE
        hboundE hcutE hredE
    refine ⟨D, hDAO, hDclean, hDout, hbndD, ?_, ?_, ?_⟩
    · have hcard := Finset.card_erase_add_one hkS
      have hEsize : E.size + 1 = C.size := erase_size n C k q hk
      omega
    · intro x w hw
      exact (hDprefix x w hw).trans (hprefixE x w hw)
    · intro x hx
      have hEx : val E (List.ofFn x) p = false := by rwa [hprefixE x p hp]
      exact (hDfun x hEx).trans (hEfun x hx)

end PEqualNP.Outside.L_meta_2583.ConditionalCopy

namespace PEqualNP.Outside.L_meta_2583.SharedRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma lambda_raw_nonempty {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) {j : ℕ} (hj : j ∈ lam G C) :
    (orIn n C (n + j)).Nonempty := by
  classical
  obtain ⟨hN, hleft, _⟩ := Finset.mem_filter.mp hj
  have hdata : j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧ ¬ BelowF G C j := by
    simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using hN
  obtain ⟨v, hv⟩ := hleft
  refine ⟨v, Frontier.reach_mem_orIn v ?_⟩
  exact Relation.ReflTransGen.head
    ⟨j, hdata.1, rfl, hdata.2.1, Frontier.opndMem hC hdata.1 0,
      Frontier.opndBound hC hdata.1 0⟩ (Frontier.mem_orIn_reach v hv)

lemma shared_singleton_lambda_value_when_B_false {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (B C : Circuit) (hC : IsAO2 n C) (hTop : TopForm G C)
    (hBo : B.output < n + B.gates.length) {j : ℕ} (hj : j ∈ lam G C)
    (v : Fin n) (hraw : orIn n C (n + j) = {v}) (x : Fin n → Bool)
    (hBx : circuitFun n B x = false) :
    val (shared G B C) (List.ofFn x) (n + (B.gates.length + j)) = x v := by
  apply Bool.eq_iff_iff.mpr
  have hs := shared_or_signature G B C hC hBo (n + j)
    (lambda_or_boundaries_dirty G C hC hTop hj) x
  rw [shift_gate, hraw, hBx] at hs
  simpa using hs

end PEqualNP.Outside.L_meta_2583.SharedRepair

namespace PEqualNP.Outside.L_meta_2583.SharedRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma shared_equal_lambda_raw_when_B_false {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (B C : Circuit) (hC : IsAO2 n C) (hTop : TopForm G C)
    (hBo : B.output < n + B.gates.length) {j k : ℕ}
    (hj : j ∈ lam G C) (hk : k ∈ lam G C)
    (hraw : orIn n C (n + j) = orIn n C (n + k))
    (x : Fin n → Bool) (hBx : circuitFun n B x = false) :
    val (shared G B C) (List.ofFn x) (n + (B.gates.length + j)) =
      val (shared G B C) (List.ofFn x) (n + (B.gates.length + k)) := by
  apply Bool.eq_iff_iff.mpr
  have hjv := shared_or_signature G B C hC hBo (n + j)
    (lambda_or_boundaries_dirty G C hC hTop hj) x
  have hkv := shared_or_signature G B C hC hBo (n + k)
    (lambda_or_boundaries_dirty G C hC hTop hk) x
  rw [shift_gate, hBx] at hjv hkv
  rw [hjv, hkv, hraw]
  simp

lemma shared_exact_of_ustar {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C)
    (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hfun : circuitFun n C = graphFun G ∅)
    (hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j)
    (hlive : ∀ a ∈ tops G C, OrReaches n C C.output a)
    (hU : ∀ u v : Fin n, s(u, v) ∈ Ustar G C → circuitFun n B (pairInput u v) = true) :
    circuitFun n (shared G B C) = graphFun G ∅ := by
  obtain ⟨hAO, _, hsafe, _⟩ := shared_safe_clean G B C hB hC hBo hBsafe
    (fun x hx => by rwa [← hfun]) hBclean
  apply eq_graphFun_of_boundary G _ hAO
    (SourcePool.shared_accepts_edges_of_ustar G B C hC hBo hfun hlive hU)
  intro x hx
  apply Bool.eq_false_iff.mpr
  intro ht
  have hh := hsafe x ht
  rw [hx.1] at hh
  cases hh

lemma shared_collapse_lambda_raw {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C) (hTop : TopForm G C)
    (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hfun : circuitFun n C = graphFun G ∅)
    (hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j)
    (hlive : ∀ a ∈ tops G C, OrReaches n C C.output a)
    (hU : ∀ u v : Fin n, s(u, v) ∈ Ustar G C → circuitFun n B (pairInput u v) = true)
    (T : Finset ℕ) (hT : T ⊆ lam G C) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.size + (junk G C).card + (centreless G C).card + T.card =
        B.size + C.size +
          ((T.filter fun k => 1 < (orIn n C (n + k)).card).image fun k => orIn n C (n + k)).card + 1 := by
  classical
  let label := fun k => orIn n C (n + k)
  let L := T.filter fun k => 1 < (orIn n C (n + k)).card
  have hLT : L ⊆ T := Finset.filter_subset _ _
  obtain ⟨R, hRL, hRcard, hrepresent⟩ := Duplicate.minimum_label_representatives L label
  have hRT : R ⊆ T := hRL.trans hLT
  let A := junk G C ∪ centreless G C
  let S := A ∪ (T \ R)
  let Q := S.image fun k => B.gates.length + k
  have hTdata : ∀ k ∈ T, k < C.gates.length ∧ (gateAt C k).op = GateOp.or := by
    intro k hk
    have h := (Finset.mem_filter.mp (hT hk)).1
    simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at h
    exact ⟨h.1, h.2.1⟩
  have hK : ∀ k ∈ centreless G C, k ∈ tops G C := fun _ h => (Finset.mem_filter.mp h).1
  have hAdata : ∀ k ∈ A, k < C.gates.length ∧ (gateAt C k).op = GateOp.and := by
    intro k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · exact ⟨(Frontier.junkData hk).1, (Frontier.junkData hk).2.1⟩
    · exact ⟨(Frontier.topData (hK k hk)).1, (Frontier.topData (hK k hk)).2.1⟩
  obtain ⟨hAO, hsize, _, hclean⟩ := shared_safe_clean G B C hB hC hBo hBsafe
    (fun x hx => by rwa [← hfun]) hBclean
  have hCo : C.output < n + C.gates.length := by
    apply Completion.output_valid_of_true C (fun _ => true)
    rw [hfun]
    exact hBsafe _ (Completion.ao2_all_true B hB B.output hBo)
  have hQbound : ∀ k ∈ Q, k < (shared G B C).gates.length := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    have hlen : j < C.gates.length := by
      rcases Finset.mem_union.mp hj with hj | hj
      · exact (hAdata j hj).1
      · exact (hTdata j (Finset.mem_sdiff.mp hj).1).1
    rw [shared_length]
    omega
  have hQcut : ∀ k ∈ Q, n + B.gates.length ≤ n + k := by
    intro k hk
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
    omega
  have hpsafe : ∀ x, val (shared G B C) (List.ofFn x) B.output = true →
      graphFun G ∅ x = true := by
    intro x hx
    rw [prefix_value G B C x hBo] at hx
    exact hBsafe x hx
  have hred : ∀ k ∈ Q, ∃ p < n + k, ∀ x : Fin n → Bool,
      val (shared G B C) (List.ofFn x) B.output = false →
      val (shared G B C) (List.ofFn x) p = val (shared G B C) (List.ofFn x) (n + k) := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    rcases Finset.mem_union.mp hj with hj | hj
    · refine ⟨B.output, by omega, ?_⟩
      intro x hBx
      rw [prefix_value G B C x hBo] at hBx ⊢
      change circuitFun n B x = false at hBx
      change circuitFun n B x = val (shared G B C) (List.ofFn x) (n + (B.gates.length + j))
      rcases Finset.mem_union.mp hj with hj | hj
      · rw [copied_value G B C hBo (Frontier.junkData hj).1 (Labeling.junk_is_dirty hj) x]
      · rw [hBx]
        symm
        apply Bool.eq_false_iff.mpr
        intro ht
        have hf := shared_centreless_dominated_by_B G B C hB hC hTop hBo hj x ht
        rw [hBx] at hf
        cases hf
    · have hjT := (Finset.mem_sdiff.mp hj).1
      by_cases hjL : j ∈ L
      · obtain ⟨i, hiL, hij, he⟩ := hrepresent j
          (Finset.mem_sdiff.mpr ⟨hjL, (Finset.mem_sdiff.mp hj).2⟩)
        refine ⟨n + (B.gates.length + i), by omega, ?_⟩
        intro x hBx
        rw [prefix_value G B C x hBo] at hBx
        exact shared_equal_lambda_raw_when_B_false G B C hC hTop hBo (hT (hLT hiL)) (hT hjT) he x hBx
      · have hsmall : (orIn n C (n + j)).card ≤ 1 := by
          have hn : ¬ 1 < (orIn n C (n + j)).card :=
            fun h => hjL (Finset.mem_filter.mpr ⟨hjT, h⟩)
          omega
        have hpos := Finset.card_pos.mpr (lambda_raw_nonempty hC (hT hjT))
        obtain ⟨v, hv⟩ := Finset.card_eq_one.mp
          (show (orIn n C (n + j)).card = 1 by omega)
        refine ⟨v.val, by omega, ?_⟩
        intro x hBx
        rw [prefix_value G B C x hBo] at hBx
        rw [val_ofFn, shared_singleton_lambda_value_when_B_false G B C hC hTop hBo
          (hT hjT) v hv x hBx]
  obtain ⟨E, hEAO, hEclean, hEo, hbnd, hEsize, hEpre, hEfun⟩ :=
    ConditionalCopy.collapse_conditional_copies G Q (n + B.gates.length) B.output
      (shared G B C) hAO hclean (shared_output_valid G B C hCo) hBo
      (by rw [shared_length]; omega) hpsafe hQbound hQcut hred
  have hpE : B.output < n + E.gates.length := by omega
  let D := StarCompletion.appendBinary n E GateOp.or B.output E.output
  have hDAO : IsAO2 n D := StarCompletion.appendBinary_ao n E GateOp.or B.output E.output
    hEAO (Or.inr rfl) hpE hEo
  have hDclean : ∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j :=
    StarCompletion.appendBinary_clean G E GateOp.or B.output E.output hpE hEo hEclean
      (by intro h; cases h)
  have hDval (x : Fin n → Bool) : circuitFun n D x = (circuitFun n B x || circuitFun n E x) := by
    rw [StarCompletion.appendBinary_fun E GateOp.or B.output E.output hpE hEo]
    rw [hEpre x B.output hBo, prefix_value G B C x hBo]
    simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    rfl
  have hDfun : circuitFun n D = graphFun G ∅ := by
    funext x
    cases hBx : circuitFun n B x
    · rw [hDval, hBx, Bool.false_or, hEfun x (by rw [prefix_value G B C x hBo]; exact hBx)]
      exact congrFun (shared_exact_of_ustar G B C hB hC hBo hBsafe hfun hBclean hlive hU) x
    · rw [hDval, hBx, Bool.true_or]
      exact (hBsafe x hBx).symm
  have hJKdis : Disjoint (junk G C) (centreless G C) := by
    apply Finset.disjoint_left.mpr
    intro k hj hk
    exact (Labeling.junk_is_dirty hj).2 (Frontier.topData (hK k hk)).2.2
  have hdis : Disjoint A (T \ R) := by
    apply Finset.disjoint_left.mpr
    intro k hkA hkT
    have ha := (hAdata k hkA).2
    have ho := (hTdata k (Finset.mem_sdiff.mp hkT).1).2
    cases ha.symm.trans ho
  have hAcard : A.card = (junk G C).card + (centreless G C).card :=
    Finset.card_union_of_disjoint hJKdis
  have hScard : S.card = A.card + (T \ R).card := Finset.card_union_of_disjoint hdis
  have hQcard : Q.card = S.card :=
    Finset.card_image_of_injective _ (by intro a b h; exact Nat.add_left_cancel h)
  have hTR : (T \ R).card + R.card = T.card := Finset.card_sdiff_add_card_eq_card hRT
  have hDsize : D.size = E.size + 1 := StarCompletion.appendBinary_size n E GateOp.or B.output E.output
  refine ⟨D, hDAO, hDfun, hDclean, ?_⟩
  change D.size + (junk G C).card + (centreless G C).card + T.card =
    B.size + C.size + (L.image label).card + 1
  omega

end PEqualNP.Outside.L_meta_2583.SharedRepair
