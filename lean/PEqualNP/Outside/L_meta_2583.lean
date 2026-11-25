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

lemma getElem?_gateAt {C : Circuit} {j : ℕ} {g : Gate} (h : C.gates[j]? = some g) :
    gateAt C j = g ∧ j < C.gates.length := by
  have hj : j < C.gates.length := by
    by_contra hc; rw [List.getElem?_eq_none (by omega)] at h; cases h
  refine ⟨?_, hj⟩
  rw [gateAt_eq hj]
  rw [List.getElem?_eq_getElem hj] at h
  exact Option.some.inj h

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

lemma erase_hop_le (r : ℕ → ℕ) (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool)
    (hop : op = GateOp.and ∨ op = GateOp.or) (h : ∀ i, f i = true → f' (r i) = true) :
    op.eval (l.map f) = true → op.eval ((l.map r).map f') = true := by
  rcases hop with rfl | rfl
  · intro hall
    have h1 : (l.map f).all id = true := hall
    show ((l.map r).map f').all id = true
    rw [List.all_eq_true] at h1 ⊢
    intro b hb
    obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hj
    exact h i (h1 (f i) (List.mem_map.2 ⟨i, hi, rfl⟩))
  · intro hany
    have h1 : (l.map f).any id = true := hany
    show ((l.map r).map f').any id = true
    rw [List.any_eq_true] at h1 ⊢
    obtain ⟨b, hb, hbt⟩ := h1
    obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hb
    exact ⟨f' (r i), List.mem_map.2 ⟨r i, List.mem_map.2 ⟨i, hi, rfl⟩, rfl⟩, h i hbt⟩

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

lemma erase_val_imp {n : ℕ} {C : Circuit} {m p : ℕ} (hm : m < C.gates.length) (hp : p < n + m)
    (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) {x : List Bool} (hx : x.length = n)
    (hv : val C x (n + m) = true → val C x p = true) :
    ∀ i, val C x i = true → val (eraseGate n C m p) x (eraseRedirect n m p i) = true :=
  erase_val_rel (fun op => op = GateOp.and ∨ op = GateOp.or) (fun a b => a = true → b = true)
    (fun _ h => h) hm hp (erase_hop_le (eraseRedirect n m p))
    (fun g hg => hAO g (List.mem_of_mem_drop hg)) hx hv

lemma erase_eval_imp {n : ℕ} {C : Circuit} {m p : ℕ} (hm : m < C.gates.length) (hp : p < n + m)
    (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) {x : List Bool} (hx : x.length = n)
    (hv : val C x (n + m) = true → val C x p = true) :
    C.eval x = true → (eraseGate n C m p).eval x = true := by
  intro hC
  show val (eraseGate n C m p) x (eraseGate n C m p).output = true
  rw [erase_output n C m p hm]
  exact erase_val_imp hm hp hAO hx hv C.output hC

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

lemma erase_eval_reverse {n : ℕ} {C : Circuit} {m p : ℕ}
    (hm : m < C.gates.length) (hp : p < n + m)
    (hAO : PEqualNP.EdgeOwnership.AndOrOnly C) {x : List Bool} (hx : x.length = n)
    (hv : val C x p = true → val C x (n + m) = true) :
    (eraseGate n C m p).eval x = true → C.eval x = true := by
  have hop : ∀ (op : GateOp) (l : List ℕ) (f f' : ℕ → Bool),
      (op = GateOp.and ∨ op = GateOp.or) →
      (∀ i, f' (eraseRedirect n m p i) = true → f i = true) →
      op.eval ((l.map (eraseRedirect n m p)).map f') = true →
        op.eval (l.map f) = true := by
    intro op l f f' hOp h
    simpa only [List.map_map, Function.comp_def] using
      (opMono_imp op hOp l (fun i => f' (eraseRedirect n m p i)) f (fun i _ => h i))
  have h := erase_val_rel (fun op => op = GateOp.and ∨ op = GateOp.or)
    (fun a b => b = true → a = true) (fun _ h => h) hm hp hop
    (fun g hg => hAO g (List.mem_of_mem_drop hg)) hx hv C.output
  change val (eraseGate n C m p) x (eraseGate n C m p).output = true →
    val C x C.output = true
  rw [erase_output n C m p hm]
  exact h

lemma erase_singleton_star {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (p : Fin n)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅)
    (hg : g < C.gates.length)
    (hunit : PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.SplitCount.unitInput p) = true)
    (hstar : ∀ u v : Fin n, G.Adj u v →
      PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.EdgeOwnership.pairInput u v) = true →
      p = u ∨ p = v) :
    PEqualNP.TopForm.IsAO2 n (eraseGate n C g p.val) ∧
      (eraseGate n C g p.val).size < C.size ∧
      circuitFun n (eraseGate n C g p.val) = graphFun G ∅ := by
  have hp : p.val < n + g := by omega
  have hD := erase_isAO2 n C g p.val hg hp hAO
  refine ⟨hD, ?_, ?_⟩
  · have hs := erase_size n C g p.val hg
    omega
  · have hsub : ∀ x : Fin n → Bool, x p = true →
        val C (List.ofFn x) (n + g) = true := by
      intro x hxp
      apply mono n C hAO.1 (PEqualNP.SplitCount.unitInput p) x ?_ (n + g) hunit
      intro i hi
      have hip : i = p := by simpa [PEqualNP.SplitCount.unitInput] using hi
      simpa [hip] using hxp
    have hpair : ∀ u v : Fin n, G.Adj u v →
        circuitFun n (eraseGate n C g p.val) (PEqualNP.EdgeOwnership.pairInput u v) = true := by
      intro u v huv
      apply erase_eval_imp hg hp hAO.1 (by simp)
      · intro hgate
        rw [val_ofFn]
        simpa [PEqualNP.EdgeOwnership.pairInput] using hstar u v huv hgate
      · change circuitFun n C (PEqualNP.EdgeOwnership.pairInput u v) = true
        rw [hfun]
        simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
          Bool.false_or, decide_eq_true_eq]
        exact ⟨u, v, huv, by simp [PEqualNP.EdgeOwnership.pairInput],
          by simp [PEqualNP.EdgeOwnership.pairInput]⟩
    funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      rw [← hfun]
      apply erase_eval_reverse hg hp hAO.1 (by simp) ?_ hx
      intro hxp
      apply hsub x
      rwa [val_ofFn] at hxp
    · intro hx
      have hedges : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
        simpa [graphFun] using hx
      obtain ⟨u, v, huv, hxu, hxv⟩ := hedges
      apply circuitFun_mono n (eraseGate n C g p.val) hD.1
        (PEqualNP.EdgeOwnership.pairInput u v) x ?_ (hpair u v huv)
      intro i hi
      have hiuv : i = u ∨ i = v := by simpa [PEqualNP.EdgeOwnership.pairInput] using hi
      rcases hiuv with rfl | rfl
      · exact hxu
      · exact hxv

lemma minimum_gate_has_disjoint_edge {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (g : ℕ) (p : Fin n)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅)
    (hmin : ∀ D : Circuit, PEqualNP.TopForm.IsAO2 n D →
      circuitFun n D = graphFun G ∅ → C.size ≤ D.size)
    (hg : g < C.gates.length)
    (hunit : PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.SplitCount.unitInput p) = true) :
    ∃ u v : Fin n, G.Adj u v ∧
      PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
      p ≠ u ∧ p ≠ v := by
  classical
  by_contra hnone
  have hstar : ∀ u v : Fin n, G.Adj u v →
      PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.EdgeOwnership.pairInput u v) = true →
      p = u ∨ p = v := by
    intro u v huv hgate
    by_cases hpu : p = u
    · exact Or.inl hpu
    by_cases hpv : p = v
    · exact Or.inr hpv
    exact False.elim (hnone ⟨u, v, huv, hgate, hpu, hpv⟩)
  obtain ⟨hD, hsize, hDF⟩ := erase_singleton_star G C g p hAO hfun hg hunit hstar
  exact Nat.not_le_of_gt hsize (hmin _ hD hDF)

lemma minimum_gate_has_critical_disjoint_edge {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (g : ℕ) (p : Fin n)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅)
    (hmin : ∀ D : Circuit, PEqualNP.TopForm.IsAO2 n D →
      circuitFun n D = graphFun G ∅ → C.size ≤ D.size)
    (hg : g < C.gates.length)
    (hunit : PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.SplitCount.unitInput p) = true) :
    ∃ u v : Fin n, G.Adj u v ∧ p ≠ u ∧ p ≠ v ∧
      PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
      circuitFun n (eraseGate n C g p.val) (PEqualNP.EdgeOwnership.pairInput u v) = false := by
  classical
  have hp : p.val < n + g := by omega
  have hD := erase_isAO2 n C g p.val hg hp hAO
  have hCpair : ∀ u v : Fin n, G.Adj u v →
      circuitFun n C (PEqualNP.EdgeOwnership.pairInput u v) = true := by
    intro u v huv
    rw [hfun]
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨u, v, huv, by simp [PEqualNP.EdgeOwnership.pairInput],
      by simp [PEqualNP.EdgeOwnership.pairInput]⟩
  have hsub : ∀ x : Fin n → Bool, x p = true →
      val C (List.ofFn x) (n + g) = true := by
    intro x hxp
    apply mono n C hAO.1 (PEqualNP.SplitCount.unitInput p) x ?_ (n + g) hunit
    intro i hi
    have hip : i = p := by simpa [PEqualNP.SplitCount.unitInput] using hi
    simpa [hip] using hxp
  have hlost : ∃ u v : Fin n, G.Adj u v ∧
      circuitFun n (eraseGate n C g p.val) (PEqualNP.EdgeOwnership.pairInput u v) = false := by
    by_contra hnone
    have hpair : ∀ u v : Fin n, G.Adj u v →
        circuitFun n (eraseGate n C g p.val) (PEqualNP.EdgeOwnership.pairInput u v) = true := by
      intro u v huv
      cases hval : circuitFun n (eraseGate n C g p.val)
          (PEqualNP.EdgeOwnership.pairInput u v) with
      | false => exact False.elim (hnone ⟨u, v, huv, hval⟩)
      | true => rfl
    have hDF : circuitFun n (eraseGate n C g p.val) = graphFun G ∅ := by
      funext x
      apply Bool.eq_iff_iff.mpr
      constructor
      · intro hx
        rw [← hfun]
        apply erase_eval_reverse hg hp hAO.1 (by simp) ?_ hx
        intro hxp
        apply hsub x
        rwa [val_ofFn] at hxp
      · intro hx
        have hedges : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
          simpa [graphFun] using hx
        obtain ⟨u, v, huv, hxu, hxv⟩ := hedges
        apply circuitFun_mono n (eraseGate n C g p.val) hD.1
          (PEqualNP.EdgeOwnership.pairInput u v) x ?_ (hpair u v huv)
        intro i hi
        have hiuv : i = u ∨ i = v := by simpa [PEqualNP.EdgeOwnership.pairInput] using hi
        rcases hiuv with rfl | rfl
        · exact hxu
        · exact hxv
    have hle := hmin _ hD hDF
    have hs := erase_size n C g p.val hg
    omega
  obtain ⟨u, v, huv, hdrop⟩ := hlost
  have hgate : PEqualNP.EdgeOwnership.gateVal n C g
      (PEqualNP.EdgeOwnership.pairInput u v) = true := by
    by_contra hgate
    have hkeep : circuitFun n (eraseGate n C g p.val)
        (PEqualNP.EdgeOwnership.pairInput u v) = true := by
      apply erase_eval_imp hg hp hAO.1 (by simp) ?_ (hCpair u v huv)
      intro h
      exact False.elim (hgate h)
    rw [hdrop] at hkeep
    cases hkeep
  have hdisjoint : ¬ (p = u ∨ p = v) := by
    intro hin
    have hpin : val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) p.val = true := by
      rw [val_ofFn]
      simpa [PEqualNP.EdgeOwnership.pairInput] using hin
    have hkeep : circuitFun n (eraseGate n C g p.val)
        (PEqualNP.EdgeOwnership.pairInput u v) = true :=
      erase_eval_imp hg hp hAO.1 (by simp) (fun _ => hpin) (hCpair u v huv)
    rw [hdrop] at hkeep
    cases hkeep
  exact ⟨u, v, huv, fun h => hdisjoint (Or.inl h),
    fun h => hdisjoint (Or.inr h), hgate, hdrop⟩


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

lemma erase_of_edge_and_maximal_false_conditions {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (g w : ℕ)
    (hAO : PEqualNP.TopForm.IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅)
    (hg : g < C.gates.length) (hw : w < n + g)
    (hpos : ∀ u v : Fin n, G.Adj u v →
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) (n + g) = true →
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) w = true)
    (hneg : ∀ x : Fin n → Bool, Maximal (fun y => graphFun G ∅ y = false) x →
      val C (List.ofFn x) w = true → val C (List.ofFn x) (n + g) = true) :
    PEqualNP.TopForm.IsAO2 n (eraseGate n C g w) ∧
      (eraseGate n C g w).size < C.size ∧
      circuitFun n (eraseGate n C g w) = graphFun G ∅ := by
  have hD := erase_isAO2 n C g w hg hw hAO
  refine ⟨hD, ?_, eq_graphFun_of_boundary G _ hD ?_ ?_⟩
  · have hs := erase_size n C g w hg
    omega
  · intro u v huv
    apply erase_eval_imp hg hw hAO.1 (by simp) (hpos u v huv)
    change circuitFun n C (PEqualNP.EdgeOwnership.pairInput u v) = true
    rw [hfun]
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨u, v, huv, by simp [PEqualNP.EdgeOwnership.pairInput],
      by simp [PEqualNP.EdgeOwnership.pairInput]⟩
  · intro x hx
    apply Bool.eq_false_iff.mpr
    intro hDx
    have hCx : circuitFun n C x = true :=
      erase_eval_reverse hg hw hAO.1 (by simp) (hneg x hx) hDx
    rw [hfun, hx.1] at hCx
    contradiction

lemma minimum_no_earlier_maximal_boundary_dominator {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (g w : ℕ)
    (hmin : PEqualNP.TopForm.IsLeastAO G C)
    (hg : g < C.gates.length) (hw : w < n + g) :
    (∃ u v : Fin n, G.Adj u v ∧
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) (n + g) = true ∧
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) w = false) ∨
    (∃ x : Fin n → Bool, Maximal (fun y => graphFun G ∅ y = false) x ∧
      val C (List.ofFn x) w = true ∧ val C (List.ofFn x) (n + g) = false) := by
  classical
  by_contra hnone
  have hpos : ∀ u v : Fin n, G.Adj u v →
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) (n + g) = true →
      val C (List.ofFn (PEqualNP.EdgeOwnership.pairInput u v)) w = true := by
    intro u v huv hgval
    by_contra hwval
    exact hnone (Or.inl ⟨u, v, huv, hgval, Bool.eq_false_iff.mpr hwval⟩)
  have hneg : ∀ x : Fin n → Bool, Maximal (fun y => graphFun G ∅ y = false) x →
      val C (List.ofFn x) w = true → val C (List.ofFn x) (n + g) = true := by
    intro x hFx hwval
    by_contra hgval
    exact hnone (Or.inr ⟨x, hFx, hwval, Bool.eq_false_iff.mpr hgval⟩)
  obtain ⟨hD, hsize, hDF⟩ := erase_of_edge_and_maximal_false_conditions G C g w
    hmin.1 hmin.2.1 hg hw hpos hneg
  exact Nat.not_le_of_gt hsize (hmin.2.2 _ hD hDF)


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

lemma or_trace {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) :
    ∀ w : ℕ, val C x w = true →
      ∃ w', Relation.ReflTransGen (OrStep n C) w w' ∧ val C x w' = true ∧
        (w' < n ∨ ∃ h, h < C.gates.length ∧ w' = n + h ∧ (gateAt C h).op ≠ GateOp.or) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hw : w < n
    · exact ⟨w, Relation.ReflTransGen.refl, hv, Or.inl hw⟩
    · by_cases hlen : n + C.gates.length ≤ w
      · rw [val_ge hx hlen] at hv; cases hv
      · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
        have hk : k < C.gates.length := by omega
        by_cases hop : (gateAt C k).op = GateOp.or
        · obtain ⟨i, hin, hlt, hi⟩ := (val_or hx hk hop).mp hv
          obtain ⟨w', hr, hv', hw'⟩ := ih i hlt hi
          exact ⟨w', Relation.ReflTransGen.head ⟨k, hk, rfl, hop, hin, hlt⟩ hr, hv', hw'⟩
        · exact ⟨n + k, Relation.ReflTransGen.refl, hv, Or.inr ⟨k, hk, rfl, hop⟩⟩

lemma pairInput_left {n : ℕ} (u v : Fin n) : pairInput u v u = true := by
  simp [pairInput]

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

lemma operand_trace {n : ℕ} {C : Circuit} (u v : Fin n) (p : ℕ)
    (hv : val C (List.ofFn (pairInput u v)) p = true) :
    (∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (OrStep n C) p t.val) ∨
    (∃ h, h < C.gates.length ∧ (gateAt C h).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) p (n + h) ∧
      val C (List.ofFn (pairInput u v)) (n + h) = true) := by
  obtain ⟨w', hr, hv', hw'⟩ := or_trace (n := n) (C := C) (x := List.ofFn (pairInput u v))
    (by simp) p hv
  rcases hw' with hlt | ⟨h, hh, rfl, hop⟩
  · left
    refine ⟨⟨w', hlt⟩, ?_, hr⟩
    have h1 := val_ofFn C (pairInput u v) ⟨w', hlt⟩
    rw [show (⟨w', hlt⟩ : Fin n).val = w' from rfl, hv'] at h1
    exact (pairInput_true u v _).mp h1.symm
  · right
    exact ⟨h, hh, hop, hr, hv'⟩

lemma reach_var_val {n : ℕ} {C : Circuit} (x : Fin n → Bool) (p : ℕ) (t : Fin n)
    (hr : Relation.ReflTransGen (OrStep n C) p t.val) (ht : x t = true) :
    val C (List.ofFn x) p = true :=
  orStep_up (n := n) (by simp) hr (by rw [val_ofFn]; exact ht)

lemma edge_trace {n : ℕ} (G : SimpleGraph (Fin n)) {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hF : ∀ u v : Fin n, F (pairInput u v) = true → G.Adj u v)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x)
    (u v : Fin n) (huv : F (pairInput u v) = true) :
    ∃ a, a < C.gates.length ∧ (gateAt C a).op ≠ GateOp.or ∧
      Relation.ReflTransGen (OrStep n C) C.output (n + a) ∧
      val C (List.ofFn (pairInput u v)) (n + a) = true := by
  rcases operand_trace (C := C) u v C.output (by rw [hout]; exact huv) with
    ⟨t, _, hr⟩ | h
  · exfalso
    have h1 := reach_var_val (pairInput t t) _ t hr (pairInput_left t t)
    rw [hout] at h1
    exact G.irrefl (hF t t h1)
  · exact h

lemma below_of_reach {n : ℕ} {C : Circuit} (F : (Fin n → Bool) → Bool)
    (hout : ∀ x : Fin n → Bool, val C (List.ofFn x) C.output = F x) (a : ℕ)
    (hr : Relation.ReflTransGen (OrStep n C) C.output (n + a)) (x : Fin n → Bool)
    (hv : val C (List.ofFn x) (n + a) = true) : F x = true := by
  rw [← hout]
  exact orStep_up (n := n) (by simp) hr hv

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

lemma andValOperands (hAO : IsAO2 n C) {a : ℕ} (ha : a < C.gates.length)
    (hop : (gateAt C a).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C a x = true ↔ ∀ b : Fin 2, val C (List.ofFn x) (opnd C a b) = true := by
  rw [andValBoth hAO ha hop]
  constructor
  · intro h b
    fin_cases b
    · exact h.1
    · exact h.2
  · intro h
    exact ⟨h 0, h 1⟩

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

lemma reachVal {w h : ℕ} {x : Fin n → Bool} (hr : OrReaches n C w h)
    (hh : gateVal n C h x = true) : val C (List.ofFn x) w = true :=
  orStep_up (n := n) (by simp) (orReaches_reach h _ hr).1 hh

lemma operandSupport (hAO : IsAO2 n C) (hT : TopForm G C) {a : ℕ}
    (ha : a < C.gates.length) (ho : (gateAt C a).op = GateOp.and) {b : Fin 2}
    {u v : Fin n} (h : val C (List.ofFn (pairInput u v)) (opnd C a b) = true) :
    (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
      ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧
        gateVal n C j (pairInput u v) = true := by
  rcases operand_trace (C := C) u v _ h with ⟨t, ht, hr⟩ | ⟨j, hj, hn, hr, hv⟩
  · exact .inl ⟨t, reach_mem_orIn t hr, ht⟩
  · have hr' := reach_orReaches hr j rfl hj
    exact .inr ⟨j, operandOrAndJunk hAO hT ha ho hr'
      ((hAO.1 _ (gateAt_mem hj)).resolve_right hn), hr', hv⟩

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

lemma accepted_top_with_reach (hAO : IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅) {u v : Fin n} (hadj : G.Adj u v) :
    ∃ a ∈ tops G C, OrReaches n C C.output a ∧ gateVal n C a (pairInput u v) = true := by
  have hout (x : Fin n → Bool) : val C (List.ofFn x) C.output = graphFun G ∅ x :=
    congrFun hfun x
  obtain ⟨a, hl, ho, hr, hv⟩ :=
    edge_trace G (graphFun G ∅) (fun k l => (graphFun_pair G k l).mp)
      hout u v ((graphFun_pair G u v).mpr hadj)
  have hand := (hAO.1 _ (gateAt_mem hl)).resolve_right ho
  have hb : BelowF G C a := fun x hx =>
    below_of_reach (graphFun G ∅) hout a hr x (gateVal_eq_val n C a x ▸ hx)
  refine ⟨a, ?_, reach_orReaches hr a rfl hl, hv⟩
  simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using
    And.intro hl (And.intro hand hb)

lemma top_dirty_frontiers_distinct (hAO : IsAO2 n C) {a j k : ℕ}
    (ha : a ∈ tops G C) (hj : j ∈ junk G C)
    (hrj : OrReaches n C (opnd C a 0) j)
    (hrk : OrReaches n C (opnd C a 1) k) : j ≠ k := by
  rintro rfl
  obtain ⟨haLen, haOp, haBelow⟩ := topData ha
  obtain ⟨_, _, x, hx, hFx⟩ := junkData hj
  have haTrue : gateVal n C a x = true :=
    (andValBoth hAO haLen haOp x).mpr ⟨reachVal hrj hx, reachVal hrk hx⟩
  have h := haBelow x haTrue
  rw [hFx] at h
  cases h

lemma two_dirty_frontier (hAO : IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅) (hT : TopForm G C)
    {u v : Fin n} (hadj : G.Adj u v) :
    ∃ a ∈ tops G C, OrReaches n C C.output a ∧
      gateVal n C a (pairInput u v) = true ∧
      ∃ H : Finset ℕ, H.card ≤ 2 ∧ H ⊆ junk G C ∧
        (∀ j ∈ H, gateVal n C j (pairInput u v) = true ∧
          ∃ b : Fin 2, OrReaches n C (opnd C a b) j) ∧
        (∀ b : Fin 2, (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
          ∃ j ∈ H, OrReaches n C (opnd C a b) j ∧ gateVal n C j (pairInput u v) = true) := by
  classical
  obtain ⟨a, ha, hr, hva⟩ := accepted_top_with_reach hAO hfun hadj
  obtain ⟨haLen, haOp, _⟩ := topData ha
  let raw : Fin 2 → Prop := fun b => ∃ t ∈ side (n := n) C a b, t = u ∨ t = v
  have hs : ∀ b : Fin 2, ∃ j : ℕ, raw b ∨
      (j ∈ junk G C ∧ OrReaches n C (opnd C a b) j ∧ gateVal n C j (pairInput u v) = true) := by
    intro b
    rcases operandSupport hAO hT haLen haOp ((andValOperands hAO haLen haOp _).mp hva b) with
      hraw | ⟨j, hj, hjr, hjv⟩
    · exact ⟨0, Or.inl hraw⟩
    · exact ⟨j, Or.inr ⟨hj, hjr, hjv⟩⟩
  let f : Fin 2 → ℕ := fun b => Classical.choose (hs b)
  have hf (b : Fin 2) : raw b ∨
      (f b ∈ junk G C ∧ OrReaches n C (opnd C a b) (f b) ∧
        gateVal n C (f b) (pairInput u v) = true) := Classical.choose_spec (hs b)
  let B : Finset (Fin 2) := Finset.univ.filter fun b => ¬ raw b
  let H : Finset ℕ := B.image f
  have hb (b : Fin 2) (hbB : b ∈ B) :
      f b ∈ junk G C ∧ OrReaches n C (opnd C a b) (f b) ∧
        gateVal n C (f b) (pairInput u v) = true :=
    (hf b).resolve_left (Finset.mem_filter.mp hbB).2
  refine ⟨a, ha, hr, hva, H, ?_, ?_, ?_, ?_⟩
  · calc
      H.card ≤ B.card := Finset.card_image_le
      _ ≤ (Finset.univ : Finset (Fin 2)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 2 := by simp
  · intro j hj
    obtain ⟨b, hbB, rfl⟩ := Finset.mem_image.mp hj
    exact (hb b hbB).1
  · intro j hj
    obtain ⟨b, hbB, rfl⟩ := Finset.mem_image.mp hj
    exact ⟨(hb b hbB).2.2, b, (hb b hbB).2.1⟩
  · intro b
    by_cases hraw : raw b
    · exact Or.inl hraw
    · have hbB : b ∈ B := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hraw⟩
      exact Or.inr ⟨f b, Finset.mem_image.mpr ⟨b, hbB, rfl⟩,
        (hb b hbB).2.1, (hb b hbB).2.2⟩

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

lemma ustar_two_dirty_frontier (hAO : IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅) (hT : TopForm G C)
    {u v : Fin n} (huv : s(u, v) ∈ Ustar G C) :
    ∃ a ∈ tops G C, OrReaches n C C.output a ∧
      gateVal n C a (pairInput u v) = true ∧
      ∃ H : Finset ℕ, H.Nonempty ∧ H.card ≤ 2 ∧ H ⊆ junk G C ∧
        (∀ j ∈ H, gateVal n C j (pairInput u v) = true ∧
          ∃ b : Fin 2, OrReaches n C (opnd C a b) j) ∧
        (∀ b : Fin 2, (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
          ∃ j ∈ H, OrReaches n C (opnd C a b) j ∧ gateVal n C j (pairInput u v) = true) := by
  classical
  have he : s(u, v) ∈ G.edgeFinset := (Finset.mem_sdiff.mp huv).1
  have hadj : G.Adj u v := SimpleGraph.mem_edgeFinset.mp he
  obtain ⟨a, ha, hr, hva, H, hcard, hjunk, hH, hcover⟩ := two_dirty_frontier hAO hfun hT hadj
  refine ⟨a, ha, hr, hva, H, ?_, hcard, hjunk, hH, hcover⟩
  by_contra hnone
  have hempty : H = ∅ := Finset.not_nonempty_iff_eq_empty.mp hnone
  have hraw (b : Fin 2) : ∃ t ∈ side (n := n) C a b, t = u ∨ t = v := by
    rcases hcover b with h | ⟨j, hj, _, _⟩
    · exact h
    · rw [hempty] at hj
      exact False.elim (Finset.notMem_empty _ hj)
  obtain ⟨x, hx, hxe⟩ := hraw 0
  obtain ⟨y, hy, hye⟩ := hraw 1
  have hne : x ≠ y := G.ne_of_adj (topAdj hAO ha hx hy)
  have hsym : s(u, v) = s(x, y) := by
    rcases hxe with hxu | hxv <;> rcases hye with hyu | hyv
    · exact False.elim (hne (hxu.trans hyu.symm))
    · rw [hxu, hyv]
    · rw [hxv, hyu]
      exact Sym2.eq_swap
    · exact False.elim (hne (hxv.trans hyv.symm))
  apply (Finset.mem_sdiff.mp huv).2
  rw [hsym]
  exact Finset.mem_biUnion.mpr ⟨a, ha,
    Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩⟩

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

noncomputable def repair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (pick : ℕ → Fin n × Fin n) : Circuit := by
  classical
  exact ⟨(List.range C.gates.length).map fun j =>
    if dirty G C j then ⟨GateOp.and, [(pick j).1.val, (pick j).2.val]⟩ else gateAt C j,
    C.output⟩

lemma repair_len {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (pick : ℕ → Fin n × Fin n) :
    (repair G C pick).gates.length = C.gates.length := by
  simp [repair]

lemma repair_gate {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (pick : ℕ → Fin n × Fin n) {j : ℕ} (hj : j < C.gates.length) :
    gateAt (repair G C pick) j =
      @ite Gate (dirty G C j) (Classical.propDecidable _)
        ⟨GateOp.and, [(pick j).1.val, (pick j).2.val]⟩ (gateAt C j) := by
  classical
  have hj' : j < (repair G C pick).gates.length := by rwa [repair_len]
  rw [gateAt_eq hj']
  simp [repair]

lemma repair_ao {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) (pick : ℕ → Fin n × Fin n) :
    IsAO2 n (repair G C pick) := by
  classical
  have hgate (j : ℕ) (hj : j < (repair G C pick).gates.length) :
      ((gateAt (repair G C pick) j).op = GateOp.and ∨
        (gateAt (repair G C pick) j).op = GateOp.or) ∧
      (gateAt (repair G C pick) j).inputs.length = 2 ∧
      ∀ w ∈ (gateAt (repair G C pick) j).inputs, w < n + j := by
    rw [repair_len] at hj
    rw [repair_gate pick hj]
    split_ifs
    · refine ⟨Or.inl rfl, rfl, ?_⟩
      intro w hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · have := (pick j).1.isLt
        omega
      · have := (pick j).2.isLt
        omega
    · exact ⟨hC.1 _ (gateAt_mem hj), hC.2.2 _ (gateAt_mem hj), hC.2.1 j hj⟩
  refine ⟨?_, fun j hj => (hgate j hj).2.2, ?_⟩
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    rw [← gateAt_eq hj]
    exact (hgate j hj).1
  · intro g hg
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
    rw [← gateAt_eq hj]
    exact (hgate j hj).2.1

lemma repair_kept {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (pick : ℕ → Fin n × Fin n) {j : ℕ} (hj : j < C.gates.length)
    (h : ¬ dirty G C j) : gateAt (repair G C pick) j = gateAt C j := by
  classical
  rw [repair_gate pick hj, ite_eq_right h]

lemma repair_replaced_val {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (pick : ℕ → Fin n × Fin n) {j : ℕ} (hj : j < C.gates.length)
    (hd : dirty G C j) (x : Fin n → Bool) :
    val (repair G C pick) (List.ofFn x) (n + j) = true ↔
      x (pick j).1 = true ∧ x (pick j).2 = true := by
  classical
  have hj' : j < (repair G C pick).gates.length := by rwa [repair_len]
  have hg := (repair_gate (G := G) pick hj).trans (ite_eq_left hd)
  rw [val_and (by simp) hj' (congrArg Gate.op hg), hg]
  have h₁ : (pick j).1.val < n + j := by have := (pick j).1.isLt; omega
  have h₂ : (pick j).2.val < n + j := by have := (pick j).2.isLt; omega
  simp [h₁, h₂, val_ofFn]

lemma repair_compare {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) (pick : ℕ → Fin n × Fin n)
    (x : Fin n → Bool) (forward : Bool)
    (hreplaced : ∀ j < C.gates.length, dirty G C j →
      if forward then
        val C (List.ofFn x) (n + j) = true → val (repair G C pick) (List.ofFn x) (n + j) = true
      else
        val (repair G C pick) (List.ofFn x) (n + j) = true → val C (List.ofFn x) (n + j) = true) :
    ∀ w : ℕ, if forward then
      val C (List.ofFn x) w = true → val (repair G C pick) (List.ofFn x) w = true
    else
      val (repair G C pick) (List.ofFn x) w = true → val C (List.ofFn x) w = true := by
  let D := repair G C pick
  let xs := List.ofFn x
  have hl : D.gates.length = C.gates.length := repair_len G C pick
  have hx : xs.length = n := List.length_ofFn
  have transfer (A B : Circuit) (heq : A.gates.length = C.gates.length)
      (heq' : B.gates.length = C.gates.length)
      (hkeep : ∀ j < C.gates.length, ¬ dirty G C j →
        gateAt A j = gateAt C j ∧ gateAt B j = gateAt C j)
      (hchange : ∀ j < C.gates.length, dirty G C j →
        val A xs (n + j) = true → val B xs (n + j) = true) :
      ∀ w, val A xs w = true → val B xs w = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro ht
      by_cases hi : w < n
      · rwa [val_input hx hi, ← val_input (C := A) hx hi]
      by_cases hj : w < n + C.gates.length
      · obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt hi)
        have hj' : j < C.gates.length := by omega
        by_cases hd : dirty G C j
        · exact hchange j hj' hd ht
        obtain ⟨ha, hb⟩ := hkeep j hj' hd
        have hjA : j < A.gates.length := by rwa [heq]
        have hjB : j < B.gates.length := by rwa [heq']
        rcases hC.1 _ (gateAt_mem hj') with op | op
        · rw [val_and hx hjA (by rwa [ha]), ha] at ht
          rw [val_and hx hjB (by rwa [hb]), hb]
          exact fun i hi => ⟨(ht i hi).1, ih i (ht i hi).1 (ht i hi).2⟩
        · rw [val_or hx hjA (by rwa [ha]), ha] at ht
          rw [val_or hx hjB (by rwa [hb]), hb]
          obtain ⟨i, hi, hlt, hv⟩ := ht
          exact ⟨i, hi, hlt, ih i hlt hv⟩
      · rw [val_ge hx (by omega)] at ht
        cases ht
  cases forward
  · exact transfer D C hl rfl (fun j hj hn => ⟨repair_kept pick hj hn, rfl⟩) hreplaced
  · exact transfer C D rfl hl (fun j hj hn => ⟨rfl, repair_kept pick hj hn⟩) hreplaced

lemma arbitrary_edge_repair {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) (hc : circuitFun n C = graphFun G ∅)
    (pick : ℕ → Fin n × Fin n)
    (hp : ∀ j < C.gates.length, dirty G C j → G.Adj (pick j).1 (pick j).2) :
    IsAO2 n (repair G C pick) ∧ (repair G C pick).size = C.size ∧
      (∀ x : Fin n → Bool, circuitFun n (repair G C pick) x = true → graphFun G ∅ x = true) ∧
      (∀ j < (repair G C pick).gates.length, (gateAt (repair G C pick) j).op = GateOp.and →
        BelowF G (repair G C pick) j) := by
  have hreflect (x : Fin n → Bool) (hn : graphFun G ∅ x ≠ true) (w : ℕ) :
      val (repair G C pick) (List.ofFn x) w = true → val C (List.ofFn x) w = true :=
    repair_compare hC pick x false (by
      intro j hj hd hval
      have hpv := (repair_replaced_val pick hj hd x).1 hval
      exact (hn (graph_true.2 ⟨_, _, hp j hj hd, hpv.1, hpv.2⟩)).elim) w
  refine ⟨repair_ao hC pick, ?_, ?_, ?_⟩
  · exact repair_len G C pick
  · intro x hx
    by_contra hn
    have h := hreflect x hn C.output hx
    change circuitFun n C x = true at h
    rw [hc] at h
    exact hn h
  · intro j hj hop x hv
    have hj' : j < C.gates.length := by rwa [repair_len] at hj
    by_cases hd : dirty G C j
    · have h := (repair_replaced_val pick hj' hd x).1 hv
      exact graph_true.2 ⟨_, _, hp j hj' hd, h.1, h.2⟩
    · have hop' : (gateAt C j).op = GateOp.and := by
        rwa [repair_kept pick hj' hd] at hop
      by_contra hn
      have hbelow : BelowF G C j := by
        by_contra h
        exact hd ⟨hop', h⟩
      exact hn (hbelow x (hreflect x hn (n + j) hv))

lemma arbitrary_edge_repair_exact_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) (hc : circuitFun n C = graphFun G ∅)
    (pick : ℕ → Fin n × Fin n)
    (hp : ∀ j < C.gates.length, dirty G C j → G.Adj (pick j).1 (pick j).2) :
    circuitFun n (repair G C pick) = graphFun G ∅ ↔
      ∀ u v : Fin n, G.Adj u v → circuitFun n (repair G C pick) (pairInput u v) = true := by
  obtain ⟨hD, _, hsound, _⟩ := arbitrary_edge_repair hC hc pick hp
  constructor
  · intro heq u v huv
    rw [heq]
    exact graph_true.mpr ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
  · intro hcover
    have hDM : Monotone2 (repair G C pick) := by
      intro g hg
      refine ⟨?_, ?_⟩
      · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hD.1 g hg
      · rw [hD.2.2 g hg]
    funext x
    apply Bool.eq_iff_iff.mpr
    refine ⟨hsound x, ?_⟩
    intro hx
    obtain ⟨u, v, huv, hxu, hxv⟩ := graph_true.mp hx
    apply pair_mono hDM (x := pairInput u v) (y := x) ?_
      (repair G C pick).output (hcover u v huv)
    intro i hi
    have hiuv : i = u ∨ i = v := by simpa [pairInput] using hi
    rcases hiuv with rfl | rfl
    · exact hxu
    · exact hxv

end Repair

namespace Labeling

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

lemma or_step_repair (pick : ℕ → Fin n × Fin n) {w w' : ℕ}
    (h : Frontier.OrStep n C w w') : Frontier.OrStep n (Repair.repair G C pick) w w' := by
  obtain ⟨j, hj, rfl, hop, hin, hlt⟩ := h
  have hkeep : gateAt (Repair.repair G C pick) j = gateAt C j :=
    Repair.repair_kept pick hj (fun hd => by cases hop.symm.trans hd.1)
  refine ⟨j, ?_, rfl, ?_, ?_, hlt⟩
  · rwa [Repair.repair_len]
  · rwa [hkeep]
  · rwa [hkeep]

lemma or_path_repair (pick : ℕ → Fin n × Fin n) {w w' : ℕ}
    (h : Relation.ReflTransGen (Frontier.OrStep n C) w w') :
    Relation.ReflTransGen (Frontier.OrStep n (Repair.repair G C pick)) w w' := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Relation.ReflTransGen.refl
  | head hstep _ ih => exact Relation.ReflTransGen.head (or_step_repair pick hstep) ih

lemma or_reaches_repair_value (pick : ℕ → Fin n × Fin n) {w j : ℕ} {x : Fin n → Bool}
    (hr : OrReaches n C w j)
    (hv : gateVal n (Repair.repair G C pick) j x = true) :
    Frontier.val (Repair.repair G C pick) (List.ofFn x) w = true :=
  Frontier.orStep_up (n := n) (by simp)
    (or_path_repair pick (Frontier.orReaches_reach j w hr).1) hv

lemma raw_side_repair_value (pick : ℕ → Fin n × Fin n) {a : ℕ} {b : Fin 2}
    {x : Fin n → Bool} {t : Fin n} (ht : t ∈ side (n := n) C a b) (hxt : x t = true) :
    Frontier.val (Repair.repair G C pick) (List.ofFn x) (opnd C a b) = true :=
  Frontier.reach_var_val x _ t (or_path_repair pick (Frontier.mem_orIn_reach t ht)) hxt

lemma junk_is_dirty {j : ℕ} (hj : j ∈ junk G C) : Repair.dirty G C j := by
  obtain ⟨_, hop, x, hx, hFx⟩ := Frontier.junkData hj
  refine ⟨hop, ?_⟩
  intro hbelow
  have h := hbelow x hx
  rw [hFx] at h
  cases h

lemma repair_accepts_frontier_certificate (hAO : IsAO2 n C) (pick : ℕ → Fin n × Fin n)
    {a : ℕ} {u v : Fin n} (ha : a ∈ tops G C) (hr : OrReaches n C C.output a)
    (hcert : ∀ b : Fin 2, (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
      ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧ s((pick j).1, (pick j).2) = s(u, v)) :
    circuitFun n (Repair.repair G C pick) (pairInput u v) = true := by
  have hD := Repair.repair_ao (G := G) hAO pick
  obtain ⟨haLen, haOp, haBelow⟩ := Frontier.topData ha
  have haKeep : gateAt (Repair.repair G C pick) a = gateAt C a :=
    Repair.repair_kept pick haLen (fun hd => hd.2 haBelow)
  have haDLen : a < (Repair.repair G C pick).gates.length := by rwa [Repair.repair_len]
  have hTop : gateVal n (Repair.repair G C pick) a (pairInput u v) = true := by
    apply (Frontier.andValOperands hD haDLen (by rwa [haKeep]) _).mpr
    intro b
    have hopnd : opnd (Repair.repair G C pick) a b = opnd C a b := by
      unfold opnd
      rw [haKeep]
    rw [hopnd]
    rcases hcert b with ⟨t, ht, hte⟩ | ⟨j, hj, hjr, hlabel⟩
    · apply raw_side_repair_value pick ht
      simpa [pairInput] using hte
    · have hjLen := (Frontier.junkData hj).1
      have hjTrue : gateVal n (Repair.repair G C pick) j (pairInput u v) = true := by
        apply (Repair.repair_replaced_val pick hjLen (junk_is_dirty hj) _).mpr
        rcases Sym2.eq_iff.mp hlabel with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> simp [h₁, h₂, pairInput]
      exact or_reaches_repair_value pick hjr hjTrue
  exact or_reaches_repair_value pick hr hTop

lemma repair_accepts_raw_top_pair (hAO : IsAO2 n C) (pick : ℕ → Fin n × Fin n)
    {a : ℕ} {u v : Fin n} (ha : a ∈ tops G C) (hr : OrReaches n C C.output a)
    (hu : u ∈ side (n := n) C a 0) (hv : v ∈ side (n := n) C a 1) :
    circuitFun n (Repair.repair G C pick) (pairInput u v) = true := by
  apply repair_accepts_frontier_certificate hAO pick ha hr
  intro b
  fin_cases b
  · exact Or.inl ⟨u, hu, Or.inl rfl⟩
  · exact Or.inl ⟨v, hv, Or.inr rfl⟩

lemma repair_exact_of_frontier_certificates (hAO : IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅) (pick : ℕ → Fin n × Fin n)
    (hp : ∀ j < C.gates.length, Repair.dirty G C j → G.Adj (pick j).1 (pick j).2)
    (hcover : ∀ u v : Fin n, G.Adj u v → ∃ a ∈ tops G C,
      OrReaches n C C.output a ∧
      ∀ b : Fin 2, (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
        ∃ j ∈ junk G C, OrReaches n C (opnd C a b) j ∧ s((pick j).1, (pick j).2) = s(u, v)) :
    IsAO2 n (Repair.repair G C pick) ∧ (Repair.repair G C pick).size = C.size ∧
      circuitFun n (Repair.repair G C pick) = graphFun G ∅ ∧
      (∀ j < (Repair.repair G C pick).gates.length,
        (gateAt (Repair.repair G C pick) j).op = GateOp.and → BelowF G (Repair.repair G C pick) j) := by
  obtain ⟨hD, hsize, _, hclean⟩ := Repair.arbitrary_edge_repair hAO hfun pick hp
  refine ⟨hD, hsize, ?_, hclean⟩
  apply (Repair.arbitrary_edge_repair_exact_iff hAO hfun pick hp).mpr
  intro u v huv
  obtain ⟨a, ha, hr, hcert⟩ := hcover u v huv
  exact repair_accepts_frontier_certificate hAO pick ha hr hcert

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

lemma erase_equal_circuit {n : ℕ} {C : Circuit} {k p : ℕ}
    (hk : k < C.gates.length) (hp : p < n + k)
    (heq : ∀ x : Fin n → Bool, val C (List.ofFn x) p = val C (List.ofFn x) (n + k)) :
    circuitFun n (eraseGate n C k p) = circuitFun n C := by
  funext x
  change val (eraseGate n C k p) (List.ofFn x) (eraseGate n C k p).output =
    val C (List.ofFn x) C.output
  rw [erase_output n C k p hk]
  exact erase_equal_wires hk hp (heq x) C.output

lemma erase_equal_preserves_clean {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {k p : ℕ} (hk : k < C.gates.length) (hp : p < n + k)
    (heq : ∀ x : Fin n → Bool, val C (List.ofFn x) p = val C (List.ofFn x) (n + k))
    (hclean : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → BelowF G C i) :
    ∀ i < (eraseGate n C k p).gates.length, (gateAt (eraseGate n C k p) i).op = GateOp.and →
      BelowF G (eraseGate n C k p) i := by
  have hlen := erase_length n C k p hk
  intro i hi hop x hx
  have hi' : i + 1 < C.gates.length := by omega
  by_cases hik : i < k
  · have hg : gateAt (eraseGate n C k p) i = gateAt C i := by
      rw [erase_gateAt n C k p i hk hi', if_pos hik]
    have hop' : (gateAt C i).op = GateOp.and := by rwa [hg] at hop
    apply hclean i (by omega) hop' x
    have hwire := erase_equal_wires hk hp (heq x) (n + i)
    rw [erase_redirect_lt n k p (n + i) (by omega)] at hwire
    change val C (List.ofFn x) (n + i) = true
    rw [← hwire]
    exact hx
  · have hg : gateAt (eraseGate n C k p) i = erase_rg (eraseRedirect n k p) (gateAt C (i + 1)) := by
      rw [erase_gateAt n C k p i hk hi', if_neg hik]
    have hop' : (gateAt C (i + 1)).op = GateOp.and := by
      rw [hg] at hop
      exact hop
    apply hclean (i + 1) hi' hop' x
    have hwire := erase_equal_wires hk hp (heq x) (n + (i + 1))
    have hr : eraseRedirect n k p (n + (i + 1)) = n + i := by
      rw [erase_redirect_gt n k p (n + (i + 1)) (by omega)]
      omega
    rw [hr] at hwire
    change val C (List.ofFn x) (n + (i + 1)) = true
    rw [← hwire]
    exact hx

lemma erase_equal_ao_clean {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {k p : ℕ} (hk : k < C.gates.length) (hp : p < n + k)
    (hAO : IsAO2 n C)
    (heq : ∀ x : Fin n → Bool, val C (List.ofFn x) p = val C (List.ofFn x) (n + k))
    (hclean : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and → BelowF G C i) :
    IsAO2 n (eraseGate n C k p) ∧ (eraseGate n C k p).size + 1 = C.size ∧
      circuitFun n (eraseGate n C k p) = circuitFun n C ∧
      (∀ i < (eraseGate n C k p).gates.length, (gateAt (eraseGate n C k p) i).op = GateOp.and →
        BelowF G (eraseGate n C k p) i) :=
  ⟨erase_isAO2 n C k p hk hp hAO, erase_size n C k p hk,
    erase_equal_circuit hk hp heq, erase_equal_preserves_clean hk hp heq hclean⟩

lemma duplicate_edge_label_values {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (pick : ℕ → Fin n × Fin n) {j k : ℕ}
    (hj : j < C.gates.length) (hk : k < C.gates.length)
    (hdj : Repair.dirty G C j) (hdk : Repair.dirty G C k)
    (hlabel : s((pick j).1, (pick j).2) = s((pick k).1, (pick k).2))
    (x : Fin n → Bool) :
    val (Repair.repair G C pick) (List.ofFn x) (n + j) =
      val (Repair.repair G C pick) (List.ofFn x) (n + k) := by
  apply Bool.eq_iff_iff.mpr
  change (Repair.val (Repair.repair G C pick) (List.ofFn x) (n + j) = true) ↔
    (Repair.val (Repair.repair G C pick) (List.ofFn x) (n + k) = true)
  rw [Repair.repair_replaced_val pick hj hdj x, Repair.repair_replaced_val pick hk hdk x]
  rcases Sym2.eq_iff.mp hlabel with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> simp [h₁, h₂, and_comm]

lemma merge_duplicate_edge_labels {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (pick : ℕ → Fin n × Fin n)
    (hpick : ∀ i < C.gates.length, Repair.dirty G C i → G.Adj (pick i).1 (pick i).2)
    {j k : ℕ} (hjk : j < k) (hk : k < C.gates.length)
    (hdj : Repair.dirty G C j) (hdk : Repair.dirty G C k)
    (hlabel : s((pick j).1, (pick j).2) = s((pick k).1, (pick k).2)) :
    let D := eraseGate n (Repair.repair G C pick) k (n + j)
    IsAO2 n D ∧ D.size + 1 = C.size ∧
      circuitFun n D = circuitFun n (Repair.repair G C pick) ∧
      (∀ i < D.gates.length, (gateAt D i).op = GateOp.and → BelowF G D i) := by
  intro D
  obtain ⟨hR, hsize, _, hclean⟩ := Repair.arbitrary_edge_repair hAO hfun pick hpick
  have hk' : k < (Repair.repair G C pick).gates.length := by rwa [Repair.repair_len]
  have hresult := erase_equal_ao_clean hk' (by omega : n + j < n + k) hR
    (duplicate_edge_label_values pick (by omega) hk hdj hdk hlabel) hclean
  refine ⟨hresult.1, ?_, hresult.2.2.1, hresult.2.2.2⟩
  exact hresult.2.1.trans hsize

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

lemma collapse_redundant_set {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (S : Finset ℕ) : ∀ C : Circuit, IsAO2 n C →
    (∀ i < C.gates.length, (gateAt C i).op = GateOp.and → BelowF G C i) →
    (∀ k ∈ S, k < C.gates.length ∧ ∃ p < n + k,
      ∀ x : Fin n → Bool, val C (List.ofFn x) p = val C (List.ofFn x) (n + k)) →
    ∃ D : Circuit, IsAO2 n D ∧
      (∀ i < D.gates.length, (gateAt D i).op = GateOp.and → BelowF G D i) ∧
      D.size + S.card = C.size ∧ circuitFun n D = circuitFun n C := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro C hAO hclean hred
    by_cases hzero : S = ∅
    · exact ⟨C, hAO, hclean, by simp [hzero], rfl⟩
    have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hzero
    let k := S.max' hne
    have hkS : k ∈ S := S.max'_mem hne
    obtain ⟨hk, p, hp, heq⟩ := hred k hkS
    let E := eraseGate n C k p
    obtain ⟨hEAO, hEsize, hEfun, hEclean⟩ := erase_equal_ao_clean hk hp hAO heq hclean
    have hremaining : ∀ i ∈ S.erase k, i < E.gates.length ∧ ∃ q < n + i,
        ∀ x : Fin n → Bool, val E (List.ofFn x) q = val E (List.ofFn x) (n + i) := by
      intro i hi
      obtain ⟨hik, hiS⟩ := Finset.mem_erase.mp hi
      have himax : i ≤ k := S.le_max' i hiS
      have hilt : i < k := by omega
      obtain ⟨_, q, hq, hqeq⟩ := hred i hiS
      refine ⟨?_, q, hq, ?_⟩
      · have hlen := erase_length n C k p hk
        change i < (eraseGate n C k p).gates.length
        omega
      · intro x
        change val (eraseGate n C k p) (List.ofFn x) q =
          val (eraseGate n C k p) (List.ofFn x) (n + i)
        rw [erase_lower_value hk (by simp) (by omega : q < n + k),
          erase_lower_value hk (by simp) (by omega : n + i < n + k)]
        exact hqeq x
    obtain ⟨D, hDAO, hDclean, hDsize, hDfun⟩ :=
      ih (S.erase k) (Finset.erase_ssubset hkS) E hEAO hEclean hremaining
    refine ⟨D, hDAO, hDclean, ?_, hDfun.trans hEfun⟩
    have hcard := Finset.card_erase_add_one hkS
    change E.size + 1 = C.size at hEsize
    omega

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

lemma collapse_labeled_dirty_set {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (pick : ℕ → Fin n × Fin n)
    (hpick : ∀ i < C.gates.length, Repair.dirty G C i → G.Adj (pick i).1 (pick i).2)
    (T : Finset ℕ) (hT : ∀ k ∈ T, k < C.gates.length ∧ Repair.dirty G C k) :
    ∃ D : Circuit, IsAO2 n D ∧
      (∀ i < D.gates.length, (gateAt D i).op = GateOp.and → BelowF G D i) ∧
      D.size + T.card = C.size + (T.image fun k => s((pick k).1, (pick k).2)).card ∧
      circuitFun n D = circuitFun n (Repair.repair G C pick) := by
  classical
  let label : ℕ → Sym2 (Fin n) := fun k => s((pick k).1, (pick k).2)
  obtain ⟨R, hRT, hRcard, hrepresent⟩ := minimum_label_representatives T label
  let S := T \ R
  obtain ⟨hRAO, hRsize, _, hRclean⟩ := Repair.arbitrary_edge_repair hAO hfun pick hpick
  have hred : ∀ k ∈ S, k < (Repair.repair G C pick).gates.length ∧ ∃ p < n + k,
      ∀ x : Fin n → Bool, val (Repair.repair G C pick) (List.ofFn x) p =
        val (Repair.repair G C pick) (List.ofFn x) (n + k) := by
    intro k hk
    have hkT : k ∈ T := (Finset.mem_sdiff.mp hk).1
    obtain ⟨j, hjT, hjk, hlabel⟩ := hrepresent k hk
    refine ⟨?_, n + j, by omega, ?_⟩
    · rw [Repair.repair_len]
      exact (hT k hkT).1
    · intro x
      exact duplicate_edge_label_values pick (hT j hjT).1 (hT k hkT).1
        (hT j hjT).2 (hT k hkT).2 hlabel x
  obtain ⟨D, hDAO, hDclean, hDsize, hDfun⟩ :=
    collapse_redundant_set S (Repair.repair G C pick) hRAO hRclean hred
  refine ⟨D, hDAO, hDclean, ?_, hDfun⟩
  have hcard : S.card + R.card = T.card := Finset.card_sdiff_add_card_eq_card hRT
  change D.size + T.card = C.size + (T.image label).card
  omega

lemma collapse_all_dirty_labels {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (pick : ℕ → Fin n × Fin n)
    (hpick : ∀ i < C.gates.length, Repair.dirty G C i → G.Adj (pick i).1 (pick i).2) :
    let T := @Finset.filter ℕ (Repair.dirty G C)
      (fun k => Classical.propDecidable (Repair.dirty G C k)) (Finset.range C.gates.length)
    ∃ D : Circuit, IsAO2 n D ∧
      (∀ i < D.gates.length, (gateAt D i).op = GateOp.and → BelowF G D i) ∧
      D.size + T.card = C.size + (T.image fun k => s((pick k).1, (pick k).2)).card ∧
      circuitFun n D = circuitFun n (Repair.repair G C pick) := by
  classical
  apply collapse_labeled_dirty_set hAO hfun pick hpick
    ((Finset.range C.gates.length).filter (Repair.dirty G C))
  intro k hk
  obtain ⟨hk, hd⟩ := Finset.mem_filter.mp hk
  exact ⟨Finset.mem_range.mp hk, hd⟩

end Duplicate


namespace Completion
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

def addEdge {n : ℕ} (C : Circuit) (u v : Fin n) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.and, [u.val, v.val]⟩,
    ⟨GateOp.or, [C.output, n + C.gates.length]⟩], n + C.gates.length + 1⟩

lemma addEdge_size {n : ℕ} (C : Circuit) (u v : Fin n) :
    (addEdge C u v).size = C.size + 2 := by
  simp [addEdge, Circuit.size]

lemma addEdge_output {n : ℕ} (C : Circuit) (u v : Fin n) :
    (addEdge C u v).output < n + (addEdge C u v).gates.length := by
  simp only [addEdge, List.length_append, List.length_cons, List.length_nil]
  omega

lemma addEdge_gate_old {n : ℕ} (C : Circuit) (u v : Fin n)
    {j : ℕ} (hj : j < C.gates.length) : gateAt (addEdge C u v) j = gateAt C j := by
  simp [gateAt, addEdge, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

lemma addEdge_gate_new {n : ℕ} (C : Circuit) (u v : Fin n) :
    gateAt (addEdge C u v) C.gates.length = ⟨GateOp.and, [u.val, v.val]⟩ ∧
    gateAt (addEdge C u v) (C.gates.length + 1) =
      ⟨GateOp.or, [C.output, n + C.gates.length]⟩ := by
  simp [gateAt, addEdge, List.getD_eq_getElem?_getD]

lemma addEdge_ao {n : ℕ} (C : Circuit) (u v : Fin n) (hAO : IsAO2 n C)
    (ho : C.output < n + C.gates.length) : IsAO2 n (addEdge C u v) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [addEdge, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact hAO.1 g hg
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro j hj i hi
    have hj' : j < C.gates.length + 2 := by simpa [addEdge] using hj
    by_cases hlt : j < C.gates.length
    · rw [addEdge_gate_old C u v hlt] at hi
      exact hAO.2.1 j hlt i hi
    · have he : j = C.gates.length ∨ j = C.gates.length + 1 := by omega
      rcases he with rfl | rfl
      · rw [(addEdge_gate_new C u v).1] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> omega
      · rw [(addEdge_gate_new C u v).2] at hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl <;> omega
  · intro g hg
    simp only [addEdge, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact hAO.2.2 g hg
    · rfl
    · rfl

lemma addEdge_val_old {n : ℕ} (C : Circuit) (u v : Fin n) (x : Fin n → Bool)
    {i : ℕ} (hi : i < n + C.gates.length) :
    val (addEdge C u v) (List.ofFn x) i = val C (List.ofFn x) i := by
  change (W (C.gates ++ _) (List.ofFn x)).getD i false = _
  rw [W_append, W_prefix]
  · rfl
  · simpa [W_length] using hi

lemma addEdge_val_new {n : ℕ} (C : Circuit) (u v : Fin n) (x : Fin n → Bool) :
    gateVal n (addEdge C u v) C.gates.length x = (x u && x v) := by
  have hj : C.gates.length < (addEdge C u v).gates.length := by simp [addEdge]
  change val (addEdge C u v) (List.ofFn x) (n + C.gates.length) = _
  rw [val_gate (by simp) hj, (addEdge_gate_new C u v).1]
  have hu : u.val < n + C.gates.length := by omega
  have hv : v.val < n + C.gates.length := by omega
  simp [GateOp.eval, hu, hv, val_ofFn]

lemma addEdge_fun {n : ℕ} (C : Circuit) (u v : Fin n)
    (ho : C.output < n + C.gates.length) (x : Fin n → Bool) :
    circuitFun n (addEdge C u v) x = (circuitFun n C x || (x u && x v)) := by
  have hj : C.gates.length + 1 < (addEdge C u v).gates.length := by simp [addEdge]
  change val (addEdge C u v) (List.ofFn x) (n + C.gates.length + 1) = _
  rw [show n + C.gates.length + 1 = n + (C.gates.length + 1) by omega,
    val_gate (by simp) hj, (addEdge_gate_new C u v).2]
  have ho' : C.output < n + (C.gates.length + 1) := by omega
  have hl : n + C.gates.length < n + (C.gates.length + 1) := by omega
  simp only [List.map_cons, List.map_nil, ite_eq_left ho', ite_eq_left hl, GateOp.eval,
    List.any_cons, List.any_nil, id_eq, Bool.or_false]
  rw [addEdge_val_old C u v x ho]
  change (circuitFun n C x || gateVal n (addEdge C u v) C.gates.length x) = _
  rw [addEdge_val_new]

lemma addEdge_clean {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (u v : Fin n) (he : G.Adj u v)
    (hc : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) :
    ∀ j < (addEdge C u v).gates.length,
      (gateAt (addEdge C u v) j).op = GateOp.and → BelowF G (addEdge C u v) j := by
  intro j hj hop x hx
  have hj' : j < C.gates.length + 2 := by simpa [addEdge] using hj
  by_cases hlt : j < C.gates.length
  · rw [addEdge_gate_old C u v hlt] at hop
    apply hc j hlt hop x
    change val C (List.ofFn x) (n+j) = true
    change val (addEdge C u v) (List.ofFn x) (n+j) = true at hx
    rwa [addEdge_val_old C u v x (by omega)] at hx
  · have heq : j = C.gates.length ∨ j = C.gates.length + 1 := by omega
    rcases heq with rfl | rfl
    · rw [addEdge_val_new] at hx
      obtain ⟨hu, hv⟩ : x u = true ∧ x v = true := by simpa using hx
      exact Repair.graph_true.mpr ⟨u, v, he, hu, hv⟩
    · rw [(addEdge_gate_new C u v).2] at hop
      cases hop


def addEdges {n : ℕ} (C : Circuit) : List (Fin n × Fin n) → Circuit
  | [] => C
  | e :: es => addEdges (addEdge C e.1 e.2) es

lemma addEdges_size {n : ℕ} (C : Circuit) (es : List (Fin n × Fin n)) :
    (addEdges C es).size = C.size + 2 * es.length := by
  induction es generalizing C with
  | nil => simp [addEdges]
  | cons e es ih =>
    rw [addEdges, ih, addEdge_size, List.length_cons]
    omega

lemma addEdges_ao_output {n : ℕ} (C : Circuit) (es : List (Fin n × Fin n))
    (hAO : IsAO2 n C) (ho : C.output < n + C.gates.length) :
    IsAO2 n (addEdges C es) ∧ (addEdges C es).output < n + (addEdges C es).gates.length := by
  induction es generalizing C with
  | nil => exact ⟨hAO, ho⟩
  | cons e es ih =>
    exact ih (addEdge C e.1 e.2) (addEdge_ao C e.1 e.2 hAO ho) (addEdge_output C e.1 e.2)

lemma addEdges_fun {n : ℕ} (C : Circuit) (es : List (Fin n × Fin n))
    (ho : C.output < n + C.gates.length) (x : Fin n → Bool) :
    circuitFun n (addEdges C es) x = (circuitFun n C x || es.any (fun e => x e.1 && x e.2)) := by
  induction es generalizing C with
  | nil => simp [addEdges]
  | cons e es ih =>
    rw [addEdges, ih (addEdge C e.1 e.2) (addEdge_output C e.1 e.2),
      addEdge_fun C e.1 e.2 ho]
    simp [Bool.or_assoc]

lemma addEdges_clean {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (es : List (Fin n × Fin n))
    (he : ∀ e ∈ es, G.Adj e.1 e.2)
    (hc : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) :
    ∀ j < (addEdges C es).gates.length,
      (gateAt (addEdges C es) j).op = GateOp.and → BelowF G (addEdges C es) j := by
  induction es generalizing C with
  | nil => exact hc
  | cons e es ih =>
    apply ih (addEdge C e.1 e.2)
    · exact fun e' he' => he e' (List.mem_cons_of_mem e he')
    · exact addEdge_clean G C e.1 e.2 (he e (by simp)) hc

lemma complete_missing_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (es : List (Fin n × Fin n))
    (hAO : IsAO2 n C) (ho : C.output < n + C.gates.length)
    (he : ∀ e ∈ es, G.Adj e.1 e.2)
    (hsafe : ∀ x, circuitFun n C x = true → graphFun G ∅ x = true)
    (hc : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j)
    (hcover : ∀ u v : Fin n, G.Adj u v → circuitFun n C (pairInput u v) = true ∨
      ∃ e ∈ es, s(e.1, e.2) = s(u, v)) :
    IsAO2 n (addEdges C es) ∧
      (addEdges C es).size = C.size + 2 * es.length ∧
      circuitFun n (addEdges C es) = graphFun G ∅ ∧
      (∀ j < (addEdges C es).gates.length,
        (gateAt (addEdges C es) j).op = GateOp.and → BelowF G (addEdges C es) j) := by
  have hD := (addEdges_ao_output C es hAO ho).1
  refine ⟨hD, addEdges_size C es, ?_, addEdges_clean G C es he hc⟩
  apply eq_graphFun_of_boundary G _ hD
  · intro u v huv
    rw [addEdges_fun C es ho]
    rcases hcover u v huv with h | ⟨e, heMem, hEq⟩
    · simp [h]
    · have hpair : pairInput u v e.1 = true ∧ pairInput u v e.2 = true := by
        rcases Sym2.eq_iff.mp hEq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> simp [h₁, h₂, pairInput]
      have hAny : es.any (fun e => pairInput u v e.1 && pairInput u v e.2) = true := by
        apply List.any_eq_true.mpr
        exact ⟨e, heMem, by simp [hpair.1, hpair.2]⟩
      simp [hAny]
  · intro x hx
    apply Bool.eq_false_iff.mpr
    intro h
    rw [addEdges_fun C es ho] at h
    have hF : graphFun G ∅ x = true := by
      rcases Bool.or_eq_true_iff.mp h with h | h
      · exact hsafe x h
      · obtain ⟨e, heMem, heVal⟩ := List.any_eq_true.mp h
        obtain ⟨hu, hv⟩ : x e.1 = true ∧ x e.2 = true := by simpa using heVal
        exact Repair.graph_true.mpr ⟨e.1, e.2, he e heMem, hu, hv⟩
    rw [hx.1] at hF
    cases hF


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


namespace Cost
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma repair_merge_complete {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (ho : C.output < n + C.gates.length) (pick : ℕ → Fin n × Fin n)
    (hpick : ∀ i < C.gates.length, Repair.dirty G C i → G.Adj (pick i).1 (pick i).2)
    (T : Finset ℕ) (hT : ∀ k ∈ T, k < C.gates.length ∧ Repair.dirty G C k)
    (es : List (Fin n × Fin n)) (he : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcover : ∀ u v : Fin n, G.Adj u v →
      circuitFun n (Repair.repair G C pick) (pairInput u v) = true ∨
      ∃ e ∈ es, s(e.1, e.2) = s(u, v)) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
      (∀ i < D.gates.length, (gateAt D i).op = GateOp.and → BelowF G D i) ∧
      D.size + T.card = C.size + (T.image fun k => s((pick k).1, (pick k).2)).card + 2 * es.length := by
  obtain ⟨R, hRAO, hRclean, hRsize, hRfun⟩ :=
    Duplicate.collapse_labeled_dirty_set hAO hfun pick hpick T hT
  obtain ⟨hPAO, _, hPsafe, _⟩ := Repair.arbitrary_edge_repair hAO hfun pick hpick
  have hpo : (Repair.repair G C pick).output < n + (Repair.repair G C pick).gates.length := by
    change C.output < n + (Repair.repair G C pick).gates.length
    rwa [Repair.repair_len]
  have hRtrue : circuitFun n R (fun _ => true) = true := by
    rw [hRfun]
    exact Completion.ao2_all_true (Repair.repair G C pick) hPAO _ hpo
  have hRo := Completion.output_valid_of_true R (fun _ => true) hRtrue
  have hRsafe : ∀ x, circuitFun n R x = true → graphFun G ∅ x = true := by
    intro x hx
    rw [hRfun] at hx
    exact hPsafe x hx
  have hRcover : ∀ u v : Fin n, G.Adj u v → circuitFun n R (pairInput u v) = true ∨
      ∃ e ∈ es, s(e.1, e.2) = s(u, v) := by
    intro u v huv
    rw [hRfun]
    exact hcover u v huv
  obtain ⟨hDAO, hDsize, hDfun, hDclean⟩ :=
    Completion.complete_missing_edges G R es hRAO hRo he hRsafe hRclean hRcover
  refine ⟨Completion.addEdges R es, hDAO, hDfun, hDclean, ?_⟩
  omega

lemma repair_merge_complete_no_larger {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (ho : C.output < n + C.gates.length) (pick : ℕ → Fin n × Fin n)
    (hpick : ∀ i < C.gates.length, Repair.dirty G C i → G.Adj (pick i).1 (pick i).2)
    (T : Finset ℕ) (hT : ∀ k ∈ T, k < C.gates.length ∧ Repair.dirty G C k)
    (es : List (Fin n × Fin n)) (he : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcover : ∀ u v : Fin n, G.Adj u v →
      circuitFun n (Repair.repair G C pick) (pairInput u v) = true ∨
      ∃ e ∈ es, s(e.1, e.2) = s(u, v))
    (hcost : (T.image fun k => s((pick k).1, (pick k).2)).card + 2 * es.length ≤ T.card) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
      ∀ i < D.gates.length, (gateAt D i).op = GateOp.and → BelowF G D i := by
  obtain ⟨D, hDAO, hDfun, hDclean, hDsize⟩ := repair_merge_complete hAO hfun ho pick hpick T hT es he hcover
  exact ⟨D, hDAO, hDfun, by omega, hDclean⟩

end Cost


namespace Assignment
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma labels_of_disjoint_resources {α : Type*} [DecidableEq α]
    (E : Finset α) (hE : E.Nonempty) (H : α → Finset ℕ)
    (hdisjoint : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → Disjoint (H e) (H f)) :
    ∃ pick : ℕ → α, (∀ j, pick j ∈ E) ∧ ∀ e ∈ E, ∀ j ∈ H e, pick j = e := by
  classical
  let pick : ℕ → α := fun j => if h : ∃ e ∈ E, j ∈ H e then Classical.choose h else hE.choose
  have hmem : ∀ j, pick j ∈ E := by
    intro j
    dsimp [pick]
    split_ifs with h
    · exact (Classical.choose_spec h).1
    · exact hE.choose_spec
  refine ⟨pick, hmem, ?_⟩
  intro e he j hj
  have h : ∃ e ∈ E, j ∈ H e := ⟨e, he, hj⟩
  have hpick : pick j = Classical.choose h := by simp [pick, h]
  rw [hpick]
  by_contra hne
  have hd := hdisjoint (Classical.choose h) (Classical.choose_spec h).1 e he hne
  exact Finset.disjoint_left.mp hd (Classical.choose_spec h).2 hj

lemma repair_labels_of_disjoint_certificates {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (E : Finset (Fin n × Fin n)) (hE : E.Nonempty)
    (he : ∀ e ∈ E, G.Adj e.1 e.2) (H : (Fin n × Fin n) → Finset ℕ)
    (hdisjoint : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → Disjoint (H e) (H f))
    (hcert : ∀ e ∈ E, ∃ a ∈ tops G C, OrReaches n C C.output a ∧
      ∀ b : Fin 2, (∃ t ∈ side (n := n) C a b, t = e.1 ∨ t = e.2) ∨
        ∃ j ∈ H e, j ∈ junk G C ∧ OrReaches n C (opnd C a b) j) :
    ∃ pick : ℕ → Fin n × Fin n,
      (∀ j, G.Adj (pick j).1 (pick j).2) ∧
      (∀ e ∈ E, circuitFun n (Repair.repair G C pick) (pairInput e.1 e.2) = true) ∧
      ∀ T : Finset ℕ, (T.image fun k => s((pick k).1, (pick k).2)).card ≤ E.card := by
  classical
  obtain ⟨pick, hpick, hlabels⟩ := labels_of_disjoint_resources E hE H hdisjoint
  refine ⟨pick, fun j => he (pick j) (hpick j), ?_, ?_⟩
  · intro e heE
    obtain ⟨a, ha, hr, hab⟩ := hcert e heE
    apply Labeling.repair_accepts_frontier_certificate hAO pick ha hr
    intro b
    rcases hab b with h | ⟨j, hjH, hj, hjr⟩
    · exact Or.inl h
    · exact Or.inr ⟨j, hj, hjr, by rw [hlabels e heE j hjH]⟩
  · intro T
    have hsub : (T.image fun k => s((pick k).1, (pick k).2)) ⊆
        E.image (fun e => s(e.1, e.2)) := by
      intro e heT
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp heT
      exact Finset.mem_image.mpr ⟨pick j, hpick j, rfl⟩
    exact (Finset.card_le_card hsub).trans Finset.card_image_le

lemma clean_repair_of_disjoint_certificates {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (ho : C.output < n + C.gates.length)
    (E : Finset (Fin n × Fin n)) (hE : E.Nonempty) (he : ∀ e ∈ E, G.Adj e.1 e.2)
    (H : (Fin n × Fin n) → Finset ℕ)
    (hdisjoint : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → Disjoint (H e) (H f))
    (hcert : ∀ e ∈ E, ∃ a ∈ tops G C, OrReaches n C C.output a ∧
      ∀ b : Fin 2, (∃ t ∈ side (n := n) C a b, t = e.1 ∨ t = e.2) ∨
        ∃ j ∈ H e, j ∈ junk G C ∧ OrReaches n C (opnd C a b) j)
    (T : Finset ℕ) (hT : ∀ k ∈ T, k < C.gates.length ∧ Repair.dirty G C k)
    (es : List (Fin n × Fin n)) (hes : ∀ e ∈ es, G.Adj e.1 e.2)
    (hcover : ∀ u v : Fin n, G.Adj u v →
      (∃ a ∈ tops G C, OrReaches n C C.output a ∧
        ((u ∈ side (n := n) C a 0 ∧ v ∈ side (n := n) C a 1) ∨
         (v ∈ side (n := n) C a 0 ∧ u ∈ side (n := n) C a 1))) ∨
      (∃ e ∈ E, s(e.1, e.2) = s(u, v)) ∨ (∃ e ∈ es, s(e.1, e.2) = s(u, v)))
    (hcost : E.card + 2 * es.length ≤ T.card) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
      ∀ i < D.gates.length, (gateAt D i).op = GateOp.and → BelowF G D i := by
  classical
  obtain ⟨pick, hpick, haccept, hcard⟩ := repair_labels_of_disjoint_certificates hAO E hE he H hdisjoint hcert
  apply Cost.repair_merge_complete_no_larger hAO hfun ho pick (fun j _ _ => hpick j) T hT es hes
  · intro u v huv
    rcases hcover u v huv with ⟨a, ha, hr, hraw⟩ | ⟨e, heE, heq⟩ | hmissing
    · apply Or.inl
      rcases hraw with ⟨hu, hv⟩ | ⟨hv, hu⟩
      · exact Labeling.repair_accepts_raw_top_pair hAO pick ha hr hu hv
      · have h := Labeling.repair_accepts_raw_top_pair hAO pick ha hr hv hu
        have hswap : pairInput v u = pairInput u v := by funext x; simp [pairInput, or_comm]
        rwa [hswap] at h
    · apply Or.inl
      have hv := haccept e heE
      have hinput : pairInput e.1 e.2 = pairInput u v := by
        funext x
        rcases Sym2.eq_iff.mp heq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;>
          simp [pairInput, h₁, h₂, or_comm]
      rwa [hinput] at hv
    · exact Or.inr hmissing
  · have hb := hcard T
    omega

end Assignment

namespace StarCompletion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

def appendBinary (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨op, [a, b]⟩], n + C.gates.length⟩

lemma appendBinary_size (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    (appendBinary n C op a b).size = C.size + 1 := by simp [appendBinary, Circuit.size]

lemma appendBinary_output (n : ℕ) (C : Circuit) (op : GateOp) (a b : ℕ) :
    (appendBinary n C op a b).output < n + (appendBinary n C op a b).gates.length := by
  simp [appendBinary]

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

def orTail {n : ℕ} (C : Circuit) : List (Fin n) → Circuit
  | [] => C
  | v :: vs => orTail (appendBinary n C GateOp.or C.output v.val) vs

lemma orTail_size {n : ℕ} (C : Circuit) (vs : List (Fin n)) :
    (orTail C vs).size = C.size + vs.length := by
  induction vs generalizing C with
  | nil => simp [orTail]
  | cons v vs ih => rw [orTail, ih, appendBinary_size, List.length_cons]; omega

lemma orTail_ao_output {n : ℕ} (C : Circuit) (vs : List (Fin n))
    (hAO : IsAO2 n C) (ho : C.output < n + C.gates.length) :
    IsAO2 n (orTail C vs) ∧ (orTail C vs).output < n + (orTail C vs).gates.length := by
  induction vs generalizing C with
  | nil => exact ⟨hAO, ho⟩
  | cons v vs ih =>
    exact ih _ (appendBinary_ao n C GateOp.or C.output v.val hAO (Or.inr rfl) ho (by omega))
      (appendBinary_output n C GateOp.or C.output v.val)

lemma orTail_fun {n : ℕ} (C : Circuit) (vs : List (Fin n))
    (ho : C.output < n + C.gates.length) (x : Fin n → Bool) :
    circuitFun n (orTail C vs) x = (circuitFun n C x || vs.any x) := by
  induction vs generalizing C with
  | nil => simp [orTail]
  | cons v vs ih =>
    rw [orTail, ih _ (appendBinary_output n C GateOp.or C.output v.val),
      appendBinary_fun C GateOp.or C.output v.val ho (by omega)]
    rw [val_ofFn]
    simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    change ((circuitFun n C x || x v) || vs.any x) = (circuitFun n C x || (x v || vs.any x))
    exact Bool.or_assoc _ _ _

lemma orTail_val_old {n : ℕ} (C : Circuit) (vs : List (Fin n))
    (x : Fin n → Bool) {i : ℕ} (hi : i < n + C.gates.length) :
    val (orTail C vs) (List.ofFn x) i = val C (List.ofFn x) i := by
  induction vs generalizing C with
  | nil => rfl
  | cons v vs ih =>
    rw [orTail, ih _ (by simp only [appendBinary, List.length_append, List.length_singleton]; omega)]
    exact appendBinary_val_old C GateOp.or C.output v.val x hi

lemma orTail_clean {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (vs : List (Fin n)) (ho : C.output < n + C.gates.length)
    (hc : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) :
    ∀ j < (orTail C vs).gates.length, (gateAt (orTail C vs) j).op = GateOp.and → BelowF G (orTail C vs) j := by
  induction vs generalizing C with
  | nil => exact hc
  | cons v vs ih =>
    apply ih _ (appendBinary_output n C GateOp.or C.output v.val)
    exact appendBinary_clean G C GateOp.or C.output v.val ho (by omega) hc (by intro h; cases h)

def appendStarHead {n : ℕ} (C : Circuit) (c v : Fin n) (vs : List (Fin n)) : Circuit :=
  let B := orTail ⟨C.gates, v.val⟩ vs
  let A := appendBinary n B GateOp.and c.val B.output
  appendBinary n A GateOp.or C.output A.output

lemma appendStarHead_size {n : ℕ} (C : Circuit) (c v : Fin n) (vs : List (Fin n)) :
    (appendStarHead C c v vs).size = C.size + vs.length + 2 := by
  dsimp only [appendStarHead]
  rw [appendBinary_size, appendBinary_size, orTail_size]
  change C.size + vs.length + 1 + 1 = C.size + vs.length + 2
  omega

lemma appendStarHead_spec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (c v : Fin n) (vs : List (Fin n))
    (hAO : IsAO2 n C) (ho : C.output < n + C.gates.length)
    (he : ∀ w ∈ v :: vs, G.Adj c w)
    (hc : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) :
    IsAO2 n (appendStarHead C c v vs) ∧
      (appendStarHead C c v vs).output < n + (appendStarHead C c v vs).gates.length ∧
      (∀ x : Fin n → Bool, circuitFun n (appendStarHead C c v vs) x =
        (circuitFun n C x || (x c && (v :: vs).any x))) ∧
      (∀ j < (appendStarHead C c v vs).gates.length,
        (gateAt (appendStarHead C c v vs) j).op = GateOp.and → BelowF G (appendStarHead C c v vs) j) := by
  let S : Circuit := ⟨C.gates, v.val⟩
  let B := orTail S vs
  let A := appendBinary n B GateOp.and c.val B.output
  have hS : IsAO2 n S := hAO
  have hSo : S.output < n + S.gates.length := by change v.val < n + C.gates.length; omega
  have hB := orTail_ao_output S vs hS hSo
  have hBlen : B.gates.length = C.gates.length + vs.length := orTail_size S vs
  have hcB : c.val < n + B.gates.length := by omega
  have hoB : C.output < n + B.gates.length := by omega
  have hBfun (x : Fin n → Bool) : circuitFun n B x = (v :: vs).any x := by
    rw [orTail_fun S vs hSo]
    change (val C (List.ofFn x) v.val || vs.any x) = _
    rw [val_ofFn]
    rfl
  have hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j :=
    orTail_clean G S vs hSo hc
  have hAOA : IsAO2 n A := appendBinary_ao n B GateOp.and c.val B.output hB.1 (Or.inl rfl) hcB hB.2
  have hAo : A.output < n + A.gates.length := appendBinary_output n B GateOp.and c.val B.output
  have hoA : C.output < n + A.gates.length := by
    change C.output < n + (appendBinary n B GateOp.and c.val B.output).gates.length
    simp only [appendBinary, List.length_append, List.length_singleton]
    omega
  have hAfun (x : Fin n → Bool) : circuitFun n A x = (x c && (v :: vs).any x) := by
    rw [appendBinary_fun B GateOp.and c.val B.output hcB hB.2, val_ofFn]
    simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    change (x c && circuitFun n B x) = _
    rw [hBfun]
  have hAclean : ∀ j < A.gates.length, (gateAt A j).op = GateOp.and → BelowF G A j := by
    apply appendBinary_clean G B GateOp.and c.val B.output hcB hB.2 hBclean
    intro _ x hx
    have hAx : circuitFun n A x = true := by
      rw [appendBinary_fun B GateOp.and c.val B.output hcB hB.2]
      exact hx
    rw [hAfun] at hAx
    obtain ⟨hxc, hAny⟩ : x c = true ∧ (v :: vs).any x = true := by simpa using hAx
    obtain ⟨w, hw, hxw⟩ := List.any_eq_true.mp hAny
    exact Repair.graph_true.mpr ⟨c, w, he w hw, hxc, hxw⟩
  refine ⟨appendBinary_ao n A GateOp.or C.output A.output hAOA (Or.inr rfl) hoA hAo,
    appendBinary_output n A GateOp.or C.output A.output, ?_, ?_⟩
  · intro x
    change circuitFun n (appendBinary n A GateOp.or C.output A.output) x = _
    rw [appendBinary_fun A GateOp.or C.output A.output hoA hAo]
    simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false]
    have hOld : val A (List.ofFn x) C.output = val C (List.ofFn x) C.output := by
      rw [appendBinary_val_old B GateOp.and c.val B.output x hoB, orTail_val_old S vs x ho]
      rfl
    rw [hOld]
    change (circuitFun n C x || circuitFun n A x) = _
    rw [hAfun]
    simp only [List.any_cons]
  · exact appendBinary_clean G A GateOp.or C.output A.output hoA hAo hAclean (by intro h; cases h)

def appendStar {n : ℕ} (C : Circuit) (c : Fin n) : List (Fin n) → Circuit
  | [] => C
  | v :: vs => appendStarHead C c v vs

lemma appendStar_spec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (c : Fin n) (vs : List (Fin n)) (hne : vs ≠ [])
    (hAO : IsAO2 n C) (ho : C.output < n + C.gates.length)
    (he : ∀ w ∈ vs, G.Adj c w)
    (hc : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) :
    IsAO2 n (appendStar C c vs) ∧
      (appendStar C c vs).output < n + (appendStar C c vs).gates.length ∧
      (appendStar C c vs).size = C.size + vs.length + 1 ∧
      (∀ x : Fin n → Bool, circuitFun n (appendStar C c vs) x =
        (circuitFun n C x || (x c && vs.any x))) ∧
      (∀ j < (appendStar C c vs).gates.length,
        (gateAt (appendStar C c vs) j).op = GateOp.and → BelowF G (appendStar C c vs) j) := by
  cases vs with
  | nil => exact False.elim (hne rfl)
  | cons v vs =>
    obtain ⟨hD, hDo, hDf, hDc⟩ := appendStarHead_spec G C c v vs hAO ho he hc
    refine ⟨hD, hDo, ?_, hDf, hDc⟩
    rw [appendStar, appendStarHead_size, List.length_cons]
    omega

def appendStars {n : ℕ} (C : Circuit) : List (Fin n × List (Fin n)) → Circuit
  | [] => C
  | s :: ss => appendStars (appendStar C s.1 s.2) ss

lemma appendStars_spec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ss : List (Fin n × List (Fin n)))
    (hne : ∀ s ∈ ss, s.2 ≠ [])
    (hAO : IsAO2 n C) (ho : C.output < n + C.gates.length)
    (he : ∀ s ∈ ss, ∀ w ∈ s.2, G.Adj s.1 w)
    (hc : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) :
    IsAO2 n (appendStars C ss) ∧
      (appendStars C ss).output < n + (appendStars C ss).gates.length ∧
      (appendStars C ss).size = C.size + (ss.map fun s => s.2.length + 1).sum ∧
      (∀ x : Fin n → Bool, circuitFun n (appendStars C ss) x =
        (circuitFun n C x || ss.any (fun s => x s.1 && s.2.any x))) ∧
      (∀ j < (appendStars C ss).gates.length,
        (gateAt (appendStars C ss) j).op = GateOp.and → BelowF G (appendStars C ss) j) := by
  induction ss generalizing C with
  | nil =>
    refine ⟨hAO, ho, by simp [appendStars], ?_, hc⟩
    intro x
    simp [appendStars]
  | cons s ss ih =>
    obtain ⟨hS, hSo, hSsize, hSf, hSc⟩ := appendStar_spec G C s.1 s.2 (hne s (by simp))
      hAO ho (he s (by simp)) hc
    obtain ⟨hD, hDo, hDsize, hDf, hDc⟩ := ih (appendStar C s.1 s.2)
      (fun t ht => hne t (List.mem_cons_of_mem _ ht)) hS hSo
      (fun t ht => he t (List.mem_cons_of_mem _ ht)) hSc
    refine ⟨hD, hDo, ?_, ?_, hDc⟩
    · rw [appendStars, hDsize, hSsize, List.map_cons, List.sum_cons]
      omega
    · intro x
      rw [appendStars, hDf, hSf]
      simp only [List.any_cons, Bool.or_assoc]

lemma complete_missing_stars {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (ss : List (Fin n × List (Fin n)))
    (hne : ∀ s ∈ ss, s.2 ≠ [])
    (hAO : IsAO2 n C) (ho : C.output < n + C.gates.length)
    (he : ∀ s ∈ ss, ∀ w ∈ s.2, G.Adj s.1 w)
    (hsafe : ∀ x, circuitFun n C x = true → graphFun G ∅ x = true)
    (hc : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j)
    (hcover : ∀ u v : Fin n, G.Adj u v → circuitFun n C (pairInput u v) = true ∨
      ∃ s ∈ ss, ∃ w ∈ s.2, s(s.1, w) = s(u, v)) :
    IsAO2 n (appendStars C ss) ∧
      (appendStars C ss).output < n + (appendStars C ss).gates.length ∧
      (appendStars C ss).size = C.size + (ss.map fun s => s.2.length + 1).sum ∧
      circuitFun n (appendStars C ss) = graphFun G ∅ ∧
      (∀ j < (appendStars C ss).gates.length,
        (gateAt (appendStars C ss) j).op = GateOp.and → BelowF G (appendStars C ss) j) := by
  obtain ⟨hD, hDo, hsize, hfun, hclean⟩ := appendStars_spec G C ss hne hAO ho he hc
  refine ⟨hD, hDo, hsize, ?_, hclean⟩
  apply eq_graphFun_of_boundary G _ hD
  · intro u v huv
    rw [hfun]
    rcases hcover u v huv with h | ⟨s, hs, w, hw, hEq⟩
    · simp [h]
    · have hpair : pairInput u v s.1 = true ∧ pairInput u v w = true := by
        rcases Sym2.eq_iff.mp hEq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> simp [h₁, h₂, pairInput]
      have hLeaf : s.2.any (pairInput u v) = true :=
        List.any_eq_true.mpr ⟨w, hw, hpair.2⟩
      have hAny : ss.any (fun t => pairInput u v t.1 && t.2.any (pairInput u v)) = true := by
        apply List.any_eq_true.mpr
        exact ⟨s, hs, by simp [hpair.1, hLeaf]⟩
      simp [hAny]
  · intro x hx
    apply Bool.eq_false_iff.mpr
    intro h
    rw [hfun] at h
    have hF : graphFun G ∅ x = true := by
      rcases Bool.or_eq_true_iff.mp h with h | h
      · exact hsafe x h
      · obtain ⟨s, hs, hsVal⟩ := List.any_eq_true.mp h
        obtain ⟨hcVal, hLeaf⟩ : x s.1 = true ∧ s.2.any x = true := by simpa using hsVal
        obtain ⟨w, hw, hxw⟩ := List.any_eq_true.mp hLeaf
        exact Repair.graph_true.mpr ⟨s.1, w, he s hs w hw, hcVal, hxw⟩
    rw [hx.1] at hF
    cases hF

end StarCompletion


namespace StarCost
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma repair_merge_complete_stars {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (ho : C.output < n + C.gates.length) (pick : ℕ → Fin n × Fin n)
    (hpick : ∀ i < C.gates.length, Repair.dirty G C i → G.Adj (pick i).1 (pick i).2)
    (T : Finset ℕ) (hT : ∀ k ∈ T, k < C.gates.length ∧ Repair.dirty G C k)
    (ss : List (Fin n × List (Fin n))) (hne : ∀ s ∈ ss, s.2 ≠ [])
    (he : ∀ s ∈ ss, ∀ w ∈ s.2, G.Adj s.1 w)
    (hcover : ∀ u v : Fin n, G.Adj u v →
      circuitFun n (Repair.repair G C pick) (pairInput u v) = true ∨
      ∃ s ∈ ss, ∃ w ∈ s.2, s(s.1, w) = s(u, v)) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
      (∀ i < D.gates.length, (gateAt D i).op = GateOp.and → BelowF G D i) ∧
      D.size + T.card = C.size + (T.image fun k => s((pick k).1, (pick k).2)).card + (ss.map fun s => s.2.length + 1).sum := by
  obtain ⟨R, hRAO, hRclean, hRsize, hRfun⟩ :=
    Duplicate.collapse_labeled_dirty_set hAO hfun pick hpick T hT
  obtain ⟨hPAO, _, hPsafe, _⟩ := Repair.arbitrary_edge_repair hAO hfun pick hpick
  have hpo : (Repair.repair G C pick).output < n + (Repair.repair G C pick).gates.length := by
    change C.output < n + (Repair.repair G C pick).gates.length
    rwa [Repair.repair_len]
  have hRtrue : circuitFun n R (fun _ => true) = true := by
    rw [hRfun]
    exact Completion.ao2_all_true (Repair.repair G C pick) hPAO _ hpo
  have hRo := Completion.output_valid_of_true R (fun _ => true) hRtrue
  have hRsafe : ∀ x, circuitFun n R x = true → graphFun G ∅ x = true := by
    intro x hx
    rw [hRfun] at hx
    exact hPsafe x hx
  have hRcover : ∀ u v : Fin n, G.Adj u v → circuitFun n R (pairInput u v) = true ∨
      ∃ s ∈ ss, ∃ w ∈ s.2, s(s.1, w) = s(u, v) := by
    intro u v huv
    rw [hRfun]
    exact hcover u v huv
  obtain ⟨hDAO, _, hDsize, hDfun, hDclean⟩ :=
    StarCompletion.complete_missing_stars G R ss hne hRAO hRo he hRsafe hRclean hRcover
  refine ⟨StarCompletion.appendStars R ss, hDAO, hDfun, hDclean, ?_⟩
  omega

lemma repair_merge_complete_stars_no_larger {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (ho : C.output < n + C.gates.length) (pick : ℕ → Fin n × Fin n)
    (hpick : ∀ i < C.gates.length, Repair.dirty G C i → G.Adj (pick i).1 (pick i).2)
    (T : Finset ℕ) (hT : ∀ k ∈ T, k < C.gates.length ∧ Repair.dirty G C k)
    (ss : List (Fin n × List (Fin n))) (hne : ∀ s ∈ ss, s.2 ≠ [])
    (he : ∀ s ∈ ss, ∀ w ∈ s.2, G.Adj s.1 w)
    (hcover : ∀ u v : Fin n, G.Adj u v →
      circuitFun n (Repair.repair G C pick) (pairInput u v) = true ∨
      ∃ s ∈ ss, ∃ w ∈ s.2, s(s.1, w) = s(u, v))
    (hcost : (T.image fun k => s((pick k).1, (pick k).2)).card + (ss.map fun s => s.2.length + 1).sum ≤ T.card) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
      ∀ i < D.gates.length, (gateAt D i).op = GateOp.and → BelowF G D i := by
  obtain ⟨D, hDAO, hDfun, hDclean, hDsize⟩ := repair_merge_complete_stars hAO hfun ho pick hpick T hT ss hne he hcover
  exact ⟨D, hDAO, hDfun, by omega, hDclean⟩

end StarCost

end PEqualNP.Outside.L_meta_2583
