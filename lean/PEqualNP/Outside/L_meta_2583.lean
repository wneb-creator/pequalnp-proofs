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


namespace FrontierCount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma binary_forest_leaves (O L R : Finset ℕ) (next : ℕ → Fin 2 → ℕ)
    (hdisjoint : Disjoint O L)
    (hcover : ∀ w ∈ O ∪ L, w ∈ R ∨ ∃ o ∈ O, ∃ b : Fin 2, next o b = w) :
    L.card ≤ O.card + R.card := by
  classical
  let children : Finset ℕ := (O.product Finset.univ).image fun p => next p.1 p.2
  have hsub : O ∪ L ⊆ R ∪ children := by
    intro w hw
    rcases hcover w hw with hr | ⟨o, ho, b, hb⟩
    · exact Finset.mem_union_left children hr
    · apply Finset.mem_union_right R
      exact Finset.mem_image.mpr ⟨(o, b), Finset.mem_product.mpr ⟨ho, Finset.mem_univ b⟩, hb⟩
  have hcard := Finset.card_le_card hsub
  have hunion := Finset.card_union_le R children
  have hchildren : children.card ≤ O.card * 2 := by
    have h := Finset.card_image_le (s := O.product (Finset.univ : Finset (Fin 2)))
      (f := fun p => next p.1 p.2)
    simpa [children] using h
  rw [Finset.card_union_of_disjoint hdisjoint] at hcard
  omega

lemma circuit_forest_leaves {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (O L R : Finset ℕ)
    (hO : ∀ j ∈ O, j < C.gates.length ∧ (gateAt C j).op = GateOp.or)
    (hL : ∀ j ∈ L, (gateAt C j).op = GateOp.and)
    (hcover : ∀ j ∈ O ∪ L, n + j ∈ R ∨
      ∃ o ∈ O, n + j ∈ (gateAt C o).inputs) :
    L.card ≤ O.card + R.card := by
  classical
  let wires (S : Finset ℕ) := S.image fun j => n + j
  have hcard (S : Finset ℕ) : (wires S).card = S.card := by
    apply Finset.card_image_of_injective
    intro a b hab
    change n + a = n + b at hab
    omega
  have hdisjoint : Disjoint (wires O) (wires L) := by
    apply Finset.disjoint_left.mpr
    intro w hwO hwL
    obtain ⟨o, ho, hwo⟩ := Finset.mem_image.mp hwO
    obtain ⟨l, hl, hwl⟩ := Finset.mem_image.mp hwL
    have hol : o = l := by omega
    have hor := (hO o ho).2
    have hand := hL l hl
    rw [hol, hand] at hor
    cases hor
  let next (w : ℕ) (b : Fin 2) := opnd C (w - n) b
  have hcov : ∀ w ∈ wires O ∪ wires L, w ∈ R ∨
      ∃ o ∈ wires O, ∃ b : Fin 2, next o b = w := by
    intro w hw
    have hx : ∃ j ∈ O ∪ L, n + j = w := by
      rcases Finset.mem_union.mp hw with hw | hw
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
        exact ⟨j, Finset.mem_union_left L hj, rfl⟩
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
        exact ⟨j, Finset.mem_union_right O hj, rfl⟩
    obtain ⟨j, hj, rfl⟩ := hx
    rcases hcover j hj with hr | ⟨o, ho, hin⟩
    · exact Or.inl hr
    · obtain ⟨p, q, hpq⟩ := Frontier.binaryInputs hAO (hO o ho).1
      rw [hpq] at hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      apply Or.inr
      refine ⟨n + o, Finset.mem_image.mpr ⟨o, ho, rfl⟩, ?_⟩
      rcases hin with hin | hin
      · refine ⟨0, ?_⟩
        simpa [next, opnd, hpq] using hin.symm
      · refine ⟨1, ?_⟩
        simpa [next, opnd, hpq] using hin.symm
  have h := binary_forest_leaves (wires O) (wires L) R next hdisjoint hcov
  simpa only [hcard] using h

noncomputable def pathOrs (n : ℕ) (C : Circuit) (R L : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.range C.gates.length).filter fun j =>
    (gateAt C j).op = GateOp.or ∧ ∃ r ∈ R,
      Relation.ReflTransGen (Frontier.OrStep n C) r (n + j) ∧
      ∃ l ∈ L, Relation.ReflTransGen (Frontier.OrStep n C) (n + j) (n + l)

lemma mem_pathOrs {n : ℕ} {C : Circuit} {R L : Finset ℕ} {j : ℕ} :
    j ∈ pathOrs n C R L ↔ j < C.gates.length ∧
      (gateAt C j).op = GateOp.or ∧ ∃ r ∈ R,
        Relation.ReflTransGen (Frontier.OrStep n C) r (n + j) ∧
        ∃ l ∈ L, Relation.ReflTransGen (Frontier.OrStep n C) (n + j) (n + l) := by
  classical
  simp only [pathOrs, Finset.mem_filter, Finset.mem_range]

lemma or_path_leaves {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (R L : Finset ℕ)
    (hL : ∀ j ∈ L, (gateAt C j).op = GateOp.and)
    (hreach : ∀ j ∈ L, ∃ r ∈ R,
      Relation.ReflTransGen (Frontier.OrStep n C) r (n + j)) :
    L.card ≤ (pathOrs n C R L).card + R.card := by
  classical
  apply circuit_forest_leaves hAO (pathOrs n C R L) L R
  · intro j hj
    have h := mem_pathOrs.mp hj
    exact ⟨h.1, h.2.1⟩
  · exact hL
  · intro j hj
    have hp : ∃ r ∈ R, Relation.ReflTransGen (Frontier.OrStep n C) r (n + j) ∧
        ∃ l ∈ L, Relation.ReflTransGen (Frontier.OrStep n C) (n + j) (n + l) := by
      rcases Finset.mem_union.mp hj with hj | hj
      · exact (mem_pathOrs.mp hj).2.2
      · obtain ⟨r, hr, hpath⟩ := hreach j hj
        exact ⟨r, hr, hpath, j, hj, Relation.ReflTransGen.refl⟩
    obtain ⟨r, hr, hpath, l, hl, hdown⟩ := hp
    rcases Relation.ReflTransGen.cases_tail hpath with heq | ⟨w, hpre, hstep⟩
    · exact Or.inl (heq ▸ hr)
    · obtain ⟨o, ho, rfl, hop, hin, hlt⟩ := hstep
      apply Or.inr
      refine ⟨o, ?_, hin⟩
      apply mem_pathOrs.mpr
      exact ⟨ho, hop, r, hr, hpre, l, hl,
        Relation.ReflTransGen.head ⟨o, ho, rfl, hop, hin, hlt⟩ hdown⟩

lemma raw_descendant_empty {n : ℕ} {C : Circuit} {r w : ℕ}
    (hempty : orIn n C r = ∅)
    (hpath : Relation.ReflTransGen (Frontier.OrStep n C) r w) : orIn n C w = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have hm := Frontier.reach_mem_orIn t (hpath.trans (Frontier.mem_orIn_reach t ht))
  rw [hempty] at hm
  exact Finset.notMem_empty t hm

lemma raw_operand_empty {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or)
    (hempty : orIn n C (n + j) = ∅) (b : Fin 2) : orIn n C (opnd C j b) = ∅ := by
  apply raw_descendant_empty hempty
  exact Relation.ReflTransGen.single ⟨j, hj, rfl, hop,
    Frontier.opndMem hAO hj b, Frontier.opndBound hAO hj b⟩

lemma pathOrs_outside_lam_mixing {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (R L : Finset ℕ)
    (hL : ∀ j ∈ L, j ∈ junk G C) (hR : ∀ r ∈ R, orIn n C r = ∅) :
    pathOrs n C R L ⊆ (orN G C \ lam G C) \ mixing G C := by
  classical
  intro j hj
  obtain ⟨hjlen, hjor, r, hr, hpath, l, hl, hdown⟩ := mem_pathOrs.mp hj
  obtain ⟨_, _, x, hxl, hxG⟩ := Frontier.junkData (hL l hl)
  have hxj : gateVal n C j x = true := by
    apply Frontier.orStep_up (by simp) hdown
    exact hxl
  have hnot : ¬ BelowF G C j := by
    intro h
    have ht := h x hxj
    rw [hxG] at ht
    cases ht
  have hraw := raw_descendant_empty (hR r hr) hpath
  have h0 := raw_operand_empty hAO hjlen hjor hraw 0
  have h1 := raw_operand_empty hAO hjlen hjor hraw 1
  have hN : j ∈ orN G C := by
    simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
    exact ⟨hjlen, hjor, hnot⟩
  apply Finset.mem_sdiff.mpr
  constructor
  · apply Finset.mem_sdiff.mpr
    refine ⟨hN, ?_⟩
    intro hm
    have hp := (Finset.mem_filter.mp hm).2.1
    rw [h0] at hp
    exact Finset.not_nonempty_empty hp
  · intro hm
    have hp := (Finset.mem_filter.mp hm).2
    exact hp (by simp [h0, h1])

lemma mixing_subset_outside_lam {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} : mixing G C ⊆ orN G C \ lam G C := by
  classical
  intro j hj
  obtain ⟨hN, hmix⟩ := Finset.mem_filter.mp hj
  apply Finset.mem_sdiff.mpr
  refine ⟨hN, ?_⟩
  intro hl
  obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hl
  exact hmix (by simp [h0.ne_empty, h1.ne_empty])

lemma dirty_empty_source_count {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (R L : Finset ℕ)
    (hL : ∀ j ∈ L, j ∈ junk G C) (hR : ∀ r ∈ R, orIn n C r = ∅)
    (hreach : ∀ j ∈ L, ∃ r ∈ R, PEqualNP.CleanedNonEdge.OrReaches n C r j) :
    L.card + (mixing G C).card ≤ (orN G C \ lam G C).card + R.card := by
  classical
  have hleaf := or_path_leaves hAO R L (fun j hj => (Frontier.junkData (hL j hj)).2.1)
    (fun j hj => by
      obtain ⟨r, hr, hp⟩ := hreach j hj
      exact ⟨r, hr, (Frontier.orReaches_reach j r hp).1⟩)
  have hsub := pathOrs_outside_lam_mixing hAO R L hL hR
  have hdisjoint : Disjoint (pathOrs n C R L) (mixing G C) := by
    apply Finset.disjoint_left.mpr
    intro j hj hm
    exact (Finset.mem_sdiff.mp (hsub hj)).2 hm
  have hunion : pathOrs n C R L ∪ mixing G C ⊆ orN G C \ lam G C := by
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · exact (Finset.mem_sdiff.mp (hsub hj)).1
    · exact mixing_subset_outside_lam hj
  have hcard := Finset.card_le_card hunion
  rw [Finset.card_union_of_disjoint hdisjoint] at hcard
  omega

lemma dirty_frontier_budget {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (R L : Finset ℕ) (z : ℕ)
    (hL : ∀ j ∈ L, j ∈ junk G C) (hR : ∀ r ∈ R, orIn n C r = ∅)
    (hreach : ∀ j ∈ L, ∃ r ∈ R, PEqualNP.CleanedNonEdge.OrReaches n C r j)
    (hroots : R.card ≤ (mixing G C).card + z) :
    L.card ≤ (orN G C \ lam G C).card + z := by
  have h := dirty_empty_source_count hAO R L hL hR hreach
  omega

end FrontierCount


namespace FrontierCount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge

noncomputable def emptyWire (n : ℕ) (C : Circuit) (j : ℕ) : ℕ := by
  classical
  exact opnd C j (if side (n := n) C j 0 = ∅ then 0 else 1)

lemma emptyWire_empty {n : ℕ} {C : Circuit} {j : ℕ}
    (h : side (n := n) C j 0 = ∅ ∨ side (n := n) C j 1 = ∅) :
    orIn n C (emptyWire n C j) = ∅ := by
  classical
  unfold emptyWire
  split_ifs with h0
  · exact h0
  · exact h.resolve_left h0

lemma mixing_emptyWire_empty {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {j : ℕ} (hj : j ∈ mixing G C) :
    orIn n C (emptyWire n C j) = ∅ := by
  apply emptyWire_empty
  have h := (Finset.mem_filter.mp hj).2
  change (side (n := n) C j 0 = ∅) ≠ (side (n := n) C j 1 = ∅) at h
  by_cases h0 : side (n := n) C j 0 = ∅
  · exact Or.inl h0
  · right
    by_contra h1
    exact h (by simp [h0, h1])

lemma and_raw_empty {n : ℕ} {C : Circuit} {j : ℕ}
    (hop : (gateAt C j).op = GateOp.and) : orIn n C (n + j) = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro t ht
  have hpath := Frontier.mem_orIn_reach t ht
  rcases Relation.ReflTransGen.cases_head hpath with heq | ⟨w, hstep, _⟩
  · omega
  · obtain ⟨k, _, heq, hor, _, _⟩ := hstep
    have hkj : k = j := by omega
    rw [hkj, hop] at hor
    cases hor

lemma raw_or_nonempty_operand {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (hraw : (orIn n C (n + j)).Nonempty) :
    ∃ b : Fin 2, (side (n := n) C j b).Nonempty := by
  obtain ⟨t, ht⟩ := hraw
  have hpath := Frontier.mem_orIn_reach t ht
  rcases Relation.ReflTransGen.cases_head hpath with heq | ⟨w, hstep, hrest⟩
  · omega
  · obtain ⟨k, _, heq, _, hin, _⟩ := hstep
    have hkj : k = j := by omega
    subst k
    obtain ⟨p, q, hpq⟩ := Frontier.binaryInputs hAO hj
    rw [hpq] at hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl
    · refine ⟨0, t, ?_⟩
      simpa [side, opnd, hpq] using Frontier.reach_mem_orIn t hrest
    · refine ⟨1, t, ?_⟩
      simpa [side, opnd, hpq] using Frontier.reach_mem_orIn t hrest

lemma mixing_of_empty_child {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {j v : ℕ}
    (hN : j ∈ orN G C) (hraw : (orIn n C (n + j)).Nonempty)
    (hin : v ∈ (gateAt C j).inputs) (hv : orIn n C v = ∅) :
    j ∈ mixing G C ∧ emptyWire n C j = v := by
  classical
  have hData : j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧ ¬ BelowF G C j := by
    simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using hN
  have hj := hData.1
  obtain ⟨p, q, hpq⟩ := Frontier.binaryInputs hAO hj
  obtain ⟨b, hb⟩ := raw_or_nonempty_operand hAO hj hraw
  rw [hpq] at hin
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
  rcases hin with rfl | rfl
  · have h0 : side (n := n) C j 0 = ∅ := by simpa [side, opnd, hpq] using hv
    have h1 : side (n := n) C j 1 ≠ ∅ := by
      intro he
      fin_cases b <;> simp_all
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨hN, ?_⟩
      change (side (n := n) C j 0 = ∅) ≠ (side (n := n) C j 1 = ∅)
      simp [h0, h1]
    · simp [emptyWire, h0, opnd, hpq]
  · have h1 : side (n := n) C j 1 = ∅ := by simpa [side, opnd, hpq] using hv
    have h0 : side (n := n) C j 0 ≠ ∅ := by
      intro he
      fin_cases b <;> simp_all
    constructor
    · apply Finset.mem_filter.mpr
      refine ⟨hN, ?_⟩
      change (side (n := n) C j 0 = ∅) ≠ (side (n := n) C j 1 = ∅)
      simp [h0, h1]
    · simp [emptyWire, h0, opnd, hpq]

lemma dirty_reach_has_mixing {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {g : ℕ} (hg : g ∈ junk G C) :
    ∀ w : ℕ, (orIn n C w).Nonempty → OrReaches n C w g →
      ∃ m ∈ mixing G C, OrReaches n C (emptyWire n C m) g := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hraw hreach
    have hn : n ≤ w := hreach.1
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hnot : ¬ BelowF G C j := by
      obtain ⟨_, _, x, hx, hxG⟩ := Frontier.junkData hg
      intro hb
      have hv : gateVal n C j x = true := Frontier.reachVal hreach hx
      have hf := hb x hv
      rw [hxG] at hf
      cases hf
    obtain ⟨hj, hcase⟩ := (Frontier.orReaches_iff n C j g).mp hreach
    rcases hcase with heq | ⟨hop, v, hin, hlt, hvg⟩
    · rw [← heq, and_raw_empty (Frontier.junkData hg).2.1] at hraw
      exact False.elim (Finset.not_nonempty_empty hraw)
    · by_cases hv : (orIn n C v).Nonempty
      · exact ih v hlt hv hvg
      · have hvempty : orIn n C v = ∅ := Finset.not_nonempty_iff_eq_empty.mp hv
        have hN : j ∈ orN G C := by
          simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range]
          exact ⟨hj, hop, hnot⟩
        obtain ⟨hm, heq⟩ := mixing_of_empty_child hAO hN hraw hin hvempty
        exact ⟨j, hm, heq.symm ▸ hvg⟩

noncomputable def emptyRoots {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) : Finset ℕ := by
  classical
  exact ((centreless G C).image (emptyWire n C)) ∪ ((mixing G C).image (emptyWire n C))

lemma emptyRoots_card {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) :
    (emptyRoots G C).card ≤ (mixing G C).card + (centreless G C).card := by
  classical
  have h := Finset.card_union_le ((centreless G C).image (emptyWire n C))
    ((mixing G C).image (emptyWire n C))
  have h0 := Finset.card_image_le (s := centreless G C) (f := emptyWire n C)
  have h1 := Finset.card_image_le (s := mixing G C) (f := emptyWire n C)
  change _ ≤ _ at h
  unfold emptyRoots
  omega

lemma emptyRoots_empty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (r : ℕ) (hr : r ∈ emptyRoots G C) : orIn n C r = ∅ := by
  classical
  rcases Finset.mem_union.mp hr with hr | hr
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hr
    exact emptyWire_empty (Finset.mem_filter.mp ha).2
  · obtain ⟨m, hm, rfl⟩ := Finset.mem_image.mp hr
    exact mixing_emptyWire_empty hm

lemma selected_dirty_frontier_bound {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (L : Finset ℕ)
    (hL : ∀ g ∈ L, g ∈ junk G C)
    (hselected : ∀ g ∈ L,
      (∃ a ∈ centreless G C, OrReaches n C (emptyWire n C a) g) ∨
      ∃ a ∈ tops G C, a ∉ centreless G C ∧ ∃ b : Fin 2, OrReaches n C (opnd C a b) g) :
    L.card ≤ (orN G C \ lam G C).card + (centreless G C).card := by
  classical
  apply dirty_frontier_budget hAO (emptyRoots G C) L (centreless G C).card hL
    (emptyRoots_empty G C)
  · intro g hg
    rcases hselected g hg with ⟨a, ha, hp⟩ | ⟨a, ha, hnc, b, hp⟩
    · refine ⟨emptyWire n C a, ?_, hp⟩
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    · have hraw : (orIn n C (opnd C a b)).Nonempty := by
        apply Finset.nonempty_iff_ne_empty.mpr
        intro he
        apply hnc
        apply Finset.mem_filter.mpr
        refine ⟨ha, ?_⟩
        fin_cases b
        · exact Or.inl he
        · exact Or.inr he
      obtain ⟨m, hm, hmg⟩ := dirty_reach_has_mixing hAO (hL g hg) _ hraw hp
      refine ⟨emptyWire n C m, ?_, hmg⟩
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨m, hm, rfl⟩)
  · exact emptyRoots_card G C

end FrontierCount


namespace FrontierCount

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma certificate_selected_resource {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {u v : Fin n}
    (hbad : s(u, v) ∉ starEdges G C) (H : Finset ℕ) {a : ℕ} (ha : a ∈ tops G C)
    (hcert : ∀ b : Fin 2, (∃ t ∈ side (n := n) C a b, t = u ∨ t = v) ∨
      ∃ j ∈ H, j ∈ junk G C ∧ OrReaches n C (opnd C a b) j) :
    ∃ g ∈ H, g ∈ junk G C ∧
      ((∃ a ∈ centreless G C, OrReaches n C (emptyWire n C a) g) ∨
       ∃ a ∈ tops G C, a ∉ centreless G C ∧ ∃ b : Fin 2, OrReaches n C (opnd C a b) g) := by
  classical
  by_cases hc : a ∈ centreless G C
  · let b : Fin 2 := if side (n := n) C a 0 = ∅ then 0 else 1
    have hw : emptyWire n C a = opnd C a b := rfl
    have he := emptyWire_empty (Finset.mem_filter.mp hc).2
    rcases hcert b with ⟨t, ht, _⟩ | ⟨g, hg, hj, hp⟩
    · change t ∈ orIn n C (opnd C a b) at ht
      rw [← hw, he] at ht
      exact False.elim (Finset.notMem_empty t ht)
    · exact ⟨g, hg, hj, Or.inl ⟨a, hc, hw.symm ▸ hp⟩⟩
  · have hmissing : ∃ b : Fin 2, ¬ ∃ t ∈ side (n := n) C a b, t = u ∨ t = v := by
      by_contra! hall
      obtain ⟨x, hx, hxe⟩ := hall 0
      obtain ⟨y, hy, hye⟩ := hall 1
      have hne : x ≠ y := G.ne_of_adj (Frontier.topAdj hAO ha hx hy)
      have hsym : s(u, v) = s(x, y) := by
        rcases hxe with hxu | hxv <;> rcases hye with hyu | hyv
        · exact False.elim (hne (hxu.trans hyu.symm))
        · rw [hxu, hyv]
        · rw [hxv, hyu]
          exact Sym2.eq_swap
        · exact False.elim (hne (hxv.trans hyv.symm))
      apply hbad
      rw [hsym]
      exact Finset.mem_biUnion.mpr ⟨a, ha,
        Finset.mem_image.mpr ⟨(x, y), Finset.mem_product.mpr ⟨hx, hy⟩, rfl⟩⟩
    obtain ⟨b, hb⟩ := hmissing
    rcases hcert b with hraw | ⟨g, hg, hj, hp⟩
    · exact False.elim (hb hraw)
    · exact ⟨g, hg, hj, Or.inr ⟨a, ha, hc, b, hp⟩⟩

lemma disjoint_ustar_certificates_bound {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (E : Finset (Fin n × Fin n))
    (hE : ∀ e ∈ E, s(e.1, e.2) ∈ Ustar G C) (H : (Fin n × Fin n) → Finset ℕ)
    (hdisjoint : ∀ e ∈ E, ∀ f ∈ E, e ≠ f → Disjoint (H e) (H f))
    (hcert : ∀ e ∈ E, ∃ a ∈ tops G C,
      ∀ b : Fin 2, (∃ t ∈ side (n := n) C a b, t = e.1 ∨ t = e.2) ∨
        ∃ j ∈ H e, j ∈ junk G C ∧ OrReaches n C (opnd C a b) j) :
    E.card ≤ (orN G C \ lam G C).card + (centreless G C).card := by
  classical
  have hex (e : E) : ∃ g ∈ H e.val, g ∈ junk G C ∧
      ((∃ a ∈ centreless G C, OrReaches n C (emptyWire n C a) g) ∨
       ∃ a ∈ tops G C, a ∉ centreless G C ∧ ∃ b : Fin 2, OrReaches n C (opnd C a b) g) := by
    obtain ⟨a, ha, hp⟩ := hcert e.val e.property
    exact certificate_selected_resource hAO (Finset.mem_sdiff.mp (hE e.val e.property)).2 _ ha hp
  let f : E → ℕ := fun e => Classical.choose (hex e)
  have hf (e : E) := Classical.choose_spec (hex e)
  have hinj : Function.Injective f := by
    intro e d heq
    apply Subtype.ext
    by_contra hne
    have hd := hdisjoint e.val e.property d.val d.property hne
    have he := (hf e).1
    have hd' := (hf d).1
    change f e ∈ H e.val at he
    change f d ∈ H d.val at hd'
    rw [← heq] at hd'
    exact Finset.disjoint_left.mp hd he hd'
  let L : Finset ℕ := Finset.univ.image f
  have hL : ∀ g ∈ L, g ∈ junk G C := by
    intro g hg
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hg
    exact (hf e).2.1
  have hselected : ∀ g ∈ L,
      (∃ a ∈ centreless G C, OrReaches n C (emptyWire n C a) g) ∨
      ∃ a ∈ tops G C, a ∉ centreless G C ∧ ∃ b : Fin 2, OrReaches n C (opnd C a b) g := by
    intro g hg
    obtain ⟨e, _, rfl⟩ := Finset.mem_image.mp hg
    exact (hf e).2.2
  have hcard : L.card = E.card := by
    simp only [L, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_coe]
  rw [← hcard]
  exact selected_dirty_frontier_bound hAO L hL hselected

end FrontierCount

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

lemma collapse_shared_dirty_set {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C)
    (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hCsafe : ∀ x, circuitFun n C x = true → graphFun G ∅ x = true)
    (hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j)
    (T : Finset ℕ) (hT : ∀ j ∈ T, j < C.gates.length ∧ Repair.dirty G C j) :
    ∃ D : Circuit, IsAO2 n D ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.size + T.card = B.size + C.size ∧
      circuitFun n D = circuitFun n (shared G B C) ∧
      (∀ x, circuitFun n D x = true → graphFun G ∅ x = true) := by
  classical
  obtain ⟨hR, hRsize, hRsafe, hRclean⟩ := shared_safe_clean G B C hB hC hBo hBsafe hCsafe hBclean
  let S := T.image fun j => B.gates.length + j
  have hcard : S.card = T.card :=
    Finset.card_image_of_injOn (fun _ _ _ _ heq => Nat.add_left_cancel heq)
  have hred : ∀ k ∈ S, k < (shared G B C).gates.length ∧ ∃ p < n + k,
      ∀ x : Fin n → Bool, val (shared G B C) (List.ofFn x) p =
        val (shared G B C) (List.ofFn x) (n + k) := by
    intro k hk
    obtain ⟨j, hjT, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hj, hd⟩ := hT j hjT
    refine ⟨?_, B.output, by omega, ?_⟩
    · rw [shared_length]
      omega
    · intro x
      rw [copied_value G B C hBo hj hd x, prefix_value G B C x hBo]
      rfl
  obtain ⟨D, hD, hDclean, hDsize, hDfun⟩ :=
    Duplicate.collapse_redundant_set S (shared G B C) hR hRclean hred
  refine ⟨D, hD, hDclean, ?_, hDfun, ?_⟩
  · rw [hcard, hRsize] at hDsize
    exact hDsize
  · intro x hx
    apply hRsafe x
    rwa [← hDfun]

lemma shared_completion_of_coverage {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C)
    (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hCsafe : ∀ x, circuitFun n C x = true → graphFun G ∅ x = true)
    (hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j)
    (T : Finset ℕ) (hT : ∀ j ∈ T, j < C.gates.length ∧ Repair.dirty G C j)
    (hcover : ∀ u v : Fin n, G.Adj u v → circuitFun n (shared G B C) (pairInput u v) = true) :
    ∃ D : Circuit, IsAO2 n D ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.size + T.card = B.size + C.size ∧ circuitFun n D = graphFun G ∅ := by
  obtain ⟨D, hD, hDclean, hDsize, hDfun, hDsafe⟩ :=
    collapse_shared_dirty_set G B C hB hC hBo hBsafe hCsafe hBclean T hT
  refine ⟨D, hD, hDclean, hDsize, ?_⟩
  apply eq_graphFun_of_boundary G D hD
  · intro u v huv
    rw [hDfun]
    exact hcover u v huv
  · intro x hx
    apply Bool.eq_false_iff.mpr
    intro ht
    have h := hDsafe x ht
    rw [hx.1] at h
    cases h

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

lemma shared_completion_of_B_or_raw {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C)
    (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hfun : circuitFun n C = graphFun G ∅)
    (hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j)
    (T : Finset ℕ) (hT : ∀ j ∈ T, j < C.gates.length ∧ Repair.dirty G C j)
    (hcover : ∀ u v : Fin n, G.Adj u v → circuitFun n B (pairInput u v) = true ∨
      ∃ a ∈ tops G C, OrReaches n C C.output a ∧
        ∃ p ∈ side (n := n) C a 0, ∃ q ∈ side (n := n) C a 1, s(p, q) = s(u, v)) :
    ∃ D : Circuit, IsAO2 n D ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.size + T.card = B.size + C.size ∧ circuitFun n D = graphFun G ∅ := by
  apply shared_completion_of_coverage G B C hB hC hBo hBsafe
    (fun x hx => by rwa [← hfun]) hBclean T hT
  intro u v huv
  rcases hcover u v huv with hBx | ⟨a, ha, hr, p, hp, q, hq, hEq⟩
  · apply shared_forward_of_B_true G B C hC hBo (pairInput u v) hBx
    rw [hfun]
    exact Repair.graph_true.mpr ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
  · have hpair : pairInput u v p = true ∧ pairInput u v q = true := by
      rcases Sym2.eq_iff.mp hEq with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩ <;> simp [h₁, h₂, pairInput]
    exact shared_accepts_raw_top G B C hC (pairInput u v) ha hr hp hq hpair.1 hpair.2

end SharedRepair

namespace SharedRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma shared_completion_of_ustar {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C)
    (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hfun : circuitFun n C = graphFun G ∅)
    (hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j)
    (hlive : ∀ a ∈ tops G C, OrReaches n C C.output a)
    (hU : ∀ u v : Fin n, s(u, v) ∈ Ustar G C → circuitFun n B (pairInput u v) = true) :
    ∃ D : Circuit, IsAO2 n D ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.size + (junk G C).card = B.size + C.size ∧ circuitFun n D = graphFun G ∅ := by
  classical
  apply shared_completion_of_B_or_raw G B C hB hC hBo hBsafe hfun hBclean (junk G C)
  · intro j hj
    exact ⟨(Frontier.junkData hj).1, Labeling.junk_is_dirty hj⟩
  · intro u v huv
    by_cases hbad : s(u, v) ∈ Ustar G C
    · exact Or.inl (hU u v hbad)
    · have he : s(u, v) ∈ G.edgeFinset := by simpa using huv
      have hraw : s(u, v) ∈ starEdges G C := by
        by_contra hn
        exact hbad (Finset.mem_sdiff.mpr ⟨he, hn⟩)
      obtain ⟨a, ha, hcross⟩ := Finset.mem_biUnion.mp hraw
      obtain ⟨⟨p, q⟩, hpq, hpqe⟩ := Finset.mem_image.mp hcross
      obtain ⟨hp, hq⟩ := Finset.mem_product.mp hpq
      exact Or.inr ⟨a, ha, hlive a ha, p, hp, q, hq, hpqe⟩

lemma shared_completion_ustar_no_larger {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C)
    (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hfun : circuitFun n C = graphFun G ∅)
    (hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j)
    (hlive : ∀ a ∈ tops G C, OrReaches n C C.output a)
    (hU : ∀ u v : Fin n, s(u, v) ∈ Ustar G C → circuitFun n B (pairInput u v) = true)
    (hcost : B.size ≤ (junk G C).card) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
      ∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j := by
  obtain ⟨D, hDAO, hDclean, hDsize, hDfun⟩ :=
    shared_completion_of_ustar G B C hB hC hBo hBsafe hfun hBclean hlive hU
  exact ⟨D, hDAO, hDfun, by omega, hDclean⟩

end SharedRepair

namespace DeadSet

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CircuitMoves PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma erase_unread_value {n : ℕ} {C : Circuit} {k p : ℕ}
    (hAO : IsAO2 n C) (hk : k < C.gates.length) (hp : p < n + k)
    (hread : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs)
    (x : Fin n → Bool) : ∀ w : ℕ, w ≠ n + k →
      val (eraseGate n C k p) (List.ofFn x) (eraseRedirect n k p w) =
        val C (List.ofFn x) w := by
  let E := eraseGate n C k p
  have hEAO : IsAO2 n E := erase_isAO2 n C k p hk hp hAO
  have hlen : E.gates.length + 1 = C.gates.length := erase_length n C k p hk
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hne
    by_cases hlow : w < n + k
    · rw [erase_redirect_lt n k p w hlow]
      exact Duplicate.erase_lower_value hk (by simp) hlow
    have hgt : n + k < w := by omega
    rw [erase_redirect_gt n k p w hgt]
    by_cases hout : n + C.gates.length ≤ w
    · rw [val_ge (n := n) (by simp) hout,
        val_ge (n := n) (by simp) (show n + E.gates.length ≤ w - 1 by omega)]
    obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
    have hj : j < C.gates.length := by omega
    have hkj : k < j := by omega
    have hjE : j - 1 < E.gates.length := by omega
    have hwire : n + j - 1 = n + (j - 1) := by omega
    have hg : gateAt E (j - 1) = erase_rg (eraseRedirect n k p) (gateAt C j) := by
      change gateAt (eraseGate n C k p) (j - 1) = _
      rw [erase_gateAt n C k p (j - 1) hk (by omega), ite_eq_right (by omega)]
      congr 2
      omega
    rw [hwire, SharedRepair.old_value E hEAO hjE x, hg, SharedRepair.old_value C hAO hj x]
    simp only [erase_rg, List.map_map, Function.comp_def]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact ih i (hAO.2.1 j hj i hi) (fun heq => hread j hj (heq ▸ hi))

lemma erase_unread_circuit {n : ℕ} {C : Circuit} {k p : ℕ}
    (hAO : IsAO2 n C) (hk : k < C.gates.length) (hp : p < n + k)
    (hread : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs)
    (hout : C.output ≠ n + k) :
    circuitFun n (eraseGate n C k p) = circuitFun n C := by
  funext x
  change val (eraseGate n C k p) (List.ofFn x) (eraseGate n C k p).output =
    val C (List.ofFn x) C.output
  rw [erase_output n C k p hk]
  exact erase_unread_value hAO hk hp hread x C.output hout

lemma erase_unread_clean {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {k p : ℕ} (hAO : IsAO2 n C)
    (hk : k < C.gates.length) (hp : p < n + k)
    (hread : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) :
    ∀ j < (eraseGate n C k p).gates.length,
      (gateAt (eraseGate n C k p) j).op = GateOp.and → BelowF G (eraseGate n C k p) j := by
  have hlen := erase_length n C k p hk
  intro j hj hop x hx
  by_cases hjk : j < k
  · have hg : gateAt (eraseGate n C k p) j = gateAt C j := by
      rw [erase_gateAt n C k p j hk (by omega), ite_eq_left hjk]
    have hop' : (gateAt C j).op = GateOp.and := by rwa [hg] at hop
    apply hclean j (by omega) hop' x
    have hw := erase_unread_value hAO hk hp hread x (n + j) (by omega)
    rw [erase_redirect_lt n k p (n + j) (by omega)] at hw
    change val C (List.ofFn x) (n + j) = true
    rw [← hw]
    exact hx
  · have hg : gateAt (eraseGate n C k p) j = erase_rg (eraseRedirect n k p) (gateAt C (j + 1)) := by
      rw [erase_gateAt n C k p j hk (by omega), ite_eq_right hjk]
    have hop' : (gateAt C (j + 1)).op = GateOp.and := by rw [hg] at hop; exact hop
    apply hclean (j + 1) (by omega) hop' x
    have hw := erase_unread_value hAO hk hp hread x (n + (j + 1)) (by omega)
    have hr : eraseRedirect n k p (n + (j + 1)) = n + j := by
      rw [erase_redirect_gt n k p (n + (j + 1)) (by omega)]
      omega
    rw [hr] at hw
    change val C (List.ofFn x) (n + (j + 1)) = true
    rw [← hw]
    exact hx

lemma redirect_zero_eq_lower {n k i w : ℕ} (hn : 0 < n) (hi : i < k) :
    eraseRedirect n k 0 w = n + i ↔ w = n + i := by
  unfold eraseRedirect
  split_ifs <;> omega

lemma erase_dead_set {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hn : 0 < n) (S : Finset ℕ) : ∀ C : Circuit, IsAO2 n C →
    (∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) →
    (∀ k ∈ S, k < C.gates.length) →
    (∀ k ∈ S, C.output ≠ n + k) →
    (∀ j < C.gates.length, j ∉ S → ∀ k ∈ S, n + k ∉ (gateAt C j).inputs) →
    ∃ D : Circuit, IsAO2 n D ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.size + S.card = C.size ∧ circuitFun n D = circuitFun n C := by
  classical
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    intro C hAO hclean hS hout hread
    by_cases hzero : S = ∅
    · exact ⟨C, hAO, hclean, by simp [hzero], rfl⟩
    have hne : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hzero
    let k := S.max' hne
    have hkS : k ∈ S := S.max'_mem hne
    have hk : k < C.gates.length := hS k hkS
    have hp : 0 < n + k := by omega
    have hdead : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs := by
      intro j hj hin
      by_cases hjS : j ∈ S
      · have hjk : j ≤ k := S.le_max' j hjS
        have hlt := hAO.2.1 j hj (n + k) hin
        omega
      · exact hread j hj hjS k hkS hin
    let E := eraseGate n C k 0
    have hEAO : IsAO2 n E := erase_isAO2 n C k 0 hk hp hAO
    have hEclean := erase_unread_clean hAO hk hp hdead hclean
    have hEfun := erase_unread_circuit hAO hk hp hdead (hout k hkS)
    have hlen : E.gates.length + 1 = C.gates.length := erase_length n C k 0 hk
    have hsmall : ∀ i ∈ S.erase k, i < k := by
      intro i hi
      obtain ⟨hne, hiS⟩ := Finset.mem_erase.mp hi
      have hmax := S.le_max' i hiS
      omega
    have hremain : ∀ i ∈ S.erase k, i < E.gates.length := by
      intro i hi
      have hi' := hsmall i hi
      omega
    have houtE : ∀ i ∈ S.erase k, E.output ≠ n + i := by
      intro i hi heq
      have heq' : eraseRedirect n k 0 C.output = n + i := by
        change (eraseGate n C k 0).output = n + i at heq
        rwa [erase_output n C k 0 hk] at heq
      exact hout i (Finset.mem_of_mem_erase hi) ((redirect_zero_eq_lower hn (hsmall i hi)).mp heq')
    have hreadE : ∀ j < E.gates.length, j ∉ S.erase k →
        ∀ i ∈ S.erase k, n + i ∉ (gateAt E j).inputs := by
      intro j hj hjS i hi hin
      have hilow := hsmall i hi
      by_cases hjk : j < k
      · have hg : gateAt E j = gateAt C j := by
          change gateAt (eraseGate n C k 0) j = _
          rw [erase_gateAt n C k 0 j hk (by omega), ite_eq_left hjk]
        have hjnot : j ∉ S := by
          intro hjin
          exact hjS (Finset.mem_erase.mpr ⟨by omega, hjin⟩)
        rw [hg] at hin
        exact hread j (by omega) hjnot i (Finset.mem_of_mem_erase hi) hin
      · have hg : gateAt E j = erase_rg (eraseRedirect n k 0) (gateAt C (j + 1)) := by
          change gateAt (eraseGate n C k 0) j = _
          rw [erase_gateAt n C k 0 j hk (by omega), ite_eq_right hjk]
        have hjnot : j + 1 ∉ S := by
          intro hjin
          have hjmax := S.le_max' (j + 1) hjin
          omega
        rw [hg] at hin
        obtain ⟨w, hw, heq⟩ := List.mem_map.mp hin
        have heq' : w = n + i := (redirect_zero_eq_lower hn hilow).mp heq
        subst w
        exact hread (j + 1) (by omega) hjnot i (Finset.mem_of_mem_erase hi) hw
    obtain ⟨D, hDAO, hDclean, hDsize, hDfun⟩ :=
      ih (S.erase k) (Finset.erase_ssubset hkS) E hEAO hEclean hremain houtE hreadE
    refine ⟨D, hDAO, hDclean, ?_, hDfun.trans hEfun⟩
    have hsize : E.size + 1 = C.size := erase_size n C k 0 hk
    have hcard := Finset.card_erase_add_one hkS
    omega

end DeadSet

namespace DeadSet

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CircuitMoves PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma redirect_prefix_eq_lower {n k i p w : ℕ} (hp : p < n + i) (hi : i < k) :
    eraseRedirect n k p w = n + i ↔ w = n + i := by
  unfold eraseRedirect
  split_ifs <;> omega

lemma erase_mixed_union {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (U : Finset ℕ) : ∀ R S : Finset ℕ, R ∪ S = U → Disjoint R S →
    ∀ (C : Circuit) (p : ℕ), IsAO2 n C →
    (∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) →
    (∀ k ∈ U, k < C.gates.length) →
    (∀ k ∈ U, p < n + k) →
    (∀ k ∈ R, ∀ x : Fin n → Bool,
      val C (List.ofFn x) p = val C (List.ofFn x) (n + k)) →
    (∀ k ∈ S, C.output ≠ n + k) →
    (∀ j < C.gates.length, j ∉ S → ∀ k ∈ S, n + k ∉ (gateAt C j).inputs) →
    ∃ D : Circuit, IsAO2 n D ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.size + R.card + S.card = C.size ∧ circuitFun n D = circuitFun n C := by
  classical
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    intro R S hU hdis C p hAO hclean hbound hprefix hcopy hout hread
    by_cases hzero : U = ∅
    · have hR : R = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro k hk
        have hmem : k ∈ U := hU ▸ Finset.mem_union_left S hk
        rw [hzero] at hmem
        exact Finset.notMem_empty k hmem
      have hS : S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro k hk
        have hmem : k ∈ U := hU ▸ Finset.mem_union_right R hk
        rw [hzero] at hmem
        exact Finset.notMem_empty k hmem
      exact ⟨C, hAO, hclean, by simp [hR, hS], rfl⟩
    have hne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hzero
    let k := U.max' hne
    have hkU : k ∈ U := U.max'_mem hne
    have hk : k < C.gates.length := hbound k hkU
    have hp : p < n + k := hprefix k hkU
    let E := eraseGate n C k p
    have hEAO : IsAO2 n E := erase_isAO2 n C k p hk hp hAO
    have hstep : circuitFun n E = circuitFun n C ∧
        (∀ j < E.gates.length, (gateAt E j).op = GateOp.and → BelowF G E j) := by
      have hmember : k ∈ R ∪ S := hU.symm ▸ hkU
      rcases Finset.mem_union.mp hmember with hkR | hkS
      · exact ⟨Duplicate.erase_equal_circuit hk hp (hcopy k hkR),
          Duplicate.erase_equal_preserves_clean hk hp (hcopy k hkR) hclean⟩
      · have hdead : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs := by
          intro j hj hin
          by_cases hjS : j ∈ S
          · have hjU : j ∈ U := hU ▸ Finset.mem_union_right R hjS
            have hjk : j ≤ k := U.le_max' j hjU
            have hlt := hAO.2.1 j hj (n + k) hin
            omega
          · exact hread j hj hjS k hkS hin
        exact ⟨erase_unread_circuit hAO hk hp hdead (hout k hkS),
          erase_unread_clean hAO hk hp hdead hclean⟩
    have hlen : E.gates.length + 1 = C.gates.length := erase_length n C k p hk
    have hsmall : ∀ i ∈ U.erase k, i < k := by
      intro i hi
      obtain ⟨hne, hiU⟩ := Finset.mem_erase.mp hi
      have hmax := U.le_max' i hiU
      omega
    have hU' : R.erase k ∪ S.erase k = U.erase k := by
      rw [← hU]
      ext i
      simp only [Finset.mem_union, Finset.mem_erase]
      tauto
    have hdis' : Disjoint (R.erase k) (S.erase k) :=
      hdis.mono (Finset.erase_subset k R) (Finset.erase_subset k S)
    have hRmem : ∀ i ∈ R.erase k, i ∈ U.erase k := by
      intro i hi
      rw [← hU']
      exact Finset.mem_union_left _ hi
    have hSmem : ∀ i ∈ S.erase k, i ∈ U.erase k := by
      intro i hi
      rw [← hU']
      exact Finset.mem_union_right _ hi
    have hremain : ∀ i ∈ U.erase k, i < E.gates.length := by
      intro i hi
      have hi' := hsmall i hi
      omega
    have hprefix' : ∀ i ∈ U.erase k, p < n + i := by
      intro i hi
      exact hprefix i (Finset.mem_of_mem_erase hi)
    have hcopy' : ∀ i ∈ R.erase k, ∀ x : Fin n → Bool,
        val E (List.ofFn x) p = val E (List.ofFn x) (n + i) := by
      intro i hi x
      have hilow := hsmall i (hRmem i hi)
      change val (eraseGate n C k p) (List.ofFn x) p =
        val (eraseGate n C k p) (List.ofFn x) (n + i)
      rw [Duplicate.erase_lower_value hk (by simp) hp,
        Duplicate.erase_lower_value hk (by simp) (by omega : n + i < n + k)]
      exact hcopy i (Finset.mem_of_mem_erase hi) x
    have hout' : ∀ i ∈ S.erase k, E.output ≠ n + i := by
      intro i hi heq
      have heq' : eraseRedirect n k p C.output = n + i := by
        change (eraseGate n C k p).output = n + i at heq
        rwa [erase_output n C k p hk] at heq
      have himem := hSmem i hi
      exact hout i (Finset.mem_of_mem_erase hi)
        ((redirect_prefix_eq_lower (hprefix' i himem) (hsmall i himem)).mp heq')
    have hread' : ∀ j < E.gates.length, j ∉ S.erase k →
        ∀ i ∈ S.erase k, n + i ∉ (gateAt E j).inputs := by
      intro j hj hjS i hi hin
      have himem := hSmem i hi
      have hilow := hsmall i himem
      by_cases hjk : j < k
      · have hg : gateAt E j = gateAt C j := by
          change gateAt (eraseGate n C k p) j = _
          rw [erase_gateAt n C k p j hk (by omega), ite_eq_left hjk]
        have hjnot : j ∉ S := by
          intro hjin
          exact hjS (Finset.mem_erase.mpr ⟨by omega, hjin⟩)
        rw [hg] at hin
        exact hread j (by omega) hjnot i (Finset.mem_of_mem_erase hi) hin
      · have hg : gateAt E j = erase_rg (eraseRedirect n k p) (gateAt C (j + 1)) := by
          change gateAt (eraseGate n C k p) j = _
          rw [erase_gateAt n C k p j hk (by omega), ite_eq_right hjk]
        have hjnot : j + 1 ∉ S := by
          intro hjin
          have hjU : j + 1 ∈ U := hU ▸ Finset.mem_union_right R hjin
          have hjmax := U.le_max' (j + 1) hjU
          omega
        rw [hg] at hin
        obtain ⟨w, hw, heq⟩ := List.mem_map.mp hin
        have heq' : w = n + i := (redirect_prefix_eq_lower (hprefix' i himem) hilow).mp heq
        subst w
        exact hread (j + 1) (by omega) hjnot i (Finset.mem_of_mem_erase hi) hw
    obtain ⟨D, hDAO, hDclean, hDsize, hDfun⟩ :=
      ih (U.erase k) (Finset.erase_ssubset hkU) (R.erase k) (S.erase k) hU' hdis'
        E p hEAO hstep.2 hremain hprefix' hcopy' hout' hread'
    refine ⟨D, hDAO, hDclean, ?_, hDfun.trans hstep.1⟩
    have hsize : E.size + 1 = C.size := erase_size n C k p hk
    have hcard := Finset.card_erase_add_one hkU
    have hcount := Finset.card_union_of_disjoint hdis
    have hcount' := Finset.card_union_of_disjoint hdis'
    rw [hU] at hcount
    rw [hU'] at hcount'
    omega

lemma erase_mixed_sets {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (R S : Finset ℕ) (hdis : Disjoint R S) (C : Circuit) (p : ℕ)
    (hAO : IsAO2 n C)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j)
    (hbound : ∀ k ∈ R ∪ S, k < C.gates.length)
    (hprefix : ∀ k ∈ R ∪ S, p < n + k)
    (hcopy : ∀ k ∈ R, ∀ x : Fin n → Bool,
      val C (List.ofFn x) p = val C (List.ofFn x) (n + k))
    (hout : ∀ k ∈ S, C.output ≠ n + k)
    (hread : ∀ j < C.gates.length, j ∉ S → ∀ k ∈ S, n + k ∉ (gateAt C j).inputs) :
    ∃ D : Circuit, IsAO2 n D ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.size + R.card + S.card = C.size ∧ circuitFun n D = circuitFun n C :=
  erase_mixed_union (R ∪ S) R S rfl hdis C p hAO hclean hbound hprefix hcopy hout hread

end DeadSet


namespace SourcePool
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open SharedRepair

lemma shift_injective (n m : ℕ) : Function.Injective (shiftWire n m) := by
  intro a b h
  unfold shiftWire at h
  split_ifs at h <;> omega

lemma shifted_source_pool {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hBo : B.output < n + B.gates.length)
    (S : Finset ℕ) (hS : ∀ k ∈ S, k < C.gates.length)
    (hout : ∀ k ∈ S, C.output ≠ n + k)
    (hread : ∀ j < C.gates.length, j ∉ S → ¬ Repair.dirty G C j →
      ∀ w ∈ (gateAt C j).inputs, ∀ k ∈ S, w ≠ n + k) :
    let D := shared G B C
    let A := S.image fun k => B.gates.length + k
    (∀ k ∈ A, k < D.gates.length) ∧
      (∀ k ∈ A, D.output ≠ n + k) ∧
      (∀ j < D.gates.length, j ∉ A → ∀ w ∈ (gateAt D j).inputs,
        ∀ k ∈ A, w ≠ n + k) := by
  classical
  let D := shared G B C
  let A := S.image fun k => B.gates.length + k
  change (∀ k ∈ A, k < D.gates.length) ∧
      (∀ k ∈ A, D.output ≠ n + k) ∧
      (∀ j < D.gates.length, j ∉ A → ∀ w ∈ (gateAt D j).inputs,
        ∀ k ∈ A, w ≠ n + k)
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hk
    have hslt := hS s hs
    change B.gates.length + s < (shared G B C).gates.length
    rw [shared_length]
    omega
  · intro k hk heq
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hk
    change shiftWire n B.gates.length C.output = n + (B.gates.length + s) at heq
    rw [← shift_gate] at heq
    exact hout s hs (shift_injective n B.gates.length heq)
  · intro j hj hjA w hw k hk heq
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hk
    change j < (shared G B C).gates.length at hj
    rw [shared_length] at hj
    change w ∈ (gateAt (shared G B C) j).inputs at hw
    by_cases hjB : j < B.gates.length
    · rw [shared_gate_prefix G B C hjB] at hw
      have hlt := hB.2.1 j hjB w hw
      omega
    · obtain ⟨t, rfl⟩ : ∃ t, j = B.gates.length + t := ⟨j-B.gates.length, by omega⟩
      have ht : t < C.gates.length := by omega
      have htS : t ∉ S := by
        intro hm
        exact hjA (Finset.mem_image.mpr ⟨t, hm, rfl⟩)
      rw [shared_gate_old G B C ht] at hw
      unfold patchedGate at hw
      by_cases hd : Repair.dirty G C t
      · rw [ite_eq_left hd] at hw
        have hw' : w = B.output := by simpa using hw
        omega
      · rw [ite_eq_right hd] at hw
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        rw [← shift_gate] at heq
        exact hread t ht htS hd i hi s hs (shift_injective n B.gates.length heq)

end SourcePool

namespace SourcePool

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge SharedRepair

lemma shared_reclaim_source_pool {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C)
    (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hCsafe : ∀ x, circuitFun n C x = true → graphFun G ∅ x = true)
    (hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j)
    (T S : Finset ℕ) (hT : ∀ j ∈ T, j < C.gates.length ∧ Repair.dirty G C j)
    (hS : ∀ j ∈ S, j < C.gates.length ∧ ¬ Repair.dirty G C j)
    (hout : ∀ k ∈ S, C.output ≠ n + k)
    (hread : ∀ j < C.gates.length, j ∉ S → ¬ Repair.dirty G C j →
      ∀ w ∈ (gateAt C j).inputs, ∀ k ∈ S, w ≠ n + k) :
    ∃ D : Circuit, IsAO2 n D ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.size + T.card + S.card = B.size + C.size ∧
      circuitFun n D = circuitFun n (shared G B C) ∧
      (∀ x, circuitFun n D x = true → graphFun G ∅ x = true) := by
  classical
  let R := T.image fun k => B.gates.length + k
  let A := S.image fun k => B.gates.length + k
  have hRcard : R.card = T.card := Finset.card_image_of_injOn (fun _ _ _ _ h => Nat.add_left_cancel h)
  have hAcard : A.card = S.card := Finset.card_image_of_injOn (fun _ _ _ _ h => Nat.add_left_cancel h)
  obtain ⟨hAO, hsize, hsafe, hclean⟩ := shared_safe_clean G B C hB hC hBo hBsafe hCsafe hBclean
  obtain ⟨hAbound, hAout, hAread⟩ := shifted_source_pool G B C hB hBo S (fun k hk => (hS k hk).1) hout hread
  have hdis : Disjoint R A := by
    apply Finset.disjoint_left.mpr
    intro k hkR hkA
    obtain ⟨t, ht, heqT⟩ := Finset.mem_image.mp hkR
    obtain ⟨s, hs, heqS⟩ := Finset.mem_image.mp hkA
    have hts : t = s := by omega
    subst s
    exact (hS t hs).2 (hT t ht).2
  have hbound : ∀ k ∈ R ∪ A, k < (shared G B C).gates.length := by
    intro k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
      have htlen := (hT t ht).1
      rw [shared_length]
      omega
    · exact hAbound k hk
  have hprefix : ∀ k ∈ R ∪ A, B.output < n + k := by
    intro k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hk
      omega
    · obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hk
      omega
  have hcopy : ∀ k ∈ R, ∀ x : Fin n → Bool,
      val (shared G B C) (List.ofFn x) B.output = val (shared G B C) (List.ofFn x) (n + k) := by
    intro k hk x
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
    rw [prefix_value G B C x hBo, copied_value G B C hBo (hT t ht).1 (hT t ht).2 x]
    rfl
  have hreadA : ∀ j < (shared G B C).gates.length, j ∉ A →
      ∀ k ∈ A, n + k ∉ (gateAt (shared G B C) j).inputs := by
    intro j hj hjA k hk hin
    exact hAread j hj hjA (n+k) hin k hk rfl
  obtain ⟨D, hDAO, hDclean, hDsize, hDfun⟩ :=
    DeadSet.erase_mixed_sets R A hdis (shared G B C) B.output hAO hclean hbound hprefix hcopy hAout hreadA
  refine ⟨D, hDAO, hDclean, ?_, hDfun, ?_⟩
  · rwa [hRcard, hAcard, hsize] at hDsize
  · intro x hx
    apply hsafe x
    rwa [← hDfun]

lemma shared_reclaim_of_coverage {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C)
    (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hCsafe : ∀ x, circuitFun n C x = true → graphFun G ∅ x = true)
    (hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j)
    (T S : Finset ℕ) (hT : ∀ j ∈ T, j < C.gates.length ∧ Repair.dirty G C j)
    (hS : ∀ j ∈ S, j < C.gates.length ∧ ¬ Repair.dirty G C j)
    (hout : ∀ k ∈ S, C.output ≠ n + k)
    (hread : ∀ j < C.gates.length, j ∉ S → ¬ Repair.dirty G C j →
      ∀ w ∈ (gateAt C j).inputs, ∀ k ∈ S, w ≠ n + k)
    (hcover : ∀ u v : Fin n, G.Adj u v → circuitFun n (shared G B C) (pairInput u v) = true) :
    ∃ D : Circuit, IsAO2 n D ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.size + T.card + S.card = B.size + C.size ∧ circuitFun n D = graphFun G ∅ := by
  obtain ⟨D, hDAO, hDclean, hDsize, hDfun, hDsafe⟩ :=
    shared_reclaim_source_pool G B C hB hC hBo hBsafe hCsafe hBclean T S hT hS hout hread
  refine ⟨D, hDAO, hDclean, hDsize, ?_⟩
  apply eq_graphFun_of_boundary G D hDAO
  · intro u v huv
    rw [hDfun]
    exact hcover u v huv
  · intro x hx
    apply Bool.eq_false_iff.mpr
    intro ht
    have h := hDsafe x ht
    rw [hx.1] at h
    cases h

end SourcePool


namespace SourcePool
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge SharedRepair

lemma shared_reclaim_ustar_no_larger {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C)
    (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hfun : circuitFun n C = graphFun G ∅)
    (hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j)
    (hlive : ∀ a ∈ tops G C, OrReaches n C C.output a)
    (hU : ∀ u v : Fin n, s(u, v) ∈ Ustar G C → circuitFun n B (pairInput u v) = true)
    (S : Finset ℕ) (hS : ∀ j ∈ S, j < C.gates.length ∧ ¬ Repair.dirty G C j)
    (hout : ∀ k ∈ S, C.output ≠ n + k)
    (hread : ∀ j < C.gates.length, j ∉ S → ¬ Repair.dirty G C j →
      ∀ w ∈ (gateAt C j).inputs, ∀ k ∈ S, w ≠ n + k)
    (hcost : B.size ≤ (junk G C).card + S.card) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.size + (junk G C).card + S.card = B.size + C.size := by
  classical
  have hcover : ∀ u v : Fin n, G.Adj u v → circuitFun n (shared G B C) (pairInput u v) = true := by
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
  have hT : ∀ j ∈ junk G C, j < C.gates.length ∧ Repair.dirty G C j :=
    fun j hj => ⟨(Frontier.junkData hj).1, Labeling.junk_is_dirty hj⟩
  obtain ⟨D, hDAO, hDclean, hDsize, hDfun⟩ :=
    shared_reclaim_of_coverage G B C hB hC hBo hBsafe (fun x hx => by rwa [← hfun])
      hBclean (junk G C) S hT hS hout hread hcover
  exact ⟨D, hDAO, hDfun, by omega, hDclean, hDsize⟩

end SourcePool

namespace DominatedDelete

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CircuitMoves PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma erase_reflect_false {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {k p : ℕ} (hk : k < C.gates.length) (hp : p < n + k)
    (hAO : IsAO2 n C)
    (hpsafe : ∀ x : Fin n → Bool, val C (List.ofFn x) p = true → graphFun G ∅ x = true)
    (x : Fin n → Bool) (hFx : graphFun G ∅ x = false) :
    ∀ w, val (eraseGate n C k p) (List.ofFn x) (eraseRedirect n k p w) = true →
      val C (List.ofFn x) w = true := by
  apply erase_val_rel (fun op => op = GateOp.and ∨ op = GateOp.or)
    (fun a b => b = true → a = true) (fun _ h => h) hk hp ?_
    (fun g hg => hAO.1 g (List.mem_of_mem_drop hg)) (by simp) ?_
  · intro op l f f' hop h
    simpa only [List.map_map, Function.comp_def] using
      (opMono_imp op hop l (fun i => f' (eraseRedirect n k p i)) f (fun i _ => h i))
  · intro htrue
    have hf := hpsafe x htrue
    rw [hFx] at hf
    cases hf

lemma erase_safe_preserves_clean {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {k p : ℕ} (hAO : IsAO2 n C)
    (hk : k < C.gates.length) (hp : p < n + k)
    (hpsafe : ∀ x : Fin n → Bool, val C (List.ofFn x) p = true → graphFun G ∅ x = true)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) :
    ∀ j < (eraseGate n C k p).gates.length,
      (gateAt (eraseGate n C k p) j).op = GateOp.and → BelowF G (eraseGate n C k p) j := by
  have hlen := erase_length n C k p hk
  intro j hj hop x hx
  by_contra hn
  have hFx : graphFun G ∅ x = false := Bool.eq_false_iff.mpr hn
  by_cases hjk : j < k
  · have hg : gateAt (eraseGate n C k p) j = gateAt C j := by
      rw [erase_gateAt n C k p j hk (by omega), ite_eq_left hjk]
    have hop' : (gateAt C j).op = GateOp.and := by rwa [hg] at hop
    apply hn
    apply hclean j (by omega) hop' x
    have hw := erase_reflect_false hk hp hAO hpsafe x hFx (n + j)
    rw [erase_redirect_lt n k p (n + j) (by omega)] at hw
    exact hw hx
  · have hg : gateAt (eraseGate n C k p) j = erase_rg (eraseRedirect n k p) (gateAt C (j + 1)) := by
      rw [erase_gateAt n C k p j hk (by omega), ite_eq_right hjk]
    have hop' : (gateAt C (j + 1)).op = GateOp.and := by rw [hg] at hop; exact hop
    apply hn
    apply hclean (j + 1) (by omega) hop' x
    have hw := erase_reflect_false hk hp hAO hpsafe x hFx (n + (j + 1))
    have hr : eraseRedirect n k p (n + (j + 1)) = n + j := by
      rw [erase_redirect_gt n k p (n + (j + 1)) (by omega)]
      omega
    rw [hr] at hw
    exact hw hx

lemma erase_dominated_ao_clean {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {k p : ℕ} (hAO : IsAO2 n C)
    (hfun : circuitFun n C = graphFun G ∅)
    (hk : k < C.gates.length) (hp : p < n + k)
    (hpsafe : ∀ x : Fin n → Bool, val C (List.ofFn x) p = true → graphFun G ∅ x = true)
    (hdom : ∀ x : Fin n → Bool, val C (List.ofFn x) (n + k) = true → val C (List.ofFn x) p = true)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) :
    IsAO2 n (eraseGate n C k p) ∧ (eraseGate n C k p).size + 1 = C.size ∧
      circuitFun n (eraseGate n C k p) = graphFun G ∅ ∧
      (∀ j < (eraseGate n C k p).gates.length,
        (gateAt (eraseGate n C k p) j).op = GateOp.and → BelowF G (eraseGate n C k p) j) := by
  refine ⟨erase_isAO2 n C k p hk hp hAO, erase_size n C k p hk, ?_,
    erase_safe_preserves_clean hAO hk hp hpsafe hclean⟩
  funext x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    by_contra hn
    have hFx : graphFun G ∅ x = false := Bool.eq_false_iff.mpr hn
    have hback := erase_reflect_false hk hp hAO hpsafe x hFx C.output
    have hout : val (eraseGate n C k p) (List.ofFn x) (eraseRedirect n k p C.output) = true := by
      change val (eraseGate n C k p) (List.ofFn x) (eraseGate n C k p).output = true at hx
      rwa [erase_output n C k p hk] at hx
    have hCtrue : circuitFun n C x = true := hback hout
    rw [hfun] at hCtrue
    exact hn hCtrue
  · intro hx
    apply erase_eval_imp hk hp hAO.1 (by simp) (hdom x)
    change circuitFun n C x = true
    rwa [hfun]

lemma erase_dominated_union {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (U : Finset ℕ) : ∀ R S : Finset ℕ, R ∪ S = U → Disjoint R S →
    ∀ (C : Circuit) (p : ℕ), IsAO2 n C → circuitFun n C = graphFun G ∅ →
    (∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) →
    (∀ k ∈ U, k < C.gates.length) →
    (∀ k ∈ U, p < n + k) →
    (∀ x : Fin n → Bool, val C (List.ofFn x) p = true → graphFun G ∅ x = true) →
    (∀ k ∈ R, ∀ x : Fin n → Bool,
      val C (List.ofFn x) (n + k) = true → val C (List.ofFn x) p = true) →
    (∀ k ∈ S, C.output ≠ n + k) →
    (∀ j < C.gates.length, j ∉ U → ∀ k ∈ S, n + k ∉ (gateAt C j).inputs) →
    ∃ D : Circuit, IsAO2 n D ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.size + R.card + S.card = C.size ∧ circuitFun n D = graphFun G ∅ := by
  classical
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    intro R S hU hdis C p hAO hfun hclean hbound hprefix hpsafe hdom hout hread
    by_cases hzero : U = ∅
    · have hR : R = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro k hk
        have hmem : k ∈ U := hU ▸ Finset.mem_union_left S hk
        rw [hzero] at hmem
        exact Finset.notMem_empty k hmem
      have hS : S = ∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro k hk
        have hmem : k ∈ U := hU ▸ Finset.mem_union_right R hk
        rw [hzero] at hmem
        exact Finset.notMem_empty k hmem
      exact ⟨C, hAO, hclean, by simp [hR, hS], hfun⟩
    have hne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hzero
    let k := U.max' hne
    have hkU : k ∈ U := U.max'_mem hne
    have hk : k < C.gates.length := hbound k hkU
    have hp : p < n + k := hprefix k hkU
    let E := eraseGate n C k p
    have hEAO : IsAO2 n E := erase_isAO2 n C k p hk hp hAO
    have hstep : circuitFun n E = graphFun G ∅ ∧
        (∀ j < E.gates.length, (gateAt E j).op = GateOp.and → BelowF G E j) := by
      have hmember : k ∈ R ∪ S := hU.symm ▸ hkU
      rcases Finset.mem_union.mp hmember with hkR | hkS
      · obtain ⟨_, _, hEfun, hEclean⟩ :=
          erase_dominated_ao_clean hAO hfun hk hp hpsafe (hdom k hkR) hclean
        exact ⟨hEfun, hEclean⟩
      · have hdead : ∀ j < C.gates.length, n + k ∉ (gateAt C j).inputs := by
          intro j hj hin
          by_cases hjU : j ∈ U
          · have hjk : j ≤ k := U.le_max' j hjU
            have hlt := hAO.2.1 j hj (n + k) hin
            omega
          · exact hread j hj hjU k hkS hin
        exact ⟨(DeadSet.erase_unread_circuit hAO hk hp hdead (hout k hkS)).trans hfun,
          DeadSet.erase_unread_clean hAO hk hp hdead hclean⟩
    have hlen : E.gates.length + 1 = C.gates.length := erase_length n C k p hk
    have hsmall : ∀ i ∈ U.erase k, i < k := by
      intro i hi
      obtain ⟨hne, hiU⟩ := Finset.mem_erase.mp hi
      have hmax := U.le_max' i hiU
      omega
    have hU' : R.erase k ∪ S.erase k = U.erase k := by
      rw [← hU]
      ext i
      simp only [Finset.mem_union, Finset.mem_erase]
      tauto
    have hdis' : Disjoint (R.erase k) (S.erase k) :=
      hdis.mono (Finset.erase_subset k R) (Finset.erase_subset k S)
    have hRmem : ∀ i ∈ R.erase k, i ∈ U.erase k := by
      intro i hi
      rw [← hU']
      exact Finset.mem_union_left _ hi
    have hSmem : ∀ i ∈ S.erase k, i ∈ U.erase k := by
      intro i hi
      rw [← hU']
      exact Finset.mem_union_right _ hi
    have hremain : ∀ i ∈ U.erase k, i < E.gates.length := by
      intro i hi
      have hi' := hsmall i hi
      omega
    have hprefix' : ∀ i ∈ U.erase k, p < n + i := by
      intro i hi
      exact hprefix i (Finset.mem_of_mem_erase hi)
    have hpsafe' : ∀ x : Fin n → Bool, val E (List.ofFn x) p = true → graphFun G ∅ x = true := by
      intro x hx
      apply hpsafe x
      change val (eraseGate n C k p) (List.ofFn x) p = true at hx
      rwa [Duplicate.erase_lower_value hk (by simp) hp] at hx
    have hdom' : ∀ i ∈ R.erase k, ∀ x : Fin n → Bool,
        val E (List.ofFn x) (n + i) = true → val E (List.ofFn x) p = true := by
      intro i hi x hx
      have hilow := hsmall i (hRmem i hi)
      change val (eraseGate n C k p) (List.ofFn x) (n + i) = true at hx
      change val (eraseGate n C k p) (List.ofFn x) p = true
      rw [Duplicate.erase_lower_value hk (by simp) (by omega : n + i < n + k)] at hx
      rw [Duplicate.erase_lower_value hk (by simp) hp]
      exact hdom i (Finset.mem_of_mem_erase hi) x hx
    have hout' : ∀ i ∈ S.erase k, E.output ≠ n + i := by
      intro i hi heq
      have heq' : eraseRedirect n k p C.output = n + i := by
        change (eraseGate n C k p).output = n + i at heq
        rwa [erase_output n C k p hk] at heq
      have himem := hSmem i hi
      exact hout i (Finset.mem_of_mem_erase hi)
        ((DeadSet.redirect_prefix_eq_lower (hprefix' i himem) (hsmall i himem)).mp heq')
    have hread' : ∀ j < E.gates.length, j ∉ U.erase k →
        ∀ i ∈ S.erase k, n + i ∉ (gateAt E j).inputs := by
      intro j hj hjU i hi hin
      have himem := hSmem i hi
      have hilow := hsmall i himem
      by_cases hjk : j < k
      · have hg : gateAt E j = gateAt C j := by
          change gateAt (eraseGate n C k p) j = _
          rw [erase_gateAt n C k p j hk (by omega), ite_eq_left hjk]
        have hjnot : j ∉ U := by
          intro hjin
          exact hjU (Finset.mem_erase.mpr ⟨by omega, hjin⟩)
        rw [hg] at hin
        exact hread j (by omega) hjnot i (Finset.mem_of_mem_erase hi) hin
      · have hg : gateAt E j = erase_rg (eraseRedirect n k p) (gateAt C (j + 1)) := by
          change gateAt (eraseGate n C k p) j = _
          rw [erase_gateAt n C k p j hk (by omega), ite_eq_right hjk]
        have hjnot : j + 1 ∉ U := by
          intro hjin
          have hjmax := U.le_max' (j + 1) hjin
          omega
        rw [hg] at hin
        obtain ⟨w, hw, heq⟩ := List.mem_map.mp hin
        have heq' : w = n + i :=
          (DeadSet.redirect_prefix_eq_lower (hprefix' i himem) hilow).mp heq
        subst w
        exact hread (j + 1) (by omega) hjnot i (Finset.mem_of_mem_erase hi) hw
    obtain ⟨D, hDAO, hDclean, hDsize, hDfun⟩ :=
      ih (U.erase k) (Finset.erase_ssubset hkU) (R.erase k) (S.erase k) hU' hdis'
        E p hEAO hstep.1 hstep.2 hremain hprefix' hpsafe' hdom' hout' hread'
    refine ⟨D, hDAO, hDclean, ?_, hDfun⟩
    have hsize : E.size + 1 = C.size := erase_size n C k p hk
    have hcard := Finset.card_erase_add_one hkU
    have hcount := Finset.card_union_of_disjoint hdis
    have hcount' := Finset.card_union_of_disjoint hdis'
    rw [hU] at hcount
    rw [hU'] at hcount'
    omega

lemma erase_dominated_sets {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (R S : Finset ℕ) (hdis : Disjoint R S) (C : Circuit) (p : ℕ)
    (hAO : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j)
    (hbound : ∀ k ∈ R ∪ S, k < C.gates.length)
    (hprefix : ∀ k ∈ R ∪ S, p < n + k)
    (hpsafe : ∀ x : Fin n → Bool, val C (List.ofFn x) p = true → graphFun G ∅ x = true)
    (hdom : ∀ k ∈ R, ∀ x : Fin n → Bool,
      val C (List.ofFn x) (n + k) = true → val C (List.ofFn x) p = true)
    (hout : ∀ k ∈ S, C.output ≠ n + k)
    (hread : ∀ j < C.gates.length, j ∉ R ∪ S → ∀ k ∈ S, n + k ∉ (gateAt C j).inputs) :
    ∃ D : Circuit, IsAO2 n D ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.size + R.card + S.card = C.size ∧ circuitFun n D = graphFun G ∅ :=
  erase_dominated_union (R ∪ S) R S rfl hdis C p hAO hfun hclean hbound hprefix hpsafe hdom hout hread

end DominatedDelete

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
open PEqualNP.EdgeOwnership PEqualNP.TopForm SharedRepair

lemma shifted_absorption_pool {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hBo : B.output < n + B.gates.length)
    (R S : Finset ℕ) (hS : ∀ k ∈ S, k < C.gates.length)
    (hout : ∀ k ∈ S, C.output ≠ n + k)
    (hread : ∀ j < C.gates.length, j ∉ R ∪ S → ¬ Repair.dirty G C j →
      ∀ w ∈ (gateAt C j).inputs, ∀ k ∈ S, w ≠ n + k) :
    let D := shared G B C
    let A := R.image fun k => B.gates.length + k
    let Q := S.image fun k => B.gates.length + k
    (∀ k ∈ Q, k < D.gates.length) ∧
      (∀ k ∈ Q, D.output ≠ n + k) ∧
      (∀ j < D.gates.length, j ∉ A ∪ Q → ∀ w ∈ (gateAt D j).inputs,
        ∀ k ∈ Q, w ≠ n + k) := by
  classical
  let D := shared G B C
  let A := R.image fun k => B.gates.length + k
  let Q := S.image fun k => B.gates.length + k
  change (∀ k ∈ Q, k < D.gates.length) ∧
      (∀ k ∈ Q, D.output ≠ n + k) ∧
      (∀ j < D.gates.length, j ∉ A ∪ Q → ∀ w ∈ (gateAt D j).inputs,
        ∀ k ∈ Q, w ≠ n + k)
  refine ⟨?_, ?_, ?_⟩
  · intro k hk
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hk
    have hslt := hS s hs
    change B.gates.length + s < (shared G B C).gates.length
    rw [shared_length]
    omega
  · intro k hk heq
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hk
    change shiftWire n B.gates.length C.output = n + (B.gates.length + s) at heq
    rw [← shift_gate] at heq
    exact hout s hs (shift_injective n B.gates.length heq)
  · intro j hj hjAQ w hw k hk heq
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hk
    change j < (shared G B C).gates.length at hj
    rw [shared_length] at hj
    change w ∈ (gateAt (shared G B C) j).inputs at hw
    by_cases hjB : j < B.gates.length
    · rw [shared_gate_prefix G B C hjB] at hw
      have hlt := hB.2.1 j hjB w hw
      omega
    · obtain ⟨t, rfl⟩ : ∃ t, j = B.gates.length + t := ⟨j - B.gates.length, by omega⟩
      have ht : t < C.gates.length := by omega
      have htRS : t ∉ R ∪ S := by
        intro hm
        apply hjAQ
        rcases Finset.mem_union.mp hm with hm | hm
        · exact Finset.mem_union_left Q (Finset.mem_image.mpr ⟨t, hm, rfl⟩)
        · exact Finset.mem_union_right A (Finset.mem_image.mpr ⟨t, hm, rfl⟩)
      rw [shared_gate_old G B C ht] at hw
      unfold patchedGate at hw
      by_cases hd : Repair.dirty G C t
      · rw [ite_eq_left hd] at hw
        have hw' : w = B.output := by simpa using hw
        omega
      · rw [ite_eq_right hd] at hw
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hw
        rw [← shift_gate] at heq
        exact hread t ht htRS hd i hi s hs (shift_injective n B.gates.length heq)

end SourcePool

namespace SourcePool
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge SharedRepair

lemma shared_absorb_reclaim {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C) (hTop : TopForm G C)
    (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hCsafe : ∀ x, circuitFun n C x = true → graphFun G ∅ x = true)
    (hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j)
    (R S : Finset ℕ) (hdis : Disjoint R S)
    (hR : ∀ j ∈ R, j < C.gates.length ∧
      (Repair.dirty G C j ∨ (j ∈ tops G C ∧
        ∀ u ∈ side (n := n) C j 0, ∀ v ∈ side (n := n) C j 1,
          circuitFun n B (pairInput u v) = true)))
    (hS : ∀ j ∈ S, j < C.gates.length)
    (hout : ∀ k ∈ S, C.output ≠ n + k)
    (hread : ∀ j < C.gates.length, j ∉ R ∪ S → ¬ Repair.dirty G C j →
      ∀ w ∈ (gateAt C j).inputs, ∀ k ∈ S, w ≠ n + k)
    (hcover : ∀ u v : Fin n, G.Adj u v → circuitFun n (shared G B C) (pairInput u v) = true) :
    ∃ D : Circuit, IsAO2 n D ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.size + R.card + S.card = B.size + C.size ∧ circuitFun n D = graphFun G ∅ := by
  classical
  let A := R.image fun k => B.gates.length + k
  let Q := S.image fun k => B.gates.length + k
  have hAcard : A.card = R.card := Finset.card_image_of_injOn (fun _ _ _ _ h => Nat.add_left_cancel h)
  have hQcard : Q.card = S.card := Finset.card_image_of_injOn (fun _ _ _ _ h => Nat.add_left_cancel h)
  obtain ⟨hAO, hsize, hsafe, hclean⟩ := shared_safe_clean G B C hB hC hBo hBsafe hCsafe hBclean
  have hfun : circuitFun n (shared G B C) = graphFun G ∅ := by
    apply eq_graphFun_of_boundary G (shared G B C) hAO hcover
    intro x hx
    apply Bool.eq_false_iff.mpr
    intro ht
    have hf := hsafe x ht
    rw [hx.1] at hf
    cases hf
  obtain ⟨hQbound, hQout, hQread⟩ := shifted_absorption_pool G B C hB hBo R S hS hout hread
  have hdis' : Disjoint A Q := by
    apply Finset.disjoint_left.mpr
    intro k hkA hkQ
    obtain ⟨r, hr, heqr⟩ := Finset.mem_image.mp hkA
    obtain ⟨s, hs, heqs⟩ := Finset.mem_image.mp hkQ
    have hrs : r = s := by omega
    subst s
    exact Finset.disjoint_left.mp hdis hr hs
  have hbound : ∀ k ∈ A ∪ Q, k < (shared G B C).gates.length := by
    intro k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hk
      have hrlen := (hR r hr).1
      rw [shared_length]
      omega
    · exact hQbound k hk
  have hprefix : ∀ k ∈ A ∪ Q, B.output < n + k := by
    intro k hk
    rcases Finset.mem_union.mp hk with hk | hk
    · obtain ⟨r, _, rfl⟩ := Finset.mem_image.mp hk
      omega
    · obtain ⟨s, _, rfl⟩ := Finset.mem_image.mp hk
      omega
  have hpsafe : ∀ x : Fin n → Bool,
      val (shared G B C) (List.ofFn x) B.output = true → graphFun G ∅ x = true := by
    intro x hx
    rw [prefix_value G B C x hBo] at hx
    exact hBsafe x hx
  have hdom : ∀ k ∈ A, ∀ x : Fin n → Bool,
      val (shared G B C) (List.ofFn x) (n + k) = true →
        val (shared G B C) (List.ofFn x) B.output = true := by
    intro k hk x hx
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hk
    rw [prefix_value G B C x hBo]
    rcases (hR r hr).2 with hd | ⟨htop, hcross⟩
    · rwa [copied_value G B C hBo (hR r hr).1 hd x] at hx
    · exact shared_top_dominated_by_B G B C hB hC hTop hBo htop hcross x hx
  have hreadQ : ∀ j < (shared G B C).gates.length, j ∉ A ∪ Q →
      ∀ k ∈ Q, n + k ∉ (gateAt (shared G B C) j).inputs := by
    intro j hj hjA k hk hin
    exact hQread j hj hjA (n+k) hin k hk rfl
  obtain ⟨D, hDAO, hDclean, hDsize, hDfun⟩ :=
    DominatedDelete.erase_dominated_sets A Q hdis' (shared G B C) B.output
      hAO hfun hclean hbound hprefix hpsafe hdom hQout hreadQ
  refine ⟨D, hDAO, hDclean, ?_, hDfun⟩
  rwa [hAcard, hQcard, hsize] at hDsize

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

lemma shared_absorb_ustar_no_larger {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C) (hTop : TopForm G C)
    (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hfun : circuitFun n C = graphFun G ∅)
    (hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j)
    (hlive : ∀ a ∈ tops G C, OrReaches n C C.output a)
    (hU : ∀ u v : Fin n, s(u, v) ∈ Ustar G C → circuitFun n B (pairInput u v) = true)
    (K S : Finset ℕ) (hK : ∀ k ∈ K, k ∈ tops G C)
    (hcross : ∀ k ∈ K, ∀ u ∈ side (n := n) C k 0, ∀ v ∈ side (n := n) C k 1,
      circuitFun n B (pairInput u v) = true)
    (hdis : Disjoint (junk G C ∪ K) S)
    (hS : ∀ j ∈ S, j < C.gates.length)
    (hout : ∀ k ∈ S, C.output ≠ n + k)
    (hread : ∀ j < C.gates.length, j ∉ (junk G C ∪ K) ∪ S → ¬ Repair.dirty G C j →
      ∀ w ∈ (gateAt C j).inputs, ∀ k ∈ S, w ≠ n + k)
    (hcost : B.size ≤ (junk G C).card + K.card + S.card) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.size + (junk G C).card + K.card + S.card = B.size + C.size := by
  classical
  have hJK : Disjoint (junk G C) K := by
    apply Finset.disjoint_left.mpr
    intro k hkJ hkK
    exact (Labeling.junk_is_dirty hkJ).2 (Frontier.topData (hK k hkK)).2.2
  have hR : ∀ j ∈ junk G C ∪ K, j < C.gates.length ∧
      (Repair.dirty G C j ∨ (j ∈ tops G C ∧
        ∀ u ∈ side (n := n) C j 0, ∀ v ∈ side (n := n) C j 1,
          circuitFun n B (pairInput u v) = true)) := by
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · exact ⟨(Frontier.junkData hj).1, Or.inl (Labeling.junk_is_dirty hj)⟩
    · exact ⟨(Frontier.topData (hK j hj)).1, Or.inr ⟨hK j hj, hcross j hj⟩⟩
  obtain ⟨D, hDAO, hDclean, hDsize, hDfun⟩ :=
    shared_absorb_reclaim G B C hB hC hTop hBo hBsafe (fun x hx => by rwa [← hfun])
      hBclean (junk G C ∪ K) S hdis hR hS hout hread
      (shared_accepts_edges_of_ustar G B C hC hBo hfun hlive hU)
  rw [Finset.card_union_of_disjoint hJK] at hDsize
  exact ⟨D, hDAO, hDfun, by omega, hDclean, by omega⟩

end SourcePool

namespace SourcePool

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma or_path_stays_in_pool {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (K S : Finset ℕ) (hK : K ⊆ tops G C)
    (hread : ∀ j < C.gates.length, j ∉ junk G C ∪ K ∪ S →
      ∀ k ∈ S, n + k ∉ (gateAt C j).inputs)
    {w w' : ℕ} (hr : Relation.ReflTransGen (Frontier.OrStep n C) w w')
    (hend : ∃ k ∈ S, w' = n + k) : ∃ k ∈ S, w = n + k := by
  induction hr using Relation.ReflTransGen.head_induction_on with
  | refl => exact hend
  | head hstep _ ih =>
    obtain ⟨j, hj, rfl, hop, hin, _⟩ := hstep
    obtain ⟨k, hk, heq⟩ := ih
    have hjS : j ∈ S := by
      by_contra hnS
      have hnjunk : j ∉ junk G C := by
        intro hm
        have hand := (Frontier.junkData hm).2.1
        rw [hop] at hand
        cases hand
      have hnK : j ∉ K := by
        intro hm
        have hand := (Frontier.topData (hK hm)).2.1
        rw [hop] at hand
        cases hand
      have hout : j ∉ junk G C ∪ K ∪ S := by simp [hnjunk, hnK, hnS]
      rw [heq] at hin
      exact hread j hj hout k hk hin
    exact ⟨j, hjS, rfl⟩

lemma lambda_pool_has_selected_top {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (K S : Finset ℕ) (hK : K ⊆ tops G C)
    (hS : ∀ j ∈ S, (gateAt C j).op = GateOp.or)
    (hread : ∀ j < C.gates.length, j ∉ junk G C ∪ K ∪ S →
      ∀ k ∈ S, n + k ∉ (gateAt C j).inputs)
    {h : ℕ} (hlam : h ∈ lam G C) (hpool : h ∈ S) :
    ∃ a ∈ K, a ∈ tops G C ∧ a ∉ centreless G C ∧
      ∃ b : Fin 2, (side (n := n) C a (1 - b)).card = 1 ∧ OrReaches n C (opnd C a b) h := by
  classical
  obtain ⟨hN, h0, _, a, ha, b, hother, hr⟩ := Finset.mem_filter.mp hlam
  have hdata : h < C.gates.length ∧ (gateAt C h).op = GateOp.or ∧ ¬ BelowF G C h := by
    simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using hN
  have hown : (side (n := n) C a b).Nonempty := by
    obtain ⟨t, ht⟩ := h0
    refine ⟨t, ?_⟩
    apply Frontier.reach_mem_orIn
    exact (Frontier.orReaches_reach h _ hr).1.trans
      (Relation.ReflTransGen.head
        ⟨h, hdata.1, rfl, hdata.2.1, Frontier.opndMem hAO hdata.1 0,
          Frontier.opndBound hAO hdata.1 0⟩ (Frontier.mem_orIn_reach t ht))
  have hotherNE : (side (n := n) C a (1 - b)).Nonempty := Finset.card_pos.mp (by omega)
  have hncentre : a ∉ centreless G C := by
    intro hc
    have he := (Finset.mem_filter.mp hc).2
    rcases he with he | he <;> fin_cases b <;> simp_all
  have haK : a ∈ K := by
    by_contra hnK
    have hnjunk : a ∉ junk G C := by
      intro hm
      exact (Labeling.junk_is_dirty hm).2 (Frontier.topData ha).2.2
    have hnS : a ∉ S := by
      intro hm
      have hand := (Frontier.topData ha).2.1
      rw [hS a hm] at hand
      cases hand
    obtain ⟨g, hg, heq⟩ := or_path_stays_in_pool K S hK hread
      (Frontier.orReaches_reach h _ hr).1 ⟨h, hpool, rfl⟩
    have hin := Frontier.opndMem hAO (Frontier.topData ha).1 b
    rw [heq] at hin
    exact hread a (Frontier.topData ha).1 (by simp [hnjunk, hnK, hnS]) g hg hin
  exact ⟨a, haK, ha, hncentre, b, hother, hr⟩

lemma centreless_or_pool_disjoint_lambda {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (S : Finset ℕ)
    (hS : ∀ j ∈ S, (gateAt C j).op = GateOp.or)
    (hread : ∀ j < C.gates.length, j ∉ junk G C ∪ centreless G C ∪ S →
      ∀ k ∈ S, n + k ∉ (gateAt C j).inputs) : S ∩ lam G C = ∅ := by
  classical
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro h hh
  obtain ⟨hpool, hlam⟩ := Finset.mem_inter.mp hh
  obtain ⟨a, ha, _, hnc, _⟩ := lambda_pool_has_selected_top hAO (centreless G C) S
    (Finset.filter_subset _ _) hS hread hlam hpool
  exact hnc ha

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

lemma gate_budget {n : ℕ} {C : Circuit} (hm : Monotone2 C) (rb : ReadsBack n C)
    (hclean : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      singletonSupport n C (n + k) = ∅) :
    2 * (births n C).card + (merges n C).card ≤ C.size + 1 := by
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
  have hRc : R.card ≤ C.size := by
    change R.card ≤ C.gates.length
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  omega


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

lemma leaf_budget {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} {c : Fin n}
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (hclean : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      singletonSupport n C (n + k) = ∅)
    (m : ℕ) (roots : Finset ℕ)
    (hvalid : ∀ w ∈ roots, w < n ∨ reachable n C (w - n))
    (hadj : ∀ w ∈ roots, ∀ v ∈ singletonSupport n C w, G.Adj c v)
    (hbound : ∀ w ∈ roots, 1 < (singletonSupport n C w).card → w < n + m) :
    (roots.biUnion (singletonSupport n C)).card ≤ roots.card + (mergePool C G c m).card := by
  classical
  induction m generalizing roots with
  | zero =>
    have hsmall : ∀ w ∈ roots, (singletonSupport n C w).card ≤ 1 := by
      intro w hw
      by_contra! hb
      have hw' := hbound w hw hb
      have hs := support_input (C := C) (⟨w, by omega⟩ : Fin n)
      simp [hs] at hb
    calc
      _ ≤ ∑ w ∈ roots, (singletonSupport n C w).card := Finset.card_biUnion_le
      _ ≤ ∑ _w ∈ roots, 1 := Finset.sum_le_sum hsmall
      _ = _ := by simp [mergePool]
  | succ m ih =>
    have hpool : mergePool C G c m ⊆ mergePool C G c (m + 1) := by
      intro k hk
      obtain ⟨hk, hh⟩ := mem_mergePool.1 hk
      exact mem_mergePool.2 ⟨by omega, hh⟩
    by_cases htop : n + m ∈ roots ∧ 1 < (singletonSupport n C (n + m)).card
    · obtain ⟨hmem, hlarge⟩ := htop
      have hr : reachable n C m := by
        rcases hvalid _ hmem with h | h
        · omega
        · simpa using h
      have hor : (gateAt C m).op = GateOp.or := (gate_op hm hr.1).resolve_left fun h => by
        simp [hclean m hr h] at hlarge
      let P := positiveInputs n C m
      let T := roots.erase (n + m) ∪ P
      have hback : ∀ w ∈ P, w < n + m :=
        fun w hw => rb m hr.1 w (mem_positiveInputs.1 hw).1
      have hup : ∀ w ∈ P, singletonSupport n C w ⊆ singletonSupport n C (n + m) := by
        intro w hw u hu
        exact (support_or rb hr.1 hor u).2 ⟨w, (mem_positiveInputs.1 hw).1, hu⟩
      have hTvalid : ∀ w ∈ T, w < n ∨ reachable n C (w - n) := by
        intro w hw
        rcases Finset.mem_union.1 hw with hw | hw
        · exact hvalid _ (Finset.mem_of_mem_erase hw)
        · by_cases hn : w < n
          · exact Or.inl hn
          · exact Or.inr (reachable_child rb hr (by
              rw [show n + (w - n) = w by omega]
              exact (mem_positiveInputs.1 hw).1))
      have hTadj : ∀ w ∈ T, ∀ v ∈ singletonSupport n C w, G.Adj c v := by
        intro w hw v hv
        rcases Finset.mem_union.1 hw with hw | hw
        · exact hadj _ (Finset.mem_of_mem_erase hw) v hv
        · exact hadj _ hmem v (hup _ hw hv)
      have hTbound : ∀ w ∈ T, 1 < (singletonSupport n C w).card → w < n + m := by
        intro w hw hcard
        rcases Finset.mem_union.1 hw with hw | hw
        · have hlt := hbound w (Finset.mem_of_mem_erase hw) hcard
          have hne := (Finset.mem_erase.1 hw).1
          omega
        · exact hback w hw
      have hsub : roots.biUnion (singletonSupport n C) ⊆ T.biUnion (singletonSupport n C) := by
        intro u hu
        obtain ⟨w, hw, huw⟩ := Finset.mem_biUnion.1 hu
        by_cases he : w = n + m
        · subst w
          obtain ⟨a, ha, hua⟩ := (support_or rb hr.1 hor u).1 huw
          exact Finset.mem_biUnion.2 ⟨a, Finset.mem_union_right _
            (mem_positiveInputs.2 ⟨ha, u, hua⟩), hua⟩
        · exact Finset.mem_biUnion.2 ⟨w, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨he, hw⟩), huw⟩
      have hfirst := (Finset.card_le_card hsub).trans (ih T hTvalid hTadj hTbound)
      have hTcard := Finset.card_union_le (roots.erase (n + m)) P
      have herase := Finset.card_erase_add_one hmem
      have hPc : P.card ≤ 2 := (Finset.card_filter_le _ _).trans (input_card hm hr.1)
      by_cases hp : 1 < P.card
      · have hnew : m ∈ mergePool C G c (m + 1) := mem_mergePool.2
          ⟨by omega, mem_merges.2 ⟨hr, hor, hlarge, hp⟩, hadj _ hmem⟩
        have hn : m ∉ mergePool C G c m := fun h => (Nat.lt_irrefl m) (mem_mergePool.1 h).1
        have hsubpool : insert m (mergePool C G c m) ⊆ mergePool C G c (m + 1) :=
          Finset.insert_subset_iff.2 ⟨hnew, hpool⟩
        have hinc := Finset.card_le_card hsubpool
        rw [Finset.card_insert_of_notMem hn] at hinc
        change T.card ≤ (roots.erase (n + m)).card + P.card at hTcard
        omega
      · have hinc := Finset.card_le_card hpool
        change T.card ≤ (roots.erase (n + m)).card + P.card at hTcard
        omega
    · have hnew : ∀ w ∈ roots, 1 < (singletonSupport n C w).card → w < n + m := by
        intro w hw hw'
        have hlt := hbound w hw hw'
        have hne : w ≠ n + m := fun he => htop ⟨he ▸ hw, he ▸ hw'⟩
        omega
      have hfirst := ih roots hvalid hadj hnew
      have hinc := Finset.card_le_card hpool
      omega


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


lemma graph_budget {n : ℕ} {C : Circuit} (G : SimpleGraph (Fin n)) (seed : Fin n)
    (hm : Monotone2 C) (rb : ReadsBack n C)
    (hsafe : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      ∀ u v, gateVal n C k (pairInput u v) = true → G.Adj u v)
    (hempty : ∀ k, reachable n C k → (gateAt C k).op = GateOp.and →
      gateVal n C k (fun _ => false) = false)
    (hcommon : ∀ c d v w : Fin n, c ≠ d → v ≠ w →
      G.Adj c v → G.Adj c w → G.Adj d v → G.Adj d w → False)
    (hout : singletonSupport n C C.output = ∅)
    (hpair : ∀ u v, G.Adj u v → C.eval (List.ofFn (pairInput u v)) = true)
    (E : Finset (Fin n × Fin n))
    (hE : ∀ p ∈ E, G.Adj p.1 p.2 ∧ p.1 ≤ p.2) :
    ∃ T : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T) ∧
      T.card ≤ (births n C).card ∧ E.card + (births n C).card ≤ C.size + 1 := by
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
  have cover (u v) (huv : G.Adj u v) :
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
  let leaves (u : Fin n) := (roots u).biUnion (singletonSupport n C)
  have hcov : ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T := by
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
    · exact Finset.mem_image.2 ⟨v, Finset.mem_biUnion.2 ⟨w k, hroot, h⟩, by rwa [← he]⟩
    · exact Finset.mem_image.2 ⟨u, Finset.mem_biUnion.2 ⟨w k, hroot, h⟩, by rwa [← he, edgeKey_comm]⟩
  have hleaf (t : Fin n) : (leaves t).card ≤ (fiber t).card +
      (mergePool C G t C.gates.length).card := by
    have hr (a) (ha : a ∈ roots t) : ∃ k ∈ B, c k = t ∧ w k = a := by
      obtain ⟨k, hk, he⟩ := Finset.mem_image.1 ha
      exact ⟨k, (Finset.mem_filter.1 hk).1, (Finset.mem_filter.1 hk).2, he⟩
    have h := leaf_budget (G := G) (c := t) hm rb hclean C.gates.length (roots t) (by
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
  have hdisjPool : (T : Set (Fin n)).PairwiseDisjoint (fun t => mergePool C G t C.gates.length) := by
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro k hka hkb
    obtain ⟨_, hk, ha⟩ := mem_mergePool.1 hka
    have hb := (mem_mergePool.1 hkb).2.2
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 (mem_merges.1 hk).2.2.1
    exact hcommon a b u v hab huv (ha u hu) (ha v hv) (hb u hu) (hb v hv)
  have hsumL : (∑ t ∈ T, (mergePool C G t C.gates.length).card) ≤ (merges n C).card := by
    rw [← Finset.card_biUnion hdisjPool]
    apply Finset.card_le_card
    intro k hk
    obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.1 hk
    exact (mem_mergePool.1 ht).2.1
  have hEL : E.card ≤ B.card + (merges n C).card := by
    calc
      _ ≤ (T.biUnion fun t => (leaves t).image (edgeKey t)).card := Finset.card_le_card hEsub
      _ ≤ ∑ t ∈ T, ((leaves t).image (edgeKey t)).card := Finset.card_biUnion_le
      _ ≤ ∑ t ∈ T, (leaves t).card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
      _ ≤ ∑ t ∈ T, ((fiber t).card + (mergePool C G t C.gates.length).card) :=
        Finset.sum_le_sum fun t _ => hleaf t
      _ ≤ _ := by rw [Finset.sum_add_distrib, hsumB]; exact Nat.add_le_add_left hsumL _
  have hgate := gate_budget hm rb hclean
  change 2 * B.card + (merges n C).card ≤ C.size + 1 at hgate
  exact ⟨T, hcov, Finset.card_image_le, by change E.card + B.card ≤ C.size + 1; omega⟩

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

lemma clean_graph_budget {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hfour : NoFourCycle G) (hne : G.edgeFinset.Nonempty)
    (hC : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) :
    ∃ T : Finset (Fin n), G.IsVertexCover ↑T ∧ G.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  obtain ⟨e, he⟩ := hne
  induction e using Sym2.ind with
  | _ u v =>
    have hm : Monotone2 C := by
      intro g hg
      exact ⟨by simpa using hC.1 g hg, (hC.2.2 g hg).le⟩
    obtain ⟨E, hcard, hE⟩ := sorted_edges G
    obtain ⟨T, hcover, hT, hbound⟩ := graph_budget (C := C) G u hm hC.2.1
      (fun j hj hop a b ht => edge_true_pair.1 (graph_true.1 (hclean j hj.1 hop _ ht)))
      (by
        intro j hj hop
        cases h : gateVal n C j (fun _ => false)
        · rfl
        · obtain ⟨a, b, hab, ha, hb⟩ := graph_true.1 (hclean j hj.1 hop _ h)
          cases ha)
      (fun _ _ _ _ => no_four_cycle hfour)
      (by
        apply Finset.eq_empty_iff_forall_notMem.2
        intro a ha
        have hh : circuitFun n C (pairInput a a) = true := mem_support.1 ha
        rw [hfun] at hh
        exact G.irrefl (edge_true_pair.1 (graph_true.1 hh)))
      (by
        intro a b hab
        change circuitFun n C (pairInput a b) = true
        rw [hfun]
        exact graph_true.2 (edge_true_pair.2 hab)) E hE
    refine ⟨T, hcover, ?_⟩
    omega

end CleanBudget

namespace CleanBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma graph_budget_relative {n : ℕ} {C : Circuit} (G H : SimpleGraph (Fin n)) (seed : Fin n)
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
    (hE : ∀ p ∈ E, H.Adj p.1 p.2 ∧ p.1 ≤ p.2) :
    ∃ T : Finset (Fin n), (∀ u v, H.Adj u v → u ∈ T ∨ v ∈ T) ∧
      T.card ≤ (births n C).card ∧ E.card + (births n C).card ≤ C.size + 1 := by
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
  let leaves (u : Fin n) := (roots u).biUnion (singletonSupport n C)
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
    · exact Finset.mem_image.2 ⟨v, Finset.mem_biUnion.2 ⟨w k, hroot, h⟩, by rwa [← he]⟩
    · exact Finset.mem_image.2 ⟨u, Finset.mem_biUnion.2 ⟨w k, hroot, h⟩, by rwa [← he, edgeKey_comm]⟩
  have hleaf (t : Fin n) : (leaves t).card ≤ (fiber t).card +
      (mergePool C G t C.gates.length).card := by
    have hr (a) (ha : a ∈ roots t) : ∃ k ∈ B, c k = t ∧ w k = a := by
      obtain ⟨k, hk, he⟩ := Finset.mem_image.1 ha
      exact ⟨k, (Finset.mem_filter.1 hk).1, (Finset.mem_filter.1 hk).2, he⟩
    have h := leaf_budget (G := G) (c := t) hm rb hclean C.gates.length (roots t) (by
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
  have hdisjPool : (T : Set (Fin n)).PairwiseDisjoint (fun t => mergePool C G t C.gates.length) := by
    intro a _ b _ hab
    rw [Function.onFun, Finset.disjoint_left]
    intro k hka hkb
    obtain ⟨_, hk, ha⟩ := mem_mergePool.1 hka
    have hb := (mem_mergePool.1 hkb).2.2
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.1 (mem_merges.1 hk).2.2.1
    exact hcommon a b u v hab huv (ha u hu) (ha v hv) (hb u hu) (hb v hv)
  have hsumL : (∑ t ∈ T, (mergePool C G t C.gates.length).card) ≤ (merges n C).card := by
    rw [← Finset.card_biUnion hdisjPool]
    apply Finset.card_le_card
    intro k hk
    obtain ⟨t, _, ht⟩ := Finset.mem_biUnion.1 hk
    exact (mem_mergePool.1 ht).2.1
  have hEL : E.card ≤ B.card + (merges n C).card := by
    calc
      _ ≤ (T.biUnion fun t => (leaves t).image (edgeKey t)).card := Finset.card_le_card hEsub
      _ ≤ ∑ t ∈ T, ((leaves t).image (edgeKey t)).card := Finset.card_biUnion_le
      _ ≤ ∑ t ∈ T, (leaves t).card := Finset.sum_le_sum fun _ _ => Finset.card_image_le
      _ ≤ ∑ t ∈ T, ((fiber t).card + (mergePool C G t C.gates.length).card) :=
        Finset.sum_le_sum fun t _ => hleaf t
      _ ≤ _ := by rw [Finset.sum_add_distrib, hsumB]; exact Nat.add_le_add_left hsumL _
  have hgate := gate_budget hm rb hclean
  change 2 * B.card + (merges n C).card ≤ C.size + 1 at hgate
  exact ⟨T, hcov, Finset.card_image_le, by change E.card + B.card ≤ C.size + 1; omega⟩

lemma relative_clean_graph_budget {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (C : Circuit)
    (_hHG : H ≤ G) (hfour : NoFourCycle G) (hC : IsAO2 n C)
    (hsafe : ∀ x, circuitFun n C x = true → graphFun G ∅ x = true)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j)
    (hpair : ∀ u v, H.Adj u v → circuitFun n C (pairInput u v) = true) :
    ∃ T : Finset (Fin n), H.IsVertexCover ↑T ∧ H.edgeFinset.card + T.card ≤ C.size + 1 := by
  classical
  by_cases hne : H.edgeFinset.Nonempty
  · obtain ⟨e, he⟩ := hne
    induction e using Sym2.ind with
    | _ u v =>
      have hm : Monotone2 C := by
        intro g hg
        exact ⟨by simpa using hC.1 g hg, (hC.2.2 g hg).le⟩
      obtain ⟨E, hcard, hE⟩ := sorted_edges H
      obtain ⟨T, hcover, hT, hbound⟩ := graph_budget_relative (C := C) G H u hm hC.2.1
        (fun j hj hop a b ht => edge_true_pair.1 (graph_true.1 (hclean j hj.1 hop _ ht)))
        (by
          intro j hj hop
          cases h : gateVal n C j (fun _ => false)
          · rfl
          · obtain ⟨a, b, hab, ha, hb⟩ := graph_true.1 (hclean j hj.1 hop _ h)
            cases ha)
        (fun _ _ _ _ => no_four_cycle hfour)
        (by
          apply Finset.eq_empty_iff_forall_notMem.2
          intro a ha
          have hh : circuitFun n C (pairInput a a) = true := mem_support.1 ha
          exact G.irrefl (edge_true_pair.1 (graph_true.1 (hsafe _ hh))))
        hpair E hE
      refine ⟨T, hcover, ?_⟩
      omega
  · have hempty : H.edgeFinset = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    refine ⟨∅, ?_, by simp [hempty]⟩
    intro u v huv
    have he : s(u, v) ∈ H.edgeFinset := SimpleGraph.mem_edgeFinset.mpr huv
    rw [hempty] at he
    exact False.elim (Finset.notMem_empty _ he)

end CleanBudget

namespace PrefixReuse
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CircuitMoves

lemma erase_safe_or_copy_set {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (U : Finset ℕ) (b p : ℕ) : ∀ C : Circuit, IsAO2 n C →
    circuitFun n C = graphFun G ∅ →
    (∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) →
    (∀ k ∈ U, k < C.gates.length) → (∀ k ∈ U, b ≤ n + k) → p < b →
    (∀ x : Fin n → Bool, val C (List.ofFn x) p = true → graphFun G ∅ x = true) →
    (∀ k ∈ U,
      (∀ x : Fin n → Bool, val C (List.ofFn x) (n + k) = true → val C (List.ofFn x) p = true) ∨
      ∃ q < b, ∀ x : Fin n → Bool, val C (List.ofFn x) q = val C (List.ofFn x) (n + k)) →
    ∃ D : Circuit, IsAO2 n D ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.size + U.card = C.size ∧ circuitFun n D = graphFun G ∅ := by
  classical
  induction U using Finset.strongInductionOn with
  | _ U ih =>
    intro C hAO hfun hclean hbound hcut hp hpsafe hcase
    by_cases hzero : U = ∅
    · exact ⟨C, hAO, hclean, by simp [hzero], hfun⟩
    have hne : U.Nonempty := Finset.nonempty_iff_ne_empty.mpr hzero
    let k := U.max' hne
    have hkU : k ∈ U := U.max'_mem hne
    have hk := hbound k hkU
    have hb := hcut k hkU
    obtain ⟨q, hq, hEAO, hEsize, hEfun, hEclean⟩ :
        ∃ q < b, IsAO2 n (eraseGate n C k q) ∧
          (eraseGate n C k q).size + 1 = C.size ∧
          circuitFun n (eraseGate n C k q) = graphFun G ∅ ∧
          (∀ j < (eraseGate n C k q).gates.length,
            (gateAt (eraseGate n C k q) j).op = GateOp.and → BelowF G (eraseGate n C k q) j) := by
      rcases hcase k hkU with hd | ⟨q, hq, heq⟩
      · exact ⟨p, hp, DominatedDelete.erase_dominated_ao_clean hAO hfun hk (by omega)
          hpsafe hd hclean⟩
      · obtain ⟨ha, hs, hf, hc⟩ := Duplicate.erase_equal_ao_clean hk (by omega) hAO heq hclean
        exact ⟨q, hq, ha, hs, hf.trans hfun, hc⟩
    let E := eraseGate n C k q
    have hlen : E.gates.length + 1 = C.gates.length := erase_length n C k q hk
    have hsmall : ∀ i ∈ U.erase k, i < k := by
      intro i hi
      obtain ⟨hne, hiU⟩ := Finset.mem_erase.mp hi
      have hmax := U.le_max' i hiU
      omega
    have hremain : ∀ i ∈ U.erase k, i < E.gates.length := by
      intro i hi
      have hlt := hsmall i hi
      omega
    have hcut' : ∀ i ∈ U.erase k, b ≤ n + i := fun i hi => hcut i (Finset.mem_of_mem_erase hi)
    have hlower (x : Fin n → Bool) (w : ℕ) (hw : w < n + k) :
        val E (List.ofFn x) w = val C (List.ofFn x) w :=
      Duplicate.erase_lower_value hk (by simp) hw
    have hpsafe' : ∀ x : Fin n → Bool, val E (List.ofFn x) p = true → graphFun G ∅ x = true := by
      intro x hx
      apply hpsafe x
      rwa [hlower x p (by omega)] at hx
    have hcase' : ∀ i ∈ U.erase k,
        (∀ x : Fin n → Bool, val E (List.ofFn x) (n + i) = true → val E (List.ofFn x) p = true) ∨
        ∃ r < b, ∀ x : Fin n → Bool, val E (List.ofFn x) r = val E (List.ofFn x) (n + i) := by
      intro i hi
      have hiK := hsmall i hi
      rcases hcase i (Finset.mem_of_mem_erase hi) with hd | ⟨r, hr, heq⟩
      · apply Or.inl
        intro x hx
        rw [hlower x (n + i) (by omega)] at hx
        rw [hlower x p (by omega)]
        exact hd x hx
      · apply Or.inr
        refine ⟨r, hr, ?_⟩
        intro x
        rw [hlower x r (by omega), hlower x (n + i) (by omega)]
        exact heq x
    obtain ⟨D, hDAO, hDclean, hDsize, hDfun⟩ :=
      ih (U.erase k) (Finset.erase_ssubset hkU) E hEAO hEfun hEclean hremain hcut' hp hpsafe' hcase'
    refine ⟨D, hDAO, hDclean, ?_, hDfun⟩
    have hcard := Finset.card_erase_add_one hkU
    change E.size + 1 = C.size at hEsize
    omega

end PrefixReuse

namespace SharedRepair
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma pure_or_shift_value {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hC : IsAO2 n C) (w : ℕ)
    (hno : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      ¬ Relation.ReflTransGen (Frontier.OrStep n C) w (n + j))
    (x : Fin n → Bool) :
    val (shared G B C) (List.ofFn x) (shiftWire n B.gates.length w) =
      val C (List.ofFn x) w := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hv
    rcases shared_or_trace G B C hC x w hv with ⟨t, ht, hxt⟩ | ⟨j, hj, hop, hr, _⟩
    · exact Frontier.reach_var_val x w t (Frontier.mem_orIn_reach t ht) hxt
    · exact False.elim (hno j hj hop (Frontier.orReaches_reach j _ hr).1)
  · intro hv
    obtain ⟨w', hr, hv', hlast⟩ := Frontier.or_trace (n := n) (by simp) w hv
    rcases hlast with hw | ⟨j, hj, rfl, hop⟩
    · apply shifted_or_path_value G B C hC x hr
      rw [shift_input n B.gates.length w' hw]
      have h₁ := val_ofFn C x ⟨w', hw⟩
      have h₂ := val_ofFn (shared G B C) x ⟨w', hw⟩
      exact h₂.trans (h₁.symm.trans hv')
    · have hand : (gateAt C j).op = GateOp.and :=
        (hC.1 _ (gateAt_mem hj)).resolve_right hop
      exact False.elim (hno j hj hand hr)

lemma pure_or_prefix_copy {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hC : IsAO2 n C) (j q : ℕ)
    (hno : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ Relation.ReflTransGen (Frontier.OrStep n C) (n + j) (n + k))
    (hcopy : ∀ x : Fin n → Bool, val B (List.ofFn x) q = val C (List.ofFn x) (n + j)) :
    ∀ x : Fin n → Bool, val B (List.ofFn x) q =
      val (shared G B C) (List.ofFn x) (n + (B.gates.length + j)) := by
  intro x
  rw [← shift_gate, pure_or_shift_value G B C hC (n + j) hno x]
  exact hcopy x

lemma pure_or_pool_copies {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hC : IsAO2 n C) (S : Finset ℕ)
    (hno : ∀ j ∈ S, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ Relation.ReflTransGen (Frontier.OrStep n C) (n + j) (n + k))
    (hcopy : ∀ j ∈ S, ∃ q < n + B.gates.length, ∀ x : Fin n → Bool,
      val B (List.ofFn x) q = val C (List.ofFn x) (n + j)) :
    ∀ j ∈ S, ∃ q < n + B.gates.length, ∀ x : Fin n → Bool,
      val B (List.ofFn x) q = val (shared G B C) (List.ofFn x) (n + (B.gates.length + j)) := by
  intro j hj
  obtain ⟨q, hq, heq⟩ := hcopy j hj
  exact ⟨q, hq, pure_or_prefix_copy G B C hC j q (hno j hj) heq⟩

end SharedRepair

namespace SourcePool
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge SharedRepair

lemma shared_absorb_reuse {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C) (hTop : TopForm G C)
    (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hCsafe : ∀ x, circuitFun n C x = true → graphFun G ∅ x = true)
    (hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j)
    (R S : Finset ℕ) (hdis : Disjoint R S)
    (hR : ∀ j ∈ R, j < C.gates.length ∧
      (Repair.dirty G C j ∨ (j ∈ tops G C ∧
        ∀ u ∈ side (n := n) C j 0, ∀ v ∈ side (n := n) C j 1,
          circuitFun n B (pairInput u v) = true)))
    (hS : ∀ j ∈ S, j < C.gates.length)
    (hcopy : ∀ j ∈ S, ∃ q < n + B.gates.length, ∀ x : Fin n → Bool,
      val B (List.ofFn x) q = val (shared G B C) (List.ofFn x) (n + (B.gates.length + j)))
    (hcover : ∀ u v : Fin n, G.Adj u v → circuitFun n (shared G B C) (pairInput u v) = true) :
    ∃ D : Circuit, IsAO2 n D ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.size + R.card + S.card = B.size + C.size ∧ circuitFun n D = graphFun G ∅ := by
  classical
  let U := (R ∪ S).image fun k => B.gates.length + k
  have hUcard : U.card = R.card + S.card := by
    rw [Finset.card_image_of_injOn (fun _ _ _ _ h => Nat.add_left_cancel h),
      Finset.card_union_of_disjoint hdis]
  obtain ⟨hAO, hsize, hsafe, hclean⟩ := shared_safe_clean G B C hB hC hBo hBsafe hCsafe hBclean
  have hfun : circuitFun n (shared G B C) = graphFun G ∅ := by
    apply eq_graphFun_of_boundary G (shared G B C) hAO hcover
    intro x hx
    apply Bool.eq_false_iff.mpr
    intro ht
    have hf := hsafe x ht
    rw [hx.1] at hf
    cases hf
  have hbound : ∀ k ∈ U, k < (shared G B C).gates.length := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    have hlen : j < C.gates.length := by
      rcases Finset.mem_union.mp hj with hj | hj
      · exact (hR j hj).1
      · exact hS j hj
    rw [shared_length]
    omega
  have hcut : ∀ k ∈ U, n + B.gates.length ≤ n + k := by
    intro k hk
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hk
    omega
  have hpsafe : ∀ x : Fin n → Bool,
      val (shared G B C) (List.ofFn x) B.output = true → graphFun G ∅ x = true := by
    intro x hx
    rw [prefix_value G B C x hBo] at hx
    exact hBsafe x hx
  have hcase : ∀ k ∈ U,
      (∀ x : Fin n → Bool, val (shared G B C) (List.ofFn x) (n + k) = true →
        val (shared G B C) (List.ofFn x) B.output = true) ∨
      ∃ q < n + B.gates.length, ∀ x : Fin n → Bool,
        val (shared G B C) (List.ofFn x) q = val (shared G B C) (List.ofFn x) (n + k) := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    rcases Finset.mem_union.mp hj with hj | hj
    · apply Or.inl
      intro x hx
      rw [prefix_value G B C x hBo]
      rcases (hR j hj).2 with hd | ⟨htop, hcross⟩
      · rwa [copied_value G B C hBo (hR j hj).1 hd x] at hx
      · exact shared_top_dominated_by_B G B C hB hC hTop hBo htop hcross x hx
    · apply Or.inr
      obtain ⟨q, hq, heq⟩ := hcopy j hj
      refine ⟨q, hq, ?_⟩
      intro x
      rw [prefix_value G B C x hq]
      exact heq x
  obtain ⟨D, hDAO, hDclean, hDsize, hDfun⟩ :=
    PrefixReuse.erase_safe_or_copy_set U (n + B.gates.length) B.output
      (shared G B C) hAO hfun hclean hbound hcut hBo hpsafe hcase
  refine ⟨D, hDAO, hDclean, ?_, hDfun⟩
  rw [hUcard, hsize] at hDsize
  omega

lemma shared_reuse_ustar_no_larger {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C) (hTop : TopForm G C)
    (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hfun : circuitFun n C = graphFun G ∅)
    (hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j)
    (hlive : ∀ a ∈ tops G C, OrReaches n C C.output a)
    (hU : ∀ u v : Fin n, s(u, v) ∈ Ustar G C → circuitFun n B (pairInput u v) = true)
    (K S : Finset ℕ) (hK : ∀ k ∈ K, k ∈ tops G C)
    (hcross : ∀ k ∈ K, ∀ u ∈ side (n := n) C k 0, ∀ v ∈ side (n := n) C k 1,
      circuitFun n B (pairInput u v) = true)
    (hdis : Disjoint (junk G C ∪ K) S)
    (hS : ∀ j ∈ S, j < C.gates.length)
    (hcopy : ∀ j ∈ S, ∃ q < n + B.gates.length, ∀ x : Fin n → Bool,
      val B (List.ofFn x) q = val (shared G B C) (List.ofFn x) (n + (B.gates.length + j)))
    (hcost : B.size ≤ (junk G C).card + K.card + S.card) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.size + (junk G C).card + K.card + S.card = B.size + C.size := by
  classical
  have hJK : Disjoint (junk G C) K := by
    apply Finset.disjoint_left.mpr
    intro k hkJ hkK
    exact (Labeling.junk_is_dirty hkJ).2 (Frontier.topData (hK k hkK)).2.2
  have hR : ∀ j ∈ junk G C ∪ K, j < C.gates.length ∧
      (Repair.dirty G C j ∨ (j ∈ tops G C ∧
        ∀ u ∈ side (n := n) C j 0, ∀ v ∈ side (n := n) C j 1,
          circuitFun n B (pairInput u v) = true)) := by
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · exact ⟨(Frontier.junkData hj).1, Or.inl (Labeling.junk_is_dirty hj)⟩
    · exact ⟨(Frontier.topData (hK j hj)).1, Or.inr ⟨hK j hj, hcross j hj⟩⟩
  obtain ⟨D, hDAO, hDclean, hDsize, hDfun⟩ :=
    shared_absorb_reuse G B C hB hC hTop hBo hBsafe (fun x hx => by rwa [← hfun])
      hBclean (junk G C ∪ K) S hdis hR hS hcopy
      (shared_accepts_edges_of_ustar G B C hC hBo hfun hlive hU)
  rw [Finset.card_union_of_disjoint hJK] at hDsize
  exact ⟨D, hDAO, hDfun, by omega, hDclean, by omega⟩

end SourcePool

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

lemma graph_budget_excluded_merges {n : ℕ} {C : Circuit} (G H : SimpleGraph (Fin n)) [DecidableRel H.Adj] (seed : Fin n)
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
      T.card ≤ (births n C).card ∧ E.card + (births n C).card + S.card ≤ C.size + 1 := by
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
  have hgate := gate_budget hm rb hclean
  change 2 * B.card + (merges n C).card ≤ C.size + 1 at hgate
  exact ⟨T, hcov, Finset.card_image_le, by change E.card + B.card + S.card ≤ C.size + 1; omega⟩


lemma relative_clean_graph_budget_excluding_merges {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (C : Circuit)
    (_hHG : H ≤ G) (hfour : NoFourCycle G) (hC : IsAO2 n C)
    (hsafe : ∀ x, circuitFun n C x = true → graphFun G ∅ x = true)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j)
    (hpair : ∀ u v, H.Adj u v → circuitFun n C (pairInput u v) = true)
    (S : Finset ℕ) (hS : S ⊆ merges n C)
    (hskip : ∀ k ∈ S, ∀ c : Fin n,
      (∀ v ∈ singletonSupport n C (n + k), G.Adj c v) →
      (restrictedSupport n C (Finset.univ.filter (H.Adj c)) (n + k)).card ≤ 1) :
    ∃ T : Finset (Fin n), H.IsVertexCover ↑T ∧ H.edgeFinset.card + T.card + S.card ≤ C.size + 1 := by
  classical
  by_cases hne : H.edgeFinset.Nonempty
  · obtain ⟨e, he⟩ := hne
    induction e using Sym2.ind with
    | _ u v =>
      have hm : Monotone2 C := by
        intro g hg
        exact ⟨by simpa using hC.1 g hg, (hC.2.2 g hg).le⟩
      obtain ⟨E, hcard, hE⟩ := sorted_edges H
      obtain ⟨T, hcover, hT, hbound⟩ := graph_budget_excluded_merges (C := C) G H u hm hC.2.1
        (fun j hj hop a b ht => edge_true_pair.1 (graph_true.1 (hclean j hj.1 hop _ ht)))
        (by
          intro j hj hop
          cases h : gateVal n C j (fun _ => false)
          · rfl
          · obtain ⟨a, b, hab, ha, hb⟩ := graph_true.1 (hclean j hj.1 hop _ h)
            cases ha)
        (fun _ _ _ _ => no_four_cycle hfour)
        (by
          apply Finset.eq_empty_iff_forall_notMem.2
          intro a ha
          have hh : circuitFun n C (pairInput a a) = true := mem_support.1 ha
          exact G.irrefl (edge_true_pair.1 (graph_true.1 (hsafe _ hh))))
        hpair E hE S hS hskip
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
        exact Finset.mem_range.mpr (mem_merges.mp (hS hk)).1.1
      have hc : S.card ≤ C.size := by
        change S.card ≤ C.gates.length
        simpa only [Finset.card_range] using Finset.card_le_card hSrange
      simpa only [hempty, Finset.card_empty, Nat.zero_add] using hc.trans (Nat.le_succ _)


lemma relative_clean_graph_budget_anchored_merges {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (C : Circuit)
    (hHG : H ≤ G) (hfour : NoFourCycle G) (hC : IsAO2 n C)
    (hsafe : ∀ x, circuitFun n C x = true → graphFun G ∅ x = true)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j)
    (hpair : ∀ u v, H.Adj u v → circuitFun n C (pairInput u v) = true)
    (S : Finset ℕ) (hS : S ⊆ merges n C)
    (hanchor : ∀ k ∈ S, ∃ a : Fin n,
      (∀ v ∈ singletonSupport n C (n + k), G.Adj a v) ∧
      (∀ v ∈ singletonSupport n C (n + k), ¬ H.Adj a v)) :
    ∃ T : Finset (Fin n), H.IsVertexCover ↑T ∧
      H.edgeFinset.card + T.card + S.card ≤ C.size + 1 := by
  classical
  apply relative_clean_graph_budget_excluding_merges G H C hHG hfour hC hsafe hclean hpair S hS
  intro k hk c hc
  obtain ⟨a, ha, hnot⟩ := hanchor k hk
  obtain ⟨u, hu, v, hv, huv⟩ := Finset.one_lt_card.mp (mem_merges.mp (hS hk)).2.2.1
  have hca : c = a := by
    by_contra hne
    exact no_four_cycle hfour hne huv (hc u hu) (hc v hv) (ha u hu) (ha v hv)
  subst c
  have hz : restrictedSupport n C (Finset.univ.filter (H.Adj a)) (n + k) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hvs, hvn⟩ := Finset.mem_inter.mp hv
    exact hnot v hvs (Finset.mem_filter.mp hvn).2
  rw [hz]
  simp

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

lemma relative_clean_graph_budget_lambda_clones {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (B C : Circuit)
    (hfour : NoFourCycle G) (hB : IsAO2 n B) (hC : IsAO2 n C)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j)
    (hpair : ∀ u v, H.Adj u v → circuitFun n B (pairInput u v) = true)
    (hHU : ∀ u v, H.Adj u v → s(u, v) ∈ Ustar G C)
    (S : Finset ℕ) (hS : S ⊆ merges n B)
    (hcopy : ∀ k ∈ S, ∃ j ∈ lam G C,
      singletonSupport n B (n + k) = orIn n C (n + j)) :
    ∃ T : Finset (Fin n), H.IsVertexCover ↑T ∧
      H.edgeFinset.card + T.card + S.card ≤ B.size + 1 := by
  classical
  have hHG : H ≤ G := by
    intro u v huv
    exact SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp (hHU u v huv)).1
  apply relative_clean_graph_budget_anchored_merges G H B hHG hfour hB hBsafe hBclean hpair S hS
  intro k hk
  obtain ⟨j, hj, heq⟩ := hcopy k hk
  obtain ⟨a, ha⟩ := lambda_raw_anchor hC hj
  refine ⟨a, ?_, ?_⟩
  · intro v hv
    rw [heq] at hv
    exact (ha v hv).1
  · intro v hv hadj
    rw [heq] at hv
    exact (Finset.mem_sdiff.mp (hHU a v hadj)).2 (ha v hv).2

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

namespace PEqualNP.Outside.L_meta_2583.CleanBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CircuitMoves

lemma pure_or_val_iff {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {w : ℕ}
    (hno : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ Relation.ReflTransGen (Frontier.OrStep n C) w (n + k)) (x : Fin n → Bool) :
    val C (List.ofFn x) w = true ↔ ∃ v ∈ orIn n C w, x v = true := by
  constructor
  · intro hv
    obtain ⟨w', hr, hv', hlast⟩ := Frontier.or_trace (n := n) (by simp) w hv
    rcases hlast with hw | ⟨k, hk, rfl, hop⟩
    · refine ⟨⟨w', hw⟩, Frontier.reach_mem_orIn ⟨w', hw⟩ hr, ?_⟩
      exact (Frontier.val_ofFn C x ⟨w', hw⟩).symm.trans hv'
    · exact False.elim (hno k hk ((hC.1 _ (gateAt_mem hk)).resolve_right hop) hr)
  · rintro ⟨v, hv, hx⟩
    exact Frontier.reach_var_val x w v (Frontier.mem_orIn_reach v hv) hx

lemma pure_or_singleton_support {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {w : ℕ}
    (hno : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ Relation.ReflTransGen (Frontier.OrStep n C) w (n + k)) :
    singletonSupport n C w = orIn n C w := by
  classical
  ext v
  rw [mem_support, pure_or_val_iff hC hno]
  simp [pairInput]

lemma pure_or_support_nonempty {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {w : ℕ}
    (hw : w < n + C.gates.length)
    (hno : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ Relation.ReflTransGen (Frontier.OrStep n C) w (n + k)) :
    (orIn n C w).Nonempty := by
  obtain ⟨v, hv, _⟩ := (pure_or_val_iff hC hno (fun _ => true)).mp
    (Completion.ao2_all_true C hC w hw)
  exact ⟨v, hv⟩

lemma minimum_no_equal_earlier_wire {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hmin : IsLeastAO G C) {j p : ℕ} (hj : j < C.gates.length)
    (hp : p < n + j) :
    ¬ (∀ x : Fin n → Bool, val C (List.ofFn x) p = val C (List.ofFn x) (n + j)) := by
  intro heq
  have hAO := erase_isAO2 n C j p hj hp hmin.1
  have hfun := (Duplicate.erase_equal_circuit hj hp heq).trans hmin.2.1
  have hle := hmin.2.2 _ hAO hfun
  have hsize := erase_size n C j p hj
  omega

lemma minimum_pure_or_support_card {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hmin : IsLeastAO G C) {j : ℕ} (hj : j < C.gates.length)
    (hno : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ Relation.ReflTransGen (Frontier.OrStep n C) (n + j) (n + k)) :
    1 < (orIn n C (n + j)).card := by
  classical
  have hne := pure_or_support_nonempty hmin.1 (by omega : n + j < n + C.gates.length) hno
  by_contra! hc
  have hcard : (orIn n C (n + j)).card = 1 := by
    have hpos := Finset.card_pos.mpr hne
    omega
  obtain ⟨v, hv⟩ := Finset.card_eq_one.mp hcard
  apply minimum_no_equal_earlier_wire hmin hj (show v.val < n + j by omega)
  intro x
  apply Bool.eq_iff_iff.mpr
  rw [val_ofFn, pure_or_val_iff hmin.1 hno, hv]
  simp

lemma pure_or_equal_of_support {n : ℕ} {C : Circuit} (hC : IsAO2 n C) {w z : ℕ}
    (hnoW : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ Relation.ReflTransGen (Frontier.OrStep n C) w (n + k))
    (hnoZ : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ Relation.ReflTransGen (Frontier.OrStep n C) z (n + k))
    (heq : orIn n C w = orIn n C z) (x : Fin n → Bool) :
    val C (List.ofFn x) w = val C (List.ofFn x) z := by
  apply Bool.eq_iff_iff.mpr
  rw [pure_or_val_iff hC hnoW, pure_or_val_iff hC hnoZ, heq]

lemma minimum_pure_or_support_injective {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hmin : IsLeastAO G C) {j k : ℕ}
    (hj : j < C.gates.length) (hk : k < C.gates.length)
    (hnoJ : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and →
      ¬ Relation.ReflTransGen (Frontier.OrStep n C) (n + j) (n + i))
    (hnoK : ∀ i < C.gates.length, (gateAt C i).op = GateOp.and →
      ¬ Relation.ReflTransGen (Frontier.OrStep n C) (n + k) (n + i))
    (heq : orIn n C (n + j) = orIn n C (n + k)) : j = k := by
  rcases lt_trichotomy j k with hlt | he | hgt
  · exact False.elim (minimum_no_equal_earlier_wire hmin hk (by omega)
      (pure_or_equal_of_support hmin.1 hnoJ hnoK heq))
  · exact he
  · exact False.elim (minimum_no_equal_earlier_wire hmin hj (by omega)
      (pure_or_equal_of_support hmin.1 hnoK hnoJ heq.symm))

lemma minimum_pure_or_support_injOn {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hmin : IsLeastAO G C) (S : Finset ℕ)
    (hbound : ∀ j ∈ S, j < C.gates.length)
    (hpure : ∀ j ∈ S, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ Relation.ReflTransGen (Frontier.OrStep n C) (n + j) (n + k)) :
    Set.InjOn (fun j => orIn n C (n + j)) ↑S := by
  intro j hj k hk heq
  exact minimum_pure_or_support_injective hmin (hbound j hj) (hbound k hk)
    (hpure j hj) (hpure k hk) heq

end PEqualNP.Outside.L_meta_2583.CleanBudget

namespace PEqualNP.Outside.L_meta_2583.CleanBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma pure_lambda_clone_cancellation {n : ℕ} (G H : SimpleGraph (Fin n))
    [DecidableRel G.Adj] [DecidableRel H.Adj] (B C : Circuit)
    (hfour : NoFourCycle G) (hB : IsAO2 n B) (hmin : IsLeastAO G C)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hBclean : ∀ k < B.gates.length, (gateAt B k).op = GateOp.and → BelowF G B k)
    (hpair : ∀ u v, H.Adj u v → circuitFun n B (pairInput u v) = true)
    (hHU : ∀ u v, H.Adj u v → s(u, v) ∈ Ustar G C)
    (S : Finset ℕ) (hS : S ⊆ lam G C)
    (hpure : ∀ j ∈ S, ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      ¬ Relation.ReflTransGen (Frontier.OrStep n C) (n + j) (n + k))
    (hcopy : ∀ j ∈ S, ∃ q < n + B.gates.length, ∀ x : Fin n → Bool,
      val B (List.ofFn x) q = val C (List.ofFn x) (n + j)) :
    ∃ T : Finset (Fin n), H.IsVertexCover ↑T ∧
      H.edgeFinset.card + T.card + S.card ≤ B.size + 1 := by
  classical
  have hbound : ∀ j ∈ S, j < C.gates.length := by
    intro j hj
    have hN := (Finset.mem_filter.mp (hS hj)).1
    have hdata : j < C.gates.length ∧ (gateAt C j).op = GateOp.or ∧ ¬ BelowF G C j := by
      simpa only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] using hN
    exact hdata.1
  have holdlarge (j : ℕ) (hj : j ∈ S) : 1 < (orIn n C (n + j)).card :=
    minimum_pure_or_support_card hmin (hbound j hj) (hpure j hj)
  have holdinj := minimum_pure_or_support_injOn hmin S hbound hpure
  have hex : ∀ j ∈ S, ∃ k < B.gates.length,
      singletonSupport n B (n + k) = orIn n C (n + j) := by
    intro j hj
    obtain ⟨q, hq, heq⟩ := hcopy j hj
    have hs : singletonSupport n B q = orIn n C (n + j) := by
      rw [← pure_or_singleton_support hmin.1 (hpure j hj)]
      ext v
      rw [mem_support, mem_support, heq]
    have hqn : n ≤ q := by
      by_contra hn
      have hinput := support_input (C := B) (⟨q, by omega⟩ : Fin n)
      have hc := holdlarge j hj
      rw [← hs, hinput] at hc
      simp at hc
    refine ⟨q - n, by omega, ?_⟩
    simpa only [show n + (q - n) = q by omega] using hs
  let f (j : ℕ) := if hj : j ∈ S then (hex j hj).choose else 0
  have hf (j : ℕ) (hj : j ∈ S) : f j < B.gates.length ∧
      singletonSupport n B (n + f j) = orIn n C (n + j) := by
    simpa only [f, dite_eq_left hj] using (hex j hj).choose_spec
  have hfinj : Set.InjOn f (S : Set ℕ) := by
    intro j hj k hk heq
    apply holdinj hj hk
    change orIn n C (n + j) = orIn n C (n + k)
    rw [← (hf j hj).2, ← (hf k hk).2, heq]
  let M := S.image f
  have hMcard : M.card = S.card := Finset.card_image_of_injOn hfinj
  have hMbound : ∀ k ∈ M, k < B.gates.length := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    exact (hf j hj).1
  have hMlarge : ∀ k ∈ M, 1 < (singletonSupport n B (n + k)).card := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    rw [(hf j hj).2]
    exact holdlarge j hj
  have hMinj : Set.InjOn (fun k => singletonSupport n B (n + k)) (M : Set ℕ) := by
    intro k hk l hl heq
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hl
    change singletonSupport n B (n + f j) = singletonSupport n B (n + f i) at heq
    rw [(hf j hj).2, (hf i hi).2] at heq
    exact congrArg f (holdinj hj hi heq)
  have hanchor : ∀ k ∈ M, ∃ a : Fin n,
      (∀ v ∈ singletonSupport n B (n + k), G.Adj a v) ∧
      (∀ v ∈ singletonSupport n B (n + k), ¬ H.Adj a v) := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨a, ha⟩ := lambda_raw_anchor hmin.1 (hS hj)
    refine ⟨a, ?_, ?_⟩
    · intro v hv
      rw [(hf j hj).2] at hv
      exact (ha v hv).1
    · intro v hv hadj
      rw [(hf j hj).2] at hv
      exact (Finset.mem_sdiff.mp (hHU a v hadj)).2 (ha v hv).2
  obtain ⟨T, hT, hbudget⟩ := relative_clean_graph_budget_distinct_sources G H B hfour hB
    hBsafe hBclean hpair M hMbound hMlarge hMinj hanchor
  exact ⟨T, hT, by rwa [hMcard] at hbudget⟩

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

lemma shared_equal_or_signatures {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hC : IsAO2 n C) (hBo : B.output < n + B.gates.length)
    (w v : ℕ)
    (hw : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      OrReaches n C w j → Repair.dirty G C j)
    (hv : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      OrReaches n C v j → Repair.dirty G C j)
    (hraw : orIn n C w = orIn n C v)
    (hflag : (∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ OrReaches n C w j) ↔
      ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ OrReaches n C v j)
    (x : Fin n → Bool) :
    val (shared G B C) (List.ofFn x) (shiftWire n B.gates.length w) =
      val (shared G B C) (List.ofFn x) (shiftWire n B.gates.length v) := by
  apply Bool.eq_iff_iff.mpr
  rw [shared_or_signature G B C hC hBo w hw x,
    shared_or_signature G B C hC hBo v hv x, hraw, hflag]

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

lemma shared_equal_lambda_signatures {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hC : IsAO2 n C) (hT : TopForm G C)
    (hBo : B.output < n + B.gates.length) {k l : ℕ}
    (hk : k ∈ lam G C) (hl : l ∈ lam G C)
    (hraw : orIn n C (n + k) = orIn n C (n + l))
    (hflag : (∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ OrReaches n C (n + k) j) ↔
      ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ OrReaches n C (n + l) j)
    (x : Fin n → Bool) :
    val (shared G B C) (List.ofFn x) (n + (B.gates.length + k)) =
      val (shared G B C) (List.ofFn x) (n + (B.gates.length + l)) := by
  simpa only [shift_gate] using shared_equal_or_signatures G B C hC hBo (n + k) (n + l)
    (lambda_or_boundaries_dirty G C hC hT hk)
    (lambda_or_boundaries_dirty G C hC hT hl) hraw hflag x

end PEqualNP.Outside.L_meta_2583.SharedRepair

namespace PEqualNP.Outside.L_meta_2583.SharedRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge

noncomputable def orSignature (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) × Bool := by
  classical
  exact (orIn n C w,
    decide (∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ OrReaches n C w j))

lemma orSignature_eq_iff {n : ℕ} {C : Circuit} {w v : ℕ} :
    orSignature n C w = orSignature n C v ↔ orIn n C w = orIn n C v ∧
      ((∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ OrReaches n C w j) ↔
        ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ OrReaches n C v j) := by
  classical
  simp [orSignature]

lemma shared_collapse_lambda_signatures {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C) (hTop : TopForm G C)
    (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hCsafe : ∀ x, circuitFun n C x = true → graphFun G ∅ x = true)
    (hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j)
    (T : Finset ℕ) (hT : T ⊆ lam G C) :
    ∃ D : Circuit, IsAO2 n D ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      circuitFun n D = circuitFun n (shared G B C) ∧
      D.size + (junk G C).card + T.card = B.size + C.size +
        (T.image fun k => orSignature n C (n + k)).card := by
  classical
  let label := fun k => orSignature n C (n + k)
  obtain ⟨R, hRT, hRcard, hrepresent⟩ := Duplicate.minimum_label_representatives T label
  let S := junk G C ∪ (T \ R)
  let Q := S.image fun k => B.gates.length + k
  have hTdata : ∀ k ∈ T, k < C.gates.length ∧ (gateAt C k).op = GateOp.or := by
    intro k hk
    have h := (Finset.mem_filter.mp (hT hk)).1
    simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at h
    exact ⟨h.1, h.2.1⟩
  obtain ⟨hAO, hsize, _, hclean⟩ := shared_safe_clean G B C hB hC hBo hBsafe hCsafe hBclean
  have hred : ∀ k ∈ Q, k < (shared G B C).gates.length ∧ ∃ p < n + k,
      ∀ x : Fin n → Bool, val (shared G B C) (List.ofFn x) p =
        val (shared G B C) (List.ofFn x) (n + k) := by
    intro k hk
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hk
    rcases Finset.mem_union.mp hj with hj | hj
    · have hjlen := (Frontier.junkData hj).1
      refine ⟨by rw [shared_length]; omega, B.output, by omega, ?_⟩
      intro x
      rw [prefix_value G B C x hBo, copied_value G B C hBo hjlen (Labeling.junk_is_dirty hj) x]
      rfl
    · have hjT := (Finset.mem_sdiff.mp hj).1
      have hjlen := (hTdata j hjT).1
      obtain ⟨i, hiT, hij, he⟩ := hrepresent j hj
      obtain ⟨hraw, hflag⟩ := orSignature_eq_iff.mp he
      refine ⟨by rw [shared_length]; omega, n + (B.gates.length + i), by omega, ?_⟩
      intro x
      exact shared_equal_lambda_signatures G B C hC hTop hBo (hT hiT) (hT hjT) hraw hflag x
  obtain ⟨D, hDAO, hDclean, hDsize, hDfun⟩ :=
    Duplicate.collapse_redundant_set Q (shared G B C) hAO hclean hred
  have hdis : Disjoint (junk G C) (T \ R) := by
    apply Finset.disjoint_left.mpr
    intro k hkJ hkS
    have ha := (Frontier.junkData hkJ).2.1
    have ho := (hTdata k (Finset.mem_sdiff.mp hkS).1).2
    cases ha.symm.trans ho
  have hScard : S.card = (junk G C).card + (T \ R).card := Finset.card_union_of_disjoint hdis
  have hQcard : Q.card = S.card := Finset.card_image_of_injective _ (by intro a b h; exact Nat.add_left_cancel h)
  have hTR : (T \ R).card + R.card = T.card := Finset.card_sdiff_add_card_eq_card hRT
  refine ⟨D, hDAO, hDclean, hDfun, ?_⟩
  change D.size + (junk G C).card + T.card = B.size + C.size + (T.image label).card
  omega

end PEqualNP.Outside.L_meta_2583.SharedRepair

/-! Mixed-source copies retain the same large-support cost. Singleton sources
whose input is implied by the repair can instead be redirected to that raw input.
A star circuit gives a repair with one gate per leaf. -/

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

namespace PEqualNP.Outside.L_meta_2583.SharedRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma shared_singleton_lambda_value {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hC : IsAO2 n C) (hTop : TopForm G C)
    (hBo : B.output < n + B.gates.length) {j : ℕ} (hj : j ∈ lam G C)
    (v : Fin n) (hraw : orIn n C (n + j) = {v})
    (hdom : ∀ x, circuitFun n B x = true → x v = true) (x : Fin n → Bool) :
    val (shared G B C) (List.ofFn x) (n + (B.gates.length + j)) = x v := by
  apply Bool.eq_iff_iff.mpr
  have hs := shared_or_signature G B C hC hBo (n + j)
    (lambda_or_boundaries_dirty G C hC hTop hj) x
  rw [shift_gate, hraw] at hs
  rw [hs]
  simp only [Finset.mem_singleton, exists_eq_left]
  exact ⟨fun h => h.elim id (fun h => hdom x h.1), Or.inl⟩

lemma shared_reuse_singleton_lambda_no_larger {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C)
    (hTop : TopForm G C) (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hfun : circuitFun n C = graphFun G ∅)
    (hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j)
    (hlive : ∀ a ∈ tops G C, OrReaches n C C.output a)
    (hU : ∀ u v : Fin n, s(u, v) ∈ Ustar G C → circuitFun n B (pairInput u v) = true)
    (S : Finset ℕ) (hS : S ⊆ lam G C)
    (hraw : ∀ j ∈ S, ∃ v : Fin n, orIn n C (n + j) = {v} ∧
      ∀ x, circuitFun n B x = true → x v = true)
    (hcost : B.size ≤ (junk G C).card + (centreless G C).card + S.card) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.size + (junk G C).card + (centreless G C).card + S.card = B.size + C.size := by
  classical
  have hdata : ∀ j ∈ S, j < C.gates.length ∧ (gateAt C j).op = GateOp.or := by
    intro j hj
    have h := (Finset.mem_filter.mp (hS hj)).1
    simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at h
    exact ⟨h.1, h.2.1⟩
  have hK : ∀ j ∈ centreless G C, j ∈ tops G C := fun _ h => (Finset.mem_filter.mp h).1
  have hcross : ∀ j ∈ centreless G C, ∀ u ∈ side (n := n) C j 0,
      ∀ v ∈ side (n := n) C j 1, circuitFun n B (pairInput u v) = true := by
    intro j hj u hu v hv
    rcases (Finset.mem_filter.mp hj).2 with hz | hz
    · rw [hz] at hu
      exact False.elim (Finset.notMem_empty _ hu)
    · rw [hz] at hv
      exact False.elim (Finset.notMem_empty _ hv)
  have hdis : Disjoint (junk G C ∪ centreless G C) S := by
    apply Finset.disjoint_left.mpr
    intro j hj hjS
    have ha : (gateAt C j).op = GateOp.and := by
      rcases Finset.mem_union.mp hj with hj | hj
      · exact (Frontier.junkData hj).2.1
      · exact (Frontier.topData (hK j hj)).2.1
    have ho := (hdata j hjS).2
    cases ha.symm.trans ho
  have hcopy : ∀ j ∈ S, ∃ q < n + B.gates.length, ∀ x : Fin n → Bool,
      val B (List.ofFn x) q = val (shared G B C) (List.ofFn x) (n + (B.gates.length + j)) := by
    intro j hj
    obtain ⟨v, hv, hdom⟩ := hraw j hj
    refine ⟨v.val, by omega, ?_⟩
    intro x
    rw [val_ofFn, shared_singleton_lambda_value G B C hC hTop hBo (hS hj) v hv hdom x]
  have h := SourcePool.shared_reuse_ustar_no_larger G B C hB hC hTop hBo hBsafe hfun
    hBclean hlive hU (centreless G C) S hK hcross hdis (fun j hj => (hdata j hj).1) hcopy hcost
  simpa using h

end PEqualNP.Outside.L_meta_2583.SharedRepair

namespace PEqualNP.Outside.L_meta_2583.StarCompletion

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

def starHead {n : ℕ} (c v : Fin n) (vs : List (Fin n)) : Circuit :=
  let B := orTail ⟨[], v.val⟩ vs
  appendBinary n B GateOp.and c.val B.output

lemma starHead_spec {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c v : Fin n) (vs : List (Fin n)) (he : ∀ w ∈ v :: vs, G.Adj c w) :
    IsAO2 n (starHead c v vs) ∧
      (starHead c v vs).output < n + (starHead c v vs).gates.length ∧
      (starHead c v vs).size = (v :: vs).length ∧
      (∀ x : Fin n → Bool, circuitFun n (starHead c v vs) x =
        (x c && (v :: vs).any x)) ∧
      (∀ j < (starHead c v vs).gates.length,
        (gateAt (starHead c v vs) j).op = GateOp.and → BelowF G (starHead c v vs) j) := by
  let S : Circuit := ⟨[], v.val⟩
  let B := orTail S vs
  have hS : IsAO2 n S := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg; cases hg
    · intro j hj; simp [S] at hj
    · intro g hg; cases hg
  have hSo : S.output < n + S.gates.length := by simpa [S] using v.isLt
  have hB := orTail_ao_output S vs hS hSo
  have hcB : c.val < n + B.gates.length := by omega
  have hBfun (x : Fin n → Bool) : circuitFun n B x = (v :: vs).any x := by
    rw [orTail_fun S vs hSo]
    change (val S (List.ofFn x) v.val || vs.any x) = _
    rw [val_ofFn]
    rfl
  have hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j := by
    apply orTail_clean G S vs hSo
    intro j hj
    simp [S] at hj
  have hfun (x : Fin n → Bool) : circuitFun n (starHead c v vs) x =
      (x c && (v :: vs).any x) := by
    change circuitFun n (appendBinary n B GateOp.and c.val B.output) x = _
    rw [appendBinary_fun B GateOp.and c.val B.output hcB hB.2, val_ofFn]
    simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true]
    change (x c && circuitFun n B x) = _
    rw [hBfun]
  refine ⟨appendBinary_ao n B GateOp.and c.val B.output hB.1 (Or.inl rfl) hcB hB.2,
    appendBinary_output n B GateOp.and c.val B.output, ?_, hfun, ?_⟩
  · change (appendBinary n B GateOp.and c.val B.output).size = _
    rw [appendBinary_size, orTail_size]
    simp [S, Circuit.size]
  · apply appendBinary_clean G B GateOp.and c.val B.output hcB hB.2 hBclean
    intro _ x hx
    have h : circuitFun n (starHead c v vs) x = true := by
      change circuitFun n (appendBinary n B GateOp.and c.val B.output) x = true
      rw [appendBinary_fun B GateOp.and c.val B.output hcB hB.2]
      exact hx
    rw [hfun] at h
    obtain ⟨hxc, hAny⟩ : x c = true ∧ (v :: vs).any x = true := by simpa using h
    obtain ⟨w, hw, hxw⟩ := List.any_eq_true.mp hAny
    exact Repair.graph_true.mpr ⟨c, w, he w hw, hxc, hxw⟩

lemma exists_star_prefix {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n) (V : Finset (Fin n)) (hne : V.Nonempty)
    (he : ∀ v ∈ V, G.Adj c v) :
    ∃ B : Circuit, IsAO2 n B ∧ B.output < n + B.gates.length ∧ B.size = V.card ∧
      (∀ x : Fin n → Bool, circuitFun n B x = true ↔
        x c = true ∧ ∃ v ∈ V, x v = true) ∧
      (∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j) ∧
      (∀ x, circuitFun n B x = true → graphFun G ∅ x = true) ∧
      (∀ x, circuitFun n B x = true → x c = true) := by
  classical
  have hneList : V.toList ≠ [] := by simpa using hne.ne_empty
  cases hlist : V.toList with
  | nil => exact False.elim (hneList hlist)
  | cons v vs =>
    have hmem (w : Fin n) : w ∈ v :: vs ↔ w ∈ V := by rw [← hlist]; exact Finset.mem_toList
    obtain ⟨hB, hBo, hsize, hfun, hclean⟩ := starHead_spec G c v vs
      (fun w hw => he w ((hmem w).mp hw))
    have hiff (x : Fin n → Bool) : circuitFun n (starHead c v vs) x = true ↔
        x c = true ∧ ∃ w ∈ V, x w = true := by
      rw [hfun, Bool.and_eq_true, List.any_eq_true]
      simp only [hmem]
    refine ⟨starHead c v vs, hB, hBo, ?_, hiff, hclean, ?_, ?_⟩
    · rw [hsize, ← hlist, Finset.length_toList]
    · intro x hx
      obtain ⟨hc, w, hw, hxw⟩ := (hiff x).mp hx
      exact Repair.graph_true.mpr ⟨c, w, he w hw, hc, hxw⟩
    · intro x hx
      exact ((hiff x).mp hx).1

end PEqualNP.Outside.L_meta_2583.StarCompletion

namespace PEqualNP.Outside.L_meta_2583.CleanBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma full_pencil_excludes_lambda_raw {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hC : IsAO2 n C) (p : Fin n)
    (hfull : ∀ v, G.Adj p v → s(p, v) ∈ Ustar G C)
    {j : ℕ} (hj : j ∈ lam G C) : p ∉ orIn n C (n + j) := by
  intro hp
  obtain ⟨a, ha⟩ := lambda_raw_anchor hC hj
  obtain ⟨hadj, hstar⟩ := ha p hp
  have hswap : s(a, p) = s(p, a) := Sym2.eq_swap
  exact (Finset.mem_sdiff.mp (hfull a hadj.symm)).2 (hswap ▸ hstar)

end PEqualNP.Outside.L_meta_2583.CleanBudget

/-! Conditional source erasure preserves the safe repair wire. One final OR
restores all inputs accepted by that repair, allowing singleton sources and
pure/mixed copies with the same raw support to be removed together. -/

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


namespace PEqualNP.Outside.L_meta_2583.SharedRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma shared_collapse_lambda_raw_absorb {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C) (hTop : TopForm G C)
    (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hfun : circuitFun n C = graphFun G ∅)
    (hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j)
    (hlive : ∀ a ∈ tops G C, OrReaches n C C.output a)
    (hU : ∀ u v : Fin n, s(u, v) ∈ Ustar G C → circuitFun n B (pairInput u v) = true)
    (K : Finset ℕ) (hK : ∀ k ∈ K, k ∈ tops G C)
    (hcross : ∀ k ∈ K, ∀ u ∈ side (n := n) C k 0, ∀ v ∈ side (n := n) C k 1,
      circuitFun n B (pairInput u v) = true)
    (T : Finset ℕ) (hT : T ⊆ lam G C) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.size + (junk G C).card + K.card + T.card =
        B.size + C.size +
          ((T.filter fun k => 1 < (orIn n C (n + k)).card).image fun k => orIn n C (n + k)).card + 1 := by
  classical
  let label := fun k => orIn n C (n + k)
  let L := T.filter fun k => 1 < (orIn n C (n + k)).card
  have hLT : L ⊆ T := Finset.filter_subset _ _
  obtain ⟨R, hRL, hRcard, hrepresent⟩ := Duplicate.minimum_label_representatives L label
  have hRT : R ⊆ T := hRL.trans hLT
  let A := junk G C ∪ K
  let S := A ∪ (T \ R)
  let Q := S.image fun k => B.gates.length + k
  have hTdata : ∀ k ∈ T, k < C.gates.length ∧ (gateAt C k).op = GateOp.or := by
    intro k hk
    have h := (Finset.mem_filter.mp (hT hk)).1
    simp only [orN, gatesWhere, Finset.mem_filter, Finset.mem_range] at h
    exact ⟨h.1, h.2.1⟩
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
        have hf := shared_top_dominated_by_B G B C hB hC hTop hBo (hK j hj) (hcross j hj) x ht
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
  have hJKdis : Disjoint (junk G C) K := by
    apply Finset.disjoint_left.mpr
    intro k hj hk
    exact (Labeling.junk_is_dirty hj).2 (Frontier.topData (hK k hk)).2.2
  have hdis : Disjoint A (T \ R) := by
    apply Finset.disjoint_left.mpr
    intro k hkA hkT
    have ha := (hAdata k hkA).2
    have ho := (hTdata k (Finset.mem_sdiff.mp hkT).1).2
    cases ha.symm.trans ho
  have hAcard : A.card = (junk G C).card + K.card :=
    Finset.card_union_of_disjoint hJKdis
  have hScard : S.card = A.card + (T \ R).card := Finset.card_union_of_disjoint hdis
  have hQcard : Q.card = S.card :=
    Finset.card_image_of_injective _ (by intro a b h; exact Nat.add_left_cancel h)
  have hTR : (T \ R).card + R.card = T.card := Finset.card_sdiff_add_card_eq_card hRT
  have hDsize : D.size = E.size + 1 := StarCompletion.appendBinary_size n E GateOp.or B.output E.output
  refine ⟨D, hDAO, hDfun, hDclean, ?_⟩
  change D.size + (junk G C).card + K.card + T.card =
    B.size + C.size + (L.image label).card + 1
  omega


end PEqualNP.Outside.L_meta_2583.SharedRepair


namespace PEqualNP.Outside.L_meta_2583.SharedRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma shared_collapse_raw_semantics_absorb {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C) (hTop : TopForm G C)
    (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hfun : circuitFun n C = graphFun G ∅)
    (hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j)
    (hlive : ∀ a ∈ tops G C, OrReaches n C C.output a)
    (hU : ∀ u v : Fin n, s(u, v) ∈ Ustar G C → circuitFun n B (pairInput u v) = true)
    (K : Finset ℕ) (hK : ∀ k ∈ K, k ∈ tops G C)
    (hcross : ∀ k ∈ K, ∀ u ∈ side (n := n) C k 0, ∀ v ∈ side (n := n) C k 1,
      circuitFun n B (pairInput u v) = true)
    (T : Finset ℕ)
    (hTdata : ∀ k ∈ T, k < C.gates.length ∧ (gateAt C k).op = GateOp.or)
    (hrawval : ∀ j ∈ T, ∀ x : Fin n → Bool, circuitFun n B x = false →
      (val (shared G B C) (List.ofFn x) (n + (B.gates.length + j)) = true ↔
        ∃ v ∈ orIn n C (n + j), x v = true)) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.size + (junk G C).card + K.card + T.card =
        B.size + C.size +
          ((T.filter fun k => 1 < (orIn n C (n + k)).card).image fun k => orIn n C (n + k)).card + 1 := by
  classical
  let label := fun k => orIn n C (n + k)
  let L := T.filter fun k => 1 < (orIn n C (n + k)).card
  have hLT : L ⊆ T := Finset.filter_subset _ _
  obtain ⟨R, hRL, hRcard, hrepresent⟩ := Duplicate.minimum_label_representatives L label
  have hRT : R ⊆ T := hRL.trans hLT
  let A := junk G C ∪ K
  let S := A ∪ (T \ R)
  let Q := S.image fun k => B.gates.length + k
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
        have hf := shared_top_dominated_by_B G B C hB hC hTop hBo (hK j hj) (hcross j hj) x ht
        rw [hBx] at hf
        cases hf
    · have hjT := (Finset.mem_sdiff.mp hj).1
      by_cases hjL : j ∈ L
      · obtain ⟨i, hiL, hij, he⟩ := hrepresent j
          (Finset.mem_sdiff.mpr ⟨hjL, (Finset.mem_sdiff.mp hj).2⟩)
        refine ⟨n + (B.gates.length + i), by omega, ?_⟩
        intro x hBx
        rw [prefix_value G B C x hBo] at hBx
        apply Bool.eq_iff_iff.mpr
        rw [hrawval i (hLT hiL) x hBx, hrawval j hjT x hBx]
        change orIn n C (n + i) = orIn n C (n + j) at he
        rw [he]
      · have hsmall : (orIn n C (n + j)).card ≤ 1 := by
          have hn : ¬ 1 < (orIn n C (n + j)).card :=
            fun h => hjL (Finset.mem_filter.mpr ⟨hjT, h⟩)
          omega
        by_cases hzero : orIn n C (n + j) = ∅
        · refine ⟨B.output, by omega, ?_⟩
          intro x hBx
          rw [prefix_value G B C x hBo] at hBx ⊢
          apply Bool.eq_iff_iff.mpr
          rw [hrawval j hjT x hBx]
          simp [hBx, hzero]
        · have hpos := Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr hzero)
          obtain ⟨v, hv⟩ := Finset.card_eq_one.mp
            (show (orIn n C (n + j)).card = 1 by omega)
          refine ⟨v.val, by omega, ?_⟩
          intro x hBx
          rw [prefix_value G B C x hBo] at hBx
          rw [val_ofFn]
          apply Bool.eq_iff_iff.mpr
          rw [hrawval j hjT x hBx]
          simp [hv]
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
  have hJKdis : Disjoint (junk G C) K := by
    apply Finset.disjoint_left.mpr
    intro k hj hk
    exact (Labeling.junk_is_dirty hj).2 (Frontier.topData (hK k hk)).2.2
  have hdis : Disjoint A (T \ R) := by
    apply Finset.disjoint_left.mpr
    intro k hkA hkT
    have ha := (hAdata k hkA).2
    have ho := (hTdata k (Finset.mem_sdiff.mp hkT).1).2
    cases ha.symm.trans ho
  have hAcard : A.card = (junk G C).card + K.card :=
    Finset.card_union_of_disjoint hJKdis
  have hScard : S.card = A.card + (T \ R).card := Finset.card_union_of_disjoint hdis
  have hQcard : Q.card = S.card :=
    Finset.card_image_of_injective _ (by intro a b h; exact Nat.add_left_cancel h)
  have hTR : (T \ R).card + R.card = T.card := Finset.card_sdiff_add_card_eq_card hRT
  have hDsize : D.size = E.size + 1 := StarCompletion.appendBinary_size n E GateOp.or B.output E.output
  refine ⟨D, hDAO, hDfun, hDclean, ?_⟩
  change D.size + (junk G C).card + K.card + T.card =
    B.size + C.size + (L.image label).card + 1
  omega


lemma shared_collapse_or_raw_absorb {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C) (hTop : TopForm G C)
    (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hfun : circuitFun n C = graphFun G ∅)
    (hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j)
    (hlive : ∀ a ∈ tops G C, OrReaches n C C.output a)
    (hU : ∀ u v : Fin n, s(u, v) ∈ Ustar G C → circuitFun n B (pairInput u v) = true)
    (K : Finset ℕ) (hK : ∀ k ∈ K, k ∈ tops G C)
    (hcross : ∀ k ∈ K, ∀ u ∈ side (n := n) C k 0, ∀ v ∈ side (n := n) C k 1,
      circuitFun n B (pairInput u v) = true)
    (T : Finset ℕ)
    (hTdata : ∀ k ∈ T, k < C.gates.length ∧ (gateAt C k).op = GateOp.or)
    (hboundary : ∀ k ∈ T, ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      OrReaches n C (n + k) j → Repair.dirty G C j) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.size + (junk G C).card + K.card + T.card =
        B.size + C.size +
          ((T.filter fun k => 1 < (orIn n C (n + k)).card).image fun k => orIn n C (n + k)).card + 1 := by
  apply shared_collapse_raw_semantics_absorb G B C hB hC hTop hBo hBsafe hfun
    hBclean hlive hU K hK hcross T hTdata
  intro j hj x hBx
  have hs := shared_or_signature G B C hC hBo (n + j) (hboundary j hj) x
  rw [shift_gate, hBx] at hs
  simpa using hs

end PEqualNP.Outside.L_meta_2583.SharedRepair


namespace PEqualNP.Outside.L_meta_2583.SharedRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma shared_or_raw_when_boundaries_B_false {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (B C : Circuit) (hC : IsAO2 n C) (w : ℕ)
    (hboundary : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      OrReaches n C w j → ∀ x : Fin n → Bool,
        val (shared G B C) (List.ofFn x) (n + (B.gates.length + j)) = true →
        circuitFun n B x = true)
    (x : Fin n → Bool) (hBx : circuitFun n B x = false) :
    val (shared G B C) (List.ofFn x) (shiftWire n B.gates.length w) = true ↔
      ∃ t ∈ orIn n C w, x t = true := by
  constructor
  · intro hv
    rcases shared_or_trace G B C hC x w hv with hraw | ⟨j, hj, hop, hr, hvj⟩
    · exact hraw
    · have hf := hboundary j hj hop hr x hvj
      rw [hBx] at hf
      cases hf
  · rintro ⟨t, ht, hxt⟩
    apply shifted_or_path_value G B C hC x (Frontier.mem_orIn_reach t ht)
    rw [shift_input n B.gates.length t.val t.isLt, val_ofFn]
    exact hxt

lemma shared_or_raw_when_dirty_or_covered_boundaries {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C)
    (hTop : TopForm G C) (hBo : B.output < n + B.gates.length)
    (K : Finset ℕ) (hK : ∀ k ∈ K, k ∈ tops G C)
    (hcross : ∀ k ∈ K, ∀ u ∈ side (n := n) C k 0, ∀ v ∈ side (n := n) C k 1,
      circuitFun n B (pairInput u v) = true)
    (w : ℕ)
    (hboundary : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      OrReaches n C w j → Repair.dirty G C j ∨ j ∈ K)
    (x : Fin n → Bool) (hBx : circuitFun n B x = false) :
    val (shared G B C) (List.ofFn x) (shiftWire n B.gates.length w) = true ↔
      ∃ t ∈ orIn n C w, x t = true := by
  apply shared_or_raw_when_boundaries_B_false G B C hC w ?_ x hBx
  intro j hj hop hr y hy
  rcases hboundary j hj hop hr with hd | hk
  · rw [copied_value G B C hBo hj hd y] at hy
    exact hy
  · exact shared_top_dominated_by_B G B C hB hC hTop hBo (hK j hk) (hcross j hk) y hy

end PEqualNP.Outside.L_meta_2583.SharedRepair


namespace PEqualNP.Outside.L_meta_2583.SharedRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma and_ancestor_or_boundaries_dirty {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (_hAO : IsAO2 n C) (hTop : TopForm G C)
    {k a : ℕ} (ha : a < C.gates.length) (hopa : (gateAt C a).op = GateOp.and)
    (hancestor : InCone n C k a) :
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      OrReaches n C (n + k) j → Repair.dirty G C j := by
  intro j hj hopj hreach
  have hja : InCone n C j a := by
    rcases Frontier.orStep_cone (Frontier.orReaches_reach j _ hreach).1 k j rfl rfl with
      heq | hjk
    · simpa only [heq] using hancestor
    · exact CleanBudget.inCone_trans n C j k hjk a hancestor
  exact ⟨hopj, fun hbelow => hTop j hj a ha hopj hbelow hopa hja⟩

lemma exists_and_ancestor_or_boundaries_dirty {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hAO : IsAO2 n C) (hTop : TopForm G C)
    {k : ℕ} (hancestor : ∃ a < C.gates.length,
      (gateAt C a).op = GateOp.and ∧ InCone n C k a) :
    ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      OrReaches n C (n + k) j → Repair.dirty G C j := by
  obtain ⟨a, ha, hopa, hka⟩ := hancestor
  exact and_ancestor_or_boundaries_dirty hAO hTop ha hopa hka

end PEqualNP.Outside.L_meta_2583.SharedRepair

namespace PEqualNP.Outside.L_meta_2583.SharedRepair

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.CleanedNonEdge

lemma shared_collapse_covered_boundary_or_raw {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (B C : Circuit) (hB : IsAO2 n B) (hC : IsAO2 n C)
    (hTop : TopForm G C) (hBo : B.output < n + B.gates.length)
    (hBsafe : ∀ x, circuitFun n B x = true → graphFun G ∅ x = true)
    (hfun : circuitFun n C = graphFun G ∅)
    (hBclean : ∀ j < B.gates.length, (gateAt B j).op = GateOp.and → BelowF G B j)
    (hlive : ∀ a ∈ tops G C, OrReaches n C C.output a)
    (hU : ∀ u v : Fin n, s(u, v) ∈ Ustar G C → circuitFun n B (pairInput u v) = true)
    (K : Finset ℕ) (hK : ∀ k ∈ K, k ∈ tops G C)
    (hcross : ∀ k ∈ K, ∀ u ∈ side (n := n) C k 0, ∀ v ∈ side (n := n) C k 1,
      circuitFun n B (pairInput u v) = true)
    (T : Finset ℕ)
    (hT : ∀ k ∈ T, k < C.gates.length ∧ (gateAt C k).op = GateOp.or)
    (hboundary : ∀ k ∈ T, ∀ j < C.gates.length, (gateAt C j).op = GateOp.and →
      OrReaches n C (n + k) j → Repair.dirty G C j ∨ j ∈ K) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧
      (∀ j < D.gates.length, (gateAt D j).op = GateOp.and → BelowF G D j) ∧
      D.size + (junk G C).card + K.card + T.card =
        B.size + C.size +
          ((T.filter fun k => 1 < (orIn n C (n + k)).card).image fun k => orIn n C (n + k)).card + 1 := by
  apply shared_collapse_raw_semantics_absorb G B C hB hC hTop hBo hBsafe hfun hBclean
    hlive hU K hK hcross T hT
  intro k hk x hBx
  simpa only [shift_gate] using
    shared_or_raw_when_dirty_or_covered_boundaries G B C hB hC hTop hBo K hK hcross
      (n + k) (hboundary k hk) x hBx

end PEqualNP.Outside.L_meta_2583.SharedRepair

namespace PEqualNP.Outside.L_meta_2583.CleanBudget

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma sixteen_edges_four_cover_clean_size {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hfour : NoFourCycle G)
    (hedges : 16 ≤ G.edgeFinset.card)
    (hcover : ∀ T : Finset (Fin n), G.IsVertexCover ↑T → 4 ≤ T.card)
    (hC : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j) :
    19 ≤ C.size := by
  have hne : G.edgeFinset.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨T, hT, hbound⟩ := clean_graph_budget G C hfour hne hC hfun hclean
  have hTcard := hcover T hT
  omega

lemma sixteen_edges_four_cover_small_has_dirty_and {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (C : Circuit) (hfour : NoFourCycle G)
    (hedges : 16 ≤ G.edgeFinset.card)
    (hcover : ∀ T : Finset (Fin n), G.IsVertexCover ↑T → 4 ≤ T.card)
    (hC : IsAO2 n C) (hfun : circuitFun n C = graphFun G ∅)
    (hsize : C.size ≤ 18) :
    ∃ j < C.gates.length, (gateAt C j).op = GateOp.and ∧ ¬ BelowF G C j := by
  classical
  by_contra hn
  have hclean : ∀ j < C.gates.length, (gateAt C j).op = GateOp.and → BelowF G C j := by
    intro j hj hop
    by_contra hbad
    exact hn ⟨j, hj, hop, hbad⟩
  have hbound := sixteen_edges_four_cover_clean_size G C hfour hedges hcover hC hfun hclean
  omega

end PEqualNP.Outside.L_meta_2583.CleanBudget
