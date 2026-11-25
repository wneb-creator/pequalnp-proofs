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

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

def OrStep (n : ℕ) (C : Circuit) (w w' : ℕ) : Prop :=
  ∃ k, k < C.gates.length ∧ w = n + k ∧ (gateAt C k).op = GateOp.or ∧
    w' ∈ (gateAt C k).inputs ∧ w' < n + k

lemma pairInput_true {n : ℕ} (u v w : Fin n) : pairInput u v w = true ↔ w = u ∨ w = v := by
  simp [pairInput]

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

lemma mem_orIn_reach {n : ℕ} {C : Circuit} {p : ℕ} (u : Fin n)
    (hu : u ∈ PEqualNP.TopForm.orIn n C p) :
    Relation.ReflTransGen (OrStep n C) p u.val := by
  simp only [PEqualNP.TopForm.orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with h | ⟨k, hk, hr, hop, hin⟩
  · rw [h]
  · exact (orReaches_reach k p hr).1.tail ⟨k, hk, rfl, hop, hin, by omega⟩


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

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

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

end Duplicate


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

end DeadSet

namespace DeadSet

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.CircuitMoves PEqualNP.EdgeOwnership PEqualNP.TopForm

lemma redirect_prefix_eq_lower {n k i p w : ℕ} (hp : p < n + i) (hi : i < k) :
    eraseRedirect n k p w = n + i ↔ w = n + i := by
  unfold eraseRedirect
  split_ifs <;> omega

end DeadSet


namespace SourcePool
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open SharedRepair

lemma shift_injective (n m : ℕ) : Function.Injective (shiftWire n m) := by
  intro a b h
  unfold shiftWire at h
  split_ifs at h <;> omega

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

end PEqualNP.Outside.L_meta_2583
