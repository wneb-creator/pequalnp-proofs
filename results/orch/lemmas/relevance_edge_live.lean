import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.Rel

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

lemma wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

lemma getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


lemma wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

lemma gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

lemma iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

lemma val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

lemma val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

lemma val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

lemma val_mono (gates : List Gate) {n : ℕ}
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) :
    ∀ w, val gates w x = true → val gates w x' = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h ⊢
      exact hx _ h
    · by_cases hbig : n + gates.length ≤ w
      · rw [val_big gates x w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at h ⊢
        rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · apply (val_and gates x' (w - n) hi ha).2
          intro j hj
          obtain ⟨hjlt, hjv⟩ := (val_and gates x (w - n) hi ha).1 h j hj
          exact ⟨hjlt, ih j (by omega) hjv⟩
        · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gates x (w - n) hi ho).1 h
          exact (val_or gates x' (w - n) hi ho).2 ⟨j, hj, hjlt, ih j (by omega) hv⟩

def redirect (n l m i : ℕ) : ℕ :=
  if i = n + m then n + l else if i < n + m then i else i - 1

def trim (n : ℕ) (gs : List Gate) (m : ℕ) : List Gate :=
  List.ofFn fun j : Fin (gs.length - 1) =>
    let k := if j.val < m then j.val else j.val + 1
    let g := gs.getD k ⟨GateOp.or, []⟩
    ⟨g.op, g.inputs.map (redirect n gs.length m)⟩

lemma trim_length (n : ℕ) (gs : List Gate) (m : ℕ) :
    (trim n gs m).length = gs.length - 1 := by
  simp [trim]

lemma trim_get (n : ℕ) (gs : List Gate) (m j : ℕ)
    (hm : m < gs.length) (hj : j < gs.length) (hne : j ≠ m) :
    let k := if j < m then j else j - 1
    ∃ hk : k < (trim n gs m).length,
      (trim n gs m)[k] = ⟨gs[j].op, gs[j].inputs.map (redirect n gs.length m)⟩ := by
  dsimp
  have hk : (if j < m then j else j - 1) < (trim n gs m).length := by
    rw [trim_length]
    split_ifs <;> omega
  refine ⟨hk, ?_⟩
  simp only [trim, List.getElem_ofFn]
  have he : (if (if j < m then j else j - 1) < m then
      (if j < m then j else j - 1) else (if j < m then j else j - 1) + 1) = j := by
    split_ifs <;> omega
  rw [he]
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma redirect_input (n l m i : ℕ) (hi : i < n) : redirect n l m i = i := by
  simp [redirect, show i ≠ n + m by omega, show i < n + m by omega]

lemma redirect_gate (n l m j : ℕ) (hj : j ≠ m) :
    redirect n l m (n + j) = n + (if j < m then j else j - 1) := by
  unfold redirect
  split_ifs <;> omega

lemma redirect_before (n l m j i : ℕ) (hm : m < l) (hj : j < l) (hne : j ≠ m) :
    redirect n l m i < n + (if j < m then j else j - 1) ↔
      i < n + j ∧ i ≠ n + m := by
  unfold redirect
  split_ifs <;> omega

lemma trim_legal (n : ℕ) (gs : List Gate) (m : ℕ) (hm : m < gs.length)
    (hlegal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ trim n gs m, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hg
  have hj : (if j.val < m then j.val else j.val + 1) < gs.length := by
    have := j.isLt
    split_ifs <;> omega
  have h := hlegal gs[if j.val < m then j.val else j.val + 1] (List.getElem_mem hj)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj] using h

lemma trim_semantics (n : ℕ) (gs : List Gate) (m : ℕ) (hm : m < gs.length)
    (hlegal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x : Fin n → Bool) (w : ℕ) :
    (val (trim n gs m) (redirect n gs.length m w) x = true → val gs w x = true) ∧
      (val gs (n + m) x = false → val gs w x = true →
        val (trim n gs m) (redirect n gs.length m w) x = true) := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hwinput : w < n
    · rw [redirect_input n gs.length m w hwinput,
        val_input (trim n gs m) x w hwinput, val_input gs x w hwinput]
      exact ⟨id, fun _ => id⟩
    by_cases hwbig : n + gs.length ≤ w
    · have hr : n + (trim n gs m).length ≤ redirect n gs.length m w := by
        rw [trim_length]
        unfold redirect
        split_ifs <;> omega
      rw [val_big gs x w hwbig, val_big (trim n gs m) x _ hr]
      simp
    have hj : w - n < gs.length := by omega
    have hw : n + (w - n) = w := by omega
    by_cases heq : w - n = m
    · have hweq : w = n + m := by omega
      subst w
      have hr : n + (trim n gs m).length ≤ redirect n gs.length m (n + m) := by
        simp [redirect, trim_length]
      rw [val_big (trim n gs m) x _ hr]
      simp
    obtain ⟨hk, hgate⟩ := trim_get n gs m (w - n) hm hj heq
    let k := if w - n < m then w - n else (w - n) - 1
    have hredirect : redirect n gs.length m w = n + k := by
      rw [← hw, redirect_gate n gs.length m (w - n) heq]
    change k < (trim n gs m).length at hk
    change (trim n gs m)[k] = _ at hgate
    have hop := (hlegal gs[w - n] (List.getElem_mem hj)).1
    constructor
    · intro hnew
      rw [hredirect] at hnew
      rw [← hw]
      rcases hop with ha | ho
      · apply (val_and gs x (w - n) hj ha).2
        have hta : (trim n gs m)[k].op = GateOp.and := by rw [hgate]; exact ha
        have h := (val_and (trim n gs m) x k hk hta).1 hnew
        intro i hi
        have hmem : redirect n gs.length m i ∈ (trim n gs m)[k].inputs := by
          rw [hgate]
          exact List.mem_map.mpr ⟨i, hi, rfl⟩
        obtain ⟨hrlt, hrt⟩ := h _ hmem
        have hib := (redirect_before n gs.length m (w - n) i hm hj heq).1 hrlt
        exact ⟨hib.1, (ih i (by omega)).1 hrt⟩
      · have hto : (trim n gs m)[k].op = GateOp.or := by rw [hgate]; exact ho
        obtain ⟨i', hi', hilt, hit⟩ := (val_or (trim n gs m) x k hk hto).1 hnew
        rw [hgate] at hi'
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hi'
        have hib := (redirect_before n gs.length m (w - n) i hm hj heq).1 hilt
        exact (val_or gs x (w - n) hj ho).2 ⟨i, hi, hib.1, (ih i (by omega)).1 hit⟩
    · intro hzero hold
      rw [hredirect]
      rw [← hw] at hold
      rcases hop with ha | ho
      · have hta : (trim n gs m)[k].op = GateOp.and := by rw [hgate]; exact ha
        apply (val_and (trim n gs m) x k hk hta).2
        intro i' hi'
        rw [hgate] at hi'
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hi'
        obtain ⟨hilt, hit⟩ := (val_and gs x (w - n) hj ha).1 hold i hi
        have hine : i ≠ n + m := by intro he; rw [he, hzero] at hit; contradiction
        exact ⟨(redirect_before n gs.length m (w - n) i hm hj heq).2 ⟨hilt, hine⟩,
          (ih i (by omega)).2 hzero hit⟩
      · obtain ⟨i, hi, hilt, hit⟩ := (val_or gs x (w - n) hj ho).1 hold
        have hto : (trim n gs m)[k].op = GateOp.or := by rw [hgate]; exact ho
        apply (val_or (trim n gs m) x k hk hto).2
        have hine : i ≠ n + m := by intro he; rw [he, hzero] at hit; contradiction
        refine ⟨redirect n gs.length m i, ?_,
          (redirect_before n gs.length m (w - n) i hm hj heq).2 ⟨hilt, hine⟩,
          (ih i (by omega)).2 hzero hit⟩
        rw [hgate]
        exact List.mem_map.mpr ⟨i, hi, rfl⟩

lemma minimum_gate_edge_live (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit)
    (hlegal : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hfun : ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
      decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true))
    (hmin : ∀ D : Circuit,
      (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
      C.size ≤ D.size)
    (m : ℕ) (hm : m < C.gates.length) :
    ∃ u v : Fin n, G.Adj u v ∧ gateVal n C m (pairInput u v) = true := by
  classical
  by_contra hnone
  have hzero (u v : Fin n) (huv : G.Adj u v) :
      val C.gates (n + m) (pairInput u v) = false := by
    cases he : val C.gates (n + m) (pairInput u v) with
    | false => rfl
    | true => exact False.elim (hnone ⟨u, v, huv, he⟩)
  let D : Circuit := ⟨trim n C.gates m, redirect n C.gates.length m C.output⟩
  have hDlegal : ∀ g ∈ D.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
    trim_legal n C.gates m hm hlegal
  have hDfun (x : Fin n → Bool) : D.eval (List.ofFn x) =
      decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) := by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    constructor
    · intro hd
      have hc := (trim_semantics n C.gates m hm hlegal x C.output).1 hd
      change C.eval (List.ofFn x) = true at hc
      rw [hfun x] at hc
      simpa only [decide_eq_true_eq] using hc
    · rintro ⟨u, v, huv, hu, hv⟩
      have hc : C.eval (List.ofFn (pairInput u v)) = true := by
        rw [hfun]
        rw [decide_eq_true_eq]
        exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
      have hd := (trim_semantics n C.gates m hm hlegal (pairInput u v) C.output).2
        (hzero u v huv) hc
      exact val_mono D.gates hDlegal (pairInput u v) x (by
        intro z hz
        simp only [pairInput, decide_eq_true_eq] at hz
        rcases hz with rfl | rfl
        · exact hu
        · exact hv) D.output hd
  have hle := hmin D hDlegal hDfun
  change C.gates.length ≤ (trim n C.gates m).length at hle
  rw [trim_length] at hle
  omega

end PEqualNP.Outside.L_meta_1031.Rel

