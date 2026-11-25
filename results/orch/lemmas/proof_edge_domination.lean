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

lemma minimum_gate_essential (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
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
    ∃ u v : Fin n, G.Adj u v ∧
      gateVal n C m (pairInput u v) = true ∧
      Circuit.eval ⟨trim n C.gates m, redirect n C.gates.length m C.output⟩
        (List.ofFn (pairInput u v)) = false := by
  classical
  let D : Circuit := ⟨trim n C.gates m, redirect n C.gates.length m C.output⟩
  have hDlegal : ∀ g ∈ D.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
    trim_legal n C.gates m hm hlegal
  have hex : ∃ u v : Fin n, G.Adj u v ∧ D.eval (List.ofFn (pairInput u v)) = false := by
    by_contra hnone
    have hpair (u v : Fin n) (huv : G.Adj u v) :
        D.eval (List.ofFn (pairInput u v)) = true := by
      cases he : D.eval (List.ofFn (pairInput u v)) with
      | false => exact False.elim (hnone ⟨u, v, huv, he⟩)
      | true => rfl
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
        exact val_mono D.gates hDlegal (pairInput u v) x (by
          intro z hz
          simp only [pairInput, decide_eq_true_eq] at hz
          rcases hz with rfl | rfl
          · exact hu
          · exact hv) D.output (hpair u v huv)
    have hle := hmin D hDlegal hDfun
    change C.gates.length ≤ (trim n C.gates m).length at hle
    rw [trim_length] at hle
    omega
  obtain ⟨u, v, huv, hd⟩ := hex
  refine ⟨u, v, huv, ?_, hd⟩
  have hc : C.eval (List.ofFn (pairInput u v)) = true := by
    rw [hfun, decide_eq_true_eq]
    exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
  cases he : gateVal n C m (pairInput u v) with
  | true => rfl
  | false =>
    have hf := (trim_semantics n C.gates m hm hlegal (pairInput u v) C.output).2 he hc
    change D.eval (List.ofFn (pairInput u v)) = true at hf
    rw [hd] at hf
    contradiction

end PEqualNP.Outside.L_meta_1031.Rel


namespace PEqualNP.Outside.L_meta_1031.CycleStructure.Normal

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

def Rep {n : ℕ} (new : List Gate) (f : (Fin n → Bool) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Fin n → Bool, (W new x).getD j false = f x)

def Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (n : ℕ) (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h ∧ ∀ i ∈ h.inputs, i < n + new.length

lemma rep_congr {n : ℕ} {new : List Gate} {f g : (Fin n → Bool) → Bool}
    (h : ∀ x, f x = g x) (hf : Rep new f) : Rep new g := by
  obtain rfl : f = g := funext h
  exact hf

lemma rep_mono {n : ℕ} {new new' : List Gate} (he : Ext n new new')
    (f : (Fin n → Bool) → Bool) (h : Rep new f) : Rep new' f := by
  rcases he with rfl | ⟨k, rfl, _⟩
  · exact h
  · rcases h with hc | ⟨j, hj, hv⟩
    · exact Or.inl hc
    · have hne : ¬ j = n + new.length := by omega
      refine Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
      rw [W_val, if_neg hne]
      exact hv x

lemma rep_and {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext n new new' ∧ Rep new' (fun x => f x && g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | false =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
        show (f x && g x) = false
        simp [h1 x]⟩⟩
    | true =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x && g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | false =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
          show (f x && g x) = false
          simp [h2 x]⟩⟩
      | true =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x && g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inl rfl, rfl⟩, (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.and, [j, k]⟩]) x).getD (n + new.length) false = (f x && g x)
      rw [W_val, if_pos rfl]
      show GateOp.and.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_or {n : ℕ} (new : List Gate) (f g : (Fin n → Bool) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext n new new' ∧ Rep new' (fun x => f x || g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | true =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
        show (f x || g x) = true
        simp [h1 x]⟩⟩
    | false =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x || g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | true =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
          show (f x || g x) = true
          simp [h2 x]⟩⟩
      | false =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x).getD j false = (f x || g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inr rfl, rfl⟩, (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.or, [j, k]⟩]) x).getD (n + new.length) false = (f x || g x)
      rw [W_val, if_pos rfl]
      show GateOp.or.eval [(W new x).getD j false, (W new x).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_input {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (t : ℕ) :
    Rep ([] : List Gate) (fun x => (W [] (ρ x)).getD t false) := by
  by_cases ht : t < n
  · have hval : ∀ y : Fin n → Bool, (W [] y).getD t false = y ⟨t, ht⟩ := by
      intro y
      show (List.ofFn y).getD t false = _
      rw [List.getD_eq_getElem _ _ (by simpa using ht)]
      simp
    rcases hρ ⟨t, ht⟩ with ⟨c, hc⟩ | hid
    · exact Or.inl ⟨c, fun x => by
        show (W [] (ρ x)).getD t false = c
        rw [hval, hc x]⟩
    · exact Or.inr ⟨t, by simpa using ht, fun x => by
        show (W [] x).getD t false = (W [] (ρ x)).getD t false
        rw [hval, hval, hid x]⟩
  · exact Or.inl ⟨false, fun x =>
      List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)⟩

lemma gate_rep {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old new : List Gate)
    (op : GateOp) (l : List ℕ) (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : l.length ≤ 2)
    (h : ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)) :
    ∃ new', Ext n new new' ∧
      Rep new' (fun x => op.eval (l.map fun i => (W old (ρ x)).getD i false)) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by simp [GateOp.eval]⟩⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by simp [GateOp.eval]⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
  · rcases hop with rfl | rfl
    · obtain ⟨new', he, hr⟩ := rep_and new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
    · obtain ⟨new', he, hr⟩ := rep_or new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
  · simp only [List.length_cons] at hlen
    omega

def RB (n : ℕ) (new : List Gate) : Prop :=
  ∀ j < new.length, ∀ i ∈ (new.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

lemma rb_snoc {n : ℕ} {new : List Gate} {h : Gate} (hrb : RB n new)
    (hh : ∀ i ∈ h.inputs, i < n + new.length) : RB n (new ++ [h]) := by
  intro j hj i hi
  rw [List.length_append, List.length_singleton] at hj
  by_cases hlt : j < new.length
  · have e : (new ++ [h]).getD j ⟨GateOp.or, []⟩ = new.getD j ⟨GateOp.or, []⟩ := by
      simp [List.getD, List.getElem?_append_left hlt]
    rw [e] at hi
    exact hrb j hlt i hi
  · have hj' : j = new.length := by omega
    subst hj'
    have e : (new ++ [h]).getD new.length ⟨GateOp.or, []⟩ = h := by simp [List.getD]
    rw [e] at hi
    exact hh i hi

def Inv {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) : Prop :=
  ∃ new : List Gate, (∀ g ∈ new, Fan g) ∧ RB n new ∧ new.length ≤ old.length ∧
    ∀ t : ℕ, Rep new (fun x => (W old (ρ x)).getD t false)

lemma inv_step {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool) (old : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length ≤ 2)
    (h : Inv ρ old) : Inv ρ (old ++ [g]) := by
  obtain ⟨new, hfan, hrb, hl, hrep⟩ := h
  obtain ⟨new', he, hr⟩ := gate_rep ρ old new g.op g.inputs hop hlen hrep
  refine ⟨new', ?_, ?_, ?_, ?_⟩
  · rcases he with rfl | ⟨k, rfl, hk, _⟩
    · exact hfan
    · intro q hq
      rcases List.mem_append.mp hq with hq | hq
      · exact hfan q hq
      · rw [List.mem_singleton] at hq
        rw [hq]
        exact hk
  · rcases he with rfl | ⟨k, rfl, _, hkb⟩
    · exact hrb
    · exact rb_snoc hrb hkb
  · rcases he with rfl | ⟨k, rfl, hk, _⟩
    · rw [List.length_append, List.length_singleton]
      omega
    · rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton]
      omega
  · intro t
    by_cases ht : t = n + old.length
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, if_pos ht]) hr
    · exact rep_congr (fun x => by
        show _ = (W (old ++ [g]) (ρ x)).getD t false
        rw [W_val, if_neg ht]) (rep_mono he _ (hrep t))

lemma inv_all {n : ℕ} (ρ : (Fin n → Bool) → Fin n → Bool)
    (hρ : ∀ i : Fin n, (∃ c : Bool, ∀ x : Fin n → Bool, ρ x i = c) ∨
      (∀ x : Fin n → Bool, ρ x i = x i)) (gates : List Gate)
    (hg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    Inv ρ gates := by
  have hall : ∀ (post pre : List Gate), pre ++ post = gates → Inv ρ pre → Inv ρ gates := by
    intro post
    induction post with
    | nil =>
      intro pre h hinv
      rw [List.append_nil] at h
      rw [← h]
      exact hinv
    | cons g post ih =>
      intro pre h hinv
      have hmem : g ∈ gates := by
        rw [← h]
        simp
      exact ih (pre ++ [g]) (by rw [List.append_assoc]; exact h)
        (inv_step ρ pre g (hg g hmem).1 (hg g hmem).2 hinv)
  exact hall gates [] (List.nil_append _)
    ⟨[], by simp, (by intro j hj; simp at hj), le_refl _, rep_input ρ hρ⟩

lemma eval_eq {n : ℕ} (gs : List Gate) (o : ℕ) (x : Fin n → Bool) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn x) = (W gs x).getD o false := rfl

theorem main_aux : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (_ : DecidableRel G.Adj) (C : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 C →
    (∀ x : Fin n → Bool,
      (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
    ∃ C' : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n C' ∧ PEqualNP.MetaComplexity.circuitFun n C' = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧ C'.size ≤ C.size := by
  intro n G inst C hm hC
  have hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hgm
    have h := hm g hgm
    refine ⟨?_, h.2⟩
    have h1 := h.1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact h1
  obtain ⟨new, hfan, hrb, hl, hrep⟩ :=
    inv_all (fun (x : Fin n → Bool) => x) (fun i => Or.inr (fun x => rfl)) C.gates hg
  have hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = (W C.gates x).getD C.output false :=
    fun x => rfl
  have hgf : ∀ x : Fin n → Bool, PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x
      = C.eval (List.ofFn x) := by
    intro x
    rw [Bool.eq_iff_iff, hC x]
    simp [PEqualNP.MetaComplexity.NestedCover.graphFun]
  rcases hrep C.output with ⟨c, hc⟩ | ⟨j, _, hj⟩
  · have hc' : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = c := fun x => (hev x).trans (hc x)
    have hcf : c = false := by
      have h0 := hC (fun _ => false)
      rw [hc'] at h0
      cases c with
      | false => rfl
      | true =>
        obtain ⟨u, v, _, hu, _⟩ := h0.mp rfl
        exact absurd hu (by simp)
    subst hcf
    refine ⟨⟨[], n⟩, ⟨?_, ?_, ?_⟩, ?_, Nat.zero_le _⟩
    · intro g hgm
      simp at hgm
    · intro k hk
      simp at hk
    · intro g hgm
      simp at hgm
    · funext x
      rw [hgf x, hc' x]
      show (W ([] : List Gate) x).getD n false = false
      exact List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)
  · refine ⟨⟨new, j⟩, ⟨?_, ?_, ?_⟩, ?_, hl⟩
    · intro g hgm
      exact (hfan g hgm).1
    · exact hrb
    · intro g hgm
      exact (hfan g hgm).2
    · funext x
      rw [hgf x, hev x]
      exact hj x

end PEqualNP.Outside.L_meta_1031.CycleStructure.Normal

namespace PEqualNP.Outside.L_meta_1031.CycleStructure

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_1031.Rel

theorem step_iff {n : ℕ} (A B : List Gate) (ka kb : ℕ) (hka : ka < A.length)
    (hkb : kb < B.length) (hop : A[ka].op = B[kb].op)
    (hlegal : B[kb].op = GateOp.and ∨ B[kb].op = GateOp.or)
    (f : ℕ → ℕ) (hin : A[ka].inputs = B[kb].inputs.map f) (x : Fin n → Bool)
    (hloc : ∀ j ∈ B[kb].inputs,
      ((f j < n + ka ∧ val A (f j) x = true) ↔ (j < n + kb ∧ val B j x = true))) :
    val A (n + ka) x = true ↔ val B (n + kb) x = true := by
  rcases hlegal with ha | ho
  · rw [val_and A x ka hka (by rw [hop]; exact ha), val_and B x kb hkb ha, hin]
    constructor
    · intro H j hj
      exact (hloc j hj).1 (H (f j) (List.mem_map.2 ⟨j, hj, rfl⟩))
    · intro H j' hj'
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hj'
      exact (hloc j hj).2 (H j hj)
  · rw [val_or A x ka hka (by rw [hop]; exact ho), val_or B x kb hkb ho, hin]
    constructor
    · rintro ⟨j', hj', H⟩
      obtain ⟨j, hj, rfl⟩ := List.mem_map.1 hj'
      exact ⟨j, hj, (hloc j hj).1 H⟩
    · rintro ⟨j, hj, H⟩
      exact ⟨f j, List.mem_map.2 ⟨j, hj, rfl⟩, (hloc j hj).2 H⟩

def rd (n m p i : ℕ) : ℕ := if i = n + m then p else if n + m < i then i - 1 else i

def er (n : ℕ) (gs : List Gate) (m p : ℕ) : List Gate :=
  (List.range (gs.length - 1)).map fun j =>
    if j < m then gs.getD j ⟨GateOp.or, []⟩
    else ⟨(gs.getD (j + 1) ⟨GateOp.or, []⟩).op,
      (gs.getD (j + 1) ⟨GateOp.or, []⟩).inputs.map (rd n m p)⟩

theorem er_len (n : ℕ) (gs : List Gate) (m p : ℕ) : (er n gs m p).length = gs.length - 1 := by
  simp [er]

theorem er_lt (n : ℕ) (gs : List Gate) (m p j : ℕ) (hjm : j < m) (hj : j < gs.length)
    (hj' : j < (er n gs m p).length) : (er n gs m p)[j] = gs[j] := by
  simp [er, hjm, List.getD_eq_getElem?_getD, hj]

theorem er_ge (n : ℕ) (gs : List Gate) (m p j : ℕ) (hjm : m ≤ j) (hj : j + 1 < gs.length)
    (hj' : j < (er n gs m p).length) :
    (er n gs m p)[j] = ⟨gs[j + 1].op, gs[j + 1].inputs.map (rd n m p)⟩ := by
  simp [er, Nat.not_lt.2 hjm, List.getD_eq_getElem?_getD, hj]

theorem rd_small (n m p a : ℕ) (h : a < n + m) : rd n m p a = a := by
  unfold rd
  split_ifs <;> omega

theorem rd_at (n m p : ℕ) : rd n m p (n + m) = p := by
  simp [rd]

theorem rd_succ (n m p k : ℕ) (h : m ≤ k) : rd n m p (n + (k + 1)) = n + k := by
  unfold rd
  split_ifs <;> omega

theorem rd_lt (n m p a k : ℕ) (hp : p < n + m) (h : m ≤ k) :
    rd n m p a < n + k ↔ a < n + (k + 1) := by
  unfold rd
  split_ifs <;> omega

theorem er_pre {n : ℕ} (gs : List Gate)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (m p : ℕ) (hm : m < gs.length) (x : Fin n → Bool) :
    ∀ i, i < n + m → (val (er n gs m p) i x = true ↔ val gs i x = true) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    by_cases hin : i < n
    · rw [val_input _ _ i hin, val_input _ _ i hin]
    · obtain ⟨k, rfl⟩ : ∃ k, i = n + k := ⟨i - n, by omega⟩
      have hk : k < gs.length := by omega
      have hkE : k < (er n gs m p).length := by rw [er_len]; omega
      have hg := er_lt n gs m p k (by omega) hk hkE
      apply step_iff (er n gs m p) gs k k hkE hk (by rw [hg])
        (legal gs[k] (List.getElem_mem hk)).1 id (by rw [hg]; simp) x
      intro j _
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, (ih j (by simpa using h1) (by simp at h1; omega)).1 h2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨h1, (ih j h1 (by omega)).2 h2⟩

lemma erase_congr {n : ℕ} (gs : List Gate)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (m p : ℕ) (hm : m < gs.length) (hp : p < n + m)
    (x : Fin n → Bool)
    (hgate : val gs p x = val gs (n + m) x ∨
      ∀ j (hj : j < gs.length), m < j → n + m ∉ gs[j].inputs) :
    ∀ i, (i = n + m → val gs p x = val gs (n + m) x) →
      val (er n gs m p) (rd n m p i) x = val gs i x := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hallow
    by_cases him : i < n + m
    · rw [rd_small n m p i him, Bool.eq_iff_iff]
      exact er_pre gs legal m p hm x i him
    by_cases hbig : n + gs.length ≤ i
    · rw [val_big gs x i hbig]
      apply val_big
      rw [er_len]
      unfold rd
      split_ifs <;> omega
    by_cases hieq : i = n + m
    · subst i
      rw [rd_at]
      have e := ih p hp (by intro h; omega)
      rw [rd_small n m p p hp] at e
      exact e.trans (hallow rfl)
    obtain ⟨k, rfl⟩ : ∃ k, i = n + (k + 1) := ⟨i - n - 1, by omega⟩
    have hmk : m ≤ k := by omega
    have hk : k + 1 < gs.length := by omega
    have hkE : k < (er n gs m p).length := by rw [er_len]; omega
    have hg := er_ge n gs m p k hmk hk hkE
    rw [rd_succ n m p k hmk, Bool.eq_iff_iff]
    apply step_iff (er n gs m p) gs k (k + 1) hkE hk (by rw [hg])
      (legal gs[k + 1] (List.getElem_mem hk)).1 (rd n m p) (by rw [hg]) x
    intro j hj
    have hjallow : j = n + m → val gs p x = val gs (n + m) x := by
      intro he
      rcases hgate with heq | hno
      · exact heq
      · exact False.elim (hno (k + 1) hk (by omega) (he ▸ hj))
    constructor
    · rintro ⟨h1, h2⟩
      have hjlt := (rd_lt n m p j k hp hmk).1 h1
      exact ⟨hjlt, by rw [← ih j hjlt hjallow]; exact h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨(rd_lt n m p j k hp hmk).2 h1,
        by rw [ih j h1 hjallow]; exact h2⟩

lemma er_legal (n : ℕ) (gs : List Gate) (m p : ℕ)
    (hlegal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ er n gs m p, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hg
  have hjb := List.mem_range.mp hj
  by_cases hjm : j < m
  · simp only [if_pos hjm]
    have h : j < gs.length := by omega
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h,
      Option.getD_some] using hlegal gs[j] (List.getElem_mem h)
  · simp only [if_neg hjm]
    have h : j + 1 < gs.length := by omega
    have hh := hlegal gs[j + 1] (List.getElem_mem h)
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h,
      Option.getD_some, List.length_map] using hh

def Minimal (n : ℕ) (C : Circuit) : Prop :=
  Monotone2 C ∧ ∀ D : Circuit, Monotone2 D →
    circuitFun n D = circuitFun n C → C.size ≤ D.size

lemma minimal_no_alias (n : ℕ) (C : Circuit) (hmin : Minimal n C)
    (m p : ℕ) (hm : m < C.gates.length) (hp : p < n + m) :
    ¬ ∀ x : Fin n → Bool, val C.gates (n + m) x = val C.gates p x := by
  intro heq
  let D : Circuit := ⟨er n C.gates m p, rd n m p C.output⟩
  have hD : Monotone2 D := er_legal n C.gates m p hmin.1
  have hev : circuitFun n D = circuitFun n C := by
    funext x
    exact erase_congr C.gates hmin.1 m p hm hp x (Or.inl (heq x).symm)
      C.output (fun _ => (heq x).symm)
  have hle := hmin.2 D hD hev
  have hs : D.size = C.gates.length - 1 := er_len n C.gates m p
  change C.gates.length ≤ D.size at hle
  omega

lemma minimal_reader (n : ℕ) (hn : 0 < n) (C : Circuit) (hmin : Minimal n C)
    (m : ℕ) (hm : m < C.gates.length) (hout : C.output ≠ n + m) :
    ∃ j, m < j ∧ ∃ hj : j < C.gates.length, n + m ∈ C.gates[j].inputs := by
  by_contra hno
  have hno' : ∀ j (hj : j < C.gates.length), m < j → n + m ∉ C.gates[j].inputs := by
    intro j hj hmj hmem
    exact hno ⟨j, hmj, hj, hmem⟩
  let D : Circuit := ⟨er n C.gates m 0, rd n m 0 C.output⟩
  have hD : Monotone2 D := er_legal n C.gates m 0 hmin.1
  have hev : circuitFun n D = circuitFun n C := by
    funext x
    exact erase_congr C.gates hmin.1 m 0 hm (by omega) x (Or.inr hno')
      C.output (fun h => False.elim (hout h))
  have hle := hmin.2 D hD hev
  have hs : D.size = C.gates.length - 1 := er_len n C.gates m 0
  change C.gates.length ≤ D.size at hle
  omega

lemma strict_inputs (n : ℕ) (C : Circuit) (hmodel : PEqualNP.TopForm.IsAO2 n C)
    (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b : ℕ, C.gates[j].inputs = [a, b] ∧ a < n + j ∧ b < n + j := by
  have hlen := hmodel.2.2 C.gates[j] (List.getElem_mem hj)
  obtain ⟨a, b, hab⟩ : ∃ a b, C.gates[j].inputs = [a, b] := by
    have h := List.length_eq_two.mp hlen
    exact h
  refine ⟨a, b, hab, ?_, ?_⟩
  · have h := hmodel.2.1 j hj a
    apply h
    simpa only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      Option.getD_some, hab] using (show a ∈ [a, b] by simp)
  · have h := hmodel.2.1 j hj b
    apply h
    simpa only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      Option.getD_some, hab] using (show b ∈ [a, b] by simp)

lemma strict_gate (n : ℕ) (C : Circuit) (hmodel : PEqualNP.TopForm.IsAO2 n C)
    (x : Fin n → Bool) (j : ℕ) (hj : j < C.gates.length) :
    val C.gates (n + j) x = C.gates[j].op.eval
      (C.gates[j].inputs.map (fun w => val C.gates w x)) := by
  have hv := gate_val C.gates (List.ofFn x) j hj
  rw [List.length_ofFn] at hv
  rw [val, hv]
  congr 1
  apply List.map_congr_left
  intro w hw
  symm
  apply wire_take C.gates (List.ofFn x) j w _ (by omega)
  simpa only [List.length_ofFn] using hmodel.2.1 j hj w (by
    simpa only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      Option.getD_some] using hw)

lemma strict_distinct (n : ℕ) (C : Circuit) (hmin : Minimal n C)
    (hmodel : PEqualNP.TopForm.IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (a b : ℕ) (hab : C.gates[j].inputs = [a, b]) : a ≠ b := by
  intro he
  subst b
  have ha : a < n + j := hmodel.2.1 j hj a (by
    simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
      Option.getD_some, hab]
    simp)
  apply minimal_no_alias n C hmin j a hj ha
  intro x
  rw [strict_gate n C hmodel x j hj, hab]
  have hop : C.gates[j].op = GateOp.and ∨ C.gates[j].op = GateOp.or :=
    (hmin.1 C.gates[j] (List.getElem_mem hj)).1
  rcases hop with hand | hor
  · simp [hand, GateOp.eval]
  · simp [hor, GateOp.eval]

end PEqualNP.Outside.L_meta_1031.CycleStructure

namespace PEqualNP.Outside.L_meta_1031.CycleStructure

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_1031.Rel

lemma erase_decreases {n : ℕ} (gs : List Gate)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (m p : ℕ) (hm : m < gs.length) (hp : p < n + m)
    (x : Fin n → Bool) (himp : val gs p x = true → val gs (n + m) x = true) :
    ∀ i, val (er n gs m p) (rd n m p i) x = true → val gs i x = true := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    by_cases him : i < n + m
    · rw [rd_small n m p i him] at hi
      exact (er_pre gs legal m p hm x i him).1 hi
    by_cases hbig : n + gs.length ≤ i
    · have hnew : n + (er n gs m p).length ≤ rd n m p i := by
        rw [er_len]
        unfold rd
        split_ifs <;> omega
      rw [val_big (er n gs m p) x (rd n m p i) hnew] at hi
      contradiction
    by_cases hieq : i = n + m
    · subst i
      rw [rd_at] at hi
      exact himp ((er_pre gs legal m p hm x p hp).1 hi)
    obtain ⟨k, rfl⟩ : ∃ k, i = n + (k + 1) := ⟨i - n - 1, by omega⟩
    have hmk : m ≤ k := by omega
    have hk : k + 1 < gs.length := by omega
    have hkE : k < (er n gs m p).length := by rw [er_len]; omega
    have hg := er_ge n gs m p k hmk hk hkE
    rw [rd_succ n m p k hmk] at hi
    rcases (legal gs[k + 1] (List.getElem_mem hk)).1 with ha | ho
    · apply (val_and gs x (k + 1) hk ha).2
      intro j hj
      obtain ⟨hlt, hv⟩ := (val_and (er n gs m p) x k hkE (by rw [hg]; exact ha)).1 hi
        (rd n m p j) (by rw [hg]; exact List.mem_map.mpr ⟨j, hj, rfl⟩)
      have hjlt := (rd_lt n m p j k hp hmk).1 hlt
      exact ⟨hjlt, ih j hjlt hv⟩
    · obtain ⟨j', hj', hlt, hv⟩ :=
        (val_or (er n gs m p) x k hkE (by rw [hg]; exact ho)).1 hi
      rw [hg] at hj'
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hj'
      have hjlt := (rd_lt n m p j k hp hmk).1 hlt
      exact (val_or gs x (k + 1) hk ho).2 ⟨j, hj, hjlt, ih j hjlt hv⟩

lemma minimum_no_edge_domination (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hmin : Minimal n C)
    (hfun : ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
      decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true))
    (m p : ℕ) (hm : m < C.gates.length) (hp : p < n + m) :
    ¬ ((∀ x : Fin n → Bool, val C.gates p x = true → val C.gates (n + m) x = true) ∧
      ∀ u v : Fin n, G.Adj u v →
        val C.gates (n + m) (pairInput u v) = true →
        val C.gates p (pairInput u v) = true) := by
  rintro ⟨himp, hedge⟩
  let D : Circuit := ⟨er n C.gates m p, rd n m p C.output⟩
  have hD : Monotone2 D := er_legal n C.gates m p hmin.1
  have hpair : ∀ u v : Fin n, G.Adj u v → D.eval (List.ofFn (pairInput u v)) = true := by
    intro u v huv
    have heq : val C.gates p (pairInput u v) = val C.gates (n + m) (pairInput u v) := by
      rw [Bool.eq_iff_iff]
      exact ⟨himp _, hedge u v huv⟩
    have hd := erase_congr C.gates hmin.1 m p hm hp (pairInput u v)
      (Or.inl heq) C.output (fun _ => heq)
    change D.eval (List.ofFn (pairInput u v)) = C.eval (List.ofFn (pairInput u v)) at hd
    rw [hd, hfun, decide_eq_true_eq]
    exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
  have hsame : circuitFun n D = circuitFun n C := by
    funext x
    rw [Bool.eq_iff_iff]
    constructor
    · exact erase_decreases C.gates hmin.1 m p hm hp x (himp x) C.output
    · intro hx
      change C.eval (List.ofFn x) = true at hx
      rw [hfun, decide_eq_true_eq] at hx
      obtain ⟨u, v, huv, hux, hvx⟩ := hx
      exact val_mono D.gates hD (pairInput u v) x (by
        intro w hw
        simp only [pairInput, decide_eq_true_eq] at hw
        rcases hw with rfl | rfl
        · exact hux
        · exact hvx) D.output (hpair u v huv)
  have hle := hmin.2 D hD hsame
  have hs : D.size = C.gates.length - 1 := er_len n C.gates m p
  change C.gates.length ≤ D.size at hle
  omega

end PEqualNP.Outside.L_meta_1031.CycleStructure
