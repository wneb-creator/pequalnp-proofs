import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_650.OrReplacement
open PEqualNP.CircuitLowerBounds

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

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

lemma wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

lemma wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma evalT (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (ins.map f) = true → op.eval (ins.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

lemma wf_mono (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (U V : List Bool) (hlen : U.length = V.length)
    (hUV : ∀ i, U.getD i false = true → V.getD i false = true) :
    ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs generalizing U V with
  | nil => exact hUV
  | cons g gs ih =>
    rw [wf_cons, wf_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')) _ _ (by simp [hlen])
    intro i hi
    rcases Nat.lt_trichotomy i U.length with h | h | h
    · rw [getD_snoc_lt _ _ _ h] at hi
      rw [getD_snoc_lt _ _ _ (by omega)]
      exact hUV i hi
    · subst i
      rw [getD_snoc_eq] at hi
      rw [hlen, getD_snoc_eq]
      exact evalT g.op (hgs g (List.mem_cons_self ..)) g.inputs _ _ hUV hi
    · rw [getD_snoc_gt _ _ _ h] at hi
      exact Bool.noConfusion hi

lemma wires_mono {n : ℕ} (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    ∀ w, (C.wires (List.ofFn x)).getD w false = true →
      (C.wires (List.ofFn y)).getD w false = true := by
  apply wf_mono C.gates (fun g hg => (hm g hg).1) _ _ (by simp)
  intro i hi
  by_cases h : i < n
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h] using
      hxy ⟨i, h⟩ (by simpa [List.getD_eq_getElem?_getD, List.getElem?_ofFn, h] using hi)
  · simp [List.getD_eq_getElem?_getD, h] at hi

lemma input_wire {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    (C.wires (List.ofFn x)).getD p.val false = x p := by
  change (wf C.gates (List.ofFn x)).getD p.val false = x p
  rw [wf_keep _ _ _ (by simpa using p.isLt)]
  simp [List.getD_eq_getElem?_getD, p.isLt]

def replace {n : ℕ} (C : Circuit) (m : ℕ) (p q : Fin n) : Circuit :=
  ⟨C.gates.set m ⟨GateOp.or, [p.val, q.val]⟩, C.output⟩

def andCount (C : Circuit) : ℕ :=
  C.gates.countP (fun g => match g.op with | .and => true | _ => false)

lemma replace_size {n : ℕ} (C : Circuit) (m : ℕ) (p q : Fin n) :
    (replace C m p q).size = C.size := by simp [replace, Circuit.size]

lemma replace_monotone {n : ℕ} (C : Circuit) (m : ℕ) (p q : Fin n)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (hi : m < C.gates.length) :
    PEqualNP.MetaComplexity.Monotone2 (replace C m p q) := by
  intro g hg
  change g ∈ C.gates.set m ⟨GateOp.or, [p.val, q.val]⟩ at hg
  rw [List.set_eq_take_cons_drop _ hi] at hg
  rcases List.mem_append.mp hg with h | h
  · exact hm g (List.mem_of_mem_take h)
  · rcases List.mem_cons.mp h with rfl | h
    · simp [PEqualNP.MetaComplexity.Monotone2]
    · exact hm g (List.mem_of_mem_drop h)

lemma replace_back {n : ℕ} (C : Circuit) (m : ℕ) (p q : Fin n)
    (hr : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (hi : m < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.ReadsBack n (replace C m p q) := by
  intro j hj i hmem
  by_cases he : m = j
  · subst j
    simp [replace, PEqualNP.MetaComplexity.NestedCover.gateAt,
      List.getD_eq_getElem?_getD, List.getElem?_set, hi] at hmem
    rcases hmem with rfl | rfl <;> omega
  · have hg : PEqualNP.MetaComplexity.NestedCover.gateAt (replace C m p q) j =
        PEqualNP.MetaComplexity.NestedCover.gateAt C j := by
      simp [replace, PEqualNP.MetaComplexity.NestedCover.gateAt,
        List.getD_eq_getElem?_getD, List.getElem?_set, he]
    rw [hg] at hmem
    exact hr j (by simpa [replace] using hj) i hmem

lemma replace_andCount {n : ℕ} (C : Circuit) (m : ℕ) (p q : Fin n)
    (hi : m < C.gates.length) (hop : C.gates[m].op = GateOp.and) :
    andCount (replace C m p q) + 1 = andCount C := by
  have splitC : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  let f : Gate → Bool := fun g => match g.op with | .and => true | _ => false
  have hand : f C.gates[m] = true := by simp [f, hop]
  have hnew : f ⟨GateOp.or, [p.val, q.val]⟩ = false := rfl
  have old := congrArg (List.countP f) splitC
  rw [List.countP_append, List.countP_cons, hand] at old
  change List.countP f (C.gates.set m ⟨GateOp.or, [p.val, q.val]⟩) + 1 =
    List.countP f C.gates
  rw [List.set_eq_take_cons_drop _ hi, List.countP_append, List.countP_cons, hnew]
  simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
  simp only [↓reduceIte] at old
  omega

lemma original_wires {n : ℕ} (C : Circuit) (m : ℕ) (hi : m < C.gates.length)
    (x : Fin n → Bool) :
    C.wires (List.ofFn x) = wf (C.gates.drop (m + 1))
      (wf (C.gates.take m) (List.ofFn x) ++
        [(C.wires (List.ofFn x)).getD (n + m) false]) := by
  have splitC : C.gates = C.gates.take m ++ C.gates[m] :: C.gates.drop (m + 1) := by
    rw [← List.drop_eq_getElem_cons hi, List.take_append_drop]
  have gate := gate_val C.gates (List.ofFn x) m hi
  simp only [List.length_ofFn] at gate
  change wf C.gates (List.ofFn x) = wf (C.gates.drop (m + 1))
    (wf (C.gates.take m) (List.ofFn x) ++ [(wf C.gates (List.ofFn x)).getD (n + m) false])
  rw [gate]
  conv_lhs => rw [splitC]
  rw [wf_append, wf_cons]

lemma replacement_wires {n : ℕ} (C : Circuit) (m : ℕ) (p q : Fin n)
    (hi : m < C.gates.length) (x : Fin n → Bool) :
    (replace C m p q).wires (List.ofFn x) = wf (C.gates.drop (m + 1))
      (wf (C.gates.take m) (List.ofFn x) ++ [x p || x q]) := by
  change wf (C.gates.set m ⟨GateOp.or, [p.val, q.val]⟩) (List.ofFn x) = _
  rw [List.set_eq_take_cons_drop _ hi, wf_append, wf_cons]
  have hp : (wf (C.gates.take m) (List.ofFn x)).getD p.val false = x p := by
    rw [wf_keep _ _ _ (by simpa using p.isLt)]
    simp [List.getD_eq_getElem?_getD, p.isLt]
  have hq : (wf (C.gates.take m) (List.ofFn x)).getD q.val false = x q := by
    rw [wf_keep _ _ _ (by simpa using q.isLt)]
    simp [List.getD_eq_getElem?_getD, q.isLt]
  simp only [List.map_cons, List.map_nil, hp, hq, GateOp.eval, List.any_cons,
    List.any_nil, id_eq, Bool.or_false]

lemma replace_eval_eq {n : ℕ} (C : Circuit) (m : ℕ) (p q : Fin n)
    (hi : m < C.gates.length) (x : Fin n → Bool)
    (hval : (C.wires (List.ofFn x)).getD (n + m) false = (x p || x q)) :
    (replace C m p q).eval (List.ofFn x) = C.eval (List.ofFn x) := by
  unfold Circuit.eval
  rw [replacement_wires C m p q hi x, original_wires C m hi x, hval]
  rfl

lemma replace_eval_le {n : ℕ} (C : Circuit) (m : ℕ) (p q : Fin n)
    (hm : PEqualNP.MetaComplexity.Monotone2 C) (hi : m < C.gates.length)
    (x : Fin n → Bool)
    (hval : (x p || x q) = true → (C.wires (List.ofFn x)).getD (n + m) false = true) :
    (replace C m p q).eval (List.ofFn x) = true → C.eval (List.ofFn x) = true := by
  unfold Circuit.eval
  rw [replacement_wires C m p q hi x, original_wires C m hi x]
  apply wf_mono _ (fun g hg => (hm g (List.mem_of_mem_drop hg)).1) _ _ (by simp)
  intro i htrue
  let W := wf (C.gates.take m) (List.ofFn x)
  rcases Nat.lt_trichotomy i W.length with h | h | h
  · rw [getD_snoc_lt _ _ _ h] at htrue
    rw [getD_snoc_lt _ _ _ h]
    exact htrue
  · subst i
    rw [getD_snoc_eq] at htrue
    rw [getD_snoc_eq]
    exact hval htrue
  · rw [getD_snoc_gt _ _ _ h] at htrue
    exact Bool.noConfusion htrue

lemma replace_preserves_edge_function
    {n : ℕ} (C : Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (hr : PEqualNP.MetaComplexity.NestedCover.ReadsBack n C)
    (m : ℕ) (hi : m < C.gates.length) (p q : Fin n)
    (hop : C.gates[m].op = GateOp.and) (E : Fin n → Fin n → Prop)
    (correct : ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = true ↔ ∃ u v, E u v ∧ x u = true ∧ x v = true)
    (singleP : (C.wires (List.ofFn (fun i : Fin n => decide (i = p)))).getD
      (n + m) false = true)
    (singleQ : (C.wires (List.ofFn (fun i : Fin n => decide (i = q)))).getD
      (n + m) false = true)
    (pairs : ∀ u v, E u v →
      (C.wires (List.ofFn (fun i : Fin n => decide (i = u ∨ i = v)))).getD
        (n + m) false = (decide (p = u ∨ p = v) || decide (q = u ∨ q = v))) :
    PEqualNP.MetaComplexity.Monotone2 (replace C m p q) ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack n (replace C m p q) ∧
      (replace C m p q).size = C.size ∧
      andCount (replace C m p q) + 1 = andCount C ∧
      ∀ x : Fin n → Bool,
        (replace C m p q).eval (List.ofFn x) = true ↔
          ∃ u v, E u v ∧ x u = true ∧ x v = true := by
  have mono := replace_monotone C m p q hm hi
  refine ⟨mono, replace_back C m p q hr hi, replace_size C m p q,
    replace_andCount C m p q hi hop, ?_⟩
  intro x
  constructor
  · intro hnew
    apply (correct x).mp
    apply replace_eval_le C m p q hm hi x _ hnew
    intro hor
    rcases Bool.or_eq_true_iff.mp hor with hp | hq
    · apply wires_mono C hm (fun i : Fin n => decide (i = p)) x _ (n + m) singleP
      intro i he
      have hip : i = p := of_decide_eq_true he
      simpa [hip] using hp
    · apply wires_mono C hm (fun i : Fin n => decide (i = q)) x _ (n + m) singleQ
      intro i he
      have hiq : i = q := of_decide_eq_true he
      simpa [hiq] using hq
  · rintro ⟨u, v, huv, hu, hv⟩
    let edge := fun i : Fin n => decide (i = u ∨ i = v)
    have hedge : ∀ i, edge i = true → x i = true := by
      intro i he
      rcases of_decide_eq_true he with rfl | rfl
      · exact hu
      · exact hv
    have hC : C.eval (List.ofFn edge) = true :=
      (correct edge).mpr ⟨u, v, huv, by simp [edge], by simp [edge]⟩
    have hD : (replace C m p q).eval (List.ofFn edge) = true :=
      (replace_eval_eq C m p q hi edge (pairs u v huv)).trans hC
    exact wires_mono (replace C m p q) mono edge x hedge C.output hD

end PEqualNP.Outside.L_meta_650.OrReplacement
