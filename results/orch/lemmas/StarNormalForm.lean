import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448_aux.StarNormal

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (ins : List ℕ)
    (U V : List Bool) (h : ∀ i, U.getD i false = true → V.getD i false = true) :
    op.eval (ins.map fun i => U.getD i false) = true →
    op.eval (ins.map fun i => V.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
    exact fun hall i hi => h i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact fun ⟨i, hi, hv⟩ => ⟨i, hi, h i hv⟩

lemma ofFn_mono (n : ℕ) (x y : Fin n → Bool) (hxy : ∀ v : Fin n, x v = true → y v = true)
    (w : ℕ) : (List.ofFn x).getD w false = true → (List.ofFn y).getD w false = true := by
  by_cases hw : w < n
  · simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, dite_true, Option.getD_some]
    exact hxy ⟨w, hw⟩
  · rw [List.getD_eq_default _ _ (by simp; omega)]
    simp


lemma mono2 (gs : List Gate)
    (hleg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ U V : List Bool, U.length = V.length →
      (∀ i, U.getD i false = true → V.getD i false = true) →
      ∀ i, (wf gs U).getD i false = true → (wf gs V).getD i false = true := by
  induction gs with
  | nil => intro U V _ h i; exact h i
  | cons g gs ih =>
    intro U V hlen h i
    have hg := (hleg g (by simp)).1
    have := ih (fun g' hg' => hleg g' (by simp [hg']))
      (U ++ [g.op.eval (g.inputs.map fun i => U.getD i false)])
      (V ++ [g.op.eval (g.inputs.map fun i => V.getD i false)]) (by simp [hlen]) (by
        intro t
        rcases Nat.lt_trichotomy t U.length with ht | ht | ht
        · rw [getD_snoc_lt _ _ _ ht, getD_snoc_lt _ _ _ (by omega)]; exact h t
        · subst ht
          rw [getD_snoc_eq]
          have e2 := getD_snoc_eq V (g.op.eval (g.inputs.map fun i => V.getD i false))
          rw [← hlen] at e2
          rw [e2]
          exact eval_mono g.op hg g.inputs U V h
        · rw [getD_snoc_gt _ _ _ ht]; intro hf; exact absurd hf (by simp)) i
    simpa [wf] using this

lemma wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

lemma wf_append (a b : List Gate) (w : List Bool) : wf (a ++ b) w = wf b (wf a w) := by
  simp [wf, List.foldl_append]

lemma wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma snoc_mono (W : List Bool) (v v' : Bool) (h : v = true → v' = true) (i : ℕ) :
    (W ++ [v]).getD i false = true → (W ++ [v']).getD i false = true := by
  rcases Nat.lt_trichotomy i W.length with hi | hi | hi
  · rw [getD_snoc_lt _ _ _ hi, getD_snoc_lt _ _ _ hi]; exact id
  · subst hi; rw [getD_snoc_eq, getD_snoc_eq]; exact h
  · rw [getD_snoc_gt _ _ _ hi]; intro hf; exact absurd hf (by simp)

lemma opmono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (a b a' b' : Bool)
    (ha : a = true → a' = true) (hb : b = true → b' = true) :
    op.eval [a, b] = true → op.eval [a', b'] = true := by
  rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval] <;> tauto

lemma core (n g : ℕ) (gates : List Gate) (hg : g < gates.length) (o w' : ℕ) (replacement : Gate)
    (hleg : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hw' : w' < n + g) (x : Fin n → Bool)
    (hF : (wf gates (List.ofFn x)).getD w' false = true → (wf gates (List.ofFn x)).getD o false = true)
    (hsame : (wf (gates.take g) (List.ofFn x)).getD w' false = false →
      replacement.op.eval (replacement.inputs.map fun i => (wf (gates.take g) (List.ofFn x)).getD i false)
        = gates[g].op.eval (gates[g].inputs.map fun i => (wf (gates.take g) (List.ofFn x)).getD i false))
    (hup : gates[g].op.eval (gates[g].inputs.map fun i => (wf (gates.take g) (List.ofFn x)).getD i false) = true →
      replacement.op.eval (replacement.inputs.map fun i => (wf (gates.take g) (List.ofFn x)).getD i false) = true) :
    (wf (gates.set g replacement) (List.ofFn x)).getD o false
      = (wf gates (List.ofFn x)).getD o false := by
  have h2 : ∀ a : Gate, gates.set g a = gates.take g ++ a :: gates.drop (g + 1) := by
    intro a
    rw [List.set_eq_take_append_cons_drop]
    simp [hg]
  have h1 : gates = gates.take g ++ gates[g] :: gates.drop (g + 1) := by
    rw [← h2]
    exact (List.set_getElem_self _).symm
  generalize hW : wf (gates.take g) (List.ofFn x) = W at *
  have hWlen : W.length = n + g := by
    rw [← hW, wf_len, List.length_ofFn, List.length_take, Nat.min_eq_left (le_of_lt hg)]
  have e1 : wf gates (List.ofFn x) = wf (gates.drop (g + 1))
      (W ++ [gates[g].op.eval (gates[g].inputs.map fun i => W.getD i false)]) := by
    conv_lhs => rw [h1]
    rw [wf_append, wf_cons, hW]
  have e2 : wf (gates.set g replacement) (List.ofFn x) = wf (gates.drop (g + 1))
      (W ++ [replacement.op.eval (replacement.inputs.map fun i => W.getD i false)]) := by
    rw [h2, wf_append, wf_cons, hW]
  rw [e2, e1]
  rw [e1] at hF
  cases hc : W.getD w' false
  · rw [hsame hc]
  · have hk : (wf (gates.drop (g + 1)) (W ++ [gates[g].op.eval (gates[g].inputs.map fun i => W.getD i false)])).getD w' false = true := by
      rw [wf_keep _ _ _ (by simp; omega), getD_snoc_lt _ _ _ (by omega)]
      exact hc
    have ht := hF hk
    rw [ht]
    exact mono2 (gates.drop (g + 1)) (fun g' hg' => hleg g' (List.mem_of_mem_drop hg')) _ _ (by simp)
      (snoc_mono W _ _ hup) o ht

lemma bypass_and (n : ℕ) (C : Circuit) (j w : ℕ)
    (hm : Monotone2 C) (hj : j < C.gates.length)
    (hop : C.gates[j].op = GateOp.and) (hw : w ∈ C.gates[j].inputs)
    (hwb : w < n + j)
    (hbelow : ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD w false = true → circuitFun n C x = true) :
    let D : Circuit := ⟨C.gates.set j ⟨GateOp.or, [w]⟩, C.output⟩
    Monotone2 D ∧ circuitFun n D = circuitFun n C ∧ D.size = C.size := by
  dsimp only
  refine ⟨?_, ?_, by simp [Circuit.size]⟩
  · intro g hg
    rcases List.mem_or_eq_of_mem_set hg with hg | rfl
    · exact hm g hg
    · simp
  · funext x
    apply core n j C.gates hj C.output w ⟨GateOp.or, [w]⟩
    · intro g hg
      have h := hm g hg
      simpa using h
    · exact hwb
    · exact hbelow x
    · intro hwfalse
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false, hwfalse]
      symm
      rw [hop]
      apply Bool.eq_false_iff.mpr
      intro htrue
      have h := (List.all_eq_true.mp htrue) _ (List.mem_map_of_mem hw)
      change (wf (C.gates.take j) (List.ofFn x)).getD w false = true at h
      rw [hwfalse] at h
      contradiction
    · intro htrue
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
        id_eq, Bool.or_false]
      rw [hop] at htrue
      exact (List.all_eq_true.mp htrue) _ (List.mem_map_of_mem hw)

namespace CopyDeletion

open PEqualNP.MetaComplexity.NestedCover

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma foldl_step_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ s : List Bool, gs.foldl step w = w ++ s ∧ s.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨s, hs, hl⟩ := ih (step w g)
    refine ⟨(g.op.eval (g.inputs.map fun i => w.getD i false)) :: s, ?_, by simp [hl]⟩
    rw [List.foldl_cons, hs]
    simp [step]

lemma foldl_step_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨s, hs, hl⟩ := foldl_step_prefix gs w
  simp [hs, hl]

lemma getD_append_left (w s : List Bool) (i : ℕ) (hi : i < w.length) :
    (w ++ s).getD i false = w.getD i false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_step_getD (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl step w).getD i false = w.getD i false := by
  obtain ⟨s, hs, _⟩ := foldl_step_prefix gs w
  rw [hs, getD_append_left w s i hi]

lemma getD_append_singleton_last (w : List Bool) (b : Bool) :
    (w ++ [b]).getD w.length false = b := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_append_singleton (w : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  rcases Nat.lt_or_gt_of_ne hi with h | h
  · exact getD_append_left w [b] i h
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega : (w ++ [b]).length ≤ i),
      List.getElem?_eq_none (by omega : w.length ≤ i)]
lemma foldl_split (gs : List Gate) (k : ℕ) (g : Gate) (hg : gs[k]? = some g) (w0 : List Bool) :
    gs.foldl step w0 = (gs.drop (k + 1)).foldl step (step ((gs.take k).foldl step w0) g) := by
  have hk : k < gs.length := by
    rcases (List.getElem?_eq_some_iff.mp hg) with ⟨hk, _⟩
    exact hk
  have hgk : gs[k] = g := (List.getElem?_eq_some_iff.mp hg).2
  conv_lhs => rw [← List.take_append_drop k gs, List.drop_eq_getElem_cons hk, hgk]
  rw [List.foldl_append, List.foldl_cons]

lemma take_fold_length (gs : List Gate) (k : ℕ) (hk : k < gs.length) (w0 : List Bool) :
    ((gs.take k).foldl step w0).length = w0.length + k := by
  rw [foldl_step_length, List.length_take]
  omega

lemma wires_copy (F : Circuit) (k u : ℕ) (hk : F.gates[k]? = some ⟨GateOp.or, [u]⟩)
    (w0 : List Bool) (hu : u < w0.length + k) :
    (F.wires w0).getD (w0.length + k) false = (F.wires w0).getD u false := by
  have hk' : k < F.gates.length := (List.getElem?_eq_some_iff.mp hk).1
  rw [wires_eq, foldl_split F.gates k _ hk w0]
  have hl := take_fold_length F.gates k hk' w0
  set Wp := (F.gates.take k).foldl step w0
  rw [foldl_step_getD _ _ _ (by simp [step]; omega), foldl_step_getD _ _ _ (by simp [step]; omega)]
  unfold step
  rw [← hl, getD_append_singleton_last, getD_append_left _ _ _ (by omega)]
  simp [GateOp.eval]


def sig (m u : ℕ) (i : ℕ) : ℕ := if i < m then i else if i = m then u else i - 1

def rd (m u : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (sig m u)⟩

def sg (k : ℕ) (j : ℕ) : ℕ := if j < k then j else j - 1

def del (n k u : ℕ) (E : Circuit) : Circuit :=
  ⟨(E.gates.eraseIdx k).map (rd (n + k) u), sig (n + k) u E.output⟩

lemma sig_gate (n k u j : ℕ) (hj : j ≠ k) : sig (n + k) u (n + j) = n + sg k j := by
  unfold sig sg
  split_ifs <;> omega

def Rel (m u : ℕ) (a b : List Bool) : Prop :=
  a.length = b.length + 1 ∧ m < a.length ∧ ∀ i, b.getD (sig m u i) false = a.getD i false

lemma getD_oob (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma rel_step (m u : ℕ) (hu : u < m) (a b : List Bool) (g : Gate) (h : Rel m u a b) :
    Rel m u (step a g) (step b (rd m u g)) := by
  obtain ⟨hl, hm, hv⟩ := h
  have hev : (rd m u g).op.eval ((rd m u g).inputs.map fun i => b.getD i false) =
      g.op.eval (g.inputs.map fun i => a.getD i false) := by
    simp only [rd, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact hv i
  unfold step
  rw [hev]
  set v := g.op.eval (g.inputs.map fun i => a.getD i false)
  refine ⟨by simp [hl], by simp; omega, ?_⟩
  intro i
  rcases Nat.lt_trichotomy i a.length with h1 | h1 | h1
  · have hs : sig m u i < b.length := by unfold sig; split_ifs <;> omega
    rw [getD_append_left _ _ _ hs, getD_append_left _ _ _ h1, hv]
  · have hs : sig m u i = b.length := by unfold sig; split_ifs <;> omega
    rw [hs, getD_append_singleton_last, h1, getD_append_singleton_last]
  · have hs : sig m u i > b.length := by unfold sig; split_ifs <;> omega
    rw [getD_oob _ _ (by simp; omega), getD_oob _ _ (by simp; omega)]

lemma rel_fold (m u : ℕ) (hu : u < m) (gs : List Gate) : ∀ a b : List Bool, Rel m u a b →
    Rel m u (gs.foldl step a) ((gs.map (rd m u)).foldl step b) := by
  induction gs with
  | nil => intro a b h; simpa using h
  | cons g gs ih =>
    intro a b h
    simp only [List.foldl_cons, List.map_cons]
    exact ih _ _ (rel_step m u hu a b g h)

lemma rd_id (m u : ℕ) (g : Gate) (h : ∀ i ∈ g.inputs, i < m) : rd m u g = g := by
  obtain ⟨op, ins⟩ := g
  simp only [rd, Gate.mk.injEq, true_and]
  conv_rhs => rw [← List.map_id ins]
  apply List.map_congr_left
  intro i hi
  have := h i hi
  simp [sig, this]

lemma del_fun (n k u : ℕ) (E : Circuit) (hk : k < E.gates.length) (hu : u < n + k)
    (hpre : ∀ g ∈ E.gates.take k, ∀ i ∈ g.inputs, i < n + k)
    (hcopy : ∀ x : Fin n → Bool,
      (E.wires (List.ofFn x)).getD (n + k) false = (E.wires (List.ofFn x)).getD u false) :
    circuitFun n (del n k u E) = circuitFun n E := by
  funext x
  have hc := hcopy x
  unfold circuitFun Circuit.eval
  have hgk : E.gates[k]? = some E.gates[k] := List.getElem?_eq_getElem hk
  set gk := E.gates[k]
  set w0 := List.ofFn x with hw0
  have hw0l : w0.length = n := by simp [hw0]
  have hl := take_fold_length E.gates k hk w0
  rw [hw0l] at hl
  set Wp := (E.gates.take k).foldl step w0 with hWp
  have hW : E.wires w0 = (E.gates.drop (k + 1)).foldl step (step Wp gk) := by
    rw [wires_eq, foldl_split E.gates k gk hgk w0]
  have hD : (del n k u E).wires w0 =
      ((E.gates.drop (k + 1)).map (rd (n + k) u)).foldl step Wp := by
    rw [wires_eq]
    simp only [del]
    rw [List.eraseIdx_eq_take_drop_succ, List.map_append, List.foldl_append]
    congr 1
    rw [hWp]
    congr 1
    conv_rhs => rw [← List.map_id (E.gates.take k)]
    apply List.map_congr_left
    intro g hg
    exact rd_id _ _ g (hpre g hg)
  -- the value of gate k equals that of u
  have hvk : (step Wp gk).getD (n + k) false = Wp.getD u false := by
    rw [hW, foldl_step_getD _ _ _ (by simp [step]; omega),
      foldl_step_getD _ _ _ (by simp [step]; omega)] at hc
    rw [hc]
    unfold step
    exact getD_append_left _ _ _ (by omega)
  have hrel0 : Rel (n + k) u (step Wp gk) Wp := by
    refine ⟨by simp [step], by simp [step]; omega, ?_⟩
    intro i
    rcases Nat.lt_trichotomy i (n + k) with h1 | h1 | h1
    · have : sig (n + k) u i = i := by simp [sig, h1]
      rw [this]
      unfold step
      rw [getD_append_left _ _ _ (by omega)]
    · have : sig (n + k) u i = u := by simp [sig, h1]
      rw [this, h1, hvk]
    · have : sig (n + k) u i = i - 1 := by
        unfold sig; split_ifs <;> omega
      rw [this, getD_oob _ _ (by omega), getD_oob _ _ (by simp [step]; omega)]
  have hrel := rel_fold (n + k) u hu (E.gates.drop (k + 1)) _ _ hrel0
  rw [hD, hW]
  exact hrel.2.2 E.output

lemma del_length (n k u : ℕ) (E : Circuit) (hk : k < E.gates.length) :
    (del n k u E).gates.length + 1 = E.gates.length := by
  simp only [del, List.length_map, List.length_eraseIdx, if_pos hk]
  omega
lemma del_mono (n k u : ℕ) (E : Circuit) (hE : Monotone2 E) : Monotone2 (del n k u E) := by
  intro g hg
  simp only [del, List.mem_map] at hg
  obtain ⟨g0, hg0, rfl⟩ := hg
  have := hE g0 (List.mem_of_mem_eraseIdx hg0)
  simpa [rd] using this

lemma gateAt_some (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    C.gates[j]? = some (gateAt C j) := by
  rw [List.getElem?_eq_getElem hj]
  simp [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]

lemma readsBack_get (n : ℕ) (C : Circuit) (h : ReadsBack n C) (j : ℕ) (g : Gate)
    (hg : C.gates[j]? = some g) : ∀ i ∈ g.inputs, i < n + j := by
  have hj : j < C.gates.length := (List.getElem?_eq_some_iff.mp hg).1
  have := gateAt_some C j hj
  rw [hg] at this
  cases this
  exact h j hj

lemma readsBack_of_get (n : ℕ) (C : Circuit)
    (h : ∀ j (g : Gate), C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j) : ReadsBack n C := by
  intro j hj
  exact h j _ (gateAt_some C j hj)
lemma readsBack_take (n : ℕ) (C : Circuit) (h : ReadsBack n C) (k : ℕ) :
    ∀ g ∈ C.gates.take k, ∀ i ∈ g.inputs, i < n + k := by
  intro g hg i hi
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
  rw [List.getElem_take] at hi
  have hjl : j < k := by simp at hj; omega
  have hj' : j < C.gates.length := by simp at hj; omega
  have := readsBack_get n C h j _ (List.getElem?_eq_getElem hj') i hi
  omega

lemma least_no_and_operand_below (n : ℕ) (C : Circuit)
    (hmin : IsMinimalMonoCircuit n C) (hr : ReadsBack n C)
    (j : ℕ) (hj : j < C.gates.length) (hop : C.gates[j].op = GateOp.and)
    (w : ℕ) (hw : w ∈ C.gates[j].inputs) :
    ¬ (∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD w false = true → circuitFun n C x = true) := by
  intro hbelow
  have hwb : w < n + j := readsBack_get n C hr j _ (List.getElem?_eq_getElem hj) w hw
  obtain ⟨hm, hf, hs⟩ := bypass_and n C j w hmin.1 hj hop hw hwb hbelow
  let E : Circuit := ⟨C.gates.set j ⟨GateOp.or, [w]⟩, C.output⟩
  have hE : E.gates[j]? = some ⟨GateOp.or, [w]⟩ := by
    simp [E, List.getElem?_set, hj]
  have hjE : j < E.gates.length := by simpa [E] using hj
  have hpre : ∀ g ∈ E.gates.take j, ∀ i ∈ g.inputs, i < n + j := by
    simpa [E, List.take_set_of_le] using readsBack_take n C hr j
  have hcopy : ∀ x : Fin n → Bool,
      (E.wires (List.ofFn x)).getD (n + j) false = (E.wires (List.ofFn x)).getD w false := by
    intro x
    simpa using wires_copy E j w hE (List.ofFn x) (by simpa using hwb)
  have hdf := del_fun n j w E hjE hwb hpre hcopy
  have hlen := del_length n j w E hjE
  have hle := hmin.2 (del n j w E) (del_mono n j w E hm) (hdf.trans hf)
  change (del n j w E).gates.length + 1 = E.size at hlen
  change C.size ≤ (del n j w E).gates.length at hle
  change E.size = C.size at hs
  omega

end CopyDeletion

end PEqualNP.Outside.L_meta_2448_aux.StarNormal
