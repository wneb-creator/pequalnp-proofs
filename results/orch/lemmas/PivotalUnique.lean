import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2448_aux.PivotalUnique

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

open PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

lemma circuit_mono (n : ℕ) (C : Circuit) (hm : Monotone2 C)
    (x y : Fin n → Bool) (hxy : ∀ v, x v = true → y v = true) :
    circuitFun n C x = true → circuitFun n C y = true := by
  apply mono2 C.gates
  · intro g hg
    simpa using hm g hg
  · simp
  · exact ofFn_mono n x y hxy

lemma graph_sandwich (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (D : Circuit) (hm : Monotone2 D)
    (hbelow : ∀ x : Fin n → Bool, circuitFun n D x = true → graphFun G ∅ x = true)
    (hedges : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = graphFun G ∅ := by
  funext x
  apply Bool.eq_iff_iff.mpr
  refine ⟨hbelow x, ?_⟩
  intro hx
  obtain ⟨u, v, huv, hu, hv⟩ : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
    simpa [graphFun] using hx
  apply circuit_mono n D hm (pairInput u v) x _ (hedges u v huv)
  intro w hw
  have h : w = u ∨ w = v := of_decide_eq_true hw
  rcases h with rfl | rfl
  · exact hu
  · exact hv

lemma graph_rewrite (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C D : Circuit) (hm : Monotone2 D) (hC : circuitFun n C = graphFun G ∅)
    (hdown : ∀ x : Fin n → Bool, circuitFun n D x = true → circuitFun n C x = true)
    (hedges : ∀ u v : Fin n, G.Adj u v → circuitFun n D (pairInput u v) = true) :
    circuitFun n D = circuitFun n C := by
  rw [hC]
  apply graph_sandwich n G D hm _ hedges
  intro x hx
  rw [← hC]
  exact hdown x hx

lemma set_eval_mono (n j : ℕ) (C : Circuit) (hm : Monotone2 C)
    (hj : j < C.gates.length) (r s : Gate) (x : Fin n → Bool)
    (hle : r.op.eval (r.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false) = true →
      s.op.eval (s.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false) = true) :
    circuitFun n ⟨C.gates.set j r, C.output⟩ x = true →
    circuitFun n ⟨C.gates.set j s, C.output⟩ x = true := by
  change (wf (C.gates.set j r) (List.ofFn x)).getD C.output false = true →
    (wf (C.gates.set j s) (List.ofFn x)).getD C.output false = true
  have hs : ∀ t : Gate, C.gates.set j t =
      C.gates.take j ++ t :: C.gates.drop (j + 1) := by
    intro t
    rw [List.set_eq_take_append_cons_drop]
    simp [hj]
  rw [hs r, hs s, wf_append, wf_append, wf_cons, wf_cons]
  apply mono2 (C.gates.drop (j + 1))
  · intro g hg
    simpa using hm g (List.mem_of_mem_drop hg)
  · simp
  · exact snoc_mono _ _ _ hle

lemma set_eval_eq (n j : ℕ) (C : Circuit) (hm : Monotone2 C)
    (hj : j < C.gates.length) (r s : Gate) (x : Fin n → Bool)
    (heq : r.op.eval (r.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false) =
      s.op.eval (s.inputs.map fun i =>
      (wf (C.gates.take j) (List.ofFn x)).getD i false)) :
    circuitFun n ⟨C.gates.set j r, C.output⟩ x =
    circuitFun n ⟨C.gates.set j s, C.output⟩ x := by
  apply Bool.eq_iff_iff.mpr
  exact ⟨set_eval_mono n j C hm hj r s x (by rw [heq]; exact id),
    set_eval_mono n j C hm hj s r x (by rw [heq]; exact id)⟩

lemma set_gate_val (n j : ℕ) (C : Circuit) (hj : j < C.gates.length)
    (r : Gate) (x : Fin n → Bool) :
    gateVal n ⟨C.gates.set j r, C.output⟩ j x =
      r.op.eval (r.inputs.map fun i =>
        (wf (C.gates.take j) (List.ofFn x)).getD i false) := by
  change (wf (C.gates.set j r) (List.ofFn x)).getD (n + j) false = _
  rw [List.set_eq_take_append_cons_drop]
  simp only [hj, ↓reduceIte]
  rw [wf_append, wf_cons]
  have hl : (wf (C.gates.take j) (List.ofFn x)).length = n + j := by
    rw [wf_len, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  rw [wf_keep _ _ _ (by simp [hl]), ← hl, getD_snoc_eq]

lemma replace_by_pivotal_pair (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hm : Monotone2 C) (hfun : circuitFun n C = graphFun G ∅)
    (j : ℕ) (hj : j < C.gates.length) (u v : Fin n) (huv : G.Adj u v)
    (hcritical : circuitFun n ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩
      (pairInput u v) = false)
    (hunique : ∀ a b : Fin n, G.Adj a b →
      circuitFun n ⟨C.gates.set j ⟨GateOp.or, []⟩, C.output⟩ (pairInput a b) = false →
      (a = u ∧ b = v) ∨ (a = v ∧ b = u)) :
    let D : Circuit := ⟨C.gates.set j ⟨GateOp.and, [u.val, v.val]⟩, C.output⟩
    Monotone2 D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = C.size ∧
      ∀ a b : Fin n, gateVal n D j (pairInput a b) = true → a = u ∨ b = u := by
  classical
  dsimp only
  let z : Gate := ⟨GateOp.or, []⟩
  let r : Gate := ⟨GateOp.and, [u.val, v.val]⟩
  let D : Circuit := ⟨C.gates.set j r, C.output⟩
  let V (x : Fin n → Bool) := C.gates[j].op.eval
    (C.gates[j].inputs.map fun i => (wf (C.gates.take j) (List.ofFn x)).getD i false)
  have hsame : (⟨C.gates.set j C.gates[j], C.output⟩ : Circuit) = C := by simp
  have hVm : ∀ x, gateVal n C j x = V x := by
    intro x
    have h := set_gate_val n j C hj C.gates[j] x
    rw [hsame] at h
    exact h
  have hinput : ∀ (x : Fin n → Bool) (t : Fin n),
      (wf (C.gates.take j) (List.ofFn x)).getD t.val false = x t := by
    intro x t
    rw [wf_keep _ _ _ (by simp)]
    simp [List.getD_eq_getElem?_getD, t.isLt]
  have hedge : ∀ a b : Fin n, G.Adj a b → circuitFun n C (pairInput a b) = true := by
    intro a b hab
    rw [hfun]
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq]
    exact ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩
  have pivotal_value : ∀ a b : Fin n, G.Adj a b →
      circuitFun n ⟨C.gates.set j z, C.output⟩ (pairInput a b) = false →
      V (pairInput a b) = true := by
    intro a b hab hp
    by_contra hn
    have hf := Bool.eq_false_iff.mpr hn
    have he := set_eval_eq n j C hm hj C.gates[j] z (pairInput a b)
      (by change V (pairInput a b) = false; exact hf)
    rw [hsame, hedge a b hab, hp] at he
    contradiction
  have hVuv := pivotal_value u v huv hcritical
  have hdown_value : ∀ x : Fin n → Bool,
      r.op.eval (r.inputs.map fun i =>
        (wf (C.gates.take j) (List.ofFn x)).getD i false) = true → V x = true := by
    intro x hx
    simp only [r, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true, hinput, Bool.and_eq_true] at hx
    have hxy : ∀ w : Fin n, pairInput u v w = true → x w = true := by
      intro w hw
      rcases of_decide_eq_true hw with h | h
      · simpa only [h] using hx.1
      · simpa only [h] using hx.2
    have hstart : circuitFun n ⟨C.gates, n + j⟩ (pairInput u v) = true := by
      change gateVal n C j (pairInput u v) = true
      rw [hVm]
      exact hVuv
    have hend := circuit_mono n ⟨C.gates, n + j⟩ hm (pairInput u v) x hxy hstart
    change gateVal n C j x = true at hend
    rwa [hVm] at hend
  have hDm : Monotone2 D := by
    intro g hg
    rcases List.mem_or_eq_of_mem_set hg with hg | rfl
    · exact hm g hg
    · simp [r]
  have hdown : ∀ x, circuitFun n D x = true → circuitFun n C x = true := by
    intro x hx
    rw [← hsame]
    exact set_eval_mono n j C hm hj r C.gates[j] x (hdown_value x) hx
  have hedges : ∀ a b : Fin n, G.Adj a b → circuitFun n D (pairInput a b) = true := by
    intro a b hab
    by_cases hp : circuitFun n ⟨C.gates.set j z, C.output⟩ (pairInput a b) = false
    · have hv := pivotal_value a b hab hp
      have hr : r.op.eval (r.inputs.map fun i =>
          (wf (C.gates.take j) (List.ofFn (pairInput a b))).getD i false) = true := by
        rcases hunique a b hab hp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;>
          simp only [r, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, id_eq, Bool.and_true, hinput] <;> simp [pairInput]
      have he := set_eval_eq n j C hm hj r C.gates[j] (pairInput a b) (hr.trans hv.symm)
      rw [hsame, hedge a b hab] at he
      exact he
    · have hz : circuitFun n ⟨C.gates.set j z, C.output⟩ (pairInput a b) = true := by
        cases he : circuitFun n ⟨C.gates.set j z, C.output⟩ (pairInput a b) <;> simp_all
      exact set_eval_mono n j C hm hj z r (pairInput a b) (by simp [z, GateOp.eval]) hz
  refine ⟨hDm, graph_sandwich n G D hDm ?_ hedges, by simp [Circuit.size], ?_⟩
  · intro x hx
    rw [← hfun]
    exact hdown x hx
  · intro a b h
    rw [set_gate_val n j C hj] at h
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
      List.all_nil, id_eq, Bool.and_true, hinput, Bool.and_eq_true] at h
    have hu : u = a ∨ u = b := of_decide_eq_true h.1
    exact hu.imp Eq.symm Eq.symm

end PEqualNP.Outside.L_meta_2448_aux.PivotalUnique
