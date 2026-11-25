import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

lemma edge_list_circuit_edges {n : ℕ} (es : List (Fin n × Fin n)) :
    ∀ (m a : ℕ), n ≤ m → a < m →
      ∃ (gs : List Gate) (o : ℕ),
        (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
        (∀ g ∈ gs, g.op = GateOp.and → ∃ p ∈ es, g.inputs = [p.1.val, p.2.val]) ∧
        o < m + gs.length ∧
        ∀ w : List Bool, w.length = m →
          (run gs w).getD o false =
            (w.getD a false || es.any (fun p => w.getD p.1.val false && w.getD p.2.val false)) := by
  induction es with
  | nil =>
      intro m a _ ha
      refine ⟨[], a, by simp, by simp, by simpa using ha, ?_⟩
      intro w _
      simp [run]
  | cons p es ih =>
      intro m a hnm ha
      obtain ⟨gs, o, hgs, hpair, ho, hev⟩ := ih (m + 2) (m + 1) (by omega) (by omega)
      let pre : List Gate := [⟨GateOp.and, [p.1.val, p.2.val]⟩, ⟨GateOp.or, [a, m]⟩]
      refine ⟨pre ++ gs, o, ?_, ?_, ?_, ?_⟩
      · intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · simp only [pre, List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl <;> simp
        · exact hgs g hg
      · intro g hg hop
        rcases List.mem_append.mp hg with hg | hg
        · simp only [pre, List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl
          · exact ⟨p, List.mem_cons_self, rfl⟩
          · cases hop
        · obtain ⟨q, hq, hin⟩ := hpair g hg hop
          exact ⟨q, List.mem_cons_of_mem p hq, hin⟩
      · simp only [List.length_append]
        have : pre.length = 2 := rfl
        omega
      · intro w hw
        let e := w.getD p.1.val false && w.getD p.2.val false
        have hstep : run pre w = w ++ [e, w.getD a false || e] := by
          have ha' : a < w.length := by omega
          simp [pre, run, GateOp.eval, List.getElem?_append_left ha', ← hw, e]
        have hlen : (run pre w).length = m + 2 := by rw [hstep]; simp [hw]
        have old (i : Fin n) : (run pre w).getD i.val false = w.getD i.val false := by
          rw [hstep]
          exact List.getD_append _ _ _ _ (by have := i.isLt; omega)
        have acc : (run pre w).getD (m + 1) false = (w.getD a false || e) := by
          rw [hstep]
          simp [← hw]
        rw [run_append, hev _ hlen, acc]
        have he : es.any (fun p => (run pre w).getD p.1.val false &&
            (run pre w).getD p.2.val false) =
            es.any (fun p => w.getD p.1.val false && w.getD p.2.val false) := by
          congr 1
          funext p
          rw [old, old]
        rw [he]
        simp [List.any_cons, Bool.or_assoc, e]

lemma graph_has_edge_circuit (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ C : Circuit,
      (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
      ∀ g ∈ C.gates, g.op = GateOp.and →
        ∃ u v : Fin n, G.Adj u v ∧ g.inputs = [u.val, v.val] := by
  classical
  let es : List (Fin n × Fin n) := (Finset.univ.filter (fun p => G.Adj p.1 p.2)).toList
  obtain ⟨gs, o, hgs, hpair, _, hev⟩ := edge_list_circuit_edges es (n + 1) n (by omega) (by omega)
  refine ⟨⟨⟨GateOp.or, []⟩ :: gs, o⟩, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp
    · exact hgs g hg
  · intro x
    change (run gs (List.ofFn x ++ [false])).getD o false = _
    rw [hev _ (by simp)]
    have old (i : Fin n) : (List.ofFn x ++ [false]).getD i.val false = x i := by
      rw [List.getD_append _ _ _ _ (by simpa using i.isLt)]
      simp
    have acc : (List.ofFn x ++ [false]).getD n false = false := by simp
    rw [acc, Bool.false_or]
    have he : es.any (fun p => (List.ofFn x ++ [false]).getD p.1.val false &&
        (List.ofFn x ++ [false]).getD p.2.val false) =
        es.any (fun p => x p.1 && x p.2) := by
      congr 1
      funext p
      rw [old, old]
    rw [he]
    apply Bool.eq_iff_iff.mpr
    simp [es, List.any_eq_true, Prod.exists, Bool.and_eq_true, and_assoc]
  · intro g hg hop
    rcases List.mem_cons.mp hg with rfl | hg
    · cases hop
    · obtain ⟨p, hp, hin⟩ := hpair g hg hop
      exact ⟨p.1, p.2, by simpa [es] using hp, hin⟩

lemma run_prefix (gs : List Gate) (w : List Bool) :
    ∃ s : List Bool, run gs w = w ++ s ∧ s.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    obtain ⟨s, hs, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: s, ?_, by simp [hl]⟩
    change run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [hs]
    simp

lemma run_length (gs : List Gate) (w : List Bool) : (run gs w).length = w.length + gs.length := by
  obtain ⟨s, hs, hl⟩ := run_prefix gs w
  rw [hs]
  simp [hl]

lemma run_read (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨s, hs, _⟩ := run_prefix gs w
  rw [hs]
  exact List.getD_append _ _ _ _ hi

lemma direct_gate_value (n : ℕ) (C : Circuit) (t : ℕ) (g : Gate)
    (ht : C.gates[t]? = some g) (hop : g.op = GateOp.and)
    (u v : Fin n) (hin : g.inputs = [u.val, v.val]) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).getD (n + t) false = (x u && x v) := by
  obtain ⟨hlt, hget⟩ := List.getElem?_eq_some_iff.mp ht
  have split : C.gates = C.gates.take t ++ g :: C.gates.drop (t + 1) := by
    rw [← hget]
    exact (List.take_append_drop t C.gates).symm.trans (by rw [List.drop_eq_getElem_cons hlt])
  let w := run (C.gates.take t) (List.ofFn x)
  have hw : w.length = n + t := by
    simp [w, run_length, List.length_take, Nat.min_eq_left (Nat.le_of_lt hlt)]
  have old (i : Fin n) : w.getD i.val false = x i := by
    rw [run_read _ _ _ (by simpa using i.isLt)]
    simp
  change (run C.gates (List.ofFn x)).getD (n + t) false = _
  rw [split, run_append]
  change (run (C.gates.drop (t + 1))
    (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD (n + t) false = _
  rw [run_read _ _ _ (by simp [hw])]
  have old' (i : Fin n) : w[i.val]?.getD false = x i := by
    simpa only [List.getD_eq_getElem?_getD] using old i
  simp [← hw, hop, hin, GateOp.eval, old']

lemma no_ancestor_of_direct (n : ℕ) (C : Circuit) (t : ℕ) (g : Gate)
    (ht : C.gates[t]? = some g) (hinput : ∀ i ∈ g.inputs, i < n) (s : ℕ) :
    ¬ Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ k h,
      b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + s) (n + t) := by
  let step (a b : ℕ) : Prop := a < b ∧ ∃ k h,
    b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs
  have increasing {a b : ℕ} (hpath : Relation.TransGen step a b) : a < b := by
    induction hpath with
    | single h => exact h.1
    | tail _ h ih => exact ih.trans h.1
  intro path
  have last : ∃ a, n + s ≤ a ∧ step a (n + t) := by
    cases path with
    | single h => exact ⟨n + s, le_rfl, h⟩
    | tail hp hs => exact ⟨_, Nat.le_of_lt (increasing hp), hs⟩
  obtain ⟨a, ha, _, k, h, hk, hh, hin⟩ := last
  have hkt : k = t := by omega
  subst k
  have hge : h = g := Option.some.inj (hh.symm.trans ht)
  subst h
  have := hinput a hin
  omega


def OwnsPair (n : ℕ) (C : Circuit) (t : ℕ) (u v : Fin n) : Prop :=
  (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧
    ∀ (s : ℕ) (h : Gate), C.gates[s]? = some h → h.op = GateOp.and →
      Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ k h,
        b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + s) (n + t) →
      (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + s) false = false

lemma direct_owns (n : ℕ) (C : Circuit) (t : ℕ) (g : Gate)
    (ht : C.gates[t]? = some g) (hop : g.op = GateOp.and)
    (u v : Fin n) (hin : g.inputs = [u.val, v.val]) : OwnsPair n C t u v := by
  refine ⟨?_, ?_⟩
  · rw [direct_gate_value n C t g ht hop u v hin]
    simp
  · intro s h _ _ path
    apply False.elim
    apply no_ancestor_of_direct n C t g ht (fun i hi => ?_) s path
    simp only [hin, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact u.isLt
    · exact v.isLt

lemma direct_stars (n : ℕ) (G : SimpleGraph (Fin n)) (C : Circuit)
    (hshape : ∀ g ∈ C.gates, g.op = GateOp.and →
      ∃ u v : Fin n, G.Adj u v ∧ g.inputs = [u.val, v.val]) :
    ∀ t g, C.gates[t]? = some g → g.op = GateOp.and →
      ∃ c : Fin n, (∃ u v : Fin n, G.Adj u v ∧ OwnsPair n C t u v) ∧
        ∀ u v : Fin n, G.Adj u v → OwnsPair n C t u v → u = c ∨ v = c := by
  intro t g ht hop
  have hmem : g ∈ C.gates := List.mem_iff_getElem?.mpr ⟨t, ht⟩
  obtain ⟨u, v, huv, hin⟩ := hshape g hmem hop
  refine ⟨u, ⟨u, v, huv, direct_owns n C t g ht hop u v hin⟩, ?_⟩
  intro a b _ hown
  have hv := hown.1
  rw [direct_gate_value n C t g ht hop u v hin] at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  rcases hv.1 with h | h
  · exact Or.inl h.symm
  · exact Or.inr h.symm

lemma graph_has_stars (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ C : Circuit,
      (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
      ∀ t g, C.gates[t]? = some g → g.op = GateOp.and →
        ∃ c : Fin n, (∃ u v : Fin n, G.Adj u v ∧ OwnsPair n C t u v) ∧
          ∀ u v : Fin n, G.Adj u v → OwnsPair n C t u v → u = c ∨ v = c := by
  obtain ⟨C, hC, hf, hshape⟩ := graph_has_edge_circuit n G
  exact ⟨C, hC, hf, direct_stars n G C hshape⟩

lemma graph_has_circuit (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ C : Circuit,
      (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) := by
  obtain ⟨C, hC, hf, _⟩ := graph_has_edge_circuit n G
  exact ⟨C, hC, hf⟩

lemma graph_has_minimum (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] :
    ∃ C : Circuit,
      (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
      ∀ D : Circuit,
        (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
          decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
        C.size ≤ D.size := by
  classical
  let Good (C : Circuit) : Prop :=
    (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)
  have hex : ∃ s : ℕ, ∃ C : Circuit, Good C ∧ C.size = s := by
    obtain ⟨C, hC⟩ := graph_has_circuit n G
    exact ⟨C.size, C, hC, rfl⟩
  obtain ⟨C, hC, hs⟩ := Nat.find_spec hex
  refine ⟨C, hC.1, hC.2, ?_⟩
  intro D hD hf
  rw [hs]
  exact Nat.find_min' hex ⟨D, ⟨hD, hf⟩, rfl⟩

end PEqualNP.Outside.L_meta_1031

namespace PEqualNP.Outside.L_meta_1031

open PEqualNP.CircuitLowerBounds

lemma empty_graph (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hEmpty : ∀ u v : Fin n, ¬ G.Adj u v) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧ (∀ D : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size ≤ D.size) ∧ ∀ (t : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[t]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ c : Fin n, (∃ u v : Fin n, G.Adj u v ∧ ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false)) ∧ ∀ u v : Fin n, G.Adj u v → ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false) → u = c ∨ v = c := by
  refine ⟨⟨[], n⟩, ?_, ?_, ?_, ?_⟩
  · simp
  · intro x
    simp [Circuit.eval, Circuit.wires, List.getD_eq_getElem?_getD, hEmpty]
  · intro D _ _
    exact Nat.zero_le _
  · intro t g hg
    simp at hg

end PEqualNP.Outside.L_meta_1031

namespace PEqualNP.Outside.L_meta_1031_aux
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

lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

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

lemma getD_ofFn {n : ℕ} (f : Fin n → Bool) (i : Fin n) :
    (List.ofFn f).getD (i : ℕ) false = f i := by
  simp

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    PEqualNP.MetaComplexity.NestedCover.gateAt C k = C.gates[k] := by
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ hk]

def cf (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) : List (List ℕ) :=
  gs.foldl (PEqualNP.EdgeOwnership.coneStep n) cs

lemma cf_append (n : ℕ) (a b : List Gate) (cs : List (List ℕ)) :
    cf n (a ++ b) cs = cf n b (cf n a cs) := by
  simp [cf, List.foldl_append]

lemma cf_cons (n : ℕ) (g : Gate) (gs : List Gate) (cs : List (List ℕ)) :
    cf n (g :: gs) cs = cf n gs (PEqualNP.EdgeOwnership.coneStep n cs g) := rfl

lemma cs_len (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (PEqualNP.EdgeOwnership.coneStep n cs g).length = cs.length + 1 := by
  unfold PEqualNP.EdgeOwnership.coneStep; simp

lemma cf_len (n : ℕ) : ∀ (gs : List Gate) (cs : List (List ℕ)),
    (cf n gs cs).length = cs.length + gs.length := by
  intro gs
  induction gs with
  | nil => intro cs; rfl
  | cons g gs ih =>
    intro cs
    rw [cf_cons, ih, cs_len, List.length_cons]; omega

lemma cf_keep (n : ℕ) : ∀ (gs : List Gate) (cs : List (List ℕ)) (j : ℕ), j < cs.length →
    (cf n gs cs).getD j [] = cs.getD j [] := by
  intro gs
  induction gs with
  | nil => intro cs j _; rfl
  | cons g gs ih =>
    intro cs j hj
    rw [cf_cons, ih _ j (by rw [cs_len]; omega)]
    unfold PEqualNP.EdgeOwnership.coneStep
    exact List.getD_append _ _ _ _ hj

lemma snocD (L : List (List ℕ)) (v : List ℕ) (j : ℕ) (h : L.length = j) :
    (L ++ [v]).getD j [] = v := by
  subst h; simp [List.getD_eq_getElem?_getD]

lemma cone_iff (n : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) (i : ℕ) :
    i ∈ (cf n gs []).getD j [] ↔ ∃ w ∈ gs[j].inputs, n ≤ w ∧ w < n + j ∧
      (i = w - n ∨ i ∈ (cf n gs []).getD (w - n) []) := by
  have hP : (cf n (gs.take j) []).length = j := by
    rw [cf_len, List.length_take, Nat.min_eq_left (le_of_lt hj)]; simp
  have hsplit : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by
    rw [← List.drop_eq_getElem_cons hj, List.take_append_drop]
  have e : cf n gs [] = cf n (gs.drop (j + 1))
      (PEqualNP.EdgeOwnership.coneStep n (cf n (gs.take j) []) gs[j]) := by
    conv_lhs => rw [hsplit]
    rw [cf_append, cf_cons]
  have hfull : ∀ m, m < j → (cf n gs []).getD m [] = (cf n (gs.take j) []).getD m [] := by
    intro m hm
    rw [e, cf_keep _ _ _ m (by rw [cs_len, hP]; omega)]
    unfold PEqualNP.EdgeOwnership.coneStep
    exact List.getD_append _ _ _ _ (by omega)
  have hj_eq : (cf n gs []).getD j [] =
      (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (cf n (gs.take j) []).length))).flatMap
        (fun w => (w - n) :: (cf n (gs.take j) []).getD (w - n) []) := by
    rw [e, cf_keep _ _ _ j (by rw [cs_len, hP]; omega)]
    unfold PEqualNP.EdgeOwnership.coneStep
    exact snocD _ _ j hP
  rw [hj_eq, List.mem_flatMap]
  constructor
  · rintro ⟨w, hw, hi⟩
    obtain ⟨hw1, hw2⟩ := List.mem_filter.1 hw
    have hw3 := of_decide_eq_true hw2
    rw [hP] at hw3
    refine ⟨w, hw1, hw3.1, hw3.2, ?_⟩
    rcases List.mem_cons.1 hi with h1 | h1
    · exact Or.inl h1
    · right; rw [hfull _ (by omega)]; exact h1
  · rintro ⟨w, hw1, hw2, hw3, hi⟩
    refine ⟨w, List.mem_filter.2 ⟨hw1, decide_eq_true (by rw [hP]; exact ⟨hw2, hw3⟩)⟩, ?_⟩
    rcases hi with h1 | h1
    · exact List.mem_cons.2 (Or.inl h1)
    · rw [hfull _ (by omega)] at h1
      exact List.mem_cons.2 (Or.inr h1)

lemma cone_lt (n : ℕ) (gs : List Gate) (i j : ℕ) (h : i ∈ (cf n gs []).getD j []) :
    j < gs.length := by
  by_contra hc
  rw [List.getD_eq_default _ _ (by rw [cf_len]; simp; omega)] at h
  cases h

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover in
lemma valf (n : ℕ) (C : Circuit) (y : Fin n → Bool) (m : ℕ) (hm : m < C.gates.length) :
    gateVal n C m y = (C.gates[m]).op.eval
      (C.gates[m].inputs.map fun i => (wf (C.gates.take m) (List.ofFn y)).getD i false) := by
  have h := gate_val C.gates (List.ofFn y) m hm
  rw [List.length_ofFn] at h
  exact h

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover in
lemma wire_reach (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (e : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (rec : ∀ j, j < k → (gateAt C j).op = GateOp.or → gateVal n C j e = true →
      (∀ i, InCone n C i j → (gateAt C i).op = GateOp.and → gateVal n C i e = false) →
      ∃ u : Fin n, e u = true ∧ ∀ y : Fin n → Bool, y u = true → gateVal n C j y = true)
    (hown : ∀ i, InCone n C i k → (gateAt C i).op = GateOp.and → gateVal n C i e = false)
    (i : ℕ) (hi : i ∈ C.gates[k].inputs)
    (hv : (wf (C.gates.take k) (List.ofFn e)).getD i false = true) :
    ∃ u : Fin n, e u = true ∧ ∀ y : Fin n → Bool, y u = true →
      (wf (C.gates.take k) (List.ofFn y)).getD i false = true := by
  have hik : i < n + k := by
    by_contra hge
    rw [List.getD_eq_default _ _ (by
      rw [wf_len, List.length_ofFn, List.length_take, Nat.min_eq_left (le_of_lt hk)]; omega)] at hv
    exact absurd hv (by decide)
  by_cases hin : i < n
  · refine ⟨⟨i, hin⟩, ?_, ?_⟩
    · rw [wf_keep _ _ i (by rw [List.length_ofFn]; exact hin)] at hv
      rw [← getD_ofFn e ⟨i, hin⟩]
      exact hv
    · intro y hy
      rw [wf_keep _ _ i (by rw [List.length_ofFn]; exact hin)]
      rw [← getD_ofFn y ⟨i, hin⟩] at hy
      exact hy
  · have hj : i - n < k := by omega
    have hjl : i - n < C.gates.length := by omega
    have hw : ∀ y : Fin n → Bool, (wf (C.gates.take k) (List.ofFn y)).getD i false
        = gateVal n C (i - n) y := by
      intro y
      rw [← wire_take C.gates (List.ofFn y) k i (by rw [List.length_ofFn]; exact hik) (le_of_lt hk)]
      show _ = (wf C.gates (List.ofFn y)).getD (n + (i - n)) false
      congr 1
      omega
    have hcone : InCone n C (i - n) k :=
      (cone_iff n C.gates k hk (i - n)).2 ⟨i, hi, by omega, hik, Or.inl rfl⟩
    have hop : (gateAt C (i - n)).op = GateOp.or := by
      rw [gateAt_eq C _ hjl]
      rcases (hC _ (List.getElem_mem hjl)).1 with h | h
      · exfalso
        have := hown (i - n) hcone (by rw [gateAt_eq C _ hjl]; exact h)
        rw [← hw e, hv] at this
        exact absurd this (by decide)
      · exact h
    obtain ⟨u, hu1, hu2⟩ := rec (i - n) hj hop (by rw [← hw e]; exact hv)
      (fun i' hc ha => hown i' ((cone_iff n C.gates k hk i').2 ⟨i, hi, by omega, hik, Or.inr hc⟩) ha)
    exact ⟨u, hu1, fun y hy => by rw [hw y]; exact hu2 y hy⟩

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover in
lemma or_reach (n : ℕ) (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (e : Fin n → Bool) : ∀ m, m < C.gates.length → (gateAt C m).op = GateOp.or →
      gateVal n C m e = true →
      (∀ i, InCone n C i m → (gateAt C i).op = GateOp.and → gateVal n C i e = false) →
      ∃ u : Fin n, e u = true ∧ ∀ y : Fin n → Bool, y u = true → gateVal n C m y = true := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm hop hval hown
    rw [gateAt_eq C m hm] at hop
    have hv2 := hval
    rw [valf n C e m hm, hop] at hv2
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id] at hv2
    obtain ⟨i, hi, hiv⟩ := hv2
    obtain ⟨u, hu1, hu2⟩ := wire_reach n C hC e m hm
      (fun j hj h1 h2 h3 => ih j hj (lt_trans hj hm) h1 h2 h3) hown i hi hiv
    refine ⟨u, hu1, fun y hy => ?_⟩
    rw [valf n C y m hm, hop]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
    exact ⟨i, hi, hu2 y hy⟩

lemma cone_idx (n : ℕ) (gs : List Gate) : ∀ j i, i ∈ (cf n gs []).getD j [] → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i hc
    have hj := cone_lt n gs i j hc
    obtain ⟨w, _, hw1, hw2, hw3⟩ := (cone_iff n gs j hj i).1 hc
    rcases hw3 with e | e
    · omega
    · have := ih (w - n) (by omega) i e
      omega

open PEqualNP.EdgeOwnership PEqualNP.MetaComplexity.NestedCover

lemma pair_sound_global {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    (C : Circuit) (hC : PEqualNP.MetaComplexity.Monotone2 C)
    (hs : ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.and →
      ∀ u v : Fin n, gateVal n C j (pairInput u v) = true → G.Adj u v) :
    ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.and →
      ∀ x : Fin n → Bool, gateVal n C j x = true →
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  classical
  intro j hj hop x hv
  have hex : ∃ k, k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      gateVal n C k x = true := ⟨j, hj, hop, hv⟩
  let k := Nat.find hex
  obtain ⟨hk, hkop, hkv⟩ := Nat.find_spec hex
  change k < C.gates.length at hk
  change (gateAt C k).op = GateOp.and at hkop
  change gateVal n C k x = true at hkv
  have hown : ∀ i, InCone n C i k → (gateAt C i).op = GateOp.and →
      gateVal n C i x = false := by
    intro i hc ha
    have hik : i < k := cone_idx n C.gates k i hc
    cases h : gateVal n C i x with
    | false => rfl
    | true => exact False.elim ((Nat.find_min hex hik) ⟨by omega, ha, h⟩)
  have hvinputs : ∀ i ∈ C.gates[k].inputs,
      (wf (C.gates.take k) (List.ofFn x)).getD i false = true := by
    rw [gateAt_eq C k hk] at hkop
    rw [valf n C x k hk, hkop] at hkv
    simpa only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id] using hkv
  have reach : ∀ i ∈ C.gates[k].inputs, ∃ u : Fin n, x u = true ∧
      ∀ y : Fin n → Bool, y u = true →
        (wf (C.gates.take k) (List.ofFn y)).getD i false = true := by
    intro i hi
    exact wire_reach n C hC x k hk
      (fun t ht h1 h2 h3 => or_reach n C hC x t (ht.trans hk) h1 h2 h3)
      hown i hi (hvinputs i hi)
  have make_true (y : Fin n → Bool)
      (hy : ∀ i ∈ C.gates[k].inputs,
        (wf (C.gates.take k) (List.ofFn y)).getD i false = true) :
      gateVal n C k y = true := by
    rw [valf n C y k hk, ← gateAt_eq C k hk, hkop]
    simpa only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id,
      gateAt_eq C k hk] using hy
  have hlen : C.gates[k].inputs.length ≤ 2 := (hC _ (List.getElem_mem hk)).2
  rcases hi : C.gates[k].inputs with _ | ⟨a, as⟩
  · let u : Fin n := ⟨0, hn⟩
    have h := hs k hk hkop u u (make_true _ (by simp [hi]))
    exact False.elim (G.irrefl h)
  · cases as with
    | nil =>
      obtain ⟨u, hux, hu⟩ := reach a (by simp [hi])
      have h := hs k hk hkop u u (make_true _ (by
        intro i him
        have : i = a := by simpa [hi] using him
        subst i
        exact hu _ (by simp [pairInput])))
      exact False.elim (G.irrefl h)
    | cons b bs =>
      have hbs : bs = [] := by simpa [hi] using hlen
      subst bs
      obtain ⟨u, hux, hu⟩ := reach a (by simp [hi])
      obtain ⟨v, hvx, hv⟩ := reach b (by simp [hi])
      refine ⟨u, v, hs k hk hkop u v (make_true _ ?_), hux, hvx⟩
      intro i him
      have hia : i = a ∨ i = b := by simpa [hi] using him
      rcases hia with rfl | rfl
      · exact hu _ (by simp [pairInput])
      · exact hv _ (by simp [pairInput])



namespace Prune

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover


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

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]


open PEqualNP.EdgeOwnership in
lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.EdgeOwnership in
lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h


lemma legal_of (C : Circuit) (hmono : Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨h1, h2⟩ := hmono g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

open PEqualNP.EdgeOwnership in
lemma inCone_lt (n : ℕ) (C : Circuit) : ∀ k, k < C.gates.length → ∀ i, InCone n C i k → i < k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk i h
    obtain ⟨w, hw, hn, hlt, h | h⟩ := (inCone_iff n C i k hk).1 h
    · omega
    · have := ih (w - n) (by omega) (by omega) i h
      omega

open PEqualNP.EdgeOwnership in
lemma pi_symm {n : ℕ} (u v : Fin n) : pairInput u v = pairInput v u := by
  funext w
  simp [pairInput, or_comm]

open PEqualNP.EdgeOwnership in
lemma pi_val {n : ℕ} (u v : Fin n) (w : Fin n) : pairInput u v w = true ↔ (w = u ∨ w = v) := by
  simp [pairInput]

open PEqualNP.EdgeOwnership in
lemma pi_le {n : ℕ} (x u v : Fin n) (h : x = u ∨ x = v) :
    ∀ w, pairInput x x w = true → pairInput u v w = true := by
  intro w hw
  rw [pi_val] at hw ⊢
  rw [or_self] at hw
  rw [hw]
  exact h


open PEqualNP.EdgeOwnership

def F {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true

def Tb (n : ℕ) (gs : List Gate) (w : ℕ) : Prop :=
  ∃ z : Fin n, val gs w (pairInput z z) = true

def Snd {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), gs[j].op = GateOp.and →
    ∀ x : Fin n → Bool, val gs (n + j) x = true → F G x

def Cmp {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (o : ℕ) : Prop :=
  ∀ x : Fin n → Bool, val gs o x = true ↔ F G x

def Absorb (n : ℕ) (gs : List Gate) (j : ℕ) : Prop :=
  ∃ hj : j < gs.length, gs[j].op = GateOp.or ∧ Tb n gs (n + j) ∧
    ∃ h ∈ gs[j].inputs, h < n + j ∧ ¬ Tb n gs h

def BadAnd (n : ℕ) (gs : List Gate) (j : ℕ) : Prop :=
  ∃ hj : j < gs.length, gs[j].op = GateOp.and ∧
    ∃ i ∈ gs[j].inputs, ¬ (i < n + j ∧ Tb n gs i)

def Defect (n : ℕ) (gs : List Gate) (j : ℕ) : Prop :=
  Absorb n gs j ∨ BadAnd n gs j

lemma F_single {n : ℕ} (G : SimpleGraph (Fin n)) (z : Fin n) : ¬ F G (pairInput z z) := by
  rintro ⟨u, v, huv, hu, hv⟩
  rw [pi_val, or_self] at hu hv
  rw [hu, hv] at huv
  exact huv.ne rfl

lemma soundw {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hs : Snd G gs) :
    ∀ w, ¬ Tb n gs w → ∀ x : Fin n → Bool, val gs w x = true → F G x := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hT x h
    by_cases hwn : w < n
    · exfalso
      apply hT
      refine ⟨⟨w, hwn⟩, ?_⟩
      rw [val_input gs _ w hwn, pi_val]
      exact Or.inl rfl
    · by_cases hbig : n + gs.length ≤ w
      · rw [val_big gs x w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < gs.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at h hT
        rcases (legal gs[w - n] (List.getElem_mem hi)).1 with ha | ho
        · exact hs (w - n) hi ha x h
        · obtain ⟨p, hp, hplt, hv⟩ := (val_or gs x (w - n) hi ho).1 h
          apply ih p (by omega) _ x hv
          rintro ⟨z, hz⟩
          exact hT ⟨z, (val_or gs _ (w - n) hi ho).2 ⟨p, hp, hplt, hz⟩⟩

lemma trans_gen {n : ℕ} (gs gs' : List Gate) (hlen : gs'.length = gs.length)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (L : ℕ) (hsame : ∀ k, k ≠ L → gs'[k]? = gs[k]?) (x : Fin n → Bool)
    (hL : (∀ i, i < n + L → val gs i x = true → val gs' i x = true) →
      val gs (n + L) x = true → val gs' (n + L) x = true) :
    ∀ w, val gs w x = true → val gs' w x = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [val_input gs' _ w hwn]
      rw [val_input gs _ w hwn] at h
      exact h
    · by_cases hbig : n + gs.length ≤ w
      · rw [val_big gs x w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < gs.length := by omega
        have hi' : w - n < gs'.length := by omega
        have he : n + (w - n) = w := by omega
        by_cases hk : w - n = L
        · have key := hL (fun i hi2 hv => ih i (by omega) hv)
          have he2 : n + L = w := by omega
          rw [he2] at key
          exact key h
        · have hg : gs'[w - n] = gs[w - n] := by
            have h1 := hsame (w - n) hk
            rw [List.getElem?_eq_getElem hi', List.getElem?_eq_getElem hi] at h1
            exact Option.some.inj h1
          rw [← he] at h ⊢
          rcases (legal gs[w - n] (List.getElem_mem hi)).1 with ha | ho
          · apply (val_and gs' x (w - n) hi' (by rw [hg]; exact ha)).2
            intro j hj
            rw [hg] at hj
            obtain ⟨hjlt, hjv⟩ := (val_and gs x (w - n) hi ha).1 h j hj
            exact ⟨hjlt, ih j (by omega) hjv⟩
          · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gs x (w - n) hi ho).1 h
            exact (val_or gs' x (w - n) hi' (by rw [hg]; exact ho)).2
              ⟨j, by rw [hg]; exact hj, hjlt, ih j (by omega) hv⟩

lemma step_iff {n : ℕ} (A B : List Gate) (ka kb : ℕ) (hka : ka < A.length)
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

lemma two_mem (l : List ℕ) (hl : l.length ≤ 2) (p h : ℕ) (hp : p ∈ l) (hh : h ∈ l)
    (hne : p ≠ h) : ∀ i ∈ l, i = p ∨ i = h := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp at hp
  · simp only [List.mem_singleton] at hp hh
    exact absurd (hp.trans hh.symm) hne
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hp hh hi
    omega
  · simp only [List.length_cons] at hl
    omega

def rd (n m p i : ℕ) : ℕ := if i = n + m then p else if n + m < i then i - 1 else i

def er (n : ℕ) (gs : List Gate) (m p : ℕ) : List Gate :=
  (List.range (gs.length - 1)).map fun j =>
    if j < m then gs.getD j ⟨GateOp.or, []⟩
    else ⟨(gs.getD (j + 1) ⟨GateOp.or, []⟩).op,
      (gs.getD (j + 1) ⟨GateOp.or, []⟩).inputs.map (rd n m p)⟩

lemma er_len (n : ℕ) (gs : List Gate) (m p : ℕ) : (er n gs m p).length = gs.length - 1 := by
  simp [er]

lemma er_lt (n : ℕ) (gs : List Gate) (m p j : ℕ) (hjm : j < m) (hj : j < gs.length)
    (hj' : j < (er n gs m p).length) : (er n gs m p)[j] = gs[j] := by
  simp [er, hjm, List.getD_eq_getElem?_getD, hj]

lemma er_ge (n : ℕ) (gs : List Gate) (m p j : ℕ) (hjm : m ≤ j) (hj : j + 1 < gs.length)
    (hj' : j < (er n gs m p).length) :
    (er n gs m p)[j] = ⟨gs[j + 1].op, gs[j + 1].inputs.map (rd n m p)⟩ := by
  simp [er, Nat.not_lt.2 hjm, List.getD_eq_getElem?_getD, hj]

lemma rd_small (n m p a : ℕ) (h : a < n + m) : rd n m p a = a := by
  unfold rd
  split_ifs <;> omega

lemma rd_at (n m p : ℕ) : rd n m p (n + m) = p := by
  simp [rd]

lemma rd_succ (n m p k : ℕ) (h : m ≤ k) : rd n m p (n + (k + 1)) = n + k := by
  unfold rd
  split_ifs <;> omega

lemma rd_lt (n m p a k : ℕ) (hp : p < n + m) (h : m ≤ k) :
    rd n m p a < n + k ↔ a < n + (k + 1) := by
  unfold rd
  split_ifs <;> omega

lemma er_pre {n : ℕ} (gs : List Gate)
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

lemma erase_iff {n : ℕ} (gs : List Gate)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (m p h : ℕ) (hm : m < gs.length) (hp : p < n + m)
    (hor : gs[m].op = GateOp.or) (hpin : p ∈ gs[m].inputs)
    (two : ∀ i ∈ gs[m].inputs, i = p ∨ i = h)
    (x : Fin n → Bool) (hS : ¬ (val gs h x = true)) :
    ∀ i, i < n + gs.length →
      (val (er n gs m p) (rd n m p i) x = true ↔ val gs i x = true) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    by_cases him : i < n + m
    · rw [rd_small n m p i him]
      exact er_pre gs legal m p hm x i him
    · by_cases hieq : i = n + m
      · subst hieq
        rw [rd_at]
        have e1 := ih p hp (by omega)
        rw [rd_small n m p p hp] at e1
        rw [e1, val_or gs x m hm hor]
        constructor
        · intro hv
          exact ⟨p, hpin, hp, hv⟩
        · rintro ⟨j, hj, hjlt, hv⟩
          rcases two j hj with e | e
          · rw [e] at hv
            exact hv
          · rw [e] at hv
            exact absurd hv hS
      · obtain ⟨k, rfl⟩ : ∃ k, i = n + (k + 1) := ⟨i - n - 1, by omega⟩
        have hmk : m ≤ k := by omega
        have hk : k + 1 < gs.length := by omega
        have hkE : k < (er n gs m p).length := by rw [er_len]; omega
        have hg := er_ge n gs m p k hmk hk hkE
        rw [rd_succ n m p k hmk]
        apply step_iff (er n gs m p) gs k (k + 1) hkE hk (by rw [hg])
          (legal gs[k + 1] (List.getElem_mem hk)).1 (rd n m p) (by rw [hg]) x
        intro j _
        constructor
        · rintro ⟨h1, h2⟩
          have hj := (rd_lt n m p j k hp hmk).1 h1
          exact ⟨hj, (ih j hj (by omega)).1 h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨(rd_lt n m p j k hp hmk).2 h1, (ih j h1 (by omega)).2 h2⟩

lemma conv_step {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (o : ℕ)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hs : Snd G gs) (hc : Cmp G gs o) (L : ℕ) (hb : BadAnd n gs L)
    (hno : ∀ j, L < j → ¬ Defect n gs j) :
    ∃ (gs1 : List Gate) (o1 : ℕ), gs1.length = gs.length ∧
      (∀ g ∈ gs1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      Snd G gs1 ∧ Cmp G gs1 o1 ∧ ∀ j, L ≤ j → ¬ Defect n gs1 j := by
  obtain ⟨hL, hand, i0, hi0, hbad⟩ := hb
  obtain ⟨gs1, hlen, ⟨hL1, g1L⟩, same, legal1⟩ : ∃ gs1 : List Gate, gs1.length = gs.length ∧
      (∃ h : L < gs1.length, gs1[L] = ⟨GateOp.or, [i0]⟩) ∧
      (∀ k, k ≠ L → gs1[k]? = gs[k]?) ∧
      (∀ g ∈ gs1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) := by
    refine ⟨gs.set L ⟨GateOp.or, [i0]⟩, by simp, ⟨by simpa using hL, by simp⟩, ?_, ?_⟩
    · intro k hk
      exact List.getElem?_set_ne (Ne.symm hk)
    · intro g hg
      rcases List.mem_or_eq_of_mem_set hg with h | h
      · exact legal g h
      · rw [h]
        exact ⟨Or.inr rfl, by simp⟩
  have sameE : ∀ k (hk : k < gs.length) (hk1 : k < gs1.length), k ≠ L → gs1[k] = gs[k] := by
    intro k hk hk1 hne
    have h1 := same k hne
    rw [List.getElem?_eq_getElem hk1, List.getElem?_eq_getElem hk] at h1
    exact Option.some.inj h1
  have hor1 : gs1[L].op = GateOp.or := by rw [g1L]
  have up : ∀ (x : Fin n → Bool) w, val gs w x = true → val gs1 w x = true := by
    intro x
    apply trans_gen gs gs1 hlen legal L same x
    intro tr h
    obtain ⟨h1, h2⟩ := (val_and gs x L hL hand).1 h i0 hi0
    exact (val_or gs1 x L hL1 hor1).2 ⟨i0, by rw [g1L]; simp, h1, tr i0 h1 h2⟩
  have down : ∀ (x : Fin n → Bool), ¬ F G x → ∀ w, val gs1 w x = true → val gs w x = true := by
    intro x hF
    apply trans_gen gs1 gs hlen.symm legal1 L (fun k hk => (same k hk).symm) x
    intro tr h
    exfalso
    obtain ⟨i, hi, hlt, hv⟩ := (val_or gs1 x L hL1 hor1).1 h
    rw [g1L] at hi
    simp only [List.mem_singleton] at hi
    rw [hi] at hlt hv
    exact hF (soundw G gs legal hs i0 (fun hT => hbad ⟨hlt, hT⟩) x (tr i0 hlt hv))
  have Tbeq : ∀ w, Tb n gs1 w ↔ Tb n gs w := by
    intro w
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, down _ (F_single G z) w hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, up _ w hz⟩
  refine ⟨gs1, o, hlen, legal1, ?_, ?_, ?_⟩
  · intro j hj ha x hv
    by_cases hF : F G x
    · exact hF
    · have hjL : j ≠ L := by
        intro e
        subst e
        rw [hor1] at ha
        exact GateOp.noConfusion ha
      have hj0 : j < gs.length := by omega
      rw [sameE j hj0 hj hjL] at ha
      exact hs j hj0 ha x (down x hF (n + j) hv)
  · intro x
    constructor
    · intro h
      by_contra hF
      exact hF ((hc x).1 (down x hF o h))
    · intro hF
      exact up x o ((hc x).2 hF)
  · intro j hj hd
    by_cases hjL : j = L
    · subst hjL
      rcases hd with ⟨_, _, hT, _⟩ | ⟨_, ha, _⟩
      · obtain ⟨z, hz⟩ := (Tbeq _).1 hT
        exact F_single G z (hs j hL hand _ hz)
      · rw [hor1] at ha
        exact GateOp.noConfusion ha
    · apply hno j (by omega)
      rcases hd with ⟨hj1, hor, hT, h, hh, hlt, hnT⟩ | ⟨hj1, ha, i, hi, hbd⟩
      · have hj0 : j < gs.length := by omega
        rw [sameE j hj0 hj1 hjL] at hor hh
        exact Or.inl ⟨hj0, hor, (Tbeq _).1 hT, h, hh, hlt, fun t => hnT ((Tbeq h).2 t)⟩
      · have hj0 : j < gs.length := by omega
        rw [sameE j hj0 hj1 hjL] at ha hi
        exact Or.inr ⟨hj0, ha, i, hi, fun t => hbd ⟨t.1, (Tbeq i).2 t.2⟩⟩

lemma lift_step {n : ℕ} (G : SimpleGraph (Fin n)) (gs : List Gate) (o : ℕ)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hs : Snd G gs) (hc : Cmp G gs o) (m : ℕ) (hab : Absorb n gs m)
    (hno : ∀ j, m < j → ¬ Defect n gs j) :
    ∃ (gs1 : List Gate) (o1 : ℕ), gs1.length = gs.length ∧
      (∀ g ∈ gs1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      Snd G gs1 ∧ Cmp G gs1 o1 ∧ ∀ j, m ≤ j → ¬ Defect n gs1 j := by
  obtain ⟨hm, hor, ⟨z0, hz0⟩, h, hh, hlt, hnT⟩ := hab
  obtain ⟨p, hpin, hp, hpv⟩ := (val_or gs _ m hm hor).1 hz0
  have hne : p ≠ h := by
    intro e
    rw [e] at hpv
    exact hnT ⟨z0, hpv⟩
  have two := two_mem gs[m].inputs (legal gs[m] (List.getElem_mem hm)).2 p h hpin hh hne
  have hElen := er_len n gs m p
  have hsh : ∀ x : Fin n → Bool, val gs h x = true → F G x := soundw G gs legal hs h hnT
  have hS0 : ∀ z : Fin n, ¬ (val gs h (pairInput z z) = true) := fun z hz => hnT ⟨z, hz⟩
  have pre1 : ∀ w, w < n + (er n gs m p).length → ∀ x : Fin n → Bool,
      val (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])]) w x = val (er n gs m p) w x := by
    intro w hw x
    exact wf_prefix (er n gs m p) [(Gate.mk GateOp.or [rd n m p o, h])] (List.ofFn x) w
      (by rw [List.length_ofFn]; exact hw)
  have rdl : ∀ i, i < n + gs.length → rd n m p i < n + (er n gs m p).length := by
    intro i hi
    rw [hElen]
    unfold rd
    split_ifs <;> omega
  have rdl' : ∀ i, rd n m p i < n + (er n gs m p).length → i < n + gs.length := by
    intro i hi
    rw [hElen] at hi
    unfold rd at hi
    split_ifs at hi <;> omega
  have eqv : ∀ x : Fin n → Bool, ¬ (val gs h x = true) → ∀ i, i < n + gs.length →
      (val (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])]) (rd n m p i) x = true ↔
        val gs i x = true) := by
    intro x hS i hi
    rw [pre1 _ (rdl i hi)]
    exact erase_iff gs legal m p h hm hp hor hpin two x hS i hi
  have hval : ∀ x : Fin n → Bool,
      val (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])]) h x = val gs h x := by
    intro x
    rw [pre1 h (by rw [hElen]; omega)]
    have := er_pre gs legal m p hm x h hlt
    exact Bool.eq_iff_iff.2 this
  have Tbeq : ∀ i, i < n + gs.length →
      (Tb n (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])]) (rd n m p i) ↔ Tb n gs i) := by
    intro i hi
    constructor
    · rintro ⟨z, hz⟩
      exact ⟨z, (eqv _ (hS0 z) i hi).1 hz⟩
    · rintro ⟨z, hz⟩
      exact ⟨z, (eqv _ (hS0 z) i hi).2 hz⟩
  have hlen1 : (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])]).length = gs.length := by
    rw [List.length_append, hElen]
    simp
    omega
  have hJlt : (er n gs m p).length <
      (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])]).length := by
    rw [List.length_append]
    simp
  have hJ : (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])])[(er n gs m p).length]'hJlt =
      (Gate.mk GateOp.or [rd n m p o, h]) := by
    simp
  have hJv : ∀ x : Fin n → Bool,
      val (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])]) (n + (er n gs m p).length) x = true ↔
        ((rd n m p o < n + (er n gs m p).length ∧
          val (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])]) (rd n m p o) x = true) ∨
          val gs h x = true) := by
    intro x
    rw [val_or _ x (er n gs m p).length hJlt (by rw [hJ]), hJ]
    constructor
    · rintro ⟨i, hi, h1, h2⟩
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with e | e
      · rw [e] at h1 h2
        exact Or.inl ⟨h1, h2⟩
      · rw [e, hval x] at h2
        exact Or.inr h2
    · rintro (⟨h1, h2⟩ | h2)
      · exact ⟨rd n m p o, by simp, h1, h2⟩
      · exact ⟨h, by simp, by rw [hElen]; omega, by rw [hval x]; exact h2⟩
  have hEget : ∀ j (hjE : j < (er n gs m p).length)
      (hj1 : j < (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])]).length),
      (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])])[j] = (er n gs m p)[j] := by
    intro j hjE hj1
    exact List.getElem_append_left hjE
  refine ⟨er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])], n + (er n gs m p).length, hlen1,
    ?_, ?_, ?_, ?_⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hg
      by_cases hjm : j < m
      · rw [er_lt n gs m p j hjm (by omega) hj]
        exact legal _ (List.getElem_mem _)
      · have hj2 : j + 1 < gs.length := by rw [hElen] at hj; omega
        rw [er_ge n gs m p j (by omega) hj2 hj]
        have := legal gs[j + 1] (List.getElem_mem hj2)
        exact ⟨this.1, by simpa using this.2⟩
    · simp only [List.mem_singleton] at hg
      rw [hg]
      exact ⟨Or.inr rfl, by simp⟩
  · intro j hj ha x hv
    by_cases hS : val gs h x = true
    · exact hsh x hS
    · by_cases hjE : j < (er n gs m p).length
      · rw [hEget j hjE hj] at ha
        by_cases hjm : j < m
        · have hj0 : j < gs.length := by omega
          rw [er_lt n gs m p j hjm hj0 hjE] at ha
          have e := eqv x hS (n + j) (by omega)
          rw [rd_small n m p (n + j) (by omega)] at e
          exact hs j hj0 ha x (e.1 hv)
        · have hj2 : j + 1 < gs.length := by rw [hElen] at hjE; omega
          rw [er_ge n gs m p j (by omega) hj2 hjE] at ha
          have e := eqv x hS (n + (j + 1)) (by omega)
          rw [rd_succ n m p j (by omega)] at e
          exact hs (j + 1) hj2 ha x (e.1 hv)
      · have hje : j = (er n gs m p).length := by rw [hlen1] at hj; rw [hElen] at hjE ⊢; omega
        subst hje
        rw [hJ] at ha
        exact GateOp.noConfusion ha
  · intro x
    rw [hJv x]
    constructor
    · rintro (⟨h1, h2⟩ | h2)
      · by_cases hS : val gs h x = true
        · exact hsh x hS
        · exact (hc x).1 ((eqv x hS o (rdl' o h1)).1 h2)
      · exact hsh x h2
    · intro hF
      by_cases hS : val gs h x = true
      · exact Or.inr hS
      · have hvo := (hc x).2 hF
        have holt : o < n + gs.length := by
          by_contra hcon
          rw [val_big gs x o (by omega)] at hvo
          exact Bool.noConfusion hvo
        exact Or.inl ⟨rdl o holt, (eqv x hS o holt).2 hvo⟩
  · intro j hjm hd
    by_cases hjE : j < (er n gs m p).length
    · have hj2 : j + 1 < gs.length := by rw [hElen] at hjE; omega
      have hj1 : j < (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])]).length := by
        rw [hlen1]; omega
      have hg : (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])])[j] =
          ⟨gs[j + 1].op, gs[j + 1].inputs.map (rd n m p)⟩ := by
        rw [hEget j hjE hj1, er_ge n gs m p j hjm hj2 hjE]
      have hTj : ∀ a, a < n + gs.length →
          (Tb n (er n gs m p ++ [(Gate.mk GateOp.or [rd n m p o, h])]) (rd n m p a) ↔ Tb n gs a) :=
        Tbeq
      apply hno (j + 1) (by omega)
      rcases hd with ⟨_, hor1, hT, h', hh', hlt', hnT'⟩ | ⟨_, ha, i', hi', hbd⟩
      · rw [hg] at hor1 hh'
        obtain ⟨a, ha2, rfl⟩ := List.mem_map.1 hh'
        have halt := (rd_lt n m p a j hp hjm).1 hlt'
        have hT2 := hTj (n + (j + 1)) (by omega)
        rw [rd_succ n m p j hjm] at hT2
        exact Or.inl ⟨hj2, hor1, hT2.1 hT, a, ha2, halt,
          fun t => hnT' ((hTj a (by omega)).2 t)⟩
      · rw [hg] at ha hi'
        obtain ⟨a, ha2, rfl⟩ := List.mem_map.1 hi'
        exact Or.inr ⟨hj2, ha, a, ha2, fun t => hbd
          ⟨(rd_lt n m p a j hp hjm).2 t.1, (hTj a (by omega)).2 t.2⟩⟩
    · rcases hd with ⟨hj1, hor1, ⟨z, hz⟩, _⟩ | ⟨hj1, ha, _⟩
      · have hje : j = (er n gs m p).length := by
          rw [hlen1] at hj1; rw [hElen] at hjE ⊢; omega
        subst hje
        rcases (hJv _).1 hz with ⟨h1, h2⟩ | h2
        · exact F_single G z ((hc _).1 ((eqv _ (hS0 z) o (rdl' o h1)).1 h2))
        · exact hS0 z h2
      · have hje : j = (er n gs m p).length := by
          rw [hlen1] at hj1; rw [hElen] at hjE ⊢; omega
        subst hje
        rw [hJ] at ha
        exact GateOp.noConfusion ha

lemma fix_all {n : ℕ} (G : SimpleGraph (Fin n)) : ∀ (L : ℕ) (gs : List Gate) (o : ℕ),
    (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
    Snd G gs → Cmp G gs o → (∀ j, L ≤ j → ¬ Defect n gs j) →
    ∃ (gs1 : List Gate) (o1 : ℕ), gs1.length = gs.length ∧
      (∀ g ∈ gs1, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      Snd G gs1 ∧ Cmp G gs1 o1 ∧ ∀ j, ¬ Defect n gs1 j := by
  intro L
  induction L with
  | zero =>
    intro gs o hl hs hc hno
    exact ⟨gs, o, rfl, hl, hs, hc, fun j => hno j (Nat.zero_le j)⟩
  | succ L ih =>
    intro gs o hl hs hc hno
    by_cases hd : Defect n gs L
    · rcases hd with ha | hb
      · obtain ⟨gs1, o1, hlen, hl1, hs1, hc1, hno1⟩ :=
          lift_step G gs o hl hs hc L ha (fun j hj => hno j hj)
        obtain ⟨gs2, o2, hlen2, r⟩ := ih gs1 o1 hl1 hs1 hc1 hno1
        exact ⟨gs2, o2, hlen2.trans hlen, r⟩
      · obtain ⟨gs1, o1, hlen, hl1, hs1, hc1, hno1⟩ :=
          conv_step G gs o hl hs hc L hb (fun j hj => hno j hj)
        obtain ⟨gs2, o2, hlen2, r⟩ := ih gs1 o1 hl1 hs1 hc1 hno1
        exact ⟨gs2, o2, hlen2.trans hlen, r⟩
    · apply ih gs o hl hs hc
      intro j hj
      rcases Nat.eq_or_lt_of_le hj with e | hlt
      · rw [← e]
        exact hd
      · exact hno j hlt

lemma pure_cone {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (legal : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hs : Snd G C.gates) (hno : ∀ j, ¬ Defect n C.gates j) :
    ∀ k, k < C.gates.length → Tb n C.gates (n + k) →
      ∀ i, InCone n C i k → Tb n C.gates (n + i) := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hk hT i hc
    obtain ⟨w, hw, hn, hlt, h⟩ := (inCone_iff n C i k hk).1 hc
    rw [gateAt_eq C k hk] at hw
    have hwT : Tb n C.gates w := by
      by_contra hnT
      rcases (legal C.gates[k] (List.getElem_mem hk)).1 with ha | ho
      · obtain ⟨z, hz⟩ := hT
        exact F_single G z (hs k hk ha _ hz)
      · exact hno k (Or.inl ⟨hk, ho, hT, w, hw, hlt, hnT⟩)
    have he : n + (w - n) = w := by omega
    rcases h with h | h
    · rw [h, he]
      exact hwT
    · exact ih (w - n) (by omega) (by omega) (by rw [he]; exact hwT) i h

lemma own_edge {n : ℕ} (G : SimpleGraph (Fin n)) (C : Circuit)
    (legal : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hs : Snd G C.gates) (hno : ∀ j, ¬ Defect n C.gates j) (j : ℕ)
    (hj : j < C.gates.length) (ha : C.gates[j].op = GateOp.and) :
    ∃ u v : Fin n, G.Adj u v ∧ Owns n C j u v := by
  have hgood : ∀ i ∈ C.gates[j].inputs, i < n + j ∧ Tb n C.gates i := by
    intro i hi
    by_contra hcon
    exact hno j (Or.inr ⟨hj, ha, i, hi, hcon⟩)
  have hlen := (legal C.gates[j] (List.getElem_mem hj)).2
  rcases hin : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · exfalso
    have hv : val C.gates (n + j) (fun _ : Fin n => false) = true :=
      (val_and C.gates _ j hj ha).2 (by rw [hin]; intro i hi; simp at hi)
    obtain ⟨u, v, _, hu, _⟩ := hs j hj ha _ hv
    exact Bool.noConfusion hu
  · exfalso
    obtain ⟨hlt, z, hz⟩ := hgood a (by rw [hin]; simp)
    have hv : val C.gates (n + j) (pairInput z z) = true :=
      (val_and C.gates _ j hj ha).2 (by
        rw [hin]
        intro i hi
        simp only [List.mem_singleton] at hi
        rw [hi]
        exact ⟨hlt, hz⟩)
    exact F_single G z (hs j hj ha _ hv)
  · obtain ⟨hlta, za, hza⟩ := hgood a (by rw [hin]; simp)
    obtain ⟨hltb, zb, hzb⟩ := hgood b (by rw [hin]; simp)
    have hva : val C.gates a (pairInput za zb) = true :=
      val_mono C.gates legal _ _ (pi_le za za zb (Or.inl rfl)) a hza
    have hvb : val C.gates b (pairInput za zb) = true :=
      val_mono C.gates legal _ _ (pi_le zb za zb (Or.inr rfl)) b hzb
    have hv : val C.gates (n + j) (pairInput za zb) = true :=
      (val_and C.gates _ j hj ha).2 (by
        rw [hin]
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with e | e
        · rw [e]
          exact ⟨hlta, hva⟩
        · rw [e]
          exact ⟨hltb, hvb⟩)
    obtain ⟨u, v, huv, hu, hv2⟩ := hs j hj ha _ hv
    rw [pi_val] at hu hv2
    have hadj : G.Adj za zb := by
      rcases hu with e1 | e1 <;> rcases hv2 with e2 | e2
      · rw [e1, e2] at huv
        exact absurd rfl huv.ne
      · rw [e1, e2] at huv
        exact huv
      · rw [e1, e2] at huv
        exact huv.symm
      · rw [e1, e2] at huv
        exact absurd rfl huv.ne
    refine ⟨za, zb, hadj, hj, by rw [gateAt_eq C j hj]; exact ha, hv, ?_⟩
    intro i hij hc hai
    exfalso
    obtain ⟨w, hw, hn, hlt, h⟩ := (inCone_iff n C i j hj).1 hc
    rw [gateAt_eq C j hj] at hw
    obtain ⟨_, hwT⟩ := hgood w hw
    have he : n + (w - n) = w := by omega
    have hiT : Tb n C.gates (n + i) := by
      rcases h with h | h
      · rw [h, he]
        exact hwT
      · exact pure_cone G C legal hs hno (w - n) (by omega) (by rw [he]; exact hwT) i h
    obtain ⟨z, hz⟩ := hiT
    have hil : i < C.gates.length := by omega
    rw [gateAt_eq C i hil] at hai
    exact F_single G z (hs i hil hai _ hz)
  · exfalso
    rw [hin] at hlen
    simp only [List.length_cons] at hlen
    omega


lemma result : ∀ (x1 : ℕ) (x2 : SimpleGraph (Fin x1)) [x3 : DecidableRel x2.Adj] (x4 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x5 x6 x7 : Fin x1), x2.Adj x5 x6 → x2.Adj x6 x7 → ¬x2.Adj x7 x5) → (∀ (x6 x7 x8 x9 : Fin x1), x2.Adj x6 x7 → x2.Adj x7 x8 → x2.Adj x8 x9 → x2.Adj x9 x6 → x6 = x8 ∨ x7 = x9) → PEqualNP.MetaComplexity.Monotone2 x4 → (∀ (x8 : Fin x1 → Bool), x4.eval (List.ofFn x8) = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x1), x2.Adj x9 x10 ∧ x8 x9 = Bool.true ∧ x8 x10 = Bool.true)) → (∀ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x9 → (∀ (x11 : Fin x1 → Bool), x9.eval (List.ofFn x11) = Decidable.decide (∃ (x12 : Fin x1) (x13 : Fin x1), x2.Adj x12 x13 ∧ x11 x12 = Bool.true ∧ x11 x13 = Bool.true)) → x4.size ≤ x9.size) → (∀ (x10 : ℕ) (x11 : PEqualNP.CircuitLowerBounds.Gate), x4.gates[x10]? = Option.some x11 → x11.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ (x14 : Fin x1 → Bool), (x4.wires (List.ofFn x14)).getD (x1 + x10) Bool.false = Bool.true → ∃ (x16 : Fin x1) (x17 : Fin x1), x2.Adj x16 x17 ∧ x14 x16 = Bool.true ∧ x14 x17 = Bool.true) → ∃ (x11 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x11 ∧ x11.size ≤ x4.size ∧ (∀ (x12 : Fin x1 → Bool), x11.eval (List.ofFn x12) = Decidable.decide (∃ (x13 : Fin x1) (x14 : Fin x1), x2.Adj x13 x14 ∧ x12 x13 = Bool.true ∧ x12 x14 = Bool.true)) ∧ ∀ (x12 : ℕ) (x13 : PEqualNP.CircuitLowerBounds.Gate), x11.gates[x12]? = Option.some x13 → x13.op = PEqualNP.CircuitLowerBounds.GateOp.and → (∀ (x16 : Fin x1 → Bool), (x11.wires (List.ofFn x16)).getD (x1 + x12) Bool.false = Bool.true → ∃ (x18 : Fin x1) (x19 : Fin x1), x2.Adj x18 x19 ∧ x16 x18 = Bool.true ∧ x16 x19 = Bool.true) ∧ ∃ (x16 : Fin x1) (x17 : Fin x1), x2.Adj x16 x17 ∧ PEqualNP.EdgeOwnership.Owns x1 x11 x12 x16 x17 := by
  intro n G _ C _ _ hmono hcomp _ hsound
  have legal := PEqualNP.Outside.L_meta_1031_aux.Prune.legal_of C hmono
  have hs : PEqualNP.Outside.L_meta_1031_aux.Prune.Snd G C.gates := by
    intro j hj ha x hv
    exact hsound j C.gates[j] (List.getElem?_eq_getElem hj) ha x hv
  have hc : PEqualNP.Outside.L_meta_1031_aux.Prune.Cmp G C.gates C.output := by
    intro x
    constructor
    · intro h
      have h2 : C.eval (List.ofFn x) = true := h
      rw [hcomp x, decide_eq_true_iff] at h2
      exact h2
    · intro hF
      have h2 : C.eval (List.ofFn x) = true := by
        rw [hcomp x, decide_eq_true_iff]
        exact hF
      exact h2
  obtain ⟨gs1, o1, hlen, hl1, hs1, hc1, hno1⟩ :=
    PEqualNP.Outside.L_meta_1031_aux.Prune.fix_all G C.gates.length C.gates C.output legal hs hc (by
      intro j hj hd
      rcases hd with ⟨h, _⟩ | ⟨h, _⟩ <;> omega)
  refine ⟨⟨gs1, o1⟩, ?_, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨h1, h2⟩ := hl1 g hg
    refine ⟨?_, h2⟩
    rcases h1 with h | h
    · rw [h]
      exact Or.inl rfl
    · rw [h]
      exact Or.inr rfl
  · show gs1.length ≤ C.gates.length
    omega
  · intro x
    rw [Bool.eq_iff_iff, decide_eq_true_iff]
    exact hc1 x
  · intro j g hg ha
    have hj : j < gs1.length := by
      by_contra hcon
      have hnone : gs1[j]? = none := List.getElem?_eq_none (by omega)
      have hg' : gs1[j]? = some g := hg
      rw [hnone] at hg'
      cases hg'
    have hgj : gs1[j] = g := by
      have hg' : gs1[j]? = some g := hg
      rw [List.getElem?_eq_getElem hj] at hg'
      exact Option.some.inj hg'
    refine ⟨fun x hv => hs1 j hj (by rw [hgj]; exact ha) x hv, ?_⟩
    exact PEqualNP.Outside.L_meta_1031_aux.Prune.own_edge G ⟨gs1, o1⟩ hl1 hs1 hno1 j hj
      (by rw [hgj]; exact ha)

end Prune


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

lemma normalize_bridge :
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      ∃ C : Circuit, Monotone2 C ∧
        (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
          decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
        (∀ D : Circuit, Monotone2 D →
          (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
            decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
          C.size ≤ D.size) ∧
        ∀ (t : ℕ) (g : Gate), C.gates[t]? = some g → g.op = GateOp.and →
          ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + t) false = true →
            ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) →
    (∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit),
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) →
      Monotone2 C →
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      (∀ D : Circuit, Monotone2 D →
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
          decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
        C.size ≤ D.size) →
      (∀ (t : ℕ) (g : Gate), C.gates[t]? = some g → g.op = GateOp.and →
        ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + t) false = true →
          ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) →
      ∃ C' : Circuit, Monotone2 C' ∧ C'.size ≤ C.size ∧
        (∀ x : Fin n → Bool, C'.eval (List.ofFn x) =
          decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
        ∀ (t : ℕ) (g : Gate), C'.gates[t]? = some g → g.op = GateOp.and →
          (∀ x : Fin n → Bool, (C'.wires (List.ofFn x)).getD (n + t) false = true →
            ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) ∧
          ∃ u v : Fin n, G.Adj u v ∧ Owns n C' t u v) →
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧ (∀ D : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size ≤ D.size) ∧ ∀ (t : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[t]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ c : Fin n, (∃ u v : Fin n, G.Adj u v ∧ ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false)) ∧ ∀ u v : Fin n, G.Adj u v → ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false) → u = c ∨ v = c := by
  intro hSoundLeast hCleanOwn n G instDec htri hc4
  obtain ⟨C0, hM0, hE0, hMin0, hS0⟩ := hSoundLeast n G htri hc4
  obtain ⟨C, hM, hSz, hE, hSO⟩ := hCleanOwn n G C0 htri hc4 hM0 hE0 hMin0 hS0
  have hM_unfold : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
    fun g hg => hM g hg
  have hMin : ∀ D : Circuit,
      (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) →
      C.size ≤ D.size := fun D hDM hDE => hSz.trans (hMin0 D hDM hDE)
  let stepW : List Bool → Gate → List Bool :=
    fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
  have getD_app_lt : ∀ (w t : List Bool) (i : ℕ), i < w.length →
      (w ++ t).getD i false = w.getD i false := by
    intro w t i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
  have getD_app_self : ∀ (w : List Bool) (b : Bool),
      (w ++ [b]).getD w.length false = b := by
    intro w b
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (le_refl w.length)]
    simp
  have getD_ge : ∀ (w : List Bool) (i : ℕ), w.length ≤ i → w.getD i false = false := by
    intro w i hi
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi, Option.getD_none]
  have foldl_getD_lt : ∀ (gs : List Gate) (w : List Bool) (i : ℕ), i < w.length →
      (gs.foldl stepW w).getD i false = w.getD i false := by
    intro gs
    induction gs with
    | nil => intro w i _; rfl
    | cons g0 gs ih =>
      intro w i hi
      rw [List.foldl_cons]
      have hlt : i < (stepW w g0).length := by
        change i < (w ++ [_]).length
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [ih (stepW w g0) i hlt]
      exact getD_app_lt w _ i hi
  have foldl_gate : ∀ (gs : List Gate) (w : List Bool) (j : ℕ) (g : Gate),
      gs[j]? = some g →
      (gs.foldl stepW w).getD (w.length + j) false =
        g.op.eval (g.inputs.map fun i =>
          if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
    intro gs
    induction gs with
    | nil => intro _ _ _ h; simp at h
    | cons g0 gs ih =>
      intro w j g hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        rw [Nat.add_zero, List.foldl_cons]
        have hlt : w.length < (stepW w g0).length := by
          change w.length < (w ++ [_]).length
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [foldl_getD_lt gs (stepW w g0) w.length hlt]
        rw [getD_app_self w _]
        congr 1
        apply List.map_congr_left
        intro i _
        by_cases hi : i < w.length
        · have hilt : i < (stepW w g0).length := by
            change i < (w ++ [_]).length
            simp only [List.length_append, List.length_cons, List.length_nil]
            omega
          simp only [hi, ↓reduceIte, foldl_getD_lt gs (stepW w g0) i hilt]
          exact (getD_app_lt w _ i hi).symm
        · simp only [hi, ↓reduceIte]
          exact getD_ge w i (Nat.le_of_not_lt hi)
      | succ j' =>
        simp only [List.getElem?_cons_succ] at hj
        have hlen : (stepW w g0).length + j' = w.length + (j' + 1) := by
          change (w ++ [_]).length + j' = w.length + (j' + 1)
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [List.foldl_cons, ← hlen]
        exact ih (stepW w g0) j' g hj
  have wires_gate : ∀ (x : Fin n → Bool) (j : ℕ) (g : Gate),
      C.gates[j]? = some g →
      (C.wires (List.ofFn x)).getD (n + j) false =
        g.op.eval (g.inputs.map fun i =>
          if i < n + j then (C.wires (List.ofFn x)).getD i false else false) := by
    intro x j g hj
    have h := foldl_gate C.gates (List.ofFn x) j g hj
    have hlen : (List.ofFn x).length = n := List.length_ofFn
    rw [hlen] at h
    exact h
  have wires_inp : ∀ (x : Fin n → Bool) (w : ℕ) (hw : w < n),
      (C.wires (List.ofFn x)).getD w false = x ⟨w, hw⟩ := by
    intro x w hw
    have h := foldl_getD_lt C.gates (List.ofFn x) w (by rw [List.length_ofFn]; exact hw)
    change (C.gates.foldl stepW (List.ofFn x)).getD w false = x ⟨w, hw⟩
    rw [h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hw, ↓reduceDIte, Option.getD_some]
  let stepRel : ℕ → ℕ → Prop := fun a b =>
    a < b ∧ ∃ (k : ℕ) (h : Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs
  have cone_getD_lt : ∀ (gs : List Gate) (cs : List (List ℕ)) (j : ℕ), j < cs.length →
      (gs.foldl (coneStep n) cs).getD j [] = cs.getD j [] := by
    intro gs
    induction gs with
    | nil => intro cs j _; rfl
    | cons g0 gs ih =>
      intro cs j hj
      rw [List.foldl_cons]
      have hlt : j < (coneStep n cs g0).length := by
        change j < (cs ++ [_]).length
        simp only [List.length_append, List.length_cons, List.length_nil]
        omega
      rw [ih (coneStep n cs g0) j hlt]
      change (cs ++ [_]).getD j [] = cs.getD j []
      simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]
  have cone_gate : ∀ (gs : List Gate) (cs : List (List ℕ)) (k : ℕ) (h : Gate),
      gs[k]? = some h →
      (gs.foldl (coneStep n) cs).getD (cs.length + k) [] =
        (h.inputs.filter (fun w => decide (n ≤ w ∧ w < n + (cs.length + k)))).flatMap
          (fun w => (w - n) :: (gs.foldl (coneStep n) cs).getD (w - n) []) := by
    intro gs
    induction gs with
    | nil => intro _ _ _ h; simp at h
    | cons g0 gs ih =>
      intro cs k h hk
      cases k with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
        subst hk
        rw [Nat.add_zero, List.foldl_cons]
        have hlt : cs.length < (coneStep n cs g0).length := by
          change cs.length < (cs ++ [_]).length
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [cone_getD_lt gs (coneStep n cs g0) cs.length hlt]
        have hself : (coneStep n cs g0).getD cs.length [] =
            (g0.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
              (fun w => (w - n) :: cs.getD (w - n) []) := by
          change (cs ++ [_]).getD cs.length [] = _
          simp only [List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (le_refl cs.length)]
          simp
        rw [hself]
        apply List.flatMap_congr
        intro w hw
        simp only [List.mem_filter, decide_eq_true_eq] at hw
        have hwlt : w - n < cs.length := by omega
        have hwlt2 : w - n < (coneStep n cs g0).length := by
          change w - n < (cs ++ [_]).length
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [cone_getD_lt gs (coneStep n cs g0) (w - n) hwlt2]
        change (w - n) :: cs.getD (w - n) [] = (w - n) :: (cs ++ [_]).getD (w - n) []
        simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hwlt]
      | succ k' =>
        simp only [List.getElem?_cons_succ] at hk
        have hlen : (coneStep n cs g0).length + k' = cs.length + (k' + 1) := by
          change (cs ++ [_]).length + k' = cs.length + (k' + 1)
          simp only [List.length_append, List.length_cons, List.length_nil]
          omega
        rw [List.foldl_cons, ← hlen]
        exact ih (coneStep n cs g0) k' h hk
  have inCone_iff_rec : ∀ (k : ℕ) (h : Gate) (i : ℕ), C.gates[k]? = some h →
      (InCone n C i k ↔ ∃ w ∈ h.inputs, n ≤ w ∧ w < n + k ∧ (i = w - n ∨ InCone n C i (w - n))) := by
    intro k h i hk
    change i ∈ (C.gates.foldl (coneStep n) []).getD k [] ↔ _
    have hcg := cone_gate C.gates [] k h hk
    simp only [List.length_nil, Nat.zero_add] at hcg
    rw [hcg, List.mem_flatMap]
    constructor
    · rintro ⟨w, hw, hi⟩
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      simp only [List.mem_cons] at hi
      exact ⟨w, hw.1, hw.2.1, hw.2.2, hi⟩
    · rintro ⟨w, hwin, hle, hlt, hi⟩
      refine ⟨w, ?_, ?_⟩
      · simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hwin, hle, hlt⟩
      · rw [List.mem_cons]; exact hi
  have transGen_ge : ∀ {a b : ℕ}, Relation.TransGen stepRel a b → a < b := by
    intro a b hab
    induction hab with
    | single h => exact h.1
    | tail _ hbc ih => exact lt_trans ih hbc.1
  have inCone_of_transGen : ∀ {a b : ℕ}, Relation.TransGen stepRel a b →
      ∀ i j : ℕ, a = n + i → b = n + j → InCone n C i j := by
    intro a b hab
    induction hab with
    | single h =>
      intro i j ha hb
      rcases h with ⟨hlt, k, g, hbk, hgk, hain⟩
      have hjk : j = k := by omega
      subst hjk
      rw [inCone_iff_rec j g i hgk]
      exact ⟨n + i, ha ▸ hain, by omega, by omega, Or.inl (by omega)⟩
    | tail hab hbc ih =>
      rename_i b' c'
      intro i j ha hc
      have hlt_a : a < b' := transGen_ge hab
      have hnb : n ≤ b' := by omega
      rcases hbc with ⟨hlt_b, k, g, hck, hgk, hbin⟩
      have hjk : j = k := by omega
      subst hjk
      have hib : InCone n C i (b' - n) := ih i (b' - n) ha (by omega)
      rw [inCone_iff_rec j g i hgk]
      exact ⟨b', hbin, hnb, by omega, Or.inr hib⟩
  have or_cone_input : ∀ (w : ℕ) (x : Fin n → Bool),
      w < n + C.gates.length →
      (C.wires (List.ofFn x)).getD w false = true →
      (∀ (k : ℕ) (g : Gate), C.gates[k]? = some g → g.op = GateOp.and →
        Relation.ReflTransGen stepRel (n + k) w →
        (C.wires (List.ofFn x)).getD (n + k) false = false) →
      ∃ p : Fin n, x p = true ∧
        ∀ y : Fin n → Bool, y p = true → (C.wires (List.ofFn y)).getD w false = true := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro x hw_lt hw_true hno_and
      by_cases hw_n : w < n
      · refine ⟨⟨w, hw_n⟩, ?_, ?_⟩
        · rwa [wires_inp x w hw_n] at hw_true
        · intro y hy
          rw [wires_inp y w hw_n]
          exact hy
      · let k := w - n
        have hk_lt : k < C.gates.length := by omega
        have hwk : w = n + k := by omega
        obtain ⟨g, hgk⟩ : ∃ g, C.gates[k]? = some g := ⟨C.gates[k], List.getElem?_eq_getElem hk_lt⟩
        have hg_op := (hM_unfold g (List.mem_of_getElem? hgk)).1
        rcases hg_op with hand | hor
        · have hf := hno_and k g hgk hand (by rw [hwk])
          rw [hwk] at hw_true
          rw [hf] at hw_true
          exact Bool.noConfusion hw_true
        · have hwg := wires_gate x k g hgk
          rw [hwk] at hw_true
          rw [hw_true, hor] at hwg
          have hwg' : (g.inputs.map fun i =>
              if i < n + k then (C.wires (List.ofFn x)).getD i false else false).any id = true :=
            hwg.symm
          rw [List.any_eq_true] at hwg'
          rcases hwg' with ⟨_, hmem, hval⟩
          rw [List.mem_map] at hmem
          rcases hmem with ⟨a, hain, haeq⟩
          rw [id_eq] at hval
          rw [← haeq] at hval
          have ha_lt : a < n + k := by
            by_contra hge
            simp only [hge, ↓reduceIte] at hval
            exact Bool.noConfusion hval
          simp only [ha_lt, ↓reduceIte] at hval
          have ha_no_and : ∀ (k' : ℕ) (g' : Gate), C.gates[k']? = some g' → g'.op = GateOp.and →
              Relation.ReflTransGen stepRel (n + k') a →
              (C.wires (List.ofFn x)).getD (n + k') false = false := by
            intro k' g' hgk' hand' hreach
            apply hno_and k' g' hgk' hand'
            rw [hwk]
            exact Relation.ReflTransGen.tail hreach ⟨ha_lt, k, g, rfl, hgk, hain⟩
          obtain ⟨p, hxp, hp_wire⟩ := ih a (by omega) x (by omega) hval ha_no_and
          refine ⟨p, hxp, ?_⟩
          intro y hyp
          rw [hwk, wires_gate y k g hgk, hor]
          change (g.inputs.map fun i =>
            if i < n + k then (C.wires (List.ofFn y)).getD i false else false).any id = true
          rw [List.any_eq_true]
          refine ⟨true, List.mem_map.mpr ⟨a, hain, ?_⟩, rfl⟩
          simp only [ha_lt, ↓reduceIte]
          exact hp_wire y hyp
  refine ⟨C, hM_unfold, hE, hMin, ?_⟩
  intro t g hgt hand
  have ht_lt : t < C.gates.length := by
    by_contra hge
    rw [List.getElem?_eq_none (Nat.le_of_not_lt hge)] at hgt
    simp at hgt
  obtain ⟨hsound, u0, v0, hadj0, howns0⟩ := hSO t g hgt hand
  have inline_of_owns : ∀ u v : Fin n, Owns n C t u v →
      (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧
      ∀ (t' : ℕ) (g' : Gate), C.gates[t']? = some g' → g'.op = GateOp.and →
        Relation.TransGen stepRel (n + t') (n + t) →
        (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false := by
    intro u v ho
    refine ⟨ho.2.2.1, ?_⟩
    intro t' g' hgt' hand' htr
    have hlt_t' : t' < t := by
      have := transGen_ge htr
      omega
    have hcone : InCone n C t' t := inCone_of_transGen htr t' t rfl rfl
    have hgateAt : (PEqualNP.MetaComplexity.NestedCover.gateAt C t').op = GateOp.and := by
      change (C.gates.getD t' ⟨GateOp.or, []⟩).op = GateOp.and
      have hget : C.gates.getD t' ⟨GateOp.or, []⟩ = g' := by
        simp only [List.getD_eq_getElem?_getD, hgt', Option.getD_some]
      rw [hget]
      exact hand'
    exact ho.2.2.2 t' hlt_t' hcone hgateAt
  have h0_inline := inline_of_owns u0 v0 howns0
  have eval_and : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
  have hlen_le : g.inputs.length ≤ 2 := (hM_unfold g (List.mem_of_getElem? hgt)).2
  have hex_ab : ∃ a b : ℕ, g.inputs = [a, b] := by
    have hcases : g.inputs = [] ∨ (∃ a, g.inputs = [a]) ∨ (∃ a b, g.inputs = [a, b]) := by
      have aux : ∀ l : List ℕ, l.length ≤ 2 → l = [] ∨ (∃ a, l = [a]) ∨ (∃ a b, l = [a, b]) := by
        intro l hl
        rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl ⟨a, rfl⟩)
        · exact Or.inr (Or.inr ⟨a, b, rfl⟩)
        · simp at hl
      exact aux g.inputs hlen_le
    rcases hcases with hins | ⟨a, hins⟩ | ⟨a, b, hins⟩
    · have hf := wires_gate (fun _ : Fin n => false) t g hgt
      rw [hand, hins, eval_and] at hf
      simp only [List.map_nil, List.all_nil] at hf
      obtain ⟨i, j, _, hi, _⟩ := hsound (fun _ => false) hf
      exact Bool.noConfusion hi
    · have hf0 := wires_gate (fun k : Fin n => decide (k = u0 ∨ k = v0)) t g hgt
      rw [hand, hins, h0_inline.1, eval_and] at hf0
      simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        id_eq, Bool.and_true] at hf0
      have ha_lt : a < n + t := by
        by_contra hge
        simp only [hge, ↓reduceIte] at hf0
        exact Bool.noConfusion hf0
      simp only [ha_lt, ↓reduceIte] at hf0
      have ha_no_and : ∀ (k' : ℕ) (g' : Gate), C.gates[k']? = some g' → g'.op = GateOp.and →
          Relation.ReflTransGen stepRel (n + k') a →
          (C.wires (List.ofFn (fun k : Fin n => decide (k = u0 ∨ k = v0)))).getD (n + k') false = false := by
        intro k' g' hgk' hand' hreach
        apply h0_inline.2 k' g' hgk' hand'
        have hstep : stepRel a (n + t) := ⟨ha_lt, t, g, rfl, hgt, by rw [hins]; exact List.mem_singleton_self a⟩
        exact Relation.TransGen.tail' hreach hstep
      obtain ⟨p, _, hp_wire⟩ := or_cone_input a (fun k : Fin n => decide (k = u0 ∨ k = v0)) (by omega) hf0.symm ha_no_and
      let yp : Fin n → Bool := fun w => decide (w = p)
      have hta : (C.wires (List.ofFn yp)).getD (n + t) false = true := by
        rw [wires_gate yp t g hgt, hand, hins, eval_and]
        simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, ha_lt, ↓reduceIte]
        exact hp_wire yp (by simp [yp])
      obtain ⟨i, j, hij, hi, hj⟩ := hsound yp hta
      simp only [yp, decide_eq_true_eq] at hi hj
      subst hi; subst hj
      exact False.elim (G.ne_of_adj hij rfl)
    · exact ⟨a, b, hins⟩
  obtain ⟨a, b, hab⟩ := hex_ab
  have split_owned : ∀ u v : Fin n, G.Adj u v →
      ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧
        ∀ (t' : ℕ) (g' : Gate), C.gates[t']? = some g' → g'.op = GateOp.and →
          Relation.TransGen stepRel (n + t') (n + t) →
          (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false) →
      ∃ x y : Fin n, ((x = u ∧ y = v) ∨ (x = v ∧ y = u)) ∧ G.Adj x y ∧
        (∀ z : Fin n → Bool, z x = true → (C.wires (List.ofFn z)).getD a false = true) ∧
        (∀ z : Fin n → Bool, z y = true → (C.wires (List.ofFn z)).getD b false = true) ∧
        a < n + t ∧ b < n + t := by
    intro u v huv hown
    have htrue := hown.1
    have hbelow := hown.2
    let puv : Fin n → Bool := fun k => decide (k = u ∨ k = v)
    have hwg := wires_gate puv t g hgt
    rw [htrue, hand, hab, eval_and] at hwg
    simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true] at hwg
    have hwg' := Bool.and_eq_true_iff.mp hwg.symm
    have ha_lt : a < n + t := by
      by_contra hge
      have h1 := hwg'.1
      simp only [hge, ↓reduceIte] at h1
      exact Bool.noConfusion h1
    have hb_lt : b < n + t := by
      by_contra hge
      have h2 := hwg'.2
      simp only [hge, ↓reduceIte] at h2
      exact Bool.noConfusion h2
    have ha_true : (C.wires (List.ofFn puv)).getD a false = true := by
      simpa only [ha_lt, ↓reduceIte] using hwg'.1
    have hb_true : (C.wires (List.ofFn puv)).getD b false = true := by
      simpa only [hb_lt, ↓reduceIte] using hwg'.2
    have ha_no : ∀ (k' : ℕ) (g' : Gate), C.gates[k']? = some g' → g'.op = GateOp.and →
        Relation.ReflTransGen stepRel (n + k') a →
        (C.wires (List.ofFn puv)).getD (n + k') false = false := by
      intro k' g' hgk' hand' hreach
      exact hbelow k' g' hgk' hand'
        (Relation.TransGen.tail' hreach ⟨ha_lt, t, g, rfl, hgt, by rw [hab]; simp⟩)
    have hb_no : ∀ (k' : ℕ) (g' : Gate), C.gates[k']? = some g' → g'.op = GateOp.and →
        Relation.ReflTransGen stepRel (n + k') b →
        (C.wires (List.ofFn puv)).getD (n + k') false = false := by
      intro k' g' hgk' hand' hreach
      exact hbelow k' g' hgk' hand'
        (Relation.TransGen.tail' hreach ⟨hb_lt, t, g, rfl, hgt, by rw [hab]; simp⟩)
    obtain ⟨pa, hpa_in, hpa_w⟩ := or_cone_input a puv (by omega) ha_true ha_no
    obtain ⟨pb, hpb_in, hpb_w⟩ := or_cone_input b puv (by omega) hb_true hb_no
    have hne : pa ≠ pb := by
      intro heq
      subst heq
      let yp : Fin n → Bool := fun w => decide (w = pa)
      have hta : (C.wires (List.ofFn yp)).getD (n + t) false = true := by
        rw [wires_gate yp t g hgt, hand, hab, eval_and]
        simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, ha_lt, hb_lt, ↓reduceIte, Bool.and_eq_true]
        exact ⟨hpa_w yp (by simp [yp]), hpb_w yp (by simp [yp])⟩
      obtain ⟨i, j, hij, hi, hj⟩ := hsound yp hta
      simp only [yp, decide_eq_true_eq] at hi hj
      subst hi; subst hj
      exact G.ne_of_adj hij rfl
    simp only [puv, decide_eq_true_eq] at hpa_in hpb_in
    rcases hpa_in with rfl | rfl <;> rcases hpb_in with rfl | rfl
    · exact False.elim (hne rfl)
    · exact ⟨pa, pb, Or.inl ⟨rfl, rfl⟩, huv, hpa_w, hpb_w, ha_lt, hb_lt⟩
    · exact ⟨pa, pb, Or.inr ⟨rfl, rfl⟩, huv.symm, hpa_w, hpb_w, ha_lt, hb_lt⟩
    · exact False.elim (hne rfl)
  have pair_compat : ∀ (x1 y1 x2 y2 : Fin n),
      G.Adj x1 y1 → G.Adj x2 y2 →
      (∀ z : Fin n → Bool, z x1 = true → (C.wires (List.ofFn z)).getD a false = true) →
      (∀ z : Fin n → Bool, z y1 = true → (C.wires (List.ofFn z)).getD b false = true) →
      (∀ z : Fin n → Bool, z x2 = true → (C.wires (List.ofFn z)).getD a false = true) →
      (∀ z : Fin n → Bool, z y2 = true → (C.wires (List.ofFn z)).getD b false = true) →
      a < n + t → b < n + t →
      x1 = x2 ∨ y1 = y2 := by
    intro x1 y1 x2 y2 h12 h34 hx1 hy1 hx2 hy2 ha_lt hb_lt
    have adj_cross : ∀ (x y : Fin n),
        (∀ z : Fin n → Bool, z x = true → (C.wires (List.ofFn z)).getD a false = true) →
        (∀ z : Fin n → Bool, z y = true → (C.wires (List.ofFn z)).getD b false = true) →
        G.Adj x y := by
      intro x y hxw hyw
      let pxy : Fin n → Bool := fun k => decide (k = x ∨ k = y)
      have hta : (C.wires (List.ofFn pxy)).getD (n + t) false = true := by
        rw [wires_gate pxy t g hgt, hand, hab, eval_and]
        simp only [List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, ha_lt, hb_lt, ↓reduceIte, Bool.and_eq_true]
        exact ⟨hxw pxy (by simp [pxy]), hyw pxy (by simp [pxy])⟩
      obtain ⟨i, j, hij, hi, hj⟩ := hsound pxy hta
      simp only [pxy, decide_eq_true_eq] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact False.elim (G.ne_of_adj hij rfl)
      · exact hij
      · exact hij.symm
      · exact False.elim (G.ne_of_adj hij rfl)
    have h14 : G.Adj x1 y2 := adj_cross x1 y2 hx1 hy2
    have h32 : G.Adj x2 y1 := adj_cross x2 y1 hx2 hy1
    exact hc4 x1 y1 x2 y2 h12 h32.symm h34 h14.symm
  obtain ⟨x0, y0, _, hxy0, hx0, hy0, ha_lt, hb_lt⟩ := split_owned u0 v0 hadj0 h0_inline
  by_cases hall_x0 : ∀ u v : Fin n, G.Adj u v →
      ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧
        ∀ (t' : ℕ) (g' : Gate), C.gates[t']? = some g' → g'.op = GateOp.and →
          Relation.TransGen stepRel (n + t') (n + t) →
          (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false) →
      u = x0 ∨ v = x0
  · exact ⟨x0, ⟨u0, v0, hadj0, h0_inline⟩, hall_x0⟩
  · push Not at hall_x0
    obtain ⟨u1, v1, hadj1, h1_inline, hu1_ne, hv1_ne⟩ := hall_x0
    obtain ⟨x1, y1, hxy1_eq, hxy1, hx1, hy1, _, _⟩ := split_owned u1 v1 hadj1 h1_inline
    have hx1_ne : x1 ≠ x0 := by
      rcases hxy1_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hu1_ne
      · exact hv1_ne
    have hy1_eq : y1 = y0 := by
      rcases pair_compat x0 y0 x1 y1 hxy0 hxy1 hx0 hy0 hx1 hy1 ha_lt hb_lt with hxx | hyy
      · exact False.elim (hx1_ne hxx.symm)
      · exact hyy.symm
    subst hy1_eq
    refine ⟨y1, ⟨u0, v0, hadj0, h0_inline⟩, ?_⟩
    intro u v hadj h_inline
    obtain ⟨x, y, hxy_eq, hxy, hx, hy, _, _⟩ := split_owned u v hadj h_inline
    have hy_eq : y = y1 := by
      rcases pair_compat x0 y1 x y hxy0 hxy hx0 hy0 hx hy ha_lt hb_lt with hxx0 | hyy
      · rcases pair_compat x1 y1 x y hxy1 hxy hx1 hy1 hx hy ha_lt hb_lt with hxx1 | hyy
        · exact False.elim (hx1_ne (hxx1.trans hxx0.symm))
        · exact hyy.symm
      · exact hyy.symm
    rcases hxy_eq with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact Or.inr hy_eq
    · exact Or.inl hy_eq


open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

lemma finish_from_pair_normalization
    (hnorm : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) →
      (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
        a = c ∨ b = d) →
      ∃ C : Circuit, IsMinimalMonoCircuit n C ∧ circuitFun n C = graphFun G ∅ ∧
        ∀ t, t < C.gates.length → (gateAt C t).op = GateOp.and →
          ∀ u v : Fin n, gateVal n C t (pairInput u v) = true → G.Adj u v) :
    ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a) → (∀ a b c d : Fin n, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a → a = c ∨ b = d) → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧ (∀ D : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size ≤ D.size) ∧ ∀ (t : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[t]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ c : Fin n, (∃ u v : Fin n, G.Adj u v ∧ ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false)) ∧ ∀ u v : Fin n, G.Adj u v → ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false) → u = c ∨ v = c := by
  classical
  apply normalize_bridge
  · intro n G _ htri hfour
    obtain ⟨C, hmin, hfun, hpair⟩ := hnorm n G htri hfour
    have hcomp : ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) := by
      intro x
      simpa [circuitFun, graphFun] using congrFun hfun x
    have hmin' (D : Circuit) (hD : Monotone2 D)
        (hDf : ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
          decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) :
        C.size ≤ D.size := by
      apply hmin.2 D hD
      calc
        circuitFun n D = graphFun G ∅ := by
          funext x
          simpa [circuitFun, graphFun] using hDf x
        _ = circuitFun n C := hfun.symm
    refine ⟨C, hmin.1, hcomp, hmin', ?_⟩
    intro t g ht hop x hx
    by_cases hn : 0 < n
    · have htlt : t < C.gates.length := (List.getElem?_eq_some_iff.mp ht).1
      have hgat : gateAt C t = g := by
        simp [gateAt, List.getD_eq_getElem?_getD, ht]
      exact pair_sound_global hn G C hmin.1 hpair t htlt
        (by simpa [hgat] using hop) x hx
    · have hn0 : n = 0 := by omega
      subst n
      have hbound := hmin' (⟨[], 0⟩ : Circuit)
        (by simp [Monotone2])
        (by intro z; simp [Circuit.eval, Circuit.wires])
      have hnil : C.gates = [] := by
        apply List.length_eq_zero_iff.mp
        simpa [Circuit.size] using hbound
      simp [hnil] at ht
  · exact Prune.result

end PEqualNP.Outside.L_meta_1031_aux

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

lemma last_difference (n : ℕ) (gs : List Gate) (m : ℕ) (hm : m < gs.length)
    (hlegal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hlast : ∀ j (hj : j < gs.length), m < j → gs[j].op = GateOp.or)
    (x y : Fin n → Bool) :
    ∀ w, val gs w y = true →
      val (trim n gs m) (redirect n gs.length m w) y = false →
      n + m ≤ w ∧ (val gs (n + m) x = true → val gs w x = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hold hnew
    by_cases hwinput : w < n
    · rw [redirect_input n gs.length m w hwinput,
        val_input (trim n gs m) y w hwinput] at hnew
      rw [val_input gs y w hwinput] at hold
      rw [hold] at hnew
      contradiction
    by_cases hwbig : n + gs.length ≤ w
    · rw [val_big gs y w hwbig] at hold
      contradiction
    have hj : w - n < gs.length := by omega
    have hw : n + (w - n) = w := by omega
    by_cases heq : w - n = m
    · have hweq : w = n + m := by omega
      subst w
      exact ⟨le_rfl, id⟩
    obtain ⟨hk, hgate⟩ := trim_get n gs m (w - n) hm hj heq
    let k := if w - n < m then w - n else (w - n) - 1
    have hredirect : redirect n gs.length m w = n + k := by
      rw [← hw, redirect_gate n gs.length m (w - n) heq]
    change k < (trim n gs m).length at hk
    change (trim n gs m)[k] = _ at hgate
    rw [hredirect] at hnew
    rw [← hw] at hold
    rcases (hlegal gs[w - n] (List.getElem_mem hj)).1 with ha | ho
    · have hjm : w - n < m := by
        by_contra hge
        have hh := hlast (w - n) hj (by omega)
        rw [ha] at hh
        contradiction
      have hta : (trim n gs m)[k].op = GateOp.and := by rw [hgate]; exact ha
      have hnt : val (trim n gs m) (n + k) y = true := by
        apply (val_and (trim n gs m) y k hk hta).2
        intro i' hi'
        rw [hgate] at hi'
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hi'
        obtain ⟨hilt, hit⟩ := (val_and gs y (w - n) hj ha).1 hold i hi
        have hine : i ≠ n + m := by omega
        refine ⟨(redirect_before n gs.length m (w - n) i hm hj heq).2 ⟨hilt, hine⟩, ?_⟩
        cases he : val (trim n gs m) (redirect n gs.length m i) y with
        | true => rfl
        | false =>
          have hh := (ih i (by omega) hit he).1
          omega
      rw [hnew] at hnt
      contradiction
    · have hto : (trim n gs m)[k].op = GateOp.or := by rw [hgate]; exact ho
      obtain ⟨i, hi, hilt, hit⟩ := (val_or gs y (w - n) hj ho).1 hold
      have hifalse : val (trim n gs m) (redirect n gs.length m i) y = false := by
        by_cases him : i = n + m
        · subst i
          apply val_big
          simp [redirect, trim_length]
        · cases he : val (trim n gs m) (redirect n gs.length m i) y with
          | false => rfl
          | true =>
            have hnt : val (trim n gs m) (n + k) y = true :=
              (val_or (trim n gs m) y k hk hto).2
                ⟨redirect n gs.length m i, by rw [hgate]; exact List.mem_map.mpr ⟨i, hi, rfl⟩,
                  (redirect_before n gs.length m (w - n) i hm hj heq).2 ⟨hilt, him⟩, he⟩
            rw [hnew] at hnt
            contradiction
      obtain ⟨hmi, hix⟩ := ih i (by omega) hit hifalse
      refine ⟨by omega, ?_⟩
      intro hx
      rw [← hw]
      exact (val_or gs x (w - n) hj ho).2 ⟨i, hi, hilt, hix hx⟩

lemma minimum_last_gate_sound (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
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
    (m : ℕ) (hm : m < C.gates.length)
    (hlast : ∀ j (hj : j < C.gates.length), m < j → C.gates[j].op = GateOp.or) :
    ∀ x : Fin n → Bool, gateVal n C m x = true →
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  obtain ⟨u, v, huv, _, hdel⟩ := minimum_gate_essential n G C hlegal hfun hmin m hm
  have hy : val C.gates C.output (pairInput u v) = true := by
    change C.eval (List.ofFn (pairInput u v)) = true
    rw [hfun, decide_eq_true_eq]
    exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
  intro x hx
  have hout := (last_difference n C.gates m hm hlegal hlast x (pairInput u v)
    C.output hy hdel).2 hx
  change C.eval (List.ofFn x) = true at hout
  rw [hfun, decide_eq_true_eq] at hout
  exact hout

end PEqualNP.Outside.L_meta_1031.Rel

namespace PEqualNP.Outside.L_meta_1031.StarLower

open PEqualNP.CircuitLowerBounds

lemma getD_snoc {α : Type} (L : List α) (a d : α) (w : ℕ) :
    (L ++ [a]).getD w d = if w < L.length then L.getD w d else if w = L.length then a else d := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_append_right (by omega)]
    rw [List.getElem?_eq_none (by simp; omega)]; simp

-- one step of evaluation and one step of the dependency sets
def wstep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def dstep (D : List (Finset ℕ)) (g : Gate) : List (Finset ℕ) :=
  D ++ [g.inputs.toFinset.biUnion fun i => D.getD i ∅]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl wstep x := rfl

lemma sem (P : ℕ → Prop) : ∀ (gs : List Gate) (W1 W2 : List Bool) (D : List (Finset ℕ)),
    W1.length = D.length → W2.length = D.length →
    (∀ w, (∀ i ∈ D.getD w ∅, P i) → W1.getD w false = W2.getD w false) →
    ∀ w, (∀ i ∈ (gs.foldl dstep D).getD w ∅, P i) →
      (gs.foldl wstep W1).getD w false = (gs.foldl wstep W2).getD w false := by
  intro gs
  induction gs with
  | nil => intro W1 W2 D _ _ h; simpa using h
  | cons g gs ih =>
    intro W1 W2 D h1 h2 h
    simp only [List.foldl_cons]
    apply ih
    · simp [wstep, dstep, h1]
    · simp [wstep, dstep, h2]
    · intro w hw
      simp only [wstep, dstep] at hw ⊢
      rw [getD_snoc, getD_snoc]
      rw [getD_snoc] at hw
      rw [h1, h2]
      split_ifs with c1 c2
      · rw [if_pos c1] at hw; exact h w hw
      · rw [if_neg c1, if_pos c2] at hw
        congr 1
        apply List.map_congr_left
        intro j hj
        apply h j
        intro i hi
        apply hw
        rw [Finset.mem_biUnion]
        exact ⟨j, List.mem_toFinset.mpr hj, hi⟩
      · rfl

lemma cardb : ∀ (gs : List Gate) (D : List (Finset ℕ)) (k : ℕ),
    (∀ g ∈ gs, g.inputs.length ≤ 2) →
    (∀ T : Finset ℕ, (T.biUnion fun w => D.getD w ∅).card ≤ T.card + k) →
    ∀ T : Finset ℕ, (T.biUnion fun w => (gs.foldl dstep D).getD w ∅).card ≤
      T.card + k + gs.length := by
  intro gs
  induction gs with
  | nil => intro D k _ h T; simpa using h T
  | cons g gs ih =>
    intro D k hg h T
    simp only [List.foldl_cons, List.length_cons]
    have := ih (dstep D g) (k + 1) (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) ?_ T
    · omega
    intro T
    have hsub : (T.biUnion fun w => (dstep D g).getD w ∅) ⊆
        ((T.erase D.length) ∪ g.inputs.toFinset).biUnion fun w => D.getD w ∅ := by
      intro i hi
      rw [Finset.mem_biUnion] at hi
      obtain ⟨w, hw, hi⟩ := hi
      simp only [dstep] at hi
      rw [getD_snoc] at hi
      rw [Finset.mem_biUnion]
      split_ifs at hi with c1 c2
      · exact ⟨w, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨by omega, hw⟩), hi⟩
      · rw [Finset.mem_biUnion] at hi
        obtain ⟨j, hj, hi⟩ := hi
        exact ⟨j, Finset.mem_union_right _ hj, hi⟩
      · simp at hi
    have hc := h ((T.erase D.length) ∪ g.inputs.toFinset)
    have h3 := Finset.card_union_le (T.erase D.length) g.inputs.toFinset
    have h4 := List.toFinset_card_le g.inputs
    have h5 := hg g List.mem_cons_self
    have h6 := Finset.card_le_card hsub
    by_cases hm : D.length ∈ T
    · have h7 := Finset.card_erase_of_mem hm
      have h8 : 1 ≤ T.card := Finset.card_pos.mpr ⟨_, hm⟩
      omega
    · have h9 : (T.biUnion fun w => (dstep D g).getD w ∅) =
          T.biUnion fun w => D.getD w ∅ := by
        apply Finset.biUnion_congr rfl
        intro w hw
        simp only [dstep]
        rw [getD_snoc]
        have : w ≠ D.length := fun e => hm (e ▸ hw)
        split_ifs with c1
        · rfl
        · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
      rw [h9]; have := h T; omega

lemma base_card (n : ℕ) (T : Finset ℕ) :
    (T.biUnion fun w => ((List.range n).map fun i => ({i} : Finset ℕ)).getD w ∅).card ≤
      T.card + 0 := by
  refine le_trans Finset.card_biUnion_le ?_
  rw [Nat.add_zero]
  calc (∑ w ∈ T, (((List.range n).map fun i => ({i} : Finset ℕ)).getD w ∅).card)
      ≤ ∑ w ∈ T, 1 := by
        apply Finset.sum_le_sum
        intro w _
        rw [List.getD_eq_getElem?_getD]
        by_cases hw : w < n
        · simp [hw]
        · rw [List.getElem?_eq_none (by simp; omega)]; simp
    _ = T.card := by simp

lemma essential_subset_bound (n : ℕ) (C : Circuit) (T : Finset ℕ)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hdep : ∀ i ∈ T, ∃ x y : List Bool, x.length = n ∧ y.length = n ∧
      (∀ j : ℕ, j ≠ i → x.getD j false = y.getD j false) ∧ C.eval x ≠ C.eval y) :
    T.card ≤ C.size + 1 := by
  let D0 : List (Finset ℕ) := (List.range n).map fun i => ({i} : Finset ℕ)
  let S := (C.gates.foldl dstep D0).getD C.output ∅
  have hsub : T ⊆ S := by
    intro i hi
    by_contra hni
    obtain ⟨x, y, hx, hy, hxy, hne⟩ := hdep i hi
    apply hne
    have key := sem (fun j => x.getD j false = y.getD j false) C.gates x y D0
      (by simp [D0, hx]) (by simp [D0, hy]) ?_ C.output ?_
    · unfold Circuit.eval
      rw [wires_eq, wires_eq]
      exact key
    · intro w hw
      by_cases hwn : w < n
      · apply hw w
        simp [D0, List.getD_eq_getElem?_getD, hwn]
      · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
          List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
    · intro j hj
      exact hxy j (fun e => hni (e ▸ hj))
  have hc := cardb C.gates D0 0 hfan (base_card n) {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton] at hc
  have ht := Finset.card_le_card hsub
  change T.card ≤ ((C.gates.foldl dstep D0).getD C.output ∅).card at ht
  unfold Circuit.size
  omega

lemma adjacent_vertex_essential (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit)
    (hC : ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
      decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true))
    (v u : Fin n) (hvu : G.Adj v u) :
    ∃ x y : List Bool, x.length = n ∧ y.length = n ∧
      (∀ j : ℕ, j ≠ v.val → x.getD j false = y.getD j false) ∧
      C.eval x ≠ C.eval y := by
  let x : Fin n → Bool := fun k => decide (k = v ∨ k = u)
  let y : Fin n → Bool := fun k => decide (k = u)
  refine ⟨List.ofFn x, List.ofFn y, by simp, by simp, ?_, ?_⟩
  · intro j hjv
    by_cases hj : j < n
    · have hne : (⟨j, hj⟩ : Fin n) ≠ v := by
        intro he
        exact hjv (congrArg Fin.val he)
      simp [List.getD_eq_getElem?_getD, hj, x, y, hne]
    · rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD,
        List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]
  · have hx : C.eval (List.ofFn x) = true := by
      rw [hC]
      simp only [decide_eq_true_eq]
      exact ⟨v, u, hvu, by simp [x], by simp [x]⟩
    have hy : C.eval (List.ofFn y) = false := by
      rw [hC]
      apply decide_eq_false_iff_not.mpr
      rintro ⟨a, b, hab, ha, hb⟩
      have hau : a = u := of_decide_eq_true ha
      have hbu : b = u := of_decide_eq_true hb
      subst a
      subst b
      exact G.ne_of_adj hab rfl
    rw [hx, hy]
    decide

lemma degree_lower_bound (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n) (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hC : ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
      decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) :
    (Finset.univ.filter (fun v => G.Adj c v)).card ≤ C.size := by
  classical
  let N : Finset (Fin n) := Finset.univ.filter (fun v => G.Adj c v)
  by_cases hN : N.Nonempty
  · obtain ⟨u, hu⟩ := hN
    have hcu : G.Adj c u := (Finset.mem_filter.mp hu).2
    let V : Finset (Fin n) := insert c N
    let T : Finset ℕ := V.image Fin.val
    have hess : ∀ i ∈ T, ∃ x y : List Bool, x.length = n ∧ y.length = n ∧
        (∀ j : ℕ, j ≠ i → x.getD j false = y.getD j false) ∧ C.eval x ≠ C.eval y := by
      intro i hi
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
      rcases Finset.mem_insert.mp hv with rfl | hv
      · exact adjacent_vertex_essential n G C hC _ u hcu
      · exact adjacent_vertex_essential n G C hC v c (G.adj_symm (Finset.mem_filter.mp hv).2)
    have hcard : T.card = N.card + 1 := by
      have hcn : c ∉ N := by simp [N]
      simp only [T, Finset.card_image_of_injective V Fin.val_injective]
      exact Finset.card_insert_of_notMem hcn
    have hbound := essential_subset_bound n C T hfan hess
    change N.card ≤ C.size
    omega
  · have hn : N = ∅ := Finset.not_nonempty_iff_eq_empty.mp hN
    change N.card ≤ C.size
    simp [hn]

def run (gs : List Gate) (w : List Bool) : List Bool := gs.foldl wstep w

lemma run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

lemma run_prefix (gs : List Gate) (w : List Bool) :
    ∃ s : List Bool, run gs w = w ++ s ∧ s.length = gs.length := by
  induction gs generalizing w with
  | nil => exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    obtain ⟨s, hs, hl⟩ := ih (wstep w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: s, ?_, by simp [hl]⟩
    change run gs (wstep w g) = _
    rw [hs]
    simp [wstep]

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  obtain ⟨s, hs, hl⟩ := run_prefix gs w
  rw [hs]
  simp [hl]

lemma run_read (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨s, hs, _⟩ := run_prefix gs w
  rw [hs]
  exact List.getD_append _ _ _ _ hi

lemma or_chain {n : ℕ} (es : List (Fin n)) : ∀ (m a : ℕ), n ≤ m → a < m →
    ∃ (gs : List Gate) (o : ℕ), gs.length = es.length ∧
      (∀ g ∈ gs, g.op = GateOp.or ∧ g.inputs.length ≤ 2) ∧
      o < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (run gs w).getD o false =
          (w.getD a false || es.any (fun v => w.getD v.val false)) := by
  induction es with
  | nil =>
      intro m a _ ha
      refine ⟨[], a, rfl, by simp, by simpa using ha, ?_⟩
      intro w _
      simp [run]
  | cons v es ih =>
      intro m a hnm ha
      obtain ⟨gs, o, hlen, hgs, ho, hev⟩ := ih (m + 1) m (by omega) (by omega)
      let g : Gate := ⟨GateOp.or, [a, v.val]⟩
      refine ⟨g :: gs, o, by simp [hlen], ?_, by simp only [List.length_cons]; omega, ?_⟩
      · intro h hh
        rcases List.mem_cons.mp hh with rfl | hh
        · simp [g]
        · exact hgs h hh
      · intro w hw
        let b := w.getD a false || w.getD v.val false
        have hstep : wstep w g = w ++ [b] := by simp [wstep, g, GateOp.eval, b]
        have hw' : (wstep w g).length = m + 1 := by rw [hstep]; simp [hw]
        have old (i : Fin n) : (wstep w g).getD i.val false = w.getD i.val false := by
          rw [hstep]
          exact List.getD_append _ _ _ _ (by have := i.isLt; omega)
        have acc : (wstep w g).getD m false = b := by rw [hstep]; simp [← hw]
        change (run gs (wstep w g)).getD o false = _
        rw [hev _ hw', acc]
        have he : es.any (fun i => (wstep w g).getD i.val false) =
            es.any (fun i => w.getD i.val false) := by
          congr 1
          funext i
          exact old i
        rw [he]
        simp [List.any_cons, Bool.or_assoc, b]

lemma star_factor (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n) (hstar : ∀ u v, G.Adj u v → u = c ∨ v = c)
    (x : Fin n → Bool) :
    decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) =
      (x c && (Finset.univ.filter (fun v => G.Adj c v)).toList.any x) := by
  classical
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, Bool.and_eq_true, List.any_eq_true, Finset.mem_toList,
    Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    rcases hstar u v huv with rfl | rfl
    · exact ⟨hu, v, huv, hv⟩
    · exact ⟨hv, u, G.adj_symm huv, hu⟩
  · rintro ⟨hc, u, hu, hx⟩
    exact ⟨c, u, hu, hc, hx⟩

lemma star_nonempty_circuit (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n) (hstar : ∀ u v, G.Adj u v → u = c ∨ v = c)
    (hN : (Finset.univ.filter (fun v => G.Adj c v)).Nonempty) :
    ∃ C : Circuit,
      (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
      C.size = (Finset.univ.filter (fun v => G.Adj c v)).card ∧
      ∃ (gs : List Gate) (g : Gate), C.gates = gs ++ [g] ∧
        (∀ h ∈ gs, h.op = GateOp.or) ∧ g.op = GateOp.and ∧ C.output = n + gs.length := by
  classical
  let N := Finset.univ.filter (fun v => G.Adj c v)
  have hne : N.toList ≠ [] := by
    intro he0
    exact hN.ne_empty (Finset.toList_eq_nil.mp he0)
  obtain ⟨u, es, he⟩ := List.exists_cons_of_ne_nil hne
  obtain ⟨gs, o, hlen, hgs, ho, hev⟩ := or_chain es n u.val le_rfl u.isLt
  let g : Gate := ⟨GateOp.and, [c.val, o]⟩
  let C : Circuit := ⟨gs ++ [g], n + gs.length⟩
  refine ⟨C, ?_, ?_, ?_, gs, g, rfl, fun h hh => (hgs h hh).1, rfl, rfl⟩
  · intro h hh
    rcases List.mem_append.mp hh with hh | hh
    · exact ⟨Or.inr (hgs h hh).1, (hgs h hh).2⟩
    · have hEq : h = g := by simpa using hh
      subst h
      simp [g]
  · intro x
    have hw : (run gs (List.ofFn x)).length = n + gs.length := by simp [run_length]
    have hc : (run gs (List.ofFn x)).getD c.val false = x c := by
      rw [run_read _ _ _ (by simpa using c.isLt)]
      simp
    have hout : (run gs (List.ofFn x)).getD o false = (x u || es.any x) := by
      rw [hev _ (by simp)]
      simp
    change (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = _
    rw [run_append]
    change ((run gs (List.ofFn x)) ++ [g.op.eval
      (g.inputs.map fun i => (run gs (List.ofFn x)).getD i false)]).getD (n + gs.length) false = _
    rw [getD_snoc, if_neg (by omega), if_pos hw.symm]
    rw [star_factor n G c hstar x]
    have he' : (Finset.univ.filter (fun v => G.Adj c v)).toList = u :: es := he
    simp only [g, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
      id_eq, Bool.and_true, hc, hout, he', List.any_cons]
  · have hcard : N.card = es.length + 1 := by
      have := congrArg List.length he
      simpa using this
    change (gs ++ [g]).length = N.card
    simp [hlen, hcard]

def OwnsExplicit (n : ℕ) (C : Circuit) (t : ℕ) (u v : Fin n) : Prop :=
  (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧
    ∀ (t' : ℕ) (g' : Gate), C.gates[t']? = some g' → g'.op = GateOp.and →
      Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : Gate),
        b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) →
      (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false

lemma last_and_index (C : Circuit) (gs : List Gate) (g : Gate)
    (hC : C.gates = gs ++ [g]) (hgs : ∀ h ∈ gs, h.op = GateOp.or)
    (t : ℕ) (h : Gate) (ht : C.gates[t]? = some h) (hop : h.op = GateOp.and) :
    t = gs.length := by
  have hlt := (List.getElem?_eq_some_iff.mp ht).1
  rw [hC, List.length_append, List.length_singleton] at hlt
  have hn : ¬ t < gs.length := by
    intro hpre
    rw [hC, List.getElem?_append_left hpre] at ht
    have hh := hgs h (List.mem_of_getElem? ht)
    rw [hop] at hh
    cases hh
  omega

lemma unique_and_owns (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (t : ℕ)
    (hcompute : ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
      decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true))
    (hout : C.output = n + t)
    (hunique : ∀ (s : ℕ) (g : Gate), C.gates[s]? = some g → g.op = GateOp.and → s = t)
    (u v : Fin n) (huv : G.Adj u v) : OwnsExplicit n C t u v := by
  constructor
  · rw [← hout]
    change C.eval (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v))) = true
    rw [hcompute]
    simp only [decide_eq_true_eq]
    exact ⟨u, v, huv, by simp, by simp⟩
  · intro s g hs hop hpath
    have hst := hunique s g hs hop
    subst s
    have inc {a b : ℕ} (hp : Relation.TransGen (fun a b : ℕ => a < b ∧
        ∃ (k : ℕ) (h : Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) a b) :
        a < b := by
      induction hp with
      | single h => exact h.1
      | tail _ h ih => exact ih.trans h.1
    have := inc hpath
    omega

lemma star_optimal (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (c : Fin n) (hstar : ∀ u v, G.Adj u v → u = c ∨ v = c) :
    ∃ C : Circuit,
      (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
      (∀ D : Circuit,
        (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
          decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size ≤ D.size) ∧
      ∀ (t : ℕ) (g : Gate), C.gates[t]? = some g → g.op = GateOp.and →
        ∃ a : Fin n, (∃ u v : Fin n, G.Adj u v ∧ OwnsExplicit n C t u v) ∧
          ∀ u v : Fin n, G.Adj u v → OwnsExplicit n C t u v → u = a ∨ v = a := by
  classical
  let N := Finset.univ.filter (fun v => G.Adj c v)
  by_cases hN : N.Nonempty
  · obtain ⟨C, hgate, hcompute, hsize, gs, g, hsplit, hgs, _, hout⟩ :=
      star_nonempty_circuit n G c hstar hN
    refine ⟨C, hgate, hcompute, ?_, ?_⟩
    · intro D hD hDeval
      rw [hsize]
      exact degree_lower_bound n G c D (fun h hh => (hD h hh).2) hDeval
    · intro t h ht hop
      have htlast := last_and_index C gs g hsplit hgs t h ht hop
      subst t
      have hunique := last_and_index C gs g hsplit hgs
      obtain ⟨u, hu⟩ := hN
      have hcu : G.Adj c u := (Finset.mem_filter.mp hu).2
      refine ⟨c, ⟨c, u, hcu, unique_and_owns n G C gs.length hcompute hout hunique c u hcu⟩, ?_⟩
      intro u v huv _
      exact hstar u v huv
  · have hno : ∀ u v : Fin n, ¬ G.Adj u v := by
      intro u v huv
      apply hN
      rcases hstar u v huv with rfl | rfl
      · exact ⟨v, Finset.mem_filter.mpr ⟨Finset.mem_univ _, huv⟩⟩
      · exact ⟨u, Finset.mem_filter.mpr ⟨Finset.mem_univ _, G.adj_symm huv⟩⟩
    let C : Circuit := ⟨[], n⟩
    refine ⟨C, by simp [C], ?_, ?_, ?_⟩
    · intro x
      simp [C, Circuit.eval, Circuit.wires, hno]
    · intro D _ _
      exact Nat.zero_le D.size
    · intro t g ht _
      simp [C] at ht

end PEqualNP.Outside.L_meta_1031.StarLower

namespace PEqualNP.Outside.L_meta_1031.Matching

open PEqualNP.CircuitLowerBounds

lemma edge_chain {n : ℕ} (es : List (Fin n × Fin n)) :
    ∀ (m a : ℕ), n ≤ m → a < m →
      ∃ (gs : List Gate) (o : ℕ),
        gs.length = 2 * es.length ∧
        (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
        (∀ g ∈ gs, g.op = GateOp.and → ∃ p ∈ es, g.inputs = [p.1.val, p.2.val]) ∧
        o < m + gs.length ∧
        ∀ w : List Bool, w.length = m →
          (run gs w).getD o false =
            (w.getD a false || es.any (fun p => w.getD p.1.val false && w.getD p.2.val false)) := by
  induction es with
  | nil =>
      intro m a _ ha
      refine ⟨[], a, by simp, by simp, by simp, by simpa using ha, ?_⟩
      intro w _
      simp [run]
  | cons p es ih =>
      intro m a hnm ha
      obtain ⟨gs, o, hlen, hgs, hpair, ho, hev⟩ := ih (m + 2) (m + 1) (by omega) (by omega)
      let pre : List Gate := [⟨GateOp.and, [p.1.val, p.2.val]⟩, ⟨GateOp.or, [a, m]⟩]
      refine ⟨pre ++ gs, o, ?_, ?_, ?_, ?_, ?_⟩
      · simp [pre, hlen]; omega
      · intro g hg
        rcases List.mem_append.mp hg with hg | hg
        · simp only [pre, List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl <;> simp
        · exact hgs g hg
      · intro g hg hop
        rcases List.mem_append.mp hg with hg | hg
        · simp only [pre, List.mem_cons, List.not_mem_nil, or_false] at hg
          rcases hg with rfl | rfl
          · exact ⟨p, List.mem_cons_self, rfl⟩
          · cases hop
        · obtain ⟨q, hq, hin⟩ := hpair g hg hop
          exact ⟨q, List.mem_cons_of_mem p hq, hin⟩
      · simp only [List.length_append]
        have : pre.length = 2 := rfl
        omega
      · intro w hw
        let e := w.getD p.1.val false && w.getD p.2.val false
        have hstep : run pre w = w ++ [e, w.getD a false || e] := by
          have ha' : a < w.length := by omega
          simp [pre, run, GateOp.eval, List.getElem?_append_left ha', ← hw, e]
        have hlen : (run pre w).length = m + 2 := by rw [hstep]; simp [hw]
        have old (i : Fin n) : (run pre w).getD i.val false = w.getD i.val false := by
          rw [hstep]
          exact List.getD_append _ _ _ _ (by have := i.isLt; omega)
        have acc : (run pre w).getD (m + 1) false = (w.getD a false || e) := by
          rw [hstep]
          simp [← hw]
        rw [run_append, hev _ hlen, acc]
        have he : es.any (fun p => (run pre w).getD p.1.val false &&
            (run pre w).getD p.2.val false) =
            es.any (fun p => w.getD p.1.val false && w.getD p.2.val false) := by
          congr 1
          funext p
          rw [old, old]
        rw [he]
        simp [List.any_cons, Bool.or_assoc, e]

lemma nonempty_edge_circuit (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (p : Fin n × Fin n) (es : List (Fin n × Fin n))
    (hedges : ∀ u v, G.Adj u v ↔ (u, v) ∈ p :: es ∨ (v, u) ∈ p :: es) :
    ∃ C : Circuit,
      C.size = 2 * (p :: es).length - 1 ∧
      (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
      ∀ g ∈ C.gates, g.op = GateOp.and →
        ∃ u v : Fin n, G.Adj u v ∧ g.inputs = [u.val, v.val] := by
  obtain ⟨gs, o, hlen, hgs, hpair, _, hev⟩ :=
    edge_chain es (n + 1) n (by omega) (by omega)
  let first : Gate := ⟨GateOp.and, [p.1.val, p.2.val]⟩
  refine ⟨⟨first :: gs, o⟩, ?_, ?_, ?_, ?_⟩
  · change (first :: gs).length = _
    simp [hlen]; omega
  · intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [first]
    · exact hgs g hg
  · intro x
    let e := x p.1 && x p.2
    have hfirst : run [first] (List.ofFn x) = List.ofFn x ++ [e] := by
      simp [run, first, GateOp.eval, e]
    change (run ([first] ++ gs) (List.ofFn x)).getD o false = _
    rw [run_append, hfirst]
    rw [hev _ (by simp)]
    have old (i : Fin n) : (List.ofFn x ++ [e]).getD i.val false = x i := by
      rw [List.getD_append _ _ _ _ (by simpa using i.isLt)]
      simp
    have acc : (List.ofFn x ++ [e]).getD n false = e := by simp
    rw [acc]
    have he : es.any (fun q => (List.ofFn x ++ [e]).getD q.1.val false &&
        (List.ofFn x ++ [e]).getD q.2.val false) = es.any (fun q => x q.1 && x q.2) := by
      congr 1
      funext q
      rw [old, old]
    rw [he]
    apply Bool.eq_iff_iff.mpr
    change (p :: es).any (fun q => x q.1 && x q.2) = true ↔ _
    simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · rintro ⟨q, hq, h1, h2⟩
      exact ⟨q.1, q.2, (hedges _ _).mpr (Or.inl hq), h1, h2⟩
    · rintro ⟨u, v, huv, hu, hv⟩
      rcases (hedges _ _).mp huv with h | h
      · exact ⟨(u, v), h, hu, hv⟩
      · exact ⟨(v, u), h, hv, hu⟩
  · intro g hg hop
    rcases List.mem_cons.mp hg with rfl | hg
    · exact ⟨p.1, p.2, (hedges _ _).mpr (Or.inl List.mem_cons_self), rfl⟩
    · obtain ⟨q, hq, hin⟩ := hpair g hg hop
      exact ⟨q.1, q.2, (hedges _ _).mpr (Or.inl (List.mem_cons_of_mem p hq)), hin⟩

lemma vertices_lower_bound (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (V : Finset (Fin n))
    (hV : ∀ v ∈ V, ∃ u, G.Adj v u)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hC : ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
      decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) :
    V.card ≤ C.size + 1 := by
  let T : Finset ℕ := V.image Fin.val
  have hdep : ∀ i ∈ T, ∃ x y : List Bool, x.length = n ∧ y.length = n ∧
      (∀ j : ℕ, j ≠ i → x.getD j false = y.getD j false) ∧ C.eval x ≠ C.eval y := by
    intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨u, hu⟩ := hV v hv
    exact StarLower.adjacent_vertex_essential n G C hC v u hu
  have hbound := StarLower.essential_subset_bound n C T hfan hdep
  have hcard : T.card = V.card := Finset.card_image_of_injective V Fin.val_injective
  omega

lemma matching_lower_bound (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (es : List (Fin n × Fin n))
    (hedges : ∀ p ∈ es, G.Adj p.1 p.2)
    (hdistinct : (es.flatMap (fun p => [p.1, p.2])).Nodup)
    (C : Circuit)
    (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hC : ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
      decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) :
    2 * es.length ≤ C.size + 1 := by
  classical
  let V := (es.flatMap (fun p => [p.1, p.2])).toFinset
  have hv : ∀ v ∈ V, ∃ u, G.Adj v u := by
    intro v hv
    obtain ⟨p, hp, hv⟩ := List.mem_flatMap.mp (List.mem_toFinset.mp hv)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact ⟨p.2, hedges p hp⟩
    · exact ⟨p.1, G.adj_symm (hedges p hp)⟩
  have hlength (xs : List (Fin n × Fin n)) :
      (xs.flatMap (fun p => [p.1, p.2])).length = 2 * xs.length := by
    induction xs with
    | nil => simp
    | cons p xs ih => simp [ih]; omega
  have hcard : V.card = 2 * es.length := by
    change (es.flatMap (fun p => [p.1, p.2])).toFinset.card = _
    rw [List.toFinset_card_of_nodup hdistinct, hlength]
  have hbound := vertices_lower_bound n G C V hv hfan hC
  omega

lemma matching_optimal (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (es : List (Fin n × Fin n))
    (hedges : ∀ u v, G.Adj u v ↔ (u, v) ∈ es ∨ (v, u) ∈ es)
    (hdistinct : (es.flatMap (fun p => [p.1, p.2])).Nodup) :
    ∃ C : Circuit,
      C.size = 2 * es.length - 1 ∧
      (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
      (∀ D : Circuit,
        (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
          decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size ≤ D.size) ∧
      ∀ t g, C.gates[t]? = some g → g.op = GateOp.and →
        ∃ c : Fin n, (∃ u v : Fin n, G.Adj u v ∧ OwnsPair n C t u v) ∧
          ∀ u v : Fin n, G.Adj u v → OwnsPair n C t u v → u = c ∨ v = c := by
  cases es with
  | nil =>
    have hno : ∀ u v : Fin n, ¬ G.Adj u v := by simpa using hedges
    let C : Circuit := ⟨[], n⟩
    refine ⟨C, rfl, by simp [C], ?_, ?_, ?_⟩
    · intro x
      simp [C, Circuit.eval, Circuit.wires, hno]
    · intro D _ _
      exact Nat.zero_le D.size
    · intro t g ht _
      simp [C] at ht
  | cons p es =>
    obtain ⟨C, hsize, hgate, hcompute, hshape⟩ := nonempty_edge_circuit n G p es hedges
    refine ⟨C, hsize, hgate, hcompute, ?_, direct_stars n G C hshape⟩
    intro D hD hDeval
    have hedge : ∀ q ∈ p :: es, G.Adj q.1 q.2 := by
      intro q hq
      exact (hedges _ _).mpr (Or.inl hq)
    have hbound := matching_lower_bound n G (p :: es) hedge hdistinct D
      (fun g hg => (hD g hg).2) hDeval
    omega

lemma degree_one_edge_list (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdegree : ∀ u v w, G.Adj u v → G.Adj u w → v = w) :
    ∃ es : List (Fin n × Fin n),
      (∀ u v, G.Adj u v ↔ (u, v) ∈ es ∨ (v, u) ∈ es) ∧
      (es.flatMap (fun p => [p.1, p.2])).Nodup := by
  classical
  let E := Finset.univ.filter (fun p : Fin n × Fin n => G.Adj p.1 p.2 ∧ p.1.val < p.2.val)
  let es := E.toList
  have hmem (p : Fin n × Fin n) : p ∈ es ↔ G.Adj p.1 p.2 ∧ p.1.val < p.2.val := by
    simp [es, E]
  refine ⟨es, ?_, ?_⟩
  · intro u v
    constructor
    · intro huv
      have hne : u.val ≠ v.val := fun h => G.ne_of_adj huv (Fin.ext h)
      rcases Nat.lt_or_gt_of_ne hne with h | h
      · exact Or.inl ((hmem _).mpr ⟨huv, h⟩)
      · exact Or.inr ((hmem _).mpr ⟨huv.symm, h⟩)
    · rintro (h | h)
      · exact ((hmem _).mp h).1
      · exact ((hmem _).mp h).1.symm
  · apply List.nodup_flatMap.mpr
    constructor
    · intro p hp
      have hne : p.1 ≠ p.2 := fun h => by
        have hlt := ((hmem p).mp hp).2
        rw [h] at hlt
        omega
      simp [hne]
    · apply E.nodup_toList.pairwise_of_forall_ne
      intro p hp q hq hpq
      change List.Disjoint [p.1, p.2] [q.1, q.2]
      apply List.disjoint_left.mpr
      intro x hx hy
      obtain ⟨hpedge, hplt⟩ := (hmem p).mp hp
      obtain ⟨hqedge, hqlt⟩ := (hmem q).mp hq
      rcases p with ⟨a, b⟩
      rcases q with ⟨c, d⟩
      simp only [Prod.fst, Prod.snd] at *
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx hy
      rcases hx with hxa | hxb
      · subst x
        rcases hy with h | h
        · subst c
          have hbd := hdegree a b d hpedge hqedge
          exact hpq (Prod.ext rfl hbd)
        · subst d
          have hbc := hdegree a b c hpedge hqedge.symm
          subst c
          omega
      · subst x
        rcases hy with h | h
        · subst c
          have had := hdegree b a d hpedge.symm hqedge
          subst d
          omega
        · subst d
          have hac := hdegree b a c hpedge.symm hqedge.symm
          exact hpq (Prod.ext hac rfl)

lemma degree_one_optimal (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hdegree : ∀ u v w, G.Adj u v → G.Adj u w → v = w) :
    ∃ C : Circuit,
      (∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧
      (∀ D : Circuit,
        (∀ g ∈ D.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
          decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size ≤ D.size) ∧
      ∀ t g, C.gates[t]? = some g → g.op = GateOp.and →
        ∃ c : Fin n, (∃ u v : Fin n, G.Adj u v ∧ OwnsPair n C t u v) ∧
          ∀ u v : Fin n, G.Adj u v → OwnsPair n C t u v → u = c ∨ v = c := by
  obtain ⟨es, he, hd⟩ := degree_one_edge_list n G hdegree
  obtain ⟨C, _, hC⟩ := matching_optimal n G es he hd
  exact ⟨C, hC⟩

end PEqualNP.Outside.L_meta_1031.Matching

namespace PEqualNP.Outside.L_meta_1031_aux.Maximal

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

def wireStep (n : ℕ) (gs : List Gate) (a b : ℕ) : Prop :=
  a < b ∧ ∃ j, ∃ hj : j < gs.length, b = n + j ∧ a ∈ gs[j].inputs

lemma downstream_difference (n : ℕ) (gs : List Gate) (m : ℕ) (hm : m < gs.length)
    (hlegal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (htop : ∀ j (hj : j < gs.length),
      Relation.TransGen (wireStep n gs) (n + m) (n + j) → gs[j].op = GateOp.or)
    (x y : Fin n → Bool) :
    ∀ w, val gs w y = true →
      val (trim n gs m) (redirect n gs.length m w) y = false →
      Relation.ReflTransGen (wireStep n gs) (n + m) w ∧
        (val gs (n + m) x = true → val gs w x = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hold hnew
    by_cases hwinput : w < n
    · rw [redirect_input n gs.length m w hwinput,
        val_input (trim n gs m) y w hwinput] at hnew
      rw [val_input gs y w hwinput] at hold
      rw [hold] at hnew
      contradiction
    by_cases hwbig : n + gs.length ≤ w
    · rw [val_big gs y w hwbig] at hold
      contradiction
    have hj : w - n < gs.length := by omega
    have hw : n + (w - n) = w := by omega
    by_cases heq : w - n = m
    · have hweq : w = n + m := by omega
      subst w
      exact ⟨Relation.ReflTransGen.refl, id⟩
    obtain ⟨hk, hgate⟩ := trim_get n gs m (w - n) hm hj heq
    let k := if w - n < m then w - n else (w - n) - 1
    have hredirect : redirect n gs.length m w = n + k := by
      rw [← hw, redirect_gate n gs.length m (w - n) heq]
    change k < (trim n gs m).length at hk
    change (trim n gs m)[k] = _ at hgate
    rw [hredirect] at hnew
    rw [← hw] at hold
    have step (i : ℕ) (hi : i ∈ gs[w - n].inputs) (hilt : i < n + (w - n)) :
        wireStep n gs i (n + (w - n)) := ⟨hilt, w - n, hj, rfl, hi⟩
    rcases (hlegal gs[w - n] (List.getElem_mem hj)).1 with ha | ho
    · have hta : (trim n gs m)[k].op = GateOp.and := by rw [hgate]; exact ha
      have hnt : val (trim n gs m) (n + k) y = true := by
        apply (val_and (trim n gs m) y k hk hta).2
        intro i' hi'
        rw [hgate] at hi'
        obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hi'
        obtain ⟨hilt, hit⟩ := (val_and gs y (w - n) hj ha).1 hold i hi
        have hine : i ≠ n + m := by
          intro he
          have hpath : Relation.TransGen (wireStep n gs) (n + m) (n + (w - n)) := by
            rw [← he]
            exact Relation.TransGen.single (step i hi hilt)
          have hbad := htop (w - n) hj hpath
          rw [ha] at hbad
          contradiction
        refine ⟨(redirect_before n gs.length m (w - n) i hm hj heq).2 ⟨hilt, hine⟩, ?_⟩
        cases he : val (trim n gs m) (redirect n gs.length m i) y with
        | true => rfl
        | false =>
          have hreach := (ih i (by omega) hit he).1
          have hpath : Relation.TransGen (wireStep n gs) (n + m) (n + (w - n)) :=
            Relation.TransGen.tail' hreach (step i hi hilt)
          have hbad := htop (w - n) hj hpath
          rw [ha] at hbad
          contradiction
      rw [hnew] at hnt
      contradiction
    · have hto : (trim n gs m)[k].op = GateOp.or := by rw [hgate]; exact ho
      obtain ⟨i, hi, hilt, hit⟩ := (val_or gs y (w - n) hj ho).1 hold
      have hifalse : val (trim n gs m) (redirect n gs.length m i) y = false := by
        by_cases him : i = n + m
        · subst i
          apply val_big
          simp [redirect, trim_length]
        · cases he : val (trim n gs m) (redirect n gs.length m i) y with
          | false => rfl
          | true =>
            have hnt : val (trim n gs m) (n + k) y = true :=
              (val_or (trim n gs m) y k hk hto).2
                ⟨redirect n gs.length m i, by rw [hgate]; exact List.mem_map.mpr ⟨i, hi, rfl⟩,
                  (redirect_before n gs.length m (w - n) i hm hj heq).2 ⟨hilt, him⟩, he⟩
            rw [hnew] at hnt
            contradiction
      obtain ⟨hmi, hix⟩ := ih i (by omega) hit hifalse
      refine ⟨?_, ?_⟩
      · rw [← hw]
        exact Relation.ReflTransGen.tail hmi (step i hi hilt)
      · intro hx
        rw [← hw]
        exact (val_or gs x (w - n) hj ho).2 ⟨i, hi, hilt, hix hx⟩

lemma minimum_top_gate_sound (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
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
    (m : ℕ) (hm : m < C.gates.length)
    (htop : ∀ j (hj : j < C.gates.length),
      Relation.TransGen (wireStep n C.gates) (n + m) (n + j) → C.gates[j].op = GateOp.or) :
    ∀ x : Fin n → Bool, gateVal n C m x = true →
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  obtain ⟨u, v, huv, _, hdel⟩ := minimum_gate_essential n G C hlegal hfun hmin m hm
  have hy : val C.gates C.output (pairInput u v) = true := by
    change C.eval (List.ofFn (pairInput u v)) = true
    rw [hfun, decide_eq_true_eq]
    exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
  intro x hx
  have hout := (downstream_difference n C.gates m hm hlegal htop x (pairInput u v)
    C.output hy hdel).2 hx
  change C.eval (List.ofFn x) = true at hout
  rw [hfun, decide_eq_true_eq] at hout
  exact hout

end PEqualNP.Outside.L_meta_1031_aux.Maximal

namespace PEqualNP.Outside.L_meta_1031.ReadOnce

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1031.StarLower

def positive {n : ℕ} : DMFormula n → Prop
  | .lit _ b => b = true
  | .and a b => positive a ∧ positive b
  | .or a b => positive a ∧ positive b

lemma leaves_pos {n : ℕ} (f : DMFormula n) : 0 < f.leaves := by
  induction f with
  | lit i b => simp [DMFormula.leaves]
  | and a b ha hb => simp only [DMFormula.leaves]; omega
  | or a b ha hb => simp only [DMFormula.leaves]; omega

lemma compile {n : ℕ} (f : DMFormula n) (hf : positive f) :
    ∀ m : ℕ, n ≤ m → ∃ (gs : List Gate) (o : ℕ),
      gs.length + 1 = f.leaves ∧
      (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      o < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (run gs w).getD o false = f.eval (fun i => w.getD i.val false) := by
  induction f with
  | lit i b =>
    intro m hnm
    have hb : b = true := hf
    subst b
    refine ⟨[], i.val, rfl, by simp, by have := i.isLt; simp; omega, ?_⟩
    intro w hw
    rfl
  | and a b ia ib =>
    intro m hnm
    obtain ⟨ga, oa, hla, hga, hoa, hea⟩ := ia hf.1 m hnm
    obtain ⟨gb, ob, hlb, hgb, hob, heb⟩ := ib hf.2 (m + ga.length) (by omega)
    let g : Gate := ⟨GateOp.and, [oa, ob]⟩
    refine ⟨ga ++ gb ++ [g], m + ga.length + gb.length, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton, DMFormula.leaves]
      omega
    · intro h hh
      rcases List.mem_append.mp hh with hh | hh
      · rcases List.mem_append.mp hh with hh | hh
        · exact hga h hh
        · exact hgb h hh
      · have he : h = g := by simpa using hh
        subst h
        simp [g]
    · simp only [List.length_append, List.length_singleton]
      omega
    · intro w hw
      let wa := run ga w
      let wb := run gb wa
      have hwa : wa.length = m + ga.length := by simp [wa, run_length, hw]
      have hwb : wb.length = m + ga.length + gb.length := by simp [wb, run_length, hwa]
      have hgetA : wb.getD oa false = a.eval (fun i => w.getD i.val false) := by
        rw [run_read gb wa oa (by omega)]
        exact hea w hw
      have hgetB : wb.getD ob false = b.eval (fun i => w.getD i.val false) := by
        rw [heb wa hwa]
        congr 1
        funext i
        exact run_read ga w i.val (by have := i.isLt; omega)
      rw [run_append, run_append]
      change (wb ++ [g.op.eval (g.inputs.map fun i => wb.getD i false)]).getD
        (m + ga.length + gb.length) false = _
      rw [← hwb, getD_snoc]
      simp only [lt_self_iff_false, ↓reduceIte, g, GateOp.eval,
        List.map_cons, List.map_nil, List.all_cons, List.all_nil, id_eq,
        Bool.and_true, DMFormula.eval]
      exact congrArg₂ Bool.and hgetA hgetB
  | or a b ia ib =>
    intro m hnm
    obtain ⟨ga, oa, hla, hga, hoa, hea⟩ := ia hf.1 m hnm
    obtain ⟨gb, ob, hlb, hgb, hob, heb⟩ := ib hf.2 (m + ga.length) (by omega)
    let g : Gate := ⟨GateOp.or, [oa, ob]⟩
    refine ⟨ga ++ gb ++ [g], m + ga.length + gb.length, ?_, ?_, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton, DMFormula.leaves]
      omega
    · intro h hh
      rcases List.mem_append.mp hh with hh | hh
      · rcases List.mem_append.mp hh with hh | hh
        · exact hga h hh
        · exact hgb h hh
      · have he : h = g := by simpa using hh
        subst h
        simp [g]
    · simp only [List.length_append, List.length_singleton]
      omega
    · intro w hw
      let wa := run ga w
      let wb := run gb wa
      have hwa : wa.length = m + ga.length := by simp [wa, run_length, hw]
      have hwb : wb.length = m + ga.length + gb.length := by simp [wb, run_length, hwa]
      have hgetA : wb.getD oa false = a.eval (fun i => w.getD i.val false) := by
        rw [run_read gb wa oa (by omega)]
        exact hea w hw
      have hgetB : wb.getD ob false = b.eval (fun i => w.getD i.val false) := by
        rw [heb wa hwa]
        congr 1
        funext i
        exact run_read ga w i.val (by have := i.isLt; omega)
      rw [run_append, run_append]
      change (wb ++ [g.op.eval (g.inputs.map fun i => wb.getD i false)]).getD
        (m + ga.length + gb.length) false = _
      rw [← hwb, getD_snoc]
      simp only [lt_self_iff_false, ↓reduceIte, g, GateOp.eval,
        List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq,
        Bool.or_false, DMFormula.eval]
      exact congrArg₂ Bool.or hgetA hgetB

lemma active_lower (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
    (hc : ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
      decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) :
    (Finset.univ.filter (fun v => ∃ u, G.Adj v u)).card ≤ C.size + 1 := by
  classical
  let V := Finset.univ.filter (fun v => ∃ u, G.Adj v u)
  let T := V.image Fin.val
  have hb := essential_subset_bound n C T hfan (by
    intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨u, hu⟩ := (Finset.mem_filter.mp hv).2
    exact adjacent_vertex_essential n G C hc v u hu)
  have he : T.card = V.card := Finset.card_image_of_injective _ Fin.val_injective
  rwa [he] at hb

lemma compact_formula_minimum (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (f : DMFormula n) (hf : positive f)
    (heval : ∀ x : Fin n → Bool, f.eval x =
      decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true))
    (hleaves : f.leaves ≤ (Finset.univ.filter (fun v => ∃ u, G.Adj v u)).card) :
    ∃ C : Circuit, Monotone2 C ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) ∧
      (∀ D : Circuit, Monotone2 D →
        (∀ x : Fin n → Bool, D.eval (List.ofFn x) =
          decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) →
        C.size ≤ D.size) ∧ C.size + 1 = f.leaves := by
  classical
  obtain ⟨gs, o, hlen, hgs, ho, he⟩ := compile f hf n le_rfl
  let C : Circuit := ⟨gs, o⟩
  have hm : Monotone2 C := by
    intro g hg
    obtain ⟨hop, hfan⟩ := hgs g hg
    refine ⟨?_, hfan⟩
    simpa using hop
  have hc : ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
      decide (∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) := by
    intro x
    change (run gs (List.ofFn x)).getD o false = _
    rw [he _ (by simp)]
    simpa using heval x
  refine ⟨C, hm, hc, ?_, hlen⟩
  intro D hD hDe
  have hb := active_lower n G D (fun g hg => (hD g hg).2) hDe
  change gs.length ≤ D.size
  omega

end PEqualNP.Outside.L_meta_1031.ReadOnce

namespace PEqualNP.Outside.L_meta_1031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

abbrev c5Graph : SimpleGraph (Fin 5) :=
  edgeGraph 5 [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0)]

def c5Circuit : Circuit :=
  ⟨[⟨.or, [1, 4]⟩, ⟨.and, [0, 5]⟩,
    ⟨.or, [1, 3]⟩, ⟨.and, [2, 7]⟩,
    ⟨.and, [3, 4]⟩, ⟨.or, [6, 8]⟩, ⟨.or, [9, 10]⟩], 11⟩

lemma c5_size : c5Circuit.size = 7 := rfl

lemma c5_no_triangle : ∀ a b c : Fin 5,
    c5Graph.Adj a b → c5Graph.Adj b c → ¬ c5Graph.Adj c a := by
  decide

lemma c5_no_four : ∀ a b c d : Fin 5,
    c5Graph.Adj a b → c5Graph.Adj b c → c5Graph.Adj c d → c5Graph.Adj d a →
      a = c ∨ b = d := by
  decide

lemma c5_monotone : Monotone2 c5Circuit := by
  simp [Monotone2, c5Circuit]

lemma c5_computes : ∀ x : Fin 5 → Bool,
    c5Circuit.eval (List.ofFn x) =
      decide (∃ u v : Fin 5, c5Graph.Adj u v ∧ x u = true ∧ x v = true) := by
  decide

lemma c5_star : HasStarProfile 5 c5Graph c5Circuit := by
  decide

lemma c5_nonempty : ∀ j < c5Circuit.gates.length,
    (PEqualNP.MetaComplexity.NestedCover.gateAt c5Circuit j).op = GateOp.and →
      ∃ u v : Fin 5, c5Graph.Adj u v ∧ Owns 5 c5Circuit j u v := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  decide

end PEqualNP.Outside.L_meta_1031_aux

namespace PEqualNP.Outside.L_meta_1031_aux.TwoDirty

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

abbrev graph : SimpleGraph (Fin 4) := edgeGraph 4 [(0, 1), (2, 3)]

def circuit : Circuit :=
  ⟨[⟨GateOp.or, [0, 2]⟩, ⟨GateOp.or, [1, 3]⟩, ⟨GateOp.and, [4, 5]⟩,
    ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.or, [1, 2]⟩, ⟨GateOp.and, [7, 8]⟩,
    ⟨GateOp.and, [6, 9]⟩], 10⟩

def direct : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.or, [4, 5]⟩], 6⟩

lemma legal : Monotone2 circuit := by
  simp [Monotone2, circuit]

lemma computes : ∀ x : Fin 4 → Bool,
    circuitFun 4 circuit x = ((x 0 && x 1) || (x 2 && x 3)) := by
  decide +kernel

lemma computes_graph : ∀ x : Fin 4 → Bool,
    circuitFun 4 circuit x = decide (∃ u v : Fin 4, graph.Adj u v ∧ x u = true ∧ x v = true) := by
  decide +kernel

lemma no_triangles : ∀ a b c : Fin 4,
    graph.Adj a b → graph.Adj b c → ¬ graph.Adj c a := by
  decide +kernel

lemma no_four_cycles : ∀ a b c d : Fin 4,
    graph.Adj a b → graph.Adj b c → graph.Adj c d → graph.Adj d a → a = c ∨ b = d := by
  decide +kernel

lemma both_own : Owns 4 circuit 2 0 1 ∧ Owns 4 circuit 2 2 3 ∧
    Owns 4 circuit 5 0 1 ∧ Owns 4 circuit 5 2 3 := by
  decide +kernel

lemma no_common_center : ¬ ∃ c : Fin 4, (0 = c ∨ 1 = c) ∧ (2 = c ∨ 3 = c) := by
  decide +kernel

lemma not_star : ¬ HasStarProfile 4 graph circuit := by
  decide +kernel

lemma final_owns_none : ∀ u v : Fin 4, graph.Adj u v → ¬ Owns 4 circuit 6 u v := by
  decide +kernel

lemma dirty_witnesses : gateVal 4 circuit 2 (pairInput 0 3) = true ∧ ¬ graph.Adj 0 3 ∧
    gateVal 4 circuit 5 (pairInput 0 2) = true ∧ ¬ graph.Adj 0 2 := by
  decide +kernel

lemma final_sound : ∀ x : Fin 4 → Bool,
    gateVal 4 circuit 6 x = true → (x 0 && x 1) || (x 2 && x 3) = true := by
  decide +kernel

lemma every_gate_essential : ∀ t : Fin 7,
    gateVal 4 circuit t (pairInput 0 1) = true ∧
      circuitFun 4 (PEqualNP.CircuitMoves.eraseGate 4 circuit t 11) (pairInput 0 1) = false := by
  decide +kernel

lemma no_earlier_bypass : ∀ t : Fin 7, ∀ r : Fin (4 + t.val), ∃ x : Fin 4 → Bool,
    circuitFun 4 (PEqualNP.CircuitMoves.eraseGate 4 circuit t r) x ≠ circuitFun 4 circuit x := by
  decide +kernel

lemma cheaper : direct.size < circuit.size ∧
    ∀ x : Fin 4 → Bool, circuitFun 4 direct x = circuitFun 4 circuit x := by
  decide +kernel

end PEqualNP.Outside.L_meta_1031_aux.TwoDirty

namespace PEqualNP.Outside.L_meta_1031.PairThreeCNF

lemma disjoint_hits_bipartite {n : ℕ} (G : SimpleGraph (Fin n))
    (A B : Finset (Fin n)) (hd : Disjoint A B)
    (hA : ∀ u v, G.Adj u v → u ∈ A ∨ v ∈ A)
    (hB : ∀ u v, G.Adj u v → u ∈ B ∨ v ∈ B) :
    ∃ s : Fin n → Bool, ∀ u v, G.Adj u v → s u ≠ s v := by
  classical
  refine ⟨fun v => decide (v ∈ A), ?_⟩
  intro u v huv
  rcases hA u v huv with hu | hv <;> rcases hB u v huv with hu' | hv'
  · exact (Finset.disjoint_left.mp hd hu hu').elim
  · have hn : v ∉ A := fun h => Finset.disjoint_left.mp hd h hv'
    simp [hu, hn]
  · have hn : u ∉ A := fun h => Finset.disjoint_left.mp hd h hu'
    simp [hv, hn]
  · exact (Finset.disjoint_left.mp hd hv hv').elim

lemma three_clause_disjoint {n : ℕ} (G : SimpleGraph (Fin n))
    (A B C : Finset (Fin n))
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hpair : ∀ u v, (u ∈ A ∨ v ∈ A) → (u ∈ B ∨ v ∈ B) →
      (u ∈ C ∨ v ∈ C) → G.Adj u v) :
    Disjoint A B ∨ Disjoint A C ∨ Disjoint B C := by
  classical
  by_contra h
  push Not at h
  obtain ⟨a, haA, haB⟩ := Finset.not_disjoint_iff.mp h.1
  obtain ⟨b, hbA, hbC⟩ := Finset.not_disjoint_iff.mp h.2.1
  obtain ⟨c, hcB, hcC⟩ := Finset.not_disjoint_iff.mp h.2.2
  exact htri a b c
    (hpair a b (Or.inl haA) (Or.inl haB) (Or.inr hbC))
    (hpair b c (Or.inl hbA) (Or.inr hcB) (Or.inl hbC))
    (hpair c a (Or.inr haA) (Or.inl hcB) (Or.inl hcC))

lemma three_clause_bipartite {n : ℕ} (G : SimpleGraph (Fin n))
    (A B C : Finset (Fin n))
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hrep : ∀ u v, G.Adj u v ↔
      (u ∈ A ∨ v ∈ A) ∧ (u ∈ B ∨ v ∈ B) ∧ (u ∈ C ∨ v ∈ C)) :
    ∃ s : Fin n → Bool, ∀ u v, G.Adj u v → s u ≠ s v := by
  have hdis := three_clause_disjoint G A B C htri
    (fun u v ha hb hc => (hrep u v).mpr ⟨ha, hb, hc⟩)
  rcases hdis with hAB | hAC | hBC
  · exact disjoint_hits_bipartite G A B hAB
      (fun u v h => ((hrep u v).mp h).1)
      (fun u v h => ((hrep u v).mp h).2.1)
  · exact disjoint_hits_bipartite G A C hAC
      (fun u v h => ((hrep u v).mp h).1)
      (fun u v h => ((hrep u v).mp h).2.2)
  · exact disjoint_hits_bipartite G B C hBC
      (fun u v h => ((hrep u v).mp h).2.1)
      (fun u v h => ((hrep u v).mp h).2.2)

lemma disjoint_three_clause_cover {n : ℕ} (G : SimpleGraph (Fin n))
    (A B C : Finset (Fin n)) (hd : Disjoint A B)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d →
      G.Adj d a → a = c ∨ b = d)
    (hrep : ∀ u v, G.Adj u v ↔
      (u ∈ A ∨ v ∈ A) ∧ (u ∈ B ∨ v ∈ B) ∧ (u ∈ C ∨ v ∈ C)) :
    ∃ T : Finset (Fin n), T.card ≤ 2 ∧ ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T := by
  classical
  by_cases hA : A.card ≤ 1
  · exact ⟨A, by omega, fun u v h => ((hrep u v).mp h).1⟩
  by_cases hB : B.card ≤ 1
  · exact ⟨B, by omega, fun u v h => ((hrep u v).mp h).2.1⟩
  obtain ⟨a, ha, a', ha', haa'⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
  obtain ⟨b, hb, b', hb', hbb'⟩ := Finset.one_lt_card.mp (by omega : 1 < B.card)
  have hAC : (A ∩ C).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    obtain ⟨huA, huC⟩ := Finset.mem_inter.mp hu
    obtain ⟨hvA, hvC⟩ := Finset.mem_inter.mp hv
    apply Or.resolve_right (hfour u b v b' ?_ ?_ ?_ ?_) hbb'
    · exact (hrep u b).mpr ⟨Or.inl huA, Or.inr hb, Or.inl huC⟩
    · exact (hrep b v).mpr ⟨Or.inr hvA, Or.inl hb, Or.inr hvC⟩
    · exact (hrep v b').mpr ⟨Or.inl hvA, Or.inr hb', Or.inl hvC⟩
    · exact (hrep b' u).mpr ⟨Or.inr huA, Or.inl hb', Or.inr huC⟩
  have hBC : (B ∩ C).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro u hu v hv
    obtain ⟨huB, huC⟩ := Finset.mem_inter.mp hu
    obtain ⟨hvB, hvC⟩ := Finset.mem_inter.mp hv
    apply Or.resolve_right (hfour u a v a' ?_ ?_ ?_ ?_) haa'
    · exact (hrep u a).mpr ⟨Or.inr ha, Or.inl huB, Or.inl huC⟩
    · exact (hrep a v).mpr ⟨Or.inl ha, Or.inr hvB, Or.inr hvC⟩
    · exact (hrep v a').mpr ⟨Or.inr ha', Or.inl hvB, Or.inl hvC⟩
    · exact (hrep a' u).mpr ⟨Or.inl ha', Or.inr huB, Or.inr huC⟩
  refine ⟨(A ∩ C) ∪ (B ∩ C), ?_, ?_⟩
  · have := Finset.card_union_le (A ∩ C) (B ∩ C)
    omega
  · intro u v huv
    have h := (hrep u v).mp huv
    have hnu : ¬ (u ∈ A ∧ u ∈ B) := fun h => Finset.disjoint_left.mp hd h.1 h.2
    have hnv : ¬ (v ∈ A ∧ v ∈ B) := fun h => Finset.disjoint_left.mp hd h.1 h.2
    simp only [Finset.mem_union, Finset.mem_inter]
    tauto

lemma three_clause_cover {n : ℕ} (G : SimpleGraph (Fin n))
    (A B C : Finset (Fin n))
    (htri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (hfour : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d →
      G.Adj d a → a = c ∨ b = d)
    (hrep : ∀ u v, G.Adj u v ↔
      (u ∈ A ∨ v ∈ A) ∧ (u ∈ B ∨ v ∈ B) ∧ (u ∈ C ∨ v ∈ C)) :
    ∃ T : Finset (Fin n), T.card ≤ 2 ∧ ∀ u v, G.Adj u v → u ∈ T ∨ v ∈ T := by
  have hdis := three_clause_disjoint G A B C htri
    (fun u v ha hb hc => (hrep u v).mpr ⟨ha, hb, hc⟩)
  rcases hdis with hAB | hAC | hBC
  · exact disjoint_three_clause_cover G A B C hAB hfour hrep
  · apply disjoint_three_clause_cover G A C B hAC hfour
    intro u v
    rw [hrep]
    tauto
  · apply disjoint_three_clause_cover G B C A hBC hfour
    intro u v
    rw [hrep]
    tauto

end PEqualNP.Outside.L_meta_1031.PairThreeCNF

namespace PEqualNP.Outside.L_meta_1031_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.EdgeOwnership
open PEqualNP.MetaComplexity.NestedCover

lemma pair_owned_before {n : ℕ} (C : Circuit) (j : ℕ)
    (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and)
    (u v : Fin n) (hv : gateVal n C j (pairInput u v) = true) :
    ∃ k, k ≤ j ∧ Owns n C k u v := by
  classical
  have hex : ∃ k, k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧
      gateVal n C k (pairInput u v) = true := ⟨j, hj, hop, hv⟩
  let k := Nat.find hex
  obtain ⟨hk, hkop, hkv⟩ := Nat.find_spec hex
  refine ⟨k, Nat.find_min' hex ⟨hj, hop, hv⟩, hk, hkop, hkv, ?_⟩
  intro i hik _ hio
  cases hi : gateVal n C i (pairInput u v) with
  | false => rfl
  | true =>
    have hn := Nat.find_min hex hik
    exact False.elim (hn ⟨hik.trans hk, hio, hi⟩)

lemma owned_pairs_sound_global {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    (C : Circuit) (hC : Monotone2 C)
    (howned : ∀ j u v, Owns n C j u v → G.Adj u v) :
    ∀ j, j < C.gates.length → (gateAt C j).op = GateOp.and →
      ∀ x : Fin n → Bool, gateVal n C j x = true →
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  apply pair_sound_global hn G C hC
  intro j hj hop u v hv
  obtain ⟨k, _, hk⟩ := pair_owned_before C j hj hop u v hv
  exact howned k u v hk

lemma unsound_owned_nonedge {n : ℕ} (hn : 0 < n) (G : SimpleGraph (Fin n))
    (C : Circuit) (hC : Monotone2 C)
    (hbad : ∃ j, j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      ∃ x : Fin n → Bool, gateVal n C j x = true ∧
        ¬ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) :
    ∃ j u v, Owns n C j u v ∧ ¬ G.Adj u v := by
  classical
  by_contra h
  have ho : ∀ j u v, Owns n C j u v → G.Adj u v := by
    intro j u v hj
    by_contra huv
    exact h ⟨j, u, v, hj, huv⟩
  obtain ⟨j, hj, hop, x, hx, hneg⟩ := hbad
  exact hneg (owned_pairs_sound_global hn G C hC ho j hj hop x hx)

end PEqualNP.Outside.L_meta_1031_aux
