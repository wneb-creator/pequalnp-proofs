import PEqualNP.Defs
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Finite

-- Partial results for L-meta-1031.
-- The full posted theorem remains unproved.

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

namespace PEqualNP.Outside.L_meta_1031.ForestAux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

theorem final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem shannon (k : ℕ) : ∀ (f : (Fin k → Bool) → Bool) (m : ℕ), k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 4 ≤ 5 * 2 ^ k ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = f (fun i : Fin k => w.getD i false) := by
  induction k with
  | zero =>
    intro f m _
    refine ⟨[⟨if f (fun i => i.elim0) = true then GateOp.and else GateOp.or, []⟩], m, ?_, by simp,
      by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      by_cases h : f (fun i => i.elim0) = true <;> simp [h]
    · intro w hw
      have hf : (fun i : Fin 0 => w.getD i false) = (fun i => i.elim0) := Subsingleton.elim _ _
      rw [hf]
      by_cases h : f (fun i => i.elim0) = true <;>
        simp [wiresFrom, h, ← hw, GateOp.eval]
  | succ k ih =>
    intro f m hm
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ :=
      ih (fun y => f (Fin.snoc y false)) m (by omega)
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ :=
      ih (fun y => f (Fin.snoc y true)) (m + gs0.length) (by omega)
    let M := m + gs0.length + gs1.length
    refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [M, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | hg) | hg | hg | hg | hg
      · exact ok0 g hg
      · exact ok1 g hg
      all_goals (subst hg; simp [Ok])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [pow_succ]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom gs0 w with hw1
      set w2 := wiresFrom gs1 w1 with hw2
      have l1 : w1.length = m + gs0.length := by rw [hw1, length_wiresFrom, hw]
      have l2 : w2.length = M := by rw [hw2, length_wiresFrom, l1]
      have e0 : w2.getD o0 false = f (Fin.snoc (fun i : Fin k => w.getD i false) false) := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega)]; exact ev0 w hw
      have e1 : w2.getD o1 false = f (Fin.snoc (fun i : Fin k => w.getD i false) true) := by
        rw [ev1 w1 l1]
        congr 2; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have ek : w2.getD k false = w.getD k false := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega), hw1, getD_wiresFrom _ _ _ (by omega)]
      have hx : (fun i : Fin (k + 1) => w.getD i false)
          = Fin.snoc (fun i : Fin k => w.getD i false) (w.getD k false) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hx]
      have hk2 : k < w2.length := by omega
      have h02 : o0 < w2.length := by omega
      have h12 : o1 < w2.length := by omega
      rw [show M = w2.length from l2.symm, final_gates w2 k o0 o1 hk2 h02 h12, ek, e0, e1]
      cases w.getD k false <;> simp

end PEqualNP.Outside.L_meta_1031.ForestAux

namespace PEqualNP.Outside.L_meta_1031.ForestAux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

variable {n : ℕ}

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega

end PEqualNP.Outside.L_meta_1031.ForestAux

namespace PEqualNP.Outside.L_meta_1031.ForestAux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat := Bool ⊕ ℕ

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => (Sum.inr i.val : Stat)) ++ [Sum.inl b]

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr i.val : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Sum.inl false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

end PEqualNP.Outside.L_meta_1031.ForestAux

namespace PEqualNP.Outside.L_meta_1031.ForestAux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Sum.inl b ∈ ins) : ∃ c, (simplify op m ins).2 = Sum.inl c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Sum.inl false) = Sum.inl c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
  rw [hnone]; simp

def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false

theorem elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Sum.inl false) = Sum.inl (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Sum.inl false) = Sum.inl c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Sum.inl false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩

theorem suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]

theorem length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

theorem supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Sum.inl false) ≠ Sum.inl c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Sum.inl false) = Sum.inl b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Sum.inl false)
      = Sum.inl b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1

theorem gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      ((elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) ≠ Sum.inl c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Sum.inl false) with
  | inl c => exact absurd hst (hout b c)
  | inr j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this

def par (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)

theorem par_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    par (n + 1) (Fin.snoc y b) = xor (par n y) b := by
  unfold par
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  generalize (∑ i : Fin n, if y i = true then 1 else 0) = S
  have h := Nat.mod_two_eq_zero_or_one S
  cases b <;> rcases h with h | h <;> simp [Nat.add_mod, h]

theorem par_lower : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s →
      2 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    have hdep : ∃ x : Fin (n + 1 + 1) → Bool,
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c)
          (Function.update x (Fin.last (n + 1)) (!x (Fin.last (n + 1))))
        ≠ (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) x := by
      refine ⟨Fin.snoc (fun _ => false) false, ?_⟩
      simp only [Fin.snoc_last, Fin.update_snoc_last, par_snoc]
      simp
    have hnc : ∀ b : Bool, ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y b)
        ≠ (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y' b) := by
      intro b
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    obtain ⟨b, s', hs, h'⟩ := gate_elim_two (n + 1) _ s hdep hnc h
    have e : (fun y : Fin (n + 1) → Bool =>
          (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y b))
        = fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) (xor b c) := by
      funext y
      show xor (par (n + 1 + 1) (Fin.snoc y b)) c = _
      rw [par_snoc]
      cases par (n + 1) y <;> cases b <;> cases c <;> rfl
    rw [e] at h'
    have := ih _ _ h'
    omega

theorem parity_lower : ∀ (n s : ℕ),
    HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    2 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have := par_lower n false s h'
    omega

end PEqualNP.Outside.L_meta_1031.ForestAux

namespace PEqualNP.Outside.L_meta_1031.ForestAux.PermInputs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

theorem dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : T.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
  omega

theorem snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]

theorem gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := gate_elim_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

theorem fix_many {N : ℕ} (T : Finset (Fin N)) (hT : T.Nonempty) :
    ∀ (L : List (Fin N)) (f : (Fin N → Bool) → Bool), L.Nodup → (∀ p ∈ L, p ∉ T) →
    (∀ (a : Fin N → Bool) (pre post : List (Fin N)) (p : Fin N), L = pre ++ p :: post →
      ∃ x : Fin N → Bool, (∀ q ∈ pre, x q = a q) ∧ f (Function.update x p (!x p)) ≠ f x) →
    (∀ (a : Fin N → Bool), ∀ i ∈ T, ∃ x : Fin N → Bool, (∀ q ∈ L, x q = a q) ∧
      f (Function.update x i (!x i)) ≠ f x) →
    ∀ s : ℕ, HasCircuitSize N f s → T.card + 2 * L.length ≤ s + 1 := by
  obtain ⟨i0, hi0⟩ := hT
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := i0.2; omega⟩
  intro L
  induction L with
  | nil =>
    intro f _ _ _ hC s h
    have := dep_lower_set (n + 1) f T (fun i hi => by
      obtain ⟨x, _, hx⟩ := hC (fun _ => false) i hi
      exact ⟨x, hx⟩) s h
    simpa using this
  | cons p L ih =>
    intro f hnd hdis hA hC s h
    have hpL : p ∉ L := (List.nodup_cons.1 hnd).1
    have hpT : p ∉ T := hdis p List.mem_cons_self
    have hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x := by
      obtain ⟨x, _, hx⟩ := hA (fun _ => false) [] L p rfl
      exact ⟨x, hx⟩
    have hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
        f (Function.update x p b) ≠ f (Function.update y p b) := by
      intro b
      obtain ⟨x, hxa, hx⟩ := hC (fun _ => b) i0 hi0
      have hxp : x p = b := hxa p List.mem_cons_self
      have hi0p : i0 ≠ p := fun e => hpT (e ▸ hi0)
      refine ⟨Function.update x i0 (!x i0), x, ?_⟩
      have e1 : Function.update (Function.update x i0 (!x i0)) p b
          = Function.update x i0 (!x i0) :=
        Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hi0p), hxp])
      have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
      rw [e1, e2]
      exact hx
    obtain ⟨b, s', hs, h'⟩ := gate_elim_at n f p s hdep hnc h
    have := ih (fun x => f (Function.update x p b)) (List.nodup_cons.1 hnd).2
      (fun q hq => hdis q (List.mem_cons_of_mem _ hq)) ?_ ?_ s' h'
    · simp only [List.length_cons]; omega
    · intro a pre post p' hL
      obtain ⟨x, hxa, hx⟩ := hA (Function.update a p b) (p :: pre) post p' (by rw [hL]; rfl)
      have hxp : x p = b := by
        rw [hxa p List.mem_cons_self, Function.update_self]
      have hp' : p' ≠ p := by
        intro e; apply hpL; rw [← e, hL]; simp
      refine ⟨x, fun q hq => ?_, ?_⟩
      · have hqp : q ≠ p := by
          intro e; apply hpL; rw [← e, hL]; simp [hq]
        rw [hxa q (List.mem_cons_of_mem _ hq), Function.update_of_ne hqp]
      · have e1 : Function.update (Function.update x p' (!x p')) p b
            = Function.update x p' (!x p') :=
          Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hp'), hxp])
        have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
        show f _ ≠ f _
        rw [e1, e2]
        exact hx
    · intro a i hi
      obtain ⟨x, hxa, hx⟩ := hC (Function.update a p b) i hi
      have hxp : x p = b := by
        rw [hxa p List.mem_cons_self, Function.update_self]
      have hip : i ≠ p := fun e => hpT (e ▸ hi)
      refine ⟨x, fun q hq => ?_, ?_⟩
      · have hqp : q ≠ p := fun e => hpL (e ▸ hq)
        rw [hxa q (List.mem_cons_of_mem _ hq), Function.update_of_ne hqp]
      · have e1 : Function.update (Function.update x i (!x i)) p b
            = Function.update x i (!x i) :=
          Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hip), hxp])
        have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
        show f _ ≠ f _
        rw [e1, e2]
        exact hx

end PEqualNP.Outside.L_meta_1031.ForestAux.PermInputs

namespace PEqualNP.Outside.L_meta_1031.ForestAux.Forest

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1031.ForestAux.PermInputs

theorem one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool)
    (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) (s + 1) := relabel_size (⇑σ) f _ h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  have h' := PEqualNP.Outside.L_meta_1031.ForestAux.gate_elim n _ b s hdep' hnc' hg
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''

end PEqualNP.Outside.L_meta_1031.ForestAux.Forest

namespace PEqualNP.Outside.L_meta_1031.ForestAux.Forest

open SimpleGraph

theorem exists_longest_path {V : Type*} [Fintype V] (G : SimpleGraph V) [Nonempty V] :
    ∃ (a b : V) (P : G.Walk a b), P.IsPath ∧
      ∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P.length := by
  by_contra hno
  push_neg at hno
  have hk : ∀ k : ℕ, ∃ (a b : V) (P : G.Walk a b), P.IsPath ∧ k ≤ P.length := by
    intro k
    induction k with
    | zero =>
      obtain ⟨v⟩ := ‹Nonempty V›
      exact ⟨v, v, Walk.nil, Walk.IsPath.nil, le_refl _⟩
    | succ k ih =>
      obtain ⟨a, b, P, hP, hk⟩ := ih
      obtain ⟨c, d, Q, hQ, hlt⟩ := hno a b P hP
      exact ⟨c, d, Q, hQ, by omega⟩
  obtain ⟨a, b, P, hP, hle⟩ := hk (Fintype.card V)
  have := hP.length_lt
  omega

theorem forest_good_leaf {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (he : ∃ u v : V, G.Adj u v) :
    ∃ l p : V, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧
      ((∃ q : V, ∀ w, G.Adj p w → w = l ∨ w = q) ∨
        (∃ l' : V, l' ≠ l ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p)) := by
  classical
  obtain ⟨u0, v0, h0⟩ := he
  haveI : Nonempty V := ⟨u0⟩
  obtain ⟨l, z, P, hP, hmax⟩ := exists_longest_path G
  have h1 : 1 ≤ P.length := by
    have := hmax u0 v0 (Walk.cons h0 Walk.nil) (by simp [Walk.cons_isPath_iff, h0.ne])
    simpa using this
  cases P with
  | nil => simp at h1
  | @cons _ p _ hlp P' =>
    rw [Walk.cons_isPath_iff] at hP
    obtain ⟨hP', hlP'⟩ := hP
    have hmax' : ∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P'.length + 1 := by
      intro c d Q hQ
      have := hmax c d Q hQ
      simpa using this
    have hPfull : (Walk.cons hlp P').IsPath := (Walk.cons_isPath_iff _ _).2 ⟨hP', hlP'⟩
    have hleaf : ∀ w, G.Adj l w → w = p := by
      intro w hw
      by_cases hm : w ∈ (Walk.cons hlp P').support
      · have := hG.eq_snd_of_adj_start hPfull hw hm
        simpa using this
      · exfalso
        have hQ : (Walk.cons hw.symm (Walk.cons hlp P')).IsPath :=
          (Walk.cons_isPath_iff _ _).2 ⟨hPfull, hm⟩
        have := hmax' _ _ _ hQ
        simp at this
    refine ⟨l, p, hlp, hleaf, ?_⟩
    
    have hoff : ∀ w, G.Adj p w → w ∉ (Walk.cons hlp P').support →
        ∀ u, G.Adj w u → u = p := by
      intro w hw hwm u hu
      have hwP' : w ∉ P'.support := by
        intro h; exact hwm (by simp [h])
      have hQ : (Walk.cons hw.symm P').IsPath := (Walk.cons_isPath_iff _ _).2 ⟨hP', hwP'⟩
      by_cases hm : u ∈ (Walk.cons hw.symm P').support
      · have := hG.eq_snd_of_adj_start hQ hu hm
        simpa using this
      · exfalso
        have hQ2 : (Walk.cons hu.symm (Walk.cons hw.symm P')).IsPath :=
          (Walk.cons_isPath_iff _ _).2 ⟨hQ, hm⟩
        have := hmax' _ _ _ hQ2
        simp at this
    by_cases hex : ∃ l' : V, l' ≠ l ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p
    · exact Or.inr hex
    · left
      refine ⟨P'.snd, fun w hw => ?_⟩
      by_cases hwl : w = l
      · exact Or.inl hwl
      · right
        by_cases hm : w ∈ P'.support
        · exact hG.eq_snd_of_adj_start hP' hw hm
        · exfalso
          apply hex
          refine ⟨w, hwl, hw, hoff w hw ?_⟩
          simp [hwl, hm]

end PEqualNP.Outside.L_meta_1031.ForestAux.Forest

namespace PEqualNP.Outside.L_meta_1031.ForestAux.Forest

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1031.ForestAux.PermInputs
open SimpleGraph

noncomputable def F {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) :
    Bool :=
  @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)
    (Classical.propDecidable _)

theorem F_true {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) :
    F G A x = true ↔
      ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) := by
  unfold F
  exact @decide_eq_true_iff _ (Classical.propDecidable _)

theorem F_eq {n : ℕ} (G G' : SimpleGraph (Fin n)) (A A' : Finset (Fin n)) (x y : Fin n → Bool)
    (h : ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) ↔
      ((∃ a ∈ A', y a = true) ∨ ∃ i j : Fin n, G'.Adj i j ∧ y i = true ∧ y j = true)) :
    F G A x = F G' A' y := by
  rw [Bool.eq_iff_iff, F_true, F_true]
  exact h

theorem F_zero {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    F G A (fun _ => false) = false := by
  rw [Bool.eq_false_iff, ne_eq, F_true]
  simp

theorem F_nc {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (h : A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) :
    ∃ x y : Fin n → Bool, F G A x ≠ F G A y := by
  refine ⟨fun _ => true, fun _ => false, ?_⟩
  rw [F_zero]
  have : F G A (fun _ => true) = true := by
    rw [F_true]
    rcases h with ⟨a, ha⟩ | ⟨i, j, hij⟩
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨i, j, hij, rfl, rfl⟩
  rw [this]
  simp

theorem F_dep {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (u v : Fin n)
    (huv : G.Adj u v) (hv : v ∉ A) :
    ∃ x : Fin n → Bool, F G A (Function.update x u (!x u)) ≠ F G A x := by
  have hne : u ≠ v := huv.ne
  refine ⟨Function.update (fun _ => false) v true, ?_⟩
  have h1 : F G A (Function.update (Function.update (fun _ => false) v true) u
      (!(Function.update (fun _ => false) v true u))) = true := by
    rw [F_true]
    right
    refine ⟨u, v, huv, ?_, ?_⟩
    · simp [Function.update_of_ne hne]
    · simp [Function.update_of_ne hne.symm]
  have h2 : F G A (Function.update (fun _ => false) v true) = false := by
    rw [Bool.eq_false_iff, ne_eq, F_true]
    rintro (⟨a, ha, hx⟩ | ⟨i, j, hij, hi, hj⟩)
    · by_cases hav : a = v
      · exact hv (hav ▸ ha)
      · simp [Function.update_of_ne hav] at hx
    · have hiv : i = v := by
        by_contra h; simp [Function.update_of_ne h] at hi
      have hjv : j = v := by
        by_contra h; simp [Function.update_of_ne h] at hj
      exact hij.ne (hiv.trans hjv.symm)
  rw [h1, h2]
  simp

theorem F_dep_A {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a : Fin n)
    (ha : a ∈ A) :
    ∃ x : Fin n → Bool, F G A (Function.update x a (!x a)) ≠ F G A x := by
  refine ⟨fun _ => false, ?_⟩
  rw [F_zero]
  have : F G A (Function.update (fun _ => false) a (!false)) = true := by
    rw [F_true]
    exact Or.inl ⟨a, ha, by simp⟩
  rw [this]
  simp

theorem restrict_false {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p : Fin n)
    (hlA : l ∉ A) (hleaf : ∀ w, G.Adj l w → w = p) (x : Fin n → Bool) :
    F G A (Function.update x l false) = F (G.deleteEdges {s(l, p)}) A x := by
  apply F_eq
  apply or_congr
  · constructor
    · rintro ⟨a, ha, h⟩
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hal] at h⟩
    · rintro ⟨a, ha, h⟩
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hal]⟩
  · constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      have hil : i ≠ l := by rintro rfl; simp at hi
      have hjl : j ≠ l := by rintro rfl; simp at hj
      refine ⟨i, j, ?_, by rwa [Function.update_of_ne hil] at hi,
        by rwa [Function.update_of_ne hjl] at hj⟩
      rw [deleteEdges_adj]
      refine ⟨hij, ?_⟩
      simp [Sym2.eq_iff, hil, hjl]
    · rintro ⟨i, j, hij, hi, hj⟩
      rw [deleteEdges_adj] at hij
      obtain ⟨hij, hne⟩ := hij
      have hil : i ≠ l := by
        rintro rfl
        have := hleaf j hij
        subst this
        exact hne rfl
      have hjl : j ≠ l := by
        rintro rfl
        have := hleaf i hij.symm
        subst this
        exact hne (Sym2.eq_swap)
      exact ⟨i, j, hij, by rwa [Function.update_of_ne hil], by rwa [Function.update_of_ne hjl]⟩

theorem restrict_true {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p q : Fin n)
    (hlA : l ∉ A) (hlp : G.Adj l p) (hleaf : ∀ w, G.Adj l w → w = p)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q) (x : Fin n → Bool) :
    F G A (Function.update x l true) = F (G.deleteEdges {s(p, l), s(p, q)}) (insert p A) x := by
  have hpl : p ≠ l := hlp.ne.symm
  have hA : ∀ a ∈ A, Function.update x l true a = x a := fun a ha =>
    Function.update_of_ne (by rintro rfl; exact hlA ha) _ _
  
  have hG1 : ∀ i j, (G.deleteEdges {s(p, l), s(p, q)}).Adj i j → i ≠ p ∧ i ≠ l := by
    intro i j hij
    rw [deleteEdges_adj] at hij
    obtain ⟨hij, hne⟩ := hij
    constructor
    · rintro rfl
      rcases hp j hij with rfl | rfl
      · exact hne (by simp)
      · exact hne (by simp)
    · rintro rfl
      have := hleaf j hij
      subst this
      exact hne (by simp [Sym2.eq_swap])
  apply F_eq
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · exact Or.inl ⟨a, Finset.mem_insert_of_mem ha, by rwa [hA a ha] at h⟩
    · by_cases hip : i = p
      · subst hip
        exact Or.inl ⟨i, Finset.mem_insert_self _ _, by rwa [Function.update_of_ne hpl] at hi⟩
      by_cases hjp : j = p
      · subst hjp
        exact Or.inl ⟨j, Finset.mem_insert_self _ _, by rwa [Function.update_of_ne hpl] at hj⟩
      have hil : i ≠ l := by
        rintro rfl; exact hjp (hleaf j hij)
      have hjl : j ≠ l := by
        rintro rfl; exact hip (hleaf i hij.symm)
      right
      refine ⟨i, j, ?_, by rwa [Function.update_of_ne hil] at hi,
        by rwa [Function.update_of_ne hjl] at hj⟩
      rw [deleteEdges_adj]
      refine ⟨hij, ?_⟩
      simp [Sym2.eq_iff, hip, hjp]
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · rcases Finset.mem_insert.1 ha with rfl | ha
      · right
        exact ⟨l, a, hlp, by simp, by rwa [Function.update_of_ne hpl]⟩
      · exact Or.inl ⟨a, ha, by rwa [hA a ha]⟩
    · right
      have hi' := hG1 i j hij
      have hj' := hG1 j i hij.symm
      rw [deleteEdges_adj] at hij
      exact ⟨i, j, hij.1, by rwa [Function.update_of_ne hi'.2],
        by rwa [Function.update_of_ne hj'.2]⟩

def Cov {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T

theorem cov_insert {n : ℕ} (G : SimpleGraph (Fin n)) (S : Set (Sym2 (Fin n))) (p : Fin n)
    (hS : ∀ e ∈ S, p ∈ e) (T : Finset (Fin n)) (hT : Cov (G.deleteEdges S) T) :
    Cov G (insert p T) := by
  intro i j hij
  by_cases he : s(i, j) ∈ S
  · have := hS _ he
    rcases Sym2.mem_iff.1 this with rfl | rfl
    · exact Or.inl (Finset.mem_insert_self _ _)
    · exact Or.inr (Finset.mem_insert_self _ _)
  · rcases hT i j ((deleteEdges_adj).2 ⟨hij, he⟩) with h | h
    · exact Or.inl (Finset.mem_insert_of_mem h)
    · exact Or.inr (Finset.mem_insert_of_mem h)

theorem cov_swap {n : ℕ} (G : SimpleGraph (Fin n)) (l p l' : Fin n) (k : ℕ)
    (hll' : l' ≠ l) (hl'p : G.Adj p l') (hleaf' : ∀ w, G.Adj l' w → w = p)
    (hk : ∀ T, Cov G T → k ≤ T.card) (T : Finset (Fin n))
    (hT : Cov (G.deleteEdges {s(l, p)}) T) : k ≤ T.card := by
  have hS : ∀ e ∈ ({s(l, p)} : Set (Sym2 (Fin n))), p ∈ e := by
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst he
    exact Sym2.mem_mk_right _ _
  by_cases hpT : p ∈ T
  · have := hk _ (cov_insert G _ p hS T hT)
    rwa [Finset.insert_eq_of_mem hpT] at this
  · have hl'T : l' ∈ T := by
      have hpl' : p ≠ l' := hl'p.ne
      rcases hT p l' ((deleteEdges_adj).2 ⟨hl'p, by
          simp [Sym2.eq_iff, hll', hpl'.symm]⟩) with h | h
      · exact absurd h hpT
      · exact h
    have hcov : Cov G (insert p (T.erase l')) := by
      intro i j hij
      by_cases hip : i = p
      · exact Or.inl (hip ▸ Finset.mem_insert_self _ _)
      by_cases hjp : j = p
      · exact Or.inr (hjp ▸ Finset.mem_insert_self _ _)
      have h0 : (G.deleteEdges {s(l, p)}).Adj i j :=
        (deleteEdges_adj).2 ⟨hij, by simp [Sym2.eq_iff, hip, hjp]⟩
      rcases hT i j h0 with h | h
      · have hil' : i ≠ l' := by
          rintro rfl; exact hjp (hleaf' j hij)
        exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hil', h⟩))
      · have hjl' : j ≠ l' := by
          rintro rfl; exact hip (hleaf' i hij.symm)
        exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hjl', h⟩))
    have h1 := hk _ hcov
    have h2 := Finset.card_insert_le p (T.erase l')
    have h3 := Finset.card_erase_add_one hl'T
    omega

theorem ncard_del1 {n : ℕ} (G : SimpleGraph (Fin n)) (l p : Fin n) (h : G.Adj l p) :
    (G.deleteEdges {s(l, p)}).edgeSet.ncard + 1 = G.edgeSet.ncard := by
  rw [edgeSet_deleteEdges]
  exact Set.ncard_sdiff_singleton_add_one (G.mem_edgeSet.2 h)

theorem ncard_del2 {n : ℕ} (G : SimpleGraph (Fin n)) (l p q : Fin n) (h : G.Adj l p) :
    G.edgeSet.ncard ≤ (G.deleteEdges {s(p, l), s(p, q)}).edgeSet.ncard + 2 ∧
      (G.deleteEdges {s(p, l), s(p, q)}).edgeSet.ncard < G.edgeSet.ncard := by
  rw [edgeSet_deleteEdges]
  constructor
  · have h1 := Set.ncard_le_ncard_sdiff_add_ncard G.edgeSet ({s(p, l), s(p, q)} : Set (Sym2 (Fin n)))
    have h2 := Set.ncard_insert_le (s(p, l)) ({s(p, q)} : Set (Sym2 (Fin n)))
    rw [Set.ncard_singleton] at h2
    omega
  · have hmem : s(l, p) ∈ G.edgeSet := G.mem_edgeSet.2 h
    have hsub : G.edgeSet \ {s(p, l), s(p, q)} ⊆ G.edgeSet \ {s(l, p)} := by
      intro e he
      refine ⟨he.1, ?_⟩
      intro he'
      apply he.2
      rw [Set.mem_singleton_iff] at he'
      rw [he', Sym2.eq_swap]
      exact Set.mem_insert _ _
    have h1 := Set.ncard_le_ncard hsub
    have h2 := Set.ncard_sdiff_singleton_lt_of_mem hmem
    omega

theorem noedge_ncard {n : ℕ} (G : SimpleGraph (Fin n)) (h : ∀ i j, ¬ G.Adj i j) :
    G.edgeSet.ncard = 0 := by
  have : G.edgeSet = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro e
    induction e using Sym2.ind with
    | _ i j => exact fun he => h i j (G.mem_edgeSet.1 he)
  rw [this, Set.ncard_empty]

theorem del_p_adj {n : ℕ} (G : SimpleGraph (Fin n)) (l p q : Fin n)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q) (i j : Fin n)
    (hij : (G.deleteEdges {s(p, l), s(p, q)}).Adj i j) : i ≠ p := by
  rw [deleteEdges_adj] at hij
  obtain ⟨hij, hne⟩ := hij
  rintro rfl
  rcases hp j hij with rfl | rfl
  · exact hne (by simp)
  · exact hne (by simp)

theorem claimQ : ∀ (m n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (k s : ℕ),
    G.edgeSet.ncard = m → G.IsAcyclic → (∀ i j, G.Adj i j → i ∉ A) →
    (∀ T, Cov G T → k ≤ T.card) → (A.Nonempty ∨ ∃ i j, G.Adj i j) →
    HasCircuitSize n (F G A) s → A.card + m + k ≤ s + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro n G A k s hm hac hinv hk hne hC
  by_cases hE : ∃ i j, G.Adj i j
  swap
  · push_neg at hE
    have hk0 : k ≤ (∅ : Finset (Fin n)).card := hk ∅ (fun i j h => absurd h (hE i j))
    have hm0 : m = 0 := by rw [← hm]; exact noedge_ncard G hE
    have := dep_lower_set n (F G A) A (fun a ha => F_dep_A G A a ha) s hC
    simp at hk0
    omega
  obtain ⟨l, p, hlp, hleaf, hcase⟩ := forest_good_leaf G hac hE
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := l.2; omega⟩
  have hlA : l ∉ A := hinv l p hlp
  have hpA : p ∉ A := hinv p l hlp.symm
  have hdepl := F_dep G A l p hlp hpA
  have hdepp := F_dep G A p l hlp.symm hlA
  have hs1 : 2 ≤ s + 1 := by
    have := dep_lower_set _ (F G A) {l, p} (by
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hdepl
      · rw [Finset.mem_singleton] at hi
        subst hi
        exact hdepp) s hC
    rwa [Finset.card_pair hlp.ne] at this
  set G0 := G.deleteEdges {s(l, p)} with hG0
  have hm0 : G0.edgeSet.ncard + 1 = m := by rw [← hm]; exact ncard_del1 G l p hlp
  have hac0 : G0.IsAcyclic := hac.anti (deleteEdges_le _)
  have hinv0 : ∀ i j, G0.Adj i j → i ∉ A := fun i j h => hinv i j ((deleteEdges_adj).1 h).1
  have hS0 : ∀ e ∈ ({s(l, p)} : Set (Sym2 (Fin (n' + 1)))), p ∈ e := by
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst he
    exact Sym2.mem_mk_right _ _
  have hrf : (fun x => F G A (Function.update x l false)) = F G0 A :=
    funext (restrict_false G A l p hlA hleaf)
  rcases hcase with ⟨q, hq⟩ | ⟨l', hl'l, hpl', hleaf'⟩
  · set G1 := G.deleteEdges {s(p, l), s(p, q)} with hG1
    by_cases h0 : A.Nonempty ∨ ∃ i j, G0.Adj i j
    · have hrt : (fun x => F G A (Function.update x l true)) = F G1 (insert p A) :=
        funext (restrict_true G A l p q hlA hlp hleaf hq)
      have hnc : ∀ b : Bool, ∃ x y : Fin (n' + 1) → Bool,
          F G A (Function.update x l b) ≠ F G A (Function.update y l b) := by
        intro b
        cases b
        · obtain ⟨x, y, hxy⟩ := F_nc G0 A h0
          refine ⟨x, y, ?_⟩
          have e1 := congrFun hrf x
          have e2 := congrFun hrf y
          rw [e1, e2]; exact hxy
        · obtain ⟨x, y, hxy⟩ := F_nc G1 (insert p A) (Or.inl (Finset.insert_nonempty _ _))
          refine ⟨x, y, ?_⟩
          have e1 := congrFun hrt x
          have e2 := congrFun hrt y
          rw [e1, e2]; exact hxy
      obtain ⟨b, s', hs', hC'⟩ := gate_elim_at n' (F G A) l s hdepl hnc hC
      cases b
      · rw [hrf] at hC'
        have hk0 : ∀ T, Cov G0 T → k - 1 ≤ T.card := fun T hT => by
          have := hk _ (cov_insert G _ p hS0 T hT)
          have := Finset.card_insert_le p T
          omega
        have := ih G0.edgeSet.ncard (by omega) _ G0 A (k - 1) s' rfl hac0 hinv0 hk0 h0 hC'
        omega
      · rw [hrt] at hC'
        have hS1 : ∀ e ∈ ({s(p, l), s(p, q)} : Set (Sym2 (Fin (n' + 1)))), p ∈ e := by
          intro e he
          rcases he with rfl | he
          · exact Sym2.mem_mk_left _ _
          · rw [Set.mem_singleton_iff] at he
            subst he
            exact Sym2.mem_mk_left _ _
        have hk1 : ∀ T, Cov G1 T → k - 1 ≤ T.card := fun T hT => by
          have := hk _ (cov_insert G _ p hS1 T hT)
          have := Finset.card_insert_le p T
          omega
        have hac1 : G1.IsAcyclic := hac.anti (deleteEdges_le _)
        have hinv1 : ∀ i j, G1.Adj i j → i ∉ insert p A := by
          intro i j h hi
          rcases Finset.mem_insert.1 hi with heq | hi
          · exact del_p_adj G l p q hq i j h heq
          · exact hinv i j ((deleteEdges_adj).1 h).1 hi
        obtain ⟨hc1, hc2⟩ := ncard_del2 G l p q hlp
        rw [← hG1] at hc1 hc2
        have := ih G1.edgeSet.ncard (by omega) _ G1 (insert p A) (k - 1) s' rfl hac1 hinv1
          hk1 (Or.inl (Finset.insert_nonempty _ _)) hC'
        rw [Finset.card_insert_of_notMem hpA] at this
        omega
    · push_neg at h0
      obtain ⟨hA0, hG00⟩ := h0
      have hm1 : m = 1 := by
        have := noedge_ncard G0 hG00
        omega
      have hk1 : k ≤ ({p} : Finset (Fin (n' + 1))).card := by
        apply hk
        intro i j hij
        have h1 := hG00 i j
        rw [deleteEdges_adj] at h1
        push_neg at h1
        have h2 := h1 hij
        rw [Set.mem_singleton_iff, Sym2.eq_iff] at h2
        rcases h2 with ⟨_, rfl⟩ | ⟨rfl, _⟩
        · exact Or.inr (Finset.mem_singleton_self _)
        · exact Or.inl (Finset.mem_singleton_self _)
      rw [Finset.card_singleton] at hk1
      subst hA0
      simp only [Finset.card_empty]
      omega
  · obtain ⟨s0, rfl⟩ : ∃ s0, s = s0 + 1 := ⟨s - 1, by omega⟩
    have hpl'0 : G0.Adj p l' := (deleteEdges_adj).2 ⟨hpl', by
      simp [Sym2.eq_iff, hl'l, hpl'.ne.symm]⟩
    have hnc0 : ∃ x y : Fin (n' + 1) → Bool,
        F G A (Function.update x l false) ≠ F G A (Function.update y l false) := by
      obtain ⟨x, y, hxy⟩ := F_nc G0 A (Or.inr ⟨p, l', hpl'0⟩)
      refine ⟨x, y, ?_⟩
      have e1 := congrFun hrf x
      have e2 := congrFun hrf y
      rw [e1, e2]; exact hxy
    have hC' := one_gate_at n' (F G A) l false s0 hdepl hnc0 hC
    rw [hrf] at hC'
    have hk0 : ∀ T, Cov G0 T → k ≤ T.card := cov_swap G l p l' k hl'l hpl' hleaf' hk
    have := ih G0.edgeSet.ncard (by omega) _ G0 A k s0 rfl hac0 hinv0 hk0
      (Or.inr ⟨p, l', hpl'0⟩) hC'
    omega

theorem forest_bound : ∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.IsAcyclic → (∃ i j : Fin n, G.Adj i j) →
    (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) →
    HasCircuitSize n
      (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) s →
    G.edgeFinset.card + k ≤ s + 1 := by
  intro n k s G _ hac hE hk hC
  have hf : (fun x : Fin n → Bool =>
      decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) = F G ∅ := by
    funext x
    rw [Bool.eq_iff_iff, F_true, decide_eq_true_iff]
    simp
  rw [hf] at hC
  have := claimQ _ n G ∅ k s rfl hac (by simp) (fun T hT => hk T hT) (Or.inr hE) hC
  have he : G.edgeFinset.card = G.edgeSet.ncard := by
    rw [← Set.ncard_coe_finset, coe_edgeFinset]
  rw [Finset.card_empty] at this
  omega

end PEqualNP.Outside.L_meta_1031.ForestAux.Forest

namespace PEqualNP.Outside.L_meta_1031.ForestCover

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

def V {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) : List Bool :=
  List.ofFn x ++ fs.map (fun f => f x)

def Sem {n : ℕ} (gs : List Gate) (fs : List ((Fin n → Bool) → Bool)) : Prop :=
  ∀ x : Fin n → Bool, wf gs (List.ofFn x) = V fs x

def Val {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (i : ℕ) (F : (Fin n → Bool) → Bool) : Prop :=
  i < n + fs.length ∧ ∀ x, (V fs x).getD i false = F x

theorem V_append {n : ℕ} (fs fs' : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) :
    V (fs ++ fs') x = V fs x ++ fs'.map (fun f => f x) := by
  simp [V]

theorem V_length {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) :
    (V fs x).length = n + fs.length := by simp [V]

theorem V_read {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) (j : ℕ)
    (hj : j < fs.length) : (V fs x).getD (n + j) false = fs.getD j (fun _ => false) x := by
  simp only [V]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, hj]

theorem val_ext {n : ℕ} {fs : List ((Fin n → Bool) → Bool)} {i : ℕ} {F : (Fin n → Bool) → Bool}
    (h : Val fs i F) (fs' : List ((Fin n → Bool) → Bool)) : Val (fs ++ fs') i F := by
  refine ⟨by have := h.1; simp; omega, fun x => ?_⟩
  rw [V_append, List.getD_append _ _ _ _ (by rw [V_length]; exact h.1)]
  exact h.2 x

theorem val_congr {n : ℕ} {fs : List ((Fin n → Bool) → Bool)} {i : ℕ}
    {F F' : (Fin n → Bool) → Bool} (h : Val fs i F) (e : ∀ x, F x = F' x) : Val fs i F' :=
  ⟨h.1, fun x => by rw [h.2 x, e x]⟩

theorem val_in {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (a : Fin n) :
    Val fs a.val (fun x => x a) := by
  refine ⟨by omega, fun x => ?_⟩
  simp only [V]
  rw [List.getD_append _ _ _ _ (by simp)]
  simp

theorem val_new {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (f : (Fin n → Bool) → Bool) :
    Val (fs ++ [f]) (n + fs.length) f := by
  refine ⟨by simp, fun x => ?_⟩
  rw [V_read _ _ _ (by simp)]
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

theorem sem_snoc {n : ℕ} {gs : List Gate} {fs : List ((Fin n → Bool) → Bool)} (h : Sem gs fs)
    (op : GateOp) (a b : ℕ) (A B : (Fin n → Bool) → Bool) (ha : Val fs a A) (hb : Val fs b B) :
    Sem (gs ++ [⟨op, [a, b]⟩]) (fs ++ [fun x => op.eval [A x, B x]]) := by
  intro x
  rw [wf_snoc, h x, V_append]
  simp only [List.map_cons, List.map_nil, ha.2 x, hb.2 x]

def Mono (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def St {n : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Prop) (gs : List Gate)
    (fs : List ((Fin n → Bool) → Bool)) : Prop :=
  Sem gs fs ∧ fs.length = gs.length ∧ Mono gs ∧
  (∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
    ∃ l, P l ∧ ∀ x, fs.getD j (fun _ => false) x = true → x l = true) ∧
  (∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
    ∃ c v : Fin n, G.Adj c v ∧
      fs.getD j (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c v) = true ∧
      ∀ i < j, (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and →
        fs.getD i (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c v) = false)

theorem st_nil {n : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Prop) : St G P [] [] := by
  refine ⟨fun x => by simp [wf, V], rfl, by simp [Mono], ?_, ?_⟩ <;> simp

theorem st_weak {n : ℕ} {G : SimpleGraph (Fin n)} {P Q : Fin n → Prop} {gs fs}
    (h : St G P gs fs) (hPQ : ∀ l, P l → Q l) : St G Q gs fs := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨h1, h2, h3, fun j hj hand => ?_, h5⟩
  obtain ⟨l, hl, hl2⟩ := h4 j hj hand
  exact ⟨l, hPQ l hl, hl2⟩

theorem push {n : ℕ} {G : SimpleGraph (Fin n)} {P : Fin n → Prop} {gs : List Gate}
    {fs : List ((Fin n → Bool) → Bool)} (h : St G P gs fs) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (a b : ℕ) (A B : (Fin n → Bool) → Bool)
    (ha : Val fs a A) (hb : Val fs b B)
    (nA : op = GateOp.and → ∃ l, P l ∧ ∀ x, op.eval [A x, B x] = true → x l = true)
    (nB : op = GateOp.and → ∃ c v : Fin n, G.Adj c v ∧
      op.eval [A (PEqualNP.EdgeOwnership.pairInput c v), B (PEqualNP.EdgeOwnership.pairInput c v)]
        = true ∧
      ∀ i < gs.length, (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and →
        fs.getD i (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c v) = false) :
    St G P (gs ++ [⟨op, [a, b]⟩]) (fs ++ [fun x => op.eval [A x, B x]]) ∧
      Val (fs ++ [fun x => op.eval [A x, B x]]) (n + fs.length) (fun x => op.eval [A x, B x]) := by
  obtain ⟨hs, hl, hm, hA, hB⟩ := h
  refine ⟨⟨sem_snoc hs op a b A B ha hb, by simp [hl], ?_, ?_, ?_⟩, val_new _ _⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact hm g hg
    · simp only [List.mem_singleton] at hg
      subst hg
      rcases hop with e | e <;> simp [e]
  · intro j hj hand
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [List.getD_append _ _ _ _ hj] at hand
      obtain ⟨l, hl1, hl2⟩ := hA j hj hand
      refine ⟨l, hl1, fun x hx => hl2 x ?_⟩
      rwa [List.getD_append _ _ _ _ (by omega)] at hx
    · subst hj
      rw [List.getD_append_right _ _ _ _ le_rfl] at hand
      simp only [Nat.sub_self, List.getD_cons_zero] at hand
      obtain ⟨l, hl1, hl2⟩ := nA hand
      refine ⟨l, hl1, fun x hx => hl2 x ?_⟩
      rw [← hl, List.getD_append_right _ _ _ _ le_rfl] at hx
      simpa using hx
  · intro j hj hand
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [List.getD_append _ _ _ _ hj] at hand
      obtain ⟨c, v, hadj, h1, h2⟩ := hB j hj hand
      refine ⟨c, v, hadj, ?_, fun i hi hand' => ?_⟩
      · rw [List.getD_append _ _ _ _ (by omega)]; exact h1
      · rw [List.getD_append _ _ _ _ (by omega)] at hand'
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h2 i hi hand'
    · subst hj
      rw [List.getD_append_right _ _ _ _ le_rfl] at hand
      simp only [Nat.sub_self, List.getD_cons_zero] at hand
      obtain ⟨c, v, hadj, h1, h2⟩ := nB hand
      refine ⟨c, v, hadj, ?_, fun i hi hand' => ?_⟩
      · rw [← hl, List.getD_append_right _ _ _ _ le_rfl]
        simpa using h1
      · rw [List.getD_append _ _ _ _ hi] at hand'
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h2 i hi hand'

theorem chain {n : ℕ} {G : SimpleGraph (Fin n)} {P : Fin n → Prop} :
    ∀ (rest : List (Fin n)) (gs : List Gate) (fs : List ((Fin n → Bool) → Bool)) (a : ℕ)
      (A : (Fin n → Bool) → Bool), St G P gs fs → Val fs a A →
      ∃ gs' fs' o, St G P gs' fs' ∧ (∃ fsn, fs' = fs ++ fsn) ∧
        gs'.length = gs.length + rest.length ∧
        Val fs' o (fun x => A x || rest.any (fun w => x w))
  | [], gs, fs, a, A, h, ha => ⟨gs, fs, a, h, ⟨[], by simp⟩, by simp, by simpa using ha⟩
  | w :: rest, gs, fs, a, A, h, ha => by
    obtain ⟨h1, h2⟩ := push h GateOp.or (Or.inr rfl) a w.val A (fun x => x w) ha (val_in fs w)
      (fun e => by simp at e) (fun e => by simp at e)
    obtain ⟨gs', fs', o, h3, ⟨fsn, hfs⟩, hlen, hv⟩ := chain rest _ _ _ _ h1 h2
    refine ⟨gs', fs', o, h3, ⟨(fun x => GateOp.or.eval [A x, x w]) :: fsn, by rw [hfs]; simp⟩, ?_, ?_⟩
    · rw [hlen]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
    refine ⟨hv.1, fun x => ?_⟩
    rw [hv.2 x]
    simp [GateOp.eval, Bool.or_assoc]

def N {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) (c : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter (fun w => G.Adj c w ∧ ¬ (w ∈ C ∧ w < c))

def gad {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) (c : Fin n)
    (x : Fin n → Bool) : Bool :=
  x c && decide (∃ w ∈ N G C c, x w = true)

theorem gad_empty {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    {c : Fin n} (h : N G C c = ∅) (x : Fin n → Bool) : gad G C c x = false := by
  simp [gad, h]

theorem gadget {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    {P : Fin n → Prop} (c : Fin n) (hP : ∀ l, P l → l ∈ C ∧ l < c) (hne : (N G C c).Nonempty)
    (gs : List Gate) (fs : List ((Fin n → Bool) → Bool)) (h : St G P gs fs) :
    ∃ gs' fs' o, St G (fun l => P l ∨ l = c) gs' fs' ∧ (∃ fsn, fs' = fs ++ fsn) ∧
      gs'.length = gs.length + (N G C c).card ∧ Val fs' o (gad G C c) := by
  have hL : (N G C c).toList ≠ [] := by
    rw [Ne, Finset.toList_eq_nil]; exact hne.ne_empty
  obtain ⟨w0, rest, hL⟩ := List.exists_cons_of_ne_nil hL
  have hw0 : w0 ∈ N G C c := by
    rw [← Finset.mem_toList, hL]; exact List.mem_cons_self
  have hcard : (N G C c).card = rest.length + 1 := by
    rw [← Finset.length_toList, hL]; simp
  have key : ∀ x : Fin n → Bool,
      (x w0 || rest.any (fun w => x w)) = decide (∃ w ∈ N G C c, x w = true) := by
    intro x
    have : (x w0 || rest.any (fun w => x w)) = (N G C c).toList.any (fun w => x w) := by
      rw [hL]; simp
    rw [this, Bool.eq_iff_iff]
    simp [List.any_eq_true, Finset.mem_toList]
  obtain ⟨gs1, fs1, o1, h1, ⟨fsn, hfs⟩, hlen1, hv1⟩ :=
    chain rest gs fs w0.val (fun x => x w0) h (val_in fs w0)
  have hlab := h1.2.2.2.1
  have hl1 := h1.2.1
  obtain ⟨h2, hv2⟩ := push (st_weak (Q := fun l => P l ∨ l = c) h1 (fun l hl => Or.inl hl)) GateOp.and (Or.inl rfl) c.val o1
    (fun x => x c) _ (val_in fs1 c) hv1
    (fun _ => ⟨c, Or.inr rfl, fun x hx => by simp [GateOp.eval] at hx; exact hx.1⟩)
    (fun _ => ⟨c, w0, by
        simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hw0; exact hw0.1, by
        simp [GateOp.eval, PEqualNP.EdgeOwnership.pairInput], by
        intro i hi hand
        obtain ⟨l, hl, hl2⟩ := hlab i hi hand
        obtain ⟨hlC, hlc⟩ := hP l hl
        cases hval : fs1.getD i (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c w0) with
        | false => rfl
        | true =>
          exfalso
          have := hl2 _ hval
          simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at this
          rcases this with rfl | rfl
          · exact lt_irrefl _ hlc
          · simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hw0
            exact hw0.2 ⟨hlC, hlc⟩⟩)
  refine ⟨_, _, n + fs1.length, h2, ⟨fsn ++ [fun x => GateOp.and.eval [x c, x w0 || rest.any fun w => x w]], by rw [hfs]; simp⟩, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton, hlen1, hcard]; omega
  refine val_congr hv2 (fun x => ?_)
  simp only [GateOp.eval, gad, ← key x]
  simp

theorem build {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (S : Finset (Fin n)) : S ⊆ C →
    ∃ gs fs, St G (fun l => l ∈ S) gs fs ∧
      ((gs = [] ∧ ∀ c ∈ S, N G C c = ∅) ∨
       ∃ o, Val fs o (fun x => decide (∃ c ∈ S, gad G C c x = true)) ∧
         gs.length + 1 ≤ (∑ c ∈ S, (N G C c).card) + S.card) := by
  induction S using Finset.induction_on_max with
  | empty => intro _; exact ⟨[], [], st_nil G _, Or.inl ⟨rfl, by simp⟩⟩
  | insert c S hlt ih =>
    intro hsub
    have hcS : c ∉ S := fun hc => lt_irrefl _ (hlt c hc)
    obtain ⟨gs, fs, h, hcase⟩ := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
    have hP : ∀ l, l ∈ S → l ∈ C ∧ l < c :=
      fun l hl => ⟨hsub (Finset.mem_insert_of_mem hl), hlt l hl⟩
    by_cases hN : N G C c = ∅
    · refine ⟨gs, fs, st_weak h (fun l hl => Finset.mem_insert_of_mem hl), ?_⟩
      rcases hcase with ⟨hg, hall⟩ | ⟨o, hv, hlen⟩
      · left
        refine ⟨hg, ?_⟩
        intro c' hc'
        rcases Finset.mem_insert.1 hc' with rfl | hc'
        · exact hN
        · exact hall c' hc'
      · right
        refine ⟨o, val_congr hv ?_, ?_⟩
        · intro x
          simp [Finset.mem_insert, gad_empty hN]
        · rw [Finset.sum_insert hcS, Finset.card_insert_of_notMem hcS]; omega
    · have hne : (N G C c).Nonempty := Finset.nonempty_iff_ne_empty.2 hN
      obtain ⟨gs1, fs1, o1, h1, ⟨fsn, hfs⟩, hlen1, hv1⟩ := gadget c hP hne gs fs h
      have h1' : St G (fun l => l ∈ insert c S) gs1 fs1 := by
        refine st_weak h1 ?_
        intro l hl
        rcases hl with hl | rfl
        · exact Finset.mem_insert_of_mem hl
        · exact Finset.mem_insert_self _ _
      rcases hcase with ⟨hg, hall⟩ | ⟨o, hv, hlen⟩
      · refine ⟨gs1, fs1, h1', Or.inr ⟨o1, val_congr hv1 ?_, ?_⟩⟩
        · intro x
          have : ¬ ∃ c' ∈ S, gad G C c' x = true := by
            rintro ⟨c', hc', hg'⟩
            rw [gad_empty (hall c' hc')] at hg'
            exact Bool.false_ne_true hg'
          rw [Bool.eq_iff_iff]
          simp only [decide_eq_true_eq, Finset.mem_insert]
          constructor
          · intro hx; exact ⟨c, Or.inl rfl, hx⟩
          · rintro ⟨c', hc' | hc', hx⟩
            · subst hc'; exact hx
            · exact absurd ⟨c', hc', hx⟩ this
        · subst hg
          rw [Finset.sum_insert hcS, Finset.card_insert_of_notMem hcS]
          simp at hlen1
          omega
      · obtain ⟨h2, hv2⟩ := push h1' GateOp.or (Or.inr rfl) o o1 _ _
          (by rw [hfs]; exact val_ext hv fsn) hv1 (fun e => by simp at e) (fun e => by simp at e)
        refine ⟨_, _, h2, Or.inr ⟨_, val_congr hv2 ?_, ?_⟩⟩
        · intro x
          rw [Bool.eq_iff_iff]
          simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id,
            Bool.or_eq_true, decide_eq_true_eq, Finset.mem_insert]
          constructor
          · rintro (⟨c', hc', hx⟩ | hx)
            · exact ⟨c', Or.inr hc', hx⟩
            · exact ⟨c, Or.inl rfl, hx⟩
          · rintro ⟨c', hc' | hc', hx⟩
            · subst hc'; exact Or.inr hx
            · exact Or.inl ⟨c', hc', hx⟩
        · rw [Finset.sum_insert hcS, Finset.card_insert_of_notMem hcS]
          simp only [List.length_append, List.length_singleton]
          omega

theorem edge_N {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    (hC : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C) {u v : Fin n} (h : G.Adj u v) :
    ∃ c ∈ C, ∃ w ∈ N G C c, (c = u ∧ w = v) ∨ (c = v ∧ w = u) := by
  simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hC u v h with hu | hv
  · by_cases hv' : v ∈ C ∧ v < u
    · refine ⟨v, hv'.1, u, ⟨h.symm, fun hh => lt_asymm hh.2 hv'.2⟩, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨u, hu, v, ⟨h, hv'⟩, Or.inl ⟨rfl, rfl⟩⟩
  · by_cases hu' : u ∈ C ∧ u < v
    · exact ⟨u, hu'.1, v, ⟨h, fun hh => lt_asymm hh.2 hu'.2⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨v, hv, u, ⟨h.symm, hu'⟩, Or.inr ⟨rfl, rfl⟩⟩

theorem any_gad {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    (hC : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C) (x : Fin n → Bool) :
    decide (∃ c ∈ C, gad G C c x = true) = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x := by
  rw [Bool.eq_iff_iff]
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, gad, decide_eq_true_eq,
    Bool.and_eq_true, Bool.or_eq_true, Finset.notMem_empty, false_and, exists_false,
    false_or]
  constructor
  · rintro ⟨c, -, hc, w, hw, hxw⟩
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact ⟨c, w, hw.1, hc, hxw⟩
  · rintro ⟨u, v, h, hu, hv⟩
    obtain ⟨c, hc, w, hw, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := edge_N hC h
    · exact ⟨c, hc, hu, w, hw, hv⟩
    · exact ⟨c, hc, hv, w, hw, hu⟩

theorem sumN_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) :
    ∑ c ∈ C, (N G C c).card ≤ G.edgeSet.ncard := by
  rw [← Finset.card_sigma]
  have : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [this]
  apply Finset.card_le_card_of_injOn (fun p => s(p.1, p.2))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_sigma, N, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp
    simp only [Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hp.2.1
  · rintro ⟨c, w⟩ hp ⟨c', w'⟩ hq hpq
    simp only [Finset.mem_coe, Finset.mem_sigma, N, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp hq
    rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2; rfl
    · exfalso
      subst h1; subst h2
      have e1 : ¬ w < c := fun hl => hp.2.2 ⟨hq.1, hl⟩
      have e2 : ¬ c < w := fun hl => hq.2.2 ⟨hp.1, hl⟩
      have : c = w := le_antisymm (not_lt.1 e1) (not_lt.1 e2)
      subst this
      exact G.irrefl hp.2.1

theorem main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (hC : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G C) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
      D.size ≤ G.edgeSet.ncard + C.card - 1 ∧
      ∀ j < D.size, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = GateOp.and →
        (∃ c : Fin n, ∀ x, PEqualNP.EdgeOwnership.gateVal n D j x = true → x c = true) ∧
        ∃ u v : Fin n, G.Adj u v ∧
          PEqualNP.EdgeOwnership.gateVal n D j (PEqualNP.EdgeOwnership.pairInput u v) = true ∧
          ∀ i < j, (PEqualNP.MetaComplexity.NestedCover.gateAt D i).op = GateOp.and →
            PEqualNP.EdgeOwnership.gateVal n D i (PEqualNP.EdgeOwnership.pairInput u v) = false := by
  have hC' : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C := hC
  obtain ⟨gs, fs, ⟨hs, hl, hm, hA, hB⟩, hcase⟩ := build G C C (subset_refl _)
  rcases hcase with ⟨hg, hall⟩ | ⟨o, hv, hlen⟩
  · subst hg
    refine ⟨⟨[], n⟩, by simp [PEqualNP.MetaComplexity.Monotone2], ?_, by simp [Circuit.size], ?_⟩
    · funext x
      rw [← any_gad hC' x]
      have : ¬ ∃ c ∈ C, gad G C c x = true := by
        rintro ⟨c', hc', hg'⟩
        rw [gad_empty (hall c' hc')] at hg'
        exact Bool.false_ne_true hg'
      simp only [this, decide_false]
      show (wf [] (List.ofFn x)).getD n false = false
      simp only [wf, List.foldl_nil]
      exact List.getD_eq_default _ _ (by simp)
    · intro j hj
      simp [Circuit.size] at hj
  · refine ⟨⟨gs, o⟩, hm, ?_, ?_, ?_⟩
    · funext x
      show (wf gs (List.ofFn x)).getD o false = _
      rw [hs x, hv.2 x]
      exact any_gad hC' x
    · have h1 := sumN_le G C
      show gs.length ≤ _
      omega
    · intro j hj hand
      have hj' : j < gs.length := hj
      obtain ⟨c, v, hadj, h1, h2⟩ := hB j hj' hand
      have gv : ∀ i, i < gs.length → ∀ y : Fin n → Bool,
          PEqualNP.EdgeOwnership.gateVal n ⟨gs, o⟩ i y = fs.getD i (fun _ => false) y := by
        intro i hi y
        show (wf gs (List.ofFn y)).getD (n + i) false = _
        rw [hs y, V_read _ _ _ (by omega)]
      constructor
      · obtain ⟨l, _, hcenter⟩ := hA j hj' hand
        refine ⟨l, fun x hx => hcenter x ?_⟩
        rwa [gv j hj'] at hx
      · refine ⟨c, v, hadj, by rw [gv j hj']; exact h1, ?_⟩
        intro i hi hand'
        rw [gv i (by omega)]
        exact h2 i hi hand'

end PEqualNP.Outside.L_meta_1031.ForestCover

namespace PEqualNP.Outside.L_meta_1031.ForestCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

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

end PEqualNP.Outside.L_meta_1031.ForestCase


namespace PEqualNP.Outside.L_meta_1031.ForestCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma forest_optimal (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hacyclic : G.IsAcyclic) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ (∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) ∧ (∀ D : PEqualNP.CircuitLowerBounds.Circuit, (∀ g ∈ D.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) → (∀ x : Fin n → Bool, D.eval (List.ofFn x) = decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → C.size ≤ D.size) ∧ ∀ (t : ℕ) (g : PEqualNP.CircuitLowerBounds.Gate), C.gates[t]? = some g → g.op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ c : Fin n, (∃ u v : Fin n, G.Adj u v ∧ ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false)) ∧ ∀ u v : Fin n, G.Adj u v → ((C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t) false = true ∧ ∀ (t' : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), C.gates[t']? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.and → Relation.TransGen (fun a b : ℕ => a < b ∧ ∃ (k : ℕ) (h : PEqualNP.CircuitLowerBounds.Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) (n + t') (n + t) → (C.wires (List.ofFn (fun k : Fin n => decide (k = u ∨ k = v)))).getD (n + t') false = false) → u = c ∨ v = c := by
  classical
  by_cases hE : ∃ u v : Fin n, G.Adj u v
  swap
  · apply empty_graph n G
    intro u v huv
    exact hE ⟨u, v, huv⟩
  have hex : ∃ k : ℕ, ∃ T : Finset (Fin n),
      CoverPromise.IsVertexCover G T ∧ T.card = k := by
    refine ⟨Finset.univ.card, Finset.univ, ?_, rfl⟩
    intro u v _
    exact Or.inl (Finset.mem_univ u)
  obtain ⟨T, hT, hcard⟩ := Nat.find_spec hex
  have hmin : ∀ S : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ S ∨ v ∈ S) →
      T.card ≤ S.card := by
    intro S hS
    rw [hcard]
    exact Nat.find_min' hex ⟨S, hS, rfl⟩
  obtain ⟨C, hmono, hcompute, hsize, hstars⟩ := ForestCover.main n G T hT
  refine ⟨C, ?_, ?_, ?_, ?_⟩
  · simpa [Monotone2] using hmono
  · intro x
    have hx := congrFun hcompute x
    simpa [circuitFun, NestedCover.graphFun] using hx
  · intro D hm hc
    have hD : FanInTwo D := by
      intro g hg
      obtain ⟨hop, hlen⟩ := hm g hg
      refine ⟨?_, hlen⟩
      rcases hop with hop | hop <;> simp [hop]
    have hlow := ForestAux.Forest.forest_bound n T.card D.size G hacyclic hE hmin
      ⟨D, hD, le_rfl, hc⟩
    have he : G.edgeFinset.card = G.edgeSet.ncard := by
      rw [← Set.ncard_coe_finset, SimpleGraph.coe_edgeFinset]
    rw [he] at hlow
    omega
  · intro t g ht hand
    have hlt : t < C.size := (List.getElem?_eq_some_iff.mp ht).1
    have hgate : NestedCover.gateAt C t = g := by
      simp [NestedCover.gateAt, List.getD_eq_getElem?_getD, ht]
    obtain ⟨⟨c, hcenter⟩, u, v, huv, hval, hearlier⟩ := hstars t hlt (by simpa only [hgate] using hand)
    refine ⟨c, ⟨u, v, huv, hval, ?_⟩, ?_⟩
    · intro t' g' ht' hand' hpath
      have hgate' : NestedCover.gateAt C t' = g' := by
        simp [NestedCover.gateAt, List.getD_eq_getElem?_getD, ht']
      have inc {a b : ℕ} (hp : Relation.TransGen (fun a b : ℕ => a < b ∧
          ∃ (k : ℕ) (h : Gate), b = n + k ∧ C.gates[k]? = some h ∧ a ∈ h.inputs) a b) :
          a < b := by
        induction hp with
        | single h => exact h.1
        | tail _ h ih => exact ih.trans h.1
      have hi := inc hpath
      exact hearlier t' (by omega) (by simpa only [hgate'] using hand')
    · intro u' v' _ hown
      have hc := hcenter (EdgeOwnership.pairInput u' v') hown.1
      simp only [EdgeOwnership.pairInput, decide_eq_true_eq] at hc
      exact hc.elim (fun h => Or.inl h.symm) (fun h => Or.inr h.symm)

end PEqualNP.Outside.L_meta_1031.ForestCase

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

namespace PEqualNP.Outside.L_meta_1031.CounterOr

open PEqualNP.CircuitLowerBounds

def edgeList : List (Fin 8 × Fin 8) :=
  [(0, 1), (1, 2), (0, 5), (1, 6), (2, 7),
   (3, 5), (4, 6), (5, 7), (6, 3), (7, 4)]

abbrev adjacent (u v : Fin 8) : Prop :=
  (u, v) ∈ edgeList ∨ (v, u) ∈ edgeList

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
abbrev graph : SimpleGraph (Fin 8) where
  Adj := adjacent
  symm := ⟨fun _ _ h => h.symm⟩
  loopless := ⟨by decide⟩

def circuit : Circuit :=
  ⟨[⟨.or, [1, 5]⟩, ⟨.or, [1, 7]⟩, ⟨.or, [5, 6]⟩,
    ⟨.and, [8, 9]⟩, ⟨.and, [10, 11]⟩, ⟨.or, [4, 12]⟩,
    ⟨.or, [6, 7]⟩, ⟨.and, [13, 14]⟩, ⟨.and, [0, 8]⟩,
    ⟨.or, [15, 16]⟩, ⟨.and, [3, 10]⟩, ⟨.or, [17, 18]⟩,
    ⟨.and, [2, 9]⟩, ⟨.or, [19, 20]⟩], 21⟩

def orCount (C : Circuit) : ℕ :=
  C.gates.countP fun g => match g.op with | .or => true | _ => false

theorem binary_monotone :
    ∀ g ∈ circuit.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  simp [circuit]

theorem gate_count : circuit.size = 14 := rfl

theorem or_count : orCount circuit = 8 := rfl

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem edge_count : graph.edgeFinset.card = 10 := by decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no_triangle :
    ∀ a b c : Fin 8, graph.Adj a b → graph.Adj b c → ¬graph.Adj c a := by
  letI : DecidableRel graph.Adj := fun u v => inferInstanceAs (Decidable (adjacent u v))
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem no_four_cycle :
    ∀ a b c d : Fin 8, a ≠ c → b ≠ d →
      graph.Adj a b → graph.Adj b c → graph.Adj c d → ¬graph.Adj d a := by
  letI : DecidableRel graph.Adj := fun u v => inferInstanceAs (Decidable (adjacent u v))
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem computes :
    ∀ x : Fin 8 → Bool, circuit.eval (List.ofFn x) =
      decide (∃ i j : Fin 8, graph.Adj i j ∧ x i = true ∧ x j = true) := by
  decide

theorem violates_or_edge_bound : orCount circuit < graph.edgeFinset.card - 1 := by
  rw [or_count, edge_count]
  decide

end PEqualNP.Outside.L_meta_1031.CounterOr
