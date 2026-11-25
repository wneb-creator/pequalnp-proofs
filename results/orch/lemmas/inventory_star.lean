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

end PEqualNP.Outside.L_meta_1031
