import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031

open PEqualNP.CircuitLowerBounds

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

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

end PEqualNP.Outside.L_meta_1031

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
