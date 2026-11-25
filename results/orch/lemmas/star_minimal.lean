import PEqualNP.Defs

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

