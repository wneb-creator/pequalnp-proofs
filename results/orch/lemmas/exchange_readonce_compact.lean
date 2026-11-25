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

end PEqualNP.Outside.L_meta_1031.StarLower

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
