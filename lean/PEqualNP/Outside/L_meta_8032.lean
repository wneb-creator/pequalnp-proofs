import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_8032
open CircuitLowerBounds MetaComplexity EdgeOwnership

abbrev edges : List (Fin 11 × Fin 11) :=
  [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
   (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]

abbrev negatives : List ℕ :=
  [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,582,596,1066,1186,1288,1408,1546]

lemma wire_mono (C : Circuit) (hm : Monotone2 C) (x y : List Bool)
    (hl : x.length = y.length) (hxy : ∀ k, x.getD k false = true → y.getD k false = true) :
    ∀ k, (C.wires x).getD k false = true → (C.wires y).getD k false = true := by
  have snoc (w : List Bool) (v : Bool) (k : ℕ) : (w ++ [v]).getD k false =
      if k = w.length then v else w.getD k false := by
    rcases lt_trichotomy k w.length with h | h | h
    · rw [ite_eq_right (by omega),List.getD_append _ _ _ _ h]
    · subst k; simp [List.getD_eq_getElem?_getD]
    · rw [ite_eq_right (by omega)]
      rw [List.getD_eq_getElem?_getD,List.getD_eq_getElem?_getD,List.getElem?_eq_none (by simp; omega),
        List.getElem?_eq_none (by omega)]
  obtain ⟨gs,out⟩ := C
  unfold Circuit.wires
  induction gs generalizing x y with
  | nil => exact hxy
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih
    · simp [hl]
    · intro k hk
      simp only [snoc,hl] at hk ⊢
      split_ifs at hk ⊢ with h
      · have hgate : g.op = .and ∨ g.op = .or := (hm g (List.mem_cons_self ..)).1
        rcases hgate with h | h
        · simp only [h,GateOp.eval,List.all_map,List.all_eq_true,Function.comp_apply,id_eq] at hk ⊢
          exact fun i hi => hxy i (hk i hi)
        · simp only [h,GateOp.eval,List.any_map,List.any_eq_true,Function.comp_apply,id_eq] at hk ⊢
          obtain ⟨i,hi,hv⟩ := hk; exact ⟨i,hi,hxy i hv⟩
      · exact hxy k hk
    · exact fun g' hg' => hm g' (List.mem_cons_of_mem _ hg')


lemma up (C : Circuit) (hm : Monotone2 C) {x y : Fin 11 → Bool}
    (h : ∀ i, x i = true → y i = true) : circuitFun 11 C x = true → circuitFun 11 C y = true := by
  apply wire_mono C hm (List.ofFn x) (List.ofFn y) (by simp) _ C.output
  intro k hk
  by_cases hlt : k < 11
  · rw [List.getD_eq_getElem _ _ (by simpa using hlt)] at hk ⊢
    simp only [List.getElem_ofFn] at hk ⊢
    exact h ⟨k,hlt⟩ hk
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hlt)] at hk; cases hk

-- Every independent support is contained in one of the listed negative masks.
set_option maxHeartbeats 4000000 in
lemma covered : ∀ x : Fin 11 → Bool,
    edges.any (fun e => x e.1 && x e.2) = false →
    ∃ m ∈ negatives, ∀ i, x i = true → m.testBit i.val = true := by decide +kernel

lemma exactTests_compute : ∀ C : Circuit, Monotone2 C →
    (∀ e ∈ edges, C.eval (List.ofFn (pairInput e.1 e.2)) = true) →
    (∀ m ∈ negatives, C.eval (List.ofFn fun i : Fin 11 => m.testBit i.val) = false) →
    circuitFun 11 C = fun x => edges.any fun e => x e.1 && x e.2 := by
  intro C hm positive negative; funext x
  cases hv : edges.any (fun e => x e.1 && x e.2) with
  | false =>
    obtain ⟨m,hm',hsub⟩ := covered x hv
    apply Bool.eq_false_iff.mpr; intro hx
    have ht := up C hm hsub hx
    exact Bool.noConfusion ((negative m hm').symm.trans ht)
  | true =>
    obtain ⟨e,he,hbit⟩ := List.any_eq_true.mp hv
    simp only [Bool.and_eq_true] at hbit
    apply up C hm _ (positive e he)
    intro i hi; rw [pairInput,decide_eq_true_eq] at hi
    rcases hi with rfl | rfl
    · exact hbit.1
    · exact hbit.2


open PEqualNP PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

set_option maxHeartbeats 1500000 in
set_option maxRecDepth 8192 in
lemma packed_search_sound
    (search : ∃ (k : Fin 22) (op : Fin ↑k → Bool) (a b : Fin ↑k → Fin 33)
        (w : Fin 33) (s : ℕ → ℕ) (d : Fin 3 → Fin ↑k) (q : Fin 3 → Fin 24),
      ↑w < (11 : ℕ)+↑k ∧ s ↑w = 65535 ∧
      (∀ i : Fin 11, s ↑i = ([2147418115,663661903884,34144976944,728266375360,
        21653750532,103293914128,26322415680,344922804352,414195942664,581968119809,
        1065151898146] : List ℕ).getD ↑i 0) ∧
      (∀ i, ↑(a i) < (11 : ℕ)+↑i ∧ ↑(b i) < (11 : ℕ)+↑i ∧ s (11+↑i) =
        if op i = true then s ↑(a i) &&& s ↑(b i) else s ↑(a i) ||| s ↑(b i)) ∧
      Function.Injective d ∧ ∀ i, op (d i) = true ∧
        (s (11+↑(d i))).testBit (16+↑(q i)) = true) :
    have x1 : List (Fin (11 : ℕ) × Fin (11 : ℕ)) := [((0 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))), ((0 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))), ((1 : Fin (11 : ℕ)), (4 : Fin (11 : ℕ))), ((1 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (5 : Fin (11 : ℕ))), ((2 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))), ((3 : Fin (11 : ℕ)), (6 : Fin (11 : ℕ))), ((3 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))), ((4 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), ((4 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))), ((5 : Fin (11 : ℕ)), (8 : Fin (11 : ℕ))), ((5 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (7 : Fin (11 : ℕ))), ((6 : Fin (11 : ℕ)), (10 : Fin (11 : ℕ))), ((7 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ))), ((8 : Fin (11 : ℕ)), (9 : Fin (11 : ℕ)))]; have x2 : List ℕ := [(15 : ℕ), (29 : ℕ), (43 : ℕ), (57 : ℕ), (71 : ℕ), (85 : ℕ), (99 : ℕ), (113 : ℕ), (135 : ℕ), (149 : ℕ), (163 : ℕ), (177 : ℕ), (269 : ℕ), (325 : ℕ), (389 : ℕ), (526 : ℕ), (540 : ℕ), (582 : ℕ), (596 : ℕ), (1066 : ℕ), (1186 : ℕ), (1288 : ℕ), (1408 : ℕ), (1546 : ℕ)]; ∃ (x3 : Fin (22 : ℕ)) (x4 : Fin ↑x3 → Bool) (x5 : Fin ↑x3 → Option (Fin (33 : ℕ)) × Option (Fin (33 : ℕ))) (x6 : Fin (33 : ℕ)),   have x7 : PEqualNP.CircuitLowerBounds.Circuit := { gates := List.ofFn fun (x7 : Fin ↑x3) => { op := if x4 x7 = Bool.true then PEqualNP.CircuitLowerBounds.GateOp.and else PEqualNP.CircuitLowerBounds.GateOp.or, inputs := List.map Fin.val ((x5 x7).1.toList ++ (x5 x7).2.toList) : PEqualNP.CircuitLowerBounds.Gate }, output := ↑x6 : PEqualNP.CircuitLowerBounds.Circuit };   (∀ x8 ∈ x1, x7.eval (List.ofFn (PEqualNP.EdgeOwnership.pairInput x8.1 x8.2)) = Bool.true) ∧ (∀ x8 ∈ x2, x7.eval (List.ofFn fun (x10 : Fin (11 : ℕ)) => x8.testBit ↑x10) = Bool.false) ∧ (3 : ℕ) ≤ (PEqualNP.TopForm.junk (PEqualNP.EdgeOwnership.edgeGraph (11 : ℕ) (List.map (fun (x8 : Fin (11 : ℕ) × Fin (11 : ℕ)) => (↑x8.1, ↑x8.2)) x1)) x7).card := by
  have replayAux (f : ℕ → Bool) : ∀ (gs : List Gate) (w : List Bool),
      (∀ i, i < w.length → w.getD i false = f i) →
      (∀ k (hk : k < gs.length), (∀ j ∈ (gs[k]).inputs, j < w.length + k) ∧
          (gs[k]).op.eval ((gs[k]).inputs.map f) = f (w.length + k)) →
      ∀ i, i < w.length + gs.length →
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD i
          false = f i := by
    intro gs
    induction gs with
    | nil =>
      intro w hw _ i hi
      simp only [List.length_nil, Nat.add_zero] at hi
      simpa using hw i hi
    | cons g gs ih =>
      intro w hw hg i hi
      rw [List.foldl_cons]
      have h0 := hg 0 (by simp)
      simp only [List.getElem_cons_zero, Nat.add_zero] at h0
      obtain ⟨hin, hev⟩ := h0
      apply ih
      · intro j hj
        simp only [List.length_append, List.length_singleton] at hj
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | hj
        · rw [List.getD_append _ _ _ _ hj]
          exact hw j hj
        · subst hj
          rw [List.getD_eq_getElem?_getD]
          simp only [List.getElem?_append_right (le_refl _), Nat.sub_self,
            List.getElem?_cons_zero, Option.getD_some]
          rw [← hev]
          congr 1
          apply List.map_congr_left
          intro a ha
          exact hw a (hin a ha)
      · intro k hk
        have h := hg (k + 1) (by simp; omega)
        simp only [List.getElem_cons_succ] at h
        obtain ⟨h1, h2⟩ := h
        simp only [List.length_append, List.length_singleton]
        refine ⟨fun j hj => by have := h1 j hj; omega, ?_⟩
        rw [h2]
        congr 1
        omega
      · simp only [List.length_append, List.length_singleton]
        simp only [List.length_cons] at hi
        omega
  have replay : ∀ (x1 : List PEqualNP.CircuitLowerBounds.Gate) (x2 : List Bool) (x3 : ℕ → Bool), (∀ (x4 : Fin x2.length), x2.get x4 = x3 ↑x4) → (∀ (x5 : Fin x1.length), (∀ x6 ∈ (x1.get x5).inputs, x6 < x2.length + ↑x5) ∧ (x1.get x5).op.eval (List.map x3 (x1.get x5).inputs) = x3 (x2.length + ↑x5)) → ∀ (x6 : Fin (x2.length + x1.length)), ({ gates := x1, output := (0 : ℕ) : PEqualNP.CircuitLowerBounds.Circuit }.wires x2).getD (↑x6) Bool.false = x3 ↑x6 := by
    intro gs w f hw hg i
    unfold PEqualNP.CircuitLowerBounds.Circuit.wires
    apply replayAux f gs w
    · intro j hj
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
      exact hw ⟨j, hj⟩
    · intro k hk
      exact hg ⟨k, hk⟩
    · exact i.isLt
  let E : List (Fin 11 × Fin 11) := [(0,9),(0,10),(1,4),(1,8),(2,5),(2,10),(3,6),(3,7),
    (4,8),(4,10),(5,8),(5,9),(6,7),(6,10),(7,9),(8,9)]
  let Q : List ℕ := [15,29,43,57,71,85,99,113,135,149,163,177,269,325,389,526,540,
    582,596,1066,1186,1288,1408,1546]
  let T : List ℕ := [513,1025,18,258,36,1028,72,136,272,1040,288,544,192,1088,640,768] ++ Q
  let col : List ℕ := [2147418115,663661903884,34144976944,728266375360,21653750532,
    103293914128,26322415680,344922804352,414195942664,581968119809,1065151898146]
  let row (u : Fin 40) (i : Fin 11) := T[u.val]!.testBit i.val
  let graph := edgeGraph 11 (E.map fun e => (e.1.val,e.2.val))
  have tab : ∀ (u : Fin 40) (i : Fin 11), row u i = (col.getD i.val 0).testBit u.val := by decide
  have pos : ∀ (e : Fin 11 × Fin 11), e ∈ E → ∃ u : Fin 40,
      (65535 : ℕ).testBit u.val = true ∧ ∀ i, row u i = pairInput e.1 e.2 i := by
    decide +kernel
  have neg : ∀ m ∈ Q, ∃ u : Fin 40, (65535 : ℕ).testBit u.val = false ∧
      ∀ i : Fin 11, row u i = m.testBit i.val := by decide
  have indep : ∀ z : Fin 24, graphFun graph ∅ (row ⟨16+z.val,Nat.add_lt_add_left z.isLt 16⟩) = false := by
    decide +kernel
  obtain ⟨k,op,a,b,w,s,d,q,hw,hout,hinput,hgate,hd,hq⟩ := search
  let g (i : Fin k.val) : Gate := ⟨if op i then .and else .or, [(a i).val,(b i).val]⟩
  let C : Circuit := ⟨List.ofFn g, w.val⟩
  have gate_spec (i : Fin k.val) : C.gates[i.val]'(by simp [C]) = g i := by simp [C]
  have sim (u : Fin 40) (v : ℕ) (hv : v < 11+k.val) :
      (C.wires (List.ofFn (row u))).getD v false = (s v).testBit u.val := by
    let xs := List.ofFn (row u)
    let bit (n : ℕ) := (s n).testBit u.val
    have first (i : Fin xs.length) : xs[i.val] = bit i.val := by
      have hi : i.val < 11 := by simpa [xs] using i.isLt
      let h : Fin 11 := ⟨i.val,hi⟩
      have eqs : s h.val = col.getD h.val 0 := hinput h
      have firstWire : xs[i.val]'i.isLt = row u h := List.getElem_ofFn i.isLt
      exact firstWire.trans ((tab u h).trans (congrArg (fun l : ℕ => l.testBit u.val) eqs.symm))
    have step (i : Fin C.gates.length) :
        (∀ p ∈ C.gates[i.val].inputs, p < xs.length+i.val) ∧
        C.gates[i.val].op.eval (C.gates[i.val].inputs.map bit) = bit (xs.length+i.val) := by
      have hi : i.val < k.val := by simpa [C] using i.isLt
      let j : Fin k.val := ⟨i.val,hi⟩
      rw [show C.gates[i.val] = g j from gate_spec j]
      obtain ⟨la,lb,rule⟩ := hgate j
      constructor
      · intro p hp
        rcases (show p = (a j).val ∨ p = (b j).val by simpa [g] using hp) with rfl | rfl
        · simpa [xs,j] using la
        · simpa [xs,j] using lb
      · change _ = (s (xs.length+i.val)).testBit u.val
        rw [show xs.length+i.val = 11+j.val by simp [xs,j],rule]
        cases hh : op j
        · simp only [g,hh,Bool.false_eq_true,ite_false,Nat.testBit_or,List.map_cons,List.map_nil]
          change (bit (a j).val || (bit (b j).val || false)) = _
          simp only [Bool.or_false,bit]
        · simp only [g,hh,ite_true,Nat.testBit_and,List.map_cons,List.map_nil]
          change (bit (a j).val && (bit (b j).val && true)) = _
          simp only [Bool.and_true,bit]
    exact replay C.gates xs bit first step ⟨v, by simpa [C,xs] using hv⟩
  have outs (u : Fin 40) : C.eval (List.ofFn (row u)) = (65535 : ℕ).testBit u.val := by
    exact (sim u w.val hw).trans (congrArg (fun m : ℕ => m.testBit u.val) hout)
  refine ⟨k,op,(fun j => (some (a j),some (b j))),w,?_,?_,?_⟩
  · change ∀ e ∈ E, C.eval (List.ofFn (pairInput e.1 e.2)) = true
    intro e he
    obtain ⟨u,hu,heq⟩ := pos e he
    rw [← funext heq, outs,hu]
  · change ∀ m ∈ Q, C.eval (List.ofFn (fun i : Fin 11 => m.testBit i.val)) = false
    intro m hm
    obtain ⟨u,hu,heq⟩ := neg m hm
    rw [← funext heq, outs,hu]
  · change 3 ≤ (junk graph C).card
    have hit (i : Fin 3) : (d i).val ∈ junk graph C := by
      let u : Fin 40 := ⟨16+(q i).val,by omega⟩
      have hi : (d i).val < C.gates.length := by simp [C]
      have andGate : (gateAt C (d i).val).op = .and := by
        change (C.gates.getD (d i).val _).op = GateOp.and
        rw [List.getD_eq_getElem _ _ hi,gate_spec]
        change (if op (d i) then GateOp.and else GateOp.or) = GateOp.and
        rw [(hq i).1]
        rfl
      exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hi,andGate,hi,row u,
        (sim u (11+(d i).val) (by omega)).trans (hq i).2,indep (q i)⟩
    let f (i : Fin 3) : ↥(junk graph C) := ⟨(d i).val,hit i⟩
    have hf : Function.Injective f := fun _ _ h => hd (Fin.ext (congrArg Subtype.val h))
    calc
      3 = Fintype.card (Fin 3) := (Fintype.card_fin 3).symm
      _ ≤ Fintype.card ↥(junk graph C) := Fintype.card_le_of_injective f hf
      _ = (junk graph C).card := Fintype.card_coe _



open PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge PEqualNP.TopForm

abbrev graph := edgeGraph 11 (edges.map fun e => (e.1.val,e.2.val))

set_option maxRecDepth 8192 in
lemma graph_formula (x : Fin 11 → Bool) :
    graphFun graph ∅ x = edges.any (fun e => x e.1 && x e.2) := by
  apply Bool.eq_iff_iff.mpr
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false,
    decide_false, Bool.false_or, decide_eq_true_eq, List.any_eq_true, Bool.and_eq_true]
  constructor
  · rintro ⟨u,v,⟨hne,hm⟩,hu,hv⟩
    rcases hm with hm | hm
    · obtain ⟨e,he,eq⟩ := List.mem_map.mp hm
      have ha : e.1 = u := Fin.ext (congrArg Prod.fst eq)
      have hb : e.2 = v := Fin.ext (congrArg Prod.snd eq)
      exact ⟨e,he,ha.symm ▸ hu,hb.symm ▸ hv⟩
    · obtain ⟨e,he,eq⟩ := List.mem_map.mp hm
      have ha : e.1 = v := Fin.ext (congrArg Prod.fst eq)
      have hb : e.2 = u := Fin.ext (congrArg Prod.snd eq)
      exact ⟨e,he,ha.symm ▸ hv,hb.symm ▸ hu⟩
  · rintro ⟨e,he,ha,hb⟩
    have noloop : ∀ f ∈ edges, f.1 ≠ f.2 := by decide
    exact ⟨e.1,e.2,⟨noloop e he,Or.inl (List.mem_map.mpr ⟨e,he,rfl⟩)⟩,ha,hb⟩

lemma negative_independent (m : ℕ) (hm : m ∈ negatives) :
    graphFun graph ∅ (fun i : Fin 11 => m.testBit i.val) = false := by
  rw [graph_formula]
  have h : ∀ m ∈ negatives,
      edges.any (fun e => m.testBit e.1.val && m.testBit e.2.val) = false := by decide
  exact h m hm

lemma gate_up (C : Circuit) (hm : Monotone2 C) (j : ℕ) {x y : Fin 11 → Bool}
    (h : ∀ i, x i = true → y i = true) :
    gateVal 11 C j x = true → gateVal 11 C j y = true := by
  apply wire_mono C hm (List.ofFn x) (List.ofFn y) (by simp) _ (11+j)
  intro k hk
  by_cases hlt : k < 11
  · rw [List.getD_eq_getElem _ _ (by simpa using hlt)] at hk ⊢
    simp only [List.getElem_ofFn] at hk ⊢
    exact h ⟨k,hlt⟩ hk
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hlt)] at hk
    cases hk

lemma junk_iff_samples (C : Circuit) (hm : Monotone2 C) (j : ℕ) :
    j ∈ junk graph C ↔ j < C.gates.length ∧ (gateAt C j).op = GateOp.and ∧
      ∃ m ∈ negatives, gateVal 11 C j (fun i : Fin 11 => m.testBit i.val) = true := by
  change j ∈ (Finset.range C.gates.length).filter (fun k => IsDirtyAnd 11 graph C k) ↔ _
  rw [Finset.mem_filter, Finset.mem_range]
  unfold IsDirtyAnd IsDirty
  constructor
  · rintro ⟨hj,hop,hj',x,hx,hf⟩
    rw [graph_formula] at hf
    obtain ⟨m,hm',hsub⟩ := covered x hf
    exact ⟨hj,hop,m,hm',gate_up C hm j hsub hx⟩
  · rintro ⟨hj,hop,m,hm',hv⟩
    exact ⟨hj,hop,hj,_,hv,negative_independent m hm'⟩



lemma three_junk_samples (C : Circuit) (hm : Monotone2 C)
    (h : 3 ≤ (junk graph C).card) :
    ∃ d : Fin 3 → Fin C.gates.length, ∃ m : Fin 3 → ℕ,
      Function.Injective d ∧ ∀ i,
        m i ∈ negatives ∧ (gateAt C (d i).val).op = GateOp.and ∧
        gateVal 11 C (d i).val (fun v : Fin 11 => (m i).testBit v.val) = true := by
  classical
  let S := junk graph C
  have hc : 3 ≤ Fintype.card ↥S := by simpa [S] using h
  let f (i : Fin 3) : ↥S :=
    (Fintype.equivFin ↥S).symm ⟨i.val,lt_of_lt_of_le i.isLt hc⟩
  have hf : Function.Injective f := by
    intro i j eq
    apply Fin.ext
    have hv := congrArg (fun a : ↥S => ((Fintype.equivFin ↥S) a).val) eq
    simpa [f] using hv
  have props (i : Fin 3) := (junk_iff_samples C hm (f i).val).mp (f i).property
  let d (i : Fin 3) : Fin C.gates.length := ⟨(f i).val,(props i).1⟩
  have witness (i : Fin 3) : ∃ m ∈ negatives,
      gateVal 11 C (d i).val (fun v : Fin 11 => m.testBit v.val) = true := (props i).2.2
  choose m hm' hv using witness
  refine ⟨d,m,?_,?_⟩
  · intro i j eq
    apply hf
    exact Subtype.ext (congrArg Fin.val eq)
  · intro i
    exact ⟨hm' i,(props i).2.1,hv i⟩


end PEqualNP.Outside.L_meta_8032
