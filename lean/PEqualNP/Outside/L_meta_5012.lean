import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_5012_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.CleanedNonEdge PEqualNP.TopForm

def gateBit (w : List Bool) (g : Gate) : Bool :=
  g.op.eval (g.inputs.map fun i => w.getD i false)

def stepWire (w : List Bool) (g : Gate) : List Bool := w ++ [gateBit w g]

def WiresLE (w z : List Bool) : Prop :=
  w.length = z.length ∧ ∀ i, w.getD i false = true → z.getD i false = true

def IsMonoGate (g : Gate) : Prop := g.op = GateOp.and ∨ g.op = GateOp.or

lemma monoGate_of_mem {C : Circuit} (hC : Monotone2 C) {g : Gate} (hg : g ∈ C.gates) :
    IsMonoGate g := by
  simpa [IsMonoGate] using (hC g hg).1

lemma bit_mono {w z : List Bool} (h : WiresLE w z) {g : Gate} (hg : IsMonoGate g)
    (hw : gateBit w g = true) : gateBit z g = true := by
  rcases hg with hop | hop
  · simp only [gateBit, hop, GateOp.eval, List.all_map, List.all_eq_true,
      Function.comp_apply, id_eq] at hw ⊢
    exact fun i hi => h.2 i (hw i hi)
  · simp only [gateBit, hop, GateOp.eval, List.any_map, List.any_eq_true,
      Function.comp_apply, id_eq] at hw ⊢
    obtain ⟨i, hi, hv⟩ := hw
    exact ⟨i, hi, h.2 i hv⟩

lemma append_mono {w z : List Bool} {a b : Bool} (h : WiresLE w z)
    (hab : a = true → b = true) : WiresLE (w ++ [a]) (z ++ [b]) := by
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  rw [List.getD_eq_getElem?_getD] at hi ⊢
  by_cases hlt : i < w.length
  · rw [List.getElem?_append_left hlt] at hi
    rw [List.getElem?_append_left (by rwa [← h.1])]
    simpa only [List.getD_eq_getElem?_getD] using h.2 i
      (by simpa only [List.getD_eq_getElem?_getD] using hi)
  · rw [List.getElem?_append_right (Nat.le_of_not_gt hlt)] at hi
    rw [List.getElem?_append_right (by rw [← h.1]; omega), ← h.1]
    cases hd : i - w.length with
    | zero =>
      simp only [hd, List.getElem?_cons_zero, Option.getD_some] at hi ⊢
      exact hab hi
    | succ k => simp [hd] at hi

lemma fold_mono (gs : List Gate) (hg : ∀ g ∈ gs, IsMonoGate g)
    {w z : List Bool} (h : WiresLE w z) :
    WiresLE (gs.foldl stepWire w) (gs.foldl stepWire z) := by
  induction gs generalizing w z with
  | nil => exact h
  | cons g gs ih =>
    exact ih (fun k hk => hg k (List.mem_cons_of_mem _ hk))
      (append_mono h (bit_mono h (hg g (by simp))))

lemma fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma fold_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (stepWire w g) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma ofFn_getD {n : ℕ} (x : Fin n → Bool) (u : Fin n) :
    (List.ofFn x).getD u.val false = x u := by
  simp [List.getD_eq_getElem?_getD]

lemma ofFn_mono {n : ℕ} {x y : Fin n → Bool} (h : ∀ u, x u = true → y u = true) :
    WiresLE (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hlt : i < n
  · rw [ofFn_getD y ⟨i, hlt⟩]
    exact h ⟨i, hlt⟩ (by simpa only [ofFn_getD x ⟨i, hlt⟩] using hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simpa using Nat.le_of_not_gt hlt)] at hi
    cases hi

def patch (C : Circuit) (j : ℕ) (g : Gate) : Circuit := ⟨C.gates.set j g, C.output⟩

def earlierWires (C : Circuit) (j : ℕ) (w : List Bool) : List Bool :=
  (C.gates.take j).foldl stepWire w

def off : Gate := ⟨GateOp.or, []⟩

def edgeGate {n : ℕ} (u v : Fin n) : Gate := ⟨GateOp.and, [u.val, v.val]⟩

lemma off_bit (w : List Bool) : gateBit w off = false := rfl

lemma edge_bit {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) (u v : Fin n) :
    gateBit (earlierWires C j (List.ofFn x)) (edgeGate u v) = (x u && x v) := by
  simp only [gateBit, edgeGate, GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
    List.all_nil, id_eq, Bool.and_true]
  unfold earlierWires
  rw [fold_getD_lt _ _ _ (by simp), fold_getD_lt _ _ _ (by simp),
    ofFn_getD, ofFn_getD]

lemma wires_patch {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (g : Gate) (w : List Bool) :
    (patch C j g).wires w = (C.gates.drop (j + 1)).foldl stepWire (stepWire (earlierWires C j w) g) := by
  change (C.gates.set j g).foldl stepWire w = _
  rw [List.set_eq_take_append_cons_drop, ite_eq_left hj, List.foldl_append, List.foldl_cons]
  rfl

lemma original_patch {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    patch C j C.gates[j] = C := by
  cases C with
  | mk gates output =>
    change Circuit.mk (gates.set j gates[j]) output = Circuit.mk gates output
    congr 1
    exact List.set_getElem_self hj

lemma patch_mono {C : Circuit} (hC : Monotone2 C) {j : ℕ} (hj : j < C.gates.length)
    (g h : Gate) (w : List Bool)
    (hbit : gateBit (earlierWires C j w) g = true → gateBit (earlierWires C j w) h = true) :
    WiresLE ((patch C j g).wires w) ((patch C j h).wires w) := by
  rw [wires_patch hj, wires_patch hj]
  apply fold_mono _ (fun k hk => monoGate_of_mem hC (List.mem_of_mem_drop hk))
  exact append_mono ⟨rfl, fun _ h => h⟩ hbit

lemma patch_bit {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
    (g : Gate) (x : Fin n → Bool) :
    gateVal n (patch C j g) j x = gateBit (earlierWires C j (List.ofFn x)) g := by
  have hlen : (earlierWires C j (List.ofFn x)).length = n + j := by
    unfold earlierWires
    rw [fold_length]
    simp [Nat.min_eq_left (Nat.le_of_lt hj)]
  unfold gateVal
  rw [wires_patch hj, fold_getD_lt _ _ _ (by simp [stepWire, hlen]), ← hlen]
  simp [stepWire, List.getD_eq_getElem?_getD]

lemma patch_isMono {C : Circuit} (hC : Monotone2 C) {j : ℕ} {g : Gate}
    (hg : IsMonoGate g) (hlen : g.inputs.length ≤ 2) : Monotone2 (patch C j g) := by
  intro k hk
  change k ∈ C.gates.set j g at hk
  rcases List.mem_or_eq_of_mem_set hk with hk | rfl
  · exact hC k hk
  · exact ⟨by simpa [IsMonoGate] using hg, hlen⟩

lemma gateAt_patch_ne (C : Circuit) (j k : ℕ) (g : Gate) (hne : j ≠ k) :
    gateAt (patch C j g) k = gateAt C k := by
  simp [patch, gateAt, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma graph_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by
  simp [graphFun]

lemma pair_le {n : ℕ} {x : Fin n → Bool} {u v : Fin n}
    (hu : x u = true) (hv : x v = true) (k : Fin n) :
    pairInput u v k = true → x k = true := by
  simp only [pairInput, decide_eq_true_eq]
  rintro (rfl | rfl)
  · exact hu
  · exact hv

lemma circuit_mono {n : ℕ} {C : Circuit} (hC : Monotone2 C) {x y : Fin n → Bool}
    (hxy : ∀ u, x u = true → y u = true) :
    circuitFun n C x = true → circuitFun n C y = true :=
  (fold_mono C.gates (fun _ hg => monoGate_of_mem hC hg) (ofFn_mono hxy)).2 C.output

lemma mem_junk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {j : ℕ} :
    j ∈ junk G C ↔ j < C.gates.length ∧ IsDirtyAnd n G C j := by
  unfold junk gatesWhere
  rw [Finset.mem_filter, Finset.mem_range]

lemma ao_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) : Monotone2 C := by
  intro r hr
  exact ⟨by simpa using hAO.1 r hr, (hAO.2.2 r hr).le⟩

lemma patch_gate_ao {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (r : Gate)
    (hrop : IsMonoGate r) (hrlen : r.inputs.length = 2)
    (hrback : ∀ i ∈ r.inputs, i < n + j) : IsAO2 n (patch C j r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    rcases List.mem_or_eq_of_mem_set hq with hq | rfl
    · exact hAO.1 q hq
    · exact hrop
  · intro k hk i hi
    have hkc : k < C.gates.length := by simpa [patch] using hk
    by_cases h : j = k
    · subst k
      have he : gateAt (patch C j r) j = r := by
        simp [gateAt, patch, List.getD_eq_getElem?_getD, hj]
      rw [he] at hi
      exact hrback i hi
    · rw [gateAt_patch_ne C j k r h] at hi
      exact hAO.2.1 k hkc i hi
  · intro q hq
    rcases List.mem_or_eq_of_mem_set hq with hq | rfl
    · exact hAO.2.2 q hq
    · exact hrlen

lemma patch_edge_ao {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j : ℕ} (hj : j < C.gates.length) (u v : Fin n) :
    IsAO2 n (patch C j (edgeGate u v)) := by
  apply patch_gate_ao hAO hj
  · exact Or.inl rfl
  · rfl
  · intro i hi
    simp only [edgeGate, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact lt_of_lt_of_le u.isLt (Nat.le_add_right _ _)
    · exact lt_of_lt_of_le v.isLt (Nat.le_add_right _ _)

lemma gateVal_patch_before {n : ℕ} {C : Circuit} {j k : ℕ}
    (hj : j < C.gates.length) (hkj : k < j) (r : Gate) (x : Fin n → Bool) :
    gateVal n (patch C j r) k x = gateVal n C k x := by
  have hlen : (earlierWires C j (List.ofFn x)).length = n + j := by
    unfold earlierWires
    rw [fold_length]
    simp [Nat.min_eq_left hj.le]
  have hp (r : Gate) : gateVal n (patch C j r) k x =
      (earlierWires C j (List.ofFn x)).getD (n + k) false := by
    unfold gateVal
    rw [wires_patch hj, fold_getD_lt _ _ _ (by simp [stepWire, hlen]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD,
      List.getElem?_append_left (show n + k < (earlierWires C j (List.ofFn x)).length by omega)]
  rw [hp, ← hp C.gates[j], original_patch hj]

lemma repair_clean_gate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (hAO : IsAO2 n C)
    (hF : circuitFun n C = graphFun G ∅) (hj : j < C.gates.length)
    (r : Gate) (hrop : IsMonoGate r) (hrlen : r.inputs.length = 2)
    (hrback : ∀ i ∈ r.inputs, i < n + j)
    (clean : ∀ x : Fin n → Bool,
      gateBit (earlierWires C j (List.ofFn x)) r = true → graphFun G ∅ x = true)
    (critical : ∀ a b, G.Adj a b → circuitFun n (patch C j off) (pairInput a b) = false →
      gateBit (earlierWires C j (List.ofFn (pairInput a b))) r = true) :
    let D := patch C j r
    IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = C.size ∧
      junk G D ⊆ junk G C ∧ j ∉ junk G D ∧
      (∀ k < j, k ∈ junk G C → k ∈ junk G D) := by
  have hC := ao_mono hAO
  let dropped := patch C j off
  let D := patch C j r
  have haoD : IsAO2 n D := patch_gate_ao hAO hj r hrop hrlen hrback
  have hmono : Monotone2 D := ao_mono haoD
  have hdom (x : Fin n → Bool) (hxG : graphFun G ∅ x = false) :
      WiresLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x)) := by
    rw [← original_patch hj]
    apply patch_mono hC hj
    intro hx
    have hh := clean x hx
    rw [hxG] at hh
    cases hh
  have hlow (x : Fin n → Bool) :
      circuitFun n dropped x = true → circuitFun n D x = true := by
    exact (patch_mono hC hj off r (List.ofFn x)
      (by simp [off_bit])).2 C.output
  have allEdges (a b : Fin n) (hab : G.Adj a b) : circuitFun n D (pairInput a b) = true := by
    cases hcut : circuitFun n dropped (pairInput a b) with
    | true => exact hlow _ hcut
    | false =>
      have hle := patch_mono hC hj C.gates[j] r (List.ofFn (pairInput a b))
        (fun _ => critical a b hab hcut)
      rw [original_patch hj] at hle
      apply hle.2 C.output
      change circuitFun n C (pairInput a b) = true
      rw [hF]
      exact (graph_true G (pairInput a b)).mpr
        ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩
  have hcompute : circuitFun n D = graphFun G ∅ := by
    funext x
    cases hG : graphFun G ∅ x with
    | true =>
      obtain ⟨a, b, hab, ha, hb⟩ := (graph_true G x).mp hG
      exact circuit_mono hmono (pair_le ha hb) (allEdges a b hab)
    | false =>
      cases hD : circuitFun n D x with
      | false => rfl
      | true =>
        have hout : circuitFun n C x = true := (hdom x hG).2 C.output hD
        rw [hF, hG] at hout
        cases hout
  have hlen : D.gates.length = C.gates.length := List.length_set
  have hclean : j ∉ junk G D := by
    intro h
    obtain ⟨x, hx, hxG⟩ := (mem_junk.mp h).2.2.2
    change gateVal n (patch C j r) j x = true at hx
    rw [patch_bit hj] at hx
    have hh := clean x hx
    rw [hxG] at hh
    cases hh
  have hsub : junk G D ⊆ junk G C := by
    intro k hk
    have hne : j ≠ k := fun he => hclean (he.symm ▸ hk)
    obtain ⟨hklen, hkop, _, x, hx, hxG⟩ := mem_junk.mp hk
    have hkc : k < C.gates.length := hlen ▸ hklen
    have hcop : (gateAt C k).op = GateOp.and := by
      rwa [show gateAt D k = gateAt C k from gateAt_patch_ne C j k r hne] at hkop
    exact mem_junk.mpr ⟨hkc, hcop, hkc, x, (hdom x hxG).2 (n + k) hx, hxG⟩
  refine ⟨haoD, hcompute, hlen, hsub, hclean, ?_⟩
  intro k hkj hk
  obtain ⟨hklen, hkop, _, x, hx, hxG⟩ := mem_junk.mp hk
  apply mem_junk.mpr
  refine ⟨by simpa [patch] using hklen, ?_, by simpa [patch] using hklen, x, ?_, hxG⟩
  · rw [gateAt_patch_ne C j k r (by omega)]
    exact hkop
  · rwa [gateVal_patch_before hj hkj]

lemma repair_unique_edge {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (j : ℕ) (hAO : IsAO2 n C)
    (hF : circuitFun n C = graphFun G ∅) (hjunk : j ∈ junk G C)
    (u v : Fin n) (huv : G.Adj u v)
    (unique : ∀ a b, G.Adj a b → circuitFun n (patch C j off) (pairInput a b) = false →
      pairInput a b = pairInput u v) :
    let D := patch C j (edgeGate u v)
    IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = C.size ∧
      junk G D ⊆ junk G C ∧ j ∉ junk G D ∧
      (∀ k < j, k ∈ junk G C → k ∈ junk G D) := by
  apply repair_clean_gate G C j hAO hF (mem_junk.mp hjunk).1
  · exact Or.inl rfl
  · rfl
  · intro i hi
    simp only [edgeGate, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact lt_of_lt_of_le u.isLt (Nat.le_add_right _ _)
    · exact lt_of_lt_of_le v.isLt (Nat.le_add_right _ _)
  · intro x hx
    rw [edge_bit, Bool.and_eq_true] at hx
    exact (graph_true G x).mpr ⟨u, v, huv, hx.1, hx.2⟩
  · intro a b hab hlost
    rw [unique a b hab hlost, edge_bit]
    simp [pairInput]

lemma no_clean_later_replacement
    (rungOne : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (s : Fin n → Bool),
      (∀ u v, G.Adj u v → s u ≠ s v) → NoFourCycle G → IsLeastAO G C →
        (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (g h : ℕ)
    (hgh : g < h) (hJ : junk G C = {g, h})
    (r : Gate) (hrop : IsMonoGate r) (hrlen : r.inputs.length = 2)
    (hrback : ∀ i ∈ r.inputs, i < n + h)
    (clean : ∀ x : Fin n → Bool,
      gateBit (earlierWires C h (List.ofFn x)) r = true → graphFun G ∅ x = true)
    (critical : ∀ a b, G.Adj a b → circuitFun n (patch C h off) (pairInput a b) = false →
      gateBit (earlierWires C h (List.ofFn (pairInput a b))) r = true) : False := by
  have hgJ : g ∈ junk G C := by simp [hJ]
  have hhJ : h ∈ junk G C := by simp [hJ]
  obtain ⟨hAO, hF, hsize, hsub, hclean, hbefore⟩ :=
    repair_clean_gate G C h hL.1 hL.2.1 (mem_junk.mp hhJ).1 r hrop hrlen hrback clean critical
  let D := patch C h r
  have hDL : IsLeastAO G D := by
    refine ⟨hAO, hF, ?_⟩
    intro E hE hEF
    rw [hsize]
    exact hL.2.2 E hE hEF
  have hDJ : junk G D = {g} := by
    apply Finset.ext
    intro k
    constructor
    · intro hk
      have hkC := hsub hk
      rw [hJ] at hkC
      simp only [Finset.mem_insert, Finset.mem_singleton] at hkC
      rcases hkC with rfl | rfl
      · simp
      · exact False.elim (hclean hk)
    · intro hk
      have heq : k = g := Finset.mem_singleton.mp hk
      subst k
      exact hbefore g hgh hgJ
  apply rungOne n G D s hcol h4 hDL
  rw [hDJ]
  exact Finset.card_singleton g

lemma earlier_read_eq_wireVal {n : ℕ} {C : Circuit} {j w : ℕ}
    (hj : j < C.gates.length) (hw : w < n + j) (x : Fin n → Bool) :
    (earlierWires C j (List.ofFn x)).getD w false = wireVal n C w x := by
  have hlen : (earlierWires C j (List.ofFn x)).length = n + j := by
    unfold earlierWires
    rw [fold_length]
    simp [Nat.min_eq_left hj.le]
  calc
    (earlierWires C j (List.ofFn x)).getD w false =
        ((patch C j C.gates[j]).wires (List.ofFn x)).getD w false := by
      rw [wires_patch hj, fold_getD_lt _ _ _ (by simp [stepWire, hlen]; omega)]
      simp [stepWire, List.getD_eq_getElem?_getD,
        List.getElem?_append_left (show w < (earlierWires C j (List.ofFn x)).length by omega)]
    _ = wireVal n C w x := by rw [original_patch hj]; rfl

def rawStarGate {n : ℕ} (u : Fin n) (w : ℕ) : Gate := ⟨GateOp.and, [u.val, w]⟩

lemma rawStar_bit {n : ℕ} {C : Circuit} {j w : ℕ}
    (hj : j < C.gates.length) (hw : w < n + j) (x : Fin n → Bool) (u : Fin n) :
    gateBit (earlierWires C j (List.ofFn x)) (rawStarGate u w) =
      (x u && wireVal n C w x) := by
  simp only [gateBit, rawStarGate, GateOp.eval, List.map_cons, List.map_nil,
    List.all_cons, List.all_nil, id_eq, Bool.and_true]
  rw [earlier_read_eq_wireVal hj hw]
  unfold earlierWires
  rw [fold_getD_lt _ _ _ (by simp), ofFn_getD]

lemma no_clean_later_star
    (rungOne : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (s : Fin n → Bool),
      (∀ u v, G.Adj u v → s u ≠ s v) → NoFourCycle G → IsLeastAO G C →
        (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (g h : ℕ)
    (hgh : g < h) (hJ : junk G C = {g, h}) (u : Fin n) (w : ℕ) (hw : w < n + h)
    (clean : ∀ x : Fin n → Bool,
      x u = true → wireVal n C w x = true → graphFun G ∅ x = true)
    (critical : ∀ a b, G.Adj a b → circuitFun n (patch C h off) (pairInput a b) = false →
      pairInput a b u = true ∧ wireVal n C w (pairInput a b) = true) : False := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hh := (mem_junk.mp hhJ).1
  apply no_clean_later_replacement rungOne G C s hcol h4 hL g h hgh hJ (rawStarGate u w)
  · exact Or.inl rfl
  · rfl
  · intro i hi
    simp only [rawStarGate, List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact lt_of_lt_of_le u.isLt (Nat.le_add_right _ _)
    · exact hw
  · intro x hx
    rw [rawStar_bit hh hw, Bool.and_eq_true] at hx
    exact clean x hx.1 hx.2
  · intro a b hab hlost
    rw [rawStar_bit hh hw, Bool.and_eq_true]
    exact critical a b hab hlost

lemma no_unique_later_edge
    (rungOne : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (s : Fin n → Bool),
      (∀ u v, G.Adj u v → s u ≠ s v) → NoFourCycle G → IsLeastAO G C →
        (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (g h : ℕ)
    (hgh : g < h) (hJ : junk G C = {g, h}) (u v : Fin n) (huv : G.Adj u v)
    (unique : ∀ a b, G.Adj a b → circuitFun n (patch C h off) (pairInput a b) = false →
      pairInput a b = pairInput u v) : False := by
  have hgJ : g ∈ junk G C := by simp [hJ]
  have hhJ : h ∈ junk G C := by simp [hJ]
  obtain ⟨hAO, hF, hsize, hsub, hclean, hbefore⟩ :=
    repair_unique_edge G C h hL.1 hL.2.1 hhJ u v huv unique
  let D := patch C h (edgeGate u v)
  have hDL : IsLeastAO G D := by
    refine ⟨hAO, hF, ?_⟩
    intro E hE hEF
    rw [hsize]
    exact hL.2.2 E hE hEF
  have hDJ : junk G D = {g} := by
    apply Finset.ext
    intro k
    constructor
    · intro hk
      have hkC := hsub hk
      rw [hJ] at hkC
      simp only [Finset.mem_insert, Finset.mem_singleton] at hkC
      rcases hkC with rfl | rfl
      · simp
      · exact False.elim (hclean hk)
    · intro hk
      have heq : k = g := Finset.mem_singleton.mp hk
      subst k
      exact hbefore g hgh hgJ
  apply rungOne n G D s hcol h4 hDL
  rw [hDJ]
  exact Finset.card_singleton g

lemma least_nonempty_graph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hL : IsLeastAO G C) (j : ℕ) (hj : j ∈ junk G C) :
    ∃ u v, G.Adj u v := by
  classical
  by_contra hn
  push Not at hn
  let D : Circuit := ⟨[], n⟩
  have hD : IsAO2 n D := by
    simp [IsAO2, AndOrOnly, ReadsBack, D]
  have hDF : circuitFun n D = graphFun G ∅ := by
    funext x
    simp [circuitFun, Circuit.eval, Circuit.wires, D, graphFun, hn,
      List.getD_eq_getElem?_getD]
  have hsize := hL.2.2 D hD hDF
  have hjlen := (mem_junk.mp hj).1
  simp only [Circuit.size, D, List.length_nil] at hsize
  omega

lemma later_has_two_essential_edges
    (rungOne : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (s : Fin n → Bool),
      (∀ u v, G.Adj u v → s u ≠ s v) → NoFourCycle G → IsLeastAO G C →
        (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (g h : ℕ)
    (hgh : g < h) (hJ : junk G C = {g, h}) :
    ∃ u v a b : Fin n, G.Adj u v ∧ G.Adj a b ∧
      circuitFun n (patch C h off) (pairInput u v) = false ∧
      circuitFun n (patch C h off) (pairInput a b) = false ∧
      pairInput u v ≠ pairInput a b := by
  classical
  have choose_other (u v : Fin n) (huv : G.Adj u v) :
      ∃ a b : Fin n, G.Adj a b ∧
        circuitFun n (patch C h off) (pairInput a b) = false ∧
        pairInput a b ≠ pairInput u v := by
    by_contra hn
    push Not at hn
    exact no_unique_later_edge rungOne G C s hcol h4 hL g h hgh hJ u v huv hn
  have hgJ : g ∈ junk G C := by simp [hJ]
  obtain ⟨u, v, huv⟩ := least_nonempty_graph G C hL g hgJ
  obtain ⟨a, b, hab, hlab, _⟩ := choose_other u v huv
  obtain ⟨c, d, hcd, hlcd, hne⟩ := choose_other a b hab
  exact ⟨a, b, c, d, hab, hcd, hlab, hlcd, hne.symm⟩

end PEqualNP.Outside.L_meta_5012_aux



namespace PEqualNP.Outside.L_meta_5012_aux.FourClauses

def matrixCode (R : Fin 3 → Fin 3 → Bool) : Nat :=
  (if R 0 1 then 1 else 0) + (if R 0 2 then 2 else 0) +
  (if R 1 0 then 4 else 0) + (if R 1 2 then 8 else 0) +
  (if R 2 0 then 16 else 0) + (if R 2 1 then 32 else 0)

def certificate (R : Fin 3 → Fin 3 → Bool) : List Nat :=
  match matrixCode R with
  | 0 => [7, 14, 21, 28, 35]
  | 1 => [7, 14, 28, 35, 42]
  | 2 => [7, 14, 21, 28, 42]
  | 3 => [7, 14, 28, 42, 56]
  | 4 => [7, 21, 28, 35, 49]
  | 6 => [7, 21, 28, 34, 56]
  | 8 => [7, 14, 21, 28, 49]
  | 9 => [7, 14, 28, 33, 56]
  | 10 => [7, 14, 21, 28, 56]
  | 12 => [7, 21, 28, 49, 56]
  | 16 => [7, 21, 35, 42, 49]
  | 17 => [7, 20, 35, 42, 56]
  | 20 => [7, 21, 35, 49, 56]
  | 24 => [7, 10, 21, 49, 56]
  | 25 => [7, 10, 20, 33, 56]
  | 32 => [7, 14, 35, 42, 49]
  | 33 => [7, 14, 35, 42, 56]
  | 34 => [7, 14, 17, 42, 56]
  | 36 => [7, 12, 35, 49, 56]
  | 38 => [7, 12, 17, 34, 56]
  | 48 => [7, 35, 42, 49, 56]
  | _ => []

def leftBit (R : Fin 3 → Fin 3 → Bool) (k : Fin 5) (i : Fin 3) : Bool :=
  Nat.testBit ((certificate R).getD k.val 0) i.val

def rightBit (R : Fin 3 → Fin 3 → Bool) (k : Fin 5) (i : Fin 3) : Bool :=
  Nat.testBit ((certificate R).getD k.val 0) (3 + i.val)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma certificate_valid : ∀ (R : Fin 3 → Fin 3 → Bool),
    (∀ i, R i i = true) →
    (∀ i i' j j', i ≠ i' → j ≠ j' →
      R i j = true → R i j' = true → R i' j = true → R i' j' = true → False) →
    (∀ k : Fin 5, ∀ i j : Fin 3,
      leftBit R k i = true → rightBit R k j = true → R i j = false) ∧
    (∀ k l : Fin 5, k ≠ l → ∃ i : Fin 3,
      (leftBit R k i = true ∧ rightBit R l i = true) ∨
      (rightBit R k i = true ∧ leftBit R l i = true)) := by
  decide

lemma independent_four_clauses (R : Fin 3 → Fin 3 → Bool)
    (diag : ∀ i, R i i = true)
    (no4 : ∀ i i' j j', i ≠ i' → j ≠ j' →
      R i j = true → R i j' = true → R i' j = true → R i' j' = true → False)
    (clause : Fin 4 → Fin 3 → Bool) :
    ∃ U V : Fin 3 → Bool,
      (∀ i j, U i = true → V j = true → R i j = false) ∧
      ∀ k, ∃ i, (U i = true ∧ clause k i = true) ∨
        (V i = true ∧ clause k i = false) := by
  classical
  obtain ⟨hind, hsep⟩ := certificate_valid R diag no4
  by_contra hn
  have hbad : ∀ t : Fin 5, ∃ k : Fin 4, ¬ ∃ i : Fin 3,
      (leftBit R t i = true ∧ clause k i = true) ∨
      (rightBit R t i = true ∧ clause k i = false) := by
    intro t
    by_contra ht
    apply hn
    refine ⟨leftBit R t, rightBit R t, hind t, ?_⟩
    intro k
    by_contra hk
    exact ht ⟨k, hk⟩
  choose f hf using hbad
  have hni : ¬ Function.Injective f :=
    Fintype.not_injective_of_card_lt f (by decide)
  have hex : ∃ t u : Fin 5, f t = f u ∧ t ≠ u := by
    by_contra h
    apply hni
    intro t u he
    by_contra htu
    exact h ⟨t, u, he, htu⟩
  obtain ⟨t, u, hfu, htu⟩ := hex
  obtain ⟨i, hcross⟩ := hsep t u htu
  cases hc : clause (f t) i with
  | false =>
    rcases hcross with h | h
    · exact hf u ⟨i, Or.inr ⟨h.2, by simpa [hfu] using hc⟩⟩
    · exact hf t ⟨i, Or.inr ⟨h.1, hc⟩⟩
  | true =>
    rcases hcross with h | h
    · exact hf t ⟨i, Or.inl ⟨h.1, hc⟩⟩
    · exact hf u ⟨i, Or.inl ⟨h.2, by simpa [hfu] using hc⟩⟩

end PEqualNP.Outside.L_meta_5012_aux.FourClauses


namespace PEqualNP.Outside.L_meta_5012_aux.FourClausePullback

open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

lemma no_four_edges {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : NoFourCycle G) (a b c d : Fin n) (hab : a ≠ b) (hcd : c ≠ d)
    (hac : G.Adj a c) (had : G.Adj a d) (hbc : G.Adj b c) (hbd : G.Adj b d) : False := by
  have hcard := h4 a b hab
  have hsub : ({c, d} : Finset (Fin n)) ⊆
      Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl
    · simp [hac, hbc]
    · simp [had, hbd]
  have hle := Finset.card_le_card hsub
  rw [Finset.card_pair hcd] at hle
  omega

lemma no_matching_of_finite
    (finite : ∀ (R : Fin 3 → Fin 3 → Bool),
      (∀ i, R i i = true) →
      (∀ i i' j j', i ≠ i' → j ≠ j' → R i j = true → R i j' = true →
        R i' j = true → R i' j' = true → False) →
      ∀ clause : Fin 4 → Fin 3 → Bool, ∃ U V : Fin 3 → Bool,
        (∀ i j, U i = true → V j = true → R i j = false) ∧
        ∀ k, ∃ i, (U i = true ∧ clause k i = true) ∨
          (V i = true ∧ clause k i = false))
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (A : Fin 4 → Finset (Fin n))
    (hclean : ∀ x : Fin n → Bool,
      (∀ k, ∃ u ∈ A k, x u = true) → graphFun G ∅ x = true)
    (left right : Fin 3 → Fin n)
    (hleft : Function.Injective left) (hright : Function.Injective right)
    (hleftcol : ∀ i, s (left i) = false) (hrightcol : ∀ i, s (right i) = true)
    (hedge : ∀ i, G.Adj (left i) (right i))
    (haccept : ∀ i k, left i ∈ A k ∨ right i ∈ A k) : False := by
  classical
  let R : Fin 3 → Fin 3 → Bool := fun i j => decide (G.Adj (left i) (right j))
  have hdiag : ∀ i, R i i = true := by
    intro i
    simpa [R] using hedge i
  have hR4 : ∀ i i' j j', i ≠ i' → j ≠ j' → R i j = true → R i j' = true →
      R i' j = true → R i' j' = true → False := by
    intro i i' j j' hii hjj hij hij' hi'j hi'j'
    apply no_four_edges G h4 (left i) (left i') (right j) (right j')
      (fun h => hii (hleft h)) (fun h => hjj (hright h))
    · simpa [R] using hij
    · simpa [R] using hij'
    · simpa [R] using hi'j
    · simpa [R] using hi'j'
  let clause : Fin 4 → Fin 3 → Bool := fun k i => decide (left i ∈ A k)
  obtain ⟨U, V, hindep, hhit⟩ := finite R hdiag hR4 clause
  let x : Fin n → Bool := fun v => decide
    ((∃ i, U i = true ∧ v = left i) ∨ (∃ i, V i = true ∧ v = right i))
  have hxleft (i : Fin 3) (hi : U i = true) : x (left i) = true := by
    simp only [x, decide_eq_true_eq]
    exact Or.inl ⟨i, hi, rfl⟩
  have hxright (i : Fin 3) (hi : V i = true) : x (right i) = true := by
    simp only [x, decide_eq_true_eq]
    exact Or.inr ⟨i, hi, rfl⟩
  have hall : ∀ k, ∃ u ∈ A k, x u = true := by
    intro k
    obtain ⟨i, h | h⟩ := hhit k
    · refine ⟨left i, ?_, hxleft i h.1⟩
      simpa [clause] using h.2
    · refine ⟨right i, ?_, hxright i h.1⟩
      have hnot : left i ∉ A k := by simpa [clause] using h.2
      exact (haccept i k).resolve_left hnot
  have hout := hclean x hall
  have hgraph : graphFun G ∅ x = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true := by simp [graphFun]
  obtain ⟨u, v, huv, hu, hv⟩ := hgraph.mp hout
  simp only [x, decide_eq_true_eq] at hu hv
  rcases hu with ⟨i, hi, rfl⟩ | ⟨i, hi, rfl⟩ <;>
    rcases hv with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · exact hcol _ _ huv ((hleftcol i).trans (hleftcol j).symm)
  · have hno := hindep i j hi hj
    have hyes : R i j = true := by simpa [R] using huv
    rw [hyes] at hno
    cases hno
  · have hno := hindep j i hj hi
    have hyes : R j i = true := by simpa [R] using huv.symm
    rw [hyes] at hno
    cases hno
  · exact hcol _ _ huv ((hrightcol i).trans (hrightcol j).symm)

end PEqualNP.Outside.L_meta_5012_aux.FourClausePullback

namespace PEqualNP.Outside.L_meta_5012_aux.FourClausePullback

open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

lemma no_three_disjoint_accepted_edges
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (A : Fin 4 → Finset (Fin n))
    (hclean : ∀ x : Fin n → Bool,
      (∀ k, ∃ u ∈ A k, x u = true) → graphFun G ∅ x = true) :
    ¬ ∃ left right : Fin 3 → Fin n,
      Function.Injective left ∧ Function.Injective right ∧
      (∀ i, s (left i) = false) ∧ (∀ i, s (right i) = true) ∧
      (∀ i, G.Adj (left i) (right i)) ∧
      (∀ i k, left i ∈ A k ∨ right i ∈ A k) := by
  rintro ⟨left, right, hl, hr, hlc, hrc, he, ha⟩
  exact no_matching_of_finite FourClauses.independent_four_clauses
    G s hcol h4 A hclean left right hl hr hlc hrc he ha

end PEqualNP.Outside.L_meta_5012_aux.FourClausePullback


namespace PEqualNP.Outside.L_meta_5012_aux.TwoCover

def NoThree {α : Type} (R : α → α → Prop) : Prop :=
  ∀ a c e b d f, a ≠ c → a ≠ e → c ≠ e → b ≠ d → b ≠ f → d ≠ f →
    R a b → R c d → R e f → False

lemma edge_touches {α : Type} {R : α → α → Prop} (h3 : NoThree R)
    {a c b d : α} (hac : a ≠ c) (hbd : b ≠ d) (hab : R a b) (hcd : R c d)
    {u v : α} (huv : R u v) : u = a ∨ u = c ∨ v = b ∨ v = d := by
  by_contra hn
  push Not at hn
  exact h3 a c u b d v hac hn.1.symm hn.2.1.symm hbd hn.2.2.1.symm
    hn.2.2.2.symm hab hcd huv

lemma cover_with_external {α : Type} [DecidableEq α] {R : α → α → Prop}
    (h3 : NoThree R) {a c b d x : α}
    (hac : a ≠ c) (hbd : b ≠ d) (hab : R a b) (hcd : R c d)
    (hax : R a x) (hxb : x ≠ b) (hxd : x ≠ d) :
    ∃ K : Finset α, K.card ≤ 2 ∧ ∀ u v, R u v → u ∈ K ∨ v ∈ K := by
  classical
  have no_b : ∀ u, u ≠ a → u ≠ c → ¬ R u b := by
    intro u hua huc hub
    exact h3 a c u x d b hac hua.symm huc.symm hxd hxb hbd.symm hax hcd hub
  by_cases hd : ∃ u, u ≠ a ∧ u ≠ c ∧ R u d
  · obtain ⟨l, hla, hlc, hld⟩ := hd
    have no_c_ext : ∀ v, v ≠ b → v ≠ d → ¬ R c v := by
      intro v hvb hvd hcv
      exact h3 a c l b v d hac hla.symm hlc.symm hvb.symm hbd hvd hab hcv hld
    have no_cb : ¬ R c b := by
      intro hcb
      exact h3 a c l x b d hac hla.symm hlc.symm hxb hxd hbd hax hcb hld
    refine ⟨{a, d}, Finset.card_le_two, ?_⟩
    intro u v huv
    by_cases hua : u = a
    · subst u; exact Or.inl (by simp)
    by_cases hvd : v = d
    · subst v; exact Or.inr (by simp)
    exfalso
    have hb : v = b := by
      by_contra hvb
      rcases edge_touches h3 hac hbd hab hcd huv with h | h | h | h
      · exact hua h
      · subst u; exact no_c_ext v hvb hvd huv
      · exact hvb h
      · exact hvd h
    subst v
    by_cases huc : u = c
    · subst u; exact no_cb huv
    · exact no_b u hua huc huv
  · refine ⟨{a, c}, Finset.card_le_two, ?_⟩
    intro u v huv
    by_cases hua : u = a
    · subst u; exact Or.inl (by simp)
    by_cases huc : u = c
    · subst u; exact Or.inl (by simp)
    exfalso
    rcases edge_touches h3 hac hbd hab hcd huv with h | h | h | h
    · exact hua h
    · exact huc h
    · subst v; exact no_b u hua huc huv
    · subst v; exact hd ⟨u, hua, huc, huv⟩

lemma cover_of_two_edges {α : Type} [DecidableEq α] {R : α → α → Prop}
    (h3 : NoThree R) {a c b d : α}
    (hac : a ≠ c) (hbd : b ≠ d) (hab : R a b) (hcd : R c d) :
    ∃ K : Finset α, K.card ≤ 2 ∧ ∀ u v, R u v → u ∈ K ∨ v ∈ K := by
  classical
  by_cases ha : ∃ x, x ≠ b ∧ x ≠ d ∧ R a x
  · obtain ⟨x, hxb, hxd, hax⟩ := ha
    exact cover_with_external h3 hac hbd hab hcd hax hxb hxd
  by_cases hc : ∃ x, x ≠ b ∧ x ≠ d ∧ R c x
  · obtain ⟨x, hxb, hxd, hcx⟩ := hc
    exact cover_with_external h3 hac.symm hbd.symm hcd hab hcx hxd hxb
  refine ⟨{b, d}, Finset.card_le_two, ?_⟩
  intro u v huv
  by_cases hvb : v = b
  · subst v; exact Or.inr (by simp)
  by_cases hvd : v = d
  · subst v; exact Or.inr (by simp)
  exfalso
  rcases edge_touches h3 hac hbd hab hcd huv with h | h | h | h
  · subst u; exact ha ⟨v, hvb, hvd, huv⟩
  · subst u; exact hc ⟨v, hvb, hvd, huv⟩
  · exact hvb h
  · exact hvd h

lemma cover_of_noThree {α : Type} [DecidableEq α] {R : α → α → Prop}
    (h3 : NoThree R) :
    ∃ K : Finset α, K.card ≤ 2 ∧ ∀ u v, R u v → u ∈ K ∨ v ∈ K := by
  classical
  by_cases he : ∃ a b, R a b
  · obtain ⟨a, b, hab⟩ := he
    by_cases hcover : ∀ u v, R u v → u = a ∨ v = b
    · refine ⟨{a, b}, Finset.card_le_two, ?_⟩
      intro u v huv
      rcases hcover u v huv with rfl | rfl <;> simp
    · push Not at hcover
      obtain ⟨c, d, hcd, hca, hdb⟩ := hcover
      exact cover_of_two_edges h3 hca.symm hdb.symm hab hcd
  · refine ⟨∅, by simp, ?_⟩
    intro u v huv
    exact False.elim (he ⟨u, v, huv⟩)

lemma triple_injective {α : Type} (a b c : α) (hab : a ≠ b) (hac : a ≠ c)
    (hbc : b ≠ c) : Function.Injective ![a, b, c] := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> simp_all

lemma bipartite_relation_cover_of_no_matching_three {α : Type} [DecidableEq α]
    (P : α → α → Prop) (hsymm : ∀ u v, P u v → P v u)
    (s : α → Bool) (hcol : ∀ u v, P u v → s u ≠ s v)
    (h3 : ¬ ∃ left right : Fin 3 → α,
      Function.Injective left ∧ Function.Injective right ∧
      (∀ i, s (left i) = false) ∧ (∀ i, s (right i) = true) ∧
      ∀ i, P (left i) (right i)) :
    ∃ K : Finset α, K.card ≤ 2 ∧ ∀ u v, P u v → u ∈ K ∨ v ∈ K := by
  classical
  let R : α → α → Prop := fun u v => P u v ∧ s u = false ∧ s v = true
  have hR3 : NoThree R := by
    intro a c e b d f hac hae hce hbd hbf hdf hab hcd hef
    apply h3
    refine ⟨![a, c, e], ![b, d, f], triple_injective _ _ _ hac hae hce,
      triple_injective _ _ _ hbd hbf hdf, ?_, ?_, ?_⟩
    · intro i; fin_cases i <;> simp_all [R]
    · intro i; fin_cases i <;> simp_all [R]
    · intro i; fin_cases i <;> simp_all [R]
  obtain ⟨K, hcard, hcov⟩ := cover_of_noThree hR3
  refine ⟨K, hcard, ?_⟩
  intro u v huv
  have hneq := hcol u v huv
  cases hu : s u <;> cases hv : s v
  · exact False.elim (hneq (hu.trans hv.symm))
  · exact hcov u v ⟨huv, hu, hv⟩
  · exact (hcov v u ⟨hsymm u v huv, hv, hu⟩).symm
  · exact False.elim (hneq (hu.trans hv.symm))

lemma bipartite_cover_of_no_matching_three {n : ℕ} (G : SimpleGraph (Fin n))
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h3 : ¬ ∃ left right : Fin 3 → Fin n,
      Function.Injective left ∧ Function.Injective right ∧
      (∀ i, s (left i) = false) ∧ (∀ i, s (right i) = true) ∧
      ∀ i, G.Adj (left i) (right i)) :
    ∃ K : Finset (Fin n), K.card ≤ 2 ∧ ∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K :=
  bipartite_relation_cover_of_no_matching_three G.Adj (fun _ _ h => h.symm) s hcol h3

end PEqualNP.Outside.L_meta_5012_aux.TwoCover

namespace PEqualNP.Outside.L_meta_5012_aux.FourClausePullback

open PEqualNP.TopForm PEqualNP.MetaComplexity.NestedCover

lemma two_center_cover
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (A : Fin 4 → Finset (Fin n))
    (hclean : ∀ x : Fin n → Bool,
      (∀ k, ∃ u ∈ A k, x u = true) → graphFun G ∅ x = true) :
    ∃ K : Finset (Fin n), K.card ≤ 2 ∧
      ∀ u v, G.Adj u v → (∀ k, u ∈ A k ∨ v ∈ A k) → u ∈ K ∨ v ∈ K := by
  classical
  let H : SimpleGraph (Fin n) :=
    { Adj := fun u v => G.Adj u v ∧ ∀ k, u ∈ A k ∨ v ∈ A k
      symm := by
        constructor
        intro u v h
        exact ⟨h.1.symm, fun k => (h.2 k).symm⟩
      loopless := by
        constructor
        intro u h
        simpa using h.1 }
  have hHcol : ∀ u v, H.Adj u v → s u ≠ s v := fun u v h => hcol u v h.1
  have hH3 : ¬ ∃ left right : Fin 3 → Fin n,
      Function.Injective left ∧ Function.Injective right ∧
      (∀ i, s (left i) = false) ∧ (∀ i, s (right i) = true) ∧
      ∀ i, H.Adj (left i) (right i) := by
    rintro ⟨left, right, hl, hr, hlc, hrc, he⟩
    exact no_three_disjoint_accepted_edges G s hcol h4 A hclean
      ⟨left, right, hl, hr, hlc, hrc, fun i => (he i).1, fun i => (he i).2⟩
  obtain ⟨K, hKcard, hKcover⟩ := TwoCover.bipartite_cover_of_no_matching_three H s hHcol hH3
  exact ⟨K, hKcard, fun u v he ha => hKcover u v ⟨he, ha⟩⟩

lemma clean_two_products_two_center_cover
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (A B C D : Finset (Fin n))
    (hclean : ∀ x : Fin n → Bool,
      (∃ a ∈ A, x a = true) → (∃ b ∈ B, x b = true) →
      (∃ c ∈ C, x c = true) → (∃ d ∈ D, x d = true) → graphFun G ∅ x = true) :
    ∃ K : Finset (Fin n), K.card ≤ 2 ∧
      ∀ u v, G.Adj u v → (u ∈ A ∨ v ∈ A) → (u ∈ B ∨ v ∈ B) →
        (u ∈ C ∨ v ∈ C) → (u ∈ D ∨ v ∈ D) → u ∈ K ∨ v ∈ K := by
  obtain ⟨K, hKcard, hKcover⟩ := two_center_cover G s hcol h4 ![A, B, C, D] (by
    intro x hx
    exact hclean x (hx 0) (hx 1) (hx 2) (hx 3))
  refine ⟨K, hKcard, ?_⟩
  intro u v he hA hB hC hD
  apply hKcover u v he
  intro k
  fin_cases k <;> simp_all

end PEqualNP.Outside.L_meta_5012_aux.FourClausePullback
