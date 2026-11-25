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


namespace PEqualNP.Outside.L_meta_5012_aux.Cost

open PEqualNP.TopForm

lemma edge_union_of_pair_cover {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (a b : Fin n)
    (hcover : ∀ u v, G.Adj u v → u = a ∨ u = b ∨ v = a ∨ v = b) :
    G.edgeFinset = G.incidenceFinset a ∪ G.incidenceFinset b := by
  classical
  ext e
  induction e using Sym2.inductionOn with
  | _ u v =>
    simp only [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet,
      Finset.mem_union, SimpleGraph.mem_incidenceFinset,
      SimpleGraph.mk'_mem_incidenceSet_iff]
    constructor
    · intro huv
      have h := hcover u v huv
      rcases h with rfl | rfl | rfl | rfl <;> simp_all
    · rintro (h | h) <;> exact h.1

lemma star_edge_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (S : Finset (Fin n)) (hS : ∀ u v, G.Adj u v → u ∈ S ∧ v ∈ S)
    (hne : ∃ u v, G.Adj u v) (a : Fin n)
    (hcover : ∀ u v, G.Adj u v → u = a ∨ v = a) :
    G.edgeFinset.card + 1 ≤ S.card := by
  classical
  have heq : G.edgeFinset = G.incidenceFinset a := by
    simpa using edge_union_of_pair_cover G a a (by
      intro u v huv
      rcases hcover u v huv with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr (Or.inl h)))
  have haS : a ∈ S := by
    obtain ⟨u, v, huv⟩ := hne
    rcases hcover u v huv with rfl | rfl
    · exact (hS _ _ huv).1
    · exact (hS _ _ huv).2
  have hsub : insert a (G.neighborFinset a) ⊆ S := by
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact haS
    · exact (hS a x (G.mem_neighborFinset a x |>.mp hx)).2
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_insert_of_notMem (G.notMem_neighborFinset_self a)] at hcard
  have hedgecard : G.edgeFinset.card = (G.neighborFinset a).card := by
    rw [heq, G.card_incidenceFinset_eq_degree]
    rfl
  rwa [← hedgecard] at hcard

lemma pair_cover_edge_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (S : Finset (Fin n))
    (hS : ∀ u v, G.Adj u v → u ∈ S ∧ v ∈ S)
    (hne : ∃ u v, G.Adj u v) (a b : Fin n)
    (hcover : ∀ u v, G.Adj u v → u = a ∨ u = b ∨ v = a ∨ v = b) :
    G.edgeFinset.card + 1 ≤ S.card := by
  classical
  by_cases hab : a = b
  · subst b
    apply star_edge_bound G S hS hne a
    intro u v huv
    rcases hcover u v huv with h | h | h | h
    · exact Or.inl h
    · exact Or.inl h
    · exact Or.inr h
    · exact Or.inr h
  by_cases ha : ∃ u, G.Adj a u
  swap
  · apply star_edge_bound G S hS hne b
    intro u v huv
    rcases hcover u v huv with rfl | rfl | rfl | rfl
    · exact False.elim (ha ⟨v, huv⟩)
    · exact Or.inl rfl
    · exact False.elim (ha ⟨u, huv.symm⟩)
    · exact Or.inr rfl
  by_cases hb : ∃ u, G.Adj b u
  swap
  · apply star_edge_bound G S hS hne a
    intro u v huv
    rcases hcover u v huv with rfl | rfl | rfl | rfl
    · exact Or.inl rfl
    · exact False.elim (hb ⟨v, huv⟩)
    · exact Or.inr rfl
    · exact False.elim (hb ⟨u, huv.symm⟩)
  have haS : a ∈ S := by obtain ⟨u, hu⟩ := ha; exact (hS a u hu).1
  have hbS : b ∈ S := by obtain ⟨u, hu⟩ := hb; exact (hS b u hu).1
  have hneigh : G.neighborFinset a ∪ G.neighborFinset b ⊆ S := by
    intro u hu
    rcases Finset.mem_union.mp hu with hu | hu
    · exact (hS a u (G.mem_neighborFinset a u |>.mp hu)).2
    · exact (hS b u (G.mem_neighborFinset b u |>.mp hu)).2
  have hedge := edge_union_of_pair_cover G a b hcover
  have hsum : G.edgeFinset.card ≤
      (G.neighborFinset a).card + (G.neighborFinset b).card := by
    rw [hedge]
    simpa only [SimpleGraph.card_incidenceFinset_eq_degree, SimpleGraph.degree] using
      Finset.card_union_le (G.incidenceFinset a) (G.incidenceFinset b)
  by_cases hadj : G.Adj a b
  · have hd : Disjoint (G.neighborFinset a) (G.neighborFinset b) := by
      rw [Finset.disjoint_left]
      intro u hua hub
      have hau := G.mem_neighborFinset a u |>.mp hua
      have hbu := G.mem_neighborFinset b u |>.mp hub
      have habc := hcol a b hadj
      have hauc := hcol a u hau
      have hbuc := hcol b u hbu
      cases sa : s a <;> cases sb : s b <;> cases su : s u <;> simp_all
    have hinc : G.incidenceFinset a ∩ G.incidenceFinset b = {s(a, b)} := by
      apply Finset.coe_injective
      simp only [Finset.coe_inter, SimpleGraph.coe_incidenceFinset, Finset.coe_singleton]
      exact G.incidenceSet_inter_incidenceSet_of_adj hadj
    have heq := Finset.card_union_add_card_inter (G.incidenceFinset a) (G.incidenceFinset b)
    rw [← hedge, hinc, Finset.card_singleton] at heq
    have hcard := Finset.card_le_card hneigh
    rw [Finset.card_union_of_disjoint hd] at hcard
    simp only [SimpleGraph.card_incidenceFinset_eq_degree, SimpleGraph.degree] at heq
    omega
  · have hcommon : (G.neighborFinset a ∩ G.neighborFinset b).card ≤ 1 := by
      have heq : G.neighborFinset a ∩ G.neighborFinset b =
          Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w) := by
        ext w
        simp
      rw [heq]
      exact h4 a b hab
    have haN : a ∉ G.neighborFinset a ∪ G.neighborFinset b := by
      simp [hadj, SimpleGraph.adj_comm]
    have hbN : b ∉ G.neighborFinset a ∪ G.neighborFinset b := by
      simp [hadj]
    have hsub : insert a (insert b (G.neighborFinset a ∪ G.neighborFinset b)) ⊆ S :=
      Finset.insert_subset haS (Finset.insert_subset hbS hneigh)
    have hcard := Finset.card_le_card hsub
    rw [Finset.card_insert_of_notMem (by simpa using And.intro hab haN),
      Finset.card_insert_of_notMem hbN] at hcard
    have hsumN := Finset.card_union_add_card_inter (G.neighborFinset a) (G.neighborFinset b)
    omega

lemma two_cover_edge_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (S K : Finset (Fin n))
    (hS : ∀ u v, G.Adj u v → u ∈ S ∧ v ∈ S)
    (hne : G.edgeFinset.Nonempty) (hK : K.card ≤ 2)
    (hcover : ∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K) :
    G.edgeFinset.card + 1 ≤ S.card := by
  classical
  have he : ∃ u v, G.Adj u v := G.ne_bot_iff_exists_adj.mp (G.edgeFinset_nonempty.mp hne)
  have hKpos : 0 < K.card := by
    obtain ⟨u, v, huv⟩ := he
    rcases hcover u v huv with hu | hv
    · exact Finset.card_pos.mpr ⟨u, hu⟩
    · exact Finset.card_pos.mpr ⟨v, hv⟩
  by_cases hK1 : K.card = 1
  · obtain ⟨a, hKa⟩ := Finset.card_eq_one.mp hK1
    apply star_edge_bound G S hS he a
    intro u v huv
    simpa [hKa] using hcover u v huv
  · have hK2 : K.card = 2 := by omega
    obtain ⟨a, b, _, hKab⟩ := Finset.card_eq_two.mp hK2
    apply pair_cover_edge_bound G s hcol h4 S hS he a b
    intro u v huv
    simpa [hKab, or_assoc] using hcover u v huv

lemma two_cover_support_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (K : Finset (Fin n))
    (hne : G.edgeFinset.Nonempty) (hK : K.card ≤ 2)
    (hcover : ∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K) :
    G.edgeFinset.card + 1 ≤ G.support.toFinset.card := by
  classical
  apply two_cover_edge_bound G s hcol h4 G.support.toFinset K ?_ hne hK hcover
  intro u v huv
  simp only [Set.mem_toFinset, SimpleGraph.mem_support]
  exact ⟨⟨v, huv⟩, ⟨u, huv.symm⟩⟩

end PEqualNP.Outside.L_meta_5012_aux.Cost


namespace PEqualNP.Outside.L_meta_5012_aux.MixedGeometry

open PEqualNP.MetaComplexity.NestedCover

def inputOf {n : ℕ} (S : Finset (Fin n)) : Fin n → Bool := fun v => decide (v ∈ S)

lemma independent_three {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (a b d : Fin n) (hsame : s b = s d) (hab : ¬ G.Adj a b) (had : ¬ G.Adj a d) :
    graphFun G ∅ (inputOf {a, b, d}) = false := by
  have hnone : ¬ ∃ u v, G.Adj u v ∧ inputOf {a, b, d} u = true ∧
      inputOf {a, b, d} v = true := by
    rintro ⟨u, v, huv, hu, hv⟩
    simp only [inputOf, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton] at hu hv
    rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
    · exact hcol _ _ huv rfl
    · exact hab huv
    · exact had huv
    · exact hab huv.symm
    · exact hcol _ _ huv rfl
    · exact hcol _ _ huv hsame
    · exact had huv.symm
    · exact hcol _ _ huv hsame.symm
    · exact hcol _ _ huv rfl
  simpa [graphFun] using hnone

lemma clean_four_factor_missing_side
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (A B C D : Finset (Fin n))
    (hclean : ∀ x : Fin n → Bool,
      (∃ a ∈ A, x a = true) → (∃ b ∈ B, x b = true) →
      (∃ c ∈ C, x c = true) → (∃ d ∈ D, x d = true) → graphFun G ∅ x = true)
    (u b : Fin n) (huA : u ∈ A) (huC : u ∈ C) (hbB : b ∈ B)
    (hub : ¬ G.Adj u b) :
    u ∉ D ∧ b ∉ D ∧ ∀ d ∈ D, s d = s b → G.Adj u d := by
  have pairFalse : graphFun G ∅ (inputOf {u, b, b}) = false :=
    independent_three G s hcol u b b rfl hub hub
  have hu_true : inputOf {u, b, b} u = true := by simp [inputOf]
  have hb_true : inputOf {u, b, b} b = true := by simp [inputOf]
  have huD : u ∉ D := by
    intro huD
    have hh := hclean (inputOf {u, b, b}) ⟨u, huA, hu_true⟩ ⟨b, hbB, hb_true⟩
      ⟨u, huC, hu_true⟩ ⟨u, huD, hu_true⟩
    rw [pairFalse] at hh
    cases hh
  have hbD : b ∉ D := by
    intro hbD
    have hh := hclean (inputOf {u, b, b}) ⟨u, huA, hu_true⟩ ⟨b, hbB, hb_true⟩
      ⟨u, huC, hu_true⟩ ⟨b, hbD, hb_true⟩
    rw [pairFalse] at hh
    cases hh
  refine ⟨huD, hbD, ?_⟩
  intro d hd hsame
  by_contra hno
  have hfalse := independent_three G s hcol u b d hsame.symm hub hno
  have htrue := hclean (inputOf {u, b, d})
    ⟨u, huA, by simp [inputOf]⟩ ⟨b, hbB, by simp [inputOf]⟩
    ⟨u, huC, by simp [inputOf]⟩ ⟨d, hd, by simp [inputOf]⟩
  rw [hfalse] at htrue
  cases htrue

lemma clean_four_factor_star_choice
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (A B C D : Finset (Fin n))
    (hclean : ∀ x : Fin n → Bool,
      (∃ a ∈ A, x a = true) → (∃ b ∈ B, x b = true) →
      (∃ c ∈ C, x c = true) → (∃ d ∈ D, x d = true) → graphFun G ∅ x = true)
    (u : Fin n) (huA : u ∈ A) (huC : u ∈ C) (color : Bool)
    (hB : ∀ b ∈ B, s b = color) :
    (∀ b ∈ B, G.Adj u b) ∨
      (u ∉ D ∧ ∀ d ∈ D, s d = color → G.Adj u d) := by
  classical
  by_cases h : ∀ b ∈ B, G.Adj u b
  · exact Or.inl h
  · push Not at h
    obtain ⟨b, hb, hub⟩ := h
    obtain ⟨huD, _, hD⟩ := clean_four_factor_missing_side G s hcol A B C D hclean u b huA huC hb hub
    exact Or.inr ⟨huD, fun d hd hc => hD d hd (hc.trans (hB b hb).symm)⟩

end PEqualNP.Outside.L_meta_5012_aux.MixedGeometry

namespace PEqualNP.Outside.L_meta_5012_aux.Mixed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_stepWire_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

lemma foldl_stepWire_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_length (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepWire_length, List.length_ofFn]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]


def W (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD u false

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma W_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length) :
    W n C x (n + k) = (gateAt C k).op.eval ((gateAt C k).inputs.map fun i =>
      if i < n + k then W n C x i else false) := by
  obtain ⟨pre, post, gj, hgs, hpre_len, hgj⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gj := by rw [gateAt_eq C k hk]; exact hgj
  rw [hga]
  let w0 := pre.foldl stepWire (List.ofFn x)
  have hw0_len : w0.length = n + k := by
    simp [w0, foldl_stepWire_length, hpre_len]
  have hCj : W n C x (n + k) = gj.op.eval (gj.inputs.map fun i => w0.getD i false) := by
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append, List.foldl_cons]
    rw [foldl_stepWire_getD_lt post (stepWire w0 gj) (n + k) (by simp [stepWire]; omega)]
    simp [stepWire, List.getD_eq_getElem?_getD, hw0_len]
  rw [hCj]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  by_cases hi : i < n + k
  · simp only [hi, ↓reduceIte]
    simp only [W]
    rw [wires_eq_foldl, hgs, List.foldl_append]
    exact (foldl_stepWire_getD_lt (gj :: post) w0 i (by omega)).symm
  · simp only [hi, ↓reduceIte]
    exact getD_ge_length w0 i (by omega)

lemma W_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (u : ℕ) (hu : u < n) :
    W n C x u = x ⟨u, hu⟩ := by
  simp only [W]
  rw [wires_eq_foldl, foldl_stepWire_getD_lt C.gates (List.ofFn x) u (by simpa using hu)]
  simp [List.getD_eq_getElem?_getD, hu]

open PEqualNP.CleanedNonEdge in
lemma orFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [orStep]
    omega

open PEqualNP.CleanedNonEdge in
lemma orStep_mem_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) (x : ℕ) :
    x ∈ (orStep n cs g).getD cs.length [] ↔ x = cs.length ∨ (g.op = GateOp.or ∧
      ∃ w ∈ g.inputs, n ≤ w ∧ w < n + cs.length ∧ x ∈ cs.getD (w - n) []) := by
  by_cases h : g.op = GateOp.or
  · simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right le_rfl, h,
      ↓reduceIte, true_and, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some,
      List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (h1 | ⟨w, ⟨hw, hn, hlt⟩, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, hw, hn, hlt, hx⟩
    · rintro (h1 | ⟨w, hw, hn, hlt, hx⟩)
      · exact Or.inl h1
      · exact Or.inr ⟨w, ⟨hw, hn, hlt⟩, hx⟩
  · simp [orStep, List.getD_eq_getElem?_getD, h]

open PEqualNP.CleanedNonEdge in
lemma orStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (orStep n cs g).getD m [] = cs.getD m [] := by
  simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.CleanedNonEdge in
lemma orFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (orStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (orStep n cs g) (by simp [orStep]; omega)]
    exact orStep_getD_lt n cs g k hk

open PEqualNP.CleanedNonEdge in
lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧ x ∈ (orSets n C).getD (w - n) []) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : orSets n C = post.foldl (orStep n) (orStep n (pre.foldl (orStep n) []) gk) := by
    simp only [orSets]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (orStep n) []).length = k := by
    rw [orFold_length]; simp [hpre_len]
  have hl1 : (orStep n (pre.foldl (orStep n) []) gk).length = k + 1 := by
    simp [orStep, hl0]
  have h1 : (orSets n C).getD k [] = (orStep n (pre.foldl (orStep n) []) gk).getD k [] := by
    rw [hc, orFold_getD_lt n post _ k (by omega)]
  have h2 : ∀ m, m < k → (orSets n C).getD m [] = (pre.foldl (orStep n) []).getD m [] := by
    intro m hm
    rw [hc, orFold_getD_lt n post _ m (by omega)]
    exact orStep_getD_lt n _ gk m (by omega)
  have h3 := orStep_mem_last n (pre.foldl (orStep n) []) gk x
  rw [hl0] at h3
  rw [h1, h3]
  constructor
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [h2 (w - n) (by omega)]; exact hx⟩
  · rintro (h | ⟨hop, w, hw, hn, hlt, hx⟩)
    · exact Or.inl h
    · exact Or.inr ⟨hop, w, hw, hn, hlt, by rw [← h2 (w - n) (by omega)]; exact hx⟩


lemma W_or (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.or) (i : ℕ) (hi : i ∈ (gateAt C r).inputs)
    (hlt : i < n + r) (hv : W n C x i = true) : W n C x (n + r) = true := by
  rw [W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  exact ⟨i, hi, by rw [ite_eq_left hlt]; exact hv⟩

lemma W_and (n : ℕ) (C : Circuit) (x : Fin n → Bool) (r : ℕ) (hr : r < C.gates.length)
    (hop : (gateAt C r).op = GateOp.and)
    (h : ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ W n C x i = true) :
    W n C x (n + r) = true := by
  rw [W_gate n C x r hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  intro i hi
  rw [ite_eq_left (h i hi).1]; exact (h i hi).2

open PEqualNP.CleanedNonEdge in
lemma reach_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (g : ℕ)
    (hv : W n C x (n + g) = true) :
    ∀ k, k < C.gates.length → g ∈ (orSets n C).getD k [] → W n C x (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hmem
    rcases (orSets_mem_iff n C k g hk).mp hmem with h | ⟨hop, w, hw, hn, hlt, hx⟩
    · rw [← h]; exact hv
    · have h3 := ih (w - n) (by omega) (by omega) hx
      have e : n + (w - n) = w := by omega
      rw [e] at h3
      exact W_or n C x k hk hop w hw hlt h3

open PEqualNP.CleanedNonEdge in
lemma reach_up (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w g : ℕ)
    (h : OrReaches n C w g) (hv : W n C x (n + g) = true) : W n C x w = true := by
  obtain ⟨hn, hmem⟩ := h
  by_cases hk : w - n < C.gates.length
  · have h3 := reach_val n C x g hv (w - n) hk hmem
    have e : n + (w - n) = w := by omega
    rw [e] at h3
    exact h3
  · exfalso
    have hlen : (orSets n C).length = C.gates.length := by
      unfold orSets; rw [orFold_length]; simp
    have hge : (orSets n C).length ≤ w - n := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hmem
    simp at hmem

lemma mem_filter_gen {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α)
    (h : a ∈ @Finset.filter α p d s) : p a :=
  ((@Finset.mem_filter α p d s a).mp h).2

lemma side_val (n : ℕ) (C : Circuit) (x : Fin n → Bool) (j : ℕ) (b : Fin 2) (i : Fin n)
    (hi : i ∈ PEqualNP.TopForm.side (n := n) C j b) (hx : x i = true) :
    W n C x (PEqualNP.TopForm.opnd C j b) = true := by
  unfold PEqualNP.TopForm.side PEqualNP.TopForm.orIn at hi
  have hi2 := mem_filter_gen _ _ _ _ hi
  rcases hi2 with h | ⟨k, hk, hreach, hop, hin⟩
  · rw [← h, W_input n C x i.val i.isLt]; exact hx
  · have hk1 : W n C x (n + k) = true := by
      apply W_or n C x k hk hop i.val hin (by have := i.isLt; omega)
      rw [W_input n C x i.val i.isLt]; exact hx
    exact reach_up n C x _ k hreach hk1

open PEqualNP.EdgeOwnership in
lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3


lemma gateAt_mem' (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq C j hj]; exact List.getElem_mem hj

open PEqualNP.EdgeOwnership in
lemma inCone_lt (n : ℕ) (C : Circuit) : ∀ j i, InCone n C i j → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro i h
    obtain ⟨_, k, hk, _, h3⟩ := (inCone_iff n C i j).mp h
    rcases h3 with h3 | h3
    · omega
    · have := ih k hk i h3; omega

open PEqualNP.CleanedNonEdge in
lemma orReach_trans (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (w : ℕ) (hw : w ∈ (gateAt C k).inputs)
    (hlt : w < n + k) (g : ℕ) (h : OrReaches n C w g) : OrReaches n C (n + k) g := by
  obtain ⟨hn, hmem⟩ := h
  refine ⟨by omega, ?_⟩
  have e : n + k - n = k := by omega
  rw [e]
  exact (orSets_mem_iff n C k g hk).mpr (Or.inr ⟨hop, w, hw, hn, hlt, hmem⟩)

open PEqualNP.CleanedNonEdge in
lemma orReach_self (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    OrReaches n C (n + k) k := by
  refine ⟨by omega, ?_⟩
  have e : n + k - n = k := by omega
  rw [e]
  exact (orSets_mem_iff n C k k hk).mpr (Or.inl rfl)

lemma orIn_mem (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

open PEqualNP.CleanedNonEdge in
lemma down (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (hAO : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ w, W n C x w = true → (∃ i : Fin n, i ∈ PEqualNP.TopForm.orIn n C w ∧ x i = true) ∨
      ∃ k, k < C.gates.length ∧ OrReaches n C w k ∧ (gateAt C k).op = GateOp.and ∧
        W n C x (n + k) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hwn : w < n
    · left
      refine ⟨⟨w, hwn⟩, (orIn_mem n C w _).mpr (Or.inl rfl), ?_⟩
      rw [← W_input n C x w hwn]; exact hv
    · by_cases hk : w - n < C.gates.length
      · have hw : w = n + (w - n) := by omega
        set k := w - n with hkdef
        rcases hAO k hk with hop | hop
        · right
          refine ⟨k, hk, ?_, hop, ?_⟩
          · rw [hw]; exact orReach_self n C k hk
          · rw [← hw]; exact hv
        · have hv2 := hv
          rw [hw, W_gate n C x k hk, hop] at hv2
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hv2
          obtain ⟨i, hi, hiv⟩ := hv2
          split_ifs at hiv with hlt
          rcases ih i (by omega) hiv with ⟨j, hj, hxj⟩ | ⟨k', hk', hr, hop', hv'⟩
          · left
            refine ⟨j, ?_, hxj⟩
            rw [orIn_mem] at hj ⊢
            right
            rcases hj with hj | ⟨k'', hk'', hr, hop'', hin⟩
            · refine ⟨k, hk, ?_, hop, ?_⟩
              · rw [hw]; exact orReach_self n C k hk
              · rw [hj]; exact hi
            · refine ⟨k'', hk'', ?_, hop'', hin⟩
              rw [hw]; exact orReach_trans n C k hk hop i hi hlt k'' hr
          · right
            refine ⟨k', hk', ?_, hop', hv'⟩
            rw [hw]; exact orReach_trans n C k hk hop i hi hlt k' hr
      · exfalso
        have hl := wires_length n C x
        have : W n C x w = false := getD_ge_length _ w (by omega)
        rw [this] at hv; exact Bool.false_ne_true hv

open PEqualNP.EdgeOwnership in
lemma orSets_cone (n : ℕ) (C : Circuit) : ∀ m, m < C.gates.length → ∀ k,
    k ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD m [] → k = m ∨ InCone n C k m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm k hk
    rcases (orSets_mem_iff n C m k hm).mp hk with h | ⟨_, w, hw, hn, hlt, hx⟩
    · exact Or.inl h
    · right
      have h2 := ih (w - n) (by omega) (by omega) k hx
      have e : n + (w - n) = w := by omega
      exact (inCone_iff n C k m).mpr ⟨hm, w - n, by omega, by rw [e]; exact hw, h2⟩

open PEqualNP.EdgeOwnership in
lemma reach_cone (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (o : ℕ)
    (ho : o ∈ (gateAt C j).inputs) (hlt : o < n + j) (k : ℕ)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C o k) : InCone n C k j := by
  obtain ⟨hn, hmem⟩ := h
  have h2 := orSets_cone n C (o - n) (by omega) k hmem
  have e : n + (o - n) = o := by omega
  exact (inCone_iff n C k j).mpr ⟨hj, o - n, by omega, by rw [e]; exact ho, h2⟩


open PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm

def monoInput {n : ℕ} (s : Fin n → Bool) (c : Bool) : Fin n → Bool :=
  fun u => decide (s u = c)

lemma monoInput_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v) (c : Bool) :
    graphFun G ∅ (monoInput s c) = false := by
  have hn : ¬ ∃ u v, G.Adj u v ∧ monoInput s c u = true ∧ monoInput s c v = true := by
    rintro ⟨u, v, huv, hu, hv⟩
    have hu' : s u = c := by simpa [monoInput] using hu
    have hv' : s v = c := by simpa [monoInput] using hv
    exact hcol u v huv (hu'.trans hv'.symm)
  simp [graphFun, hn]

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b ∈ (gateAt C a).inputs := by
  have hlen := hAO.2.2 _ (gateAt_mem' C a ha)
  unfold opnd
  have hb : b.val < (gateAt C a).inputs.length := by omega
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hb, Option.getD_some]
  exact List.getElem_mem hb

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {a : ℕ} (ha : a < C.gates.length) (b : Fin 2) :
    opnd C a b < n + a := hAO.2.1 a ha _ (opnd_mem hAO ha b)

lemma mem_inputs_iff_opnd {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {a : ℕ} (ha : a < C.gates.length) (w : ℕ) :
    w ∈ (gateAt C a).inputs ↔ ∃ b : Fin 2, opnd C a b = w := by
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hAO.2.2 _ (gateAt_mem' C a ha))
  constructor
  · intro hw
    rw [hin] at hw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact ⟨0, by simp [opnd, hin]⟩
    · exact ⟨1, by simp [opnd, hin]⟩
  · rintro ⟨b, rfl⟩
    exact opnd_mem hAO ha b

lemma and_two {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {a : ℕ} (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (b : Fin 2) (x : Fin n → Bool)
    (hb : W n C x (opnd C a b) = true)
    (hc : W n C x (opnd C a (1 - b)) = true) :
    gateVal n C a x = true := by
  apply W_and n C x a ha hand
  intro w hw
  obtain ⟨d, rfl⟩ := (mem_inputs_iff_opnd hAO ha w).mp hw
  refine ⟨opnd_lt hAO ha d, ?_⟩
  have hd : d = b ∨ d = 1 - b := by fin_cases b <;> fin_cases d <;> decide
  rcases hd with rfl | rfl
  · exact hb
  · exact hc

lemma wire_all_true {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) :
    ∀ w, w < n + C.gates.length → W n C (fun _ => true) w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · rw [W_input n C _ w hn]
    · have hk : w - n < C.gates.length := by omega
      have heq : w = n + (w - n) := by omega
      rcases hAO.1 _ (gateAt_mem' C (w - n) hk) with hand | hor
      · rw [heq]
        apply W_and n C _ _ hk hand
        intro i hi
        have hi' := hAO.2.1 (w - n) hk i hi
        exact ⟨hi', ih i (by omega) (by omega)⟩
      · rw [heq]
        apply W_or n C _ _ hk hor (opnd C (w - n) 0)
          (opnd_mem hAO hk 0) (opnd_lt hAO hk 0)
        exact ih _ (by have := opnd_lt hAO hk 0; omega)
          (by have := opnd_lt hAO hk 0; omega)

lemma and_ancestor_junk {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hTop : TopForm G C) {a k : ℕ}
    (ha : a < C.gates.length) (hand : (gateAt C a).op = GateOp.and)
    (hk : k < C.gates.length) (hkand : (gateAt C k).op = GateOp.and)
    (hc : InCone n C k a) : k ∈ junk G C := by
  have hnb : ¬ BelowF G C k := fun hb => hTop k hk a ha hkand hb hand hc
  have hd : IsDirtyAnd n G C k := by
    unfold IsDirtyAnd IsDirty
    refine ⟨hkand, hk, ?_⟩
    by_contra he
    apply hnb
    intro x hx
    by_contra hf
    exact he ⟨x, hx, Bool.eq_false_iff.mpr hf⟩
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hd⟩

lemma opposite_of_mixed_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (t : ℕ) (ht : t < C.gates.length) (htand : (gateAt C t).op = GateOp.and)
    (htbelow : BelowF G C t) (b : Fin 2) (hreach : OrReaches n C (opnd C t b) h) :
    side (n := n) C t (1 - b) = ∅ ∧
      ¬ OrReaches n C (opnd C t (1 - b)) h ∧
      OrReaches n C (opnd C t (1 - b)) g ∧
      ∀ x : Fin n → Bool, wireVal n C (opnd C t (1 - b)) x = gateVal n C g x := by
  have hempty : side (n := n) C t (1 - b) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    have hh : W n C (monoInput s (s u)) (opnd C t b) = true :=
      reach_up n C _ _ h hreach (hmix (s u))
    have ho : W n C (monoInput s (s u)) (opnd C t (1 - b)) = true :=
      side_val n C _ t (1 - b) u hu (by simp [monoInput])
    have htf := htbelow _ (and_two hAO ht htand b _ hh ho)
    rw [monoInput_false G s hcol] at htf
    cases htf
  have hnot : ¬ OrReaches n C (opnd C t (1 - b)) h := by
    intro hr
    have hh : W n C (monoInput s false) (opnd C t b) = true :=
      reach_up n C _ _ h hreach (hmix false)
    have ho : W n C (monoInput s false) (opnd C t (1 - b)) = true :=
      reach_up n C _ _ h hr (hmix false)
    have htf := htbelow _ (and_two hAO ht htand b _ hh ho)
    rw [monoInput_false G s hcol] at htf
    cases htf
  have hdown (x : Fin n → Bool) (hv : W n C x (opnd C t (1 - b)) = true) :
      OrReaches n C (opnd C t (1 - b)) g ∧ gateVal n C g x = true := by
    rcases down n C x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) _ hv with
      ⟨u, hu, _⟩ | ⟨k, hk, hr, hkand, hkv⟩
    · change u ∈ side (n := n) C t (1 - b) at hu
      rw [hempty] at hu
      exact False.elim (Finset.notMem_empty _ hu)
    · have hcone := reach_cone n C t ht _ (opnd_mem hAO ht (1 - b))
        (opnd_lt hAO ht (1 - b)) k hr
      have hkJ := and_ancestor_junk hTop ht htand hk hkand hcone
      have hkg : k = g ∨ k = h := by simpa [hJ] using hkJ
      rcases hkg with hkg | hkg <;> subst k
      · exact ⟨hr, hkv⟩
      · exact False.elim (hnot hr)
  have hr := (hdown (fun _ => true) (wire_all_true hAO _
    (by have := opnd_lt hAO ht (1 - b); omega))).1
  refine ⟨hempty, hnot, hr, ?_⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact fun hv => (hdown x hv).2
  · exact reach_up n C x _ g hr

lemma W_or_patch {n : ℕ} {C : Circuit} {h : ℕ} (hhand : (gateAt C h).op = GateOp.and)
    (r : Gate) (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hkor : (gateAt C k).op = GateOp.or) (w : ℕ) (hw : w ∈ (gateAt C k).inputs)
    (hwlt : w < n + k) (hv : W n (patch C h r) x w = true) :
    W n (patch C h r) x (n + k) = true := by
  have hne : h ≠ k := by rintro rfl; rw [hhand] at hkor; cases hkor
  apply W_or n (patch C h r) x k (by simpa [patch] using hk) _ w _ hwlt hv
  · rw [gateAt_patch_ne C h k r hne]; exact hkor
  · rw [gateAt_patch_ne C h k r hne]; exact hw

lemma W_and_patch {n : ℕ} {C : Circuit} {h : ℕ} (r : Gate) (x : Fin n → Bool)
    (k : ℕ) (hk : k < C.gates.length) (hkop : (gateAt C k).op = GateOp.and)
    (hne : h ≠ k)
    (hall : ∀ w ∈ (gateAt C k).inputs, w < n + k ∧ W n (patch C h r) x w = true) :
    W n (patch C h r) x (n + k) = true := by
  apply W_and n (patch C h r) x k (by simpa [patch] using hk)
  · rw [gateAt_patch_ne C h k r hne]; exact hkop
  · rw [gateAt_patch_ne C h k r hne]; exact hall

lemma reach_val_patch {n : ℕ} {C : Circuit} {h : ℕ}
    (hhand : (gateAt C h).op = GateOp.and) (r : Gate) (x : Fin n → Bool) (g : ℕ)
    (hv : W n (patch C h r) x (n + g) = true) :
    ∀ k, k < C.gates.length → g ∈ (orSets n C).getD k [] →
      W n (patch C h r) x (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hmem
    rcases (orSets_mem_iff n C k g hk).mp hmem with he | ⟨hop, w, hw, hn, hlt, hx⟩
    · rw [← he]; exact hv
    · have h3 := ih (w - n) (by omega) (by omega) hx
      have e : n + (w - n) = w := by omega
      rw [e] at h3
      exact W_or_patch hhand r x k hk hop w hw hlt h3

lemma reach_up_patch {n : ℕ} {C : Circuit} {h : ℕ}
    (hhand : (gateAt C h).op = GateOp.and) (r : Gate) (x : Fin n → Bool) (w g : ℕ)
    (hr : OrReaches n C w g) (hv : W n (patch C h r) x (n + g) = true) :
    W n (patch C h r) x w = true := by
  obtain ⟨hn, hmem⟩ := hr
  by_cases hk : w - n < C.gates.length
  · have h3 := reach_val_patch hhand r x g hv (w - n) hk hmem
    have e : n + (w - n) = w := by omega
    rw [e] at h3
    exact h3
  · exfalso
    have hlen : (orSets n C).length = C.gates.length := by
      unfold orSets; rw [orFold_length]; simp
    have hge : (orSets n C).length ≤ w - n := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hmem
    simp at hmem

lemma orIn_val_patch {n : ℕ} {C : Circuit} {h : ℕ}
    (hhand : (gateAt C h).op = GateOp.and) (r : Gate) (x : Fin n → Bool)
    (w : ℕ) (u : Fin n) (hu : u ∈ orIn n C w) (hxu : x u = true) :
    W n (patch C h r) x w = true := by
  rcases (orIn_mem n C w u).mp hu with hu | ⟨k, hk, hr, hkor, huk⟩
  · rw [← hu, W_input n (patch C h r) x u.val u.isLt]
    exact hxu
  · apply reach_up_patch hhand r x w k hr
    apply W_or_patch hhand r x k hk hkor u.val huk (by have := u.isLt; omega)
    rw [W_input n (patch C h r) x u.val u.isLt]
    exact hxu

lemma down_patch {n : ℕ} {C : Circuit} {h : ℕ}
    (hhand : (gateAt C h).op = GateOp.and) (r : Gate) (x : Fin n → Bool)
    (hAO : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or) :
    ∀ w, W n (patch C h r) x w = true →
      (∃ i : Fin n, i ∈ orIn n C w ∧ x i = true) ∨
      ∃ k, k < C.gates.length ∧ OrReaches n C w k ∧ (gateAt C k).op = GateOp.and ∧
        W n (patch C h r) x (n + k) = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hv
    by_cases hwn : w < n
    · left
      refine ⟨⟨w, hwn⟩, (orIn_mem n C w _).mpr (Or.inl rfl), ?_⟩
      rw [← W_input n (patch C h r) x w hwn]; exact hv
    · by_cases hk : w - n < C.gates.length
      · have hw : w = n + (w - n) := by omega
        set k := w - n with hkdef
        rcases hAO k hk with hop | hop
        · right
          refine ⟨k, hk, ?_, hop, ?_⟩
          · rw [hw]; exact orReach_self n C k hk
          · rw [← hw]; exact hv
        · have hv2 := hv
          have hne : h ≠ k := by rintro rfl; rw [hhand] at hop; cases hop
          rw [hw, W_gate n (patch C h r) x k (by simpa [patch] using hk),
            gateAt_patch_ne C h k r hne, hop] at hv2
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hv2
          obtain ⟨i, hi, hiv⟩ := hv2
          split_ifs at hiv with hlt
          rcases ih i (by omega) hiv with ⟨j, hj, hxj⟩ | ⟨k', hk', hr, hop', hv'⟩
          · left
            refine ⟨j, ?_, hxj⟩
            rw [orIn_mem] at hj ⊢
            right
            rcases hj with hj | ⟨k'', hk'', hr, hop'', hin⟩
            · refine ⟨k, hk, ?_, hop, ?_⟩
              · rw [hw]; exact orReach_self n C k hk
              · rw [hj]; exact hi
            · refine ⟨k'', hk'', ?_, hop'', hin⟩
              rw [hw]; exact orReach_trans n C k hk hop i hi hlt k'' hr
          · right
            refine ⟨k', hk', ?_, hop', hv'⟩
            rw [hw]; exact orReach_trans n C k hk hop i hi hlt k' hr
      · exfalso
        have hl : ((patch C h r).wires (List.ofFn x)).length = n + C.gates.length := by
          rw [wires_length]
          simp [patch]
        have : W n (patch C h r) x w = false := getD_ge_length _ w (by omega)
        rw [this] at hv; exact Bool.false_ne_true hv

lemma and_true_operands {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {t : ℕ} (ht : t < C.gates.length) (hop : (gateAt C t).op = GateOp.and)
    (x : Fin n → Bool) (hv : gateVal n C t x = true) (b : Fin 2) :
    W n C x (opnd C t b) = true := by
  change W n C x (n + t) = true at hv
  rw [W_gate n C x t ht, hop] at hv
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hv
  have hb := hv _ (opnd_mem hAO ht b)
  rwa [ite_eq_left (opnd_lt hAO ht b)] at hb

lemma and_true_operands_patch {n : ℕ} {C : Circuit} {h : ℕ} (r : Gate)
    (hAO : IsAO2 n C) {t : ℕ} (ht : t < C.gates.length)
    (hop : (gateAt C t).op = GateOp.and) (hne : h ≠ t)
    (x : Fin n → Bool) (hv : gateVal n (patch C h r) t x = true) (b : Fin 2) :
    W n (patch C h r) x (opnd C t b) = true := by
  change W n (patch C h r) x (n + t) = true at hv
  rw [W_gate n (patch C h r) x t (by simpa [patch] using ht),
    gateAt_patch_ne C h t r hne, hop] at hv
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hv
  have hb := hv _ (opnd_mem hAO ht b)
  rwa [ite_eq_left (opnd_lt hAO ht b)] at hb

lemma and_junk_or_below {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {k : ℕ} (hk : k < C.gates.length)
    (hand : (gateAt C k).op = GateOp.and) : k ∈ junk G C ∨ BelowF G C k := by
  by_cases hb : BelowF G C k
  · exact Or.inr hb
  · left
    apply mem_junk.mpr
    refine ⟨hk, hand, hk, ?_⟩
    by_contra he
    apply hb
    intro x hx
    by_contra hf
    exact he ⟨x, hx, Bool.eq_false_iff.mpr hf⟩

lemma orIn_val (n : ℕ) (C : Circuit) (x : Fin n → Bool)
    (w : ℕ) (u : Fin n) (hu : u ∈ orIn n C w) (hxu : x u = true) :
    W n C x w = true := by
  rcases (orIn_mem n C w u).mp hu with hu | ⟨k, hk, hr, hkor, huk⟩
  · rw [← hu, W_input n C x u.val u.isLt]
    exact hxu
  · apply reach_up n C x w k hr
    apply W_or n C x k hk hkor u.val huk (by have := u.isLt; omega)
    rw [W_input n C x u.val u.isLt]
    exact hxu

lemma mixed_ne_clean {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {s : Fin n → Bool} (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    {h t : ℕ} (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (htbelow : BelowF G C t) : h ≠ t := by
  rintro rfl
  have hf := htbelow (monoInput s false) (hmix false)
  rw [monoInput_false G s hcol] at hf
  cases hf

lemma output_not_reaches_mixed {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {s : Fin n → Bool} (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hF : circuitFun n C = graphFun G ∅) {h : ℕ}
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true) :
    ¬ OrReaches n C C.output h := by
  intro hr
  have hv := reach_up n C (monoInput s false) C.output h hr (hmix false)
  change circuitFun n C (monoInput s false) = true at hv
  rw [hF, monoInput_false G s hcol] at hv
  cases hv

lemma patched_opposite_implies_other {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (t : ℕ) (ht : t < C.gates.length) (htand : (gateAt C t).op = GateOp.and)
    (htbelow : BelowF G C t) (b : Fin 2) (hreach : OrReaches n C (opnd C t b) h)
    (r : Gate) (x : Fin n → Bool)
    (hv : wireVal n (patch C h r) (opnd C t (1 - b)) x = true) :
    gateVal n (patch C h r) g x = true := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hhand := (mem_junk.mp hhJ).2.1
  obtain ⟨hempty, hnot, _, _⟩ :=
    opposite_of_mixed_junk G C s hcol hAO hTop g h hJ hmix t ht htand htbelow b hreach
  rcases down_patch hhand r x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) _ hv with
    ⟨u, hu, _⟩ | ⟨k, hk, hr, hkand, hkv⟩
  · change u ∈ side (n := n) C t (1 - b) at hu
    rw [hempty] at hu
    exact False.elim (Finset.notMem_empty _ hu)
  · have hcone := reach_cone n C t ht _ (opnd_mem hAO ht (1 - b))
      (opnd_lt hAO ht (1 - b)) k hr
    have hkJ := and_ancestor_junk hTop ht htand hk hkand hcone
    have hkg : k = g ∨ k = h := by simpa [hJ] using hkJ
    rcases hkg with hkg | hkg <;> subst k
    · exact hkv
    · exact False.elim (hnot hr)

lemma clean_and_false_under_guard {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (r : Gate) (x : Fin n → Bool) (hxF : graphFun G ∅ x = false)
    (hxg : gateVal n (patch C h r) g x = false)
    (t : ℕ) (ht : t < C.gates.length) (htand : (gateAt C t).op = GateOp.and)
    (htbelow : BelowF G C t) : gateVal n (patch C h r) t x = false := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hhand := (mem_junk.mp hhJ).2.1
  have hne := mixed_ne_clean hcol hmix htbelow
  cases hv : gateVal n (patch C h r) t x with
  | false => rfl
  | true =>
    have hraw (b : Fin 2) : W n C x (opnd C t b) = true := by
      have hb := and_true_operands_patch r hAO ht htand hne x hv b
      rcases down_patch hhand r x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) _ hb with
        ⟨u, hu, hxu⟩ | ⟨k, hk, hr, hkand, hkv⟩
      · exact orIn_val n C x _ u hu hxu
      · have hcone := reach_cone n C t ht _ (opnd_mem hAO ht b) (opnd_lt hAO ht b) k hr
        have hkJ := and_ancestor_junk hTop ht htand hk hkand hcone
        have hkg : k = g ∨ k = h := by simpa [hJ] using hkJ
        rcases hkg with hkg | hkg <;> subst k
        · change gateVal n (patch C h r) g x = true at hkv
          rw [hxg] at hkv
          cases hkv
        · have hother := and_true_operands_patch r hAO ht htand hne x hv (1 - b)
          have hg := patched_opposite_implies_other G C s hcol hAO hTop g h hJ hmix
            t ht htand htbelow b hr r x hother
          rw [hxg] at hg
          cases hg
    have hf := htbelow x (and_two hAO ht htand 0 x (hraw 0) (hraw (1 - 0)))
    rw [hxF] at hf
    cases hf

lemma output_false_under_guard {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (hF : circuitFun n C = graphFun G ∅)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (r : Gate) (x : Fin n → Bool) (hxF : graphFun G ∅ x = false)
    (hxg : gateVal n (patch C h r) g x = false) :
    circuitFun n (patch C h r) x = false := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hhand := (mem_junk.mp hhJ).2.1
  cases hv : circuitFun n (patch C h r) x with
  | false => rfl
  | true =>
    rcases down_patch hhand r x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) C.output hv with
      ⟨u, hu, hxu⟩ | ⟨k, hk, hr, hkand, hkv⟩
    · have hvC := orIn_val n C x C.output u hu hxu
      change circuitFun n C x = true at hvC
      rw [hF, hxF] at hvC
      cases hvC
    · rcases and_junk_or_below (G := G) hk hkand with hkJ | hkbelow
      · have hkg : k = g ∨ k = h := by simpa [hJ] using hkJ
        rcases hkg with hkg | hkg <;> subst k
        · change gateVal n (patch C h r) g x = true at hkv
          rw [hxg] at hkv
          cases hkv
        · exact False.elim (output_not_reaches_mixed hcol hF hmix hr)
      · have hf := clean_and_false_under_guard G C s hcol hAO hTop g h hJ hmix
          r x hxF hxg k hk hkand hkbelow
        change gateVal n (patch C h r) k x = true at hkv
        rw [hf] at hkv
        cases hkv

lemma clean_and_survives_without_other {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (r : Gate) (x : Fin n → Bool) (hxg : gateVal n C g x = false)
    (t : ℕ) (ht : t < C.gates.length) (htand : (gateAt C t).op = GateOp.and)
    (htbelow : BelowF G C t) (hv : gateVal n C t x = true) :
    gateVal n (patch C h r) t x = true := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hhand := (mem_junk.mp hhJ).2.1
  have hne := mixed_ne_clean hcol hmix htbelow
  have hraw (b : Fin 2) : W n (patch C h r) x (opnd C t b) = true := by
    have hb := and_true_operands hAO ht htand x hv b
    rcases down n C x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) _ hb with
      ⟨u, hu, hxu⟩ | ⟨k, hk, hr, hkand, hkv⟩
    · exact orIn_val_patch hhand r x _ u hu hxu
    · have hcone := reach_cone n C t ht _ (opnd_mem hAO ht b) (opnd_lt hAO ht b) k hr
      have hkJ := and_ancestor_junk hTop ht htand hk hkand hcone
      have hkg : k = g ∨ k = h := by simpa [hJ] using hkJ
      rcases hkg with hkg | hkg <;> subst k
      · change gateVal n C g x = true at hkv
        rw [hxg] at hkv
        cases hkv
      · have hother := and_true_operands hAO ht htand x hv (1 - b)
        have heq := (opposite_of_mixed_junk G C s hcol hAO hTop g h hJ hmix
          t ht htand htbelow b hr).2.2.2 x
        change wireVal n C (opnd C t (1 - b)) x = true at hother
        rw [heq, hxg] at hother
        cases hother
  apply W_and_patch r x t ht htand hne
  intro w hw
  obtain ⟨b, rfl⟩ := (mem_inputs_iff_opnd hAO ht w).mp hw
  exact ⟨opnd_lt hAO ht b, hraw b⟩

lemma output_survives_without_other {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (hF : circuitFun n C = graphFun G ∅)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (r : Gate) (x : Fin n → Bool) (hxg : gateVal n C g x = false)
    (hv : circuitFun n C x = true) : circuitFun n (patch C h r) x = true := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hhand := (mem_junk.mp hhJ).2.1
  rcases down n C x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) C.output hv with
    ⟨u, hu, hxu⟩ | ⟨k, hk, hr, hkand, hkv⟩
  · exact orIn_val_patch hhand r x C.output u hu hxu
  · rcases and_junk_or_below (G := G) hk hkand with hkJ | hkbelow
    · have hkg : k = g ∨ k = h := by simpa [hJ] using hkJ
      rcases hkg with hkg | hkg <;> subst k
      · change gateVal n C g x = true at hkv
        rw [hxg] at hkv
        cases hkv
      · exact False.elim (output_not_reaches_mixed hcol hF hmix hr)
    · apply reach_up_patch hhand r x C.output k hr
      exact clean_and_survives_without_other G C s hcol hAO hTop g h hJ hmix r x hxg
        k hk hkand hkbelow hkv

lemma lost_edge_uses_other {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (hF : circuitFun n C = graphFun G ∅)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (r : Gate) (u v : Fin n) (huv : G.Adj u v)
    (hlost : circuitFun n (patch C h r) (pairInput u v) = false) :
    gateVal n C g (pairInput u v) = true := by
  cases hg : gateVal n C g (pairInput u v) with
  | true => rfl
  | false =>
    have hv : circuitFun n C (pairInput u v) = true := by
      rw [hF]
      exact (graph_true G (pairInput u v)).mpr
        ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
    have hp := output_survives_without_other G C s hcol hAO hTop hF g h hJ hmix r _ hg hv
    rw [hlost] at hp
    cases hp

lemma wire_unchanged_away {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (f : ℕ) (r : Gate) (x : Fin n → Bool) :
    ∀ w, w < n + C.gates.length → w ≠ n + f →
      (∀ k, w = n + k → ¬ InCone n C f k) →
      W n (patch C f r) x w = W n C x w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hwne hwcone
    by_cases hwn : w < n
    · rw [W_input n (patch C f r) x w hwn, W_input n C x w hwn]
    · have hk : w - n < C.gates.length := by omega
      have heq : w = n + (w - n) := by omega
      have hne : f ≠ w - n := by intro hf; apply hwne; omega
      rw [heq, W_gate n (patch C f r) x (w - n) (by simpa [patch] using hk),
        W_gate n C x (w - n) hk, gateAt_patch_ne C f (w - n) r hne]
      congr 1
      apply List.map_congr_left
      intro i hi
      have hil := hAO.2.1 (w - n) hk i hi
      rw [ite_eq_left hil, ite_eq_left hil]
      apply ih i (by omega) (by omega)
      · intro hie
        apply hwcone (w - n) heq
        apply (inCone_iff n C f (w - n)).mpr
        refine ⟨hk, f, by omega, ?_, Or.inl rfl⟩
        rwa [← hie]
      · intro k hik hfk
        apply hwcone (w - n) heq
        apply (inCone_iff n C f (w - n)).mpr
        refine ⟨hk, k, by omega, ?_, Or.inr hfk⟩
        rwa [← hik]

lemma gate_unchanged_of_notCone {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (f k : ℕ) (r : Gate) (hk : k < C.gates.length) (hne : f ≠ k)
    (hcone : ¬ InCone n C f k) (x : Fin n → Bool) :
    gateVal n (patch C f r) k x = gateVal n C k x := by
  apply wire_unchanged_away hAO f r x (n + k) (by omega) (by omega)
  intro j hj
  have hkj : k = j := by omega
  subst j
  exact hcone

lemma guarded_or_repair {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (hF : circuitFun n C = graphFun G ∅)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (r : Gate) (hror : r.op = GateOp.or) (hrlen : r.inputs.length = 2)
    (hrback : ∀ i ∈ r.inputs, i < n + h)
    (preserve : ∀ x : Fin n → Bool, gateVal n (patch C h r) g x = gateVal n C g x)
    (guarded : ∀ x : Fin n → Bool, gateVal n C g x = true →
      gateBit (earlierWires C h (List.ofFn x)) r = true → graphFun G ∅ x = true)
    (critical : ∀ a b, G.Adj a b → circuitFun n (patch C h off) (pairInput a b) = false →
      gateBit (earlierWires C h (List.ofFn (pairInput a b))) r = true) :
    let D := patch C h r
    IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size = C.size ∧
      junk G D ⊆ junk G C ∧ h ∉ junk G D := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  have hh := (mem_junk.mp hhJ).1
  have hC := ao_mono hAO
  let D := patch C h r
  have hDAO : IsAO2 n D := patch_gate_ao hAO hh r (Or.inr hror) hrlen hrback
  have hmono : Monotone2 D := ao_mono hDAO
  have hdom (x : Fin n → Bool) (hxF : graphFun G ∅ x = false)
      (hxg : gateVal n C g x = true) :
      WiresLE (D.wires (List.ofFn x)) (C.wires (List.ofFn x)) := by
    rw [← original_patch hh]
    apply patch_mono hC hh
    intro hr
    have hf := guarded x hxg hr
    rw [hxF] at hf
    cases hf
  have clean_stays (t : ℕ) (ht : t < C.gates.length)
      (htand : (gateAt C t).op = GateOp.and) (htbelow : BelowF G C t) : BelowF G D t := by
    intro x hx
    cases hxF : graphFun G ∅ x with
    | true => rfl
    | false =>
      cases hxg : gateVal n C g x with
      | false =>
        have hgp : gateVal n D g x = false := (preserve x).trans hxg
        have hf := clean_and_false_under_guard G C s hcol hAO hTop g h hJ hmix
          r x hxF hgp t ht htand htbelow
        rw [hf] at hx
        cases hx
      | true =>
        have hv : gateVal n C t x = true := (hdom x hxF hxg).2 (n + t) hx
        have hf := htbelow x hv
        rw [hxF] at hf
        cases hf
  have allEdges (a b : Fin n) (hab : G.Adj a b) : circuitFun n D (pairInput a b) = true := by
    cases hcut : circuitFun n (patch C h off) (pairInput a b) with
    | true =>
      exact (patch_mono hC hh off r (List.ofFn (pairInput a b))
        (by simp [off_bit])).2 C.output hcut
    | false =>
      have hle := patch_mono hC hh C.gates[h] r (List.ofFn (pairInput a b))
        (fun _ => critical a b hab hcut)
      rw [original_patch hh] at hle
      apply hle.2 C.output
      change circuitFun n C (pairInput a b) = true
      rw [hF]
      exact (graph_true G (pairInput a b)).mpr
        ⟨a, b, hab, by simp [pairInput], by simp [pairInput]⟩
  have hcompute : circuitFun n D = graphFun G ∅ := by
    funext x
    cases hxF : graphFun G ∅ x with
    | true =>
      obtain ⟨a, b, hab, ha, hb⟩ := (graph_true G x).mp hxF
      exact circuit_mono hmono (pair_le ha hb) (allEdges a b hab)
    | false =>
      cases hxg : gateVal n C g x with
      | false =>
        exact output_false_under_guard G C s hcol hAO hTop hF g h hJ hmix
          r x hxF ((preserve x).trans hxg)
      | true =>
        cases hxD : circuitFun n D x with
        | false => rfl
        | true =>
          have hv : circuitFun n C x = true := (hdom x hxF hxg).2 C.output hxD
          rw [hF, hxF] at hv
          cases hv
  have hlen : D.gates.length = C.gates.length := List.length_set
  have hclean : h ∉ junk G D := by
    intro hd
    have hop := (mem_junk.mp hd).2.1
    have he : gateAt D h = r := by
      simp [D, patch, gateAt, List.getD_eq_getElem?_getD, hh]
    rw [he, hror] at hop
    cases hop
  have hsub : junk G D ⊆ junk G C := by
    intro k hk
    have hne : h ≠ k := fun he => hclean (he.symm ▸ hk)
    obtain ⟨hklen, hkop, _, x, hx, hxF⟩ := mem_junk.mp hk
    have hkc : k < C.gates.length := hlen ▸ hklen
    have hcop : (gateAt C k).op = GateOp.and := by
      rwa [show gateAt D k = gateAt C k from gateAt_patch_ne C h k r hne] at hkop
    rcases and_junk_or_below (G := G) hkc hcop with hkJ | hkbelow
    · exact hkJ
    · have hf := clean_stays k hkc hcop hkbelow x hx
      rw [hxF] at hf
      cases hf
  exact ⟨hDAO, hcompute, hlen, hsub, hclean⟩

lemma no_guarded_or_replacement
    (rungOne : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (s : Fin n → Bool),
      (∀ u v, G.Adj u v → s u ≠ s v) → NoFourCycle G → IsLeastAO G C →
        (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hne : g ≠ h) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (r : Gate) (hror : r.op = GateOp.or) (hrlen : r.inputs.length = 2)
    (hrback : ∀ i ∈ r.inputs, i < n + h)
    (preserve : ∀ x : Fin n → Bool, gateVal n (patch C h r) g x = gateVal n C g x)
    (guarded : ∀ x : Fin n → Bool, gateVal n C g x = true →
      gateBit (earlierWires C h (List.ofFn x)) r = true → graphFun G ∅ x = true)
    (critical : ∀ a b, G.Adj a b → circuitFun n (patch C h off) (pairInput a b) = false →
      gateBit (earlierWires C h (List.ofFn (pairInput a b))) r = true) : False := by
  have hgJ : g ∈ junk G C := by simp [hJ]
  obtain ⟨hAO, hF, hsize, hsub, hclean⟩ :=
    guarded_or_repair G C s hcol hL.1 hTop hL.2.1 g h hJ hmix r hror hrlen hrback
      preserve guarded critical
  let D := patch C h r
  have hDL : IsLeastAO G D := by
    refine ⟨hAO, hF, ?_⟩
    intro E hE hEF
    rw [hsize]
    exact hL.2.2 E hE hEF
  have hgD : g ∈ junk G D := by
    obtain ⟨hglen, hgop, _, x, hx, hxF⟩ := mem_junk.mp hgJ
    apply mem_junk.mpr
    refine ⟨by simpa [D, patch] using hglen, ?_, by simpa [D, patch] using hglen, x, ?_, hxF⟩
    · rw [gateAt_patch_ne C h g r hne.symm]
      exact hgop
    · rwa [preserve]
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
      exact hgD
  apply rungOne n G D s hcol h4 hDL
  rw [hDJ]
  exact Finset.card_singleton g

lemma no_guarded_or_later_replacement
    (rungOne : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
      (C : Circuit) (s : Fin n → Bool),
      (∀ u v, G.Adj u v → s u ≠ s v) → NoFourCycle G → IsLeastAO G C →
        (junk G C).card ≠ 1)
    {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (h4 : NoFourCycle G) (hL : IsLeastAO G C) (hTop : TopForm G C)
    (g h : ℕ) (hgh : g < h) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (r : Gate) (hror : r.op = GateOp.or) (hrlen : r.inputs.length = 2)
    (hrback : ∀ i ∈ r.inputs, i < n + h)
    (guarded : ∀ x : Fin n → Bool, gateVal n C g x = true →
      gateBit (earlierWires C h (List.ofFn x)) r = true → graphFun G ∅ x = true)
    (critical : ∀ a b, G.Adj a b → circuitFun n (patch C h off) (pairInput a b) = false →
      gateBit (earlierWires C h (List.ofFn (pairInput a b))) r = true) : False := by
  have hhJ : h ∈ junk G C := by simp [hJ]
  exact no_guarded_or_replacement rungOne G C s hcol h4 hL hTop g h (by omega) hJ hmix
    r hror hrlen hrback
    (fun x => gateVal_patch_before (mem_junk.mp hhJ).1 hgh r x) guarded critical

end PEqualNP.Outside.L_meta_5012_aux.Mixed

namespace PEqualNP.Outside.L_meta_5012_aux.MixedOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012_aux.Mixed

lemma W_or_patch_ne {n : ℕ} {C : Circuit} {e : ℕ} (r : Gate)
    (x : Fin n → Bool) (k : ℕ) (hk : k < C.gates.length)
    (hne : e ≠ k) (hkor : (gateAt C k).op = GateOp.or)
    (w : ℕ) (hw : w ∈ (gateAt C k).inputs) (hwlt : w < n + k)
    (hv : W n (patch C e r) x w = true) :
    W n (patch C e r) x (n + k) = true := by
  apply W_or n (patch C e r) x k (by simpa [patch] using hk) _ w _ hwlt hv
  · rw [gateAt_patch_ne C e k r hne]; exact hkor
  · rw [gateAt_patch_ne C e k r hne]; exact hw

lemma reach_val_patch_away {n : ℕ} {C : Circuit} {e : ℕ}
    (r : Gate) (x : Fin n → Bool) (g : ℕ)
    (hv : W n (patch C e r) x (n + g) = true) :
    ∀ k, k < C.gates.length → e ∉ (orSets n C).getD k [] →
      g ∈ (orSets n C).getD k [] → W n (patch C e r) x (n + k) = true := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk hnot hmem
    rcases (orSets_mem_iff n C k g hk).mp hmem with he | ⟨hop, w, hw, hn, hlt, hx⟩
    · rw [← he]; exact hv
    · have hne : e ≠ k := fun he => hnot ((orSets_mem_iff n C k e hk).mpr (Or.inl he))
      have hnot' : e ∉ (orSets n C).getD (w - n) [] := by
        intro he
        exact hnot ((orSets_mem_iff n C k e hk).mpr
          (Or.inr ⟨hop, w, hw, hn, hlt, he⟩))
      have h3 := ih (w - n) (by omega) (by omega) hnot' hx
      have heq : n + (w - n) = w := by omega
      rw [heq] at h3
      exact W_or_patch_ne r x k hk hne hop w hw hlt h3

lemma reach_up_patch_away {n : ℕ} {C : Circuit} {e : ℕ}
    (r : Gate) (x : Fin n → Bool) (w g : ℕ)
    (hnot : ¬ OrReaches n C w e)
    (hr : OrReaches n C w g) (hv : W n (patch C e r) x (n + g) = true) :
    W n (patch C e r) x w = true := by
  obtain ⟨hn, hmem⟩ := hr
  by_cases hk : w - n < C.gates.length
  · have hnot' : e ∉ (orSets n C).getD (w - n) [] := fun he => hnot ⟨hn, he⟩
    have h3 := reach_val_patch_away r x g hv (w - n) hk hnot' hmem
    have heq : n + (w - n) = w := by omega
    rwa [heq] at h3
  · exfalso
    have hlen : (orSets n C).length = C.gates.length := by
      unfold orSets; rw [orFold_length]; simp
    have hge : (orSets n C).length ≤ w - n := by omega
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hge] at hmem
    simp at hmem

lemma orIn_val_patch_away {n : ℕ} {C : Circuit} {e : ℕ}
    (r : Gate) (x : Fin n → Bool) (w : ℕ)
    (hnot : ¬ OrReaches n C w e)
    (u : Fin n) (hu : u ∈ orIn n C w) (hxu : x u = true) :
    W n (patch C e r) x w = true := by
  rcases (orIn_mem n C w u).mp hu with hu | ⟨k, hk, hr, hkor, huk⟩
  · rw [← hu, W_input n (patch C e r) x u.val u.isLt]
    exact hxu
  · have hne : e ≠ k := by rintro rfl; exact hnot hr
    apply reach_up_patch_away r x w k hnot hr
    apply W_or_patch_ne r x k hk hne hkor u.val huk (by have := u.isLt; omega)
    rw [W_input n (patch C e r) x u.val u.isLt]
    exact hxu

end PEqualNP.Outside.L_meta_5012_aux.MixedOr

namespace PEqualNP.Outside.L_meta_5012_aux.MixedOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012_aux.Mixed

lemma opposite_of_mixed_gate {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (E : ℕ) (hmixE : ∀ c : Bool, gateVal n C E (monoInput s c) = true)
    (t : ℕ) (ht : t < C.gates.length) (htand : (gateAt C t).op = GateOp.and)
    (htbelow : BelowF G C t) (b : Fin 2) (hreach : OrReaches n C (opnd C t b) E) :
    side (n := n) C t (1 - b) = ∅ ∧
      ¬ OrReaches n C (opnd C t (1 - b)) h ∧
      OrReaches n C (opnd C t (1 - b)) g ∧
      ∀ x : Fin n → Bool, wireVal n C (opnd C t (1 - b)) x = gateVal n C g x := by
  have hempty : side (n := n) C t (1 - b) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro u hu
    have hh : W n C (monoInput s (s u)) (opnd C t b) = true :=
      reach_up n C _ _ E hreach (hmixE (s u))
    have ho : W n C (monoInput s (s u)) (opnd C t (1 - b)) = true :=
      side_val n C _ t (1 - b) u hu (by simp [monoInput])
    have htf := htbelow _ (and_two hAO ht htand b _ hh ho)
    rw [monoInput_false G s hcol] at htf
    cases htf
  have hnot : ¬ OrReaches n C (opnd C t (1 - b)) h := by
    intro hr
    have hh : W n C (monoInput s false) (opnd C t b) = true :=
      reach_up n C _ _ E hreach (hmixE false)
    have ho : W n C (monoInput s false) (opnd C t (1 - b)) = true :=
      reach_up n C _ _ h hr (hmix false)
    have htf := htbelow _ (and_two hAO ht htand b _ hh ho)
    rw [monoInput_false G s hcol] at htf
    cases htf
  have hdown (x : Fin n → Bool) (hv : W n C x (opnd C t (1 - b)) = true) :
      OrReaches n C (opnd C t (1 - b)) g ∧ gateVal n C g x = true := by
    rcases down n C x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) _ hv with
      ⟨u, hu, _⟩ | ⟨k, hk, hr, hkand, hkv⟩
    · change u ∈ side (n := n) C t (1 - b) at hu
      rw [hempty] at hu
      exact False.elim (Finset.notMem_empty _ hu)
    · have hcone := reach_cone n C t ht _ (opnd_mem hAO ht (1 - b))
        (opnd_lt hAO ht (1 - b)) k hr
      have hkJ := and_ancestor_junk hTop ht htand hk hkand hcone
      have hkg : k = g ∨ k = h := by simpa [hJ] using hkJ
      rcases hkg with hkg | hkg <;> subst k
      · exact ⟨hr, hkv⟩
      · exact False.elim (hnot hr)
  have hr := (hdown (fun _ => true) (wire_all_true hAO _
    (by have := opnd_lt hAO ht (1 - b); omega))).1
  refine ⟨hempty, hnot, hr, ?_⟩
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact fun hv => (hdown x hv).2
  · exact reach_up n C x _ g hr

end PEqualNP.Outside.L_meta_5012_aux.MixedOr

namespace PEqualNP.Outside.L_meta_5012_aux.MixedOr

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_5012_aux.Mixed

lemma clean_and_survives_mixed_patch {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (e : ℕ) (hmixE : ∀ c : Bool, gateVal n C e (monoInput s c) = true)
    (r : Gate) (x : Fin n → Bool) (hxg : gateVal n C g x = false)
    (t : ℕ) (ht : t < C.gates.length) (htand : (gateAt C t).op = GateOp.and)
    (htbelow : BelowF G C t) (hv : gateVal n C t x = true) :
    gateVal n (patch C e r) t x = true := by
  have hne := mixed_ne_clean hcol hmixE htbelow
  have hnot (b : Fin 2) : ¬ OrReaches n C (opnd C t b) e := by
    intro hr
    have heq := (opposite_of_mixed_gate G C s hcol hAO hTop g h hJ hmix
      e hmixE t ht htand htbelow b hr).2.2.2 x
    have hother := and_true_operands hAO ht htand x hv (1 - b)
    change wireVal n C (opnd C t (1 - b)) x = true at hother
    rw [heq, hxg] at hother
    cases hother
  have hraw (b : Fin 2) : W n (patch C e r) x (opnd C t b) = true := by
    have hb := and_true_operands hAO ht htand x hv b
    rcases down n C x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) _ hb with
      ⟨u, hu, hxu⟩ | ⟨k, hk, hr, hkand, hkv⟩
    · exact orIn_val_patch_away r x _ (hnot b) u hu hxu
    · have hcone := reach_cone n C t ht _ (opnd_mem hAO ht b) (opnd_lt hAO ht b) k hr
      have hkJ := and_ancestor_junk hTop ht htand hk hkand hcone
      have hkg : k = g ∨ k = h := by simpa [hJ] using hkJ
      rcases hkg with hkg | hkg <;> subst k
      · change gateVal n C g x = true at hkv
        rw [hxg] at hkv
        cases hkv
      · have hother := and_true_operands hAO ht htand x hv (1 - b)
        have heq := (opposite_of_mixed_junk G C s hcol hAO hTop g h hJ hmix
          t ht htand htbelow b hr).2.2.2 x
        change wireVal n C (opnd C t (1 - b)) x = true at hother
        rw [heq, hxg] at hother
        cases hother
  apply W_and_patch r x t ht htand hne
  intro w hw
  obtain ⟨b, rfl⟩ := (mem_inputs_iff_opnd hAO ht w).mp hw
  exact ⟨opnd_lt hAO ht b, hraw b⟩

lemma output_survives_mixed_patch {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (hF : circuitFun n C = graphFun G ∅)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (e : ℕ) (hmixE : ∀ c : Bool, gateVal n C e (monoInput s c) = true)
    (r : Gate) (x : Fin n → Bool) (hxg : gateVal n C g x = false)
    (hv : circuitFun n C x = true) : circuitFun n (patch C e r) x = true := by
  have hnot := output_not_reaches_mixed hcol hF hmixE
  rcases down n C x (fun k hk => hAO.1 _ (gateAt_mem' C k hk)) C.output hv with
    ⟨u, hu, hxu⟩ | ⟨k, hk, hr, hkand, hkv⟩
  · exact orIn_val_patch_away r x C.output hnot u hu hxu
  · rcases and_junk_or_below (G := G) hk hkand with hkJ | hkbelow
    · have hkg : k = g ∨ k = h := by simpa [hJ] using hkJ
      rcases hkg with hkg | hkg <;> subst k
      · change gateVal n C g x = true at hkv
        rw [hxg] at hkv
        cases hkv
      · exact False.elim (output_not_reaches_mixed hcol hF hmix hr)
    · apply reach_up_patch_away r x C.output k hnot hr
      exact clean_and_survives_mixed_patch G C s hcol hAO hTop g h hJ hmix e hmixE
        r x hxg k hk hkand hkbelow hkv

lemma mixed_lost_edge_uses_other {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (s : Fin n → Bool) (hcol : ∀ u v, G.Adj u v → s u ≠ s v)
    (hAO : IsAO2 n C) (hTop : TopForm G C) (hF : circuitFun n C = graphFun G ∅)
    (g h : ℕ) (hJ : junk G C = {g, h})
    (hmix : ∀ c : Bool, gateVal n C h (monoInput s c) = true)
    (e : ℕ) (hmixE : ∀ c : Bool, gateVal n C e (monoInput s c) = true)
    (r : Gate) (u v : Fin n) (huv : G.Adj u v)
    (hlost : circuitFun n (patch C e r) (pairInput u v) = false) :
    gateVal n C g (pairInput u v) = true := by
  cases hg : gateVal n C g (pairInput u v) with
  | true => rfl
  | false =>
    have hv : circuitFun n C (pairInput u v) = true := by
      rw [hF]
      exact (graph_true G (pairInput u v)).mpr
        ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩
    have hp := output_survives_mixed_patch G C s hcol hAO hTop hF g h hJ hmix e hmixE
      r _ hg hv
    rw [hlost] at hp
    cases hp

end PEqualNP.Outside.L_meta_5012_aux.MixedOr
