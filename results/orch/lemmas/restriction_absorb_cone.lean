import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012.RestrictionCone

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.Core PEqualNP.ReadTwo

lemma card_sdiff_eq {α : Type} [DecidableEq α] {A B : Finset α} (h : A ⊆ B) :
    (B \ A).card = B.card - A.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr h]

-- Section 1: Basic wire, cone, OrReaches, orIn, and side lemmas

lemma foldl_wires_len (gs : List Gate) (acc : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) acc).length =
      acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wires_getD_lt (gs : List Gate) (acc : List Bool) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD i false =
      acc.getD i false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]).length := by
      simp only [List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_wires_getD_gate (gs : List Gate) (acc : List Bool) (j : ℕ) (hj : j < gs.length)
    (hback : ∀ k ∈ gs[j].inputs, k < acc.length + j) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun k => w.getD k false)]) acc).getD
        (acc.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun k =>
        (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun m => w.getD m false)]) acc).getD
          k false) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero] at hback ⊢
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen : acc.length < acc'.length := by
        simp only [acc', List.length_append, List.length_singleton]; omega
      rw [foldl_wires_getD_lt gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length false = g.op.eval (g.inputs.map fun k => acc.getD k false) := by
        simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      congr 1
      apply List.map_congr_left
      intro k hk
      have hka : k < acc.length := hback k hk
      have hka' : k < acc'.length := by omega
      rw [foldl_wires_getD_lt gs acc' k hka']
      simp only [acc', List.getD_eq_getElem?_getD, List.getElem?_append_left hka]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := acc ++ [g.op.eval (g.inputs.map fun k => acc.getD k false)]
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      apply ih acc' j' hj'
      intro k hk
      have hbk := hback k (by simpa using hk)
      omega

lemma wires_length (C : Circuit) (x : List Bool) :
    (C.wires x).length = x.length + C.gates.length :=
  foldl_wires_len C.gates x

lemma wval_input {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) (hi : i < n) :
    wval C x i = x ⟨i, hi⟩ := by
  unfold wval Circuit.wires
  have hlt : i < (List.ofFn x).length := by simp [hi]
  rw [foldl_wires_getD_lt C.gates (List.ofFn x) i hlt]
  simp [List.getD_eq_getElem?_getD, hi]

lemma gateVal_eq_wval {n : ℕ} (C : Circuit) (j : ℕ) (x : Fin n → Bool) :
    gateVal n C j x = wval C x (n + j) := rfl

lemma wval_ge_len {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ} (hw : n + C.gates.length ≤ w) :
    wval C x w = false := by
  unfold wval
  rw [List.getD_eq_getElem?_getD]
  have hlen : (C.wires (List.ofFn x)).length = n + C.gates.length := by
    rw [wires_length, List.length_ofFn]
  rw [List.getElem?_eq_none (by omega)]
  rfl

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt
  simp [List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  unfold opnd
  match h : (gateAt C j).inputs with
  | [a, b] => simp
  | [] => rw [h] at hlen; simp at hlen
  | [_] => rw [h] at hlen; simp at hlen
  | _ :: _ :: _ :: _ => rw [h] at hlen; simp at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]
  fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj _ (opnd_mem hAO hj b)

lemma wval_gate_eval {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) :
    wval C x (n + j) = (gateAt C j).op.eval [wval C x (opnd C j 0), wval C x (opnd C j 1)] := by
  unfold wval Circuit.wires
  have hlen : (List.ofFn x).length = n := List.length_ofFn
  have hback : ∀ k ∈ C.gates[j].inputs, k < (List.ofFn x).length + j := by
    intro k hk; rw [hlen, ← gateAt_eq hj] at *; exact hAO.2.1 j hj k hk
  have h := foldl_wires_getD_gate C.gates (List.ofFn x) j hj hback
  rw [hlen] at h
  rw [h, ← gateAt_eq hj, gate_inputs_eq hAO hj]
  simp

lemma wval_gate_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.and) :
    wval C x (n + j) = (wval C x (opnd C j 0) && wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]

lemma wval_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j : ℕ} (hj : j < C.gates.length) (hop : (gateAt C j).op = GateOp.or) :
    wval C x (n + j) = (wval C x (opnd C j 0) || wval C x (opnd C j 1)) := by
  rw [wval_gate_eval hAO x hj, hop]; simp [GateOp.eval]


def rewireAnd (C : Circuit) (j u v : ℕ) : Circuit :=
  { gates := C.gates.set j ⟨.and, [u, v]⟩
    output := C.output }

lemma rewireAnd_length (C : Circuit) (j u v : ℕ) :
    (rewireAnd C j u v).gates.length = C.gates.length := by
  simp [rewireAnd]

lemma rewireAnd_gateAt {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
    (u v i : ℕ) : gateAt (rewireAnd C j u v) i =
      if i = j then ⟨.and, [u, v]⟩ else gateAt C i := by
  simp only [gateAt, rewireAnd, List.getD_eq_getElem?_getD, List.getElem?_set]
  by_cases hij : i = j
  · subst i
    simp [hj]
  · simp [hij, Ne.symm hij]

lemma rewireAnd_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j u v : ℕ} (hj : j < C.gates.length) (hu : u < n + j) (hv : v < n + j) :
    IsAO2 n (rewireAnd C j u v) := by
  have hidx : ∀ i < (rewireAnd C j u v).gates.length,
      ((gateAt (rewireAnd C j u v) i).op = .and ∨
        (gateAt (rewireAnd C j u v) i).op = .or) ∧
      (∀ w ∈ (gateAt (rewireAnd C j u v) i).inputs, w < n + i) ∧
      (gateAt (rewireAnd C j u v) i).inputs.length = 2 := by
    intro i hi
    rw [rewireAnd_length] at hi
    simp only [rewireAnd_gateAt hj]
    by_cases hij : i = j
    · subst i
      simp only [if_pos (rfl : j = j)]
      refine ⟨Or.inl rfl, ?_, rfl⟩
      intro w hw
      change w ∈ [u, v] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact hu
      · exact hv
    · rw [ite_eq_right hij]
      exact ⟨hAO.1 _ (gateAt_mem hi), hAO.2.1 i hi,
        hAO.2.2 _ (gateAt_mem hi)⟩
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    simpa only [gateAt_eq hi] using (hidx i hi).1
  · intro i hi
    exact (hidx i hi).2.1
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    simpa only [gateAt_eq hi] using (hidx i hi).2.2

lemma rewireAnd_values {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j u v : ℕ} (hj : j < C.gates.length) (hu : u < n + j) (hv : v < n + j)
    (hval : ∀ x : Fin n → Bool,
      (wval C x u && wval C x v) = gateVal n C j x) :
    ∀ (x : Fin n → Bool) (w : ℕ),
      wval (rewireAnd C j u v) x w = wval C x w := by
  have hAO' := rewireAnd_isAO2 hAO hj hu hv
  intro x w
  by_cases hwlen : w < n + C.gates.length
  · induction w using Nat.strong_induction_on with
    | ind w ih =>
      by_cases hwn : w < n
      · rw [wval_input _ x w hwn, wval_input _ x w hwn]
      · have hk : w - n < C.gates.length := by omega
        have hk' : w - n < (rewireAnd C j u v).gates.length := by
          rw [rewireAnd_length]
          exact hk
        have hw_eq : w = n + (w - n) := by omega
        have hnew : wval (rewireAnd C j u v) x (n + (w - n)) =
            (gateAt (rewireAnd C j u v) (w - n)).op.eval
              ((gateAt (rewireAnd C j u v) (w - n)).inputs.map fun z => wval C x z) := by
          rw [wval_gate_eval hAO' x hk', gate_inputs_eq hAO' hk']
          simp only [List.map_cons, List.map_nil]
          rw [ih (opnd (rewireAnd C j u v) (w - n) 0) (by
            have := opnd_lt hAO' hk' 0
            omega) (by have := opnd_lt hAO' hk' 0; omega)]
          rw [ih (opnd (rewireAnd C j u v) (w - n) 1) (by
            have := opnd_lt hAO' hk' 1
            omega) (by have := opnd_lt hAO' hk' 1; omega)]
        rw [hw_eq, hnew, rewireAnd_gateAt hj]
        by_cases hkj : w - n = j
        · rw [ite_eq_left hkj]
          simpa only [List.map_cons, List.map_nil, GateOp.eval,
            List.all_cons, List.all_nil, Bool.and_true, id_eq, hkj, gateVal_eq_wval] using hval x
        · rw [ite_eq_right hkj, gate_inputs_eq hAO hk]
          simp only [List.map_cons, List.map_nil]
          exact (wval_gate_eval hAO x hk).symm
  · rw [wval_ge_len C x (by omega), wval_ge_len (rewireAnd C j u v) x (by
      rw [rewireAnd_length]
      omega)]

lemma rewireAnd_junk {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {j u v : ℕ}
    (hj : j < C.gates.length) (hu : u < n + j) (hv : v < n + j)
    (hand : (gateAt C j).op = .and)
    (hval : ∀ x : Fin n → Bool,
      (wval C x u && wval C x v) = gateVal n C j x) :
    junk G (rewireAnd C j u v) = junk G C := by
  have hop (i : ℕ) : (gateAt (rewireAnd C j u v) i).op = (gateAt C i).op := by
    rw [rewireAnd_gateAt hj]
    by_cases hij : i = j
    · subst i
      simpa using hand.symm
    · simp [hij]
  ext i
  change (i ∈ (Finset.range (rewireAnd C j u v).gates.length).filter
      (fun k => IsDirtyAnd n G (rewireAnd C j u v) k)) ↔
    i ∈ (Finset.range C.gates.length).filter (fun k => IsDirtyAnd n G C k)
  rw [Finset.mem_filter, Finset.mem_filter, rewireAnd_length]
  simp only [IsDirtyAnd, IsDirty, hop, rewireAnd_length, gateVal_eq_wval,
    rewireAnd_values hAO hj hu hv hval]

lemma rewireAnd_least {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {j u v : ℕ}
    (hj : j < C.gates.length) (hu : u < n + j) (hv : v < n + j)
    (hval : ∀ x : Fin n → Bool,
      (wval C x u && wval C x v) = gateVal n C j x) :
    IsLeastAO G (rewireAnd C j u v) := by
  refine ⟨rewireAnd_isAO2 hL.1 hj hu hv, ?_, ?_⟩
  · funext x
    change wval (rewireAnd C j u v) x C.output = _
    rw [rewireAnd_values hL.1 hj hu hv hval]
    exact congrFun hL.2.1 x
  · intro D hD hDfun
    simpa only [Circuit.size, rewireAnd_length] using hL.2.2 D hD hDfun

def delWire (n j r w : ℕ) : ℕ :=
  if w = n + j then r else if n + j < w then w - 1 else w

def delCircuit (n : ℕ) (C : Circuit) (j r : ℕ) : Circuit :=
  { gates := (C.gates.eraseIdx j).map (fun g => { g with inputs := g.inputs.map (delWire n j r) })
    output := delWire n j r C.output }

lemma delCircuit_len (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) (r : ℕ) :
    (delCircuit n C j r).gates.length = C.gates.length - 1 := by
  simp [delCircuit, List.length_eraseIdx, hj]

lemma delCircuit_gateAt_lt {n : ℕ} {C : Circuit} {j r i : ℕ}
    (hj : j < C.gates.length) (hi : i < j) :
    gateAt (delCircuit n C j r) i =
      { (gateAt C i) with inputs := (gateAt C i).inputs.map (delWire n j r) } := by
  have hi' : i < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
  rw [gateAt_eq hi', gateAt_eq (by omega)]
  simp only [delCircuit, List.getElem_map]
  rw [List.getElem_eraseIdx_of_lt (by rw [List.length_eraseIdx, if_pos hj]; omega) hi]

lemma delCircuit_gateAt_ge {n : ℕ} {C : Circuit} {j r i : ℕ}
    (hj : j < C.gates.length) (hji : j ≤ i) (hi : i < C.gates.length - 1) :
    gateAt (delCircuit n C j r) i =
      { (gateAt C (i + 1)) with inputs := (gateAt C (i + 1)).inputs.map (delWire n j r) } := by
  have hi' : i < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
  rw [gateAt_eq hi', gateAt_eq (by omega)]
  simp only [delCircuit, List.getElem_map]
  rw [List.getElem_eraseIdx_of_ge (by rw [List.length_eraseIdx, if_pos hj]; omega) hji]

lemma delCircuit_isAO2 {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j r : ℕ}
    (hj : j < C.gates.length) (hr : r < n + j) : IsAO2 n (delCircuit n C j r) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [delCircuit, List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    exact hAO.1 g0 (List.mem_of_mem_eraseIdx hg0)
  · intro i hi w hw
    rw [delCircuit_len n C hj r] at hi
    by_cases hij : i < j
    · rw [delCircuit_gateAt_lt hj hij] at hw
      simp only [List.mem_map] at hw
      rcases hw with ⟨u, hu, rfl⟩
      have hult : u < n + i := hAO.2.1 i (by omega) u hu
      unfold delWire
      rw [if_neg (by omega), if_neg (by omega)]
      exact hult
    · rw [delCircuit_gateAt_ge hj (by omega) hi] at hw
      simp only [List.mem_map] at hw
      rcases hw with ⟨u, hu, rfl⟩
      have hult : u < n + (i + 1) := hAO.2.1 (i + 1) (by omega) u hu
      unfold delWire
      split_ifs <;> omega
  · intro g hg
    simp only [delCircuit, List.mem_map] at hg
    rcases hg with ⟨g0, hg0, rfl⟩
    simp only [List.length_map]
    exact hAO.2.2 g0 (List.mem_of_mem_eraseIdx hg0)

lemma delCircuit_opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j r i : ℕ}
    (hj : j < C.gates.length) (hi : i < j) (b : Fin 2) :
    opnd (delCircuit n C j r) i b = delWire n j r (opnd C i b) := by
  unfold opnd
  rw [delCircuit_gateAt_lt hj hi, gate_inputs_eq hAO (by omega)]
  fin_cases b <;> rfl

lemma delCircuit_opnd_ge {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j r i : ℕ}
    (hj : j < C.gates.length) (hji : j ≤ i) (hi : i < C.gates.length - 1) (b : Fin 2) :
    opnd (delCircuit n C j r) i b = delWire n j r (opnd C (i + 1) b) := by
  unfold opnd
  rw [delCircuit_gateAt_ge hj hji hi, gate_inputs_eq hAO (by omega)]
  fin_cases b <;> rfl


lemma graphFun_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  unfold graphFun; simp

lemma graphFun_unit_false {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (v : Fin n) :
    graphFun G ∅ (fun w => decide (w = v)) = false := by
  rw [Bool.eq_false_iff, ne_eq, graphFun_iff]
  rintro ⟨a, b, hab, ha, hb⟩
  simp only [decide_eq_true_eq] at ha hb
  subst ha; subst hb
  exact G.loopless.irrefl _ hab

lemma graphFun_pair_iff {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] (u v : Fin n) :
    graphFun G ∅ (pairInput u v) = true ↔ G.Adj u v := by
  rw [graphFun_iff]
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    unfold pairInput at ha hb
    simp only [decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact absurd hab (G.loopless.irrefl _)
    · exact hab
    · exact hab.symm
    · exact absurd hab (G.loopless.irrefl _)
  · intro huv
    exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

-- Consequences of IsLeastAO + IsLiftFixedPoint

lemma output_bounds {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v) :
    n ≤ C.output ∧ C.output < n + C.gates.length := by
  obtain ⟨u, v, huv⟩ := hne
  have hfun : ∀ x, wval C x C.output = graphFun G ∅ x := fun x => congrFun hL.2.1 x
  constructor
  · by_contra hlt
    push Not at hlt
    have h1 := hfun (fun w => decide (w = ⟨C.output, hlt⟩))
    rw [wval_input C _ C.output hlt, graphFun_unit_false] at h1
    simp at h1
  · by_contra hge
    push Not at hge
    have h1 := hfun (pairInput u v)
    rw [wval_ge_len C _ hge, (graphFun_pair_iff u v).mpr huv] at h1
    cases h1

lemma delCircuit_unused_values {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    (x : Fin n → Bool) {j r : ℕ} (hj : j < C.gates.length) (hr : r < n + j)
    (hread : ∀ k < C.gates.length, n + j ∉ (gateAt C k).inputs) :
    ∀ w < n + C.gates.length, w ≠ n + j →
      wval (delCircuit n C j r) x (delWire n j r w) = wval C x w := by
  have hAO' := delCircuit_isAO2 hAO hj hr
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hneq
    by_cases hwn : w < n
    · have hdw : delWire n j r w = w := by
        unfold delWire
        rw [if_neg (by omega), if_neg (by omega)]
      rw [hdw, wval_input _ x w hwn, wval_input _ x w hwn]
    · have hchild (k : ℕ) (hk : k < C.gates.length) (b : Fin 2) :
          opnd C k b ≠ n + j := by
        intro heq
        exact hread k hk (heq ▸ opnd_mem hAO hk b)
      by_cases hlt : w < n + j
      · have hk : w - n < j := by omega
        have hdw : delWire n j r w = n + (w - n) := by
          unfold delWire
          rw [if_neg hneq, if_neg (by omega)]
          omega
        have hw_eq : w = n + (w - n) := by omega
        rw [hdw]
        conv_rhs => rw [hw_eq]
        have hk' : w - n < (delCircuit n C j r).gates.length := by
          rw [delCircuit_len n C hj r]
          omega
        rw [wval_gate_eval hAO' x hk', wval_gate_eval hAO x (by omega)]
        have hg := delCircuit_gateAt_lt (n := n) (r := r) hj hk
        rw [delCircuit_opnd_lt hAO hj hk 0, delCircuit_opnd_lt hAO hj hk 1]
        have h0 := ih (opnd C (w - n) 0)
          (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega)
          (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega)
          (hchild (w - n) (by omega) 0)
        have h1 := ih (opnd C (w - n) 1)
          (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega)
          (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega)
          (hchild (w - n) (by omega) 1)
        rw [h0, h1, hg]
      · have hgt : n + j < w := by omega
        have hk : w - n - 1 < C.gates.length - 1 := by omega
        have hjk : j ≤ w - n - 1 := by omega
        have hdw : delWire n j r w = n + (w - n - 1) := by
          unfold delWire
          rw [if_neg hneq, if_pos hgt]
          omega
        have hw_eq : w = n + (w - n - 1 + 1) := by omega
        rw [hdw]
        conv_rhs => rw [hw_eq]
        have hk' : w - n - 1 < (delCircuit n C j r).gates.length := by
          rw [delCircuit_len n C hj r]
          omega
        rw [wval_gate_eval hAO' x hk', wval_gate_eval hAO x (by omega)]
        have hg := delCircuit_gateAt_ge (n := n) (r := r) hj hjk hk
        rw [delCircuit_opnd_ge hAO hj hjk hk 0, delCircuit_opnd_ge hAO hj hjk hk 1]
        have h0 := ih (opnd C (w - n - 1 + 1) 0)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega)
          (hchild (w - n - 1 + 1) (by omega) 0)
        have h1 := ih (opnd C (w - n - 1 + 1) 1)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega)
          (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega)
          (hchild (w - n - 1 + 1) (by omega) 1)
        rw [h0, h1, hg]

lemma least_gate_has_reader {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {j : ℕ} (hj : j < C.gates.length) (hout : C.output ≠ n + j) :
    ∃ k < C.gates.length, n + j ∈ (gateAt C k).inputs := by
  by_contra hnone
  have hread : ∀ k < C.gates.length, n + j ∉ (gateAt C k).inputs := by
    intro k hk hr
    exact hnone ⟨k, hk, hr⟩
  obtain ⟨a, b, hab⟩ := hne
  have hn : 0 < n := by
    have := a.isLt
    omega
  have hbounds := output_bounds hL ⟨a, b, hab⟩
  let D := delCircuit n C j 0
  have hD : IsAO2 n D := delCircuit_isAO2 hL.1 hj (by omega)
  have hfun : circuitFun n D = graphFun G ∅ := by
    funext x
    change wval D x D.output = _
    rw [← congrFun hL.2.1 x]
    exact delCircuit_unused_values hL.1 x hj (by omega) hread C.output hbounds.2 hout
  have hsize := hL.2.2 D hD hfun
  simp only [Circuit.size, D, delCircuit_len n C hj 0] at hsize
  omega

lemma nested_absorb_rewire {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {g h u v w : ℕ}
    (hgh : g < h) (hh : h < C.gates.length)
    (hu : u < n + g) (hv : v < n + g) (hw : w < n + h)
    (hand : (gateAt C h).op = .and)
    (hgshape : ∀ x : Fin n → Bool,
      gateVal n C g x = (wval C x u && wval C x v))
    (hhshape : ∀ x : Fin n → Bool,
      gateVal n C h x = (gateVal n C g x && wval C x w))
    (hdom : ∀ x : Fin n → Bool, wval C x w = true → wval C x u = true) :
    IsLeastAO G (rewireAnd C h v w) ∧
      (rewireAnd C h v w).size = C.size ∧
      junk G (rewireAnd C h v w) = junk G C ∧
      (gateAt (rewireAnd C h v w) h).inputs = [v, w] := by
  have hvh : v < n + h := by omega
  have hval (x : Fin n → Bool) :
      (wval C x v && wval C x w) = gateVal n C h x := by
    rw [hhshape, hgshape]
    cases hwx : wval C x w with
    | false => simp
    | true => simp [hdom x hwx]
  refine ⟨rewireAnd_least hL hh hvh hw hval, ?_,
    rewireAnd_junk G hL.1 hh hvh hw hand hval, ?_⟩
  · simp only [Circuit.size, rewireAnd_length]
  · rw [rewireAnd_gateAt hh]
    simp

lemma least_no_private_nested_absorption {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ a b : Fin n, G.Adj a b)
    {g h u v w : ℕ} (hgh : g < h) (hh : h < C.gates.length)
    (hu : u < n + g) (hv : v < n + g) (hw : w < n + h)
    (hwg : w ≠ n + g) (hout : C.output ≠ n + g)
    (hand : (gateAt C h).op = .and)
    (hgshape : ∀ x : Fin n → Bool,
      gateVal n C g x = (wval C x u && wval C x v))
    (hhshape : ∀ x : Fin n → Bool,
      gateVal n C h x = (gateVal n C g x && wval C x w))
    (hdom : ∀ x : Fin n → Bool, wval C x w = true → wval C x u = true)
    (hprivate : ∀ k < C.gates.length, n + g ∈ (gateAt C k).inputs → k = h) : False := by
  have hnew := nested_absorb_rewire hL hgh hh hu hv hw hand hgshape hhshape hdom
  obtain ⟨k, hk, hkg⟩ := least_gate_has_reader hnew.1 hne
    (j := g) (by rw [rewireAnd_length]; omega) hout
  rw [rewireAnd_length] at hk
  rw [rewireAnd_gateAt hh] at hkg
  by_cases hkh : k = h
  · rw [if_pos hkh] at hkg
    change n + g ∈ [v, w] at hkg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hkg
    rcases hkg with heq | heq
    · omega
    · exact hwg heq.symm
  · rw [if_neg hkh] at hkg
    exact hkh (hprivate k hk hkg)

lemma foldl_cones_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (coneStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, coneStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_cones_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (coneStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (coneStep n acc g).length := by
      simp only [coneStep, List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones; rw [foldl_cones_len]; simp

lemma foldl_cones_getD_gate (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (coneStep n) acc).getD (acc.length + j) [] =
      (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (acc.length + j)))).flatMap
        (fun w => (w - n) :: (gs.foldl (coneStep n) acc).getD (w - n) []) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero]
      set acc' := coneStep n acc g
      have hlen : acc.length < acc'.length := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]; omega
      rw [foldl_cones_getD_lt n gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + acc.length))).flatMap
            (fun w => (w - n) :: acc.getD (w - n) []) := by
        simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
      rw [hlhs]
      apply List.flatMap_congr
      intro w hw
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      have hwn : w - n < acc.length := by omega
      have hwn' : w - n < acc'.length := by omega
      rw [foldl_cones_getD_lt n gs acc' (w - n) hwn']
      simp only [acc', coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := coneStep n acc g
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', coneStep, List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      exact ih acc' j' hj'

lemma inCone_lt_len {n : ℕ} {C : Circuit} {i j : ℕ} (h : InCone n C i j) : j < C.gates.length := by
  by_contra hge
  unfold InCone at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [cones_length]; omega)] at h
  simp at h

lemma inCone_iff {n : ℕ} {C : Circuit} {i j : ℕ} (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone cones
  have h := foldl_cones_getD_gate n C.gates [] j hj
  simp only [List.length_nil, Nat.zero_add] at h
  rw [h, ← gateAt_eq hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩; exact ⟨w, hw1, hw2, hw3, hw4⟩
  · rintro ⟨w, hw1, hw2, hw3, hw4⟩; exact ⟨w, ⟨hw1, hw2, hw3⟩, hw4⟩

lemma inCone_lt {n : ℕ} {C : Circuit} {i j : ℕ} : InCone n C i j → i < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro h
    have hj := inCone_lt_len h
    rw [inCone_iff hj] at h
    rcases h with ⟨w, _, hnw, hwnj, rfl | hsub⟩
    · omega
    · have := ih (w - n) (by omega) hsub; omega

lemma inCone_trans {n : ℕ} {C : Circuit} {i j k : ℕ} (h1 : InCone n C i j) (h2 : InCone n C j k) :
    InCone n C i k := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    have hk := inCone_lt_len h2
    rw [inCone_iff hk] at h2 ⊢
    rcases h2 with ⟨w, hw, hnw, hwnk, rfl | hsub⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr h1⟩
    · exact ⟨w, hw, hnw, hwnk, Or.inr (ih (w - n) (by omega) hsub)⟩

-- OrReaches and orIn characterization


lemma rewireAnd_cone_mono {n : ℕ} {C : Circuit} {j u v : ℕ}
    (hj : j < C.gates.length)
    (hu : n ≤ u → InCone n C (u - n) j)
    (hv : n ≤ v → InCone n C (v - n) j) :
    ∀ i k : ℕ, InCone n (rewireAnd C j u v) i k → InCone n C i k := by
  intro i k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro hik
    have hk' := inCone_lt_len hik
    have hk : k < C.gates.length := by simpa only [rewireAnd_length] using hk'
    obtain ⟨w, hw, hnw, hwk, hiw⟩ := (inCone_iff hk').mp hik
    have hdeep : i = w - n ∨ InCone n C i (w - n) :=
      hiw.imp id (ih (w - n) (by omega))
    rw [rewireAnd_gateAt hj] at hw
    by_cases hkj : k = j
    · subst k
      rw [if_pos rfl] at hw
      change w ∈ [u, v] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      have hwj : InCone n C (w - n) j := by
        rcases hw with rfl | rfl
        · exact hu hnw
        · exact hv hnw
      rcases hdeep with rfl | hiw
      · exact hwj
      · exact inCone_trans hiw hwj
    · rw [if_neg hkj] at hw
      exact (inCone_iff hk).mpr ⟨w, hw, hnw, hwk, hdeep⟩

lemma rewireAnd_topForm {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) (hTF : TopForm G C) {j u v : ℕ}
    (hj : j < C.gates.length) (hu : u < n + j) (hv : v < n + j)
    (hand : (gateAt C j).op = .and)
    (hucone : n ≤ u → InCone n C (u - n) j)
    (hvcone : n ≤ v → InCone n C (v - n) j)
    (hval : ∀ x : Fin n → Bool,
      (wval C x u && wval C x v) = gateVal n C j x) :
    TopForm G (rewireAnd C j u v) := by
  have hop (k : ℕ) : (gateAt (rewireAnd C j u v) k).op = (gateAt C k).op := by
    rw [rewireAnd_gateAt hj]
    by_cases hkj : k = j
    · subst k
      simpa using hand.symm
    · simp [hkj]
  intro a ha b hb haop habel hbop hab
  have ha' : a < C.gates.length := by simpa only [rewireAnd_length] using ha
  have hb' : b < C.gates.length := by simpa only [rewireAnd_length] using hb
  have hab' := rewireAnd_cone_mono hj hucone hvcone a b hab
  have habel' : BelowF G C a := by
    intro x hx
    apply habel x
    change wval (rewireAnd C j u v) x (n + a) = true
    rw [rewireAnd_values hAO hj hu hv hval]
    exact hx
  exact hTF a ha' b hb' (by simpa only [hop] using haop) habel'
    (by simpa only [hop] using hbop) hab'

lemma rewireAnd_excludes_ancestor {n : ℕ} {C : Circuit} {g j u v : ℕ}
    (hj : j < C.gates.length) (hgj : g < j) (hu : u < n + g)
    (hvg : v ≠ n + g) (hvpure : n ≤ v → ¬ InCone n C g (v - n))
    (hucone : n ≤ u → InCone n C (u - n) j)
    (hvcone : n ≤ v → InCone n C (v - n) j) :
    ¬ InCone n (rewireAnd C j u v) g j := by
  intro hgj'
  have hj' : j < (rewireAnd C j u v).gates.length := by
    simpa only [rewireAnd_length] using hj
  obtain ⟨w, hw, hnw, _, hgw⟩ := (inCone_iff hj').mp hgj'
  rw [rewireAnd_gateAt hj] at hw
  simp only [if_pos rfl] at hw
  change w ∈ [u, v] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · rcases hgw with heq | hcone
    · omega
    · have := inCone_lt hcone
      omega
  · rcases hgw with heq | hcone
    · apply hvg
      omega
    · exact hvpure hnw (rewireAnd_cone_mono hj hucone hvcone g _ hcone)

end PEqualNP.Outside.L_meta_5012.RestrictionCone
