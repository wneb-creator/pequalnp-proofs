import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012.RestrictionNestedShared

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



lemma wval_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {x y : Fin n → Bool}
    (hxy : ∀ i : Fin n, x i = true → y i = true) :
    ∀ w : ℕ, wval C x w = true → wval C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwx
    by_cases hwn : w < n
    · rw [wval_input C x w hwn] at hwx
      rw [wval_input C y w hwn]
      exact hxy ⟨w, hwn⟩ hwx
    · by_cases hwlen : w < n + C.gates.length
      · have hj : w - n < C.gates.length := by omega
        have hw_eq : w = n + (w - n) := by omega
        rw [hw_eq] at hwx ⊢
        have h0 : opnd C (w - n) 0 < w := by have := opnd_lt hAO hj 0; omega
        have h1 : opnd C (w - n) 1 < w := by have := opnd_lt hAO hj 1; omega
        rcases hAO.1 _ (gateAt_mem hj) with hand | hor
        · rw [wval_gate_and hAO x hj hand, Bool.and_eq_true] at hwx
          rw [wval_gate_and hAO y hj hand, Bool.and_eq_true]
          exact ⟨ih _ h0 hwx.1, ih _ h1 hwx.2⟩
        · rw [wval_gate_or hAO x hj hor, Bool.or_eq_true] at hwx
          rw [wval_gate_or hAO y hj hor, Bool.or_eq_true]
          exact hwx.imp (ih _ h0) (ih _ h1)
      · rw [wval_ge_len C x (by omega)] at hwx; cases hwx

-- Cone characterization

lemma rewireAnd_values_at {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j u v : ℕ} (hj : j < C.gates.length) (hu : u < n + j) (hv : v < n + j)
    (x : Fin n → Bool)
    (hval : (wval C x u && wval C x v) = gateVal n C j x) :
    ∀ (w : ℕ),
      wval (rewireAnd C j u v) x w = wval C x w := by
  have hAO' := rewireAnd_isAO2 hAO hj hu hv
  intro w
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
            List.all_cons, List.all_nil, Bool.and_true, id_eq, hkj, gateVal_eq_wval] using hval
        · rw [ite_eq_right hkj, gate_inputs_eq hAO hk]
          simp only [List.map_cons, List.map_nil]
          exact (wval_gate_eval hAO x hk).symm
  · rw [wval_ge_len C x (by omega), wval_ge_len (rewireAnd C j u v) x (by
      rw [rewireAnd_length]
      omega)]



lemma rewireAnd_values_le {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j u v : ℕ} (hj : j < C.gates.length) (hu : u < n + j) (hv : v < n + j)
    (hval : ∀ x : Fin n → Bool,
      (wval C x u && wval C x v) = true → gateVal n C j x = true) :
    ∀ (x : Fin n → Bool) (w : ℕ),
      wval (rewireAnd C j u v) x w = true → wval C x w = true := by
  have hAO' := rewireAnd_isAO2 hAO hj hu hv
  intro x w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro htrue
    by_cases hwn : w < n
    · rw [wval_input _ x w hwn] at htrue ⊢
      exact htrue
    by_cases hwlen : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hk' : k < (rewireAnd C j u v).gates.length := by
        simpa only [rewireAnd_length] using hk
      by_cases hkj : k = j
      · subst k
        have hop : (gateAt (rewireAnd C j u v) j).op = .and := by
          rw [rewireAnd_gateAt hj]
          simp
        rw [wval_gate_and hAO' x hk' hop] at htrue
        simp [opnd, rewireAnd_gateAt hj] at htrue
        apply hval x
        rw [Bool.and_eq_true]
        exact ⟨ih _ hu htrue.1, ih _ hv htrue.2⟩
      · have hg : gateAt (rewireAnd C j u v) k = gateAt C k := by
          rw [rewireAnd_gateAt hj, if_neg hkj]
        have ho (b : Fin 2) : opnd (rewireAnd C j u v) k b = opnd C k b := by
          simp only [opnd, hg]
        have h0 := opnd_lt hAO hk 0
        have h1 := opnd_lt hAO hk 1
        rcases hAO.1 _ (gateAt_mem hk) with hand | hor
        · rw [wval_gate_and hAO' x hk' (by simpa only [hg] using hand),
            ho 0, ho 1, Bool.and_eq_true] at htrue
          rw [wval_gate_and hAO x hk hand, Bool.and_eq_true]
          exact ⟨ih _ h0 htrue.1, ih _ h1 htrue.2⟩
        · rw [wval_gate_or hAO' x hk' (by simpa only [hg] using hor),
            ho 0, ho 1, Bool.or_eq_true] at htrue
          rw [wval_gate_or hAO x hk hor, Bool.or_eq_true]
          exact htrue.imp (ih _ h0) (ih _ h1)
    · rw [wval_ge_len (rewireAnd C j u v) x (by rw [rewireAnd_length]; omega)] at htrue
      cases htrue

lemma rewireAnd_lowering_least {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) {j u v : ℕ}
    (hj : j < C.gates.length) (hu : u < n + j) (hv : v < n + j)
    (hval : ∀ x : Fin n → Bool,
      (wval C x u && wval C x v) = true → gateVal n C j x = true)
    (hedge : ∀ a b : Fin n, G.Adj a b →
      (wval C (pairInput a b) u && wval C (pairInput a b) v) =
        gateVal n C j (pairInput a b)) :
    IsLeastAO G (rewireAnd C j u v) := by
  have hAO' := rewireAnd_isAO2 hL.1 hj hu hv
  refine ⟨hAO', ?_, ?_⟩
  · funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      have hv := rewireAnd_values_le hL.1 hj hu hv hval x C.output hx
      exact (congrFun hL.2.1 x).symm.trans hv
    · intro hx
      obtain ⟨a, b, hab, ha, hb⟩ := (graphFun_iff x).mp hx
      have hp : wval (rewireAnd C j u v) (pairInput a b) C.output = true := by
        rw [rewireAnd_values_at hL.1 hj hu hv (pairInput a b) (hedge a b hab)]
        exact (congrFun hL.2.1 (pairInput a b)).trans ((graphFun_pair_iff a b).mpr hab)
      apply wval_mono hAO' (x := pairInput a b) (y := x) _ C.output hp
      intro p hp
      simp only [pairInput, decide_eq_true_eq] at hp
      rcases hp with rfl | rfl <;> assumption
  · intro D hD hDfun
    simpa only [Circuit.size, rewireAnd_length] using hL.2.2 D hD hDfun



lemma rewireAnd_outside_cone {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j u v : ℕ} (hj : j < C.gates.length) (hu : u < n + j) (hv : v < n + j)
    (x : Fin n → Bool) : ∀ w < n + C.gates.length,
    w ≠ n + j → (n ≤ w → ¬ InCone n C j (w - n)) →
    wval (rewireAnd C j u v) x w = wval C x w := by
  have hAO' := rewireAnd_isAO2 hAO hj hu hv
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwj hcone
    by_cases hwn : w < n
    · rw [wval_input _ x w hwn, wval_input _ x w hwn]
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    have hk : k < C.gates.length := by omega
    have hkj : k ≠ j := by omega
    have hk' : k < (rewireAnd C j u v).gates.length := by
      simpa only [rewireAnd_length] using hk
    have hg : gateAt (rewireAnd C j u v) k = gateAt C k := by
      rw [rewireAnd_gateAt hj, if_neg hkj]
    have ho (b : Fin 2) : opnd (rewireAnd C j u v) k b = opnd C k b := by
      simp only [opnd, hg]
    have hchild (b : Fin 2) :
        wval (rewireAnd C j u v) x (opnd C k b) = wval C x (opnd C k b) := by
      have hb := opnd_lt hAO hk b
      apply ih _ hb (by omega)
      · intro heq
        apply hcone (by omega)
        simp only [Nat.add_sub_cancel_left]
        apply (inCone_iff hk).mpr
        exact ⟨opnd C k b, opnd_mem hAO hk b, by omega, hb, Or.inl (by omega)⟩
      · intro hnb hsub
        apply hcone (by omega)
        simp only [Nat.add_sub_cancel_left]
        apply (inCone_iff hk).mpr
        exact ⟨opnd C k b, opnd_mem hAO hk b, hnb, hb, Or.inr hsub⟩
    rw [wval_gate_eval hAO' x hk', wval_gate_eval hAO x hk, hg, ho 0, ho 1,
      hchild 0, hchild 1]

lemma rewireAnd_clean {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {j u v : ℕ}
    (hj : j < C.gates.length) (hu : u < n + j) (hv : v < n + j)
    (hval : ∀ x : Fin n → Bool,
      (wval C x u && wval C x v) = true → gateVal n C j x = true)
    (hclean : ∀ x : Fin n → Bool,
      (wval C x u && wval C x v) = true → graphFun G ∅ x = true) :
    BelowF G (rewireAnd C j u v) j := by
  have hAO' := rewireAnd_isAO2 hAO hj hu hv
  intro x hx
  have hj' : j < (rewireAnd C j u v).gates.length := by
    simpa only [rewireAnd_length] using hj
  have hop : (gateAt (rewireAnd C j u v) j).op = .and := by
    rw [rewireAnd_gateAt hj]
    simp
  rw [gateVal_eq_wval, wval_gate_and hAO' x hj' hop] at hx
  simp [opnd, rewireAnd_gateAt hj] at hx
  apply hclean x
  rw [Bool.and_eq_true]
  exact ⟨rewireAnd_values_le hAO hj hu hv hval x u hx.1,
    rewireAnd_values_le hAO hj hu hv hval x v hx.2⟩

lemma rewireAnd_junk_subset {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {j u v : ℕ}
    (hj : j < C.gates.length) (hu : u < n + j) (hv : v < n + j)
    (hand : (gateAt C j).op = .and)
    (hval : ∀ x : Fin n → Bool,
      (wval C x u && wval C x v) = true → gateVal n C j x = true)
    (hclean : BelowF G (rewireAnd C j u v) j) :
    junk G (rewireAnd C j u v) ⊆ (junk G C).erase j := by
  intro k hk
  have hmem := Finset.mem_filter.mp hk
  have hlen : k < C.gates.length := by
    simpa only [Finset.mem_range, rewireAnd_length] using hmem.1
  obtain ⟨hop, _, x, hx, hFx⟩ := hmem.2
  have hkj : k ≠ j := by
    intro hkj
    subst k
    exact Bool.noConfusion ((hclean x hx).symm.trans hFx)
  apply Finset.mem_erase.mpr
  refine ⟨hkj, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlen, ?_⟩⟩
  refine ⟨?_, hlen, x, ?_, hFx⟩
  · simpa [rewireAnd_gateAt hj, hkj] using hop
  · exact rewireAnd_values_le hAO hj hu hv hval x (n + k) hx



lemma no_independent_clean_lowering {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hfirst : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    {C : Circuit} (hL : IsLeastAO G C) {g h u v : ℕ}
    (hjunk : junk G C = {g, h}) (hgh : g ≠ h) (hind : ¬ InCone n C g h)
    (hu : u < n + g) (hv : v < n + g)
    (hval : ∀ x : Fin n → Bool,
      (wval C x u && wval C x v) = true → gateVal n C g x = true)
    (hclean : ∀ x : Fin n → Bool,
      (wval C x u && wval C x v) = true → graphFun G ∅ x = true)
    (hedge : ∀ a b : Fin n, G.Adj a b →
      (wval C (pairInput a b) u && wval C (pairInput a b) v) =
        gateVal n C g (pairInput a b)) : False := by
  have hgmem : g ∈ junk G C := by simp [hjunk]
  have hhmem : h ∈ junk G C := by simp [hjunk]
  obtain ⟨hgOp, hg, _⟩ := (Finset.mem_filter.mp hgmem).2
  obtain ⟨hhOp, hh, x, hx, hFx⟩ := (Finset.mem_filter.mp hhmem).2
  have hL' := rewireAnd_lowering_least hL hg hu hv hval hedge
  have hclean' := rewireAnd_clean hL.1 hg hu hv hval hclean
  have hsub : junk G (rewireAnd C g u v) ⊆ {h} := by
    have hs := rewireAnd_junk_subset hL.1 hg hu hv hgOp hval hclean'
    simpa [hjunk, hgh] using hs
  have hh' : h ∈ junk G (rewireAnd C g u v) := by
    have hlen : h < (rewireAnd C g u v).gates.length := by
      simpa only [rewireAnd_length] using hh
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hlen, ?_, hlen, x, ?_, hFx⟩
    · simpa [rewireAnd_gateAt hg, Ne.symm hgh] using hhOp
    · rw [gateVal_eq_wval,
        rewireAnd_outside_cone hL.1 hg hu hv x (n + h) (by omega) (by omega)]
      · exact hx
      · intro _
        simpa only [Nat.add_sub_cancel_left] using hind
  have heq : junk G (rewireAnd C g u v) = {h} :=
    Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hh')
  apply hfirst (rewireAnd C g u v) hL'
  rw [heq]
  simp

lemma star_below_product {n : ℕ} (P Q : Finset (Fin n)) (z : Fin n)
    (hz : z ∈ P) (x : Fin n → Bool)
    (hstar : (x z && decide (∃ q ∈ Q, x q = true)) = true) :
    (decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)) = true := by
  rw [Bool.and_eq_true] at hstar ⊢
  exact ⟨decide_eq_true ⟨z, hz, hstar.1⟩, hstar.2⟩

lemma star_below_graph {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (Q : Finset (Fin n)) (z : Fin n) (hQ : ∀ q ∈ Q, G.Adj z q)
    (x : Fin n → Bool)
    (hstar : (x z && decide (∃ q ∈ Q, x q = true)) = true) :
    graphFun G ∅ x = true := by
  rw [Bool.and_eq_true] at hstar
  obtain ⟨hzx, hQx⟩ := hstar
  obtain ⟨q, hq, hqx⟩ := of_decide_eq_true hQx
  have he : ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true :=
    ⟨z, q, hQ q hq, hzx, hqx⟩
  simpa [graphFun] using he

lemma star_agrees_on_edges {n : ℕ} (G : SimpleGraph (Fin n))
    (P Q : Finset (Fin n)) (z : Fin n) (hz : z ∈ P)
    (hcover : ∀ u v, G.Adj u v →
      ((decide (∃ p ∈ P, pairInput u v p = true) &&
        decide (∃ q ∈ Q, pairInput u v q = true)) = true) → u = z ∨ v = z)
    (u v : Fin n) (huv : G.Adj u v) :
    (pairInput u v z && decide (∃ q ∈ Q, pairInput u v q = true)) =
      (decide (∃ p ∈ P, pairInput u v p = true) &&
        decide (∃ q ∈ Q, pairInput u v q = true)) := by
  apply Bool.eq_iff_iff.mpr
  constructor
  · exact star_below_product P Q z hz (pairInput u v)
  · intro hg
    have hc := hcover u v huv hg
    rw [Bool.and_eq_true] at hg ⊢
    refine ⟨?_, hg.2⟩
    rcases hc with rfl | rfl <;> simp [pairInput]

lemma clean_star_replacement {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (P Q : Finset (Fin n)) (z : Fin n)
    (hsem : ∀ x : Fin n → Bool, gateVal n C g x =
      (decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)))
    (hz : z ∈ P) (hQ : ∀ q ∈ Q, G.Adj z q)
    (hcover : ∀ u v, G.Adj u v →
      gateVal n C g (pairInput u v) = true → u = z ∨ v = z) :
    (∀ x : Fin n → Bool,
      (x z && decide (∃ q ∈ Q, x q = true)) = true → gateVal n C g x = true) ∧
    (∀ x : Fin n → Bool,
      (x z && decide (∃ q ∈ Q, x q = true)) = true → graphFun G ∅ x = true) ∧
    (∀ u v, G.Adj u v →
      (pairInput u v z && decide (∃ q ∈ Q, pairInput u v q = true)) =
        gateVal n C g (pairInput u v)) := by
  refine ⟨?_, star_below_graph G Q z hQ, ?_⟩
  · intro x hx
    rw [hsem]
    exact star_below_product P Q z hz x hx
  · intro u v huv
    rw [hsem]
    apply star_agrees_on_edges G P Q z hz _ u v huv
    intro a b hab hg
    apply hcover a b hab
    simpa only [hsem] using hg


lemma no_independent_clean_star {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hfirst : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    {C : Circuit} (hL : IsLeastAO G C) {g h v : ℕ}
    (hjunk : junk G C = {g, h}) (hgh : g ≠ h) (hind : ¬ InCone n C g h)
    (P Q : Finset (Fin n)) (z : Fin n) (hz : z ∈ P)
    (hv : v < n + g) (hvsem : ∀ x : Fin n → Bool,
      wval C x v = decide (∃ q ∈ Q, x q = true))
    (hgsem : ∀ x : Fin n → Bool, gateVal n C g x =
      (decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)))
    (hQ : ∀ q ∈ Q, G.Adj z q)
    (hcover : ∀ a b, G.Adj a b → gateVal n C g (pairInput a b) = true →
      a = z ∨ b = z) : False := by
  obtain ⟨hdown, hclean, hedge⟩ := clean_star_replacement G C g P Q z hgsem hz hQ hcover
  apply no_independent_clean_lowering hfirst hL hjunk hgh hind
    (u := z.val) (v := v) (by have := z.isLt; omega) hv
  · intro x hx
    rw [wval_input C x z.val z.isLt, hvsem] at hx
    exact hdown x hx
  · intro x hx
    rw [wval_input C x z.val z.isLt, hvsem] at hx
    exact hclean x hx
  · intro a b hab
    rw [wval_input C (pairInput a b) z.val z.isLt, hvsem]
    exact hedge a b hab



-- OrReaches and orIn characterization

lemma foldl_orSets_len (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) :
    (gs.foldl (orStep n) acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, orStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_orSets_getD_lt (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (i : ℕ) (hi : i < acc.length) :
    (gs.foldl (orStep n) acc).getD i [] = acc.getD i [] := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (orStep n acc g).length := by
      simp only [orStep, List.length_append, List.length_singleton]; omega
    rw [ih _ hlt]
    simp only [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma orSets_length (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  unfold orSets; rw [foldl_orSets_len]; simp

lemma foldl_orSets_getD_gate (n : ℕ) (gs : List Gate) (acc : List (List ℕ)) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl (orStep n) acc).getD (acc.length + j) [] =
      (acc.length + j) :: (match gs[j].op with
        | GateOp.or =>
          (gs[j].inputs.filter (fun w => decide (n ≤ w ∧ w < n + (acc.length + j)))).flatMap
            (fun w => (gs.foldl (orStep n) acc).getD (w - n) [])
        | _ => []) := by
  induction gs generalizing acc j with
  | nil => cases hj
  | cons g gs ih =>
    cases j with
    | zero =>
      simp only [Nat.add_zero, List.foldl_cons, List.getElem_cons_zero]
      set acc' := orStep n acc g
      have hlen : acc.length < acc'.length := by
        simp only [acc', orStep, List.length_append, List.length_singleton]; omega
      rw [foldl_orSets_getD_lt n gs acc' acc.length hlen]
      have hlhs : acc'.getD acc.length [] =
          acc.length :: (match g.op with
            | GateOp.or =>
              (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + acc.length))).flatMap
                (fun w => acc.getD (w - n) [])
            | _ => []) := by
        simp only [acc', orStep, List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl _),
          Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
        cases g.op <;> rfl
      rw [hlhs]
      congr 1
      cases g.op
      · rfl
      · apply List.flatMap_congr
        intro w hw
        simp only [List.mem_filter, decide_eq_true_eq] at hw
        have hwn : w - n < acc.length := by omega
        have hwn' : w - n < acc'.length := by omega
        rw [foldl_orSets_getD_lt n gs acc' (w - n) hwn']
        simp only [acc', orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hwn]
      · rfl
      · rfl
      · rfl
    | succ j' =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      set acc' := orStep n acc g
      have hlen' : acc'.length = acc.length + 1 := by
        simp only [acc', orStep, List.length_append, List.length_singleton]
      have hj' : j' < gs.length := by simp only [List.length_cons] at hj; omega
      have hidx : acc.length + (j' + 1) = acc'.length + j' := by omega
      rw [hidx]
      exact ih acc' j' hj'

lemma orReaches_lt_len {n : ℕ} {C : Circuit} {w g : ℕ} (h : OrReaches n C w g) :
    w - n < C.gates.length := by
  by_contra hge
  unfold OrReaches at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [orSets_length]; omega)] at h
  simp at h

lemma orReaches_gate_iff {n : ℕ} {C : Circuit} {j g : ℕ} (hj : j < C.gates.length) :
    OrReaches n C (n + j) g ↔
      g = j ∨ ((gateAt C j).op = GateOp.or ∧
        ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ OrReaches n C w g) := by
  unfold OrReaches orSets
  have h := foldl_orSets_getD_gate n C.gates [] j hj
  simp only [List.length_nil, Nat.zero_add] at h
  rw [Nat.add_sub_cancel_left, h, ← gateAt_eq hj]
  constructor
  · rintro ⟨_, hmem⟩
    rw [List.mem_cons] at hmem
    rcases hmem with rfl | hmem
    · exact Or.inl rfl
    · cases hop : (gateAt C j).op
      · rw [hop] at hmem; simp at hmem
      · rw [hop] at hmem
        rw [List.mem_flatMap] at hmem
        rcases hmem with ⟨w, hw, hwg⟩
        rw [List.mem_filter] at hw
        simp only [decide_eq_true_eq] at hw
        exact Or.inr ⟨rfl, w, hw.1, hw.2.1, hw.2.2, ⟨hw.2.1, hwg⟩⟩
      · rw [hop] at hmem; simp at hmem
      · rw [hop] at hmem; simp at hmem
      · rw [hop] at hmem; simp at hmem
  · rintro (rfl | ⟨hop, w, hw, hnw, hwnj, hwg⟩)
    · exact ⟨Nat.le_add_right n _, List.mem_cons_self⟩
    · refine ⟨Nat.le_add_right n j, List.mem_cons_of_mem j ?_⟩
      rw [hop, List.mem_flatMap]
      exact ⟨w, List.mem_filter.mpr ⟨hw, by simp [hnw, hwnj]⟩, hwg.2⟩

lemma orReaches_input_false {n : ℕ} {C : Circuit} {w g : ℕ} (hw : w < n) : ¬ OrReaches n C w g :=
  fun h => by have := h.1; omega

lemma orReaches_le {n : ℕ} {C : Circuit} {w g : ℕ} (h : OrReaches n C w g) : g ≤ w - n := by
  have hnw : n ≤ w := h.1
  have hj : w - n < C.gates.length := orReaches_lt_len h
  obtain ⟨k, hk⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  subst hk
  rw [Nat.add_sub_cancel_left] at hj ⊢
  clear hnw
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [orReaches_gate_iff hj] at h
    rcases h with rfl | ⟨_, u, _, hnu, hunk, hug⟩
    · exact le_refl _
    · have hlt : u - n < k := by omega
      have hu_eq : u = n + (u - n) := by omega
      rw [hu_eq] at hug
      have := ih (u - n) hlt hug (by omega)
      omega

lemma orReaches_self {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    OrReaches n C (n + j) j :=
  (orReaches_gate_iff hj).mpr (Or.inl rfl)

lemma orReaches_trans {n : ℕ} {C : Circuit} {w j g : ℕ}
    (h1 : OrReaches n C w j) (h2 : OrReaches n C (n + j) g) : OrReaches n C w g := by
  have hnw : n ≤ w := h1.1
  have hwn : w - n < C.gates.length := orReaches_lt_len h1
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  rw [Nat.add_sub_cancel_left] at hwn
  clear hnw
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [orReaches_gate_iff hwn] at h1
    rcases h1 with rfl | ⟨hop, u, hu, hnu, hunk, huj⟩
    · exact h2
    · rw [orReaches_gate_iff hwn]
      refine Or.inr ⟨hop, u, hu, hnu, hunk, ?_⟩
      have hu_eq : u = n + (u - n) := by omega
      rw [hu_eq] at huj ⊢
      exact ih (u - n) (by omega) huj (by omega)

lemma orReaches_inCone_or_eq {n : ℕ} {C : Circuit} {j g : ℕ} (h : OrReaches n C (n + j) g) :
    g = j ∨ InCone n C g j := by
  have hj := orReaches_lt_len h
  rw [Nat.add_sub_cancel_left] at hj
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [orReaches_gate_iff hj] at h
    rcases h with rfl | ⟨_, u, hu, hnu, hunj, hug⟩
    · exact Or.inl rfl
    · right
      rw [inCone_iff hj]
      refine ⟨u, hu, hnu, hunj, ?_⟩
      have hu_eq : u = n + (u - n) := by omega
      rw [hu_eq] at hug
      exact ih (u - n) (by omega) hug (by omega)

lemma orReaches_val_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {w g : ℕ} (h : OrReaches n C w g) (hg : gateVal n C g x = true) : wval C x w = true := by
  have hnw : n ≤ w := h.1
  have hwn : w - n < C.gates.length := orReaches_lt_len h
  obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
  rw [Nat.add_sub_cancel_left] at hwn
  clear hnw
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [orReaches_gate_iff hwn] at h
    rcases h with rfl | ⟨hop, u, hu, hnu, hunk, hug⟩
    · exact hg
    · rw [wval_gate_or hAO x hwn hop, Bool.or_eq_true]
      rw [gate_inputs_eq hAO hwn] at hu
      have hu_eq : u = n + (u - n) := by omega
      rw [hu_eq] at hug
      have hvu := ih (u - n) (by omega) hug (by omega)
      rw [← hu_eq] at hvu
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
      rcases hu with rfl | rfl
      · exact Or.inl hvu
      · exact Or.inr hvu

lemma mem_orIn_input {n : ℕ} (C : Circuit) (u v : Fin n) :
    u ∈ orIn n C v.val ↔ u = v := by
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (heq | ⟨k, _, hreach, _, _⟩)
    · exact Fin.ext heq
    · exact absurd hreach (orReaches_input_false v.isLt)
  · rintro rfl; exact Or.inl rfl

lemma orIn_and_eq_empty {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) : orIn n C (n + j) = ∅ := by
  ext u
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_or]
  refine ⟨by have := u.isLt; omega, ?_⟩
  rintro ⟨k, hk, hreach, hor, _⟩
  rw [orReaches_gate_iff hj] at hreach
  rcases hreach with rfl | ⟨hor', _⟩
  · rw [hand] at hor; cases hor
  · rw [hand] at hor'; cases hor'

lemma orIn_or_eq_union {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hor : (gateAt C j).op = GateOp.or) :
    orIn n C (n + j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1) := by
  ext u
  simp only [Finset.mem_union, orIn, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (hu | ⟨k, hk, hreach, hork, huk⟩)
    · omega
    · rw [orReaches_gate_iff hj] at hreach
      rcases hreach with rfl | ⟨_, w, hw, hnw, hwnj, hwk⟩
      · rw [gate_inputs_eq hAO hj] at huk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at huk
        rcases huk with h0 | h1
        · exact Or.inl (Or.inl h0)
        · exact Or.inr (Or.inl h1)
      · rw [gate_inputs_eq hAO hj] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl
        · exact Or.inl (Or.inr ⟨k, hk, hwk, hork, huk⟩)
        · exact Or.inr (Or.inr ⟨k, hk, hwk, hork, huk⟩)
  · rintro ((h0 | ⟨k, hk, hwk, hork, huk⟩) | (h1 | ⟨k, hk, hwk, hork, huk⟩))
    · right
      refine ⟨j, hj, orReaches_self hj, hor, ?_⟩
      rw [gate_inputs_eq hAO hj, h0]; simp
    · right
      refine ⟨k, hk, (orReaches_gate_iff hj).mpr (Or.inr ⟨hor, opnd C j 0, opnd_mem hAO hj 0, hwk.1,
        opnd_lt hAO hj 0, hwk⟩), hork, huk⟩
    · right
      refine ⟨j, hj, orReaches_self hj, hor, ?_⟩
      rw [gate_inputs_eq hAO hj, h1]; simp
    · right
      refine ⟨k, hk, (orReaches_gate_iff hj).mpr (Or.inr ⟨hor, opnd C j 1, opnd_mem hAO hj 1, hwk.1,
        opnd_lt hAO hj 1, hwk⟩), hork, huk⟩

lemma orIn_val_mono {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {w : ℕ} {u : Fin n} (hu : u ∈ orIn n C w) (hx : x u = true) : wval C x w = true := by
  unfold orIn at hu
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hu
  rcases hu with rfl | ⟨k, hk, hreach, hork, huk⟩
  · rw [wval_input C x u.val u.isLt]; exact hx
  · apply orReaches_val_mono hAO x hreach
    rw [gateVal_eq_wval, wval_gate_or hAO x hk hork, Bool.or_eq_true]
    rw [gate_inputs_eq hAO hk] at huk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at huk
    rcases huk with h0 | h1
    · left; rw [← h0, wval_input C x u.val u.isLt]; exact hx
    · right; rw [← h1, wval_input C x u.val u.isLt]; exact hx


lemma least_gate_reaches_output {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hne : ∃ a b : Fin n, G.Adj a b)
    {j : ℕ} (hj : j < C.gates.length) :
    C.output = n + j ∨ InCone n C j (C.output - n) := by
  have hmain : ∀ m : ℕ, ∀ k < C.gates.length, C.gates.length - k = m →
      C.output = n + k ∨ InCone n C k (C.output - n) := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro k hk hkm
      by_cases hout : C.output = n + k
      · exact Or.inl hout
      obtain ⟨l, hl, hkl⟩ := least_gate_has_reader hL hne hk hout
      have hlt : k < l := by have := hL.1.2.1 l hl (n + k) hkl; omega
      have hcone : InCone n C k l := by
        apply (inCone_iff hl).mpr
        exact ⟨n + k, hkl, by omega, by omega, Or.inl (by omega)⟩
      have hnext := ih (C.gates.length - l) (by omega) l hl rfl
      right
      rcases hnext with houtl | hsub
      · simpa only [houtl, Nat.add_sub_cancel_left] using hcone
      · exact inCone_trans hcone hsub
  exact hmain _ j hj rfl

lemma rewireAnd_propagates_clean_top {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hL : IsLeastAO G C) (hTF : TopForm G C)
    (hne : ∃ a b : Fin n, G.Adj a b) {j u v a : ℕ}
    (hj : j < C.gates.length) (hu : u < n + j) (hv : v < n + j)
    (hjand : (gateAt C j).op = .and) (ha : a < C.gates.length)
    (haand : (gateAt C a).op = .and) (haclean : BelowF G C a)
    (x : Fin n → Bool) (hax : gateVal n (rewireAnd C j u v) a x = true) :
    circuitFun n (rewireAnd C j u v) x = true := by
  have hAO' := rewireAnd_isAO2 hL.1 hj hu hv
  have hprop : ∀ k, InCone n C a k → gateVal n (rewireAnd C j u v) k x = true := by
    intro k
    induction k using Nat.strong_induction_on with
    | ind k ih =>
      intro hak
      have hk := inCone_lt_len hak
      have hor : (gateAt C k).op = .or := by
        rcases hL.1.1 _ (gateAt_mem hk) with hand | hor
        · exact False.elim (hTF a ha k hk haand haclean hand hak)
        · exact hor
      have hkj : k ≠ j := by intro heq; rw [heq, hjand] at hor; cases hor
      have hg : gateAt (rewireAnd C j u v) k = gateAt C k := by
        rw [rewireAnd_gateAt hj, if_neg hkj]
      have hk' : k < (rewireAnd C j u v).gates.length := by
        simpa only [rewireAnd_length] using hk
      obtain ⟨w, hw, hnw, hwb, hrel⟩ := (inCone_iff hk).mp hak
      have hwtrue : wval (rewireAnd C j u v) x w = true := by
        have hw_eq : n + (w - n) = w := by omega
        rcases hrel with heq | hsub
        · rw [← hw_eq, ← gateVal_eq_wval, ← heq]
          exact hax
        · have ht := ih (w - n) (by omega) hsub
          simpa only [gateVal_eq_wval, hw_eq] using ht
      rw [gateVal_eq_wval, wval_gate_or hAO' x hk' (by simpa only [hg] using hor),
        Bool.or_eq_true]
      have hopnd (b : Fin 2) : opnd (rewireAnd C j u v) k b = opnd C k b := by
        simp only [opnd, hg]
      rw [hopnd 0, hopnd 1]
      rw [gate_inputs_eq hL.1 hk] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact Or.inl hwtrue
      · exact Or.inr hwtrue
  rcases least_gate_reaches_output hL hne ha with hout | hcone
  · change wval (rewireAnd C j u v) x C.output = true
    rw [hout]
    exact hax
  · change wval (rewireAnd C j u v) x C.output = true
    have hout := (output_bounds hL hne).1
    have htrue := hprop (C.output - n) hcone
    simpa only [gateVal_eq_wval, Nat.add_sub_of_le hout] using htrue

lemma rewireAnd_orReaches {n : ℕ} {C : Circuit} {j u v : ℕ}
    (hj : j < C.gates.length) (hjand : (gateAt C j).op = .and) :
    ∀ w k, OrReaches n C w k → OrReaches n (rewireAnd C j u v) w k := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro k hwk
    have hnw := hwk.1
    have hwlen := orReaches_lt_len hwk
    have hr : w - n < C.gates.length := hwlen
    have hr' : w - n < (rewireAnd C j u v).gates.length := by
      simpa only [rewireAnd_length] using hr
    have hweq : w = n + (w - n) := by omega
    rw [hweq, orReaches_gate_iff hr] at hwk
    rw [hweq, orReaches_gate_iff hr']
    rcases hwk with hself | ⟨hor, z, hz, hnz, hzb, hzk⟩
    · exact Or.inl hself
    · have hrj : w - n ≠ j := by intro heq; rw [heq, hjand] at hor; cases hor
      have hg : gateAt (rewireAnd C j u v) (w - n) = gateAt C (w - n) := by
        rw [rewireAnd_gateAt hj, if_neg hrj]
      exact Or.inr ⟨by simpa only [hg] using hor, z, by simpa only [hg] using hz,
        hnz, hzb, ih z (by omega) k hzk⟩

lemma rewireAnd_orIn_subset {n : ℕ} {C : Circuit} {j u v : ℕ}
    (hj : j < C.gates.length) (hjand : (gateAt C j).op = .and) (w : ℕ) :
    orIn n C w ⊆ orIn n (rewireAnd C j u v) w := by
  intro t ht
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at ht ⊢
  rcases ht with heq | ⟨k, hk, hreach, hor, ht⟩
  · exact Or.inl heq
  · have hkj : k ≠ j := by intro heq; rw [heq, hjand] at hor; cases hor
    have hg : gateAt (rewireAnd C j u v) k = gateAt C k := by
      rw [rewireAnd_gateAt hj, if_neg hkj]
    exact Or.inr ⟨k, by simpa only [rewireAnd_length] using hk,
      rewireAnd_orReaches hj hjand w k hreach, by simpa only [hg] using hor,
      by simpa only [hg] using ht⟩



lemma rewireAnd_starEdges_survive {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hTF : TopForm G C)
    {j u v : ℕ} (hjunk : j ∈ junk G C) (hu : u < n + j) (hv : v < n + j)
    {p q : Fin n} (hpq : G.Adj p q) (hstar : s(p, q) ∈ starEdges G C) :
    circuitFun n (rewireAnd C j u v) (pairInput p q) = true := by
  obtain ⟨hjand, hj, xbad, hjbad, hFbad⟩ := (Finset.mem_filter.mp hjunk).2
  have hAO' := rewireAnd_isAO2 hL.1 hj hu hv
  obtain ⟨a, ha, hpairs⟩ := Finset.mem_biUnion.mp hstar
  obtain ⟨⟨r, t⟩, hrt, heq⟩ := Finset.mem_image.mp hpairs
  obtain ⟨hr, ht⟩ := Finset.mem_product.mp hrt
  have hrttrue : pairInput p q r = true ∧ pairInput p q t = true := by
    have he : r = p ∧ t = q ∨ r = q ∧ t = p := Sym2.eq_iff.mp heq
    rcases he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp [pairInput]
  have htop : a < C.gates.length ∧ (gateAt C a).op = .and ∧ BelowF G C a := by
    simpa only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] using ha
  obtain ⟨halen, haand, haclean⟩ := htop
  have haj : a ≠ j := by
    intro heq
    subst a
    exact Bool.noConfusion ((haclean xbad hjbad).symm.trans hFbad)
  have hg : gateAt (rewireAnd C j u v) a = gateAt C a := by
    rw [rewireAnd_gateAt hj, if_neg haj]
  have ho (b : Fin 2) : opnd (rewireAnd C j u v) a b = opnd C a b := by
    simp only [opnd, hg]
  have hax : gateVal n (rewireAnd C j u v) a (pairInput p q) = true := by
    have ha' : a < (rewireAnd C j u v).gates.length := by
      simpa only [rewireAnd_length] using halen
    rw [gateVal_eq_wval, wval_gate_and hAO' (pairInput p q) ha'
      (by simpa only [hg] using haand), ho 0, ho 1, Bool.and_eq_true]
    exact ⟨orIn_val_mono hAO' _ (rewireAnd_orIn_subset hj hjand _ hr) hrttrue.1,
      orIn_val_mono hAO' _ (rewireAnd_orIn_subset hj hjand _ ht) hrttrue.2⟩
  exact rewireAnd_propagates_clean_top hL hTF ⟨p, q, hpq⟩ hj hu hv hjand halen haand
    haclean (pairInput p q) hax

lemma rewireAnd_Ustar_least {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hTF : TopForm G C) {j u v : ℕ}
    (hjunk : j ∈ junk G C) (hu : u < n + j) (hv : v < n + j)
    (hval : ∀ x : Fin n → Bool,
      (wval C x u && wval C x v) = true → gateVal n C j x = true)
    (hedge : ∀ a b : Fin n, s(a, b) ∈ Ustar G C →
      (wval C (pairInput a b) u && wval C (pairInput a b) v) =
        gateVal n C j (pairInput a b)) :
    IsLeastAO G (rewireAnd C j u v) := by
  have hj := (Finset.mem_filter.mp hjunk).2.2.1
  have hAO' := rewireAnd_isAO2 hL.1 hj hu hv
  refine ⟨hAO', ?_, ?_⟩
  · funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      have hv := rewireAnd_values_le hL.1 hj hu hv hval x C.output hx
      exact (congrFun hL.2.1 x).symm.trans hv
    · intro hx
      obtain ⟨a, b, hab, ha, hb⟩ := (graphFun_iff x).mp hx
      have hp : wval (rewireAnd C j u v) (pairInput a b) C.output = true := by
        by_cases hs : s(a, b) ∈ starEdges G C
        · exact rewireAnd_starEdges_survive hL hTF hjunk hu hv hab hs
        · have hU : s(a, b) ∈ Ustar G C :=
            Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hab, hs⟩
          rw [rewireAnd_values_at hL.1 hj hu hv (pairInput a b) (hedge a b hU)]
          exact (congrFun hL.2.1 (pairInput a b)).trans ((graphFun_pair_iff a b).mpr hab)
      apply wval_mono hAO' (x := pairInput a b) (y := x) _ C.output hp
      intro p hp
      simp only [pairInput, decide_eq_true_eq] at hp
      rcases hp with rfl | rfl <;> assumption
  · intro D hD hDfun
    simpa only [Circuit.size, rewireAnd_length] using hL.2.2 D hD hDfun


lemma no_independent_Ustar_lowering {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hfirst : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    {C : Circuit} (hL : IsLeastAO G C) (hTF : TopForm G C) {g h u v : ℕ}
    (hjunk : junk G C = {g, h}) (hgh : g ≠ h) (hind : ¬ InCone n C g h)
    (hu : u < n + g) (hv : v < n + g)
    (hval : ∀ x : Fin n → Bool,
      (wval C x u && wval C x v) = true → gateVal n C g x = true)
    (hclean : ∀ x : Fin n → Bool,
      (wval C x u && wval C x v) = true → graphFun G ∅ x = true)
    (hedge : ∀ a b : Fin n, s(a, b) ∈ Ustar G C →
      (wval C (pairInput a b) u && wval C (pairInput a b) v) =
        gateVal n C g (pairInput a b)) : False := by
  have hgmem : g ∈ junk G C := by simp [hjunk]
  have hhmem : h ∈ junk G C := by simp [hjunk]
  obtain ⟨hgOp, hg, _⟩ := (Finset.mem_filter.mp hgmem).2
  obtain ⟨hhOp, hh, x, hx, hFx⟩ := (Finset.mem_filter.mp hhmem).2
  have hL' := rewireAnd_Ustar_least hL hTF hgmem hu hv hval hedge
  have hclean' := rewireAnd_clean hL.1 hg hu hv hval hclean
  have hsub : junk G (rewireAnd C g u v) ⊆ {h} := by
    have hs := rewireAnd_junk_subset hL.1 hg hu hv hgOp hval hclean'
    simpa [hjunk, hgh] using hs
  have hh' : h ∈ junk G (rewireAnd C g u v) := by
    have hlen : h < (rewireAnd C g u v).gates.length := by
      simpa only [rewireAnd_length] using hh
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hlen, ?_, hlen, x, ?_, hFx⟩
    · simpa [rewireAnd_gateAt hg, Ne.symm hgh] using hhOp
    · rw [gateVal_eq_wval,
        rewireAnd_outside_cone hL.1 hg hu hv x (n + h) (by omega) (by omega)]
      · exact hx
      · intro _
        simpa only [Nat.add_sub_cancel_left] using hind
  have heq : junk G (rewireAnd C g u v) = {h} :=
    Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hh')
  apply hfirst (rewireAnd C g u v) hL'
  rw [heq]
  simp



lemma no_independent_Ustar_star {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hfirst : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    {C : Circuit} (hL : IsLeastAO G C) (hTF : TopForm G C) {g h v : ℕ}
    (hjunk : junk G C = {g, h}) (hgh : g ≠ h) (hind : ¬ InCone n C g h)
    (P Q : Finset (Fin n)) (z : Fin n) (hz : z ∈ P)
    (hv : v < n + g) (hvsem : ∀ x : Fin n → Bool,
      wval C x v = decide (∃ q ∈ Q, x q = true))
    (hgsem : ∀ x : Fin n → Bool, gateVal n C g x =
      (decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)))
    (hQ : ∀ q ∈ Q, G.Adj z q)
    (hcover : ∀ a b, s(a, b) ∈ Ustar G C →
      gateVal n C g (pairInput a b) = true → a = z ∨ b = z) : False := by
  apply no_independent_Ustar_lowering hfirst hL hTF hjunk hgh hind
    (u := z.val) (v := v) (by have := z.isLt; omega) hv
  · intro x hx
    rw [wval_input C x z.val z.isLt, hvsem] at hx
    rw [hgsem]
    exact star_below_product P Q z hz x hx
  · intro x hx
    rw [wval_input C x z.val z.isLt, hvsem] at hx
    exact star_below_graph G Q z hQ x hx
  · intro a b hU
    rw [wval_input C (pairInput a b) z.val z.isLt, hvsem]
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      rw [hgsem]
      exact star_below_product P Q z hz (pairInput a b) hx
    · intro hg
      have hc := hcover a b hU hg
      rw [hgsem, Bool.and_eq_true] at hg
      rw [Bool.and_eq_true]
      refine ⟨?_, hg.2⟩
      rcases hc with rfl | rfl <;> simp [pairInput]


lemma rewireAnd_values_le_at {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j u v : ℕ} (hj : j < C.gates.length) (hu : u < n + j) (hv : v < n + j)
    (x : Fin n → Bool)
    (hval : (wval C x u && wval C x v) = true → gateVal n C j x = true) :
    ∀ (w : ℕ),
      wval (rewireAnd C j u v) x w = true → wval C x w = true := by
  have hAO' := rewireAnd_isAO2 hAO hj hu hv
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro htrue
    by_cases hwn : w < n
    · rw [wval_input _ x w hwn] at htrue ⊢
      exact htrue
    by_cases hwlen : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hk' : k < (rewireAnd C j u v).gates.length := by
        simpa only [rewireAnd_length] using hk
      by_cases hkj : k = j
      · subst k
        have hop : (gateAt (rewireAnd C j u v) j).op = .and := by
          rw [rewireAnd_gateAt hj]
          simp
        rw [wval_gate_and hAO' x hk' hop] at htrue
        simp [opnd, rewireAnd_gateAt hj] at htrue
        apply hval
        rw [Bool.and_eq_true]
        exact ⟨ih _ hu htrue.1, ih _ hv htrue.2⟩
      · have hg : gateAt (rewireAnd C j u v) k = gateAt C k := by
          rw [rewireAnd_gateAt hj, if_neg hkj]
        have ho (b : Fin 2) : opnd (rewireAnd C j u v) k b = opnd C k b := by
          simp only [opnd, hg]
        have h0 := opnd_lt hAO hk 0
        have h1 := opnd_lt hAO hk 1
        rcases hAO.1 _ (gateAt_mem hk) with hand | hor
        · rw [wval_gate_and hAO' x hk' (by simpa only [hg] using hand),
            ho 0, ho 1, Bool.and_eq_true] at htrue
          rw [wval_gate_and hAO x hk hand, Bool.and_eq_true]
          exact ⟨ih _ h0 htrue.1, ih _ h1 htrue.2⟩
        · rw [wval_gate_or hAO' x hk' (by simpa only [hg] using hor),
            ho 0, ho 1, Bool.or_eq_true] at htrue
          rw [wval_gate_or hAO x hk hor, Bool.or_eq_true]
          exact htrue.imp (ih _ h0) (ih _ h1)
    · rw [wval_ge_len (rewireAnd C j u v) x (by rw [rewireAnd_length]; omega)] at htrue
      cases htrue



lemma rewireAnd_values_ge_at {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j u v : ℕ} (hj : j < C.gates.length) (hu : u < n + j) (hv : v < n + j)
    (x : Fin n → Bool)
    (hval : gateVal n C j x = true → (wval C x u && wval C x v) = true) :
    ∀ w : ℕ, wval C x w = true → wval (rewireAnd C j u v) x w = true := by
  have hAO' := rewireAnd_isAO2 hAO hj hu hv
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro htrue
    by_cases hwn : w < n
    · rw [wval_input _ x w hwn] at htrue ⊢
      exact htrue
    by_cases hwlen : w < n + C.gates.length
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      have hk : k < C.gates.length := by omega
      have hk' : k < (rewireAnd C j u v).gates.length := by
        simpa only [rewireAnd_length] using hk
      by_cases hkj : k = j
      · subst k
        have hvtrue : wval C x u = true ∧ wval C x v = true := by
          simpa only [Bool.and_eq_true] using hval htrue
        have hop : (gateAt (rewireAnd C j u v) j).op = .and := by
          rw [rewireAnd_gateAt hj]
          simp
        rw [wval_gate_and hAO' x hk' hop]
        simp only [opnd, rewireAnd_gateAt hj, ite_self]
        simp only [List.getD_cons_zero, Fin.val_zero, Fin.val_one, List.getD_cons_succ,
          Bool.and_eq_true]
        exact ⟨ih _ hu hvtrue.1, ih _ hv hvtrue.2⟩
      · have hg : gateAt (rewireAnd C j u v) k = gateAt C k := by
          rw [rewireAnd_gateAt hj, if_neg hkj]
        have ho (b : Fin 2) : opnd (rewireAnd C j u v) k b = opnd C k b := by
          simp only [opnd, hg]
        have h0 := opnd_lt hAO hk 0
        have h1 := opnd_lt hAO hk 1
        rcases hAO.1 _ (gateAt_mem hk) with hand | hor
        · rw [wval_gate_and hAO x hk hand, Bool.and_eq_true] at htrue
          rw [wval_gate_and hAO' x hk' (by simpa only [hg] using hand), ho 0, ho 1,
            Bool.and_eq_true]
          exact ⟨ih _ h0 htrue.1, ih _ h1 htrue.2⟩
        · rw [wval_gate_or hAO x hk hor, Bool.or_eq_true] at htrue
          rw [wval_gate_or hAO' x hk' (by simpa only [hg] using hor), ho 0, ho 1,
            Bool.or_eq_true]
          exact htrue.imp (ih _ h0) (ih _ h1)
    · rw [wval_ge_len C x (by omega)] at htrue
      cases htrue

lemma rewireAnd_prefix {n : ℕ} {C : Circuit} (hAO : IsAO2 n C)
    {j u v : ℕ} (hj : j < C.gates.length) (hu : u < n + j) (hv : v < n + j)
    (x : Fin n → Bool) {w : ℕ} (hw : w < n + j) :
    wval (rewireAnd C j u v) x w = wval C x w := by
  apply rewireAnd_outside_cone hAO hj hu hv x w (by omega) (by omega)
  intro hnw hc
  have := inCone_lt hc
  omega

lemma rewireAnd_clean_without_lowering {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hAO : IsAO2 n C) {j u v : ℕ}
    (hj : j < C.gates.length) (hu : u < n + j) (hv : v < n + j)
    (hclean : ∀ x : Fin n → Bool,
      (wval C x u && wval C x v) = true → graphFun G ∅ x = true) :
    BelowF G (rewireAnd C j u v) j := by
  have hAO' := rewireAnd_isAO2 hAO hj hu hv
  intro x hx
  have hj' : j < (rewireAnd C j u v).gates.length := by
    simpa only [rewireAnd_length] using hj
  have hop : (gateAt (rewireAnd C j u v) j).op = .and := by
    rw [rewireAnd_gateAt hj]
    simp
  rw [gateVal_eq_wval, wval_gate_and hAO' x hj' hop] at hx
  simp [opnd, rewireAnd_gateAt hj] at hx
  apply hclean x
  rw [Bool.and_eq_true]
  exact ⟨(rewireAnd_prefix hAO hj hu hv x hu).symm.trans hx.1,
    (rewireAnd_prefix hAO hj hu hv x hv).symm.trans hx.2⟩

lemma clean_rewire_Ustar_least {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hL : IsLeastAO G C) (hTF : TopForm G C) {j u v : ℕ}
    (hjunk : j ∈ junk G C) (hu : u < n + j) (hv : v < n + j)
    (hclean : ∀ x : Fin n → Bool,
      (wval C x u && wval C x v) = true → graphFun G ∅ x = true)
    (hedge : ∀ a b : Fin n, s(a, b) ∈ Ustar G C → gateVal n C j (pairInput a b) = true →
      (wval C (pairInput a b) u && wval C (pairInput a b) v) = true) :
    IsLeastAO G (rewireAnd C j u v) := by
  have hj := (Finset.mem_filter.mp hjunk).2.2.1
  have hAO' := rewireAnd_isAO2 hL.1 hj hu hv
  refine ⟨hAO', ?_, ?_⟩
  · funext x
    apply Bool.eq_iff_iff.mpr
    constructor
    · intro hx
      by_contra hnot
      have hFx : graphFun G ∅ x = false := by cases he : graphFun G ∅ x <;> simp_all
      have hdown : (wval C x u && wval C x v) = true → gateVal n C j x = true := by
        intro hnew
        have := hclean x hnew
        rw [hFx] at this
        cases this
      have hold := rewireAnd_values_le_at hL.1 hj hu hv x hdown C.output hx
      have hOldF := (congrFun hL.2.1 x).symm.trans hold
      rw [hFx] at hOldF
      cases hOldF
    · intro hx
      obtain ⟨a, b, hab, ha, hb⟩ := (graphFun_iff x).mp hx
      have hp : wval (rewireAnd C j u v) (pairInput a b) C.output = true := by
        by_cases hs : s(a, b) ∈ starEdges G C
        · exact rewireAnd_starEdges_survive hL hTF hjunk hu hv hab hs
        · have hU : s(a, b) ∈ Ustar G C :=
            Finset.mem_sdiff.mpr ⟨SimpleGraph.mem_edgeFinset.mpr hab, hs⟩
          apply rewireAnd_values_ge_at hL.1 hj hu hv (pairInput a b) (hedge a b hU)
          exact (congrFun hL.2.1 (pairInput a b)).trans ((graphFun_pair_iff a b).mpr hab)
      apply wval_mono hAO' (x := pairInput a b) (y := x) _ C.output hp
      intro p hp
      simp only [pairInput, decide_eq_true_eq] at hp
      rcases hp with rfl | rfl <;> assumption
  · intro D hD hDfun
    simpa only [Circuit.size, rewireAnd_length] using hL.2.2 D hD hDfun



lemma clean_rewire_junk_subset {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (hAO : IsAO2 n C) {j u v : ℕ}
    (hj : j < C.gates.length) (hu : u < n + j) (hv : v < n + j)
    (hclean : ∀ x : Fin n → Bool,
      (wval C x u && wval C x v) = true → graphFun G ∅ x = true) :
    junk G (rewireAnd C j u v) ⊆ (junk G C).erase j := by
  have hclean' := rewireAnd_clean_without_lowering hAO hj hu hv hclean
  intro k hk
  have hmem := Finset.mem_filter.mp hk
  have hlen : k < C.gates.length := by
    simpa only [Finset.mem_range, rewireAnd_length] using hmem.1
  obtain ⟨hop, _, x, hx, hFx⟩ := hmem.2
  have hkj : k ≠ j := by
    intro hkj
    subst k
    exact Bool.noConfusion ((hclean' x hx).symm.trans hFx)
  apply Finset.mem_erase.mpr
  refine ⟨hkj, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hlen, ?_⟩⟩
  refine ⟨?_, hlen, x, ?_, hFx⟩
  · simpa [rewireAnd_gateAt hj, hkj] using hop
  · apply rewireAnd_values_le_at hAO hj hu hv x _ (n + k) hx
    intro hnew
    have hF := hclean x hnew
    rw [hFx] at hF
    cases hF

lemma no_independent_clean_rewrite {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    (hfirst : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    {C : Circuit} (hL : IsLeastAO G C) (hTF : TopForm G C) {g h u v : ℕ}
    (hjunk : junk G C = {g, h}) (hgh : g ≠ h) (hind : ¬ InCone n C g h)
    (hu : u < n + g) (hv : v < n + g)
    (hclean : ∀ x : Fin n → Bool,
      (wval C x u && wval C x v) = true → graphFun G ∅ x = true)
    (hedge : ∀ a b : Fin n, s(a, b) ∈ Ustar G C → gateVal n C g (pairInput a b) = true →
      (wval C (pairInput a b) u && wval C (pairInput a b) v) = true) : False := by
  have hgmem : g ∈ junk G C := by simp [hjunk]
  have hhmem : h ∈ junk G C := by simp [hjunk]
  obtain ⟨_, hg, _⟩ := (Finset.mem_filter.mp hgmem).2
  obtain ⟨hhOp, hh, x, hx, hFx⟩ := (Finset.mem_filter.mp hhmem).2
  have hL' := clean_rewire_Ustar_least hL hTF hgmem hu hv hclean hedge
  have hsub : junk G (rewireAnd C g u v) ⊆ {h} := by
    have hs := clean_rewire_junk_subset hL.1 hg hu hv hclean
    simpa [hjunk, hgh] using hs
  have hh' : h ∈ junk G (rewireAnd C g u v) := by
    have hlen : h < (rewireAnd C g u v).gates.length := by
      simpa only [rewireAnd_length] using hh
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hlen, ?_, hlen, x, ?_, hFx⟩
    · simpa [rewireAnd_gateAt hg, Ne.symm hgh] using hhOp
    · rw [gateVal_eq_wval,
        rewireAnd_outside_cone hL.1 hg hu hv x (n + h) (by omega) (by omega)]
      · exact hx
      · intro _
        simpa only [Nat.add_sub_cancel_left] using hind
  have heq : junk G (rewireAnd C g u v) = {h} :=
    Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hh')
  apply hfirst (rewireAnd C g u v) hL'
  rw [heq]
  simp

lemma no_nested_filter_with_clean_center {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj]
    (hfirst : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    {C : Circuit} (hL : IsLeastAO G C) (hTF : TopForm G C) {g h : ℕ}
    (hjunk : junk G C = {g, h}) (hgh : g < h)
    (hbelow : ∀ x : Fin n → Bool, gateVal n C h x = true → gateVal n C g x = true)
    (w : Fin n) (hw : w ∈ wmax G C g)
    (hcover : ∀ a b : Fin n, s(a, b) ∈ Ustar G C →
      gateVal n C h (pairInput a b) = true → a = w ∨ b = w) : False := by
  have hswap : junk G C = {h, g} := hjunk.trans (Finset.pair_comm _ _)
  apply no_independent_clean_rewrite hfirst hL hTF hswap (by omega)
    (by intro hc; have := inCone_lt hc; omega)
    (u := n + g) (v := w.val) (by omega) (by have := w.isLt; omega)
  · intro x hx
    rw [wval_input C x w.val w.isLt, Bool.and_eq_true] at hx
    exact (Finset.mem_filter.mp hw).2 x hx.1 hx.2
  · intro a b hU hhval
    rw [wval_input C (pairInput a b) w.val w.isLt, Bool.and_eq_true]
    refine ⟨hbelow (pairInput a b) hhval, ?_⟩
    rcases hcover a b hU hhval with rfl | rfl <;> simp [pairInput]



lemma nested_flag_filter_edge_center {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (g h : ℕ)
    (P Q S : Finset (Fin n)) (z zp : Fin n)
    (hPQ : Disjoint P Q) (hSQ : Disjoint S Q) (hzS : z ∉ S)
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q → p = z ∨ q = zp)
    (hgsem : ∀ x : Fin n → Bool, gateVal n C g x =
      (decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)))
    (hhsem : ∀ x : Fin n → Bool, gateVal n C h x =
      (gateVal n C g x && decide (∃ r ∈ S, x r = true)))
    (a b : Fin n) (hab : G.Adj a b) (hh : gateVal n C h (pairInput a b) = true) :
    a = zp ∨ b = zp := by
  rw [hhsem, Bool.and_eq_true] at hh
  rw [hgsem, Bool.and_eq_true] at hh
  obtain ⟨p, hpP, hpv⟩ := of_decide_eq_true hh.1.1
  obtain ⟨q, hqQ, hqv⟩ := of_decide_eq_true hh.1.2
  obtain ⟨r, hrS, hrv⟩ := of_decide_eq_true hh.2
  simp only [pairInput, decide_eq_true_eq] at hpv hqv hrv
  rcases hqv with hqa | hqb
  · subst q
    have hra : r ≠ a := by
      intro heq
      subst r
      exact (Finset.disjoint_left.mp hSQ) hrS hqQ
    have hpa : p ≠ a := by
      intro heq
      subst p
      exact (Finset.disjoint_left.mp hPQ) hpP hqQ
    have hrb : r = b := hrv.resolve_left hra
    have hpb : p = b := hpv.resolve_left hpa
    subst r
    subst p
    have hc := hcross b hpP a hqQ hab.symm
    exact Or.inl (hc.resolve_left (by intro heq; subst b; exact hzS hrS))
  · subst q
    have hrb : r ≠ b := by
      intro heq
      subst r
      exact (Finset.disjoint_left.mp hSQ) hrS hqQ
    have hpb : p ≠ b := by
      intro heq
      subst p
      exact (Finset.disjoint_left.mp hPQ) hpP hqQ
    have hra : r = a := hrv.resolve_right hrb
    have hpa : p = a := hpv.resolve_right hpb
    subst r
    subst p
    have hc := hcross a hpP b hqQ hab
    exact Or.inr (hc.resolve_left (by intro heq; subst a; exact hzS hrS))

lemma no_nested_flag_filter_avoiding_center {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj]
    (hfirst : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    {C : Circuit} (hL : IsLeastAO G C) (hTF : TopForm G C) {g h : ℕ}
    (hjunk : junk G C = {g, h}) (hgh : g < h)
    (P Q S : Finset (Fin n)) (z zp : Fin n)
    (hPQ : Disjoint P Q) (hSQ : Disjoint S Q) (hzS : z ∉ S)
    (hzp : zp ∈ wmax G C g)
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q → p = z ∨ q = zp)
    (hgsem : ∀ x : Fin n → Bool, gateVal n C g x =
      (decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)))
    (hhsem : ∀ x : Fin n → Bool, gateVal n C h x =
      (gateVal n C g x && decide (∃ r ∈ S, x r = true))) : False := by
  have hbelow : ∀ x : Fin n → Bool, gateVal n C h x = true → gateVal n C g x = true := by
    intro x hx
    rw [hhsem, Bool.and_eq_true] at hx
    exact hx.1
  apply no_nested_filter_with_clean_center hfirst hL hTF hjunk hgh hbelow zp hzp
  intro a b hU hh
  have hab := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hU).1
  exact nested_flag_filter_edge_center g h P Q S z zp hPQ hSQ hzS hcross hgsem hhsem
    a b hab hh



lemma cleaner_centers_cross_edges {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (h4 : NoFourCycle G) (g : ℕ) (P Q : Finset (Fin n)) (z zp : Fin n)
    (hzP : z ∈ P) (hzpQ : zp ∈ Q) (hz : z ∈ wmax G C g) (hzp : zp ∈ wmax G C g)
    (hgsem : ∀ x : Fin n → Bool, gateVal n C g x =
      (decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true))) :
    ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q → p = z ∨ q = zp := by
  have hP (p : Fin n) (hp : p ∈ P) : G.Adj p zp := by
    apply (graphFun_pair_iff p zp).mp
    apply (Finset.mem_filter.mp hzp).2 (pairInput p zp)
    · rw [hgsem, Bool.and_eq_true]
      exact ⟨decide_eq_true ⟨p, hp, by simp [pairInput]⟩,
        decide_eq_true ⟨zp, hzpQ, by simp [pairInput]⟩⟩
    · simp [pairInput]
  have hQ (q : Fin n) (hq : q ∈ Q) : G.Adj z q := by
    apply (graphFun_pair_iff z q).mp
    apply (Finset.mem_filter.mp hz).2 (pairInput z q)
    · rw [hgsem, Bool.and_eq_true]
      exact ⟨decide_eq_true ⟨z, hzP, by simp [pairInput]⟩,
        decide_eq_true ⟨q, hq, by simp [pairInput]⟩⟩
    · simp [pairInput]
  intro p hp q hq hpq
  by_cases hpz : p = z
  · exact Or.inl hpz
  · right
    apply Finset.card_le_one.mp (h4 p z hpz)
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hpq, hQ q hq⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hP p hp, hQ zp hzpQ⟩

lemma no_nested_flag_one_side_filter {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj]
    (hfirst : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    {C : Circuit} (hL : IsLeastAO G C) (hTF : TopForm G C) (h4 : NoFourCycle G)
    {g h : ℕ} (hjunk : junk G C = {g, h}) (hgh : g < h)
    (P Q S : Finset (Fin n)) (z zp : Fin n)
    (hPQ : Disjoint P Q) (hSQ : Disjoint S Q) (hzS : z ∉ S)
    (hzP : z ∈ P) (hzpQ : zp ∈ Q) (hz : z ∈ wmax G C g) (hzp : zp ∈ wmax G C g)
    (hgsem : ∀ x : Fin n → Bool, gateVal n C g x =
      (decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)))
    (hhsem : ∀ x : Fin n → Bool, gateVal n C h x =
      (gateVal n C g x && decide (∃ r ∈ S, x r = true))) : False := by
  exact no_nested_flag_filter_avoiding_center hfirst hL hTF hjunk hgh P Q S z zp hPQ hSQ hzS
    hzp (cleaner_centers_cross_edges h4 g P Q z zp hzP hzpQ hz hzp hgsem) hgsem hhsem



lemma pure_filter_cleaner_intersection {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (g h : ℕ) (S : Finset (Fin n))
    (hhsem : ∀ x : Fin n → Bool, gateVal n C h x =
      (gateVal n C g x && decide (∃ r ∈ S, x r = true))) :
    S ∩ wmax G C h = S ∩ wmax G C g := by
  ext w
  simp only [Finset.mem_inter]
  constructor
  · rintro ⟨hwS, hwh⟩
    refine ⟨hwS, Finset.mem_filter.mpr ⟨Finset.mem_univ w, ?_⟩⟩
    intro x hgx hwx
    apply (Finset.mem_filter.mp hwh).2 x _ hwx
    rw [hhsem, Bool.and_eq_true]
    exact ⟨hgx, decide_eq_true ⟨w, hwS, hwx⟩⟩
  · rintro ⟨hwS, hwg⟩
    refine ⟨hwS, Finset.mem_filter.mpr ⟨Finset.mem_univ w, ?_⟩⟩
    intro x hhx hwx
    rw [hhsem, Bool.and_eq_true] at hhx
    exact (Finset.mem_filter.mp hwg).2 x hhx.1 hwx

lemma flag_pair_has_center {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (g : ℕ) (P Q : Finset (Fin n)) (z zp : Fin n)
    (hPQ : Disjoint P Q)
    (hcross : ∀ p ∈ P, ∀ q ∈ Q, G.Adj p q → p = z ∨ q = zp)
    (hgsem : ∀ x : Fin n → Bool, gateVal n C g x =
      (decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)))
    (a b : Fin n) (hab : G.Adj a b) (hg : gateVal n C g (pairInput a b) = true) :
    (pairInput a b z || pairInput a b zp) = true := by
  rw [hgsem, Bool.and_eq_true] at hg
  obtain ⟨p, hpP, hpv⟩ := of_decide_eq_true hg.1
  obtain ⟨q, hqQ, hqv⟩ := of_decide_eq_true hg.2
  simp only [pairInput, decide_eq_true_eq] at hpv hqv
  have hpq : G.Adj p q := by
    rcases hpv with rfl | rfl <;> rcases hqv with rfl | rfl
    · exact False.elim ((Finset.disjoint_left.mp hPQ) hpP hqQ)
    · exact hab
    · exact hab.symm
    · exact False.elim ((Finset.disjoint_left.mp hPQ) hpP hqQ)
  rw [Bool.or_eq_true]
  rcases hcross p hpP q hqQ hpq with hpz | hqzp
  · left
    rw [← hpz]
    simpa only [pairInput, decide_eq_true_eq] using hpv
  · right
    rw [← hqzp]
    simpa only [pairInput, decide_eq_true_eq] using hqv

lemma no_nested_flag_center_wire {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj]
    (hfirst : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    {C : Circuit} (hL : IsLeastAO G C) (hTF : TopForm G C) (h4 : NoFourCycle G)
    {g h w : ℕ} (hjunk : junk G C = {g, h}) (hgh : g < h) (hw : w < n + h)
    (P Q : Finset (Fin n)) (z zp : Fin n)
    (hPQ : Disjoint P Q) (hzP : z ∈ P) (hzpQ : zp ∈ Q)
    (hz : z ∈ wmax G C g) (hzp : zp ∈ wmax G C g)
    (hgsem : ∀ x : Fin n → Bool, gateVal n C g x =
      (decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)))
    (hhbelow : ∀ x : Fin n → Bool, gateVal n C h x = true → gateVal n C g x = true)
    (hwsem : ∀ x : Fin n → Bool, wval C x w = (x z || x zp)) : False := by
  have hswap : junk G C = {h, g} := hjunk.trans (Finset.pair_comm _ _)
  have hcross := cleaner_centers_cross_edges h4 g P Q z zp hzP hzpQ hz hzp hgsem
  apply no_independent_clean_rewrite hfirst hL hTF hswap (by omega)
    (by intro hc; have := inCone_lt hc; omega) (u := n + g) (v := w) (by omega) hw
  · intro x hx
    rw [hwsem, Bool.and_eq_true, Bool.or_eq_true] at hx
    rcases hx.2 with hzx | hzpx
    · exact (Finset.mem_filter.mp hz).2 x hx.1 hzx
    · exact (Finset.mem_filter.mp hzp).2 x hx.1 hzpx
  · intro a b hU hh
    rw [hwsem, Bool.and_eq_true]
    have hg := hhbelow (pairInput a b) hh
    have hab := SimpleGraph.mem_edgeFinset.mp (Finset.mem_sdiff.mp hU).1
    exact ⟨hg, flag_pair_has_center g P Q z zp hPQ hcross hgsem a b hab hg⟩


lemma delCircuit_wval_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) (x : Fin n → Bool)
    {j r : ℕ} (hj : j < C.gates.length) (hr : r < n + j)
    (heq : wval C x r = wval C x (n + j)) :
    ∀ w < n + C.gates.length, wval (delCircuit n C j r) x (delWire n j r w) = wval C x w := by
  have hAO' := delCircuit_isAO2 hAO hj hr
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · have hdw : delWire n j r w = w := by unfold delWire; rw [if_neg (by omega), if_neg (by omega)]
      rw [hdw, wval_input _ x w hwn, wval_input _ x w hwn]
    · by_cases hwj : w = n + j
      · subst hwj
        have hdw : delWire n j r (n + j) = r := by unfold delWire; simp
        have hdr : delWire n j r r = r := by unfold delWire; rw [if_neg (by omega), if_neg (by omega)]
        have h1 := ih r hr (by omega)
        rw [hdr] at h1
        rw [hdw, h1, heq]
      · by_cases hlt : w < n + j
        · have hk : w - n < j := by omega
          have hdw : delWire n j r w = n + (w - n) := by
            unfold delWire; rw [if_neg hwj, if_neg (by omega)]; omega
          have hw_eq : w = n + (w - n) := by omega
          rw [hdw]
          conv_rhs => rw [hw_eq]
          have hk' : w - n < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
          rw [wval_gate_eval hAO' x hk', wval_gate_eval hAO x (by omega)]
          have hg := delCircuit_gateAt_lt (n := n) (r := r) hj hk
          rw [delCircuit_opnd_lt hAO hj hk 0, delCircuit_opnd_lt hAO hj hk 1]
          have h0 := ih (opnd C (w - n) 0) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 0; omega)
          have h1 := ih (opnd C (w - n) 1) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega) (by have := opnd_lt hAO (by omega : w - n < C.gates.length) 1; omega)
          rw [h0, h1, hg]
        · have hgt : n + j < w := by omega
          have hk : w - n - 1 < C.gates.length - 1 := by omega
          have hjk : j ≤ w - n - 1 := by omega
          have hdw : delWire n j r w = n + (w - n - 1) := by
            unfold delWire; rw [if_neg hwj, if_pos hgt]; omega
          have hw_eq : w = n + (w - n - 1 + 1) := by omega
          rw [hdw]
          conv_rhs => rw [hw_eq]
          have hk' : w - n - 1 < (delCircuit n C j r).gates.length := by rw [delCircuit_len n C hj r]; omega
          rw [wval_gate_eval hAO' x hk', wval_gate_eval hAO x (by omega)]
          have hg := delCircuit_gateAt_ge (n := n) (r := r) hj hjk hk
          rw [delCircuit_opnd_ge hAO hj hjk hk 0, delCircuit_opnd_ge hAO hj hjk hk 1]
          have h0 := ih (opnd C (w - n - 1 + 1) 0) (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega) (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 0; omega)
          have h1 := ih (opnd C (w - n - 1 + 1) 1) (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega) (by have := opnd_lt hAO (by omega : w - n - 1 + 1 < C.gates.length) 1; omega)
          rw [h0, h1, hg]



lemma least_no_equiv_wire {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hL : IsLeastAO G C) (hne : ∃ u v : Fin n, G.Adj u v)
    {j r : ℕ} (hj : j < C.gates.length) (hr : r < n + j) :
    ¬ ∀ x : Fin n → Bool, wval C x r = wval C x (n + j) := by
  have hout := output_bounds hL hne
  intro heq
  let C' := delCircuit n C j r
  have hAO' := delCircuit_isAO2 hL.1 hj hr
  have hfun' : circuitFun n C' = graphFun G ∅ := by
    funext x
    change wval C' x C'.output = graphFun G ∅ x
    rw [← congrFun hL.2.1 x]
    exact delCircuit_wval_eq hL.1 x hj hr (heq x) C.output hout.2
  have hsz := hL.2.2 C' hAO' hfun'
  simp only [Circuit.size, C', delCircuit_len n C hj r] at hsz
  omega



lemma least_pure_wire_pair_support {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} (hL : IsLeastAO G C)
    (hne : ∃ a b : Fin n, G.Adj a b) {w : ℕ} (hnw : n ≤ w)
    (hw : w < n + C.gates.length) (R : Finset (Fin n)) (hR : R.Nonempty)
    (z zp : Fin n) (hsub : R ⊆ {z, zp})
    (hsem : ∀ x : Fin n → Bool, wval C x w = decide (∃ r ∈ R, x r = true)) :
    ∀ x : Fin n → Bool, wval C x w = (x z || x zp) := by
  have hnot (r : Fin n) (hRr : R = {r}) : False := by
    have hj : w - n < C.gates.length := by omega
    apply least_no_equiv_wire hL hne hj (r := r.val) (by have := r.isLt; omega)
    intro x
    have hweq : n + (w - n) = w := by omega
    rw [wval_input C x r.val r.isLt, hweq, hsem, hRr]
    simp
  have hcard : 2 ≤ R.card := by
    by_contra hh
    have hone : R.card = 1 := by have := Finset.card_pos.mpr hR; omega
    obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hone
    exact hnot r hr
  have hpair : ({z, zp} : Finset (Fin n)).card ≤ 2 := by
    by_cases hzz : z = zp <;> simp [hzz]
  have heq : R = {z, zp} := Finset.eq_of_subset_of_card_le hsub (by omega)
  intro x
  rw [hsem]
  simp [heq, Bool.decide_or]

lemma no_nested_flag_shared_support {n : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj]
    (hfirst : ∀ D : Circuit, IsLeastAO G D → (junk G D).card ≠ 1)
    {C : Circuit} (hL : IsLeastAO G C) (hTF : TopForm G C) (h4 : NoFourCycle G)
    (hne : ∃ a b : Fin n, G.Adj a b)
    {g h w : ℕ} (hjunk : junk G C = {g, h}) (hgh : g < h)
    (hnw : n ≤ w) (hw : w < n + h)
    (P Q R : Finset (Fin n)) (hR : R.Nonempty) (z zp : Fin n)
    (hsub : R ⊆ {z, zp}) (hPQ : Disjoint P Q) (hzP : z ∈ P) (hzpQ : zp ∈ Q)
    (hz : z ∈ wmax G C g) (hzp : zp ∈ wmax G C g)
    (hgsem : ∀ x : Fin n → Bool, gateVal n C g x =
      (decide (∃ p ∈ P, x p = true) && decide (∃ q ∈ Q, x q = true)))
    (hhbelow : ∀ x : Fin n → Bool, gateVal n C h x = true → gateVal n C g x = true)
    (hwsem : ∀ x : Fin n → Bool, wval C x w = decide (∃ r ∈ R, x r = true)) : False := by
  have hhmem : h ∈ junk G C := by simp [hjunk]
  have hhlen := (Finset.mem_filter.mp hhmem).2.2.1
  have hcenters := least_pure_wire_pair_support hL hne hnw (by omega) R hR z zp hsub hwsem
  exact no_nested_flag_center_wire hfirst hL hTF h4 hjunk hgh hw P Q z zp hPQ hzP hzpQ
    hz hzp hgsem hhbelow hcenters

end PEqualNP.Outside.L_meta_5012.RestrictionNestedShared
