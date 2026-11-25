import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5012.RestrictionSurgery

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

end PEqualNP.Outside.L_meta_5012.RestrictionSurgery
