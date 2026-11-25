import Mathlib.Logic.Relation
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

namespace LiftAux


open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def evalGates (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma evalGates_length (gs : List Gate) (w : List Bool) :
    (evalGates gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [evalGates]
  | cons g gs ih =>
    simp only [evalGates, List.foldl_cons] at ih ⊢
    rw [ih]
    simp
    omega

lemma evalGates_append (gs1 gs2 : List Gate) (w : List Bool) :
    evalGates (gs1 ++ gs2) w = evalGates gs2 (evalGates gs1 w) := by
  simp [evalGates, List.foldl_append]

lemma evalGates_getD_lt (gs : List Gate) (w : List Bool) (k : ℕ) (hk : k < w.length) :
    (evalGates gs w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [evalGates, List.foldl_cons] at ih ⊢
    have hk' : k < (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]).length := by
      simp
      omega
    rw [ih _ hk']
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

lemma evalGates_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (evalGates gs w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i => (evalGates (gs.take j) w).getD i false) := by
  have hsplit : gs = gs.take j ++ [gs[j]] ++ gs.drop (j + 1) := by
    have h1 := List.take_append_drop j gs
    have h2 : gs.drop j = gs[j] :: gs.drop (j + 1) := List.drop_eq_getElem_cons hj
    rw [h2] at h1
    simp
  conv_lhs => rw [hsplit]
  rw [evalGates_append, evalGates_append]
  set w1 := evalGates (gs.take j) w
  have hw1 : w1.length = w.length + j := by
    rw [evalGates_length, List.length_take]
    omega
  have hlt : w.length + j < (evalGates [gs[j]] w1).length := by
    rw [evalGates_length, hw1]
    simp
  rw [evalGates_getD_lt _ _ _ hlt]
  simp only [evalGates, List.foldl_cons, List.foldl_nil]
  rw [← hw1]
  simp [List.getD_eq_getElem?_getD]

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma wires_getD_gate (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (x : List Bool) (hx : x.length = n) (j : ℕ) (hj : j < C.gates.length) :
    (C.wires x).getD (n + j) false =
      (C.gates[j]).op.eval ((C.gates[j]).inputs.map fun i => (C.wires x).getD i false) := by
  change (evalGates C.gates x).getD (n + j) false = _
  have h1 := evalGates_getD_gate C.gates x j hj
  rw [hx] at h1
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro i hi
  have hi_lt : i < n + j := by
    have := hRB j hj i
    rw [gateAt_eq_getElem C j hj] at this
    exact this hi
  have hlen : (evalGates (C.gates.take j) x).length = n + j := by
    rw [evalGates_length, hx, List.length_take]
    omega
  have hsplit : C.gates = C.gates.take j ++ C.gates.drop j := (List.take_append_drop j C.gates).symm
  symm
  change (evalGates C.gates x).getD i false = (evalGates (C.gates.take j) x).getD i false
  conv_lhs => rw [hsplit, evalGates_append]
  exact evalGates_getD_lt (C.gates.drop j) (evalGates (C.gates.take j) x) i (by omega)

lemma eraseRedirect_lt (n m p j u : ℕ) (hp : p < n + m) (hmj : m ≤ j) (hu : u < n + (j + 1)) :
    eraseRedirect n m p u < n + j := by
  unfold eraseRedirect
  split_ifs <;> omega

lemma eraseGate_gates_length (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates.length = C.gates.length - 1 := by
  simp [eraseGate, hm]
  omega

lemma liftAt_gates_length (n : ℕ) (C : Circuit) (m p h : ℕ) (hm : m < C.gates.length) :
    (liftAt n C m p h).gates.length = C.gates.length := by
  simp [liftAt, eraseGate_gates_length n C m p hm]
  omega

lemma eraseGate_output_lt (n : ℕ) (C : Circuit) (m p : ℕ)
    (hm : m < C.gates.length) (hp : p < n + m) (hout : C.output < n + C.gates.length) :
    (eraseGate n C m p).output < n + (eraseGate n C m p).gates.length := by
  rw [eraseGate_gates_length n C m p hm]
  simp only [eraseGate, hm, ↓reduceIte]
  unfold eraseRedirect
  split_ifs <;> omega

lemma eraseGate_getElem_lt (n : ℕ) (C : Circuit) (m p j : ℕ)
    (hm : m < C.gates.length) (hjm : j < m) (hj : j < (eraseGate n C m p).gates.length) :
    (eraseGate n C m p).gates[j] = C.gates[j]'(by omega) := by
  have htake : j < (C.gates.take m).length := by simp; omega
  simp only [eraseGate, hm, ↓reduceIte]
  rw [List.getElem_append_left htake, List.getElem_take]

lemma eraseGate_getElem_ge (n : ℕ) (C : Circuit) (m p j : ℕ)
    (hm : m < C.gates.length) (hmj : m ≤ j) (hj : j < (eraseGate n C m p).gates.length) :
    (eraseGate n C m p).gates[j] =
      ⟨(C.gates[j + 1]'(by have := eraseGate_gates_length n C m p hm; omega)).op,
        (C.gates[j + 1]'(by have := eraseGate_gates_length n C m p hm; omega)).inputs.map
          (eraseRedirect n m p)⟩ := by
  have hlen := eraseGate_gates_length n C m p hm
  have htake : (C.gates.take m).length = m := by simp; omega
  have hidx : m + 1 + (j - m) = j + 1 := by omega
  simp only [eraseGate, hm, ↓reduceIte]
  rw [List.getElem_append_right (by omega)]
  simp only [htake, List.getElem_map, List.getElem_drop, hidx]

lemma eraseGate_isAO2 (n : ℕ) (C : Circuit) (m p : ℕ)
    (hAO : IsAO2 n C) (hm : m < C.gates.length) (hp : p < n + m) :
    IsAO2 n (eraseGate n C m p) := by
  rcases hAO with ⟨hAO_op, hRB, hLen2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [eraseGate, hm, ↓reduceIte, List.mem_append, List.mem_map] at hg
    rcases hg with h1 | ⟨g0, hg0, rfl⟩
    · exact hAO_op g (List.mem_of_mem_take h1)
    · exact hAO_op g0 (List.mem_of_mem_drop hg0)
  · intro j hj i hi
    rw [gateAt_eq_getElem _ j hj] at hi
    by_cases hjm : j < m
    · rw [eraseGate_getElem_lt n C m p j hm hjm hj] at hi
      have := hRB j (by omega) i
      rw [gateAt_eq_getElem C j (by omega)] at this
      exact this hi
    · have hmj : m ≤ j := by omega
      have hlen := eraseGate_gates_length n C m p hm
      rw [eraseGate_getElem_ge n C m p j hm hmj hj] at hi
      simp only [List.mem_map] at hi
      rcases hi with ⟨u, hu, rfl⟩
      have hu_lt : u < n + (j + 1) := by
        have := hRB (j + 1) (by omega) u
        rw [gateAt_eq_getElem C (j + 1) (by omega)] at this
        exact this hu
      exact eraseRedirect_lt n m p j u hp hmj hu_lt
  · intro g hg
    simp only [eraseGate, hm, ↓reduceIte, List.mem_append, List.mem_map] at hg
    rcases hg with h1 | ⟨g0, hg0, rfl⟩
    · exact hLen2 g (List.mem_of_mem_take h1)
    · simp [hLen2 g0 (List.mem_of_mem_drop hg0)]

lemma liftAt_isAO2 (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m) :
    IsAO2 n (liftAt n C m p h) := by
  have hE := eraseGate_isAO2 n C m p hAO hm hp
  have hEout := eraseGate_output_lt n C m p hm hp hout
  have hElen := eraseGate_gates_length n C m p hm
  rcases hE with ⟨hE_op, hE_RB, hE_len2⟩
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [liftAt, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hE_op g hg
    · exact Or.inr rfl
  · intro j hj i hi
    rw [gateAt_eq_getElem _ j hj] at hi
    simp only [liftAt, List.length_append, List.length_singleton] at hj
    by_cases hjE : j < (eraseGate n C m p).gates.length
    · have hg : (liftAt n C m p h).gates[j] = (eraseGate n C m p).gates[j] := by
        simp only [liftAt]
        rw [List.getElem_append_left hjE]
      rw [hg] at hi
      have := hE_RB j hjE i
      rw [gateAt_eq_getElem _ j hjE] at this
      exact this hi
    · have hj_eq : j = (eraseGate n C m p).gates.length := by omega
      have hg : (liftAt n C m p h).gates[j] = ⟨GateOp.or, [(eraseGate n C m p).output, h]⟩ := by
        simp only [liftAt]
        rw [List.getElem_append_right (by omega)]
        have : j - (eraseGate n C m p).gates.length = 0 := by omega
        simp [this]
      rw [hg] at hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl
      · omega
      · omega
  · intro g hg
    simp only [liftAt, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hE_len2 g hg
    · rfl

lemma eraseGate_wires_prefix (n : ℕ) (C : Circuit) (m p : ℕ)
    (hm : m < C.gates.length) (x : List Bool) (hx : x.length = n)
    (k : ℕ) (hk : k < n + m) :
    ((eraseGate n C m p).wires x).getD k false = (C.wires x).getD k false := by
  change (evalGates (eraseGate n C m p).gates x).getD k false = (evalGates C.gates x).getD k false
  have hC : C.gates = C.gates.take m ++ C.gates.drop m := (List.take_append_drop m C.gates).symm
  have hE : (eraseGate n C m p).gates = C.gates.take m ++
      (C.gates.drop (m + 1)).map (fun g => ⟨g.op, g.inputs.map (eraseRedirect n m p)⟩) := by
    simp [eraseGate, hm]
  have hlen : (evalGates (C.gates.take m) x).length = n + m := by
    rw [evalGates_length, hx, List.length_take]
    omega
  have hl : (evalGates (eraseGate n C m p).gates x).getD k false =
      (evalGates (C.gates.take m) x).getD k false := by
    rw [hE, evalGates_append]
    exact evalGates_getD_lt _ _ k (by omega)
  have hr : (evalGates C.gates x).getD k false =
      (evalGates (C.gates.take m) x).getD k false := by
    conv_lhs => rw [hC, evalGates_append]
    exact evalGates_getD_lt _ _ k (by omega)
  rw [hl, hr]

lemma liftAt_wires_lt (n : ℕ) (C : Circuit) (m p h : ℕ)
    (x : List Bool) (hx : x.length = n)
    (k : ℕ) (hk : k < n + (eraseGate n C m p).gates.length) :
    ((liftAt n C m p h).wires x).getD k false = ((eraseGate n C m p).wires x).getD k false := by
  change (evalGates ((eraseGate n C m p).gates ++ _) x).getD k false =
    (evalGates (eraseGate n C m p).gates x).getD k false
  rw [evalGates_append]
  have hlen : (evalGates (eraseGate n C m p).gates x).length = n + (eraseGate n C m p).gates.length := by
    rw [evalGates_length, hx]
  exact evalGates_getD_lt _ _ k (by omega)

lemma liftAt_eval_formula (n : ℕ) (C : Circuit) (m p h : ℕ)
    (x : List Bool) (hx : x.length = n) :
    (liftAt n C m p h).eval x =
      ((eraseGate n C m p).eval x || ((eraseGate n C m p).wires x).getD h false) := by
  unfold Circuit.eval liftAt
  change (evalGates ((eraseGate n C m p).gates ++ [⟨GateOp.or, [(eraseGate n C m p).output, h]⟩]) x).getD
      (n + (eraseGate n C m p).gates.length) false =
    ((evalGates (eraseGate n C m p).gates x).getD (eraseGate n C m p).output false ||
      (evalGates (eraseGate n C m p).gates x).getD h false)
  rw [evalGates_append]
  set wE := evalGates (eraseGate n C m p).gates x
  have hwE : wE.length = n + (eraseGate n C m p).gates.length := by
    rw [evalGates_length, hx]
  simp only [evalGates, List.foldl_cons, List.foldl_nil]
  rw [← hwE]
  simp [List.getD_eq_getElem?_getD, GateOp.eval]

lemma gateOp_eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List ℕ) (f g : ℕ → Bool) (hfg : ∀ u ∈ l, f u = true → g u = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
    intro hf b hb
    rcases hb with ⟨u, hu, rfl⟩
    exact hfg u hu (hf (f u) ⟨u, hu, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    rintro ⟨b, ⟨u, hu, rfl⟩, hfu⟩
    exact ⟨g u, ⟨u, hu, rfl⟩, hfg u hu hfu⟩

lemma gate_m_val (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hRB : ReadsBack n C) (hm : m < C.gates.length)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (x : List Bool) (hx : x.length = n) :
    (C.wires x).getD (n + m) false = ((C.wires x).getD p false || (C.wires x).getD h false) := by
  rw [wires_getD_gate n C hRB x hx m hm]
  have hg : C.gates[m] = ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m] = ⟨GateOp.or, [h, p]⟩ := by
    rcases hgate with h1 | h1
    · left; simpa [hm] using h1
    · right; simpa [hm] using h1
  rcases hg with h1 | h1
  · rw [h1]; simp [GateOp.eval]
  · rw [h1]; simp [GateOp.eval, Bool.or_comm]

lemma eraseGate_wires_le (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hAO : IsAO2 n C) (hm : m < C.gates.length) (hp : p < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (x : List Bool) (hx : x.length = n) :
    ∀ k < n + (eraseGate n C m p).gates.length,
      ((eraseGate n C m p).wires x).getD k false = true →
      (C.wires x).getD (if k < n + m then k else k + 1) false = true := by
  have hEAO := eraseGate_isAO2 n C m p hAO hm hp
  have hElen := eraseGate_gates_length n C m p hm
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk htrue
    by_cases hkm : k < n + m
    · simp only [hkm, ↓reduceIte]
      rwa [eraseGate_wires_prefix n C m p hm x hx k hkm] at htrue
    · simp only [hkm, ↓reduceIte]
      set j := k - n
      have hkj : k = n + j := by omega
      have hmj : m ≤ j := by omega
      have hjE : j < (eraseGate n C m p).gates.length := by omega
      have hjC : j + 1 < C.gates.length := by omega
      rw [hkj] at htrue ⊢
      have hkj1 : n + j + 1 = n + (j + 1) := by omega
      rw [hkj1]
      rw [wires_getD_gate n (eraseGate n C m p) hEAO.2.1 x hx j hjE] at htrue
      rw [eraseGate_getElem_ge n C m p j hm hmj hjE] at htrue
      rw [List.map_map] at htrue
      rw [wires_getD_gate n C hAO.2.1 x hx (j + 1) hjC]
      have hop : (C.gates[j + 1]).op = GateOp.and ∨ (C.gates[j + 1]).op = GateOp.or :=
        hAO.1 _ (List.getElem_mem hjC)
      refine gateOp_eval_mono _ hop _ _ _ ?_ htrue
      intro u hu huE
      have hu_lt : u < n + (j + 1) := by
        have := hAO.2.1 (j + 1) hjC u
        rw [gateAt_eq_getElem C (j + 1) hjC] at this
        exact this hu
      simp only [Function.comp_apply] at huE
      unfold eraseRedirect at huE
      split_ifs at huE with heq hgt
      · rw [heq, gate_m_val n C m p h hAO.2.1 hm hgate x hx]
        rw [eraseGate_wires_prefix n C m p hm x hx p hp] at huE
        rw [huE]
        rfl
      · have hstep := ih (u - 1) (by omega) (by omega) huE
        have hnotlt : ¬ (u - 1 < n + m) := by omega
        simp only [hnotlt, ↓reduceIte] at hstep
        have hu1 : u - 1 + 1 = u := by omega
        rwa [hu1] at hstep
      · have hult : u < n + m := by omega
        rwa [eraseGate_wires_prefix n C m p hm x hx u hult] at huE

lemma eraseGate_wires_eq_of_h_false (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hAO : IsAO2 n C) (hm : m < C.gates.length) (hp : p < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (x : List Bool) (hx : x.length = n) (hfalse : (C.wires x).getD h false = false) :
    ∀ k < n + (eraseGate n C m p).gates.length,
      ((eraseGate n C m p).wires x).getD k false =
      (C.wires x).getD (if k < n + m then k else k + 1) false := by
  have hEAO := eraseGate_isAO2 n C m p hAO hm hp
  have hElen := eraseGate_gates_length n C m p hm
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk
    by_cases hkm : k < n + m
    · simp only [hkm, ↓reduceIte]
      exact eraseGate_wires_prefix n C m p hm x hx k hkm
    · simp only [hkm, ↓reduceIte]
      set j := k - n
      have hkj : k = n + j := by omega
      have hmj : m ≤ j := by omega
      have hjE : j < (eraseGate n C m p).gates.length := by omega
      have hjC : j + 1 < C.gates.length := by omega
      rw [hkj]
      have hkj1 : n + j + 1 = n + (j + 1) := by omega
      rw [hkj1]
      rw [wires_getD_gate n (eraseGate n C m p) hEAO.2.1 x hx j hjE]
      rw [eraseGate_getElem_ge n C m p j hm hmj hjE]
      rw [List.map_map]
      rw [wires_getD_gate n C hAO.2.1 x hx (j + 1) hjC]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hu_lt : u < n + (j + 1) := by
        have := hAO.2.1 (j + 1) hjC u
        rw [gateAt_eq_getElem C (j + 1) hjC] at this
        exact this hu
      simp only [Function.comp_apply]
      unfold eraseRedirect
      split_ifs with heq hgt
      · rw [heq, gate_m_val n C m p h hAO.2.1 hm hgate x hx, hfalse, Bool.or_false]
        exact eraseGate_wires_prefix n C m p hm x hx p hp
      · have hstep := ih (u - 1) (by omega) (by omega)
        have hnotlt : ¬ (u - 1 < n + m) := by omega
        simp only [hnotlt, ↓reduceIte] at hstep
        have hu1 : u - 1 + 1 = u := by omega
        rwa [hu1] at hstep
      · have hult : u < n + m := by omega
        exact eraseGate_wires_prefix n C m p hm x hx u hult

lemma liftAt_eval_eq (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (hBelowH : WireBelowOutput n C h) (v : Fin n → Bool) :
    (liftAt n C m p h).eval (List.ofFn v) = C.eval (List.ofFn v) := by
  have hx : (List.ofFn v).length = n := List.length_ofFn
  rw [liftAt_eval_formula n C m p h (List.ofFn v) hx]
  rw [eraseGate_wires_prefix n C m p hm (List.ofFn v) hx h hh]
  cases hb : (C.wires (List.ofFn v)).getD h false
  · rw [Bool.or_false]
    unfold Circuit.eval
    have hEout : (eraseGate n C m p).output = eraseRedirect n m p C.output := by
      simp [eraseGate, hm]
    rw [hEout]
    have hElen := eraseGate_gates_length n C m p hm
    unfold eraseRedirect
    split_ifs with heq hgt
    · rw [heq, gate_m_val n C m p h hAO.2.1 hm hgate (List.ofFn v) hx, hb, Bool.or_false]
      exact eraseGate_wires_prefix n C m p hm (List.ofFn v) hx p hp
    · have hstep := eraseGate_wires_eq_of_h_false n C m p h hAO hm hp hgate
        (List.ofFn v) hx hb (C.output - 1) (by omega)
      have hnotlt : ¬ (C.output - 1 < n + m) := by omega
      simp only [hnotlt, ↓reduceIte] at hstep
      have ho1 : C.output - 1 + 1 = C.output := by omega
      rwa [ho1] at hstep
    · have holt : C.output < n + m := by omega
      exact eraseGate_wires_prefix n C m p hm (List.ofFn v) hx C.output holt
  · rw [Bool.or_true]
    exact (hBelowH v hb).symm

noncomputable def belowCount (n : ℕ) (C : Circuit) : ℕ :=
  ((Finset.range C.gates.length).filter (fun j => WireBelowOutput n C (n + j))).card

lemma belowCount_le (n : ℕ) (C : Circuit) : belowCount n C ≤ C.gates.length := by
  unfold belowCount
  calc ((Finset.range C.gates.length).filter _).card
      ≤ (Finset.range C.gates.length).card := Finset.card_filter_le _ _
    _ = C.gates.length := Finset.card_range _

lemma belowCount_lt_liftAt (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hm : m < C.gates.length) (hp : p < n + m) (hh : h < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨ C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (hBelowH : WireBelowOutput n C h) (hNotBelowP : ¬ WireBelowOutput n C p) :
    belowCount n C < belowCount n (liftAt n C m p h) := by
  classical
  have hElen : (eraseGate n C m p).gates.length = C.gates.length - 1 :=
    eraseGate_gates_length n C m p hm
  have hC'len : (liftAt n C m p h).gates.length = C.gates.length :=
    liftAt_gates_length n C m p h hm
  have heval : ∀ v : Fin n → Bool, (liftAt n C m p h).eval (List.ofFn v) = C.eval (List.ofFn v) :=
    liftAt_eval_eq n C m p h hAO hout hm hp hh hgate hBelowH
  set S := (Finset.range C.gates.length).filter (fun j => WireBelowOutput n C (n + j))
  set S' := (Finset.range (liftAt n C m p h).gates.length).filter
    (fun j => WireBelowOutput n (liftAt n C m p h) (n + j))
  have hm_not : m ∉ S := by
    intro hmS
    have hBm : WireBelowOutput n C (n + m) := (Finset.mem_filter.mp hmS).2
    apply hNotBelowP
    intro v hpv
    apply hBm v
    rw [gate_m_val n C m p h hAO.2.1 hm hgate (List.ofFn v) List.length_ofFn, hpv]
    rfl
  have hlast_mem : (eraseGate n C m p).gates.length ∈ S' := by
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    intro v hv
    exact hv
  let f : ℕ → ℕ := fun j => if j < m then j else j - 1
  have hsub : S.image f ⊆ S'.erase (eraseGate n C m p).gates.length := by
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨j, hjS, rfl⟩
    have hj_ne : j ≠ m := fun heq => hm_not (heq ▸ hjS)
    rcases Finset.mem_filter.mp hjS with ⟨hj_rng, hBj⟩
    have hj_lt : j < C.gates.length := Finset.mem_range.mp hj_rng
    rw [Finset.mem_erase, Finset.mem_filter, Finset.mem_range]
    by_cases hjm : j < m
    · simp only [f, hjm, ↓reduceIte]
      refine ⟨by omega, by omega, ?_⟩
      intro v hv
      rw [heval v]
      apply hBj v
      rw [liftAt_wires_lt n C m p h (List.ofFn v) List.length_ofFn (n + j) (by omega)] at hv
      rwa [eraseGate_wires_prefix n C m p hm (List.ofFn v) List.length_ofFn (n + j) (by omega)] at hv
    · simp only [f, hjm, ↓reduceIte]
      refine ⟨by omega, by omega, ?_⟩
      intro v hv
      rw [heval v]
      apply hBj v
      rw [liftAt_wires_lt n C m p h (List.ofFn v) List.length_ofFn (n + (j - 1)) (by omega)] at hv
      have hle := eraseGate_wires_le n C m p h hAO hm hp hgate
        (List.ofFn v) List.length_ofFn (n + (j - 1)) (by omega) hv
      have hnotlt : ¬ (n + (j - 1) < n + m) := by omega
      simp only [hnotlt, ↓reduceIte] at hle
      have hj1 : n + (j - 1) + 1 = n + j := by omega
      rwa [hj1] at hle
  have hinj : Set.InjOn f (S : Set ℕ) := by
    intro j1 hj1 j2 hj2 hfeq
    have h1ne : j1 ≠ m := fun heq => hm_not (heq ▸ hj1)
    have h2ne : j2 ≠ m := fun heq => hm_not (heq ▸ hj2)
    simp only [f] at hfeq
    split_ifs at hfeq <;> omega
  have hcard1 : S.card = (S.image f).card := (Finset.card_image_of_injOn hinj).symm
  have hcard2 : (S.image f).card ≤ (S'.erase (eraseGate n C m p).gates.length).card :=
    Finset.card_le_card hsub
  have hcard3 : (S'.erase (eraseGate n C m p).gates.length).card + 1 = S'.card :=
    Finset.card_erase_add_one hlast_mem
  show S.card < S'.card
  omega


lemma main : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output < x1 + x2.gates.length → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), Relation.ReflTransGen (PEqualNP.CircuitMoves.Lift x1) x2 x5 ∧ ∀ x6 < x5.gates.length, ∀ (x8 x9 : ℕ), x5.gates[x6]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x8, x9] : PEqualNP.CircuitLowerBounds.Gate } → (x1 ≤ x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x8) ∧ (x1 ≤ x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x9) := by
  intro n C hAO hout
  have main : ∀ k : ℕ, ∀ C0 : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 n C0 →
      C0.output < n + C0.gates.length →
      C0.gates.length - PEqualNP.Outside.L_meta_2583.LiftAux.belowCount n C0 = k →
      ∃ C' : PEqualNP.CircuitLowerBounds.Circuit,
        Relation.ReflTransGen (PEqualNP.CircuitMoves.Lift n) C0 C' ∧
        ∀ m < C'.gates.length, ∀ a b : ℕ,
          C'.gates[m]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a, b] } →
          (n ≤ b → PEqualNP.CircuitMoves.WireBelowOutput n C' b → PEqualNP.CircuitMoves.WireBelowOutput n C' a) ∧
          (n ≤ a → PEqualNP.CircuitMoves.WireBelowOutput n C' a → PEqualNP.CircuitMoves.WireBelowOutput n C' b) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro C0 hAO0 hout0 hk0
      by_cases hNF : ∀ m < C0.gates.length, ∀ a b : ℕ,
          C0.gates[m]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a, b] } →
          (n ≤ b → PEqualNP.CircuitMoves.WireBelowOutput n C0 b → PEqualNP.CircuitMoves.WireBelowOutput n C0 a) ∧
          (n ≤ a → PEqualNP.CircuitMoves.WireBelowOutput n C0 a → PEqualNP.CircuitMoves.WireBelowOutput n C0 b)
      · exact ⟨C0, Relation.ReflTransGen.refl, hNF⟩
      · push Not at hNF
        rcases hNF with ⟨m, hm, a, b, hgate, hbad⟩
        have ha_lt : a < n + m := by
          have := hAO0.2.1 m hm a
          rw [PEqualNP.Outside.L_meta_2583.LiftAux.gateAt_eq_getElem C0 m hm] at this
          have hgm : C0.gates[m] = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a, b] } := by
            simpa [hm] using hgate
          rw [hgm] at this
          exact this (by simp)
        have hb_lt : b < n + m := by
          have := hAO0.2.1 m hm b
          rw [PEqualNP.Outside.L_meta_2583.LiftAux.gateAt_eq_getElem C0 m hm] at this
          have hgm : C0.gates[m] = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a, b] } := by
            simpa [hm] using hgate
          rw [hgm] at this
          exact this (by simp)
        have hstep : ∃ p h : ℕ, p < n + m ∧ h < n + m ∧ n ≤ h ∧
            (C0.gates[m]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [p, h] } ∨
              C0.gates[m]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [h, p] }) ∧
            PEqualNP.CircuitMoves.WireBelowOutput n C0 h ∧
            ¬ PEqualNP.CircuitMoves.WireBelowOutput n C0 p := by
          by_cases h1 : n ≤ b → PEqualNP.CircuitMoves.WireBelowOutput n C0 b →
              PEqualNP.CircuitMoves.WireBelowOutput n C0 a
          · rcases hbad h1 with ⟨hna, hBa, hNb⟩
            exact ⟨b, a, hb_lt, ha_lt, hna, Or.inr hgate, hBa, hNb⟩
          · push Not at h1
            rcases h1 with ⟨hnb, hBb, hNa⟩
            exact ⟨a, b, ha_lt, hb_lt, hnb, Or.inl hgate, hBb, hNa⟩
        rcases hstep with ⟨p, h, hp, hh, hnh, hgm, hBh, hNp⟩
        have hLift : PEqualNP.CircuitMoves.Lift n C0 (PEqualNP.CircuitMoves.liftAt n C0 m p h) :=
          ⟨m, hm, p, hp, h, hh, hnh, hgm, hBh, rfl⟩
        have hAO1 := PEqualNP.Outside.L_meta_2583.LiftAux.liftAt_isAO2 n C0 m p h hAO0 hout0 hm hp hh
        have hlen1 := PEqualNP.Outside.L_meta_2583.LiftAux.liftAt_gates_length n C0 m p h hm
        have hElen := PEqualNP.Outside.L_meta_2583.LiftAux.eraseGate_gates_length n C0 m p hm
        have hout1 : (PEqualNP.CircuitMoves.liftAt n C0 m p h).output <
            n + (PEqualNP.CircuitMoves.liftAt n C0 m p h).gates.length := by
          change n + (PEqualNP.CircuitMoves.eraseGate n C0 m p).gates.length <
            n + (PEqualNP.CircuitMoves.liftAt n C0 m p h).gates.length
          omega
        have hlt := PEqualNP.Outside.L_meta_2583.LiftAux.belowCount_lt_liftAt n C0 m p h hAO0 hout0 hm hp hh hgm hBh hNp
        have hle1 := PEqualNP.Outside.L_meta_2583.LiftAux.belowCount_le n (PEqualNP.CircuitMoves.liftAt n C0 m p h)
        have hk1 : (PEqualNP.CircuitMoves.liftAt n C0 m p h).gates.length -
            PEqualNP.Outside.L_meta_2583.LiftAux.belowCount n (PEqualNP.CircuitMoves.liftAt n C0 m p h) < k := by
          omega
        obtain ⟨C', hR, hNF'⟩ := ih _ hk1 (PEqualNP.CircuitMoves.liftAt n C0 m p h) hAO1 hout1 rfl
        exact ⟨C', Relation.ReflTransGen.head hLift hR, hNF'⟩
  exact main _ C hAO hout rfl

end LiftAux

namespace SplitAux


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.CircuitMoves

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_wireStep_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl wireStep acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wireStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wireStep_prefix (gs : List Gate) (acc : List Bool) (w : ℕ) (hw : w < acc.length) :
    (gs.foldl wireStep acc).getD w false = acc.getD w false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hw' : w < (wireStep acc g).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (wireStep acc g) hw']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_left hw]

lemma gateAt_eq_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

lemma wireValue_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    PEqualNP.BlindGate.wireValue C n x w = x ⟨w, hw⟩ := by
  unfold PEqualNP.BlindGate.wireValue Circuit.wires
  have hw' : w < (List.ofFn x).length := by simp [hw]
  have h1 := foldl_wireStep_prefix C.gates (List.ofFn x) w hw'
  change (C.gates.foldl wireStep (List.ofFn x)).getD w false = x ⟨w, hw⟩
  rw [h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw']
  simp

lemma wireValue_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ)
    (hk : k < C.gates.length) (hRB : ReadsBack n C) :
    PEqualNP.BlindGate.wireValue C n x (n + k) =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun u => PEqualNP.BlindGate.wireValue C n x u) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take k).foldl wireStep (List.ofFn x) with hacc
  have hacc_len : acc.length = n + k := by
    rw [hacc, foldl_wireStep_length, List.length_ofFn, List.length_take]
    omega
  have hpref : ∀ u < n + k, PEqualNP.BlindGate.wireValue C n x u = acc.getD u false := by
    intro u hu
    unfold PEqualNP.BlindGate.wireValue Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD u false = acc.getD u false
    conv_lhs => rw [← List.take_append_drop k C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_wireStep_prefix (C.gates.drop k) acc u (by omega)
  have hval : PEqualNP.BlindGate.wireValue C n x (n + k) =
      C.gates[k].op.eval (C.gates[k].inputs.map fun u => acc.getD u false) := by
    unfold PEqualNP.BlindGate.wireValue Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD (n + k) false = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : n + k < (wireStep acc C.gates[k]).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_wireStep_prefix (C.gates.drop (k + 1)) (wireStep acc C.gates[k]) (n + k) hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_right (by omega : acc.length ≤ n + k),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hval, gateAt_eq_getElem C k hk]
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [← gateAt_eq_getElem C k hk] at hu
  exact (hpref u (hRB k hk u hu)).symm

lemma list_eq_two {α : Type} {l : List α} (h : l.length = 2) : ∃ a b, l = [a, b] := by
  cases l with
  | nil => simp at h
  | cons a t =>
    cases t with
    | nil => simp at h
    | cons b t2 =>
      cases t2 with
      | nil => exact ⟨a, b, rfl⟩
      | cons _ _ => simp at h

lemma gate_inputs_two (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    ∃ a b, (gateAt C j).inputs = [a, b] ∧ a < n + j ∧ b < n + j := by
  have hlen : (gateAt C j).inputs.length = 2 := by
    rw [gateAt_eq_getElem C j hj]
    exact hAO.2.2 C.gates[j] (List.getElem_mem hj)
  rcases list_eq_two hlen with ⟨a, b, hab⟩
  refine ⟨a, b, hab, ?_, ?_⟩
  · exact hAO.2.1 j hj a (by simp [hab])
  · exact hAO.2.1 j hj b (by simp [hab])

lemma wireValue_and_pair (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (j a b : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.and)
    (hin : (gateAt C j).inputs = [a, b]) (x : Fin n → Bool) :
    PEqualNP.BlindGate.wireValue C n x (n + j) =
      (PEqualNP.BlindGate.wireValue C n x a && PEqualNP.BlindGate.wireValue C n x b) := by
  rw [wireValue_gate n C x j hj hRB, hop, hin]
  simp [GateOp.eval]

lemma wireValue_or_pair (n : ℕ) (C : Circuit) (hRB : ReadsBack n C)
    (j a b : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or)
    (hin : (gateAt C j).inputs = [a, b]) (x : Fin n → Bool) :
    PEqualNP.BlindGate.wireValue C n x (n + j) =
      (PEqualNP.BlindGate.wireValue C n x a || PEqualNP.BlindGate.wireValue C n x b) := by
  rw [wireValue_gate n C x j hj hRB, hop, hin]
  simp [GateOp.eval]

def keepList (p : ℕ → Bool) (m : ℕ) : List ℕ :=
  (List.range m).filter p

def rankOf (p : ℕ → Bool) (k : ℕ) : ℕ :=
  (keepList p k).length

lemma keepList_succ (p : ℕ → Bool) (m : ℕ) :
    keepList p (m + 1) = keepList p m ++ if p m then [m] else [] := by
  unfold keepList
  rw [List.range_succ, List.filter_append]
  cases hp : p m <;> simp [hp]

lemma rankOf_succ (p : ℕ → Bool) (m : ℕ) :
    rankOf p (m + 1) = rankOf p m + if p m then 1 else 0 := by
  unfold rankOf
  rw [keepList_succ, List.length_append]
  cases p m <;> simp

lemma rankOf_mono (p : ℕ → Bool) {a b : ℕ} (hab : a ≤ b) :
    rankOf p a ≤ rankOf p b := by
  induction b with
  | zero =>
    have ha : a = 0 := by omega
    subst ha
    exact le_refl _
  | succ b ih =>
    by_cases hlt : a ≤ b
    · have h1 := ih hlt
      rw [rankOf_succ]
      omega
    · have ha : a = b + 1 := by omega
      subst ha
      exact le_refl _

lemma rankOf_lt_of_lt (p : ℕ → Bool) {a b : ℕ} (hab : a < b) (ha : p a = true) :
    rankOf p a < rankOf p b := by
  have h1 : rankOf p a + 1 = rankOf p (a + 1) := by
    rw [rankOf_succ, ha]
    simp
  have h2 : rankOf p (a + 1) ≤ rankOf p b := rankOf_mono p hab
  omega

lemma keepList_getElem_props (p : ℕ → Bool) (m : ℕ) :
    ∀ k (hk : k < (keepList p m).length),
      (keepList p m)[k] < m ∧ p (keepList p m)[k] = true ∧ rankOf p (keepList p m)[k] = k := by
  induction m with
  | zero =>
    intro k hk
    simp [keepList] at hk
  | succ m ih =>
    intro k hk
    cases hpm : p m
    · have hEq : keepList p (m + 1) = keepList p m := by
        rw [keepList_succ, hpm]
        simp
      have hk' : k < (keepList p m).length := by simpa [hEq] using hk
      have h1 := ih k hk'
      have hget : (keepList p (m + 1))[k] = (keepList p m)[k] := by
        simp [hEq]
      rw [hget]
      exact ⟨by omega, h1.2.1, h1.2.2⟩
    · have hEq : keepList p (m + 1) = keepList p m ++ [m] := by
        rw [keepList_succ, hpm]
        simp
      have hk' : k < (keepList p m).length + 1 := by
        simpa [hEq] using hk
      by_cases hlt : k < (keepList p m).length
      · have h1 := ih k hlt
        have hget : (keepList p (m + 1))[k] = (keepList p m)[k] := by
          simp [hEq, List.getElem_append_left hlt]
        rw [hget]
        exact ⟨by omega, h1.2.1, h1.2.2⟩
      · have hkeq : k = (keepList p m).length := by omega
        have hget : (keepList p (m + 1))[k] = m := by
          simp [hEq, hkeq]
        rw [hget]
        exact ⟨by omega, hpm, by unfold rankOf; omega⟩

lemma keepList_getElem_rankOf (p : ℕ → Bool) (m : ℕ) :
    ∀ j < m, p j = true →
      ∃ hlt : rankOf p j < (keepList p m).length, (keepList p m)[rankOf p j] = j := by
  induction m with
  | zero =>
    intro j hj
    omega
  | succ m ih =>
    intro j hj hpj
    cases hpm : p m
    · have hEq : keepList p (m + 1) = keepList p m := by
        rw [keepList_succ, hpm]
        simp
      have hjm : j < m := by
        by_contra hge
        have : j = m := by omega
        subst this
        rw [hpm] at hpj
        cases hpj
      obtain ⟨hlt, hget⟩ := ih j hjm hpj
      refine ⟨by simpa [hEq] using hlt, ?_⟩
      simp [hEq, hget]
    · have hEq : keepList p (m + 1) = keepList p m ++ [m] := by
        rw [keepList_succ, hpm]
        simp
      by_cases hjm : j < m
      · obtain ⟨hlt, hget⟩ := ih j hjm hpj
        refine ⟨by simp [hEq]; omega, ?_⟩
        simp [hEq, List.getElem_append_left hlt, hget]
      · have hjeq : j = m := by omega
        subst hjeq
        have hr : rankOf p j = (keepList p j).length := rfl
        refine ⟨by simp [hEq, hr], ?_⟩
        simp [hEq, hr]

lemma rankOf_add_filter_card (p : ℕ → Bool) (m : ℕ) :
    rankOf p m + ((Finset.range m).filter (fun j => p j = false)).card = m := by
  induction m with
  | zero => simp [rankOf, keepList]
  | succ m ih =>
    rw [rankOf_succ, Finset.range_add_one, Finset.filter_insert]
    cases hpm : p m
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
      have hnot : m ∉ (Finset.range m).filter (fun j => p j = false) := by
        simp
      rw [Finset.card_insert_of_notMem hnot]
      omega
    · simp only [↓reduceIte, Bool.true_eq_false]
      omega

def isAndOp : GateOp → Bool
  | GateOp.and => true
  | _ => false

lemma isAndOp_eq_true_iff (op : GateOp) : isAndOp op = true ↔ op = GateOp.and := by
  cases op <;> simp [isAndOp]

def isTopAndB (n : ℕ) (C : Circuit) (j : ℕ) : Bool :=
  decide (j < C.gates.length) &&
  decide (WireBelowOutput n C (n + j)) &&
  isAndOp (gateAt C j).op &&
  (gateAt C j).inputs.all (fun u => !decide (WireBelowOutput n C u))

lemma isTopAndB_eq_true_iff (n : ℕ) (C : Circuit) (j : ℕ) :
    isTopAndB n C j = true ↔
      j < C.gates.length ∧ WireBelowOutput n C (n + j) ∧
      (gateAt C j).op = GateOp.and ∧
      ∀ u ∈ (gateAt C j).inputs, ¬ WireBelowOutput n C u := by
  unfold isTopAndB
  simp only [Bool.and_eq_true, decide_eq_true_eq, isAndOp_eq_true_iff, List.all_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, and_assoc]

lemma kept_downward_closed (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hNoIn : ∀ i < n, ¬ WireBelowOutput n C i)
    (hOr : ∀ j < C.size, ∀ (a b : ℕ),
      C.gates[j]? = some ⟨GateOp.or, [a, b]⟩ →
        (n ≤ b → WireBelowOutput n C b → WireBelowOutput n C a) ∧
        (n ≤ a → WireBelowOutput n C a → WireBelowOutput n C b))
    (j : ℕ) (hj : j < C.gates.length) (hnot : ¬ WireBelowOutput n C (n + j)) :
    ∀ u ∈ (gateAt C j).inputs, ¬ WireBelowOutput n C u := by
  obtain ⟨a, b, hab, _, _⟩ := gate_inputs_two n C hAO j hj
  have hop : (gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or := by
    rw [gateAt_eq_getElem C j hj]
    exact hAO.1 C.gates[j] (List.getElem_mem hj)
  intro u hu
  rw [hab] at hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hop with hand | hor
  · intro hwu
    apply hnot
    intro x hx
    change PEqualNP.BlindGate.wireValue C n x (n + j) = true at hx
    rw [wireValue_and_pair n C hAO.2.1 j a b hj hand hab x] at hx
    rw [Bool.and_eq_true] at hx
    rcases hu with rfl | rfl
    · exact hwu x hx.1
    · exact hwu x hx.2
  · have hget : C.gates[j]? = some ⟨GateOp.or, [a, b]⟩ := by
      rw [List.getElem?_eq_getElem hj]
      congr 1
      have h1 : C.gates[j].op = GateOp.or := by rw [← gateAt_eq_getElem C j hj]; exact hor
      have h2 : C.gates[j].inputs = [a, b] := by rw [← gateAt_eq_getElem C j hj]; exact hab
      cases hcj : C.gates[j] with
      | mk gop ginputs =>
        rw [hcj] at h1 h2
        dsimp only at h1 h2
        rw [h1, h2]
    have horj := hOr j hj a b hget
    intro hwu
    have hboth : WireBelowOutput n C a ∧ WireBelowOutput n C b := by
      rcases hu with hEq | hEq
      · rw [hEq] at hwu
        have ha_ge : n ≤ a := by
          by_contra hlt
          exact hNoIn a (by omega) hwu
        exact ⟨hwu, horj.2 ha_ge hwu⟩
      · rw [hEq] at hwu
        have hb_ge : n ≤ b := by
          by_contra hlt
          exact hNoIn b (by omega) hwu
        exact ⟨horj.1 hb_ge hwu, hwu⟩
    apply hnot
    intro x hx
    change PEqualNP.BlindGate.wireValue C n x (n + j) = true at hx
    rw [wireValue_or_pair n C hAO.2.1 j a b hj hor hab x] at hx
    rw [Bool.or_eq_true] at hx
    rcases hx with hxa | hxb
    · exact hboth.1 x hxa
    · exact hboth.2 x hxb

lemma peel_below (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hNoIn : ∀ i < n, ¬ WireBelowOutput n C i)
    (below : Finset ℕ)
    (hbelow_def : below = (Finset.range C.gates.length).filter (fun j => WireBelowOutput n C (n + j))) :
    ∀ k : ℕ, ∀ S D : Finset ℕ,
      below.card - D.card ≤ k →
      S ⊆ below →
      D ⊆ below →
      Disjoint S D →
      S.card ≤ D.card + 1 →
      (∀ x : Fin n → Bool, circuitFun n C x = true →
        ∃ j ∈ S, PEqualNP.BlindGate.wireValue C n x (n + j) = true) →
      (∀ s ∈ S, isTopAndB n C s = false → ∀ d ∈ D, s < d) →
      ∃ S' D' : Finset ℕ,
        S' ⊆ below ∧
        D' ⊆ below ∧
        Disjoint S' D' ∧
        S'.card ≤ D'.card + 1 ∧
        (∀ j ∈ S', isTopAndB n C j = true) ∧
        (∀ x : Fin n → Bool, circuitFun n C x = true →
          ∃ j ∈ S', PEqualNP.BlindGate.wireValue C n x (n + j) = true) := by
  intro k
  induction k with
  | zero =>
    intro S D hk hS hD hDisj hCard hCov hOrd
    set bad := S.filter (fun j => isTopAndB n C j = false) with hbad_def
    by_cases hEmpty : bad = ∅
    · refine ⟨S, D, hS, hD, hDisj, hCard, ?_, hCov⟩
      intro j hj
      cases ht : isTopAndB n C j with
      | true => rfl
      | false =>
        have hmem : j ∈ bad := by
          rw [hbad_def, Finset.mem_filter]
          exact ⟨hj, ht⟩
        rw [hEmpty] at hmem
        exact absurd hmem (Finset.notMem_empty j)
    · have hne : bad.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
      obtain ⟨m, hm⟩ := hne
      rw [hbad_def, Finset.mem_filter] at hm
      have hmB : m ∈ below := hS hm.1
      have hmNotD : m ∉ D := Finset.disjoint_left.mp hDisj hm.1
      have hDlt : D.card < below.card := by
        have hsub : insert m D ⊆ below := Finset.insert_subset hmB hD
        have h1 := Finset.card_le_card hsub
        rw [Finset.card_insert_of_notMem hmNotD] at h1
        omega
      omega
  | succ k ih =>
    intro S D hk hS hD hDisj hCard hCov hOrd
    set bad := S.filter (fun j => isTopAndB n C j = false) with hbad_def
    by_cases hEmpty : bad = ∅
    · refine ⟨S, D, hS, hD, hDisj, hCard, ?_, hCov⟩
      intro j hj
      cases ht : isTopAndB n C j with
      | true => rfl
      | false =>
        have hmem : j ∈ bad := by
          rw [hbad_def, Finset.mem_filter]
          exact ⟨hj, ht⟩
        rw [hEmpty] at hmem
        exact absurd hmem (Finset.notMem_empty j)
    · have hne : bad.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEmpty
      set m := bad.max' hne with hm_def
      have hm_bad : m ∈ bad := Finset.max'_mem bad hne
      rw [hbad_def, Finset.mem_filter] at hm_bad
      have hmS : m ∈ S := hm_bad.1
      have hmFalse : isTopAndB n C m = false := hm_bad.2
      have hmB : m ∈ below := hS hmS
      have hmNotD : m ∉ D := Finset.disjoint_left.mp hDisj hmS
      have hmProps : m < C.gates.length ∧ WireBelowOutput n C (n + m) := by
        rw [hbelow_def, Finset.mem_filter, Finset.mem_range] at hmB
        exact hmB
      have hm_lt_D : ∀ d ∈ D, m < d := hOrd m hmS hmFalse
      have hD'_card : (insert m D).card = D.card + 1 := Finset.card_insert_of_notMem hmNotD
      have hD'_sub : insert m D ⊆ below := Finset.insert_subset hmB hD
      have hk' : below.card - (insert m D).card ≤ k := by
        have hle := Finset.card_le_card hD'_sub
        omega
      obtain ⟨a, b, hab, ha_lt, hb_lt⟩ := gate_inputs_two n C hAO m hmProps.1
      have hop : (gateAt C m).op = GateOp.and ∨ (gateAt C m).op = GateOp.or := by
        rw [gateAt_eq_getElem C m hmProps.1]
        exact hAO.1 C.gates[m] (List.getElem_mem hmProps.1)
      rcases hop with hand | hor
      · have hex : ∃ u ∈ (gateAt C m).inputs, WireBelowOutput n C u := by
          by_contra hall
          push Not at hall
          have htrue : isTopAndB n C m = true := by
            rw [isTopAndB_eq_true_iff]
            exact ⟨hmProps.1, hmProps.2, hand, hall⟩
          rw [hmFalse] at htrue
          cases htrue
        obtain ⟨u, hu_mem, hu_below⟩ := hex
        have hu_lt : u < n + m := hAO.2.1 m hmProps.1 u hu_mem
        have hu_ge : n ≤ u := by
          by_contra hlt
          exact hNoIn u (by omega) hu_below
        set ju := u - n with hju_def
        have hju_lt : ju < m := by omega
        have hju_eq : n + ju = u := by omega
        have hjuB : ju ∈ below := by
          rw [hbelow_def, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, by rw [hju_eq]; exact hu_below⟩
        set S1 := insert ju (S.erase m) with hS1_def
        set D1 := insert m D with hD1_def
        apply ih S1 D1 hk'
        · intro s hs
          simp only [hS1_def, Finset.mem_insert, Finset.mem_erase] at hs
          rcases hs with rfl | ⟨_, hsS⟩
          · exact hjuB
          · exact hS hsS
        · exact hD'_sub
        · rw [Finset.disjoint_left]
          intro s hs hsD1
          simp only [hD1_def, Finset.mem_insert] at hsD1
          simp only [hS1_def, Finset.mem_insert, Finset.mem_erase] at hs
          rcases hs with hEqs | ⟨hne_m, hsS⟩
          · rcases hsD1 with hEqm | hdD
            · omega
            · have hlt_d := hm_lt_D s hdD
              omega
          · rcases hsD1 with hEqm | hdD
            · exact hne_m hEqm
            · exact Finset.disjoint_left.mp hDisj hsS hdD
        · have h1 : S1.card ≤ (S.erase m).card + 1 := Finset.card_insert_le ju (S.erase m)
          have h2 : (S.erase m).card = S.card - 1 := Finset.card_erase_of_mem hmS
          have h3 : 1 ≤ S.card := Finset.one_le_card.mpr ⟨m, hmS⟩
          rw [hD1_def, hD'_card]
          omega
        · intro x hfx
          obtain ⟨j, hjS, hjx⟩ := hCov x hfx
          by_cases hjm : j = m
          · rw [hjm] at hjx
            refine ⟨ju, ?_, ?_⟩
            · simp [hS1_def]
            · rw [hju_eq]
              rw [wireValue_and_pair n C hAO.2.1 m a b hmProps.1 hand hab x] at hjx
              rw [Bool.and_eq_true] at hjx
              rw [hab] at hu_mem
              simp only [List.mem_cons, List.not_mem_nil, or_false] at hu_mem
              rcases hu_mem with rfl | rfl
              · exact hjx.1
              · exact hjx.2
          · exact ⟨j, by simp [hS1_def, hjm, hjS], hjx⟩
        · intro s hs hsFalse d hd
          have hm_le_d : m ≤ d := by
            simp only [hD1_def, Finset.mem_insert] at hd
            rcases hd with hEqm | hdD
            · omega
            · have := hm_lt_D d hdD; omega
          simp only [hS1_def, Finset.mem_insert, Finset.mem_erase] at hs
          rcases hs with hEqs | ⟨hne_m, hsS⟩
          · omega
          · have hs_bad : s ∈ bad := by
              rw [hbad_def, Finset.mem_filter]
              exact ⟨hsS, hsFalse⟩
            have hs_le : s ≤ m := Finset.le_max' bad s hs_bad
            omega
      · have ha_below : WireBelowOutput n C a := by
          intro x hxa
          apply hmProps.2 x
          change PEqualNP.BlindGate.wireValue C n x (n + m) = true
          change PEqualNP.BlindGate.wireValue C n x a = true at hxa
          rw [wireValue_or_pair n C hAO.2.1 m a b hmProps.1 hor hab x, hxa]
          simp
        have hb_below : WireBelowOutput n C b := by
          intro x hxb
          apply hmProps.2 x
          change PEqualNP.BlindGate.wireValue C n x (n + m) = true
          change PEqualNP.BlindGate.wireValue C n x b = true at hxb
          rw [wireValue_or_pair n C hAO.2.1 m a b hmProps.1 hor hab x, hxb]
          simp
        have ha_ge : n ≤ a := by
          by_contra hlt
          exact hNoIn a (by omega) ha_below
        have hb_ge : n ≤ b := by
          by_contra hlt
          exact hNoIn b (by omega) hb_below
        set ja := a - n with hja_def
        set jb := b - n with hjb_def
        have hja_lt : ja < m := by omega
        have hjb_lt : jb < m := by omega
        have hja_eq : n + ja = a := by omega
        have hjb_eq : n + jb = b := by omega
        have hjaB : ja ∈ below := by
          rw [hbelow_def, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, by rw [hja_eq]; exact ha_below⟩
        have hjbB : jb ∈ below := by
          rw [hbelow_def, Finset.mem_filter, Finset.mem_range]
          exact ⟨by omega, by rw [hjb_eq]; exact hb_below⟩
        set S1 := insert ja (insert jb (S.erase m)) with hS1_def
        set D1 := insert m D with hD1_def
        apply ih S1 D1 hk'
        · intro s hs
          simp only [hS1_def, Finset.mem_insert, Finset.mem_erase] at hs
          rcases hs with rfl | rfl | ⟨_, hsS⟩
          · exact hjaB
          · exact hjbB
          · exact hS hsS
        · exact hD'_sub
        · rw [Finset.disjoint_left]
          intro s hs hsD1
          simp only [hD1_def, Finset.mem_insert] at hsD1
          simp only [hS1_def, Finset.mem_insert, Finset.mem_erase] at hs
          rcases hs with hEqa | hEqb | ⟨hne_m, hsS⟩
          · rcases hsD1 with hEqm | hdD
            · omega
            · have hlt_d := hm_lt_D s hdD; omega
          · rcases hsD1 with hEqm | hdD
            · omega
            · have hlt_d := hm_lt_D s hdD; omega
          · rcases hsD1 with hEqm | hdD
            · exact hne_m hEqm
            · exact Finset.disjoint_left.mp hDisj hsS hdD
        · have h1 : S1.card ≤ (insert jb (S.erase m)).card + 1 :=
            Finset.card_insert_le ja (insert jb (S.erase m))
          have h2 : (insert jb (S.erase m)).card ≤ (S.erase m).card + 1 :=
            Finset.card_insert_le jb (S.erase m)
          have h3 : (S.erase m).card = S.card - 1 := Finset.card_erase_of_mem hmS
          have h4 : 1 ≤ S.card := Finset.one_le_card.mpr ⟨m, hmS⟩
          rw [hD1_def, hD'_card]
          omega
        · intro x hfx
          obtain ⟨j, hjS, hjx⟩ := hCov x hfx
          by_cases hjm : j = m
          · rw [hjm] at hjx
            rw [wireValue_or_pair n C hAO.2.1 m a b hmProps.1 hor hab x] at hjx
            rw [Bool.or_eq_true] at hjx
            rcases hjx with hxa | hxb
            · exact ⟨ja, by simp [hS1_def], by rw [hja_eq]; exact hxa⟩
            · exact ⟨jb, by simp [hS1_def], by rw [hjb_eq]; exact hxb⟩
          · exact ⟨j, by simp [hS1_def, hjm, hjS], hjx⟩
        · intro s hs hsFalse d hd
          have hm_le_d : m ≤ d := by
            simp only [hD1_def, Finset.mem_insert] at hd
            rcases hd with hEqm | hdD
            · omega
            · have := hm_lt_D d hdD; omega
          simp only [hS1_def, Finset.mem_insert, Finset.mem_erase] at hs
          rcases hs with hEqa | hEqb | ⟨hne_m, hsS⟩
          · omega
          · omega
          · have hs_bad : s ∈ bad := by
              rw [hbad_def, Finset.mem_filter]
              exact ⟨hsS, hsFalse⟩
            have hs_le : s ≤ m := Finset.le_max' bad s hs_bad
            omega

lemma main_proof (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hOut : C.output < n + C.size)
    (hNoIn : ∀ i < n, ¬ WireBelowOutput n C i)
    (hOr : ∀ j < C.size, ∀ (a b : ℕ),
      C.gates[j]? = some ⟨GateOp.or, [a, b]⟩ →
        (n ≤ b → WireBelowOutput n C b → WireBelowOutput n C a) ∧
        (n ≤ a → WireBelowOutput n C a → WireBelowOutput n C b)) :
    ∃ (C' : Circuit) (pairs : List (ℕ × ℕ)),
      IsAO2 n C' ∧
      (∀ k < C'.size, ∃ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue C' n x (n + k) = true ∧ circuitFun n C x = false) ∧
      (∀ x : Fin n → Bool, circuitFun n C x = true ↔
        ∃ p ∈ pairs, PEqualNP.BlindGate.wireValue C' n x p.1 = true ∧
          PEqualNP.BlindGate.wireValue C' n x p.2 = true) ∧
      C'.size + 2 * pairs.length ≤ C.size + 1 := by
  let keepB : ℕ → Bool := fun j => !decide (WireBelowOutput n C (n + j))
  have hkeepB_true : ∀ j, keepB j = true ↔ ¬ WireBelowOutput n C (n + j) := by
    intro j
    simp [keepB]
  have hkeepB_false : ∀ j, keepB j = false ↔ WireBelowOutput n C (n + j) := by
    intro j
    simp [keepB]
  let wmap : ℕ → ℕ := fun w => if w < n then w else n + rankOf keepB (w - n)
  let kl := keepList keepB C.gates.length
  let C' : Circuit :=
    { gates := kl.map (fun j => ⟨(gateAt C j).op, (gateAt C j).inputs.map wmap⟩)
      output := 0 }
  have hC'_len : C'.gates.length = kl.length := by
    simp [C']
  have hDC : ∀ j < C.gates.length, keepB j = true →
      ∀ u ∈ (gateAt C j).inputs, ¬ WireBelowOutput n C u := by
    intro j hj hkj u hu
    exact kept_downward_closed n C hAO hNoIn hOr j hj ((hkeepB_true j).mp hkj) u hu
  have hC'_gateAt : ∀ k (hk : k < kl.length),
      gateAt C' k = ⟨(gateAt C kl[k]).op, (gateAt C kl[k]).inputs.map wmap⟩ := by
    intro k hk
    have hk' : k < C'.gates.length := by rw [hC'_len]; exact hk
    rw [gateAt_eq_getElem C' k hk']
    simp [C']
  have hC'_AO : IsAO2 n C' := by
    refine ⟨?_, ?_, ?_⟩
    · intro g hg
      simp only [C', List.mem_map] at hg
      obtain ⟨j, hj, rfl⟩ := hg
      have hj_lt : j < C.gates.length := by
        simp only [kl, keepList, List.mem_filter, List.mem_range] at hj
        exact hj.1
      rw [gateAt_eq_getElem C j hj_lt]
      exact hAO.1 C.gates[j] (List.getElem_mem hj_lt)
    · intro k hk w' hw'
      have hk_kl : k < kl.length := by rw [← hC'_len]; exact hk
      rw [hC'_gateAt k hk_kl] at hw'
      simp only [List.mem_map] at hw'
      obtain ⟨u, hu, rfl⟩ := hw'
      have hprops := keepList_getElem_props keepB C.gates.length k hk_kl
      have hj_lt : kl[k] < C.gates.length := hprops.1
      have hj_keep : keepB kl[k] = true := hprops.2.1
      have hj_rank : rankOf keepB kl[k] = k := hprops.2.2
      have hu_lt : u < n + kl[k] := hAO.2.1 kl[k] hj_lt u hu
      have hu_not : ¬ WireBelowOutput n C u := hDC kl[k] hj_lt hj_keep u hu
      by_cases hun : u < n
      · simp only [wmap, hun, ↓reduceIte]
        omega
      · simp only [wmap, hun, ↓reduceIte]
        have hku_true : keepB (u - n) = true := by
          rw [hkeepB_true]
          have heq : n + (u - n) = u := by omega
          rw [heq]
          exact hu_not
        have hlt_r : rankOf keepB (u - n) < rankOf keepB kl[k] :=
          rankOf_lt_of_lt keepB (by omega) hku_true
        omega
    · intro g hg
      simp only [C', List.mem_map] at hg
      obtain ⟨j, hj, rfl⟩ := hg
      have hj_lt : j < C.gates.length := by
        simp only [kl, keepList, List.mem_filter, List.mem_range] at hj
        exact hj.1
      simp only [List.length_map]
      rw [gateAt_eq_getElem C j hj_lt]
      exact hAO.2.2 C.gates[j] (List.getElem_mem hj_lt)
  have hWireEq : ∀ w < n + C.gates.length, ¬ WireBelowOutput n C w →
      ∀ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue C' n x (wmap w) = PEqualNP.BlindGate.wireValue C n x w := by
    intro w
    induction w using Nat.strong_induction_on with
    | ind w ih =>
      intro hw hnot x
      by_cases hwn : w < n
      · simp only [wmap, hwn, ↓reduceIte]
        rw [wireValue_input n C' x w hwn, wireValue_input n C x w hwn]
      · simp only [wmap, hwn, ↓reduceIte]
        set j := w - n with hj_def
        have hw_eq : n + j = w := by omega
        have hj_lt : j < C.gates.length := by omega
        have hj_keep : keepB j = true := by
          rw [hkeepB_true, hw_eq]
          exact hnot
        obtain ⟨hr_lt, hr_get⟩ := keepList_getElem_rankOf keepB C.gates.length j hj_lt hj_keep
        have hr_lt' : rankOf keepB j < C'.gates.length := by rw [hC'_len]; exact hr_lt
        rw [wireValue_gate n C' x (rankOf keepB j) hr_lt' hC'_AO.2.1]
        rw [hC'_gateAt (rankOf keepB j) hr_lt, hr_get]
        rw [← hw_eq, wireValue_gate n C x j hj_lt hAO.2.1]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro u hu
        have hu_lt : u < n + j := hAO.2.1 j hj_lt u hu
        have hu_not : ¬ WireBelowOutput n C u := hDC j hj_lt hj_keep u hu
        exact ih u (by omega) (by omega) hu_not x
  have hC'_dirty : ∀ k < C'.size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue C' n x (n + k) = true ∧ circuitFun n C x = false := by
    intro k hk
    have hk_kl : k < kl.length := by
      change k < C'.gates.length at hk
      rw [← hC'_len]; exact hk
    have hprops := keepList_getElem_props keepB C.gates.length k hk_kl
    have hj_lt : kl[k] < C.gates.length := hprops.1
    have hj_not : ¬ WireBelowOutput n C (n + kl[k]) := (hkeepB_true kl[k]).mp hprops.2.1
    have hj_rank : rankOf keepB kl[k] = k := hprops.2.2
    have hex : ∃ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue C n x (n + kl[k]) = true ∧ circuitFun n C x = false := by
      by_contra hno
      apply hj_not
      intro x hx
      cases hcx : circuitFun n C x with
      | true => exact hcx
      | false => exact absurd ⟨x, hx, hcx⟩ hno
    obtain ⟨x, hx1, hx2⟩ := hex
    refine ⟨x, ?_, hx2⟩
    have hweq := hWireEq (n + kl[k]) (by omega) hj_not x
    have hwm : wmap (n + kl[k]) = n + k := by
      have hge : ¬ (n + kl[k] < n) := by omega
      simp only [wmap, hge, ↓reduceIte, Nat.add_sub_cancel_left, hj_rank]
    rw [← hwm, hweq]
    exact hx1
  set below := (Finset.range C.gates.length).filter (fun j => WireBelowOutput n C (n + j)) with hbelow_def
  have hOut_below : WireBelowOutput n C C.output := fun _ hx => hx
  have hOut_ge : n ≤ C.output := by
    by_contra hlt
    exact hNoIn C.output (by omega) hOut_below
  set jOut := C.output - n with hjOut_def
  have hjOut_eq : n + jOut = C.output := by omega
  have hjOut_lt : jOut < C.gates.length := by
    change C.output < n + C.gates.length at hOut
    omega
  have hjOut_mem : jOut ∈ below := by
    rw [hbelow_def, Finset.mem_filter, Finset.mem_range]
    exact ⟨hjOut_lt, by rw [hjOut_eq]; exact hOut_below⟩
  obtain ⟨S, D, hS_sub, hD_sub, hDisj, hCard, hS_top, hCov⟩ :=
    peel_below n C hAO hNoIn below hbelow_def below.card {jOut} ∅ (by simp)
      (Finset.singleton_subset_iff.mpr hjOut_mem) (Finset.empty_subset _)
      (Finset.disjoint_empty_right _) (by simp)
      (fun x hfx => ⟨jOut, Finset.mem_singleton_self jOut, by rw [hjOut_eq]; exact hfx⟩)
      (fun _ _ _ _ hd => absurd hd (Finset.notMem_empty _))
  let pairs : List (ℕ × ℕ) := S.toList.map (fun j => (wmap (opnd C j 0), wmap (opnd C j 1)))
  refine ⟨C', pairs, hC'_AO, hC'_dirty, ?_, ?_⟩
  · intro x
    constructor
    · intro hfx
      obtain ⟨j, hjS, hjx⟩ := hCov x hfx
      have htop := (isTopAndB_eq_true_iff n C j).mp (hS_top j hjS)
      obtain ⟨a, b, hab, ha_lt, hb_lt⟩ := gate_inputs_two n C hAO j htop.1
      have ha_not : ¬ WireBelowOutput n C a := htop.2.2.2 a (by simp [hab])
      have hb_not : ¬ WireBelowOutput n C b := htop.2.2.2 b (by simp [hab])
      have hop0 : opnd C j 0 = a := by simp [opnd, hab]
      have hop1 : opnd C j 1 = b := by simp [opnd, hab]
      rw [wireValue_and_pair n C hAO.2.1 j a b htop.1 htop.2.2.1 hab x, Bool.and_eq_true] at hjx
      refine ⟨(wmap a, wmap b), ?_, ?_, ?_⟩
      · simp only [pairs, List.mem_map, Finset.mem_toList]
        exact ⟨j, hjS, by rw [hop0, hop1]⟩
      · rw [hWireEq a (by omega) ha_not x]; exact hjx.1
      · rw [hWireEq b (by omega) hb_not x]; exact hjx.2
    · rintro ⟨p, hp, hp1, hp2⟩
      simp only [pairs, List.mem_map, Finset.mem_toList] at hp
      obtain ⟨j, hjS, rfl⟩ := hp
      have htop := (isTopAndB_eq_true_iff n C j).mp (hS_top j hjS)
      obtain ⟨a, b, hab, ha_lt, hb_lt⟩ := gate_inputs_two n C hAO j htop.1
      have ha_not : ¬ WireBelowOutput n C a := htop.2.2.2 a (by simp [hab])
      have hb_not : ¬ WireBelowOutput n C b := htop.2.2.2 b (by simp [hab])
      have hop0 : opnd C j 0 = a := by simp [opnd, hab]
      have hop1 : opnd C j 1 = b := by simp [opnd, hab]
      dsimp only at hp1 hp2
      rw [hop0] at hp1
      rw [hop1] at hp2
      rw [hWireEq a (by omega) ha_not x] at hp1
      rw [hWireEq b (by omega) hb_not x] at hp2
      apply htop.2.1 x
      change PEqualNP.BlindGate.wireValue C n x (n + j) = true
      rw [wireValue_and_pair n C hAO.2.1 j a b htop.1 htop.2.2.1 hab x, hp1, hp2]
      rfl
  · have hpair_len : pairs.length = S.card := by
      simp [pairs]
    have hSD_le : S.card + D.card ≤ below.card := by
      rw [← Finset.card_union_of_disjoint hDisj]
      exact Finset.card_le_card (Finset.union_subset hS_sub hD_sub)
    have hbelow_eq : below = (Finset.range C.gates.length).filter (fun j => keepB j = false) := by
      ext j
      simp [hbelow_def, hkeepB_false]
    have hsum_size : C'.size + below.card = C.size := by
      have h1 := rankOf_add_filter_card keepB C.gates.length
      rw [← hbelow_eq] at h1
      change C'.gates.length + below.card = C.gates.length
      rw [hC'_len]
      exact h1
    omega


lemma main :
    ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output < x1 + x2.size → (∀ x5 < x1, ¬PEqualNP.CircuitMoves.WireBelowOutput x1 x2 x5) → (∀ x6 < x2.size, ∀ (x8 x9 : ℕ), x2.gates[x6]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x8, x9] : PEqualNP.CircuitLowerBounds.Gate } → (x1 ≤ x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x2 x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x2 x8) ∧ (x1 ≤ x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x2 x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x2 x9)) → ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : List (ℕ × ℕ)), PEqualNP.TopForm.IsAO2 x1 x7 ∧ (∀ x9 < x7.size, ∃ (x11 : Fin x1 → Bool), PEqualNP.BlindGate.wireValue x7 x1 x11 (x1 + x9) = Bool.true ∧ PEqualNP.MetaComplexity.circuitFun x1 x2 x11 = Bool.false) ∧ (∀ (x9 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x2 x9 = Bool.true ↔ ∃ x10 ∈ x8, PEqualNP.BlindGate.wireValue x7 x1 x9 x10.1 = Bool.true ∧ PEqualNP.BlindGate.wireValue x7 x1 x9 x10.2 = Bool.true) ∧ x7.size + (2 : ℕ) * x8.length ≤ x2.size + (1 : ℕ) :=
  PEqualNP.Outside.L_meta_2583.SplitAux.main_proof

end SplitAux

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.MetaComplexity
  PEqualNP.TopForm

lemma lift_preserves (n : ℕ) (C C' : Circuit) (hAO : IsAO2 n C)
    (hout : C.output < n + C.gates.length) (hL : Lift n C C') :
    IsAO2 n C' ∧ C'.output < n + C'.gates.length ∧ C'.size = C.size ∧
      circuitFun n C' = circuitFun n C := by
  rcases hL with ⟨m, hm, p, hp, h, hh, hnh, hgm, hB, rfl⟩
  refine ⟨LiftAux.liftAt_isAO2 n C m p h hAO hout hm hp hh, ?_, ?_, ?_⟩
  · simp only [liftAt, List.length_append, List.length_singleton]
    omega
  · exact LiftAux.liftAt_gates_length n C m p h hm
  · funext x
    exact LiftAux.liftAt_eval_eq n C m p h hAO hout hm hp hh hgm hB x

lemma product_decomposition (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hout : C.output < n + C.size)
    (hinputs : ∀ w < n, ¬ WireBelowOutput n C w) :
    ∃ (D : Circuit) (B : List (ℕ × ℕ)), IsAO2 n D ∧
      (∀ j < D.size, ∃ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue D n x (n + j) = true ∧ circuitFun n C x = false) ∧
      (∀ x : Fin n → Bool, circuitFun n C x = true ↔ ∃ t ∈ B,
        PEqualNP.BlindGate.wireValue D n x t.1 = true ∧
        PEqualNP.BlindGate.wireValue D n x t.2 = true) ∧
      D.size + 2 * B.length ≤ C.size + 1 := by
  obtain ⟨C', hR, hNF⟩ := LiftAux.main n C hAO hout
  have hinv : ∀ E : Circuit, Relation.ReflTransGen (Lift n) C E →
      IsAO2 n E ∧ E.output < n + E.gates.length ∧ E.size = C.size ∧
        circuitFun n E = circuitFun n C := by
    intro E hR'
    induction hR' with
    | refl => exact ⟨hAO, hout, rfl, rfl⟩
    | tail _ hL ih =>
      obtain ⟨a, b, c, d⟩ := ih
      obtain ⟨a', b', c', d'⟩ := lift_preserves n _ _ a b hL
      exact ⟨a', b', c'.trans c, d'.trans d⟩
  obtain ⟨hAO', hout', hsize, hfun⟩ := hinv C' hR
  have hinputs' : ∀ w < n, ¬ WireBelowOutput n C' w := by
    intro w hw hb
    apply hinputs w hw
    intro x hx
    change circuitFun n C x = true
    rw [← hfun]
    apply hb x
    change PEqualNP.BlindGate.wireValue C' n x w = true
    rw [SplitAux.wireValue_input n C' x w hw]
    change PEqualNP.BlindGate.wireValue C n x w = true at hx
    rwa [SplitAux.wireValue_input n C x w hw] at hx
  obtain ⟨D, B, hD, hnot, hFn, hCost⟩ := SplitAux.main n C' hAO' hout' hinputs' hNF
  refine ⟨D, B, hD, ?_, ?_, ?_⟩
  · intro j hj
    obtain ⟨x, hx, hfalse⟩ := hnot j hj
    exact ⟨x, hx, by rwa [hfun] at hfalse⟩
  · intro x
    simpa only [hfun] using hFn x
  · simpa only [hsize] using hCost

lemma incidence_no_input_below (p l : ℕ) (I : Fin p → Fin l → Prop) [DecidableRel I]
    (C : Circuit)
    (hF : ∀ z : Fin (p + l) → Bool, circuitFun (p + l) C z =
      decide (∃ a b, I a b ∧ z (Fin.castAdd l a) = true ∧ z (Fin.natAdd p b) = true)) :
    ∀ w < p + l, ¬ WireBelowOutput (p + l) C w := by
  intro w hw hb
  let x : Fin (p + l) → Bool := fun i => decide (i.val = w)
  have hx : PEqualNP.BlindGate.wireValue C (p + l) x w = true := by
    rw [SplitAux.wireValue_input (p + l) C x w hw]
    simp [x]
  have hyes : circuitFun (p + l) C x = true := hb x hx
  have hno : ¬ ∃ a b, I a b ∧ x (Fin.castAdd l a) = true ∧ x (Fin.natAdd p b) = true := by
    rintro ⟨a, b, _, ha, hb⟩
    simp only [x, decide_eq_true_eq, Fin.val_castAdd, Fin.val_natAdd] at ha hb
    have := a.isLt
    omega
  rw [hF, decide_eq_false hno] at hyes
  cases hyes

lemma incidence_output_valid (p l : ℕ) (I : Fin p → Fin l → Prop) [DecidableRel I]
    (C : Circuit) (hne : ∃ a b, I a b)
    (hF : ∀ z : Fin (p + l) → Bool, circuitFun (p + l) C z =
      decide (∃ a b, I a b ∧ z (Fin.castAdd l a) = true ∧ z (Fin.natAdd p b) = true)) :
    C.output < p + l + C.size := by
  by_contra hout
  have hyes : circuitFun (p + l) C (fun _ => true) = true := by
    rw [hF]
    apply decide_eq_true
    obtain ⟨a, b, hab⟩ := hne
    exact ⟨a, b, hab, rfl, rfl⟩
  have hzero : circuitFun (p + l) C (fun _ => true) = false := by
    unfold circuitFun Circuit.eval Circuit.wires
    change (C.gates.foldl SplitAux.wireStep (List.ofFn (fun _ : Fin (p + l) => true))).getD
      C.output false = false
    apply List.getD_eq_default
    rw [SplitAux.foldl_wireStep_length, List.length_ofFn]
    exact Nat.le_of_not_gt hout
  rw [hzero] at hyes
  cases hyes

lemma incidence_product_decomposition (p l : ℕ) (I : Fin p → Fin l → Prop)
    [DecidableRel I] (C : Circuit) (hAO : IsAO2 (p + l) C) (hne : ∃ a b, I a b)
    (hF : ∀ z : Fin (p + l) → Bool, circuitFun (p + l) C z =
      decide (∃ a b, I a b ∧ z (Fin.castAdd l a) = true ∧ z (Fin.natAdd p b) = true)) :
    ∃ (D : Circuit) (B : List (ℕ × ℕ)), IsAO2 (p + l) D ∧
      (∀ j < D.size, ∃ x : Fin (p + l) → Bool,
        PEqualNP.BlindGate.wireValue D (p + l) x (p + l + j) = true ∧
        circuitFun (p + l) C x = false) ∧
      (∀ x : Fin (p + l) → Bool, circuitFun (p + l) C x = true ↔ ∃ t ∈ B,
        PEqualNP.BlindGate.wireValue D (p + l) x t.1 = true ∧
        PEqualNP.BlindGate.wireValue D (p + l) x t.2 = true) ∧
      D.size + 2 * B.length ≤ C.size + 1 :=
  product_decomposition (p + l) C hAO (incidence_output_valid p l I C hne hF)
    (incidence_no_input_below p l I C hF)

lemma plane_product_decomposition :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true)) →
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
        ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) ∧
      ∃ (D : Circuit) (B : List (ℕ × ℕ)), IsAO2 (N + N) D ∧
        (∀ j < D.size, ∃ x : Fin (N + N) → Bool,
          PEqualNP.BlindGate.wireValue D (N + N) x (N + N + j) = true ∧
          circuitFun (N + N) C x = false) ∧
        (∀ x : Fin (N + N) → Bool, circuitFun (N + N) C x = true ↔ ∃ t ∈ B,
          PEqualNP.BlindGate.wireValue D (N + N) x t.1 = true ∧
          PEqualNP.BlindGate.wireValue D (N + N) x t.2 = true) ∧
        D.size + 2 * B.length ≤ C.size + 1 := by
  intro q N I inst C hq hN hlines huniq hAO hF
  have hNpos : 0 < N := by omega
  let l0 : Fin N := ⟨0, hNpos⟩
  have hpoints : (Finset.univ.filter (fun p => I p l0)).Nonempty := by
    apply Finset.card_pos.mp
    rw [hlines l0]
    omega
  obtain ⟨p0, hp0⟩ := hpoints
  have hne : ∃ p l : Fin N, I p l := ⟨p0, l0, (Finset.mem_filter.mp hp0).2⟩
  refine ⟨?_, incidence_product_decomposition N N I C hAO hne hF⟩
  intro p p' l l' hpp hll hfour
  obtain ⟨k, hk, hku⟩ := huniq p p' hpp
  have hl : l = k := hku l ⟨hfour.1, hfour.2.2.1⟩
  have hl' : l' = k := hku l' ⟨hfour.2.1, hfour.2.2.2⟩
  exact hll (hl.trans hl'.symm)

namespace Geometry

lemma exists_line_avoiding_small_set
    {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (huniq : ∀ p p' : Fin P, p ≠ p' →
      ∀ l l' : Fin L, I p l → I p' l → I p l' → I p' l' → l = l')
    (S : Finset (Fin P)) (p : Fin P) (hp : p ∉ S)
    (hsize : S.card < (Finset.univ.filter (I p)).card) :
    ∃ l : Fin L, I p l ∧ ∀ s ∈ S, ¬ I s l := by
  classical
  by_contra hnone
  let overlaps : Fin P → Finset (Fin L) :=
    fun s => Finset.univ.filter (fun l => I p l ∧ I s l)
  have hoverlap : ∀ s ∈ S, (overlaps s).card ≤ 1 := by
    intro s hs
    apply Finset.card_le_one.mpr
    intro l hl l' hl'
    have hps : p ≠ s := by intro h; exact hp (h ▸ hs)
    have h1 := (Finset.mem_filter.mp hl).2
    have h2 := (Finset.mem_filter.mp hl').2
    exact huniq p s hps l l' h1.1 h1.2 h2.1 h2.2
  have hcover : Finset.univ.filter (I p) ⊆ S.biUnion overlaps := by
    intro l hl
    have hit : I p l := (Finset.mem_filter.mp hl).2
    have hex : ∃ s ∈ S, I s l := by
      by_contra h
      exact hnone ⟨l, hit, fun s hs his => h ⟨s, hs, his⟩⟩
    obtain ⟨s, hs, his⟩ := hex
    exact Finset.mem_biUnion.mpr ⟨s, hs, by simp [overlaps, hit, his]⟩
  have bound : (Finset.univ.filter (I p)).card ≤ S.card := calc
    _ ≤ (S.biUnion overlaps).card := Finset.card_le_card hcover
    _ ≤ ∑ s ∈ S, (overlaps s).card := Finset.card_biUnion_le
    _ ≤ ∑ s ∈ S, 1 := Finset.sum_le_sum hoverlap
    _ = S.card := by simp
  exact (Nat.not_le_of_gt hsize) bound

lemma avoiding_sets_injective
    {P L k : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (huniq : ∀ p p' : Fin P, p ≠ p' →
      ∀ l l' : Fin L, I p l → I p' l → I p l' → I p' l' → l = l')
    (hdeg : ∀ p : Fin P, k < (Finset.univ.filter (I p)).card)
    (S T : Finset (Fin P)) (hS : S.card ≤ k) (hT : T.card ≤ k)
    (heq : (Finset.univ.filter (fun l => ∀ p ∈ S, ¬ I p l)) =
      Finset.univ.filter (fun l => ∀ p ∈ T, ¬ I p l)) : S = T := by
  classical
  have sub : ∀ A B : Finset (Fin P), A.card ≤ k → B.card ≤ k →
      (Finset.univ.filter (fun l => ∀ p ∈ A, ¬ I p l)) =
        Finset.univ.filter (fun l => ∀ p ∈ B, ¬ I p l) → A ⊆ B := by
    intro A B hA hB hAB p hp
    by_contra hpB
    obtain ⟨l, hpl, hl⟩ := exists_line_avoiding_small_set I huniq B p hpB
      (lt_of_le_of_lt hB (hdeg p))
    have hm : l ∈ Finset.univ.filter (fun l => ∀ p ∈ B, ¬ I p l) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ l, hl⟩
    rw [← hAB] at hm
    exact (Finset.mem_filter.mp hm).2 p hp hpl
  exact Finset.Subset.antisymm (sub S T hS hT heq) (sub T S hT hS heq.symm)

end Geometry

namespace SharedBlock

def sharedJ (a b x : Bool) : Bool := (a || b) && (a || x)

def sharedBlock (a b x y : Bool) : Bool := sharedJ a b x && (x || y)

lemma sharedJ_eq (a b x : Bool) : sharedJ a b x = (a || (b && x)) := by
  cases a <;> cases b <;> cases x <;> rfl

lemma sharedBlock_eq (a b x y : Bool) :
    sharedBlock a b x y = ((a && (x || y)) || (b && x)) := by
  cases a <;> cases b <;> cases x <;> cases y <;> rfl

lemma sharedBlock_edge_eq (a b x y : Bool) :
    sharedBlock a b x y = (((a && x) || (a && y)) || (b && x)) := by
  cases a <;> cases b <;> cases x <;> cases y <;> rfl

lemma sharedUnion_eq (a b x y z : Bool) :
    (sharedBlock a b x y || sharedBlock a b x z) =
      ((a && ((x || y) || z)) || (b && x)) := by
  cases a <;> cases b <;> cases x <;> cases y <;> cases z <;> rfl

lemma sharedJ_not_below : sharedJ true false false = true ∧
    ((true && (false || false)) || (false && false)) = false := by
  decide

lemma sharedBlock_pair_ax : sharedBlock true false true false = true := rfl

lemma sharedBlock_pair_ay : sharedBlock true false false true = true := rfl

lemma sharedBlock_pair_bx : sharedBlock false true true false = true := rfl

lemma sharedBlock_pair_by : sharedBlock false true false true = false := rfl

lemma sharedBlock_safe (a b x y : Bool) (h : sharedBlock a b x y = true) :
    (a = true ∧ x = true) ∨ (a = true ∧ y = true) ∨ (b = true ∧ x = true) := by
  cases a <;> cases b <;> cases x <;> cases y <;> simp_all [sharedBlock, sharedJ]

open PEqualNP.CircuitLowerBounds

def sharedCircuit : Circuit :=
  ⟨[⟨.or, [0, 1]⟩, ⟨.or, [0, 2]⟩, ⟨.and, [5, 6]⟩,
    ⟨.or, [2, 3]⟩, ⟨.and, [7, 8]⟩, ⟨.or, [2, 4]⟩,
    ⟨.and, [7, 10]⟩, ⟨.or, [9, 11]⟩], 12⟩

def compactSharedCircuit : Circuit :=
  ⟨[⟨.or, [2, 3]⟩, ⟨.or, [5, 4]⟩, ⟨.and, [0, 6]⟩,
    ⟨.and, [1, 2]⟩, ⟨.or, [7, 8]⟩], 9⟩

lemma sharedCircuit_size : sharedCircuit.size = 8 := rfl

lemma compactSharedCircuit_size : compactSharedCircuit.size = 5 := rfl

lemma sharedCircuit_ao2 : PEqualNP.TopForm.IsAO2 5 sharedCircuit := by decide

lemma compactSharedCircuit_ao2 : PEqualNP.TopForm.IsAO2 5 compactSharedCircuit := by decide

lemma sharedCircuit_eval (a b x y z : Bool) :
    sharedCircuit.eval [a, b, x, y, z] =
      (sharedBlock a b x y || sharedBlock a b x z) := by
  cases a <;> cases b <;> cases x <;> cases y <;> cases z <;> rfl

lemma compactSharedCircuit_eval (a b x y z : Bool) :
    compactSharedCircuit.eval [a, b, x, y, z] =
      ((a && ((x || y) || z)) || (b && x)) := by
  cases a <;> cases b <;> cases x <;> cases y <;> cases z <;> rfl

lemma sharedCircuit_equiv (a b x y z : Bool) :
    sharedCircuit.eval [a, b, x, y, z] = compactSharedCircuit.eval [a, b, x, y, z] := by
  rw [sharedCircuit_eval, compactSharedCircuit_eval, sharedUnion_eq]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
lemma sharedCircuit_below_pattern :
    ∀ j : Fin 8, PEqualNP.CircuitMoves.WireBelowOutput 5 sharedCircuit (5 + j.val) ↔
      j.val = 4 ∨ j.val = 6 ∨ j.val = 7 := by decide

end SharedBlock

namespace PathCover

lemma cross_endpoints_cover {α : Type} (G : SimpleGraph α)
    (hnf : ∀ a b : α, a ≠ b → ∀ c d : α,
      G.Adj a c → G.Adj b c → G.Adj a d → G.Adj b d → c = d)
    (S T : Finset α) (hcomplete : ∀ s ∈ S, ∀ t ∈ T, G.Adj s t)
    (s : α) (hs : s ∈ S) (t : α) (ht : t ∈ T) :
    ∀ a ∈ S, ∀ b ∈ T, a = s ∨ b = t := by
  intro a ha b hb
  by_cases has : a = s
  · exact Or.inl has
  · right
    exact hnf s a (Ne.symm has) b t
      (hcomplete s hs b hb) (hcomplete a ha b hb)
      (hcomplete s hs t ht) (hcomplete a ha t ht)

lemma biclique_vertex_cover_two {α : Type} (G : SimpleGraph α)
    (hnf : ∀ a b : α, a ≠ b → ∀ c d : α,
      G.Adj a c → G.Adj b c → G.Adj a d → G.Adj b d → c = d)
    (S T : Finset α) (hcomplete : ∀ s ∈ S, ∀ t ∈ T, G.Adj s t)
    (hedges : ∀ a b : α, G.Adj a b →
      (a ∈ S ∧ b ∈ T) ∨ (b ∈ S ∧ a ∈ T)) :
    ∃ K : Finset α, K.card ≤ 2 ∧ ∀ a b : α, G.Adj a b → a ∈ K ∨ b ∈ K := by
  classical
  by_cases hs : S.Nonempty
  · by_cases ht : T.Nonempty
    · obtain ⟨s, hs⟩ := hs
      obtain ⟨t, ht⟩ := ht
      refine ⟨{s, t}, ?_, ?_⟩
      · calc
          ({s, t} : Finset α).card ≤ ({t} : Finset α).card + 1 := Finset.card_insert_le _ _
          _ = 2 := by simp
      · intro a b hab
        rcases hedges a b hab with ⟨ha, hb⟩ | ⟨hb, ha⟩
        · rcases cross_endpoints_cover G hnf S T hcomplete s hs t ht a ha b hb with h | h
          · left; simp [h]
          · right; simp [h]
        · rcases cross_endpoints_cover G hnf S T hcomplete s hs t ht b hb a ha with h | h
          · right; simp [h]
          · left; simp [h]
    · refine ⟨∅, by simp, ?_⟩
      intro a b hab
      rcases hedges a b hab with ⟨ha, hb⟩ | ⟨hb, ha⟩
      · exact False.elim (ht ⟨b, hb⟩)
      · exact False.elim (ht ⟨a, ha⟩)
  · refine ⟨∅, by simp, ?_⟩
    intro a b hab
    rcases hedges a b hab with ⟨ha, hb⟩ | ⟨hb, ha⟩
    · exact False.elim (hs ⟨a, ha⟩)
    · exact False.elim (hs ⟨b, hb⟩)

lemma blowup_path_vertex_cover_two {α : Type} (G : SimpleGraph α)
    (hnf : ∀ a b : α, a ≠ b → ∀ c d : α,
      G.Adj a c → G.Adj b c → G.Adj a d → G.Adj b d → c = d)
    (A U V D : Finset α)
    (hAU : ∀ a ∈ A, ∀ u ∈ U, G.Adj a u)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, G.Adj u v)
    (hVD : ∀ v ∈ V, ∀ d ∈ D, G.Adj v d)
    (hedges : ∀ a b : α, G.Adj a b →
      (a ∈ A ∧ b ∈ U) ∨ (b ∈ A ∧ a ∈ U) ∨
      (a ∈ U ∧ b ∈ V) ∨ (b ∈ U ∧ a ∈ V) ∨
      (a ∈ V ∧ b ∈ D) ∨ (b ∈ V ∧ a ∈ D)) :
    ∃ K : Finset α, K.card ≤ 2 ∧ ∀ a b : α, G.Adj a b → a ∈ K ∨ b ∈ K := by
  classical
  by_cases hU : U.Nonempty
  · by_cases hV : V.Nonempty
    · obtain ⟨u, hu⟩ := hU
      obtain ⟨v, hv⟩ := hV
      let K : Finset α := {u, v}
      have leftCover : ∀ a ∈ A, ∀ b ∈ U, a ∈ K ∨ b ∈ K := by
        intro a ha b hb
        by_cases hav : a = v
        · left; simp [K, hav]
        by_cases hbu : b = u
        · right; simp [K, hbu]
        have hav' := hnf u b (Ne.symm hbu) a v
          (hAU a ha u hu).symm (hAU a ha b hb).symm
          (hUV u hu v hv) (hUV b hb v hv)
        exact False.elim (hav hav')
      have middleCover : ∀ a ∈ U, ∀ b ∈ V, a ∈ K ∨ b ∈ K := by
        intro a ha b hb
        rcases cross_endpoints_cover G hnf U V hUV u hu v hv a ha b hb with h | h
        · left; simp [K, h]
        · right; simp [K, h]
      have rightCover : ∀ a ∈ V, ∀ b ∈ D, a ∈ K ∨ b ∈ K := by
        intro a ha b hb
        by_cases hav : a = v
        · left; simp [K, hav]
        by_cases hbu : b = u
        · right; simp [K, hbu]
        have hub := hnf v a (Ne.symm hav) u b
          (hUV u hu v hv).symm (hUV u hu a ha).symm
          (hVD v hv b hb) (hVD a ha b hb)
        exact False.elim (hbu hub.symm)
      refine ⟨K, ?_, ?_⟩
      · calc
          K.card ≤ ({v} : Finset α).card + 1 := Finset.card_insert_le _ _
          _ = 2 := by simp
      · intro a b hab
        rcases hedges a b hab with h | h | h | h | h | h
        · exact leftCover a h.1 b h.2
        · exact (leftCover b h.1 a h.2).symm
        · exact middleCover a h.1 b h.2
        · exact (middleCover b h.1 a h.2).symm
        · exact rightCover a h.1 b h.2
        · exact (rightCover b h.1 a h.2).symm
    · apply biclique_vertex_cover_two G hnf A U hAU
      intro a b hab
      rcases hedges a b hab with h | h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact False.elim (hV ⟨b, h.2⟩)
      · exact False.elim (hV ⟨a, h.2⟩)
      · exact False.elim (hV ⟨a, h.1⟩)
      · exact False.elim (hV ⟨b, h.1⟩)
  · apply biclique_vertex_cover_two G hnf V D hVD
    intro a b hab
    rcases hedges a b hab with h | h | h | h | h | h
    · exact False.elim (hU ⟨b, h.2⟩)
    · exact False.elim (hU ⟨a, h.2⟩)
    · exact False.elim (hU ⟨a, h.1⟩)
    · exact False.elim (hU ⟨b, h.1⟩)
    · exact Or.inl h
    · exact Or.inr h

lemma blowup_path_vertex_cover_two_of_noFourCycle {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hnf : PEqualNP.TopForm.NoFourCycle G)
    (A U V D : Finset (Fin n))
    (hAU : ∀ a ∈ A, ∀ u ∈ U, G.Adj a u)
    (hUV : ∀ u ∈ U, ∀ v ∈ V, G.Adj u v)
    (hVD : ∀ v ∈ V, ∀ d ∈ D, G.Adj v d)
    (hedges : ∀ a b : Fin n, G.Adj a b →
      (a ∈ A ∧ b ∈ U) ∨ (b ∈ A ∧ a ∈ U) ∨
      (a ∈ U ∧ b ∈ V) ∨ (b ∈ U ∧ a ∈ V) ∨
      (a ∈ V ∧ b ∈ D) ∨ (b ∈ V ∧ a ∈ D)) :
    ∃ K : Finset (Fin n), K.card ≤ 2 ∧
      ∀ a b : Fin n, G.Adj a b → a ∈ K ∨ b ∈ K := by
  apply blowup_path_vertex_cover_two G ?_ A U V D hAU hUV hVD hedges
  intro a b hab c d hac hbc had hbd
  apply Finset.card_le_one.mp (hnf a b hab)
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ c, hac, hbc⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ d, had, hbd⟩

lemma three_clause_missing_pair_cover_two {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hnf : PEqualNP.TopForm.NoFourCycle G)
    (P Q R : Fin n → Prop)
    (hedges : ∀ a b : Fin n, G.Adj a b ↔
      (P a ∨ P b) ∧ (Q a ∨ Q b) ∧ (R a ∨ R b))
    (hmiss : ∀ a : Fin n, ¬ (Q a ∧ R a)) :
    ∃ K : Finset (Fin n), K.card ≤ 2 ∧
      ∀ a b : Fin n, G.Adj a b → a ∈ K ∨ b ∈ K := by
  classical
  let A := Finset.univ.filter (fun a : Fin n => R a ∧ ¬ P a)
  let U := Finset.univ.filter (fun a : Fin n => P a ∧ Q a)
  let V := Finset.univ.filter (fun a : Fin n => P a ∧ R a)
  let D := Finset.univ.filter (fun a : Fin n => Q a ∧ ¬ P a)
  apply blowup_path_vertex_cover_two_of_noFourCycle G hnf A U V D
  · intro a ha u hu
    have ha' := (Finset.mem_filter.mp ha).2
    have hu' := (Finset.mem_filter.mp hu).2
    exact (hedges a u).mpr ⟨Or.inr hu'.1, Or.inr hu'.2, Or.inl ha'.1⟩
  · intro u hu v hv
    have hu' := (Finset.mem_filter.mp hu).2
    have hv' := (Finset.mem_filter.mp hv).2
    exact (hedges u v).mpr ⟨Or.inl hu'.1, Or.inl hu'.2, Or.inr hv'.2⟩
  · intro v hv d hd
    have hv' := (Finset.mem_filter.mp hv).2
    have hd' := (Finset.mem_filter.mp hd).2
    exact (hedges v d).mpr ⟨Or.inl hv'.1, Or.inr hd'.1, Or.inl hv'.2⟩
  · intro a b hab
    simp only [A, U, V, D, Finset.mem_filter, Finset.mem_univ, true_and]
    have he := (hedges a b).mp hab
    have ha := hmiss a
    have hb := hmiss b
    tauto

lemma three_clause_vertex_cover_two {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hnf : PEqualNP.TopForm.NoFourCycle G)
    (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (P Q R : Fin n → Prop)
    (hedges : ∀ a b : Fin n, G.Adj a b ↔
      (P a ∨ P b) ∧ (Q a ∨ Q b) ∧ (R a ∨ R b)) :
    ∃ K : Finset (Fin n), K.card ≤ 2 ∧
      ∀ a b : Fin n, G.Adj a b → a ∈ K ∨ b ∈ K := by
  classical
  by_cases hpq : ∃ a : Fin n, P a ∧ Q a
  · by_cases hpr : ∃ a : Fin n, P a ∧ R a
    · by_cases hqr : ∃ a : Fin n, Q a ∧ R a
      · obtain ⟨a, haP, haQ⟩ := hpq
        obtain ⟨b, hbP, hbR⟩ := hpr
        obtain ⟨c, hcQ, hcR⟩ := hqr
        have hab : G.Adj a b := (hedges a b).mpr ⟨Or.inl haP, Or.inl haQ, Or.inr hbR⟩
        have hbc : G.Adj b c := (hedges b c).mpr ⟨Or.inl hbP, Or.inr hcQ, Or.inl hbR⟩
        have hca : G.Adj c a := (hedges c a).mpr ⟨Or.inr haP, Or.inl hcQ, Or.inl hcR⟩
        exact False.elim (htri a b c hab hbc hca)
      · exact three_clause_missing_pair_cover_two G hnf P Q R hedges
          (fun a ha => hqr ⟨a, ha⟩)
    · apply three_clause_missing_pair_cover_two G hnf Q P R
      · intro a b
        rw [hedges a b]
        tauto
      · intro a ha
        exact hpr ⟨a, ha⟩
  · apply three_clause_missing_pair_cover_two G hnf R P Q
    · intro a b
      rw [hedges a b]
      tauto
    · intro a ha
      exact hpq ⟨a, ha⟩

lemma three_bool_clause_vertex_cover_two {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hnf : PEqualNP.TopForm.NoFourCycle G)
    (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (P Q R : Fin n → Bool)
    (hedges : ∀ a b : Fin n, G.Adj a b ↔
      ((P a || P b) && (Q a || Q b) && (R a || R b)) = true) :
    ∃ K : Finset (Fin n), K.card ≤ 2 ∧
      ∀ a b : Fin n, G.Adj a b → a ∈ K ∨ b ∈ K := by
  apply three_clause_vertex_cover_two G hnf htri (fun a => P a = true)
    (fun a => Q a = true) (fun a => R a = true)
  intro a b
  simpa only [Bool.and_eq_true, Bool.or_eq_true, and_assoc] using hedges a b

lemma three_bool_clause_safe_vertex_cover_two {n : ℕ}
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (hnf : PEqualNP.TopForm.NoFourCycle G)
    (htri : ∀ a b c : Fin n, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (P Q R : Fin n → Bool)
    (hsafe : ∀ a b : Fin n,
      ((P a || P b) && (Q a || Q b) && (R a || R b)) = true → G.Adj a b) :
    ∃ K : Finset (Fin n), K.card ≤ 2 ∧ ∀ a b : Fin n,
      ((P a || P b) && (Q a || Q b) && (R a || R b)) = true → a ∈ K ∨ b ∈ K := by
  classical
  let H : SimpleGraph (Fin n) := {
    Adj := fun a b => ((P a || P b) && (Q a || Q b) && (R a || R b)) = true
    symm := ⟨fun a b h => by simpa only [Bool.or_comm] using h⟩
    loopless := ⟨fun a h => G.irrefl (hsafe a a h)⟩ }
  have hsub : ∀ a b, H.Adj a b → G.Adj a b := hsafe
  have hHnf : PEqualNP.TopForm.NoFourCycle H := by
    intro a b hab
    calc
      (Finset.univ.filter (fun w => H.Adj a w ∧ H.Adj b w)).card ≤
          (Finset.univ.filter (fun w => G.Adj a w ∧ G.Adj b w)).card := by
        apply Finset.card_le_card
        intro w hw
        have hw' := (Finset.mem_filter.mp hw).2
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ w, hsub a w hw'.1, hsub b w hw'.2⟩
      _ ≤ 1 := hnf a b hab
  have hHtri : ∀ a b c, H.Adj a b → H.Adj b c → ¬ H.Adj c a := by
    intro a b c hab hbc hca
    exact htri a b c (hsub a b hab) (hsub b c hbc) (hsub c a hca)
  exact three_bool_clause_vertex_cover_two H hHnf hHtri P Q R (fun _ _ => Iff.rfl)

end PathCover

namespace MatchingCNF

lemma separated_clause_count {P L r k : ℕ}
    (I : Fin P → Fin L → Prop) (p : Fin r → Fin P) (l : Fin r → Fin L)
    (Sp : Fin k → Fin P → Prop) (Sl : Fin k → Fin L → Prop)
    (hcross : ∀ i j : Fin r, i ≠ j → ¬ (I (p i) (l j) ∧ I (p j) (l i)))
    (hcover : ∀ c : Fin k, ∀ i : Fin r, Sp c (p i) ∨ Sl c (l i))
    (hzero : ∃ c : Fin k, ∀ i : Fin r, ¬ Sp c (p i))
    (hline : ∀ i : Fin r, ∃ c : Fin k,
      ¬ Sl c (l i) ∧ ∀ j : Fin r, ¬ I (p j) (l i) → ¬ Sp c (p j)) :
    r + 1 ≤ k := by
  classical
  obtain ⟨c0, hc0⟩ := hzero
  choose c hc using hline
  let f : Option (Fin r) → Fin k := fun i => i.elim c0 c
  have hinj : Function.Injective f := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some i =>
        change c0 = c i at hab
        rcases hcover (c i) i with hp | hl
        · rw [← hab] at hp
          exact False.elim (hc0 i hp)
        · exact False.elim ((hc i).1 hl)
    | some i =>
      cases b with
      | none =>
        change c i = c0 at hab
        rcases hcover (c i) i with hp | hl
        · rw [hab] at hp
          exact False.elim (hc0 i hp)
        · exact False.elim ((hc i).1 hl)
      | some j =>
        change c i = c j at hab
        by_cases hij : i = j
        · subst j
          rfl
        · have hpi : Sp (c i) (p i) := (hcover (c i) i).resolve_right (hc i).1
          have hpj : Sp (c j) (p j) := (hcover (c j) j).resolve_right (hc j).1
          have hsep : ¬ I (p i) (l j) ∨ ¬ I (p j) (l i) := not_and_or.mp (hcross i j hij)
          rcases hsep with hsep | hsep
          · rw [hab] at hpi
            exact False.elim ((hc j).2 i hsep hpi)
          · rw [← hab] at hpj
            exact False.elim ((hc i).2 j hsep hpj)
  have hcard := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_option, Fintype.card_fin] using hcard

lemma full_safety_clause_count {P L r k : ℕ}
    (I : Fin P → Fin L → Prop) (p : Fin r → Fin P) (l : Fin r → Fin L)
    (Sp : Fin k → Fin P → Prop) (Sl : Fin k → Fin L → Prop)
    (hcross : ∀ i j : Fin r, i ≠ j → ¬ (I (p i) (l j) ∧ I (p j) (l i)))
    (hcover : ∀ c : Fin k, ∀ i : Fin r, Sp c (p i) ∨ Sl c (l i))
    (hsafe : ∀ (x : Fin P → Bool) (y : Fin L → Bool),
      (∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ x a = true) ∨ (∃ b : Fin L, Sl c b ∧ y b = true)) →
      ∃ a b, I a b ∧ x a = true ∧ y b = true) :
    r + 1 ≤ k := by
  classical
  apply separated_clause_count I p l Sp Sl hcross hcover
  · by_contra hnone
    have hhits : ∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ (true : Bool) = true) ∨
        (∃ b : Fin L, Sl c b ∧ (false : Bool) = true) := by
      intro c
      have hex : ∃ i : Fin r, Sp c (p i) := by
        by_contra h
        apply hnone
        exact ⟨c, fun i hi => h ⟨i, hi⟩⟩
      obtain ⟨i, hi⟩ := hex
      exact Or.inl ⟨p i, hi, rfl⟩
    obtain ⟨a, b, hab, ha, hb⟩ := hsafe (fun _ => true) (fun _ => false) hhits
    cases hb
  · intro i
    let x : Fin P → Bool := fun a => decide (¬ I a (l i))
    let y : Fin L → Bool := fun b => decide (b = l i)
    by_contra hnone
    have hhits : ∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ x a = true) ∨ (∃ b : Fin L, Sl c b ∧ y b = true) := by
      intro c
      by_cases hli : Sl c (l i)
      · exact Or.inr ⟨l i, hli, by simp [y]⟩
      · have hex : ∃ j : Fin r, ¬ I (p j) (l i) ∧ Sp c (p j) := by
          by_contra h
          apply hnone
          exact ⟨c, hli, fun j hj hSp => h ⟨j, hj, hSp⟩⟩
        obtain ⟨j, hj, hSp⟩ := hex
        exact Or.inl ⟨p j, hSp, by simp [x, hj]⟩
    obtain ⟨a, b, hab, ha, hb⟩ := hsafe x y hhits
    have heq : b = l i := by simpa only [y, decide_eq_true_eq] using hb
    have hnot : ¬ I a (l i) := by simpa only [x, decide_eq_true_eq] using ha
    exact hnot (heq ▸ hab)

lemma no_four_cycle_full_safety_clause_count {P L r k : ℕ}
    (I : Fin P → Fin L → Prop) (p : Fin r → Fin P) (l : Fin r → Fin L)
    (hp : Function.Injective p) (hl : Function.Injective l)
    (hdiag : ∀ i : Fin r, I (p i) (l i))
    (hfour : ∀ a a' : Fin P, a ≠ a' → ∀ b b' : Fin L,
      I a b → I a' b → I a b' → I a' b' → b = b')
    (Sp : Fin k → Fin P → Prop) (Sl : Fin k → Fin L → Prop)
    (hcover : ∀ c : Fin k, ∀ i : Fin r, Sp c (p i) ∨ Sl c (l i))
    (hsafe : ∀ (x : Fin P → Bool) (y : Fin L → Bool),
      (∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ x a = true) ∨ (∃ b : Fin L, Sl c b ∧ y b = true)) →
      ∃ a b, I a b ∧ x a = true ∧ y b = true) :
    r + 1 ≤ k := by
  apply full_safety_clause_count I p l Sp Sl ?_ hcover hsafe
  intro i j hij hcross
  have hpp : p i ≠ p j := fun h => hij (hp h)
  have hll : l i = l j := hfour (p i) (p j) hpp (l i) (l j)
    (hdiag i) hcross.2 hcross.1 (hdiag j)
  exact hij (hl hll)

lemma unified_full_safety_matching_bound {P L r k : ℕ}
    (I : Fin P → Fin L → Prop) (p : Fin r → Fin P) (l : Fin r → Fin L)
    (hp : Function.Injective p) (hl : Function.Injective l)
    (hdiag : ∀ i : Fin r, I (p i) (l i))
    (hfour : ∀ a a' : Fin P, a ≠ a' → ∀ b b' : Fin L,
      I a b → I a' b → I a b' → I a' b' → b = b')
    (S : Fin k → Fin (P + L) → Bool)
    (hcover : ∀ c : Fin k, ∀ i : Fin r,
      S c (Fin.castAdd L (p i)) = true ∨ S c (Fin.natAdd P (l i)) = true)
    (hsafe : ∀ z : Fin (P + L) → Bool,
      (∀ c : Fin k, ∃ v : Fin (P + L), S c v = true ∧ z v = true) →
      ∃ a b, I a b ∧ z (Fin.castAdd L a) = true ∧ z (Fin.natAdd P b) = true) :
    r + 1 ≤ k := by
  apply no_four_cycle_full_safety_clause_count I p l hp hl hdiag hfour
    (fun c a => S c (Fin.castAdd L a) = true)
    (fun c b => S c (Fin.natAdd P b) = true) hcover
  intro x y hhits
  let z : Fin (P + L) → Bool := Fin.addCases x y
  have hhits' : ∀ c : Fin k, ∃ v : Fin (P + L), S c v = true ∧ z v = true := by
    intro c
    rcases hhits c with ⟨a, ha, hxa⟩ | ⟨b, hb, hyb⟩
    · exact ⟨Fin.castAdd L a, ha, by simpa only [z, Fin.addCases_left] using hxa⟩
    · exact ⟨Fin.natAdd P b, hb, by simpa only [z, Fin.addCases_right] using hyb⟩
  obtain ⟨a, b, hab, ha, hb⟩ := hsafe z hhits'
  exact ⟨a, b, hab, by simpa only [z, Fin.addCases_left] using ha,
    by simpa only [z, Fin.addCases_right] using hb⟩

end MatchingCNF

namespace CNF

lemma clause_of_maximal_false
    {n : ℕ} (F : (Fin n → Bool) → Bool)
    (clauses : Finset (Finset (Fin n))) (M : Finset (Fin n))
    (hcnf : ∀ z, F z = true ↔ ∀ K ∈ clauses, ∃ v ∈ K, z v = true)
    (hfalse : F (PEqualNP.ReadK.setInput M) = false)
    (hmax : ∀ i ∉ M, F (PEqualNP.ReadK.setInput (insert i M)) = true) :
    Mᶜ ∈ clauses := by
  classical
  have hnot : ¬ ∀ K ∈ clauses, ∃ v ∈ K, PEqualNP.ReadK.setInput M v = true := by
    intro h
    have ht := (hcnf _).mpr h
    rw [hfalse] at ht
    cases ht
  push Not at hnot
  obtain ⟨K, hK, havoid⟩ := hnot
  have hKM : K ⊆ Mᶜ := by
    intro v hv
    simpa [PEqualNP.ReadK.setInput] using havoid v hv
  have hMK : Mᶜ ⊆ K := by
    intro i hi
    have hiM : i ∉ M := by simpa using hi
    obtain ⟨v, hv, ht⟩ := (hcnf _).mp (hmax i hiM) K hK
    have hvi : v = i ∨ v ∈ M := by simpa [PEqualNP.ReadK.setInput] using ht
    rcases hvi with rfl | hvm
    · exact hv
    · have hvnot : v ∉ M := by simpa using hKM hv
      exact (hvnot hvm).elim
  have heq : K = Mᶜ := Finset.Subset.antisymm hKM hMK
  exact heq ▸ hK

lemma maximal_false_family_card_le
    {n : ℕ} (F : (Fin n → Bool) → Bool)
    (clauses family : Finset (Finset (Fin n)))
    (hcnf : ∀ z, F z = true ↔ ∀ K ∈ clauses, ∃ v ∈ K, z v = true)
    (hfalse : ∀ M ∈ family, F (PEqualNP.ReadK.setInput M) = false)
    (hmax : ∀ M ∈ family, ∀ i ∉ M,
      F (PEqualNP.ReadK.setInput (insert i M)) = true) :
    family.card ≤ clauses.card := by
  classical
  have hsub : family.image (fun M => Mᶜ) ⊆ clauses := by
    intro K hK
    obtain ⟨M, hM, rfl⟩ := Finset.mem_image.mp hK
    exact clause_of_maximal_false F clauses M hcnf (hfalse M hM) (hmax M hM)
  calc
    family.card = (family.image (fun M => Mᶜ)).card := by
      rw [Finset.card_image_of_injective]
      intro A B h
      simpa only [compl_compl] using congrArg (fun M : Finset (Fin n) => Mᶜ) h
    _ ≤ clauses.card := Finset.card_le_card hsub

def incidenceSet {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (S : Finset (Fin P)) : Finset (Fin (P + L)) :=
  S.image (Fin.castAdd L) ∪
    (Finset.univ.filter (fun l => ∀ p ∈ S, ¬ I p l)).image (Fin.natAdd P)

lemma incidenceSet_point {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (S : Finset (Fin P)) (p : Fin P) :
    Fin.castAdd L p ∈ incidenceSet I S ↔ p ∈ S := by
  simp [incidenceSet]
  intro x hx heq
  have hv := congrArg Fin.val heq
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

lemma incidenceSet_line {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (S : Finset (Fin P)) (l : Fin L) :
    Fin.natAdd P l ∈ incidenceSet I S ↔ ∀ p ∈ S, ¬ I p l := by
  simp [incidenceSet]
  intro x hx heq
  have hv := congrArg Fin.val heq
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

lemma incidenceSet_false {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (S : Finset (Fin P)) :
    ¬ ∃ p l, I p l ∧ Fin.castAdd L p ∈ incidenceSet I S ∧
      Fin.natAdd P l ∈ incidenceSet I S := by
  rintro ⟨p, l, hpl, hp, hl⟩
  exact (incidenceSet_line I S l).mp hl p ((incidenceSet_point I S p).mp hp) hpl

lemma incidenceSet_maximal {P L : ℕ} (I : Fin P → Fin L → Prop) [DecidableRel I]
    (S : Finset (Fin P))
    (hsep : ∀ p ∉ S, ∃ l, I p l ∧ ∀ s ∈ S, ¬ I s l) :
    ∀ i ∉ incidenceSet I S,
      ∃ p l, I p l ∧ Fin.castAdd L p ∈ insert i (incidenceSet I S) ∧
        Fin.natAdd P l ∈ insert i (incidenceSet I S) := by
  intro i
  refine Fin.addCases ?_ ?_ i
  · intro p hp
    have hpS : p ∉ S := by simpa only [incidenceSet_point] using hp
    obtain ⟨l, hpl, hl⟩ := hsep p hpS
    refine ⟨p, l, hpl, Finset.mem_insert_self _ _, Finset.mem_insert_of_mem ?_⟩
    exact (incidenceSet_line I S l).mpr hl
  · intro l hl
    have hnot : ¬ ∀ p ∈ S, ¬ I p l := by simpa only [incidenceSet_line] using hl
    push Not at hnot
    obtain ⟨p, hp, hpl⟩ := hnot
    refine ⟨p, l, hpl, Finset.mem_insert_of_mem ?_, Finset.mem_insert_self _ _⟩
    exact (incidenceSet_point I S p).mpr hp

lemma incidence_clause_family_bound {P L : ℕ}
    (I : Fin P → Fin L → Prop) [DecidableRel I]
    (family : Finset (Finset (Fin P)))
    (clauses : Finset (Finset (Fin (P + L))))
    (hsep : ∀ S ∈ family, ∀ p ∉ S, ∃ l, I p l ∧ ∀ s ∈ S, ¬ I s l)
    (hcnf : ∀ z : Fin (P + L) → Bool,
      (∃ p l, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true) ↔
      ∀ K ∈ clauses, ∃ v ∈ K, z v = true) :
    family.card ≤ clauses.card := by
  classical
  let F := fun z : Fin (P + L) → Bool =>
    decide (∃ p l, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true)
  have hF : ∀ z, F z = true ↔ ∀ K ∈ clauses, ∃ v ∈ K, z v = true := by
    intro z
    simpa only [F, decide_eq_true_eq] using hcnf z
  have hinj : Function.Injective (incidenceSet I) := by
    intro S T h
    apply Finset.ext
    intro p
    rw [← incidenceSet_point I S p, h, incidenceSet_point I T p]
  have hc := maximal_false_family_card_le F clauses (family.image (incidenceSet I)) hF
    (by
      intro M hM
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hM
      apply decide_eq_false
      simpa only [PEqualNP.ReadK.setInput, decide_eq_true_eq] using incidenceSet_false I S)
    (by
      intro M hM i hi
      obtain ⟨S, hS, rfl⟩ := Finset.mem_image.mp hM
      apply decide_eq_true
      simpa only [PEqualNP.ReadK.setInput, decide_eq_true_eq] using
        incidenceSet_maximal I S (hsep S hS) i hi)
  simpa only [Finset.card_image_of_injective family hinj] using hc

lemma small_point_subsets_clause_bound {P L : ℕ}
    (I : Fin P → Fin L → Prop) [DecidableRel I]
    (clauses : Finset (Finset (Fin (P + L))))
    (huniq : ∀ p p' : Fin P, p ≠ p' →
      ∀ l l' : Fin L, I p l → I p' l → I p l' → I p' l' → l = l')
    (hdeg : ∀ p : Fin P, 2 < (Finset.univ.filter (I p)).card)
    (hcnf : ∀ z : Fin (P + L) → Bool,
      (∃ p l, I p l ∧ z (Fin.castAdd L p) = true ∧ z (Fin.natAdd P l) = true) ↔
      ∀ K ∈ clauses, ∃ v ∈ K, z v = true) :
    1 + P + Nat.choose P 2 ≤ clauses.card := by
  classical
  let U : Finset (Fin P) := Finset.univ
  let family := U.powersetCard 0 ∪ (U.powersetCard 1 ∪ U.powersetCard 2)
  have hmem : ∀ S ∈ family, S.card ≤ 2 := by
    intro S hS
    rcases Finset.mem_union.mp hS with h | h
    · have := (Finset.mem_powersetCard.mp h).2
      omega
    · rcases Finset.mem_union.mp h with h | h
      · have := (Finset.mem_powersetCard.mp h).2
        omega
      · have := (Finset.mem_powersetCard.mp h).2
        omega
  have hcard : family.card = 1 + P + Nat.choose P 2 := by
    unfold family
    rw [Finset.card_union_of_disjoint, Finset.card_union_of_disjoint]
    · simp [U, Nat.add_assoc]
    · exact Finset.disjoint_powersetCard_of_ne (by decide) U U
    · exact Finset.disjoint_union_right.mpr ⟨
        Finset.disjoint_powersetCard_of_ne (m := 0) (n := 1) (by decide) U U,
        Finset.disjoint_powersetCard_of_ne (m := 0) (n := 2) (by decide) U U⟩
  rw [← hcard]
  exact incidence_clause_family_bound I family clauses
    (fun S hS p hp => PEqualNP.Outside.L_meta_2583.Geometry.exists_line_avoiding_small_set
      I huniq S p hp (lt_of_le_of_lt (hmem S hS) (hdeg p))) hcnf

lemma plane_size_small_subsets_bound (q N : ℕ) (hq : 2 ≤ q)
    (hN : N = q ^ 2 + q + 1) : N * (q + 2) + 1 ≤ 1 + N + Nat.choose N 2 := by
  have hq2 : 2 * q ≤ q * q := Nat.mul_le_mul_right q hq
  have hN0 : 1 ≤ N := by nlinarith
  have hNbig : 2 * q + 3 ≤ N := by nlinarith
  have hsub : N - 1 + 1 = N := by omega
  have hc := Nat.add_one_mul_choose_eq (N - 1) 1
  simp only [Nat.choose_one_right, hsub] at hc
  have hm := Nat.mul_le_mul_left N hNbig
  have hsubmul : N * (N - 1) + N = N * N := by
    calc
      N * (N - 1) + N = N * (N - 1 + 1) := by simp [Nat.mul_add]
      _ = N * N := by rw [hsub]
  nlinarith

end CNF


namespace CNF

lemma plane_point_degree_three
    (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hlines : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (hjoin : ∀ p p' : Fin N, p ≠ p' → ∃ l : Fin N, I p l ∧ I p' l) :
    ∀ p : Fin N, 2 < (Finset.univ.filter (I p)).card := by
  classical
  intro p
  have hNpos : 1 < N := by omega
  have hpother : ∃ p' : Fin N, p ≠ p' := by
    by_cases hp0 : p.val = 0
    · refine ⟨⟨1, hNpos⟩, ?_⟩
      intro h
      have hh := congrArg Fin.val h
      change p.val = 1 at hh
      omega
    · refine ⟨⟨0, by omega⟩, ?_⟩
      intro h
      exact hp0 (congrArg Fin.val h)
  obtain ⟨p', hpp'⟩ := hpother
  obtain ⟨l0, hp0, hp'0⟩ := hjoin p p' hpp'
  let lines : Finset (Fin N) := Finset.univ.filter (I p)
  let points : Fin N → Finset (Fin N) := fun l => Finset.univ.filter (fun x => I x l)
  have hcover : Finset.univ ⊆ lines.biUnion points := by
    intro x hx
    by_cases hpx : p = x
    · subst x
      exact Finset.mem_biUnion.mpr ⟨l0, by simp [lines, hp0], by simp [points, hp0]⟩
    · obtain ⟨l, hpl, hxl⟩ := hjoin p x hpx
      exact Finset.mem_biUnion.mpr ⟨l, by simp [lines, hpl], by simp [points, hxl]⟩
  have hbound : N ≤ lines.card * (q + 1) := calc
    N = (Finset.univ : Finset (Fin N)).card := by simp
    _ ≤ (lines.biUnion points).card := Finset.card_le_card hcover
    _ ≤ ∑ l ∈ lines, (points l).card := Finset.card_biUnion_le
    _ = lines.card * (q + 1) := by simp [points, hlines]
  by_contra hsmall
  have hsmall' : lines.card ≤ 2 := Nat.le_of_not_gt hsmall
  have hprod := Nat.mul_le_mul_right (q + 1) hsmall'
  have hq2 : 2 * q ≤ q * q := Nat.mul_le_mul_right q hq
  nlinarith

end CNF

namespace CNF

lemma plane_cnf_clause_bounds
    (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q ^ 2 + q + 1)
    (hlines : ∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1)
    (huniq : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (clauses : Finset (Finset (Fin (N + N))))
    (hcnf : ∀ z : Fin (N + N) → Bool,
      (∃ p l, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ↔
      ∀ K ∈ clauses, ∃ v ∈ K, z v = true) :
    1 + N + Nat.choose N 2 ≤ clauses.card ∧ N * (q + 2) + 1 ≤ clauses.card := by
  have hdeg : ∀ p : Fin N, 2 < (Finset.univ.filter (I p)).card :=
    plane_point_degree_three q N I hq hN hlines (fun p p' h => (huniq p p' h).exists)
  have hunique : ∀ p p' : Fin N, p ≠ p' →
      ∀ l l' : Fin N, I p l → I p' l → I p l' → I p' l' → l = l' := by
    intro p p' hpp l l' hpl hp'l hpl' hp'l'
    obtain ⟨k, hk, hku⟩ := huniq p p' hpp
    exact (hku l ⟨hpl, hp'l⟩).trans (hku l' ⟨hpl', hp'l'⟩).symm
  have hbound := small_point_subsets_clause_bound I clauses hunique hdeg hcnf
  exact ⟨hbound, (plane_size_small_subsets_bound q N hq hN).trans hbound⟩

end CNF

namespace StrictMatchingCNF

lemma selected_clause_injective {P L r k : ℕ}
    (I : Fin P → Fin L → Prop) (p : Fin r → Fin P) (l : Fin r → Fin L)
    (Sp : Fin k → Fin P → Prop) (Sl : Fin k → Fin L → Prop)
    (hcross : ∀ i j : Fin r, i ≠ j → ¬ (I (p i) (l j) ∧ I (p j) (l i)))
    (hcover : ∀ c : Fin k, ∀ i : Fin r, Sp c (p i) ∨ Sl c (l i))
    (c0 : Fin k) (hc0 : ∀ i : Fin r, ¬ Sp c0 (p i))
    (c : Fin r → Fin k) (hc : ∀ i : Fin r,
      ¬ Sl (c i) (l i) ∧ ∀ j : Fin r, ¬ I (p j) (l i) → ¬ Sp (c i) (p j)) :
    Function.Injective (fun i : Option (Fin r) => i.elim c0 c) := by
  classical
  intro a b hab
  cases a with
  | none =>
    cases b with
    | none => rfl
    | some i =>
      change c0 = c i at hab
      rcases hcover (c i) i with hp | hl
      · rw [← hab] at hp
        exact False.elim (hc0 i hp)
      · exact False.elim ((hc i).1 hl)
  | some i =>
    cases b with
    | none =>
      change c i = c0 at hab
      rcases hcover (c i) i with hp | hl
      · rw [hab] at hp
        exact False.elim (hc0 i hp)
      · exact False.elim ((hc i).1 hl)
    | some j =>
      change c i = c j at hab
      by_cases hij : i = j
      · subst j
        rfl
      · have hpi : Sp (c i) (p i) := (hcover (c i) i).resolve_right (hc i).1
        have hpj : Sp (c j) (p j) := (hcover (c j) j).resolve_right (hc j).1
        have hsep : ¬ I (p i) (l j) ∨ ¬ I (p j) (l i) := not_and_or.mp (hcross i j hij)
        rcases hsep with hsep | hsep
        · rw [hab] at hpi
          exact False.elim ((hc j).2 i hsep hpi)
        · rw [← hab] at hpj
          exact False.elim ((hc i).2 j hsep hpj)

lemma strict_full_safety_matching_bound {P L r k : ℕ}
    (I : Fin P → Fin L → Prop) (p : Fin r → Fin P) (l : Fin r → Fin L)
    (hp : Function.Injective p) (hl : Function.Injective l)
    (hdiag : ∀ i : Fin r, I (p i) (l i))
    (hfour : ∀ a a' : Fin P, a ≠ a' → ∀ b b' : Fin L,
      I a b → I a' b → I a b' → I a' b' → b = b')
    (Sp : Fin k → Fin P → Prop) (Sl : Fin k → Fin L → Prop)
    (hcover : ∀ c : Fin k, ∀ i : Fin r, Sp c (p i) ∨ Sl c (l i))
    (hsafe : ∀ (x : Fin P → Bool) (y : Fin L → Bool),
      (∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ x a = true) ∨ (∃ b : Fin L, Sl c b ∧ y b = true)) →
      ∃ a b, I a b ∧ x a = true ∧ y b = true)
    (hr : 3 ≤ r) : r + 2 ≤ k := by
  classical
  have hbase := MatchingCNF.no_four_cycle_full_safety_clause_count
    I p l hp hl hdiag hfour Sp Sl hcover hsafe
  by_contra hsmall
  have hkeq : k = r + 1 := by omega
  have hcross : ∀ i j : Fin r, i ≠ j → ¬ (I (p i) (l j) ∧ I (p j) (l i)) := by
    intro i j hij hcross
    have hpp : p i ≠ p j := fun h => hij (hp h)
    have hll : l i = l j := hfour (p i) (p j) hpp (l i) (l j)
      (hdiag i) hcross.2 hcross.1 (hdiag j)
    exact hij (hl hll)
  have hzero : ∃ c : Fin k, ∀ i : Fin r, ¬ Sp c (p i) := by
    by_contra hnone
    have hhits : ∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ (true : Bool) = true) ∨
        (∃ b : Fin L, Sl c b ∧ (false : Bool) = true) := by
      intro c
      have hex : ∃ i : Fin r, Sp c (p i) := by
        by_contra h
        exact hnone ⟨c, fun i hi => h ⟨i, hi⟩⟩
      obtain ⟨i, hi⟩ := hex
      exact Or.inl ⟨p i, hi, rfl⟩
    obtain ⟨a, b, hab, ha, hb⟩ := hsafe (fun _ => true) (fun _ => false) hhits
    cases hb
  have hline : ∀ i : Fin r, ∃ c : Fin k,
      ¬ Sl c (l i) ∧ ∀ j : Fin r, ¬ I (p j) (l i) → ¬ Sp c (p j) := by
    intro i
    let x : Fin P → Bool := fun a => decide (¬ I a (l i))
    let y : Fin L → Bool := fun b => decide (b = l i)
    by_contra hnone
    have hhits : ∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ x a = true) ∨ (∃ b : Fin L, Sl c b ∧ y b = true) := by
      intro c
      by_cases hli : Sl c (l i)
      · exact Or.inr ⟨l i, hli, by simp [y]⟩
      · have hex : ∃ j : Fin r, ¬ I (p j) (l i) ∧ Sp c (p j) := by
          by_contra h
          exact hnone ⟨c, hli, fun j hj hSp => h ⟨j, hj, hSp⟩⟩
        obtain ⟨j, hj, hSp⟩ := hex
        exact Or.inl ⟨p j, hSp, by simp [x, hj]⟩
    obtain ⟨a, b, hab, ha, hb⟩ := hsafe x y hhits
    have heq : b = l i := by simpa only [y, decide_eq_true_eq] using hb
    have hnot : ¬ I a (l i) := by simpa only [x, decide_eq_true_eq] using ha
    exact hnot (heq ▸ hab)
  have hall : ∃ c : Fin k, ∀ i : Fin r, ¬ Sl c (l i) := by
    by_contra hnone
    have hhits : ∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ (false : Bool) = true) ∨
        (∃ b : Fin L, Sl c b ∧ (true : Bool) = true) := by
      intro c
      have hex : ∃ i : Fin r, Sl c (l i) := by
        by_contra h
        exact hnone ⟨c, fun i hi => h ⟨i, hi⟩⟩
      obtain ⟨i, hi⟩ := hex
      exact Or.inr ⟨l i, hi, rfl⟩
    obtain ⟨a, b, hab, ha, hb⟩ := hsafe (fun _ => false) (fun _ => true) hhits
    cases ha
  obtain ⟨c0, hc0⟩ := hzero
  choose c hc using hline
  let f : Option (Fin r) → Fin k := fun i => i.elim c0 c
  have hinj : Function.Injective f := selected_clause_injective I p l Sp Sl hcross hcover c0 hc0 c hc
  have hsurj : Function.Surjective f := by
    by_contra hnot
    have hc := Fintype.card_lt_of_injective_not_surjective f hinj hnot
    simp only [Fintype.card_option, Fintype.card_fin] at hc
    omega
  obtain ⟨cl, hcl⟩ := hall
  have hclP : ∀ a : Fin r, Sp cl (p a) := fun a => (hcover cl a).resolve_right (hcl a)
  have hspecial : ∃ i : Fin r, (∀ a : Fin r, Sp (c i) (p a)) ∧
      (∀ a : Fin r, ¬ Sl (c i) (l a)) := by
    obtain ⟨o, ho⟩ := hsurj cl
    cases o with
    | none =>
      change c0 = cl at ho
      let a : Fin r := ⟨0, by omega⟩
      exact False.elim (hc0 a (by rw [ho]; exact hclP a))
    | some i =>
      change c i = cl at ho
      exact ⟨i, by simpa only [ho] using hclP, by simpa only [ho] using hcl⟩
  obtain ⟨i, hiP, hiL⟩ := hspecial
  have hiUniversal : ∀ a : Fin r, I (p a) (l i) := by
    intro a
    by_contra hnot
    exact (hc i).2 a hnot (hiP a)
  have hOtherNonedge : ∀ j : Fin r, j ≠ i → ∀ a : Fin r, a ≠ j → ¬ I (p a) (l j) := by
    intro j hji a haj hcross
    have hpp : p a ≠ p j := fun h => haj (hp h)
    have hll : l i = l j := hfour (p a) (p j) hpp (l i) (l j)
      (hiUniversal a) (hiUniversal j) hcross (hdiag j)
    exact hji (hl hll).symm
  have hOtherL : ∀ j : Fin r, j ≠ i → ∀ a : Fin r, a ≠ j → Sl (c j) (l a) := by
    intro j hji a haj
    exact (hcover (c j) a).resolve_left ((hc j).2 a (hOtherNonedge j hji a haj))
  have h0L : ∀ a : Fin r, Sl c0 (l a) := fun a => (hcover c0 a).resolve_left (hc0 a)
  have hremain : 1 < ((Finset.univ : Finset (Fin r)).erase i).card := by
    simp only [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j, hj, t, ht, hjt⟩ := Finset.one_lt_card.mp hremain
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  have hti : t ≠ i := (Finset.mem_erase.mp ht).1
  let x : Fin P → Bool := fun a => decide (a = p i)
  let y : Fin L → Bool := fun b => decide (b = l j ∨ b = l t)
  have hhits : ∀ d : Fin k,
      (∃ a : Fin P, Sp d a ∧ x a = true) ∨ (∃ b : Fin L, Sl d b ∧ y b = true) := by
    intro d
    obtain ⟨o, ho⟩ := hsurj d
    cases o with
    | none =>
      change c0 = d at ho
      exact Or.inr ⟨l j, ho ▸ h0L j, by simp [y]⟩
    | some m =>
      change c m = d at ho
      by_cases hmi : m = i
      · subst m
        exact Or.inl ⟨p i, ho ▸ hiP i, by simp [x]⟩
      · by_cases hmj : m = j
        · subst m
          exact Or.inr ⟨l t, ho ▸ hOtherL j hji t (Ne.symm hjt), by simp [y]⟩
        · exact Or.inr ⟨l j, ho ▸ hOtherL m hmi j (Ne.symm hmj), by simp [y]⟩
  obtain ⟨a, b, hab, ha, hb⟩ := hsafe x y hhits
  have haeq : a = p i := by simpa only [x, decide_eq_true_eq] using ha
  have hbeq : b = l j ∨ b = l t := by simpa only [y, decide_eq_true_eq] using hb
  rcases hbeq with hb | hb
  · rw [haeq, hb] at hab
    exact hOtherNonedge j hji i (Ne.symm hji) hab
  · rw [haeq, hb] at hab
    exact hOtherNonedge t hti i (Ne.symm hti) hab

lemma unified_strict_full_safety_matching_bound {P L r k : ℕ}
    (I : Fin P → Fin L → Prop) (p : Fin r → Fin P) (l : Fin r → Fin L)
    (hp : Function.Injective p) (hl : Function.Injective l)
    (hdiag : ∀ i : Fin r, I (p i) (l i))
    (hfour : ∀ a a' : Fin P, a ≠ a' → ∀ b b' : Fin L,
      I a b → I a' b → I a b' → I a' b' → b = b')
    (S : Fin k → Fin (P + L) → Bool)
    (hcover : ∀ c : Fin k, ∀ i : Fin r,
      S c (Fin.castAdd L (p i)) = true ∨ S c (Fin.natAdd P (l i)) = true)
    (hsafe : ∀ z : Fin (P + L) → Bool,
      (∀ c : Fin k, ∃ v : Fin (P + L), S c v = true ∧ z v = true) →
      ∃ a b, I a b ∧ z (Fin.castAdd L a) = true ∧ z (Fin.natAdd P b) = true)
    (hr : 3 ≤ r) : r + 2 ≤ k := by
  apply strict_full_safety_matching_bound I p l hp hl hdiag hfour
    (fun c a => S c (Fin.castAdd L a) = true)
    (fun c b => S c (Fin.natAdd P b) = true) hcover ?_ hr
  intro x y hhits
  let z : Fin (P + L) → Bool := Fin.addCases x y
  have hhits' : ∀ c : Fin k, ∃ v : Fin (P + L), S c v = true ∧ z v = true := by
    intro c
    rcases hhits c with ⟨a, ha, hxa⟩ | ⟨b, hb, hyb⟩
    · exact ⟨Fin.castAdd L a, ha, by simpa only [z, Fin.addCases_left] using hxa⟩
    · exact ⟨Fin.natAdd P b, hb, by simpa only [z, Fin.addCases_right] using hyb⟩
  obtain ⟨a, b, hab, ha, hb⟩ := hsafe z hhits'
  exact ⟨a, b, hab, by simpa only [z, Fin.addCases_left] using ha,
    by simpa only [z, Fin.addCases_right] using hb⟩

end StrictMatchingCNF

namespace ActivePointCNF

lemma separated_active_points_clause_count {P L r k : ℕ}
    (I H : Fin P → Fin L → Prop) (p : Fin r → Fin P)
    (Sp : Fin k → Fin P → Prop) (Sl : Fin k → Fin L → Prop)
    (hactive : ∀ i : Fin r, ∃ l, H (p i) l)
    (hseparate : ∀ i j : Fin r, i ≠ j →
      ∃ l, (H (p i) l ∧ ¬ I (p j) l) ∨ (H (p j) l ∧ ¬ I (p i) l))
    (hcover : ∀ c : Fin k, ∀ a b, H a b → Sp c a ∨ Sl c b)
    (hsafe : ∀ (x : Fin P → Bool) (y : Fin L → Bool),
      (∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ x a = true) ∨
        (∃ b : Fin L, Sl c b ∧ y b = true)) →
      ∃ a b, I a b ∧ x a = true ∧ y b = true) :
    r + 1 ≤ k := by
  classical
  have hbase : ∃ c : Fin k, ∀ b, ¬ Sl c b := by
    by_contra h
    have hits : ∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ (false : Bool) = true) ∨
        (∃ b : Fin L, Sl c b ∧ (true : Bool) = true) := by
      intro c
      have hex : ∃ b, Sl c b := by
        by_contra hn
        exact h ⟨c, fun b hb => hn ⟨b, hb⟩⟩
      obtain ⟨b, hb⟩ := hex
      exact Or.inr ⟨b, hb, rfl⟩
    obtain ⟨a, b, hab, ha, hb⟩ := hsafe (fun _ => false) (fun _ => true) hits
    cases ha
  have hpoint : ∀ i : Fin r, ∃ c : Fin k,
      ¬ Sp c (p i) ∧ ∀ b, ¬ I (p i) b → ¬ Sl c b := by
    intro i
    let x : Fin P → Bool := fun a => decide (a = p i)
    let y : Fin L → Bool := fun b => decide (¬ I (p i) b)
    by_contra h
    have hits : ∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ x a = true) ∨
        (∃ b : Fin L, Sl c b ∧ y b = true) := by
      intro c
      by_cases hp : Sp c (p i)
      · exact Or.inl ⟨p i, hp, by simp [x]⟩
      · have hex : ∃ b, ¬ I (p i) b ∧ Sl c b := by
          by_contra hn
          exact h ⟨c, hp, fun b hnb hb => hn ⟨b, hnb, hb⟩⟩
        obtain ⟨b, hnb, hb⟩ := hex
        exact Or.inr ⟨b, hb, by simp [y, hnb]⟩
    obtain ⟨a, b, hab, ha, hb⟩ := hsafe x y hits
    have hap : a = p i := by simpa only [x, decide_eq_true_eq] using ha
    have hnb : ¬ I (p i) b := by simpa only [y, decide_eq_true_eq] using hb
    exact hnb (hap ▸ hab)
  obtain ⟨c0, hc0⟩ := hbase
  choose c hc using hpoint
  have c_ne_base (i : Fin r) : c i ≠ c0 := by
    intro heq
    obtain ⟨b, hb⟩ := hactive i
    rcases hcover (c i) (p i) b hb with hp | hl
    · exact (hc i).1 hp
    · rw [heq] at hl
      exact hc0 b hl
  have c_injective : Function.Injective c := by
    intro i j heq
    by_contra hij
    obtain ⟨b, hb | hb⟩ := hseparate i j hij
    · rcases hcover (c i) (p i) b hb.1 with hp | hl
      · exact (hc i).1 hp
      · rw [heq] at hl
        exact (hc j).2 b hb.2 hl
    · rcases hcover (c j) (p j) b hb.1 with hp | hl
      · exact (hc j).1 hp
      · rw [← heq] at hl
        exact (hc i).2 b hb.2 hl
  let f : Option (Fin r) → Fin k := fun i => i.elim c0 c
  have hinj : Function.Injective f := by
    intro a b hab
    cases a with
    | none =>
      cases b with
      | none => rfl
      | some i => exact False.elim (c_ne_base i hab.symm)
    | some i =>
      cases b with
      | none => exact False.elim (c_ne_base i hab)
      | some j => exact congrArg some (c_injective hab)
  have hcard := Fintype.card_le_of_injective f hinj
  simpa only [Fintype.card_option, Fintype.card_fin] using hcard

lemma no_four_cycle_active_points_clause_count {P L r k : ℕ}
    (I H : Fin P → Fin L → Prop) (p : Fin r → Fin P) (l : Fin r → Fin L)
    (hp : Function.Injective p) (hsub : ∀ a b, H a b → I a b)
    (hdiag : ∀ i : Fin r, H (p i) (l i))
    (hfour : ∀ a a' : Fin P, a ≠ a' → ∀ b b' : Fin L,
      I a b → I a' b → I a b' → I a' b' → b = b')
    (hcollision : ∀ i j : Fin r, i ≠ j → l i = l j →
      (∃ b, H (p i) b ∧ b ≠ l i) ∨ (∃ b, H (p j) b ∧ b ≠ l j))
    (Sp : Fin k → Fin P → Prop) (Sl : Fin k → Fin L → Prop)
    (hcover : ∀ c : Fin k, ∀ a b, H a b → Sp c a ∨ Sl c b)
    (hsafe : ∀ (x : Fin P → Bool) (y : Fin L → Bool),
      (∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ x a = true) ∨
        (∃ b : Fin L, Sl c b ∧ y b = true)) →
      ∃ a b, I a b ∧ x a = true ∧ y b = true) :
    r + 1 ≤ k := by
  apply separated_active_points_clause_count I H p Sp Sl
    (fun i => ⟨l i, hdiag i⟩) ?_ hcover hsafe
  intro i j hij
  have hpp : p i ≠ p j := fun h => hij (hp h)
  by_cases hli : ¬ I (p j) (l i)
  · exact ⟨l i, Or.inl ⟨hdiag i, hli⟩⟩
  by_cases hlj : ¬ I (p i) (l j)
  · exact ⟨l j, Or.inr ⟨hdiag j, hlj⟩⟩
  have hcrossi : I (p j) (l i) := Classical.not_not.mp hli
  have hcrossj : I (p i) (l j) := Classical.not_not.mp hlj
  have heq : l i = l j := hfour (p i) (p j) hpp (l i) (l j)
    (hsub _ _ (hdiag i)) hcrossi hcrossj (hsub _ _ (hdiag j))
  rcases hcollision i j hij heq with ⟨b, hb, hne⟩ | ⟨b, hb, hne⟩
  · refine ⟨b, Or.inl ⟨hb, ?_⟩⟩
    intro hother
    exact hne (hfour (p i) (p j) hpp b (l i)
      (hsub _ _ hb) hother (hsub _ _ (hdiag i)) hcrossi)
  · refine ⟨b, Or.inr ⟨hb, ?_⟩⟩
    intro hother
    exact hne (hfour (p i) (p j) hpp b (l j)
      hother (hsub _ _ hb) hcrossj (hsub _ _ (hdiag j)))

end ActivePointCNF


namespace ProductFactor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.CircuitMoves
  PEqualNP.MetaComplexity.NestedCover

def appendOr (D : Circuit) (a b : ℕ) : Circuit :=
  ⟨D.gates ++ [⟨GateOp.or, [a, b]⟩], D.output⟩

lemma appendOr_size (D : Circuit) (a b : ℕ) :
    (appendOr D a b).size = D.size + 1 := by
  simp [appendOr, Circuit.size]

lemma old_wire_appendOr (n : ℕ) (D : Circuit) (a b w : ℕ)
    (hw : w < n + D.size) (x : Fin n → Bool) :
    PEqualNP.BlindGate.wireValue (appendOr D a b) n x w =
      PEqualNP.BlindGate.wireValue D n x w := by
  unfold PEqualNP.BlindGate.wireValue Circuit.wires appendOr
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  apply List.getD_append
  change w < (D.gates.foldl SplitAux.wireStep (List.ofFn x)).length
  rw [SplitAux.foldl_wireStep_length, List.length_ofFn]
  exact hw

lemma appendOr_gate (D : Circuit) (a b : ℕ) :
    gateAt (appendOr D a b) D.gates.length = ⟨GateOp.or, [a, b]⟩ := by
  simp [gateAt, appendOr, List.getD_eq_getElem?_getD]

lemma appendOr_ao2 (n : ℕ) (D : Circuit) (a b : ℕ) (hD : IsAO2 n D)
    (ha : a < n + D.size) (hb : b < n + D.size) : IsAO2 n (appendOr D a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [appendOr, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hD.1 g hg
    · exact Or.inr rfl
  · intro j hj w hw
    have hlen : (appendOr D a b).gates.length = D.gates.length + 1 := by
      simp [appendOr]
    by_cases hjD : j < D.gates.length
    · have heq : gateAt (appendOr D a b) j = gateAt D j := by
        simp only [gateAt, appendOr]
        exact List.getD_append _ _ _ _ hjD
      rw [heq] at hw
      exact hD.2.1 j hjD w hw
    · have hjeq : j = D.gates.length := by omega
      subst j
      rw [appendOr_gate] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact ha
      · exact hb
  · intro g hg
    simp only [appendOr, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hD.2.2 g hg
    · rfl

lemma new_wire_appendOr (n : ℕ) (D : Circuit) (a b : ℕ) (hD : IsAO2 n D)
    (ha : a < n + D.size) (hb : b < n + D.size) (x : Fin n → Bool) :
    PEqualNP.BlindGate.wireValue (appendOr D a b) n x (n + D.size) =
      (PEqualNP.BlindGate.wireValue D n x a || PEqualNP.BlindGate.wireValue D n x b) := by
  have hD' := appendOr_ao2 n D a b hD ha hb
  change PEqualNP.BlindGate.wireValue (appendOr D a b) n x (n + D.gates.length) = _
  rw [SplitAux.wireValue_gate n (appendOr D a b) x D.gates.length (by simp [appendOr]) hD'.2.1]
  rw [appendOr_gate]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
    Bool.or_false, id_eq]
  rw [old_wire_appendOr n D a b a ha x, old_wire_appendOr n D a b b hb x]

lemma appendOr_nonbelow (n : ℕ) (D : Circuit) (a b : ℕ) (F : (Fin n → Bool) → Bool)
    (hD : IsAO2 n D) (ha : a < n + D.size) (hb : b < n + D.size)
    (hold : ∀ j < D.size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x (n + j) = true ∧ F x = false)
    (haF : ∃ x : Fin n → Bool, PEqualNP.BlindGate.wireValue D n x a = true ∧ F x = false) :
    ∀ j < (appendOr D a b).size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue (appendOr D a b) n x (n + j) = true ∧ F x = false := by
  intro j hj
  rw [appendOr_size] at hj
  by_cases hjD : j < D.size
  · obtain ⟨x, hx, hF⟩ := hold j hjD
    refine ⟨x, ?_, hF⟩
    rwa [old_wire_appendOr n D a b (n + j) (by omega) x]
  · have hjEq : j = D.size := by omega
    subst j
    obtain ⟨x, hx, hF⟩ := haF
    refine ⟨x, ?_, hF⟩
    rw [new_wire_appendOr n D a b hD ha hb x, hx]
    rfl

lemma factor_pair_semantics (n : ℕ) (D : Circuit) (J a b : ℕ)
    (R : List (ℕ × ℕ)) (hD : IsAO2 n D)
    (hJ : J < n + D.size) (ha : a < n + D.size) (hb : b < n + D.size)
    (hR : ∀ t ∈ R, t.1 < n + D.size ∧ t.2 < n + D.size)
    (x : Fin n → Bool) :
    (∃ t ∈ (J, a) :: (J, b) :: R,
      PEqualNP.BlindGate.wireValue D n x t.1 = true ∧
      PEqualNP.BlindGate.wireValue D n x t.2 = true) ↔
    ∃ t ∈ (J, n + D.size) :: R,
      PEqualNP.BlindGate.wireValue (appendOr D a b) n x t.1 = true ∧
      PEqualNP.BlindGate.wireValue (appendOr D a b) n x t.2 = true := by
  have hrest : (∃ t ∈ R,
      PEqualNP.BlindGate.wireValue D n x t.1 = true ∧
      PEqualNP.BlindGate.wireValue D n x t.2 = true) ↔
      ∃ t ∈ R,
        PEqualNP.BlindGate.wireValue (appendOr D a b) n x t.1 = true ∧
        PEqualNP.BlindGate.wireValue (appendOr D a b) n x t.2 = true := by
    apply exists_congr
    intro t
    constructor
    · rintro ⟨ht, ht1, ht2⟩
      exact ⟨ht, by rwa [old_wire_appendOr n D a b t.1 (hR t ht).1 x],
        by rwa [old_wire_appendOr n D a b t.2 (hR t ht).2 x]⟩
    · rintro ⟨ht, ht1, ht2⟩
      exact ⟨ht, by rwa [old_wire_appendOr n D a b t.1 (hR t ht).1 x] at ht1,
        by rwa [old_wire_appendOr n D a b t.2 (hR t ht).2 x] at ht2⟩
  simp only [List.mem_cons, exists_eq_or_imp] at *
  rw [old_wire_appendOr n D a b J hJ x, new_wire_appendOr n D a b hD ha hb x,
    Bool.or_eq_true, ← hrest]
  tauto

lemma factor_pair_cost (D : Circuit) (n J a b : ℕ) (R : List (ℕ × ℕ)) :
    (appendOr D a b).size + 2 * ((J, n + D.size) :: R).length + 1 =
      D.size + 2 * ((J, a) :: (J, b) :: R).length := by
  rw [appendOr_size]
  simp only [List.length_cons]
  omega


lemma invalid_wire_false (n : ℕ) (D : Circuit) (w : ℕ)
    (hw : n + D.size ≤ w) (x : Fin n → Bool) :
    PEqualNP.BlindGate.wireValue D n x w = false := by
  unfold PEqualNP.BlindGate.wireValue Circuit.wires
  change (D.gates.foldl SplitAux.wireStep (List.ofFn x)).getD w false = false
  apply List.getD_eq_default
  rw [SplitAux.foldl_wireStep_length, List.length_ofFn]
  exact hw

def validPairs (n : ℕ) (D : Circuit) (B : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  B.filter (fun t => decide (t.1 < n + D.size ∧ t.2 < n + D.size))

lemma mem_validPairs (n : ℕ) (D : Circuit) (B : List (ℕ × ℕ)) (t : ℕ × ℕ) :
    t ∈ validPairs n D B ↔ t ∈ B ∧ t.1 < n + D.size ∧ t.2 < n + D.size := by
  simp [validPairs]

lemma validPairs_length_le (n : ℕ) (D : Circuit) (B : List (ℕ × ℕ)) :
    (validPairs n D B).length ≤ B.length := by
  exact List.length_filter_le _ _

lemma validPairs_semantics (n : ℕ) (D : Circuit) (B : List (ℕ × ℕ))
    (x : Fin n → Bool) :
    (∃ t ∈ B, PEqualNP.BlindGate.wireValue D n x t.1 = true ∧
      PEqualNP.BlindGate.wireValue D n x t.2 = true) ↔
    ∃ t ∈ validPairs n D B, PEqualNP.BlindGate.wireValue D n x t.1 = true ∧
      PEqualNP.BlindGate.wireValue D n x t.2 = true := by
  constructor
  · rintro ⟨t, ht, h1, h2⟩
    have hb1 : t.1 < n + D.size := by
      by_contra h
      rw [invalid_wire_false n D t.1 (by omega) x] at h1
      cases h1
    have hb2 : t.2 < n + D.size := by
      by_contra h
      rw [invalid_wire_false n D t.2 (by omega) x] at h2
      cases h2
    exact ⟨t, (mem_validPairs n D B t).mpr ⟨ht, hb1, hb2⟩, h1, h2⟩
  · rintro ⟨t, ht, h1, h2⟩
    exact ⟨t, ((mem_validPairs n D B t).mp ht).1, h1, h2⟩

lemma factor_pair_package (n : ℕ) (D : Circuit) (J a b : ℕ)
    (R : List (ℕ × ℕ)) (F : (Fin n → Bool) → Bool)
    (hD : IsAO2 n D)
    (hbound : ∀ t ∈ (J, a) :: (J, b) :: R,
      t.1 < n + D.size ∧ t.2 < n + D.size)
    (hnot : ∀ w < n + D.size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x w = true ∧ F x = false)
    (hF : ∀ x : Fin n → Bool, F x = true ↔ ∃ t ∈ (J, a) :: (J, b) :: R,
      PEqualNP.BlindGate.wireValue D n x t.1 = true ∧
      PEqualNP.BlindGate.wireValue D n x t.2 = true) :
    ∃ (E : Circuit) (A : List (ℕ × ℕ)), IsAO2 n E ∧
      (∀ t ∈ A, t.1 < n + E.size ∧ t.2 < n + E.size) ∧
      (∀ w < n + E.size, ∃ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue E n x w = true ∧ F x = false) ∧
      (∀ x : Fin n → Bool, F x = true ↔ ∃ t ∈ A,
        PEqualNP.BlindGate.wireValue E n x t.1 = true ∧
        PEqualNP.BlindGate.wireValue E n x t.2 = true) ∧
      E.size + 2 * A.length + 1 = D.size + 2 * ((J, a) :: (J, b) :: R).length := by
  have hb1 := hbound (J, a) (by simp)
  have hb2 := hbound (J, b) (by simp)
  have hR : ∀ t ∈ R, t.1 < n + D.size ∧ t.2 < n + D.size := by
    intro t ht
    exact hbound t (by simp [ht])
  refine ⟨appendOr D a b, (J, n + D.size) :: R,
    appendOr_ao2 n D a b hD hb1.2 hb2.2, ?_, ?_, ?_, factor_pair_cost D n J a b R⟩
  · intro t ht
    rw [appendOr_size]
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · simpa using (show J < n + (D.size + 1) ∧ n + D.size < n + (D.size + 1) by omega)
    · have := hR t ht
      constructor <;> omega
  · intro w hw
    rw [appendOr_size] at hw
    by_cases hwold : w < n + D.size
    · obtain ⟨x, hx, hfalse⟩ := hnot w hwold
      exact ⟨x, by rwa [old_wire_appendOr n D a b w hwold x], hfalse⟩
    · have heq : w = n + D.size := by omega
      subst w
      obtain ⟨x, hx, hfalse⟩ := hnot a hb1.2
      refine ⟨x, ?_, hfalse⟩
      rw [new_wire_appendOr n D a b hD hb1.2 hb2.2 x, hx]
      rfl
  · intro x
    exact (hF x).trans (factor_pair_semantics n D J a b R hD hb1.1 hb1.2 hb2.2 hR x)


def IsResidual (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) : Prop :=
  IsAO2 n D ∧
  (∀ t ∈ B, t.1 < n + D.size ∧ t.2 < n + D.size) ∧
  (∀ w < n + D.size, ∃ x : Fin n → Bool,
    PEqualNP.BlindGate.wireValue D n x w = true ∧ F x = false) ∧
  (∀ x : Fin n → Bool, F x = true ↔ ∃ t ∈ B,
    PEqualNP.BlindGate.wireValue D n x t.1 = true ∧
    PEqualNP.BlindGate.wireValue D n x t.2 = true)

lemma factor_oriented_pairs (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (hres : IsResidual n F D B)
    (t s : ℕ × ℕ) (R : List (ℕ × ℕ)) (hperm : B.Perm (t :: s :: R))
    (J a b : ℕ) (ht : t = (J, a) ∨ t = (a, J))
    (hs : s = (J, b) ∨ s = (b, J)) :
    ∃ (E : Circuit) (A : List (ℕ × ℕ)), IsResidual n F E A ∧
      E.size + 2 * A.length + 1 = D.size + 2 * B.length := by
  have htb := hres.2.1 t ((hperm.mem_iff).mpr (by simp))
  have hsb := hres.2.1 s ((hperm.mem_iff).mpr (by simp))
  have hJ : J < n + D.size := by rcases ht with rfl | rfl <;> tauto
  have ha : a < n + D.size := by rcases ht with rfl | rfl <;> tauto
  have hb : b < n + D.size := by rcases hs with rfl | rfl <;> tauto
  have hR : ∀ v ∈ R, v.1 < n + D.size ∧ v.2 < n + D.size := by
    intro v hv
    exact hres.2.1 v ((hperm.mem_iff).mpr (by simp [hv]))
  have hbound : ∀ v ∈ (J, a) :: (J, b) :: R,
      v.1 < n + D.size ∧ v.2 < n + D.size := by
    intro v hv
    simp only [List.mem_cons] at hv
    rcases hv with rfl | rfl | hv
    · exact ⟨hJ, ha⟩
    · exact ⟨hJ, hb⟩
    · exact hR v hv
  have hfun : ∀ x : Fin n → Bool, F x = true ↔ ∃ v ∈ (J, a) :: (J, b) :: R,
      PEqualNP.BlindGate.wireValue D n x v.1 = true ∧
      PEqualNP.BlindGate.wireValue D n x v.2 = true := by
    intro x
    rw [hres.2.2.2 x]
    simp only [hperm.mem_iff, List.mem_cons, exists_eq_or_imp]
    rcases ht with rfl | rfl <;> rcases hs with rfl | rfl <;> simp only <;> tauto
  obtain ⟨E, A, hAO, hbd, hnot, hF, hcost⟩ :=
    factor_pair_package n D J a b R F hres.1 hbound hres.2.2.1 hfun
  refine ⟨E, A, ⟨hAO, hbd, hnot, hF⟩, ?_⟩
  simpa only [hperm.length_eq, List.length_cons] using hcost

lemma factor_shared_pairs (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (hres : IsResidual n F D B)
    (t s : ℕ × ℕ) (R : List (ℕ × ℕ)) (hperm : B.Perm (t :: s :: R))
    (hshare : t.1 = s.1 ∨ t.1 = s.2 ∨ t.2 = s.1 ∨ t.2 = s.2) :
    ∃ (E : Circuit) (A : List (ℕ × ℕ)), IsResidual n F E A ∧
      E.size + 2 * A.length + 1 = D.size + 2 * B.length := by
  rcases t with ⟨u, v⟩
  rcases s with ⟨w, z⟩
  simp only at hshare
  rcases hshare with h | h | h | h
  · subst w
    exact factor_oriented_pairs n F D B hres (u, v) (u, z) R hperm u v z
      (Or.inl rfl) (Or.inl rfl)
  · subst z
    exact factor_oriented_pairs n F D B hres (u, v) (w, u) R hperm u v w
      (Or.inl rfl) (Or.inr rfl)
  · subst w
    exact factor_oriented_pairs n F D B hres (u, v) (v, z) R hperm v u z
      (Or.inr rfl) (Or.inl rfl)
  · subst z
    exact factor_oriented_pairs n F D B hres (u, v) (w, v) R hperm v u w
      (Or.inr rfl) (Or.inr rfl)

lemma pairwise_of_pair_perm (B : List (ℕ × ℕ)) (R : (ℕ × ℕ) → (ℕ × ℕ) → Prop)
    (h : ∀ t s T, B.Perm (t :: s :: T) → R t s) : B.Pairwise R := by
  induction B with
  | nil => simp
  | cons t B ih =>
    rw [List.pairwise_cons]
    constructor
    · intro s hs
      exact h t s (B.erase s) ((List.perm_cons_erase hs).cons t)
    · apply ih
      intro s u T hp
      apply h s u (t :: T)
      exact (hp.cons t).trans ((List.Perm.swap s t (u :: T)).trans
        ((List.Perm.swap u t T).cons s))

lemma minimum_residual_matching (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (hres : IsResidual n F D B)
    (hmin : ∀ (E : Circuit) (A : List (ℕ × ℕ)), IsResidual n F E A →
      D.size + 2 * B.length ≤ E.size + 2 * A.length) :
    (∀ t ∈ B, t.1 ≠ t.2) ∧
    B.Pairwise (fun t s => t.1 ≠ s.1 ∧ t.1 ≠ s.2 ∧ t.2 ≠ s.1 ∧ t.2 ≠ s.2) := by
  constructor
  · intro t ht heq
    obtain ⟨x, hx, hfalse⟩ := hres.2.2.1 t.1 (hres.2.1 t ht).1
    have htrue : F x = true := (hres.2.2.2 x).mpr ⟨t, ht, hx, by rwa [← heq]⟩
    rw [hfalse] at htrue
    cases htrue
  · apply pairwise_of_pair_perm
    intro t s R hp
    by_contra h
    have hshare : t.1 = s.1 ∨ t.1 = s.2 ∨ t.2 = s.1 ∨ t.2 = s.2 := by tauto
    obtain ⟨E, A, hEA, hcost⟩ := factor_shared_pairs n F D B hres t s R hp hshare
    have := hmin E A hEA
    omega

lemma exists_minimum_residual_matching (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (hres : IsResidual n F D B) :
    ∃ (E : Circuit) (A : List (ℕ × ℕ)), IsResidual n F E A ∧
      E.size + 2 * A.length ≤ D.size + 2 * B.length ∧
      (∀ t ∈ A, t.1 ≠ t.2) ∧
      A.Pairwise (fun t s => t.1 ≠ s.1 ∧ t.1 ≠ s.2 ∧ t.2 ≠ s.1 ∧ t.2 ≠ s.2) := by
  classical
  let P : ℕ → Prop := fun k => ∃ (E : Circuit) (A : List (ℕ × ℕ)),
    IsResidual n F E A ∧ E.size + 2 * A.length = k
  have hex : ∃ k, P k := ⟨D.size + 2 * B.length, D, B, hres, rfl⟩
  obtain ⟨E, A, hEA, hcost⟩ := Nat.find_spec hex
  have hmin : ∀ (D' : Circuit) (B' : List (ℕ × ℕ)), IsResidual n F D' B' →
      E.size + 2 * A.length ≤ D'.size + 2 * B'.length := by
    intro D' B' h'
    rw [hcost]
    exact Nat.find_min' hex ⟨D', B', h', rfl⟩
  exact ⟨E, A, hEA, hmin D B hres, minimum_residual_matching n F E A hEA hmin⟩


lemma residual_of_decomposition (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (hD : IsAO2 n D)
    (hinput : ∀ i : Fin n, ∃ x : Fin n → Bool, x i = true ∧ F x = false)
    (hnot : ∀ j < D.size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x (n + j) = true ∧ F x = false)
    (hF : ∀ x : Fin n → Bool, F x = true ↔ ∃ t ∈ B,
      PEqualNP.BlindGate.wireValue D n x t.1 = true ∧
      PEqualNP.BlindGate.wireValue D n x t.2 = true) :
    IsResidual n F D (validPairs n D B) := by
  refine ⟨hD, ?_, ?_, ?_⟩
  · intro t ht
    exact ((mem_validPairs n D B t).mp ht).2
  · intro w hw
    by_cases hwi : w < n
    · obtain ⟨x, hx, hfalse⟩ := hinput ⟨w, hwi⟩
      refine ⟨x, ?_, hfalse⟩
      rwa [SplitAux.wireValue_input n D x w hwi]
    · obtain ⟨x, hx, hfalse⟩ := hnot (w - n) (by omega)
      refine ⟨x, ?_, hfalse⟩
      simpa only [Nat.add_sub_of_le (by omega : n ≤ w)] using hx
  · intro x
    exact (hF x).trans (validPairs_semantics n D B x)

lemma not_below_input_witnesses (n : ℕ) (C : Circuit)
    (hinputs : ∀ w < n, ¬ WireBelowOutput n C w) :
    ∀ i : Fin n, ∃ x : Fin n → Bool, x i = true ∧ circuitFun n C x = false := by
  classical
  intro i
  have hn := hinputs i.val i.isLt
  change ¬ ∀ x : Fin n → Bool,
    PEqualNP.BlindGate.wireValue C n x i.val = true → circuitFun n C x = true at hn
  push_neg at hn
  obtain ⟨x, hx, hfalse⟩ := hn
  refine ⟨x, ?_, by simpa only [Bool.not_eq_true] using hfalse⟩
  simpa only [SplitAux.wireValue_input n C x i.val i.isLt] using hx

lemma matching_product_decomposition (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hout : C.output < n + C.size)
    (hinputs : ∀ w < n, ¬ WireBelowOutput n C w) :
    ∃ (D : Circuit) (B : List (ℕ × ℕ)), IsResidual n (circuitFun n C) D B ∧
      D.size + 2 * B.length ≤ C.size + 1 ∧
      (∀ t ∈ B, t.1 ≠ t.2) ∧
      B.Pairwise (fun t s => t.1 ≠ s.1 ∧ t.1 ≠ s.2 ∧ t.2 ≠ s.1 ∧ t.2 ≠ s.2) := by
  obtain ⟨D, B, hD, hnot, hF, hcost⟩ := product_decomposition n C hAO hout hinputs
  have hres := residual_of_decomposition n (circuitFun n C) D B hD
    (not_below_input_witnesses n C hinputs) hnot hF
  obtain ⟨E, A, hEA, hle, hloop, hpair⟩ :=
    exists_minimum_residual_matching n (circuitFun n C) D (validPairs n D B) hres
  refine ⟨E, A, hEA, ?_, hloop, hpair⟩
  have := validPairs_length_le n D B
  omega

lemma incidence_matching_product_decomposition (p l : ℕ) (I : Fin p → Fin l → Prop)
    [DecidableRel I] (C : Circuit) (hAO : IsAO2 (p + l) C) (hne : ∃ a b, I a b)
    (hF : ∀ z : Fin (p + l) → Bool, circuitFun (p + l) C z =
      decide (∃ a b, I a b ∧ z (Fin.castAdd l a) = true ∧ z (Fin.natAdd p b) = true)) :
    ∃ (D : Circuit) (B : List (ℕ × ℕ)), IsResidual (p + l) (circuitFun (p + l) C) D B ∧
      D.size + 2 * B.length ≤ C.size + 1 ∧
      (∀ t ∈ B, t.1 ≠ t.2) ∧
      B.Pairwise (fun t s => t.1 ≠ s.1 ∧ t.1 ≠ s.2 ∧ t.2 ≠ s.1 ∧ t.2 ≠ s.2) :=
  matching_product_decomposition (p + l) C hAO (incidence_output_valid p l I C hne hF)
    (incidence_no_input_below p l I C hF)

lemma plane_matching_product_decomposition :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit),
      2 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) →
      (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) →
      IsAO2 (N + N) C →
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z =
        decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
          z (Fin.natAdd N l) = true)) →
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' →
        ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) ∧
      ∃ (D : Circuit) (B : List (ℕ × ℕ)), IsResidual (N + N) (circuitFun (N + N) C) D B ∧
        D.size + 2 * B.length ≤ C.size + 1 ∧
        (∀ t ∈ B, t.1 ≠ t.2) ∧
        B.Pairwise (fun t s => t.1 ≠ s.1 ∧ t.1 ≠ s.2 ∧ t.2 ≠ s.1 ∧ t.2 ≠ s.2) := by
  intro q N I inst C hq hN hlines huniq hAO hF
  have hfour := (plane_product_decomposition q N I C hq hN hlines huniq hAO hF).1
  have hNpos : 0 < N := by omega
  let l0 : Fin N := ⟨0, hNpos⟩
  have hpoints : (Finset.univ.filter (fun p => I p l0)).Nonempty := by
    apply Finset.card_pos.mp
    rw [hlines l0]
    omega
  obtain ⟨p0, hp0⟩ := hpoints
  have hne : ∃ p l : Fin N, I p l := ⟨p0, l0, (Finset.mem_filter.mp hp0).2⟩
  exact ⟨hfour, incidence_matching_product_decomposition N N I C hAO hne hF⟩

end ProductFactor


namespace CoreClauses

lemma option_elim_injective {α β : Type} (b : β) (f : α → β)
    (hf : Function.Injective f) (hneq : ∀ a, f a ≠ b) :
    Function.Injective (fun a : Option α => a.elim b f) := by
  intro a c h
  cases a with
  | none =>
    cases c with
    | none => rfl
    | some c => exact False.elim (hneq c h.symm)
  | some a =>
    cases c with
    | none => exact False.elim (hneq a h)
    | some c => exact congrArg some (hf h)

lemma outside_separated_active_clause_surplus {P L r k : ℕ}
    (I H : Fin P → Fin L → Prop) (p : Fin r → Fin P)
    (Sp : Fin k → Fin P → Prop) (Sl : Fin k → Fin L → Prop)
    (hactive : ∀ i : Fin r, ∃ l, H (p i) l)
    (hseparate : ∀ i j : Fin r, i ≠ j →
      ∃ l, (H (p i) l ∧ ¬ I (p j) l) ∨ (H (p j) l ∧ ¬ I (p i) l))
    (houtside : ∀ i : Fin r, ∃ a : Fin P, ∃ l, H a l ∧ ¬ I (p i) l)
    (hcover : ∀ c : Fin k, ∀ a b, H a b → Sp c a ∨ Sl c b)
    (hsafe : ∀ (x : Fin P → Bool) (y : Fin L → Bool),
      (∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ x a = true) ∨
        (∃ b : Fin L, Sl c b ∧ y b = true)) →
      ∃ a b, I a b ∧ x a = true ∧ y b = true)
    (hr : 1 ≤ r) : r + 2 ≤ k := by
  classical
  have hpointBase : ∃ c : Fin k, ∀ a, ¬ Sp c a := by
    by_contra h
    have hits : ∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ (true : Bool) = true) ∨
        (∃ b : Fin L, Sl c b ∧ (false : Bool) = true) := by
      intro c
      have hex : ∃ a, Sp c a := by
        by_contra hn
        exact h ⟨c, fun a ha => hn ⟨a, ha⟩⟩
      obtain ⟨a, ha⟩ := hex
      exact Or.inl ⟨a, ha, rfl⟩
    obtain ⟨a, b, hab, ha, hb⟩ := hsafe (fun _ => true) (fun _ => false) hits
    cases hb
  have hlineBase : ∃ c : Fin k, ∀ b, ¬ Sl c b := by
    by_contra h
    have hits : ∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ (false : Bool) = true) ∨
        (∃ b : Fin L, Sl c b ∧ (true : Bool) = true) := by
      intro c
      have hex : ∃ b, Sl c b := by
        by_contra hn
        exact h ⟨c, fun b hb => hn ⟨b, hb⟩⟩
      obtain ⟨b, hb⟩ := hex
      exact Or.inr ⟨b, hb, rfl⟩
    obtain ⟨a, b, hab, ha, hb⟩ := hsafe (fun _ => false) (fun _ => true) hits
    cases ha
  have hpoint : ∀ i : Fin r, ∃ c : Fin k,
      ¬ Sp c (p i) ∧ ∀ b, ¬ I (p i) b → ¬ Sl c b := by
    intro i
    let x : Fin P → Bool := fun a => decide (a = p i)
    let y : Fin L → Bool := fun b => decide (¬ I (p i) b)
    by_contra h
    have hits : ∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ x a = true) ∨
        (∃ b : Fin L, Sl c b ∧ y b = true) := by
      intro c
      by_cases hp : Sp c (p i)
      · exact Or.inl ⟨p i, hp, by simp [x]⟩
      · have hex : ∃ b, ¬ I (p i) b ∧ Sl c b := by
          by_contra hn
          exact h ⟨c, hp, fun b hnb hb => hn ⟨b, hnb, hb⟩⟩
        obtain ⟨b, hnb, hb⟩ := hex
        exact Or.inr ⟨b, hb, by simp [y, hnb]⟩
    obtain ⟨a, b, hab, ha, hb⟩ := hsafe x y hits
    have hap : a = p i := by simpa only [x, decide_eq_true_eq] using ha
    have hnb : ¬ I (p i) b := by simpa only [y, decide_eq_true_eq] using hb
    exact hnb (hap ▸ hab)
  obtain ⟨cP, hcP⟩ := hpointBase
  obtain ⟨cL, hcL⟩ := hlineBase
  choose c hc using hpoint
  have hLP : cL ≠ cP := by
    intro h
    let i : Fin r := ⟨0, by omega⟩
    obtain ⟨b, hb⟩ := hactive i
    rcases hcover cL (p i) b hb with hp | hl
    · rw [h] at hp
      exact hcP (p i) hp
    · exact hcL b hl
  have hcL_ne (i : Fin r) : c i ≠ cL := by
    intro h
    obtain ⟨b, hb⟩ := hactive i
    rcases hcover (c i) (p i) b hb with hp | hl
    · exact (hc i).1 hp
    · rw [h] at hl
      exact hcL b hl
  have hcP_ne (i : Fin r) : c i ≠ cP := by
    intro h
    obtain ⟨a, b, hb, hnb⟩ := houtside i
    rcases hcover (c i) a b hb with hp | hl
    · rw [h] at hp
      exact hcP a hp
    · exact (hc i).2 b hnb hl
  have hcinj : Function.Injective c := by
    intro i j h
    by_contra hij
    obtain ⟨b, hb | hb⟩ := hseparate i j hij
    · rcases hcover (c i) (p i) b hb.1 with hp | hl
      · exact (hc i).1 hp
      · rw [h] at hl
        exact (hc j).2 b hb.2 hl
    · rcases hcover (c j) (p j) b hb.1 with hp | hl
      · exact (hc j).1 hp
      · rw [← h] at hl
        exact (hc i).2 b hb.2 hl
  let g : Option (Fin r) → Fin k := fun i => i.elim cL c
  have hginj : Function.Injective g := option_elim_injective cL c hcinj hcL_ne
  have hgP : ∀ i, g i ≠ cP := by
    intro i
    cases i with
    | none => exact hLP
    | some i => exact hcP_ne i
  have hinj := option_elim_injective cP g hginj hgP
  have hcard := Fintype.card_le_of_injective _ hinj
  simpa only [Fintype.card_option, Fintype.card_fin, Nat.add_assoc] using hcard

lemma directed_separated_active_clause_surplus {P L r k : ℕ}
    (I H : Fin P → Fin L → Prop) (p : Fin r → Fin P)
    (Sp : Fin k → Fin P → Prop) (Sl : Fin k → Fin L → Prop)
    (hactive : ∀ i : Fin r, ∃ l, H (p i) l)
    (hdirected : ∀ i j : Fin r, i ≠ j → ∃ l, H (p j) l ∧ ¬ I (p i) l)
    (hcover : ∀ c : Fin k, ∀ a b, H a b → Sp c a ∨ Sl c b)
    (hsafe : ∀ (x : Fin P → Bool) (y : Fin L → Bool),
      (∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ x a = true) ∨
        (∃ b : Fin L, Sl c b ∧ y b = true)) →
      ∃ a b, I a b ∧ x a = true ∧ y b = true)
    (hr : 2 ≤ r) : r + 2 ≤ k := by
  apply outside_separated_active_clause_surplus I H p Sp Sl hactive ?_ ?_ hcover hsafe (by omega)
  · intro i j hij
    obtain ⟨b, hb⟩ := hdirected i j hij
    exact ⟨b, Or.inr hb⟩
  · intro i
    have hex : ∃ j : Fin r, i ≠ j := by
      by_cases hi : i.val = 0
      · refine ⟨⟨1, by omega⟩, ?_⟩
        intro h
        have hh := congrArg Fin.val h
        change i.val = 1 at hh
        omega
      · refine ⟨⟨0, by omega⟩, ?_⟩
        intro h
        exact hi (congrArg Fin.val h)
    obtain ⟨j, hij⟩ := hex
    obtain ⟨b, hb⟩ := hdirected i j hij
    exact ⟨p j, b, hb⟩

lemma two_neighbors_directed_separation {P L r : ℕ}
    (I H : Fin P → Fin L → Prop) (p : Fin r → Fin P)
    (hp : Function.Injective p) (hsub : ∀ a b, H a b → I a b)
    (hfour : ∀ a a' : Fin P, a ≠ a' → ∀ b b' : Fin L,
      I a b → I a' b → I a b' → I a' b' → b = b')
    (htwo : ∀ i : Fin r, ∃ b b', b ≠ b' ∧ H (p i) b ∧ H (p i) b') :
    ∀ i j : Fin r, i ≠ j → ∃ b, H (p j) b ∧ ¬ I (p i) b := by
  intro i j hij
  obtain ⟨b, b', hbb', hjb, hjb'⟩ := htwo j
  by_cases hib : I (p i) b
  · refine ⟨b', hjb', ?_⟩
    intro hib'
    have hpp : p i ≠ p j := fun h => hij (hp h)
    exact hbb' (hfour (p i) (p j) hpp b b' hib (hsub _ _ hjb) hib' (hsub _ _ hjb'))
  · exact ⟨b, hjb, hib⟩

lemma no_four_cycle_two_neighbor_clause_surplus {P L r k : ℕ}
    (I H : Fin P → Fin L → Prop) (p : Fin r → Fin P)
    (hp : Function.Injective p) (hsub : ∀ a b, H a b → I a b)
    (hfour : ∀ a a' : Fin P, a ≠ a' → ∀ b b' : Fin L,
      I a b → I a' b → I a b' → I a' b' → b = b')
    (htwo : ∀ i : Fin r, ∃ b b', b ≠ b' ∧ H (p i) b ∧ H (p i) b')
    (Sp : Fin k → Fin P → Prop) (Sl : Fin k → Fin L → Prop)
    (hcover : ∀ c : Fin k, ∀ a b, H a b → Sp c a ∨ Sl c b)
    (hsafe : ∀ (x : Fin P → Bool) (y : Fin L → Bool),
      (∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ x a = true) ∨
        (∃ b : Fin L, Sl c b ∧ y b = true)) →
      ∃ a b, I a b ∧ x a = true ∧ y b = true)
    (hr : 2 ≤ r) : r + 2 ≤ k := by
  apply directed_separated_active_clause_surplus I H p Sp Sl ?_
    (two_neighbors_directed_separation I H p hp hsub hfour htwo) hcover hsafe hr
  intro i
  obtain ⟨b, b', hbb', hb, hb'⟩ := htwo i
  exact ⟨b, hb⟩

lemma no_four_cycle_degree_two_clause_surplus {P L r k : ℕ}
    (I H : Fin P → Fin L → Prop) [DecidableRel H] (p : Fin r → Fin P)
    (hp : Function.Injective p) (hsub : ∀ a b, H a b → I a b)
    (hfour : ∀ a a' : Fin P, a ≠ a' → ∀ b b' : Fin L,
      I a b → I a' b → I a b' → I a' b' → b = b')
    (hdegree : ∀ i : Fin r, 2 ≤ (Finset.univ.filter (H (p i))).card)
    (Sp : Fin k → Fin P → Prop) (Sl : Fin k → Fin L → Prop)
    (hcover : ∀ c : Fin k, ∀ a b, H a b → Sp c a ∨ Sl c b)
    (hsafe : ∀ (x : Fin P → Bool) (y : Fin L → Bool),
      (∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ x a = true) ∨
        (∃ b : Fin L, Sl c b ∧ y b = true)) →
      ∃ a b, I a b ∧ x a = true ∧ y b = true)
    (hr : 2 ≤ r) : r + 2 ≤ k := by
  apply no_four_cycle_two_neighbor_clause_surplus I H p hp hsub hfour ?_ Sp Sl hcover hsafe hr
  intro i
  have hcard : 1 < (Finset.univ.filter (H (p i))).card := by have := hdegree i; omega
  obtain ⟨b, hb, b', hb', hbb'⟩ := Finset.one_lt_card.mp hcard
  exact ⟨b, b', hbb', (Finset.mem_filter.mp hb).2, (Finset.mem_filter.mp hb').2⟩

lemma outside_neighbor_of_two_neighbors {P L : ℕ}
    (I H : Fin P → Fin L → Prop) (a c : Fin P) (hac : a ≠ c)
    (hsub : ∀ u b, H u b → I u b)
    (hfour : ∀ u u' : Fin P, u ≠ u' → ∀ b b' : Fin L,
      I u b → I u' b → I u b' → I u' b' → b = b')
    (htwo : ∃ b b', b ≠ b' ∧ H c b ∧ H c b') :
    ∃ b, H c b ∧ ¬ I a b := by
  classical
  obtain ⟨b, b', hbb', hcb, hcb'⟩ := htwo
  by_cases hab : I a b
  · refine ⟨b', hcb', ?_⟩
    intro hab'
    exact hbb' (hfour a c hac b b' hab (hsub _ _ hcb) hab' (hsub _ _ hcb'))
  · exact ⟨b, hcb, hab⟩

lemma two_core_points_clause_surplus {P L r k : ℕ}
    (I H : Fin P → Fin L → Prop) (p : Fin r → Fin P)
    (u v : Fin P) (huv : u ≠ v)
    (hsub : ∀ a b, H a b → I a b)
    (hfour : ∀ a a' : Fin P, a ≠ a' → ∀ b b' : Fin L,
      I a b → I a' b → I a b' → I a' b' → b = b')
    (hu : ∃ b b', b ≠ b' ∧ H u b ∧ H u b')
    (hv : ∃ b b', b ≠ b' ∧ H v b ∧ H v b')
    (Sp : Fin k → Fin P → Prop) (Sl : Fin k → Fin L → Prop)
    (hactive : ∀ i : Fin r, ∃ l, H (p i) l)
    (hseparate : ∀ i j : Fin r, i ≠ j →
      ∃ l, (H (p i) l ∧ ¬ I (p j) l) ∨ (H (p j) l ∧ ¬ I (p i) l))
    (hcover : ∀ c : Fin k, ∀ a b, H a b → Sp c a ∨ Sl c b)
    (hsafe : ∀ (x : Fin P → Bool) (y : Fin L → Bool),
      (∀ c : Fin k,
        (∃ a : Fin P, Sp c a ∧ x a = true) ∨
        (∃ b : Fin L, Sl c b ∧ y b = true)) →
      ∃ a b, I a b ∧ x a = true ∧ y b = true)
    (hr : 1 ≤ r) : r + 2 ≤ k := by
  classical
  apply outside_separated_active_clause_surplus I H p Sp Sl hactive hseparate ?_
    hcover hsafe hr
  intro i
  by_cases hiu : p i = u
  · have hiv : p i ≠ v := fun h => huv (hiu.symm.trans h)
    obtain ⟨b, hb⟩ := outside_neighbor_of_two_neighbors I H (p i) v hiv hsub hfour hv
    exact ⟨v, b, hb⟩
  · obtain ⟨b, hb⟩ := outside_neighbor_of_two_neighbors I H (p i) u hiu hsub hfour hu
    exact ⟨u, b, hb⟩

end CoreClauses

namespace LastAndFactor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover
open ProductFactor

def appendAnd (D : Circuit) (a b : ℕ) : Circuit :=
  ⟨D.gates ++ [⟨GateOp.and, [a, b]⟩], D.output⟩

lemma appendAnd_size (D : Circuit) (a b : ℕ) :
    (appendAnd D a b).size = D.size + 1 := by
  simp [appendAnd, Circuit.size]

lemma old_wire_appendAnd (n : ℕ) (D : Circuit) (a b w : ℕ)
    (hw : w < n + D.size) (x : Fin n → Bool) :
    PEqualNP.BlindGate.wireValue (appendAnd D a b) n x w =
      PEqualNP.BlindGate.wireValue D n x w := by
  unfold PEqualNP.BlindGate.wireValue Circuit.wires appendAnd
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  apply List.getD_append
  change w < (D.gates.foldl SplitAux.wireStep (List.ofFn x)).length
  rw [SplitAux.foldl_wireStep_length, List.length_ofFn]
  exact hw

lemma appendAnd_gate (D : Circuit) (a b : ℕ) :
    gateAt (appendAnd D a b) D.gates.length = ⟨GateOp.and, [a, b]⟩ := by
  simp [gateAt, appendAnd, List.getD_eq_getElem?_getD]

lemma appendAnd_ao2 (n : ℕ) (D : Circuit) (a b : ℕ) (hD : IsAO2 n D)
    (ha : a < n + D.size) (hb : b < n + D.size) : IsAO2 n (appendAnd D a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [appendAnd, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hD.1 g hg
    · exact Or.inl rfl
  · intro j hj w hw
    have hlen : (appendAnd D a b).gates.length = D.gates.length + 1 := by
      simp [appendAnd]
    by_cases hjD : j < D.gates.length
    · have heq : gateAt (appendAnd D a b) j = gateAt D j := by
        simp only [gateAt, appendAnd]
        exact List.getD_append _ _ _ _ hjD
      rw [heq] at hw
      exact hD.2.1 j hjD w hw
    · have hjeq : j = D.gates.length := by omega
      subst j
      rw [appendAnd_gate] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl
      · exact ha
      · exact hb
  · intro g hg
    simp only [appendAnd, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hD.2.2 g hg
    · rfl

lemma new_wire_appendAnd (n : ℕ) (D : Circuit) (a b : ℕ) (hD : IsAO2 n D)
    (ha : a < n + D.size) (hb : b < n + D.size) (x : Fin n → Bool) :
    PEqualNP.BlindGate.wireValue (appendAnd D a b) n x (n + D.size) =
      (PEqualNP.BlindGate.wireValue D n x a && PEqualNP.BlindGate.wireValue D n x b) := by
  have hD' := appendAnd_ao2 n D a b hD ha hb
  change PEqualNP.BlindGate.wireValue (appendAnd D a b) n x (n + D.gates.length) = _
  rw [SplitAux.wireValue_gate n (appendAnd D a b) x D.gates.length (by simp [appendAnd]) hD'.2.1]
  rw [appendAnd_gate]
  simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
    Bool.and_true, id_eq]
  rw [old_wire_appendAnd n D a b a ha x, old_wire_appendAnd n D a b b hb x]



def products (n : ℕ) (D : Circuit) (B : List (ℕ × ℕ)) (x : Fin n → Bool) : Prop :=
  ∃ t ∈ B, PEqualNP.BlindGate.wireValue D n x t.1 = true ∧
    PEqualNP.BlindGate.wireValue D n x t.2 = true

lemma products_cons (n : ℕ) (D : Circuit) (t : ℕ × ℕ) (B : List (ℕ × ℕ))
    (x : Fin n → Bool) : products n D (t :: B) x ↔
    (PEqualNP.BlindGate.wireValue D n x t.1 = true ∧
      PEqualNP.BlindGate.wireValue D n x t.2 = true) ∨ products n D B x := by
  simp only [products, List.mem_cons, exists_eq_or_imp]

lemma products_congr (n : ℕ) (D E : Circuit) (B : List (ℕ × ℕ)) (x : Fin n → Bool)
    (h : ∀ t ∈ B,
      PEqualNP.BlindGate.wireValue D n x t.1 = PEqualNP.BlindGate.wireValue E n x t.1 ∧
      PEqualNP.BlindGate.wireValue D n x t.2 = PEqualNP.BlindGate.wireValue E n x t.2) :
    products n D B x ↔ products n E B x := by
  unfold products
  apply exists_congr
  intro t
  apply and_congr_right
  intro ht
  rw [(h t ht).1, (h t ht).2]

lemma products_appendAnd (n : ℕ) (E : Circuit) (u v : ℕ) (B : List (ℕ × ℕ))
    (hbound : ∀ t ∈ B, t.1 < n + E.size ∧ t.2 < n + E.size) (x : Fin n → Bool) :
    products n (appendAnd E u v) B x ↔ products n E B x := by
  apply products_congr
  intro t ht
  exact ⟨old_wire_appendAnd n E u v t.1 (hbound t ht).1 x,
    old_wire_appendAnd n E u v t.2 (hbound t ht).2 x⟩

lemma appendAnd_all_nonbelow (n : ℕ) (E : Circuit) (u v : ℕ)
    (F : (Fin n → Bool) → Bool) (hE : IsAO2 n E)
    (hu : u < n + E.size) (hv : v < n + E.size)
    (hold : ∀ w < n + E.size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E n x w = true ∧ F x = false)
    (hnew : ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E n x u = true ∧
      PEqualNP.BlindGate.wireValue E n x v = true ∧ F x = false) :
    ∀ w < n + (appendAnd E u v).size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue (appendAnd E u v) n x w = true ∧ F x = false := by
  intro w hw
  rw [appendAnd_size] at hw
  by_cases hwold : w < n + E.size
  · obtain ⟨x, hx, hfalse⟩ := hold w hwold
    exact ⟨x, by rwa [old_wire_appendAnd n E u v w hwold x], hfalse⟩
  · have heq : w = n + E.size := by omega
    subst w
    obtain ⟨x, hx1, hx2, hfalse⟩ := hnew
    refine ⟨x, ?_, hfalse⟩
    rw [new_wire_appendAnd n E u v hE hu hv x, hx1, hx2]
    rfl

lemma appendOr_all_nonbelow (n : ℕ) (E : Circuit) (u v : ℕ)
    (F : (Fin n → Bool) → Bool) (hE : IsAO2 n E)
    (hu : u < n + E.size) (hv : v < n + E.size)
    (hold : ∀ w < n + E.size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E n x w = true ∧ F x = false) :
    ∀ w < n + (appendOr E u v).size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue (appendOr E u v) n x w = true ∧ F x = false := by
  intro w hw
  rw [appendOr_size] at hw
  by_cases hwold : w < n + E.size
  · obtain ⟨x, hx, hfalse⟩ := hold w hwold
    exact ⟨x, by rwa [old_wire_appendOr n E u v w hwold x], hfalse⟩
  · have heq : w = n + E.size := by omega
    subst w
    obtain ⟨x, hx, hfalse⟩ := hold u hu
    refine ⟨x, ?_, hfalse⟩
    rw [new_wire_appendOr n E u v hE hu hv x, hx]
    rfl

lemma last_and_shared_endpoint_reduction (n : ℕ) (F : (Fin n → Bool) → Bool)
    (E : Circuit) (u v a b : ℕ) (R : List (ℕ × ℕ))
    (hE : IsAO2 n E)
    (hu : u < n + E.size) (hv : v < n + E.size)
    (ha : a < n + E.size) (hb : b < n + E.size)
    (hR : ∀ t ∈ R, t.1 < n + E.size ∧ t.2 < n + E.size)
    (hres : IsResidual n F (appendAnd E u v) ((n + E.size, a) :: (u, b) :: R)) :
    ∃ (D : Circuit) (B : List (ℕ × ℕ)), IsResidual n F D B ∧
      D.size + 2 * B.length + 1 =
        (appendAnd E u v).size + 2 * ((n + E.size, a) :: (u, b) :: R).length := by
  classical
  have hnotE : ∀ w < n + E.size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E n x w = true ∧ F x = false := by
    intro w hw
    obtain ⟨x, hx, hfalse⟩ := hres.2.2.1 w (by rw [appendAnd_size]; omega)
    exact ⟨x, by rwa [old_wire_appendAnd n E u v w hw x] at hx, hfalse⟩
  have hfold (x : Fin n → Bool) : F x = true ↔
      ((PEqualNP.BlindGate.wireValue E n x u = true ∧
        PEqualNP.BlindGate.wireValue E n x v = true) ∧
        PEqualNP.BlindGate.wireValue E n x a = true) ∨
      (PEqualNP.BlindGate.wireValue E n x u = true ∧
        PEqualNP.BlindGate.wireValue E n x b = true) ∨ products n E R x := by
    rw [hres.2.2.2 x]
    change products n (appendAnd E u v) ((n + E.size, a) :: (u, b) :: R) x ↔ _
    rw [products_cons, products_cons]
    rw [new_wire_appendAnd n E u v hE hu hv x,
      old_wire_appendAnd n E u v a ha x, old_wire_appendAnd n E u v u hu x,
      old_wire_appendAnd n E u v b hb x, products_appendAnd n E u v R hR x]
    simp only [Bool.and_eq_true]
  by_cases hbelow : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E n x v = true →
      PEqualNP.BlindGate.wireValue E n x a = true → F x = true
  · refine ⟨E, (v, a) :: (u, b) :: R, ⟨hE, ?_, hnotE, ?_⟩, ?_⟩
    · intro t ht
      simp only [List.mem_cons] at ht
      rcases ht with rfl | rfl | ht
      · exact ⟨hv, ha⟩
      · exact ⟨hu, hb⟩
      · exact hR t ht
    · intro x
      change F x = true ↔ products n E ((v, a) :: (u, b) :: R) x
      rw [products_cons, products_cons]
      have hf := hfold x
      have hsub := hbelow x
      tauto
    · rw [appendAnd_size]
      simp only [List.length_cons]
      omega
  · have hnew : ∃ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue E n x v = true ∧
        PEqualNP.BlindGate.wireValue E n x a = true ∧ F x = false := by
      push Not at hbelow
      obtain ⟨x, hx1, hx2, hfalse⟩ := hbelow
      exact ⟨x, hx1, hx2, by simpa only [Bool.not_eq_true] using hfalse⟩
    let T : Circuit := appendAnd E v a
    let t : ℕ := n + E.size
    have hT : IsAO2 n T := appendAnd_ao2 n E v a hE hv ha
    have hTsize : T.size = E.size + 1 := appendAnd_size E v a
    have ht : t < n + T.size := by dsimp [t]; omega
    have hbT : b < n + T.size := by omega
    have hnotT : ∀ w < n + T.size, ∃ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue T n x w = true ∧ F x = false :=
      appendAnd_all_nonbelow n E v a F hE hv ha hnotE hnew
    let D : Circuit := appendOr T t b
    let h : ℕ := n + T.size
    have hD : IsAO2 n D := appendOr_ao2 n T t b hT ht hbT
    have hDsize : D.size = E.size + 2 := by
      dsimp [D]
      rw [appendOr_size, hTsize]
    have hold (w : ℕ) (hw : w < n + E.size) (x : Fin n → Bool) :
        PEqualNP.BlindGate.wireValue D n x w = PEqualNP.BlindGate.wireValue E n x w := by
      dsimp [D]
      rw [old_wire_appendOr n T t b w (by omega) x]
      exact old_wire_appendAnd n E v a w hw x
    have hh (x : Fin n → Bool) : PEqualNP.BlindGate.wireValue D n x h =
        ((PEqualNP.BlindGate.wireValue E n x v &&
          PEqualNP.BlindGate.wireValue E n x a) ||
          PEqualNP.BlindGate.wireValue E n x b) := by
      dsimp [D, h]
      rw [new_wire_appendOr n T t b hT ht hbT x]
      change (PEqualNP.BlindGate.wireValue (appendAnd E v a) n x (n + E.size) ||
        PEqualNP.BlindGate.wireValue (appendAnd E v a) n x b) = _
      rw [new_wire_appendAnd n E v a hE hv ha x, old_wire_appendAnd n E v a b hb x]
    refine ⟨D, (u, h) :: R, ⟨hD, ?_, appendOr_all_nonbelow n T t b F hT ht hbT hnotT, ?_⟩, ?_⟩
    · intro s hs
      simp only [List.mem_cons] at hs
      rcases hs with rfl | hs
      · dsimp [h]
        constructor <;> omega
      · have := hR s hs
        constructor <;> omega
    · intro x
      change F x = true ↔ products n D ((u, h) :: R) x
      rw [products_cons]
      rw [hold u hu x, hh x]
      have hrest : products n D R x ↔ products n E R x := by
        apply products_congr
        intro s hs
        exact ⟨hold s.1 (hR s hs).1 x, hold s.2 (hR s hs).2 x⟩
      rw [hrest, Bool.or_eq_true, Bool.and_eq_true]
      have hf := hfold x
      tauto
    · rw [hDsize, appendAnd_size]
      simp only [List.length_cons]
      omega


lemma last_and_shared_endpoint_not_minimum (n : ℕ) (F : (Fin n → Bool) → Bool)
    (E : Circuit) (u v a b : ℕ) (R : List (ℕ × ℕ))
    (hE : IsAO2 n E)
    (hu : u < n + E.size) (hv : v < n + E.size)
    (ha : a < n + E.size) (hb : b < n + E.size)
    (hR : ∀ t ∈ R, t.1 < n + E.size ∧ t.2 < n + E.size)
    (hres : IsResidual n F (appendAnd E u v) ((n + E.size, a) :: (u, b) :: R))
    (hmin : ∀ (D : Circuit) (B : List (ℕ × ℕ)), IsResidual n F D B →
      (appendAnd E u v).size + 2 * ((n + E.size, a) :: (u, b) :: R).length ≤
        D.size + 2 * B.length) : False := by
  obtain ⟨D, B, hDB, hcost⟩ :=
    last_and_shared_endpoint_reduction n F E u v a b R hE hu hv ha hb hR hres
  have := hmin D B hDB
  omega


lemma exists_minimum_residual_certified (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (hres : IsResidual n F D B) :
    ∃ (E : Circuit) (A : List (ℕ × ℕ)), IsResidual n F E A ∧
      E.size + 2 * A.length ≤ D.size + 2 * B.length ∧
      (∀ (D' : Circuit) (B' : List (ℕ × ℕ)), IsResidual n F D' B' →
        E.size + 2 * A.length ≤ D'.size + 2 * B'.length) ∧
      (∀ t ∈ A, t.1 ≠ t.2) ∧
      A.Pairwise (fun t s => t.1 ≠ s.1 ∧ t.1 ≠ s.2 ∧ t.2 ≠ s.1 ∧ t.2 ≠ s.2) := by
  classical
  let P : ℕ → Prop := fun k => ∃ (E : Circuit) (A : List (ℕ × ℕ)),
    IsResidual n F E A ∧ E.size + 2 * A.length = k
  have hex : ∃ k, P k := ⟨D.size + 2 * B.length, D, B, hres, rfl⟩
  obtain ⟨E, A, hEA, hcost⟩ := Nat.find_spec hex
  have hmin : ∀ (D' : Circuit) (B' : List (ℕ × ℕ)), IsResidual n F D' B' →
      E.size + 2 * A.length ≤ D'.size + 2 * B'.length := by
    intro D' B' h'
    rw [hcost]
    exact Nat.find_min' hex ⟨D', B', h', rfl⟩
  exact ⟨E, A, hEA, hmin D B hres, hmin, minimum_residual_matching n F E A hEA hmin⟩

lemma matching_product_decomposition_certified (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hout : C.output < n + C.size)
    (hinputs : ∀ w < n, ¬ PEqualNP.CircuitMoves.WireBelowOutput n C w) :
    ∃ (D : Circuit) (B : List (ℕ × ℕ)), IsResidual n (circuitFun n C) D B ∧
      D.size + 2 * B.length ≤ C.size + 1 ∧
      (∀ (E : Circuit) (A : List (ℕ × ℕ)), IsResidual n (circuitFun n C) E A →
        D.size + 2 * B.length ≤ E.size + 2 * A.length) ∧
      (∀ t ∈ B, t.1 ≠ t.2) ∧
      B.Pairwise (fun t s => t.1 ≠ s.1 ∧ t.1 ≠ s.2 ∧ t.2 ≠ s.1 ∧ t.2 ≠ s.2) := by
  obtain ⟨D, B, hres, hcost, _, _⟩ := matching_product_decomposition n C hAO hout hinputs
  obtain ⟨E, A, hEA, hle, hmin, hloop, hpair⟩ :=
    exists_minimum_residual_certified n (circuitFun n C) D B hres
  exact ⟨E, A, hEA, hle.trans hcost, hmin, hloop, hpair⟩


lemma appendAnd_prefix_ao2 (n : ℕ) (E : Circuit) (u v : ℕ)
    (hD : IsAO2 n (appendAnd E u v)) : IsAO2 n E := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    exact hD.1 g (by simp [appendAnd, hg])
  · intro j hj w hw
    have heq : gateAt (appendAnd E u v) j = gateAt E j := by
      simp only [gateAt, appendAnd]
      exact List.getD_append _ _ _ _ hj
    exact hD.2.1 j (by simp only [appendAnd, List.length_append, List.length_cons,
      List.length_nil]; omega) w (by rwa [heq])
  · intro g hg
    exact hD.2.2 g (by simp [appendAnd, hg])

lemma appendAnd_inputs_valid (n : ℕ) (E : Circuit) (u v : ℕ)
    (hD : IsAO2 n (appendAnd E u v)) : u < n + E.size ∧ v < n + E.size := by
  have hlen : E.gates.length < (appendAnd E u v).gates.length := by simp [appendAnd]
  constructor
  · exact hD.2.1 E.gates.length hlen u (by rw [appendAnd_gate]; simp)
  · exact hD.2.1 E.gates.length hlen v (by rw [appendAnd_gate]; simp)

lemma minimum_residual_no_last_and_operand_endpoint (n : ℕ)
    (F : (Fin n → Bool) → Bool) (E : Circuit) (u v a b : ℕ) (R : List (ℕ × ℕ))
    (hres : IsResidual n F (appendAnd E u v) ((n + E.size, a) :: (u, b) :: R))
    (hmin : ∀ (D : Circuit) (B : List (ℕ × ℕ)), IsResidual n F D B →
      (appendAnd E u v).size + 2 * ((n + E.size, a) :: (u, b) :: R).length ≤
        D.size + 2 * B.length) : False := by
  have hE := appendAnd_prefix_ao2 n E u v hres.1
  obtain ⟨hu, hv⟩ := appendAnd_inputs_valid n E u v hres.1
  obtain ⟨hloop, hmatch⟩ := minimum_residual_matching n F (appendAnd E u v)
    ((n + E.size, a) :: (u, b) :: R) hres hmin
  have hfirst := (List.pairwise_cons.mp hmatch).1
  have ha : a < n + E.size := by
    have hbd := (hres.2.1 (n + E.size, a) (by simp)).2
    have hne := hloop (n + E.size, a) (by simp)
    rw [appendAnd_size] at hbd
    change n + E.size ≠ a at hne
    omega
  have hb : b < n + E.size := by
    have hbd := (hres.2.1 (u, b) (by simp)).2
    have hne := (hfirst (u, b) (by simp)).2.1
    rw [appendAnd_size] at hbd
    change n + E.size ≠ b at hne
    omega
  have hR : ∀ t ∈ R, t.1 < n + E.size ∧ t.2 < n + E.size := by
    intro t ht
    have hbd := hres.2.1 t (by simp [ht])
    have hneq := hfirst t (by simp [ht])
    rw [appendAnd_size] at hbd
    change n + E.size ≠ t.1 ∧ n + E.size ≠ t.2 ∧ _ at hneq
    constructor <;> omega
  exact last_and_shared_endpoint_not_minimum n F E u v a b R hE hu hv ha hb hR hres hmin


lemma products_appendOr (n : ℕ) (E : Circuit) (u v : ℕ) (B : List (ℕ × ℕ))
    (hbound : ∀ t ∈ B, t.1 < n + E.size ∧ t.2 < n + E.size) (x : Fin n → Bool) :
    products n (appendOr E u v) B x ↔ products n E B x := by
  apply products_congr
  intro t ht
  exact ⟨old_wire_appendOr n E u v t.1 (hbound t ht).1 x,
    old_wire_appendOr n E u v t.2 (hbound t ht).2 x⟩

lemma last_or_rotation (n : ℕ) (F : (Fin n → Bool) → Bool)
    (E : Circuit) (u v a b : ℕ) (R : List (ℕ × ℕ))
    (hE : IsAO2 n E)
    (hu : u < n + E.size) (hv : v < n + E.size)
    (ha : a < n + E.size) (hb : b < n + E.size)
    (hR : ∀ t ∈ R, t.1 < n + E.size ∧ t.2 < n + E.size)
    (hres : IsResidual n F (appendOr E u v) ((n + E.size, a) :: (u, b) :: R)) :
    IsResidual n F (appendOr E a b) ((n + E.size, u) :: (v, a) :: R) ∧
      (appendOr E a b).size + 2 * ((n + E.size, u) :: (v, a) :: R).length =
        (appendOr E u v).size + 2 * ((n + E.size, a) :: (u, b) :: R).length := by
  have hnotE : ∀ w < n + E.size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E n x w = true ∧ F x = false := by
    intro w hw
    obtain ⟨x, hx, hfalse⟩ := hres.2.2.1 w (by rw [appendOr_size]; omega)
    exact ⟨x, by rwa [old_wire_appendOr n E u v w hw x] at hx, hfalse⟩
  refine ⟨⟨appendOr_ao2 n E a b hE ha hb, ?_,
    appendOr_all_nonbelow n E a b F hE ha hb hnotE, ?_⟩, ?_⟩
  · intro t ht
    rw [appendOr_size]
    simp only [List.mem_cons] at ht
    rcases ht with rfl | rfl | ht
    · constructor <;> omega
    · constructor <;> omega
    · have := hR t ht
      constructor <;> omega
  · intro x
    rw [hres.2.2.2 x]
    change products n (appendOr E u v) ((n + E.size, a) :: (u, b) :: R) x ↔
      products n (appendOr E a b) ((n + E.size, u) :: (v, a) :: R) x
    rw [products_cons, products_cons, products_cons, products_cons]
    rw [new_wire_appendOr n E u v hE hu hv x,
      old_wire_appendOr n E u v a ha x, old_wire_appendOr n E u v u hu x,
      old_wire_appendOr n E u v b hb x, products_appendOr n E u v R hR x,
      new_wire_appendOr n E a b hE ha hb x,
      old_wire_appendOr n E a b u hu x, old_wire_appendOr n E a b v hv x,
      old_wire_appendOr n E a b a ha x, products_appendOr n E a b R hR x]
    simp only [Bool.or_eq_true]
    tauto
  · rw [appendOr_size, appendOr_size]
    simp only [List.length_cons]

lemma last_or_two_operand_endpoint_reduction (n : ℕ) (F : (Fin n → Bool) → Bool)
    (E : Circuit) (u v a b c : ℕ) (R : List (ℕ × ℕ))
    (hE : IsAO2 n E)
    (hu : u < n + E.size) (hv : v < n + E.size)
    (ha : a < n + E.size) (hb : b < n + E.size) (hc : c < n + E.size)
    (hR : ∀ t ∈ R, t.1 < n + E.size ∧ t.2 < n + E.size)
    (hres : IsResidual n F (appendOr E u v)
      ((n + E.size, a) :: (u, b) :: (v, c) :: R)) :
    ∃ (D : Circuit) (B : List (ℕ × ℕ)), IsResidual n F D B ∧
      D.size + 2 * B.length + 1 =
        (appendOr E u v).size + 2 * ((n + E.size, a) :: (u, b) :: (v, c) :: R).length := by
  have htail : ∀ t ∈ (v, c) :: R, t.1 < n + E.size ∧ t.2 < n + E.size := by
    intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact ⟨hv, hc⟩
    · exact hR t ht
  obtain ⟨hrot, hcost⟩ := last_or_rotation n F E u v a b ((v, c) :: R)
    hE hu hv ha hb htail hres
  have hp : ((n + E.size, u) :: (v, a) :: (v, c) :: R).Perm
      ((v, a) :: (v, c) :: (n + E.size, u) :: R) :=
    (List.Perm.swap (v, a) (n + E.size, u) ((v, c) :: R)).trans
      ((List.Perm.swap (v, c) (n + E.size, u) R).cons (v, a))
  obtain ⟨D, B, hDB, hfac⟩ := factor_shared_pairs n F (appendOr E a b)
    ((n + E.size, u) :: (v, a) :: (v, c) :: R) hrot (v, a) (v, c)
    ((n + E.size, u) :: R) hp (Or.inl rfl)
  exact ⟨D, B, hDB, hfac.trans hcost⟩

lemma appendOr_prefix_ao2 (n : ℕ) (E : Circuit) (u v : ℕ)
    (hD : IsAO2 n (appendOr E u v)) : IsAO2 n E := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    exact hD.1 g (by simp [appendOr, hg])
  · intro j hj w hw
    have heq : gateAt (appendOr E u v) j = gateAt E j := by
      simp only [gateAt, appendOr]
      exact List.getD_append _ _ _ _ hj
    exact hD.2.1 j (by simp only [appendOr, List.length_append, List.length_cons,
      List.length_nil]; omega) w (by rwa [heq])
  · intro g hg
    exact hD.2.2 g (by simp [appendOr, hg])

lemma appendOr_inputs_valid (n : ℕ) (E : Circuit) (u v : ℕ)
    (hD : IsAO2 n (appendOr E u v)) : u < n + E.size ∧ v < n + E.size := by
  have hlen : E.gates.length < (appendOr E u v).gates.length := by simp [appendOr]
  constructor
  · exact hD.2.1 E.gates.length hlen u (by rw [appendOr_gate]; simp)
  · exact hD.2.1 E.gates.length hlen v (by rw [appendOr_gate]; simp)

lemma minimum_residual_no_last_or_two_operand_endpoints (n : ℕ)
    (F : (Fin n → Bool) → Bool) (E : Circuit) (u v a b c : ℕ) (R : List (ℕ × ℕ))
    (hres : IsResidual n F (appendOr E u v) ((n + E.size, a) :: (u, b) :: (v, c) :: R))
    (hmin : ∀ (D : Circuit) (B : List (ℕ × ℕ)), IsResidual n F D B →
      (appendOr E u v).size + 2 * ((n + E.size, a) :: (u, b) :: (v, c) :: R).length ≤
        D.size + 2 * B.length) : False := by
  have hE := appendOr_prefix_ao2 n E u v hres.1
  obtain ⟨hu, hv⟩ := appendOr_inputs_valid n E u v hres.1
  obtain ⟨hloop, hmatch⟩ := minimum_residual_matching n F (appendOr E u v)
    ((n + E.size, a) :: (u, b) :: (v, c) :: R) hres hmin
  have hfirst := (List.pairwise_cons.mp hmatch).1
  have ha : a < n + E.size := by
    have hbd := (hres.2.1 (n + E.size, a) (by simp)).2
    have hne := hloop (n + E.size, a) (by simp)
    rw [appendOr_size] at hbd
    change n + E.size ≠ a at hne
    omega
  have htail : ∀ t ∈ (u, b) :: (v, c) :: R,
      t.1 < n + E.size ∧ t.2 < n + E.size := by
    intro t ht
    have hbd := hres.2.1 t (by simp [ht])
    have hneq := hfirst t ht
    rw [appendOr_size] at hbd
    change n + E.size ≠ t.1 ∧ n + E.size ≠ t.2 ∧ _ at hneq
    constructor <;> omega
  have hb := (htail (u, b) (by simp)).2
  have hc := (htail (v, c) (by simp)).2
  have hR : ∀ t ∈ R, t.1 < n + E.size ∧ t.2 < n + E.size := by
    intro t ht
    exact htail t (by simp [ht])
  obtain ⟨D, B, hDB, hcost⟩ := last_or_two_operand_endpoint_reduction n F E u v a b c R
    hE hu hv ha hb hc hR hres
  have := hmin D B hDB
  omega

end LastAndFactor

namespace ContextBypass

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover
open ProductFactor LastAndFactor

def andMark : GateOp → ℕ
  | .and => 1
  | _ => 0

def weightStep (acc : List ℕ) (g : Gate) : List ℕ :=
  acc ++ [(g.inputs.map (fun w => acc.getD w 0)).sum + andMark g.op]

def wireWeight (n : ℕ) (D : Circuit) (w : ℕ) : ℕ :=
  (D.gates.foldl weightStep (List.replicate n 0)).getD w 0

def potential (n : ℕ) (D : Circuit) (B : List (ℕ × ℕ)) : ℕ :=
  (B.map (fun t => wireWeight n D t.1 + wireWeight n D t.2)).sum

lemma foldl_weightStep_length (gs : List Gate) (acc : List ℕ) :
    (gs.foldl weightStep acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, weightStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_weightStep_prefix (gs : List Gate) (acc : List ℕ) (w : ℕ)
    (hw : w < acc.length) :
    (gs.foldl weightStep acc).getD w 0 = acc.getD w 0 := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hw' : w < (weightStep acc g).length := by
      simp only [weightStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (weightStep acc g) hw']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [weightStep, List.getElem?_append_left hw]

lemma wireWeight_gate (n : ℕ) (D : Circuit) (k : ℕ)
    (hk : k < D.gates.length) (hRB : ReadsBack n D) :
    wireWeight n D (n + k) =
      ((gateAt D k).inputs.map (fun u => wireWeight n D u)).sum + andMark (gateAt D k).op := by
  have hsplit : D.gates = D.gates.take k ++ [D.gates[k]] ++ D.gates.drop (k + 1) := by
    have h1 := List.take_append_drop k D.gates
    have h2 : D.gates.drop k = D.gates[k] :: D.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (D.gates.take k).foldl weightStep (List.replicate n 0) with hacc
  have hacc_len : acc.length = n + k := by
    rw [hacc, foldl_weightStep_length, List.length_replicate, List.length_take]
    omega
  have hpref : ∀ u < n + k, wireWeight n D u = acc.getD u 0 := by
    intro u hu
    unfold wireWeight
    conv_lhs => rw [← List.take_append_drop k D.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_weightStep_prefix (D.gates.drop k) acc u (by omega)
  have hval : wireWeight n D (n + k) =
      (D.gates[k].inputs.map (fun u => acc.getD u 0)).sum + andMark D.gates[k].op := by
    unfold wireWeight
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : n + k < (weightStep acc D.gates[k]).length := by
      simp only [weightStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_weightStep_prefix (D.gates.drop (k + 1)) (weightStep acc D.gates[k]) (n + k) hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [weightStep, List.getElem?_append_right (by omega : acc.length ≤ n + k),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hval, SplitAux.gateAt_eq_getElem D k hk]
  have hmap : D.gates[k].inputs.map (fun u => acc.getD u 0) =
      D.gates[k].inputs.map (fun u => wireWeight n D u) := by
    apply List.map_congr_left
    intro u hu
    rw [← SplitAux.gateAt_eq_getElem D k hk] at hu
    exact (hpref u (hRB k hk u hu)).symm
  rw [hmap]

lemma wireWeight_appendOr_old (n : ℕ) (E : Circuit) (u v w : ℕ)
    (hw : w < n + E.size) : wireWeight n (appendOr E u v) w = wireWeight n E w := by
  unfold wireWeight appendOr
  simp only [List.foldl_append, List.foldl_cons, List.foldl_nil]
  apply List.getD_append
  rw [foldl_weightStep_length, List.length_replicate]
  exact hw

lemma wireWeight_appendOr_new (n : ℕ) (E : Circuit) (u v : ℕ)
    (hE : IsAO2 n E) (hu : u < n + E.size) (hv : v < n + E.size) :
    wireWeight n (appendOr E u v) (n + E.size) = wireWeight n E u + wireWeight n E v := by
  have hD := appendOr_ao2 n E u v hE hu hv
  change wireWeight n (appendOr E u v) (n + E.gates.length) = _
  rw [wireWeight_gate n (appendOr E u v) E.gates.length (by simp [appendOr]) hD.2.1,
    appendOr_gate]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, andMark, Nat.add_zero]
  rw [wireWeight_appendOr_old n E u v u hu, wireWeight_appendOr_old n E u v v hv]

lemma wireWeight_and_gate (n : ℕ) (E : Circuit) (j A C : ℕ)
    (hE : IsAO2 n E) (hj : j < E.size) (hgate : gateAt E j = ⟨GateOp.and, [A, C]⟩) :
    wireWeight n E (n + j) = wireWeight n E A + wireWeight n E C + 1 := by
  rw [wireWeight_gate n E j hj hE.2.1, hgate]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, andMark, Nat.add_zero]

lemma potential_cons (n : ℕ) (E : Circuit) (t : ℕ × ℕ) (B : List (ℕ × ℕ)) :
    potential n E (t :: B) = wireWeight n E t.1 + wireWeight n E t.2 + potential n E B := by
  simp only [potential, List.map_cons, List.sum_cons]

lemma potential_appendOr_prefix (n : ℕ) (E : Circuit) (u v : ℕ) (B : List (ℕ × ℕ))
    (hbound : ∀ t ∈ B, t.1 < n + E.size ∧ t.2 < n + E.size) :
    potential n (appendOr E u v) B = potential n E B := by
  unfold potential
  congr 1
  apply List.map_congr_left
  intro t ht
  rw [wireWeight_appendOr_old n E u v t.1 (hbound t ht).1,
    wireWeight_appendOr_old n E u v t.2 (hbound t ht).2]


lemma last_or_relative_context_bypass (n : ℕ) (F : (Fin n → Bool) → Bool)
    (E : Circuit) (j A C a b : ℕ) (R : List (ℕ × ℕ))
    (hE : IsAO2 n E) (hj : j < E.size)
    (hgate : gateAt E j = ⟨GateOp.and, [A, C]⟩)
    (ha : a < n + E.size) (hb : b < n + E.size)
    (hR : ∀ t ∈ R, t.1 < n + E.size ∧ t.2 < n + E.size)
    (hres : IsResidual n F (appendOr E (n + j) b) ((n + E.size, a) :: R))
    (hcontext : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E n x a = true →
      PEqualNP.BlindGate.wireValue E n x A = true ∨ F x = true) :
    IsResidual n F (appendOr E C b) ((n + E.size, a) :: R) ∧
      (appendOr E C b).size + 2 * ((n + E.size, a) :: R).length =
        (appendOr E (n + j) b).size + 2 * ((n + E.size, a) :: R).length ∧
      potential n (appendOr E C b) ((n + E.size, a) :: R) + wireWeight n E A + 1 =
        potential n (appendOr E (n + j) b) ((n + E.size, a) :: R) := by
  have hA : A < n + E.size := by
    have h := hE.2.1 j hj A (by rw [hgate]; simp)
    omega
  have hC : C < n + E.size := by
    have h := hE.2.1 j hj C (by rw [hgate]; simp)
    omega
  have hJ : n + j < n + E.size := by omega
  have hnotE : ∀ w < n + E.size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E n x w = true ∧ F x = false := by
    intro w hw
    obtain ⟨x, hx, hfalse⟩ := hres.2.2.1 w (by rw [appendOr_size]; omega)
    exact ⟨x, by rwa [old_wire_appendOr n E (n + j) b w hw x] at hx, hfalse⟩
  refine ⟨⟨appendOr_ao2 n E C b hE hC hb, ?_,
    appendOr_all_nonbelow n E C b F hE hC hb hnotE, ?_⟩, ?_, ?_⟩
  · intro t ht
    rw [appendOr_size]
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · constructor <;> omega
    · have := hR t ht
      constructor <;> omega
  · intro x
    have hf := hres.2.2.2 x
    change F x = true ↔ products n (appendOr E (n + j) b) ((n + E.size, a) :: R) x at hf
    rw [products_cons, new_wire_appendOr n E (n + j) b hE hJ hb x,
      old_wire_appendOr n E (n + j) b a ha x, products_appendOr n E (n + j) b R hR x,
      SplitAux.wireValue_gate n E x j hj hE.2.1, hgate] at hf
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
      id_eq, Bool.and_true, Bool.or_eq_true, Bool.and_eq_true] at hf
    change F x = true ↔ products n (appendOr E C b) ((n + E.size, a) :: R) x
    rw [products_cons, new_wire_appendOr n E C b hE hC hb x,
      old_wire_appendOr n E C b a ha x, products_appendOr n E C b R hR x]
    simp only [Bool.or_eq_true]
    have hc := hcontext x
    tauto
  · simp only [appendOr_size]
  · rw [potential_cons, potential_cons,
      wireWeight_appendOr_new n E C b hE hC hb,
      wireWeight_appendOr_new n E (n + j) b hE hJ hb,
      wireWeight_appendOr_old n E C b a ha,
      wireWeight_appendOr_old n E (n + j) b a ha,
      potential_appendOr_prefix n E C b R hR,
      potential_appendOr_prefix n E (n + j) b R hR,
      wireWeight_and_gate n E j A C hE hj hgate]
    omega

lemma last_or_relative_context_bypass_not_potential_minimum (n : ℕ) (F : (Fin n → Bool) → Bool)
    (E : Circuit) (j A C a b : ℕ) (R : List (ℕ × ℕ))
    (hE : IsAO2 n E) (hj : j < E.size)
    (hgate : gateAt E j = ⟨GateOp.and, [A, C]⟩)
    (ha : a < n + E.size) (hb : b < n + E.size)
    (hR : ∀ t ∈ R, t.1 < n + E.size ∧ t.2 < n + E.size)
    (hres : IsResidual n F (appendOr E (n + j) b) ((n + E.size, a) :: R))
    (hcontext : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E n x a = true →
      PEqualNP.BlindGate.wireValue E n x A = true ∨ F x = true)
    (hminPhi : ∀ (D : Circuit) (B : List (ℕ × ℕ)), IsResidual n F D B →
      D.size + 2 * B.length =
        (appendOr E (n + j) b).size + 2 * ((n + E.size, a) :: R).length →
      potential n (appendOr E (n + j) b) ((n + E.size, a) :: R) ≤ potential n D B) : False := by
  obtain ⟨hnew, hcost, hPhi⟩ :=
    last_or_relative_context_bypass n F E j A C a b R hE hj hgate ha hb hR hres hcontext
  have := hminPhi (appendOr E C b) ((n + E.size, a) :: R) hnew hcost
  omega

lemma exists_lex_minimum_residual (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (hres : IsResidual n F D B) :
    ∃ (E : Circuit) (A : List (ℕ × ℕ)), IsResidual n F E A ∧
      E.size + 2 * A.length ≤ D.size + 2 * B.length ∧
      (∀ (D' : Circuit) (B' : List (ℕ × ℕ)), IsResidual n F D' B' →
        E.size + 2 * A.length ≤ D'.size + 2 * B'.length) ∧
      (∀ (D' : Circuit) (B' : List (ℕ × ℕ)), IsResidual n F D' B' →
        D'.size + 2 * B'.length = E.size + 2 * A.length →
        potential n E A ≤ potential n D' B') ∧
      (∀ t ∈ A, t.1 ≠ t.2) ∧
      A.Pairwise (fun t s => t.1 ≠ s.1 ∧ t.1 ≠ s.2 ∧ t.2 ≠ s.1 ∧ t.2 ≠ s.2) := by
  classical
  obtain ⟨E, A, hEA, hle, hmin, _, _⟩ := exists_minimum_residual_certified n F D B hres
  let P : ℕ → Prop := fun k => ∃ (D' : Circuit) (B' : List (ℕ × ℕ)),
    IsResidual n F D' B' ∧ D'.size + 2 * B'.length = E.size + 2 * A.length ∧
      potential n D' B' = k
  have hex : ∃ k, P k := ⟨potential n E A, E, A, hEA, rfl, rfl⟩
  obtain ⟨E', A', hEA', hcost, hPhi⟩ := Nat.find_spec hex
  have hmin' : ∀ (D' : Circuit) (B' : List (ℕ × ℕ)), IsResidual n F D' B' →
      E'.size + 2 * A'.length ≤ D'.size + 2 * B'.length := by
    intro D' B' h'
    rw [hcost]
    exact hmin D' B' h'
  refine ⟨E', A', hEA', ?_, hmin', ?_, minimum_residual_matching n F E' A' hEA' hmin'⟩
  · rwa [hcost]
  · intro D' B' h' heq
    rw [hPhi]
    exact Nat.find_min' hex ⟨D', B', h', heq.trans hcost, rfl⟩

lemma lex_minimum_residual_no_last_or_relative_context_bypass (n : ℕ)
    (F : (Fin n → Bool) → Bool) (E : Circuit) (j A C a b : ℕ) (R : List (ℕ × ℕ))
    (hj : j < E.size) (hgate : gateAt E j = ⟨GateOp.and, [A, C]⟩)
    (hres : IsResidual n F (appendOr E (n + j) b) ((n + E.size, a) :: R))
    (hcontext : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E n x a = true →
      PEqualNP.BlindGate.wireValue E n x A = true ∨ F x = true)
    (hmin : ∀ (D : Circuit) (B : List (ℕ × ℕ)), IsResidual n F D B →
      (appendOr E (n + j) b).size + 2 * ((n + E.size, a) :: R).length ≤ D.size + 2 * B.length)
    (hminPhi : ∀ (D : Circuit) (B : List (ℕ × ℕ)), IsResidual n F D B →
      D.size + 2 * B.length =
        (appendOr E (n + j) b).size + 2 * ((n + E.size, a) :: R).length →
      potential n (appendOr E (n + j) b) ((n + E.size, a) :: R) ≤ potential n D B) : False := by
  have hE := appendOr_prefix_ao2 n E (n + j) b hres.1
  have hb := (appendOr_inputs_valid n E (n + j) b hres.1).2
  obtain ⟨hloop, hmatch⟩ := minimum_residual_matching n F (appendOr E (n + j) b)
    ((n + E.size, a) :: R) hres hmin
  have ha : a < n + E.size := by
    have hbd := (hres.2.1 (n + E.size, a) (by simp)).2
    have hne := hloop (n + E.size, a) (by simp)
    rw [appendOr_size] at hbd
    change n + E.size ≠ a at hne
    omega
  have hR : ∀ t ∈ R, t.1 < n + E.size ∧ t.2 < n + E.size := by
    intro t ht
    have hbd := hres.2.1 t (by simp [ht])
    have hneq := (List.pairwise_cons.mp hmatch).1 t ht
    rw [appendOr_size] at hbd
    change n + E.size ≠ t.1 ∧ n + E.size ≠ t.2 ∧ _ at hneq
    constructor <;> omega
  exact last_or_relative_context_bypass_not_potential_minimum n F E j A C a b R
    hE hj hgate ha hb hR hres hcontext hminPhi


lemma last_or_context_bypass (n : ℕ) (F : (Fin n → Bool) → Bool)
    (E : Circuit) (j A C a b : ℕ) (R : List (ℕ × ℕ))
    (hE : IsAO2 n E) (hj : j < E.size)
    (hgate : gateAt E j = ⟨GateOp.and, [A, C]⟩)
    (ha : a < n + E.size) (hb : b < n + E.size)
    (hR : ∀ t ∈ R, t.1 < n + E.size ∧ t.2 < n + E.size)
    (hres : IsResidual n F (appendOr E (n + j) b) ((n + E.size, a) :: R))
    (hcontext : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E n x a = true →
      PEqualNP.BlindGate.wireValue E n x A = true) :
    IsResidual n F (appendOr E C b) ((n + E.size, a) :: R) ∧
      (appendOr E C b).size + 2 * ((n + E.size, a) :: R).length =
        (appendOr E (n + j) b).size + 2 * ((n + E.size, a) :: R).length ∧
      potential n (appendOr E C b) ((n + E.size, a) :: R) + wireWeight n E A + 1 =
        potential n (appendOr E (n + j) b) ((n + E.size, a) :: R) :=
  last_or_relative_context_bypass n F E j A C a b R hE hj hgate ha hb hR hres
    (fun x hx => Or.inl (hcontext x hx))

lemma last_and_relative_context_drop (n : ℕ) (F : (Fin n → Bool) → Bool)
    (E : Circuit) (A C a : ℕ) (R : List (ℕ × ℕ))
    (hE : IsAO2 n E) (hA : A < n + E.size) (hC : C < n + E.size)
    (ha : a < n + E.size)
    (hR : ∀ t ∈ R, t.1 < n + E.size ∧ t.2 < n + E.size)
    (hres : IsResidual n F (appendAnd E A C) ((n + E.size, a) :: R))
    (hcontext : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E n x a = true →
      PEqualNP.BlindGate.wireValue E n x A = true ∨ F x = true) :
    IsResidual n F E ((C, a) :: R) ∧
      E.size + 2 * ((C, a) :: R).length + 1 =
        (appendAnd E A C).size + 2 * ((n + E.size, a) :: R).length := by
  have hnotE : ∀ w < n + E.size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E n x w = true ∧ F x = false := by
    intro w hw
    obtain ⟨x, hx, hfalse⟩ := hres.2.2.1 w (by rw [appendAnd_size]; omega)
    exact ⟨x, by rwa [old_wire_appendAnd n E A C w hw x] at hx, hfalse⟩
  refine ⟨⟨hE, ?_, hnotE, ?_⟩, ?_⟩
  · intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact ⟨hC, ha⟩
    · exact hR t ht
  · intro x
    have hf := hres.2.2.2 x
    change F x = true ↔ products n (appendAnd E A C) ((n + E.size, a) :: R) x at hf
    rw [products_cons, new_wire_appendAnd n E A C hE hA hC x,
      old_wire_appendAnd n E A C a ha x, products_appendAnd n E A C R hR x] at hf
    simp only [Bool.and_eq_true] at hf
    change F x = true ↔ products n E ((C, a) :: R) x
    rw [products_cons]
    have hc := hcontext x
    tauto
  · rw [appendAnd_size]
    simp only [List.length_cons]
    omega

lemma last_and_context_drop (n : ℕ) (F : (Fin n → Bool) → Bool)
    (E : Circuit) (A C a : ℕ) (R : List (ℕ × ℕ))
    (hE : IsAO2 n E) (hA : A < n + E.size) (hC : C < n + E.size)
    (ha : a < n + E.size)
    (hR : ∀ t ∈ R, t.1 < n + E.size ∧ t.2 < n + E.size)
    (hres : IsResidual n F (appendAnd E A C) ((n + E.size, a) :: R))
    (hcontext : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E n x a = true →
      PEqualNP.BlindGate.wireValue E n x A = true) :
    IsResidual n F E ((C, a) :: R) ∧
      E.size + 2 * ((C, a) :: R).length + 1 =
        (appendAnd E A C).size + 2 * ((n + E.size, a) :: R).length :=
  last_and_relative_context_drop n F E A C a R hE hA hC ha hR hres
    (fun x hx => Or.inl (hcontext x hx))


lemma last_or_safe_pair_bypass (n : ℕ) (F : (Fin n → Bool) → Bool)
    (E : Circuit) (j A C a b : ℕ) (R : List (ℕ × ℕ))
    (hE : IsAO2 n E) (hj : j < E.size)
    (hgate : gateAt E j = ⟨GateOp.and, [A, C]⟩)
    (ha : a < n + E.size) (hb : b < n + E.size)
    (hR : ∀ t ∈ R, t.1 < n + E.size ∧ t.2 < n + E.size)
    (hres : IsResidual n F (appendOr E (n + j) b) ((n + E.size, a) :: R))
    (hsafe : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E n x a = true →
      PEqualNP.BlindGate.wireValue E n x C = true → F x = true) :
    IsResidual n F (appendOr E C b) ((n + E.size, a) :: R) ∧
      (appendOr E C b).size + 2 * ((n + E.size, a) :: R).length =
        (appendOr E (n + j) b).size + 2 * ((n + E.size, a) :: R).length ∧
      potential n (appendOr E C b) ((n + E.size, a) :: R) + wireWeight n E A + 1 =
        potential n (appendOr E (n + j) b) ((n + E.size, a) :: R) := by
  have hA : A < n + E.size := by
    have h := hE.2.1 j hj A (by rw [hgate]; simp)
    omega
  have hC : C < n + E.size := by
    have h := hE.2.1 j hj C (by rw [hgate]; simp)
    omega
  have hJ : n + j < n + E.size := by omega
  have hnotE : ∀ w < n + E.size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E n x w = true ∧ F x = false := by
    intro w hw
    obtain ⟨x, hx, hfalse⟩ := hres.2.2.1 w (by rw [appendOr_size]; omega)
    exact ⟨x, by rwa [old_wire_appendOr n E (n + j) b w hw x] at hx, hfalse⟩
  refine ⟨⟨appendOr_ao2 n E C b hE hC hb, ?_,
    appendOr_all_nonbelow n E C b F hE hC hb hnotE, ?_⟩, ?_, ?_⟩
  · intro t ht
    rw [appendOr_size]
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · constructor <;> omega
    · have := hR t ht
      constructor <;> omega
  · intro x
    have hf := hres.2.2.2 x
    change F x = true ↔ products n (appendOr E (n + j) b) ((n + E.size, a) :: R) x at hf
    rw [products_cons, new_wire_appendOr n E (n + j) b hE hJ hb x,
      old_wire_appendOr n E (n + j) b a ha x, products_appendOr n E (n + j) b R hR x,
      SplitAux.wireValue_gate n E x j hj hE.2.1, hgate] at hf
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
      id_eq, Bool.and_true, Bool.or_eq_true, Bool.and_eq_true] at hf
    change F x = true ↔ products n (appendOr E C b) ((n + E.size, a) :: R) x
    rw [products_cons, new_wire_appendOr n E C b hE hC hb x,
      old_wire_appendOr n E C b a ha x, products_appendOr n E C b R hR x]
    simp only [Bool.or_eq_true]
    have hc := hsafe x
    tauto
  · simp only [appendOr_size]
  · rw [potential_cons, potential_cons,
      wireWeight_appendOr_new n E C b hE hC hb,
      wireWeight_appendOr_new n E (n + j) b hE hJ hb,
      wireWeight_appendOr_old n E C b a ha,
      wireWeight_appendOr_old n E (n + j) b a ha,
      potential_appendOr_prefix n E C b R hR,
      potential_appendOr_prefix n E (n + j) b R hR,
      wireWeight_and_gate n E j A C hE hj hgate]
    omega

lemma last_or_safe_pair_bypass_not_potential_minimum (n : ℕ) (F : (Fin n → Bool) → Bool)
    (E : Circuit) (j A C a b : ℕ) (R : List (ℕ × ℕ))
    (hE : IsAO2 n E) (hj : j < E.size)
    (hgate : gateAt E j = ⟨GateOp.and, [A, C]⟩)
    (ha : a < n + E.size) (hb : b < n + E.size)
    (hR : ∀ t ∈ R, t.1 < n + E.size ∧ t.2 < n + E.size)
    (hres : IsResidual n F (appendOr E (n + j) b) ((n + E.size, a) :: R))
    (hsafe : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E n x a = true →
      PEqualNP.BlindGate.wireValue E n x C = true → F x = true)
    (hminPhi : ∀ (D : Circuit) (B : List (ℕ × ℕ)), IsResidual n F D B →
      D.size + 2 * B.length =
        (appendOr E (n + j) b).size + 2 * ((n + E.size, a) :: R).length →
      potential n (appendOr E (n + j) b) ((n + E.size, a) :: R) ≤ potential n D B) : False := by
  obtain ⟨hnew, hcost, hPhi⟩ :=
    last_or_safe_pair_bypass n F E j A C a b R hE hj hgate ha hb hR hres hsafe
  have := hminPhi (appendOr E C b) ((n + E.size, a) :: R) hnew hcost
  omega

lemma lex_minimum_residual_no_last_or_safe_pair_bypass (n : ℕ)
    (F : (Fin n → Bool) → Bool) (E : Circuit) (j A C a b : ℕ) (R : List (ℕ × ℕ))
    (hj : j < E.size) (hgate : gateAt E j = ⟨GateOp.and, [A, C]⟩)
    (hres : IsResidual n F (appendOr E (n + j) b) ((n + E.size, a) :: R))
    (hsafe : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E n x a = true →
      PEqualNP.BlindGate.wireValue E n x C = true → F x = true)
    (hmin : ∀ (D : Circuit) (B : List (ℕ × ℕ)), IsResidual n F D B →
      (appendOr E (n + j) b).size + 2 * ((n + E.size, a) :: R).length ≤ D.size + 2 * B.length)
    (hminPhi : ∀ (D : Circuit) (B : List (ℕ × ℕ)), IsResidual n F D B →
      D.size + 2 * B.length =
        (appendOr E (n + j) b).size + 2 * ((n + E.size, a) :: R).length →
      potential n (appendOr E (n + j) b) ((n + E.size, a) :: R) ≤ potential n D B) : False := by
  have hE := appendOr_prefix_ao2 n E (n + j) b hres.1
  have hb := (appendOr_inputs_valid n E (n + j) b hres.1).2
  obtain ⟨hloop, hmatch⟩ := minimum_residual_matching n F (appendOr E (n + j) b)
    ((n + E.size, a) :: R) hres hmin
  have ha : a < n + E.size := by
    have hbd := (hres.2.1 (n + E.size, a) (by simp)).2
    have hne := hloop (n + E.size, a) (by simp)
    rw [appendOr_size] at hbd
    change n + E.size ≠ a at hne
    omega
  have hR : ∀ t ∈ R, t.1 < n + E.size ∧ t.2 < n + E.size := by
    intro t ht
    have hbd := hres.2.1 t (by simp [ht])
    have hneq := (List.pairwise_cons.mp hmatch).1 t ht
    rw [appendOr_size] at hbd
    change n + E.size ≠ t.1 ∧ n + E.size ≠ t.2 ∧ _ at hneq
    constructor <;> omega
  exact last_or_safe_pair_bypass_not_potential_minimum n F E j A C a b R
    hE hj hgate ha hb hR hres hsafe hminPhi


lemma last_and_safe_pair_drop (n : ℕ) (F : (Fin n → Bool) → Bool)
    (E : Circuit) (A C a : ℕ) (R : List (ℕ × ℕ))
    (hE : IsAO2 n E) (hA : A < n + E.size) (hC : C < n + E.size)
    (ha : a < n + E.size)
    (hR : ∀ t ∈ R, t.1 < n + E.size ∧ t.2 < n + E.size)
    (hres : IsResidual n F (appendAnd E A C) ((n + E.size, a) :: R))
    (hsafe : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E n x a = true →
      PEqualNP.BlindGate.wireValue E n x C = true → F x = true) :
    IsResidual n F E ((C, a) :: R) ∧
      E.size + 2 * ((C, a) :: R).length + 1 =
        (appendAnd E A C).size + 2 * ((n + E.size, a) :: R).length := by
  have hnotE : ∀ w < n + E.size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E n x w = true ∧ F x = false := by
    intro w hw
    obtain ⟨x, hx, hfalse⟩ := hres.2.2.1 w (by rw [appendAnd_size]; omega)
    exact ⟨x, by rwa [old_wire_appendAnd n E A C w hw x] at hx, hfalse⟩
  refine ⟨⟨hE, ?_, hnotE, ?_⟩, ?_⟩
  · intro t ht
    simp only [List.mem_cons] at ht
    rcases ht with rfl | ht
    · exact ⟨hC, ha⟩
    · exact hR t ht
  · intro x
    have hf := hres.2.2.2 x
    change F x = true ↔ products n (appendAnd E A C) ((n + E.size, a) :: R) x at hf
    rw [products_cons, new_wire_appendAnd n E A C hE hA hC x,
      old_wire_appendAnd n E A C a ha x, products_appendAnd n E A C R hR x] at hf
    simp only [Bool.and_eq_true] at hf
    change F x = true ↔ products n E ((C, a) :: R) x
    rw [products_cons]
    have hc := hsafe x
    tauto
  · rw [appendAnd_size]
    simp only [List.length_cons]
    omega

end ContextBypass



namespace CopyErase

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.MetaComplexity
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open LiftAux ProductFactor

lemma eraseGate_wires_eq_of_copy (n : ℕ) (C : Circuit) (m p : ℕ)
    (hAO : IsAO2 n C) (hm : m < C.gates.length) (hp : p < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, p]⟩)
    (x : List Bool) (hx : x.length = n) :
    ∀ k < n + (eraseGate n C m p).gates.length,
      ((eraseGate n C m p).wires x).getD k false =
      (C.wires x).getD (if k < n + m then k else k + 1) false := by
  have hEAO := eraseGate_isAO2 n C m p hAO hm hp
  have hElen := eraseGate_gates_length n C m p hm
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk
    by_cases hkm : k < n + m
    · simp only [hkm, ↓reduceIte]
      exact eraseGate_wires_prefix n C m p hm x hx k hkm
    · simp only [hkm, ↓reduceIte]
      set j := k - n
      have hkj : k = n + j := by omega
      have hmj : m ≤ j := by omega
      have hjE : j < (eraseGate n C m p).gates.length := by omega
      have hjC : j + 1 < C.gates.length := by omega
      rw [hkj]
      have hkj1 : n + j + 1 = n + (j + 1) := by omega
      rw [hkj1]
      rw [wires_getD_gate n (eraseGate n C m p) hEAO.2.1 x hx j hjE]
      rw [eraseGate_getElem_ge n C m p j hm hmj hjE]
      rw [List.map_map]
      rw [wires_getD_gate n C hAO.2.1 x hx (j + 1) hjC]
      congr 1
      apply List.map_congr_left
      intro u hu
      have hu_lt : u < n + (j + 1) := by
        have := hAO.2.1 (j + 1) hjC u
        rw [gateAt_eq_getElem C (j + 1) hjC] at this
        exact this hu
      simp only [Function.comp_apply]
      unfold eraseRedirect
      split_ifs with heq hgt
      · rw [heq, gate_m_val n C m p p hAO.2.1 hm (Or.inl hgate) x hx, Bool.or_self]
        exact eraseGate_wires_prefix n C m p hm x hx p hp
      · have hstep := ih (u - 1) (by omega) (by omega)
        have hnotlt : ¬ (u - 1 < n + m) := by omega
        simp only [hnotlt, ↓reduceIte] at hstep
        have hu1 : u - 1 + 1 = u := by omega
        rwa [hu1] at hstep
      · have hult : u < n + m := by omega
        exact eraseGate_wires_prefix n C m p hm x hx u hult


lemma copy_getElem_option (Q : Circuit) (j c : ℕ) (hj : j < Q.size)
    (hcopy : gateAt Q j = ⟨GateOp.or, [c, c]⟩) :
    Q.gates[j]? = some ⟨GateOp.or, [c, c]⟩ := by
  rw [List.getElem?_eq_getElem hj, ← LiftAux.gateAt_eq_getElem Q j hj, hcopy]

lemma erase_copy_wire (n : ℕ) (Q : Circuit) (j c : ℕ)
    (hQ : IsAO2 n Q) (hj : j < Q.size) (hc : c < n + j)
    (hcopy : gateAt Q j = ⟨GateOp.or, [c, c]⟩)
    (x : Fin n → Bool) (w : ℕ) (hw : w < n + Q.size) :
    PEqualNP.BlindGate.wireValue (eraseGate n Q j c) n x (eraseRedirect n j c w) =
      PEqualNP.BlindGate.wireValue Q n x w := by
  have hget := copy_getElem_option Q j c hj hcopy
  have hsize := LiftAux.eraseGate_gates_length n Q j c hj
  change ((eraseGate n Q j c).wires (List.ofFn x)).getD (eraseRedirect n j c w) false =
    (Q.wires (List.ofFn x)).getD w false
  unfold eraseRedirect
  split_ifs with heq hgt
  · subst w
    rw [LiftAux.gate_m_val n Q j c c hQ.2.1 hj (Or.inl hget) (List.ofFn x) (by simp),
      Bool.or_self]
    exact LiftAux.eraseGate_wires_prefix n Q j c hj (List.ofFn x) (by simp) c hc
  · have hbound : w - 1 < n + (eraseGate n Q j c).gates.length := by
      change w < n + Q.gates.length at hw
      omega
    have h := eraseGate_wires_eq_of_copy n Q j c hQ hj hc hget (List.ofFn x)
      (by simp) (w - 1) hbound
    have hnot : ¬ (w - 1 < n + j) := by omega
    have hw1 : w - 1 + 1 = w := by omega
    simpa only [hnot, ↓reduceIte, hw1] using h
  · have hlt : w < n + j := by omega
    exact LiftAux.eraseGate_wires_prefix n Q j c hj (List.ofFn x) (by simp) w hlt

lemma erase_copy_bound (n : ℕ) (Q : Circuit) (j c w : ℕ)
    (hj : j < Q.size) (hc : c < n + j) (hw : w < n + Q.size) :
    eraseRedirect n j c w < n + (eraseGate n Q j c).size := by
  change eraseRedirect n j c w < n + (eraseGate n Q j c).gates.length
  rw [LiftAux.eraseGate_gates_length n Q j c hj]
  change j < Q.gates.length at hj
  change w < n + Q.gates.length at hw
  unfold eraseRedirect
  split_ifs <;> omega

lemma erase_copy_residual (n : ℕ) (F : (Fin n → Bool) → Bool)
    (Q : Circuit) (B : List (ℕ × ℕ)) (j c : ℕ)
    (hres : IsResidual n F Q B) (hj : j < Q.size)
    (hcopy : gateAt Q j = ⟨GateOp.or, [c, c]⟩) (hc : c < n + j) :
    ∃ (E : Circuit) (A : List (ℕ × ℕ)), IsResidual n F E A ∧
      E.size + 2 * A.length + 1 = Q.size + 2 * B.length := by
  let E : Circuit := eraseGate n Q j c
  let A : List (ℕ × ℕ) := B.map (fun t => (eraseRedirect n j c t.1, eraseRedirect n j c t.2))
  have hsize : E.size + 1 = Q.size := by
    change (eraseGate n Q j c).gates.length + 1 = Q.gates.length
    rw [LiftAux.eraseGate_gates_length n Q j c hj]
    change j < Q.gates.length at hj
    omega
  have hget := copy_getElem_option Q j c hj hcopy
  refine ⟨E, A, ⟨LiftAux.eraseGate_isAO2 n Q j c hres.1 hj hc, ?_, ?_, ?_⟩, ?_⟩
  · intro t ht
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp ht
    exact ⟨erase_copy_bound n Q j c s.1 hj hc (hres.2.1 s hs).1,
      erase_copy_bound n Q j c s.2 hj hc (hres.2.1 s hs).2⟩
  · intro w hw
    let wold : ℕ := if w < n + j then w else w + 1
    have hwold : wold < n + Q.size := by dsimp [wold]; split_ifs <;> omega
    obtain ⟨x, hx, hfalse⟩ := hres.2.2.1 wold hwold
    refine ⟨x, ?_, hfalse⟩
    have heq := eraseGate_wires_eq_of_copy n Q j c hres.1 hj hc hget (List.ofFn x)
      (by simp) w hw
    change PEqualNP.BlindGate.wireValue E n x w =
      PEqualNP.BlindGate.wireValue Q n x wold at heq
    exact heq.trans hx
  · intro x
    rw [hres.2.2.2 x]
    constructor
    · rintro ⟨t, ht, h1, h2⟩
      refine ⟨(eraseRedirect n j c t.1, eraseRedirect n j c t.2),
        List.mem_map.mpr ⟨t, ht, rfl⟩, ?_, ?_⟩
      · exact (erase_copy_wire n Q j c hres.1 hj hc hcopy x t.1 (hres.2.1 t ht).1).trans h1
      · exact (erase_copy_wire n Q j c hres.1 hj hc hcopy x t.2 (hres.2.1 t ht).2).trans h2
    · rintro ⟨s, hs, h1, h2⟩
      obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hs
      refine ⟨t, ht, ?_, ?_⟩
      · exact (erase_copy_wire n Q j c hres.1 hj hc hcopy x t.1 (hres.2.1 t ht).1).symm.trans h1
      · exact (erase_copy_wire n Q j c hres.1 hj hc hcopy x t.2 (hres.2.1 t ht).2).symm.trans h2
  · have hlen : A.length = B.length := List.length_map _
    omega

end CopyErase


namespace GlobalOrFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover
open ProductFactor

def copyGate (D : Circuit) (j c : ℕ) : Circuit :=
  ⟨D.gates.set j ⟨GateOp.or, [c, c]⟩, D.output⟩

def IsOrFrontier (n : ℕ) (D : Circuit) (j : ℕ) (S : ℕ → Prop) : Prop :=
  (∀ w < n + j, ¬ S w) ∧ S (n + j) ∧
    ∀ k < D.size, k ≠ j →
      (S (n + k) ↔ ∃ u ∈ (gateAt D k).inputs, S u) ∧
      (S (n + k) → (gateAt D k).op = GateOp.or)

lemma copyGate_size (D : Circuit) (j c : ℕ) : (copyGate D j c).size = D.size := by
  simp [copyGate, Circuit.size]

lemma copyGate_at (D : Circuit) (j c k : ℕ) (hk : k < D.size) :
    gateAt (copyGate D j c) k =
      if j = k then ⟨GateOp.or, [c, c]⟩ else gateAt D k := by
  rw [SplitAux.gateAt_eq_getElem (copyGate D j c) k (by simpa [copyGate, Circuit.size] using hk),
    SplitAux.gateAt_eq_getElem D k hk]
  exact List.getElem_set _

lemma copyGate_ao2 (n : ℕ) (D : Circuit) (j c : ℕ)
    (hD : IsAO2 n D) (hc : c < n + j) : IsAO2 n (copyGate D j c) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨k, hk, hkg⟩ := List.mem_iff_getElem.mp hg
    have hkD : k < D.size := by simpa [copyGate, Circuit.size] using hk
    have heq : gateAt (copyGate D j c) k = g :=
      (SplitAux.gateAt_eq_getElem _ k hk).trans hkg
    rw [copyGate_at D j c k hkD] at heq
    by_cases hjk : j = k
    · rw [ite_eq_left hjk] at heq
      rw [← heq]
      exact Or.inr rfl
    · rw [ite_eq_right hjk] at heq
      rw [← heq, SplitAux.gateAt_eq_getElem D k hkD]
      exact hD.1 _ (List.getElem_mem hkD)
  · intro k hk w hw
    have hkD : k < D.size := by simpa [copyGate, Circuit.size] using hk
    rw [copyGate_at D j c k hkD] at hw
    by_cases hjk : j = k
    · rw [ite_eq_left hjk] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false, or_self] at hw
      subst w
      omega
    · rw [ite_eq_right hjk] at hw
      exact hD.2.1 k hkD w hw
  · intro g hg
    obtain ⟨k, hk, hkg⟩ := List.mem_iff_getElem.mp hg
    have hkD : k < D.size := by simpa [copyGate, Circuit.size] using hk
    have heq : gateAt (copyGate D j c) k = g :=
      (SplitAux.gateAt_eq_getElem _ k hk).trans hkg
    rw [copyGate_at D j c k hkD] at heq
    by_cases hjk : j = k
    · rw [ite_eq_left hjk] at heq
      rw [← heq]
      rfl
    · rw [ite_eq_right hjk] at heq
      rw [← heq, SplitAux.gateAt_eq_getElem D k hkD]
      exact hD.2.2 _ (List.getElem_mem hkD)

lemma frontier_dominates (n : ℕ) (D : Circuit) (j : ℕ) (S : ℕ → Prop)
    (hD : IsAO2 n D) (hS : IsOrFrontier n D j S) :
    ∀ w < n + D.size, S w → ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x (n + j) = true →
      PEqualNP.BlindGate.wireValue D n x w = true := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hs x hJ
    by_cases hwj : w = n + j
    · simpa only [hwj] using hJ
    have hlarge : n + j < w := by
      have hnot : ¬ w < n + j := fun h => hS.1 w h hs
      omega
    let k := w - n
    have hwk : w = n + k := by dsimp [k]; omega
    have hk : k < D.size := by omega
    have hkj : k ≠ j := by omega
    have hsk : S (n + k) := by rwa [← hwk]
    obtain ⟨u, hu, hsu⟩ := (hS.2.2 k hk hkj).1.mp hsk
    have huw : u < w := by have := hD.2.1 k hk u hu; omega
    have huD : u < n + D.size := by omega
    have hval := ih u huw huD hsu x hJ
    rw [hwk, SplitAux.wireValue_gate n D x k hk hD.2.1, (hS.2.2 k hk hkj).2 hsk]
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
    exact ⟨PEqualNP.BlindGate.wireValue D n x u, ⟨u, hu, rfl⟩, hval⟩

lemma copyGate_frontier_values (n : ℕ) (D : Circuit) (j A C : ℕ) (S : ℕ → Prop) [DecidablePred S]
    (hD : IsAO2 n D) (hj : j < D.size)
    (hgate : gateAt D j = ⟨GateOp.and, [A, C]⟩) (hS : IsOrFrontier n D j S)
    (x : Fin n → Bool) :
    ∀ w < n + D.size,
      PEqualNP.BlindGate.wireValue (copyGate D j C) n x w =
        if S w then
          (PEqualNP.BlindGate.wireValue D n x w || PEqualNP.BlindGate.wireValue D n x C)
        else PEqualNP.BlindGate.wireValue D n x w := by
  classical
  have hC : C < n + j := hD.2.1 j hj C (by rw [hgate]; simp)
  have hCD : C < n + D.size := by omega
  have hnew : IsAO2 n (copyGate D j C) := copyGate_ao2 n D j C hD hC
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hinput : w < n
    · have hnot : ¬ S w := hS.1 w (by omega)
      rw [ite_eq_right hnot, SplitAux.wireValue_input n (copyGate D j C) x w hinput,
        SplitAux.wireValue_input n D x w hinput]
    · let k := w - n
      have hwk : w = n + k := by dsimp [k]; omega
      have hk : k < D.size := by omega
      have hknew : k < (copyGate D j C).size := by rwa [copyGate_size]
      by_cases hkj : k = j
      · have hwj : w = n + j := by omega
        have ihC := ih C (by omega) hCD
        rw [ite_eq_right (hS.1 C hC)] at ihC
        rw [hwj, ite_eq_left hS.2.1,
          SplitAux.wireValue_gate n (copyGate D j C) x j (by simpa [copyGate, Circuit.size] using hj) hnew.2.1,
          copyGate_at D j C j hj, ite_eq_left rfl,
          SplitAux.wireValue_gate n D x j hj hD.2.1, hgate]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
          List.all_cons, List.all_nil, id_eq, Bool.or_false, Bool.and_true]
        rw [ihC]
        cases ha : PEqualNP.BlindGate.wireValue D n x A <;>
          cases hc : PEqualNP.BlindGate.wireValue D n x C <;> rfl
      · obtain ⟨u, v, hin, hu, hv⟩ := SplitAux.gate_inputs_two n D hD k hk
        have ihu := ih u (by omega) (by omega)
        have ihv := ih v (by omega) (by omega)
        have hnewval := SplitAux.wireValue_gate n (copyGate D j C) x k hknew hnew.2.1
        rw [copyGate_at D j C k hk, ite_eq_right (Ne.symm hkj), hin] at hnewval
        simp only [List.map_cons, List.map_nil] at hnewval
        have holdval := SplitAux.wireValue_gate n D x k hk hD.2.1
        rw [hin] at holdval
        simp only [List.map_cons, List.map_nil] at holdval
        have hiff : S (n + k) ↔ S u ∨ S v := by
          simpa [hin] using (hS.2.2 k hk hkj).1
        rw [hwk, hnewval, ihu, ihv, holdval]
        by_cases hs : S (n + k)
        · have hor := (hS.2.2 k hk hkj).2 hs
          rw [ite_eq_left hs, hor]
          have huv : S u ∨ S v := hiff.mp hs
          by_cases hsu : S u <;> by_cases hsv : S v <;>
            cases hwu : PEqualNP.BlindGate.wireValue D n x u <;>
            cases hwv : PEqualNP.BlindGate.wireValue D n x v <;>
            cases hwc : PEqualNP.BlindGate.wireValue D n x C <;>
            simp_all [GateOp.eval]
        · have hsu : ¬ S u := fun h => hs (hiff.mpr (Or.inl h))
          have hsv : ¬ S v := fun h => hs (hiff.mpr (Or.inr h))
          simp only [ite_eq_right hs, ite_eq_right hsu, ite_eq_right hsv]


lemma frontier_pair_disjoint (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (j : ℕ) (S : ℕ → Prop)
    (hres : IsResidual n F D B) (hj : j < D.size) (hS : IsOrFrontier n D j S) :
    ∀ t ∈ B, ¬ (S t.1 ∧ S t.2) := by
  intro t ht hs
  obtain ⟨x, hJ, hfalse⟩ := hres.2.2.1 (n + j) (by omega)
  have h1 := frontier_dominates n D j S hres.1 hS t.1 (hres.2.1 t ht).1 hs.1 x hJ
  have h2 := frontier_dominates n D j S hres.1 hS t.2 (hres.2.1 t ht).2 hs.2 x hJ
  have htrue : F x = true := (hres.2.2.2 x).mpr ⟨t, ht, h1, h2⟩
  rw [hfalse] at htrue
  cases htrue

lemma copyGate_wire_mono (n : ℕ) (D : Circuit) (j A C : ℕ) (S : ℕ → Prop)
    (hD : IsAO2 n D) (hj : j < D.size)
    (hgate : gateAt D j = ⟨GateOp.and, [A, C]⟩) (hS : IsOrFrontier n D j S)
    (x : Fin n → Bool) (w : ℕ) (hw : w < n + D.size)
    (htrue : PEqualNP.BlindGate.wireValue D n x w = true) :
    PEqualNP.BlindGate.wireValue (copyGate D j C) n x w = true := by
  classical
  rw [copyGate_frontier_values n D j A C S hD hj hgate hS x w hw]
  by_cases hs : S w
  · rw [ite_eq_left hs, htrue]
    rfl
  · rwa [ite_eq_right hs]

lemma copyGate_preserves_residual (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (j A C : ℕ) (S : ℕ → Prop)
    (hres : IsResidual n F D B) (hj : j < D.size)
    (hgate : gateAt D j = ⟨GateOp.and, [A, C]⟩) (hS : IsOrFrontier n D j S)
    (hleft : ∀ t ∈ B, S t.1 → ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x t.2 = true →
      PEqualNP.BlindGate.wireValue D n x C = true → F x = true)
    (hright : ∀ t ∈ B, S t.2 → ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x t.1 = true →
      PEqualNP.BlindGate.wireValue D n x C = true → F x = true) :
    IsResidual n F (copyGate D j C) B := by
  classical
  have hC : C < n + j := hres.1.2.1 j hj C (by rw [hgate]; simp)
  have hdisjoint := frontier_pair_disjoint n F D B j S hres hj hS
  refine ⟨copyGate_ao2 n D j C hres.1 hC, ?_, ?_, ?_⟩
  · intro t ht
    simpa only [copyGate_size] using hres.2.1 t ht
  · intro w hw
    rw [copyGate_size] at hw
    obtain ⟨x, hx, hfalse⟩ := hres.2.2.1 w hw
    exact ⟨x, copyGate_wire_mono n D j A C S hres.1 hj hgate hS x w hw hx, hfalse⟩
  · intro x
    constructor
    · intro hF
      obtain ⟨t, ht, h1, h2⟩ := (hres.2.2.2 x).mp hF
      exact ⟨t, ht,
        copyGate_wire_mono n D j A C S hres.1 hj hgate hS x t.1 (hres.2.1 t ht).1 h1,
        copyGate_wire_mono n D j A C S hres.1 hj hgate hS x t.2 (hres.2.1 t ht).2 h2⟩
    · rintro ⟨t, ht, h1, h2⟩
      have hval1 := copyGate_frontier_values n D j A C S hres.1 hj hgate hS x t.1
        (hres.2.1 t ht).1
      have hval2 := copyGate_frontier_values n D j A C S hres.1 hj hgate hS x t.2
        (hres.2.1 t ht).2
      by_cases hs1 : S t.1
      · have hs2 : ¬ S t.2 := fun h => hdisjoint t ht ⟨hs1, h⟩
        rw [hval1, ite_eq_left hs1, Bool.or_eq_true] at h1
        rw [hval2, ite_eq_right hs2] at h2
        rcases h1 with h1 | hCval
        · exact (hres.2.2.2 x).mpr ⟨t, ht, h1, h2⟩
        · exact hleft t ht hs1 x h2 hCval
      · rw [hval1, ite_eq_right hs1] at h1
        by_cases hs2 : S t.2
        · rw [hval2, ite_eq_left hs2, Bool.or_eq_true] at h2
          rcases h2 with h2 | hCval
          · exact (hres.2.2.2 x).mpr ⟨t, ht, h1, h2⟩
          · exact hright t ht hs2 x h1 hCval
        · rw [hval2, ite_eq_right hs2] at h2
          exact (hres.2.2.2 x).mpr ⟨t, ht, h1, h2⟩

lemma erase_or_frontier_factor (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (j A C : ℕ) (S : ℕ → Prop)
    (hres : IsResidual n F D B) (hj : j < D.size)
    (hgate : gateAt D j = ⟨GateOp.and, [A, C]⟩) (hS : IsOrFrontier n D j S)
    (hleft : ∀ t ∈ B, S t.1 → ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x t.2 = true →
      PEqualNP.BlindGate.wireValue D n x C = true → F x = true)
    (hright : ∀ t ∈ B, S t.2 → ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x t.1 = true →
      PEqualNP.BlindGate.wireValue D n x C = true → F x = true) :
    ∃ (E : Circuit) (T : List (ℕ × ℕ)), IsResidual n F E T ∧
      E.size + 2 * T.length + 1 = D.size + 2 * B.length := by
  have hnew := copyGate_preserves_residual n F D B j A C S hres hj hgate hS hleft hright
  have hC : C < n + j := hres.1.2.1 j hj C (by rw [hgate]; simp)
  have hjnew : j < (copyGate D j C).size := by rwa [copyGate_size]
  have hcopy : gateAt (copyGate D j C) j = ⟨GateOp.or, [C, C]⟩ := by
    rw [copyGate_at D j C j hj, ite_eq_left rfl]
  obtain ⟨E, T, hET, hcost⟩ := CopyErase.erase_copy_residual n F (copyGate D j C) B j C
    hnew hjnew hcopy hC
  exact ⟨E, T, hET, by simpa only [copyGate_size] using hcost⟩

end GlobalOrFrontier

namespace GlobalOrFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover

def inputEdge (n : ℕ) (D : Circuit) (u v : ℕ) : Prop :=
  ∃ k < D.size, v = n + k ∧ u ∈ (gateAt D k).inputs

def descendants (n : ℕ) (D : Circuit) (j w : ℕ) : Prop :=
  Relation.ReflTransGen (inputEdge n D) (n + j) w

lemma inputEdge_lt (n : ℕ) (D : Circuit) (hD : IsAO2 n D)
    {u v : ℕ} (h : inputEdge n D u v) : u < v := by
  obtain ⟨k, hk, rfl, hu⟩ := h
  exact hD.2.1 k hk u hu

lemma descendants_le (n : ℕ) (D : Circuit) (j w : ℕ)
    (hD : IsAO2 n D) (h : descendants n D j w) : n + j ≤ w := by
  induction h with
  | refl => exact Nat.le_refl _
  | tail h he ih => exact Nat.le_trans ih (Nat.le_of_lt (inputEdge_lt n D hD he))

lemma descendants_gate (n : ℕ) (D : Circuit) (j k : ℕ)
    (hk : k < D.size) (hkj : k ≠ j) :
    descendants n D j (n + k) ↔
      ∃ u ∈ (gateAt D k).inputs, descendants n D j u := by
  constructor
  · intro h
    rcases Relation.ReflTransGen.cases_tail h with heq | ⟨u, hu, hedge⟩
    · omega
    · obtain ⟨i, hi, heq, hui⟩ := hedge
      have hik : i = k := by omega
      subst i
      exact ⟨u, hui, hu⟩
  · rintro ⟨u, hu, hreach⟩
    exact Relation.ReflTransGen.tail hreach ⟨k, hk, rfl, hu⟩

lemma descendants_frontier (n : ℕ) (D : Circuit) (j : ℕ)
    (hD : IsAO2 n D)
    (hterminal : ∀ k < D.size, k ≠ j → descendants n D j (n + k) →
      (gateAt D k).op = GateOp.or) :
    IsOrFrontier n D j (descendants n D j) := by
  refine ⟨?_, Relation.ReflTransGen.refl, ?_⟩
  · intro w hw hreach
    have := descendants_le n D j w hD hreach
    omega
  · intro k hk hkj
    exact ⟨descendants_gate n D j k hk hkj, hterminal k hk hkj⟩

lemma last_and_descendants_frontier (n : ℕ) (D : Circuit) (j : ℕ)
    (hD : IsAO2 n D)
    (hlast : ∀ k < D.size, j < k → (gateAt D k).op = GateOp.or) :
    IsOrFrontier n D j (descendants n D j) := by
  apply descendants_frontier n D j hD
  intro k hk hkj hreach
  have := descendants_le n D j (n + k) hD hreach
  exact hlast k hk (by omega)

lemma exists_and_descendants_frontier (n : ℕ) (D : Circuit)
    (hD : IsAO2 n D)
    (hAND : ∃ j < D.size, (gateAt D j).op = GateOp.and) :
    ∃ j < D.size, (gateAt D j).op = GateOp.and ∧
      IsOrFrontier n D j (descendants n D j) := by
  classical
  let J : Finset ℕ := (Finset.range D.size).filter (fun k => (gateAt D k).op = GateOp.and)
  have hJ : J.Nonempty := by
    obtain ⟨j, hj, hop⟩ := hAND
    exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hop⟩⟩
  let j := J.max' hJ
  have hjJ : j ∈ J := Finset.max'_mem J hJ
  obtain ⟨hj, hop⟩ := Finset.mem_filter.mp hjJ
  have hjD : j < D.size := Finset.mem_range.mp hj
  refine ⟨j, hjD, hop, last_and_descendants_frontier n D j hD ?_⟩
  intro k hk hjk
  have hmem : gateAt D k ∈ D.gates := by
    rw [SplitAux.gateAt_eq_getElem D k hk]
    exact List.getElem_mem hk
  rcases hD.1 (gateAt D k) hmem with hand | hor
  · have hkJ : k ∈ J := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hand⟩
    have hkle : k ≤ j := Finset.le_max' J k hkJ
    omega
  · exact hor

end GlobalOrFrontier

namespace GlobalOrFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover
open ProductFactor

lemma minimum_frontier_right_child_has_unsafe_partner (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (j A C : ℕ) (S : ℕ → Prop)
    (hres : IsResidual n F D B) (hj : j < D.size)
    (hgate : gateAt D j = ⟨GateOp.and, [A, C]⟩) (hS : IsOrFrontier n D j S)
    (hmin : ∀ (E : Circuit) (T : List (ℕ × ℕ)), IsResidual n F E T →
      D.size + 2 * B.length ≤ E.size + 2 * T.length) :
    ∃ t ∈ B, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x C = true ∧ F x = false ∧
      ((S t.1 ∧ ¬ S t.2 ∧ PEqualNP.BlindGate.wireValue D n x t.2 = true) ∨
        (S t.2 ∧ ¬ S t.1 ∧ PEqualNP.BlindGate.wireValue D n x t.1 = true)) := by
  classical
  by_contra hn
  have hdisjoint := frontier_pair_disjoint n F D B j S hres hj hS
  have hleft : ∀ t ∈ B, S t.1 → ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x t.2 = true →
      PEqualNP.BlindGate.wireValue D n x C = true → F x = true := by
    intro t ht hs x hpartner hC
    by_contra hF
    have hfalse : F x = false := by simpa only [Bool.not_eq_true] using hF
    have hnot : ¬ S t.2 := fun h => hdisjoint t ht ⟨hs, h⟩
    exact hn ⟨t, ht, x, hC, hfalse, Or.inl ⟨hs, hnot, hpartner⟩⟩
  have hright : ∀ t ∈ B, S t.2 → ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x t.1 = true →
      PEqualNP.BlindGate.wireValue D n x C = true → F x = true := by
    intro t ht hs x hpartner hC
    by_contra hF
    have hfalse : F x = false := by simpa only [Bool.not_eq_true] using hF
    have hnot : ¬ S t.1 := fun h => hdisjoint t ht ⟨h, hs⟩
    exact hn ⟨t, ht, x, hC, hfalse, Or.inr ⟨hs, hnot, hpartner⟩⟩
  obtain ⟨E, T, hET, hcost⟩ := erase_or_frontier_factor n F D B j A C S
    hres hj hgate hS hleft hright
  have := hmin E T hET
  omega

end GlobalOrFrontier


namespace GlobalOrFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover
open ProductFactor

lemma copyGate_frontier_values_of_dominating (n : ℕ) (D : Circuit) (j C : ℕ) (S : ℕ → Prop) [DecidablePred S]
    (hD : IsAO2 n D) (hj : j < D.size)
    (hC : C < n + j) (hS : IsOrFrontier n D j S)
    (hdom : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x (n + j) = true →
      PEqualNP.BlindGate.wireValue D n x C = true)
    (x : Fin n → Bool) :
    ∀ w < n + D.size,
      PEqualNP.BlindGate.wireValue (copyGate D j C) n x w =
        if S w then
          (PEqualNP.BlindGate.wireValue D n x w || PEqualNP.BlindGate.wireValue D n x C)
        else PEqualNP.BlindGate.wireValue D n x w := by
  classical
  have hCD : C < n + D.size := by omega
  have hnew : IsAO2 n (copyGate D j C) := copyGate_ao2 n D j C hD hC
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hinput : w < n
    · have hnot : ¬ S w := hS.1 w (by omega)
      rw [ite_eq_right hnot, SplitAux.wireValue_input n (copyGate D j C) x w hinput,
        SplitAux.wireValue_input n D x w hinput]
    · let k := w - n
      have hwk : w = n + k := by dsimp [k]; omega
      have hk : k < D.size := by omega
      have hknew : k < (copyGate D j C).size := by rwa [copyGate_size]
      by_cases hkj : k = j
      · have hwj : w = n + j := by omega
        have ihC := ih C (by omega) hCD
        rw [ite_eq_right (hS.1 C hC)] at ihC
        rw [hwj, ite_eq_left hS.2.1,
          SplitAux.wireValue_gate n (copyGate D j C) x j (by simpa [copyGate, Circuit.size] using hj) hnew.2.1,
          copyGate_at D j C j hj, ite_eq_left rfl]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
          id_eq, Bool.or_false]
        rw [ihC]
        have hd := hdom x
        cases hJ : PEqualNP.BlindGate.wireValue D n x (n + j) <;>
          cases hc : PEqualNP.BlindGate.wireValue D n x C <;> simp_all
      · obtain ⟨u, v, hin, hu, hv⟩ := SplitAux.gate_inputs_two n D hD k hk
        have ihu := ih u (by omega) (by omega)
        have ihv := ih v (by omega) (by omega)
        have hnewval := SplitAux.wireValue_gate n (copyGate D j C) x k hknew hnew.2.1
        rw [copyGate_at D j C k hk, ite_eq_right (Ne.symm hkj), hin] at hnewval
        simp only [List.map_cons, List.map_nil] at hnewval
        have holdval := SplitAux.wireValue_gate n D x k hk hD.2.1
        rw [hin] at holdval
        simp only [List.map_cons, List.map_nil] at holdval
        have hiff : S (n + k) ↔ S u ∨ S v := by
          simpa [hin] using (hS.2.2 k hk hkj).1
        rw [hwk, hnewval, ihu, ihv, holdval]
        by_cases hs : S (n + k)
        · have hor := (hS.2.2 k hk hkj).2 hs
          rw [ite_eq_left hs, hor]
          have huv : S u ∨ S v := hiff.mp hs
          by_cases hsu : S u <;> by_cases hsv : S v <;>
            cases hwu : PEqualNP.BlindGate.wireValue D n x u <;>
            cases hwv : PEqualNP.BlindGate.wireValue D n x v <;>
            cases hwc : PEqualNP.BlindGate.wireValue D n x C <;>
            simp_all [GateOp.eval]
        · have hsu : ¬ S u := fun h => hs (hiff.mpr (Or.inl h))
          have hsv : ¬ S v := fun h => hs (hiff.mpr (Or.inr h))
          simp only [ite_eq_right hs, ite_eq_right hsu, ite_eq_right hsv]

lemma copyGate_wire_mono_of_dominating (n : ℕ) (D : Circuit) (j c : ℕ) (S : ℕ → Prop)
    (hD : IsAO2 n D) (hj : j < D.size)
    (hc : c < n + j) (hS : IsOrFrontier n D j S)
    (hdom : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x (n + j) = true →
      PEqualNP.BlindGate.wireValue D n x c = true)
    (x : Fin n → Bool) (w : ℕ) (hw : w < n + D.size)
    (htrue : PEqualNP.BlindGate.wireValue D n x w = true) :
    PEqualNP.BlindGate.wireValue (copyGate D j c) n x w = true := by
  classical
  rw [copyGate_frontier_values_of_dominating n D j c S hD hj hc hS hdom x w hw]
  by_cases hs : S w
  · rw [ite_eq_left hs, htrue]
    rfl
  · rwa [ite_eq_right hs]

lemma copyGate_preserves_residual_of_dominating (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (j c : ℕ) (S : ℕ → Prop)
    (hres : IsResidual n F D B) (hj : j < D.size)
    (hc : c < n + j) (hS : IsOrFrontier n D j S)
    (hdom : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x (n + j) = true →
      PEqualNP.BlindGate.wireValue D n x c = true)
    (hleft : ∀ t ∈ B, S t.1 → ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x t.2 = true →
      PEqualNP.BlindGate.wireValue D n x c = true → F x = true)
    (hright : ∀ t ∈ B, S t.2 → ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x t.1 = true →
      PEqualNP.BlindGate.wireValue D n x c = true → F x = true) :
    IsResidual n F (copyGate D j c) B := by
  classical
  have hdisjoint := frontier_pair_disjoint n F D B j S hres hj hS
  refine ⟨copyGate_ao2 n D j c hres.1 hc, ?_, ?_, ?_⟩
  · intro t ht
    simpa only [copyGate_size] using hres.2.1 t ht
  · intro w hw
    rw [copyGate_size] at hw
    obtain ⟨x, hx, hfalse⟩ := hres.2.2.1 w hw
    exact ⟨x, copyGate_wire_mono_of_dominating n D j c S hres.1 hj hc hS hdom x w hw hx, hfalse⟩
  · intro x
    constructor
    · intro hF
      obtain ⟨t, ht, h1, h2⟩ := (hres.2.2.2 x).mp hF
      exact ⟨t, ht,
        copyGate_wire_mono_of_dominating n D j c S hres.1 hj hc hS hdom x t.1 (hres.2.1 t ht).1 h1,
        copyGate_wire_mono_of_dominating n D j c S hres.1 hj hc hS hdom x t.2 (hres.2.1 t ht).2 h2⟩
    · rintro ⟨t, ht, h1, h2⟩
      have hval1 := copyGate_frontier_values_of_dominating n D j c S hres.1 hj hc hS hdom x t.1
        (hres.2.1 t ht).1
      have hval2 := copyGate_frontier_values_of_dominating n D j c S hres.1 hj hc hS hdom x t.2
        (hres.2.1 t ht).2
      by_cases hs1 : S t.1
      · have hs2 : ¬ S t.2 := fun h => hdisjoint t ht ⟨hs1, h⟩
        rw [hval1, ite_eq_left hs1, Bool.or_eq_true] at h1
        rw [hval2, ite_eq_right hs2] at h2
        rcases h1 with h1 | hCval
        · exact (hres.2.2.2 x).mpr ⟨t, ht, h1, h2⟩
        · exact hleft t ht hs1 x h2 hCval
      · rw [hval1, ite_eq_right hs1] at h1
        by_cases hs2 : S t.2
        · rw [hval2, ite_eq_left hs2, Bool.or_eq_true] at h2
          rcases h2 with h2 | hCval
          · exact (hres.2.2.2 x).mpr ⟨t, ht, h1, h2⟩
          · exact hright t ht hs2 x h1 hCval
        · rw [hval2, ite_eq_right hs2] at h2
          exact (hres.2.2.2 x).mpr ⟨t, ht, h1, h2⟩

lemma erase_or_frontier_dominating (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (j c : ℕ) (S : ℕ → Prop)
    (hres : IsResidual n F D B) (hj : j < D.size)
    (hc : c < n + j) (hS : IsOrFrontier n D j S)
    (hdom : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x (n + j) = true →
      PEqualNP.BlindGate.wireValue D n x c = true)
    (hleft : ∀ t ∈ B, S t.1 → ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x t.2 = true →
      PEqualNP.BlindGate.wireValue D n x c = true → F x = true)
    (hright : ∀ t ∈ B, S t.2 → ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x t.1 = true →
      PEqualNP.BlindGate.wireValue D n x c = true → F x = true) :
    ∃ (E : Circuit) (T : List (ℕ × ℕ)), IsResidual n F E T ∧
      E.size + 2 * T.length + 1 = D.size + 2 * B.length := by
  have hnew := copyGate_preserves_residual_of_dominating n F D B j c S hres hj hc hS hdom hleft hright
  have hjnew : j < (copyGate D j c).size := by rwa [copyGate_size]
  have hcopy : gateAt (copyGate D j c) j = ⟨GateOp.or, [c, c]⟩ := by
    rw [copyGate_at D j c j hj, ite_eq_left rfl]
  obtain ⟨E, T, hET, hcost⟩ := CopyErase.erase_copy_residual n F (copyGate D j c) B j c
    hnew hjnew hcopy hc
  exact ⟨E, T, hET, by simpa only [copyGate_size] using hcost⟩

lemma minimum_frontier_dominating_has_unsafe_partner (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (j c : ℕ) (S : ℕ → Prop)
    (hres : IsResidual n F D B) (hj : j < D.size)
    (hc : c < n + j) (hS : IsOrFrontier n D j S)
    (hdom : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x (n + j) = true →
      PEqualNP.BlindGate.wireValue D n x c = true)
    (hmin : ∀ (E : Circuit) (T : List (ℕ × ℕ)), IsResidual n F E T →
      D.size + 2 * B.length ≤ E.size + 2 * T.length) :
    ∃ t ∈ B, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x c = true ∧ F x = false ∧
      ((S t.1 ∧ ¬ S t.2 ∧ PEqualNP.BlindGate.wireValue D n x t.2 = true) ∨
        (S t.2 ∧ ¬ S t.1 ∧ PEqualNP.BlindGate.wireValue D n x t.1 = true)) := by
  classical
  by_contra hn
  have hdisjoint := frontier_pair_disjoint n F D B j S hres hj hS
  have hleft : ∀ t ∈ B, S t.1 → ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x t.2 = true →
      PEqualNP.BlindGate.wireValue D n x c = true → F x = true := by
    intro t ht hs x hpartner hC
    by_contra hF
    have hfalse : F x = false := by simpa only [Bool.not_eq_true] using hF
    have hnot : ¬ S t.2 := fun h => hdisjoint t ht ⟨hs, h⟩
    exact hn ⟨t, ht, x, hC, hfalse, Or.inl ⟨hs, hnot, hpartner⟩⟩
  have hright : ∀ t ∈ B, S t.2 → ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x t.1 = true →
      PEqualNP.BlindGate.wireValue D n x c = true → F x = true := by
    intro t ht hs x hpartner hC
    by_contra hF
    have hfalse : F x = false := by simpa only [Bool.not_eq_true] using hF
    have hnot : ¬ S t.1 := fun h => hdisjoint t ht ⟨h, hs⟩
    exact hn ⟨t, ht, x, hC, hfalse, Or.inr ⟨hs, hnot, hpartner⟩⟩
  obtain ⟨E, T, hET, hcost⟩ := erase_or_frontier_dominating n F D B j c S
    hres hj hc hS hdom hleft hright
  have := hmin E T hET
  omega


end GlobalOrFrontier

namespace GlobalOrFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover
open ProductFactor

lemma minimum_frontier_dominating_has_separating_input (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (j c : ℕ) (S : ℕ → Prop)
    (hres : IsResidual n F D B) (hj : j < D.size) (hc : c < n + j)
    (hS : IsOrFrontier n D j S)
    (hdom : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x (n + j) = true →
      PEqualNP.BlindGate.wireValue D n x c = true)
    (hmin : ∀ (E : Circuit) (T : List (ℕ × ℕ)), IsResidual n F E T →
      D.size + 2 * B.length ≤ E.size + 2 * T.length) :
    ∃ t ∈ B, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x c = true ∧
      PEqualNP.BlindGate.wireValue D n x (n + j) = false ∧ F x = false ∧
      ((S t.1 ∧ ¬ S t.2 ∧ PEqualNP.BlindGate.wireValue D n x t.2 = true) ∨
        (S t.2 ∧ ¬ S t.1 ∧ PEqualNP.BlindGate.wireValue D n x t.1 = true)) := by
  obtain ⟨t, ht, x, hcval, hfalse, hcontext⟩ :=
    minimum_frontier_dominating_has_unsafe_partner n F D B j c S hres hj hc hS hdom hmin
  have hJfalse : PEqualNP.BlindGate.wireValue D n x (n + j) = false := by
    cases hJ : PEqualNP.BlindGate.wireValue D n x (n + j) with
    | false => rfl
    | true =>
      have hFtrue : F x = true := by
        rcases hcontext with hleft | hright
        · have h1 := frontier_dominates n D j S hres.1 hS t.1 (hres.2.1 t ht).1 hleft.1 x hJ
          exact (hres.2.2.2 x).mpr ⟨t, ht, h1, hleft.2.2⟩
        · have h2 := frontier_dominates n D j S hres.1 hS t.2 (hres.2.1 t ht).2 hright.1 x hJ
          exact (hres.2.2.2 x).mpr ⟨t, ht, hright.2.2, h2⟩
      rw [hfalse] at hFtrue
      cases hFtrue
  exact ⟨t, ht, x, hcval, hJfalse, hfalse, hcontext⟩

lemma minimum_frontier_and_children_have_separating_inputs (n : ℕ)
    (F : (Fin n → Bool) → Bool) (D : Circuit) (B : List (ℕ × ℕ))
    (j A C : ℕ) (S : ℕ → Prop) (hres : IsResidual n F D B) (hj : j < D.size)
    (hgate : gateAt D j = ⟨GateOp.and, [A, C]⟩) (hS : IsOrFrontier n D j S)
    (hmin : ∀ (E : Circuit) (T : List (ℕ × ℕ)), IsResidual n F E T →
      D.size + 2 * B.length ≤ E.size + 2 * T.length) :
    ∀ keep drop : ℕ, (keep = A ∧ drop = C) ∨ (keep = C ∧ drop = A) →
      ∃ t ∈ B, ∃ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue D n x keep = true ∧
        PEqualNP.BlindGate.wireValue D n x drop = false ∧ F x = false ∧
        ((S t.1 ∧ ¬ S t.2 ∧ PEqualNP.BlindGate.wireValue D n x t.2 = true) ∨
          (S t.2 ∧ ¬ S t.1 ∧ PEqualNP.BlindGate.wireValue D n x t.1 = true)) := by
  intro keep drop hwhich
  have hkeepMem : keep ∈ (gateAt D j).inputs := by
    rw [hgate]
    rcases hwhich with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp
  have hkeepBound : keep < n + j := hres.1.2.1 j hj keep hkeepMem
  have hpair (x : Fin n → Bool) :
      PEqualNP.BlindGate.wireValue D n x (n + j) = true ↔
      PEqualNP.BlindGate.wireValue D n x A = true ∧
        PEqualNP.BlindGate.wireValue D n x C = true := by
    rw [SplitAux.wireValue_gate n D x j hj hres.1.2.1, hgate]
    simp [GateOp.eval]
  have hdom : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x (n + j) = true →
      PEqualNP.BlindGate.wireValue D n x keep = true := by
    intro x hJ
    obtain ⟨hA, hC⟩ := (hpair x).mp hJ
    rcases hwhich with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact hA
    · exact hC
  obtain ⟨t, ht, x, hkeep, hJfalse, hfalse, hcontext⟩ :=
    minimum_frontier_dominating_has_separating_input n F D B j keep S
      hres hj hkeepBound hS hdom hmin
  have hdropnot : PEqualNP.BlindGate.wireValue D n x drop ≠ true := by
    intro hdrop
    have hJtrue : PEqualNP.BlindGate.wireValue D n x (n + j) = true := by
      apply (hpair x).mpr
      rcases hwhich with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hkeep, hdrop⟩
      · exact ⟨hdrop, hkeep⟩
    rw [hJfalse] at hJtrue
    cases hJtrue
  exact ⟨t, ht, x, hkeep, by simpa only [Bool.not_eq_true] using hdropnot, hfalse, hcontext⟩

end GlobalOrFrontier


namespace GlobalOrFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover
open ProductFactor

def IsForwardClosure (n : ℕ) (D : Circuit) (j : ℕ) (S : ℕ → Prop) : Prop :=
  (∀ w < n + j, ¬ S w) ∧ S (n + j) ∧
    ∀ k < D.size, k ≠ j → (S (n + k) ↔ ∃ u ∈ (gateAt D k).inputs, S u)

lemma or_frontier_forward_closure (n : ℕ) (D : Circuit) (j : ℕ) (S : ℕ → Prop)
    (hS : IsOrFrontier n D j S) : IsForwardClosure n D j S :=
  ⟨hS.1, hS.2.1, fun k hk hkj => (hS.2.2 k hk hkj).1⟩

lemma copyGate_forward_bounds (n : ℕ) (D : Circuit) (j c : ℕ) (S : ℕ → Prop)
    (hD : IsAO2 n D) (hj : j < D.size) (hc : c < n + j)
    (hS : IsForwardClosure n D j S)
    (hdom : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x (n + j) = true →
      PEqualNP.BlindGate.wireValue D n x c = true) (x : Fin n → Bool) :
    ∀ w < n + D.size,
      (PEqualNP.BlindGate.wireValue D n x w = true →
        PEqualNP.BlindGate.wireValue (copyGate D j c) n x w = true) ∧
      (PEqualNP.BlindGate.wireValue (copyGate D j c) n x w = true →
        PEqualNP.BlindGate.wireValue D n x w = true ∨
          (S w ∧ PEqualNP.BlindGate.wireValue D n x c = true)) := by
  have hcD : c < n + D.size := by omega
  have hnew : IsAO2 n (copyGate D j c) := copyGate_ao2 n D j c hD hc
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw
    by_cases hinput : w < n
    · rw [SplitAux.wireValue_input n (copyGate D j c) x w hinput,
        SplitAux.wireValue_input n D x w hinput]
      exact ⟨fun h => h, fun h => Or.inl h⟩
    · let k := w - n
      have hwk : w = n + k := by dsimp [k]; omega
      have hk : k < D.size := by omega
      have hknew : k < (copyGate D j c).size := by rwa [copyGate_size]
      by_cases hkj : k = j
      · have hwj : w = n + j := by omega
        obtain ⟨hcm, hcu⟩ := ih c (by omega) hcD
        have hceq : PEqualNP.BlindGate.wireValue (copyGate D j c) n x c =
            PEqualNP.BlindGate.wireValue D n x c := by
          apply Bool.eq_iff_iff.mpr
          constructor
          · intro h
            rcases hcu h with h | h
            · exact h
            · exact False.elim (hS.1 c hc h.1)
          · exact hcm
        have hnewJ : PEqualNP.BlindGate.wireValue (copyGate D j c) n x (n + j) =
            PEqualNP.BlindGate.wireValue D n x c := by
          rw [SplitAux.wireValue_gate n (copyGate D j c) x j
            (by simpa [copyGate, Circuit.size] using hj) hnew.2.1,
            copyGate_at D j c j hj, ite_eq_left rfl]
          simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
            id_eq, Bool.or_false, Bool.or_self, hceq]
        rw [hwj, hnewJ]
        exact ⟨hdom x, fun h => Or.inr ⟨hS.2.1, h⟩⟩
      · obtain ⟨u, v, hin, hu, hv⟩ := SplitAux.gate_inputs_two n D hD k hk
        obtain ⟨hmu, hbu⟩ := ih u (by omega) (by omega)
        obtain ⟨hmv, hbv⟩ := ih v (by omega) (by omega)
        have hnewval := SplitAux.wireValue_gate n (copyGate D j c) x k hknew hnew.2.1
        rw [copyGate_at D j c k hk, ite_eq_right (Ne.symm hkj), hin] at hnewval
        simp only [List.map_cons, List.map_nil] at hnewval
        have holdval := SplitAux.wireValue_gate n D x k hk hD.2.1
        rw [hin] at holdval
        simp only [List.map_cons, List.map_nil] at holdval
        have hiff : S (n + k) ↔ S u ∨ S v := by
          simpa [hin] using hS.2.2 k hk hkj
        have hmark : S u ∨ S v → S (n + k) := hiff.mpr
        have hop : (gateAt D k).op = GateOp.and ∨ (gateAt D k).op = GateOp.or := by
          rw [SplitAux.gateAt_eq_getElem D k hk]
          exact hD.1 _ (List.getElem_mem hk)
        rw [hwk, holdval, hnewval]
        rcases hop with hop | hop
        · rw [hop]
          simp only [GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true,
            Bool.and_eq_true]
          constructor
          · rintro ⟨h1, h2⟩
            exact ⟨hmu h1, hmv h2⟩
          · rintro ⟨h1, h2⟩
            rcases hbu h1 with huold | huchange
            · rcases hbv h2 with hvold | hvchange
              · exact Or.inl ⟨huold, hvold⟩
              · exact Or.inr ⟨hmark (Or.inr hvchange.1), hvchange.2⟩
            · exact Or.inr ⟨hmark (Or.inl huchange.1), huchange.2⟩
        · rw [hop]
          simp only [GateOp.eval, List.any_cons, List.any_nil, id_eq, Bool.or_false,
            Bool.or_eq_true]
          constructor
          · intro h
            rcases h with h | h
            · exact Or.inl (hmu h)
            · exact Or.inr (hmv h)
          · intro h
            rcases h with h | h
            · rcases hbu h with huold | huchange
              · exact Or.inl (Or.inl huold)
              · exact Or.inr ⟨hmark (Or.inl huchange.1), huchange.2⟩
            · rcases hbv h with hvold | hvchange
              · exact Or.inl (Or.inr hvold)
              · exact Or.inr ⟨hmark (Or.inr hvchange.1), hvchange.2⟩


lemma copyGate_preserves_residual_mixed (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (j c : ℕ) (S : ℕ → Prop)
    (hres : IsResidual n F D B) (hj : j < D.size)
    (hc : c < n + j) (hS : IsForwardClosure n D j S)
    (hdom : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x (n + j) = true →
      PEqualNP.BlindGate.wireValue D n x c = true)
    (hdisjoint : ∀ t ∈ B, ¬ (S t.1 ∧ S t.2))
    (hleft : ∀ t ∈ B, S t.1 → ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x t.2 = true →
      PEqualNP.BlindGate.wireValue D n x c = true → F x = true)
    (hright : ∀ t ∈ B, S t.2 → ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x t.1 = true →
      PEqualNP.BlindGate.wireValue D n x c = true → F x = true) :
    IsResidual n F (copyGate D j c) B := by
  refine ⟨copyGate_ao2 n D j c hres.1 hc, ?_, ?_, ?_⟩
  · intro t ht
    simpa only [copyGate_size] using hres.2.1 t ht
  · intro w hw
    rw [copyGate_size] at hw
    obtain ⟨x, hx, hfalse⟩ := hres.2.2.1 w hw
    exact ⟨x, (copyGate_forward_bounds n D j c S hres.1 hj hc hS hdom x w hw).1 hx, hfalse⟩
  · intro x
    constructor
    · intro hF
      obtain ⟨t, ht, h1, h2⟩ := (hres.2.2.2 x).mp hF
      exact ⟨t, ht,
        (copyGate_forward_bounds n D j c S hres.1 hj hc hS hdom x t.1 (hres.2.1 t ht).1).1 h1,
        (copyGate_forward_bounds n D j c S hres.1 hj hc hS hdom x t.2 (hres.2.1 t ht).2).1 h2⟩
    · rintro ⟨t, ht, h1, h2⟩
      have hupper1 :=
        (copyGate_forward_bounds n D j c S hres.1 hj hc hS hdom x t.1 (hres.2.1 t ht).1).2 h1
      have hupper2 :=
        (copyGate_forward_bounds n D j c S hres.1 hj hc hS hdom x t.2 (hres.2.1 t ht).2).2 h2
      rcases hupper1 with hold1 | ⟨hs1, hc1⟩
      · rcases hupper2 with hold2 | ⟨hs2, hc2⟩
        · exact (hres.2.2.2 x).mpr ⟨t, ht, hold1, hold2⟩
        · exact hright t ht hs2 x hold1 hc2
      · rcases hupper2 with hold2 | ⟨hs2, hc2⟩
        · exact hleft t ht hs1 x hold2 hc1
        · exact False.elim (hdisjoint t ht ⟨hs1, hs2⟩)

lemma erase_mixed_frontier_dominating (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (j c : ℕ) (S : ℕ → Prop)
    (hres : IsResidual n F D B) (hj : j < D.size)
    (hc : c < n + j) (hS : IsForwardClosure n D j S)
    (hdom : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x (n + j) = true →
      PEqualNP.BlindGate.wireValue D n x c = true)
    (hdisjoint : ∀ t ∈ B, ¬ (S t.1 ∧ S t.2))
    (hleft : ∀ t ∈ B, S t.1 → ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x t.2 = true →
      PEqualNP.BlindGate.wireValue D n x c = true → F x = true)
    (hright : ∀ t ∈ B, S t.2 → ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x t.1 = true →
      PEqualNP.BlindGate.wireValue D n x c = true → F x = true) :
    ∃ (E : Circuit) (T : List (ℕ × ℕ)), IsResidual n F E T ∧
      E.size + 2 * T.length + 1 = D.size + 2 * B.length := by
  have hnew := copyGate_preserves_residual_mixed n F D B j c S
    hres hj hc hS hdom hdisjoint hleft hright
  have hjnew : j < (copyGate D j c).size := by rwa [copyGate_size]
  have hcopy : gateAt (copyGate D j c) j = ⟨GateOp.or, [c, c]⟩ := by
    rw [copyGate_at D j c j hj, ite_eq_left rfl]
  obtain ⟨E, T, hET, hcost⟩ := CopyErase.erase_copy_residual n F (copyGate D j c) B j c
    hnew hjnew hcopy hc
  exact ⟨E, T, hET, by simpa only [copyGate_size] using hcost⟩

lemma minimum_mixed_frontier_has_unsafe_partner (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (j c : ℕ) (S : ℕ → Prop)
    (hres : IsResidual n F D B) (hj : j < D.size)
    (hc : c < n + j) (hS : IsForwardClosure n D j S)
    (hdom : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x (n + j) = true →
      PEqualNP.BlindGate.wireValue D n x c = true)
    (hdisjoint : ∀ t ∈ B, ¬ (S t.1 ∧ S t.2))
    (hmin : ∀ (E : Circuit) (T : List (ℕ × ℕ)), IsResidual n F E T →
      D.size + 2 * B.length ≤ E.size + 2 * T.length) :
    ∃ t ∈ B, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x c = true ∧ F x = false ∧
      ((S t.1 ∧ ¬ S t.2 ∧ PEqualNP.BlindGate.wireValue D n x t.2 = true) ∨
        (S t.2 ∧ ¬ S t.1 ∧ PEqualNP.BlindGate.wireValue D n x t.1 = true)) := by
  classical
  by_contra hn
  have hleft : ∀ t ∈ B, S t.1 → ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x t.2 = true →
      PEqualNP.BlindGate.wireValue D n x c = true → F x = true := by
    intro t ht hs x hpartner hC
    by_contra hF
    have hfalse : F x = false := by simpa only [Bool.not_eq_true] using hF
    have hnot : ¬ S t.2 := fun h => hdisjoint t ht ⟨hs, h⟩
    exact hn ⟨t, ht, x, hC, hfalse, Or.inl ⟨hs, hnot, hpartner⟩⟩
  have hright : ∀ t ∈ B, S t.2 → ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x t.1 = true →
      PEqualNP.BlindGate.wireValue D n x c = true → F x = true := by
    intro t ht hs x hpartner hC
    by_contra hF
    have hfalse : F x = false := by simpa only [Bool.not_eq_true] using hF
    have hnot : ¬ S t.1 := fun h => hdisjoint t ht ⟨h, hs⟩
    exact hn ⟨t, ht, x, hC, hfalse, Or.inr ⟨hs, hnot, hpartner⟩⟩
  obtain ⟨E, T, hET, hcost⟩ := erase_mixed_frontier_dominating n F D B j c S
    hres hj hc hS hdom hdisjoint hleft hright
  have := hmin E T hET
  omega

end GlobalOrFrontier

namespace GlobalOrFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

lemma descendants_forward_closure (n : ℕ) (D : Circuit) (j : ℕ)
    (hD : IsAO2 n D) : IsForwardClosure n D j (descendants n D j) := by
  refine ⟨?_, Relation.ReflTransGen.refl, ?_⟩
  · intro w hw hreach
    have := descendants_le n D j w hD hreach
    omega
  · intro k hk hkj
    exact descendants_gate n D j k hk hkj

end GlobalOrFrontier

namespace GlobalOrFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover
open ProductFactor

lemma wire_true_mono (n : ℕ) (D : Circuit) (hD : IsAO2 n D)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    ∀ w < n + D.size, PEqualNP.BlindGate.wireValue D n x w = true →
      PEqualNP.BlindGate.wireValue D n y w = true := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hx
    by_cases hin : w < n
    · rw [SplitAux.wireValue_input n D x w hin] at hx
      rw [SplitAux.wireValue_input n D y w hin]
      exact hxy ⟨w, hin⟩ hx
    · let k := w - n
      have hwk : w = n + k := by dsimp [k]; omega
      have hk : k < D.size := by omega
      rw [hwk, SplitAux.wireValue_gate n D x k hk hD.2.1] at hx
      rw [hwk, SplitAux.wireValue_gate n D y k hk hD.2.1]
      have hop : (gateAt D k).op = GateOp.and ∨ (gateAt D k).op = GateOp.or := by
        apply hD.1
        rw [SplitAux.gateAt_eq_getElem D k hk]
        exact List.getElem_mem hk
      apply LiftAux.gateOp_eval_mono _ hop _ _ _ ?_ hx
      intro u hu huval
      have hub := hD.2.1 k hk u hu
      exact ih u (by omega) (by omega) huval

lemma frontier_context_forces_output (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (j : ℕ) (S : ℕ → Prop)
    (hres : IsResidual n F D B) (hS : IsOrFrontier n D j S)
    (t : ℕ × ℕ) (ht : t ∈ B) (x : Fin n → Bool)
    (hcontext : (S t.1 ∧ PEqualNP.BlindGate.wireValue D n x t.2 = true) ∨
      (S t.2 ∧ PEqualNP.BlindGate.wireValue D n x t.1 = true))
    (hJ : PEqualNP.BlindGate.wireValue D n x (n + j) = true) : F x = true := by
  rcases hcontext with ⟨hs, hp⟩ | ⟨hs, hp⟩
  · exact (hres.2.2.2 x).mpr ⟨t, ht,
      frontier_dominates n D j S hres.1 hS t.1 (hres.2.1 t ht).1 hs x hJ, hp⟩
  · exact (hres.2.2.2 x).mpr ⟨t, ht, hp,
      frontier_dominates n D j S hres.1 hS t.2 (hres.2.1 t ht).2 hs x hJ⟩

lemma minimum_frontier_false_join_triple (n : ℕ)
    (F : (Fin n → Bool) → Bool) (D : Circuit) (B : List (ℕ × ℕ))
    (j A C : ℕ) (S : ℕ → Prop) (hres : IsResidual n F D B) (hj : j < D.size)
    (hgate : gateAt D j = ⟨GateOp.and, [A, C]⟩) (hS : IsOrFrontier n D j S)
    (hmin : ∀ (E : Circuit) (T : List (ℕ × ℕ)), IsResidual n F E T →
      D.size + 2 * B.length ≤ E.size + 2 * T.length) :
    ∃ x y z : Fin n → Bool,
      F x = false ∧ F y = false ∧ F z = false ∧
      PEqualNP.BlindGate.wireValue D n x A = true ∧
      PEqualNP.BlindGate.wireValue D n x C = false ∧
      PEqualNP.BlindGate.wireValue D n y A = false ∧
      PEqualNP.BlindGate.wireValue D n y C = true ∧
      PEqualNP.BlindGate.wireValue D n z (n + j) = true ∧
      F (fun i => x i || y i) = true ∧
      F (fun i => x i || z i) = true ∧
      F (fun i => y i || z i) = true := by
  obtain ⟨t, ht, x, hAx, hCx, hFx, hctx⟩ :=
    minimum_frontier_and_children_have_separating_inputs n F D B j A C S hres hj hgate hS
      hmin A C (Or.inl ⟨rfl, rfl⟩)
  obtain ⟨u, hu, y, hCy, hAy, hFy, hcty⟩ :=
    minimum_frontier_and_children_have_separating_inputs n F D B j A C S hres hj hgate hS
      hmin C A (Or.inr ⟨rfl, rfl⟩)
  obtain ⟨z, hJz, hFz⟩ := hres.2.2.1 (n + j) (by omega)
  have hAb : A < n + D.size := by
    have := hres.1.2.1 j hj A (by rw [hgate]; simp)
    omega
  have hCb : C < n + D.size := by
    have := hres.1.2.1 j hj C (by rw [hgate]; simp)
    omega
  have hleft (a b : Fin n → Bool) (w : ℕ) (hw : w < n + D.size)
      (hv : PEqualNP.BlindGate.wireValue D n a w = true) :
      PEqualNP.BlindGate.wireValue D n (fun i => a i || b i) w = true :=
    wire_true_mono n D hres.1 a (fun i => a i || b i)
      (by intro i hi; rw [hi]; rfl) w hw hv
  have hright (a b : Fin n → Bool) (w : ℕ) (hw : w < n + D.size)
      (hv : PEqualNP.BlindGate.wireValue D n b w = true) :
      PEqualNP.BlindGate.wireValue D n (fun i => a i || b i) w = true :=
    wire_true_mono n D hres.1 b (fun i => a i || b i)
      (by intro i hi; rw [hi]; exact Bool.or_true _) w hw hv
  have hcontextUp (v : ℕ × ℕ) (hv : v ∈ B) (a b : Fin n → Bool)
      (h : (S v.1 ∧ ¬ S v.2 ∧ PEqualNP.BlindGate.wireValue D n a v.2 = true) ∨
        (S v.2 ∧ ¬ S v.1 ∧ PEqualNP.BlindGate.wireValue D n a v.1 = true)) :
      (S v.1 ∧ PEqualNP.BlindGate.wireValue D n (fun i => a i || b i) v.2 = true) ∨
        (S v.2 ∧ PEqualNP.BlindGate.wireValue D n (fun i => a i || b i) v.1 = true) := by
    rcases h with h | h
    · exact Or.inl ⟨h.1, hleft a b v.2 (hres.2.1 v hv).2 h.2.2⟩
    · exact Or.inr ⟨h.1, hleft a b v.1 (hres.2.1 v hv).1 h.2.2⟩
  have hJxy : PEqualNP.BlindGate.wireValue D n (fun i => x i || y i) (n + j) = true := by
    rw [SplitAux.wireValue_gate n D _ j hj hres.1.2.1, hgate]
    simp [GateOp.eval, hleft x y A hAb hAx, hright x y C hCb hCy]
  refine ⟨x, y, z, hFx, hFy, hFz, hAx, hCx, hAy, hCy, hJz, ?_, ?_, ?_⟩
  · exact frontier_context_forces_output n F D B j S hres hS t ht _
      (hcontextUp t ht x y hctx) hJxy
  · exact frontier_context_forces_output n F D B j S hres hS t ht _
      (hcontextUp t ht x z hctx) (hright x z (n + j) (by omega) hJz)
  · exact frontier_context_forces_output n F D B j S hres hS u hu _
      (hcontextUp u hu y z hcty) (hright y z (n + j) (by omega) hJz)

end GlobalOrFrontier

namespace GlobalOrFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover
open ProductFactor

lemma true_wire_has_or_trace_atom (n : ℕ) (D : Circuit) (hD : IsAO2 n D)
    (x : Fin n → Bool) :
    ∀ w < n + D.size, PEqualNP.BlindGate.wireValue D n x w = true →
      ∃ r ≤ w, PEqualNP.BlindGate.wireValue D n x r = true ∧
        (r < n ∨ ∃ k < D.size, r = n + k ∧ (gateAt D k).op = GateOp.and) ∧
        ∀ y : Fin n → Bool, PEqualNP.BlindGate.wireValue D n y r = true →
          PEqualNP.BlindGate.wireValue D n y w = true := by
  intro w
  induction w using Nat.strongRecOn with
  | ind w ih =>
    intro hw hx
    by_cases hin : w < n
    · exact ⟨w, Nat.le_refl _, hx, Or.inl hin, fun _ h => h⟩
    · let k := w - n
      have hwk : w = n + k := by dsimp [k]; omega
      have hk : k < D.size := by omega
      have hop : (gateAt D k).op = GateOp.and ∨ (gateAt D k).op = GateOp.or := by
        apply hD.1
        rw [SplitAux.gateAt_eq_getElem D k hk]
        exact List.getElem_mem hk
      rcases hop with hand | hor
      · exact ⟨w, Nat.le_refl _, hx, Or.inr ⟨k, hk, hwk, hand⟩, fun _ h => h⟩
      · have hvalue (y : Fin n → Bool) : PEqualNP.BlindGate.wireValue D n y w = true ↔
            ∃ u ∈ (gateAt D k).inputs, PEqualNP.BlindGate.wireValue D n y u = true := by
          rw [hwk, SplitAux.wireValue_gate n D y k hk hD.2.1, hor]
          simp [GateOp.eval]
        obtain ⟨u, hu, hux⟩ := (hvalue x).mp hx
        have hub := hD.2.1 k hk u hu
        obtain ⟨r, hru, hrx, hatom, hdom⟩ := ih u (by omega) (by omega) hux
        exact ⟨r, by omega, hrx, hatom, fun y hy => (hvalue y).mpr ⟨u, hu, hdom y hy⟩⟩

lemma separating_context_has_atomic_guard (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (j c : ℕ) (S : ℕ → Prop)
    (hres : IsResidual n F D B) (hS : IsOrFrontier n D j S)
    (t : ℕ × ℕ) (ht : t ∈ B) (x : Fin n → Bool)
    (hc : PEqualNP.BlindGate.wireValue D n x c = true) (hF : F x = false)
    (hcontext : (S t.1 ∧ PEqualNP.BlindGate.wireValue D n x t.2 = true) ∨
      (S t.2 ∧ PEqualNP.BlindGate.wireValue D n x t.1 = true)) :
    ∃ r < n + D.size, PEqualNP.BlindGate.wireValue D n x r = true ∧
      (r < n ∨ ∃ k < D.size, r = n + k ∧ (gateAt D k).op = GateOp.and) ∧
      (∀ y : Fin n → Bool, PEqualNP.BlindGate.wireValue D n y (n + j) = true →
        PEqualNP.BlindGate.wireValue D n y r = true → F y = true) ∧
      ¬ (∀ y : Fin n → Bool, PEqualNP.BlindGate.wireValue D n y c = true →
        PEqualNP.BlindGate.wireValue D n y r = true → F y = true) := by
  have build (q : ℕ) (hq : q < n + D.size)
      (hqx : PEqualNP.BlindGate.wireValue D n x q = true)
      (hqsafe : ∀ y : Fin n → Bool, PEqualNP.BlindGate.wireValue D n y (n + j) = true →
        PEqualNP.BlindGate.wireValue D n y q = true → F y = true) :
      ∃ r < n + D.size, PEqualNP.BlindGate.wireValue D n x r = true ∧
        (r < n ∨ ∃ k < D.size, r = n + k ∧ (gateAt D k).op = GateOp.and) ∧
        (∀ y : Fin n → Bool, PEqualNP.BlindGate.wireValue D n y (n + j) = true →
          PEqualNP.BlindGate.wireValue D n y r = true → F y = true) ∧
        ¬ (∀ y : Fin n → Bool, PEqualNP.BlindGate.wireValue D n y c = true →
          PEqualNP.BlindGate.wireValue D n y r = true → F y = true) := by
    obtain ⟨r, hrq, hrx, hatom, hdom⟩ := true_wire_has_or_trace_atom n D hres.1 x q hq hqx
    refine ⟨r, by omega, hrx, hatom, ?_, ?_⟩
    · intro y hJ hr
      exact hqsafe y hJ (hdom y hr)
    · intro hall
      have := hall x hc hrx
      rw [hF] at this
      cases this
  rcases hcontext with ⟨hs, hp⟩ | ⟨hs, hp⟩
  · apply build t.2 (hres.2.1 t ht).2 hp
    intro y hJ hq
    exact (hres.2.2.2 y).mpr ⟨t, ht,
      frontier_dominates n D j S hres.1 hS t.1 (hres.2.1 t ht).1 hs y hJ, hq⟩
  · apply build t.1 (hres.2.1 t ht).1 hp
    intro y hJ hq
    exact (hres.2.2.2 y).mpr ⟨t, ht, hq,
      frontier_dominates n D j S hres.1 hS t.2 (hres.2.1 t ht).2 hs y hJ⟩

lemma last_and_atomic_guard_is_earlier (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (j r : ℕ)
    (hlast : ∀ k < D.size, j < k → (gateAt D k).op = GateOp.or)
    (hdirty : ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x (n + j) = true ∧ F x = false)
    (hatom : r < n ∨ ∃ k < D.size, r = n + k ∧ (gateAt D k).op = GateOp.and)
    (hsafe : ∀ y : Fin n → Bool, PEqualNP.BlindGate.wireValue D n y (n + j) = true →
      PEqualNP.BlindGate.wireValue D n y r = true → F y = true) :
    r < n ∨ ∃ k < j, r = n + k ∧ (gateAt D k).op = GateOp.and := by
  rcases hatom with hin | ⟨k, hk, rfl, hand⟩
  · exact Or.inl hin
  · have hkle : k ≤ j := by
      by_contra hnot
      have hor := hlast k hk (by omega)
      rw [hand] at hor
      cases hor
    have hne : k ≠ j := by
      intro heq
      subst k
      obtain ⟨x, hJ, hF⟩ := hdirty
      have := hsafe x hJ hJ
      rw [hF] at this
      cases this
    exact Or.inr ⟨k, by omega, rfl, hand⟩

lemma minimum_last_and_has_earlier_atomic_guards (n : ℕ)
    (F : (Fin n → Bool) → Bool) (D : Circuit) (B : List (ℕ × ℕ))
    (j A C : ℕ) (hres : IsResidual n F D B) (hj : j < D.size)
    (hgate : gateAt D j = ⟨GateOp.and, [A, C]⟩)
    (hlast : ∀ k < D.size, j < k → (gateAt D k).op = GateOp.or)
    (hmin : ∀ (E : Circuit) (T : List (ℕ × ℕ)), IsResidual n F E T →
      D.size + 2 * B.length ≤ E.size + 2 * T.length) :
    ∀ keep drop : ℕ, (keep = A ∧ drop = C) ∨ (keep = C ∧ drop = A) →
      ∃ (x : Fin n → Bool) (r : ℕ), r < n + D.size ∧
        PEqualNP.BlindGate.wireValue D n x keep = true ∧ F x = false ∧
        PEqualNP.BlindGate.wireValue D n x r = true ∧
        (r < n ∨ ∃ k < j, r = n + k ∧ (gateAt D k).op = GateOp.and) ∧
        (∀ y : Fin n → Bool, PEqualNP.BlindGate.wireValue D n y (n + j) = true →
          PEqualNP.BlindGate.wireValue D n y r = true → F y = true) ∧
        ¬ (∀ y : Fin n → Bool, PEqualNP.BlindGate.wireValue D n y keep = true →
          PEqualNP.BlindGate.wireValue D n y r = true → F y = true) := by
  intro keep drop hwhich
  let S := descendants n D j
  have hS : IsOrFrontier n D j S := last_and_descendants_frontier n D j hres.1 hlast
  obtain ⟨t, ht, x, hkeep, _, hF, hctx⟩ :=
    minimum_frontier_and_children_have_separating_inputs n F D B j A C S hres hj hgate hS
      hmin keep drop hwhich
  have hcontext : (S t.1 ∧ PEqualNP.BlindGate.wireValue D n x t.2 = true) ∨
      (S t.2 ∧ PEqualNP.BlindGate.wireValue D n x t.1 = true) := by
    rcases hctx with h | h
    · exact Or.inl ⟨h.1, h.2.2⟩
    · exact Or.inr ⟨h.1, h.2.2⟩
  obtain ⟨r, hr, hrx, hatom, hsafe, hunsafe⟩ :=
    separating_context_has_atomic_guard n F D B j keep S hres hS t ht x hkeep hF hcontext
  have hdirty := hres.2.2.1 (n + j) (by omega)
  exact ⟨x, r, hr, hkeep, hF, hrx,
    last_and_atomic_guard_is_earlier n F D j r hlast hdirty hatom hsafe, hsafe, hunsafe⟩

end GlobalOrFrontier


namespace ZeroPrune

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover
open ProductFactor LastAndFactor

def WireSound (n : ℕ) (D E : Circuit) (j w : ℕ) (r : Option ℕ) : Prop :=
  match r with
  | none => ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x (n + j) = false →
      PEqualNP.BlindGate.wireValue D n x w = false
  | some v => v < n + E.size ∧
      (∀ x : Fin n → Bool, PEqualNP.BlindGate.wireValue E n x v = true →
        PEqualNP.BlindGate.wireValue D n x w = true) ∧
      (∀ x : Fin n → Bool, PEqualNP.BlindGate.wireValue D n x (n + j) = false →
        PEqualNP.BlindGate.wireValue E n x v = PEqualNP.BlindGate.wireValue D n x w)

def MapSound (n : ℕ) (D E : Circuit) (j : ℕ) (f : ℕ → Option ℕ) (m : ℕ) : Prop :=
  ∀ w < m, WireSound n D E j w (f w)

lemma wireSound_transport (n : ℕ) (D E E' : Circuit) (j w : ℕ) (r : Option ℕ)
    (h : WireSound n D E j w r) (hle : E.size ≤ E'.size)
    (heq : ∀ v < n + E.size, ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E' n x v = PEqualNP.BlindGate.wireValue E n x v) :
    WireSound n D E' j w r := by
  cases r with
  | none => exact h
  | some v =>
    refine ⟨by have := h.1; omega, ?_, ?_⟩
    · intro x hx
      exact h.2.1 x (by rwa [heq v h.1 x] at hx)
    · intro x hx
      exact (heq v h.1 x).trans (h.2.2 x hx)

lemma mapSound_extend (n : ℕ) (D E : Circuit) (j : ℕ) (f : ℕ → Option ℕ)
    (m : ℕ) (r : Option ℕ) (h : MapSound n D E j f m)
    (hr : WireSound n D E j m r) :
    MapSound n D E j (Function.update f m r) (m + 1) := by
  intro w hw
  by_cases hwm : w = m
  · subst w
    simpa only [Function.update_self] using hr
  · rw [Function.update_of_ne hwm]
    exact h w (by omega)

lemma build_or_step (n : ℕ) (D E : Circuit) (j w u v : ℕ) (ru rv : Option ℕ)
    (F : (Fin n → Bool) → Bool) (hE : IsAO2 n E)
    (hnot : ∀ z < n + E.size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E n x z = true ∧ F x = false)
    (hu : WireSound n D E j u ru) (hv : WireSound n D E j v rv)
    (hval : ∀ x : Fin n → Bool, PEqualNP.BlindGate.wireValue D n x w =
      (PEqualNP.BlindGate.wireValue D n x u || PEqualNP.BlindGate.wireValue D n x v)) :
    ∃ (E' : Circuit) (r : Option ℕ), IsAO2 n E' ∧
      (∀ z < n + E'.size, ∃ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue E' n x z = true ∧ F x = false) ∧
      E.size ≤ E'.size ∧ E'.size ≤ E.size + 1 ∧
      (∀ z < n + E.size, ∀ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue E' n x z = PEqualNP.BlindGate.wireValue E n x z) ∧
      WireSound n D E' j w r := by
  cases ru with
  | none =>
    cases rv with
    | none =>
      refine ⟨E, none, hE, hnot, le_rfl, by omega, fun _ _ _ => rfl, ?_⟩
      intro x hx
      rw [hval x, hu x hx, hv x hx]
      rfl
    | some q =>
      refine ⟨E, some q, hE, hnot, le_rfl, by omega, fun _ _ _ => rfl,
        hv.1, ?_, ?_⟩
      · intro x hx
        rw [hval x, hv.2.1 x hx, Bool.or_true]
      · intro x hx
        rw [hval x, hu x hx, Bool.false_or]
        exact hv.2.2 x hx
  | some p =>
    cases rv with
    | none =>
      refine ⟨E, some p, hE, hnot, le_rfl, by omega, fun _ _ _ => rfl,
        hu.1, ?_, ?_⟩
      · intro x hx
        rw [hval x, hu.2.1 x hx]
        rfl
      · intro x hx
        rw [hval x, hv x hx, Bool.or_false]
        exact hu.2.2 x hx
    | some q =>
      refine ⟨appendOr E p q, some (n + E.size), appendOr_ao2 n E p q hE hu.1 hv.1,
        appendOr_all_nonbelow n E p q F hE hu.1 hv.1 hnot, ?_, ?_,
        fun z hz x => old_wire_appendOr n E p q z hz x, ?_⟩
      · rw [appendOr_size]; omega
      · rw [appendOr_size]
      · refine ⟨by rw [appendOr_size]; omega, ?_, ?_⟩
        · intro x hx
          rw [new_wire_appendOr n E p q hE hu.1 hv.1 x, Bool.or_eq_true] at hx
          rw [hval x, Bool.or_eq_true]
          rcases hx with hx | hx
          · exact Or.inl (hu.2.1 x hx)
          · exact Or.inr (hv.2.1 x hx)
        · intro x hx
          rw [new_wire_appendOr n E p q hE hu.1 hv.1 x, hu.2.2 x hx, hv.2.2 x hx, hval x]


def circuitPrefix (D : Circuit) (j : ℕ) : Circuit :=
  ⟨D.gates.take j, D.output⟩

lemma prefix_size (D : Circuit) (j : ℕ) (hj : j ≤ D.size) :
    (circuitPrefix D j).size = j := by
  simp only [circuitPrefix, Circuit.size, List.length_take]
  exact Nat.min_eq_left hj

lemma prefix_isAO2 (n : ℕ) (D : Circuit) (j : ℕ) (hD : IsAO2 n D) :
    IsAO2 n (circuitPrefix D j) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    exact hD.1 g (List.mem_of_mem_take hg)
  · intro k hk u hu
    have hkD : k < D.gates.length := by
      have : k < min j D.gates.length := by
        simpa only [circuitPrefix, List.length_take] using hk
      omega
    rw [LiftAux.gateAt_eq_getElem (circuitPrefix D j) k hk] at hu
    have heq : (circuitPrefix D j).gates[k] = D.gates[k] := by
      exact List.getElem_take
    rw [heq] at hu
    apply hD.2.1 k hkD u
    rwa [LiftAux.gateAt_eq_getElem D k hkD]
  · intro g hg
    exact hD.2.2 g (List.mem_of_mem_take hg)

lemma prefix_wire (n : ℕ) (D : Circuit) (j : ℕ) (hj : j ≤ D.size)
    (x : Fin n → Bool) (w : ℕ) (hw : w < n + j) :
    PEqualNP.BlindGate.wireValue (circuitPrefix D j) n x w =
      PEqualNP.BlindGate.wireValue D n x w := by
  unfold PEqualNP.BlindGate.wireValue Circuit.wires
  change (LiftAux.evalGates (D.gates.take j) (List.ofFn x)).getD w false =
    (LiftAux.evalGates D.gates (List.ofFn x)).getD w false
  have hlen : (LiftAux.evalGates (D.gates.take j) (List.ofFn x)).length = n + j := by
    rw [LiftAux.evalGates_length, List.length_ofFn, List.length_take]
    have h : min j D.gates.length = j := Nat.min_eq_left hj
    rw [h]
  conv_rhs => rw [← List.take_append_drop j D.gates, LiftAux.evalGates_append]
  exact (LiftAux.evalGates_getD_lt (D.gates.drop j)
    (LiftAux.evalGates (D.gates.take j) (List.ofFn x)) w (by omega)).symm

lemma prefix_base (n : ℕ) (F : (Fin n → Bool) → Bool) (D : Circuit) (j : ℕ)
    (hD : IsAO2 n D) (hj : j < D.size)
    (hnot : ∀ w < n + D.size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x w = true ∧ F x = false) :
    ∃ (E : Circuit) (f : ℕ → Option ℕ), IsAO2 n E ∧
      (∀ z < n + E.size, ∃ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue E n x z = true ∧ F x = false) ∧
      E.size + 1 ≤ j + 1 ∧ MapSound n D E j f (n + j + 1) := by
  have hsize := prefix_size D j (by omega)
  refine ⟨circuitPrefix D j, (fun w => if w = n + j then none else some w),
    prefix_isAO2 n D j hD, ?_, by omega, ?_⟩
  · intro w hw
    rcases hnot w (by omega) with ⟨x, hx, hF⟩
    refine ⟨x, ?_, hF⟩
    rw [prefix_wire n D j (by omega) x w (by omega)]
    exact hx
  · intro w hw
    by_cases hweq : w = n + j
    · subst w
      simp only [WireSound]
      intro x hx
      exact hx
    · simp only [hweq, ite_false, WireSound]
      have hwj : w < n + j := by omega
      refine ⟨by omega, ?_, ?_⟩
      · intro x hx
        rwa [prefix_wire n D j (by omega) x w hwj] at hx
      · intro x _
        exact prefix_wire n D j (by omega) x w hwj

end ZeroPrune

namespace ZeroPrune

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover
open ProductFactor LastAndFactor

lemma zero_prune_or_suffix_map (n : ℕ) (D : Circuit) (j : ℕ)
    (F : (Fin n → Bool) → Bool) (hD : IsAO2 n D) (hj : j < D.size)
    (hnot : ∀ w < n + D.size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x w = true ∧ F x = false)
    (hOR : ∀ k < D.size, j < k → (gateAt D k).op = GateOp.or) :
    ∃ (E : Circuit) (f : ℕ → Option ℕ), IsAO2 n E ∧
      (∀ w < n + E.size, ∃ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue E n x w = true ∧ F x = false) ∧
      E.size + 1 ≤ D.size ∧ MapSound n D E j f (n + D.size) := by
  have hbuild : ∀ k : ℕ, j < k → k ≤ D.size →
      ∃ (E : Circuit) (f : ℕ → Option ℕ), IsAO2 n E ∧
        (∀ w < n + E.size, ∃ x : Fin n → Bool,
          PEqualNP.BlindGate.wireValue E n x w = true ∧ F x = false) ∧
        E.size + 1 ≤ k ∧ MapSound n D E j f (n + k) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hjk hk
      by_cases hbase : k = j + 1
      · subst k
        simpa only [Nat.add_assoc] using prefix_base n F D j hD hj hnot
      · have hjprev : j < k - 1 := by omega
        have hprev : k - 1 < k := by omega
        have hkprev : k - 1 < D.size := by omega
        obtain ⟨E, f, hE, hnotE, hsize, hmap⟩ := ih (k - 1) hprev hjprev (by omega)
        obtain ⟨u, v, hin, hu, hv⟩ := SplitAux.gate_inputs_two n D hD (k - 1) hkprev
        have hval : ∀ x : Fin n → Bool,
            PEqualNP.BlindGate.wireValue D n x (n + (k - 1)) =
              (PEqualNP.BlindGate.wireValue D n x u || PEqualNP.BlindGate.wireValue D n x v) :=
          SplitAux.wireValue_or_pair n D hD.2.1 (k - 1) u v hkprev
            (hOR (k - 1) hkprev hjprev) hin
        obtain ⟨E', r, hE', hnotE', hle, hupper, heq, hr⟩ :=
          build_or_step n D E j (n + (k - 1)) u v (f u) (f v) F hE hnotE
            (hmap u hu) (hmap v hv) hval
        have hmap' : MapSound n D E' j f (n + (k - 1)) := by
          intro w hw
          exact wireSound_transport n D E E' j w (f w) (hmap w hw) hle heq
        have hext := mapSound_extend n D E' j f (n + (k - 1)) r hmap' hr
        have hnum : n + (k - 1) + 1 = n + k := by omega
        refine ⟨E', Function.update f (n + (k - 1)) r, hE', hnotE', by omega, ?_⟩
        rwa [hnum] at hext
  exact hbuild D.size hj le_rfl

def mapPair (f : ℕ → Option ℕ) (t : ℕ × ℕ) : Option (ℕ × ℕ) :=
  match f t.1, f t.2 with
  | some u, some v => some (u, v)
  | _, _ => none

def mapProducts (f : ℕ → Option ℕ) (B : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  B.filterMap (mapPair f)

lemma mem_mapProducts (f : ℕ → Option ℕ) (B : List (ℕ × ℕ)) (t : ℕ × ℕ) :
    t ∈ mapProducts f B ↔ ∃ s ∈ B, ∃ u v,
      f s.1 = some u ∧ f s.2 = some v ∧ t = (u, v) := by
  rw [mapProducts, List.mem_filterMap]
  constructor
  · rintro ⟨s, hs, hval⟩
    cases hu : f s.1 with
    | none => simp [mapPair, hu] at hval
    | some u =>
      cases hv : f s.2 with
      | none => simp [mapPair, hu, hv] at hval
      | some v =>
        have heq : (u, v) = t := by simpa [mapPair, hu, hv] using hval
        exact ⟨s, hs, u, v, hu, hv, heq.symm⟩
  · rintro ⟨s, hs, u, v, hu, hv, rfl⟩
    exact ⟨s, hs, by simp [mapPair, hu, hv]⟩

lemma mapProducts_length_le (f : ℕ → Option ℕ) (B : List (ℕ × ℕ)) :
    (mapProducts f B).length ≤ B.length := by
  exact List.length_filterMap_le _ _

lemma mapProducts_bound (n : ℕ) (D E : Circuit) (j : ℕ) (f : ℕ → Option ℕ)
    (B : List (ℕ × ℕ)) (hmap : MapSound n D E j f (n + D.size))
    (hbound : ∀ t ∈ B, t.1 < n + D.size ∧ t.2 < n + D.size) :
    ∀ t ∈ mapProducts f B, t.1 < n + E.size ∧ t.2 < n + E.size := by
  intro t ht
  obtain ⟨s, hs, u, v, hu, hv, rfl⟩ := (mem_mapProducts f B t).mp ht
  have hsu := hmap s.1 (hbound s hs).1
  have hsv := hmap s.2 (hbound s hs).2
  rw [hu] at hsu
  rw [hv] at hsv
  exact ⟨hsu.1, hsv.1⟩

lemma mapProducts_sound (n : ℕ) (D E : Circuit) (j : ℕ) (f : ℕ → Option ℕ)
    (B : List (ℕ × ℕ)) (hmap : MapSound n D E j f (n + D.size))
    (hbound : ∀ t ∈ B, t.1 < n + D.size ∧ t.2 < n + D.size) :
    ∀ x : Fin n → Bool, products n E (mapProducts f B) x → products n D B x := by
  intro x hnew
  obtain ⟨t, ht, h1, h2⟩ := hnew
  obtain ⟨s, hs, u, v, hu, hv, rfl⟩ := (mem_mapProducts f B t).mp ht
  have hsu := hmap s.1 (hbound s hs).1
  have hsv := hmap s.2 (hbound s hs).2
  rw [hu] at hsu
  rw [hv] at hsv
  exact ⟨s, hs, hsu.2.1 x h1, hsv.2.1 x h2⟩

lemma mapProducts_complete_when_zero (n : ℕ) (D E : Circuit) (j : ℕ)
    (f : ℕ → Option ℕ) (B : List (ℕ × ℕ))
    (hmap : MapSound n D E j f (n + D.size))
    (hbound : ∀ t ∈ B, t.1 < n + D.size ∧ t.2 < n + D.size)
    (x : Fin n → Bool) (hzero : PEqualNP.BlindGate.wireValue D n x (n + j) = false) :
    products n D B x → products n E (mapProducts f B) x := by
  rintro ⟨t, ht, h1, h2⟩
  have htu := hmap t.1 (hbound t ht).1
  have htv := hmap t.2 (hbound t ht).2
  cases hu : f t.1 with
  | none =>
    rw [hu] at htu
    have := htu x hzero
    rw [this] at h1
    cases h1
  | some u =>
    cases hv : f t.2 with
    | none =>
      rw [hv] at htv
      have := htv x hzero
      rw [this] at h2
      cases h2
    | some v =>
      rw [hu] at htu
      rw [hv] at htv
      refine ⟨(u, v), (mem_mapProducts f B (u, v)).mpr ⟨t, ht, u, v, hu, hv, rfl⟩, ?_, ?_⟩
      · exact (htu.2.2 x hzero).trans h1
      · exact (htv.2.2 x hzero).trans h2

lemma zero_prune_last_and_residual (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (j : ℕ)
    (hres : IsResidual n F D B) (hj : j < D.size)
    (hOR : ∀ k < D.size, j < k → (gateAt D k).op = GateOp.or) :
    ∃ (E : Circuit) (T : List (ℕ × ℕ)), IsAO2 n E ∧
      (∀ t ∈ T, t.1 < n + E.size ∧ t.2 < n + E.size) ∧
      (∀ w < n + E.size, ∃ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue E n x w = true ∧ F x = false) ∧
      E.size + 2 * T.length + 1 ≤ D.size + 2 * B.length ∧
      (∀ x : Fin n → Bool, products n E T x → F x = true) ∧
      (∀ x : Fin n → Bool, PEqualNP.BlindGate.wireValue D n x (n + j) = false →
        F x = true → products n E T x) := by
  obtain ⟨E, f, hE, hnot, hsize, hmap⟩ :=
    zero_prune_or_suffix_map n D j F hres.1 hj hres.2.2.1 hOR
  refine ⟨E, mapProducts f B, hE, mapProducts_bound n D E j f B hmap hres.2.1,
    hnot, ?_, ?_, ?_⟩
  · have := mapProducts_length_le f B
    omega
  · intro x hx
    exact (hres.2.2.2 x).mpr (mapProducts_sound n D E j f B hmap hres.2.1 x hx)
  · intro x hzero hF
    exact mapProducts_complete_when_zero n D E j f B hmap hres.2.1 x hzero
      ((hres.2.2.2 x).mp hF)

end ZeroPrune

namespace GlobalOrFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover
open ProductFactor

lemma minimum_residual_essential_basis {α : Type*} (n : ℕ)
    (F : (Fin n → Bool) → Bool) (D : Circuit) (B : List (ℕ × ℕ)) (j : ℕ)
    (hmin : ∀ (E : Circuit) (T : List (ℕ × ℕ)), IsResidual n F E T →
      D.size + 2 * B.length ≤ E.size + 2 * T.length)
    (E : Circuit) (T : List (ℕ × ℕ)) (hE : IsAO2 n E)
    (hvalid : ∀ t ∈ T, t.1 < n + E.size ∧ t.2 < n + E.size)
    (hnonbelow : ∀ w < n + E.size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E n x w = true ∧ F x = false)
    (hcost : E.size + 2 * T.length < D.size + 2 * B.length)
    (hsound : ∀ x : Fin n → Bool,
      (∃ t ∈ T, PEqualNP.BlindGate.wireValue E n x t.1 = true ∧
        PEqualNP.BlindGate.wireValue E n x t.2 = true) → F x = true)
    (hagree : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x (n + j) = false → F x = true →
      ∃ t ∈ T, PEqualNP.BlindGate.wireValue E n x t.1 = true ∧
        PEqualNP.BlindGate.wireValue E n x t.2 = true)
    (basis : α → Fin n → Bool) (hpositive : ∀ a, F (basis a) = true)
    (hcover : ∀ x : Fin n → Bool, F x = true →
      ∃ a, ∀ i, basis a i = true → x i = true) :
    ∃ a, PEqualNP.BlindGate.wireValue D n (basis a) (n + j) = true ∧
      ¬ (∃ t ∈ T, PEqualNP.BlindGate.wireValue E n (basis a) t.1 = true ∧
        PEqualNP.BlindGate.wireValue E n (basis a) t.2 = true) := by
  classical
  by_contra hn
  have hall (a : α) : ∃ t ∈ T,
      PEqualNP.BlindGate.wireValue E n (basis a) t.1 = true ∧
      PEqualNP.BlindGate.wireValue E n (basis a) t.2 = true := by
    by_contra hbad
    have hJ : PEqualNP.BlindGate.wireValue D n (basis a) (n + j) = true := by
      cases hv : PEqualNP.BlindGate.wireValue D n (basis a) (n + j) with
      | false => exact False.elim (hbad (hagree (basis a) hv (hpositive a)))
      | true => rfl
    exact hn ⟨a, hJ, hbad⟩
  have hres : IsResidual n F E T := by
    refine ⟨hE, hvalid, hnonbelow, ?_⟩
    intro x
    constructor
    · intro hFx
      obtain ⟨a, hax⟩ := hcover x hFx
      obtain ⟨t, ht, h1, h2⟩ := hall a
      exact ⟨t, ht,
        wire_true_mono n E hE (basis a) x hax t.1 (hvalid t ht).1 h1,
        wire_true_mono n E hE (basis a) x hax t.2 (hvalid t ht).2 h2⟩
    · exact hsound x
  have := hmin E T hres
  omega

def edgeAssignment {n : ℕ} (a b : Fin n) : Fin n → Bool :=
  fun i => decide (i = a ∨ i = b)

lemma graph_edge_assignment_true {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (a b : Fin n) (hab : G.Adj a b) : graphFun G ∅ (edgeAssignment a b) = true := by
  have h : ∃ u v, G.Adj u v ∧ edgeAssignment a b u = true ∧
      edgeAssignment a b v = true :=
    ⟨a, b, hab, by simp [edgeAssignment], by simp [edgeAssignment]⟩
  simpa [graphFun] using h

lemma graph_positive_contains_edge_assignment {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (x : Fin n → Bool) (hx : graphFun G ∅ x = true) :
    ∃ a b : Fin n, G.Adj a b ∧ ∀ i, edgeAssignment a b i = true → x i = true := by
  have h : ∃ a b, G.Adj a b ∧ x a = true ∧ x b = true := by simpa [graphFun] using hx
  obtain ⟨a, b, hab, ha, hb⟩ := h
  refine ⟨a, b, hab, ?_⟩
  intro i hi
  have heq : i = a ∨ i = b := by simpa only [edgeAssignment, decide_eq_true_eq] using hi
  rcases heq with rfl | rfl
  · exact ha
  · exact hb

end GlobalOrFrontier

namespace GlobalOrFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover
open ProductFactor LastAndFactor

lemma minimum_last_gate_has_essential_graph_edge (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (D : Circuit) (B : List (ℕ × ℕ)) (j : ℕ)
    (hres : IsResidual n (graphFun G ∅) D B) (hj : j < D.size)
    (hOR : ∀ k < D.size, j < k → (gateAt D k).op = GateOp.or)
    (hmin : ∀ (E : Circuit) (T : List (ℕ × ℕ)), IsResidual n (graphFun G ∅) E T →
      D.size + 2 * B.length ≤ E.size + 2 * T.length) :
    ∃ (E : Circuit) (T : List (ℕ × ℕ)) (a b : Fin n), IsAO2 n E ∧
      (∀ t ∈ T, t.1 < n + E.size ∧ t.2 < n + E.size) ∧
      (∀ w < n + E.size, ∃ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue E n x w = true ∧ graphFun G ∅ x = false) ∧
      E.size + 2 * T.length + 1 ≤ D.size + 2 * B.length ∧
      (∀ x : Fin n → Bool, products n E T x → graphFun G ∅ x = true) ∧
      (∀ x : Fin n → Bool, PEqualNP.BlindGate.wireValue D n x (n + j) = false →
        graphFun G ∅ x = true → products n E T x) ∧
      G.Adj a b ∧ PEqualNP.BlindGate.wireValue D n (edgeAssignment a b) (n + j) = true ∧
      ¬ products n E T (edgeAssignment a b) := by
  classical
  obtain ⟨E, T, hE, hvalid, hnonbelow, hcost, hsound, hagree⟩ :=
    ZeroPrune.zero_prune_last_and_residual n (graphFun G ∅) D B j hres hj hOR
  let α := {p : Fin n × Fin n // G.Adj p.1 p.2}
  let basis : α → Fin n → Bool := fun e => edgeAssignment e.val.1 e.val.2
  have hpositive : ∀ e : α, graphFun G ∅ (basis e) = true := by
    intro e
    exact graph_edge_assignment_true G e.val.1 e.val.2 e.property
  have hcover : ∀ x : Fin n → Bool, graphFun G ∅ x = true →
      ∃ e : α, ∀ i, basis e i = true → x i = true := by
    intro x hx
    obtain ⟨a, b, hab, hle⟩ := graph_positive_contains_edge_assignment G x hx
    exact ⟨⟨(a, b), hab⟩, hle⟩
  obtain ⟨e, he, hbad⟩ := minimum_residual_essential_basis n (graphFun G ∅) D B j hmin
    E T hE hvalid hnonbelow (by omega) hsound hagree basis hpositive hcover
  exact ⟨E, T, e.val.1, e.val.2, hE, hvalid, hnonbelow, hcost, hsound, hagree,
    e.property, he, hbad⟩

lemma minimum_last_gate_accepts_graph_edge (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (D : Circuit) (B : List (ℕ × ℕ)) (j : ℕ)
    (hres : IsResidual n (graphFun G ∅) D B) (hj : j < D.size)
    (hOR : ∀ k < D.size, j < k → (gateAt D k).op = GateOp.or)
    (hmin : ∀ (E : Circuit) (T : List (ℕ × ℕ)), IsResidual n (graphFun G ∅) E T →
      D.size + 2 * B.length ≤ E.size + 2 * T.length) :
    ∃ a b : Fin n, G.Adj a b ∧
      PEqualNP.BlindGate.wireValue D n (edgeAssignment a b) (n + j) = true := by
  obtain ⟨E, T, a, b, _, _, _, _, _, _, hab, hgate, _⟩ :=
    minimum_last_gate_has_essential_graph_edge n G D B j hres hj hOR hmin
  exact ⟨a, b, hab, hgate⟩

end GlobalOrFrontier


namespace ZeroPrune

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover
open ProductFactor LastAndFactor GlobalOrFrontier

def WireExact (n : ℕ) (D E : Circuit) (w : ℕ) (r : Option ℕ) : Prop :=
  ∃ v, r = some v ∧ v < n + E.size ∧ ∀ x : Fin n → Bool,
    PEqualNP.BlindGate.wireValue E n x v = PEqualNP.BlindGate.wireValue D n x w

def MapExactOutside (n : ℕ) (D E : Circuit) (f : ℕ → Option ℕ) (S : ℕ → Prop) (m : ℕ) : Prop :=
  ∀ w < m, ¬ S w → WireExact n D E w (f w)

lemma wireExact_transport (n : ℕ) (D E E' : Circuit) (w : ℕ) (r : Option ℕ)
    (h : WireExact n D E w r) (hle : E.size ≤ E'.size)
    (heq : ∀ v < n + E.size, ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E' n x v = PEqualNP.BlindGate.wireValue E n x v) :
    WireExact n D E' w r := by
  obtain ⟨v, hr, hv, hval⟩ := h
  exact ⟨v, hr, by omega, fun x => (heq v hv x).trans (hval x)⟩

lemma mapExactOutside_extend (n : ℕ) (D E : Circuit) (f : ℕ → Option ℕ)
    (S : ℕ → Prop) (m : ℕ) (r : Option ℕ) (h : MapExactOutside n D E f S m)
    (hr : ¬ S m → WireExact n D E m r) :
    MapExactOutside n D E (Function.update f m r) S (m + 1) := by
  intro w hw hs
  by_cases hwm : w = m
  · subst w
    simpa only [Function.update_self] using hr hs
  · rw [Function.update_of_ne hwm]
    exact h w (by omega) hs

lemma build_or_step_tracked (n : ℕ) (D E : Circuit) (j w u v : ℕ)
    (ru rv : Option ℕ) (S : ℕ → Prop) (F : (Fin n → Bool) → Bool) (hE : IsAO2 n E)
    (hnot : ∀ z < n + E.size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue E n x z = true ∧ F x = false)
    (hu : WireSound n D E j u ru) (hv : WireSound n D E j v rv)
    (hval : ∀ x : Fin n → Bool, PEqualNP.BlindGate.wireValue D n x w =
      (PEqualNP.BlindGate.wireValue D n x u || PEqualNP.BlindGate.wireValue D n x v))
    (hout : ¬ S w → WireExact n D E u ru ∧ WireExact n D E v rv) :
    ∃ (E' : Circuit) (r : Option ℕ), IsAO2 n E' ∧
      (∀ z < n + E'.size, ∃ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue E' n x z = true ∧ F x = false) ∧
      E.size ≤ E'.size ∧ E'.size ≤ E.size + 1 ∧
      (∀ z < n + E.size, ∀ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue E' n x z = PEqualNP.BlindGate.wireValue E n x z) ∧
      WireSound n D E' j w r ∧ (¬ S w → WireExact n D E' w r) := by
  classical
  by_cases hs : S w
  · obtain ⟨E', r, hE', hn', hle, hup, heq, hr⟩ :=
      build_or_step n D E j w u v ru rv F hE hnot hu hv hval
    exact ⟨E', r, hE', hn', hle, hup, heq, hr, fun hn => False.elim (hn hs)⟩
  · obtain ⟨⟨p, hrp, hp, hpe⟩, ⟨q, hrq, hq, hqe⟩⟩ := hout hs
    have hnewval : ∀ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue (appendOr E p q) n x (n + E.size) =
          PEqualNP.BlindGate.wireValue D n x w := by
      intro x
      rw [new_wire_appendOr n E p q hE hp hq x, hpe x, hqe x, hval x]
    have hnewbound : n + E.size < n + (appendOr E p q).size := by
      rw [appendOr_size]; omega
    refine ⟨appendOr E p q, some (n + E.size), appendOr_ao2 n E p q hE hp hq,
      appendOr_all_nonbelow n E p q F hE hp hq hnot, ?_, ?_,
      fun z hz x => old_wire_appendOr n E p q z hz x,
      ⟨hnewbound, ?_, ?_⟩, ?_⟩
    · rw [appendOr_size]; omega
    · rw [appendOr_size]
    · intro x hx
      exact (hnewval x).symm.trans hx
    · intro x _
      exact hnewval x
    · intro _
      exact ⟨n + E.size, rfl, hnewbound, hnewval⟩

lemma prefix_base_tracked (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (j : ℕ) (S : ℕ → Prop)
    (hD : IsAO2 n D) (hj : j < D.size)
    (hnot : ∀ w < n + D.size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x w = true ∧ F x = false)
    (hseed : S (n + j)) :
    ∃ (E : Circuit) (f : ℕ → Option ℕ), IsAO2 n E ∧
      (∀ z < n + E.size, ∃ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue E n x z = true ∧ F x = false) ∧
      E.size + 1 ≤ j + 1 ∧ MapSound n D E j f (n + j + 1) ∧
      MapExactOutside n D E f S (n + j + 1) := by
  have hsize := prefix_size D j (by omega)
  refine ⟨circuitPrefix D j, (fun w => if w = n + j then none else some w),
    prefix_isAO2 n D j hD, ?_, by omega, ?_, ?_⟩
  · intro w hw
    rcases hnot w (by omega) with ⟨x, hx, hF⟩
    refine ⟨x, ?_, hF⟩
    rw [prefix_wire n D j (by omega) x w (by omega)]
    exact hx
  · intro w hw
    by_cases hweq : w = n + j
    · subst w
      simp only [WireSound]
      intro x hx
      exact hx
    · simp only [hweq, ite_false, WireSound]
      have hwj : w < n + j := by omega
      refine ⟨by omega, ?_, ?_⟩
      · intro x hx
        rwa [prefix_wire n D j (by omega) x w hwj] at hx
      · intro x _
        exact prefix_wire n D j (by omega) x w hwj
  · intro w hw hSw
    have hweq : w ≠ n + j := by
      intro heq
      exact hSw (heq.symm ▸ hseed)
    refine ⟨w, ?_, by omega, ?_⟩
    · simp only [hweq, ite_false]
    · intro x
      exact prefix_wire n D j (by omega) x w (by omega)

end ZeroPrune

namespace ZeroPrune

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover
open ProductFactor LastAndFactor GlobalOrFrontier

lemma zero_prune_or_suffix_map_tracked (n : ℕ) (D : Circuit) (j : ℕ) (S : ℕ → Prop)
    (F : (Fin n → Bool) → Bool) (hD : IsAO2 n D) (hj : j < D.size)
    (hnot : ∀ w < n + D.size, ∃ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x w = true ∧ F x = false)
    (hOR : ∀ k < D.size, j < k → (gateAt D k).op = GateOp.or)
    (hS : IsForwardClosure n D j S) :
    ∃ (E : Circuit) (f : ℕ → Option ℕ), IsAO2 n E ∧
      (∀ w < n + E.size, ∃ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue E n x w = true ∧ F x = false) ∧
      E.size + 1 ≤ D.size ∧ MapSound n D E j f (n + D.size) ∧
      MapExactOutside n D E f S (n + D.size) := by
  have hbuild : ∀ k : ℕ, j < k → k ≤ D.size →
      ∃ (E : Circuit) (f : ℕ → Option ℕ), IsAO2 n E ∧
        (∀ w < n + E.size, ∃ x : Fin n → Bool,
          PEqualNP.BlindGate.wireValue E n x w = true ∧ F x = false) ∧
        E.size + 1 ≤ k ∧ MapSound n D E j f (n + k) ∧ MapExactOutside n D E f S (n + k) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hjk hk
      by_cases hbase : k = j + 1
      · subst k
        simpa only [Nat.add_assoc] using prefix_base_tracked n F D j S hD hj hnot hS.2.1
      · have hjprev : j < k - 1 := by omega
        have hprev : k - 1 < k := by omega
        have hkprev : k - 1 < D.size := by omega
        obtain ⟨E, f, hE, hnotE, hsize, hmap, houtside⟩ := ih (k - 1) hprev hjprev (by omega)
        obtain ⟨u, v, hin, hu, hv⟩ := SplitAux.gate_inputs_two n D hD (k - 1) hkprev
        have hval : ∀ x : Fin n → Bool,
            PEqualNP.BlindGate.wireValue D n x (n + (k - 1)) =
              (PEqualNP.BlindGate.wireValue D n x u || PEqualNP.BlindGate.wireValue D n x v) :=
          SplitAux.wireValue_or_pair n D hD.2.1 (k - 1) u v hkprev
            (hOR (k - 1) hkprev hjprev) hin
        have hout : ¬ S (n + (k - 1)) →
            WireExact n D E u (f u) ∧ WireExact n D E v (f v) := by
          intro hs
          have hsu : ¬ S u := by
            intro h
            apply hs
            exact (hS.2.2 (k - 1) hkprev (by omega)).mpr ⟨u, by simp [hin], h⟩
          have hsv : ¬ S v := by
            intro h
            apply hs
            exact (hS.2.2 (k - 1) hkprev (by omega)).mpr ⟨v, by simp [hin], h⟩
          exact ⟨houtside u hu hsu, houtside v hv hsv⟩
        obtain ⟨E', r, hE', hnotE', hle, hupper, heq, hr, hre⟩ :=
          build_or_step_tracked n D E j (n + (k - 1)) u v (f u) (f v) S F hE hnotE
            (hmap u hu) (hmap v hv) hval hout
        have hmap' : MapSound n D E' j f (n + (k - 1)) := by
          intro w hw
          exact wireSound_transport n D E E' j w (f w) (hmap w hw) hle heq
        have houtside' : MapExactOutside n D E' f S (n + (k - 1)) := by
          intro w hw hs
          exact wireExact_transport n D E E' w (f w) (houtside w hw hs) hle heq
        have hext := mapSound_extend n D E' j f (n + (k - 1)) r hmap' hr
        have hextout := mapExactOutside_extend n D E' f S (n + (k - 1)) r houtside' hre
        have hnum : n + (k - 1) + 1 = n + k := by omega
        refine ⟨E', Function.update f (n + (k - 1)) r, hE', hnotE', by omega, ?_, ?_⟩
        · rwa [hnum] at hext
        · rwa [hnum] at hextout
  exact hbuild D.size hj le_rfl

lemma mapProducts_preserves_unaffected (n : ℕ) (D E : Circuit) (f : ℕ → Option ℕ)
    (S : ℕ → Prop) (B : List (ℕ × ℕ))
    (hbound : ∀ t ∈ B, t.1 < n + D.size ∧ t.2 < n + D.size)
    (houtside : MapExactOutside n D E f S (n + D.size)) :
    ∀ t ∈ B, ¬ S t.1 → ¬ S t.2 → ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x t.1 = true →
      PEqualNP.BlindGate.wireValue D n x t.2 = true → products n E (mapProducts f B) x := by
  intro t ht hs1 hs2 x h1 h2
  obtain ⟨u, hu, _, hval1⟩ := houtside t.1 (hbound t ht).1 hs1
  obtain ⟨v, hv, _, hval2⟩ := houtside t.2 (hbound t ht).2 hs2
  exact ⟨(u, v), (mem_mapProducts f B (u, v)).mpr ⟨t, ht, u, v, hu, hv, rfl⟩,
    (hval1 x).trans h1, (hval2 x).trans h2⟩

lemma zero_prune_last_and_residual_tracked (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (j : ℕ) (S : ℕ → Prop)
    (hres : IsResidual n F D B) (hj : j < D.size)
    (hOR : ∀ k < D.size, j < k → (gateAt D k).op = GateOp.or)
    (hS : IsForwardClosure n D j S) :
    ∃ (E : Circuit) (T : List (ℕ × ℕ)), IsAO2 n E ∧
      (∀ t ∈ T, t.1 < n + E.size ∧ t.2 < n + E.size) ∧
      (∀ w < n + E.size, ∃ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue E n x w = true ∧ F x = false) ∧
      E.size + 2 * T.length + 1 ≤ D.size + 2 * B.length ∧
      (∀ x : Fin n → Bool, products n E T x → F x = true) ∧
      (∀ x : Fin n → Bool, PEqualNP.BlindGate.wireValue D n x (n + j) = false →
        F x = true → products n E T x) ∧
      (∀ t ∈ B, ¬ S t.1 → ¬ S t.2 → ∀ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue D n x t.1 = true →
        PEqualNP.BlindGate.wireValue D n x t.2 = true → products n E T x) := by
  obtain ⟨E, f, hE, hnot, hsize, hmap, houtside⟩ :=
    zero_prune_or_suffix_map_tracked n D j S F hres.1 hj hres.2.2.1 hOR hS
  refine ⟨E, mapProducts f B, hE, mapProducts_bound n D E j f B hmap hres.2.1,
    hnot, ?_, ?_, ?_, mapProducts_preserves_unaffected n D E f S B hres.2.1 houtside⟩
  · have := mapProducts_length_le f B
    omega
  · intro x hx
    exact (hres.2.2.2 x).mpr (mapProducts_sound n D E j f B hmap hres.2.1 x hx)
  · intro x hzero hF
    exact mapProducts_complete_when_zero n D E j f B hmap hres.2.1 x hzero
      ((hres.2.2.2 x).mp hF)

end ZeroPrune

namespace GlobalOrFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover
open ProductFactor LastAndFactor

lemma true_context_has_safe_atomic_guard (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (j : ℕ) (S : ℕ → Prop)
    (hres : IsResidual n F D B) (hS : IsOrFrontier n D j S)
    (t : ℕ × ℕ) (ht : t ∈ B) (x : Fin n → Bool)
    (hcontext : (S t.1 ∧ PEqualNP.BlindGate.wireValue D n x t.2 = true) ∨
      (S t.2 ∧ PEqualNP.BlindGate.wireValue D n x t.1 = true)) :
    ∃ r < n + D.size, PEqualNP.BlindGate.wireValue D n x r = true ∧
      (r < n ∨ ∃ k < D.size, r = n + k ∧ (gateAt D k).op = GateOp.and) ∧
      (∀ y : Fin n → Bool, PEqualNP.BlindGate.wireValue D n y (n + j) = true →
        PEqualNP.BlindGate.wireValue D n y r = true → F y = true) := by
  have build (q : ℕ) (hq : q < n + D.size)
      (hqx : PEqualNP.BlindGate.wireValue D n x q = true)
      (hqsafe : ∀ y : Fin n → Bool, PEqualNP.BlindGate.wireValue D n y (n + j) = true →
        PEqualNP.BlindGate.wireValue D n y q = true → F y = true) :
      ∃ r < n + D.size, PEqualNP.BlindGate.wireValue D n x r = true ∧
        (r < n ∨ ∃ k < D.size, r = n + k ∧ (gateAt D k).op = GateOp.and) ∧
        (∀ y : Fin n → Bool, PEqualNP.BlindGate.wireValue D n y (n + j) = true →
          PEqualNP.BlindGate.wireValue D n y r = true → F y = true) := by
    obtain ⟨r, hrq, hrx, hatom, hdom⟩ := true_wire_has_or_trace_atom n D hres.1 x q hq hqx
    exact ⟨r, by omega, hrx, hatom, fun y hJ hr => hqsafe y hJ (hdom y hr)⟩
  rcases hcontext with ⟨hs, hp⟩ | ⟨hs, hp⟩
  · apply build t.2 (hres.2.1 t ht).2 hp
    intro y hJ hq
    exact (hres.2.2.2 y).mpr ⟨t, ht,
      frontier_dominates n D j S hres.1 hS t.1 (hres.2.1 t ht).1 hs y hJ, hq⟩
  · apply build t.1 (hres.2.1 t ht).1 hp
    intro y hJ hq
    exact (hres.2.2.2 y).mpr ⟨t, ht, hq,
      frontier_dominates n D j S hres.1 hS t.2 (hres.2.1 t ht).2 hs y hJ⟩

lemma lost_positive_has_safe_atomic_guard (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D E : Circuit) (B T : List (ℕ × ℕ)) (j : ℕ) (S : ℕ → Prop)
    (hres : IsResidual n F D B) (hS : IsOrFrontier n D j S)
    (x : Fin n → Bool) (hFx : F x = true) (hbad : ¬ products n E T x)
    (hpres : ∀ t ∈ B, ¬ S t.1 → ¬ S t.2 →
      PEqualNP.BlindGate.wireValue D n x t.1 = true →
      PEqualNP.BlindGate.wireValue D n x t.2 = true → products n E T x) :
    ∃ r < n + D.size, PEqualNP.BlindGate.wireValue D n x r = true ∧
      (r < n ∨ ∃ k < D.size, r = n + k ∧ (gateAt D k).op = GateOp.and) ∧
      (∀ y : Fin n → Bool, PEqualNP.BlindGate.wireValue D n y (n + j) = true →
        PEqualNP.BlindGate.wireValue D n y r = true → F y = true) := by
  classical
  obtain ⟨t, ht, h1, h2⟩ := (hres.2.2.2 x).mp hFx
  apply true_context_has_safe_atomic_guard n F D B j S hres hS t ht x
  by_cases hs : S t.1
  · exact Or.inl ⟨hs, h2⟩
  · by_cases hs2 : S t.2
    · exact Or.inr ⟨hs2, h1⟩
    · exact False.elim (hbad (hpres t ht hs hs2 h1 h2))

lemma last_gate_lost_positive_has_earlier_atomic_guard (n : ℕ)
    (F : (Fin n → Bool) → Bool) (D E : Circuit) (B T : List (ℕ × ℕ)) (j : ℕ)
    (hres : IsResidual n F D B) (hj : j < D.size)
    (hOR : ∀ k < D.size, j < k → (gateAt D k).op = GateOp.or)
    (x : Fin n → Bool) (hFx : F x = true) (hbad : ¬ products n E T x)
    (hpres : ∀ t ∈ B, ¬ descendants n D j t.1 → ¬ descendants n D j t.2 →
      PEqualNP.BlindGate.wireValue D n x t.1 = true →
      PEqualNP.BlindGate.wireValue D n x t.2 = true → products n E T x) :
    ∃ r < n + D.size, PEqualNP.BlindGate.wireValue D n x r = true ∧
      (r < n ∨ ∃ k < j, r = n + k ∧ (gateAt D k).op = GateOp.and) ∧
      (∀ y : Fin n → Bool, PEqualNP.BlindGate.wireValue D n y (n + j) = true →
        PEqualNP.BlindGate.wireValue D n y r = true → F y = true) := by
  have hS := last_and_descendants_frontier n D j hres.1 hOR
  obtain ⟨r, hr, hrx, hatom, hsafe⟩ := lost_positive_has_safe_atomic_guard n F D E B T j
    (descendants n D j) hres hS x hFx hbad hpres
  have hdirty := hres.2.2.1 (n + j) (by omega)
  exact ⟨r, hr, hrx, last_and_atomic_guard_is_earlier n F D j r hOR hdirty hatom hsafe, hsafe⟩

end GlobalOrFrontier

namespace GlobalOrFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover
open ProductFactor LastAndFactor

lemma minimum_last_gate_has_productive_guard (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (D : Circuit) (B : List (ℕ × ℕ)) (j : ℕ)
    (hres : IsResidual n (graphFun G ∅) D B) (hj : j < D.size)
    (hOR : ∀ k < D.size, j < k → (gateAt D k).op = GateOp.or)
    (hmin : ∀ (E : Circuit) (T : List (ℕ × ℕ)), IsResidual n (graphFun G ∅) E T →
      D.size + 2 * B.length ≤ E.size + 2 * T.length) :
    ∃ a b : Fin n, G.Adj a b ∧
      PEqualNP.BlindGate.wireValue D n (edgeAssignment a b) (n + j) = true ∧
      ((∃ v : Fin n, (v = a ∨ v = b) ∧
        ∀ x : Fin n → Bool, PEqualNP.BlindGate.wireValue D n x (n + j) = true →
          x v = true → graphFun G ∅ x = true) ∨
        ∃ k < j, (gateAt D k).op = GateOp.and ∧
          PEqualNP.BlindGate.wireValue D n (edgeAssignment a b) (n + k) = true ∧
          ∀ x : Fin n → Bool, PEqualNP.BlindGate.wireValue D n x (n + j) = true →
            PEqualNP.BlindGate.wireValue D n x (n + k) = true → graphFun G ∅ x = true) := by
  classical
  let S := descendants n D j
  have hS : IsForwardClosure n D j S := descendants_forward_closure n D j hres.1
  obtain ⟨E, T, hE, hvalid, hnonbelow, hcost, hsound, hagree, houtside⟩ :=
    ZeroPrune.zero_prune_last_and_residual_tracked n (graphFun G ∅) D B j S hres hj hOR hS
  let α := {p : Fin n × Fin n // G.Adj p.1 p.2}
  let basis : α → Fin n → Bool := fun e => edgeAssignment e.val.1 e.val.2
  have hpositive : ∀ e : α, graphFun G ∅ (basis e) = true := by
    intro e
    exact graph_edge_assignment_true G e.val.1 e.val.2 e.property
  have hcover : ∀ x : Fin n → Bool, graphFun G ∅ x = true →
      ∃ e : α, ∀ i, basis e i = true → x i = true := by
    intro x hx
    obtain ⟨a, b, hab, hle⟩ := graph_positive_contains_edge_assignment G x hx
    exact ⟨⟨(a, b), hab⟩, hle⟩
  obtain ⟨e, hJe, hbad⟩ := minimum_residual_essential_basis n (graphFun G ∅) D B j hmin
    E T hE hvalid hnonbelow (by omega) hsound hagree basis hpositive hcover
  have hpres : ∀ t ∈ B, ¬ descendants n D j t.1 → ¬ descendants n D j t.2 →
      PEqualNP.BlindGate.wireValue D n (basis e) t.1 = true →
      PEqualNP.BlindGate.wireValue D n (basis e) t.2 = true → products n E T (basis e) := by
    intro t ht h1 h2
    exact houtside t ht h1 h2 (basis e)
  obtain ⟨r, hr, hre, hkind, hsafe⟩ := last_gate_lost_positive_has_earlier_atomic_guard n
    (graphFun G ∅) D E B T j hres hj hOR (basis e) (hpositive e) hbad hpres
  refine ⟨e.val.1, e.val.2, e.property, hJe, ?_⟩
  rcases hkind with hraw | ⟨k, hk, rfl, hand⟩
  · refine Or.inl ⟨⟨r, hraw⟩, ?_, ?_⟩
    · rw [SplitAux.wireValue_input n D (basis e) r hraw] at hre
      simpa only [basis, edgeAssignment, decide_eq_true_eq] using hre
    · intro x hJ hv
      apply hsafe x hJ
      rw [SplitAux.wireValue_input n D x r hraw]
      exact hv
  · exact Or.inr ⟨k, hk, hand, hre, hsafe⟩

end GlobalOrFrontier

namespace GlobalOrFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover
open ProductFactor

lemma graph_residual_gate_not_below (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (D : Circuit) (B : List (ℕ × ℕ))
    (hres : IsResidual n (graphFun G ∅) D B) (j : ℕ) (hj : j < D.size) :
    ¬ PEqualNP.TopForm.BelowF G D j := by
  intro hbelow
  obtain ⟨x, hx, hF⟩ := hres.2.2.1 (n + j) (by omega)
  have htrue := hbelow x hx
  rw [hF] at htrue
  cases htrue

lemma graph_residual_topForm (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (D : Circuit) (B : List (ℕ × ℕ))
    (hres : IsResidual n (graphFun G ∅) D B) : PEqualNP.TopForm.TopForm G D := by
  intro i hi j hj hiand hib hjand
  exact False.elim (graph_residual_gate_not_below n G D B hres i hi hib)

lemma graph_residual_and_is_dirty (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (D : Circuit) (B : List (ℕ × ℕ))
    (hres : IsResidual n (graphFun G ∅) D B) (j : ℕ) (hj : j < D.size)
    (hand : (gateAt D j).op = GateOp.and) : PEqualNP.CleanedNonEdge.IsDirtyAnd n G D j := by
  exact ⟨hand, hj, hres.2.2.1 (n + j) (by omega)⟩

end GlobalOrFrontier


namespace ZeroPrune

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover
open ProductFactor LastAndFactor

lemma build_or_step_plain (n : ℕ) (D E : Circuit) (j w u v : ℕ) (ru rv : Option ℕ)
    (hE : IsAO2 n E)
    (hu : WireSound n D E j u ru) (hv : WireSound n D E j v rv)
    (hval : ∀ x : Fin n → Bool, PEqualNP.BlindGate.wireValue D n x w =
      (PEqualNP.BlindGate.wireValue D n x u || PEqualNP.BlindGate.wireValue D n x v)) :
    ∃ (E' : Circuit) (r : Option ℕ), IsAO2 n E' ∧
      E.size ≤ E'.size ∧ E'.size ≤ E.size + 1 ∧
      (∀ z < n + E.size, ∀ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue E' n x z = PEqualNP.BlindGate.wireValue E n x z) ∧
      WireSound n D E' j w r := by
  cases ru with
  | none =>
    cases rv with
    | none =>
      refine ⟨E, none, hE, le_rfl, by omega, fun _ _ _ => rfl, ?_⟩
      intro x hx
      rw [hval x, hu x hx, hv x hx]
      rfl
    | some q =>
      refine ⟨E, some q, hE, le_rfl, by omega, fun _ _ _ => rfl,
        hv.1, ?_, ?_⟩
      · intro x hx
        rw [hval x, hv.2.1 x hx, Bool.or_true]
      · intro x hx
        rw [hval x, hu x hx, Bool.false_or]
        exact hv.2.2 x hx
  | some p =>
    cases rv with
    | none =>
      refine ⟨E, some p, hE, le_rfl, by omega, fun _ _ _ => rfl,
        hu.1, ?_, ?_⟩
      · intro x hx
        rw [hval x, hu.2.1 x hx]
        rfl
      · intro x hx
        rw [hval x, hv x hx, Bool.or_false]
        exact hu.2.2 x hx
    | some q =>
      refine ⟨appendOr E p q, some (n + E.size), appendOr_ao2 n E p q hE hu.1 hv.1,
        ?_, ?_,
        fun z hz x => old_wire_appendOr n E p q z hz x, ?_⟩
      · rw [appendOr_size]; omega
      · rw [appendOr_size]
      · refine ⟨by rw [appendOr_size]; omega, ?_, ?_⟩
        · intro x hx
          rw [new_wire_appendOr n E p q hE hu.1 hv.1 x, Bool.or_eq_true] at hx
          rw [hval x, Bool.or_eq_true]
          rcases hx with hx | hx
          · exact Or.inl (hu.2.1 x hx)
          · exact Or.inr (hv.2.1 x hx)
        · intro x hx
          rw [new_wire_appendOr n E p q hE hu.1 hv.1 x, hu.2.2 x hx, hv.2.2 x hx, hval x]

lemma build_and_step_plain (n : ℕ) (D E : Circuit) (j w u v : ℕ) (ru rv : Option ℕ)
    (hE : IsAO2 n E)
    (hu : WireSound n D E j u ru) (hv : WireSound n D E j v rv)
    (hval : ∀ x : Fin n → Bool, PEqualNP.BlindGate.wireValue D n x w =
      (PEqualNP.BlindGate.wireValue D n x u && PEqualNP.BlindGate.wireValue D n x v)) :
    ∃ (E' : Circuit) (r : Option ℕ), IsAO2 n E' ∧
      E.size ≤ E'.size ∧ E'.size ≤ E.size + 1 ∧
      (∀ z < n + E.size, ∀ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue E' n x z = PEqualNP.BlindGate.wireValue E n x z) ∧
      WireSound n D E' j w r := by
  cases ru with
  | none =>
    refine ⟨E, none, hE, le_rfl, by omega, fun _ _ _ => rfl, ?_⟩
    intro x hx
    rw [hval x, hu x hx, Bool.false_and]
  | some p =>
    cases rv with
    | none =>
      refine ⟨E, none, hE, le_rfl, by omega, fun _ _ _ => rfl, ?_⟩
      intro x hx
      rw [hval x, hv x hx, Bool.and_false]
    | some q =>
      refine ⟨appendAnd E p q, some (n + E.size), appendAnd_ao2 n E p q hE hu.1 hv.1,
        ?_, ?_, fun z hz x => old_wire_appendAnd n E p q z hz x, ?_⟩
      · rw [appendAnd_size]; omega
      · rw [appendAnd_size]
      · refine ⟨by rw [appendAnd_size]; omega, ?_, ?_⟩
        · intro x hx
          rw [new_wire_appendAnd n E p q hE hu.1 hv.1 x, Bool.and_eq_true] at hx
          rw [hval x, Bool.and_eq_true]
          exact ⟨hu.2.1 x hx.1, hv.2.1 x hx.2⟩
        · intro x hx
          rw [new_wire_appendAnd n E p q hE hu.1 hv.1 x, hu.2.2 x hx, hv.2.2 x hx, hval x]

lemma prefix_base_plain (n : ℕ) (D : Circuit) (j : ℕ)
    (hD : IsAO2 n D) (hj : j < D.size) :
    ∃ (E : Circuit) (f : ℕ → Option ℕ), IsAO2 n E ∧
      E.size + 1 ≤ j + 1 ∧ MapSound n D E j f (n + j + 1) := by
  have hsize := prefix_size D j (by omega)
  refine ⟨circuitPrefix D j, (fun w => if w = n + j then none else some w),
    prefix_isAO2 n D j hD, by omega, ?_⟩
  intro w hw
  by_cases hweq : w = n + j
  · subst w
    simp only [WireSound]
    intro x hx
    exact hx
  · simp only [hweq, ite_false, WireSound]
    have hwj : w < n + j := by omega
    refine ⟨by omega, ?_, ?_⟩
    · intro x hx
      rwa [prefix_wire n D j (by omega) x w hwj] at hx
    · intro x _
      exact prefix_wire n D j (by omega) x w hwj

lemma zero_prune_mixed_map (n : ℕ) (D : Circuit) (j : ℕ)
    (hD : IsAO2 n D) (hj : j < D.size) :
    ∃ (E : Circuit) (f : ℕ → Option ℕ), IsAO2 n E ∧
      E.size + 1 ≤ D.size ∧ MapSound n D E j f (n + D.size) := by
  have hbuild : ∀ k : ℕ, j < k → k ≤ D.size →
      ∃ (E : Circuit) (f : ℕ → Option ℕ), IsAO2 n E ∧
        E.size + 1 ≤ k ∧ MapSound n D E j f (n + k) := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro hjk hk
      by_cases hbase : k = j + 1
      · subst k
        simpa only [Nat.add_assoc] using prefix_base_plain n D j hD hj
      · have hjprev : j < k - 1 := by omega
        have hprev : k - 1 < k := by omega
        have hkprev : k - 1 < D.size := by omega
        obtain ⟨E, f, hE, hsize, hmap⟩ := ih (k - 1) hprev hjprev (by omega)
        obtain ⟨u, v, hin, hu, hv⟩ := SplitAux.gate_inputs_two n D hD (k - 1) hkprev
        have hstep : ∃ (E' : Circuit) (r : Option ℕ), IsAO2 n E' ∧
            E.size ≤ E'.size ∧ E'.size ≤ E.size + 1 ∧
            (∀ z < n + E.size, ∀ x : Fin n → Bool,
              PEqualNP.BlindGate.wireValue E' n x z = PEqualNP.BlindGate.wireValue E n x z) ∧
            WireSound n D E' j (n + (k - 1)) r := by
          have hmem : gateAt D (k - 1) ∈ D.gates := by
            rw [SplitAux.gateAt_eq_getElem D (k - 1) hkprev]
            exact List.getElem_mem hkprev
          rcases hD.1 (gateAt D (k - 1)) hmem with hand | hor
          · exact build_and_step_plain n D E j (n + (k - 1)) u v (f u) (f v) hE
              (hmap u hu) (hmap v hv)
              (SplitAux.wireValue_and_pair n D hD.2.1 (k - 1) u v hkprev hand hin)
          · exact build_or_step_plain n D E j (n + (k - 1)) u v (f u) (f v) hE
              (hmap u hu) (hmap v hv)
              (SplitAux.wireValue_or_pair n D hD.2.1 (k - 1) u v hkprev hor hin)
        obtain ⟨E', r, hE', hle, hupper, heq, hr⟩ := hstep
        have hmap' : MapSound n D E' j f (n + (k - 1)) := by
          intro w hw
          exact wireSound_transport n D E E' j w (f w) (hmap w hw) hle heq
        have hext := mapSound_extend n D E' j f (n + (k - 1)) r hmap' hr
        have hnum : n + (k - 1) + 1 = n + k := by omega
        refine ⟨E', Function.update f (n + (k - 1)) r, hE', by omega, ?_⟩
        rwa [hnum] at hext
  exact hbuild D.size hj le_rfl

lemma zero_prune_any_gate_products (n : ℕ) (F : (Fin n → Bool) → Bool)
    (D : Circuit) (B : List (ℕ × ℕ)) (j : ℕ)
    (hres : IsResidual n F D B) (hj : j < D.size) :
    ∃ (E : Circuit) (T : List (ℕ × ℕ)), IsAO2 n E ∧
      (∀ t ∈ T, t.1 < n + E.size ∧ t.2 < n + E.size) ∧
      E.size + 2 * T.length + 1 ≤ D.size + 2 * B.length ∧
      (∀ x : Fin n → Bool, products n E T x → F x = true) ∧
      (∀ x : Fin n → Bool, PEqualNP.BlindGate.wireValue D n x (n + j) = false →
        F x = true → products n E T x) := by
  obtain ⟨E, f, hE, hsize, hmap⟩ := zero_prune_mixed_map n D j hres.1 hj
  refine ⟨E, mapProducts f B, hE, mapProducts_bound n D E j f B hmap hres.2.1,
    ?_, ?_, ?_⟩
  · have := mapProducts_length_le f B
    omega
  · intro x hx
    exact (hres.2.2.2 x).mpr (mapProducts_sound n D E j f B hmap hres.2.1 x hx)
  · intro x hzero hF
    exact mapProducts_complete_when_zero n D E j f B hmap hres.2.1 x hzero
      ((hres.2.2.2 x).mp hF)

end ZeroPrune


namespace ProductAssembler

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover
open ProductFactor LastAndFactor

lemma assemble_products_wire (n : ℕ) (E : Circuit) (T : List (ℕ × ℕ))
    (hE : IsAO2 n E)
    (hbound : ∀ t ∈ T, t.1 < n + E.size ∧ t.2 < n + E.size)
    (hne : T ≠ []) :
    ∃ (D : Circuit) (w : ℕ), IsAO2 n D ∧ E.size ≤ D.size ∧
      D.size + 1 = E.size + 2 * T.length ∧ w < n + D.size ∧
      (∀ z < n + E.size, ∀ x : Fin n → Bool,
        PEqualNP.BlindGate.wireValue D n x z = PEqualNP.BlindGate.wireValue E n x z) ∧
      (∀ x : Fin n → Bool, PEqualNP.BlindGate.wireValue D n x w = true ↔
        products n E T x) := by
  induction T with
  | nil => exact (hne rfl).elim
  | cons t T ih =>
    have ht := hbound t (by simp)
    by_cases hT : T = []
    · subst T
      refine ⟨appendAnd E t.1 t.2, n + E.size,
        appendAnd_ao2 n E t.1 t.2 hE ht.1 ht.2, ?_, ?_, ?_,
        fun z hz x => old_wire_appendAnd n E t.1 t.2 z hz x, ?_⟩
      · rw [appendAnd_size]; omega
      · rw [appendAnd_size]; simp
      · rw [appendAnd_size]; omega
      · intro x
        rw [new_wire_appendAnd n E t.1 t.2 hE ht.1 ht.2 x]
        simp only [Bool.and_eq_true, products, List.mem_singleton, exists_eq_left]
    · obtain ⟨D, w, hD, hle, hsize, hw, heq, hsem⟩ :=
        ih (fun s hs => hbound s (by simp [hs])) hT
      have ht1 : t.1 < n + D.size := by omega
      have ht2 : t.2 < n + D.size := by omega
      let A := appendAnd D t.1 t.2
      have hA : IsAO2 n A := appendAnd_ao2 n D t.1 t.2 hD ht1 ht2
      have hAsize : A.size = D.size + 1 := appendAnd_size D t.1 t.2
      have hq : n + D.size < n + A.size := by omega
      have hwA : w < n + A.size := by omega
      let O := appendOr A (n + D.size) w
      have hOsize : O.size = A.size + 1 := appendOr_size A (n + D.size) w
      refine ⟨O, n + A.size, appendOr_ao2 n A (n + D.size) w hA hq hwA,
        by omega, ?_, by omega, ?_, ?_⟩
      · simp only [List.length_cons]
        omega
      · intro z hz x
        have hzD : z < n + D.size := by omega
        have hzA : z < n + A.size := by omega
        exact (old_wire_appendOr n A (n + D.size) w z hzA x).trans
          ((old_wire_appendAnd n D t.1 t.2 z hzD x).trans (heq z hz x))
      · intro x
        have hval : PEqualNP.BlindGate.wireValue O n x (n + A.size) =
            ((PEqualNP.BlindGate.wireValue E n x t.1 &&
              PEqualNP.BlindGate.wireValue E n x t.2) ||
              PEqualNP.BlindGate.wireValue D n x w) := by
          rw [new_wire_appendOr n A (n + D.size) w hA hq hwA x,
            new_wire_appendAnd n D t.1 t.2 hD ht1 ht2 x,
            old_wire_appendAnd n D t.1 t.2 w hw x,
            heq t.1 ht.1 x, heq t.2 ht.2 x]
        rw [hval, Bool.or_eq_true, Bool.and_eq_true, hsem x, products_cons]

lemma assemble_products (n : ℕ) (E : Circuit) (T : List (ℕ × ℕ))
    (hE : IsAO2 n E)
    (hbound : ∀ t ∈ T, t.1 < n + E.size ∧ t.2 < n + E.size)
    (hne : T ≠ []) :
    ∃ C : Circuit, IsAO2 n C ∧ C.output < n + C.size ∧
      C.size + 1 = E.size + 2 * T.length ∧
      ∀ x : Fin n → Bool, circuitFun n C x = true ↔ products n E T x := by
  obtain ⟨D, w, hD, _, hsize, hw, _, hsem⟩ :=
    assemble_products_wire n E T hE hbound hne
  refine ⟨⟨D.gates, w⟩, hD, hw, hsize, ?_⟩
  intro x
  exact hsem x

end ProductAssembler

namespace GlobalOrFrontier

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.MetaComplexity PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover
open ProductFactor LastAndFactor

lemma minimum_residual_essential_basis_via_normalization {α : Type*} (n : ℕ)
    (F : (Fin n → Bool) → Bool) (D : Circuit) (B : List (ℕ × ℕ)) (j : ℕ)
    (hres : IsResidual n F D B) (hpositiveF : ∃ x, F x = true)
    (hmin : ∀ (E : Circuit) (T : List (ℕ × ℕ)), IsResidual n F E T →
      D.size + 2 * B.length ≤ E.size + 2 * T.length)
    (E : Circuit) (T : List (ℕ × ℕ)) (hE : IsAO2 n E)
    (hvalid : ∀ t ∈ T, t.1 < n + E.size ∧ t.2 < n + E.size)
    (hcost : E.size + 2 * T.length < D.size + 2 * B.length)
    (hsound : ∀ x : Fin n → Bool, products n E T x → F x = true)
    (hagree : ∀ x : Fin n → Bool,
      PEqualNP.BlindGate.wireValue D n x (n + j) = false →
      F x = true → products n E T x)
    (basis : α → Fin n → Bool) (hpositive : ∀ a, F (basis a) = true)
    (hcover : ∀ x : Fin n → Bool, F x = true →
      ∃ a, ∀ i, basis a i = true → x i = true) :
    ∃ a, PEqualNP.BlindGate.wireValue D n (basis a) (n + j) = true ∧
      ¬ products n E T (basis a) := by
  classical
  by_contra hn
  have hall (a : α) : products n E T (basis a) := by
    by_contra hbad
    have hJ : PEqualNP.BlindGate.wireValue D n (basis a) (n + j) = true := by
      cases hv : PEqualNP.BlindGate.wireValue D n (basis a) (n + j) with
      | false => exact False.elim (hbad (hagree (basis a) hv (hpositive a)))
      | true => rfl
    exact hn ⟨a, hJ, hbad⟩
  have hcomplete : ∀ x : Fin n → Bool, F x = true → products n E T x := by
    intro x hFx
    obtain ⟨a, hax⟩ := hcover x hFx
    obtain ⟨t, ht, h1, h2⟩ := hall a
    exact ⟨t, ht,
      wire_true_mono n E hE (basis a) x hax t.1 (hvalid t ht).1 h1,
      wire_true_mono n E hE (basis a) x hax t.2 (hvalid t ht).2 h2⟩
  have hT : T ≠ [] := by
    obtain ⟨x, hx⟩ := hpositiveF
    obtain ⟨t, ht, _, _⟩ := hcomplete x hx
    intro heq
    simp only [heq, List.not_mem_nil] at ht
  obtain ⟨C, hC, hout, hsize, hsem⟩ :=
    ProductAssembler.assemble_products n E T hE hvalid hT
  have hfun : circuitFun n C = F := by
    funext x
    apply Bool.eq_iff_iff.mpr
    exact (hsem x).trans ⟨hsound x, hcomplete x⟩
  have hinputs : ∀ w < n, ¬ WireBelowOutput n C w := by
    intro w hw hb
    obtain ⟨x, hx, hfalse⟩ := hres.2.2.1 w (by omega)
    have hCx : PEqualNP.BlindGate.wireValue C n x w = true := by
      rw [SplitAux.wireValue_input n C x w hw]
      simpa only [SplitAux.wireValue_input n D x w hw] using hx
    have hyes := hb x hCx
    change circuitFun n C x = true at hyes
    rw [hfun, hfalse] at hyes
    contradiction
  obtain ⟨D', B', hD', hn', hF', hcost'⟩ := product_decomposition n C hC hout hinputs
  have hr' := residual_of_decomposition n (circuitFun n C) D' B' hD'
    (not_below_input_witnesses n C hinputs) hn' hF'
  rw [hfun] at hr'
  have hmin' := hmin D' (validPairs n D' B') hr'
  have hlen := validPairs_length_le n D' B'
  omega

lemma minimum_any_gate_has_essential_graph_edge (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (D : Circuit) (B : List (ℕ × ℕ)) (j : ℕ)
    (hres : IsResidual n (graphFun G ∅) D B) (hj : j < D.size)
    (hne : ∃ a b : Fin n, G.Adj a b)
    (hmin : ∀ (E : Circuit) (T : List (ℕ × ℕ)), IsResidual n (graphFun G ∅) E T →
      D.size + 2 * B.length ≤ E.size + 2 * T.length) :
    ∃ (E : Circuit) (T : List (ℕ × ℕ)) (a b : Fin n), IsAO2 n E ∧
      (∀ t ∈ T, t.1 < n + E.size ∧ t.2 < n + E.size) ∧
      E.size + 2 * T.length + 1 ≤ D.size + 2 * B.length ∧
      (∀ x : Fin n → Bool, products n E T x → graphFun G ∅ x = true) ∧
      (∀ x : Fin n → Bool, PEqualNP.BlindGate.wireValue D n x (n + j) = false →
        graphFun G ∅ x = true → products n E T x) ∧
      G.Adj a b ∧ PEqualNP.BlindGate.wireValue D n (edgeAssignment a b) (n + j) = true ∧
      ¬ products n E T (edgeAssignment a b) := by
  classical
  obtain ⟨E, T, hE, hvalid, hcost, hsound, hagree⟩ :=
    ZeroPrune.zero_prune_any_gate_products n (graphFun G ∅) D B j hres hj
  let α := {p : Fin n × Fin n // G.Adj p.1 p.2}
  let basis : α → Fin n → Bool := fun e => edgeAssignment e.val.1 e.val.2
  have hpositive : ∀ e : α, graphFun G ∅ (basis e) = true := by
    intro e
    exact graph_edge_assignment_true G e.val.1 e.val.2 e.property
  have hcover : ∀ x : Fin n → Bool, graphFun G ∅ x = true →
      ∃ e : α, ∀ i, basis e i = true → x i = true := by
    intro x hx
    obtain ⟨a, b, hab, hle⟩ := graph_positive_contains_edge_assignment G x hx
    exact ⟨⟨(a, b), hab⟩, hle⟩
  have hpositiveF : ∃ x, graphFun G ∅ x = true := by
    obtain ⟨a, b, hab⟩ := hne
    exact ⟨edgeAssignment a b, graph_edge_assignment_true G a b hab⟩
  obtain ⟨e, he, hbad⟩ := minimum_residual_essential_basis_via_normalization n (graphFun G ∅)
    D B j hres hpositiveF hmin E T hE hvalid (by omega) hsound hagree basis hpositive hcover
  exact ⟨E, T, e.val.1, e.val.2, hE, hvalid, hcost, hsound, hagree, e.property, he, hbad⟩

lemma minimum_any_gate_accepts_graph_edge (n : ℕ) (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (D : Circuit) (B : List (ℕ × ℕ)) (j : ℕ)
    (hres : IsResidual n (graphFun G ∅) D B) (hj : j < D.size)
    (hne : ∃ a b : Fin n, G.Adj a b)
    (hmin : ∀ (E : Circuit) (T : List (ℕ × ℕ)), IsResidual n (graphFun G ∅) E T →
      D.size + 2 * B.length ≤ E.size + 2 * T.length) :
    ∃ a b : Fin n, G.Adj a b ∧
      PEqualNP.BlindGate.wireValue D n (edgeAssignment a b) (n + j) = true := by
  obtain ⟨E, T, a, b, _, _, _, _, _, hab, hgate, _⟩ :=
    minimum_any_gate_has_essential_graph_edge n G D B j hres hj hne hmin
  exact ⟨a, b, hab, hgate⟩

end GlobalOrFrontier

end PEqualNP.Outside.L_meta_2583
