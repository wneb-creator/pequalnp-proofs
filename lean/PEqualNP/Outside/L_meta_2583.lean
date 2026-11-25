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

end PEqualNP.Outside.L_meta_2583
