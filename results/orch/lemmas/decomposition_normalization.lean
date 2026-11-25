import Mathlib.Logic.Relation
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

open PEqualNP.CircuitLowerBounds

lemma exists_size_measure_minimal
    (P : Circuit → Prop) (measure : Circuit → ℕ) (C : Circuit) (hC : P C) :
    ∃ D : Circuit, P D ∧ D.size ≤ C.size ∧
      (∀ E : Circuit, P E → D.size ≤ E.size) ∧
      (∀ E : Circuit, P E → E.size = D.size → measure D ≤ measure E) := by
  classical
  have hs : ∃ s : ℕ, ∃ D : Circuit, P D ∧ D.size = s :=
    ⟨C.size, C, hC, rfl⟩
  obtain ⟨E, hE, hEs⟩ := Nat.find_spec hs
  have hm : ∃ m : ℕ, ∃ D : Circuit,
      P D ∧ D.size = Nat.find hs ∧ measure D = m :=
    ⟨measure E, E, hE, hEs, rfl⟩
  obtain ⟨D, hD, hDs, hDm⟩ := Nat.find_spec hm
  refine ⟨D, hD, ?_, ?_, ?_⟩
  · rw [hDs]
    exact Nat.find_min' hs ⟨C, hC, rfl⟩
  · intro F hF
    rw [hDs]
    exact Nat.find_min' hs ⟨F, hF, rfl⟩
  · intro F hF hFs
    rw [hDm]
    exact Nat.find_min' hm ⟨F, hF, hFs.trans hDs, rfl⟩

end PEqualNP.Outside.L_meta_2583

namespace PEqualNP.Outside.L_meta_2583.Normalization

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

lemma fixed_point : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 x1 x2 → x2.output < x1 + x2.gates.length → ∃ (x5 : PEqualNP.CircuitLowerBounds.Circuit), Relation.ReflTransGen (PEqualNP.CircuitMoves.Lift x1) x2 x5 ∧ ∀ x6 < x5.gates.length, ∀ (x8 x9 : ℕ), x5.gates[x6]? = Option.some { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [x8, x9] : PEqualNP.CircuitLowerBounds.Gate } → (x1 ≤ x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x9 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x8) ∧ (x1 ≤ x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x8 → PEqualNP.CircuitMoves.WireBelowOutput x1 x5 x9) := by
  intro n C hAO hout
  have main : ∀ k : ℕ, ∀ C0 : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.TopForm.IsAO2 n C0 →
      C0.output < n + C0.gates.length →
      C0.gates.length - PEqualNP.Outside.L_meta_2583.Normalization.belowCount n C0 = k →
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
          rw [PEqualNP.Outside.L_meta_2583.Normalization.gateAt_eq_getElem C0 m hm] at this
          have hgm : C0.gates[m] = { op := PEqualNP.CircuitLowerBounds.GateOp.or, inputs := [a, b] } := by
            simpa [hm] using hgate
          rw [hgm] at this
          exact this (by simp)
        have hb_lt : b < n + m := by
          have := hAO0.2.1 m hm b
          rw [PEqualNP.Outside.L_meta_2583.Normalization.gateAt_eq_getElem C0 m hm] at this
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
        have hAO1 := PEqualNP.Outside.L_meta_2583.Normalization.liftAt_isAO2 n C0 m p h hAO0 hout0 hm hp hh
        have hlen1 := PEqualNP.Outside.L_meta_2583.Normalization.liftAt_gates_length n C0 m p h hm
        have hElen := PEqualNP.Outside.L_meta_2583.Normalization.eraseGate_gates_length n C0 m p hm
        have hout1 : (PEqualNP.CircuitMoves.liftAt n C0 m p h).output <
            n + (PEqualNP.CircuitMoves.liftAt n C0 m p h).gates.length := by
          change n + (PEqualNP.CircuitMoves.eraseGate n C0 m p).gates.length <
            n + (PEqualNP.CircuitMoves.liftAt n C0 m p h).gates.length
          omega
        have hlt := PEqualNP.Outside.L_meta_2583.Normalization.belowCount_lt_liftAt n C0 m p h hAO0 hout0 hm hp hh hgm hBh hNp
        have hle1 := PEqualNP.Outside.L_meta_2583.Normalization.belowCount_le n (PEqualNP.CircuitMoves.liftAt n C0 m p h)
        have hk1 : (PEqualNP.CircuitMoves.liftAt n C0 m p h).gates.length -
            PEqualNP.Outside.L_meta_2583.Normalization.belowCount n (PEqualNP.CircuitMoves.liftAt n C0 m p h) < k := by
          omega
        obtain ⟨C', hR, hNF'⟩ := ih _ hk1 (PEqualNP.CircuitMoves.liftAt n C0 m p h) hAO1 hout1 rfl
        exact ⟨C', Relation.ReflTransGen.head hLift hR, hNF'⟩
  exact main _ C hAO hout rfl

lemma lift_closure_preserves (n : ℕ) (C D : Circuit)
    (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hR : Relation.ReflTransGen (Lift n) C D) :
    IsAO2 n D ∧ D.output < n + D.gates.length ∧
      D.size = C.size ∧ PEqualNP.MetaComplexity.circuitFun n D =
        PEqualNP.MetaComplexity.circuitFun n C := by
  induction hR with
  | refl => exact ⟨hAO, hout, rfl, rfl⟩
  | @tail B D hCB hBD ih =>
    obtain ⟨hBA, hBo, hBs, hBf⟩ := ih
    obtain ⟨m, hm, p, hp, h, hh, hnh, hgate, hbelow, rfl⟩ := hBD
    have hlen := liftAt_gates_length n B m p h hm
    have hElen := eraseGate_gates_length n B m p hm
    refine ⟨liftAt_isAO2 n B m p h hBA hBo hm hp hh, ?_, ?_, ?_⟩
    · change n + (eraseGate n B m p).gates.length <
        n + (liftAt n B m p h).gates.length
      omega
    · exact (show (liftAt n B m p h).size = B.size from hlen).trans hBs
    · apply Eq.trans _ hBf
      funext v
      exact liftAt_eval_eq n B m p h hBA hBo hm hp hh hgate hbelow v

lemma exists_least_lift_normal (n : ℕ) (C : Circuit)
    (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length) :
    ∃ D : Circuit, IsAO2 n D ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧
      D.size ≤ C.size ∧ D.output < n + D.gates.length ∧
      (∀ m < D.gates.length, ∀ a b : ℕ,
        D.gates[m]? = some ⟨GateOp.or, [a, b]⟩ →
        (n ≤ b → WireBelowOutput n D b → WireBelowOutput n D a) ∧
        (n ≤ a → WireBelowOutput n D a → WireBelowOutput n D b)) ∧
      (∀ E : Circuit, IsAO2 n E →
        PEqualNP.MetaComplexity.circuitFun n E = PEqualNP.MetaComplexity.circuitFun n C →
        E.output < n + E.gates.length → D.size ≤ E.size) := by
  let P : Circuit → Prop := fun E => IsAO2 n E ∧
    PEqualNP.MetaComplexity.circuitFun n E = PEqualNP.MetaComplexity.circuitFun n C ∧
    E.output < n + E.gates.length
  obtain ⟨M, hM, hMC, hMin, _⟩ :=
    PEqualNP.Outside.L_meta_2583.exists_size_measure_minimal P (fun _ => 0) C
      ⟨hAO, rfl, hout⟩
  obtain ⟨D, hR, hNF⟩ := fixed_point n M hM.1 hM.2.2
  obtain ⟨hDA, hDo, hDs, hDf⟩ := lift_closure_preserves n M D hM.1 hM.2.2 hR
  refine ⟨D, hDA, hDf.trans hM.2.1, hDs.le.trans hMC, hDo, hNF, ?_⟩
  intro E hEA hEf hEo
  rw [hDs]
  exact hMin E ⟨hEA, hEf, hEo⟩

end PEqualNP.Outside.L_meta_2583.Normalization
