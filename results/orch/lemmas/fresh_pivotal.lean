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

namespace PEqualNP.Outside.L_meta_2583.DeadGate

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.Outside.L_meta_2583.Normalization

lemma erase_unused_wires_eq (n : ℕ) (C : Circuit) (m p : ℕ)
    (hAO : IsAO2 n C) (hm : m < C.gates.length) (hp : p < n + m)
    (hUnused : ∀ j (hj : j < C.gates.length), n + m ∉ (C.gates[j]'hj).inputs)
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
      · exact False.elim (hUnused (j + 1) hjC (heq ▸ hu))
      · have hstep := ih (u - 1) (by omega) (by omega)
        have hnotlt : ¬ (u - 1 < n + m) := by omega
        simp only [hnotlt, ↓reduceIte] at hstep
        have hu1 : u - 1 + 1 = u := by omega
        rwa [hu1] at hstep
      · have hult : u < n + m := by omega
        exact eraseGate_wires_prefix n C m p hm x hx u hult

lemma erase_unused_eval_eq (n : ℕ) (C : Circuit) (m p : ℕ)
    (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hm : m < C.gates.length) (hp : p < n + m)
    (hUnused : ∀ j (hj : j < C.gates.length), n + m ∉ (C.gates[j]'hj).inputs)
    (hOutNe : C.output ≠ n + m) (v : Fin n → Bool) :
    (eraseGate n C m p).eval (List.ofFn v) = C.eval (List.ofFn v) := by
  have hx : (List.ofFn v).length = n := List.length_ofFn
  have hEout : (eraseGate n C m p).output = eraseRedirect n m p C.output := by
    simp [eraseGate, hm]
  have hElen := eraseGate_gates_length n C m p hm
  unfold Circuit.eval
  rw [hEout]
  unfold eraseRedirect
  split_ifs with heq hgt
  · exact False.elim (hOutNe heq)
  · have hstep := erase_unused_wires_eq n C m p hAO hm hp hUnused
      (List.ofFn v) hx (C.output - 1) (by omega)
    have hnotlt : ¬ (C.output - 1 < n + m) := by omega
    simp only [hnotlt, ↓reduceIte] at hstep
    have ho1 : C.output - 1 + 1 = C.output := by omega
    rwa [ho1] at hstep
  · have holt : C.output < n + m := by omega
    exact eraseGate_wires_prefix n C m p hm (List.ofFn v) hx C.output holt

lemma least_every_gate_used (n : ℕ) (hn : 0 < n) (C : Circuit)
    (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hmin : ∀ D : Circuit, IsAO2 n D →
      (∀ v : Fin n → Bool, D.eval (List.ofFn v) = C.eval (List.ofFn v)) →
      C.size ≤ D.size) (m : ℕ) (hm : m < C.gates.length) :
    C.output = n + m ∨ ∃ j, ∃ hj : j < C.gates.length,
      m < j ∧ n + m ∈ (C.gates[j]'hj).inputs := by
  classical
  by_contra hbad
  push_neg at hbad
  obtain ⟨hOut, hInputs⟩ := hbad
  have hUnused : ∀ j (hj : j < C.gates.length), n + m ∉ (C.gates[j]'hj).inputs := by
    intro j hj hmem
    have hr := hAO.2.1 j hj (n + m)
    rw [gateAt_eq_getElem C j hj] at hr
    have hmj : m < j := by have := hr hmem; omega
    exact hInputs j hj hmj hmem
  have hp : 0 < n + m := by omega
  have hsize := hmin (eraseGate n C m 0) (eraseGate_isAO2 n C m 0 hAO hm hp)
    (erase_unused_eval_eq n C m 0 hAO hout hm hp hUnused hOut)
  have hlen := eraseGate_gates_length n C m 0 hm
  unfold Circuit.size at hsize
  omega

end PEqualNP.Outside.L_meta_2583.DeadGate

namespace PEqualNP.Outside.L_meta_2583.PairUseful

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.Outside.L_meta_2583.Normalization
  PEqualNP.Outside.L_meta_2583.DeadGate

lemma wires_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (i : Fin n) :
    (C.wires (List.ofFn x)).getD i false = x i := by
  change (evalGates C.gates (List.ofFn x)).getD i false = _
  rw [evalGates_getD_lt C.gates (List.ofFn x) i (by simpa using i.isLt)]
  simp [List.getD_eq_getElem?_getD]

lemma wire_mono (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) :
    ∀ k < n + C.gates.length, (C.wires (List.ofFn x)).getD k false = true →
      (C.wires (List.ofFn y)).getD k false = true := by
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk htrue
    by_cases hkn : k < n
    · have hx := wires_input n C x ⟨k, hkn⟩
      have hy := wires_input n C y ⟨k, hkn⟩
      exact hy.trans (hxy _ (hx.symm.trans htrue))
    · let j := k - n
      have hkj : k = n + j := by omega
      have hj : j < C.gates.length := by omega
      rw [hkj, wires_getD_gate n C hAO.2.1 _ List.length_ofFn j hj] at htrue ⊢
      apply gateOp_eval_mono _ (hAO.1 _ (List.getElem_mem hj)) _ _ _ ?_ htrue
      intro u hu huTrue
      have hu_lt : u < n + j := by
        have hh := hAO.2.1 j hj u
        rw [gateAt_eq_getElem C j hj] at hh
        exact hh hu
      exact ih u (by omega) (by omega) huTrue

lemma erase_or_eval_le (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hm : m < C.gates.length) (hp : p < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨
      C.gates[m]? = some ⟨GateOp.or, [h, p]⟩) (v : Fin n → Bool) :
    (eraseGate n C m p).eval (List.ofFn v) = true → C.eval (List.ofFn v) = true := by
  have hx : (List.ofFn v).length = n := List.length_ofFn
  have hEout : (eraseGate n C m p).output = eraseRedirect n m p C.output := by
    simp [eraseGate, hm]
  have hElen := eraseGate_gates_length n C m p hm
  unfold Circuit.eval
  rw [hEout]
  unfold eraseRedirect
  split_ifs with heq hgt
  · rw [heq, gate_m_val n C m p h hAO.2.1 hm hgate (List.ofFn v) hx]
    rw [eraseGate_wires_prefix n C m p hm (List.ofFn v) hx p hp]
    intro ht
    rw [ht]
    rfl
  · intro ht
    have hstep := eraseGate_wires_le n C m p h hAO hm hp hgate
      (List.ofFn v) hx (C.output - 1) (by omega) ht
    have hnotlt : ¬ (C.output - 1 < n + m) := by omega
    simp only [hnotlt, ↓reduceIte] at hstep
    have ho1 : C.output - 1 + 1 = C.output := by omega
    rwa [ho1] at hstep
  · have holt : C.output < n + m := by omega
    rw [eraseGate_wires_prefix n C m p hm (List.ofFn v) hx C.output holt]
    exact id

lemma erase_or_eval_eq_of_h_false (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hm : m < C.gates.length) (hp : p < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨
      C.gates[m]? = some ⟨GateOp.or, [h, p]⟩) (v : Fin n → Bool)
    (hb : (C.wires (List.ofFn v)).getD h false = false) :
    (eraseGate n C m p).eval (List.ofFn v) = C.eval (List.ofFn v) := by
  have hx : (List.ofFn v).length = n := List.length_ofFn
  have hEout : (eraseGate n C m p).output = eraseRedirect n m p C.output := by
    simp [eraseGate, hm]
  have hElen := eraseGate_gates_length n C m p hm
  unfold Circuit.eval
  rw [hEout]
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

lemma graphFun_pair_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (u v : Fin n) (huv : G.Adj u v) : graphFun G ∅ (pairInput u v) = true := by
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq]
  exact ⟨u, v, huv, by simp [pairInput], by simp [pairInput]⟩

lemma erase_pair_false_or (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (m p h : ℕ) (hAO : IsAO2 n C)
    (hout : C.output < n + C.gates.length)
    (hComp : ∀ v : Fin n → Bool, C.eval (List.ofFn v) = graphFun G ∅ v)
    (hm : m < C.gates.length) (hp : p < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨
      C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (hFalse : ∀ u v : Fin n, G.Adj u v →
      (C.wires (List.ofFn (pairInput u v))).getD h false = false) :
    ∀ v : Fin n → Bool, (eraseGate n C m p).eval (List.ofFn v) = C.eval (List.ofFn v) := by
  intro x
  cases hx : C.eval (List.ofFn x)
  · cases hE : (eraseGate n C m p).eval (List.ofFn x)
    · rfl
    · have := erase_or_eval_le n C m p h hAO hout hm hp hgate x hE
      rw [hx] at this
      contradiction
  · have hF : graphFun G ∅ x = true := (hComp x).symm.trans hx
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq] at hF
    obtain ⟨u, v, huv, hxu, hxv⟩ := hF
    have hPair : C.eval (List.ofFn (pairInput u v)) = true :=
      (hComp _).trans (graphFun_pair_true n G u v huv)
    have hPairE : (eraseGate n C m p).eval (List.ofFn (pairInput u v)) = true :=
      (erase_or_eval_eq_of_h_false n C m p h hAO hout hm hp hgate
        (pairInput u v) (hFalse u v huv)).trans hPair
    apply wire_mono n (eraseGate n C m p) (eraseGate_isAO2 n C m p hAO hm hp)
      (pairInput u v) x ?_ _ (eraseGate_output_lt n C m p hm hp hout) hPairE
    intro i hi
    simp only [pairInput, decide_eq_true_eq] at hi
    rcases hi with rfl | rfl
    · exact hxu
    · exact hxv

lemma least_or_operand_pair_true (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hComp : ∀ v : Fin n → Bool, C.eval (List.ofFn v) = graphFun G ∅ v)
    (hmin : ∀ D : Circuit, IsAO2 n D →
      (∀ v : Fin n → Bool, D.eval (List.ofFn v) = C.eval (List.ofFn v)) →
      C.size ≤ D.size)
    (m p h : ℕ) (hm : m < C.gates.length) (hp : p < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨
      C.gates[m]? = some ⟨GateOp.or, [h, p]⟩) :
    ∃ u v : Fin n, G.Adj u v ∧ (C.wires (List.ofFn (pairInput u v))).getD h false = true := by
  classical
  by_contra hbad
  have hFalse : ∀ u v : Fin n, G.Adj u v →
      (C.wires (List.ofFn (pairInput u v))).getD h false = false := by
    intro u v huv
    cases hh : (C.wires (List.ofFn (pairInput u v))).getD h false
    · rfl
    · exact False.elim (hbad ⟨u, v, huv, hh⟩)
  have hsize := hmin (eraseGate n C m p) (eraseGate_isAO2 n C m p hAO hm hp)
    (erase_pair_false_or n G C m p h hAO hout hComp hm hp hgate hFalse)
  have hlen := eraseGate_gates_length n C m p hm
  unfold Circuit.size at hsize
  omega

lemma least_every_gate_pair_true (n : ℕ) (hn : 0 < n)
    (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (hEdge : ∃ u v : Fin n, G.Adj u v)
    (C : Circuit) (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hComp : ∀ v : Fin n → Bool, C.eval (List.ofFn v) = graphFun G ∅ v)
    (hmin : ∀ D : Circuit, IsAO2 n D →
      (∀ v : Fin n → Bool, D.eval (List.ofFn v) = C.eval (List.ofFn v)) →
      C.size ≤ D.size) :
    ∀ m < C.gates.length, ∃ u v : Fin n, G.Adj u v ∧
      (C.wires (List.ofFn (pairInput u v))).getD (n + m) false = true := by
  have haux : ∀ d : ℕ, ∀ m < C.gates.length, C.gates.length - m = d →
      ∃ u v : Fin n, G.Adj u v ∧
        (C.wires (List.ofFn (pairInput u v))).getD (n + m) false = true := by
    intro d
    induction d using Nat.strongRecOn with
    | ind d ih =>
      intro m hm hdm
      rcases least_every_gate_used n hn C hAO hout hmin m hm with hOut | hUsed
      · obtain ⟨u, v, huv⟩ := hEdge
        refine ⟨u, v, huv, ?_⟩
        have htrue := (hComp (pairInput u v)).trans (graphFun_pair_true n G u v huv)
        simpa only [Circuit.eval, hOut] using htrue
      · obtain ⟨j, hj, hmj, hmem⟩ := hUsed
        obtain ⟨u, v, huv, htrue⟩ := ih (C.gates.length - j) (by omega) j hj rfl
        rcases hAO.1 _ (List.getElem_mem hj) with hop | hop
        · refine ⟨u, v, huv, ?_⟩
          rw [wires_getD_gate n C hAO.2.1 _ List.length_ofFn j hj, hop] at htrue
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at htrue
          exact htrue _ ⟨n + m, hmem, rfl⟩
        · obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hAO.2.2 _ (List.getElem_mem hj))
          have hgateVal : C.gates[j] = ⟨GateOp.or, [a, b]⟩ := by
            have heta : C.gates[j] = ⟨(C.gates[j]).op, (C.gates[j]).inputs⟩ := rfl
            rwa [hop, hab] at heta
          rw [hab] at hmem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
          have hback := hAO.2.1 j hj
          rw [gateAt_eq_getElem C j hj, hab] at hback
          rcases hmem with hma | hmb
          · have hb : b < n + j := hback b (by simp)
            apply least_or_operand_pair_true n G C hAO hout hComp hmin j b (n + m) hj hb
            right
            simpa [hj, ← hma] using congrArg some hgateVal
          · have ha : a < n + j := hback a (by simp)
            apply least_or_operand_pair_true n G C hAO hout hComp hmin j a (n + m) hj ha
            left
            simpa [hj, ← hmb] using congrArg some hgateVal
  intro m hm
  exact haux (C.gates.length - m) m hm rfl

end PEqualNP.Outside.L_meta_2583.PairUseful

namespace PEqualNP.Outside.L_meta_2583.AndErasure

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.Outside.L_meta_2583.Normalization

lemma eraseGate_wires_mono (n : ℕ) (C : Circuit) (m p : ℕ)
    (hAO : IsAO2 n C) (hm : m < C.gates.length) (hp : p < n + m)
    (x : List Bool) (hx : x.length = n)
    (hlocal : (C.wires x).getD (n + m) false = true →
      (C.wires x).getD p false = true) :
    ∀ k < n + (eraseGate n C m p).gates.length,
      (C.wires x).getD (if k < n + m then k else k + 1) false = true →
      ((eraseGate n C m p).wires x).getD k false = true := by
  have hEAO := eraseGate_isAO2 n C m p hAO hm hp
  have hElen := eraseGate_gates_length n C m p hm
  intro k
  induction k using Nat.strongRecOn with
  | ind k ih =>
    intro hk htrue
    by_cases hkm : k < n + m
    · simp only [hkm, ↓reduceIte] at htrue
      rwa [eraseGate_wires_prefix n C m p hm x hx k hkm]
    · simp only [hkm, ↓reduceIte] at htrue
      set j := k - n
      have hkj : k = n + j := by omega
      have hmj : m ≤ j := by omega
      have hjE : j < (eraseGate n C m p).gates.length := by omega
      have hjC : j + 1 < C.gates.length := by omega
      rw [hkj] at htrue ⊢
      have hkj1 : n + j + 1 = n + (j + 1) := by omega
      rw [hkj1] at htrue
      rw [wires_getD_gate n C hAO.2.1 x hx (j + 1) hjC] at htrue
      rw [wires_getD_gate n (eraseGate n C m p) hEAO.2.1 x hx j hjE]
      rw [eraseGate_getElem_ge n C m p j hm hmj hjE]
      rw [List.map_map]
      have hop : (C.gates[j + 1]).op = GateOp.and ∨ (C.gates[j + 1]).op = GateOp.or :=
        hAO.1 _ (List.getElem_mem hjC)
      refine gateOp_eval_mono _ hop _ _ _ ?_ htrue
      intro u hu huC
      have hu_lt : u < n + (j + 1) := by
        have := hAO.2.1 (j + 1) hjC u
        rw [gateAt_eq_getElem C (j + 1) hjC] at this
        exact this hu
      simp only [Function.comp_apply]
      unfold eraseRedirect
      split_ifs with heq hgt
      · rw [heq] at huC
        rw [eraseGate_wires_prefix n C m p hm x hx p hp]
        exact hlocal huC
      · have hnotlt : ¬ (u - 1 < n + m) := by omega
        apply ih (u - 1) (by omega) (by omega)
        simpa only [hnotlt, ↓reduceIte, Nat.sub_add_cancel (by omega : 1 ≤ u)] using huC
      · have hult : u < n + m := by omega
        rwa [eraseGate_wires_prefix n C m p hm x hx u hult]

lemma eraseGate_wires_eq (n : ℕ) (C : Circuit) (m p : ℕ)
    (hAO : IsAO2 n C) (hm : m < C.gates.length) (hp : p < n + m)
    (x : List Bool) (hx : x.length = n)
    (hlocal : (C.wires x).getD (n + m) false = (C.wires x).getD p false) :
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
      · rw [heq, hlocal]
        exact eraseGate_wires_prefix n C m p hm x hx p hp
      · have hstep := ih (u - 1) (by omega) (by omega)
        have hnotlt : ¬ (u - 1 < n + m) := by omega
        simp only [hnotlt, ↓reduceIte] at hstep
        have hu1 : u - 1 + 1 = u := by omega
        rwa [hu1] at hstep
      · have hult : u < n + m := by omega
        exact eraseGate_wires_prefix n C m p hm x hx u hult

lemma gate_m_and_val (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hRB : ReadsBack n C) (hm : m < C.gates.length)
    (hgate : C.gates[m]? = some ⟨GateOp.and, [p, h]⟩ ∨
      C.gates[m]? = some ⟨GateOp.and, [h, p]⟩)
    (x : List Bool) (hx : x.length = n) :
    (C.wires x).getD (n + m) false =
      ((C.wires x).getD p false && (C.wires x).getD h false) := by
  rw [wires_getD_gate n C hRB x hx m hm]
  have hg : C.gates[m] = ⟨GateOp.and, [p, h]⟩ ∨
      C.gates[m] = ⟨GateOp.and, [h, p]⟩ := by
    rcases hgate with h1 | h1
    · left; simpa [hm] using h1
    · right; simpa [hm] using h1
  rcases hg with h1 | h1
  · rw [h1]; simp [GateOp.eval]
  · rw [h1]; simp [GateOp.eval, Bool.and_comm]

lemma erase_and_eval_eq (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hm : m < C.gates.length) (hp : p < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.and, [p, h]⟩ ∨
      C.gates[m]? = some ⟨GateOp.and, [h, p]⟩)
    (hBelowP : WireBelowOutput n C p) (v : Fin n → Bool) :
    (eraseGate n C m p).eval (List.ofFn v) = C.eval (List.ofFn v) := by
  have hx : (List.ofFn v).length = n := List.length_ofFn
  have hEout : (eraseGate n C m p).output = eraseRedirect n m p C.output := by
    simp [eraseGate, hm]
  have hElen := eraseGate_gates_length n C m p hm
  cases hb : C.eval (List.ofFn v)
  · have hpfalse : (C.wires (List.ofFn v)).getD p false = false := by
      cases hpv : (C.wires (List.ofFn v)).getD p false
      · rfl
      · have := hBelowP v hpv
        rw [hb] at this
        contradiction
    have hlocal : (C.wires (List.ofFn v)).getD (n + m) false =
        (C.wires (List.ofFn v)).getD p false := by
      rw [gate_m_and_val n C m p h hAO.2.1 hm hgate (List.ofFn v) hx, hpfalse]
      rfl
    have heval : (eraseGate n C m p).eval (List.ofFn v) = C.eval (List.ofFn v) := by
      unfold Circuit.eval
      rw [hEout]
      unfold eraseRedirect
      split_ifs with heq hgt
      · rw [heq, hlocal]
        exact eraseGate_wires_prefix n C m p hm (List.ofFn v) hx p hp
      · have hstep := eraseGate_wires_eq n C m p hAO hm hp (List.ofFn v) hx
          hlocal (C.output - 1) (by omega)
        have hnotlt : ¬ (C.output - 1 < n + m) := by omega
        simp only [hnotlt, ↓reduceIte] at hstep
        have ho1 : C.output - 1 + 1 = C.output := by omega
        rwa [ho1] at hstep
      · have holt : C.output < n + m := by omega
        exact eraseGate_wires_prefix n C m p hm (List.ofFn v) hx C.output holt
    exact heval.trans hb
  · have hlocal : (C.wires (List.ofFn v)).getD (n + m) false = true →
        (C.wires (List.ofFn v)).getD p false = true := by
      rw [gate_m_and_val n C m p h hAO.2.1 hm hgate (List.ofFn v) hx]
      intro ht
      simpa using (Bool.and_eq_true_iff.mp ht).1
    unfold Circuit.eval at hb ⊢
    rw [hEout]
    unfold eraseRedirect
    split_ifs with heq hgt
    · rw [heq] at hb
      rw [eraseGate_wires_prefix n C m p hm (List.ofFn v) hx p hp]
      exact hlocal hb
    · apply eraseGate_wires_mono n C m p hAO hm hp (List.ofFn v) hx hlocal
        (C.output - 1) (by omega)
      have hnotlt : ¬ (C.output - 1 < n + m) := by omega
      simpa only [hnotlt, ↓reduceIte,
        Nat.sub_add_cancel (by omega : 1 ≤ C.output)] using hb
    · have holt : C.output < n + m := by omega
      rwa [eraseGate_wires_prefix n C m p hm (List.ofFn v) hx C.output holt]

lemma least_and_not_below (n : ℕ) (C : Circuit)
    (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hmin : ∀ D : Circuit, IsAO2 n D →
      (∀ v : Fin n → Bool, D.eval (List.ofFn v) = C.eval (List.ofFn v)) →
      C.size ≤ D.size)
    (m p h : ℕ) (hm : m < C.gates.length) (hp : p < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.and, [p, h]⟩ ∨
      C.gates[m]? = some ⟨GateOp.and, [h, p]⟩) :
    ¬ WireBelowOutput n C p := by
  intro hBelow
  have hsize := hmin (eraseGate n C m p) (eraseGate_isAO2 n C m p hAO hm hp)
    (erase_and_eval_eq n C m p h hAO hout hm hp hgate hBelow)
  have hlen := eraseGate_gates_length n C m p hm
  unfold Circuit.size at hsize
  omega

end PEqualNP.Outside.L_meta_2583.AndErasure

namespace PEqualNP.Outside.L_meta_2583.OrStrict

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.Outside.L_meta_2583.Normalization
  PEqualNP.Outside.L_meta_2583.PairUseful
  PEqualNP.Outside.L_meta_2583.AndErasure

lemma erase_eval_eq_of_gate_eq (n : ℕ) (C : Circuit) (m p : ℕ)
    (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hm : m < C.gates.length) (hp : p < n + m) (v : Fin n → Bool)
    (hlocal : (C.wires (List.ofFn v)).getD (n + m) false =
      (C.wires (List.ofFn v)).getD p false) :
    (eraseGate n C m p).eval (List.ofFn v) = C.eval (List.ofFn v) := by
  have hx : (List.ofFn v).length = n := List.length_ofFn
  have hEout : (eraseGate n C m p).output = eraseRedirect n m p C.output := by
    simp [eraseGate, hm]
  have hElen := eraseGate_gates_length n C m p hm
  unfold Circuit.eval
  rw [hEout]
  unfold eraseRedirect
  split_ifs with heq hgt
  · rw [heq, hlocal]
    exact eraseGate_wires_prefix n C m p hm (List.ofFn v) hx p hp
  · have hstep := eraseGate_wires_eq n C m p hAO hm hp
      (List.ofFn v) hx hlocal (C.output - 1) (by omega)
    have hnotlt : ¬ (C.output - 1 < n + m) := by omega
    simp only [hnotlt, ↓reduceIte] at hstep
    have ho1 : C.output - 1 + 1 = C.output := by omega
    rwa [ho1] at hstep
  · have holt : C.output < n + m := by omega
    exact eraseGate_wires_prefix n C m p hm (List.ofFn v) hx C.output holt

lemma erase_pair_dominated_or (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (m p h : ℕ) (hAO : IsAO2 n C)
    (hout : C.output < n + C.gates.length)
    (hComp : ∀ v : Fin n → Bool, C.eval (List.ofFn v) = graphFun G ∅ v)
    (hm : m < C.gates.length) (hp : p < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨
      C.gates[m]? = some ⟨GateOp.or, [h, p]⟩)
    (hImp : ∀ u v : Fin n, G.Adj u v →
      (C.wires (List.ofFn (pairInput u v))).getD h false = true →
      (C.wires (List.ofFn (pairInput u v))).getD p false = true) :
    ∀ v : Fin n → Bool, (eraseGate n C m p).eval (List.ofFn v) = C.eval (List.ofFn v) := by
  intro x
  cases hx : C.eval (List.ofFn x)
  · cases hE : (eraseGate n C m p).eval (List.ofFn x)
    · rfl
    · have := erase_or_eval_le n C m p h hAO hout hm hp hgate x hE
      rw [hx] at this
      contradiction
  · have hF : graphFun G ∅ x = true := (hComp x).symm.trans hx
    simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
      Bool.false_or, decide_eq_true_eq] at hF
    obtain ⟨u, v, huv, hxu, hxv⟩ := hF
    have hPair : C.eval (List.ofFn (pairInput u v)) = true :=
      (hComp _).trans (graphFun_pair_true n G u v huv)
    have hLocal : (C.wires (List.ofFn (pairInput u v))).getD (n + m) false =
        (C.wires (List.ofFn (pairInput u v))).getD p false := by
      rw [gate_m_val n C m p h hAO.2.1 hm hgate _ List.length_ofFn]
      cases hh : (C.wires (List.ofFn (pairInput u v))).getD h false
      · simp
      · rw [hImp u v huv hh]
        rfl
    have hPairE : (eraseGate n C m p).eval (List.ofFn (pairInput u v)) = true :=
      (erase_eval_eq_of_gate_eq n C m p hAO hout hm hp (pairInput u v) hLocal).trans hPair
    apply wire_mono n (eraseGate n C m p) (eraseGate_isAO2 n C m p hAO hm hp)
      (pairInput u v) x ?_ _ (eraseGate_output_lt n C m p hm hp hout) hPairE
    intro i hi
    simp only [pairInput, decide_eq_true_eq] at hi
    rcases hi with rfl | rfl
    · exact hxu
    · exact hxv

lemma least_or_operand_pair_strict (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hComp : ∀ v : Fin n → Bool, C.eval (List.ofFn v) = graphFun G ∅ v)
    (hmin : ∀ D : Circuit, IsAO2 n D →
      (∀ v : Fin n → Bool, D.eval (List.ofFn v) = C.eval (List.ofFn v)) →
      C.size ≤ D.size)
    (m p h : ℕ) (hm : m < C.gates.length) (hp : p < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨
      C.gates[m]? = some ⟨GateOp.or, [h, p]⟩) :
    ∃ u v : Fin n, G.Adj u v ∧
      (C.wires (List.ofFn (pairInput u v))).getD h false = true ∧
      (C.wires (List.ofFn (pairInput u v))).getD p false = false := by
  classical
  by_contra hbad
  have hImp : ∀ u v : Fin n, G.Adj u v →
      (C.wires (List.ofFn (pairInput u v))).getD h false = true →
      (C.wires (List.ofFn (pairInput u v))).getD p false = true := by
    intro u v huv hh
    cases hp : (C.wires (List.ofFn (pairInput u v))).getD p false
    · exact False.elim (hbad ⟨u, v, huv, hh, hp⟩)
    · rfl
  have hsize := hmin (eraseGate n C m p) (eraseGate_isAO2 n C m p hAO hm hp)
    (erase_pair_dominated_or n G C m p h hAO hout hComp hm hp hgate hImp)
  have hlen := eraseGate_gates_length n C m p hm
  unfold Circuit.size at hsize
  omega

end PEqualNP.Outside.L_meta_2583.OrStrict

namespace PEqualNP.Outside.L_meta_2583.Pivotal

open PEqualNP.CircuitLowerBounds PEqualNP.CircuitMoves PEqualNP.TopForm
  PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.Outside.L_meta_2583.Normalization
  PEqualNP.Outside.L_meta_2583.PairUseful
  PEqualNP.Outside.L_meta_2583.AndErasure
  PEqualNP.Outside.L_meta_2583.OrStrict

lemma least_erase_changes_output (n : ℕ) (C : Circuit)
    (hAO : IsAO2 n C)
    (hmin : ∀ D : Circuit, IsAO2 n D →
      (∀ v : Fin n → Bool, D.eval (List.ofFn v) = C.eval (List.ofFn v)) →
      C.size ≤ D.size)
    (m p : ℕ) (hm : m < C.gates.length) (hp : p < n + m) :
    ∃ v : Fin n → Bool, (eraseGate n C m p).eval (List.ofFn v) ≠ C.eval (List.ofFn v) := by
  classical
  by_contra! h
  have hsize := hmin (eraseGate n C m p) (eraseGate_isAO2 n C m p hAO hm hp) h
  have hlen := eraseGate_gates_length n C m p hm
  unfold Circuit.size at hsize
  omega

lemma least_or_pivotal_edge (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hComp : ∀ v : Fin n → Bool, C.eval (List.ofFn v) = graphFun G ∅ v)
    (hmin : ∀ D : Circuit, IsAO2 n D →
      (∀ v : Fin n → Bool, D.eval (List.ofFn v) = C.eval (List.ofFn v)) →
      C.size ≤ D.size)
    (m p h : ℕ) (hm : m < C.gates.length) (hp : p < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.or, [p, h]⟩ ∨
      C.gates[m]? = some ⟨GateOp.or, [h, p]⟩) :
    ∃ u v : Fin n, G.Adj u v ∧
      (eraseGate n C m p).eval (List.ofFn (pairInput u v)) = false ∧
      (C.wires (List.ofFn (pairInput u v))).getD h false = true ∧
      (C.wires (List.ofFn (pairInput u v))).getD p false = false := by
  obtain ⟨x, hne⟩ := least_erase_changes_output n C hAO hmin m p hm hp
  have hle := erase_or_eval_le n C m p h hAO hout hm hp hgate x
  have hvals : (eraseGate n C m p).eval (List.ofFn x) = false ∧ C.eval (List.ofFn x) = true := by
    cases hE : (eraseGate n C m p).eval (List.ofFn x) <;>
      cases hC : C.eval (List.ofFn x) <;> simp_all
  have hF : graphFun G ∅ x = true := (hComp x).symm.trans hvals.2
  simp only [graphFun, Finset.notMem_empty, false_and, exists_false, decide_false,
    Bool.false_or, decide_eq_true_eq] at hF
  obtain ⟨u, v, huv, hxu, hxv⟩ := hF
  have hE : (eraseGate n C m p).eval (List.ofFn (pairInput u v)) = false := by
    cases he : (eraseGate n C m p).eval (List.ofFn (pairInput u v))
    · rfl
    · have hpos := wire_mono n (eraseGate n C m p) (eraseGate_isAO2 n C m p hAO hm hp)
        (pairInput u v) x (by
          intro i hi
          simp only [pairInput, decide_eq_true_eq] at hi
          rcases hi with rfl | rfl
          · exact hxu
          · exact hxv) _ (eraseGate_output_lt n C m p hm hp hout) he
      exact False.elim (Bool.noConfusion (hvals.1.symm.trans hpos))
  have hpair := (hComp (pairInput u v)).trans (graphFun_pair_true n G u v huv)
  have hlocal : (C.wires (List.ofFn (pairInput u v))).getD (n + m) false ≠
      (C.wires (List.ofFn (pairInput u v))).getD p false := by
    intro heq
    have ht := erase_eval_eq_of_gate_eq n C m p hAO hout hm hp (pairInput u v) heq
    rw [hE, hpair] at ht
    contradiction
  rw [gate_m_val n C m p h hAO.2.1 hm hgate _ List.length_ofFn] at hlocal
  refine ⟨u, v, huv, hE, ?_⟩
  cases hh : (C.wires (List.ofFn (pairInput u v))).getD h false <;>
    cases hpv : (C.wires (List.ofFn (pairInput u v))).getD p false <;> simp_all

lemma erase_and_eval_ge (n : ℕ) (C : Circuit) (m p h : ℕ)
    (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hm : m < C.gates.length) (hp : p < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.and, [p, h]⟩ ∨
      C.gates[m]? = some ⟨GateOp.and, [h, p]⟩) (v : Fin n → Bool) :
    C.eval (List.ofFn v) = true → (eraseGate n C m p).eval (List.ofFn v) = true := by
  intro hb
  have hx := List.length_ofFn (f := v)
  have hEout : (eraseGate n C m p).output = eraseRedirect n m p C.output := by
    simp [eraseGate, hm]
  have hElen := eraseGate_gates_length n C m p hm
  have hlocal : (C.wires (List.ofFn v)).getD (n + m) false = true →
      (C.wires (List.ofFn v)).getD p false = true := by
    rw [gate_m_and_val n C m p h hAO.2.1 hm hgate _ hx]
    intro ht
    exact (Bool.and_eq_true_iff.mp ht).1
  unfold Circuit.eval at hb ⊢
  rw [hEout]
  unfold eraseRedirect
  split_ifs with heq hgt
  · rw [heq] at hb
    rw [eraseGate_wires_prefix n C m p hm (List.ofFn v) hx p hp]
    exact hlocal hb
  · apply eraseGate_wires_mono n C m p hAO hm hp (List.ofFn v) hx hlocal
      (C.output - 1) (by omega)
    have hnotlt : ¬ (C.output - 1 < n + m) := by omega
    simpa only [hnotlt, ↓reduceIte,
      Nat.sub_add_cancel (by omega : 1 ≤ C.output)] using hb
  · have holt : C.output < n + m := by omega
    rwa [eraseGate_wires_prefix n C m p hm (List.ofFn v) hx C.output holt]

lemma least_and_pivotal_maximal_false (n : ℕ) (C : Circuit)
    (hAO : IsAO2 n C) (hout : C.output < n + C.gates.length)
    (hmin : ∀ D : Circuit, IsAO2 n D →
      (∀ v : Fin n → Bool, D.eval (List.ofFn v) = C.eval (List.ofFn v)) →
      C.size ≤ D.size)
    (m p h : ℕ) (hm : m < C.gates.length) (hp : p < n + m)
    (hgate : C.gates[m]? = some ⟨GateOp.and, [p, h]⟩ ∨
      C.gates[m]? = some ⟨GateOp.and, [h, p]⟩) :
    ∃ y : Fin n → Bool, Maximal (fun x : Fin n → Bool => C.eval (List.ofFn x) = false) y ∧
      (eraseGate n C m p).eval (List.ofFn y) = true ∧
      (C.wires (List.ofFn y)).getD p false = true ∧
      (C.wires (List.ofFn y)).getD h false = false := by
  classical
  obtain ⟨x, hne⟩ := least_erase_changes_output n C hAO hmin m p hm hp
  have hle := erase_and_eval_ge n C m p h hAO hout hm hp hgate x
  have hvals : (eraseGate n C m p).eval (List.ofFn x) = true ∧ C.eval (List.ofFn x) = false := by
    cases hE : (eraseGate n C m p).eval (List.ofFn x) <;>
      cases hC : C.eval (List.ofFn x) <;> simp_all
  obtain ⟨y, hxy, hmax⟩ := Finite.exists_le_maximal
    (p := fun z : Fin n → Bool => C.eval (List.ofFn z) = false) hvals.2
  have hY : (eraseGate n C m p).eval (List.ofFn y) = true := by
    apply wire_mono n (eraseGate n C m p) (eraseGate_isAO2 n C m p hAO hm hp) x y
      ?_ _ (eraseGate_output_lt n C m p hm hp hout) hvals.1
    intro i hi
    have h := hxy i
    cases hy : y i
    · rw [hi, hy] at h
      exact False.elim ((by decide : ¬ ((true : Bool) ≤ false)) h)
    · rfl
  have hlocal : (C.wires (List.ofFn y)).getD (n + m) false ≠
      (C.wires (List.ofFn y)).getD p false := by
    intro heq
    have ht := erase_eval_eq_of_gate_eq n C m p hAO hout hm hp y heq
    rw [hY, hmax.1] at ht
    contradiction
  rw [gate_m_and_val n C m p h hAO.2.1 hm hgate _ List.length_ofFn] at hlocal
  refine ⟨y, hmax, hY, ?_⟩
  cases hpv : (C.wires (List.ofFn y)).getD p false <;>
    cases hh : (C.wires (List.ofFn y)).getD h false <;> simp_all

end PEqualNP.Outside.L_meta_2583.Pivotal
