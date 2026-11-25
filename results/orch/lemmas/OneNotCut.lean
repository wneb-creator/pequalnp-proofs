import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.OneNotCut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

lemma fold_len (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, step]; omega

lemma split_last (l : List Gate) (h : ∃ g ∈ l, g.op = GateOp.not) :
    ∃ pre g suf, l = pre ++ g :: suf ∧ g.op = GateOp.not ∧
      ∀ q ∈ suf, q.op ≠ GateOp.not := by
  classical
  induction l with
  | nil => obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons a l ih =>
    by_cases h' : ∃ g ∈ l, g.op = GateOp.not
    · obtain ⟨pre, g, suf, h1, h2, h3⟩ := ih h'
      exact ⟨a :: pre, g, suf, by rw [h1]; rfl, h2, h3⟩
    · push_neg at h'
      obtain ⟨g, hg, hn⟩ := h
      rcases List.mem_cons.1 hg with rfl | hg
      · exact ⟨[], g, l, rfl, hn, h'⟩
      · exact absurd hn (h' g hg)

lemma split_one (C : Circuit) (hn : PEqualNP.NotBracket.notCount C = 1) :
    ∃ pre g suf, C.gates = pre ++ g :: suf ∧ g.op = GateOp.not ∧
      (∀ q ∈ pre, q.op ≠ GateOp.not) ∧ (∀ q ∈ suf, q.op ≠ GateOp.not) := by
  let _ : DecidableEq GateOp := lineDegreeGateOpDecEq
  change (C.gates.filter fun g => decide (g.op = GateOp.not)).length = 1 at hn
  have hhas : ∃ g ∈ C.gates, g.op = GateOp.not := by
    cases he : C.gates.filter (fun g => decide (g.op = GateOp.not)) with
    | nil => simp [he] at hn
    | cons g gs =>
      have hmem : g ∈ C.gates.filter (fun q => decide (q.op = GateOp.not)) := by
        rw [he]
        exact List.mem_cons_self
      obtain ⟨hg, hop⟩ := List.mem_filter.mp hmem
      exact ⟨g, hg, of_decide_eq_true hop⟩
  obtain ⟨pre, g, suf, he, hg, hs⟩ := split_last C.gates hhas
  refine ⟨pre, g, suf, he, hg, ?_, hs⟩
  have hlen : (pre.filter fun q => decide (q.op = GateOp.not)).length = 0 := by
    rw [he] at hn
    simp only [List.filter_append, List.filter_cons, hg, decide_true, if_true,
      List.length_append, List.length_cons] at hn
    omega
  have hempty := List.length_eq_zero_iff.mp hlen
  intro q hq hnot
  have hmem : q ∈ pre.filter (fun a => decide (a.op = GateOp.not)) := by
    simp [hq, hnot]
  rw [hempty] at hmem
  cases hmem

lemma replace_middle (pre suf : List Gate) (g : Gate) (b : Bool) :
    PEqualNP.NotPremium.replaceByConst (pre ++ g :: suf) pre.length b =
      pre ++ PEqualNP.NotPremium.constGate b :: suf := by
  change (pre ++ g :: suf).set pre.length (PEqualNP.NotPremium.constGate b) = _
  induction pre with
  | nil => rfl
  | cons a pre ih =>
    change a :: (pre ++ g :: suf).set pre.length (PEqualNP.NotPremium.constGate b) =
      a :: (pre ++ PEqualNP.NotPremium.constGate b :: suf)
    rw [ih]

lemma cut (n : ℕ) (C : Circuit) (hf : FanInTwo C)
    (hn : PEqualNP.NotBracket.notCount C = 1) :
    ∃ P Q : Circuit, Monotone2 P ∧ Monotone2 Q ∧
      P.size + Q.size + 1 = C.size ∧
      (∃ g : Gate, C.gates[P.size]? = some g ∧ g.op = GateOp.not) ∧
      (∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)])) ∧
      (∀ (b : Bool) (x : Fin n → Bool),
        (Circuit.mk (PEqualNP.NotPremium.replaceByConst C.gates P.size b)
          C.output).eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [b])) := by
  obtain ⟨pre, g, suf, he, hg, hp, hs⟩ := split_one C hn
  refine ⟨⟨pre, g.inputs.headD (n + pre.length)⟩, ⟨suf, C.output⟩,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    have ha' : a ∈ pre := ha
    obtain ⟨ho, hl⟩ := hf a (by rw [he]; simp [ha'])
    refine ⟨?_, hl⟩
    have := hp a ha'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
    tauto
  · intro a ha
    have ha' : a ∈ suf := ha
    obtain ⟨ho, hl⟩ := hf a (by rw [he]; simp [ha'])
    refine ⟨?_, hl⟩
    have := hs a ha'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ho ⊢
    tauto
  · simp [Circuit.size, he]; omega
  · exact ⟨g, by simp [Circuit.size, he], hg⟩
  · intro x
    simp only [Circuit.eval, wires_eq, he, List.foldl_append, List.foldl_cons]
    congr 2
    have hl : (List.foldl step (List.ofFn x) pre).length = n + pre.length := by
      rw [fold_len]
      simp
    generalize List.foldl step (List.ofFn x) pre = W at hl
    simp only [step, hg]
    congr 2
    rcases g.inputs with _ | ⟨a, t⟩
    · simp [GateOp.eval, List.getD_eq_getElem?_getD, List.getElem?_eq_none, hl]
    · simp [GateOp.eval]
  · intro b x
    simp only [Circuit.size, he, replace_middle, Circuit.eval, wires_eq,
      List.foldl_append, List.foldl_cons]
    cases b <;> rfl

end PEqualNP.Outside.L_meta_2592_aux.OneNotCut
