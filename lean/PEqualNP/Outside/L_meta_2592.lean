import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma last_not_split (gs : List Gate) :
    (∃ g ∈ gs, g.op = GateOp.not) →
    ∃ (pre : List Gate) (g : Gate) (post : List Gate),
      gs = pre ++ g :: post ∧ g.op = GateOp.not ∧
      ∀ t ∈ post, t.op ≠ GateOp.not := by
  classical
  induction gs with
  | nil =>
    rintro ⟨g, hg, _⟩
    cases hg
  | cons a gs ih =>
    intro h
    by_cases ht : ∃ g ∈ gs, g.op = GateOp.not
    · obtain ⟨pre, g, post, heq, hnot, hpost⟩ := ih ht
      exact ⟨a :: pre, g, post, by simp [heq], hnot, hpost⟩
    · refine ⟨[], a, gs, rfl, ?_, ?_⟩
      · obtain ⟨g, hg, hn⟩ := h
        rcases List.mem_cons.mp hg with rfl | hg
        · exact hn
        · exact False.elim (ht ⟨g, hg, hn⟩)
      · intro t ht' hn
        exact ht ⟨t, ht', hn⟩

lemma run_length (gs : List Gate) (x : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, 0⟩ (x ++ [_])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma last_not_cut (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hnot : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ P Q : Circuit, FanInTwo P ∧ Monotone2 Q ∧
      P.size + Q.size + 1 = C.size ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) := by
  obtain ⟨pre, g, post, hsplit, hg, hpost⟩ := last_not_split C.gates hnot
  let P : Circuit := ⟨pre, g.inputs.headD (n + pre.length)⟩
  let Q : Circuit := ⟨post, C.output⟩
  have pre_mem (t : Gate) (ht : t ∈ pre) : t ∈ C.gates := by
    rw [hsplit]
    exact List.mem_append_left _ ht
  have post_mem (t : Gate) (ht : t ∈ post) : t ∈ C.gates := by
    rw [hsplit]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ ht)
  refine ⟨P, Q, ?_, ?_, ?_, ?_⟩
  · intro t ht
    exact hfan t (pre_mem t ht)
  · intro t ht
    obtain ⟨hop, hlen⟩ := hfan t (post_mem t ht)
    refine ⟨?_, hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    rcases hop with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · exact False.elim (hpost t ht hop)
  · change pre.length + post.length + 1 = C.gates.length
    rw [hsplit]
    simp only [List.length_append, List.length_cons]
    omega
  · intro x
    have hlen : (P.wires (List.ofFn x)).length = n + pre.length := by
      have h := run_length pre (List.ofFn x)
      simpa only [P, Circuit.wires, List.length_ofFn] using h
    have hvalue : g.op.eval (g.inputs.map fun i =>
        (P.wires (List.ofFn x)).getD i false) = !P.eval (List.ofFn x) := by
      rw [hg]
      cases hinputs : g.inputs with
      | nil =>
        change true = !((P.wires (List.ofFn x)).getD P.output false)
        have hout : P.output = n + pre.length := by simp [P, hinputs]
        rw [hout, ← hlen, List.getD_eq_default _ _ (by omega)]
        rfl
      | cons a rest =>
        change (!((P.wires (List.ofFn x)).getD a false)) =
          (!((P.wires (List.ofFn x)).getD P.output false))
        have hout : P.output = a := by simp [P, hinputs]
        rw [hout]
    change (C.gates.foldl _ (List.ofFn x)).getD C.output false = _
    rw [hsplit, List.foldl_append]
    change (post.foldl _ (P.wires (List.ofFn x) ++
      [g.op.eval (g.inputs.map fun i =>
        (P.wires (List.ofFn x)).getD i false)])).getD C.output false = _
    rw [hvalue]
    rfl

open PEqualNP.CircuitLowerBounds

def renameWire (n : ℕ) (p : Fin n → Fin n) (i : ℕ) : ℕ :=
  if h : i < n then p ⟨i, h⟩ else i

def renameGate (n : ℕ) (p : Fin n → Fin n) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (renameWire n p)⟩

def renameCircuit (n : ℕ) (p : Fin n → Fin n) (C : Circuit) : Circuit :=
  ⟨C.gates.map (renameGate n p), renameWire n p C.output⟩

def wireRelated (n : ℕ) (p : Fin n → Fin n) (w v : List Bool) : Prop :=
  ∀ i : ℕ, v.getD (renameWire n p i) false = w.getD i false

lemma related_ofFn (n : ℕ) (p : Fin n → Fin n) (x : Fin n → Bool) :
    wireRelated n p (List.ofFn (fun i => x (p i))) (List.ofFn x) := by
  intro i
  by_cases hi : i < n
  · simp [renameWire, hi]
  · simp only [renameWire, hi, dite_false]
    rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hi),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hi)]

lemma related_append (n : ℕ) (p : Fin n → Fin n) (w v : List Bool)
    (hr : wireRelated n p w v) (hl : w.length = v.length) (hn : n ≤ w.length) (b : Bool) :
    wireRelated n p (w ++ [b]) (v ++ [b]) := by
  intro i
  by_cases hi : i < w.length
  · have hj : renameWire n p i < v.length := by
      by_cases his : i < n
      · simp only [renameWire, his, dite_true]
        have := (p ⟨i, his⟩).isLt
        omega
      · simpa [renameWire, his, ← hl] using hi
    rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ hi]
    exact hr i
  · have his : ¬ i < n := by omega
    simp only [renameWire, his, dite_false]
    by_cases he : i = w.length
    · subst i
      calc
        (v ++ [b]).getD w.length false = b := by rw [hl]; simp
        _ = (w ++ [b]).getD w.length false := by simp
    · rw [List.getD_eq_default _ _ (by simp; omega),
          List.getD_eq_default _ _ (by simp; omega)]

lemma renamed_gate_value (n : ℕ) (p : Fin n → Fin n) (w v : List Bool)
    (hr : wireRelated n p w v) (g : Gate) :
    (renameGate n p g).op.eval ((renameGate n p g).inputs.map (fun i => v.getD i false)) =
      g.op.eval (g.inputs.map (fun i => w.getD i false)) := by
  simp only [renameGate, List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact hr i

lemma related_fold (n : ℕ) (p : Fin n → Fin n) (gs : List Gate) :
    ∀ w v : List Bool, wireRelated n p w v → w.length = v.length → n ≤ w.length →
    wireRelated n p
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w)
      ((gs.map (renameGate n p)).foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) v) := by
  induction gs with
  | nil => intro w v hr hl hn; exact hr
  | cons g gs ih =>
    intro w v hr hl hn
    simp only [List.map_cons, List.foldl_cons]
    rw [renamed_gate_value n p w v hr g]
    apply ih
    · exact related_append n p w v hr hl hn _
    · simpa using hl
    · simp only [List.length_append, List.length_singleton]
      omega

lemma renameCircuit_eval (n : ℕ) (p : Fin n → Fin n) (C : Circuit) (x : Fin n → Bool) :
    (renameCircuit n p C).eval (List.ofFn x) = C.eval (List.ofFn (fun i => x (p i))) := by
  exact related_fold n p C.gates _ _ (related_ofFn n p x) (by simp) (by simp) C.output

lemma renameCircuit_size (n : ℕ) (p : Fin n → Fin n) (C : Circuit) :
    (renameCircuit n p C).size = C.size := by
  simp [renameCircuit, Circuit.size]

lemma renameCircuit_fanin (n : ℕ) (p : Fin n → Fin n) (C : Circuit)
    (h : PEqualNP.MetaComplexity.FanInTwo C) :
    PEqualNP.MetaComplexity.FanInTwo (renameCircuit n p C) := by
  intro g hg
  change g ∈ C.gates.map (renameGate n p) at hg
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
  simpa [renameGate] using h q hq

lemma renameCircuit_has_not (n : ℕ) (p : Fin n → Fin n) (C : Circuit)
    (h : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ g ∈ (renameCircuit n p C).gates, g.op = GateOp.not := by
  obtain ⟨g, hg, hop⟩ := h
  exact ⟨renameGate n p g, List.mem_map.mpr ⟨g, hg, rfl⟩, hop⟩

end PEqualNP.Outside.L_meta_2592
