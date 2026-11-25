import MonoBase

namespace PEqualNP.Outside.L_meta_1884.NineCircuitFloor

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_2590.Mono18

def gateFn {R : Type} (w : List (Wire R)) (g : Gate) : Wire R :=
  fun r => g.op.eval (g.inputs.map (fun i => (w.getD i (fun _ => false)) r))

def runFn {R : Type} (gs : List Gate) (w : List (Wire R)) : List (Wire R) :=
  gs.foldl (fun a g => a ++ [gateFn a g]) w

lemma read_available {R : Type} (w bank : List (Wire R))
    (hw : ∀ a ∈ w, Available false bank a) (i : Nat) :
    Available false bank (w.getD i (fun _ => false)) := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact hw _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact Or.inr (Or.inl ⟨false, rfl⟩)

lemma gate_decompose {R : Type} (w bank : List (Wire R)) (g : Gate)
    (hw : ∀ a ∈ w, Available false bank a)
    (hg : (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) :
    ∃ op a b, gateFn w g = combine op a b ∧
      Available false bank a ∧ Available false bank b := by
  have hf : Available false bank (fun _ : R => false) := Or.inr (Or.inl ⟨false, rfl⟩)
  have ht : Available false bank (fun _ : R => true) := Or.inr (Or.inl ⟨true, rfl⟩)
  have hr := read_available w bank hw
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only at hop hlen
  rcases hop with rfl | rfl
  · cases ins with
    | nil => exact ⟨false, (fun _ => true), (fun _ => true), rfl, ht, ht⟩
    | cons i ins =>
      cases ins with
      | nil =>
        refine ⟨false, w.getD i (fun _ => false), (fun _ => true), ?_, hr i, ht⟩
        funext r
        simp [gateFn, combine, GateOp.eval]
      | cons j ins =>
        cases ins with
        | nil =>
          refine ⟨false, w.getD i (fun _ => false), w.getD j (fun _ => false), ?_, hr i, hr j⟩
          funext r
          simp [gateFn, combine, GateOp.eval]
        | cons k rest => simp at hlen
  · cases ins with
    | nil => exact ⟨true, (fun _ => false), (fun _ => false), rfl, hf, hf⟩
    | cons i ins =>
      cases ins with
      | nil =>
        refine ⟨true, w.getD i (fun _ => false), (fun _ => false), ?_, hr i, hf⟩
        funext r
        simp [gateFn, combine, GateOp.eval]
      | cons j ins =>
        cases ins with
        | nil =>
          refine ⟨true, w.getD i (fun _ => false), w.getD j (fun _ => false), ?_, hr i, hr j⟩
          funext r
          simp [gateFn, combine, GateOp.eval]
        | cons k rest => simp at hlen

lemma run_reachable {R : Type} (gs : List Gate) (w roots bank : List (Wire R)) (p : Nat)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (hr : Reach false roots p bank) (hw : ∀ a ∈ w, Available false bank a) :
    ∃ next, Reach false roots (p + gs.length) next ∧
      ∀ a ∈ runFn gs w, Available false next a := by
  induction gs generalizing w bank p with
  | nil => exact ⟨bank, by simpa using hr, hw⟩
  | cons g gs ih =>
    obtain ⟨op, a, b, heq, ha, hb⟩ := gate_decompose w bank g hw (hg g (by simp))
    have hr' := Reach.two op hr ha hb
    have hw' : ∀ v ∈ w ++ [gateFn w g], Available false (combine op a b :: bank) v := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact available_cons _ (hw v hv)
      · have hv' : v = gateFn w g := List.mem_singleton.mp hv
        rw [hv', heq]
        exact Or.inl (by simp)
    obtain ⟨next, hn, hs⟩ := ih (w ++ [gateFn w g]) (combine op a b :: bank) (p + 1)
      (fun g' hg' => hg g' (by simp [hg'])) hr' hw'
    refine ⟨next, ?_, hs⟩
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hn

lemma read_row {R : Type} (w : List (Wire R)) (r : R) (i : Nat) :
    (w.getD i (fun _ => false)) r = (w.map (fun a => a r)).getD i false := by
  exact (List.getD_map w (fun _ => false) (n := i) (fun a => a r)).symm

lemma run_rows {R : Type} (gs : List Gate) (w : List (Wire R)) (r : R) :
    (runFn gs w).map (fun a => a r) =
      gs.foldl (fun a g => a ++ [g.op.eval (g.inputs.map (fun i => a.getD i false))])
        (w.map (fun a => a r)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (runFn gs (w ++ [gateFn w g])).map (fun a => a r) = _
    rw [ih]
    simp only [List.foldl_cons, List.map_append, List.map_cons, List.map_nil, gateFn, read_row]

lemma root_rows (r : Row) :
    (inputs.map observe).map (fun a => a r) = List.ofFn (sample r) := by
  rw [sampled, List.map_map]
  rfl

theorem nine_circuit_floor (C : Circuit) (hmono : PEqualNP.MetaComplexity.Monotone2 C)
    (hcomputes : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = edge x) : 16 ≤ C.size := by
  have hg : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    intro g hm
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hmono g hm
  obtain ⟨bank, hr, hs⟩ := run_reachable C.gates (inputs.map observe) (inputs.map observe)
    (inputs.map observe) 0 hg Reach.start (fun a ha => Or.inl ha)
  have hout := read_available (runFn C.gates (inputs.map observe)) bank hs C.output
  have heq : (runFn C.gates (inputs.map observe)).getD C.output (fun _ => false) =
      observe graph := by
    funext r
    rw [read_row, run_rows, root_rows]
    change C.eval (List.ofFn (sample r)) = bit r graph
    rw [hcomputes, edge_table]
  rw [heq] at hout
  exact nineMonoFloor C.size bank (by simpa [Circuit.size] using hr) hout

end PEqualNP.Outside.L_meta_1884.NineCircuitFloor
