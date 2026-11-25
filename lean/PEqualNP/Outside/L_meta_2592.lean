import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592

def petersenEdges : Finset (Fin 10 × Fin 10) :=
  {(0, 1), (1, 2), (2, 3), (3, 4), (0, 4), (0, 5), (1, 6), (2, 7),
    (3, 8), (4, 9), (5, 7), (7, 9), (6, 9), (6, 8), (5, 8)}

def petersenValue (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
    x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
    x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def petersenSupport (x : Fin 10 → Bool) : Finset (Fin 10) :=
  Finset.univ.filter (fun i => x i = true)

def petersenAdjacent (i j : Fin 10) : Prop :=
  (i, j) ∈ petersenEdges ∨ (j, i) ∈ petersenEdges

def petersenNeighbor (i : Fin 10) : Fin 10 :=
  match i.val with
  | 0 => 1
  | 1 => 0
  | 2 => 1
  | 3 => 2
  | 4 => 0
  | 5 => 0
  | 6 => 1
  | 7 => 2
  | 8 => 3
  | _ => 4

lemma petersen_edge_count : petersenEdges.card = 15 := by decide

set_option synthInstance.maxSize 100000 in
lemma petersen_triangle_free :
    ∀ a b c : Fin 10,
      petersenAdjacent a b → petersenAdjacent b c → ¬petersenAdjacent c a := by
  unfold petersenAdjacent
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
set_option synthInstance.maxSize 100000 in
lemma petersen_square_free :
    ∀ a b c d : Fin 10, a ≠ c → b ≠ d →
      petersenAdjacent a b → petersenAdjacent b c →
      petersenAdjacent c d → ¬petersenAdjacent d a := by
  unfold petersenAdjacent
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma petersen_independent_set_bound :
    ∀ x : Fin 10 → Bool, petersenValue x = false → (petersenSupport x).card ≤ 4 := by
  decide

lemma petersen_independent_set_witness :
    let x : Fin 10 → Bool := fun i => decide (i ∈ ({0, 2, 8, 9} : Finset (Fin 10)))
    petersenValue x = false ∧ (petersenSupport x).card = 4 := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma petersen_vertex_cover_bound :
    ∀ x : Fin 10 → Bool,
      (∀ p ∈ petersenEdges, x p.1 || x p.2 = true) → 6 ≤ (petersenSupport x).card := by
  decide

lemma petersen_star_cover_cost (x : Fin 10 → Bool)
    (h : ∀ p ∈ petersenEdges, x p.1 || x p.2 = true) :
    20 ≤ petersenEdges.card + (petersenSupport x).card - 1 := by
  have hc := petersen_vertex_cover_bound x h
  rw [petersen_edge_count]
  omega

lemma petersen_essential_witnesses :
    ∀ i : Fin 10,
      petersenValue (fun j => decide (j = petersenNeighbor i)) = false ∧
      petersenValue (fun j => decide (j = petersenNeighbor i ∨ j = i)) = true := by
  decide

lemma petersen_all_inputs_essential (i : Fin 10) :
    ∃ x y : Fin 10 → Bool,
      (∀ j, j ≠ i → x j = y j) ∧ petersenValue x ≠ petersenValue y := by
  refine ⟨fun j => decide (j = petersenNeighbor i),
    fun j => decide (j = petersenNeighbor i ∨ j = i), ?_, ?_⟩
  · intro j h
    simp only [h, or_false]
  · rw [(petersen_essential_witnesses i).1, (petersen_essential_witnesses i).2]
    decide

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma split_last_not {gs : List Gate}
    (h : ∃ g ∈ gs, g.op = GateOp.not) :
    ∃ pre g post, gs = pre ++ g :: post ∧ g.op = GateOp.not ∧
      ∀ q ∈ post, q.op ≠ GateOp.not := by
  induction gs with
  | nil => simp at h
  | cons a gs ih =>
    by_cases ht : ∃ g ∈ gs, g.op = GateOp.not
    · obtain ⟨pre, g, post, heq, hg, hpost⟩ := ih ht
      refine ⟨a :: pre, g, post, ?_, hg, hpost⟩
      simp only [List.cons_append, heq]
    · refine ⟨[], a, gs, rfl, ?_, ?_⟩
      · obtain ⟨g, hm, hg⟩ := h
        rcases List.mem_cons.mp hm with ha | hm
        · simpa [ha] using hg
        · exact (ht ⟨g, hm, hg⟩).elim
      · intro q hq hop
        exact ht ⟨q, hq, hop⟩

lemma fold_wires_length (gs : List Gate) (w : List Bool) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).length =
      w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma cut_last_not (n : ℕ) (C : Circuit) (fan : FanInTwo C)
    (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ P Q : Circuit, FanInTwo P ∧ Monotone2 Q ∧ P.size + Q.size + 1 = C.size ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) := by
  obtain ⟨pre, g, post, heq, hg, hpost⟩ := split_last_not hasNot
  let P : Circuit := ⟨pre, g.inputs.headD (n + pre.length)⟩
  let Q : Circuit := ⟨post, C.output⟩
  refine ⟨P, Q, ?_, ?_, ?_, ?_⟩
  · intro a ha
    exact fan a (by rw [heq]; exact List.mem_append_left _ ha)
  · intro a ha
    have hf := fan a (by rw [heq]; exact List.mem_append_right _ (List.mem_cons_of_mem _ ha))
    refine ⟨?_, hf.2⟩
    have hn := hpost a ha
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hf ⊢
    rcases hf.1 with hand | hor | hnot
    · exact Or.inl hand
    · exact Or.inr hor
    · exact (hn hnot).elim
  · simp only [Circuit.size, P, Q, heq, List.length_append, List.length_cons]
    omega
  · intro x
    have hlen : (P.wires (List.ofFn x)).length = n + pre.length := by
      simp only [Circuit.wires, P, fold_wires_length, List.length_ofFn]
    have hgate : g.op.eval (g.inputs.map fun i =>
        (P.wires (List.ofFn x)).getD i false) = !P.eval (List.ofFn x) := by
      rw [hg]
      cases hi : g.inputs with
      | nil =>
        have hd : (P.wires (List.ofFn x)).getD (n + pre.length) false = false :=
          List.getD_eq_default _ _ (by rw [hlen])
        change GateOp.not.eval _ =
          !((P.wires (List.ofFn x)).getD (g.inputs.headD (n + pre.length)) false)
        simp only [hi, List.map_nil, GateOp.eval, List.headD_nil, hd, Bool.not_false]
      | cons i is => simp [GateOp.eval, Circuit.eval, P, hi]
    change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (List.ofFn x)).getD C.output false = _
    rw [heq, List.foldl_append, List.foldl_cons]
    change (post.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (P.wires (List.ofFn x) ++ [g.op.eval (g.inputs.map fun i =>
        (P.wires (List.ofFn x)).getD i false)])).getD C.output false = _
    rw [hgate]
    rfl

end PEqualNP.Outside.L_meta_2592
