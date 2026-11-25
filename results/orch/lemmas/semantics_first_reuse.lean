import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

def searchEdge (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def searchBits (m : ℕ) (i : Fin 10) : Bool := m.testBit i.val

def andPairWitnesses : List (ℕ × ℕ) :=
  [(0, 0), (16, 17), (2, 3), (2, 3), (2, 3), (2, 3), (2, 3), (2, 3), (2, 3), (2, 3), (4, 6), (0, 0), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (1, 3), (2, 6), (8, 12), (0, 0), (2, 6), (2, 6), (2, 6), (2, 6), (2, 6), (2, 6), (2, 6), (4, 12), (4, 12), (16, 24), (0, 0), (4, 12), (4, 12), (4, 12), (4, 12), (4, 12), (4, 12), (8, 24), (1, 17), (1, 17), (1, 17), (0, 0), (1, 17), (1, 17), (1, 17), (1, 17), (1, 17), (128, 160), (1, 33), (1, 33), (1, 33), (1, 33), (0, 0), (1, 33), (1, 33), (1, 33), (1, 33), (2, 66), (256, 320), (2, 66), (2, 66), (2, 66), (2, 66), (0, 0), (2, 66), (2, 66), (2, 66), (4, 132), (4, 132), (32, 160), (4, 132), (4, 132), (4, 132), (4, 132), (0, 0), (4, 132), (4, 132), (8, 264), (8, 264), (8, 264), (32, 288), (8, 264), (8, 264), (8, 264), (8, 264), (0, 0), (8, 264), (16, 528), (16, 528), (16, 528), (16, 528), (64, 576), (16, 528), (16, 528), (16, 528), (16, 528), (0, 0)]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
lemma andPairWitnesses_sound :
    ∀ i j : Fin 10, i ≠ j →
      let p := andPairWitnesses.getD (10 * i.val + j.val) (0, 0)
      (∀ k : Fin 10, k ≠ i → searchBits p.1 k = searchBits p.2 k) ∧
      (searchBits p.1 i && searchBits p.1 j) =
        (searchBits p.2 i && searchBits p.2 j) ∧
      searchEdge (searchBits p.1) = false ∧ searchEdge (searchBits p.2) = true := by
  decide

def orPairWitnesses : List (ℕ × ℕ) :=
  [(0, 0), (2, 3), (20, 21), (10, 11), (16, 17), (32, 33), (80, 81), (130, 131), (258, 259), (514, 515), (1, 3), (0, 0), (4, 6), (9, 11), (20, 22), (36, 38), (64, 66), (129, 131), (257, 259), (513, 515), (9, 13), (2, 6), (0, 0), (8, 12), (18, 22), (34, 38), (72, 76), (128, 132), (258, 262), (514, 518), (5, 13), (18, 26), (4, 12), (0, 0), (16, 24), (36, 44), (68, 76), (144, 152), (256, 264), (516, 524), (1, 17), (10, 26), (5, 21), (8, 24), (0, 0), (40, 56), (65, 81), (129, 145), (257, 273), (512, 528), (1, 33), (130, 162), (5, 37), (9, 41), (144, 176), (0, 0), (65, 97), (128, 160), (256, 288), (513, 545), (257, 321), (2, 66), (260, 324), (10, 74), (18, 82), (34, 98), (0, 0), (130, 194), (256, 320), (512, 576), (5, 133), (34, 162), (4, 132), (40, 168), (20, 148), (32, 160), (68, 196), (0, 0), (260, 388), (512, 640), (9, 265), (10, 266), (36, 292), (8, 264), (48, 304), (32, 288), (64, 320), (136, 392), (0, 0), (520, 776), (65, 577), (18, 530), (20, 532), (72, 584), (16, 528), (48, 560), (64, 576), (128, 640), (272, 784), (0, 0)]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2000000 in
lemma orPairWitnesses_sound :
    ∀ i j : Fin 10, i ≠ j →
      let p := orPairWitnesses.getD (10 * i.val + j.val) (0, 0)
      (∀ k : Fin 10, k ≠ i → searchBits p.1 k = searchBits p.2 k) ∧
      (searchBits p.1 i || searchBits p.1 j) =
        (searchBits p.2 i || searchBits p.2 j) ∧
      searchEdge (searchBits p.1) = false ∧ searchEdge (searchBits p.2) = true := by
  decide

open PEqualNP.CircuitLowerBounds

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)]

lemma append_agree_except (i : ℕ) (w v : List Bool) (z : Bool)
    (hlen : w.length = v.length)
    (heq : ∀ j, j ≠ i → w.getD j false = v.getD j false) :
    ∀ j, j ≠ i → (w ++ [z]).getD j false = (v ++ [z]).getD j false := by
  intro j hji
  by_cases hj : j < w.length
  · rw [List.getD_append _ _ _ _ hj, List.getD_append _ _ _ _ (by omega)]
    exact heq j hji
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by omega), hlen]

lemma run_agree_except (i : ℕ) (gs : List Gate) (w v : List Bool)
    (hlen : w.length = v.length)
    (heq : ∀ j, j ≠ i → w.getD j false = v.getD j false)
    (hnoread : ∀ g ∈ gs, i ∉ g.inputs) :
    ∀ j, j ≠ i → (gs.foldl wireStep w).getD j false = (gs.foldl wireStep v).getD j false := by
  induction gs generalizing w v with
  | nil => exact heq
  | cons g gs ih =>
      have he : g.inputs.map (fun j => w.getD j false) =
          g.inputs.map (fun j => v.getD j false) := by
        apply List.map_congr_left
        intro j hj
        apply heq
        intro hji
        exact hnoread g (by simp) (hji ▸ hj)
      simp only [List.foldl_cons]
      apply ih
      · simp [wireStep, hlen]
      · unfold wireStep
        rw [he]
        exact append_agree_except i w v _ hlen heq
      · intro g' hg'
        exact hnoread g' (by simp [hg'])

lemma run_input_read (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < w.length) :
    (gs.foldl wireStep w).getD j false = w.getD j false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
      simp only [List.foldl_cons]
      rw [ih _ (by simp [wireStep]; omega)]
      exact List.getD_append _ _ _ _ hj

lemma ofFn_agree_except {n : ℕ} (i : Fin n) (x y : Fin n → Bool)
    (heq : ∀ j : Fin n, j ≠ i → x j = y j) :
    ∀ j, j ≠ i.val → (List.ofFn x).getD j false = (List.ofFn y).getD j false := by
  intro j hji
  by_cases hj : j < n
  · simpa [List.getD_eq_getElem?_getD, hj] using
      heq ⟨j, hj⟩ (fun e => hji (congrArg Fin.val e))
  · rw [List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]

lemma ofFn_read {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt,
    dite_true, Option.getD_some]

lemma coordinate_not_target (C : Circuit)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = searchEdge x)
    (i : Fin 10) : C.output ≠ i.val := by
  intro hi
  let x : Fin 10 → Bool := fun j => decide (j = i)
  have hv : C.eval (List.ofFn x) = true := by
    unfold Circuit.eval Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD C.output false = true
    rw [hi, run_input_read _ _ _ (by simp)]
    rw [ofFn_read]
    simp [x]
  have hz : ∀ j : Fin 10, searchEdge (fun k => decide (k = j)) = false := by decide
  have ht := computes x
  rw [hv, hz i] at ht
  exact Bool.noConfusion ht

lemma primary_pair_witnesses (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (i j : Fin 10) (hij : i ≠ j) :
    ∃ x y : Fin 10 → Bool,
      (∀ k, k ≠ i → x k = y k) ∧
      op.eval [x i, x j] = op.eval [y i, y j] ∧
      searchEdge x = false ∧ searchEdge y = true := by
  rcases hop with rfl | rfl
  · have h := andPairWitnesses_sound i j hij
    exact ⟨_, _, h.1, by simpa [GateOp.eval] using h.2.1, h.2.2⟩
  · have h := orPairWitnesses_sound i j hij
    exact ⟨_, _, h.1, by simpa [GateOp.eval] using h.2.1, h.2.2⟩

lemma first_binary_reuses_input (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (i j : Fin 10) (hij : i ≠ j)
    (tail : List Gate) (output : ℕ)
    (computes : ∀ x : Fin 10 → Bool,
      (Circuit.mk (Gate.mk op [i.val, j.val] :: tail) output).eval (List.ofFn x) = searchEdge x) :
    ∃ g ∈ tail, i.val ∈ g.inputs := by
  by_contra! hnoread
  let C := Circuit.mk (Gate.mk op [i.val, j.val] :: tail) output
  have hout : output ≠ i.val := coordinate_not_target C computes i
  obtain ⟨x, y, hagree, hgate, hx, hy⟩ := primary_pair_witnesses op hop i j hij
  have ha := ofFn_agree_except i x y hagree
  have he : op.eval (([i.val, j.val] : List ℕ).map (fun k => (List.ofFn x).getD k false)) =
      op.eval (([i.val, j.val] : List ℕ).map (fun k => (List.ofFn y).getD k false)) := by
    simpa only [List.map_cons, List.map_nil, ofFn_read] using hgate
  have hs : ∀ k, k ≠ i.val →
      (wireStep (List.ofFn x) ⟨op, [i.val, j.val]⟩).getD k false =
      (wireStep (List.ofFn y) ⟨op, [i.val, j.val]⟩).getD k false := by
    unfold wireStep
    rw [he]
    exact append_agree_except i.val _ _ _ (by simp) ha
  have houtEq := run_agree_except i.val tail _ _
    (by simp [wireStep]) hs hnoread output hout
  change C.eval (List.ofFn x) = C.eval (List.ofFn y) at houtEq
  rw [computes x, computes y, hx, hy] at houtEq
  exact Bool.noConfusion houtEq

end PEqualNP.Outside.L_meta_2592_aux

