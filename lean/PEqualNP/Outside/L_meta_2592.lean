import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def trimNot (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma trimNot_op (g : Gate) : (trimNot g).op = g.op := by
  cases g with
  | mk op ins => cases op <;> rfl

lemma trimNot_eval (g : Gate) (w : ℕ → Bool) :
    (trimNot g).op.eval ((trimNot g).inputs.map w) = g.op.eval (g.inputs.map w) := by
  cases g with
  | mk op ins =>
    cases op <;> simp only [trimNot]
    cases ins <;> simp [GateOp.eval]

lemma trimNot_fanin (g : Gate) (h : g.inputs.length ≤ 2) :
    (trimNot g).inputs.length ≤ 2 := by
  cases g with
  | mk op ins =>
    cases op <;> simp_all [trimNot]

lemma trimNot_unary (g : Gate) (h : (trimNot g).op = GateOp.not) :
    (trimNot g).inputs.length ≤ 1 := by
  cases g with
  | mk op ins => cases op <;> simp_all [trimNot]

def trimNotCircuit (C : Circuit) : Circuit := ⟨C.gates.map trimNot, C.output⟩

lemma trimNotCircuit_fanin (C : Circuit) (h : FanInTwo C) :
    FanInTwo (trimNotCircuit C) := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
  exact ⟨by simpa only [trimNot_op] using (h a ha).1, trimNot_fanin a (h a ha).2⟩

lemma trimNotCircuit_size (C : Circuit) : (trimNotCircuit C).size = C.size :=
  List.length_map _

lemma trimNotCircuit_wires (C : Circuit) (w : List Bool) :
    (trimNotCircuit C).wires w = C.wires w := by
  cases C with
  | mk gs out =>
    change (gs.map trimNot).foldl _ w = gs.foldl _ w
    induction gs generalizing w with
    | nil => rfl
    | cons g gs ih =>
      simp only [List.map_cons, List.foldl_cons, trimNot_eval, ih]

lemma trimNotCircuit_eval (C : Circuit) (w : List Bool) :
    (trimNotCircuit C).eval w = C.eval w := by
  unfold Circuit.eval
  rw [trimNotCircuit_wires]
  rfl

lemma trimNotCircuit_hasNot (C : Circuit) :
    (∃ g ∈ (trimNotCircuit C).gates, g.op = GateOp.not) ↔
      ∃ g ∈ C.gates, g.op = GateOp.not := by
  constructor
  · rintro ⟨g, hg, hn⟩
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact ⟨a, ha, (trimNot_op a).symm.trans hn⟩
  · rintro ⟨g, hg, hn⟩
    exact ⟨trimNot g, List.mem_map.mpr ⟨g, hg, rfl⟩, (trimNot_op g).trans hn⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma split_last_not (gs : List Gate)
    (h : ∃ g ∈ gs, g.op = GateOp.not) :
    ∃ (pre post : List Gate) (ins : List ℕ),
      gs = pre ++ (⟨GateOp.not, ins⟩ : Gate) :: post ∧
      ∀ g ∈ post, g.op ≠ GateOp.not := by
  classical
  induction gs with
  | nil => simp at h
  | cons g gs ih =>
    by_cases tail : ∃ t ∈ gs, t.op = GateOp.not
    · obtain ⟨pre, post, ins, e, hn⟩ := ih tail
      exact ⟨g :: pre, post, ins, by simp only [List.cons_append, e], hn⟩
    · obtain ⟨t, ht, hop⟩ := h
      have e : t = g := by
        rcases List.mem_cons.mp ht with e | mem
        · exact e
        · exact (tail ⟨t, mem, hop⟩).elim
      subst t
      refine ⟨[], gs, g.inputs, ?_, ?_⟩
      · cases g with
        | mk op ins => simp only at hop; subst op; rfl
      · intro t ht hop
        exact tail ⟨t, ht, hop⟩

lemma wires_length (gs : List Gate) (w : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, 0⟩ (w ++ [_])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

lemma cutLast (n : ℕ) (C : Circuit) (fan : FanInTwo C)
    (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not) :
    ∃ P Q : Circuit, FanInTwo P ∧ Monotone2 Q ∧
      P.size + Q.size + 1 = C.size ∧
      ∀ x : Fin n → Bool, C.eval (List.ofFn x) =
        Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]) := by
  obtain ⟨pre, post, ins, split, noNot⟩ := split_last_not C.gates hasNot
  let P : Circuit := ⟨pre, ins.headD (n + pre.length)⟩
  let Q : Circuit := ⟨post, C.output⟩
  refine ⟨P, Q, ?_, ?_, ?_, ?_⟩
  · intro g hg
    apply fan g
    rw [split]
    exact List.mem_append_left _ hg
  · intro g hg
    obtain ⟨hop, hlen⟩ := fan g (by
      rw [split]
      exact List.mem_append_right _ (List.mem_cons_of_mem _ hg))
    refine ⟨?_, hlen⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop ⊢
    rcases hop with ha | ho | hn
    · exact Or.inl ha
    · exact Or.inr ho
    · exact (noNot g hg hn).elim
  · change pre.length + post.length + 1 = C.gates.length
    rw [split]
    simp only [List.length_append, List.length_cons]
    omega
  · intro x
    have operand :
        (ins.map fun i => (P.wires (List.ofFn x)).getD i false).headD false =
          P.eval (List.ofFn x) := by
      cases ins with
      | nil =>
        change false = (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD (n + pre.length) false
        rw [List.getD_eq_default _ _ (by rw [wires_length]; simp)]
      | cons i rest => rfl
    unfold Circuit.eval Circuit.wires
    rw [split, List.foldl_append]
    change (post.foldl _ (P.wires (List.ofFn x) ++
      [GateOp.not.eval (ins.map fun i => (P.wires (List.ofFn x)).getD i false)])).getD C.output false = _
    simp only [GateOp.eval, operand]
    rfl

def petersenEdges : List (Fin 10 × Fin 10) :=
  [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6),
   (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
lemma petersen_vertex_cover_lower : ∀ c : Fin 10 → Bool,
    (∀ e ∈ petersenEdges, c e.1 || c e.2 = true) →
    6 ≤ (List.ofFn c).count true := by
  decide

open PEqualNP.CircuitLowerBounds

def satEdgeFunction (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) ||
  (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) ||
  (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) ||
  (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma sat_dependency_witness :
    ∀ u v : Fin 10, u ≠ v → ∀ b : Bool, ∃ w : Fin 10,
      ∀ a : Bool,
        satEdgeFunction (fun i =>
          if i = u then a else if i = v then b else decide (i = w)) = a := by
  decide

lemma sat_cofactor_essential (u v : Fin 10) (huv : u ≠ v) (b : Bool) :
    ∃ x y : Fin 10 → Bool,
      (∀ i, i ≠ u → x i = y i) ∧ x v = b ∧ y v = b ∧
      satEdgeFunction x ≠ satEdgeFunction y := by
  obtain ⟨w, hw⟩ := sat_dependency_witness u v huv b
  refine ⟨(fun i => if i = u then false else if i = v then b else decide (i = w)),
    (fun i => if i = u then true else if i = v then b else decide (i = w)),
    ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp [hi]
  · simp [Ne.symm huv]
  · simp [Ne.symm huv]
  · rw [hw false, hw true]
    decide

def satStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma sat_fold_length (gs : List Gate) (x : List Bool) :
    (gs.foldl satStep x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp
  | cons g gs ih =>
    simp [List.foldl_cons, ih, satStep, Nat.add_comm, Nat.add_left_comm]

lemma sat_fold_getD (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (gs.foldl satStep x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    change (gs.foldl satStep (satStep x g)).getD i false = _
    rw [ih _ (by simp [satStep]; omega)]
    exact List.getD_append _ _ _ _ hi

lemma sat_eval_input (C : Circuit) (x : Fin 10 → Bool) (i : Fin 10)
    (output : C.output = i.val) : C.eval (List.ofFn x) = x i := by
  unfold Circuit.eval Circuit.wires
  change (C.gates.foldl satStep (List.ofFn x)).getD C.output false = x i
  rw [output, sat_fold_getD _ _ _ (by simp)]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, i.isLt, dif_pos,
    Option.getD_some]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma sat_edge_avoids :
    ∀ i : Fin 10, ∃ u v : Fin 10,
      (fun j : Fin 10 => decide (j = u ∨ j = v)) i = false ∧
      satEdgeFunction (fun j => decide (j = u ∨ j = v)) = true := by
  decide

lemma sat_output_bounds (C : Circuit)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = satEdgeFunction x) :
    10 ≤ C.output ∧ C.output < 10 + C.size := by
  constructor
  · by_contra! small
    let i : Fin 10 := ⟨C.output, small⟩
    obtain ⟨u, v, zero, one⟩ := sat_edge_avoids i
    let x : Fin 10 → Bool := fun j => decide (j = u ∨ j = v)
    have value : C.eval (List.ofFn x) = false := (sat_eval_input C x i rfl).trans zero
    have target : satEdgeFunction x = true := one
    have bad : false = true := value.symm.trans ((computes x).trans target)
    cases bad
  · by_contra! large
    let x : Fin 10 → Bool := fun j => decide (j = 0 ∨ j = 1)
    have target : satEdgeFunction x = true := by decide
    have length : (C.wires (List.ofFn x)).length = 10 + C.size := by
      change (C.gates.foldl satStep (List.ofFn x)).length = 10 + C.gates.length
      rw [sat_fold_length, List.length_ofFn]
    have value : C.eval (List.ofFn x) = false := by
      apply List.getD_eq_default
      omega
    have bad : false = true := value.symm.trans ((computes x).trans target)
    cases bad

namespace Endpoint

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_wiresStep_length (gs : List Gate) (w : List Bool) :
    (gs.foldl wiresStep w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wiresStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wiresStep_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length) :
    (gs.foldl wiresStep w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (wiresStep w g).length := by
      simp only [wiresStep, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [ih (wiresStep w g) hlt]
    simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_length (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma getD_append_last_eq (w : List Bool) (b : Bool) (m : ℕ) (hm : w.length = m) :
    (w ++ [b]).getD m false = b := by
  subst hm
  simp [List.getD_eq_getElem?_getD]

lemma getD_ofFn {m : ℕ} (x : Fin m → Bool) (i : ℕ) (hi : i < m) :
    (List.ofFn x).getD i false = x ⟨i, hi⟩ := by
  simp [List.getD_eq_getElem?_getD, hi]

lemma monotone_foldl_wiresStep (gs : List Gate)
    (hM : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (w1 w2 : List Bool) (hlen : w1.length = w2.length)
    (hle : ∀ k : ℕ, w1.getD k false = true → w2.getD k false = true) :
    ∀ k : ℕ, (gs.foldl wiresStep w1).getD k false = true →
      (gs.foldl wiresStep w2).getD k false = true := by
  induction gs generalizing w1 w2 with
  | nil => exact hle
  | cons g gs ih =>
    have hg : g.op = GateOp.and ∨ g.op = GateOp.or := by
      simpa using hM g List.mem_cons_self
    have hM' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) :=
      fun g' hg' => hM g' (List.mem_cons_of_mem g hg')
    apply ih hM' (wiresStep w1 g) (wiresStep w2 g)
    · simp only [wiresStep, List.length_append, List.length_cons, List.length_nil, hlen]
    · intro k hk
      by_cases hlt : k < w1.length
      · have hlt2 : k < w2.length := hlen ▸ hlt
        simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt] at hk
        simp only [wiresStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hlt2]
        exact hle k hk
      · by_cases heq : k = w1.length
        · subst heq
          have hk1 : g.op.eval (g.inputs.map fun i => w1.getD i false) = true := by
            simpa [wiresStep, getD_append_last_eq w1 _ w1.length rfl] using hk
          rw [wiresStep, getD_append_last_eq w2 _ w1.length hlen.symm]
          rcases hg with hand | hor
          · rw [hand] at hk1 ⊢
            simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq,
              forall_exists_index, and_imp, forall_apply_eq_imp_iff₂] at hk1 ⊢
            intro i hi
            exact hle i (hk1 i hi)
          · rw [hor] at hk1 ⊢
            simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hk1 ⊢
            obtain ⟨b, ⟨i, hi, rfl⟩, hbi⟩ := hk1
            exact ⟨true, ⟨i, hi, hle i hbi⟩, rfl⟩
        · have hge : (wiresStep w1 g).length ≤ k := by
            simp only [wiresStep, List.length_append, List.length_cons, List.length_nil]
            omega
          rw [getD_ge_length _ k hge] at hk
          cases hk


lemma getD_snoc_ne (w : List Bool) (b : Bool) (i : ℕ) (hi : i ≠ w.length) :
    (w ++ [b]).getD i false = w.getD i false := by
  by_cases hlt : i < w.length
  · exact List.getD_append _ _ _ _ hlt
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma all_drop (w : List Bool) (b : Bool) (pins : List ℕ)
    (neutral : w.length ∈ pins → b = true) :
    (pins.map fun i => (w ++ [b]).getD i false).all id =
      ((pins.filter (fun i => i != w.length)).map fun i => w.getD i false).all id := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.all_map, Function.comp_def, id_eq, List.all_eq_true]
  constructor
  · intro h a ha
    obtain ⟨ha, hn⟩ := List.mem_filter.mp ha
    have ne : a ≠ w.length := by simpa using hn
    rw [← getD_snoc_ne w b a ne]
    exact h a ha
  · intro h a ha
    by_cases ne : a = w.length
    · subst a
      rw [getD_append_last_eq w b _ rfl, neutral ha]
    · rw [getD_snoc_ne w b a ne]
      exact h a (List.mem_filter.mpr ⟨ha, by simpa using ne⟩)

lemma any_drop (w : List Bool) (b : Bool) (pins : List ℕ)
    (neutral : w.length ∈ pins → b = false) :
    (pins.map fun i => (w ++ [b]).getD i false).any id =
      ((pins.filter (fun i => i != w.length)).map fun i => w.getD i false).any id := by
  apply Bool.eq_iff_iff.mpr
  simp only [List.any_map, Function.comp_def, id_eq, List.any_eq_true]
  constructor
  · rintro ⟨a, ha, hv⟩
    by_cases ne : a = w.length
    · subst a
      rw [getD_append_last_eq w b _ rfl, neutral ha] at hv
      cases hv
    · exact ⟨a, List.mem_filter.mpr ⟨ha, by simpa using ne⟩,
        (getD_snoc_ne w b a ne).symm.trans hv⟩
  · rintro ⟨a, ha, hv⟩
    obtain ⟨ha, hn⟩ := List.mem_filter.mp ha
    have ne : a ≠ w.length := by simpa using hn
    exact ⟨a, ha, (getD_snoc_ne w b a ne).trans hv⟩

lemma input_order {n : ℕ} (x y : Fin n → Bool)
    (hxy : ∀ i, x i = true → y i = true) :
    ∀ k, (List.ofFn x).getD k false = true → (List.ofFn y).getD k false = true := by
  intro k hk
  by_cases hlt : k < n
  · rw [getD_ofFn _ _ hlt] at hk ⊢
    exact hxy _ hk
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hlt)] at hk
    cases hk

lemma mono_wire {n : ℕ} (gs : List Gate)
    (mono : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true) (k : ℕ) :
    (gs.foldl wiresStep (List.ofFn x)).getD k false = true →
      (gs.foldl wiresStep (List.ofFn y)).getD k false = true :=
  monotone_foldl_wiresStep gs mono _ _ (by simp) (input_order x y hxy) k

lemma output_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    (Circuit.mk (gs ++ [g]) (n + gs.length)).eval (List.ofFn x) =
      g.op.eval (g.inputs.map fun i => (gs.foldl wiresStep (List.ofFn x)).getD i false) := by
  change ((gs ++ [g]).foldl wiresStep (List.ofFn x)).getD _ false = _
  rw [List.foldl_append]
  simp only [List.foldl_cons, List.foldl_nil, wiresStep]
  apply getD_append_last_eq
  rw [foldl_wiresStep_length, List.length_ofFn]

lemma output_not_snoc {n : ℕ} (gs : List Gate) (i : ℕ) (g : Gate) (x : Fin n → Bool) :
    (Circuit.mk (gs ++ [⟨.not, [i]⟩, g]) (n + gs.length + 1)).eval (List.ofFn x) =
      g.op.eval (g.inputs.map fun j =>
        (gs.foldl wiresStep (List.ofFn x) ++
          [!((gs.foldl wiresStep (List.ofFn x)).getD i false)]).getD j false) := by
  have h := output_snoc (gs ++ [⟨.not, [i]⟩]) g x
  simpa [List.append_assoc, List.foldl_append, wiresStep, GateOp.eval, Nat.add_assoc] using h

lemma remove_terminal_not {n : ℕ} (gs : List Gate) (i : ℕ) (g : Gate)
    (mono : ∀ q ∈ gs, q.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (op : g.op = .and ∨ g.op = .or)
    (zero : (Circuit.mk (gs ++ [⟨.not, [i]⟩, g]) (n + gs.length + 1)).eval
      (List.ofFn (fun _ : Fin n => false)) = false)
    (one : (Circuit.mk (gs ++ [⟨.not, [i]⟩, g]) (n + gs.length + 1)).eval
      (List.ofFn (fun _ : Fin n => true)) = true) :
    ∀ x : Fin n → Bool,
      (Circuit.mk (gs ++ [⟨g.op, g.inputs.filter (fun j => j != n + gs.length)⟩])
        (n + gs.length)).eval (List.ofFn x) =
      (Circuit.mk (gs ++ [⟨.not, [i]⟩, g]) (n + gs.length + 1)).eval (List.ofFn x) := by
  intro x
  rw [output_snoc, output_not_snoc]
  have len (y : Fin n → Bool) : (gs.foldl wiresStep (List.ofFn y)).length = n + gs.length := by
    rw [foldl_wiresStep_length, List.length_ofFn]
  rcases op with hand | hor
  · rw [output_not_snoc, hand] at one
    rw [hand]
    change ((g.inputs.filter (fun j => j != n + gs.length)).map
      (fun j => (gs.foldl wiresStep (List.ofFn x)).getD j false)).all id = _
    symm
    convert all_drop (gs.foldl wiresStep (List.ofFn x))
      (!((gs.foldl wiresStep (List.ofFn x)).getD i false)) g.inputs ?_ using 1 <;> try { rw [len] } <;> try rfl
    intro hm
    have hm' : n + gs.length ∈ g.inputs := by simpa [len] using hm
    have atOne := (List.all_eq_true.mp one) _ (List.mem_map.mpr ⟨n + gs.length, hm', rfl⟩)
    have sourceOne : (gs.foldl wiresStep (List.ofFn (fun _ : Fin n => true))).getD i false = false := by
      simpa [← len (fun _ : Fin n => true)] using atOne
    have source : (gs.foldl wiresStep (List.ofFn x)).getD i false = false := by
      cases hx : (gs.foldl wiresStep (List.ofFn x)).getD i false
      · rfl
      · have contra := mono_wire gs mono x (fun _ => true) (by simp) i hx
        rw [sourceOne] at contra
        cases contra
    rw [source]
    rfl
  · rw [output_not_snoc, hor] at zero
    rw [hor]
    change ((g.inputs.filter (fun j => j != n + gs.length)).map
      (fun j => (gs.foldl wiresStep (List.ofFn x)).getD j false)).any id = _
    symm
    convert any_drop (gs.foldl wiresStep (List.ofFn x))
      (!((gs.foldl wiresStep (List.ofFn x)).getD i false)) g.inputs ?_ using 1 <;> try { rw [len] } <;> try rfl
    intro hm
    have hm' : n + gs.length ∈ g.inputs := by simpa [len] using hm
    have atZero := (List.any_eq_false.mp zero) _ (List.mem_map.mpr ⟨n + gs.length, hm', rfl⟩)
    have sourceZero : (gs.foldl wiresStep (List.ofFn (fun _ : Fin n => false))).getD i false = true := by
      simpa [← len (fun _ : Fin n => false)] using atZero
    have source := mono_wire gs mono (fun _ => false) x (by simp) i sourceZero
    rw [source]
    rfl

lemma final_not_impossible {n : ℕ} (gs : List Gate) (i : ℕ)
    (mono : ∀ q ∈ gs, q.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (zero : (Circuit.mk (gs ++ [⟨.not, [i]⟩]) (n + gs.length)).eval
      (List.ofFn (fun _ : Fin n => false)) = false)
    (one : (Circuit.mk (gs ++ [⟨.not, [i]⟩]) (n + gs.length)).eval
      (List.ofFn (fun _ : Fin n => true)) = true) : False := by
  rw [output_snoc] at zero one
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, Bool.not_eq_false'] at zero
  simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons, Bool.not_eq_true'] at one
  have h := mono_wire gs mono (fun _ : Fin n => false) (fun _ => true) (by simp) i zero
  rw [one] at h
  cases h

lemma penultimate_not_smaller {n : ℕ} (gs : List Gate) (i : ℕ) (g : Gate)
    (mono : Monotone2 ⟨gs, 0⟩)
    (op : g.op = .and ∨ g.op = .or)
    (arity : g.inputs.length ≤ 2)
    (zero : (Circuit.mk (gs ++ [⟨.not, [i]⟩, g]) (n + gs.length + 1)).eval
      (List.ofFn (fun _ : Fin n => false)) = false)
    (one : (Circuit.mk (gs ++ [⟨.not, [i]⟩, g]) (n + gs.length + 1)).eval
      (List.ofFn (fun _ : Fin n => true)) = true) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 = gs.length + 2 ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) =
        (Circuit.mk (gs ++ [⟨.not, [i]⟩, g]) (n + gs.length + 1)).eval (List.ofFn x) := by
  refine ⟨⟨gs ++ [⟨g.op, g.inputs.filter (fun j => j != n + gs.length)⟩], n + gs.length⟩,
    ?_, by simp [Circuit.size], ?_⟩
  · intro q hq
    rcases List.mem_append.mp hq with before | last
    · exact mono q before
    · rw [List.mem_singleton.mp last]
      refine ⟨by simpa using op, (List.length_filter_le _ _).trans arity⟩
  · exact remove_terminal_not gs i g (fun q hq => (mono q hq).1) op zero one

end Endpoint

namespace Reader

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma append_agree_except (u : ℕ) (w z : List Bool) (b c : Bool)
    (lengths : w.length = z.length)
    (agree : ∀ i, i ≠ u → w.getD i false = z.getD i false) (same : b = c) :
    ∀ i, i ≠ u → (w ++ [b]).getD i false = (z ++ [c]).getD i false := by
  intro i hi
  by_cases hlt : i < w.length
  · rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ (by omega)]
    exact agree i hi
  · by_cases heq : i = w.length
    · subst i
      rw [show (w ++ [b]).getD w.length false = b by simp, lengths]
      simpa using same
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma fold_agree_except (u : ℕ) (gs : List Gate)
    (avoid : ∀ g ∈ gs, ∀ i ∈ g.inputs, i ≠ u) (w z : List Bool)
    (lengths : w.length = z.length)
    (agree : ∀ i, i ≠ u → w.getD i false = z.getD i false) :
    ∀ i, i ≠ u → (gs.foldl step w).getD i false = (gs.foldl step z).getD i false := by
  induction gs generalizing w z with
  | nil => exact agree
  | cons g gs ih =>
    have same : g.op.eval (g.inputs.map fun i => w.getD i false) =
        g.op.eval (g.inputs.map fun i => z.getD i false) := by
      congr 1
      apply List.map_congr_left
      intro i hi
      exact agree i (avoid g (by simp) i hi)
    exact ih (fun q hq => avoid q (List.mem_cons_of_mem g hq))
      (step w g) (step z g) (by simp [step, lengths])
      (append_agree_except u w z _ _ lengths agree same)

lemma ofFn_agree_except {n : ℕ} (u : Fin n) (x y : Fin n → Bool)
    (agree : ∀ i, i ≠ u → x i = y i) :
    ∀ i, i ≠ u.val → (List.ofFn x).getD i false = (List.ofFn y).getD i false := by
  intro i hi
  by_cases hlt : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hlt), List.getD_eq_getElem _ _ (by simpa using hlt)]
    simp only [List.getElem_ofFn]
    exact agree ⟨i,hlt⟩ (fun h => hi (congrArg Fin.val h))
  · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hlt),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hlt)]

lemma first_gate_masks_unique_read {n : ℕ} (u v : Fin n) (g : Gate) (gs : List Gate)
    (pins : g.inputs = [u.val, v.val] ∨ g.inputs = [v.val, u.val])
    (b : Bool) (control : (g.op = .and ∧ b = false) ∨ (g.op = .or ∧ b = true))
    (avoid : ∀ q ∈ gs, ∀ i ∈ q.inputs, i ≠ u.val)
    (out : ℕ) (out_ne : out ≠ u.val) (x y : Fin n → Bool)
    (agree : ∀ i, i ≠ u → x i = y i) (xv : x v = b) (yv : y v = b) :
    (Circuit.mk (g :: gs) out).eval (List.ofFn x) =
      (Circuit.mk (g :: gs) out).eval (List.ofFn y) := by
  have masked (z : Fin n → Bool) (hz : z v = b) :
      g.op.eval (g.inputs.map fun i => (List.ofFn z).getD i false) = b := by
    rcases pins with hp | hp <;> rcases control with ⟨hop, rfl⟩ | ⟨hop, rfl⟩ <;>
      simp [hp, hop, GateOp.eval, hz]
  have initial := append_agree_except u.val (List.ofFn x) (List.ofFn y) _ _
    (by simp) (ofFn_agree_except u x y agree) ((masked x xv).trans (masked y yv).symm)
  exact fold_agree_except u.val gs avoid (step (List.ofFn x) g) (step (List.ofFn y) g)
    (by simp [step]) initial out out_ne

lemma first_gate_must_read_again {n : ℕ} (f : (Fin n → Bool) → Bool)
    (u v : Fin n) (g : Gate) (gs : List Gate) (out : ℕ)
    (pins : g.inputs = [u.val, v.val] ∨ g.inputs = [v.val, u.val])
    (b : Bool) (control : (g.op = .and ∧ b = false) ∨ (g.op = .or ∧ b = true))
    (out_ne : out ≠ u.val)
    (essential : ∃ x y : Fin n → Bool, (∀ i, i ≠ u → x i = y i) ∧
      x v = b ∧ y v = b ∧ f x ≠ f y)
    (computes : ∀ x : Fin n → Bool, (Circuit.mk (g :: gs) out).eval (List.ofFn x) = f x) :
    ∃ q ∈ gs, u.val ∈ q.inputs := by
  by_contra h
  have avoid : ∀ q ∈ gs, ∀ i ∈ q.inputs, i ≠ u.val := by
    intro q hq i hi eq
    subst i
    exact h ⟨q,hq,hi⟩
  obtain ⟨x,y,agree,xv,yv,different⟩ := essential
  have same := first_gate_masks_unique_read u v g gs pins b control avoid out out_ne x y agree xv yv
  rw [computes x, computes y] at same
  exact different same

end Reader

end PEqualNP.Outside.L_meta_2592_aux
