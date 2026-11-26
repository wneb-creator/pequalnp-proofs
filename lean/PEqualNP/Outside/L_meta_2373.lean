import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2373_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def effectiveInputs (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

def isNot (g : Gate) : Bool :=
  match g.op with
  | .not => true
  | _ => false

lemma effective_slot_bound (g : Gate) (h : g.inputs.length ≤ 2) :
    (effectiveInputs g).length + (if isNot g then 1 else 0) ≤ 2 := by
  cases g with
  | mk op inputs =>
    cases op <;> simp [effectiveInputs, isNot] at * <;> omega

lemma slot_bound (gs : List Gate) (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (gs.flatMap effectiveInputs).length + (gs.filter isNot).length ≤ 2 * gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have hg := effective_slot_bound g (h g (by simp))
    have ht := ih (fun a ha => h a (by simp [ha]))
    cases hn : isNot g <;>
      simp only [List.flatMap_cons, List.length_append, List.filter_cons, hn,
        Bool.false_eq_true, ↓reduceIte, List.length_cons] at * <;> omega

lemma length_split (n : ℕ) (xs : List ℕ) :
    (xs.filter (fun i => decide (i < n))).length +
      (xs.filter (fun i => decide (n ≤ i))).length = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases hx : x < n
    · simp [hx, Nat.not_le_of_gt hx]
      omega
    · simp [hx, Nat.le_of_not_gt hx]
      omega

lemma live_gate_reads_bound (n : ℕ) (gs : List Gate)
    (live : ∀ i < gs.length - 1, n + i ∈ gs.flatMap effectiveInputs) :
    gs.length - 1 ≤
      ((gs.flatMap effectiveInputs).filter (fun i => decide (n ≤ i))).length := by
  let s := (Finset.range (gs.length - 1)).image (fun i => n + i)
  have card : s.card = gs.length - 1 := by
    rw [Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)]
    exact Finset.card_range _
  have incl : s ⊆ ((gs.flatMap effectiveInputs).filter (fun i => decide (n ≤ i))).toFinset := by
    intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨live i (Finset.mem_range.mp hi), Nat.le_add_right _ _⟩
  have h := (Finset.card_le_card incl).trans (List.toFinset_card_le _)
  rwa [card] at h

lemma input_reads_and_not_budget (n : ℕ) (gs : List Gate)
    (fanin : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (live : ∀ i < gs.length - 1, n + i ∈ gs.flatMap effectiveInputs) :
    ((gs.flatMap effectiveInputs).filter (fun i => decide (i < n))).length +
      (gs.filter isNot).length ≤ gs.length + 1 := by
  have hslots := slot_bound gs fanin
  have hsplit := length_split n (gs.flatMap effectiveInputs)
  have hlive := live_gate_reads_bound n gs live
  omega

lemma input_reads_not_and_reuse_budget (n : ℕ) (gs : List Gate)
    (fanin : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (live : ∀ i < gs.length - 1, n + i ∈ gs.flatMap effectiveInputs) :
    ((gs.flatMap effectiveInputs).filter (fun i => decide (i < n))).length +
      (gs.filter isNot).length +
      (((gs.flatMap effectiveInputs).filter (fun i => decide (n ≤ i))).length -
        (gs.length - 1)) ≤ gs.length + 1 := by
  have hslots := slot_bound gs fanin
  have hsplit := length_split n (gs.flatMap effectiveInputs)
  have hlive := live_gate_reads_bound n gs live
  omega

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def petersen (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def nearMiss : Circuit :=
  ⟨[⟨.or, [5, 3]⟩, ⟨.or, [0, 9]⟩, ⟨.or, [2, 6]⟩,
    ⟨.or, [2, 5]⟩, ⟨.or, [10, 6]⟩, ⟨.or, [11, 3]⟩,
    ⟨.or, [13, 9]⟩, ⟨.or, [12, 0]⟩, ⟨.and, [17, 14]⟩,
    ⟨.and, [4, 15]⟩, ⟨.and, [18, 15]⟩, ⟨.or, [20, 7]⟩,
    ⟨.and, [17, 1]⟩, ⟨.or, [19, 22]⟩,
    ⟨.and, [14, 8]⟩, ⟨.and, [21, 16]⟩, ⟨.or, [25, 24]⟩,
    ⟨.or, [26, 23]⟩], 27⟩

lemma nearMiss_size : nearMiss.size = 18 := rfl

lemma nearMiss_fanin : FanInTwo nearMiss := by
  intro g hg
  simp only [nearMiss, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact ⟨by simp, by decide⟩

set_option maxHeartbeats 2000000 in
lemma nearMiss_formula (x : Fin 10 → Bool) :
    nearMiss.eval (List.ofFn x) =
      (petersen x || (x 0 && x 2 && x 6) || (x 3 && x 5 && x 6) ||
        (x 0 && x 3 && x 9) || (x 2 && x 5 && x 9)) := by
  have h : ∀ a b c d e f g h i j : Bool,
      (((((c || g) || a) && ((f || d) || g)) && ((a || j) || d) || h) &&
        ((c || f) || j) || (((f || d) || g) && i) ||
          ((e && ((a || j) || d)) || (((c || g) || a) && b))) =
      ((a && b || b && c || c && d || d && e || e && a || a && f || b && g ||
        c && h || d && i || e && j || f && h || h && j || j && g || g && i || i && f) ||
      (a && c && g) || (d && f && g) || (a && d && j) || (c && f && j)) := by
    intro a b c d e f g h i j
    cases a <;> cases b <;> cases c <;> cases d <;> cases e <;>
      cases f <;> cases g <;> cases h <;> cases i <;> cases j <;> rfl
  have hx : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9] := rfl
  rw [hx]
  simp only [nearMiss, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    GateOp.eval, List.any_cons, List.any_nil, List.all_cons, List.all_nil, id_eq,
    List.getD, List.getElem?_cons_zero, List.getElem?_cons_succ, Option.getD_some,
    Bool.or_false, Bool.and_true, petersen]
  exact h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) (x 7) (x 8) (x 9)

lemma nearMiss_covers (x : Fin 10 → Bool) (h : petersen x = true) :
    nearMiss.eval (List.ofFn x) = true := by
  rw [nearMiss_formula, h]
  rfl

set_option maxHeartbeats 2000000 in
lemma nearMiss_pair_correct (a b : Fin 10) :
    nearMiss.eval (List.ofFn (fun i => decide (i = a ∨ i = b))) =
      petersen (fun i => decide (i = a ∨ i = b)) := by
  have h : ∀ a b : Fin 10,
      let x := fun i : Fin 10 => decide (i = a ∨ i = b)
      (x 0 && x 2 && x 6) = false ∧ (x 3 && x 5 && x 6) = false ∧
        (x 0 && x 3 && x 9) = false ∧ (x 2 && x 5 && x 9) = false := by
    decide +kernel
  obtain ⟨h1, h2, h3, h4⟩ := h a b
  rw [nearMiss_formula, h1, h2, h3, h4]
  simp

lemma nearMiss_is_not_counterexample :
    nearMiss.eval (List.ofFn (fun i : Fin 10 => decide (i = 0 ∨ i = 2 ∨ i = 6))) = true ∧
      petersen (fun i : Fin 10 => decide (i = 0 ∨ i = 2 ∨ i = 6)) = false := by
  rw [nearMiss_formula]
  decide +kernel

open PEqualNP.CircuitLowerBounds

def agreeExcept (v : ℕ) (xs ys : List Bool) : Prop :=
  xs.length = ys.length ∧ ∀ i, i ≠ v → xs.getD i false = ys.getD i false

lemma eval_effectiveInputs (g : Gate) (f : ℕ → Bool) :
    g.op.eval (g.inputs.map f) = g.op.eval ((effectiveInputs g).map f) := by
  rcases g with ⟨op, inputs⟩
  cases op <;> simp only [effectiveInputs]
  cases inputs <;> simp [GateOp.eval]

lemma agreeExcept_append (v : ℕ) (xs ys : List Bool) (a b : Bool)
    (h : agreeExcept v xs ys) (hab : a = b) :
    agreeExcept v (xs ++ [a]) (ys ++ [b]) := by
  subst b
  refine ⟨by simp [h.1], ?_⟩
  intro i hi
  by_cases hil : i < xs.length
  · rw [List.getD_append _ _ _ _ hil,
      List.getD_append _ _ _ _ (by simpa [h.1] using hil)]
    exact h.2 i hi
  · rw [List.getD_append_right _ _ _ _ (by omega),
      List.getD_append_right _ _ _ _ (by have := h.1; omega), h.1]

lemma agreeExcept_gate (v : ℕ) (xs ys : List Bool) (g : Gate)
    (h : agreeExcept v xs ys) (hg : v ∉ effectiveInputs g) :
    g.op.eval (g.inputs.map (fun i => xs.getD i false)) =
      g.op.eval (g.inputs.map (fun i => ys.getD i false)) := by
  rw [eval_effectiveInputs, eval_effectiveInputs]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact h.2 i (by intro he; subst i; exact hg hi)

lemma agreeExcept_fold (v : ℕ) (xs ys : List Bool) (gs : List Gate)
    (h : agreeExcept v xs ys) (hg : ∀ g ∈ gs, v ∉ effectiveInputs g) :
    agreeExcept v
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) xs)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) ys) := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih
    · exact agreeExcept_append v xs ys _ _ h
        (agreeExcept_gate v xs ys g h (hg g (by simp)))
    · intro a ha
      exact hg a (by simp [ha])

lemma first_gate_mask (v : ℕ) (xs ys : List Bool) (g : Gate) (gs : List Gate)
    (out : ℕ) (hout : out ≠ v) (h : agreeExcept v xs ys)
    (hfirst : g.op.eval (g.inputs.map (fun i => xs.getD i false)) =
      g.op.eval (g.inputs.map (fun i => ys.getD i false)))
    (hrest : ∀ q ∈ gs, v ∉ effectiveInputs q) :
    (Circuit.mk (g :: gs) out).eval xs = (Circuit.mk (g :: gs) out).eval ys := by
  exact (agreeExcept_fold v _ _ gs (agreeExcept_append v xs ys _ _ h hfirst) hrest).2 out hout

lemma ofFn_agreeExcept {n : ℕ} (v : Fin n) (x y : Fin n → Bool)
    (h : ∀ i, i ≠ v → x i = y i) : agreeExcept v.val (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, ?_⟩
  intro i hi
  by_cases hin : i < n
  · simpa [List.getD, hin] using h ⟨i, hin⟩ (by intro he; exact hi (congrArg Fin.val he))
  · simp [List.getD, hin]

lemma getD_ofFn_val {n : ℕ} (x : Fin n → Bool) (i : Fin n) :
    (List.ofFn x).getD i.val false = x i := by
  simp [List.getD]

lemma original_wire_preserved (xs : List Bool) (gs : List Gate) (i : ℕ)
    (hi : i < xs.length) :
    (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun j => w.getD j false))]) xs).getD i false =
      xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

lemma eval_original_inputs (xs : List Bool) (gs : List Gate) (g : Gate)
    (hg : ∀ i ∈ g.inputs, i < xs.length) :
    g.op.eval (g.inputs.map (fun i =>
      (gs.foldl (fun w q => w ++ [q.op.eval (q.inputs.map (fun j => w.getD j false))]) xs).getD i false)) =
      g.op.eval (g.inputs.map (fun i => xs.getD i false)) := by
  congr 1
  apply List.map_congr_left
  intro i hi
  exact original_wire_preserved xs gs i (hg i hi)

lemma gate_mask_in_context (v : ℕ) (xs ys : List Bool) (pre post : List Gate)
    (g : Gate) (out : ℕ) (hout : out ≠ v) (h : agreeExcept v xs ys)
    (hinputs : ∀ i ∈ g.inputs, i < xs.length)
    (hfirst : g.op.eval (g.inputs.map (fun i => xs.getD i false)) =
      g.op.eval (g.inputs.map (fun i => ys.getD i false)))
    (hpre : ∀ q ∈ pre, v ∉ effectiveInputs q)
    (hpost : ∀ q ∈ post, v ∉ effectiveInputs q) :
    (Circuit.mk (pre ++ g :: post) out).eval xs =
      (Circuit.mk (pre ++ g :: post) out).eval ys := by
  have heq := first_gate_mask v _ _ g post out hout
    (agreeExcept_fold v xs ys pre h hpre)
    (by
      rw [eval_original_inputs xs pre g hinputs,
        eval_original_inputs ys pre g (by intro i hi; rw [← h.1]; exact hinputs i hi)]
      exact hfirst) hpost
  simpa only [Circuit.eval, Circuit.wires, List.foldl_append] using heq

lemma petersen_singleton_false : ∀ a : Fin 10,
    petersen (fun i => decide (i = a)) = false := by
  decide +kernel

lemma petersen_output_not_input (C : Circuit)
    (hev : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x)
    (a : Fin 10) : C.output ≠ a.val := by
  intro hout
  have h := hev (fun i => decide (i = a))
  unfold Circuit.eval Circuit.wires at h
  rw [hout, original_wire_preserved _ _ _ (by simp), getD_ofFn_val,
    petersen_singleton_false] at h
  simp at h

set_option maxHeartbeats 2000000 in
lemma petersen_and_mask_witness : ∀ a b : Fin 10, a ≠ b → ∃ t : Fin 10,
    t ≠ b ∧
    petersen (fun i => decide (i = t)) = false ∧
    petersen (fun i => decide (i = a ∨ i = t)) = true := by
  decide +kernel

set_option maxHeartbeats 2000000 in
lemma petersen_or_mask_witness : ∀ a b : Fin 10, a ≠ b → ∃ t : Fin 10,
    petersen (fun i => decide (i = b ∨ i = t)) = false ∧
    petersen (fun i => decide (i = a ∨ i = b ∨ i = t)) = true := by
  decide +kernel

lemma petersen_input_read (C : Circuit)
    (hev : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x)
    (a : Fin 10) : ∃ g ∈ C.gates, a.val ∈ effectiveInputs g := by
  by_contra hn
  have hrest : ∀ g ∈ C.gates, a.val ∉ effectiveInputs g := fun g hg ha => hn ⟨g, hg, ha⟩
  obtain ⟨b, hba⟩ := exists_ne a
  obtain ⟨t, _, hx, hy⟩ := petersen_and_mask_witness a b hba.symm
  have e := (agreeExcept_fold a.val
    (List.ofFn (fun i : Fin 10 => decide (i = t)))
    (List.ofFn (fun i : Fin 10 => decide (i = a ∨ i = t))) C.gates
    (ofFn_agreeExcept a _ _ (by intro i hi; simp [hi])) hrest).2 C.output
      (petersen_output_not_input C hev a)
  change C.eval _ = C.eval _ at e
  rw [hev, hev, hx, hy] at e
  exact Bool.false_ne_true e

lemma first_and_input_reread (a b : Fin 10) (hab : a ≠ b)
    (gs : List Gate) (out : ℕ)
    (hev : ∀ x : Fin 10 → Bool,
      (Circuit.mk (⟨.and, [a.val, b.val]⟩ :: gs) out).eval (List.ofFn x) = petersen x) :
    ∃ g ∈ gs, a.val ∈ effectiveInputs g := by
  by_contra hn
  have hrest : ∀ g ∈ gs, a.val ∉ effectiveInputs g := fun g hg ha => hn ⟨g, hg, ha⟩
  obtain ⟨t, htb, hx, hy⟩ := petersen_and_mask_witness a b hab
  have e := first_gate_mask a.val
    (List.ofFn (fun i : Fin 10 => decide (i = t)))
    (List.ofFn (fun i : Fin 10 => decide (i = a ∨ i = t)))
    ⟨.and, [a.val, b.val]⟩ gs out (petersen_output_not_input _ hev a)
    (ofFn_agreeExcept a _ _ (by intro i hi; simp [hi]))
    (by
      simp only [List.map_cons, List.map_nil, getD_ofFn_val, GateOp.eval,
        List.all_cons, List.all_nil, id_eq, Bool.and_true]
      simp [htb.symm, hab.symm]) hrest
  rw [hev, hev, hx, hy] at e
  exact Bool.false_ne_true e

lemma first_or_input_reread (a b : Fin 10) (hab : a ≠ b)
    (gs : List Gate) (out : ℕ)
    (hev : ∀ x : Fin 10 → Bool,
      (Circuit.mk (⟨.or, [a.val, b.val]⟩ :: gs) out).eval (List.ofFn x) = petersen x) :
    ∃ g ∈ gs, a.val ∈ effectiveInputs g := by
  by_contra hn
  have hrest : ∀ g ∈ gs, a.val ∉ effectiveInputs g := fun g hg ha => hn ⟨g, hg, ha⟩
  obtain ⟨t, hx, hy⟩ := petersen_or_mask_witness a b hab
  have e := first_gate_mask a.val
    (List.ofFn (fun i : Fin 10 => decide (i = b ∨ i = t)))
    (List.ofFn (fun i : Fin 10 => decide (i = a ∨ i = b ∨ i = t)))
    ⟨.or, [a.val, b.val]⟩ gs out (petersen_output_not_input _ hev a)
    (ofFn_agreeExcept a _ _ (by intro i hi; simp [hi]))
    (by
      simp only [List.map_cons, List.map_nil, getD_ofFn_val, GateOp.eval,
        List.any_cons, List.any_nil, id_eq, Bool.or_false]
      simp) hrest
  rw [hev, hev, hx, hy] at e
  exact Bool.false_ne_true e

lemma first_and_second_input_reread (a b : Fin 10) (hab : a ≠ b)
    (gs : List Gate) (out : ℕ)
    (hev : ∀ x : Fin 10 → Bool,
      (Circuit.mk (⟨.and, [a.val, b.val]⟩ :: gs) out).eval (List.ofFn x) = petersen x) :
    ∃ g ∈ gs, b.val ∈ effectiveInputs g := by
  by_contra hn
  have hrest : ∀ g ∈ gs, b.val ∉ effectiveInputs g := fun g hg ha => hn ⟨g, hg, ha⟩
  obtain ⟨t, hta, hx, hy⟩ := petersen_and_mask_witness b a hab.symm
  have e := first_gate_mask b.val
    (List.ofFn (fun i : Fin 10 => decide (i = t)))
    (List.ofFn (fun i : Fin 10 => decide (i = b ∨ i = t)))
    ⟨.and, [a.val, b.val]⟩ gs out (petersen_output_not_input _ hev b)
    (ofFn_agreeExcept b _ _ (by intro i hi; simp [hi]))
    (by
      simp only [List.map_cons, List.map_nil, getD_ofFn_val, GateOp.eval,
        List.all_cons, List.all_nil, id_eq, Bool.and_true]
      simp [hta.symm, hab]) hrest
  rw [hev, hev, hx, hy] at e
  exact Bool.false_ne_true e

lemma first_or_second_input_reread (a b : Fin 10) (hab : a ≠ b)
    (gs : List Gate) (out : ℕ)
    (hev : ∀ x : Fin 10 → Bool,
      (Circuit.mk (⟨.or, [a.val, b.val]⟩ :: gs) out).eval (List.ofFn x) = petersen x) :
    ∃ g ∈ gs, b.val ∈ effectiveInputs g := by
  by_contra hn
  have hrest : ∀ g ∈ gs, b.val ∉ effectiveInputs g := fun g hg ha => hn ⟨g, hg, ha⟩
  obtain ⟨t, hx, hy⟩ := petersen_or_mask_witness b a hab.symm
  have e := first_gate_mask b.val
    (List.ofFn (fun i : Fin 10 => decide (i = a ∨ i = t)))
    (List.ofFn (fun i : Fin 10 => decide (i = b ∨ i = a ∨ i = t)))
    ⟨.or, [a.val, b.val]⟩ gs out (petersen_output_not_input _ hev b)
    (ofFn_agreeExcept b _ _ (by intro i hi; simp [hi]))
    (by
      simp only [List.map_cons, List.map_nil, getD_ofFn_val, GateOp.eval,
        List.any_cons, List.any_nil, id_eq, Bool.or_false]
      simp) hrest
  rw [hev, hev, hx, hy] at e
  exact Bool.false_ne_true e

lemma and_input_read_elsewhere (a b : Fin 10) (hab : a ≠ b)
    (pre post : List Gate) (out : ℕ)
    (hev : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨.and, [a.val, b.val]⟩ :: post) out).eval (List.ofFn x) =
        petersen x) :
    ∃ g ∈ pre ++ post, a.val ∈ effectiveInputs g := by
  by_contra hn
  have hpre : ∀ g ∈ pre, a.val ∉ effectiveInputs g :=
    fun g hg ha => hn ⟨g, List.mem_append_left post hg, ha⟩
  have hpost : ∀ g ∈ post, a.val ∉ effectiveInputs g :=
    fun g hg ha => hn ⟨g, List.mem_append_right pre hg, ha⟩
  obtain ⟨t, htb, hx, hy⟩ := petersen_and_mask_witness a b hab
  have e := gate_mask_in_context a.val
    (List.ofFn (fun i : Fin 10 => decide (i = t)))
    (List.ofFn (fun i : Fin 10 => decide (i = a ∨ i = t)))
    pre post ⟨.and, [a.val, b.val]⟩ out (petersen_output_not_input _ hev a)
    (ofFn_agreeExcept a _ _ (by intro i hi; simp [hi]))
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi;
        rcases hi with rfl | rfl <;> simp)
    (by
      simp only [List.map_cons, List.map_nil, getD_ofFn_val, GateOp.eval,
        List.all_cons, List.all_nil, id_eq, Bool.and_true]
      simp [htb.symm, hab.symm]) hpre hpost
  rw [hev, hev, hx, hy] at e
  exact Bool.false_ne_true e

lemma or_input_read_elsewhere (a b : Fin 10) (hab : a ≠ b)
    (pre post : List Gate) (out : ℕ)
    (hev : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨.or, [a.val, b.val]⟩ :: post) out).eval (List.ofFn x) =
        petersen x) :
    ∃ g ∈ pre ++ post, a.val ∈ effectiveInputs g := by
  by_contra hn
  have hpre : ∀ g ∈ pre, a.val ∉ effectiveInputs g :=
    fun g hg ha => hn ⟨g, List.mem_append_left post hg, ha⟩
  have hpost : ∀ g ∈ post, a.val ∉ effectiveInputs g :=
    fun g hg ha => hn ⟨g, List.mem_append_right pre hg, ha⟩
  obtain ⟨t, hx, hy⟩ := petersen_or_mask_witness a b hab
  have e := gate_mask_in_context a.val
    (List.ofFn (fun i : Fin 10 => decide (i = b ∨ i = t)))
    (List.ofFn (fun i : Fin 10 => decide (i = a ∨ i = b ∨ i = t)))
    pre post ⟨.or, [a.val, b.val]⟩ out (petersen_output_not_input _ hev a)
    (ofFn_agreeExcept a _ _ (by intro i hi; simp [hi]))
    (by intro i hi; simp only [List.mem_cons, List.not_mem_nil, or_false] at hi;
        rcases hi with rfl | rfl <;> simp)
    (by
      simp only [List.map_cons, List.map_nil, getD_ofFn_val, GateOp.eval,
        List.any_cons, List.any_nil, id_eq, Bool.or_false]
      simp) hpre hpost
  rw [hev, hev, hx, hy] at e
  exact Bool.false_ne_true e

lemma binary_eval_comm (op : GateOp) (hop : op = .and ∨ op = .or)
    (a b : ℕ) (f : ℕ → Bool) :
    op.eval ([a, b].map f) = op.eval ([b, a].map f) := by
  rcases hop with rfl | rfl <;> simp [GateOp.eval, Bool.and_comm, Bool.or_comm]

lemma binary_gate_context_comm (op : GateOp) (hop : op = .and ∨ op = .or)
    (a b : ℕ) (pre post : List Gate) (out : ℕ) (xs : List Bool) :
    (Circuit.mk (pre ++ ⟨op, [a, b]⟩ :: post) out).eval xs =
      (Circuit.mk (pre ++ ⟨op, [b, a]⟩ :: post) out).eval xs := by
  simp only [Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons]
  rw [binary_eval_comm op hop a b]

lemma binary_inputs_read_elsewhere (op : GateOp) (hop : op = .and ∨ op = .or)
    (a b : Fin 10) (hab : a ≠ b) (pre post : List Gate) (out : ℕ)
    (hev : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨op, [a.val, b.val]⟩ :: post) out).eval (List.ofFn x) =
        petersen x) :
    (∃ g ∈ pre ++ post, a.val ∈ effectiveInputs g) ∧
      (∃ g ∈ pre ++ post, b.val ∈ effectiveInputs g) := by
  have hev' : ∀ x : Fin 10 → Bool,
      (Circuit.mk (pre ++ ⟨op, [b.val, a.val]⟩ :: post) out).eval (List.ofFn x) =
        petersen x := by
    intro x
    rw [binary_gate_context_comm op hop b.val a.val]
    exact hev x
  rcases hop with rfl | rfl
  · exact ⟨and_input_read_elsewhere a b hab pre post out hev,
      and_input_read_elsewhere b a hab.symm pre post out hev'⟩
  · exact ⟨or_input_read_elsewhere a b hab pre post out hev,
      or_input_read_elsewhere b a hab.symm pre post out hev'⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def maskedReadShape (a b c : ℕ) (g : Gate) : Prop :=
  g = ⟨.and, [a, b]⟩ ∨ g = ⟨.and, [b, a]⟩ ∨
    g = ⟨.or, [a, c]⟩ ∨ g = ⟨.or, [c, a]⟩

lemma and_or_masked_gate (a b c : ℕ) (xs ys : List Bool) (g : Gate)
    (hba : b ≠ a) (hca : c ≠ a) (h : agreeExcept a xs ys)
    (hb : xs.getD b false = false) (hc : xs.getD c false = true)
    (hshape : a ∈ effectiveInputs g → maskedReadShape a b c g) :
    g.op.eval (g.inputs.map (fun i => xs.getD i false)) =
      g.op.eval (g.inputs.map (fun i => ys.getD i false)) := by
  have hby : ys.getD b false = false := by rw [← h.2 b hba]; exact hb
  have hcy : ys.getD c false = true := by rw [← h.2 c hca]; exact hc
  by_cases ha : a ∈ effectiveInputs g
  · rcases hshape ha with rfl | rfl | rfl | rfl <;>
      simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
        List.all_nil, List.any_cons, List.any_nil, id_eq, hb, hc, hby, hcy,
        Bool.and_true, Bool.and_false, Bool.false_and, Bool.or_false,
        Bool.or_true, Bool.true_or]
  · exact agreeExcept_gate a xs ys g h ha

lemma and_or_masked_fold (a b c : ℕ) (xs ys : List Bool) (gs : List Gate)
    (hba : b ≠ a) (hca : c ≠ a) (h : agreeExcept a xs ys)
    (hbidx : b < xs.length) (hcidx : c < xs.length)
    (hb : xs.getD b false = false) (hc : xs.getD c false = true)
    (hshape : ∀ g ∈ gs, a ∈ effectiveInputs g → maskedReadShape a b c g) :
    agreeExcept a
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) xs)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) ys) := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih
    · exact agreeExcept_append a xs ys _ _ h
        (and_or_masked_gate a b c xs ys g hba hca h hb hc (hshape g (by simp)))
    · simp; omega
    · simp; omega
    · rw [List.getD_append _ _ _ _ hbidx]; exact hb
    · rw [List.getD_append _ _ _ _ hcidx]; exact hc
    · intro q hq
      exact hshape q (by simp [hq])

set_option maxHeartbeats 4000000 in
lemma petersen_and_or_mask_witness : ∀ a b c : Fin 10,
    a ≠ b → a ≠ c → b ≠ c → ∃ t : Fin 10,
    t ≠ b ∧ petersen (fun i => decide (i = c ∨ i = t)) = false ∧
      petersen (fun i => decide (i = a ∨ i = c ∨ i = t)) = true := by
  decide +kernel

lemma petersen_and_or_raw_read_obstruction (C : Circuit) (a b c : Fin 10)
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hshape : ∀ g ∈ C.gates, a.val ∈ effectiveInputs g →
      maskedReadShape a.val b.val c.val g) :
    ¬ (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) := by
  intro hev
  obtain ⟨t, htb, hx, hy⟩ := petersen_and_or_mask_witness a b c hab hac hbc
  have e := (and_or_masked_fold a.val b.val c.val
    (List.ofFn (fun i : Fin 10 => decide (i = c ∨ i = t)))
    (List.ofFn (fun i : Fin 10 => decide (i = a ∨ i = c ∨ i = t))) C.gates
    (by intro he; exact hab (Fin.ext he.symm))
    (by intro he; exact hac (Fin.ext he.symm))
    (ofFn_agreeExcept a _ _ (by intro i hi; simp [hi]))
    (by simp) (by simp)
    (by rw [getD_ofFn_val]; simp [hbc, htb.symm])
    (by rw [getD_ofFn_val]; simp) hshape).2 C.output
      (petersen_output_not_input C hev a)
  change C.eval _ = C.eval _ at e
  rw [hev, hev, hx, hy] at e
  exact Bool.false_ne_true e

set_option maxHeartbeats 4000000 in
lemma two_and_read_mask_witness : ∀ a b c : Fin 10,
    a ≠ b → a ≠ c → ∃ t : Fin 10,
      t ≠ b ∧ t ≠ c ∧
      petersen (fun i => decide (i = t)) = false ∧
      petersen (fun i => decide (i = a ∨ i = t)) = true := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma two_or_read_mask_witness : ∀ a b c : Fin 10,
    a ≠ b → a ≠ c → petersen (fun i => decide (i = b ∨ i = c)) = false →
    ∃ t : Fin 10,
      petersen (fun i => decide (i = b ∨ i = c ∨ i = t)) = false ∧
      petersen (fun i => decide (i = a ∨ i = b ∨ i = c ∨ i = t)) = true := by
  decide +kernel

open PEqualNP.CircuitLowerBounds

def uniformReadShape (z : Bool) (a b c : ℕ) (g : Gate) : Prop :=
  let op := if z then GateOp.or else GateOp.and
  g = ⟨op, [a, b]⟩ ∨ g = ⟨op, [b, a]⟩ ∨
    g = ⟨op, [a, c]⟩ ∨ g = ⟨op, [c, a]⟩

lemma uniform_masked_gate (z : Bool) (a b c : ℕ) (xs ys : List Bool) (g : Gate)
    (hba : b ≠ a) (hca : c ≠ a) (h : agreeExcept a xs ys)
    (hb : xs.getD b false = z) (hc : xs.getD c false = z)
    (hshape : a ∈ effectiveInputs g → uniformReadShape z a b c g) :
    g.op.eval (g.inputs.map (fun i => xs.getD i false)) =
      g.op.eval (g.inputs.map (fun i => ys.getD i false)) := by
  have hby : ys.getD b false = z := by rw [← h.2 b hba]; exact hb
  have hcy : ys.getD c false = z := by rw [← h.2 c hca]; exact hc
  by_cases ha : a ∈ effectiveInputs g
  · cases z <;> rcases hshape ha with rfl | rfl | rfl | rfl <;>
      simp only [Bool.false_eq_true, ↓reduceIte, GateOp.eval, List.map_cons,
        List.map_nil, List.all_cons, List.all_nil, List.any_cons, List.any_nil, id_eq,
        hb, hc, hby, hcy, Bool.and_true, Bool.and_false, Bool.false_and,
        Bool.or_false, Bool.or_true, Bool.true_or]
  · exact agreeExcept_gate a xs ys g h ha

lemma uniform_masked_fold (z : Bool) (a b c : ℕ) (xs ys : List Bool) (gs : List Gate)
    (hba : b ≠ a) (hca : c ≠ a) (h : agreeExcept a xs ys)
    (hbidx : b < xs.length) (hcidx : c < xs.length)
    (hb : xs.getD b false = z) (hc : xs.getD c false = z)
    (hshape : ∀ g ∈ gs, a ∈ effectiveInputs g → uniformReadShape z a b c g) :
    agreeExcept a
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) xs)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) ys) := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih
    · exact agreeExcept_append a xs ys _ _ h
        (uniform_masked_gate z a b c xs ys g hba hca h hb hc (hshape g (by simp)))
    · simp; omega
    · simp; omega
    · rw [List.getD_append _ _ _ _ hbidx]; exact hb
    · rw [List.getD_append _ _ _ _ hcidx]; exact hc
    · intro q hq
      exact hshape q (by simp [hq])

lemma petersen_two_and_raw_read_obstruction (C : Circuit) (a b c : Fin 10)
    (hab : a ≠ b) (hac : a ≠ c)
    (hshape : ∀ g ∈ C.gates, a.val ∈ effectiveInputs g →
      uniformReadShape false a.val b.val c.val g) :
    ¬ (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) := by
  intro hev
  obtain ⟨t, htb, htc, hx, hy⟩ := two_and_read_mask_witness a b c hab hac
  have e := (uniform_masked_fold false a.val b.val c.val
    (List.ofFn (fun i : Fin 10 => decide (i = t)))
    (List.ofFn (fun i : Fin 10 => decide (i = a ∨ i = t))) C.gates
    (by intro he; exact hab (Fin.ext he.symm))
    (by intro he; exact hac (Fin.ext he.symm))
    (ofFn_agreeExcept a _ _ (by intro i hi; simp [hi]))
    (by simp) (by simp)
    (by rw [getD_ofFn_val]; simp [htb.symm])
    (by rw [getD_ofFn_val]; simp [htc.symm]) hshape).2 C.output
      (petersen_output_not_input C hev a)
  change C.eval _ = C.eval _ at e
  rw [hev, hev, hx, hy] at e
  exact Bool.false_ne_true e

lemma petersen_two_or_raw_read_obstruction (C : Circuit) (a b c : Fin 10)
    (hab : a ≠ b) (hac : a ≠ c)
    (hbc : petersen (fun i => decide (i = b ∨ i = c)) = false)
    (hshape : ∀ g ∈ C.gates, a.val ∈ effectiveInputs g →
      uniformReadShape true a.val b.val c.val g) :
    ¬ (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) := by
  intro hev
  obtain ⟨t, hx, hy⟩ := two_or_read_mask_witness a b c hab hac hbc
  have e := (uniform_masked_fold true a.val b.val c.val
    (List.ofFn (fun i : Fin 10 => decide (i = b ∨ i = c ∨ i = t)))
    (List.ofFn (fun i : Fin 10 => decide (i = a ∨ i = b ∨ i = c ∨ i = t))) C.gates
    (by intro he; exact hab (Fin.ext he.symm))
    (by intro he; exact hac (Fin.ext he.symm))
    (ofFn_agreeExcept a _ _ (by intro i hi; simp [hi]))
    (by simp) (by simp)
    (by rw [getD_ofFn_val]; simp)
    (by rw [getD_ofFn_val]; simp) hshape).2 C.output
      (petersen_output_not_input C hev a)
  change C.eval _ = C.eval _ at e
  rw [hev, hev, hx, hy] at e
  exact Bool.false_ne_true e

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def swapAgree (a b : ℕ) (xs ys : List Bool) : Prop :=
  xs.length = ys.length ∧ xs.getD a false = ys.getD b false ∧
    xs.getD b false = ys.getD a false ∧
      ∀ i, i ≠ a → i ≠ b → xs.getD i false = ys.getD i false

def sharedSymmetricReadShape (a b : ℕ) (g : Gate) : Prop :=
  g = ⟨.and, [a, b]⟩ ∨ g = ⟨.and, [b, a]⟩ ∨
    g = ⟨.or, [a, b]⟩ ∨ g = ⟨.or, [b, a]⟩

lemma swapAgree_append (a b : ℕ) (xs ys : List Bool) (u v : Bool)
    (ha : a < xs.length) (hb : b < xs.length)
    (h : swapAgree a b xs ys) (huv : u = v) :
    swapAgree a b (xs ++ [u]) (ys ++ [v]) := by
  subst v
  refine ⟨by simp [h.1], ?_, ?_, ?_⟩
  · rw [List.getD_append _ _ _ _ ha,
      List.getD_append _ _ _ _ (by simpa [h.1] using hb)]
    exact h.2.1
  · rw [List.getD_append _ _ _ _ hb,
      List.getD_append _ _ _ _ (by simpa [h.1] using ha)]
    exact h.2.2.1
  · intro i hia hib
    by_cases hi : i < xs.length
    · rw [List.getD_append _ _ _ _ hi,
        List.getD_append _ _ _ _ (by simpa [h.1] using hi)]
      exact h.2.2.2 i hia hib
    · rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by have := h.1; omega), h.1]

lemma shared_symmetric_gate (a b : ℕ) (xs ys : List Bool) (g : Gate)
    (h : swapAgree a b xs ys)
    (hshape : a ∈ effectiveInputs g ∨ b ∈ effectiveInputs g →
      sharedSymmetricReadShape a b g) :
    g.op.eval (g.inputs.map (fun i => xs.getD i false)) =
      g.op.eval (g.inputs.map (fun i => ys.getD i false)) := by
  by_cases hab : a ∈ effectiveInputs g ∨ b ∈ effectiveInputs g
  · rcases hshape hab with rfl | rfl | rfl | rfl <;>
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
        List.any_cons, List.any_nil, id_eq, Bool.true_and, Bool.false_or,
        h.2.1, h.2.2.1, Bool.and_comm, Bool.or_comm]
  · rw [eval_effectiveInputs, eval_effectiveInputs]
    congr 1
    apply List.map_congr_left
    intro i hi
    apply h.2.2.2 i
    · intro he
      subst i
      exact hab (Or.inl hi)
    · intro he
      subst i
      exact hab (Or.inr hi)

lemma shared_symmetric_fold (a b : ℕ) (xs ys : List Bool) (gs : List Gate)
    (ha : a < xs.length) (hb : b < xs.length) (h : swapAgree a b xs ys)
    (hshape : ∀ g ∈ gs, a ∈ effectiveInputs g ∨ b ∈ effectiveInputs g →
      sharedSymmetricReadShape a b g) :
    swapAgree a b
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) xs)
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) ys) := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply ih
    · simp; omega
    · simp; omega
    · exact swapAgree_append a b xs ys _ _ ha hb h
        (shared_symmetric_gate a b xs ys g h (hshape g (by simp)))
    · intro q hq
      exact hshape q (by simp [hq])

lemma ofFn_swapAgree {n : ℕ} (a b : Fin n) (x y : Fin n → Bool)
    (ha : x a = y b) (hb : x b = y a)
    (hrest : ∀ i, i ≠ a → i ≠ b → x i = y i) :
    swapAgree a.val b.val (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, by simpa [getD_ofFn_val] using ha,
    by simpa [getD_ofFn_val] using hb, ?_⟩
  intro i hia hib
  by_cases hi : i < n
  · simpa [List.getD, hi] using hrest ⟨i, hi⟩
      (by intro he; exact hia (congrArg Fin.val he))
      (by intro he; exact hib (congrArg Fin.val he))
  · simp [List.getD, hi]

set_option maxHeartbeats 4000000 in
lemma petersen_pair_swap_witness : ∀ a b : Fin 10, a ≠ b → ∃ t : Fin 10,
    t ≠ a ∧ t ≠ b ∧ petersen (fun i => decide (i = b ∨ i = t)) = false ∧
      petersen (fun i => decide (i = a ∨ i = t)) = true := by
  decide +kernel

lemma petersen_shared_and_or_read_obstruction (C : Circuit) (a b : Fin 10)
    (hab : a ≠ b)
    (hshape : ∀ g ∈ C.gates, a.val ∈ effectiveInputs g ∨ b.val ∈ effectiveInputs g →
      sharedSymmetricReadShape a.val b.val g) :
    ¬ (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x) := by
  intro hev
  obtain ⟨t, hta, htb, hx, hy⟩ := petersen_pair_swap_witness a b hab
  have e := (shared_symmetric_fold a.val b.val
    (List.ofFn (fun i : Fin 10 => decide (i = b ∨ i = t)))
    (List.ofFn (fun i : Fin 10 => decide (i = a ∨ i = t))) C.gates
    (by simp) (by simp)
    (ofFn_swapAgree a b _ _
      (by simp [hab, hab.symm, hta.symm, htb.symm])
      (by simp)
      (by intro i hia hib; simp [hia, hib])) hshape).2.2.2 C.output
      (petersen_output_not_input C hev a) (petersen_output_not_input C hev b)
  change C.eval _ = C.eval _ at e
  rw [hev, hev, hx, hy] at e
  exact Bool.false_ne_true e

lemma nearMiss_zero_correct :
    nearMiss.eval (List.ofFn (fun _ : Fin 10 => false)) = false := by
  rw [nearMiss_formula]
  rfl

def partnerRaise (t : Fin 10) (x : Fin 10 → Bool) : Fin 10 → Bool :=
  fun i => if i = t then true else x i

def partnerClear01 (x : Fin 10 → Bool) : Fin 10 → Bool :=
  fun i => if i = 0 ∨ i = 1 then false else x i

set_option maxHeartbeats 4000000 in
lemma partner_clear_independent : ∀ x : Fin 10 → Bool,
    petersen x = false → petersen (partnerClear01 x) = false := by
  decide +kernel

set_option maxHeartbeats 4000000 in
lemma partner_independent_extension : ∀ y : Fin 10 → Bool,
    y 0 = false → y 1 = false → petersen y = false →
    ∃ t : Fin 10, t ≠ 0 ∧ t ≠ 1 ∧
      petersen (partnerRaise t y) = false ∧
      (petersen (partnerRaise 0 (partnerRaise t y)) = true ∨
        petersen (partnerRaise 1 (partnerRaise t y)) = true) := by
  decide +kernel

lemma monotone_common_partner_below_petersen (H : (Fin 10 → Bool) → Bool)
    (hmono : Monotone H)
    (hmask : ∀ x : Fin 10 → Bool, petersen x = false →
      H x = H (partnerClear01 x))
    (hflip : ∀ y : Fin 10 → Bool, y 0 = false → y 1 = false → H y = true →
      petersen (partnerRaise 0 y) = petersen y ∧
        petersen (partnerRaise 1 y) = petersen y) :
    ∀ x : Fin 10 → Bool, H x = true → petersen x = true := by
  intro x hx
  cases hf : petersen x with
  | true => rfl
  | false =>
    let y := partnerClear01 x
    have hy : H y = true := by simpa [y, ← hmask x hf] using hx
    have hy0 : y 0 = false := by simp [y, partnerClear01]
    have hy1 : y 1 = false := by simp [y, partnerClear01]
    have hyf : petersen y = false := partner_clear_independent x hf
    obtain ⟨t, ht0, ht1, hzf, hpos⟩ := partner_independent_extension y hy0 hy1 hyf
    have hle : y ≤ partnerRaise t y := by
      intro i
      by_cases hi : i = t <;> simp [partnerRaise, hi]
    have hz : H (partnerRaise t y) = true := by
      have hh := hmono hle
      apply Bool.eq_true_of_true_le
      simpa [hy] using hh
    have hz0 : partnerRaise t y 0 = false := by
      simp [partnerRaise, Ne.symm ht0, hy0]
    have hz1 : partnerRaise t y 1 = false := by
      simp [partnerRaise, Ne.symm ht1, hy1]
    obtain ⟨hzero, hone⟩ := hflip (partnerRaise t y) hz0 hz1 hz
    rcases hpos with hpos | hpos
    · rw [hpos, hzf] at hzero
      contradiction
    · rw [hpos, hzf] at hone
      contradiction

open PEqualNP.CircuitLowerBounds

def partnerAndReadShape (a b : ℕ) (g : Gate) : Prop :=
  g = ⟨.and, [a, b]⟩ ∨ g = ⟨.and, [b, a]⟩

def partnerSuffixReadShape (a b h : ℕ) (g : Gate) : Prop :=
  partnerAndReadShape a b g ∨
    g = ⟨.or, [a, h]⟩ ∨ g = ⟨.or, [h, a]⟩ ∨
    g = ⟨.or, [b, h]⟩ ∨ g = ⟨.or, [h, b]⟩

def partnerRun (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) xs

def commonPartnerValue (pre : List Gate) (h : ℕ) (x : Fin 10 → Bool) : Bool :=
  (partnerRun pre (List.ofFn x)).getD h false

lemma partner_run_length (gs : List Gate) (xs : List Bool) :
    (partnerRun gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [partnerRun]
  | cons g gs ih =>
    simp only [partnerRun, List.foldl_cons]
    rw [← partnerRun, ih]
    simp
    omega

def partnerProductAgree (a b : ℕ) (xs ys : List Bool) : Prop :=
  xs.length = ys.length ∧
    (xs.getD a false && xs.getD b false) = (ys.getD a false && ys.getD b false) ∧
    ∀ i, i ≠ a → i ≠ b → xs.getD i false = ys.getD i false

lemma partner_product_append (a b : ℕ) (xs ys : List Bool) (u v : Bool)
    (ha : a < xs.length) (hb : b < xs.length)
    (h : partnerProductAgree a b xs ys) (huv : u = v) :
    partnerProductAgree a b (xs ++ [u]) (ys ++ [v]) := by
  subst v
  refine ⟨by simp [h.1], ?_, ?_⟩
  · rw [List.getD_append _ _ _ _ ha, List.getD_append _ _ _ _ hb,
      List.getD_append _ _ _ _ (by simpa [h.1] using ha),
      List.getD_append _ _ _ _ (by simpa [h.1] using hb)]
    exact h.2.1
  · intro i hia hib
    by_cases hi : i < xs.length
    · rw [List.getD_append _ _ _ _ hi,
        List.getD_append _ _ _ _ (by simpa [h.1] using hi)]
      exact h.2.2 i hia hib
    · rw [List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by have := h.1; omega), h.1]

lemma partner_product_gate (a b : ℕ) (xs ys : List Bool) (g : Gate)
    (h : partnerProductAgree a b xs ys)
    (hshape : a ∈ effectiveInputs g ∨ b ∈ effectiveInputs g →
      partnerAndReadShape a b g) :
    g.op.eval (g.inputs.map (fun i => xs.getD i false)) =
      g.op.eval (g.inputs.map (fun i => ys.getD i false)) := by
  by_cases hab : a ∈ effectiveInputs g ∨ b ∈ effectiveInputs g
  · rcases hshape hab with rfl | rfl
    · simpa [GateOp.eval] using h.2.1
    · simpa [GateOp.eval, Bool.and_comm] using h.2.1
  · rw [eval_effectiveInputs, eval_effectiveInputs]
    congr 1
    apply List.map_congr_left
    intro i hi
    apply h.2.2 i
    · intro he
      subst i
      exact hab (Or.inl hi)
    · intro he
      subst i
      exact hab (Or.inr hi)

lemma partner_product_fold (a b : ℕ) (xs ys : List Bool) (gs : List Gate)
    (ha : a < xs.length) (hb : b < xs.length)
    (h : partnerProductAgree a b xs ys)
    (hshape : ∀ g ∈ gs, a ∈ effectiveInputs g ∨ b ∈ effectiveInputs g →
      partnerAndReadShape a b g) :
    partnerProductAgree a b (partnerRun gs xs) (partnerRun gs ys) := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g gs ih =>
    simp only [partnerRun, List.foldl_cons]
    apply ih
    · simp; omega
    · simp; omega
    · exact partner_product_append a b xs ys _ _ ha hb h
        (partner_product_gate a b xs ys g h (hshape g (by simp)))
    · intro q hq
      exact hshape q (by simp [hq])

lemma partner_ofFn_productAgree {n : ℕ} (a b : Fin n) (x y : Fin n → Bool)
    (hprod : (x a && x b) = (y a && y b))
    (hrest : ∀ i, i ≠ a → i ≠ b → x i = y i) :
    partnerProductAgree a.val b.val (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp, by simpa [getD_ofFn_val] using hprod, ?_⟩
  intro i hia hib
  by_cases hi : i < n
  · simpa [List.getD, hi] using hrest ⟨i, hi⟩
      (by intro he; exact hia (congrArg Fin.val he))
      (by intro he; exact hib (congrArg Fin.val he))
  · simp [List.getD, hi]

set_option maxHeartbeats 4000000 in
lemma partner_edge01_false : ∀ x : Fin 10 → Bool,
    petersen x = false → (x 0 && x 1) = false := by
  decide +kernel

lemma common_partner_clear_mask (pre : List Gate) (h : ℕ) (hh : 10 ≤ h)
    (hpre : ∀ g ∈ pre, 0 ∈ effectiveInputs g ∨ 1 ∈ effectiveInputs g →
      partnerAndReadShape 0 1 g) :
    ∀ x : Fin 10 → Bool, petersen x = false →
      commonPartnerValue pre h x = commonPartnerValue pre h (partnerClear01 x) := by
  intro x hx
  have he := partner_product_fold 0 1 (List.ofFn x)
    (List.ofFn (partnerClear01 x)) pre (by simp) (by simp)
    (partner_ofFn_productAgree (0 : Fin 10) 1 x (partnerClear01 x)
      (by simp [partnerClear01, partner_edge01_false x hx])
      (by intro i hi0 hi1; simp [partnerClear01, hi0, hi1])) hpre
  exact he.2.2 h (by omega) (by omega)

lemma partner_and_read_symm (a b : ℕ) (g : Gate)
    (h : partnerAndReadShape a b g) : partnerAndReadShape b a g := by
  exact h.symm

lemma partner_suffix_read_symm (a b h : ℕ) (g : Gate)
    (hs : partnerSuffixReadShape a b h g) : partnerSuffixReadShape b a h g := by
  simp only [partnerSuffixReadShape, partnerAndReadShape] at hs ⊢
  tauto

lemma partner_suffix_masked_read (a b h : ℕ) (g : Gate)
    (hab : a ≠ b) (hah : a ≠ h)
    (hs : partnerSuffixReadShape a b h g) (ha : a ∈ effectiveInputs g) :
    maskedReadShape a b h g := by
  rcases hs with (rfl | rfl) | rfl | rfl | rfl | rfl
  · simp [maskedReadShape]
  · simp [maskedReadShape]
  · simp [maskedReadShape]
  · simp [maskedReadShape]
  · simp [effectiveInputs, hab, hah] at ha
  · simp [effectiveInputs, hab, hah] at ha

lemma common_partner_endpoint_flip (a b : Fin 10) (hab : a ≠ b)
    (pre post : List Gate) (out h : ℕ) (hh : 10 ≤ h) (hupper : h < 10 + pre.length)
    (hpre : ∀ g ∈ pre, a.val ∈ effectiveInputs g ∨ b.val ∈ effectiveInputs g →
      partnerAndReadShape a.val b.val g)
    (hpost : ∀ g ∈ post, a.val ∈ effectiveInputs g ∨ b.val ∈ effectiveInputs g →
      partnerSuffixReadShape a.val b.val h g)
    (hev : ∀ x : Fin 10 → Bool,
      ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) = petersen x)
    (x : Fin 10 → Bool) (hb : x b = false) (hx : commonPartnerValue pre h x = true) :
    petersen (partnerRaise a x) = petersen x := by
  have hba : b.val ≠ a.val := by
    intro he
    exact hab (Fin.ext he.symm)
  have ep := uniform_masked_fold false a.val b.val b.val
    (List.ofFn x) (List.ofFn (partnerRaise a x)) pre hba hba
    (ofFn_agreeExcept a _ _ (by intro i hi; simp [partnerRaise, hi]))
    (by simp) (by simp)
    (by rw [getD_ofFn_val]; exact hb) (by rw [getD_ofFn_val]; exact hb)
    (by
      intro g hg ha
      rcases hpre g hg (Or.inl ha) with rfl | rfl <;> simp [uniformReadShape])
  have hbpre : (partnerRun pre (List.ofFn x)).getD b.val false = false := by
    rw [partnerRun, original_wire_preserved _ _ _ (by simp), getD_ofFn_val]
    exact hb
  have es := and_or_masked_fold a.val b.val h
    (partnerRun pre (List.ofFn x)) (partnerRun pre (List.ofFn (partnerRaise a x))) post
    hba (by have := a.isLt; omega) ep
    (by rw [partner_run_length]; simp; omega)
    (by rw [partner_run_length]; simpa using hupper) hbpre hx
    (by
      intro g hg ha
      apply partner_suffix_masked_read a.val b.val h g hba.symm
        (by have := a.isLt; omega) (hpost g hg (Or.inl ha)) ha)
  have e := es.2 out
    (petersen_output_not_input ({gates := pre ++ post, output := out} : Circuit) hev a)
  have ee :
      ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) =
      ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn (partnerRaise a x)) := by
    simpa only [Circuit.eval, Circuit.wires, List.foldl_append, partnerRun] using e
  rw [hev, hev] at ee
  exact ee.symm

lemma common_or_partner_circuit_below_petersen
    (pre post : List Gate) (out h : ℕ) (hh : 10 ≤ h) (hupper : h < 10 + pre.length)
    (hpre : ∀ g ∈ pre, 0 ∈ effectiveInputs g ∨ 1 ∈ effectiveInputs g →
      partnerAndReadShape 0 1 g)
    (hpost : ∀ g ∈ post, 0 ∈ effectiveInputs g ∨ 1 ∈ effectiveInputs g →
      partnerSuffixReadShape 0 1 h g)
    (hev : ∀ x : Fin 10 → Bool,
      ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) = petersen x)
    (hmono : Monotone (commonPartnerValue pre h)) :
    ∀ x : Fin 10 → Bool, commonPartnerValue pre h x = true → petersen x = true := by
  apply monotone_common_partner_below_petersen (commonPartnerValue pre h) hmono
    (common_partner_clear_mask pre h hh hpre)
  intro y hy0 hy1 hy
  constructor
  · exact common_partner_endpoint_flip 0 1 (by decide) pre post out h hh hupper
      hpre hpost hev y hy1 hy
  · apply common_partner_endpoint_flip 1 0 (by decide) pre post out h hh hupper
      _ _ hev y hy0 hy
    · intro g hg hr
      exact partner_and_read_symm 0 1 g (hpre g hg hr.symm)
    · intro g hg hr
      exact partner_suffix_read_symm 0 1 h g (hpost g hg hr.symm)



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def liftRun (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]) xs

def liftRename (cut p i : ℕ) : ℕ :=
  if i = cut then p else if cut < i then i - 1 else i

def liftMapGate (cut p : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (liftRename cut p)⟩

lemma liftRun_length (gs : List Gate) (xs : List Bool) :
    (liftRun gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [liftRun]
  | cons g gs ih =>
    simp only [liftRun, List.foldl_cons] at *
    rw [ih]
    simp
    omega

lemma liftRun_append (gs hs : List Gate) (xs : List Bool) :
    liftRun (gs ++ hs) xs = liftRun hs (liftRun gs xs) := by
  simp [liftRun, List.foldl_append]

lemma liftRun_cons (g : Gate) (gs : List Gate) (xs : List Bool) :
    liftRun (g :: gs) xs =
      liftRun gs (xs ++ [g.op.eval (g.inputs.map (fun i => xs.getD i false))]) := rfl

lemma liftRun_original (gs : List Gate) (xs : List Bool) (i : ℕ)
    (hi : i < xs.length) : (liftRun gs xs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    rw [liftRun_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

lemma lift_rename_append (cut p : ℕ) (xs ys : List Bool) (v : Bool)
    (hp : p < cut) (hlen : xs.length = ys.length + 1) (hcut : cut < xs.length)
    (h : ∀ i, ys.getD (liftRename cut p i) false = xs.getD i false) :
    ∀ i, (ys ++ [v]).getD (liftRename cut p i) false = (xs ++ [v]).getD i false := by
  intro i
  by_cases hi : i < xs.length
  · have hir : liftRename cut p i < ys.length := by
      unfold liftRename
      split_ifs <;> omega
    rw [List.getD_append _ _ _ _ hir, List.getD_append _ _ _ _ hi]
    exact h i
  · have hir : ys.length ≤ liftRename cut p i := by
      unfold liftRename
      split_ifs <;> omega
    have he : liftRename cut p i - ys.length = i - xs.length := by
      unfold liftRename
      split_ifs <;> omega
    rw [List.getD_append_right _ _ _ _ hir,
      List.getD_append_right _ _ _ _ (by omega), he]

lemma lift_rename_insert (xs : List Bool) (p : ℕ) (v : Bool)
    (hp : p < xs.length) (hv : v = xs.getD p false) :
    ∀ i, xs.getD (liftRename xs.length p i) false = (xs ++ [v]).getD i false := by
  intro i
  by_cases hi : i < xs.length
  · have hr : liftRename xs.length p i = i := by
      simp [liftRename, Nat.ne_of_lt hi, Nat.not_lt_of_ge (Nat.le_of_lt hi)]
    rw [hr, List.getD_append _ _ _ _ hi]
  · by_cases he : i = xs.length
    · subst i
      simp [liftRename, hv]
    · have hgt : xs.length < i := by omega
      have hge : xs.length ≤ i - 1 := by omega
      simp only [liftRename, he, ↓reduceIte, hgt]
      have hleft : xs.getD (i - 1) false = false := by
        simp [List.getD, List.getElem?_eq_none hge]
      have hright : (xs ++ [v]).getD i false = false := by
        have hidx : (xs ++ [v]).length ≤ i := by simp; omega
        simp [List.getD, List.getElem?_eq_none hidx]
      rw [hleft, hright]

lemma lift_rename_run (cut p : ℕ) (xs ys : List Bool) (gs : List Gate)
    (hp : p < cut) (hlen : xs.length = ys.length + 1) (hcut : cut < xs.length)
    (h : ∀ i, ys.getD (liftRename cut p i) false = xs.getD i false) :
    ∀ i, (liftRun (gs.map (liftMapGate cut p)) ys).getD (liftRename cut p i) false =
      (liftRun gs xs).getD i false := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g gs ih =>
    have he : (liftMapGate cut p g).op.eval
        ((liftMapGate cut p g).inputs.map (fun i => ys.getD i false)) =
        g.op.eval (g.inputs.map (fun i => xs.getD i false)) := by
      simp only [liftMapGate, List.map_map, Function.comp_def]
      congr 1
      apply List.map_congr_left
      intro i _
      exact h i
    simp only [List.map_cons, liftRun_cons, he]
    apply ih
    · simp [hlen]
    · simp; omega
    · exact lift_rename_append cut p xs ys _ hp hlen hcut h

lemma lift_delete_run (pre post : List Gate) (g : Gate) (xs : List Bool) (p : ℕ)
    (hp : p < xs.length + pre.length)
    (hv : g.op.eval (g.inputs.map (fun i => (liftRun pre xs).getD i false)) =
      (liftRun pre xs).getD p false) :
    ∀ i, (liftRun (pre ++ post.map (liftMapGate (xs.length + pre.length) p)) xs).getD
      (liftRename (xs.length + pre.length) p i) false =
      (liftRun (pre ++ g :: post) xs).getD i false := by
  rw [liftRun_append, liftRun_append, liftRun_cons]
  have hlen := liftRun_length pre xs
  apply lift_rename_run
  · exact hp
  · simp
  · simp; omega
  · rw [← hlen]
    exact lift_rename_insert (liftRun pre xs) p _ (by omega) hv

lemma liftRun_prefix (pre post : List Gate) (xs : List Bool) (i : ℕ)
    (hi : i < xs.length + pre.length) :
    (liftRun (pre ++ post) xs).getD i false = (liftRun pre xs).getD i false := by
  rw [liftRun_append]
  exact liftRun_original post (liftRun pre xs) i (by rw [liftRun_length]; exact hi)


def doubleOrOriginal (pre mid post : List Gate) (a b h out : ℕ) : Circuit :=
  ⟨pre ++ ⟨.or, [a, h]⟩ :: (mid ++ ⟨.or, [b, h]⟩ :: post), out⟩

def doubleOrBody (n : ℕ) (pre mid post : List Gate) (a b : ℕ) : List Gate :=
  pre ++ (mid ++ post.map (liftMapGate (n + (pre.length + (mid.length + 1))) b)).map
    (liftMapGate (n + pre.length) a)

def doubleOrLift (n : ℕ) (pre mid post : List Gate) (a b h out : ℕ) : Circuit :=
  let body := doubleOrBody n pre mid post a b
  let output := liftRename (n + pre.length) a
    (liftRename (n + (pre.length + (mid.length + 1))) b out)
  ⟨body ++ [⟨.or, [output, h]⟩], n + body.length⟩

lemma doubleOrLift_size (n : ℕ) (pre mid post : List Gate) (a b h out : ℕ) :
    (doubleOrLift n pre mid post a b h out).size + 1 =
      (doubleOrOriginal pre mid post a b h out).size := by
  simp [doubleOrLift, doubleOrBody, doubleOrOriginal, Circuit.size]
  omega

lemma lift_top_or_eval (gs : List Gate) (xs : List Bool) (out h : ℕ) :
    (Circuit.mk (gs ++ [⟨.or, [out, h]⟩]) (xs.length + gs.length)).eval xs =
      ((liftRun gs xs).getD out false || (liftRun gs xs).getD h false) := by
  change (liftRun (gs ++ [⟨.or, [out, h]⟩]) xs).getD _ false = _
  rw [liftRun_append, liftRun_cons]
  change ((liftRun gs xs) ++ [_]).getD _ false = _
  rw [← liftRun_length gs xs,
    List.getD_append_right _ _ _ _ (Nat.le_refl _)]
  simp [GateOp.eval]

lemma doubleOrBody_h (n : ℕ) (pre mid post : List Gate) (a b h : ℕ)
    (hh : h < n + pre.length) (x : Fin n → Bool) :
    (liftRun (doubleOrBody n pre mid post a b) (List.ofFn x)).getD h false =
      (liftRun pre (List.ofFn x)).getD h false := by
  apply liftRun_prefix
  simpa using hh

lemma doubleOrOriginal_h (n : ℕ) (pre mid post : List Gate) (a b h out : ℕ)
    (hh : h < n + pre.length) (x : Fin n → Bool) :
    ((doubleOrOriginal pre mid post a b h out).wires (List.ofFn x)).getD h false =
      (liftRun pre (List.ofFn x)).getD h false := by
  apply liftRun_prefix
  simpa using hh

lemma doubleOrBody_eval_of_guard_false (n : ℕ) (pre mid post : List Gate)
    (a b h out : ℕ) (ha : a < n + pre.length)
    (hb : b < n + (pre.length + (mid.length + 1)))
    (hh : h < n + pre.length) (x : Fin n → Bool)
    (hx : (liftRun pre (List.ofFn x)).getD h false = false) :
    (liftRun (doubleOrBody n pre mid post a b) (List.ofFn x)).getD
      (liftRename (n + pre.length) a
        (liftRename (n + (pre.length + (mid.length + 1))) b out)) false =
      (doubleOrOriginal pre mid post a b h out).eval (List.ofFn x) := by
  let g1 : Gate := ⟨.or, [a, h]⟩
  let g2 : Gate := ⟨.or, [b, h]⟩
  let tail := mid ++ post.map (liftMapGate (n + (pre.length + (mid.length + 1))) b)
  have hx2 : (liftRun (pre ++ g1 :: mid) (List.ofFn x)).getD h false = false := by
    rw [liftRun_prefix pre (g1 :: mid) _ h (by simpa using hh), hx]
  have e2 := lift_delete_run (pre ++ g1 :: mid) post g2 (List.ofFn x) b
    (by simpa using hb)
    (by
      simp only [g2, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
        List.any_nil, id_eq, hx2, Bool.or_false]) out
  have e1 := lift_delete_run pre tail g1 (List.ofFn x) a (by simpa using ha)
    (by
      simp only [g1, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
        List.any_nil, id_eq, hx, Bool.or_false])
    (liftRename (n + (pre.length + (mid.length + 1))) b out)
  have e2' :
      (liftRun (pre ++ g1 :: tail) (List.ofFn x)).getD
        (liftRename (n + (pre.length + (mid.length + 1))) b out) false =
        (doubleOrOriginal pre mid post a b h out).eval (List.ofFn x) := by
    simpa [tail, doubleOrOriginal, Circuit.eval, Circuit.wires, liftRun,
      g1, g2, List.append_assoc] using e2
  calc
    _ = (liftRun (pre ++ g1 :: tail) (List.ofFn x)).getD
        (liftRename (n + (pre.length + (mid.length + 1))) b out) false := by
      simpa [doubleOrBody, tail] using e1
    _ = _ := e2'

lemma doubleOrLift_eval (n : ℕ) (pre mid post : List Gate) (a b h out : ℕ)
    (ha : a < n + pre.length) (hb : b < n + (pre.length + (mid.length + 1)))
    (hh : h < n + pre.length)
    (hbelow : ∀ x : Fin n → Bool,
      ((doubleOrOriginal pre mid post a b h out).wires (List.ofFn x)).getD h false = true →
        (doubleOrOriginal pre mid post a b h out).eval (List.ofFn x) = true) :
    ∀ x : Fin n → Bool, (doubleOrLift n pre mid post a b h out).eval (List.ofFn x) =
      (doubleOrOriginal pre mid post a b h out).eval (List.ofFn x) := by
  intro x
  have htop := lift_top_or_eval (doubleOrBody n pre mid post a b) (List.ofFn x)
    (liftRename (n + pre.length) a
      (liftRename (n + (pre.length + (mid.length + 1))) b out)) h
  simp only [List.length_ofFn] at htop
  change (doubleOrLift n pre mid post a b h out).eval (List.ofFn x) = _ at htop
  rw [htop, doubleOrBody_h n pre mid post a b h hh x]
  cases hx : (liftRun pre (List.ofFn x)).getD h false with
  | false =>
    simp only [Bool.or_false]
    exact doubleOrBody_eval_of_guard_false n pre mid post a b h out ha hb hh x hx
  | true =>
    have hf := hbelow x (by rw [doubleOrOriginal_h n pre mid post a b h out hh x]; exact hx)
    simp [hf]


lemma doubleOrLift_fanin (n : ℕ) (pre mid post : List Gate) (a b h out : ℕ)
    (hfanin : FanInTwo (doubleOrOriginal pre mid post a b h out)) :
    FanInTwo (doubleOrLift n pre mid post a b h out) := by
  have hsource (q : Gate) (hq : q ∈ pre ∨ q ∈ mid ∨ q ∈ post) :
      q.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ q.inputs.length ≤ 2 := by
    apply hfanin q
    rcases hq with hp | hm | ht <;> simp [doubleOrOriginal, *]
  intro g hg
  dsimp only [doubleOrLift] at hg
  rcases List.mem_append.mp hg with hg | hg
  · dsimp only [doubleOrBody] at hg
    rcases List.mem_append.mp hg with hg | hg
    · exact hsource g (Or.inl hg)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
      rcases List.mem_append.mp hq with hq | hq
      · obtain ⟨hop, hlen⟩ := hsource q (Or.inr (Or.inl hq))
        exact ⟨hop, by simpa [liftMapGate] using hlen⟩
      · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
        obtain ⟨hop, hlen⟩ := hsource r (Or.inr (Or.inr hr))
        exact ⟨hop, by simpa [liftMapGate] using hlen⟩
  · obtain rfl := List.mem_singleton.mp hg
    exact ⟨by simp, by simp⟩

lemma doubleOrLift_improves (n : ℕ) (pre mid post : List Gate) (a b h out : ℕ)
    (ha : a < n + pre.length) (hb : b < n + (pre.length + (mid.length + 1)))
    (hh : h < n + pre.length)
    (hfanin : FanInTwo (doubleOrOriginal pre mid post a b h out))
    (hbelow : ∀ x : Fin n → Bool,
      ((doubleOrOriginal pre mid post a b h out).wires (List.ofFn x)).getD h false = true →
        (doubleOrOriginal pre mid post a b h out).eval (List.ofFn x) = true) :
    FanInTwo (doubleOrLift n pre mid post a b h out) ∧
      (doubleOrLift n pre mid post a b h out).size + 1 =
        (doubleOrOriginal pre mid post a b h out).size ∧
      ∀ x : Fin n → Bool, (doubleOrLift n pre mid post a b h out).eval (List.ofFn x) =
        (doubleOrOriginal pre mid post a b h out).eval (List.ofFn x) :=
  ⟨doubleOrLift_fanin n pre mid post a b h out hfanin,
    doubleOrLift_size n pre mid post a b h out,
    doubleOrLift_eval n pre mid post a b h out ha hb hh hbelow⟩




open PEqualNP.CircuitLowerBounds

lemma partner_endpoint_flip_of_read_masks (a b : Fin 10) (hab : a ≠ b)
    (pre post : List Gate) (out h : ℕ) (hh : 10 ≤ h) (hupper : h < 10 + pre.length)
    (hpre : ∀ g ∈ pre, a.val ∈ effectiveInputs g →
      uniformReadShape false a.val b.val b.val g)
    (hpost : ∀ g ∈ post, a.val ∈ effectiveInputs g →
      maskedReadShape a.val b.val h g)
    (hev : ∀ x : Fin 10 → Bool,
      ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) = petersen x)
    (x : Fin 10 → Bool) (hb : x b = false) (hx : commonPartnerValue pre h x = true) :
    petersen (partnerRaise a x) = petersen x := by
  have hba : b.val ≠ a.val := by
    intro he
    exact hab (Fin.ext he.symm)
  have ep := uniform_masked_fold false a.val b.val b.val
    (List.ofFn x) (List.ofFn (partnerRaise a x)) pre hba hba
    (ofFn_agreeExcept a _ _ (by intro i hi; simp [partnerRaise, hi]))
    (by simp) (by simp)
    (by rw [getD_ofFn_val]; exact hb) (by rw [getD_ofFn_val]; exact hb) hpre
  have hbpre : (partnerRun pre (List.ofFn x)).getD b.val false = false := by
    rw [partnerRun, original_wire_preserved _ _ _ (by simp), getD_ofFn_val]
    exact hb
  have es := and_or_masked_fold a.val b.val h
    (partnerRun pre (List.ofFn x)) (partnerRun pre (List.ofFn (partnerRaise a x))) post
    hba (by have := a.isLt; omega) ep
    (by rw [partner_run_length]; simp; omega)
    (by rw [partner_run_length]; simpa using hupper) hbpre hx hpost
  have e := es.2 out
    (petersen_output_not_input ({gates := pre ++ post, output := out} : Circuit) hev a)
  have ee :
      ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) =
      ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn (partnerRaise a x)) := by
    simpa only [Circuit.eval, Circuit.wires, List.foldl_append, partnerRun] using e
  rw [hev, hev] at ee
  exact ee.symm

lemma two_or_partners_product_below_petersen
    (pre post : List Gate) (out h0 h1 : ℕ)
    (hh0 : 10 ≤ h0) (hupper0 : h0 < 10 + pre.length)
    (hh1 : 10 ≤ h1) (hupper1 : h1 < 10 + pre.length)
    (hpre : ∀ g ∈ pre, 0 ∈ effectiveInputs g ∨ 1 ∈ effectiveInputs g →
      partnerAndReadShape 0 1 g)
    (hpost0 : ∀ g ∈ post, 0 ∈ effectiveInputs g → maskedReadShape 0 1 h0 g)
    (hpost1 : ∀ g ∈ post, 1 ∈ effectiveInputs g → maskedReadShape 1 0 h1 g)
    (hev : ∀ x : Fin 10 → Bool,
      ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) = petersen x)
    (hmono : Monotone (fun x => commonPartnerValue pre h0 x && commonPartnerValue pre h1 x)) :
    ∀ x : Fin 10 → Bool,
      (commonPartnerValue pre h0 x && commonPartnerValue pre h1 x) = true → petersen x = true := by
  apply monotone_common_partner_below_petersen
    (fun x => commonPartnerValue pre h0 x && commonPartnerValue pre h1 x) hmono
  · intro x hx
    rw [common_partner_clear_mask pre h0 hh0 hpre x hx,
      common_partner_clear_mask pre h1 hh1 hpre x hx]
  · intro y hy0 hy1 hy
    obtain ⟨hyh0, hyh1⟩ := Bool.and_eq_true_iff.mp hy
    constructor
    · apply partner_endpoint_flip_of_read_masks 0 1 (by decide)
        pre post out h0 hh0 hupper0 _ hpost0 hev y hy1 hyh0
      intro g hg hr
      rcases hpre g hg (Or.inl hr) with rfl | rfl <;> simp [uniformReadShape]
    · apply partner_endpoint_flip_of_read_masks 1 0 (by decide)
        pre post out h1 hh1 hupper1 _ hpost1 hev y hy0 hyh1
      intro g hg hr
      rcases hpre g hg (Or.inr hr) with rfl | rfl <;> simp [uniformReadShape]

lemma two_or_partners_below_petersen
    (pre post : List Gate) (out h0 h1 : ℕ)
    (hh0 : 10 ≤ h0) (hupper0 : h0 < 10 + pre.length)
    (hh1 : 10 ≤ h1) (hupper1 : h1 < 10 + pre.length)
    (hpre : ∀ g ∈ pre, 0 ∈ effectiveInputs g ∨ 1 ∈ effectiveInputs g →
      partnerAndReadShape 0 1 g)
    (hpost0 : ∀ g ∈ post, 0 ∈ effectiveInputs g → maskedReadShape 0 1 h0 g)
    (hpost1 : ∀ g ∈ post, 1 ∈ effectiveInputs g → maskedReadShape 1 0 h1 g)
    (hev : ∀ x : Fin 10 → Bool,
      ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) = petersen x)
    (hmono : Monotone (fun x => commonPartnerValue pre h0 x && commonPartnerValue pre h1 x)) :
    ∀ x : Fin 10 → Bool,
      commonPartnerValue pre h0 x = true → commonPartnerValue pre h1 x = true →
      petersen x = true := by
  intro x hx0 hx1
  exact two_or_partners_product_below_petersen pre post out h0 h1
    hh0 hupper0 hh1 hupper1 hpre hpost0 hpost1 hev hmono x (by simp [hx0, hx1])




open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma common_or_partner_strict_improvement
    (pre mid post : List Gate) (out h : ℕ)
    (hh : 10 ≤ h) (hupper : h < 10 + pre.length)
    (hpre : ∀ g ∈ pre, 0 ∈ effectiveInputs g ∨ 1 ∈ effectiveInputs g →
      partnerAndReadShape 0 1 g)
    (hother : ∀ g ∈ mid ++ post, 0 ∈ effectiveInputs g ∨ 1 ∈ effectiveInputs g →
      partnerSuffixReadShape 0 1 h g)
    (hfanin : FanInTwo (doubleOrOriginal pre mid post 0 1 h out))
    (hev : ∀ x : Fin 10 → Bool,
      (doubleOrOriginal pre mid post 0 1 h out).eval (List.ofFn x) = petersen x)
    (hmono : Monotone (commonPartnerValue pre h)) :
    ∃ D : Circuit, FanInTwo D ∧
      D.size + 1 = (doubleOrOriginal pre mid post 0 1 h out).size ∧
      ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = petersen x := by
  have hsuffix : ∀ g ∈ (⟨.or, [0, h]⟩ : Gate) :: (mid ++ ⟨.or, [1, h]⟩ :: post),
      0 ∈ effectiveInputs g ∨ 1 ∈ effectiveInputs g → partnerSuffixReadShape 0 1 h g := by
    intro g hg hr
    rcases List.mem_cons.mp hg with rfl | hg
    · simp [partnerSuffixReadShape]
    · rcases List.mem_append.mp hg with hm | hg
      · exact hother g (List.mem_append_left post hm) hr
      · rcases List.mem_cons.mp hg with rfl | hp
        · simp [partnerSuffixReadShape]
        · exact hother g (List.mem_append_right mid hp) hr
  have hpartner := common_or_partner_circuit_below_petersen pre
    ((⟨.or, [0, h]⟩ : Gate) :: (mid ++ ⟨.or, [1, h]⟩ :: post)) out h
    hh hupper hpre hsuffix hev hmono
  have hbelow : ∀ x : Fin 10 → Bool,
      ((doubleOrOriginal pre mid post 0 1 h out).wires (List.ofFn x)).getD h false = true →
        (doubleOrOriginal pre mid post 0 1 h out).eval (List.ofFn x) = true := by
    intro x hx
    rw [hev]
    apply hpartner x
    change (liftRun pre (List.ofFn x)).getD h false = true
    rw [← doubleOrOriginal_h 10 pre mid post 0 1 h out hupper x]
    exact hx
  obtain ⟨hD, hsize, heval⟩ := doubleOrLift_improves 10 pre mid post 0 1 h out
    (by omega) (by omega) hupper hfanin hbelow
  refine ⟨doubleOrLift 10 pre mid post 0 1 h out, hD, hsize, ?_⟩
  intro x
  rw [heval, hev]

lemma common_or_partner_not_minimal
    (pre mid post : List Gate) (out h : ℕ)
    (hh : 10 ≤ h) (hupper : h < 10 + pre.length)
    (hpre : ∀ g ∈ pre, 0 ∈ effectiveInputs g ∨ 1 ∈ effectiveInputs g →
      partnerAndReadShape 0 1 g)
    (hother : ∀ g ∈ mid ++ post, 0 ∈ effectiveInputs g ∨ 1 ∈ effectiveInputs g →
      partnerSuffixReadShape 0 1 h g)
    (hfanin : FanInTwo (doubleOrOriginal pre mid post 0 1 h out))
    (hev : ∀ x : Fin 10 → Bool,
      (doubleOrOriginal pre mid post 0 1 h out).eval (List.ofFn x) = petersen x)
    (hmono : Monotone (commonPartnerValue pre h))
    (hminimal : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = petersen x) →
      (doubleOrOriginal pre mid post 0 1 h out).size ≤ D.size) : False := by
  obtain ⟨D, hD, hsize, heval⟩ := common_or_partner_strict_improvement pre mid post out h
    hh hupper hpre hother hfanin hev hmono
  have hmin := hminimal D hD heval
  omega



namespace Restriction


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2





lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp





def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

abbrev Stat := Bool ⊕ Nat

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg; subst hg; simp [Ok]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; subst hg; simp [Ok]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg; subst hg; simp [Ok]
  · simp at hg
  · simp at hg

lemma simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

lemma simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · rcases a with ⟨_ | _⟩ | _ <;> rcases b with ⟨_ | _⟩ | _ <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · rcases a with ⟨_ | _⟩ | _ <;> rcases b with ⟨_ | _⟩ | _ <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

lemma toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

lemma elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

lemma Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

lemma Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

lemma inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2


def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

lemma normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

lemma wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]


def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat)) ++ [Sum.inl b]

lemma inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

lemma ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp


def readerCount (k : ℕ) : List Gate → ℕ
  | [] => 0
  | g :: gs => (if k ∈ g.inputs then 1 else 0) + readerCount k gs

lemma elim_len_readers (n k : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      (∀ g ∈ gs, NOk g) → k < acc.1.length →
      (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + readerCount k gs ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim, readerCount]
  | cons g gs ih =>
    intro acc hok hk hc
    have ht := ih (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [elimStep]; omega)
      (by
        obtain ⟨c, hc⟩ := hc
        refine ⟨c, ?_⟩
        simp only [elimStep]
        rw [getD_snoc_ne _ _ _ _ (by omega)]
        exact hc)
    have he : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [he, List.length_cons]
    by_cases hr : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hr, hc⟩⟩
      have hs : (elimStep n acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone]
        simp
      simp only [readerCount, if_pos hr]
      omega
    · have hs : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [readerCount, if_neg hr]
      omega


lemma fix_last_counted (n : ℕ) (b : Bool) (C : Circuit)
    (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y b)) ≠ C.eval (List.ofFn (Fin.snoc y' b))) :
    ∃ E : Circuit, FanInTwo E ∧
      E.size + readerCount n (C.gates.map normGate) ≤ C.size ∧
      ∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y b)) := by
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hC g0 hg0)
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y)
        (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) =
        C.eval (List.ofFn (Fin.snoc y b)) := by
    intro y
    rw [((hinv y).2 C.output).2, hgs, wiresFrom_norm]
    rfl
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | inr j =>
    have hlen := elim_len_readers n n gs (initStats n b, []) hnok
      (by simp [initStats]) ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩
    rw [← hacc] at hlen
    have hok : ∀ g ∈ acc.2, Ok g := by
      rw [hacc]
      exact elim_ok n gs _ (by simp)
    refine ⟨⟨acc.2, j⟩, hok, ?_, ?_⟩
    · simpa [hgs, Circuit.size] using hlen
    · intro y
      have hv := hval y
      rw [hst] at hv
      exact hv

lemma readers_le_of_cofactor_lower (n q s : ℕ) (b : Bool) (C : Circuit)
    (hC : FanInTwo C) (hsize : C.size ≤ s)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y b)) ≠ C.eval (List.ofFn (Fin.snoc y' b)))
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y b))) →
      q ≤ E.size) :
    q + readerCount n (C.gates.map normGate) ≤ s := by
  obtain ⟨E, hE, hbound, hev⟩ := fix_last_counted n b C hC hnc
  have := hlower E hE hev
  omega

def setReaderCount (K : Finset ℕ) : List Gate → ℕ
  | [] => 0
  | g :: gs => (if ∃ k ∈ g.inputs, k ∈ K then 1 else 0) + setReaderCount K gs

lemma elim_len_setReaders (n : ℕ) (K : Finset ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      (∀ g ∈ gs, NOk g) →
      (∀ k ∈ K, k < acc.1.length ∧ ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + setReaderCount K gs ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _; simp [elim, setReaderCount]
  | cons g gs ih =>
    intro acc hok hK
    have ht := ih (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by
        intro k hk
        obtain ⟨hlt, c, hc⟩ := hK k hk
        refine ⟨by simp [elimStep]; omega, c, ?_⟩
        simp only [elimStep]
        rw [getD_snoc_ne _ _ _ _ (by omega)]
        exact hc)
    have he : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [he, List.length_cons]
    by_cases hr : ∃ k ∈ g.inputs, k ∈ K
    · obtain ⟨k, hkg, hk⟩ := hr
      obtain ⟨_, c, hc⟩ := hK k hk
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have hs : (elimStep n acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone]
        simp
      have hr : ∃ k ∈ g.inputs, k ∈ K := ⟨k, hkg, hk⟩
      simp only [setReaderCount, ite_eq_left hr]
      omega
    · have hs : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [setReaderCount, ite_eq_right hr]
      omega

lemma elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have he : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [he, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

lemma elim_status_length (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elim]
  | cons g gs ih =>
    change (elim n gs (elimStep n acc g)).1.length = _
    rw [ih]
    simp [elimStep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma simplify_and_false (m : ℕ) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hz : Sum.inl false ∈ ins) :
    simplify GateOp.and m ins = (none, Sum.inl false) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    (try cases a) <;> (try cases b) <;> simp_all [simplify, simpAnd]
  rcases hz with h | h <;> simp_all

lemma elim_and_reader_bound (n k : ℕ) (pre post : List Gate) (g : Gate)
    (acc : List Stat × List Gate)
    (hok : ∀ h ∈ pre ++ g :: post, NOk h)
    (hk : k < acc.1.length) (hz : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (hg : g.op = GateOp.and) (hread : k ∈ g.inputs) :
    (elim n (pre ++ g :: post) acc).2.length + readerCount k pre + 1 +
        setReaderCount {k, acc.1.length + pre.length} post ≤
      acc.2.length + (pre ++ g :: post).length := by
  let mid := elim n pre acc
  have hm : mid.1.length = acc.1.length + pre.length := elim_status_length n pre acc
  have hmk : k < mid.1.length := by omega
  have hmz : mid.1.getD k (Sum.inl false) = Sum.inl false := by
    rw [elim_getD n k _ pre acc hk, hz]
  have hpre := elim_len_readers n k pre acc
    (fun h hh => hok h (List.mem_append_left _ hh)) hk ⟨false, hz⟩
  have hgood := hok g (List.mem_append_right _ List.mem_cons_self)
  have hs : simplify g.op (n + mid.2.length)
      (g.inputs.map fun i => mid.1.getD i (Sum.inl false)) = (none, Sum.inl false) := by
    rw [hg]
    apply simplify_and_false
    · simpa using hgood.1.2
    · exact List.mem_map.2 ⟨k, hread, hmz⟩
  have hstep : elimStep n mid g = (mid.1 ++ [Sum.inl false], mid.2) := by
    simp only [elimStep]
    rw [hs]
    simp
  have htail := elim_len_setReaders n {k, acc.1.length + pre.length} post
    (elimStep n mid g)
    (fun h hh => hok h (List.mem_append_right _ (List.mem_cons_of_mem _ hh)))
    (by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · refine ⟨by rw [hstep]; simp; omega, false, ?_⟩
        rw [hstep, getD_snoc_ne _ _ _ _ (by omega)]
        exact hmz
      · refine ⟨by rw [hstep]; simp; omega, false, ?_⟩
        rw [hstep, ← hm, getD_snoc_eq])
  have he : elim n (pre ++ g :: post) acc = elim n post (elimStep n mid g) := by
    simp [elim, List.foldl_append, mid]
  rw [he, hstep]
  rw [hstep] at htail
  simp only [List.length_append, List.length_cons]
  change mid.2.length + readerCount k pre ≤ acc.2.length + pre.length at hpre
  dsimp only at htail
  omega

lemma readerCount_append (k : ℕ) (xs ys : List Gate) :
    readerCount k (xs ++ ys) = readerCount k xs + readerCount k ys := by
  induction xs with
  | nil => simp [readerCount]
  | cons g gs ih => simp [readerCount, ih, Nat.add_assoc]

lemma setReaderCount_pair_cons (k l : ℕ) (g : Gate) (gs : List Gate) :
    setReaderCount {k, l} (g :: gs) =
      (if k ∈ g.inputs ∨ l ∈ g.inputs then 1 else 0) + setReaderCount {k, l} gs := by
  have he : (∃ i ∈ g.inputs, i ∈ ({k, l} : Finset ℕ)) ↔ k ∈ g.inputs ∨ l ∈ g.inputs := by
    constructor
    · rintro ⟨i, hi, his⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at his
      rcases his with rfl | rfl
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (hk | hl)
      · exact ⟨k, hk, by simp⟩
      · exact ⟨l, hl, by simp⟩
  simp only [setReaderCount, he]

lemma setReaderCount_pair_ge (k l : ℕ) (gs : List Gate) :
    readerCount k gs ≤ setReaderCount {k, l} gs := by
  induction gs with
  | nil => simp [readerCount, setReaderCount]
  | cons g gs ih =>
    rw [setReaderCount_pair_cons]
    by_cases hk : k ∈ g.inputs <;> by_cases hl : l ∈ g.inputs <;>
      simp_all [readerCount] <;> omega

lemma setReaderCount_pair_extra (k l : ℕ) (gs : List Gate)
    (hx : ∃ g ∈ gs, l ∈ g.inputs ∧ k ∉ g.inputs) :
    readerCount k gs + 1 ≤ setReaderCount {k, l} gs := by
  induction gs with
  | nil => simpa using hx
  | cons g gs ih =>
    rw [setReaderCount_pair_cons]
    obtain ⟨h, hh, hl, hk⟩ := hx
    rcases List.mem_cons.mp hh with rfl | hh
    · have ht := setReaderCount_pair_ge k l gs
      simp only [readerCount, ite_eq_right hk, zero_add, hl, or_true, ite_true]
      omega
    · have ht := ih ⟨h, hh, hl, hk⟩
      by_cases hkg : k ∈ g.inputs <;> by_cases hlg : l ∈ g.inputs <;>
        simp_all [readerCount] <;> omega

lemma elim_and_extra_saving (n k : ℕ) (pre post : List Gate) (g : Gate)
    (acc : List Stat × List Gate)
    (hok : ∀ h ∈ pre ++ g :: post, NOk h)
    (hk : k < acc.1.length) (hz : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (hg : g.op = GateOp.and) (hread : k ∈ g.inputs)
    (hconsumer : ∃ h ∈ post, acc.1.length + pre.length ∈ h.inputs ∧ k ∉ h.inputs) :
    (elim n (pre ++ g :: post) acc).2.length +
        readerCount k (pre ++ g :: post) + 1 ≤
      acc.2.length + (pre ++ g :: post).length := by
  have hb := elim_and_reader_bound n k pre post g acc hok hk hz hg hread
  have he := setReaderCount_pair_extra k (acc.1.length + pre.length) post hconsumer
  rw [readerCount_append]
  simp only [readerCount, ite_eq_left hread]
  omega

lemma fix_last_with_savings (n q : ℕ) (b : Bool) (C : Circuit)
    (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y b)) ≠ C.eval (List.ofFn (Fin.snoc y' b)))
    (hbudget : (elim n (C.gates.map normGate) (initStats n b, [])).2.length + q ≤ C.size) :
    ∃ E : Circuit, FanInTwo E ∧ E.size + q ≤ C.size ∧
      ∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y b)) := by
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hC g0 hg0)
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y)
        (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) =
        C.eval (List.ofFn (Fin.snoc y b)) := by
    intro y
    rw [((hinv y).2 C.output).2, hgs, wiresFrom_norm]
    rfl
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | inr j =>
    have hok : ∀ g ∈ acc.2, Ok g := by
      rw [hacc]
      exact elim_ok n gs _ (by simp)
    refine ⟨⟨acc.2, j⟩, hok, hbudget, ?_⟩
    intro y
    have hv := hval y
    rw [hst] at hv
    exact hv

lemma fix_false_and_extra (n : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate)
    (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hgs : C.gates.map normGate = pre ++ g :: post)
    (hg : g.op = GateOp.and) (hread : n ∈ g.inputs)
    (hconsumer : ∃ h ∈ post, n + 1 + pre.length ∈ h.inputs ∧ n ∉ h.inputs) :
    ∃ E : Circuit, FanInTwo E ∧
      E.size + readerCount n (C.gates.map normGate) + 1 ≤ C.size ∧
      ∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false)) := by
  have hok : ∀ h ∈ pre ++ g :: post, NOk h := by
    intro h hh
    rw [← hgs] at hh
    obtain ⟨h0, hh0, rfl⟩ := List.mem_map.1 hh
    exact normGate_nok h0 (hC h0 hh0)
  have hb := elim_and_extra_saving n n pre post g (initStats n false, []) hok
    (by simp [initStats]) (getD_snoc_len _ _ _ _ (by simp)) hg hread
    (by simpa [initStats] using hconsumer)
  have hlen : (pre ++ g :: post).length = C.size := by
    rw [← hgs]
    simp [Circuit.size]
  have hbudget : (elim n (C.gates.map normGate) (initStats n false, [])).2.length +
      (readerCount n (C.gates.map normGate) + 1) ≤ C.size := by
    simpa only [hgs, hlen, List.length_nil, Nat.zero_add, Nat.add_assoc] using hb
  obtain ⟨E, hE, hsize, hev⟩ := fix_last_with_savings n
    (readerCount n (C.gates.map normGate) + 1) false C hC hnc hbudget
  exact ⟨E, hE, by omega, hev⟩

lemma and_readers_le_of_cofactor_lower (n q s : ℕ) (C : Circuit)
    (pre post : List Gate) (g : Gate)
    (hC : FanInTwo C) (hsize : C.size ≤ s)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false))) →
      q ≤ E.size)
    (hgs : C.gates.map normGate = pre ++ g :: post)
    (hg : g.op = GateOp.and) (hread : n ∈ g.inputs)
    (hconsumer : ∃ h ∈ post, n + 1 + pre.length ∈ h.inputs ∧ n ∉ h.inputs) :
    q + readerCount n (C.gates.map normGate) + 1 ≤ s := by
  obtain ⟨E, hE, hbound, hev⟩ := fix_false_and_extra n C pre post g hC hnc
    hgs hg hread hconsumer
  have := hlower E hE hev
  omega

namespace Consumer

open PEqualNP.CircuitLowerBounds

lemma two_inputs_of_distinct (l : List ℕ) (v w : ℕ) (hvw : v ≠ w)
    (hl : l.length ≤ 2) (hv : v ∈ l) (hw : w ∈ l) :
    l = [v, w] ∨ l = [w, v] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp at hv
  · simp only [List.mem_singleton] at hv hw
    exact False.elim (hvw (hv.trans hw.symm))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv hw
    rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
    · exact False.elim (hvw rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact False.elim (hvw rfl)
  · simp at hl

lemma and_value_implies_input {A : Type} (F : A → ℕ → Bool) (g : Gate) (v w : ℕ)
    (hop : g.op = GateOp.and) (hv : v ∈ g.inputs)
    (heval : ∀ a, F a w = g.op.eval (g.inputs.map (F a))) :
    ∀ a, F a w = true → F a v = true := by
  intro a ha
  rw [heval a, hop] at ha
  have hall : ∀ b ∈ g.inputs.map (F a), b = true := by
    simpa [GateOp.eval, List.all_eq_true] using ha
  exact hall _ (List.mem_map.2 ⟨v, hv, rfl⟩)

lemma consumer_absorbs {A : Type} (F : A → ℕ → Bool) (g : Gate) (v w out : ℕ)
    (hvw : v ≠ w) (hv : v ∈ g.inputs) (hw : w ∈ g.inputs)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2) (hnot : g.op = GateOp.not → g.inputs.length ≤ 1)
    (heval : ∀ a, F a out = g.op.eval (g.inputs.map (F a)))
    (himp : ∀ a, F a w = true → F a v = true) :
    (∀ a, F a out = F a w) ∨ (∀ a, F a out = F a v) := by
  have hins := two_inputs_of_distinct g.inputs v w hvw hlen hv hw
  rcases hop with hop | hop | hop
  · left
    intro a
    rw [heval a, hop]
    rcases hins with hins | hins <;> rw [hins] <;>
      cases hvv : F a v <;> cases hww : F a w <;>
      simp_all [GateOp.eval]
  · right
    intro a
    rw [heval a, hop]
    rcases hins with hins | hins <;> rw [hins] <;>
      cases hvv : F a v <;> cases hww : F a w <;>
      simp_all [GateOp.eval]
  · have := hnot hop
    rcases hins with hins | hins <;> simp_all

lemma consumer_avoids_raw_input {A : Type} (F : A → ℕ → Bool)
    (source consumer : Gate) (n v p q : ℕ) (hv : v < n) (hpq : p < q)
    (hsource : source.op = GateOp.and) (hsourcev : v ∈ source.inputs)
    (hread : n + p ∈ consumer.inputs)
    (hop : consumer.op = GateOp.and ∨ consumer.op = GateOp.or ∨ consumer.op = GateOp.not)
    (hlen : consumer.inputs.length ≤ 2)
    (hnot : consumer.op = GateOp.not → consumer.inputs.length ≤ 1)
    (hsourceval : ∀ a, F a (n + p) = source.op.eval (source.inputs.map (F a)))
    (hconsumerval : ∀ a, F a (n + q) = consumer.op.eval (consumer.inputs.map (F a)))
    (hnoalias : ∀ j, j < n + q → ¬ ∀ a, F a (n + q) = F a j) :
    v ∉ consumer.inputs := by
  intro hraw
  have himp := and_value_implies_input F source v (n + p) hsource hsourcev hsourceval
  rcases consumer_absorbs F consumer v (n + p) (n + q) (by omega) hraw hread
      hop hlen hnot hconsumerval himp with ha | ha
  · exact hnoalias (n + p) (by omega) ha
  · exact hnoalias v (by omega) ha

lemma live_consumer_avoids_raw_input {A : Type} (F : A → ℕ → Bool)
    (gs : List Gate) (n v p : ℕ) (source : Gate) (hv : v < n)
    (hsource : gs[p]? = some source) (hsourceop : source.op = GateOp.and)
    (hsourcev : v ∈ source.inputs)
    (hnormal : ∀ (q : ℕ) (g : Gate), gs[q]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 ∧ (g.op = GateOp.not → g.inputs.length ≤ 1))
    (hvalues : ∀ (q : ℕ) (g : Gate), gs[q]? = some g →
      ∀ a, F a (n + q) = g.op.eval (g.inputs.map (F a)))
    (hnoalias : ∀ q, q < gs.length → ∀ j, j < n + q →
      ¬ ∀ a, F a (n + q) = F a j)
    (hlive : ∃ q, p < q ∧ ∃ g, gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∃ q g, p < q ∧ gs[q]? = some g ∧ n + p ∈ g.inputs ∧ v ∉ g.inputs := by
  obtain ⟨q, hpq, g, hq, hread⟩ := hlive
  have hqlt : q < gs.length := by
    by_contra h
    have hnone : gs[q]? = none := List.getElem?_eq_none_iff.2 (by omega)
    rw [hnone] at hq
    cases hq
  obtain ⟨hop, hlen, hnot⟩ := hnormal q g hq
  refine ⟨q, g, hpq, hq, hread, ?_⟩
  exact consumer_avoids_raw_input F source g n v p q hv hpq hsourceop hsourcev
    hread hop hlen hnot (hvalues p source hsource) (hvalues q g hq) (hnoalias q hqlt)

end Consumer




open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma readerCount_pos_iff (k : ℕ) (gs : List Gate) :
    0 < readerCount k gs ↔ ∃ g ∈ gs, k ∈ g.inputs := by
  induction gs with
  | nil => simp [readerCount]
  | cons g gs ih =>
    by_cases hk : k ∈ g.inputs <;> simp [readerCount, hk, ih]

lemma setReaderCount_three_of_two_consumers (k l : ℕ) (gs : List Gate)
    (htwo : 2 ≤ readerCount l gs)
    (hraw : ∃ g ∈ gs, k ∈ g.inputs)
    (havoid : ∀ g ∈ gs, l ∈ g.inputs → k ∉ g.inputs) :
    3 ≤ setReaderCount {k, l} gs := by
  obtain ⟨g, hg, hk⟩ := hraw
  have hl : l ∉ g.inputs := by
    intro hl
    exact havoid g hg hl hk
  have he := setReaderCount_pair_extra l k gs ⟨g, hg, hk, hl⟩
  rw [Finset.pair_comm l k] at he
  omega

lemma fix_false_first_and_two_consumers (n : ℕ) (C : Circuit) (g : Gate) (post : List Gate)
    (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hgs : C.gates.map normGate = g :: post)
    (hg : g.op = GateOp.and) (hread : n ∈ g.inputs)
    (hraw : ∃ q ∈ post, n ∈ q.inputs)
    (htwo : 2 ≤ readerCount (n + 1) post)
    (havoid : ∀ q ∈ post, n + 1 ∈ q.inputs → n ∉ q.inputs) :
    ∃ E : Circuit, FanInTwo E ∧ E.size + 4 ≤ C.size ∧
      ∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false)) := by
  have hok : ∀ q ∈ ([] : List Gate) ++ g :: post, NOk q := by
    intro q hq
    have hqm : q ∈ C.gates.map normGate := by simpa [hgs] using hq
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hqm
    exact normGate_nok q0 (hC q0 hq0)
  have hbase := elim_and_reader_bound n n [] post g (initStats n false, []) hok
    (by simp [initStats]) (getD_snoc_len _ _ _ _ (by simp)) hg hread
  have hbound : (elim n (g :: post) (initStats n false, [])).2.length + 1 +
      setReaderCount {n, n + 1} post ≤ (g :: post).length := by
    simpa [initStats, readerCount] using hbase
  have hthree := setReaderCount_three_of_two_consumers n (n + 1) post htwo hraw havoid
  have hlen : (g :: post).length = C.size := by
    rw [← hgs]
    simp [Circuit.size]
  have hbudget : (elim n (C.gates.map normGate) (initStats n false, [])).2.length + 4 ≤ C.size := by
    rw [hgs]
    rw [hlen] at hbound
    omega
  exact fix_last_with_savings n 4 false C hC hnc hbudget

lemma first_and_has_at_most_one_consumer (n : ℕ) (C : Circuit) (g : Gate) (post : List Gate)
    (hC : FanInTwo C) (hsize : C.size ≤ 19)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false))) →
      16 ≤ E.size)
    (hgs : C.gates.map normGate = g :: post)
    (hg : g.op = GateOp.and) (hread : n ∈ g.inputs)
    (hraw : ∃ q ∈ post, n ∈ q.inputs)
    (havoid : ∀ q ∈ post, n + 1 ∈ q.inputs → n ∉ q.inputs) :
    readerCount (n + 1) post ≤ 1 := by
  by_contra hn
  have htwo : 2 ≤ readerCount (n + 1) post := by omega
  obtain ⟨E, hE, hbound, heval⟩ :=
    fix_false_first_and_two_consumers n C g post hC hnc hgs hg hread hraw htwo havoid
  have hlow := hlower E hE heval
  omega


lemma first_and_consumers_avoid_input {A : Type} (F : A → ℕ → Bool)
    (n v : ℕ) (source : Gate) (post : List Gate) (hv : v < n + 1)
    (hsource : source.op = GateOp.and) (hsourcev : v ∈ source.inputs)
    (hnormal : ∀ g ∈ source :: post, NOk g)
    (hvalues : ∀ (q : ℕ) (g : Gate), (source :: post)[q]? = some g →
      ∀ x, F x (n + 1 + q) = g.op.eval (g.inputs.map (F x)))
    (hnoalias : ∀ q, q < (source :: post).length → ∀ j, j < n + 1 + q →
      ¬ ∀ x, F x (n + 1 + q) = F x j) :
    ∀ g ∈ post, n + 1 ∈ g.inputs → v ∉ g.inputs := by
  intro g hg hread
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hg
  have hjfull : (source :: post)[j + 1]? = some g := by simpa using hj
  have hjlen : j + 1 < (source :: post).length :=
    (List.getElem?_eq_some_iff.mp hjfull).1
  have hgok := hnormal g (List.mem_cons_of_mem source hg)
  have hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not := by
    simpa using hgok.1.1
  exact Consumer.consumer_avoids_raw_input F source g (n + 1) v 0 (j + 1)
    hv (by omega) hsource hsourcev (by simpa using hread) hop hgok.1.2 hgok.2
    (by simpa using hvalues 0 source (by simp))
    (hvalues (j + 1) g hjfull) (hnoalias (j + 1) hjlen)




open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma elim_and_set_reader_bound (n : ℕ) (K : Finset ℕ) (k : ℕ)
    (pre post : List Gate) (g : Gate) (acc : List Stat × List Gate)
    (hok : ∀ q ∈ pre ++ g :: post, NOk q)
    (hK : ∀ j ∈ K, j < acc.1.length ∧
      ∃ c, acc.1.getD j (Sum.inl false) = Sum.inl c)
    (hk : k ∈ K) (hz : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (hg : g.op = GateOp.and) (hread : k ∈ g.inputs) :
    (elim n (pre ++ g :: post) acc).2.length + setReaderCount K pre + 1 +
      setReaderCount (insert (acc.1.length + pre.length) K) post ≤
        acc.2.length + (pre ++ g :: post).length := by
  let mid := elim n pre acc
  have hm : mid.1.length = acc.1.length + pre.length := elim_status_length n pre acc
  have hklt : k < acc.1.length := (hK k hk).1
  have hmz : mid.1.getD k (Sum.inl false) = Sum.inl false := by
    rw [elim_getD n k _ pre acc hklt, hz]
  have hpre := elim_len_setReaders n K pre acc
    (fun q hq => hok q (List.mem_append_left _ hq)) hK
  have hgood := hok g (List.mem_append_right _ List.mem_cons_self)
  have hs : simplify g.op (n + mid.2.length)
      (g.inputs.map fun i => mid.1.getD i (Sum.inl false)) = (none, Sum.inl false) := by
    rw [hg]
    apply simplify_and_false
    · simpa using hgood.1.2
    · exact List.mem_map.2 ⟨k, hread, hmz⟩
  have hstep : elimStep n mid g = (mid.1 ++ [Sum.inl false], mid.2) := by
    simp only [elimStep]
    rw [hs]
    simp
  have htail := elim_len_setReaders n (insert (acc.1.length + pre.length) K) post
    (elimStep n mid g)
    (fun q hq => hok q (List.mem_append_right _ (List.mem_cons_of_mem _ hq)))
    (by
      intro j hj
      simp only [Finset.mem_insert] at hj
      rcases hj with rfl | hj
      · refine ⟨by rw [hstep]; simp; omega, false, ?_⟩
        rw [hstep, ← hm, getD_snoc_eq]
      · obtain ⟨hjlt, c, hjc⟩ := hK j hj
        refine ⟨by rw [hstep]; simp; omega, c, ?_⟩
        rw [hstep, getD_snoc_ne _ _ _ _ (by omega)]
        exact (elim_getD n j _ pre acc hjlt).trans hjc)
  have he : elim n (pre ++ g :: post) acc = elim n post (elimStep n mid g) := by
    simp [elim, List.foldl_append, mid]
  rw [he, hstep]
  rw [hstep] at htail
  simp only [List.length_append, List.length_cons]
  change mid.2.length + setReaderCount K pre ≤ acc.2.length + pre.length at hpre
  dsimp only at htail
  omega


lemma chain_setReaderCount_append (K : Finset ℕ) (xs ys : List Gate) :
    setReaderCount K (xs ++ ys) = setReaderCount K xs + setReaderCount K ys := by
  induction xs with
  | nil => simp [setReaderCount]
  | cons g gs ih => simp [setReaderCount, ih, Nat.add_assoc]

lemma chain_setReaderCount_mono (K L : Finset ℕ) (hKL : K ⊆ L) (gs : List Gate) :
    setReaderCount K gs ≤ setReaderCount L gs := by
  induction gs with
  | nil => simp [setReaderCount]
  | cons g gs ih =>
    by_cases hk : ∃ k ∈ g.inputs, k ∈ K
    · have hl : ∃ k ∈ g.inputs, k ∈ L := by
        obtain ⟨k, hkg, hkK⟩ := hk
        exact ⟨k, hkg, hKL hkK⟩
      simp only [setReaderCount, ite_eq_left hk, ite_eq_left hl]
      omega
    · by_cases hl : ∃ k ∈ g.inputs, k ∈ L <;>
        simp only [setReaderCount, ite_eq_right hk, hl, ↓reduceIte] <;> omega

lemma chain_setReaderCount_insert_extra (K : Finset ℕ) (j : ℕ) (gs : List Gate)
    (hx : ∃ g ∈ gs, j ∈ g.inputs ∧ ∀ k ∈ K, k ∉ g.inputs) :
    setReaderCount K gs + 1 ≤ setReaderCount (insert j K) gs := by
  induction gs with
  | nil => simpa using hx
  | cons g gs ih =>
    obtain ⟨q, hq, hqj, hqK⟩ := hx
    rcases List.mem_cons.mp hq with he | hq
    · subst q
      have hk : ¬ ∃ k ∈ g.inputs, k ∈ K := by
        rintro ⟨k, hkg, hkK⟩
        exact hqK k hkK hkg
      have hl : ∃ k ∈ g.inputs, k ∈ insert j K := ⟨j, hqj, by simp⟩
      have ht := chain_setReaderCount_mono K (insert j K) (by intro k hk; simp [hk]) gs
      simp only [setReaderCount, ite_eq_right hk, ite_eq_left hl]
      omega
    · have ht := ih ⟨q, hq, hqj, hqK⟩
      by_cases hk : ∃ k ∈ g.inputs, k ∈ K
      · have hl : ∃ k ∈ g.inputs, k ∈ insert j K := by
          obtain ⟨k, hkg, hkK⟩ := hk
          exact ⟨k, hkg, by simp [hkK]⟩
        simp only [setReaderCount, ite_eq_left hk, ite_eq_left hl]
        omega
      · by_cases hl : ∃ k ∈ g.inputs, k ∈ insert j K <;>
          simp only [setReaderCount, ite_eq_right hk, hl, ↓reduceIte] <;> omega

lemma elim_and_set_reader_extra_saving (n : ℕ) (K : Finset ℕ) (k : ℕ)
    (pre post : List Gate) (g : Gate) (acc : List Stat × List Gate)
    (hok : ∀ q ∈ pre ++ g :: post, NOk q)
    (hK : ∀ j ∈ K, j < acc.1.length ∧
      ∃ c, acc.1.getD j (Sum.inl false) = Sum.inl c)
    (hk : k ∈ K) (hz : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (hg : g.op = GateOp.and) (hread : k ∈ g.inputs)
    (hconsumer : ∃ q ∈ post, acc.1.length + pre.length ∈ q.inputs ∧
      ∀ j ∈ K, j ∉ q.inputs) :
    (elim n (pre ++ g :: post) acc).2.length +
      setReaderCount K (pre ++ g :: post) + 1 ≤
        acc.2.length + (pre ++ g :: post).length := by
  have hb := elim_and_set_reader_bound n K k pre post g acc hok hK hk hz hg hread
  have he := chain_setReaderCount_insert_extra K (acc.1.length + pre.length) post hconsumer
  have hr : ∃ j ∈ g.inputs, j ∈ K := ⟨k, hread, hk⟩
  rw [chain_setReaderCount_append]
  simp only [setReaderCount, ite_eq_left hr]
  omega


lemma chain_readerCount_positive (k : ℕ) (gs : List Gate)
    (hx : ∃ g ∈ gs, k ∈ g.inputs) : 1 ≤ readerCount k gs := by
  induction gs with
  | nil => simp at hx
  | cons g gs ih =>
    obtain ⟨q, hq, hk⟩ := hx
    rcases List.mem_cons.mp hq with hq | hq
    · subst q
      simp [readerCount, hk]
    · have ht := ih ⟨q, hq, hk⟩
      simp only [readerCount]
      omega

lemma fix_false_first_and_and_consumer (n : ℕ) (C : Circuit)
    (g q : Gate) (pre post : List Gate)
    (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hgs : C.gates.map normGate = g :: (pre ++ q :: post))
    (hg : g.op = GateOp.and) (hread : n ∈ g.inputs)
    (hq : q.op = GateOp.and) (hqread : n + 1 ∈ q.inputs) (hqavoid : n ∉ q.inputs)
    (hraw : ∃ r ∈ pre ++ q :: post, n ∈ r.inputs)
    (hconsumer : ∃ r ∈ post, n + 2 + pre.length ∈ r.inputs ∧
      ∀ j ∈ ({n, n + 1} : Finset ℕ), j ∉ r.inputs) :
    ∃ E : Circuit, FanInTwo E ∧ E.size + 4 ≤ C.size ∧
      ∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false)) := by
  have hok : ∀ r ∈ g :: (pre ++ q :: post), NOk r := by
    intro r hr
    have hrm : r ∈ C.gates.map normGate := by simpa [hgs] using hr
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hrm
    exact normGate_nok r0 (hC r0 hr0)
  let acc0 : List Stat × List Gate := (initStats n false, [])
  let acc1 : List Stat × List Gate := (initStats n false ++ [Sum.inl false], [])
  have hinitlen : (initStats n false).length = n + 1 := by simp [initStats]
  have hinitfalse : (initStats n false).getD n (Sum.inl false) = Sum.inl false :=
    getD_snoc_len _ _ _ _ (by simp)
  have hs : simplify g.op (n + acc0.2.length)
      (g.inputs.map fun i => acc0.1.getD i (Sum.inl false)) = (none, Sum.inl false) := by
    rw [hg]
    apply simplify_and_false
    · simpa using (hok g List.mem_cons_self).1.2
    · exact List.mem_map.mpr ⟨n, hread, hinitfalse⟩
  have hstep : elimStep n acc0 g = acc1 := by
    simp only [elimStep]
    rw [hs]
    rfl
  have haccraw : acc1.1.getD n (Sum.inl false) = Sum.inl false := by
    change (initStats n false ++ [Sum.inl false]).getD n (Sum.inl false) = _
    rw [getD_snoc_ne _ _ _ _ (by omega)]
    exact hinitfalse
  have haccfirst : acc1.1.getD (n + 1) (Sum.inl false) = Sum.inl false := by
    change (initStats n false ++ [Sum.inl false]).getD (n + 1) (Sum.inl false) = _
    rw [← hinitlen, getD_snoc_eq]
  have hK : ∀ j ∈ ({n, n + 1} : Finset ℕ), j < acc1.1.length ∧
      ∃ c, acc1.1.getD j (Sum.inl false) = Sum.inl c := by
    intro j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hj
    rcases hj with rfl | rfl
    · exact ⟨by simp [acc1, initStats], false, haccraw⟩
    · exact ⟨by simp [acc1, initStats], false, haccfirst⟩
  have ht := elim_and_set_reader_extra_saving n {n, n + 1} (n + 1)
    pre post q acc1 (fun r hr => hok r (List.mem_cons_of_mem g hr)) hK
    (by simp) haccfirst hq hqread
    (by simpa [acc1, initStats, Nat.add_assoc] using hconsumer)
  have hrawcount := chain_readerCount_positive n (pre ++ q :: post) hraw
  have hcount := setReaderCount_pair_extra n (n + 1) (pre ++ q :: post)
    ⟨q, List.mem_append_right pre List.mem_cons_self, hqread, hqavoid⟩
  have hlen : (g :: (pre ++ q :: post)).length = C.size := by
    rw [← hgs]
    simp [Circuit.size]
  have hrun : elim n (g :: (pre ++ q :: post)) acc0 =
      elim n (pre ++ q :: post) acc1 := by
    change elim n (pre ++ q :: post) (elimStep n acc0 g) = _
    rw [hstep]
  have hbudget : (elim n (C.gates.map normGate) (initStats n false, [])).2.length + 4 ≤ C.size := by
    change (elim n (C.gates.map normGate) acc0).2.length + 4 ≤ C.size
    rw [hgs, hrun]
    change (elim n (pre ++ q :: post) acc1).2.length +
      setReaderCount {n, n + 1} (pre ++ q :: post) + 1 ≤
        0 + (pre ++ q :: post).length at ht
    simp only [List.length_cons] at hlen
    omega
  exact fix_last_with_savings n 4 false C hC hnc hbudget



namespace InputRename


def wire {n : ℕ} (s : Equiv.Perm (Fin n)) (i : ℕ) : ℕ :=
  if h : i < n then s ⟨i, h⟩ else i

def gate {n : ℕ} (s : Equiv.Perm (Fin n)) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wire s)⟩

def circuit {n : ℕ} (s : Equiv.Perm (Fin n)) (C : Circuit) : Circuit :=
  ⟨C.gates.map (gate s), wire s C.output⟩

lemma wire_ge {n : ℕ} (s : Equiv.Perm (Fin n)) {i : ℕ} (hi : n ≤ i) :
    wire s i = i := by simp [wire, Nat.not_lt.mpr hi]

lemma wire_ne_ge {n : ℕ} (s : Equiv.Perm (Fin n)) {i j : ℕ}
    (hj : n ≤ j) (hne : i ≠ j) : wire s i ≠ j := by
  by_cases hi : i < n
  · have hlt := (s ⟨i, hi⟩).isLt
    simp only [wire, dif_pos hi]
    omega
  · simpa [wire, hi] using hne

lemma wires_relation {n : ℕ} (s : Equiv.Perm (Fin n)) (gs : List Gate) :
    ∀ w w' : List Bool, w'.length = w.length → n ≤ w.length →
      (∀ i, w'.getD (wire s i) false = w.getD i false) →
      ∀ i, (wiresFrom (gs.map (gate s)) w').getD (wire s i) false =
        (wiresFrom gs w).getD i false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hlen hn hrel
    have hv : (gate s g).op.eval ((gate s g).inputs.map fun i => w'.getD i false) =
        g.op.eval (g.inputs.map fun i => w.getD i false) := by
      unfold gate
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact hrel i
    change ∀ i,
      (wiresFrom (gs.map (gate s))
        (w' ++ [(gate s g).op.eval ((gate s g).inputs.map fun j => w'.getD j false)])).getD
          (wire s i) false =
      (wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun j => w.getD j false)])).getD i false
    rw [hv]
    apply ih
    · simp [hlen]
    · simp; omega
    · intro i
      by_cases hi : i = w.length
      · subst i
        rw [wire_ge s hn, getD_snoc_eq, ← hlen, getD_snoc_eq]
      · rw [getD_snoc_ne _ _ _ _ hi,
          getD_snoc_ne _ _ _ _ (by rw [hlen]; exact wire_ne_ge s hn hi)]
        exact hrel i

lemma eval {n : ℕ} (s : Equiv.Perm (Fin n)) (C : Circuit) (x : Fin n → Bool) :
    (circuit s C).eval (List.ofFn (x ∘ s.symm)) = C.eval (List.ofFn x) := by
  apply wires_relation s C.gates (List.ofFn x) (List.ofFn (x ∘ s.symm))
    (by simp) (by simp) _ C.output
  intro i
  by_cases hi : i < n
  · simp [wire, hi, Function.comp_def]
  · have he : wire s i = i := wire_ge s (by omega)
    rw [he, List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi),
      List.getD_eq_default _ _ (by simpa using Nat.le_of_not_gt hi)]

lemma size {n : ℕ} (s : Equiv.Perm (Fin n)) (C : Circuit) :
    (circuit s C).size = C.size := by simp [circuit, Circuit.size]

lemma fanInTwo {n : ℕ} (s : Equiv.Perm (Fin n)) (C : Circuit) (hC : FanInTwo C) :
    FanInTwo (circuit s C) := by
  intro g hg
  obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
  obtain ⟨hop, hlen⟩ := hC g0 hg0
  exact ⟨hop, by simpa [gate] using hlen⟩

lemma wire_preimage {n : ℕ} (s : Equiv.Perm (Fin n)) (i : Fin n) (k : ℕ) :
    wire s k = i ↔ k = (s.symm i : ℕ) := by
  by_cases hk : k < n
  · constructor
    · intro h
      have he : s ⟨k, hk⟩ = i := Fin.ext (by simpa [wire, hk] using h)
      have := congrArg (fun j : Fin n => (s.symm j : ℕ)) he
      simpa using this
    · intro h
      subst k
      simp [wire]
  · have hi := i.isLt
    have hsi := (s.symm i).isLt
    simp only [wire, dif_neg hk]
    constructor <;> intro h <;> omega

lemma norm_gate {n : ℕ} (s : Equiv.Perm (Fin n)) (g : Gate) :
    normGate (gate s g) = gate s (normGate g) := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp [normGate, gate, List.map_take]

lemma readerCount_map {n : ℕ} (s : Equiv.Perm (Fin n)) (i : Fin n) (gs : List Gate) :
    readerCount i (gs.map (gate s)) = readerCount (s.symm i) gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hm : (i : ℕ) ∈ (gate s g).inputs ↔ (s.symm i : ℕ) ∈ g.inputs := by
      change (i : ℕ) ∈ g.inputs.map (wire s) ↔ _
      simp only [List.mem_map, wire_preimage]
      constructor
      · rintro ⟨j, hj, he⟩
        simpa only [he] using hj
      · intro hi
        exact ⟨s.symm i, hi, rfl⟩
    simp only [List.map_cons, readerCount, hm, ih]

lemma effective_readers {n : ℕ} (s : Equiv.Perm (Fin n)) (i : Fin n) (C : Circuit) :
    readerCount i ((circuit s C).gates.map normGate) =
      readerCount (s.symm i) (C.gates.map normGate) := by
  have he : (circuit s C).gates.map normGate = (C.gates.map normGate).map (gate s) := by
    simp only [circuit, List.map_map]
    apply List.map_congr_left
    intro g _
    exact norm_gate s g
  rw [he, readerCount_map]

lemma eval_relabel {n : ℕ} (s : Equiv.Perm (Fin n)) (C : Circuit) (y : Fin n → Bool) :
    (circuit s C).eval (List.ofFn y) = C.eval (List.ofFn (y ∘ s)) := by
  simpa [Function.comp_def] using eval s C (y ∘ s)


end InputRename



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma simplify_all_constants (op : GateOp) (m : ℕ) (ins : List Stat)
    (hc : ∀ s ∈ ins, ∃ b, s = Sum.inl b) :
    ∃ b, simplify op m ins = (none, Sum.inl b) := by
  rcases ins with _ | ⟨a, ins⟩
  · cases op <;> simp [simplify, simpAnd, simpOr, simpNot]
  obtain ⟨a, rfl⟩ := hc a (by simp)
  rcases ins with _ | ⟨b, ins⟩
  · cases op <;> simp [simplify, simpAnd, simpOr, simpNot]
  obtain ⟨b, rfl⟩ := hc b (by simp)
  cases ins <;> cases op <;> simp [simplify, simpAnd, simpOr, simpNot]

lemma elim_known_constants (n : ℕ) (K : Finset ℕ) (gs : List Gate)
    (acc : List Stat × List Gate)
    (hK : ∀ j ∈ K, j < acc.1.length ∧
      ∃ c, acc.1.getD j (Sum.inl false) = Sum.inl c) :
    ∀ j ∈ K, j < (elim n gs acc).1.length ∧
      ∃ c, (elim n gs acc).1.getD j (Sum.inl false) = Sum.inl c := by
  intro j hj
  obtain ⟨hlt, c, hc⟩ := hK j hj
  refine ⟨by rw [elim_status_length]; omega, c, ?_⟩
  rw [elim_getD n j _ gs acc hlt, hc]

lemma known_inputs_simplify_constant (n : ℕ) (K : Finset ℕ) (g : Gate)
    (acc : List Stat × List Gate)
    (hK : ∀ j ∈ K, j < acc.1.length ∧
      ∃ c, acc.1.getD j (Sum.inl false) = Sum.inl c)
    (hinputs : ∀ j ∈ g.inputs, j ∈ K) :
    ∃ c, simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) = (none, Sum.inl c) := by
  apply simplify_all_constants
  intro s hs
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hs
  exact (hK j (hinputs j hj)).2

lemma known_constants_step (n : ℕ) (K : Finset ℕ) (g : Gate)
    (acc : List Stat × List Gate) (c : Bool)
    (hK : ∀ j ∈ K, j < acc.1.length ∧
      ∃ b, acc.1.getD j (Sum.inl false) = Sum.inl b)
    (hs : simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) = (none, Sum.inl c)) :
    (elimStep n acc g).2 = acc.2 ∧
    ∀ j ∈ insert acc.1.length K, j < (elimStep n acc g).1.length ∧
      ∃ b, (elimStep n acc g).1.getD j (Sum.inl false) = Sum.inl b := by
  have he : elimStep n acc g = (acc.1 ++ [Sum.inl c], acc.2) := by
    simp only [elimStep]
    rw [hs]
    simp
  rw [he]
  refine ⟨rfl, ?_⟩
  intro j hj
  simp only [Finset.mem_insert] at hj
  rcases hj with rfl | hj
  · exact ⟨by simp, c, getD_snoc_eq _ _ _⟩
  · obtain ⟨hlt, b, hb⟩ := hK j hj
    refine ⟨by simp; omega, b, ?_⟩
    rw [getD_snoc_ne _ _ _ _ (by omega), hb]

lemma elim_known_inputs_set_reader_bound (n : ℕ) (K : Finset ℕ)
    (pre post : List Gate) (g : Gate) (acc : List Stat × List Gate)
    (hok : ∀ q ∈ pre ++ g :: post, NOk q)
    (hK : ∀ j ∈ K, j < acc.1.length ∧
      ∃ c, acc.1.getD j (Sum.inl false) = Sum.inl c)
    (hinputs : ∀ j ∈ g.inputs, j ∈ K) :
    (elim n (pre ++ g :: post) acc).2.length + setReaderCount K pre + 1 +
      setReaderCount (insert (acc.1.length + pre.length) K) post ≤
        acc.2.length + (pre ++ g :: post).length := by
  let mid := elim n pre acc
  have hm : mid.1.length = acc.1.length + pre.length := elim_status_length n pre acc
  have hmK := elim_known_constants n K pre acc hK
  obtain ⟨c, hs⟩ := known_inputs_simplify_constant n K g mid hmK hinputs
  have hstep := known_constants_step n K g mid c hmK hs
  have hpre := elim_len_setReaders n K pre acc
    (fun q hq => hok q (List.mem_append_left _ hq)) hK
  have htail := elim_len_setReaders n (insert (acc.1.length + pre.length) K) post
    (elimStep n mid g)
    (fun q hq => hok q (List.mem_append_right _ (List.mem_cons_of_mem _ hq)))
    (by rw [← hm]; exact hstep.2)
  have he : elim n (pre ++ g :: post) acc = elim n post (elimStep n mid g) := by
    simp [elim, List.foldl_append, mid]
  rw [he]
  rw [hstep.1] at htail
  simp only [List.length_append, List.length_cons]
  change mid.2.length + setReaderCount K pre ≤ acc.2.length + pre.length at hpre
  omega

lemma root_simplify_constant (n : ℕ) (K : Finset ℕ) (k : ℕ) (g : Gate)
    (acc : List Stat × List Gate)
    (hK : ∀ j ∈ K, j < acc.1.length ∧
      ∃ c, acc.1.getD j (Sum.inl false) = Sum.inl c)
    (hok : NOk g) (hz : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (hroot : (g.op = GateOp.and ∧ k ∈ g.inputs) ∨ ∀ j ∈ g.inputs, j ∈ K) :
    ∃ c, simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) = (none, Sum.inl c) := by
  rcases hroot with ⟨hg, hk⟩ | hinputs
  · refine ⟨false, ?_⟩
    rw [hg]
    apply simplify_and_false
    · simpa using hok.1.2
    · exact List.mem_map.mpr ⟨k, hk, hz⟩
  · exact known_inputs_simplify_constant n K g acc hK hinputs

lemma elim_root_set_reader_bound (n : ℕ) (K : Finset ℕ) (k : ℕ)
    (pre post : List Gate) (g : Gate) (acc : List Stat × List Gate)
    (hok : ∀ q ∈ pre ++ g :: post, NOk q)
    (hK : ∀ j ∈ K, j < acc.1.length ∧
      ∃ c, acc.1.getD j (Sum.inl false) = Sum.inl c)
    (hk : k ∈ K) (hz : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (hroot : (g.op = GateOp.and ∧ k ∈ g.inputs) ∨ ∀ j ∈ g.inputs, j ∈ K) :
    (elim n (pre ++ g :: post) acc).2.length + setReaderCount K pre + 1 +
      setReaderCount (insert (acc.1.length + pre.length) K) post ≤
        acc.2.length + (pre ++ g :: post).length := by
  rcases hroot with ⟨hg, hread⟩ | hinputs
  · exact elim_and_set_reader_bound n K k pre post g acc hok hK hk hz hg hread
  · exact elim_known_inputs_set_reader_bound n K pre post g acc hok hK hinputs

lemma first_and_initial_state (n : ℕ) (g : Gate) (hok : NOk g)
    (hg : g.op = GateOp.and) (hread : n ∈ g.inputs) :
    elimStep n (initStats n false, []) g =
      (initStats n false ++ [Sum.inl false], []) := by
  have hz : (initStats n false).getD n (Sum.inl false) = Sum.inl false :=
    getD_snoc_len _ _ _ _ (by simp)
  have hs : simplify g.op n
      (g.inputs.map fun i => (initStats n false).getD i (Sum.inl false)) =
      (none, Sum.inl false) := by
    rw [hg]
    apply simplify_and_false
    · simpa using hok.1.2
    · exact List.mem_map.mpr ⟨n, hread, hz⟩
  simp only [elimStep, List.length_nil, Nat.add_zero]
  rw [hs]
  simp

lemma first_and_initial_known (n : ℕ) :
    ∀ j ∈ ({n, n + 1} : Finset ℕ),
      j < (initStats n false ++ [Sum.inl false]).length ∧
      ∃ c, (initStats n false ++ [Sum.inl false]).getD j (Sum.inl false) = Sum.inl c := by
  intro j hj
  simp only [Finset.mem_insert, Finset.mem_singleton] at hj
  rcases hj with rfl | rfl
  · refine ⟨by simp [initStats], false, ?_⟩
    rw [getD_snoc_ne _ _ _ _ (by simp [initStats])]
    exact getD_snoc_len _ _ _ _ (by simp)
  · refine ⟨by simp [initStats], false, ?_⟩
    exact getD_snoc_len _ _ _ _ (by simp [initStats])

lemma first_and_two_roots_budget (n : ℕ) (C : Circuit)
    (g q : Gate) (pre post : List Gate) (hC : FanInTwo C)
    (hgs : C.gates.map normGate = g :: (pre ++ q :: post))
    (hg : g.op = GateOp.and) (hread : n ∈ g.inputs)
    (hroot : (q.op = GateOp.and ∧ n ∈ q.inputs) ∨
      ∀ j ∈ q.inputs, j ∈ ({n, n + 1} : Finset ℕ)) :
    (elim n (C.gates.map normGate) (initStats n false, [])).2.length + 2 +
      setReaderCount {n, n + 1} pre +
      setReaderCount (insert (n + 2 + pre.length) {n, n + 1}) post ≤ C.size := by
  have hok : ∀ r ∈ g :: (pre ++ q :: post), NOk r := by
    intro r hr
    rw [← hgs] at hr
    obtain ⟨r0, hr0, rfl⟩ := List.mem_map.mp hr
    exact normGate_nok r0 (hC r0 hr0)
  have hstep := first_and_initial_state n g (hok g (by simp)) hg hread
  let acc : List Stat × List Gate := (initStats n false ++ [Sum.inl false], [])
  have hz : acc.1.getD n (Sum.inl false) = Sum.inl false := by
    change (initStats n false ++ [Sum.inl false]).getD n (Sum.inl false) = _
    rw [getD_snoc_ne _ _ _ _ (by simp [initStats])]
    exact getD_snoc_len _ _ _ _ (by simp)
  have hb := elim_root_set_reader_bound n {n, n + 1} n pre post q acc
    (fun r hr => hok r (List.mem_cons_of_mem _ hr)) (first_and_initial_known n)
    (by simp) hz hroot
  have he : elim n (C.gates.map normGate) (initStats n false, []) =
      elim n (pre ++ q :: post) acc := by
    rw [hgs]
    change elim n (pre ++ q :: post) (elimStep n (initStats n false, []) g) = _
    rw [hstep]
  have hlen : (g :: (pre ++ q :: post)).length = C.size := by
    rw [← hgs]
    simp [Circuit.size]
  rw [he]
  have hacclen : acc.1.length = n + 2 := by simp [acc, initStats]
  have hacc2 : acc.2.length = 0 := rfl
  rw [hacclen, hacc2] at hb
  simp only [Nat.zero_add, List.length_append, List.length_cons] at hb
  simp only [List.length_cons, List.length_append] at hlen
  omega

lemma fix_false_first_and_two_roots_distinct_consumers (n : ℕ) (C : Circuit)
    (g q : Gate) (pre post : List Gate) (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hgs : C.gates.map normGate = g :: (pre ++ q :: post))
    (hg : g.op = GateOp.and) (hread : n ∈ g.inputs)
    (hroot : (q.op = GateOp.and ∧ n ∈ q.inputs) ∨
      ∀ j ∈ q.inputs, j ∈ ({n, n + 1} : Finset ℕ))
    (hconsumers : 2 ≤ setReaderCount {n, n + 1} pre +
      setReaderCount (insert (n + 2 + pre.length) {n, n + 1}) post) :
    ∃ E : Circuit, FanInTwo E ∧ E.size + 4 ≤ C.size ∧
      ∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false)) := by
  have hb := first_and_two_roots_budget n C g q pre post hC hgs hg hread hroot
  apply fix_last_with_savings n 4 false C hC hnc
  omega

lemma elim_root_then_known_inputs_bound (n : ℕ) (K : Finset ℕ) (k : ℕ)
    (pre mid post : List Gate) (q r : Gate) (acc : List Stat × List Gate)
    (hok : ∀ g ∈ pre ++ q :: (mid ++ r :: post), NOk g)
    (hK : ∀ j ∈ K, j < acc.1.length ∧
      ∃ c, acc.1.getD j (Sum.inl false) = Sum.inl c)
    (hk : k ∈ K) (hz : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (hroot : (q.op = GateOp.and ∧ k ∈ q.inputs) ∨ ∀ j ∈ q.inputs, j ∈ K)
    (hrinputs : ∀ j ∈ r.inputs, j ∈ insert (acc.1.length + pre.length) K) :
    (elim n (pre ++ q :: (mid ++ r :: post)) acc).2.length + 2 +
      readerCount (acc.1.length + pre.length + 1 + mid.length) post ≤
        acc.2.length + (pre ++ q :: (mid ++ r :: post)).length := by
  let atQ := elim n pre acc
  have hatQlen : atQ.1.length = acc.1.length + pre.length := elim_status_length n pre acc
  have hQK := elim_known_constants n K pre acc hK
  have hQz : atQ.1.getD k (Sum.inl false) = Sum.inl false := by
    rw [elim_getD n k _ pre acc (hK k hk).1, hz]
  have hqok : NOk q := hok q (by simp)
  obtain ⟨cq, hsq⟩ := root_simplify_constant n K k q atQ hQK hqok hQz hroot
  have hqstep := known_constants_step n K q atQ cq hQK hsq
  let afterQ := elimStep n atQ q
  have hafterQK : ∀ j ∈ insert (acc.1.length + pre.length) K,
      j < afterQ.1.length ∧ ∃ c, afterQ.1.getD j (Sum.inl false) = Sum.inl c := by
    rw [← hatQlen]
    exact hqstep.2
  let atR := elim n mid afterQ
  have hRK := elim_known_constants n (insert (acc.1.length + pre.length) K)
    mid afterQ hafterQK
  obtain ⟨cr, hsr⟩ := known_inputs_simplify_constant n
    (insert (acc.1.length + pre.length) K) r atR hRK hrinputs
  have hrstep := known_constants_step n (insert (acc.1.length + pre.length) K)
    r atR cr hRK hsr
  have hatRlen : atR.1.length = acc.1.length + pre.length + 1 + mid.length := by
    rw [elim_status_length]
    simp only [afterQ, elimStep, List.length_append, List.length_cons, List.length_nil]
    rw [hatQlen]
  have hknownr := hrstep.2 atR.1.length (by simp)
  have htail := elim_len_readers n atR.1.length post (elimStep n atR r)
    (fun g hg => hok g (by simp [hg])) hknownr.1 hknownr.2
  have hpre := elim_len n pre acc
  have hmid := elim_len n mid afterQ
  have he : elim n (pre ++ q :: (mid ++ r :: post)) acc =
      elim n post (elimStep n atR r) := by
    simp [elim, List.foldl_append, atR, afterQ, atQ]
  rw [he, ← hatRlen]
  rw [hrstep.1] at htail
  change atR.2.length ≤ afterQ.2.length + mid.length at hmid
  change atQ.2.length ≤ acc.2.length + pre.length at hpre
  have hq2 : afterQ.2 = atQ.2 := hqstep.1
  rw [hq2] at hmid
  simp only [List.length_append, List.length_cons]
  omega

lemma fix_false_first_and_two_roots_shared_consumer (n : ℕ) (C : Circuit)
    (g q r : Gate) (pre mid post : List Gate) (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hgs : C.gates.map normGate = g :: (pre ++ q :: (mid ++ r :: post)))
    (hg : g.op = GateOp.and) (hread : n ∈ g.inputs)
    (hroot : (q.op = GateOp.and ∧ n ∈ q.inputs) ∨
      ∀ j ∈ q.inputs, j ∈ ({n, n + 1} : Finset ℕ))
    (hrinputs : ∀ j ∈ r.inputs, j ∈ insert (n + 2 + pre.length) ({n, n + 1} : Finset ℕ))
    (hconsumer : ∃ s ∈ post, n + 3 + pre.length + mid.length ∈ s.inputs) :
    ∃ E : Circuit, FanInTwo E ∧ E.size + 4 ≤ C.size ∧
      ∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false)) := by
  have hok : ∀ s ∈ g :: (pre ++ q :: (mid ++ r :: post)), NOk s := by
    intro s hs
    rw [← hgs] at hs
    obtain ⟨s0, hs0, rfl⟩ := List.mem_map.mp hs
    exact normGate_nok s0 (hC s0 hs0)
  have hstep := first_and_initial_state n g (hok g (by simp)) hg hread
  let acc : List Stat × List Gate := (initStats n false ++ [Sum.inl false], [])
  have hacclen : acc.1.length = n + 2 := by simp [acc, initStats]
  have hacc2 : acc.2.length = 0 := rfl
  have hz : acc.1.getD n (Sum.inl false) = Sum.inl false := by
    change (initStats n false ++ [Sum.inl false]).getD n (Sum.inl false) = _
    rw [getD_snoc_ne _ _ _ _ (by simp [initStats])]
    exact getD_snoc_len _ _ _ _ (by simp)
  have hb := elim_root_then_known_inputs_bound n {n, n + 1} n pre mid post q r acc
    (fun s hs => hok s (List.mem_cons_of_mem _ hs)) (first_and_initial_known n)
    (by simp) hz hroot (by rw [hacclen]; exact hrinputs)
  have he : elim n (C.gates.map normGate) (initStats n false, []) =
      elim n (pre ++ q :: (mid ++ r :: post)) acc := by
    rw [hgs]
    change elim n (pre ++ q :: (mid ++ r :: post)) (elimStep n (initStats n false, []) g) = _
    rw [hstep]
  have hlen : (g :: (pre ++ q :: (mid ++ r :: post))).length = C.size := by
    rw [← hgs]
    simp [Circuit.size]
  have hcons := chain_readerCount_positive _ _ hconsumer
  apply fix_last_with_savings n 4 false C hC hnc
  rw [he]
  rw [hacclen, hacc2] at hb
  have hindex : n + 2 + pre.length + 1 + mid.length = n + 3 + pre.length + mid.length := by omega
  rw [hindex] at hb
  simp only [Nat.zero_add, List.length_append, List.length_cons] at hb hlen
  omega

lemma single_reader_inputs (g : Gate) (k : ℕ)
    (hlen : g.inputs.length ≤ 1) (hk : k ∈ g.inputs) :
    ∀ j ∈ g.inputs, j = k := by
  rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, rest⟩⟩
  · simp [hins] at hk
  · simp only [hins, List.mem_singleton] at hk ⊢
    intro j hj
    exact hj.trans hk.symm
  · simp [hins] at hlen

lemma two_readers_exhaust_inputs (g : Gate) (p q : ℕ)
    (hlen : g.inputs.length ≤ 2) (hpq : p ≠ q)
    (hp : p ∈ g.inputs) (hq : q ∈ g.inputs) :
    ∀ j ∈ g.inputs, j = p ∨ j = q := by
  rcases hins : g.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp [hins] at hp
  · simp only [hins, List.mem_singleton] at hp hq
    exact False.elim (hpq (hp.trans hq.symm))
  · simp only [hins, List.mem_cons, List.not_mem_nil, or_false] at hp hq ⊢
    rcases hp with hp | hp <;> rcases hq with hq | hq
    · exact False.elim (hpq (hp.trans hq.symm))
    · intro j hj
      rcases hj with hj | hj
      · exact Or.inl (hj.trans hp.symm)
      · exact Or.inr (hj.trans hq.symm)
    · intro j hj
      rcases hj with hj | hj
      · exact Or.inr (hj.trans hq.symm)
      · exact Or.inl (hj.trans hp.symm)
    · exact False.elim (hpq (hp.trans hq.symm))
  · simp [hins] at hlen

lemma not_raw_reader_is_root (n : ℕ) (q : Gate) (hok : NOk q)
    (hq : q.op = GateOp.not) (hread : n ∈ q.inputs) :
    (q.op = GateOp.and ∧ n ∈ q.inputs) ∨
      ∀ j ∈ q.inputs, j ∈ ({n, n + 1} : Finset ℕ) := by
  right
  intro j hj
  have he := single_reader_inputs q n (hok.2 hq) hread j hj
  simp [he]

lemma shared_root_consumer_inputs (n : ℕ) (pre : List Gate) (r : Gate)
    (hlen : r.inputs.length ≤ 2)
    (hp : n + 1 ∈ r.inputs) (hq : n + 2 + pre.length ∈ r.inputs) :
    ∀ j ∈ r.inputs, j ∈ insert (n + 2 + pre.length) ({n, n + 1} : Finset ℕ) := by
  intro j hj
  have h := two_readers_exhaust_inputs r (n + 1) (n + 2 + pre.length)
    hlen (by omega) hp hq j hj
  rcases h with rfl | rfl <;> simp




open PEqualNP.CircuitLowerBounds

lemma root_setReaderCount_singleton (p : ℕ) (gs : List Gate) :
    setReaderCount {p} gs = readerCount p gs := by
  induction gs with
  | nil => simp [setReaderCount, readerCount]
  | cons g gs ih => simp [setReaderCount, readerCount, ih]

lemma root_setReaderCount_positive (K : Finset ℕ) (p : ℕ) (gs : List Gate)
    (hpK : p ∈ K) (hp : ∃ g ∈ gs, p ∈ g.inputs) :
    1 ≤ setReaderCount K gs := by
  have hpos := chain_readerCount_positive p gs hp
  have hmono := chain_setReaderCount_mono {p} K
    (by intro i hi; simp only [Finset.mem_singleton] at hi; subst i; exact hpK) gs
  rw [root_setReaderCount_singleton] at hmono
  omega

lemma constant_roots_reader_dichotomy (raw p q : ℕ) (gs : List Gate)
    (hp : ∃ g ∈ gs, p ∈ g.inputs) (hq : ∃ g ∈ gs, q ∈ g.inputs) :
    2 ≤ setReaderCount {raw, p, q} gs ∨
      ∃ g ∈ gs, p ∈ g.inputs ∧ q ∈ g.inputs := by
  classical
  by_cases hshared : ∃ g ∈ gs, p ∈ g.inputs ∧ q ∈ g.inputs
  · exact Or.inr hshared
  · left
    obtain ⟨g, hg, hgp⟩ := hp
    have hgq : q ∉ g.inputs := by
      intro h
      exact hshared ⟨g, hg, hgp, h⟩
    have hextra := chain_setReaderCount_insert_extra {q} p gs
      ⟨g, hg, hgp, by
        intro k hk
        simp only [Finset.mem_singleton] at hk
        subst k
        exact hgq⟩
    rw [root_setReaderCount_singleton] at hextra
    have hpos := chain_readerCount_positive q gs hq
    have hmono := chain_setReaderCount_mono {p, q} {raw, p, q}
      (by
        intro k hk
        simp only [Finset.mem_insert, Finset.mem_singleton] at hk ⊢
        tauto) gs
    omega

lemma constant_roots_split_reader_dichotomy (raw p q : ℕ) (pre post : List Gate)
    (hp : ∃ g ∈ pre ++ post, p ∈ g.inputs)
    (hq : ∃ g ∈ post, q ∈ g.inputs) :
    2 ≤ setReaderCount {raw, p} pre + setReaderCount {raw, p, q} post ∨
      ∃ g ∈ post, p ∈ g.inputs ∧ q ∈ g.inputs := by
  obtain ⟨g, hg, hgp⟩ := hp
  rcases List.mem_append.mp hg with hg | hg
  · left
    have hpre := root_setReaderCount_positive {raw, p} p pre (by simp) ⟨g, hg, hgp⟩
    have hpost := root_setReaderCount_positive {raw, p, q} q post (by simp) hq
    omega
  · rcases constant_roots_reader_dichotomy raw p q post ⟨g, hg, hgp⟩ hq with hcount | hshared
    · exact Or.inl (by omega)
    · exact Or.inr hshared


end Restriction


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Restriction

def positiveInitStats (m h : ℕ) : List Stat :=
  List.ofFn (fun i : Fin m => if i.val = h then Sum.inl false else Sum.inr i.val)

lemma positive_init_get (m h i : ℕ) (hi : i < m) :
    (positiveInitStats m h).getD i (Sum.inl false) =
      (if i = h then Sum.inl false else Sum.inr i) := by
  simp [positiveInitStats, List.getD, hi]

lemma positive_init_beyond (m h i : ℕ) (hi : m ≤ i) :
    (positiveInitStats m h).getD i (Sum.inl false) = Sum.inl false := by
  apply List.getD_eq_default
  simpa [positiveInitStats] using hi

lemma positive_init_inv (n : ℕ) (pre : List Gate) (h : ℕ)
    (x : Fin n → Bool) (hx : (wiresFrom pre (List.ofFn x)).getD h false = false) :
    Inv n (List.ofFn x) (wiresFrom pre (List.ofFn x))
      (positiveInitStats (n + pre.length) h, pre) := by
  have lw : (wiresFrom pre (List.ofFn x)).length = n + pre.length := by
    simp [length_wiresFrom]
  refine ⟨by simp [positiveInitStats, lw], ?_⟩
  intro i
  by_cases hi : i < n + pre.length
  · rw [positive_init_get _ _ _ hi]
    by_cases he : i = h
    · subst i
      simp only [↓reduceIte]
      exact ⟨trivial, hx.symm⟩
    · rw [ite_eq_right he]
      exact ⟨hi, rfl⟩
  · rw [positive_init_beyond _ _ _ (by omega)]
    refine ⟨trivial, ?_⟩
    change false = _
    symm
    apply List.getD_eq_default
    omega

lemma positive_elim_prefix (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    ∃ tail : List Gate, (elim n gs acc).2 = acc.2 ++ tail := by
  induction gs generalizing acc with
  | nil => exact ⟨[], by simp [elim]⟩
  | cons g gs ih =>
    obtain ⟨tail, ht⟩ := ih (elimStep n acc g)
    refine ⟨(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList ++ tail, ?_⟩
    change (elim n gs (elimStep n acc g)).2 = _
    rw [ht]
    simp [elimStep, List.append_assoc]

lemma positive_top_or_eval (n : ℕ) (gs : List Gate) (j h : ℕ) (x : Fin n → Bool) :
    ({gates := gs ++ [⟨.or, [j, h]⟩], output := n + gs.length} : Circuit).eval (List.ofFn x) =
      ((wiresFrom gs (List.ofFn x)).getD j false ||
        (wiresFrom gs (List.ofFn x)).getD h false) := by
  change (wiresFrom (gs ++ [⟨.or, [j, h]⟩]) (List.ofFn x)).getD _ false = _
  rw [wiresFrom_append]
  change ((wiresFrom gs (List.ofFn x)) ++ [_]).getD _ false = _
  have hlen : (wiresFrom gs (List.ofFn x)).length = n + gs.length := by
    simp [length_wiresFrom]
  rw [← hlen, List.getD_append_right _ _ _ _ (Nat.le_refl _)]
  simp [GateOp.eval]

lemma positive_wire_lift (n : ℕ) (pre post : List Gate) (out h : ℕ)
    (hh : h < n + pre.length)
    (hfanin : FanInTwo ({gates := pre ++ post, output := out} : Circuit))
    (hbelow : ∀ x : Fin n → Bool,
      (wiresFrom pre (List.ofFn x)).getD h false = true →
        ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) = true) :
    ∃ E : Circuit, FanInTwo E ∧
      E.size + readerCount h (post.map normGate) ≤
        ({gates := pre ++ post, output := out} : Circuit).size + 1 ∧
      ∀ x : Fin n → Bool, E.eval (List.ofFn x) =
        ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) := by
  have hpre : ∀ g ∈ pre, Ok g := by
    intro g hg
    exact hfanin g (List.mem_append_left _ hg)
  have hpost : ∀ g ∈ post.map normGate, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact normGate_nok g0 (hfanin g0 (List.mem_append_right _ hg0))
  set acc := elim n (post.map normGate) (positiveInitStats (n + pre.length) h, pre) with hacc
  have hcount := elim_len_readers n h (post.map normGate)
    (positiveInitStats (n + pre.length) h, pre) hpost
    (by simpa [positiveInitStats] using hh)
    ⟨false, by rw [positive_init_get _ _ _ hh]; simp⟩
  rw [← hacc] at hcount
  have hok : ∀ g ∈ acc.2, Ok g := by
    rw [hacc]
    exact elim_ok n (post.map normGate) _ hpre
  obtain ⟨tail, htail⟩ := positive_elim_prefix n (post.map normGate)
    (positiveInitStats (n + pre.length) h, pre)
  change (elim n (post.map normGate) (positiveInitStats (n + pre.length) h, pre)).2 =
    pre ++ tail at htail
  rw [← hacc] at htail
  have hpreserve (x : Fin n → Bool) :
      (wiresFrom acc.2 (List.ofFn x)).getD h false =
        (wiresFrom pre (List.ofFn x)).getD h false := by
    rw [htail, wiresFrom_append]
    exact getD_wiresFrom tail _ h (by simpa [length_wiresFrom] using hh)
  have hval (x : Fin n → Bool)
      (hx : (wiresFrom pre (List.ofFn x)).getD h false = false) :
      (acc.1.getD out (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) =
        ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) := by
    have hi := inv_elim n (List.ofFn x) (by simp) (post.map normGate)
      (wiresFrom pre (List.ofFn x)) (positiveInitStats (n + pre.length) h, pre)
      (fun g hg => (hpost g hg).1) (positive_init_inv n pre h x hx)
    rw [← hacc] at hi
    have hv := (hi.2 out).2
    rw [wiresFrom_norm] at hv
    simpa only [Circuit.eval, Circuit.wires, wiresFrom, List.foldl_append] using hv
  cases hs : acc.1.getD out (Sum.inl false) with
  | inl c =>
    cases c with
    | false =>
      refine ⟨⟨pre, h⟩, hpre, ?_, ?_⟩
      · simp only [Circuit.size, List.length_append]
        simp only [List.length_map] at hcount
        have hp : pre.length ≤ acc.2.length := by rw [htail]; simp
        omega
      · intro x
        cases hx : (wiresFrom pre (List.ofFn x)).getD h false with
        | false =>
          have hv := hval x hx
          rw [hs] at hv
          change (wiresFrom pre (List.ofFn x)).getD h false = _
          rw [hx]
          exact hv
        | true =>
          change (wiresFrom pre (List.ofFn x)).getD h false = _
          rw [hx, hbelow x hx]
    | true =>
      refine ⟨⟨[⟨.and, []⟩], n⟩, ?_, ?_, ?_⟩
      · intro g hg
        obtain rfl := List.mem_singleton.mp hg
        simp
      · simp only [Circuit.size, List.length_append, List.length_singleton]
        simp only [List.length_map] at hcount
        omega
      · intro x
        have hf : ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) = true := by
          cases hx : (wiresFrom pre (List.ofFn x)).getD h false with
          | false =>
            have hv := hval x hx
            rw [hs] at hv
            exact hv.symm
          | true => exact hbelow x hx
        rw [hf]
        simp [Circuit.eval, Circuit.wires, GateOp.eval]
  | inr j =>
    refine ⟨⟨acc.2 ++ [⟨.or, [j, h]⟩], n + acc.2.length⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hok g hg
      · obtain rfl := List.mem_singleton.mp hg
        simp
    · simp only [Circuit.size, List.length_append, List.length_singleton]
      simp only [List.length_map] at hcount
      omega
    · intro x
      rw [positive_top_or_eval, hpreserve]
      cases hx : (wiresFrom pre (List.ofFn x)).getD h false with
      | false =>
        simp only [Bool.or_false]
        have hv := hval x hx
        rw [hs] at hv
        exact hv
      | true => simp [hbelow x hx]

lemma positive_wire_two_readers_improves (n : ℕ) (pre post : List Gate) (out h : ℕ)
    (hh : h < n + pre.length)
    (hfanin : FanInTwo ({gates := pre ++ post, output := out} : Circuit))
    (hbelow : ∀ x : Fin n → Bool,
      (wiresFrom pre (List.ofFn x)).getD h false = true →
        ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) = true)
    (hread : 2 ≤ readerCount h (post.map normGate)) :
    ∃ E : Circuit, FanInTwo E ∧
      E.size < ({gates := pre ++ post, output := out} : Circuit).size ∧
      ∀ x : Fin n → Bool, E.eval (List.ofFn x) =
        ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) := by
  obtain ⟨E, hE, hsize, heval⟩ := positive_wire_lift n pre post out h hh hfanin hbelow
  exact ⟨E, hE, by omega, heval⟩

lemma minimum_positive_wire_readers_le_one (n : ℕ) (pre post : List Gate) (out h : ℕ)
    (hh : h < n + pre.length)
    (hfanin : FanInTwo ({gates := pre ++ post, output := out} : Circuit))
    (hbelow : ∀ x : Fin n → Bool,
      (wiresFrom pre (List.ofFn x)).getD h false = true →
        ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) = true)
    (hmin : ∀ E : Circuit, FanInTwo E →
      (∀ x : Fin n → Bool, E.eval (List.ofFn x) =
        ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x)) →
      ({gates := pre ++ post, output := out} : Circuit).size ≤ E.size) :
    readerCount h (post.map normGate) ≤ 1 := by
  obtain ⟨E, hE, hsize, heval⟩ := positive_wire_lift n pre post out h hh hfanin hbelow
  have hm := hmin E hE heval
  omega



namespace Wires


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma wires_length (C : Circuit) (xs : List Bool) :
    (C.wires xs).length = xs.length + C.size := by
  rcases C with ⟨gs, out⟩
  induction gs generalizing xs with
  | nil => simp [Circuit.wires, Circuit.size]
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, out⟩
      (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil, Circuit.size]
    omega

lemma wires_input (C : Circuit) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    (C.wires xs).getD i false = xs.getD i false := by
  rcases C with ⟨gs, out⟩
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, out⟩
      (xs ++ [g.op.eval (g.inputs.map fun j => xs.getD j false)])).getD i false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]


end Wires

namespace LivePruning


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def effective (g : Gate) : List ℕ :=
  match g.op with
  | .not => g.inputs.take 1
  | _ => g.inputs

def down (k i : ℕ) : ℕ := if i < k then i else i - 1

def rename (k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (down k)⟩

def gateValue (g : Gate) (xs : List Bool) : Bool :=
  g.op.eval (g.inputs.map fun i => xs.getD i false)

lemma effective_value (g : Gate) (xs : List Bool) :
    gateValue g xs = g.op.eval ((effective g).map fun i => xs.getD i false) := by
  rcases g with ⟨op, ins⟩
  cases op <;> try rfl
  cases ins <;> rfl

lemma effective_rename (k : ℕ) (g : Gate) :
    effective (rename k g) = (effective g).map (down k) := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp [effective, rename, List.map_take]

lemma rename_value (k : ℕ) (g : Gate) (xs ys : List Bool)
    (hun : k ∉ effective g)
    (heq : ∀ i, i ≠ k → xs.getD (down k i) false = ys.getD i false) :
    gateValue (rename k g) xs = gateValue g ys := by
  rw [effective_value, effective_value, effective_rename]
  change g.op.eval (((effective g).map (down k)).map fun i => xs.getD i false) = _
  rw [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i hi
  exact heq i (fun h => hun (h ▸ hi))

lemma append_agree (k : ℕ) (xs ys : List Bool) (b : Bool)
    (hlen : xs.length + 1 = ys.length) (hk : k < ys.length)
    (heq : ∀ i, i ≠ k → xs.getD (down k i) false = ys.getD i false) :
    ∀ i, i ≠ k → (xs ++ [b]).getD (down k i) false = (ys ++ [b]).getD i false := by
  intro i hi
  rcases Nat.lt_trichotomy i ys.length with hlt | he | hgt
  · have hd : down k i < xs.length := by unfold down; split <;> omega
    rw [List.getD_append _ _ _ _ hd, List.getD_append _ _ _ _ hlt]
    exact heq i hi
  · subst i
    have hd : down k ys.length = xs.length := by unfold down; split <;> omega
    rw [hd]
    simp [List.getD_eq_getElem?_getD]
  · rw [List.getD_eq_default _ _ (by
      simp only [List.length_append, List.length_singleton]
      unfold down; split <;> omega),
      List.getD_eq_default _ _ (by simp; omega)]

lemma initial_agree (xs : List Bool) (b : Bool) :
    ∀ i, i ≠ xs.length → xs.getD (down xs.length i) false = (xs ++ [b]).getD i false := by
  intro i hi
  by_cases hlt : i < xs.length
  · simp only [down, ite_eq_left hlt]
    rw [List.getD_append _ _ _ _ hlt]
  · have hgt : xs.length < i := by omega
    rw [List.getD_eq_default _ _ (by unfold down; split <;> omega),
      List.getD_eq_default _ _ (by simp; omega)]

lemma wires_rename (k : ℕ) (gs : List Gate) (xs ys : List Bool)
    (hlen : xs.length + 1 = ys.length) (hk : k < ys.length)
    (hun : ∀ g ∈ gs, k ∉ effective g)
    (heq : ∀ i, i ≠ k → xs.getD (down k i) false = ys.getD i false) :
    ∀ i, i ≠ k →
      (Circuit.wires ⟨gs.map (rename k), 0⟩ xs).getD (down k i) false =
      (Circuit.wires ⟨gs, 0⟩ ys).getD i false := by
  induction gs generalizing xs ys with
  | nil => exact heq
  | cons g gs ih =>
    have hg : gateValue (rename k g) xs = gateValue g ys :=
      rename_value k g xs ys (hun g (by simp)) heq
    change ∀ i, i ≠ k →
      (Circuit.wires ⟨gs.map (rename k), 0⟩ (xs ++ [gateValue (rename k g) xs])).getD
        (down k i) false =
      (Circuit.wires ⟨gs, 0⟩ (ys ++ [gateValue g ys])).getD i false
    rw [hg]
    apply ih _ _
    · simp only [List.length_append, List.length_singleton]; omega
    · simp only [List.length_append, List.length_singleton]; omega
    · intro h hh
      exact hun h (by simp [hh])
    · exact append_agree k xs ys _ hlen hk heq

lemma wires_length (gs : List Gate) (xs : List Bool) :
    (Circuit.wires ⟨gs, 0⟩ xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [Circuit.wires]
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, 0⟩ (xs ++ [gateValue g xs])).length = _
    rw [ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega

def erase (n : ℕ) (pre post : List Gate) (o : ℕ) : Circuit :=
  ⟨pre ++ post.map (rename (n + pre.length)), down (n + pre.length) o⟩

lemma erase_eval (n : ℕ) (pre post : List Gate) (g : Gate) (o : ℕ)
    (hun : ∀ h ∈ post, n + pre.length ∉ effective h)
    (ho : o ≠ n + pre.length) (x : Fin n → Bool) :
    (erase n pre post o).eval (List.ofFn x) =
      (Circuit.mk (pre ++ g :: post) o).eval (List.ofFn x) := by
  let xs := Circuit.wires ⟨pre, 0⟩ (List.ofFn x)
  have hx : xs.length = n + pre.length := by
    unfold xs
    rw [wires_length, List.length_ofFn]
  simp only [erase, Circuit.eval, Circuit.wires, List.foldl_append,
    List.foldl_cons]
  change (Circuit.wires ⟨post.map (rename (n + pre.length)), 0⟩ xs).getD
      (down (n + pre.length) o) false =
    (Circuit.wires ⟨post, 0⟩ (xs ++ [gateValue g xs])).getD o false
  apply wires_rename _ _ _ _ (by simp) (by simp [hx]) hun _ o ho
  rw [← hx]
  exact initial_agree xs _

lemma erase_size (n : ℕ) (pre post : List Gate) (g : Gate) (o : ℕ) :
    (erase n pre post o).size + 1 = (Circuit.mk (pre ++ g :: post) o).size := by
  simp [erase, Circuit.size]
  omega

lemma erase_fanin (n : ℕ) (pre post : List Gate) (g : Gate) (o : ℕ)
    (hfan : FanInTwo (Circuit.mk (pre ++ g :: post) o)) :
    FanInTwo (erase n pre post o) := by
  intro h hh
  change h ∈ pre ++ post.map (rename (n + pre.length)) at hh
  rcases List.mem_append.mp hh with hh | hh
  · exact hfan h (List.mem_append.mpr (Or.inl hh))
  · obtain ⟨q, hq, heq⟩ := List.mem_map.mp hh
    subst h
    have hhf := hfan q (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hq)))
    simpa [rename] using hhf

lemma minimal_live (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (pre post : List Gate) (g : Gate) (hs : C.gates = pre ++ g :: post)
    (ho : C.output ≠ n + pre.length) :
    ∃ h ∈ post, n + pre.length ∈ effective h := by
  by_contra hn
  have hun : ∀ h ∈ post, n + pre.length ∉ effective h := by
    intro h hh hi
    exact hn ⟨h, hh, hi⟩
  have hC : C = ⟨pre ++ g :: post, C.output⟩ := by cases C; simp_all
  have hD := erase_fanin n pre post g C.output (hC ▸ hfan)
  have hsz := hmin (erase n pre post C.output) hD (by
    intro x
    rw [erase_eval n pre post g C.output hun ho x, ← hC])
  have hlen := erase_size n pre post g C.output
  rw [← hC] at hlen
  omega

lemma minimal_output_last (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (hpos : 0 < C.size) : C.output + 1 = n + C.size := by
  have split_last (gs : List Gate) (hp : 0 < gs.length) :
      ∃ pre g, gs = pre ++ [g] := by
    induction gs using List.reverseRecOn with
    | nil => simp at hp
    | append_singleton pre g _ => exact ⟨pre, g, rfl⟩
  obtain ⟨pre, g, hs⟩ := split_last C.gates hpos
  have ho : C.output = n + pre.length := by
    by_contra hne
    obtain ⟨h, hh, _⟩ := minimal_live n C hfan hmin pre [] g hs hne
    simp at hh
  rw [ho]
  simp only [Circuit.size, hs, List.length_append, List.length_singleton]
  omega

lemma minimal_live_index (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (p : ℕ) (hp : p + 1 < C.size) :
    ∃ q, p < q ∧ ∃ g, C.gates[q]? = some g ∧ n + p ∈ effective g := by
  have hp' : p < C.gates.length := by change p + 1 < C.gates.length at hp; omega
  have hs : C.gates = C.gates.take p ++ C.gates[p] :: C.gates.drop (p + 1) := by
    rw [List.getElem_cons_drop hp', List.take_append_drop]
  have hlen : (C.gates.take p).length = p := by simp; omega
  have ho : C.output ≠ n + (C.gates.take p).length := by
    have hlast := minimal_output_last n C hfan hmin (by omega)
    rw [hlen]
    omega
  obtain ⟨g, hg, hread⟩ := minimal_live n C hfan hmin _ _ _ hs ho
  obtain ⟨q, hq⟩ := List.mem_iff_getElem?.mp hg
  rw [List.getElem?_drop] at hq
  exact ⟨p + 1 + q, by omega, g, hq, by simpa [hlen] using hread⟩

lemma exists_minimal (n : ℕ) (C : Circuit) (hfan : FanInTwo C) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
      (∀ E : Circuit, FanInTwo E →
        (∀ x : Fin n → Bool, E.eval (List.ofFn x) = D.eval (List.ofFn x)) → D.size ≤ E.size) := by
  classical
  let P (k : ℕ) := ∃ D : Circuit, FanInTwo D ∧ D.size = k ∧
    ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)
  have hex : ∃ k, P k := ⟨C.size, C, hfan, rfl, fun _ => rfl⟩
  obtain ⟨D, hD, hsize, heval⟩ := Nat.find_spec hex
  refine ⟨D, hD, ?_, heval, ?_⟩
  · rw [hsize]
    exact Nat.find_min' hex ⟨C, hfan, rfl, fun _ => rfl⟩
  · intro E hE hEC
    rw [hsize]
    apply Nat.find_min' hex
    exact ⟨E, hE, rfl, fun x => (hEC x).trans (heval x)⟩

lemma exists_live (n : ℕ) (C : Circuit) (hfan : FanInTwo C) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) ∧
      (∀ E : Circuit, FanInTwo E →
        (∀ x : Fin n → Bool, E.eval (List.ofFn x) = D.eval (List.ofFn x)) → D.size ≤ E.size) ∧
      (0 < D.size → D.output + 1 = n + D.size) ∧
      (∀ p, p + 1 < D.size →
        ∃ q, p < q ∧ ∃ g, D.gates[q]? = some g ∧ n + p ∈ effective g) := by
  obtain ⟨D, hD, hsz, heval, hmin⟩ := exists_minimal n C hfan
  exact ⟨D, hD, hsz, heval, hmin,
    minimal_output_last n D hD hmin, minimal_live_index n D hD hmin⟩


end LivePruning

namespace AliasPruning


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2373_aux.LivePruning

def redirect (k p i : ℕ) : ℕ := if i = k then p else down k i

def renamed (k p : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (redirect k p)⟩

lemma renamed_value (k p : ℕ) (g : Gate) (xs ys : List Bool)
    (heq : ∀ i, xs.getD (redirect k p i) false = ys.getD i false) :
    gateValue (renamed k p g) xs = gateValue g ys := by
  unfold gateValue renamed
  simp only [List.map_map]
  congr 1
  apply List.map_congr_left
  intro i _
  exact heq i

lemma append_agree (k p : ℕ) (xs ys : List Bool) (b : Bool)
    (hlen : xs.length + 1 = ys.length) (hk : k < ys.length) (hp : p < k)
    (heq : ∀ i, xs.getD (redirect k p i) false = ys.getD i false) :
    ∀ i, (xs ++ [b]).getD (redirect k p i) false = (ys ++ [b]).getD i false := by
  intro i
  by_cases hi : i = k
  · subst i
    simp only [redirect, ite_true]
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hk]
    simpa [redirect] using heq k
  · simp only [redirect, ite_eq_right hi]
    apply LivePruning.append_agree k xs ys b hlen hk _ i hi
    intro j hj
    simpa [redirect, hj] using heq j

lemma initial_agree (xs : List Bool) (p : ℕ) (b : Bool)
    (hcopy : b = xs.getD p false) :
    ∀ i, xs.getD (redirect xs.length p i) false = (xs ++ [b]).getD i false := by
  intro i
  by_cases hi : i = xs.length
  · subst i
    simp [redirect, List.getD_eq_getElem?_getD, hcopy]
  · simpa [redirect, hi] using LivePruning.initial_agree xs b i hi

lemma wires_renamed (k p : ℕ) (gs : List Gate) (xs ys : List Bool)
    (hlen : xs.length + 1 = ys.length) (hk : k < ys.length) (hp : p < k)
    (heq : ∀ i, xs.getD (redirect k p i) false = ys.getD i false) :
    ∀ i, (Circuit.wires ⟨gs.map (renamed k p), 0⟩ xs).getD (redirect k p i) false =
      (Circuit.wires ⟨gs, 0⟩ ys).getD i false := by
  induction gs generalizing xs ys with
  | nil => exact heq
  | cons g gs ih =>
    have hg := renamed_value k p g xs ys heq
    change ∀ i,
      (Circuit.wires ⟨gs.map (renamed k p), 0⟩ (xs ++ [gateValue (renamed k p g) xs])).getD
        (redirect k p i) false =
      (Circuit.wires ⟨gs, 0⟩ (ys ++ [gateValue g ys])).getD i false
    rw [hg]
    apply ih _ _
    · simp only [List.length_append, List.length_singleton]; omega
    · simp only [List.length_append, List.length_singleton]; omega
    · exact append_agree k p xs ys _ hlen hk hp heq

lemma wires_input (gs : List Gate) (xs : List Bool) (i : ℕ) (hi : i < xs.length) :
    (Circuit.wires ⟨gs, 0⟩ xs).getD i false = xs.getD i false := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, 0⟩ (xs ++ [gateValue g xs])).getD i false = _
    rw [ih _ (by simp; omega), List.getD_append _ _ _ _ hi]

def erase (n : ℕ) (pre post : List Gate) (p o : ℕ) : Circuit :=
  ⟨pre ++ post.map (renamed (n + pre.length) p), redirect (n + pre.length) p o⟩

lemma erase_eval (n : ℕ) (pre post : List Gate) (g : Gate) (p o : ℕ)
    (hp : p < n + pre.length)
    (hcopy : ∀ x : Fin n → Bool,
      (Circuit.wires ⟨pre ++ g :: post, o⟩ (List.ofFn x)).getD (n + pre.length) false =
      (Circuit.wires ⟨pre ++ g :: post, o⟩ (List.ofFn x)).getD p false)
    (x : Fin n → Bool) :
    (erase n pre post p o).eval (List.ofFn x) =
      (Circuit.mk (pre ++ g :: post) o).eval (List.ofFn x) := by
  let xs := Circuit.wires ⟨pre, 0⟩ (List.ofFn x)
  have hx : xs.length = n + pre.length := by
    unfold xs
    rw [wires_length, List.length_ofFn]
  have hcopy' : gateValue g xs = xs.getD p false := by
    have h := hcopy x
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons] at h
    change (Circuit.wires ⟨post, 0⟩ (xs ++ [gateValue g xs])).getD (n + pre.length) false =
      (Circuit.wires ⟨post, 0⟩ (xs ++ [gateValue g xs])).getD p false at h
    rw [wires_input _ _ _ (by simp [hx]), wires_input _ _ _ (by simp [hx]; omega)] at h
    rw [List.getD_append xs [gateValue g xs] false p (by omega), ← hx] at h
    simpa [List.getD_eq_getElem?_getD] using h
  simp only [erase, Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons]
  change (Circuit.wires ⟨post.map (renamed (n + pre.length) p), 0⟩ xs).getD
      (redirect (n + pre.length) p o) false =
    (Circuit.wires ⟨post, 0⟩ (xs ++ [gateValue g xs])).getD o false
  apply wires_renamed _ _ _ _ _ (by simp) (by simp [hx]) hp _ o
  rw [← hx]
  exact initial_agree xs p _ hcopy'

lemma erase_size (n : ℕ) (pre post : List Gate) (g : Gate) (p o : ℕ) :
    (erase n pre post p o).size + 1 = (Circuit.mk (pre ++ g :: post) o).size := by
  simp [erase, Circuit.size]
  omega

lemma erase_fanin (n : ℕ) (pre post : List Gate) (g : Gate) (p o : ℕ)
    (hfan : FanInTwo (Circuit.mk (pre ++ g :: post) o)) :
    FanInTwo (erase n pre post p o) := by
  intro h hh
  change h ∈ pre ++ post.map (renamed (n + pre.length) p) at hh
  rcases List.mem_append.mp hh with hh | hh
  · exact hfan h (List.mem_append.mpr (Or.inl hh))
  · obtain ⟨q, hq, heq⟩ := List.mem_map.mp hh
    subst h
    have hhf := hfan q (List.mem_append.mpr (Or.inr (List.mem_cons_of_mem _ hq)))
    simpa [renamed] using hhf

lemma minimal_no_alias (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (pre post : List Gate) (g : Gate) (hs : C.gates = pre ++ g :: post)
    (p : ℕ) (hp : p < n + pre.length) :
    ¬ ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n + pre.length) false =
      (C.wires (List.ofFn x)).getD p false := by
  intro hcopy
  have hC : C = ⟨pre ++ g :: post, C.output⟩ := by cases C; simp_all
  have hD := erase_fanin n pre post g p C.output (hC ▸ hfan)
  have hsz := hmin (erase n pre post p C.output) hD (by
    intro x
    rw [erase_eval n pre post g p C.output hp (by simpa [← hC] using hcopy) x, ← hC])
  have hlen := erase_size n pre post g p C.output
  rw [← hC] at hlen
  omega

lemma minimal_no_alias_index (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (k : ℕ) (hk : k < C.size) (p : ℕ) (hp : p < n + k) :
    ¬ ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD (n + k) false = (C.wires (List.ofFn x)).getD p false := by
  have hk' : k < C.gates.length := hk
  have hs : C.gates = C.gates.take k ++ C.gates[k] :: C.gates.drop (k + 1) := by
    rw [List.getElem_cons_drop hk', List.take_append_drop]
  have hlen : (C.gates.take k).length = k := by simp; omega
  simpa [hlen] using minimal_no_alias n C hfan hmin _ _ _ hs p (by simpa [hlen] using hp)


end AliasPruning

namespace NandRestriction


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2





lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp





def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

abbrev Stat := Bool ⊕ Nat

def Stat.val (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def Stat.Valid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg; subst hg; simp [Ok]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg; subst hg; simp [Ok]
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg; subst hg; simp [Ok]
  · simp at hg
  · simp at hg

lemma simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

lemma simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · rcases a with ⟨_ | _⟩ | _ <;> rcases b with ⟨_ | _⟩ | _ <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · rcases a with ⟨_ | _⟩ | _ <;> rcases b with ⟨_ | _⟩ | _ <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

lemma toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

lemma elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

lemma elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega

lemma Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

lemma Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Sum.inl false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Sum.inl false)).val (wiresFrom acc.2 y) = w.getD i false

lemma inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Sum.inl false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Sum.inl false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2


def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

lemma normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

lemma wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]


def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat)) ++ [Sum.inl b]

lemma inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

lemma ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp


def readerCount (k : ℕ) : List Gate → ℕ
  | [] => 0
  | g :: gs => (if k ∈ g.inputs then 1 else 0) + readerCount k gs

lemma elim_len_readers (n k : ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      (∀ g ∈ gs, NOk g) → k < acc.1.length →
      (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + readerCount k gs ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim, readerCount]
  | cons g gs ih =>
    intro acc hok hk hc
    have ht := ih (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [elimStep]; omega)
      (by
        obtain ⟨c, hc⟩ := hc
        refine ⟨c, ?_⟩
        simp only [elimStep]
        rw [getD_snoc_ne _ _ _ _ (by omega)]
        exact hc)
    have he : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [he, List.length_cons]
    by_cases hr : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hr, hc⟩⟩
      have hs : (elimStep n acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone]
        simp
      simp only [readerCount, ite_eq_left hr]
      omega
    · have hs : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [readerCount, ite_eq_right hr]
      omega

lemma fix_last_counted (n : ℕ) (b : Bool) (C : Circuit)
    (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y b)) ≠ C.eval (List.ofFn (Fin.snoc y' b))) :
    ∃ E : Circuit, FanInTwo E ∧
      E.size + readerCount n (C.gates.map normGate) ≤ C.size ∧
      ∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y b)) := by
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hC g0 hg0)
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y)
        (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) =
        C.eval (List.ofFn (Fin.snoc y b)) := by
    intro y
    rw [((hinv y).2 C.output).2, hgs, wiresFrom_norm]
    rfl
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | inr j =>
    have hlen := elim_len_readers n n gs (initStats n b, []) hnok
      (by simp [initStats]) ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩
    rw [← hacc] at hlen
    have hok : ∀ g ∈ acc.2, Ok g := by
      rw [hacc]
      exact elim_ok n gs _ (by simp)
    refine ⟨⟨acc.2, j⟩, hok, ?_, ?_⟩
    · simpa [hgs, Circuit.size] using hlen
    · intro y
      have hv := hval y
      rw [hst] at hv
      exact hv

lemma readers_le_of_cofactor_lower (n q s : ℕ) (b : Bool) (C : Circuit)
    (hC : FanInTwo C) (hsize : C.size ≤ s)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y b)) ≠ C.eval (List.ofFn (Fin.snoc y' b)))
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y b))) →
      q ≤ E.size) :
    q + readerCount n (C.gates.map normGate) ≤ s := by
  obtain ⟨E, hE, hbound, hev⟩ := fix_last_counted n b C hC hnc
  have := hlower E hE hev
  omega

def setReaderCount (K : Finset ℕ) : List Gate → ℕ
  | [] => 0
  | g :: gs => (if ∃ k ∈ g.inputs, k ∈ K then 1 else 0) + setReaderCount K gs

lemma elim_len_setReaders (n : ℕ) (K : Finset ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      (∀ g ∈ gs, NOk g) →
      (∀ k ∈ K, k < acc.1.length ∧ ∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
      (elim n gs acc).2.length + setReaderCount K gs ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _; simp [elim, setReaderCount]
  | cons g gs ih =>
    intro acc hok hK
    have ht := ih (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by
        intro k hk
        obtain ⟨hlt, c, hc⟩ := hK k hk
        refine ⟨by simp [elimStep]; omega, c, ?_⟩
        simp only [elimStep]
        rw [getD_snoc_ne _ _ _ _ (by omega)]
        exact hc)
    have he : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [he, List.length_cons]
    by_cases hr : ∃ k ∈ g.inputs, k ∈ K
    · obtain ⟨k, hkg, hk⟩ := hr
      obtain ⟨_, c, hc⟩ := hK k hk
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have hs : (elimStep n acc g).2.length = acc.2.length := by
        simp only [elimStep, hnone]
        simp
      have hr : ∃ k ∈ g.inputs, k ∈ K := ⟨k, hkg, hk⟩
      simp only [setReaderCount, ite_eq_left hr]
      omega
    · have hs : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      simp only [setReaderCount, ite_eq_right hr]
      omega

lemma elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have he : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [he, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

lemma elim_status_length (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elim]
  | cons g gs ih =>
    change (elim n gs (elimStep n acc g)).1.length = _
    rw [ih]
    simp [elimStep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

lemma simplify_and_false (m : ℕ) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hz : Sum.inl false ∈ ins) :
    simplify GateOp.and m ins = (none, Sum.inl false) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    (try cases a) <;> (try cases b) <;> simp_all [simplify, simpAnd]
  rcases hz with h | h <;> simp_all

lemma elim_and_reader_bound (n k : ℕ) (pre post : List Gate) (g : Gate)
    (acc : List Stat × List Gate)
    (hok : ∀ h ∈ pre ++ g :: post, NOk h)
    (hk : k < acc.1.length) (hz : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (hg : g.op = GateOp.and) (hread : k ∈ g.inputs) :
    (elim n (pre ++ g :: post) acc).2.length + readerCount k pre + 1 +
        setReaderCount {k, acc.1.length + pre.length} post ≤
      acc.2.length + (pre ++ g :: post).length := by
  let mid := elim n pre acc
  have hm : mid.1.length = acc.1.length + pre.length := elim_status_length n pre acc
  have hmk : k < mid.1.length := by omega
  have hmz : mid.1.getD k (Sum.inl false) = Sum.inl false := by
    rw [elim_getD n k _ pre acc hk, hz]
  have hpre := elim_len_readers n k pre acc
    (fun h hh => hok h (List.mem_append_left _ hh)) hk ⟨false, hz⟩
  have hgood := hok g (List.mem_append_right _ List.mem_cons_self)
  have hs : simplify g.op (n + mid.2.length)
      (g.inputs.map fun i => mid.1.getD i (Sum.inl false)) = (none, Sum.inl false) := by
    rw [hg]
    apply simplify_and_false
    · simpa using hgood.1.2
    · exact List.mem_map.2 ⟨k, hread, hmz⟩
  have hstep : elimStep n mid g = (mid.1 ++ [Sum.inl false], mid.2) := by
    simp only [elimStep]
    rw [hs]
    simp
  have htail := elim_len_setReaders n {k, acc.1.length + pre.length} post
    (elimStep n mid g)
    (fun h hh => hok h (List.mem_append_right _ (List.mem_cons_of_mem _ hh)))
    (by
      intro j hj
      simp only [Finset.mem_insert, Finset.mem_singleton] at hj
      rcases hj with rfl | rfl
      · refine ⟨by rw [hstep]; simp; omega, false, ?_⟩
        rw [hstep, getD_snoc_ne _ _ _ _ (by omega)]
        exact hmz
      · refine ⟨by rw [hstep]; simp; omega, false, ?_⟩
        rw [hstep, ← hm, getD_snoc_eq])
  have he : elim n (pre ++ g :: post) acc = elim n post (elimStep n mid g) := by
    simp [elim, List.foldl_append, mid]
  rw [he, hstep]
  rw [hstep] at htail
  simp only [List.length_append, List.length_cons]
  change mid.2.length + readerCount k pre ≤ acc.2.length + pre.length at hpre
  dsimp only at htail
  omega

lemma readerCount_append (k : ℕ) (xs ys : List Gate) :
    readerCount k (xs ++ ys) = readerCount k xs + readerCount k ys := by
  induction xs with
  | nil => simp [readerCount]
  | cons g gs ih => simp [readerCount, ih, Nat.add_assoc]

lemma setReaderCount_pair_cons (k l : ℕ) (g : Gate) (gs : List Gate) :
    setReaderCount {k, l} (g :: gs) =
      (if k ∈ g.inputs ∨ l ∈ g.inputs then 1 else 0) + setReaderCount {k, l} gs := by
  have he : (∃ i ∈ g.inputs, i ∈ ({k, l} : Finset ℕ)) ↔ k ∈ g.inputs ∨ l ∈ g.inputs := by
    constructor
    · rintro ⟨i, hi, his⟩
      simp only [Finset.mem_insert, Finset.mem_singleton] at his
      rcases his with rfl | rfl
      · exact Or.inl hi
      · exact Or.inr hi
    · rintro (hk | hl)
      · exact ⟨k, hk, by simp⟩
      · exact ⟨l, hl, by simp⟩
  simp only [setReaderCount, he]

lemma setReaderCount_pair_ge (k l : ℕ) (gs : List Gate) :
    readerCount k gs ≤ setReaderCount {k, l} gs := by
  induction gs with
  | nil => simp [readerCount, setReaderCount]
  | cons g gs ih =>
    rw [setReaderCount_pair_cons]
    by_cases hk : k ∈ g.inputs <;> by_cases hl : l ∈ g.inputs <;>
      simp_all [readerCount] <;> omega

lemma setReaderCount_pair_extra (k l : ℕ) (gs : List Gate)
    (hx : ∃ g ∈ gs, l ∈ g.inputs ∧ k ∉ g.inputs) :
    readerCount k gs + 1 ≤ setReaderCount {k, l} gs := by
  induction gs with
  | nil => simpa using hx
  | cons g gs ih =>
    rw [setReaderCount_pair_cons]
    obtain ⟨h, hh, hl, hk⟩ := hx
    rcases List.mem_cons.mp hh with rfl | hh
    · have ht := setReaderCount_pair_ge k l gs
      simp only [readerCount, ite_eq_right hk, zero_add, hl, or_true, ite_true]
      omega
    · have ht := ih ⟨h, hh, hl, hk⟩
      by_cases hkg : k ∈ g.inputs <;> by_cases hlg : l ∈ g.inputs <;>
        simp_all [readerCount] <;> omega

lemma elim_and_extra_saving (n k : ℕ) (pre post : List Gate) (g : Gate)
    (acc : List Stat × List Gate)
    (hok : ∀ h ∈ pre ++ g :: post, NOk h)
    (hk : k < acc.1.length) (hz : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (hg : g.op = GateOp.and) (hread : k ∈ g.inputs)
    (hconsumer : ∃ h ∈ post, acc.1.length + pre.length ∈ h.inputs ∧ k ∉ h.inputs) :
    (elim n (pre ++ g :: post) acc).2.length +
        readerCount k (pre ++ g :: post) + 1 ≤
      acc.2.length + (pre ++ g :: post).length := by
  have hb := elim_and_reader_bound n k pre post g acc hok hk hz hg hread
  have he := setReaderCount_pair_extra k (acc.1.length + pre.length) post hconsumer
  rw [readerCount_append]
  simp only [readerCount, ite_eq_left hread]
  omega

lemma fix_last_with_savings (n q : ℕ) (b : Bool) (C : Circuit)
    (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y b)) ≠ C.eval (List.ofFn (Fin.snoc y' b)))
    (hbudget : (elim n (C.gates.map normGate) (initStats n b, [])).2.length + q ≤ C.size) :
    ∃ E : Circuit, FanInTwo E ∧ E.size + q ≤ C.size ∧
      ∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y b)) := by
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hC g0 hg0)
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y)
        (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) =
        C.eval (List.ofFn (Fin.snoc y b)) := by
    intro y
    rw [((hinv y).2 C.output).2, hgs, wiresFrom_norm]
    rfl
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | inr j =>
    have hok : ∀ g ∈ acc.2, Ok g := by
      rw [hacc]
      exact elim_ok n gs _ (by simp)
    refine ⟨⟨acc.2, j⟩, hok, hbudget, ?_⟩
    intro y
    have hv := hval y
    rw [hst] at hv
    exact hv

lemma fix_false_and_extra (n : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate)
    (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hgs : C.gates.map normGate = pre ++ g :: post)
    (hg : g.op = GateOp.and) (hread : n ∈ g.inputs)
    (hconsumer : ∃ h ∈ post, n + 1 + pre.length ∈ h.inputs ∧ n ∉ h.inputs) :
    ∃ E : Circuit, FanInTwo E ∧
      E.size + readerCount n (C.gates.map normGate) + 1 ≤ C.size ∧
      ∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false)) := by
  have hok : ∀ h ∈ pre ++ g :: post, NOk h := by
    intro h hh
    rw [← hgs] at hh
    obtain ⟨h0, hh0, rfl⟩ := List.mem_map.1 hh
    exact normGate_nok h0 (hC h0 hh0)
  have hb := elim_and_extra_saving n n pre post g (initStats n false, []) hok
    (by simp [initStats]) (getD_snoc_len _ _ _ _ (by simp)) hg hread
    (by simpa [initStats] using hconsumer)
  have hlen : (pre ++ g :: post).length = C.size := by
    rw [← hgs]
    simp [Circuit.size]
  have hbudget : (elim n (C.gates.map normGate) (initStats n false, [])).2.length +
      (readerCount n (C.gates.map normGate) + 1) ≤ C.size := by
    simpa only [hgs, hlen, List.length_nil, Nat.zero_add, Nat.add_assoc] using hb
  obtain ⟨E, hE, hsize, hev⟩ := fix_last_with_savings n
    (readerCount n (C.gates.map normGate) + 1) false C hC hnc hbudget
  exact ⟨E, hE, by omega, hev⟩

lemma and_readers_le_of_cofactor_lower (n q s : ℕ) (C : Circuit)
    (pre post : List Gate) (g : Gate)
    (hC : FanInTwo C) (hsize : C.size ≤ s)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false))) →
      q ≤ E.size)
    (hgs : C.gates.map normGate = pre ++ g :: post)
    (hg : g.op = GateOp.and) (hread : n ∈ g.inputs)
    (hconsumer : ∃ h ∈ post, n + 1 + pre.length ∈ h.inputs ∧ n ∉ h.inputs) :
    q + readerCount n (C.gates.map normGate) + 1 ≤ s := by
  obtain ⟨E, hE, hbound, hev⟩ := fix_false_and_extra n C pre post g hC hnc
    hgs hg hread hconsumer
  have := hlower E hE hev
  omega

namespace Consumer

open PEqualNP.CircuitLowerBounds

lemma two_inputs_of_distinct (l : List ℕ) (v w : ℕ) (hvw : v ≠ w)
    (hl : l.length ≤ 2) (hv : v ∈ l) (hw : w ∈ l) :
    l = [v, w] ∨ l = [w, v] := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, t⟩⟩⟩
  · simp at hv
  · simp only [List.mem_singleton] at hv hw
    exact False.elim (hvw (hv.trans hw.symm))
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hv hw
    rcases hv with rfl | rfl <;> rcases hw with rfl | rfl
    · exact False.elim (hvw rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact False.elim (hvw rfl)
  · simp at hl

lemma and_value_implies_input {A : Type} (F : A → ℕ → Bool) (g : Gate) (v w : ℕ)
    (hop : g.op = GateOp.and) (hv : v ∈ g.inputs)
    (heval : ∀ a, F a w = g.op.eval (g.inputs.map (F a))) :
    ∀ a, F a w = true → F a v = true := by
  intro a ha
  rw [heval a, hop] at ha
  have hall : ∀ b ∈ g.inputs.map (F a), b = true := by
    simpa [GateOp.eval, List.all_eq_true] using ha
  exact hall _ (List.mem_map.2 ⟨v, hv, rfl⟩)

lemma consumer_absorbs {A : Type} (F : A → ℕ → Bool) (g : Gate) (v w out : ℕ)
    (hvw : v ≠ w) (hv : v ∈ g.inputs) (hw : w ∈ g.inputs)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2) (hnot : g.op = GateOp.not → g.inputs.length ≤ 1)
    (heval : ∀ a, F a out = g.op.eval (g.inputs.map (F a)))
    (himp : ∀ a, F a w = true → F a v = true) :
    (∀ a, F a out = F a w) ∨ (∀ a, F a out = F a v) := by
  have hins := two_inputs_of_distinct g.inputs v w hvw hlen hv hw
  rcases hop with hop | hop | hop
  · left
    intro a
    rw [heval a, hop]
    rcases hins with hins | hins <;> rw [hins] <;>
      cases hvv : F a v <;> cases hww : F a w <;>
      simp_all [GateOp.eval]
  · right
    intro a
    rw [heval a, hop]
    rcases hins with hins | hins <;> rw [hins] <;>
      cases hvv : F a v <;> cases hww : F a w <;>
      simp_all [GateOp.eval]
  · have := hnot hop
    rcases hins with hins | hins <;> simp_all

lemma consumer_avoids_raw_input {A : Type} (F : A → ℕ → Bool)
    (source consumer : Gate) (n v p q : ℕ) (hv : v < n) (hpq : p < q)
    (hsource : source.op = GateOp.and) (hsourcev : v ∈ source.inputs)
    (hread : n + p ∈ consumer.inputs)
    (hop : consumer.op = GateOp.and ∨ consumer.op = GateOp.or ∨ consumer.op = GateOp.not)
    (hlen : consumer.inputs.length ≤ 2)
    (hnot : consumer.op = GateOp.not → consumer.inputs.length ≤ 1)
    (hsourceval : ∀ a, F a (n + p) = source.op.eval (source.inputs.map (F a)))
    (hconsumerval : ∀ a, F a (n + q) = consumer.op.eval (consumer.inputs.map (F a)))
    (hnoalias : ∀ j, j < n + q → ¬ ∀ a, F a (n + q) = F a j) :
    v ∉ consumer.inputs := by
  intro hraw
  have himp := and_value_implies_input F source v (n + p) hsource hsourcev hsourceval
  rcases consumer_absorbs F consumer v (n + p) (n + q) (by omega) hraw hread
      hop hlen hnot hconsumerval himp with ha | ha
  · exact hnoalias (n + p) (by omega) ha
  · exact hnoalias v (by omega) ha

lemma live_consumer_avoids_raw_input {A : Type} (F : A → ℕ → Bool)
    (gs : List Gate) (n v p : ℕ) (source : Gate) (hv : v < n)
    (hsource : gs[p]? = some source) (hsourceop : source.op = GateOp.and)
    (hsourcev : v ∈ source.inputs)
    (hnormal : ∀ (q : ℕ) (g : Gate), gs[q]? = some g →
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 ∧ (g.op = GateOp.not → g.inputs.length ≤ 1))
    (hvalues : ∀ (q : ℕ) (g : Gate), gs[q]? = some g →
      ∀ a, F a (n + q) = g.op.eval (g.inputs.map (F a)))
    (hnoalias : ∀ q, q < gs.length → ∀ j, j < n + q →
      ¬ ∀ a, F a (n + q) = F a j)
    (hlive : ∃ q, p < q ∧ ∃ g, gs[q]? = some g ∧ n + p ∈ g.inputs) :
    ∃ q g, p < q ∧ gs[q]? = some g ∧ n + p ∈ g.inputs ∧ v ∉ g.inputs := by
  obtain ⟨q, hpq, g, hq, hread⟩ := hlive
  have hqlt : q < gs.length := by
    by_contra h
    have hnone : gs[q]? = none := List.getElem?_eq_none_iff.2 (by omega)
    rw [hnone] at hq
    cases hq
  obtain ⟨hop, hlen, hnot⟩ := hnormal q g hq
  refine ⟨q, g, hpq, hq, hread, ?_⟩
  exact consumer_avoids_raw_input F source g n v p q hv hpq hsourceop hsourcev
    hread hop hlen hnot (hvalues p source hsource) (hvalues q g hq) (hnoalias q hqlt)

end Consumer

lemma elim_len_final_constants (n : ℕ) (K : Finset ℕ) (gs : List Gate) :
    ∀ acc : List Stat × List Gate,
      (∀ g ∈ gs, NOk g) →
      (∀ j g, gs[j]? = some g → ∀ k ∈ g.inputs, k < acc.1.length + j) →
      (∀ k ∈ K, ∃ b, (elim n gs acc).1.getD k (Sum.inl false) = Sum.inl b) →
      (elim n gs acc).2.length + setReaderCount K gs ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc hok back constants; simp [elim, setReaderCount]
  | cons g gs ih =>
    intro acc hok back constants
    have he : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    have ht := ih (elimStep n acc g)
      (fun h hh => hok h (List.mem_cons_of_mem _ hh))
      (by
        intro j h hj k hk
        have hb := back (j + 1) h (by simpa using hj) k hk
        dsimp only [elimStep]
        simp only [List.length_append, List.length_singleton]
        omega)
      (by simpa only [← he] using constants)
    by_cases hr : ∃ k ∈ g.inputs, k ∈ K
    · obtain ⟨k, hkg, hkK⟩ := hr
      have hk : k < acc.1.length := by simpa using back 0 g (by simp) k hkg
      obtain ⟨b, hb⟩ := constants k hkK
      have hb' : acc.1.getD k (Sum.inl false) = Sum.inl b := by
        rw [elim_getD n k _ (g :: gs) acc hk] at hb
        exact hb
      have hnok := hok g List.mem_cons_self
      have hn : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨b, List.mem_map.2 ⟨k, hkg, hb'⟩⟩
      have hs : (elimStep n acc g).2.length = acc.2.length := by
        simp only [elimStep]
        rw [hn]
        simp
      have hr : ∃ k ∈ g.inputs, k ∈ K := ⟨k, hkg, hkK⟩
      rw [he]
      simp only [setReaderCount, ite_eq_left hr, List.length_cons]
      omega
    · have hs : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      rw [he]
      simp only [setReaderCount, ite_eq_right hr, zero_add, List.length_cons]
      omega

lemma elim_output_status (n : ℕ) (pre post : List Gate) (g : Gate)
    (acc : List Stat × List Gate) :
    (elim n (pre ++ g :: post) acc).1.getD (acc.1.length + pre.length) (Sum.inl false) =
      (simplify g.op (n + (elim n pre acc).2.length)
        (g.inputs.map fun i => (elim n pre acc).1.getD i (Sum.inl false))).2 := by
  have hm := elim_status_length n pre acc
  have he : elim n (pre ++ g :: post) acc = elim n post (elimStep n (elim n pre acc) g) := by
    simp [elim, List.foldl_append]
  rw [he, elim_getD]
  · simp only [elimStep]
    rw [← hm, getD_snoc_eq]
  · simp [elimStep, hm]

lemma elim_before_status (n k : ℕ) (pre post : List Gate)
    (acc : List Stat × List Gate) (hk : k < acc.1.length + pre.length) :
    (elim n (pre ++ post) acc).1.getD k (Sum.inl false) =
      (elim n pre acc).1.getD k (Sum.inl false) := by
  have he : elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
    simp [elim, List.foldl_append]
  rw [he, elim_getD]
  rw [elim_status_length]
  exact hk

lemma elim_and_output_false (n k : ℕ) (pre post : List Gate) (g : Gate)
    (acc : List Stat × List Gate) (hop : g.op = GateOp.and)
    (hinputs : g.inputs.length ≤ 2) (hread : k ∈ g.inputs)
    (hback : k < acc.1.length + pre.length)
    (hconstant : (elim n (pre ++ g :: post) acc).1.getD k (Sum.inl false) = Sum.inl false) :
    (elim n (pre ++ g :: post) acc).1.getD (acc.1.length + pre.length) (Sum.inl false) = Sum.inl false := by
  have hm : (elim n pre acc).1.getD k (Sum.inl false) = Sum.inl false := by
    rw [elim_before_status n k pre (g :: post) acc hback] at hconstant
    exact hconstant
  rw [elim_output_status, hop]
  have he := simplify_and_false (n + (elim n pre acc).2.length)
    (g.inputs.map fun i => (elim n pre acc).1.getD i (Sum.inl false))
    (by simpa using hinputs) (List.mem_map.2 ⟨k, hread, hm⟩)
  rw [he]

lemma elim_not_output (n k : ℕ) (pre post : List Gate) (acc : List Stat × List Gate)
    (b : Bool) (hback : k < acc.1.length + pre.length)
    (hconstant : (elim n (pre ++ ⟨GateOp.not, [k]⟩ :: post) acc).1.getD k
      (Sum.inl false) = Sum.inl b) :
    (elim n (pre ++ ⟨GateOp.not, [k]⟩ :: post) acc).1.getD (acc.1.length + pre.length)
      (Sum.inl false) = Sum.inl (!b) := by
  have hm : (elim n pre acc).1.getD k (Sum.inl false) = Sum.inl b := by
    rw [elim_before_status n k pre (⟨GateOp.not, [k]⟩ :: post) acc hback] at hconstant
    exact hconstant
  rw [elim_output_status]
  simp only [List.map_cons, List.map_nil, hm]
  rfl

lemma setReaderCount_eq_countP (K : Finset ℕ) (gs : List Gate) :
    setReaderCount K gs = gs.countP (fun g => decide (∃ k ∈ g.inputs, k ∈ K)) := by
  induction gs with
  | nil => rfl
  | cons g gs ih => simp [setReaderCount, List.countP_cons, ih, Nat.add_comm]

lemma setReaderCount_eq_card (K : Finset ℕ) (gs : List Gate) :
    setReaderCount K gs =
      (Finset.univ.filter fun i : Fin gs.length => ∃ k ∈ (gs.get i).inputs, k ∈ K).card := by
  rw [setReaderCount_eq_countP]
  have h := List.countP_ofFn gs.get (fun g => decide (∃ k ∈ g.inputs, k ∈ K))
  simpa only [List.ofFn_get, decide_eq_true_eq] using h

lemma marked_readers_le (K : Finset ℕ) (gs : List Gate) (M : Finset (Fin gs.length))
    (hits : ∀ i ∈ M, ∃ k ∈ (gs.get i).inputs, k ∈ K) :
    M.card ≤ setReaderCount K gs := by
  rw [setReaderCount_eq_card]
  apply Finset.card_le_card
  intro i hi
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hits i hi⟩

lemma four_readers_le (K : Finset ℕ) (gs : List Gate) (p q r s : Fin gs.length)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s)
    (hits : ∀ i ∈ ({p, q, r, s} : Finset (Fin gs.length)),
      ∃ k ∈ (gs.get i).inputs, k ∈ K) : 4 ≤ setReaderCount K gs := by
  have h := marked_readers_le K gs {p, q, r, s} hits
  simpa [hpq, hpr, hps, hqr, hqs, hrs] using h

lemma gate_decomposition (gs : List Gate) (p : Fin gs.length) :
    gs = gs.take p.val ++ gs.get p :: gs.drop (p.val + 1) := by
  rw [List.get_eq_getElem, List.getElem_cons_drop p.isLt, List.take_append_drop]

lemma final_and_false (n k : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (p : Fin gs.length) (hop : (gs.get p).op = GateOp.and)
    (hlen : (gs.get p).inputs.length ≤ 2) (hread : k ∈ (gs.get p).inputs)
    (hback : k < acc.1.length + p.val)
    (hz : (elim n gs acc).1.getD k (Sum.inl false) = Sum.inl false) :
    (elim n gs acc).1.getD (acc.1.length + p.val) (Sum.inl false) = Sum.inl false := by
  have h := elim_and_output_false n k (gs.take p.val) (gs.drop (p.val + 1)) (gs.get p)
    acc hop hlen hread (by simpa using hback) (by simpa [← gate_decomposition gs p] using hz)
  simpa only [← gate_decomposition gs p, List.length_take_of_le (Nat.le_of_lt p.isLt)] using h

lemma final_not (n k : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (p : Fin gs.length) (hg : gs.get p = ⟨GateOp.not, [k]⟩)
    (b : Bool) (hback : k < acc.1.length + p.val)
    (hc : (elim n gs acc).1.getD k (Sum.inl false) = Sum.inl b) :
    (elim n gs acc).1.getD (acc.1.length + p.val) (Sum.inl false) = Sum.inl (!b) := by
  have eq : gs = gs.take p.val ++ ⟨GateOp.not, [k]⟩ :: gs.drop (p.val + 1) := by
    rw [← hg]
    exact gate_decomposition gs p
  have h := elim_not_output n k (gs.take p.val) (gs.drop (p.val + 1)) acc b
    (by simpa using hback) (by simpa [← eq] using hc)
  simpa only [← eq, List.length_take_of_le (Nat.le_of_lt p.isLt)] using h

lemma final_two_constants (n k l : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (p : Fin gs.length) (hop : (gs.get p).op = GateOp.and ∨ (gs.get p).op = GateOp.or)
    (hlen : (gs.get p).inputs.length ≤ 2) (hkl : k ≠ l)
    (hk : k ∈ (gs.get p).inputs) (hl : l ∈ (gs.get p).inputs)
    (hbackk : k < acc.1.length + p.val) (hbackl : l < acc.1.length + p.val)
    (b c : Bool) (hb : (elim n gs acc).1.getD k (Sum.inl false) = Sum.inl b)
    (hc : (elim n gs acc).1.getD l (Sum.inl false) = Sum.inl c) :
    ∃ d, (elim n gs acc).1.getD (acc.1.length + p.val) (Sum.inl false) = Sum.inl d := by
  have hins := Consumer.two_inputs_of_distinct (gs.get p).inputs k l hkl hlen hk hl
  have hbk : (elim n (gs.take p.val) acc).1.getD k (Sum.inl false) = Sum.inl b := by
    have he := elim_before_status n k (gs.take p.val)
      (gs.get p :: gs.drop (p.val + 1)) acc (by simpa using hbackk)
    rw [← gate_decomposition gs p, hb] at he
    exact he.symm
  have hcl : (elim n (gs.take p.val) acc).1.getD l (Sum.inl false) = Sum.inl c := by
    have he := elim_before_status n l (gs.take p.val)
      (gs.get p :: gs.drop (p.val + 1)) acc (by simpa using hbackl)
    rw [← gate_decomposition gs p, hc] at he
    exact he.symm
  have he := elim_output_status n (gs.take p.val) (gs.drop (p.val + 1)) (gs.get p) acc
  rw [← gate_decomposition gs p, List.length_take_of_le (Nat.le_of_lt p.isLt)] at he
  rw [he]
  rcases hop with hop | hop <;> rcases hins with hins | hins <;>
    rw [hop, hins] <;> simp only [List.map_cons, List.map_nil, hbk, hcl] <;>
    simp [simplify, simpAnd, simpOr]

lemma nand_saving_distinct (n k : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (p q r s : Fin gs.length)
    (normal : ∀ g ∈ gs, NOk g)
    (back : ∀ j g, gs[j]? = some g → ∀ a ∈ g.inputs, a < acc.1.length + j)
    (hk : k < acc.1.length) (hkfalse : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (pand : (gs.get p).op = GateOp.and) (pread : k ∈ (gs.get p).inputs)
    (qnot : gs.get q = ⟨GateOp.not, [acc.1.length + p.val]⟩)
    (rread : k ∈ (gs.get r).inputs) (sread : acc.1.length + q.val ∈ (gs.get s).inputs)
    (hpq : p ≠ q) (hpr : p ≠ r) (hps : p ≠ s)
    (hqr : q ≠ r) (hqs : q ≠ s) (hrs : r ≠ s) :
    (elim n gs acc).2.length + 4 ≤ acc.2.length + gs.length := by
  let K : Finset ℕ := {k, acc.1.length + p.val, acc.1.length + q.val}
  have hkfinal : (elim n gs acc).1.getD k (Sum.inl false) = Sum.inl false := by
    rw [elim_getD n k _ gs acc hk, hkfalse]
  have hpgood := normal (gs.get p) (List.get_mem gs p)
  have hpfalse := final_and_false n k gs acc p pand hpgood.1.2 pread (by omega) hkfinal
  have hqback : acc.1.length + p.val < acc.1.length + q.val := by
    apply back q.val (gs.get q) (by simp) (acc.1.length + p.val)
    simp only [qnot, List.mem_singleton]
  have hqtrue := final_not n (acc.1.length + p.val) gs acc q qnot false hqback hpfalse
  have hc : ∀ a ∈ K, ∃ b, (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl b := by
    intro a ha
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl
    · exact ⟨false, hkfinal⟩
    · exact ⟨false, hpfalse⟩
    · exact ⟨true, hqtrue⟩
  have count := four_readers_le K gs p q r s hpq hpr hps hqr hqs hrs (by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl | rfl
    · exact ⟨k, pread, by simp [K]⟩
    · exact ⟨acc.1.length + p.val, by simp only [qnot, List.mem_singleton], by simp [K]⟩
    · exact ⟨k, rread, by simp [K]⟩
    · exact ⟨acc.1.length + q.val, sread, by simp [K]⟩)
  have budget := elim_len_final_constants n K gs acc normal back hc
  omega

lemma nand_saving_collision (n k : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (p q r t : Fin gs.length)
    (normal : ∀ g ∈ gs, NOk g)
    (back : ∀ j g, gs[j]? = some g → ∀ a ∈ g.inputs, a < acc.1.length + j)
    (hk : k < acc.1.length) (hkfalse : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (pand : (gs.get p).op = GateOp.and) (pread : k ∈ (gs.get p).inputs)
    (qnot : gs.get q = ⟨GateOp.not, [acc.1.length + p.val]⟩)
    (rraw : k ∈ (gs.get r).inputs) (rnot : acc.1.length + q.val ∈ (gs.get r).inputs)
    (tread : acc.1.length + r.val ∈ (gs.get t).inputs) :
    (elim n gs acc).2.length + 4 ≤ acc.2.length + gs.length := by
  let K : Finset ℕ := {k, acc.1.length + p.val, acc.1.length + q.val, acc.1.length + r.val}
  have hkfinal : (elim n gs acc).1.getD k (Sum.inl false) = Sum.inl false := by
    rw [elim_getD n k _ gs acc hk, hkfalse]
  have hpgood := normal (gs.get p) (List.get_mem gs p)
  have hrgood := normal (gs.get r) (List.get_mem gs r)
  have hpfalse := final_and_false n k gs acc p pand hpgood.1.2 pread (by omega) hkfinal
  have hpq : p.val < q.val := by
    have hb := back q.val (gs.get q) (by simp) (acc.1.length + p.val) (by simp only [qnot, List.mem_singleton])
    omega
  have hqr : q.val < r.val := by
    have hb := back r.val (gs.get r) (by simp) (acc.1.length + q.val) rnot
    omega
  have hrt : r.val < t.val := by
    have hb := back t.val (gs.get t) (by simp) (acc.1.length + r.val) tread
    omega
  have hqtrue := final_not n (acc.1.length + p.val) gs acc q qnot false (by omega) hpfalse
  have hins := Consumer.two_inputs_of_distinct (gs.get r).inputs k (acc.1.length + q.val)
    (by omega) hrgood.1.2 rraw rnot
  have hrop : (gs.get r).op = GateOp.and ∨ (gs.get r).op = GateOp.or := by
    rcases hrgood.1.1 with hop | hop | hop
    · exact Or.inl hop
    · exact Or.inr hop
    · have hlen := hrgood.2 hop
      rcases hins with hins | hins <;> rw [hins] at hlen <;> simp at hlen
  obtain ⟨b, hrconstant⟩ := final_two_constants n k (acc.1.length + q.val) gs acc r hrop
    hrgood.1.2 (by omega) rraw rnot (by omega) (by omega) false true hkfinal hqtrue
  have hc : ∀ a ∈ K, ∃ b, (elim n gs acc).1.getD a (Sum.inl false) = Sum.inl b := by
    intro a ha
    simp only [K, Finset.mem_insert, Finset.mem_singleton] at ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact ⟨false, hkfinal⟩
    · exact ⟨false, hpfalse⟩
    · exact ⟨true, hqtrue⟩
    · exact ⟨b, hrconstant⟩
  have count := four_readers_le K gs p q r t
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by
      intro i hi
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact ⟨k, pread, by simp [K]⟩
      · exact ⟨acc.1.length + p.val, by simp only [qnot, List.mem_singleton], by simp [K]⟩
      · exact ⟨k, rraw, by simp [K]⟩
      · exact ⟨acc.1.length + r.val, tread, by simp [K]⟩)
  have budget := elim_len_final_constants n K gs acc normal back hc
  omega

lemma nand_four_saving (n k : ℕ) (gs : List Gate) (acc : List Stat × List Gate)
    (p q r : Fin gs.length)
    (normal : ∀ g ∈ gs, NOk g)
    (back : ∀ j g, gs[j]? = some g → ∀ a ∈ g.inputs, a < acc.1.length + j)
    (hk : k < acc.1.length) (hkfalse : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (pand : (gs.get p).op = GateOp.and) (pread : k ∈ (gs.get p).inputs)
    (qnot : gs.get q = ⟨GateOp.not, [acc.1.length + p.val]⟩)
    (rread : k ∈ (gs.get r).inputs) (hpr : p ≠ r)
    (live : ∀ i : Fin gs.length,
      (∃ b, (elim n gs acc).1.getD (acc.1.length + i.val) (Sum.inl false) = Sum.inl b) →
      ∃ j : Fin gs.length, acc.1.length + i.val ∈ (gs.get j).inputs) :
    (elim n gs acc).2.length + 4 ≤ acc.2.length + gs.length := by
  have hkfinal : (elim n gs acc).1.getD k (Sum.inl false) = Sum.inl false := by
    rw [elim_getD n k _ gs acc hk, hkfalse]
  have hpgood := normal (gs.get p) (List.get_mem gs p)
  have hpfalse := final_and_false n k gs acc p pand hpgood.1.2 pread (by omega) hkfinal
  have hpq : p.val < q.val := by
    have hb := back q.val (gs.get q) (by simp) (acc.1.length + p.val)
      (by simp only [qnot, List.mem_singleton])
    omega
  have hqtrue := final_not n (acc.1.length + p.val) gs acc q qnot false (by omega) hpfalse
  obtain ⟨s, sread⟩ := live q ⟨true, hqtrue⟩
  have hqs : q.val < s.val := by
    have hb := back s.val (gs.get s) (by simp) (acc.1.length + q.val) sread
    omega
  have hqr : q ≠ r := by
    intro heq
    subst r
    rw [qnot] at rread
    simp only [List.mem_singleton] at rread
    omega
  by_cases hsr : s = r
  · subst s
    have hrgood := normal (gs.get r) (List.get_mem gs r)
    have hins := Consumer.two_inputs_of_distinct (gs.get r).inputs k (acc.1.length + q.val)
      (by omega) hrgood.1.2 rread sread
    have hrop : (gs.get r).op = GateOp.and ∨ (gs.get r).op = GateOp.or := by
      rcases hrgood.1.1 with hop | hop | hop
      · exact Or.inl hop
      · exact Or.inr hop
      · have hlen := hrgood.2 hop
        rcases hins with hins | hins <;> rw [hins] at hlen <;> simp at hlen
    obtain ⟨b, hrconstant⟩ := final_two_constants n k (acc.1.length + q.val) gs acc r hrop
      hrgood.1.2 (by omega) rread sread (by omega) (by omega) false true hkfinal hqtrue
    obtain ⟨t, tread⟩ := live r ⟨b, hrconstant⟩
    exact nand_saving_collision n k gs acc p q r t normal back hk hkfalse pand pread qnot
      rread sread tread
  · exact nand_saving_distinct n k gs acc p q r s normal back hk hkfalse pand pread qnot
      rread sread (by omega) hpr (by omega) hqr (by omega) (Ne.symm hsr)

lemma restricted_output_not_constant (n : ℕ) (b : Bool) (C : Circuit)
    (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y b)) ≠ C.eval (List.ofFn (Fin.snoc y' b))) :
    ∀ c, (elim n (C.gates.map normGate) (initStats n b, [])).1.getD C.output
      (Sum.inl false) ≠ Sum.inl c := by
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hC g0 hg0)
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y)
        (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn y)) =
        C.eval (List.ofFn (Fin.snoc y b)) := by
    intro y
    rw [((hinv y).2 C.output).2, hgs, wiresFrom_norm]
    rfl
  intro c hc
  obtain ⟨y, y', hne⟩ := hnc
  apply hne
  rw [← hval y, ← hval y', hc]
  rfl

lemma fix_last_nand_four (n : ℕ) (C : Circuit) (gs : List Gate)
    (p q r : Fin gs.length) (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hgs : C.gates.map normGate = gs)
    (back : ∀ j g, gs[j]? = some g → ∀ a ∈ g.inputs, a < n + 1 + j)
    (live : ∀ i : Fin gs.length, n + 1 + i.val ≠ C.output →
      ∃ j : Fin gs.length, n + 1 + i.val ∈ (gs.get j).inputs)
    (pand : (gs.get p).op = GateOp.and) (pread : n ∈ (gs.get p).inputs)
    (qnot : gs.get q = ⟨GateOp.not, [n + 1 + p.val]⟩)
    (rread : n ∈ (gs.get r).inputs) (hpr : p ≠ r) :
    ∃ E : Circuit, FanInTwo E ∧ E.size + 4 ≤ C.size ∧
      ∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false)) := by
  have normal : ∀ g ∈ gs, NOk g := by
    intro g hg
    rw [← hgs] at hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact normGate_nok g0 (hC g0 hg0)
  have outNonconstant := restricted_output_not_constant n false C hC hnc
  rw [hgs] at outNonconstant
  have hbudget := nand_four_saving n n gs (initStats n false, []) p q r normal
    (by simpa [initStats] using back) (by simp [initStats])
    (getD_snoc_len _ _ _ _ (by simp)) pand pread (by simpa [initStats] using qnot)
    rread hpr (by
      intro i hi
      obtain ⟨b, hb⟩ := hi
      have hne : n + 1 + i.val ≠ C.output := by
        intro heq
        apply outNonconstant b
        simpa [initStats, heq] using hb
      simpa [initStats] using live i hne)
  apply fix_last_with_savings n 4 false C hC hnc
  rw [hgs]
  have hlength : gs.length = C.size := by rw [← hgs]; simp [Circuit.size]
  simpa [hlength] using hbudget

lemma nand_lower_bound (n lower : ℕ) (C : Circuit) (gs : List Gate)
    (p q r : Fin gs.length) (hC : FanInTwo C)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hgs : C.gates.map normGate = gs)
    (back : ∀ j g, gs[j]? = some g → ∀ a ∈ g.inputs, a < n + 1 + j)
    (live : ∀ i : Fin gs.length, n + 1 + i.val ≠ C.output →
      ∃ j : Fin gs.length, n + 1 + i.val ∈ (gs.get j).inputs)
    (pand : (gs.get p).op = GateOp.and) (pread : n ∈ (gs.get p).inputs)
    (qnot : gs.get q = ⟨GateOp.not, [n + 1 + p.val]⟩)
    (rread : n ∈ (gs.get r).inputs) (hpr : p ≠ r)
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false))) →
      lower ≤ E.size) : lower + 4 ≤ C.size := by
  obtain ⟨E, hE, size, computes⟩ := fix_last_nand_four n C gs p q r hC hnc hgs back live
    pand pread qnot rread hpr
  have bound := hlower E hE computes
  omega


end NandRestriction

namespace FirstAndClassification


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Restriction

lemma full_gate_value (n : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate)
    (hs : C.gates = pre ++ g :: post)
    (hback : ∀ i ∈ g.inputs, i < n + pre.length) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).getD (n + pre.length) false =
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) := by
  let w := wiresFrom pre (List.ofFn x)
  have hwlen : w.length = n + pre.length := by simp [w, length_wiresFrom]
  have hwfull : C.wires (List.ofFn x) = wiresFrom (g :: post) w := by
    simp only [Circuit.wires, wiresFrom, hs, List.foldl_append, w]
  have hread : ∀ i ∈ g.inputs,
      (C.wires (List.ofFn x)).getD i false = w.getD i false := by
    intro i hi
    rw [hwfull, getD_wiresFrom]
    rw [hwlen]
    exact hback i hi
  rw [List.map_congr_left hread, hwfull]
  change (wiresFrom post (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD
    (n + pre.length) false = _
  rw [getD_wiresFrom _ _ _ (by simp [hwlen])]
  rw [← hwlen, getD_snoc_eq]

lemma full_gate_value_index (n : ℕ) (C : Circuit)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j)
    (j : ℕ) (g : Gate) (hj : C.gates[j]? = some g) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).getD (n + j) false =
      g.op.eval (g.inputs.map fun i => (C.wires (List.ofFn x)).getD i false) := by
  have hlt : j < C.gates.length := by
    by_contra hn
    rw [List.getElem?_eq_none_iff.2 (by omega)] at hj
    cases hj
  have hg : C.gates[j] = g := by simpa [List.getElem?_eq_getElem hlt] using hj
  have hs : C.gates = C.gates.take j ++ g :: C.gates.drop (j + 1) := by
    rw [← hg, List.getElem_cons_drop hlt, List.take_append_drop]
  have hlen : (C.gates.take j).length = j := by simp; omega
  simpa only [hlen] using full_gate_value n C _ _ g hs
    (by simpa only [hlen] using back j g hj) x

lemma minimal_consumer_avoids_input (n : ℕ) (C : Circuit)
    (hfan : FanInTwo C)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j)
    (v p q : ℕ) (source consumer : Gate) (hv : v < n)
    (hsource : C.gates[p]? = some source) (hconsumer : C.gates[q]? = some consumer)
    (hsourceop : source.op = GateOp.and) (hsourcev : v ∈ source.inputs)
    (hread : n + p ∈ consumer.inputs) : v ∉ consumer.inputs := by
  have hcmem : consumer ∈ C.gates := List.mem_of_getElem? hconsumer
  have hpq : p < q := by have := back q consumer hconsumer (n + p) hread; omega
  have hqlt : q < C.size := by
    change q < C.gates.length
    by_contra hn
    rw [List.getElem?_eq_none_iff.2 (by omega)] at hconsumer
    cases hconsumer
  apply Consumer.consumer_avoids_raw_input
    (fun x : Fin n → Bool => fun i => (C.wires (List.ofFn x)).getD i false)
    source consumer n v p q hv hpq hsourceop hsourcev hread
  · simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using (hfan consumer hcmem).1
  · exact (hfan consumer hcmem).2
  · exact hnot consumer hcmem
  · exact full_gate_value_index n C back p source hsource
  · exact full_gate_value_index n C back q consumer hconsumer
  · intro j hj
    exact AliasPruning.minimal_no_alias_index n C hfan hmin q hqlt j hj

lemma normGate_eq_self (g : Gate) (hn : g.op = GateOp.not → g.inputs.length ≤ 1) :
    normGate g = g := by
  obtain ⟨op, ins⟩ := g
  cases op <;> simp only [normGate]
  have hlen : ins.length ≤ 1 := hn rfl
  simp only [List.take_of_length_le hlen]

lemma normalized_map_eq_self (gs : List Gate)
    (hn : ∀ g ∈ gs, g.op = GateOp.not → g.inputs.length ≤ 1) : gs.map normGate = gs := by
  calc
    gs.map normGate = gs.map (fun g => g) := List.map_congr_left (fun g hg => normGate_eq_self g (hn g hg))
    _ = gs := List.map_id' gs

lemma minimal_first_and_unique_consumer (n : ℕ) (C : Circuit) (g : Gate) (post : List Gate)
    (hfan : FanInTwo C) (hsize : C.size ≤ 19)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin (n + 1) → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + 1 + j)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false))) →
      16 ≤ E.size)
    (hgs : C.gates = g :: post) (hg : g.op = GateOp.and) (hread : n ∈ g.inputs)
    (hraw : ∃ q ∈ post, n ∈ q.inputs) : readerCount (n + 1) post = 1 := by
  have hnorm : C.gates.map normGate = g :: post := by
    rw [normalized_map_eq_self C.gates hnot, hgs]
  have havoid : ∀ q ∈ post, n + 1 ∈ q.inputs → n ∉ q.inputs := by
    intro q hq hqread
    obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hq
    exact minimal_consumer_avoids_input (n + 1) C hfan hmin hnot back
      n 0 (j + 1) g q (by omega) (by simp [hgs]) (by simpa [hgs] using hj)
      hg hread (by simpa using hqread)
  have hmax := first_and_has_at_most_one_consumer n C g post hfan hsize hnc hlower
    hnorm hg hread hraw havoid
  have htwo : 0 + 1 < C.size := by
    obtain ⟨q, hq, _⟩ := hraw
    have hlen : 0 < post.length := List.length_pos_of_mem hq
    simp only [Circuit.size, hgs, List.length_cons]
    omega
  obtain ⟨j, hj, q, hq, hqread⟩ := LivePruning.minimal_live_index (n + 1) C hfan hmin 0 htwo
  have hqm : q ∈ post := by
    have hjpos : j ≠ 0 := by omega
    cases j with
    | zero => contradiction
    | succ j =>
      have he : post[j]? = some q := by simpa [hgs] using hq
      exact List.mem_of_getElem? he
  have hqread' : n + 1 ∈ q.inputs := by
    change n + 1 + 0 ∈ LivePruning.effective q at hqread
    have hsub : LivePruning.effective q ⊆ q.inputs := by
      simp only [LivePruning.effective]
      split
      · exact List.take_subset _ _
      · exact List.Subset.refl _
    exact hsub (by simpa using hqread)
  have hpos := (readerCount_pos_iff (n + 1) post).2 ⟨q, hqm, hqread'⟩
  omega

lemma petersen_first_and_unique_consumer (C : Circuit) (b : Fin 10) (post : List Gate)
    (hb : (9 : Fin 10) ≠ b) (hfan : FanInTwo C) (hsize : C.size ≤ 19)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < 10 + j)
    (hgs : C.gates = ⟨GateOp.and, [9, b.val]⟩ :: post)
    (hev : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x)
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin 9 → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false))) →
      16 ≤ E.size) : readerCount 10 post = 1 := by
  have hC : C = ⟨⟨GateOp.and, [9, b.val]⟩ :: post, C.output⟩ := by cases C; simp_all
  have hev' : ∀ x : Fin 10 → Bool,
      (Circuit.mk (⟨GateOp.and, [9, b.val]⟩ :: post) C.output).eval (List.ofFn x) = petersen x := by
    intro x
    rw [← hC]
    exact hev x
  obtain ⟨q, hq, hread⟩ := first_and_input_reread 9 b hb post C.output hev'
  have hraw : ∃ q ∈ post, 9 ∈ q.inputs := by
    refine ⟨q, hq, ?_⟩
    have hsub : effectiveInputs q ⊆ q.inputs := by
      simp only [effectiveInputs]
      split
      · exact List.take_subset _ _
      · exact List.Subset.refl _
    exact hsub hread
  have hnc : ∃ y y' : Fin 9 → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)) := by
    refine ⟨(fun _ => false), (fun i => decide (i = 0 ∨ i = 1)), ?_⟩
    rw [hev, hev]
    decide +kernel
  exact minimal_first_and_unique_consumer 9 C _ post hfan hsize hmin hnot back hnc hlower
    hgs rfl (by simp) hraw

lemma minimal_consumer_avoids_implicate (n : ℕ) (C : Circuit)
    (hfan : FanInTwo C)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j)
    (v w q : ℕ) (consumer : Gate) (hvw : v ≠ w) (hv : v < n + q)
    (hconsumer : C.gates[q]? = some consumer) (hread : w ∈ consumer.inputs)
    (himp : ∀ x : Fin n → Bool,
      (C.wires (List.ofFn x)).getD w false = true →
      (C.wires (List.ofFn x)).getD v false = true) : v ∉ consumer.inputs := by
  intro hraw
  have hcmem : consumer ∈ C.gates := List.mem_of_getElem? hconsumer
  have hw : w < n + q := back q consumer hconsumer w hread
  have hqlt : q < C.size := by
    change q < C.gates.length
    by_contra hn
    rw [List.getElem?_eq_none_iff.2 (by omega)] at hconsumer
    cases hconsumer
  have hn := hfan consumer hcmem
  have hop : consumer.op = GateOp.and ∨ consumer.op = GateOp.or ∨ consumer.op = GateOp.not := by
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hn.1
  rcases Consumer.consumer_absorbs
      (fun x : Fin n → Bool => fun i => (C.wires (List.ofFn x)).getD i false)
      consumer v w (n + q) hvw hraw hread hop hn.2 (hnot consumer hcmem)
      (full_gate_value_index n C back q consumer hconsumer) himp with he | he
  · exact AliasPruning.minimal_no_alias_index n C hfan hmin q hqlt w hw he
  · exact AliasPruning.minimal_no_alias_index n C hfan hmin q hqlt v hv he

lemma minimal_first_and_consumer_not_and (n : ℕ) (C : Circuit)
    (g q : Gate) (pre post : List Gate)
    (hfan : FanInTwo C) (hsize : C.size ≤ 19)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin (n + 1) → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + 1 + j)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false))) →
      16 ≤ E.size)
    (hgs : C.gates = g :: (pre ++ q :: post)) (hg : g.op = GateOp.and)
    (hread : n ∈ g.inputs) (hqread : n + 1 ∈ q.inputs)
    (hraw : ∃ r ∈ pre ++ q :: post, n ∈ r.inputs) : q.op ≠ GateOp.and := by
  intro hq
  let F := fun x : Fin (n + 1) → Bool => fun i => (C.wires (List.ofFn x)).getD i false
  have hgindex : C.gates[0]? = some g := by simp [hgs]
  have hqindex : C.gates[pre.length + 1]? = some q := by simp [hgs]
  have hgval : ∀ x, F x (n + 1) = g.op.eval (g.inputs.map (F x)) := by
    simpa [F] using full_gate_value_index (n + 1) C back 0 g hgindex
  have hqval : ∀ x, F x (n + 2 + pre.length) = q.op.eval (q.inputs.map (F x)) := by
    simpa [F, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
      full_gate_value_index (n + 1) C back (pre.length + 1) q hqindex
  have hgimp := Consumer.and_value_implies_input F g n (n + 1) hg hread hgval
  have hqimp := Consumer.and_value_implies_input F q (n + 1) (n + 2 + pre.length) hq hqread hqval
  have hrawimp (x : Fin (n + 1) → Bool) (hx : F x (n + 2 + pre.length) = true) :
      F x n = true := hgimp x (hqimp x hx)
  have hqavoid : n ∉ q.inputs :=
    minimal_consumer_avoids_input (n + 1) C hfan hmin hnot back n 0 (pre.length + 1)
      g q (by omega) hgindex hqindex hg hread (by simpa using hqread)
  have hqout : C.output ≠ n + 2 + pre.length := by
    intro ho
    have hzero (y : Fin n → Bool) : C.eval (List.ofFn (Fin.snoc y false)) = false := by
      cases he : C.eval (List.ofFn (Fin.snoc y false)) with
      | false => rfl
      | true =>
        have hx : F (Fin.snoc y false) (n + 2 + pre.length) = true := by
          simpa [F, Circuit.eval, ho] using he
        have hfalse := hrawimp (Fin.snoc y false) hx
        change (C.wires (List.ofFn (Fin.snoc y false))).getD n false = true at hfalse
        rw [Wires.wires_input C _ n (by simp)] at hfalse
        have hz := getD_snoc_len (List.ofFn y) false false n (by simp)
        rw [ofFn_snoc, hz] at hfalse
        exact False.elim (Bool.false_ne_true hfalse)
    obtain ⟨y, y', hne⟩ := hnc
    exact hne ((hzero y).trans (hzero y').symm)
  have hsplit : C.gates = (g :: pre) ++ q :: post := by simpa using hgs
  obtain ⟨r, hr, hrr⟩ := LivePruning.minimal_live (n + 1) C hfan hmin (g :: pre) post q hsplit
    (by simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hqout)
  have hrr' : n + 2 + pre.length ∈ r.inputs := by
    have hsub : LivePruning.effective r ⊆ r.inputs := by
      simp only [LivePruning.effective]
      split
      · exact List.take_subset _ _
      · exact List.Subset.refl _
    apply hsub
    simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrr
  have hrmem : r ∈ C.gates := by simp only [hgs, List.mem_cons, List.mem_append]; exact Or.inr (Or.inr (Or.inr hr))
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hrmem
  have havoidraw : n ∉ r.inputs := minimal_consumer_avoids_implicate (n + 1) C hfan hmin hnot back
    n (n + 2 + pre.length) j r (by omega) (by omega) hj hrr' hrawimp
  have havoidfirst : n + 1 ∉ r.inputs := minimal_consumer_avoids_implicate (n + 1) C hfan hmin hnot back
    (n + 1) (n + 2 + pre.length) j r (by omega)
    (by have := back j r hj (n + 2 + pre.length) hrr'; omega) hj hrr' hqimp
  have hravoid : ∀ i ∈ ({n, n + 1} : Finset ℕ), i ∉ r.inputs := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl
    · exact havoidraw
    · exact havoidfirst
  obtain ⟨E, hE, hbound, heval⟩ := fix_false_first_and_and_consumer n C g q pre post hfan hnc
    (by rw [normalized_map_eq_self C.gates hnot, hgs]) hg hread hq hqread hqavoid hraw
    ⟨r, hr, hrr', hravoid⟩
  have hlow := hlower E hE heval
  omega

lemma minimal_live_fin (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size) :
    ∀ i : Fin C.gates.length, n + i.val ≠ C.output →
      ∃ j : Fin C.gates.length, n + i.val ∈ (C.gates.get j).inputs := by
  intro i hne
  have hpos : 0 < C.size := by have := i.isLt; change 0 < C.gates.length; omega
  have hout := LivePruning.minimal_output_last n C hfan hmin hpos
  have hi : i.val + 1 < C.size := by have := i.isLt; change i.val < C.size at this; omega
  obtain ⟨q, hq, g, hg, hr⟩ := LivePruning.minimal_live_index n C hfan hmin i.val hi
  have hqlt : q < C.gates.length := by
    by_contra hn
    rw [List.getElem?_eq_none_iff.2 (by omega)] at hg
    cases hg
  have hget : C.gates.get ⟨q, hqlt⟩ = g := by
    simpa [List.getElem?_eq_getElem hqlt] using hg
  refine ⟨⟨q, hqlt⟩, ?_⟩
  rw [hget]
  have hsub : LivePruning.effective g ⊆ g.inputs := by
    simp only [LivePruning.effective]
    split
    · exact List.take_subset _ _
    · exact List.Subset.refl _
  exact hsub hr

lemma singleton_inputs_of_read (ins : List ℕ) (k : ℕ) (hlen : ins.length ≤ 1)
    (hread : k ∈ ins) : ins = [k] := by
  rcases ins with _ | ⟨a, _ | ⟨b, tail⟩⟩
  · simp at hread
  · have he : k = a := by simpa using hread
    subst a
    rfl
  · simp at hlen

lemma minimal_first_and_consumer_not_not (n : ℕ) (C : Circuit)
    (g q : Gate) (pre post : List Gate)
    (hfan : FanInTwo C) (hsize : C.size ≤ 19)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin (n + 1) → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + 1 + j)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false))) →
      16 ≤ E.size)
    (hgs : C.gates = g :: (pre ++ q :: post)) (hg : g.op = GateOp.and)
    (hread : n ∈ g.inputs) (hqread : n + 1 ∈ q.inputs)
    (hraw : ∃ r ∈ pre ++ q :: post, n ∈ r.inputs) : q.op ≠ GateOp.not := by
  intro hq
  have hqlen : q.inputs.length ≤ 1 := hnot q (by simp [hgs]) hq
  have hqeq : q = ⟨GateOp.not, [n + 1]⟩ := by
    have hi := singleton_inputs_of_read q.inputs (n + 1) hqlen hqread
    cases q with
    | mk op inputs =>
      change op = GateOp.not at hq
      change inputs = [n + 1] at hi
      simp only [hq, hi]
  have hlen0 : 0 < C.gates.length := by simp [hgs]
  have hlenq : pre.length + 1 < C.gates.length := by simp [hgs]
  let p : Fin C.gates.length := ⟨0, hlen0⟩
  let z : Fin C.gates.length := ⟨pre.length + 1, hlenq⟩
  obtain ⟨r, hr, hrread⟩ := hraw
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hr
  have hrindex : C.gates[j + 1]? = some r := by simpa [hgs] using hj
  have hlenr : j + 1 < C.gates.length := by
    by_contra hn
    rw [List.getElem?_eq_none_iff.2 (by omega)] at hrindex
    cases hrindex
  let rindex : Fin C.gates.length := ⟨j + 1, hlenr⟩
  have hgetp : C.gates.get p = g := by simp [p, hgs]
  have hgetq : C.gates.get z = q := by simp [z, hgs]
  have hgetr : C.gates.get rindex = r := by
    simpa [rindex, List.getElem?_eq_getElem hlenr] using hrindex
  have hnmap : C.gates.map NandRestriction.normGate = C.gates := by
    change C.gates.map normGate = C.gates
    exact normalized_map_eq_self C.gates hnot
  have hbound := NandRestriction.nand_lower_bound n 16 C C.gates p z rindex hfan hnc
    hnmap back (minimal_live_fin (n + 1) C hfan hmin)
    (by rw [hgetp]; exact hg) (by rw [hgetp]; exact hread)
    (by rw [hgetq, hqeq]; rfl) (by rw [hgetr]; exact hrread)
    (by intro he; have he' := congrArg Fin.val he; simp [p, rindex] at he') hlower
  omega

lemma minimal_first_and_consumer_or (n : ℕ) (C : Circuit)
    (g q : Gate) (pre post : List Gate)
    (hfan : FanInTwo C) (hsize : C.size ≤ 19)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin (n + 1) → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + 1 + j)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false))) →
      16 ≤ E.size)
    (hgs : C.gates = g :: (pre ++ q :: post)) (hg : g.op = GateOp.and)
    (hread : n ∈ g.inputs) (hqread : n + 1 ∈ q.inputs)
    (hraw : ∃ r ∈ pre ++ q :: post, n ∈ r.inputs) : q.op = GateOp.or := by
  have hnand := minimal_first_and_consumer_not_and n C g q pre post hfan hsize hmin hnot
    back hnc hlower hgs hg hread hqread hraw
  have hnnot := minimal_first_and_consumer_not_not n C g q pre post hfan hsize hmin hnot
    back hnc hlower hgs hg hread hqread hraw
  have hop := (hfan q (by simp [hgs])).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with ha | ho | hn
  · exact False.elim (hnand ha)
  · exact ho
  · exact False.elim (hnnot hn)

lemma petersen_first_and_unique_or_consumer (C : Circuit) (b : Fin 10) (post : List Gate)
    (hb : (9 : Fin 10) ≠ b) (hfan : FanInTwo C) (hsize : C.size ≤ 19)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < 10 + j)
    (hgs : C.gates = ⟨GateOp.and, [9, b.val]⟩ :: post)
    (hev : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x)
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin 9 → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false))) →
      16 ≤ E.size) :
    readerCount 10 post = 1 ∧ ∀ q ∈ post, 10 ∈ q.inputs → q.op = GateOp.or := by
  refine ⟨petersen_first_and_unique_consumer C b post hb hfan hsize hmin hnot back hgs hev hlower, ?_⟩
  intro q hq hqread
  have hC : C = ⟨⟨GateOp.and, [9, b.val]⟩ :: post, C.output⟩ := by cases C; simp_all
  have hev' : ∀ x : Fin 10 → Bool,
      (Circuit.mk (⟨GateOp.and, [9, b.val]⟩ :: post) C.output).eval (List.ofFn x) = petersen x := by
    intro x
    rw [← hC]
    exact hev x
  obtain ⟨r, hr, hrread⟩ := first_and_input_reread 9 b hb post C.output hev'
  have hraw : ∃ r ∈ post, 9 ∈ r.inputs := by
    refine ⟨r, hr, ?_⟩
    have hsub : effectiveInputs r ⊆ r.inputs := by
      simp only [effectiveInputs]
      split
      · exact List.take_subset _ _
      · exact List.Subset.refl _
    exact hsub hrread
  have hnc : ∃ y y' : Fin 9 → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)) := by
    refine ⟨(fun _ => false), (fun i => decide (i = 0 ∨ i = 1)), ?_⟩
    rw [hev, hev]
    decide +kernel
  obtain ⟨i, hi⟩ := List.mem_iff_getElem?.mp hq
  have hilt : i < post.length := by
    by_contra hn
    rw [List.getElem?_eq_none_iff.2 (by omega)] at hi
    cases hi
  have hget : post[i] = q := by simpa [List.getElem?_eq_getElem hilt] using hi
  have hpost : post = post.take i ++ q :: post.drop (i + 1) := by
    rw [← hget, List.getElem_cons_drop hilt, List.take_append_drop]
  apply minimal_first_and_consumer_or 9 C _ q (post.take i) (post.drop (i + 1))
    hfan hsize hmin hnot back hnc hlower (by rw [hgs, ← hpost]) rfl (by simp) hqread
  simpa only [← hpost] using hraw


end FirstAndClassification


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2373_aux.Restriction

set_option maxHeartbeats 2000000 in
lemma petersen_edge_support_implies (a b : Fin 10)
    (hab : petersen (fun i => decide (i = a ∨ i = b)) = true)
    (x : Fin 10 → Bool) (ha : x a = true) (hb : x b = true) :
    petersen x = true := by
  fin_cases a <;> fin_cases b <;> simp_all [petersen]

lemma petersen_first_and_edge_positive (a b : Fin 10) (post : List Gate) (out : ℕ)
    (hab : petersen (fun i => decide (i = a ∨ i = b)) = true)
    (hev : ∀ x : Fin 10 → Bool,
      ({gates := ⟨.and, [a.val, b.val]⟩ :: post, output := out} : Circuit).eval (List.ofFn x) =
        petersen x) :
    ∀ x : Fin 10 → Bool,
      (wiresFrom [⟨.and, [a.val, b.val]⟩] (List.ofFn x)).getD 10 false = true →
      ({gates := ⟨.and, [a.val, b.val]⟩ :: post, output := out} : Circuit).eval (List.ofFn x) = true := by
  intro x hx
  have hp : (x a && x b) = true := by
    simp only [wiresFrom, List.foldl_cons, List.foldl_nil, List.map_cons, List.map_nil,
      GateOp.eval, List.all_cons, List.all_nil, id_eq, Bool.and_true, getD_ofFn_val] at hx
    rw [List.getD_append_right _ _ _ _ (by simp)] at hx
    simpa using hx
  obtain ⟨ha, hb⟩ := Bool.and_eq_true_iff.mp hp
  rw [hev]
  exact petersen_edge_support_implies a b hab x ha hb

lemma minimum_petersen_first_and_edge_readers_le_one
    (a b : Fin 10) (post : List Gate) (out : ℕ)
    (hab : petersen (fun i => decide (i = a ∨ i = b)) = true)
    (hfanin : FanInTwo
      ({gates := ⟨.and, [a.val, b.val]⟩ :: post, output := out} : Circuit))
    (hev : ∀ x : Fin 10 → Bool,
      ({gates := ⟨.and, [a.val, b.val]⟩ :: post, output := out} : Circuit).eval (List.ofFn x) =
        petersen x)
    (hmin : ∀ E : Circuit, FanInTwo E →
      (∀ x : Fin 10 → Bool, E.eval (List.ofFn x) = petersen x) →
      ({gates := ⟨.and, [a.val, b.val]⟩ :: post, output := out} : Circuit).size ≤ E.size) :
    readerCount 10 (post.map normGate) ≤ 1 := by
  apply minimum_positive_wire_readers_le_one 10 [⟨.and, [a.val, b.val]⟩] post out 10
    (by simp) hfanin (petersen_first_and_edge_positive a b post out hab hev)
  intro E hE he
  exact hmin E hE (fun x => (he x).trans (hev x))



namespace Restriction


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma cofactor_effective_mem_inputs (g : Gate) (i : ℕ)
    (hi : i ∈ PEqualNP.Outside.L_meta_2373_aux.LivePruning.effective g) : i ∈ g.inputs := by
  rcases g with ⟨op, inputs⟩
  cases op <;> simp only [PEqualNP.Outside.L_meta_2373_aux.LivePruning.effective] at hi ⊢
  · exact hi
  · exact hi
  · exact List.mem_of_mem_take hi
  · exact hi
  · exact hi

lemma cofactor_constant_has_later_effective_consumer
    (n : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate)
    (hfan : FanInTwo C)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin (n + 1) → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) →
        C.size ≤ D.size)
    (hsplit : C.gates = pre ++ g :: post)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hconst : ∀ y y' : Fin n → Bool,
      (C.wires (List.ofFn (Fin.snoc y false))).getD (n + 1 + pre.length) false =
        (C.wires (List.ofFn (Fin.snoc y' false))).getD (n + 1 + pre.length) false) :
    ∃ r ∈ post, n + 1 + pre.length ∈
      PEqualNP.Outside.L_meta_2373_aux.LivePruning.effective r := by
  have hout : C.output ≠ n + 1 + pre.length := by
    intro he
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    unfold Circuit.eval
    rw [he]
    exact hconst y y'
  exact PEqualNP.Outside.L_meta_2373_aux.LivePruning.minimal_live
    (n + 1) C hfan hmin pre post g hsplit hout

lemma cofactor_constant_has_later_consumer
    (n : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate)
    (hfan : FanInTwo C)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin (n + 1) → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) →
        C.size ≤ D.size)
    (hsplit : C.gates = pre ++ g :: post)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hconst : ∀ y y' : Fin n → Bool,
      (C.wires (List.ofFn (Fin.snoc y false))).getD (n + 1 + pre.length) false =
        (C.wires (List.ofFn (Fin.snoc y' false))).getD (n + 1 + pre.length) false) :
    ∃ r ∈ post, n + 1 + pre.length ∈ r.inputs := by
  obtain ⟨r, hr, hread⟩ := cofactor_constant_has_later_effective_consumer
    n C pre post g hfan hmin hsplit hnc hconst
  exact ⟨r, hr, cofactor_effective_mem_inputs r _ hread⟩

lemma false_raw_wire (n : ℕ) (C : Circuit) (y : Fin n → Bool) :
    (C.wires (List.ofFn (Fin.snoc y false))).getD n false = false := by
  change (wiresFrom C.gates (List.ofFn (Fin.snoc y false))).getD n false = false
  rw [getD_wiresFrom _ _ _ (by simp), ofFn_snoc]
  exact getD_snoc_len _ _ _ _ (by simp)

lemma gate_constant_on_cofactor (n : ℕ) (C : Circuit) (g : Gate) (root : ℕ)
    (hvalue : ∀ y : Fin n → Bool,
      (C.wires (List.ofFn (Fin.snoc y false))).getD root false =
        g.op.eval (g.inputs.map fun i =>
          (C.wires (List.ofFn (Fin.snoc y false))).getD i false))
    (hinputs : ∀ i ∈ g.inputs, ∀ y y' : Fin n → Bool,
      (C.wires (List.ofFn (Fin.snoc y false))).getD i false =
        (C.wires (List.ofFn (Fin.snoc y' false))).getD i false) :
    ∀ y y' : Fin n → Bool,
      (C.wires (List.ofFn (Fin.snoc y false))).getD root false =
        (C.wires (List.ofFn (Fin.snoc y' false))).getD root false := by
  intro y y'
  rw [hvalue y, hvalue y']
  congr 1
  apply List.map_congr_left
  intro i hi
  exact hinputs i hi y y'


end Restriction

namespace FirstAndClassification


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Restriction

lemma raw_false_cofactor_wire (n : ℕ) (C : Circuit) (y : Fin n → Bool) :
    (C.wires (List.ofFn (Fin.snoc y false))).getD n false = false := by
  rw [Wires.wires_input C _ n (by simp), ofFn_snoc]
  exact getD_snoc_len _ _ _ _ (by simp)

lemma raw_and_not_reader_constant (n : ℕ) (C : Circuit) (q : Gate) (j : ℕ)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + 1 + j)
    (hqindex : C.gates[j]? = some q) (hread : n ∈ q.inputs)
    (hop : q.op = GateOp.and ∨ q.op = GateOp.not) :
    ∃ c, ∀ y : Fin n → Bool,
      (C.wires (List.ofFn (Fin.snoc y false))).getD (n + 1 + j) false = c := by
  let F := fun x : Fin (n + 1) → Bool => fun i => (C.wires (List.ofFn x)).getD i false
  have hvalue : ∀ x, F x (n + 1 + j) = q.op.eval (q.inputs.map (F x)) :=
    full_gate_value_index (n + 1) C back j q hqindex
  rcases hop with hop | hop
  · refine ⟨false, ?_⟩
    intro y
    have himp := Consumer.and_value_implies_input F q n (n + 1 + j) hop hread hvalue
    cases he : (C.wires (List.ofFn (Fin.snoc y false))).getD (n + 1 + j) false with
    | false => rfl
    | true =>
      have h := himp (Fin.snoc y false) he
      change (C.wires (List.ofFn (Fin.snoc y false))).getD n false = true at h
      rw [raw_false_cofactor_wire] at h
      exact False.elim (Bool.false_ne_true h)
  · refine ⟨true, ?_⟩
    have hinputs : q.inputs = [n] := singleton_inputs_of_read q.inputs n
      (hnot q (List.mem_of_getElem? hqindex) hop) hread
    intro y
    change F (Fin.snoc y false) (n + 1 + j) = true
    rw [hvalue, hop, hinputs]
    simp only [List.map_cons, List.map_nil, GateOp.eval]
    change !(C.wires (List.ofFn (Fin.snoc y false))).getD n false = true
    rw [raw_false_cofactor_wire]
    rfl

lemma minimal_first_and_other_raw_reader_not_and_not (n : ℕ) (C : Circuit)
    (g q : Gate) (pre post : List Gate)
    (hfan : FanInTwo C) (hsize : C.size ≤ 19)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin (n + 1) → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + 1 + j)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false))) →
      16 ≤ E.size)
    (hgs : C.gates = g :: (pre ++ q :: post)) (hg : g.op = GateOp.and)
    (hread : n ∈ g.inputs) (hqraw : n ∈ q.inputs) :
    q.op ≠ GateOp.and ∧ q.op ≠ GateOp.not := by
  suffices hbad : ¬ (q.op = GateOp.and ∨ q.op = GateOp.not) by tauto
  intro hop
  have hgindex : C.gates[0]? = some g := by simp [hgs]
  have hqindex : C.gates[pre.length + 1]? = some q := by simp [hgs]
  have hqmem : q ∈ C.gates := List.mem_of_getElem? hqindex
  obtain ⟨cg, hcg0⟩ := raw_and_not_reader_constant n C g 0 hnot back hgindex hread (Or.inl hg)
  have hcg : ∀ y : Fin n → Bool,
      (C.wires (List.ofFn (Fin.snoc y false))).getD (n + 1) false = cg := by
    simpa using hcg0
  obtain ⟨cq, hcq0⟩ := raw_and_not_reader_constant n C q (pre.length + 1) hnot back hqindex hqraw hop
  have hcq : ∀ y : Fin n → Bool,
      (C.wires (List.ofFn (Fin.snoc y false))).getD (n + 2 + pre.length) false = cq := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hcq0
  have hqavoid : n + 1 ∉ q.inputs := by
    intro hqfirst
    exact minimal_consumer_avoids_input (n + 1) C hfan hmin hnot back
      n 0 (pre.length + 1) g q (by omega) hgindex hqindex hg hread
      (by simpa using hqfirst) hqraw
  obtain ⟨u, hu, huread⟩ := cofactor_constant_has_later_consumer n C []
    (pre ++ q :: post) g hfan hmin (by simpa using hgs) hnc
    (by intro y y'; simpa using (hcg y).trans (hcg y').symm)
  have hfirstconsumer : ∃ r ∈ pre ++ post, n + 1 ∈ r.inputs := by
    have hur : n + 1 ∈ u.inputs := by simpa using huread
    refine ⟨u, ?_, hur⟩
    rcases List.mem_append.mp hu with hu | hu
    · exact List.mem_append_left _ hu
    · rcases List.mem_cons.mp hu with hu | hu
      · subst u
        exact False.elim (hqavoid hur)
      · exact List.mem_append_right _ hu
  obtain ⟨v, hv, hvread⟩ := cofactor_constant_has_later_consumer n C (g :: pre) post q
    hfan hmin (by simpa using hgs) hnc
    (by intro y y'; simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using (hcq y).trans (hcq y').symm)
  have hsecondconsumer : ∃ r ∈ post, n + 2 + pre.length ∈ r.inputs := by
    exact ⟨v, hv, by simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hvread⟩
  have hroot : (q.op = GateOp.and ∧ n ∈ q.inputs) ∨
      ∀ j ∈ q.inputs, j ∈ ({n, n + 1} : Finset ℕ) := by
    rcases hop with hop | hop
    · exact Or.inl ⟨hop, hqraw⟩
    · exact not_raw_reader_is_root n q ⟨hfan q hqmem, hnot q hqmem⟩ hop hqraw
  rcases constant_roots_split_reader_dichotomy n (n + 1) (n + 2 + pre.length)
    pre post hfirstconsumer hsecondconsumer with hcount | hshared
  · have hset : ({n, n + 1, n + 2 + pre.length} : Finset ℕ) =
        insert (n + 2 + pre.length) {n, n + 1} := by
      ext j
      simp only [Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [hset] at hcount
    obtain ⟨E, hE, hbound, heval⟩ := fix_false_first_and_two_roots_distinct_consumers
      n C g q pre post hfan hnc
      (by rw [normalized_map_eq_self C.gates hnot, hgs]) hg hread hroot hcount
    have hlow := hlower E hE heval
    omega
  · obtain ⟨r, hr, hrfirst, hrsecond⟩ := hshared
    obtain ⟨mid, tail, hpost⟩ := List.mem_iff_append.mp hr
    have hsplit : C.gates = (g :: (pre ++ q :: mid)) ++ r :: tail := by
      simp [hgs, hpost, List.append_assoc]
    let beforeR := g :: (pre ++ q :: mid)
    have hrindex : C.gates[beforeR.length]? = some r := by
      rw [hsplit]
      change (beforeR ++ r :: tail)[beforeR.length]? = some r
      simp
    have hrmem : r ∈ C.gates := List.mem_of_getElem? hrindex
    have hrinputs := shared_root_consumer_inputs n pre r (hfan r hrmem).2 hrfirst hrsecond
    have hrvalue : ∀ y : Fin n → Bool,
        (C.wires (List.ofFn (Fin.snoc y false))).getD (n + 1 + beforeR.length) false =
          r.op.eval (r.inputs.map fun i =>
            (C.wires (List.ofFn (Fin.snoc y false))).getD i false) := by
      intro y
      exact full_gate_value (n + 1) C beforeR tail r hsplit
        (back beforeR.length r hrindex) (Fin.snoc y false)
    have hrconst := gate_constant_on_cofactor n C r (n + 1 + beforeR.length) hrvalue
      (by
        intro i hi y y'
        have hiK := hrinputs i hi
        simp only [Finset.mem_insert, Finset.mem_singleton] at hiK
        rcases hiK with rfl | rfl | rfl
        · exact (hcq y).trans (hcq y').symm
        · rw [raw_false_cofactor_wire, raw_false_cofactor_wire]
        · exact (hcg y).trans (hcg y').symm)
    obtain ⟨s, hs, hsread⟩ := cofactor_constant_has_later_consumer n C beforeR tail r
      hfan hmin hsplit hnc hrconst
    have hsread' : n + 3 + pre.length + mid.length ∈ s.inputs := by
      simpa [beforeR, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hsread
    obtain ⟨E, hE, hbound, heval⟩ := fix_false_first_and_two_roots_shared_consumer
      n C g q r pre mid tail hfan hnc
      (by rw [normalized_map_eq_self C.gates hnot, hgs, hpost]) hg hread hroot hrinputs
      ⟨s, hs, hsread'⟩
    have hlow := hlower E hE heval
    omega

lemma minimal_first_and_other_raw_reader_or (n : ℕ) (C : Circuit)
    (g q : Gate) (pre post : List Gate)
    (hfan : FanInTwo C) (hsize : C.size ≤ 19)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin (n + 1) → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + 1 + j)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false))) →
      16 ≤ E.size)
    (hgs : C.gates = g :: (pre ++ q :: post)) (hg : g.op = GateOp.and)
    (hread : n ∈ g.inputs) (hqraw : n ∈ q.inputs) : q.op = GateOp.or := by
  have hn := minimal_first_and_other_raw_reader_not_and_not n C g q pre post
    hfan hsize hmin hnot back hnc hlower hgs hg hread hqraw
  have hqmem : q ∈ C.gates := by simp [hgs]
  have hop := (hfan q hqmem).1
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  tauto

lemma minimal_first_and_unique_other_raw_reader (n : ℕ) (C : Circuit)
    (g : Gate) (post : List Gate)
    (hfan : FanInTwo C) (hsize : C.size ≤ 19)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin (n + 1) → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + 1 + j)
    (hnc : ∃ y y' : Fin n → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)))
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin n → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false))) →
      16 ≤ E.size)
    (hgs : C.gates = g :: post) (hg : g.op = GateOp.and)
    (hread : n ∈ g.inputs) (hraw : ∃ q ∈ post, n ∈ q.inputs) :
    readerCount n post = 1 := by
  have hgindex : C.gates[0]? = some g := by simp [hgs]
  obtain ⟨c, hc⟩ := raw_and_not_reader_constant n C g 0 hnot back hgindex hread (Or.inl hg)
  obtain ⟨q, hq, hqread⟩ := cofactor_constant_has_later_consumer n C [] post g
    hfan hmin (by simpa using hgs) hnc
    (by intro y y'; simpa using (hc y).trans (hc y').symm)
  obtain ⟨j, hj⟩ := List.mem_iff_getElem?.mp hq
  have hqindex : C.gates[j + 1]? = some q := by simpa [hgs] using hj
  have havoid := minimal_consumer_avoids_input (n + 1) C hfan hmin hnot back
    n 0 (j + 1) g q (by omega) hgindex hqindex hg hread (by simpa using hqread)
  have hnorm : C.gates.map normGate = g :: post := by
    rw [normalized_map_eq_self C.gates hnot, hgs]
  have hb := and_readers_le_of_cofactor_lower n 16 19 C [] post g hfan hsize hnc hlower
    (by simpa using hnorm) hg hread ⟨q, hq, hqread, havoid⟩
  rw [hnorm] at hb
  simp only [readerCount, ite_eq_left hread] at hb
  have hpos := (readerCount_pos_iff n post).mpr hraw
  omega

lemma petersen_first_and_sparse_readers (C : Circuit) (b : Fin 10) (post : List Gate)
    (hb : (9 : Fin 10) ≠ b) (hfan : FanInTwo C) (hsize : C.size ≤ 19)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < 10 + j)
    (hgs : C.gates = ⟨GateOp.and, [9, b.val]⟩ :: post)
    (hev : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x)
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin 9 → Bool, E.eval (List.ofFn y) = C.eval (List.ofFn (Fin.snoc y false))) →
      16 ≤ E.size) :
    readerCount 9 post = 1 ∧ (∀ q ∈ post, 9 ∈ q.inputs → q.op = GateOp.or) ∧
      readerCount 10 post = 1 ∧ (∀ q ∈ post, 10 ∈ q.inputs → q.op = GateOp.or) := by
  have hC : C = ⟨⟨GateOp.and, [9, b.val]⟩ :: post, C.output⟩ := by cases C; simp_all
  have hev' : ∀ x : Fin 10 → Bool,
      (Circuit.mk (⟨GateOp.and, [9, b.val]⟩ :: post) C.output).eval (List.ofFn x) = petersen x := by
    intro x
    rw [← hC]
    exact hev x
  obtain ⟨r, hr, hrread⟩ := first_and_input_reread 9 b hb post C.output hev'
  have hraw : ∃ r ∈ post, 9 ∈ r.inputs := by
    refine ⟨r, hr, ?_⟩
    have hsub : effectiveInputs r ⊆ r.inputs := by
      simp only [effectiveInputs]
      split
      · exact List.take_subset _ _
      · exact List.Subset.refl _
    exact hsub hrread
  have hnc : ∃ y y' : Fin 9 → Bool,
      C.eval (List.ofFn (Fin.snoc y false)) ≠ C.eval (List.ofFn (Fin.snoc y' false)) := by
    refine ⟨(fun _ => false), (fun i => decide (i = 0 ∨ i = 1)), ?_⟩
    rw [hev, hev]
    decide +kernel
  refine ⟨minimal_first_and_unique_other_raw_reader 9 C _ post hfan hsize hmin hnot back
    hnc hlower hgs rfl (by simp) hraw, ?_,
    petersen_first_and_unique_or_consumer C b post hb hfan hsize hmin hnot back hgs hev hlower⟩
  intro q hq hqread
  obtain ⟨pre, tail, hpost⟩ := List.mem_iff_append.mp hq
  exact minimal_first_and_other_raw_reader_or 9 C _ q pre tail hfan hsize hmin hnot back
    hnc hlower (by rw [hgs, hpost]) rfl (by simp) hqread


end FirstAndClassification

namespace Transport


def table : Fin 10 → Fin 10 → Fin 10 := ![
  ![7, 9, 6, 8, 5, 2, 4, 1, 3, 0],
  ![8, 5, 7, 9, 6, 3, 0, 2, 4, 1],
  ![9, 6, 8, 5, 7, 4, 1, 3, 0, 2],
  ![5, 7, 9, 6, 8, 0, 2, 4, 1, 3],
  ![6, 8, 5, 7, 9, 1, 3, 0, 2, 4],
  ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
  ![2, 3, 4, 0, 1, 7, 8, 9, 5, 6],
  ![3, 4, 0, 1, 2, 8, 9, 5, 6, 7],
  ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]

def invTable : Fin 10 → Fin 10 → Fin 10 := ![
  ![9, 7, 5, 8, 6, 4, 2, 0, 3, 1],
  ![6, 9, 7, 5, 8, 1, 4, 2, 0, 3],
  ![8, 6, 9, 7, 5, 3, 1, 4, 2, 0],
  ![5, 8, 6, 9, 7, 0, 3, 1, 4, 2],
  ![7, 5, 8, 6, 9, 2, 0, 3, 1, 4],
  ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
  ![3, 4, 0, 1, 2, 8, 9, 5, 6, 7],
  ![2, 3, 4, 0, 1, 7, 8, 9, 5, 6],
  ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]

lemma inverse_left : ∀ v i, invTable v (table v i) = i := by decide +kernel
lemma inverse_right : ∀ v i, table v (invTable v i) = i := by decide +kernel

def relabel (v : Fin 10) : Equiv.Perm (Fin 10) where
  toFun := table v
  invFun := invTable v
  left_inv := inverse_left v
  right_inv := inverse_right v

lemma relabel_last : ∀ v, relabel v 9 = v := by decide +kernel

def edge (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

lemma edge_relabel (v : Fin 10) (x : Fin 10 → Bool) :
    edge (x ∘ relabel v) = edge x := by
  fin_cases v <;> simp [edge, relabel, table, Bool.and_comm] <;> ac_rfl

lemma edge_relabel_symm (v : Fin 10) (x : Fin 10 → Bool) :
    edge (x ∘ (relabel v).symm) = edge x := by
  have h := edge_relabel v (x ∘ (relabel v).symm)
  have he : (x ∘ (relabel v).symm) ∘ relabel v = x := by
    funext i
    simp
  rw [he] at h
  exact h.symm

lemma relabel_symm_vertex (v : Fin 10) : (relabel v).symm v = 9 := by
  apply (relabel v).injective
  simp [relabel_last]

def cofactorInput (v : Fin 10) (b : Bool) (y : Fin 9 → Bool) : Fin 10 → Bool :=
  (Fin.lastCases b y) ∘ (relabel v).symm

lemma cofactorInput_at_vertex (v : Fin 10) (b : Bool) (y : Fin 9 → Bool) :
    cofactorInput v b y v = b := by
  change Fin.lastCases b y ((relabel v).symm v) = b
  rw [relabel_symm_vertex]
  exact Fin.lastCases_last

lemma cofactor_false (v : Fin 10) (y : Fin 9 → Bool) :
    edge (cofactorInput v false y) =
      ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) ||
        (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) ||
        (y 3 && y 8) || (y 5 && y 7) || (y 6 && y 8) || (y 8 && y 5)) := by
  rw [cofactorInput, edge_relabel_symm]
  change ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) ||
        (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) ||
        (y 3 && y 8) || (y 4 && false) || (y 5 && y 7) || (y 7 && false) ||
        (false && y 6) || (y 6 && y 8) || (y 8 && y 5)) = _
  simp only [Bool.and_false, Bool.false_and, Bool.or_false]

lemma cofactor_true (v : Fin 10) (y : Fin 9 → Bool) :
    edge (cofactorInput v true y) =
      (y 4 || y 6 || y 7 || (y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) ||
        (y 0 && y 5) || (y 3 && y 8) || (y 8 && y 5)) := by
  rw [cofactorInput, edge_relabel_symm]
  change ((y 0 && y 1) || (y 1 && y 2) || (y 2 && y 3) || (y 3 && y 4) ||
        (y 4 && y 0) || (y 0 && y 5) || (y 1 && y 6) || (y 2 && y 7) ||
        (y 3 && y 8) || (y 4 && true) || (y 5 && y 7) || (y 7 && true) ||
        (true && y 6) || (y 6 && y 8) || (y 8 && y 5)) = _
  cases h4 : y 4 <;> cases h6 : y 6 <;> cases h7 : y 7 <;> simp

lemma cofactorInput_surjective (v : Fin 10) (b : Bool) (x : Fin 10 → Bool)
    (hx : x v = b) : ∃ y : Fin 9 → Bool, cofactorInput v b y = x := by
  let y : Fin 9 → Bool := fun i => x (relabel v i.castSucc)
  have he : (Fin.lastCases b y : Fin 10 → Bool) = x ∘ relabel v := by
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change Fin.lastCases b y (Fin.last 9) = x (relabel v 9)
      rw [Fin.lastCases_last, relabel_last]
      exact hx.symm
    · rw [Fin.lastCases_castSucc]
      rfl
  refine ⟨y, ?_⟩
  funext i
  simp only [cofactorInput, he, Function.comp_apply, Equiv.apply_symm_apply]

lemma cofactor_nonconstant (v : Fin 10) (b : Bool) :
    ∃ x y : Fin 10 → Bool,
      x v = b ∧ y v = b ∧ edge x = false ∧ edge y = true := by
  refine ⟨cofactorInput v b (fun _ => false), cofactorInput v b (fun _ => true),
    cofactorInput_at_vertex v b _, cofactorInput_at_vertex v b _, ?_, ?_⟩ <;>
    cases b <;> simp [cofactor_false, cofactor_true]


end Transport

namespace FirstAndClassification


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Restriction

lemma rename_wire_lt {n : ℕ} (s : Equiv.Perm (Fin n)) {i m : ℕ}
    (hn : n ≤ m) (hi : i < m) : InputRename.wire s i < m := by
  by_cases hraw : i < n
  · have hh := (s ⟨i, hraw⟩).isLt
    simp only [InputRename.wire, dite_eq_left hraw]
    omega
  · rw [InputRename.wire_ge s (by omega)]
    exact hi

lemma rename_wire_eq_internal {n : ℕ} (s : Equiv.Perm (Fin n)) (i k : ℕ) (hi : n ≤ i) :
    InputRename.wire s k = i ↔ k = i := by
  constructor
  · intro he
    by_contra hn
    exact InputRename.wire_ne_ge s hi hn he
  · rintro rfl
    exact InputRename.wire_ge s hi

lemma readerCount_map_internal {n : ℕ} (s : Equiv.Perm (Fin n)) (i : ℕ) (hi : n ≤ i)
    (gs : List Gate) : readerCount i (gs.map (InputRename.gate s)) = readerCount i gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    have hm : i ∈ (InputRename.gate s g).inputs ↔ i ∈ g.inputs := by
      change i ∈ g.inputs.map (InputRename.wire s) ↔ _
      simp only [List.mem_map, rename_wire_eq_internal s i _ hi]
      constructor
      · rintro ⟨k, hk, he⟩
        simpa only [he] using hk
      · intro hh
        exact ⟨i, hh, rfl⟩
    simp only [List.map_cons, readerCount, hm, ih]

lemma rename_normal {n : ℕ} (s : Equiv.Perm (Fin n)) (C : Circuit)
    (hn : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1) :
    ∀ g ∈ (InputRename.circuit s C).gates, g.op = GateOp.not → g.inputs.length ≤ 1 := by
  intro g hg
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
  simpa only [InputRename.gate, List.length_map] using hn q hq

lemma rename_back {n : ℕ} (s : Equiv.Perm (Fin n)) (C : Circuit)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j) :
    ∀ j g, (InputRename.circuit s C).gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j := by
  intro j g hj
  simp only [InputRename.circuit, List.getElem?_map] at hj
  cases hlookup : C.gates[j]? with
  | none => simp [hlookup] at hj
  | some q =>
    have he : InputRename.gate s q = g := by simpa [hlookup] using hj
    subst g
    intro i hi
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hi
    exact rename_wire_lt s (by omega) (back j q hlookup k hk)

lemma rename_minimal {n : ℕ} (s : Equiv.Perm (Fin n)) (C : Circuit)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size) :
    ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = (InputRename.circuit s C).eval (List.ofFn x)) →
      (InputRename.circuit s C).size ≤ D.size := by
  intro D hD heval
  have hcomp : ∀ x : Fin n → Bool,
      (InputRename.circuit s.symm D).eval (List.ofFn x) = C.eval (List.ofFn x) := by
    intro x
    rw [InputRename.eval_relabel, heval, InputRename.eval_relabel]
    simp only [Function.comp_def, Equiv.symm_apply_apply]
  have hh := hmin (InputRename.circuit s.symm D) (InputRename.fanInTwo s.symm D hD) hcomp
  simpa only [InputRename.size] using hh

lemma petersen_first_and_unique_or_consumer_any (C : Circuit) (a b : Fin 10) (post : List Gate)
    (hab : a ≠ b) (hfan : FanInTwo C) (hsize : C.size ≤ 19)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < 10 + j)
    (hgs : C.gates = ⟨GateOp.and, [a.val, b.val]⟩ :: post)
    (hev : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x)
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin 9 → Bool, E.eval (List.ofFn y) = petersen (Fin.snoc y false)) →
      16 ≤ E.size) :
    readerCount 10 post = 1 ∧ ∀ q ∈ post, 10 ∈ q.inputs → q.op = GateOp.or := by
  let s := (Transport.relabel a).symm
  let D := InputRename.circuit s C
  have hsa : s a = 9 := Transport.relabel_symm_vertex a
  have hsb : (9 : Fin 10) ≠ s b := by
    intro he
    apply hab
    apply s.injective
    exact hsa.trans he
  have hDfan : FanInTwo D := InputRename.fanInTwo s C hfan
  have hDsize : D.size ≤ 19 := by simpa only [D, InputRename.size] using hsize
  have hDmin := rename_minimal s C hmin
  have hDnormal := rename_normal s C hnot
  have hDback := rename_back s C back
  have hDgs : D.gates = ⟨GateOp.and, [9, (s b).val]⟩ :: post.map (InputRename.gate s) := by
    change C.gates.map (InputRename.gate s) = _
    rw [hgs, List.map_cons]
    simp only [InputRename.gate, List.map_cons, List.map_nil, InputRename.wire,
      dite_eq_left a.isLt, dite_eq_left b.isLt, hsa]
    rfl
  have hDev : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = petersen x := by
    intro x
    change (InputRename.circuit s C).eval (List.ofFn x) = _
    rw [InputRename.eval_relabel, hev]
    exact Transport.edge_relabel_symm a x
  obtain ⟨hcount, hreader⟩ := petersen_first_and_unique_or_consumer D (s b)
    (post.map (InputRename.gate s)) hsb hDfan hDsize hDmin hDnormal hDback hDgs hDev
    (by
      intro E hE he
      apply hlower E hE
      intro y
      rw [he, hDev])
  refine ⟨?_, ?_⟩
  · simpa only [readerCount_map_internal s 10 (by decide)] using hcount
  · intro q hq hqread
    have hmem : InputRename.gate s q ∈ post.map (InputRename.gate s) := List.mem_map_of_mem hq
    have hread : 10 ∈ (InputRename.gate s q).inputs := by
      apply List.mem_map.2
      exact ⟨10, hqread, InputRename.wire_ge s (by decide)⟩
    exact hreader (InputRename.gate s q) hmem hread


end FirstAndClassification



open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2373_aux.Restriction

lemma positive_wire_lift_with_budget (n : ℕ) (pre post : List Gate) (out h q : ℕ)
    (hh : h < n + pre.length)
    (hfanin : FanInTwo ({gates := pre ++ post, output := out} : Circuit))
    (hbelow : ∀ x : Fin n → Bool,
      (wiresFrom pre (List.ofFn x)).getD h false = true →
        ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) = true)
    (hbudget : (elim n (post.map normGate)
      (positiveInitStats (n + pre.length) h, pre)).2.length + q ≤ pre.length + post.length) :
    ∃ E : Circuit, FanInTwo E ∧
      E.size + q ≤
        ({gates := pre ++ post, output := out} : Circuit).size + 1 ∧
      ∀ x : Fin n → Bool, E.eval (List.ofFn x) =
        ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) := by
  have hpre : ∀ g ∈ pre, Ok g := by
    intro g hg
    exact hfanin g (List.mem_append_left _ hg)
  have hpost : ∀ g ∈ post.map normGate, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
    exact normGate_nok g0 (hfanin g0 (List.mem_append_right _ hg0))
  set acc := elim n (post.map normGate) (positiveInitStats (n + pre.length) h, pre) with hacc
  have hcount := hbudget
  have hok : ∀ g ∈ acc.2, Ok g := by
    rw [hacc]
    exact elim_ok n (post.map normGate) _ hpre
  obtain ⟨tail, htail⟩ := positive_elim_prefix n (post.map normGate)
    (positiveInitStats (n + pre.length) h, pre)
  change (elim n (post.map normGate) (positiveInitStats (n + pre.length) h, pre)).2 =
    pre ++ tail at htail
  rw [← hacc] at htail
  have hpreserve (x : Fin n → Bool) :
      (wiresFrom acc.2 (List.ofFn x)).getD h false =
        (wiresFrom pre (List.ofFn x)).getD h false := by
    rw [htail, wiresFrom_append]
    exact getD_wiresFrom tail _ h (by simpa [length_wiresFrom] using hh)
  have hval (x : Fin n → Bool)
      (hx : (wiresFrom pre (List.ofFn x)).getD h false = false) :
      (acc.1.getD out (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) =
        ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) := by
    have hi := inv_elim n (List.ofFn x) (by simp) (post.map normGate)
      (wiresFrom pre (List.ofFn x)) (positiveInitStats (n + pre.length) h, pre)
      (fun g hg => (hpost g hg).1) (positive_init_inv n pre h x hx)
    rw [← hacc] at hi
    have hv := (hi.2 out).2
    rw [wiresFrom_norm] at hv
    simpa only [Circuit.eval, Circuit.wires, wiresFrom, List.foldl_append] using hv
  cases hs : acc.1.getD out (Sum.inl false) with
  | inl c =>
    cases c with
    | false =>
      refine ⟨⟨pre, h⟩, hpre, ?_, ?_⟩
      · simp only [Circuit.size, List.length_append]
        have hp : pre.length ≤ acc.2.length := by rw [htail]; simp
        omega
      · intro x
        cases hx : (wiresFrom pre (List.ofFn x)).getD h false with
        | false =>
          have hv := hval x hx
          rw [hs] at hv
          change (wiresFrom pre (List.ofFn x)).getD h false = _
          rw [hx]
          exact hv
        | true =>
          change (wiresFrom pre (List.ofFn x)).getD h false = _
          rw [hx, hbelow x hx]
    | true =>
      refine ⟨⟨[⟨.and, []⟩], n⟩, ?_, ?_, ?_⟩
      · intro g hg
        obtain rfl := List.mem_singleton.mp hg
        simp
      · simp only [Circuit.size, List.length_append, List.length_singleton]
        omega
      · intro x
        have hf : ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) = true := by
          cases hx : (wiresFrom pre (List.ofFn x)).getD h false with
          | false =>
            have hv := hval x hx
            rw [hs] at hv
            exact hv.symm
          | true => exact hbelow x hx
        rw [hf]
        simp [Circuit.eval, Circuit.wires, GateOp.eval]
  | inr j =>
    refine ⟨⟨acc.2 ++ [⟨.or, [j, h]⟩], n + acc.2.length⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · exact hok g hg
      · obtain rfl := List.mem_singleton.mp hg
        simp
    · simp only [Circuit.size, List.length_append, List.length_singleton]
      omega
    · intro x
      rw [positive_top_or_eval, hpreserve]
      cases hx : (wiresFrom pre (List.ofFn x)).getD h false with
      | false =>
        simp only [Bool.or_false]
        have hv := hval x hx
        rw [hs] at hv
        exact hv
      | true => simp [hbelow x hx]

lemma positive_elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) :
    ∀ acc : List Stat × List Gate, k < acc.1.length →
      (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    change (elim n gs (elimStep n acc g)).1.getD k d = _
    rw [ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

lemma positive_elim_status_length (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp [elim]
  | cons g gs ih =>
    change (elim n gs (elimStep n acc g)).1.length = _
    rw [ih]
    simp [elimStep, Nat.add_comm, Nat.add_left_comm]

lemma positive_simplify_and_false (m : ℕ) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hz : Sum.inl false ∈ ins) :
    simplify GateOp.and m ins = (none, Sum.inl false) := by
  rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    (try cases a) <;> (try cases b) <;> simp_all [simplify, simpAnd]
  rcases hz with h | h <;> simp_all

lemma positive_simplify_not_false (m : ℕ) (ins : List Stat) (hlen : ins.length ≤ 1)
    (hz : Sum.inl false ∈ ins) :
    simplify GateOp.not m ins = (none, Sum.inl true) := by
  rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
  · simp at hz
  · simpa [simplify, simpNot] using
      congrArg (fun s => simplify GateOp.not m [s]) (List.mem_singleton.mp hz).symm
  · simp at hlen

lemma positive_non_or_simplifies (m k : ℕ) (g : Gate) (F : ℕ → Stat)
    (hok : NOk g) (hor : g.op ≠ GateOp.or) (hk : k ∈ g.inputs)
    (hz : F k = Sum.inl false) :
    ∃ c, simplify g.op m (g.inputs.map F) = (none, Sum.inl c) := by
  have hmem : Sum.inl false ∈ g.inputs.map F := List.mem_map.mpr ⟨k, hk, hz⟩
  rcases hok.1.1 with hop | hop | hop
  · refine ⟨false, ?_⟩
    rw [hop]
    exact positive_simplify_and_false m _ (by simpa using hok.1.2) hmem
  · exact False.elim (hor hop)
  · refine ⟨true, ?_⟩
    rw [hop]
    exact positive_simplify_not_false m _ (by simpa using hok.2 hop) hmem

lemma positive_readerCount_pos (k : ℕ) (gs : List Gate)
    (hr : ∃ g ∈ gs, k ∈ g.inputs) : 1 ≤ readerCount k gs := by
  induction gs with
  | nil => simp at hr
  | cons g gs ih =>
    obtain ⟨q, hq, hk⟩ := hr
    rcases List.mem_cons.mp hq with rfl | hq
    · simp [readerCount, hk]
    · have ht := ih ⟨q, hq, hk⟩
      simp only [readerCount]
      split_ifs <;> omega

lemma positive_non_or_reader_budget (n k : ℕ) (mid post : List Gate) (g : Gate)
    (acc : List Stat × List Gate)
    (hok : ∀ q ∈ mid ++ g :: post, NOk q)
    (hk : k < acc.1.length) (hz : acc.1.getD k (Sum.inl false) = Sum.inl false)
    (hor : g.op ≠ GateOp.or) (hread : k ∈ g.inputs)
    (hnext : ∃ q ∈ post, acc.1.length + mid.length ∈ q.inputs) :
    (elim n (mid ++ g :: post) acc).2.length + 2 ≤
      acc.2.length + (mid ++ g :: post).length := by
  let next := elim n mid acc
  have hnlen : next.1.length = acc.1.length + mid.length :=
    positive_elim_status_length n mid acc
  have hnzero : next.1.getD k (Sum.inl false) = Sum.inl false := by
    rw [positive_elim_getD n k _ mid acc hk, hz]
  obtain ⟨c, hc⟩ := positive_non_or_simplifies (n + next.2.length) k g
    (fun i => next.1.getD i (Sum.inl false))
    (hok g (List.mem_append_right _ List.mem_cons_self)) hor hread hnzero
  have hstep : elimStep n next g = (next.1 ++ [Sum.inl c], next.2) := by
    simp only [elimStep]
    rw [hc]
    simp
  have ht := elim_len_readers n (acc.1.length + mid.length) post (elimStep n next g)
    (fun q hq => hok q (List.mem_append_right _ (List.mem_cons_of_mem _ hq)))
    (by rw [hstep]; simp; omega)
    ⟨c, by rw [hstep, ← hnlen, getD_snoc_eq]⟩
  have hpos := positive_readerCount_pos _ post hnext
  have hm := elim_len n mid acc
  have he : elim n (mid ++ g :: post) acc = elim n post (elimStep n next g) := by
    simp [elim, List.foldl_append, next]
  rw [he, hstep]
  rw [hstep] at ht
  change next.2.length ≤ acc.2.length + mid.length at hm
  simp only [List.length_append, List.length_cons]
  dsimp only at ht
  omega

lemma positive_normGate_inputs (g : Gate) : (normGate g).inputs = effectiveInputs g := by
  rcases g with ⟨op, ins⟩
  cases op <;> rfl

lemma positive_normGate_op (g : Gate) : (normGate g).op = g.op := by
  rcases g with ⟨op, ins⟩
  cases op <;> rfl

lemma positive_non_or_consumer_improves (n : ℕ) (pre mid post : List Gate)
    (g : Gate) (out h : ℕ) (hh : h < n + pre.length)
    (hfanin : FanInTwo ({gates := pre ++ (mid ++ g :: post), output := out} : Circuit))
    (hbelow : ∀ x : Fin n → Bool,
      (wiresFrom pre (List.ofFn x)).getD h false = true →
        ({gates := pre ++ (mid ++ g :: post), output := out} : Circuit).eval (List.ofFn x) = true)
    (hor : g.op ≠ GateOp.or) (hread : h ∈ effectiveInputs g)
    (hnext : ∃ q ∈ post, n + pre.length + mid.length ∈ effectiveInputs q) :
    ∃ E : Circuit, FanInTwo E ∧
      E.size < ({gates := pre ++ (mid ++ g :: post), output := out} : Circuit).size ∧
      ∀ x : Fin n → Bool, E.eval (List.ofFn x) =
        ({gates := pre ++ (mid ++ g :: post), output := out} : Circuit).eval (List.ofFn x) := by
  have hnok : ∀ q ∈ mid.map normGate ++ normGate g :: post.map normGate, NOk q := by
    intro q hq
    have hq' : q ∈ (mid ++ g :: post).map normGate := by simpa using hq
    obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq'
    exact normGate_nok q0 (hfanin q0 (List.mem_append_right _ hq0))
  have hb := positive_non_or_reader_budget n h (mid.map normGate) (post.map normGate)
    (normGate g) (positiveInitStats (n + pre.length) h, pre) hnok
    (by simpa [positiveInitStats] using hh)
    (by rw [positive_init_get _ _ _ hh]; simp)
    (by simpa [positive_normGate_op] using hor)
    (by simpa [positive_normGate_inputs] using hread)
    (by
      obtain ⟨q, hq, hw⟩ := hnext
      refine ⟨normGate q, List.mem_map.mpr ⟨q, hq, rfl⟩, ?_⟩
      simpa [positiveInitStats, positive_normGate_inputs] using hw)
  have hbudget :
      (elim n ((mid ++ g :: post).map normGate)
        (positiveInitStats (n + pre.length) h, pre)).2.length + 2 ≤
        pre.length + (mid ++ g :: post).length := by
    simpa using hb
  obtain ⟨E, hE, hsize, he⟩ := positive_wire_lift_with_budget n pre (mid ++ g :: post)
    out h 2 hh hfanin hbelow hbudget
  exact ⟨E, hE, by omega, he⟩

lemma positive_gate_output_value (pre post : List Gate) (g : Gate) (xs : List Bool) :
    (wiresFrom (pre ++ g :: post) xs).getD (xs.length + pre.length) false =
      g.op.eval (g.inputs.map fun i => (wiresFrom pre xs).getD i false) := by
  rw [wiresFrom_append]
  change (wiresFrom post ((wiresFrom pre xs) ++
    [g.op.eval (g.inputs.map fun i => (wiresFrom pre xs).getD i false)])).getD _ false = _
  rw [getD_wiresFrom post _ _ (by simp [length_wiresFrom])]
  rw [← length_wiresFrom pre xs, getD_snoc_eq]

lemma positive_and_value_implies (g : Gate) (xs : List Bool) (h : ℕ)
    (hop : g.op = GateOp.and) (hread : h ∈ effectiveInputs g)
    (hv : g.op.eval (g.inputs.map fun i => xs.getD i false) = true) :
    xs.getD h false = true := by
  have hr : h ∈ g.inputs := by simpa [effectiveInputs, hop] using hread
  have he : (g.inputs.map fun i => xs.getD i false).all id = true := by
    simpa [hop, GateOp.eval] using hv
  have hall : ∀ v ∈ g.inputs.map (fun i => xs.getD i false), id v = true := by
    simpa only [List.all_eq_true] using he
  exact hall _ (List.mem_map.mpr ⟨h, hr, rfl⟩)

lemma positive_not_value (g : Gate) (xs : List Bool) (h : ℕ)
    (hop : g.op = GateOp.not) (hread : h ∈ effectiveInputs g) :
    g.op.eval (g.inputs.map fun i => xs.getD i false) = !xs.getD h false := by
  have hr : h ∈ g.inputs.take 1 := by simpa [effectiveInputs, hop] using hread
  cases hi : g.inputs with
  | nil => simp [hi] at hr
  | cons i ins =>
    have hh : h = i := by simpa [hi] using hr
    simp [hop, hh, GateOp.eval]

lemma minimum_positive_internal_readers_are_or (n : ℕ) (pre mid post : List Gate)
    (g : Gate) (out h : ℕ) (hn : n ≤ h) (hh : h < n + pre.length)
    (hfanin : FanInTwo ({gates := pre ++ (mid ++ g :: post), output := out} : Circuit))
    (hbelow : ∀ x : Fin n → Bool,
      (wiresFrom pre (List.ofFn x)).getD h false = true →
        ({gates := pre ++ (mid ++ g :: post), output := out} : Circuit).eval (List.ofFn x) = true)
    (hmin : ∀ E : Circuit, FanInTwo E →
      (∀ x : Fin n → Bool, E.eval (List.ofFn x) =
        ({gates := pre ++ (mid ++ g :: post), output := out} : Circuit).eval (List.ofFn x)) →
      ({gates := pre ++ (mid ++ g :: post), output := out} : Circuit).size ≤ E.size)
    (hread : h ∈ effectiveInputs g) : g.op = GateOp.or := by
  by_contra hor
  have hg : g ∈ pre ++ (mid ++ g :: post) := by simp
  have hprefix : ∀ q ∈ pre, Ok q := by
    intro q hq
    exact hfanin q (List.mem_append_left _ hq)
  by_cases hout : out = n + (pre ++ mid).length
  · have hvalue (x : Fin n → Bool) :
        ({gates := pre ++ (mid ++ g :: post), output := out} : Circuit).eval (List.ofFn x) =
        g.op.eval (g.inputs.map fun i => (wiresFrom (pre ++ mid) (List.ofFn x)).getD i false) := by
      simpa [Circuit.eval, Circuit.wires, wiresFrom, hout, List.foldl_append,
        List.append_assoc] using positive_gate_output_value (pre ++ mid) post g (List.ofFn x)
    have hkeep (x : Fin n → Bool) :
        (wiresFrom (pre ++ mid) (List.ofFn x)).getD h false =
        (wiresFrom pre (List.ofFn x)).getD h false := by
      rw [wiresFrom_append]
      exact getD_wiresFrom mid _ h (by simpa [length_wiresFrom] using hh)
    rcases (hfanin g hg).1 with hop | hop | hop
    · have himp (x : Fin n → Bool)
          (hx : ({gates := pre ++ (mid ++ g :: post), output := out} : Circuit).eval (List.ofFn x) = true) :
          (wiresFrom pre (List.ofFn x)).getD h false = true := by
        rw [hvalue] at hx
        have he := positive_and_value_implies g _ h hop hread hx
        rw [hkeep] at he
        exact he
      have heval (x : Fin n → Bool) :
          ({gates := pre, output := h} : Circuit).eval (List.ofFn x) =
          ({gates := pre ++ (mid ++ g :: post), output := out} : Circuit).eval (List.ofFn x) := by
        change (wiresFrom pre (List.ofFn x)).getD h false = _
        cases hx : (wiresFrom pre (List.ofFn x)).getD h false with
        | false =>
          cases hf : ({gates := pre ++ (mid ++ g :: post), output := out} : Circuit).eval (List.ofFn x) with
          | false => rfl
          | true => have he := himp x hf; rw [hx] at he; contradiction
        | true => rw [hbelow x hx]
      have hm := hmin ⟨pre, h⟩ hprefix heval
      simp only [Circuit.size, List.length_append, List.length_cons] at hm
      omega
    · exact hor hop
    · have hconst (x : Fin n → Bool) :
          ({gates := pre ++ (mid ++ g :: post), output := out} : Circuit).eval (List.ofFn x) = true := by
        have he := hvalue x
        rw [positive_not_value g _ h hop hread, hkeep] at he
        cases hx : (wiresFrom pre (List.ofFn x)).getD h false with
        | false =>
          rw [hx] at he
          exact he
        | true => exact hbelow x hx
      have hE : FanInTwo ({gates := [⟨.and, []⟩], output := n} : Circuit) := by
        intro q hq
        obtain rfl := List.mem_singleton.mp hq
        simp
      have hm := hmin ⟨[⟨.and, []⟩], n⟩ hE (by
        intro x
        rw [hconst x]
        simp [Circuit.eval, Circuit.wires, GateOp.eval])
      simp only [Circuit.size, List.length_append, List.length_cons, List.length_nil] at hm
      omega
  · obtain ⟨q, hq, hqr⟩ := LivePruning.minimal_live n
      ({gates := pre ++ (mid ++ g :: post), output := out} : Circuit) hfanin hmin
      (pre ++ mid) post g (by simp [List.append_assoc]) hout
    have hnext : ∃ q ∈ post, n + pre.length + mid.length ∈ effectiveInputs q := by
      refine ⟨q, hq, ?_⟩
      change n + (pre ++ mid).length ∈ effectiveInputs q at hqr
      rw [List.length_append] at hqr
      simpa only [Nat.add_assoc] using hqr
    obtain ⟨E, hE, hsize, heval⟩ :=
      positive_non_or_consumer_improves n pre mid post g out h hh hfanin hbelow hor hread hnext
    have hm := hmin E hE heval
    omega



namespace FirstAndClassification


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Restriction

lemma petersen_first_and_endpoint_sparse (C : Circuit) (v : Fin 10) (g : Gate) (post : List Gate)
    (hfan : FanInTwo C) (hsize : C.size ≤ 19)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < 10 + j)
    (hgs : C.gates = g :: post) (hg : g.op = GateOp.and) (hread : v.val ∈ g.inputs)
    (hraw : ∃ q ∈ post, v.val ∈ q.inputs)
    (hev : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x)
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin 9 → Bool, E.eval (List.ofFn y) = petersen (Fin.snoc y false)) →
      16 ≤ E.size) :
    readerCount v.val post = 1 ∧ ∀ q ∈ post, v.val ∈ q.inputs → q.op = GateOp.or := by
  let s := (Transport.relabel v).symm
  let D := InputRename.circuit s C
  have hsa : s v = 9 := Transport.relabel_symm_vertex v
  have hs9 : s.symm 9 = v := by rw [← hsa]; simp
  have hwire : InputRename.wire s v.val = 9 := by
    simp only [InputRename.wire, dite_eq_left v.isLt, hsa]
    rfl
  have hDfan : FanInTwo D := InputRename.fanInTwo s C hfan
  have hDsize : D.size ≤ 19 := by simpa only [D, InputRename.size] using hsize
  have hDmin := rename_minimal s C hmin
  have hDnormal := rename_normal s C hnot
  have hDback := rename_back s C back
  have hDgs : D.gates = InputRename.gate s g :: post.map (InputRename.gate s) := by
    change C.gates.map (InputRename.gate s) = _
    rw [hgs, List.map_cons]
  have hDev : ∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = petersen x := by
    intro x
    change (InputRename.circuit s C).eval (List.ofFn x) = _
    rw [InputRename.eval_relabel, hev]
    exact Transport.edge_relabel_symm v x
  have hDlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin 9 → Bool, E.eval (List.ofFn y) = D.eval (List.ofFn (Fin.snoc y false))) →
      16 ≤ E.size := by
    intro E hE he
    apply hlower E hE
    intro y
    rw [he, hDev]
  have hDnc : ∃ y y' : Fin 9 → Bool,
      D.eval (List.ofFn (Fin.snoc y false)) ≠ D.eval (List.ofFn (Fin.snoc y' false)) := by
    refine ⟨(fun _ => false), (fun i => decide (i = 0 ∨ i = 1)), ?_⟩
    rw [hDev, hDev]
    decide +kernel
  have hDread : 9 ∈ (InputRename.gate s g).inputs := List.mem_map.mpr ⟨v.val, hread, hwire⟩
  have hDraw : ∃ q ∈ post.map (InputRename.gate s), 9 ∈ q.inputs := by
    obtain ⟨q, hq, hqr⟩ := hraw
    exact ⟨InputRename.gate s q, List.mem_map_of_mem hq, List.mem_map.mpr ⟨v.val, hqr, hwire⟩⟩
  have hcount := minimal_first_and_unique_other_raw_reader 9 D (InputRename.gate s g)
    (post.map (InputRename.gate s)) hDfan hDsize hDmin hDnormal hDback hDnc hDlower
    hDgs hg hDread hDraw
  have hReaders : ∀ q ∈ post.map (InputRename.gate s), 9 ∈ q.inputs → q.op = GateOp.or := by
    intro q hq hqread
    obtain ⟨pre, tail, hpost⟩ := List.mem_iff_append.mp hq
    exact minimal_first_and_other_raw_reader_or 9 D (InputRename.gate s g) q pre tail
      hDfan hDsize hDmin hDnormal hDback hDnc hDlower
      (by rw [hDgs, hpost]) hg hDread hqread
  refine ⟨?_, ?_⟩
  · have he := InputRename.readerCount_map s (9 : Fin 10) post
    rw [hs9] at he
    exact he.symm.trans hcount
  · intro q hq hqread
    have hqD : InputRename.gate s q ∈ post.map (InputRename.gate s) := List.mem_map_of_mem hq
    have hrD : 9 ∈ (InputRename.gate s q).inputs := List.mem_map.mpr ⟨v.val, hqread, hwire⟩
    exact hReaders (InputRename.gate s q) hqD hrD

lemma petersen_first_and_sparse_readers_any (C : Circuit) (a b : Fin 10) (post : List Gate)
    (hab : a ≠ b) (hfan : FanInTwo C) (hsize : C.size ≤ 19)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < 10 + j)
    (hgs : C.gates = ⟨GateOp.and, [a.val, b.val]⟩ :: post)
    (hev : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x)
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin 9 → Bool, E.eval (List.ofFn y) = petersen (Fin.snoc y false)) →
      16 ≤ E.size) :
    (readerCount a.val post = 1 ∧ ∀ q ∈ post, a.val ∈ q.inputs → q.op = GateOp.or) ∧
    (readerCount b.val post = 1 ∧ ∀ q ∈ post, b.val ∈ q.inputs → q.op = GateOp.or) ∧
    (readerCount 10 post = 1 ∧ ∀ q ∈ post, 10 ∈ q.inputs → q.op = GateOp.or) := by
  have hC : C = ⟨⟨GateOp.and, [a.val, b.val]⟩ :: post, C.output⟩ := by cases C; simp_all
  have hev' : ∀ x : Fin 10 → Bool,
      (Circuit.mk ([] ++ ⟨GateOp.and, [a.val, b.val]⟩ :: post) C.output).eval (List.ofFn x) = petersen x := by
    intro x
    simpa only [List.nil_append, ← hC] using hev x
  have hreads := binary_inputs_read_elsewhere GateOp.and (Or.inl rfl) a b hab [] post C.output hev'
  have hsub (q : Gate) : effectiveInputs q ⊆ q.inputs := by
    simp only [effectiveInputs]
    split
    · exact List.take_subset _ _
    · exact List.Subset.refl _
  have ha : ∃ q ∈ post, a.val ∈ q.inputs := by
    obtain ⟨q, hq, hr⟩ := hreads.1
    exact ⟨q, by simpa using hq, hsub q hr⟩
  have hb : ∃ q ∈ post, b.val ∈ q.inputs := by
    obtain ⟨q, hq, hr⟩ := hreads.2
    exact ⟨q, by simpa using hq, hsub q hr⟩
  exact ⟨petersen_first_and_endpoint_sparse C a _ post hfan hsize hmin hnot back hgs
      rfl (by simp) ha hev hlower,
    petersen_first_and_endpoint_sparse C b _ post hfan hsize hmin hnot back hgs
      rfl (by simp) hb hev hlower,
    petersen_first_and_unique_or_consumer_any C a b post hab hfan hsize hmin hnot back hgs hev hlower⟩


end FirstAndClassification


namespace FirstAndClassification


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2373_aux.Restriction

lemma minimal_or_reader_two_distinct_inputs (n : ℕ) (C : Circuit)
    (hfan : FanInTwo C)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j)
    (j h : ℕ) (q : Gate) (hj : C.gates[j]? = some q)
    (hop : q.op = GateOp.or) (hread : h ∈ q.inputs) :
    ∃ t, t ≠ h ∧ t < n + j ∧ (q.inputs = [h, t] ∨ q.inputs = [t, h]) := by
  have hlen := (hfan q (List.mem_of_getElem? hj)).2
  have hlt : j < C.size := (List.getElem?_eq_some_iff.mp hj).1
  have hh := back j q hj h hread
  have hno := AliasPruning.minimal_no_alias_index n C hfan hmin j hlt h hh
  have hvalue := full_gate_value_index n C back j q hj
  rcases hins : q.inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, tail⟩⟩⟩
  · simp [hins] at hread
  · have he : h = a := by simpa [hins] using hread
    subst a
    exfalso
    apply hno
    intro x
    rw [hvalue x, hop, hins]
    simp [GateOp.eval]
  · have he : h = a ∨ h = b := by simpa [hins] using hread
    rcases he with rfl | rfl
    · by_cases hb : b = h
      · subst b
        exfalso
        apply hno
        intro x
        rw [hvalue x, hop, hins]
        simp [GateOp.eval]
      · exact ⟨b, hb, back j q hj b (by simp [hins]), Or.inl rfl⟩
    · by_cases ha : a = h
      · subst a
        exfalso
        apply hno
        intro x
        rw [hvalue x, hop, hins]
        simp [GateOp.eval]
      · exact ⟨a, ha, back j q hj a (by simp [hins]), Or.inr rfl⟩
  · simp [hins] at hlen

lemma unique_reader_split_avoids (h : ℕ) (pre post : List Gate) (q : Gate)
    (hcount : readerCount h (pre ++ q :: post) = 1) (hread : h ∈ q.inputs) :
    (∀ g ∈ pre, h ∉ g.inputs) ∧ ∀ g ∈ post, h ∉ g.inputs := by
  have he : readerCount h pre + (1 + readerCount h post) = 1 := by
    simpa only [readerCount_append, readerCount, ite_eq_left hread] using hcount
  have hp : readerCount h pre = 0 := by omega
  have ht : readerCount h post = 0 := by omega
  constructor
  · intro g hg hr
    have hz := (readerCount_pos_iff h pre).mpr ⟨g, hg, hr⟩
    omega
  · intro g hg hr
    have hz := (readerCount_pos_iff h post).mpr ⟨g, hg, hr⟩
    omega


end FirstAndClassification

namespace ResidualFirstAnd


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Restriction

lemma alias_erase_eval_at (n : ℕ) (pre post : List Gate) (g : Gate) (p o : ℕ)
    (hp : p < n + pre.length) (x : Fin n → Bool)
    (hcopy : (Circuit.wires ⟨pre ++ g :: post, o⟩ (List.ofFn x)).getD (n + pre.length) false =
      (Circuit.wires ⟨pre ++ g :: post, o⟩ (List.ofFn x)).getD p false) :
    (AliasPruning.erase n pre post p o).eval (List.ofFn x) =
      (Circuit.mk (pre ++ g :: post) o).eval (List.ofFn x) := by
  let xs := Circuit.wires ⟨pre, 0⟩ (List.ofFn x)
  have hx : xs.length = n + pre.length := by
    unfold xs
    rw [LivePruning.wires_length, List.length_ofFn]
  have hcopy' : LivePruning.gateValue g xs = xs.getD p false := by
    have h := hcopy
    simp only [Circuit.wires, List.foldl_append, List.foldl_cons] at h
    change (Circuit.wires ⟨post, 0⟩ (xs ++ [LivePruning.gateValue g xs])).getD (n + pre.length) false =
      (Circuit.wires ⟨post, 0⟩ (xs ++ [LivePruning.gateValue g xs])).getD p false at h
    rw [AliasPruning.wires_input _ _ _ (by simp [hx]),
      AliasPruning.wires_input _ _ _ (by simp [hx]; omega)] at h
    rw [List.getD_append xs [LivePruning.gateValue g xs] false p (by omega), ← hx] at h
    simpa [List.getD_eq_getElem?_getD] using h
  simp only [AliasPruning.erase, Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons]
  change (Circuit.wires ⟨post.map (AliasPruning.renamed (n + pre.length) p), 0⟩ xs).getD
      (AliasPruning.redirect (n + pre.length) p o) false =
    (Circuit.wires ⟨post, 0⟩ (xs ++ [LivePruning.gateValue g xs])).getD o false
  apply AliasPruning.wires_renamed _ _ _ _ _ (by simp) (by simp [hx]) hp _ o
  rw [← hx]
  exact AliasPruning.initial_agree xs p _ hcopy'

lemma redirect_avoids_earlier (h k t i : ℕ) (hhk : h < k) (ht : t ≠ h) (hi : i ≠ h) :
    AliasPruning.redirect k t i ≠ h := by
  by_cases hik : i = k
  · simpa [AliasPruning.redirect, hik] using ht
  · simp only [AliasPruning.redirect, ite_eq_right hik, LivePruning.down]
    split <;> omega

lemma renamed_avoids_earlier (h k t : ℕ) (g : Gate)
    (hhk : h < k) (ht : t ≠ h) (hg : h ∉ g.inputs) :
    h ∉ (AliasPruning.renamed k t g).inputs := by
  intro hr
  obtain ⟨i, hi, he⟩ := List.mem_map.mp hr
  exact redirect_avoids_earlier h k t i hhk ht (by intro h; subst i; exact hg hi) he

def circuit (n : ℕ) (pre post : List Gate) (t o : ℕ) : Circuit :=
  LivePruning.erase n []
    (pre ++ post.map (AliasPruning.renamed (n + (pre.length + 1)) t))
    (AliasPruning.redirect (n + (pre.length + 1)) t o)

lemma circuit_size (n : ℕ) (pre post : List Gate) (g q : Gate) (t o : ℕ) :
    (circuit n pre post t o).size + 2 = (Circuit.mk (g :: (pre ++ q :: post)) o).size := by
  simp [circuit, LivePruning.erase, Circuit.size]
  omega

lemma circuit_fanin (n : ℕ) (pre post : List Gate) (g q : Gate) (t o : ℕ)
    (hfan : FanInTwo (Circuit.mk (g :: (pre ++ q :: post)) o)) :
    FanInTwo (circuit n pre post t o) := by
  have halias := AliasPruning.erase_fanin n (g :: pre) post q t o (by simpa using hfan)
  exact LivePruning.erase_fanin n []
    (pre ++ post.map (AliasPruning.renamed (n + (pre.length + 1)) t)) g
    (AliasPruning.redirect (n + (pre.length + 1)) t o) halias

lemma circuit_eval_of_first_false (n : ℕ) (pre post : List Gate) (g q : Gate) (t o : ℕ)
    (hq : q.op = GateOp.or) (hinputs : q.inputs = [n, t] ∨ q.inputs = [t, n])
    (ht : t < n + (pre.length + 1)) (htn : t ≠ n)
    (hpre : ∀ r ∈ pre, n ∉ r.inputs) (hpost : ∀ r ∈ post, n ∉ r.inputs)
    (ho : o ≠ n) (x : Fin n → Bool)
    (hzero : (Circuit.wires ⟨g :: (pre ++ q :: post), o⟩ (List.ofFn x)).getD n false = false) :
    (circuit n pre post t o).eval (List.ofFn x) =
      (Circuit.mk (g :: (pre ++ q :: post)) o).eval (List.ofFn x) := by
  have hcut : n < n + (pre.length + 1) := by omega
  have hqback : ∀ i ∈ q.inputs, i < n + (g :: pre).length := by
    rcases hinputs with hinputs | hinputs <;> simp only [hinputs, List.mem_cons,
      List.not_mem_nil, or_false, List.length_cons] <;> intro i hi <;>
      rcases hi with rfl | rfl <;> omega
  have hqval := FirstAndClassification.full_gate_value n
    (Circuit.mk (g :: (pre ++ q :: post)) o) (g :: pre) post q
    (by simp) hqback x
  have hcopy : (Circuit.wires ⟨(g :: pre) ++ q :: post, o⟩ (List.ofFn x)).getD
      (n + (g :: pre).length) false =
      (Circuit.wires ⟨(g :: pre) ++ q :: post, o⟩ (List.ofFn x)).getD t false := by
    simpa only [List.cons_append] using (show
      (Circuit.wires ⟨g :: (pre ++ q :: post), o⟩ (List.ofFn x)).getD
        (n + (g :: pre).length) false =
        (Circuit.wires ⟨g :: (pre ++ q :: post), o⟩ (List.ofFn x)).getD t false from by
      rw [hqval, hq]
      rcases hinputs with hi | hi <;> rw [hi] <;>
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil] <;>
        rw [hzero] <;> simp)
  have halias := alias_erase_eval_at n (g :: pre) post q t o ht x hcopy
  have hun : ∀ r ∈ pre ++ post.map (AliasPruning.renamed (n + (pre.length + 1)) t),
      n + ([] : List Gate).length ∉ LivePruning.effective r := by
    intro r hr hn
    have hin : n ∈ r.inputs := cofactor_effective_mem_inputs r n (by simpa using hn)
    rcases List.mem_append.mp hr with hr | hr
    · exact hpre r hr hin
    · obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
      exact renamed_avoids_earlier n _ t s hcut htn (hpost s hs) hin
  have houtput : AliasPruning.redirect (n + (pre.length + 1)) t o ≠ n + ([] : List Gate).length := by
    simpa using redirect_avoids_earlier n _ t o hcut htn ho
  have herase := LivePruning.erase_eval n []
    (pre ++ post.map (AliasPruning.renamed (n + (pre.length + 1)) t)) g
    (AliasPruning.redirect (n + (pre.length + 1)) t o) hun houtput x
  exact herase.trans halias

lemma exists_residual_of_minimal_unique_or (n : ℕ) (C : Circuit) (g : Gate) (tail : List Gate)
    (hfan : FanInTwo C)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (back : ∀ j q, C.gates[j]? = some q → ∀ i ∈ q.inputs, i < n + j)
    (hgs : C.gates = g :: tail) (hcount : readerCount n tail = 1)
    (hor : ∀ q ∈ tail, n ∈ q.inputs → q.op = GateOp.or) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 2 = C.size ∧
      ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD n false = false →
        D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  obtain ⟨q, hq, hqread⟩ := (readerCount_pos_iff n tail).mp (by omega)
  obtain ⟨pre, post, htail⟩ := List.mem_iff_append.mp hq
  have hsplit : C.gates = g :: (pre ++ q :: post) := by rw [hgs, htail]
  have hqindex : C.gates[pre.length + 1]? = some q := by simp [hsplit]
  obtain ⟨t, htn, ht, hinputs⟩ := FirstAndClassification.minimal_or_reader_two_distinct_inputs
    n C hfan hmin back (pre.length + 1) n q hqindex (hor q hq hqread) hqread
  have havoids := FirstAndClassification.unique_reader_split_avoids n pre post q
    (by rw [← htail]; exact hcount) hqread
  have hsize : 2 ≤ C.size := by
    simp [Circuit.size, hsplit]
    omega
  have hout := LivePruning.minimal_output_last n C hfan hmin (by omega)
  have houtput : C.output ≠ n := by omega
  have hC : C = ⟨g :: (pre ++ q :: post), C.output⟩ := by cases C; simp_all
  refine ⟨circuit n pre post t C.output, ?_, ?_, ?_⟩
  · exact circuit_fanin n pre post g q t C.output (by simpa only [← hC] using hfan)
  · simpa only [← hC] using circuit_size n pre post g q t C.output
  · intro x hzero
    simpa only [← hC] using circuit_eval_of_first_false n pre post g q t C.output
      (hor q hq hqread) hinputs ht htn havoids.1 havoids.2 houtput x
      (by simpa only [← hC] using hzero)

lemma petersen_first_and_residual_seventeen (C : Circuit) (a b : Fin 10) (tail : List Gate)
    (hab : a ≠ b) (hfan : FanInTwo C) (hsize : C.size ≤ 19)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < 10 + j)
    (hgs : C.gates = ⟨GateOp.and, [a.val, b.val]⟩ :: tail)
    (hev : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x)
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin 9 → Bool, E.eval (List.ofFn y) = petersen (Fin.snoc y false)) →
      16 ≤ E.size) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 2 = C.size ∧ D.size ≤ 17 ∧
      ∀ x : Fin 10 → Bool, (x a && x b) = false → D.eval (List.ofFn x) = petersen x := by
  have hreaders := FirstAndClassification.petersen_first_and_unique_or_consumer_any
    C a b tail hab hfan hsize hmin hnot back hgs hev hlower
  obtain ⟨D, hD, hDsize, hDeval⟩ := exists_residual_of_minimal_unique_or 10 C _ tail
    hfan hmin back hgs hreaders.1 hreaders.2
  refine ⟨D, hD, hDsize, by omega, ?_⟩
  intro x hxab
  have hgindex : C.gates[0]? = some ⟨GateOp.and, [a.val, b.val]⟩ := by simp [hgs]
  have hfirst := FirstAndClassification.full_gate_value_index 10 C back 0
    ⟨GateOp.and, [a.val, b.val]⟩ hgindex x
  have hzero : (C.wires (List.ofFn x)).getD 10 false = false := by
    simp only [Nat.add_zero] at hfirst
    rw [hfirst]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, Bool.and_true]
    rw [Wires.wires_input C _ a.val (by simp), Wires.wires_input C _ b.val (by simp)]
    simpa only [getD_ofFn_val, id_eq] using hxab
  rw [hDeval x hzero, hev x]


end ResidualFirstAnd

namespace ResidualFirstAnd


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Restriction

lemma circuit_gate_ops (n : ℕ) (pre post : List Gate) (t o : ℕ) :
    (circuit n pre post t o).gates.map Gate.op =
      pre.map Gate.op ++ post.map Gate.op := by
  simp [circuit, LivePruning.erase, LivePruning.rename, AliasPruning.renamed,
    List.map_append, List.map_map, Function.comp_def]

lemma circuit_monotone (n : ℕ) (pre post : List Gate) (g q : Gate) (t o : ℕ)
    (hmono : Monotone2 (Circuit.mk (g :: (pre ++ q :: post)) o)) :
    Monotone2 (circuit n pre post t o) := by
  intro r hr
  change r ∈ (pre ++ post.map (AliasPruning.renamed (n + (pre.length + 1)) t)).map
    (LivePruning.rename n) at hr
  obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hr
  have hsm : s.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ s.inputs.length ≤ 2 := by
    rcases List.mem_append.mp hs with hs | hs
    · exact hmono s (by simp [hs])
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hs
      simpa only [AliasPruning.renamed, List.length_map] using hmono u (by simp [hu])
  simpa only [LivePruning.rename, List.length_map] using hsm

lemma notCount_eq_filter_isNot (C : Circuit) :
    PEqualNP.NotBracket.notCount C = (C.gates.filter isNot).length := by
  unfold PEqualNP.NotBracket.notCount
  congr 1
  apply List.filter_congr
  intro g hg
  rcases g with ⟨op, inputs⟩
  cases op <;> rfl

lemma circuit_notCount (n : ℕ) (pre post : List Gate) (g q : Gate) (t o : ℕ)
    (hg : g.op = GateOp.and) (hq : q.op = GateOp.or) :
    PEqualNP.NotBracket.notCount (circuit n pre post t o) =
      PEqualNP.NotBracket.notCount (Circuit.mk (g :: (pre ++ q :: post)) o) := by
  simp [PEqualNP.NotBracket.notCount, circuit, LivePruning.erase,
    LivePruning.rename, AliasPruning.renamed, List.filter_map, Function.comp_def, hg, hq]
  rfl

lemma circuit_isNot_count (n : ℕ) (pre post : List Gate) (g q : Gate) (t o : ℕ)
    (hg : g.op = GateOp.and) (hq : q.op = GateOp.or) :
    ((circuit n pre post t o).gates.filter isNot).length =
      ((Circuit.mk (g :: (pre ++ q :: post)) o).gates.filter isNot).length := by
  rw [← notCount_eq_filter_isNot, ← notCount_eq_filter_isNot]
  exact circuit_notCount n pre post g q t o hg hq

lemma exists_residual_of_minimal_unique_or_kinds (n : ℕ) (C : Circuit) (g : Gate) (tail : List Gate)
    (hfan : FanInTwo C)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (back : ∀ j q, C.gates[j]? = some q → ∀ i ∈ q.inputs, i < n + j)
    (hgs : C.gates = g :: tail) (hg : g.op = GateOp.and) (hcount : readerCount n tail = 1)
    (hor : ∀ q ∈ tail, n ∈ q.inputs → q.op = GateOp.or) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 2 = C.size ∧
      PEqualNP.NotBracket.notCount D = PEqualNP.NotBracket.notCount C ∧
      (Monotone2 C → Monotone2 D) ∧
      ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD n false = false →
        D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  obtain ⟨q, hq, hqread⟩ := (readerCount_pos_iff n tail).mp (by omega)
  obtain ⟨pre, post, htail⟩ := List.mem_iff_append.mp hq
  have hsplit : C.gates = g :: (pre ++ q :: post) := by rw [hgs, htail]
  have hqindex : C.gates[pre.length + 1]? = some q := by simp [hsplit]
  obtain ⟨t, htn, ht, hinputs⟩ := FirstAndClassification.minimal_or_reader_two_distinct_inputs
    n C hfan hmin back (pre.length + 1) n q hqindex (hor q hq hqread) hqread
  have havoids := FirstAndClassification.unique_reader_split_avoids n pre post q
    (by rw [← htail]; exact hcount) hqread
  have hsize : 2 ≤ C.size := by
    simp [Circuit.size, hsplit]
    omega
  have hout := LivePruning.minimal_output_last n C hfan hmin (by omega)
  have houtput : C.output ≠ n := by omega
  have hC : C = ⟨g :: (pre ++ q :: post), C.output⟩ := by cases C; simp_all
  refine ⟨circuit n pre post t C.output, ?_, ?_, ?_, ?_, ?_⟩
  · exact circuit_fanin n pre post g q t C.output (by simpa only [← hC] using hfan)
  · simpa only [← hC] using circuit_size n pre post g q t C.output
  · simpa only [← hC] using circuit_notCount n pre post g q t C.output hg (hor q hq hqread)
  · intro hmono
    exact circuit_monotone n pre post g q t C.output (by simpa only [← hC] using hmono)
  · intro x hzero
    simpa only [← hC] using circuit_eval_of_first_false n pre post g q t C.output
      (hor q hq hqread) hinputs ht htn havoids.1 havoids.2 houtput x
      (by simpa only [← hC] using hzero)

lemma petersen_first_and_residual_seventeen_kinds (C : Circuit) (a b : Fin 10) (tail : List Gate)
    (hab : a ≠ b) (hfan : FanInTwo C) (hsize : C.size ≤ 19)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < 10 + j)
    (hgs : C.gates = ⟨GateOp.and, [a.val, b.val]⟩ :: tail)
    (hev : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x)
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin 9 → Bool, E.eval (List.ofFn y) = petersen (Fin.snoc y false)) →
      16 ≤ E.size) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 2 = C.size ∧ D.size ≤ 17 ∧
      PEqualNP.NotBracket.notCount D = PEqualNP.NotBracket.notCount C ∧
      (Monotone2 C → Monotone2 D) ∧
      ∀ x : Fin 10 → Bool, (x a && x b) = false → D.eval (List.ofFn x) = petersen x := by
  have hreaders := FirstAndClassification.petersen_first_and_unique_or_consumer_any
    C a b tail hab hfan hsize hmin hnot back hgs hev hlower
  obtain ⟨D, hD, hDsize, hDnot, hDmono, hDeval⟩ := exists_residual_of_minimal_unique_or_kinds 10 C _ tail
    hfan hmin back hgs rfl hreaders.1 hreaders.2
  refine ⟨D, hD, hDsize, by omega, hDnot, hDmono, ?_⟩
  intro x hxab
  have hgindex : C.gates[0]? = some ⟨GateOp.and, [a.val, b.val]⟩ := by simp [hgs]
  have hfirst := FirstAndClassification.full_gate_value_index 10 C back 0
    ⟨GateOp.and, [a.val, b.val]⟩ hgindex x
  have hzero : (C.wires (List.ofFn x)).getD 10 false = false := by
    simp only [Nat.add_zero] at hfirst
    rw [hfirst]
    simp only [List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil, Bool.and_true]
    rw [Wires.wires_input C _ a.val (by simp), Wires.wires_input C _ b.val (by simp)]
    simpa only [getD_ofFn_val, id_eq] using hxab
  rw [hDeval x hzero, hev x]


lemma petersen_first_and_residual_seventeen_with_not_bound
    (C : Circuit) (a b : Fin 10) (tail : List Gate) (k : ℕ)
    (hab : a ≠ b) (hfan : FanInTwo C) (hsize : C.size ≤ 19)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin 10 → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < 10 + j)
    (hgs : C.gates = ⟨GateOp.and, [a.val, b.val]⟩ :: tail)
    (hev : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = petersen x)
    (hlower : ∀ E : Circuit, FanInTwo E →
      (∀ y : Fin 9 → Bool, E.eval (List.ofFn y) = petersen (Fin.snoc y false)) →
      16 ≤ E.size)
    (hbudget : PEqualNP.NotBracket.notCount C ≤ k) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 2 = C.size ∧ D.size ≤ 17 ∧
      PEqualNP.NotBracket.notCount D ≤ k ∧ (Monotone2 C → Monotone2 D) ∧
      ∀ x : Fin 10 → Bool, (x a && x b) = false → D.eval (List.ofFn x) = petersen x := by
  obtain ⟨D, hD, hDsize, hseventeen, hnotcount, hmono, heval⟩ :=
    petersen_first_and_residual_seventeen_kinds C a b tail hab hfan hsize hmin hnot
      back hgs hev hlower
  exact ⟨D, hD, hDsize, hseventeen, hnotcount ▸ hbudget, hmono, heval⟩


end ResidualFirstAnd


namespace BoundaryOperands

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2373_aux

def ordered (up : Bool) (new old : Bool) : Prop := if up then old ≤ new else new ≤ old

lemma ordered_refl (up a : Bool) : ordered up a a := by cases up <;> simp [ordered]

lemma ordered_and : ∀ up a b c d : Bool, ordered up a b → ordered up c d →
    ordered up (a && c) (b && d) := by unfold ordered; decide +kernel

lemma ordered_or : ∀ up a b c d : Bool, ordered up a b → ordered up c d →
    ordered up (a || c) (b || d) := by unfold ordered; decide +kernel

lemma all_ordered (up : Bool) (ins : List ℕ) (f g : ℕ → Bool)
    (h : ∀ i ∈ ins, ordered up (f i) (g i)) :
    ordered up ((ins.map f).all id) ((ins.map g).all id) := by
  induction ins with
  | nil => exact ordered_refl up true
  | cons i ins ih =>
    simp only [List.map_cons, List.all_cons, id_eq]
    exact ordered_and up _ _ _ _ (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

lemma any_ordered (up : Bool) (ins : List ℕ) (f g : ℕ → Bool)
    (h : ∀ i ∈ ins, ordered up (f i) (g i)) :
    ordered up ((ins.map f).any id) ((ins.map g).any id) := by
  induction ins with
  | nil => exact ordered_refl up false
  | cons i ins ih =>
    simp only [List.map_cons, List.any_cons, id_eq]
    exact ordered_or up _ _ _ _ (h i (by simp)) (ih (fun j hj => h j (by simp [hj])))

lemma gate_ordered (up : Bool) (q : Gate) (f g : ℕ → Bool)
    (hop : q.op = GateOp.and ∨ q.op = GateOp.or)
    (h : ∀ i ∈ q.inputs, ordered up (f i) (g i)) :
    ordered up (q.op.eval (q.inputs.map f)) (q.op.eval (q.inputs.map g)) := by
  rcases hop with hop | hop
  · simpa [hop, GateOp.eval] using all_ordered up q.inputs f g h
  · simpa [hop, GateOp.eval] using any_ordered up q.inputs f g h

lemma append_ordered (up : Bool) (k p : ℕ) (xs ys : List Bool) (u v : Bool)
    (hlen : xs.length + 1 = ys.length) (hk : k < ys.length) (hp : p < k)
    (h : ∀ i, ordered up (xs.getD (AliasPruning.redirect k p i) false) (ys.getD i false))
    (huv : ordered up u v) :
    ∀ i, ordered up ((xs ++ [u]).getD (AliasPruning.redirect k p i) false)
      ((ys ++ [v]).getD i false) := by
  intro i
  by_cases hik : i = k
  · subst i
    simp only [AliasPruning.redirect, ite_true]
    rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ hk]
    simpa [AliasPruning.redirect] using h k
  · simp only [AliasPruning.redirect, ite_eq_right hik]
    rcases Nat.lt_trichotomy i ys.length with hlt | he | hgt
    · have hd : LivePruning.down k i < xs.length := by
        unfold LivePruning.down
        split <;> omega
      rw [List.getD_append _ _ _ _ hd, List.getD_append _ _ _ _ hlt]
      simpa [AliasPruning.redirect, hik] using h i
    · subst i
      have hd : LivePruning.down k ys.length = xs.length := by
        unfold LivePruning.down
        split <;> omega
      rw [hd]
      simpa using huv
    · rw [List.getD_eq_default _ _ (by
        simp only [List.length_append, List.length_singleton]
        unfold LivePruning.down
        split <;> omega),
        List.getD_eq_default _ _ (by simp; omega)]
      exact ordered_refl up false

lemma initial_ordered (up : Bool) (xs : List Bool) (p : ℕ) (v : Bool)
    (h : ordered up (xs.getD p false) v) :
    ∀ i, ordered up (xs.getD (AliasPruning.redirect xs.length p i) false)
      ((xs ++ [v]).getD i false) := by
  intro i
  by_cases hi : i = xs.length
  · subst i
    simpa [AliasPruning.redirect] using h
  · have he := LivePruning.initial_agree xs v i hi
    rw [show AliasPruning.redirect xs.length p i = LivePruning.down xs.length i by
      simp [AliasPruning.redirect, hi], he]
    exact ordered_refl up _

lemma wires_ordered (up : Bool) (k p : ℕ) (gs : List Gate) (xs ys : List Bool)
    (hlen : xs.length + 1 = ys.length) (hk : k < ys.length) (hp : p < k)
    (hmono : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (h : ∀ i, ordered up (xs.getD (AliasPruning.redirect k p i) false) (ys.getD i false)) :
    ∀ i, ordered up
      ((Circuit.wires ⟨gs.map (AliasPruning.renamed k p), 0⟩ xs).getD
        (AliasPruning.redirect k p i) false)
      ((Circuit.wires ⟨gs, 0⟩ ys).getD i false) := by
  induction gs generalizing xs ys with
  | nil => exact h
  | cons g gs ih =>
    have hg : ordered up (LivePruning.gateValue (AliasPruning.renamed k p g) xs)
        (LivePruning.gateValue g ys) := by
      unfold LivePruning.gateValue AliasPruning.renamed
      simp only [List.map_map, Function.comp_def]
      exact gate_ordered up g _ _ (hmono g (by simp)) (fun i _ => h i)
    change ∀ i, ordered up
      ((Circuit.wires ⟨gs.map (AliasPruning.renamed k p), 0⟩
        (xs ++ [LivePruning.gateValue (AliasPruning.renamed k p g) xs])).getD
          (AliasPruning.redirect k p i) false)
      ((Circuit.wires ⟨gs, 0⟩ (ys ++ [LivePruning.gateValue g ys])).getD i false)
    apply ih _ _
    · simp only [List.length_append, List.length_singleton]; omega
    · simp only [List.length_append, List.length_singleton]; omega
    · intro q hq
      exact hmono q (by simp [hq])
    · exact append_ordered up k p xs ys _ _ hlen hk hp h hg

lemma erase_monotone (n : ℕ) (pre post : List Gate) (g : Gate) (p out : ℕ)
    (hmono : Monotone2 (Circuit.mk (pre ++ g :: post) out)) :
    Monotone2 (AliasPruning.erase n pre post p out) := by
  intro q hq
  change q ∈ pre ++ post.map (AliasPruning.renamed (n + pre.length) p) at hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hmono q (List.mem_append_left _ hq)
  · obtain ⟨q0, hq0, rfl⟩ := List.mem_map.mp hq
    simpa [AliasPruning.renamed] using
      hmono q0 (List.mem_append_right _ (List.mem_cons_of_mem _ hq0))

lemma erase_ordered (up : Bool) (n : ℕ) (pre post : List Gate) (g : Gate) (p out : ℕ)
    (hp : p < n + pre.length)
    (hmono : Monotone2 (Circuit.mk (pre ++ g :: post) out))
    (x : Fin n → Bool)
    (hlocal : ordered up ((Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD p false)
      (LivePruning.gateValue g (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)))) :
    ordered up ((AliasPruning.erase n pre post p out).eval (List.ofFn x))
      ((Circuit.mk (pre ++ g :: post) out).eval (List.ofFn x)) := by
  let xs := Circuit.wires ⟨pre, 0⟩ (List.ofFn x)
  have hx : xs.length = n + pre.length := by
    simp [xs, LivePruning.wires_length]
  simp only [AliasPruning.erase, Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons]
  change ordered up
    ((Circuit.wires ⟨post.map (AliasPruning.renamed (n + pre.length) p), 0⟩ xs).getD
      (AliasPruning.redirect (n + pre.length) p out) false)
    ((Circuit.wires ⟨post, 0⟩ (xs ++ [LivePruning.gateValue g xs])).getD out false)
  apply wires_ordered up _ _ _ _ _ (by simp) (by simp [hx]) hp _ _ out
  · intro q hq
    exact (hmono q (List.mem_append_right _ (List.mem_cons_of_mem _ hq))).1
  · rw [← hx]
    exact initial_ordered up xs p _ hlocal

def CompleteBoundary (n : ℕ) (f : (Fin n → Bool) → Bool)
    (positive negative : List (Fin n → Bool)) : Prop :=
  ∀ D : Circuit, Monotone2 D →
    (∀ x ∈ positive, D.eval (List.ofFn x) = true) →
    (∀ x ∈ negative, D.eval (List.ofFn x) = false) →
    ∀ x : Fin n → Bool, D.eval (List.ofFn x) = f x

lemma boundary_alias_failure (up : Bool) (n : ℕ) (f : (Fin n → Bool) → Bool)
    (positive negative : List (Fin n → Bool)) (pre post : List Gate) (g : Gate) (p out : ℕ)
    (hp : p < n + pre.length)
    (hmono : Monotone2 (Circuit.mk (pre ++ g :: post) out))
    (hev : ∀ x : Fin n → Bool, (Circuit.mk (pre ++ g :: post) out).eval (List.ofFn x) = f x)
    (hmin : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = f x) →
      (Circuit.mk (pre ++ g :: post) out).size ≤ D.size)
    (hpos : ∀ x ∈ positive, f x = true) (hneg : ∀ x ∈ negative, f x = false)
    (hcomplete : CompleteBoundary n f positive negative)
    (horder : ∀ x : Fin n → Bool,
      ordered up ((AliasPruning.erase n pre post p out).eval (List.ofFn x))
        ((Circuit.mk (pre ++ g :: post) out).eval (List.ofFn x))) :
    ∃ x ∈ (if up then negative else positive),
      ((Circuit.mk (pre ++ g :: post) out).wires (List.ofFn x)).getD (n + pre.length) false ≠
        ((Circuit.mk (pre ++ g :: post) out).wires (List.ofFn x)).getD p false := by
  classical
  by_contra hn
  have hcopy (x : Fin n → Bool) (hx : x ∈ (if up then negative else positive)) :
      ((Circuit.mk (pre ++ g :: post) out).wires (List.ofFn x)).getD (n + pre.length) false =
        ((Circuit.mk (pre ++ g :: post) out).wires (List.ofFn x)).getD p false := by
    by_contra he
    exact hn ⟨x, hx, he⟩
  have hexact (x : Fin n → Bool) (hx : x ∈ (if up then negative else positive)) :
      (AliasPruning.erase n pre post p out).eval (List.ofFn x) =
        (Circuit.mk (pre ++ g :: post) out).eval (List.ofFn x) :=
    ResidualFirstAnd.alias_erase_eval_at n pre post g p out hp x (hcopy x hx)
  have hDmono := erase_monotone n pre post g p out hmono
  have hDpos : ∀ x ∈ positive, (AliasPruning.erase n pre post p out).eval (List.ofFn x) = true := by
    intro x hx
    cases hu : up with
    | false => rw [hexact x (by simpa [hu] using hx), hev, hpos x hx]
    | true =>
      have ho := horder x
      change (if up then _ else _) at ho
      simp only [hu, ite_true] at ho
      rw [hev, hpos x hx] at ho
      exact Bool.eq_true_of_true_le ho
  have hDneg : ∀ x ∈ negative, (AliasPruning.erase n pre post p out).eval (List.ofFn x) = false := by
    intro x hx
    cases hu : up with
    | false =>
      have ho := horder x
      change (if up then _ else _) at ho
      simp only [hu, Bool.false_eq_true, ite_false] at ho
      rw [hev, hneg x hx] at ho
      exact Bool.eq_false_of_le_false ho
    | true => rw [hexact x (by simpa [hu] using hx), hev, hneg x hx]
  have hD := hcomplete (AliasPruning.erase n pre post p out) hDmono hDpos hDneg
  have hm := hmin (AliasPruning.erase n pre post p out) hDmono hD
  have hs := AliasPruning.erase_size n pre post g p out
  omega

lemma and_left_order : ∀ a b : Bool, ordered true a (a && b) := by unfold ordered; decide +kernel
lemma and_right_order : ∀ a b : Bool, ordered true b (a && b) := by unfold ordered; decide +kernel
lemma or_left_order : ∀ a b : Bool, ordered false a (a || b) := by unfold ordered; decide +kernel
lemma or_right_order : ∀ a b : Bool, ordered false b (a || b) := by unfold ordered; decide +kernel

lemma and_ne_left : ∀ a b : Bool, (a && b) ≠ a → a = true ∧ b = false := by decide +kernel
lemma and_ne_right : ∀ a b : Bool, (a && b) ≠ b → a = false ∧ b = true := by decide +kernel
lemma or_ne_left : ∀ a b : Bool, (a || b) ≠ a → a = false ∧ b = true := by decide +kernel
lemma or_ne_right : ∀ a b : Bool, (a || b) ≠ b → a = true ∧ b = false := by decide +kernel

abbrev wireValue {n : ℕ} (C : Circuit) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD i false

lemma minimum_and_negative_incomparable (n : ℕ) (f : (Fin n → Bool) → Bool)
    (positive negative : List (Fin n → Bool)) (C : Circuit)
    (pre post : List Gate) (p q : ℕ)
    (hp : p < n + pre.length) (hq : q < n + pre.length)
    (hgs : C.gates = pre ++ ⟨GateOp.and, [p, q]⟩ :: post)
    (hmono : Monotone2 C)
    (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hmin : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = f x) → C.size ≤ D.size)
    (hpos : ∀ x ∈ positive, f x = true) (hneg : ∀ x ∈ negative, f x = false)
    (hcomplete : CompleteBoundary n f positive negative) :
    (∃ x ∈ negative, wireValue C x p = true ∧ wireValue C x q = false) ∧
    (∃ x ∈ negative, wireValue C x p = false ∧ wireValue C x q = true) := by
  rcases C with ⟨gs, out⟩
  change gs = _ at hgs
  subst gs
  let C : Circuit := ⟨pre ++ ⟨GateOp.and, [p, q]⟩ :: post, out⟩
  have hvalue (x : Fin n → Bool) :
      wireValue C x (n + pre.length) = (wireValue C x p && wireValue C x q) := by
    have he := FirstAndClassification.full_gate_value n C pre post
      ⟨GateOp.and, [p, q]⟩ rfl (by
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact hp
        · exact hq) x
    simpa [wireValue, GateOp.eval] using he
  have hl := boundary_alias_failure true n f positive negative pre post
    ⟨GateOp.and, [p, q]⟩ p out hp hmono hev hmin hpos hneg hcomplete (by
      intro x
      apply erase_ordered true n pre post _ p out hp hmono x
      simpa [LivePruning.gateValue, GateOp.eval] using
        and_left_order ((Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD p false)
          ((Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD q false))
  have hr := boundary_alias_failure true n f positive negative pre post
    ⟨GateOp.and, [p, q]⟩ q out hq hmono hev hmin hpos hneg hcomplete (by
      intro x
      apply erase_ordered true n pre post _ q out hq hmono x
      simpa [LivePruning.gateValue, GateOp.eval] using
        and_right_order ((Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD p false)
          ((Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD q false))
  constructor
  · obtain ⟨x, hx, hne⟩ := hl
    change wireValue C x (n + pre.length) ≠ wireValue C x p at hne
    rw [hvalue x] at hne
    exact ⟨x, hx, and_ne_left _ _ hne⟩
  · obtain ⟨x, hx, hne⟩ := hr
    change wireValue C x (n + pre.length) ≠ wireValue C x q at hne
    rw [hvalue x] at hne
    exact ⟨x, hx, and_ne_right _ _ hne⟩

lemma minimum_or_positive_incomparable (n : ℕ) (f : (Fin n → Bool) → Bool)
    (positive negative : List (Fin n → Bool)) (C : Circuit)
    (pre post : List Gate) (p q : ℕ)
    (hp : p < n + pre.length) (hq : q < n + pre.length)
    (hgs : C.gates = pre ++ ⟨GateOp.or, [p, q]⟩ :: post)
    (hmono : Monotone2 C)
    (hev : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x)
    (hmin : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = f x) → C.size ≤ D.size)
    (hpos : ∀ x ∈ positive, f x = true) (hneg : ∀ x ∈ negative, f x = false)
    (hcomplete : CompleteBoundary n f positive negative) :
    (∃ x ∈ positive, wireValue C x p = true ∧ wireValue C x q = false) ∧
    (∃ x ∈ positive, wireValue C x p = false ∧ wireValue C x q = true) := by
  rcases C with ⟨gs, out⟩
  change gs = _ at hgs
  subst gs
  let C : Circuit := ⟨pre ++ ⟨GateOp.or, [p, q]⟩ :: post, out⟩
  have hvalue (x : Fin n → Bool) :
      wireValue C x (n + pre.length) = (wireValue C x p || wireValue C x q) := by
    have he := FirstAndClassification.full_gate_value n C pre post
      ⟨GateOp.or, [p, q]⟩ rfl (by
        intro i hi
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · exact hp
        · exact hq) x
    simpa [wireValue, GateOp.eval] using he
  have hl := boundary_alias_failure false n f positive negative pre post
    ⟨GateOp.or, [p, q]⟩ p out hp hmono hev hmin hpos hneg hcomplete (by
      intro x
      apply erase_ordered false n pre post _ p out hp hmono x
      simpa [LivePruning.gateValue, GateOp.eval] using
        or_left_order ((Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD p false)
          ((Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD q false))
  have hr := boundary_alias_failure false n f positive negative pre post
    ⟨GateOp.or, [p, q]⟩ q out hq hmono hev hmin hpos hneg hcomplete (by
      intro x
      apply erase_ordered false n pre post _ q out hq hmono x
      simpa [LivePruning.gateValue, GateOp.eval] using
        or_right_order ((Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD p false)
          ((Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD q false))
  constructor
  · obtain ⟨x, hx, hne⟩ := hr
    change wireValue C x (n + pre.length) ≠ wireValue C x q at hne
    rw [hvalue x] at hne
    exact ⟨x, hx, or_ne_right _ _ hne⟩
  · obtain ⟨x, hx, hne⟩ := hl
    change wireValue C x (n + pre.length) ≠ wireValue C x p at hne
    rw [hvalue x] at hne
    exact ⟨x, hx, or_ne_left _ _ hne⟩

end BoundaryOperands

namespace BoundaryOperands

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma erase_ordered_of_full_wires (up : Bool) (n : Nat)
    (pre post : List Gate) (g : Gate) (p out : Nat)
    (hp : p < n + pre.length)
    (hmono : Monotone2 (Circuit.mk (pre ++ g :: post) out))
    (x : Fin n → Bool)
    (horder : ordered up
      (wireValue (Circuit.mk (pre ++ g :: post) out) x p)
      (wireValue (Circuit.mk (pre ++ g :: post) out) x (n + pre.length))) :
    ordered up ((AliasPruning.erase n pre post p out).eval (List.ofFn x))
      ((Circuit.mk (pre ++ g :: post) out).eval (List.ofFn x)) := by
  apply erase_ordered up n pre post g p out hp hmono x
  have hpv := Restriction.getD_wiresFrom (g :: post)
    (Restriction.wiresFrom pre (List.ofFn x)) p
    (by simpa [Restriction.length_wiresFrom] using hp)
  have hgv := positive_gate_output_value pre post g (List.ofFn x)
  have hpv' : wireValue (Circuit.mk (pre ++ g :: post) out) x p =
      (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)).getD p false := by
    simpa only [wireValue, Circuit.wires, Restriction.wiresFrom, List.foldl_append] using hpv
  have hgv' : wireValue (Circuit.mk (pre ++ g :: post) out) x (n + pre.length) =
      LivePruning.gateValue g (Circuit.wires ⟨pre, 0⟩ (List.ofFn x)) := by
    simpa only [wireValue, Circuit.wires, Restriction.wiresFrom, List.length_ofFn,
      LivePruning.gateValue] using hgv
  rwa [hpv', hgv'] at horder

lemma minimum_no_boundary_dominator (n : Nat) (f : (Fin n → Bool) → Bool)
    (positive negative : List (Fin n → Bool)) (pre post : List Gate)
    (g : Gate) (p out : Nat) (hp : p < n + pre.length)
    (hmono : Monotone2 (Circuit.mk (pre ++ g :: post) out))
    (hev : ∀ x : Fin n → Bool, (Circuit.mk (pre ++ g :: post) out).eval (List.ofFn x) = f x)
    (hmin : ∀ D : Circuit, Monotone2 D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = f x) →
      (Circuit.mk (pre ++ g :: post) out).size ≤ D.size)
    (hpos : ∀ x ∈ positive, f x = true)
    (hneg : ∀ x ∈ negative, f x = false)
    (hcomplete : CompleteBoundary n f positive negative) :
    (∃ x ∈ positive,
      wireValue (Circuit.mk (pre ++ g :: post) out) x (n + pre.length) = true ∧
      wireValue (Circuit.mk (pre ++ g :: post) out) x p = false) ∨
    (∃ x ∈ negative,
      wireValue (Circuit.mk (pre ++ g :: post) out) x p = true ∧
      wireValue (Circuit.mk (pre ++ g :: post) out) x (n + pre.length) = false) := by
  classical
  by_contra hn
  have hDmono := erase_monotone n pre post g p out hmono
  have hDpos : ∀ x ∈ positive, (AliasPruning.erase n pre post p out).eval (List.ofFn x) = true := by
    intro x hx
    have hw : wireValue (Circuit.mk (pre ++ g :: post) out) x (n + pre.length) ≤
        wireValue (Circuit.mk (pre ++ g :: post) out) x p := by
      cases hz : wireValue (Circuit.mk (pre ++ g :: post) out) x (n + pre.length) <;>
        cases hpv : wireValue (Circuit.mk (pre ++ g :: post) out) x p <;> simp_all
    have ho := erase_ordered_of_full_wires true n pre post g p out hp hmono x hw
    change (Circuit.mk (pre ++ g :: post) out).eval (List.ofFn x) ≤ _ at ho
    rw [hev, hpos x hx] at ho
    exact Bool.eq_true_of_true_le ho
  have hDneg : ∀ x ∈ negative, (AliasPruning.erase n pre post p out).eval (List.ofFn x) = false := by
    intro x hx
    have hw : wireValue (Circuit.mk (pre ++ g :: post) out) x p ≤
        wireValue (Circuit.mk (pre ++ g :: post) out) x (n + pre.length) := by
      cases hpv : wireValue (Circuit.mk (pre ++ g :: post) out) x p <;>
        cases hz : wireValue (Circuit.mk (pre ++ g :: post) out) x (n + pre.length) <;> simp_all
    have ho := erase_ordered_of_full_wires false n pre post g p out hp hmono x hw
    change (AliasPruning.erase n pre post p out).eval (List.ofFn x) ≤ _ at ho
    rw [hev, hneg x hx] at ho
    exact Bool.eq_false_of_le_false ho
  have he := hcomplete (AliasPruning.erase n pre post p out) hDmono hDpos hDneg
  have hm := hmin (AliasPruning.erase n pre post p out) hDmono he
  have hs := AliasPruning.erase_size n pre post g p out
  omega

end BoundaryOperands

namespace EarlierGuardBlockers

set_option maxHeartbeats 4000000 in
lemma endpoint0_independent_extension : ∀ y : Fin 10 → Bool,
    y 0 = false → y 1 = false → petersen y = false →
    ((y 3 && y 7) || (y 8 && y 9)) = false →
    ∃ t : Fin 10, (t = 4 ∨ t = 5) ∧
      petersen (partnerRaise t y) = false ∧
      petersen (partnerRaise 0 (partnerRaise t y)) = true := by
  decide +kernel

lemma monotone_endpoint0_guard_blockers (H : (Fin 10 → Bool) → Bool)
    (hmono : Monotone H)
    (hmask : ∀ x : Fin 10 → Bool, petersen x = false →
      H x = H (partnerClear01 x))
    (hflip0 : ∀ y : Fin 10 → Bool, y 0 = false → y 1 = false → H y = true →
      petersen (partnerRaise 0 y) = petersen y) :
    ∀ x : Fin 10 → Bool, H x = true → petersen x = false →
      ((x 3 && x 7) || (x 8 && x 9)) = true := by
  intro x hx hf
  cases hb : ((x 3 && x 7) || (x 8 && x 9)) with
  | true => rfl
  | false =>
    let y := partnerClear01 x
    have hy : H y = true := by simpa [y, ← hmask x hf] using hx
    have hy0 : y 0 = false := by simp [y, partnerClear01]
    have hy1 : y 1 = false := by simp [y, partnerClear01]
    have hyf : petersen y = false := partner_clear_independent x hf
    have hyb : ((y 3 && y 7) || (y 8 && y 9)) = false := by
      simpa [y, partnerClear01] using hb
    obtain ⟨t, ht, hzf, hzpositive⟩ := endpoint0_independent_extension y hy0 hy1 hyf hyb
    have ht0 : t ≠ 0 := by rcases ht with rfl | rfl <;> decide
    have ht1 : t ≠ 1 := by rcases ht with rfl | rfl <;> decide
    have hle : y ≤ partnerRaise t y := by
      intro i
      by_cases hi : i = t <;> simp [partnerRaise, hi]
    have hz : H (partnerRaise t y) = true := by
      have hh := hmono hle
      apply Bool.eq_true_of_true_le
      simpa [hy] using hh
    have hz0 : partnerRaise t y 0 = false := by
      simp [partnerRaise, Ne.symm ht0, hy0]
    have hz1 : partnerRaise t y 1 = false := by
      simp [partnerRaise, Ne.symm ht1, hy1]
    have hsame := hflip0 (partnerRaise t y) hz0 hz1 hz
    rw [hzpositive, hzf] at hsame
    exact False.elim (Bool.false_ne_true hsame.symm)

set_option maxHeartbeats 4000000 in
lemma endpoint0_blocker_rows_below_maxima : ∀ y : Fin 10 → Bool,
    y 0 = false → y 1 = false → petersen y = false →
    ((y 3 && y 7) || (y 8 && y 9)) = true →
    y ≤ (fun i => decide (i = 3 ∨ i = 6 ∨ i = 7)) ∨
      y ≤ (fun i => decide (i = 2 ∨ i = 8 ∨ i = 9)) := by
  decide +kernel

lemma endpoint0_maximal_rows_negative :
    petersen (fun i => decide (i = 3 ∨ i = 6 ∨ i = 7)) = false ∧
      petersen (fun i => decide (i = 2 ∨ i = 8 ∨ i = 9)) = false := by
  decide +kernel

lemma monotone_endpoint0_unsafe_fixed_row (H : (Fin 10 → Bool) → Bool)
    (hmono : Monotone H)
    (hmask : ∀ x : Fin 10 → Bool, petersen x = false →
      H x = H (partnerClear01 x))
    (hflip0 : ∀ y : Fin 10 → Bool, y 0 = false → y 1 = false → H y = true →
      petersen (partnerRaise 0 y) = petersen y)
    (hunsafe : ∃ x : Fin 10 → Bool, H x = true ∧ petersen x = false) :
    H (fun i => decide (i = 3 ∨ i = 6 ∨ i = 7)) = true ∨
      H (fun i => decide (i = 2 ∨ i = 8 ∨ i = 9)) = true := by
  obtain ⟨x, hx, hf⟩ := hunsafe
  let y := partnerClear01 x
  have hy : H y = true := by simpa [y, ← hmask x hf] using hx
  have hy0 : y 0 = false := by simp [y, partnerClear01]
  have hy1 : y 1 = false := by simp [y, partnerClear01]
  have hyf : petersen y = false := partner_clear_independent x hf
  have hyb := monotone_endpoint0_guard_blockers H hmono hmask hflip0 y hy hyf
  rcases endpoint0_blocker_rows_below_maxima y hy0 hy1 hyf hyb with hle | hle
  · left
    apply Bool.eq_true_of_true_le
    simpa [hy] using hmono hle
  · right
    apply Bool.eq_true_of_true_le
    simpa [hy] using hmono hle

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

set_option maxHeartbeats 4000000 in
lemma endpoint1_independent_extension : ∀ y : Fin 10 → Bool,
    y 0 = false → y 1 = false → petersen y = false →
    ((y 3 && y 9) || (y 7 && y 8)) = false →
    ∃ t : Fin 10, (t = 2 ∨ t = 6) ∧
      petersen (partnerRaise t y) = false ∧
      petersen (partnerRaise 1 (partnerRaise t y)) = true := by
  decide +kernel

lemma monotone_endpoint1_blockers (H : (Fin 10 → Bool) → Bool)
    (hmono : Monotone H)
    (hmask : ∀ x : Fin 10 → Bool, petersen x = false →
      H x = H (partnerClear01 x))
    (hflip : ∀ y : Fin 10 → Bool, y 0 = false → y 1 = false → H y = true →
      petersen (partnerRaise 1 y) = petersen y) :
    ∀ x : Fin 10 → Bool, H x = true → petersen x = false →
      ((x 3 && x 9) || (x 7 && x 8)) = true := by
  intro x hx hxf
  cases hb : ((x 3 && x 9) || (x 7 && x 8)) with
  | true => rfl
  | false =>
    let y := partnerClear01 x
    have hy : H y = true := by simpa [y, ← hmask x hxf] using hx
    have hy0 : y 0 = false := by simp [y, partnerClear01]
    have hy1 : y 1 = false := by simp [y, partnerClear01]
    have hyf : petersen y = false := partner_clear_independent x hxf
    have hyb : ((y 3 && y 9) || (y 7 && y 8)) = false := by
      simpa [y, partnerClear01] using hb
    obtain ⟨t, ht, hzf, hpos⟩ := endpoint1_independent_extension y hy0 hy1 hyf hyb
    have hle : y ≤ partnerRaise t y := by
      intro i
      by_cases hi : i = t <;> simp [partnerRaise, hi]
    have hz : H (partnerRaise t y) = true := by
      have hh := hmono hle
      apply Bool.eq_true_of_true_le
      simpa [hy] using hh
    have hz0 : partnerRaise t y 0 = false := by
      rcases ht with rfl | rfl <;> simp [partnerRaise, hy0]
    have hz1 : partnerRaise t y 1 = false := by
      rcases ht with rfl | rfl <;> simp [partnerRaise, hy1]
    have he := hflip (partnerRaise t y) hz0 hz1 hz
    rw [hpos, hzf] at he
    contradiction

lemma circuit_endpoint0_blockers
    (pre post : List Gate) (out h : ℕ) (hh : 10 ≤ h) (hupper : h < 10 + pre.length)
    (hpre : ∀ g ∈ pre, 0 ∈ effectiveInputs g ∨ 1 ∈ effectiveInputs g →
      partnerAndReadShape 0 1 g)
    (hpost : ∀ g ∈ post, 0 ∈ effectiveInputs g → maskedReadShape 0 1 h g)
    (hev : ∀ x : Fin 10 → Bool,
      ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) = petersen x)
    (hmono : Monotone (commonPartnerValue pre h)) :
    ∀ x : Fin 10 → Bool, commonPartnerValue pre h x = true → petersen x = false →
      ((x 3 && x 7) || (x 8 && x 9)) = true := by
  apply monotone_endpoint0_guard_blockers (commonPartnerValue pre h) hmono
    (common_partner_clear_mask pre h hh hpre)
  intro y hy0 hy1 hy
  apply partner_endpoint_flip_of_read_masks 0 1 (by decide)
    pre post out h hh hupper _ hpost hev y hy1 hy
  intro g hg hr
  rcases hpre g hg (Or.inl hr) with rfl | rfl <;> simp [uniformReadShape]

lemma circuit_endpoint1_blockers
    (pre post : List Gate) (out h : ℕ) (hh : 10 ≤ h) (hupper : h < 10 + pre.length)
    (hpre : ∀ g ∈ pre, 0 ∈ effectiveInputs g ∨ 1 ∈ effectiveInputs g →
      partnerAndReadShape 0 1 g)
    (hpost : ∀ g ∈ post, 1 ∈ effectiveInputs g → maskedReadShape 1 0 h g)
    (hev : ∀ x : Fin 10 → Bool,
      ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) = petersen x)
    (hmono : Monotone (commonPartnerValue pre h)) :
    ∀ x : Fin 10 → Bool, commonPartnerValue pre h x = true → petersen x = false →
      ((x 3 && x 9) || (x 7 && x 8)) = true := by
  apply monotone_endpoint1_blockers (commonPartnerValue pre h) hmono
    (common_partner_clear_mask pre h hh hpre)
  intro y hy0 hy1 hy
  apply partner_endpoint_flip_of_read_masks 1 0 (by decide)
    pre post out h hh hupper _ hpost hev y hy0 hy
  intro g hg hr
  rcases hpre g hg (Or.inr hr) with rfl | rfl <;> simp [uniformReadShape]


lemma monotone_endpoint0_unsafe_fixed_row_iff (H : (Fin 10 → Bool) → Bool)
    (hmono : Monotone H)
    (hmask : ∀ x : Fin 10 → Bool, petersen x = false →
      H x = H (partnerClear01 x))
    (hflip0 : ∀ y : Fin 10 → Bool, y 0 = false → y 1 = false → H y = true →
      petersen (partnerRaise 0 y) = petersen y) :
    (∃ x : Fin 10 → Bool, H x = true ∧ petersen x = false) ↔
      H (fun i => decide (i = 3 ∨ i = 6 ∨ i = 7)) = true ∨
        H (fun i => decide (i = 2 ∨ i = 8 ∨ i = 9)) = true := by
  constructor
  · exact monotone_endpoint0_unsafe_fixed_row H hmono hmask hflip0
  · intro hrows
    rcases hrows with hrow | hrow
    · exact ⟨_, hrow, endpoint0_maximal_rows_negative.1⟩
    · exact ⟨_, hrow, endpoint0_maximal_rows_negative.2⟩

lemma monotone_endpoint0_guard_singleton_false (H : (Fin 10 → Bool) → Bool)
    (hmono : Monotone H)
    (hmask : ∀ x : Fin 10 → Bool, petersen x = false →
      H x = H (partnerClear01 x))
    (hflip0 : ∀ y : Fin 10 → Bool, y 0 = false → y 1 = false → H y = true →
      petersen (partnerRaise 0 y) = petersen y) :
    ∀ a : Fin 10, H (fun i => decide (i = a)) = false := by
  intro a
  cases he : H (fun i => decide (i = a)) with
  | false => rfl
  | true =>
    have hb := monotone_endpoint0_guard_blockers H hmono hmask hflip0
      (fun i => decide (i = a)) he (petersen_singleton_false a)
    have hsingle : ∀ a : Fin 10,
        ((decide ((3 : Fin 10) = a) && decide ((7 : Fin 10) = a)) ||
          (decide ((8 : Fin 10) = a) && decide ((9 : Fin 10) = a))) = false := by
      decide +kernel
    rw [hsingle a] at hb
    exact False.elim (Bool.false_ne_true hb)

lemma circuit_endpoint0_unsafe_fixed_row_iff
    (pre post : List Gate) (out h : ℕ) (hh : 10 ≤ h) (hupper : h < 10 + pre.length)
    (hpre : ∀ g ∈ pre, 0 ∈ effectiveInputs g ∨ 1 ∈ effectiveInputs g →
      partnerAndReadShape 0 1 g)
    (hpost : ∀ g ∈ post, 0 ∈ effectiveInputs g → maskedReadShape 0 1 h g)
    (hev : ∀ x : Fin 10 → Bool,
      ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) = petersen x)
    (hmono : Monotone (commonPartnerValue pre h)) :
    (∃ x : Fin 10 → Bool, commonPartnerValue pre h x = true ∧ petersen x = false) ↔
      commonPartnerValue pre h (fun i => decide (i = 3 ∨ i = 6 ∨ i = 7)) = true ∨
        commonPartnerValue pre h (fun i => decide (i = 2 ∨ i = 8 ∨ i = 9)) = true := by
  apply monotone_endpoint0_unsafe_fixed_row_iff (commonPartnerValue pre h) hmono
    (common_partner_clear_mask pre h hh hpre)
  intro y hy0 hy1 hy
  apply partner_endpoint_flip_of_read_masks 0 1 (by decide)
    pre post out h hh hupper _ hpost hev y hy1 hy
  intro g hg hr
  rcases hpre g hg (Or.inl hr) with rfl | rfl <;> simp [uniformReadShape]

lemma circuit_endpoint0_guard_singleton_false
    (pre post : List Gate) (out h : ℕ) (hh : 10 ≤ h) (hupper : h < 10 + pre.length)
    (hpre : ∀ g ∈ pre, 0 ∈ effectiveInputs g ∨ 1 ∈ effectiveInputs g →
      partnerAndReadShape 0 1 g)
    (hpost : ∀ g ∈ post, 0 ∈ effectiveInputs g → maskedReadShape 0 1 h g)
    (hev : ∀ x : Fin 10 → Bool,
      ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) = petersen x)
    (hmono : Monotone (commonPartnerValue pre h)) :
    ∀ a : Fin 10, commonPartnerValue pre h (fun i => decide (i = a)) = false := by
  apply monotone_endpoint0_guard_singleton_false (commonPartnerValue pre h) hmono
    (common_partner_clear_mask pre h hh hpre)
  intro y hy0 hy1 hy
  apply partner_endpoint_flip_of_read_masks 0 1 (by decide)
    pre post out h hh hupper _ hpost hev y hy1 hy
  intro g hg hr
  rcases hpre g hg (Or.inl hr) with rfl | rfl <;> simp [uniformReadShape]

set_option maxHeartbeats 4000000 in
lemma endpoint1_blocker_rows_below_maxima : ∀ y : Fin 10 → Bool,
    y 0 = false → y 1 = false → petersen y = false →
    ((y 3 && y 9) || (y 7 && y 8)) = true →
    y ≤ (fun i => decide (i = 3 ∨ i = 5 ∨ i = 9)) ∨
      y ≤ (fun i => decide (i = 4 ∨ i = 7 ∨ i = 8)) := by
  decide +kernel

lemma endpoint1_maximal_rows_negative :
    petersen (fun i => decide (i = 3 ∨ i = 5 ∨ i = 9)) = false ∧
      petersen (fun i => decide (i = 4 ∨ i = 7 ∨ i = 8)) = false := by
  decide +kernel

lemma monotone_endpoint1_unsafe_fixed_row (H : (Fin 10 → Bool) → Bool)
    (hmono : Monotone H)
    (hmask : ∀ x : Fin 10 → Bool, petersen x = false →
      H x = H (partnerClear01 x))
    (hflip1 : ∀ y : Fin 10 → Bool, y 0 = false → y 1 = false → H y = true →
      petersen (partnerRaise 1 y) = petersen y)
    (hunsafe : ∃ x : Fin 10 → Bool, H x = true ∧ petersen x = false) :
    H (fun i => decide (i = 3 ∨ i = 5 ∨ i = 9)) = true ∨
      H (fun i => decide (i = 4 ∨ i = 7 ∨ i = 8)) = true := by
  obtain ⟨x, hx, hf⟩ := hunsafe
  let y := partnerClear01 x
  have hy : H y = true := by simpa [y, ← hmask x hf] using hx
  have hy0 : y 0 = false := by simp [y, partnerClear01]
  have hy1 : y 1 = false := by simp [y, partnerClear01]
  have hyf : petersen y = false := partner_clear_independent x hf
  have hyb := monotone_endpoint1_blockers H hmono hmask hflip1 y hy hyf
  rcases endpoint1_blocker_rows_below_maxima y hy0 hy1 hyf hyb with hle | hle
  · left
    apply Bool.eq_true_of_true_le
    simpa [hy] using hmono hle
  · right
    apply Bool.eq_true_of_true_le
    simpa [hy] using hmono hle

lemma monotone_endpoint1_unsafe_fixed_row_iff (H : (Fin 10 → Bool) → Bool)
    (hmono : Monotone H)
    (hmask : ∀ x : Fin 10 → Bool, petersen x = false →
      H x = H (partnerClear01 x))
    (hflip1 : ∀ y : Fin 10 → Bool, y 0 = false → y 1 = false → H y = true →
      petersen (partnerRaise 1 y) = petersen y) :
    (∃ x : Fin 10 → Bool, H x = true ∧ petersen x = false) ↔
      (H (fun i => decide (i = 3 ∨ i = 5 ∨ i = 9)) = true ∨
        H (fun i => decide (i = 4 ∨ i = 7 ∨ i = 8)) = true) := by
  constructor
  · exact monotone_endpoint1_unsafe_fixed_row H hmono hmask hflip1
  · intro h
    rcases h with h | h
    · exact ⟨_, h, endpoint1_maximal_rows_negative.1⟩
    · exact ⟨_, h, endpoint1_maximal_rows_negative.2⟩

lemma endpoint1_singleton_negative_unblocked : ∀ v : Fin 10,
    petersen (fun i => decide (i = v)) = false ∧
      (((fun i : Fin 10 => decide (i = v)) 3 && (fun i : Fin 10 => decide (i = v)) 9) ||
        ((fun i : Fin 10 => decide (i = v)) 7 && (fun i : Fin 10 => decide (i = v)) 8)) = false := by
  decide +kernel

lemma monotone_endpoint1_singleton_false (H : (Fin 10 → Bool) → Bool)
    (hmono : Monotone H)
    (hmask : ∀ x : Fin 10 → Bool, petersen x = false →
      H x = H (partnerClear01 x))
    (hflip1 : ∀ y : Fin 10 → Bool, y 0 = false → y 1 = false → H y = true →
      petersen (partnerRaise 1 y) = petersen y) :
    ∀ v : Fin 10, H (fun i => decide (i = v)) = false := by
  intro v
  cases hh : H (fun i => decide (i = v)) with
  | false => rfl
  | true =>
    have hb := monotone_endpoint1_blockers H hmono hmask hflip1
      (fun i => decide (i = v)) hh (endpoint1_singleton_negative_unblocked v).1
    rw [(endpoint1_singleton_negative_unblocked v).2] at hb
    exact False.elim (Bool.false_ne_true hb)

lemma circuit_endpoint1_unsafe_fixed_row_iff
    (pre post : List Gate) (out h : ℕ) (hh : 10 ≤ h) (hupper : h < 10 + pre.length)
    (hpre : ∀ g ∈ pre, 0 ∈ effectiveInputs g ∨ 1 ∈ effectiveInputs g →
      partnerAndReadShape 0 1 g)
    (hpost : ∀ g ∈ post, 1 ∈ effectiveInputs g → maskedReadShape 1 0 h g)
    (hev : ∀ x : Fin 10 → Bool,
      ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) = petersen x)
    (hmono : Monotone (commonPartnerValue pre h)) :
    (∃ x : Fin 10 → Bool, commonPartnerValue pre h x = true ∧ petersen x = false) ↔
      (commonPartnerValue pre h (fun i => decide (i = 3 ∨ i = 5 ∨ i = 9)) = true ∨
        commonPartnerValue pre h (fun i => decide (i = 4 ∨ i = 7 ∨ i = 8)) = true) := by
  apply monotone_endpoint1_unsafe_fixed_row_iff (commonPartnerValue pre h) hmono
    (common_partner_clear_mask pre h hh hpre)
  intro y hy0 hy1 hy
  apply partner_endpoint_flip_of_read_masks 1 0 (by decide)
    pre post out h hh hupper _ hpost hev y hy0 hy
  intro g hg hr
  rcases hpre g hg (Or.inr hr) with rfl | rfl <;> simp [uniformReadShape]

lemma circuit_endpoint1_guard_singleton_false
    (pre post : List Gate) (out h : ℕ) (hh : 10 ≤ h) (hupper : h < 10 + pre.length)
    (hpre : ∀ g ∈ pre, 0 ∈ effectiveInputs g ∨ 1 ∈ effectiveInputs g →
      partnerAndReadShape 0 1 g)
    (hpost : ∀ g ∈ post, 1 ∈ effectiveInputs g → maskedReadShape 1 0 h g)
    (hev : ∀ x : Fin 10 → Bool,
      ({gates := pre ++ post, output := out} : Circuit).eval (List.ofFn x) = petersen x)
    (hmono : Monotone (commonPartnerValue pre h)) :
    ∀ a : Fin 10, commonPartnerValue pre h (fun i => decide (i = a)) = false := by
  apply monotone_endpoint1_singleton_false (commonPartnerValue pre h) hmono
    (common_partner_clear_mask pre h hh hpre)
  intro y hy0 hy1 hy
  apply partner_endpoint_flip_of_read_masks 1 0 (by decide)
    pre post out h hh hupper _ hpost hev y hy0 hy
  intro g hg hr
  rcases hpre g hg (Or.inr hr) with rfl | rfl <;> simp [uniformReadShape]


end EarlierGuardBlockers

namespace AliasPruning

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open LivePruning

lemma wires_renamed_true_count (k p : ℕ) (gs : List Gate) (xs ys : List Bool)
    (hlen : xs.length + 1 = ys.length) (hk : k < ys.length) (hp : p < k)
    (heq : ∀ i, xs.getD (redirect k p i) false = ys.getD i false)
    (d : ℕ) (hcount : xs.countP id + d = ys.countP id) :
    (Circuit.wires ⟨gs.map (renamed k p), 0⟩ xs).countP id + d =
      (Circuit.wires ⟨gs, 0⟩ ys).countP id := by
  induction gs generalizing xs ys with
  | nil => exact hcount
  | cons g gs ih =>
    have hg := renamed_value k p g xs ys heq
    change (Circuit.wires ⟨gs.map (renamed k p), 0⟩
        (xs ++ [gateValue (renamed k p g) xs])).countP id + d =
      (Circuit.wires ⟨gs, 0⟩ (ys ++ [gateValue g ys])).countP id
    rw [hg]
    apply ih _ _
    · simp only [List.length_append, List.length_singleton]
      omega
    · simp only [List.length_append, List.length_singleton]
      omega
    · exact append_agree k p xs ys _ hlen hk hp heq
    · simp only [List.countP_append]
      omega

lemma alias_erase_true_count_at (n : ℕ) (pre post : List Gate) (g : Gate) (p o : ℕ)
    (hp : p < n + pre.length) (x : Fin n → Bool)
    (hcopy : (Circuit.wires ⟨pre ++ g :: post, o⟩ (List.ofFn x)).getD (n + pre.length) false =
      (Circuit.wires ⟨pre ++ g :: post, o⟩ (List.ofFn x)).getD p false) :
    ((erase n pre post p o).wires (List.ofFn x)).countP id +
      Bool.toNat ((Circuit.wires ⟨pre ++ g :: post, o⟩ (List.ofFn x)).getD (n + pre.length) false) =
      (Circuit.wires ⟨pre ++ g :: post, o⟩ (List.ofFn x)).countP id := by
  let xs := Circuit.wires ⟨pre, 0⟩ (List.ofFn x)
  have hx : xs.length = n + pre.length := by
    unfold xs
    rw [LivePruning.wires_length, List.length_ofFn]
  have hwires : Circuit.wires ⟨pre ++ g :: post, o⟩ (List.ofFn x) =
      Circuit.wires ⟨post, 0⟩ (xs ++ [gateValue g xs]) := by
    simp [Circuit.wires, List.foldl_append, xs, gateValue]
  have hgate : (Circuit.wires ⟨pre ++ g :: post, o⟩ (List.ofFn x)).getD (n + pre.length) false =
      gateValue g xs := by
    rw [hwires, wires_input _ _ _ (by simp [hx])]
    rw [← hx]
    simp
  have hwirep : (Circuit.wires ⟨pre ++ g :: post, o⟩ (List.ofFn x)).getD p false =
      xs.getD p false := by
    rw [hwires, wires_input _ _ _ (by simp [hx]; omega)]
    exact List.getD_append _ _ _ _ (by omega)
  have hcopy' : gateValue g xs = xs.getD p false := by
    rw [hgate, hwirep] at hcopy
    exact hcopy
  have hnew : (erase n pre post p o).wires (List.ofFn x) =
      Circuit.wires ⟨post.map (renamed (n + pre.length) p), 0⟩ xs := by
    simp [erase, Circuit.wires, List.foldl_append, xs]
  rw [hnew, hgate, hwires]
  apply wires_renamed_true_count (n + pre.length) p post xs (xs ++ [gateValue g xs])
  · simp
  · simp [hx]
  · exact hp
  · rw [← hx]
    exact initial_agree xs p _ hcopy'
  · cases gateValue g xs <;> simp [List.countP_append]

end AliasPruning

namespace AliasPruning

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma redirect_lt_after_delete (k p i m : ℕ) (hp : p < k) (hkm : k ≤ m)
    (hi : i < m + 1) : redirect k p i < m := by
  by_cases hik : i = k
  · subst i
    simpa only [redirect, ite_true] using lt_of_lt_of_le hp hkm
  · simp only [redirect, ite_eq_right hik, LivePruning.down]
    split <;> omega

lemma erase_output_bound (n : ℕ) (pre post : List Gate) (g : Gate) (p o : ℕ)
    (hp : p < n + pre.length) (ho : o < n + (pre ++ g :: post).length) :
    (erase n pre post p o).output < n + (erase n pre post p o).gates.length := by
  have hi : o < (n + pre.length + post.length) + 1 := by
    simp only [List.length_append, List.length_cons] at ho
    omega
  have hh := redirect_lt_after_delete (n + pre.length) p o
    (n + pre.length + post.length) hp (by omega) hi
  simpa only [erase, List.length_append, List.length_map, Nat.add_assoc] using hh

lemma erase_monotone (n : ℕ) (pre post : List Gate) (g : Gate) (p o : ℕ)
    (hmono : Monotone2 (Circuit.mk (pre ++ g :: post) o)) :
    Monotone2 (erase n pre post p o) := by
  intro q hq
  change q ∈ pre ++ post.map (renamed (n + pre.length) p) at hq
  rcases List.mem_append.mp hq with hq | hq
  · exact hmono q (by simp [hq])
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hq
    simpa only [renamed, List.length_map] using hmono r (by simp [hr])

lemma erase_strict_back (n : ℕ) (pre post : List Gate) (g : Gate) (p o : ℕ)
    (hp : p < n + pre.length)
    (back : ∀ j q, (pre ++ g :: post)[j]? = some q → ∀ i ∈ q.inputs, i < n + j) :
    ∀ j q, (erase n pre post p o).gates[j]? = some q → ∀ i ∈ q.inputs, i < n + j := by
  intro j q hq
  change (pre ++ post.map (renamed (n + pre.length) p))[j]? = some q at hq
  by_cases hj : j < pre.length
  · have hpre : pre[j]? = some q := by
      rwa [List.getElem?_append_left hj] at hq
    apply back j q
    rw [List.getElem?_append_left hj]
    exact hpre
  · rw [List.getElem?_append_right (by omega), List.getElem?_map] at hq
    cases hr : post[j - pre.length]? with
    | none => simp [hr] at hq
    | some r =>
      have hqr : renamed (n + pre.length) p r = q := by simpa [hr] using hq
      subst q
      intro i hi
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp hi
      apply redirect_lt_after_delete (n + pre.length) p s (n + j) hp (by omega)
      have hsource : (pre ++ g :: post)[j + 1]? = some r := by
        rw [List.getElem?_append_right (by omega)]
        have he : j + 1 - pre.length = (j - pre.length) + 1 := by omega
        rw [he]
        simpa using hr
      have hb := back (j + 1) r hsource s hs
      simpa only [Nat.add_assoc] using hb

end AliasPruning

namespace SingleOrEnergy

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Restriction

def original (pre post : List Gate) (a h out : ℕ) : Circuit :=
  ⟨pre ++ ⟨.or, [a, h]⟩ :: post, out⟩

def lifted (n : ℕ) (pre post : List Gate) (a h out : ℕ) : Circuit :=
  let body := AliasPruning.erase n pre post a out
  ⟨body.gates ++ [⟨.or, [body.output, h]⟩], n + body.size⟩

lemma prefix_value (pre post : List Gate) (out : ℕ) (xs : List Bool) (i : ℕ)
    (hi : i < xs.length + pre.length) :
    ((Circuit.mk (pre ++ post) out).wires xs).getD i false =
      (wiresFrom pre xs).getD i false := by
  change (wiresFrom (pre ++ post) xs).getD i false = _
  rw [wiresFrom_append, getD_wiresFrom _ _ _ (by simpa [length_wiresFrom] using hi)]

lemma original_guard (n : ℕ) (pre post : List Gate) (a h out : ℕ)
    (hh : h < n + pre.length) (x : Fin n → Bool) :
    ((original pre post a h out).wires (List.ofFn x)).getD h false =
      (wiresFrom pre (List.ofFn x)).getD h false := by
  exact prefix_value pre _ out _ h (by simpa using hh)

lemma body_guard (n : ℕ) (pre post : List Gate) (a h out : ℕ)
    (hh : h < n + pre.length) (x : Fin n → Bool) :
    ((AliasPruning.erase n pre post a out).wires (List.ofFn x)).getD h false =
      (wiresFrom pre (List.ofFn x)).getD h false := by
  exact prefix_value pre _ _ _ h (by simpa using hh)

lemma original_gate_value (n : ℕ) (pre post : List Gate) (a h out : ℕ) (x : Fin n → Bool) :
    ((original pre post a h out).wires (List.ofFn x)).getD (n + pre.length) false =
      ((wiresFrom pre (List.ofFn x)).getD a false || (wiresFrom pre (List.ofFn x)).getD h false) := by
  simpa [original, Circuit.wires, wiresFrom, GateOp.eval] using
    positive_gate_output_value pre post ⟨.or, [a, h]⟩ (List.ofFn x)

lemma original_gate_copy (n : ℕ) (pre post : List Gate) (a h out : ℕ)
    (ha : a < n + pre.length) (x : Fin n → Bool)
    (hz : (wiresFrom pre (List.ofFn x)).getD h false = false) :
    ((original pre post a h out).wires (List.ofFn x)).getD (n + pre.length) false =
      ((original pre post a h out).wires (List.ofFn x)).getD a false := by
  rw [original_gate_value, hz, Bool.or_false]
  exact (prefix_value pre _ out _ a (by simpa using ha)).symm

lemma lifted_eval (n : ℕ) (pre post : List Gate) (a h out : ℕ)
    (ha : a < n + pre.length) (hh : h < n + pre.length)
    (hbelow : ∀ x : Fin n → Bool,
      (wiresFrom pre (List.ofFn x)).getD h false = true →
        (original pre post a h out).eval (List.ofFn x) = true) :
    ∀ x : Fin n → Bool, (lifted n pre post a h out).eval (List.ofFn x) =
      (original pre post a h out).eval (List.ofFn x) := by
  intro x
  rw [lifted, Circuit.size, positive_top_or_eval]
  change ((AliasPruning.erase n pre post a out).eval (List.ofFn x) ||
    ((AliasPruning.erase n pre post a out).wires (List.ofFn x)).getD h false) = _
  rw [body_guard n pre post a h out hh x]
  cases hz : (wiresFrom pre (List.ofFn x)).getD h false with
  | false =>
    simp only [Bool.or_false]
    exact ResidualFirstAnd.alias_erase_eval_at n pre post ⟨.or, [a, h]⟩ a out ha x
      (original_gate_copy n pre post a h out ha x hz)
  | true => simp [hbelow x hz]

lemma lifted_size (n : ℕ) (pre post : List Gate) (a h out : ℕ) :
    (lifted n pre post a h out).size = (original pre post a h out).size := by
  simp [lifted, original, AliasPruning.erase, Circuit.size]

lemma lifted_fanin (n : ℕ) (pre post : List Gate) (a h out : ℕ)
    (hfan : FanInTwo (original pre post a h out)) :
    FanInTwo (lifted n pre post a h out) := by
  have hbody := AliasPruning.erase_fanin n pre post ⟨.or, [a, h]⟩ a out hfan
  intro g hg
  change g ∈ (AliasPruning.erase n pre post a out).gates ++ [⟨.or, [_, h]⟩] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hbody g hg
  · obtain rfl := List.mem_singleton.mp hg
    simp

lemma lifted_op_count (n : ℕ) (pre post : List Gate) (a h out : ℕ) (P : GateOp → Bool) :
    (lifted n pre post a h out).gates.countP (fun g => P g.op) =
      (original pre post a h out).gates.countP (fun g => P g.op) := by
  simp [lifted, original, AliasPruning.erase, AliasPruning.renamed, List.countP_map, List.countP_cons, Function.comp_def,
    Nat.add_comm, Nat.add_left_comm]

lemma lifted_first (n : ℕ) (pre post : List Gate) (a h out : ℕ) (hn : 0 < pre.length) :
    (lifted n pre post a h out).gates[0]? = (original pre post a h out).gates[0]? := by
  cases pre with
  | nil => simp at hn
  | cons g pre => simp [lifted, original, AliasPruning.erase]

lemma lifted_normal (n : ℕ) (pre post : List Gate) (a h out : ℕ)
    (hn : ∀ g ∈ (original pre post a h out).gates,
      g.op = GateOp.not → g.inputs.length ≤ 1) :
    ∀ g ∈ (lifted n pre post a h out).gates,
      g.op = GateOp.not → g.inputs.length ≤ 1 := by
  intro g hg
  change g ∈ (pre ++ post.map (AliasPruning.renamed (n + pre.length) a)) ++ [⟨.or, [_, h]⟩] at hg
  rcases List.mem_append.mp hg with hg | hg
  · rcases List.mem_append.mp hg with hg | hg
    · exact hn g (List.mem_append_left _ hg)
    · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hg
      simpa [AliasPruning.renamed] using hn q (List.mem_append_right _ (List.mem_cons_of_mem _ hq))
  · obtain rfl := List.mem_singleton.mp hg
    simp

lemma append_false_true_count (n : ℕ) (gs : List Gate) (g : Gate) (x : Fin n → Bool)
    (hz : (Circuit.mk (gs ++ [g]) (n + gs.length)).eval (List.ofFn x) = false) :
    ((Circuit.mk (gs ++ [g]) (n + gs.length)).wires (List.ofFn x)).countP id =
      ((Circuit.mk gs 0).wires (List.ofFn x)).countP id := by
  have he : (Circuit.mk (gs ++ [g]) (n + gs.length)).eval (List.ofFn x) =
      g.op.eval (g.inputs.map fun i => (wiresFrom gs (List.ofFn x)).getD i false) := by
    simpa [Circuit.eval, Circuit.wires, wiresFrom] using
      positive_gate_output_value gs [] g (List.ofFn x)
  have hg : g.op.eval (g.inputs.map fun i => (wiresFrom gs (List.ofFn x)).getD i false) = false := by
    rw [← he, hz]
  change (wiresFrom (gs ++ [g]) (List.ofFn x)).countP id =
    (wiresFrom gs (List.ofFn x)).countP id
  rw [wiresFrom_append]
  change ((wiresFrom gs (List.ofFn x)) ++ [_]).countP id = _
  rw [hg]
  simp

lemma guard_false_on_negative (n : ℕ) (pre post : List Gate) (a h out : ℕ)
    (hbelow : ∀ x : Fin n → Bool,
      (wiresFrom pre (List.ofFn x)).getD h false = true →
        (original pre post a h out).eval (List.ofFn x) = true)
    (x : Fin n → Bool) (hz : (original pre post a h out).eval (List.ofFn x) = false) :
    (wiresFrom pre (List.ofFn x)).getD h false = false := by
  cases hh : (wiresFrom pre (List.ofFn x)).getD h false with
  | false => rfl
  | true => have he := hbelow x hh; rw [hz] at he; contradiction

lemma lifted_true_count_on_negative (n : ℕ) (pre post : List Gate) (a h out : ℕ)
    (ha : a < n + pre.length) (hh : h < n + pre.length)
    (hbelow : ∀ x : Fin n → Bool,
      (wiresFrom pre (List.ofFn x)).getD h false = true →
        (original pre post a h out).eval (List.ofFn x) = true)
    (x : Fin n → Bool) (hz : (original pre post a h out).eval (List.ofFn x) = false) :
    ((lifted n pre post a h out).wires (List.ofFn x)).countP id +
      Bool.toNat (((original pre post a h out).wires (List.ofFn x)).getD a false) =
      ((original pre post a h out).wires (List.ofFn x)).countP id := by
  have hguard := guard_false_on_negative n pre post a h out hbelow x hz
  have hcopy := original_gate_copy n pre post a h out ha x hguard
  have hb := AliasPruning.alias_erase_true_count_at n pre post ⟨.or, [a, h]⟩ a out ha x hcopy
  change ((AliasPruning.erase n pre post a out).wires (List.ofFn x)).countP id +
    Bool.toNat (((original pre post a h out).wires (List.ofFn x)).getD (n + pre.length) false) =
    ((original pre post a h out).wires (List.ofFn x)).countP id at hb
  rw [hcopy] at hb
  have hnew : (lifted n pre post a h out).eval (List.ofFn x) = false := by
    rw [lifted_eval n pre post a h out ha hh hbelow x, hz]
  have hc := append_false_true_count n (AliasPruning.erase n pre post a out).gates
    ⟨.or, [(AliasPruning.erase n pre post a out).output, h]⟩ x hnew
  change ((lifted n pre post a h out).wires (List.ofFn x)).countP id =
    ((AliasPruning.erase n pre post a out).wires (List.ofFn x)).countP id at hc
  rw [hc]
  exact hb

def sampleEnergy {n : ℕ} (S : Finset (Fin n → Bool)) (C : Circuit) : ℕ :=
  ∑ x ∈ S, (C.wires (List.ofFn x)).countP id

lemma sample_energy_balance (n : ℕ) (pre post : List Gate) (a h out : ℕ)
    (ha : a < n + pre.length) (hh : h < n + pre.length)
    (hbelow : ∀ x : Fin n → Bool,
      (wiresFrom pre (List.ofFn x)).getD h false = true →
        (original pre post a h out).eval (List.ofFn x) = true)
    (S : Finset (Fin n → Bool))
    (hneg : ∀ x ∈ S, (original pre post a h out).eval (List.ofFn x) = false) :
    sampleEnergy S (lifted n pre post a h out) +
      (∑ x ∈ S, Bool.toNat (((original pre post a h out).wires (List.ofFn x)).getD a false)) =
        sampleEnergy S (original pre post a h out) := by
  unfold sampleEnergy
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  exact lifted_true_count_on_negative n pre post a h out ha hh hbelow x (hneg x hx)

lemma sample_energy_decreases (n : ℕ) (pre post : List Gate) (a h out : ℕ)
    (ha : a < n + pre.length) (hh : h < n + pre.length)
    (hbelow : ∀ x : Fin n → Bool,
      (wiresFrom pre (List.ofFn x)).getD h false = true →
        (original pre post a h out).eval (List.ofFn x) = true)
    (S : Finset (Fin n → Bool))
    (hneg : ∀ x ∈ S, (original pre post a h out).eval (List.ofFn x) = false)
    (hunsafe : ∃ x ∈ S, ((original pre post a h out).wires (List.ofFn x)).getD a false = true) :
    sampleEnergy S (lifted n pre post a h out) < sampleEnergy S (original pre post a h out) := by
  obtain ⟨x, hx, ha1⟩ := hunsafe
  have hsum := Finset.single_le_sum
    (fun y (_ : y ∈ S) => Nat.zero_le (Bool.toNat
      (((original pre post a h out).wires (List.ofFn y)).getD a false))) hx
  rw [ha1] at hsum
  have hbalance := sample_energy_balance n pre post a h out ha hh hbelow S hneg
  simp only [Bool.toNat_true] at hsum
  omega

noncomputable def negativeSamples {n : ℕ} (F : (Fin n → Bool) → Bool) : Finset (Fin n → Bool) := by
  classical
  exact Finset.univ.filter fun x => F x = false

noncomputable def negativeEnergy {n : ℕ} (F : (Fin n → Bool) → Bool) (C : Circuit) : ℕ :=
  sampleEnergy (negativeSamples F) C

lemma negativeSamples_mem {n : ℕ} (F : (Fin n → Bool) → Bool) (x : Fin n → Bool) :
    x ∈ negativeSamples F ↔ F x = false := by
  classical
  simp [negativeSamples]

lemma negative_energy_decreases (n : ℕ) (F : (Fin n → Bool) → Bool)
    (pre post : List Gate) (a h out : ℕ)
    (ha : a < n + pre.length) (hh : h < n + pre.length)
    (heval : ∀ x : Fin n → Bool, (original pre post a h out).eval (List.ofFn x) = F x)
    (hbelow : ∀ x : Fin n → Bool,
      (wiresFrom pre (List.ofFn x)).getD h false = true → F x = true)
    (hunsafe : ∃ x : Fin n → Bool, F x = false ∧
      ((original pre post a h out).wires (List.ofFn x)).getD a false = true) :
    negativeEnergy F (lifted n pre post a h out) < negativeEnergy F (original pre post a h out) := by
  apply sample_energy_decreases n pre post a h out ha hh
    (by intro x hx; rw [heval]; exact hbelow x hx) (negativeSamples F)
  · intro x hx
    rw [heval]
    exact (negativeSamples_mem F x).mp hx
  · obtain ⟨x, hx, hax⟩ := hunsafe
    exact ⟨x, (negativeSamples_mem F x).mpr hx, hax⟩

lemma exists_energy_minimum (n : ℕ) (F : (Fin n → Bool) → Bool) (Admissible : Circuit → Prop)
    (hne : ∃ C, Admissible C) :
    ∃ C, Admissible C ∧ ∀ D, Admissible D → negativeEnergy F C ≤ negativeEnergy F D := by
  classical
  have hex : ∃ k, ∃ C, Admissible C ∧ negativeEnergy F C = k := by
    obtain ⟨C, hC⟩ := hne
    exact ⟨negativeEnergy F C, C, hC, rfl⟩
  obtain ⟨C, hC, hval⟩ := Nat.find_spec hex
  refine ⟨C, hC, ?_⟩
  intro D hD
  have hmin := Nat.find_min' hex (show ∃ C, Admissible C ∧ negativeEnergy F C = negativeEnergy F D from
    ⟨D, hD, rfl⟩)
  simpa only [← hval] using hmin

lemma minimum_energy_no_mixed_or (n : ℕ) (F : (Fin n → Bool) → Bool)
    (Admissible : Circuit → Prop) (pre post : List Gate) (a h out : ℕ)
    (ha : a < n + pre.length) (hh : h < n + pre.length)
    (heval : ∀ x : Fin n → Bool, (original pre post a h out).eval (List.ofFn x) = F x)
    (hminimum : ∀ D, Admissible D →
      negativeEnergy F (original pre post a h out) ≤ negativeEnergy F D)
    (hclosed : (∀ x : Fin n → Bool,
      (wiresFrom pre (List.ofFn x)).getD h false = true → F x = true) →
        Admissible (lifted n pre post a h out))
    (hunsafe : ∃ x : Fin n → Bool, F x = false ∧
      ((original pre post a h out).wires (List.ofFn x)).getD a false = true) :
    ∃ x : Fin n → Bool, F x = false ∧ (wiresFrom pre (List.ofFn x)).getD h false = true := by
  classical
  by_contra hn
  have hsafe : ∀ x : Fin n → Bool,
      (wiresFrom pre (List.ofFn x)).getD h false = true → F x = true := by
    intro x hx
    cases he : F x with
    | false => exact False.elim (hn ⟨x, he, hx⟩)
    | true => rfl
  have hlt := negative_energy_decreases n F pre post a h out ha hh heval hsafe hunsafe
  have hle := hminimum (lifted n pre post a h out) (hclosed hsafe)
  omega

lemma lifted_output_bound (n : ℕ) (pre post : List Gate) (a h out : ℕ) :
    (lifted n pre post a h out).output < n + (lifted n pre post a h out).gates.length := by
  simp [lifted, Circuit.size]

lemma lifted_monotone (n : ℕ) (pre post : List Gate) (a h out : ℕ)
    (hmono : Monotone2 (original pre post a h out)) :
    Monotone2 (lifted n pre post a h out) := by
  have hb := AliasPruning.erase_monotone n pre post ⟨.or, [a, h]⟩ a out hmono
  intro g hg
  change g ∈ (AliasPruning.erase n pre post a out).gates ++ [⟨.or, [_, h]⟩] at hg
  rcases List.mem_append.mp hg with hg | hg
  · exact hb g hg
  · obtain rfl := List.mem_singleton.mp hg
    simp

lemma lifted_back (n : ℕ) (pre post : List Gate) (a h out : ℕ)
    (ha : a < n + pre.length) (hh : h < n + pre.length)
    (ho : out < n + (pre ++ ⟨.or, [a, h]⟩ :: post).length)
    (back : ∀ j g, (original pre post a h out).gates[j]? = some g →
      ∀ i ∈ g.inputs, i < n + j) :
    ∀ j g, (lifted n pre post a h out).gates[j]? = some g →
      ∀ i ∈ g.inputs, i < n + j := by
  let body := AliasPruning.erase n pre post a out
  have hb := AliasPruning.erase_strict_back n pre post ⟨.or, [a, h]⟩ a out ha back
  have hout := AliasPruning.erase_output_bound n pre post ⟨.or, [a, h]⟩ a out ha ho
  have hguard : h < n + body.gates.length := by
    simp only [body, AliasPruning.erase, List.length_append, List.length_map]
    omega
  intro j g hj i hi
  change (body.gates ++ [⟨.or, [body.output, h]⟩])[j]? = some g at hj
  by_cases hjlt : j < body.gates.length
  · rw [List.getElem?_append_left hjlt] at hj
    exact hb j g hj i hi
  · have hjlen : j < (body.gates ++ [(⟨.or, [body.output, h]⟩ : Gate)]).length := by
      by_contra hn
      rw [List.getElem?_eq_none_iff.2 (by omega)] at hj
      cases hj
    have heq : j = body.gates.length := by simp only [List.length_append, List.length_singleton] at hjlen; omega
    subst j
    have hg : g = ⟨.or, [body.output, h]⟩ := by simpa using hj.symm
    subst g
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl
    · exact hout
    · exact hguard

def Candidate (n : ℕ) (F : (Fin n → Bool) → Bool) (size nots : ℕ)
    (requireMono : Bool) (first : Gate) (C : Circuit) : Prop :=
  FanInTwo C ∧ C.size = size ∧
    (∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x) ∧
    C.gates[0]? = some first ∧
    (∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1) ∧
    (∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j) ∧
    C.output < n + C.gates.length ∧
    C.gates.countP isNot = nots ∧
    (requireMono = true → Monotone2 C)

lemma candidate_or_prefix_nonempty (n : ℕ) (F : (Fin n → Bool) → Bool) (size nots : ℕ)
    (requireMono : Bool) (first : Gate) (hfirst : first.op ≠ GateOp.or)
    (pre post : List Gate) (a h out : ℕ)
    (hC : Candidate n F size nots requireMono first (original pre post a h out)) :
    0 < pre.length := by
  have hf := hC.2.2.2.1
  cases pre with
  | nil =>
    have he : (⟨GateOp.or, [a, h]⟩ : Gate) = first := by simpa [original] using hf
    have hop := congrArg Gate.op he
    exact False.elim (hfirst hop.symm)
  | cons g pre => simp

lemma lifted_candidate (n : ℕ) (F : (Fin n → Bool) → Bool) (size nots : ℕ)
    (requireMono : Bool) (first : Gate) (hfirst : first.op ≠ GateOp.or)
    (pre post : List Gate) (a h out : ℕ)
    (hC : Candidate n F size nots requireMono first (original pre post a h out))
    (hsafe : ∀ x : Fin n → Bool, (wiresFrom pre (List.ofFn x)).getD h false = true → F x = true) :
    Candidate n F size nots requireMono first (lifted n pre post a h out) := by
  obtain ⟨hfan, hsize, heval, hf, hnormal, hback, hout, hnots, hmono⟩ := hC
  have hlookup : (original pre post a h out).gates[pre.length]? = some ⟨.or, [a, h]⟩ := by simp [original]
  have ha := hback pre.length _ hlookup a (by simp)
  have hh := hback pre.length _ hlookup h (by simp)
  have hpre : 0 < pre.length := candidate_or_prefix_nonempty n F size nots requireMono first hfirst
    pre post a h out ⟨hfan, hsize, heval, hf, hnormal, hback, hout, hnots, hmono⟩
  refine ⟨lifted_fanin n pre post a h out hfan, ?_, ?_, ?_,
    lifted_normal n pre post a h out hnormal,
    lifted_back n pre post a h out ha hh hout hback,
    lifted_output_bound n pre post a h out, ?_, ?_⟩
  · rw [lifted_size, hsize]
  · intro x
    rw [lifted_eval n pre post a h out ha hh (by intro y hy; rw [heval]; exact hsafe y hy), heval]
  · rw [lifted_first n pre post a h out hpre, hf]
  · have hc := lifted_op_count n pre post a h out
      (fun op => match op with | GateOp.not => true | _ => false)
    change (lifted n pre post a h out).gates.countP isNot =
      (original pre post a h out).gates.countP isNot at hc
    rw [hc, hnots]
  · intro hm
    exact lifted_monotone n pre post a h out (hmono hm)

lemma exists_candidate_ordered_normal_form (n : ℕ) (F : (Fin n → Bool) → Bool) (size nots : ℕ)
    (requireMono : Bool) (first : Gate) (hfirst : first.op ≠ GateOp.or)
    (hne : ∃ C, Candidate n F size nots requireMono first C) :
    ∃ C, Candidate n F size nots requireMono first C ∧
      ∀ pre post a h out, C = original pre post a h out →
        (∃ x : Fin n → Bool, F x = false ∧ (C.wires (List.ofFn x)).getD a false = true) →
        ∃ x : Fin n → Bool, F x = false ∧ (C.wires (List.ofFn x)).getD h false = true := by
  obtain ⟨C, hC, hminimum⟩ := exists_energy_minimum n F (Candidate n F size nots requireMono first) hne
  refine ⟨C, hC, ?_⟩
  intro pre post a h out hsplit hunsafe
  subst C
  have hlookup : (original pre post a h out).gates[pre.length]? = some ⟨.or, [a, h]⟩ := by simp [original]
  have hback := hC.2.2.2.2.2.1
  have ha := hback pre.length _ hlookup a (by simp)
  have hh := hback pre.length _ hlookup h (by simp)
  obtain ⟨x, hx, hhx⟩ := minimum_energy_no_mixed_or n F (Candidate n F size nots requireMono first)
    pre post a h out ha hh hC.2.2.1 hminimum
    (lifted_candidate n F size nots requireMono first hfirst pre post a h out hC) hunsafe
  refine ⟨x, hx, ?_⟩
  rw [original_guard n pre post a h out hh x]
  exact hhx

end SingleOrEnergy

namespace SingleOrEnergy

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma original_swap_wires (pre post : List Gate) (a h out : ℕ) (xs : List Bool) :
    (original pre post a h out).wires xs = (original pre post h a out).wires xs := by
  simp [original, Circuit.wires, List.foldl_append, GateOp.eval, Bool.or_comm]

lemma original_swap_eval (n : ℕ) (pre post : List Gate) (a h out : ℕ) (x : Fin n → Bool) :
    (original pre post a h out).eval (List.ofFn x) =
      (original pre post h a out).eval (List.ofFn x) := by
  unfold Circuit.eval
  rw [original_swap_wires]
  rfl

lemma original_swap_first (pre post : List Gate) (a h out : ℕ) (hpre : 0 < pre.length) :
    (original pre post h a out).gates[0]? = (original pre post a h out).gates[0]? := by
  cases pre with
  | nil => simp at hpre
  | cons g pre => rfl

lemma original_swap_back (n : ℕ) (pre post : List Gate) (a h out : ℕ)
    (back : ∀ j g, (original pre post a h out).gates[j]? = some g →
      ∀ i ∈ g.inputs, i < n + j) :
    ∀ j g, (original pre post h a out).gates[j]? = some g →
      ∀ i ∈ g.inputs, i < n + j := by
  intro j g hg
  by_cases hj : j = pre.length
  · have he : g = ⟨GateOp.or, [h, a]⟩ := by
      simpa [original, hj] using hg.symm
    subst g
    intro i hi
    apply back j ⟨GateOp.or, [a, h]⟩ (by simp [original, hj])
    simpa [or_comm] using hi
  · have hs : (original pre post h a out).gates[j]? =
        (original pre post a h out).gates[j]? := by
      change (pre ++ ⟨GateOp.or, [h, a]⟩ :: post)[j]? =
        (pre ++ ⟨GateOp.or, [a, h]⟩ :: post)[j]?
      by_cases hlt : j < pre.length
      · rw [List.getElem?_append_left hlt, List.getElem?_append_left hlt]
      · rw [List.getElem?_append_right (by omega), List.getElem?_append_right (by omega)]
        cases hd : j - pre.length with
        | zero => omega
        | succ k => rfl
    exact back j g (hs.symm.trans hg)

lemma sampleEnergy_swap {n : ℕ} (S : Finset (Fin n → Bool))
    (pre post : List Gate) (a h out : ℕ) :
    sampleEnergy S (original pre post a h out) = sampleEnergy S (original pre post h a out) := by
  unfold sampleEnergy
  apply Finset.sum_congr rfl
  intro x hx
  rw [original_swap_wires]

lemma negativeEnergy_swap {n : ℕ} (F : (Fin n → Bool) → Bool)
    (pre post : List Gate) (a h out : ℕ) :
    negativeEnergy F (original pre post a h out) =
      negativeEnergy F (original pre post h a out) := by
  exact sampleEnergy_swap (negativeSamples F) pre post a h out

lemma candidate_swap (n : ℕ) (F : (Fin n → Bool) → Bool) (size nots : ℕ)
    (requireMono : Bool) (first : Gate) (hfirst : first.op ≠ GateOp.or)
    (pre post : List Gate) (a h out : ℕ)
    (hC : Candidate n F size nots requireMono first (original pre post a h out)) :
    Candidate n F size nots requireMono first (original pre post h a out) := by
  have hpre := candidate_or_prefix_nonempty n F size nots requireMono first hfirst
    pre post a h out hC
  obtain ⟨hfan, hsize, heval, hf, hnormal, hback, hout, hnots, hmono⟩ := hC
  refine ⟨?_, ?_, ?_, ?_, ?_, original_swap_back n pre post a h out hback, ?_, ?_, ?_⟩
  · intro q hq
    simp only [original, List.mem_append, List.mem_cons] at hq
    rcases hq with hq | rfl | hq
    · exact hfan q (by simp [original, hq])
    · simp
    · exact hfan q (by simp [original, hq])
  · simpa only [original, Circuit.size, List.length_append, List.length_cons] using hsize
  · intro x
    rw [original_swap_eval n pre post h a out x]
    exact heval x
  · rw [original_swap_first pre post a h out hpre, hf]
  · intro q hq hqnot
    simp only [original, List.mem_append, List.mem_cons] at hq
    rcases hq with hq | rfl | hq
    · exact hnormal q (by simp [original, hq]) hqnot
    · cases hqnot
    · exact hnormal q (by simp [original, hq]) hqnot
  · simpa only [original, List.length_append, List.length_cons] using hout
  · simpa [original, List.countP_append, List.countP_cons, isNot] using hnots
  · intro hm q hq
    have hmon := hmono hm
    simp only [original, List.mem_append, List.mem_cons] at hq
    rcases hq with hq | rfl | hq
    · exact hmon q (by simp [original, hq])
    · simp
    · exact hmon q (by simp [original, hq])


end SingleOrEnergy

namespace SingleOrEnergy

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Restriction

lemma candidate_energy_minimum_ordered_rule (n : ℕ) (F : (Fin n → Bool) → Bool) (size nots : ℕ)
    (requireMono : Bool) (first : Gate) (hfirst : first.op ≠ GateOp.or) (C : Circuit)
    (hC : Candidate n F size nots requireMono first C)
    (hminimum : ∀ D, Candidate n F size nots requireMono first D → negativeEnergy F C ≤ negativeEnergy F D) :
    ∀ pre post a h out, C = original pre post a h out →
      (∃ x : Fin n → Bool, F x = false ∧ (C.wires (List.ofFn x)).getD a false = true) →
      ∃ x : Fin n → Bool, F x = false ∧ (C.wires (List.ofFn x)).getD h false = true := by
  intro pre post a h out hsplit hunsafe
  subst C
  have hlookup : (original pre post a h out).gates[pre.length]? = some ⟨.or, [a, h]⟩ := by simp [original]
  have hback := hC.2.2.2.2.2.1
  have ha := hback pre.length _ hlookup a (by simp)
  have hh := hback pre.length _ hlookup h (by simp)
  obtain ⟨x, hx, hhx⟩ := minimum_energy_no_mixed_or n F (Candidate n F size nots requireMono first)
    pre post a h out ha hh hC.2.2.1 hminimum
    (lifted_candidate n F size nots requireMono first hfirst pre post a h out hC) hunsafe
  refine ⟨x, hx, ?_⟩
  rw [original_guard n pre post a h out hh x]
  exact hhx

lemma candidate_of_minimal (n : ℕ) (F : (Fin n → Bool) → Bool) (C : Circuit)
    (first : Gate) (requireMono : Bool) (hfan : FanInTwo C)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (heval : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x)
    (hfirst : C.gates[0]? = some first)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j)
    (hmono : requireMono = true → Monotone2 C) :
    Candidate n F C.size (C.gates.countP isNot) requireMono first C := by
  have hpos : 0 < C.size := by
    change 0 < C.gates.length
    by_contra hn
    rw [List.getElem?_eq_none_iff.2 (by omega)] at hfirst
    cases hfirst
  have hlast := LivePruning.minimal_output_last n C hfan hmin hpos
  refine ⟨hfan, rfl, heval, hfirst, hnot, back, ?_, rfl, hmono⟩
  change C.output < n + C.size
  omega

lemma candidate_inherits_minimum (n : ℕ) (F : (Fin n → Bool) → Bool) (C : Circuit)
    (first : Gate) (requireMono : Bool)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (heval : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x)
    (D : Circuit) (hD : Candidate n F C.size (C.gates.countP isNot) requireMono first D) :
    ∀ E : Circuit, FanInTwo E →
      (∀ x : Fin n → Bool, E.eval (List.ofFn x) = D.eval (List.ofFn x)) → D.size ≤ E.size := by
  intro E hE he
  rw [hD.2.1]
  apply hmin E hE
  intro x
  rw [he, hD.2.2.1, heval]

lemma exists_minimal_candidate_energy (n : ℕ) (F : (Fin n → Bool) → Bool) (C : Circuit)
    (first : Gate) (requireMono : Bool) (hfan : FanInTwo C)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (heval : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x)
    (hfirst : C.gates[0]? = some first)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j)
    (hmono : requireMono = true → Monotone2 C) :
    ∃ D, Candidate n F C.size (C.gates.countP isNot) requireMono first D ∧
      (∀ E : Circuit, FanInTwo E →
        (∀ x : Fin n → Bool, E.eval (List.ofFn x) = D.eval (List.ofFn x)) → D.size ≤ E.size) ∧
      (∀ E, Candidate n F C.size (C.gates.countP isNot) requireMono first E →
        negativeEnergy F D ≤ negativeEnergy F E) := by
  have hC := candidate_of_minimal n F C first requireMono hfan hmin heval hfirst hnot back hmono
  obtain ⟨D, hD, henergy⟩ := exists_energy_minimum n F
    (Candidate n F C.size (C.gates.countP isNot) requireMono first) ⟨C, hC⟩
  exact ⟨D, hD, candidate_inherits_minimum n F C first requireMono hmin heval D hD, henergy⟩

def NoMixedOr (n : ℕ) (F : (Fin n → Bool) → Bool) (C : Circuit) : Prop :=
  ∀ pre post a h out, C = original pre post a h out →
    ((∃ x : Fin n → Bool, F x = false ∧ (C.wires (List.ofFn x)).getD a false = true) ↔
      ∃ x : Fin n → Bool, F x = false ∧ (C.wires (List.ofFn x)).getD h false = true)

lemma candidate_energy_minimum_no_mixed_or (n : ℕ) (F : (Fin n → Bool) → Bool) (size nots : ℕ)
    (requireMono : Bool) (first : Gate) (hfirst : first.op ≠ GateOp.or) (C : Circuit)
    (hC : Candidate n F size nots requireMono first C)
    (hminimum : ∀ D, Candidate n F size nots requireMono first D → negativeEnergy F C ≤ negativeEnergy F D) :
    NoMixedOr n F C := by
  intro pre post a h out hsplit
  constructor
  · exact candidate_energy_minimum_ordered_rule n F size nots requireMono first hfirst C hC hminimum
      pre post a h out hsplit
  · intro hunsafe
    subst C
    have hswap := candidate_swap n F size nots requireMono first hfirst pre post a h out hC
    have hminswap : ∀ D, Candidate n F size nots requireMono first D →
        negativeEnergy F (original pre post h a out) ≤ negativeEnergy F D := by
      intro D hD
      rw [← negativeEnergy_swap F pre post a h out]
      exact hminimum D hD
    have hunsafeSwap : ∃ x : Fin n → Bool, F x = false ∧
        ((original pre post h a out).wires (List.ofFn x)).getD h false = true := by
      obtain ⟨x, hx, hw⟩ := hunsafe
      refine ⟨x, hx, ?_⟩
      rw [← original_swap_wires pre post a h out]
      exact hw
    obtain ⟨x, hx, hw⟩ := candidate_energy_minimum_ordered_rule n F size nots requireMono first hfirst
      (original pre post h a out) hswap hminswap pre post h a out rfl hunsafeSwap
    refine ⟨x, hx, ?_⟩
    rw [original_swap_wires pre post a h out]
    exact hw

lemma exists_minimal_no_mixed_or (n : ℕ) (F : (Fin n → Bool) → Bool) (C : Circuit)
    (first : Gate) (hfirstop : first.op ≠ GateOp.or) (requireMono : Bool) (hfan : FanInTwo C)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (heval : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = F x)
    (hfirst : C.gates[0]? = some first)
    (hnot : ∀ g ∈ C.gates, g.op = GateOp.not → g.inputs.length ≤ 1)
    (back : ∀ j g, C.gates[j]? = some g → ∀ i ∈ g.inputs, i < n + j)
    (hmono : requireMono = true → Monotone2 C) :
    ∃ D, Candidate n F C.size (C.gates.countP isNot) requireMono first D ∧
      (∀ E : Circuit, FanInTwo E →
        (∀ x : Fin n → Bool, E.eval (List.ofFn x) = D.eval (List.ofFn x)) → D.size ≤ E.size) ∧
      (∀ E, Candidate n F C.size (C.gates.countP isNot) requireMono first E →
        negativeEnergy F D ≤ negativeEnergy F E) ∧
      NoMixedOr n F D := by
  obtain ⟨D, hD, hDmin, henergy⟩ := exists_minimal_candidate_energy n F C first requireMono
    hfan hmin heval hfirst hnot back hmono
  exact ⟨D, hD, hDmin, henergy,
    candidate_energy_minimum_no_mixed_or n F C.size (C.gates.countP isNot)
      requireMono first hfirstop D hD henergy⟩

lemma raw_wire_unsafe (n : ℕ) (F : (Fin n → Bool) → Bool) (C : Circuit) (a : Fin n)
    (hzero : F (fun i => decide (i = a)) = false) :
    ∃ x : Fin n → Bool, F x = false ∧ (C.wires (List.ofFn x)).getD a.val false = true := by
  refine ⟨(fun i => decide (i = a)), hzero, ?_⟩
  have hi : a.val < (List.ofFn (fun i : Fin n => decide (i = a))).length := by simp
  change ((Circuit.mk C.gates 0).wires (List.ofFn (fun i : Fin n => decide (i = a)))).getD a.val false = true
  rw [AliasPruning.wires_input C.gates _ a.val hi]
  simp only [List.getD, List.getElem?_ofFn, dite_eq_left a.isLt, Option.getD_some]
  simp

lemma raw_or_partner_unsafe (n : ℕ) (F : (Fin n → Bool) → Bool) (C : Circuit)
    (hnormal : NoMixedOr n F C) (a : Fin n)
    (hzero : F (fun i => decide (i = a)) = false)
    (pre post : List Gate) (h out : ℕ)
    (hshape : C = original pre post a.val h out) :
    ∃ x : Fin n → Bool, F x = false ∧ (C.wires (List.ofFn x)).getD h false = true := by
  exact (hnormal pre post a.val h out hshape).mp (raw_wire_unsafe n F C a hzero)

lemma raw_or_partner_unsafe_rev (n : ℕ) (F : (Fin n → Bool) → Bool) (C : Circuit)
    (hnormal : NoMixedOr n F C) (a : Fin n)
    (hzero : F (fun i => decide (i = a)) = false)
    (pre post : List Gate) (h out : ℕ)
    (hshape : C = original pre post h a.val out) :
    ∃ x : Fin n → Bool, F x = false ∧ (C.wires (List.ofFn x)).getD h false = true := by
  exact (hnormal pre post h a.val out hshape).mpr (raw_wire_unsafe n F C a hzero)

end SingleOrEnergy


namespace SingleOrEnergy

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Restriction

def WirePositive (n : ℕ) (F : (Fin n → Bool) → Bool) (C : Circuit) (i : ℕ) : Prop :=
  ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD i false = true → F x = true

lemma wire_positive_iff_not_unsafe (n : ℕ) (F : (Fin n → Bool) → Bool)
    (C : Circuit) (i : ℕ) : WirePositive n F C i ↔
      ¬ ∃ x : Fin n → Bool, F x = false ∧ (C.wires (List.ofFn x)).getD i false = true := by
  constructor
  · rintro hp ⟨x, hx, hw⟩
    have := hp x hw
    simp_all
  · intro hn x hx
    cases hf : F x with
    | false => exact False.elim (hn ⟨x, hf, hx⟩)
    | true => rfl

lemma no_mixed_or_positive_iff (n : ℕ) (F : (Fin n → Bool) → Bool)
    (C : Circuit) (hnormal : NoMixedOr n F C) (pre post : List Gate) (a h out : ℕ)
    (hshape : C = original pre post a h out) :
    WirePositive n F C a ↔ WirePositive n F C h := by
  rw [wire_positive_iff_not_unsafe, wire_positive_iff_not_unsafe]
  exact not_congr (hnormal pre post a h out hshape)

lemma minimum_positive_consumer_output (n : ℕ) (F : (Fin n → Bool) → Bool)
    (pre post : List Gate) (g : Gate) (out h : ℕ)
    (hn : n ≤ h) (hh : h < n + pre.length)
    (hfanin : FanInTwo ({gates := pre ++ g :: post, output := out} : Circuit))
    (heval : ∀ x : Fin n → Bool,
      ({gates := pre ++ g :: post, output := out} : Circuit).eval (List.ofFn x) = F x)
    (hpositive : WirePositive n F ⟨pre ++ g :: post, out⟩ h)
    (hmin : ∀ E : Circuit, FanInTwo E →
      (∀ x : Fin n → Bool, E.eval (List.ofFn x) =
        ({gates := pre ++ g :: post, output := out} : Circuit).eval (List.ofFn x)) →
      ({gates := pre ++ g :: post, output := out} : Circuit).size ≤ E.size)
    (hread : h ∈ effectiveInputs g)
    (hback : ∀ i ∈ g.inputs, i < n + pre.length)
    (hnormal : NoMixedOr n F ⟨pre ++ g :: post, out⟩) :
    g.op = GateOp.or ∧ WirePositive n F ⟨pre ++ g :: post, out⟩ (n + pre.length) := by
  have hkeep (x : Fin n → Bool) :
      (({gates := pre ++ g :: post, output := out} : Circuit).wires (List.ofFn x)).getD h false =
        (wiresFrom pre (List.ofFn x)).getD h false := by
    change (wiresFrom (pre ++ g :: post) (List.ofFn x)).getD h false = _
    rw [wiresFrom_append, getD_wiresFrom]
    simpa [length_wiresFrom] using hh
  have hop : g.op = GateOp.or := by
    apply minimum_positive_internal_readers_are_or n pre [] post g out h hn hh hfanin
    · intro x hx
      change ({gates := pre ++ g :: post, output := out} : Circuit).eval (List.ofFn x) = true
      rw [heval]
      apply hpositive x
      rw [hkeep]
      exact hx
    · exact hmin
    · exact hread
  refine ⟨hop, ?_⟩
  have hlen := (hfanin g (by simp)).2
  have hin : h ∈ g.inputs := by simpa [effectiveInputs, hop] using hread
  have hv (x : Fin n → Bool) := FirstAndClassification.full_gate_value n
    ⟨pre ++ g :: post, out⟩ pre post g rfl hback x
  cases hg : g.inputs with
  | nil => simp [hg] at hin
  | cons a rest =>
    cases rest with
    | nil =>
      have hha : h = a := by simpa [hg] using hin
      intro x hx
      apply hpositive x
      simpa [hop, hg, GateOp.eval, hha] using (hv x).symm.trans hx
    | cons b tail =>
      have ht : tail = [] := by simp only [hg, List.length_cons] at hlen; simpa using (show tail.length = 0 by omega)
      subst tail
      have hgate : g = ⟨.or, [a,b]⟩ := by cases g; simp_all
      have hshape : ({gates := pre ++ g :: post, output := out} : Circuit) =
          original pre post a b out := by simp [original, hgate]
      have hab := no_mixed_or_positive_iff n F _ hnormal pre post a b out hshape
      have hpa : WirePositive n F ⟨pre ++ g :: post, out⟩ a := by
        rcases (show h = a ∨ h = b by simpa [hg] using hin) with rfl | rfl
        · exact hpositive
        · exact hab.mpr hpositive
      have hpb := hab.mp hpa
      intro x hx
      have hx' :
          ((({gates := pre ++ g :: post, output := out} : Circuit).wires (List.ofFn x)).getD a false ||
            (({gates := pre ++ g :: post, output := out} : Circuit).wires (List.ofFn x)).getD b false) = true := by
        simpa [hop, hg, GateOp.eval] using (hv x).symm.trans hx
      by_cases ha : (({gates := pre ++ g :: post, output := out} : Circuit).wires (List.ofFn x)).getD a false = true
      · exact hpa x ha
      · apply hpb x
        have hd :
            (({gates := pre ++ g :: post, output := out} : Circuit).wires (List.ofFn x)).getD a false = true ∨
            (({gates := pre ++ g :: post, output := out} : Circuit).wires (List.ofFn x)).getD b false = true := by
          simpa using hx'
        exact hd.resolve_left ha

lemma positive_wire_not_raw (n : ℕ) (F : (Fin n → Bool) → Bool) (C : Circuit)
    (hsingle : ∀ a : Fin n, F (fun i => decide (i = a)) = false)
    (i : ℕ) (hp : WirePositive n F C i) : n ≤ i := by
  by_contra hn
  have hi : i < n := by omega
  have hnunsafe := (wire_positive_iff_not_unsafe n F C i).mp hp
  exact hnunsafe (raw_wire_unsafe n F C ⟨i, hi⟩ (hsingle ⟨i, hi⟩))

end SingleOrEnergy

namespace ConstantPruning

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Restriction

def initStats (m : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin (m + 1) => if i.val = m then Sum.inl b else Sum.inr i.val)

lemma init_inv (n : ℕ) (pre : List Gate) (b : Bool) (x : Fin n → Bool) :
    Inv n (List.ofFn x) (wiresFrom pre (List.ofFn x) ++ [b])
      (initStats (n + pre.length) b, pre) := by
  have hl : (wiresFrom pre (List.ofFn x)).length = n + pre.length := by
    simp [length_wiresFrom]
  refine ⟨by simp [initStats, hl], ?_⟩
  intro i
  by_cases hi : i < n + pre.length + 1
  · have hs : (initStats (n + pre.length) b).getD i (Sum.inl false) =
        if i = n + pre.length then Sum.inl b else Sum.inr i := by
      simp only [initStats, List.getD, List.getElem?_ofFn, dite_eq_left hi, Option.getD_some]
    rw [hs]
    by_cases he : i = n + pre.length
    · subst i
      simp only [↓reduceIte]
      refine ⟨trivial, ?_⟩
      change b = _
      rw [← hl, getD_snoc_eq]
    · rw [ite_eq_right he]
      refine ⟨?_, ?_⟩
      · change i < n + pre.length
        omega
      change (wiresFrom pre (List.ofFn x)).getD i false = (wiresFrom pre (List.ofFn x) ++ [b]).getD i false
      rw [List.getD_append _ _ _ _ (by omega)]
  · have hs : (initStats (n + pre.length) b).getD i (Sum.inl false) = Sum.inl false := by
      apply List.getD_eq_default
      simp only [initStats, List.length_ofFn]
      omega
    rw [hs]
    refine ⟨trivial, ?_⟩
    change false = _
    symm
    apply List.getD_eq_default
    simp only [List.length_append, List.length_singleton, hl]
    omega

lemma delete_constant_gate (n : ℕ) (C : Circuit) (pre post : List Gate) (g : Gate)
    (hshape : C.gates = pre ++ g :: post) (hfan : FanInTwo C) (b : Bool)
    (hconstant : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + pre.length) false = b)
    (hnonconstant : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y)) :
    ∃ D : Circuit, FanInTwo D ∧ D.size + 1 ≤ C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x) := by
  have hpre : ∀ q ∈ pre, Ok q := by
    intro q hq
    apply hfan q
    rw [hshape]
    exact List.mem_append_left _ hq
  have hpost : ∀ q ∈ post, Ok q := by
    intro q hq
    apply hfan q
    rw [hshape]
    exact List.mem_append_right _ (List.mem_cons_of_mem _ hq)
  let acc := elim n post (initStats (n + pre.length) b, pre)
  have hcount : acc.2.length ≤ pre.length + post.length := elim_len n post _
  have hok : ∀ q ∈ acc.2, Ok q := elim_ok n post _ hpre
  have hprefix (x : Fin n → Bool) :
      wiresFrom (pre ++ [g]) (List.ofFn x) = wiresFrom pre (List.ofFn x) ++ [b] := by
    have hv := hconstant x
    change (wiresFrom C.gates (List.ofFn x)).getD (n + pre.length) false = b at hv
    rw [hshape, wiresFrom_append] at hv
    change (wiresFrom post (wiresFrom pre (List.ofFn x) ++ [_])).getD _ false = b at hv
    rw [getD_wiresFrom] at hv
    · have hl : (wiresFrom pre (List.ofFn x)).length = n + pre.length := by simp [length_wiresFrom]
      rw [← hl, getD_snoc_eq] at hv
      rw [wiresFrom_append]
      change wiresFrom pre (List.ofFn x) ++ [_] = _
      rw [hv]
    · simp [length_wiresFrom]
  have hval (x : Fin n → Bool) :
      (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) = C.eval (List.ofFn x) := by
    have hinv := inv_elim n (List.ofFn x) (by simp) post
      (wiresFrom pre (List.ofFn x) ++ [b]) (initStats (n + pre.length) b, pre)
      hpost (init_inv n pre b x)
    have hv := (hinv.2 C.output).2
    change (acc.1.getD C.output (Sum.inl false)).val (wiresFrom acc.2 (List.ofFn x)) = _ at hv
    rw [← hprefix x] at hv
    rw [← wiresFrom_append] at hv
    simpa [Circuit.eval, Circuit.wires, wiresFrom, hshape, List.append_assoc] using hv
  cases hs : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨x, y, hxy⟩ := hnonconstant
    have hx := hval x
    have hy := hval y
    rw [hs] at hx hy
    exact False.elim (hxy (hx.symm.trans hy))
  | inr j =>
    refine ⟨⟨acc.2, j⟩, hok, ?_, ?_⟩
    · simp only [Circuit.size, hshape, List.length_append, List.length_cons]
      omega
    · intro x
      have hv := hval x
      rw [hs] at hv
      exact hv

lemma minimal_no_constant_gate (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (hnonconstant : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y))
    (pre post : List Gate) (g : Gate) (hshape : C.gates = pre ++ g :: post) :
    ¬ ∃ b : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + pre.length) false = b := by
  rintro ⟨b, hb⟩
  obtain ⟨D, hD, hsize, heval⟩ := delete_constant_gate n C pre post g hshape hfan b hb hnonconstant
  have hbound := hmin D hD heval
  omega

lemma minimal_no_constant_index (n : ℕ) (C : Circuit) (hfan : FanInTwo C)
    (hmin : ∀ D : Circuit, FanInTwo D →
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x)) → C.size ≤ D.size)
    (hnonconstant : ∃ x y : Fin n → Bool, C.eval (List.ofFn x) ≠ C.eval (List.ofFn y))
    (j : ℕ) (hj : j < C.size) :
    ¬ ∃ b : Bool, ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD (n + j) false = b := by
  have hlt : j < C.gates.length := hj
  have hshape : C.gates = C.gates.take j ++ C.gates[j] :: C.gates.drop (j + 1) := by
    rw [List.getElem_cons_drop hlt, List.take_append_drop]
  have hl : (C.gates.take j).length = j := by simp; omega
  simpa only [hl] using minimal_no_constant_gate n C hfan hmin hnonconstant _ _ _ hshape

end ConstantPruning

end PEqualNP.Outside.L_meta_2373_aux
