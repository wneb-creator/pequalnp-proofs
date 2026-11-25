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

end PEqualNP.Outside.L_meta_2373_aux
