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


end PEqualNP.Outside.L_meta_2373_aux
