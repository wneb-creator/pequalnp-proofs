import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4592

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.GenericRejection PEqualNP.SyntacticMultilinear PEqualNP.CrossAnd

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl step x

lemma run_nil (x : List Bool) : run [] x = x := rfl

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (step x g) := rfl

lemma run_append (l1 l2 : List Gate) (x : List Bool) :
    run (l1 ++ l2) x = run l2 (run l1 x) := by
  simp [run, List.foldl_append]

lemma step_length (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih, step_length]; simp; omega

lemma step_getD (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp only [step]
  exact List.getD_append _ _ _ _ hi

lemma step_getD_last (w : List Bool) (g : Gate) :
    (step w g).getD w.length false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  simp only [step]
  rw [List.getD_append_right _ _ _ _ (le_refl _)]
  simp

lemma run_getD (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih => rw [run_cons, ih _ (by rw [step_length]; omega), step_getD _ _ _ hi]

lemma run_gate (gs : List Gate) (x : List Bool) (j : ℕ) (hj : j < gs.length) :
    (run gs x).getD (x.length + j) false =
      gs[j].op.eval (gs[j].inputs.map fun i => (run (gs.take j) x).getD i false) := by
  have hsplit : run gs x = run (gs.drop (j + 1)) (step (run (gs.take j) x) gs[j]) := by
    conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons hj]
    rw [run_append, run_cons]
  have hl : (run (gs.take j) x).length = x.length + j := by
    rw [run_length, List.length_take]; omega
  rw [hsplit, run_getD _ _ _ (by rw [step_length]; omega), ← hl, step_getD_last]

lemma run_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    {x y : List Bool} (hlen : x.length = y.length)
    (hxy : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (run gs x).getD i false = true → (run gs y).getD i false = true := by
  induction gs generalizing x y with
  | nil => intro i hi; exact hxy i hi
  | cons g gs ih =>
    have hg := hgs g List.mem_cons_self
    have hgs' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg')
    apply ih hgs' (by simp [step_length, hlen])
    intro i hi
    by_cases hilt : i < x.length
    · rw [step_getD _ _ _ hilt] at hi
      rw [step_getD _ _ _ (by omega)]
      exact hxy i hi
    · have hieq : i = x.length ∨ x.length < i := by omega
      rcases hieq with rfl | hgt
      · rw [step_getD_last] at hi
        rw [hlen, step_getD_last]
        rcases hg.1 with hop | hop
        · rw [hop] at hi ⊢
          simp only [GateOp.eval, List.all_eq_true, List.mem_map, id_eq] at hi ⊢
          intro b hb
          rcases hb with ⟨a, ha, rfl⟩
          exact hxy a (hi (x.getD a false) ⟨a, ha, rfl⟩)
        · rw [hop] at hi ⊢
          simp only [GateOp.eval, List.any_eq_true, List.mem_map, id_eq] at hi ⊢
          rcases hi with ⟨_, ⟨a, ha, rfl⟩, ha_true⟩
          exact ⟨y.getD a false, ⟨a, ha, rfl⟩, hxy a ha_true⟩
      · have h1 : ¬ i < (step x g).length := by rw [step_length]; omega
        rw [List.getD_eq_default _ _ (Nat.le_of_not_lt h1)] at hi
        cases hi

def wval (n : ℕ) (C : Circuit) (w : ℕ) (X Y : Finset (Fin n)) : Bool :=
  (C.wires (incidenceInput X Y)).getD w false

def pts (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun p => wval n C w {p} ∅ = true

def lns (n : ℕ) (C : Circuit) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter fun l => wval n C w ∅ {l} = true

lemma incidenceInput_length {n : ℕ} (X Y : Finset (Fin n)) :
    (incidenceInput X Y).length = n + n := by
  simp [incidenceInput]

lemma incidenceInput_getD_left {n : ℕ} (X Y : Finset (Fin n)) (i : ℕ) (hi : i < n) :
    (incidenceInput X Y).getD i false = decide (⟨i, hi⟩ ∈ X) := by
  rw [incidenceInput, List.getD_append _ _ _ _ (by simp [hi])]
  have hof : (List.ofFn fun p : Fin n => decide (p ∈ X))[i]? = some (decide (⟨i, hi⟩ ∈ X)) := by
    simp [List.getElem?_eq_getElem (by simp [hi] : i < (List.ofFn fun p : Fin n => decide (p ∈ X)).length)]
  rw [List.getD, hof]; rfl

lemma incidenceInput_getD_right {n : ℕ} (X Y : Finset (Fin n)) (i : ℕ) (hi1 : n ≤ i) (hi2 : i < n + n) :
    (incidenceInput X Y).getD i false = decide (⟨i - n, by omega⟩ ∈ Y) := by
  rw [incidenceInput, List.getD_append_right _ _ _ _ (by simp only [List.length_ofFn]; exact hi1)]
  simp only [List.length_ofFn]
  have hof : (List.ofFn fun l : Fin n => decide (l ∈ Y))[i - n]? = some (decide (⟨i - n, by omega⟩ ∈ Y)) := by
    simp [List.getElem?_eq_getElem (by simp; omega : i - n < (List.ofFn fun l : Fin n => decide (l ∈ Y)).length)]
  rw [List.getD, hof]; rfl

lemma wval_mono {n : ℕ} {C : Circuit} (hmono : Monotone2 C) {X1 X2 Y1 Y2 : Finset (Fin n)}
    (hX : X1 ⊆ X2) (hY : Y1 ⊆ Y2) (w : ℕ) :
    wval n C w X1 Y1 = true → wval n C w X2 Y2 = true := by
  apply run_mono C.gates hmono (by simp [incidenceInput_length])
  intro i hi
  by_cases hi1 : i < n
  · rw [incidenceInput_getD_left X1 Y1 i hi1] at hi
    rw [incidenceInput_getD_left X2 Y2 i hi1]
    simp only [decide_eq_true_eq] at hi ⊢
    exact hX hi
  · by_cases hi2 : i < n + n
    · rw [incidenceInput_getD_right X1 Y1 i (by omega) hi2] at hi
      rw [incidenceInput_getD_right X2 Y2 i (by omega) hi2]
      simp only [decide_eq_true_eq] at hi ⊢
      exact hY hi
    · rw [List.getD_eq_default _ _ (by simp [incidenceInput_length]; omega)] at hi
      cases hi

lemma wval_lt_in {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n + n) (X Y : Finset (Fin n)) :
    wval n C w X Y = (incidenceInput X Y).getD w false := by
  change (run C.gates (incidenceInput X Y)).getD w false = _
  exact run_getD C.gates (incidenceInput X Y) w (by rw [incidenceInput_length]; exact hw)

lemma wval_ge_end {n : ℕ} (C : Circuit) (w : ℕ) (hw : n + n + C.gates.length ≤ w) (X Y : Finset (Fin n)) :
    wval n C w X Y = false := by
  change (run C.gates (incidenceInput X Y)).getD w false = false
  rw [List.getD_eq_default]
  rw [run_length, incidenceInput_length]
  exact hw

lemma wval_gate {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (X Y : Finset (Fin n)) :
    wval n C (n + n + j) X Y =
      C.gates[j].op.eval (C.gates[j].inputs.map fun w => if w < n + n + j then wval n C w X Y else false) := by
  change (run C.gates (incidenceInput X Y)).getD (n + n + j) false = _
  have h1 := run_gate C.gates (incidenceInput X Y) j hj
  rw [incidenceInput_length] at h1
  rw [h1]
  congr 1
  apply List.map_congr_left
  intro w hw
  split_ifs with hlt
  · have hsplit : run C.gates (incidenceInput X Y) =
        run (C.gates.drop j) (run (C.gates.take j) (incidenceInput X Y)) := by
      rw [← run_append, List.take_append_drop]
    change _ = (run C.gates (incidenceInput X Y)).getD w false
    have hgd : (run (C.gates.drop j) (run (C.gates.take j) (incidenceInput X Y))).getD w false =
        (run (C.gates.take j) (incidenceInput X Y)).getD w false :=
      run_getD _ _ _ (by rw [run_length, incidenceInput_length, List.length_take]; omega)
    rw [hsplit, hgd]
  · rw [List.getD_eq_default]
    rw [run_length, incidenceInput_length, List.length_take]
    omega

lemma supportStep_length {m : ℕ} (s : List (Finset (Fin m))) (g : Gate) :
    (supportStep s g).length = s.length + 1 := by
  simp [supportStep]

lemma supports_length (m : ℕ) (C : Circuit) :
    (supports m C).length = m + C.gates.length := by
  have h : ∀ (gs : List Gate) (s : List (Finset (Fin m))),
      (gs.foldl supportStep s).length = s.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro s; simp
    | cons g gs ih => intro s; simp [List.foldl_cons, ih, supportStep_length]; omega
  unfold supports
  rw [h, List.length_ofFn]

lemma support_input (m : ℕ) (C : Circuit) (i : ℕ) (hi : i < m) :
    support m C i = ({⟨i, hi⟩} : Finset (Fin m)) := by
  have hfold : ∀ (gs : List Gate) (s : List (Finset (Fin m))), i < s.length →
      (gs.foldl supportStep s).getD i ∅ = s.getD i ∅ := by
    intro gs
    induction gs with
    | nil => intro s _; rfl
    | cons g gs ih =>
      intro s hs
      rw [List.foldl_cons, ih _ (by rw [supportStep_length]; omega), supportStep, List.getD_append _ _ _ _ hs]
  unfold support supports
  rw [hfold _ _ (by simp [hi])]
  have hof : (List.ofFn fun i : Fin m => ({i} : Finset (Fin m)))[i]? = some ({⟨i, hi⟩} : Finset (Fin m)) := by
    simp [List.getElem?_eq_getElem (by simp [hi] : i < (List.ofFn fun i : Fin m => ({i} : Finset (Fin m))).length)]
  rw [List.getD, hof]; rfl

lemma support_gate (m : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    support m C (m + j) =
      C.gates[j].inputs.foldr (fun w acc => operandSupport m C j w ∪ acc) ∅ := by
  have hfold_getD : ∀ (gs : List Gate) (s : List (Finset (Fin m))) (k : ℕ), k < s.length →
      (gs.foldl supportStep s).getD k ∅ = s.getD k ∅ := by
    intro gs
    induction gs with
    | nil => intro s _ _; rfl
    | cons g gs ih =>
      intro s k hk
      rw [List.foldl_cons, ih _ k (by rw [supportStep_length]; omega), supportStep, List.getD_append _ _ _ _ hk]
  have hfold_len : ∀ (gs : List Gate) (s : List (Finset (Fin m))),
      (gs.foldl supportStep s).length = s.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro s; simp
    | cons g gs ih => intro s; simp [List.foldl_cons, ih, supportStep_length]; omega
  set s0 : List (Finset (Fin m)) := List.ofFn fun i : Fin m => ({i} : Finset (Fin m))
  set s1 : List (Finset (Fin m)) := (C.gates.take j).foldl supportStep s0
  have hs1_len : s1.length = m + j := by
    dsimp only [s1]
    rw [hfold_len, List.length_ofFn, List.length_take]
    omega
  have hsplit : supports m C = (C.gates.drop (j + 1)).foldl supportStep (supportStep s1 C.gates[j]) := by
    unfold supports
    conv_lhs => rw [← List.take_append_drop j C.gates, List.drop_eq_getElem_cons hj, List.foldl_append, List.foldl_cons]
  have hget : support m C (m + j) = (supportStep s1 C.gates[j]).getD (m + j) ∅ := by
    unfold support
    rw [hsplit, hfold_getD _ _ _ (by rw [supportStep_length, hs1_len]; omega)]
  rw [hget, supportStep, ← hs1_len, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self, List.getD_cons_zero]
  congr 1
  ext w acc
  congr 1
  by_cases hw : w < m + j
  · have heq : s1.getD w ∅ = support m C w := by
      unfold support supports
      conv_rhs => rw [← List.take_append_drop j C.gates, List.foldl_append]
      exact (hfold_getD (C.gates.drop j) s1 w (by rw [hs1_len]; exact hw)).symm
    rw [operandSupport, if_pos hw, heq]
  · rw [operandSupport, if_neg hw, List.getD_eq_default s1 _ (by rw [hs1_len]; omega)]

lemma mem_foldr_union {α : Type*} [DecidableEq α] (l : List ℕ) (f : ℕ → Finset α) (x : α) :
    x ∈ l.foldr (fun w acc => f w ∪ acc) ∅ ↔ ∃ w ∈ l, x ∈ f w := by
  induction l with
  | nil => simp
  | cons a l ih => simp [Finset.mem_union, ih]

lemma mem_support_gate {m : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length) (x : Fin m) :
    x ∈ support m C (m + j) ↔ ∃ w ∈ C.gates[j].inputs, x ∈ operandSupport m C j w := by
  rw [support_gate m C j hj, mem_foldr_union]

lemma operandSupport_subset {m : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length) {w : ℕ}
    (hw : w ∈ C.gates[j].inputs) :
    operandSupport m C j w ⊆ support m C (m + j) := by
  intro x hx
  exact (mem_support_gate hj x).2 ⟨w, hw, hx⟩

lemma wval_eq_of_support {n : ℕ} {C : Circuit} :
    ∀ w < n + n + C.gates.length, ∀ X1 Y1 X2 Y2 : Finset (Fin n),
      (∀ k ∈ support (n + n) C w,
        (∀ p : Fin n, Fin.castAdd n p = k → (p ∈ X1 ↔ p ∈ X2)) ∧
        (∀ l : Fin n, Fin.natAdd n l = k → (l ∈ Y1 ↔ l ∈ Y2))) →
      wval n C w X1 Y1 = wval n C w X2 Y2 := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw X1 Y1 X2 Y2 hagree
    by_cases hw1 : w < n
    · have hk : Fin.castAdd n ⟨w, hw1⟩ ∈ support (n + n) C w := by
        rw [support_input (n + n) C w (by omega)]
        simp [Fin.ext_iff]
      have hp := (hagree _ hk).1 ⟨w, hw1⟩ rfl
      rw [wval_lt_in C w (by omega), wval_lt_in C w (by omega),
        incidenceInput_getD_left X1 Y1 w hw1, incidenceInput_getD_left X2 Y2 w hw1]
      simp [hp]
    · by_cases hw2 : w < n + n
      · have hk : Fin.natAdd n ⟨w - n, by omega⟩ ∈ support (n + n) C w := by
          rw [support_input (n + n) C w hw2]
          simp [Fin.ext_iff]
          omega
        have hl := (hagree _ hk).2 ⟨w - n, by omega⟩ rfl
        rw [wval_lt_in C w hw2, wval_lt_in C w hw2,
          incidenceInput_getD_right X1 Y1 w (by omega) hw2,
          incidenceInput_getD_right X2 Y2 w (by omega) hw2]
        simp [hl]
      · set j := w - (n + n)
        have hj : j < C.gates.length := by omega
        have hweq : w = n + n + j := by omega
        rw [hweq, wval_gate C j hj, wval_gate C j hj]
        congr 1
        apply List.map_congr_left
        intro u hu
        split_ifs with hlt
        · apply ih u (by omega) (by omega)
          intro k hk
          apply hagree k
          rw [hweq]
          exact operandSupport_subset (m := n + n) hj hu (by simp [operandSupport, hlt, hk])
        · rfl

lemma wval_const_of_empty_support {n : ℕ} {C : Circuit} {w : ℕ} (hw : w < n + n + C.gates.length)
    (hemp : support (n + n) C w = ∅) (X Y : Finset (Fin n)) :
    wval n C w X Y = wval n C w ∅ ∅ := by
  apply wval_eq_of_support w hw X Y ∅ ∅
  intro k hk
  rw [hemp] at hk
  cases hk

lemma fin_castAdd_not_mem_M {n : ℕ} (p : Fin n) :
    Fin.castAdd n p ∉ Finset.map (Fin.natAddEmb n) (Finset.univ : Finset (Fin n)) := by
  simp only [Finset.mem_map, Finset.mem_univ, true_and, Fin.natAddEmb_apply, Fin.ext_iff, Fin.val_natAdd, Fin.val_castAdd]
  rintro ⟨x, hx⟩
  omega

lemma fin_natAdd_mem_M {n : ℕ} (l : Fin n) :
    Fin.natAdd n l ∈ Finset.map (Fin.natAddEmb n) (Finset.univ : Finset (Fin n)) := by
  simp

lemma crossAnd_split {n : ℕ} {C : Circuit} {j : ℕ} (hj : j < C.gates.length)
    (hcross : ¬ IsCrossAnd (n + n) (Finset.map (Fin.natAddEmb n) Finset.univ) C j)
    (hop : C.gates[j].op = GateOp.and) (a b : ℕ) (hins : C.gates[j].inputs = [a, b]) :
    let M := Finset.map (Fin.natAddEmb n) (Finset.univ : Finset (Fin n))
    let Sa := operandSupport (n + n) C j a
    let Sb := operandSupport (n + n) C j b
    (Sa = ∅ ∨ Sb = ∅) ∨ (Disjoint Sa M ∧ Sb ⊆ M) ∨ (Disjoint Sb M ∧ Sa ⊆ M) := by
  intro M Sa Sb
  by_cases ha : Sa = ∅
  · exact Or.inl (Or.inl ha)
  · by_cases hb : Sb = ∅
    · exact Or.inl (Or.inr hb)
    · right
      have ha_ne : Sa.Nonempty := Finset.nonempty_iff_ne_empty.2 ha
      have hb_ne : Sb.Nonempty := Finset.nonempty_iff_ne_empty.2 hb
      have hgate : gateAt C j = C.gates[j] := by simp [gateAt, List.getD, hj]
      have hca : ¬ (((Sa ∩ M).Nonempty ∧ (Sb ∩ M).Nonempty) ∨ ((Sa \ M).Nonempty ∧ (Sb \ M).Nonempty)) := by
        intro h
        apply hcross
        refine ⟨by rw [hgate]; exact hop, by rw [hgate, hins]; rfl, ?_⟩
        simpa [Sa, Sb, hgate, hins] using h
      by_cases haM : (Sa ∩ M).Nonempty
      · right
        have hnbM : ¬ (Sb ∩ M).Nonempty := fun h => hca (Or.inl ⟨haM, h⟩)
        have hdisj : Disjoint Sb M := Finset.not_nonempty_iff_eq_empty.1 hnbM |> fun h => Finset.disjoint_iff_inter_eq_empty.2 h
        have hbdiff : (Sb \ M).Nonempty := by
          rcases hb_ne with ⟨x, hx⟩
          exact ⟨x, Finset.mem_sdiff.2 ⟨hx, fun hxM => Finset.disjoint_left.1 hdisj hx hxM⟩⟩
        have hna : ¬ (Sa \ M).Nonempty := fun h => hca (Or.inr ⟨h, hbdiff⟩)
        have hasub : Sa ⊆ M := Finset.sdiff_eq_empty_iff_subset.1 (Finset.not_nonempty_iff_eq_empty.1 hna)
        exact ⟨hdisj, hasub⟩
      · left
        have hdisja : Disjoint Sa M := Finset.disjoint_iff_inter_eq_empty.2 (Finset.not_nonempty_iff_eq_empty.1 haM)
        have hadiff : (Sa \ M).Nonempty := by
          rcases ha_ne with ⟨x, hx⟩
          exact ⟨x, Finset.mem_sdiff.2 ⟨hx, fun hxM => Finset.disjoint_left.1 hdisja hx hxM⟩⟩
        have hnb : ¬ (Sb \ M).Nonempty := fun h => hca (Or.inr ⟨hadiff, h⟩)
        have hbsub : Sb ⊆ M := Finset.sdiff_eq_empty_iff_subset.1 (Finset.not_nonempty_iff_eq_empty.1 hnb)
        exact ⟨hdisja, hbsub⟩

lemma pure_point_class {n : ℕ} {C : Circuit} (hmono : Monotone2 C)
    (hno : ∀ j < C.gates.length, ¬ IsCrossAnd (n + n) (Finset.map (Fin.natAddEmb n) Finset.univ) C j) :
    ∀ w < n + n + C.gates.length,
      Disjoint (support (n + n) C w) (Finset.map (Fin.natAddEmb n) Finset.univ) →
      wval n C w ∅ ∅ = false →
      ∀ X Y : Finset (Fin n), wval n C w X Y = true ↔ ∃ p ∈ X, p ∈ pts n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hdisj h00 X Y
    constructor
    · intro htrue
      by_cases hw1 : w < n
      · rw [wval_lt_in C w (by omega), incidenceInput_getD_left X Y w hw1] at htrue
        simp only [decide_eq_true_eq] at htrue
        refine ⟨⟨w, hw1⟩, htrue, ?_⟩
        simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [wval_lt_in C w (by omega), incidenceInput_getD_left {⟨w, hw1⟩} ∅ w hw1]
        simp
      · by_cases hw2 : w < n + n
        · have hm : Fin.natAdd n ⟨w - n, by omega⟩ ∈ support (n + n) C w := by
            rw [support_input (n + n) C w hw2]
            simp [Fin.ext_iff]; omega
          exact (Finset.disjoint_left.1 hdisj hm (fin_natAdd_mem_M _)).elim
        · set j := w - (n + n)
          have hj : j < C.gates.length := by omega
          have hweq : w = n + n + j := by omega
          have hgj := hmono C.gates[j] (List.getElem_mem hj)
          rcases hgj with ⟨hop, hlen⟩
          rcases hop with hop | hop
          · rcases hins : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l3⟩⟩⟩
            · rw [hweq, wval_gate C j hj, hins, hop] at h00
              cases h00
            · rw [hweq, wval_gate C j hj, hins, hop] at htrue h00
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq] at htrue h00
              split_ifs at htrue with ha
              · have had : Disjoint (support (n + n) C a) (Finset.map (Fin.natAddEmb n) Finset.univ) := by
                  refine Finset.disjoint_of_subset_left ?_ hdisj
                  rw [hweq]
                  simpa [operandSupport, ha] using operandSupport_subset (m := n + n) hj (w := a) (by rw [hins]; simp)
                have h00' : wval n C a ∅ ∅ = false := by simpa [ha] using h00
                rcases (ih a (by omega) (by omega) had h00' X Y).1 htrue with ⟨p, hpX, hp⟩
                refine ⟨p, hpX, ?_⟩
                simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
                rw [hweq, wval_gate C j hj, hins, hop]
                simpa [GateOp.eval, ha] using hp
            · rw [hweq, wval_gate C j hj, hins, hop] at htrue h00
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, id_eq] at htrue
              split_ifs at htrue with ha hb
              · have hsp := crossAnd_split hj (hno j hj) hop a b hins
                have hasub : operandSupport (n + n) C j a ⊆ support (n + n) C w := by
                  rw [hweq]; exact operandSupport_subset (m := n + n) hj (by rw [hins]; simp)
                have hbsub : operandSupport (n + n) C j b ⊆ support (n + n) C w := by
                  rw [hweq]; exact operandSupport_subset (m := n + n) hj (by rw [hins]; simp)
                have had : Disjoint (support (n + n) C a) (Finset.map (Fin.natAddEmb n) Finset.univ) := by
                  refine Finset.disjoint_of_subset_left ?_ hdisj
                  simpa [operandSupport, ha] using hasub
                have hbd : Disjoint (support (n + n) C b) (Finset.map (Fin.natAddEmb n) Finset.univ) := by
                  refine Finset.disjoint_of_subset_left ?_ hdisj
                  simpa [operandSupport, hb] using hbsub
                have h00_cases : wval n C a ∅ ∅ = false ∨ wval n C b ∅ ∅ = false := by
                  have h00' : (wval n C a ∅ ∅ && wval n C b ∅ ∅) = false := by
                    simpa [GateOp.eval, ha, hb] using h00
                  exact Bool.and_eq_false_iff.1 h00'
                have ha_or_hb_emp : support (n + n) C a = ∅ ∨ support (n + n) C b = ∅ := by
                  rcases hsp with (h | h) | ⟨_, h⟩ | ⟨_, h⟩
                  · left; simpa [operandSupport, ha] using h
                  · right; simpa [operandSupport, hb] using h
                  · right
                    have hb_sub_m : support (n + n) C b ⊆ Finset.map (Fin.natAddEmb n) Finset.univ := by
                      simpa [operandSupport, hb] using h
                    ext z; simp only [Finset.notMem_empty, iff_false]; intro hz; exact Finset.disjoint_left.1 hbd hz (hb_sub_m hz)
                  · left
                    have ha_sub_m : support (n + n) C a ⊆ Finset.map (Fin.natAddEmb n) Finset.univ := by
                      simpa [operandSupport, ha] using h
                    ext z; simp only [Finset.notMem_empty, iff_false]; intro hz; exact Finset.disjoint_left.1 had hz (ha_sub_m hz)
                rcases ha_or_hb_emp with hemp | hemp
                · have ha_all : ∀ X' Y', wval n C a X' Y' = true := by
                    intro X' Y'
                    rw [wval_const_of_empty_support (by omega) hemp X' Y', ← wval_const_of_empty_support (by omega) hemp X Y]
                    exact htrue.1
                  have hb0 : wval n C b ∅ ∅ = false := by
                    rcases h00_cases with ha0 | hb0
                    · rw [ha_all ∅ ∅] at ha0; cases ha0
                    · exact hb0
                  rcases (ih b (by omega) (by omega) hbd hb0 X Y).1 htrue.2 with ⟨p, hpX, hp⟩
                  refine ⟨p, hpX, ?_⟩
                  simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
                  rw [hweq, wval_gate C j hj, hins, hop]
                  simp [GateOp.eval, ha, hb, ha_all {p} ∅, hp]
                · have hb_all : ∀ X' Y', wval n C b X' Y' = true := by
                    intro X' Y'
                    rw [wval_const_of_empty_support (by omega) hemp X' Y', ← wval_const_of_empty_support (by omega) hemp X Y]
                    exact htrue.2
                  have ha0 : wval n C a ∅ ∅ = false := by
                    rcases h00_cases with ha0 | hb0
                    · exact ha0
                    · rw [hb_all ∅ ∅] at hb0; cases hb0
                  rcases (ih a (by omega) (by omega) had ha0 X Y).1 htrue.1 with ⟨p, hpX, hp⟩
                  refine ⟨p, hpX, ?_⟩
                  simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
                  rw [hweq, wval_gate C j hj, hins, hop]
                  simp [GateOp.eval, ha, hb, hb_all {p} ∅, hp]
              · simp at htrue
              · simp at htrue
              · simp at htrue
            · rw [hins] at hlen; simp at hlen
          · rcases hins : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l3⟩⟩⟩
            · rw [hweq, wval_gate C j hj, hins, hop] at htrue
              cases htrue
            · rw [hweq, wval_gate C j hj, hins, hop] at htrue h00
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq] at htrue h00
              split_ifs at htrue with ha
              · have had : Disjoint (support (n + n) C a) (Finset.map (Fin.natAddEmb n) Finset.univ) := by
                  refine Finset.disjoint_of_subset_left ?_ hdisj
                  rw [hweq]
                  simpa [operandSupport, ha] using operandSupport_subset (m := n + n) hj (w := a) (by rw [hins]; simp)
                have h00' : wval n C a ∅ ∅ = false := by simpa [ha] using h00
                rcases (ih a (by omega) (by omega) had h00' X Y).1 htrue with ⟨p, hpX, hp⟩
                refine ⟨p, hpX, ?_⟩
                simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
                rw [hweq, wval_gate C j hj, hins, hop]
                simpa [GateOp.eval, ha] using hp
            · rw [hweq, wval_gate C j hj, hins, hop] at htrue h00
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, id_eq] at htrue h00
              rcases htrue with h1 | h2
              · split_ifs at h1 with ha
                have had : Disjoint (support (n + n) C a) (Finset.map (Fin.natAddEmb n) Finset.univ) := by
                  refine Finset.disjoint_of_subset_left ?_ hdisj
                  rw [hweq]
                  simpa [operandSupport, ha] using operandSupport_subset (m := n + n) hj (w := a) (by rw [hins]; simp)
                have ha0 : wval n C a ∅ ∅ = false := by
                  by_contra hc
                  have hct : wval n C a ∅ ∅ = true := Bool.eq_true_of_not_eq_false hc
                  simp [ha, hct] at h00
                rcases (ih a (by omega) (by omega) had ha0 X Y).1 h1 with ⟨p, hpX, hp⟩
                refine ⟨p, hpX, ?_⟩
                simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
                rw [hweq, wval_gate C j hj, hins, hop]
                simp [GateOp.eval, ha, hp]
              · split_ifs at h2 with hb
                have hbd : Disjoint (support (n + n) C b) (Finset.map (Fin.natAddEmb n) Finset.univ) := by
                  refine Finset.disjoint_of_subset_left ?_ hdisj
                  rw [hweq]
                  simpa [operandSupport, hb] using operandSupport_subset (m := n + n) hj (w := b) (by rw [hins]; simp)
                have hb0 : wval n C b ∅ ∅ = false := by
                  by_contra hc
                  have hct : wval n C b ∅ ∅ = true := Bool.eq_true_of_not_eq_false hc
                  simp [hb, hct] at h00
                rcases (ih b (by omega) (by omega) hbd hb0 X Y).1 h2 with ⟨p, hpX, hp⟩
                refine ⟨p, hpX, ?_⟩
                simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
                rw [hweq, wval_gate C j hj, hins, hop]
                simp [GateOp.eval, hb, hp]
            · rw [hins] at hlen; simp at hlen
    · rintro ⟨p, hpX, hp⟩
      simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      exact wval_mono hmono (Finset.singleton_subset_iff.2 hpX) (Finset.empty_subset Y) w hp

lemma pure_line_class {n : ℕ} {C : Circuit} (hmono : Monotone2 C)
    (hno : ∀ j < C.gates.length, ¬ IsCrossAnd (n + n) (Finset.map (Fin.natAddEmb n) Finset.univ) C j) :
    ∀ w < n + n + C.gates.length,
      support (n + n) C w ⊆ Finset.map (Fin.natAddEmb n) Finset.univ →
      wval n C w ∅ ∅ = false →
      ∀ X Y : Finset (Fin n), wval n C w X Y = true ↔ ∃ l ∈ Y, l ∈ lns n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hsub h00 X Y
    constructor
    · intro htrue
      by_cases hw1 : w < n
      · have hk : Fin.castAdd n ⟨w, hw1⟩ ∈ support (n + n) C w := by
          rw [support_input (n + n) C w (by omega)]; simp [Fin.ext_iff]
        exact (fin_castAdd_not_mem_M ⟨w, hw1⟩ (hsub hk)).elim
      · by_cases hw2 : w < n + n
        · rw [wval_lt_in C w hw2, incidenceInput_getD_right _ _ _ (by omega) hw2] at htrue
          simp only [decide_eq_true_eq] at htrue
          refine ⟨⟨w - n, by omega⟩, htrue, ?_⟩
          simp only [lns, Finset.mem_filter, Finset.mem_univ, true_and]
          rw [wval_lt_in C w hw2, incidenceInput_getD_right _ _ _ (by omega) hw2]
          simp
        · set j := w - (n + n)
          have hj : j < C.gates.length := by omega
          have hweq : w = n + n + j := by omega
          have hgj := hmono C.gates[j] (List.getElem_mem hj)
          rcases hgj with ⟨hop, hlen⟩
          rcases hop with hop | hop
          · rcases hins : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l3⟩⟩⟩
            · rw [hweq, wval_gate C j hj, hins, hop] at h00; cases h00
            · rw [hweq, wval_gate C j hj, hins, hop] at htrue h00
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq] at htrue h00
              split_ifs at htrue with ha
              · have hasub : support (n + n) C a ⊆ Finset.map (Fin.natAddEmb n) Finset.univ := by
                  refine Finset.Subset.trans ?_ hsub
                  rw [hweq]; simpa [operandSupport, ha] using operandSupport_subset (m := n + n) hj (w := a) (by rw [hins]; simp)
                have h00' : wval n C a ∅ ∅ = false := by simpa [ha] using h00
                rcases (ih a (by omega) (by omega) hasub h00' X Y).1 htrue with ⟨l, hlY, hl⟩
                refine ⟨l, hlY, ?_⟩
                simp only [lns, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
                rw [hweq, wval_gate C j hj, hins, hop]
                simpa [GateOp.eval, ha] using hl
            · rw [hweq, wval_gate C j hj, hins, hop] at htrue h00
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, id_eq] at htrue
              split_ifs at htrue with ha hb
              · have hsp := crossAnd_split hj (hno j hj) hop a b hins
                have hasub : support (n + n) C a ⊆ Finset.map (Fin.natAddEmb n) Finset.univ := by
                  refine Finset.Subset.trans ?_ hsub
                  rw [hweq]; simpa [operandSupport, ha] using operandSupport_subset (m := n + n) hj (w := a) (by rw [hins]; simp)
                have hbsub : support (n + n) C b ⊆ Finset.map (Fin.natAddEmb n) Finset.univ := by
                  refine Finset.Subset.trans ?_ hsub
                  rw [hweq]; simpa [operandSupport, hb] using operandSupport_subset (m := n + n) hj (w := b) (by rw [hins]; simp)
                have h00_cases : wval n C a ∅ ∅ = false ∨ wval n C b ∅ ∅ = false := by
                  have h00' : (wval n C a ∅ ∅ && wval n C b ∅ ∅) = false := by
                    simpa [GateOp.eval, ha, hb] using h00
                  exact Bool.and_eq_false_iff.1 h00'
                have ha_or_hb_emp : support (n + n) C a = ∅ ∨ support (n + n) C b = ∅ := by
                  rcases hsp with (h | h) | ⟨h, _⟩ | ⟨h, _⟩
                  · left; simpa [operandSupport, ha] using h
                  · right; simpa [operandSupport, hb] using h
                  · left
                    have ha_disj_m : Disjoint (support (n + n) C a) (Finset.map (Fin.natAddEmb n) Finset.univ) := by
                      simpa [operandSupport, ha] using h
                    ext z; simp only [Finset.notMem_empty, iff_false]; intro hz; exact Finset.disjoint_left.1 ha_disj_m hz (hasub hz)
                  · right
                    have hb_disj_m : Disjoint (support (n + n) C b) (Finset.map (Fin.natAddEmb n) Finset.univ) := by
                      simpa [operandSupport, hb] using h
                    ext z; simp only [Finset.notMem_empty, iff_false]; intro hz; exact Finset.disjoint_left.1 hb_disj_m hz (hbsub hz)
                rcases ha_or_hb_emp with hemp | hemp
                · have ha_all : ∀ X' Y', wval n C a X' Y' = true := by
                    intro X' Y'
                    rw [wval_const_of_empty_support (by omega) hemp X' Y', ← wval_const_of_empty_support (by omega) hemp X Y]
                    exact htrue.1
                  have hb0 : wval n C b ∅ ∅ = false := by
                    rcases h00_cases with ha0 | hb0
                    · rw [ha_all ∅ ∅] at ha0; cases ha0
                    · exact hb0
                  rcases (ih b (by omega) (by omega) hbsub hb0 X Y).1 htrue.2 with ⟨l, hlY, hl⟩
                  refine ⟨l, hlY, ?_⟩
                  simp only [lns, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
                  rw [hweq, wval_gate C j hj, hins, hop]
                  simp [GateOp.eval, ha, hb, ha_all ∅ {l}, hl]
                · have hb_all : ∀ X' Y', wval n C b X' Y' = true := by
                    intro X' Y'
                    rw [wval_const_of_empty_support (by omega) hemp X' Y', ← wval_const_of_empty_support (by omega) hemp X Y]
                    exact htrue.2
                  have ha0 : wval n C a ∅ ∅ = false := by
                    rcases h00_cases with ha0 | hb0
                    · exact ha0
                    · rw [hb_all ∅ ∅] at hb0; cases hb0
                  rcases (ih a (by omega) (by omega) hasub ha0 X Y).1 htrue.1 with ⟨l, hlY, hl⟩
                  refine ⟨l, hlY, ?_⟩
                  simp only [lns, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
                  rw [hweq, wval_gate C j hj, hins, hop]
                  simp [GateOp.eval, ha, hb, hb_all ∅ {l}, hl]
              · simp at htrue
              · simp at htrue
              · simp at htrue
            · rw [hins] at hlen; simp at hlen
          · rcases hins : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l3⟩⟩⟩
            · rw [hweq, wval_gate C j hj, hins, hop] at htrue; cases htrue
            · rw [hweq, wval_gate C j hj, hins, hop] at htrue h00
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq] at htrue h00
              split_ifs at htrue with ha
              · have hasub : support (n + n) C a ⊆ Finset.map (Fin.natAddEmb n) Finset.univ := by
                  refine Finset.Subset.trans ?_ hsub
                  rw [hweq]; simpa [operandSupport, ha] using operandSupport_subset (m := n + n) hj (w := a) (by rw [hins]; simp)
                have h00' : wval n C a ∅ ∅ = false := by simpa [ha] using h00
                rcases (ih a (by omega) (by omega) hasub h00' X Y).1 htrue with ⟨l, hlY, hl⟩
                refine ⟨l, hlY, ?_⟩
                simp only [lns, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
                rw [hweq, wval_gate C j hj, hins, hop]
                simpa [GateOp.eval, ha] using hl
            · rw [hweq, wval_gate C j hj, hins, hop] at htrue h00
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, id_eq] at htrue h00
              rcases htrue with h1 | h2
              · split_ifs at h1 with ha
                have hasub : support (n + n) C a ⊆ Finset.map (Fin.natAddEmb n) Finset.univ := by
                  refine Finset.Subset.trans ?_ hsub
                  rw [hweq]; simpa [operandSupport, ha] using operandSupport_subset (m := n + n) hj (w := a) (by rw [hins]; simp)
                have ha0 : wval n C a ∅ ∅ = false := by
                  by_contra hc
                  have hct : wval n C a ∅ ∅ = true := Bool.eq_true_of_not_eq_false hc
                  simp [ha, hct] at h00
                rcases (ih a (by omega) (by omega) hasub ha0 X Y).1 h1 with ⟨l, hlY, hl⟩
                refine ⟨l, hlY, ?_⟩
                simp only [lns, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
                rw [hweq, wval_gate C j hj, hins, hop]
                simp [GateOp.eval, ha, hl]
              · split_ifs at h2 with hb
                have hbsub : support (n + n) C b ⊆ Finset.map (Fin.natAddEmb n) Finset.univ := by
                  refine Finset.Subset.trans ?_ hsub
                  rw [hweq]; simpa [operandSupport, hb] using operandSupport_subset (m := n + n) hj (w := b) (by rw [hins]; simp)
                have hb0 : wval n C b ∅ ∅ = false := by
                  by_contra hc
                  have hct : wval n C b ∅ ∅ = true := Bool.eq_true_of_not_eq_false hc
                  simp [hb, hct] at h00
                rcases (ih b (by omega) (by omega) hbsub hb0 X Y).1 h2 with ⟨l, hlY, hl⟩
                refine ⟨l, hlY, ?_⟩
                simp only [lns, Finset.mem_filter, Finset.mem_univ, true_and] at hl ⊢
                rw [hweq, wval_gate C j hj, hins, hop]
                simp [GateOp.eval, hb, hl]
            · rw [hins] at hlen; simp at hlen
    · rintro ⟨l, hlY, hl⟩
      simp only [lns, Finset.mem_filter, Finset.mem_univ, true_and] at hl
      exact wval_mono hmono (Finset.empty_subset X) (Finset.singleton_subset_iff.2 hlY) w hl

def pick {n : ℕ} (S : Finset (Fin n)) (d : Fin n) : Fin n :=
  if h : S.Nonempty then S.min' h else d

lemma pick_mem {n : ℕ} {S : Finset (Fin n)} (hS : S.Nonempty) (d : Fin n) :
    pick S d ∈ S := by
  simp [pick, hS, Finset.min'_mem]

lemma pick_eq_of_singleton {n : ℕ} {S : Finset (Fin n)} {x : Fin n} (hS : S = {x}) (d : Fin n) :
    pick S d = x := by
  have hne : S.Nonempty := by
    rw [hS]
    exact Finset.singleton_nonempty x
  have hm : pick S d ∈ ({x} : Finset (Fin n)) := hS ▸ pick_mem hne d
  exact Finset.mem_singleton.1 hm

def effPts (n : ℕ) (C : Circuit) (w u : ℕ) : Finset (Fin n) :=
  if u < w then pts n C u else ∅

def effLns (n : ℕ) (C : Circuit) (w u : ℕ) : Finset (Fin n) :=
  if u < w then lns n C u else ∅

noncomputable def assignTriple (n : ℕ) (d0 : Fin n) (C : Circuit) (j : Fin C.size) : Fin n × Fin n × Fin 3 :=
  let g := C.gates[j.val]
  let w := n + n + j.val
  let M := Finset.map (Fin.natAddEmb n) (Finset.univ : Finset (Fin n))
  match g.op, g.inputs with
  | GateOp.or, [a, b] =>
    if Disjoint (support (n + n) C w) M then
      let Pa := effPts n C w a
      let Pb := effPts n C w b
      if Pa.card = 1 ∧ (Pb \ Pa).Nonempty then
        (pick Pa d0, pick (Pb \ Pa) d0, 1)
      else if Pb.card = 1 ∧ (Pa \ Pb).Nonempty then
        (pick Pb d0, pick (Pa \ Pb) d0, 1)
      else (d0, d0, 0)
    else if support (n + n) C w ⊆ M then
      let La := effLns n C w a
      let Lb := effLns n C w b
      if La.card = 1 ∧ (Lb \ La).Nonempty then
        (pick La d0, pick (Lb \ La) d0, 2)
      else if Lb.card = 1 ∧ (La \ Lb).Nonempty then
        (pick Lb d0, pick (La \ Lb) d0, 2)
      else (d0, d0, 0)
    else (d0, d0, 0)
  | GateOp.and, [a, b] =>
    if a < w ∧ b < w ∧ Disjoint (support (n + n) C a) M ∧ support (n + n) C b ⊆ M ∧
        (pts n C a).card = 1 ∧ (lns n C b).card = 1 then
      (pick (pts n C a) d0, pick (lns n C b) d0, 0)
    else if a < w ∧ b < w ∧ Disjoint (support (n + n) C b) M ∧ support (n + n) C a ⊆ M ∧
        (pts n C b).card = 1 ∧ (lns n C a).card = 1 then
      (pick (pts n C b) d0, pick (lns n C a) d0, 0)
    else (d0, d0, 0)
  | _, _ => (d0, d0, 0)

lemma pure_point_cover {n : ℕ} {d0 : Fin n} {C : Circuit} (hmono : Monotone2 C)
    (hno : ∀ j < C.gates.length, ¬ IsCrossAnd (n + n) (Finset.map (Fin.natAddEmb n) Finset.univ) C j) :
    ∀ w < n + n + C.gates.length,
      Disjoint (support (n + n) C w) (Finset.map (Fin.natAddEmb n) Finset.univ) →
      wval n C w ∅ ∅ = false →
      2 ≤ (pts n C w).card →
      ∀ p ∈ pts n C w, ∃ j : Fin C.size,
        (assignTriple n d0 C j).2.2 = 1 ∧
        (assignTriple n d0 C j).1 ≠ (assignTriple n d0 C j).2.1 ∧
        (p = (assignTriple n d0 C j).1 ∨ p = (assignTriple n d0 C j).2.1) ∧
        (assignTriple n d0 C j).1 ∈ pts n C w ∧
        (assignTriple n d0 C j).2.1 ∈ pts n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hdisj h00 hcard p hp
    by_cases hw1 : w < n
    · have hsub : pts n C w ⊆ {⟨w, hw1⟩} := by
        intro q hq
        simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        rw [wval_lt_in C w (by omega), incidenceInput_getD_left {q} ∅ w hw1] at hq
        simp only [decide_eq_true_eq, Finset.mem_singleton] at hq ⊢
        exact Fin.ext (Fin.val_eq_of_eq hq).symm
      have hc1 : (pts n C w).card ≤ 1 := le_trans (Finset.card_le_card hsub) (by simp)
      omega
    · by_cases hw2 : w < n + n
      · have hm : Fin.natAdd n ⟨w - n, by omega⟩ ∈ support (n + n) C w := by
          rw [support_input (n + n) C w hw2]; simp [Fin.ext_iff]; omega
        exact (Finset.disjoint_left.1 hdisj hm (fin_natAdd_mem_M _)).elim
      · set j := w - (n + n)
        have hj : j < C.gates.length := by omega
        have hweq : w = n + n + j := by omega
        have hgj := hmono C.gates[j] (List.getElem_mem hj)
        rcases hgj with ⟨hop, hlen⟩
        rcases hop with hop | hop
        · rcases hins : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l3⟩⟩⟩
          · rw [hweq, wval_gate C j hj, hins, hop] at h00; cases h00
          · rw [hweq, wval_gate C j hj, hins, hop] at h00
            by_cases ha : a < w
            · have hpts : pts n C w = pts n C a := by
                ext q
                simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and]
                rw [hweq, wval_gate C j hj, hins, hop]
                simp [GateOp.eval, (by omega : a < n + n + j)]
              have had : Disjoint (support (n + n) C a) (Finset.map (Fin.natAddEmb n) Finset.univ) := by
                refine Finset.disjoint_of_subset_left ?_ hdisj
                rw [hweq]; simpa [operandSupport, (by omega : a < n + n + j)] using operandSupport_subset (m := n + n) hj (w := a) (by rw [hins]; simp)
              have h00' : wval n C a ∅ ∅ = false := by
                simpa [GateOp.eval, (by omega : a < n + n + j)] using h00
              rw [hpts] at hcard hp ⊢
              exact ih a ha (by omega) had h00' hcard p hp
            · have hpts : pts n C w = ∅ := by
                ext q
                simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
                rw [hweq, wval_gate C j hj, hins, hop]
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
                rw [if_neg (by omega : ¬ a < n + n + j)]
                simp
              rw [hpts] at hcard; simp at hcard
          · rw [hweq, wval_gate C j hj, hins, hop] at h00
            by_cases hab : a < w ∧ b < w
            · have hsp := crossAnd_split hj (hno j hj) hop a b hins
              have hasub : operandSupport (n + n) C j a ⊆ support (n + n) C w := by
                rw [hweq]; exact operandSupport_subset (m := n + n) hj (by rw [hins]; simp)
              have hbsub : operandSupport (n + n) C j b ⊆ support (n + n) C w := by
                rw [hweq]; exact operandSupport_subset (m := n + n) hj (by rw [hins]; simp)
              have ha_lt : a < n + n + j := by omega
              have hb_lt : b < n + n + j := by omega
              have had : Disjoint (support (n + n) C a) (Finset.map (Fin.natAddEmb n) Finset.univ) :=
                Finset.disjoint_of_subset_left (by simpa [operandSupport, ha_lt] using hasub) hdisj
              have hbd : Disjoint (support (n + n) C b) (Finset.map (Fin.natAddEmb n) Finset.univ) :=
                Finset.disjoint_of_subset_left (by simpa [operandSupport, hb_lt] using hbsub) hdisj
              have ha_or_hb_emp : support (n + n) C a = ∅ ∨ support (n + n) C b = ∅ := by
                rcases hsp with (h | h) | ⟨_, h⟩ | ⟨_, h⟩
                · left; simpa [operandSupport, ha_lt] using h
                · right; simpa [operandSupport, hb_lt] using h
                · right
                  have hb_sub_m : support (n + n) C b ⊆ Finset.map (Fin.natAddEmb n) Finset.univ := by
                    simpa [operandSupport, hb_lt] using h
                  ext z; simp only [Finset.notMem_empty, iff_false]; intro hz; exact Finset.disjoint_left.1 hbd hz (hb_sub_m hz)
                · left
                  have ha_sub_m : support (n + n) C a ⊆ Finset.map (Fin.natAddEmb n) Finset.univ := by
                    simpa [operandSupport, ha_lt] using h
                  ext z; simp only [Finset.notMem_empty, iff_false]; intro hz; exact Finset.disjoint_left.1 had hz (ha_sub_m hz)
              have hnonempty : (pts n C w).Nonempty := Finset.card_pos.1 (by omega)
              rcases hnonempty with ⟨q0, hq0⟩
              simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and] at hq0
              rw [hweq, wval_gate C j hj, hins, hop] at hq0
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, ha_lt, hb_lt, ↓reduceIte, id_eq] at hq0
              rcases ha_or_hb_emp with hemp | hemp
              · have ha_all : ∀ X' Y', wval n C a X' Y' = true := by
                  intro X' Y'
                  rw [wval_const_of_empty_support (by omega) hemp X' Y', ← wval_const_of_empty_support (by omega) hemp {q0} ∅]
                  exact hq0.1
                have hpts : pts n C w = pts n C b := by
                  ext q
                  simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and]
                  rw [hweq, wval_gate C j hj, hins, hop]
                  simp [GateOp.eval, ha_lt, hb_lt, ha_all {q} ∅]
                have hb0 : wval n C b ∅ ∅ = false := by
                  simp [GateOp.eval, ha_lt, hb_lt, ha_all ∅ ∅] at h00; exact h00
                rw [hpts] at hcard hp ⊢
                exact ih b hab.2 (by omega) hbd hb0 hcard p hp
              · have hb_all : ∀ X' Y', wval n C b X' Y' = true := by
                  intro X' Y'
                  rw [wval_const_of_empty_support (by omega) hemp X' Y', ← wval_const_of_empty_support (by omega) hemp {q0} ∅]
                  exact hq0.2
                have hpts : pts n C w = pts n C a := by
                  ext q
                  simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and]
                  rw [hweq, wval_gate C j hj, hins, hop]
                  simp [GateOp.eval, ha_lt, hb_lt, hb_all {q} ∅]
                have ha0 : wval n C a ∅ ∅ = false := by
                  simp [GateOp.eval, ha_lt, hb_lt, hb_all ∅ ∅] at h00; exact h00
                rw [hpts] at hcard hp ⊢
                exact ih a hab.1 (by omega) had ha0 hcard p hp
            · have hpts : pts n C w = ∅ := by
                ext q
                simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
                rw [hweq, wval_gate C j hj, hins, hop]
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
                by_cases ha : a < w <;> by_cases hb : b < w
                · exact (hab ⟨ha, hb⟩).elim
                · rw [if_neg (by omega : ¬ b < n + n + j)]; simp
                · rw [if_neg (by omega : ¬ a < n + n + j)]; simp
                · rw [if_neg (by omega : ¬ a < n + n + j)]; simp
              rw [hpts] at hcard; simp at hcard
          · rw [hins] at hlen; simp at hlen
        · rcases hins : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l3⟩⟩⟩
          · have hpts : pts n C w = ∅ := by
              ext q
              simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
              rw [hweq, wval_gate C j hj, hins, hop]
              simp [GateOp.eval]
            rw [hpts] at hcard; simp at hcard
          · rw [hweq, wval_gate C j hj, hins, hop] at h00
            by_cases ha : a < w
            · have hpts : pts n C w = pts n C a := by
                ext q
                simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and]
                rw [hweq, wval_gate C j hj, hins, hop]
                simp [GateOp.eval, (by omega : a < n + n + j)]
              have had : Disjoint (support (n + n) C a) (Finset.map (Fin.natAddEmb n) Finset.univ) := by
                refine Finset.disjoint_of_subset_left ?_ hdisj
                rw [hweq]; simpa [operandSupport, (by omega : a < n + n + j)] using operandSupport_subset (m := n + n) hj (w := a) (by rw [hins]; simp)
              have h00' : wval n C a ∅ ∅ = false := by
                simpa [GateOp.eval, (by omega : a < n + n + j)] using h00
              rw [hpts] at hcard hp ⊢
              exact ih a ha (by omega) had h00' hcard p hp
            · have hpts : pts n C w = ∅ := by
                ext q
                simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
                rw [hweq, wval_gate C j hj, hins, hop]
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
                rw [if_neg (by omega : ¬ a < n + n + j)]
                simp
              rw [hpts] at hcard; simp at hcard
          · set Pa := effPts n C w a
            set Pb := effPts n C w b
            have hpts_union : pts n C w = Pa ∪ Pb := by
              ext q
              dsimp only [Pa, Pb]
              simp only [pts, effPts, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
              rw [hweq, wval_gate C j hj, hins, hop]
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, id_eq]
              have ha_iff : a < n + n + j ↔ a < w := by omega
              have hb_iff : b < n + n + j ↔ b < w := by omega
              by_cases ha : a < w <;> by_cases hb : b < w <;>
                simp [GateOp.eval, ha, hb, ha_iff, hb_iff]
            have ha_sub : Pa ⊆ pts n C w := by rw [hpts_union]; exact Finset.subset_union_left
            have hb_sub : Pb ⊆ pts n C w := by rw [hpts_union]; exact Finset.subset_union_right
            have lift_a : ∀ (j' : Fin C.size),
                ((assignTriple n d0 C j').2.2 = 1 ∧ (assignTriple n d0 C j').1 ≠ (assignTriple n d0 C j').2.1 ∧
                  (p = (assignTriple n d0 C j').1 ∨ p = (assignTriple n d0 C j').2.1) ∧
                  (assignTriple n d0 C j').1 ∈ Pa ∧ (assignTriple n d0 C j').2.1 ∈ Pa) →
                ∃ j'' : Fin C.size,
                  (assignTriple n d0 C j'').2.2 = 1 ∧ (assignTriple n d0 C j'').1 ≠ (assignTriple n d0 C j'').2.1 ∧
                  (p = (assignTriple n d0 C j'').1 ∨ p = (assignTriple n d0 C j'').2.1) ∧
                  (assignTriple n d0 C j'').1 ∈ pts n C w ∧ (assignTriple n d0 C j'').2.1 ∈ pts n C w :=
              fun j' ⟨h1, h2, h3, h4, h5⟩ => ⟨j', h1, h2, h3, ha_sub h4, ha_sub h5⟩
            have lift_b : ∀ (j' : Fin C.size),
                ((assignTriple n d0 C j').2.2 = 1 ∧ (assignTriple n d0 C j').1 ≠ (assignTriple n d0 C j').2.1 ∧
                  (p = (assignTriple n d0 C j').1 ∨ p = (assignTriple n d0 C j').2.1) ∧
                  (assignTriple n d0 C j').1 ∈ Pb ∧ (assignTriple n d0 C j').2.1 ∈ Pb) →
                ∃ j'' : Fin C.size,
                  (assignTriple n d0 C j'').2.2 = 1 ∧ (assignTriple n d0 C j'').1 ≠ (assignTriple n d0 C j'').2.1 ∧
                  (p = (assignTriple n d0 C j'').1 ∨ p = (assignTriple n d0 C j'').2.1) ∧
                  (assignTriple n d0 C j'').1 ∈ pts n C w ∧ (assignTriple n d0 C j'').2.1 ∈ pts n C w :=
              fun j' ⟨h1, h2, h3, h4, h5⟩ => ⟨j', h1, h2, h3, hb_sub h4, hb_sub h5⟩
            by_cases ha2 : 2 ≤ Pa.card
            · have ha_lt : a < w := by
                by_contra hna
                have : Pa = ∅ := by simp [Pa, effPts, hna]
                rw [this] at ha2; simp at ha2
              have had : Disjoint (support (n + n) C a) (Finset.map (Fin.natAddEmb n) Finset.univ) := by
                refine Finset.disjoint_of_subset_left ?_ hdisj
                rw [hweq]; simpa [operandSupport, (by omega : a < n + n + j)] using operandSupport_subset (m := n + n) hj (w := a) (by rw [hins]; simp)
              have ha0 : wval n C a ∅ ∅ = false := by
                rw [hweq, wval_gate C j hj, hins, hop] at h00
                by_contra hc
                have hct : wval n C a ∅ ∅ = true := Bool.eq_true_of_not_eq_false hc
                simp [GateOp.eval, (by omega : a < n + n + j), hct] at h00
              have hPa_eq : Pa = pts n C a := by simp [Pa, effPts, ha_lt]
              have ha2' := ha2
              rw [hPa_eq] at ha2'
              by_cases hpPa : p ∈ Pa
              · rw [hPa_eq] at hpPa
                rcases ih a ha_lt (by omega) had ha0 ha2' p hpPa with ⟨j', hj'⟩
                exact lift_a j' (by simpa [hPa_eq] using hj')
              · have hpPb : p ∈ Pb := by
                  rw [hpts_union, Finset.mem_union] at hp
                  exact hp.resolve_left hpPa
                by_cases hb2 : 2 ≤ Pb.card
                · have hb_lt : b < w := by
                    by_contra hnb
                    have : Pb = ∅ := by simp [Pb, effPts, hnb]
                    rw [this] at hb2; simp at hb2
                  have hbd : Disjoint (support (n + n) C b) (Finset.map (Fin.natAddEmb n) Finset.univ) := by
                    refine Finset.disjoint_of_subset_left ?_ hdisj
                    rw [hweq]; simpa [operandSupport, (by omega : b < n + n + j)] using operandSupport_subset (m := n + n) hj (w := b) (by rw [hins]; simp)
                  have hb0 : wval n C b ∅ ∅ = false := by
                    rw [hweq, wval_gate C j hj, hins, hop] at h00
                    by_contra hc
                    have hct : wval n C b ∅ ∅ = true := Bool.eq_true_of_not_eq_false hc
                    simp [GateOp.eval, (by omega : b < n + n + j), hct] at h00
                  have hPb_eq : Pb = pts n C b := by simp [Pb, effPts, hb_lt]
                  have hb2' := hb2
                  rw [hPb_eq] at hb2'
                  rw [hPb_eq] at hpPb
                  rcases ih b hb_lt (by omega) hbd hb0 hb2' p hpPb with ⟨j', hj'⟩
                  exact lift_b j' (by simpa [hPb_eq] using hj')
                · have hb_card1 : Pb.card = 1 := by
                    have hpos : 0 < Pb.card := Finset.card_pos.2 ⟨p, hpPb⟩
                    omega
                  have hPa_diff : (Pa \ Pb).Nonempty := by
                    have hle : (Pa ∩ Pb).card ≤ 1 := le_trans (Finset.card_le_card Finset.inter_subset_right) (by omega)
                    have hdiff : 1 ≤ (Pa \ Pb).card := by
                      have hsum := Finset.card_sdiff_add_card_inter Pa Pb
                      omega
                    exact Finset.card_pos.1 (by omega)
                  have ha_not1 : ¬ (Pa.card = 1 ∧ (Pb \ Pa).Nonempty) := by omega
                  refine ⟨⟨j, hj⟩, ?_⟩
                  have hassign : assignTriple n d0 C ⟨j, hj⟩ = (pick Pb d0, pick (Pa \ Pb) d0, 1) := by
                    dsimp only [assignTriple]
                    rw [hop, hins]
                    simp only [← hweq]
                    rw [if_pos hdisj]
                    simp only [Pa, Pb]
                    rw [if_neg ha_not1, if_pos ⟨hb_card1, hPa_diff⟩]
                  rw [hassign]
                  have hPb_sing : Pb = {p} := Finset.card_eq_one.1 hb_card1 |>.elim fun q hq => by
                    rw [hq, Finset.mem_singleton] at hpPb; subst hpPb; exact hq
                  have hp1 : pick Pb d0 = p := pick_eq_of_singleton hPb_sing d0
                  have hqmem : pick (Pa \ Pb) d0 ∈ Pa \ Pb := pick_mem hPa_diff d0
                  rw [Finset.mem_sdiff] at hqmem
                  have hne : p ≠ pick (Pa \ Pb) d0 := fun heq => hqmem.2 (by rw [← heq]; exact hpPb)
                  exact ⟨rfl, by rw [hp1]; exact hne, Or.inl hp1.symm, by rw [hp1]; exact hp, ha_sub hqmem.1⟩
            · by_cases hb2 : 2 ≤ Pb.card
              · have hb_lt : b < w := by
                  by_contra hnb
                  have : Pb = ∅ := by simp [Pb, effPts, hnb]
                  rw [this] at hb2; simp at hb2
                have hbd : Disjoint (support (n + n) C b) (Finset.map (Fin.natAddEmb n) Finset.univ) := by
                  refine Finset.disjoint_of_subset_left ?_ hdisj
                  rw [hweq]; simpa [operandSupport, (by omega : b < n + n + j)] using operandSupport_subset (m := n + n) hj (w := b) (by rw [hins]; simp)
                have hb0 : wval n C b ∅ ∅ = false := by
                  rw [hweq, wval_gate C j hj, hins, hop] at h00
                  by_contra hc
                  have hct : wval n C b ∅ ∅ = true := Bool.eq_true_of_not_eq_false hc
                  simp [GateOp.eval, (by omega : b < n + n + j), hct] at h00
                have hPb_eq : Pb = pts n C b := by simp [Pb, effPts, hb_lt]
                have hb2' := hb2
                rw [hPb_eq] at hb2'
                by_cases hpPb : p ∈ Pb
                · rw [hPb_eq] at hpPb
                  rcases ih b hb_lt (by omega) hbd hb0 hb2' p hpPb with ⟨j', hj'⟩
                  exact lift_b j' (by simpa [hPb_eq] using hj')
                · have hpPa : p ∈ Pa := by
                    rw [hpts_union, Finset.mem_union] at hp
                    exact hp.resolve_right hpPb
                  have ha_card1 : Pa.card = 1 := by
                    have hpos : 0 < Pa.card := Finset.card_pos.2 ⟨p, hpPa⟩
                    omega
                  have hPb_diff : (Pb \ Pa).Nonempty := by
                    have hle : (Pb ∩ Pa).card ≤ 1 := le_trans (Finset.card_le_card Finset.inter_subset_right) (by omega)
                    have hdiff : 1 ≤ (Pb \ Pa).card := by
                      have hsum := Finset.card_sdiff_add_card_inter Pb Pa
                      omega
                    exact Finset.card_pos.1 (by omega)
                  refine ⟨⟨j, hj⟩, ?_⟩
                  have hassign : assignTriple n d0 C ⟨j, hj⟩ = (pick Pa d0, pick (Pb \ Pa) d0, 1) := by
                    dsimp only [assignTriple]
                    rw [hop, hins]
                    simp only [← hweq]
                    rw [if_pos hdisj]
                    simp only [Pa, Pb]
                    rw [if_pos ⟨ha_card1, hPb_diff⟩]
                  rw [hassign]
                  have hPa_sing : Pa = {p} := Finset.card_eq_one.1 ha_card1 |>.elim fun q hq => by
                    rw [hq, Finset.mem_singleton] at hpPa; subst hpPa; exact hq
                  have hp1 : pick Pa d0 = p := pick_eq_of_singleton hPa_sing d0
                  have hqmem : pick (Pb \ Pa) d0 ∈ Pb \ Pa := pick_mem hPb_diff d0
                  rw [Finset.mem_sdiff] at hqmem
                  have hne : p ≠ pick (Pb \ Pa) d0 := fun heq => hqmem.2 (by rw [← heq]; exact hpPa)
                  exact ⟨rfl, by rw [hp1]; exact hne, Or.inl hp1.symm, by rw [hp1]; exact hp, hb_sub hqmem.1⟩
              · have ha1 : Pa.card = 1 := by
                  have hle : (Pa ∪ Pb).card ≤ Pa.card + Pb.card := Finset.card_union_le Pa Pb
                  rw [← hpts_union] at hle
                  omega
                have hb1 : Pb.card = 1 := by
                  have hle : (Pa ∪ Pb).card ≤ Pa.card + Pb.card := Finset.card_union_le Pa Pb
                  rw [← hpts_union] at hle
                  omega
                have hdisj_ab : Disjoint Pa Pb := by
                  by_contra hnd
                  rcases Finset.not_disjoint_iff.1 hnd with ⟨q, hqa, hqb⟩
                  have hpa' : Pa = {q} := Finset.card_eq_one.1 ha1 |>.elim fun x hx => by rw [hx, Finset.mem_singleton] at hqa; subst hqa; exact hx
                  have hpb' : Pb = {q} := Finset.card_eq_one.1 hb1 |>.elim fun x hx => by rw [hx, Finset.mem_singleton] at hqb; subst hqb; exact hx
                  rw [hpts_union, hpa', hpb', Finset.union_idempotent, Finset.card_singleton] at hcard
                  omega
                have hPb_diff : (Pb \ Pa).Nonempty := by
                  rw [Finset.sdiff_eq_self_iff_disjoint.2 hdisj_ab.symm]
                  exact Finset.card_pos.1 (by omega)
                have hPa_diff : (Pa \ Pb).Nonempty := by
                  rw [Finset.sdiff_eq_self_iff_disjoint.2 hdisj_ab]
                  exact Finset.card_pos.1 (by omega)
                refine ⟨⟨j, hj⟩, ?_⟩
                have hassign : assignTriple n d0 C ⟨j, hj⟩ = (pick Pa d0, pick (Pb \ Pa) d0, 1) := by
                  dsimp only [assignTriple]
                  rw [hop, hins]
                  simp only [← hweq]
                  rw [if_pos hdisj]
                  simp only [Pa, Pb]
                  rw [if_pos ⟨ha1, hPb_diff⟩]
                rw [hassign]
                have hp1 : pick Pa d0 ∈ Pa := pick_mem (Finset.card_pos.1 (by omega)) d0
                have hq1 : pick (Pb \ Pa) d0 ∈ Pb \ Pa := pick_mem hPb_diff d0
                rw [Finset.mem_sdiff] at hq1
                have hne : pick Pa d0 ≠ pick (Pb \ Pa) d0 := fun heq => hq1.2 (by rw [← heq]; exact hp1)
                have hp_or : p = pick Pa d0 ∨ p = pick (Pb \ Pa) d0 := by
                  rw [hpts_union, Finset.mem_union] at hp
                  rcases hp with hpa | hpb
                  · left
                    have hPa_sing : Pa = {p} := Finset.card_eq_one.1 ha1 |>.elim fun x hx => by rw [hx, Finset.mem_singleton] at hpa; subst hpa; exact hx
                    exact (pick_eq_of_singleton hPa_sing d0).symm
                  · right
                    have hPb_sing : Pb = {p} := Finset.card_eq_one.1 hb1 |>.elim fun x hx => by rw [hx, Finset.mem_singleton] at hpb; subst hpb; exact hx
                    have : Pb \ Pa = {p} := by
                      rw [Finset.sdiff_eq_self_iff_disjoint.2 hdisj_ab.symm]; exact hPb_sing
                    exact (pick_eq_of_singleton this d0).symm
                exact ⟨rfl, hne, hp_or, ha_sub hp1, hb_sub hq1.1⟩
          · rw [hins] at hlen; simp at hlen

lemma pure_line_cover {n : ℕ} {d0 : Fin n} {C : Circuit} (hmono : Monotone2 C)
    (hno : ∀ j < C.gates.length, ¬ IsCrossAnd (n + n) (Finset.map (Fin.natAddEmb n) Finset.univ) C j) :
    ∀ w < n + n + C.gates.length,
      support (n + n) C w ⊆ Finset.map (Fin.natAddEmb n) Finset.univ →
      wval n C w ∅ ∅ = false →
      2 ≤ (lns n C w).card →
      ∀ l ∈ lns n C w, ∃ j : Fin C.size,
        (assignTriple n d0 C j).2.2 = 2 ∧
        (assignTriple n d0 C j).1 ≠ (assignTriple n d0 C j).2.1 ∧
        (l = (assignTriple n d0 C j).1 ∨ l = (assignTriple n d0 C j).2.1) ∧
        (assignTriple n d0 C j).1 ∈ lns n C w ∧
        (assignTriple n d0 C j).2.1 ∈ lns n C w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hsub h00 hcard l hl
    have hnot_disj : ¬ Disjoint (support (n + n) C w) (Finset.map (Fin.natAddEmb n) Finset.univ) := by
      intro hd
      have hemp : support (n + n) C w = ∅ := by
        ext z; simp only [Finset.notMem_empty, iff_false]; intro hz; exact Finset.disjoint_left.1 hd hz (hsub hz)
      have hlns_emp : lns n C w = ∅ := by
        ext q
        simp only [lns, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
        rw [wval_const_of_empty_support hw hemp ∅ {q}, h00]
        simp
      rw [hlns_emp] at hcard; simp at hcard
    by_cases hw1 : w < n
    · have hk : Fin.castAdd n ⟨w, hw1⟩ ∈ support (n + n) C w := by
        rw [support_input (n + n) C w (by omega)]; simp [Fin.ext_iff]
      exact (fin_castAdd_not_mem_M ⟨w, hw1⟩ (hsub hk)).elim
    · by_cases hw2 : w < n + n
      · have hsub' : lns n C w ⊆ {⟨w - n, by omega⟩} := by
          intro q hq
          simp only [lns, Finset.mem_filter, Finset.mem_univ, true_and] at hq
          rw [wval_lt_in C w hw2, incidenceInput_getD_right _ _ _ (by omega) hw2] at hq
          simp only [decide_eq_true_eq, Finset.mem_singleton] at hq ⊢
          exact Fin.ext (Fin.val_eq_of_eq hq).symm
        have hc1 : (lns n C w).card ≤ 1 := le_trans (Finset.card_le_card hsub') (by simp)
        omega
      · set j := w - (n + n)
        have hj : j < C.gates.length := by omega
        have hweq : w = n + n + j := by omega
        have hgj := hmono C.gates[j] (List.getElem_mem hj)
        rcases hgj with ⟨hop, hlen⟩
        rcases hop with hop | hop
        · rcases hins : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l3⟩⟩⟩
          · rw [hweq, wval_gate C j hj, hins, hop] at h00; cases h00
          · rw [hweq, wval_gate C j hj, hins, hop] at h00
            by_cases ha : a < w
            · have hlns : lns n C w = lns n C a := by
                ext q
                simp only [lns, Finset.mem_filter, Finset.mem_univ, true_and]
                rw [hweq, wval_gate C j hj, hins, hop]
                simp [GateOp.eval, (by omega : a < n + n + j)]
              have hasub : support (n + n) C a ⊆ Finset.map (Fin.natAddEmb n) Finset.univ := by
                refine Finset.Subset.trans ?_ hsub
                rw [hweq]; simpa [operandSupport, (by omega : a < n + n + j)] using operandSupport_subset (m := n + n) hj (w := a) (by rw [hins]; simp)
              have h00' : wval n C a ∅ ∅ = false := by
                simpa [GateOp.eval, (by omega : a < n + n + j)] using h00
              rw [hlns] at hcard hl ⊢
              exact ih a ha (by omega) hasub h00' hcard l hl
            · have hlns : lns n C w = ∅ := by
                ext q
                simp only [lns, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
                rw [hweq, wval_gate C j hj, hins, hop]
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
                rw [if_neg (by omega : ¬ a < n + n + j)]
                simp
              rw [hlns] at hcard; simp at hcard
          · rw [hweq, wval_gate C j hj, hins, hop] at h00
            by_cases hab : a < w ∧ b < w
            · have hsp := crossAnd_split hj (hno j hj) hop a b hins
              have ha_lt : a < n + n + j := by omega
              have hb_lt : b < n + n + j := by omega
              have hasub : support (n + n) C a ⊆ Finset.map (Fin.natAddEmb n) Finset.univ := by
                refine Finset.Subset.trans ?_ hsub
                rw [hweq]; simpa [operandSupport, ha_lt] using operandSupport_subset (m := n + n) hj (w := a) (by rw [hins]; simp)
              have hbsub : support (n + n) C b ⊆ Finset.map (Fin.natAddEmb n) Finset.univ := by
                refine Finset.Subset.trans ?_ hsub
                rw [hweq]; simpa [operandSupport, hb_lt] using operandSupport_subset (m := n + n) hj (w := b) (by rw [hins]; simp)
              have ha_or_hb_emp : support (n + n) C a = ∅ ∨ support (n + n) C b = ∅ := by
                rcases hsp with (h | h) | ⟨h, _⟩ | ⟨h, _⟩
                · left; simpa [operandSupport, ha_lt] using h
                · right; simpa [operandSupport, hb_lt] using h
                · left
                  have ha_disj_m : Disjoint (support (n + n) C a) (Finset.map (Fin.natAddEmb n) Finset.univ) := by
                    simpa [operandSupport, ha_lt] using h
                  ext z; simp only [Finset.notMem_empty, iff_false]; intro hz; exact Finset.disjoint_left.1 ha_disj_m hz (hasub hz)
                · right
                  have hb_disj_m : Disjoint (support (n + n) C b) (Finset.map (Fin.natAddEmb n) Finset.univ) := by
                    simpa [operandSupport, hb_lt] using h
                  ext z; simp only [Finset.notMem_empty, iff_false]; intro hz; exact Finset.disjoint_left.1 hb_disj_m hz (hbsub hz)
              have hnonempty : (lns n C w).Nonempty := Finset.card_pos.1 (by omega)
              rcases hnonempty with ⟨q0, hq0⟩
              simp only [lns, Finset.mem_filter, Finset.mem_univ, true_and] at hq0
              rw [hweq, wval_gate C j hj, hins, hop] at hq0
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, ha_lt, hb_lt, ↓reduceIte, id_eq] at hq0
              rcases ha_or_hb_emp with hemp | hemp
              · have ha_all : ∀ X' Y', wval n C a X' Y' = true := by
                  intro X' Y'
                  rw [wval_const_of_empty_support (by omega) hemp X' Y', ← wval_const_of_empty_support (by omega) hemp ∅ {q0}]
                  exact hq0.1
                have hlns : lns n C w = lns n C b := by
                  ext q
                  simp only [lns, Finset.mem_filter, Finset.mem_univ, true_and]
                  rw [hweq, wval_gate C j hj, hins, hop]
                  simp [GateOp.eval, ha_lt, hb_lt, ha_all ∅ {q}]
                have hb0 : wval n C b ∅ ∅ = false := by
                  simp [GateOp.eval, ha_lt, hb_lt, ha_all ∅ ∅] at h00; exact h00
                rw [hlns] at hcard hl ⊢
                exact ih b hab.2 (by omega) hbsub hb0 hcard l hl
              · have hb_all : ∀ X' Y', wval n C b X' Y' = true := by
                  intro X' Y'
                  rw [wval_const_of_empty_support (by omega) hemp X' Y', ← wval_const_of_empty_support (by omega) hemp ∅ {q0}]
                  exact hq0.2
                have hlns : lns n C w = lns n C a := by
                  ext q
                  simp only [lns, Finset.mem_filter, Finset.mem_univ, true_and]
                  rw [hweq, wval_gate C j hj, hins, hop]
                  simp [GateOp.eval, ha_lt, hb_lt, hb_all ∅ {q}]
                have ha0 : wval n C a ∅ ∅ = false := by
                  simp [GateOp.eval, ha_lt, hb_lt, hb_all ∅ ∅] at h00; exact h00
                rw [hlns] at hcard hl ⊢
                exact ih a hab.1 (by omega) hasub ha0 hcard l hl
            · have hlns : lns n C w = ∅ := by
                ext q
                simp only [lns, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
                rw [hweq, wval_gate C j hj, hins, hop]
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
                by_cases ha : a < w <;> by_cases hb : b < w
                · exact (hab ⟨ha, hb⟩).elim
                · rw [if_neg (by omega : ¬ b < n + n + j)]; simp
                · rw [if_neg (by omega : ¬ a < n + n + j)]; simp
                · rw [if_neg (by omega : ¬ a < n + n + j)]; simp
              rw [hlns] at hcard; simp at hcard
          · rw [hins] at hlen; simp at hlen
        · rcases hins : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l3⟩⟩⟩
          · have hlns : lns n C w = ∅ := by
              ext q
              simp only [lns, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
              rw [hweq, wval_gate C j hj, hins, hop]
              simp [GateOp.eval]
            rw [hlns] at hcard; simp at hcard
          · rw [hweq, wval_gate C j hj, hins, hop] at h00
            by_cases ha : a < w
            · have hlns : lns n C w = lns n C a := by
                ext q
                simp only [lns, Finset.mem_filter, Finset.mem_univ, true_and]
                rw [hweq, wval_gate C j hj, hins, hop]
                simp [GateOp.eval, (by omega : a < n + n + j)]
              have hasub : support (n + n) C a ⊆ Finset.map (Fin.natAddEmb n) Finset.univ := by
                refine Finset.Subset.trans ?_ hsub
                rw [hweq]; simpa [operandSupport, (by omega : a < n + n + j)] using operandSupport_subset (m := n + n) hj (w := a) (by rw [hins]; simp)
              have h00' : wval n C a ∅ ∅ = false := by
                simpa [GateOp.eval, (by omega : a < n + n + j)] using h00
              rw [hlns] at hcard hl ⊢
              exact ih a ha (by omega) hasub h00' hcard l hl
            · have hlns : lns n C w = ∅ := by
                ext q
                simp only [lns, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
                rw [hweq, wval_gate C j hj, hins, hop]
                simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq]
                rw [if_neg (by omega : ¬ a < n + n + j)]
                simp
              rw [hlns] at hcard; simp at hcard
          · set La := effLns n C w a
            set Lb := effLns n C w b
            have hlns_union : lns n C w = La ∪ Lb := by
              ext q
              dsimp only [La, Lb]
              simp only [lns, effLns, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
              rw [hweq, wval_gate C j hj, hins, hop]
              simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, id_eq]
              have ha_iff : a < n + n + j ↔ a < w := by omega
              have hb_iff : b < n + n + j ↔ b < w := by omega
              by_cases ha : a < w <;> by_cases hb : b < w <;>
                simp [GateOp.eval, ha, hb, ha_iff, hb_iff]
            have ha_sub : La ⊆ lns n C w := by rw [hlns_union]; exact Finset.subset_union_left
            have hb_sub : Lb ⊆ lns n C w := by rw [hlns_union]; exact Finset.subset_union_right
            have lift_a : ∀ (j' : Fin C.size),
                ((assignTriple n d0 C j').2.2 = 2 ∧ (assignTriple n d0 C j').1 ≠ (assignTriple n d0 C j').2.1 ∧
                  (l = (assignTriple n d0 C j').1 ∨ l = (assignTriple n d0 C j').2.1) ∧
                  (assignTriple n d0 C j').1 ∈ La ∧ (assignTriple n d0 C j').2.1 ∈ La) →
                ∃ j'' : Fin C.size,
                  (assignTriple n d0 C j'').2.2 = 2 ∧ (assignTriple n d0 C j'').1 ≠ (assignTriple n d0 C j'').2.1 ∧
                  (l = (assignTriple n d0 C j'').1 ∨ l = (assignTriple n d0 C j'').2.1) ∧
                  (assignTriple n d0 C j'').1 ∈ lns n C w ∧ (assignTriple n d0 C j'').2.1 ∈ lns n C w :=
              fun j' ⟨h1, h2, h3, h4, h5⟩ => ⟨j', h1, h2, h3, ha_sub h4, ha_sub h5⟩
            have lift_b : ∀ (j' : Fin C.size),
                ((assignTriple n d0 C j').2.2 = 2 ∧ (assignTriple n d0 C j').1 ≠ (assignTriple n d0 C j').2.1 ∧
                  (l = (assignTriple n d0 C j').1 ∨ l = (assignTriple n d0 C j').2.1) ∧
                  (assignTriple n d0 C j').1 ∈ Lb ∧ (assignTriple n d0 C j').2.1 ∈ Lb) →
                ∃ j'' : Fin C.size,
                  (assignTriple n d0 C j'').2.2 = 2 ∧ (assignTriple n d0 C j'').1 ≠ (assignTriple n d0 C j'').2.1 ∧
                  (l = (assignTriple n d0 C j'').1 ∨ l = (assignTriple n d0 C j'').2.1) ∧
                  (assignTriple n d0 C j'').1 ∈ lns n C w ∧ (assignTriple n d0 C j'').2.1 ∈ lns n C w :=
              fun j' ⟨h1, h2, h3, h4, h5⟩ => ⟨j', h1, h2, h3, hb_sub h4, hb_sub h5⟩
            by_cases ha2 : 2 ≤ La.card
            · have ha_lt : a < w := by
                by_contra hna
                have : La = ∅ := by simp [La, effLns, hna]
                rw [this] at ha2; simp at ha2
              have hasub : support (n + n) C a ⊆ Finset.map (Fin.natAddEmb n) Finset.univ := by
                refine Finset.Subset.trans ?_ hsub
                rw [hweq]; simpa [operandSupport, (by omega : a < n + n + j)] using operandSupport_subset (m := n + n) hj (w := a) (by rw [hins]; simp)
              have ha0 : wval n C a ∅ ∅ = false := by
                rw [hweq, wval_gate C j hj, hins, hop] at h00
                by_contra hc
                have hct : wval n C a ∅ ∅ = true := Bool.eq_true_of_not_eq_false hc
                simp [GateOp.eval, (by omega : a < n + n + j), hct] at h00
              have hLa_eq : La = lns n C a := by simp [La, effLns, ha_lt]
              have ha2' := ha2
              rw [hLa_eq] at ha2'
              by_cases hlLa : l ∈ La
              · rw [hLa_eq] at hlLa
                rcases ih a ha_lt (by omega) hasub ha0 ha2' l hlLa with ⟨j', hj'⟩
                exact lift_a j' (by simpa [hLa_eq] using hj')
              · have hlLb : l ∈ Lb := by
                  rw [hlns_union, Finset.mem_union] at hl
                  exact hl.resolve_left hlLa
                by_cases hb2 : 2 ≤ Lb.card
                · have hb_lt : b < w := by
                    by_contra hnb
                    have : Lb = ∅ := by simp [Lb, effLns, hnb]
                    rw [this] at hb2; simp at hb2
                  have hbsub : support (n + n) C b ⊆ Finset.map (Fin.natAddEmb n) Finset.univ := by
                    refine Finset.Subset.trans ?_ hsub
                    rw [hweq]; simpa [operandSupport, (by omega : b < n + n + j)] using operandSupport_subset (m := n + n) hj (w := b) (by rw [hins]; simp)
                  have hb0 : wval n C b ∅ ∅ = false := by
                    rw [hweq, wval_gate C j hj, hins, hop] at h00
                    by_contra hc
                    have hct : wval n C b ∅ ∅ = true := Bool.eq_true_of_not_eq_false hc
                    simp [GateOp.eval, (by omega : b < n + n + j), hct] at h00
                  have hLb_eq : Lb = lns n C b := by simp [Lb, effLns, hb_lt]
                  have hb2' := hb2
                  rw [hLb_eq] at hb2'
                  rw [hLb_eq] at hlLb
                  rcases ih b hb_lt (by omega) hbsub hb0 hb2' l hlLb with ⟨j', hj'⟩
                  exact lift_b j' (by simpa [hLb_eq] using hj')
                · have hb_card1 : Lb.card = 1 := by
                    have hpos : 0 < Lb.card := Finset.card_pos.2 ⟨l, hlLb⟩
                    omega
                  have hLa_diff : (La \ Lb).Nonempty := by
                    have hle : (La ∩ Lb).card ≤ 1 := le_trans (Finset.card_le_card Finset.inter_subset_right) (by omega)
                    have hdiff : 1 ≤ (La \ Lb).card := by
                      have hsum := Finset.card_sdiff_add_card_inter La Lb
                      omega
                    exact Finset.card_pos.1 (by omega)
                  have ha_not1 : ¬ (La.card = 1 ∧ (Lb \ La).Nonempty) := by omega
                  refine ⟨⟨j, hj⟩, ?_⟩
                  have hassign : assignTriple n d0 C ⟨j, hj⟩ = (pick Lb d0, pick (La \ Lb) d0, 2) := by
                    dsimp only [assignTriple]
                    rw [hop, hins]
                    simp only [← hweq]
                    rw [if_neg hnot_disj, if_pos hsub]
                    simp only [La, Lb]
                    rw [if_neg ha_not1, if_pos ⟨hb_card1, hLa_diff⟩]
                  rw [hassign]
                  have hLb_sing : Lb = {l} := Finset.card_eq_one.1 hb_card1 |>.elim fun q hq => by
                    rw [hq, Finset.mem_singleton] at hlLb; subst hlLb; exact hq
                  have hl1 : pick Lb d0 = l := pick_eq_of_singleton hLb_sing d0
                  have hqmem : pick (La \ Lb) d0 ∈ La \ Lb := pick_mem hLa_diff d0
                  rw [Finset.mem_sdiff] at hqmem
                  have hne : l ≠ pick (La \ Lb) d0 := fun heq => hqmem.2 (by rw [← heq]; exact hlLb)
                  exact ⟨rfl, by rw [hl1]; exact hne, Or.inl hl1.symm, by rw [hl1]; exact hl, ha_sub hqmem.1⟩
            · by_cases hb2 : 2 ≤ Lb.card
              · have hb_lt : b < w := by
                  by_contra hnb
                  have : Lb = ∅ := by simp [Lb, effLns, hnb]
                  rw [this] at hb2; simp at hb2
                have hbsub : support (n + n) C b ⊆ Finset.map (Fin.natAddEmb n) Finset.univ := by
                  refine Finset.Subset.trans ?_ hsub
                  rw [hweq]; simpa [operandSupport, (by omega : b < n + n + j)] using operandSupport_subset (m := n + n) hj (w := b) (by rw [hins]; simp)
                have hb0 : wval n C b ∅ ∅ = false := by
                  rw [hweq, wval_gate C j hj, hins, hop] at h00
                  by_contra hc
                  have hct : wval n C b ∅ ∅ = true := Bool.eq_true_of_not_eq_false hc
                  simp [GateOp.eval, (by omega : b < n + n + j), hct] at h00
                have hLb_eq : Lb = lns n C b := by simp [Lb, effLns, hb_lt]
                have hb2' := hb2
                rw [hLb_eq] at hb2'
                by_cases hlLb : l ∈ Lb
                · rw [hLb_eq] at hlLb
                  rcases ih b hb_lt (by omega) hbsub hb0 hb2' l hlLb with ⟨j', hj'⟩
                  exact lift_b j' (by simpa [hLb_eq] using hj')
                · have hlLa : l ∈ La := by
                    rw [hlns_union, Finset.mem_union] at hl
                    exact hl.resolve_right hlLb
                  have ha_card1 : La.card = 1 := by
                    have hpos : 0 < La.card := Finset.card_pos.2 ⟨l, hlLa⟩
                    omega
                  have hLb_diff : (Lb \ La).Nonempty := by
                    have hle : (Lb ∩ La).card ≤ 1 := le_trans (Finset.card_le_card Finset.inter_subset_right) (by omega)
                    have hdiff : 1 ≤ (Lb \ La).card := by
                      have hsum := Finset.card_sdiff_add_card_inter Lb La
                      omega
                    exact Finset.card_pos.1 (by omega)
                  refine ⟨⟨j, hj⟩, ?_⟩
                  have hassign : assignTriple n d0 C ⟨j, hj⟩ = (pick La d0, pick (Lb \ La) d0, 2) := by
                    dsimp only [assignTriple]
                    rw [hop, hins]
                    simp only [← hweq]
                    rw [if_neg hnot_disj, if_pos hsub]
                    simp only [La, Lb]
                    rw [if_pos ⟨ha_card1, hLb_diff⟩]
                  rw [hassign]
                  have hLa_sing : La = {l} := Finset.card_eq_one.1 ha_card1 |>.elim fun q hq => by
                    rw [hq, Finset.mem_singleton] at hlLa; subst hlLa; exact hq
                  have hl1 : pick La d0 = l := pick_eq_of_singleton hLa_sing d0
                  have hqmem : pick (Lb \ La) d0 ∈ Lb \ La := pick_mem hLb_diff d0
                  rw [Finset.mem_sdiff] at hqmem
                  have hne : l ≠ pick (Lb \ La) d0 := fun heq => hqmem.2 (by rw [← heq]; exact hlLa)
                  exact ⟨rfl, by rw [hl1]; exact hne, Or.inl hl1.symm, by rw [hl1]; exact hl, hb_sub hqmem.1⟩
              · have ha1 : La.card = 1 := by
                  have hle : (La ∪ Lb).card ≤ La.card + Lb.card := Finset.card_union_le La Lb
                  rw [← hlns_union] at hle
                  omega
                have hb1 : Lb.card = 1 := by
                  have hle : (La ∪ Lb).card ≤ La.card + Lb.card := Finset.card_union_le La Lb
                  rw [← hlns_union] at hle
                  omega
                have hdisj_ab : Disjoint La Lb := by
                  by_contra hnd
                  rcases Finset.not_disjoint_iff.1 hnd with ⟨q, hqa, hqb⟩
                  have hpa' : La = {q} := Finset.card_eq_one.1 ha1 |>.elim fun x hx => by rw [hx, Finset.mem_singleton] at hqa; subst hqa; exact hx
                  have hpb' : Lb = {q} := Finset.card_eq_one.1 hb1 |>.elim fun x hx => by rw [hx, Finset.mem_singleton] at hqb; subst hqb; exact hx
                  rw [hlns_union, hpa', hpb', Finset.union_idempotent, Finset.card_singleton] at hcard
                  omega
                have hLb_diff : (Lb \ La).Nonempty := by
                  rw [Finset.sdiff_eq_self_iff_disjoint.2 hdisj_ab.symm]
                  exact Finset.card_pos.1 (by omega)
                refine ⟨⟨j, hj⟩, ?_⟩
                have hassign : assignTriple n d0 C ⟨j, hj⟩ = (pick La d0, pick (Lb \ La) d0, 2) := by
                  dsimp only [assignTriple]
                  rw [hop, hins]
                  simp only [← hweq]
                  rw [if_neg hnot_disj, if_pos hsub]
                  simp only [La, Lb]
                  rw [if_pos ⟨ha1, hLb_diff⟩]
                rw [hassign]
                have hl1 : pick La d0 ∈ La := pick_mem (Finset.card_pos.1 (by omega)) d0
                have hq1 : pick (Lb \ La) d0 ∈ Lb \ La := pick_mem hLb_diff d0
                rw [Finset.mem_sdiff] at hq1
                have hne : pick La d0 ≠ pick (Lb \ La) d0 := fun heq => hq1.2 (by rw [← heq]; exact hl1)
                have hl_or : l = pick La d0 ∨ l = pick (Lb \ La) d0 := by
                  rw [hlns_union, Finset.mem_union] at hl
                  rcases hl with hla | hlb
                  · left
                    have hLa_sing : La = {l} := Finset.card_eq_one.1 ha1 |>.elim fun x hx => by rw [hx, Finset.mem_singleton] at hla; subst hla; exact hx
                    exact (pick_eq_of_singleton hLa_sing d0).symm
                  · right
                    have hLb_sing : Lb = {l} := Finset.card_eq_one.1 hb1 |>.elim fun x hx => by rw [hx, Finset.mem_singleton] at hlb; subst hlb; exact hx
                    have : Lb \ La = {l} := by
                      rw [Finset.sdiff_eq_self_iff_disjoint.2 hdisj_ab.symm]; exact hLb_sing
                    exact (pick_eq_of_singleton this d0).symm
                exact ⟨rfl, hne, hl_or, ha_sub hl1, hb_sub hq1.1⟩
          · rw [hins] at hlen; simp at hlen

lemma below_cover {n : ℕ} {d0 : Fin n} (S : Fin n → Finset (Fin n)) {C : Circuit} (hmono : Monotone2 C)
    (hno : ∀ j < C.gates.length, ¬ IsCrossAnd (n + n) (Finset.map (Fin.natAddEmb n) Finset.univ) C j) :
    ∀ w < n + n + C.gates.length,
      (∀ X Y : Finset (Fin n), wval n C w X Y = true → incidenceFun S X Y = true) →
      ∀ p l : Fin n, wval n C w {p} {l} = true →
        ∃ j : Fin C.size,
          ((assignTriple n d0 C j).2.2 = 0 ∧ p = (assignTriple n d0 C j).1 ∧ l = (assignTriple n d0 C j).2.1) ∨
          ((assignTriple n d0 C j).2.2 = 1 ∧ (assignTriple n d0 C j).1 ≠ (assignTriple n d0 C j).2.1 ∧
            (p = (assignTriple n d0 C j).1 ∨ p = (assignTriple n d0 C j).2.1) ∧
            (assignTriple n d0 C j).1 ∈ S l ∧ (assignTriple n d0 C j).2.1 ∈ S l) ∨
          ((assignTriple n d0 C j).2.2 = 2 ∧ (assignTriple n d0 C j).1 ≠ (assignTriple n d0 C j).2.1 ∧
            (l = (assignTriple n d0 C j).1 ∨ l = (assignTriple n d0 C j).2.1) ∧
            p ∈ S (assignTriple n d0 C j).1 ∧ p ∈ S (assignTriple n d0 C j).2.1) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hbelow p l hpl
    by_cases hw1 : w < n
    · let p0 : Fin n := ⟨w, hw1⟩
      have hbad : wval n C w {p0} ∅ = true := by
        rw [wval_lt_in C w (by omega), incidenceInput_getD_left {p0} ∅ w hw1]
        simp [p0]
      have hinc := hbelow {p0} ∅ hbad
      unfold PEqualNP.GenericRejection.incidenceFun at hinc
      simp only [decide_eq_true_eq, Finset.notMem_empty, false_and, exists_false, and_false] at hinc
    · by_cases hw2 : w < n + n
      · let l0 : Fin n := ⟨w - n, by omega⟩
        have hbad : wval n C w ∅ {l0} = true := by
          rw [wval_lt_in C w hw2, incidenceInput_getD_right ∅ {l0} w (by omega) hw2]
          simp [l0]
        have hinc := hbelow ∅ {l0} hbad
        unfold PEqualNP.GenericRejection.incidenceFun at hinc
        simp only [decide_eq_true_eq, Finset.notMem_empty, false_and, exists_false] at hinc
      · set j := w - (n + n)
        have hj : j < C.gates.length := by omega
        have hweq : w = n + n + j := by omega
        have hgj := hmono C.gates[j] (List.getElem_mem hj)
        rcases hgj with ⟨hop, hlen⟩
        rcases hop with hop | hop
        · rcases hins : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l3⟩⟩⟩
          · have hbad : wval n C w ∅ ∅ = true := by rw [hweq, wval_gate C j hj, hins, hop]; rfl
            have hinc := hbelow ∅ ∅ hbad
            unfold PEqualNP.GenericRejection.incidenceFun at hinc
            simp only [decide_eq_true_eq, Finset.notMem_empty, false_and, exists_false] at hinc
          · rw [hweq, wval_gate C j hj, hins, hop] at hpl
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, id_eq] at hpl
            split_ifs at hpl with ha
            · apply ih a (by omega) (by omega) _ p l hpl
              intro X Y hXY
              apply hbelow X Y
              rw [hweq, wval_gate C j hj, hins, hop]
              simp [GateOp.eval, ha, hXY]
          · rw [hweq, wval_gate C j hj, hins, hop] at hpl
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true, id_eq] at hpl
            split_ifs at hpl with ha hb
            · have hsp := crossAnd_split hj (hno j hj) hop a b hins
              have handle_emp_a : support (n + n) C a = ∅ → _ := fun hemp => by
                have ha_all : ∀ X' Y', wval n C a X' Y' = true := by
                  intro X' Y'
                  rw [wval_const_of_empty_support (by omega) hemp X' Y', ← wval_const_of_empty_support (by omega) hemp {p} {l}]
                  exact hpl.1
                apply ih b (by omega) (by omega) _ p l hpl.2
                intro X Y hXY
                apply hbelow X Y
                rw [hweq, wval_gate C j hj, hins, hop]
                simp [GateOp.eval, ha, hb, ha_all X Y, hXY]
              have handle_emp_b : support (n + n) C b = ∅ → _ := fun hemp => by
                have hb_all : ∀ X' Y', wval n C b X' Y' = true := by
                  intro X' Y'
                  rw [wval_const_of_empty_support (by omega) hemp X' Y', ← wval_const_of_empty_support (by omega) hemp {p} {l}]
                  exact hpl.2
                apply ih a (by omega) (by omega) _ p l hpl.1
                intro X Y hXY
                apply hbelow X Y
                rw [hweq, wval_gate C j hj, hins, hop]
                simp [GateOp.eval, ha, hb, hb_all X Y, hXY]
              have handle_pure : ∀ (u v : ℕ), u < w → v < w →
                  Disjoint (support (n + n) C u) (Finset.map (Fin.natAddEmb n) Finset.univ) →
                  support (n + n) C v ⊆ Finset.map (Fin.natAddEmb n) Finset.univ →
                  wval n C u {p} {l} = true → wval n C v {p} {l} = true →
                  (∀ X Y, wval n C u X Y = true → wval n C v X Y = true → wval n C w X Y = true) →
                  ((u = a ∧ v = b) ∨ (u = b ∧ v = a)) →
                  ∃ j' : Fin C.size,
                    ((assignTriple n d0 C j').2.2 = 0 ∧ p = (assignTriple n d0 C j').1 ∧ l = (assignTriple n d0 C j').2.1) ∨
                    ((assignTriple n d0 C j').2.2 = 1 ∧ (assignTriple n d0 C j').1 ≠ (assignTriple n d0 C j').2.1 ∧
                      (p = (assignTriple n d0 C j').1 ∨ p = (assignTriple n d0 C j').2.1) ∧
                      (assignTriple n d0 C j').1 ∈ S l ∧ (assignTriple n d0 C j').2.1 ∈ S l) ∨
                    ((assignTriple n d0 C j').2.2 = 2 ∧ (assignTriple n d0 C j').1 ≠ (assignTriple n d0 C j').2.1 ∧
                      (l = (assignTriple n d0 C j').1 ∨ l = (assignTriple n d0 C j').2.1) ∧
                      p ∈ S (assignTriple n d0 C j').1 ∧ p ∈ S (assignTriple n d0 C j').2.1) := by
                intro u v hu hv hud hvsub hupl hvpl hcomb huv
                have hu0 : wval n C u ∅ ∅ = false := by
                  by_contra hnc
                  have hut : wval n C u ∅ ∅ = true := Bool.eq_true_of_not_eq_false hnc
                  have hul : wval n C u ∅ {l} = true := wval_mono hmono (Finset.Subset.refl ∅) (Finset.empty_subset {l}) u hut
                  have hv_empty_l : wval n C v ∅ {l} = true := by
                    rw [← hvpl]
                    refine wval_eq_of_support v (by omega) ∅ {l} {p} {l} ?_
                    intro k hk
                    refine ⟨fun p0 hp0 => (fin_castAdd_not_mem_M p0 (by rw [hp0]; exact hvsub hk)).elim, fun l0 _ => Iff.rfl⟩
                  have hinc := hbelow ∅ {l} (hcomb ∅ {l} hul hv_empty_l)
                  unfold PEqualNP.GenericRejection.incidenceFun at hinc
                  simp only [decide_eq_true_eq, Finset.notMem_empty, false_and, exists_false] at hinc
                have hv0 : wval n C v ∅ ∅ = false := by
                  by_contra hnc
                  have hvt : wval n C v ∅ ∅ = true := Bool.eq_true_of_not_eq_false hnc
                  have hvp : wval n C v {p} ∅ = true := wval_mono hmono (Finset.empty_subset {p}) (Finset.Subset.refl ∅) v hvt
                  have hu_p_empty : wval n C u {p} ∅ = true := by
                    rw [← hupl]
                    refine wval_eq_of_support u (by omega) {p} ∅ {p} {l} ?_
                    intro k hk
                    refine ⟨fun p0 _ => Iff.rfl, fun l0 hl0 => (Finset.disjoint_left.1 hud hk (by rw [← hl0]; exact fin_natAdd_mem_M l0)).elim⟩
                  have hinc := hbelow {p} ∅ (hcomb {p} ∅ hu_p_empty hvp)
                  unfold PEqualNP.GenericRejection.incidenceFun at hinc
                  simp only [decide_eq_true_eq, Finset.notMem_empty, false_and, and_false, exists_false] at hinc
                have hpu := (pure_point_class hmono hno u (by omega) hud hu0 {p} {l}).1 hupl
                have hpv := (pure_line_class hmono hno v (by omega) hvsub hv0 {p} {l}).1 hvpl
                rcases hpu with ⟨p', hp', hpu'⟩
                rw [Finset.mem_singleton] at hp'
                rw [hp'] at hpu'
                rcases hpv with ⟨l', hl', hpv'⟩
                rw [Finset.mem_singleton] at hl'
                rw [hl'] at hpv'
                have hprod : ∀ x ∈ pts n C u, ∀ y ∈ lns n C v, x ∈ S y := by
                  intro x hx y hy
                  have hux := (pure_point_class hmono hno u (by omega) hud hu0 {x} {y}).2 ⟨x, Finset.mem_singleton_self x, hx⟩
                  have hvy := (pure_line_class hmono hno v (by omega) hvsub hv0 {x} {y}).2 ⟨y, Finset.mem_singleton_self y, hy⟩
                  have hinc := hbelow {x} {y} (hcomb {x} {y} hux hvy)
                  simpa [incidenceFun] using hinc
                by_cases huc : 2 ≤ (pts n C u).card
                · rcases pure_point_cover hmono hno u (by omega) hud hu0 huc p hpu' with ⟨j', h1, h2, h3, h4, h5⟩
                  exact ⟨j', Or.inr (Or.inl ⟨h1, h2, h3, hprod _ h4 l hpv', hprod _ h5 l hpv'⟩)⟩
                · by_cases hvc : 2 ≤ (lns n C v).card
                  · rcases pure_line_cover hmono hno v (by omega) hvsub hv0 hvc l hpv' with ⟨j', h1, h2, h3, h4, h5⟩
                    exact ⟨j', Or.inr (Or.inr ⟨h1, h2, h3, hprod p hpu' _ h4, hprod p hpu' _ h5⟩)⟩
                  · have hu1 : (pts n C u).card = 1 := by
                      have := Finset.card_pos.2 ⟨p, hpu'⟩; omega
                    have hv1 : (lns n C v).card = 1 := by
                      have := Finset.card_pos.2 ⟨l, hpv'⟩; omega
                    have hpts_sing : pts n C u = {p} := Finset.card_eq_one.1 hu1 |>.elim fun x hx => by rw [hx, Finset.mem_singleton] at hpu'; subst hpu'; exact hx
                    have hlns_sing : lns n C v = {l} := Finset.card_eq_one.1 hv1 |>.elim fun y hy => by rw [hy, Finset.mem_singleton] at hpv'; subst hpv'; exact hy
                    refine ⟨⟨j, hj⟩, Or.inl ?_⟩
                    rcases huv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
                    · have hassign : assignTriple n d0 C ⟨j, hj⟩ = (pick (pts n C u) d0, pick (lns n C v) d0, 0) := by
                        dsimp only [assignTriple]
                        rw [hop, hins]
                        simp only [← hweq]
                        rw [if_pos ⟨hu, hv, hud, hvsub, hu1, hv1⟩]
                      rw [hassign, pick_eq_of_singleton hpts_sing d0, pick_eq_of_singleton hlns_sing d0]
                      exact ⟨rfl, rfl, rfl⟩
                    · have hnot1 : ¬ (v < w ∧ u < w ∧ Disjoint (support (n + n) C v) (Finset.map (Fin.natAddEmb n) Finset.univ) ∧
                          support (n + n) C u ⊆ Finset.map (Fin.natAddEmb n) Finset.univ ∧ (pts n C v).card = 1 ∧ (lns n C u).card = 1) := by
                        rintro ⟨_, _, hdv, hsu, _, _⟩
                        have hemp : support (n + n) C u = ∅ := by
                          ext z; simp only [Finset.notMem_empty, iff_false]; intro hz; exact Finset.disjoint_left.1 hud hz (hsu hz)
                        have : pts n C u = ∅ := by
                          ext q
                          simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
                          rw [wval_const_of_empty_support (by omega) hemp {q} ∅, hu0]
                          simp
                        rw [this] at hu1; simp at hu1
                      have hassign : assignTriple n d0 C ⟨j, hj⟩ = (pick (pts n C u) d0, pick (lns n C v) d0, 0) := by
                        dsimp only [assignTriple]
                        rw [hop, hins]
                        simp only [← hweq]
                        rw [if_neg hnot1, if_pos ⟨hv, hu, hud, hvsub, hu1, hv1⟩]
                      rw [hassign, pick_eq_of_singleton hpts_sing d0, pick_eq_of_singleton hlns_sing d0]
                      exact ⟨rfl, rfl, rfl⟩
              rcases hsp with (he | he) | ⟨had, hbsub⟩ | ⟨hbd, hasub⟩
              · exact handle_emp_a (by simpa [operandSupport, ha] using he)
              · exact handle_emp_b (by simpa [operandSupport, hb] using he)
              · exact handle_pure a b (by omega) (by omega) (by simpa [operandSupport, ha] using had)
                  (by simpa [operandSupport, hb] using hbsub) hpl.1 hpl.2
                  (fun X Y hx hy => by rw [hweq, wval_gate C j hj, hins, hop]; simp [GateOp.eval, ha, hb, hx, hy])
                  (Or.inl ⟨rfl, rfl⟩)
              · exact handle_pure b a (by omega) (by omega) (by simpa [operandSupport, hb] using hbd)
                  (by simpa [operandSupport, ha] using hasub) hpl.2 hpl.1
                  (fun X Y hx hy => by rw [hweq, wval_gate C j hj, hins, hop]; simp [GateOp.eval, ha, hb, hx, hy])
                  (Or.inr ⟨rfl, rfl⟩)
            · exact hpl.2.elim
            · exact hpl.1.elim
            · exact hpl.1.elim
          · rw [hins] at hlen; simp at hlen
        · rcases hins : C.gates[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨c, l3⟩⟩⟩
          · rw [hweq, wval_gate C j hj, hins, hop] at hpl; cases hpl
          · rw [hweq, wval_gate C j hj, hins, hop] at hpl
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, id_eq] at hpl
            split_ifs at hpl with ha
            · apply ih a (by omega) (by omega) _ p l hpl
              intro X Y hXY
              apply hbelow X Y
              rw [hweq, wval_gate C j hj, hins, hop]
              simp [GateOp.eval, ha, hXY]
          · rw [hweq, wval_gate C j hj, hins, hop] at hpl
            simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, Bool.or_false, Bool.or_eq_true, id_eq] at hpl
            rcases hpl with h1 | h2
            · split_ifs at h1 with ha
              apply ih a (by omega) (by omega) _ p l h1
              intro X Y hXY
              apply hbelow X Y
              rw [hweq, wval_gate C j hj, hins, hop]
              simp [GateOp.eval, ha, hXY]
            · split_ifs at h2 with hb
              apply ih b (by omega) (by omega) _ p l h2
              intro X Y hXY
              apply hbelow X Y
              rw [hweq, wval_gate C j hj, hins, hop]
              simp [GateOp.eval, hb, hXY]
          · rw [hins] at hlen; simp at hlen

end PEqualNP.Outside.L_meta_4592

theorem PEqualNP.Outside.L_meta_4592 : ∀ (x1 : ℕ) (x2 : Fin x1 → Finset (Fin x1)) (x3 : PEqualNP.CircuitLowerBounds.Circuit), (0 : ℕ) < x1 → PEqualNP.MetaComplexity.Monotone2 x3 → PEqualNP.GenericRejection.ComputesIncidence x2 x3 → PEqualNP.CrossAnd.crossCount (x1 + x1) (Finset.map (Fin.natAddEmb x1) Finset.univ) x3 = (0 : ℕ) → ∃ (x8 : Fin x3.size → Fin x1) (x9 : Fin x3.size → Fin x1) (x10 : Fin x3.size → Fin (3 : ℕ)), ∀ (x11 x12 : Fin x1), x11 ∈ x2 x12 → ∃ (x14 : Fin x3.size), x10 x14 = (0 : Fin (3 : ℕ)) ∧ x11 = x8 x14 ∧ x12 = x9 x14 ∨ x10 x14 = (1 : Fin (3 : ℕ)) ∧ x8 x14 ≠ x9 x14 ∧ (x11 = x8 x14 ∨ x11 = x9 x14) ∧ x8 x14 ∈ x2 x12 ∧ x9 x14 ∈ x2 x12 ∨ x10 x14 = (2 : Fin (3 : ℕ)) ∧ x8 x14 ≠ x9 x14 ∧ (x12 = x8 x14 ∨ x12 = x9 x14) ∧ x11 ∈ x2 (x8 x14) ∧ x11 ∈ x2 (x9 x14) := by
  intro n S C hx1 hmono hcomp hcross
  have hno : ∀ j < C.gates.length, ¬ PEqualNP.CrossAnd.IsCrossAnd (n + n) (Finset.map (Fin.natAddEmb n) Finset.univ) C j := by
    intro j hj hc
    have hmem : j ∈ (Finset.range C.gates.length).filter (fun j => PEqualNP.CrossAnd.IsCrossAnd (n + n) (Finset.map (Fin.natAddEmb n) Finset.univ) C j) :=
      Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, hc⟩
    have hpos : 0 < PEqualNP.CrossAnd.crossCount (n + n) (Finset.map (Fin.natAddEmb n) Finset.univ) C :=
      Finset.card_pos.2 ⟨j, hmem⟩
    omega
  let d0 : Fin n := ⟨0, hx1⟩
  refine ⟨fun j => (PEqualNP.Outside.L_meta_4592.assignTriple n d0 C j).1,
    fun j => (PEqualNP.Outside.L_meta_4592.assignTriple n d0 C j).2.1,
    fun j => (PEqualNP.Outside.L_meta_4592.assignTriple n d0 C j).2.2, ?_⟩
  intro p l hpl
  have hev : PEqualNP.Outside.L_meta_4592.wval n C C.output {p} {l} = true := by
    change C.eval (PEqualNP.GenericRejection.incidenceInput {p} {l}) = true
    rw [hcomp {p} {l}]
    exact decide_eq_true ⟨p, Finset.mem_singleton_self p, l, Finset.mem_singleton_self l, hpl⟩
  have hout : C.output < n + n + C.gates.length := by
    by_contra hno_out
    have hf := PEqualNP.Outside.L_meta_4592.wval_ge_end C C.output (Nat.le_of_not_lt hno_out) {p} {l}
    rw [hev] at hf
    cases hf
  have hbelow : ∀ X Y : Finset (Fin n),
      PEqualNP.Outside.L_meta_4592.wval n C C.output X Y = true →
      PEqualNP.GenericRejection.incidenceFun S X Y = true := by
    intro X Y hXY
    have hce : C.eval (PEqualNP.GenericRejection.incidenceInput X Y) = true := hXY
    rw [hcomp X Y] at hce
    exact hce
  exact PEqualNP.Outside.L_meta_4592.below_cover S hmono hno C.output hout hbelow p l hev
