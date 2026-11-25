import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1896.Normalize

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def cleanGate (k : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map fun i => if i < k then i + 1 else 0⟩

def cleanGates : ℕ → List Gate → List Gate
  | _, [] => []
  | k, g :: gs => cleanGate k g :: cleanGates (k + 1) gs

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma cleanGate_values (w : List Bool) (g : Gate) :
    (cleanGate w.length g).op.eval ((cleanGate w.length g).inputs.map
      fun i => (false :: w).getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  congr 1
  simp only [cleanGate, List.map_map]
  apply List.map_congr_left
  intro i hi
  by_cases h : i < w.length
  · simp [h]
  · simp [h, List.getD_eq_default w false (Nat.le_of_not_gt h)]

lemma clean_run (gs : List Gate) (w : List Bool) :
    run (cleanGates w.length gs) (false :: w) = false :: run gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [cleanGates, run, List.foldl_cons]
    rw [cleanGate_values]
    simpa only [run, List.cons_append, List.length_append, List.length_singleton] using
      ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])

lemma cleanGates_length (k : ℕ) (gs : List Gate) : (cleanGates k gs).length = gs.length := by
  induction gs generalizing k with
  | nil => rfl
  | cons g gs ih => simp [cleanGates, ih]

lemma cleanGate_inputs_lt (k : ℕ) (g : Gate) :
    ∀ a ∈ (cleanGate k g).inputs, a < k + 1 := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ha
  split_ifs <;> omega

lemma cleanGates_back (k : ℕ) (gs : List Gate) :
    ∀ j : Fin (cleanGates k gs).length,
      ∀ a ∈ ((cleanGates k gs).get j).inputs, a < k + 1 + j.val := by
  induction gs generalizing k with
  | nil => intro j; exact Fin.elim0 j
  | cons g gs ih =>
    intro j
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa [cleanGates] using cleanGate_inputs_lt k g
    · simpa [cleanGates, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih (k + 1) j

lemma cleanGates_op (k : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ((cleanGates k gs)[j]'(by simpa [cleanGates_length] using hj)).op = (gs[j]'hj).op := by
  induction gs generalizing k j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero => rfl
    | succ j => simpa [cleanGates] using ih (k + 1) j (by simpa using hj)

lemma cleanGates_legal (k : ℕ) (gs : List Gate)
    (h : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ cleanGates k gs,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction gs generalizing k with
  | nil => simp [cleanGates]
  | cons g gs ih =>
    intro g' hg'
    rcases List.mem_cons.mp hg' with rfl | hg'
    · simpa [cleanGate] using h g (by simp)
    · exact ih (k + 1) (fun g hg => h g (by simp [hg])) g' hg'

def cleanCircuit (n : ℕ) (C : Circuit) : Circuit :=
  ⟨cleanGates n C.gates, C.output + 1⟩

lemma cleanCircuit_eval (C : Circuit) (x : List Bool) :
    (cleanCircuit x.length C).eval (false :: x) = C.eval x := by
  change (run (cleanGates x.length C.gates) (false :: x)).getD (C.output + 1) false = _
  rw [clean_run]
  rfl

lemma cleanCircuit_fun {n : ℕ} (C : Circuit) (x : Fin n → Bool) :
    circuitFun (n + 1) (cleanCircuit n C) (Fin.cases false x) = circuitFun n C x := by
  have h := cleanCircuit_eval C (List.ofFn x)
  simpa [circuitFun, List.ofFn_succ] using h

lemma cleanCircuit_or_count (n : ℕ) (C : Circuit) :
    {j : Fin (cleanCircuit n C).gates.length |
      ((cleanCircuit n C).gates.get j).op = GateOp.or}.ncard =
      {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard := by
  classical
  simp only [Set.ncard_eq_toFinset_card', Set.toFinset_setOf, Finset.card_filter]
  apply Fintype.sum_equiv (finCongr (cleanGates_length n C.gates))
  intro j
  have hj : j.val < C.gates.length := by simpa [cleanGates_length] using j.isLt
  simp only [cleanCircuit, List.get_eq_getElem, finCongr_apply, Fin.val_cast]
  simp only [cleanGates_op n C.gates j.val hj]

end PEqualNP.Outside.L_meta_1896.Normalize


-- The counting argument below reuses willakone’s checked proof of L-meta-2059 (PR 4283).

namespace PEqualNP.Outside.L_meta_1896_aux.CleanOrSkip

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover


def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

lemma wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

lemma wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

lemma getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

lemma getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega


lemma wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

lemma gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

lemma iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

lemma val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

lemma val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

lemma val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

lemma val_mono (gates : List Gate) {n : ℕ}
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x x' : Fin n → Bool) (hx : ∀ v, x v = true → x' v = true) :
    ∀ w, val gates w x = true → val gates w x' = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro h
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h ⊢
      exact hx _ h
    · by_cases hbig : n + gates.length ≤ w
      · rw [val_big gates x w hbig] at h
        exact Bool.noConfusion h
      · have hi : w - n < gates.length := by omega
        have he : n + (w - n) = w := by omega
        rw [← he] at h ⊢
        rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
        · apply (val_and gates x' (w - n) hi ha).2
          intro j hj
          obtain ⟨hjlt, hjv⟩ := (val_and gates x (w - n) hi ha).1 h j hj
          exact ⟨hjlt, ih j (by omega) hjv⟩
        · obtain ⟨j, hj, hjlt, hv⟩ := (val_or gates x (w - n) hi ho).1 h
          exact (val_or gates x' (w - n) hi ho).2 ⟨j, hj, hjlt, ih j (by omega) hv⟩

lemma zero_false {n : ℕ} (gates : List Gate)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (x : Fin n → Bool) (hf : val gates w x = false) :
    val gates w (fun _ : Fin n => false) = false := by
  cases hz : val gates w (fun _ : Fin n => false) with
  | false => rfl
  | true =>
    have ht := val_mono gates legal (fun _ : Fin n => false) x (by simp) w hz
    rw [hf] at ht
    cases ht

def Cl {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (i : Fin gates.length) (X : Finset (Fin m)) : Prop :=
  (gates.get i).op = GateOp.or →
    val gates (n + i.val) (fun _ : Fin n => false) = false →
    ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ M, ∀ y' ∈ M,
      (val gates a (τ y) = true ∨ val gates b (τ y) = true) →
      (val gates a (τ y') = true ∨ val gates b (τ y') = true) → (y ∈ X ↔ y' ∈ X)

def Con {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (k : ℕ) (X : Finset (Fin m)) : Prop :=
  ∀ i : Fin gates.length, (i : ℕ) < k → Cl gates M τ i X

def Mrg {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (g : Fin gates.length) : Prop :=
  (gates.get g).op = GateOp.or ∧
    val gates (n + g.val) (fun _ : Fin n => false) = false ∧
    ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ M, ∃ r' ∈ M,
      val gates w1 (τ r) = true ∧ val gates w2 (τ r') = true ∧
      ∃ X : Finset (Fin m), r ∈ X ∧ r' ∉ X ∧ Con gates M τ (g : ℕ) X

def meet {n m : ℕ} (τ : Fin m → Fin n → Bool) (p q : Fin m) : Fin n → Bool :=
  fun i => τ p i && τ q i

lemma single {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) (X : Finset (Fin m)) (hX : Con gates M τ k X) :
    ∀ w, w < n + k → ∀ y ∈ M, ∀ y' ∈ M,
      val gates w (meet τ y y') = false →
      val gates w (τ y) = true → val gates w (τ y') = true → (y ∈ X ↔ y' ∈ X) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw y hy y' hy' hwc h1 h2
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at hwc h1 h2
      simp [meet, h1, h2] at hwc
    · have hi : w - n < gates.length := by omega
      have he : n + (w - n) = w := by omega
      rw [← he] at hwc h1 h2
      have hinp : ∀ a ∈ gates[w - n].inputs, a < n + (w - n) := hin ⟨w - n, hi⟩
      have hlen := (legal gates[w - n] (List.getElem_mem hi)).2
      rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
      · have hex : ∃ j ∈ gates[w - n].inputs, val gates j (meet τ y y') = false := by
          by_contra hne
          have hall : val gates (n + (w - n)) (meet τ y y') = true := by
            apply (val_and gates _ (w - n) hi ha).2
            intro j hj
            refine ⟨hinp j hj, ?_⟩
            cases hv : val gates j (meet τ y y') with
            | true => rfl
            | false => exact absurd ⟨j, hj, hv⟩ hne
          rw [hall] at hwc
          exact Bool.noConfusion hwc
        obtain ⟨j, hj, hjc⟩ := hex
        exact ih j (by have := hinp j hj; omega) (by have := hinp j hj; omega)
          y hy y' hy' hjc
          ((val_and gates (τ y) (w - n) hi ha).1 h1 j hj).2
          ((val_and gates (τ y') (w - n) hi ha).1 h2 j hj).2
      · have hall : ∀ j ∈ gates[w - n].inputs, val gates j (meet τ y y') = false := by
          intro j hj
          cases hv : val gates j (meet τ y y') with
          | false => rfl
          | true =>
            have ht : val gates (n + (w - n)) (meet τ y y') = true :=
              (val_or gates _ (w - n) hi ho).2 ⟨j, hj, hinp j hj, hv⟩
            rw [ht] at hwc
            exact Bool.noConfusion hwc
        obtain ⟨j1, hj1, _, hv1⟩ := (val_or gates (τ y) (w - n) hi ho).1 h1
        obtain ⟨j2, hj2, _, hv2⟩ := (val_or gates (τ y') (w - n) hi ho).1 h2
        rcases hinpe : gates[w - n].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
        · rw [hinpe] at hj1
          simp at hj1
        · rw [hinpe] at hj1 hj2
          have e1 : j1 = a := by simpa using hj1
          have e2 : j2 = a := by simpa using hj2
          rw [e1] at hv1
          rw [e2] at hv2
          have hjlt := hinp a (by rw [hinpe]; simp)
          exact ih a (by omega) (by omega) y hy y' hy'
            (hall a (by rw [hinpe]; simp)) hv1 hv2
        · rw [hinpe] at hj1 hj2
          have d1 : val gates a (τ y) = true ∨ val gates b (τ y) = true := by
            rcases List.mem_pair.1 hj1 with e | e
            · subst e; exact Or.inl hv1
            · subst e; exact Or.inr hv1
          have d2 : val gates a (τ y') = true ∨ val gates b (τ y') = true := by
            rcases List.mem_pair.1 hj2 with e | e
            · subst e; exact Or.inl hv2
            · subst e; exact Or.inr hv2
          exact hX ⟨w - n, hi⟩ (by simp; omega) ho
            (zero_false gates legal _ _ hwc) a b hinpe y hy y' hy' d1 d2
        · rw [hinpe] at hlen
          simp at hlen

lemma con_succ {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (k : ℕ) (hk : k < gates.length) (X : Finset (Fin m)) :
    Con gates M τ (k + 1) X ↔ Con gates M τ k X ∧ Cl gates M τ ⟨k, hk⟩ X := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h ⟨k, hk⟩ (by simp)⟩
  · rintro ⟨h1, h2⟩ i hi
    by_cases e : (i : ℕ) = k
    · have e' : i = ⟨k, hk⟩ := Fin.ext e
      rw [e']
      exact h2
    · exact h1 i (by omega)

lemma con_compl {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (k : ℕ) (X : Finset (Fin m)) (h : Con gates M τ k X) :
    Con gates M τ k Xᶜ := by
  intro i hi ho hz a b hab y hy y' hy' h1 h2
  rw [Finset.mem_compl, Finset.mem_compl, not_iff_not]
  exact h i hi ho hz a b hab y hy y' hy' h1 h2

lemma con_symm {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin m)) (hX : Con gates M τ k X)
    (hY : Con gates M τ k Y) : Con gates M τ k (symmDiff X Y) := by
  intro i hi ho hz a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hz a b hab y hy y' hy' h1 h2
  have e2 := hY i hi ho hz a b hab y hy y' hy' h1 h2
  rw [Finset.mem_symmDiff, Finset.mem_symmDiff, e1, e2]

lemma con_inter {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (k : ℕ) (X : Finset (Fin m)) (hX : Con gates M τ k X) :
    Con gates M τ k (X ∩ M) := by
  intro i hi ho hz a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hz a b hab y hy y' hy' h1 h2
  rw [Finset.mem_inter, Finset.mem_inter, e1]
  exact ⟨fun h => ⟨h.1, hy'⟩, fun h => ⟨h.1, hy⟩⟩

lemma cl_of {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (g : Fin gates.length) (X : Finset (Fin m)) (a b : ℕ)
    (hab : (gates.get g).inputs = [a, b])
    (sA : ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true → val gates a (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (sB : ∀ y ∈ M, ∀ y' ∈ M, val gates b (τ y) = true → val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (Q : ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true → val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X)) : Cl gates M τ g X := by
  intro _ _ a' b' hab' y hy y' hy' h1 h2
  rw [hab] at hab'
  obtain ⟨e1, e2⟩ : a = a' ∧ b = b' := by simpa using hab'
  subst e1
  subst e2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact sA y hy y' hy' h1 h2
  · exact Q y hy y' hy' h1 h2
  · exact (Q y' hy' y hy h2 h1).symm
  · exact sB y hy y' hy' h1 h2

lemma symm_flip {m : ℕ} (X Y : Finset (Fin m)) (r r' : Fin m) (hr : r ∈ Y) (hr' : r' ∉ Y) :
    (r ∈ symmDiff X Y ↔ r' ∈ symmDiff X Y) ↔ ¬ (r ∈ X ↔ r' ∈ X) := by
  by_cases h1 : r ∈ X <;> by_cases h2 : r' ∈ X <;> simp [Finset.mem_symmDiff, h1, h2, hr, hr']

open Classical in
noncomputable def P {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (k : ℕ) : Finset (Finset (Fin m)) :=
  M.powerset.filter (fun X => Con gates M τ k X)

open Classical in
lemma symm_mem {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin m)) (hX : X ∈ P gates M τ k)
    (hY : Y ⊆ M) (hYc : Con gates M τ k Y) : symmDiff X Y ∈ P gates M τ k := by
  rw [P, Finset.mem_filter, Finset.mem_powerset] at hX ⊢
  refine ⟨?_, con_symm gates M τ k X Y hX.2 hYc⟩
  intro v hv
  rw [Finset.mem_symmDiff] at hv
  rcases hv with hv | hv
  · exact hX.1 hv.1
  · exact hY hv.1


open Classical in
lemma step {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool)
    (clean : ∀ i : Fin gates.length, (gates.get i).op = GateOp.or →
      val gates (n + i.val) (fun _ : Fin n => false) = false →
      ∀ p ∈ M, ∀ q ∈ M, p ≠ q → val gates (n + i.val) (meet τ p q) = false)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (g : Fin gates.length) :
    (P gates M τ ((g : ℕ) + 1)).card * (if Mrg gates M τ g then 2 else 1)
      = (P gates M τ (g : ℕ)).card := by
  by_cases hal : (gates.get g).op = GateOp.or ∧
      val gates (n + g.val) (fun _ : Fin n => false) = false ∧
      ∃ a b : ℕ, (gates.get g).inputs = [a, b]
  swap
  · have hnm : ¬ Mrg gates M τ g := by
      rintro ⟨h1, hz, w1, w2, h3, _⟩
      exact hal ⟨h1, hz, w1, w2, h3⟩
    have hP : P gates M τ ((g : ℕ) + 1) = P gates M τ (g : ℕ) := by
      unfold P
      apply Finset.filter_congr
      intro X _
      rw [con_succ gates M τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        intro ho hz a b hab
        exact absurd ⟨ho, hz, a, b, hab⟩ hal
    rw [hP, ite_eq_right hnm, Nat.mul_one]
  · obtain ⟨ho, hz, a, b, hab⟩ := hal
    have hma : a ∈ (gates.get g).inputs := by rw [hab]; simp
    have hmb : b ∈ (gates.get g).inputs := by rw [hab]; simp
    have ha : a < n + (g : ℕ) := hin g a hma
    have hb : b < n + (g : ℕ) := hin g b hmb
    have hac (p : Fin m) (hp : p ∈ M) (q : Fin m) (hq : q ∈ M) (hpq : p ≠ q) :
        val gates a (meet τ p q) = false := by
      cases hv : val gates a (meet τ p q) with
      | false => rfl
      | true =>
        have ht : val gates (n + (g : ℕ)) (meet τ p q) = true :=
          (val_or gates _ g g.2 ho).2 ⟨a, hma, ha, hv⟩
        rw [clean g ho hz p hp q hq hpq] at ht
        cases ht
    have hbc (p : Fin m) (hp : p ∈ M) (q : Fin m) (hq : q ∈ M) (hpq : p ≠ q) :
        val gates b (meet τ p q) = false := by
      cases hv : val gates b (meet τ p q) with
      | false => rfl
      | true =>
        have ht : val gates (n + (g : ℕ)) (meet τ p q) = true :=
          (val_or gates _ g g.2 ho).2 ⟨b, hmb, hb, hv⟩
        rw [clean g ho hz p hp q hq hpq] at ht
        cases ht
    have sA : ∀ X, Con gates M τ g X → ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true →
        val gates a (τ y') = true → (y ∈ X ↔ y' ∈ X) := by
      intro X hX y hy y' hy' h1 h2
      by_cases he : y = y'
      · simp [he]
      · exact single gates M τ legal hin g (le_of_lt g.2) X hX a ha y hy y' hy'
          (hac y hy y' hy' he) h1 h2
    have sB : ∀ X, Con gates M τ g X → ∀ y ∈ M, ∀ y' ∈ M, val gates b (τ y) = true →
        val gates b (τ y') = true → (y ∈ X ↔ y' ∈ X) := by
      intro X hX y hy y' hy' h1 h2
      by_cases he : y = y'
      · simp [he]
      · exact single gates M τ legal hin g (le_of_lt g.2) X hX b hb y hy y' hy'
          (hbc y hy y' hy' he) h1 h2
    by_cases hm : ∃ r ∈ M, ∃ r' ∈ M, val gates a (τ r) = true ∧ val gates b (τ r') = true ∧
        ∃ X : Finset (Fin m), r ∈ X ∧ r' ∉ X ∧ Con gates M τ (g : ℕ) X
    · have hmrg : Mrg gates M τ g := ⟨ho, hz, a, b, hab, hm⟩
      obtain ⟨r, hr, r', hr', hra, hrb, X0, hrX, hr'X, hX0⟩ := hm
      rw [ite_eq_left hmrg]
      have hP : P gates M τ ((g : ℕ) + 1)
          = (P gates M τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X) := by
        unfold P
        rw [Finset.filter_filter]
        apply Finset.filter_congr
        intro X _
        rw [con_succ gates M τ g g.2 X]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, h2 ho hz a b hab r hr r' hr' (Or.inl hra) (Or.inr hrb)⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, cl_of gates M τ g X a b hab (sA X h1) (sB X h1) ?_⟩
          intro y hy y' hy' hya hyb
          exact ((sA X h1 y hy r hr hya hra).trans h2).trans (sB X h1 r' hr' y' hy' hrb hyb)
      rw [hP]
      have hsplit := Finset.card_filter_add_card_filter_not (s := P gates M τ (g : ℕ))
        (fun X => r ∈ X ↔ r' ∈ X)
      have hY0 : X0 ∩ M ⊆ M := Finset.inter_subset_right
      have hY0c := con_inter gates M τ g X0 hX0
      have hrY : r ∈ X0 ∩ M := Finset.mem_inter.2 ⟨hrX, hr⟩
      have hr'Y : r' ∉ X0 ∩ M := fun h => hr'X (Finset.mem_inter.1 h).1
      have hbij : ((P gates M τ (g : ℕ)).filter (fun X => ¬ (r ∈ X ↔ r' ∈ X))).card
          = ((P gates M τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X)).card := by
        refine Finset.card_bij' (fun X _ => symmDiff X (X0 ∩ M)) (fun X _ => symmDiff X (X0 ∩ M))
          ?_ ?_ ?_ ?_
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨symm_mem gates M τ g X _ hX.1 hY0 hY0c, ?_⟩
          exact (symm_flip X (X0 ∩ M) r r' hrY hr'Y).2 hX.2
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨symm_mem gates M τ g X _ hX.1 hY0 hY0c, ?_⟩
          intro hcon
          exact (symm_flip X (X0 ∩ M) r r' hrY hr'Y).1 hcon hX.2
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
      omega
    · have hnm : ¬ Mrg gates M τ g := by
        rintro ⟨_, _, w1, w2, h3, r, hr, r', hr', h4, h5, h6⟩
        rw [hab] at h3
        obtain ⟨e1, e2⟩ : a = w1 ∧ b = w2 := by simpa using h3
        subst e1
        subst e2
        exact hm ⟨r, hr, r', hr', h4, h5, h6⟩
      rw [ite_eq_right hnm, Nat.mul_one]
      congr 1
      unfold P
      apply Finset.filter_congr
      intro X _
      rw [con_succ gates M τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, cl_of gates M τ g X a b hab (sA X h) (sB X h) ?_⟩
        intro y hy y' hy' hya hyb
        constructor
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, X, hyX, hn, h⟩
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, Xᶜ, Finset.mem_compl.2 hn,
            fun h' => Finset.mem_compl.1 h' hyX, con_compl gates M τ g X h⟩

open Classical in
lemma count {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool)
    (clean : ∀ i : Fin gates.length, (gates.get i).op = GateOp.or →
      val gates (n + i.val) (fun _ : Fin n => false) = false →
      ∀ p ∈ M, ∀ q ∈ M, p ≠ q → val gates (n + i.val) (meet τ p q) = false)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) :
    (P gates M τ k).card *
      2 ^ (∑ g : Fin gates.length, if (g : ℕ) < k ∧ Mrg gates M τ g then 1 else 0)
      = 2 ^ M.card := by
  induction k with
  | zero =>
    have h0 : P gates M τ 0 = M.powerset := by
      unfold P
      apply Finset.filter_true_of_mem
      intro X _ i hi
      exact absurd hi (Nat.not_lt_zero _)
    rw [h0, Finset.card_powerset]
    simp
  | succ k ih =>
    have hk' : k < gates.length := hk
    have hs : (P gates M τ (k + 1)).card * (if Mrg gates M τ ⟨k, hk'⟩ then 2 else 1)
        = (P gates M τ k).card := step gates M τ clean legal hin ⟨k, hk'⟩
    have hsum : (∑ g : Fin gates.length, if (g : ℕ) < k + 1 ∧ Mrg gates M τ g then 1 else 0)
        = (∑ g : Fin gates.length, if (g : ℕ) < k ∧ Mrg gates M τ g then 1 else 0)
          + (if Mrg gates M τ ⟨k, hk'⟩ then 1 else 0) := by
      have hpt : ∀ g : Fin gates.length,
          (if (g : ℕ) < k + 1 ∧ Mrg gates M τ g then 1 else 0)
          = (if (g : ℕ) < k ∧ Mrg gates M τ g then 1 else 0)
            + (if g = ⟨k, hk'⟩ then (if Mrg gates M τ ⟨k, hk'⟩ then 1 else 0) else 0) := by
        intro g
        by_cases e : g = ⟨k, hk'⟩
        · subst e
          simp
        · have hne : (g : ℕ) ≠ k := fun h => e (Fin.ext h)
          have h2 : ((g : ℕ) < k + 1) ↔ ((g : ℕ) < k) := by omega
          simp [e, h2]
      rw [Finset.sum_congr rfl (fun g _ => hpt g), Finset.sum_add_distrib]
      simp
    rw [hsum, pow_add, ← ih (le_of_lt hk'), ← hs]
    split_ifs <;> ring


open Classical in
lemma mcount {n m : ℕ} (gates : List Gate) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool)
    (clean : ∀ i : Fin gates.length, (gates.get i).op = GateOp.or →
      val gates (n + i.val) (fun _ : Fin n => false) = false →
      ∀ p ∈ M, ∀ q ∈ M, p ≠ q → val gates (n + i.val) (meet τ p q) = false)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hM : 1 ≤ M.card) (o : ℕ) (hoc : ∀ p ∈ M, ∀ q ∈ M, p ≠ q → val gates o (meet τ p q) = false)
    (hot : ∀ p ∈ M, val gates o (τ p) = true) :
    (∑ g : Fin gates.length, if Mrg gates M τ g then 1 else 0) = M.card - 1 := by
  have hne : M.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨p0, hp0⟩ := hne
  have holt : o < n + gates.length := by
    by_contra h
    have hb := val_big gates (τ p0) o (by omega)
    rw [hot p0 hp0] at hb
    exact Bool.noConfusion hb
  have hfin : P gates M τ gates.length = {∅, M} := by
    ext X
    rw [P, Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hsub, hX⟩
      have hs := single gates M τ legal hin gates.length le_rfl X hX o holt
      by_cases hex : ∃ y ∈ M, y ∈ X
      · obtain ⟨y, hy, hyX⟩ := hex
        right
        apply Finset.Subset.antisymm hsub
        intro z hz
        by_cases he : y = z
        · simpa [he] using hyX
        · exact (hs y hy z hz (hoc y hy z hz he) (hot y hy) (hot z hz)).1 hyX
      · left
        apply Finset.eq_empty_of_forall_notMem
        intro z hz
        exact hex ⟨z, hsub hz, hz⟩
    · rintro (e | e)
      · subst e
        refine ⟨Finset.empty_subset _, ?_⟩
        intro i _ _ _ a b _ y _ y' _ _ _
        simp
      · subst e
        refine ⟨Finset.Subset.refl _, ?_⟩
        intro i _ _ _ a b _ y hy y' hy' _ _
        exact ⟨fun _ => hy', fun _ => hy⟩
  have hcnt := count gates M τ clean legal hin gates.length le_rfl
  have hpair : ({∅, M} : Finset (Finset (Fin m))).card = 2 := by
    apply Finset.card_pair
    intro h
    rw [← h] at hp0
    simp at hp0
  rw [hfin, hpair] at hcnt
  have hsum : (∑ g : Fin gates.length, if (g : ℕ) < gates.length ∧ Mrg gates M τ g then 1 else 0)
      = ∑ g : Fin gates.length, if Mrg gates M τ g then 1 else 0 :=
    Finset.sum_congr rfl (fun g _ => by simp [g.2])
  rw [hsum] at hcnt
  have hm1 : 2 ^ M.card = 2 * 2 ^ (M.card - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h8 : 2 ^ (∑ g : Fin gates.length, if Mrg gates M τ g then 1 else 0) = 2 ^ (M.card - 1) :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (hcnt.trans hm1)
  exact Nat.pow_right_injective (le_refl 2) h8

lemma clean_or_bound {n m : ℕ} (C : Circuit) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool)
    (clean : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.or →
      circuitFun n {C with output := n + i.val} (fun _ => false) = false →
      ∀ p ∈ M, ∀ q ∈ M, p ≠ q →
        circuitFun n {C with output := n + i.val} (meet τ p q) = false)
    (legal : Monotone2 C)
    (hin : ∀ i : Fin C.gates.length, ∀ a ∈ (C.gates.get i).inputs, a < n + i.val)
    (hM : 1 ≤ M.card)
    (hc : ∀ p ∈ M, ∀ q ∈ M, p ≠ q → circuitFun n C (meet τ p q) = false)
    (ht : ∀ p ∈ M, circuitFun n C (τ p) = true) :
    M.card - 1 ≤ {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard := by
  classical
  have h := mcount C.gates M τ clean legal hin hM C.output hc ht
  rw [← h]
  simp only [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, Finset.card_filter]
  apply Finset.sum_le_sum
  intro g hg
  by_cases hm : Mrg C.gates M τ g
  · have hop : C.gates[g.val].op = GateOp.or := hm.1
    simp [hm, hop]
  · simp [hm]

end PEqualNP.Outside.L_meta_1896_aux.CleanOrSkip


namespace PEqualNP.Outside.L_meta_1896_aux.CleanOrSkip

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma clean_or_bound_excluding {n m : ℕ} (C : Circuit) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool)
    (clean : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.or →
      circuitFun n {C with output := n + i.val} (fun _ => false) = false →
      ∀ p ∈ M, ∀ q ∈ M, p ≠ q →
        circuitFun n {C with output := n + i.val} (meet τ p q) = false)
    (legal : Monotone2 C)
    (hin : ∀ i : Fin C.gates.length, ∀ a ∈ (C.gates.get i).inputs, a < n + i.val)
    (hM : 1 ≤ M.card)
    (hc : ∀ p ∈ M, ∀ q ∈ M, p ≠ q → circuitFun n C (meet τ p q) = false)
    (ht : ∀ p ∈ M, circuitFun n C (τ p) = true)
    (E : Finset (Fin C.gates.length))
    (hE : ∀ j ∈ E, (C.gates.get j).op = GateOp.or)
    (exclude : ∀ j ∈ E, ¬Mrg C.gates M τ j) :
    M.card - 1 + E.card ≤ {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard := by
  classical
  have h := mcount C.gates M τ clean legal hin hM C.output hc ht
  have he : (∑ j : Fin C.gates.length, if j ∈ E then 1 else 0) = E.card := by simp
  rw [← h, ← he, ← Finset.sum_add_distrib]
  simp only [Set.ncard_eq_toFinset_card', Set.toFinset_ofPred, Finset.card_filter]
  apply Finset.sum_le_sum
  intro j hj
  by_cases hm : Mrg C.gates M τ j
  · have hop : C.gates[j.val].op = GateOp.or := hm.1
    have hne : j ∉ E := fun hjE => exclude j hjE hm
    simp [hm, hne, hop]
  · by_cases hjE : j ∈ E
    · have hop : C.gates[j.val].op = GateOp.or := hE j hjE
      simp [hm, hjE, hop]
    · simp [hm, hjE]

lemma not_merge_of_dead_operand {n m : ℕ} (C : Circuit) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (j : Fin C.gates.length)
    (dead : ∀ a b, (C.gates.get j).inputs = [a, b] →
      (∀ p ∈ M, val C.gates a (τ p) = false) ∨
      (∀ p ∈ M, val C.gates b (τ p) = false)) :
    ¬Mrg C.gates M τ j := by
  rintro ⟨ho, hz, a, b, hab, p, hp, q, hq, ha, hb, _⟩
  rcases dead a b hab with h | h
  · exact Bool.noConfusion ((h p hp).symm.trans ha)
  · exact Bool.noConfusion ((h q hq).symm.trans hb)

end PEqualNP.Outside.L_meta_1896_aux.CleanOrSkip

namespace PEqualNP.Outside.L_meta_1896_aux.CleanOrSkip

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1896.Normalize

lemma cleanGates_entry (k : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ((cleanGates k gs)[j]'(by simpa [cleanGates_length] using hj)) =
      cleanGate (k + j) (gs[j]'hj) := by
  induction gs generalizing k j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero => rfl
    | succ j =>
      simpa [cleanGates, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (k + 1) j (by simpa using hj)

lemma not_merge_of_mem_dead {n m : ℕ} (C : Circuit) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool) (j : Fin C.gates.length)
    (dead : ∃ a ∈ (C.gates.get j).inputs, ∀ p ∈ M, val C.gates a (τ p) = false) :
    ¬Mrg C.gates M τ j := by
  apply not_merge_of_dead_operand C M τ j
  intro a b hab
  obtain ⟨w, hw, hd⟩ := dead
  rw [hab] at hw
  have hw' : w = a ∨ w = b := by simpa using hw
  rcases hw' with rfl | rfl
  · exact Or.inl hd
  · exact Or.inr hd

lemma clean_or_bound_excluding_general {n m : ℕ} (C : Circuit) (M : Finset (Fin m))
    (τ : Fin m → Fin n → Bool)
    (clean : ∀ i : Fin C.gates.length, (C.gates.get i).op = GateOp.or →
      circuitFun n {C with output := n + i.val} (fun _ => false) = false →
      ∀ p ∈ M, ∀ q ∈ M, p ≠ q →
        circuitFun n {C with output := n + i.val} (meet τ p q) = false)
    (legal : Monotone2 C) (hM : 1 ≤ M.card)
    (hc : ∀ p ∈ M, ∀ q ∈ M, p ≠ q → circuitFun n C (meet τ p q) = false)
    (ht : ∀ p ∈ M, circuitFun n C (τ p) = true)
    (E : Finset (Fin C.gates.length))
    (hE : ∀ j ∈ E, (C.gates.get j).op = GateOp.or)
    (dead : ∀ j ∈ E, ∃ a ∈ (C.gates.get j).inputs, a < n + j.val ∧
      ∀ p ∈ M, circuitFun n {C with output := a} (τ p) = false) :
    M.card - 1 + E.card ≤ {j : Fin C.gates.length | (C.gates.get j).op = GateOp.or}.ncard := by
  classical
  let τ' : Fin m → Fin (n + 1) → Bool := fun p => Fin.cases false (τ p)
  let e : Fin (cleanCircuit n C).gates.length ≃ Fin C.gates.length :=
    finCongr (cleanGates_length n C.gates)
  let E' : Finset (Fin (cleanCircuit n C).gates.length) := E.map e.symm.toEmbedding
  have emem (i : Fin (cleanCircuit n C).gates.length) (hi : i ∈ E') : e i ∈ E := by
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    simpa using hj
  have hlen (i : Fin (cleanCircuit n C).gates.length) : i.val < C.gates.length := by
    simpa [cleanCircuit, cleanGates_length] using i.isLt
  have hsame (w : ℕ) (x : Fin n → Bool) : circuitFun (n + 1)
      {cleanCircuit n C with output := w + 1} (Fin.cases false x) =
      circuitFun n {C with output := w} x :=
    cleanCircuit_fun {C with output := w} x
  have eqmeet (p q : Fin m) : meet τ' p q = Fin.cases false (meet τ p q) := by
    funext i
    exact Fin.cases rfl (fun _ => rfl) i
  have hlegal : Monotone2 (cleanCircuit n C) := cleanGates_legal n C.gates legal
  have hback : ∀ i : Fin (cleanCircuit n C).gates.length,
      ∀ a ∈ ((cleanCircuit n C).gates.get i).inputs, a < (n + 1) + i.val :=
    cleanGates_back n C.gates
  have hclean : ∀ i : Fin (cleanCircuit n C).gates.length,
      ((cleanCircuit n C).gates.get i).op = GateOp.or →
      circuitFun (n + 1) {cleanCircuit n C with output := (n + 1) + i.val} (fun _ => false) = false →
      ∀ p ∈ M, ∀ q ∈ M, p ≠ q →
        circuitFun (n + 1) {cleanCircuit n C with output := (n + 1) + i.val}
          (meet τ' p q) = false := by
    intro i hi hz p hp q hq hpq
    have hop : (C.gates.get (e i)).op = GateOp.or :=
      (cleanGates_op n C.gates i.val (hlen i)).symm.trans hi
    have zeq : Fin.cases false (fun _ : Fin n => false) = (fun _ : Fin (n + 1) => false) := by
      funext i
      exact Fin.cases rfl (fun _ => rfl) i
    have oldzero : circuitFun n {C with output := n + i.val} (fun _ => false) = false := by
      rw [← hsame, zeq]
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz
    rw [eqmeet]
    have hs := hsame (n + i.val) (meet τ p q)
    have hc := clean (e i) hop oldzero p hp q hq hpq
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hs.trans hc
  have hfalse : ∀ p ∈ M, ∀ q ∈ M, p ≠ q →
      circuitFun (n + 1) (cleanCircuit n C) (meet τ' p q) = false := by
    intro p hp q hq hpq
    rw [eqmeet, cleanCircuit_fun]
    exact hc p hp q hq hpq
  have htrue : ∀ p ∈ M, circuitFun (n + 1) (cleanCircuit n C) (τ' p) = true := by
    intro p hp
    exact (cleanCircuit_fun C (τ p)).trans (ht p hp)
  have heop : ∀ i ∈ E', ((cleanCircuit n C).gates.get i).op = GateOp.or := by
    intro i hi
    exact (cleanGates_op n C.gates i.val (hlen i)).trans (hE (e i) (emem i hi))
  have hexclude : ∀ i ∈ E', ¬Mrg (cleanCircuit n C).gates M τ' i := by
    intro i hi
    apply not_merge_of_mem_dead (cleanCircuit n C) M τ' i
    obtain ⟨a, ha, halt, hd⟩ := dead (e i) (emem i hi)
    refine ⟨a + 1, ?_, ?_⟩
    · change a + 1 ∈ ((cleanGates n C.gates)[i.val]'(by simpa [cleanGates_length] using hlen i)).inputs
      rw [cleanGates_entry n C.gates i.val (hlen i)]
      apply List.mem_map.mpr
      refine ⟨a, ha, ?_⟩
      exact if_pos halt
    · intro p hp
      exact (hsame a (τ p)).trans (hd p hp)
  have h := clean_or_bound_excluding (cleanCircuit n C) M τ' hclean hlegal hback
    hM hfalse htrue E' heop hexclude
  have ec : E'.card = E.card := Finset.card_map _
  rwa [ec, cleanCircuit_or_count] at h

end PEqualNP.Outside.L_meta_1896_aux.CleanOrSkip
