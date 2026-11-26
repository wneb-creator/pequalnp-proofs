import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18294.Flat

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem eval_eq (gs : List Gate) (o : ℕ) (x : List Bool) :
    Circuit.eval ⟨gs, o⟩ x = (wf gs x).getD o false := rfl

theorem wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

theorem wf_keep (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wf gs w).getD i false = w.getD i false := by
  induction gs with
  | nil => intro w i _; rfl
  | cons g gs ih =>
    intro w i hi
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) i (by simp; omega)
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

theorem wf_prefix (pre post : List Gate) (w : List Bool) (i : ℕ)
    (hi : i < w.length + pre.length) :
    (wf (pre ++ post) w).getD i false = (wf pre w).getD i false := by
  have : wf (pre ++ post) w = wf post (wf pre w) := by simp [wf, List.foldl_append]
  rw [this]
  exact wf_keep post _ i (by rw [wf_len]; exact hi)

theorem getD_snoc_lt (L : List Bool) (a : Bool) (w : ℕ) (h : w < L.length) :
    (L ++ [a]).getD w false = L.getD w false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_snoc_eq (L : List Bool) (a : Bool) : (L ++ [a]).getD L.length false = a := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_snoc_gt (L : List Bool) (a : Bool) (w : ℕ) (h : L.length < w) :
    (L ++ [a]).getD w false = false := by
  rw [List.getD_eq_default]; simp; omega

theorem wire_take (gates : List Gate) (X : List Bool) (k i : ℕ) (hi : i < X.length + k)
    (hk : k ≤ gates.length) :
    (wf gates X).getD i false = (wf (gates.take k) X).getD i false := by
  conv_lhs => rw [← List.take_append_drop k gates]
  exact wf_prefix _ _ _ _ (by rw [List.length_take, Nat.min_eq_left hk]; exact hi)

theorem gate_val (gates : List Gate) (X : List Bool) (k : ℕ) (hk : k < gates.length) :
    (wf gates X).getD (X.length + k) false
      = gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false) := by
  rw [wire_take gates X (k + 1) _ (by omega) hk, List.take_succ_eq_append_getElem hk, wf_snoc]
  have := getD_snoc_eq (wf (gates.take k) X)
    (gates[k].op.eval (gates[k].inputs.map fun i => (wf (gates.take k) X).getD i false))
  rw [wf_len, List.length_take, Nat.min_eq_left (Nat.le_of_lt hk)] at this
  exact this

def val (gates : List Gate) {n : ℕ} (w : ℕ) (x : Fin n → Bool) : Bool :=
  (wf gates (List.ofFn x)).getD w false

theorem iv_eq (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k ≤ gates.length)
    (i : ℕ) : (wf (gates.take k) (List.ofFn x)).getD i false = true ↔
      i < n + k ∧ val gates i x = true := by
  by_cases hi : i < n + k
  · rw [val, wire_take gates (List.ofFn x) k i (by simpa using hi) hk]
    simp [hi]
  · rw [List.getD_eq_default _ _ (by rw [wf_len, List.length_take, Nat.min_eq_left hk]; simp; omega)]
    simp [hi]

theorem val_and (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.and) :
    val gates (n + k) x = true ↔ ∀ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp, id]
  constructor
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).1 (h i hi)
  · intro h i hi; exact (iv_eq gates x k (Nat.le_of_lt hk) i).2 (h i hi)

theorem val_or (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (k : ℕ) (hk : k < gates.length)
    (hop : gates[k].op = GateOp.or) :
    val gates (n + k) x = true ↔ ∃ i ∈ gates[k].inputs, i < n + k ∧ val gates i x = true := by
  have := gate_val gates (List.ofFn x) k hk
  rw [List.length_ofFn] at this
  rw [val, this, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp, id]
  constructor
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).1 h⟩
  · rintro ⟨i, hi, h⟩; exact ⟨i, hi, (iv_eq gates x k (Nat.le_of_lt hk) i).2 h⟩

theorem val_input (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    val gates w x = x ⟨w, hw⟩ := by
  rw [val, wf_keep gates _ w (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

theorem val_big (gates : List Gate) {n : ℕ} (x : Fin n → Bool) (w : ℕ)
    (hw : n + gates.length ≤ w) : val gates w x = false := by
  rw [val, List.getD_eq_default _ _ (by rw [wf_len]; simpa using hw)]

def Cl {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (i : Fin gates.length) (X : Finset (Fin n)) : Prop :=
  (gates.get i).op = GateOp.or → val gates (n + (i : ℕ)) c = false →
    ∀ a b : ℕ, (gates.get i).inputs = [a, b] → ∀ y ∈ M, ∀ y' ∈ M,
      (val gates a (τ y) = true ∨ val gates b (τ y) = true) →
      (val gates a (τ y') = true ∨ val gates b (τ y') = true) → (y ∈ X ↔ y' ∈ X)

def Con {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (k : ℕ) (X : Finset (Fin n)) : Prop :=
  ∀ i : Fin gates.length, (i : ℕ) < k → Cl gates M c τ i X

def Mrg {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool) (τ : Fin n → Fin n → Bool)
    (g : Fin gates.length) : Prop :=
  (gates.get g).op = GateOp.or ∧ val gates (n + (g : ℕ)) c = false ∧
    ∃ w1 w2 : ℕ, (gates.get g).inputs = [w1, w2] ∧ ∃ r ∈ M, ∃ r' ∈ M,
      val gates w1 (τ r) = true ∧ val gates w2 (τ r') = true ∧
      ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ Con gates M c τ (g : ℕ) X

theorem single {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) (X : Finset (Fin n)) (hX : Con gates M c τ k X) :
    ∀ w, w < n + k → val gates w c = false → ∀ y ∈ M, ∀ y' ∈ M,
      val gates w (τ y) = true → val gates w (τ y') = true → (y ∈ X ↔ y' ∈ X) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hwc y hy y' hy' h1 h2
    by_cases hwn : w < n
    · rw [val_input gates _ w hwn] at h1 h2
      have e1 := hτ y hy _ h1
      have e2 := hτ y' hy' _ h2
      rw [← e1, ← e2]
    · have hi : w - n < gates.length := by omega
      have he : n + (w - n) = w := by omega
      rw [← he] at hwc h1 h2
      have hinp : ∀ a ∈ gates[w - n].inputs, a < n + (w - n) :=
        hin ⟨w - n, hi⟩
      have hlen := (legal gates[w - n] (List.getElem_mem hi)).2
      rcases (legal gates[w - n] (List.getElem_mem hi)).1 with ha | ho
      · have hex : ∃ j ∈ gates[w - n].inputs, val gates j c = false := by
          by_contra hne
          have hall : val gates (n + (w - n)) c = true := by
            apply (val_and gates c (w - n) hi ha).2
            intro j hj
            refine ⟨hinp j hj, ?_⟩
            cases hv : val gates j c with
            | true => rfl
            | false => exact absurd ⟨j, hj, hv⟩ hne
          rw [hall] at hwc
          exact Bool.noConfusion hwc
        obtain ⟨j, hj, hjc⟩ := hex
        have hjlt := hinp j hj
        exact ih j (by omega) (by omega) hjc y hy y' hy'
          ((val_and gates (τ y) (w - n) hi ha).1 h1 j hj).2
          ((val_and gates (τ y') (w - n) hi ha).1 h2 j hj).2
      · have hall : ∀ j ∈ gates[w - n].inputs, val gates j c = false := by
          intro j hj
          cases hv : val gates j c with
          | false => rfl
          | true =>
            have ht : val gates (n + (w - n)) c = true :=
              (val_or gates c (w - n) hi ho).2 ⟨j, hj, hinp j hj, hv⟩
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
          exact ih a (by omega) (by omega) (hall a (by rw [hinpe]; simp)) y hy y' hy' hv1 hv2
        · rw [hinpe] at hj1 hj2
          have d1 : val gates a (τ y) = true ∨ val gates b (τ y) = true := by
            rcases List.mem_pair.1 hj1 with e | e
            · subst e; exact Or.inl hv1
            · subst e; exact Or.inr hv1
          have d2 : val gates a (τ y') = true ∨ val gates b (τ y') = true := by
            rcases List.mem_pair.1 hj2 with e | e
            · subst e; exact Or.inl hv2
            · subst e; exact Or.inr hv2
          exact hX ⟨w - n, hi⟩ (by simp; omega) ho hwc a b hinpe y hy y' hy' d1 d2
        · rw [hinpe] at hlen
          simp at hlen

theorem con_succ {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (hk : k < gates.length) (X : Finset (Fin n)) :
    Con gates M c τ (k + 1) X ↔ Con gates M c τ k X ∧ Cl gates M c τ ⟨k, hk⟩ X := by
  constructor
  · intro h
    exact ⟨fun i hi => h i (by omega), h ⟨k, hk⟩ (by simp)⟩
  · rintro ⟨h1, h2⟩ i hi
    by_cases e : (i : ℕ) = k
    · have e' : i = ⟨k, hk⟩ := Fin.ext e
      rw [e']
      exact h2
    · exact h1 i (by omega)

theorem con_compl {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X : Finset (Fin n)) (h : Con gates M c τ k X) :
    Con gates M c τ k Xᶜ := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_compl, Finset.mem_compl, not_iff_not]
  exact h i hi ho hc' a b hab y hy y' hy' h1 h2

theorem con_symm {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin n)) (hX : Con gates M c τ k X)
    (hY : Con gates M c τ k Y) : Con gates M c τ k (symmDiff X Y) := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hc' a b hab y hy y' hy' h1 h2
  have e2 := hY i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_symmDiff, Finset.mem_symmDiff, e1, e2]

theorem con_inter {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X : Finset (Fin n)) (hX : Con gates M c τ k X) :
    Con gates M c τ k (X ∩ M) := by
  intro i hi ho hc' a b hab y hy y' hy' h1 h2
  have e1 := hX i hi ho hc' a b hab y hy y' hy' h1 h2
  rw [Finset.mem_inter, Finset.mem_inter, e1]
  exact ⟨fun h => ⟨h.1, hy'⟩, fun h => ⟨h.1, hy⟩⟩

theorem cl_of {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (g : Fin gates.length) (X : Finset (Fin n)) (a b : ℕ)
    (hab : (gates.get g).inputs = [a, b])
    (sA : ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true → val gates a (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (sB : ∀ y ∈ M, ∀ y' ∈ M, val gates b (τ y) = true → val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X))
    (Q : ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true → val gates b (τ y') = true →
      (y ∈ X ↔ y' ∈ X)) : Cl gates M c τ g X := by
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

theorem symm_flip {n : ℕ} (X Y : Finset (Fin n)) (r r' : Fin n) (hr : r ∈ Y) (hr' : r' ∉ Y) :
    (r ∈ symmDiff X Y ↔ r' ∈ symmDiff X Y) ↔ ¬ (r ∈ X ↔ r' ∈ X) := by
  by_cases h1 : r ∈ X <;> by_cases h2 : r' ∈ X <;> simp [Finset.mem_symmDiff, h1, h2, hr, hr']

open Classical in
noncomputable def P {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) : Finset (Finset (Fin n)) :=
  M.powerset.filter (fun X => Con gates M c τ k X)

open Classical in
theorem symm_mem {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool) (k : ℕ) (X Y : Finset (Fin n)) (hX : X ∈ P gates M c τ k)
    (hY : Y ⊆ M) (hYc : Con gates M c τ k Y) : symmDiff X Y ∈ P gates M c τ k := by
  rw [P, Finset.mem_filter, Finset.mem_powerset] at hX ⊢
  refine ⟨?_, con_symm gates M c τ k X Y hX.2 hYc⟩
  intro v hv
  rw [Finset.mem_symmDiff] at hv
  rcases hv with hv | hv
  · exact hX.1 hv.1
  · exact hY hv.1

open Classical in
theorem step {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (g : Fin gates.length) :
    (P gates M c τ ((g : ℕ) + 1)).card * (if Mrg gates M c τ g then 2 else 1)
      = (P gates M c τ (g : ℕ)).card := by
  by_cases hal : (gates.get g).op = GateOp.or ∧ val gates (n + (g : ℕ)) c = false ∧
      ∃ a b : ℕ, (gates.get g).inputs = [a, b]
  swap
  · have hnm : ¬ Mrg gates M c τ g := by
      rintro ⟨h1, h2, w1, w2, h3, _⟩
      exact hal ⟨h1, h2, w1, w2, h3⟩
    have hP : P gates M c τ ((g : ℕ) + 1) = P gates M c τ (g : ℕ) := by
      unfold P
      apply Finset.filter_congr
      intro X _
      rw [con_succ gates M c τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, ?_⟩
        intro ho hc' a b hab
        exact absurd ⟨ho, hc', a, b, hab⟩ hal
    rw [hP, if_neg hnm, Nat.mul_one]
  · obtain ⟨ho, hgc, a, b, hab⟩ := hal
    have hma : a ∈ (gates.get g).inputs := by rw [hab]; simp
    have hmb : b ∈ (gates.get g).inputs := by rw [hab]; simp
    have ha : a < n + (g : ℕ) := hin g a hma
    have hb : b < n + (g : ℕ) := hin g b hmb
    have hac : val gates a c = false := by
      cases hv : val gates a c with
      | false => rfl
      | true =>
        have ht : val gates (n + (g : ℕ)) c = true :=
          (val_or gates c g g.2 ho).2 ⟨a, hma, ha, hv⟩
        rw [ht] at hgc
        exact Bool.noConfusion hgc
    have hbc : val gates b c = false := by
      cases hv : val gates b c with
      | false => rfl
      | true =>
        have ht : val gates (n + (g : ℕ)) c = true :=
          (val_or gates c g g.2 ho).2 ⟨b, hmb, hb, hv⟩
        rw [ht] at hgc
        exact Bool.noConfusion hgc
    have sA : ∀ X, Con gates M c τ g X → ∀ y ∈ M, ∀ y' ∈ M, val gates a (τ y) = true →
        val gates a (τ y') = true → (y ∈ X ↔ y' ∈ X) := fun X hX =>
      single gates M c τ hτ legal hin g (le_of_lt g.2) X hX a ha hac
    have sB : ∀ X, Con gates M c τ g X → ∀ y ∈ M, ∀ y' ∈ M, val gates b (τ y) = true →
        val gates b (τ y') = true → (y ∈ X ↔ y' ∈ X) := fun X hX =>
      single gates M c τ hτ legal hin g (le_of_lt g.2) X hX b hb hbc
    by_cases hm : ∃ r ∈ M, ∃ r' ∈ M, val gates a (τ r) = true ∧ val gates b (τ r') = true ∧
        ∃ X : Finset (Fin n), r ∈ X ∧ r' ∉ X ∧ Con gates M c τ (g : ℕ) X
    · have hmrg : Mrg gates M c τ g := ⟨ho, hgc, a, b, hab, hm⟩
      obtain ⟨r, hr, r', hr', hra, hrb, X0, hrX, hr'X, hX0⟩ := hm
      rw [if_pos hmrg]
      have hP : P gates M c τ ((g : ℕ) + 1)
          = (P gates M c τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X) := by
        unfold P
        rw [Finset.filter_filter]
        apply Finset.filter_congr
        intro X _
        rw [con_succ gates M c τ g g.2 X]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1, h2 ho hgc a b hab r hr r' hr' (Or.inl hra) (Or.inr hrb)⟩
        · rintro ⟨h1, h2⟩
          refine ⟨h1, cl_of gates M c τ g X a b hab (sA X h1) (sB X h1) ?_⟩
          intro y hy y' hy' hya hyb
          exact ((sA X h1 y hy r hr hya hra).trans h2).trans (sB X h1 r' hr' y' hy' hrb hyb)
      rw [hP]
      have hsplit := Finset.card_filter_add_card_filter_not (s := P gates M c τ (g : ℕ))
        (fun X => r ∈ X ↔ r' ∈ X)
      have hY0 : X0 ∩ M ⊆ M := Finset.inter_subset_right
      have hY0c := con_inter gates M c τ g X0 hX0
      have hrY : r ∈ X0 ∩ M := Finset.mem_inter.2 ⟨hrX, hr⟩
      have hr'Y : r' ∉ X0 ∩ M := fun h => hr'X (Finset.mem_inter.1 h).1
      have hbij : ((P gates M c τ (g : ℕ)).filter (fun X => ¬ (r ∈ X ↔ r' ∈ X))).card
          = ((P gates M c τ (g : ℕ)).filter (fun X => r ∈ X ↔ r' ∈ X)).card := by
        refine Finset.card_bij' (fun X _ => symmDiff X (X0 ∩ M)) (fun X _ => symmDiff X (X0 ∩ M))
          ?_ ?_ ?_ ?_
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨symm_mem gates M c τ g X _ hX.1 hY0 hY0c, ?_⟩
          exact (symm_flip X (X0 ∩ M) r r' hrY hr'Y).2 hX.2
        · intro X hX
          rw [Finset.mem_filter] at hX ⊢
          refine ⟨symm_mem gates M c τ g X _ hX.1 hY0 hY0c, ?_⟩
          intro hcon
          exact (symm_flip X (X0 ∩ M) r r' hrY hr'Y).1 hcon hX.2
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
        · intro X _
          exact symmDiff_symmDiff_cancel_right _ _
      omega
    · have hnm : ¬ Mrg gates M c τ g := by
        rintro ⟨_, _, w1, w2, h3, r, hr, r', hr', h4, h5, h6⟩
        rw [hab] at h3
        obtain ⟨e1, e2⟩ : a = w1 ∧ b = w2 := by simpa using h3
        subst e1
        subst e2
        exact hm ⟨r, hr, r', hr', h4, h5, h6⟩
      rw [if_neg hnm, Nat.mul_one]
      congr 1
      unfold P
      apply Finset.filter_congr
      intro X _
      rw [con_succ gates M c τ g g.2 X]
      constructor
      · exact fun h => h.1
      · intro h
        refine ⟨h, cl_of gates M c τ g X a b hab (sA X h) (sB X h) ?_⟩
        intro y hy y' hy' hya hyb
        constructor
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, X, hyX, hn, h⟩
        · intro hyX
          by_contra hn
          exact hm ⟨y, hy, y', hy', hya, hyb, Xᶜ, Finset.mem_compl.2 hn,
            fun h' => Finset.mem_compl.1 h' hyX, con_compl gates M c τ g X h⟩

open Classical in
theorem count {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (k : ℕ) (hk : k ≤ gates.length) :
    (P gates M c τ k).card *
      2 ^ (∑ g : Fin gates.length, if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
      = 2 ^ M.card := by
  induction k with
  | zero =>
    have h0 : P gates M c τ 0 = M.powerset := by
      unfold P
      apply Finset.filter_true_of_mem
      intro X _ i hi
      exact absurd hi (Nat.not_lt_zero _)
    rw [h0, Finset.card_powerset]
    simp
  | succ k ih =>
    have hk' : k < gates.length := hk
    have hs : (P gates M c τ (k + 1)).card * (if Mrg gates M c τ ⟨k, hk'⟩ then 2 else 1)
        = (P gates M c τ k).card := step gates M c τ hτ legal hin ⟨k, hk'⟩
    have hsum : (∑ g : Fin gates.length, if (g : ℕ) < k + 1 ∧ Mrg gates M c τ g then 1 else 0)
        = (∑ g : Fin gates.length, if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
          + (if Mrg gates M c τ ⟨k, hk'⟩ then 1 else 0) := by
      have hpt : ∀ g : Fin gates.length,
          (if (g : ℕ) < k + 1 ∧ Mrg gates M c τ g then 1 else 0)
          = (if (g : ℕ) < k ∧ Mrg gates M c τ g then 1 else 0)
            + (if g = ⟨k, hk'⟩ then (if Mrg gates M c τ ⟨k, hk'⟩ then 1 else 0) else 0) := by
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
theorem mcount {n : ℕ} (gates : List Gate) (M : Finset (Fin n)) (c : Fin n → Bool)
    (τ : Fin n → Fin n → Bool)
    (hτ : ∀ p ∈ M, ∀ v, τ p v = true → v = p)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hM : 1 ≤ M.card) (o : ℕ) (hoc : val gates o c = false)
    (hot : ∀ p ∈ M, val gates o (τ p) = true) :
    (∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0) = M.card - 1 := by
  have hne : M.Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨p0, hp0⟩ := hne
  have holt : o < n + gates.length := by
    by_contra h
    have hb := val_big gates (τ p0) o (by omega)
    rw [hot p0 hp0] at hb
    exact Bool.noConfusion hb
  have hfin : P gates M c τ gates.length = {∅, M} := by
    ext X
    rw [P, Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hsub, hX⟩
      have hs := single gates M c τ hτ legal hin gates.length le_rfl X hX o holt hoc
      by_cases hex : ∃ y ∈ M, y ∈ X
      · obtain ⟨y, hy, hyX⟩ := hex
        right
        apply Finset.Subset.antisymm hsub
        intro z hz
        exact (hs y hy z hz (hot y hy) (hot z hz)).1 hyX
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
  have hcnt := count gates M c τ hτ legal hin gates.length le_rfl
  have hpair : ({∅, M} : Finset (Finset (Fin n))).card = 2 := by
    apply Finset.card_pair
    intro h
    rw [← h] at hp0
    simp at hp0
  rw [hfin, hpair] at hcnt
  have hsum : (∑ g : Fin gates.length, if (g : ℕ) < gates.length ∧ Mrg gates M c τ g then 1 else 0)
      = ∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0 :=
    Finset.sum_congr rfl (fun g _ => by simp [g.2])
  rw [hsum] at hcnt
  have hm1 : 2 ^ M.card = 2 * 2 ^ (M.card - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have h8 : 2 ^ (∑ g : Fin gates.length, if Mrg gates M c τ g then 1 else 0) = 2 ^ (M.card - 1) :=
    Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 2) (hcnt.trans hm1)
  exact Nat.pow_right_injective (le_refl 2) h8

theorem val_mono (gates : List Gate) {n : ℕ}
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

theorem disj {n : ℕ} (gates : List Gate)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (L1 L2 A1 A2 : Finset (Fin n)) (hA : A1 ⊆ L1) (hcard : (L1 ∩ L2).card ≤ 1)
    (g : Fin gates.length)
    (h1 : Mrg gates A1 (fun v => decide (v ∉ L1)) (fun y v => decide (v = y)) g)
    (h2 : Mrg gates A2 (fun v => decide (v ∉ L2)) (fun y v => decide (v = y)) g) : False := by
  obtain ⟨ho, _, w1, w2, hab, r, hr, r', hr', hv1, hv2, X, hrX, hr'X, _⟩ := h1
  obtain ⟨_, hc2, _⟩ := h2
  have hne : r ≠ r' := fun e => hr'X (e ▸ hrX)
  have hm1 : w1 ∈ (gates.get g).inputs := by rw [hab]; simp
  have hm2 : w2 ∈ (gates.get g).inputs := by rw [hab]; simp
  have ht1 : val gates (n + (g : ℕ)) (fun v : Fin n => decide (v = r)) = true :=
    (val_or gates _ g g.2 ho).2 ⟨w1, hm1, hin g w1 hm1, hv1⟩
  have ht2 : val gates (n + (g : ℕ)) (fun v : Fin n => decide (v = r')) = true :=
    (val_or gates _ g g.2 ho).2 ⟨w2, hm2, hin g w2 hm2, hv2⟩
  have key : ∀ s : Fin n, val gates (n + (g : ℕ)) (fun v : Fin n => decide (v = s)) = true →
      s ∈ L2 := by
    intro s hs
    by_contra hns
    have hmo := val_mono gates legal (fun v : Fin n => decide (v = s))
      (fun v : Fin n => decide (v ∉ L2)) (by
        intro v hv
        have e : v = s := of_decide_eq_true hv
        rw [e]
        exact decide_eq_true hns) _ hs
    rw [hc2] at hmo
    exact Bool.noConfusion hmo
  have hr2 := key r ht1
  have hr2' := key r' ht2
  have hsub : ({r, r'} : Finset (Fin n)) ⊆ L1 ∩ L2 := by
    intro v hv
    rw [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with e | e
    · rw [e]; exact Finset.mem_inter.2 ⟨hA hr, hr2⟩
    · rw [e]; exact Finset.mem_inter.2 ⟨hA hr', hr2'⟩
  have hc := Finset.card_le_card hsub
  rw [Finset.card_pair hne] at hc
  omega

def MJ {n m : ℕ} (gates : List Gate) (L A : Fin m → Finset (Fin n)) (j : Fin m)
    (g : Fin gates.length) : Prop :=
  Mrg gates (A j) (fun v => decide (v ∉ L j)) (fun y v => decide (v = y)) g

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

open PEqualNP.EdgeOwnership in
lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.EdgeOwnership in
lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h

def adjb (s t : Fin 26) : Bool :=
  decide (s.val < 13 ∧ 13 ≤ t.val ∧ (s.val + 26 - t.val) % 13 ∈ [0, 1, 3, 9]) ||
  decide (t.val < 13 ∧ 13 ≤ s.val ∧ (t.val + 26 - s.val) % 13 ∈ [0, 1, 3, 9])

def mk (f g : Fin 13 → Bool) (u : Fin 26) : Bool :=
  if h : u.val < 13 then f ⟨u.val, h⟩ else g ⟨u.val - 13, by omega⟩

theorem mk_eq (f g : Fin 13 → Bool) : List.ofFn f ++ List.ofFn g = List.ofFn (mk f g) := by
  have hl : (List.ofFn f).length = 13 := List.length_ofFn
  apply List.ext_getElem
  · rw [List.length_append, List.length_ofFn, List.length_ofFn, List.length_ofFn]
  · intro i h1 h2
    rw [List.getElem_ofFn]
    by_cases h : i < 13
    · rw [List.getElem_append_left (by rw [hl]; exact h), List.getElem_ofFn]
      unfold mk
      rw [dif_pos h]
    · rw [List.getElem_append_right (by rw [hl]; omega), List.getElem_ofFn]
      unfold mk
      rw [dif_neg h]
      congr 2

def pr (s t : Fin 26) : Fin 26 → Bool := fun u => decide (u = s ∨ u = t)

def N (v : Fin 26) : Finset (Fin 26) := Finset.univ.filter (fun y => adjb v y = true)

theorem mem_N (v y : Fin 26) : y ∈ N v ↔ adjb v y = true := by
  simp [N]

def qin (Q : Finset (Fin 13)) : Fin 26 → Bool :=
  mk (fun u => decide (u ∈ Q)) (fun v => decide (∀ r ∈ Q, r - v ∉ ({0, 1, 3, 9} : Finset (Fin 13))))

def ein (p l : Fin 13) : Fin 26 → Bool :=
  mk (fun x => decide (x = p)) (fun x => decide (x = l))

def Pp (s t : Fin 26) : Fin 13 := ⟨(min s.val t.val) % 13, Nat.mod_lt _ (by norm_num)⟩

def Ll (s t : Fin 26) : Fin 13 := ⟨(max s.val t.val - 13) % 13, Nat.mod_lt _ (by norm_num)⟩

theorem adj_irr : ∀ s : Fin 26, adjb s s = false := by decide +kernel

theorem adj_symm : ∀ s t : Fin 26, adjb s t = adjb t s := by decide +kernel

theorem hLN : ∀ i j : Fin 26, i ≠ j → (N i ∩ N j).card ≤ 1 := by
  intro i
  fin_cases i <;> decide +kernel

theorem degN : ∀ v : Fin 26, (N v).card = 4 := by decide +kernel

theorem adj_total :
    ∑ v : Fin 26, ∑ y : Fin 26, (if adjb v y = true then (1 : ℕ) else 0) = 104 := by
  decide +kernel

theorem k22 (s1 s2 t1 t2 : Fin 26) (h11 : adjb s1 t1 = true) (h12 : adjb s1 t2 = true)
    (h21 : adjb s2 t1 = true) (h22 : adjb s2 t2 = true) (hne : s1 ≠ s2) : t1 = t2 := by
  have hc := hLN s1 s2 hne
  rw [Finset.card_le_one] at hc
  exact hc t1 (Finset.mem_inter.2 ⟨(mem_N _ _).2 h11, (mem_N _ _).2 h21⟩) t2
    (Finset.mem_inter.2 ⟨(mem_N _ _).2 h12, (mem_N _ _).2 h22⟩)

theorem legal_of (C : Circuit) (hmono : Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨h1, h2⟩ := hmono g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem hin_of (C : Circuit) (n : ℕ) (hrb : ReadsBack n C) :
    ∀ i : Fin C.gates.length, ∀ a ∈ (C.gates.get i).inputs, a < n + (i : ℕ) := by
  intro i a ha
  apply hrb i i.2 a
  unfold PEqualNP.MetaComplexity.NestedCover.gateAt
  rw [List.getD_eq_getElem _ _ i.2]
  exact ha

def Lin (gs : List Gate) (w : ℕ) : Prop :=
  ∀ x : Fin 26 → Bool, val gs w x = true →
    ∃ u : Fin 26, x u = true ∧ val gs w (fun v => decide (v = u)) = true

open PEqualNP.EdgeOwnership in
theorem lin_ind (C : Circuit)
    (legal : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin C.gates.length, ∀ a ∈ (C.gates.get i).inputs, a < 26 + (i : ℕ)) :
    ∀ w, (26 ≤ w → w - 26 < C.gates.length → (gateAt C (w - 26)).op = GateOp.or ∧
      ∀ i, InCone 26 C i (w - 26) → (gateAt C i).op ≠ GateOp.and) → Lin C.gates w := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw x hx
    by_cases hwn : w < 26
    · refine ⟨⟨w, hwn⟩, ?_, ?_⟩
      · rw [val_input C.gates _ w hwn] at hx
        exact hx
      · rw [val_input C.gates _ w hwn]
        simp
    · by_cases hbig : 26 + C.gates.length ≤ w
      · rw [val_big C.gates x w hbig] at hx
        exact Bool.noConfusion hx
      · have hi : w - 26 < C.gates.length := by omega
        have he : 26 + (w - 26) = w := by omega
        obtain ⟨hor, hcone⟩ := hw (by omega) hi
        rw [gateAt_eq C _ hi] at hor
        have hx' : val C.gates (26 + (w - 26)) x = true := by rw [he]; exact hx
        obtain ⟨a, ha, halt, hav⟩ := (val_or C.gates x (w - 26) hi hor).1 hx'
        have hga : a ∈ (gateAt C (w - 26)).inputs := by rw [gateAt_eq C _ hi]; exact ha
        have hla : Lin C.gates a := by
          apply ih a (by omega)
          intro ha26 hai
          have hic : InCone 26 C (a - 26) (w - 26) :=
            (inCone_iff 26 C (a - 26) (w - 26) hi).2 ⟨a, hga, ha26, halt, Or.inl rfl⟩
          have hna := hcone _ hic
          refine ⟨?_, ?_⟩
          · rw [gateAt_eq C _ hai] at hna ⊢
            rcases (legal _ (List.getElem_mem hai)).1 with h | h
            · exact absurd h hna
            · exact h
          · intro i hi2
            exact hcone i ((inCone_iff 26 C i (w - 26) hi).2 ⟨a, hga, ha26, halt, Or.inr hi2⟩)
        obtain ⟨u, hu, huv⟩ := hla x hav
        refine ⟨u, hu, ?_⟩
        rw [← he]
        exact (val_or C.gates _ (w - 26) hi hor).2 ⟨a, ha, halt, huv⟩

open PEqualNP.EdgeOwnership in
theorem lin_and (C : Circuit)
    (legal : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin C.gates.length, ∀ a ∈ (C.gates.get i).inputs, a < 26 + (i : ℕ))
    (hflat : ¬ ∃ i j, (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      InCone 26 C i j)
    (j : ℕ) (hj : j < C.gates.length) (hop : C.gates[j].op = GateOp.and) (a : ℕ)
    (ha : a ∈ C.gates[j].inputs) : Lin C.gates a := by
  have halt : a < 26 + j := hin ⟨j, hj⟩ a ha
  have hgj : (gateAt C j).op = GateOp.and := by rw [gateAt_eq C j hj]; exact hop
  have hga : a ∈ (gateAt C j).inputs := by rw [gateAt_eq C j hj]; exact ha
  apply lin_ind C legal hin a
  intro ha26 hai
  have hic : InCone 26 C (a - 26) j :=
    (inCone_iff 26 C (a - 26) j hj).2 ⟨a, hga, ha26, halt, Or.inl rfl⟩
  refine ⟨?_, ?_⟩
  · rcases (legal _ (List.getElem_mem hai)).1 with h | h
    · exact absurd ⟨a - 26, j, by rw [gateAt_eq C _ hai]; exact h, hgj, hic⟩ hflat
    · rw [gateAt_eq C _ hai]; exact h
  · intro i hi2 hand
    exact hflat ⟨i, j, hand, hgj,
      (inCone_iff 26 C i j hj).2 ⟨a, hga, ha26, halt, Or.inr hi2⟩⟩

def Reach (gs : List Gate) (o : ℕ) (w : ℕ) : Prop :=
  ∀ S : ℕ → Prop, S o →
    (∀ (k : ℕ) (hk : k < gs.length), gs[k].op = GateOp.or → S (26 + k) →
      ∀ a ∈ gs[k].inputs, S a) → S w

theorem reach_out (gs : List Gate) (o : ℕ) : Reach gs o o := fun _ h _ => h

theorem reach_step (gs : List Gate) (o : ℕ) (k : ℕ) (hk : k < gs.length)
    (hop : gs[k].op = GateOp.or) (hr : Reach gs o (26 + k)) (a : ℕ) (ha : a ∈ gs[k].inputs) :
    Reach gs o a :=
  fun S h0 hs => hs k hk hop (hr S h0 hs) a ha

theorem reach_imp (gs : List Gate) (o : ℕ)
    (hin : ∀ i : Fin gs.length, ∀ a ∈ (gs.get i).inputs, a < 26 + (i : ℕ))
    (w : ℕ) (hr : Reach gs o w) :
    ∀ x : Fin 26 → Bool, val gs w x = true → val gs o x = true := by
  apply hr (fun w => ∀ x : Fin 26 → Bool, val gs w x = true → val gs o x = true)
  · intro x h
    exact h
  · intro k hk hop hS a ha x hx
    exact hS x ((val_or gs x k hk hop).2 ⟨a, ha, hin ⟨k, hk⟩ a ha, hx⟩)

theorem reach_down (gs : List Gate) (o : ℕ)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x : Fin 26 → Bool) :
    ∀ w, Reach gs o w → val gs w x = true →
      ∃ w', Reach gs o w' ∧ val gs w' x = true ∧
        (w' < 26 ∨ ∃ (j : ℕ) (hj : j < gs.length), w' = 26 + j ∧ gs[j].op = GateOp.and) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hr hx
    by_cases hwn : w < 26
    · exact ⟨w, hr, hx, Or.inl hwn⟩
    · by_cases hbig : 26 + gs.length ≤ w
      · rw [val_big gs x w hbig] at hx
        exact Bool.noConfusion hx
      · have hi : w - 26 < gs.length := by omega
        have he : 26 + (w - 26) = w := by omega
        rcases (legal gs[w - 26] (List.getElem_mem hi)).1 with ha | ho
        · exact ⟨w, hr, hx, Or.inr ⟨w - 26, hi, he.symm, ha⟩⟩
        · have hx' : val gs (26 + (w - 26)) x = true := by rw [he]; exact hx
          have hr' : Reach gs o (26 + (w - 26)) := by rw [he]; exact hr
          obtain ⟨a, ha, halt, hav⟩ := (val_or gs x (w - 26) hi ho).1 hx'
          exact ih a (by omega) (reach_step gs o (w - 26) hi ho hr' a ha) hav

theorem reach_parent (gs : List Gate) (o : ℕ) (w : ℕ) (hr : Reach gs o w) :
    w = o ∨ ∃ (k : ℕ) (hk : k < gs.length), gs[k].op = GateOp.or ∧ Reach gs o (26 + k) ∧
      w ∈ gs[k].inputs := by
  apply hr (fun w => w = o ∨ ∃ (k : ℕ) (hk : k < gs.length), gs[k].op = GateOp.or ∧
    Reach gs o (26 + k) ∧ w ∈ gs[k].inputs)
  · exact Or.inl rfl
  · intro k hk hop hS a ha
    right
    refine ⟨k, hk, hop, ?_, ha⟩
    rcases hS with h | ⟨k', hk', hop', hr', hmem⟩
    · rw [h]
      exact reach_out gs o
    · exact reach_step gs o k' hk' hop' hr' _ hmem

open Classical in
theorem top_count (gs : List Gate) (o : ℕ)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (U RO : Finset (Fin gs.length))
    (hU : ∀ j ∈ U, (gs.get j).op = GateOp.and ∧ Reach gs o (26 + (j : ℕ)))
    (hRO : ∀ j, j ∈ RO ↔ ((gs.get j).op = GateOp.or ∧ Reach gs o (26 + (j : ℕ)))) :
    U.card ≤ RO.card + 1 := by
  have hdisj : Disjoint U RO := by
    rw [Finset.disjoint_left]
    intro j h1 h2
    have a1 := (hU j h1).1
    have a2 := ((hRO j).1 h2).1
    rw [a1] at a2
    exact GateOp.noConfusion a2
  have hsub : (U ∪ RO).image (fun j : Fin gs.length => 26 + (j : ℕ)) ⊆
      insert o (RO.biUnion (fun k => (gs.get k).inputs.toFinset)) := by
    intro w hw
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hw
    have hr : Reach gs o (26 + (j : ℕ)) := by
      rcases Finset.mem_union.1 hj with h | h
      · exact (hU j h).2
      · exact ((hRO j).1 h).2
    rcases reach_parent gs o _ hr with h | ⟨k, hk, hop, hrk, hmem⟩
    · rw [h]
      exact Finset.mem_insert_self _ _
    · apply Finset.mem_insert_of_mem
      rw [Finset.mem_biUnion]
      exact ⟨⟨k, hk⟩, (hRO ⟨k, hk⟩).2 ⟨hop, hrk⟩, List.mem_toFinset.2 hmem⟩
  have hinj : Function.Injective (fun j : Fin gs.length => 26 + (j : ℕ)) := by
    intro a b h
    apply Fin.ext
    simpa using h
  have hc1 : ((U ∪ RO).image (fun j : Fin gs.length => 26 + (j : ℕ))).card
      = U.card + RO.card := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_union_of_disjoint hdisj]
  have hc2 : (RO.biUnion (fun k => (gs.get k).inputs.toFinset)).card ≤ RO.card * 2 := by
    refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_card_nsmul _ _ 2 ?_).trans (by simp)
    intro k _
    exact (List.toFinset_card_le _).trans (legal _ (List.getElem_mem k.2)).2
  have hc3 := Finset.card_le_card hsub
  have hc4 := Finset.card_insert_le o (RO.biUnion (fun k => (gs.get k).inputs.toFinset))
  omega

open Classical in
theorem mrg_count {n m : ℕ} (L A : Fin m → Finset (Fin n)) (gates : List Gate) (o : Fin m → ℕ)
    (hL : ∀ i j : Fin m, i ≠ j → (L i ∩ L j).card ≤ 1)
    (legal : ∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hin : ∀ i : Fin gates.length, ∀ a ∈ (gates.get i).inputs, a < n + (i : ℕ))
    (hA : ∀ j : Fin m, A j ⊆ L j)
    (hot : ∀ (j : Fin m) (p : Fin n), p ∈ A j →
      val gates (o j) (fun i : Fin n => decide (i = p)) = true)
    (hoc : ∀ j : Fin m, 1 ≤ (A j).card →
      val gates (o j) (fun i : Fin n => decide (i ∉ L j)) = false) :
    ∑ j : Fin m, ((A j).card - 1) ≤
      (Finset.univ.filter (fun g : Fin gates.length => ∃ j, MJ gates L A j g)).card := by
  have h1 : ∀ j : Fin m, (A j).card - 1 ≤
      ∑ g : Fin gates.length, (if MJ gates L A j g then (1 : ℕ) else 0) := by
    intro j
    by_cases hc : 1 ≤ (A j).card
    · exact le_of_eq (mcount gates (A j) (fun v => decide (v ∉ L j)) (fun y v => decide (v = y))
        (fun p _ v hv => of_decide_eq_true hv) legal hin hc (o j) (hoc j hc)
        (fun p hp => hot j p hp)).symm
    · have hz : (A j).card - 1 = 0 := by omega
      rw [hz]
      exact Nat.zero_le _
  have h2 : ∀ g : Fin gates.length,
      (∑ j : Fin m, (if MJ gates L A j g then (1 : ℕ) else 0)) ≤
        (if ∃ j, MJ gates L A j g then (1 : ℕ) else 0) := by
    intro g
    by_cases hex : ∃ j0 : Fin m, MJ gates L A j0 g
    · rw [if_pos hex]
      obtain ⟨j0, hj0⟩ := hex
      have hle : ∀ j ∈ (Finset.univ : Finset (Fin m)),
          (if MJ gates L A j g then (1 : ℕ) else 0) ≤ (if j = j0 then (1 : ℕ) else 0) := by
        intro j _
        by_cases hj : MJ gates L A j g
        · have e : j = j0 := by
            by_contra hne
            exact disj gates legal hin (L j) (L j0) (A j) (A j0) (hA j) (hL j j0 hne) g hj hj0
          rw [if_pos hj, if_pos e]
        · rw [if_neg hj]
          exact Nat.zero_le _
      refine (Finset.sum_le_sum hle).trans ?_
      simp
    · have hz : ∀ j ∈ (Finset.univ : Finset (Fin m)),
          (if MJ gates L A j g then (1 : ℕ) else 0) = 0 :=
        fun j _ => if_neg (fun h => hex ⟨j, h⟩)
      rw [Finset.sum_eq_zero hz]
      exact Nat.zero_le _
  calc ∑ j : Fin m, ((A j).card - 1)
      ≤ ∑ j : Fin m, ∑ g : Fin gates.length, (if MJ gates L A j g then (1 : ℕ) else 0) :=
        Finset.sum_le_sum (fun j _ => h1 j)
    _ = ∑ g : Fin gates.length, ∑ j : Fin m, (if MJ gates L A j g then (1 : ℕ) else 0) :=
        Finset.sum_comm
    _ ≤ ∑ g : Fin gates.length, (if ∃ j, MJ gates L A j g then (1 : ℕ) else 0) :=
        Finset.sum_le_sum (fun g _ => h2 g)
    _ = (Finset.univ.filter (fun g : Fin gates.length => ∃ j, MJ gates L A j g)).card := by
        rw [Finset.card_filter]

def Hy (gs : List Gate) (o : ℕ) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) ∧
  (∀ i : Fin gs.length, ∀ a ∈ (gs.get i).inputs, a < 26 + (i : ℕ)) ∧
  (∀ (j : ℕ) (hj : j < gs.length), gs[j].op = GateOp.and → ∀ a ∈ gs[j].inputs, Lin gs a) ∧
  (∀ s t : Fin 26, adjb s t = true → val gs o (pr s t) = true) ∧
  (∀ s t : Fin 26, adjb s t = false → val gs o (pr s t) = false)

theorem reach_adj (gs : List Gate) (o : ℕ) (H : Hy gs o) (w : ℕ) (hr : Reach gs o w)
    (s t : Fin 26) (h : val gs w (pr s t) = true) : adjb s t = true := by
  have h2 := reach_imp gs o H.2.1 w hr _ h
  cases hb : adjb s t with
  | true => rfl
  | false =>
    rw [H.2.2.2.2 s t hb] at h2
    exact Bool.noConfusion h2

theorem val_e_pr (gs : List Gate)
    (legal : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : ℕ) (s t u : Fin 26) (hu : u = s ∨ u = t)
    (h : val gs w (fun v : Fin 26 => decide (v = u)) = true) : val gs w (pr s t) = true :=
  val_mono gs legal _ _ (by
    intro v hv
    have e : v = u := of_decide_eq_true hv
    rw [e]
    exact decide_eq_true hu) w h

theorem reach_single (gs : List Gate) (o : ℕ) (H : Hy gs o) (w : ℕ) (hr : Reach gs o w)
    (s : Fin 26) (h : val gs w (fun v : Fin 26 => decide (v = s)) = true) : False := by
  have h2 := reach_adj gs o H w hr s s (val_e_pr gs H.1 w s s s (Or.inl rfl) h)
  rw [adj_irr s] at h2
  exact Bool.noConfusion h2

theorem and_struct (gs : List Gate) (o : ℕ) (H : Hy gs o) (j : ℕ) (hj : j < gs.length)
    (hop : gs[j].op = GateOp.and) (hr : Reach gs o (26 + j)) (s0 t0 : Fin 26)
    (h0 : val gs (26 + j) (pr s0 t0) = true) : ∃ a b : ℕ, gs[j].inputs = [a, b] := by
  have hlen := (H.1 gs[j] (List.getElem_mem hj)).2
  have hall := (val_and gs (pr s0 t0) j hj hop).1 h0
  have hlinj := H.2.2.1 j hj hop
  rcases hinp : gs[j].inputs with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
  · exfalso
    apply reach_single gs o H _ hr s0
    apply (val_and gs _ j hj hop).2
    intro i hi
    rw [hinp] at hi
    simp at hi
  · exfalso
    have ha : a ∈ gs[j].inputs := by rw [hinp]; simp
    obtain ⟨halt, hav⟩ := hall a ha
    obtain ⟨u, hu, huv⟩ := hlinj a ha _ hav
    apply reach_single gs o H _ hr u
    apply (val_and gs _ j hj hop).2
    intro i hi
    rw [hinp] at hi
    have e : i = a := by simpa using hi
    rw [e]
    exact ⟨halt, huv⟩
  · exact ⟨a, b, rfl⟩
  · rw [hinp] at hlen
    simp at hlen

theorem star (gs : List Gate) (o : ℕ) (H : Hy gs o) (j : ℕ) (hj : j < gs.length)
    (hop : gs[j].op = GateOp.and) (hr : Reach gs o (26 + j)) (s0 t0 : Fin 26)
    (h0 : val gs (26 + j) (pr s0 t0) = true) :
    ∃ (z : Fin 26) (A : Finset (Fin 26)) (lw : ℕ), A ⊆ N z ∧
      (∀ p ∈ A, val gs lw (fun v : Fin 26 => decide (v = p)) = true) ∧
      val gs lw (fun v : Fin 26 => decide (v ∉ N z)) = false ∧
      ∀ s t : Fin 26, val gs (26 + j) (pr s t) = true → (s = z ∧ t ∈ A) ∨ (t = z ∧ s ∈ A) := by
  obtain ⟨a, b, hab⟩ := and_struct gs o H j hj hop hr s0 t0 h0
  have ha : a ∈ gs[j].inputs := by rw [hab]; simp
  have hb : b ∈ gs[j].inputs := by rw [hab]; simp
  have halt : a < 26 + j := H.2.1 ⟨j, hj⟩ a ha
  have hblt : b < 26 + j := H.2.1 ⟨j, hj⟩ b hb
  have la : Lin gs a := H.2.2.1 j hj hop a ha
  have lb : Lin gs b := H.2.2.1 j hj hop b hb
  have hST : ∀ s t : Fin 26, val gs a (fun v : Fin 26 => decide (v = s)) = true →
      val gs b (fun v : Fin 26 => decide (v = t)) = true → adjb s t = true := by
    intro s t hs ht
    apply reach_adj gs o H _ hr s t
    apply (val_and gs _ j hj hop).2
    intro i hi
    rw [hab] at hi
    rcases List.mem_pair.1 hi with e | e
    · rw [e]
      exact ⟨halt, val_e_pr gs H.1 a s t s (Or.inl rfl) hs⟩
    · rw [e]
      exact ⟨hblt, val_e_pr gs H.1 b s t t (Or.inr rfl) ht⟩
  have hcov : ∀ s t : Fin 26, val gs (26 + j) (pr s t) = true →
      (val gs a (fun v : Fin 26 => decide (v = s)) = true ∧
        val gs b (fun v : Fin 26 => decide (v = t)) = true) ∨
      (val gs a (fun v : Fin 26 => decide (v = t)) = true ∧
        val gs b (fun v : Fin 26 => decide (v = s)) = true) := by
    intro s t h
    have hall := (val_and gs (pr s t) j hj hop).1 h
    obtain ⟨u1, hu1, hv1⟩ := la _ (hall a ha).2
    obtain ⟨u2, hu2, hv2⟩ := lb _ (hall b hb).2
    have hadj := hST u1 u2 hv1 hv2
    have e1 : u1 = s ∨ u1 = t := of_decide_eq_true hu1
    have e2 : u2 = s ∨ u2 = t := of_decide_eq_true hu2
    have hne : u1 ≠ u2 := by
      intro e
      rw [e, adj_irr] at hadj
      exact Bool.noConfusion hadj
    rcases e1 with e1 | e1 <;> rcases e2 with e2 | e2
    · exact absurd (e1.trans e2.symm) hne
    · left
      rw [← e1, ← e2]
      exact ⟨hv1, hv2⟩
    · right
      rw [← e1, ← e2]
      exact ⟨hv1, hv2⟩
    · exact absurd (e1.trans e2.symm) hne
  have hne : ∃ sa tb : Fin 26, val gs a (fun v : Fin 26 => decide (v = sa)) = true ∧
      val gs b (fun v : Fin 26 => decide (v = tb)) = true := by
    rcases hcov s0 t0 h0 with h | h
    · exact ⟨s0, t0, h⟩
    · exact ⟨t0, s0, h⟩
  obtain ⟨sa, tb, hsa, htb⟩ := hne
  by_cases hT : ∀ t : Fin 26, val gs b (fun v : Fin 26 => decide (v = t)) = true → t = tb
  · refine ⟨tb, Finset.univ.filter
      (fun s : Fin 26 => val gs a (fun v : Fin 26 => decide (v = s)) = true), a, ?_, ?_, ?_, ?_⟩
    · intro s hs
      rw [Finset.mem_filter] at hs
      rw [mem_N, adj_symm]
      exact hST s tb hs.2 htb
    · intro p hp
      exact (Finset.mem_filter.1 hp).2
    · cases hv : val gs a (fun v : Fin 26 => decide (v ∉ N tb)) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨u, hu, huv⟩ := la _ hv
        have hu' : u ∉ N tb := of_decide_eq_true hu
        apply hu'
        rw [mem_N, adj_symm]
        exact hST u tb huv htb
    · intro s t h
      rcases hcov s t h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · right
        exact ⟨hT t h2, Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩⟩
      · left
        exact ⟨hT s h2, Finset.mem_filter.2 ⟨Finset.mem_univ _, h1⟩⟩
  · push_neg at hT
    obtain ⟨t1, ht1, hne1⟩ := hT
    have hS : ∀ s : Fin 26, val gs a (fun v : Fin 26 => decide (v = s)) = true → s = sa := by
      intro s hs
      by_contra hne2
      exact hne1 (k22 s sa t1 tb (hST s t1 hs ht1) (hST s tb hs htb) (hST sa t1 hsa ht1)
        (hST sa tb hsa htb) hne2)
    refine ⟨sa, Finset.univ.filter
      (fun t : Fin 26 => val gs b (fun v : Fin 26 => decide (v = t)) = true), b, ?_, ?_, ?_, ?_⟩
    · intro t ht
      rw [Finset.mem_filter] at ht
      rw [mem_N]
      exact hST sa t hsa ht.2
    · intro p hp
      exact (Finset.mem_filter.1 hp).2
    · cases hv : val gs b (fun v : Fin 26 => decide (v ∉ N sa)) with
      | false => rfl
      | true =>
        exfalso
        obtain ⟨u, hu, huv⟩ := lb _ hv
        have hu' : u ∉ N sa := of_decide_eq_true hu
        apply hu'
        rw [mem_N]
        exact hST sa u hsa huv
    · intro s t h
      rcases hcov s t h with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · left
        exact ⟨hS s h1, Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩⟩
      · right
        exact ⟨hS t h1, Finset.mem_filter.2 ⟨Finset.mem_univ _, h2⟩⟩

open Classical in
noncomputable def US (gs : List Gate) (o : ℕ) : Finset (Fin gs.length) :=
  Finset.univ.filter (fun j => (gs.get j).op = GateOp.and ∧ Reach gs o (26 + (j : ℕ)) ∧
    ∃ s t : Fin 26, val gs (26 + (j : ℕ)) (pr s t) = true)

open Classical in
noncomputable def ROS (gs : List Gate) (o : ℕ) : Finset (Fin gs.length) :=
  Finset.univ.filter (fun j => (gs.get j).op = GateOp.or ∧ Reach gs o (26 + (j : ℕ)))

open Classical in
noncomputable def MGS (gs : List Gate) (A' : Fin 26 → Finset (Fin 26)) :
    Finset (Fin gs.length) :=
  Finset.univ.filter (fun g : Fin gs.length => ∃ j, MJ gs N A' j g)

open Classical in
theorem mem_US (gs : List Gate) (o : ℕ) (j : Fin gs.length) :
    j ∈ US gs o ↔ ((gs.get j).op = GateOp.and ∧ Reach gs o (26 + (j : ℕ)) ∧
      ∃ s t : Fin 26, val gs (26 + (j : ℕ)) (pr s t) = true) := by
  unfold US
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

open Classical in
theorem mem_ROS (gs : List Gate) (o : ℕ) (j : Fin gs.length) :
    j ∈ ROS gs o ↔ ((gs.get j).op = GateOp.or ∧ Reach gs o (26 + (j : ℕ))) := by
  unfold ROS
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem cover (gs : List Gate) (o : ℕ) (H : Hy gs o) (v y : Fin 26) (hadj : adjb v y = true) :
    ∃ j : Fin gs.length, j ∈ US gs o ∧ val gs (26 + (j : ℕ)) (pr v y) = true := by
  have hout := H.2.2.2.1 v y hadj
  obtain ⟨w, hr, hx, hw⟩ := reach_down gs o H.1 (pr v y) o (reach_out gs o) hout
  rcases hw with hw | ⟨j, hj, e, hop⟩
  · exfalso
    apply reach_single gs o H w hr ⟨w, hw⟩
    rw [val_input gs _ w hw]
    simp
  · rw [e] at hr hx
    exact ⟨⟨j, hj⟩, (mem_US gs o _).2 ⟨hop, hr, v, y, hx⟩, hx⟩

theorem arith (b c m : ℕ) (h4 : b ≤ 4) (hm : b ≤ c * m) :
    5 * b ≤ 4 * (2 * c + (m - 1)) := by
  rcases c with _ | _ | _ | c
  · simp at hm
    omega
  · simp at hm
    omega
  · omega
  · clear hm
    omega

theorem tally {ι : Type} (U : Finset ι) (z : ι → Fin 26) (A : ι → Finset (Fin 26))
    (A' : Fin 26 → Finset (Fin 26))
    (h1 : ∀ j ∈ U, A j ⊆ N (z j)) (h2 : ∀ j ∈ U, (A j).card ≤ (A' (z j)).card)
    (h3 : ∀ v y : Fin 26, adjb v y = true →
      ∃ j ∈ U, (v = z j ∧ y ∈ A j) ∨ (y = z j ∧ v ∈ A j)) :
    260 ≤ 8 * U.card + 4 * ∑ v : Fin 26, ((A' v).card - 1) := by
  obtain ⟨B, hB⟩ : ∃ B : Fin 26 → Finset (Fin 26),
      ∀ v, B v = (U.filter (fun j => z j = v)).biUnion A := ⟨_, fun _ => rfl⟩
  have hB4 : ∀ v, (B v).card ≤ 4 := by
    intro v
    rw [← degN v, hB v]
    apply Finset.card_le_card
    intro y hy
    obtain ⟨j, hj, hyj⟩ := Finset.mem_biUnion.1 hy
    rw [Finset.mem_filter] at hj
    rw [← hj.2]
    exact h1 j hj.1 hyj
  have hBm : ∀ v, (B v).card ≤ (U.filter (fun j => z j = v)).card * (A' v).card := by
    intro v
    rw [hB v]
    refine Finset.card_biUnion_le.trans ?_
    refine (Finset.sum_le_card_nsmul _ _ ((A' v).card) ?_).trans (by simp)
    intro j hj
    rw [Finset.mem_filter] at hj
    rw [← hj.2]
    exact h2 j hj.1
  have hv : ∀ v, 5 * (B v).card ≤
      4 * (2 * (U.filter (fun j => z j = v)).card + ((A' v).card - 1)) :=
    fun v => arith _ _ _ (hB4 v) (hBm v)
  have hpt : ∀ v y : Fin 26, (if adjb v y = true then (1 : ℕ) else 0) ≤
      (if y ∈ B v then (1 : ℕ) else 0) + (if v ∈ B y then (1 : ℕ) else 0) := by
    intro v y
    by_cases hadj : adjb v y = true
    · obtain ⟨j, hj, h | h⟩ := h3 v y hadj
      · have hm : y ∈ B v := by
          rw [hB v]
          exact Finset.mem_biUnion.2 ⟨j, Finset.mem_filter.2 ⟨hj, h.1.symm⟩, h.2⟩
        rw [if_pos hadj, if_pos hm]
        omega
      · have hm : v ∈ B y := by
          rw [hB y]
          exact Finset.mem_biUnion.2 ⟨j, Finset.mem_filter.2 ⟨hj, h.1.symm⟩, h.2⟩
        rw [if_pos hadj, if_pos hm]
        omega
    · rw [if_neg hadj]
      exact Nat.zero_le _
  have hsumB : ∀ v : Fin 26, ∑ y : Fin 26, (if y ∈ B v then (1 : ℕ) else 0) = (B v).card := by
    intro v
    simp
  have hsumB' : ∑ v : Fin 26, ∑ y : Fin 26, (if v ∈ B y then (1 : ℕ) else 0)
      = ∑ y : Fin 26, (B y).card := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun y _ => hsumB y)
  have h104 : 104 ≤ 2 * ∑ v : Fin 26, (B v).card := by
    calc 104 = ∑ v : Fin 26, ∑ y : Fin 26, (if adjb v y = true then (1 : ℕ) else 0) :=
          adj_total.symm
      _ ≤ ∑ v : Fin 26, ∑ y : Fin 26,
            ((if y ∈ B v then (1 : ℕ) else 0) + (if v ∈ B y then (1 : ℕ) else 0)) :=
          Finset.sum_le_sum (fun v _ => Finset.sum_le_sum (fun y _ => hpt v y))
      _ = (∑ v : Fin 26, (B v).card) + ∑ y : Fin 26, (B y).card := by
          simp only [Finset.sum_add_distrib]
          rw [hsumB', Finset.sum_congr rfl (fun v _ => hsumB v)]
      _ = 2 * ∑ v : Fin 26, (B v).card := by ring
  have hU : U.card = ∑ v : Fin 26, (U.filter (fun j => z j = v)).card :=
    Finset.card_eq_sum_card_fiberwise (fun j _ => Finset.mem_univ (z j))
  have hfin : ∑ v : Fin 26, 5 * (B v).card ≤ ∑ v : Fin 26,
      4 * (2 * (U.filter (fun j => z j = v)).card + ((A' v).card - 1)) :=
    Finset.sum_le_sum (fun v _ => hv v)
  rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum, ← hU]
    at hfin
  omega

open Classical in
theorem core2 (gs : List Gate) (o : ℕ) (H : Hy gs o) : 64 ≤ gs.length := by
  have hstar : ∀ j : Fin gs.length, ∃ (z : Fin 26) (A : Finset (Fin 26)) (lw : ℕ),
      ((gs.get j).op = GateOp.and → Reach gs o (26 + (j : ℕ)) →
        (∃ s t : Fin 26, val gs (26 + (j : ℕ)) (pr s t) = true) →
        A ⊆ N z ∧ (∀ p ∈ A, val gs lw (fun v : Fin 26 => decide (v = p)) = true) ∧
        val gs lw (fun v : Fin 26 => decide (v ∉ N z)) = false ∧
        ∀ s t : Fin 26, val gs (26 + (j : ℕ)) (pr s t) = true →
          (s = z ∧ t ∈ A) ∨ (t = z ∧ s ∈ A)) := by
    intro j
    by_cases h : (gs.get j).op = GateOp.and ∧ Reach gs o (26 + (j : ℕ)) ∧
        ∃ s t : Fin 26, val gs (26 + (j : ℕ)) (pr s t) = true
    · obtain ⟨h1, h2, s, t, h3⟩ := h
      obtain ⟨z, A, lw, hh⟩ := star gs o H j j.2 h1 h2 s t h3
      exact ⟨z, A, lw, fun _ _ _ => hh⟩
    · exact ⟨0, ∅, 0, fun h1 h2 h3 => absurd ⟨h1, h2, h3⟩ h⟩
  choose z A lw hst using hstar
  have hst' : ∀ j ∈ US gs o, A j ⊆ N (z j) ∧
      (∀ p ∈ A j, val gs (lw j) (fun v : Fin 26 => decide (v = p)) = true) ∧
      val gs (lw j) (fun v : Fin 26 => decide (v ∉ N (z j))) = false ∧
      ∀ s t : Fin 26, val gs (26 + (j : ℕ)) (pr s t) = true →
        (s = z j ∧ t ∈ A j) ∨ (t = z j ∧ s ∈ A j) := by
    intro j hj
    obtain ⟨h1, h2, h3⟩ := (mem_US gs o j).1 hj
    exact hst j h1 h2 h3
  have hmax : ∀ v : Fin 26, ∃ (A' : Finset (Fin 26)) (o' : ℕ), A' ⊆ N v ∧
      (∀ p : Fin 26, p ∈ A' → val gs o' (fun i : Fin 26 => decide (i = p)) = true) ∧
      (1 ≤ A'.card → val gs o' (fun i : Fin 26 => decide (i ∉ N v)) = false) ∧
      (∀ j ∈ US gs o, z j = v → (A j).card ≤ A'.card) := by
    intro v
    by_cases hne : ((US gs o).filter (fun j => z j = v)).Nonempty
    · obtain ⟨j0, hj0, hmx⟩ := Finset.exists_max_image _ (fun j => (A j).card) hne
      rw [Finset.mem_filter] at hj0
      obtain ⟨hA1, hA2, hA3, _⟩ := hst' j0 hj0.1
      rw [hj0.2] at hA1 hA3
      exact ⟨A j0, lw j0, hA1, hA2, fun _ => hA3,
        fun j hj hz => hmx j (Finset.mem_filter.2 ⟨hj, hz⟩)⟩
    · refine ⟨∅, 0, Finset.empty_subset _, ?_, ?_, ?_⟩
      · intro p hp
        simp at hp
      · intro h
        simp at h
      · intro j hj hz
        exact absurd ⟨j, Finset.mem_filter.2 ⟨hj, hz⟩⟩ hne
  choose A' o' hA1 hA2 hA3 hA4 using hmax
  have hmc : ∑ v : Fin 26, ((A' v).card - 1) ≤ (MGS gs A').card :=
    mrg_count N A' gs o' hLN H.1 H.2.1 hA1 hA2 hA3
  have htl := tally (US gs o) z A A' (fun j hj => (hst' j hj).1)
    (fun j hj => hA4 (z j) j hj rfl) (by
      intro v y hadj
      obtain ⟨j, hj, hval⟩ := cover gs o H v y hadj
      exact ⟨j, hj, (hst' j hj).2.2.2 v y hval⟩)
  have htop := top_count gs o H.1 (US gs o) (ROS gs o)
    (fun j hj => ⟨((mem_US gs o j).1 hj).1, ((mem_US gs o j).1 hj).2.1⟩) (mem_ROS gs o)
  have hd1 : Disjoint (US gs o) (ROS gs o) := by
    rw [Finset.disjoint_left]
    intro g h1 h2
    have a1 := ((mem_US gs o g).1 h1).1
    have a2 := ((mem_ROS gs o g).1 h2).1
    rw [a1] at a2
    exact GateOp.noConfusion a2
  have hd2 : Disjoint (US gs o ∪ ROS gs o) (MGS gs A') := by
    rw [Finset.disjoint_left]
    intro g hg hm
    obtain ⟨_, v, hmj⟩ := Finset.mem_filter.1 hm
    obtain ⟨ho, _, w1, w2, hab, r, _, r', _, hv1, _⟩ := hmj
    rcases Finset.mem_union.1 hg with h | h
    · have a1 := ((mem_US gs o g).1 h).1
      rw [a1] at ho
      exact GateOp.noConfusion ho
    · have hr := ((mem_ROS gs o g).1 h).2
      have hm1 : w1 ∈ (gs.get g).inputs := by rw [hab]; simp
      exact reach_single gs o H _ hr r
        ((val_or gs _ g g.2 ho).2 ⟨w1, hm1, H.2.1 g w1 hm1, hv1⟩)
  have hcard : (US gs o ∪ ROS gs o ∪ MGS gs A').card ≤ gs.length := by
    simpa using Finset.card_le_univ (US gs o ∪ ROS gs o ∪ MGS gs A')
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1] at hcard
  omega

end PEqualNP.Outside.L_meta_18294.Flat

namespace PEqualNP.Outside.L_meta_18294.Lift

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wf_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wf (g :: gs) w = wf gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

theorem wf_append (pre post : List Gate) (w : List Bool) :
    wf (pre ++ post) w = wf post (wf pre w) := by
  simp [wf, List.foldl_append]

theorem wf_len (gs : List Gate) : ∀ w : List Bool, (wf gs w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp [wf]
  | cons g gs ih =>
    intro w
    have := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    simp only [wf, List.foldl_cons] at this ⊢
    rw [this]; simp; omega

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

theorem legal_of (C : Circuit) (hmono : Monotone2 C) :
    ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  intro g hg
  obtain ⟨h1, h2⟩ := hmono g hg
  refine ⟨?_, h2⟩
  rcases h1 with h | h
  · exact Or.inl h
  · exact Or.inr h

def sk (N i : ℕ) : ℕ := if i < N then i else i - 1

def rn (N a i : ℕ) : ℕ := if i < N then i else if i = N then a else i - 1

theorem sk_lt (N M i : ℕ) (hN0 : 0 < N) (hM : N ≤ M) (hi : i < M + 1) : sk N i < M := by
  unfold sk
  split_ifs <;> omega

theorem getD_mid (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) :
    (A ++ b :: E).getD N false = b := by
  subst hN
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right (le_refl A.length),
    Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]

theorem getD_sk (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (i : ℕ) (hi : i ≠ N) :
    (A ++ E).getD (sk N i) false = (A ++ b :: E).getD i false := by
  subst hN
  unfold sk
  by_cases h : i < A.length
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · rw [if_neg h]
    have h1 : A.length ≤ i - 1 := by omega
    have h2 : A.length ≤ i := by omega
    have h3 : i - A.length = (i - 1 - A.length) + 1 := by omega
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_right h1,
      List.getElem?_append_right h2]
    rw [h3, List.getElem?_cons_succ]

theorem getD_rn (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (a : ℕ) (ha : a < N)
    (hb : A.getD a false = b) (i : ℕ) :
    (A ++ E).getD (rn N a i) false = (A ++ b :: E).getD i false := by
  by_cases h : i = N
  · have e : rn N a N = a := by
      unfold rn
      rw [if_neg (lt_irrefl _), if_pos rfl]
    have ha' : a < A.length := by omega
    rw [h, getD_mid A E b N hN, e, ← hb]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left ha']
  · have e : rn N a i = sk N i := by
      unfold rn sk
      by_cases h' : i < N
      · rw [if_pos h', if_pos h']
      · rw [if_neg h', if_neg h, if_neg h']
    rw [e]
    exact getD_sk A E b N hN i h

theorem surg (T : Gate → Gate) (A : List Bool) (b : Bool) :
    ∀ (post : List Gate) (E : List Bool),
      (∀ h ∈ post, ∀ E' : List Bool,
        h.op.eval (h.inputs.map fun i => (A ++ b :: E').getD i false)
          = (T h).op.eval ((T h).inputs.map fun i => (A ++ E').getD i false)) →
      ∃ E2 : List Bool, wf post (A ++ b :: E) = A ++ b :: E2 ∧
        wf (post.map T) (A ++ E) = A ++ E2 := by
  intro post
  induction post with
  | nil => intro E _; exact ⟨E, rfl, rfl⟩
  | cons h post ih =>
    intro E hT
    have e := hT h (List.mem_cons.mpr (Or.inl rfl)) E
    obtain ⟨E2, h1, h2⟩ :=
      ih (E ++ [h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false)])
        (fun h' hh' E' => hT h' (List.mem_cons.mpr (Or.inr hh')) E')
    refine ⟨E2, ?_, ?_⟩
    · rw [wf_cons, List.append_assoc, List.cons_append]
      exact h1
    · rw [List.map_cons, wf_cons, ← e, List.append_assoc]
      exact h2

theorem ev (pre post : List Gate) (g : Gate) (T : Gate → Gate) (x : List Bool) (b : Bool)
    (hb : g.op.eval (g.inputs.map fun i => (wf pre x).getD i false) = b)
    (hT : ∀ h ∈ post, ∀ E' : List Bool,
        h.op.eval (h.inputs.map fun i => (wf pre x ++ b :: E').getD i false)
          = (T h).op.eval ((T h).inputs.map fun i => (wf pre x ++ E').getD i false)) :
    ∃ E2 : List Bool, wf (pre ++ g :: post) x = wf pre x ++ b :: E2 ∧
      wf (pre ++ post.map T) x = wf pre x ++ E2 := by
  obtain ⟨E2, h1, h2⟩ := surg T (wf pre x) b post [] hT
  rw [List.append_nil] at h2
  refine ⟨E2, ?_, ?_⟩
  · rw [wf_append, wf_cons, hb]
    exact h1
  · rw [wf_append]
    exact h2

def Tc (N a : ℕ) (h : Gate) : Gate := ⟨h.op, h.inputs.map (rn N a)⟩

def Tt (N : ℕ) (h : Gate) : Gate :=
  match h.op with
  | GateOp.and => ⟨GateOp.and, (h.inputs.filter (fun i => decide (i ≠ N))).map (sk N)⟩
  | _ => if N ∈ h.inputs then ⟨GateOp.and, []⟩ else ⟨h.op, h.inputs.map (sk N)⟩

def Tf (N : ℕ) (h : Gate) : Gate :=
  match h.op with
  | GateOp.or => ⟨GateOp.or, (h.inputs.filter (fun i => decide (i ≠ N))).map (sk N)⟩
  | _ => if N ∈ h.inputs then ⟨GateOp.or, []⟩ else ⟨h.op, h.inputs.map (sk N)⟩

theorem Tt_and (N : ℕ) (ins : List ℕ) : Tt N ⟨GateOp.and, ins⟩
    = ⟨GateOp.and, (ins.filter (fun i => decide (i ≠ N))).map (sk N)⟩ := rfl

theorem Tt_or (N : ℕ) (ins : List ℕ) : Tt N ⟨GateOp.or, ins⟩
    = if N ∈ ins then ⟨GateOp.and, []⟩ else ⟨GateOp.or, ins.map (sk N)⟩ := rfl

theorem Tf_or (N : ℕ) (ins : List ℕ) : Tf N ⟨GateOp.or, ins⟩
    = ⟨GateOp.or, (ins.filter (fun i => decide (i ≠ N))).map (sk N)⟩ := rfl

theorem Tf_and (N : ℕ) (ins : List ℕ) : Tf N ⟨GateOp.and, ins⟩
    = if N ∈ ins then ⟨GateOp.or, []⟩ else ⟨GateOp.and, ins.map (sk N)⟩ := rfl

theorem map_sk (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (ins : List ℕ)
    (hni : N ∉ ins) :
    (ins.map (sk N)).map (fun i => (A ++ E).getD i false)
      = ins.map (fun i => (A ++ b :: E).getD i false) := by
  rw [List.map_map]
  apply List.map_congr_left
  intro i hi
  exact getD_sk A E b N hN i (fun e => hni (by rw [← e]; exact hi))

theorem all_drop (f : ℕ → Bool) (N : ℕ) (hf : f N = true) : ∀ ins : List ℕ,
    (ins.map f).all id = ((ins.filter (fun i => decide (i ≠ N))).map f).all id := by
  intro ins
  induction ins with
  | nil => rfl
  | cons i rest ih =>
    by_cases h : i = N
    · have e : (i :: rest).filter (fun i => decide (i ≠ N))
          = rest.filter (fun i => decide (i ≠ N)) :=
        List.filter_cons_of_neg (by simp [h])
      rw [e, ← ih, List.map_cons, List.all_cons, h]
      simp [hf]
    · have e : (i :: rest).filter (fun i => decide (i ≠ N))
          = i :: rest.filter (fun i => decide (i ≠ N)) :=
        List.filter_cons_of_pos (by simpa using h)
      rw [e]
      simp only [List.map_cons, List.all_cons, ih]

theorem any_drop (f : ℕ → Bool) (N : ℕ) (hf : f N = false) : ∀ ins : List ℕ,
    (ins.map f).any id = ((ins.filter (fun i => decide (i ≠ N))).map f).any id := by
  intro ins
  induction ins with
  | nil => rfl
  | cons i rest ih =>
    by_cases h : i = N
    · have e : (i :: rest).filter (fun i => decide (i ≠ N))
          = rest.filter (fun i => decide (i ≠ N)) :=
        List.filter_cons_of_neg (by simp [h])
      rw [e, ← ih, List.map_cons, List.any_cons, h]
      simp [hf]
    · have e : (i :: rest).filter (fun i => decide (i ≠ N))
          = i :: rest.filter (fun i => decide (i ≠ N)) :=
        List.filter_cons_of_pos (by simpa using h)
      rw [e]
      simp only [List.map_cons, List.any_cons, ih]

theorem sound_c (A E : List Bool) (b : Bool) (N : ℕ) (hN : A.length = N) (a : ℕ) (ha : a < N)
    (hb : A.getD a false = b) (h : Gate) :
    h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false)
      = (Tc N a h).op.eval ((Tc N a h).inputs.map fun i => (A ++ E).getD i false) := by
  have e : (h.inputs.map (rn N a)).map (fun i => (A ++ E).getD i false)
      = h.inputs.map fun i => (A ++ b :: E).getD i false := by
    rw [List.map_map]
    apply List.map_congr_left
    intro i _
    exact getD_rn A E b N hN a ha hb i
  show h.op.eval _ = h.op.eval ((h.inputs.map (rn N a)).map fun i => (A ++ E).getD i false)
  rw [e]

theorem sound_t (A E : List Bool) (N : ℕ) (hN : A.length = N) (h : Gate)
    (hop : h.op = GateOp.and ∨ h.op = GateOp.or) :
    h.op.eval (h.inputs.map fun i => (A ++ true :: E).getD i false)
      = (Tt N h).op.eval ((Tt N h).inputs.map fun i => (A ++ E).getD i false) := by
  obtain ⟨op, ins⟩ := h
  have hf : (A ++ true :: E).getD N false = true := getD_mid A E true N hN
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tt_and]
    show (ins.map fun i => (A ++ true :: E).getD i false).all id
      = (((ins.filter (fun i => decide (i ≠ N))).map (sk N)).map
          fun i => (A ++ E).getD i false).all id
    rw [map_sk A E true N hN (ins.filter (fun i => decide (i ≠ N))) (by simp)]
    exact all_drop _ N hf ins
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tt_or]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      show (ins.map fun i => (A ++ true :: E).getD i false).any id = true
      exact List.any_eq_true.mpr ⟨_, List.mem_map.mpr ⟨N, hm, rfl⟩, hf⟩
    · rw [if_neg hm]
      show (ins.map fun i => (A ++ true :: E).getD i false).any id
        = ((ins.map (sk N)).map fun i => (A ++ E).getD i false).any id
      rw [map_sk A E true N hN ins hm]

theorem sound_f (A E : List Bool) (N : ℕ) (hN : A.length = N) (h : Gate)
    (hop : h.op = GateOp.and ∨ h.op = GateOp.or) :
    h.op.eval (h.inputs.map fun i => (A ++ false :: E).getD i false)
      = (Tf N h).op.eval ((Tf N h).inputs.map fun i => (A ++ E).getD i false) := by
  obtain ⟨op, ins⟩ := h
  have hf : (A ++ false :: E).getD N false = false := getD_mid A E false N hN
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tf_and]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      show (ins.map fun i => (A ++ false :: E).getD i false).all id = false
      cases hall : (ins.map fun i => (A ++ false :: E).getD i false).all id with
      | false => rfl
      | true =>
        have t := List.all_eq_true.mp hall _ (List.mem_map.mpr ⟨N, hm, rfl⟩)
        have t2 : (A ++ false :: E).getD N false = true := t
        rw [hf] at t2
        exact Bool.noConfusion t2
    · rw [if_neg hm]
      show (ins.map fun i => (A ++ false :: E).getD i false).all id
        = ((ins.map (sk N)).map fun i => (A ++ E).getD i false).all id
      rw [map_sk A E false N hN ins hm]
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tf_or]
    show (ins.map fun i => (A ++ false :: E).getD i false).any id
      = (((ins.filter (fun i => decide (i ≠ N))).map (sk N)).map
          fun i => (A ++ E).getD i false).any id
    rw [map_sk A E false N hN (ins.filter (fun i => decide (i ≠ N))) (by simp)]
    exact any_drop _ N hf ins

theorem Tc_legal (N a : ℕ) (h : Gate)
    (hl : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) :
    ((Tc N a h).op = GateOp.and ∨ (Tc N a h).op = GateOp.or) ∧ (Tc N a h).inputs.length ≤ 2 := by
  refine ⟨hl.1, ?_⟩
  show (h.inputs.map (rn N a)).length ≤ 2
  rw [List.length_map]
  exact hl.2

theorem Tc_rb (N a : ℕ) (ha : a < N) (h : Gate) (M : ℕ) (hM : N ≤ M)
    (hi : ∀ i ∈ h.inputs, i < M + 1) : ∀ i ∈ (Tc N a h).inputs, i < M := by
  intro i hi'
  obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
  have := hi j hj
  unfold rn
  split_ifs <;> omega

theorem Tt_legal (N : ℕ) (h : Gate)
    (hl : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) :
    ((Tt N h).op = GateOp.and ∨ (Tt N h).op = GateOp.or) ∧ (Tt N h).inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := h
  obtain ⟨hop, hlen⟩ := hl
  have hlen' : ins.length ≤ 2 := hlen
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tt_and]
    refine ⟨Or.inl rfl, ?_⟩
    show ((ins.filter (fun i => decide (i ≠ N))).map (sk N)).length ≤ 2
    rw [List.length_map]
    exact le_trans (List.length_filter_le _ _) hlen'
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tt_or]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      exact ⟨Or.inl rfl, Nat.zero_le 2⟩
    · rw [if_neg hm]
      refine ⟨Or.inr rfl, ?_⟩
      show (ins.map (sk N)).length ≤ 2
      rw [List.length_map]
      exact hlen'

theorem Tf_legal (N : ℕ) (h : Gate)
    (hl : (h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) :
    ((Tf N h).op = GateOp.and ∨ (Tf N h).op = GateOp.or) ∧ (Tf N h).inputs.length ≤ 2 := by
  obtain ⟨op, ins⟩ := h
  obtain ⟨hop, hlen⟩ := hl
  have hlen' : ins.length ≤ 2 := hlen
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tf_and]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      exact ⟨Or.inr rfl, Nat.zero_le 2⟩
    · rw [if_neg hm]
      refine ⟨Or.inl rfl, ?_⟩
      show (ins.map (sk N)).length ≤ 2
      rw [List.length_map]
      exact hlen'
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tf_or]
    refine ⟨Or.inr rfl, ?_⟩
    show ((ins.filter (fun i => decide (i ≠ N))).map (sk N)).length ≤ 2
    rw [List.length_map]
    exact le_trans (List.length_filter_le _ _) hlen'

theorem Tt_rb (N : ℕ) (hN0 : 0 < N) (h : Gate) (hop : h.op = GateOp.and ∨ h.op = GateOp.or)
    (M : ℕ) (hM : N ≤ M) (hi : ∀ i ∈ h.inputs, i < M + 1) : ∀ i ∈ (Tt N h).inputs, i < M := by
  obtain ⟨op, ins⟩ := h
  have hi2 : ∀ i ∈ ins, i < M + 1 := hi
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tt_and]
    intro i hi'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
    exact sk_lt N M j hN0 hM (hi2 j (List.mem_filter.mp hj).1)
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tt_or]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      intro i hi'
      exact absurd hi' List.not_mem_nil
    · rw [if_neg hm]
      intro i hi'
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
      exact sk_lt N M j hN0 hM (hi2 j hj)

theorem Tf_rb (N : ℕ) (hN0 : 0 < N) (h : Gate) (hop : h.op = GateOp.and ∨ h.op = GateOp.or)
    (M : ℕ) (hM : N ≤ M) (hi : ∀ i ∈ h.inputs, i < M + 1) : ∀ i ∈ (Tf N h).inputs, i < M := by
  obtain ⟨op, ins⟩ := h
  have hi2 : ∀ i ∈ ins, i < M + 1 := hi
  rcases hop with hop | hop
  · have hop' : op = GateOp.and := hop
    subst hop'
    rw [Tf_and]
    by_cases hm : N ∈ ins
    · rw [if_pos hm]
      intro i hi'
      exact absurd hi' List.not_mem_nil
    · rw [if_neg hm]
      intro i hi'
      obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
      exact sk_lt N M j hN0 hM (hi2 j hj)
  · have hop' : op = GateOp.or := hop
    subst hop'
    rw [Tf_or]
    intro i hi'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi'
    exact sk_lt N M j hN0 hM (hi2 j (List.mem_filter.mp hj).1)

theorem assemble (C : Circuit) (pre post : List Gate) (g : Gate)
    (hC : C.gates = pre ++ g :: post) (T : Gate → Gate) (o' : ℕ)
    (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (hTm : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ((T h).op = GateOp.and ∨ (T h).op = GateOp.or) ∧ (T h).inputs.length ≤ 2)
    (hTr : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ∀ M : ℕ, 26 + pre.length ≤ M → (∀ i ∈ h.inputs, i < M + 1) → ∀ i ∈ (T h).inputs, i < M)
    (hev : ∀ x : List Bool, x.length = 26 →
      Circuit.eval ⟨pre ++ post.map T, o'⟩ x = C.eval x) :
    ∃ C' : Circuit, Monotone2 C' ∧ ReadsBack 26 C' ∧
      (∀ x : List Bool, x.length = 26 → C'.eval x = C.eval x) ∧ C'.size < C.size := by
  have legal := legal_of C hmono
  refine ⟨⟨pre ++ post.map T, o'⟩, ?_, ?_, hev, ?_⟩
  · intro g' hg'
    have hg2 : g' ∈ pre ∨ g' ∈ post.map T := List.mem_append.mp hg'
    rcases hg2 with hp | hp
    · exact hmono g' (by rw [hC]; exact List.mem_append.mpr (Or.inl hp))
    · obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hp
      have hl := hTm h (legal h (by
        rw [hC]; exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hh)))))
      refine ⟨?_, hl.2⟩
      rcases hl.1 with e | e
      · exact Or.inl e
      · exact Or.inr e
  · intro j hj i hi
    have hj' : j < pre.length + post.length := by simpa using hj
    by_cases hjp : j < pre.length
    · have e : gateAt ⟨pre ++ post.map T, o'⟩ j = gateAt C j := by
        simp only [gateAt, hC, List.getD_eq_getElem?_getD, List.getElem?_append_left hjp]
      rw [e] at hi
      exact hrb j (by rw [hC]; simp only [List.length_append, List.length_cons]; omega) i hi
    · have hjk : j - pre.length < post.length := by omega
      have e1 : gateAt ⟨pre ++ post.map T, o'⟩ j = T (post[j - pre.length]) := by
        simp [gateAt, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (Nat.le_of_not_lt hjp), hjk]
      have e2 : gateAt C (j + 1) = post[j - pre.length] := by
        have h3 : j + 1 - pre.length = (j - pre.length) + 1 := by omega
        simp [gateAt, hC, List.getD_eq_getElem?_getD,
          List.getElem?_append_right (show pre.length ≤ j + 1 by omega), h3, hjk]
      rw [e1] at hi
      have hmem : post[j - pre.length] ∈ C.gates := by
        rw [hC]
        exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr (List.getElem_mem hjk))))
      have hold : ∀ i ∈ (post[j - pre.length]).inputs, i < (26 + j) + 1 := by
        intro i hi2
        have := hrb (j + 1) (by rw [hC]; simp only [List.length_append, List.length_cons]; omega)
          i (by rw [e2]; exact hi2)
        omega
      exact hTr _ (legal _ hmem) (26 + j) (by omega) hold i hi
  · show (pre ++ post.map T).length < C.gates.length
    rw [hC]
    simp

theorem copy_case (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (pre post : List Gate) (g : Gate) (hC : C.gates = pre ++ g :: post) (a : ℕ)
    (ha : a < 26 + pre.length)
    (hb : ∀ A : List Bool, g.op.eval (g.inputs.map fun i => A.getD i false) = A.getD a false) :
    ∃ C' : Circuit, Monotone2 C' ∧ ReadsBack 26 C' ∧
      (∀ x : List Bool, x.length = 26 → C'.eval x = C.eval x) ∧ C'.size < C.size := by
  apply assemble C pre post g hC (Tc (26 + pre.length) a) (rn (26 + pre.length) a C.output)
    hmono hrb
  · intro h hl
    exact Tc_legal _ _ h hl
  · intro h _ M hM hi
    exact Tc_rb _ _ ha h M hM hi
  · intro x hx
    have hlen : (wf pre x).length = 26 + pre.length := by rw [wf_len, hx]
    obtain ⟨E2, h1, h2⟩ := ev pre post g (Tc (26 + pre.length) a) x _ (hb (wf pre x))
      (fun h _ E' => sound_c (wf pre x) E' _ (26 + pre.length) hlen a ha rfl h)
    show (wf (pre ++ post.map (Tc (26 + pre.length) a)) x).getD
        (rn (26 + pre.length) a C.output) false = (wf C.gates x).getD C.output false
    rw [h2, hC, h1]
    exact getD_rn (wf pre x) E2 _ (26 + pre.length) hlen a ha rfl C.output

theorem const_case (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (pre post : List Gate) (g : Gate) (hC : C.gates = pre ++ g :: post) (T : Gate → Gate)
    (b : Bool)
    (hb : ∀ A : List Bool, g.op.eval (g.inputs.map fun i => A.getD i false) = b)
    (hTm : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ((T h).op = GateOp.and ∨ (T h).op = GateOp.or) ∧ (T h).inputs.length ≤ 2)
    (hTr : ∀ h : Gate, ((h.op = GateOp.and ∨ h.op = GateOp.or) ∧ h.inputs.length ≤ 2) →
      ∀ M : ℕ, 26 + pre.length ≤ M → (∀ i ∈ h.inputs, i < M + 1) → ∀ i ∈ (T h).inputs, i < M)
    (hs : ∀ h : Gate, (h.op = GateOp.and ∨ h.op = GateOp.or) → ∀ (A E : List Bool),
      A.length = 26 + pre.length →
      h.op.eval (h.inputs.map fun i => (A ++ b :: E).getD i false)
        = (T h).op.eval ((T h).inputs.map fun i => (A ++ E).getD i false))
    (hne : ∃ x y : List Bool, x.length = 26 ∧ y.length = 26 ∧ C.eval x = true ∧
      C.eval y = false) :
    ∃ C' : Circuit, Monotone2 C' ∧ ReadsBack 26 C' ∧
      (∀ x : List Bool, x.length = 26 → C'.eval x = C.eval x) ∧ C'.size < C.size := by
  have legal := legal_of C hmono
  have key : ∀ x : List Bool, x.length = 26 → ∃ E2 : List Bool,
      wf C.gates x = wf pre x ++ b :: E2 ∧ wf (pre ++ post.map T) x = wf pre x ++ E2 := by
    intro x hx
    have hlen : (wf pre x).length = 26 + pre.length := by rw [wf_len, hx]
    have hpost : ∀ h ∈ post, h.op = GateOp.and ∨ h.op = GateOp.or := by
      intro h hh
      exact (legal h (by
        rw [hC]; exact List.mem_append.mpr (Or.inr (List.mem_cons.mpr (Or.inr hh))))).1
    rw [hC]
    exact ev pre post g T x b (hb (wf pre x))
      (fun h hh E' => hs h (hpost h hh) (wf pre x) E' hlen)
  have hout : C.output ≠ 26 + pre.length := by
    intro ho
    obtain ⟨x, y, hx, hy, ex, ey⟩ := hne
    obtain ⟨E2, h1, _⟩ := key x hx
    obtain ⟨E3, h3, _⟩ := key y hy
    have vx : C.eval x = b := by
      show (wf C.gates x).getD C.output false = b
      rw [h1, ho]
      exact getD_mid _ _ _ _ (by rw [wf_len, hx])
    have vy : C.eval y = b := by
      show (wf C.gates y).getD C.output false = b
      rw [h3, ho]
      exact getD_mid _ _ _ _ (by rw [wf_len, hy])
    rw [vx] at ex
    rw [vy, ex] at ey
    exact Bool.noConfusion ey
  apply assemble C pre post g hC T (sk (26 + pre.length) C.output) hmono hrb hTm hTr
  intro x hx
  obtain ⟨E2, h1, h2⟩ := key x hx
  show (wf (pre ++ post.map T) x).getD (sk (26 + pre.length) C.output) false
    = (wf C.gates x).getD C.output false
  rw [h2, h1]
  exact getD_sk _ _ _ _ (by rw [wf_len, hx]) _ hout

theorem copy_val (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (v : Bool) :
    op.eval [v] = v ∧ op.eval [v, v] = v := by
  rcases hop with rfl | rfl <;> cases v <;> exact ⟨rfl, rfl⟩

theorem len26 (f g : Fin 13 → Bool) : (List.ofFn f ++ List.ofFn g).length = 26 := by
  simp

theorem short_case (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (hne : ∃ x y : List Bool, x.length = 26 ∧ y.length = 26 ∧ C.eval x = true ∧
      C.eval y = false)
    (hdeg : ∃ g ∈ C.gates, g.inputs.length < 2 ∨ g.inputs.getD 0 0 = g.inputs.getD 1 0) :
    ∃ C' : Circuit, Monotone2 C' ∧ ReadsBack 26 C' ∧
      (∀ x : List Bool, x.length = 26 → C'.eval x = C.eval x) ∧ C'.size < C.size := by
    obtain ⟨g, hg, hd⟩ := hdeg
    obtain ⟨k, hk, hgk⟩ := List.getElem_of_mem hg
    obtain ⟨pre, post, gj, hC, hpl, hgj⟩ := split_gates C.gates k hk
    have hgg : gj = g := by rw [← hgj, hgk]
    rw [hgg] at hC
    have hl := legal_of C hmono g hg
    have hin : ∀ i ∈ g.inputs, i < 26 + pre.length := by
      intro i hi
      have := hrb k hk i (by rw [gateAt_eq C k hk, hgk]; exact hi)
      omega
    obtain ⟨op, ins⟩ := g
    have hop : op = GateOp.and ∨ op = GateOp.or := hl.1
    have hlen : ins.length ≤ 2 := hl.2
    have hd' : ins.length < 2 ∨ ins.getD 0 0 = ins.getD 1 0 := hd
    have hin' : ∀ i ∈ ins, i < 26 + pre.length := hin
    rcases ins with _ | ⟨a, _ | ⟨c, _ | ⟨d, r⟩⟩⟩
    · rcases hop with hop | hop
      · subst hop
        exact const_case C hmono hrb pre post _ hC (Tt (26 + pre.length)) true (fun _ => rfl)
          (fun h hl => Tt_legal _ h hl)
          (fun h hl M hM hi => Tt_rb _ (by omega) h hl.1 M hM hi)
          (fun h hop A E hA => sound_t A E _ hA h hop) hne
      · subst hop
        exact const_case C hmono hrb pre post _ hC (Tf (26 + pre.length)) false (fun _ => rfl)
          (fun h hl => Tf_legal _ h hl)
          (fun h hl M hM hi => Tf_rb _ (by omega) h hl.1 M hM hi)
          (fun h hop A E hA => sound_f A E _ hA h hop) hne
    · exact copy_case C hmono hrb pre post _ hC a (hin' a (by simp))
        (fun A => (copy_val op hop _).1)
    · have hac : a = c := by simpa using hd'
      subst hac
      exact copy_case C hmono hrb pre post _ hC a (hin' a (by simp))
        (fun A => (copy_val op hop _).2)
    · have h3 : (a :: c :: d :: r).length ≤ 2 := hlen
      simp only [List.length_cons] at h3
      omega

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepW]
    omega

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma foldl_char (gs : List Gate) (w : List Bool) :
    ∀ j, j < gs.length → (gs.foldl stepW w).getD (w.length + j) false =
      (gs.getD j ⟨GateOp.or, []⟩).op.eval ((gs.getD j ⟨GateOp.or, []⟩).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepW w).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen := foldl_len gs w
    simp only [List.length_append, List.length_singleton] at hj
    have key : ∀ i, i < w.length + gs.length →
        (stepW (gs.foldl stepW w) g).getD i false = (gs.foldl stepW w).getD i false := by
      intro i hi
      simp only [stepW, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_or_ge j gs.length with h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [e1, key _ (by omega), ih j h]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i (by omega)]
      · rfl
    · have hj' : j = gs.length := by omega
      subst hj'
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      have e2 : (stepW (gs.foldl stepW w) g).getD (w.length + gs.length) false =
          g.op.eval (g.inputs.map fun i => (gs.foldl stepW w).getD i false) := by
        simp only [stepW, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with hi
      · rw [key i hi]
      · simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by omega)]
        rfl

def wv (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl stepW x := rfl

lemma wv_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    wv n C x w = x ⟨w, hw⟩ := by
  unfold wv
  rw [wires_eq, foldl_getD_lt _ _ _ (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

def AOB (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma wv_rec (n : ℕ) (C : Circuit) (x : Fin n → Bool) (hC : AOB n C) (j : ℕ)
    (hj : j < C.gates.length) :
    wv n C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map (wv n C x)) := by
  have h := foldl_char C.gates (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold wv gateAt
  rw [wires_eq, h]
  congr 1
  apply List.map_congr_left
  intro i hi
  rw [if_pos ((hC j hj).2 i hi)]

lemma cones_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

lemma cones_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (coneStep n) []).getD j [] ↔
      j < gs.length ∧ ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
        (i = w - n ∨ i ∈ (gs.foldl (coneStep n) []).getD (w - n) []) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (coneStep n) []).length = gs.length := by
      rw [cones_len]; simp
    have key : ∀ k, k < gs.length →
        (coneStep n (gs.foldl (coneStep n) []) g).getD k [] =
          (gs.foldl (coneStep n) []).getD k [] := by
      intro k hk
      simp only [coneStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨by simp; omega, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        refine ⟨h, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)] at h3
        exact h3
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      have e2 : (coneStep n (gs.foldl (coneStep n) []) g).getD gs.length [] =
          (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
            (fun w => (w - n) :: (gs.foldl (coneStep n) []).getD (w - n) []) := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_right (by omega)]
        simp [hlen]
      rw [e2, e1]
      simp only [List.mem_flatMap, List.mem_filter, List.mem_cons, decide_eq_true_eq]
      constructor
      · rintro ⟨w, ⟨hw, h1, h2⟩, h3⟩
        refine ⟨by simp, w, hw, h1, h2, ?_⟩
        rw [key (w - n) (by omega)]
        exact h3
      · rintro ⟨_, w, hw, h1, h2, h3⟩
        rw [key (w - n) (by omega)] at h3
        exact ⟨w, ⟨hw, h1, h2⟩, h3⟩
    · have e0 : (coneStep n (gs.foldl (coneStep n) []) g).getD j [] = [] := by
        simp only [coneStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma inCone_iff (n : ℕ) (C : Circuit) (i j : ℕ) :
    InCone n C i j ↔ j < C.gates.length ∧ ∃ k, k < j ∧ n + k ∈ (gateAt C j).inputs ∧
      (i = k ∨ InCone n C i k) := by
  have h := cones_char n C.gates i j
  unfold InCone cones gateAt
  rw [h]
  constructor
  · rintro ⟨h0, w, hw, h1, h2, h3⟩
    refine ⟨h0, w - n, by omega, ?_, h3⟩
    have : n + (w - n) = w := by omega
    rw [this]
    exact hw
  · rintro ⟨h0, k, hk, hw, h3⟩
    refine ⟨h0, n + k, hw, by omega, by omega, ?_⟩
    have : n + k - n = k := by omega
    rw [this]
    exact h3

lemma inCone_lt (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → i < j ∧ j < C.gates.length := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k, hk, _, h3 | h3⟩ := h
    · exact ⟨by omega, h0⟩
    · have := (ih k hk h3).1
      exact ⟨by omega, h0⟩

lemma inCone_reader (n : ℕ) (C : Circuit) (i : ℕ) :
    ∀ j, InCone n C i j → ∃ r, r < C.gates.length ∧ i < r ∧ n + i ∈ (gateAt C r).inputs ∧
      (r = j ∨ InCone n C r j) := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    have h' := h
    rw [inCone_iff] at h'
    obtain ⟨h0, k, hk, hin, h3 | h3⟩ := h'
    · subst h3
      exact ⟨j, h0, hk, hin, Or.inl rfl⟩
    · obtain ⟨r, hr, hir, hrin, h4⟩ := ih k hk h3
      refine ⟨r, hr, hir, hrin, Or.inr ?_⟩
      rw [inCone_iff]
      refine ⟨h0, k, hk, hin, ?_⟩
      rcases h4 with h4 | h4
      · exact Or.inl h4
      · exact Or.inr h4

def tau (n r b w : ℕ) : ℕ := if w < n + r then w else if w = n + r then b else w - 1

def rho (r k : ℕ) : ℕ := if k < r then k else k + 1

def IsRedirect (n : ℕ) (C C' : Circuit) (r b : ℕ) : Prop :=
  ∀ k, k < C.gates.length - 1 →
    gateAt C' k = ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩

lemma transfer (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool) (R : Bool → Bool → Prop)
    (hRrefl : ∀ a, R a a) (hRtrans : ∀ a b c, R a b → R b c → R a c)
    (hRand : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.and.eval (l.map f)) (GateOp.and.eval (l.map f')))
    (hRor : ∀ (l : List ℕ) (f f' : ℕ → Bool), (∀ w ∈ l, R (f w) (f' w)) →
      R (GateOp.or.eval (l.map f)) (GateOp.or.eval (l.map f')))
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → R (wv n C x (n + r)) (wv n C x b)) →
      R (wv n C x w) (wv n C' x (tau n r b w)) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw hR0
    by_cases h1 : w < n
    · have ht : tau n r b w = w := by unfold tau; rw [if_pos (by omega)]
      rw [ht, wv_input n C x w h1, wv_input n C' x w h1]
      exact hRrefl _
    · obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
      by_cases hk : k = r
      · subst hk
        have ht : tau n k b (n + k) = b := by unfold tau; simp
        have htb : tau n k b b = b := by unfold tau; rw [if_pos hb]
        have h2 := ih b (by omega) (by omega) (fun h => absurd h (by omega))
        rw [htb] at h2
        rw [ht]
        exact hRtrans _ _ _ (hR0 le_rfl) h2
      · have hkm : k < C.gates.length := by omega
        obtain ⟨k', hk'1, hk'2, hk'3⟩ : ∃ k', tau n r b (n + k) = n + k' ∧ rho r k' = k ∧
            k' < C.gates.length - 1 := by
          by_cases hkr : k < r
          · refine ⟨k, ?_, ?_, by omega⟩
            · unfold tau; rw [if_pos (by omega)]
            · unfold rho; rw [if_pos hkr]
          · refine ⟨k - 1, ?_, ?_, by omega⟩
            · unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
            · unfold rho; rw [if_neg (by omega)]; omega
        have hg := hred k' hk'3
        rw [hk'2] at hg
        rw [hk'1, wv_rec n C x hC k hkm, wv_rec n C' x hC' k' (by omega), hg]
        simp only [List.map_map]
        have hin : ∀ w ∈ (gateAt C k).inputs,
            R (wv n C x w) ((wv n C' x ∘ tau n r b) w) := by
          intro w hw'
          have hlt := (hC k hkm).2 w hw'
          exact ih w hlt (by omega) (fun h => hR0 (by omega))
        rcases (hC k hkm).1 with hop | hop
        · rw [hop]; exact hRand _ _ _ hin
        · rw [hop]; exact hRor _ _ _ hin

lemma transfer_eq (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length → (n + r ≤ w → wv n C x (n + r) = wv n C x b) →
      wv n C x w = wv n C' x (tau n r b w) := by
  refine transfer n C C' r b x (fun a b => a = b) (fun _ => rfl) (fun _ _ _ h1 h2 => h1.trans h2)
    ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h
    rw [List.map_congr_left h]
  · intro l f f' h
    rw [List.map_congr_left h]

lemma transfer_le (n : ℕ) (C C' : Circuit) (r b : ℕ) (x : Fin n → Bool)
    (hC : AOB n C) (hC' : AOB n C') (hr : r < C.gates.length) (hb : b < n + r)
    (hlen : C.gates.length - 1 ≤ C'.gates.length)
    (hred : IsRedirect n C C' r b) :
    ∀ w, w < n + C.gates.length →
      (n + r ≤ w → (wv n C x (n + r) = true → wv n C x b = true)) →
      (wv n C x w = true → wv n C' x (tau n r b w) = true) := by
  refine transfer n C C' r b x (fun a b => a = true → b = true) (fun _ h => h)
    (fun _ _ _ h1 h2 h => h2 (h1 h)) ?_ ?_ hC hC' hr hb hlen hred
  · intro l f f' h hall
    simp only [GateOp.eval] at hall ⊢
    rw [List.all_eq_true] at hall ⊢
    intro v hv
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact h w hw (hall (f w) (List.mem_map.mpr ⟨w, hw, rfl⟩))
  · intro l f f' h hany
    simp only [GateOp.eval] at hany ⊢
    rw [List.any_eq_true] at hany ⊢
    obtain ⟨v, hv, hv2⟩ := hany
    rw [List.mem_map] at hv
    obtain ⟨w, hw, rfl⟩ := hv
    exact ⟨f' w, List.mem_map.mpr ⟨w, hw, rfl⟩, h w hw hv2⟩

def gfun (n : ℕ) (C : Circuit) (r b : ℕ) (top : Gate) (k : ℕ) : Gate :=
  if k < C.gates.length - 1 then
    ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ else top

def V1 (n : ℕ) (C : Circuit) (r b : ℕ) : Circuit :=
  ⟨(List.range (C.gates.length - 1)).map (gfun n C r b ⟨GateOp.or, []⟩), tau n r b C.output⟩

def V2 (n : ℕ) (C : Circuit) (r b i : ℕ) : Circuit :=
  ⟨(List.range C.gates.length).map (gfun n C r b ⟨GateOp.or, [tau n r b C.output, n + i]⟩),
    n + C.gates.length - 1⟩

lemma gateAt_range (m : ℕ) (g : ℕ → Gate) (out k : ℕ) (hk : k < m) :
    gateAt ⟨(List.range m).map g, out⟩ k = g k := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma V1_len (n : ℕ) (C : Circuit) (r b : ℕ) :
    (V1 n C r b).gates.length = C.gates.length - 1 := by simp [V1]

lemma V2_len (n : ℕ) (C : Circuit) (r b i : ℕ) :
    (V2 n C r b i).gates.length = C.gates.length := by simp [V2]

lemma V1_gate (n : ℕ) (C : Circuit) (r b k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V1 n C r b) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V1
  rw [gateAt_range _ _ _ _ hk]
  unfold gfun
  rw [if_pos hk]

lemma V2_gate (n : ℕ) (C : Circuit) (r b i k : ℕ) (hk : k < C.gates.length - 1) :
    gateAt (V2 n C r b i) k =
      ⟨(gateAt C (rho r k)).op, (gateAt C (rho r k)).inputs.map (tau n r b)⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_pos hk]

lemma V2_top (n : ℕ) (C : Circuit) (r b i : ℕ) (hm : 0 < C.gates.length) :
    gateAt (V2 n C r b i) (C.gates.length - 1) =
      ⟨GateOp.or, [tau n r b C.output, n + i]⟩ := by
  unfold V2
  rw [gateAt_range _ _ _ _ (by omega)]
  unfold gfun
  rw [if_neg (by omega)]

def AO2 (n : ℕ) (C : Circuit) : Prop :=
  ∀ j, j < C.gates.length →
    ((gateAt C j).op = GateOp.and ∨ (gateAt C j).op = GateOp.or) ∧
      (∃ a b, (gateAt C j).inputs = [a, b]) ∧ ∀ i ∈ (gateAt C j).inputs, i < n + j

lemma aob {n : ℕ} {C : Circuit} (h : AO2 n C) : AOB n C :=
  fun j hj => ⟨(h j hj).1, (h j hj).2.2⟩

lemma rho_lt (r k m : ℕ) (hr : r < m) (hk : k < m - 1) : rho r k < m := by
  unfold rho; split_ifs <;> omega

lemma tau_lt (n r b w k : ℕ) (hb : b < n + r) (hw : w < n + rho r k) :
    tau n r b w < n + k := by
  unfold tau; unfold rho at hw; split_ifs at hw ⊢ <;> omega

lemma tau_low (n r b w : ℕ) (hw : w < n + r) : tau n r b w = w := by
  unfold tau; rw [if_pos hw]

lemma tau_rho (n r b k : ℕ) : tau n r b (n + rho r k) = n + k := by
  unfold tau rho; split_ifs <;> omega

lemma eval_or_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.or.eval ([a, b].map f) = (f a || f b) := by simp [GateOp.eval]

lemma eval_and_pair (f : ℕ → Bool) (a b : ℕ) :
    GateOp.and.eval ([a, b].map f) = (f a && f b) := by simp [GateOp.eval]

lemma V1_AO2 (n : ℕ) (C : Circuit) (r b : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) : AO2 n (V1 n C r b) := by
  intro k hk
  rw [V1_len] at hk
  rw [V1_gate n C r b k hk]
  obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk)
  refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
  intro w hw
  simp only [List.mem_map] at hw
  obtain ⟨w0, hw0, rfl⟩ := hw
  exact tau_lt n r b w0 k hb (h3 w0 hw0)

lemma V2_AO2 (n : ℕ) (C : Circuit) (r b i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hb : b < n + r) (hi : i < r) (hout : C.output < n + C.gates.length) :
    AO2 n (V2 n C r b i) := by
  intro k hk
  rw [V2_len] at hk
  by_cases hk1 : k < C.gates.length - 1
  · rw [V2_gate n C r b i k hk1]
    obtain ⟨h1, ⟨a, c, h2⟩, h3⟩ := hC (rho r k) (rho_lt r k _ hr hk1)
    refine ⟨h1, ⟨tau n r b a, tau n r b c, by simp [h2]⟩, ?_⟩
    intro w hw
    simp only [List.mem_map] at hw
    obtain ⟨w0, hw0, rfl⟩ := hw
    exact tau_lt n r b w0 k hb (h3 w0 hw0)
  · have hk2 : k = C.gates.length - 1 := by omega
    subst hk2
    rw [V2_top n C r b i (by omega)]
    refine ⟨Or.inr rfl, ⟨_, _, rfl⟩, ?_⟩
    intro w hw
    have hw' : w = tau n r b C.output ∨ w = n + i := by simpa using hw
    rcases hw' with rfl | rfl
    · unfold tau; split_ifs <;> omega
    · omega

lemma V1_red (n : ℕ) (C : Circuit) (r b : ℕ) : IsRedirect n C (V1 n C r b) r b :=
  fun k hk => V1_gate n C r b k hk

lemma V2_red (n : ℕ) (C : Circuit) (r b i : ℕ) : IsRedirect n C (V2 n C r b i) r b :=
  fun k hk => V2_gate n C r b i k hk

lemma V1_fun (n : ℕ) (C : Circuit) (r b : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hout : C.output < n + C.gates.length)
    (h1 : wv n C x b = true → wv n C x C.output = true)
    (h2 : wv n C x b = false → wv n C x (n + r) = false) :
    wv n (V1 n C r b) x (V1 n C r b).output = wv n C x C.output := by
  have hC' := V1_AO2 n C r b hC hr hb
  have hlen : C.gates.length - 1 ≤ (V1 n C r b).gates.length := by rw [V1_len]
  show wv n (V1 n C r b) x (tau n r b C.output) = wv n C x C.output
  cases hbv : wv n C x b with
  | true =>
    rw [h1 hbv]
    exact transfer_le n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ _ => hbv) (h1 hbv)
  | false =>
    exact (transfer_eq n C _ r b x (aob hC) (aob hC') hr hb hlen (V1_red n C r b) C.output hout
      (fun _ => by rw [h2 hbv, hbv])).symm

lemma V2_low (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) :
    ∀ w, w < n + r → wv n (V2 n C r b i) x w = wv n C x w := by
  intro w hw
  have h := transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w (by omega) (fun h => absurd h (by omega))
  rw [tau_low n r b w hw] at h
  exact h.symm

lemma V2_same (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length) (h0 : wv n C x (n + r) = wv n C x b) :
    ∀ w, w < n + C.gates.length → wv n (V2 n C r b i) x (tau n r b w) = wv n C x w := by
  intro w hw
  exact (transfer_eq n C _ r b x (aob hC) (aob (V2_AO2 n C r b i hC hr hb hi hout)) hr hb
    (by rw [V2_len]; omega) (V2_red n C r b i) w hw (fun _ => h0)).symm

lemma V2_out (n : ℕ) (C : Circuit) (r b i : ℕ) (x : Fin n → Bool) (hC : AO2 n C)
    (hr : r < C.gates.length) (hb : b < n + r) (hi : i < r)
    (hout : C.output < n + C.gates.length)
    (hbel : wv n C x (n + i) = true → wv n C x C.output = true)
    (h0 : wv n C x (n + i) = false → wv n C x (n + r) = wv n C x b) :
    wv n (V2 n C r b i) x (V2 n C r b i).output = wv n C x C.output := by
  have hC' := V2_AO2 n C r b i hC hr hb hi hout
  have hm : 0 < C.gates.length := by omega
  have e : (V2 n C r b i).output = n + (C.gates.length - 1) := by
    show n + C.gates.length - 1 = _
    omega
  rw [e, wv_rec n _ x (aob hC') (C.gates.length - 1) (by rw [V2_len]; omega),
    V2_top n C r b i hm]
  have hi' := V2_low n C r b i x hC hr hb hi hout (n + i) (by omega)
  dsimp only
  rw [eval_or_pair, hi']
  cases hv : wv n C x (n + i) with
  | true => rw [hbel hv]; simp
  | false =>
    rw [V2_same n C r b i x hC hr hb hi hout (h0 hv) C.output hout]; simp

lemma V1_fun_top (n : ℕ) (D : Circuit) (r c i y : ℕ) (x : Fin n → Bool) (hD : AO2 n D)
    (hr : r < D.gates.length - 1) (hc : c < n + r) (hi : i < r)
    (hout : D.output = n + (D.gates.length - 1))
    (htop : gateAt D (D.gates.length - 1) = ⟨GateOp.or, [y, n + i]⟩)
    (h0 : wv n D x (n + i) = false → wv n D x (n + r) = wv n D x c) :
    wv n (V1 n D r c) x (V1 n D r c).output = wv n D x D.output := by
  have hr' : r < D.gates.length := by omega
  have hE := V1_AO2 n D r c hD hr' hc
  have hlen : D.gates.length - 1 ≤ (V1 n D r c).gates.length := by rw [V1_len]
  have hred := V1_red n D r c
  show wv n (V1 n D r c) x (tau n r c D.output) = wv n D x D.output
  cases hv : wv n D x (n + i) with
  | false =>
    exact (transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred D.output (by omega)
      (fun _ => h0 hv)).symm
  | true =>
    have e1 : wv n D x D.output = true := by
      rw [hout, wv_rec n D x (aob hD) _ (by omega), htop]
      dsimp only
      rw [eval_or_pair, hv]; simp
    have e2 : tau n r c D.output = n + (D.gates.length - 2) := by
      rw [hout]; unfold tau; rw [if_neg (by omega), if_neg (by omega)]; omega
    have e3 : gateAt (V1 n D r c) (D.gates.length - 2) =
        ⟨GateOp.or, [tau n r c y, n + i]⟩ := by
      rw [V1_gate n D r c _ (by omega)]
      have hrho : rho r (D.gates.length - 2) = D.gates.length - 1 := by
        unfold rho; rw [if_neg (by omega)]; omega
      rw [hrho, htop]
      simp [tau_low n r c (n + i) (by omega)]
    have e4 : wv n (V1 n D r c) x (n + i) = true := by
      have h := transfer_eq n D _ r c x (aob hD) (aob hE) hr' hc hlen hred (n + i) (by omega)
        (fun h => absurd h (by omega))
      rw [tau_low n r c (n + i) (by omega)] at h
      rw [← h, hv]
    rw [e1, e2, wv_rec n _ x (aob hE) _ (by rw [V1_len]; omega), e3]
    dsimp only
    rw [eval_or_pair, e4]; simp

lemma inCone_trans (n : ℕ) (C : Circuit) (a k : ℕ) (hak : InCone n C a k) :
    ∀ j, InCone n C k j → InCone n C a j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro h
    rw [inCone_iff] at h
    obtain ⟨h0, k2, hk2, hin, h3 | h3⟩ := h
    · subst h3
      rw [inCone_iff]
      exact ⟨h0, k, hk2, hin, Or.inr hak⟩
    · rw [inCone_iff]
      exact ⟨h0, k2, hk2, hin, Or.inr (ih k2 hk2 h3)⟩

lemma V2_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hC : AO2 n C) (hr : r < C.gates.length)
    (hc : c < n + r) (hcin : c ∈ (gateAt C r).inputs) (a' : ℕ) :
    ∀ b', b' < C.gates.length - 1 → InCone n (V2 n C r c i) a' b' →
      InCone n C (rho r a') (rho r b') := by
  intro b'
  induction b' using Nat.strong_induction_on with
  | _ b' ih =>
    intro hb' h
    rw [inCone_iff] at h
    obtain ⟨_, k', hk', hin, h3⟩ := h
    rw [V2_gate n C r c i b' hb'] at hin
    simp only [List.mem_map] at hin
    obtain ⟨w, hw, hwk⟩ := hin
    have hbm : rho r b' < C.gates.length := rho_lt r b' _ hr hb'
    have hwlt := (hC (rho r b') hbm).2.2 w hw
    have hrb : rho r b' ≤ b' + 1 := by unfold rho; split_ifs <;> omega
    have hrb2 : b' < r → rho r b' = b' := by intro h; unfold rho; rw [if_pos h]
    have hstep : InCone n C (rho r k') (rho r b') := by
      unfold tau at hwk
      by_cases h1 : w < n + r
      · rw [if_pos h1] at hwk
        have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
        rw [e, inCone_iff]
        refine ⟨hbm, k', by omega, ?_, Or.inl rfl⟩
        rw [← hwk]; exact hw
      · rw [if_neg h1] at hwk
        by_cases h2 : w = n + r
        · rw [if_pos h2] at hwk
          have e : rho r k' = k' := by unfold rho; rw [if_pos (by omega)]
          rw [e]
          have s1 : InCone n C k' r := by
            rw [inCone_iff]
            refine ⟨hr, k', by omega, ?_, Or.inl rfl⟩
            rw [← hwk]; exact hcin
          have s2 : InCone n C r (rho r b') := by
            rw [inCone_iff]
            refine ⟨hbm, r, by omega, ?_, Or.inl rfl⟩
            rw [← h2]; exact hw
          exact inCone_trans n C k' r s1 _ s2
        · rw [if_neg h2] at hwk
          have e : rho r k' = k' + 1 := by unfold rho; rw [if_neg (by omega)]
          rw [e, inCone_iff]
          refine ⟨hbm, k' + 1, by omega, ?_, Or.inl rfl⟩
          have e2 : n + (k' + 1) = w := by omega
          rw [e2]; exact hw
    rcases h3 with h3 | h3
    · rw [h3]; exact hstep
    · exact inCone_trans n C _ _ (ih k' hk' (by omega) h3) _ hstep

lemma V2_no_reader (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ k', k' < C.gates.length - 1 → n + i ∉ (gateAt (V2 n C r c i) k').inputs := by
  intro k' hk' hin
  rw [V2_gate n C r c i k' hk'] at hin
  simp only [List.mem_map] at hin
  obtain ⟨w, hw, hwk⟩ := hin
  have hbm : rho r k' < C.gates.length := rho_lt r k' _ hr hk'
  have hne : rho r k' ≠ r := by unfold rho; split_ifs <;> omega
  unfold tau at hwk
  by_cases h1 : w < n + r
  · rw [if_pos h1] at hwk
    rw [hwk] at hw
    exact hne (huniq _ hbm hw)
  · rw [if_neg h1] at hwk
    by_cases h2 : w = n + r
    · rw [if_pos h2] at hwk
      exact hci hwk
    · rw [if_neg h2] at hwk
      omega

lemma V2_no_cone (n : ℕ) (C : Circuit) (r c i : ℕ) (hr : r < C.gates.length)
    (hi : i < r) (hci : c ≠ n + i)
    (huniq : ∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) :
    ∀ j', j' < C.gates.length - 1 → ¬ InCone n (V2 n C r c i) i j' := by
  intro j' hj' h
  obtain ⟨r', _, _, hrin, h4⟩ := inCone_reader n _ i j' h
  have hr'j : r' ≤ j' := by
    rcases h4 with h4 | h4
    · omega
    · have := (inCone_lt n _ r' j' h4).1
      omega
  exact V2_no_reader n C r c i hr hi hci huniq r' (by omega) hrin

lemma rho_inj (r : ℕ) : Function.Injective (rho r) := by
  intro a b h
  unfold rho at h
  split_ifs at h <;> omega

lemma rho_ne (r k : ℕ) : rho r k ≠ r := by
  unfold rho; split_ifs <;> omega

lemma rho_surj (r k m : ℕ) (hr : r < m) (hk : k < m) (hne : k ≠ r) : ∃ k', k' < m - 1 ∧ rho r k' = k := by
  by_cases h : k < r
  · exact ⟨k, by omega, by unfold rho; rw [if_pos h]⟩
  · exact ⟨k - 1, by omega, by unfold rho; rw [if_neg (by omega)]; omega⟩

lemma wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq, foldl_len, List.length_ofFn]

lemma out_lt (n : ℕ) (C : Circuit) (x : Fin n → Bool) (h : wv n C x C.output = true) :
    C.output < n + C.gates.length := by
  by_contra hge
  unfold wv at h
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [wires_len]; omega)] at h
  simp at h

lemma card_pairs_rho (m r : ℕ) (hr : r < m) (P Q : ℕ → ℕ → Prop)
    [DecidablePred (fun p : ℕ × ℕ => P p.1 p.2)] [DecidablePred (fun p : ℕ × ℕ => Q p.1 p.2)]
    (hQP : ∀ a' b', a' < m → b' < m → Q a' b' →
      a' < m - 1 ∧ b' < m - 1 ∧ P (rho r a') (rho r b'))
    (i j : ℕ) (hi : i < m) (hj : j < m) (hP : P i j)
    (hne : ∀ a' b', Q a' b' → ¬ (rho r a' = i ∧ rho r b' = j)) :
    ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => Q p.1 p.2)).card <
      ((Finset.range m ×ˢ Finset.range m).filter (fun p : ℕ × ℕ => P p.1 p.2)).card := by
  have hinj : Function.Injective (fun p : ℕ × ℕ => (rho r p.1, rho r p.2)) := by
    intro p q h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (rho_inj r h.1) (rho_inj r h.2)
  rw [← Finset.card_image_of_injective _ hinj]
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_of_subset]
  · refine ⟨(i, j), ?_, ?_⟩
    · rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
      exact ⟨⟨hi, hj⟩, hP⟩
    · intro hmem
      rw [Finset.mem_image] at hmem
      obtain ⟨⟨a', b'⟩, hab, heq⟩ := hmem
      rw [Finset.mem_filter] at hab
      simp only [Prod.mk.injEq] at heq
      exact hne a' b' hab.2 heq
  · intro p hp
    rw [Finset.mem_image] at hp
    obtain ⟨⟨a', b'⟩, hab, rfl⟩ := hp
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hab
    obtain ⟨h1, h2, h3⟩ := hQP a' b' hab.1.1 hab.1.2 hab.2
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
    exact ⟨⟨rho_lt r a' m hr h1, rho_lt r b' m hr h2⟩, h3⟩

lemma pairs_lt (n : ℕ) (C C' : Circuit) (r i j : ℕ) (hr : r < C.gates.length) (hir : i < r)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hcone : ∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b'))
    (hno : ∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j')
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone n C i j)
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
      (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)]
    [DecidablePred (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
      (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)] :
    ((Finset.range C'.gates.length ×ˢ Finset.range C'.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
        (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2)).card <
    ((Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
        (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)).card := by
  rw [hlen]
  have hjm := (inCone_lt n C i j hij)
  refine card_pairs_rho C.gates.length r hr
    (fun a b => (gateAt C a).op = GateOp.and ∧ (gateAt C b).op = GateOp.and ∧ InCone n C a b)
    (fun a b => (gateAt C' a).op = GateOp.and ∧ (gateAt C' b).op = GateOp.and ∧
      InCone n C' a b) ?_ i j (by omega) hjm.2 ⟨hi, hj, hij⟩ ?_
  · rintro a' b' _ hb' ⟨ha, hb, hab⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have ha' := (inCone_lt n C' a' b' hab).1
    have ha'' : a' < C.gates.length - 1 := by omega
    refine ⟨ha'', hb'', ?_, ?_, hcone a' b' hb'' hab⟩
    · rw [← hops a' ha'']; exact ha
    · rw [← hops b' hb'']; exact hb
  · rintro a' b' ⟨_, hb, hab⟩ ⟨h1, _⟩
    have hb'' : b' < C.gates.length - 1 := by
      rcases Nat.lt_or_ge b' (C.gates.length - 1) with h | h
      · exact h
      · have hb3 := (inCone_lt n C' a' b' hab).2
        have e : b' = C.gates.length - 1 := by omega
        rw [e, htop] at hb
        exact absurd hb (by simp)
    have e : rho r i = i := by unfold rho; rw [if_pos hir]
    have e2 : a' = i := rho_inj r (h1.trans e.symm)
    rw [e2] at hab
    exact hno b' hb'' hab

lemma pairs_lt2 (n : ℕ) (C C' : Circuit) (r i j : ℕ) (hr : r < C.gates.length) (hir : i < r)
    (hlen : C'.gates.length = C.gates.length)
    (hops : ∀ k', k' < C.gates.length - 1 → (gateAt C' k').op = (gateAt C (rho r k')).op)
    (htop : (gateAt C' (C.gates.length - 1)).op = GateOp.or)
    (hcone : ∀ a' b', b' < C.gates.length - 1 → InCone n C' a' b' →
        InCone n C (rho r a') (rho r b'))
    (hno : ∀ j', j' < C.gates.length - 1 → ¬ InCone n C' i j')
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone n C i j)
    (T T' : Finset (ℕ × ℕ))
    (hT : ∀ p : ℕ × ℕ, p ∈ T ↔ (p.1 < C.gates.length ∧ p.2 < C.gates.length) ∧
      (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2)
    (hT' : ∀ p : ℕ × ℕ, p ∈ T' ↔ (p.1 < C'.gates.length ∧ p.2 < C'.gates.length) ∧
      (gateAt C' p.1).op = GateOp.and ∧ (gateAt C' p.2).op = GateOp.and ∧
        InCone n C' p.1 p.2) :
    T'.card < T.card := by
  classical
  have e : T = (Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C p.1).op = GateOp.and ∧
        (gateAt C p.2).op = GateOp.and ∧ InCone n C p.1 p.2) := by
    ext p
    rw [hT, Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  have e' : T' = (Finset.range C'.gates.length ×ˢ Finset.range C'.gates.length).filter
      (fun p : ℕ × ℕ => (gateAt C' p.1).op = GateOp.and ∧
        (gateAt C' p.2).op = GateOp.and ∧ InCone n C' p.1 p.2) := by
    ext p
    rw [hT', Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range]
  rw [e, e']
  exact pairs_lt n C C' r i j hr hir hlen hops htop hcone hno hi hj hij

lemma reader_or (n : ℕ) (C : Circuit) (hC : AO2 n C) (hout : C.output < n + C.gates.length)
    (i r : ℕ) (hr : r < C.gates.length)
    (hmin : ∀ D : Circuit, AO2 n D →
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) → C.gates.length ≤ D.gates.length)
    (hin : n + i ∈ (gateAt C r).inputs) :
    (gateAt C r).op = GateOp.or ∧ ∃ c, c ≠ n + i ∧ c < n + r ∧
      ((gateAt C r).inputs = [n + i, c] ∨ (gateAt C r).inputs = [c, n + i]) := by
  obtain ⟨hop, ⟨a, c0, hab⟩, hlt⟩ := hC r hr
  have hir : n + i < n + r := hlt _ hin
  have hin' : n + i = a ∨ n + i = c0 := by rw [hab] at hin; simpa using hin
  by_contra hcon
  have key : ∀ x, wv n C x (n + i) = false → wv n C x (n + r) = false := by
    intro x hx
    rw [wv_rec n C x (aob hC) r hr, hab]
    rcases hop with hop | hop
    · rw [hop, eval_and_pair]
      rcases hin' with h | h
      · rw [← h, hx]; rfl
      · rw [← h, hx]; simp
    · rw [hop, eval_or_pair]
      have ha : a = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, a, hne, hlt a (by rw [hab]; simp), ?_⟩
        rcases hin' with h | h
        · exact absurd h.symm hne
        · right; rw [hab, h]
      have hc : c0 = n + i := by
        by_contra hne
        apply hcon
        refine ⟨hop, c0, hne, hlt c0 (by rw [hab]; simp), ?_⟩
        left; rw [hab, ha]
      rw [ha, hc, hx]; rfl
  have hfun : ∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
      wv n (V1 n C r (n + i)) x (V1 n C r (n + i)).output = wv n C x C.output :=
    fun x hb => V1_fun n C r (n + i) x hC hr hir hout hb (key x)
  have hle := hmin _ (V1_AO2 n C r (n + i) hC hr hir) hfun
  rw [V1_len] at hle
  omega

lemma reader_unique (n : ℕ) (C : Circuit) (hC : AO2 n C)
    (hout : C.output < n + C.gates.length) (i r1 r2 : ℕ) (h12 : r1 < r2)
    (hr2 : r2 < C.gates.length)
    (hmin : ∀ D : Circuit, AO2 n D →
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) → C.gates.length ≤ D.gates.length)
    (hin1 : n + i ∈ (gateAt C r1).inputs) (hin2 : n + i ∈ (gateAt C r2).inputs) : False := by
  have hr1 : r1 < C.gates.length := by omega
  obtain ⟨hop1, c1, hc1, hc1lt, hi1⟩ := reader_or n C hC hout i r1 hr1 hmin hin1
  obtain ⟨hop2, c2, hc2, hc2lt, hi2⟩ := reader_or n C hC hout i r2 hr2 hmin hin2
  have hir1 : i < r1 := by have := (hC r1 hr1).2.2 _ hin1; omega
  have hir2 : i < r2 := by omega
  have k2 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r2) = wv n C x c2 := by
    intro x hx
    rw [wv_rec n C x (aob hC) r2 hr2, hop2]
    rcases hi2 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have k1 : ∀ x, wv n C x (n + i) = false → wv n C x (n + r1) = wv n C x c1 := by
    intro x hx
    rw [wv_rec n C x (aob hC) r1 hr1, hop1]
    rcases hi1 with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp
  have hD : AO2 n (V2 n C r2 c2 i) := V2_AO2 n C r2 c2 i hC hr2 hc2lt hir2 hout
  have hDlen := V2_len n C r2 c2 i
  have hDfun : ∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
      wv n (V2 n C r2 c2 i) x (V2 n C r2 c2 i).output = wv n C x C.output :=
    fun x hb => V2_out n C r2 c2 i x hC hr2 hc2lt hir2 hout hb (k2 x)
  have hDout : (V2 n C r2 c2 i).output = n + ((V2 n C r2 c2 i).gates.length - 1) := by
    rw [hDlen]
    show n + C.gates.length - 1 = n + (C.gates.length - 1)
    omega
  have hDtop : gateAt (V2 n C r2 c2 i) ((V2 n C r2 c2 i).gates.length - 1) =
      ⟨GateOp.or, [tau n r2 c2 C.output, n + i]⟩ := by
    rw [hDlen]
    exact V2_top n C r2 c2 i (by omega)
  have h0 : ∀ x, wv n (V2 n C r2 c2 i) x (n + i) = false →
      wv n (V2 n C r2 c2 i) x (n + r1) = wv n (V2 n C r2 c2 i) x c1 := by
    intro x hx
    rw [V2_low n C r2 c2 i x hC hr2 hc2lt hir2 hout (n + i) (by omega)] at hx
    rw [V2_low n C r2 c2 i x hC hr2 hc2lt hir2 hout (n + r1) (by omega),
      V2_low n C r2 c2 i x hC hr2 hc2lt hir2 hout c1 (by omega)]
    exact k1 x hx
  have hEfun : ∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
      wv n (V1 n (V2 n C r2 c2 i) r1 c1) x (V1 n (V2 n C r2 c2 i) r1 c1).output =
      wv n C x C.output := fun x hb =>
    (V1_fun_top n (V2 n C r2 c2 i) r1 c1 i (tau n r2 c2 C.output) x hD (by rw [hDlen]; omega)
      hc1lt hir1 hDout hDtop (h0 x)).trans (hDfun x hb)
  have hle := hmin _ (V1_AO2 n (V2 n C r2 c2 i) r1 c1 hD (by rw [hDlen]; omega) hc1lt) hEfun
  rw [V1_len, hDlen] at hle
  omega

lemma step3_core (n : ℕ) (C : Circuit) (hC : AO2 n C) (hout : C.output < n + C.gates.length)
    (i j : ℕ)
    (hmin : ∀ D : Circuit, AO2 n D →
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) → C.gates.length ≤ D.gates.length)
    (hcone : InCone n C i j) :
    ∃ r c, r < C.gates.length ∧ i < r ∧ c < n + r ∧ c ≠ n + i ∧ c ∈ (gateAt C r).inputs ∧
      (gateAt C r).op = GateOp.or ∧
      (∀ k, k < C.gates.length → n + i ∈ (gateAt C k).inputs → k = r) ∧
      (∀ x, wv n C x (n + i) = false → wv n C x (n + r) = wv n C x c) := by
  obtain ⟨r, hr, hir, hrin, _⟩ := inCone_reader n C i j hcone
  obtain ⟨hop, c, hc, hclt, hi⟩ := reader_or n C hC hout i r hr hmin hrin
  refine ⟨r, c, hr, hir, hclt, hc, ?_, hop, ?_, ?_⟩
  · rcases hi with h | h <;> rw [h] <;> simp
  · intro k hk hkin
    rcases Nat.lt_trichotomy k r with h | h | h
    · exact (reader_unique n C hC hout i k r h hr hmin hkin hrin).elim
    · exact h
    · exact (reader_unique n C hC hout i r k h hk hmin hrin hkin).elim
  · intro x hx
    rw [wv_rec n C x (aob hC) r hr, hop]
    rcases hi with h | h
    · rw [h, eval_or_pair, hx]; rfl
    · rw [h, eval_or_pair, hx]; simp

lemma lift_abs (n : ℕ) (C : Circuit) (hC : AO2 n C) (hout : C.output < n + C.gates.length)
    (i j : ℕ)
    (hmin : ∀ D : Circuit, AO2 n D →
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) → C.gates.length ≤ D.gates.length)
    (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hcone : InCone n C i j) :
    ∃ D : Circuit, AO2 n D ∧ D.gates.length = C.gates.length ∧
      (∀ x, (wv n C x (n + i) = true → wv n C x C.output = true) →
        wv n D x D.output = wv n C x C.output) ∧
      PEqualNP.TopForm.andPairs n D < PEqualNP.TopForm.andPairs n C := by
  obtain ⟨r, c, hr, hir, hclt, hci, hcin, hop, huniq, h0⟩ :=
    step3_core n C hC hout i j hmin hcone
  refine ⟨V2 n C r c i, V2_AO2 n C r c i hC hr hclt hir hout, V2_len n C r c i,
    fun x hb => V2_out n C r c i x hC hr hclt hir hout hb (h0 x), ?_⟩
  unfold PEqualNP.TopForm.andPairs
  refine pairs_lt2 n C (V2 n C r c i) r i j hr hir (V2_len n C r c i) ?_ ?_ ?_ ?_ hi hj hcone
    _ _ ?_ ?_
  · intro k' hk'
    rw [V2_gate n C r c i k' hk']
  · rw [V2_top n C r c i (by omega)]
  · intro a' b' hb' h
    exact V2_cone n C r c i hC hr hclt hcin a' b' hb' h
  · exact V2_no_cone n C r c i hr hir hci huniq
  · intro p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
  · intro p
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]

lemma ofFn_of_len (L : List Bool) : ∀ (m : ℕ), L.length = m →
    ∃ x : Fin m → Bool, List.ofFn x = L := by
  intro m hm
  subst hm
  exact ⟨L.get, List.ofFn_get L⟩

lemma AO2_mono {n : ℕ} {C : Circuit} (h : AO2 n C) : Monotone2 C := by
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.getElem_of_mem hg
  have e := gateAt_eq C k hk
  obtain ⟨h1, ⟨a, b, h2⟩, _⟩ := h k hk
  rw [e] at h1 h2
  refine ⟨?_, by rw [h2]; simp⟩
  rcases h1 with h1 | h1
  · exact Or.inl h1
  · exact Or.inr h1

lemma to_AO2 (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (h2 : ∀ g ∈ C.gates, ¬ g.inputs.length < 2) : AO2 26 C := by
  intro k hk
  have e := gateAt_eq C k hk
  have hmem : C.gates[k] ∈ C.gates := List.getElem_mem hk
  have hl := legal_of C hmono _ hmem
  have h3 := h2 _ hmem
  refine ⟨by rw [e]; exact hl.1, ?_, hrb k hk⟩
  rw [e]
  have h4 : (C.gates[k]).inputs.length = 2 := by
    have := hl.2
    omega
  exact List.length_eq_two.mp h4

theorem main26 (A R : List Bool → Prop) (hA : ∀ L, A L → L.length = 26)
    (hR : ∀ L, R L → L.length = 26) (hAne : ∃ L, A L) (hRne : ∃ L, R L)
    (C : Circuit) (hmono : Monotone2 C) (hrb : ReadsBack 26 C)
    (hacc : ∀ L, A L → C.eval L = true) (hrej : ∀ L, R L → C.eval L = false)
    (i j : ℕ) (hi : (gateAt C i).op = GateOp.and) (hj : (gateAt C j).op = GateOp.and)
    (hij : InCone 26 C i j)
    (hB : ∀ L, R L → (C.wires L).getD (26 + i) false = false) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧ ((∀ L, A L → D.eval L = true) ∧
      ∀ L, R L → D.eval L = false) ∧
      (D.size < C.size ∨ D.size = C.size ∧
        PEqualNP.TopForm.andPairs 26 D < PEqualNP.TopForm.andPairs 26 C) := by
  by_cases hsm : ∃ D : Circuit, Monotone2 D ∧ ReadsBack 26 D ∧
      ((∀ L, A L → D.eval L = true) ∧ ∀ L, R L → D.eval L = false) ∧ D.size < C.size
  · obtain ⟨D, h1, h2, h3, h4⟩ := hsm
    exact ⟨D, h1, h2, h3, Or.inl h4⟩
  · have hne : ∃ x y : List Bool, x.length = 26 ∧ y.length = 26 ∧ C.eval x = true ∧
        C.eval y = false := by
      obtain ⟨La, ha⟩ := hAne
      obtain ⟨Lr, hr⟩ := hRne
      exact ⟨La, Lr, hA _ ha, hR _ hr, hacc _ ha, hrej _ hr⟩
    have hC : AO2 26 C := by
      apply to_AO2 C hmono hrb
      intro g hg hlt
      obtain ⟨C', m1, m2, heq, hsz⟩ := short_case C hmono hrb hne ⟨g, hg, Or.inl hlt⟩
      apply hsm
      refine ⟨C', m1, m2, ⟨?_, ?_⟩, hsz⟩
      · intro L hL
        rw [heq L (hA L hL)]
        exact hacc L hL
      · intro L hL
        rw [heq L (hR L hL)]
        exact hrej L hL
    have hbelA : ∀ x : Fin 26 → Bool, A (List.ofFn x) →
        (wv 26 C x (26 + i) = true → wv 26 C x C.output = true) := by
      intro x hL _
      exact hacc _ hL
    have hbelR : ∀ x : Fin 26 → Bool, R (List.ofFn x) →
        (wv 26 C x (26 + i) = true → wv 26 C x C.output = true) := by
      intro x hL hv
      have h1 : wv 26 C x (26 + i) = false := hB _ hL
      rw [h1] at hv
      exact absurd hv (by simp)
    have tg : ∀ D : Circuit, AO2 26 D →
        (∀ x, (wv 26 C x (26 + i) = true → wv 26 C x C.output = true) →
          wv 26 D x D.output = wv 26 C x C.output) →
        ((∀ L, A L → D.eval L = true) ∧ ∀ L, R L → D.eval L = false) := by
      intro D _ hf
      constructor
      · intro L hL
        obtain ⟨x, hx⟩ := ofFn_of_len L 26 (hA L hL)
        subst hx
        have h1 := hf x (hbelA x hL)
        have h2 : wv 26 C x C.output = true := hacc _ hL
        show wv 26 D x D.output = true
        rw [h1]
        exact h2
      · intro L hL
        obtain ⟨x, hx⟩ := ofFn_of_len L 26 (hR L hL)
        subst hx
        have h1 := hf x (hbelR x hL)
        have h2 : wv 26 C x C.output = false := hrej _ hL
        show wv 26 D x D.output = false
        rw [h1]
        exact h2
    have hmin : ∀ D : Circuit, AO2 26 D →
        (∀ x, (wv 26 C x (26 + i) = true → wv 26 C x C.output = true) →
          wv 26 D x D.output = wv 26 C x C.output) → C.gates.length ≤ D.gates.length := by
      intro D hD hf
      by_contra hlt
      apply hsm
      refine ⟨D, AO2_mono hD, (fun k hk => (hD k hk).2.2), tg D hD hf, ?_⟩
      show D.gates.length < C.gates.length
      omega
    have hout : C.output < 26 + C.gates.length := by
      obtain ⟨La, ha⟩ := hAne
      obtain ⟨x, hx⟩ := ofFn_of_len La 26 (hA La ha)
      subst hx
      exact out_lt 26 C x (hacc _ ha)
    obtain ⟨D, hD, hlen, hf, hp⟩ := lift_abs 26 C hC hout i j hmin hi hj hij
    exact ⟨D, AO2_mono hD, (fun k hk => (hD k hk).2.2), tg D hD hf, Or.inr ⟨hlen, hp⟩⟩

end PEqualNP.Outside.L_meta_18294.Lift

namespace PEqualNP.Outside.L_meta_18294.Main

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_18294.Flat

def incidence (p l : Fin 13) : Prop :=
  ∃ d ∈ ({0, 1, 3, 9} : Finset (Fin 13)), p = l + d

instance (p l : Fin 13) : Decidable (incidence p l) := by unfold incidence; infer_instance

def star (X Y : Finset (Fin 13)) : Prop :=
  (∃ l, ∀ p ∈ X, incidence p l) ∨ ∃ p, ∀ l ∈ Y, incidence p l

def row (X Y : Finset (Fin 13)) (u : Fin 26) : Bool :=
  decide ((∃ i ∈ X, u = Fin.castAdd 13 i) ∨ ∃ j ∈ Y, u = Fin.natAdd 13 j)

def answer (X Y : Finset (Fin 13)) : Bool :=
  decide (∃ p ∈ X, ∃ l ∈ Y, incidence p l)

def fits (C : Circuit) : Prop :=
  ∀ X Y, star X Y → C.eval (List.ofFn (row X Y)) = answer X Y

def trim (cap : ℕ) (g : Gate) : Gate :=
  match g.op with
  | .and => if ∀ i ∈ g.inputs, i < cap then g else ⟨.or, []⟩
  | _ => ⟨.or, g.inputs.filter fun i => decide (i < cap)⟩

def trimList (cap : ℕ) : List Gate → List Gate
  | [] => []
  | g :: gs => trim cap g :: trimList (cap + 1) gs

lemma trimLength (n : ℕ) (gs : List Gate) : (trimList n gs).length = gs.length := by
  induction gs generalizing n with
  | nil => rfl
  | cons g gs ih => simp [trimList, ih]

lemma trimGet (n : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    (trimList n gs)[j]'(by rwa [trimLength]) = trim (n+j) gs[j] := by
  induction gs generalizing n j with
  | nil => simp at hj
  | cons g gs ih =>
    cases j with
    | zero => simp [trimList]
    | succ j =>
      simpa [trimList,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
        (ih (n+1) j (Nat.lt_of_succ_lt_succ hj))

lemma trimLegal (cap : ℕ) (g : Gate) (h : g.inputs.length ≤ 2) :
    ((trim cap g).op = .and ∨ (trim cap g).op = .or) ∧
      (trim cap g).inputs.length ≤ 2 ∧ ∀ i ∈ (trim cap g).inputs, i < cap := by
  rcases g with ⟨op, ins⟩
  have orBranch :
      ((⟨.or, ins.filter fun i => decide (i < cap)⟩ : Gate).op = .and ∨
        (⟨.or, ins.filter fun i => decide (i < cap)⟩ : Gate).op = .or) ∧
      (ins.filter fun i => decide (i < cap)).length ≤ 2 ∧
      ∀ i ∈ (ins.filter fun i => decide (i < cap)), i < cap :=
    ⟨Or.inr rfl, (List.length_filter_le _ _).trans h,
      fun i hi => of_decide_eq_true (List.mem_filter.mp hi).2⟩
  cases op
  case and =>
    unfold trim
    simp only
    split
    · rename_i good
      exact ⟨Or.inl rfl, h, good⟩
    · simp
  all_goals exact orBranch

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun v g => v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) w

lemma trimBit (w : List Bool) (g : Gate) (h : g.op = .and ∨ g.op = .or) :
    (trim w.length g).op.eval ((trim w.length g).inputs.map fun i => w.getD i false) =
      g.op.eval (g.inputs.map fun i => w.getD i false) := by
  rcases g with ⟨op, ins⟩
  change op = .and ∨ op = .or at h
  rcases h with hop | hop
  · subst op
    unfold trim
    simp only
    split
    · rfl
    · rename_i bad
      change false = (ins.map fun i => w.getD i false).all id
      symm
      apply Bool.eq_false_iff.mpr
      intro on
      apply bad
      intro i mem
      by_contra beyond
      have ix := List.all_eq_true.mp on (w.getD i false) (List.mem_map.mpr ⟨i, mem, rfl⟩)
      have miss : w.getD i false = false := List.getD_eq_default _ _ (by omega)
      rw [id_eq, miss] at ix
      contradiction
  · subst op
    change ((ins.filter fun i => decide (i < w.length)).map fun i => w.getD i false).any id =
      (ins.map fun i => w.getD i false).any id
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_map, List.any_eq_true, Function.comp_apply, id_eq,
      List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨i, ⟨mem, _⟩, val⟩
      exact ⟨i, mem, val⟩
    · rintro ⟨i, mem, val⟩
      refine ⟨i, ⟨mem, ?_⟩, val⟩
      by_contra beyond
      have miss : w.getD i false = false := List.getD_eq_default _ _ (by omega)
      rw [miss] at val
      contradiction

lemma trimRun (gs : List Gate) (h : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (w : List Bool) :
    run (trimList w.length gs) w = run gs w := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    let b := g.op.eval (g.inputs.map fun i => w.getD i false)
    change run (trimList (w.length + 1) gs)
      (w ++ [(trim w.length g).op.eval ((trim w.length g).inputs.map fun i => w.getD i false)]) =
      run gs (w ++ [b])
    rw [trimBit w g (h g (by simp))]
    have e : (w ++ [b]).length = w.length + 1 := by simp
    rw [← e]
    exact ih (fun z hz => h z (List.mem_cons_of_mem _ hz)) _

lemma runLength (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w ++ [_])).length = _
    rw [ih]
    simp [Nat.add_comm, Nat.add_left_comm]

lemma appendValue (C : Circuit) (a b : ℕ) (w : List Bool) :
    (⟨C.gates ++ [⟨.or, [a,b]⟩], w.length + C.size⟩ : Circuit).eval w =
      ((C.wires w).getD a false || (C.wires w).getD b false) := by
  change (run (C.gates ++ [⟨.or,[a,b]⟩]) w).getD (w.length + C.gates.length) false = _
  have l : (run C.gates w).length = w.length + C.gates.length :=
    runLength _ _
  rw [show run (C.gates ++ [⟨.or,[a,b]⟩]) w =
    run C.gates w ++ [((C.wires w).getD a false || (C.wires w).getD b false)] by
      simp [run, Circuit.wires, List.foldl_append, GateOp.eval]]
  rw [← l, List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self]
  rfl

lemma normalize (n : ℕ) (C : Circuit) (hm : Monotone2 C)
    (a b : Fin (n + C.size)) :
    ∃ D : Circuit, Monotone2 D ∧ ReadsBack n D ∧ D.size = C.size + 1 ∧
      ∀ w : List Bool, w.length = n →
        D.eval w = ((C.wires w).getD a.val false || (C.wires w).getD b.val false) := by
  let gs := C.gates ++ [⟨.or, [a.val, b.val]⟩]
  let D : Circuit := ⟨trimList n gs, n + C.size⟩
  have legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    rcases List.mem_append.mp hg with hg | hg
    · exact legal_of C hm g hg
    · obtain rfl := List.mem_singleton.mp hg
      simp
  have hlen : D.gates.length = gs.length := trimLength _ _
  have indexed (j : ℕ) (hj : j < D.gates.length) :
      (D.gates[j].op = .and ∨ D.gates[j].op = .or) ∧ D.gates[j].inputs.length ≤ 2 ∧
        ∀ i ∈ D.gates[j].inputs, i < n+j := by
    have hj' : j < gs.length := by omega
    have eq : D.gates[j] = trim (n+j) gs[j] := trimGet _ _ _ hj'
    rw [eq]
    exact trimLegal _ _ (legal _ (List.getElem_mem hj')).2
  refine ⟨D, ?_, ?_, by simp [D, gs, Circuit.size, trimLength], ?_⟩
  · intro g hg
    obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
    have z := indexed j hj
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using And.intro z.1 z.2.1
  · intro j hj i hi
    rw [gateAt_eq D j hj] at hi
    exact (indexed j hj).2.2 i hi
  · intro w hw
    have eq : run (trimList n gs) w = run gs w := by
      rw [← hw]
      exact trimRun _ (fun g hg => (legal g hg).1) _
    change (run (trimList n gs) w).getD (n + C.size) false = _
    rw [eq]
    calc
      (run gs w).getD (n + C.size) false = (run gs w).getD (w.length + C.size) false :=
        congrArg (fun i => (run gs w).getD i false) (congrArg (· + C.size) hw.symm)
      _ = _ := appendValue C a b w

def points (s t : Fin 26) : Finset (Fin 13) :=
  Finset.univ.filter fun p => Fin.castAdd 13 p = s ∨ Fin.castAdd 13 p = t

def lines (s t : Fin 26) : Finset (Fin 13) :=
  Finset.univ.filter fun l => Fin.natAdd 13 l = s ∨ Fin.natAdd 13 l = t

lemma pairRow (s t : Fin 26) : row (points s t) (lines s t) = pr s t := by
  funext u
  apply decide_eq_decide.mpr
  constructor
  · rintro (⟨p, hp, rfl⟩ | ⟨l, hl, rfl⟩)
    · exact (Finset.mem_filter.mp hp).2
    · exact (Finset.mem_filter.mp hl).2
  · intro h
    rcases Fin.addCases (fun p : Fin 13 => Or.inl ⟨p, rfl⟩)
      (fun l : Fin 13 => Or.inr ⟨l, rfl⟩) u (motive := fun v =>
        (∃ p, v = Fin.castAdd 13 p) ∨ ∃ l, v = Fin.natAdd 13 l) with ⟨p, rfl⟩ | ⟨l, rfl⟩
    · exact Or.inl ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩
    · exact Or.inr ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩

set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
lemma pairStar : ∀ s t : Fin 26, ∃ l : Fin 13, ∀ p ∈ points s t, incidence p l := by
  intro s
  fin_cases s <;> decide +kernel

set_option maxRecDepth 32768 in
set_option maxHeartbeats 5000000 in
lemma rowAnswer : ∀ s t : Fin 26, answer (points s t) (lines s t) = adjb s t := by
  intro s
  fin_cases s <;> decide +kernel

lemma fitsPairs {C : Circuit} (h : fits C) (s t : Fin 26) :
    val C.gates C.output (pr s t) = adjb s t := by
  have e := h (points s t) (lines s t) (Or.inl (pairStar s t))
  rw [pairRow, rowAnswer] at e
  exact e

lemma flatLower {C : Circuit} (hm : Monotone2 C) (hr : ReadsBack 26 C) (ok : fits C)
    (flat : ¬ ∃ i j, (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j) :
    64 ≤ C.size := by
  have legal := legal_of C hm
  have hin := hin_of C 26 hr
  have H : Hy C.gates C.output := by
    exact ⟨legal, hin, lin_and C legal hin flat,
      fun u v e => (fitsPairs ok u v).trans e, fun u v e => (fitsPairs ok u v).trans e⟩
  exact core2 C.gates C.output H

end PEqualNP.Outside.L_meta_18294.Main

namespace PEqualNP.Outside.L_meta_18294.Single

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.CircuitMoves
  PEqualNP.HeptadCover

def pgAdj (u v : Fin 26) : Bool :=
  if h1 : u.val < 13 ∧ 13 ≤ v.val then
    decide (⟨u.val, h1.1⟩ ∈ singerLines3 ⟨v.val - 13, by omega⟩)
  else if h2 : v.val < 13 ∧ 13 ≤ u.val then
    decide (⟨v.val, h2.1⟩ ∈ singerLines3 ⟨u.val - 13, by omega⟩)
  else false

def nbrs (u : Fin 26) : Finset (Fin 26) :=
  Finset.univ.filter fun v => pgAdj u v = true

def pgEdges : Finset (Fin 26 × Fin 26) :=
  Finset.univ.filter fun p => p.1.val < 13 ∧ pgAdj p.1 p.2 = true

lemma pgAdj_symm : ∀ u v : Fin 26, pgAdj u v = pgAdj v u := by decide

lemma pgAdj_irrefl : ∀ u : Fin 26, pgAdj u u = false := by decide

lemma pgAdj_bip : ∀ u v : Fin 26, pgAdj u v = true → (u.val < 13) ≠ (v.val < 13) := by decide

lemma nbrs_card : ∀ u : Fin 26, (nbrs u).card = 4 := by decide

set_option maxRecDepth 32768 in
lemma pgAdj_eq_adjb : ∀ u v : Fin 26, pgAdj u v = PEqualNP.Outside.L_meta_18294.Flat.adjb u v := by
  intro u
  fin_cases u <;> decide +kernel

lemma pg_no_c4 : ∀ u v : Fin 26, u ≠ v → (nbrs u ∩ nbrs v).card ≤ 1 := by
  have e (u : Fin 26) : nbrs u = PEqualNP.Outside.L_meta_18294.Flat.N u := by
    unfold nbrs PEqualNP.Outside.L_meta_18294.Flat.N
    simp only [pgAdj_eq_adjb]
  intro u v he
  rw [e, e]
  exact PEqualNP.Outside.L_meta_18294.Flat.hLN u v he

lemma pgEdges_card : pgEdges.card = 52 := by
  have heq : pgEdges = (Finset.univ.filter fun u : Fin 26 => u.val < 13).biUnion
      fun u => (nbrs u).image fun v => (u, v) := by
    ext ⟨u, v⟩
    simp only [pgEdges, nbrs, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion,
      Finset.mem_image, Prod.mk.injEq]
    constructor
    · intro ⟨hu, hadj⟩
      exact ⟨u, hu, v, hadj, rfl, rfl⟩
    · rintro ⟨u', hu', v', hadj, rfl, rfl⟩
      exact ⟨hu', hadj⟩
  rw [heq, Finset.card_biUnion]
  · calc ∑ u ∈ Finset.univ.filter (fun u : Fin 26 => u.val < 13), ((nbrs u).image fun v => (u, v)).card
        = ∑ u ∈ Finset.univ.filter (fun u : Fin 26 => u.val < 13), (nbrs u).card := by
          refine Finset.sum_congr rfl fun u _ => Finset.card_image_of_injective _ fun a b h => congrArg Prod.snd h
      _ = ∑ _u ∈ Finset.univ.filter (fun u : Fin 26 => u.val < 13), 4 :=
          Finset.sum_congr rfl fun u _ => nbrs_card u
      _ = (Finset.univ.filter fun u : Fin 26 => u.val < 13).card * 4 := by rw [Finset.sum_const, smul_eq_mul]
      _ = 52 := by
          have h13 : (Finset.univ.filter fun u : Fin 26 => u.val < 13).card = 13 := by decide
          rw [h13]
  · intro u1 _ u2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro p h1 h2
    obtain ⟨v1, _, rfl⟩ := Finset.mem_image.mp h1
    obtain ⟨v2, _, heqp⟩ := Finset.mem_image.mp h2
    exact hne (congrArg Prod.fst heqp).symm

lemma mem_nbrs_iff (u v : Fin 26) : v ∈ nbrs u ↔ pgAdj u v = true := by
  simp [nbrs]

lemma mem_pgEdges_iff (p : Fin 26 × Fin 26) :
    p ∈ pgEdges ↔ p.1.val < 13 ∧ pgAdj p.1 p.2 = true := by
  simp [pgEdges]

def qPPList : List (List (Fin 13)) :=
  [[0, 1, 2, 5], [0, 1, 2, 5], [0, 1, 2, 5], [0, 2, 3, 4], [0, 1, 4, 6],
   [0, 1, 2, 5], [0, 1, 2, 6], [0, 1, 2, 7], [0, 1, 4, 8], [0, 2, 4, 9],
   [0, 1, 5, 10], [0, 1, 2, 11], [0, 1, 4, 12]]

def qLLList : List (List (Fin 13)) :=
  [[2, 4, 5, 6], [5, 6, 7, 11], [4, 6, 7, 8], [2, 5, 7, 8], [2, 6, 8, 10],
   [2, 4, 7, 11], [4, 5, 8, 10], [2, 4, 5, 6], [2, 5, 6, 10], [2, 4, 6, 8],
   [2, 4, 5, 8], [2, 4, 5, 6], [4, 5, 6, 10]]

def qPLList : List (List (Fin 13)) :=
  [[0, 1, 2, 5], [0, 1, 2, 5], [2, 4, 5, 6], [0, 1, 2, 5], [2, 4, 5, 6],
   [2, 4, 5, 6], [2, 4, 5, 6], [2, 4, 7, 8], [2, 4, 5, 8], [0, 1, 2, 5],
   [2, 5, 6, 10], [2, 4, 6, 11], [2, 4, 5, 12]]

def qPP (d : Fin 13) : Finset (Fin 13) := (qPPList.getD d.val []).toFinset
def qLL (d : Fin 13) : Finset (Fin 13) := (qLLList.getD d.val []).toFinset
def qPL (d : Fin 13) : Finset (Fin 13) := (qPLList.getD d.val []).toFinset

lemma qPP_ok : ∀ d : Fin 13, IsQuadrangle singerLines3 (qPP d) ∧ (0 : Fin 13) ∈ qPP d ∧ d ∈ qPP d := by
  decide

lemma qLL_ok : ∀ d : Fin 13, IsQuadrangle singerLines3 (qLL d) ∧
    (0 : Fin 13) ∈ missLines singerLines3 (qLL d) ∧ d ∈ missLines singerLines3 (qLL d) := by
  decide

lemma qPL_ok : ∀ d : Fin 13, d ∉ singerLines3 0 →
    IsQuadrangle singerLines3 (qPL d) ∧ d ∈ qPL d ∧ (0 : Fin 13) ∈ missLines singerLines3 (qPL d) := by
  decide

lemma singerLines3_shift (k l p : Fin 13) :
    p + k ∈ singerLines3 (l + k) ↔ p ∈ singerLines3 l := by
  simp only [singerLines3, Finset.mem_filter, Finset.mem_univ, true_and]
  have hmod : ((p + k).val + 13 - (l + k).val) % 13 = (p.val + 13 - l.val) % 13 := by
    simp only [Fin.val_add]
    omega
  rw [hmod]

lemma isQuad_shift (k : Fin 13) (Q : Finset (Fin 13)) (hQ : IsQuadrangle singerLines3 Q) :
    IsQuadrangle singerLines3 (Q.image (· + k)) := by
  have hinj : Function.Injective (fun x : Fin 13 => x + k) := fun a b h => by
    simpa using congrArg (· - k) h
  refine ⟨by rw [Finset.card_image_of_injective Q hinj]; exact hQ.1, fun l => ?_⟩
  have hsub : (Q.image (· + k) ∩ singerLines3 l) = (Q ∩ singerLines3 (l - k)).image (· + k) := by
    ext x
    simp only [Finset.mem_inter, Finset.mem_image]
    constructor
    · rintro ⟨⟨y, hy, rfl⟩, hxl⟩
      refine ⟨y, ⟨hy, ?_⟩, rfl⟩
      have h1 := singerLines3_shift k (l - k) y
      have h2 : l - k + k = l := sub_add_cancel l k
      rw [h2] at h1
      exact h1.mp hxl
    · rintro ⟨y, ⟨hy, hyl⟩, rfl⟩
      refine ⟨⟨y, hy, rfl⟩, ?_⟩
      have h1 := singerLines3_shift k (l - k) y
      have h2 : l - k + k = l := sub_add_cancel l k
      rw [h2] at h1
      exact h1.mpr hyl
  rw [hsub, Finset.card_image_of_injective _ hinj]
  exact hQ.2 (l - k)

lemma mem_missLines_shift (k : Fin 13) (Q : Finset (Fin 13)) (l : Fin 13) :
    l + k ∈ missLines singerLines3 (Q.image (· + k)) ↔ l ∈ missLines singerLines3 Q := by
  simp only [missLines, Finset.mem_filter, Finset.mem_univ, true_and, Finset.disjoint_left]
  constructor
  · intro h p hp hQ
    exact h ((singerLines3_shift k l p).mpr hp) (Finset.mem_image.mpr ⟨p, hQ, rfl⟩)
  · intro h q hq hQ
    obtain ⟨p, hpQ, rfl⟩ := Finset.mem_image.mp hQ
    exact h ((singerLines3_shift k l p).mp hq) hpQ

def heptFn (Q : Finset (Fin 13)) : Fin 26 → Bool :=
  fun w => if h : w.val < 13 then decide (⟨w.val, h⟩ ∈ Q)
    else decide (⟨w.val - 13, by omega⟩ ∈ missLines singerLines3 Q)

lemma ofFn_heptFn (Q : Finset (Fin 13)) :
    List.ofFn (heptFn Q) =
      (List.ofFn fun p : Fin 13 => decide (p ∈ Q)) ++
      (List.ofFn fun l : Fin 13 => decide (l ∈ missLines singerLines3 Q)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp only [List.getElem_ofFn, heptFn]
    by_cases hi : i < 13
    · rw [List.getElem_append_left (by simp [hi]), List.getElem_ofFn]
      simp [hi]
    · have hlen : (List.ofFn fun p : Fin 13 => decide (p ∈ Q)).length = 13 := List.length_ofFn
      rw [List.getElem_append_right (by omega), List.getElem_ofFn]
      simp [hi]

lemma ofFn_pair_pt_ln (p l : Fin 13) :
    List.ofFn (pairInput (⟨p.val, by omega⟩ : Fin 26) (⟨13 + l.val, by omega⟩ : Fin 26)) =
      (List.ofFn fun x : Fin 13 => decide (x = p)) ++
      (List.ofFn fun x : Fin 13 => decide (x = l)) := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    rw [List.length_ofFn] at h1
    simp only [List.getElem_ofFn, pairInput]
    by_cases hi : i < 13
    · rw [List.getElem_append_left (by simp [hi]), List.getElem_ofFn]
      simp only [Fin.ext_iff]
      have : i ≠ 13 + l.val := by omega
      simp [this]
    · have hlen : (List.ofFn fun x : Fin 13 => decide (x = p)).length = 13 := List.length_ofFn
      rw [List.getElem_append_right (by omega), List.getElem_ofFn]
      simp only [Fin.ext_iff, List.length_ofFn]
      have : i ≠ p.val := by omega
      simp only [this, false_or, decide_eq_decide]
      omega

lemma nonAdj_le_quad (u v : Fin 26) (h : pgAdj u v = false) :
    ∃ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q ∧
      ∀ w : Fin 26, pairInput u v w = true → heptFn Q w = true := by
  have step : ∀ Q : Finset (Fin 13), IsQuadrangle singerLines3 Q →
      heptFn Q u = true → heptFn Q v = true →
      ∃ Q' : Finset (Fin 13), IsQuadrangle singerLines3 Q' ∧
        ∀ w : Fin 26, pairInput u v w = true → heptFn Q' w = true := by
    intro Q hQ hu hv
    refine ⟨Q, hQ, fun w hw => ?_⟩
    simp only [pairInput, decide_eq_true_eq] at hw
    rcases hw with rfl | rfl <;> assumption
  by_cases hu : u.val < 13 <;> by_cases hv : v.val < 13
  · set p1 : Fin 13 := ⟨u.val, hu⟩
    set p2 : Fin 13 := ⟨v.val, hv⟩
    have hok := qPP_ok (p2 - p1)
    apply step ((qPP (p2 - p1)).image (· + p1)) (isQuad_shift p1 _ hok.1)
    · simp only [heptFn, hu, ↓reduceDIte, decide_eq_true_eq, Finset.mem_image]
      exact ⟨0, hok.2.1, zero_add p1⟩
    · simp only [heptFn, hv, ↓reduceDIte, decide_eq_true_eq, Finset.mem_image]
      exact ⟨p2 - p1, hok.2.2, sub_add_cancel p2 p1⟩
  · set p : Fin 13 := ⟨u.val, hu⟩
    set l : Fin 13 := ⟨v.val - 13, by omega⟩
    have hnot : p ∉ singerLines3 l := by
      unfold pgAdj at h
      have hv' : 13 ≤ v.val := by omega
      simp only [hu, hv', and_self, ↓reduceDIte, decide_eq_false_iff_not] at h
      exact h
    have hnot0 : p - l ∉ singerLines3 0 := by
      intro hmem
      have h1 := (singerLines3_shift l 0 (p - l)).mpr hmem
      rw [sub_add_cancel, zero_add] at h1
      exact hnot h1
    have hok := qPL_ok (p - l) hnot0
    apply step ((qPL (p - l)).image (· + l)) (isQuad_shift l _ hok.1)
    · simp only [heptFn, hu, ↓reduceDIte, decide_eq_true_eq, Finset.mem_image]
      exact ⟨p - l, hok.2.1, sub_add_cancel p l⟩
    · simp only [heptFn, hv, ↓reduceDIte, decide_eq_true_eq]
      have h1 := (mem_missLines_shift l (qPL (p - l)) 0).mpr hok.2.2
      rwa [zero_add] at h1
  · set l : Fin 13 := ⟨u.val - 13, by omega⟩
    set p : Fin 13 := ⟨v.val, hv⟩
    have hnot : p ∉ singerLines3 l := by
      unfold pgAdj at h
      have hu' : 13 ≤ u.val := by omega
      have h1 : ¬ (u.val < 13 ∧ 13 ≤ v.val) := by omega
      simp only [h1, ↓reduceDIte, hv, hu', and_self, decide_eq_false_iff_not] at h
      exact h
    have hnot0 : p - l ∉ singerLines3 0 := by
      intro hmem
      have h1 := (singerLines3_shift l 0 (p - l)).mpr hmem
      rw [sub_add_cancel, zero_add] at h1
      exact hnot h1
    have hok := qPL_ok (p - l) hnot0
    apply step ((qPL (p - l)).image (· + l)) (isQuad_shift l _ hok.1)
    · simp only [heptFn, hu, ↓reduceDIte, decide_eq_true_eq]
      have h1 := (mem_missLines_shift l (qPL (p - l)) 0).mpr hok.2.2
      rwa [zero_add] at h1
    · simp only [heptFn, hv, ↓reduceDIte, decide_eq_true_eq, Finset.mem_image]
      exact ⟨p - l, hok.2.1, sub_add_cancel p l⟩
  · set l1 : Fin 13 := ⟨u.val - 13, by omega⟩
    set l2 : Fin 13 := ⟨v.val - 13, by omega⟩
    have hok := qLL_ok (l2 - l1)
    apply step ((qLL (l2 - l1)).image (· + l1)) (isQuad_shift l1 _ hok.1)
    · simp only [heptFn, hu, ↓reduceDIte, decide_eq_true_eq]
      have h1 := (mem_missLines_shift l1 (qLL (l2 - l1)) 0).mpr hok.2.1
      rwa [zero_add] at h1
    · simp only [heptFn, hv, ↓reduceDIte, decide_eq_true_eq]
      have h1 := (mem_missLines_shift l1 (qLL (l2 - l1)) (l2 - l1)).mpr hok.2.2
      rwa [sub_add_cancel l2 l1] at h1

def ValidCirc (C : Circuit) : Prop :=
  Monotone2 C ∧ ReadsBack 26 C ∧
  (∀ (p l : Fin 13), p ∈ singerLines3 l →
    C.eval ((List.ofFn fun x : Fin 13 => decide (x = p)) ++
            (List.ofFn fun x : Fin 13 => decide (x = l))) = true) ∧
  (∀ X Y : Finset (Fin 13), PEqualNP.Outside.L_meta_18294.Main.star X Y →
    PEqualNP.Outside.L_meta_18294.Main.answer X Y = false →
    C.eval (List.ofFn (PEqualNP.Outside.L_meta_18294.Main.row X Y)) = false)

def IsMin (C : Circuit) : Prop :=
  ValidCirc C ∧ ∀ C' : Circuit, ValidCirc C' → C.size ≤ C'.size

def stepW (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepW x := rfl

lemma foldl_stepW_len (gs : List Gate) (w : List Bool) :
    (gs.foldl stepW w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [stepW]; omega

lemma foldl_stepW_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepW w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : i < (stepW w g).length := by simp [stepW]; omega
    rw [ih (stepW w g) hlt]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge_len (w : List Bool) (i : ℕ) (hi : w.length ≤ i) :
    w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma wires_len (n : ℕ) (C : Circuit) (x : Fin n → Bool) :
    (C.wires (List.ofFn x)).length = n + C.gates.length := by
  rw [wires_eq_foldl, foldl_stepW_len, List.length_ofFn]

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j = C.gates[j] := by
  unfold gateAt; exact List.getD_eq_getElem C.gates _ hj

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) :
    gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma wireVal_input {n : ℕ} (C : Circuit) (w : ℕ) (hw : w < n) (x : Fin n → Bool) :
    wireVal n C w x = x ⟨w, hw⟩ := by
  unfold wireVal
  rw [wires_eq_foldl, foldl_stepW_getD_lt _ _ _ (by simp; exact hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma wireVal_ge {n : ℕ} (C : Circuit) (w : ℕ) (hw : n + C.gates.length ≤ w) (x : Fin n → Bool) :
    wireVal n C w x = false := by
  unfold wireVal
  exact getD_ge_len _ _ (by rw [wires_len]; exact hw)

lemma wireVal_gate {n : ℕ} (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (x : Fin n → Bool) :
    wireVal n C (n + j) x = (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i => if i < n + j then wireVal n C i x else false) := by
  unfold wireVal
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    rw [gateAt_eq hj]
    exact (List.take_append_drop j C.gates).symm.trans (by
      congr 1; exact (List.cons_getElem_drop_succ (h := hj)).symm)
  set pre := (C.gates.take j).foldl stepW (List.ofFn x)
  have hpre_len : pre.length = n + j := by
    rw [foldl_stepW_len, List.length_ofFn, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have heq : C.wires (List.ofFn x) = (C.gates.drop (j + 1)).foldl stepW (stepW pre (gateAt C j)) := by
    rw [wires_eq_foldl]
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hpre_get : ∀ i < n + j, (C.wires (List.ofFn x)).getD i false = pre.getD i false := by
    intro i hi
    rw [heq, foldl_stepW_getD_lt _ _ _ (by simp [stepW, hpre_len]; omega)]
    simp [stepW, List.getD_eq_getElem?_getD, List.getElem?_append_left (show i < pre.length by omega)]
  have hnj : (C.wires (List.ofFn x)).getD (n + j) false =
      (gateAt C j).op.eval ((gateAt C j).inputs.map fun i => pre.getD i false) := by
    rw [heq, foldl_stepW_getD_lt _ _ _ (by simp [stepW, hpre_len])]
    simp [stepW, List.getD_eq_getElem?_getD, hpre_len]
  rw [hnj]
  congr 1
  apply List.map_congr_left
  intro i _
  by_cases hi : i < n + j
  · simp only [hi, ↓reduceIte]; exact (hpre_get i hi).symm
  · simp only [hi, ↓reduceIte]; exact getD_ge_len pre i (by omega)

lemma wireVal_gate_rb {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j : ℕ} (hj : j < C.gates.length)
    (x : Fin n → Bool) :
    wireVal n C (n + j) x = (gateAt C j).op.eval
      ((gateAt C j).inputs.map fun i => wireVal n C i x) := by
  rw [wireVal_gate C j hj x]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp [hRB j hj i hi]

lemma wireVal_mono_m2 {n : ℕ} {C : Circuit} (hM : Monotone2 C) (hRB : ReadsBack n C)
    {x y : Fin n → Bool} (hxy : ∀ v : Fin n, x v = true → y v = true) :
    ∀ w : ℕ, wireVal n C w x = true → wireVal n C w y = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hwx
    by_cases hlt : w < n
    · rw [wireVal_input C w hlt x] at hwx
      rw [wireVal_input C w hlt y]
      exact hxy ⟨w, hlt⟩ hwx
    · by_cases hge : n + C.gates.length ≤ w
      · rw [wireVal_ge C w hge x] at hwx; cases hwx
      · have hj : w - n < C.gates.length := by omega
        have heq : w = n + (w - n) := by omega
        rw [heq] at hwx ⊢
        rw [wireVal_gate_rb hRB hj] at hwx ⊢
        have hop := (hM _ (gateAt_mem hj)).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop
        · rw [hop] at hwx ⊢
          simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq] at hwx ⊢
          intro u hu
          exact ih u (by have := hRB (w - n) hj u hu; omega) (hwx u hu)
        · rw [hop] at hwx ⊢
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hwx ⊢
          obtain ⟨u, hu, hux⟩ := hwx
          exact ⟨u, hu, ih u (by have := hRB (w - n) hj u hu; omega) hux⟩

lemma valid_eval_pairInput_true {C : Circuit} (hV : ValidCirc C) {u v : Fin 26}
    (hadj : pgAdj u v = true) :
    wireVal 26 C C.output (pairInput u v) = true := by
  have h1 : ∀ p l : Fin 13, p ∈ singerLines3 l →
      wireVal 26 C C.output (pairInput ⟨p.val, by omega⟩ ⟨13 + l.val, by omega⟩) = true := by
    intro p l hpl
    unfold wireVal
    rw [ofFn_pair_pt_ln p l]
    exact hV.2.2.1 p l hpl
  unfold pgAdj at hadj
  by_cases h1c : u.val < 13 ∧ 13 ≤ v.val
  · rw [dif_pos h1c, decide_eq_true_eq] at hadj
    have hu : (⟨u.val, by omega⟩ : Fin 26) = u := by ext; rfl
    have hv : (⟨13 + (v.val - 13), by omega⟩ : Fin 26) = v := by ext; simp; omega
    have res := h1 ⟨u.val, h1c.1⟩ ⟨v.val - 13, by omega⟩ hadj
    rwa [hu, hv] at res
  · rw [dif_neg h1c] at hadj
    by_cases h2c : v.val < 13 ∧ 13 ≤ u.val
    · rw [dif_pos h2c, decide_eq_true_eq] at hadj
      have hv : (⟨v.val, by omega⟩ : Fin 26) = v := by ext; rfl
      have hu : (⟨13 + (u.val - 13), by omega⟩ : Fin 26) = u := by ext; simp; omega
      have res := h1 ⟨v.val, h2c.1⟩ ⟨u.val - 13, by omega⟩ hadj
      rw [hv, hu] at res
      have hpeq : pairInput v u = pairInput u v := by
        funext w; simp [pairInput, or_comm]
      rwa [hpeq] at res
    · rw [dif_neg h2c] at hadj; cases hadj

lemma valid_eval_pairInput_false {C : Circuit} (hV : ValidCirc C) {u v : Fin 26}
    (hnadj : pgAdj u v = false) :
    wireVal 26 C C.output (pairInput u v) = false := by
  open PEqualNP.Outside.L_meta_18294.Main in
  have e := (rowAnswer u v).trans ((pgAdj_eq_adjb u v).symm.trans hnadj)
  open PEqualNP.Outside.L_meta_18294.Main in
  have h := hV.2.2.2 (points u v) (lines u v) (Or.inl (pairStar u v)) e
  rw [PEqualNP.Outside.L_meta_18294.Main.pairRow] at h
  exact h

lemma foldl_coneStep_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [coneStep]; omega

lemma foldl_coneStep_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (j : ℕ)
    (hj : j < cs.length) :
    (gs.foldl (coneStep n) cs).getD j [] = cs.getD j [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : j < (coneStep n cs g).length := by simp [coneStep]; omega
    rw [ih (coneStep n cs g) hlt]
    simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

lemma cones_len (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones; rw [foldl_coneStep_len]; simp

lemma cones_getD_eq (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
  unfold cones
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    rw [gateAt_eq hj]
    exact (List.take_append_drop j C.gates).symm.trans (by
      congr 1; exact (List.cons_getElem_drop_succ (h := hj)).symm)
  set pre := (C.gates.take j).foldl (coneStep n) []
  have hpre_len : pre.length = j := by
    rw [foldl_coneStep_len, List.length_nil, zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have heq : C.gates.foldl (coneStep n) [] =
      (C.gates.drop (j + 1)).foldl (coneStep n) (coneStep n pre (gateAt C j)) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hpre_get : ∀ k < j, (C.gates.foldl (coneStep n) []).getD k [] = pre.getD k [] := by
    intro k hk
    rw [heq, foldl_coneStep_getD_lt _ _ _ _ (by simp [coneStep, hpre_len]; omega)]
    simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left (show k < pre.length by omega)]
  conv_lhs => rw [heq, foldl_coneStep_getD_lt _ _ _ _ (by simp [coneStep, hpre_len])]
  conv_lhs => simp only [coneStep, List.getD_eq_getElem?_getD, hpre_len]
  conv_lhs => rw [List.getElem?_append_right (by omega), hpre_len]
  conv_lhs => simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  apply List.flatMap_congr
  intro w hw
  simp only [List.mem_filter, decide_eq_true_eq] at hw
  have hwn : w - n < j := by omega
  have hg := hpre_get (w - n) hwn
  simp only [List.getD_eq_getElem?_getD] at hg ⊢
  congr 1
  exact hg.symm

lemma inCone_gate_iff (n : ℕ) (C : Circuit) (i j : ℕ) (hj : j < C.gates.length) :
    InCone n C i j ↔
      ∃ w ∈ (gateAt C j).inputs, n ≤ w ∧ w < n + j ∧ (i = w - n ∨ InCone n C i (w - n)) := by
  unfold InCone
  rw [cones_getD_eq n C j hj]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hnw, hwn⟩, hmem⟩
    exact ⟨w, hw, hnw, hwn, hmem⟩
  · rintro ⟨w, hw, hnw, hwn, hmem⟩
    exact ⟨w, ⟨hw, hnw, hwn⟩, hmem⟩

lemma inCone_ge_false (n : ℕ) (C : Circuit) (i j : ℕ) (hj : C.gates.length ≤ j) :
    ¬ InCone n C i j := by
  unfold InCone
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [cones_len]; exact hj)]
  simp

lemma inCone_lt (n : ℕ) (C : Circuit) (i j : ℕ) (h : InCone n C i j) : i < j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    by_cases hj : j < C.gates.length
    · rw [inCone_gate_iff n C i j hj] at h
      obtain ⟨w, _, hnw, hwn, rfl | hc⟩ := h
      · omega
      · have := ih (w - n) (by omega) hc; omega
    · exact (inCone_ge_false n C i j (by omega) h).elim

lemma inCone_trans (n : ℕ) (C : Circuit) (a b c : ℕ)
    (hab : InCone n C a b) (hbc : InCone n C b c) : InCone n C a c := by
  induction c using Nat.strong_induction_on with
  | ind c ih =>
    by_cases hc : c < C.gates.length
    · rw [inCone_gate_iff n C b c hc] at hbc
      obtain ⟨w, hw, hnw, hwc, rfl | hbw⟩ := hbc
      · rw [inCone_gate_iff n C a c hc]
        exact ⟨w, hw, hnw, hwc, Or.inr hab⟩
      · rw [inCone_gate_iff n C a c hc]
        exact ⟨w, hw, hnw, hwc, Or.inr (ih (w - n) (by omega) hbw)⟩
    · exact (inCone_ge_false n C b c (by omega) hbc).elim

lemma foldl_orStep_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih => rw [List.foldl_cons, ih]; simp [orStep]; omega

lemma foldl_orStep_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (j : ℕ)
    (hj : j < cs.length) :
    (gs.foldl (orStep n) cs).getD j [] = cs.getD j [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hlt : j < (orStep n cs g).length := by simp [orStep]; omega
    rw [ih (orStep n cs g) hlt]
    simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

lemma orSets_len (n : ℕ) (C : Circuit) : (orSets n C).length = C.gates.length := by
  unfold orSets; rw [foldl_orStep_len]; simp

lemma orSets_getD_eq_or (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hor : (gateAt C j).op = GateOp.or) :
    (orSets n C).getD j [] =
      j :: ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (orSets n C).getD (w - n) []) := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  unfold orSets
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    rw [gateAt_eq hj]
    exact (List.take_append_drop j C.gates).symm.trans (by
      congr 1; exact (List.cons_getElem_drop_succ (h := hj)).symm)
  set pre := (C.gates.take j).foldl (orStep n) []
  have hpre_len : pre.length = j := by
    rw [foldl_orStep_len, List.length_nil, zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have heq : C.gates.foldl (orStep n) [] =
      (C.gates.drop (j + 1)).foldl (orStep n) (orStep n pre (gateAt C j)) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  have hpre_get : ∀ k < j, (C.gates.foldl (orStep n) []).getD k [] = pre.getD k [] := by
    intro k hk
    rw [heq, foldl_orStep_getD_lt _ _ _ _ (by simp [orStep, hpre_len]; omega)]
    simp [orStep, List.getD_eq_getElem?_getD, List.getElem?_append_left (show k < pre.length by omega)]
  conv_lhs => rw [heq, foldl_orStep_getD_lt _ _ _ _ (by simp [orStep, hpre_len])]
  conv_lhs => simp only [orStep, List.getD_eq_getElem?_getD, hpre_len]
  conv_lhs => rw [List.getElem?_append_right (by omega), hpre_len]
  conv_lhs => simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, hor, ↓reduceIte]
  congr 1
  apply List.flatMap_congr
  intro w hw
  simp only [List.mem_filter, decide_eq_true_eq] at hw
  have hg := hpre_get (w - n) (by omega)
  simp only [List.getD_eq_getElem?_getD] at hg ⊢
  exact hg.symm

lemma orSets_getD_eq_ne_or (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (hne : (gateAt C j).op ≠ GateOp.or) :
    (orSets n C).getD j [] = [j] := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  unfold orSets
  have hsplit : C.gates = C.gates.take j ++ gateAt C j :: C.gates.drop (j + 1) := by
    rw [gateAt_eq hj]
    exact (List.take_append_drop j C.gates).symm.trans (by
      congr 1; exact (List.cons_getElem_drop_succ (h := hj)).symm)
  set pre := (C.gates.take j).foldl (orStep n) []
  have hpre_len : pre.length = j := by
    rw [foldl_orStep_len, List.length_nil, zero_add, List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  have heq : C.gates.foldl (orStep n) [] =
      (C.gates.drop (j + 1)).foldl (orStep n) (orStep n pre (gateAt C j)) := by
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_cons]
  rw [heq, foldl_orStep_getD_lt _ _ _ _ (by simp [orStep, hpre_len])]
  simp only [orStep, List.getD_eq_getElem?_getD, hpre_len]
  rw [List.getElem?_append_right (by omega), hpre_len]
  simp only [Nat.sub_self, List.getElem?_cons_zero, Option.getD_some, hne, ↓reduceIte]

lemma orReaches_self (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) :
    OrReaches n C (n + j) j := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  refine ⟨Nat.le_add_right n j, ?_⟩
  rw [Nat.add_sub_cancel_left]
  by_cases hor : (gateAt C j).op = GateOp.or
  · rw [orSets_getD_eq_or n C j hj hor]; exact List.mem_cons_self ..
  · rw [orSets_getD_eq_ne_or n C j hj hor]; exact List.mem_singleton_self j

lemma orReaches_gate_iff (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) (g : ℕ) :
    OrReaches n C (n + j) g ↔
      g = j ∨ ((gateAt C j).op = GateOp.or ∧
        ∃ w ∈ (gateAt C j).inputs, w < n + j ∧ OrReaches n C w g) := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  unfold OrReaches
  simp only [Nat.le_add_right, true_and, Nat.add_sub_cancel_left]
  by_cases hop : (gateAt C j).op = GateOp.or
  · rw [orSets_getD_eq_or n C j hj hop, List.mem_cons]
    simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro (rfl | ⟨w, ⟨hw, hnw, hwn⟩, hmem⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨hop, w, hw, hwn, hnw, hmem⟩
    · rintro (rfl | ⟨_, w, hw, hwn, hnw, hmem⟩)
      · exact Or.inl rfl
      · exact Or.inr ⟨w, ⟨hw, hnw, hwn⟩, hmem⟩
  · rw [orSets_getD_eq_ne_or n C j hj hop, List.mem_singleton]
    constructor
    · intro h; exact Or.inl h
    · rintro (rfl | ⟨h, _⟩); rfl; exact (hop h).elim

lemma orReaches_ge_false (n : ℕ) (C : Circuit) {w : ℕ} (hw : n + C.gates.length ≤ w) (g : ℕ) :
    ¬ OrReaches n C w g := by
  intro ⟨hnw, hmem⟩
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [orSets_len]; omega)] at hmem
  cases hmem

lemma orReaches_le_aux (n : ℕ) (C : Circuit) (j g : ℕ) (hj : j < C.gates.length)
    (h : OrReaches n C (n + j) g) : g ≤ j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [orReaches_gate_iff n C hj g] at h
    rcases h with rfl | ⟨_, u, _, huj, hu⟩
    · exact le_rfl
    · have hu1 := hu.1
      have hlt : u - n < j := by omega
      have h2 := ih (u - n) hlt (by omega) (by rwa [show n + (u - n) = u by omega])
      omega

lemma orReaches_le (n : ℕ) (C : Circuit) (w g : ℕ) (h : OrReaches n C w g) :
    g ≤ w - n ∧ g < C.gates.length := by
  have hnw := h.1
  by_cases hge : n + C.gates.length ≤ w
  · exact (orReaches_ge_false n C hge g h).elim
  · have hj : w - n < C.gates.length := by omega
    have h1 := orReaches_le_aux n C (w - n) g hj (by rwa [show n + (w - n) = w by omega])
    omega

lemma orReaches_imp_inCone_or_eq (n : ℕ) (C : Circuit) {j : ℕ} (hj : j < C.gates.length) (g : ℕ)
    (h : OrReaches n C (n + j) g) : g = j ∨ InCone n C g j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    rw [orReaches_gate_iff n C hj g] at h
    rcases h with rfl | ⟨_, u, hu, huj, hru⟩
    · exact Or.inl rfl
    · right
      have hun := hru.1
      have huk : u - n < j := by omega
      have h1 := ih (u - n) huk (by omega) (by rwa [show n + (u - n) = u by omega])
      rw [inCone_gate_iff n C g j hj]
      exact ⟨u, hu, hun, huj, h1⟩

lemma orReaches_trans_aux (n : ℕ) (C : Circuit) (k j g : ℕ) (hk : k < C.gates.length)
    (h1 : OrReaches n C (n + k) j) (h2 : OrReaches n C (n + j) g) : OrReaches n C (n + k) g := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [orReaches_gate_iff n C hk j] at h1
    rcases h1 with rfl | ⟨hor, u, hu, huk, hru⟩
    · exact h2
    · rw [orReaches_gate_iff n C hk g]
      right
      refine ⟨hor, u, hu, huk, ?_⟩
      have hun := hru.1
      have hres := ih (u - n) (by omega) (by omega) (by rwa [show n + (u - n) = u by omega])
      rwa [show n + (u - n) = u by omega] at hres

lemma orReaches_trans (n : ℕ) (C : Circuit) (w j g : ℕ)
    (h1 : OrReaches n C w j) (h2 : OrReaches n C (n + j) g) : OrReaches n C w g := by
  have hnw := h1.1
  by_cases hge : n + C.gates.length ≤ w
  · exact (orReaches_ge_false n C hge j h1).elim
  · have hk : w - n < C.gates.length := by omega
    have hres := orReaches_trans_aux n C (w - n) j g hk (by rwa [show n + (w - n) = w by omega]) h2
    rwa [show n + (w - n) = w by omega] at hres

lemma wireVal_ge_of_orReaches_aux {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (k g : ℕ) (x : Fin n → Bool)
    (hk : k < C.gates.length) (hr : OrReaches n C (n + k) g) (hg : gateVal n C g x = true) :
    wireVal n C (n + k) x = true := by
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    rw [orReaches_gate_iff n C hk g] at hr
    rcases hr with rfl | ⟨hor, u, hu, huk, hru⟩
    · exact hg
    · rw [wireVal_gate_rb hRB hk, hor]
      simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
      have hun := hru.1
      have hval := ih (u - n) (by omega) (by omega) (by rwa [show n + (u - n) = u by omega])
      rw [show n + (u - n) = u by omega] at hval
      exact ⟨u, hu, hval⟩

lemma wireVal_ge_of_orReaches {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (w g : ℕ) (x : Fin n → Bool)
    (hr : OrReaches n C w g) (hg : gateVal n C g x = true) : wireVal n C w x = true := by
  have hnw := hr.1
  by_cases hge : n + C.gates.length ≤ w
  · exact (orReaches_ge_false n C hge g hr).elim
  · have hk : w - n < C.gates.length := by omega
    have hres := wireVal_ge_of_orReaches_aux hRB (w - n) g x hk (by rwa [show n + (w - n) = w by omega]) hg
    rwa [show n + (w - n) = w by omega] at hres

lemma orIn_input {n : ℕ} (C : Circuit) {w : ℕ} (hw : w < n) (v : Fin n) :
    v ∈ orIn n C w ↔ (v : ℕ) = w := by
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨_, _, hr, _, _⟩)
    · exact h
    · have := hr.1; omega
  · exact Or.inl

lemma orIn_gate_and {n : ℕ} (C : Circuit) {j : ℕ} (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) :
    orIn n C (n + j) = ∅ := by
  ext v
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false,
    not_or, not_exists, not_and]
  refine ⟨by omega, fun k _ hr hor _ => ?_⟩
  rw [orReaches_gate_iff n C hj k] at hr
  rcases hr with rfl | ⟨h, _⟩
  · rw [hand] at hor; cases hor
  · rw [hand] at h; cases h

lemma orIn_gate_or_rb {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {j : ℕ} (hj : j < C.gates.length)
    (hor : (gateAt C j).op = GateOp.or) (v : Fin n) :
    v ∈ orIn n C (n + j) ↔ ∃ w ∈ (gateAt C j).inputs, v ∈ orIn n C w := by
  unfold orIn
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro (h | ⟨k, hk, hr, hkor, hvk⟩)
    · omega
    · rw [orReaches_gate_iff n C hj k] at hr
      rcases hr with rfl | ⟨_, w, hw, _, hwk⟩
      · exact ⟨v.val, hvk, Or.inl rfl⟩
      · exact ⟨w, hw, Or.inr ⟨k, hk, hwk, hkor, hvk⟩⟩
  · rintro ⟨w, hw, heq | ⟨k, hk, hwk, hkor, hvk⟩⟩
    · right
      refine ⟨j, hj, orReaches_self n C hj, hor, ?_⟩
      rwa [heq]
    · right
      refine ⟨k, hk, ?_, hkor, hvk⟩
      rw [orReaches_gate_iff n C hj k]
      exact Or.inr ⟨hor, w, hw, hRB j hj w hw, hwk⟩

lemma orIn_mono_of_orReaches {n : ℕ} (C : Circuit) (w j : ℕ) (hr : OrReaches n C w j) :
    orIn n C (n + j) ⊆ orIn n C w := by
  intro v hv
  unfold orIn at hv ⊢
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
  rcases hv with h | ⟨k, hk, hjk, hkor, hvk⟩
  · omega
  · exact Or.inr ⟨k, hk, orReaches_trans n C w j k hr hjk, hkor, hvk⟩

lemma wireVal_ge_of_orIn {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) (w : ℕ) (v : Fin n)
    (x : Fin n → Bool) (hv : v ∈ orIn n C w) (hx : x v = true) :
    wireVal n C w x = true := by
  unfold orIn at hv
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
  rcases hv with heq | ⟨k, hk, hwk, hkor, hvk⟩
  · rw [← heq, wireVal_input C v.val v.isLt x]; exact hx
  · apply wireVal_ge_of_orReaches hRB w k x hwk
    change wireVal n C (n + k) x = true
    rw [wireVal_gate_rb hRB hk, hkor]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    exact ⟨v.val, hvk, by rw [wireVal_input C v.val v.isLt x]; exact hx⟩

lemma wireVal_eq_orIn_or_i {n : ℕ} {C : Circuit} (hM : Monotone2 C) (hRB : ReadsBack n C)
    (i : ℕ) (w : ℕ) (hw : w < n + C.gates.length)
    (honly : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → OrReaches n C w a → a = i)
    (x : Fin n → Bool) :
    wireVal n C w x = true ↔
      (OrReaches n C w i ∧ gateVal n C i x = true) ∨ ∃ v ∈ orIn n C w, x v = true := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    constructor
    · intro hval
      by_cases hwn : w < n
      · right
        refine ⟨⟨w, hwn⟩, (orIn_input C hwn _).mpr rfl, ?_⟩
        rwa [wireVal_input C w hwn x] at hval
      · set k := w - n
        have hk : k < C.gates.length := by omega
        have hwk : w = n + k := by omega
        rw [hwk] at hval honly ⊢
        have hop := (hM _ (gateAt_mem hk)).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hand | hor
        · have hki : k = i := honly k hk hand (orReaches_self n C hk)
          subst hki
          exact Or.inl ⟨orReaches_self n C hk, hval⟩
        · rw [wireVal_gate_rb hRB hk, hor] at hval
          simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq] at hval
          obtain ⟨u, hu, hux⟩ := hval
          have hult := hRB k hk u hu
          have honly_u : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → OrReaches n C u a → a = i := by
            intro a ha haand hru
            apply honly a ha haand
            rw [orReaches_gate_iff n C hk a]
            exact Or.inr ⟨hor, u, hu, hult, hru⟩
          have hres := (ih u (by omega) (by omega) honly_u).mp hux
          rcases hres with ⟨hrui, hi⟩ | ⟨v, hvu, hvx⟩
          · left
            refine ⟨?_, hi⟩
            rw [orReaches_gate_iff n C hk i]
            exact Or.inr ⟨hor, u, hu, hult, hrui⟩
          · right
            exact ⟨v, (orIn_gate_or_rb hRB hk hor v).mpr ⟨u, hu, hvu⟩, hvx⟩
    · rintro (⟨hri, hi⟩ | ⟨v, hv, hvx⟩)
      · exact wireVal_ge_of_orReaches hRB w i x hri hi
      · exact wireVal_ge_of_orIn hRB w v x hv hvx

lemma eraseGate_len (n : ℕ) (C : Circuit) (m p : ℕ) (hm : m < C.gates.length) :
    (eraseGate n C m p).gates.length = C.gates.length - 1 := by
  unfold eraseGate
  simp only [hm, ↓reduceIte, List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

lemma eraseGate_gateAt_lt (n : ℕ) (C : Circuit) (m p j : ℕ) (hm : m < C.gates.length) (hj : j < m) :
    gateAt (eraseGate n C m p) j = gateAt C j := by
  unfold gateAt eraseGate
  simp only [hm, ↓reduceIte, List.getD_eq_getElem?_getD]
  have htl : j < (C.gates.take m).length := by simp; omega
  rw [List.getElem?_append_left htl, List.getElem?_take_of_lt hj]

lemma eraseGate_gateAt_ge (n : ℕ) (C : Circuit) (m p j : ℕ) (hm : m < C.gates.length)
    (hj1 : m ≤ j) (hj2 : j + 1 < C.gates.length) :
    gateAt (eraseGate n C m p) j =
      ⟨(gateAt C (j + 1)).op, (gateAt C (j + 1)).inputs.map (eraseRedirect n m p)⟩ := by
  unfold gateAt eraseGate
  simp only [hm, ↓reduceIte, List.getD_eq_getElem?_getD]
  have htl : (C.gates.take m).length = m := by simp; omega
  rw [List.getElem?_append_right (by omega), htl, List.getElem?_map, List.getElem?_drop]
  have heq : m + 1 + (j - m) = j + 1 := by omega
  rw [heq, List.getElem?_eq_getElem hj2]
  simp

lemma eraseGate_monotone2 {n : ℕ} {C : Circuit} (hM : Monotone2 C) {m p : ℕ}
    (hm : m < C.gates.length) : Monotone2 (eraseGate n C m p) := by
  have hlen := eraseGate_len n C m p hm
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
  rw [← gateAt_eq hj]
  by_cases hjm : j < m
  · rw [eraseGate_gateAt_lt n C m p j hm hjm]
    exact hM _ (gateAt_mem (by omega))
  · rw [eraseGate_gateAt_ge n C m p j hm (by omega) (by omega)]
    have hm1 := hM _ (gateAt_mem (show j + 1 < C.gates.length by omega))
    exact ⟨hm1.1, by simp [hm1.2]⟩

lemma eraseGate_readsBack {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {m p : ℕ}
    (hm : m < C.gates.length) (hp : p < n + m) : ReadsBack n (eraseGate n C m p) := by
  have hlen := eraseGate_len n C m p hm
  intro j hj i hi
  by_cases hjm : j < m
  · rw [eraseGate_gateAt_lt n C m p j hm hjm] at hi
    exact hRB j (by omega) i hi
  · rw [eraseGate_gateAt_ge n C m p j hm (by omega) (by omega)] at hi
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hi
    have hult := hRB (j + 1) (by omega) u hu
    unfold eraseRedirect
    split_ifs <;> omega

lemma eraseGate_wireVal_eq {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {m p : ℕ}
    (hm : m < C.gates.length) (hp : p < n + m) (x : Fin n → Bool)
    (heq_mp : wireVal n C (n + m) x = wireVal n C p x) :
    ∀ w < n + C.gates.length,
      wireVal n (eraseGate n C m p) (eraseRedirect n m p w) x = wireVal n C w x := by
  have hRB' := eraseGate_readsBack hRB hm hp
  have hlen := eraseGate_len n C m p hm
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw
    by_cases hwn : w < n
    · have hred : eraseRedirect n m p w = w := by unfold eraseRedirect; split_ifs <;> omega
      rw [hred, wireVal_input _ w hwn, wireVal_input _ w hwn]
    · set j := w - n
      have hwj : w = n + j := by omega
      have hj : j < C.gates.length := by omega
      by_cases hjm : j < m
      · have hred : eraseRedirect n m p w = n + j := by unfold eraseRedirect; split_ifs <;> omega
        rw [hred, hwj]
        have hj' : j < (eraseGate n C m p).gates.length := by omega
        rw [wireVal_gate_rb hRB' hj', wireVal_gate_rb hRB hj, eraseGate_gateAt_lt n C m p j hm hjm]
        congr 1
        apply List.map_congr_left
        intro u hu
        have hult := hRB j hj u hu
        have hured : eraseRedirect n m p u = u := by unfold eraseRedirect; split_ifs <;> omega
        have := ih u (by omega) (by omega)
        rwa [hured] at this
      · by_cases heqm : j = m
        · have hw_eq : w = n + m := by omega
          have hred : eraseRedirect n m p w = p := by unfold eraseRedirect; simp [hw_eq]
          rw [hred, hw_eq, heq_mp]
          have hpred : eraseRedirect n m p p = p := by unfold eraseRedirect; split_ifs <;> omega
          have := ih p (by omega) (by omega)
          rwa [hpred] at this
        · have hgt : m < j := by omega
          have hred : eraseRedirect n m p w = n + (j - 1) := by unfold eraseRedirect; split_ifs <;> omega
          rw [hred, hwj]
          have hj' : j - 1 < (eraseGate n C m p).gates.length := by omega
          rw [wireVal_gate_rb hRB' hj', wireVal_gate_rb hRB hj,
            eraseGate_gateAt_ge n C m p (j - 1) hm (by omega) (by omega)]
          have hj1 : j - 1 + 1 = j := by omega
          rw [hj1]
          simp only [List.map_map]
          congr 1
          apply List.map_congr_left
          intro u hu
          have hult := hRB j hj u hu
          exact ih u (by omega) (by omega)

lemma min_no_eq_wire {C : Circuit} (hMin : IsMin C) {m p : ℕ}
    (hm : m < C.gates.length) (hp : p < 26 + m)
    (heq : ∀ x : Fin 26 → Bool, wireVal 26 C (26 + m) x = wireVal 26 C p x) : False := by
  have hV := hMin.1
  set C' := eraseGate 26 C m p
  have hlen : C'.gates.length = C.gates.length - 1 := eraseGate_len 26 C m p hm
  have hout_C' : C'.output = eraseRedirect 26 m p C.output := by
    simp only [C', eraseGate, hm, ↓reduceIte]
  have heval : ∀ x : Fin 26 → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    intro x
    change wireVal 26 C' C'.output x = wireVal 26 C C.output x
    rw [hout_C']
    by_cases hout : C.output < 26 + C.gates.length
    · exact eraseGate_wireVal_eq hV.2.1 hm hp x (heq x) C.output hout
    · have hout' : 26 + C'.gates.length ≤ eraseRedirect 26 m p C.output := by
        unfold eraseRedirect; split_ifs <;> omega
      rw [wireVal_ge C' _ hout', wireVal_ge C _ (by omega)]
  have hV' : ValidCirc C' := by
    refine ⟨eraseGate_monotone2 hV.1 hm, eraseGate_readsBack hV.2.1 hm hp, ?_, ?_⟩
    · intro a l hal
      rw [← ofFn_pair_pt_ln a l, heval, ofFn_pair_pt_ln a l]
      exact hV.2.2.1 a l hal
    · intro X Y hs hn
      rw [heval]
      exact hV.2.2.2 X Y hs hn
  have hle : C.gates.length ≤ C'.gates.length := hMin.2 C' hV'
  omega

def shiftDown (n m w : ℕ) : ℕ :=
  if n + m < w then w - 1 else w

def substConstGate (n m : ℕ) (b : Bool) (g : Gate) : Gate :=
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  match b with
  | false =>
    if g.op = GateOp.or then
      ⟨GateOp.or, (g.inputs.filter (fun w => decide (w ≠ n + m))).map (shiftDown n m)⟩
    else if n + m ∈ g.inputs then
      ⟨GateOp.or, []⟩
    else
      ⟨g.op, g.inputs.map (shiftDown n m)⟩
  | true =>
    if g.op = GateOp.and then
      ⟨GateOp.and, (g.inputs.filter (fun w => decide (w ≠ n + m))).map (shiftDown n m)⟩
    else if n + m ∈ g.inputs then
      ⟨GateOp.and, []⟩
    else
      ⟨g.op, g.inputs.map (shiftDown n m)⟩

def deleteConstGate (n : ℕ) (C : Circuit) (m : ℕ) (b : Bool) : Circuit :=
  { gates := C.gates.take m ++ (C.gates.drop (m + 1)).map (substConstGate n m b)
    output := shiftDown n m C.output }

lemma deleteConstGate_len (n : ℕ) (C : Circuit) (m : ℕ) (b : Bool) (hm : m < C.gates.length) :
    (deleteConstGate n C m b).gates.length = C.gates.length - 1 := by
  unfold deleteConstGate
  simp only [List.length_append, List.length_take, List.length_map, List.length_drop]
  omega

lemma deleteConstGate_gateAt_lt (n : ℕ) (C : Circuit) (m : ℕ) (b : Bool) (j : ℕ)
    (hm : m < C.gates.length) (hj : j < m) :
    gateAt (deleteConstGate n C m b) j = gateAt C j := by
  unfold gateAt deleteConstGate
  simp only [List.getD_eq_getElem?_getD]
  have htl : j < (C.gates.take m).length := by simp; omega
  rw [List.getElem?_append_left htl, List.getElem?_take_of_lt hj]

lemma deleteConstGate_gateAt_ge (n : ℕ) (C : Circuit) (m : ℕ) (b : Bool) (j : ℕ)
    (hm : m < C.gates.length) (hj1 : m ≤ j) (hj2 : j + 1 < C.gates.length) :
    gateAt (deleteConstGate n C m b) j = substConstGate n m b (gateAt C (j + 1)) := by
  unfold gateAt deleteConstGate
  simp only [List.getD_eq_getElem?_getD]
  have htl : (C.gates.take m).length = m := by simp; omega
  rw [List.getElem?_append_right (by omega), htl, List.getElem?_map, List.getElem?_drop]
  have heq : m + 1 + (j - m) = j + 1 := by omega
  rw [heq, List.getElem?_eq_getElem hj2]
  simp

lemma deleteConstGate_monotone2 {n : ℕ} {C : Circuit} (hM : Monotone2 C) {m : ℕ} (b : Bool)
    (hm : m < C.gates.length) : Monotone2 (deleteConstGate n C m b) := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have hlen := deleteConstGate_len n C m b hm
  intro g hg
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp hg
  rw [← gateAt_eq hj]
  by_cases hjm : j < m
  · rw [deleteConstGate_gateAt_lt n C m b j hm hjm]
    exact hM _ (gateAt_mem (by omega))
  · rw [deleteConstGate_gateAt_ge n C m b j hm (by omega) (by omega)]
    have hm1 := hM _ (gateAt_mem (show j + 1 < C.gates.length by omega))
    unfold substConstGate
    cases b <;> dsimp only <;> split_ifs
    · refine ⟨by simp, ?_⟩
      simp only [List.length_map]
      exact (List.length_filter_le _ _).trans hm1.2
    · exact ⟨by simp, by simp⟩
    · exact ⟨hm1.1, by simp [hm1.2]⟩
    · refine ⟨by simp, ?_⟩
      simp only [List.length_map]
      exact (List.length_filter_le _ _).trans hm1.2
    · exact ⟨by simp, by simp⟩
    · exact ⟨hm1.1, by simp [hm1.2]⟩

lemma deleteConstGate_readsBack {n : ℕ} {C : Circuit} (hRB : ReadsBack n C) {m : ℕ} (b : Bool)
    (hm : m < C.gates.length) : ReadsBack n (deleteConstGate n C m b) := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have hlen := deleteConstGate_len n C m b hm
  intro j hj i hi
  by_cases hjm : j < m
  · rw [deleteConstGate_gateAt_lt n C m b j hm hjm] at hi
    exact hRB j (by omega) i hi
  · rw [deleteConstGate_gateAt_ge n C m b j hm (by omega) (by omega)] at hi
    unfold substConstGate at hi
    cases b <;> dsimp only at hi <;> split_ifs at hi
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hi
      simp only [List.mem_filter, decide_eq_true_eq] at hu
      have hult := hRB (j + 1) (by omega) u hu.1
      unfold shiftDown; split_ifs <;> omega
    · cases hi
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hi
      have hult := hRB (j + 1) (by omega) u hu
      have hne : u ≠ n + m := fun h => by subst h; contradiction
      unfold shiftDown; split_ifs <;> omega
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hi
      simp only [List.mem_filter, decide_eq_true_eq] at hu
      have hult := hRB (j + 1) (by omega) u hu.1
      unfold shiftDown; split_ifs <;> omega
    · cases hi
    · obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hi
      have hult := hRB (j + 1) (by omega) u hu
      have hne : u ≠ n + m := fun h => by subst h; contradiction
      unfold shiftDown; split_ifs <;> omega

lemma deleteConstGate_wireVal_eq {n : ℕ} {C : Circuit} (hM : Monotone2 C) (hRB : ReadsBack n C)
    {m : ℕ} (b : Bool) (hm : m < C.gates.length) (x : Fin n → Bool)
    (hconst : wireVal n C (n + m) x = b) :
    ∀ w < n + C.gates.length, w ≠ n + m →
      wireVal n (deleteConstGate n C m b) (shiftDown n m w) x = wireVal n C w x := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have hRB' := deleteConstGate_readsBack hRB b hm
  have hlen := deleteConstGate_len n C m b hm
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hne
    by_cases hwn : w < n
    · have hs : shiftDown n m w = w := by unfold shiftDown; split_ifs <;> omega
      rw [hs, wireVal_input _ w hwn, wireVal_input _ w hwn]
    · set j := w - n
      have hwj : w = n + j := by omega
      have hj : j < C.gates.length := by omega
      have hjm_ne : j ≠ m := by omega
      by_cases hjm : j < m
      · have hs : shiftDown n m w = n + j := by unfold shiftDown; split_ifs <;> omega
        rw [hs, hwj]
        have hj' : j < (deleteConstGate n C m b).gates.length := by omega
        rw [wireVal_gate_rb hRB' hj', wireVal_gate_rb hRB hj, deleteConstGate_gateAt_lt n C m b j hm hjm]
        congr 1
        apply List.map_congr_left
        intro u hu
        have hult := hRB j hj u hu
        have hus : shiftDown n m u = u := by unfold shiftDown; split_ifs <;> omega
        have := ih u (by omega) (by omega) (by omega)
        rwa [hus] at this
      · have hgt : m < j := by omega
        have hs : shiftDown n m w = n + (j - 1) := by unfold shiftDown; split_ifs <;> omega
        rw [hs, hwj]
        have hj' : j - 1 < (deleteConstGate n C m b).gates.length := by omega
        rw [wireVal_gate_rb hRB' hj', wireVal_gate_rb hRB hj,
          deleteConstGate_gateAt_ge n C m b (j - 1) hm (by omega) (by omega)]
        have hj1 : j - 1 + 1 = j := by omega
        rw [hj1]
        have hop := (hM _ (gateAt_mem hj)).1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        unfold substConstGate
        cases b
        ·
          dsimp only
          split_ifs with hor hmem
          · rw [hor]
            simp only [GateOp.eval, List.map_map, List.any_map, List.any_filter, Function.comp_apply, id_eq]
            apply Bool.eq_iff_iff.mpr
            simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
            constructor
            · rintro ⟨u, hu, hune, hval⟩
              have hult := hRB j hj u hu
              rw [ih u (by omega) (by omega) hune] at hval
              exact ⟨u, hu, hval⟩
            · rintro ⟨u, hu, hval⟩
              have hult := hRB j hj u hu
              have hune : u ≠ n + m := by
                intro heq; subst heq; dsimp only [Function.comp_apply, id_eq] at hval; rw [hconst] at hval; cases hval
              exact ⟨u, hu, hune, by rwa [ih u (by omega) (by omega) hune]⟩
          · rcases hop with hand | hor'
            · rw [hand]
              simp only [GateOp.eval, List.map_nil, List.any_nil]
              symm
              rw [List.all_eq_false]
              exact ⟨false, List.mem_map.mpr ⟨n + m, hmem, hconst⟩, by simp⟩
            · exact (hor hor').elim
          · simp only [List.map_map]
            congr 1
            apply List.map_congr_left
            intro u hu
            have hult := hRB j hj u hu
            have hune : u ≠ n + m := fun h => hmem (h ▸ hu)
            exact ih u (by omega) (by omega) hune
        ·
          dsimp only
          split_ifs with hand hmem
          · rw [hand]
            simp only [GateOp.eval, List.map_map, List.all_map, List.all_filter, Function.comp_apply, id_eq]
            apply Bool.eq_iff_iff.mpr
            simp only [List.all_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not,
              not_not]
            constructor
            · intro hall u hu
              have hult := hRB j hj u hu
              by_cases hune : u = n + m
              · subst hune; exact hconst
              · have h1 := hall u hu
                rcases h1 with heq | hval
                · exact (hune heq).elim
                · rwa [ih u (by omega) (by omega) hune] at hval
            · intro hall u hu
              by_cases hune : u = n + m
              · exact Or.inl hune
              · right
                have hult := hRB j hj u hu
                rw [ih u (by omega) (by omega) hune]
                exact hall u hu
          · rcases hop with hand' | hor
            · exact (hand hand').elim
            · rw [hor]
              simp only [GateOp.eval, List.map_nil, List.all_nil]
              symm
              rw [List.any_eq_true]
              exact ⟨true, List.mem_map.mpr ⟨n + m, hmem, hconst⟩, by simp⟩
          · simp only [List.map_map]
            congr 1
            apply List.map_congr_left
            intro u hu
            have hult := hRB j hj u hu
            have hune : u ≠ n + m := fun h => hmem (h ▸ hu)
            exact ih u (by omega) (by omega) hune

lemma deleteConstGate_wireVal_not_inCone {n : ℕ} {C : Circuit} (hM : Monotone2 C) (hRB : ReadsBack n C)
    {m : ℕ} (hm : m < C.gates.length) (x : Fin n → Bool) :
    ∀ w < n + C.gates.length, w ≠ n + m → (∀ j, w = n + j → ¬ InCone n C m j) →
      wireVal n (deleteConstGate n C m false) (shiftDown n m w) x = wireVal n C w x := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have hRB' := deleteConstGate_readsBack hRB false hm
  have hlen := deleteConstGate_len n C m false hm
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hne hnc
    by_cases hwn : w < n
    · have hs : shiftDown n m w = w := by unfold shiftDown; split_ifs <;> omega
      rw [hs, wireVal_input _ w hwn, wireVal_input _ w hwn]
    · set j := w - n
      have hwj : w = n + j := by omega
      have hj : j < C.gates.length := by omega
      have hncj : ¬ InCone n C m j := hnc j hwj
      have hnotmem : n + m ∉ (gateAt C j).inputs := by
        intro hmem
        apply hncj
        rw [inCone_gate_iff n C m j hj]
        exact ⟨n + m, hmem, Nat.le_add_right n m, hRB j hj (n + m) hmem, Or.inl (by omega)⟩
      have hsub_nc : ∀ u ∈ (gateAt C j).inputs, u ≠ n + m ∧ ∀ k, u = n + k → ¬ InCone n C m k := by
        intro u hu
        refine ⟨fun h => hnotmem (h ▸ hu), fun k huk hmk => hncj ?_⟩
        rw [inCone_gate_iff n C m j hj]
        exact ⟨u, hu, by omega, hRB j hj u hu, Or.inr (by rwa [huk, Nat.add_sub_cancel_left])⟩
      by_cases hjm : j < m
      · have hs : shiftDown n m w = n + j := by unfold shiftDown; split_ifs <;> omega
        rw [hs, hwj]
        have hj' : j < (deleteConstGate n C m false).gates.length := by omega
        rw [wireVal_gate_rb hRB' hj', wireVal_gate_rb hRB hj, deleteConstGate_gateAt_lt n C m false j hm hjm]
        congr 1
        apply List.map_congr_left
        intro u hu
        have hult := hRB j hj u hu
        have hus : shiftDown n m u = u := by unfold shiftDown; split_ifs <;> omega
        have := ih u (by omega) (by omega) (hsub_nc u hu).1 (hsub_nc u hu).2
        rwa [hus] at this
      · have hgt : m < j := by omega
        have hs : shiftDown n m w = n + (j - 1) := by unfold shiftDown; split_ifs <;> omega
        rw [hs, hwj]
        have hj' : j - 1 < (deleteConstGate n C m false).gates.length := by omega
        rw [wireVal_gate_rb hRB' hj', wireVal_gate_rb hRB hj,
          deleteConstGate_gateAt_ge n C m false (j - 1) hm (by omega) (by omega)]
        have hj1 : j - 1 + 1 = j := by omega
        rw [hj1]
        unfold substConstGate
        dsimp only
        split_ifs with hor
        · rw [hor]
          have hfilt : (gateAt C j).inputs.filter (fun u => decide (u ≠ n + m)) = (gateAt C j).inputs := by
            rw [List.filter_eq_self]
            intro u hu; simp [(hsub_nc u hu).1]
          rw [hfilt, List.map_map]
          congr 1
          apply List.map_congr_left
          intro u hu
          have hult := hRB j hj u hu
          exact ih u (by omega) (by omega) (hsub_nc u hu).1 (hsub_nc u hu).2
        · simp only [List.map_map]
          congr 1
          apply List.map_congr_left
          intro u hu
          have hult := hRB j hj u hu
          exact ih u (by omega) (by omega) (hsub_nc u hu).1 (hsub_nc u hu).2

lemma min_output_bounds {C : Circuit} (hV : ValidCirc C) :
    26 ≤ C.output ∧ C.output < 26 + C.gates.length := by
  constructor
  · by_contra hlt
    push_neg at hlt
    have hf := valid_eval_pairInput_false hV (pgAdj_irrefl ⟨C.output, hlt⟩)
    rw [wireVal_input C C.output hlt] at hf
    simp [pairInput] at hf
  · by_contra hge
    push_neg at hge
    have ht := valid_eval_pairInput_true hV (u := (0 : Fin 26)) (v := (13 : Fin 26)) (by decide)
    rw [wireVal_ge C C.output hge] at ht
    cases ht

lemma min_no_const_gate {C : Circuit} (hMin : IsMin C) {m : ℕ} (hm : m < C.gates.length) (b : Bool)
    (hconst : ∀ x : Fin 26 → Bool, wireVal 26 C (26 + m) x = b) : False := by
  have hV := hMin.1
  have hne_out : C.output ≠ 26 + m := by
    intro heq
    cases b
    · have ht := valid_eval_pairInput_true hV (u := (0 : Fin 26)) (v := (13 : Fin 26)) (by decide)
      rw [heq, hconst] at ht; cases ht
    · have hf := valid_eval_pairInput_false hV (pgAdj_irrefl (0 : Fin 26))
      rw [heq, hconst] at hf; cases hf
  have hout := min_output_bounds hV
  set C' := deleteConstGate 26 C m b
  have hlen : C'.gates.length = C.gates.length - 1 := deleteConstGate_len 26 C m b hm
  have heval : ∀ x : Fin 26 → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := fun x =>
    deleteConstGate_wireVal_eq hV.1 hV.2.1 b hm x (hconst x) C.output hout.2 hne_out
  have hV' : ValidCirc C' := by
    refine ⟨deleteConstGate_monotone2 hV.1 b hm, deleteConstGate_readsBack hV.2.1 b hm, ?_, ?_⟩
    · intro a l hal
      rw [← ofFn_pair_pt_ln a l, heval, ofFn_pair_pt_ln a l]; exact hV.2.2.1 a l hal
    · intro X Y hs hn
      rw [heval]
      exact hV.2.2.2 X Y hs hn
  have hle : C.gates.length ≤ C'.gates.length := hMin.2 C' hV'
  omega

lemma min_in_output_cone {C : Circuit} (hMin : IsMin C) {m : ℕ} (hm : m < C.gates.length) :
    m = C.output - 26 ∨ InCone 26 C m (C.output - 26) := by
  by_contra h
  push_neg at h
  have hV := hMin.1
  have hout := min_output_bounds hV
  have hne_out : C.output ≠ 26 + m := by omega
  set C' := deleteConstGate 26 C m false
  have hlen : C'.gates.length = C.gates.length - 1 := deleteConstGate_len 26 C m false hm
  have heval : ∀ x : Fin 26 → Bool, C'.eval (List.ofFn x) = C.eval (List.ofFn x) := by
    intro x
    apply deleteConstGate_wireVal_not_inCone hV.1 hV.2.1 hm x C.output hout.2 hne_out
    intro k hk
    have : k = C.output - 26 := by omega
    rw [this]; exact h.2
  have hV' : ValidCirc C' := by
    refine ⟨deleteConstGate_monotone2 hV.1 false hm, deleteConstGate_readsBack hV.2.1 false hm, ?_, ?_⟩
    · intro a l hal
      rw [← ofFn_pair_pt_ln a l, heval, ofFn_pair_pt_ln a l]; exact hV.2.2.1 a l hal
    · intro X Y hs hn
      rw [heval]
      exact hV.2.2.2 X Y hs hn
  have hle : C.gates.length ≤ C'.gates.length := hMin.2 C' hV'
  omega

lemma min_isAO2 {C : Circuit} (hMin : IsMin C) : IsAO2 26 C := by
  have hV := hMin.1
  refine ⟨?_, hV.2.1, ?_⟩
  · intro g hg
    have h := (hV.1 g hg).1
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using h
  · intro g hg
    obtain ⟨m, hm, rfl⟩ := List.mem_iff_getElem.mp hg
    rw [← gateAt_eq hm]
    have hle := (hV.1 _ (gateAt_mem hm)).2
    have hop := (hV.1 _ (gateAt_mem hm)).1
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
    cases hl : (gateAt C m).inputs with
    | nil =>
      exfalso
      rcases hop with hand | hor
      · apply min_no_const_gate hMin hm true
        intro x; rw [wireVal_gate_rb hV.2.1 hm, hand, hl]; rfl
      · apply min_no_const_gate hMin hm false
        intro x; rw [wireVal_gate_rb hV.2.1 hm, hor, hl]; rfl
    | cons u rest =>
      cases rest with
      | nil =>
        exfalso
        have hult : u < 26 + m := hV.2.1 m hm u (by rw [hl]; simp)
        apply min_no_eq_wire hMin hm hult
        intro x
        rw [wireVal_gate_rb hV.2.1 hm, hl]
        rcases hop with hand | hor
        · simp [hand, GateOp.eval]
        · simp [hor, GateOp.eval]
      | cons v rest' =>
        cases rest' with
        | nil => rfl
        | cons _ _ => rw [hl] at hle; simp at hle

lemma min_opnd_ne {C : Circuit} (hMin : IsMin C) {m : ℕ} (hm : m < C.gates.length) :
    opnd C m 0 ≠ opnd C m 1 := by
  intro heq
  have hAO := min_isAO2 hMin
  have hlen : (gateAt C m).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hm)
  have hinp : (gateAt C m).inputs = [opnd C m 0, opnd C m 1] := by
    unfold opnd
    cases hl : (gateAt C m).inputs with
    | nil => simp [hl] at hlen
    | cons a l =>
      cases l with
      | nil => simp [hl] at hlen
      | cons b l' =>
        cases l' with
        | nil => simp
        | cons _ _ => simp [hl] at hlen
  have h0lt : opnd C m 0 < 26 + m := hMin.1.2.1 m hm (opnd C m 0) (by rw [hinp]; simp)
  apply min_no_eq_wire hMin hm h0lt
  intro x
  rw [wireVal_gate_rb hMin.1.2.1 hm, hinp, heq]
  rcases hAO.1 _ (gateAt_mem hm) with hand | hor
  · simp [hand, GateOp.eval]
  · simp [hor, GateOp.eval]

lemma gate_inputs_eq {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] := by
  have hlen : (gateAt C j).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hj)
  unfold opnd
  cases hl : (gateAt C j).inputs with
  | nil => simp [hl] at hlen
  | cons a l =>
    cases l with
    | nil => simp [hl] at hlen
    | cons b l' =>
      cases l' with
      | nil => simp
      | cons _ _ => simp [hl] at hlen

lemma opnd_mem {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b ∈ (gateAt C j).inputs := by
  rw [gate_inputs_eq hAO hj]; fin_cases b <;> simp

lemma opnd_lt {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length) (b : Fin 2) :
    opnd C j b < n + j :=
  hAO.2.1 j hj (opnd C j b) (opnd_mem hAO hj b)

lemma wireVal_gate_and {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hand : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
    wireVal n C (n + j) x = (wireVal n C (opnd C j 0) x && wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate_rb hAO.2.1 hj, gate_inputs_eq hAO hj, hand]
  simp [GateOp.eval]

lemma wireVal_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hor : (gateAt C j).op = GateOp.or) (x : Fin n → Bool) :
    wireVal n C (n + j) x = (wireVal n C (opnd C j 0) x || wireVal n C (opnd C j 1) x) := by
  rw [wireVal_gate_rb hAO.2.1 hj, gate_inputs_eq hAO hj, hor]
  simp [GateOp.eval]

lemma orIn_gate_or {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hor : (gateAt C j).op = GateOp.or) :
    orIn n C (n + j) = orIn n C (opnd C j 0) ∪ orIn n C (opnd C j 1) := by
  ext v
  rw [orIn_gate_or_rb hAO.2.1 hj hor, gate_inputs_eq hAO hj]
  simp

lemma orReaches_gate_or_iff {n : ℕ} {C : Circuit} (hAO : IsAO2 n C) {j : ℕ} (hj : j < C.gates.length)
    (hor : (gateAt C j).op = GateOp.or) {g : ℕ} (hne : g ≠ j) :
    OrReaches n C (n + j) g ↔ OrReaches n C (opnd C j 0) g ∨ OrReaches n C (opnd C j 1) g := by
  rw [orReaches_gate_iff n C hj g, gate_inputs_eq hAO hj]
  have h0 := opnd_lt hAO hj 0
  have h1 := opnd_lt hAO hj 1
  simp [hne, hor, h0, h1]

lemma min_pure_or_card_ge_two {C : Circuit} (hMin : IsMin C) {h : ℕ} (hh : h < C.gates.length)
    (hor : (gateAt C h).op = GateOp.or)
    (hpure : ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → ¬ OrReaches 26 C (26 + h) a) :
    2 ≤ (orIn 26 C (26 + h)).card := by
  have hval : ∀ x : Fin 26 → Bool, wireVal 26 C (26 + h) x = true ↔ ∃ v ∈ orIn 26 C (26 + h), x v = true := by
    intro x
    have h1 := wireVal_eq_orIn_or_i hMin.1.1 hMin.1.2.1 C.gates.length (26 + h) (by omega)
      (fun a ha haand hru => (hpure a ha haand hru).elim) x
    have h2 : ¬ OrReaches 26 C (26 + h) C.gates.length := fun hr => by
      have := (orReaches_le 26 C (26 + h) C.gates.length hr).2; omega
    simpa [h2] using h1
  by_contra hlt
  push_neg at hlt
  by_cases h0 : (orIn 26 C (26 + h)).card = 0
  · have hemp : orIn 26 C (26 + h) = ∅ := Finset.card_eq_zero.mp h0
    apply min_no_const_gate hMin hh false
    intro x
    rw [Bool.eq_false_iff]
    intro ht
    obtain ⟨v, hv, _⟩ := (hval x).mp ht
    rw [hemp] at hv; exact Finset.notMem_empty v hv
  · have h1 : (orIn 26 C (26 + h)).card = 1 := by omega
    obtain ⟨v, hv⟩ := Finset.card_eq_one.mp h1
    apply min_no_eq_wire hMin hh (p := v.val) (by omega)
    intro x
    rw [wireVal_input C v.val v.isLt x]
    apply Bool.eq_iff_iff.mpr
    rw [hval x, hv]
    simp

lemma exists_unique_andPair {C : Circuit} (h1 : andPairs 26 C = 1) :
    ∃ i j : ℕ, i < C.gates.length ∧ j < C.gates.length ∧
      (gateAt C i).op = GateOp.and ∧ (gateAt C j).op = GateOp.and ∧
      InCone 26 C i j ∧
      ∀ a < C.gates.length, ∀ b < C.gates.length,
        (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
        InCone 26 C a b → a = i ∧ b = j := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  unfold andPairs at h1
  obtain ⟨⟨i, j⟩, heq⟩ := Finset.card_eq_one.mp h1
  have hmem : (i, j) ∈ (Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p => (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧ InCone 26 C p.1 p.2) := by
    rw [heq]; exact Finset.mem_singleton_self _
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hmem
  refine ⟨i, j, hmem.1.1, hmem.1.2, hmem.2.1, hmem.2.2.1, hmem.2.2.2, ?_⟩
  intro a ha b hb haand hband hab
  have hmem' : (a, b) ∈ (Finset.range C.gates.length ×ˢ Finset.range C.gates.length).filter
      (fun p => (gateAt C p.1).op = GateOp.and ∧ (gateAt C p.2).op = GateOp.and ∧ InCone 26 C p.1 p.2) := by
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨ha, hb⟩, haand, hband, hab⟩
  rw [heq, Finset.mem_singleton, Prod.mk.injEq] at hmem'
  exact hmem'

def A_gates (C : Circuit) : Finset ℕ :=
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  (Finset.range C.gates.length).filter fun g => (gateAt C g).op = GateOp.and

def O_out (C : Circuit) : Finset ℕ :=
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  (Finset.range C.gates.length).filter fun g => (gateAt C g).op = GateOp.or ∧ OrReaches 26 C C.output g

def T_gates (C : Circuit) : Finset ℕ :=
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  (Finset.range C.gates.length).filter fun g => (gateAt C g).op = GateOp.and ∧ OrReaches 26 C C.output g

def O_N (C : Circuit) : Finset ℕ :=
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  (Finset.range C.gates.length).filter fun g => (gateAt C g).op = GateOp.or ∧ ¬ OrReaches 26 C C.output g

def O_pure (C : Circuit) (i : ℕ) : Finset ℕ :=
  (O_N C).filter fun h => ¬ OrReaches 26 C (26 + h) i

lemma mem_A_gates {C : Circuit} {g : ℕ} :
    g ∈ A_gates C ↔ g < C.gates.length ∧ (gateAt C g).op = GateOp.and := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  unfold A_gates; rw [Finset.mem_filter, Finset.mem_range]

lemma mem_O_out {C : Circuit} {g : ℕ} :
    g ∈ O_out C ↔ g < C.gates.length ∧ (gateAt C g).op = GateOp.or ∧ OrReaches 26 C C.output g := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  unfold O_out; rw [Finset.mem_filter, Finset.mem_range]

lemma mem_T_gates {C : Circuit} {g : ℕ} :
    g ∈ T_gates C ↔ g < C.gates.length ∧ (gateAt C g).op = GateOp.and ∧ OrReaches 26 C C.output g := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  unfold T_gates; rw [Finset.mem_filter, Finset.mem_range]

lemma mem_O_N {C : Circuit} {g : ℕ} :
    g ∈ O_N C ↔ g < C.gates.length ∧ (gateAt C g).op = GateOp.or ∧ ¬ OrReaches 26 C C.output g := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  unfold O_N; rw [Finset.mem_filter, Finset.mem_range]

lemma mem_O_pure {C : Circuit} {i h : ℕ} :
    h ∈ O_pure C i ↔ h ∈ O_N C ∧ ¬ OrReaches 26 C (26 + h) i := by
  unfold O_pure; rw [Finset.mem_filter]

lemma size_eq_A_Oout_ON {C : Circuit} (hAO : IsAO2 26 C) :
    C.gates.length = (A_gates C).card + (O_out C).card + (O_N C).card := by
  have hd1 : Disjoint (A_gates C) (O_out C) := by
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    rw [mem_A_gates] at hg1; rw [mem_O_out] at hg2
    rw [hg1.2] at hg2; cases hg2.2.1
  have hd2 : Disjoint (A_gates C ∪ O_out C) (O_N C) := by
    rw [Finset.disjoint_left]
    intro g hg1 hg2
    rw [mem_O_N] at hg2
    rcases Finset.mem_union.mp hg1 with ha | ho
    · rw [mem_A_gates] at ha; rw [ha.2] at hg2; cases hg2.2.1
    · rw [mem_O_out] at ho; exact hg2.2.2 ho.2.2
  have hunion : A_gates C ∪ O_out C ∪ O_N C = Finset.range C.gates.length := by
    ext g
    simp only [Finset.mem_union, mem_A_gates, mem_O_out, mem_O_N, Finset.mem_range]
    constructor
    · rintro ((h | h) | h) <;> exact h.1
    · intro hg
      rcases hAO.1 _ (gateAt_mem hg) with hand | hor
      · exact Or.inl (Or.inl ⟨hg, hand⟩)
      · by_cases hr : OrReaches 26 C C.output g
        · exact Or.inl (Or.inr ⟨hg, hor, hr⟩)
        · exact Or.inr ⟨hg, hor, hr⟩
  have hc := congrArg Finset.card hunion
  rw [Finset.card_union_of_disjoint hd2, Finset.card_union_of_disjoint hd1, Finset.card_range] at hc
  exact hc.symm

lemma inCone_to_orReaches {C : Circuit} (hAO : IsAO2 26 C) (a g : ℕ) (hg : g < C.gates.length)
    (hic : InCone 26 C a g)
    (hnoand : ∀ b < C.gates.length, (gateAt C b).op = GateOp.and → InCone 26 C a b →
      b ≠ g ∧ ¬ InCone 26 C b g) :
    OrReaches 26 C (26 + g) a := by
  induction g using Nat.strong_induction_on with
  | ind g ih =>
    have hgor : (gateAt C g).op = GateOp.or := by
      rcases hAO.1 _ (gateAt_mem hg) with hand | hor
      · exact ((hnoand g hg hand hic).1 rfl).elim
      · exact hor
    rw [inCone_gate_iff 26 C a g hg] at hic
    obtain ⟨w, hw, h26w, hwg, rfl | hick⟩ := hic
    · rw [orReaches_gate_iff 26 C hg (w - 26)]
      right
      refine ⟨hgor, w, hw, hwg, ?_⟩
      have hself := orReaches_self 26 C (show w - 26 < C.gates.length by omega)
      rwa [show 26 + (w - 26) = w by omega] at hself
    · set k := w - 26
      have hk : k < C.gates.length := by omega
      have hnoand_k : ∀ b < C.gates.length, (gateAt C b).op = GateOp.and → InCone 26 C a b →
          b ≠ k ∧ ¬ InCone 26 C b k := by
        intro b hb hband hab
        have hbg := hnoand b hb hband hab
        have hkg : InCone 26 C k g := by
          rw [inCone_gate_iff 26 C k g hg]
          exact ⟨w, hw, h26w, hwg, Or.inl rfl⟩
        refine ⟨fun heq => hbg.2 (heq ▸ hkg), fun hbk => hbg.2 (inCone_trans 26 C b k g hbk hkg)⟩
      have hrk := ih k (by omega) hk hick hnoand_k
      rw [orReaches_gate_iff 26 C hg a]
      right
      exact ⟨hgor, w, hw, hwg, by rwa [show 26 + k = w by omega] at hrk⟩

lemma and_ne_i_in_T {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    {a : ℕ} (ha : a ∈ A_gates C) (hnei : a ≠ i) : a ∈ T_gates C := by
  have hAO := min_isAO2 hMin
  have hout := min_output_bounds hMin.1
  rw [mem_A_gates] at ha
  rw [mem_T_gates]
  refine ⟨ha.1, ha.2, ?_⟩
  have hcone := min_in_output_cone hMin ha.1
  set out := C.output - 26
  have hout_eq : C.output = 26 + out := by omega
  have hout_lt : out < C.gates.length := by omega
  rw [hout_eq]
  rcases hcone with rfl | hic
  · exact orReaches_self 26 C ha.1
  · apply inCone_to_orReaches hAO a out hout_lt hic
    intro b hb hband hab
    exact (hnei (huniq a ha.1 b hb ha.2 hband hab).1).elim

lemma oOut_reads_ge_26 {C : Circuit} (hMin : IsMin C) {h : ℕ} (hh : h ∈ O_out C)
    {w : ℕ} (hw : w ∈ (gateAt C h).inputs) : 26 ≤ w := by
  by_contra hlt
  push_neg at hlt
  rw [mem_O_out] at hh
  have hf := valid_eval_pairInput_false hMin.1 (pgAdj_irrefl ⟨w, hlt⟩)
  have hht : gateVal 26 C h (pairInput ⟨w, hlt⟩ ⟨w, hlt⟩) = true := by
    change wireVal 26 C (26 + h) (pairInput ⟨w, hlt⟩ ⟨w, hlt⟩) = true
    rw [wireVal_gate_rb hMin.1.2.1 hh.1, hh.2.1]
    simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    exact ⟨w, hw, by rw [wireVal_input C w hlt]; simp [pairInput]⟩
  have hout_t := wireVal_ge_of_orReaches hMin.1.2.1 C.output h _ hh.2.2 hht
  rw [hf] at hout_t
  cases hout_t

lemma oOut_not_inCone_j {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (hj : j < C.gates.length) (hjand : (gateAt C j).op = GateOp.and)
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    {h : ℕ} (hh : h ∈ O_out C) : ¬ InCone 26 C h j := by
  intro hic
  have hAO := min_isAO2 hMin
  set S := (O_out C).filter fun g => g = h ∨ InCone 26 C g h
  have hS_ne : S.Nonempty := ⟨h, Finset.mem_filter.mpr ⟨hh, Or.inl rfl⟩⟩
  set h0 := S.min' hS_ne
  have hh0_mem : h0 ∈ S := Finset.min'_mem S hS_ne
  obtain ⟨hh0_out, hh0_rel⟩ := Finset.mem_filter.mp hh0_mem
  have hh0_info := mem_O_out.mp hh0_out
  have h0_ic_j : InCone 26 C h0 j := by
    rcases hh0_rel with heq | h0h
    · rw [heq]; exact hic
    · exact inCone_trans 26 C h0 h j h0h hic
  have hop_and : ∀ b : Fin 2, ∃ a < C.gates.length, opnd C h0 b = 26 + a ∧ (gateAt C a).op = GateOp.and := by
    intro b
    have hmem := opnd_mem hAO hh0_info.1 b
    have hge := oOut_reads_ge_26 hMin hh0_out hmem
    have hlt := opnd_lt hAO hh0_info.1 b
    set a := opnd C h0 b - 26
    have ha_lt : a < C.gates.length := by dsimp only [a]; omega
    have ha_eq : opnd C h0 b = 26 + a := by dsimp only [a]; omega
    refine ⟨a, ha_lt, ha_eq, ?_⟩
    rcases hAO.1 _ (gateAt_mem ha_lt) with hand | hor
    · exact hand
    · exfalso
      have ha_out : a ∈ O_out C := by
        rw [mem_O_out]
        refine ⟨ha_lt, hor, orReaches_trans 26 C C.output h0 a hh0_info.2.2 ?_⟩
        rw [orReaches_gate_iff 26 C hh0_info.1 a]
        right
        exact ⟨hh0_info.2.1, opnd C h0 b, hmem, hlt, by rw [ha_eq]; exact orReaches_self 26 C ha_lt⟩
      have ha_ic_h0 : InCone 26 C a h0 := by
        rw [inCone_gate_iff 26 C a h0 hh0_info.1]
        exact ⟨opnd C h0 b, hmem, hge, hlt, Or.inl rfl⟩
      have ha_S : a ∈ S := Finset.mem_filter.mpr ⟨ha_out, Or.inr (by
        rcases hh0_rel with heq | h0h
        · rwa [← heq]
        · exact inCone_trans 26 C a h0 h ha_ic_h0 h0h)⟩
      have hle : h0 ≤ a := Finset.min'_le S a ha_S
      dsimp only [a] at hle
      omega
  obtain ⟨a0, ha0_lt, ha0_eq, ha0_and⟩ := hop_and 0
  obtain ⟨a1, ha1_lt, ha1_eq, ha1_and⟩ := hop_and 1
  have ha0_ic_h0 : InCone 26 C a0 h0 := by
    rw [inCone_gate_iff 26 C a0 h0 hh0_info.1]
    exact ⟨opnd C h0 0, opnd_mem hAO hh0_info.1 0, by omega, opnd_lt hAO hh0_info.1 0, Or.inl (by omega)⟩
  have ha1_ic_h0 : InCone 26 C a1 h0 := by
    rw [inCone_gate_iff 26 C a1 h0 hh0_info.1]
    exact ⟨opnd C h0 1, opnd_mem hAO hh0_info.1 1, by omega, opnd_lt hAO hh0_info.1 1, Or.inl (by omega)⟩
  have heq0 := (huniq a0 ha0_lt j hj ha0_and hjand (inCone_trans 26 C a0 h0 j ha0_ic_h0 h0_ic_j)).1
  have heq1 := (huniq a1 ha1_lt j hj ha1_and hjand (inCone_trans 26 C a1 h0 j ha1_ic_h0 h0_ic_j)).1
  have hne := min_opnd_ne hMin hh0_info.1
  rw [ha0_eq, ha1_eq, heq0, heq1] at hne
  exact hne rfl

def killWireInGate (w : ℕ) (g : Gate) : Gate :=
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  if g.op = GateOp.or then
    ⟨GateOp.or, g.inputs.filter (fun u => decide (u ≠ w))⟩
  else if w ∈ g.inputs then
    ⟨GateOp.or, []⟩
  else g

def killIInSet (C : Circuit) (i : ℕ) (S : Finset ℕ) : Circuit :=
  { gates := (List.range C.gates.length).map fun k =>
      if k ∈ S then killWireInGate (26 + i) (gateAt C k) else gateAt C k
    output := C.output }

lemma killIInSet_len (C : Circuit) (i : ℕ) (S : Finset ℕ) :
    (killIInSet C i S).gates.length = C.gates.length := by
  simp [killIInSet]

lemma killIInSet_gateAt (C : Circuit) (i : ℕ) (S : Finset ℕ) {k : ℕ} (hk : k < C.gates.length) :
    gateAt (killIInSet C i S) k =
      if k ∈ S then killWireInGate (26 + i) (gateAt C k) else gateAt C k := by
  conv_lhs => unfold gateAt killIInSet
  rw [List.getD_eq_getElem _ _ (by simp [hk])]
  simp [List.getElem_map, List.getElem_range]

lemma killIInSet_monotone2 {C : Circuit} (hM : Monotone2 C) (i : ℕ) (S : Finset ℕ) :
    Monotone2 (killIInSet C i S) := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  intro g hg
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp hg
  have hk' : k < C.gates.length := by simpa [killIInSet_len] using hk
  rw [← gateAt_eq hk, killIInSet_gateAt C i S hk']
  have hm := hM _ (gateAt_mem hk')
  split_ifs with hmem
  · unfold killWireInGate
    split_ifs
    · exact ⟨by simp, (List.length_filter_le _ _).trans hm.2⟩
    · exact ⟨by simp, by simp⟩
    · exact hm
  · exact hm

lemma killIInSet_readsBack {C : Circuit} (hRB : ReadsBack 26 C) (i : ℕ) (S : Finset ℕ) :
    ReadsBack 26 (killIInSet C i S) := by
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  intro k hk u hu
  have hk' : k < C.gates.length := by simpa [killIInSet_len] using hk
  rw [killIInSet_gateAt C i S hk'] at hu
  split_ifs at hu with hmem
  · unfold killWireInGate at hu
    split_ifs at hu
    · exact hRB k hk' u (List.mem_filter.mp hu).1
    · cases hu
    · exact hRB k hk' u hu
  · exact hRB k hk' u hu

lemma not_orToOutput_i {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (hi : i < C.gates.length) (hj : j < C.gates.length)
    (hiand : (gateAt C i).op = GateOp.and) (hjand : (gateAt C j).op = GateOp.and)
    (hic_ij : InCone 26 C i j)
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j) :
    ¬ OrReaches 26 C C.output i := by
  intro hri_out
  letI := PEqualNP.MetaComplexity.NestedCover.gateOpDecEq
  have hAO := min_isAO2 hMin
  have hout := min_output_bounds hMin.1
  set M := (O_N C).filter fun h => OrReaches 26 C (26 + h) i ∧ InCone 26 C h j
  set S := insert j M
  set C1 := killIInSet C i S
  have hS_gt_i : ∀ k ∈ S, i < k := by
    intro k hk
    rcases Finset.mem_insert.mp hk with heq | hkM
    · rw [heq]; exact inCone_lt 26 C i j hic_ij
    · obtain ⟨hkN, hkri, _⟩ := Finset.mem_filter.mp hkM
      have hle := (orReaches_le 26 C (26 + k) i hkri).1
      have hne : i ≠ k := by
        intro heq; subst heq; rw [(mem_O_N.mp hkN).2.1] at hiand; cases hiand
      omega
  have hS_disj_Oout : ∀ k ∈ O_out C, k ∉ S := by
    intro k hk hkS
    rcases Finset.mem_insert.mp hkS with rfl | hkM
    · rw [(mem_O_out.mp hk).2.1] at hjand; cases hjand
    · exact (mem_O_N.mp (Finset.mem_filter.mp hkM).1).2.2 (mem_O_out.mp hk).2.2
  have hRB1 := killIInSet_readsBack hMin.1.2.1 i S
  have hlen1 := killIInSet_len C i S
  have heval1 : ∀ x : Fin 26 → Bool, wireVal 26 C1 C.output x = wireVal 26 C C.output x := by
    intro x
    cases hix : gateVal 26 C i x
    ·
      suffices hall : ∀ w < 26 + C.gates.length, wireVal 26 C1 w x = wireVal 26 C w x from
        hall C.output hout.2
      intro w
      induction w using Nat.strong_induction_on with
      | ind w ih =>
        intro hw
        by_cases hwn : w < 26
        · rw [wireVal_input _ w hwn, wireVal_input _ w hwn]
        · set k := w - 26
          have hk : k < C.gates.length := by omega
          have hwk : w = 26 + k := by omega
          rw [hwk, wireVal_gate_rb hRB1 (by omega), wireVal_gate_rb hMin.1.2.1 hk,
            killIInSet_gateAt C i S hk]
          split_ifs with hkS
          · unfold killWireInGate
            split_ifs with hkor hmem
            · rw [hkor]
              simp only [GateOp.eval, List.any_map, List.any_filter, Function.comp_apply, id_eq]
              apply Bool.eq_iff_iff.mpr
              simp only [List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq]
              constructor
              · rintro ⟨u, hu, _, huv⟩
                have hult := hMin.1.2.1 k hk u hu
                rw [ih u (by omega) (by omega)] at huv
                exact ⟨u, hu, huv⟩
              · rintro ⟨u, hu, huv⟩
                have hult := hMin.1.2.1 k hk u hu
                have hune : u ≠ 26 + i := by
                  intro heq; subst heq; change gateVal 26 C i x = true at huv
                  rw [hix] at huv; cases huv
                exact ⟨u, hu, hune, by rwa [ih u (by omega) (by omega)]⟩
            · rcases hAO.1 _ (gateAt_mem hk) with hkand | hkor'
              · rw [hkand]
                simp only [GateOp.eval, List.map_nil, List.any_nil]
                symm
                rw [List.all_eq_false]
                exact ⟨false, List.mem_map.mpr ⟨26 + i, hmem, hix⟩, by simp⟩
              · exact (hkor hkor').elim
            · congr 1
              apply List.map_congr_left
              intro u hu
              have hult := hMin.1.2.1 k hk u hu
              exact ih u (by omega) (by omega)
          · congr 1
            apply List.map_congr_left
            intro u hu
            have hult := hMin.1.2.1 k hk u hu
            exact ih u (by omega) (by omega)
    ·
      have hle_i : ∀ w ≤ 26 + i, wireVal 26 C1 w x = wireVal 26 C w x := by
        intro w
        induction w using Nat.strong_induction_on with
        | ind w ih =>
          intro hw
          by_cases hwn : w < 26
          · rw [wireVal_input _ w hwn, wireVal_input _ w hwn]
          · set k := w - 26
            have hk : k < C.gates.length := by omega
            have hwk : w = 26 + k := by omega
            have hk_notS : k ∉ S := fun hkS => by have := hS_gt_i k hkS; omega
            rw [hwk, wireVal_gate_rb hRB1 (by omega), wireVal_gate_rb hMin.1.2.1 hk,
              killIInSet_gateAt C i S hk]
            simp only [hk_notS, ↓reduceIte]
            congr 1
            apply List.map_congr_left
            intro u hu
            have hult := hMin.1.2.1 k hk u hu
            exact ih u (by omega) (by omega)
      have hi_t1 : wireVal 26 C1 (26 + i) x = true := by
        rw [hle_i (26 + i) le_rfl]; exact hix
      have hout_t_C : wireVal 26 C C.output x = true :=
        wireVal_ge_of_orReaches hMin.1.2.1 C.output i x hri_out hix
      rw [hout_t_C]
      suffices hreach_t1 : ∀ k < C.gates.length, (k = i ∨ k ∈ O_out C) →
          OrReaches 26 C (26 + k) i → wireVal 26 C1 (26 + k) x = true by
        set out := C.output - 26
        have hout_eq : C.output = 26 + out := by omega
        rw [hout_eq] at hri_out ⊢
        apply hreach_t1 out (by omega) ?_ hri_out
        rcases hAO.1 _ (gateAt_mem (show out < C.gates.length by omega)) with hand | hor
        · left
          rw [orReaches_gate_iff 26 C (show out < C.gates.length by omega) i] at hri_out
          rcases hri_out with heq | ⟨hor', _⟩
          · exact heq.symm
          · rw [hand] at hor'; cases hor'
        · right
          exact mem_O_out.mpr ⟨by omega, hor, by rw [hout_eq]; exact orReaches_self 26 C (by omega)⟩
      intro k
      induction k using Nat.strong_induction_on with
      | ind k ih =>
        intro hk hki hkri
        rcases hki with rfl | hkout
        · exact hi_t1
        · have hk_notS := hS_disj_Oout k hkout
          have hk_info := mem_O_out.mp hkout
          rw [orReaches_gate_iff 26 C hk i] at hkri
          rcases hkri with heq | ⟨_, u, hu, huk, huri⟩
          · subst heq; exact hi_t1
          · have h26u : 26 ≤ u := huri.1
            set k' := u - 26
            have hk'_lt : k' < k := by omega
            have hu_eq : u = 26 + k' := by omega
            have hk'_ki : k' = i ∨ k' ∈ O_out C := by
              rcases hAO.1 _ (gateAt_mem (show k' < C.gates.length by omega)) with hand | hor
              · left
                rw [hu_eq, orReaches_gate_iff 26 C (show k' < C.gates.length by omega) i] at huri
                rcases huri with heq | ⟨hor', _⟩
                · exact heq.symm
                · rw [hand] at hor'; cases hor'
              · right
                refine mem_O_out.mpr ⟨by omega, hor, orReaches_trans 26 C C.output k k' hk_info.2.2 ?_⟩
                rw [orReaches_gate_iff 26 C hk k']
                right
                exact ⟨hk_info.2.1, u, hu, huk, by rw [hu_eq]; exact orReaches_self 26 C (by omega)⟩
            have ht' := ih k' hk'_lt (by omega) hk'_ki (by rwa [← hu_eq])
            rw [wireVal_gate_rb hRB1 (by omega), killIInSet_gateAt C i S hk]
            simp only [hk_notS, ↓reduceIte, hk_info.2.1, GateOp.eval, List.any_map, List.any_eq_true,
              Function.comp_apply, id_eq]
            exact ⟨u, hu, by rwa [hu_eq]⟩

  have hV1 : ValidCirc C1 := by
    refine ⟨killIInSet_monotone2 hMin.1.1 i S, hRB1, ?_, ?_⟩
    · intro a l hal
      rw [← ofFn_pair_pt_ln a l]
      change wireVal 26 C1 C.output _ = true
      rw [heval1]
      change C.eval _ = true
      rw [ofFn_pair_pt_ln a l]
      exact hMin.1.2.2.1 a l hal
    · intro X Y hs hn
      change wireVal 26 C1 C.output _ = false
      rw [heval1]
      exact hMin.1.2.2.2 X Y hs hn
  have hMin1 : IsMin C1 := ⟨hV1, fun C' hC' => by
    change C1.gates.length ≤ C'.size
    rw [hlen1]
    exact hMin.2 C' hC'⟩
  have hAO1 := min_isAO2 hMin1

  have hsmall : ∃ g < C.gates.length, (gateAt C1 g).inputs.length ≤ 1 := by
    by_cases hM : M.Nonempty
    · set h0 := M.min' hM
      have hh0_M : h0 ∈ M := Finset.min'_mem M hM
      obtain ⟨hh0_N, hh0_ri, hh0_ic⟩ := Finset.mem_filter.mp hh0_M
      have hh0_info := mem_O_N.mp hh0_N
      have hreads_i : 26 + i ∈ (gateAt C h0).inputs := by
        rw [orReaches_gate_iff 26 C hh0_info.1 i] at hh0_ri
        rcases hh0_ri with heq | ⟨_, u, hu, huk, huri⟩
        · rw [heq] at hiand; rw [hh0_info.2.1] at hiand; cases hiand
        · by_cases hui : u = 26 + i
          · rwa [← hui]
          · exfalso
            have h26u := huri.1
            set k := u - 26
            have hk_lt : k < h0 := by omega
            have hu_eq : u = 26 + k := by omega
            have hk_ic_h0 : InCone 26 C k h0 := by
              rw [inCone_gate_iff 26 C k h0 hh0_info.1]
              exact ⟨u, hu, h26u, huk, Or.inl rfl⟩
            have hk_ic_j : InCone 26 C k j := inCone_trans 26 C k h0 j hk_ic_h0 hh0_ic
            rcases hAO.1 _ (gateAt_mem (show k < C.gates.length by omega)) with hand | hor
            · rw [hu_eq, orReaches_gate_iff 26 C (show k < C.gates.length by omega) i] at huri
              rcases huri with heq | ⟨hor', _⟩
              · exact hui (by omega)
              · rw [hand] at hor'; cases hor'
            · have hk_not_out : ¬ OrReaches 26 C C.output k := fun hko =>
                oOut_not_inCone_j hMin hj hjand huniq (mem_O_out.mpr ⟨by omega, hor, hko⟩) hk_ic_j
              have hk_M : k ∈ M := Finset.mem_filter.mpr
                ⟨mem_O_N.mpr ⟨by omega, hor, hk_not_out⟩, by rwa [← hu_eq], hk_ic_j⟩
              have hle := Finset.min'_le M k hk_M
              omega
      refine ⟨h0, hh0_info.1, ?_⟩
      rw [killIInSet_gateAt C i S hh0_info.1]
      have hh0_S : h0 ∈ S := Finset.mem_insert_of_mem hh0_M
      simp only [hh0_S, ↓reduceIte, killWireInGate, hh0_info.2.1, ↓reduceIte]
      have hlen2 : (gateAt C h0).inputs.length = 2 := hAO.2.2 _ (gateAt_mem hh0_info.1)
      have hlt : ((gateAt C h0).inputs.filter (fun u => decide (u ≠ 26 + i))).length <
          (gateAt C h0).inputs.length :=
        List.length_filter_lt_length_iff_exists.mpr ⟨26 + i, hreads_i, by simp⟩
      omega
    ·
      have hM_emp : M = ∅ := Finset.not_nonempty_iff_eq_empty.mp hM
      have hj_reads_i : 26 + i ∈ (gateAt C j).inputs := by
        rw [inCone_gate_iff 26 C i j hj] at hic_ij
        obtain ⟨w, hw, h26w, hwj, hiw | hick⟩ := hic_ij
        · rwa [show 26 + i = w by omega]
        · exfalso
          set k := w - 26
          have hk_lt : k < j := by omega
          have hk_ic_j : InCone 26 C k j := by
            rw [inCone_gate_iff 26 C k j hj]
            exact ⟨w, hw, h26w, hwj, Or.inl rfl⟩
          have hk_or : (gateAt C k).op = GateOp.or := by
            rcases hAO.1 _ (gateAt_mem (show k < C.gates.length by omega)) with hand | hor
            · have := (huniq k (by omega) j hj hand hjand hk_ic_j).1
              have := inCone_lt 26 C i k hick
              omega
            · exact hor
          have hk_ri : OrReaches 26 C (26 + k) i := by
            apply inCone_to_orReaches hAO i k (by omega) hick
            intro b hb hband hib
            have heq := (huniq i hi b hb hiand hband hib).2
            rw [heq]
            refine ⟨by omega, fun hjk => ?_⟩
            have := inCone_lt 26 C j k hjk
            omega
          have hk_not_out : ¬ OrReaches 26 C C.output k := fun hko =>
            oOut_not_inCone_j hMin hj hjand huniq (mem_O_out.mpr ⟨by omega, hk_or, hko⟩) hk_ic_j
          have hk_M : k ∈ M := Finset.mem_filter.mpr
            ⟨mem_O_N.mpr ⟨by omega, hk_or, hk_not_out⟩, hk_ri, hk_ic_j⟩
          rw [hM_emp] at hk_M
          exact Finset.notMem_empty k hk_M
      refine ⟨j, hj, ?_⟩
      rw [killIInSet_gateAt C i S hj]
      have hjS : j ∈ S := Finset.mem_insert_self j M
      simp only [hjS, ↓reduceIte, killWireInGate, hjand, reduceCtorEq, hj_reads_i,
        List.length_nil, Nat.zero_le]
  obtain ⟨g, hg, hle1⟩ := hsmall
  have heq2 : (gateAt C1 g).inputs.length = 2 := hAO1.2.2 _ (gateAt_mem (by rw [hlen1]; exact hg))
  omega

lemma oPure_no_and {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    {h : ℕ} (hh : h ∈ O_pure C i) :
    ∀ a < C.gates.length, (gateAt C a).op = GateOp.and → ¬ OrReaches 26 C (26 + h) a := by
  intro a ha haand hha
  have hAO := min_isAO2 hMin
  have hout := min_output_bounds hMin.1
  obtain ⟨hhN, hnotri⟩ := mem_O_pure.mp hh
  have hh_info := mem_O_N.mp hhN
  have hah_ic : InCone 26 C a h := by
    rcases orReaches_imp_inCone_or_eq 26 C hh_info.1 a hha with rfl | hic
    · rw [hh_info.2.1] at haand; cases haand
    · exact hic

  set out := C.output - 26
  have hout_eq : C.output = 26 + out := by omega
  have hout_lt : out < C.gates.length := by omega
  have hh_ne_out : h ≠ out := by
    intro heq; apply hh_info.2.2; rw [hout_eq, ← heq]; exact orReaches_self 26 C hh_info.1
  have hh_ic_out : InCone 26 C h out := (min_in_output_cone hMin hh_info.1).resolve_left hh_ne_out
  have hex_b : ∃ b < C.gates.length, (gateAt C b).op = GateOp.and ∧ InCone 26 C h b := by
    by_contra hno
    push_neg at hno
    apply hh_info.2.2
    rw [hout_eq]
    apply inCone_to_orReaches hAO h out hout_lt hh_ic_out
    intro b hb hband hhb
    exact (hno b hb hband hhb).elim
  obtain ⟨b, hb, hband, hhb⟩ := hex_b
  have hab : InCone 26 C a b := inCone_trans 26 C a h b hah_ic hhb
  have hai := (huniq a ha b hb haand hband hab).1
  subst hai
  exact hnotri hha

def EdgeReach {α : Type*} (E : List (α × α)) : α → α → Prop :=
  Relation.ReflTransGen fun u v => (u, v) ∈ E ∨ (v, u) ∈ E

lemma edgeReach_symm {α : Type*} {E : List (α × α)} {u v : α} (h : EdgeReach E u v) :
    EdgeReach E v u := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact Relation.ReflTransGen.head
      (by rcases hstep with h1 | h2 <;> [exact Or.inr h1; exact Or.inl h2]) ih

lemma graph_spanning_bound {α : Type*} [DecidableEq α] (E : List (α × α)) :
    ∀ (L R : Finset α), (∀ u ∈ L, ∃ r ∈ R, EdgeReach E u r) →
      L.card ≤ E.length + R.card := by
  classical
  induction E with
  | nil =>
    intro L R hcov
    have hsub : L ⊆ R := by
      intro u hu
      obtain ⟨r, hr, hreach⟩ := hcov u hu
      cases hreach with
      | refl => exact hr
      | tail _ hstep => simp at hstep
    have := Finset.card_le_card hsub
    simp; omega
  | cons e rest ih =>
    rcases e with ⟨a, b⟩
    intro L R hcov
    have hsplit_path : ∀ u r, EdgeReach ((a, b) :: rest) u r →
        EdgeReach rest u r ∨
        (EdgeReach rest u a ∧ (EdgeReach rest a r ∨ EdgeReach rest b r)) ∨
        (EdgeReach rest u b ∧ (EdgeReach rest a r ∨ EdgeReach rest b r)) := by
      intro u r hreach
      induction hreach with
      | refl => exact Or.inl Relation.ReflTransGen.refl
      | @tail x y _ hstep ih' =>
        simp only [List.mem_cons] at hstep
        rcases hstep with (heq | hmem) | (heq | hmem)
        · have hxa : x = a := congrArg Prod.fst heq
          have hyb : y = b := congrArg Prod.snd heq
          subst hxa; subst hyb
          rcases ih' with hr | ⟨hu1, _⟩ | ⟨hu2, _⟩
          · exact Or.inr (Or.inl ⟨hr, Or.inr Relation.ReflTransGen.refl⟩)
          · exact Or.inr (Or.inl ⟨hu1, Or.inr Relation.ReflTransGen.refl⟩)
          · exact Or.inr (Or.inr ⟨hu2, Or.inr Relation.ReflTransGen.refl⟩)
        · rcases ih' with hr | ⟨hu1, ha | hb⟩ | ⟨hu2, ha | hb⟩
          · exact Or.inl (Relation.ReflTransGen.tail hr (Or.inl hmem))
          · exact Or.inr (Or.inl ⟨hu1, Or.inl (Relation.ReflTransGen.tail ha (Or.inl hmem))⟩)
          · exact Or.inr (Or.inl ⟨hu1, Or.inr (Relation.ReflTransGen.tail hb (Or.inl hmem))⟩)
          · exact Or.inr (Or.inr ⟨hu2, Or.inl (Relation.ReflTransGen.tail ha (Or.inl hmem))⟩)
          · exact Or.inr (Or.inr ⟨hu2, Or.inr (Relation.ReflTransGen.tail hb (Or.inl hmem))⟩)
        · have hya : y = a := congrArg Prod.fst heq
          have hxb : x = b := congrArg Prod.snd heq
          subst hya; subst hxb
          rcases ih' with hr | ⟨hu1, _⟩ | ⟨hu2, _⟩
          · exact Or.inr (Or.inr ⟨hr, Or.inl Relation.ReflTransGen.refl⟩)
          · exact Or.inr (Or.inl ⟨hu1, Or.inl Relation.ReflTransGen.refl⟩)
          · exact Or.inr (Or.inr ⟨hu2, Or.inl Relation.ReflTransGen.refl⟩)
        · rcases ih' with hr | ⟨hu1, ha | hb⟩ | ⟨hu2, ha | hb⟩
          · exact Or.inl (Relation.ReflTransGen.tail hr (Or.inr hmem))
          · exact Or.inr (Or.inl ⟨hu1, Or.inl (Relation.ReflTransGen.tail ha (Or.inr hmem))⟩)
          · exact Or.inr (Or.inl ⟨hu1, Or.inr (Relation.ReflTransGen.tail hb (Or.inr hmem))⟩)
          · exact Or.inr (Or.inr ⟨hu2, Or.inl (Relation.ReflTransGen.tail ha (Or.inr hmem))⟩)
          · exact Or.inr (Or.inr ⟨hu2, Or.inr (Relation.ReflTransGen.tail hb (Or.inr hmem))⟩)
    by_cases haR : ∃ r ∈ R, EdgeReach rest a r
    · obtain ⟨ra, hra, hrea⟩ := haR
      have hcov' : ∀ u ∈ L, ∃ r ∈ insert b R, EdgeReach rest u r := by
        intro u hu
        obtain ⟨r, hr, hreach⟩ := hcov u hu
        rcases hsplit_path u r hreach with hr' | ⟨hua, _⟩ | ⟨hub, _⟩
        · exact ⟨r, Finset.mem_insert_of_mem hr, hr'⟩
        · exact ⟨ra, Finset.mem_insert_of_mem hra, hua.trans hrea⟩
        · exact ⟨b, Finset.mem_insert_self b R, hub⟩
      have := ih L (insert b R) hcov'
      have hcard := Finset.card_insert_le b R
      simp only [List.length_cons]; omega
    · by_cases hbR : ∃ r ∈ R, EdgeReach rest b r
      · obtain ⟨rb, hrb, hreb⟩ := hbR
        have hcov' : ∀ u ∈ L, ∃ r ∈ insert a R, EdgeReach rest u r := by
          intro u hu
          obtain ⟨r, hr, hreach⟩ := hcov u hu
          rcases hsplit_path u r hreach with hr' | ⟨hua, _⟩ | ⟨hub, _⟩
          · exact ⟨r, Finset.mem_insert_of_mem hr, hr'⟩
          · exact ⟨a, Finset.mem_insert_self a R, hua⟩
          · exact ⟨rb, Finset.mem_insert_of_mem hrb, hub.trans hreb⟩
        have := ih L (insert a R) hcov'
        have hcard := Finset.card_insert_le a R
        simp only [List.length_cons]; omega
      · have hcov' : ∀ u ∈ L, ∃ r ∈ R, EdgeReach rest u r := by
          intro u hu
          obtain ⟨r, hr, hreach⟩ := hcov u hu
          rcases hsplit_path u r hreach with hr' | ⟨_, ha' | hb'⟩ | ⟨_, ha' | hb'⟩
          · exact ⟨r, hr, hr'⟩
          · exact (haR ⟨r, hr, ha'⟩).elim
          · exact (hbR ⟨r, hr, hb'⟩).elim
          · exact (haR ⟨r, hr, ha'⟩).elim
          · exact (hbR ⟨r, hr, hb'⟩).elim
        have := ih L R hcov'
        simp only [List.length_cons]; omega

lemma dag_conn {α : Type*} [DecidableEq α] {C : Circuit} (hAO : IsAO2 26 C)
    (f : ℕ → Finset α)
    (hf_in : ∀ w < 26, (f w).card ≤ 1)
    (hf_and : ∀ g < C.gates.length, (gateAt C g).op = GateOp.and → (f (26 + g)).card ≤ 1)
    (hf_or : ∀ g < C.gates.length, (gateAt C g).op = GateOp.or →
      f (26 + g) = f (opnd C g 0) ∪ f (opnd C g 1))
    (S : Finset ℕ) (L : Finset α) (W : Finset ℕ)
    (hW_lt : ∀ w ∈ W, w < 26 + C.gates.length)
    (hS_cov : ∀ w ∈ W, ∀ h, OrReaches 26 C w h → (gateAt C h).op = GateOp.or →
      2 ≤ (f (26 + h) ∩ L).card →
      (f (opnd C h 0) ∩ L).Nonempty → (f (opnd C h 1) ∩ L).Nonempty → h ∈ S) :
    ∃ E : List (α × α), E.length ≤ S.card ∧
      ∀ w ∈ W, ∀ u ∈ f w ∩ L, ∀ v ∈ f w ∩ L, EdgeReach E u v := by
  classical
  let mkEdge : ℕ → Option (α × α) := fun h =>
    if hh : (f (opnd C h 0) ∩ L).Nonempty ∧ (f (opnd C h 1) ∩ L).Nonempty then
      some (hh.1.choose, hh.2.choose)
    else none
  let E : List (α × α) := S.toList.filterMap mkEdge
  refine ⟨E, (List.length_filterMap_le _ _).trans (Finset.length_toList S).le, ?_⟩
  have hconn : ∀ x < 26 + C.gates.length,
      (∃ w ∈ W, x = w ∨ (26 ≤ x ∧ OrReaches 26 C w (x - 26))) →
      ∀ u ∈ f x ∩ L, ∀ v ∈ f x ∩ L, EdgeReach E u v := by
    intro x
    induction x using Nat.strong_induction_on with
    | ind x ih =>
      intro hx hreach_w u hu v hv
      by_cases huv : u = v
      · rw [huv]; exact Relation.ReflTransGen.refl
      · by_cases hxn : x < 26
        · have hle1 := (Finset.card_le_card (Finset.inter_subset_left (s₂ := L))).trans (hf_in x hxn)
          have hgt1 := Finset.one_lt_card.mpr ⟨u, hu, v, hv, huv⟩
          omega
        · set h := x - 26
          have hxh : x = 26 + h := by omega
          have hh_lt : h < C.gates.length := by omega
          rw [hxh] at hu hv
          rcases hAO.1 _ (gateAt_mem hh_lt) with hand | hor
          · have hle1 := (Finset.card_le_card (Finset.inter_subset_left (s₂ := L))).trans (hf_and h hh_lt hand)
            have hgt1 := Finset.one_lt_card.mpr ⟨u, hu, v, hv, huv⟩
            omega
          · have hwh : ∃ w ∈ W, OrReaches 26 C w h := by
              obtain ⟨w, hw, hw_eq | ⟨_, hwr⟩⟩ := hreach_w
              · exact ⟨w, hw, hw_eq ▸ hxh ▸ orReaches_self 26 C hh_lt⟩
              · exact ⟨w, hw, hwr⟩
            obtain ⟨w, hw, hwr⟩ := hwh
            have hsub_conn : ∀ b : Fin 2, ∀ a1 ∈ f (opnd C h b) ∩ L,
                ∀ a2 ∈ f (opnd C h b) ∩ L, EdgeReach E a1 a2 := by
              intro b a1 ha1 a2 ha2
              have hblt := opnd_lt hAO hh_lt b
              by_cases hbn : opnd C h b < 26
              · by_cases heq : a1 = a2
                · rw [heq]; exact Relation.ReflTransGen.refl
                · have hle1 := (Finset.card_le_card (Finset.inter_subset_left (s₂ := L))).trans (hf_in _ hbn)
                  have hgt1 := Finset.one_lt_card.mpr ⟨a1, ha1, a2, ha2, heq⟩
                  omega
              · apply ih (opnd C h b) (by omega) (by omega)
                · refine ⟨w, hw, Or.inr ⟨by omega, orReaches_trans 26 C w h (opnd C h b - 26) hwr ?_⟩⟩
                  rw [orReaches_gate_iff 26 C hh_lt]
                  right
                  refine ⟨hor, opnd C h b, opnd_mem hAO hh_lt b, hblt, ?_⟩
                  have hself := orReaches_self 26 C (show opnd C h b - 26 < C.gates.length by omega)
                  rwa [show 26 + (opnd C h b - 26) = opnd C h b by omega] at hself
                · exact ha1
                · exact ha2
            have hcard2 : 2 ≤ (f (26 + h) ∩ L).card :=
              Finset.one_lt_card.mpr ⟨u, hu, v, hv, huv⟩
            rw [hf_or h hh_lt hor, Finset.union_inter_distrib_right] at hu hv
            rcases Finset.mem_union.mp hu with hu0 | hu1 <;> rcases Finset.mem_union.mp hv with hv0 | hv1
            · exact hsub_conn 0 u hu0 v hv0
            · have hne0 : (f (opnd C h 0) ∩ L).Nonempty := ⟨u, hu0⟩
              have hne1 : (f (opnd C h 1) ∩ L).Nonempty := ⟨v, hv1⟩
              have hhS : h ∈ S := hS_cov w hw h hwr hor hcard2 hne0 hne1
              have hh_mem : (hne0.choose, hne1.choose) ∈ E := by
                simp only [E, List.mem_filterMap]
                refine ⟨h, Finset.mem_toList.mpr hhS, ?_⟩
                simp only [mkEdge, hne0, hne1, and_self, ↓reduceDIte]
              have hr1 := hsub_conn 0 u hu0 _ hne0.choose_spec
              have hr2 : EdgeReach E hne0.choose hne1.choose :=
                Relation.ReflTransGen.single (Or.inl hh_mem)
              have hr3 := hsub_conn 1 _ hne1.choose_spec v hv1
              exact (hr1.trans hr2).trans hr3
            · have hne0 : (f (opnd C h 0) ∩ L).Nonempty := ⟨v, hv0⟩
              have hne1 : (f (opnd C h 1) ∩ L).Nonempty := ⟨u, hu1⟩
              have hhS : h ∈ S := hS_cov w hw h hwr hor hcard2 hne0 hne1
              have hh_mem : (hne0.choose, hne1.choose) ∈ E := by
                simp only [E, List.mem_filterMap]
                refine ⟨h, Finset.mem_toList.mpr hhS, ?_⟩
                simp only [mkEdge, hne0, hne1, and_self, ↓reduceDIte]
              have hr1 := hsub_conn 1 u hu1 _ hne1.choose_spec
              have hr2 : EdgeReach E hne1.choose hne0.choose :=
                Relation.ReflTransGen.single (Or.inr hh_mem)
              have hr3 := hsub_conn 0 _ hne0.choose_spec v hv0
              exact (hr1.trans hr2).trans hr3
            · exact hsub_conn 1 u hu1 v hv1
  intro w hw u hu v hv
  exact hconn w (hW_lt w hw) ⟨w, hw, Or.inl rfl⟩ u hu v hv

lemma oOut_card_bound {C : Circuit} (hMin : IsMin C) :
    (T_gates C).card ≤ (O_out C).card + 1 := by
  have hAO := min_isAO2 hMin
  have hout := min_output_bounds hMin.1
  by_cases hTe : (T_gates C).Nonempty
  · let f : ℕ → Finset ℕ := fun w => (T_gates C).filter fun a => OrReaches 26 C w a
    have hf_in : ∀ w < 26, (f w).card ≤ 1 := by
      intro w hw
      have hemp : f w = ∅ := by
        ext a; simp only [f, Finset.mem_filter, Finset.notMem_empty, iff_false, not_and]
        intro _ hr; have := hr.1; omega
      rw [hemp]; simp
    have hf_and : ∀ g < C.gates.length, (gateAt C g).op = GateOp.and → (f (26 + g)).card ≤ 1 := by
      intro g hg hand
      have hsub : f (26 + g) ⊆ {g} := by
        intro a ha
        simp only [f, Finset.mem_filter, Finset.mem_singleton] at ha ⊢
        rw [orReaches_gate_iff 26 C hg a] at ha
        rcases ha.2 with rfl | ⟨hor, _⟩
        · rfl
        · rw [hand] at hor; cases hor
      exact (Finset.card_le_card hsub).trans (by simp)
    have hf_or : ∀ g < C.gates.length, (gateAt C g).op = GateOp.or →
        f (26 + g) = f (opnd C g 0) ∪ f (opnd C g 1) := by
      intro g hg hor
      ext a
      simp only [f, Finset.mem_union, Finset.mem_filter]
      constructor
      · intro ⟨haT, hrg⟩
        have hne : a ≠ g := by
          intro heq; subst heq; rw [(mem_T_gates.mp haT).2.1] at hor; cases hor
        rw [orReaches_gate_or_iff hAO hg hor hne] at hrg
        rcases hrg with h0 | h1
        · exact Or.inl ⟨haT, h0⟩
        · exact Or.inr ⟨haT, h1⟩
      · rintro (⟨haT, h0⟩ | ⟨haT, h1⟩)
        · have hne : a ≠ g := by
            intro heq; subst heq; rw [(mem_T_gates.mp haT).2.1] at hor; cases hor
          exact ⟨haT, (orReaches_gate_or_iff hAO hg hor hne).mpr (Or.inl h0)⟩
        · have hne : a ≠ g := by
            intro heq; subst heq; rw [(mem_T_gates.mp haT).2.1] at hor; cases hor
          exact ⟨haT, (orReaches_gate_or_iff hAO hg hor hne).mpr (Or.inr h1)⟩
    obtain ⟨E, hElen, hconn⟩ := dag_conn hAO f hf_in hf_and hf_or (O_out C) (T_gates C) {C.output}
      (fun w hw => by rw [Finset.mem_singleton.mp hw]; exact hout.2)
      (fun w hw h hwr hor _ _ _ => by
        rw [Finset.mem_singleton.mp hw] at hwr
        exact mem_O_out.mpr ⟨(orReaches_le 26 C C.output h hwr).2, hor, hwr⟩)
    obtain ⟨r0, hr0⟩ := hTe
    have hf_out : f C.output ∩ T_gates C = T_gates C := by
      ext a; simp only [f, Finset.mem_inter, Finset.mem_filter]
      constructor
      · exact fun h => h.2
      · intro ha; exact ⟨⟨ha, (mem_T_gates.mp ha).2.2⟩, ha⟩
    have hcov : ∀ u ∈ T_gates C, ∃ r ∈ ({r0} : Finset ℕ), EdgeReach E u r := by
      intro u hu
      refine ⟨r0, Finset.mem_singleton_self r0, ?_⟩
      apply hconn C.output (Finset.mem_singleton_self _)
      · rw [hf_out]; exact hu
      · rw [hf_out]; exact hr0
    have hb := graph_spanning_bound E (T_gates C) {r0} hcov
    rw [Finset.card_singleton] at hb
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hTe]; simp

def O_c (C : Circuit) (i : ℕ) (c : Fin 26) : Finset ℕ :=
  (O_pure C i).filter fun h => orIn 26 C (26 + h) ⊆ nbrs c

def O_extra (C : Circuit) (i : ℕ) : Finset ℕ :=
  O_N C \ (Finset.univ : Finset (Fin 26)).biUnion (O_c C i)

lemma oC_pairwiseDisjoint {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j) :
    Set.PairwiseDisjoint (↑(Finset.univ : Finset (Fin 26))) (O_c C i) := by
  intro c1 _ c2 _ hne
  dsimp only [Function.onFun]
  rw [Finset.disjoint_left]
  intro h h1 h2
  obtain ⟨hpure, hsub1⟩ := Finset.mem_filter.mp h1
  obtain ⟨_, hsub2⟩ := Finset.mem_filter.mp h2
  have hhN := (mem_O_pure.mp hpure).1
  have hh_info := mem_O_N.mp hhN
  have hge2 := min_pure_or_card_ge_two hMin hh_info.1 hh_info.2.1 (oPure_no_and hMin huniq hpure)
  have hsub_inter : orIn 26 C (26 + h) ⊆ nbrs c1 ∩ nbrs c2 := Finset.subset_inter hsub1 hsub2
  have hle1 := (Finset.card_le_card hsub_inter).trans (pg_no_c4 c1 c2 hne)
  omega

lemma oN_card_eq {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j) :
    (O_N C).card = (O_extra C i).card + ∑ c : Fin 26, (O_c C i c).card := by
  have hsub : (Finset.univ : Finset (Fin 26)).biUnion (O_c C i) ⊆ O_N C := by
    intro h hh
    obtain ⟨c, _, hc⟩ := Finset.mem_biUnion.mp hh
    exact (mem_O_pure.mp (Finset.mem_filter.mp hc).1).1
  have hcard_bi : ((Finset.univ : Finset (Fin 26)).biUnion (O_c C i)).card =
      ∑ c : Fin 26, (O_c C i c).card :=
    Finset.card_biUnion (oC_pairwiseDisjoint hMin huniq)
  unfold O_extra
  have hs := Finset.card_sdiff_add_card_eq_card hsub
  omega

lemma pure_star_center_bound {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    (c : Fin 26) (W : Finset ℕ)
    (hW_lt : ∀ w ∈ W, w < 26 + C.gates.length)
    (hW_sub : ∀ w ∈ W, orIn 26 C w ⊆ nbrs c)
    (hW_pure : ∀ w ∈ W, ∀ h, OrReaches 26 C w h → (gateAt C h).op = GateOp.or → h ∈ O_pure C i) :
    (W.biUnion (orIn 26 C)).card ≤ (O_c C i c).card + W.card := by
  classical
  have hAO := min_isAO2 hMin
  set U := W.biUnion (orIn 26 C)
  have hf_in : ∀ w < 26, (orIn 26 C w).card ≤ 1 := by
    intro w hw
    have heq : orIn 26 C w = {⟨w, hw⟩} := by
      ext v; simp [orIn_input C hw v, Fin.ext_iff]
    rw [heq]; simp
  have hf_and : ∀ g < C.gates.length, (gateAt C g).op = GateOp.and → (orIn 26 C (26 + g)).card ≤ 1 := by
    intro g hg hand; rw [orIn_gate_and C hg hand]; simp
  have hf_or : ∀ g < C.gates.length, (gateAt C g).op = GateOp.or →
      orIn 26 C (26 + g) = orIn 26 C (opnd C g 0) ∪ orIn 26 C (opnd C g 1) :=
    fun g hg hor => orIn_gate_or hAO hg hor
  obtain ⟨E, hElen, hconn⟩ := dag_conn hAO (orIn 26 C) hf_in hf_and hf_or (O_c C i c) U W hW_lt
    (fun w hw h hwr hor _ _ _ => Finset.mem_filter.mpr
      ⟨hW_pure w hw h hwr hor, (orIn_mono_of_orReaches C w h hwr).trans (hW_sub w hw)⟩)
  let Wne := W.filter fun w => (orIn 26 C w).Nonempty
  let R : Finset (Fin 26) := Wne.attach.image fun w => (Finset.mem_filter.mp w.2).2.choose
  have hR_card : R.card ≤ W.card :=
    Finset.card_image_le.trans (by rw [Finset.card_attach]; exact Finset.card_filter_le _ _)
  have hcov : ∀ u ∈ U, ∃ r ∈ R, EdgeReach E u r := by
    intro u hu
    obtain ⟨w, hwW, huw⟩ := Finset.mem_biUnion.mp hu
    have hne : (orIn 26 C w).Nonempty := ⟨u, huw⟩
    have hwne : w ∈ Wne := Finset.mem_filter.mpr ⟨hwW, hne⟩
    let r := (Finset.mem_filter.mp hwne).2.choose
    have hr_mem : r ∈ orIn 26 C w := (Finset.mem_filter.mp hwne).2.choose_spec
    have hr_U : r ∈ U := Finset.mem_biUnion.mpr ⟨w, hwW, hr_mem⟩
    have hr_R : r ∈ R := Finset.mem_image.mpr ⟨⟨w, hwne⟩, Finset.mem_attach _ _, rfl⟩
    exact ⟨r, hr_R, hconn w hwW u (Finset.mem_inter.mpr ⟨huw, hu⟩) r (Finset.mem_inter.mpr ⟨hr_mem, hr_U⟩)⟩
  have hb := graph_spanning_bound E U R hcov
  omega

def fMix (C : Circuit) (i : ℕ) (w : ℕ) : Finset (Option (Fin 26)) :=
  (orIn 26 C w).image some ∪ if OrReaches 26 C w i then {none} else ∅

lemma mixed_center_conn {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (hi : i < C.gates.length) (hiand : (gateAt C i).op = GateOp.and)
    (c0 : Fin 26) (L : Finset (Option (Fin 26)))
    (hL_sub : L ⊆ (nbrs c0).image some ∪ {some c0, none})
    (W : Finset ℕ) (hW_lt : ∀ w ∈ W, w < 26 + C.gates.length)
    (hW_oN : ∀ w ∈ W, ∀ h, OrReaches 26 C w h → (gateAt C h).op = GateOp.or → h ∈ O_N C) :
    ∃ E : List (Option (Fin 26) × Option (Fin 26)),
      E.length ≤ (O_c C i c0 ∪ O_extra C i).card ∧
      ∀ w ∈ W, ∀ u ∈ fMix C i w ∩ L, ∀ v ∈ fMix C i w ∩ L, EdgeReach E u v := by
  have hAO := min_isAO2 hMin
  have hf_in : ∀ w < 26, (fMix C i w).card ≤ 1 := by
    intro w hw
    have hnr : ¬ OrReaches 26 C w i := fun hr => by have := hr.1; omega
    have heq : orIn 26 C w = {⟨w, hw⟩} := by ext v; simp [orIn_input C hw v, Fin.ext_iff]
    simp [fMix, hnr, heq]
  have hf_and : ∀ g < C.gates.length, (gateAt C g).op = GateOp.and → (fMix C i (26 + g)).card ≤ 1 := by
    intro g hg hand
    simp only [fMix, orIn_gate_and C hg hand, Finset.image_empty, Finset.empty_union]
    split_ifs <;> simp
  have hf_or : ∀ g < C.gates.length, (gateAt C g).op = GateOp.or →
      fMix C i (26 + g) = fMix C i (opnd C g 0) ∪ fMix C i (opnd C g 1) := by
    intro g hg hor
    have hne : i ≠ g := fun heq => by subst heq; rw [hiand] at hor; cases hor
    ext x
    simp only [fMix, orIn_gate_or hAO hg hor, Finset.image_union, Finset.mem_union,
      orReaches_gate_or_iff hAO hg hor hne]
    cases x <;>
      by_cases h0 : OrReaches 26 C (opnd C g 0) i <;>
      by_cases h1 : OrReaches 26 C (opnd C g 1) i <;>
      simp [h0, h1]
  apply dag_conn hAO (fMix C i) hf_in hf_and hf_or (O_c C i c0 ∪ O_extra C i) L W hW_lt
  intro w hw h hwr hor hcard2 _ _
  have hhN : h ∈ O_N C := hW_oN w hw h hwr hor
  by_cases hex : h ∈ O_extra C i
  · exact Finset.mem_union_right _ hex
  · apply Finset.mem_union_left
    unfold O_extra at hex
    rw [Finset.mem_sdiff] at hex
    push_neg at hex
    obtain ⟨c, _, hhc⟩ := Finset.mem_biUnion.mp (hex hhN)
    by_cases hcc0 : c = c0
    · rwa [hcc0] at hhc
    · exfalso
      obtain ⟨hhpure, hsub_c⟩ := Finset.mem_filter.mp hhc
      have hnotri := (mem_O_pure.mp hhpure).2
      obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcard2
      obtain ⟨hxf, hxL⟩ := Finset.mem_inter.mp hx
      obtain ⟨hyf, hyL⟩ := Finset.mem_inter.mp hy
      simp only [fMix, hnotri, ↓reduceIte, Finset.union_empty, Finset.mem_image] at hxf hyf
      obtain ⟨u, hu, rfl⟩ := hxf
      obtain ⟨v, hv, rfl⟩ := hyf
      have huv : u ≠ v := fun heq => hxy (congrArg some heq)
      have huc : u ∈ nbrs c := hsub_c hu
      have hvc : v ∈ nbrs c := hsub_c hv
      have huL : u ∈ nbrs c0 ∨ u = c0 := by
        have h1 := hL_sub hxL
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton,
          Option.some.injEq, reduceCtorEq, or_false] at h1
        rcases h1 with ⟨u', hu', heq⟩ | heq
        · left; rwa [← heq]
        · exact Or.inr heq
      have hvL : v ∈ nbrs c0 ∨ v = c0 := by
        have h1 := hL_sub hyL
        simp only [Finset.mem_union, Finset.mem_image, Finset.mem_insert, Finset.mem_singleton,
          Option.some.injEq, reduceCtorEq, or_false] at h1
        rcases h1 with ⟨v', hv', heq⟩ | heq
        · left; rwa [← heq]
        · exact Or.inr heq
      rcases huL with hu0 | rfl <;> rcases hvL with hv0 | rfl
      · have hpair : ({u, v} : Finset (Fin 26)) ⊆ nbrs c ∩ nbrs c0 := by
          intro z hz
          simp only [Finset.mem_insert, Finset.mem_singleton] at hz
          rcases hz with rfl | rfl <;> exact Finset.mem_inter.mpr ⟨by assumption, by assumption⟩
        have := (Finset.card_le_card hpair).trans (pg_no_c4 c c0 hcc0)
        rw [Finset.card_pair huv] at this; omega
      · have hb1 := pgAdj_bip c u (mem_nbrs_iff c u |>.mp huc)
        have hb2 := pgAdj_bip c v (mem_nbrs_iff c v |>.mp hvc)
        have hb3 := pgAdj_bip v u (mem_nbrs_iff v u |>.mp hu0)
        tauto
      · have hb1 := pgAdj_bip c u (mem_nbrs_iff c u |>.mp huc)
        have hb2 := pgAdj_bip c v (mem_nbrs_iff c v |>.mp hvc)
        have hb3 := pgAdj_bip u v (mem_nbrs_iff u v |>.mp hv0)
        tauto
      · exact huv rfl

def dirEdge (u v : Fin 26) : Fin 26 × Fin 26 :=
  if u.val < 13 then (u, v) else (v, u)

lemma dirEdge_mem_pgEdges {u v : Fin 26} (h : pgAdj u v = true) : dirEdge u v ∈ pgEdges := by
  have hbip := pgAdj_bip u v h
  rw [mem_pgEdges_iff]
  unfold dirEdge
  split_ifs with hu
  · exact ⟨hu, h⟩
  · have hv : v.val < 13 := by tauto
    exact ⟨hv, by rwa [pgAdj_symm]⟩

lemma dirEdge_symm {u v : Fin 26} (h : pgAdj u v = true) : dirEdge u v = dirEdge v u := by
  have hbip := pgAdj_bip u v h
  unfold dirEdge
  by_cases hu : u.val < 13 <;> by_cases hv : v.val < 13
  · exact (hbip (propext (iff_of_true hu hv))).elim
  · simp [hu, hv]
  · simp [hu, hv]
  · exact (hbip (propext (iff_of_false hu hv))).elim

lemma dirEdge_eq_of_mem_pgEdges {e : Fin 26 × Fin 26} (he : e ∈ pgEdges) :
    dirEdge e.1 e.2 = e := by
  rw [mem_pgEdges_iff] at he
  unfold dirEdge
  simp [he.1]

def starEdgesOf (c : Fin 26) (L : Finset (Fin 26)) : Finset (Fin 26 × Fin 26) :=
  L.image (dirEdge c)

lemma starEdgesOf_card (c : Fin 26) (L : Finset (Fin 26)) :
    (starEdgesOf c L).card = L.card := by
  unfold starEdgesOf
  apply Finset.card_image_of_injective
  intro x y hxy
  unfold dirEdge at hxy
  split_ifs at hxy
  · exact congrArg Prod.snd hxy
  · exact congrArg Prod.fst hxy

lemma starEdgesOf_card_le_four {c : Fin 26} {L : Finset (Fin 26)} (hL : L ⊆ nbrs c) :
    (starEdgesOf c L).card ≤ 4 := by
  rw [starEdgesOf_card]
  exact (Finset.card_le_card hL).trans (nbrs_card c).le

lemma mem_starEdgesOf_left {c v : Fin 26} {L : Finset (Fin 26)} (hv : v ∈ L) :
    dirEdge c v ∈ starEdgesOf c L :=
  Finset.mem_image.mpr ⟨v, hv, rfl⟩

lemma mem_starEdgesOf_right {c u : Fin 26} {L : Finset (Fin 26)} (hadj : pgAdj u c = true) (hu : u ∈ L) :
    dirEdge u c ∈ starEdgesOf c L := by
  rw [dirEdge_symm hadj]
  exact mem_starEdgesOf_left hu

lemma biclique_is_star {S0 S1 : Finset (Fin 26)}
    (hadj : ∀ u ∈ S0, ∀ v ∈ S1, pgAdj u v = true) :
    S0.card ≤ 1 ∨ S1.card ≤ 1 := by
  by_contra h
  push_neg at h
  obtain ⟨u1, hu1, u2, hu2, hune⟩ := Finset.one_lt_card.mp h.1
  obtain ⟨v1, hv1, v2, hv2, hvne⟩ := Finset.one_lt_card.mp h.2
  have hsub : ({v1, v2} : Finset (Fin 26)) ⊆ nbrs u1 ∩ nbrs u2 := by
    intro v hv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with heq | heq
    · rw [heq]; exact Finset.mem_inter.mpr ⟨(mem_nbrs_iff u1 v1).mpr (hadj u1 hu1 v1 hv1),
        (mem_nbrs_iff u2 v1).mpr (hadj u2 hu2 v1 hv1)⟩
    · rw [heq]; exact Finset.mem_inter.mpr ⟨(mem_nbrs_iff u1 v2).mpr (hadj u1 hu1 v2 hv2),
        (mem_nbrs_iff u2 v2).mpr (hadj u2 hu2 v2 hv2)⟩
  have hle := (Finset.card_le_card hsub).trans (pg_no_c4 u1 u2 hune)
  rw [Finset.card_pair hvne] at hle
  omega

lemma oOut_not_inCone_any_and {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    {b : ℕ} (hb : b < C.gates.length) (hband : (gateAt C b).op = GateOp.and)
    {h : ℕ} (hh : h ∈ O_out C) : ¬ InCone 26 C h b := by
  intro hic
  have hAO := min_isAO2 hMin
  set S := (O_out C).filter fun g => g = h ∨ InCone 26 C g h
  have hS_ne : S.Nonempty := ⟨h, Finset.mem_filter.mpr ⟨hh, Or.inl rfl⟩⟩
  set h0 := S.min' hS_ne with hh0_def
  obtain ⟨hh0_out, hh0_rel⟩ := Finset.mem_filter.mp (Finset.min'_mem S hS_ne)
  have hh0_info := mem_O_out.mp hh0_out
  have h0_ic_b : InCone 26 C h0 b := by
    rcases hh0_rel with heq | h0h
    · rw [← hh0_def] at heq; rw [heq]; exact hic
    · exact inCone_trans 26 C h0 h b h0h hic
  have hop_and : ∀ s : Fin 2, ∃ a < C.gates.length, opnd C h0 s = 26 + a ∧ (gateAt C a).op = GateOp.and := by
    intro s
    have hh0_lt : h0 < C.gates.length := hh0_info.1
    have hmem : opnd C h0 s ∈ (gateAt C h0).inputs := opnd_mem hAO hh0_lt s
    have hge : 26 ≤ opnd C h0 s := oOut_reads_ge_26 hMin hh0_out hmem
    have hlt : opnd C h0 s < 26 + h0 := opnd_lt hAO hh0_lt s
    set a := opnd C h0 s - 26 with ha_def
    have ha_lt : a < C.gates.length := by rw [ha_def]; omega
    have ha_eq : opnd C h0 s = 26 + a := by rw [ha_def]; omega
    refine ⟨a, ha_lt, ha_eq, ?_⟩
    rcases hAO.1 _ (gateAt_mem ha_lt) with hand | hor
    · exact hand
    · exfalso
      have ha_out : a ∈ O_out C := by
        rw [mem_O_out]
        refine ⟨ha_lt, hor, orReaches_trans 26 C C.output h0 a hh0_info.2.2 ?_⟩
        rw [orReaches_gate_iff 26 C hh0_info.1 a]
        right
        exact ⟨hh0_info.2.1, opnd C h0 s, hmem, hlt, by rw [ha_eq]; exact orReaches_self 26 C ha_lt⟩
      have ha_ic_h0 : InCone 26 C a h0 := by
        rw [inCone_gate_iff 26 C a h0 hh0_info.1]
        exact ⟨opnd C h0 s, hmem, hge, hlt, Or.inl rfl⟩
      have ha_S : a ∈ S := Finset.mem_filter.mpr ⟨ha_out, Or.inr (by
        rcases hh0_rel with heq | h0h
        · rw [← hh0_def] at heq; rwa [← heq]
        · exact inCone_trans 26 C a h0 h ha_ic_h0 h0h)⟩
      have hle : h0 ≤ a := Finset.min'_le S a ha_S
      rw [ha_def] at hle
      omega
  obtain ⟨a0, ha0_lt, ha0_eq, ha0_and⟩ := hop_and 0
  obtain ⟨a1, ha1_lt, ha1_eq, ha1_and⟩ := hop_and 1
  have ha0_ic : InCone 26 C a0 b := inCone_trans 26 C a0 h0 b (by
    rw [inCone_gate_iff 26 C a0 h0 hh0_info.1]
    exact ⟨opnd C h0 0, opnd_mem hAO hh0_info.1 0, by omega, opnd_lt hAO hh0_info.1 0, Or.inl (by omega)⟩) h0_ic_b
  have ha1_ic : InCone 26 C a1 b := inCone_trans 26 C a1 h0 b (by
    rw [inCone_gate_iff 26 C a1 h0 hh0_info.1]
    exact ⟨opnd C h0 1, opnd_mem hAO hh0_info.1 1, by omega, opnd_lt hAO hh0_info.1 1, Or.inl (by omega)⟩) h0_ic_b
  have heq0 := (huniq a0 ha0_lt b hb ha0_and hband ha0_ic).1
  have heq1 := (huniq a1 ha1_lt b hb ha1_and hband ha1_ic).1
  have hne := min_opnd_ne hMin hh0_info.1
  rw [ha0_eq, ha1_eq, heq0, heq1] at hne
  exact hne rfl

lemma opnd_or_in_ON {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    {a : ℕ} (ha : a < C.gates.length) (haand : (gateAt C a).op = GateOp.and) (s : Fin 2)
    {h : ℕ} (hhr : OrReaches 26 C (opnd C a s) h) (hhor : (gateAt C h).op = GateOp.or) :
    h ∈ O_N C := by
  have hAO := min_isAO2 hMin
  have hh_lt := (orReaches_le 26 C (opnd C a s) h hhr).2
  have hh_ic : InCone 26 C h a := by
    have h26 := hhr.1
    have hlt := opnd_lt hAO ha s
    have hsub := orReaches_imp_inCone_or_eq 26 C (show opnd C a s - 26 < C.gates.length by omega) h
      (by rwa [show 26 + (opnd C a s - 26) = opnd C a s by omega])
    rw [inCone_gate_iff 26 C h a ha]
    exact ⟨opnd C a s, opnd_mem hAO ha s, h26, hlt, hsub⟩
  refine mem_O_N.mpr ⟨hh_lt, hhor, fun hro => ?_⟩
  exact oOut_not_inCone_any_and hMin huniq ha haand (mem_O_out.mpr ⟨hh_lt, hhor, hro⟩) hh_ic

lemma opnd_or_in_Opure_of_ne_j {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (hi : i < C.gates.length) (hiand : (gateAt C i).op = GateOp.and)
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    {a : ℕ} (ha : a < C.gates.length) (haand : (gateAt C a).op = GateOp.and) (hnej : a ≠ j)
    (s : Fin 2) {h : ℕ} (hhr : OrReaches 26 C (opnd C a s) h) (hhor : (gateAt C h).op = GateOp.or) :
    h ∈ O_pure C i := by
  have hAO := min_isAO2 hMin
  have hhN := opnd_or_in_ON hMin huniq ha haand s hhr hhor
  refine mem_O_pure.mpr ⟨hhN, fun hhi => ?_⟩
  have hri : OrReaches 26 C (opnd C a s) i := orReaches_trans 26 C (opnd C a s) h i hhr hhi
  have h26 := hri.1
  have hlt := opnd_lt hAO ha s
  have hsub := orReaches_imp_inCone_or_eq 26 C (show opnd C a s - 26 < C.gates.length by omega) i
    (by rwa [show 26 + (opnd C a s - 26) = opnd C a s by omega])
  have hic : InCone 26 C i a := by
    rw [inCone_gate_iff 26 C i a ha]
    exact ⟨opnd C a s, opnd_mem hAO ha s, h26, hlt, hsub⟩
  exact hnej (huniq i hi a ha hiand haand hic).2

lemma opnd_or_in_Opure_of_not_reach_i {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    {a : ℕ} (ha : a < C.gates.length) (haand : (gateAt C a).op = GateOp.and) (s : Fin 2)
    (hnri : ¬ OrReaches 26 C (opnd C a s) i)
    {h : ℕ} (hhr : OrReaches 26 C (opnd C a s) h) (hhor : (gateAt C h).op = GateOp.or) :
    h ∈ O_pure C i :=
  mem_O_pure.mpr ⟨opnd_or_in_ON hMin huniq ha haand s hhr hhor,
    fun hhi => hnri (orReaches_trans 26 C (opnd C a s) h i hhr hhi)⟩

lemma pure_and_eval {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    {a : ℕ} (ha : a < C.gates.length) (haand : (gateAt C a).op = GateOp.and) (hnej : a ≠ j)
    (x : Fin 26 → Bool) :
    gateVal 26 C a x = true ↔
      (∃ u ∈ side (n := 26) C a 0, x u = true) ∧ (∃ v ∈ side (n := 26) C a 1, x v = true) := by
  have hAO := min_isAO2 hMin
  change wireVal 26 C (26 + a) x = true ↔ _
  unfold side
  rw [wireVal_gate_and hAO ha haand, Bool.and_eq_true]
  have hside : ∀ s : Fin 2, wireVal 26 C (opnd C a s) x = true ↔ ∃ u ∈ orIn 26 C (opnd C a s), x u = true := by
    intro s
    have hlt := opnd_lt hAO ha s
    have hno : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ OrReaches 26 C (opnd C a s) k := by
      intro k hk hkand hrk
      have h26 := hrk.1
      have hsub := orReaches_imp_inCone_or_eq 26 C (show opnd C a s - 26 < C.gates.length by omega) k
        (by rwa [show 26 + (opnd C a s - 26) = opnd C a s by omega])
      have hic : InCone 26 C k a := by
        rw [inCone_gate_iff 26 C k a ha]
        exact ⟨opnd C a s, opnd_mem hAO ha s, h26, hlt, hsub⟩
      exact hnej (huniq k hk a ha hkand haand hic).2
    have h1 := wireVal_eq_orIn_or_i hMin.1.1 hMin.1.2.1 C.gates.length (opnd C a s) (by omega)
      (fun k hk hkand hrk => (hno k hk hkand hrk).elim) x
    have h2 : ¬ OrReaches 26 C (opnd C a s) C.gates.length := fun hr => by
      have := (orReaches_le 26 C (opnd C a s) C.gates.length hr).2; omega
    simpa [h2] using h1
  rw [hside 0, hside 1]

lemma j_eval {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (hj : j < C.gates.length) (hjand : (gateAt C j).op = GateOp.and)
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    (x : Fin 26 → Bool) :
    gateVal 26 C j x = true ↔
      ((OrReaches 26 C (opnd C j 0) i ∧ gateVal 26 C i x = true) ∨
        ∃ u ∈ side (n := 26) C j 0, x u = true) ∧
      ((OrReaches 26 C (opnd C j 1) i ∧ gateVal 26 C i x = true) ∨
        ∃ v ∈ side (n := 26) C j 1, x v = true) := by
  have hAO := min_isAO2 hMin
  change wireVal 26 C (26 + j) x = true ↔ _
  unfold side
  rw [wireVal_gate_and hAO hj hjand, Bool.and_eq_true]
  have hside : ∀ s : Fin 2, wireVal 26 C (opnd C j s) x = true ↔
      (OrReaches 26 C (opnd C j s) i ∧ gateVal 26 C i x = true) ∨
      ∃ u ∈ orIn 26 C (opnd C j s), x u = true := by
    intro s
    have hlt := opnd_lt hAO hj s
    apply wireVal_eq_orIn_or_i hMin.1.1 hMin.1.2.1 i (opnd C j s) (by omega)
    intro k hk hkand hrk
    have h26 := hrk.1
    have hsub := orReaches_imp_inCone_or_eq 26 C (show opnd C j s - 26 < C.gates.length by omega) k
      (by rwa [show 26 + (opnd C j s - 26) = opnd C j s by omega])
    have hic : InCone 26 C k j := by
      rw [inCone_gate_iff 26 C k j hj]
      exact ⟨opnd C j s, opnd_mem hAO hj s, h26, hlt, hsub⟩
    exact (huniq k hk j hj hkand hjand hic).1
  rw [hside 0, hside 1]

lemma j_orReaches_i {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (hi : i < C.gates.length) (hj : j < C.gates.length)
    (hiand : (gateAt C i).op = GateOp.and) (hjand : (gateAt C j).op = GateOp.and)
    (hic : InCone 26 C i j)
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j) :
    OrReaches 26 C (opnd C j 0) i ∨ OrReaches 26 C (opnd C j 1) i := by
  have hAO := min_isAO2 hMin
  rw [inCone_gate_iff 26 C i j hj, gate_inputs_eq hAO hj] at hic
  obtain ⟨w, hw, h26w, hwj, hiw | hick⟩ := hic
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    have hself := orReaches_self 26 C hi
    rw [show 26 + i = w by omega] at hself
    rcases hw with rfl | rfl
    · exact Or.inl hself
    · exact Or.inr hself
  · set k := w - 26
    have hk_lt : k < C.gates.length := by omega
    have hrk : OrReaches 26 C (26 + k) i := by
      apply inCone_to_orReaches hAO i k hk_lt hick
      intro b hb hband hib
      have hbj := (huniq i hi b hb hiand hband hib).2
      rw [hbj]
      refine ⟨by omega, fun hjk => ?_⟩
      have := inCone_lt 26 C j k hjk
      omega
    rw [show 26 + k = w by omega] at hrk
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inl hrk
    · exact Or.inr hrk

lemma edge_accepted_by_T {C : Circuit} (hMin : IsMin C) {e : Fin 26 × Fin 26} (he : e ∈ pgEdges) :
    ∃ a ∈ T_gates C, gateVal 26 C a (pairInput e.1 e.2) = true := by
  have hAO := min_isAO2 hMin
  have hout := min_output_bounds hMin.1
  have ht : wireVal 26 C C.output (pairInput e.1 e.2) = true :=
    valid_eval_pairInput_true hMin.1 (mem_pgEdges_iff e |>.mp he).2
  suffices hrec : ∀ w < 26 + C.gates.length, (w = C.output ∨ (26 ≤ w ∧ OrReaches 26 C C.output (w - 26))) →
      wireVal 26 C w (pairInput e.1 e.2) = true →
      ∃ a ∈ T_gates C, gateVal 26 C a (pairInput e.1 e.2) = true from
    hrec C.output hout.2 (Or.inl rfl) ht
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hreach hval
    have h26w : 26 ≤ w := by
      rcases hreach with rfl | ⟨h26, _⟩
      · exact hout.1
      · exact h26
    set k := w - 26
    have hk_lt : k < C.gates.length := by omega
    have hwk : w = 26 + k := by omega
    have hro : OrReaches 26 C C.output k := by
      rcases hreach with rfl | ⟨_, hr⟩
      · rw [hwk]; exact orReaches_self 26 C hk_lt
      · exact hr
    rcases hAO.1 _ (gateAt_mem hk_lt) with hand | hor
    · exact ⟨k, mem_T_gates.mpr ⟨hk_lt, hand, hro⟩, by change wireVal 26 C (26 + k) _ = true; rwa [← hwk]⟩
    · rw [hwk, wireVal_gate_or hAO hk_lt hor, Bool.or_eq_true] at hval
      have hkout : k ∈ O_out C := mem_O_out.mpr ⟨hk_lt, hor, hro⟩
      rcases hval with h0 | h1
      · have h0lt := opnd_lt hAO hk_lt 0
        have h0ge := oOut_reads_ge_26 hMin hkout (opnd_mem hAO hk_lt 0)
        apply ih (opnd C k 0) (by omega) (by omega) ?_ h0
        right; refine ⟨h0ge, orReaches_trans 26 C C.output k (opnd C k 0 - 26) hro ?_⟩
        rw [orReaches_gate_iff 26 C hk_lt]
        right
        refine ⟨hor, opnd C k 0, opnd_mem hAO hk_lt 0, h0lt, ?_⟩
        have hself := orReaches_self 26 C (show opnd C k 0 - 26 < C.gates.length by omega)
        rwa [show 26 + (opnd C k 0 - 26) = opnd C k 0 by omega] at hself
      · have h1lt := opnd_lt hAO hk_lt 1
        have h1ge := oOut_reads_ge_26 hMin hkout (opnd_mem hAO hk_lt 1)
        apply ih (opnd C k 1) (by omega) (by omega) ?_ h1
        right; refine ⟨h1ge, orReaches_trans 26 C C.output k (opnd C k 1 - 26) hro ?_⟩
        rw [orReaches_gate_iff 26 C hk_lt]
        right
        refine ⟨hor, opnd C k 1, opnd_mem hAO hk_lt 1, h1lt, ?_⟩
        have hself := orReaches_self 26 C (show opnd C k 1 - 26 < C.gates.length by omega)
        rwa [show 26 + (opnd C k 1 - 26) = opnd C k 1 by omega] at hself

lemma pure_star_spec {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    {a : ℕ} (ha : a < C.gates.length) (haand : (gateAt C a).op = GateOp.and) (hnej : a ≠ j)
    (hbelow : ∀ u v : Fin 26, pgAdj u v = false → gateVal 26 C a (pairInput u v) = false) :
    ∃ (c : Fin 26) (s : Fin 2),
      side (n := 26) C a (1 - s) = {c} ∧
      side (n := 26) C a s ⊆ nbrs c ∧
      (side (n := 26) C a s).Nonempty ∧
      ∀ e ∈ pgEdges, gateVal 26 C a (pairInput e.1 e.2) = true →
        e ∈ starEdgesOf c (side (n := 26) C a s) := by
  have hadj : ∀ u ∈ side (n := 26) C a 0, ∀ v ∈ side (n := 26) C a 1, pgAdj u v = true := by
    intro u hu v hv
    cases h : pgAdj u v
    · exfalso
      have hf := hbelow u v h
      have ht : gateVal 26 C a (pairInput u v) = true :=
        (pure_and_eval hMin huniq ha haand hnej (pairInput u v)).mpr
          ⟨⟨u, hu, by simp [pairInput]⟩, ⟨v, hv, by simp [pairInput]⟩⟩
      rw [hf] at ht; cases ht
    · rfl
  have hne0 : (side (n := 26) C a 0).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply min_no_const_gate hMin ha false
    intro x
    rw [Bool.eq_false_iff]
    intro ht
    obtain ⟨⟨u, hu, _⟩, _⟩ := (pure_and_eval hMin huniq ha haand hnej x).mp ht
    rw [h] at hu; exact Finset.notMem_empty u hu
  have hne1 : (side (n := 26) C a 1).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    apply min_no_const_gate hMin ha false
    intro x
    rw [Bool.eq_false_iff]
    intro ht
    obtain ⟨_, ⟨v, hv, _⟩⟩ := (pure_and_eval hMin huniq ha haand hnej x).mp ht
    rw [h] at hv; exact Finset.notMem_empty v hv
  rcases biclique_is_star hadj with h0 | h1
  · have h0eq : (side (n := 26) C a 0).card = 1 := le_antisymm h0 (Finset.card_pos.mpr hne0)
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp h0eq
    refine ⟨c, 1, by simpa using hc, ?_, hne1, ?_⟩
    · intro v hv
      exact (mem_nbrs_iff c v).mpr (hadj c (by rw [hc]; simp) v hv)
    · intro e he hgt
      obtain ⟨⟨u, hu, hup⟩, ⟨v, hv, hvp⟩⟩ := (pure_and_eval hMin huniq ha haand hnej _).mp hgt
      rw [hc, Finset.mem_singleton] at hu; subst u
      simp only [pairInput, decide_eq_true_eq] at hup hvp
      have hne_cv : c ≠ v := fun heq => by
        subst heq; have := hadj c (by rw [hc]; simp) c hv; rw [pgAdj_irrefl] at this; cases this
      have hadj_e := (mem_pgEdges_iff e).mp he |>.2
      rw [← dirEdge_eq_of_mem_pgEdges he]
      rcases hup with h1c | h2c <;> rcases hvp with h1' | h2'
      · exact (hne_cv (h1c.trans h1'.symm)).elim
      · rw [← h1c, ← h2']; exact mem_starEdgesOf_left hv
      · rw [← h1', ← h2c] at hadj_e ⊢; exact mem_starEdgesOf_right hadj_e hv
      · exact (hne_cv (h2c.trans h2'.symm)).elim
  · have h1eq : (side (n := 26) C a 1).card = 1 := le_antisymm h1 (Finset.card_pos.mpr hne1)
    obtain ⟨c, hc⟩ := Finset.card_eq_one.mp h1eq
    refine ⟨c, 0, by simpa using hc, ?_, hne0, ?_⟩
    · intro u hu
      exact (mem_nbrs_iff c u).mpr (by rw [pgAdj_symm]; exact hadj u hu c (by rw [hc]; simp))
    · intro e he hgt
      obtain ⟨⟨u, hu, hup⟩, ⟨v, hv, hvp⟩⟩ := (pure_and_eval hMin huniq ha haand hnej _).mp hgt
      rw [hc, Finset.mem_singleton] at hv; subst v
      simp only [pairInput, decide_eq_true_eq] at hup hvp
      have hne_uc : u ≠ c := fun heq => by
        subst heq; have := hadj u hu u (by rw [hc]; simp); rw [pgAdj_irrefl] at this; cases this
      have hadj_e := (mem_pgEdges_iff e).mp he |>.2
      rw [← dirEdge_eq_of_mem_pgEdges he]
      rcases hup with h1u | h2u <;> rcases hvp with h1' | h2'
      · exact (hne_uc (h1u.trans h1'.symm)).elim
      · rw [← h1u, ← h2'] at hadj_e ⊢; exact mem_starEdgesOf_right hadj_e hu
      · rw [← h2u, ← h1']; exact mem_starEdgesOf_left hu
      · exact (hne_uc (h2u.trans h2'.symm)).elim

lemma below_of_mem_T {C : Circuit} (hMin : IsMin C) {a : ℕ} (ha : a ∈ T_gates C) :
    ∀ u v : Fin 26, pgAdj u v = false → gateVal 26 C a (pairInput u v) = false := by
  intro u v hnadj
  rw [Bool.eq_false_iff]
  intro ht
  have hf := valid_eval_pairInput_false hMin.1 hnadj
  have hout := wireVal_ge_of_orReaches hMin.1.2.1 C.output a (pairInput u v) (mem_T_gates.mp ha).2.2 ht
  rw [hf] at hout
  cases hout

lemma extra_of_mixed_bipartite {C : Circuit} (hMin : IsMin C) {i : ℕ}
    {w : ℕ} (hw : w < 26 + C.gates.length)
    (hwoN : ∀ h, OrReaches 26 C w h → (gateAt C h).op = GateOp.or → h ∈ O_N C)
    {u v : Fin 26} (hu : u ∈ orIn 26 C w) (hv : v ∈ orIn 26 C w)
    (hbip : (u.val < 13) ≠ (v.val < 13)) :
    1 ≤ (O_extra C i).card := by
  have hAO := min_isAO2 hMin
  have hne : u ≠ v := fun heq => hbip (by rw [heq])
  have h26 : 26 ≤ w := by
    by_contra hlt; push_neg at hlt
    have e1 := (orIn_input C hlt u).mp hu
    have e2 := (orIn_input C hlt v).mp hv
    exact hne (Fin.ext (e1.trans e2.symm))
  set h := w - 26
  have hh_lt : h < C.gates.length := by omega
  have hwh : w = 26 + h := by omega
  rw [hwh] at hu hv hwoN
  have hhor : (gateAt C h).op = GateOp.or := by
    rcases hAO.1 _ (gateAt_mem hh_lt) with hand | hor
    · rw [orIn_gate_and C hh_lt hand] at hu; exact (Finset.notMem_empty u hu).elim
    · exact hor
  have hhN : h ∈ O_N C := hwoN h (orReaches_self 26 C hh_lt) hhor
  have hhex : h ∈ O_extra C i := by
    unfold O_extra
    rw [Finset.mem_sdiff]
    refine ⟨hhN, ?_⟩
    intro hbi
    obtain ⟨c, _, hhc⟩ := Finset.mem_biUnion.mp hbi
    have hsub := (Finset.mem_filter.mp hhc).2
    have hb1 := pgAdj_bip c u ((mem_nbrs_iff c u).mp (hsub hu))
    have hb2 := pgAdj_bip c v ((mem_nbrs_iff c v).mp (hsub hv))
    tauto
  exact Finset.card_pos.mpr ⟨h, hhex⟩

lemma extra_of_reaches_i_and_input {C : Circuit} (hMin : IsMin C) {i : ℕ}
    (hiand : (gateAt C i).op = GateOp.and)
    {w : ℕ} (hw : w < 26 + C.gates.length)
    (hri : OrReaches 26 C w i) (hne : (orIn 26 C w).Nonempty)
    (hwoN : ∀ h, OrReaches 26 C w h → (gateAt C h).op = GateOp.or → h ∈ O_N C) :
    1 ≤ (O_extra C i).card := by
  have hAO := min_isAO2 hMin
  have h26 := hri.1
  set h := w - 26
  have hh_lt : h < C.gates.length := by omega
  have hwh : w = 26 + h := by omega
  rw [hwh] at hri hne hwoN
  have hhor : (gateAt C h).op = GateOp.or := by
    rcases hAO.1 _ (gateAt_mem hh_lt) with hand | hor
    · rw [orIn_gate_and C hh_lt hand] at hne; exact (Finset.not_nonempty_empty hne).elim
    · exact hor
  have hhN : h ∈ O_N C := hwoN h (orReaches_self 26 C hh_lt) hhor
  have hhex : h ∈ O_extra C i := by
    unfold O_extra
    rw [Finset.mem_sdiff]
    refine ⟨hhN, ?_⟩
    intro hbi
    obtain ⟨c, _, hhc⟩ := Finset.mem_biUnion.mp hbi
    exact (mem_O_pure.mp (Finset.mem_filter.mp hhc).1).2 hri
  exact Finset.card_pos.mpr ⟨h, hhex⟩

lemma card_filter_sum {α β : Type*} [Fintype β] [DecidableEq β] [DecidableEq α]
    (s : Finset α) (f : α → β) :
    ∑ b : β, (s.filter fun a => f a = b).card = s.card := by
  rw [← Finset.card_biUnion]
  · congr 1; ext a; simp
  · intro b1 _ b2 _ hne
    dsimp only [Function.onFun]
    rw [Finset.disjoint_left]
    intro a h1 h2
    exact hne ((Finset.mem_filter.mp h1).2.symm.trans (Finset.mem_filter.mp h2).2)

lemma pure_family_sum_bound {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    (Idx : Finset ℕ) (ctr : ℕ → Fin 26) (wire : ℕ → ℕ)
    (hW_lt : ∀ k ∈ Idx, wire k < 26 + C.gates.length)
    (hW_sub : ∀ k ∈ Idx, orIn 26 C (wire k) ⊆ nbrs (ctr k))
    (hW_pure : ∀ k ∈ Idx, ∀ h, OrReaches 26 C (wire k) h → (gateAt C h).op = GateOp.or → h ∈ O_pure C i)
    (hcov : ∀ e ∈ pgEdges, ∃ k ∈ Idx, e ∈ starEdgesOf (ctr k) (orIn 26 C (wire k))) :
    52 ≤ (∑ c : Fin 26, (O_c C i c).card) + Idx.card := by
  let Wc : Fin 26 → Finset ℕ := fun c => (Idx.filter fun k => ctr k = c).image wire
  let Uc : Fin 26 → Finset (Fin 26) := fun c => (Wc c).biUnion (orIn 26 C)
  have hper_c : ∀ c : Fin 26, (Uc c).card ≤ (O_c C i c).card + (Idx.filter fun k => ctr k = c).card := by
    intro c
    have hb := pure_star_center_bound hMin huniq c (Wc c)
      (fun w hw => by obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw; exact hW_lt k (Finset.mem_filter.mp hk).1)
      (fun w hw => by
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
        obtain ⟨hkI, hkc⟩ := Finset.mem_filter.mp hk
        rw [← hkc]; exact hW_sub k hkI)
      (fun w hw => by obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw; exact hW_pure k (Finset.mem_filter.mp hk).1)
    have hwc_le : (Wc c).card ≤ (Idx.filter fun k => ctr k = c).card := Finset.card_image_le
    exact hb.trans (Nat.add_le_add_left hwc_le _)
  have hsum_U : ∑ c : Fin 26, (Uc c).card ≤ (∑ c : Fin 26, (O_c C i c).card) + Idx.card := by
    have h1 := Finset.sum_le_sum (s := Finset.univ) fun c _ => hper_c c
    rw [Finset.sum_add_distrib, card_filter_sum Idx ctr] at h1
    exact h1
  have hcov_bi : pgEdges ⊆ (Finset.univ : Finset (Fin 26)).biUnion fun c => starEdgesOf c (Uc c) := by
    intro e he
    obtain ⟨k, hk, hke⟩ := hcov e he
    refine Finset.mem_biUnion.mpr ⟨ctr k, Finset.mem_univ _, ?_⟩
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hke
    refine Finset.mem_image.mpr ⟨v, Finset.mem_biUnion.mpr ⟨wire k, ?_, hv⟩, rfl⟩
    exact Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, rfl⟩, rfl⟩
  have h52 : 52 ≤ ∑ c : Fin 26, (Uc c).card := by
    calc 52 = pgEdges.card := pgEdges_card.symm
      _ ≤ ((Finset.univ : Finset (Fin 26)).biUnion fun c => starEdgesOf c (Uc c)).card :=
          Finset.card_le_card hcov_bi
      _ ≤ ∑ c : Fin 26, (starEdgesOf c (Uc c)).card := Finset.card_biUnion_le
      _ = ∑ c : Fin 26, (Uc c).card := by congr 1; ext c; exact starEdgesOf_card c (Uc c)
  omega

lemma one_mixed_center_bound {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    (Idx : Finset ℕ) (ctr : ℕ → Fin 26) (wire : ℕ → ℕ)
    (hW_lt : ∀ k ∈ Idx, wire k < 26 + C.gates.length)
    (hW_sub : ∀ k ∈ Idx, orIn 26 C (wire k) ⊆ nbrs (ctr k))
    (hW_pure : ∀ k ∈ Idx, ∀ h, OrReaches 26 C (wire k) h → (gateAt C h).op = GateOp.or → h ∈ O_pure C i)
    (c0 : Fin 26) (L0 : Finset (Fin 26)) (bonus extra_r : ℕ)
    (hcov : ∀ e ∈ pgEdges, (∃ k ∈ Idx, e ∈ starEdgesOf (ctr k) (orIn 26 C (wire k))) ∨
      e ∈ starEdgesOf c0 L0)
    (hc0_bound : (((Idx.filter fun k => ctr k = c0).image wire).biUnion (orIn 26 C) ∪ L0).card + bonus ≤
      (O_c C i c0).card + (O_extra C i).card + (Idx.filter fun k => ctr k = c0).card + extra_r) :
    52 + bonus ≤ (O_N C).card + Idx.card + extra_r := by
  let Wc : Fin 26 → Finset ℕ := fun c => (Idx.filter fun k => ctr k = c).image wire
  let Uc : Fin 26 → Finset (Fin 26) := fun c =>
    if c = c0 then (Wc c0).biUnion (orIn 26 C) ∪ L0 else (Wc c).biUnion (orIn 26 C)
  have hper_ne : ∀ c ∈ (Finset.univ : Finset (Fin 26)).erase c0,
      (Uc c).card ≤ (O_c C i c).card + (Idx.filter fun k => ctr k = c).card := by
    intro c hc
    have hne : c ≠ c0 := (Finset.mem_erase.mp hc).1
    simp only [Uc, hne, ↓reduceIte]
    have hb := pure_star_center_bound hMin huniq c (Wc c)
      (fun w hw => by obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw; exact hW_lt k (Finset.mem_filter.mp hk).1)
      (fun w hw => by
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw
        obtain ⟨hkI, hkc⟩ := Finset.mem_filter.mp hk
        rw [← hkc]; exact hW_sub k hkI)
      (fun w hw => by obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hw; exact hW_pure k (Finset.mem_filter.mp hk).1)
    have hwc_le : (Wc c).card ≤ (Idx.filter fun k => ctr k = c).card := Finset.card_image_le
    exact hb.trans (Nat.add_le_add_left hwc_le _)
  have hsum_ne := Finset.sum_le_sum hper_ne
  rw [Finset.sum_add_distrib] at hsum_ne
  have hsum_all : ∑ c : Fin 26, (Uc c).card + bonus ≤ (O_N C).card + Idx.card + extra_r := by
    have h1 : ∑ c : Fin 26, (Uc c).card = (Uc c0).card + ∑ c ∈ Finset.univ.erase c0, (Uc c).card :=
      (Finset.add_sum_erase Finset.univ (fun c => (Uc c).card) (Finset.mem_univ c0)).symm
    have h2 : ∑ c : Fin 26, (O_c C i c).card =
        (O_c C i c0).card + ∑ c ∈ Finset.univ.erase c0, (O_c C i c).card :=
      (Finset.add_sum_erase Finset.univ (fun c => (O_c C i c).card) (Finset.mem_univ c0)).symm
    have h3 : ∑ c : Fin 26, (Idx.filter fun k => ctr k = c).card =
        (Idx.filter fun k => ctr k = c0).card +
        ∑ c ∈ Finset.univ.erase c0, (Idx.filter fun k => ctr k = c).card :=
      (Finset.add_sum_erase Finset.univ (fun c => (Idx.filter fun k => ctr k = c).card) (Finset.mem_univ c0)).symm
    have hpart := card_filter_sum Idx ctr
    have hoN := oN_card_eq hMin huniq
    have hc0_eq : (Uc c0).card = (((Idx.filter fun k => ctr k = c0).image wire).biUnion (orIn 26 C) ∪ L0).card := by
      simp [Uc, Wc]
    omega
  have hcov_bi : pgEdges ⊆ (Finset.univ : Finset (Fin 26)).biUnion fun c => starEdgesOf c (Uc c) := by
    intro e he
    rcases hcov e he with ⟨k, hk, hke⟩ | he0
    · refine Finset.mem_biUnion.mpr ⟨ctr k, Finset.mem_univ _, ?_⟩
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hke
      refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
      have hmem_bi : v ∈ (Wc (ctr k)).biUnion (orIn 26 C) :=
        Finset.mem_biUnion.mpr ⟨wire k, Finset.mem_image.mpr ⟨k, Finset.mem_filter.mpr ⟨hk, rfl⟩, rfl⟩, hv⟩
      by_cases hkc : ctr k = c0
      · simp only [Uc, hkc, ↓reduceIte]
        exact Finset.mem_union_left _ (hkc ▸ hmem_bi)
      · simp only [Uc, hkc, ↓reduceIte]; exact hmem_bi
    · refine Finset.mem_biUnion.mpr ⟨c0, Finset.mem_univ _, ?_⟩
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp he0
      refine Finset.mem_image.mpr ⟨v, ?_, rfl⟩
      simp only [Uc, ↓reduceIte]
      exact Finset.mem_union_right _ hv
  have h52 : 52 ≤ ∑ c : Fin 26, (Uc c).card := by
    calc 52 = pgEdges.card := pgEdges_card.symm
      _ ≤ ((Finset.univ : Finset (Fin 26)).biUnion fun c => starEdgesOf c (Uc c)).card :=
          Finset.card_le_card hcov_bi
      _ ≤ ∑ c : Fin 26, (starEdgesOf c (Uc c)).card := Finset.card_biUnion_le
      _ = ∑ c : Fin 26, (Uc c).card := by congr 1; ext c; exact starEdgesOf_card c (Uc c)
  omega

lemma oC_disj_oExtra (C : Circuit) (i : ℕ) (c0 : Fin 26) :
    (O_c C i c0 ∪ O_extra C i).card = (O_c C i c0).card + (O_extra C i).card := by
  apply Finset.card_union_of_disjoint
  rw [Finset.disjoint_left]
  intro h h1 h2
  unfold O_extra at h2
  rw [Finset.mem_sdiff] at h2
  exact h2.2 (Finset.mem_biUnion.mpr ⟨c0, Finset.mem_univ _, h1⟩)

lemma aGates_card_of_j_edges {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (hi : i < C.gates.length) (hj : j < C.gates.length)
    (hiand : (gateAt C i).op = GateOp.and) (hjand : (gateAt C j).op = GateOp.and)
    (hij_ne : i ≠ j)
    (hT_eq : T_gates C = (A_gates C).erase i)
    (Astar : Finset ℕ) (hAstar : Astar = ((A_gates C).erase i).erase j)
    (ctr : ℕ → Fin 26) (leaf : ℕ → Finset (Fin 26))
    (hleaf_le : ∀ a ∈ Astar, (leaf a).card ≤ 4)
    (hcov_a : ∀ a ∈ Astar, ∀ e ∈ pgEdges, gateVal 26 C a (pairInput e.1 e.2) = true →
      e ∈ starEdgesOf (ctr a) (leaf a))
    (Ej : Finset (Fin 26 × Fin 26))
    (hcov_j : ∀ e ∈ pgEdges, gateVal 26 C j (pairInput e.1 e.2) = true → e ∈ Ej) :
    52 ≤ 4 * Astar.card + Ej.card := by
  have hsub : pgEdges ⊆ Astar.biUnion (fun a => starEdgesOf (ctr a) (leaf a)) ∪ Ej := by
    intro e he
    obtain ⟨a, haT, hga⟩ := edge_accepted_by_T hMin he
    by_cases haj : a = j
    · subst haj; exact Finset.mem_union_right _ (hcov_j e he hga)
    · apply Finset.mem_union_left
      have haS : a ∈ Astar := by
        rw [hAstar, Finset.mem_erase, ← hT_eq]
        exact ⟨haj, haT⟩
      exact Finset.mem_biUnion.mpr ⟨a, haS, hcov_a a haS e he hga⟩
  have h1 : 52 ≤ (Astar.biUnion fun a => starEdgesOf (ctr a) (leaf a)).card + Ej.card := by
    calc 52 = pgEdges.card := pgEdges_card.symm
      _ ≤ (Astar.biUnion (fun a => starEdgesOf (ctr a) (leaf a)) ∪ Ej).card := Finset.card_le_card hsub
      _ ≤ _ := Finset.card_union_le _ _
  have h2 : (Astar.biUnion fun a => starEdgesOf (ctr a) (leaf a)).card ≤ 4 * Astar.card := by
    calc (Astar.biUnion fun a => starEdgesOf (ctr a) (leaf a)).card
        ≤ ∑ a ∈ Astar, (starEdgesOf (ctr a) (leaf a)).card := Finset.card_biUnion_le
      _ ≤ ∑ _a ∈ Astar, 4 := Finset.sum_le_sum fun a ha => by rw [starEdgesOf_card]; exact hleaf_le a ha
      _ = 4 * Astar.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
  omega

lemma case_both_reach {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (hi : i < C.gates.length) (hj : j < C.gates.length)
    (hiand : (gateAt C i).op = GateOp.and) (hjand : (gateAt C j).op = GateOp.and)
    (hij_ne : i ≠ j)
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    (hT_eq : T_gates C = (A_gates C).erase i)
    (hOout_ge : (A_gates C).card ≤ (O_out C).card + 2)
    (hr0 : OrReaches 26 C (opnd C j 0) i) (hr1 : OrReaches 26 C (opnd C j 1) i) :
    64 ≤ C.size := by
  classical
  have hAO := min_isAO2 hMin
  have hjT : j ∈ T_gates C := by
    rw [hT_eq]; exact Finset.mem_erase.mpr ⟨hij_ne.symm, mem_A_gates.mpr ⟨hj, hjand⟩⟩
  have hj_below := below_of_mem_T hMin hjT
  have hi_below : ∀ u v : Fin 26, pgAdj u v = false → gateVal 26 C i (pairInput u v) = false := by
    intro u v hnadj
    rw [Bool.eq_false_iff]
    intro hit
    have hjt : gateVal 26 C j (pairInput u v) = true :=
      (j_eval hMin hj hjand huniq _).mpr ⟨Or.inl ⟨hr0, hit⟩, Or.inl ⟨hr1, hit⟩⟩
    rw [hj_below u v hnadj] at hjt; cases hjt

  set Anj := (A_gates C).erase j
  have hAnj_card : Anj.card = (A_gates C).card - 1 := by
    rw [Finset.card_erase_of_mem (mem_A_gates.mpr ⟨hj, hjand⟩)]
  have hAnj_spec : ∀ a ∈ Anj, ∃ (c : Fin 26) (s : Fin 2),
      side (n := 26) C a (1 - s) = {c} ∧ side (n := 26) C a s ⊆ nbrs c ∧
      (side (n := 26) C a s).Nonempty ∧
      ∀ e ∈ pgEdges, gateVal 26 C a (pairInput e.1 e.2) = true →
        e ∈ starEdgesOf c (side (n := 26) C a s) := by
    intro a ha
    obtain ⟨hanej, haA⟩ := Finset.mem_erase.mp ha
    obtain ⟨ha_lt, ha_and⟩ := mem_A_gates.mp haA
    apply pure_star_spec hMin huniq ha_lt ha_and hanej
    by_cases hai : a = i
    · subst hai; exact hi_below
    · exact below_of_mem_T hMin (by rw [hT_eq]; exact Finset.mem_erase.mpr ⟨hai, haA⟩)
  let ctr : ℕ → Fin 26 := fun a => if h : a ∈ Anj then (hAnj_spec a h).choose else 0
  let sfn : ℕ → Fin 2 := fun a => if h : a ∈ Anj then (hAnj_spec a h).choose_spec.choose else 0
  let wire : ℕ → ℕ := fun a => opnd C a (sfn a)
  have hW_lt : ∀ a ∈ Anj, wire a < 26 + C.gates.length := by
    intro a ha
    have ha_lt := (mem_A_gates.mp (Finset.mem_erase.mp ha).2).1
    have := opnd_lt hAO ha_lt (sfn a)
    dsimp only [wire]; omega
  have hW_sub : ∀ a ∈ Anj, orIn 26 C (wire a) ⊆ nbrs (ctr a) := by
    intro a ha
    simp only [wire, ctr, sfn, ha, ↓reduceDIte]
    exact (hAnj_spec a ha).choose_spec.choose_spec.2.1
  have hW_pure : ∀ a ∈ Anj, ∀ h, OrReaches 26 C (wire a) h → (gateAt C h).op = GateOp.or → h ∈ O_pure C i := by
    intro a ha h hhr hhor
    obtain ⟨hanej, haA⟩ := Finset.mem_erase.mp ha
    obtain ⟨ha_lt, ha_and⟩ := mem_A_gates.mp haA
    exact opnd_or_in_Opure_of_ne_j hMin hi hiand huniq ha_lt ha_and hanej (sfn a) hhr hhor
  have hcov_Anj : ∀ a ∈ Anj, ∀ e ∈ pgEdges, gateVal 26 C a (pairInput e.1 e.2) = true →
      e ∈ starEdgesOf (ctr a) (orIn 26 C (wire a)) := by
    intro a ha e he hga
    simp only [wire, ctr, sfn, ha, ↓reduceDIte]
    exact (hAnj_spec a ha).choose_spec.choose_spec.2.2.2 e he hga

  set Aj := side (n := 26) C j 0
  set Bj := side (n := 26) C j 1
  have hAB_adj : ∀ u ∈ Aj, ∀ v ∈ Bj, pgAdj u v = true := by
    intro u hu v hv
    cases h : pgAdj u v
    · exfalso
      have hjt : gateVal 26 C j (pairInput u v) = true :=
        (j_eval hMin hj hjand huniq _).mpr ⟨Or.inr ⟨u, hu, by simp [pairInput]⟩, Or.inr ⟨v, hv, by simp [pairInput]⟩⟩
      rw [hj_below u v h] at hjt; cases hjt
    · rfl

  have hop_ne_i : ∀ s : Fin 2, opnd C j s ≠ 26 + i := by
    intro s heq
    have hilt : 26 + i < 26 + j := by have := opnd_lt hAO hj s; omega
    apply min_no_eq_wire hMin hj hilt
    intro x
    apply Bool.eq_iff_iff.mpr
    change gateVal 26 C j x = true ↔ gateVal 26 C i x = true
    rw [j_eval hMin hj hjand huniq x]
    fin_cases s
    · have heq0 : opnd C j 0 = 26 + i := heq
      have hemp : side (n := 26) C j 0 = ∅ := by
        change orIn 26 C (opnd C j 0) = ∅; rw [heq0]; exact orIn_gate_and C hi hiand
      simp only [hemp, Finset.notMem_empty, false_and, exists_false, or_false, hr0, hr1, true_and]
      tauto
    · have heq1 : opnd C j 1 = 26 + i := heq
      have hemp : side (n := 26) C j 1 = ∅ := by
        change orIn 26 C (opnd C j 1) = ∅; rw [heq1]; exact orIn_gate_and C hi hiand
      simp only [hemp, Finset.notMem_empty, false_and, exists_false, or_false, hr0, hr1, true_and]
      tauto

  have hop_extra : ∀ s : Fin 2, ∃ h ∈ O_extra C i, opnd C j s = 26 + h := by
    intro s
    have hri_s : OrReaches 26 C (opnd C j s) i := by fin_cases s <;> assumption
    have h26 := hri_s.1
    have hlt := opnd_lt hAO hj s
    set h := opnd C j s - 26
    have hh_lt : h < C.gates.length := by omega
    have hwh : opnd C j s = 26 + h := by omega
    have hhor : (gateAt C h).op = GateOp.or := by
      rcases hAO.1 _ (gateAt_mem hh_lt) with hand | hor
      · exfalso
        rw [hwh, orReaches_gate_iff 26 C hh_lt i] at hri_s
        rcases hri_s with rfl | ⟨hor', _⟩
        · exact hop_ne_i s hwh
        · rw [hand] at hor'; cases hor'
      · exact hor
    have hhN := opnd_or_in_ON hMin huniq hj hjand s (by rw [hwh]; exact orReaches_self 26 C hh_lt) hhor
    refine ⟨h, ?_, hwh⟩
    unfold O_extra
    rw [Finset.mem_sdiff]
    refine ⟨hhN, fun hbi => ?_⟩
    obtain ⟨c, _, hhc⟩ := Finset.mem_biUnion.mp hbi
    exact (mem_O_pure.mp (Finset.mem_filter.mp hhc).1).2 (by rwa [← hwh])
  have hex_ge2 : 2 ≤ (O_extra C i).card := by
    obtain ⟨h0, hh0, heq0⟩ := hop_extra 0
    obtain ⟨h1, hh1, heq1⟩ := hop_extra 1
    have hne : h0 ≠ h1 := by
      intro heq; apply min_opnd_ne hMin hj; rw [heq0, heq1, heq]
    have hsub : ({h0, h1} : Finset ℕ) ⊆ O_extra C i := by
      intro x hx; simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl <;> assumption
    calc 2 = ({h0, h1} : Finset ℕ).card := (Finset.card_pair hne).symm
      _ ≤ (O_extra C i).card := Finset.card_le_card hsub
  have hsize := size_eq_A_Oout_ON hAO
  have hoN := oN_card_eq hMin huniq
  by_cases hAB_ne : Aj.Nonempty ∧ Bj.Nonempty
  ·
    have hstar_j : ∃ (c0 : Fin 26) (s0 : Fin 2),
        side (n := 26) C j (1 - s0) = {c0} ∧ side (n := 26) C j s0 ⊆ nbrs c0 ∧
        ∀ e ∈ pgEdges, gateVal 26 C j (pairInput e.1 e.2) = true →
          gateVal 26 C i (pairInput e.1 e.2) = true ∨ e ∈ starEdgesOf c0 (side (n := 26) C j s0) := by
      rcases biclique_is_star hAB_adj with h0 | h1
      · have h0eq : Aj.card = 1 := le_antisymm h0 (Finset.card_pos.mpr hAB_ne.1)
        obtain ⟨c0, hc0⟩ := Finset.card_eq_one.mp h0eq
        refine ⟨c0, 1, by simpa using hc0, fun v hv => (mem_nbrs_iff c0 v).mpr (hAB_adj c0 (by rw [hc0]; simp) v hv), ?_⟩
        intro e he hjt
        obtain ⟨hleft, hright⟩ := (j_eval hMin hj hjand huniq _).mp hjt
        rcases hleft with ⟨_, hit⟩ | ⟨u, hu, hup⟩
        · exact Or.inl hit
        · rcases hright with ⟨_, hit⟩ | ⟨v, hv, hvp⟩
          · exact Or.inl hit
          · right
            change u ∈ Aj at hu
            rw [hc0, Finset.mem_singleton] at hu; subst u
            simp only [pairInput, decide_eq_true_eq] at hup hvp
            have hne_cv : c0 ≠ v := fun heq => by
              subst heq; have := hAB_adj c0 (by rw [hc0]; simp) c0 hv; rw [pgAdj_irrefl] at this; cases this
            have hadj_e := (mem_pgEdges_iff e).mp he |>.2
            rw [← dirEdge_eq_of_mem_pgEdges he]
            rcases hup with h1c | h2c <;> rcases hvp with h1' | h2'
            · exact (hne_cv (h1c.trans h1'.symm)).elim
            · rw [← h1c, ← h2']; exact mem_starEdgesOf_left hv
            · rw [← h1', ← h2c] at hadj_e ⊢; exact mem_starEdgesOf_right hadj_e hv
            · exact (hne_cv (h2c.trans h2'.symm)).elim
      · have h1eq : Bj.card = 1 := le_antisymm h1 (Finset.card_pos.mpr hAB_ne.2)
        obtain ⟨c0, hc0⟩ := Finset.card_eq_one.mp h1eq
        refine ⟨c0, 0, by simpa using hc0, fun u hu => (mem_nbrs_iff c0 u).mpr (by rw [pgAdj_symm]; exact hAB_adj u hu c0 (by rw [hc0]; simp)), ?_⟩
        intro e he hjt
        obtain ⟨hleft, hright⟩ := (j_eval hMin hj hjand huniq _).mp hjt
        rcases hleft with ⟨_, hit⟩ | ⟨u, hu, hup⟩
        · exact Or.inl hit
        · rcases hright with ⟨_, hit⟩ | ⟨v, hv, hvp⟩
          · exact Or.inl hit
          · right
            change v ∈ Bj at hv
            rw [hc0, Finset.mem_singleton] at hv; subst v
            simp only [pairInput, decide_eq_true_eq] at hup hvp
            have hne_uc : u ≠ c0 := fun heq => by
              subst heq; have := hAB_adj u hu u (by rw [hc0]; simp); rw [pgAdj_irrefl] at this; cases this
            have hadj_e := (mem_pgEdges_iff e).mp he |>.2
            rw [← dirEdge_eq_of_mem_pgEdges he]
            rcases hup with h1u | h2u <;> rcases hvp with h1' | h2'
            · exact (hne_uc (h1u.trans h1'.symm)).elim
            · rw [← h1u, ← h2'] at hadj_e ⊢; exact mem_starEdgesOf_right hadj_e hu
            · rw [← h2u, ← h1']; exact mem_starEdgesOf_left hu
            · exact (hne_uc (h2u.trans h2'.symm)).elim
    obtain ⟨c0, s0, hs0_ctr, hs0_sub, hcov_j⟩ := hstar_j
    set L0 := side (n := 26) C j s0

    have hA_ge13 : 13 ≤ (A_gates C).card := by
      have hsub : pgEdges ⊆ Anj.biUnion (fun a => starEdgesOf (ctr a) (orIn 26 C (wire a))) ∪ starEdgesOf c0 L0 := by
        intro e he
        obtain ⟨a, haT, hga⟩ := edge_accepted_by_T hMin he
        by_cases haj : a = j
        · subst haj
          rcases hcov_j e he hga with hit | hej
          · apply Finset.mem_union_left
            have hiAnj : i ∈ Anj := Finset.mem_erase.mpr ⟨hij_ne, mem_A_gates.mpr ⟨hi, hiand⟩⟩
            exact Finset.mem_biUnion.mpr ⟨i, hiAnj, hcov_Anj i hiAnj e he hit⟩
          · exact Finset.mem_union_right _ hej
        · apply Finset.mem_union_left
          have haAnj : a ∈ Anj := Finset.mem_erase.mpr ⟨haj, (Finset.mem_erase.mp (hT_eq ▸ haT)).2⟩
          exact Finset.mem_biUnion.mpr ⟨a, haAnj, hcov_Anj a haAnj e he hga⟩
      have h1 : 52 ≤ (Anj.biUnion fun a => starEdgesOf (ctr a) (orIn 26 C (wire a))).card + (starEdgesOf c0 L0).card := by
        calc 52 = pgEdges.card := pgEdges_card.symm
          _ ≤ _ := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
      have h2 : (Anj.biUnion fun a => starEdgesOf (ctr a) (orIn 26 C (wire a))).card ≤ 4 * Anj.card := by
        calc _ ≤ ∑ a ∈ Anj, (starEdgesOf (ctr a) (orIn 26 C (wire a))).card := Finset.card_biUnion_le
          _ ≤ ∑ _a ∈ Anj, 4 := Finset.sum_le_sum fun a ha => starEdgesOf_card_le_four (hW_sub a ha)
          _ = 4 * Anj.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      have h3 : (starEdgesOf c0 L0).card ≤ 4 := starEdgesOf_card_le_four hs0_sub
      omega

    have hmb : 52 + 2 ≤ (O_N C).card + Anj.card + 1 := by
      apply one_mixed_center_bound hMin huniq Anj ctr wire hW_lt hW_sub hW_pure c0 L0 2 1
      · intro e he
        obtain ⟨a, haT, hga⟩ := edge_accepted_by_T hMin he
        by_cases haj : a = j
        · subst haj
          rcases hcov_j e he hga with hit | hej
          · left
            have hiAnj : i ∈ Anj := Finset.mem_erase.mpr ⟨hij_ne, mem_A_gates.mpr ⟨hi, hiand⟩⟩
            exact ⟨i, hiAnj, hcov_Anj i hiAnj e he hit⟩
          · exact Or.inr hej
        · left
          have haAnj : a ∈ Anj := Finset.mem_erase.mpr ⟨haj, (Finset.mem_erase.mp (hT_eq ▸ haT)).2⟩
          exact ⟨a, haAnj, hcov_Anj a haAnj e he hga⟩
      ·
        set Anj0 := Anj.filter fun a => ctr a = c0
        set W0 := Anj0.image wire
        set U0 := W0.biUnion (orIn 26 C) ∪ L0
        have hU0_nbr : U0 ⊆ nbrs c0 := Finset.union_subset (by
          intro v hv
          obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp hv
          obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
          obtain ⟨haAnj, hac⟩ := Finset.mem_filter.mp ha
          rw [← hac]; exact hW_sub a haAnj hvw) hs0_sub
        set Lmix : Finset (Option (Fin 26)) := U0.image some ∪ {some c0, none}
        have hLmix_card : Lmix.card = U0.card + 2 := by
          have hc0_not : c0 ∉ U0 := fun hmem => by
            have := (mem_nbrs_iff c0 c0).mp (hU0_nbr hmem); rw [pgAdj_irrefl] at this; cases this
          have hdisj : Disjoint (U0.image some) ({some c0, none} : Finset (Option (Fin 26))) := by
            rw [Finset.disjoint_left]
            intro x hx1 hx2
            obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hx1
            simp only [Finset.mem_insert, Finset.mem_singleton, Option.some.injEq, reduceCtorEq, or_false] at hx2
            exact hc0_not (hx2 ▸ hu)
          rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injective _ (Option.some_injective (Fin 26)),
            Finset.card_pair (by simp)]
        set Wall := W0 ∪ {opnd C j 0, opnd C j 1}
        obtain ⟨E, hElen, hconn⟩ := mixed_center_conn hMin (j := j) hi hiand c0 Lmix
          (Finset.union_subset_union_left (Finset.image_subset_image hU0_nbr))
          Wall
          (fun w hw => by
            rcases Finset.mem_union.mp hw with hw0 | hwj
            · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw0
              exact hW_lt a (Finset.mem_filter.mp ha).1
            · simp only [Finset.mem_insert, Finset.mem_singleton] at hwj
              rcases hwj with rfl | rfl
              · have := opnd_lt hAO hj 0; omega
              · have := opnd_lt hAO hj 1; omega)
          (fun w hw h hwr hor => by
            rcases Finset.mem_union.mp hw with hw0 | hwj
            · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw0
              exact (mem_O_pure.mp (hW_pure a (Finset.mem_filter.mp ha).1 h hwr hor)).1
            · simp only [Finset.mem_insert, Finset.mem_singleton] at hwj
              rcases hwj with rfl | rfl
              · exact opnd_or_in_ON hMin huniq hj hjand 0 hwr hor
              · exact opnd_or_in_ON hMin huniq hj hjand 1 hwr hor)
        let W0ne := W0.filter fun w => (orIn 26 C w).Nonempty
        let R0 : Finset (Option (Fin 26)) := W0ne.attach.image fun w => some (Finset.mem_filter.mp w.2).2.choose
        let R : Finset (Option (Fin 26)) := insert none R0
        have hR_card : R.card ≤ Anj0.card + 1 := by
          have h1 : R0.card ≤ W0.card := Finset.card_image_le.trans
            (by rw [Finset.card_attach]; exact Finset.card_filter_le _ _)
          have h2 : W0.card ≤ Anj0.card := Finset.card_image_le
          have h3 : R.card ≤ R0.card + 1 := Finset.card_insert_le _ _
          omega
        have hr_s0 : OrReaches 26 C (opnd C j s0) i := by fin_cases s0 <;> assumption
        have hr_1s0 : OrReaches 26 C (opnd C j (1 - s0)) i := by fin_cases s0 <;> assumption
        have hmem_s0 : opnd C j s0 ∈ Wall := by
          apply Finset.mem_union_right; fin_cases s0 <;> simp
        have hmem_1s0 : opnd C j (1 - s0) ∈ Wall := by
          apply Finset.mem_union_right; fin_cases s0 <;> simp
        have hnone_L : (none : Option (Fin 26)) ∈ Lmix := by simp [Lmix]
        have hcov_R : ∀ x ∈ Lmix, ∃ r ∈ R, EdgeReach E x r := by
          intro x hx
          rcases Finset.mem_union.mp hx with hxu | hx2
          · obtain ⟨u, huU0, rfl⟩ := Finset.mem_image.mp hxu
            rcases Finset.mem_union.mp huU0 with huW | huL0
            · obtain ⟨w, hwW0, huw⟩ := Finset.mem_biUnion.mp huW
              have hwne : w ∈ W0ne := Finset.mem_filter.mpr ⟨hwW0, ⟨u, huw⟩⟩
              let r0 := (Finset.mem_filter.mp hwne).2.choose
              have hr0_w : r0 ∈ orIn 26 C w := (Finset.mem_filter.mp hwne).2.choose_spec
              have hr0_U0 : r0 ∈ U0 := Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨w, hwW0, hr0_w⟩)
              refine ⟨some r0, Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨⟨w, hwne⟩, Finset.mem_attach _ _, rfl⟩), ?_⟩
              apply hconn w (Finset.mem_union_left _ hwW0)
              · exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, huw, rfl⟩), hx⟩
              · exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r0, hr0_w, rfl⟩),
                  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r0, hr0_U0, rfl⟩)⟩
            · refine ⟨none, Finset.mem_insert_self _ _, ?_⟩
              apply hconn (opnd C j s0) hmem_s0
              · exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, huL0, rfl⟩), hx⟩
              · exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ (by simp [hr_s0]), hnone_L⟩
          · simp only [Finset.mem_insert, Finset.mem_singleton] at hx2
            rcases hx2 with rfl | rfl
            · refine ⟨none, Finset.mem_insert_self _ _, ?_⟩
              apply hconn (opnd C j (1 - s0)) hmem_1s0
              · have hc0_mem : c0 ∈ orIn 26 C (opnd C j (1 - s0)) := by
                  change c0 ∈ side (n := 26) C j (1 - s0); rw [hs0_ctr]; simp
                exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨c0, hc0_mem, rfl⟩), hx⟩
              · exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ (by simp [hr_1s0]), hnone_L⟩
            · exact ⟨none, Finset.mem_insert_self _ _, Relation.ReflTransGen.refl⟩
        have hb := graph_spanning_bound E Lmix R hcov_R
        rw [hLmix_card] at hb
        rw [oC_disj_oExtra] at hElen
        omega
    change 64 ≤ C.gates.length
    omega
  ·
    have hcov_all : ∀ e ∈ pgEdges, ∃ a ∈ Anj, e ∈ starEdgesOf (ctr a) (orIn 26 C (wire a)) := by
      intro e he
      obtain ⟨a, haT, hga⟩ := edge_accepted_by_T hMin he
      by_cases haj : a = j
      · subst haj
        obtain ⟨hleft, hright⟩ := (j_eval hMin hj hjand huniq _).mp hga
        have hit : gateVal 26 C i (pairInput e.1 e.2) = true := by
          by_cases hAj : Aj.Nonempty
          · have hBj : Bj = ∅ := Finset.not_nonempty_iff_eq_empty.mp fun h => hAB_ne ⟨hAj, h⟩
            rcases hright with ⟨_, h⟩ | ⟨v, hv, _⟩
            · exact h
            · change v ∈ Bj at hv; rw [hBj] at hv; exact (Finset.notMem_empty v hv).elim
          · have hAj' : Aj = ∅ := Finset.not_nonempty_iff_eq_empty.mp hAj
            rcases hleft with ⟨_, h⟩ | ⟨u, hu, _⟩
            · exact h
            · change u ∈ Aj at hu; rw [hAj'] at hu; exact (Finset.notMem_empty u hu).elim
        have hiAnj : i ∈ Anj := Finset.mem_erase.mpr ⟨hij_ne, mem_A_gates.mpr ⟨hi, hiand⟩⟩
        exact ⟨i, hiAnj, hcov_Anj i hiAnj e he hit⟩
      · have haAnj : a ∈ Anj := Finset.mem_erase.mpr ⟨haj, (Finset.mem_erase.mp (hT_eq ▸ haT)).2⟩
        exact ⟨a, haAnj, hcov_Anj a haAnj e he hga⟩
    have hA_ge14 : 14 ≤ (A_gates C).card := by
      have hsub : pgEdges ⊆ Anj.biUnion fun a => starEdgesOf (ctr a) (orIn 26 C (wire a)) := by
        intro e he; obtain ⟨a, ha, hmem⟩ := hcov_all e he
        exact Finset.mem_biUnion.mpr ⟨a, ha, hmem⟩
      have h52 : 52 ≤ 4 * Anj.card := by
        calc 52 = pgEdges.card := pgEdges_card.symm
          _ ≤ (Anj.biUnion fun a => starEdgesOf (ctr a) (orIn 26 C (wire a))).card := Finset.card_le_card hsub
          _ ≤ ∑ a ∈ Anj, (starEdgesOf (ctr a) (orIn 26 C (wire a))).card := Finset.card_biUnion_le
          _ ≤ ∑ _a ∈ Anj, 4 := Finset.sum_le_sum fun a ha => starEdgesOf_card_le_four (hW_sub a ha)
          _ = 4 * Anj.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]
      omega
    have hpf := pure_family_sum_bound hMin huniq Anj ctr wire hW_lt hW_sub hW_pure hcov_all
    change 64 ≤ C.gates.length
    omega

lemma case2_sub22 {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (hi : i < C.gates.length) (hj : j < C.gates.length)
    (hiand : (gateAt C i).op = GateOp.and) (hjand : (gateAt C j).op = GateOp.and)
    (hij_ne : i ≠ j)
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    (hT_eq : T_gates C = (A_gates C).erase i)
    (hOout_ge : (A_gates C).card ≤ (O_out C).card + 2)
    (b : Fin 2) (hb_r : OrReaches 26 C (opnd C j b) i) (hnb_r : ¬ OrReaches 26 C (opnd C j (1 - b)) i)
    (Astar : Finset ℕ) (hAstar : Astar = ((A_gates C).erase i).erase j)
    (ctr : ℕ → Fin 26) (wire : ℕ → ℕ)
    (hW_lt : ∀ a ∈ Astar, wire a < 26 + C.gates.length)
    (hW_sub : ∀ a ∈ Astar, orIn 26 C (wire a) ⊆ nbrs (ctr a))
    (hW_pure : ∀ a ∈ Astar, ∀ h, OrReaches 26 C (wire a) h → (gateAt C h).op = GateOp.or → h ∈ O_pure C i)
    (hcov_Astar : ∀ a ∈ Astar, ∀ e ∈ pgEdges, gateVal 26 C a (pairInput e.1 e.2) = true →
      e ∈ starEdgesOf (ctr a) (orIn 26 C (wire a)))
    (si : Fin 2) (c1 c2 : Fin 26)
    (hc1_mem : c1 ∈ side (n := 26) C j b ∪ (side (n := 26) C i si ∩ side (n := 26) C i (1 - si)))
    (hc2_mem : c2 ∈ side (n := 26) C i si ∩ side (n := 26) C j (1 - b))
    (hBj_sub : side (n := 26) C j (1 - b) ⊆ nbrs c1)
    (hBi_sub : side (n := 26) C i (1 - si) ⊆ nbrs c2)
    (hcov_j : ∀ e ∈ pgEdges, gateVal 26 C j (pairInput e.1 e.2) = true →
      e ∈ starEdgesOf c1 (side (n := 26) C j (1 - b)) ∪ starEdgesOf c2 (side (n := 26) C i (1 - si))) :
    64 ≤ C.size := by
  have hAO := min_isAO2 hMin
  have hAstar_card : Astar.card = (A_gates C).card - 2 := by
    rw [hAstar, Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hij_ne.symm, mem_A_gates.mpr ⟨hj, hjand⟩⟩),
      Finset.card_erase_of_mem (mem_A_gates.mpr ⟨hi, hiand⟩)]
    omega

  have hEj_le7 : (starEdgesOf c1 (side (n := 26) C j (1 - b)) ∪
      starEdgesOf c2 (side (n := 26) C i (1 - si))).card ≤ 7 := by
    have hadj12 : pgAdj c1 c2 = true := (mem_nbrs_iff c1 c2).mp (hBj_sub (Finset.mem_inter.mp hc2_mem).2)
    by_cases hc1_in : c1 ∈ side (n := 26) C i (1 - si)
    · have hsh : dirEdge c1 c2 ∈ starEdgesOf c1 (side (n := 26) C j (1 - b)) ∩
          starEdgesOf c2 (side (n := 26) C i (1 - si)) := by
        refine Finset.mem_inter.mpr ⟨mem_starEdgesOf_left (Finset.mem_inter.mp hc2_mem).2, ?_⟩
        exact mem_starEdgesOf_right hadj12 hc1_in
      have hinter_pos : 1 ≤ (starEdgesOf c1 (side (n := 26) C j (1 - b)) ∩
          starEdgesOf c2 (side (n := 26) C i (1 - si))).card := Finset.card_pos.mpr ⟨_, hsh⟩
      have hu := Finset.card_union_add_card_inter (starEdgesOf c1 (side (n := 26) C j (1 - b)))
        (starEdgesOf c2 (side (n := 26) C i (1 - si)))
      have h4a := starEdgesOf_card_le_four hBj_sub
      have h4b := starEdgesOf_card_le_four hBi_sub
      omega
    · have hsub_er : side (n := 26) C i (1 - si) ⊆ (nbrs c2).erase c1 := by
        intro v hv
        exact Finset.mem_erase.mpr ⟨fun heq => hc1_in (heq ▸ hv), hBi_sub hv⟩
      have hc1_nbr : c1 ∈ nbrs c2 := (mem_nbrs_iff c2 c1).mpr (by rw [pgAdj_symm]; exact hadj12)
      have h3 : (side (n := 26) C i (1 - si)).card ≤ 3 := by
        have := Finset.card_le_card hsub_er
        rw [Finset.card_erase_of_mem hc1_nbr, nbrs_card c2] at this; omega
      have h4a := starEdgesOf_card_le_four hBj_sub
      have hu := Finset.card_union_le (starEdgesOf c1 (side (n := 26) C j (1 - b)))
        (starEdgesOf c2 (side (n := 26) C i (1 - si)))
      rw [starEdgesOf_card c2] at hu
      omega
  have h52 := aGates_card_of_j_edges hMin hi hj hiand hjand hij_ne hT_eq Astar hAstar
    ctr (fun a => orIn 26 C (wire a))
    (fun a ha => (Finset.card_le_card (hW_sub a ha)).trans (nbrs_card _).le)
    hcov_Astar _ hcov_j
  have hA_ge14 : 14 ≤ (A_gates C).card := by omega

  have hex_ge1 : 1 ≤ (O_extra C i).card := by
    rcases Finset.mem_union.mp hc1_mem with hc1Aj | hc1AiBi
    · apply extra_of_reaches_i_and_input hMin hiand (w := opnd C j b) (by have := opnd_lt hAO hj b; omega)
        hb_r ⟨c1, hc1Aj⟩
      intro h hhr hor; exact opnd_or_in_ON hMin huniq hj hjand b hhr hor
    · have hadj12 : pgAdj c1 c2 = true := (mem_nbrs_iff c1 c2).mp (hBj_sub (Finset.mem_inter.mp hc2_mem).2)
      apply extra_of_mixed_bipartite hMin (w := opnd C i si) (by have := opnd_lt hAO hi si; omega)
        (fun h hhr hor => opnd_or_in_ON hMin huniq hi hiand si hhr hor)
        (Finset.mem_inter.mp hc1AiBi).1 (Finset.mem_inter.mp hc2_mem).1 (pgAdj_bip c1 c2 hadj12)

  have hi_notA : i ∉ Astar := by rw [hAstar]; simp
  have hj_notA : j ∉ Astar := by rw [hAstar]; simp
  set Idx := insert i (insert j Astar)
  have hIdx_card : Idx.card = (A_gates C).card := by
    have heq : Idx = A_gates C := by
      ext x
      simp only [Idx, hAstar, Finset.mem_insert, Finset.mem_erase]
      constructor
      · rintro (rfl | rfl | ⟨_, _, hx⟩)
        · exact mem_A_gates.mpr ⟨hi, hiand⟩
        · exact mem_A_gates.mpr ⟨hj, hjand⟩
        · exact hx
      · intro hx
        by_cases hxi : x = i
        · exact Or.inl hxi
        · by_cases hxj : x = j
          · exact Or.inr (Or.inl hxj)
          · exact Or.inr (Or.inr ⟨hxj, hxi, hx⟩)
    rw [heq]
  let ctr' : ℕ → Fin 26 := fun k => if k = i then c2 else if k = j then c1 else ctr k
  let wire' : ℕ → ℕ := fun k => if k = i then opnd C i (1 - si) else if k = j then opnd C j (1 - b) else wire k
  have hpf : 52 ≤ (∑ c : Fin 26, (O_c C i c).card) + Idx.card := by
    apply pure_family_sum_bound hMin huniq Idx ctr' wire'
    · intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk1
      · simp only [wire', ↓reduceIte]; have := opnd_lt hAO hi (1 - si); omega
      · rcases Finset.mem_insert.mp hk1 with rfl | hkA
        · simp only [wire', hij_ne.symm, ↓reduceIte]; have := opnd_lt hAO hj (1 - b); omega
        · have hki : k ≠ i := fun h => hi_notA (h ▸ hkA)
          have hkj : k ≠ j := fun h => hj_notA (h ▸ hkA)
          simp only [wire', hki, hkj, ↓reduceIte]; exact hW_lt k hkA
    · intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk1
      · simp only [wire', ctr', ↓reduceIte]; exact hBi_sub
      · rcases Finset.mem_insert.mp hk1 with rfl | hkA
        · simp only [wire', ctr', hij_ne.symm, ↓reduceIte]; exact hBj_sub
        · have hki : k ≠ i := fun h => hi_notA (h ▸ hkA)
          have hkj : k ≠ j := fun h => hj_notA (h ▸ hkA)
          simp only [wire', ctr', hki, hkj, ↓reduceIte]; exact hW_sub k hkA
    · intro k hk h hhr hor
      rcases Finset.mem_insert.mp hk with rfl | hk1
      · simp only [wire', ↓reduceIte] at hhr
        exact opnd_or_in_Opure_of_ne_j hMin hi hiand huniq hi hiand hij_ne (1 - si) hhr hor
      · rcases Finset.mem_insert.mp hk1 with rfl | hkA
        · simp only [wire', hij_ne.symm, ↓reduceIte] at hhr
          exact opnd_or_in_Opure_of_not_reach_i hMin huniq hj hjand (1 - b) hnb_r hhr hor
        · have hki : k ≠ i := fun h => hi_notA (h ▸ hkA)
          have hkj : k ≠ j := fun h => hj_notA (h ▸ hkA)
          simp only [wire', hki, hkj, ↓reduceIte] at hhr
          exact hW_pure k hkA h hhr hor
    · intro e he
      obtain ⟨a, haT, hga⟩ := edge_accepted_by_T hMin he
      by_cases haj : a = j
      · subst a
        rcases Finset.mem_union.mp (hcov_j e he hga) with he1 | he2
        · refine ⟨j, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_⟩
          simp only [ctr', wire', hij_ne.symm, ↓reduceIte]; exact he1
        · refine ⟨i, Finset.mem_insert_self _ _, ?_⟩
          simp only [ctr', wire', ↓reduceIte]; exact he2
      · have haA : a ∈ Astar := by rw [hAstar, Finset.mem_erase, ← hT_eq]; exact ⟨haj, haT⟩
        have hai : a ≠ i := fun h => hi_notA (h ▸ haA)
        refine ⟨a, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem haA), ?_⟩
        simp only [ctr', wire', hai, haj, ↓reduceIte]
        exact hcov_Astar a haA e he hga
  have hsize := size_eq_A_Oout_ON hAO
  have hoN := oN_card_eq hMin huniq
  change 64 ≤ C.gates.length
  omega

lemma case_one_reach {C : Circuit} (hMin : IsMin C) {i j : ℕ}
    (hi : i < C.gates.length) (hj : j < C.gates.length)
    (hiand : (gateAt C i).op = GateOp.and) (hjand : (gateAt C j).op = GateOp.and)
    (hij_ne : i ≠ j)
    (huniq : ∀ a < C.gates.length, ∀ b < C.gates.length,
      (gateAt C a).op = GateOp.and → (gateAt C b).op = GateOp.and →
      InCone 26 C a b → a = i ∧ b = j)
    (hT_eq : T_gates C = (A_gates C).erase i)
    (hOout_ge : (A_gates C).card ≤ (O_out C).card + 2)
    (b : Fin 2) (hb_r : OrReaches 26 C (opnd C j b) i) (hnb_r : ¬ OrReaches 26 C (opnd C j (1 - b)) i) :
    64 ≤ C.size := by
  classical
  have hAO := min_isAO2 hMin
  have hjT : j ∈ T_gates C := by
    rw [hT_eq]; exact Finset.mem_erase.mpr ⟨hij_ne.symm, mem_A_gates.mpr ⟨hj, hjand⟩⟩
  have hj_below := below_of_mem_T hMin hjT

  set Astar := ((A_gates C).erase i).erase j
  have hAstar_card : Astar.card = (A_gates C).card - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hij_ne.symm, mem_A_gates.mpr ⟨hj, hjand⟩⟩),
      Finset.card_erase_of_mem (mem_A_gates.mpr ⟨hi, hiand⟩)]
    omega
  have hAstar_spec : ∀ a ∈ Astar, ∃ (c : Fin 26) (s : Fin 2),
      side (n := 26) C a (1 - s) = {c} ∧ side (n := 26) C a s ⊆ nbrs c ∧
      (side (n := 26) C a s).Nonempty ∧
      ∀ e ∈ pgEdges, gateVal 26 C a (pairInput e.1 e.2) = true →
        e ∈ starEdgesOf c (side (n := 26) C a s) := by
    intro a ha
    obtain ⟨hanej, haei⟩ := Finset.mem_erase.mp ha
    obtain ⟨hanei, haA⟩ := Finset.mem_erase.mp haei
    obtain ⟨ha_lt, ha_and⟩ := mem_A_gates.mp haA
    exact pure_star_spec hMin huniq ha_lt ha_and hanej
      (below_of_mem_T hMin (by rw [hT_eq]; exact Finset.mem_erase.mpr ⟨hanei, haA⟩))
  let ctr : ℕ → Fin 26 := fun a => if h : a ∈ Astar then (hAstar_spec a h).choose else 0
  let sfn : ℕ → Fin 2 := fun a => if h : a ∈ Astar then (hAstar_spec a h).choose_spec.choose else 0
  let wire : ℕ → ℕ := fun a => opnd C a (sfn a)
  have hW_lt : ∀ a ∈ Astar, wire a < 26 + C.gates.length := by
    intro a ha
    have ha_lt := (mem_A_gates.mp (Finset.mem_erase.mp (Finset.mem_erase.mp ha).2).2).1
    have := opnd_lt hAO ha_lt (sfn a)
    dsimp only [wire]; omega
  have hW_sub : ∀ a ∈ Astar, orIn 26 C (wire a) ⊆ nbrs (ctr a) := by
    intro a ha
    simp only [wire, ctr, sfn, ha, ↓reduceDIte]
    exact (hAstar_spec a ha).choose_spec.choose_spec.2.1
  have hW_pure : ∀ a ∈ Astar, ∀ h, OrReaches 26 C (wire a) h → (gateAt C h).op = GateOp.or → h ∈ O_pure C i := by
    intro a ha h hhr hhor
    obtain ⟨hanej, haei⟩ := Finset.mem_erase.mp ha
    obtain ⟨ha_lt, ha_and⟩ := mem_A_gates.mp (Finset.mem_erase.mp haei).2
    exact opnd_or_in_Opure_of_ne_j hMin hi hiand huniq ha_lt ha_and hanej (sfn a) hhr hhor
  have hcov_Astar : ∀ a ∈ Astar, ∀ e ∈ pgEdges, gateVal 26 C a (pairInput e.1 e.2) = true →
      e ∈ starEdgesOf (ctr a) (orIn 26 C (wire a)) := by
    intro a ha e he hga
    simp only [wire, ctr, sfn, ha, ↓reduceDIte]
    exact (hAstar_spec a ha).choose_spec.choose_spec.2.2.2 e he hga

  set Aj := side (n := 26) C j b
  set Bj := side (n := 26) C j (1 - b)
  set Ai := side (n := 26) C i 0
  set Bi := side (n := 26) C i 1
  set C1 := Aj ∪ (Ai ∩ Bi)
  have hj_ev : ∀ x : Fin 26 → Bool, gateVal 26 C j x = true ↔
      (((∃ u ∈ Ai, x u = true) ∧ (∃ v ∈ Bi, x v = true)) ∨ ∃ u ∈ Aj, x u = true) ∧
      ∃ v ∈ Bj, x v = true := by
    intro x
    rw [j_eval hMin hj hjand huniq x, pure_and_eval hMin huniq hi hiand hij_ne x]
    fin_cases b
    · have h0r : OrReaches 26 C (opnd C j 0) i := hb_r
      have h1r : ¬ OrReaches 26 C (opnd C j 1) i := hnb_r
      change (((OrReaches 26 C (opnd C j 0) i ∧ _) ∨ _) ∧ ((OrReaches 26 C (opnd C j 1) i ∧ _) ∨ _)) ↔ _
      simp only [Aj, Bj, Ai, Bi, h0r, h1r, true_and, false_and, false_or, Fin.isValue]
      rfl
    · have h1r : OrReaches 26 C (opnd C j 1) i := hb_r
      have h0r : ¬ OrReaches 26 C (opnd C j 0) i := hnb_r
      have hsub1 : (1 : Fin 2) - 1 = 0 := rfl
      simp only [Aj, Bj, Ai, Bi, h0r, h1r, hsub1, true_and, false_and, false_or, Fin.isValue]
      exact and_comm
  have hE1 : ∀ u ∈ C1, ∀ v ∈ Bj, pgAdj u v = true := by
    intro u hu v hv
    cases h : pgAdj u v
    · exfalso
      have hjt : gateVal 26 C j (pairInput u v) = true := by
        rw [hj_ev]
        refine ⟨?_, v, hv, by simp [pairInput]⟩
        rcases Finset.mem_union.mp hu with huAj | huAB
        · exact Or.inr ⟨u, huAj, by simp [pairInput]⟩
        · obtain ⟨huA, huB⟩ := Finset.mem_inter.mp huAB
          exact Or.inl ⟨⟨u, huA, by simp [pairInput]⟩, ⟨u, huB, by simp [pairInput]⟩⟩
      rw [hj_below u v h] at hjt; cases hjt
    · rfl
  have hE2 : ∀ u ∈ Ai ∩ Bj, ∀ v ∈ Bi, pgAdj u v = true := by
    intro u hu v hv
    obtain ⟨huA, huB⟩ := Finset.mem_inter.mp hu
    cases h : pgAdj u v
    · exfalso
      have hjt : gateVal 26 C j (pairInput u v) = true := by
        rw [hj_ev]
        exact ⟨Or.inl ⟨⟨u, huA, by simp [pairInput]⟩, ⟨v, hv, by simp [pairInput]⟩⟩,
          u, huB, by simp [pairInput]⟩
      rw [hj_below u v h] at hjt; cases hjt
    · rfl
  have hE3 : ∀ u ∈ Bi ∩ Bj, ∀ v ∈ Ai, pgAdj u v = true := by
    intro u hu v hv
    obtain ⟨huB, huBj⟩ := Finset.mem_inter.mp hu
    cases h : pgAdj u v
    · exfalso
      have hjt : gateVal 26 C j (pairInput u v) = true := by
        rw [hj_ev]
        exact ⟨Or.inl ⟨⟨v, hv, by simp [pairInput]⟩, ⟨u, huB, by simp [pairInput]⟩⟩,
          u, huBj, by simp [pairInput]⟩
      rw [hj_below u v h] at hjt; cases hjt
    · rfl
  have hEdge_split : ∀ e ∈ pgEdges, gateVal 26 C j (pairInput e.1 e.2) = true →
      (e.1 ∈ C1 ∧ e.2 ∈ Bj) ∨ (e.2 ∈ C1 ∧ e.1 ∈ Bj) ∨
      (e.1 ∈ Ai ∩ Bj ∧ e.2 ∈ Bi) ∨ (e.2 ∈ Ai ∩ Bj ∧ e.1 ∈ Bi) ∨
      (e.1 ∈ Bi ∩ Bj ∧ e.2 ∈ Ai) ∨ (e.2 ∈ Bi ∩ Bj ∧ e.1 ∈ Ai) := by
    intro e he hjt
    rw [hj_ev] at hjt
    obtain ⟨hL, w, hwBj, hwp⟩ := hjt
    simp only [pairInput, decide_eq_true_eq] at hwp
    have hnot_self : ∀ z ∈ Bj, z ∉ C1 := fun z hzB hzC => by
      have := hE1 z hzC z hzB; rw [pgAdj_irrefl] at this; cases this
    have hnot_i_self : ∀ z ∈ Bj, ¬ (z ∈ Ai ∧ z ∈ Bi) := fun z hzB h =>
      hnot_self z hzB (Finset.mem_union_right _ (Finset.mem_inter.mpr h))
    rcases hwp with rfl | rfl
    · rcases hL with ⟨⟨u, huA, hup⟩, ⟨v, hvB, hvp⟩⟩ | ⟨u, huAj, hup⟩
      · simp only [pairInput, decide_eq_true_eq] at hup hvp
        rcases hup with rfl | rfl <;> rcases hvp with h1 | h2
        · exact (hnot_i_self e.1 hwBj ⟨huA, h1 ▸ hvB⟩).elim
        · subst h2; exact Or.inr (Or.inr (Or.inl ⟨Finset.mem_inter.mpr ⟨huA, hwBj⟩, hvB⟩))
        · subst h1; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨Finset.mem_inter.mpr ⟨hvB, hwBj⟩, huA⟩))))
        · subst h2; exact Or.inr (Or.inl ⟨Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨huA, hvB⟩), hwBj⟩)
      · simp only [pairInput, decide_eq_true_eq] at hup
        rcases hup with rfl | rfl
        · exact (hnot_self e.1 hwBj (Finset.mem_union_left _ huAj)).elim
        · exact Or.inr (Or.inl ⟨Finset.mem_union_left _ huAj, hwBj⟩)
    · rcases hL with ⟨⟨u, huA, hup⟩, ⟨v, hvB, hvp⟩⟩ | ⟨u, huAj, hup⟩
      · simp only [pairInput, decide_eq_true_eq] at hup hvp
        rcases hup with rfl | rfl <;> rcases hvp with h1 | h2
        · subst h1; exact Or.inl ⟨Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨huA, hvB⟩), hwBj⟩
        · subst h2; exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨Finset.mem_inter.mpr ⟨hvB, hwBj⟩, huA⟩))))
        · subst h1; exact Or.inr (Or.inr (Or.inr (Or.inl ⟨Finset.mem_inter.mpr ⟨huA, hwBj⟩, hvB⟩)))
        · exact (hnot_i_self e.2 hwBj ⟨huA, h2 ▸ hvB⟩).elim
      · simp only [pairInput, decide_eq_true_eq] at hup
        rcases hup with rfl | rfl
        · exact Or.inl ⟨Finset.mem_union_left _ huAj, hwBj⟩
        · exact (hnot_self e.2 hwBj (Finset.mem_union_left _ huAj)).elim

  have hsingle_star : ∀ (c0 : Fin 26) (L0 : Finset (Fin 26)), L0 ⊆ nbrs c0 →
      (∀ e ∈ pgEdges, gateVal 26 C j (pairInput e.1 e.2) = true → e ∈ starEdgesOf c0 L0) →
      (∀ v ∈ L0, gateVal 26 C j (pairInput c0 v) = true) →
      64 ≤ C.size := by
    intro c0 L0 hL0_sub hcov_j hL0_real
    have h52 := aGates_card_of_j_edges hMin hi hj hiand hjand hij_ne hT_eq Astar rfl
      ctr (fun a => orIn 26 C (wire a))
      (fun a ha => (Finset.card_le_card (hW_sub a ha)).trans (nbrs_card _).le)
      hcov_Astar (starEdgesOf c0 L0) hcov_j
    have hL0_le4 : (starEdgesOf c0 L0).card ≤ 4 := starEdgesOf_card_le_four hL0_sub
    have hA_ge14 : 14 ≤ (A_gates C).card := by omega
    have hsize := size_eq_A_Oout_ON hAO

    have hsub_single_wire : ∀ w0 < 26 + C.gates.length,
        (∀ h, OrReaches 26 C w0 h → (gateAt C h).op = GateOp.or → h ∈ O_N C) →
        L0 ⊆ orIn 26 C w0 → 64 ≤ C.size := by
      intro w0 hw0_lt hw0_oN hL0_w0
      have hmb : 52 + 0 ≤ (O_N C).card + Astar.card + 1 := by
        apply one_mixed_center_bound hMin huniq Astar ctr wire hW_lt hW_sub hW_pure c0 L0 0 1
        · intro e he
          obtain ⟨a, haT, hga⟩ := edge_accepted_by_T hMin he
          by_cases haj : a = j
          · subst haj; exact Or.inr (hcov_j e he hga)
          · left
            have haA : a ∈ Astar := by rw [Finset.mem_erase, ← hT_eq]; exact ⟨haj, haT⟩
            exact ⟨a, haA, hcov_Astar a haA e he hga⟩
        · set A0 := Astar.filter fun a => ctr a = c0
          set W0 := A0.image wire
          set U0 := W0.biUnion (orIn 26 C) ∪ L0
          have hU0_nbr : U0 ⊆ nbrs c0 := Finset.union_subset (by
            intro v hv
            obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp hv
            obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
            obtain ⟨haA, hac⟩ := Finset.mem_filter.mp ha
            rw [← hac]; exact hW_sub a haA hvw) hL0_sub
          set Lmix : Finset (Option (Fin 26)) := U0.image some
          set Wall := insert w0 W0
          obtain ⟨E, hElen, hconn⟩ := mixed_center_conn hMin (j := j) hi hiand c0 Lmix
            (Finset.Subset.trans (Finset.image_subset_image hU0_nbr) Finset.subset_union_left)
            Wall
            (fun w hw => by
              rcases Finset.mem_insert.mp hw with rfl | hw0
              · exact hw0_lt
              · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw0
                exact hW_lt a (Finset.mem_filter.mp ha).1)
            (fun w hw h hwr hor => by
              rcases Finset.mem_insert.mp hw with rfl | hw0
              · exact hw0_oN h hwr hor
              · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw0
                exact (mem_O_pure.mp (hW_pure a (Finset.mem_filter.mp ha).1 h hwr hor)).1)
          let Wne := Wall.filter fun w => (fMix C i w ∩ Lmix).Nonempty
          let R : Finset (Option (Fin 26)) := Wne.attach.image fun w => (Finset.mem_filter.mp w.2).2.choose
          have hR_card : R.card ≤ A0.card + 1 := by
            have h1 : R.card ≤ Wall.card := Finset.card_image_le.trans
              (by rw [Finset.card_attach]; exact Finset.card_filter_le _ _)
            have h2 : Wall.card ≤ W0.card + 1 := Finset.card_insert_le _ _
            have h3 : W0.card ≤ A0.card := Finset.card_image_le
            omega
          have hcov_R : ∀ x ∈ Lmix, ∃ r ∈ R, EdgeReach E x r := by
            intro x hx
            obtain ⟨u, huU0, rfl⟩ := Finset.mem_image.mp hx
            have hex_w : ∃ w ∈ Wall, some u ∈ fMix C i w ∩ Lmix := by
              rcases Finset.mem_union.mp huU0 with huW | huL0
              · obtain ⟨w, hwW0, huw⟩ := Finset.mem_biUnion.mp huW
                exact ⟨w, Finset.mem_insert_of_mem hwW0,
                  Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, huw, rfl⟩), hx⟩⟩
              · exact ⟨w0, Finset.mem_insert_self _ _,
                  Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, hL0_w0 huL0, rfl⟩), hx⟩⟩
            obtain ⟨w, hwWall, huw⟩ := hex_w
            have hwne : w ∈ Wne := Finset.mem_filter.mpr ⟨hwWall, ⟨some u, huw⟩⟩
            let r := (Finset.mem_filter.mp hwne).2.choose
            have hr_spec := (Finset.mem_filter.mp hwne).2.choose_spec
            exact ⟨r, Finset.mem_image.mpr ⟨⟨w, hwne⟩, Finset.mem_attach _ _, rfl⟩,
              hconn w hwWall (some u) huw r hr_spec⟩
          have hb := graph_spanning_bound E Lmix R hcov_R
          rw [Finset.card_image_of_injective _ (Option.some_injective (Fin 26))] at hb
          rw [oC_disj_oExtra] at hElen
          omega
      change 64 ≤ C.gates.length
      omega

    by_cases hc0Bj : c0 ∈ Bj
    ·
      have hc0_notAB : ¬ (c0 ∈ Ai ∧ c0 ∈ Bi) := fun h => by
        have := hE1 c0 (Finset.mem_union_right _ (Finset.mem_inter.mpr h)) c0 hc0Bj
        rw [pgAdj_irrefl] at this; cases this
      by_cases hLB : (L0 ∩ Bj).Nonempty
      ·
        obtain ⟨v0, hv0⟩ := hLB
        obtain ⟨hv0L, hv0Bj⟩ := Finset.mem_inter.mp hv0
        have hC1_emp : C1 = ∅ := by
          ext z; simp only [Finset.notMem_empty, iff_false]
          intro hz
          have hb1 := pgAdj_bip z c0 (hE1 z hz c0 hc0Bj)
          have hb2 := pgAdj_bip z v0 (hE1 z hz v0 hv0Bj)
          have hb3 := pgAdj_bip c0 v0 ((mem_nbrs_iff c0 v0).mp (hL0_sub hv0L))
          tauto
        by_cases hc0Ai : c0 ∈ Ai
        ·
          have hc0_notBi : c0 ∉ Bi := fun h => hc0_notAB ⟨hc0Ai, h⟩
          apply hsub_single_wire (opnd C i 1) (by have := opnd_lt hAO hi 1; omega)
            (fun h hhr hor => opnd_or_in_ON hMin huniq hi hiand 1 hhr hor)
          intro v hvL0
          have hadj_cv := (mem_nbrs_iff c0 v).mp (hL0_sub hvL0)
          have hjt := hL0_real v hvL0
          rw [hj_ev] at hjt
          obtain ⟨hL, _⟩ := hjt
          rcases hL with ⟨_, ⟨y, hyBi, hyp⟩⟩ | ⟨y, hyAj, _⟩
          · simp only [pairInput, decide_eq_true_eq] at hyp
            rcases hyp with rfl | rfl
            · exact (hc0_notBi hyBi).elim
            · exact hyBi
          · have : y ∈ C1 := Finset.mem_union_left _ hyAj
            rw [hC1_emp] at this; exact (Finset.notMem_empty y this).elim
        ·
          apply hsub_single_wire (opnd C i 0) (by have := opnd_lt hAO hi 0; omega)
            (fun h hhr hor => opnd_or_in_ON hMin huniq hi hiand 0 hhr hor)
          intro v hvL0
          have hjt := hL0_real v hvL0
          rw [hj_ev] at hjt
          obtain ⟨hL, _⟩ := hjt
          rcases hL with ⟨⟨y, hyAi, hyp⟩, _⟩ | ⟨y, hyAj, _⟩
          · simp only [pairInput, decide_eq_true_eq] at hyp
            rcases hyp with rfl | rfl
            · exact (hc0Ai hyAi).elim
            · exact hyAi
          · have : y ∈ C1 := Finset.mem_union_left _ hyAj
            rw [hC1_emp] at this; exact (Finset.notMem_empty y this).elim
      ·
        set LA := L0 ∩ Aj
        set Li := L0 \ Aj
        have hLi_in_si : ∃ si : Fin 2, Li ⊆ side (n := 26) C i si := by
          by_cases hc0Ai : c0 ∈ Ai
          · refine ⟨1, fun v hv => ?_⟩
            obtain ⟨hvL0, hv_notAj⟩ := Finset.mem_sdiff.mp hv
            have hc0_notBi : c0 ∉ Bi := fun h => hc0_notAB ⟨hc0Ai, h⟩
            have hjt := hL0_real v hvL0
            rw [hj_ev] at hjt
            rcases hjt.1 with ⟨_, ⟨y, hyBi, hyp⟩⟩ | ⟨y, hyAj, hyp⟩
            · simp only [pairInput, decide_eq_true_eq] at hyp
              rcases hyp with rfl | rfl
              · exact (hc0_notBi hyBi).elim
              · exact hyBi
            · simp only [pairInput, decide_eq_true_eq] at hyp
              rcases hyp with heq | heq
              · rw [heq] at hyAj
                have := hE1 c0 (Finset.mem_union_left _ hyAj) c0 hc0Bj
                rw [pgAdj_irrefl] at this; cases this
              · rw [heq] at hyAj; exact (hv_notAj hyAj).elim
          · refine ⟨0, fun v hv => ?_⟩
            obtain ⟨hvL0, hv_notAj⟩ := Finset.mem_sdiff.mp hv
            have hjt := hL0_real v hvL0
            rw [hj_ev] at hjt
            rcases hjt.1 with ⟨⟨y, hyAi, hyp⟩, _⟩ | ⟨y, hyAj, hyp⟩
            · simp only [pairInput, decide_eq_true_eq] at hyp
              rcases hyp with rfl | rfl
              · exact (hc0Ai hyAi).elim
              · exact hyAi
            · simp only [pairInput, decide_eq_true_eq] at hyp
              rcases hyp with heq | heq
              · rw [heq] at hyAj
                have := hE1 c0 (Finset.mem_union_left _ hyAj) c0 hc0Bj
                rw [pgAdj_irrefl] at this; cases this
              · rw [heq] at hyAj; exact (hv_notAj hyAj).elim
        obtain ⟨si, hLi_sub⟩ := hLi_in_si
        by_cases hLi_ne : Li.Nonempty
        ·
          have hmb : 52 + 1 ≤ (O_N C).card + Astar.card + 2 := by
            apply one_mixed_center_bound hMin huniq Astar ctr wire hW_lt hW_sub hW_pure c0 L0 1 2
            · intro e he
              obtain ⟨a, haT, hga⟩ := edge_accepted_by_T hMin he
              by_cases haj : a = j
              · subst haj; exact Or.inr (hcov_j e he hga)
              · left
                have haA : a ∈ Astar := by rw [Finset.mem_erase, ← hT_eq]; exact ⟨haj, haT⟩
                exact ⟨a, haA, hcov_Astar a haA e he hga⟩
            · set A0 := Astar.filter fun a => ctr a = c0
              set W0 := A0.image wire
              set U0 := W0.biUnion (orIn 26 C) ∪ L0
              have hU0_nbr : U0 ⊆ nbrs c0 := Finset.union_subset (by
                intro v hv
                obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.mp hv
                obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw
                obtain ⟨haA, hac⟩ := Finset.mem_filter.mp ha
                rw [← hac]; exact hW_sub a haA hvw) hL0_sub
              set Lmix : Finset (Option (Fin 26)) := insert none (U0.image some)
              have hLmix_card : Lmix.card = U0.card + 1 := by
                rw [Finset.card_insert_of_notMem (by simp), Finset.card_image_of_injective _ (Option.some_injective (Fin 26))]
              set Wall := insert (opnd C j b) (insert (opnd C i si) W0)
              obtain ⟨E, hElen, hconn⟩ := mixed_center_conn hMin (j := j) hi hiand c0 Lmix
                (by
                  intro x hx
                  rcases Finset.mem_insert.mp hx with rfl | hxu
                  · simp
                  · exact Finset.mem_union_left _ (Finset.image_subset_image hU0_nbr hxu))
                Wall
                (fun w hw => by
                  rcases Finset.mem_insert.mp hw with rfl | hw1
                  · have := opnd_lt hAO hj b; omega
                  · rcases Finset.mem_insert.mp hw1 with rfl | hw0
                    · have := opnd_lt hAO hi si; omega
                    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw0
                      exact hW_lt a (Finset.mem_filter.mp ha).1)
                (fun w hw h hwr hor => by
                  rcases Finset.mem_insert.mp hw with rfl | hw1
                  · exact opnd_or_in_ON hMin huniq hj hjand b hwr hor
                  · rcases Finset.mem_insert.mp hw1 with rfl | hw0
                    · exact opnd_or_in_ON hMin huniq hi hiand si hwr hor
                    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hw0
                      exact (mem_O_pure.mp (hW_pure a (Finset.mem_filter.mp ha).1 h hwr hor)).1)
              let W0ne := W0.filter fun w => (orIn 26 C w).Nonempty
              let R0 : Finset (Option (Fin 26)) := W0ne.attach.image fun w => some (Finset.mem_filter.mp w.2).2.choose
              let r_i : Fin 26 := hLi_ne.choose
              have hr_i_mem : r_i ∈ Li := hLi_ne.choose_spec
              let R : Finset (Option (Fin 26)) := insert none (insert (some r_i) R0)
              have hR_card : R.card ≤ A0.card + 2 := by
                have h1 : R0.card ≤ W0.card := Finset.card_image_le.trans
                  (by rw [Finset.card_attach]; exact Finset.card_filter_le _ _)
                have h2 : W0.card ≤ A0.card := Finset.card_image_le
                have h3 : R.card ≤ (insert (some r_i) R0).card + 1 := Finset.card_insert_le _ _
                have h4 : (insert (some r_i) R0).card ≤ R0.card + 1 := Finset.card_insert_le _ _
                omega
              have hcov_R : ∀ x ∈ Lmix, ∃ r ∈ R, EdgeReach E x r := by
                intro x hx
                rcases Finset.mem_insert.mp hx with rfl | hxu
                · exact ⟨none, Finset.mem_insert_self _ _, Relation.ReflTransGen.refl⟩
                · obtain ⟨u, huU0, rfl⟩ := Finset.mem_image.mp hxu
                  rcases Finset.mem_union.mp huU0 with huW | huL0
                  · obtain ⟨w, hwW0, huw⟩ := Finset.mem_biUnion.mp huW
                    have hwne : w ∈ W0ne := Finset.mem_filter.mpr ⟨hwW0, ⟨u, huw⟩⟩
                    let r0 := (Finset.mem_filter.mp hwne).2.choose
                    have hr0_w : r0 ∈ orIn 26 C w := (Finset.mem_filter.mp hwne).2.choose_spec
                    have hr0_U0 : r0 ∈ U0 := Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨w, hwW0, hr0_w⟩)
                    refine ⟨some r0, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
                      (Finset.mem_image.mpr ⟨⟨w, hwne⟩, Finset.mem_attach _ _, rfl⟩)), ?_⟩
                    apply hconn w (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hwW0))
                    · exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, huw, rfl⟩), hx⟩
                    · exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r0, hr0_w, rfl⟩),
                        Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r0, hr0_U0, rfl⟩)⟩
                  · by_cases huAj : u ∈ Aj
                    · refine ⟨none, Finset.mem_insert_self _ _, ?_⟩
                      apply hconn (opnd C j b) (Finset.mem_insert_self _ _)
                      · exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, huAj, rfl⟩), hx⟩
                      · exact Finset.mem_inter.mpr ⟨Finset.mem_union_right _ (by simp [hb_r]), Finset.mem_insert_self _ _⟩
                    · have huLi : u ∈ Li := Finset.mem_sdiff.mpr ⟨huL0, huAj⟩
                      refine ⟨some r_i, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_⟩
                      apply hconn (opnd C i si) (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
                      · exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨u, hLi_sub huLi, rfl⟩), hx⟩
                      · have hri_U0 : r_i ∈ U0 := Finset.mem_union_right _ (Finset.mem_sdiff.mp hr_i_mem).1
                        exact Finset.mem_inter.mpr ⟨Finset.mem_union_left _ (Finset.mem_image.mpr ⟨r_i, hLi_sub hr_i_mem, rfl⟩),
                          Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨r_i, hri_U0, rfl⟩)⟩
              have hb := graph_spanning_bound E Lmix R hcov_R
              rw [hLmix_card] at hb
              rw [oC_disj_oExtra] at hElen
              omega
          change 64 ≤ C.gates.length
          omega
        ·
          have hLi_emp : Li = ∅ := Finset.not_nonempty_iff_eq_empty.mp hLi_ne
          apply hsub_single_wire (opnd C j b) (by have := opnd_lt hAO hj b; omega)
            (fun h hhr hor => opnd_or_in_ON hMin huniq hj hjand b hhr hor)
          intro v hvL0
          by_contra hv_notAj
          have : v ∈ Li := Finset.mem_sdiff.mpr ⟨hvL0, hv_notAj⟩
          rw [hLi_emp] at this; exact Finset.notMem_empty v this
    ·
      apply hsub_single_wire (opnd C j (1 - b)) (by have := opnd_lt hAO hj (1 - b); omega)
        (fun h hhr hor => opnd_or_in_ON hMin huniq hj hjand (1 - b) hhr hor)
      intro v hvL0
      have hjt := hL0_real v hvL0
      rw [hj_ev] at hjt
      obtain ⟨_, w, hwBj, hwp⟩ := hjt
      simp only [pairInput, decide_eq_true_eq] at hwp
      rcases hwp with rfl | rfl
      · exact (hc0Bj hwBj).elim
      · exact hwBj

  have hsingle_star_cover : ∀ (c0 : Fin 26) (S : Finset (Fin 26)), S ⊆ nbrs c0 →
      (∀ e ∈ pgEdges, gateVal 26 C j (pairInput e.1 e.2) = true → e ∈ starEdgesOf c0 S) →
      64 ≤ C.size := by
    intro c0 S hS_sub hcov_S
    set L0 := S.filter fun v => gateVal 26 C j (pairInput c0 v) = true
    apply hsingle_star c0 L0 ((Finset.filter_subset _ _).trans hS_sub)
    · intro e he hjt
      have heS := hcov_S e he hjt
      obtain ⟨v, hvS, hdeq⟩ := Finset.mem_image.mp heS
      have hv_real : gateVal 26 C j (pairInput c0 v) = true := by
        have heq_p : pairInput c0 v = pairInput e.1 e.2 := by
          unfold dirEdge at hdeq
          split_ifs at hdeq
          · have h1 : c0 = e.1 := congrArg Prod.fst hdeq
            have h2 : v = e.2 := congrArg Prod.snd hdeq
            rw [h1, h2]
          · have h1 : v = e.1 := congrArg Prod.fst hdeq
            have h2 : c0 = e.2 := congrArg Prod.snd hdeq
            rw [← h1, ← h2]; funext w; simp [pairInput, or_comm]
        rwa [heq_p]
      exact Finset.mem_image.mpr ⟨v, Finset.mem_filter.mpr ⟨hvS, hv_real⟩, hdeq⟩
    · intro v hv; exact (Finset.mem_filter.mp hv).2

  by_cases hBj1 : Bj.card ≤ 1
  · by_cases hBj0 : Bj.card = 0
    · have hBj_emp : Bj = ∅ := Finset.card_eq_zero.mp hBj0
      apply hsingle_star_cover 0 ∅ (Finset.empty_subset _)
      intro e he hjt
      rw [hj_ev] at hjt
      obtain ⟨_, w, hw, _⟩ := hjt
      rw [hBj_emp] at hw; exact (Finset.notMem_empty w hw).elim
    · have hBjeq1 : Bj.card = 1 := by omega
      obtain ⟨c0, hc0⟩ := Finset.card_eq_one.mp hBjeq1
      apply hsingle_star_cover c0 (nbrs c0) (Finset.Subset.refl _)
      intro e he hjt
      rw [hj_ev] at hjt
      obtain ⟨_, w, hw, hwp⟩ := hjt
      rw [hc0, Finset.mem_singleton] at hw; subst hw
      simp only [pairInput, decide_eq_true_eq] at hwp
      have hadj_e := (mem_pgEdges_iff e).mp he |>.2
      rw [← dirEdge_eq_of_mem_pgEdges he]
      rcases hwp with h1 | h2
      · subst h1; exact mem_starEdgesOf_left ((mem_nbrs_iff e.1 e.2).mpr hadj_e)
      · subst h2; exact mem_starEdgesOf_right hadj_e ((mem_nbrs_iff e.2 e.1).mpr (by rw [pgAdj_symm]; exact hadj_e))
  ·
    push_neg at hBj1
    by_cases hE23 : ((Ai ∩ Bj).Nonempty ∧ Bi.Nonempty) ∧ ((Bi ∩ Bj).Nonempty ∧ Ai.Nonempty)
    ·
      obtain ⟨⟨⟨p, hp⟩, _⟩, ⟨⟨l, hl⟩, _⟩⟩ := hE23
      have hadj_pl : pgAdj p l = true := hE2 p hp l (Finset.mem_inter.mp hl).1
      have hC1_emp : C1 = ∅ := by
        ext z; simp only [Finset.notMem_empty, iff_false]
        intro hz
        have hb1 := pgAdj_bip z p (hE1 z hz p (Finset.mem_inter.mp hp).2)
        have hb2 := pgAdj_bip z l (hE1 z hz l (Finset.mem_inter.mp hl).2)
        have hb3 := pgAdj_bip p l hadj_pl
        tauto
      by_cases hAiBj : (Ai ∩ Bj).card ≤ 1
      · by_cases hBiBj : (Bi ∩ Bj).card ≤ 1
        ·
          have hp_eq : Ai ∩ Bj = {p} := by
            have h1 : (Ai ∩ Bj).card = 1 := le_antisymm hAiBj (Finset.card_pos.mpr ⟨p, hp⟩)
            obtain ⟨p', hp'⟩ := Finset.card_eq_one.mp h1
            have : p = p' := Finset.mem_singleton.mp (hp' ▸ hp)
            rwa [← this] at hp'
          have hl_eq : Bi ∩ Bj = {l} := by
            have h1 : (Bi ∩ Bj).card = 1 := le_antisymm hBiBj (Finset.card_pos.mpr ⟨l, hl⟩)
            obtain ⟨l', hl'⟩ := Finset.card_eq_one.mp h1
            have : l = l' := Finset.mem_singleton.mp (hl' ▸ hl)
            rwa [← this] at hl'
          have hBi_sub : Bi ⊆ nbrs p := fun v hv => (mem_nbrs_iff p v).mpr (hE2 p hp v hv)
          have hAi_sub : Ai ⊆ nbrs l := fun v hv => (mem_nbrs_iff l v).mpr (hE3 l hl v hv)
          have hcov_j21 : ∀ e ∈ pgEdges, gateVal 26 C j (pairInput e.1 e.2) = true →
              e ∈ starEdgesOf p Bi ∪ starEdgesOf l Ai := by
            intro e he hjt
            have hadj_e := (mem_pgEdges_iff e).mp he |>.2
            rw [← dirEdge_eq_of_mem_pgEdges he]
            rcases hEdge_split e he hjt with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩
            · rw [hC1_emp] at h1; exact (Finset.notMem_empty _ h1).elim
            · rw [hC1_emp] at h1; exact (Finset.notMem_empty _ h1).elim
            · rw [hp_eq, Finset.mem_singleton] at h1; subst h1
              exact Finset.mem_union_left _ (mem_starEdgesOf_left h2)
            · rw [hp_eq, Finset.mem_singleton] at h1; subst h1
              exact Finset.mem_union_left _ (mem_starEdgesOf_right hadj_e h2)
            · rw [hl_eq, Finset.mem_singleton] at h1; subst h1
              exact Finset.mem_union_right _ (mem_starEdgesOf_left h2)
            · rw [hl_eq, Finset.mem_singleton] at h1; subst h1
              exact Finset.mem_union_right _ (mem_starEdgesOf_right hadj_e h2)

          have hEj_le7 : (starEdgesOf p Bi ∪ starEdgesOf l Ai).card ≤ 7 := by
            have hsh : dirEdge p l ∈ starEdgesOf p Bi ∩ starEdgesOf l Ai :=
              Finset.mem_inter.mpr ⟨mem_starEdgesOf_left (Finset.mem_inter.mp hl).1,
                mem_starEdgesOf_right hadj_pl (Finset.mem_inter.mp hp).1⟩
            have hpos : 1 ≤ (starEdgesOf p Bi ∩ starEdgesOf l Ai).card := Finset.card_pos.mpr ⟨_, hsh⟩
            have hu := Finset.card_union_add_card_inter (starEdgesOf p Bi) (starEdgesOf l Ai)
            have h4a := starEdgesOf_card_le_four hBi_sub
            have h4b := starEdgesOf_card_le_four hAi_sub
            omega
          have h52 := aGates_card_of_j_edges hMin hi hj hiand hjand hij_ne hT_eq Astar rfl
            ctr (fun a => orIn 26 C (wire a))
            (fun a ha => (Finset.card_le_card (hW_sub a ha)).trans (nbrs_card _).le)
            hcov_Astar _ hcov_j21
          have hA_ge14 : 14 ≤ (A_gates C).card := by omega

          have hex_ge1 : 1 ≤ (O_extra C i).card :=
            extra_of_mixed_bipartite hMin (w := opnd C j (1 - b)) (by have := opnd_lt hAO hj (1 - b); omega)
              (fun h hhr hor => opnd_or_in_ON hMin huniq hj hjand (1 - b) hhr hor)
              (Finset.mem_inter.mp hp).2 (Finset.mem_inter.mp hl).2 (pgAdj_bip p l hadj_pl)

          have hi_notA : i ∉ Astar := by simp [Astar]
          have hj_notA : j ∉ Astar := by simp [Astar]
          set Idx := insert i (insert j Astar)
          have hIdx_card : Idx.card = (A_gates C).card := by
            have heq : Idx = A_gates C := by
              ext x; simp only [Idx, Astar, Finset.mem_insert, Finset.mem_erase]
              constructor
              · rintro (rfl | rfl | ⟨_, _, hx⟩)
                · exact mem_A_gates.mpr ⟨hi, hiand⟩
                · exact mem_A_gates.mpr ⟨hj, hjand⟩
                · exact hx
              · intro hx
                by_cases hxi : x = i; · exact Or.inl hxi
                by_cases hxj : x = j; · exact Or.inr (Or.inl hxj)
                exact Or.inr (Or.inr ⟨hxj, hxi, hx⟩)
            rw [heq]
          let ctr' : ℕ → Fin 26 := fun k => if k = i then p else if k = j then l else ctr k
          let wire' : ℕ → ℕ := fun k => if k = i then opnd C i 1 else if k = j then opnd C i 0 else wire k
          have hpf : 52 ≤ (∑ c : Fin 26, (O_c C i c).card) + Idx.card := by
            apply pure_family_sum_bound hMin huniq Idx ctr' wire'
            · intro k hk
              rcases Finset.mem_insert.mp hk with rfl | hk1
              · simp only [wire', ↓reduceIte]; have := opnd_lt hAO hi 1; omega
              · rcases Finset.mem_insert.mp hk1 with rfl | hkA
                · simp only [wire', hij_ne.symm, ↓reduceIte]; have := opnd_lt hAO hi 0; omega
                · have hki : k ≠ i := fun h => hi_notA (h ▸ hkA)
                  have hkj : k ≠ j := fun h => hj_notA (h ▸ hkA)
                  simp only [wire', hki, hkj, ↓reduceIte]; exact hW_lt k hkA
            · intro k hk
              rcases Finset.mem_insert.mp hk with rfl | hk1
              · simp only [wire', ctr', ↓reduceIte]; exact hBi_sub
              · rcases Finset.mem_insert.mp hk1 with rfl | hkA
                · simp only [wire', ctr', hij_ne.symm, ↓reduceIte]; exact hAi_sub
                · have hki : k ≠ i := fun h => hi_notA (h ▸ hkA)
                  have hkj : k ≠ j := fun h => hj_notA (h ▸ hkA)
                  simp only [wire', ctr', hki, hkj, ↓reduceIte]; exact hW_sub k hkA
            · intro k hk h hhr hor
              rcases Finset.mem_insert.mp hk with rfl | hk1
              · simp only [wire', ↓reduceIte] at hhr
                exact opnd_or_in_Opure_of_ne_j hMin hi hiand huniq hi hiand hij_ne 1 hhr hor
              · rcases Finset.mem_insert.mp hk1 with rfl | hkA
                · simp only [wire', hij_ne.symm, ↓reduceIte] at hhr
                  exact opnd_or_in_Opure_of_ne_j hMin hi hiand huniq hi hiand hij_ne 0 hhr hor
                · have hki : k ≠ i := fun h => hi_notA (h ▸ hkA)
                  have hkj : k ≠ j := fun h => hj_notA (h ▸ hkA)
                  simp only [wire', hki, hkj, ↓reduceIte] at hhr
                  exact hW_pure k hkA h hhr hor
            · intro e he
              obtain ⟨a, haT, hga⟩ := edge_accepted_by_T hMin he
              by_cases haj : a = j
              · subst a
                rcases Finset.mem_union.mp (hcov_j21 e he hga) with he1 | he2
                · refine ⟨i, Finset.mem_insert_self _ _, ?_⟩
                  simp only [ctr', wire', ↓reduceIte]; exact he1
                · refine ⟨j, Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_⟩
                  simp only [ctr', wire', hij_ne.symm, ↓reduceIte]; exact he2
              · have haA : a ∈ Astar := by rw [Finset.mem_erase, ← hT_eq]; exact ⟨haj, haT⟩
                have hai : a ≠ i := fun h => hi_notA (h ▸ haA)
                refine ⟨a, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem haA), ?_⟩
                simp only [ctr', wire', hai, haj, ↓reduceIte]
                exact hcov_Astar a haA e he hga
          have hsize := size_eq_A_Oout_ON hAO
          have hoN := oN_card_eq hMin huniq
          change 64 ≤ C.gates.length
          omega
        ·
          push_neg at hBiBj
          have hAi1 : Ai.card = 1 := by
            rcases biclique_is_star hE3 with h1 | h2
            · omega
            · exact le_antisymm h2 (Finset.card_pos.mpr ⟨p, (Finset.mem_inter.mp hp).1⟩)
          have hAi_eq : Ai = {p} := by
            obtain ⟨p', hp'⟩ := Finset.card_eq_one.mp hAi1
            have : p = p' := Finset.mem_singleton.mp (hp' ▸ (Finset.mem_inter.mp hp).1)
            rwa [← this] at hp'
          apply hsingle_star_cover p (nbrs p) (Finset.Subset.refl _)
          intro e he hjt
          have hadj_e := (mem_pgEdges_iff e).mp he |>.2
          rw [← dirEdge_eq_of_mem_pgEdges he]
          rcases hEdge_split e he hjt with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨_, h2⟩ | ⟨_, h2⟩
          · rw [hC1_emp] at h1; exact (Finset.notMem_empty _ h1).elim
          · rw [hC1_emp] at h1; exact (Finset.notMem_empty _ h1).elim
          · have : e.1 = p := Finset.mem_singleton.mp (hAi_eq ▸ (Finset.mem_inter.mp h1).1)
            subst this; exact mem_starEdgesOf_left ((mem_nbrs_iff e.1 e.2).mpr hadj_e)
          · have : e.2 = p := Finset.mem_singleton.mp (hAi_eq ▸ (Finset.mem_inter.mp h1).1)
            subst this; exact mem_starEdgesOf_right hadj_e ((mem_nbrs_iff e.2 e.1).mpr (by rw [pgAdj_symm]; exact hadj_e))
          · rw [hAi_eq, Finset.mem_singleton] at h2; subst h2
            exact mem_starEdgesOf_right hadj_e ((mem_nbrs_iff e.2 e.1).mpr (by rw [pgAdj_symm]; exact hadj_e))
          · rw [hAi_eq, Finset.mem_singleton] at h2; subst h2
            exact mem_starEdgesOf_left ((mem_nbrs_iff e.1 e.2).mpr hadj_e)
      ·
        push_neg at hAiBj
        have hBi1 : Bi.card = 1 := by
          rcases biclique_is_star hE2 with h1 | h2
          · omega
          · exact le_antisymm h2 (Finset.card_pos.mpr ⟨l, (Finset.mem_inter.mp hl).1⟩)
        have hBi_eq : Bi = {l} := by
          obtain ⟨l', hl'⟩ := Finset.card_eq_one.mp hBi1
          have : l = l' := Finset.mem_singleton.mp (hl' ▸ (Finset.mem_inter.mp hl).1)
          rwa [← this] at hl'
        apply hsingle_star_cover l (nbrs l) (Finset.Subset.refl _)
        intro e he hjt
        have hadj_e := (mem_pgEdges_iff e).mp he |>.2
        rw [← dirEdge_eq_of_mem_pgEdges he]
        rcases hEdge_split e he hjt with ⟨h1, _⟩ | ⟨h1, _⟩ | ⟨_, h2⟩ | ⟨_, h2⟩ | ⟨h1, _⟩ | ⟨h1, _⟩
        · rw [hC1_emp] at h1; exact (Finset.notMem_empty _ h1).elim
        · rw [hC1_emp] at h1; exact (Finset.notMem_empty _ h1).elim
        · rw [hBi_eq, Finset.mem_singleton] at h2; subst h2
          exact mem_starEdgesOf_right hadj_e ((mem_nbrs_iff e.2 e.1).mpr (by rw [pgAdj_symm]; exact hadj_e))
        · rw [hBi_eq, Finset.mem_singleton] at h2; subst h2
          exact mem_starEdgesOf_left ((mem_nbrs_iff e.1 e.2).mpr hadj_e)
        · have : e.1 = l := Finset.mem_singleton.mp (hBi_eq ▸ (Finset.mem_inter.mp h1).1)
          subst this; exact mem_starEdgesOf_left ((mem_nbrs_iff e.1 e.2).mpr hadj_e)
        · have : e.2 = l := Finset.mem_singleton.mp (hBi_eq ▸ (Finset.mem_inter.mp h1).1)
          subst this; exact mem_starEdgesOf_right hadj_e ((mem_nbrs_iff e.2 e.1).mpr (by rw [pgAdj_symm]; exact hadj_e))
    ·

      have hone_empty : ∀ (si : Fin 2),
          ¬ ((side (n := 26) C i (1 - si) ∩ Bj).Nonempty ∧ (side (n := 26) C i si).Nonempty) →
          64 ≤ C.size := by
        intro si hEother_emp
        set Si := side (n := 26) C i si
        set Ti := side (n := 26) C i (1 - si)
        have hEsi : ∀ u ∈ Si ∩ Bj, ∀ v ∈ Ti, pgAdj u v = true := by
          fin_cases si <;> assumption
        have hEdge_s : ∀ e ∈ pgEdges, gateVal 26 C j (pairInput e.1 e.2) = true →
            (e.1 ∈ C1 ∧ e.2 ∈ Bj) ∨ (e.2 ∈ C1 ∧ e.1 ∈ Bj) ∨
            (e.1 ∈ Si ∩ Bj ∧ e.2 ∈ Ti) ∨ (e.2 ∈ Si ∩ Bj ∧ e.1 ∈ Ti) := by
          intro e he hjt
          rcases hEdge_split e he hjt with h | h | h | h | h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
          · fin_cases si
            · exact Or.inr (Or.inr (Or.inl h))
            · exact (hEother_emp ⟨⟨e.1, h.1⟩, ⟨e.2, h.2⟩⟩).elim
          · fin_cases si
            · exact Or.inr (Or.inr (Or.inr h))
            · exact (hEother_emp ⟨⟨e.2, h.1⟩, ⟨e.1, h.2⟩⟩).elim
          · fin_cases si
            · exact (hEother_emp ⟨⟨e.1, h.1⟩, ⟨e.2, h.2⟩⟩).elim
            · exact Or.inr (Or.inr (Or.inl h))
          · fin_cases si
            · exact (hEother_emp ⟨⟨e.2, h.1⟩, ⟨e.1, h.2⟩⟩).elim
            · exact Or.inr (Or.inr (Or.inr h))
        by_cases hC1_ne : C1.Nonempty
        ·
          have hC1_1 : C1.card = 1 := by
            rcases biclique_is_star hE1 with h1 | h2
            · exact le_antisymm h1 (Finset.card_pos.mpr hC1_ne)
            · omega
          obtain ⟨c1, hc1_eq⟩ := Finset.card_eq_one.mp hC1_1
          have hc1_mem : c1 ∈ C1 := by rw [hc1_eq]; simp
          have hBj_sub : Bj ⊆ nbrs c1 := fun v hv => (mem_nbrs_iff c1 v).mpr (hE1 c1 hc1_mem v hv)
          by_cases hE2_ne : (Si ∩ Bj).Nonempty ∧ Ti.Nonempty
          · by_cases hSiBj1 : (Si ∩ Bj).card ≤ 1
            ·
              have h1 : (Si ∩ Bj).card = 1 := le_antisymm hSiBj1 (Finset.card_pos.mpr hE2_ne.1)
              obtain ⟨c2, hc2_eq⟩ := Finset.card_eq_one.mp h1
              have hc2_mem : c2 ∈ Si ∩ Bj := by rw [hc2_eq]; simp
              have hTi_sub : Ti ⊆ nbrs c2 := fun v hv => (mem_nbrs_iff c2 v).mpr (hEsi c2 hc2_mem v hv)
              have hc1_mem' : c1 ∈ Aj ∪ (Si ∩ Ti) := by
                fin_cases si
                · exact hc1_mem
                · simpa [C1, Si, Ti, Finset.inter_comm] using hc1_mem
              apply case2_sub22 hMin hi hj hiand hjand hij_ne huniq hT_eq hOout_ge b hb_r hnb_r
                Astar rfl ctr wire hW_lt hW_sub hW_pure hcov_Astar si c1 c2 hc1_mem' hc2_mem hBj_sub hTi_sub
              intro e he hjt
              have hadj_e := (mem_pgEdges_iff e).mp he |>.2
              rw [← dirEdge_eq_of_mem_pgEdges he]
              rcases hEdge_s e he hjt with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩
              · rw [hc1_eq, Finset.mem_singleton] at h1'; subst h1'
                exact Finset.mem_union_left _ (mem_starEdgesOf_left h2')
              · rw [hc1_eq, Finset.mem_singleton] at h1'; subst h1'
                exact Finset.mem_union_left _ (mem_starEdgesOf_right hadj_e h2')
              · rw [hc2_eq, Finset.mem_singleton] at h1'; subst h1'
                exact Finset.mem_union_right _ (mem_starEdgesOf_left h2')
              · rw [hc2_eq, Finset.mem_singleton] at h1'; subst h1'
                exact Finset.mem_union_right _ (mem_starEdgesOf_right hadj_e h2')
            ·
              push_neg at hSiBj1
              have hTi_sub_c1 : Ti ⊆ {c1} := by
                intro v hv
                rw [Finset.mem_singleton]
                obtain ⟨u1, hu1, u2, hu2, hune⟩ := Finset.one_lt_card.mp hSiBj1
                by_contra hvc1
                have hpair : ({u1, u2} : Finset (Fin 26)) ⊆ nbrs c1 ∩ nbrs v := by
                  intro z hz
                  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
                  rcases hz with heq | heq
                  · rw [heq]; exact Finset.mem_inter.mpr ⟨hBj_sub (Finset.mem_inter.mp hu1).2,
                      (mem_nbrs_iff v u1).mpr (by rw [pgAdj_symm]; exact hEsi u1 hu1 v hv)⟩
                  · rw [heq]; exact Finset.mem_inter.mpr ⟨hBj_sub (Finset.mem_inter.mp hu2).2,
                      (mem_nbrs_iff v u2).mpr (by rw [pgAdj_symm]; exact hEsi u2 hu2 v hv)⟩
                have hle := (Finset.card_le_card hpair).trans (pg_no_c4 c1 v (Ne.symm hvc1))
                rw [Finset.card_pair hune] at hle; omega
              apply hsingle_star_cover c1 Bj hBj_sub
              intro e he hjt
              have hadj_e := (mem_pgEdges_iff e).mp he |>.2
              rw [← dirEdge_eq_of_mem_pgEdges he]
              rcases hEdge_s e he hjt with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩
              · rw [hc1_eq, Finset.mem_singleton] at h1'; subst h1'; exact mem_starEdgesOf_left h2'
              · rw [hc1_eq, Finset.mem_singleton] at h1'; subst h1'; exact mem_starEdgesOf_right hadj_e h2'
              · have := Finset.mem_singleton.mp (hTi_sub_c1 h2'); subst this
                exact mem_starEdgesOf_right hadj_e (Finset.mem_inter.mp h1').2
              · have := Finset.mem_singleton.mp (hTi_sub_c1 h2'); subst this
                exact mem_starEdgesOf_left (Finset.mem_inter.mp h1').2
          ·
            apply hsingle_star_cover c1 Bj hBj_sub
            intro e he hjt
            have hadj_e := (mem_pgEdges_iff e).mp he |>.2
            rw [← dirEdge_eq_of_mem_pgEdges he]
            rcases hEdge_s e he hjt with ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩
            · rw [hc1_eq, Finset.mem_singleton] at h1'; subst h1'; exact mem_starEdgesOf_left h2'
            · rw [hc1_eq, Finset.mem_singleton] at h1'; subst h1'; exact mem_starEdgesOf_right hadj_e h2'
            · exact (hE2_ne ⟨⟨e.1, h1'⟩, ⟨e.2, h2'⟩⟩).elim
            · exact (hE2_ne ⟨⟨e.2, h1'⟩, ⟨e.1, h2'⟩⟩).elim
        ·
          have hC1_emp : C1 = ∅ := Finset.not_nonempty_iff_eq_empty.mp hC1_ne
          by_cases hE2_ne : (Si ∩ Bj).Nonempty ∧ Ti.Nonempty
          · rcases biclique_is_star hEsi with h1 | h2
            · have h1eq : (Si ∩ Bj).card = 1 := le_antisymm h1 (Finset.card_pos.mpr hE2_ne.1)
              obtain ⟨c0, hc0⟩ := Finset.card_eq_one.mp h1eq
              have hTi_sub : Ti ⊆ nbrs c0 := fun v hv => (mem_nbrs_iff c0 v).mpr (hEsi c0 (by rw [hc0]; simp) v hv)
              apply hsingle_star_cover c0 Ti hTi_sub
              intro e he hjt
              have hadj_e := (mem_pgEdges_iff e).mp he |>.2
              rw [← dirEdge_eq_of_mem_pgEdges he]
              rcases hEdge_s e he hjt with ⟨h1', _⟩ | ⟨h1', _⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩
              · rw [hC1_emp] at h1'; exact (Finset.notMem_empty _ h1').elim
              · rw [hC1_emp] at h1'; exact (Finset.notMem_empty _ h1').elim
              · rw [hc0, Finset.mem_singleton] at h1'; subst h1'; exact mem_starEdgesOf_left h2'
              · rw [hc0, Finset.mem_singleton] at h1'; subst h1'; exact mem_starEdgesOf_right hadj_e h2'
            · have h2eq : Ti.card = 1 := le_antisymm h2 (Finset.card_pos.mpr hE2_ne.2)
              obtain ⟨c0, hc0⟩ := Finset.card_eq_one.mp h2eq
              have hSi_sub : Si ∩ Bj ⊆ nbrs c0 := fun u hu =>
                (mem_nbrs_iff c0 u).mpr (by rw [pgAdj_symm]; exact hEsi u hu c0 (by rw [hc0]; simp))
              apply hsingle_star_cover c0 (Si ∩ Bj) hSi_sub
              intro e he hjt
              have hadj_e := (mem_pgEdges_iff e).mp he |>.2
              rw [← dirEdge_eq_of_mem_pgEdges he]
              rcases hEdge_s e he hjt with ⟨h1', _⟩ | ⟨h1', _⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩
              · rw [hC1_emp] at h1'; exact (Finset.notMem_empty _ h1').elim
              · rw [hC1_emp] at h1'; exact (Finset.notMem_empty _ h1').elim
              · rw [hc0, Finset.mem_singleton] at h2'; subst h2'; exact mem_starEdgesOf_right hadj_e h1'
              · rw [hc0, Finset.mem_singleton] at h2'; subst h2'; exact mem_starEdgesOf_left h1'
          ·
            apply hsingle_star_cover 0 ∅ (Finset.empty_subset _)
            intro e he hjt
            rcases hEdge_s e he hjt with ⟨h1', _⟩ | ⟨h1', _⟩ | ⟨h1', h2'⟩ | ⟨h1', h2'⟩
            · rw [hC1_emp] at h1'; exact (Finset.notMem_empty _ h1').elim
            · rw [hC1_emp] at h1'; exact (Finset.notMem_empty _ h1').elim
            · exact (hE2_ne ⟨⟨e.1, h1'⟩, ⟨e.2, h2'⟩⟩).elim
            · exact (hE2_ne ⟨⟨e.2, h1'⟩, ⟨e.1, h2'⟩⟩).elim
      by_cases hE3 : (Bi ∩ Bj).Nonempty ∧ Ai.Nonempty
      · exact hone_empty 1 (fun h => hE23 ⟨h, hE3⟩)
      · exact hone_empty 0 hE3

lemma main_proof (C : Circuit) (hV : ValidCirc C) (hMinAll : ∀ C', ValidCirc C' → C.size ≤ C'.size)
    (hand1 : andPairs 26 C = 1) : 64 ≤ C.size := by
  have hMin : IsMin C := ⟨hV, hMinAll⟩
  obtain ⟨i, j, hi, hj, hiand, hjand, hic_ij, huniq⟩ := exists_unique_andPair hand1
  have hij_ne : i ≠ j := by have := inCone_lt 26 C i j hic_ij; omega
  have hnot_i_out := not_orToOutput_i hMin hi hj hiand hjand hic_ij huniq
  have hT_eq : T_gates C = (A_gates C).erase i := by
    ext a
    simp only [Finset.mem_erase, mem_A_gates]
    constructor
    · intro haT
      have ha_info := mem_T_gates.mp haT
      refine ⟨fun heq => hnot_i_out (heq ▸ ha_info.2.2), ha_info.1, ha_info.2.1⟩
    · rintro ⟨hnei, ha_lt, ha_and⟩
      exact and_ne_i_in_T hMin huniq (mem_A_gates.mpr ⟨ha_lt, ha_and⟩) hnei
  have hOout_ge : (A_gates C).card ≤ (O_out C).card + 2 := by
    have h1 := oOut_card_bound hMin
    rw [hT_eq, Finset.card_erase_of_mem (mem_A_gates.mpr ⟨hi, hiand⟩)] at h1
    omega
  rcases j_orReaches_i hMin hi hj hiand hjand hic_ij huniq with hr0 | hr1
  · by_cases hr1' : OrReaches 26 C (opnd C j 1) i
    · exact case_both_reach hMin hi hj hiand hjand hij_ne huniq hT_eq hOout_ge hr0 hr1'
    · exact case_one_reach hMin hi hj hiand hjand hij_ne huniq hT_eq hOout_ge 0 hr0 hr1'
  · by_cases hr0' : OrReaches 26 C (opnd C j 0) i
    · exact case_both_reach hMin hi hj hiand hjand hij_ne huniq hT_eq hOout_ge hr0' hr1
    · exact case_one_reach hMin hi hj hiand hjand hij_ne huniq hT_eq hOout_ge 1 hr1 hr0'

end PEqualNP.Outside.L_meta_18294.Single

namespace PEqualNP.Outside.L_meta_18294.Main

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_18294.Flat

def positive (w : List Bool) : Prop :=
  ∃ p l : Fin 13, incidence p l ∧ w = List.ofFn (row {p} {l})

def negative (w : List Bool) : Prop :=
  ∃ X Y : Finset (Fin 13), star X Y ∧ answer X Y = false ∧ w = List.ofFn (row X Y)

lemma posLength (w : List Bool) (h : positive w) : w.length = 26 := by
  obtain ⟨p,l,_,rfl⟩ := h
  simp

lemma negLength (w : List Bool) (h : negative w) : w.length = 26 := by
  obtain ⟨X,Y,_,_,rfl⟩ := h
  simp

lemma posSome : ∃ w, positive w := ⟨_, 0, 0, by decide, rfl⟩

lemma negSome : ∃ w, negative w :=
  ⟨_, ∅, ∅, Or.inl ⟨0, by simp⟩, by decide, rfl⟩

lemma singletonInteresting (p l : Fin 13) (h : incidence p l) :
    star {p} {l} := Or.inl ⟨l, fun _ hp => (Finset.mem_singleton.mp hp).symm ▸ h⟩

lemma rowMono {X X' Y Y' : Finset (Fin 13)} (hX : X ⊆ X') (hY : Y ⊆ Y')
    {v : Fin 26} (h : row X Y v = true) : row X' Y' v = true := by
  rcases of_decide_eq_true h with ⟨p,hp,e⟩ | ⟨l,hl,e⟩
  · exact decide_eq_true (Or.inl ⟨p,hX hp,e⟩)
  · exact decide_eq_true (Or.inr ⟨l,hY hl,e⟩)

lemma fitsIff (C : Circuit) (hm : Monotone2 C) :
    fits C ↔ (∀ w, positive w → C.eval w = true) ∧
      ∀ w, negative w → C.eval w = false := by
  refine ⟨fun h => ⟨?_,?_⟩,?_⟩
  · rintro w ⟨p,l,hi,rfl⟩
    have eq : answer {p} {l} = true := decide_eq_true ⟨p,by simp,l,by simp,hi⟩
    exact (h _ _ (singletonInteresting p l hi)).trans eq
  · rintro w ⟨X,Y,hs,off,rfl⟩
    exact (h _ _ hs).trans off
  · intro h X Y hs
    cases hA : answer X Y with
    | false => exact h.2 _ ⟨X,Y,hs,hA,rfl⟩
    | true =>
      obtain ⟨p,hp,l,hl,adj⟩ := of_decide_eq_true hA
      have e := h.1 _ ⟨p,l,adj,rfl⟩
      have mono := legal_of C hm
      have grow : ∀ u, row {p} {l} u = true → row X Y u = true :=
        fun _ h => rowMono (Finset.singleton_subset_iff.mpr hp)
          (Finset.singleton_subset_iff.mpr hl) h
      exact val_mono C.gates mono _ _ grow C.output e

lemma incidenceInput_eq (X Y : Finset (Fin 13)) :
    PEqualNP.GenericRejection.incidenceInput X Y = List.ofFn (row X Y) := by
  unfold PEqualNP.GenericRejection.incidenceInput
  rw [← List.ofFn_fin_append]
  congr 1
  funext u
  refine Fin.addCases (fun p => ?_) (fun l => ?_) u
  · rw [Fin.append_left]
    apply decide_eq_decide.mpr
    constructor
    · intro hp
      exact Or.inl ⟨p,hp,rfl⟩
    · rintro (⟨q,hq,e⟩ | ⟨l,_,e⟩)
      · have pq : p = q := Fin.ext (congrArg (fun x : Fin 26 => x.val) e)
        exact pq.symm ▸ hq
      · have clash := congrArg Fin.val e
        simp only [Fin.val_castAdd, Fin.val_natAdd] at clash
        omega
  · rw [Fin.append_right]
    apply decide_eq_decide.mpr
    constructor
    · intro hl
      exact Or.inr ⟨l,hl,rfl⟩
    · rintro (⟨p,_,e⟩ | ⟨q,hq,e⟩)
      · have clash := congrArg Fin.val e
        simp only [Fin.val_castAdd, Fin.val_natAdd] at clash
        omega
      · have lq : l = q := by
          apply Fin.ext
          have z := congrArg Fin.val e
          simp only [Fin.val_natAdd] at z
          omega
        exact lq.symm ▸ hq

set_option maxRecDepth 32768 in
lemma singerIncidence : ∀ p l, p ∈ PEqualNP.HeptadCover.singerLines3 l ↔ incidence p l := by
  intro p
  fin_cases p <;> decide +kernel

lemma positiveRow (p l : Fin 13) :
    List.ofFn (row {p} {l}) =
      List.ofFn (fun x : Fin 13 => decide (x = p)) ++ List.ofFn (fun x : Fin 13 => decide (x = l)) := by
  rw [← incidenceInput_eq]
  simp [PEqualNP.GenericRejection.incidenceInput]

lemma validSingleIff (C : Circuit) :
    PEqualNP.Outside.L_meta_18294.Single.ValidCirc C ↔ Monotone2 C ∧ ReadsBack 26 C ∧ fits C := by
  constructor
  · rintro ⟨hm,hr,pos,neg⟩
    refine ⟨hm,hr,(fitsIff C hm).mpr ⟨?_,?_⟩⟩
    · rintro w ⟨p,l,hi,rfl⟩
      rw [positiveRow]
      exact pos p l ((singerIncidence p l).mpr hi)
    · rintro w ⟨X,Y,hs,hn,rfl⟩
      exact neg X Y hs hn
  · rintro ⟨hm,hr,fit⟩
    have checks := (fitsIff C hm).mp fit
    refine ⟨hm,hr,?_,?_⟩
    · intro p l hi
      rw [← positiveRow]
      exact checks.1 _ ⟨p,l,(singerIncidence p l).mp hi,rfl⟩
    · intro X Y hs hn
      exact checks.2 _ ⟨X,Y,hs,hn,rfl⟩

private lemma leastWitness {α : Type*} (P : α → Prop) (cost : α → ℕ) (exist : ∃ x, P x) :
    ∃ x, P x ∧ ∀ y, P y → cost x ≤ cost y := by
  classical
  have ex : ∃ n, ∃ x, P x ∧ cost x = n := by obtain ⟨x,h⟩ := exist; exact ⟨_,x,h,rfl⟩
  obtain ⟨w,hw,eq⟩ := Nat.find_spec ex
  exact ⟨w,hw,fun y hy => eq ▸ Nat.find_min' ex ⟨y,hy,rfl⟩⟩

abbrev nested (C : Circuit) (i j : ℕ) : Prop :=
  (gateAt C i).op = .and ∧ (gateAt C j).op = .and ∧ InCone 26 C i j

lemma minimalHard {C : Circuit} (h : Monotone2 C) (back : ReadsBack 26 C)
    (ok : fits C) (size : C.size ≤ 63) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 26 D ∧ fits D ∧ D.size ≤ C.size ∧
      2 ≤ PEqualNP.TopForm.andPairs 26 D ∧
      ∀ i j, nested D i j → ∃ w, negative w ∧ (D.wires w).getD (26+i) false = true := by
  let valid (E : Circuit) := Monotone2 E ∧ ReadsBack 26 E ∧ fits E
  obtain ⟨M,vM,mSize⟩ := leastWitness valid Circuit.size ⟨C,h,back,ok⟩
  obtain ⟨D,⟨vD,dM⟩,mAnd⟩ := leastWitness (fun E => valid E ∧ E.size = M.size)
    (PEqualNP.TopForm.andPairs 26) ⟨M,vM,rfl⟩
  obtain ⟨md, bd, fd⟩ := vD
  have dSize (E : Circuit) (ev : valid E) : D.size ≤ E.size := dM ▸ mSize E ev
  have dAnd (E : Circuit) (ev : valid E) (eq : E.size = D.size) :
      PEqualNP.TopForm.andPairs 26 D ≤ PEqualNP.TopForm.andPairs 26 E :=
    mAnd E ⟨ev,eq.trans dM⟩
  have ds : D.size ≤ C.size := dSize C ⟨h,back,ok⟩
  have forced : ∃ i j, nested D i j := by
    by_contra! flat
    have poor := flatLower md bd fd (by rintro ⟨i,j,h⟩; exact flat i j h)
    omega
  have spec := (fitsIff D md).mp fd
  have nonconstant : ∃ x y : List Bool, x.length = 26 ∧ y.length = 26 ∧
      D.eval x = true ∧ D.eval y = false := by
    obtain ⟨x,px⟩ := posSome
    obtain ⟨y,ny⟩ := negSome
    exact ⟨x,y,posLength x px,negLength y ny,spec.1 x px,spec.2 y ny⟩
  have two : ∀ g ∈ D.gates, ¬g.inputs.length < 2 := by
    intro g hg few
    obtain ⟨E,me,be,ev,small⟩ :=
      PEqualNP.Outside.L_meta_18294.Lift.short_case D md bd nonconstant ⟨g,hg,Or.inl few⟩
    have vf : fits E := by
      intro X Y hs
      rw [ev _ (by simp)]
      exact fd X Y hs
    exact (Nat.not_lt_of_ge (dSize E ⟨me,be,vf⟩)) small
  have ao : PEqualNP.TopForm.IsAO2 26 D := by
    refine ⟨fun g hg => (legal_of D md g hg).1, bd, ?_⟩
    intro g hg
    have hle := (legal_of D md g hg).2
    have hge := two g hg
    omega
  have count : 2 ≤ PEqualNP.TopForm.andPairs 26 D := by
    obtain ⟨i,j,hn⟩ := forced
    have bounds := PEqualNP.Outside.L_meta_18294.Lift.inCone_lt 26 D i j hn.2.2
    have pos : 0 < PEqualNP.TopForm.andPairs 26 D := by
      letI : DecidableEq GateOp := gateOpDecEq
      unfold PEqualNP.TopForm.andPairs
      apply Finset.card_pos.mpr
      refine ⟨(i,j), Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ?_, hn⟩⟩
      exact ⟨Finset.mem_range.mpr (by omega), Finset.mem_range.mpr bounds.2⟩
    by_contra! hlt
    have eq : PEqualNP.TopForm.andPairs 26 D = 1 := by omega
    have di := (validSingleIff D).mpr ⟨md,bd,fd⟩
    have large := PEqualNP.Outside.L_meta_18294.Single.main_proof D di
      (fun E Eok => dSize E ((validSingleIff E).mp Eok)) eq
    omega
  refine ⟨D,ao,fd,ds,count,?_⟩
  intro i j hn
  by_contra! absent
  have offAll (w) (hw : negative w) : (D.wires w).getD (26+i) false = false :=
    Bool.eq_false_iff.mpr (absent w hw)
  obtain ⟨E,me,be,fe,decr⟩ :=
    PEqualNP.Outside.L_meta_18294.Lift.main26 positive negative posLength negLength posSome negSome
      D md bd spec.1 spec.2 i j hn.1 hn.2.1 hn.2.2 offAll
  have ev : valid E := ⟨me,be,(fitsIff E me).mpr fe⟩
  rcases decr with d | ⟨eq,d⟩
  · exact (Nat.not_lt_of_ge (dSize E ev)) d
  · exact (Nat.not_lt_of_ge (dAnd E ev eq)) d

end PEqualNP.Outside.L_meta_18294.Main

namespace PEqualNP.Outside.L_meta_18294.Main

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.GenericRejection PEqualNP.HeptadCover

def negativeStar (X Y : Finset (Fin 13)) : Prop :=
  IsFalseInput singerLines3 X Y ∧
    ((∃ l, X ⊆ singerLines3 l) ∨ ∃ p, ∀ l ∈ Y, p ∈ singerLines3 l)

lemma negativeStar_iff (X Y : Finset (Fin 13)) :
    negativeStar X Y ↔ star X Y ∧ answer X Y = false := by
  have hstar : ((∃ l, X ⊆ singerLines3 l) ∨ ∃ p, ∀ l ∈ Y, p ∈ singerLines3 l) ↔ star X Y := by
    unfold star
    simp only [Finset.subset_iff, singerIncidence]
  have hfalse : IsFalseInput singerLines3 X Y ↔ answer X Y = false := by
    unfold IsFalseInput answer
    rw [decide_eq_false_iff_not]
    constructor
    · rintro h ⟨p,hp,l,hl,inc⟩
      exact (Finset.disjoint_left.mp (h l hl)) ((singerIncidence p l).mpr inc) hp
    · intro h l hl
      apply Finset.disjoint_left.mpr
      intro p hp hp'
      exact h ⟨p,hp',l,hl,(singerIncidence p l).mp hp⟩
  exact and_comm.trans ((and_congr hstar hfalse))

lemma goodIff (C : Circuit) (hm : Monotone2 C) :
    (RightOnIncidentPairs singerLines3 C ∧
      ∀ X Y, negativeStar X Y → C.eval (incidenceInput X Y) = false) ↔ fits C := by
  rw [fitsIff C hm]
  constructor
  · rintro ⟨hp,hn⟩
    constructor
    · rintro w ⟨p,l,hi,rfl⟩
      rw [← incidenceInput_eq]
      exact hp l p ((singerIncidence p l).mpr hi)
    · rintro w ⟨X,Y,hs,hA,rfl⟩
      rw [← incidenceInput_eq]
      exact hn X Y ((negativeStar_iff X Y).mpr ⟨hs,hA⟩)
  · rintro ⟨hp,hn⟩
    constructor
    · intro l p hi
      rw [incidenceInput_eq]
      exact hp _ ⟨p,l,(singerIncidence p l).mp hi,rfl⟩
    · intro X Y hs
      rw [incidenceInput_eq]
      obtain ⟨hc,hf⟩ := (negativeStar_iff X Y).mp hs
      exact hn _ ⟨X,Y,hc,hf,rfl⟩

end PEqualNP.Outside.L_meta_18294.Main

open PEqualNP.Outside.L_meta_18294.Main PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.GenericRejection PEqualNP.HeptadCover in
theorem PEqualNP.Outside.L_meta_18294 : (have x1 : Fin (13 : ℕ) → Finset (Fin (13 : ℕ)) := PEqualNP.HeptadCover.singerLines3; have x2 : Finset (Fin (13 : ℕ)) → Finset (Fin (13 : ℕ)) → Prop := fun (x2 x3 : Finset (Fin (13 : ℕ))) => PEqualNP.GenericRejection.IsFalseInput x1 x2 x3 ∧ ((∃ (x4 : Fin (13 : ℕ)), x2 ⊆ x1 x4) ∨ ∃ (x4 : Fin (13 : ℕ)), ∀ x5 ∈ x3, x4 ∈ x1 x5); have x3 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x3 : PEqualNP.CircuitLowerBounds.Circuit) => PEqualNP.GenericRejection.RightOnIncidentPairs x1 x3 ∧ ∀ (x4 x5 : Finset (Fin (13 : ℕ))), x2 x4 x5 → x3.eval (PEqualNP.GenericRejection.incidenceInput x4 x5) = Bool.false; have x4 : PEqualNP.CircuitLowerBounds.Circuit → Prop := fun (x4 : PEqualNP.CircuitLowerBounds.Circuit) => (2 : ℕ) ≤ PEqualNP.TopForm.andPairs (26 : ℕ) x4 ∧ ∀ (x5 x6 : ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x5).op = PEqualNP.CircuitLowerBounds.GateOp.and → (PEqualNP.MetaComplexity.NestedCover.gateAt x4 x6).op = PEqualNP.CircuitLowerBounds.GateOp.and → PEqualNP.EdgeOwnership.InCone (26 : ℕ) x4 x5 x6 → ∃ (x10 : Finset (Fin (13 : ℕ))) (x11 : Finset (Fin (13 : ℕ))), x2 x10 x11 ∧ (x4.wires (PEqualNP.GenericRejection.incidenceInput x10 x11)).getD ((26 : ℕ) + x5) Bool.false = Bool.true; ∀ (x5 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.MetaComplexity.Monotone2 x5 → PEqualNP.MetaComplexity.NestedCover.ReadsBack (26 : ℕ) x5 → x5.size ≤ (63 : ℕ) → x3 x5 → ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (26 : ℕ) x10 ∧ x10.size ≤ (63 : ℕ) ∧ x3 x10 ∧ x4 x10) := by
  dsimp only
  intro C hm back cs fit
  have f := (goodIff C hm).mp fit
  obtain ⟨D,dA,ok,ds,count,dirty⟩ := minimalHard hm back f cs
  have dm : Monotone2 D := by
    intro g hg
    obtain p := dA.1 g hg
    exact ⟨by simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using p, (dA.2.2 g hg).le⟩
  refine ⟨D,dA,ds.trans cs,(goodIff D dm).mpr ok,count,?_⟩
  intro i j hi hj co
  obtain ⟨_,⟨X,Y,hs,off,rfl⟩,on⟩ := dirty i j ⟨hi,hj,co⟩
  refine ⟨X,Y,(negativeStar_iff X Y).mpr ⟨hs,off⟩,?_⟩
  rwa [incidenceInput_eq]
