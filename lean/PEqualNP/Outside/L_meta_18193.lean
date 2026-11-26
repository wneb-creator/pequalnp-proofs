import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_18193

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def rg (ρ : ℕ → ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map ρ⟩

def rho (n i : ℕ) : ℕ := if i < n then i else i - n

theorem step_getD (w : List Bool) (g : Gate) (i : ℕ) : (step w g).getD i false =
    if i < w.length then w.getD i false
    else if i = w.length then g.op.eval (g.inputs.map fun i => w.getD i false) else false := by
  unfold step
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · rw [List.getD_append_right _ _ _ _ (by omega), h2]
    simp
  · exact List.getD_eq_default _ _ (by simp; omega)

theorem ren (n : ℕ) (gs : List Gate) : ∀ (w w' : List Bool) (L : ℕ), 2 * n ≤ L → w.length = L →
    w'.length = L - n → (∀ i, w'.getD (rho n i) false = w.getD i false) →
    ∀ i, ((gs.map (rg (rho n))).foldl step w').getD (rho n i) false
      = (gs.foldl step w).getD i false := by
  induction gs with
  | nil => intro w w' L _ _ _ h i; simpa using h i
  | cons g gs ih =>
    intro w w' L hL hw hw' hrel
    simp only [List.map_cons, List.foldl_cons]
    apply ih (step w g) (step w' (rg (rho n) g)) (L + 1) (by omega) (by simp [step, hw])
      (by simp [step, hw']; omega)
    intro i
    have hv : (rg (rho n) g).op.eval ((rg (rho n) g).inputs.map fun i => w'.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [rg, List.map_map]
      congr 1
      apply List.map_congr_left
      intro a _
      exact hrel a
    rw [step_getD, step_getD, hv, hw, hw']
    have hr : rho n i = if i < n then i else i - n := rfl
    by_cases h1 : i < L
    · have h2 : rho n i < L - n := by
        rw [hr]; split_ifs <;> omega
      rw [if_pos h1, if_pos h2]
      exact hrel i
    · by_cases h3 : i = L
      · have h4 : rho n i = L - n := by
          rw [hr]; split_ifs <;> omega
        rw [if_neg h1, if_pos h3, h4, if_neg (by omega), if_pos rfl]
      · have h4 : ¬ rho n i < L - n := by
          rw [hr]; split_ifs <;> omega
        have h5 : ¬ rho n i = L - n := by
          rw [hr]; split_ifs <;> omega
        rw [if_neg h1, if_neg h3, if_neg h4, if_neg h5]

theorem eval_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (f f' : ℕ → Bool)
    (h : ∀ i, f i = true → f' i = true) (hv : g.op.eval (g.inputs.map f) = true) :
    g.op.eval (g.inputs.map f') = true := by
  rcases hop with h1 | h1
  · rw [h1] at hv ⊢
    simp only [GateOp.eval, List.all_eq_true, List.mem_map, id] at hv ⊢
    rintro b ⟨a, ha, rfl⟩
    exact h a (hv (f a) ⟨a, ha, rfl⟩)
  · rw [h1] at hv ⊢
    simp only [GateOp.eval, List.any_eq_true, List.mem_map, id] at hv ⊢
    obtain ⟨b, ⟨a, ha, rfl⟩, hb⟩ := hv
    exact ⟨f' a, ⟨a, ha, rfl⟩, h a hb⟩

theorem mono_run (gs : List Gate) : ∀ (w w' : List Bool),
    (∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) → w.length = w'.length →
    (∀ i, w.getD i false = true → w'.getD i false = true) →
    ∀ i, (gs.foldl step w).getD i false = true → (gs.foldl step w').getD i false = true := by
  induction gs with
  | nil => intro w w' _ _ h i; simpa using h i
  | cons g gs ih =>
    intro w w' hall hl h
    simp only [List.foldl_cons]
    apply ih (step w g) (step w' g) (fun g' hg' => hall g' (List.mem_cons_of_mem _ hg'))
      (by simp [step, hl])
    intro i
    rw [step_getD, step_getD, hl]
    split_ifs with h1 h2
    · exact h i
    · exact eval_mono g (hall g List.mem_cons_self) _ _ h
    · exact id

theorem xx_get (n : ℕ) (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x ++ List.ofFn x).getD i false = (List.ofFn x).getD (rho n i) false := by
  unfold rho
  split_ifs with h
  · exact List.getD_append _ _ _ _ (by simpa using h)
  · rw [List.getD_append_right _ _ _ _ (by simpa using h)]
    simp

theorem one_get (n : ℕ) (u v : Fin n) (i : ℕ) (h : (oneEach u v).getD i false = true) :
    (i < n ∧ i = (u : ℕ)) ∨ (n ≤ i ∧ i - n = (v : ℕ)) := by
  unfold oneEach at h
  by_cases hi : i < n
  · rw [List.getD_append _ _ _ _ (by simpa using hi), List.getD_eq_getElem _ _ (by simpa using hi),
      List.getElem_ofFn] at h
    left
    refine ⟨hi, ?_⟩
    have := of_decide_eq_true h
    exact congrArg Fin.val this
  · right
    refine ⟨by omega, ?_⟩
    rw [List.getD_append_right _ _ _ _ (by simpa using hi)] at h
    by_cases h2 : i - n < n
    · have e : i - (List.ofFn fun i : Fin n => decide (i = u)).length = i - n := by simp
      rw [e, List.getD_eq_getElem _ _ (by simpa using h2), List.getElem_ofFn] at h
      have := of_decide_eq_true h
      exact congrArg Fin.val this
    · rw [List.getD_eq_default _ _ (by simp; omega)] at h
      exact absurd h (by simp)

theorem ofFn_get (n : ℕ) (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    (List.ofFn x).getD i false = x ⟨i, h⟩ := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]

theorem main (n s : ℕ) (h : RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s) :
    ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin n → Bool,
      C.eval (List.ofFn x) = decide (2 ≤ (List.ofFn x).count true) := by
  obtain ⟨C, hM, hs, hrep⟩ := h
  by_cases hn : n = 0
  · subst hn
    refine ⟨⟨[], 0⟩, by intro g hg; simp at hg, by simp [Circuit.size], ?_⟩
    intro x
    simp [Circuit.eval, Circuit.wires]
  · have hall : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
      intro g hg
      have h1 := (hM g hg).1
      simpa using h1
    refine ⟨⟨C.gates.map (rg (rho n)), rho n C.output⟩, ?_, by simpa [Circuit.size] using hs, ?_⟩
    · intro g hg
      obtain ⟨g0, hg0, rfl⟩ := List.mem_map.mp hg
      have h1 := hM g0 hg0
      simpa [rg] using h1
    · intro x
      have key : (⟨C.gates.map (rg (rho n)), rho n C.output⟩ : Circuit).eval (List.ofFn x)
          = C.eval (List.ofFn x ++ List.ofFn x) := by
        have h1 := ren n C.gates (List.ofFn x ++ List.ofFn x) (List.ofFn x) (2 * n) le_rfl
          (by simp; omega) (by simp; omega) (fun i => (xx_get n x i).symm) C.output
        exact h1
      rw [key, List.count_ofFn]
      by_cases h2 : ∃ u v : Fin n, u ≠ v ∧ x u = true ∧ x v = true
      · obtain ⟨u, v, huv, hu, hv⟩ := h2
        have hcard : 2 ≤ (Finset.univ.filter fun i : Fin n => x i = true).card := by
          have hsub : ({u, v} : Finset (Fin n)) ⊆ Finset.univ.filter fun i : Fin n => x i = true := by
            intro a ha
            simp only [Finset.mem_insert, Finset.mem_singleton] at ha
            rcases ha with rfl | rfl <;> simp [hu, hv]
          have := Finset.card_le_card hsub
          rw [Finset.card_pair huv] at this
          exact this
        rw [decide_eq_true hcard]
        have h0 : C.eval (oneEach u v) = true := by
          rw [hrep u v]
          exact decide_eq_true huv
        refine mono_run C.gates (oneEach u v) (List.ofFn x ++ List.ofFn x) hall
          (by simp [oneEach]) ?_ C.output h0
        intro i hi
        rw [xx_get]
        rcases one_get n u v i hi with ⟨h3, h4⟩ | ⟨h3, h4⟩
        · have hr : rho n i = i := if_pos h3
          rw [hr, ofFn_get n x i h3]
          have : (⟨i, h3⟩ : Fin n) = u := Fin.ext h4
          rw [this]; exact hu
        · have hlt : i - n < n := by rw [h4]; exact v.isLt
          have hr : rho n i = i - n := if_neg (by omega)
          rw [hr, ofFn_get n x (i - n) hlt]
          have : (⟨i - n, hlt⟩ : Fin n) = v := Fin.ext h4
          rw [this]; exact hv
      · have huniq : ∀ a b : Fin n, x a = true → x b = true → a = b := by
          intro a b ha hb
          by_contra hab
          exact h2 ⟨a, b, hab, ha, hb⟩
        have hcard : ¬ 2 ≤ (Finset.univ.filter fun i : Fin n => x i = true).card := by
          have : (Finset.univ.filter fun i : Fin n => x i = true).card ≤ 1 := by
            apply Finset.card_le_one.mpr
            intro a ha b hb
            exact huniq a b (Finset.mem_filter.mp ha).2 (Finset.mem_filter.mp hb).2
          omega
        rw [decide_eq_false hcard]
        by_contra hne
        have ht : C.eval (List.ofFn x ++ List.ofFn x) = true := by simpa using hne
        obtain ⟨w, hw⟩ : ∃ w : Fin n, ∀ a : Fin n, x a = true → a = w := by
          by_cases hex : ∃ a : Fin n, x a = true
          · obtain ⟨a, ha⟩ := hex
            exact ⟨a, fun b hb => huniq b a hb ha⟩
          · exact ⟨⟨0, Nat.pos_of_ne_zero hn⟩, fun a ha => absurd ⟨a, ha⟩ hex⟩
        have h0 : C.eval (oneEach w w) = true := by
          refine mono_run C.gates (List.ofFn x ++ List.ofFn x) (oneEach w w) hall
            (by simp [oneEach]) ?_ C.output ht
          intro i hi
          rw [xx_get] at hi
          unfold oneEach
          by_cases h3 : i < n
          · have hr : rho n i = i := if_pos h3
            rw [hr, ofFn_get n x i h3] at hi
            rw [List.getD_append _ _ _ _ (by simpa using h3), ofFn_get n _ i h3]
            exact decide_eq_true (hw _ hi)
          · have hr : rho n i = i - n := if_neg h3
            rw [hr] at hi
            by_cases h4 : i - n < n
            · rw [ofFn_get n x (i - n) h4] at hi
              rw [List.getD_append_right _ _ _ _ (by simpa using h3)]
              have e : i - (List.ofFn fun i : Fin n => decide (i = w)).length = i - n := by simp
              rw [e, ofFn_get n _ (i - n) h4]
              exact decide_eq_true (hw _ hi)
            · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
              exact absurd hi (by simp)
        rw [hrep w w] at h0
        simp at h0

end PEqualNP.Outside.L_meta_18193

theorem PEqualNP.Outside.L_meta_18193 : ∀ n s : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v : Fin n => decide (u ≠ v)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin n → Bool, C.eval (List.ofFn x) = decide (2 ≤ (List.ofFn x).count true) := by
  intro n s h
  exact PEqualNP.Outside.L_meta_18193.main n s h
