import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590_aux.GraphBound

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq_foldl (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl stepWire x := rfl

lemma foldl_getD_lt (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (gs.foldl stepWire w).getD i false = w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    have hlt : i < (stepWire w g).length := by simp [stepWire]; omega
    rw [ih (stepWire w g) hlt]
    simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_ge (w : List Bool) (i : ℕ) (hi : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma foldl_getD_gate (gs : List Gate) (w : List Bool) (j : ℕ) (hj : j < gs.length) :
    (gs.foldl stepWire w).getD (w.length + j) false =
      (gs[j]).op.eval ((gs[j]).inputs.map fun i =>
        if i < w.length + j then (gs.foldl stepWire w).getD i false else false) := by
  induction gs generalizing w j with
  | nil => simp at hj
  | cons g gs ih =>
    rw [List.foldl_cons]
    cases j with
    | zero =>
      have h1 : w.length < (stepWire w g).length := by simp [stepWire]
      rw [Nat.add_zero, foldl_getD_lt gs (stepWire w g) w.length h1]
      simp only [List.getElem_cons_zero]
      have h2 : (stepWire w g).getD w.length false =
          g.op.eval (g.inputs.map fun i => w.getD i false) := by
        simp [stepWire, List.getD_eq_getElem?_getD]
      rw [h2]
      congr 1
      apply List.map_congr_left
      intro i _
      by_cases hi : i < w.length
      · rw [ite_eq_left hi, foldl_getD_lt gs (stepWire w g) i (by simp [stepWire]; omega)]
        simp [stepWire, List.getD_eq_getElem?_getD, List.getElem?_append_left hi]
      · rw [ite_eq_right hi]; exact getD_ge w i (by omega)
    | succ j =>
      have hj' : j < gs.length := by simpa using hj
      have key := ih (stepWire w g) j hj'
      have hl : (stepWire w g).length = w.length + 1 := by simp [stepWire]
      rw [hl] at key
      have e : w.length + (j + 1) = w.length + 1 + j := by omega
      simp only [List.getElem_cons_succ]
      rw [e]
      exact key

def val (C : Circuit) (x : List Bool) (u : ℕ) : Bool := (C.wires x).getD u false

lemma gateAt_eq {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma gateAt_mem {C : Circuit} {j : ℕ} (hj : j < C.gates.length) : gateAt C j ∈ C.gates := by
  rw [gateAt_eq hj]; exact List.getElem_mem hj

lemma val_input {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {u : ℕ} (hu : u < n) :
    val C x u = x.getD u false := by
  unfold val; rw [wires_eq_foldl]; exact foldl_getD_lt _ _ _ (by omega)

lemma val_gate {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {j : ℕ}
    (hj : j < C.gates.length) :
    val C x (n + j) = (gateAt C j).op.eval ((gateAt C j).inputs.map fun i =>
      if i < n + j then val C x i else false) := by
  subst hx
  rw [gateAt_eq hj]
  exact foldl_getD_gate C.gates x j hj

lemma val_or {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.or) :
    val C x (n + r) = true ↔ ∃ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
  constructor
  · rintro ⟨i, hi, h⟩
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h; exact ⟨i, hi, hlt, h⟩
    · rw [ite_eq_right hlt] at h; cases h
  · rintro ⟨i, hi, hlt, h⟩
    exact ⟨i, hi, by rw [ite_eq_left hlt]; exact h⟩

lemma val_and {n : ℕ} {C : Circuit} {x : List Bool} (hx : x.length = n) {r : ℕ}
    (hr : r < C.gates.length) (hop : (gateAt C r).op = GateOp.and) :
    val C x (n + r) = true ↔ ∀ i ∈ (gateAt C r).inputs, i < n + r ∧ val C x i = true := by
  rw [val_gate hx hr, hop]
  simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
  constructor
  · intro h i hi
    have h' := h i hi
    by_cases hlt : i < n + r
    · rw [ite_eq_left hlt] at h'; exact ⟨hlt, h'⟩
    · rw [ite_eq_right hlt] at h'; cases h'
  · intro h i hi
    rw [ite_eq_left (h i hi).1]; exact (h i hi).2

lemma val_ofFn {n : ℕ} (C : Circuit) (x : Fin n → Bool) (u : Fin n) :
    val C (List.ofFn x) u.val = x u := by
  rw [val_input (n := n) (by simp) u.isLt]
  simp [List.getD_eq_getElem?_getD]

lemma cover_bound (n : ℕ) (H : SimpleGraph (Fin n)) (T : Finset ℕ) (c : ℕ → Fin n)
    (hcov : ∀ u v : Fin n, H.Adj u v → ∃ a, a ∈ T ∧ (c a = u ∨ c a = v))
    (K : Finset (Fin n)) (hK : IsMinCover H K) : K.card ≤ T.card := by
  classical
  refine (hK.2 (T.image c) ?_).trans Finset.card_image_le
  intro u v huv
  obtain ⟨a, ha, h | h⟩ := hcov u v huv
  · left
    rw [Finset.mem_coe, ← h]
    exact Finset.mem_image_of_mem _ ha
  · right
    rw [Finset.mem_coe, ← h]
    exact Finset.mem_image_of_mem _ ha

lemma cover_g {α : Type} [DecidableEq α] (n : ℕ) (g : ℕ → Gate)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset α)
    (hf : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (Z : Finset ℕ) (r : ℕ) (R : Finset ℕ)
    (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k)
    (stops : Finset ℕ)
    (hstops : ∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or))) :
    f (n + r) ⊆ stops.biUnion f ∧ ∀ k, k ∈ R → f (n + k) ⊆ f (n + r) := by
  have hdown : ∀ k, k ∈ R → f (n + k) ⊆ stops.biUnion f := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro hk u hu
      by_cases hs : k ∈ Z ∨ (g k).op ≠ GateOp.or
      · refine Finset.mem_biUnion.2 ⟨n + k, (hstops _).2 (Or.inr ⟨by omega, ?_, ?_⟩), hu⟩
        · rwa [Nat.add_sub_cancel_left]
        · rwa [Nat.add_sub_cancel_left]
      · have hkZ : k ∉ Z := fun h => hs (Or.inl h)
        have hor : (g k).op = GateOp.or := by
          by_contra h
          exact hs (Or.inr h)
        obtain ⟨w, hw, huw⟩ := (hf k hor u).1 hu
        by_cases hwn : w < n
        · exact Finset.mem_biUnion.2 ⟨w, (hstops _).2 (Or.inl ⟨hwn, k, hk, hkZ, hor, hw⟩), huw⟩
        · have hwk := hback k w hw
          have hweq : n + (w - n) = w := by omega
          have hwR : w - n ∈ R :=
            (hR _).2 (((hR k).1 hk).tail ⟨hkZ, hor, by rwa [hweq]⟩)
          exact ih (w - n) (by omega) hwR (by rwa [hweq])
  have hup : ∀ k, k ∈ R → f (n + k) ⊆ f (n + r) := by
    intro k hk
    have h := (hR k).1 hk
    clear hk
    induction h with
    | refl => exact Finset.Subset.refl _
    | tail _ hbc ih =>
      intro u hu
      exact ih ((hf _ hbc.2.1 u).2 ⟨_, hbc.2.2, hu⟩)
  exact ⟨hdown r ((hR r).2 Relation.ReflTransGen.refl), hup⟩

def TwoNe {α : Type} (g : ℕ → Gate) (f : ℕ → Finset α) (k : ℕ) : Prop :=
  ∃ w1 ∈ (g k).inputs, ∃ w2 ∈ (g k).inputs, w1 ≠ w2 ∧ (f w1).Nonempty ∧ (f w2).Nonempty

lemma cone_count2 {α : Type} [DecidableEq α] (n : ℕ) (g : ℕ → Gate) (f : ℕ → Finset α)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (Z : Finset ℕ)
    (hlen : ∀ k, k ∉ Z → (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (r : ℕ) (R : Finset ℕ)
    (hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
      (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k)
    (stops : Finset ℕ)
    (hstops : ∀ w, w ∈ stops ↔
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or)))
    (I : Finset ℕ)
    (hI : ∀ k, k ∈ R → k ∉ Z → (g k).op = GateOp.or → TwoNe g f k → k ∈ I) :
    (stops.filter (fun w => (f w).Nonempty)).card ≤ I.card + 1 := by
  classical
  set E : Finset ℕ := R.filter (fun k => k ∉ Z ∧ (g k).op = GateOp.or) with hE
  set N : ℕ → Finset ℕ := fun k => (g k).inputs.toFinset.filter (fun w => (f w).Nonempty)
    with hN
  set U : Finset ℕ := insert (n + r) (E.biUnion N) with hU
  set E2 := E.filter (fun k => 2 ≤ (N k).card) with hE2
  set Ene := E.filter (fun k => (f (n + k)).Nonempty) with hEne
  have hE2I : E2 ⊆ I := by
    intro k hk
    simp only [hE2, hE, Finset.mem_filter] at hk
    obtain ⟨⟨hkR, hkZ, hor⟩, h2⟩ := hk
    apply hI k hkR hkZ hor
    obtain ⟨w1, hw1, w2, hw2, hne⟩ := Finset.one_lt_card.1 (by omega : 1 < (N k).card)
    simp only [hN, Finset.mem_filter, List.mem_toFinset] at hw1 hw2
    exact ⟨w1, hw1.1, w2, hw2.1, hne, hw1.2, hw2.2⟩
  have hNk : ∀ k ∈ E, (N k).card ≤ (if 2 ≤ (N k).card then 1 else 0) +
      (if (f (n + k)).Nonempty then 1 else 0) := by
    intro k hk
    simp only [hE, Finset.mem_filter] at hk
    have hc : (N k).card ≤ 2 := (Finset.card_filter_le _ _).trans
      ((List.toFinset_card_le _).trans (hlen k hk.2.1 hk.2.2))
    have hne : 1 ≤ (N k).card → (f (n + k)).Nonempty := by
      intro h1
      obtain ⟨w, hw⟩ := Finset.card_pos.1 (by omega : 0 < (N k).card)
      simp only [hN, Finset.mem_filter, List.mem_toFinset] at hw
      obtain ⟨u, hu⟩ := hw.2
      exact ⟨u, (hf2 k hk.2.2 u).2 ⟨w, hw.1, hu⟩⟩
    rcases Nat.lt_or_ge (N k).card 1 with h0 | h0
    · omega
    · rw [ite_eq_left (hne h0)]
      split_ifs <;> omega
  have hsum : (E.biUnion N).card ≤ E2.card + Ene.card := by
    calc (E.biUnion N).card ≤ ∑ k ∈ E, (N k).card := Finset.card_biUnion_le
      _ ≤ ∑ k ∈ E, ((if 2 ≤ (N k).card then 1 else 0) +
          (if (f (n + k)).Nonempty then 1 else 0)) := Finset.sum_le_sum hNk
      _ = E2.card + Ene.card := by
        rw [Finset.sum_add_distrib, hE2, hEne, Finset.card_filter, Finset.card_filter]
  have hUcard : U.card ≤ E2.card + Ene.card + 1 := by
    have hins : U.card ≤ (E.biUnion N).card + 1 := Finset.card_insert_le (n + r) (E.biUnion N)
    omega
  have hmem : ∀ w, (f w).Nonempty → (w = n + r ∨ ∃ k' ∈ E, w ∈ (g k').inputs) → w ∈ U := by
    rintro w hw (h | ⟨k', hk', hin⟩)
    · rw [h]
      exact Finset.mem_insert_self _ _
    · refine Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨k', hk', ?_⟩)
      simp only [hN, Finset.mem_filter, List.mem_toFinset]
      exact ⟨hin, hw⟩
  have hRU : ∀ k, k ∈ R → n + k = n + r ∨ ∃ k' ∈ E, n + k ∈ (g k').inputs := by
    intro k hk
    rcases Relation.ReflTransGen.cases_tail ((hR k).1 hk) with h | ⟨b, hb, hb1, hb2, hb3⟩
    · left
      rw [h]
    · right
      refine ⟨b, ?_, hb3⟩
      rw [hE, Finset.mem_filter]
      exact ⟨(hR b).2 hb, hb1, hb2⟩
  set S2 : Finset ℕ := Ene.image (fun k => n + k) with hS2
  have hS2card : S2.card = Ene.card :=
    Finset.card_image_of_injective _ (fun a b h => Nat.add_left_cancel h)
  have hdisj : Disjoint (stops.filter (fun w => (f w).Nonempty)) S2 := by
    rw [Finset.disjoint_left]
    intro w hw hw2
    rw [Finset.mem_filter] at hw
    rw [hS2, Finset.mem_image] at hw2
    obtain ⟨k, hk, rfl⟩ := hw2
    rw [hEne, hE, Finset.mem_filter, Finset.mem_filter] at hk
    rcases (hstops _).1 hw.1 with ⟨h1, _⟩ | ⟨_, _, h3⟩
    · omega
    · rw [Nat.add_sub_cancel_left] at h3
      rcases h3 with h3 | h3
      · exact hk.1.2.1 h3
      · exact h3 hk.1.2.2
  have hsub : (stops.filter (fun w => (f w).Nonempty)) ∪ S2 ⊆ U := by
    intro w hw
    rcases Finset.mem_union.1 hw with hw | hw
    · rw [Finset.mem_filter] at hw
      rcases (hstops _).1 hw.1 with ⟨_, k, hk, hk1, hk2, hk3⟩ | ⟨h1, h2, _⟩
      · refine hmem w hw.2 (Or.inr ⟨k, ?_, hk3⟩)
        rw [hE, Finset.mem_filter]
        exact ⟨hk, hk1, hk2⟩
      · have := hRU _ h2
        rw [Nat.add_sub_cancel' h1] at this
        exact hmem w hw.2 this
    · rw [hS2, Finset.mem_image] at hw
      obtain ⟨k, hk, rfl⟩ := hw
      rw [hEne, hE, Finset.mem_filter, Finset.mem_filter] at hk
      exact hmem _ hk.2 (hRU k hk.1.1)
  have h3 := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, hS2card] at h3
  have h4 := Finset.card_le_card hE2I
  omega

lemma top_step2 (n : ℕ) (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (Z : Finset ℕ) (ρ : ℕ) (c : Fin n) (E0 : Finset (Sym2 (Fin n)))
    (hZ : ∀ k, k ∈ Z → f (n + k) ⊆ f ρ →
      (∀ v, v ∈ f (n + k) → s(c, v) ∈ E0) ∨ (f (n + k)).card ≤ 1) :
    ∃ Znew : Finset ℕ, Disjoint Z Znew ∧
      (∀ k, k ∈ Znew → (g k).op = GateOp.or ∧ TwoNe g f k ∧ n ≤ ρ ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (ρ - n) k ∧ f (n + k) ⊆ f ρ) ∧
      (((f ρ).image (fun v => s(c, v))) \ E0).card ≤ Znew.card + 1 := by
  classical
  by_cases hρ : ρ < n
  · refine ⟨∅, Finset.disjoint_empty_right _, by simp, ?_⟩
    calc (((f ρ).image (fun v => s(c, v))) \ E0).card
        ≤ ((f ρ).image (fun v => s(c, v))).card := Finset.card_le_card Finset.sdiff_subset
      _ ≤ (f ρ).card := Finset.card_image_le
      _ ≤ 1 := hf1 ρ hρ
      _ ≤ (∅ : Finset ℕ).card + 1 := by simp
  · have hρn : n ≤ ρ := Nat.le_of_not_lt hρ
    obtain ⟨r, rfl⟩ : ∃ r, ρ = n + r := ⟨ρ - n, by omega⟩
    have hle : ∀ k, Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k → k ≤ r := by
      intro k h
      induction h with
      | refl => exact le_refl _
      | tail _ hbc ih =>
        have := hback _ _ hbc.2.2
        omega
    set R : Finset ℕ := (Finset.range (r + 1)).filter (fun k =>
      Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k) with hRdef
    have hR : ∀ k, k ∈ R ↔ Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
        (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k := by
      intro k
      rw [hRdef, Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · intro h
        exact ⟨Nat.lt_succ_of_le (hle k h), h⟩
    set stops : Finset ℕ := (Finset.range (n + r + 1)).filter (fun w =>
      (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
      (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or))) with hsdef
    have hstops : ∀ w, w ∈ stops ↔
        (w < n ∧ ∃ k ∈ R, k ∉ Z ∧ (g k).op = GateOp.or ∧ w ∈ (g k).inputs) ∨
        (n ≤ w ∧ w - n ∈ R ∧ (w - n ∈ Z ∨ (g (w - n)).op ≠ GateOp.or)) := by
      intro w
      rw [hsdef, Finset.mem_filter, Finset.mem_range]
      constructor
      · exact fun h => h.2
      · intro h
        refine ⟨?_, h⟩
        rcases h with ⟨h1, _⟩ | ⟨h1, h2, _⟩
        · omega
        · have := hle _ ((hR _).1 h2)
          omega
    set Znew : Finset ℕ := R.filter (fun k => k ∉ Z ∧ (g k).op = GateOp.or ∧ TwoNe g f k)
      with hZn
    obtain ⟨hcov, hup⟩ := cover_g n g hback f hf2 Z r R hR stops hstops
    have hcnt : (stops.filter (fun w => (f w).Nonempty)).card ≤ Znew.card + 1 :=
      cone_count2 n g f hf2 Z (fun k _ h => hlen k h) r R hR stops hstops Znew (by
        intro k hk hkZ hor htwo
        rw [hZn, Finset.mem_filter]
        exact ⟨hk, hkZ, hor, htwo⟩)
    refine ⟨Znew, ?_, ?_, ?_⟩
    · rw [Finset.disjoint_left]
      intro k hk hk2
      rw [hZn, Finset.mem_filter] at hk2
      exact hk2.2.1 hk
    · intro k hk
      rw [hZn, Finset.mem_filter] at hk
      refine ⟨hk.2.2.1, hk.2.2.2, hρn, ?_, hup k hk.1⟩
      rw [Nat.add_sub_cancel_left]
      have hreach : ∀ k, Relation.ReflTransGen (fun k k' : ℕ => k ∉ Z ∧
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k →
          Relation.ReflTransGen (fun k k' : ℕ =>
            (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) r k := by
        intro k h
        induction h with
        | refl => exact Relation.ReflTransGen.refl
        | tail _ hbc ih => exact ih.tail hbc.2
      exact hreach k ((hR k).1 hk.1)
    · have hsub : ((f (n + r)).image (fun v => s(c, v))) \ E0 ⊆
          (stops.filter (fun w => (f w).Nonempty)).biUnion
            (fun w => ((f w).image (fun v => s(c, v))) \ E0) := by
        intro e he
        rw [Finset.mem_sdiff, Finset.mem_image] at he
        obtain ⟨⟨v, hv, rfl⟩, he0⟩ := he
        obtain ⟨w, hw, hvw⟩ := Finset.mem_biUnion.1 (hcov hv)
        refine Finset.mem_biUnion.2 ⟨w, Finset.mem_filter.2 ⟨hw, ⟨v, hvw⟩⟩, ?_⟩
        rw [Finset.mem_sdiff]
        exact ⟨Finset.mem_image_of_mem _ hvw, he0⟩
      have hone : ∀ w, w ∈ stops.filter (fun w => (f w).Nonempty) →
          (((f w).image (fun v => s(c, v))) \ E0).card ≤ 1 := by
        intro w hw'
        have hw := (Finset.mem_filter.1 hw').1
        have himg : ∀ t : Finset (Fin n), t.card ≤ 1 →
            ((t.image (fun v => s(c, v))) \ E0).card ≤ 1 := fun t ht =>
          (Finset.card_le_card Finset.sdiff_subset).trans (Finset.card_image_le.trans ht)
        rcases (hstops w).1 hw with ⟨hwn, _⟩ | ⟨hwn, hwR, hw2⟩
        · exact himg _ (hf1 w hwn)
        · have hweq : n + (w - n) = w := by omega
          rcases hw2 with hz | hnor
          · have hsubw : f (n + (w - n)) ⊆ f (n + r) := hup _ hwR
            rcases hZ _ hz hsubw with hall | hc1
            · rw [hweq] at hall
              have hempty : ((f w).image (fun v => s(c, v))) \ E0 = ∅ := by
                rw [Finset.sdiff_eq_empty_iff_subset]
                intro e he
                obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 he
                exact hall v hv
              rw [hempty]
              simp
            · rw [hweq] at hc1
              exact himg _ hc1
          · have := hf3 _ hnor
            rw [hweq] at this
            exact himg _ this
      calc (((f (n + r)).image (fun v => s(c, v))) \ E0).card
          ≤ ((stops.filter (fun w => (f w).Nonempty)).biUnion
              (fun w => ((f w).image (fun v => s(c, v))) \ E0)).card :=
            Finset.card_le_card hsub
        _ ≤ (stops.filter (fun w => (f w).Nonempty)).card * 1 :=
            Finset.card_biUnion_le_card_mul _ _ _ hone
        _ ≤ Znew.card + 1 := by omega

lemma star_count2 (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (B : Finset ℕ) (hB : ∀ k, k ∈ B → (f (n + k)).card ≤ 1)
    (l : List (Fin n × ℕ))
    (hadj : ∀ p, p ∈ l → ∀ v, v ∈ f p.2 → G.Adj p.1 v) :
    ∃ Z : Finset ℕ,
      (∀ k, k ∈ Z → k ∉ B ∧ (g k).op = GateOp.or ∧ TwoNe g f k ∧ ∃ p, p ∈ l ∧ n ≤ p.2 ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (p.2 - n) k ∧ f (n + k) ⊆ f p.2) ∧
      (l.toFinset.biUnion (fun p => (f p.2).image (fun v => s(p.1, v)))).card
        ≤ l.length + Z.card := by
  classical
  induction l with
  | nil => exact ⟨∅, by simp, by simp⟩
  | cons p l ih =>
    obtain ⟨Z, hZ1, hZ2⟩ := ih (fun q hq => hadj q (List.mem_cons_of_mem _ hq))
    set E0 := l.toFinset.biUnion (fun p => (f p.2).image (fun v => s(p.1, v))) with hE0
    obtain ⟨Znew, hd, hn1, hn2⟩ := top_step2 n g hlen hback f hf1 hf2 hf3 (Z ∪ B) p.2 p.1 E0 (by
      intro k hk hsub
      rcases Finset.mem_union.1 hk with hk | hk
      · obtain ⟨_, _, _, q, hq, _, _, hfq⟩ := hZ1 k hk
        by_cases hc : q.1 = p.1
        · left
          intro v hv
          rw [hE0]
          refine Finset.mem_biUnion.2 ⟨q, List.mem_toFinset.2 hq, ?_⟩
          rw [← hc]
          exact Finset.mem_image_of_mem _ (hfq hv)
        · right
          by_contra hcard
          have h2 : 1 < (f (n + k)).card := by omega
          obtain ⟨v, hv, v', hv', hne⟩ := Finset.one_lt_card.1 h2
          have a1 : G.Adj p.1 v := hadj p List.mem_cons_self v (hsub hv)
          have a2 : G.Adj p.1 v' := hadj p List.mem_cons_self v' (hsub hv')
          have b1 : G.Adj q.1 v := hadj q (List.mem_cons_of_mem _ hq) v (hfq hv)
          have b2 : G.Adj q.1 v' := hadj q (List.mem_cons_of_mem _ hq) v' (hfq hv')
          exact h4 p.1 v q.1 v' (fun h => hc h.symm) hne ⟨a1, b1.symm, b2, a2.symm⟩
      · exact Or.inr (hB k hk))
    have hd1 : Disjoint Z Znew := Finset.disjoint_of_subset_left Finset.subset_union_left hd
    refine ⟨Z ∪ Znew, ?_, ?_⟩
    · intro k hk
      rcases Finset.mem_union.1 hk with hk | hk
      · obtain ⟨h0, h1, ht, q, hq, h2⟩ := hZ1 k hk
        exact ⟨h0, h1, ht, q, List.mem_cons_of_mem _ hq, h2⟩
      · obtain ⟨h1, ht, h2, h3, h5⟩ := hn1 k hk
        refine ⟨?_, h1, ht, p, List.mem_cons_self, h2, h3, h5⟩
        intro hkB
        exact (Finset.disjoint_left.1 hd (Finset.mem_union_right _ hkB)) hk
    · rw [List.toFinset_cons, Finset.biUnion_insert, Finset.card_union_of_disjoint hd1,
        List.length_cons, ← hE0]
      have hsplit : (f p.2).image (fun v => s(p.1, v)) ∪ E0 =
          (((f p.2).image (fun v => s(p.1, v))) \ E0) ∪ E0 := by
        rw [Finset.sdiff_union_self_eq_union]
      have hle := Finset.card_union_le (((f p.2).image (fun v => s(p.1, v))) \ E0) E0
      rw [← hsplit] at hle
      omega

lemma assemble2 (n : ℕ) (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (g : ℕ → Gate)
    (hlen : ∀ k, (g k).op = GateOp.or → (g k).inputs.length ≤ 2)
    (hback : ∀ k, ∀ i ∈ (g k).inputs, i < n + k)
    (f : ℕ → Finset (Fin n))
    (hf1 : ∀ w, w < n → (f w).card ≤ 1)
    (hf2 : ∀ k, (g k).op = GateOp.or →
      ∀ u, u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w)
    (hf3 : ∀ k, (g k).op ≠ GateOp.or → (f (n + k)).card ≤ 1)
    (B : Finset ℕ) (hB : ∀ k, k ∈ B → (f (n + k)).card ≤ 1)
    (T : Finset ℕ) (o : ℕ → Fin 2 → ℕ)
    (hstar : ∀ a, a ∈ T → (∀ u, u ∈ f (o a 0) → ∀ v, v ∈ f (o a 1) → G.Adj u v) ∧
      ((f (o a 0)).card ≤ 1 ∨ (f (o a 1)).card ≤ 1))
    (Es : Finset (Sym2 (Fin n)))
    (hEs : ∀ e, e ∈ Es → ∃ a, a ∈ T ∧ ∃ u, u ∈ f (o a 0) ∧ ∃ v, v ∈ f (o a 1) ∧ e = s(u, v)) :
    (∃ Z : Finset ℕ,
      (∀ k, k ∈ Z → k ∉ B ∧ (g k).op = GateOp.or ∧ TwoNe g f k ∧ ∃ a, a ∈ T ∧ ∃ b : Fin 2,
        n ≤ o a b ∧
        Relation.ReflTransGen (fun k k' : ℕ =>
          (g k).op = GateOp.or ∧ n + k' ∈ (g k).inputs) (o a b - n) k ∧
        f (n + k) ⊆ f (o a b) ∧ (f (o a (1 - b))).card = 1) ∧
      Es.card ≤ T.card + Z.card) ∧
    ∀ (H : SimpleGraph (Fin n)) (K : Finset (Fin n)),
      (∀ u v : Fin n, H.Adj u v → s(u, v) ∈ Es) → IsMinCover H K → K.card ≤ T.card := by
  classical
  by_cases hEe : Es = ∅
  · subst hEe
    refine ⟨⟨∅, by simp, by simp⟩, ?_⟩
    intro H K hH hK
    have h0 := hK.2 ∅ (by
      intro u v huv
      exact absurd (hH u v huv) (Finset.notMem_empty _))
    simp only [Finset.card_empty] at h0
    omega
  · obtain ⟨e0, he0⟩ := Finset.nonempty_iff_ne_empty.2 hEe
    obtain ⟨_, _, v0, _, _⟩ := hEs e0 he0
    set c : ℕ → Fin n := fun a =>
      if (f (o a 0)).card ≤ 1 then (if h : (f (o a 0)).Nonempty then h.choose else v0)
      else (if h : (f (o a 1)).Nonempty then h.choose else v0) with hc
    set ρ : ℕ → ℕ := fun a => if (f (o a 0)).card ≤ 1 then o a 1 else o a 0 with hρ
    have hkey : ∀ a, a ∈ T → ∀ u, u ∈ f (o a 0) → ∀ v, v ∈ f (o a 1) →
        (c a = u ∧ v ∈ f (ρ a)) ∨ (c a = v ∧ u ∈ f (ρ a)) := by
      intro a ha u hu v hv
      by_cases h0 : (f (o a 0)).card ≤ 1
      · left
        have hne : (f (o a 0)).Nonempty := ⟨u, hu⟩
        refine ⟨?_, ?_⟩
        · simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
          exact Finset.card_le_one.1 h0 _ hne.choose_spec _ hu
        · simp only [hρ, h0, ↓reduceIte]
          exact hv
      · right
        have h1 : (f (o a 1)).card ≤ 1 := by
          rcases (hstar a ha).2 with h | h
          · exact absurd h h0
          · exact h
        have hne : (f (o a 1)).Nonempty := ⟨v, hv⟩
        refine ⟨?_, ?_⟩
        · simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
          exact Finset.card_le_one.1 h1 _ hne.choose_spec _ hv
        · simp only [hρ, h0, ↓reduceIte]
          exact hu
    set T' : Finset ℕ := T.filter (fun a => (f (o a 0)).Nonempty ∧ (f (o a 1)).Nonempty)
      with hT'
    have hT'T : ∀ a, a ∈ T' → a ∈ T := fun a ha => (Finset.mem_filter.1 ha).1
    have hT'card : T'.card ≤ T.card := Finset.card_le_card (Finset.filter_subset _ _)
    have hadjc : ∀ a, a ∈ T' → ∀ v, v ∈ f (ρ a) → G.Adj (c a) v := by
      intro a ha' v hv
      have ha := hT'T a ha'
      have hnn := (Finset.mem_filter.1 ha').2
      by_cases h0 : (f (o a 0)).card ≤ 1
      · simp only [hρ, h0, ↓reduceIte] at hv
        have hne := hnn.1
        simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
        exact (hstar a ha).1 _ hne.choose_spec v hv
      · simp only [hρ, h0, ↓reduceIte] at hv
        have hne := hnn.2
        simp only [hc, h0, ↓reduceIte, hne, ↓reduceDIte]
        exact ((hstar a ha).1 v hv _ hne.choose_spec).symm
    have hEs' : ∀ e, e ∈ Es → ∃ a, a ∈ T' ∧ ∃ v, v ∈ f (ρ a) ∧ e = s(c a, v) := by
      intro e he
      obtain ⟨a, ha, u, hu, v, hv, rfl⟩ := hEs e he
      have ha' : a ∈ T' := Finset.mem_filter.2 ⟨ha, ⟨u, hu⟩, ⟨v, hv⟩⟩
      rcases hkey a ha u hu v hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨a, ha', v, h2, by rw [h1]⟩
      · exact ⟨a, ha', u, h2, by rw [h1]; exact Sym2.eq_swap⟩
    refine ⟨?_, ?_⟩
    · obtain ⟨Z, hZ1, hZ2⟩ := star_count2 n G h4 g hlen hback f hf1 hf2 hf3 B hB
        (T'.toList.map (fun a => (c a, ρ a))) (by
          intro p hp v hv
          obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
          exact hadjc a (Finset.mem_toList.1 ha) v hv)
      refine ⟨Z, ?_, ?_⟩
      · intro k hk
        obtain ⟨h1, h2, ht, p, hp, h3, h5, h6⟩ := hZ1 k hk
        obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hp
        have ha' := Finset.mem_toList.1 ha
        have hnn := (Finset.mem_filter.1 ha').2
        refine ⟨h1, h2, ht, a, hT'T a ha', ?_⟩
        by_cases h0 : (f (o a 0)).card ≤ 1
        · refine ⟨1, ?_⟩
          simp only [hρ, h0, ↓reduceIte] at h3 h5 h6
          have e : (1 - 1 : Fin 2) = 0 := by decide
          rw [e]
          exact ⟨h3, h5, h6, le_antisymm h0 (Finset.card_pos.2 hnn.1)⟩
        · refine ⟨0, ?_⟩
          simp only [hρ, h0, ↓reduceIte] at h3 h5 h6
          have e : (1 - 0 : Fin 2) = 1 := by decide
          rw [e]
          have h1' : (f (o a 1)).card ≤ 1 := by
            rcases (hstar a (hT'T a ha')).2 with h | h
            · exact absurd h h0
            · exact h
          exact ⟨h3, h5, h6, le_antisymm h1' (Finset.card_pos.2 hnn.2)⟩
      · have hsub : Es ⊆ (T'.toList.map (fun a => (c a, ρ a))).toFinset.biUnion
            (fun p => (f p.2).image (fun v => s(p.1, v))) := by
          intro e he
          obtain ⟨a, ha, v, hv, rfl⟩ := hEs' e he
          refine Finset.mem_biUnion.2 ⟨(c a, ρ a), ?_, Finset.mem_image_of_mem _ hv⟩
          exact List.mem_toFinset.2 (List.mem_map.2 ⟨a, Finset.mem_toList.2 ha, rfl⟩)
        have h1 := Finset.card_le_card hsub
        rw [List.length_map, Finset.length_toList] at hZ2
        omega
    · intro H K hH hK
      refine (cover_bound n H T' c ?_ K hK).trans hT'card
      intro u v huv
      obtain ⟨a, ha, w, hw, he⟩ := hEs' _ (hH u v huv)
      refine ⟨a, ha, ?_⟩
      have := Sym2.eq_iff.1 he
      rcases this with ⟨h1, _⟩ | ⟨_, h2⟩
      · exact Or.inl h1.symm
      · exact Or.inr h2.symm

lemma foldl_length (gs : List Gate) (w : List Bool) :
    (gs.foldl stepWire w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [stepWire]
    omega

def wire {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  val C (List.ofFn x) w

lemma wire_past {n : ℕ} (C : Circuit) (x : Fin n → Bool) {w : ℕ}
    (hw : n + C.gates.length ≤ w) : wire C x w = false := by
  apply getD_ge
  rw [wires_eq_foldl, foldl_length, List.length_ofFn]
  exact hw

def singletonInput {n : ℕ} (v : Fin n) (z : Fin n) : Bool := decide (z = v)

def pair {n : ℕ} (u v z : Fin n) : Bool := decide (z = u ∨ z = v)

lemma pair_edge {n : ℕ} (G : SimpleGraph (Fin n)) {u v : Fin n}
    (h : ∃ a b, G.Adj a b ∧ pair u v a = true ∧ pair u v b = true) : G.Adj u v := by
  obtain ⟨a, b, hab, ha, hb⟩ := h
  simp only [pair, decide_eq_true_eq] at ha hb
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact (G.loopless.irrefl _ hab).elim
  · exact hab
  · exact hab.symm
  · exact (G.loopless.irrefl _ hab).elim

def cleanGate (n : ℕ) (C : Circuit) (k : ℕ) : Gate :=
  if k < C.gates.length then
    ⟨(gateAt C k).op, (gateAt C k).inputs.filter (· < n + k)⟩
  else ⟨GateOp.or, []⟩

def readPort (limit missing w : ℕ) : ℕ := if w < limit then w else missing

def port (n : ℕ) (C : Circuit) (k : ℕ) (b : Fin 2) : ℕ :=
  let l := (gateAt C k).inputs
  let a := l.headD (n + C.gates.length)
  readPort (n + k) (n + C.gates.length) (l.getD b a)

lemma list_shapes {α : Type} (l : List α) (h : l.length ≤ 2) :
    l = [] ∨ (∃ a, l = [a]) ∨ ∃ a b, l = [a, b] := by
  match l with
  | [] => exact Or.inl rfl
  | [a] => exact Or.inr (Or.inl ⟨a, rfl⟩)
  | [a,b] => exact Or.inr (Or.inr ⟨a,b,rfl⟩)
  | a::b::c::l => simp at h

lemma readPort_true {n : ℕ} (C : Circuit) (x : Fin n → Bool) (k w : ℕ) :
    val C (List.ofFn x) (readPort (n + k) (n + C.gates.length) w) = true ↔
      w < n + k ∧ val C (List.ofFn x) w = true := by
  change wire C x (readPort (n + k) (n + C.gates.length) w) = true ↔
    w < n + k ∧ wire C x w = true
  by_cases h : w < n + k
  · simp [readPort, h]
  · simp [readPort, h, wire_past C x (show n + C.gates.length ≤ n + C.gates.length from le_rfl)]

lemma and_ports {n : ℕ} (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.and) (hlen : (gateAt C k).inputs.length ≤ 2)
    (hne : (gateAt C k).inputs ≠ []) (x : Fin n → Bool) :
    wire C x (n + k) = true ↔ wire C x (port n C k 0) = true ∧
      wire C x (port n C k 1) = true := by
  change val C (List.ofFn x) (n + k) = true ↔ _
  rw [val_and (by simp) hk hop]
  rcases list_shapes _ hlen with h | ⟨a, h⟩ | ⟨a, b, h⟩
  · exact (hne h).elim
  · simp [port, h, List.getD_eq_getElem?_getD, readPort_true, wire]
  · simp [port, h, List.getD_eq_getElem?_getD, readPort_true, wire]

lemma port_true_mem {n : ℕ} {C : Circuit} {k : ℕ} (hk : k < C.gates.length)
    (b : Fin 2) (x : Fin n → Bool) (hv : wire C x (port n C k b) = true) :
    port n C k b ∈ (cleanGate n C k).inputs := by
  have hb : b = 0 ∨ b = 1 := by fin_cases b <;> simp
  unfold port at hv ⊢
  dsimp only at hv ⊢
  rw [wire, readPort_true] at hv
  rw [readPort, ite_eq_left hv.1]
  simp only [cleanGate, ite_eq_left hk, List.mem_filter, decide_eq_true_eq]
  refine ⟨?_, hv.1⟩
  cases h : (gateAt C k).inputs with
  | nil => simp [h] at hv
           omega
  | cons a l =>
    rcases hb with rfl | rfl
    · simp [List.getD_eq_getElem?_getD]
    · cases l <;> simp [List.getD_eq_getElem?_getD]

lemma monotone_wire {n : ℕ} (C : Circuit)
    (hAO : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and ∨ (gateAt C k).op = GateOp.or)
    {x y : Fin n → Bool} (h : ∀ u, x u = true → y u = true) :
    ∀ w, wire C x w = true → wire C y w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hlt : w < n
    · let u : Fin n := ⟨w, hlt⟩
      exact (val_ofFn C y u).trans (h u ((val_ofFn C x u).symm.trans hw))
    by_cases hend : n + C.gates.length ≤ w
    · rw [wire_past C x hend] at hw
      cases hw
    have he : n + (w - n) = w := by omega
    have hk : w - n < C.gates.length := by omega
    rw [← he] at hw ⊢
    rcases hAO _ hk with hop | hop
    · rw [wire, val_and (by simp) hk hop] at hw ⊢
      intro i hi
      obtain ⟨hlt', ht⟩ := hw i hi
      exact ⟨hlt', ih i (by omega) ht⟩
    · rw [wire, val_or (by simp) hk hop] at hw ⊢
      obtain ⟨i, hi, hlt', ht⟩ := hw
      exact ⟨i, hi, hlt', ih i (by omega) ht⟩

lemma other_of_two {α : Type} {l : List α} (hlen : l.length ≤ 2)
    {a b : α} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    ∀ c ∈ l, c = a ∨ c = b := by
  rcases list_shapes l hlen with rfl | ⟨d, rfl⟩ | ⟨d, e, rfl⟩
  · simp at ha
  · simp only [List.mem_singleton] at ha hb
    exact (hab (ha.trans hb.symm)).elim
  · intro c hc
    simp at ha hb hc
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact hc
    · exact hc.symm
    · exact (hab rfl).elim

lemma reachable_budget (N roots R : Finset ℕ) (children : ℕ → Finset ℕ)
    (S : ℕ → Prop) [DecidablePred S] (hchild : ∀ k, (children k).card ≤ 2)
    (hR : ∀ j, j ∈ R ↔ j ∈ N ∧ ∃ r ∈ roots,
      Relation.ReflTransGen (fun k j => k ∈ N ∧ ¬ S k ∧ j ∈ children k) r j) :
    (R.filter S).card ≤ (R.filter fun k => ¬ S k).card + roots.card := by
  classical
  let I := R.filter fun k => ¬ S k
  let A := R.filter S
  change A.card ≤ I.card + roots.card
  have hsub : R ⊆ roots ∪ I.biUnion children := by
    intro j hj
    obtain ⟨_, r, hr, hp⟩ := (hR j).1 hj
    rcases Relation.ReflTransGen.cases_tail hp with h | ⟨k, hpath, hk, hs, hkj⟩
    · exact Finset.mem_union_left _ (h ▸ hr)
    · exact Finset.mem_union_right _ (Finset.mem_biUnion.2
        ⟨k, Finset.mem_filter.2 ⟨(hR k).2 ⟨hk, r, hr, hpath⟩, hs⟩, hkj⟩)
  have hsum : (I.biUnion children).card ≤ I.card * 2 :=
    Finset.card_biUnion_le_card_mul _ _ _ (fun k _ => hchild k)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le roots (I.biUnion children))
  have hsplit : A.card + I.card = R.card := by
    exact Finset.card_filter_add_card_filter_not S
  omega

lemma boxes_star {n : ℕ} (G : SimpleGraph (Fin n))
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (S T : Finset (Fin n)) (h : ∀ u ∈ S, ∀ v ∈ T, G.Adj u v) :
    S.card ≤ 1 ∨ T.card ≤ 1 := by
  by_contra! hn
  obtain ⟨a, ha, c, hc, hac⟩ := Finset.one_lt_card.1 hn.1
  obtain ⟨b, hb, d, hd, hbd⟩ := Finset.one_lt_card.1 hn.2
  exact h4 a b c d hac hbd ⟨h a ha b hb, (h c hc b hb).symm, h c hc d hd, (h a ha d hd).symm⟩

inductive OrPath (n : ℕ) (g : ℕ → Gate) (u : Fin n) : ℕ → Prop
  | input : OrPath n g u u.val
  | or_step (k w : ℕ) : (g k).op = GateOp.or → w ∈ (g k).inputs →
      OrPath n g u w → OrPath n g u (n + k)

set_option maxHeartbeats 1600000 in
lemma graph_bound {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (h4 : ∀ a b c d : Fin n, a ≠ c → b ≠ d →
      ¬ (G.Adj a b ∧ G.Adj b c ∧ G.Adj c d ∧ G.Adj d a))
    (C : Circuit)
    (hAO : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hout : ∀ x : Fin n → Bool, wire C x C.output = true ↔
      ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true)
    (hcase : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and →
      (∀ x : Fin n → Bool,
        wire C x (n + k) = true → ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true) ∨
      (∀ u v u' v' : Fin n, G.Adj u v → G.Adj u' v' →
        wire C (pair u v) (n + k) = true → wire C (pair u' v') (n + k) = true →
        (u = u' ∧ v = v') ∨ (u = v' ∧ v = u'))) :
    ∃ K : Finset (Fin n), (∀ u v, G.Adj u v → u ∈ K ∨ v ∈ K) ∧
      G.edgeFinset.card + K.card ≤ C.gates.length + 1 := by
  classical
  let L := C.gates.length
  let g := cleanGate n C
  let o := port n C
  let f : ℕ → Finset (Fin n) :=
    fun w => Finset.univ.filter fun u => OrPath n g u w
  have hfmem (w : ℕ) (u : Fin n) : u ∈ f w ↔ OrPath n g u w := by simp [f]
  have hinput (w : ℕ) (hw : w < n) : f w = {⟨w, hw⟩} := by
    ext u
    rw [hfmem, Finset.mem_singleton]
    constructor
    · intro h
      cases h with
      | input => exact Fin.ext rfl
      | or_step k w' _ _ _ => omega
    · rintro rfl
      exact OrPath.input
  have hclean (k : ℕ) (hk : k < L) :
      g k = ⟨(gateAt C k).op, (gateAt C k).inputs.filter (· < n + k)⟩ := by
    exact ite_eq_left (show k < C.gates.length from hk)
  have hclean_past (k : ℕ) (hk : ¬ k < L) : g k = ⟨GateOp.or, []⟩ := by
    exact ite_eq_right (show ¬ k < C.gates.length from hk)
  have hgate (k : ℕ) (hk : k < L) : (g k).op = (gateAt C k).op := by
    rw [hclean k hk]
  have hlen (k : ℕ) : (g k).inputs.length ≤ 2 := by
    by_cases hk : k < L
    · rw [hclean k hk]
      exact (List.length_filter_le _ _).trans (hAO _ (gateAt_mem hk)).2
    · simp [hclean_past k hk]
  have hback (k w : ℕ) (hw : w ∈ (g k).inputs) : w < n + k := by
    by_cases hk : k < L
    · simp only [hclean k hk, List.mem_filter, decide_eq_true_eq] at hw
      exact hw.2
    · simp [hclean_past k hk] at hw
  have hor (k : ℕ) (hk : k < L) (hop : (g k).op = GateOp.or) (x : Fin n → Bool) :
      wire C x (n + k) = true ↔ ∃ w ∈ (g k).inputs, wire C x w = true := by
    rw [wire, val_or (by simp) hk ((hgate k hk).symm.trans hop)]
    simp only [hclean k hk, List.mem_filter, decide_eq_true_eq, and_assoc, wire]
  have hnoSingle (u : Fin n) :
      ¬ ∃ a b, G.Adj a b ∧ singletonInput u a = true ∧ singletonInput u b = true := by
    rintro ⟨a,b,hab,ha,hb⟩
    simp only [singletonInput, decide_eq_true_eq] at ha hb
    subst a
    subst b
    exact G.loopless.irrefl _ hab
  have hfNotOr (k : ℕ) (hop : (g k).op ≠ GateOp.or) : f (n + k) = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.2
    intro u hu
    rw [hfmem] at hu
    generalize he : n + k = w at hu
    cases hu with
    | input => have := u.isLt; omega
    | or_step k' w' hor' _ _ =>
      have hk' : k' = k := by omega
      subst hk'
      exact hop hor'
  have hfAnd (k : ℕ) (_ : k < L) (hop : (g k).op = GateOp.and) : f (n + k) = ∅ :=
    hfNotOr k (by rw [hop]; rintro ⟨⟩)
  have hfOr (k : ℕ) (hop : (g k).op = GateOp.or) (u : Fin n) :
      u ∈ f (n + k) ↔ ∃ w ∈ (g k).inputs, u ∈ f w := by
    simp only [hfmem]
    constructor
    · intro hu
      generalize he : n + k = w at hu
      cases hu with
      | input => have := u.isLt; omega
      | or_step k' w' _ hw' hp =>
        have hk' : k' = k := by omega
        subst hk'
        exact ⟨w', hw', hp⟩
    · rintro ⟨w, hw, hp⟩
      exact OrPath.or_step k w hop hw hp
  have hf_wire (w : ℕ) (u : Fin n) (hu : u ∈ f w) : wire C (singletonInput u) w = true := by
    rw [hfmem] at hu
    induction hu with
    | input =>
      change val C (List.ofFn (singletonInput u)) u.val = true
      rw [val_ofFn]
      simp [singletonInput]
    | or_step k w' hop hw' _ ih =>
      have hk : k < L := by
        by_contra h
        simp [hclean_past k h] at hw'
      exact (hor k hk hop (singletonInput u)).2 ⟨w', hw', ih⟩
  let Sound : ℕ → Prop := fun k =>
    ∀ x : Fin n → Bool, wire C x (n + k) = true → ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true
  let Single : ℕ → Prop := fun k =>
    ∀ u v u' v' : Fin n, G.Adj u v → G.Adj u' v' →
      wire C (pair u v) (n + k) = true → wire C (pair u' v') (n + k) = true →
      (u = u' ∧ v = v') ∨ (u = v' ∧ v = u')
  have hSingle (k : ℕ) (hk : k < L) (hop : (g k).op = GateOp.and) (hns : ¬ Sound k) : Single k := by
    rcases hcase k hk ((hgate k hk).symm.trans hop) with hs | hsg
    · exact (hns hs).elim
    · exact hsg
  have hand (k : ℕ) (hk : k < L) (hop : (g k).op = GateOp.and) (hs : Sound k) (x : Fin n → Bool) :
      wire C x (n + k) = true ↔ wire C x (o k 0) = true ∧ wire C x (o k 1) = true := by
    have hop' := (hgate k hk).symm.trans hop
    refine and_ports C k hk hop' (hAO _ (gateAt_mem hk)).2 ?_ x
    intro hnil
    have hall : wire C (fun _ : Fin n => false) (n + k) = true :=
      (val_and (by simp) hk hop').2 (by simp [hnil])
    obtain ⟨_, _, _, ha, _⟩ := hs _ hall
    cases ha
  have hadj (k : ℕ) (hk : k < L) (hop : (g k).op = GateOp.and) (hs : Sound k) :
      ∀ u ∈ f (o k 0), ∀ v ∈ f (o k 1), G.Adj u v := by
    intro u hu v hv
    have hmono : ∀ {x y : Fin n → Bool}, (∀ a, x a = true → y a = true) →
        ∀ w, wire C x w = true → wire C y w = true := by
      intro x y
      exact monotone_wire C (fun t ht => (hAO _ (gateAt_mem ht)).1)
    have hl := hmono (x := singletonInput u) (y := pair u v) (by
      intro a ha
      simp only [singletonInput, decide_eq_true_eq] at ha
      simp [pair, ha]) _ (hf_wire _ _ hu)
    have hr := hmono (x := singletonInput v) (y := pair u v) (by
      intro a ha
      simp only [singletonInput, decide_eq_true_eq] at ha
      simp [pair, ha]) _ (hf_wire _ _ hv)
    exact pair_edge G (hs _ ((hand k hk hop hs _).2 ⟨hl, hr⟩))

  let N := (Finset.range L).filter fun k => f (n + k) = ∅
  let child := fun k =>
    ((g k).inputs.toFinset.filter fun w => n ≤ w ∧ f w = ∅).image fun w => w - n
  have hc_mem (k j : ℕ) : j ∈ child k ↔ n + j ∈ (g k).inputs ∧ f (n + j) = ∅ := by
    simp only [child, Finset.mem_image, Finset.mem_filter, List.mem_toFinset]
    constructor
    · rintro ⟨w, ⟨hw, hn, hf⟩, rfl⟩
      rw [Nat.add_sub_cancel' hn]
      exact ⟨hw, hf⟩
    · rintro ⟨hw, hf⟩
      exact ⟨n + j, ⟨hw, by omega, hf⟩, Nat.add_sub_cancel_left n j⟩
  have hc_card (k : ℕ) : (child k).card ≤ 2 :=
    Finset.card_image_le.trans ((Finset.card_filter_le _ _).trans ((List.toFinset_card_le _).trans (hlen k)))
  let M := (Finset.range L).filter fun k => (g k).op = GateOp.or ∧ (f (n + k)).Nonempty
  have hc_mix (k : ℕ) (hk : k ∈ M) : (child k).card ≤ 1 := by
    obtain ⟨_, hop, u, hu⟩ := Finset.mem_filter.1 hk
    obtain ⟨w, hw, hu'⟩ := (hfOr k hop u).1 hu
    by_contra! h
    obtain ⟨j, hj, t, ht, hne⟩ := Finset.one_lt_card.1 h
    obtain ⟨hj', hj0⟩ := (hc_mem k j).1 hj
    obtain ⟨ht', ht0⟩ := (hc_mem k t).1 ht
    rcases other_of_two (hlen k) hj' ht' (by omega) w hw with e | e
    · rw [e, hj0] at hu'
      exact Finset.notMem_empty _ hu'
    · rw [e, ht0] at hu'
      exact Finset.notMem_empty _ hu'
  let roots := insert (C.output - n) (M.biUnion child)
  let S := fun k =>
    (g k).op = GateOp.and ∧ ((Sound k ∧ (f (o k 0)).Nonempty ∧ (f (o k 1)).Nonempty) ∨ ¬ Sound k)
  let step := fun k j => k ∈ N ∧ ¬ S k ∧ j ∈ child k
  let R := N.filter fun k => ∃ r ∈ roots, Relation.ReflTransGen step r k
  let A := R.filter S
  let I := R.filter fun k => ¬ S k
  let A1 := A.filter Sound
  let A2 := A.filter fun k => ¬ Sound k
  have hA_split : A1.card + A2.card = A.card := Finset.card_filter_add_card_filter_not Sound
  have hN (k : ℕ) : k ∈ N ↔ k < L ∧ f (n + k) = ∅ := by simp [N]
  have hRlt (k : ℕ) (hk : k ∈ R) : k < L := ((hN k).1 (Finset.mem_filter.1 hk).1).1
  have hA (k : ℕ) (hk : k ∈ A) : k ∈ R ∧ S k := Finset.mem_filter.1 hk
  have hRroot (k : ℕ) (hk : k ∈ N) (hr : k ∈ roots) : k ∈ R :=
    Finset.mem_filter.2 ⟨hk, k, hr, Relation.ReflTransGen.refl⟩
  have hRchild (k j : ℕ) (hk : k ∈ R) (hs : ¬ S k) (hj : j ∈ child k) : j ∈ R := by
    obtain ⟨hkN, r, hr, hp⟩ := Finset.mem_filter.1 hk
    obtain ⟨hj', hj0⟩ := (hc_mem k j).1 hj
    have hlt := hback k _ hj'
    exact Finset.mem_filter.2 ⟨(hN j).2 ⟨by have := hRlt k hk; omega, hj0⟩,
      r, hr, hp.tail ⟨hkN, hs, hj⟩⟩

  have hedge (u v : Fin n) (huv : G.Adj u v) :
      (∃ k ∈ A1, ∃ a ∈ f (o k 0), ∃ b ∈ f (o k 1), s(u,v) = s(a,b)) ∨
      (∃ k ∈ A2, wire C (pair u v) (n + k) = true) := by
    let witnessed :=
      (∃ k ∈ A1, ∃ a ∈ f (o k 0), ∃ b ∈ f (o k 1), s(u,v) = s(a,b)) ∨
      (∃ k ∈ A2, wire C (pair u v) (n + k) = true)
    have descend : ∀ w, wire C (pair u v) w = true →
        (f w = ∅ → w - n ∈ R) → witnessed ∨ u ∈ f w ∨ v ∈ f w := by
      intro w
      induction w using Nat.strong_induction_on with
      | _ w ih =>
        intro hw hreach
        by_cases hlt : w < n
        · let a : Fin n := ⟨w, hlt⟩
          have htrue : pair u v a = true := (val_ofFn C _ a).symm.trans hw
          simp only [pair, decide_eq_true_eq] at htrue
          right
          rw [hinput w hlt]
          rcases htrue with h | h
          · left
            exact Finset.mem_singleton.2 h.symm
          · right
            exact Finset.mem_singleton.2 h.symm
        by_cases hend : n + L ≤ w
        · rw [wire_past C _ hend] at hw
          cases hw
        let k := w - n
        have hk : k < L := by dsimp [k]; omega
        have he : n + k = w := by dsimp [k]; omega
        have hAO' := (hAO _ (gateAt_mem hk)).1
        rw [← hgate k hk] at hAO'
        have hktrue : wire C (pair u v) (n + k) = true := by rwa [he]
        have drop (i : ℕ) (hi : i ∈ (g k).inputs) (hit : wire C (pair u v) i = true)
            (hstep : f i = ∅ → i - n ∈ R) := ih i (by rw [← he]; exact hback k i hi) hit hstep
        have mkchild (i : ℕ) (hi : i ∈ (g k).inputs) (hi0 : f i = ∅) :
            i - n ∈ child k ∧ i - n ∈ N := by
          have hni : n ≤ i := by
            by_contra! hn
            rw [hinput i hn] at hi0
            simp at hi0
          have hei : n + (i - n) = i := Nat.add_sub_cancel' hni
          have hbi := hback k i hi
          exact ⟨(hc_mem k _).2 (by rw [hei]; exact ⟨hi, hi0⟩),
            (hN _).2 ⟨by omega, by rwa [hei]⟩⟩
        rcases hAO' with hop | hop
        · have hf0 := hfAnd k hk hop
          have hkr : k ∈ R := hreach (he ▸ hf0)
          by_cases hsk : Sound k
          · obtain ⟨ha, hb⟩ := (hand k hk hop hsk _).1 hktrue
            have ham : o k 0 ∈ (g k).inputs := port_true_mem hk 0 _ ha
            have hbm : o k 1 ∈ (g k).inputs := port_true_mem hk 1 _ hb
            by_cases hs : S k
            · have hs' : (f (o k 0)).Nonempty ∧ (f (o k 1)).Nonempty := by
                rcases hs.2 with ⟨_, h0, h1⟩ | hns
                · exact ⟨h0, h1⟩
                · exact (hns hsk).elim
              have hkA1 : k ∈ A1 := Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hkr, hs⟩, hsk⟩
              have hra : f (o k 0) = ∅ → o k 0 - n ∈ R := fun h =>
                (Finset.nonempty_iff_ne_empty.1 hs'.1 h).elim
              have hrb : f (o k 1) = ∅ → o k 1 - n ∈ R := fun h =>
                (Finset.nonempty_iff_ne_empty.1 hs'.2 h).elim
              rcases drop _ ham ha hra with hed | hua | hva
              · exact Or.inl hed
              · rcases drop _ hbm hb hrb with hed | hub | hvb
                · exact Or.inl hed
                · exact (G.loopless.irrefl _ (hadj k hk hop hsk u hua u hub)).elim
                · exact Or.inl (Or.inl ⟨k, hkA1, u, hua, v, hvb, rfl⟩)
              · rcases drop _ hbm hb hrb with hed | hub | hvb
                · exact Or.inl hed
                · exact Or.inl (Or.inl ⟨k, hkA1, v, hva, u, hub, Sym2.eq_swap⟩)
                · exact (G.loopless.irrefl _ (hadj k hk hop hsk v hva v hvb)).elim
            · have hn : f (o k 0) = ∅ ∨ f (o k 1) = ∅ := by
                by_contra! hne
                exact hs ⟨hop, Or.inl ⟨hsk, hne.1, hne.2⟩⟩
              have go (i : ℕ) (hi : i ∈ (g k).inputs) (hit : wire C (pair u v) i = true)
                  (hi0 : f i = ∅) : witnessed := by
                have hir := hRchild k _ hkr hs (mkchild i hi hi0).1
                simpa [hi0] using drop i hi hit (fun _ => hir)
              exact Or.inl (hn.elim (go _ ham ha) (go _ hbm hb))
          · have hs : S k := ⟨hop, Or.inr hsk⟩
            have hkA2 : k ∈ A2 := Finset.mem_filter.2 ⟨Finset.mem_filter.2 ⟨hkr, hs⟩, hsk⟩
            exact Or.inl (Or.inr ⟨k, hkA2, hktrue⟩)
        · obtain ⟨i, hi, hit⟩ := (hor k hk hop _).1 hktrue
          have hstep (hi0 : f i = ∅) : i - n ∈ R := by
            obtain ⟨hic, hin⟩ := mkchild i hi hi0
            rcases (f (n + k)).eq_empty_or_nonempty with h0 | hne
            · exact hRchild k _ (hreach (he ▸ h0))
                (by
                  intro h
                  have h' := h.1
                  rw [hop] at h'
                  cases h') hic
            · have hkm : k ∈ M := Finset.mem_filter.2 ⟨Finset.mem_range.2 hk, hop, hne⟩
              exact hRroot _ hin (Finset.mem_insert_of_mem (Finset.mem_biUnion.2 ⟨k, hkm, hic⟩))
          rw [← he]
          rcases drop i hi hit hstep with hed | hui | hvi
          · exact Or.inl hed
          · exact Or.inr (Or.inl ((hfOr k hop u).2 ⟨i, hi, hui⟩))
          · exact Or.inr (Or.inr ((hfOr k hop v).2 ⟨i, hi, hvi⟩))
    have ho0 : f C.output = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.2
      intro a ha
      exact hnoSingle a ((hout _).1 (hf_wire _ _ ha))
    have ho : wire C (pair u v) C.output = true :=
      (hout _).2 ⟨u, v, huv, by simp [pair], by simp [pair]⟩
    have hbound : C.output < n + L := by
      by_contra! h
      rw [wire_past C _ h] at ho
      cases ho
    have hn : n ≤ C.output := by
      by_contra! h
      rw [hinput C.output h] at ho0
      simp at ho0
    have hroot : C.output - n ∈ R := hRroot _ ((hN _).2
      ⟨by omega, by rwa [Nat.add_sub_cancel' hn]⟩) (Finset.mem_insert_self _ _)
    simpa only [ho0, Finset.notMem_empty, or_false] using descend C.output ho (fun _ => hroot)

  let Es1 : Finset (Sym2 (Fin n)) :=
    G.edgeFinset.filter fun e => ∃ k ∈ A1, ∃ a ∈ f (o k 0), ∃ b ∈ f (o k 1), e = s(a,b)
  let Es2 : Finset (Sym2 (Fin n)) := G.edgeFinset \ Es1
  have hEs1 (e : Sym2 (Fin n)) (he : e ∈ Es1) :
      ∃ k ∈ A1, ∃ a ∈ f (o k 0), ∃ b ∈ f (o k 1), e = s(a,b) :=
    (Finset.mem_filter.1 he).2
  have hA1_lt (k : ℕ) (hk : k ∈ A1) : k < L :=
    hRlt k (hA k (Finset.mem_filter.1 hk).1).1
  have hA1_op (k : ℕ) (hk : k ∈ A1) : (g k).op = GateOp.and :=
    (hA k (Finset.mem_filter.1 hk).1).2.1
  have hA1_sound (k : ℕ) (hk : k ∈ A1) : Sound k :=
    (Finset.mem_filter.1 hk).2
  have hstar (k : ℕ) (hk : k ∈ A1) : ∀ u ∈ f (o k 0), ∀ v ∈ f (o k 1), G.Adj u v :=
    hadj k (hA1_lt k hk) (hA1_op k hk) (hA1_sound k hk)
  obtain ⟨⟨Z, hZ, hEZ⟩, hcov⟩ :=
    assemble2 n G h4 g (fun k _ => hlen k) hback f
      (fun w hw => by rw [hinput w hw]; simp) hfOr
      (fun k hop => by rw [hfNotOr k hop]; simp)
      ∅ (by simp) A1 o (fun k hk => ⟨hstar k hk, boxes_star G h4 _ _ (hstar k hk)⟩)
      Es1 hEs1
  let H1 : SimpleGraph (Fin n) :=
    { Adj := fun u v => G.Adj u v ∧ s(u, v) ∈ Es1
      symm := ⟨fun u v h => ⟨h.1.symm, by rw [Sym2.eq_swap]; exact h.2⟩⟩
      loopless := ⟨fun u h => G.loopless.irrefl u h.1⟩ }
  have hK1exists : ∃ K1 : Finset (Fin n), IsMinCover H1 K1 := by
    let P := fun m : ℕ => ∃ K1 : Finset (Fin n), K1.card = m ∧ H1.IsVertexCover (K1 : Set (Fin n))
    have hp : ∃ m, P m := ⟨Finset.univ.card, Finset.univ, rfl, by intro u v huv; simp⟩
    obtain ⟨K1, hkc, hK1⟩ := Nat.find_spec hp
    exact ⟨K1, hK1, fun J hJ => hkc ▸ Nat.find_min' hp ⟨J, rfl, hJ⟩⟩
  obtain ⟨K1, hK1⟩ := hK1exists
  have hK1A1 : K1.card ≤ A1.card := hcov H1 K1 (fun _ _ huv => huv.2) hK1

  have hEs2 (e : Sym2 (Fin n)) (he : e ∈ Es2) :
      ∃ k ∈ A2, ∃ u v : Fin n, G.Adj u v ∧ e = s(u, v) ∧ wire C (pair u v) (n + k) = true := by
    obtain ⟨heG, he1⟩ := Finset.mem_sdiff.1 he
    induction e using Sym2.ind with
    | _ u v =>
      have huv : G.Adj u v := SimpleGraph.mem_edgeFinset.1 heG
      rcases hedge u v huv with h1 | ⟨k, hk, htrue⟩
      · exact (he1 (Finset.mem_filter.2 ⟨heG, h1⟩)).elim
      · exact ⟨k, hk, u, v, huv, rfl, htrue⟩
  let gateOf : Sym2 (Fin n) → ℕ := fun e =>
    if h : ∃ k ∈ A2, ∃ u v : Fin n, G.Adj u v ∧ e = s(u, v) ∧ wire C (pair u v) (n + k) = true
    then Classical.choose h else 0
  have hEs2_card : Es2.card ≤ A2.card := by
    refine Finset.card_le_card_of_injOn gateOf (fun e he => ?_) (fun e1 he1 e2 he2 hgeq => ?_)
    · have h := hEs2 e he
      have hspec := Classical.choose_spec h
      simp only [gateOf, h, ↓reduceDIte]
      exact hspec.1
    · have h1 := hEs2 e1 he1
      have h2 := hEs2 e2 he2
      simp only [gateOf, h1, h2, ↓reduceDIte] at hgeq
      obtain ⟨hk1, u1, v1, huv1, rfl, ht1⟩ := Classical.choose_spec h1
      obtain ⟨hk2, u2, v2, huv2, rfl, ht2⟩ := Classical.choose_spec h2
      rw [← hgeq] at ht2
      let k := Classical.choose h1
      have hkA : k ∈ A := (Finset.mem_filter.1 hk1).1
      have hkns : ¬ Sound k := (Finset.mem_filter.1 hk1).2
      have hkl : k < L := hRlt k (hA k hkA).1
      have hkop : (g k).op = GateOp.and := (hA k hkA).2.1
      have hsg := hSingle k hkl hkop hkns u1 v1 u2 v2 huv1 huv2 ht1 ht2
      rcases hsg with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · rfl
      · exact Sym2.eq_swap
  let K2 : Finset (Fin n) :=
    Es2.attach.image (fun ⟨e, _⟩ =>
      let S := Finset.univ.filter (fun u : Fin n => u ∈ e)
      have hne : S.Nonempty := by
        induction e using Sym2.ind with
        | _ u v => exact ⟨u, Finset.mem_filter.2 ⟨Finset.mem_univ u, Sym2.mem_mk_left u v⟩⟩
      S.min' hne)
  have hK2_card : K2.card ≤ Es2.card :=
    Finset.card_image_le.trans (by rw [Finset.card_attach])
  have hK2_cov (u v : Fin n) (he : s(u, v) ∈ Es2) : u ∈ K2 ∨ v ∈ K2 := by
    let S := Finset.univ.filter (fun w : Fin n => w ∈ s(u, v))
    have hne : S.Nonempty := ⟨u, Finset.mem_filter.2 ⟨Finset.mem_univ u, Sym2.mem_mk_left u v⟩⟩
    let w := S.min' hne
    have hwK2 : w ∈ K2 := Finset.mem_image.2 ⟨⟨s(u, v), he⟩, Finset.mem_attach _ _, rfl⟩
    have hwS : w ∈ S := Finset.min'_mem S hne
    have hwe : w ∈ s(u, v) := (Finset.mem_filter.1 hwS).2
    rcases Sym2.mem_iff.1 hwe with h | h
    · exact Or.inl (h ▸ hwK2)
    · exact Or.inr (h ▸ hwK2)

  let K := K1 ∪ K2
  have hK_cov (u v : Fin n) (huv : G.Adj u v) : u ∈ K ∨ v ∈ K := by
    by_cases he1 : s(u, v) ∈ Es1
    · rcases hK1.1 ⟨huv, he1⟩ with hu | hv
      · exact Or.inl (Finset.mem_union_left _ hu)
      · exact Or.inr (Finset.mem_union_left _ hv)
    · have he2 : s(u, v) ∈ Es2 := Finset.mem_sdiff.2 ⟨SimpleGraph.mem_edgeFinset.2 huv, he1⟩
      rcases hK2_cov u v he2 with hu | hv
      · exact Or.inl (Finset.mem_union_right _ hu)
      · exact Or.inr (Finset.mem_union_right _ hv)
  have hE_split : G.edgeFinset.card ≤ Es1.card + Es2.card := by
    have hsub : G.edgeFinset ⊆ Es1 ∪ Es2 := by
      intro e he
      by_cases h1 : e ∈ Es1
      · exact Finset.mem_union_left _ h1
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.2 ⟨he, h1⟩)
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hK_card : K.card ≤ K1.card + K2.card := Finset.card_union_le K1 K2

  have hZM : Z ⊆ M := by
    intro k hk
    obtain ⟨_, hop, ⟨w, hw, _, _, _, ⟨u, hu⟩, _⟩, _⟩ := hZ k hk
    have hkl : k < L := by
      by_contra! h
      simp [hclean_past k (by omega)] at hw
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hkl, hop, u, (hfOr k hop u).2 ⟨w, hw, hu⟩⟩
  let M' := M.filter fun k => (child k).Nonempty
  have hZM' : Disjoint Z M' := by
    rw [Finset.disjoint_left]
    intro k hk hkm
    obtain ⟨_, _, hn, _⟩ := hZ k hk
    obtain ⟨w, hw, z, hz, hwz, hfw, hfz⟩ := hn
    obtain ⟨j, hj⟩ := (Finset.mem_filter.1 hkm).2
    obtain ⟨hin, h0⟩ := (hc_mem k j).1 hj
    rcases other_of_two (hlen k) hw hz hwz _ hin with h | h
    · exact (Finset.nonempty_iff_ne_empty.1 hfw) (h ▸ h0)
    · exact (Finset.nonempty_iff_ne_empty.1 hfz) (h ▸ h0)
  have hAcount' : A.card ≤ I.card + M'.card + 1 := by
    have hM' : M.biUnion child = M'.biUnion child := by
      ext j
      simp only [Finset.mem_biUnion, M', Finset.mem_filter]
      exact ⟨fun ⟨k, hk, hj⟩ => ⟨k, ⟨hk, j, hj⟩, hj⟩, fun ⟨k, hk, hj⟩ => ⟨k, hk.1, hj⟩⟩
    have h1 : A.card ≤ I.card + roots.card :=
      reachable_budget N roots R child S hc_card (fun _ => Finset.mem_filter)
    have h2 := Finset.card_insert_le (C.output - n) (M'.biUnion child)
    have h3 : (M'.biUnion child).card ≤ M'.card * 1 :=
      Finset.card_biUnion_le_card_mul _ _ _ (fun k hk => hc_mix k (Finset.mem_filter.1 hk).1)
    simp only [roots, hM'] at h1
    omega
  have hsplit : A.card + I.card = R.card := Finset.card_filter_add_card_filter_not S
  have hdisj : Disjoint R (Z ∪ M') := by
    rw [Finset.disjoint_left]
    intro k hk hmem
    have hkm : k ∈ M := (Finset.mem_union.1 hmem).elim (hZM ·) (fun h => (Finset.mem_filter.1 h).1)
    exact (Finset.nonempty_iff_ne_empty.1 (Finset.mem_filter.1 hkm).2.2)
      ((hN k).1 (Finset.mem_filter.1 hk).1).2
  have hun : R ∪ (Z ∪ M') ⊆ Finset.range L := by
    intro k hk
    rcases Finset.mem_union.1 hk with hr | hz
    · exact Finset.mem_range.2 (hRlt k hr)
    · exact (Finset.mem_filter.1 ((Finset.mem_union.1 hz).elim
        (hZM ·) (fun h => (Finset.mem_filter.1 h).1) : k ∈ M)).1
  have ht := Finset.card_le_card hun
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_union_of_disjoint hZM', Finset.card_range] at ht
  exact ⟨K, hK_cov, by omega⟩

end PEqualNP.Outside.L_meta_2590_aux.GraphBound


namespace PEqualNP.Outside.L_meta_2590_aux

def edges : List (ℕ × ℕ) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
    (5,7),(7,9),(9,6),(6,8),(8,5)]

abbrev graph : SimpleGraph (Fin 10) := PEqualNP.EdgeOwnership.edgeGraph 10 edges

lemma no_four : ∀ a b c d : Fin 10, a ≠ c → b ≠ d →
    ¬ (graph.Adj a b ∧ graph.Adj b c ∧ graph.Adj c d ∧ graph.Adj d a) := by
  decide +kernel

lemma edge_count : graph.edgeFinset.card = 15 := by
  decide +kernel

lemma cover_bound : ∀ K : Finset (Fin 10),
    (∀ a b, graph.Adj a b → a ∈ K ∨ b ∈ K) → 6 ≤ K.card := by
  decide +kernel

def edgeFn (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

lemma computes_graph : ∀ x : Fin 10 → Bool,
    edgeFn x = true ↔ ∃ a b, graph.Adj a b ∧ x a = true ∧ x b = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_2590_aux

namespace PEqualNP.Outside.L_meta_2590_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover

def GoodAnd (C : Circuit) (k : ℕ) : Prop :=
  (∀ x : Fin 10 → Bool,
    GraphBound.wire C x (10 + k) = true → ∃ u v, graph.Adj u v ∧ x u = true ∧ x v = true) ∨
  (∀ u v u' v' : Fin 10, graph.Adj u v → graph.Adj u' v' →
    GraphBound.wire C (GraphBound.pair u v) (10 + k) = true →
    GraphBound.wire C (GraphBound.pair u' v') (10 + k) = true →
    (u = u' ∧ v = v') ∨ (u = v' ∧ v = u'))

lemma lower_of_cases (C : Circuit) (hmono : Monotone2 C)
    (hcomp : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edgeFn x)
    (hcases : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → GoodAnd C k) :
    20 ≤ C.size := by
  have hao : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 :=
    fun g hg => hmono g hg
  have heval : ∀ x : Fin 10 → Bool, GraphBound.wire C x C.output = true ↔
      ∃ u v, graph.Adj u v ∧ x u = true ∧ x v = true := by
    intro x
    change C.eval (List.ofFn x) = true ↔ _
    rw [hcomp]
    exact computes_graph x
  obtain ⟨K, hcover, hsize⟩ := GraphBound.graph_bound graph no_four C hao heval hcases
  have hk := cover_bound K hcover
  rw [edge_count] at hsize
  change 20 ≤ C.gates.length
  omega

lemma bad_gate_of_small (C : Circuit) (hmono : Monotone2 C)
    (hcomp : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edgeFn x)
    (hsize : C.size ≤ 19) :
    ∃ k < C.gates.length, (gateAt C k).op = GateOp.and ∧ ¬ GoodAnd C k := by
  by_contra! h
  have hbound := lower_of_cases C hmono hcomp h
  omega

end PEqualNP.Outside.L_meta_2590_aux
