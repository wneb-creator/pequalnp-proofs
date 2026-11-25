import Mathlib
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_4675.MaskingNext

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.TwoColour

lemma no_twoColour_of_count_zero (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hz : tCount n C s = 0) (g : ℕ) : ¬ IsTwoColour n C s g := by
  intro hg
  have he : twoColour n C s = ∅ := Finset.card_eq_zero.mp hz
  have hm : g ∈ twoColour n C s :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.1, hg⟩
  rw [he] at hm
  simpa using hm

lemma orIn_same_colour (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hz : tCount n C s = 0) (g : ℕ) (hg : g < C.gates.length)
    (hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = GateOp.or)
    (i j : Fin n) (hi : i ∈ orIn n C (n + g)) (hj : j ∈ orIn n C (n + g)) :
    s i = s j := by
  cases hci : s i <;> cases hcj : s j
  · rfl
  · exact False.elim (no_twoColour_of_count_zero n C s hz g
      ⟨hg, hop, ⟨i, hi, hci⟩, ⟨j, hj, hcj⟩⟩)
  · exact False.elim (no_twoColour_of_count_zero n C s hz g
      ⟨hg, hop, ⟨j, hj, hcj⟩, ⟨i, hi, hci⟩⟩)
  · rfl

lemma orIn_one_colour (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hz : tCount n C s = 0) (g : ℕ) (hg : g < C.gates.length)
    (hop : (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = GateOp.or) :
    (∀ i ∈ orIn n C (n + g), s i = false) ∨
      (∀ i ∈ orIn n C (n + g), s i = true) := by
  by_cases h : ∃ i ∈ orIn n C (n + g), s i = true
  · obtain ⟨i, hi, hci⟩ := h
    right
    intro j hj
    exact (orIn_same_colour n C s hz g hg hop j i hj hi).trans hci
  · left
    intro i hi
    cases hci : s i
    · rfl
    · exact False.elim (h ⟨i, hi, hci⟩)


open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.CleanedNonEdge

def wireStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma foldl_wireStep_length (gs : List Gate) (acc : List Bool) :
    (gs.foldl wireStep acc).length = acc.length + gs.length := by
  induction gs generalizing acc with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons, ih, wireStep, List.length_append, List.length_cons, List.length_nil]
    omega

lemma foldl_wireStep_prefix (gs : List Gate) (acc : List Bool) (w : ℕ) (hw : w < acc.length) :
    (gs.foldl wireStep acc).getD w false = acc.getD w false := by
  induction gs generalizing acc with
  | nil => rfl
  | cons g gs ih =>
    have hw' : w < (wireStep acc g).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [List.foldl_cons, ih (wireStep acc g) hw']
    rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_left hw]

lemma gateAt_eq_getElem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) :
    gateAt C k = C.gates[k] := by
  unfold gateAt
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk]
  rfl

lemma wireValue_input (n : ℕ) (C : Circuit) (x : Fin n → Bool) (w : ℕ) (hw : w < n) :
    PEqualNP.BlindGate.wireValue C n x w = x ⟨w, hw⟩ := by
  unfold PEqualNP.BlindGate.wireValue Circuit.wires
  have hw' : w < (List.ofFn x).length := by simp [hw]
  have h1 := foldl_wireStep_prefix C.gates (List.ofFn x) w hw'
  change (C.gates.foldl wireStep (List.ofFn x)).getD w false = x ⟨w, hw⟩
  rw [h1, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hw']
  simp

lemma wireValue_gate (n : ℕ) (C : Circuit) (x : Fin n → Bool) (k : ℕ)
    (hk : k < C.gates.length) (hRB : ReadsBack n C) :
    PEqualNP.BlindGate.wireValue C n x (n + k) =
      (gateAt C k).op.eval ((gateAt C k).inputs.map fun u => PEqualNP.BlindGate.wireValue C n x u) := by
  have hsplit : C.gates = C.gates.take k ++ [C.gates[k]] ++ C.gates.drop (k + 1) := by
    have h1 := List.take_append_drop k C.gates
    have h2 : C.gates.drop k = C.gates[k] :: C.gates.drop (k + 1) := List.drop_eq_getElem_cons hk
    rw [h2] at h1
    simp only [List.append_assoc, List.singleton_append, h1]
  set acc := (C.gates.take k).foldl wireStep (List.ofFn x) with hacc
  have hacc_len : acc.length = n + k := by
    rw [hacc, foldl_wireStep_length, List.length_ofFn, List.length_take]
    omega
  have hpref : ∀ u < n + k, PEqualNP.BlindGate.wireValue C n x u = acc.getD u false := by
    intro u hu
    unfold PEqualNP.BlindGate.wireValue Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD u false = acc.getD u false
    conv_lhs => rw [← List.take_append_drop k C.gates]
    rw [List.foldl_append, ← hacc]
    exact foldl_wireStep_prefix (C.gates.drop k) acc u (by omega)
  have hval : PEqualNP.BlindGate.wireValue C n x (n + k) =
      C.gates[k].op.eval (C.gates[k].inputs.map fun u => acc.getD u false) := by
    unfold PEqualNP.BlindGate.wireValue Circuit.wires
    change (C.gates.foldl wireStep (List.ofFn x)).getD (n + k) false = _
    conv_lhs => rw [hsplit]
    rw [List.foldl_append, List.foldl_append, ← hacc, List.foldl_cons, List.foldl_nil]
    have hlen : n + k < (wireStep acc C.gates[k]).length := by
      simp only [wireStep, List.length_append, List.length_singleton]
      omega
    rw [foldl_wireStep_prefix (C.gates.drop (k + 1)) (wireStep acc C.gates[k]) (n + k) hlen]
    rw [List.getD_eq_getElem?_getD]
    simp only [wireStep, List.getElem?_append_right (by omega : acc.length ≤ n + k),
      hacc_len, Nat.sub_self, List.getElem?_cons_zero, Option.getD_some]
  rw [hval, gateAt_eq_getElem C k hk]
  congr 1
  apply List.map_congr_left
  intro u hu
  rw [← gateAt_eq_getElem C k hk] at hu
  exact (hpref u (hRB k hk u hu)).symm

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.CleanedNonEdge.orStep]
    omega

lemma orSets_length (n : ℕ) (C : Circuit) :
    (PEqualNP.CleanedNonEdge.orSets n C).length = C.gates.length := by
  unfold PEqualNP.CleanedNonEdge.orSets
  rw [orSets_len]; simp

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.CleanedNonEdge.orStep n (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) []) := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (PEqualNP.CleanedNonEdge.orStep n
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD (w - n) []) := by
  have h := orSets_char n C.gates x k
  unfold PEqualNP.CleanedNonEdge.orSets gateAt
  rw [h]
  constructor
  · rintro ⟨_, h3⟩; exact h3
  · intro h3; exact ⟨hk, h3⟩

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g ↔ k < C.gates.length ∧
      (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ PEqualNP.CleanedNonEdge.OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold PEqualNP.CleanedNonEdge.OrReaches PEqualNP.CleanedNonEdge.orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) j :=
  (orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩

lemma orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C i g) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) g :=
  (orReaches_iff n C j g).mpr ⟨hj, Or.inr ⟨hop, i, hi, hlt, h⟩⟩

lemma orIn_mem_filter {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

lemma mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  exact ⟨fun h => ((orIn_mem_filter _ _ _ _).1 h).2,
    fun h => (orIn_mem_filter _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

lemma orIn_self (n : ℕ) (C : Circuit) (i : Fin n) : i ∈ PEqualNP.TopForm.orIn n C i :=
  (mem_orIn n C i i).mpr (Or.inl rfl)

lemma orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ PEqualNP.TopForm.orIn n C i) : a ∈ PEqualNP.TopForm.orIn n C (n + j) := by
  rw [mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩

lemma orReaches_bound (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w g → n + g ≤ w ∧ w < n + C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp hr
    rcases h3 with h3 | ⟨_, i, _, hlt, hri⟩
    · omega
    · have := ih i hlt hri
      omega

lemma true_wire_source (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (x : Fin n → Bool) :
    ∀ w < n + C.gates.length, PEqualNP.BlindGate.wireValue C n x w = true →
      (∃ i ∈ orIn n C w, x i = true) ∨
      (∃ g < C.gates.length, OrReaches n C w g ∧
        (gateAt C g).op = GateOp.and ∧
        PEqualNP.BlindGate.wireValue C n x (n + g) = true) := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hw hv
    by_cases hwinput : w < n
    · left
      refine ⟨⟨w, hwinput⟩, orIn_self n C ⟨w, hwinput⟩, ?_⟩
      rwa [wireValue_input n C x w hwinput] at hv
    · obtain ⟨g, rfl⟩ : ∃ g, w = n + g := ⟨w - n, by omega⟩
      have hg : g < C.gates.length := by omega
      have hmem : gateAt C g ∈ C.gates := by
        rw [gateAt_eq_getElem C g hg]
        exact List.getElem_mem hg
      rcases hAO.1 (gateAt C g) hmem with hop | hop
      · exact Or.inr ⟨g, hg, orReaches_self n C g hg, hop, hv⟩
      · rw [wireValue_gate n C x g hg hAO.2.1, hop] at hv
        have hor : ∃ u ∈ (gateAt C g).inputs,
            PEqualNP.BlindGate.wireValue C n x u = true := by
          simpa [GateOp.eval] using hv
        obtain ⟨u, hu, hvu⟩ := hor
        have hul : u < n + g := hAO.2.1 g hg u hu
        rcases ih u hul (by omega) hvu with ⟨i, hi, hxi⟩ | ⟨k, hk, hr, hopk, hvk⟩
        · exact Or.inl ⟨i, orIn_up n C g u i hg hop hu hul hi, hxi⟩
        · exact Or.inr ⟨k, hk, orReaches_step n C g u k hg hop hu hul hr, hopk, hvk⟩

lemma singleton_true_source (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (w : ℕ) (hw : w < n + C.gates.length) (i : Fin n)
    (hv : PEqualNP.BlindGate.wireValue C n (fun j => decide (j = i)) w = true) :
    i ∈ orIn n C w ∨
      ∃ g < C.gates.length, OrReaches n C w g ∧
        (gateAt C g).op = GateOp.and ∧
        PEqualNP.BlindGate.wireValue C n (fun j => decide (j = i)) (n + g) = true := by
  rcases true_wire_source n C hAO (fun j => decide (j = i)) w hw hv with
    ⟨j, hj, hji⟩ | h
  · have he : j = i := of_decide_eq_true hji
    exact Or.inl (he ▸ hj)
  · exact Or.inr h

lemma mixed_singletons_have_and (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hAO : IsAO2 n C) (hz : tCount n C s = 0)
    (g : ℕ) (hg : g < C.gates.length) (hop : (gateAt C g).op = GateOp.or)
    (i j : Fin n) (hij : s i ≠ s j)
    (hi : PEqualNP.BlindGate.wireValue C n (fun k => decide (k = i)) (n + g) = true)
    (hj : PEqualNP.BlindGate.wireValue C n (fun k => decide (k = j)) (n + g) = true) :
    ∃ k < C.gates.length, OrReaches n C (n + g) k ∧
      (gateAt C k).op = GateOp.and ∧
      (PEqualNP.BlindGate.wireValue C n (fun a => decide (a = i)) (n + k) = true ∨
       PEqualNP.BlindGate.wireValue C n (fun a => decide (a = j)) (n + k) = true) := by
  rcases singleton_true_source n C hAO (n + g) (by omega) i hi with
    hi | ⟨k, hk, hr, hand, hv⟩
  · rcases singleton_true_source n C hAO (n + g) (by omega) j hj with
      hj | ⟨k, hk, hr, hand, hv⟩
    · exact False.elim (hij (orIn_same_colour n C s hz g hg hop i j hi hj))
    · exact ⟨k, hk, hr, hand, Or.inr hv⟩
  · exact ⟨k, hk, hr, hand, Or.inl hv⟩

lemma mixed_singletons_have_dirty_and (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hAO : IsAO2 n C) (hz : tCount n C s = 0)
    (hunit : ∀ i : Fin n, circuitFun n C (fun k => decide (k = i)) = false)
    (g : ℕ) (hg : g < C.gates.length) (hop : (gateAt C g).op = GateOp.or)
    (i j : Fin n) (hij : s i ≠ s j)
    (hi : PEqualNP.BlindGate.wireValue C n (fun k => decide (k = i)) (n + g) = true)
    (hj : PEqualNP.BlindGate.wireValue C n (fun k => decide (k = j)) (n + g) = true) :
    ∃ k < C.gates.length, OrReaches n C (n + g) k ∧
      (gateAt C k).op = GateOp.and ∧
      ¬ PEqualNP.CircuitMoves.WireBelowOutput n C (n + k) := by
  obtain ⟨k, hk, hr, hand, hv⟩ :=
    mixed_singletons_have_and n C s hAO hz g hg hop i j hij hi hj
  refine ⟨k, hk, hr, hand, ?_⟩
  intro hbelow
  rcases hv with hv | hv
  · have ht := hbelow (fun a => decide (a = i)) hv
    have hf := hunit i
    change C.eval (List.ofFn (fun a => decide (a = i))) = false at hf
    rw [hf] at ht
    cases ht
  · have ht := hbelow (fun a => decide (a = j)) hv
    have hf := hunit j
    change C.eval (List.ofFn (fun a => decide (a = j))) = false at hf
    rw [hf] at ht
    cases ht

lemma prior_or_singletons_same_colour (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hAO : IsAO2 n C) (hz : tCount n C s = 0)
    (hunit : ∀ i : Fin n, circuitFun n C (fun k => decide (k = i)) = false)
    (g : ℕ)
    (hclean : ∀ k < g, (gateAt C k).op = GateOp.and →
      PEqualNP.CircuitMoves.WireBelowOutput n C (n + k))
    (a : ℕ) (ha : a < C.gates.length) (hag : a < g)
    (hop : (gateAt C a).op = GateOp.or)
    (i j : Fin n)
    (hi : PEqualNP.BlindGate.wireValue C n (fun k => decide (k = i)) (n + a) = true)
    (hj : PEqualNP.BlindGate.wireValue C n (fun k => decide (k = j)) (n + a) = true) :
    s i = s j := by
  by_contra hij
  obtain ⟨k, hk, hr, hand, hdirty⟩ :=
    mixed_singletons_have_dirty_and n C s hAO hz hunit a ha hop i j hij hi hj
  have hka := (orReaches_bound n C k (n + a) hr).1
  exact hdirty (hclean k (by omega) hand)

lemma prior_wire_singletons_same_colour (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hAO : IsAO2 n C) (hz : tCount n C s = 0)
    (hunit : ∀ i : Fin n, circuitFun n C (fun k => decide (k = i)) = false)
    (g : ℕ) (hg : g ≤ C.gates.length)
    (hclean : ∀ k < g, (gateAt C k).op = GateOp.and →
      PEqualNP.CircuitMoves.WireBelowOutput n C (n + k))
    (w : ℕ) (hw : w < n + g) (i j : Fin n)
    (hi : PEqualNP.BlindGate.wireValue C n (fun k => decide (k = i)) w = true)
    (hj : PEqualNP.BlindGate.wireValue C n (fun k => decide (k = j)) w = true) :
    s i = s j := by
  by_cases hin : w < n
  · rw [wireValue_input n C _ w hin] at hi hj
    have hwi : (⟨w, hin⟩ : Fin n) = i := of_decide_eq_true hi
    have hwj : (⟨w, hin⟩ : Fin n) = j := of_decide_eq_true hj
    rw [← hwi, ← hwj]
  · obtain ⟨a, rfl⟩ : ∃ a, w = n + a := ⟨w - n, by omega⟩
    have ha : a < C.gates.length := by omega
    have hag : a < g := by omega
    have hm : gateAt C a ∈ C.gates := by
      rw [gateAt_eq_getElem C a ha]
      exact List.getElem_mem ha
    rcases hAO.1 (gateAt C a) hm with hop | hop
    · have hbelow := hclean a hag hop
      have ht := hbelow (fun k => decide (k = i)) hi
      have hf := hunit i
      change C.eval (List.ofFn (fun k => decide (k = i))) = false at hf
      rw [hf] at ht
      cases ht
    · exact prior_or_singletons_same_colour n C s hAO hz hunit g hclean a ha hag hop i j hi hj

lemma orReaches_true (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (x : Fin n → Bool)
    (k : ℕ) (hv : PEqualNP.BlindGate.wireValue C n x (n + k) = true) :
    ∀ w, OrReaches n C w k → PEqualNP.BlindGate.wireValue C n x w = true := by
  intro w
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    intro hr
    have hn : n ≤ w := hr.1
    obtain ⟨a, rfl⟩ : ∃ a, w = n + a := ⟨w - n, by omega⟩
    obtain ⟨ha, he | ⟨hop, u, hu, hul, hur⟩⟩ := (orReaches_iff n C a k).mp hr
    · rw [← he]
      exact hv
    · rw [wireValue_gate n C x a ha hAO.2.1, hop]
      have hval := ih u hul hur
      simpa [GateOp.eval] using (show ∃ v ∈ (gateAt C a).inputs,
        PEqualNP.BlindGate.wireValue C n x v = true from ⟨u, hu, hval⟩)

lemma orIn_true (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (x : Fin n → Bool)
    (w : ℕ) (i : Fin n) (hi : i ∈ orIn n C w) (hx : x i = true) :
    PEqualNP.BlindGate.wireValue C n x w = true := by
  rw [mem_orIn] at hi
  have hxi : PEqualNP.BlindGate.wireValue C n x i = true :=
    (wireValue_input n C x i i.isLt).trans hx
  rcases hi with he | ⟨a, ha, hr, hop, hin⟩
  · rw [← he]
    exact hxi
  · apply orReaches_true n C hAO x a _ w hr
    rw [wireValue_gate n C x a ha hAO.2.1, hop]
    simpa [GateOp.eval] using (show ∃ v ∈ (gateAt C a).inputs,
      PEqualNP.BlindGate.wireValue C n x v = true from ⟨i, hin, hxi⟩)

lemma prior_wire_on_rejected_input (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (g : ℕ) (hg : g ≤ C.gates.length)
    (hclean : ∀ k < g, (gateAt C k).op = GateOp.and →
      PEqualNP.CircuitMoves.WireBelowOutput n C (n + k))
    (w : ℕ) (hw : w < n + g) (x : Fin n → Bool)
    (hx : circuitFun n C x = false) :
    PEqualNP.BlindGate.wireValue C n x w = true ↔ ∃ i ∈ orIn n C w, x i = true := by
  constructor
  · intro hv
    rcases true_wire_source n C hAO x w (by omega) hv with h | ⟨k, hk, hr, hand, hval⟩
    · exact h
    · have hkw := (orReaches_bound n C k w hr).1
      have hbelow := hclean k (by omega) hand
      have ht := hbelow x hval
      change C.eval (List.ofFn x) = false at hx
      rw [hx] at ht
      cases ht
  · rintro ⟨i, hi, hxi⟩
    exact orIn_true n C hAO x w i hi hxi


end PEqualNP.Outside.L_meta_4675.MaskingNext



namespace PEqualNP.Outside.L_meta_4675.OneJunk

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm
  PEqualNP.Outside.L_meta_4675.MaskingNext

lemma foldl_append_spec {α β : Type} (f : List α → β → α) :
    ∀ (l : List β) (acc : List α),
      (l.foldl (fun w b => w ++ [f w b]) acc).length = acc.length + l.length ∧
      (∀ i < acc.length, (l.foldl (fun w b => w ++ [f w b]) acc)[i]? = acc[i]?) ∧
      (∀ (j : ℕ) (b : β), l[j]? = some b →
        (l.foldl (fun w b => w ++ [f w b]) acc)[acc.length + j]? =
          some (f ((l.take j).foldl (fun w x => w ++ [f w x]) acc) b)) := by
  intro l
  induction l with
  | nil =>
    intro acc
    refine ⟨by simp, fun i _ => rfl, fun j b h => by simp at h⟩
  | cons a t ih =>
    intro acc
    have h1 := ih (acc ++ [f acc a])
    refine ⟨?_, ?_, ?_⟩
    · rw [List.foldl_cons, h1.1, List.length_append, List.length_singleton, List.length_cons]
      omega
    · intro i hi
      simp only [List.foldl_cons]
      have hi' : i < (acc ++ [f acc a]).length := by simp; omega
      rw [h1.2.1 i hi', List.getElem?_append_left hi]
    · intro j b hj
      cases j with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at hj
        subst hj
        simp only [List.foldl_cons, Nat.add_zero, List.take_zero, List.foldl_nil]
        have hi' : acc.length < (acc ++ [f acc a]).length := by simp
        rw [h1.2.1 acc.length hi', List.getElem?_append_right (le_refl _)]
        simp
      | succ j' =>
        simp only [List.getElem?_cons_succ] at hj
        simp only [List.foldl_cons, List.take_succ_cons]
        have hstep := h1.2.2 j' b hj
        simp only [List.length_append, List.length_singleton] at hstep
        have heq : acc.length + (j' + 1) = acc.length + 1 + j' := by omega
        rw [heq]
        exact hstep

lemma foldl_append_take_getD {α β : Type} (f : List α → β → α) (d : α)
    (l : List β) (acc : List α) (k i : ℕ) (hi : i < acc.length + k) (hk : k ≤ l.length) :
    ((l.take k).foldl (fun w x => w ++ [f w x]) acc).getD i d =
      (l.foldl (fun w x => w ++ [f w x]) acc).getD i d := by
  have hsplit : l = l.take k ++ l.drop k := (List.take_append_drop k l).symm
  conv_rhs => rw [hsplit, List.foldl_append]
  have hlen : ((l.take k).foldl (fun w x => w ++ [f w x]) acc).length = acc.length + k := by
    rw [(foldl_append_spec f (l.take k) acc).1, List.length_take, Nat.min_eq_left hk]
  have hget := (foldl_append_spec f (l.drop k) ((l.take k).foldl (fun w x => w ++ [f w x]) acc)).2.1 i (by omega)
  simp only [List.getD_eq_getElem?_getD, hget]


lemma cones_length (n : ℕ) (C : Circuit) : (cones n C).length = C.gates.length := by
  unfold cones
  have h := (foldl_append_spec (fun cs g =>
    (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => (w - n) :: cs.getD (w - n) [])) C.gates []).1
  change (C.gates.foldl (fun cs g => cs ++ [((g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => (w - n) :: cs.getD (w - n) []))]) []).length = C.gates.length
  rw [h]
  simp

lemma cones_getD_eq (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    (cones n C).getD j [] =
      ((gateAt C j).inputs.filter (fun w => decide (n ≤ w ∧ w < n + j))).flatMap
        (fun w => (w - n) :: (cones n C).getD (w - n) []) := by
  have hgetg : C.gates[j]? = some (gateAt C j) := by
    simp only [gateAt, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
  let f : List (List ℕ) → Gate → List ℕ := fun cs g =>
    (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => (w - n) :: cs.getD (w - n) [])
  have hstep := (foldl_append_spec f C.gates []).2.2 j (gateAt C j) hgetg
  have hlen : ((C.gates.take j).foldl (fun w x => w ++ [f w x]) []).length = j := by
    rw [(foldl_append_spec f (C.gates.take j) []).1, List.length_nil, Nat.zero_add,
      List.length_take, Nat.min_eq_left (Nat.le_of_lt hj)]
  change (C.gates.foldl (fun w x => w ++ [f w x]) []).getD j [] = _
  simp only [List.length_nil, Nat.zero_add] at hstep
  rw [List.getD_eq_getElem?_getD, hstep, Option.getD_some]
  dsimp only [f]
  rw [hlen]
  apply List.flatMap_congr
  intro w hw
  simp only [List.mem_filter, decide_eq_true_eq] at hw
  congr 1
  exact foldl_append_take_getD f [] C.gates [] j (w - n) (by simp; omega) (Nat.le_of_lt hj)

lemma inCone_lt (n : ℕ) (C : Circuit) : ∀ j i, InCone n C i j → i < j := by
  intro j
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    intro i hij
    by_cases hj : j < C.gates.length
    · unfold InCone at hij
      rw [cones_getD_eq n C j hj, List.mem_flatMap] at hij
      obtain ⟨w, hw, hmem⟩ := hij
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      simp only [List.mem_cons] at hmem
      rcases hmem with rfl | hmem
      · omega
      · have hlt := ih (w - n) (by omega) i hmem
        omega
    · unfold InCone at hij
      have hlen : (cones n C).length = C.gates.length := cones_length n C
      have hnone : (cones n C)[j]? = none := List.getElem?_eq_none (by omega)
      simp [List.getD_eq_getElem?_getD, hnone] at hij

lemma inCone_of_input (n : ℕ) (C : Circuit) (k j : ℕ) (hj : j < C.gates.length)
    (hk : k < j) (hmem : n + k ∈ (gateAt C j).inputs) : InCone n C k j := by
  unfold InCone
  rw [cones_getD_eq n C j hj, List.mem_flatMap]
  refine ⟨n + k, ?_, ?_⟩
  · simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hmem, by omega, by omega⟩
  · simp

lemma inCone_trans_of_input (n : ℕ) (C : Circuit) (i k j : ℕ) (hj : j < C.gates.length)
    (hk : k < j) (hmem : n + k ∈ (gateAt C j).inputs) (hik : InCone n C i k) : InCone n C i j := by
  unfold InCone at hik ⊢
  rw [cones_getD_eq n C j hj, List.mem_flatMap]
  refine ⟨n + k, ?_, ?_⟩
  · simp only [List.mem_filter, decide_eq_true_eq]; exact ⟨hmem, by omega, by omega⟩
  · simp only [List.mem_cons, Nat.add_sub_cancel_left]; exact Or.inr hik

lemma operands (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length) :
    (gateAt C j).inputs = [opnd C j 0, opnd C j 1] ∧
      ∀ b : Fin 2, opnd C j b ∈ (gateAt C j).inputs ∧ opnd C j b < n + j := by
  have hm : gateAt C j ∈ C.gates := by
    rw [gateAt_eq_getElem C j hj]
    exact List.getElem_mem hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hAO.2.2 _ hm)
  have h0 : opnd C j 0 = a := by simp [opnd, hab]
  have h1 : opnd C j 1 = b := by simp [opnd, hab]
  refine ⟨by rw [h0, h1]; exact hab, ?_⟩
  intro c
  have hmem : opnd C j c ∈ (gateAt C j).inputs := by fin_cases c <;> simp [h0, h1, hab]
  exact ⟨hmem, hAO.2.1 j hj _ hmem⟩

lemma reach_inCone_or_eq (n : ℕ) (C : Circuit) :
    ∀ k g, OrReaches n C (n + k) g → g = k ∨ InCone n C g k := by
  intro k
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    intro g hg
    obtain ⟨hk, he | ⟨_, u, hu, hul, hur⟩⟩ := (orReaches_iff n C k g).mp hg
    · exact Or.inl he
    · have hn : n ≤ u := hur.1
      have hue : u = n + (u - n) := by omega
      have hrec := ih (u - n) (by omega) g (by rwa [← hue])
      rcases hrec with rfl | hc
      · exact Or.inr (inCone_of_input n C (u - n) k hk (by omega) (by rwa [← hue]))
      · exact Or.inr (inCone_trans_of_input n C g (u - n) k hk (by omega) (by rwa [← hue]) hc)

lemma operand_reach_inCone (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (b : Fin 2) (k : ℕ) (hr : OrReaches n C (opnd C j b) k) :
    InCone n C k j := by
  obtain ⟨hm, hlt⟩ := (operands n C hAO j hj).2 b
  have hn : n ≤ opnd C j b := hr.1
  have he : opnd C j b = n + (opnd C j b - n) := by omega
  have hr' : OrReaches n C (n + (opnd C j b - n)) k := by rwa [← he]
  rcases reach_inCone_or_eq n C _ k hr' with rfl | hc
  · exact inCone_of_input n C _ j hj (by omega) (by rwa [← he])
  · exact inCone_trans_of_input n C k _ j hj (by omega) (by rwa [← he]) hc

lemma operand_and_is_junk (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C) (q : ℕ)
    (honly : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ BelowF G C k → k = q)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (b : Fin 2) (k : ℕ) (hk : k < C.gates.length) (hkand : (gateAt C k).op = GateOp.and)
    (hr : OrReaches n C (opnd C j b) k) : k = q := by
  apply honly k hk hkand
  intro hb
  exact hTop k hk j hj hkand hb hand (operand_reach_inCone n C hAO j hj b k hr)

lemma operand_semantics (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C) (q : ℕ)
    (honly : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ BelowF G C k → k = q)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (b : Fin 2) (x : Fin n → Bool) :
    PEqualNP.BlindGate.wireValue C n x (opnd C j b) = true ↔
      (∃ i ∈ side (n := n) C j b, x i = true) ∨
      OrReaches n C (opnd C j b) q ∧ gateVal n C q x = true := by
  constructor
  · intro hv
    have hw := ((operands n C hAO j hj).2 b).2
    rcases true_wire_source n C hAO x _ (by omega) hv with hi | ⟨k, hk, hr, hkand, hkv⟩
    · exact Or.inl hi
    · have he := operand_and_is_junk n G C hAO hTop q honly j hj hand b k hk hkand hr
      subst k
      exact Or.inr ⟨hr, hkv⟩
  · rintro (⟨i, hi, hxi⟩ | ⟨hr, hqv⟩)
    · exact orIn_true n C hAO x _ i hi hxi
    · exact orReaches_true n C hAO x q hqv _ hr

lemma junk_operand_pure (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C) (q : ℕ)
    (hq : q < C.gates.length) (hand : (gateAt C q).op = GateOp.and)
    (honly : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ BelowF G C k → k = q)
    (b : Fin 2) (x : Fin n → Bool) :
    PEqualNP.BlindGate.wireValue C n x (opnd C q b) = true ↔
      ∃ i ∈ side (n := n) C q b, x i = true := by
  rw [operand_semantics n G C hAO hTop q honly q hq hand b x]
  have hnot : ¬ OrReaches n C (opnd C q b) q := by
    intro hr
    have hb := orReaches_bound n C q _ hr
    have hw := ((operands n C hAO q hq).2 b).2
    omega
  simp [hnot]

lemma and_value (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and) (x : Fin n → Bool) :
    gateVal n C j x = true ↔
      PEqualNP.BlindGate.wireValue C n x (opnd C j 0) = true ∧
      PEqualNP.BlindGate.wireValue C n x (opnd C j 1) = true := by
  change PEqualNP.BlindGate.wireValue C n x (n + j) = true ↔ _
  rw [wireValue_gate n C x j hj hAO.2.1, hand, (operands n C hAO j hj).1]
  simp [GateOp.eval]

lemma junk_semantics (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C) (q : ℕ)
    (hq : q < C.gates.length) (hand : (gateAt C q).op = GateOp.and)
    (honly : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ BelowF G C k → k = q)
    (x : Fin n → Bool) : gateVal n C q x = true ↔
      (∃ i ∈ side (n := n) C q 0, x i = true) ∧
      (∃ i ∈ side (n := n) C q 1, x i = true) := by
  rw [and_value n C hAO q hq hand x,
    junk_operand_pure n G C hAO hTop q hq hand honly 0 x,
    junk_operand_pure n G C hAO hTop q hq hand honly 1 x]

lemma productive_reader_not_both (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (q : ℕ) (hdirty : ¬ BelowF G C q)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hbelow : BelowF G C j) :
    ¬ (OrReaches n C (opnd C j 0) q ∧ OrReaches n C (opnd C j 1) q) := by
  intro hr
  apply hdirty
  intro x hv
  apply hbelow x
  rw [and_value n C hAO j hj hand x]
  exact ⟨orReaches_true n C hAO x q hv _ hr.1, orReaches_true n C hAO x q hv _ hr.2⟩

lemma productive_reader_semantics (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C) (q : ℕ)
    (hq : q < C.gates.length) (hqand : (gateAt C q).op = GateOp.and)
    (hdirty : ¬ BelowF G C q)
    (honly : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ BelowF G C k → k = q)
    (j : ℕ) (hj : j < C.gates.length) (hand : (gateAt C j).op = GateOp.and)
    (hbelow : BelowF G C j) (b : Fin 2) (hr : OrReaches n C (opnd C j b) q)
    (x : Fin n → Bool) : gateVal n C j x = true ↔
      ((∃ i ∈ side (n := n) C q 0, x i = true) ∧
        (∃ i ∈ side (n := n) C q 1, x i = true) ∨
        (∃ i ∈ side (n := n) C j b, x i = true)) ∧
      (∃ i ∈ side (n := n) C j (1 - b), x i = true) := by
  have hnb := productive_reader_not_both n G C hAO q hdirty j hj hand hbelow
  have hsem := junk_semantics n G C hAO hTop q hq hqand honly x
  rw [and_value n C hAO j hj hand x,
    operand_semantics n G C hAO hTop q honly j hj hand 0 x,
    operand_semantics n G C hAO hTop q honly j hj hand 1 x]
  have hb : b = 0 ∨ b = 1 := by fin_cases b <;> simp
  rcases hb with rfl | rfl
  · have hn : ¬ OrReaches n C (opnd C j 1) q := fun h => hnb ⟨hr, h⟩
    simp only [hr, hn, true_and, false_and, or_false, hsem, sub_zero]
    constructor <;> rintro ⟨h0, h1⟩ <;> exact ⟨h0.symm, h1⟩
  · have hn : ¬ OrReaches n C (opnd C j 0) q := fun h => hnb ⟨h, hr⟩
    simp only [hr, hn, true_and, false_and, or_false, hsem, sub_self]
    constructor
    · rintro ⟨h0, h1⟩
      exact ⟨h1.symm, h0⟩
    · rintro ⟨h1, h0⟩
      exact ⟨h0, h1.symm⟩

lemma junk_sides_nonempty (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C) (q : ℕ)
    (hq : q < C.gates.length) (hqand : (gateAt C q).op = GateOp.and)
    (hdirty : ¬ BelowF G C q)
    (honly : ∀ k < C.gates.length, (gateAt C k).op = GateOp.and → ¬ BelowF G C k → k = q) :
    (side (n := n) C q 0).Nonempty ∧ (side (n := n) C q 1).Nonempty := by
  have hw : ∃ x : Fin n → Bool, gateVal n C q x = true := by
    by_contra h
    apply hdirty
    intro x hx
    exact False.elim (h ⟨x, hx⟩)
  obtain ⟨x, hx⟩ := hw
  obtain ⟨⟨a, ha, _⟩, ⟨b, hb, _⟩⟩ := (junk_semantics n G C hAO hTop q hq hqand honly x).mp hx
  exact ⟨⟨a, ha⟩, ⟨b, hb⟩⟩

end PEqualNP.Outside.L_meta_4675.OneJunk


namespace PEqualNP.Outside.L_meta_4675.OrReachAPI

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
  PEqualNP.MetaComplexity.NestedCover

lemma orSets_len (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [PEqualNP.CleanedNonEdge.orStep]
    omega

lemma orSets_length (n : ℕ) (C : Circuit) :
    (PEqualNP.CleanedNonEdge.orSets n C).length = C.gates.length := by
  unfold PEqualNP.CleanedNonEdge.orSets
  rw [orSets_len]; simp

lemma orSets_char (n : ℕ) (gs : List Gate) :
    ∀ i j, i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD j [] ↔
      j < gs.length ∧ (i = j ∨ ((gs.getD j ⟨GateOp.or, []⟩).op = GateOp.or ∧
        ∃ w ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, n ≤ w ∧ w < n + j ∧
          i ∈ (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) [])) := by
  induction gs using List.reverseRecOn with
  | nil => intro i j; simp
  | append_singleton gs g ih =>
    intro i j
    rw [List.foldl_append, List.foldl_cons, List.foldl_nil]
    have hlen : (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).length = gs.length := by
      rw [orSets_len]; simp
    have key : ∀ k, k < gs.length →
        (PEqualNP.CleanedNonEdge.orStep n (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD k [] =
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD k [] := by
      intro k hk
      simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left (by omega)]
    rcases Nat.lt_trichotomy j gs.length with h | h | h
    · have e1 : (gs ++ [g]).getD j ⟨GateOp.or, []⟩ = gs.getD j ⟨GateOp.or, []⟩ := by
        simp only [List.getD_eq_getElem?_getD]
        rw [List.getElem?_append_left h]
      rw [key j h, ih i j, e1]
      constructor
      · rintro ⟨_, h3⟩
        refine ⟨by simp; omega, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · refine Or.inr ⟨hop, w, hw, h1, h2, ?_⟩
          rw [key (w - n) (by omega)]
          exact h3
      · rintro ⟨_, h3⟩
        refine ⟨h, ?_⟩
        rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
        · exact Or.inl h3
        · rw [key (w - n) (by omega)] at h3
          exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩
    · subst h
      have e1 : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
        simp [List.getD_eq_getElem?_getD]
      rw [e1]
      by_cases hop : g.op = GateOp.or
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] =
            gs.length :: (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + gs.length))).flatMap
              (fun w => (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []).getD (w - n) []) := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_cons, List.mem_flatMap, List.mem_filter, decide_eq_true_eq]
        constructor
        · rintro (h3 | ⟨w, ⟨hw, h1, h2⟩, h3⟩)
          · exact ⟨by simp, Or.inl h3⟩
          · refine ⟨by simp, Or.inr ⟨hop, w, hw, h1, h2, ?_⟩⟩
            rw [key (w - n) (by omega)]
            exact h3
        · rintro ⟨_, h3 | ⟨_, w, hw, h1, h2, h3⟩⟩
          · exact Or.inl h3
          · rw [key (w - n) (by omega)] at h3
            exact Or.inr ⟨w, ⟨hw, h1, h2⟩, h3⟩
      · have e2 : (PEqualNP.CleanedNonEdge.orStep n
            (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD gs.length [] = [gs.length] := by
          simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
          rw [List.getElem?_append_right (by omega)]
          simp [hlen, hop]
        rw [e2]
        simp only [List.mem_singleton]
        constructor
        · intro h3
          exact ⟨by simp, Or.inl h3⟩
        · rintro ⟨_, h3 | ⟨hop2, _⟩⟩
          · exact h3
          · exact (hop hop2).elim
    · have e0 : (PEqualNP.CleanedNonEdge.orStep n
          (gs.foldl (PEqualNP.CleanedNonEdge.orStep n) []) g).getD j [] = [] := by
        simp only [PEqualNP.CleanedNonEdge.orStep, List.getD_eq_getElem?_getD]
        rw [List.getElem?_eq_none (by simp; omega)]
        rfl
      rw [e0]
      constructor
      · intro h0; simp at h0
      · rintro ⟨h0, _⟩
        simp at h0
        omega

lemma orSets_mem_iff (n : ℕ) (C : Circuit) (k x : ℕ) (hk : k < C.gates.length) :
    x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD k [] ↔ x = k ∨ ((gateAt C k).op = GateOp.or ∧
      ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
        x ∈ (PEqualNP.CleanedNonEdge.orSets n C).getD (w - n) []) := by
  have h := orSets_char n C.gates x k
  unfold PEqualNP.CleanedNonEdge.orSets gateAt
  rw [h]
  constructor
  · rintro ⟨_, h3⟩; exact h3
  · intro h3; exact ⟨hk, h3⟩

lemma orReaches_iff (n : ℕ) (C : Circuit) (k g : ℕ) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + k) g ↔ k < C.gates.length ∧
      (g = k ∨ ((gateAt C k).op = GateOp.or ∧
        ∃ i ∈ (gateAt C k).inputs, i < n + k ∧ PEqualNP.CleanedNonEdge.OrReaches n C i g)) := by
  have h := orSets_char n C.gates g k
  unfold PEqualNP.CleanedNonEdge.OrReaches PEqualNP.CleanedNonEdge.orSets gateAt
  have e : n + k - n = k := by omega
  rw [e, h]
  constructor
  · rintro ⟨_, hk, h3⟩
    refine ⟨hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h1, h2, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h2, h1, h3⟩
  · rintro ⟨hk, h3⟩
    refine ⟨by omega, hk, ?_⟩
    rcases h3 with h3 | ⟨hop, w, hw, h2, h1, h3⟩
    · exact Or.inl h3
    · exact Or.inr ⟨hop, w, hw, h1, h2, h3⟩

lemma orReaches_self (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) j :=
  (orReaches_iff n C j j).mpr ⟨hj, Or.inl rfl⟩

lemma orReaches_step (n : ℕ) (C : Circuit) (j i g : ℕ) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : PEqualNP.CleanedNonEdge.OrReaches n C i g) :
    PEqualNP.CleanedNonEdge.OrReaches n C (n + j) g :=
  (orReaches_iff n C j g).mpr ⟨hj, Or.inr ⟨hop, i, hi, hlt, h⟩⟩

lemma orIn_mem_filter {α : Type} (p : α → Prop) (d : DecidablePred p) (s : Finset α) (a : α) :
    a ∈ @Finset.filter α p d s ↔ a ∈ s ∧ p a :=
  @Finset.mem_filter α p d s a

lemma mem_orIn (n : ℕ) (C : Circuit) (w : ℕ) (i : Fin n) :
    i ∈ PEqualNP.TopForm.orIn n C w ↔ ((i : ℕ) = w ∨ ∃ k < C.gates.length,
      PEqualNP.CleanedNonEdge.OrReaches n C w k ∧ (gateAt C k).op = GateOp.or ∧
        (i : ℕ) ∈ (gateAt C k).inputs) := by
  unfold PEqualNP.TopForm.orIn
  exact ⟨fun h => ((orIn_mem_filter _ _ _ _).1 h).2,
    fun h => (orIn_mem_filter _ _ _ _).2 ⟨Finset.mem_univ _, h⟩⟩

lemma orIn_self (n : ℕ) (C : Circuit) (i : Fin n) : i ∈ PEqualNP.TopForm.orIn n C i :=
  (mem_orIn n C i i).mpr (Or.inl rfl)

lemma orIn_up (n : ℕ) (C : Circuit) (j i : ℕ) (a : Fin n) (hj : j < C.gates.length)
    (hop : (gateAt C j).op = GateOp.or) (hi : i ∈ (gateAt C j).inputs) (hlt : i < n + j)
    (h : a ∈ PEqualNP.TopForm.orIn n C i) : a ∈ PEqualNP.TopForm.orIn n C (n + j) := by
  rw [mem_orIn] at h ⊢
  right
  rcases h with h | ⟨k, hk, hr, hopk, hin⟩
  · exact ⟨j, hj, orReaches_self n C j hj, hop, by rw [h]; exact hi⟩
  · exact ⟨k, hk, orReaches_step n C j i k hj hop hi hlt hr, hopk, hin⟩

lemma orReaches_bound (n : ℕ) (C : Circuit) (g : ℕ) :
    ∀ w : ℕ, PEqualNP.CleanedNonEdge.OrReaches n C w g → n + g ≤ w ∧ w < n + C.gates.length := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hr
    have hnw : n ≤ w := hr.1
    obtain ⟨k, rfl⟩ : ∃ k, w = n + k := ⟨w - n, by omega⟩
    obtain ⟨hk, h3⟩ := (orReaches_iff n C k g).mp hr
    rcases h3 with h3 | ⟨_, i, _, hlt, hri⟩
    · omega
    · have := ih i hlt hri
      omega


lemma orIn_input (n : ℕ) (C : Circuit) (w : ℕ) (hw : w < n) :
    orIn n C w = {⟨w, hw⟩} := by
  ext i
  rw [mem_orIn, Finset.mem_singleton]
  constructor
  · rintro (hi | ⟨k, _, hr, _, _⟩)
    · exact Fin.ext hi
    · have := hr.1
      omega
  · intro hi
    exact Or.inl (congrArg Fin.val hi)

lemma orIn_non_or (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op ≠ GateOp.or) : orIn n C (n + k) = ∅ := by
  ext i
  simp only [Finset.notMem_empty, iff_false]
  intro hi
  rw [mem_orIn] at hi
  rcases hi with hi | ⟨j, _, hr, hjop, _⟩
  · have := i.isLt
    omega
  · obtain ⟨_, hr⟩ := (orReaches_iff n C k j).mp hr
    rcases hr with rfl | ⟨hkop, _⟩
    · exact hop hjop
    · exact hop hkop

lemma mem_orIn_or_iff (n : ℕ) (C : Circuit) (k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or)
    (hback : ∀ w ∈ (gateAt C k).inputs, w < n + k) (i : Fin n) :
    i ∈ orIn n C (n + k) ↔ ∃ w ∈ (gateAt C k).inputs, i ∈ orIn n C w := by
  constructor
  · intro hi
    rw [mem_orIn] at hi
    rcases hi with hi | ⟨j, hj, hr, hjop, hij⟩
    · have := i.isLt
      omega
    · obtain ⟨_, hr⟩ := (orReaches_iff n C k j).mp hr
      rcases hr with rfl | ⟨_, w, hw, _, hrw⟩
      · exact ⟨i.val, hij, orIn_self n C i⟩
      · exact ⟨w, hw, (mem_orIn n C w i).mpr (Or.inr ⟨j, hj, hrw, hjop, hij⟩)⟩
  · rintro ⟨w, hw, hi⟩
    exact orIn_up n C k w i hk hop hw (hback w hw) hi

lemma orIn_or_pair (n : ℕ) (C : Circuit) (k a b : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = GateOp.or) (hinputs : (gateAt C k).inputs = [a, b])
    (hback : ReadsBack n C) :
    orIn n C (n + k) = orIn n C a ∪ orIn n C b := by
  ext i
  rw [mem_orIn_or_iff n C k hk hop (hback k hk)]
  simp [hinputs]

lemma orSets_fold_prefix (n : ℕ) (hs : List Gate) (cs : List (List ℕ))
    (j : ℕ) (hj : j < cs.length) :
    (hs.foldl (orStep n) cs).getD j [] = cs.getD j [] := by
  induction hs generalizing cs with
  | nil => rfl
  | cons h hs ih =>
    rw [List.foldl_cons, ih]
    · simp only [orStep, List.getD_eq_getElem?_getD]
      rw [List.getElem?_append_left hj]
    · simp only [orStep, List.length_append, List.length_singleton]
      omega

lemma gateAt_append_old (gs hs : List Gate) (j : ℕ) (hj : j < gs.length) :
    gateAt (⟨gs ++ hs, 0⟩ : Circuit) j = gateAt ⟨gs, 0⟩ j := by
  simp only [gateAt, List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hj]

lemma orReaches_append_prefix (n : ℕ) (gs hs : List Gate) (w j : ℕ)
    (hw : w < n + gs.length) :
    OrReaches n (⟨gs ++ hs, 0⟩ : Circuit) w j ↔ OrReaches n ⟨gs, 0⟩ w j := by
  by_cases hn : n ≤ w
  · unfold OrReaches orSets
    rw [List.foldl_append, orSets_fold_prefix n hs _ (w - n)]
    rw [orSets_len]
    simp only [List.length_nil, zero_add]
    omega
  · simp only [OrReaches, hn, false_and]

lemma orIn_append_prefix (n : ℕ) (gs hs : List Gate) (w : ℕ) (hw : w < n + gs.length) :
    orIn n (⟨gs ++ hs, 0⟩ : Circuit) w = orIn n ⟨gs, 0⟩ w := by
  ext i
  rw [mem_orIn, mem_orIn]
  constructor
  · rintro (hi | ⟨j, hj, hr, hop, hin⟩)
    · exact Or.inl hi
    · have hr' := (orReaches_append_prefix n gs hs w j hw).mp hr
      have hj' : j < gs.length := by
        have hb := (orReaches_bound n (⟨gs, 0⟩ : Circuit) j w hr').1
        omega
      rw [gateAt_append_old gs hs j hj'] at hop hin
      exact Or.inr ⟨j, hj', hr', hop, hin⟩
  · rintro (hi | ⟨j, hj, hr, hop, hin⟩)
    · exact Or.inl hi
    · rw [← gateAt_append_old gs hs j hj] at hop hin
      exact Or.inr ⟨j, by
        change j < (gs ++ hs).length
        simp only [List.length_append]
        change j < gs.length at hj
        omega,
        (orReaches_append_prefix n gs hs w j hw).mpr hr, hop, hin⟩

end PEqualNP.Outside.L_meta_4675.OrReachAPI

namespace PEqualNP.Outside.L_meta_4675.Pruning

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.TwoColour

def step (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [g.op.eval (g.inputs.map fun i => ws.getD i false)]

def vals (gs : List Gate) (xs : List Bool) : List Bool := gs.foldl step xs

def optionalValue (ws : List Bool) (o : Option ℕ) : Bool :=
  o.elim false (fun i => ws.getD i false)

def pairOp (a : Bool) (x y : Bool) : Bool := if a then x && y else x || y

def pairGate (a : Bool) (i j : ℕ) : Gate :=
  ⟨if a then GateOp.and else GateOp.or, [i, j]⟩

def emitPair (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ) : List Gate × Option ℕ :=
  match x, y with
  | some i, some j => (gs ++ [pairGate a i j], some (n + gs.length))
  | some i, none => (gs, if a then none else some i)
  | none, some j => (gs, if a then none else some j)
  | none, none => (gs, none)

def isAnd : GateOp → Bool
  | GateOp.and => true
  | _ => false

def compileStep (n q : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) :
    List Gate × List (Option ℕ) :=
  if s.2.length = n + q then (s.1, s.2 ++ [none])
  else
    let r := emitPair n s.1 (isAnd g.op)
      (s.2.getD (g.inputs.getD 0 0) none) (s.2.getD (g.inputs.getD 1 0) none)
    (r.1, s.2 ++ [r.2])

def initial (n : ℕ) : List Gate × List (Option ℕ) := ([], (List.range n).map some)

def compiled (n q : ℕ) (gs : List Gate) : List Gate × List (Option ℕ) :=
  gs.foldl (compileStep n q) (initial n)

def forceStep (n q : ℕ) (ws : List Bool) (g : Gate) : List Bool :=
  ws ++ [if ws.length = n + q then false else g.op.eval (g.inputs.map fun i => ws.getD i false)]

def forcedValues (n q : ℕ) (C : Circuit) (xs : List Bool) : List Bool :=
  C.gates.foldl (forceStep n q) xs

def pruned (n q : ℕ) (C : Circuit) : Circuit :=
  let s := compiled n q C.gates
  ⟨s.1, (s.2.getD C.output none).getD (n + s.1.length)⟩

def Bounded (n : ℕ) (gs : List Gate) (o : Option ℕ) : Prop :=
  ∀ i, o = some i → i < n + gs.length

def Valid (n : ℕ) (s : List Gate × List (Option ℕ)) : Prop :=
  IsAO2 n ⟨s.1, 0⟩ ∧ ∀ o ∈ s.2, Bounded n s.1 o

def Related (xs old : List Bool) (s : List Gate × List (Option ℕ)) : Prop :=
  s.2.length = old.length ∧
    ∀ i, optionalValue (vals s.1 xs) (s.2.getD i none) = old.getD i false

lemma vals_length (gs : List Gate) (xs : List Bool) : (vals gs xs).length = xs.length + gs.length := by
  induction gs generalizing xs with
  | nil => simp [vals]
  | cons g gs ih =>
    simp only [vals, List.foldl_cons] at *
    rw [ih]
    simp [step]
    omega

lemma vals_append (gs hs : List Gate) (xs : List Bool) : vals (gs ++ hs) xs = vals hs (vals gs xs) := by
  simp [vals, List.foldl_append]

lemma vals_snoc (gs : List Gate) (g : Gate) (xs : List Bool) : vals (gs ++ [g]) xs = step (vals gs xs) g := by
  rw [vals_append]
  rfl

lemma getD_append_lt {α : Type*} (ws ys : List α) (i : ℕ) (d : α) (hi : i < ws.length) :
    (ws ++ ys).getD i d = ws.getD i d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left hi]

lemma getD_append_last {α : Type*} (ws : List α) (x d : α) :
    (ws ++ [x]).getD ws.length d = x := by simp [List.getD_eq_getElem?_getD]

lemma getD_ge {α : Type*} (ws : List α) (i : ℕ) (d : α) (hi : ws.length ≤ i) : ws.getD i d = d := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none hi]

lemma pairGate_eval (a x y : Bool) : (pairGate a 0 1).op.eval [x, y] = pairOp a x y := by
  cases a <;> cases x <;> cases y <;> rfl

lemma emitPair_length_le (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ) :
    (emitPair n gs a x y).1.length ≤ gs.length + 1 := by
  cases x <;> cases y <;> simp [emitPair]

lemma emitPair_prefix (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ)
    (xs : List Bool) (hx : xs.length = n) (i : ℕ) (hi : i < n + gs.length) :
    (vals (emitPair n gs a x y).1 xs).getD i false = (vals gs xs).getD i false := by
  cases x <;> cases y <;> simp only [emitPair]
  rw [vals_snoc]
  exact getD_append_lt _ _ _ _ (by rw [vals_length, hx]; exact hi)

lemma emitPair_optional_prefix (n : ℕ) (gs : List Gate) (a : Bool) (x y o : Option ℕ)
    (xs : List Bool) (hx : xs.length = n) (ho : Bounded n gs o) :
    optionalValue (vals (emitPair n gs a x y).1 xs) o = optionalValue (vals gs xs) o := by
  cases o with
  | none => rfl
  | some i => exact emitPair_prefix n gs a x y xs hx i (ho i rfl)

lemma emitPair_semantics (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ)
    (xs : List Bool) (hx : xs.length = n) :
    optionalValue (vals (emitPair n gs a x y).1 xs) (emitPair n gs a x y).2 =
      pairOp a (optionalValue (vals gs xs) x) (optionalValue (vals gs xs) y) := by
  cases x with
  | none => cases y <;> cases a <;> simp [emitPair, optionalValue, pairOp]
  | some i =>
    cases y with
    | none => cases a <;> simp [emitPair, optionalValue, pairOp]
    | some j =>
      simp only [emitPair, optionalValue, Option.elim_some, vals_snoc, step]
      have hl : (vals gs xs).length = n + gs.length := by rw [vals_length, hx]
      rw [← hl, getD_append_last]
      cases a <;> simp [pairGate, pairOp, GateOp.eval]

lemma emitPair_bounded (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ)
    (hx : Bounded n gs x) (hy : Bounded n gs y) :
    Bounded n (emitPair n gs a x y).1 (emitPair n gs a x y).2 := by
  cases x <;> cases y <;> cases a <;> simp_all [emitPair, Bounded]

lemma bounded_getD (n : ℕ) (s : List Gate × List (Option ℕ))
    (h : ∀ o ∈ s.2, Bounded n s.1 o) (i : ℕ) : Bounded n s.1 (s.2.getD i none) := by
  by_cases hi : i < s.2.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact h s.2[i] (List.getElem_mem hi)
  · rw [getD_ge _ _ _ (by omega)]
    simp [Bounded]

lemma gateAt_snoc_old (gs : List Gate) (g : Gate) (j : ℕ) (hj : j < gs.length) :
    gateAt ⟨gs ++ [g], 0⟩ j = gateAt ⟨gs, 0⟩ j := getD_append_lt gs [g] j _ hj

lemma gateAt_snoc_last (gs : List Gate) (g : Gate) :
    gateAt ⟨gs ++ [g], 0⟩ gs.length = g := getD_append_last gs g _

lemma append_pair_ao (n : ℕ) (gs : List Gate) (h : IsAO2 n ⟨gs, 0⟩)
    (a : Bool) (i j : ℕ) (hi : i < n + gs.length) (hj : j < n + gs.length) :
    IsAO2 n ⟨gs ++ [pairGate a i j], 0⟩ := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    rw [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact h.1 g hg
    · cases a <;> simp [pairGate]
  · intro k hk w hw
    have hkl : k < gs.length + 1 := by simpa using hk
    by_cases hkold : k < gs.length
    · rw [gateAt_snoc_old gs _ k hkold] at hw
      exact h.2.1 k hkold w hw
    · have hke : k = gs.length := by omega
      subst k
      rw [gateAt_snoc_last] at hw
      simp only [pairGate, List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> assumption
  · intro g hg
    rw [List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact h.2.2 g hg
    · rfl

lemma emitPair_ao (n : ℕ) (gs : List Gate) (h : IsAO2 n ⟨gs, 0⟩)
    (a : Bool) (x y : Option ℕ) (hx : Bounded n gs x) (hy : Bounded n gs y) :
    IsAO2 n ⟨(emitPair n gs a x y).1, 0⟩ := by
  cases x with
  | none => cases y <;> exact h
  | some i =>
    cases y with
    | none => exact h
    | some j => exact append_pair_ao n gs h a i j (hx i rfl) (hy j rfl)

lemma emitPair_length_ge (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ) :
    gs.length ≤ (emitPair n gs a x y).1.length := by
  cases x <;> cases y <;> simp [emitPair]

lemma compileStep_map_length (n q : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) :
    (compileStep n q s g).2.length = s.2.length + 1 := by
  unfold compileStep
  split_ifs <;> simp

lemma compileStep_size (n q : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) :
    (compileStep n q s g).1.length ≤ s.1.length + 1 := by
  unfold compileStep
  split_ifs
  · simp
  · exact emitPair_length_le _ _ _ _ _

lemma compileStep_valid (n q : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate) (hs : Valid n s) :
    Valid n (compileStep n q s g) := by
  have h0 := bounded_getD n s hs.2 (g.inputs.getD 0 0)
  have h1 := bounded_getD n s hs.2 (g.inputs.getD 1 0)
  unfold compileStep
  split_ifs <;> dsimp only [Valid]
  · refine ⟨hs.1, ?_⟩
    intro o ho
    rw [List.mem_append, List.mem_singleton] at ho
    rcases ho with ho | rfl
    · exact hs.2 o ho
    · simp [Bounded]
  · refine ⟨emitPair_ao _ _ hs.1 _ _ _ h0 h1, ?_⟩
    intro o ho
    rw [List.mem_append, List.mem_singleton] at ho
    rcases ho with ho | rfl
    · intro i hi
      have hb := hs.2 o ho i hi
      have hl := emitPair_length_ge n s.1 (isAnd g.op)
        (s.2.getD (g.inputs.getD 0 0) none) (s.2.getD (g.inputs.getD 1 0) none)
      omega
    · exact emitPair_bounded _ _ _ _ _ h0 h1

lemma form_eval (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (hlen : g.inputs.length = 2) (ws : List Bool) :
    g.op.eval (g.inputs.map fun i => ws.getD i false) =
      pairOp (isAnd g.op) (ws.getD (g.inputs.getD 0 0) false)
        (ws.getD (g.inputs.getD 1 0) false) := by
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
  rcases hop with hop | hop <;> simp [hop, hab, GateOp.eval, pairOp, isAnd]

lemma related_extend (xs old : List Bool) (gs : List Gate) (m : List (Option ℕ))
    (o : Option ℕ) (v : Bool) (hl : m.length = old.length)
    (hprior : ∀ i, optionalValue (vals gs xs) (m.getD i none) = old.getD i false)
    (hlast : optionalValue (vals gs xs) o = v) :
    Related xs (old ++ [v]) (gs, m ++ [o]) := by
  refine ⟨by simp [hl], ?_⟩
  intro i
  change optionalValue (vals gs xs) ((m ++ [o]).getD i none) = (old ++ [v]).getD i false
  rcases Nat.lt_trichotomy i m.length with hi | hi | hi
  · rw [getD_append_lt m [o] i none hi, getD_append_lt old [v] i false (by omega)]
    exact hprior i
  · subst i
    rw [getD_append_last, hl, getD_append_last]
    exact hlast
  · rw [getD_ge _ _ _ (by simp; omega), getD_ge _ _ _ (by simp; omega)]
    rfl

lemma compileStep_related (n q : ℕ) (xs old : List Bool) (hx : xs.length = n)
    (s : List Gate × List (Option ℕ)) (hs : Valid n s) (hr : Related xs old s)
    (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (hlen : g.inputs.length = 2) :
    Related xs (forceStep n q old g) (compileStep n q s g) := by
  by_cases hkill : s.2.length = n + q
  · have hold : old.length = n + q := by rw [← hr.1]; exact hkill
    simp only [compileStep, hkill, ↓reduceIte, forceStep, hold]
    exact related_extend xs old s.1 s.2 none false hr.1 hr.2 rfl
  · have hold : old.length ≠ n + q := by rw [← hr.1]; exact hkill
    simp only [compileStep, hkill, ↓reduceIte, forceStep, hold]
    apply related_extend xs old _ s.2 _ _ hr.1
    · intro i
      rw [emitPair_optional_prefix n s.1 (isAnd g.op) _ _ _ xs hx (bounded_getD n s hs.2 i)]
      exact hr.2 i
    · rw [emitPair_semantics n s.1 (isAnd g.op) _ _ xs hx, hr.2, hr.2]
      exact (form_eval g hop hlen old).symm

lemma initial_valid (n : ℕ) : Valid n (initial n) := by
  refine ⟨?_, ?_⟩
  · simp [initial, IsAO2, PEqualNP.EdgeOwnership.AndOrOnly, ReadsBack]
  · intro o ho
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp ho
    have hin := List.mem_range.mp hi
    simpa [Bounded, initial] using hin

lemma initial_related (n : ℕ) (xs : List Bool) (hx : xs.length = n) : Related xs xs (initial n) := by
  refine ⟨by simp [initial, hx], ?_⟩
  intro i
  by_cases hi : i < n
  · simp [initial, vals, List.getD_eq_getElem?_getD, hi, optionalValue]
  · have hn : n ≤ i := by omega
    simp [initial, vals, List.getD_eq_getElem?_getD, hi, hx, optionalValue]

lemma fold_valid_related (n q : ℕ) (xs old : List Bool) (hx : xs.length = n)
    (gs : List Gate) (hform : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2)
    (s : List Gate × List (Option ℕ)) (hs : Valid n s) (hr : Related xs old s) :
    Valid n (gs.foldl (compileStep n q) s) ∧
      Related xs (gs.foldl (forceStep n q) old) (gs.foldl (compileStep n q) s) := by
  induction gs generalizing s old with
  | nil => exact ⟨hs, hr⟩
  | cons g gs ih =>
    obtain ⟨hop, hlen⟩ := hform g (by simp)
    exact ih (forceStep n q old g) (fun h hh => hform h (by simp [hh])) (compileStep n q s g)
      (compileStep_valid n q s g hs) (compileStep_related n q xs old hx s hs hr g hop hlen)

lemma compiled_valid_related (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (xs : List Bool) (hx : xs.length = n) :
    Valid n (compiled n q C.gates) ∧ Related xs (forcedValues n q C xs) (compiled n q C.gates) := by
  exact fold_valid_related n q xs xs hx C.gates
    (fun g hg => ⟨hAO.1 g hg, hAO.2.2 g hg⟩) (initial n) (initial_valid n) (initial_related n xs hx)

lemma optionalValue_lookup (n : ℕ) (gs : List Gate) (xs : List Bool) (hx : xs.length = n)
    (o : Option ℕ) :
    (vals gs xs).getD (o.getD (n + gs.length)) false = optionalValue (vals gs xs) o := by
  cases o with
  | none =>
    change (vals gs xs).getD (n + gs.length) false = false
    exact getD_ge _ _ _ (by rw [vals_length, hx])
  | some i => rfl

lemma pruned_eval (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) (xs : List Bool) (hx : xs.length = n) :
    (pruned n q C).eval xs = (forcedValues n q C xs).getD C.output false := by
  have h := (compiled_valid_related n q C hAO xs hx).2.2 C.output
  change (vals (compiled n q C.gates).1 xs).getD
    (((compiled n q C.gates).2.getD C.output none).getD (n + (compiled n q C.gates).1.length)) false = _
  rw [optionalValue_lookup n _ xs hx]
  exact h

lemma pruned_ao (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) : IsAO2 n (pruned n q C) := by
  have h := (compiled_valid_related n q C hAO (List.replicate n false) (by simp)).1.1
  exact h

lemma compileStep_map_prior (n q : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate)
    (i : ℕ) (hi : i < s.2.length) :
    (compileStep n q s g).2.getD i none = s.2.getD i none := by
  unfold compileStep
  split_ifs <;> exact getD_append_lt _ _ _ _ hi

lemma fold_map_length (n q : ℕ) (gs : List Gate) (s : List Gate × List (Option ℕ)) :
    (gs.foldl (compileStep n q) s).2.length = s.2.length + gs.length := by
  induction gs generalizing s with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih, compileStep_map_length]
    simp [List.length_cons]
    omega

lemma fold_size_le (n q : ℕ) (gs : List Gate) (s : List Gate × List (Option ℕ)) :
    (gs.foldl (compileStep n q) s).1.length ≤ s.1.length + gs.length := by
  induction gs generalizing s with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons]
    have hh := ih (compileStep n q s g)
    have hs := compileStep_size n q s g
    simp only [List.length_cons]
    omega

lemma fold_map_prior (n q : ℕ) (gs : List Gate) (s : List Gate × List (Option ℕ))
    (i : ℕ) (hi : i < s.2.length) :
    (gs.foldl (compileStep n q) s).2.getD i none = s.2.getD i none := by
  induction gs generalizing s with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih (compileStep n q s g) (by rw [compileStep_map_length]; omega)]
    exact compileStep_map_prior n q s g i hi

lemma compiled_map_length (n q : ℕ) (gs : List Gate) :
    (compiled n q gs).2.length = n + gs.length := by
  rw [compiled, fold_map_length]
  simp [initial]

lemma compiled_size_le (n q : ℕ) (gs : List Gate) : (compiled n q gs).1.length ≤ gs.length := by
  simpa [compiled, initial] using fold_size_le n q gs (initial n)

lemma compiled_split (n q : ℕ) (gs : List Gate) (k : ℕ) :
    compiled n q gs = (gs.drop k).foldl (compileStep n q) (compiled n q (gs.take k)) := by
  unfold compiled
  rw [← List.foldl_append, List.take_append_drop]

lemma compiled_take_succ (n q : ℕ) (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    compiled n q (gs.take (j + 1)) = compileStep n q (compiled n q (gs.take j)) gs[j] := by
  unfold compiled
  rw [List.take_succ_eq_append_getElem hj, List.foldl_append]
  rfl

lemma forced_step (n q : ℕ) (gs : List Gate) (hq : q < gs.length) :
    compiled n q (gs.take (q + 1)) =
      ((compiled n q (gs.take q)).1, (compiled n q (gs.take q)).2 ++ [none]) := by
  rw [compiled_take_succ n q gs q hq]
  have hl : (compiled n q (gs.take q)).2.length = n + q := by
    rw [compiled_map_length, List.length_take, Nat.min_eq_left (by omega)]
  simp [compileStep, hl]

lemma killed_alias (n q : ℕ) (gs : List Gate) (hq : q < gs.length) :
    (compiled n q gs).2.getD (n + q) none = none := by
  rw [compiled_split n q gs (q + 1)]
  have hl : n + q < (compiled n q (gs.take (q + 1))).2.length := by
    rw [compiled_map_length, List.length_take, Nat.min_eq_left (by omega)]
    omega
  rw [fold_map_prior n q (gs.drop (q + 1)) _ (n + q) hl, forced_step n q gs hq]
  have hlq : (compiled n q (gs.take q)).2.length = n + q := by
    rw [compiled_map_length, List.length_take, Nat.min_eq_left (by omega)]
  change ((compiled n q (gs.take q)).2 ++ [none]).getD (n + q) none = none
  rw [← hlq, getD_append_last]

lemma emitPair_drop (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ)
    (h : x = none ∨ y = none) : (emitPair n gs a x y).1 = gs := by
  rcases h with rfl | rfl
  · cases y <;> rfl
  · cases x <;> rfl

lemma compileStep_drop_missing (n q : ℕ) (s : List Gate × List (Option ℕ)) (g : Gate)
    (w : ℕ) (hw : w ∈ g.inputs) (hlen : g.inputs.length = 2) (hnone : s.2.getD w none = none) :
    (compileStep n q s g).1 = s.1 := by
  unfold compileStep
  split_ifs
  · rfl
  · apply emitPair_drop
    obtain ⟨a, b, hab⟩ := List.length_eq_two.mp hlen
    simp only [hab, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inl (by simpa [hab] using hnone)
    · exact Or.inr (by simpa [hab] using hnone)

lemma reader_step_drop (n q r : ℕ) (gs : List Gate) (hqr : q < r) (hr : r < gs.length)
    (hread : n + q ∈ gs[r].inputs) (hlen : gs[r].inputs.length = 2) :
    (compiled n q (gs.take (r + 1))).1 = (compiled n q (gs.take r)).1 := by
  rw [compiled_take_succ n q gs r hr]
  apply compileStep_drop_missing n q _ gs[r] (n + q) hread hlen
  exact killed_alias n q (gs.take r) (by simp [List.length_take]; omega)

lemma count_two_skips (f : ℕ → ℕ) (N q r : ℕ) (hqr : q < r) (hr : r < N)
    (hzero : f 0 = 0) (hstep : ∀ j < N, f (j + 1) ≤ f j + 1)
    (hqdrop : f (q + 1) = f q) (hrdrop : f (r + 1) = f r) : f N + 2 ≤ N := by
  have hinterval : ∀ a d, a + d ≤ N → f (a + d) ≤ f a + d := by
    intro a d
    induction d with
    | zero => simp
    | succ d ih =>
      intro hd
      have hi := ih (by omega)
      have hs := hstep (a + d) (by omega)
      have he : a + (d + 1) = (a + d) + 1 := by omega
      rw [he]
      omega
  have h0q := hinterval 0 q (by omega)
  have hqr' := hinterval (q + 1) (r - (q + 1)) (by omega)
  have hrN := hinterval (r + 1) (N - (r + 1)) (by omega)
  have heq : q + 1 + (r - (q + 1)) = r := by omega
  have her : r + 1 + (N - (r + 1)) = N := by omega
  rw [heq, hqdrop] at hqr'
  rw [her, hrdrop] at hrN
  simp only [zero_add, hzero] at h0q
  omega

lemma pruned_size_two (n q r : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hqr : q < r) (hr : r < C.gates.length) (hread : n + q ∈ C.gates[r].inputs) :
    (pruned n q C).size + 2 ≤ C.size := by
  have hlen := hAO.2.2 C.gates[r] (List.getElem_mem hr)
  have h := count_two_skips (fun j => (compiled n q (C.gates.take j)).1.length)
    C.gates.length q r hqr hr (by simp [compiled, initial]) ?_ ?_ ?_
  · simpa [pruned, Circuit.size] using h
  · intro j hj
    rw [compiled_take_succ n q C.gates j hj]
    exact compileStep_size n q _ C.gates[j]
  · rw [forced_step n q C.gates (by omega)]
  · rw [reader_step_drop n q r C.gates hqr hr hread hlen]

end PEqualNP.Outside.L_meta_4675.Pruning

namespace PEqualNP.Outside.L_meta_4675.PruningTrace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.TopForm PEqualNP.TwoColour PEqualNP.Outside.L_meta_4675.Pruning
  PEqualNP.Outside.L_meta_4675.OrReachAPI

def AliasReach (n : ℕ) (C : Circuit) (gs : List Gate) (o : Option ℕ) (i : ℕ) : Prop :=
  ∀ w, o = some w → orIn n ⟨gs, 0⟩ w ⊆ orIn n C i

def ReachValid (n : ℕ) (C : Circuit) (s : List Gate × List (Option ℕ)) : Prop :=
  ∀ i, AliasReach n C s.1 (s.2.getD i none) i

def OrTrace (n : ℕ) (C : Circuit) (gs : List Gate) : Prop :=
  ∀ g < gs.length, (gateAt ⟨gs, 0⟩ g).op = GateOp.or →
    ∃ h < C.gates.length, (gateAt C h).op = GateOp.or ∧
      orIn n ⟨gs, 0⟩ (n + g) ⊆ orIn n C (n + h)

lemma emitPair_reach_prior (n : ℕ) (gs : List Gate) (a : Bool) (x y : Option ℕ)
    (w : ℕ) (hw : w < n + gs.length) :
    orIn n ⟨(emitPair n gs a x y).1, 0⟩ w = orIn n ⟨gs, 0⟩ w := by
  cases x <;> cases y <;> simp only [emitPair]
  exact orIn_append_prefix n gs [_] w hw

lemma emitPair_alias_prior (n : ℕ) (C : Circuit) (gs : List Gate) (a : Bool) (x y o : Option ℕ)
    (i : ℕ) (ho : Bounded n gs o) (ha : AliasReach n C gs o i) :
    AliasReach n C (emitPair n gs a x y).1 o i := by
  intro w hw
  rw [emitPair_reach_prior n gs a x y w (ho w hw)]
  exact ha w hw

lemma emitPair_output_reach (n : ℕ) (C : Circuit) (gs : List Gate) (hAO : IsAO2 n ⟨gs, 0⟩)
    (a : Bool) (x y : Option ℕ) (hx : Bounded n gs x) (hy : Bounded n gs y)
    (i j k : ℕ) (hxi : AliasReach n C gs x i) (hyj : AliasReach n C gs y j)
    (hr : orIn n C k = if a then ∅ else orIn n C i ∪ orIn n C j) :
    AliasReach n C (emitPair n gs a x y).1 (emitPair n gs a x y).2 k := by
  cases x with
  | none =>
    cases y with
    | none => simp [AliasReach, emitPair]
    | some v =>
      cases a
      · intro w hw
        have he : v = w := by simpa [emitPair] using hw
        subst w
        rw [hr]
        exact (hyj v rfl).trans Finset.subset_union_right
      · simp [AliasReach, emitPair]
  | some u =>
    cases y with
    | none =>
      cases a
      · intro w hw
        have he : u = w := by simpa [emitPair] using hw
        subst w
        rw [hr]
        exact (hxi u rfl).trans Finset.subset_union_left
      · simp [AliasReach, emitPair]
    | some v =>
      intro w hw
      have he : n + gs.length = w := by simpa [emitPair] using hw
      subst w
      have hu : u < n + gs.length := hx u rfl
      have hv : v < n + gs.length := hy v rfl
      have hao := append_pair_ao n gs hAO a u v hu hv
      change orIn n ⟨gs ++ [pairGate a u v], 0⟩ (n + gs.length) ⊆ _
      cases a with
      | false =>
        rw [orIn_or_pair n _ gs.length u v (by simp) (by rw [gateAt_snoc_last]; rfl)
          (by rw [gateAt_snoc_last]; rfl) hao.2.1]
        rw [orIn_append_prefix n gs [_] u hu, orIn_append_prefix n gs [_] v hv, hr]
        exact Finset.union_subset_union (hxi u rfl) (hyj v rfl)
      | true =>
        rw [orIn_non_or n _ gs.length (by simp) (by rw [gateAt_snoc_last]; simp [pairGate])]
        exact Finset.empty_subset _

lemma emitPair_trace (n : ℕ) (C : Circuit) (gs : List Gate) (hAO : IsAO2 n ⟨gs, 0⟩)
    (ht : OrTrace n C gs) (a : Bool) (x y : Option ℕ) (hx : Bounded n gs x) (hy : Bounded n gs y)
    (i j k : ℕ) (hk : k < C.gates.length)
    (hop : (gateAt C k).op = if a then GateOp.and else GateOp.or)
    (hxi : AliasReach n C gs x i) (hyj : AliasReach n C gs y j)
    (hr : orIn n C (n + k) = if a then ∅ else orIn n C i ∪ orIn n C j) :
    OrTrace n C (emitPair n gs a x y).1 := by
  cases x with
  | none => cases y <;> exact ht
  | some u =>
    cases y with
    | none => exact ht
    | some v =>
      intro g hg hgo
      change g < (gs ++ [pairGate a u v]).length at hg
      change (gateAt ⟨gs ++ [pairGate a u v], 0⟩ g).op = GateOp.or at hgo
      by_cases hgold : g < gs.length
      · rw [gateAt_snoc_old gs _ g hgold] at hgo
        obtain ⟨h, hh, hho, hsub⟩ := ht g hgold hgo
        refine ⟨h, hh, hho, ?_⟩
        change orIn n ⟨gs ++ [pairGate a u v], 0⟩ (n + g) ⊆ _
        rw [orIn_append_prefix n gs [_] (n + g) (by omega)]
        exact hsub
      · have hge : g = gs.length := by simp only [List.length_append, List.length_cons, List.length_nil] at hg; omega
        subst g
        rw [gateAt_snoc_last] at hgo
        have ha : a = false := by cases a <;> simp_all [pairGate]
        refine ⟨k, hk, by simpa [ha] using hop, ?_⟩
        exact emitPair_output_reach n C gs hAO a (some u) (some v) hx hy i j (n + k) hxi hyj hr
          (n + gs.length) rfl

lemma alias_extend (n : ℕ) (C : Circuit) (gs : List Gate) (m : List (Option ℕ)) (o : Option ℕ)
    (hprior : ∀ i, AliasReach n C gs (m.getD i none) i)
    (hlast : AliasReach n C gs o m.length) : ReachValid n C (gs, m ++ [o]) := by
  intro i w hw
  change (m ++ [o]).getD i none = some w at hw
  change orIn n ⟨gs, 0⟩ w ⊆ orIn n C i
  rcases Nat.lt_trichotomy i m.length with hi | hi | hi
  · rw [getD_append_lt m [o] i none hi] at hw
    exact hprior i w hw
  · subst i
    rw [getD_append_last] at hw
    exact hlast w hw
  · rw [getD_ge _ _ _ (by simp; omega)] at hw
    cases hw

lemma gateAt_mem (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k ∈ C.gates := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

lemma original_pair_reach (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) :
    orIn n C (n + k) = if isAnd (gateAt C k).op then ∅ else
      orIn n C ((gateAt C k).inputs.getD 0 0) ∪ orIn n C ((gateAt C k).inputs.getD 1 0) := by
  have hm := gateAt_mem C k hk
  have hlen := hAO.2.2 (gateAt C k) hm
  obtain ⟨i, j, hij⟩ := List.length_eq_two.mp hlen
  rcases hAO.1 (gateAt C k) hm with hop | hop
  · simp only [hop, isAnd, ↓reduceIte]
    exact orIn_non_or n C k hk (by rw [hop]; intro he; cases he)
  · simp only [hop, isAnd, hij, List.getD_cons_zero, List.getD_cons_succ]
    exact orIn_or_pair n C k i j hk hop hij hAO.2.1

lemma original_gate_kind (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) :
    (gateAt C k).op = if isAnd (gateAt C k).op then GateOp.and else GateOp.or := by
  rcases hAO.1 (gateAt C k) (gateAt_mem C k hk) with hop | hop <;> simp [hop, isAnd]

lemma compileStep_reaches (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ) (hj : j < C.gates.length)
    (s : List Gate × List (Option ℕ)) (hs : Valid n s) (hr : ReachValid n C s)
    (ht : OrTrace n C s.1) (hl : s.2.length = n + j) :
    ReachValid n C (compileStep n q s (gateAt C j)) ∧
      OrTrace n C (compileStep n q s (gateAt C j)).1 := by
  have hx := bounded_getD n s hs.2 ((gateAt C j).inputs.getD 0 0)
  have hy := bounded_getD n s hs.2 ((gateAt C j).inputs.getD 1 0)
  have hpair := original_pair_reach n C hAO j hj
  unfold compileStep
  split_ifs <;> dsimp only
  · refine ⟨alias_extend n C s.1 s.2 none hr ?_, ht⟩
    simp [AliasReach]
  · constructor
    · apply alias_extend
      · intro i
        exact emitPair_alias_prior n C s.1 _ _ _ (s.2.getD i none) i
          (bounded_getD n s hs.2 i) (hr i)
      · rw [hl]
        exact emitPair_output_reach n C s.1 hs.1 _ _ _ hx hy _ _ (n + j) (hr _) (hr _) hpair
    · exact emitPair_trace n C s.1 hs.1 ht _ _ _ hx hy _ _ j hj
        (original_gate_kind n C hAO j hj) (hr _) (hr _) hpair

lemma initial_reaches (n : ℕ) (C : Circuit) : ReachValid n C (initial n) ∧ OrTrace n C (initial n).1 := by
  constructor
  · intro i w hw
    by_cases hi : i < n
    · have hget : (initial n).2.getD i none = some i := by
        simp [initial, List.getD_eq_getElem?_getD, hi]
      rw [hget] at hw
      have he : i = w := Option.some.inj hw
      subst w
      change orIn n ⟨[], 0⟩ i ⊆ orIn n C i
      rw [orIn_input n _ i hi, orIn_input n C i hi]
    · have hget : (initial n).2.getD i none = none := by
        simp [initial, List.getD_eq_getElem?_getD, hi]
      rw [hget] at hw
      cases hw
  · intro g hg
    simp [initial] at hg

lemma gateAt_eq_getElem (C : Circuit) (j : ℕ) (hj : j < C.gates.length) : gateAt C j = C.gates[j] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hj]

lemma compiled_reaches (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) :
    ReachValid n C (compiled n q C.gates) ∧ OrTrace n C (compiled n q C.gates).1 := by
  have h : ∀ j, j ≤ C.gates.length →
      Valid n (compiled n q (C.gates.take j)) ∧
      ReachValid n C (compiled n q (C.gates.take j)) ∧
      OrTrace n C (compiled n q (C.gates.take j)).1 := by
    intro j
    induction j with
    | zero =>
      intro hj
      simpa [compiled] using (show Valid n (initial n) ∧ ReachValid n C (initial n) ∧
        OrTrace n C (initial n).1 from ⟨initial_valid n, initial_reaches n C⟩)
    | succ j ih =>
      intro hj
      obtain ⟨hv, hr, ht⟩ := ih (by omega)
      have hlt : j < C.gates.length := by omega
      rw [compiled_take_succ n q C.gates j hlt, ← gateAt_eq_getElem C j hlt]
      refine ⟨compileStep_valid n q _ (gateAt C j) hv, ?_⟩
      apply compileStep_reaches n q C hAO j hlt _ hv hr ht
      rw [compiled_map_length, List.length_take, Nat.min_eq_left (by omega)]
  simpa using (h C.gates.length le_rfl).2

lemma trace_count_zero (n : ℕ) (C : Circuit) (gs : List Gate) (s : ℕ → Bool)
    (ht : OrTrace n C gs) (hz : tCount n C s = 0) : tCount n ⟨gs, 0⟩ s = 0 := by
  have he : twoColour n C s = ∅ := Finset.card_eq_zero.mp hz
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro g hg
  have htwo : IsTwoColour n ⟨gs, 0⟩ s g := (Finset.mem_filter.mp hg).2
  obtain ⟨h, hh, hop, hsub⟩ := ht g htwo.1 htwo.2.1
  have hold : IsTwoColour n C s h := by
    refine ⟨hh, hop, ?_, ?_⟩
    · obtain ⟨i, hi, hsi⟩ := htwo.2.2.1
      exact ⟨i, hsub hi, hsi⟩
    · obtain ⟨i, hi, hsi⟩ := htwo.2.2.2
      exact ⟨i, hsub hi, hsi⟩
  have hm : h ∈ twoColour n C s := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hh, hold⟩
  rw [he] at hm
  simp at hm

lemma pruned_count_zero (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) (s : ℕ → Bool)
    (hz : tCount n C s = 0) : tCount n (pruned n q C) s = 0 := by
  exact trace_count_zero n C (compiled n q C.gates).1 s (compiled_reaches n q C hAO).2 hz

end PEqualNP.Outside.L_meta_4675.PruningTrace

namespace PEqualNP.Outside.L_meta_4675.ConeAPI

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership
  PEqualNP.Outside.L_meta_4675.OneJunk

def WireCone (n : ℕ) (C : Circuit) (w k : ℕ) : Prop :=
  w = n + k ∨ (n ≤ w ∧ InCone n C k (w - n))

lemma wireCone_bound (n : ℕ) (C : Circuit) (w k : ℕ) (h : WireCone n C w k) : n + k ≤ w := by
  rcases h with h | ⟨hn, hc⟩
  · omega
  · have := inCone_lt n C (w - n) k hc
    omega

lemma cones_append_prefix (n : ℕ) (gs hs : List Gate) (k : ℕ) (hk : k < gs.length) :
    (cones n ⟨gs ++ hs, 0⟩).getD k [] = (cones n ⟨gs, 0⟩).getD k [] := by
  let f : List (List ℕ) → Gate → List ℕ := fun cs g =>
    (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
      (fun w => (w - n) :: cs.getD (w - n) [])
  have hlen : (cones n ⟨gs, 0⟩).length = gs.length := cones_length n ⟨gs, 0⟩
  have hp := (foldl_append_spec f hs (cones n ⟨gs, 0⟩)).2.1 k (by rw [hlen]; exact hk)
  have he : (fun cs g => cs ++ [f cs g]) = coneStep n := rfl
  rw [he] at hp
  change ((gs ++ hs).foldl (coneStep n) []).getD k [] =
    (gs.foldl (coneStep n) []).getD k []
  rw [List.foldl_append]
  simpa only [List.getD_eq_getElem?_getD, cones] using congrArg (fun z => z.getD []) hp

lemma wireCone_append_prefix (n : ℕ) (gs hs : List Gate) (w : ℕ) (hw : w < n + gs.length)
    (k : ℕ) : WireCone n ⟨gs ++ hs, 0⟩ w k ↔ WireCone n ⟨gs, 0⟩ w k := by
  by_cases hn : n ≤ w
  · have hk : w - n < gs.length := by omega
    simp only [WireCone, hn, true_and, InCone, cones_append_prefix n gs hs (w - n) hk]
  · simp [WireCone, hn]

lemma wireCone_of_input (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (w : ℕ) (hw : w ∈ (gateAt C j).inputs) (hwb : w < n + j)
    (k : ℕ) (hc : WireCone n C w k) : WireCone n C (n + j) k := by
  right
  refine ⟨by omega, ?_⟩
  rw [Nat.add_sub_cancel_left]
  rcases hc with he | ⟨hn, hcone⟩
  · subst w
    exact inCone_of_input n C k j hj (by omega) hw
  · have he : w = n + (w - n) := by omega
    exact inCone_trans_of_input n C k (w - n) j hj (by omega) (by rwa [← he]) hcone

lemma wireCone_gate_iff (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length) (k : ℕ) :
    WireCone n C (n + j) k ↔ k = j ∨
      ∃ w ∈ (gateAt C j).inputs, w < n + j ∧ WireCone n C w k := by
  constructor
  · rintro (he | ⟨_, hc⟩)
    · left; omega
    · rw [Nat.add_sub_cancel_left] at hc
      unfold InCone at hc
      rw [cones_getD_eq n C j hj, List.mem_flatMap] at hc
      obtain ⟨w, hw, hc⟩ := hc
      simp only [List.mem_filter, decide_eq_true_eq] at hw
      refine Or.inr ⟨w, hw.1, hw.2.2, ?_⟩
      simp only [List.mem_cons] at hc
      rcases hc with he | hc
      · left; omega
      · exact Or.inr ⟨hw.2.1, hc⟩
  · rintro (rfl | ⟨w, hw, hwb, hc⟩)
    · exact Or.inl rfl
    · exact wireCone_of_input n C j hj w hw hwb k hc

end PEqualNP.Outside.L_meta_4675.ConeAPI

namespace PEqualNP.Outside.L_meta_4675.ConeTrace

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.TopForm PEqualNP.Outside.L_meta_4675.Pruning
  PEqualNP.Outside.L_meta_4675.ConeAPI

def AliasCone (n : ℕ) (C : Circuit) (gs : List Gate) (o : ℕ → ℕ)
    (a : Option ℕ) (i : ℕ) : Prop :=
  ∀ w, a = some w → ∀ k < gs.length, WireCone n ⟨gs, 0⟩ w k → WireCone n C i (o k)

def GateTrace (n : ℕ) (C : Circuit) (j : ℕ)
    (s : List Gate × List (Option ℕ)) (o : ℕ → ℕ) : Prop :=
  (∀ k < s.1.length, o k < j) ∧
  (∀ a b, a < b → b < s.1.length → o a < o b) ∧
  (∀ k < s.1.length, (gateAt ⟨s.1, 0⟩ k).op = (gateAt C (o k)).op) ∧
  (∀ k < s.1.length, s.2.getD (n + o k) none = some (n + k)) ∧
  (∀ i, AliasCone n C s.1 o (s.2.getD i none) i)

lemma alias_none (n : ℕ) (C : Circuit) (gs : List Gate) (o : ℕ → ℕ) (i : ℕ) :
    AliasCone n C gs o none i := by
  intro w hw
  cases hw

lemma alias_parent (n : ℕ) (C : Circuit) (gs : List Gate) (o : ℕ → ℕ) (a : Option ℕ)
    (j i : ℕ) (hj : j < C.gates.length) (hi : i ∈ (gateAt C j).inputs)
    (hib : i < n + j) (ha : AliasCone n C gs o a i) : AliasCone n C gs o a (n + j) := by
  intro w hw k hk hcone
  exact wireCone_of_input n C j hj i hi hib _ (ha w hw k hk hcone)

lemma alias_lookup_append (n : ℕ) (C : Circuit) (gs : List Gate) (o : ℕ → ℕ)
    (m : List (Option ℕ)) (a : Option ℕ)
    (hprior : ∀ i, AliasCone n C gs o (m.getD i none) i)
    (hlast : AliasCone n C gs o a m.length) :
    ∀ i, AliasCone n C gs o ((m ++ [a]).getD i none) i := by
  intro i
  rcases Nat.lt_trichotomy i m.length with hi | hi | hi
  · rw [getD_append_lt m [a] i none hi]
    exact hprior i
  · subst i
    rw [getD_append_last]
    exact hlast
  · rw [getD_ge _ _ _ (by simp; omega)]
    exact alias_none n C gs o i

lemma trace_drop (n : ℕ) (C : Circuit) (j : ℕ) (s : List Gate × List (Option ℕ))
    (o : ℕ → ℕ) (ht : GateTrace n C j s o) (hl : s.2.length = n + j)
    (a : Option ℕ) (ha : AliasCone n C s.1 o a (n + j)) :
    GateTrace n C (j + 1) (s.1, s.2 ++ [a]) o := by
  refine ⟨fun k hk => Nat.lt_succ_of_lt (ht.1 k hk), ht.2.1, ht.2.2.1, ?_, ?_⟩
  · intro k hk
    rw [getD_append_lt s.2 [a] (n + o k) none (by rw [hl]; have := ht.1 k hk; omega)]
    exact ht.2.2.2.1 k hk
  · apply alias_lookup_append n C s.1 o s.2 a ht.2.2.2.2
    rwa [hl]

def extendOrigin (o : ℕ → ℕ) (N j k : ℕ) : ℕ := if k < N then o k else j

lemma alias_append_gate (n : ℕ) (C : Circuit) (gs : List Gate) (o : ℕ → ℕ)
    (j : ℕ) (g : Gate) (a : Option ℕ) (i : ℕ) (ha : Bounded n gs a)
    (hc : AliasCone n C gs o a i) :
    AliasCone n C (gs ++ [g]) (extendOrigin o gs.length j) a i := by
  intro w hw k hk hcone
  have hwb := ha w hw
  have hkb := wireCone_bound n ⟨gs ++ [g], 0⟩ w k hcone
  have hko : k < gs.length := by omega
  have hold := (wireCone_append_prefix n gs [g] w hwb k).mp hcone
  simpa [extendOrigin, hko] using hc w hw k hko hold

lemma alias_emitted (n : ℕ) (C : Circuit) (gs : List Gate) (o : ℕ → ℕ)
    (j a b u v : ℕ) (hj : j < C.gates.length) (hinputs : (gateAt C j).inputs = [a, b])
    (ha : a < n + j) (hb : b < n + j) (hu : u < n + gs.length) (hv : v < n + gs.length)
    (hca : AliasCone n C gs o (some u) a) (hcb : AliasCone n C gs o (some v) b)
    (isA : Bool) :
    AliasCone n C (gs ++ [pairGate isA u v]) (extendOrigin o gs.length j)
      (some (n + gs.length)) (n + j) := by
  intro w hw k hk hcone
  have hwe : w = n + gs.length := (Option.some.inj hw).symm
  subst w
  have hc := (wireCone_gate_iff n ⟨gs ++ [pairGate isA u v], 0⟩ gs.length
    (by simp) k).mp hcone
  rcases hc with rfl | ⟨z, hz, hzb, hzc⟩
  · simp only [extendOrigin, lt_self_iff_false, ↓reduceIte]
    exact Or.inl rfl
  · have hzmem : z = u ∨ z = v := by
      rw [gateAt_snoc_last] at hz
      simpa [pairGate] using hz
    have hko : k < gs.length := by
      have hbound := wireCone_bound n ⟨gs ++ [pairGate isA u v], 0⟩ z k hzc
      omega
    simp only [extendOrigin, hko, ↓reduceIte]
    rcases hzmem with hzu | hzv
    · subst z
      have hco := (wireCone_append_prefix n gs [_] u hu k).mp hzc
      exact wireCone_of_input n C j hj a (by simp [hinputs]) ha _ (hca u rfl k hko hco)
    · subst z
      have hco := (wireCone_append_prefix n gs [_] v hv k).mp hzc
      exact wireCone_of_input n C j hj b (by simp [hinputs]) hb _ (hcb v rfl k hko hco)

lemma trace_emit (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < C.gates.length)
    (s : List Gate × List (Option ℕ)) (o : ℕ → ℕ) (ht : GateTrace n C j s o)
    (hvld : Valid n s) (hl : s.2.length = n + j)
    (a b u v : ℕ) (hinputs : (gateAt C j).inputs = [a, b])
    (ha : a < n + j) (hb : b < n + j)
    (hua : s.2.getD a none = some u) (hvb : s.2.getD b none = some v)
    (hop : (pairGate (isAnd (gateAt C j).op) u v).op = (gateAt C j).op) :
    GateTrace n C (j + 1)
      (s.1 ++ [pairGate (isAnd (gateAt C j).op) u v], s.2 ++ [some (n + s.1.length)])
      (extendOrigin o s.1.length j) := by
  have hu := bounded_getD n s hvld.2 a u hua
  have hv := bounded_getD n s hvld.2 b v hvb
  have hlen : (s.1 ++ [pairGate (isAnd (gateAt C j).op) u v]).length = s.1.length + 1 := by simp
  have hsplit : ∀ k < (s.1 ++ [pairGate (isAnd (gateAt C j).op) u v]).length,
      k < s.1.length ∨ k = s.1.length := by intro k hk; rw [hlen] at hk; omega
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk
    rcases hsplit k hk with hk | rfl
    · simp only [extendOrigin, hk, ↓reduceIte]
      exact Nat.lt_succ_of_lt (ht.1 k hk)
    · simp [extendOrigin]
  · intro r t hrt htlen
    rcases hsplit t htlen with hto | rfl
    · have hro : r < s.1.length := by omega
      simp only [extendOrigin, hro, hto, ↓reduceIte]
      exact ht.2.1 r t hrt hto
    · simp only [extendOrigin, hrt, lt_self_iff_false, ↓reduceIte]
      exact ht.1 r hrt
  · intro k hk
    rcases hsplit k hk with hk | rfl
    · rw [gateAt_snoc_old s.1 _ k hk]
      simp only [extendOrigin, hk, ↓reduceIte]
      exact ht.2.2.1 k hk
    · rw [gateAt_snoc_last]
      simpa [extendOrigin] using hop
  · intro k hk
    rcases hsplit k hk with hk | rfl
    · simp only [extendOrigin, hk, ↓reduceIte]
      rw [getD_append_lt s.2 [_] _ none (by rw [hl]; have := ht.1 k hk; omega)]
      exact ht.2.2.2.1 k hk
    · simp only [extendOrigin, lt_self_iff_false, ↓reduceIte]
      rw [← hl, getD_append_last]
  · apply alias_lookup_append
    · intro i
      exact alias_append_gate n C s.1 o j _ (s.2.getD i none) i
        (bounded_getD n s hvld.2 i) (ht.2.2.2.2 i)
    · rw [hl]
      apply alias_emitted n C s.1 o j a b u v hj hinputs ha hb hu hv
      · rw [← hua]
        exact ht.2.2.2.2 a
      · rw [← hvb]
        exact ht.2.2.2.2 b

lemma compileStep_trace (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) (j : ℕ)
    (hj : j < C.gates.length) (s : List Gate × List (Option ℕ)) (o : ℕ → ℕ)
    (ht : GateTrace n C j s o) (hvld : Valid n s) (hl : s.2.length = n + j) :
    ∃ o', GateTrace n C (j + 1) (compileStep n q s (gateAt C j)) o' := by
  have hm : gateAt C j ∈ C.gates := by
    rw [PEqualNP.Outside.L_meta_4675.PruningTrace.gateAt_eq_getElem C j hj]
    exact List.getElem_mem hj
  obtain ⟨a, b, hab⟩ := List.length_eq_two.mp (hAO.2.2 _ hm)
  have ha : a < n + j := hAO.2.1 j hj a (by simp [hab])
  have hb : b < n + j := hAO.2.1 j hj b (by simp [hab])
  by_cases hkill : s.2.length = n + q
  · simp only [compileStep, hkill, ↓reduceIte]
    exact ⟨o, trace_drop n C j s o ht hl none (alias_none n C s.1 o (n + j))⟩
  · simp only [compileStep, hkill, ↓reduceIte, hab, List.getD_cons_zero, List.getD_cons_succ]
    cases hx : s.2.getD a none with
    | none =>
      cases hy : s.2.getD b none with
      | none =>
        simp only [emitPair]
        exact ⟨o, trace_drop n C j s o ht hl none (alias_none n C s.1 o (n + j))⟩
      | some v =>
        cases his : isAnd (gateAt C j).op
        · simp only [emitPair, Bool.false_eq_true, ↓reduceIte]
          refine ⟨o, trace_drop n C j s o ht hl (some v) ?_⟩
          apply alias_parent n C s.1 o (some v) j b hj (by simp [hab]) hb
          rw [← hy]
          exact ht.2.2.2.2 b
        · simp only [emitPair, ↓reduceIte]
          exact ⟨o, trace_drop n C j s o ht hl none (alias_none n C s.1 o (n + j))⟩
    | some u =>
      cases hy : s.2.getD b none with
      | none =>
        cases his : isAnd (gateAt C j).op
        · simp only [emitPair, Bool.false_eq_true, ↓reduceIte]
          refine ⟨o, trace_drop n C j s o ht hl (some u) ?_⟩
          apply alias_parent n C s.1 o (some u) j a hj (by simp [hab]) ha
          rw [← hx]
          exact ht.2.2.2.2 a
        · simp only [emitPair, ↓reduceIte]
          exact ⟨o, trace_drop n C j s o ht hl none (alias_none n C s.1 o (n + j))⟩
      | some v =>
        simp only [emitPair]
        refine ⟨extendOrigin o s.1.length j, trace_emit n C j hj s o ht hvld hl a b u v hab ha hb hx hy ?_⟩
        exact (PEqualNP.Outside.L_meta_4675.PruningTrace.original_gate_kind n C hAO j hj).symm

lemma initial_trace (n : ℕ) (C : Circuit) : GateTrace n C 0 (initial n) (fun _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k hk; simp [initial] at hk
  · intro a b hab hb; simp [initial] at hb
  · intro k hk; simp [initial] at hk
  · intro k hk; simp [initial] at hk
  · intro i w hw k hk; simp [initial] at hk

lemma compiled_trace (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) :
    ∃ o, GateTrace n C C.gates.length (compiled n q C.gates) o := by
  have h : ∀ j, j ≤ C.gates.length → Valid n (compiled n q (C.gates.take j)) ∧
      ∃ o, GateTrace n C j (compiled n q (C.gates.take j)) o := by
    intro j
    induction j with
    | zero =>
      intro hj
      simpa [compiled] using (show Valid n (initial n) ∧
        ∃ o, GateTrace n C 0 (initial n) o from ⟨initial_valid n, _, initial_trace n C⟩)
    | succ j ih =>
      intro hj
      obtain ⟨hv, o, ht⟩ := ih (by omega)
      have hlt : j < C.gates.length := by omega
      rw [compiled_take_succ n q C.gates j hlt,
        ← PEqualNP.Outside.L_meta_4675.PruningTrace.gateAt_eq_getElem C j hlt]
      refine ⟨compileStep_valid n q _ (gateAt C j) hv, ?_⟩
      apply compileStep_trace n q C hAO j hlt _ o ht hv
      rw [compiled_map_length, List.length_take, Nat.min_eq_left (by omega)]
  simpa using (h C.gates.length le_rfl).2

lemma pruned_gate_cone_embedding (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) :
    ∃ o : ℕ → ℕ,
      (∀ k < (pruned n q C).gates.length, o k < C.gates.length) ∧
      (∀ a b, a < b → b < (pruned n q C).gates.length → o a < o b) ∧
      (∀ k < (pruned n q C).gates.length,
        (gateAt (pruned n q C) k).op = (gateAt C (o k)).op) ∧
      (∀ a b, a < (pruned n q C).gates.length → b < (pruned n q C).gates.length →
        InCone n (pruned n q C) a b → InCone n C (o a) (o b)) ∧
      (∀ k < (pruned n q C).gates.length, o k ≠ q) := by
  obtain ⟨o, ht⟩ := compiled_trace n q C hAO
  refine ⟨o, ht.1, ht.2.1, ht.2.2.1, ?_, ?_⟩
  · intro a b ha hb hc
    have hab : a < b := PEqualNP.Outside.L_meta_4675.OneJunk.inCone_lt n (pruned n q C) b a hc
    have horig := ht.2.1 a b hab hb
    have hnew : WireCone n ⟨(compiled n q C.gates).1, 0⟩ (n + b) a :=
      Or.inr ⟨by omega, by simpa only [Nat.add_sub_cancel_left, InCone, cones, pruned] using hc⟩
    have hold := ht.2.2.2.2 (n + o b) (n + b) (ht.2.2.2.1 b hb) a ha hnew
    rcases hold with he | ⟨_, hold⟩
    · omega
    · simpa using hold
  · intro k hk he
    by_cases hq : q < C.gates.length
    · have hlookup := ht.2.2.2.1 k hk
      rw [he, killed_alias n q C.gates hq] at hlookup
      cases hlookup
    · have hb := ht.1 k hk
      omega

lemma pruned_andPairs_le (n q : ℕ) (C : Circuit) (hAO : IsAO2 n C) :
    andPairs n (pruned n q C) ≤ andPairs n C := by
  obtain ⟨o, hb, hs, hop, hc, _⟩ := pruned_gate_cone_embedding n q C hAO
  have hi : ∀ a b, a < (pruned n q C).gates.length → b < (pruned n q C).gates.length →
      o a = o b → a = b := by
    intro a b ha hb he
    rcases Nat.lt_trichotomy a b with h | h | h
    · have := hs a b h hb; omega
    · exact h
    · have := hs b a h ha; omega
  unfold andPairs
  apply Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => (o p.1, o p.2))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hp ⊢
    exact ⟨⟨hb p.1 hp.1.1, hb p.2 hp.1.2⟩,
      (hop p.1 hp.1.1).symm.trans hp.2.1,
      (hop p.2 hp.1.2).symm.trans hp.2.2.1,
      hc p.1 p.2 hp.1.1 hp.1.2 hp.2.2.2⟩
  · intro a ha b hb he
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at ha hb
    have he1 : o a.1 = o b.1 := congrArg Prod.fst he
    have he2 : o a.2 = o b.2 := congrArg Prod.snd he
    exact Prod.ext (hi a.1 b.1 ha.1.1 hb.1.1 he1) (hi a.2 b.2 ha.1.2 hb.1.2 he2)

end PEqualNP.Outside.L_meta_4675.ConeTrace
