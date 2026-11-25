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

namespace PEqualNP.Outside.L_meta_4675.FirstJunk

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
  PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.TwoColour
  PEqualNP.Outside.L_meta_4675.MaskingNext PEqualNP.Outside.L_meta_4675.OneJunk

lemma operand_pure (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C) (q : ℕ)
    (hq : q < C.gates.length) (hqand : (gateAt C q).op = GateOp.and)
    (hfirst : ∀ k < q, ¬ IsDirtyAnd n G C k) (b : Fin 2) (x : Fin n → Bool) :
    PEqualNP.BlindGate.wireValue C n x (opnd C q b) = true ↔
      ∃ i ∈ side (n := n) C q b, x i = true := by
  constructor
  · intro hv
    have hw := ((operands n C hAO q hq).2 b).2
    rcases true_wire_source n C hAO x _ (by omega) hv with hi | ⟨k, hk, hr, hkand, _⟩
    · exact hi
    · have hc := operand_reach_inCone n C hAO q hq b k hr
      have hkq := inCone_lt n C q k hc
      have hb : BelowF G C k := by
        intro y hy
        cases hf : graphFun G ∅ y with
        | false => exact False.elim (hfirst k hkq ⟨hkand, hk, y, hy, hf⟩)
        | true => rfl
      exact False.elim (hTop k hk q hq hkand hb hqand hc)
  · rintro ⟨i, hi, hxi⟩
    exact orIn_true n C hAO x _ i hi hxi

lemma semantics (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C) (q : ℕ)
    (hq : q < C.gates.length) (hqand : (gateAt C q).op = GateOp.and)
    (hfirst : ∀ k < q, ¬ IsDirtyAnd n G C k) (x : Fin n → Bool) :
    gateVal n C q x = true ↔
      (∃ i ∈ side (n := n) C q 0, x i = true) ∧
      (∃ i ∈ side (n := n) C q 1, x i = true) := by
  rw [and_value n C hAO q hq hqand x,
    operand_pure n G C hAO hTop q hq hqand hfirst 0 x,
    operand_pure n G C hAO hTop q hq hqand hfirst 1 x]

lemma sides_nonempty (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (hAO : IsAO2 n C) (hTop : TopForm G C) (q : ℕ)
    (hq : IsDirtyAnd n G C q) (hfirst : ∀ k < q, ¬ IsDirtyAnd n G C k) :
    (side (n := n) C q 0).Nonempty ∧ (side (n := n) C q 1).Nonempty := by
  obtain ⟨x, hx, _⟩ := hq.2.2
  obtain ⟨⟨i, hi, _⟩, ⟨j, hj, _⟩⟩ :=
    (semantics n G C hAO hTop q hq.2.1 hq.1 hfirst x).mp hx
  exact ⟨⟨i, hi⟩, ⟨j, hj⟩⟩

lemma wire_one_colour (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (colour : ℕ → Bool)
    (hz : tCount n C colour = 0) (w : ℕ) (hw : w < n + C.gates.length) :
    (∀ i ∈ orIn n C w, colour i = false) ∨
      (∀ i ∈ orIn n C w, colour i = true) := by
  by_cases hin : w < n
  · rw [PEqualNP.Outside.L_meta_4675.OrReachAPI.orIn_input n C w hin]
    cases hc : colour w
    · left
      intro i hi
      have he : i = ⟨w, hin⟩ := Finset.mem_singleton.mp hi
      subst i
      exact hc
    · right
      intro i hi
      have he : i = ⟨w, hin⟩ := Finset.mem_singleton.mp hi
      subst i
      exact hc
  · obtain ⟨g, rfl⟩ : ∃ g, w = n + g := ⟨w - n, by omega⟩
    have hg : g < C.gates.length := by omega
    have hm : gateAt C g ∈ C.gates := by
      rw [gateAt_eq_getElem C g hg]
      exact List.getElem_mem hg
    rcases hAO.1 _ hm with hop | hop
    · have he := PEqualNP.Outside.L_meta_4675.OrReachAPI.orIn_non_or n C g hg
        (by rw [hop]; intro he; cases he)
      rw [he]
      simp
    · exact orIn_one_colour n C colour hz g hg hop

lemma sides_one_colour (n : ℕ) (C : Circuit) (hAO : IsAO2 n C) (colour : ℕ → Bool)
    (hz : tCount n C colour = 0) (q : ℕ) (hq : q < C.gates.length) (b : Fin 2) :
    (∀ i ∈ side (n := n) C q b, colour i = false) ∨
      (∀ i ∈ side (n := n) C q b, colour i = true) := by
  have hw := ((operands n C hAO q hq).2 b).2
  exact wire_one_colour n C hAO colour hz _ (by omega)

end PEqualNP.Outside.L_meta_4675.FirstJunk
