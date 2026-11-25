import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.NormalizationFinal

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.TwoColour

lemma no_twoColour_of_count_zero (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hz : tCount n C s = 0) (g : ℕ) : ¬ IsTwoColour n C s g := by
  intro hg
  have he : twoColour n C s = ∅ := Finset.card_eq_zero.mp hz
  have hm : g ∈ twoColour n C s :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hg.1, hg⟩
  rw [he] at hm
  simp at hm

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

lemma below_output_orIn_empty (n : ℕ) (C : Circuit) (hAO : IsAO2 n C)
    (hunit : ∀ i : Fin n, circuitFun n C (fun k => decide (k = i)) = false)
    (w : ℕ) (hw : PEqualNP.CircuitMoves.WireBelowOutput n C w) :
    orIn n C w = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  have hv := orIn_true n C hAO (fun k => decide (k = i)) w i hi (by simp)
  have ht := hw (fun k => decide (k = i)) hv
  have hf := hunit i
  change C.eval (List.ofFn (fun k => decide (k = i))) = false at hf
  rw [hf] at ht
  cases ht

lemma orIn_gate_nonempty_is_or (n : ℕ) (C : Circuit) (g : ℕ)
    (h : (orIn n C (n + g)).Nonempty) :
    g < C.gates.length ∧ (gateAt C g).op = GateOp.or := by
  obtain ⟨i, hi⟩ := h
  rw [mem_orIn] at hi
  rcases hi with hi | ⟨k, hk, hr, hop, hin⟩
  · have hlt := i.isLt
    omega
  · obtain ⟨hg, he | ⟨hgo, hrest⟩⟩ := (orReaches_iff n C g k).mp hr
    · exact ⟨hg, he ▸ hop⟩
    · exact ⟨hg, hgo⟩

lemma all_orIn_same_colour (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hz : tCount n C s = 0) (w : ℕ) (i j : Fin n)
    (hi : i ∈ orIn n C w) (hj : j ∈ orIn n C w) : s i = s j := by
  by_cases hwi : w < n
  · have hiw : (i : ℕ) = w := by
      rw [mem_orIn] at hi
      rcases hi with he | ⟨k, hk, hr, hop, hin⟩
      · exact he
      · have hn := hr.1
        omega
    have hjw : (j : ℕ) = w := by
      rw [mem_orIn] at hj
      rcases hj with he | ⟨k, hk, hr, hop, hin⟩
      · exact he
      · have hn := hr.1
        omega
    rw [hiw, hjw]
  · obtain ⟨g, rfl⟩ : ∃ g, w = n + g := ⟨w - n, by omega⟩
    obtain ⟨hg, hop⟩ := orIn_gate_nonempty_is_or n C g ⟨i, hi⟩
    exact orIn_same_colour n C s hz g hg hop i j hi hj

lemma all_orIn_one_colour (n : ℕ) (C : Circuit) (s : ℕ → Bool)
    (hz : tCount n C s = 0) (w : ℕ) :
    (∀ i ∈ orIn n C w, s i = false) ∨
      (∀ i ∈ orIn n C w, s i = true) := by
  by_cases h : ∃ i ∈ orIn n C w, s i = true
  · obtain ⟨i, hi, hci⟩ := h
    right
    intro j hj
    exact (all_orIn_same_colour n C s hz w j i hj hi).trans hci
  · left
    intro i hi
    cases hci : s i
    · rfl
    · exact False.elim (h ⟨i, hi, hci⟩)

end PEqualNP.Outside.L_meta_4675.NormalizationFinal
