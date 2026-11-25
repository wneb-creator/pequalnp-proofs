import Mathlib
import PEqualNP.Defs

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

namespace PEqualNP.Outside.L_meta_4675.StarAppend

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TwoColour
open PEqualNP.Outside.L_meta_4675.OrReachAPI

def appendStar (n : ℕ) (C : Circuit) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.and, [a, b]⟩, ⟨GateOp.or, [C.output, n + C.gates.length]⟩],
    n + C.gates.length + 1⟩

lemma appendStar_size (n : ℕ) (C : Circuit) (a b : ℕ) :
    (appendStar n C a b).size = C.size + 2 := by simp [appendStar, Circuit.size]

lemma gateAt_old (n : ℕ) (C : Circuit) (a b j : ℕ) (hj : j < C.gates.length) :
    gateAt (appendStar n C a b) j = gateAt C j := by
  exact gateAt_append_old C.gates _ j hj

lemma gateAt_and (n : ℕ) (C : Circuit) (a b : ℕ) :
    gateAt (appendStar n C a b) C.gates.length = ⟨GateOp.and, [a, b]⟩ := by
  simp [appendStar, gateAt, List.getD_eq_getElem?_getD]

lemma gateAt_output (n : ℕ) (C : Circuit) (a b : ℕ) :
    gateAt (appendStar n C a b) (C.gates.length + 1) =
      ⟨GateOp.or, [C.output, n + C.gates.length]⟩ := by
  simp [appendStar, gateAt, List.getD_eq_getElem?_getD]

lemma appendStar_ao (n : ℕ) (C : Circuit) (a b : ℕ) (hAO : IsAO2 n C)
    (ha : a < n + C.gates.length) (hb : b < n + C.gates.length)
    (ho : C.output < n + C.gates.length) : IsAO2 n (appendStar n C a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [appendStar, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact hAO.1 g hg
    · exact Or.inl rfl
    · exact Or.inr rfl
  · intro j hj w hw
    have hj' : j < C.gates.length + 2 := by simpa [appendStar] using hj
    by_cases hjold : j < C.gates.length
    · rw [gateAt_old n C a b j hjold] at hw
      exact hAO.2.1 j hjold w hw
    · by_cases hjand : j = C.gates.length
      · subst j
        rw [gateAt_and] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> assumption
      · have hjo : j = C.gates.length + 1 := by omega
        subst j
        rw [gateAt_output] at hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
        rcases hw with rfl | rfl <;> omega
  · intro g hg
    simp only [appendStar, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
    rcases hg with hg | rfl | rfl
    · exact hAO.2.2 g hg
    · rfl
    · rfl

lemma orIn_old (n : ℕ) (C : Circuit) (a b w : ℕ) (hw : w < n + C.gates.length) :
    orIn n (appendStar n C a b) w = orIn n C w :=
  orIn_append_prefix n C.gates _ w hw

lemma orIn_and (n : ℕ) (C : Circuit) (a b : ℕ) :
    orIn n (appendStar n C a b) (n + C.gates.length) = ∅ := by
  apply orIn_non_or n _ C.gates.length
  · simp [appendStar]
  · rw [gateAt_and]
    simp

lemma orIn_output (n : ℕ) (C : Circuit) (a b : ℕ) (hAO : IsAO2 n C)
    (ha : a < n + C.gates.length) (hb : b < n + C.gates.length)
    (ho : C.output < n + C.gates.length) :
    orIn n (appendStar n C a b) (n + C.gates.length + 1) = orIn n C C.output := by
  have hA := appendStar_ao n C a b hAO ha hb ho
  have he : n + C.gates.length + 1 = n + (C.gates.length + 1) := by omega
  rw [he, orIn_or_pair n _ (C.gates.length + 1) C.output (n + C.gates.length)]
  · rw [orIn_old n C a b C.output ho, orIn_and, Finset.union_empty]
  · simp [appendStar]
  · rw [gateAt_output]
  · rw [gateAt_output]
  · exact hA.2.1

lemma appendStar_tCount (n : ℕ) (C : Circuit) (a b : ℕ) (colour : ℕ → Bool)
    (hAO : IsAO2 n C) (ha : a < n + C.gates.length) (hb : b < n + C.gates.length)
    (ho : C.output < n + C.gates.length) (he : orIn n C C.output = ∅) :
    tCount n (appendStar n C a b) colour = tCount n C colour := by
  have hs : twoColour n (appendStar n C a b) colour = twoColour n C colour := by
    ext j
    simp only [twoColour, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hj, hjc⟩
      have hj' : j < C.gates.length + 2 := by simpa [appendStar] using hj
      by_cases hjo : j < C.gates.length
      · refine ⟨hjo, ?_⟩
        rcases hjc with ⟨_, hop, hp, hl⟩
        rw [gateAt_old n C a b j hjo] at hop
        rw [orIn_old n C a b (n + j) (by omega)] at hp hl
        exact ⟨hjo, hop, hp, hl⟩
      · by_cases hja : j = C.gates.length
        · subst j
          have hh := hjc.2.1
          rw [gateAt_and] at hh
          cases hh
        · have hje : j = C.gates.length + 1 := by omega
          subst j
          have hh := hjc.2.2.1
          have hro := orIn_output n C a b hAO ha hb ho
          have heq : n + (C.gates.length + 1) = n + C.gates.length + 1 := by omega
          rw [heq, hro, he] at hh
          simp at hh
    · rintro ⟨hj, _, hop, hp, hl⟩
      refine ⟨by simp [appendStar]; omega, by simp [appendStar]; omega, ?_, ?_, ?_⟩
      · rw [gateAt_old n C a b j hj]
        exact hop
      · rw [orIn_old n C a b (n + j) (by omega)]
        exact hp
      · rw [orIn_old n C a b (n + j) (by omega)]
        exact hl
  unfold tCount
  rw [hs]

lemma wires_length (C : Circuit) (xs : List Bool) :
    (C.wires xs).length = xs.length + C.gates.length := by
  have h : ∀ (gs : List Gate) (ws : List Bool),
      (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) ws).length =
        ws.length + gs.length := by
    intro gs
    induction gs with
    | nil => simp
    | cons g gs ih =>
      intro ws
      rw [List.foldl_cons, ih]
      simp
      omega
  exact h C.gates xs

lemma appendStar_eval (n : ℕ) (C : Circuit) (a b : ℕ) (xs : List Bool)
    (hx : xs.length = n) (ho : C.output < n + C.gates.length) :
    (appendStar n C a b).eval xs =
      (C.eval xs || ((C.wires xs).getD a false && (C.wires xs).getD b false)) := by
  let ws := C.wires xs
  let v := ws.getD a false && ws.getD b false
  have hw : ws.length = n + C.gates.length := by exact (wires_length C xs).trans (by rw [hx])
  have hp : (ws ++ [v]).getD C.output false = ws.getD C.output false := by
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left (by omega)]
  have hv : (ws ++ [v]).getD (n + C.gates.length) false = v := by
    rw [← hw]
    simp [List.getD_eq_getElem?_getD]
  have hl : (ws ++ [v]).length = n + C.gates.length + 1 := by simp [hw]
  have hout : ∀ t : Bool, ((ws ++ [v]) ++ [t]).getD (n + C.gates.length + 1) false = t := by
    intro t
    rw [← hl]
    simp [List.getD_eq_getElem?_getD]
  simp only [appendStar, Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons,
    List.foldl_nil, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
    List.any_cons, List.any_nil, Bool.and_true, Bool.or_false]
  change ((ws ++ [v]) ++ [(ws ++ [v]).getD C.output false ||
    (ws ++ [v]).getD (n + C.gates.length) false]).getD (n + C.gates.length + 1) false =
    (ws.getD C.output false || v)
  rw [hout, hp, hv]

end PEqualNP.Outside.L_meta_4675.StarAppend

namespace PEqualNP.Outside.L_meta_4675.StarAppendOptional

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.CleanedNonEdge
  PEqualNP.MetaComplexity.NestedCover PEqualNP.TwoColour
open PEqualNP.Outside.L_meta_4675.OrReachAPI
open PEqualNP.Outside.L_meta_4675.StarAppend

def appendAnd (n : ℕ) (C : Circuit) (a b : ℕ) : Circuit :=
  ⟨C.gates ++ [⟨GateOp.and, [a, b]⟩], n + C.gates.length⟩

def restoreStar (n : ℕ) (C : Circuit) (a b : ℕ) : Circuit :=
  if C.output < n + C.gates.length then appendStar n C a b else appendAnd n C a b

lemma appendAnd_gate (n : ℕ) (C : Circuit) (a b : ℕ) :
    gateAt (appendAnd n C a b) C.gates.length = ⟨GateOp.and, [a, b]⟩ := by
  simp [appendAnd, gateAt, List.getD_eq_getElem?_getD]

lemma appendAnd_ao (n : ℕ) (C : Circuit) (a b : ℕ) (hAO : IsAO2 n C)
    (ha : a < n + C.gates.length) (hb : b < n + C.gates.length) :
    IsAO2 n (appendAnd n C a b) := by
  refine ⟨?_, ?_, ?_⟩
  · intro g hg
    simp only [appendAnd, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO.1 g hg
    · exact Or.inl rfl
  · intro j hj w hw
    have hj' : j < C.gates.length + 1 := by simpa [appendAnd] using hj
    by_cases hjo : j < C.gates.length
    · have he : gateAt (appendAnd n C a b) j = gateAt C j := gateAt_append_old _ _ j hjo
      rw [he] at hw
      exact hAO.2.1 j hjo w hw
    · have he : j = C.gates.length := by omega
      subst j
      rw [appendAnd_gate] at hw
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
      rcases hw with rfl | rfl <;> assumption
  · intro g hg
    simp only [appendAnd, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact hAO.2.2 g hg
    · rfl

lemma appendAnd_tCount (n : ℕ) (C : Circuit) (a b : ℕ) (colour : ℕ → Bool) :
    tCount n (appendAnd n C a b) colour = tCount n C colour := by
  have hs : twoColour n (appendAnd n C a b) colour = twoColour n C colour := by
    ext j
    simp only [twoColour, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hj, hjc⟩
      have hj' : j < C.gates.length + 1 := by simpa [appendAnd] using hj
      have hjo : j < C.gates.length := by
        by_contra hno
        have he : j = C.gates.length := by omega
        subst j
        have hop := hjc.2.1
        rw [appendAnd_gate] at hop
        cases hop
      have hg : gateAt (appendAnd n C a b) j = gateAt C j := gateAt_append_old _ _ j hjo
      have hr : orIn n (appendAnd n C a b) (n+j) = orIn n C (n+j) :=
        orIn_append_prefix n C.gates _ (n+j) (by omega)
      rcases hjc with ⟨_, hop, hp, hl⟩
      rw [hg] at hop
      rw [hr] at hp hl
      exact ⟨hjo, hjo, hop, hp, hl⟩
    · rintro ⟨hj, _, hop, hp, hl⟩
      have hg : gateAt (appendAnd n C a b) j = gateAt C j := gateAt_append_old _ _ j hj
      have hr : orIn n (appendAnd n C a b) (n+j) = orIn n C (n+j) :=
        orIn_append_prefix n C.gates _ (n+j) (by omega)
      refine ⟨by simp [appendAnd]; omega, by simp [appendAnd]; omega, ?_, ?_, ?_⟩
      · rw [hg]; exact hop
      · rw [hr]; exact hp
      · rw [hr]; exact hl
  unfold tCount
  rw [hs]

lemma appendAnd_eval (n : ℕ) (C : Circuit) (a b : ℕ) (xs : List Bool) (hx : xs.length = n) :
    (appendAnd n C a b).eval xs =
      ((C.wires xs).getD a false && (C.wires xs).getD b false) := by
  have hl : (C.wires xs).length = n + C.gates.length := by rw [wires_length, hx]
  simp only [appendAnd, Circuit.eval, Circuit.wires, List.foldl_append, List.foldl_cons,
    List.foldl_nil, List.map_cons, List.map_nil, GateOp.eval, List.all_cons, List.all_nil,
    Bool.and_true]
  change (C.wires xs ++ [(C.wires xs).getD a false && (C.wires xs).getD b false]).getD
    (n + C.gates.length) false =
      ((C.wires xs).getD a false && (C.wires xs).getD b false)
  rw [← hl]
  simp [List.getD_eq_getElem?_getD]

lemma restoreStar_size (n : ℕ) (C : Circuit) (a b : ℕ) :
    (restoreStar n C a b).size ≤ C.size + 2 := by
  unfold restoreStar
  split_ifs
  · rw [appendStar_size]
  · simp [appendAnd, Circuit.size]

lemma restoreStar_ao (n : ℕ) (C : Circuit) (a b : ℕ) (hAO : IsAO2 n C)
    (ha : a < n + C.gates.length) (hb : b < n + C.gates.length) :
    IsAO2 n (restoreStar n C a b) := by
  unfold restoreStar
  split_ifs with ho
  · exact appendStar_ao n C a b hAO ha hb ho
  · exact appendAnd_ao n C a b hAO ha hb

lemma restoreStar_tCount (n : ℕ) (C : Circuit) (a b : ℕ) (colour : ℕ → Bool)
    (hAO : IsAO2 n C) (ha : a < n + C.gates.length) (hb : b < n + C.gates.length)
    (he : orIn n C C.output = ∅) :
    tCount n (restoreStar n C a b) colour = tCount n C colour := by
  unfold restoreStar
  split_ifs with ho
  · exact appendStar_tCount n C a b colour hAO ha hb ho he
  · exact appendAnd_tCount n C a b colour

lemma restoreStar_eval (n : ℕ) (C : Circuit) (a b : ℕ) (xs : List Bool) (hx : xs.length = n) :
    (restoreStar n C a b).eval xs =
      (C.eval xs || ((C.wires xs).getD a false && (C.wires xs).getD b false)) := by
  unfold restoreStar
  split_ifs with ho
  · exact appendStar_eval n C a b xs hx ho
  · have hz : C.eval xs = false := by
      unfold Circuit.eval
      simp only [List.getD_eq_getElem?_getD]
      rw [List.getElem?_eq_none (by rw [wires_length, hx]; omega)]
      rfl
    rw [hz, Bool.false_or]
    exact appendAnd_eval n C a b xs hx

end PEqualNP.Outside.L_meta_4675.StarAppendOptional
