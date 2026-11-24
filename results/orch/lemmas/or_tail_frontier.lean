import PEqualNP.Outside.L_meta_3451

namespace PEqualNP.Outside.L_meta_3451

def ofExpand (S : Finset ℕ) (w : ℕ) (ins : List ℕ) : Finset ℕ :=
  if w ∈ S then S.erase w ∪ ins.toFinset else S

noncomputable def ofAny (val : ℕ → Bool) (S : Finset ℕ) : Bool :=
  S.toList.any val

lemma ofAny_true (val : ℕ → Bool) (S : Finset ℕ) :
    ofAny val S = true ↔ ∃ w ∈ S, val w = true := by
  simp [ofAny, List.any_eq_true]

lemma ofExpand_card (S : Finset ℕ) (w : ℕ) (ins : List ℕ)
    (hbin : ins.length ≤ 2) :
    (ofExpand S w ins).card ≤ S.card + if w ∈ S then 1 else 0 := by
  by_cases hw : w ∈ S
  · rw [ofExpand, ite_eq_left hw, ite_eq_left hw]
    have he := Finset.card_erase_add_one hw
    have hu := Finset.card_union_le (S.erase w) ins.toFinset
    have hi := ins.toFinset_card_le
    omega
  · simp [ofExpand, hw]

lemma ofExpand_card_le (S : Finset ℕ) (w : ℕ) (ins : List ℕ)
    (hbin : ins.length ≤ 2) :
    (ofExpand S w ins).card ≤ S.card + 1 := by
  have h := ofExpand_card S w ins hbin
  split_ifs at h <;> omega

lemma ofExpand_semantics (val : ℕ → Bool) (S : Finset ℕ)
    (w : ℕ) (ins : List ℕ) (hw : val w = ins.any val) :
    ofAny val S = ofAny val (ofExpand S w ins) := by
  rw [Bool.eq_iff_iff, ofAny_true, ofAny_true]
  by_cases hmem : w ∈ S
  · rw [ofExpand, ite_eq_left hmem]
    constructor
    · rintro ⟨v, hv, hvtrue⟩
      by_cases hvw : v = w
      · subst v
        rw [hw, List.any_eq_true] at hvtrue
        obtain ⟨a, ha, hatrue⟩ := hvtrue
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.mpr ha), hatrue⟩
      · exact ⟨v, Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hvw, hv⟩), hvtrue⟩
    · rintro ⟨v, hv, hvtrue⟩
      rcases Finset.mem_union.mp hv with hv | hv
      · exact ⟨v, (Finset.mem_erase.mp hv).2, hvtrue⟩
      · refine ⟨w, hmem, ?_⟩
        rw [hw, List.any_eq_true]
        exact ⟨v, List.mem_toFinset.mp hv, hvtrue⟩
  · simp [ofExpand, hmem]

def ofRun : List (ℕ × List ℕ) → Finset ℕ → Finset ℕ
  | [], S => S
  | (w, ins) :: rest, S => ofRun rest (ofExpand S w ins)

def ofCost : List (ℕ × List ℕ) → Finset ℕ → ℕ
  | [], _ => 0
  | (w, ins) :: rest, S =>
      (if w ∈ S then 1 else 0) + ofCost rest (ofExpand S w ins)

lemma ofRun_card (steps : List (ℕ × List ℕ))
    (hbin : ∀ e ∈ steps, e.2.length ≤ 2) (S : Finset ℕ) :
    (ofRun steps S).card ≤ S.card + ofCost steps S := by
  induction steps generalizing S with
  | nil => simp [ofRun, ofCost]
  | cons e rest ih =>
    obtain ⟨w, ins⟩ := e
    have hstep := ofExpand_card S w ins (hbin (w, ins) (by simp))
    have hrest := ih (fun e he => hbin e (by simp [he])) (ofExpand S w ins)
    simp only [ofRun, ofCost]
    omega

lemma ofCost_le_length (steps : List (ℕ × List ℕ)) (S : Finset ℕ) :
    ofCost steps S ≤ steps.length := by
  induction steps generalizing S with
  | nil => simp [ofCost]
  | cons e rest ih =>
    obtain ⟨w, ins⟩ := e
    have hrest := ih (ofExpand S w ins)
    simp only [ofCost, List.length_cons]
    split_ifs <;> omega

lemma ofRun_semantics (val : ℕ → Bool) (steps : List (ℕ × List ℕ))
    (heq : ∀ e ∈ steps, val e.1 = e.2.any val) (S : Finset ℕ) :
    ofAny val S = ofAny val (ofRun steps S) := by
  induction steps generalizing S with
  | nil => rfl
  | cons e rest ih =>
    obtain ⟨w, ins⟩ := e
    exact (ofExpand_semantics val S w ins (heq (w, ins) (by simp))).trans
      (ih (fun e he => heq e (by simp [he])) (ofExpand S w ins))

lemma ofRun_singleton_card (steps : List (ℕ × List ℕ))
    (hbin : ∀ e ∈ steps, e.2.length ≤ 2) (output : ℕ) :
    (ofRun steps {output}).card ≤ ofCost steps {output} + 1 ∧
      (ofRun steps {output}).card ≤ steps.length + 1 := by
  have hc := ofRun_card steps hbin {output}
  have hl := ofCost_le_length steps {output}
  simp only [Finset.card_singleton] at hc
  omega

lemma ofRun_singleton_semantics (val : ℕ → Bool) (steps : List (ℕ × List ℕ))
    (heq : ∀ e ∈ steps, val e.1 = e.2.any val) (output : ℕ) :
    val output = ofAny val (ofRun steps {output}) := by
  simpa [ofAny] using ofRun_semantics val steps heq {output}

end PEqualNP.Outside.L_meta_3451

namespace PEqualNP.Outside.L_meta_3451

open CircuitLowerBounds MetaComplexity NestedCover

noncomputable def otSteps (n : ℕ) (C : Circuit) (p : ℕ) : ℕ → List (ℕ × List ℕ)
  | 0 => []
  | m + 1 => by
      classical
      exact if (gateAt C (p + m)).op = GateOp.or then
        (n + (p + m), (gateAt C (p + m)).inputs) :: otSteps n C p m
      else otSteps n C p m

lemma otSteps_spec (n : ℕ) (C : Circuit) (p m : ℕ) :
    ∀ e ∈ otSteps n C p m, ∃ k, p ≤ k ∧ k < p + m ∧
      (gateAt C k).op = GateOp.or ∧ e = (n + k, (gateAt C k).inputs) := by
  classical
  induction m with
  | zero => simp [otSteps]
  | succ m ih =>
    intro e he
    by_cases hop : (gateAt C (p + m)).op = GateOp.or
    · simp only [otSteps, ite_eq_left hop, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨p + m, by omega, by omega, hop, rfl⟩
      · obtain ⟨k, hk, hkm, hko, heq⟩ := ih e he
        exact ⟨k, hk, by omega, hko, heq⟩
    · rw [otSteps, ite_eq_right hop] at he
      obtain ⟨k, hk, hkm, hko, heq⟩ := ih e he
      exact ⟨k, hk, by omega, hko, heq⟩

open Classical in
lemma otSteps_length (n : ℕ) (C : Circuit) (p m : ℕ) :
    (otSteps n C p m).length =
      ((Finset.range m).filter fun j => (gateAt C (p + j)).op = GateOp.or).card := by
  classical
  induction m with
  | zero => simp [otSteps]
  | succ m ih =>
    by_cases hop : (gateAt C (p + m)).op = GateOp.or
    · simp [otSteps, hop, Finset.range_add_one, Finset.filter_insert, ih]
    · simp [otSteps, hop, Finset.range_add_one, Finset.filter_insert, ih]

lemma otRun_roots (n : ℕ) (C : Circuit) (hm : Monotone2 C) (hr : ReadsBack n C)
    (p m : ℕ) (hpm : p + m ≤ C.gates.length) (S : Finset ℕ) :
    ∀ w ∈ ofRun (otSteps n C p m) S,
      w < n + p ∨
      (∃ k, p ≤ k ∧ k < p + m ∧ (gateAt C k).op = GateOp.and ∧ w = n + k) ∨
      (w ∈ S ∧ n + (p + m) ≤ w) := by
  classical
  induction m generalizing S with
  | zero =>
    intro w hw
    simp only [otSteps, ofRun] at hw
    by_cases h : w < n + p
    · exact Or.inl h
    · exact Or.inr (Or.inr ⟨hw, by omega⟩)
  | succ m ih =>
    have hk : p + m < C.gates.length := by omega
    intro w hw
    by_cases hop : (gateAt C (p + m)).op = GateOp.or
    · simp only [otSteps, ite_eq_left hop, ofRun] at hw
      obtain hlow | hmid | hhigh := ih (by omega) _ w hw
      · exact Or.inl hlow
      · obtain ⟨k, hk1, hk2, hka, hwe⟩ := hmid
        exact Or.inr (Or.inl ⟨k, hk1, by omega, hka, hwe⟩)
      · obtain ⟨hmem, hbound⟩ := hhigh
        by_cases hactive : n + (p + m) ∈ S
        · rw [ofExpand, ite_eq_left hactive] at hmem
          rcases Finset.mem_union.mp hmem with hold | hins
          · obtain ⟨hne, hws⟩ := Finset.mem_erase.mp hold
            exact Or.inr (Or.inr ⟨hws, by omega⟩)
          · have hlt := hr (p + m) hk w (List.mem_toFinset.mp hins)
            omega
        · rw [ofExpand, ite_eq_right hactive] at hmem
          have hne : w ≠ n + (p + m) := by
            intro he
            exact hactive (he ▸ hmem)
          exact Or.inr (Or.inr ⟨hmem, by omega⟩)
    · rw [otSteps, ite_eq_right hop] at hw
      obtain hlow | hmid | hhigh := ih (by omega) _ w hw
      · exact Or.inl hlow
      · obtain ⟨k, hk1, hk2, hka, hwe⟩ := hmid
        exact Or.inr (Or.inl ⟨k, hk1, by omega, hka, hwe⟩)
      · obtain ⟨hmem, hbound⟩ := hhigh
        by_cases he : w = n + (p + m)
        · have hgate : gateAt C (p + m) ∈ C.gates := by
            unfold gateAt
            rw [List.getD_eq_getElem _ _ hk]
            exact List.getElem_mem hk
          have hand : (gateAt C (p + m)).op = GateOp.and := by
            have hh := (hm _ hgate).1
            exact hh.resolve_right hop
          exact Or.inr (Or.inl ⟨p + m, by omega, by omega, hand, he⟩)
        · exact Or.inr (Or.inr ⟨hmem, by omega⟩)

noncomputable def otFrontier (n : ℕ) (C : Circuit) (p : ℕ) : Finset ℕ :=
  ofRun (otSteps n C p (C.gates.length - p)) {C.output}

lemma otFrontier_roots (n : ℕ) (C : Circuit) (hm : Monotone2 C) (hr : ReadsBack n C)
    (p : ℕ) (hp : p ≤ C.gates.length) (hout : C.output < n + C.gates.length) :
    ∀ w ∈ otFrontier n C p, w < n + p ∨
      ∃ k, p ≤ k ∧ k < C.gates.length ∧ (gateAt C k).op = GateOp.and ∧ w = n + k := by
  intro w hw
  obtain hlow | hmid | hhigh := otRun_roots n C hm hr p (C.gates.length - p)
    (by omega) {C.output} w hw
  · exact Or.inl hlow
  · obtain ⟨k, hk1, hk2, hka, hwe⟩ := hmid
    exact Or.inr ⟨k, hk1, by omega, hka, hwe⟩
  · obtain ⟨hmem, hbound⟩ := hhigh
    simp only [Finset.mem_singleton] at hmem
    omega

open Classical in
lemma otFrontier_card (n : ℕ) (C : Circuit) (hm : Monotone2 C)
    (p : ℕ) (hp : p ≤ C.gates.length) :
    (otFrontier n C p).card ≤
      ((Finset.range (C.gates.length - p)).filter
        fun j => (gateAt C (p + j)).op = GateOp.or).card + 1 := by
  classical
  have hbin : ∀ e ∈ otSteps n C p (C.gates.length - p), e.2.length ≤ 2 := by
    intro e he
    obtain ⟨k, hk1, hk2, hko, rfl⟩ := otSteps_spec n C p _ e he
    have hk : k < C.gates.length := by omega
    have hgate : gateAt C k ∈ C.gates := by
      unfold gateAt
      rw [List.getD_eq_getElem _ _ hk]
      exact List.getElem_mem hk
    exact (hm _ hgate).2
  have hc := (ofRun_singleton_card (otSteps n C p (C.gates.length - p)) hbin C.output).2
  rw [otSteps_length] at hc
  exact hc

lemma otFrontier_semantics (n : ℕ) (C : Circuit) (hr : ReadsBack n C)
    (p : ℕ) (hp : p ≤ C.gates.length) (z : Fin n → Bool) :
    circuitFun n C z =
      ofAny (fun w => (C.wires (List.ofFn z)).getD w false) (otFrontier n C p) := by
  refine ofRun_singleton_semantics (fun w => (C.wires (List.ofFn z)).getD w false)
    (otSteps n C p (C.gates.length - p)) ?_ C.output
  intro e he
  obtain ⟨k, hk1, hk2, hko, rfl⟩ := otSteps_spec n C p _ e he
  have hk : k < C.gates.length := by omega
  have hg := frGateEval n C hr k hk z
  simpa [hko, GateOp.eval, List.any_map] using hg

lemma otFrontier_safe (n : ℕ) (C : Circuit) (hr : ReadsBack n C)
    (p : ℕ) (hp : p ≤ C.gates.length) (w : ℕ) (hw : w ∈ otFrontier n C p)
    (z : Fin n → Bool) (hz : (C.wires (List.ofFn z)).getD w false = true) :
    circuitFun n C z = true := by
  rw [otFrontier_semantics n C hr p hp z, ofAny_true]
  exact ⟨w, hw, hz⟩

end PEqualNP.Outside.L_meta_3451
