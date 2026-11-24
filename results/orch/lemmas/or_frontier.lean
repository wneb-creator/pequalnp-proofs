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
