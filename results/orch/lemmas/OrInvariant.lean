import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4675.OrInvariant

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
  PEqualNP.CleanedNonEdge PEqualNP.TopForm PEqualNP.TwoColour

def SameOr (g h : Gate) : Prop :=
  g.op = h.op ∧ (g.op = GateOp.or → g.inputs = h.inputs)

lemma sameOr_refl (g : Gate) : SameOr g g := ⟨rfl, fun _ => rfl⟩

lemma sameOr_symm {g h : Gate} (heq : SameOr g h) : SameOr h g := by
  refine ⟨heq.1.symm, ?_⟩
  intro hop
  exact (heq.2 (heq.1.trans hop)).symm

lemma step_eq (n : ℕ) (cs : List (List ℕ)) {g h : Gate} (heq : SameOr g h) :
    orStep n cs g = orStep n cs h := by
  by_cases hop : g.op = GateOp.or
  · have hop' : h.op = GateOp.or := heq.1.symm.trans hop
    simp only [orStep, hop, hop', ↓reduceIte, heq.2 hop]
  · have hop' : h.op ≠ GateOp.or := fun hh => hop (heq.1.trans hh)
    simp only [orStep, hop, hop', ↓reduceIte]

lemma fold_eq (n : ℕ) {gs hs : List Gate} (heq : List.Forall₂ SameOr gs hs)
    (cs : List (List ℕ)) : gs.foldl (orStep n) cs = hs.foldl (orStep n) cs := by
  induction heq generalizing cs with
  | nil => rfl
  | cons hhead htail ih =>
    simp only [List.foldl_cons]
    rw [step_eq n cs hhead]
    exact ih _

lemma getD_same {gs hs : List Gate} (heq : List.Forall₂ SameOr gs hs)
    (j : ℕ) : SameOr (gs.getD j ⟨GateOp.or, []⟩) (hs.getD j ⟨GateOp.or, []⟩) := by
  induction heq generalizing j with
  | nil => simpa using sameOr_refl ⟨GateOp.or, []⟩
  | cons hhead htail ih =>
    cases j with
    | zero => simpa using hhead
    | succ j => simpa using ih j

lemma orSets_eq (n : ℕ) {C D : Circuit} (heq : List.Forall₂ SameOr C.gates D.gates) :
    orSets n C = orSets n D := fold_eq n heq []

lemma reaches_iff (n : ℕ) {C D : Circuit} (heq : List.Forall₂ SameOr C.gates D.gates)
    (w j : ℕ) : OrReaches n C w j ↔ OrReaches n D w j := by
  simp only [OrReaches, orSets_eq n heq]

lemma orIn_subset (n : ℕ) {C D : Circuit} (heq : List.Forall₂ SameOr C.gates D.gates)
    (w : ℕ) : orIn n C w ⊆ orIn n D w := by
  intro i hi
  simp only [orIn, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
  rcases hi with hinput | ⟨j, hj, hreach, hop, hin⟩
  · exact Or.inl hinput
  · have hgate : SameOr (gateAt C j) (gateAt D j) := getD_same heq j
    refine Or.inr ⟨j, ?_, (reaches_iff n heq w j).1 hreach, hgate.1.symm.trans hop, ?_⟩
    · rwa [← heq.length_eq]
    · rwa [← hgate.2 hop]

lemma orIn_eq (n : ℕ) {C D : Circuit} (heq : List.Forall₂ SameOr C.gates D.gates)
    (w : ℕ) : orIn n C w = orIn n D w := by
  apply Finset.Subset.antisymm (orIn_subset n heq w)
  exact orIn_subset n (heq.flip.imp (fun _ _ h => sameOr_symm h)) w

lemma twoColour_iff (n : ℕ) {C D : Circuit} (heq : List.Forall₂ SameOr C.gates D.gates)
    (colour : ℕ → Bool) (j : ℕ) :
    IsTwoColour n C colour j ↔ IsTwoColour n D colour j := by
  have hgate : SameOr (gateAt C j) (gateAt D j) := getD_same heq j
  simp only [IsTwoColour, heq.length_eq, hgate.1, orIn_eq n heq]

lemma tCount_eq (n : ℕ) {C D : Circuit} (heq : List.Forall₂ SameOr C.gates D.gates)
    (colour : ℕ → Bool) : tCount n C colour = tCount n D colour := by
  unfold tCount twoColour
  congr 1
  ext j
  simp only [Finset.mem_filter, Finset.mem_range, heq.length_eq, twoColour_iff n heq]

end PEqualNP.Outside.L_meta_4675.OrInvariant
