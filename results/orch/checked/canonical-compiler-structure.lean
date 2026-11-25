import CanonicalCompilerDefs

namespace PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def emittedOr (g : Gate) : Bool :=
  match g.op with
  | .or => true
  | _ => false

lemma conjunction_legal (offset : Nat) (wires : List Nat) :
    ∀ g ∈ conjunction offset wires,
      g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction wires with
  | nil => simp [conjunction]
  | cons wire wires ih =>
    intro g hg
    simp only [conjunction, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | rfl
    · exact ih g hg
    · simp

lemma conjunction_or_count (offset : Nat) (wires : List Nat) :
    (conjunction offset wires).countP emittedOr = 0 := by
  induction wires with
  | nil => rfl
  | cons wire wires ih => simp [conjunction, List.countP_append, emittedOr, ih]

lemma compile_monotone2 {n : Nat} (k : Nat) (program : Program n k)
    (offset : Nat) (refs : Fin n → Nat) : Monotone2 (compile k program offset refs) := by
  induction k generalizing n offset with
  | zero => exact conjunction_legal offset (program.map refs)
  | succ k ih =>
    intro g hg
    simp only [compile, List.mem_append, List.mem_cons, List.not_mem_nil, false_or, or_assoc] at hg
    rcases hg with hl | hr | ho | ht
    · exact conjunction_legal _ _ g hl
    · exact conjunction_legal _ _ g hr
    · subst g
      simp
    · exact (ih (n := n + 1) program.2 _ _) g ht

lemma compile_or_count {n : Nat} (k : Nat) (program : Program n k)
    (offset : Nat) (refs : Fin n → Nat) :
    (compile k program offset refs).gates.countP emittedOr = k := by
  induction k generalizing n offset with
  | zero => exact conjunction_or_count offset (program.map refs)
  | succ k ih =>
    simp [compile, List.countP_append, List.countP_cons, conjunction_or_count, emittedOr, ih, Nat.add_comm]

lemma emittedOr_count_filter (gs : List Gate) :
    (Finset.univ.filter (fun i : Fin gs.length => emittedOr (gs.get i) = true)).card =
      gs.countP emittedOr := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    show (Finset.univ.filter
      (fun i : Fin (gs.length + 1) => emittedOr ((g :: gs).get i) = true)).card = _
    rw [Fin.card_filter_univ_succ]
    simp only [List.countP_cons]
    split_ifs with h₁ h₂ h₂
    · simpa using ih
    · exact absurd h₁ h₂
    · exact absurd h₂ h₁
    · simpa using ih

lemma emittedOr_count_ncard (gs : List Gate) :
    {i : Fin gs.length | (gs.get i).op = GateOp.or}.ncard = gs.countP emittedOr := by
  have he : {i : Fin gs.length | (gs.get i).op = GateOp.or} =
      ↑(Finset.univ.filter (fun i : Fin gs.length => emittedOr (gs.get i) = true)) := by
    ext i
    simp only [Set.mem_ofPred_eq, Finset.coe_filter, Finset.mem_univ, true_and]
    unfold emittedOr
    cases (gs.get i).op <;> simp
  rw [he, Set.ncard_coe_finset, emittedOr_count_filter]

lemma compile_or_ncard {n : Nat} (k : Nat) (program : Program n k)
    (offset : Nat) (refs : Fin n → Nat) :
    {i : Fin (compile k program offset refs).gates.length |
      ((compile k program offset refs).gates.get i).op = GateOp.or}.ncard = k := by
  rw [emittedOr_count_ncard, compile_or_count]

lemma compile_or_ncard_getElem {n : Nat} (k : Nat) (program : Program n k)
    (offset : Nat) (refs : Fin n → Nat) :
    {i : Fin (compile k program offset refs).gates.length |
      ((compile k program offset refs).gates[i]).op = GateOp.or}.ncard = k := by
  simpa only [List.get_eq_getElem, Fin.getElem_fin] using compile_or_ncard k program offset refs

end PEqualNP.Outside.L_meta_1896_aux.CanonicalCompiler
