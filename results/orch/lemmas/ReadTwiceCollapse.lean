import Mathlib
import PEqualNP.Defs
import PEqualNP.Outside.L_meta_7493

namespace PEqualNP.Outside.L_meta_2592_aux.ReadTwiceCollapse

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_7493.CircuitProof
open PEqualNP.Outside.L_meta_7493.CircuitProof.Readers

def originStep (origins : List ℕ) (g : Gate) : List ℕ :=
  origins ++ [if isNotGate g.op then origins.getD (g.inputs.getD 0 0) 0 else origins.length]

def origins (n : ℕ) (gs : List Gate) : List ℕ := gs.foldl originStep (List.range n)

def origin (n : ℕ) (gs : List Gate) (w : ℕ) : ℕ := (origins n gs).getD w 0

lemma step_prefix (gs : List Gate) (initial : List ℕ) : initial <+: gs.foldl originStep initial := by
  induction gs generalizing initial with
  | nil => exact List.prefix_refl _
  | cons g gs ih => exact (List.prefix_append initial _).trans (ih _)

lemma step_length (gs : List Gate) (initial : List ℕ) :
    (gs.foldl originStep initial).length = initial.length + gs.length := by
  induction gs generalizing initial with
  | nil => simp
  | cons g gs ih => simp [List.foldl_cons, ih, originStep]; omega

lemma prefix_get {a b : List ℕ} (pref : a <+: b) {i : ℕ} (hi : i < a.length) :
    b.getD i 0 = a.getD i 0 := by
  obtain ⟨tail, rfl⟩ := pref
  exact List.getD_append a tail 0 i hi

lemma origin_input (n : ℕ) (gs : List Gate) (w : ℕ) (hw : w < n) :
    origin n gs w = w := by
  unfold origin origins
  rw [prefix_get (step_prefix gs (List.range n)) (by simpa using hw)]
  simp [List.getD_eq_getElem?_getD, hw]

lemma origin_gate (n : ℕ) (gs : List Gate) (clean : CleanL n gs)
    (j : ℕ) (g : Gate) (atGate : gs[j]? = some g) :
    origin n gs (n + j) =
      if isNotGate g.op then origin n gs (g.inputs.getD 0 0) else n + j := by
  have hj := (List.getElem?_eq_some_iff.mp atGate).1
  have hg : gs[j] = g := (List.getElem?_eq_some_iff.mp atGate).2
  have split : gs = gs.take j ++ g :: gs.drop (j + 1) := by
    have base : gs = gs.take j ++ gs[j] :: gs.drop (j + 1) := by simp
    simpa only [hg] using base
  let pre := (gs.take j).foldl originStep (List.range n)
  have preLength : pre.length = n + j := by
    simp only [pre, step_length, List.length_range, List.length_take]
    omega
  have pref : originStep pre g <+: origins n gs := by
    unfold origins
    conv_rhs => rw [split]
    rw [List.foldl_append, List.foldl_cons]
    exact step_prefix _ _
  have shorter : pre <+: origins n gs := (List.prefix_append pre _).trans pref
  unfold origin
  rw [prefix_get pref (by simp [originStep, preLength])]
  rw [show n + j = pre.length from preLength.symm]
  unfold originStep
  rw [List.getD_append_right _ _ _ _ (Nat.le_refl _), Nat.sub_self, List.getD_cons_zero]
  split_ifs with flag
  · have op : g.op = GateOp.not := by
      cases ho : g.op <;> simp only [ho, isNotGate] at flag
      all_goals try cases flag
      rfl
    have inp : ∃ i, i < n + j ∧ g.inputs = [i] := by
      rcases clean j g atGate with ⟨_, h⟩ | ⟨h, _⟩
      · exact h
      · rcases h with h | h <;> rw [op] at h <;> cases h
    obtain ⟨i, bound, shape⟩ := inp
    simp only [shape, List.getD_cons_zero]
    exact (prefix_get shorter (i := i) (by omega)).symm
  · rfl

def binaryIndices (gs : List Gate) : Finset (Fin gs.length) :=
  Finset.univ.filter (fun j => isNotGate (gs.get j).op = false)

def slots (gs : List Gate) : Finset (Fin gs.length × Fin 2) :=
  (binaryIndices gs).product Finset.univ

def slotOrigin (n : ℕ) (gs : List Gate) (s : Fin gs.length × Fin 2) : ℕ :=
  origin n gs ((gs.get s.1).inputs.getD s.2.val 0)

def internalOrigins (n : ℕ) (gs : List Gate) : Finset ℕ :=
  (binaryIndices gs).image (fun j => n + j.val)

lemma binary_read_slot (n : ℕ) (gs : List Gate) (clean : CleanL n gs)
    (q w : ℕ) (g : Gate) (atGate : gs[q]? = some g)
    (binary : isNotGate g.op = false) (read : w ∈ g.inputs) :
    ∃ s ∈ slots gs, slotOrigin n gs s = origin n gs w := by
  have qbound := (List.getElem?_eq_some_iff.mp atGate).1
  have gateEq : gs[q] = g := (List.getElem?_eq_some_iff.mp atGate).2
  have shape : ∃ a b, g.inputs = [a,b] := by
    rcases clean q g atGate with ⟨op, _⟩ | ⟨_, a, b, _, _, inputs⟩
    · simp [op, isNotGate] at binary
    · exact ⟨a,b,inputs⟩
  obtain ⟨a,b,inputs⟩ := shape
  have index : (⟨q,qbound⟩ : Fin gs.length) ∈ binaryIndices gs := by
    simp [binaryIndices, gateEq, binary]
  rcases (by simpa [inputs] using read : w = a ∨ w = b) with rfl | rfl
  · exact ⟨(⟨q,qbound⟩,0), by simp [slots,index], by simp [slotOrigin,gateEq,inputs]⟩
  · exact ⟨(⟨q,qbound⟩,1), by simp [slots,index], by simp [slotOrigin,gateEq,inputs]⟩

lemma origin_reaches_slot (n : ℕ) (gs : List Gate) (out : ℕ) (clean : CleanL n gs)
    (live : ∀ j, j < gs.length → out ≠ n + j → ∃ q, j < q ∧ Reads gs q (n + j))
    (j : ℕ) (hj : j < gs.length) :
    origin n gs (n + j) = origin n gs out ∨
      ∃ s ∈ slots gs, slotOrigin n gs s = origin n gs (n + j) := by
  suffices aux : ∀ r j, gs.length - j = r → j < gs.length →
      origin n gs (n + j) = origin n gs out ∨
        ∃ s ∈ slots gs, slotOrigin n gs s = origin n gs (n + j) by
    exact aux _ j rfl hj
  intro r
  induction r using Nat.strong_induction_on with
  | ind r ih =>
    intro j measure hj
    by_cases output : out = n + j
    · exact Or.inl (congrArg (origin n gs) output.symm)
    obtain ⟨q, later, g, atGate, read⟩ := live j hj output
    have hq := (List.getElem?_eq_some_iff.mp atGate).1
    cases flag : isNotGate g.op with
    | false => exact Or.inr (binary_read_slot n gs clean q (n + j) g atGate flag read)
    | true =>
      have op : g.op = GateOp.not := by cases ho : g.op <;> simp_all [isNotGate]
      have inp : ∃ i, i < n + q ∧ g.inputs = [i] := by
        rcases clean q g atGate with ⟨_, h⟩ | ⟨h, _⟩
        · exact h
        · rcases h with h | h <;> simp_all
      obtain ⟨i, _, shape⟩ := inp
      have equal : n + j = i := by simpa [shape] using read
      have copied : origin n gs (n + q) = origin n gs (n + j) := by
        rw [origin_gate n gs clean q g atGate, flag]
        simp [shape, equal]
      have next := ih (gs.length - q) (by omega) q rfl hq
      simpa [copied] using next

lemma internal_productive (n : ℕ) (gs : List Gate) (out : ℕ) (clean : CleanL n gs)
    (live : ∀ j, j < gs.length → out ≠ n + j → ∃ q, j < q ∧ Reads gs q (n + j)) :
    ∀ w ∈ internalOrigins n gs,
      w = origin n gs out ∨ ∃ s ∈ slots gs, slotOrigin n gs s = w := by
  intro w hw
  obtain ⟨j, member, rfl⟩ := Finset.mem_image.mp hw
  have binary : isNotGate (gs.get j).op = false := (Finset.mem_filter.mp member).2
  have born : origin n gs (n + j.val) = n + j.val := by
    rw [origin_gate n gs clean j.val (gs.get j) (by simp), binary]
    rfl
  simpa [born] using origin_reaches_slot n gs out clean live j.val j.isLt

lemma internal_card (n : ℕ) (gs : List Gate) :
    (internalOrigins n gs).card = (binaryIndices gs).card := by
  apply Finset.card_image_iff.mpr
  intro a _ b _ equal
  apply Fin.ext
  change n + a.val = n + b.val at equal
  omega

lemma collapsed_primary_budget (n : ℕ) (gs : List Gate) (out : ℕ) (clean : CleanL n gs)
    (live : ∀ j, j < gs.length → out ≠ n + j → ∃ q, j < q ∧ Reads gs q (n + j)) :
    ((slots gs).filter (fun s => slotOrigin n gs s < n)).card ≤ (binaryIndices gs).card + 1 := by
  let inside := (slots gs).filter (fun s => n ≤ slotOrigin n gs s)
  have contain : internalOrigins n gs ⊆ insert (origin n gs out) (inside.image (slotOrigin n gs)) := by
    intro w hw
    rcases internal_productive n gs out clean live w hw with equal | ⟨s, hs, equal⟩
    · simp [equal]
    · apply Finset.mem_insert_of_mem
      apply Finset.mem_image.mpr
      refine ⟨s, ?_, equal⟩
      have above : n ≤ w := by
        obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hw
        omega
      exact Finset.mem_filter.mpr ⟨hs, by omega⟩
  have cover := Finset.card_le_card contain
  have extra := Finset.card_insert_le (origin n gs out) (inside.image (slotOrigin n gs))
  have imageBound := Finset.card_image_le (s := inside) (f := slotOrigin n gs)
  have partition : ((slots gs).filter (fun s => slotOrigin n gs s < n)).card + inside.card =
      (slots gs).card := by
    simpa [inside, Nat.not_lt] using
      Finset.card_filter_add_card_filter_not (s := slots gs) (p := fun s => slotOrigin n gs s < n)
  have capacity : (slots gs).card = (binaryIndices gs).card * 2 := by simp [slots]
  rw [internal_card] at cover
  omega

end PEqualNP.Outside.L_meta_2592_aux.ReadTwiceCollapse
