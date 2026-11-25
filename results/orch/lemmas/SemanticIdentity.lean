import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

private def copyInput (i : ℕ) : Gate := ⟨.and, [i, i]⟩

private def shiftGate (n : ℕ) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (n + ·)⟩

def hideInputs (n : ℕ) (C : Circuit) : Circuit :=
  ⟨(List.range n).map copyInput ++ C.gates.map (shiftGate n), n + C.output⟩

lemma hideInputs_size (n : ℕ) (C : Circuit) : (hideInputs n C).size = n + C.size := by
  simp [hideInputs, Circuit.size]

private def runGates (gs : List Gate) (xs : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) xs

private lemma runGates_shift (pre xs : List Bool) (gs : List Gate) :
    runGates (gs.map (shiftGate pre.length)) (pre ++ xs) = pre ++ runGates gs xs := by
  induction gs generalizing xs with
  | nil => simp [runGates]
  | cons g gs ih =>
      have hmap : (g.inputs.map (pre.length + ·)).map
          (fun i => (pre ++ xs).getD i false) =
          g.inputs.map (fun i => xs.getD i false) := by
        simp only [List.map_map]
        apply List.map_congr_left
        intro i hi
        change (pre ++ xs).getD (pre.length + i) false = xs.getD i false
        rw [List.getD_append_right _ _ _ _ (by omega)]
        simp
      change runGates (gs.map (shiftGate pre.length))
        ((pre ++ xs) ++ [(shiftGate pre.length g).op.eval
          ((shiftGate pre.length g).inputs.map (fun i => (pre ++ xs).getD i false))]) =
        pre ++ runGates gs (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)])
      simp only [shiftGate, hmap, List.append_assoc]
      exact ih _

private lemma runGates_copy (xs acc : List Bool) (is : List ℕ)
    (h : ∀ i ∈ is, i < xs.length) :
    runGates (is.map copyInput) (xs ++ acc) =
      (xs ++ acc) ++ is.map (fun i => xs.getD i false) := by
  induction is generalizing acc with
  | nil => simp [runGates]
  | cons i is ih =>
      have hi := h i (by simp)
      have ht : ∀ j ∈ is, j < xs.length := fun j hj => h j (by simp [hj])
      change runGates (is.map copyInput)
          ((xs ++ acc) ++ [(copyInput i).op.eval
            ((copyInput i).inputs.map fun j => (xs ++ acc).getD j false)]) = _
      have he : (copyInput i).op.eval
          ((copyInput i).inputs.map fun j => (xs ++ acc).getD j false) = xs.getD i false := by
        have hget : (xs ++ acc).getD i false = xs.getD i false :=
          List.getD_append _ _ _ _ hi
        change ((xs ++ acc).getD i false && ((xs ++ acc).getD i false && true)) = xs.getD i false
        rw [hget]
        simp
      rw [he, List.append_assoc, ih _ ht]
      simp [List.append_assoc]

private lemma map_range_getD (xs : List Bool) :
    (List.range xs.length).map (fun i => xs.getD i false) = xs := by
  apply List.ext_getElem
  · simp
  · intro i h1 h2
    simp [List.getD_eq_getElem?_getD, h2]

lemma hideInputs_wires (n : ℕ) (C : Circuit) (xs : List Bool) (hlen : xs.length = n) :
    (hideInputs n C).wires xs = xs ++ C.wires xs := by
  have hc : runGates ((List.range n).map copyInput) xs = xs ++ xs := by
    have h := runGates_copy xs [] (List.range n) (by
      intro i hi
      simpa [hlen] using List.mem_range.mp hi)
    simp only [List.append_nil] at h
    rw [← hlen, map_range_getD] at h
    simpa only [hlen] using h
  change runGates ((List.range n).map copyInput ++ C.gates.map (shiftGate n)) xs = _
  simp only [runGates, List.foldl_append] at hc ⊢
  rw [hc]
  change runGates (C.gates.map (shiftGate n)) (xs ++ xs) = xs ++ runGates C.gates xs
  rw [← hlen]
  exact runGates_shift xs xs C.gates

lemma hideInputs_eval (n : ℕ) (C : Circuit) (xs : List Bool) (hlen : xs.length = n) :
    (hideInputs n C).eval xs = C.eval xs := by
  unfold Circuit.eval
  rw [hideInputs_wires n C xs hlen]
  change (xs ++ C.wires xs).getD (n + C.output) false = (C.wires xs).getD C.output false
  rw [List.getD_append_right _ _ _ _ (by omega)]
  congr 1
  omega

lemma hideInputs_or_reads (n : ℕ) (C : Circuit) (g : Gate)
    (hg : g ∈ (hideInputs n C).gates) (ho : g.op = .or) :
    ∀ i ∈ g.inputs, n ≤ i := by
  change g ∈ (List.range n).map copyInput ++ C.gates.map (shiftGate n) at hg
  rcases List.mem_append.mp hg with hc | hs
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
    simp [copyInput] at ho
  · obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hs
    intro i hi
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hi
    omega

lemma hideInputs_orIn_empty (n : ℕ) (C : Circuit) (w : ℕ) (hw : n ≤ w) :
    PEqualNP.TopForm.orIn n (hideInputs n C) w = ∅ := by
  classical
  letI : DecidableEq GateOp := gateOpDecEq
  ext i
  simp only [Finset.notMem_empty, iff_false]
  intro hi
  rcases (Finset.mem_filter.mp hi).2 with h | ⟨k, hk, hr, ho, hm⟩
  · have := i.isLt
    omega
  · have hkg : gateAt (hideInputs n C) k ∈ (hideInputs n C).gates := by
      have heq : gateAt (hideInputs n C) k = (hideInputs n C).gates[k] := by
        simp [gateAt, List.getD_eq_getElem?_getD, hk]
      rw [heq]
      exact List.getElem_mem hk
    have hge := hideInputs_or_reads n C _ hkg ho i hm
    have := i.isLt
    omega

lemma hideInputs_tCount (n : ℕ) (C : Circuit) (colour : ℕ → Bool) :
    PEqualNP.TwoColour.tCount n (hideInputs n C) colour = 0 := by
  classical
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  have ht : PEqualNP.TwoColour.IsTwoColour n (hideInputs n C) colour j :=
    (Finset.mem_filter.mp hj).2
  obtain ⟨i, hi, hcol⟩ := ht.2.2.1
  rw [hideInputs_orIn_empty n C (n + j) (by omega)] at hi
  exact Finset.notMem_empty i hi

private lemma hideInputs_gate_lt (n : ℕ) (C : Circuit) (j : ℕ) (hj : j < n) :
    gateAt (hideInputs n C) j = copyInput j := by
  unfold gateAt hideInputs
  rw [List.getD_append _ _ _ _ (by simpa using hj)]
  simp [List.getD_eq_getElem?_getD, hj]

private lemma hideInputs_gate_ge (n : ℕ) (C : Circuit) (j : ℕ)
    (hj : j < (hideInputs n C).gates.length) (hge : n ≤ j) :
    gateAt (hideInputs n C) j = shiftGate n (gateAt C (j - n)) := by
  have hlt : j - n < C.gates.length := by
    simp only [hideInputs, List.length_append, List.length_map, List.length_range] at hj
    omega
  unfold gateAt hideInputs
  rw [List.getD_append_right _ _ _ _ (by simpa using hge)]
  simp [List.getD_eq_getElem?_getD, hlt]

lemma hideInputs_isAO2 (n : ℕ) (C : Circuit) (hC : PEqualNP.TopForm.IsAO2 n C) :
    PEqualNP.TopForm.IsAO2 n (hideInputs n C) := by
  have hall : ∀ g ∈ (hideInputs n C).gates,
      (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2 := by
    intro g hg
    change g ∈ (List.range n).map copyInput ++ C.gates.map (shiftGate n) at hg
    rcases List.mem_append.mp hg with hc | hs
    · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hc
      simp [copyInput]
    · obtain ⟨g, hgorig, rfl⟩ := List.mem_map.mp hs
      simpa [shiftGate] using And.intro (hC.1 g hgorig) (hC.2.2 g hgorig)
  refine ⟨fun g hg => (hall g hg).1, ?_, fun g hg => (hall g hg).2⟩
  intro j hj i hi
  by_cases hlt : j < n
  · rw [hideInputs_gate_lt n C j hlt] at hi
    simp only [copyInput, List.mem_cons, List.not_mem_nil, or_false, or_self] at hi
    subst i
    omega
  · have hge : n ≤ j := by omega
    have hbound : j - n < C.gates.length := by
      simp only [hideInputs, List.length_append, List.length_map, List.length_range] at hj
      omega
    rw [hideInputs_gate_ge n C j hj hge] at hi
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hi
    have hb := hC.2.1 (j - n) hbound k hk
    omega

lemma hideInputs_properties (n : ℕ) (C : Circuit)
    (hC : PEqualNP.TopForm.IsAO2 n C) :
    ∃ D : Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size = n + C.size ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.circuitFun n C ∧
      ∀ colour : ℕ → Bool, PEqualNP.TwoColour.tCount n D colour = 0 := by
  refine ⟨hideInputs n C, hideInputs_isAO2 n C hC, hideInputs_size n C, ?_,
    hideInputs_tCount n C⟩
  funext x
  exact hideInputs_eval n C (List.ofFn x) (by simp)

end PEqualNP.Outside.L_meta_4970_aux
