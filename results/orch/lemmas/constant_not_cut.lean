import constant_sweep_mono

namespace PEqualNP.Outside.L_meta_1886_aux.ConstantNotCut

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_aux.ConstantSweep
open ConstantSweepMono

lemma read_append_left (refs extras : List Ref) (i : ℕ) (hi : i < refs.length) :
    read (refs ++ extras) i = read refs i := List.getD_append _ _ _ _ hi

lemma cut (marks : Finset ℕ) (pre suffix : List Gate) (source : ℕ) (b : Bool)
    (hp : ∀ q ∈ pre, monoGood q) (hs : ∀ q ∈ suffix, monoGood q)
    (refs : List Ref) (n : ℕ)
    (within : ∀ i ∈ marks, i < refs.length)
    (constants : ∀ i ∈ marks, ∃ c : Bool, read refs i = .inl c)
    (sourceMark : source ∈ marks) (sourceValue : read refs source = .inl b) :
    ∃ (out : List Gate) (extraRefs : List Ref),
      (∀ q ∈ out, monoGood q) ∧ extraRefs.length = pre.length + 1 + suffix.length ∧
      out.length + (pre.filter (touched marks)).length +
        (suffix.filter (touched (insert (refs.length + pre.length) marks))).length ≤
          pre.length + suffix.length ∧
      ∀ w old, w.length = n → related refs w old →
        related (refs ++ extraRefs) (run out w)
          (run (pre ++ ⟨.not,[source]⟩ :: suffix) old) := by
  obtain ⟨preOut,preExtra,hpreOut,hpreLen,hpreSize,hpreSem⟩ :=
    ConstantSweepMono.sweep marks pre hp refs n within constants
  let preRefs := refs ++ preExtra
  let z := refs.length + pre.length
  have hz : z = preRefs.length := by simp [z,preRefs,hpreLen]
  have inherited (i : ℕ) (hi : i ∈ marks) :
      read preRefs i = read refs i := read_append_left _ _ _ (within i hi)
  have sourceConstant : read preRefs source = .inl b :=
    (inherited source sourceMark).trans sourceValue
  let nextRefs := preRefs ++ [Sum.inl (!b)]
  have nextWithin : ∀ i ∈ insert z marks, i < nextRefs.length := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · simp [nextRefs,hz]
    · have bound := within i hi
      simp [nextRefs,preRefs]
      omega
  have nextConstants : ∀ i ∈ insert z marks, ∃ c : Bool, read nextRefs i = .inl c := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · refine ⟨!b,?_⟩
      rw [hz]
      exact getD_last preRefs (Sum.inl (!b)) fixed
    · obtain ⟨c,hc⟩ := constants i hi
      have hiPre : i < preRefs.length := by
        have bound := within i hi
        simp [preRefs]
        omega
      exact ⟨c,(read_append_left preRefs [Sum.inl (!b)] i hiPre).trans
        ((inherited i hi).trans hc)⟩
  obtain ⟨suffixOut,suffixExtra,hsuffixOut,hsuffixLen,hsuffixSize,hsuffixSem⟩ :=
    ConstantSweepMono.sweep (insert z marks) suffix hs nextRefs (n + preOut.length)
      nextWithin nextConstants
  refine ⟨preOut ++ suffixOut,preExtra ++ Sum.inl (!b) :: suffixExtra,?_,?_,?_,?_⟩
  · intro q hq
    exact (List.mem_append.mp hq).elim (hpreOut q) (hsuffixOut q)
  · simp [hpreLen,hsuffixLen]
    omega
  · simp only [List.length_append]
    change preOut.length + suffixOut.length + (pre.filter (touched marks)).length +
      (suffix.filter (touched (insert z marks))).length ≤ pre.length + suffix.length
    omega
  · intro w old hw hr
    have preRelated := hpreSem w old hw hr
    have sourceRead : (run pre old).getD source false = b := by
      have h := read_value preRelated source
      change value (run preOut w) (read preRefs source) = _ at h
      rw [sourceConstant] at h
      exact h.symm
    have nextRelated : related nextRefs (run preOut w) (run pre old ++ [!b]) := by
      exact related_extend preRelated [] (.inl (!b)) (!b) (by trivial) (by rfl)
    have result := hsuffixSem (run preOut w) (run pre old ++ [!b])
      (by rw [run_length,hw]) nextRelated
    rw [run_append,run_append]
    change related (refs ++ (preExtra ++ Sum.inl (!b) :: suffixExtra))
      (run suffixOut (run preOut w))
      (run suffix (run pre old ++ [!((run pre old).getD source false)]))
    rw [sourceRead]
    simpa only [nextRefs,preRefs,List.append_assoc,List.singleton_append] using result

end PEqualNP.Outside.L_meta_1886_aux.ConstantNotCut
