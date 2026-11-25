namespace PEqualNP.Outside.L_meta_2592_aux.Binary16

open PEqualNP.Outside.L_meta_2592_aux PEqualNP.CircuitLowerBounds

abbrev inputPin (j : Fin 10) : Extended.Sig := Extended.pins.getD j.val Extended.zero

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
lemma assign_decode : ∀ (r : Extended.Row) (j : Fin 10),
    Extended.assign r j = RowEncoding.decode r j := by decide +kernel

lemma pin_mem (j : Fin 10) : inputPin j ∈ Extended.pins := by
  have hlen : Extended.pins.length = 10 := by decide +kernel
  have hi : j.val < Extended.pins.length := by omega
  simp only [inputPin,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,Option.getD_some]
  exact List.getElem_mem hi

lemma member_pin {a : Extended.Sig} (ha : a ∈ Extended.pins) :
    ∃ j : Fin 10, inputPin j = a := by
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp ha
  have hlen : Extended.pins.length = 10 := by decide +kernel
  let j : Fin 10 := ⟨i,by omega⟩
  refine ⟨j,?_⟩
  simp only [inputPin,j,List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi,
    Option.getD_some,he]

lemma transform_pin (p : Fin 10 → Fin 10) (j : Fin 10) :
    RowEncoding.transform p (inputPin j) = inputPin (p j) := by
  apply RowEncoding.bit_ext
  intro r
  rw [RowEncoding.bit_transform]
  change Extended.assign (RowEncoding.move p r) j = Extended.assign r (p j)
  rw [assign_decode,assign_decode,RowEncoding.decode_move]

lemma transform_bin (p : Fin 10 → Fin 10) (d : ℕ) (a b : Extended.Sig) :
    RowEncoding.transform p (Extended.bin d a b) =
      Extended.bin d (RowEncoding.transform p a) (RowEncoding.transform p b) := by
  unfold Extended.bin
  split_ifs <;> simp only [RowEncoding.transform_and,RowEncoding.transform_or,
    RowEncoding.transform_not]

lemma transform_target (p : Fin 10 → Fin 10)
    (hp : ∀ x : Fin 10 → Bool, edgeFunction (fun j => x (p j)) = edgeFunction x) :
    RowEncoding.transform p Extended.target = Extended.target := by
  apply RowEncoding.bit_ext
  intro r
  rw [RowEncoding.bit_transform]
  change Extended.bit (RowEncoding.move p r) Extended.target = Extended.bit r Extended.target
  rw [Extended.rowTarget,Extended.rowTarget]
  have hm : Extended.assign (RowEncoding.move p r) = fun j => Extended.assign r (p j) := by
    funext j
    rw [assign_decode,assign_decode,RowEncoding.decode_move]
  rw [hm]
  exact hp (Extended.assign r)

lemma canonical_second (a b : Fin 10) : pairSecond a b = 1 ∨ pairSecond a b = 2 := by
  unfold pairSecond
  split <;> simp

lemma suffix_of_canonical
    (canonical : ∀ (j : Fin 2) (d : Fin 4) (k : ℕ) (S : Finset Extended.Sig),
      Extended.Live true Extended.target k S →
      (∀ v ∈ S, v ∈ Extended.pins ++ [canonicalExtra j d]) → 16 ≤ k)
    (a b : Fin 10) (hne : a ≠ b) (d : Fin 4) (k : ℕ) (S : Finset Extended.Sig)
    (run : Extended.Live true Extended.target k S)
    (raw : ∀ v ∈ S, v ∈ Extended.pins ++ [Extended.bin d.val (inputPin a) (inputPin b)]) :
    16 ≤ k := by
  classical
  obtain ⟨hzero,hsecond,hbij,hadj⟩ := pairMove_properties a b hne
  let e : Fin 10 ≃ Fin 10 := Equiv.ofBijective (pairMove a b) hbij
  let j : Fin 2 := if pairSecond a b = 1 then 0 else 1
  have hj : (⟨j.val + 1, by have := j.isLt; omega⟩ : Fin 10) = pairSecond a b := by
    rcases canonical_second a b with h | h <;> simp [j,h]
  have ea : e.symm a = 0 := by
    apply e.injective
    simpa [e] using hzero.symm
  have eb : e.symm b = ⟨j.val + 1, by have := j.isLt; omega⟩ := by
    rw [hj]
    apply e.injective
    simpa [e] using hsecond.symm
  have hp : ∀ x : Fin 10 → Bool,
      edgeFunction (fun i => x (e.symm i)) = edgeFunction x := by
    intro x
    have hh := edgeFunction_pairMove a b hne (fun i => x (e.symm i))
    change edgeFunction (fun i => x (e.symm (e i))) =
      edgeFunction (fun i => x (e.symm i)) at hh
    simpa only [Equiv.symm_apply_apply] using hh.symm
  let φ : Extended.Sig → Extended.Sig := RowEncoding.transform e.symm
  have moved := map_live run φ (RowEncoding.transform_injective e.symm e.symm.surjective)
    (RowEncoding.transform_zero e.symm) (RowEncoding.transform_one e.symm)
    (transform_bin e.symm)
  have ht : φ Extended.target = Extended.target := transform_target e.symm hp
  rw [ht] at moved
  apply canonical j d k (S.image φ) moved
  intro v hv
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
  have hr := raw w hw
  rcases List.mem_append.mp hr with hr | hr
  · obtain ⟨i,rfl⟩ := member_pin hr
    apply List.mem_append_left
    change RowEncoding.transform e.symm (inputPin i) ∈ Extended.pins
    rw [transform_pin]
    exact pin_mem _
  · have he : w = Extended.bin d.val (inputPin a) (inputPin b) := by simpa using hr
    rw [he]
    apply List.mem_append_right
    change RowEncoding.transform e.symm (Extended.bin d.val (inputPin a) (inputPin b)) ∈
      [canonicalExtra j d]
    rw [transform_bin,transform_pin,transform_pin,ea,eb]
    simp only [List.mem_singleton]
    rfl

lemma suffix_of_canonical_with_extra {L : ℕ} (condition : Fin 4 → Prop)
    (canonical : ∀ (j : Fin 2) (d : Fin 4) (k : ℕ) (S : Finset Extended.Sig),
      condition d → Extended.Live true Extended.target k S → canonicalExtra j d ∈ S →
      (∀ v ∈ S, v ∈ Extended.pins ++ [canonicalExtra j d]) → L ≤ k)
    (a b : Fin 10) (hne : a ≠ b) (d : Fin 4) (hd : condition d) (k : ℕ) (S : Finset Extended.Sig)
    (run : Extended.Live true Extended.target k S)
    (hasExtra : Extended.bin d.val (inputPin a) (inputPin b) ∈ S)
    (raw : ∀ v ∈ S, v ∈ Extended.pins ++ [Extended.bin d.val (inputPin a) (inputPin b)]) :
    L ≤ k := by
  classical
  obtain ⟨hzero,hsecond,hbij,hadj⟩ := pairMove_properties a b hne
  let e : Fin 10 ≃ Fin 10 := Equiv.ofBijective (pairMove a b) hbij
  let j : Fin 2 := if pairSecond a b = 1 then 0 else 1
  have hj : (⟨j.val + 1, by have := j.isLt; omega⟩ : Fin 10) = pairSecond a b := by
    rcases canonical_second a b with h | h <;> simp [j,h]
  have ea : e.symm a = 0 := by
    apply e.injective
    simpa [e] using hzero.symm
  have eb : e.symm b = ⟨j.val + 1, by have := j.isLt; omega⟩ := by
    rw [hj]
    apply e.injective
    simpa [e] using hsecond.symm
  have hp : ∀ x : Fin 10 → Bool,
      edgeFunction (fun i => x (e.symm i)) = edgeFunction x := by
    intro x
    have hh := edgeFunction_pairMove a b hne (fun i => x (e.symm i))
    change edgeFunction (fun i => x (e.symm (e i))) =
      edgeFunction (fun i => x (e.symm i)) at hh
    simpa only [Equiv.symm_apply_apply] using hh.symm
  let φ : Extended.Sig → Extended.Sig := RowEncoding.transform e.symm
  have moved := map_live run φ (RowEncoding.transform_injective e.symm e.symm.surjective)
    (RowEncoding.transform_zero e.symm) (RowEncoding.transform_one e.symm)
    (transform_bin e.symm)
  have ht : φ Extended.target = Extended.target := transform_target e.symm hp
  rw [ht] at moved
  apply canonical j d k (S.image φ) hd moved
  · have hx : φ (Extended.bin d.val (inputPin a) (inputPin b)) ∈ S.image φ :=
      Finset.mem_image.mpr ⟨_,hasExtra,rfl⟩
    change RowEncoding.transform e.symm (Extended.bin d.val (inputPin a) (inputPin b)) ∈ S.image φ at hx
    rw [transform_bin,transform_pin,transform_pin,ea,eb] at hx
    exact hx
  · intro v hv
    obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hv
    have hr := raw w hw
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨i,rfl⟩ := member_pin hr
      apply List.mem_append_left
      change RowEncoding.transform e.symm (inputPin i) ∈ Extended.pins
      rw [transform_pin]
      exact pin_mem _
    · have he : w = Extended.bin d.val (inputPin a) (inputPin b) := by simpa using hr
      rw [he]
      apply List.mem_append_right
      change RowEncoding.transform e.symm (Extended.bin d.val (inputPin a) (inputPin b)) ∈
        [canonicalExtra j d]
      rw [transform_bin,transform_pin,transform_pin,ea,eb]
      simp only [List.mem_singleton]
      rfl


lemma binary_floor17_of_canonical
    (canonical : ∀ (j : Fin 2) (d : Fin 4) (k : ℕ) (S : Finset Extended.Sig),
      Extended.Live true Extended.target k S →
      (∀ v ∈ S, v ∈ Extended.pins ++ [canonicalExtra j d]) → 16 ≤ k)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    17 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  apply binary_floor17_of_suffix _ C legal computes
  intro k S a b d hd ha hb hab run raw
  obtain ⟨ia,rfl⟩ := member_pin ha
  obtain ⟨ib,rfl⟩ := member_pin hb
  have hne : ia ≠ ib := fun he => hab (congrArg inputPin he)
  exact suffix_of_canonical canonical ia ib hne ⟨d,hd⟩ k S run raw

end PEqualNP.Outside.L_meta_2592_aux.Binary16
