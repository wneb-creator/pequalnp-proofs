import ExistingBinary16
import LowerPair
import LowerRow
namespace PEqualNP.Outside.L_meta_2592_aux.Binary16
open PEqualNP.CircuitLowerBounds
lemma first_binary_split (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    ∃ (k : ℕ) (U : Finset Extended.Sig) (a b : Extended.Sig) (d : ℕ),
      k + 1 ≤ C.gates.countP (fun g => !Extended.isNot g) ∧ d < 4 ∧
      a ∈ Extended.initial ∧ b ∈ Extended.initial ∧ a ≠ b ∧
      Extended.Live true Extended.target k (insert (Extended.bin d a b) U) ∧
      ∀ v ∈ U, v ∈ Extended.initial := by
  obtain ⟨k, S, hk, run, raw⟩ := Extended.realize C legal computes
  cases k with
  | zero =>
      obtain ⟨rfl, hp⟩ := run
      have hmem := raw Extended.target (by simp)
      have hn : Extended.target ∉ Extended.initial := by decide +kernel
      exact False.elim (hn hmem)
  | succ k =>
      obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, hfresh, tail⟩ := run
      have hd4 : d < 4 := by
        rcases hd with hd | ⟨hu, hd⟩ <;> omega
      exact ⟨k, U, a, b, d, hk, hd4, raw a (by simp), raw b (by simp), hab,
        tail, fun v hv => raw v (by simp [hv])⟩

lemma binary_floor17_of_suffix
    (suffix : ∀ (k : ℕ) (S : Finset Extended.Sig) (a b : Extended.Sig) (d : ℕ),
      d < 4 → a ∈ Extended.initial → b ∈ Extended.initial → a ≠ b →
      Extended.Live true Extended.target k S →
      (∀ v ∈ S, v ∈ Extended.initial ++ [Extended.bin d a b]) → 16 ≤ k)
    (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    17 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  obtain ⟨k, U, a, b, d, hk, hd, ha, hb, hab, tail, raw⟩ :=
    first_binary_split C legal computes
  have floor : 16 ≤ k := by
    apply suffix k (insert (Extended.bin d a b) U) a b d hd ha hb hab tail
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · simp
    · exact List.mem_append_left _ (raw v hv)
  have sameNot :
      (fun g : Gate => @decide (g.op = GateOp.not) (lineDegreeGateOpDecEq g.op GateOp.not)) = Extended.isNot := by
    funext g
    obtain ⟨op, operands⟩ := g
    cases op <;> rfl
  rw [PEqualNP.NotBracket.notCount, sameNot, ← List.countP_eq_length_filter]
  have negSame : (fun g : Gate => decide (¬ Extended.isNot g = true)) = (fun g => !Extended.isNot g) := by
    funext g
    cases Extended.isNot g <;> rfl
  have count := List.length_eq_countP_add_countP Extended.isNot (l := C.gates)
  rw [negSame] at count
  change 17 + C.gates.countP Extended.isNot ≤ C.gates.length
  omega

lemma map_live {u : Bool} {T : Extended.Sig} {k : ℕ} {S : Finset Extended.Sig}
    (h : Extended.Live u T k S) (φ : Extended.Sig → Extended.Sig)
    (hinj : Function.Injective φ) (hz : φ Extended.zero = Extended.zero)
    (ho : φ Extended.one = Extended.one)
    (hbin : ∀ d a b, φ (Extended.bin d a b) = Extended.bin d (φ a) (φ b)) :
    Extended.Live u (φ T) k (S.image φ) := by
  have hproper : ∀ a, Extended.proper a → Extended.proper (φ a) := by
    intro a ha
    constructor
    · intro he
      exact ha.1 (hinj (he.trans hz.symm))
    · intro he
      exact ha.2 (hinj (he.trans ho.symm))
  induction h using Extended.Live.ind with
  | stop hp =>
      simpa only [Finset.image_singleton] using Extended.Live.stop (u := u) (hproper T hp)
  | @binary k U a b d hd ha hb hab hf tail ih =>
      simp only [Finset.image_insert]
      apply Extended.Live.binary hd (hproper a ha) (hproper b hb)
        (fun he => hab (hinj he))
      · intro he
        have hm : φ (Extended.bin d a b) ∈
            (insert a (insert b U)).image φ := by
          simpa only [Finset.image_insert, hbin] using he
        obtain ⟨v, hv, hvEq⟩ := Finset.mem_image.mp hm
        exact hf (hinj hvEq ▸ hv)
      · simpa only [Finset.image_insert, hbin] using ih

end PEqualNP.Outside.L_meta_2592_aux.Binary16

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

namespace PEqualNP.Outside.L_meta_2592_aux.Binary16

open PEqualNP.CircuitLowerBounds

lemma binary17 (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    17 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  exact binary_floor17_of_canonical (fun j d _ _ run raw => suffixSixteen j d run raw)
    C legal computes

lemma at_most_two_not (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (small : C.size ≤ 19)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    PEqualNP.NotBracket.notCount C ≤ 2 := by
  have bound := binary17 C legal computes
  omega

lemma one_or_two_not (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (small : C.size ≤ 19)
    (hasNot : ∃ g ∈ C.gates, g.op = GateOp.not)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = Extended.f10 x) :
    PEqualNP.NotBracket.notCount C = 1 ∨ PEqualNP.NotBracket.notCount C = 2 := by
  have bound := at_most_two_not C legal small computes
  have pos : 0 < PEqualNP.NotBracket.notCount C := by
    obtain ⟨g,hg,hnot⟩ := hasNot
    let _ : DecidableEq GateOp := lineDegreeGateOpDecEq
    have mem : g ∈ C.gates.filter (fun h => decide (h.op = GateOp.not)) :=
      List.mem_filter.mpr ⟨hg,decide_eq_true hnot⟩
    by_contra! h
    have hz : PEqualNP.NotBracket.notCount C = 0 := by omega
    have empty := List.length_eq_zero_iff.mp hz
    rw [empty] at mem
    cases mem
  omega

end PEqualNP.Outside.L_meta_2592_aux.Binary16
