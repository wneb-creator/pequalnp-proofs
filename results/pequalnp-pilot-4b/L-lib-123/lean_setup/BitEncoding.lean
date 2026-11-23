import Mathlib

namespace RadixOrder

def bitPass {α : Type} (bit : α → Bool) (rows : List α) : List α :=
  rows.filter (fun row => !(bit row)) ++ rows.filter bit

def lowValue {α : Type} (bits : α → ℕ → Bool) (row : α) : ℕ → ℕ
  | 0 => 0
  | k + 1 => lowValue bits row k + if bits row k then 2 ^ k else 0

lemma lowValue_lt {α : Type} (bits : α → ℕ → Bool) (row : α) (k : ℕ) :
    lowValue bits row k < 2 ^ k := by
  induction k with
  | zero => simp [lowValue]
  | succ k ih =>
    cases h : bits row k <;> simp [lowValue, h, pow_succ] <;> omega

lemma bitPass_perm {α : Type} (bit : α → Bool) (rows : List α) :
    (bitPass bit rows).Perm rows := by
  simpa [bitPass] using List.filter_append_perm (fun row => !(bit row)) rows

lemma bitPass_sorted {α : Type} (bits : α → ℕ → Bool) (k : ℕ) (rows : List α)
    (h : rows.Pairwise (fun a b => lowValue bits a k ≤ lowValue bits b k)) :
    (bitPass (fun row => bits row k) rows).Pairwise
      (fun a b => lowValue bits a (k + 1) ≤ lowValue bits b (k + 1)) := by
  rw [bitPass, List.pairwise_append]
  refine ⟨?_, ?_, ?_⟩
  · apply List.pairwise_filter.mpr
    apply h.imp
    intro a b hab ha hb
    have ha' : bits a k = false := by simpa using ha
    have hb' : bits b k = false := by simpa using hb
    simpa [lowValue, ha', hb'] using hab
  · apply List.pairwise_filter.mpr
    apply h.imp
    intro a b hab ha hb
    simpa [lowValue, ha, hb] using Nat.add_le_add_right hab (2 ^ k)
  · intro a ha b hb
    have ha' : bits a k = false := by simpa using (List.mem_filter.mp ha).2
    have hb' : bits b k = true := (List.mem_filter.mp hb).2
    simp only [lowValue, ha', hb', Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
    have bound := lowValue_lt bits a k
    omega

def radix {α : Type} (bits : α → ℕ → Bool) : ℕ → List α → List α
  | 0, rows => rows
  | k + 1, rows => bitPass (fun row => bits row k) (radix bits k rows)

lemma radix_perm {α : Type} (bits : α → ℕ → Bool) (k : ℕ) (rows : List α) :
    (radix bits k rows).Perm rows := by
  induction k with
  | zero => exact List.Perm.refl _
  | succ k ih => exact (bitPass_perm _ _).trans ih

lemma radix_sorted {α : Type} (bits : α → ℕ → Bool) (k : ℕ) (rows : List α) :
    (radix bits k rows).Pairwise (fun a b => lowValue bits a k ≤ lowValue bits b k) := by
  induction k with
  | zero => exact List.pairwise_of_forall (by intro a b; simp [lowValue])
  | succ k ih => exact bitPass_sorted bits k _ ih

abbrev Row := List Bool × Bool

def rowBit (row : Row) (i : ℕ) : Bool := row.1.getD i false

def rotateRow (i : ℕ) (row : Row) : Row := (row.1.rotate i, row.2)

def rowPass (rows : List Row) : List Row :=
  (bitPass (fun row => rowBit row 0) rows).map (rotateRow 1)

lemma rotateRow_zero (row : Row) : rotateRow 0 row = row := by
  simp [rotateRow]

lemma rotateRow_add (i j : ℕ) (row : Row) :
    rotateRow j (rotateRow i row) = rotateRow (i + j) row := by
  simp [rotateRow]

lemma rowBit_rotate (row : Row) (i : ℕ) (h : i < row.1.length) :
    rowBit (rotateRow i row) 0 = rowBit row i := by
  simp only [rowBit, rotateRow, List.getD_eq_getElem?_getD]
  rw [← List.head?_eq_getElem?, List.head?_rotate h]

lemma filter_map_eq {α β : Type} (f : α → β) (p : β → Bool) (q : α → Bool) (rows : List α)
    (h : ∀ row ∈ rows, p (f row) = q row) :
    (rows.map f).filter p = (rows.filter q).map f := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    have he := h row (by simp)
    have ht := ih (by intro r hr; exact h r (by simp [hr]))
    cases hb : q row <;> simp [he, hb, ht]

lemma bitPass_map {α β : Type} (f : α → β) (p : β → Bool) (q : α → Bool) (rows : List α)
    (h : ∀ row ∈ rows, p (f row) = q row) :
    bitPass p (rows.map f) = (bitPass q rows).map f := by
  rw [bitPass, bitPass, List.map_append,
    filter_map_eq f (fun row => !(p row)) (fun row => !(q row)) rows
      (by intro row hr; rw [h row hr]), filter_map_eq f p q rows h]

lemma rowPass_rotated (rows : List Row) (i : ℕ)
    (h : ∀ row ∈ rows, i < row.1.length) :
    rowPass (rows.map (rotateRow i)) =
      (bitPass (fun row => rowBit row i) rows).map (rotateRow (i + 1)) := by
  rw [rowPass, bitPass_map (rotateRow i) (fun row => rowBit row 0)
    (fun row => rowBit row i) rows (by intro row hr; exact rowBit_rotate row i (h row hr))]
  simp [List.map_map, Function.comp_def, rotateRow_add]

lemma iterated_pass (width i : ℕ) (rows : List Row)
    (hw : ∀ row ∈ rows, row.1.length = width) (hi : i ≤ width) :
    rowPass^[i] rows = (radix rowBit i rows).map (rotateRow i) := by
  induction i with
  | zero =>
    have he : rotateRow 0 = id := funext rotateRow_zero
    simp [radix, he]
  | succ i ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    rw [rowPass_rotated]
    · rfl
    · intro row hr
      have hm := (radix_perm rowBit i rows).mem_iff.mp hr
      rw [hw row hm]
      omega

lemma full_passes_eq (width : ℕ) (rows : List Row)
    (hw : ∀ row ∈ rows, row.1.length = width) :
    rowPass^[width] rows = radix rowBit width rows := by
  rw [iterated_pass width width rows hw (le_refl _)]
  calc
    (radix rowBit width rows).map (rotateRow width) = (radix rowBit width rows).map id := by
      apply List.map_congr_left
      intro row hr
      have hm := (radix_perm rowBit width rows).mem_iff.mp hr
      have hlen := hw row hm
      simp [rotateRow, ← hlen]
    _ = radix rowBit width rows := List.map_id _

lemma full_passes_correct (width : ℕ) (rows : List Row)
    (hw : ∀ row ∈ rows, row.1.length = width) :
    (rowPass^[width] rows).Perm rows ∧
    (rowPass^[width] rows).Pairwise
      (fun a b => lowValue rowBit a width ≤ lowValue rowBit b width) := by
  rw [full_passes_eq width rows hw]
  exact ⟨radix_perm _ _ _, radix_sorted _ _ _⟩

def moveHead (row : Row) : Row :=
  match row.1 with
  | [] => row
  | head :: rest => (rest ++ [head], row.2)

def concretePass (rows : List Row) : List Row :=
  ((rows.filter (fun row => row.1.headD false == false)).map moveHead) ++
    ((rows.filter (fun row => row.1.headD false == true)).map moveHead)

lemma moveHead_eq (row : Row) : moveHead row = rotateRow 1 row := by
  obtain ⟨bits, value⟩ := row
  cases bits <;> simp [moveHead, rotateRow]

lemma head_eq (row : Row) : row.1.headD false = rowBit row 0 := by
  obtain ⟨bits, value⟩ := row
  cases bits <;> rfl

lemma concretePass_eq (rows : List Row) : concretePass rows = rowPass rows := by
  have hm : moveHead = rotateRow 1 := funext moveHead_eq
  have hfalse : (fun row : Row => row.1.headD false == false) =
      (fun row : Row => !(rowBit row 0)) := by
    funext row
    rw [head_eq]
    cases rowBit row 0 <;> rfl
  have htrue : (fun row : Row => row.1.headD false == true) =
      (fun row : Row => rowBit row 0) := by
    funext row
    rw [head_eq]
    cases rowBit row 0 <;> rfl
  simp only [concretePass, rowPass, bitPass, hfalse, htrue, hm, List.map_append]

lemma concrete_full_passes_correct (width : ℕ) (rows : List Row)
    (hw : ∀ row ∈ rows, row.1.length = width) :
    (concretePass^[width] rows).Perm rows ∧
    (concretePass^[width] rows).Pairwise
      (fun a b => lowValue rowBit a width ≤ lowValue rowBit b width) := by
  have he : concretePass = rowPass := funext concretePass_eq
  rw [he]
  exact full_passes_correct width rows hw

lemma encoded_length (width : ℕ) (rows : List Row)
    (hw : ∀ row ∈ rows, row.1.length = width) :
    (rows.flatMap (fun row => row.1.map (Sum.inl : Bool → Bool ⊕ Bool) ++ [Sum.inr row.2])).length =
      (width + 1) * rows.length := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    have hrow := hw row (by simp)
    have hrows := ih (by intro r hr; exact hw r (by simp [hr]))
    simp only [List.flatMap_cons, List.length_append, List.length_map,
      List.length_cons, List.length_nil, Nat.mul_succ]
    rw [hrow, hrows]
    omega

end RadixOrder

namespace BitEncoding

open RadixOrder

def keyBits (key width : ℕ) : List Bool :=
  List.ofFn (fun i : Fin width => key.testBit i)

def encodeRow (width : ℕ) (row : ℕ × Bool) : Row :=
  (keyBits row.1 width, row.2)

@[simp] lemma keyBits_length (key width : ℕ) : (keyBits key width).length = width := by
  simp [keyBits]

lemma keyBits_getD (key width i : ℕ) (hi : i < width) :
    (keyBits key width).getD i false = key.testBit i := by
  simp [keyBits, List.getD_eq_getElem?_getD, hi]

lemma testBit_weight (key k : ℕ) :
    (if key.testBit k then 2 ^ k else 0) = 2 ^ k * (key / 2 ^ k % 2) := by
  have hmod := Nat.mod_lt (key / 2 ^ k) (by omega : 0 < 2)
  rw [Nat.testBit_eq_decide_div_mod_eq]
  by_cases h : key / 2 ^ k % 2 = 1
  · simp [h]
  · have hz : key / 2 ^ k % 2 = 0 := by omega
    simp [hz]

lemma lowValue_nat_mod (key width : ℕ) :
    lowValue Nat.testBit key width = key % 2 ^ width := by
  induction width with
  | zero => simp [lowValue, Nat.mod_one]
  | succ width ih =>
    rw [lowValue, ih, testBit_weight, pow_succ, Nat.mod_mul]

lemma lowValue_encode_partial (key width k : ℕ) (value : Bool) (hk : k ≤ width) :
    lowValue rowBit (keyBits key width, value) k = lowValue Nat.testBit key k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [lowValue, lowValue, ih (by omega)]
    rw [rowBit, keyBits_getD key width k (by omega)]

lemma lowValue_encode (key width : ℕ) (value : Bool) (hkey : key < 2 ^ width) :
    lowValue rowBit (keyBits key width, value) width = key := by
  rw [lowValue_encode_partial key width width value (le_refl _), lowValue_nat_mod,
    Nat.mod_eq_of_lt hkey]

def keyWidth (keyBound : ℕ) : ℕ := max 1 keyBound.size

lemma keyWidth_pos (keyBound : ℕ) : 0 < keyWidth keyBound := by
  unfold keyWidth
  omega

lemma key_lt_two_pow_width {key keyBound : ℕ} (hkey : key ≤ keyBound) :
    key < 2 ^ keyWidth keyBound := by
  apply (Nat.size_le).mp
  exact (Nat.size_le_size hkey).trans (le_max_right _ _)

lemma keyWidth_le_log (keyBound : ℕ) : keyWidth keyBound ≤ keyBound.size + 1 := by
  unfold keyWidth
  omega

lemma keyWidth_eq_log2 (keyBound : ℕ) : keyWidth keyBound = keyBound.log2 + 1 := by
  by_cases hz : keyBound = 0
  · subst keyBound
    simp [keyWidth, Nat.size]
  · have hu : keyBound.size ≤ keyBound.log2 + 1 :=
      Nat.size_le.mpr Nat.lt_log2_self
    have hl : keyBound.log2 < keyBound.size := Nat.lt_size.mpr (Nat.log2_self_le hz)
    unfold keyWidth
    omega

lemma natural_encoded_length (width : ℕ) (rows : List (ℕ × Bool)) :
    ((rows.map (encodeRow width)).flatMap
      (fun row => row.1.map (Sum.inl : Bool → Bool ⊕ Bool) ++ [Sum.inr row.2])).length =
      (width + 1) * rows.length := by
  have hw : ∀ row ∈ rows.map (encodeRow width), row.1.length = width := by
    intro row hr
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr
    simp [encodeRow]
  simpa only [List.length_map] using encoded_length width (rows.map (encodeRow width)) hw

lemma bounded_encoded_length (keyBound : ℕ) (rows : List (ℕ × Bool)) :
    ((rows.map (encodeRow (keyWidth keyBound))).flatMap
      (fun row => row.1.map (Sum.inl : Bool → Bool ⊕ Bool) ++ [Sum.inr row.2])).length =
      (keyBound.log2 + 2) * rows.length := by
  rw [natural_encoded_length, keyWidth_eq_log2]

def decodeRow (width : ℕ) (row : Row) : ℕ × Bool :=
  (lowValue rowBit row width, row.2)

lemma decode_encode (width : ℕ) (row : ℕ × Bool) (hkey : row.1 < 2 ^ width) :
    decodeRow width (encodeRow width row) = row := by
  obtain ⟨key, value⟩ := row
  dsimp only [decodeRow, encodeRow]
  rw [lowValue_encode key width value hkey]

def sortRows (width : ℕ) (rows : List (ℕ × Bool)) : List (ℕ × Bool) :=
  (concretePass^[width] (rows.map (encodeRow width))).map (decodeRow width)

theorem sortRows_correct (width : ℕ) (rows : List (ℕ × Bool))
    (hkey : ∀ row ∈ rows, row.1 < 2 ^ width) :
    (sortRows width rows).Perm rows ∧
      (sortRows width rows).Pairwise (fun a b => a.1 ≤ b.1) := by
  have hw : ∀ row ∈ rows.map (encodeRow width), row.1.length = width := by
    intro row hr
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hr
    simp [encodeRow]
  obtain ⟨hp, hs⟩ := concrete_full_passes_correct width (rows.map (encodeRow width)) hw
  constructor
  · unfold sortRows
    have hi : (rows.map (encodeRow width)).map (decodeRow width) = rows := by
      rw [List.map_map]
      calc
        rows.map (decodeRow width ∘ encodeRow width) = rows.map id := by
          apply List.map_congr_left
          intro row hr
          exact decode_encode width row (hkey row hr)
        _ = rows := List.map_id _
    simpa only [hi] using hp.map (decodeRow width)
  · exact List.pairwise_map.mpr hs

theorem bounded_sortRows_correct (keyBound : ℕ) (rows : List (ℕ × Bool))
    (hkey : ∀ row ∈ rows, row.1 ≤ keyBound) :
    (sortRows (keyWidth keyBound) rows).Perm rows ∧
      (sortRows (keyWidth keyBound) rows).Pairwise (fun a b => a.1 ≤ b.1) := by
  exact sortRows_correct _ rows (by intro row hr; exact key_lt_two_pow_width (hkey row hr))

end BitEncoding
