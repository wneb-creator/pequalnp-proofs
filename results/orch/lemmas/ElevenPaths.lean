import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9502_aux

def cycle33 (a b : Fin 33) : Bool :=
  decide (∃ i : Fin 11,
    ((a.val = i.val ∨ a.val = 11 + i.val) ∧
      (b.val = (i.val + 1) % 11 ∨ b.val = 22 + i.val)) ∨
    ((b.val = i.val ∨ b.val = 11 + i.val) ∧
      (a.val = (i.val + 1) % 11 ∨ a.val = 22 + i.val)))

def pathRows (r : Fin 33) : Fin 33 :=
  if r.val % 3 = 0 then ⟨11 + r.val / 3, by omega⟩
  else if r.val % 3 = 1 then ⟨r.val / 3, by omega⟩
  else ⟨22 + (r.val / 3 + 10) % 11, by omega⟩

def pathCols (c : Fin 22) : Fin 33 :=
  if c.val % 2 = 0 then ⟨22 + c.val / 2, by omega⟩
  else ⟨11 + (c.val / 2 + 10) % 11, by omega⟩

def elevenP5 (r : Fin 33) (c : Fin 22) : Bool :=
  decide (r.val / 3 = c.val / 2 ∧
    (((r.val % 3 = 0 ∨ r.val % 3 = 1) ∧ c.val % 2 = 0) ∨
     ((r.val % 3 = 1 ∨ r.val % 3 = 2) ∧ c.val % 2 = 1)))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma pathRows_injective : Function.Injective pathRows := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma pathCols_injective : Function.Injective pathCols := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma eleven_paths : ∀ r c, cycle33 (pathRows r) (pathCols c) = elevenP5 r c := by
  decide +kernel

def physicalElevenP5 (a b : Fin 33) : Bool :=
  decide (∃ i : Fin 11,
    ((a.val = 11 + i.val ∨ a.val = i.val) ∧ b.val = 22 + i.val) ∨
    ((a.val = i.val ∨ a.val = 22 + (i.val + 10) % 11) ∧
      b.val = 11 + (i.val + 10) % 11))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma physical_eleven_paths : ∀ a b,
    (cycle33 a b && decide (11 ≤ b.val)) = physicalElevenP5 a b := by
  decide +kernel

def p17Rows (r : Fin 9) : Fin 33 :=
  ⟨(2 * r.val) % 11, by omega⟩

def p17Cols (c : Fin 8) : Fin 33 :=
  ⟨(2 * c.val + 1) % 11, by omega⟩

def p17 (r : Fin 9) (c : Fin 8) : Bool :=
  decide (r.val = c.val ∨ r.val = c.val + 1)

lemma p17Rows_injective : Function.Injective p17Rows := by
  decide +kernel

lemma p17Cols_injective : Function.Injective p17Cols := by
  decide +kernel

lemma p17_embedding : ∀ r c, cycle33 (p17Rows r) (p17Cols c) = p17 r c := by
  decide +kernel

def p25Rows (r : Fin 13) : Fin 33 :=
  if r.val = 0 then ⟨22, by omega⟩
  else if r.val = 12 then ⟨21, by omega⟩
  else ⟨(2 * r.val - 1) % 11, by omega⟩

def p25Cols (c : Fin 12) : Fin 33 :=
  if c.val = 0 then ⟨11, by omega⟩
  else if c.val = 11 then ⟨32, by omega⟩
  else ⟨(2 * c.val) % 11, by omega⟩

def p25 (r : Fin 13) (c : Fin 12) : Bool :=
  decide (r.val = c.val ∨ r.val = c.val + 1)

lemma p25Rows_injective : Function.Injective p25Rows := by
  decide +kernel

lemma p25Cols_injective : Function.Injective p25Cols := by
  decide +kernel

lemma p25_embedding : ∀ r c, cycle33 (p25Rows r) (p25Cols c) = p25 r c := by
  decide +kernel

lemma p25_rows_forced : ∀ r, ∃ c, p25 r c = true ∧ ∃ r', p25 r' c = false := by
  decide +kernel

lemma p25_cols_forced : ∀ c, ∃ r, p25 r c = true ∧ ∃ c', p25 r c' = false := by
  decide +kernel

def p25RowMask (a : Fin 33) : Bool :=
  decide (a.val < 11 ∨ a.val = 21 ∨ a.val = 22)

def p25ColMask (b : Fin 33) : Bool :=
  decide ((1 ≤ b.val ∧ b.val ≤ 11) ∨ b.val = 32)

lemma p25Rows_image : ∀ a, p25RowMask a = true ↔ ∃ r, p25Rows r = a := by
  decide +kernel

lemma p25Cols_image : ∀ b, p25ColMask b = true ↔ ∃ c, p25Cols c = b := by
  decide +kernel

def physicalP25 (a b : Fin 33) : Bool :=
  cycle33 a b && p25RowMask a && p25ColMask b

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma physical_p25 : ∀ a b, physicalP25 a b =
    decide (∃ r c, p25Rows r = a ∧ p25Cols c = b ∧ p25 r c = true) := by
  decide +kernel

def packedP4A (i : Fin 14) : Fin 33 :=
  ⟨([1, 2, 4, 6, 7, 9, 10, 11, 24, 14, 16, 29, 19, 32] : List Nat)[i.val]! % 33,
    Nat.mod_lt _ (by decide)⟩

def packedP4B (i : Fin 14) : Fin 33 :=
  ⟨([22, 13, 25, 27, 18, 30, 21, 23, 12, 26, 28, 17, 31, 20] : List Nat)[i.val]! % 33,
    Nat.mod_lt _ (by decide)⟩

def packedP4C (i : Fin 14) : Fin 33 :=
  ⟨([11, 24, 14, 16, 29, 19, 32, 1, 2, 4, 6, 7, 9, 10] : List Nat)[i.val]! % 33,
    Nat.mod_lt _ (by decide)⟩

def packedP4D (i : Fin 14) : Fin 33 :=
  ⟨([23, 12, 26, 28, 17, 31, 20, 22, 13, 25, 27, 18, 30, 21] : List Nat)[i.val]! % 33,
    Nat.mod_lt _ (by decide)⟩

def packedP4Wire (i : Fin 14) (j : Fin 4) : Fin 66 :=
  if j.val = 0 then ⟨(packedP4A i).val, by omega⟩
  else if j.val = 1 then ⟨(packedP4B i).val, by omega⟩
  else if j.val = 2 then ⟨33 + (packedP4C i).val, by omega⟩
  else ⟨33 + (packedP4D i).val, by omega⟩

lemma packedP4_edges : ∀ i,
    cycle33 (packedP4A i) (packedP4C i) = true ∧
    cycle33 (packedP4A i) (packedP4D i) = true ∧
    cycle33 (packedP4B i) (packedP4C i) = true ∧
    cycle33 (packedP4B i) (packedP4D i) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma packedP4_disjoint : Function.Injective
    (fun p : Fin 14 × Fin 4 => packedP4Wire p.1 p.2) := by
  decide +kernel

lemma packedP4_hitting_size (S : Finset (Fin 66))
    (h : ∀ i : Fin 14, ∃ j : Fin 4, packedP4Wire i j ∈ S) : 14 ≤ S.card := by
  classical
  choose j hj using h
  let f : Fin 14 → {v // v ∈ S} := fun i => ⟨packedP4Wire i (j i), hj i⟩
  have hf : Function.Injective f := by
    intro i k heq
    have hw : packedP4Wire i (j i) = packedP4Wire k (j k) := congrArg Subtype.val heq
    exact congrArg Prod.fst (@packedP4_disjoint (i, j i) (k, j k) hw)
  have hc := Fintype.card_le_of_injective f hf
  simpa using hc

lemma cycle33_rows_distinct : ∀ a a' : Fin 33, a ≠ a' →
    ∃ b : Fin 33, cycle33 a b ≠ cycle33 a' b := by
  decide +kernel

lemma cycle33_cols_distinct : ∀ b b' : Fin 33, b ≠ b' →
    ∃ a : Fin 33, cycle33 a b ≠ cycle33 a b' := by
  decide +kernel

end PEqualNP.Outside.L_meta_9502_aux
