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

end PEqualNP.Outside.L_meta_9502_aux
