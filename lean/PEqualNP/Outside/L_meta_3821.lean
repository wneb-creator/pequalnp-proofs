import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.List.OfFn

namespace PEqualNP.Outside.L_meta_3821_aux

def petersen (x : Fin 10 → Bool) : Bool :=
  (List.finRange 5).any fun i =>
    (x (Fin.castAdd 5 i) && x (Fin.castAdd 5 (i + 1))) ||
    (x (Fin.castAdd 5 i) && x (Fin.natAdd 5 i)) ||
    (x (Fin.natAdd 5 i) && x (Fin.natAdd 5 (i + 2)))

def rowBits (r : ℕ) (i : Fin 10) : Bool := r.testBit i.val

def rowCode (x : Fin 10 → Bool) : ℕ :=
  (x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
  16 * (x 4).toNat + 32 * (x 5).toNat + 64 * (x 6).toNat +
  128 * (x 7).toNat + 256 * (x 8).toNat + 512 * (x 9).toNat

set_option maxRecDepth 10000 in
lemma rowCode_lt : ∀ x : Fin 10 → Bool, rowCode x < 1024 := by
  decide +kernel

set_option maxRecDepth 10000 in
lemma rowBits_code : ∀ x : Fin 10 → Bool, rowBits (rowCode x) = x := by
  decide +kernel

def negativeRows : List ℕ := [0, 1, 2, 4, 5, 8, 9, 10, 16, 18, 20, 32, 34, 36, 40, 42, 48, 50, 52, 64, 65, 68, 69, 72, 73, 80, 84, 96, 100, 104, 112, 116, 128, 129, 130, 136, 137, 138, 144, 146, 192, 193, 200, 201, 208, 256, 257, 258, 260, 261, 272, 274, 276, 384, 385, 386, 400, 402, 512, 513, 514, 516, 517, 520, 521, 522, 544, 546, 548, 552, 554, 768, 769, 770, 772, 773]

def positiveRows : List ℕ := [3, 6, 12, 17, 24, 33, 66, 132, 160, 264, 288, 320, 528, 576, 640]

set_option maxRecDepth 10000 in
lemma negativeRows_spec : ∀ r : Fin 1024,
    petersen (rowBits r.val) = false ↔ r.val ∈ negativeRows := by
  decide +kernel

set_option maxRecDepth 10000 in
lemma positiveRows_spec : ∀ r : Fin 1024,
    (petersen (rowBits r.val) = true ∧ (List.ofFn (rowBits r.val)).count true ≤ 2) ↔
      r.val ∈ positiveRows := by
  decide +kernel

lemma negativeRows_bounded : ∀ r ∈ negativeRows, r < 1024 := by decide +kernel

lemma positiveRows_bounded : ∀ r ∈ positiveRows, r < 1024 := by decide +kernel

lemma rowCounts : negativeRows.length = 76 ∧ positiveRows.length = 15 ∧
    (negativeRows ++ positiveRows).Nodup := by decide +kernel

lemma promise_iff_rows (U : (Fin 10 → Bool) → Bool) :
    (∀ x : Fin 10 → Bool,
      petersen x = false ∨ (List.ofFn x).count true ≤ 2 → U x = petersen x) ↔
    (∀ r ∈ negativeRows, U (rowBits r) = false) ∧
      (∀ r ∈ positiveRows, U (rowBits r) = true) := by
  constructor
  · intro h
    constructor
    · intro r hr
      have hg := (negativeRows_spec ⟨r, negativeRows_bounded r hr⟩).mpr hr
      exact (h (rowBits r) (Or.inl hg)).trans hg
    · intro r hr
      have hg := (positiveRows_spec ⟨r, positiveRows_bounded r hr⟩).mpr hr
      exact (h (rowBits r) (Or.inr hg.2)).trans hg.1
  · rintro ⟨hn, hp⟩ x hx
    let r : Fin 1024 := ⟨rowCode x, rowCode_lt x⟩
    have hb : rowBits r.val = x := rowBits_code x
    cases hg : petersen x with
    | false =>
      have hr : r.val ∈ negativeRows := (negativeRows_spec r).mp (hb ▸ hg)
      simpa only [hb] using hn r.val hr
    | true =>
      have hc : (List.ofFn x).count true ≤ 2 := hx.resolve_left (by simp [hg])
      have hr : r.val ∈ positiveRows := (positiveRows_spec r).mp (hb ▸ ⟨hg, hc⟩)
      simpa only [hb] using hp r.val hr

end PEqualNP.Outside.L_meta_3821_aux
