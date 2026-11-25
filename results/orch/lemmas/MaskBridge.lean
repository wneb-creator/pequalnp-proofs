import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9811.GraphProfile

abbrev V := Fin 14

def ofMask (m : Fin 16384) : Finset V :=
  Finset.univ.filter fun v => m.val.testBit v.val = true

def encodeList (L : List V) : Nat :=
  L.foldr (fun v a => 2 ^ v.val ||| a) 0

lemma encodeList_bit (L : List V) (v : V) :
    (encodeList L).testBit v.val = decide (v ∈ L) := by
  induction L with
  | nil => simp [encodeList]
  | cons w L ih =>
    change (2 ^ w.val ||| encodeList L).testBit v.val = _
    rw [Nat.testBit_or, Nat.testBit_two_pow, ih]
    simp [List.mem_cons, Fin.ext_iff, eq_comm]

noncomputable def toMask (S : Finset V) : Fin 16384 :=
  ⟨encodeList S.toList % 16384, Nat.mod_lt _ (by decide)⟩

lemma of_toMask (S : Finset V) : ofMask (toMask S) = S := by
  apply Finset.ext
  intro v
  rw [ofMask, Finset.mem_filter]
  simp only [Finset.mem_univ, true_and, toMask]
  change (encodeList S.toList % 2^14).testBit v.val = true ↔ v ∈ S
  rw [Nat.testBit_mod_two_pow, encodeList_bit]
  simp [v.isLt]

def mkMask (hi lo : Fin 128) : Fin 16384 :=
  ⟨hi.val * 128 + lo.val, by have := hi.isLt; have := lo.isLt; omega⟩

lemma splitMask (m : Fin 16384) : ∃ hi lo : Fin 128, mkMask hi lo = m := by
  refine ⟨⟨m.val / 128, by have := m.isLt; omega⟩,
    ⟨m.val % 128, Nat.mod_lt _ (by decide)⟩, ?_⟩
  apply Fin.ext
  simp only [mkMask]
  omega

end PEqualNP.Outside.L_meta_9811.GraphProfile
