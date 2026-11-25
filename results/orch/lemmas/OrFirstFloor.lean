import Floor18
import OrFirstAlgebra

namespace PEqualNP.Outside.L_meta_2592_aux.SignedFloor

lemma firstOrDifferenceFloor {a b : Extended.Sig} {U : Finset Extended.Sig} {k : Nat}
    (ha : a ∈ Extended.pins) (hb : b ∈ Extended.pins)
    (pa : Extended.proper a) (pb : Extended.proper b) (hab : a ≠ b)
    (hra : Extended.bin 1 a b ≠ a) (hrb : Extended.bin 1 a b ≠ b)
    (raw : ∀ z ∈ U, z ∈ Extended.pins ∨ z = Extended.bin 1 a b) (hbU : b ∈ U)
    (fresh : Extended.bin 2 (Extended.bin 1 a b) a ∉ insert (Extended.bin 1 a b) (insert a U))
    (tail : Extended.Live true Extended.target k (insert (Extended.bin 2 (Extended.bin 1 a b) a) U)) :
    18 ≤ k + 2 := by
  obtain ⟨m,V,hm,hraw,hfresh,htail⟩ :=
    Extended.or_difference_front {z | z ∈ Extended.pins} ha hb pa pb hab hra hrb raw hbU fresh tail
  have lower := firstNonOrFloor hb ha (Ne.symm hab)
    (show Extended.allowed true 2 by simp [Extended.allowed]) (by decide) hraw hfresh htail
  omega

lemma firstOrDifferenceDropFloor {a b : Extended.Sig} {U : Finset Extended.Sig} {k : Nat}
    (ha : a ∈ Extended.pins) (hb : b ∈ Extended.pins) (hab : a ≠ b)
    (raw : ∀ z ∈ U, z ∈ Extended.pins ∨ z = Extended.bin 1 a b) (hbU : b ∈ U)
    (missing : Extended.bin 1 a b ∉ U)
    (fresh : Extended.bin 2 (Extended.bin 1 a b) a ∉ insert (Extended.bin 1 a b) (insert a U))
    (tail : Extended.Live true Extended.target k (insert (Extended.bin 2 (Extended.bin 1 a b) a) U)) :
    19 ≤ k + 2 := by
  have value := (Extended.or_left_identities a b).2.2.1
  rw [value] at fresh tail
  have hraw : ∀ z ∈ U, z ∈ Extended.pins := by
    intro z hz
    exact (raw z hz).resolve_right (fun e => missing (e ▸ hz))
  have hfresh : Extended.bin 2 b a ∉ insert b (insert a U) := by
    intro hz
    rcases Finset.mem_insert.mp hz with he | hz
    · exact fresh (by simp [he, hbU])
    · exact fresh (Finset.mem_insert_of_mem hz)
  have lower := firstNonOrFloor hb ha (Ne.symm hab)
    (show Extended.allowed true 2 by simp [Extended.allowed]) (by decide) hraw hfresh tail
  omega

end PEqualNP.Outside.L_meta_2592_aux.SignedFloor
