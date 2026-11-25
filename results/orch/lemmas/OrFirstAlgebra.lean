import Structural16

namespace PEqualNP.Outside.L_meta_2592_aux.SignedFloor.Extended

lemma or_bit_bin (i : Row) (d : Nat) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]

lemma or_bit_zero (i : Row) : bit i zero = false := by simp [bit, zero]

lemma or_left_identities (a b : Sig) :
    bin 0 (bin 1 a b) a = a ∧ bin 1 (bin 1 a b) a = bin 1 a b ∧
    bin 2 (bin 1 a b) a = bin 2 b a ∧ bin 3 (bin 1 a b) a = zero := by
  refine ⟨?_, ?_, ?_, ?_⟩
  all_goals
    apply bit_ext
    intro r
    cases ha : bit r a <;> cases hb : bit r b <;> simp [or_bit_bin, or_bit_zero, ha, hb]

lemma or_difference_front {target : Sig} {a b : Sig} {U : Finset Sig} {k : Nat}
    (roots : Set Sig) (ha : a ∈ roots) (hb : b ∈ roots)
    (pa : proper a) (pb : proper b) (hab : a ≠ b)
    (hra : bin 1 a b ≠ a) (hrb : bin 1 a b ≠ b)
    (raw : ∀ z ∈ U, z ∈ roots ∨ z = bin 1 a b) (hbU : b ∈ U)
    (fresh : bin 2 (bin 1 a b) a ∉ insert (bin 1 a b) (insert a U))
    (tail : Live true target k (insert (bin 2 (bin 1 a b) a) U)) :
    ∃ m V, m ≤ k + 1 ∧ (∀ z ∈ V, z ∈ roots) ∧
      bin 2 b a ∉ insert b (insert a V) ∧
      Live true target m (insert (bin 2 b a) V) := by
  have value := (or_left_identities a b).2.2.1
  rw [value] at fresh tail
  have za : bin 2 b a ≠ a := fun h => fresh (by simp [h])
  have zb : bin 2 b a ≠ b := fun h => fresh (by simp [h, hbU])
  have zu : bin 2 b a ∉ U := fun h => fresh (by simp [h])
  by_cases h : bin 1 a b ∈ U
  · let R := U.erase (bin 1 a b)
    have ueq : U = insert (bin 1 a b) R := by
      exact (Finset.insert_erase h).symm
    let V := insert a (insert b R)
    have vh : ∀ z ∈ V, z ∈ roots := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact ha
      rcases Finset.mem_insert.mp hz with rfl | hz
      · exact hb
      have hzU := (Finset.mem_erase.mp hz).2
      exact (raw z hzU).resolve_right (Finset.mem_erase.mp hz).1
    have freshOr : bin 1 a b ∉ insert a (insert b (insert (bin 2 b a) R)) := by
      intro hm
      simp only [Finset.mem_insert] at hm
      rcases hm with h | h | h | h
      · exact hra h
      · exact hrb h
      · exact fresh (by simp [← h])
      · exact (Finset.mem_erase.mp h).1 rfl
    have goal : Live true target k (insert (bin 1 a b) (insert (bin 2 b a) R)) := by
      simpa only [ueq, Finset.insert_comm] using tail
    have swapped := Live.binary (show allowed true 1 by simp [allowed]) pa pb hab freshOr goal
    refine ⟨k+1, V, le_rfl, vh, ?_, ?_⟩
    · simp only [V, Finset.mem_insert, not_or]
      refine ⟨zb, za, za, zb, ?_⟩
      exact fun h => zu (Finset.mem_erase.mp h).2
    · simpa only [V, Finset.insert_comm] using swapped
  · refine ⟨k, U, Nat.le_succ _, ?_, ?_, tail⟩
    · intro z hz
      exact (raw z hz).resolve_right (fun e => h (e ▸ hz))
    · simp only [Finset.mem_insert, not_or]
      exact ⟨zb, za, zu⟩

end PEqualNP.Outside.L_meta_2592_aux.SignedFloor.Extended
