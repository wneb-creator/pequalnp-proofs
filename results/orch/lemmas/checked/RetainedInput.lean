import Mathlib.Data.Finset.Insert

namespace PEqualNP.Outside.L_meta_2592

lemma retained_of_row_collision {Signal Row : Type*} [DecidableEq Signal]
    (read : Row → Signal → Bool) (target created chosen : Signal)
    (pool : List Signal) (rest : Finset Signal)
    (raw : ∀ c ∈ rest, c ∈ pool)
    (tailDifference : ∀ r s, read r target ≠ read s target →
      ∃ c ∈ insert created rest, read r c ≠ read s c)
    (collision : ∃ r s, read r target ≠ read s target ∧
      read r created = read s created ∧
      ∀ c ∈ pool, c ≠ chosen → read r c = read s c) : chosen ∈ rest := by
  classical
  by_contra absent
  obtain ⟨r, s, different, sameCreated, sameOthers⟩ := collision
  obtain ⟨c, member, separates⟩ := tailDifference r s different
  rcases Finset.mem_insert.mp member with rfl | member
  · exact separates sameCreated
  · apply separates
    apply sameOthers c (raw c member)
    intro equal
    exact absent (equal ▸ member)

end PEqualNP.Outside.L_meta_2592
