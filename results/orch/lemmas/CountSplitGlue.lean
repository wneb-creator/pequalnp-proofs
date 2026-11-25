import ShardTimeCover
namespace PEqualNP.Outside.L_meta_10760_first
lemma count_range13_cover : ∀ t ∈ List.range 13, ∃ us ∈ [[0], [1], (List.range 13).drop 2], t ∈ us := by
  intro t ht
  have ht13 := List.mem_range.mp ht
  interval_cases t <;> decide
lemma chkT_count_split {top : Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → Nat → List W → Bool}
    {E : List Gt} {Q : List (Nat × Nat)} {fb : Nat × Nat} {Z K H ph : Nat}
    (h0 : chkT top E Q fb Z K [0] H ph = false)
    (h1 : chkT top E Q fb Z K [1] H ph = false)
    (h2 : chkT top E Q fb Z K ((List.range 13).drop 2) H ph = false) :
    chkT top E Q fb Z K (List.range 13) H ph = false := by
  apply chkT_cover count_range13_cover
  intro us hu
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hu
  rcases hu with rfl | rfl | rfl
  · exact h0
  · exact h1
  · exact h2
end PEqualNP.Outside.L_meta_10760_first
