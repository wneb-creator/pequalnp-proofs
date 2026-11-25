import RestrictionEight

namespace PEqualNP.Outside.L_meta_1884.UniqueReader

open PEqualNP.CircuitLowerBounds ElimManyCount RestrictionEight

lemma count_zero {α : Type} (p : α → Bool) (xs : List α)
    (h : xs.countP p = 0) : ∀ x ∈ xs,p x = false := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    have ha : p a = false := by
      cases he : p a
      · rfl
      · simp [List.countP_cons,he] at h
    have ht : xs.countP p = 0 := by simpa [List.countP_cons,ha] using h
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ha
    · exact ih ht x hx

theorem split_one {α : Type} (p : α → Bool) (xs : List α)
    (h : xs.countP p ≤ 1) (hex : ∃ x ∈ xs,p x = true) :
    ∃ pre x post,xs = pre++x::post ∧ p x = true ∧
      (∀ y ∈ pre,p y = false) ∧ (∀ y ∈ post,p y = false) := by
  induction xs with
  | nil => simpa using hex
  | cons a xs ih =>
    cases ha : p a with
    | false =>
      have ht : xs.countP p ≤ 1 := by simpa [List.countP_cons,ha] using h
      obtain ⟨x,hx,hp⟩ := hex
      have hx' : x ∈ xs := by
        rcases List.mem_cons.mp hx with rfl | hx
        · rw [ha] at hp
          cases hp
        · exact hx
      obtain ⟨pre,x,post,he,hpx,hpre,hpost⟩ := ih ht ⟨x,hx',hp⟩
      refine ⟨a::pre,x,post,?_,hpx,?_,hpost⟩
      · simp [he]
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact ha
        · exact hpre y hy
    | true =>
      have ht : xs.countP p = 0 := by
        simp only [List.countP_cons,ha,ite_true] at h
        omega
      exact ⟨[],a,xs,rfl,ha,by simp,count_zero p xs ht⟩

lemma reader_iff (g : Gate) : reads deleted g = true ↔ 2 ∈ g.inputs := by
  simp [reads,deleted,List.any_eq_true]

theorem raw_two_split (D : Circuit) (h : D.gates.countP (reads deleted) ≤ 1)
    (hex : ∃ g ∈ D.gates,2 ∈ g.inputs) :
    ∃ pre g post,D.gates = pre++g::post ∧ 2 ∈ g.inputs ∧
      (∀ g' ∈ pre,2 ∉ g'.inputs) ∧ (∀ g' ∈ post,2 ∉ g'.inputs) := by
  obtain ⟨g,hg,hr⟩ := hex
  obtain ⟨pre,g,post,he,hr,hpre,hpost⟩ := split_one (reads deleted) D.gates h
    ⟨g,hg,(reader_iff g).mpr hr⟩
  refine ⟨pre,g,post,he,(reader_iff g).mp hr,?_,?_⟩
  · intro g' hg' hread
    have ht := (reader_iff g').mpr hread
    rw [hpre g' hg'] at ht
    cases ht
  · intro g' hg' hread
    have ht := (reader_iff g').mpr hread
    rw [hpost g' hg'] at ht
    cases ht

end PEqualNP.Outside.L_meta_1884.UniqueReader
