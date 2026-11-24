import Mathlib

namespace PEqualNP.Outside.L_meta_3678

def UnionProgram {α : Type*} [DecidableEq α]
    (inputs steps : List (Finset α)) : Prop :=
  ∀ i (hi : i < steps.length),
    ∃ A ∈ inputs ++ steps.take i, ∃ B ∈ inputs ++ steps.take i,
      steps[i] = A ∪ B

namespace Transpose

variable {α β : Type*} [DecidableEq α] [DecidableEq β]

def count (V : Finset (Finset α)) (d : Finset α → Finset β) : ℕ :=
  (V.filter fun A => (d A).Nonempty).card

def flow (V : Finset (Finset α)) (d : Finset α → Finset β) (x : α) (y : β) : Prop :=
  ∃ A ∈ V, x ∈ A ∧ y ∈ d A

lemma program_nil (inputs : List (Finset α)) : UnionProgram inputs [] := by
  simp [UnionProgram]

lemma program_append {inputs p q : List (Finset α)}
    (hp : UnionProgram inputs p) (hq : UnionProgram (inputs ++ p) q) :
    UnionProgram inputs (p ++ q) := by
  intro i hi
  by_cases hip : i < p.length
  · obtain ⟨A, hA, B, hB, h⟩ := hp i hip
    refine ⟨A, ?_, B, ?_, ?_⟩
    · simpa [List.take_append_of_le_length (by omega : i ≤ p.length)] using hA
    · simpa [List.take_append_of_le_length (by omega : i ≤ p.length)] using hB
    · simpa [List.getElem_append_left hip] using h
  · have hiq : i - p.length < q.length := by simp only [List.length_append] at hi; omega
    obtain ⟨A, hA, B, hB, h⟩ := hq (i - p.length) hiq
    refine ⟨A, ?_, B, ?_, ?_⟩
    · simpa [List.take_append, List.take_of_length_le (by omega : p.length ≤ i),
        List.append_assoc] using hA
    · simpa [List.take_append, List.take_of_length_le (by omega : p.length ≤ i),
        List.append_assoc] using hB
    · simpa [List.getElem_append_right (by omega : p.length ≤ i)] using h

lemma program_one {inputs : List (Finset α)} {A B : Finset α}
    (hA : A ∈ inputs) (hB : B ∈ inputs) : UnionProgram inputs [A ∪ B] := by
  intro i hi
  have : i = 0 := by simpa using hi
  subst i
  exact ⟨A, by simpa using hA, B, by simpa using hB, rfl⟩

lemma count_insert {V : Finset (Finset α)} {A : Finset α}
    (hA : A ∉ V) (d : Finset α → Finset β) :
    count (insert A V) d = count V d + if (d A).Nonempty then 1 else 0 := by
  by_cases h : (d A).Nonempty
  · simp [count, Finset.filter_insert, h, hA, Nat.add_comm]
  · simp [count, Finset.filter_insert, h]

lemma count_update_erase (V : Finset (Finset α)) (A : Finset α)
    (d : Finset α → Finset β) (T : Finset β) :
    count (V.erase A) (Function.update d A T) = count (V.erase A) d := by
  unfold count
  congr 1
  ext B
  by_cases h : B = A
  · subst B; simp
  · simp [Function.update_apply, h]

lemma count_update {V : Finset (Finset α)} {A : Finset α} (hA : A ∈ V)
    (d : Finset α → Finset β) (T : Finset β) :
    count V (Function.update d A T) + (if (d A).Nonempty then 1 else 0) =
      count V d + (if T.Nonempty then 1 else 0) := by
  have hV : V = insert A (V.erase A) := (Finset.insert_erase hA).symm
  calc
    count V (Function.update d A T) + (if (d A).Nonempty then 1 else 0) =
        count (V.erase A) d + (if T.Nonempty then 1 else 0) +
          (if (d A).Nonempty then 1 else 0) := by
      conv_lhs => rw [hV]
      rw [count_insert (by simp : A ∉ V.erase A), count_update_erase]
      simp
    _ = count V d + (if T.Nonempty then 1 else 0) := by
      conv_rhs => rw [hV]
      rw [count_insert (by simp : A ∉ V.erase A)]
      omega

lemma flow_update {V : Finset (Finset α)} {A : Finset α} (hA : A ∈ V)
    (d : Finset α → Finset β) (T : Finset β) (x : α) (y : β) :
    flow V (Function.update d A (d A ∪ T)) x y ↔
      flow V d x y ∨ (x ∈ A ∧ y ∈ T) := by
  constructor
  · rintro ⟨B, hB, hx, hy⟩
    by_cases h : B = A
    · subst B
      have hy' : y ∈ d A ∪ T := by simpa using hy
      exact (Finset.mem_union.mp hy').elim (fun h => Or.inl ⟨A, hA, hx, h⟩) (fun h => Or.inr ⟨hx, h⟩)
    · exact Or.inl ⟨B, hB, hx, by simpa [Function.update_apply, h] using hy⟩
  · rintro (⟨B, hB, hx, hy⟩ | ⟨hx, hy⟩)
    · refine ⟨B, hB, hx, ?_⟩
      by_cases h : B = A
      · subst B; simp [hy]
      · simpa [Function.update_apply, h] using hy
    · exact ⟨A, hA, hx, by simp [hy]⟩

lemma merge {inputs p : List (Finset β)} (hp : UnionProgram inputs p)
    {V : Finset (Finset α)} {A : Finset α} (hA : A ∈ V)
    (d : Finset α → Finset β) (T : Finset β)
    (hd : ∀ B ∈ V, d B ∈ inputs ++ p) (hT : T ∈ inputs ++ p) :
    ∃ q : List (Finset β), UnionProgram inputs (p ++ q) ∧
      (∀ B ∈ V, Function.update d A (d A ∪ T) B ∈ inputs ++ (p ++ q)) ∧
      q.length + count V (Function.update d A (d A ∪ T)) ≤ count V d + 1 := by
  by_cases hda : (d A).Nonempty
  · by_cases ht : T.Nonempty
    · refine ⟨[d A ∪ T], program_append hp (program_one (hd A hA) hT), ?_, ?_⟩
      · intro B hB
        by_cases h : B = A
        · subst B; simp
        · have := hd B hB
          simp only [Function.update_apply, h, ↓reduceIte]
          simpa [List.append_assoc] using (List.mem_append_left [d A ∪ T] this)
      · have hc := count_update hA d (d A ∪ T)
        simp [hda, ht] at hc
        simp only [List.length_singleton]
        omega
    · have ht0 : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp ht
      subst T
      refine ⟨[], ?_, ?_, ?_⟩
      · simpa using hp
      · intro B hB
        simpa using hd B hB
      · simp
  · have hda0 : d A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hda
    refine ⟨[], ?_, ?_, ?_⟩
    · simpa using hp
    · intro B hB
      by_cases h : B = A
      · subst B; simpa [hda0] using hT
      · simpa [Function.update_apply, h] using hd B hB
    · have hc := count_update hA d (d A ∪ T)
      simp [hda0] at hc
      simp only [List.length_nil, zero_add, hda0, Finset.empty_union]
      split_ifs at hc <;> omega

end Transpose
end PEqualNP.Outside.L_meta_3678
