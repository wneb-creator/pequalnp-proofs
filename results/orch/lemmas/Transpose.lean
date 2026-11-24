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

lemma program_snoc {inputs steps : List (Finset α)} {S : Finset α}
    (h : UnionProgram inputs (steps ++ [S])) :
    UnionProgram inputs steps ∧
      ∃ A ∈ inputs ++ steps, ∃ B ∈ inputs ++ steps, S = A ∪ B := by
  constructor
  · intro i hi
    obtain ⟨A, hA, B, hB, hAB⟩ := h i (by simp; omega)
    refine ⟨A, ?_, B, ?_, ?_⟩
    · simpa [List.take_append_of_le_length (by omega : i ≤ steps.length)] using hA
    · simpa [List.take_append_of_le_length (by omega : i ≤ steps.length)] using hB
    · simpa [List.getElem_append_left hi] using hAB
  · obtain ⟨A, hA, B, hB, hAB⟩ := h steps.length (by simp)
    exact ⟨A, by simpa using hA, B, by simpa using hB, by simpa using hAB⟩

lemma flow_insert {V : Finset (Finset α)} {S : Finset α}
    (d : Finset α → Finset β) (x : α) (y : β) :
    flow (insert S V) d x y ↔ flow V d x y ∨ (x ∈ S ∧ y ∈ d S) := by
  simp only [flow, Finset.mem_insert]
  aesop

lemma flow_transfer {V : Finset (Finset α)} {S A B : Finset α}
    (hA : A ∈ V) (hB : B ∈ V) (hS : S = A ∪ B)
    (d : Finset α → Finset β) (x : α) (y : β) :
    let e := Function.update d A (d A ∪ d S)
    flow V (Function.update e B (e B ∪ d S)) x y ↔ flow (insert S V) d x y := by
  dsimp only
  rw [flow_update hB, flow_update hA, flow_insert]
  simp only [hS, Finset.mem_union]
  tauto

lemma eliminate {base steps : List (Finset α)} (hs : UnionProgram base steps)
    {inputs p : List (Finset β)} (hp : UnionProgram inputs p)
    (d : Finset α → Finset β)
    (hd : ∀ A ∈ (base ++ steps).toFinset, d A ∈ inputs ++ p) :
    ∃ (q : List (Finset β)) (e : Finset α → Finset β),
      UnionProgram inputs (p ++ q) ∧
      (∀ A ∈ base.toFinset, e A ∈ inputs ++ (p ++ q)) ∧
      q.length + count base.toFinset e ≤ steps.length + count (base ++ steps).toFinset d ∧
      (∀ x y, flow base.toFinset e x y ↔ flow (base ++ steps).toFinset d x y) := by
  induction steps using List.reverseRecOn generalizing d p with
  | nil =>
    refine ⟨[], d, by simpa using hp, ?_, ?_, ?_⟩
    · simpa using hd
    · simp
    · simp
  | append_singleton steps S ih =>
    obtain ⟨hs0, A, hA, B, hB, hS⟩ := program_snoc hs
    let V := (base ++ steps).toFinset
    have hV : (base ++ (steps ++ [S])).toFinset = insert S V := by
      simp [V, List.toFinset_append]
    have hAV : A ∈ V := by simpa [V] using hA
    have hBV : B ∈ V := by simpa [V] using hB
    have hdV : ∀ T ∈ V, d T ∈ inputs ++ p := by
      intro T hT
      exact hd T (by rw [hV]; exact Finset.mem_insert_of_mem hT)
    by_cases hSV : S ∈ V
    · have hVe : insert S V = V := Finset.insert_eq_of_mem hSV
      obtain ⟨q, e, hq, he, hb, hf⟩ := ih hs0 hp d hdV
      refine ⟨q, e, hq, he, ?_, ?_⟩
      · change q.length + count base.toFinset e ≤ steps.length + count V d at hb
        rw [hV, hVe]
        simp only [List.length_append, List.length_singleton]
        omega
      · intro x y
        rw [hV, hVe]
        exact hf x y
    · by_cases hne : (d S).Nonempty
      · obtain ⟨q1, hq1, he1, hb1⟩ := merge hp hAV d (d S) hdV
          (hd S (by rw [hV]; simp))
        let d1 := Function.update d A (d A ∪ d S)
        have hTS : d S ∈ inputs ++ (p ++ q1) := by
          have := hd S (by rw [hV]; simp)
          simpa [List.append_assoc] using List.mem_append_left q1 this
        obtain ⟨q2, hq2, he2, hb2⟩ := merge hq1 hBV d1 (d S) he1 hTS
        let d2 := Function.update d1 B (d1 B ∪ d S)
        obtain ⟨q3, e, hq3, he3, hb3, hf3⟩ := ih hs0 hq2 d2 he2
        refine ⟨q1 ++ q2 ++ q3, e, ?_, ?_, ?_, ?_⟩
        · simpa [List.append_assoc] using hq3
        · simpa [List.append_assoc] using he3
        · have hc : count (insert S V) d = count V d + 1 := by
            simpa [hne] using count_insert hSV d
          rw [hV]
          simp only [List.length_append, List.length_singleton]
          change q1.length + count V d1 ≤ count V d + 1 at hb1
          change q2.length + count V d2 ≤ count V d1 + 1 at hb2
          change q3.length + count base.toFinset e ≤ steps.length + count V d2 at hb3
          omega
        · intro x y
          rw [hV]
          exact (hf3 x y).trans (flow_transfer hAV hBV hS d x y)
      · have hzero : d S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
        obtain ⟨q, e, hq, he, hb, hf⟩ := ih hs0 hp d hdV
        refine ⟨q, e, hq, he, ?_, ?_⟩
        · have hc : count (insert S V) d = count V d := by
            simpa [hne] using count_insert hSV d
          change q.length + count base.toFinset e ≤ steps.length + count V d at hb
          rw [hV, hc]
          simp only [List.length_append, List.length_singleton]
          omega
        · intro x y
          rw [hV, flow_insert]
          simpa [hzero, V] using hf x y

lemma seed {V : Finset (Finset α)} (F : β → Finset α) (I : Finset β)
    {inputs : List (Finset β)} (hempty : ∅ ∈ inputs)
    (hF : ∀ y ∈ I, F y ∈ V) (hsingle : ∀ y ∈ I, {y} ∈ inputs) :
    ∃ (p : List (Finset β)) (d : Finset α → Finset β),
      UnionProgram inputs p ∧ (∀ A ∈ V, d A ∈ inputs ++ p) ∧
      p.length + count V d ≤ I.card ∧
      (∀ x y, flow V d x y ↔ y ∈ I ∧ x ∈ F y) := by
  induction I using Finset.induction_on with
  | empty =>
    refine ⟨[], fun _ => ∅, program_nil inputs, ?_, ?_, ?_⟩
    · intro A hA; simpa using hempty
    · simp [count]
    · simp [flow]
  | @insert z I hz ih =>
    obtain ⟨p, d, hp, hd, hb, hf⟩ := ih
      (fun y hy => hF y (Finset.mem_insert_of_mem hy))
      (fun y hy => hsingle y (Finset.mem_insert_of_mem hy))
    have hzV := hF z (Finset.mem_insert_self z I)
    obtain ⟨q, hq, he, hcost⟩ := merge hp hzV d {z} hd
      (List.mem_append_left _ (hsingle z (Finset.mem_insert_self z I)))
    refine ⟨p ++ q, Function.update d (F z) (d (F z) ∪ {z}), hq, he, ?_, ?_⟩
    · have hcI : (insert z I).card = I.card + 1 := by simp [hz]
      simp only [List.length_append]
      omega
    · intro x y
      rw [flow_update hzV, hf]
      simp only [Finset.mem_singleton, Finset.mem_insert]
      aesop

noncomputable def atoms (A : Finset α) : List (Finset α) :=
  ∅ :: A.toList.map (fun a => {a})

lemma flow_atoms (A : Finset α) (d : Finset α → Finset β) (x : α) (y : β) :
    flow (atoms A).toFinset d x y ↔ x ∈ A ∧ y ∈ d {x} := by
  constructor
  · rintro ⟨S, hS, hx, hy⟩
    simp only [atoms, List.mem_toFinset, List.mem_cons, List.mem_map,
      Finset.mem_toList] at hS
    rcases hS with rfl | ⟨a, ha, rfl⟩
    · simp at hx
    · have : x = a := by simpa using hx
      subst a
      exact ⟨ha, hy⟩
  · rintro ⟨hx, hy⟩
    exact ⟨{x}, by simp [atoms, hx], by simp, hy⟩

lemma transpose [Fintype β] (A : Finset α) (steps : List (Finset α))
    (hs : UnionProgram (atoms A) steps) (F : β → Finset α)
    (hF : ∀ y, F y ∈ atoms A ++ steps)
    (hcover : ∀ x ∈ A, ∃ y, x ∈ F y) :
    ∃ p : List (Finset β), UnionProgram (atoms Finset.univ) p ∧
      p.length + A.card ≤ steps.length + Fintype.card β ∧
      ∀ x ∈ A, Finset.univ.filter (fun y => x ∈ F y) ∈ atoms Finset.univ ++ p := by
  obtain ⟨p, d, hp, hd, hcost, hflow⟩ := seed (V := (atoms A ++ steps).toFinset) F Finset.univ
    (inputs := atoms Finset.univ) (by simp [atoms])
    (fun y _ => by simpa using hF y) (fun y _ => by simp [atoms])
  obtain ⟨q, e, hq, he, hcost2, hflow2⟩ := eliminate hs hp d hd
  have hrel : ∀ x y, flow (atoms A).toFinset e x y ↔ x ∈ F y := by
    intro x y
    exact (hflow2 x y).trans (by simpa using hflow x y)
  have hcard : A.card ≤ count (atoms A).toFinset e := by
    unfold count
    apply Finset.card_le_card_of_injOn (fun x => ({x} : Finset α))
    · intro x hx
      have hx' : x ∈ A := hx
      apply Finset.mem_filter.mpr
      refine ⟨by simp [atoms, hx'], ?_⟩
      obtain ⟨y, hy⟩ := hcover x hx
      exact ⟨y, ((flow_atoms A e x y).mp ((hrel x y).mpr hy)).2⟩
    · intro x hx y hy hxy
      simpa using hxy
  refine ⟨p ++ q, hq, ?_, ?_⟩
  · simp only [List.length_append]
    simp only [Finset.card_univ] at hcost
    omega
  · intro x hx
    have hset : e {x} = Finset.univ.filter (fun y => x ∈ F y) := by
      ext y
      simpa [flow_atoms, hx] using hrel x y
    rw [← hset]
    exact he {x} (by simp [atoms, hx])

end Transpose
end PEqualNP.Outside.L_meta_3678
