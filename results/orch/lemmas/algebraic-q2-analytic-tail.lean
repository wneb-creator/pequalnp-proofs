def qa_nb : Fin 4 → Finset (Fin 7) := ![{0,1,3},{0,2,6},{1,5,6},{0,4,5}]

def qa_unit (r : Fin 7 → Finset (Fin 3)) (j : Fin 3) : Finset (Fin 7) :=
  Finset.univ.filter (fun t => j ∈ r t)

def qa_consumers (A : Fin 4 → Finset (Fin 7)) (t : Fin 7) : Finset (Fin 4) :=
  Finset.univ.filter (fun i => t ∈ A i)

abbrev qa_allowed (S : Finset (Fin 7)) (U : Finset (Fin 7)) : Prop :=
  U.card ≤ 2 ∨ U = qa_nb 0 ∨ U = qa_nb 1 ∨ U = qa_nb 3 ∨ U = S

set_option maxHeartbeats 0 in
theorem qa_antichain_omit : ∀ q : Fin 3, ∀ A B C : Finset (Fin 3),
    q ∉ A → q ∉ B → q ∉ C → A.Nonempty → B.Nonempty → C.Nonempty →
    ¬ A ⊆ B → ¬ B ⊆ A → ¬ A ⊆ C → ¬ C ⊆ A → ¬ B ⊆ C → ¬ C ⊆ B → False := by
  decide +kernel

set_option maxHeartbeats 0 in
theorem qa_antichain_contain : ∀ q : Fin 3, ∀ A B C : Finset (Fin 3),
    q ∈ A → q ∈ B → q ∈ C →
    ¬ A ⊆ B → ¬ B ⊆ A → ¬ A ⊆ C → ¬ C ⊆ A → ¬ B ⊆ C → ¬ C ⊆ B → False := by
  decide +kernel

theorem qa_two_missing_unit (r : Fin 7 → Finset (Fin 3)) (S : Finset (Fin 7))
    (allowed : ∀ j, qa_allowed S (qa_unit r j))
    (two : (r 0).card = 2)
    (center : (r 0).card + ((Finset.univ.erase 0).filter (fun t => r t ⊆ r 0)).card ≤ 5) :
    ∃ q : Fin 3, q ∉ r 0 ∧ qa_unit r q = S ∧ (0 : Fin 7) ∉ S := by
  classical
  have geo : ∀ R : Finset (Fin 3), R.card = 2 → ∃ q : Fin 3, R = Finset.univ.erase q := by
    decide +kernel
  obtain ⟨q,eq⟩ := geo (r 0) two
  have absent : q ∉ r 0 := by rw [eq]; simp
  have subset (t : Fin 7) : r t ⊆ r 0 ↔ q ∉ r t := by
    rw [eq]
    constructor
    · intro sub member
      exact (Finset.mem_erase.1 (sub member)).1 rfl
    · intro no x hx
      refine Finset.mem_erase.2 ⟨?_,Finset.mem_univ _⟩
      intro equal
      exact no (equal ▸ hx)
  have complement : (Finset.univ.erase (0 : Fin 7)).filter (fun t => ¬ r t ⊆ r 0) = qa_unit r q := by
    ext t
    constructor
    · intro h
      have notsub := (Finset.mem_filter.1 h).2
      have member : q ∈ r t := by
        by_contra no
        exact notsub ((subset t).2 no)
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _,member⟩
    · intro h
      have member := (Finset.mem_filter.1 h).2
      apply Finset.mem_filter.2
      refine ⟨Finset.mem_erase.2 ⟨?_,Finset.mem_univ _⟩,?_⟩
      · intro equal
        exact absent (equal ▸ member)
      · intro sub
        exact (subset t).1 sub member
  have partition := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.erase (0 : Fin 7)) (fun t => r t ⊆ r 0)
  rw [complement,show (Finset.univ.erase (0 : Fin 7)).card = 6 from rfl] at partition
  have large : 3 ≤ (qa_unit r q).card := by omega
  have nozero : (0 : Fin 7) ∉ qa_unit r q := by
    intro member
    exact absent (Finset.mem_filter.1 member).2
  have equal : qa_unit r q = S := by
    rcases allowed q with small | equal | equal | equal | equal
    · omega
    · exact (nozero (by rw [equal]; decide)).elim
    · exact (nozero (by rw [equal]; decide)).elim
    · exact (nozero (by rw [equal]; decide)).elim
    · exact equal
  exact ⟨q,absent,equal,by rw [← equal]; exact nozero⟩

theorem qa_residual_impossible (S : Finset (Fin 7))
    (r : Fin 7 → Finset (Fin 3)) (A : Fin 4 → Finset (Fin 7))
    (allowed : ∀ j, qa_allowed S (qa_unit r j))
    (contains : qa_nb 2 ⊆ S)
    (supersets : ∀ i, qa_nb i ⊆ A i)
    (choices : ∀ i, A i = qa_nb 0 ∨ A i = qa_nb 1 ∨ A i = qa_nb 3 ∨ A i = S)
    (missing : A 2 = S)
    (budget : ∀ t, (qa_consumers A t).card + (if t = 0 then 0 else 1) ≤ 2 + (r t).card)
    (labels : ∀ i x t, x ∈ qa_nb i → (r x).Nonempty → r x ⊆ r t → t ∈ A i)
    (center : (r 0).card + ((Finset.univ.erase 0).filter (fun t => r t ⊆ r 0)).card ≤ 5) :
    False := by
  classical
  have zero_mem : ∀ i ∈ ({0,1,3} : Finset (Fin 4)), (0 : Fin 7) ∈ A i := by
    intro i hi
    exact supersets i ((by decide +kernel : ∀ i ∈ ({0,1,3} : Finset (Fin 4)),
      (0 : Fin 7) ∈ qa_nb i) i hi)
  have three_consumers : 3 ≤ (qa_consumers A 0).card := by
    have sub : ({0,1,3} : Finset (Fin 4)) ⊆ qa_consumers A 0 := by
      intro i hi
      exact Finset.mem_filter.2 ⟨Finset.mem_univ _,zero_mem i hi⟩
    exact Finset.card_le_card sub
  have b0 := budget 0
  simp only [ite_true,Nat.add_zero] at b0
  have positive : (r 0).Nonempty := Finset.card_pos.1 (by omega)
  have small : (r 0).card ≤ 2 := by
    have bound : (r 0).card ≤ 3 := (Finset.card_le_univ _)
    by_contra hn
    have full : r 0 = Finset.univ := Finset.eq_univ_of_card (r 0) (by change (r 0).card = 3; omega)
    have all : ((Finset.univ.erase (0 : Fin 7)).filter (fun t => r t ⊆ r 0)) = Finset.univ.erase 0 := by
      rw [full]
      simp
    rw [all,full] at center
    have : 9 ≤ 5 := center
    omega
  have nozero : (0 : Fin 7) ∉ S := by
    intro member
    have all : qa_consumers A 0 = Finset.univ := by
      apply Finset.eq_univ_iff_forall.2
      intro i
      apply Finset.mem_filter.2
      refine ⟨Finset.mem_univ _,?_⟩
      by_cases equal : i = 2
      · rw [equal,missing]
        exact member
      · exact zero_mem i ((by decide +kernel : ∀ i : Fin 4, i ≠ 2 →
          i ∈ ({0,1,3} : Finset (Fin 4))) i equal)
    rw [all] at b0
    have two : (r 0).card = 2 := by
      have card : (Finset.univ : Finset (Fin 4)).card = 4 := rfl
      rw [card] at b0
      omega
    obtain ⟨q,_,_,no⟩ := qa_two_missing_unit r S allowed two center
    exact no member
  have exact_rows : ∀ i ∈ ({0,1,3} : Finset (Fin 4)), A i = qa_nb i := by
    intro i hi
    have geometry : ∀ i ∈ ({0,1,3} : Finset (Fin 4)), ∀ j ∈ ({0,1,3} : Finset (Fin 4)),
        qa_nb i ⊆ qa_nb j → i = j := by decide +kernel
    rcases choices i with eq | eq | eq | eq
    · have same := geometry i hi 0 (by decide) (eq ▸ supersets i)
      simpa [same] using eq
    · have same := geometry i hi 1 (by decide) (eq ▸ supersets i)
      simpa [same] using eq
    · have same := geometry i hi 3 (by decide) (eq ▸ supersets i)
      simpa [same] using eq
    · exact (nozero (eq ▸ zero_mem i hi)).elim
  have zero_not_subset : ∀ t : Fin 7, t ≠ 0 → ¬ r 0 ⊆ r t := by
    intro t ht sub
    have member : ∀ i ∈ ({0,1,3} : Finset (Fin 4)), t ∈ qa_nb i := by
      intro i hi
      rw [← exact_rows i hi]
      exact labels i 0 t ((by decide +kernel : ∀ i ∈ ({0,1,3} : Finset (Fin 4)),
        (0 : Fin 7) ∈ qa_nb i) i hi) positive sub
    have intersection : ∀ t : Fin 7, t ∈ qa_nb 0 → t ∈ qa_nb 1 → t ∈ qa_nb 3 → t = 0 := by decide +kernel
    exact ht (intersection t (member 0 (by decide)) (member 1 (by decide)) (member 3 (by decide)))
  have candidates : ∀ t ∈ ({1,5,6} : Finset (Fin 7)), (r t).Nonempty := by
    intro t ht
    have geometry : ∀ t ∈ ({1,5,6} : Finset (Fin 7)), ∃ i ∈ ({0,1,3} : Finset (Fin 4)),
        t ∈ qa_nb i := by decide +kernel
    obtain ⟨i,hi,hti⟩ := geometry t ht
    have two : ({i,2} : Finset (Fin 4)) ⊆ qa_consumers A t := by
      intro j hj
      rcases Finset.mem_insert.1 hj with eqj | hj
      · subst j
        exact Finset.mem_filter.2 ⟨Finset.mem_univ _,supersets i hti⟩
      · have eq := Finset.mem_singleton.1 hj
        subst j
        refine Finset.mem_filter.2 ⟨Finset.mem_univ _,?_⟩
        rw [missing]
        exact contains ((by decide +kernel : ∀ t ∈ ({1,5,6} : Finset (Fin 7)), t ∈ qa_nb 2) t ht)
    have count := Finset.card_le_card two
    have ne : i ≠ 2 := (by decide : ∀ i ∈ ({0,1,3} : Finset (Fin 4)), i ≠ 2) i hi
    rw [Finset.card_pair ne] at count
    have bt := budget t
    have nt : t ≠ 0 := (by decide : ∀ t ∈ ({1,5,6} : Finset (Fin 7)), t ≠ 0) t ht
    rw [ite_eq_right nt] at bt
    exact Finset.card_pos.1 (by omega)
  have incomparable : ∀ x ∈ ({1,5,6} : Finset (Fin 7)), ∀ t ∈ ({1,5,6} : Finset (Fin 7)),
      x ≠ t → ¬ r x ⊆ r t := by
    intro x hx t ht different subset
    have geometry : ∀ x ∈ ({1,5,6} : Finset (Fin 7)), ∀ t ∈ ({1,5,6} : Finset (Fin 7)),
        x ≠ t → ∃ i ∈ ({0,1,3} : Finset (Fin 4)), x ∈ qa_nb i ∧ t ∉ qa_nb i := by decide +kernel
    obtain ⟨i,hi,hxi,hti⟩ := geometry x hx t ht different
    have mem := labels i x t hxi (candidates x hx) subset
    rw [exact_rows i hi] at mem
    exact hti mem
  by_cases two : (r 0).card = 2
  · obtain ⟨q,_,unit,_⟩ := qa_two_missing_unit r S allowed two center
    have contain : ∀ t ∈ ({1,5,6} : Finset (Fin 7)), q ∈ r t := by
      intro t ht
      have mem : t ∈ qa_unit r q := by
        rw [unit]
        exact contains ((by decide +kernel : ∀ t ∈ ({1,5,6} : Finset (Fin 7)), t ∈ qa_nb 2) t ht)
      exact (Finset.mem_filter.1 mem).2
    exact qa_antichain_contain q (r 1) (r 5) (r 6)
      (contain 1 (by decide)) (contain 5 (by decide)) (contain 6 (by decide))
      (incomparable 1 (by decide) 5 (by decide) (by decide))
      (incomparable 5 (by decide) 1 (by decide) (by decide))
      (incomparable 1 (by decide) 6 (by decide) (by decide))
      (incomparable 6 (by decide) 1 (by decide) (by decide))
      (incomparable 5 (by decide) 6 (by decide) (by decide))
      (incomparable 6 (by decide) 5 (by decide) (by decide))
  · have one : (r 0).card = 1 := by have := Finset.card_pos.2 positive; omega
    obtain ⟨q,eq⟩ := Finset.card_eq_one.1 one
    have omitted : ∀ t ∈ ({1,5,6} : Finset (Fin 7)), q ∉ r t := by
      intro t ht member
      apply zero_not_subset t ((by decide : ∀ t ∈ ({1,5,6} : Finset (Fin 7)), t ≠ 0) t ht)
      rw [eq]
      exact Finset.singleton_subset_iff.2 member
    exact qa_antichain_omit q (r 1) (r 5) (r 6)
      (omitted 1 (by decide)) (omitted 5 (by decide)) (omitted 6 (by decide))
      (candidates 1 (by decide)) (candidates 5 (by decide)) (candidates 6 (by decide))
      (incomparable 1 (by decide) 5 (by decide) (by decide))
      (incomparable 5 (by decide) 1 (by decide) (by decide))
      (incomparable 1 (by decide) 6 (by decide) (by decide))
      (incomparable 6 (by decide) 1 (by decide) (by decide))
      (incomparable 5 (by decide) 6 (by decide) (by decide))
      (incomparable 6 (by decide) 5 (by decide) (by decide))
