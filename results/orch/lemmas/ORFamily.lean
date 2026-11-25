import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9502

variable {α : Type*} [DecidableEq α]

def Dep (F : (α → Bool) → Bool) (N : Finset α) : Prop :=
  ∀ x y : α → Bool, (∀ i ∈ N, x i = y i) → F x = F y

def ORClass (F : (α → Bool) → Bool) (S : Finset α) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ x : α → Bool,
    F (Function.update x a true) = F (Function.update x b true)

def classRest (S : Finset α) (t p q : α) : Finset α :=
  ((S.erase t).erase p).erase q

def classSub (F : (α → Bool) → Bool) (op : Bool → Bool → Bool)
    (t p q : α) : (α → Bool) → Bool :=
  fun x => F (Function.update x t (op (x p) (x q)))

lemma classRest_mem {S : Finset α} {t p q a : α} (ha : a ∈ classRest S t p q) :
    a ∈ S ∧ a ≠ t ∧ a ≠ p ∧ a ≠ q := by
  simpa only [classRest, Finset.mem_erase, and_assoc, and_left_comm, and_comm] using ha

lemma classSub_force (F : (α → Bool) → Bool) (op : Bool → Bool → Bool)
    (t p q a : α) (x : α → Bool) (hat : a ≠ t) (hap : a ≠ p) (haq : a ≠ q) :
    classSub F op t p q (Function.update x a true) =
      F (Function.update (Function.update x t (op (x p) (x q))) a true) := by
  simp only [classSub, Function.update_of_ne hap.symm, Function.update_of_ne haq.symm]
  rw [Function.update_comm hat]

lemma orClass_survive {F : (α → Bool) → Bool} {S : Finset α}
    (hclass : ORClass F S) (op : Bool → Bool → Bool) (t p q : α) :
    ORClass (classSub F op t p q) (classRest S t p q) := by
  intro a ha b hb x
  obtain ⟨ha, hat, hap, haq⟩ := classRest_mem ha
  obtain ⟨hb, hbt, hbp, hbq⟩ := classRest_mem hb
  rw [classSub_force F op t p q a x hat hap haq,
    classSub_force F op t p q b x hbt hbp hbq]
  exact hclass a ha b hb _

lemma orClass_empty (F : (α → Bool) → Bool) : ORClass F ∅ := by
  intro a ha
  simp only [Finset.notMem_empty] at ha

lemma orClass_singleton (F : (α → Bool) → Bool) (a : α) : ORClass F {a} := by
  intro b hb c hc x
  simp only [Finset.mem_singleton] at hb hc
  subst b
  subst c
  rfl

lemma orClass_subset {F : (α → Bool) → Bool} {S T : Finset α}
    (hclass : ORClass F S) (hTS : T ⊆ S) : ORClass F T := by
  exact fun a ha b hb => hclass a (hTS ha) b (hTS hb)

lemma class_ignore {F : (α → Bool) → Bool} {N : Finset α} (hd : Dep F N)
    {a : α} (ha : a ∉ N) (x : α → Bool) (v : Bool) :
    F (Function.update x a v) = F x := by
  apply hd
  intro i hi
  have hia : i ≠ a := by
    intro h
    subst i
    exact ha hi
  exact Function.update_of_ne hia v x

lemma class_or_force_old {F : (α → Bool) → Bool} {S : Finset α}
    (hclass : ORClass F S) {t p q a : α} (ht : t ∈ S)
    (ha : a ∈ classRest S t p q) (x : α → Bool) :
    classSub F (· || ·) t p q (Function.update x a true) =
      F (Function.update x t true) := by
  obtain ⟨ha, hat, hap, haq⟩ := classRest_mem ha
  rw [classSub_force F (· || ·) t p q a x hat hap haq, hclass a ha t ht]
  rw [Function.update_idem]

lemma class_or_force_left {F : (α → Bool) → Bool} {N : Finset α}
    (hd : Dep F N) {t p q : α} (hpt : p ≠ t) (hp : p ∉ N) (x : α → Bool) :
    classSub F (· || ·) t p q (Function.update x p true) =
      F (Function.update x t true) := by
  simp only [classSub, Function.update_self, Bool.true_or]
  rw [Function.update_comm hpt]
  exact class_ignore hd hp _ true

lemma class_or_force_right {F : (α → Bool) → Bool} {N : Finset α}
    (hd : Dep F N) {t p q : α} (hqt : q ≠ t) (hq : q ∉ N) (x : α → Bool) :
    classSub F (· || ·) t p q (Function.update x q true) =
      F (Function.update x t true) := by
  simp only [classSub, Function.update_self, Bool.or_true]
  rw [Function.update_comm hqt]
  exact class_ignore hd hq _ true

lemma orClass_or_inherit {F : (α → Bool) → Bool} {N S B : Finset α}
    (hd : Dep F N) (hclass : ORClass F S) {t p q : α} (ht : t ∈ S)
    (hB : ∀ b ∈ B, (b = p ∨ b = q) ∧ b ≠ t ∧ b ∉ N) :
    ORClass (classSub F (· || ·) t p q) (classRest S t p q ∪ B) := by
  have hforce : ∀ a ∈ classRest S t p q ∪ B, ∀ x : α → Bool,
      classSub F (· || ·) t p q (Function.update x a true) =
        F (Function.update x t true) := by
    intro a ha x
    rcases Finset.mem_union.mp ha with ha | ha
    · exact class_or_force_old hclass ht ha x
    · obtain ⟨ha, hat, haN⟩ := hB a ha
      rcases ha with rfl | rfl
      · exact class_or_force_left hd hat haN x
      · exact class_or_force_right hd hat haN x
  intro a ha b hb x
  exact (hforce a ha x).trans (hforce b hb x).symm

def classFresh (rest : Finset α) (p q : α) : Finset α := {p, q} \ rest

def classReused (rest : Finset α) (p q : α) : Finset α := {p, q} ∩ rest

def classOp (isOr : Bool) (x y : Bool) : Bool := if isOr then x || y else x && y

def classNext (isOr : Bool) (rest : Finset α) (t p q : α) (S : Finset α) : Finset α :=
  classRest S t p q ∪ if isOr = true ∧ t ∈ S then classFresh rest p q else ∅

def classFamilyNext (isOr : Bool) (rest : Finset α) (t p q : α)
    (K : Finset (Finset α)) : Finset (Finset α) :=
  K.image (classNext isOr rest t p q) ∪ (classReused rest p q).image (fun a => {a})

def classUnion (K : Finset (Finset α)) : Finset α := K.biUnion id

lemma classNext_closed {F : (α → Bool) → Bool} {rest S : Finset α} {t p q : α}
    (hd : Dep F (insert t rest)) (hclass : ORClass F S)
    (htp : t ≠ p) (htq : t ≠ q) (isOr : Bool) :
    ORClass (classSub F (classOp isOr) t p q) (classNext isOr rest t p q S) := by
  by_cases h : isOr = true ∧ t ∈ S
  · rcases h with ⟨rfl, ht⟩
    simp only [classNext, ht, and_self, ite_true]
    apply orClass_or_inherit hd hclass ht
    intro b hb
    simp only [classFresh, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hb
    have hbt : b ≠ t := by
      rcases hb.1 with rfl | rfl
      · exact htp.symm
      · exact htq.symm
    exact ⟨hb.1, hbt, by simp [hbt, hb.2]⟩
  · simp only [classNext, h, ite_false, Finset.union_empty]
    exact orClass_survive hclass (classOp isOr) t p q

lemma classFamilyNext_closed {F : (α → Bool) → Bool} {rest : Finset α} {t p q : α}
    {K : Finset (Finset α)} (hd : Dep F (insert t rest))
    (hK : ∀ S ∈ K, ORClass F S) (htp : t ≠ p) (htq : t ≠ q) (isOr : Bool) :
    ∀ S ∈ classFamilyNext isOr rest t p q K,
      ORClass (classSub F (classOp isOr) t p q) S := by
  intro S hS
  rcases Finset.mem_union.mp hS with hS | hS
  · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
    exact classNext_closed hd (hK T hT) htp htq isOr
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hS
    exact orClass_singleton _ a

lemma classNext_subset {rest S : Finset α} {t p q : α}
    (hS : S ⊆ insert t rest) (isOr : Bool) :
    classNext isOr rest t p q S ⊆ insert p (insert q rest) := by
  intro a ha
  rcases Finset.mem_union.mp ha with ha | ha
  · obtain ⟨ha, hat, _, _⟩ := classRest_mem ha
    have har : a ∈ rest := (Finset.mem_insert.mp (hS ha)).resolve_left hat
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem har)
  · by_cases h : isOr = true ∧ t ∈ S
    · rw [ite_eq_left h] at ha
      simp only [classFresh, Finset.mem_sdiff, Finset.mem_insert,
        Finset.mem_singleton] at ha
      rcases ha.1 with rfl | rfl <;> simp
    · simp only [h, ite_false, Finset.notMem_empty] at ha

lemma classFamilyNext_subset {rest : Finset α} {t p q : α} {K : Finset (Finset α)}
    (hK : ∀ S ∈ K, S ⊆ insert t rest) (isOr : Bool) :
    ∀ S ∈ classFamilyNext isOr rest t p q K, S ⊆ insert p (insert q rest) := by
  intro S hS
  rcases Finset.mem_union.mp hS with hS | hS
  · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
    exact classNext_subset (hK T hT) isOr
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hS
    intro b hb
    have hba := Finset.mem_singleton.mp hb
    subst b
    have har : a ∈ rest := (Finset.mem_inter.mp ha).2
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem har)

lemma classFamilyNext_card (isOr : Bool) (rest : Finset α) (t p q : α)
    (K : Finset (Finset α)) :
    (classFamilyNext isOr rest t p q K).card ≤ K.card + (classReused rest p q).card := by
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le))

lemma classUnion_mem (K : Finset (Finset α)) (a : α) :
    a ∈ classUnion K ↔ ∃ S ∈ K, a ∈ S := by
  simp only [classUnion, Finset.mem_biUnion, id_eq]

lemma classFamilyUnion_mem (isOr : Bool) (rest : Finset α) (t p q a : α)
    (K : Finset (Finset α)) :
    a ∈ classUnion (classFamilyNext isOr rest t p q K) ↔
      (∃ S ∈ K, a ∈ classNext isOr rest t p q S) ∨ a ∈ classReused rest p q := by
  rw [classUnion_mem]
  constructor
  · rintro ⟨S, hS, ha⟩
    rcases Finset.mem_union.mp hS with hS | hS
    · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
      exact Or.inl ⟨T, hT, ha⟩
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hS
      have hab := Finset.mem_singleton.mp ha
      subst a
      exact Or.inr hb
  · rintro (⟨S, hS, ha⟩ | ha)
    · exact ⟨_, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨S, hS, rfl⟩), ha⟩
    · exact ⟨{a}, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩),
        Finset.mem_singleton_self _⟩

lemma classFamilyNext_union (isOr : Bool) (rest : Finset α) (t p q : α)
    (K : Finset (Finset α)) (hK : ∀ S ∈ K, S ⊆ insert t rest) :
    classUnion (classFamilyNext isOr rest t p q K) =
      ((classUnion K).erase t ∪ classReused rest p q) ∪
        if isOr = true ∧ t ∈ classUnion K then classFresh rest p q else ∅ := by
  ext a
  rw [classFamilyUnion_mem]
  constructor
  · rintro (⟨S, hS, ha⟩ | ha)
    · rcases Finset.mem_union.mp ha with ha | ha
      · obtain ⟨ha, hat, _, _⟩ := classRest_mem ha
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_erase.mpr ⟨hat, (classUnion_mem K a).mpr ⟨S, hS, ha⟩⟩))
      · by_cases h : isOr = true ∧ t ∈ S
        · have h' : isOr = true ∧ t ∈ classUnion K :=
            ⟨h.1, (classUnion_mem K t).mpr ⟨S, hS, h.2⟩⟩
          apply Finset.mem_union_right
          rw [ite_eq_left h']
          rwa [ite_eq_left h] at ha
        · simp only [h, ite_false, Finset.notMem_empty] at ha
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ ha)
  · intro ha
    rcases Finset.mem_union.mp ha with ha | ha
    · rcases Finset.mem_union.mp ha with ha | ha
      · obtain ⟨hat, ha⟩ := Finset.mem_erase.mp ha
        obtain ⟨S, hS, haS⟩ := (classUnion_mem K a).mp ha
        by_cases hapq : a = p ∨ a = q
        · apply Or.inr
          have har : a ∈ rest := (Finset.mem_insert.mp (hK S hS haS)).resolve_left hat
          exact Finset.mem_inter.mpr ⟨by simpa only [Finset.mem_insert,
            Finset.mem_singleton] using hapq, har⟩
        · apply Or.inl
          refine ⟨S, hS, Finset.mem_union_left _ ?_⟩
          have hap : a ≠ p := fun h => hapq (Or.inl h)
          have haq : a ≠ q := fun h => hapq (Or.inr h)
          simp only [classRest, Finset.mem_erase]
          exact ⟨haq, hap, hat, haS⟩
      · exact Or.inr ha
    · by_cases h : isOr = true ∧ t ∈ classUnion K
      · rw [ite_eq_left h] at ha
        obtain ⟨S, hS, htS⟩ := (classUnion_mem K t).mp h.2
        apply Or.inl
        refine ⟨S, hS, Finset.mem_union_right _ ?_⟩
        rw [ite_eq_left ⟨h.1, htS⟩]
        exact ha
      · simp only [h, ite_false, Finset.notMem_empty] at ha

lemma class_partition_card (rest : Finset α) (p q : α) (hpq : p ≠ q) :
    (classFresh rest p q).card + (classReused rest p q).card = 2 := by
  simpa [classFresh, classReused, hpq] using
    Finset.card_sdiff_add_card_inter ({p, q} : Finset α) rest

lemma class_frontier_card (rest : Finset α) (p q : α) :
    (insert p (insert q rest)).card = rest.card + (classFresh rest p q).card := by
  simpa [classFresh, Nat.add_comm] using
    (Finset.card_sdiff_add_card ({p, q} : Finset α) rest).symm

lemma classFamilyNext_growth (isOr : Bool) (rest : Finset α) (t p q : α)
    (K : Finset (Finset α)) (ht : t ∉ rest) (hpq : p ≠ q) :
    (insert p (insert q rest)).card + (classFamilyNext isOr rest t p q K).card ≤
      (insert t rest).card + K.card + 1 := by
  have hfamily := classFamilyNext_card isOr rest t p q K
  have hparts := class_partition_card rest p q hpq
  have hfront := class_frontier_card rest p q
  rw [Finset.card_insert_of_notMem ht]
  omega

end PEqualNP.Outside.L_meta_9502
