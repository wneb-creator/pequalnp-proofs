import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

def linePoints {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (l : Fin N) : Finset (Fin N) := Finset.univ.filter (fun p => I p l)

def pointLines {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (p : Fin N) : Finset (Fin N) := Finset.univ.filter (fun l => I p l)

lemma rectangle_thin {N : Nat} (I : Fin N → Fin N → Prop)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    {p p' l l' : Fin N} (hpl : I p l) (hp'l : I p' l)
    (hpl' : I p l') (hp'l' : I p' l') : p = p' ∨ l = l' := by
  by_cases hp : p = p'
  · exact Or.inl hp
  · exact Or.inr ((unique p p' hp).unique ⟨hpl,hp'l⟩ ⟨hpl',hp'l'⟩)

lemma line_intersection_small {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    {l l' : Fin N} (hne : l ≠ l') :
    (linePoints I l ∩ linePoints I l').card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp p' hp'
  have h := Finset.mem_inter.mp hp
  have h' := Finset.mem_inter.mp hp'
  exact (rectangle_thin I unique (Finset.mem_filter.mp h.1).2
    (Finset.mem_filter.mp h'.1).2 (Finset.mem_filter.mp h.2).2
    (Finset.mem_filter.mp h'.2).2).resolve_right hne

lemma point_intersection_small {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    {p p' : Fin N} (hne : p ≠ p') :
    (pointLines I p ∩ pointLines I p').card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro l hl l' hl'
  have h := Finset.mem_inter.mp hl
  have h' := Finset.mem_inter.mp hl'
  exact (rectangle_thin I unique (Finset.mem_filter.mp h.1).2
    (Finset.mem_filter.mp h.2).2 (Finset.mem_filter.mp h'.1).2
    (Finset.mem_filter.mp h'.2).2).resolve_left hne

lemma biclique_is_star {N : Nat} (I : Fin N → Fin N → Prop)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (A B : Finset (Fin N)) (cross : ∀ p ∈ A, ∀ l ∈ B, I p l) :
    A.card ≤ 1 ∨ B.card ≤ 1 := by
  by_cases small : A.card ≤ 1
  · exact Or.inl small
  · right
    obtain ⟨p,hp,p',hp',hne⟩ := Finset.one_lt_card.mp (by omega : 1 < A.card)
    apply Finset.card_le_one.mpr
    intro l hl l' hl'
    exact (rectangle_thin I unique (cross p hp l hl) (cross p' hp' l hl)
      (cross p hp l' hl') (cross p' hp' l' hl')).resolve_left hne

lemma line_erase_partition {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p : Fin N) :
    (pointLines I p).biUnion (fun l => (linePoints I l).erase p) = Finset.univ.erase p := by
  ext r
  constructor
  · intro hr
    obtain ⟨l,_,hl⟩ := Finset.mem_biUnion.mp hr
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hl).1,Finset.mem_univ _⟩
  · intro hr
    have hne : p ≠ r := (Finset.mem_erase.mp hr).1.symm
    obtain ⟨l,hl,_⟩ := unique p r hne
    apply Finset.mem_biUnion.mpr
    refine ⟨l,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl.1⟩,?_⟩
    exact Finset.mem_erase.mpr ⟨hne.symm,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hl.2⟩⟩

lemma line_erase_disjoint {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p : Fin N) :
    (↑(pointLines I p) : Set (Fin N)).PairwiseDisjoint
      (fun l => (linePoints I l).erase p) := by
  intro l hl l' hl' hne
  apply Finset.disjoint_left.mpr
  intro r hr hr'
  have hp : I p l := (Finset.mem_filter.mp hl).2
  have hp' : I p l' := (Finset.mem_filter.mp hl').2
  have rr := Finset.mem_erase.mp hr
  have rr' := Finset.mem_erase.mp hr'
  have heq := (rectangle_thin I unique hp (Finset.mem_filter.mp rr.2).2
    hp' (Finset.mem_filter.mp rr'.2).2).resolve_left rr.1.symm
  exact hne heq

lemma point_degree {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q^2+q+1)
    (lineSize : ∀ l : Fin N, (linePoints I l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (p : Fin N) : (pointLines I p).card = q+1 := by
  have parts : ∀ l ∈ pointLines I p, ((linePoints I l).erase p).card = q := by
    intro l hl
    have hp : p ∈ linePoints I l :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hl).2⟩
    rw [Finset.card_erase_of_mem hp,lineSize]
    omega
  have count := Finset.card_biUnion (line_erase_disjoint I unique p)
  rw [line_erase_partition I unique p,Finset.card_erase_of_mem (Finset.mem_univ p)] at count
  simp only [Finset.card_univ,Fintype.card_fin] at count
  have sumEq : ∑ l ∈ pointLines I p, ((linePoints I l).erase p).card =
      (pointLines I p).card * q := by
    rw [Finset.sum_congr rfl parts]
    simp
  rw [sumEq] at count
  have count' : q^2+q = (pointLines I p).card * q := by omega
  have hpq : 0 < q := by omega
  nlinarith


lemma star_cover_size {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q^2+q+1)
    (lineSize : ∀ l : Fin N, (linePoints I l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (A B : Finset (Fin N)) (cover : ∀ p l, I p l → p ∈ A ∨ l ∈ B) :
    N ≤ A.card + B.card := by
  have rows (p : Fin N) : (∑ l : Fin N, if I p l then 1 else 0) = q+1 := by
    simpa only [pointLines,Finset.card_filter] using point_degree I hq hN lineSize unique p
  have columns (l : Fin N) : (∑ p : Fin N, if I p l then 1 else 0) = q+1 := by
    simpa only [linePoints,Finset.card_filter] using lineSize l
  have total : (∑ p : Fin N, ∑ l : Fin N, if I p l then 1 else 0) = N*(q+1) := by
    simp_rw [rows]
    simp
  have left : (∑ p : Fin N, ∑ l : Fin N, if p ∈ A ∧ I p l then 1 else 0) = A.card*(q+1) := by
    have inner (p : Fin N) : (∑ l : Fin N, if p ∈ A ∧ I p l then 1 else 0) =
        if p ∈ A then q+1 else 0 := by
      by_cases hp : p ∈ A
      · simp only [hp,true_and,ite_true]
        exact rows p
      · simp [hp]
    simp_rw [inner]
    simp
  have right : (∑ p : Fin N, ∑ l : Fin N, if l ∈ B ∧ I p l then 1 else 0) = B.card*(q+1) := by
    rw [Finset.sum_comm]
    have inner (l : Fin N) : (∑ p : Fin N, if l ∈ B ∧ I p l then 1 else 0) =
        if l ∈ B then q+1 else 0 := by
      by_cases hl : l ∈ B
      · simp only [hl,true_and,ite_true]
        exact columns l
      · simp [hl]
    simp_rw [inner]
    simp
  have localBound (p l : Fin N) : (if I p l then 1 else 0) ≤
      (if p ∈ A ∧ I p l then 1 else 0) + (if l ∈ B ∧ I p l then 1 else 0) := by
    by_cases h : I p l
    · rcases cover p l h with hp | hl
      · simp [h,hp]
      · simp [h,hl]
    · simp [h]
  have summed := Finset.sum_le_sum (s := Finset.univ) (fun p _ =>
    Finset.sum_le_sum (s := Finset.univ) (fun l _ => localBound p l))
  simp only [Finset.sum_add_distrib] at summed
  rw [total,left,right] at summed
  nlinarith


def allIncidences {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I] :
    Finset (Fin N × Fin N) :=
  Finset.univ.biUnion (fun p => {p} ×ˢ pointLines I p)

lemma mem_allIncidences {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (p l : Fin N) : (p,l) ∈ allIncidences I ↔ I p l := by
  simp [allIncidences,pointLines]

lemma allIncidences_card {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q^2+q+1)
    (lineSize : ∀ l : Fin N, (linePoints I l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) :
    (allIncidences I).card = N*(q+1) := by
  have disj : (↑(Finset.univ : Finset (Fin N)) : Set (Fin N)).PairwiseDisjoint
      (fun p => ({p} : Finset (Fin N)) ×ˢ pointLines I p) := by
    intro p _ p' _ ne
    apply Finset.disjoint_left.mpr
    intro e he he'
    have hp : e.1 = p := Finset.mem_singleton.mp (Finset.mem_product.mp he).1
    have hp' : e.1 = p' := Finset.mem_singleton.mp (Finset.mem_product.mp he').1
    exact ne (hp.symm.trans hp')
  unfold allIncidences
  rw [Finset.card_biUnion disj]
  simp only [Finset.card_product,Finset.card_singleton,Nat.one_mul]
  simp_rw [point_degree I hq hN lineSize unique]
  simp

lemma rectangle_capacity {q N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q^2+q+1)
    (lineSize : ∀ l : Fin N, (linePoints I l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (A B : Finset (Fin N)) (cross : ∀ p ∈ A, ∀ l ∈ B, I p l) :
    A.card * B.card ≤ q+1 := by
  by_cases ha : A.Nonempty
  · by_cases hb : B.Nonempty
    · obtain ⟨p,hp⟩ := ha
      obtain ⟨l,hl⟩ := hb
      rcases biclique_is_star I unique A B cross with smallA | smallB
      · have sub : B ⊆ pointLines I p := by
          intro t ht
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,cross p hp t ht⟩
        have bound := Finset.card_le_card sub
        rw [point_degree I hq hN lineSize unique p] at bound
        have pos := Finset.card_pos.mpr ⟨p,hp⟩
        have one : A.card = 1 := by omega
        simpa only [one,Nat.one_mul] using bound
      · have sub : A ⊆ linePoints I l := by
          intro t ht
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,cross t ht l hl⟩
        have bound := Finset.card_le_card sub
        rw [lineSize l] at bound
        have pos := Finset.card_pos.mpr ⟨l,hl⟩
        have one : B.card = 1 := by omega
        simpa only [one,Nat.mul_one] using bound
    · have empty : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hb
      simp [empty]
  · have empty : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp ha
    simp [empty]

lemma rectangle_weight {N : Nat} (I : Fin N → Fin N → Prop)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (A B : Finset (Fin N)) (ha : A.Nonempty) (hb : B.Nonempty)
    (cross : ∀ p ∈ A, ∀ l ∈ B, I p l) :
    A.card + B.card = A.card * B.card + 1 := by
  have pa := Finset.card_pos.mpr ha
  have pb := Finset.card_pos.mpr hb
  rcases biclique_is_star I unique A B cross with h | h
  · have : A.card = 1 := by omega
    simp [this,Nat.add_comm]
  · have : B.card = 1 := by omega
    simp [this]

lemma rectangle_cover_weight {q N k : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hN : N = q^2+q+1)
    (lineSize : ∀ l : Fin N, (linePoints I l).card = q+1)
    (unique : ∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l)
    (A B : Fin k → Finset (Fin N))
    (nonemptyA : ∀ i, (A i).Nonempty) (nonemptyB : ∀ i, (B i).Nonempty)
    (cross : ∀ i p, p ∈ A i → ∀ l, l ∈ B i → I p l)
    (cover : ∀ p l, I p l → ∃ i, p ∈ A i ∧ l ∈ B i) :
    N*(q+2) ≤ ∑ i : Fin k, ((A i).card + (B i).card) := by
  have sub : allIncidences I ⊆ Finset.univ.biUnion (fun i => A i ×ˢ B i) := by
    intro e he
    obtain ⟨i,hi,hi'⟩ := cover e.1 e.2 ((mem_allIncidences I e.1 e.2).mp he)
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,Finset.mem_product.mpr ⟨hi,hi'⟩⟩
  have covered : N*(q+1) ≤ ∑ i : Fin k, (A i).card * (B i).card := by
    calc
      N*(q+1) = (allIncidences I).card := (allIncidences_card I hq hN lineSize unique).symm
      _ ≤ (Finset.univ.biUnion (fun i => A i ×ˢ B i)).card := Finset.card_le_card sub
      _ ≤ ∑ i : Fin k, (A i ×ˢ B i).card := Finset.card_biUnion_le
      _ = ∑ i : Fin k, (A i).card * (B i).card := by simp only [Finset.card_product]
  have capacity : (∑ i : Fin k, (A i).card * (B i).card) ≤ k*(q+1) := by
    calc
      _ ≤ ∑ _i : Fin k, (q+1) := Finset.sum_le_sum (fun i _ =>
        rectangle_capacity I hq hN lineSize unique (A i) (B i) (cross i))
      _ = k*(q+1) := by simp
  have number : N ≤ k := by nlinarith
  have weight : (∑ i : Fin k, ((A i).card + (B i).card)) =
      (∑ i : Fin k, (A i).card * (B i).card) + k := by
    simp_rw [rectangle_weight I unique _ _ (nonemptyA _) (nonemptyB _) (cross _)]
    simp [Finset.sum_add_distrib]
  rw [weight]
  nlinarith

end PEqualNP.Outside.L_meta_2583
