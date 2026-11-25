import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2583

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK

def incidence {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (z : Fin (N + N) → Bool) : Bool :=
  decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧
    z (Fin.natAdd N l) = true)

lemma opposite_ne {N : Nat} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have hv := congrArg Fin.val h
  change p.val = N + l.val at hv
  have hp := p.isLt
  omega

lemma incidence_set_true {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (S : Finset (Fin (N + N))) :
    incidence I (setInput S) = true ↔
      ∃ p l : Fin N, I p l ∧ Fin.castAdd N p ∈ S ∧ Fin.natAdd N l ∈ S := by
  simp [incidence, setInput]

lemma incidence_pair_true {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (p l : Fin N) (hil : I p l) :
    incidence I (setInput {Fin.castAdd N p, Fin.natAdd N l}) = true := by
  exact (incidence_set_true I _).2 ⟨p, l, hil, by simp, by simp⟩

lemma point_mem_pair {N : Nat} (p p' l : Fin N)
    (h : Fin.castAdd N p' ∈ ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N)))) :
    p' = p := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h
  · exact Fin.ext (congrArg (fun x : Fin (N + N) => x.val) h)
  · exact False.elim (opposite_ne p' l h)

lemma line_mem_pair {N : Nat} (p l l' : Fin N)
    (h : Fin.natAdd N l' ∈ ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N)))) :
    l' = l := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h
  · exact False.elim (opposite_ne p l' h.symm)
  · apply Fin.ext
    have hv := congrArg Fin.val h
    change N + l'.val = N + l.val at hv
    omega

lemma prime_incidence_pair {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (computes : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = incidence I z)
    (S : Finset (Fin (N + N))) :
    IsPrimeImplicant (N + N) C S ↔
      ∃ p l : Fin N, I p l ∧ S = {Fin.castAdd N p, Fin.natAdd N l} := by
  constructor
  · rintro ⟨htrue, hminimal⟩
    rw [computes] at htrue
    obtain ⟨p, l, hil, hp, hl⟩ := (incidence_set_true I S).1 htrue
    refine ⟨p, l, hil, ?_⟩
    have hsub : ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) ⊆ S := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv
      rcases hv with rfl | rfl <;> assumption
    by_contra hne
    have hproper : ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) ⊂ S := by
      exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm hne⟩
    have hfalse := hminimal _ (Finset.mem_ssubsets.mpr hproper)
    rw [computes, incidence_pair_true I p l hil] at hfalse
    cases hfalse
  · rintro ⟨p, l, hil, rfl⟩
    constructor
    · rw [computes]
      exact incidence_pair_true I p l hil
    · intro T hT
      rw [computes]
      apply Bool.eq_false_iff.mpr
      intro htrue
      obtain ⟨p', l', hi', hp', hl'⟩ := (incidence_set_true I T).1 htrue
      have hproper := Finset.mem_ssubsets.mp hT
      have hp := point_mem_pair p p' l (hproper.subset hp')
      have hl := line_mem_pair p l l' (hproper.subset hl')
      subst p'
      subst l'
      have hback : ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) ⊆ T := by
        intro v hv
        simp only [Finset.mem_insert, Finset.mem_singleton] at hv
        rcases hv with rfl | rfl <;> assumption
      exact (Finset.ssubset_iff_subset_ne.mp hproper).2 (Finset.Subset.antisymm hproper.subset hback)

lemma prime_incidence_card_two {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (computes : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = incidence I z)
    (S : Finset (Fin (N + N))) (hprime : IsPrimeImplicant (N + N) C S) : S.card = 2 := by
  obtain ⟨p, l, _, rfl⟩ := (prime_incidence_pair I C computes S).1 hprime
  have hnot : Fin.castAdd N p ∉ ({Fin.natAdd N l} : Finset (Fin (N + N))) := by
    simpa only [Finset.mem_singleton] using opposite_ne p l
  rw [Finset.card_insert_of_notMem hnot, Finset.card_singleton]

lemma read_one_iff_incident_pairs {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (computes : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = incidence I z) :
    IsReadK (N + N) C 1 ↔ ∀ p l : Fin N, I p l →
      readsAtMost C (N + N) (setList {Fin.castAdd N p, Fin.natAdd N l}) 1 = true := by
  constructor
  · intro h p l hil
    exact h _ ((prime_incidence_pair I C computes _).2 ⟨p, l, hil, rfl⟩)
  · intro h S hs
    obtain ⟨p, l, hil, rfl⟩ := (prime_incidence_pair I C computes S).1 hs
    exact h p l hil


-- The sorted-list argument is adapted from the checked L-meta-7639 proof.
lemma setList_pair_sorted {n : Nat} (a b : Fin n) (hab : a < b) :
    setList ({a, b} : Finset (Fin n)) = [a.val, b.val] := by
  have key : ∀ x y : Fin n, x < y → y < x → x = y :=
    fun x y h1 h2 => absurd h1 (lt_asymm h2)
  have hp1 : List.Pairwise (fun x y : Fin n => x < y)
      ((List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n))))) :=
    List.Pairwise.filter _ (List.pairwise_lt_finRange n)
  have hp2 : List.Pairwise (fun x y : Fin n => x < y) [a, b] := by simp [hab]
  have hperm : List.Perm
      ((List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n))))) [a, b] := by
    apply List.perm_of_nodup_nodup_toFinset_eq
    · exact List.Nodup.filter _ (List.nodup_finRange n)
    · simp [ne_of_lt hab]
    · ext x
      simp
  have h : (List.finRange n).filter (fun i => decide (i ∈ ({a, b} : Finset (Fin n)))) = [a, b] :=
    List.Perm.eq_of_pairwise (fun x y _ _ => key x y) hp1 hp2 hperm
  unfold setList
  rw [h]
  rfl

lemma setList_incidence_pair {N : Nat} (p l : Fin N) :
    setList ({Fin.castAdd N p, Fin.natAdd N l} : Finset (Fin (N + N))) =
      [p.val, N + l.val] := by
  apply setList_pair_sorted
  change p.val < N + l.val
  have hp := p.isLt
  omega

lemma read_one_iff_pair_vectors {N : Nat} (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : Circuit) (computes : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = incidence I z) :
    IsReadK (N + N) C 1 ↔
      ∀ p l : Fin N, I p l → readsAtMost C (N + N) [p.val, N + l.val] 1 = true := by
  rw [read_one_iff_incident_pairs I C computes]
  simp only [setList_incidence_pair]

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

lemma absorbed_context (context : Bool → Bool) (u t : Bool)
    (below : t = true → context (u || t) = true) :
    context (u || t) = (context u || t) := by
  cases t
  · simp
  · simpa using below rfl

lemma repeated_input_context (context : Bool → Bool) (u a b : Bool)
    (below : (a && b) = true → context ((u || a) && (u || b)) = true) :
    context ((u || a) && (u || b)) = (context u || (a && b)) := by
  have distribution : ((u || a) && (u || b)) = (u || (a && b)) := by
    cases u <;> cases a <;> cases b <;> rfl
  rw [distribution] at below ⊢
  exact absorbed_context context u (a && b) below

lemma extract_repeated_input {α : Type} (target u a b : α → Bool)
    (context : α → Bool → Bool)
    (computes : ∀ x, context x ((u x || a x) && (u x || b x)) = target x)
    (below : ∀ x, (a x && b x) = true → target x = true) :
    ∀ x, (context x (u x) || (a x && b x)) = target x := by
  intro x
  rw [← computes x]
  symm
  apply repeated_input_context
  intro h
  rw [computes x]
  exact below x h

end PEqualNP.Outside.L_meta_2583
