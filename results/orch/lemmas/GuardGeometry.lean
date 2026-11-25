import GeometryRowsDefs
import GuardCharging

namespace PEqualNP.Outside.L_meta_1896_aux.GuardGeometry

abbrev incidence := AllRows.incidence

def pencil (p : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter fun l => incidence p l

def residual (p : Fin 13) (A : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun q => q ≠ p ∧ Disjoint A (pencil q)

abbrev sameRay (p q r : Fin 13) : Prop :=
  ∃ l : Fin 13, incidence p l ∧ incidence q l ∧ incidence r l

abbrev IsFourCap (N : Finset (Fin 13)) : Prop :=
  N.card = 4 ∧ ∀ p : Fin 13, (N ∩ pencil p).card ≤ 2

def fourCaps : Finset (Finset (Fin 13)) :=
  Finset.univ.filter IsFourCap

def capFor (p q r : Fin 13) : Finset (Fin 13) :=
  Finset.univ.filter fun l =>
    ¬incidence p l ∧ ¬incidence q l ∧ ¬incidence r l

def avoidingPoints (N : Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun p => Disjoint N (pencil p)

def partBound (A : Finset (Fin 13)) : Nat :=
  if A.card = 0 then 3 else 2

lemma mem_pencil (p l : Fin 13) : l ∈ pencil p ↔ incidence p l := by
  simp [pencil]

lemma mem_residual (p q : Fin 13) (A : Finset (Fin 13)) :
    q ∈ residual p A ↔ q ≠ p ∧ Disjoint A (pencil q) := by
  simp [residual]

lemma mem_fourCaps (N : Finset (Fin 13)) : N ∈ fourCaps ↔ IsFourCap N := by
  simp [fourCaps]

lemma mem_avoidingPoints (N : Finset (Fin 13)) (p : Fin 13) :
    p ∈ avoidingPoints N ↔ Disjoint N (pencil p) := by
  simp [avoidingPoints]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pencil_card : ∀ p : Fin 13, (pencil p).card = 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma pencil_inter_card : ∀ p q : Fin 13, p ≠ q →
    (pencil p ∩ pencil q).card = 1 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_empty_card : ∀ p : Fin 13, (residual p ∅).card = 12 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_singleton_card : ∀ p a : Fin 13, a ∉ pencil p →
    (residual p {a}).card = 8 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_pair_card : ∀ p a b : Fin 13,
    a ≠ b → a ∉ pencil p → b ∉ pencil p →
    (residual p {a, b}).card = 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_empty_ray_card : ∀ p q : Fin 13, q ≠ p →
    ((residual p ∅).filter (sameRay p q)).card = 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_singleton_ray_card : ∀ p a q : Fin 13,
    a ∉ pencil p → q ≠ p →
    ((residual p {a}).filter (sameRay p q)).card = 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma capFor_spec : ∀ p q r : Fin 13,
    q ≠ p → r ≠ p → ¬sameRay p q r →
    IsFourCap (capFor p q r) ∧ avoidingPoints (capFor p q r) = {p, q, r} := by
  decide +kernel

lemma residual_mono (p : Fin 13) {A B : Finset (Fin 13)} (hAB : A ⊆ B) :
    residual p B ⊆ residual p A := by
  intro q hq
  obtain ⟨hqp, hB⟩ := (mem_residual p q B).mp hq
  exact (mem_residual p q A).mpr ⟨hqp, hB.mono_left hAB⟩

lemma capFor_disjoint (p q r : Fin 13) :
    Disjoint (capFor p q r) (pencil p) := by
  apply Finset.disjoint_left.mpr
  intro l hl hp
  exact (Finset.mem_filter.mp hl).2.1 ((mem_pencil p l).mp hp)

lemma subset_capFor (p q r : Fin 13) (A : Finset (Fin 13))
    (hp : Disjoint A (pencil p)) (hq : Disjoint A (pencil q))
    (hr : Disjoint A (pencil r)) : A ⊆ capFor p q r := by
  intro l hl
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ l, ?_⟩
  refine ⟨?_, ?_, ?_⟩
  · intro h
    exact (Finset.disjoint_left.mp hp) hl ((mem_pencil p l).mpr h)
  · intro h
    exact (Finset.disjoint_left.mp hq) hl ((mem_pencil q l).mpr h)
  · intro h
    exact (Finset.disjoint_left.mp hr) hl ((mem_pencil r l).mpr h)

lemma residual_ray_bound (p : Fin 13) (A : Finset (Fin 13))
    (outside : Disjoint A (pencil p)) :
    ∀ q ∈ residual p A,
      ((residual p A).filter (sameRay p q)).card ≤ partBound A := by
  intro q hq
  have hqp := ((mem_residual p q A).mp hq).1
  by_cases hz : A.card = 0
  · have hA : A = ∅ := Finset.card_eq_zero.mp hz
    subst A
    simpa [partBound] using (le_of_eq (residual_empty_ray_card p q hqp))
  · obtain ⟨a, ha⟩ := Finset.card_ne_zero.mp hz
    have hpa : a ∉ pencil p := by
      intro hp
      exact (Finset.disjoint_left.mp outside) ha hp
    have hsub : residual p A ⊆ residual p {a} :=
      residual_mono p (Finset.singleton_subset_iff.mpr ha)
    have hfilter : (residual p A).filter (sameRay p q) ⊆
        (residual p {a}).filter (sameRay p q) := by
      intro r hr
      obtain ⟨hrA, hray⟩ := Finset.mem_filter.mp hr
      exact Finset.mem_filter.mpr ⟨hsub hrA, hray⟩
    have hbound : ((residual p A).filter (sameRay p q)).card ≤ 2 := by
      calc
        _ ≤ ((residual p {a}).filter (sameRay p q)).card := Finset.card_le_card hfilter
        _ = 2 := residual_singleton_ray_card p a q hpa hqp
    simpa [partBound, hz] using hbound

lemma residual_geometry_bound (p : Fin 13) (A : Finset (Fin 13))
    (small : A.card ≤ 2) (outside : Disjoint A (pencil p)) :
    9 + partBound A ≤ 3 * A.card + (residual p A).card := by
  by_cases h0 : A.card = 0
  · have hs : (residual p A).card = 12 := by
      rw [Finset.card_eq_zero.mp h0]
      exact residual_empty_card p
    simp only [partBound, if_pos h0]
    omega
  · by_cases h1 : A.card = 1
    · obtain ⟨a, hA⟩ := Finset.card_eq_one.mp h1
      have ha : a ∈ A := by rw [hA]; simp
      have hpa : a ∉ pencil p := by
        intro hp
        exact (Finset.disjoint_left.mp outside) ha hp
      have hs : (residual p A).card = 8 := by
        rw [hA]
        exact residual_singleton_card p a hpa
      simp only [partBound, if_neg h0]
      omega
    · have h2 : A.card = 2 := by omega
      obtain ⟨a, b, hab, hA⟩ := Finset.card_eq_two.mp h2
      have ha : a ∈ A := by rw [hA]; simp
      have hb : b ∈ A := by rw [hA]; simp
      have hpa : a ∉ pencil p := by
        intro hp
        exact (Finset.disjoint_left.mp outside) ha hp
      have hpb : b ∉ pencil p := by
        intro hp
        exact (Finset.disjoint_left.mp outside) hb hp
      have hs : (residual p A).card = 5 := by
        rw [hA]
        exact residual_pair_card p a b hab hpa hpb
      simp only [partBound, if_neg h0]
      omega

lemma residual_cover_bound
    (p : Fin 13) (A Q : Finset (Fin 13))
    (small : A.card ≤ 2) (outside : Disjoint A (pencil p)) (other : p ∉ Q)
    (covers : ∀ N ∈ fourCaps, Disjoint N (pencil p) → A ⊆ N →
      ∃ q ∈ Q, Disjoint N (pencil q)) :
    9 ≤ 3 * A.card + Q.card := by
  have hcover : ∀ q ∈ residual p A, ∀ r ∈ residual p A,
      ¬sameRay p q r → q ∈ Q ∨ r ∈ Q := by
    intro q hq r hr hdifferent
    obtain ⟨hqp, hAq⟩ := (mem_residual p q A).mp hq
    obtain ⟨hrp, hAr⟩ := (mem_residual p r A).mp hr
    obtain ⟨hcap, havoid⟩ := capFor_spec p q r hqp hrp hdifferent
    have hN : capFor p q r ∈ fourCaps := (mem_fourCaps _).mpr hcap
    have hAN : A ⊆ capFor p q r := subset_capFor p q r A outside hAq hAr
    obtain ⟨s, hsQ, hNs⟩ := covers (capFor p q r) hN (capFor_disjoint p q r) hAN
    have hs : s ∈ avoidingPoints (capFor p q r) := (mem_avoidingPoints _ s).mpr hNs
    rw [havoid] at hs
    simp only [Finset.mem_insert, Finset.mem_singleton] at hs
    rcases hs with rfl | rfl | rfl
    · exact (other hsQ).elim
    · exact Or.inl hsQ
    · exact Or.inr hsQ
  exact GuardCharging.residual_cover_count (residual p A) Q (sameRay p)
    (partBound A) A.card (residual_ray_bound p A outside) hcover
    (residual_geometry_bound p A small outside)

end PEqualNP.Outside.L_meta_1896_aux.GuardGeometry
