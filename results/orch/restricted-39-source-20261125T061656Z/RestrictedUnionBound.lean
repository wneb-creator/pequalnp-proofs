import GuardGeometry
import PureUnionAncestry

namespace PEqualNP.Outside.L_meta_1896_aux.RestrictedUnionBound

open GuardGeometry

def targets {k : Nat} (supports : Fin k → Finset (Fin 13)) (j : Fin k) : Finset (Fin 13) :=
  Finset.univ.filter fun p => pencil p ⊆ supports j

def exactTargets {k : Nat} (supports : Fin k → Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ.filter fun p => ∃ j : Fin k, supports j = pencil p

def active {k : Nat} (supports : Fin k → Finset (Fin 13)) : Finset (Fin 13) :=
  Finset.univ \ exactTargets supports

def guards {k : Nat} (supports : Fin k → Finset (Fin 13)) : Finset (Fin k) :=
  Finset.univ.filter fun j =>
    (∃ N ∈ fourCaps, Disjoint N (supports j)) ∧
      ∃ p ∈ active supports, pencil p ⊆ supports j

lemma target_mem {k : Nat} (supports : Fin k → Finset (Fin 13)) (j : Fin k) (p : Fin 13) :
    p ∈ targets supports j ↔ pencil p ⊆ supports j := by
  simp [targets]

lemma active_mem {k : Nat} (supports : Fin k → Finset (Fin 13)) (p : Fin 13) :
    p ∈ active supports ↔ ¬∃ j : Fin k, supports j = pencil p := by
  simp [active, exactTargets]

lemma guard_targets_card {k : Nat} (supports : Fin k → Finset (Fin 13))
    (j : Fin k) (hj : j ∈ guards supports) : (targets supports j).card ≤ 3 := by
  obtain ⟨N, hN, hNj⟩ := (Finset.mem_filter.mp hj).2.1
  have hsub : targets supports j ⊆ avoidingPoints N := by
    intro p hp
    apply (mem_avoidingPoints N p).mpr
    exact hNj.mono_right ((target_mem supports j p).mp hp)
  have hc := Finset.card_le_card hsub
  rw [fourCap_avoiding_card N ((mem_fourCaps N).mp hN)] at hc
  exact hc

lemma local_guard_charge {k : Nat} (supports : Fin k → Finset (Fin 13))
    (separates : ∀ p : Fin 13, ∀ N ∈ fourCaps, Disjoint N (pencil p) →
      ∃ j : Fin k, pencil p ⊆ supports j ∧ Disjoint N (supports j))
    (p : Fin 13) (hp : p ∈ active supports) :
    9 ≤ ∑ j ∈ guards supports,
      if p ∈ targets supports j then GuardCharging.weight (targets supports j) else 0 := by
  classical
  let G := (guards supports).filter fun j => p ∈ targets supports j
  let privateGuards := G.filter fun j => (targets supports j).card = 1
  have hnotexact := (active_mem supports p).mp hp
  have hextra : ∀ j ∈ privateGuards, ∃ v : Fin 13,
      v ∈ supports j ∧ v ∉ pencil p := by
    intro j hj
    have hjG := (Finset.mem_filter.mp hj).1
    have hpj := (target_mem supports j p).mp ((Finset.mem_filter.mp hjG).2)
    by_contra hn
    have hsub : supports j ⊆ pencil p := by
      intro v hv
      by_contra hvp
      exact hn ⟨v, hv, hvp⟩
    exact hnotexact ⟨j, Finset.Subset.antisymm hsub hpj⟩
  let extra (j : Fin k) : Fin 13 :=
    if hj : j ∈ privateGuards then Classical.choose (hextra j hj) else 0
  have hextra_spec : ∀ j ∈ privateGuards,
      extra j ∈ supports j ∧ extra j ∉ pencil p := by
    intro j hj
    simp only [extra, dif_pos hj]
    exact Classical.choose_spec (hextra j hj)
  have hother : ∀ j ∈ G \ privateGuards, ∃ q : Fin 13,
      q ∈ targets supports j ∧ q ≠ p := by
    intro j hj
    have hjG := (Finset.mem_sdiff.mp hj).1
    have hjnot := (Finset.mem_sdiff.mp hj).2
    have hpj := (Finset.mem_filter.mp hjG).2
    have hne : (targets supports j).card ≠ 1 := by
      intro h
      exact hjnot (Finset.mem_filter.mpr ⟨hjG, h⟩)
    by_contra hn
    have hsub : targets supports j ⊆ {p} := by
      intro q hq
      apply Finset.mem_singleton.mpr
      by_contra hqp
      exact hn ⟨q, hq, hqp⟩
    have hc := Finset.card_le_card hsub
    have hpos : 0 < (targets supports j).card := Finset.card_pos.mpr ⟨p, hpj⟩
    simp only [Finset.card_singleton] at hc
    omega
  let other (j : Fin k) : Fin 13 :=
    if hj : j ∈ G \ privateGuards then Classical.choose (hother j hj) else 0
  have hother_spec : ∀ j ∈ G \ privateGuards,
      other j ≠ p ∧ pencil (other j) ⊆ supports j := by
    intro j hj
    have h := Classical.choose_spec (hother j hj)
    simp only [other, dif_pos hj]
    exact ⟨h.2, (target_mem supports j _).mp h.1⟩
  have hguards : ∀ N ∈ fourCaps, Disjoint N (pencil p) →
      ∃ j ∈ G, Disjoint N (supports j) := by
    intro N hN hNp
    obtain ⟨j, hpj, hNj⟩ := separates p N hN hNp
    have hj : j ∈ guards supports := Finset.mem_filter.mpr
      ⟨Finset.mem_univ j, ⟨⟨N, hN, hNj⟩, ⟨p, hp, hpj⟩⟩⟩
    exact ⟨j, Finset.mem_filter.mpr ⟨hj, (target_mem supports j p).mpr hpj⟩, hNj⟩
  have hbound := GuardCharging.private_shared_bound p pencil supports fourCaps
    G privateGuards extra other (by
      intro j hj
      exact (Finset.mem_filter.mp hj).1) hextra_spec hother_spec hguards
    (fun A Q hA hAp hpQ hcover => residual_cover_bound p A Q hA hAp hpQ hcover)
  have hprivate : privateGuards = (guards supports).filter
      (fun j => p ∈ targets supports j ∧ (targets supports j).card = 1) := by
    ext j
    simp only [privateGuards, G, Finset.mem_filter]
    tauto
  have hshared : G \ privateGuards = (guards supports).filter
      (fun j => p ∈ targets supports j ∧ (targets supports j).card ≠ 1) := by
    ext j
    simp only [privateGuards, G, Finset.mem_sdiff, Finset.mem_filter]
    tauto
  rw [GuardCharging.local_weight_count, ← hprivate, ← hshared]
  exact hbound

lemma pure_union_lower_bound (k : Nat) (supports : Fin k → Finset (Fin 13))
    (scheme : PureUnionAncestry.Scheme supports)
    (separates : ∀ p : Fin 13, ∀ N ∈ fourCaps, Disjoint N (pencil p) →
      ∃ j : Fin k, pencil p ⊆ supports j ∧ Disjoint N (supports j)) :
    39 ≤ k := by
  classical
  have hactive : 3 * (active supports).card ≤ (guards supports).card :=
    GuardCharging.three_per_active_target (active supports) (guards supports) (targets supports)
      (guard_targets_card supports) (local_guard_charge supports separates)
  have hinside : ∀ p ∈ exactTargets supports,
      3 ≤ (GuardCharging.interior pencil supports p).card := by
    intro p hp
    exact PureUnionAncestry.exact_pencil_ancestry pencil supports scheme p (pencil_card p)
      ((Finset.mem_filter.mp hp).2)
  have hlinear : ∀ p q : Fin 13, p ≠ q → (pencil p ∩ pencil q).card ≤ 1 := by
    intro p q hpq
    exact Nat.le_of_eq (pencil_inter_card p q hpq)
  have hpartition : Disjoint (exactTargets supports) (active supports) := by
    apply Finset.disjoint_left.mpr
    intro p hp ha
    exact (Finset.mem_sdiff.mp ha).2 hp
  have hguard : Disjoint (guards supports)
      ((exactTargets supports).biUnion (GuardCharging.interior pencil supports)) := by
    apply GuardCharging.guard_interior_disjoint pencil supports
      (exactTargets supports) (active supports) (guards supports) hpartition
      (fun p => by rw [pencil_card]; omega) hlinear
    intro j hj
    exact (Finset.mem_filter.mp hj).2.2
  have h := GuardCharging.exact_and_active_count (exactTargets supports) (guards supports)
    (GuardCharging.interior pencil supports) hinside
    (GuardCharging.interiors_pairwise pencil supports (exactTargets supports) hlinear)
    hguard hactive
  simpa using h

end PEqualNP.Outside.L_meta_1896_aux.RestrictedUnionBound
