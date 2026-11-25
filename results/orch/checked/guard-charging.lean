import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1896_aux.GuardCharging

lemma target_mem_of_maximal_row {P V : Type*} [DecidableEq P] [DecidableEq V]
    (pencils : P → Finset V) (points : Finset P) (lines support : Finset V)
    (hmaximal : ∀ p ∉ points, ∃ l ∈ lines, l ∈ pencils p)
    (hdis : Disjoint lines support) (p : P) (hp : pencils p ⊆ support) :
    p ∈ points := by
  by_contra hnot
  obtain ⟨l, hl, hpl⟩ := hmaximal p hnot
  exact (Finset.disjoint_left.mp hdis) hl (hp hpl)

lemma targets_card_of_maximal_row {P V : Type*} [DecidableEq P] [DecidableEq V]
    (pencils : P → Finset V) (points targets : Finset P) (lines support : Finset V)
    (hmaximal : ∀ p ∉ points, ∃ l ∈ lines, l ∈ pencils p)
    (hdis : Disjoint lines support)
    (htargets : ∀ p ∈ targets, pencils p ⊆ support) :
    targets.card ≤ points.card := by
  apply Finset.card_le_card
  intro p hp
  exact target_mem_of_maximal_row pencils points lines support hmaximal hdis p (htargets p hp)

def interior {P V J : Type*} [DecidableEq V] [Fintype J]
    (pencils : P → Finset V) (supports : J → Finset V) (p : P) : Finset J :=
  Finset.univ.filter fun j => 2 ≤ (supports j).card ∧ supports j ⊆ pencils p

lemma interiors_pairwise {P V J : Type*} [DecidableEq P] [DecidableEq V]
    [Fintype J] [DecidableEq J]
    (pencils : P → Finset V) (supports : J → Finset V) (selected : Finset P)
    (hlinear : ∀ p q : P, p ≠ q → (pencils p ∩ pencils q).card ≤ 1) :
    (selected : Set P).PairwiseDisjoint (interior pencils supports) := by
  intro p _hp q _hq hpq
  apply Finset.disjoint_left.mpr
  intro j hjp hjq
  have hp := (Finset.mem_filter.mp hjp).2
  have hq := (Finset.mem_filter.mp hjq).2
  have hsub : supports j ⊆ pencils p ∩ pencils q := by
    intro v hv
    exact Finset.mem_inter.mpr ⟨hp.2 hv, hq.2 hv⟩
  have hcard := Finset.card_le_card hsub
  have hbound := hlinear p q hpq
  omega

lemma guard_interior_disjoint {P V J : Type*} [DecidableEq P] [DecidableEq V]
    [Fintype J] [DecidableEq J]
    (pencils : P → Finset V) (supports : J → Finset V)
    (exactTargets active : Finset P) (guards : Finset J)
    (hpartition : Disjoint exactTargets active)
    (hsize : ∀ p : P, 2 ≤ (pencils p).card)
    (hlinear : ∀ p q : P, p ≠ q → (pencils p ∩ pencils q).card ≤ 1)
    (hguards : ∀ j ∈ guards, ∃ q ∈ active, pencils q ⊆ supports j) :
    Disjoint guards (exactTargets.biUnion (interior pencils supports)) := by
  apply Finset.disjoint_left.mpr
  intro j hj hinside
  obtain ⟨p, hp, hjp⟩ := Finset.mem_biUnion.mp hinside
  obtain ⟨q, hq, hqj⟩ := hguards j hj
  have hpq : p ≠ q := by
    intro he
    subst q
    exact (Finset.disjoint_left.mp hpartition) hp hq
  have hjsub := (Finset.mem_filter.mp hjp).2.2
  have hsub : pencils q ⊆ pencils p ∩ pencils q := by
    intro v hv
    exact Finset.mem_inter.mpr ⟨hjsub (hqj hv), hv⟩
  have hcard := Finset.card_le_card hsub
  have hbound := hlinear p q hpq
  have hlow := hsize q
  omega

lemma multipartite_cover_bound {V : Type*} [DecidableEq V]
    (vertices cover : Finset V) (same : V → V → Prop) [DecidableRel same]
    (partBound : Nat)
    (hparts : ∀ u ∈ vertices, (vertices.filter fun v => same u v).card ≤ partBound)
    (hcover : ∀ u ∈ vertices, ∀ v ∈ vertices,
      ¬ same u v → u ∈ cover ∨ v ∈ cover) :
    vertices.card ≤ cover.card + partBound := by
  classical
  have hrest : (vertices \ cover).card ≤ partBound := by
    by_cases hne : (vertices \ cover).Nonempty
    · obtain ⟨u, hu⟩ := hne
      have huV := (Finset.mem_sdiff.mp hu).1
      have huQ := (Finset.mem_sdiff.mp hu).2
      calc
        (vertices \ cover).card ≤ (vertices.filter fun v => same u v).card := by
          apply Finset.card_le_card
          intro v hv
          have hvV := (Finset.mem_sdiff.mp hv).1
          have hvQ := (Finset.mem_sdiff.mp hv).2
          refine Finset.mem_filter.mpr ⟨hvV, ?_⟩
          by_contra hnot
          exact (hcover u huV v hvV hnot).elim huQ hvQ
        _ ≤ partBound := hparts u huV
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
      simp
  have hcard := Finset.card_le_card_sdiff_add_card (s := vertices) (t := cover)
  omega

lemma residual_cover_count {V : Type*} [DecidableEq V]
    (vertices cover : Finset V) (same : V → V → Prop) [DecidableRel same]
    (partBound extras : Nat)
    (hparts : ∀ u ∈ vertices, (vertices.filter fun v => same u v).card ≤ partBound)
    (hcover : ∀ u ∈ vertices, ∀ v ∈ vertices,
      ¬ same u v → u ∈ cover ∨ v ∈ cover)
    (hgeometry : 9 + partBound ≤ 3 * extras + vertices.card) :
    9 ≤ 3 * extras + cover.card := by
  have h := multipartite_cover_bound vertices cover same partBound hparts hcover
  omega

lemma private_shared_bound {P V J : Type*}
    [DecidableEq P] [DecidableEq V] [DecidableEq J]
    (p : P) (pencils : P → Finset V) (supports : J → Finset V)
    (caps : Finset (Finset V)) (guards privateGuards : Finset J)
    (extra : J → V) (other : J → P)
    (hprivate : privateGuards ⊆ guards)
    (hextra : ∀ j ∈ privateGuards, extra j ∈ supports j ∧ extra j ∉ pencils p)
    (hother : ∀ j ∈ guards \ privateGuards,
      other j ≠ p ∧ pencils (other j) ⊆ supports j)
    (hguards : ∀ N ∈ caps, Disjoint N (pencils p) →
      ∃ j ∈ guards, Disjoint N (supports j))
    (hgeometry : ∀ A : Finset V, ∀ Q : Finset P,
      A.card ≤ 2 → Disjoint A (pencils p) → p ∉ Q →
      (∀ N ∈ caps, Disjoint N (pencils p) → A ⊆ N →
        ∃ q ∈ Q, Disjoint N (pencils q)) →
      9 ≤ 3 * A.card + Q.card) :
    9 ≤ 3 * privateGuards.card + (guards \ privateGuards).card := by
  classical
  by_cases hlarge : 3 ≤ privateGuards.card
  · omega
  have hsmall : privateGuards.card ≤ 2 := by omega
  let A := privateGuards.image extra
  let Q := (guards \ privateGuards).image other
  have hAcard : A.card ≤ privateGuards.card := Finset.card_image_le
  have hQcard : Q.card ≤ (guards \ privateGuards).card := Finset.card_image_le
  have hAoutside : Disjoint A (pencils p) := by
    apply Finset.disjoint_left.mpr
    intro v hv hp
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
    exact (hextra j hj).2 hp
  have hpQ : p ∉ Q := by
    intro hp
    obtain ⟨j, hj, hEq⟩ := Finset.mem_image.mp hp
    exact (hother j hj).1 hEq
  have hcover : ∀ N ∈ caps, Disjoint N (pencils p) → A ⊆ N →
      ∃ q ∈ Q, Disjoint N (pencils q) := by
    intro N hN hNp hAN
    obtain ⟨j, hj, hNj⟩ := hguards N hN hNp
    have hjnot : j ∉ privateGuards := by
      intro hjpriv
      have haA : extra j ∈ A := Finset.mem_image.mpr ⟨j, hjpriv, rfl⟩
      exact (Finset.disjoint_left.mp hNj) (hAN haA) (hextra j hjpriv).1
    have hjshared : j ∈ guards \ privateGuards := Finset.mem_sdiff.mpr ⟨hj, hjnot⟩
    refine ⟨other j, Finset.mem_image.mpr ⟨j, hjshared, rfl⟩, ?_⟩
    exact hNj.mono_right (hother j hjshared).2
  have h := hgeometry A Q (hAcard.trans hsmall) hAoutside hpQ hcover
  omega

def weight {P : Type*} (targets : Finset P) : Nat :=
  if targets.card = 1 then 3 else 1

lemma local_weight_count {P J : Type*} [DecidableEq P] [DecidableEq J]
    (p : P) (guards : Finset J) (targets : J → Finset P) :
    (∑ j ∈ guards, if p ∈ targets j then weight (targets j) else 0) =
      3 * (guards.filter fun j => p ∈ targets j ∧ (targets j).card = 1).card +
      (guards.filter fun j => p ∈ targets j ∧ (targets j).card ≠ 1).card := by
  classical
  have hterm (j : J) : (if p ∈ targets j then weight (targets j) else 0) =
      (if p ∈ targets j ∧ (targets j).card = 1 then 3 else 0) +
      (if p ∈ targets j ∧ (targets j).card ≠ 1 then 1 else 0) := by
    by_cases hp : p ∈ targets j <;> by_cases hc : (targets j).card = 1 <;>
      simp [weight, hp, hc]
  calc
    _ = ∑ j ∈ guards,
        ((if p ∈ targets j ∧ (targets j).card = 1 then 3 else 0) +
         (if p ∈ targets j ∧ (targets j).card ≠ 1 then 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro j _hj
      exact hterm j
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.sum_filter, ← Finset.sum_filter]
      simp [Nat.mul_comm]

lemma one_guard_bound {P : Type*} [DecidableEq P]
    (active targets : Finset P) (hsize : targets.card ≤ 3) :
    (∑ p ∈ active, if p ∈ targets then weight targets else 0) ≤ 3 := by
  classical
  have hsub : (active.filter fun p => p ∈ targets).card ≤ targets.card := by
    apply Finset.card_le_card
    intro p hp
    exact (Finset.mem_filter.mp hp).2
  have he : (∑ p ∈ active, if p ∈ targets then weight targets else 0) =
      (active.filter fun p => p ∈ targets).card * weight targets := by
    rw [← Finset.sum_filter]
    simp
  rw [he]
  by_cases h : targets.card = 1
  · simp only [weight, if_pos h]
    omega
  · simp only [weight, if_neg h, Nat.mul_one]
    omega

lemma three_per_active_target {P J : Type*} [DecidableEq P] [DecidableEq J]
    (active : Finset P) (guards : Finset J) (targets : J → Finset P)
    (hsize : ∀ j ∈ guards, (targets j).card ≤ 3)
    (hlocal : ∀ p ∈ active,
      9 ≤ ∑ j ∈ guards, if p ∈ targets j then weight (targets j) else 0) :
    3 * active.card ≤ guards.card := by
  classical
  have hlower : 9 * active.card ≤
      ∑ p ∈ active, ∑ j ∈ guards,
        if p ∈ targets j then weight (targets j) else 0 := by
    calc
      9 * active.card = ∑ _p ∈ active, 9 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum hlocal
  rw [Finset.sum_comm] at hlower
  have hupper : (∑ j ∈ guards, ∑ p ∈ active,
      if p ∈ targets j then weight (targets j) else 0) ≤ 3 * guards.card := by
    calc
      _ ≤ ∑ _j ∈ guards, 3 :=
        Finset.sum_le_sum fun j hj => one_guard_bound active (targets j) (hsize j hj)
      _ = _ := by simp [Nat.mul_comm]
  omega

lemma exact_and_active_count {P J : Type*} [Fintype P] [Fintype J]
    [DecidableEq P] [DecidableEq J]
    (exactTargets : Finset P) (guards : Finset J) (inside : P → Finset J)
    (hinside : ∀ p ∈ exactTargets, 3 ≤ (inside p).card)
    (hdis : (exactTargets : Set P).PairwiseDisjoint inside)
    (hguard : Disjoint guards (exactTargets.biUnion inside))
    (hactive : 3 * (Finset.univ \ exactTargets).card ≤ guards.card) :
    3 * Fintype.card P ≤ Fintype.card J := by
  classical
  have hsum : 3 * exactTargets.card ≤ (exactTargets.biUnion inside).card := by
    rw [Finset.card_biUnion hdis]
    calc
      3 * exactTargets.card = ∑ _p ∈ exactTargets, 3 := by simp [Nat.mul_comm]
      _ ≤ _ := Finset.sum_le_sum hinside
  have htotal : guards.card + (exactTargets.biUnion inside).card ≤ Fintype.card J := by
    rw [← Finset.card_union_of_disjoint hguard]
    exact Finset.card_le_univ _
  have hpartition : (Finset.univ \ exactTargets).card + exactTargets.card = Fintype.card P := by
    simpa using Finset.card_sdiff_add_card_eq_card (Finset.subset_univ exactTargets)
  omega

end PEqualNP.Outside.L_meta_1896_aux.GuardCharging
