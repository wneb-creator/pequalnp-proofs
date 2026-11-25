import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1896_aux.AllRows

abbrev incidence (p l : Fin 13) : Prop := p = l ∨ p = l + 1 ∨ p = l + 3 ∨ p = l + 9

end PEqualNP.Outside.L_meta_1896_aux.AllRows

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
lemma residual_pair_card_0 : ∀ a b : Fin 13,
    a ≠ b → a ∉ pencil 0 → b ∉ pencil 0 →
    (residual 0 {a, b}).card = 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_pair_card_1 : ∀ a b : Fin 13,
    a ≠ b → a ∉ pencil 1 → b ∉ pencil 1 →
    (residual 1 {a, b}).card = 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_pair_card_2 : ∀ a b : Fin 13,
    a ≠ b → a ∉ pencil 2 → b ∉ pencil 2 →
    (residual 2 {a, b}).card = 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_pair_card_3 : ∀ a b : Fin 13,
    a ≠ b → a ∉ pencil 3 → b ∉ pencil 3 →
    (residual 3 {a, b}).card = 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_pair_card_4 : ∀ a b : Fin 13,
    a ≠ b → a ∉ pencil 4 → b ∉ pencil 4 →
    (residual 4 {a, b}).card = 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_pair_card_5 : ∀ a b : Fin 13,
    a ≠ b → a ∉ pencil 5 → b ∉ pencil 5 →
    (residual 5 {a, b}).card = 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_pair_card_6 : ∀ a b : Fin 13,
    a ≠ b → a ∉ pencil 6 → b ∉ pencil 6 →
    (residual 6 {a, b}).card = 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_pair_card_7 : ∀ a b : Fin 13,
    a ≠ b → a ∉ pencil 7 → b ∉ pencil 7 →
    (residual 7 {a, b}).card = 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_pair_card_8 : ∀ a b : Fin 13,
    a ≠ b → a ∉ pencil 8 → b ∉ pencil 8 →
    (residual 8 {a, b}).card = 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_pair_card_9 : ∀ a b : Fin 13,
    a ≠ b → a ∉ pencil 9 → b ∉ pencil 9 →
    (residual 9 {a, b}).card = 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_pair_card_10 : ∀ a b : Fin 13,
    a ≠ b → a ∉ pencil 10 → b ∉ pencil 10 →
    (residual 10 {a, b}).card = 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_pair_card_11 : ∀ a b : Fin 13,
    a ≠ b → a ∉ pencil 11 → b ∉ pencil 11 →
    (residual 11 {a, b}).card = 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_pair_card_12 : ∀ a b : Fin 13,
    a ≠ b → a ∉ pencil 12 → b ∉ pencil 12 →
    (residual 12 {a, b}).card = 5 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_pair_card : ∀ p a b : Fin 13,
    a ≠ b → a ∉ pencil p → b ∉ pencil p →
    (residual p {a, b}).card = 5 := by
  exact (Fin.cases residual_pair_card_0 (Fin.cases residual_pair_card_1 (Fin.cases residual_pair_card_2 (Fin.cases residual_pair_card_3 (Fin.cases residual_pair_card_4 (Fin.cases residual_pair_card_5 (Fin.cases residual_pair_card_6 (Fin.cases residual_pair_card_7 (Fin.cases residual_pair_card_8 (Fin.cases residual_pair_card_9 (Fin.cases residual_pair_card_10 (Fin.cases residual_pair_card_11 (Fin.cases residual_pair_card_12 (fun i => Fin.elim0 i))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_empty_ray_card : ∀ p q : Fin 13, q ≠ p →
    ((residual p ∅).filter (sameRay p q)).card = 3 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_singleton_ray_card_0 : ∀ a q : Fin 13,
    a ∉ pencil 0 → q ≠ 0 →
    ((residual 0 {a}).filter (sameRay 0 q)).card = 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_singleton_ray_card_1 : ∀ a q : Fin 13,
    a ∉ pencil 1 → q ≠ 1 →
    ((residual 1 {a}).filter (sameRay 1 q)).card = 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_singleton_ray_card_2 : ∀ a q : Fin 13,
    a ∉ pencil 2 → q ≠ 2 →
    ((residual 2 {a}).filter (sameRay 2 q)).card = 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_singleton_ray_card_3 : ∀ a q : Fin 13,
    a ∉ pencil 3 → q ≠ 3 →
    ((residual 3 {a}).filter (sameRay 3 q)).card = 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_singleton_ray_card_4 : ∀ a q : Fin 13,
    a ∉ pencil 4 → q ≠ 4 →
    ((residual 4 {a}).filter (sameRay 4 q)).card = 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_singleton_ray_card_5 : ∀ a q : Fin 13,
    a ∉ pencil 5 → q ≠ 5 →
    ((residual 5 {a}).filter (sameRay 5 q)).card = 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_singleton_ray_card_6 : ∀ a q : Fin 13,
    a ∉ pencil 6 → q ≠ 6 →
    ((residual 6 {a}).filter (sameRay 6 q)).card = 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_singleton_ray_card_7 : ∀ a q : Fin 13,
    a ∉ pencil 7 → q ≠ 7 →
    ((residual 7 {a}).filter (sameRay 7 q)).card = 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_singleton_ray_card_8 : ∀ a q : Fin 13,
    a ∉ pencil 8 → q ≠ 8 →
    ((residual 8 {a}).filter (sameRay 8 q)).card = 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_singleton_ray_card_9 : ∀ a q : Fin 13,
    a ∉ pencil 9 → q ≠ 9 →
    ((residual 9 {a}).filter (sameRay 9 q)).card = 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_singleton_ray_card_10 : ∀ a q : Fin 13,
    a ∉ pencil 10 → q ≠ 10 →
    ((residual 10 {a}).filter (sameRay 10 q)).card = 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_singleton_ray_card_11 : ∀ a q : Fin 13,
    a ∉ pencil 11 → q ≠ 11 →
    ((residual 11 {a}).filter (sameRay 11 q)).card = 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_singleton_ray_card_12 : ∀ a q : Fin 13,
    a ∉ pencil 12 → q ≠ 12 →
    ((residual 12 {a}).filter (sameRay 12 q)).card = 2 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma residual_singleton_ray_card : ∀ p a q : Fin 13,
    a ∉ pencil p → q ≠ p →
    ((residual p {a}).filter (sameRay p q)).card = 2 := by
  exact (Fin.cases residual_singleton_ray_card_0 (Fin.cases residual_singleton_ray_card_1 (Fin.cases residual_singleton_ray_card_2 (Fin.cases residual_singleton_ray_card_3 (Fin.cases residual_singleton_ray_card_4 (Fin.cases residual_singleton_ray_card_5 (Fin.cases residual_singleton_ray_card_6 (Fin.cases residual_singleton_ray_card_7 (Fin.cases residual_singleton_ray_card_8 (Fin.cases residual_singleton_ray_card_9 (Fin.cases residual_singleton_ray_card_10 (Fin.cases residual_singleton_ray_card_11 (Fin.cases residual_singleton_ray_card_12 (fun i => Fin.elim0 i))))))))))))))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma capFor_spec_0 : ∀ q r : Fin 13,
    q ≠ 0 → r ≠ 0 → ¬sameRay 0 q r →
    IsFourCap (capFor 0 q r) ∧ avoidingPoints (capFor 0 q r) = {0, q, r} := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma capFor_spec_1 : ∀ q r : Fin 13,
    q ≠ 1 → r ≠ 1 → ¬sameRay 1 q r →
    IsFourCap (capFor 1 q r) ∧ avoidingPoints (capFor 1 q r) = {1, q, r} := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma capFor_spec_2 : ∀ q r : Fin 13,
    q ≠ 2 → r ≠ 2 → ¬sameRay 2 q r →
    IsFourCap (capFor 2 q r) ∧ avoidingPoints (capFor 2 q r) = {2, q, r} := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma capFor_spec_3 : ∀ q r : Fin 13,
    q ≠ 3 → r ≠ 3 → ¬sameRay 3 q r →
    IsFourCap (capFor 3 q r) ∧ avoidingPoints (capFor 3 q r) = {3, q, r} := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma capFor_spec_4 : ∀ q r : Fin 13,
    q ≠ 4 → r ≠ 4 → ¬sameRay 4 q r →
    IsFourCap (capFor 4 q r) ∧ avoidingPoints (capFor 4 q r) = {4, q, r} := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma capFor_spec_5 : ∀ q r : Fin 13,
    q ≠ 5 → r ≠ 5 → ¬sameRay 5 q r →
    IsFourCap (capFor 5 q r) ∧ avoidingPoints (capFor 5 q r) = {5, q, r} := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma capFor_spec_6 : ∀ q r : Fin 13,
    q ≠ 6 → r ≠ 6 → ¬sameRay 6 q r →
    IsFourCap (capFor 6 q r) ∧ avoidingPoints (capFor 6 q r) = {6, q, r} := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma capFor_spec_7 : ∀ q r : Fin 13,
    q ≠ 7 → r ≠ 7 → ¬sameRay 7 q r →
    IsFourCap (capFor 7 q r) ∧ avoidingPoints (capFor 7 q r) = {7, q, r} := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma capFor_spec_8 : ∀ q r : Fin 13,
    q ≠ 8 → r ≠ 8 → ¬sameRay 8 q r →
    IsFourCap (capFor 8 q r) ∧ avoidingPoints (capFor 8 q r) = {8, q, r} := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma capFor_spec_9 : ∀ q r : Fin 13,
    q ≠ 9 → r ≠ 9 → ¬sameRay 9 q r →
    IsFourCap (capFor 9 q r) ∧ avoidingPoints (capFor 9 q r) = {9, q, r} := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma capFor_spec_10 : ∀ q r : Fin 13,
    q ≠ 10 → r ≠ 10 → ¬sameRay 10 q r →
    IsFourCap (capFor 10 q r) ∧ avoidingPoints (capFor 10 q r) = {10, q, r} := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma capFor_spec_11 : ∀ q r : Fin 13,
    q ≠ 11 → r ≠ 11 → ¬sameRay 11 q r →
    IsFourCap (capFor 11 q r) ∧ avoidingPoints (capFor 11 q r) = {11, q, r} := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma capFor_spec_12 : ∀ q r : Fin 13,
    q ≠ 12 → r ≠ 12 → ¬sameRay 12 q r →
    IsFourCap (capFor 12 q r) ∧ avoidingPoints (capFor 12 q r) = {12, q, r} := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
set_option synthInstance.maxSize 100000 in
lemma capFor_spec : ∀ p q r : Fin 13,
    q ≠ p → r ≠ p → ¬sameRay p q r →
    IsFourCap (capFor p q r) ∧ avoidingPoints (capFor p q r) = {p, q, r} := by
  exact (Fin.cases capFor_spec_0 (Fin.cases capFor_spec_1 (Fin.cases capFor_spec_2 (Fin.cases capFor_spec_3 (Fin.cases capFor_spec_4 (Fin.cases capFor_spec_5 (Fin.cases capFor_spec_6 (Fin.cases capFor_spec_7 (Fin.cases capFor_spec_8 (Fin.cases capFor_spec_9 (Fin.cases capFor_spec_10 (Fin.cases capFor_spec_11 (Fin.cases capFor_spec_12 (fun i => Fin.elim0 i))))))))))))))

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

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma line_points_card : ∀ l : Fin 13,
    (Finset.univ.filter fun p : Fin 13 => incidence p l).card = 4 := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma line_inter_points_card : ∀ a b : Fin 13, a ≠ b →
    (Finset.univ.filter fun p : Fin 13 => incidence p a ∧ incidence p b).card = 1 := by
  decide +kernel

lemma degree_sum (N : Finset (Fin 13)) :
    (∑ p : Fin 13, (N ∩ pencil p).card) = 4 * N.card := by
  have hlocal (p : Fin 13) : (N ∩ pencil p).card =
      ∑ l ∈ N, if incidence p l then 1 else 0 := by
    have hf : N ∩ pencil p = N.filter (incidence p) := by
      ext l
      simp [pencil]
    rw [hf, ← Finset.sum_filter]
    simp
  calc
    _ = ∑ p : Fin 13, ∑ l ∈ N, if incidence p l then 1 else 0 :=
      Finset.sum_congr rfl fun p _ => hlocal p
    _ = ∑ l ∈ N, ∑ p : Fin 13, if incidence p l then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _l ∈ N, 4 := by
      apply Finset.sum_congr rfl
      intro l _hl
      rw [← Finset.sum_filter]
      simpa using line_points_card l
    _ = 4 * N.card := by simp [Nat.mul_comm]

lemma ordered_degree_sum (N : Finset (Fin 13)) :
    (∑ p : Fin 13, (N ∩ pencil p).offDiag.card) = N.offDiag.card := by
  have hlocal (p : Fin 13) : (N ∩ pencil p).offDiag.card =
      ∑ ab ∈ N.offDiag, if incidence p ab.1 ∧ incidence p ab.2 then 1 else 0 := by
    have hf : (N ∩ pencil p).offDiag =
        N.offDiag.filter fun ab => incidence p ab.1 ∧ incidence p ab.2 := by
      ext ab
      simp only [Finset.mem_offDiag, Finset.mem_inter, mem_pencil, Finset.mem_filter]
      constructor
      · rintro ⟨⟨haN, haP⟩, ⟨hbN, hbP⟩, hab⟩
        exact ⟨⟨haN, hbN, hab⟩, haP, hbP⟩
      · rintro ⟨⟨haN, hbN, hab⟩, haP, hbP⟩
        exact ⟨⟨haN, haP⟩, ⟨hbN, hbP⟩, hab⟩
    rw [hf, ← Finset.sum_filter]
    simp
  calc
    _ = ∑ p : Fin 13, ∑ ab ∈ N.offDiag,
        if incidence p ab.1 ∧ incidence p ab.2 then 1 else 0 :=
      Finset.sum_congr rfl fun p _ => hlocal p
    _ = ∑ ab ∈ N.offDiag, ∑ p : Fin 13,
        if incidence p ab.1 ∧ incidence p ab.2 then 1 else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ _ab ∈ N.offDiag, 1 := by
      apply Finset.sum_congr rfl
      intro ab hab
      rw [← Finset.sum_filter]
      simpa using line_inter_points_card ab.1 ab.2 (Finset.mem_offDiag.mp hab).2.2
    _ = N.offDiag.card := by simp

lemma fourCap_avoiding_card (N : Finset (Fin 13)) (hN : IsFourCap N) :
    (avoidingPoints N).card = 3 := by
  have hdegree : (∑ p : Fin 13, (N ∩ pencil p).card) = 16 := by
    simpa [hN.1] using degree_sum N
  have hpairs : (∑ p : Fin 13,
      ((N ∩ pencil p).card * (N ∩ pencil p).card - (N ∩ pencil p).card)) = 12 := by
    simpa [Finset.offDiag_card, hN.1] using ordered_degree_sum N
  have hzero : (∑ p : Fin 13, if (N ∩ pencil p).card = 0 then 1 else 0) =
      (avoidingPoints N).card := by
    rw [← Finset.sum_filter]
    have hf : (Finset.univ.filter fun p : Fin 13 => (N ∩ pencil p).card = 0) =
        avoidingPoints N := by
      ext p
      simp [avoidingPoints, Finset.card_eq_zero, Finset.disjoint_iff_inter_eq_empty]
    rw [hf]
    simp
  have hlocal (p : Fin 13) :
      2 * (N ∩ pencil p).card + 2 * (if (N ∩ pencil p).card = 0 then 1 else 0) =
      2 + ((N ∩ pencil p).card * (N ∩ pencil p).card - (N ∩ pencil p).card) := by
    have hbound := hN.2 p
    have hcases : (N ∩ pencil p).card = 0 ∨
        (N ∩ pencil p).card = 1 ∨ (N ∩ pencil p).card = 2 := by omega
    rcases hcases with h | h | h <;> simp [h]
  have hsum :
      2 * (∑ p : Fin 13, (N ∩ pencil p).card) +
        2 * (∑ p : Fin 13, if (N ∩ pencil p).card = 0 then 1 else 0) =
      26 + ∑ p : Fin 13,
        ((N ∩ pencil p).card * (N ∩ pencil p).card - (N ∩ pencil p).card) := by
    calc
      _ = ∑ p : Fin 13,
          (2 * (N ∩ pencil p).card +
            2 * (if (N ∩ pencil p).card = 0 then 1 else 0)) := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = ∑ p : Fin 13,
          (2 + ((N ∩ pencil p).card * (N ∩ pencil p).card - (N ∩ pencil p).card)) :=
        Finset.sum_congr rfl fun p _ => hlocal p
      _ = _ := by simp [Finset.sum_add_distrib]
  rw [hdegree, hzero, hpairs] at hsum
  omega

end PEqualNP.Outside.L_meta_1896_aux.GuardGeometry

namespace PEqualNP.Outside.L_meta_1896_aux.PureUnionAncestry

def Source {V : Type*} {k : Nat} (supports : Fin k → Finset V)
    (j : Fin k) (A : Finset V) : Prop :=
  A.card ≤ 1 ∨ ∃ i : Fin k, i.val < j.val ∧ supports i = A

def Scheme {V : Type*} [DecidableEq V] {k : Nat}
    (supports : Fin k → Finset V) : Prop :=
  ∀ j : Fin k, ∃ A B : Finset V,
    Source supports j A ∧ Source supports j B ∧ supports j = A ∪ B

def relevant {V : Type*} [DecidableEq V] {k : Nat}
    (supports : Fin k → Finset V) (target : Finset V) : Finset (Fin k) :=
  Finset.univ.filter fun j => 2 ≤ (supports j).card ∧ supports j ⊆ target

lemma source_large {V : Type*} {k : Nat} (supports : Fin k → Finset V)
    (j : Fin k) (A : Finset V) (hsource : Source supports j A) (hlarge : 2 ≤ A.card) :
    ∃ i : Fin k, i.val < j.val ∧ supports i = A := by
  rcases hsource with hsmall | hprior
  · omega
  · exact hprior

lemma large_predecessor {V : Type*} [DecidableEq V] {k : Nat}
    (supports : Fin k → Finset V) (scheme : Scheme supports)
    (j : Fin k) (hlarge : 3 ≤ (supports j).card) :
    ∃ i : Fin k, i.val < j.val ∧ 2 ≤ (supports i).card ∧ supports i ⊆ supports j := by
  obtain ⟨A, B, hA, hB, heq⟩ := scheme j
  have hcard := Finset.card_union_le A B
  rw [← heq] at hcard
  by_cases ha : 2 ≤ A.card
  · obtain ⟨i, hij, hi⟩ := source_large supports j A hA ha
    refine ⟨i, hij, ?_, ?_⟩
    · simpa [hi] using ha
    · rw [hi, heq]
      intro v hv
      exact Finset.mem_union.mpr (Or.inl hv)
  · have hb : 2 ≤ B.card := by omega
    obtain ⟨i, hij, hi⟩ := source_large supports j B hB hb
    refine ⟨i, hij, ?_, ?_⟩
    · simpa [hi] using hb
    · rw [hi, heq]
      intro v hv
      exact Finset.mem_union.mpr (Or.inr hv)

lemma three_members_card {J : Type*} [DecidableEq J]
    (M : Finset J) (a b c : J) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha : a ∈ M) (hb : b ∈ M) (hc : c ∈ M) : 3 ≤ M.card := by
  have hsub : ({a, b, c} : Finset J) ⊆ M := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
  have hcard : ({a, b, c} : Finset J).card = 3 := by
    simp [hab, hac, hbc]
  have h := Finset.card_le_card hsub
  omega

lemma large_source_has_three_nodes {V : Type*} [DecidableEq V] {k : Nat}
    (supports : Fin k → Finset V) (scheme : Scheme supports)
    (j : Fin k) (A target : Finset V)
    (hsource : Source supports j A) (hlarge : 3 ≤ A.card)
    (hAsub : A ⊆ supports j) (hjcard : 2 ≤ (supports j).card)
    (hjsub : supports j ⊆ target) :
    3 ≤ (relevant supports target).card := by
  obtain ⟨i, hij, hi⟩ := source_large supports j A hsource (by omega)
  have hicard : 3 ≤ (supports i).card := by simpa [hi] using hlarge
  obtain ⟨a, hai, hacard, hasub⟩ := large_predecessor supports scheme i hicard
  have ha_ne_i : a ≠ i := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have ha_ne_j : a ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have hi_ne_j : i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    omega
  have hisub : supports i ⊆ supports j := by simpa [hi] using hAsub
  apply three_members_card (relevant supports target) a i j ha_ne_i ha_ne_j hi_ne_j
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ a, hacard, hasub.trans (hisub.trans hjsub)⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ i, by omega, hisub.trans hjsub⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, hjcard, hjsub⟩

lemma four_support_has_three_nodes {V : Type*} [DecidableEq V] {k : Nat}
    (supports : Fin k → Finset V) (scheme : Scheme supports)
    (j : Fin k) (hcard : 4 ≤ (supports j).card) :
    3 ≤ (relevant supports (supports j)).card := by
  obtain ⟨A, B, hA, hB, heq⟩ := scheme j
  have hAsub : A ⊆ supports j := by
    rw [heq]
    intro v hv
    exact Finset.mem_union.mpr (Or.inl hv)
  have hBsub : B ⊆ supports j := by
    rw [heq]
    intro v hv
    exact Finset.mem_union.mpr (Or.inr hv)
  by_cases ha : 3 ≤ A.card
  · exact large_source_has_three_nodes supports scheme j A (supports j)
      hA ha hAsub (by omega) (fun _ hv => hv)
  · by_cases hb : 3 ≤ B.card
    · exact large_source_has_three_nodes supports scheme j B (supports j)
        hB hb hBsub (by omega) (fun _ hv => hv)
    · have hsum := Finset.card_union_le A B
      rw [← heq] at hsum
      have ha2 : A.card = 2 := by omega
      have hb2 : B.card = 2 := by omega
      obtain ⟨i, hij, hi⟩ := source_large supports j A hA (by omega)
      obtain ⟨a, haj, haS⟩ := source_large supports j B hB (by omega)
      have hia : i ≠ a := by
        intro h
        have hab : A = B := hi.symm.trans ((congrArg supports h).trans haS)
        have hj : supports j = A := by simpa [hab] using heq
        rw [hj] at hcard
        omega
      have hij_ne : i ≠ j := by
        intro h
        have hv := congrArg Fin.val h
        omega
      have haj_ne : a ≠ j := by
        intro h
        have hv := congrArg Fin.val h
        omega
      apply three_members_card (relevant supports (supports j)) i a j hia hij_ne haj_ne
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ i, ?_, ?_⟩
        · simpa [hi] using (show 2 ≤ A.card by omega)
        · simpa [hi] using hAsub
      · apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ a, ?_, ?_⟩
        · simpa [haS] using (show 2 ≤ B.card by omega)
        · simpa [haS] using hBsub
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ j, by omega, fun _ hv => hv⟩

lemma exact_pencil_ancestry {P V : Type*} [DecidableEq V] {k : Nat}
    (pencils : P → Finset V) (supports : Fin k → Finset V)
    (scheme : Scheme supports) (p : P) (hsize : (pencils p).card = 4)
    (hexact : ∃ j : Fin k, supports j = pencils p) :
    3 ≤ (GuardCharging.interior pencils supports p).card := by
  obtain ⟨j, hj⟩ := hexact
  have hc : 4 ≤ (supports j).card := by simp [hj, hsize]
  have h := four_support_has_three_nodes supports scheme j hc
  simpa only [relevant, GuardCharging.interior, hj] using h

end PEqualNP.Outside.L_meta_1896_aux.PureUnionAncestry

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
