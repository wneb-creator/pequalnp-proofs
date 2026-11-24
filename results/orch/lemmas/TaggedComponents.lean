import Mathlib

namespace PEqualNP.Outside.L_meta_1477.SharedTagExit

lemma reach_labels {V I : Type*} [DecidableEq I] (D : V → V → Prop)
    (labels : V → Finset I) (hmono : ∀ u v, D u v → labels v ⊆ labels u)
    {u v : V} (h : Relation.ReflTransGen D u v) : labels v ⊆ labels u := by
  induction h with
  | refl => exact Finset.Subset.refl _
  | tail hstep hedge ih => exact Finset.Subset.trans (hmono _ _ hedge) ih

lemma path_exit {V I K : Type*} [DecidableEq I] (D : V → V → Prop)
    (labels : V → Finset I) (component : V → Option K)
    (hmono : ∀ u v, D u v → labels v ⊆ labels u)
    (hconstant : ∀ u v, D u v → ∀ a b, component u = some a →
      component v = some b → a = b)
    {u v : V} {a : K} {i : I} (hu : component u = some a)
    (hv : component v = none) (hi : i ∈ labels v)
    (hpath : Relation.ReflTransGen D u v) :
    ∃ x y, component x = some a ∧ component y = none ∧ D x y ∧ i ∈ labels y := by
  induction hpath using Relation.ReflTransGen.head_induction_on with
  | refl => rw [hu] at hv; cases hv
  | @head w w' hstep htail ih =>
    have hi' : i ∈ labels w' := reach_labels D labels hmono htail hi
    cases hc : component w' with
    | none => exact ⟨w, w', hu, hc, hstep, hi'⟩
    | some b =>
      have hab := hconstant w w' hstep a b hu hc
      subst b
      exact ih hc

lemma two_exits {V I K : Type*} [DecidableEq I] (D : V → V → Prop)
    (labels : V → Finset I) (component : V → Option K)
    (hmono : ∀ u v, D u v → labels v ⊆ labels u)
    (hconstant : ∀ u v, D u v → ∀ a b, component u = some a →
      component v = some b → a = b)
    (hprivate : ∀ v, component v = none → (labels v).card ≤ 1)
    (root : I → V) (hroot : ∀ i, component (root i) = none ∧ i ∈ labels (root i))
    (hreach : ∀ u i, i ∈ labels u → Relation.ReflTransGen D u (root i))
    {u : V} {a : K} (hu : component u = some a) (hsize : 2 ≤ (labels u).card) :
    ∃ x₀ y₀ x₁ y₁, component x₀ = some a ∧ component y₀ = none ∧ D x₀ y₀ ∧
      component x₁ = some a ∧ component y₁ = none ∧ D x₁ y₁ ∧ y₀ ≠ y₁ := by
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp hsize
  obtain ⟨x₀, y₀, hx₀, hy₀, he₀, hi₀⟩ := path_exit D labels component hmono hconstant
    hu (hroot i).1 (hroot i).2 (hreach u i hi)
  obtain ⟨x₁, y₁, hx₁, hy₁, he₁, hj₁⟩ := path_exit D labels component hmono hconstant
    hu (hroot j).1 (hroot j).2 (hreach u j hj)
  refine ⟨x₀, y₀, x₁, y₁, hx₀, hy₀, he₀, hx₁, hy₁, he₁, ?_⟩
  intro he
  subst y₁
  exact hij (Finset.card_le_one.mp (hprivate y₀ hy₀) i hi₀ j hj₁)

lemma component_exit_card {V I K : Type*} [Fintype V] [Fintype K] [DecidableEq I]
    (D : V → V → Prop) [DecidableRel D] (labels : V → Finset I)
    (component : V → Option K)
    (hmono : ∀ u v, D u v → labels v ⊆ labels u)
    (hconstant : ∀ u v, D u v → ∀ a b, component u = some a →
      component v = some b → a = b)
    (hprivate : ∀ v, component v = none → (labels v).card ≤ 1)
    (root : I → V) (hroot : ∀ i, component (root i) = none ∧ i ∈ labels (root i))
    (hreach : ∀ u i, i ∈ labels u → Relation.ReflTransGen D u (root i))
    (hrep : ∀ a, ∃ u, component u = some a ∧ 2 ≤ (labels u).card) :
    2 * Fintype.card K ≤
      (Finset.univ.filter fun e : V × V => D e.1 e.2 ∧
        (component e.1).isSome ∧ component e.2 = none).card := by
  classical
  let E := Finset.univ.filter fun e : V × V => D e.1 e.2 ∧
    (component e.1).isSome ∧ component e.2 = none
  have htwo (a : K) : 2 ≤ (E.filter fun e => component e.1 = some a).card := by
    obtain ⟨u, hu, hsize⟩ := hrep a
    obtain ⟨x₀, y₀, x₁, y₁, hx₀, hy₀, he₀, hx₁, hy₁, he₁, hne⟩ :=
      two_exits D labels component hmono hconstant hprivate root hroot hreach hu hsize
    apply Finset.one_lt_card.mpr
    refine ⟨(x₀, y₀), ?_, (x₁, y₁), ?_, ?_⟩
    · simp [E, he₀, hx₀, hy₀]
    · simp [E, he₁, hx₁, hy₁]
    · intro he
      exact hne (congrArg Prod.snd he)
  have hdis : ∀ a ∈ (Finset.univ : Finset K), ∀ b ∈ Finset.univ, a ≠ b →
      Disjoint (E.filter fun e => component e.1 = some a) (E.filter fun e => component e.1 = some b) := by
    intro a ha b hb hab
    apply Finset.disjoint_left.mpr
    intro e hea heb
    exact hab (Option.some.inj ((Finset.mem_filter.mp hea).2.symm.trans (Finset.mem_filter.mp heb).2))
  have hsub : (Finset.univ.biUnion fun a : K => E.filter fun e => component e.1 = some a) ⊆ E := by
    intro e he
    obtain ⟨a, ha, hea⟩ := Finset.mem_biUnion.mp he
    exact (Finset.mem_filter.mp hea).1
  have hsum := Finset.sum_le_sum (s := (Finset.univ : Finset K)) (fun a ha => htwo a)
  have hcount := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdis] at hcount
  have hleft : (∑ _a : K, 2) = 2 * Fintype.card K := by simp [Nat.mul_comm]
  rw [hleft] at hsum
  exact hsum.trans hcount

end PEqualNP.Outside.L_meta_1477.SharedTagExit

namespace PEqualNP.Outside.L_meta_1477.TaggedNetwork

noncomputable def network {V : Type*} [Fintype V] (E : Finset (V × V)) : SimpleGraph V := by
  classical
  exact SimpleGraph.fromEdgeSet (↑(E.image fun e => s(e.1, e.2)) : Set (Sym2 V))

lemma adj_of_arrow {V : Type*} [Fintype V] (E : Finset (V × V)) {u v : V}
    (he : (u, v) ∈ E) (hne : u ≠ v) : (network E).Adj u v := by
  classical
  apply (SimpleGraph.fromEdgeSet_adj _).mpr
  exact ⟨Finset.mem_image.mpr ⟨(u, v), he, rfl⟩, hne⟩

lemma arrow_or_reverse {V : Type*} [Fintype V] (E : Finset (V × V)) {u v : V}
    (h : (network E).Adj u v) : (u, v) ∈ E ∨ (v, u) ∈ E := by
  classical
  obtain ⟨a, ha, he⟩ := Finset.mem_image.mp ((SimpleGraph.fromEdgeSet_adj _).mp h).1
  rcases Sym2.eq_iff.mp he with he | he
  · rcases he with ⟨he₀, he₁⟩
    left
    simpa only [← he₀, ← he₁, Prod.mk.eta] using ha
  · rcases he with ⟨he₀, he₁⟩
    right
    simpa only [← he₀, ← he₁, Prod.mk.eta] using ha

noncomputable def shared {V I : Type*} [Fintype V] (labels : V → Finset I) : Set V :=
  {v | (labels v).card = 2}

noncomputable def component {V I : Type*} [Fintype V] (E : Finset (V × V))
    (labels : V → Finset I) (v : V) : Option ((network E).induce (shared labels)).ConnectedComponent := by
  classical
  exact if h : v ∈ shared labels then some (((network E).induce (shared labels)).connectedComponentMk ⟨v, h⟩)
    else none

lemma component_none_iff {V I : Type*} [Fintype V] (E : Finset (V × V))
    (labels : V → Finset I) (v : V) : component E labels v = none ↔ (labels v).card ≠ 2 := by
  classical
  by_cases h : (labels v).card = 2 <;> simp [component, shared, h]

lemma component_constant {V I : Type*} [Fintype V] (E : Finset (V × V))
    (labels : V → Finset I) (u v : V) (he : (u, v) ∈ E)
    (a b : ((network E).induce (shared labels)).ConnectedComponent)
    (hu : component E labels u = some a) (hv : component E labels v = some b) : a = b := by
  classical
  have hus : u ∈ shared labels := by
    by_contra h
    simp [component, h] at hu
  have hvs : v ∈ shared labels := by
    by_contra h
    simp [component, h] at hv
  have hau : ((network E).induce (shared labels)).connectedComponentMk ⟨u, hus⟩ = a := by
    simpa [component, hus] using hu
  have hbv : ((network E).induce (shared labels)).connectedComponentMk ⟨v, hvs⟩ = b := by
    simpa [component, hvs] using hv
  rw [← hau, ← hbv]
  by_cases huv : u = v
  · subst v
    rfl
  · apply SimpleGraph.ConnectedComponent.sound
    exact (show ((network E).induce (shared labels)).Adj ⟨u, hus⟩ ⟨v, hvs⟩ from adj_of_arrow E he huv).reachable

lemma exits_lower_bound {V I : Type*} [Fintype V] [DecidableEq I]
    (E : Finset (V × V)) (labels : V → Finset I)
    (hcard : ∀ v, (labels v).card ≤ 2)
    (hmono : ∀ u v, (u, v) ∈ E → labels v ⊆ labels u)
    (root : I → V) (hroot : ∀ i, labels (root i) = {i})
    (hreach : ∀ u i, i ∈ labels u →
      Relation.ReflTransGen (fun u v => (u, v) ∈ E) u (root i)) :
    2 * Nat.card ((network E).induce (shared labels)).ConnectedComponent ≤
      (E.filter fun e => (labels e.1).card = 2 ∧ (labels e.2).card ≠ 2).card := by
  classical
  let K := ((network E).induce (shared labels)).ConnectedComponent
  letI : Fintype K := Fintype.ofFinite _
  have hprivate (v : V) (hv : component E labels v = none) : (labels v).card ≤ 1 := by
    have hne := (component_none_iff E labels v).mp hv
    have hc := hcard v
    omega
  have hroots (i : I) : component E labels (root i) = none ∧ i ∈ labels (root i) := by
    refine ⟨(component_none_iff E labels _).mpr ?_, ?_⟩ <;> simp [hroot]
  have hrep (a : K) : ∃ u, component E labels u = some a ∧ 2 ≤ (labels u).card := by
    induction a using SimpleGraph.ConnectedComponent.ind with
    | h v =>
      refine ⟨v.val, ?_, ?_⟩
      · simp [component, v.property]
      · exact le_of_eq v.property.symm
  have h := SharedTagExit.component_exit_card (fun u v => (u, v) ∈ E) labels (component E labels)
    hmono (component_constant E labels) hprivate root hroots hreach hrep
  have hset : (Finset.univ.filter fun e : V × V => (e.1, e.2) ∈ E ∧
      (component E labels e.1).isSome ∧ component E labels e.2 = none) =
      E.filter (fun e => (labels e.1).card = 2 ∧ (labels e.2).card ≠ 2) := by
    ext e
    by_cases h0 : (labels e.1).card = 2 <;>
      by_cases h1 : (labels e.2).card = 2 <;> simp [component, shared, h0, h1]
  rw [hset] at h
  simpa only [Nat.card_eq_fintype_card] using h

end PEqualNP.Outside.L_meta_1477.TaggedNetwork

namespace PEqualNP.Outside.L_meta_1477.TaggedNetwork

lemma shared_adj_labels {V I : Type*} [Fintype V] (E : Finset (V × V))
    (labels : V → Finset I) (hmono : ∀ u v, (u, v) ∈ E → labels v ⊆ labels u)
    {u v : shared labels} (ha : ((network E).induce (shared labels)).Adj u v) :
    labels u.val = labels v.val := by
  rcases arrow_or_reverse E ha with h | h
  · exact (Finset.eq_of_subset_of_card_le (hmono _ _ h) (by change (labels u.val).card ≤ (labels v.val).card; rw [u.property, v.property])).symm
  · exact Finset.eq_of_subset_of_card_le (hmono _ _ h) (by change (labels v.val).card ≤ (labels u.val).card; rw [u.property, v.property])

lemma component_labels {V I : Type*} [Fintype V] (E : Finset (V × V))
    (labels : V → Finset I) (hmono : ∀ u v, (u, v) ∈ E → labels v ⊆ labels u)
    (u v : shared labels)
    (he : ((network E).induce (shared labels)).connectedComponentMk u =
      ((network E).induce (shared labels)).connectedComponentMk v) : labels u.val = labels v.val := by
  obtain ⟨p⟩ := SimpleGraph.ConnectedComponent.exact he
  clear he
  induction p with
  | nil => rfl
  | cons ha p ih => exact (shared_adj_labels E labels hmono ha).trans ih

lemma realized_tags_le_components {V I : Type*} [Fintype V]
    (E : Finset (V × V)) (labels : V → Finset I)
    (hmono : ∀ u v, (u, v) ∈ E → labels v ⊆ labels u)
    (T : Finset (Finset I)) (hT : ∀ t ∈ T, ∃ v : shared labels, labels v.val = t) :
    T.card ≤ Nat.card ((network E).induce (shared labels)).ConnectedComponent := by
  classical
  let K := ((network E).induce (shared labels)).ConnectedComponent
  letI : Fintype K := Fintype.ofFinite _
  let rep (t : T) : shared labels := Classical.choose (hT t.val t.property)
  have hrep (t : T) : labels (rep t).val = t.val := Classical.choose_spec (hT t.val t.property)
  let f (t : T) : K := ((network E).induce (shared labels)).connectedComponentMk (rep t)
  have hinj : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    rw [← hrep a, ← hrep b]
    exact component_labels E labels hmono (rep a) (rep b) he
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using Fintype.card_le_of_injective f hinj

lemma private_path {V I : Type*} [Fintype V] [DecidableEq I]
    (E : Finset (V × V)) (labels : V → Finset I)
    (hcard : ∀ v, (labels v).card ≤ 2)
    (hmono : ∀ u v, (u, v) ∈ E → labels v ⊆ labels u)
    {u v : V} (hp : Relation.ReflTransGen (fun u v => (u, v) ∈ E) u v)
    (hu : (labels u).card ≠ 2) (hv : (labels v).card ≠ 2) :
    ((network E).induce {w | (labels w).card ≠ 2}).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  classical
  revert hu
  induction hp using Relation.ReflTransGen.head_induction_on with
  | refl => intro hu; exact .refl _
  | @head u w he hp ih =>
    intro hu
    have hw : (labels w).card ≠ 2 := by
      have hc := Finset.card_le_card (hmono u w he)
      have hb := hcard u
      omega
    have htail := ih hw
    by_cases huw : u = w
    · subst w
      exact htail
    · exact (show ((network E).induce {w | (labels w).card ≠ 2}).Adj ⟨u, hu⟩ ⟨w, hw⟩ from
        adj_of_arrow E he huw).reachable.trans htail

lemma private_reach_roots {V : Type*} [Fintype V] (m : ℕ)
    (E : Finset (V × V)) (labels : V → Finset (Fin m))
    (hne : ∀ v, (labels v).Nonempty) (hcard : ∀ v, (labels v).card ≤ 2)
    (hmono : ∀ u v, (u, v) ∈ E → labels v ⊆ labels u)
    (root : Fin m → V) (hroot : ∀ i, labels (root i) = {i})
    (hreach : ∀ u i, i ∈ labels u → Relation.ReflTransGen (fun u v => (u, v) ∈ E) u (root i)) :
    ∀ v : {w | (labels w).card ≠ 2}, ∃ i : Fin m,
      ((network E).induce {w | (labels w).card ≠ 2}).Reachable v
        ⟨root i, by simp [hroot]⟩ := by
  intro v
  obtain ⟨i, hi⟩ := hne v.val
  exact ⟨i, private_path E labels hcard hmono (hreach v.val i hi) v.property _⟩

lemma directed_exits_le_cross {V I : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (V × V)) [DecidableRel (network E).Adj] (labels : V → Finset I) :
    let P := Finset.univ.filter fun v : V => (labels v).card ≠ 2
    (E.filter fun e => (labels e.1).card = 2 ∧ (labels e.2).card ≠ 2).card ≤
      ((network E).edgeFinset \ (P.sym2 ∪ (Finset.univ \ P).sym2)).card := by
  classical
  intro P
  let X := E.filter fun e => (labels e.1).card = 2 ∧ (labels e.2).card ≠ 2
  let f : V × V → Sym2 V := fun e => s(e.1, e.2)
  have hinj : Set.InjOn f (X : Set (V × V)) := by
    intro a ha b hb hab
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    rcases Sym2.eq_iff.mp hab with h | h
    · exact Prod.ext h.1 h.2
    · have he : (labels a.1).card = (labels b.2).card := congrArg (fun v => (labels v).card) h.1
      exact (hb'.2 (he ▸ ha'.1)).elim
  have hsub : X.image f ⊆ (network E).edgeFinset \ (P.sym2 ∪ (Finset.univ \ P).sym2) := by
    intro e he
    obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp he
    have hm := (Finset.mem_filter.mp ha).1
    have hp := (Finset.mem_filter.mp ha).2
    have hneq : a.1 ≠ a.2 := by
      intro he
      exact hp.2 (he ▸ hp.1)
    refine Finset.mem_sdiff.mpr ⟨?_, ?_⟩
    · exact SimpleGraph.mem_edgeFinset.mpr (adj_of_arrow E hm hneq)
    · simp [f, P, hp.1, hp.2]
  rw [← Finset.card_image_of_injOn hinj]
  exact Finset.card_le_card hsub

end PEqualNP.Outside.L_meta_1477.TaggedNetwork
