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
