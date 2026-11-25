import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_gct_231_aux

theorem select_three_coordinates
    {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (F : V →ₗ[ℂ] (Fin 6 → ℂ)) (hF : Function.Injective F)
    (hdim : Module.finrank ℂ V = 3) :
    ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
      Function.Bijective (fun v : V => fun k : Fin 3 => F v (pick k)) := by
  classical
  let φ : Fin 6 → Module.Dual ℂ V := fun i => (LinearMap.proj i).comp F
  have hspan : Submodule.span ℂ (Set.range φ) = ⊤ := by
    apply Submodule.span_eq_top_of_ne_zero
    intro v hv
    have hnonzero : F v ≠ 0 := by
      intro hz
      apply hv
      apply hF
      simpa using hz
    obtain ⟨i, hi⟩ : ∃ i : Fin 6, F v i ≠ 0 := by
      by_contra! h
      exact hnonzero (funext h)
    exact ⟨φ i, ⟨i, rfl⟩, hi⟩
  let S := (linearIndepOn_empty ℂ id).extend (Set.empty_subset (Set.range φ))
  let b0 : Module.Basis S ℂ (Module.Dual ℂ V) := Module.Basis.ofSpan hspan.ge
  let : Finite S := basis_finite_of_finite_spans (Set.finite_range φ) hspan b0
  let : Fintype S := Fintype.ofFinite S
  have hc : Fintype.card S = 3 := by
    rw [← Module.finrank_eq_card_basis b0, Subspace.dual_finrank_eq, hdim]
  let b : Module.Basis (Fin 3) ℂ (Module.Dual ℂ V) :=
    b0.reindex (Fintype.equivFinOfCardEq hc)
  have hb : ∀ k : Fin 3, ∃ j : Fin 6, φ j = b k := by
    intro k
    apply Module.Basis.ofSpan_subset hspan.ge
    exact ⟨(Fintype.equivFinOfCardEq hc).symm k,
      (Module.Basis.reindex_apply b0 (Fintype.equivFinOfCardEq hc) k).symm⟩
  choose pick hpick using hb
  have hpick_inj : Function.Injective pick := by
    intro i j hij
    apply b.linearIndependent.injective
    rw [← hpick i, ← hpick j, hij]
  let G : V →ₗ[ℂ] (Fin 3 → ℂ) := LinearMap.pi fun k => φ (pick k)
  have hG : Function.Injective G := by
    intro v w hvw
    apply (Module.evalEquiv ℂ V).injective
    apply b.ext
    intro k
    change b k v = b k w
    rw [← hpick k]
    exact congrFun hvw k
  refine ⟨pick, hpick_inj, ?_⟩
  change Function.Bijective G
  refine ⟨hG, ?_⟩
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    (by simpa using hdim)).mp hG

end PEqualNP.Outside.L_gct_231_aux
