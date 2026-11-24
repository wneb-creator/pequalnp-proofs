import PEqualNP.Outside.L_meta_1024

namespace PEqualNP.Outside.L_meta_1024_aux.FourOrSinks

open PEqualNP.CircuitLowerBounds

lemma shared_parent_essential (a b : Fin 13) (hab : a ≠ b)
    (h k : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Support.Band x → (h x || k x) = Support.target a x)
    (hupperh : ∀ x, h x = true → Support.target b x = true)
    (hupperk : ∀ x, k x = true → Support.target a x = true)
    (p : Fin 13) (hp : p ∈ Support.line a \ Support.line b) :
    ∃ x y : Fin 13 → Bool, (∀ q, q ≠ p → x q = y q) ∧ k x ≠ k y := by
  obtain ⟨hpa, hpb⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨hcard, hpX, hBX, hAX⟩ := OneAnd.separating_row a b hab p hpa hpb
  let X := OneAnd.separatingRow a b p
  let x : Fin 13 → Bool := fun q => decide (q ∈ X)
  let y : Fin 13 → Bool := Function.update x p false
  have hzero : Support.zeroSet x = Finset.univ \ X := by
    ext q
    simp [Support.zeroSet, x]
  have hxband : Support.Band x := by
    apply Or.inr
    rw [hzero]
    simp [Finset.card_sdiff, show X.card = 7 from hcard]
  have hax : Support.target a x = true := by
    apply decide_eq_true
    exact ⟨p, hpa, by simp [x, X, hpX]⟩
  have hbx : Support.target b x = false := by
    simp only [Support.target, decide_eq_false_iff_not]
    rintro ⟨q, hqb, hqx⟩
    have hqX : q ∈ X := by simpa [x] using hqx
    exact Finset.disjoint_left.mp hBX hqb hqX
  have hhx : h x = false := by
    cases he : h x with
    | false => rfl
    | true =>
      have ht := hupperh x he
      rw [hbx] at ht
      cases ht
  have hkx : k x = true := by
    have he := hcorrect x hxband
    simpa only [hhx, Bool.false_or, hax] using he
  have hyline : ∀ q ∈ Support.line a, y q = false := by
    intro q hq
    by_cases hqp : q = p
    · simp [y, hqp]
    · have hqX : q ∉ X := fun h => hqp (hAX q hq h)
      simp [y, Function.update_of_ne hqp, x, hqX]
  have hay : Support.target a y = false := by
    simp only [Support.target, decide_eq_false_iff_not]
    rintro ⟨q, hq, hyq⟩
    rw [hyline q hq] at hyq
    cases hyq
  have hky : k y = false := by
    cases he : k y with
    | false => rfl
    | true =>
      have ht := hupperk y he
      rw [hay] at ht
      cases ht
  refine ⟨x, y, ?_, ?_⟩
  · intro q hqp
    simp [y, Function.update_of_ne hqp]
  · rw [hkx, hky]
    decide

lemma shared_parent_cut_depends (gs : List Gate) (o : ℕ)
    (a b : Fin 13) (hab : a ≠ b) (h : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Support.Band x →
      (h x || Cut.cutVal 13 ∅ gs x o) = Support.target a x)
    (hupperh : ∀ x, h x = true → Support.target b x = true)
    (hupperk : ∀ x, Cut.cutVal 13 ∅ gs x o = true → Support.target a x = true)
    (p : Fin 13) (hp : p ∈ Support.line a \ Support.line b) :
    Cut.Depends 13 ∅ gs o p := by
  exact shared_parent_essential a b hab h (fun x => Cut.cutVal 13 ∅ gs x o)
    hcorrect hupperh hupperk p hp

end PEqualNP.Outside.L_meta_1024_aux.FourOrSinks
