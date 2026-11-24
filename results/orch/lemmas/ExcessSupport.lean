import PEqualNP.Outside.L_meta_1024

namespace PEqualNP.Outside.L_meta_1024_aux.Excess

open PEqualNP.CircuitLowerBounds

lemma support_univ (w : Fin 13) (f : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Support.Band x → f x = Support.target w x)
    (hhigh : f (Support.fromZeros (Support.line w)) = true)
    (S : Finset (Fin 13)) (hsupport : Support.Supports f S) :
    S = Finset.univ := by
  classical
  apply Finset.eq_univ_of_forall
  intro p
  by_cases hp : p ∈ Support.line w
  · exact Support.support_contains_line w f hcorrect S hsupport hp
  · by_contra hnot
    have hband : Support.Band (Support.fromZeros (insert p (Support.line w))) := by
      left
      rw [Support.zeroSet_fromZeros, Finset.card_insert_of_notMem hp, Clamp.line_card]
    have htarget : Support.target w
        (Support.fromZeros (insert p (Support.line w))) = false := by
      have hn : ¬ ∃ q ∈ Support.line w,
          Support.fromZeros (insert p (Support.line w)) q = true := by
        rintro ⟨q, hq, hh⟩
        simp [Support.fromZeros, hq] at hh
      simp only [Support.target, hn, decide_false]
    have heq : f (Support.fromZeros (Support.line w)) =
        f (Support.fromZeros (insert p (Support.line w))) := by
      apply hsupport
      intro q hq
      have hqp : q ≠ p := by
        intro he
        subst q
        exact hnot hq
      simp [Support.fromZeros, hqp]
    rw [hhigh, hcorrect _ hband, htarget] at heq
    exact Bool.noConfusion heq

lemma mem_support (w : Fin 13) (f : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Support.Band x → f x = Support.target w x)
    (hhigh : f (Support.fromZeros (Support.line w)) = true)
    (S : Finset (Fin 13)) (hsupport : Support.Supports f S) (p : Fin 13) : p ∈ S := by
  rw [support_univ w f hcorrect hhigh S hsupport]
  exact Finset.mem_univ p

lemma support_card (w : Fin 13) (f : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Support.Band x → f x = Support.target w x)
    (hhigh : f (Support.fromZeros (Support.line w)) = true)
    (S : Finset (Fin 13)) (hsupport : Support.Supports f S) : S.card = 13 := by
  rw [support_univ w f hcorrect hhigh S hsupport]
  simp

lemma complement_false_of_support (w : Fin 13) (f : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Support.Band x → f x = Support.target w x)
    (S : Finset (Fin 13)) (hsupport : Support.Supports f S) (hsmall : S.card ≤ 12) :
    f (Support.fromZeros (Support.line w)) = false := by
  cases hh : f (Support.fromZeros (Support.line w)) with
  | false => rfl
  | true =>
    have hc := support_card w f hcorrect hh S hsupport
    omega

lemma bounded_of_complement_false (w : Fin 13) (f : (Fin 13 → Bool) → Bool)
    (hmono : ∀ x y, (∀ p, x p = true → y p = true) → f x = true → f y = true)
    (hfalse : f (Support.fromZeros (Support.line w)) = false) :
    ∀ x, f x = true → Support.target w x = true := by
  intro x hx
  by_contra ht
  have hline : ∀ p ∈ Support.line w, x p ≠ true := by
    intro p hp hxp
    apply ht
    simp only [Support.target, decide_eq_true_eq]
    exact ⟨p, hp, hxp⟩
  have hle : ∀ p, x p = true → Support.fromZeros (Support.line w) p = true := by
    intro p hp
    have hn : p ∉ Support.line w := fun hm => hline p hm hp
    simp [Support.fromZeros, hn]
  have hh := hmono x (Support.fromZeros (Support.line w)) hle hx
  rw [hfalse] at hh
  exact Bool.noConfusion hh

lemma bounded_of_support (w : Fin 13) (f : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Support.Band x → f x = Support.target w x)
    (hmono : ∀ x y, (∀ p, x p = true → y p = true) → f x = true → f y = true)
    (S : Finset (Fin 13)) (hsupport : Support.Supports f S) (hsmall : S.card ≤ 12) :
    ∀ x, f x = true → Support.target w x = true := by
  exact bounded_of_complement_false w f hmono
    (complement_false_of_support w f hcorrect S hsupport hsmall)

lemma raw_essential (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hcorrect : ∀ x, Support.Band x →
      Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Support.target w x)
    (hhigh : Circuit.eval ⟨gs, o⟩
      (List.ofFn (Support.fromZeros (Support.line w))) = true) (p : Fin 13) :
    p ∈ Cut.essential (M := 13) 13 ∅ gs o := by
  apply mem_support w (fun x => Circuit.eval ⟨gs, o⟩ (List.ofFn x))
    hcorrect hhigh (Cut.essential (M := 13) 13 ∅ gs o) ?_ p
  intro x y hxy
  change Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Circuit.eval ⟨gs, o⟩ (List.ofFn y)
  rw [← Cut.cut_empty, ← Cut.cut_empty]
  exact Cut.essential_supports 13 ∅ gs o x y hxy

lemma circuit_length (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hcorrect : ∀ x, Support.Band x →
      Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Support.target w x)
    (hhigh : Circuit.eval ⟨gs, o⟩
      (List.ofFn (Support.fromZeros (Support.line w))) = true) :
    12 ≤ gs.length := by
  have hraw : ∀ t ∈ Cut.essential (M := 13 + gs.length) 13 ∅ gs o, t.val < 13 := by
    intro t ht
    rcases Cut.essential_sources 13 ∅ gs o t ht with h | h
    · exact h
    · exact False.elim (Finset.notMem_empty _ h)
  have hc : (Cut.essential (M := 13 + gs.length) 13 ∅ gs o).card ≤ gs.length + 1 := by
    simpa using Cut.essential_bound (M := 13 + gs.length) 13 ∅ gs o hg
      (Finset.empty_subset _)
  obtain ⟨S, hS, hs⟩ := Cut.raw_support_exists (n := 13) ∅ gs o (gs.length + 1) hraw hc
  have hcard := support_card w (fun x => Circuit.eval ⟨gs, o⟩ (List.ofFn x))
    hcorrect hhigh S hs
  omega

lemma complement_false_of_short (gs : List Gate) (o : ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hcorrect : ∀ x, Support.Band x →
      Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Support.target w x)
    (hsmall : gs.length ≤ 11) :
    Circuit.eval ⟨gs, o⟩ (List.ofFn (Support.fromZeros (Support.line w))) = false := by
  cases hh : Circuit.eval ⟨gs, o⟩
      (List.ofFn (Support.fromZeros (Support.line w))) with
  | false => rfl
  | true =>
    have hb := circuit_length gs o w hg hcorrect hh
    omega

lemma prefix_length (gs : List Gate) (o k : ℕ) (w : Fin 13)
    (hg : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (hcorrect : ∀ x, Support.Band x →
      Circuit.eval ⟨gs, o⟩ (List.ofFn x) = Support.target w x)
    (hhigh : Circuit.eval ⟨gs, o⟩
      (List.ofFn (Support.fromZeros (Support.line w))) = true)
    (hk : k ≤ gs.length) (ho : o < 13 + k) : 12 ≤ k := by
  have heq : ∀ x : Fin 13 → Bool,
      Circuit.eval ⟨gs.take k, o⟩ (List.ofFn x) =
        Circuit.eval ⟨gs, o⟩ (List.ofFn x) := by
    intro x
    rw [← Cut.cut_empty, ← Cut.cut_empty]
    exact (Cut.cutVal_take 13 ∅ gs x k o hk ho).symm
  have hb := circuit_length (gs.take k) o w
    (fun g hm => hg g (List.mem_of_mem_take hm))
    (fun x hx => (heq x).trans (hcorrect x hx))
    ((heq _).trans hhigh)
  simpa only [List.length_take, Nat.min_eq_left hk] using hb

end PEqualNP.Outside.L_meta_1024_aux.Excess
