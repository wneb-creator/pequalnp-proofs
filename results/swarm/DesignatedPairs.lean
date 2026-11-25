import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2590_aux.DesignatedPairs

lemma of_indexed_witnesses (J : Finset Nat) (label : Nat → Fin 3)
    (wire : Nat → Nat) (P : Nat → Fin 3 → Prop)
    (hlabel : Set.InjOn label J) (hwire : Set.InjOn wire J)
    (hP : ∀ j ∈ J, P (wire j) (label j)) :
    ∃ S : Finset (Fin 3), S.card = J.card ∧
      ∃ designate : Fin 3 → Nat, Set.InjOn designate S ∧
        ∀ p ∈ S, P (designate p) p := by
  classical
  let S := J.image label
  have hpre (p : Fin 3) (hp : p ∈ S) : ∃ j, j ∈ J ∧ label j = p :=
    Finset.mem_image.mp hp
  let source (p : Fin 3) : Nat :=
    if hp : p ∈ S then Classical.choose (hpre p hp) else 0
  have hsource (p : Fin 3) (hp : p ∈ S) : source p ∈ J ∧ label (source p) = p := by
    simp only [source, dite_eq_left hp]
    exact Classical.choose_spec (hpre p hp)
  refine ⟨S, Finset.card_image_of_injOn hlabel, fun p => wire (source p), ?_, ?_⟩
  · intro p hp q hq he
    have hf : source p = source q :=
      hwire (hsource p hp).1 (hsource q hq).1 he
    exact (hsource p hp).2.symm.trans ((congrArg label hf).trans (hsource q hq).2)
  · intro p hp
    simpa only [(hsource p hp).2] using hP (source p) (hsource p hp).1

def singletonInput {n : Nat} (i : Fin n) : Fin n → Bool := fun j => decide (j = i)

lemma of_prefix_semantics
    (J : Finset Nat) (label : Nat → Fin 3) (wire : Nat → Nat)
    (hlabel : Set.InjOn label J) (hwire : Set.InjOn wire J)
    (old : (Fin 10 → Bool) → Nat → Bool)
    (new : (Fin 6 → Bool) → Nat → Bool)
    (restrict : (Fin 6 → Bool) → Fin 10 → Bool)
    (leftOld rightOld : Fin 3 → Fin 10) (leftNew rightNew : Fin 3 → Fin 6)
    (hsem : ∀ j ∈ J, ∀ x, new x (wire j) = old (restrict x) (10 + j))
    (hmono : ∀ j ∈ J, ∀ x y : Fin 10 → Bool,
      (∀ v, x v = true → y v = true) →
      old x (10 + j) = true → old y (10 + j) = true)
    (hleftInput : ∀ p v, singletonInput (leftOld p) v = true →
      restrict (singletonInput (leftNew p)) v = true)
    (hrightInput : ∀ p v, singletonInput (rightOld p) v = true →
      restrict (singletonInput (rightNew p)) v = true)
    (hleft : ∀ j ∈ J, old (singletonInput (leftOld (label j))) (10 + j) = true)
    (hright : ∀ j ∈ J, old (singletonInput (rightOld (label j))) (10 + j) = true) :
    ∃ S : Finset (Fin 3), S.card = J.card ∧
      ∃ designate : Fin 3 → Nat, Set.InjOn designate S ∧
        ∀ p ∈ S,
          new (singletonInput (leftNew p)) (designate p) = true ∧
          new (singletonInput (rightNew p)) (designate p) = true := by
  apply of_indexed_witnesses J label wire (fun w p =>
    new (singletonInput (leftNew p)) w = true ∧
    new (singletonInput (rightNew p)) w = true) hlabel hwire
  intro j hj
  constructor
  · rw [hsem j hj]
    exact hmono j hj _ _ (hleftInput (label j)) (hleft j hj)
  · rw [hsem j hj]
    exact hmono j hj _ _ (hrightInput (label j)) (hright j hj)

def coordinates (p : Fin 6) : Fin 10 := ![2, 8, 9, 3, 7, 6] p

def restriction (x : Fin 6 → Bool) : Fin 10 → Bool :=
  ![true, false, x 0, x 3, false, false, x 5, x 4, x 1, x 2]

lemma coordinate_singleton_le_restriction : ∀ p : Fin 6, ∀ v : Fin 10,
    singletonInput (coordinates p) v = true →
      restriction (singletonInput p) v = true := by decide +kernel

end PEqualNP.Outside.L_meta_2590_aux.DesignatedPairs
