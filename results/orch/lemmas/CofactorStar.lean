import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_4970_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

lemma single_centre_size : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit), E.Nonempty → (∃ t : Fin (n+m), ∀ e ∈ E, Fin.castAdd m e.1 = t ∨ Fin.natAdd n e.2 = t) →
      let computes := fun (F : Finset (Fin n × Fin m)) (D : Circuit) => IsAO2 (n+m) D ∧
          ∀ z, circuitFun (n+m) D z = decide (∃ e ∈ F, z (Fin.castAdd m e.1) = true ∧ z (Fin.natAdd n e.2) = true)
      computes E C → E.card ≤ C.size := by
  classical
  let run (gs : List Gate) (x : List Bool) : List Bool :=
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

  have other (x : List Bool) (b : Bool) (i : ℕ) (h : i ≠ x.length) :
      (x ++ [b]).getD i false = x.getD i false := by
    by_cases lt : i < x.length
    · exact List.getD_append _ _ _ _ lt
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

  have cone (gs : List Gate) (arity : ∀ g ∈ gs, g.inputs.length ≤ 2)
      (n : ℕ) (T : Finset ℕ) :
      ∃ S : Finset ℕ, S.card ≤ T.card + gs.length ∧
        ∀ x y : List Bool, x.length = n → y.length = n →
          (∀ i ∈ S, x.getD i false = y.getD i false) →
          ∀ j ∈ T, (run gs x).getD j false = (run gs y).getD j false := by
    induction gs generalizing n T with
    | nil => exact ⟨T,by simp,fun _ _ _ _ h => h⟩
    | cons g gs ih =>
      obtain ⟨S,small,protect⟩ := ih (fun u hu => arity u (by simp [hu])) (n+1) T
      let value (x : List Bool) := g.op.eval (g.inputs.map fun i => x.getD i false)
      by_cases used : n ∈ S
      · let R := S.erase n ∪ g.inputs.toFinset
        refine ⟨R,?_,?_⟩
        · have h := Finset.card_union_le (S.erase n) g.inputs.toFinset
          have ea := Finset.card_erase_add_one used
          have inputs := List.toFinset_card_le g.inputs
          have two := arity g (by simp)
          change (S.erase n ∪ g.inputs.toFinset).card ≤ T.card + (g :: gs).length
          simp only [List.length_cons]
          omega
        · intro x y hx hy agree
          apply protect (x ++ [value x]) (y ++ [value y]) (by simp [hx]) (by simp [hy])
          intro j hj
          by_cases split : j = n
          · subst j
            have val : value x = value y := by
              apply congrArg g.op.eval
              apply List.map_congr_left
              intro i hi
              exact agree i (Finset.mem_union_right _ (List.mem_toFinset.mpr hi))
            have atEnd (z : List Bool) (b : Bool) : (z ++ [b]).getD z.length false = b := by simp
            calc
              (x ++ [value x]).getD n false = value x := hx ▸ atEnd x _
              _ = value y := val
              _ = (y ++ [value y]).getD n false := hy ▸ (atEnd y _).symm
          · rw [other x _ j (by omega),other y _ j (by omega)]
            exact agree j (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨split,hj⟩))
      · refine ⟨S,by simp only [List.length_cons]; omega,?_⟩
        intro x y hx hy agree
        apply protect (x ++ [value x]) (y ++ [value y]) (by simp [hx]) (by simp [hy])
        intro j hj
        have diff : j ≠ n := fun h => used (h ▸ hj)
        rw [other x _ j (by omega),other y _ j (by omega)]
        exact agree j hj

  have essentialInputs (n : ℕ) (C : Circuit) (arity : ∀ g ∈ C.gates, g.inputs.length ≤ 2)
      (A : Finset (Fin n))
      (essential : ∀ i ∈ A, ∃ x y : Fin n → Bool,
        (∀ j, j ≠ i → x j = y j) ∧ circuitFun n C x ≠ circuitFun n C y) :
      A.card ≤ C.size + 1 := by
    obtain ⟨S,hs,protect⟩ := cone C.gates arity n {C.output}
    have subset : A.image Fin.val ⊆ S := by
      intro j hj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hj
      by_contra notin
      obtain ⟨x,y,agree,changeVal⟩ := essential i hi
      apply changeVal
      apply protect (List.ofFn x) (List.ofFn y) (by simp) (by simp) _ C.output (by simp)
      intro k hk
      by_cases h : k < n
      · rw [List.getD_eq_getElem (List.ofFn x) _ (by simpa using h),List.getD_eq_getElem (List.ofFn y) _ (by simpa using h)]
        simp only [List.getElem_ofFn]
        exact agree ⟨k,h⟩ (fun e => notin ((congrArg Fin.val e) ▸ hk))
      · rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]
    have ci := Finset.card_le_card subset
    rw [Finset.card_image_of_injective _ Fin.val_injective] at ci
    simp only [Finset.card_singleton] at hs
    change A.card ≤ C.gates.length + 1
    omega

  have star : ∀ (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit), E.Nonempty → (∃ t : Fin (n+m), ∀ e ∈ E, Fin.castAdd m e.1 = t ∨ Fin.natAdd n e.2 = t) →
      let computes := fun (F : Finset (Fin n × Fin m)) (D : Circuit) => IsAO2 (n+m) D ∧
          ∀ z, circuitFun (n+m) D z = decide (∃ e ∈ F, z (Fin.castAdd m e.1) = true ∧ z (Fin.natAdd n e.2) = true)
      computes E C → E.card ≤ C.size := by
    classical
    intro n m E C nonempty single
    dsimp only
    rintro ⟨ao,correct⟩
    obtain ⟨t,atCenter⟩ := single
    let L (p : Fin n) := Fin.castAdd m p
    let R (l : Fin m) := Fin.natAdd n l
    have separated (p : Fin n) (l : Fin m) : L p ≠ R l := by
      intro e
      have h := congrArg Fin.val e
      change p.val = n + l.val at h
      omega
    let ends (e : Fin n × Fin m) : Finset (Fin (n+m)) := {L e.1,R e.2}
    let A := E.biUnion ends
    have left (e) (he : e ∈ E) : L e.1 ∈ A :=
      Finset.mem_biUnion.mpr ⟨e,he,by simp [ends]⟩
    have right (e) (he : e ∈ E) : R e.2 ∈ A :=
      Finset.mem_biUnion.mpr ⟨e,he,by simp [ends]⟩
    have singletonOff (v : Fin (n+m)) :
        circuitFun (n+m) C (fun j => decide (j = v)) = false := by
      rw [correct,decide_eq_false_iff_not]
      rintro ⟨e,_,one,two⟩
      exact separated e.1 e.2 ((of_decide_eq_true one).trans (of_decide_eq_true two).symm)
    have edgeOn (e) (he : e ∈ E) :
        circuitFun (n+m) C (fun j => decide (j ∈ ends e)) = true := by
      rw [correct,decide_eq_true_eq]
      exact ⟨e,he,by simp [ends,L],by simp [ends,R]⟩
    have active : A.card ≤ C.size + 1 := by
      apply essentialInputs (n+m) C (fun g hg => Nat.le_of_eq (ao.2.2 g hg)) A
      intro i hi
      obtain ⟨e,he,hi⟩ := Finset.mem_biUnion.mp hi
      have keep (u v : Fin (n+m)) (record : ends e = {u,v}) :
          ∃ x y : Fin (n+m) → Bool, (∀ j, j ≠ u → x j = y j) ∧
            circuitFun (n+m) C x ≠ circuitFun (n+m) C y := by
        refine ⟨fun j => decide (j ∈ ends e),fun j => decide (j = v),?_,?_⟩
        · intro j diff
          simp [record,diff]
        · rw [edgeOn e he,singletonOff]
          decide
      rcases (show i = L e.1 ∨ i = R e.2 by simpa [ends] using hi) with rfl | rfl
      · exact keep _ _ rfl
      · exact keep _ _ (Finset.pair_comm ..)
    obtain ⟨e₀,h₀⟩ := nonempty
    have tin : t ∈ A := (atCenter e₀ h₀).elim (fun h => h ▸ left e₀ h₀) (fun h => h ▸ right e₀ h₀)
    let opposite (e : Fin n × Fin m) := if L e.1 = t then R e.2 else L e.1
    have otherIn (e) (he : e ∈ E) : opposite e ∈ A.erase t := by
      rcases atCenter e he with l | r
      · change L e.1 = t at l
        have nr : R e.2 ≠ t := fun h => separated _ _ (l.trans h.symm)
        simpa [opposite,l] using Finset.mem_erase.mpr ⟨nr,right e he⟩
      · change R e.2 = t at r
        have nl : L e.1 ≠ t := fun h => separated _ _ (h.trans r.symm)
        simpa [opposite,nl] using Finset.mem_erase.mpr ⟨nl,left e he⟩
    have leftInj : Function.Injective L := by
      intro a b h
      exact Fin.ext (congrArg (fun z : Fin (n+m) => z.val) h)
    have rightInj : Function.Injective R := by
      intro a b h
      apply Fin.ext
      have e := congrArg Fin.val h
      change n + a.val = n + b.val at e
      omega
    have inj : Set.InjOn opposite (E : Set (Fin n × Fin m)) := by
      intro e he f hf same
      by_cases le : L e.1 = t <;> by_cases lf : L f.1 = t <;> simp only [opposite,le,lf,↓reduceIte] at same
      · exact Prod.ext (leftInj (le.trans lf.symm)) (rightInj same)
      · exact (separated f.1 e.2 same.symm).elim
      · exact (separated e.1 f.2 same).elim
      · exact Prod.ext (leftInj same) (rightInj (((atCenter e he).resolve_left le).trans ((atCenter f hf).resolve_left lf).symm))
    have sz := Finset.card_le_card (show E.image opposite ⊆ A.erase t by
      intro j hj
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hj
      exact otherIn e he)
    rw [Finset.card_image_of_injOn inj] at sz
    have := Finset.card_erase_add_one tin
    omega
  exact star


lemma single_centre_cover (n m : ℕ) (E : Finset (Fin n × Fin m)) (C : Circuit)
    (ao : IsAO2 (n + m) C)
    (correct : ∀ x : Fin (n + m) → Bool, circuitFun (n + m) C x =
      decide (∃ e ∈ E, x (Fin.castAdd m e.1) = true ∧ x (Fin.natAdd n e.2) = true))
    (centre : ∃ t : Fin (n + m), ∀ e ∈ E,
      Fin.castAdd m e.1 = t ∨ Fin.natAdd n e.2 = t) :
    ∃ S : Finset (Fin (n + m)),
      (∀ a b, (a, b) ∈ E → Fin.castAdd m a ∈ S ∨ Fin.natAdd n b ∈ S) ∧
      E.card + S.card ≤ C.size + 1 := by
  classical
  by_cases empty : E = ∅
  · refine ⟨∅, ?_, ?_⟩
    · simp [empty]
    · simp [empty]
  · obtain ⟨t, ht⟩ := centre
    have cost := single_centre_size n m E C (Finset.nonempty_iff_ne_empty.mpr empty)
      ⟨t, ht⟩ ⟨ao, correct⟩
    refine ⟨{t}, ?_, ?_⟩
    · intro a b hab
      simpa only [Finset.mem_singleton] using ht (a, b) hab
    · simpa only [Finset.card_singleton] using Nat.add_le_add_right cost 1

end PEqualNP.Outside.L_meta_4970_aux
