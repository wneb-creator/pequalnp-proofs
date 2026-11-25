
namespace PEqualNP.Outside.L_meta_2590.Semantic
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pet (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def nineEdge (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)

def deleteRename (p : Fin 10) : Fin 10 → Fin 10 :=
  (![
    ![9, 6, 8, 5, 7, 4, 1, 3, 0, 2],
    ![7, 9, 6, 8, 5, 2, 4, 1, 3, 0],
    ![5, 7, 9, 6, 8, 0, 2, 4, 1, 3],
    ![8, 5, 7, 9, 6, 3, 0, 2, 4, 1],
    ![6, 8, 5, 7, 9, 1, 3, 0, 2, 4],
    ![4, 0, 1, 2, 3, 9, 5, 6, 7, 8],
    ![3, 4, 0, 1, 2, 8, 9, 5, 6, 7],
    ![2, 3, 4, 0, 1, 7, 8, 9, 5, 6],
    ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]]) p

def deleteInput (p i : Fin 10) : Option (Fin 9) :=
  if h : (deleteRename p i).val < 9 then some ⟨(deleteRename p i).val, h⟩ else none

lemma deleteInput_self : ∀ p : Fin 10, deleteInput p p = none := by decide +kernel

set_option maxHeartbeats 4000000 in
set_option maxRecDepth 4096 in
lemma pet_deleteInput : ∀ (p : Fin 10) (x : Fin 9 → Bool),
    pet (inputMap (deleteInput p) x) = nineEdge x := by decide +kernel

lemma fix_deleteInput (p : Fin 10) (x : Fin 9 → Bool) :
    fix p false (inputMap (deleteInput p) x) = inputMap (deleteInput p) x := by
  funext i
  by_cases h : i = p
  · subst i
    simp [fix, inputMap, deleteInput_self]
  · simp [fix, h]

lemma nineEdge_nonconstant : ∃ x y, nineEdge x ≠ nineEdge y := by
  exact ⟨fun _ => false, fun _ => true, by decide⟩

lemma pet_false_nonconstant : ∀ p : Fin 10,
    pet (fix p false (fun _ => false)) ≠ pet (fix p false (fun _ => true)) := by decide +kernel

lemma pet_false_floor
    (floor : ∀ D : Circuit, Monotone2 D →
      (∀ x, circuitFun 9 D x = nineEdge x) → 16 ≤ D.size)
    (D : Circuit) (mono : Monotone2 D) (p : Fin 10)
    (computes : ∀ x, circuitFun 10 D x = pet (fix p false x)) : 16 ≤ D.size := by
  have mapped (x : Fin 9 → Bool) :
      circuitFun 10 D (inputMap (deleteInput p) x) = nineEdge x := by
    rw [computes, fix_deleteInput, pet_deleteInput]
  obtain ⟨x, y, different⟩ := nineEdge_nonconstant
  have nc : ∃ x y, circuitFun 10 D (inputMap (deleteInput p) x) ≠
      circuitFun 10 D (inputMap (deleteInput p) y) := by
    exact ⟨x, y, by simpa only [mapped] using different⟩
  obtain ⟨E, legal, same, size⟩ := inputMap_restriction D mono (deleteInput p) nc
  exact (floor E legal (fun x => (same x).trans (mapped x))).trans size

lemma pet_all_drops_le_three
    (floor : ∀ D : Circuit, Monotone2 D →
      (∀ x, circuitFun 9 D x = nineEdge x) → 16 ≤ D.size)
    (C : Circuit) (mono : Monotone2 C) (small : C.size ≤ 19)
    (computes : ∀ x, circuitFun 10 C x = pet x) (p : Fin 10) :
    (droppedSet 10 C.gates (initial p false)).card ≤ 3 := by
  apply all_drops_card_le_three C mono small p
  · exact ⟨fun _ => false, fun _ => true, by simpa only [computes] using pet_false_nonconstant p⟩
  · intro D legal same
    apply pet_false_floor floor D legal p
    intro x
    rw [same, computes]

lemma pet_chargeSet_le_three
    (floor : ∀ D : Circuit, Monotone2 D →
      (∀ x, circuitFun 9 D x = nineEdge x) → 16 ≤ D.size)
    (C : Circuit) (mono : Monotone2 C) (small : C.size ≤ 19)
    (computes : ∀ x, circuitFun 10 C x = pet x) (p : Fin 10) :
    (chargeSet C p).card ≤ 3 := by
  apply chargeSet_card_le_three C mono small p
  · exact ⟨fun _ => false, fun _ => true, by simpa only [computes] using pet_false_nonconstant p⟩
  · intro D legal same
    apply pet_false_floor floor D legal p
    intro x
    rw [same, computes]

end PEqualNP.Outside.L_meta_2590.Semantic
