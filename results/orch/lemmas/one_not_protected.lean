import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_2592_aux.ProtectedNot

lemma increase_signal_preserves {α : Type*} (f A B : α → Bool) (G : α → Bool → Bool)
    (mono : ∀ x, Monotone (G x)) (increase : ∀ x, A x ≤ B x)
    (agree : ∀ x, f x = false → A x = B x)
    (correct : ∀ x, G x (A x) = f x) : ∀ x, G x (B x) = f x := by
  intro x
  cases hf : f x with
  | false => rw [← agree x hf, correct x, hf]
  | true =>
      apply le_antisymm
      · exact le_top
      · have h := mono x (increase x)
        rwa [correct x, hf] at h

def edges : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),
    (5,7),(7,9),(9,6),(6,8),(8,5)]

def petersen (x : Fin 10 → Bool) : Bool := edges.any (fun e => x e.1 && x e.2)

def adjacent (a b : Fin 10) : Prop := (a,b) ∈ edges ∨ (b,a) ∈ edges

lemma edge_true (x : Fin 10 → Bool) (a b : Fin 10) (hab : adjacent a b)
    (ha : x a = true) (hb : x b = true) : petersen x = true := by
  apply List.any_eq_true.mpr
  rcases hab with hab | hab
  · exact ⟨(a,b), hab, by simp [ha, hb]⟩
  · exact ⟨(b,a), hab, by simp [ha, hb]⟩

lemma protected_difference (G : (Fin 10 → Bool) → Bool → Bool)
    (a b c : Fin 10) (hca : adjacent c a) (hcb : adjacent c b)
    (mono : ∀ x, Monotone (G x))
    (correct : ∀ x, G x ((x a || x b) && !x c) = petersen x) :
    ∀ x, G x (x a || x b) = petersen x := by
  apply increase_signal_preserves petersen
    (fun x => (x a || x b) && !x c) (fun x => x a || x b) G mono
  · intro x
    cases x a <;> cases x b <;> cases x c <;> decide
  · intro x hf
    cases hc : x c with
    | false => simp
    | true =>
        have ha : x a = false := by
          cases h : x a with
          | false => rfl
          | true =>
              have bad := edge_true x c a hca hc h
              rw [hf] at bad
              cases bad
        have hb : x b = false := by
          cases h : x b with
          | false => rfl
          | true =>
              have bad := edge_true x c b hcb hc h
              rw [hf] at bad
              cases bad
        simp [ha, hb]
  · exact correct

lemma petersen_formula (x : Fin 10 → Bool) : petersen x =
    (x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
      x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
      x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5) := by
  simp [petersen, edges, Bool.or_assoc]

end PEqualNP.Outside.L_meta_2592_aux.ProtectedNot
