import Mathlib

namespace PEqualNP.Outside.L_meta_2592.MassTwo

abbrev Wire (R : Type) := R → Bool

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

lemma sum_map_two_le {α : Type} (f : α → Nat) {xs : List α} {a b : α}
    (ha : a ∈ xs) (hb : b ∈ xs) (hne : a ≠ b) :
    f a + f b ≤ (xs.map f).sum := by
  induction xs with
  | nil => simp at ha
  | cons c xs ih =>
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp ha with h | haTail
    · subst c
      have hb' : b ∈ xs := (List.mem_cons.mp hb).resolve_left (Ne.symm hne)
      have hh : f b ≤ (xs.map f).sum := List.le_sum_of_mem (List.mem_map_of_mem hb')
      omega
    · rcases List.mem_cons.mp hb with h | hbTail
      · subst c
        have hh : f a ≤ (xs.map f).sum := List.le_sum_of_mem (List.mem_map_of_mem haTail)
        omega
      · have hh := ih haTail hbTail
        omega

lemma mass_two_projected_constants {α R : Type} (project : α → Wire R)
    {xs : List α} {a b : α} (ha : a ∈ xs) (hb : b ∈ xs) (hne : a ≠ b)
    (hca : Constant (project a)) (hcb : Constant (project b)) :
    2 ≤ mass (xs.map project) := by
  classical
  have h := sum_map_two_le (fun c => cost (project c)) ha hb hne
  simpa [mass, List.map_map, Function.comp_def, cost, hca, hcb] using h

end PEqualNP.Outside.L_meta_2592.MassTwo
