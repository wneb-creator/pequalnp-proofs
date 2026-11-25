import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.Cofactor

def petersen (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) ||
  (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)

def fixed (u v : Fin 10) (a b : Bool) : Fin 10 → Bool :=
  fun i => (decide (i = u) && a) || (decide (i = v) && b)

def candidate (u v : Fin 10) (a b : Bool) (t : Fin 10) : Fin 10 → Bool :=
  fun i => fixed u v a b i || decide (i = t)

def adjacent (u v : Fin 10) : Bool :=
  petersen (fun i => decide (i = u ∨ i = v))

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
lemma fixedEdge : ∀ (u v : Fin 10) (a b : Bool),
    petersen (fixed u v a b) = (a && b && adjacent u v) := by
  decide +kernel

set_option maxRecDepth 20000 in
set_option maxHeartbeats 20000000 in
lemma candidateExists : ∀ (u v w : Fin 10) (a b : Bool),
    u ≠ w → v ≠ w → (u = v → a = b) →
    petersen (fixed u v a b) = false →
    ∃ t : Fin 10,
      candidate u v a b t u = a ∧ candidate u v a b t v = b ∧
      petersen (Function.update (candidate u v a b t) w false) = false ∧
      petersen (Function.update (candidate u v a b t) w true) = true := by
  decide +kernel

lemma twoFixedCofactor (u v w : Fin 10) (a b : Bool)
    (uw : u ≠ w) (vw : v ≠ w) (consistent : u = v → a = b)
    (safe : (a && b && adjacent u v) = false) :
    ∃ x : Fin 10 → Bool,
      x u = a ∧ x v = b ∧
      petersen (Function.update x w false) = false ∧
      petersen (Function.update x w true) = true := by
  have clean : petersen (fixed u v a b) = false := (fixedEdge u v a b).trans safe
  obtain ⟨t, hu, hv, off, on⟩ := candidateExists u v w a b uw vw consistent clean
  exact ⟨candidate u v a b t, hu, hv, off, on⟩

set_option maxRecDepth 20000 in
lemma adjacentSelf : ∀ u : Fin 10, adjacent u u = false := by
  decide

lemma oneFixedCofactor (u w : Fin 10) (a : Bool) (uw : u ≠ w) :
    ∃ x : Fin 10 → Bool, x u = a ∧
      petersen (Function.update x w false) = false ∧
      petersen (Function.update x w true) = true := by
  obtain ⟨x, hu, _, off, on⟩ := twoFixedCofactor u u w a a uw uw (fun _ => rfl)
    (by simp only [adjacentSelf, Bool.and_false])
  exact ⟨x, hu, off, on⟩

lemma twoFixedEssential (u v w : Fin 10) (a b : Bool)
    (uw : u ≠ w) (vw : v ≠ w) (consistent : u = v → a = b)
    (safe : (a && b && adjacent u v) = false) :
    ∃ x y : Fin 10 → Bool,
      x u = a ∧ y u = a ∧ x v = b ∧ y v = b ∧
      (∀ i, i ≠ w → x i = y i) ∧ petersen x = false ∧ petersen y = true := by
  obtain ⟨z, hu, hv, off, on⟩ := twoFixedCofactor u v w a b uw vw consistent safe
  refine ⟨Function.update z w false, Function.update z w true, ?_, ?_, ?_, ?_, ?_, off, on⟩
  · simpa only [Function.update_of_ne uw] using hu
  · simpa only [Function.update_of_ne uw] using hu
  · simpa only [Function.update_of_ne vw] using hv
  · simpa only [Function.update_of_ne vw] using hv
  · intro i iw
    simp only [Function.update_of_ne iw]

end PEqualNP.Outside.L_meta_2592_aux.Cofactor
