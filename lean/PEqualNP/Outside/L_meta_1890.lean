import PEqualNP.Defs

-- Checked search lemmas only; the full posted theorem remains open.

namespace PEqualNP.Outside.L_meta_1890_aux

def edge (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 10000 in
lemma pinned_dependency : ∀ (v u : Fin 10), v ≠ u →
    ∃ w : Fin 10, ∀ b : Bool,
      let x := fun i : Fin 10 => (i == w) || (b && i == u)
      let y := fun i : Fin 10 => x i || (i == v)
      x u = b ∧ y u = b ∧ edge x = false ∧ edge y = true ∧
        ∀ i : Fin 10, i ≠ v → x i = y i := by
  decide +kernel

def pin (x : Fin 10 → Bool) (i : Fin 11) : Bool :=
  if h : i.val < 10 then x ⟨i.val, h⟩ else x 0 && x 2

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 10000 in
lemma initial_wire_not_implicant : ∀ i : Fin 11,
    ∃ x : Fin 10 → Bool, pin x i = true ∧ edge x = false := by
  decide +kernel

set_option maxHeartbeats 10000000 in
set_option maxRecDepth 10000 in
lemma initial_wire_not_required : ∀ i : Fin 11,
    ∃ x : Fin 10 → Bool, pin x i = false ∧ edge x = true := by
  decide +kernel

lemma zero_input_false : edge (fun _ => false) = false := rfl

lemma pin_zero (i : Fin 11) : pin (fun _ => false) i = false := by
  simp [pin]

lemma initial_wire_not_final_and (i : Fin 11) (h : (Fin 10 → Bool) → Bool) :
    ¬ ∀ x, (pin x i && h x) = edge x := by
  obtain ⟨x, hx, he⟩ := initial_wire_not_required i
  intro correct
  have bad := correct x
  simp [hx, he] at bad

lemma initial_wire_not_final_or (i : Fin 11) (h : (Fin 10 → Bool) → Bool) :
    ¬ ∀ x, (pin x i || h x) = edge x := by
  obtain ⟨x, hx, he⟩ := initial_wire_not_implicant i
  intro correct
  have bad := correct x
  simp [hx, he] at bad

lemma initial_wire_not_final_not (i : Fin 11) :
    ¬ ∀ x, !(pin x i) = edge x := by
  intro correct
  have bad := correct (fun _ => false)
  simp [pin_zero, zero_input_false] at bad

lemma dependency_after_pinning (v u : Fin 10) (hne : v ≠ u) (b : Bool)
    (f : (Fin 10 → Bool) → Bool)
    (absorbs : ∀ x y, x u = b → y u = b →
      (∀ i : Fin 10, i ≠ v → x i = y i) → f x = f y) :
    ¬ ∀ x, f x = edge x := by
  obtain ⟨w, hw⟩ := pinned_dependency v u hne
  obtain ⟨hxu, hyu, hex, hey, hxy⟩ := hw b
  intro correct
  have same := absorbs _ _ hxu hyu hxy
  rw [correct, correct, hex, hey] at same
  cases same

end PEqualNP.Outside.L_meta_1890_aux
