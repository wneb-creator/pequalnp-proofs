namespace PEqualNP.Outside.L_meta_6659_aux

lemma override_val_gate_bounded {n : Nat} {D : Dag} (x : Fin n → Bool) (j : Nat)
    (hj : j < D.length) (ha : opA D j < n+j) (hb : opB D j < n+j) :
    val D x (n+j) = gop (tag D j) (val D x (opA D j)) (val D x (opB D j)) := by
  have equation := wl_getD_gate D (List.ofFn x) j hj
  simp only [List.length_ofFn] at equation
  unfold val
  rw [equation,wl_take_getD D _ j _ (by simpa using ha) hj.le,
    wl_take_getD D _ j _ (by simpa using hb) hj.le]

def overrideAlias (D : Dag) (edit : Nat) : Dag :=
  List.ofFn (fun j : Fin D.length =>
    if j.val=edit then (false,opB D edit,opB D edit) else D[j])

lemma overrideAlias_length (D : Dag) (edit : Nat) :
    (overrideAlias D edit).length = D.length := by simp [overrideAlias]

lemma overrideAlias_gate (D : Dag) (edit j : Nat) (hj : j < D.length) :
    tag (overrideAlias D edit) j = (if j=edit then false else tag D j) ∧
    opA (overrideAlias D edit) j = (if j=edit then opB D edit else opA D j) ∧
    opB (overrideAlias D edit) j = (if j=edit then opB D edit else opB D j) := by
  have bound : j < (overrideAlias D edit).length := by simpa [overrideAlias_length] using hj
  rw [tag_eq _ _ bound,opA_eq _ _ bound,opB_eq _ _ bound,
    tag_eq _ _ hj,opA_eq _ _ hj,opB_eq _ _ hj]
  simp only [overrideAlias,List.getElem_ofFn]
  split <;> simp_all

lemma overrideAlias_trace {n : Nat} {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (edit : Nat) :
    GateOverride n D x edit (val (overrideAlias D edit) x) := by
  refine ⟨fun w hw => val_input _ _ w hw,?_,?_⟩
  · intro j hj different
    have facts := overrideAlias_gate D edit j hj
    simp only [ite_eq_right different] at facts
    rw [override_val_gate_bounded (D := overrideAlias D edit) x j (by simpa [overrideAlias_length] using hj)
      (by rw [facts.2.1]; exact (hS j hj).1)
      (by rw [facts.2.2]; exact (hS j hj).2.1),facts.1,facts.2.1,facts.2.2]
  · intro w hw
    exact val_ge _ x w (by simpa [overrideAlias_length] using hw)

lemma overrideAlias_value {n : Nat} {D : Dag} (hS : Strict n D)
    (x : Fin n → Bool) (edit : Nat) (he : edit < D.length) :
    val (overrideAlias D edit) x (n+edit) = val (overrideAlias D edit) x (opB D edit) := by
  have facts := overrideAlias_gate D edit edit he
  simp only at facts
  rw [override_val_gate_bounded (D := overrideAlias D edit) x edit (by simpa [overrideAlias_length] using he)
    (by rw [facts.2.1]; exact (hS edit he).2.1)
    (by rw [facts.2.2]; exact (hS edit he).2.1),facts.1,facts.2.1,facts.2.2]
  simp [gop]

end PEqualNP.Outside.L_meta_6659_aux
