lemma prefix_not_top (n : Nat) (P : Circuit)
    (mono : ∀ g ∈ P.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (top : Bool.not (P.eval (List.ofFn (fun _ : Fin n => true))) = true) :
    ∀ x : Fin n → Bool, Bool.not (P.eval (List.ofFn x)) = true := by
  intro x
  cases hx : P.eval (List.ofFn x) with
  | false => rfl
  | true =>
    have rise := monoW P.gates mono (List.ofFn x)
      (List.ofFn (fun _ : Fin n => true)) (by simp)
      (ofFn_mono n x (fun _ => true) (by simp)) P.output hx
    change P.eval (List.ofFn (fun _ : Fin n => true)) = true at rise
    rw [rise] at top
    cases top

lemma prefix_not_bottom (n : Nat) (P : Circuit)
    (mono : ∀ g ∈ P.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (bottom : Bool.not (P.eval (List.ofFn (fun _ : Fin n => false))) = false) :
    ∀ x : Fin n → Bool, Bool.not (P.eval (List.ofFn x)) = false := by
  intro x
  have low : P.eval (List.ofFn (fun _ : Fin n => false)) = true := by
    simpa using bottom
  have rise := monoW P.gates mono (List.ofFn (fun _ : Fin n => false))
    (List.ofFn x) (by simp) (ofFn_mono n (fun _ => false) x (by simp)) P.output low
  change P.eval (List.ofFn x) = true at rise
  simp [rise]

lemma one_not_and_terminal_reduces (n : Nat) (P : Circuit)
    (f q : (Fin n → Bool) → Bool)
    (mono : ∀ g ∈ P.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (top : f (fun _ => true) = true)
    (computes : ∀ x : Fin n → Bool,
      (Bool.not (P.eval (List.ofFn x)) && q x) = f x) :
    (∀ x : Fin n → Bool, Bool.not (P.eval (List.ofFn x)) = true) ∧
      ∀ x : Fin n → Bool, q x = f x := by
  have atTop := computes (fun _ => true)
  rw [top] at atTop
  have constant := prefix_not_top n P mono (Bool.and_eq_true_iff.mp atTop).1
  exact ⟨constant, fun x => by simpa [constant x] using computes x⟩

lemma one_not_or_terminal_reduces (n : Nat) (P : Circuit)
    (f q : (Fin n → Bool) → Bool)
    (mono : ∀ g ∈ P.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (bottom : f (fun _ => false) = false)
    (computes : ∀ x : Fin n → Bool,
      (Bool.not (P.eval (List.ofFn x)) || q x) = f x) :
    (∀ x : Fin n → Bool, Bool.not (P.eval (List.ofFn x)) = false) ∧
      ∀ x : Fin n → Bool, q x = f x := by
  have atBottom := computes (fun _ => false)
  rw [bottom] at atBottom
  have constant := prefix_not_bottom n P mono (Bool.or_eq_false_iff.mp atBottom).1
  exact ⟨constant, fun x => by simpa [constant x] using computes x⟩
