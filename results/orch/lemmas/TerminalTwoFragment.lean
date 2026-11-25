lemma snoc_mono (U V : List Bool) (b c : Bool) (hlen : U.length = V.length)
    (hwire : ∀ i, U.getD i false = true → V.getD i false = true)
    (hbit : b = true → c = true) :
    ∀ i, (U ++ [b]).getD i false = true → (V ++ [c]).getD i false = true := by
  intro i hi
  rcases Nat.lt_trichotomy i U.length with h | h | h
  · rw [getD_snoc_lt _ _ _ h] at hi
    rw [getD_snoc_lt _ _ _ (by omega)]
    exact hwire i hi
  · rw [h, getD_snoc_eq] at hi
    rw [h, hlen, getD_snoc_eq]
    exact hbit hi
  · rw [getD_snoc_gt _ _ _ h] at hi
    cases hi

lemma two_not_terminal_reduces (n : Nat) (f : (Fin n → Bool) → Bool)
    (bottom : f (fun _ => false) = false) (top : f (fun _ => true) = true)
    (P Q : Circuit)
    (pMono : ∀ g ∈ P.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (qMono : ∀ g ∈ Q.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (computes : ∀ x : Fin n → Bool,
      Bool.not (Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)])) = f x) :
    ∀ x : Fin n → Bool, P.eval (List.ofFn x) = f x := by
  have rise (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
      (b c : Bool) (hbc : b = true → c = true) :
      Q.eval (P.wires (List.ofFn x) ++ [b]) = true →
      Q.eval (P.wires (List.ofFn y) ++ [c]) = true := by
    apply monoW Q.gates qMono _ _ _ _ Q.output
    · have hx := wf_len P.gates (List.ofFn x)
      have hy := wf_len P.gates (List.ofFn y)
      change (wf P.gates (List.ofFn x) ++ [b]).length =
        (wf P.gates (List.ofFn y) ++ [c]).length
      simp [hx, hy]
    · apply snoc_mono _ _ _ _ _ _ hbc
      · have hx := wf_len P.gates (List.ofFn x)
        have hy := wf_len P.gates (List.ofFn y)
        change (wf P.gates (List.ofFn x)).length = (wf P.gates (List.ofFn y)).length
        simp [hx, hy]
      · exact monoW P.gates pMono _ _ (by simp) (ofFn_mono n x y hxy)
  have low : Q.eval (P.wires (List.ofFn (fun _ : Fin n => false)) ++
      [!P.eval (List.ofFn (fun _ : Fin n => false))]) = true := by
    simpa [bottom] using computes (fun _ => false)
  have high : Q.eval (P.wires (List.ofFn (fun _ : Fin n => true)) ++
      [!P.eval (List.ofFn (fun _ : Fin n => true))]) = false := by
    simpa [top] using computes (fun _ => true)
  intro x
  cases hx : P.eval (List.ofFn x) with
  | false =>
    have qx : Q.eval (P.wires (List.ofFn x) ++ [true]) = true :=
      rise (fun _ => false) x (by simp) _ true (by simp) low
    simpa [hx, qx] using computes x
  | true =>
    have qx : Q.eval (P.wires (List.ofFn x) ++ [false]) = false := by
      cases hq : Q.eval (P.wires (List.ofFn x) ++ [false]) with
      | false => rfl
      | true =>
        have impossible := rise x (fun _ => true) (by simp) false
          (!P.eval (List.ofFn (fun _ : Fin n => true))) (by simp) hq
        rw [high] at impossible
        cases impossible
    simpa [hx, qx] using computes x
