import ConstantNot
open PEqualNP.CircuitLowerBounds
namespace PEqualNP.Outside.L_meta_2592.TerminalNot
lemma two_not_pair_impossible (n : Nat) (P Q : Circuit)
    (f : (Fin n → Bool) → Bool) (isOr : Bool)
    (pMono : ∀ g ∈ P.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (qMono : ∀ g ∈ Q.gates, g.op = GateOp.and ∨ g.op = GateOp.or)
    (bottom : f (fun _ => false) = false) (top : f (fun _ => true) = true)
    (computes : ∀ x : Fin n → Bool,
      (if isOr then
        Bool.not (P.eval (List.ofFn x)) ||
          Bool.not (Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]))
      else
        Bool.not (P.eval (List.ofFn x)) &&
          Bool.not (Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]))) = f x) :
    False := by
  let q := fun x : Fin n → Bool =>
    Bool.not (Q.eval (P.wires (List.ofFn x) ++ [!P.eval (List.ofFn x)]))
  have constantAndCorrect : ∃ b : Bool,
      (∀ x : Fin n → Bool, Bool.not (P.eval (List.ofFn x)) = b) ∧
      ∀ x : Fin n → Bool, q x = f x := by
    cases isOr with
    | false =>
      obtain ⟨constant, correct⟩ := one_not_and_terminal_reduces n P f q pMono top computes
      exact ⟨true, constant, correct⟩
    | true =>
      obtain ⟨constant, correct⟩ := one_not_or_terminal_reduces n P f q pMono bottom computes
      exact ⟨false, constant, correct⟩
  obtain ⟨b, constant, correct⟩ := constantAndCorrect
  have low : Q.eval (P.wires (List.ofFn (fun _ : Fin n => false)) ++ [b]) = true := by
    have h := correct (fun _ => false)
    simp only [q, constant, bottom] at h
    simpa using h
  have high : Q.eval (P.wires (List.ofFn (fun _ : Fin n => true)) ++ [b]) = false := by
    have h := correct (fun _ => true)
    simp only [q, constant, top] at h
    simpa using h
  have lengths : (P.wires (List.ofFn (fun _ : Fin n => false))).length =
      (P.wires (List.ofFn (fun _ : Fin n => true))).length := by
    change (wf P.gates _).length = (wf P.gates _).length
    simp [wf_len]
  have pointwise : ∀ i,
      (P.wires (List.ofFn (fun _ : Fin n => false))).getD i false = true →
      (P.wires (List.ofFn (fun _ : Fin n => true))).getD i false = true :=
    monoW P.gates pMono _ _ (by simp) (ofFn_mono n _ _ (by simp))
  have rise := monoW Q.gates qMono
    (P.wires (List.ofFn (fun _ : Fin n => false)) ++ [b])
    (P.wires (List.ofFn (fun _ : Fin n => true)) ++ [b])
    (by simpa only [List.length_append, List.length_singleton] using
      congrArg (fun k => k + 1) lengths)
    (snoc_mono _ _ b b lengths pointwise (fun h => h)) Q.output low
  change Q.eval (P.wires (List.ofFn (fun _ : Fin n => true)) ++ [b]) = true at rise
  rw [high] at rise
  contradiction

end PEqualNP.Outside.L_meta_2592.TerminalNot
