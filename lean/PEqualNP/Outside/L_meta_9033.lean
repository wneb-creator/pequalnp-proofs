import Mathlib.Data.Fin.Basic

namespace PEqualNP.Outside.L_meta_9033_aux

def boundaryGate (op a b : Bool) : Bool :=
  if op then a && b else a || b

def boundaryRowRel (expected a b : Bool) : Prop :=
  a = expected → b = expected

lemma boundaryRowRel_refl (expected a : Bool) :
    boundaryRowRel expected a a := by
  intro h
  exact h

lemma boundaryRowRel_trans {expected a b c : Bool}
    (hab : boundaryRowRel expected a b)
    (hbc : boundaryRowRel expected b c) :
    boundaryRowRel expected a c := by
  intro h
  exact hbc (hab h)

lemma boundaryRowRel_gate (expected op a b a' b' : Bool)
    (ha : boundaryRowRel expected a a')
    (hb : boundaryRowRel expected b b') :
    boundaryRowRel expected (boundaryGate op a b) (boundaryGate op a' b') := by
  cases expected <;> cases op <;> cases a <;> cases b <;>
    cases a' <;> cases b' <;> simp_all [boundaryRowRel, boundaryGate]

lemma boundaryReplacement (expected : Bool)
    (n k pivot source output : ℕ)
    (op : ℕ → Bool) (a b : ℕ → ℕ) (before after : ℕ → Bool)
    (hcausal : ∀ i < k, a i < n + i ∧ b i < n + i)
    (hpivot : pivot < k)
    (hsource : source < n + pivot)
    (hout : output < n + k)
    (hraw : ∀ j < n, after j = before j)
    (hbefore : ∀ i < k,
      before (n + i) = boundaryGate (op i) (before (a i)) (before (b i)))
    (hafter : ∀ i < k, i ≠ pivot →
      after (n + i) = boundaryGate (op i) (after (a i)) (after (b i)))
    (halias : after (n + pivot) = after source)
    (hdominance : boundaryRowRel expected (before (n + pivot)) (before source))
    (houtput : before output = expected) :
    after output = expected := by
  have hrel : ∀ j, j < n + k → boundaryRowRel expected (before j) (after j) := by
    intro j
    induction j using Nat.strong_induction_on with
    | ind j ih =>
      intro hj
      by_cases hinput : j < n
      · rw [hraw j hinput]
        exact boundaryRowRel_refl expected (before j)
      · obtain ⟨i, rfl⟩ : ∃ i, j = n + i := by
          exact ⟨j - n, by omega⟩
        have hi : i < k := by omega
        by_cases heq : i = pivot
        · subst i
          rw [halias]
          exact boundaryRowRel_trans hdominance
            (ih source hsource (Nat.lt_trans hsource (Nat.add_lt_add_left hpivot n)))
        · rw [hbefore i hi, hafter i hi heq]
          exact boundaryRowRel_gate expected (op i) _ _ _ _
            (ih (a i) (hcausal i hi).1 (Nat.lt_trans (hcausal i hi).1 hj))
            (ih (b i) (hcausal i hi).2 (Nat.lt_trans (hcausal i hi).2 hj))
  exact hrel output hout houtput

end PEqualNP.Outside.L_meta_9033_aux
