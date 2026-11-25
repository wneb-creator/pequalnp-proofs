import StrictRestriction

namespace PEqualNP.Outside.L_meta_2592_aux.SignedRestriction

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_2592_restrict.CircuitProof
open PEqualNP.Outside.L_meta_2592_aux.StrictRestriction

lemma signed_origin_status (n k : ℕ) (pre : List Gate)
    (seedStats : List Stat) (origins : List (Option ℕ)) (v : Fin k)
    (valuation : (Fin n → Bool) → (Fin k → Bool))
    (initial : ∀ x : Fin n → Bool,
      Inv n (List.ofFn x) (List.ofFn (valuation x)) (seedStats, []))
    (known : OriginConstant origins v.val seedStats)
    (ok : ∀ g ∈ pre, Ok g) (wire : ℕ) (sign : Bool)
    (origin : (pre.foldl originStep origins).getD wire none = some v.val)
    (fixed : ∀ x : Fin n → Bool, valuation x v = false)
    (signed : ∀ x : Fin k → Bool,
      (wiresFrom pre (List.ofFn x)).getD wire false = if sign then !(x v) else x v) :
    (elim n pre (seedStats, [])).1.getD wire (Sum.inl false) = Sum.inl sign := by
  have propagated := originConstant_run n pre origins v.val (seedStats, []) known
  obtain ⟨c, status⟩ := propagated.2 wire origin
  let x : Fin n → Bool := fun _ => false
  have invariant := inv_elim n (List.ofFn x) (by simp) pre
    (List.ofFn (valuation x)) (seedStats, []) ok (initial x)
  have value := (invariant.2 wire).2
  rw [status] at value
  change c = (wiresFrom pre (List.ofFn (valuation x))).getD wire false at value
  rw [signed, fixed] at value
  have eq : c = sign := by cases sign <;> simpa using value
  simpa only [eq] using status

lemma marked_of_signed_operand (n k : ℕ) (pre post : List Gate) (g : Gate)
    (seedStats : List Stat) (origins : List (Option ℕ)) (v : Fin k)
    (valuation : (Fin n → Bool) → (Fin k → Bool))
    (initial : ∀ x : Fin n → Bool,
      Inv n (List.ofFn x) (List.ofFn (valuation x)) (seedStats, []))
    (known : OriginConstant origins v.val seedStats)
    (ok : ∀ h ∈ pre, Ok h) (wire a b : ℕ) (inputs : g.inputs = [a, b])
    (operand : wire = a ∨ wire = b) (sign : Bool)
    (origin : (pre.foldl originStep origins).getD wire none = some v.val)
    (fixed : ∀ x : Fin n → Bool, valuation x v = false)
    (signed : ∀ x : Fin k → Bool,
      (wiresFrom pre (List.ofFn x)).getD wire false = if sign then !(x v) else x v)
    (annihilates : (g.op = GateOp.and ∧ sign = false) ∨
      (g.op = GateOp.or ∧ sign = true)) :
    Marked ((pre ++ g :: post).foldl originStep origins)
      (elim n (pre ++ g :: post) (seedStats, [])).1 (k + pre.length) := by
  have status := signed_origin_status n k pre seedStats origins v valuation initial known
    ok wire sign origin fixed signed
  have statsLength : seedStats.length = k := by
    simpa only [List.length_ofFn] using (initial (fun _ => false)).1
  have originLength : origins.length = k := known.1.trans statsLength
  apply marked_of_constant_binary n k pre post g origins (seedStats, [])
    originLength statsLength
  · rcases annihilates with ⟨op, _⟩ | ⟨op, _⟩ <;> simp [isNotGate, op]
  · refine ⟨sign, ?_⟩
    simp only [inputs, List.map_cons, List.map_nil]
    apply annihilating_status g.op sign _ _ _ annihilates
    rcases operand with rfl | rfl
    · exact Or.inl status
    · exact Or.inr status

end PEqualNP.Outside.L_meta_2592_aux.SignedRestriction
