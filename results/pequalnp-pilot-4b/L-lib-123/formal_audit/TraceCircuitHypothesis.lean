import PEqualNP.Defs

namespace PEqualNP.Outside.L_lib_123_Audit

abbrev TraceAddressLength := (Turing.TM2ComputableAux Bool Bool) → ℕ → ℕ → ℕ → ℕ

abbrev TraceBitFamily (width : TraceAddressLength) :=
  (M : (Turing.TM2ComputableAux Bool Bool)) → (B q : ℕ) → (x : List Bool) →
    (Fin (width M B q x.length) → Bool) → Bool

def TraceAddressBound (width : TraceAddressLength) : Prop :=
  ∀ (M : (Turing.TM2ComputableAux Bool Bool)) (B q : ℕ), ∃ c : ℕ,
    ∀ m : ℕ, width M B q m ≤ q * m + c * Nat.log2 (m + 2) + c

def FixedExponentTraceCircuits (width : TraceAddressLength)
    (trace : TraceBitFamily width) (q r : ℕ) : Prop :=
  ∀ (M : (Turing.TM2ComputableAux Bool Bool)) (B : ℕ), ∃ D k : ℕ,
    ∀ x : List Bool,
      PEqualNP.MetaComplexity.HasBinarySize (width M B q x.length)
        (trace M B q x)
        (D * 2 ^ (r * x.length) * (x.length + 1) ^ k + D)

def UniformSublinearTraceCircuits (width : TraceAddressLength)
    (trace : TraceBitFamily width) : Prop :=
  ∃ a b : ℕ, a < b ∧ FixedExponentTraceCircuits width trace (2 * b) (2 * a)

lemma uniform_circuits_leave_integer_margin
    (width : TraceAddressLength) (trace : TraceBitFamily width)
    (h : UniformSublinearTraceCircuits width trace) :
    ∃ r p q : ℕ, 1 ≤ p ∧ r + 1 ≤ p ∧ p < q ∧
      FixedExponentTraceCircuits width trace q r := by
  obtain ⟨a, b, hab, hcircuits⟩ := h
  refine ⟨2 * a, 2 * b - 1, 2 * b, ?_, ?_, ?_, hcircuits⟩ <;> omega

end PEqualNP.Outside.L_lib_123_Audit
