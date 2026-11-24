import Init
namespace AuditPartsTest
variable (B : Nat → Nat → Nat → Bool)
def auditParts (k start n : Nat) : Nat → Prop
 | 0 => B k start n = true
 | d+1 => auditParts k start (n/2) d ∧ auditParts k (start+n/2) (n-n/2) d
variable (joinBlock : ∀ k start a b,
 B k start a = true → B k (start+a) b = true → B k start (a+b) = true)
include joinBlock
theorem auditParts_all {k start n d} (h : auditParts B k start n d) : B k start n = true := by
 induction d generalizing start n with
 | zero => exact h
 | succ d ih =>
  obtain ⟨hl,hr⟩ := h
  have hh := joinBlock k start (n/2) (n-n/2) (ih hl) (ih hr)
  simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using hh
end AuditPartsTest
