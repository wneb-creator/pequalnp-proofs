import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_9033

def boolGate (op x y : Bool) : Bool := if op then x && y else x || y

-- Two causal evaluations agreeing at the sole reader agree at every other wire.
-- Before that reader, the reader-agreement premise is vacuous.
lemma sole_reader_agreement
    {n k v : Nat} (p : Fin k) (a b : Fin k → Nat) (op : Fin k → Bool)
    (w₀ w₁ : Nat → Bool)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (hraw : ∀ i, i < n → i ≠ v → w₀ i = w₁ i)
    (hsole : ∀ j, j ≠ p → a j ≠ v ∧ b j ≠ v)
    (heval₀ : ∀ j, w₀ (n + j.val) = boolGate (op j) (w₀ (a j)) (w₀ (b j)))
    (heval₁ : ∀ j, w₁ (n + j.val) = boolGate (op j) (w₁ (a j)) (w₁ (b j))) :
    ∀ i, i < n + k → i ≠ v →
      (n + p.val ≤ i → w₀ (n + p.val) = w₁ (n + p.val)) → w₀ i = w₁ i := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi hiv hp
    by_cases hin : i < n
    · exact hraw i hin hiv
    · let j : Fin k := ⟨i - n, by omega⟩
      have hij : i = n + j.val := by dsimp [j]; omega
      by_cases hjp : j = p
      · have hip : i = n + p.val := hij.trans (congrArg (fun q : Fin k => n + q.val) hjp)
        rw [hip]
        exact hp (by omega)
      · obtain ⟨hav, hbv⟩ := hsole j hjp
        have hea : w₀ (a j) = w₁ (a j) :=
          ih (a j) (by simpa [← hij] using ha j) (by have := ha j; omega) hav
            (fun h => hp (by have := ha j; omega))
        have heb : w₀ (b j) = w₁ (b j) :=
          ih (b j) (by simpa [← hij] using hb j) (by have := hb j; omega) hbv
            (fun h => hp (by have := hb j; omega))
        rw [hij, heval₀, heval₁, hea, heb]

-- An output change forces the sole reader's other input to the identity value.
lemma sole_reader_boundary
    {n k v out : Nat} (p : Fin k) (a b : Fin k → Nat) (op : Fin k → Bool)
    (w₀ w₁ : Nat → Bool)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (hraw : ∀ i, i < n → i ≠ v → w₀ i = w₁ i)
    (hsole : ∀ j, j ≠ p → a j ≠ v ∧ b j ≠ v)
    (heval₀ : ∀ j, w₀ (n + j.val) = boolGate (op j) (w₀ (a j)) (w₀ (b j)))
    (heval₁ : ∀ j, w₁ (n + j.val) = boolGate (op j) (w₁ (a j)) (w₁ (b j)))
    (hleft : a p = v) (hright : b p ≠ v)
    (hv₀ : w₀ v = false) (hv₁ : w₁ v = true)
    (hout : out < n + k) (houtv : out ≠ v) (hflip : w₀ out ≠ w₁ out) :
    w₀ (b p) = op p := by
  have hu : w₀ (b p) = w₁ (b p) :=
    sole_reader_agreement p a b op w₀ w₁ ha hb hraw hsole heval₀ heval₁
      (b p) (by have := hb p; have := p.isLt; omega) hright
      (fun h => by have := hb p; omega)
  have hg : w₀ (n + p.val) ≠ w₁ (n + p.val) := by
    intro heq
    exact hflip (sole_reader_agreement p a b op w₀ w₁ ha hb hraw hsole heval₀ heval₁
      out hout houtv (fun _ => heq))
  rw [heval₀, heval₁, hleft, hv₀, hv₁, ← hu] at hg
  cases hop : op p <;> cases huval : w₀ (b p) <;> simp_all [boolGate]

-- An absorbing other input makes the output insensitive to the solely read input.
lemma sole_reader_saturated
    {n k v out : Nat} (p : Fin k) (a b : Fin k → Nat) (op : Fin k → Bool)
    (w₀ w₁ : Nat → Bool)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (hraw : ∀ i, i < n → i ≠ v → w₀ i = w₁ i)
    (hsole : ∀ j, j ≠ p → a j ≠ v ∧ b j ≠ v)
    (heval₀ : ∀ j, w₀ (n + j.val) = boolGate (op j) (w₀ (a j)) (w₀ (b j)))
    (heval₁ : ∀ j, w₁ (n + j.val) = boolGate (op j) (w₁ (a j)) (w₁ (b j)))
    (hleft : a p = v) (hright : b p ≠ v)
    (hout : out < n + k) (houtv : out ≠ v) (hsat : w₀ (b p) ≠ op p) :
    w₀ out = w₁ out := by
  have hu : w₀ (b p) = w₁ (b p) :=
    sole_reader_agreement p a b op w₀ w₁ ha hb hraw hsole heval₀ heval₁
      (b p) (by have := hb p; have := p.isLt; omega) hright
      (fun h => by have := hb p; omega)
  apply sole_reader_agreement p a b op w₀ w₁ ha hb hraw hsole heval₀ heval₁ out hout houtv
  intro _
  rw [heval₀, heval₁, hleft, ← hu]
  cases hop : op p <;> cases huval : w₀ (b p) <;> simp_all [boolGate]

end PEqualNP.Outside.L_meta_9033
