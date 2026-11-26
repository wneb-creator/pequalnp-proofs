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

def crossed (a₀ b₀ a₁ b₁ : Bool) : Prop :=
  (a₀ = true ∧ b₀ = false ∧ a₁ = false ∧ b₁ = true) ∨
  (a₀ = false ∧ b₀ = true ∧ a₁ = true ∧ b₁ = false)

lemma boolGate_distributes (op merge a₀ b₀ a₁ b₁ : Bool)
    (h : op ≠ merge → ¬ crossed a₀ b₀ a₁ b₁) :
    boolGate op (boolGate merge a₀ a₁) (boolGate merge b₀ b₁) =
      boolGate merge (boolGate op a₀ b₀) (boolGate op a₁ b₁) := by
  cases op <;> cases merge <;> cases a₀ <;> cases b₀ <;> cases a₁ <;> cases b₁ <;>
    simp_all [boolGate, crossed]

-- Unless a gate crosses the two rows, evaluation preserves their union or intersection.
lemma causal_merge_agreement
    {n k : Nat} (a b : Fin k → Nat) (op : Fin k → Bool) (merge : Bool)
    (w₀ w₁ wm : Nat → Bool)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (hraw : ∀ i, i < n → wm i = boolGate merge (w₀ i) (w₁ i))
    (heval₀ : ∀ j, w₀ (n + j.val) = boolGate (op j) (w₀ (a j)) (w₀ (b j)))
    (heval₁ : ∀ j, w₁ (n + j.val) = boolGate (op j) (w₁ (a j)) (w₁ (b j)))
    (hevalm : ∀ j, wm (n + j.val) = boolGate (op j) (wm (a j)) (wm (b j)))
    (hcross : ∀ j, op j ≠ merge → ¬ crossed (w₀ (a j)) (w₀ (b j)) (w₁ (a j)) (w₁ (b j))) :
    ∀ i, i < n + k → wm i = boolGate merge (w₀ i) (w₁ i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro hi
    by_cases hin : i < n
    · exact hraw i hin
    · let j : Fin k := ⟨i - n, by omega⟩
      have hij : i = n + j.val := by dsimp [j]; omega
      have hea := ih (a j) (by simpa [← hij] using ha j) (by have := ha j; omega)
      have heb := ih (b j) (by simpa [← hij] using hb j) (by have := hb j; omega)
      rw [hij, hevalm, heval₀, heval₁, hea, heb]
      exact boolGate_distributes _ _ _ _ _ _ (hcross j)

-- A union accepted above two rejected rows forces an AND crossing; the dual forces OR.
lemma crossing_gate_exists
    {n k out : Nat} (a b : Fin k → Nat) (op : Fin k → Bool) (merge : Bool)
    (w₀ w₁ wm : Nat → Bool)
    (ha : ∀ j, a j < n + j.val) (hb : ∀ j, b j < n + j.val)
    (hraw : ∀ i, i < n → wm i = boolGate merge (w₀ i) (w₁ i))
    (heval₀ : ∀ j, w₀ (n + j.val) = boolGate (op j) (w₀ (a j)) (w₀ (b j)))
    (heval₁ : ∀ j, w₁ (n + j.val) = boolGate (op j) (w₁ (a j)) (w₁ (b j)))
    (hevalm : ∀ j, wm (n + j.val) = boolGate (op j) (wm (a j)) (wm (b j)))
    (hout : out < n + k) (hflip : wm out ≠ boolGate merge (w₀ out) (w₁ out)) :
    ∃ j, op j ≠ merge ∧ crossed (w₀ (a j)) (w₀ (b j)) (w₁ (a j)) (w₁ (b j)) := by
  by_contra h
  apply hflip
  apply causal_merge_agreement a b op merge w₀ w₁ wm ha hb hraw heval₀ heval₁ hevalm
    (fun j hop hc => h ⟨j, hop, hc⟩) out hout

end PEqualNP.Outside.L_meta_9033
