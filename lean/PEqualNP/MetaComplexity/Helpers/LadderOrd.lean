import Mathlib
import PEqualNP.Defs

/-!
# The ladder for every plane order: the order conditional for the closed form

Unverified, a conjecture until a checker accepts a row. If the recorded statement of
L-meta-1358 holds, and the pure arithmetic bound `q * (q * (q + 1 - 2 ^ s) / 2 ^ (s + 1)) ≤ G s 0 N`
holds for the recursion `G` of that statement, then every fan-in-two AND/OR/NOT list with at
most `s` NOT gates computing all line-ORs of a projective plane of order `q ≥ 2` has at least
`q * (q * (q + 1 - 2 ^ s) / 2 ^ (s + 1))` gates. The recursion is built by `Nat.rec`, so its two
equations hold by `rfl`.
-/

namespace PEqualNP.MetaComplexity.LadderOrd

/-- The order conditional: the 1358 statement and the value bound give the closed form. -/
theorem ladderOrd_cond : (∀ (q s : ℕ) (L : Fin (q ^ 2 + q + 1) → Finset (Fin (q ^ 2 + q + 1))), 2 ≤ q → (∀ i : Fin (q ^ 2 + q + 1), (L i).card = q + 1) → (∀ i j : Fin (q ^ 2 + q + 1), i ≠ j → (L i ∩ L j).card = 1) → (∀ p p' : Fin (q ^ 2 + q + 1), p ≠ p' → ∃ i : Fin (q ^ 2 + q + 1), p ∈ L i ∧ p' ∈ L i) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin (q ^ 2 + q + 1) → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) → (∀ (w : Fin (q ^ 2 + q + 1)) (x : Fin (q ^ 2 + q + 1) → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ L w, x v = true)) → (∀ G : ℕ → ℕ → ℕ → ℕ, (∀ b K : ℕ, G 0 b K = ((q ^ 2 + q + 1) - (if b = 0 then 0 else min (q ^ 2 + q + 1) (b * q + 1))) * min K q) → (∀ t b K : ℕ, G (t + 1) b K = (List.range (K + 1)).foldr (fun (j acc : ℕ) => max acc (min (G t (b + j) (K - j)) (G t b j))) 0) → G s 0 (q ^ 2 + q + 1) ≤ gates.length) ∧ (∀ j F T : ℕ, 1 ≤ j → j ≤ q → F + 1 = 2 ^ s → (∀ i : ℕ, i + 1 ≤ F → ∀ z : Finset (Fin (q ^ 2 + q + 1)), z.card ≤ i * (j * q + 1) → T ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin (q ^ 2 + q + 1) => (L l ∩ z).card + 1 ≤ q), min j (q - (L l ∩ z).card)) → (∀ z : Finset (Fin (q ^ 2 + q + 1)), z.card ≤ F * (j * q + 1) → T ≤ ∑ l ∈ Finset.univ.filter (fun l : Fin (q ^ 2 + q + 1) => (L l ∩ z).card + 1 ≤ q), (q - (L l ∩ z).card)) → T ≤ gates.length)) → (∀ (q s : ℕ), 2 ≤ q → ∀ G : ℕ → ℕ → ℕ → ℕ, (∀ b K : ℕ, G 0 b K = ((q ^ 2 + q + 1) - (if b = 0 then 0 else min (q ^ 2 + q + 1) (b * q + 1))) * min K q) → (∀ t b K : ℕ, G (t + 1) b K = (List.range (K + 1)).foldr (fun (j acc : ℕ) => max acc (min (G t (b + j) (K - j)) (G t b j))) 0) → q * (q * (q + 1 - 2 ^ s) / 2 ^ (s + 1)) ≤ G s 0 (q ^ 2 + q + 1)) → ∀ (q s : ℕ) (L : Fin (q ^ 2 + q + 1) → Finset (Fin (q ^ 2 + q + 1))), 2 ≤ q → (∀ i : Fin (q ^ 2 + q + 1), (L i).card = q + 1) → (∀ i j : Fin (q ^ 2 + q + 1), i ≠ j → (L i ∩ L j).card = 1) → (∀ p p' : Fin (q ^ 2 + q + 1), p ≠ p' → ∃ i : Fin (q ^ 2 + q + 1), p ∈ L i ∧ p' ∈ L i) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin (q ^ 2 + q + 1) → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∃ ι : Fin s → Fin gates.length, ∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ j : Fin s, ι j = i) → (∀ (w : Fin (q ^ 2 + q + 1)) (x : Fin (q ^ 2 + q + 1) → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ L w, x v = true)) → q * (q * (q + 1 - 2 ^ s) / 2 ^ (s + 1)) ≤ gates.length := by
  intro h1358 hval q s L hq hcard hinter hpts gates out hops hnot hout
  let G : ℕ → ℕ → ℕ → ℕ := fun t => Nat.rec (motive := fun _ => ℕ → ℕ → ℕ)
    (fun b K => ((q ^ 2 + q + 1) - (if b = 0 then 0 else min (q ^ 2 + q + 1) (b * q + 1))) * min K q)
    (fun _ (g : ℕ → ℕ → ℕ) (b K : ℕ) =>
      (List.range (K + 1)).foldr (fun (j acc : ℕ) => max acc (min (g (b + j) (K - j)) (g b j))) 0) t
  have h0 : ∀ b K : ℕ, G 0 b K = ((q ^ 2 + q + 1) - (if b = 0 then 0 else min (q ^ 2 + q + 1) (b * q + 1))) * min K q :=
    fun _ _ => rfl
  have hs : ∀ t b K : ℕ, G (t + 1) b K = (List.range (K + 1)).foldr (fun (j acc : ℕ) => max acc (min (G t (b + j) (K - j)) (G t b j))) 0 :=
    fun _ _ _ => rfl
  exact le_trans (hval q s hq G h0 hs)
    ((h1358 q s L hq hcard hinter hpts gates out hops hnot hout).1 G h0 hs)

end PEqualNP.MetaComplexity.LadderOrd
