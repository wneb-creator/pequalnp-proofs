import Mathlib
import PEqualNP.Defs

-- A cut of the star normal form step into the two things its proof does: reading a
-- star cover of the relation OFF a monotone circuit, and compiling a cover back INTO
-- a circuit whose AND gates are syntactically pure.
--
-- The common object is a biclique cover of the relation: finitely many pieces
-- A i x B i, each inside the relation, together covering it, with the cost
-- sum over i of (|A i| + |B i|).  A cover of cost c compiles to a circuit of size
-- c - 1 (an OR tree over A i, an OR tree over B i, one AND gate per piece, and
-- k - 1 OR gates to join the pieces), and that circuit is pure on the nose: the
-- AND gate of a piece reads the root of its right tree and the root of its left
-- tree, and a tree over one side is exactly a set closed under OR inputs whose
-- leaves are inputs of that side.  This is compileStarCover, and it needs no
-- hypothesis on the relation at all: it is the bookkeeping half, and the one that
-- can be finished.  The empty cover is the empty circuit with its output wire past
-- the last wire, which reads false.
--
-- starCoverOfCircuit is the half the four-cycle condition pays for.  Without it the
-- cost bound is false, because a two by two biclique inside the relation is one
-- piece of cost four covering four edges, while a star cover of those four edges
-- costs six.  With it every piece inside the relation is a star, so the cheapest
-- cover costs |E| + tau, the centres of the pieces being a vertex cover; the bound
-- sum <= C.size + 1 is then exactly the floor C.size >= |E| + tau - 1 that the
-- ladder quotes.  Exhaustive search over the AND/OR closure confirms the two sides
-- meet with no slack on the small four-cycle-free instances: one edge 1, two
-- disjoint edges 3, the three-edge path 4, the three-edge star 3, and the four-edge
-- double star 5 gates, each equal to |E| + tau - 1.
--
-- Neither half gives the step.  starCoverOfCircuit produces no circuit, only a
-- cover of the relation; compileStarCover produces a circuit but says nothing about
-- why a cheap cover exists, and applied to the cover of single edges alone it gives
-- a circuit of size 2|E| - 1, far above C.size.  Only the cost bound of the first
-- makes the second land inside C.size.
--
-- One warning for whoever takes the first half: the obvious reading, that every AND
-- gate below the edge function fires only on the edges of a star, is FALSE, so a
-- cover cannot be read off gate by gate.  On the three-edge path 0-0, 0-1, 1-1 the
-- six-gate AO2 circuit
--   4 = and l0 r0, 5 = and l1 r1, 6 = or 4 5, 7 = and 6 6, 8 = and l0 r1, 9 = or 7 8
-- computes the edge function, and gate 7 is an AND gate below the edge function
-- that fires at the single-edge assignments of both 0-0 and 1-1, which share no
-- vertex.  Its two operands are the same wire, an OR of two disjoint ANDs.

theorem PEqualNP.Outside.R_meta_5691_3
    (starCoverOfCircuit : ∀ (n m : ℕ) (R : Fin n → Fin m → Prop) [DecidableRel R] (C : PEqualNP.CircuitLowerBounds.Circuit), (∀ (a a' : Fin n) (b b' : Fin m), a ≠ a' → b ≠ b' → ¬(R a b ∧ R a b' ∧ R a' b ∧ R a' b')) → PEqualNP.TopForm.IsAO2 (n + m) C → (∀ (z : Fin (n + m) → Bool), PEqualNP.MetaComplexity.circuitFun (n + m) C z = Decidable.decide (∃ (a : Fin n) (b : Fin m), R a b ∧ z (Fin.castAdd m a) = Bool.true ∧ z (Fin.natAdd n b) = Bool.true)) → ∃ (k : ℕ) (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m)), (∀ (i : Fin k), (A i).Nonempty ∧ (B i).Nonempty) ∧ (∀ (i : Fin k), ∀ a ∈ A i, ∀ b ∈ B i, R a b) ∧ (∀ (a : Fin n) (b : Fin m), R a b → ∃ (i : Fin k), a ∈ A i ∧ b ∈ B i) ∧ (∑ i : Fin k, ((A i).card + (B i).card)) ≤ C.size + 1)
    (compileStarCover : ∀ (n m : ℕ) (R : Fin n → Fin m → Prop) [DecidableRel R] (s k : ℕ) (A : Fin k → Finset (Fin n)) (B : Fin k → Finset (Fin m)), (∀ (i : Fin k), (A i).Nonempty ∧ (B i).Nonempty) ∧ (∀ (i : Fin k), ∀ a ∈ A i, ∀ b ∈ B i, R a b) ∧ (∀ (a : Fin n) (b : Fin m), R a b → ∃ (i : Fin k), a ∈ A i ∧ b ∈ B i) → (∑ i : Fin k, ((A i).card + (B i).card)) ≤ s + 1 → ∃ (D : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (n + m) D ∧ (∀ (z : Fin (n + m) → Bool), PEqualNP.MetaComplexity.circuitFun (n + m) D z = Decidable.decide (∃ (a : Fin n) (b : Fin m), R a b ∧ z (Fin.castAdd m a) = Bool.true ∧ z (Fin.natAdd n b) = Bool.true)) ∧ D.size ≤ s ∧ ∀ x10 < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ) (x15 : Finset ℕ) (x16 : Finset ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt D x10).inputs = [x13, x14] ∧ x13 ∈ x16 ∧ x14 ∈ x15 ∧ (∀ x17 ∈ x15, x17 < n ∨ ∃ x19 < D.gates.length, x17 = n + m + x19 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D x19).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D x19).inputs, x20 ∈ x15) ∧ ∀ x17 ∈ x16, n ≤ x17 ∧ x17 < n + m ∨ ∃ x19 < D.gates.length, x17 = n + m + x19 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt D x19).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt D x19).inputs, x20 ∈ x16) :
    ∀ (x1 x2 : ℕ) (x3 : Fin x1 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (∀ (x6 x7 : Fin x1) (x8 x9 : Fin x2), x6 ≠ x7 → x8 ≠ x9 → ¬(x3 x6 x8 ∧ x3 x6 x9 ∧ x3 x7 x8 ∧ x3 x7 x9)) → PEqualNP.TopForm.IsAO2 (x1 + x2) x5 → (∀ (x8 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x5 x8 = Decidable.decide (∃ (x9 : Fin x1) (x10 : Fin x2), x3 x9 x10 ∧ x8 (Fin.castAdd x2 x9) = Bool.true ∧ x8 (Fin.natAdd x1 x10) = Bool.true)) → ∃ (x9 : PEqualNP.CircuitLowerBounds.Circuit), PEqualNP.TopForm.IsAO2 (x1 + x2) x9 ∧ (∀ (x10 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x9 x10 = Decidable.decide (∃ (x11 : Fin x1) (x12 : Fin x2), x3 x11 x12 ∧ x10 (Fin.castAdd x2 x11) = Bool.true ∧ x10 (Fin.natAdd x1 x12) = Bool.true)) ∧ x9.size ≤ x5.size ∧ ∀ x10 < x9.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ) (x15 : Finset ℕ) (x16 : Finset ℕ), (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x10).inputs = [x13, x14] ∧ x13 ∈ x16 ∧ x14 ∈ x15 ∧ (∀ x17 ∈ x15, x17 < x1 ∨ ∃ x19 < x9.gates.length, x17 = x1 + x2 + x19 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x19).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x19).inputs, x20 ∈ x15) ∧ ∀ x17 ∈ x16, x1 ≤ x17 ∧ x17 < x1 + x2 ∨ ∃ x19 < x9.gates.length, x17 = x1 + x2 + x19 ∧ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x19).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x20 ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt x9 x19).inputs, x20 ∈ x16 := by
  intro x1 x2 x3 x4 x5 hC4 hAO hfun
  obtain ⟨k, A, B, hA, hin, hcov, hcost⟩ :=
    starCoverOfCircuit x1 x2 x3 x5 hC4 hAO hfun
  obtain ⟨D, hDao, hDfun, hDsize, hDpure⟩ :=
    compileStarCover x1 x2 x3 x5.size k A B ⟨hA, hin, hcov⟩ hcost
  exact ⟨D, hDao, hDfun, hDsize, hDpure⟩
