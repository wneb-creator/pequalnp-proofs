# Integration plan: sixteen binary gates

Status: plan only, not compiled. Wait for SignedFloor.lean to finish before starting any integration build.

The two checked-source APIs line up definitionally:

- `Restriction.petersen_restrict_binary C fan computes` gives D computing `Restriction.deletedEdge`, with `Restriction.CircuitProof.nonNotCount D.gates + 1 ≤ Restriction.CircuitProof.nonNotCount C.gates`.
- `SignedFloor.signed_binary_lower D fanD computesD` gives `15 ≤ D.gates.countP (fun g => !SignedFloor.isNot g)`.
- `SignedFloor.edge` and `Restriction.deletedEdge` have the identical twelve Boolean edge terms.
- `SignedFloor.isNot g` and `Restriction.CircuitProof.isNotGate g.op` are the identical match on `g.op`.

After combining both source bodies under their existing namespaces, append:

```lean
namespace PEqualNP.Outside.L_meta_2592

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma petersen_sixteen_binary (C : Circuit) (fan : FanInTwo C)
    (correct : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn x) = Restriction.fullEdge x) :
    16 ≤ Restriction.CircuitProof.nonNotCount C.gates := by
  obtain ⟨D, fanD, saved, correctD⟩ :=
    Restriction.petersen_restrict_binary C fan correct
  have lower := SignedFloor.signed_binary_lower D fanD (fun x => by
    simpa only [SignedFloor.edge, Restriction.deletedEdge] using correctD x)
  change 15 ≤ Restriction.CircuitProof.nonNotCount D.gates at lower
  omega

end PEqualNP.Outside.L_meta_2592
```

For `16 + NotBracket.notCount C ≤ C.size`, copy the small `nonNotCount_add_notCount` and `not_count_eq` lemmas from BinaryFloor.lean into `Restriction` (changing their helper references to `Restriction.CircuitProof`). They partition the gate list into NOT and non-NOT gates. Combine that equality with `petersen_sixteen_binary` using omega. There is no need to include the full 3249-line BinaryFloor proof merely for these two small count identities.

For the original budget `C.size ≤ 19`, this yields `NotBracket.notCount C ≤ 3`. The stated existence of a NOT gate gives positivity via membership in the filtered gate list. The remaining cases are exactly one, two, or three NOT gates; none of them is eliminated by this integration alone.
