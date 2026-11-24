# Coverage certificate implementation diagnostic

The original termFamilyCovers API is logically sound. Its computational
implementation is impractical for the26-input candidate because elaboration of
`decide (forall A in F, exists B in G, B subset A)` selected an outer finite-type
universal quantifier over ALL finite sets of Fin26, rather than bounded iteration
through the supplied family F. This can enumerate2^26 candidate subsets.

This is confirmed by an actual elaborated-expression diagnostic, not inferred
solely from memory use:

- Source: InstanceProbe.lean, definition probeCoversInstance, followed by a
  run_cmd that logs the stored definition expression from Lean.getConstInfo.
- Successful run: `lake env lean InstanceProbe.lean`, exit0.
- Complete output: instance-probe-v2.stdout and instance-probe-v2.stderr.
- stdout lines140-143 select Fintype.decidableForallFintype at type Finset(Fin n).
- stdout lines544-546 supply Finset.fintype using Fin.fintype.
- The inner bounded existential selects Finset.decidableExistsAndFinsetCoe;
  the subset test selects Finset.instDecidableLE.

The initial main compile and both initial probes were interrupted by an execution
environment transition. They did not return a successful compilation or a known
exit code. Their complete empty logs and compile-v1.status.txt are preserved.
The original CoreBoundary.lean and TermFamilies.lean remain unchanged.

The separately versioned replacement files are CoreBoundaryBounded.lean and
../certificates/TermFamiliesBounded.lean. Their coverage function decides

    F subset (F.filter (fun A => (G.filter (fun B => B subset A)).Nonempty)).

This selects explicit finite-set operations. The new termFamilyCovers_eq_true
lemma proves equivalence with the original bounded-quantifier proposition by
unpacking subset membership and the two filter membership facts. Existing
coverage soundness then uses this proved equivalence. No circuit or certificate
data change is intended.

The restarted main compile uses documented Lean command-line resource controls
--memory=12000 --threads=1. There is only one active Lean compile. The resource
controls do not modify proof-file options or add any proof axioms.
