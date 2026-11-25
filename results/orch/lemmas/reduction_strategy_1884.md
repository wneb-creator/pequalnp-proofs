# L-meta-1884 alternate lower-bound route

2026-11-25 UTC. The lease was withdrawn at17:03:59UTC and all research is stopped. No proof of the full posted statement was obtained.

## Existing reductions

- `R_meta_1884_773` separates relabeling, arbitrary unary-input normalization, and the canonical free `!x0` lower bound. The first two pieces are already checked elsewhere; the third is the hard core.
- `R_meta_1884_412` separates a finite pivotality fact from a circuit lower bound under monotonicity, automorphism invariance, and pinned pivotality. The latter still carries essentially the main difficulty.
- `R_meta_1884_1` assumes ordinary Petersen no-18, vertex-deleted Petersen no-15, and two exceptional free-literal reader patterns. Library route located the second assumption as the unconditional internal `graphLower` in checked `L_meta_8367.lean:6860`. Ordinary Petersen no-18 remains unproved.
- Current join instructions allow at most three live reductions per step. The assignment already reports three live reductions; no fourth was attempted.

## Monotone 19-gate lower-bound component

The root assigned reuse of the checked 2590 surplus framework for the weaker monotone lower bound 19. Under size at most 18, total surplus is at most 9. The all-eligible orbit is immediate; library route handles the smaller ineligible-set orbits. This agent handles the maximal independent orbit `I={2,4,5,6}`.

Identify the six eligible vertices `[3,7,1,0,9,8]` with the six edges `[01,02,03,12,13,23]` of a complete graph on four centers `[2,4,5,6]`. Each eligible vertex has two ineligible neighbors and an eligible matching neighbor.

For a pure-branch reservation, let `R` be the remaining surplus units and `P(x)` the units whose singleton support contains `x`. Earlier checked code-count lemmas imply every `P(x)` is nonempty. The budget gives `|R|≤3`.

Define `J(c)` as the union of the ineligible neighbors of all eligible `x` with `P(x)⊆P(c)`. The generic `ri_gen` domination lemma and Petersen's finite separation property force every assigned position for `J(c)` into the consuming-position set of `c`. A matching-edge witness provides one additional position outside all assigned positions. Therefore `|J(c)|≤|P(c)|+1`.

When equality holds and zero-support surplus is zero, consuming positions are exactly those assigned positions and the matching witness. The checked framework's `full_gen` then forces the assigned star supports at both endpoints of `c` to be exact. A profile inclusion crossing one of those exact centers yields a contradiction.

`profile_probe.py` exhaustively checked all `7^6=117649` nonempty profiles on three units. Exactly 9811 satisfy the endpoint-union inequalities; every one contains the saturated-center crossing described above. This is computational evidence until the finite Lean certificate and all adapters compile. The Python source and complete stdout/stderr are in `gap1884/reduction_strategy/`.

## Frozen checked artifact

- `gap1884/reduction_strategy/I4Bridge.lean`, SHA256 `4db243de440730fd7d5bf8eeb973a6e03855a311984b4d2ce5cff0539534583d`: checked and exported with exit 0, empty `I4Bridge-03.stdout` and `.stderr`. Its last theorem proves the actual circuit-to-profile budget described above. Imports the frozen scratch modules `PetersenGeometry` and `MatchingPrivate`; final submission would inline those allowed-definition proofs. Root and reviewer notified. Source frozen.

Additional frozen checked modules, each exported with exit 0 and empty stdout/stderr:

- `I4Full.lean`, SHA256 `a3a3e80c74608c22712725dbd4ade5e0a09603db9052d151c42c51cd547edc1f`: saturated budgets imply exact star supports; a crossing inclusion contradicts them.
- `I4Geometry.lean`, SHA256 `7d5739a66e01828ee9dd06a218be16d4cc5e68f9e8f6323b585a011584139929`: actual maximal-independent-set geometry and every eligible residual profile is nonempty.
- `I4Residual.lean`, SHA256 `ad92b4f21554ab661f019c61e420c806ad18a7ce36e6efe31ac183bb8ca9165e`: for an actual size-at-most-18 circuit in this orbit, exactly three residual units and zero empty-support surplus. Uses lower-bound agent's checked `ProfileThree`.
- `ProfileCertificateAnalytic.lean`, SHA256 `27372eb5a020bdc4c088b24599fda1ebc46221bb9e9b10e2d264f389d3c34a19`: the full finite profile contradiction, proved analytically from the root's argument. Under no crossing, duplicate profiles force saturation and a contradiction, hence profiles are injective. A singleton profile excludes its bit from all five others, although only three nonempty remaining profiles exist. Without singletons, six distinct profiles would fit into only four profiles of size at least two. Only tiny finite tables are evaluated.

The original monolithic/tuple/chunk enumeration experiments were stopped for excessive memory, not accepted as checked results. Their sources and complete logs remain for provenance. `I4FinishConditional.lean` was also not checked: its run hit the explicit 3500 MB memory cap. The final adapter's initial memory failures came from the encoding helper's unnecessary whole-Mathlib import, before import profiling completed. The fresh `ProfileEncodingDefs.lean` removes only that first import and checks with identical proof bodies, SHA256 `3875bc11697e571e640fd85b527aa6627f6296e0cbe05833620dda15bd88806d`.

## Complete checked I4 orbit

`I4FinishAnalytic.lean` is now frozen and checked/exported with exit 0 under `-j 1 -M 3500`; complete `I4FinishAnalytic-02.stdout` and `.stderr` are empty. SHA256 `30999971e08e527e8086b3d2ba10e5168facd5ff57aa991a30d59cf4de34a571`.

Its theorem `PEqualNP.Outside.L_meta_1884_aux.I4Finish.four_orbit_impossible` assumes exactly `StrictLive 10 D`, `Correct D`, `D.length ≤ 18`, and `ineligSet 10 D = {2,4,5,6}`, and proves `False`. No conditional finite-certificate premise remains. All dependencies listed above are checked; the scratch imports must be inlined for a public single-file submission. Root and independent reviewer notified immediately.

This closes one orbit in the monotone Petersen 19-gate lower-bound route. It is not the full monotone lower bound and not the posted L-meta-1884 statement with arbitrary gates and a free unary input.

## Withdrawal freeze

Root reported the desk STOP at 2026-11-25 17:03:59 UTC. All proof and search work stopped. The seven checked modules above are frozen with unchanged hashes and exported oleans; no compiler owned by this agent remained active.

Unverified drafts preserved separately: `ProfileCertificate.lean`, `ProfileCertificateTuple.lean`, and `ProfileCertificateChunks.lean` are superseded memory-heavy enumeration attempts; `I4Finish.lean` was an uncompiled adapter draft; `I4FinishConditional.lean` and `I4EndpointTable.lean` hit the memory cap while importing the whole Mathlib library. Only `I4FinishAnalytic.lean` with the Defs-only encoding import is the completed final adapter. Full attempt logs remain under the scratch directory.

The subsequent I={0} investigation did not produce a new theorem. The earlier C6 fixture refutes the shortcut from singleton support to literal semantics, even at zero empty-support and residual surplus. A possible temporal argument would classify the outside C6's shared meeting gate and track its paths through the three neighbor branches after setting the ineligible input to false; that classification and effective-path argument were not proved. No restriction/deletion or source-purity claim from this exploration should be treated as checked.
