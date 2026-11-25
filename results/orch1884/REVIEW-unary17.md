# Independent review: unary-input seventeen-gate floor

UTC: 2026-11-25T15:44:44.896708+00:00

Verdict: PASS for the dependency test, mathematical composition, generated-source integrity, and format review. The standalone assembly has not yet been compiled at this review timestamp. No completed proof of L-meta-1884 is claimed.

## Inputs

- `results/orch1884/lemmas/Unary17Check.lean`: 30893 bytes; SHA256 `eacc575f93615a0c2baafbc0f75b1eb6f52b23a0ce7f7e704b87b591040bc416`.
- `results/orch1884/lemmas/UnaryExtension.lean`: 5448 bytes; SHA256 `d4a0b12e0301bc6ed817328b6bc9f7f7b57ec1b785960a7af3a68810c0b16c68`.
- `results/orch1884/lemmas/Unary17Standalone.lean`: 299211 bytes; SHA256 `7bc454d09e9e4c0aced9f7036307b0056e6f0b7043e71d4d4e0e954780e458d5`.
- `results/orch1884/generate_unary.py`: 1388 bytes; SHA256 `780de0e8017432063474562e4df3ce6c12d93f067b1dd3ef047f2784e55e6eb2`.
- `results/orch1884/unary17-checked.stdout`: 3610 bytes; SHA256 `d26f90454d4015a386d60482a8f1a2d082e2b98d4c05793266a6550ffa1af560`.
- `results/orch1884/unary17-checked.stderr`: 0 bytes; SHA256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`.
- Dependency source `results/orch/lemmas/Binary17.lean`: SHA256 `824549cea61a489c8821209214cf8d631ef13ac9741611f3c21caf9135c72bcd`.
- Dependency object `results/orch/lemmas/Binary17.olean`: SHA256 `68483000dc93ad24671d0ab0575de4f9d1c8b28b3291d9acbc719acbcddcf158`.

## Checked scope

The author reports successful Lean session 79010, exit 0, at 2026-11-25 15:42:03 UTC. Complete archived stdout contains only unused-simp/unnecessary-simpa warnings; stderr is empty. This was a check of Unary17Check.lean importing the existing Binary17 object. Its sole import, `Binary17`, is a dependency-test import and is not permitted in the eventual proof submission. It is suitable for preservation as an explicitly identified helper test.

The generated standalone file has only `import PEqualNP.Defs`, is 299211 bytes (below 512 KiB), and preserves the entire previously reviewed Binary17 source after changing its namespace to PEqualNP.Outside.L_meta_1884.Unary17. Its new extension is inserted into Extended and maps the dependency-test UnaryModel names back to Extended. I checked both generated files against the generator output exactly, without modifying or rerunning the generator. The standalone version requires a fresh successful Lean build before being represented as checked.

## Mathematical review

The four possible unary functions on Bool are represented exactly by zero, one, pin 0, or its complement. The signature evaluation lemma proves this pointwise. Complement normalization with the signed mode enabled sends the unary signature to zero or the normalized pin 0. Every live root is proper, excluding zero; thus adding any free unary function of input 0 does not enlarge the normalized initial pin bank. Mapping, reordering, or duplicating the first ten inputs is handled by List.ofFn and requires no surjectivity or injectivity assumption.

The extraction uses the existing model for FanInTwo circuits, including its actual wire semantics and gate-count convention. A complete evaluation equality is supplied for every ten-bit assignment. The generated UnaryModel is an exact copy of the reviewed Extended model, and the live-to-Extended bridge follows constructor by constructor. The prior Geometry.binary_floor_seventeen then gives at least seventeen charged non-NOT gates. The paid NOT count is identified with the exact library notCount predicate, and the count partition is over every gate, including unused gates. Therefore 17 + notCount C <= C.size and the size-at-most-eighteen corollary notCount C <= 1 follow. The free unary input is correctly excluded from paid gate count.

This leaves zero- and one-paid-NOT circuits at size eighteen. It does not establish the posted counterexample conclusion, a contradiction at eighteen gates, or the local checker target.

## Format and safety

No sorry, axiom, native_decide, unsafe declaration, metaprogram declaration, forbidden namespace substring, or string literal occurs in the Lean sources reviewed. There are no attributes. Options are only scoped maxHeartbeats/maxRecDepth limits inherited from Binary17. All definitions are under the designated namespace; the complete target is not replaced by a different assertion. The Python generator only reads/writes the named source files and contains no credential handling or networking. No credential material was observed.

The reviewer did not author the unary extension. The reviewer previously contributed finite Geometry data to Binary17; that dependency was independently compiled and separately reviewed at its original preservation checkpoint.
