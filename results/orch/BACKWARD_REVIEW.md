# Independent backward-normalization review

Verdict: PASS for partial checkpoint preservation, after the parent verifies compilation. No star-ownership or complete-gap result is claimed.

Reviewed all 345 lines of results/orch/lemmas/BackwardNormalize.lean. SHA256: 27d55004ff7669044079c1f5bcec95a66782f4d02ecad832fce2e12f41d6de2d.

The representation invariant processes each original gate while representing each current wire either by a constant or a valid new wire. Each original binary gate contributes at most one new binary gate; constants and unary gates may contribute none. New gate inputs reference existing wires, so the constructed circuit reads backward. Forward or out-of-range original references are represented as their actual false value at that evaluation stage.

normalize_graph proves exact equality to the graph function, size no greater than the original, and IsAO2. I checked the definition: IsAO2 means AND/OR only, ReadsBack, and every gate has exactly two inputs. It does not require the output wire to be in range. This matters for the constant-false branch, which correctly uses an empty gate list and output n. The all-false assignment rules out a constant-true graph function, including n=0 and edgeless graphs.

normalize_minimal uses IsMinimalMonoCircuit in its actual global sense: minimal among every Monotone2 circuit computing the same function. The constructed circuit is Monotone2; equality of functions lets the original minimality yield the opposite size inequality. Thus equal size follows, and minimality transfers to the new circuit. There are no omitted graph-girth, nonempty-edge, or positive-size assumptions.

The source has only the permitted Defs import, helpers in its own auxiliary namespace, and no forbidden text, axioms, unsupported decision procedures, string literals, options, or attributes. Parent reports component build exit 0. Complete backward-normalize-001.stdout contains only deprecated if_pos/if_neg warnings; backward-normalize-001.stderr is empty. This review did not rerun the build or the repository statement checker.
