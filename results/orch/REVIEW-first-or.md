First-OR checkpoint review

UTC: 2026-11-25T14:33:14.145826+00:00
Verdict: PASS for mathematics and source format. Root reports TestFirstOr.lean compiled with exit 0; reviewed stdout contains only an inherited deprecated if_pos warning and stderr is empty. The exact FirstOr snippet is present in that scratch file: True.

Reviewed source: results/orch/lemmas/FirstOr.lean
SHA256: 1cafe009e0b3a32c74ec1d7caef4898167b634f81026161ba1fb50a63656880d
Size: 1402 bytes; 31 lines.
Binary18 dependency SHA256: 3ae7fd370997c7f1df3be8ef2f34b1cf54b000d4e2e7fdef03ef4a7a6735760b

Mathematical review

The conclusion concerns a normalized signed Extended.Live derivation whose cost k is at most seventeen and whose starting signals are original pins. It does not assert that an arbitrary original circuit's first syntactic gate is OR. That scope is essential: the extracted derivation counts non-NOT operations and admits signed binary operations.

The zero-cost case contradicts binary_floor_seventeen. In the successor case, unfolding Extended.Live supplies exactly the first-forward-gate data, including legal operation d, distinct operands, freshness, and the suffix run. The raw-bank premise identifies each operand with an original pin; distinct signals imply distinct vertex indices. Operation legality gives d<4. The inherited raw condition is correctly restricted to U. If d is not OR (index1), first_non_or_floor gives at least eighteen total binary steps, contradicting k+1<=17. Replacing d by1 preserves every conclusion component, including freshness and the suffix Live bank. The proof contains no circular use of its own conclusion.

All hypotheses required by first_non_or_floor are supplied: distinct vertices, non-OR index, initial-only U, fresh computed signal, and the exact tail derivation. Cases0,2,3 are covered by the dependency, with3 handled there by operand swap. The witness m equals the predecessor of k, so k=m+1 is exact.

Format and preservation

The snippet has no imports, options, attributes, sorry, axiom, native_decide, _root_, quotes, code-running declarations, or credentials. It uses the existing PEqualNP.Outside.L_meta_2592.Binary17.Geometry namespace and closes it correctly. It is a plain UTF-8 regular non-executable file, below512KiB. It must be combined with its checked Binary17/Binary18 dependencies; it is not standalone and does not prove the posted gap. This review made no source edits.
