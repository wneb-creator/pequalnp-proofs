Input-renaming strategy for L-meta-2732

Prepared source: /tmp/oec/pequalnp-pilot-70/formalization/rename/Rename.lean
Status: checked by `lake env lean` on first attempt, exit 0. Full log: /tmp/oec/pequalnp-pilot-70/formalization/rename/rename-build.log. Only deprecation and unnecessary-simpa warnings.

The renaming maps Nat wire indices below n through any function Fin n → Fin n and fixes every index at least n. Mapping all gate inputs and the output preserves evaluation after precomposing the first n input values; an arbitrary identical suffix is preserved. No well-formedness condition is required, including future/missing wire references, because the invariant holds at every Nat index.

Namespace: PEqualNP.Outside.L_meta_2732_aux.Rename.
Useful lemmas: eval, size, monotone, wire_input, wire_past, wire_lt, wire_injective.

Proof route: fold induction on gates, preserving equal wire-list lengths and all-index lookup correspondence after each append. The append lookup proof follows the checked pattern in L_meta_736.lean; the actual rename map here preserves input length and supports a suffix.
