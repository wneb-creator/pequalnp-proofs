# Single-reader blocking and support-mask closure

`single_reader_chain_agreement` says that assignments differing only at one input and agreeing at the end of a single-reader chain agree at every wire with at least that endpoint index. The proof follows any changed reader path along the unique chain. `ineligible_consumption_insert_false` applies this to an ineligible input's consuming AND: when the other operand excludes the inserted base label, and the later wire also excludes that base label, insertion leaves the later wire false. The caller supplies the consuming-gate-before-wire bound explicitly. These are generic strict-DAG lemmas and do not assume Fano correctness.

The complete standalone chain source imports only Defs and has2648lines/122194bytes, SHA47c5191b3f41cf091d3e233243eab90b18e95172d59a053844cc3e35cd050374. Its process exited0 with empty full diagnostics; the source/tail and exact accepted prefix composition received independent review.

`support_mask_closed` is a separate generic induction: every actual singleton-support intersection with P lies in Closed if actual masks lie in Allowed, Closed contains empty and P-singleton masks, and Closed is closed under allowed unions/intersections. This supplies the sound connection from finite constructibility certificates to actual AND/OR DAG support masks. All family assumptions remain explicit.

The complete standalone mask-closure source imports only Defs and has894lines/39653bytes, SHAacb3ab00bcf6e6aaaef5ddc1e25f38d442b59aba80d90906aba46f7a1dce837e. Its process exited0 with empty full diagnostics; the final independent review binds its exact source and composition. Neither generic helper alone proves or refutes the posted gap.
