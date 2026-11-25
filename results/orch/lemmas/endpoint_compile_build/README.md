All four final Lean builds exited0, with complete empty stdout/stderr preserved: constant_sweep_mono, constant_not_cut, endpoint_restrict, endpoint_lower0. All four independently reviewed PASS by structural_bound.

The strengthened sweep preserves the initial reference table literally, records one reference for every original gate, preserves monotone output gates and exact touched-gate savings. ConstantNotCut compiles a restricted monotone prefix, deletes NOT of a marked initial constant, then compiles the suffix with the original NOT-output index newly marked. Prefix reads of future NOT-output indices are never charged.

EndpointRestrict specializes raw0=false and suppliedAND01=false. The explicit embedding [false,x7,x5,x8,x6,x4,x2,x0,x3,x1] identifies the cofactor with the existing nine-variable Stronger.edge, checked in Lean. It yields a monotone nine-variable circuit with the exact savings formula and preserves malformed/default-false semantics.

EndpointLowerZero combines the separately checked consumer-distinctness theorem with an explicit suffix NOT consumer to charge two distinct gates, plus the deleted NOT. Given the explicit prerequisite not HasCircuitSize9 Stronger.edge15 (provided by the separately checked MonoBridge.actualNineLower16), an exact suppliedAND circuit with monotone prefix/suffix and NOT[0] requires at least19 gates. This component still assumes a suffix NOT consumer, uses identity input pins, and handles endpoint0; it does not silently claim endpoint1 or dead-NOT coverage.

The parent reported HTTP410 while this compile pipeline was active. The existing pipeline completed, all sources froze, and no further code/build work proceeded pending parent ownership recovery.
