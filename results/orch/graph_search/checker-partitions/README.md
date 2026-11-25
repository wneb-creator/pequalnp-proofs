# UNCHECKED research: finite-checker partitions

These sources and logs preserve research from pilot-180. They are not a complete
Lean proof of L-meta-10760 and must not be submitted as one. No final grouped
certificate build was completed before the lease error stopped work.

The Native*.lean programs are research-only optimized evaluators. They replace
Bool.rec/List.rec with lazy native control flow and compile with import Std.
Their successful Boolean evaluations are ordinary computations, not Lean kernel
proofs. The raw selector definitions are separate from these native rewrites.

Native results with Q35 = grpSix ++ tg0 ++ grp5:

- Original exactly-one-NOT, 13-gate search: all original 214 first-pair mask
  buckets returned false; complete log is native-split214-pair-001.stdout.txt.
  Its elapsed_ms values are cumulative, not individual bucket times.
- Eight first-NOT selectors all returned false. Individual native times were
  88, 101, 91, 93, 101, 89, 199, and 1 ms; the eighth is the complement selector.
- First-pair unique modulus 51 plus eight operation/retention state selectors:
  all 168 returned false, 54.315 seconds total, maximum 3.020 seconds.
- A second-transition state hash modulo 31: all 651 selected checks returned
  false, 60.178 seconds total, maximum 0.917 seconds.
- The same state hash modulo 127: all 2667 selected checks returned false,
  57.272 seconds total, maximum 0.510 seconds.

The second-transition hash is
  (r.foldl (fun h w => h * 17 + w.s) 0) % 127.
The raw DeepSelectorDefinitions.lean file retains the earlier modulo-31 helper;
NativeDeepSelectors127.lean and the final proposed grouped predicates use 127.

The proposed final mask families preserve the original MM=214 and its 16 active
first-pair residues. deep127-mm214-mask-groups.json sums timing estimates for
colliding first pairs, then groups the 127 second-state residues. Every family
covers all residues exactly once in every original first-pair bucket; this was
independently audited. Timings are estimates, and coverage is independent of
those estimates. All seven DeepMasks214Typed_*.lean files were independently
parsed and evaluated against that JSON; their literal encoding passed review.
The typed files use Nat.lor/Nat.shiftLeft and short hexadecimal words to avoid
large overloaded-arithmetic elaboration.

NativeDeepGrouped150.lean was NOT successfully compiled. Its single large
arithmetic mask declaration first exceeded the default heartbeat limit. A
second attempt with unlimited heartbeats was stopped after roughly 90 seconds
to avoid competing with the final proof assembly. Preserve its complete logs;
do not infer any successful grouped execution from that file. The typed mask
alternatives were prepared afterward and were not compiled here.

RecursiveSelectorDefinitions.lean is an unused, uncompiled fallback for cutting
more transitions. It is not required by the checked second-transition helpers.

Other agents kernel-checked generic selector recombination and independently
calibrated four individual certificates. Those checked modules and calibration
logs are preserved elsewhere under results/orch by the primary agent. Their
existence does not complete the remaining grouped certificate obligations.
