Fresh-code context-rebuild prototype for L-meta-670.

STATUS: Generic soundness theorem passed Lean kernel checking and independent
review. The computational search carries only current signal/RPN-code lists;
AutoContext programs and authenticated projected values are rebuilt at every
node. Arbitrary hints remain safe through FastRecipe validation and fallback.

PERFORMANCE EXPERIMENT FAILED: child11 of case159 returned true under Lean
#eval in465ms, but kernel checking exhausted the10000MB Lean memory cap.
The failed kernel run took66.70seconds wall; kernel profile reported22.3seconds.
The established engine checks the same child in6.21seconds kernel time.
A diagnostic enumeration found37 metadata nodes versus33 in the baseline;
this is a diagnostic count, not a universal equivalence theorem.

FreshCodeChild11.lean DOES NOT COMPILE: its finite decide+kernel lemma failed.
It must not be imported as a proved finite exclusion. FreshCodeSearchTest.lean
(the generic soundness wrapper) DOES compile. The native .olean is diagnostic
only and is not included. The first native log records an import-path error;
the native2 log is the successful corrected run. All complete outputs are kept.

Benchmark uses canonical ProjectedChildTest/Case159Common dependencies from
this job, with --profile -M10000, maxRecDepth100000,maxHeartbeats0. No full439-node
case was attempted with this prototype. No new axioms or native_decide were used.
