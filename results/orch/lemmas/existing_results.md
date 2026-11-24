# Existing-result search for L-meta-1768

- `R_meta_1768_1.lean` is a merged reduction of exactly our target. It separates exposed junk witnesses (both operands of the junk AND have a pair endpoint in their OR-reachable input side) from the complementary semantic residue. It asks for exposed count at most `27 * C.size` and a universal linear residual bound.
- Parent `R_meta_606_3.lean` combines normalization (child 1733), trace partition (1766), our single-junk-witness count (1768), and a double-distinct-junk-witness residue (1770). Proofs `L_meta_1733` and `L_meta_1766` are present, no proof 1770 found.
- `L_meta_1876.lean` proves `Ustar = empty` for a least top-form circuit with no junk.
- `L_meta_1878.lean` proves `Ustar.card <= 12*(C.size+1)` with exactly one junk gate. The 952-line proof can be copied and renamed into our namespace if a useful special-case certificate is desired. It uses only Mathlib and Defs. Its arbitrary-junk reusable components are top_w (lines 837-870), exposed-biclique reasoning (871-877 and 915-935), elementary OR reachability/evaluation (first ~570 lines), no4 (704-721), and input-read count rd_card (725-754).
- The crucial obstruction in 1878 is g_down (811-836): semantic truth at either operand of the unique junk gate traces to raw input because any lower AND would be a second junk. With multiple junk gates, this fails. Reusing the rest yields an exposed bound but leaves the genuine nested-junk residue.
- Searched 40 Outside files mentioning Ustar/wmax/gammaE and 68 files containing multiplication by 27. No merged proof of the general target or exposed count appeared. The only related project helper is LeafBound, about core cones, not directly usable without copying its dependencies.
- Defs root contains definitions only and does not transitively import Outside results. Thus there is no short exact-by-existing-name route under our import allowlist.

Potential reduction direction: select minimal satisfied junk gates below each witnessing top to isolate raw-exposed certificates, then separately bound the edges whose semantic path needs a nested junk gate or shared nonlinear subcircuit. Avoid repeating the existing exposed-vs-residual reduction verbatim.

## Essential support bound

Exact child of R_meta_1735_5 is already proved by merged L_meta_2074. Extracted its 222-line self-contained proof to support_bound.lean, renamed every helper namespace/theorem to PEqualNP.Outside.L_meta_1768_support. Imports are Mathlib and PEqualNP.Defs. Awaiting local compilation. Main lemma is stronger: exact fan-in-two gate lists computing the edge function suffice; monotonicity, reads-back, and minimality are unused. It proves a dependency set of cardinal at most gate-count plus output count by backward elimination, then shows every incident graph vertex must lie in that dependency set by comparing the pair input with a singleton input.
