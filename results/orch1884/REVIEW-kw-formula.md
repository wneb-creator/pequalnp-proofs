# Independent review: monotone formula leaf bound

UTC: 2026-11-25T15:46:09.962382+00:00
Verdict: PASS for the finite certificate, signed-weight argument, positive-formula induction, and format. This is a formula-bound partial, not the circuit lower bound of L-meta-1884.

Source: `results/orch1884/lemmas/KWFormula.lean`
SHA256: `835dfeb7c4c7d691f03cc4e3c7bd9642d3bcf9cb4263c4a7f811229df6325da5`
Size: 6039 bytes, 141 lines.

Root reports Lean exit 0 for this exact source. Complete `/tmp/oec/pequalnp-pilot-103/1884-kw-formula-002.stdout` and `.stderr` are empty (SHA256 e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855).

The literal convention was checked in Defs/DeMorganFormula.lean: lit v true evaluates to x v, while false negates it. Consequently the recursively defined positive predicate excludes every negative literal and correctly means an AND/OR formula with positive input leaves. Leaves count occurrences, not distinct input names or gates.

The positive rows are exactly the fifteen Petersen edge indicators. The negative masks are exactly its fifteen maximal independent sets; I independently enumerated all 1024 masks to check both facts. I parsed the supplied 15-by-15 integer matrix, independently verified its total is 40, and checked all 80 coordinate/subset cap inequalities. The maximum cap is 2 at each of the ten vertices. Machine-readable independent results are in kw-independent-validation.json.

The weights have negative entries, so arbitrary rectangle enlargement would be invalid. The proof does not make that inference: for each chosen row subset it first replaces each allowed column sum by its nonnegative positive part, then enlarges the set of columns. Thus rectangle_bound is justified even for signed weights. Its allowed rows have input v true and its allowed columns have v false, precisely the positive-literal case.

At an AND node, all selected positive rows make both children true, and the negative columns are partitioned according to whether the first child is false. At an OR node, all negative columns make both children false, and the positive rows are partitioned according to whether the first child is true. These are disjoint partitions, so the signed rectangle sums add exactly; there is no subadditivity assumption on negative weights. Induction adds the two leaf counts and yields rectangle weight at most twice the number of leaves. Weight 40 on the full rectangle therefore implies at least twenty leaves.

The final theorem explicitly assumes positivity and separation of the thirty specified rows. The file does not provide a conversion of arbitrary shared circuits to formulas at a controlled leaf cost, and does not cover formulas using the free negative x0 rail or a paid NOT. Those remain separate obligations for any application to the posted gap.

Only import: PEqualNP.Defs. All declarations lie in PEqualNP.Outside.L_meta_1884.KW. No sorry, axiom, native_decide, forbidden namespace substring, string literal, attribute, or unsafe/meta declaration occurs. Options are scoped numeric maxRecDepth and maxHeartbeats limits. No credential material was observed. The reviewer did not author this helper or its weight certificate.
