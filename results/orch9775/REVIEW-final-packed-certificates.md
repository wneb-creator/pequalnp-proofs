# Independent review: final certificate selection

Verdict: PASS for the 21 selected certificate modules in
`search/compact-final/FINAL_SELECTION.json`, SHA-256
`c0b43c42747e3d3437c8a18b082dd2c941b7c43b151d16e76644579ac76c1f71`.
They total 194,981 source bytes. This is the final selection review;
the earlier 28-file/25-selected review remains a valid historical
checkpoint but does not define the final selection.

Every selected source and semantic JSON hash matches the selection
record and the independent audit. Every selected module has an exit-0
Lean check record at that exact source hash, reported successful olean
export, and two complete empty check logs. All 22 archived modules also
passed Lean; `P4293` is now compiled but superseded by the separately
reviewed direct argument and is excluded from the 21-file selection.

The new layout uses 64-entry clause table blocks and 96-row proof chunks.
I adapted the independent actual-text parser to read the block modulus
from each lookup leaf rather than assume the former size. It parsed and
evaluated every generated lookup tree, decoded every fact, scheme,
clause, row and final reason chain, and checked every proof-prefix
offset. All 22 decoded semantic cores are byte-identical to their
previously reviewed JSON cores; the layout change alters no clause or
reason order.

For the 21 final modules, the independent graph-scheme and dictionary-UP
replay checks 3,430 initial clauses and 1,977 learned clauses, then
verifies an assumption-free final conflict for each case. The ordinary
and budget theorem hypotheses, exact residual budget, initial-clause
bridge, `rows_sound` sequence and `book_end` linkage remain checked.
The final decoder is unchanged at SHA-256
`aa30d04d050bab40f52e50928599876d94042f1be3011754a785c34ec2bdf6a0`.

Exact per-module hashes and results are preserved in
`review-rup/compact-final-independent-validation.json` and
`review-rup/compact-final-selected-validation.json`, with complete
`compact-final-audit-checked.stdout` and `.stderr`. The independent
actual-text auditor is `review-rup/audit_final.py`, SHA-256
`71537a873f939ec7fb98b4714190ffea6e3b3efe8ec0c2f568e1ec86a5550470`.

This verdict incorporates the checker/semantic-bridge audit in
`REVIEW-rup-framework.md` and serialization audit in
`REVIEW-packed-certificates.md`. It certifies these conditional finite
exclusions, not complete case coverage by itself. The final assembled
theorem, coverage/automorphism wrappers, exact posted refutation, final
axiom audit and repository checker remain separate checks.
