# L-meta-14468 monotone constructive search

Inputs are wires0–7; gatei produces wire8+i. Operation0 is AND and
operation1 is OR. The target has the exact nine edges in `data.json`.
`baseline11.json` is independently checked on all256 assignments.

The nine positive edge assignments and seven maximal independent
negative assignments form an exact specification for monotone circuits.
`make_data.py` checks that every one of256 assignments lies above a
positive row or below a negative row as appropriate. This16-row shortcut
does not apply to arbitrary circuits containing NOT.

`search.cpp` supports fixed10-gate optimization and elastic14-slot
optimization preserving exact correctness while minimizing the live
output cone. Each reported witness is trimmed and checked on all256
assignments before printing. `validate.py` is a separate Python full
truth-table implementation for archived best states and witnesses.

The fixed diagnostic reached one missed extremal edge, with12 full-cube
false negatives and no false positives; it is not an exact result. The
elastic diagnostic retained the correct11-gate baseline. Complete
stdout/stderr are preserved. Two root-approved ten-minute searches are
recorded in `status.json`; root alone manages the lease and git.

Root stopped both searches after locating exact public proof PR18915.
The fixed run completed53,025,000 updates, best one missed extremal row;
the elastic run completed10,524,000 updates, best11live gates. Both
stopped gracefully with exit0 and passed independent final validation.
No10-gate witness was found. No search process remains active.

The public source's separate `mono` construction was parsed directly
and independently evaluated on all256 assignments. It has the same
four-AND/seven-OR cost and exact target as our baseline, with a different
gate order and final OR association. Its source hash and scope are in
`public-mono11-validation.json`; this validation does not claim to audit
the public binary-floor certificate or final Lean theorem.
