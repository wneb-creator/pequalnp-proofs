# Petersen gate-count investigation

## Checked by exhaustive truth-table evaluation

A circuit computing the exact Petersen edge function uses **13 OR gates and7 AND gates, total20**. Its explicit gate list is `gatecount-twenty.json`. All1024 Boolean assignments were checked directly, with zero mismatches. Root/library_route is formalizing this witness in Lean; the Python check is not itself a Lean verdict.

This refutes the proposed separate lower bound OR>=14, even for a circuit of size20. It does not refute the held total-size lower bound.

The witness was found by a search over13-OR circuits with arbitrary free ANDs, checking the complete set of15 true edge assignments and15 maximal-independent-set false assignments. It reached0 critical errors after427801622 mutations in81.7011seconds. The initial canonical witness expanded to28 binary gates; absorption reduced it to21, and factoring two branches with a common H gave20.

## Shared P5 identity

Let a=x0,b=x4,c=x9,d=x7,e=x2 and borrow A=a OR e, C=e OR b, F=a OR d from three other stars. Then

R=(b OR d) AND ((A AND C AND F) OR c)

computes exactly ab OR bc OR cd OR de. Together with stars at vertices1,3,5 and the two-edge star centered6, this gives the full Petersen function. Sharing A,C,F saves one OR relative to the canonical20-gate star-cover circuit while requiring one additional AND.

## Local SAT tests

CaDiCaL returnedUNSAT for a4-new-gate circuit computing the P5 from its5raw inputs plus A,C,F. Positive control with5 new gates returnedSAT.

CaDiCaL also returnedUNSAT for5 arbitrary new gates after a fixed14-gate prefix containing the7 linear ORs and all four other star terms. This means that prefix cannot be completed to a19-gate full circuit. Positive control with6 new gates returnedSAT. These are computational SAT results, not Lean-checked lower bounds. CNFs, generator, models and logs are retained as `gatecount-local-*`.

## Dual count SAT

The unrestricted dual AndCount13 CNF has7113 variables and29856 clauses. A120-second run returnedUNKNOWN. The normalized model adds incomparable zero-set constraints and direct-variable cuts, giving7503 variables and31832 clauses; it was interrupted once the13-OR witness settled satisfiability. Both complete logs remain.

The normalization argument: if a paid AND gate has operand zero sets Z(A) subset Z(B) on every target-false critical row, replace it by B. This preserves false rows and only increases the circuit on target-true rows, so critical correctness survives. Thus a minimum-AND representation may be assumed to have incomparable operand zero sets. An operand containing OR of three direct inputs, or OR of a nonedge pair, is true on every false critical row and makes the paid gate removable.

## Ongoing

Searching12OR with arbitrary ANDs, and13OR with a flattened budget of6AND gates, from the new witness. No witness below20 claimed.

Updated 2026-11-25T15:22:09.806331+00:00

## Mandatory stop

2026-11-25T15:23:32.000630+00:00 Parent reported loss of Petersen lease. Both remaining stochastic searches were interrupted immediately (exit130), with no below20 witness.

gatecount-twelve-search.stdout: best 3 iter 0 seconds 2.1583e-05; best 2 iter 100003 seconds 0.0376038; best 1 iter 1000002 seconds 0.527183
gatecount-thirteen-six-search.stdout: best 0.16 errors 0 AND 8 iter 0 seconds 7.1358e-05; best 0.08 errors 0 AND 7 iter 100021 seconds 0.0452127

The explicit13-OR witness also satisfies every clause of both generated dual13-AND CNFs:0 violated clauses out of29856 and31832 respectively, validated by gatecount_validate_cnf_witness.py. This independently validates the SAT encoding against the known witness.
