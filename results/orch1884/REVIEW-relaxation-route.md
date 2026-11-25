# Independent red-team review of the25-row relaxation route

UTC: 2026-11-25T16:39:44.746791+00:00

Verdict: the semantic normalization route is valid as a conditional proof plan. A complete circuit lower-bound wrapper is not yet reviewed or claimed. The seven-variable theta11 bound, essential-leaf restriction, sole-reader extraction, and generic lift normalization have distinct formal obligations.

## Exact preservation by LiftFix

The existing `PEqualNP.MetaComplexity.LiftFix.main` in Helpers/LiftFixMain.lean201–204 (source SHA256 `2be3a039268c38e75222dbea8375de92a16fdc7f3eacb6720cdc77e260a9867f`) assumes Monotone2 and ReadsBack, plus PA/PB for an initial setT. T=empty discharges those set assumptions. It returns a monotone backward-reading circuit of no larger size computing exactly the same Boolean function, together with PA/PB/PC. It has no graph-function or complete-specification premise. Therefore all25 positive/negative row requirements survive unchanged, as do both exact cofactors and the value at277. The graph-specific Core.IsLiftFixedPoint machinery is unnecessary here.

PA says everyT gate is OR; PB says each such gate is the output or is read by anotherT gate; PC places every OR reading a satisfiable wire that implies the output intoT. Backward reads make each PB successor index strictly larger. Thus aT gate has a finite all-OR path to output. If a rawt sole reader is OR(t,A), with satisfiable A and A≤G, PC puts this reader inT. On singletont it is true, so the all-OR path makes G true, contradicting the retained negative-row constraints. This avoids an unproved custom iteration/termination argument.

## Obligations before that contradiction

1. The25 rows plus monotonicity give the two exact false cofactors by StrongRelaxRows. A13-gate candidate must accept277 if an available exact nine-variable lower bound is greater than13; rejection would make G exactly the graph function. The floor16 is sufficient but stronger than needed.
2. The eight-variable floor12 requires a formal essential-leaf restriction/deletion bridge to the checked seven-variable theta11 theorem, with the exact coordinate permutation. The same bridge must count every deleted rawt reader. At size≤13, two such readers would leave at most11 gates, contradiction.
3. The one remaining reader cannot be AND if it becomesfalse under t=false and has a downstream reader that is also removed. An actual liveness/output argument is needed: the AND cannot itself be the output because the positive specification has edges not containingt; an unread gate can be deleted in a minimal representative. This second deletion is a syntactic proof obligation, not a consequence of semantics alone.
4. For a sole OR(t,A), A is independent oft because it precedes that reader and there are no earlier rawt readers. The output must differ from rawt. A fold simulation then gives the exact factorization hypothesis required by partner_safe. Monotone2 gives monotonicity ofA. These facts should be derived for the normalized circuit, rather than presumed inherited from the original topology.
5. Unary/copy gates, duplicated operandsOR[t,t], empty gates, and invalid/forward references need explicit normalization or case handling. In particularOR[t,t] cannot be fed to partner_safe with A=t: independence fails. Its copy deletion handles it. If A is unsatisfiable, the OR is likewise a removable copy; PC requires satisfiability explicitly.
6. Once the preceding properties hold, partner_safe proves A≤target≤G using the exact cofactors, positive rows and accepted277. It uses no negative260 premise, so the route can prove14 for the loose25-row specification itself. PA/PB/PC then give the singleton contradiction above.

## Scope and delivery

This would exclude the auxiliary monotone25-row circuit at size≤13. Applying it to every L-meta-1884 candidate still requires the separate one-NOT structural branch and replacement/counting wrapper; the shared-filter premises are not automatic for arbitrary candidates. The existing helper imports are not permitted final imports under the job rules: needed proof declarations must be copied into the final Defs-only file, with the total source kept below512KiB. No current certificate-size estimate or completed exact-target claim is made here.
