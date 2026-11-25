# Read-only route and status audit for L-meta-1884

Updated 2026-11-25T15:39:53.971310+00:00

## Main result

The cleanest complete reduction is `R_meta_1884_773`: both normalization premises are already checked exactly in `L_meta_2594` (4830bytes) and `L_meta_2596` (23329bytes). The sole remaining premise is the posted free-negated-input lower bound L-meta-2598. No existing checked result found closes that premise. Helpers must be copied, not imported, under the target namespace.

## Three reductions

- R1884_773: arbitrary relabel/duplication is absorbed into wires at equal size (L2594); any extra unary function can be simulated using free¬xi at no larger size when output is not the extra input (L2596). The reduction itself handles the exceptional direct output. Only the free¬x0 case remains.
- R1884_412: finite pivotality under two prescribed other inputs is exactly checked L6081 (19047bytes). The other premise is a strong core statement: every≤18 circuit yielding a monotone automorphism-invariant function with that pivotality must fail one of three rows. This remains the main lower-bound problem, not a usable completed route.
- R1884_1: assumes ordinary Petersen18 exclusion; nine-variable cofactor15 exclusion; and two reader-pattern exclusions for free¬x0. The cofactor premise follows checked L4332. The ordinary18 floor is not already proved by our general17 nonNOT bound or monotone18 floor. Reader cases are negative input only, read by at most2 gates, and the exact18 case with unique positive OR / negative AND readers. These were precisely the remaining difficult patterns from earlier2592 research.

## L2598 reduction children

- R2598_314 (48668bytes) uses the nine-variable≤15 exclusion (covered by L4332) plus effective-read count1–2 exclusion (not found checked).
- R2598_639 (3892bytes) uses15+effectiveReaders≤size, exactly checked L5367, plus an at-most3-reader exclusion (not found checked).
- R2598_704 (4632bytes) uses a separator image-size/topology inequality, exactly checked L4083 (64917bytes), plus its residual implication to a lower bound (not found checked).

Related checked results: L7312 (12011bytes) forces another NOT when the positive x0 input is unread; L7314 (11519bytes) sends size<18, wrong output index, or a NOT reading the supplied negation to an ordinary Petersen18 circuit. They do not prove ordinary18 impossible. L5905 only excludes≤14 gates on the x0=false slice. L8241 supplies a restriction/deletion conversion but no stronger final floor. L3624/L4771/L4773 concern13gate nine-variable circuits with a supplied NOT and raw AND; L4301 handles a different nine-variable supplied-OR restricted split. None directly matches L2598.

## Upstream / PR evidence

Authorized read-only fetch changed FETCH_HEAD to `022f56c7386fa6f44efb05ed35bdd7d327bd122a` (Prove L-meta-11281,#15777), without merge/rebase.166 meta files were added since previous2af7128d. Final statements were extracted and retained in `/tmp/oec/pequalnp-pilot-103/1884-new-upstream-statements.json`. No new10-input Petersen/free-negated-input statement or stronger signed binary count was found. New related results are general8/9-variable floors14–16; no direct target closure. Full fetch stdout/stderr retained.

Fully paginated structured GraphQL census:955 open PRs,10pages, final hasNextPage=false. Zero exact1884 or2598 mentions in title/body/head branch. Complete responses and exact-path history saved under `/tmp/oec/pequalnp-pilot-103/1884-*`.

## Reuse and limits

Our checked Binary17 gives17+NOTcount≤size for ordinary Petersen. When the supplied unary input is¬x0, normalization does not charge that external inversion, so this does not by itself give19 binary gates or rule out18 total paid gates. Mono18 proves only18 for monotone circuits, and first-AND19 applies to a normalized first-AND trace. No claim that the posted1884 theorem is already proved is justified.

The full existing L4332 source is520393bytes and L5367 is523825bytes, both near the512KiB cap. Any integration requires pruning unused helpers; a raw concatenation with normalization files is too large.
