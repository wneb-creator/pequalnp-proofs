# Structural dirty-gate experiments for L-meta-4675

These witnesses do not refute the posted size lower bound. They test proposed normalization statements. Each displayed circuit was evaluated on every Boolean assignment, and its syntactic OR-reach colours were checked independently of the SAT model. No Lean certificate for these particular witnesses is claimed here.

## Model and scope

`hardcase-synth.py` forks the free-OR AND-count generator. It requires TopForm (a clean AND may not feed another AND through ORs), at least two dirty ANDs, every AND live and true on at least one graph-edge assignment, and distinct AND boundary vectors different from the raw inputs. It additionally forbids the first dirty AND from having any clean AND reader. This last condition is stronger than merely lacking the particular simple reader used in the current normalization theorem.

Optional constraints require proper nonabsorbing dirty AND operands, opposite raw colours at the first dirty AND, a nonstar accepted-edge footprint, and a nonstar set of output edges lost when that AND is forced false. The latter uses a separate forced evaluator in the SMT formula, and the decoded model validator recomputes it on full truth tables.

An OR budget bounds a direct binary realization with no OR sharing: sum of selected operand sizes minus one per operand, plus final output OR cost. Consequently an UNSAT result with this budget is only for this restricted representation; it does not rule out all binary circuits of that size. In particular, the restricted theta five-AND/ten-OR and C6 five-AND/six-OR UNSAT queries are not new size lower bounds.

## Two dirty gates, 15 total gates

For theta with points x0,...,x3 and lines y0,...,y3, use

E={(0,1),(1,1),(1,0),(0,2),(2,2),(2,0),(0,3),(3,3),(3,0)}.

Let

- g = x2 AND (y0 OR y1),
- h = (y0 OR y2) AND (y2 OR g),
- F = x1 AND (y0 OR y1) OR x3 AND (y0 OR y3) OR x0 AND (y1 OR y3 OR h) OR x2 AND h.

Sharing y0 OR y1 gives 15 binary gates, compared with the standard 12-gate circuit. Exactly g and h are dirty ANDs. The only AND reader of g is h, so g has no clean reader. TopForm and tCount=0 hold, and every gate is live. The identity h = y2 OR (x2 AND y0) makes the output calculation transparent. Forcing g false loses only edge (2,0), so this is not a nonstar-loss obstruction.

The inventory agent independently checked this formula, count, dirty classification, and colour condition on paper. Complete model and exhaustive 256-assignment validation are `hardcase-theta-proper6-or10-model.json` and `hardcase-theta-proper6-or10-validation.txt`.

## Three dirty gates, nonstar loss, 17 total gates

On the same theta graph, let

- g = (x0 OR x2) AND (y2 OR y3),
- h = (x0 OR x3) AND (x3 OR g),
- r = (y0 OR g) AND (y0 OR y2),
- F = (x0 OR x1) AND y1 OR h AND y3 OR (x1 OR x2 OR h) AND r.

This uses 17 binary gates. Exactly g,h,r are dirty ANDs. The only AND readers of g are h and r, both dirty. Every gate is live, every AND accepts an edge, TopForm holds, and tCount=0. All 256 assignments agree with the theta edge function.

Forcing g false leaves h=x3 and r=y0. The lost output edges are precisely {(0,2),(2,2),(0,3)}, a three-edge path with no single common endpoint. Thus TopForm and absence of any clean reader of the first dirty AND do not imply that its forced-false loss is a star. The circuit is five gates larger than the standard bound, so this does not show that a minimum circuit has this obstruction.

The toolchain agent independently checked this witness on paper: h=x3 OR x0 AND(y2 OR y3), r=y0 OR(x0 OR x2)AND y2, and absorption of higher-degree terms leaves exactly the nine theta edges. It also confirmed the precise three lost edges and that every path from g to a productive AND crosses dirty h or r first.

Files: `hardcase-theta-lostnonstar6-or11-model.json`, its `-validation.txt`, and the separate binary inspection JSON/text. The unrestricted free-OR model initially had 21 gates; a bounded neutral-rewrite search also reached 17 while preserving nonstar loss. No model closer than five extra gates was found for this stronger obstruction.

## Root's smaller matching obstruction

For E={(0,0),(1,1)}, the root supplied a nine-gate circuit implementing

(x0 OR x1) AND (y0 OR y1) AND (x0 OR y1) AND (y0 OR x1).

Two idempotent AND buffers on x0,x1 make the mixed clauses tCount=0. The first dirty AND is (x0 OR x1) AND (y0 OR y1). It is directly read by the final clean AND, but that reader has another dirty AND operand rather than a raw OR side. Forcing the first dirty AND false loses both disjoint matching edges. The circuit has TopForm, all gates are live, and every AND accepts an edge.

The independent binary inspector checked all 16 assignments and all stated structural properties. Files: `hardcase-matching-root-model.json`, `hardcase-matching-root-inspection.json`, and `hardcase-matching-root-validation.txt`. The optimum is three gates, so this is a structural obstruction only.

## Search outcome

The experiments show that nested dirty regions and nonstar forced loss are real even under TopForm and tCount=0. They do not obstruct size-preserving normalization of minimum circuits: every witness found has spare gates, and no optimal dirty witness or full lower-bound counterexample was found. A general proof still needs an argument charging or eliminating an entire dirty region, rather than a universal assertion that the first dirty gate has one simple productive reader or loses only a star.
