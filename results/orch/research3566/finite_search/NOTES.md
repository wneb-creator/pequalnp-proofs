# Gap3566 finite search notes

The statement reduces numerically to: some positive-degree vertex z has c(G-z)+deg(z)+delta <= c(G), where delta=1 exactly when vertex cover number drops. If c(H)=|E(H)|+tau(H)-1 for every nonempty induced vertex-deletion subgraph, every z leaving an edge works with equality. Empty star-center deletion is exceptional: c(empty)=0, but any star leaf works because at least two edges are assumed.

Semantic check: IsAO2 checks gate op AND/OR, exact arity2 and ReadsBack only. It does not bound the circuit output. Thus empty-gate circuit output=n is constantfalse and is legal. No constants loophole refutes the statement.

First small graphs beyond forests/C6+leaf arise at8vertices: theta with3 paths of length3,9edges,cover4,star-cover upper12. Larger theta and Heawood graph specifications are in family-census.json. All have verified no4cycles; cover minima and maximalindependentset counts were enumerated explicitly. Heawood14vertices21edges needs only58 Boolean assignment rows for exact monotone synthesis:21 minimaltrue rows and37 maximalfalse rows.

SAT encoder synth.py is independently reviewed by repo_review: onehotearlier-source selectors, ordered operands, guarded truth tables, last output, monotone extremalrow correctness, and source-order symmetry audited. Any SAT witness is exhaustively evaluated on all2^n assignments before being saved. UNSAT is only a diagnostic, not a Lean certificate. Solver runs use2GiB addresslimit and explicit180second walllimit initially. Full stdoutstderr logs are retained.

## Research read 2026-11-25

Primary source https://arxiv.org/pdf/1406.3065 , Jukna, Lower Bounds for Tropical Circuits and Dynamic Programs, Remark10 pp18–19: the text explicitly distinguishes single-output Boolean bilinear complexity from multilinear/arithmetic bounds and states that an analogous matrix-weight lower bound was not known there. This makes the requested general result substantive; no counterexample follows from this historical observation.

## Search results

C6 budget7: CaDiCaL UNSAT in1.83s (diagnostic). C6 budget8 plus a nested-AND path: UNSAT in18.25s. Theta333 budget11: UNKNOWN after180s. SubdividedK4 budget14: UNKNOWN after300s. Heawood26 local mutation:22.87million edits in90s, best1 violated extremalrow, no witness. Heawood26 Z3 neighborhoods:59UNKNOWNs in121.5s. CaDiCaL neighborhoods:43UNKNOWN and2UNSAT in90.4s.

Independent5x5 census (also independently run by proof_route): with a fixed perfectmatching, exactly260 C4-free12-edge graphs, two isomorphismclasses. Class0 is theta3x4, matching-labeled multiplicity20,17maximalindependentsets. Class1 has degree sequence3,3,2,2,2 on bothsides, multiplicity240,14maximalindependentsets; cyclebasis6,6,8. GraphJSON files balanced55m12_0/1.json.

Root candidate: subdivide each of three perfectmatching edges ofK3,3 into a path oflength3. Verified12vertices15edges,no4cycles, cover6 by completeenumeration,26maximalindependentsets. Its upperbound20 means a19gate witness suffices. Saved subk33matching.json.

Optional synthesis restrictions deep/andfinal/two_dirty/topform only narrow upper-witness search. Every witness still gets complete2^n evaluation. two_dirty selects twoANDs true on maximalnegativeinputs. topform enforces no cleanAND strictly below anotherAND, using exact negative-row semantics and inherited ancestorbits. UNSATs under restrictions are only diagnostics.

## C8 reusable-helper route

C8 input ordering is b,c,d,e,Z,W,T,U =0..7, edges bZ,bW,cT,cU,dZ,dT,eW,eU. If an11-gate circuit also provides h with b∨c <= h <= b∨c∨F, append OR(a,h), AND(X,...), and OR with F. The resulting10-vertex11-edge graph has cover5 (explicit perfectmatching), so14gates would contradict its expected15 bound. No C8 lowerbound11 is assumed.

GraphJSON c8_reuse_extension.json and witness-expander extend_c8.py are ready. The expander checks helper inequalities on all256 assignments and the extended function on all1024 assignments. A known12-gate circuit formed by prepending unused OR(b,c) to the standard11-gate C8 upper gives a sanity-checked15-gate extension, not a counterexample.

The relaxed helper encoding uses the maximal independent sets of the induced graph off b,c, not merely globally maximal sets avoiding them. It adds singletonb,c and the otherwise missed independent set{d,e}, for21rows total. Selected helper values are explicitly fixed true on allsampled rows with b or c and false on allsampled rows with B=F=0. Only4positiveedge values remain free, giving16 masks in7symmetryorbits (proof_route/c8-helper-orbits.json).

Literal-helper and broad relaxed-helper SAT probes each timed out300s. A second literal-helper query with restored maximum-operand ordering also timed out300s. These are UNKNOWN, not lowerbounds. The two-helper-prefix query was interrupted when root found the weaker one-helper construction. One accidentally unconstrained short probe is preserved under the suffix unconstrained-interrupted and carries no conclusion.

Current normalization options: irredundant makes gate operands incomparable onthe requiredrows; positivegates requires acceptance ofsome positiveedge; boundarygates additionally requires rejection ofsome negative sampledrow. Both constant-wire deletions preserve the relevant outputs and simplify away constants, so these conditions hold in a least classifier. Allfound witnesses are still checked exhaustively. Output-order/all-gates-used normalization is only applied to the F-output cone; a reusable helper outside it would already yield a smaller C8 circuit and is covered by the literal-helper padding route.

## Four simultaneous safe helpers

C8 has four disjoint safe OR pairs (0,1),(2,3),(4,7),(5,6). Treating them as free inputs and finding ten further gates would yield a26-gate counterexample after private-leaf amplification, on16 vertices20 edges andcover8. The amplification script exhaustively checks all65536 inputs. The known eleven-gate C8 upper gives only27 gates, saved as a positive control. The ten-unknown-gate SAT probe returned UNKNOWN at300seconds. Its no-leaf core is isomorphic to Heawood with two adjacent vertices deleted.

For a connected eleven-gate C8 circuit, total internal reuse surplus plus repeated input occurrences is four. With one safe OR present, its two original sources must also occur elsewhere, so at most two internal reuse units remain. With four helpers supplied freely and ten unknown gates, unknown reuse surplus plus occurrences of helper sources is at most three. Thus a nonformula candidate uses at most two helpers; the exactly-two-helper case has one shared unknown and no other repeated sources. Certificate_search is exploring this small repeated-wire structure independently.

## Final bounded C10 trials (2026-11-25 22:00 UTC)

The generalized free-pair encoder permits overlapping helpers when each pair is in one common bipartition class and has disjoint neighborhoods. C10 has ten such safe pairs. Supplying them freely and seeking13 further gates returned UNKNOWN after300.115seconds. The known14-gate upper passed all46392 clauses of its positive-control instance, including the recorded AND-count lower bound5. The general amplifier removes unused helpers, adds private centers/leaves, exports a matching and valid vertex cover, and checks every Boolean assignment. Reviewer independently approved the geometry, counting recurrence and amplification.

The broader C10 absorbed-helper query sought14 total base gates with B=x0∨x1≤h≤B∨F. Its32 sample rows include both required singleton assignments and8 induced maximal negative rows dominating all65 independent assignments with x0=x1=false. The query returned UNKNOWN after300.028seconds. A known15-gate base circuit with the helper explicitly prepended expands to18 gates, matching the expected bound; all4096 extended assignments pass. This is only a positive control.

The most recent full graph queries also returned UNKNOWN: bip5x6_14 at17 gates after300.023seconds, and bip5x7_15 at18 gates after300.021seconds. No circuit below the edge-plus-cover-minus-one threshold was found. No search timeout is a lower-bound proof. All solver output is retained in full. See PRESERVATION-MANIFEST.json for sizes and SHA-256 hashes and PRESERVATION-MANIFEST.md for the complete run list.
