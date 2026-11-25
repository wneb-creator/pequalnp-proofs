# L-meta-1342 shard0 constructive prefix cut

The candidate reduction is `ReductionDraft.lean` (SHA256 b6299a3d732aa35ada0b6701284dfbe8b40c385d7932c6decb361d56c09fa658). It compiles with Defs only; `reduction-draft-003.log` is empty and Lean returned0. It has exactly one theorem with two independent hypotheses and concludes the posted size21 statement verbatim.

Child1 constructs uniformly the three-gate prefix OR(a,b), OR(c,d), AND(11,12), giving Monotone2, size3, and all three computed wire values. `PrefixClosed.lean` closes this child without hypotheses; `prefix-closed-003.log` is empty, Lean returned0, SHA2560fd1737f48ac935055a8328ab824e2acdd9ed5b2214977a003458b036c11ad30.

Child2 asks for canonical ordered pairs a<b,c<d,(a,b)<lex(c,d) and an at-most18-gate continuation on the original11 inputs plus the three prefix values. It requires Monotone2 of the continuation, exact-binary backward validity (IsAO2) of the concatenation, exactly2 junk AND gates in that concatenation, and full-function correctness on every input. The concrete graph edge list appears only once inside this child. The composition proof appends the lists and adds3+18. No boundary-only semantics or new definitions are hidden in the child.

**Unresolved:** child2 is not proved. We do not claim every size21 solution can be normalized to this three-gate prefix. The reduction is a targeted constructive specialization, not an equivalence or complete first-junk normal form. No full proof of L1342 is claimed.

## Finite census

`enumerate_units.py` considered all1485 pairs of distinct two-element OR operand sets, modulo within-pair order and swapping the two ORs. An exhaustive check of all3456 permutations preserving vertex degree found only the identity graph automorphism. Thus no graph-symmetry quotient reduces these choices.

A plausibility sieve leaves912 units:768 with disjoint operand sets and at least one target edge accepted;144 with overlapping sets and a target edge joining the two nonshared vertices. Disjoint counts by number of target edges accepted are444 with1,264 with2,60 with3. In the overlap case the unit is r OR(a AND b); when ab is not an edge, replacing the unit by r decreases the function and preserves every positive edge input, so such a unit contributes no nontrivial positive-edge behavior. This informal sieve is not assumed by the frozen reduction and no completeness theorem for it is claimed.

The full census, representatives, accepted edges, and false pairs are in `unit-enumeration.json`; the summary is in `unit-enumeration.log`. No candidate unit was mistaken for a correct output function.

## Concrete plausibility witness

The certificate agent found `direct/unit-prefix22.json`; an independent reviewer checked all2048 assignments, exactbinary backward wiring, total size22, and junk-AND set exactly{2}. Canonical first gates are OR(0,8), OR(4,9), AND. The existing continuation has19 gates. Filtering with OR(8,9) turns the rectangle into the three edges(0,9),(4,8),(8,9); that OR is shared with the star at5. This confirms a real useful instance of the prefix architecture. The new child asks for one fewer continuation gate and a second junk AND; the nearby witness does not establish either improvement.

The full target identity for the rectangle filter is the four-variable Boolean law

    ((b OR a) AND (d OR c)) AND (a OR c)
      = (a AND c) OR (a AND d) OR (b AND c).

The associated size22 Lean witness is in `Unit22Checked.lean`. Its first complete full-function proof passed (`unit22-checked-001.log`); the follow-up canonical continuation version also passed, with empty `unit22-checked-002.log`, Lean exit0. It includes AO2, size22, and the explicit19-gate continuation plus its full correctness theorem. No≤18 continuation is claimed.

## Rejected false gadget

A three-clause CNF with triangle vertices of masks3,5,6 and leaves of masks1,2,4 does not in general compute only the claimed triangle and pendant edges. Selecting one leaf of each single-bit class satisfies all clauses. For the proposed triangle{5,8,9}, independent{0,1,2} is a concrete false positive. The certificate agent retracted this candidate and verified subsequent gadgets on full truth tables.

## Frozen generic variant

`GenericReductionDraft.lean` is the stronger reusable variant: SHA2567f28b599ed0ee057c145a0b734591e1d37049f2e9e84c435f36f5e8d5481a78b,44lines2493bytes, Lean exit0 with empty `generic-reduction-draft-001.log`. Child1 quantifies arbitrary n:Nat and a,b,c,d:Fin n, builds the prefix at wiresn,n+1, and records outputn+2. The reduction specializes this constructor at11. Child2 is unchanged. The generic quantifier also avoids a large finite Decidable screening computation over11^4 choices and2048 Boolean rows.

`GenericPrefixClosed.lean` closes this generic child with a uniform list-indexing argument using List.getElem_ofFn: SHA2561745ba54f13190974fa331a8ea13a1cc1b33eae8b6ebceb150b4e0a26c3413bf,23lines930bytes. Lean exit0, empty `generic-prefix-closed-001.log`.

## Stronger nearby two-junk witness

The certificate agent subsequently found `direct/two-junk22.json`. Its independent full truth-table audit reports size22,7AND gates, and exactly the two junk indices{2,7}. The same canonical first three gates are used, followed by a19-gate continuation. This matches the intended two-junk stratum at one gate above the target.

The canonical circuit, AO2 property, size22, full-function correctness, and the explicit19-gate continuation correctness are Lean-checked in `TwoJunk22Checked.lean`: SHA256addb4a199cd3e51e88e94948fa8e9083cc9c7043ace08d2d138eb9e8fa536251,85lines2970bytes, empty `twojunk22-checked-001.log`, Lean exit0. The precise junk set is externally audited, not a theorem in this file. No18-gate continuation is proved.

Besides the earlier rectangle-filter identity, the new proof uses the five-variable Boolean identity

    (a OR b) AND (c OR ((b OR d) AND (a OR e)))
      = ac OR bc OR ab OR ad OR be.

Both local identities are proved with tauto; the circuit proof then expands the11 finite input indices and uses propositional distributivity and associativity/commutativity. No native decision procedure or unverified solver output enters the Lean proof.

## Exact two-junk stratum is now Lean-checked

TwoJunk22Stratum.lean extends the independently audited two-junk22 witness. Lean compiles with exit 0; the complete stdout/stderr log is twojunk22-stratum-003.log (empty). It proves the exact dirty-AND gate set is {2,7}, hence its cardinality is 2. The two dirty gates have explicit rejecting-graph witnesses pairInput 0 4 and pairInput 9 10. Each remaining AND gate (4,10,12,14,17) feeds the final OR aggregate, so correctness of the output implies that gate cannot be dirty. This avoids exhaustive quantification over all input functions in the proof.

Together with the earlier declarations in the file, this gives a closed exact-two-junk AO2 circuit with 22 gates, the required graph function, the proposed canonical first prefix OR(0,8), OR(4,9), AND(11,12), and a 19-gate continuation. It is evidence for the architecture of the proposed child, but does not prove an 18-gate continuation, prefix completeness, or the posted 21-gate statement.
