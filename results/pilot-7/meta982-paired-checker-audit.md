# L-meta-982 coordinate reduction and paired-checker audit

## Source review

Reviewed root982_reduce_pairs.py, its GraphWires/base.Wires encoding and transitions, and the paired checker in Finite982Checker.lean. No indexing, polarity, or fresh-move completeness defect found.

Pairs are ordered (negative, positive), with negative-major enumeration. Encoding puts every selected negative row in the low K bits and its paired positive row in the high K bits. diff marks unequal outputs in either direction. covUp marks low=false/high=true, which is the required direction for the goal whose low half is0 and high half is1. Python masks both to low K bits. Lean's definitions may have additional high bits internally, but the final AND with lo K removes them.

For a parent with R gates left and l live wires, slack is R+1-l. After one gate, R-1 remain; equality len(child)=R is precisely zero slack, so the reducer's family switch is correct. A unary NOT dropping its input needs slack>=1; retaining needs>=2. A binary step keeping k operands needs k<=slack. Both AND and OR and every unordered distinct pair are enumerated. Identity, repeated-operand gates, constants, and outputs equal to live or original-input functions are excluded under the minimum-circuit normalization proved by Least.no_alias/Least.no_const/least_fresh in Lean. Input and live functions are distinguished by the complete truth table.

The star pair set contains all (0,p) and (n,all_ones), ensuring every truth assignment occurs because the nonempty graph function is false at0 and true atall_ones. It is invariant under every input permutation. Subsequent greedy additions are entire graph-automorphism orbits. The pair action source(row)[j]=row[perm[j]] is exactly the action induced by replacing input j with input perm[j].

The greedy reduction is heuristic advice generation. It does not assert that fewer pairs imply all full-table failures in general. Its exact replay scope is every admissible fresh move from the supplied maximum-budget frontiers. Smaller-budget coverage failure preservation is not implied automatically because a different remaining budget can change the diff/covUp choice. The final kernel certificate must check its actual roots and transitions, which makes such a heuristic limitation harmless.

## Lean paired checker review

encL_injective_of_cover requires every input assignment to occur among the encoded rows. encoded_run_rows uses this injectivity to preserve Fresh, so reducing pair coordinates does not silently merge distinct Boolean functions. initial_full requires explicit witnesses separating each essential original input; it is not assumed from the graph name.

Reduced.next calls the complete Live.next enumeration and filters only Fresh forbidden output parent. Live.next includes identity unary operations, but these fail Fresh. Binary operations are commutative, so a<=b suffices; next_two explicitly handles the reversed operand order and swaps retain flags. All slack restrictions are derived from run_len in next_one/next_two_sorted.

pairedBar checks real coverage and real score inequalities on every child. An advised child index is accepted only if it is in range and the actual oriented child list isPerm the stored state. The orientation function must separately preserve RNatRun. Thus incorrect tags, index advice, or coordinate symmetries cannot produce a proof by themselves. In particular, tag collisions can cause rejection of a valid certificate but cannot cause unsound acceptance. Sorting states by encoded numeric wire value avoids the known triangular-tag collision issue in generators.

pairedBar_all uses strong induction on the remaining gate count; every accepted child lies at a strictly smaller count. Score inequalities are enabled only at zero slack. The generic rejectDepth recursion uses the same sound coverage/score predicates and complete next enumeration; rejectDepth_no proves that a real run can never be rejected, by induction on the explicit recursion depth. No symmetry or hash equality is trusted in that recursion.

Independent numerical replay passed for both outputs, using a separately implemented evaluator with a different pair ordering. Seed0:735→151 coordinates, all64 assignments, all8 graph automorphisms,35521 fresh moves,32466 old coverage failures. Case28:2496→341 coordinates, all128 assignments, both graph automorphisms,2957273 fresh moves,2755009 old coverage failures. No reduced-pass/full-fail case or other pass/fail disagreement occurred. Exact pair actions and automorphism closure were checked. Complete results and source are merge-root982-reduced-pairs-audit.json and merge_root982_reduced_pairs_audit.py. This is not a claim that the final L-meta-982 theorem or all concrete certificates compile.

## Audited snapshot SHA256

- root982_reduce_pairs.py: 147b013c25d91eaa91ad92b38f25cd99aac659314da5fa4cd1453c82fdfa1275
- term_context_982_live_bfs.py: 59ab50ff0760fce0130e3d56a3af113e39ffada143fb7a3ec832ff0c74b94882
- term_context_live_bfs.py: 824cccbd6322bb0703a0d6fbec3c1f5e27502d424d4db322f3cf846cd8a72813
- Finite982Checker.lean: 55ed9da0d72f03145e3bedff19fceac61be4e84547b89ab71aca2f0b1b405a07
- Finite982DFS.lean: 079c07824903444a8137c9dcfcf7fdb22875f9a4d84d5e7583195dba1dfbe1d0
- term-context-982-score-case0-reduced-pairs.json: f477602422b7d5df0bccd57ecd1d26fc0cd0aabe6abcbdaea5ea7f437a4c0c6c
- root982-score-case28-reduced-pairs.json: 785affaf76dff606eb0a8d976cb582cd2a43ce00a9b9b9f8d716e8d29aaac89c

## Independent Lean axiom audit

A scratch copy of Finite982DFS.lean with four appended #print axioms commands compiled independently, exit0. The queried declarations pairedBar_all, encoded_run_rows, initial_full, and rejectDepth_no each depend only on propext, Classical.choice, and Quot.sound. Complete output is audit-finite982-dfs.log. No repository file was edited.
