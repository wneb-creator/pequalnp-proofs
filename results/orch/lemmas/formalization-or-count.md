False-certificate OR-gate lower bound

false_or_count applies to any Strict binary monotone Dag, arbitrary base assignment, arbitrary output index, and finite input set I. Assume the output is false at base and, for each i in I, some assignment differing only at i makes it true. Then |I| is at most one plus the number of OR gates false at the base. No liveness, input-ordering, or output-validity assumption is needed.

Retain one fixed false operand of each false AND gate and both operands of each false OR gate. Every individually critical input has a retained path to the output. Reachable wires are covered by the output and sources of retained arcs. There is one mandatory arc per reachable gate and one additional arc per reachable OR gate. Inputs and gate wires are disjoint, so the finite counting inequality cancels the gate count and leaves |I|≤|OR|+1.

For the Fano cofactor setting every line input true and every point input false, all seven point inputs are individually critical. Hence at least six OR gates are false at that base. Such gates cannot be P-carrier gates or P-exit AND gates, allowing the p8 equality argument to identify the remaining six gates as OR gates. This application is separate from the generic theorem.

Complete source compiled exit 0; full logs and SHA256 receipt adjacent. The source uses accepted elementary Dag definitions plus new certificate lemmas and the independently reviewed finite counting lemma from status_review.
