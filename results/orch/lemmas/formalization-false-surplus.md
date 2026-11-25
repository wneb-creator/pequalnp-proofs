False-wire surplus count

The generic theorem false_surplus_bound assumes a StrictLive binary monotone Dag, a false output at an arbitrary base assignment, and a finite input set P whose inputs are all true at that base. Let F be the false-valued inner wires, U the gates leaving the P-singleton-support carrier, and B=sup_big the P-carrier merges having at least two output labels. Then surplusOn(D,F) + number of false primary inputs + |U| + |B| ≤ D.length + 1.

carrier_flow identifies false-wire surplus plus false inputs with false-carrier exit arcs plus internal merges. Each ordinary gate contributes at most one unit, except the final output can contribute two. A P-exit gate has an AND operator and a true carrier operand, so its flow contribution is zero except for the final-output allowance. A big P-carrier gate has two true operands and contributes zero. P-exit and big-carrier gates are disjoint, so their extra charges fit the same total budget. The last-gate indicator sums to one.

The complete179-line tail passed the cached build and independent source/math review, including all19 admissible Boolean gate cases. The flattened3979-line source with only PEqualNP.Defs imported also compiled successfully, exit0, empty stdout/stderr. Full logs and hash receipts are adjacent. The accepted prefix stops immediately after sup_big; the appended theorem is general and does not assume graph correctness, Bzero=0, or ordinary minimality.

Independent computational controls match equality: the quiet28 near-witness has1 false surplus +7 false inputs +7 exits +14 big merges =29; a correct quiet35 p14/Bzero0 circuit has9+7+12+8=36. These checks supplement the Lean proof.
