L-meta-9775 exact monotone circuit synthesis

The graph has14 variables and19 edges, with left neighborhoods as recorded in data.json. Its exact monotone boundary specification is the19 positive edge pairs plus36 maximal independent negative assignments. Every candidate returned by the SAT solver is independently evaluated on all16384 inputs.

prepare.py reconstructs the graph, extrema, known25-gate star circuit, an intentionally wrong circuit, and19 near24-gate seeds obtained by omitting one edge each. It validates the full truth table for the known circuit and every seed. The near seeds are not solutions: each has false negatives, recorded in data.json, and no false positives. Inputs use indices0..13, gate outputs14+i, op0 is AND and op1 is OR.

graph_cnf.py is the previously validated Fano exact encoder adapted to this graph. Its gate selector constraints enforce strict earlier operands and two binary AND/OR inputs. The output is the final gate. The current runs require every internal gate to be used and productive on at least one positive edge row; these are minimum-circuit normalizations for witness search. No ordering of the largest input index is enabled in the global run.

The encoder also tracks joint squarefree proof trees. A singleton proof propagates only through OR gates; a two-leaf edge proof propagates through OR, or is formed by AND of the two opposite singleton proofs. This is a joint multiplicity property, not independent per-variable minima and not a no-fanout/formula condition. In this strict binary constant-free model, it agrees with having a ReadK1 proof at that prime edge. The optional --require-non-read1 flag requires at least one target edge to lack such a proof.

The separate library theorem L_meta_2237 supplies a vertex coverT with |E|+|T|<=size+1 for a correct C4-free IsAO2 ReadK1 circuit. The graph's finite C4-free check and perfect matching of size7 are recorded in read1-premises.json; they give ReadK1 size at least25. A formal specialization is being prepared by another agent. This argument is separate from the formula26-leaf certificate; that formula bound alone would not justify the squarefree-proof restriction.

Completed validation: baseline25-valid is SAT and correct on all16384 rows; baseline25-invalid is UNSAT; baseline25-read1-reject is UNSAT when requiring deficiency. nonread1-baseline27 replaces the raw0 occurrence in the25-gate baseline by0 AND(0 OR1), adding two gates. It is correct on all16384 rows and the independent joint DP finds precisely edges{0,8} and{0,10} missing squarefree proofs. Its pinned deficiency encoding is SAT. The27-gate fixture only validates the encoding and is not a competitive witness.

Completed search: global24-120 ran120 seconds without the deficiency requirement and returned UNKNOWN. Full stdout/stderr, wrapper diagnostics, process ledger, source SHA256, CNF hash and exact sizes are retained. UNKNOWN does not establish a lower bound. Any subsequent case has its own separately named complete diagnostic files and process ledger.

Only reconstructible CNF hashes are stored here; large DIMACS files and the installed solver remain in scratch. No token or credential data is used by these programs.
