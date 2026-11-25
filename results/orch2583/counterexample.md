Counterexample strategy for L-meta-2583

The exact definitions have been checked. IsAO2 permits AND and OR only, requires exactly two earlier wires at every gate, and has no constants. IsReadK concerns proof-tree multiplicity on each prime implicant; it does not bound ordinary wire fanout. No malformed-hypothesis or definition loophole was found.

For q=2, use N=7 and cyclic incidence p-l mod7 in {0,1,3}. There are21 edges and an identity perfect matching. L_meta_7639 gives27 as a lower bound for any read-1 AO2 circuit; L_meta_7684 constructs a read-1 circuit with27 gates. Thus an AO2 circuit with at most26 gates is a sufficient refutation witness.

Independent enumeration agrees with circuit_search: there are37 maximal independent sets of the14-vertex incidence graph. Together with its21 edge assignments, these give58 truth rows that determine the function among monotone circuits. Any positive solver candidate is nevertheless checked on all16,384 assignments immediately.

The direct one-hot CNF encoder has passed a positive test with the standard27-gate star-cover circuit and a negative test with a deliberately broken26-gate circuit. It uses the bundled CaDiCaL and no network.

A systematic first-gate split is running sequentially,120 seconds per case. The336 incidence-graph automorphisms give three unordered pair orbits: same side (42 pairs, representative0,1), incident (21 pairs, representative0,7), and nonincident opposite sides (28 pairs, representative2,7). Each orbit is tested for AND and OR, giving six cases.

Search normalization: output is the last gate and every gate is used. A smaller AO2 witness can be trimmed to its output cone and padded at the output with identity gates to26 gates. Input order within each commutative gate is sorted. No restriction on the order of gates by source index is imposed in this split. Identity first gates can be removed and padding moved to the end. These normalization observations are mathematical reasoning, not a separate Lean-certified search-completeness theorem.

Exact source, input data, hashes, validation output, and each completed case's complete stdout/stderr are preserved in search/. An UNSAT solver result would remain a computational result, not the posted general theorem in Lean.

The parent approved a cheap necessary condition motivated by gate essentiality: require every gate to be true on some positive edge assignment. This adds one clause per gate and excludes first AND gates on nonedges. It is being used as a witness-search restriction, not as a formally established least-AO2 normalization theorem. The known 27-gate circuit passes the strengthened encoder; a first AND of two point inputs is immediately UNSAT.

The unfinished broad split was stopped and its full diagnostics archived. A focused four-case run now tests an incident first AND and all three first-OR pair orbits, with 120 seconds per case. The source, validation data, and each completed case are preserved separately with the productive-edge restriction recorded.
