# Petersen monotone lower-bound route

Checked artifact `lemmas/PetersenGraph.lean` identifies the exact posted Boolean expression with a SimpleGraph on Fin10, certifies its15edges, no4cycle, and minimum vertex-cover size6 (lower plus explicit6-cover). The decidable graph adjacency is passed by a plain abbreviation/local let, avoiding new instances. Kernel finite checks can take several minutes.

Checked artifact `lemmas/ReadOneLower.lean` specializes the existing L4897.General.main_aux to this graph. `Petersen.read_one_twenty` proves20≤C.size from IsAO2 10 C, exact target computation, and IsReadK 10 C1. `small_not_read_one` gives the useful negation at size≤19. This does not cover arbitrary Monotone2 unless an AO2 normalization preserving the relevant read property is supplied. For actual backward exactly-binary monotone SAT circuits the theorem applies directly.

Validation: PetersenGraph Lean exit0 in2590-petersen-graph5.*, ReadOneLower exit0 in2590-read-one-lower.*; stdout has style and inherited deprecation warnings, stderr empty.

Local certificate search for a stronger9-input cofactor with premade OR(x4,x6): L1908 gives unique later readers when total size≤15; L1910 and L3346/3348/3350 prove total size≥16. L3064/3066/3068 exclude a finalAND/OR/NOT after≤13additional gates. These establish15remaining gates when the premadeOR is free, one short of the proposed16remaining target. No stronger accepted descendant was found among83matching localfiles; full census/statements are2590-freeor-files.txt and2590-freeor-statements.json in scratch. Counterexample agent was informed of the new smaller SAT target.

Other useful source: L9781 excludes Monotone2 size≤16 for Petersen with adjacent outeredges(0,1),(1,2) removed, leaving13edges. Root was informed for possible edge-deletion accounting.
