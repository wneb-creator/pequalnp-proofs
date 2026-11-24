# Auxiliary mixed complement routers

These are two independently verified, nonminimal auxiliary circuits with52 and54 gates. Neither is a counterexample to the posted39-gate statement, and neither is Lean checked. They show that two distinct nine-point complement certificates can first appear at the same AND gate even when every gate is nonconstant on the band; the54-gate version also satisfies the stronger true-on-some7/false-on-some8 condition.

The complete original generators, JSON circuits, generation logs, portable independent full-table checkers and their successful logs are preserved verbatim. The generators retain their original scratch output path; use the portable checkers to validate the archived JSON without writing to that path:

    python mixed-router-independent.py mixed-complement-router.json
    python mixed-router-endpoints-independent.py mixed-complement-router-endpoints.json

The independent checkers construct all8192 truth-table columns, then check all3003 band outputs, the gate witness conditions, all shared minterms, earliest certificate ownership and the two abnormal output indices. The54-gate router is band-equivalent to its earlier cross-term wire, making its nonminimality explicit. Any general lower-bound argument still needs minimum-count or routing-cost reasoning.

The separate pure-AND25 search, which ended UNKNOWN, and its160MB incomplete trace are not part of this auxiliary archive.
