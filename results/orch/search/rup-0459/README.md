# Independent replay of restricted disconnected-template UNSAT

The reviewed RUP-only checker replayed the complete backward dependency closure of the final empty clause in the previously archived disconnected-0434 certificate. It verified25,837 learned additions using36,618 original clauses, after validating temporal hint availability throughout the full binary LRAT and parsing all2,676,975 CNF clauses. The checked final empty clause is2939481. Replay passed in6.9seconds with211,296KiB peakRSS under a1GiB address-space cap and120second wall limit.

This is external Python verification of the restricted disconnected2+3 five-output template. It is not Lean-kernel verification and does not prove the unrestricted posted thirteen-output lower bound. Needed RAT records would be rejected; none occurred in the required closure.

The complete original CNF and LRAT are preserved in../disconnected-0434. Exact reviewed checker/monitor sources, complete logs/status and losslessly compressed trimmed LRAT and needed original clauses are preserved here. The original clause identifiers are retained in needed-original-clauses.txt; this file is a numbered subset for audit, not a renumbered standalone DIMACS formula. Ten checker fixtures are preserved in../0457.
