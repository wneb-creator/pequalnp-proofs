# Disjoint-component route: literature limits

Read 2026-11-25, 09:17–09:19 UTC. This is research context, not a Lean theorem or a current survey.

Wolfgang J. Paul, *Realizing Boolean functions on disjoint sets of variables*, Theoretical Computer Science 2 (1976), pp.383–396, Theorem5, pp.394–395, credits Fischer with exact additivity of monotone circuit size for the separate output vector (f(X),g(Y)) when X and Y are disjoint. The proof removes a first shared AND by false using minterm deletion, and uses the dual argument for a first shared OR. This does not immediately bound the single output f(X) OR g(Y): its dual clauses can span both variable sets.

Source actually read: https://web.vu.lt/mif/s.jukna/Knizka/Paul-disjoint76.pdf . Some proof text has poor OCR; no verbatim quotation is used here.

Peter Anthony Bloniarz, *The Complexity of Monotone Boolean Functions and an Algorithm for Finding Shortest Paths in a Graph*, MIT-LCS-TR238 (January1979), p.80 (PDF page79), explicitly distinguishes the known separate-output theorem from then-unresolved additivity for the OR of the outputs. It also records formula additivity, which does not supply the shared-circuit bound. Thus a disjoint-component reduction must prove its cost premise, rather than silently invoking Fischer.

Read mirror: https://bitsavers.trailing-edge.com/pdf/mit/lcs/tr/MIT-LCS-TR-0238.pdf . Original MIT copy: https://publications.csail.mit.edu/lcs/pubs/pdf/MIT-LCS-TR-238.pdf . The original copy opened but had no extracted text; the mirror supplied the readable page. Whether this single-output additivity question remains open in2026 is UNVERIFIED: these are historical sources, and no current resolution was located.
