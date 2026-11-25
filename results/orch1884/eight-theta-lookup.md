# Read-only eight-variable cofactor lookup

UTC: 2026-11-25T16:35:22.994269+00:00

The desired graph is Petersen minus old vertices0 and3, with remaining vertices1,2,4,5,6,7,8,9 and edges12,16,27,49,57,79,96,68,85. Its leaf is old4, adjacent to9. Deleting that leaf gives theta(2,3,3), with endpoints6 and7 and paths6-1-2-7,6-8-5-7,6-9-7.

A narrowed repository search for HasCircuitSize8 / Fin(8:Nat) yielded 169 final statements. No direct lower bound12 for this exact leaf-extended theta graph was found. The only simple eight-variable size12 statement was L_meta_516, whose graph is theta(3,3,3); its degree sequence differs and it is not a direct match. Candidate list and full extracted statements remain in scratch1884-eight-floor-files.txt and1884-eight-floor-statements.json (SHA256 `5c16fa2245d7aaf76cc25b418553e324edefa0fcfb1d22e06bb3573f197c6b63`). This is a scoped census, not a claim that no differently formulated theorem exists anywhere in the repository.

The delegated seven-variable search by lean_setup found L_meta_517 and L_meta_3128: arbitrary FanInTwo circuits for theta(2,3,3) require at least11 total gates. L_meta_2960 is stronger: at least11 nonNOT gates for an isomorphic theta graph, in a201746-byte source. An essential-leaf restriction/deletion bridge would therefore produce the requested eight-variable lower bound12. This lookup did not prove that bridge or change any target source.
