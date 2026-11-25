# Library route for L-meta-2592

## Accepted reusable results

- `L_meta_4725.lean`: every FanInTwo circuit for the full Petersen edge function satisfies `15 + NotBracket.notCount C ≤ C.size`. Equivalent non-NOT count floor in `L_meta_6194.lean` (3255 lines). Hence a <=19 candidate has at most four NOT gates.
- `L_meta_4033.lean`: unrestricted FanInTwo Petersen-minus-one-vertex lower bound >=16; 6579 lines, 515844 bytes. Source almost fills submission limit but can likely be compressed. This permits contradiction after any restriction eliminating four gates from a <=19 full Petersen candidate.
- `R_meta_4031_23.lean`: existing conditional three-gate-deletion route to full Petersen >=19. Normal form hypothesis remains the nontrivial half.
- `R_meta_2592_271.lean`: cuts exactly our step into binary floor (now accepted above) and bounded 1..4 NOT case.
- `R_meta_2592_318.lean`: last-NOT split and separator; separator remains hard.
- `R_meta_2592_408.lean`: legal normalization and normalized bound; normalized bound remains hard.

## One-NOT thoughts

For a nonconstant monotone prefix signal g, the sole NOT has value true at zero and false at one. Since the target is false at zero and true at one, a live occurrence must eventually encounter both AND and OR masking. An all-OR suffix forces g to be constant true or the NOT unused; an all-AND suffix forces g constant false or unused. This may enable pruning, but does not yet imply the required four-gate deletion.

No generic one-NOT monotone-circuit conversion theorem was found. No accepted full Petersen >=19 theorem was found by searching theorem statements for both numeral formats.
