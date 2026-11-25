# Signed-circuit certificate extension

## Existing certificate

`L_meta_5236.lean` contains a signed live-wire search proving the 9-vertex Petersen deletion graph needs at least 15 binary gates with free complementation. Its root forest contains 761 states across remaining budgets 14 through 8 (1, 3, 30, 220, 424, 77, 6). Restriction bounds and exact truth-table row separation close children; graph automorphisms identify states.

Its final extended-input argument already proves a 16-binary-gate lower bound for the full Petersen graph even with an extra free input x0 OR x2. `BinarySixteen.lean` combines its unchanged certificate with `EmbedExtra.lean` to obtain the ordinary circuit lower bound 16 + notCount <= size, and excludes >=4 NOT gates at size <=19. Compilation completed with exit 0 at approximately 14:26 UTC; the lower bound and >=4 NOT exclusion are checked by Lean. Complete logs are `/tmp/oec/pequalnp-pilot-104/binary-sixteen.stdout` and `.stderr`.

## New computational route

Scratch scripts: `/tmp/oec/pequalnp-pilot-104/certificates/prefix_search.py` and `prefix_symmetric.py`; complete stdout/stderr adjacent. Each wire is a 1024-bit truth table. A live state retains or discards each operand independently after one of AND, OR, a AND NOT b, NOT a AND b. Pruning uses exact distinguishing-row coverage and the checked 15-gate lower bound after any one variable is set false. Restricted prefix supply costs are conservative upper bounds obtained by replaying the recorded prefix while identifying constants/equal/complement signals.

At total binary budget 17, root enumeration has 720 children; all survivors are the 45 OR pairs. By Petersen automorphisms these reduce to edge and nonedge OR representatives. In the edge branch, fixing its 8-element stabilizer leaves 15 states after gate 2 and 503 states after gate 3. The edge branch has 19,703 states after gate 4. The 180-second pilot stopped during gate 5 after 1,340 of 19,703 parent states; already 44,298 children remained. The nonedge branch has 29 states after gate 2. These deeper searches are incomplete. This is a computational exploration, not a checked new certificate.

The combinatorial agent is independently investigating stronger pruning from two or three variables set false and the existing checked lower bounds for smaller induced graphs.

## Rejected shortcut

A generic extra charge for duplicate restricted wires is false with free complements. The mux function (x AND y) OR (NOT x AND z) has a three-gate live run from roots [x,x,y,z], while its three-input signed complexity is three. Therefore a projected lower bound cannot simply add duplicate count to constant mass. Any such argument needs additional target-specific structure.

## Cofactor model bridge

`CofactorModelSuffix.lean` supplies the model using `Extended.assign (embed r)` and `inputs.map observe`. Input supply, the fixed-zero input, and target identity compiled separately against exact copied definitions. The model floor is a direct application of `nineFloor`; the final consumer instantiates the semantic agent's checked generic cofactor-floor theorem. The final integration applications also compiled in a combined harness with `nineFloor` supplied as an explicit hypothesis of its exact checked type; the real theorem was independently checked in `BinarySixteen.lean`. The full named-file build remains the final integration check.
