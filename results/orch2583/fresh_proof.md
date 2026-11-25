# Fresh proof attempt, paused on lease loss

I reread CONTRIBUTING.md, README.md, the exact gap statement, and the definitions of ReadK and SharedBlockCost. I deliberately did not read the earlier attack notes before the reasoning below. The parent requested a pause before any proof or search result was obtained. Nothing below is a checked theorem, a counterexample, or a proposed replacement for the posted statement.

## Route examined

For the incidence function, every prime implicant is an incident point-line pair. A read-1 proof of such a pair has exactly one AND gate in its unfolded proof tree: the gate joining its two singleton leaves, with only OR gates above it. Thus the desired normalization can be viewed as routing every incident pair from some first mixing AND gate to the output through OR gates alone.

An AND gate may instead preserve a pair already witnessed by one input while its other input rereads one or both endpoints. This gate can filter unwanted larger minterms from the first input; removing it just because it repeats the pair is not sound. A general singleton/pair truncation does not preserve those larger-input filtering constraints.

The pure linear construction has no nontrivial sharing between the line ORs belonging to distinct points: two points have just one common line, so a shared OR of two distinct line inputs cannot feed both point stars. This explains the usual size N(q+2)-1, but it does not constrain arbitrary nonlinear shared wires.

## A concrete nonlinear phenomenon to keep in mind

Let L be a projective line and let A_L be the conjunction of all q+1 point inputs on L. Every line intersects L. Consequently

    A_L AND (OR of all line inputs)

implies the incidence function. Dually, selecting every line of a pencil together with any selected point also implies incidence. These high-degree implicants are absorbed by the quadratic output function, yet may legitimately occur inside shared nonlinear wires. An argument based only on positive pairs must account for this source of safe larger minterms.

The elementary identity

    (x OR y_1) AND ... AND (x OR y_k)
      = x OR (y_1 AND ... AND y_k)

shows how a repeated singleton can carry such a higher-degree term. I did not find a way to turn this into a smaller circuit: constructing this substitute for a free input costs extra gates, and careless substitution produces pure-point or pure-line false positives.

## Status

No Lean file was created or changed. No computation or external read was started. The current analysis neither proves nor refutes L-meta-2583. Work was stopped at the parent's instruction after lease renewal failed.
