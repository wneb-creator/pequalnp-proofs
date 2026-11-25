# Independent review of P5Embedded

Reviewed the 213-line source with SHA-256 `ba296be312730f22279763ad8d5a56c2de06b17a3e250c284dc6daa0052a50b1`. Lean 4.36.0 checked an exact copy with five appended axiom queries in a single worker. The exit code was 0. The complete output is in `p5-embedded-independent.log`. It records four linter warnings in `input_relation`.

`arbitrary_prefix_exchange` holds for every Boolean prefix and every map of the five circuit inputs into available prefix wires. The map can repeat wires. `embedded_relation` tracks all local wires under the shift by the prefix length. The resulting equality preserves the three shared ports listed in the statement and the output. A downstream circuit can read these four values after updating its wire indices.

For the standalone graph path, the old circuit has two empty-owner gates and the replacement has only nonempty-star AND owners. The standalone replacement uses eight gates, two fewer than the old circuit. The arbitrary-prefix statement establishes equality of the listed values. Ownership under a prefix that computes some inputs with previous AND gates requires a separate ancestry argument.

Both embedding lemmas and both ownership facts use `propext`, `Classical.choice`, and `Quot.sound`. The size identity uses no axioms.
