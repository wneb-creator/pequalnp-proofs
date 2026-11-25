# Nonempty star ownership does not imply global AND soundness

This is a finite computational example, not a Lean certificate or a refutation of L-meta-1031. The complete 32-input truth table and strict-ancestor ownership calculation are in `final-profile-not-sound.json`.

Use five inputs and the graph with edges 02, 03, and 04. Define

- `g = (x0 OR x1) AND (x2 OR x3)`;
- `h = (g OR x4) AND x0`, the output.

The explicit binary circuit has five gates. Absorption gives `h = x0 AND (x2 OR x3 OR x4)`, exactly the graph function. The first AND, at gate index 2 / wire 7, owns edges 02 and 03, a nonempty star with center 0. The last AND, at gate index 4 / wire 9, owns edge 04: the earlier AND is false on that pair. On pairs 02 and 03 the earlier AND is true, so those pairs are not owned by the last AND. Thus every AND owns a nonempty star under the posted strict-dependency definition.

Nevertheless, `g` is true at the independent pairs 12 and 13, so it does not globally imply the graph function. The two dirty pair masks are 6 and 10; the JSON also records all larger dirty assignments.

The circuit is **not minimum**. An OR chain on inputs 2, 3, 4 followed by AND with input 0 uses three gates. The four essential inputs 0, 2, 3, 4 require at least three fan-in-two gates; equivalently, the already-compiled star special case gives the same optimum. The JSON includes the three-gate witness and verifies it on all 32 assignments.

Consequently, the ownership condition cannot be replaced by global AND soundness without another argument using minimality. This example leaves the posted existential minimum-circuit theorem unresolved. It also supplies no lower bound for all circuits satisfying the ownership condition.
