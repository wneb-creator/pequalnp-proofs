# Mixed-filter obstruction (mathematical, not Lean-checked)

This observation concerns the full bipartite incidence function. Both the assignment with every point true and every line false, and its opposite, are false inputs.

If H is an AND of two ORs of primary inputs, and both ORs contain a point and a line, then H is true on both of these false inputs. Every OR context containing H remains true on both. Consequently a clean AND consumer of that context needs its other operand to be false on both inputs. A nonzero OR of primaries cannot supply that operand.

The smallest overlapping cone H=(b OR c) AND (b OR d), for three distinct primaries, equals b OR (c AND d). If {c,d} is a nonedge, H has the same positive-edge profile as b and is at least b on every negative input; therefore primary b dominates H under the checked directed-dominance criterion. Independently of incidence, if the two input OR gates are exclusive to this cone, the identity replaces three gates by two. Neither observation covers arbitrary shared input cones.

A stronger conditional conclusion is available under all of these assumptions:

- The circuit is a least-size IsAO2 circuit for the exact nonzero bipartite graph function.
- It satisfies the jointly attainable clean normalization: no clean AND operand, no mixed clean/dirty OR, and at most one distinct reader for each clean internal gate.
- There are exactly two dirty AND gates, called H and K, and H is true on both pure-side false inputs.

Under these assumptions H has at most one first-AND consumer, where paths to a first-AND consumer traverse OR gates only.

To see this, every dirty OR cone contains only primaries and dirty AND outputs: clean inputs could neither enter a dirty OR nor feed an AND. If K depends syntactically on H, then K is true on at least one pure-side input. A clean reader of an H-context would require a partner false on both sides; an OR cone of primaries, H, and K cannot provide one. Therefore K is the only possible first-AND consumer of H.

If K does not depend syntactically on H, the partner false on both sides must be an OR of copies of K, and K must itself be false on both sides. Minimum size removes these copy gates, so every clean reader of an H-context has the form K AND Wi. The clean suffix is an OR tree: clean gates have at most one distinct reader, every live clean AND feeds only clean ORs, and minimum circuits have no duplicate-input OR gates. Reassociate this tree to group any two such leaves. Replacing (K AND Wi) OR (K AND Wj) by K AND (Wi OR Wj) replaces three gates by two. Wi and Wj are retained even if they have other readers. Retopological ordering incurs no gate cost. This contradicts minimum size.

The argument was independently reviewed mathematically. It is not a kernel-checked theorem and does not apply to nonminimal circuits or circuits with three or more dirty AND gates. It does not establish that every optimal circuit must have shared dirty AND gates, and no search constraint has been added from it.

The existing 78 paired-star 68-gate seeds already expose mixed singleton profiles: H=(p OR S) AND (q OR R), where R and S share a line c, accepts the singleton c and both pure-side inputs. Its independent partner K=(p OR q) AND (R OR S) is false on both sides, and H AND K computes the two stars. Component-library extraction can reuse these profiles without introducing another seed family.
