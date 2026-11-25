# Read-only literature check

Read 2026-11-25 through the built-in web tool: Stasys Jukna, Disproving the Single Level Conjecture, author-hosted manuscript, https://web.vu.lt/mif/s.jukna/ftp/single1.pdf .

The abstract says that there are quadratic functions whose monotone circuits have linear size while single-level circuits require almost quadratic size. The construction in section 2 uses saturated extensions of Sylvester-type graphs. This confirms that generic quadratic normalization cannot be assumed; it does not refute the current triangle/four-cycle-free statement. Section 3 distinguishes pairwise graph representation from exact computation on all independent inputs.

Short source quote: “there may be many other boolean functions representing the same graph”.

No literature-derived numerical claim is used in any Lean proof. The paper does not supply the missing girth-specific total-gate argument. The site paper note-1 and Springer abstract pages could not be opened by the web tool, so their search snippets are not relied upon.

## Additional Boolean-sums lead

Read 2026-11-25: Ingo Wegener, The Complexity of Boolean Functions, chapter6 section6, printed pages165–166 (PDF pages175–176), https://web.vu.lt/mif/s.jukna/boolean/blaues_book.pdf . The ECCC landing page also identifies this monograph: https://eccc.weizmann.ac.il/static/books/The_Complexity_of_Boolean_Functions/ .

Corollary6.1 states that optimal monotone circuits for (1,1)-disjoint Boolean sums use only OR gates. Short quotation: “Optimal monotone circuits for (1,1)-disjoint Boolean sums”. Its preceding argument eliminates the last AND while tracking its output readers.

Possible connection, not proved here: neighborhoods of distinct vertices in a four-cycle-free graph intersect in at most one vertex, so their OR sums satisfy this disjointness condition. The assigned task computes a single quadratic edge function. No cost-preserving transformation from that circuit to the multi-output neighborhood-sum problem was established. This literature result is therefore not a proof of the gap and is not used in any Lean declaration.

The Mehlhorn PDF search result could not be opened (web403); its detailed contents were not relied upon.
