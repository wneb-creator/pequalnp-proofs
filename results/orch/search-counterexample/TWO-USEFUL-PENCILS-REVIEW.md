# Two useful exact pencils at an OR budget of 38

Independent mathematical review by algebraic_witness, 2026-11-25. Approved as an argument for the standalone thirteen-line-input, thirteen-output cap-promise model. No new Lean build was performed for this review.

Let U be the paid OR gates whose actual Boolean functions are false on at least one four-cap assignment. This is stronger than asking only that a gate's singleton support be disjoint from a four-cap. All subsequent counting is restricted to U. Let e be the number of distinct pencils that occur as exact singleton supports of gates in U.

The output separation conditions imply that U is a separating guard family: for any pencil and any disjoint four-cap, descend through false AND gates from the output while retaining all four accepted singleton inputs. A false AND has a false child, and both children accept every singleton accepted by the parent. An input cannot accept four distinct singletons. Thus the descent reaches a false OR accepting the whole pencil. This gate belongs to U, and monotonicity makes its singleton support disjoint from the cap.

Apply the established private/shared guard charging argument to U. There are 13-e active targets without an exact useful support. The family G of useful guards containing an active pencil has cardinality at least 3(13-e).

Choose the earliest gate j in U whose singleton support contains any pencil P. Such a gate exists by separation. Let N be a four-cap where j is false. N is disjoint from P: a member of their intersection would be an accepted singleton below a false assignment, contradicting monotonicity.

Apply Routes.mcount to the circuit prefix ending at j, with positive samples the four raw singleton assignments in P and baseline N. Its one-coordinate perturbation premise holds for raw singletons; they need not extend the baseline. The prefix contains three distinct merging OR gates false on N. At most one of these is j, so at least two precede j. Each is in U because it is false on N. Neither contains any whole pencil, by the minimality of j. Call these two targetless gates B.

Choose one useful exact-support representative per exact pencil, giving e distinct gates R. Distinct pencils have distinct four-element supports, so the representatives are distinct. R is disjoint from G: an exact support of an inactive pencil cannot contain a distinct active four-element pencil. The two gates B are disjoint from both G and R because they contain no whole pencil at all. Therefore

    k >= |G| + |R| + |B| >= 3(13-e) + e + 2 = 41-2e.

In particular, k <= 38 implies e >= 2. This justifies requiring two distinct exact-pencil singleton supports, each witnessed by an OR gate false on some four-cap. The witnessing caps may differ.

Implementation cautions:

- Actual sample falsity defines U; support/cap disjointness alone is insufficient for the earliest-prefix argument.
- The earliest gate is earliest among all useful target-containing OR gates, not merely among exact-pencil gates.
- Use a genuine prefix or separately prove that the three counted merges occur no later than j. Applying a whole-circuit lower bound without this timing fact would leave the targetlessness argument incomplete.
- The argument uses the standalone model's common line inputs and common singleton supports. It does not directly give a cut for point restrictions of a global 26-input circuit.
