# L-meta-2590: theoretical gate-elimination investigation

## Checked Lean component

`dirty-blocks.lean` compiled with pinned Lean 4.36.0 and PEqualNP.Defs using `lake env lean`; exit 0, empty complete output in `dirty-blocks.log`.

The helper names are in PEqualNP.Outside.L_meta_2590:
- `petersen` and `row`: target Boolean function and a bitmask input.
- `exceptional_supports`: if x0=false and F(x)=false, then F(x with w=true) is true for all three neighbors w=1,4,5 iff x is row772 or row200.
- `or_guard_exceptional`: for monotone h and arbitrary B satisfying B(x with x0 replaced by x0 OR h(x))=F(x), every independent x avoiding0 on which h=true is one of those two exceptional rows.
- `or_guard_below`: if h additionally ignores x0 and is false on both exceptional rows, h implies F everywhere.

The two exceptional independent triples are A={2,8,9}, B={3,6,7}. They are the bipartition classes of the induced six-cycle outside {0} union N(0). Thus a one-read OR-input case can be split into four patterns of h on A,B, with the all-false pattern giving an exact below-F helper.

The proof of the abstract implication uses only monotonicity of h, not B: if h(x)=true then h(x+w)=true; substitution correctness on x+w and x+w+0 identifies their B-inputs. The latter graph input accepts the edge0w, forcing F(x+w)=true. A finite 1024-input classification then identifies x.

## Gate-count dichotomy

For a live binary single-output circuit, let R count reads of original input wires and t count internal fanout beyond one per non-output gate. Counting gate-input edges gives s=R-1+t. A <=19-gate circuit on ten essential inputs either has a singly-read input, or has exactly19 gates, each input read twice, and no sharing (a20-leaf formula). The parent is formalizing this; another agent is applying existing L531 formula lower bound21.

The existing checked16-gate lower bound for the Petersen graph with one vertex removed implies that setting any vertexfalse may delete at most3 gates from a19-gate counterexample. In particular input fanout is at most3. The remaining structural case is a singly-read input.

## Limitations

These lemmas do not prove the full20-gate lower bound. Nonzero helper values on either exceptional triple remain possible. General mixed-block normalization is not assumed. Existing reduction R_meta_2590_491 already separates one-read AND/OR cases; the checked component strengthens the OR case to two exceptional independent supports.

## Checked OR-gate deletion lemma

The same file now also includes `edgeRow`, `positive_has_edge`, `edgeRow_true`, and `drop_or_guard`; compilation again exited0 with no output. If B is monotone, substitution through x0 OR h computesF, and h is false on all15edge rows, then B already computesF without the substitution. Thus a size-minimal actual circuit cannot have such a helper at a singly-read OR input: deleting that OR would save a gate.

## Symmetry

The vertex permutation [0,4,3,2,1,5,9,8,7,6] fixes0, preserves Petersen edges, and exchanges masks772 and200. A separate `symmetry.lean` checks involutivity, preservation ofF, and both row exchanges. This collapses exceptional-helper truthpatterns to neither, exactlyone, both. SAT search has been notified.

## Possible stronger normalization (not yet proved)

When helperh is belowF, an OR gate x0 OR h can be removed and h hoisted to a final OR, preserving size and function. If its old fanout is at least2 this removes a singly-read originalinput; if fanout1, the firstreader ofx0 moves one gate toward its firstAND. A lexicographic minimality argument may therefore arrange that every singly-readOR helper has some exceptional support. This is only a proposed normalization, not a checked lemma or an admissible restriction for the full theorem yet.
