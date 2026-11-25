# Independent audit: L-meta-2590

This is an audit and strategy note, not a proof or a checker verdict.

## Statement and model

The exact assigned statement forbids a Monotone2 circuit of at most 19 gates computing the explicit Petersen edge function on ten inputs. The title refers to the AND/OR/NOT parent step; this child statement allows AND and OR only. Monotone2 permits fan-in zero, one, or two and imposes no ReadsBack condition. Nullary AND is true, nullary OR is false, unary gates copy, and unavailable or forward operands evaluate to false. Every gate counts. The output can name any wire; an unavailable output is false. An UNSAT result for exactly binary backward circuits requires a sound normalization argument before it proves this statement.

## Reduction capacity

The received desk row has reductions=true and reductions_live=3. Upstream contains R_meta_2590_1, R_meta_2590_491, and R_meta_2590_932. The published cap is three live reductions per step, so another reduction is not an available fallback while that count remains three.

## Existing routes

R_meta_2590_1 splits on the first operation and provides the first gate as an extra input to an 18-gate tail. It uses the fifteen edge inputs and fifteen maximal independent-set inputs.

R_meta_2590_491 uses a compression hypothesis into a 16-to-18-gate AO2 circuit with a guarded input, then two finite guarded-row exclusions. The compression premise is a substantive additional obligation.

R_meta_2590_932 is the strongest available semantic normalization: choose a shortest trace of distinct Boolean functions generated from constants and inputs, delete pure nonedge conjunctions, then split into three cases using Petersen automorphisms and reordering. The cases start with edge OR x0||x1, nonedge OR x0||x2, or edge AND x0&&x1. All exclude pure nonedge conjunction gates; the second also excludes pure edge disjunction gates; the third excludes every pure input-pair disjunction. These restrictions may strengthen SAT search but must be imposed with their stated semantic meaning. Only PEqualNP.Defs is allowed, so useful outside proofs must be inlined in the one submission file.

## Independent finite checks

A Python enumeration of all 1024 subsets confirms fifteen edges, fifteen maximal independent sets (ten of size three and five of size four), vertex-cover number six, and at most one common neighbor for distinct vertices. The maximal independent-set masks are 50,69,104,116,138,201,208,276,385,402,521,548,554,770,773, matching the checked reduction. For monotone candidate circuits these thirty critical assignments determine the full function. This computation is exploratory evidence, not a Lean certificate.

The standard edge-plus-cover construction has 15+6-1=20 gates. The general vertex-plus-cover lower bound provides only 10+6-1=15 gates, leaving five gates unresolved. The graph has an outer five-cycle, so bipartite normalization lemmas do not apply.

## Delivery review

The final proof must have exactly the desk statement, named PEqualNP.Outside.L_meta_2590 at top level and last. Helpers must remain inside its own or _aux namespace. Final PR tree must add only lean/PEqualNP/Outside/L_meta_2590.lean; retained plane files and results belong only in preservation history, not the final PR diff. Check imports/plain/namespace guards, named lake build, and authoritative local checker before declaring completion.
