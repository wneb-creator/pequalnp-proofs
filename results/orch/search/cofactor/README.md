Cofactor search aids for L-meta-2373

These programs generate search cuts, not a checked proof of the target. They use exact-Live projected bounds and lower bounds extracted from the checked source L_meta_670. Every chosen new target cut still needs a Lean certificate.

cofactor_prune.py: live-state restriction scoring. A cut requires lower + constant live roots > remaining binary gates + paid replay gates. Replayed prefix gates supply the restricted live pool; constants, aliases, and unused replay gates are removed. Optional direct input-pair synthesis seeds are constructive but gave no benchmark improvement.

extract_bounds.py: extracts checked nine-variable subgraph bounds and transports them through all120 Petersen automorphisms. Proper induced subgraphs on at most8vertices attain the star-cover upper bound; nine-vertex bounds are16 monotone and15 with free complementation. The JSON includes transport indices.

Observed benchmark: of1000 depth7 states surviving65 simple cofactor cuts,240 mixed/triple-variable cuts reject982;840 further restrictions reject12 of the remaining18; all17522 proper nonconstant restrictions, even with direct synthesis seeds, leave6. These6 are archived for a stronger terminal argument. This is not an exhaustive search of all circuits.

Validation: all restrictions tested on all21 exact-live states of the explicit20-gate witness in both modes produced no false rejection. All480 mode/restriction combinations for the240 supplementary profiles matched the exact target as a disjunction of forced literals and the residual graph. Constructive paid replays passed2000 random dependency/semantics checks. All1023 proper-subgraph lower bounds were compared with explicit minimum-vertex-cover star constructions.
