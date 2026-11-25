# Structural strategy for L-meta-2592

2026-11-25 UTC. Inspected the root circuit model: fan-in-two means AND, OR, NOT only, each at most two operands. Invalid/future wire references read false. Empty AND/NOT is true; empty OR false; second NOT operand ignored. No semantic counterexample or loophole found.

Three existing checked reductions already cover this step:
- R_meta_2592_318: last-NOT factorization plus separator.
- R_meta_2592_408: normalization into legal inputs and last output plus bounded exclusion.
- R_meta_2592_271: Petersen requires 15 non-NOT gates, then exclude 1 through 4 NOT gates at size at most 19.
The desk says reductions_live=3, so a fourth reduction is not currently permitted.

L_meta_6194 is self-contained under Mathlib + PEqualNP.Defs. It proves at least 15 non-NOT gates via at least six branching wires. Its auxiliary petersen_binary_lower and nonNotCount_add_notCount establish the first premise of R_meta_2592_271. The file is 3255 lines / 144705 bytes. Existing L_meta_4725 proves the same floor.

The branch accounting identity is binary gates >= number of essential inputs - 1 + number of branching wires. Petersen gives 10 - 1 + 6 = 15. To reach 20 through a weighted form would require total excess outdegree at least 11. The available combinatorial first-branch grouping only proves six distinct branching wires; it does not by itself give that weighted excess. Logical AND/OR/NOT restrictions must supply the missing strength.

A monotone star-cover implementation uses 20 gates because Petersen has 15 edges and vertex-cover number 6. Its no-four-cycle property precludes reuse of an OR of two neighbors between different star centers. Extending that charge to arbitrary NOT intermediates is the unresolved structural issue, not a routine missing Lean lemma.

Restriction route: the best available deleted-Petersen binary floor is 14 (L_meta_7493), total floor 15 (L_meta_4550). To imply the target, need a five-gate elimination onto a 15-gate lower-bound minor, or a four-gate elimination plus a strengthened exact 16-gate minor bound. Neither follows merely from 10-input dependence.

Sound symmetry idea for SAT/search: for a minimal irredundant circuit, the first gate has five automorphism orbits: NOT x0; AND/OR on adjacent x0,x1; AND/OR on nonadjacent x0,x2. Petersen is vertex-transitive and transitive on adjacent and nonadjacent pairs. Normalization must separately handle constants, copies, future inputs, unused gates. Removing an unused NOT can yield a NOT-free circuit of at most 18 gates, so a search restricted to useful-NOT circuits must also exclude that monotone case.

## Updated restriction route

L_meta_670 is now checked: Petersen with one vertex removed requires at least16 total gates. Its signedRoot branch rules out at most14 binary gates even with free negations. Thus a four-gate zero restriction is sufficient for the original total20 bound. Earlier note about only total15 was stale.

A cleaned live candidate with s<=19 and at least one NOT has at most2s-1 operand slots. Its s-1 non-output internal wires are each used, so at mosts<=19 operand occurrences are inputs. All10 inputs are essential, so at least one input occurs exactly once.

For a positive AND reader of a read-once variable v, the partner must evaluate true on every independent set containing a neighbor of v. Petersen has three neighbors and no four-cycles. Therefore a nonconstant partner cannot be a literal or a single AND/OR/NOT gate: AND/OR of at most2 variables fails some neighbor singleton, and NOT of a variable fails some independent critical set. L_meta_6081 already proves the relevant finite essential-variable witnesses. If this partner has a private cone containing at least2 gates, settingv=false deletes those two, the AND reader, and a later reader, for the needed4. The unresolved case is shared gates in the partner cone, or OR/negative first readers; these require charging/normalization rather than the counting observation alone.

For the local-search near circuit, four shared ORs correspond to the four vertex-stars of K4, on its six edge variables. Their conjunction accepts all K4 edge covers: three perfect matchings plus four unwanted three-edge stars. A repair using only those four OR signals cannot distinguish good pairs from bad stars because all four signals are true on both. A monotone NOT argument that suppresses a bad star also suppresses its larger supersets, so an OR bypass must restore those supersets. This explains why a one-gate NOT patch is not immediate.

## Checked supporting file

At14:00UTC, results/orch/lemmas/Structural.lean first compiled with two finite critical-input witness lemmas. Extended file also compiles with only unused-simp warnings. It adds Critical v x (x_v=false, f(x)=false, f(x[v:=true])=true), and proves that no AND/OR of two other input variables, or NOT of one other variable, is true on every critical input. These are direct kernel proofs under only Mathlib.Data.Fin.Basic. Root notified to preserve according to push-early rule. This is supporting progress only; it does not prove the posted statement.

## Oracle factorization and signed partner classification

StructuralOracle.lean compiles. Its new lemmas formalize: if f(x)=H(x[v:=0],x_v AND h(x)) and h is independent of v, then h must be true on every Critical(v,x). Therefore no AND/OR of two other raw inputs or NOT of one raw input can be that partner. lemma_routes independently reviewed the extension as sound and plain-format compliant. Root owns the named delivery file; this standalone extension copies the small base for scratch compilation.

Stronger classification being checked in StructuralClassification.lean: for distinct v,a,b, critical inputs realize every pattern of(a,b) except11 when(a,b)is an actual edge. Thus any two-variable function true on all critical inputs is constanttrue or NAND of an actual edge. The finite witness construction has at most three true inputs.

A useful semantic normalization for the exception: if a NOT gate negates h with h<=f, replace that NOT everywhere bytrue and append OR h to the output. Whenh=false the computation is unchanged; whenh=true the target already equals true. Constant propagation removes the NOT gate. If it has an AND reader, that reader becomes a copy and is also removable, so this operation strictly saves a gate even if h or the NOT wire were shared. A circuit-level implementation would use the existing constant-propagation normalizer while keeping h available for the final OR.

Rejected avenue: charging an extra gate merely because two live roots become equal after restriction is unsound with free signed gates. A multiplexercounterexample computes(a AND c) OR(NOT b AND d) in three binary gates; identifyinga=b still gives a three-gate mux. Constant-root contraction remains sound; duplicate roots need monotonicity-specific reasoning.

## Actual circuit bridge

StructuralCircuit.lean compiled successfully. AgreeAway and runGates_agreeAway prove that gate lists not reading raw inputv preserve agreement at every other wire, including out-of-range default reads. sole_and_reader_factor then gives an explicit factorization of the real circuit pre++AND[v,w]::post, provided no gate in pre/post reads rawv and output!=v. The oracle is the actual suffix evaluated after the prefix withv setfalse plus the marked AND result. sole_and_reader_binary_impossible rules out such a Petersen circuit when the partner wire computes AND/OR of at mosttwo other raw inputs. The partner-function assumption remains explicit; no unjustified claim that all read-once partners are simple. lemma_routes independently reviewed these lemmas and the classification extension as sound.

StructuralNot.lean compiled successfully. sole_not_reader_impossible excludes the real circuit pre++NOT[v]::post when rawv has no other reader, output!=v, and every suffixgate is AND/OR. Earlier prefixgates may include NOT. Comparison on a critical input makes the marked NOT outputfall while the targetrises, contradicting suffixmonotonicity. This is a structuralcase of the original problem, not a full lowerbound.

StructuralRaw.lean adds analogous actual OR-reader factorization and excludes a sole AND or OR reader whose other operand is another rawinput. Compilation inprogress. This will force anyread-onceinput in a normalizedcorrectcircuit to enter a gatewhose otheroperand is an actualearliergatewire (unless its reader isNOT, addressed partiallyabove).

2026-11-25 14:16 UTC: StructuralRaw.lean compiles exit0. Sole AND or OR primary-input reader cannot have another distinct raw input as partner. This connects actual circuit prefixes/suffixes with earlier critical-input oracle obstructions. Independent review requested.

2026-11-25 14:19 UTC: StructuralPartner.lean compiled exit0. New real-circuit constraints force sole-AND partner true and sole-OR partner false on every critical Petersen assignment; excludes NOT(raw-input) as a partner in both cases. Prefix/suffix arbitrary gates, exact no-other-read and output-not-v hypotheses explicit. File frozen pending review.

2026-11-25 14:21 UTC: StructuralSplit.lean and StructuralReader.lean both compile exit0. Count1 now connects to an actual unique gate decomposition, and the strict real-circuit theorem single_reader_has_gate_partner proves that every primary leaf is either a NOT reader or binary reader with a gate-output partner (w>=10), including reversed operand order. All intermediate input/default-wire behavior is retained exactly. Files frozen and independent review requested.

2026-11-25 14:27 UTC: StructuralFunnel and StructuralSymmetry compile. Funnel excludes forgetting a raw input through any binary function with an absorbing partner value, including all four signed normalized operations. Symmetry gives explicit involutive automorphism taking9 to each v and full truth-function invariance, all kernel checked. StructuralEssential additionally proves every raw input has a reader in any correct circuit, discharging the input premise of counting. StructuralRun supplies generic Run.rows_agree and Run.separates requested by restriction_review; it uses a local FullExtension import for development ONLY, and its bodies must be concatenated into final proof. Every listed file frozen, independently reviewed or queued.

2026-11-25 14:31 UTC: StructuralNotLater compiled exit0; it packages sole-NOT-primary-reader implies another NOT later, under only FanInTwo/no-other-read/output-not-v/correctness. StructuralAdjacentOr.lean is UNVALIDATED: adapted L5236 from firstOR(0,2) to firstOR(0,1), changing signature and witness rows96/608 to128/640. Its redundant heavy build was intentionally terminated (exit143) to free CPU for root and restriction agent. Do not claim this file as checked. Generic Run projection route should cover the same case without another full certificate copy.

2026-11-25 14:38 UTC: StructuralBinaryLeaf.lean and StructuralBinaryPartner.lean compile exit0 and are frozen. Under explicit Strict/live<=19/hasNOT/computes hypotheses, at least one actual primary input has exactly one reader, that reader is AND/OR, and its partner is a genuine earlier gate output10<=w<10+prefix.length. Proof: root leaf-cardinality>=NOTcount, each NOT can read at most one leaf, last NOT cannot read any leaf by monotone-suffix contradiction, so some leaf must feed binary gate. Generic counting helpers also compiled standalone in StructuralLeafCounting. Independent review queued. Floor18 received independent mathematical source review PASS (conditional first nonOR binary18), pending its author's build.
