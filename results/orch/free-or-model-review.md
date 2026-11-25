Independent review: Fano six-AND / free-OR search

2026-11-25T15:05:49.572795+00:00

Status: mathematical model review complete; generator/decoder source review awaits the implementation. No additional solver process was started by this reviewer.

Completeness conditions

Enumerate AND gates of an actual AO2 circuit in their original order. Recursively replace every OR wire by the union of the raw inputs and earlier AND outputs reachable through its OR-only cone. Each AND then has two set-valued sides; repeated OR operands disappear by idempotency. Shared OR cones may be expanded without changing function. The final output has its own selected OR-set. It must not be forced to include every AND output, since intermediate AND gates may accept nonincidences and be filtered by later ANDs. Earlier-read constraints must remain on AND references. Repeated operands of an AND are legal; a disequality cut needs separate justification.

Defs/AndCountCircuit.lean formalizes exactly this free-OR model, with empty sides allowed and outputsets of raw inputs and AND gates. Exact incidence semantics excludes raw outputvariables, since a singleton cannot contain anedge. Allowing empty sides is a relaxation; such false wires must be eliminated before constructing no-constant AO2 gates. Padding with unused false AND gates lets a fixed six-gate search represent every circuit with at mostsix AND gates.

Checked optional normalization

L_meta_563.lean:273 proves every AndCountCircuit can be replaced by one with no more AND gates, the same function, every AND wire false on singleton inputs, disjoint rawvariable sets on its two sides, and WellFormed preserved. This justifies those cuts for the ANDcount relaxation. It does not establish preservation of total AO2 gates: reconstructing larger OR sides may cost additional gates.

Witness acceptance

A SAT model only shows a six-AND free-OR circuit. For each selected side, an independent ORchain costs max(sidecard−1,0) realbinary OR gates; identical/shared OR expressions may reduce this cost, but must be represented by actual earlier wires. A one-term side needs no gate. Empty false sides/gates may be removed semantically. Count every reconstructed AND and OR gate, verify both operands of each are earlier wires and exactlytwo operands, and exhaustively evaluate all16384 inputs against the Fano incidence function. A candidate with at most26 real AO2 gates refutes the READ1 replacement claim only after the separate READ1≥27 theorem and Lean checker validate the exact circuit. A SAT model with higher reconstructedcost is only a candidate, not a refutation. An UNSAT answer without a checkedcertificate is not a Lean lower-bound proof.

Source review completed 2026-11-25T15:07:46.473333+00:00

PASS as a complete six-AND/free-OR relaxation. gen-fano-andcap.py SHA-256563711860b6afcbf602379e740949ed1230efd3b65f7415504a1e81a09ea2c0d; decode-fano-andcap.py SHA-25627904fd43fe9b69e2f750ddf5cfecafd4db8b4e3059bcfb1a1138e3e65ab8da6. Generator uses Boolean selectors for arbitrary raw/earlierAND operands, exact Tseitin conjunctions for selectedgatevalue, exact OR equivalence for eachside including empty=false, exact AND output, and independently selected outputANDs. Omitting rawoutputvariables is valid because exactincidence rejects allsingletons.

Independently checked all16384rows:21minimaltrue assignments are exactlytheedges,37listedmaximalfalse assignments are maximalindependentsets, andeveryfalseassignment is contained inone. Thus exactAND/OR agreement onthe58boundaryrows implies fullfunction agreement bymonotonicity.

Decoder review: falseANDs propagate asNone; None summands disappear fromORs; one-termORs alias theirwire; eachadditionalORterm createsone countedbinarygate. Deadgate pruning and topologicalrenaming are correct. All surviving operands are checked against currentwirelength. Outputtruth is compared exhaustively across16384assignments. Joint cappedcount vectors correctly testREAD1 on eachprimeedge. Reconstructed ORchains maybe moreexpensive than optimizedsharing, but reportedcost is exactfor the constructed circuit.

Independent smokechecks in scratch/plane/review-andcap: sevenstar selector model (metadata k7 solelyforthistest) reconstructs27gates=7AND+20OR, exactfunction onall16384rows, allREAD1edges. Sixstars reconstruct23gates=6AND+17OR but232wrongrows andcorrectlyfalse refutationflag. NoSATsolver launched. Root discovered checkedL_meta_4187 alreadyimplies at least7ANDs, so a sixANDsolve is unnecessary; the source remains usefulfor a dualOR-caprelaxation.

Additional READ1cut source review: add-fano-read1.py correctly propagates existenceof exactjointvectors(1,0),(0,1),(1,1). For realAO2 circuits noemptyprooftree exists, so anAND cancreate(1,1) onlyfromopposite singletonvectors; ORtakesunions. ThebaseCNF paddingopcode2 represents constanttrue, although itsREAD1flags are setfalse. This is harmless onlybecause theexistingpadrd constraints forbid everypad read and exactincidence forbids selectingaconstanttruepad asoutput. Preserve thoseconstraints in anyvariant.
