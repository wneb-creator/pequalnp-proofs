# L-meta-2583 independent audit

2026-11-25: active lease changed from L-meta-2592 to L-meta-2583. Old research is paused and preserved in checkpoint818074a5. Root alone handles desk and git delivery.

## Exact scope and model

The posted statement asks that every AND/OR exactly-two-backward-input circuit computing projective-plane incidence admits a no-larger READ-1 circuit. Definitions inspected: `Defs/ReadK.lean`, `Defs/TopForm.lean`, `Defs/ReadKJoin.lean`.

`IsAO2` excludes constants, NOT and forward reads. `IsReadK` uses joint proof-tree count vectors: a single tree must read BOTH inputs at most once. The scalar-per-variable variant is explicitly weaker and cannot establish this gap. Existing singleton/empty-output loopholes do not survive the exact computation premise. The geometry includes q>=2 and N=q^2+q+1; the uniform line sizes and unique line through each pair supply the usual projective plane properties. No immediate definitional counterexample found. No local file or git history exists for L_meta_2583.

## Existing sharp READ-1 characterization

`Outside/L_meta_7639.lean:1964` proves READ-1 size at least |E|+N-1 for rectangle-free bipartite graphs with a perfect matching. `Outside/L_meta_7684.lean:1123` constructs READ-1 circuits of size at most |E|+|vertex cover|-1. Applying all point-stars in a plane gives N(q+2)-1. Therefore a circuit below that size refutes the new statement. Fano threshold is27; q=3 threshold64. Existing2581/1942/2058 are only constant-factor bounds under extra READ3/READ2 premises.

The local note `notes/note-1-edge-function-exact-size.md` warns that single-level lower bounds do not automatically extend to general monotone circuits, citing Jukna. Restricted-domain web search found a project page claiming an explicit superlinear monotone edge-function bound was posed open, but opening that page failed; this external status is UNVERIFIED. No literature conclusion is being used as a proof.

## Fano concrete sanity check

For points0..6 and line l={l,l+1,l+3} mod7, exhaustive128 point subsets give37 maximal independent assignments: size pairs(0,7):1,(1,4):7,(2,2):21,(4,1):7,(7,0):1. Thus a monotone circuit is exactly validated by the21 incident pair true rows and these37 maximal-false rows. The empty and all-point/all-line rows are essential. This is mathematical finite verification, not a Lean certificate yet.

## Independent pre-push reviews

- StarConstruction2583.lean: APPROVED SHA256235ecb539b876155d053dcdfd308e55ac05a035d6276a1c8b1b3aea42c22e7c4, compiled by author. General constructor exactly copied checkedL7684 modulo namespace/name; new finite incidence count and upper bound are correct. Final normalization explicitly assumes the missing lower bound.
- PlaneStarExact2583.lean: APPROVED SHA256dd6e73b3f2a7b599d143eed3e8726f87f833001f9b596e5a4f741612f9d5ec1a, compiled by author. Exact star assembly, backward reads, joint READ1 vectors and cost N(q+2)-1 audited; copied core is an exact substring of checkedL2393. PositiveN is explicit. This664line version is preferable for final integration.
- OrLift2583.lean: static APPROVED SHA2565d8f2c04974fba8e0753ba7dc6b57f2dff01c6144991d12b38a8ad167a132f2b, compile pending at review. CheckedL1499 helper copies, explicit V2 lifting preserves size/function, V1 deletion saves onegate above an implicant. Least-circuit corollary correctly excludes an AND reader of a below-output wire. This is preprocessing, not full block normalization.
- FanoReadOneBound.lean: general prefix matches checkedL7639 exactly modulo namespace; new Fano data independently audited. First compile failed only at DecidableExistsUnique synthesis; author added explicit unfolding before kernel decision. Final review awaits updated bytes.

## Distinct finite search

One300second C++ annealing run targets26gates on all58 Fano boundary rows, seeded by deleting onegate from27star circuits. Mutations include input rewiring, AND/OR changes and topology-preserving adjacent swaps. Source and complete stdout/stderr are scratch/review-2583/fano_search.cpp and fano-search.stdout/stderr. No lower-bound conclusion follows from heuristic failure. Root requested no extension because a separate agent has a longer independent heuristic.

The bounded300second heuristic completed:2,087,202,493 evaluated mutations over23,191 restarts; bestone failing boundary row, no exact26gate circuit. Exit2 was the program's intentional no-witness status andstderr wasempty. This does not prove a lower bound. No extension.

Final reviewed FanoReadOneBound SHA25661570a7a4558d5248e4aee15295dfe37e8e94556a601e99a1c5e36a9bdd73229 compiledexit0 after expressing finite uniqueness with an explicit finite quantified proposition, then rebuilding ExistsUnique. APPROVED.

FanoCriticalRows.lean static APPROVED SHA25614066b6db28fbc6d1681f5f2c18166cb22529a5b12c72d8ce39221e943b4cffa. Parsed all data and independently checked21positive,37distinct maximalfalse rows plus128closurecoverage cases; exact correctness from monotonicity is sound. Compile pending at review.

OrLiftFixed2583.lean static APPROVED SHA256365c1d659ecaf514fb8b0feaaba9a1c446b44be79ed9e43165999346b3eb87fb. FrozenOrLift prefix copied exactly modulo namespace. Newly added transfer inequality shows survivingwire values decrease, so newlydirtyOR gates inject by rho into olddirtyOR exceptremovedgate; appendedtop isF andclean. Thus dirtyOR count strictlydecreases. Compile pending at review.

## Important source discovery: canonical Fano already settled

Independent audit confirmed `Outside/L_meta_7997.lean:9341` proves the unrestricted monotone fan-in-two Heawood lower bound27. Helper `fano27` at9406 translates it to exactly the cyclicFano relation p=l,l+1,l+3, and `ao27` at9428 requires only IsAO2 and exactcomputation. No READ1, distinct-operand or single-read hypotheses occur in these helper statements, and all sections containing variables close before their declarations. The narrower final posted theorem ignores its extra hypotheses. Therefore a canonical26gateFano counterexample cannot exist; all such searches should stop. My boundedrun had alreadyended.

Order3 hidden-bound audit found only conditional64bounds in selected candidates: L4101 requires Productive/allANDs belowF; L1500 requires lineDegree1; L8791 requires least+TopForm+junkempty; L5162/L2059/L5158/L4803/L4145 have specific nestedAND hypotheses. No unrestricted64bound was found.

Latest static approvals (compile status owned by authors/root):
- FanoCriticalRows after finite-enumeration optimization and routine elaboration fixes: SHA256b8beaa68ec15633bbc3cba1d5fa50a4dc9e3c4af7e743a64a11c028849229851. List.any/all visits listedrows only; BitVec7 spans128pointsets. Semantics unchanged.
- OrLiftFixed with explicit V2_gate argument: SHA256c6f9a8796832ba3038065e6b1e0db463a9dacb5299e846e84cb257daabc6a2e9.
- NormalForm2583: SHA25622b6e9980b0affef37f818519f83dacb1325614dfcaf6e1785e1dafd287e48be. Exact copiedfixedpoint base, Nat.find minimizes dirtyOR among leastcircuits, no inputwire is an implicant of graphfunction, and final wrapper first minimizes gates. Correctly yields a no-larger least lift-fixed-point circuit; does NOT assert READ1.
- SingerThreeReadOneBound: SHA2567913fd344ac017ac85499eae7dc928534d5ac04bd67584454ece02f4377707f6. Prefix equals approvedFano generalbound modulo namespace; independent finite geometry check52edges,degree4,unique commonline for156ordered distinctpointpairs. READ1lower64 follows matching theorem. No unrestrictedlowerbound claim.

## Independent Singer13 boundary and orbit audit

Enumerating8192point subsets for cyclicdifferenceD={0,1,3,9} gives52 positivepair masks and704 distinct maximalfalse masks,756total. Negative side-size census:(0,13):1,(1,9):13,(2,6):78,(3,3):52,(3,4):234,(4,3):234,(6,2):78,(9,1):13,(13,0):1. Every falsemask is independent and becomes true after any absentbit is added. Own data: scratch/review-2583/singer13/boundary.json.

Exact rowset comparison with not_elimination/singer-rows.txt passed; SHA25698570a57319ad1499fd7d1f7a706cb29a9d5dbbd3cfd3c8eed64ebec0075fe4c.

Independent orbit rerun enumerated108 distinct projective collineations fixingpoint0/line0, checked each permutation against all169 incidencepairs, and recomputed21 dualorbits. Their union exactly matches all704 independentnegative rows; orbitJSON SHA25698af93f0a342ed1910eccfaa37c8d16506f1c9b6b9836604a2817c32f1422757. Polarity swaps0 and13, preserving their unorderededge. The21representatives are valid CEGARseeds only; a finalwitness still needs all704false rows checked.

CleanReaders2583 static APPROVED SHA256112fff4818e489cc5c9ea604b06378334c12a2878d8b9b6c13f6c405a14f1ac1. Base exactly frozenOrLift modulo namespace; readerhelperblock exact substring ofL1499. New wrappers prove cleanwire readeruniqueness and readers.card<=1 under IsLeastAO. No arbitrarycircuit claim.

IncidenceCriticalRows.lean independently APPROVED compiled SHA2568cc4f28ad5823dbd5a8d372d2b49f8c5b2582777aafe521c71b80129c5d38a7f. Generic arbitrary-bipartite incidence correctness from all positivepairs and negativeclosures, optional listednegativecover, is sound even with empty sides. No lowerbound claim.

Singleton2583.lean static APPROVED SHA256a8835671d1ddd450029bae6dc37f4b91a32519ef68090a087b12683ca4a7f8a5. Replacing a singletonpositiveprofile gate by its primaryedgeAND preserves all positiveprofiles, decreases all wirefunctions and retains exact graphfunction. Main proof uses monotonicity both to establish atom<=oldwire and to transfer pairtruth to arbitrarytrueassignments. Compile pending at review.

Parent's simultaneous-normalization argument independently validated: among least-size circuits minimize dirtyORcount, then among those minimize noncanonical-singletonprofile gates. Atomicreplacement preserves every positiveprofile and everyothergate's syntax, turns chosenop toAND and decreases allwirefunctions, so dirtyORcount cannotincrease. Any strictdrop contradicts firstminimum; otherwise noncanonicalcountstrictlydrops. ORlift contradicts thefirstminimum regardless of changes to positiveprofiles. Uniqueedge must use unordered or canonicalpoint/line orientation. This supplies a route to a proof ofconjunction rather than merely combining separatelysound normalizations.

Exact comparison of circuit_search's plane3-data.json passed; SHA256e46876bc469fd9743e0b2c98ab65af85390c0bbd021295792a8acbd6bebf02f2. All756rows,704negative and52edges match independentdata. Its64gatecontrol was independentlyevaluated onall756rows with validAND/OR/backwardinputs andoutput89. Current97row query is correctlytreated asCEGARrelaxation.

## Second lease410 preservation review

Root reported L-meta-2583 lease410 at15:07:16 despite a15:02renewal returning15:22expiry. All newresearch paused; no reviewersearch/build process remains. Staticchecks below approve preservation of drafts, NOT successfulcompilation or gapcompletion:

- Singleton2583 SHA256a8835671d1ddd450029bae6dc37f4b91a32519ef68090a087b12683ca4a7f8a5,673lines: unchanged previouslyreviewed replacementtheorem.
- NormalSingleton2583 SHA2563f24d396004e98594387c60ed283ebf59c975f5dce809a86abf2e31254e3c758,1064lines: NormalForm andSingleton blocks match exactcopies; minimum totaldirty-gate count yields simultaneous OrNormal andSingletonClean. Does not claimdirectatomic syntax.
- StrongNormal2583 SHA256b485e408c2d74ebc08a92da2e7b19dd9b9136ffed1a4eb06e9df979229466e2b,1073lines: lex dirtyOR thennoncanonicalSingleton argument is mathematicallysound. AtomicFor accepts bothoperandorders, and atom_not_bad usesdistinctendpoints to establishuniqueunorderededge. This is the directatomic-syntax normalization draft.
- PackedCircuit2583 SHA2562bdc88274464f219d2f33078cdf0cbcc66d2e1d3a414161f90bafa36f0fab349,217lines: packedAND/OR evaluation projects correctly perbit; logdoubling pointpatterns andlinecomplement patterns representallpointselected closures. Finaltheorem explicitly assumespackedEval=0; lastcompile failedonlya rowfunctionrewrite atline215 accordingtoauthor. Entiremodule remainsUNCOMPILED asdelivered.

All fourdrafts passed forbidden-token/format scans. No full2583proof orrefutation exists in thisreview.
