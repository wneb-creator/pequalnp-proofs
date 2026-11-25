# Exact synthesis strategy

2026-11-25T13:50:59.328792+00:00

Built official Kissat SAT solver under scratch. Wrote CNF synthesis encoder with one-hot gate kind and source selection, binary AND/OR and unary NOT; output is final gate. Complete scripts/logs at `/tmp/oec/pequalnp-pilot-98/exact/`.

Encoder sanity check: fixed independently validated 20-gate Petersen circuit, all 1024 rows, SAT decoded exact circuit (zero mismatches). Flexible 19-gate CEGIS starts with singleton, pair, all-zero/all-one, and 16 random assignments; adds up to32 counterexamples per candidate. Initial attempt exactly one NOT and first gate AND of adjacent inputs0,1. Solver cap120 CPU seconds per round; one solver process. No result yet.

Search is counterexample-oriented; restricted encoding excludes constants, duplicate binary operands, and non-last outputs, so UNSAT of this encoding would not by itself prove the posted statement.

2026-11-25T13:54:01.493655+00:00 General19-gate first-orbit CEGIS hit120 CPU sec without SAT/UNSAT. This is inconclusive.

Derived focused problem from stochastic near19 candidate: independent satellites {2,4,5,6}; remaining six vertices {0,1,3,7,8,9} induce matching {01,38,79}. A11-gate multioutput circuit for four satellite-neighborhood ORtriples and matching M yields full19-gate circuit via4 satellite AND+4 finalOR. Root/direct_lower_bound observation improves constraints: matching must be exact64 assignments; ORtriples matter only on27 assignments where matching is false. Running both exact and relaxed11-gate models with oneNOT, arbitrary output selectors,300CPU-second caps. Code `multi.py`, `multi_relaxed.py`, directories `multi11`, `relaxed11`.

2026-11-25T13:58:30.572548+00:00 Computational obstructions found (not Lean proofs):

- Four star ORtriple outputs alone,27point matching-false care domain,7totalgates exactly1NOT: UNSAT,0.19CPU s,7014conflicts.
- Same with8totalgates exactly1NOT: UNSAT,1.66CPU s,55750conflicts.
- Control8totalgates0NOT: SAT, decoded valid fourORtriples.
- Same8totalgates exactly1NOT evaluated only onempty+6singleton inputs: UNSAT,2.31CPU s,96236conflicts. This suggests a finite7bit set-generation obstruction.

All these search encodings exclude repeated binary operands and constants, enforce allgatesused, and oneNOT cannot be designated output (each desired output increases fromempty tosome singleton). They are computational evidence about that restricted model only; no wholePetersen conclusion follows.

Current scripts SHA256:
- `synth.py` `9ed85f79a595e3829619ea1325907360248977628b239c0a7b2b6f7ae9b56f63`
- `multi.py` `537068b631cf25f23ce10682da07de99c467793dd52e414ed2fd28fca6b86df8`
- `multi_relaxed.py` `395e2e238a4cd02686d579a1811f11eaa1c0d7bcd86fb07f7b3824254c55c9b6`
- `multi_relaxed_count.py` `418d87f951e54cf7847dadc51cf81a35ff279a9d606913ba7cd856b86e5dcb40`
- `stars_relaxed.py` `7c90a07e0f22a21bd36a1795661077a1dd37514fb69fe13d70885721ed680204`
- `stars_singletons.py` `7b1a6798e313f1af2858394c9710226be6cae9ce405b637601249d4d7027d58b`

2026-11-25T14:00:07.197061+00:00 Further focused repair: with free6coreinputs, one satellite x5, four exactORtriples B,E,H,J, synthesize matching M OR(x5 ANDJ) using5extra gates incl1NOT. Exhaustive128rowSAT encoding UNSAT in0.27CPU sec(3574conflicts). This blocks the obvious5gate complemented replacement of the near19 product expression. Complete logs/CNF at exact/residual5; generator residual.py.

2026-11-25T14:02:15.688294+00:00 Main synthesis results: full19gate orbitANDadjacent+1NOT (120s), exact11core+1NOT(300s), relaxed11core+1NOT(300s), relaxed11core+3NOT(120s), relaxed12core0NOT firstORnonmatching(120s) all timedout UNKNOWN. NoSATwitness and noUNSATconclusion for these.

Now running boundedSAT repair around stochastic best19 (4wrongrows), atmost4 gateedits withNOTplacementfree, exactly1NOT, allgatesactive,188initialrows includingallweight≤3.180s cap thenCEGIS. Source synth_distance.py; near19-d4.

2026-11-25T14:20:21.892016+00:00 Switched to incrementalCaDiCaL2.1.2 linked from pinnedLean distribution, no solver rebuild. Matchedheader fetched fromofficialrel-2.1.2 tag. API smokeSAT→SAT→UNSAT passed; fixed20monotone and23gate1NOT controls bothvalidatedall1024. Active900-wall-second19gate1NOTsearch preservesclauses/phases acrosscounterexample additions. Canonicalfaninorder, positivepath-to-output foreachinput(neededfor1NOTtarget), allfirstorbits viafirstleft0/right∈{0,1,2}; latter argument underindependentreview. Code incremental.cpp, log exact/inc19.log.

Prior900wall-secondKissatgeneral19orbitORnonedge endedUNKNOWN withoutcandidate. Factored11core1NOT120wallpilot likewiseUNKNOWN. RegenerablefinishedCNFs removedtodisk-pressurewithchecksumsmanifest; fullstdoutstderr retained.

2026-11-25T14:24:05.996933+00:00 Archived completefinishedsolverlogs compressed underresults/orch/exact/logs, withuncompressedSHA256inarchived-logs.json. Thesearecomputationalevidence, notLeanproofs. Currentincrementalrunlogremainsliveinscratchuntilcompletion. Independentreviewatresults/orch/sat-review.md confirmsencoding, indexing, canonicalallorbitcut, andpositivepathnecessityforoneNOT.

2026-11-25T14:30:39.487881+00:00 Preparedsequentialexact2–4NOT phases. General signed-path necessity nowimplemented andindependentlyreviewed: binarygates unionpositive/negative reachability; NOTswaps; everyessentialinput requirespositiveoutputpath. Only1NOTrunusesthezero-NOT-path specialization. Full1024 controlsPASS for22g2NOT(doubleoutputnegation),23g3NOT(replaceanORwithDeMorgan),24g4NOT(quadoutputnegation). Actualsearches19g2–4NOTnotyetlaunched; waitfor1NOT900wallphase. NextdriverprintsCPUandwallmetrics.

2026-11-25T14:36:38.913439+00:00 Full19gate1NOTincrementalphase endedUNKNOWN at900wallsec,8models,40rows,best92full-tableerrors. External1secondprocessCPUpoll recorded788.27CPU sec justbeforeexit(lowerbound). Completephase log+monitor archived.

Started19gate2NOT900wallphase sequentially afterfreshrootlease. Usesgeneral signedpaths andnewindependentlyreviewedorbitpriority: anyprimaryNOT forcesfirstNOT0; else anyinputedgegate forcesfirst01; otherwisefirst02. Full1024 controlswith0,1,2,3,4NOTallpassed. Source/binaryhashes+UTCstoredinc19-not2-meta.json.

2026-11-25T14:40:03.590029+00:00 STOPPED afterrootleaseHTTP410. SentSIGINTtoown2NOTsolver;exit-2 confirmed. Noactiveownsearchremains. Full19gate1NOTphaseUNKNOWN900wallsec;2NOTphaseINTERRUPTEDafter202.417957wallsec. No19gatefull-tablewitnessfound; noLeanprooffromthisagent. Completecurrentlogs/meta/candidates/generatorspreservedunderresults/orch/exact; FINAL-STATUS.json isauthoritativecurrentstatus. Awaitnewrootleasebeforeanyfurthergapwork.
