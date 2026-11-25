# Counterexample route for L-meta-2583

## Semantics

ReadK means one proof tree per prime implicant whose leaf multiplicities are bounded, not input fanout one. For this incidence function the prime implicants are the incident point-line pairs. A star circuit is read1. IsAO2 means AND/OR only, exactly two inputs per gate, all reads to earlier wires.

## Smallest plane ruled out by existing proof

The final theorem in checked L_meta_971 proves the unrestricted monotone Heawood/Fano lower bound27. L_meta_7997 transports this to the cyclic Fano labeling. Thus a26gate Fano search cannot supply the desired refutation; it was not started.

## Order3 plane

`counterexample_2583_data.py` builds PG(2,3) from normalized nonzero vectors in F3³ with first nonzero coordinate1, lexicographically ordered. Point/line incidence is dot product zero. Independently checked all13 point and line degrees4 and exactly one common line for every distinct point pair. There are52edges on26input variables. The star circuit uses64gates.

Exhausted all8192point subsets. Each determines its maximal compatible line subset; retaining only closed point subsets gives exactly704maximal independent sets. Together with52minimal true edge pairs these form756complete boundary rows for a monotone circuit. Data is in `counterexample_2583_data.json`.

A size63candidate below the known read1 floor64 would refute normalization, provided its computation and the read1 bound are proved inLean. No such candidate is known from this work.

## Search and SAT seeds

A random hill-climbing AND/OR search evaluates all756rows. The first run allowed deletions anywhere in a64gate star circuit; its final recorded best was2missing boundary rows before it was stopped for an improved strategy. The refined run always deletes one innerOR input, so every random seed has exactly one missing incidence. It randomizes star side, star order, OR parenthesization, and uses neutral/improving mutations with occasional small escapes. Complete logs remain in task scratch and will be copied here.

Constructed a deterministic63gate circuit with only edge(0,14) missing, verified onall756rows, for localSAT repair. A second seed uses projective duality followed by GL3 action A=[[0,0,1],[0,1,0],[1,2,0]] and contragredient line action. Its input permutation preserves every incidence. Greedy topological reordering puts OR(0,1) first and makes maximum source indices nondecreasing. This canonical seed misses only edge(3,17). Generator: `counterexample_2583_relabel.py`.

## Lean prerequisite

`counterexample_2583_pg3.lean` defines explicit13row incidence masks, proves line degree4 and unique pair lines, and supplies a perfect matching point→line `[10,5,4,2,0,12,1,11,8,9,7,6,3]`. Compiled with Lean exit0; complete stdout/stderr empty. Independent checker_audit source review passed for all four finite claims. This validates prerequisites, not the posted normalization theorem.


## Stopped and preserved after lease410

Root instructed STOP after renewal HTTP410 at15:06:52UTC and diagnosticconfirmation15:07:20UTC. No core search or forced-reread longrun was started. The initial unrestricted-deletion run reached best2errors before it was terminated for replacement; the full900second refined run remains a search only and did not find an exact witness.

Prepared forced-reread search:14AND/49OR whole-plane seeds with2missingedges and2acceptededges lacking anyread1tree. The saved seed was independently checked againstall756boundaryrows and thefullcapped count-vector recurrence for52edgepairs. Only a zero-second initial-seed validation ran; no long forced-reread search ran.

Prepared core strategy: select kpoints andalltheirincidentlines. Acore circuit ofatmost5k−2 gates lifts toatmost63full-plane gates byadding the13−kremaining4-gatepointstars and13−kORs. Exhaustive projective-generator orbits give3k4,3k5,4k6,and4k7 representatives. Each JSONrecordsits globalwiremap and completeboundaryrows; eachTXT hasSATschema n point_count edge_count row_count,thenedges,thenrows. ThemapTXT recordsselectedpointsandglobalwiremap.

Promising untestedcore: k6_r1 has17inputs,24edges,76completeboundaryrows,and28gatetarget versus29-gatestar construction. Its11lineinputs consistoftwo degree3linesandnine degree2lines, withno privateleaves. k5_r2 has16inputs,20edges,50rows,and23gatetarget.

`counterexample_2583_lift.cpp` implements explicitglobalcircuit lifting and checks52edges,704maximalnegativeclosures,andall8192point-subsetnegativeclosures. `counterexample_2583_core_search.cpp` implementsnormalorforced-reread coresearch with64-bititerationcounters. They compiled, butno runtime selftest was completed beforeSTOP; do nottreatthem asvalidated results. No core search was run.
