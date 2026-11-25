# NOT elimination and descendant audit

## Findings

- Generic size-preserving NOT elimination was not found. Existing OneNot helpers prove conditional replacement/deletion under a fixed sign of the negated wire; they do not eliminate a NOT on all inputs of a nonconstant monotone function.
- `L_meta_4725.lean` proves the exact binaryFloor hypothesis of `R_meta_2592_271`: Petersen-computing FanInTwo C implies 15 + notCount C ≤ C.size. 3224 lines, 146284 bytes. Imports Mathlib.Tactic, Mathlib.Combinatorics.SimpleGraph.Basic, PEqualNP.Defs only. Thus any desired counterexample has1..4NOT.
- `L_meta_5236.lean` proves the first-nonedge-OR residual case with3..4NOT and≤18gates. Its helper atLeastSixteen actually gives≥16binary gates with negations free, even given x0∨x2 free. 4560lines,285226bytes,Defs only.
- `L_meta_5238.lean` handles≥5NOT in the same free-OR residual.
- `L_meta_8367.lean` proves the9-vertex deletion function cannot be computed with≤15gates and≤2NOT (strict normalized circuits). 6873lines,524213bytes, nearly512KiB alone.
- `L_meta_4988.lean` lower-bounds9-vertex deletion with free x4∨x6 and1..2NOT by15gates; the statement requires unique ordered readers of4and6, but final proof ignores the reader and NOT hypotheses and invokes stronger `glue_one`. `L_meta_4986.lean` is a monotone sampled variant.
- `L_meta_3404.lean` provides≥14gates for9-vertex deletion plus free x0∨x4 and OR of≤2inputs,1..2NOT.
- `L_meta_5096.lean` rules out≤13gates for9-vertex deletion plus free x0∨x2 and certain secondOR gates.

## Remaining gaps in assembly

The three R2592 reductions are all present. Few-NOT step4727 has only reductions; L8021 is a vacuous no-NOT subcase. Parent first-gate split651→1884/1886/1888/1890 has only reductions for these four. For1888, R1888_3 splits normalized residual by NOT counts: L5236 andL5238 are present, but5232(monotone) and5234(1..2NOT) have only reductions. R5234_1 has a checked9-vertex-deletion premise(L8367), but its other tight-shape premises remain unlocated.

## Notes

Inlining several complete signed certificate files exceeds512KiB. Their live-wire compiler and finite search kernel are heavily duplicated and potentially shareable; consolidate only after choosing a concrete closed route. No final Lean file edited by this agent.


## Stronger signed bound route (paused for lease audit)

Coordinated with lower_bound agent: L5236 Extended uses BitVec1024, not a sampled cube. Its ten pins encode variables in bitpositions [9,7,5,8,6,4,2,0,3,1]. Projecting to low512rows sets Petersen vertex0 tofalse and leaves the9-vertex deletion graph with checked signed binary lower bound15 (`nineFloor`).

Every pair of distinct Petersen vertices a,b has this cofactor essentiality: after fixing b to eitherfalse ortrue, the target still depends on a. A finite certificate can choose w adjacent to a, distinct fromb, and nonadjacent tob; compare assignments with truevertices {w} plus(optional b), against the same assignment plusa. No triangles/C4s guarantee such w; finite10-vertex check is simplest.

Consequently, in the FIRST step of signed Live extraction, BOTH input operands a,b must remain in the live remainderU. Ifa vanished, chooseb's canalizingvalue for the selected bin operation (AND:b=0;OR:b=1;a&!b:b=1;!a&b:b=0). The two essentiality witnessrows agree onallremaininginputs andthefirstgate, but disagreeontarget, violating Live.row_difference. Sameargumentforb.

For any retainedoperand a, use a graphautomorphism carrying it tovertex0, restricta=0, and project the suffix. Firstbinarygatecollapsestoa literal orconstant andremainingbankrootsare signedavailablefromnineinputs. The retaineda gives oneconstant cost in suffixmass. Thus suffix k≥15+1=16 andfullbinary≥17.

For AND or signedAND firstgate, choosea positiveoperandsetto0: firstgateitself becomesconstant aswellasretaineda. Suffixmass≥2 givesbinary≥18. ORfirstgate givesonly17 withcurrentconstant-only mass. AlthoughORaliasesotherretainedinput onrestriction, duplicatebankentries cannot becharged asconstantsgenerically (multiplexer counterexample), so no automatic18claim.

Lower_bound agent owns generic retained_operand_floor using projected_bound. This agent was toprovide finitecofactorwitnesses and10vertexautomorphisms. No17-sourcefile was written beforepause. Exact requiredsymmetry facts: for eacha∈Extended.pins, rows:Fin512→Fin1024 setsobservea constant, carriesExtended.target to9graph, andsends everyinputpin to Available true(inputs.map observe). Can generate10automorphisms from existingR651_1 generators; rowmap permutesbitsaccordingly. Goalshavefinite domains andcan becheckedwithdecide+kernel.
