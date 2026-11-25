L-meta-2583 status and star bound

2026-11-25T14:53:18.466733+00:00

Status: canonical gaps feed updated 2026-11-25T14:50:47.740Z lists L-meta-2583 and L-meta-2584 open. Neither is checked/withdrawn.2584 is the general C4-free bipartite READ-2 replacement statement, not the negation of2583. The desk assigned2583 with reductions_open=false.

GitHub canonical repository is now open-goat/pequalnp-proofs; the brilliant-hq REST endpoint redirects to this full_name. All-state search for2583 returned6/6 records, incomplete_results=false. One PR is open: https://github.com/open-goat/pequalnp-proofs/pull/13723. It contains7090lines of partial lemmas, but no final fully qualified theorem. Intake refused it before building on2026-11-25T12:01:08Z: the theorem must stand at the top level, last, written with its full name. Its last result is only unrestricted_plane_size_lower:3*N-1≤C.size. The source was saved read-only in scratch/plane-pr13723-source.lean; it also has two imports beyondDefs. No merged2583 proof. All-state2584 search returned7/7 records, all closed unmerged.

Branch: pnp/pilot-100 at 34b0ebd3ad13f4b76273ac2ca0d2a9738ddc8219. Origin branch observation: 34b0ebd3ad13f4b76273ac2ca0d2a9738ddc8219	refs/heads/pnp/pilot-100. No local origin/pnp/pilot-100 tracking ref exists; git status still compares withorigin/main, so its ahead count is not proof of unpushed work. Latest preservation commits are34b0ebd3 andaa417739. Existing Petersen files are old-gap partials, not a2583 solution; any eventual proof PR must contain only the new2583 file.

Exact checked reusable sources:

- PEqualNP.ReadK.IsReadK in lean/PEqualNP/Defs/ReadK.lean:162 quantifies over prime implicants and requires one joint proof tree with each leaf variable used at mostk times. It is not a global fan-out/read-once condition.
- PEqualNP.TopForm.IsAO2 in lean/PEqualNP/Defs/TopForm.lean:82 is AND/OR-only, earlier reads, and exactly two operands at each gate, repetitions allowed.
- lean/PEqualNP/Outside/L_meta_2393.lean:4673, PEqualNP.Outside.L_meta_2393.Own.upper, constructs an AO2 circuit computing incidence, READ-1, with D.size+1=N*(q+2), assuming onlyN>0 and eachline hasq+1points. The same Own namespace has lines_through:4806 and cover_ge:4977 for point regularity and minimumcover≥N.
- L_meta_7684.lean:1123 constructs READ-1 AO2 from any bipartite vertex cover with size≤|E|+|cover|−1.
- L_meta_7639.lean:1964 gives |E|+N≤C.size+1 for C4-free bipartite incidence with a perfectmatching, explicitly assuming C isREAD-1. L_meta_2237:1877 andL_meta_6369:1394 give the corresponding graph vertex-cover lower bound, also assumingREAD-1.

Independent count: N lines each haveq+1point neighbors. A line-star needsq binaryORs ofpoints andoneAND with its linevariable. TheN stars needN−1 outputORs. Total=N*q+N+(N−1)=N*(q+2)−1; each incidence pair chooses its star and its point in the OR tree, giving one pointleaf andone lineleaf. This construction is supported by the checked Own.upper helper.

Obstacle: the matching lower bound for arbitraryAO2 is not supplied by these READ-1 results. Forq=2,N=7 it is27gates. Applying READ-1 lower bounds to arbitraryC would assume the desired normalization. The available unrestricted3N−1 bound is strictly weaker forq≥2. No full proof or refutation established.
