# L-meta-2590 structural route

The active statement rules out size<=19 Monotone2 circuits computing the Petersen edge function. Imports allow PEqualNP.Defs and Mathlib. Root owns lease/git.

## Existing sharp route

The read1 lower bound gives15edges+6vertexcover-1=20; toolchain_setup owns that extraction. No existing IsLeastAO theorem specialized to Petersen was found. Existing L1491 provides top/junk/Ustar accounting; L1492/1503/1505/1506 give one-junk structure. One-junk eliminations L3653/L3700 assume bipartite, so cannot directly apply to Petersen, whose5cycles are material.

## Structural observation under investigation

For a first dirty AND g=(OR A) AND (OR B), a clean top g AND (OR R) accepts minimal quadratic pairs only with an endpoint in R intersect(A union B). R vertices outside A union B contribute only higher-degree terms. If A andB disjoint and bothhave at least2vertices, C4-freeness forces at mostone admissible centre in R intersectA and at mostone in R intersectB. If bothcentres exist, theyare adjacent; triangle-freeness obstructs sharing OR R with any other clean AND whoseotheroperand is purelylinear. Turning this into budget-preserving surgery still requires controlling shared OR cones.

## General normalization strengthening

Copied generic singleton and joint-normalization drafts from2583 into fresh2590 namespaces because they apply to arbitrary graphs, including Petersen. Singleton2590.lean: replace a gate with singleton positive-edge profile by the atomic primary-input AND, preserving size/function and all positivewireprofiles while decreasing wirefunctions. StrongNormal2590.lean: firstminimize dirtyORcount amongleastcircuits, then numberofnon-atomic singleton-profilegates; obtains both mixedOR-free and atomic-singleton conditions simultaneously. Drafts were independently staticallyreviewed in2583, butnotcompiled beforelease410; fresh2590 firstbuilds pending.
