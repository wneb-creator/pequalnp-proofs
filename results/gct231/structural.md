# L-gct-231 structural route

The full statement remains unresolved by this route. No three-dimensional
witness or general nonexistence theorem is claimed here.

## Row-sum-zero ansatz

Let V have columns (1,1,-1,-1), (1,-1,1,-1), (1,-1,-1,1).
Every complex symmetric row-sum-zero matrix is V A Vᵀ for a symmetric
three-by-three matrix A (with the corresponding harmless scaling of A).
Writing A's diagonal as a,b,c and off-diagonal entries as d,e,f, exact
24-permutation expansion gives

    permanent(J+z V A Vᵀ)
      = 24 + 16 z² (a²+b²+c²+2d²+2e²+2f²)
           + 64 z³ (abc+af²+be²+cd²+2def) + z⁴ permanent(V A Vᵀ).

Thus a three-dimensional row-sum-zero witness would be a maximal totally
isotropic plane for the displayed quadratic form and would annihilate the
displayed cubic. The quartic condition is not needed for the obstruction
found below.

Set r²=-2 and a_i=r(X_i+Y_i), off_i=X_i-Y_i. The quadratic becomes
-8 times the sum of X_i Y_i. Each admissible coordinate chart takes the
chosen X coordinates as free and writes Y=S X, where S is skew-symmetric
with three parameters. Swapping either coordinate of each hyperbolic pair
gives eight charts. All eight cubic coefficient ideals have Gröbner basis
[1] over Q(r). They reduce to two parity-distinct systems, because each
swap changes an off-diagonal sign and the cubic depends on these signs
only through their product.

The chart coverage has an independently reviewed linear-algebra argument:
projection of an isotropic three-plane onto any j hyperbolic coordinate
pairs has rank at least j. Its kernel is isotropic in the nondegenerate
complement of dimension 2(3-j), so that kernel has dimension at most 3-j.
Rado's independent-transversal theorem therefore selects three independent
coordinate columns, one from each pair. This is an invertible admissible
projection, and isotropy forces the graph matrix to be skew-symmetric.
This coverage argument is not formalized in Lean.

## Exact certificates and checked scope

The frozen `rowzero/` archive contains all source scripts, complete logs,
all eight explicit degree-one Nullstellensatz certificates, and a SHA256
manifest. Each certificate was checked by exact expansion. Clearing
denominators gives an integer identity

    sum_i H_i F_i - D = (r²+2) H.

`RowzeroCharts.lean` contains two independent polynomial contradiction
lemmas corresponding to the parity representatives. It compiled with only
unused-hypothesis warnings. It imports only PEqualNP.Defs and uses
`linear_combination` and `norm_num`; no computational oracle is trusted.
Its SHA256 is
`25037c36ccebc6181f1e4554611db1b33f1691084452cad91dee95ff8ac86856`.
These are polynomial lemmas only: they do not establish the geometric
reduction or refute the full unrestricted gap in Lean.

The status_review agent independently reproduced the permanent expansion,
all eight Gröbner bases, the parity reduction, and the chart-coverage
argument. An independent Lean source/axiom audit was requested after the
successful build.

## Path-support and full path chart

`path_support.py` independently parameterizes variations supported on
off-diagonal edges 01,12,23, with these entries x,y,z. Diagonal00,11,22 are
arbitrary linear forms; diagonal33 enforces total entry sum zero. The
resulting 31 equations in nine unknowns have exact QQ Gröbner basis [1]
(99.64 seconds, complete log preserved in task scratch). This excludes
only that fixed-support family.

The full path chart allows the other three off-diagonal entries to be
arbitrary linear forms as well, yielding 18 unknowns. The bounded
300-second run of the finite agent's shared exact generator returned
UNKNOWN_TIME_LIMIT at 300.0125 seconds, with no basis produced. This is
not evidence of nonexistence.

A separate complex least-squares search ran 1,000 starts with seed
23175013. It found no witness; the best maximum coefficient residual was
0.06530386596151683, at coefficient-vector norm 5.2079. This is only a
failure to find a witness. The `path/` archive preserves every source,
equation system, full log, numerical best point and status file.

## Disjoint coordinate-pair planes

In the full Hadamard tangent coordinates write the transformed symmetric
matrix as [[0,bᵀ],[b,A]]. The quadratic form is proportional to
tr(A²)-6 b·b. Normalize the three b coordinates, three diagonal A
coordinates and three off-diagonal A coordinates to weights -1 and +1.
There are 72 coordinate-pair isotropic lines, including both signs for
each of the 36 pairs. Every such line was tested by exact symbolic cubic
and quartic evaluation; none is a constant-permanent line. Consequently
no three-plane spanned by three disjoint such pairs can work. No
numerical triple filtering was needed. This is a finite ansatz exclusion,
not a general classification. Sources, all 72 coefficient records and
complete output are frozen in `coordinate-pairs/`.

## Axiom audit

`RowzeroChartsAudit.lean` and the complete `rowzero-axiom-audit.log` sit
outside the frozen rowzero archive. Both polynomial contradiction lemmas
depend only on propext, Classical.choice and Quot.sound. Independent
review matched their hypothesis polynomials to the exact chart systems
and checked all certificate identities.

## Exact OpenF4 row certificates (10:09 UTC checkpoint)

A separate source overlay, generated by `gct231/make_trace_overlay.py` in scratch, records each initial Macaulay row, every rational row addition/scaling, and every resulting polynomial. It leaves the shared OpenF4 source and finite agent adapter unchanged. The critical-pair batch is capped at 32, retaining the remaining queue.

`replay_f4_trace.py` checks original generators against the input, recognizes every new input row as a scalar monomial multiple of an already established polynomial, and independently verifies every output polynomial as an exact rational combination of its initial rows. It does not rely on the reported Groebner-basis verdict. The strict OpenF4 text parser gives a byte-identical rowzero certificate to the original SymPy parser.

Toy unit, nonunit, and rational-basis controls passed. The known rowzero unit system (four variables, eleven equations) solved in 0.034 seconds; replay verified all 170 output identities. Its dependency slice contains 63 polynomial steps. The first 69 KiB Lean emission failed at a large nested linear-combination expression; a balanced, parent-grouped 71 KiB revision is still being compiled at this checkpoint. No successful new Lean result is claimed yet.

The known star-support system (nine variables, 31 equations) solved in 3.131 seconds with the 32-pair cap, versus a previous 120-second timeout without it. Its full trace is about 10 MB; exact replay of its 2,492 outputs is pending. No full 18-variable chart run has started; root requested successful exact support replay first. These are proof-pipeline calibrations, not a proof or refutation of L-gct-231.

### Exact trace update (10:14 UTC)

The star-support trace now passes both independent parsing paths: all 2,492 output identities are verified, and the final nonzero constant is established. Both complete certificate JSON files have SHA256 `d8455c78d9ea4e6b1164f3d368b088579be71bf81008f64d617ca1ce678dfbc0`. The necessary slice has 724 steps, 48,016 polynomial terms and 51,427 parent-combination terms; compact JSON is 6,749,809 bytes. This does not yet fit a straightforward 512 KiB Lean emission.

The rowzero Lean emission failure was precisely a missing type annotation on the final constant equation, which Lean defaulted to Nat; both prior failed logs are retained. A corrected 71,633-byte source explicitly types all equations in complex numbers. Its compilation is deferred while the root serializes Lean builds to avoid OOM. No new successful Lean compile is claimed.

The full path 18-variable chart, batch32, failed under its 2 GiB address-space cap after 15.646 seconds with `GNU MP: Cannot allocate memory (size=8)`, exit -6. This is UNKNOWN, not a contradiction or solution. Full stdout/stderr and the 49,724,206-byte partial row trace remain in scratch. Root authorized one batch4 / 4 GiB / 120-second retry after the finite agent's modular diagnostic finishes. The adapter now takes an explicit batch-limit argument; its batch4 toy-unit control passed exact replay.

### Trace Lean calibration checked

The corrected exact row-trace Lean theorem `rowzero_even_trace` compiled with exit0 in58.933seconds, peakprocessgroupRSS5,994,936KiB. Source71,633bytes/128lines, SHA25683e92fab3fbcd7e2d8f6911457652926b97fa2102e209fec0b2e87ae61780483. Global independently checked the same source, its emitted polynomial identities, and both calibration systems. The complete reviewed archive is `f4-trace/`, including buildlogs and resource metadata; no full-gap conclusion is claimed.
