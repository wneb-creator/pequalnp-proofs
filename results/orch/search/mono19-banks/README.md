Tight monotone formula banks from an incomplete copy-search benchmark

The fresh source adds only the already proved restrictions: distinct operands,
proper output, and output distinct from either operand. The banks source adds
JSONL instrumentation for slow or large depth-0 closures and the interrupted
closure at the resource guard. No bank is a counterexample or a full proof.

Fresh run: --cap 19 --seconds 120 --nodes 1000000
Instrumented run: --cap 19 --seconds 60 --nodes 1000000
Both reached the same 41,908 visits before the estimated memory guard,
850,009,940 bytes, with 4,896 closure attempts. The estimate is not measured RSS.
The root monotone-19 exclusion remains unfinished.

The JSONL preserves 41 snapshots. Each raw state list preserves duplicate
labels, has remaining budget exactly raw.length - 1, and gives exact 1024-bit
truth words. The selected file has the eight largest snapshots. All eight
selected banks are pure input multisets with 20 roots and budget 19. One is
interrupted, marked reason=limit; the others completed computational closure.
The complete benchmark logs and exact sources are preserved.

These banks are being tested against independently checked rectangle weights;
no rectangle cut or unified recursive Lean certificate is claimed here.
