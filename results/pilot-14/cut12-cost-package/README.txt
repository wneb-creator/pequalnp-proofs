UNVERIFIED diagnostic search-cost census for L-meta-670.

All11,365 enabled budget12 frontier cases were measured with exact native
projection-prefix contexts, twelve projection coverage checks, no automorphism
memoization, and semantic state memoization. Each case resets caches. These
counts measure candidate replay cost; they do not constitute a Lean proof.

Compile live_cut12_batch.cpp with g++ -std=c++17 -O2. Decompress
cut12_seed_data.txt.gz in the working directory. Arguments are per-case wall
seconds, per-case node cap, first seed, memo flag, optimization mode, exclusive
last seed. Commands used:
  ./live_cut12_batch 2 5000 0 1 0 1000
  ./live_cut12_batch 2 5000 1000 1 0 11365
  ./live_cut12_batch 2 50000 11315 0 0 11365

Nodes are capped immediately after increment, so UNKNOWN records have5001
calls. Wall/RSS caps are only sampled every65,536 calls. Native completed
EXCLUDED is not a machine-checked Lean lower bound. SeedMetadata triples are
[k,t,globalRow] in Cut12CodecManifest order. The seed text includes exact
projected circuits, so the larger original JSON context file is unnecessary.

Allcases totals:1933 exceed1000 calls, representing1662 distinct global rows.
Ninety t0 cases hit5000 cap. Combined native measured search time82.76seconds.
The fifty t4 cases withoutmemo range1..568 calls, total9086calls.
