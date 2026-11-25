# Full-star finite-field search with smaller pair batches

This run used the same reviewed full-star F1009 input and unchanged native
engine as `native-star-r1/`. The changed strategy set `--pairs 32`, with two
threads, a 600-second wall limit, 6 GiB address-space limit, and disabled core
dumps. A separate known-unit control exercised the batching path before this
run. Upstream includes same-LCM boundary ties, so selections reached 35 pairs
despite the parameter value 32.

The outcome was `UNKNOWN_TIME_LIMIT` after 600.085 seconds, with peak child
RSS 1,645,844 KiB. There were 126 completed algebra rounds, including repeated
descents from degree six to degrees four and five. The last completed round
selected 33 degree-six pairs, produced 28 new basis elements and five zero
reductions, and took 16.30 seconds. No basis or mathematical verdict was
emitted. The additional completed rounds are computational progress, not a
proof of consistency or inconsistency.

The frozen seven-file `native-star-b32-r2/` archive contains exact input and
provenance, a launch record written before execution with source/tool hashes,
full stdout/stderr, wrapper metadata, and wrapper source. The launch record
also identifies the prior control and explicit lease renewal. This remains
a finite-field diagnostic, not a characteristic-zero or Lean result.
