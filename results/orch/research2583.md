L-meta-2583 research notes

Read on 2026-11-25 UTC: https://github.com/open-goat/pequalnp-proofs/discussions/12644 . The author reports negative small core-cover and PG(2,3) local searches, explicitly noting incomplete definition auditing and a failed positive control. We treat those observations as context only. They are not proofs of the present theorem. The linked gist could not be opened through the web tool.

Exact reduction established by checked local components: the desired read-1 replacement follows if every arbitrary AO2 incidence circuit has at least N*(q+2)-1 gates. Existing constructor attains that cost; reviewed lower bound establishes it only for read-1 circuits. Applying it directly to arbitrary C would be circular.

Current new proof attempt: eliminate any gate false on every incident-pair input from a least AO2 circuit. Force false can only decrease a monotone function, preserves every minimal positive input, and should preserve the whole edge function. Existing circuit surgery can compile this deletion without constants.

Read 2026-11-25: https://pequalnp.com/papers/note-1 , section7. The site distinguishes formula and read-restricted lower bounds from arbitrary monotone circuits and identifies the latter as a historical open problem in its cited literature. We read the site account, but did not independently read the cited2005 primary paper; its historical scope is therefore UNVERIFIED from that primary source. This supports treating generic homogeneous-circuit conversion as an unresolved mathematical step.
