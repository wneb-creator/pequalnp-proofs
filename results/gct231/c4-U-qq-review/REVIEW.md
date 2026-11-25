# Independent U-nonzero QQ failure archive audit

Verdict: PASS for archive integrity, status and scope. The 14 covered files exactly match `SHA256SUMS`, whose SHA256 is 0eb6a2f21680531625ceda62accc632ee26ce034ff4028448c9d2078c91a4d80. Every listed file hash was verified.

Both runs correctly remain UNKNOWN_OUTPUT_FILE_SIZE_LIMIT, exit signal -25, at the 256-MiB cap. Case 2 ended after 69.296 seconds and 23 complete rounds; case 3 after 24.183 seconds and 35 complete rounds. The last partially printed matrix line is excluded from each count. Input and companion hashes, complete saved logs, metadata, and limits of 120 seconds / 1 GiB / pairs32 agree.

The README correctly makes no basis, characteristic-zero inconsistency, certificate or Lean claim. Large failed traces are represented by recorded size/hash metadata, not copied into the archive. This audit did not reread or replay those raw traces and makes no independent claim about their algebraic content. No source or archive was changed.
