# Capped direct C4 exact-QQ trace attempt

Status: **UNKNOWN_OUTPUT_FILE_SIZE_LIMIT**, no Gröbner basis or nonexistence verdict. The serial rational run used the independently reviewed `../neogb-trace/` adapter with 32 critical pairs per batch, a 600-second wall limit, a 4 GiB address-space limit, and a 256 MiB per-output-file size limit. It received SIGXFSZ after 14.9887 seconds when the auxiliary trace reached that size.

The exact 12-variable, 31-equation input describes only the fixed-C4 off-diagonal support family. It is byte-identical to the earlier direct-C4 input, SHA256 `0bbe0c2f65b276ddfbf99d3bc262dfe160af2ef2d0062be5675784fb4241f9b6`. This is not a full-gap proof or refutation.

The archive preserves complete stdout/stderr, resource and binary metadata, exact input, and trace statistics/hash. The truncated 256 MiB trace remains in scratch and is intentionally omitted. Its SHA256 is `173114e22def4645729b82cc79bb6f6e82b7e070af2e58e2335effa179f60e7d`. No prefix or partial trace is presented as a certificate. Gzip level 1 reduced it to 122,016,828 bytes, still too large to preserve here.

Repeated matrix-input polynomial snapshots accounted for 146,316,158 bytes, output snapshots 47,824,599 bytes, and arithmetic records the remainder. This motivates a separately controlled compact monomial-reference adapter; that follow-up is not part of this frozen snapshot.
