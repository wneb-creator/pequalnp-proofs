# Independent syntactic slicer review

PASS. The slicer preserves all original generator records and recursively follows
row-operation parents plus prior-output references of monomial input records.
It keeps every output record for a retained node, so an M parent is still
established before use. Original order is preserved and gaps in node IDs are
accepted by the exact replayer. It rejects incomplete last lines, forward or
missing M references, late literal fallback inputs, and traces with no literal
nonzero constant output. The transformation is deliberately untrusted: the
unchanged exact replay must still verify every polynomial identity.

Independent rerun of slicing the frozen rowzero control followed by unchanged
exact replay passed and established a nonzero constant. No heavy CAS or Lean
build was run, and this review makes no full-chart claim.

Source SHA256: bcbee5bd5f339fcfe59df4bbdb9ea89d7d149fc7f52aa6a3463b0f298f0d2d65

Slice metadata: {"constant_node": 898, "needed_nodes": 768, "output": "/tmp/oec/pequalnp-pilot-75/gct231/slicer-review/rowzero.slice.trace", "output_bytes": 25677, "output_records": {"A": 477, "G": 11, "I": 11, "M": 135, "O": 35, "S": 145}, "output_sha256": "1c977410c100214ac29d1dbd907ed866a8d094a156fcf172f47af9fcfecaac47", "scope": "Untrusted syntactic dependency slice; exact replay is still required.", "source": "/tmp/oec/pequalnp-pilot-75/gct231/sparse-engine/certificate-trace-compact/rowzero.trace", "source_bytes": 29728, "source_nodes": 898, "source_records": {"A": 566, "G": 11, "I": 11, "M": 141, "O": 43, "S": 180}, "source_sha256": "3f0792b625a128030796442bf1308edc556cb305f6ee3285e09cebfa6f24152b"}
