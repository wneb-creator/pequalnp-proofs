Frozen source-to-Lean generation for actual exporter node1098.

The original generator, exact input JSON, report, and complete generation output
are preserved unchanged. replay.py differs only in importing sys and selecting
its input from this archive and its output directory from argv[1]. Run:

    python3 replay.py /tmp/oec/pequalnp-pilot-87/count-fixture1098-replay

The replay was independently checked to reproduce the exact archived Lean source
SHA cc018281d898af864d7b5f81137ca299dac39f2375d1506e55f160f9fc3c1091
and the report byte-for-byte. Its output is a finite table certificate; cuts and
child recurrence require their separate checked proofs. The untrusted generator
is outside the Lean trust base; all generated finite obligations are kernel checked.
