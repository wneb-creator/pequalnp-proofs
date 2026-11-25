# L-meta-3773 circuit search diagnostics

No 63-gate witness was found by these runs. No global lower bound or refutation
is claimed. There is no new Lean proof in this directory.

The whole-circuit encoding uses two one-hot fanin selectors per binary gate.
The five-point encoding additionally selects compatible outside OR trees.
All successful SAT candidates are independently evaluated against the full
finite test family; a five-point candidate is additionally evaluated on all
65,536 physical assignments. The two whole-circuit curriculum models are
invalid: they fail hundreds of negative tests and are preserved only as
search diagnostics.

The core round 1 solver reports UNSAT for at most two gate changes from the
specified frozen 58-gate seed, with all three output choices free and 109
selected constraints. This excludes only that finite repair neighborhood.
The exact CNF, metadata, seed, data and full solver output are preserved.
No independently checked SAT proof or Lean certificate was produced.
Core rounds 0 and 2 are inconclusive. Core round 980 is a zero-change UNSAT
smoke test, not an additional circuit lower bound. The bounded whole and
five-point searches are inconclusive unless their status file explicitly
records a successful (possibly invalid curriculum) candidate.

Known controls verify every clause of the whole 64-gate, core 60-gate, and
five-point 24-gate encodings. The original core control failed because its
string operation labels were passed to an integer-label interface; that
failed log is retained. The typed control fixes the interface and passes.
Later production code explicitly checks the integer-label schema.

The pencil circuits are all-positive overapproximations with false positives;
they are not witnesses. Both frozen global 63-gate near-candidates miss three
positive edges. Their bad AND gates admit absorption or double-star consensus
rewrites, so neither indicates a genuine saving over the 64-gate star cover.

Operation conventions are explicit in generators/metadata: whole SAT uses
strings; core/five SAT and pencil generators use 1=AND,0=OR; raw stochastic
global seeds use 0=AND,1=OR. Do not mix these conventions.

The scripts expect their data under /tmp/oec/pequalnp-pilot-79 and use the
bundled Lean-toolchain CaDiCaL. Each solver run is bounded by CPU, address-space
and wall limits, with an ordinary child environment and core dumps disabled.
Full stdout/stderr logs are retained. Current scripts may contain later
reviewed improvements; exact selected historical CNFs are therefore frozen
with compressed and uncompressed SHA-256 hashes. Exact source snapshots exist
for five-point rounds 2, 3 and control 992. Older inconclusive whole/core runs
are preserved as diagnostics, not claimed byte-for-byte source reconstructions.
