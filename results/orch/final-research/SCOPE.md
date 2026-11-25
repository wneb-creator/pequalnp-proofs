# Final research preservation bundle

This bundle preserves completed research for job pequalnp-pilot-60 and
gap L-meta-2602. It contains no proof of the posted theorem and no Lean
certificate for the SAT outcomes. No solver was rerun while packaging.

Outcomes:

- All four six-vertex C4-free seven-edge graph types were UNSAT with five
  AND gates in the normalized free-OR model for their vertex-cover CNFs.
  By duality these searches found no five-OR circuits for the quadratic
  graph functions. Full truth inputs were encoded, not merely edge pairs.
- The seven-vertex bipartite seven-edge type was also UNSAT at five ANDs.
- The clean-cover sampler checked148236 transitions in24706 trials over
  forty seconds without finding a local violation. Explicit larger/local
  counterexamples nevertheless refute the proposed potential; see notes.
- The original generic plane signed-code run was UNKNOWN at45seconds.
  Two intended180-second extensions retained a hard300MiB address-space
  cap. The default run aborted after13.20seconds and the --plain fallback
  after15.01seconds, both with std::bad_alloc/SIGABRT and UNKNOWN. No model
  or UNSAT certificate was obtained. The cap was never raised.

Preservation:

- logs/ contains complete stdout/stderr logs and run metadata.
- inputs/ contains graph/row data, exact small CNFs and the exact generic
  plane CNF, losslessly gzip-compressed. Each compressed input was streamed
  back through SHA256 and byte-count verification before packaging ended.
- sources/ contains the exact generators, dependencies, bounded runner,
  and the packaging script. Solver binaries are not copied; the manifest
  records the installed CaDiCaL binary hash and the logs identify its version.
- manifest.json maps every payload file to its original source and hash.
  SHA256SUMS covers every bundle file except itself. Original scratch
  files remain untouched.

The packaged scripts may be run from sources/ because their sibling imports
are included. The exact commands and original paths are preserved in logs,
metadata, and the source argument parsers. Reproduction should decompress a
CNF into scratch before passing it to CaDiCaL. This bundle does not authorize
additional solver execution or a larger resource cap.

The circuit counterexamples to proposed local potentials are also preserved
by the structural agent in results/orch/tau-*.json and research-support/.
Those examples refute intermediate proof strategies, not L-meta-2602.
