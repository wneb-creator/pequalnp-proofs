# S06 finite-case archive, wave1

The17-case serial sweep completed at03:44:07UTC: five new online-checked CNF UNSAT cases (right-source wires14..18), twelve time limits (12,19..29), no SAT candidate. AAAA and the assigned shard remain open. Controller exit0 means the queue completed, not that all cases are UNSAT.

`summary.json` states the scope. `manifest.json` binds every archived file. `S06/serial-wave1/` contains complete final controller/runner records, atomic progress, event journal, copied metadata, all four solver/checker logs per case (including empty logs), and controller stdout/stderr. The production online runner retains proof hashes but no replayable proof stream. Its five verified results must not be described as retained certificates.

Replayable evidence is retained separately: all3692 RUP additions and earlier stages; the16 prefix-selector subcase proof; the1.24MB direct wire13 DRAT certificate; all local/independent checker logs and reviews; exact partition/coverage metadata. S08's final review is copied with full checker diagnostics under `S08/s06-final-review/`; earlier reviews/diagnostics are under `S08/s06-rup-review/`. Original review paths and hashes remain unchanged inside records.

No raw CNF or compiled solver/probe binary is archived. `omitted-files.json` retains their exact hashes and sizes. `cnf-recipes.json` plus deduplicated `cnf-deltas/` reconstruct every actual parent-derived input/snapshot exactly. Synthetic controller fixtures are reproduced by `S06/test_serial_controller.py`. Scalar TSV statistics are omitted with hashes; all full checker and solver diagnostics are retained.

To verify reconstruction without starting any worker:

    python3 S06/restore_archive_cnfs.py ARCHIVE ORIGINAL.cnf --verify-only

To restore raw CNFs into a fresh external directory:

    python3 S06/restore_archive_cnfs.py ARCHIVE ORIGINAL.cnf FRESH_EXTERNAL_DIRECTORY

ORIGINAL.cnf must have SHA25638d93ec59a86378a8434b232d19b2b53e8cbc3c715e81432ee94db59ca6ace08. Its exact metadata is in `parent/original.json`. Original generator dependencies are copied in `reproduction/`; use the recorded reverse-counter generator with --distinct-prefix to create a fresh parent, then build_original_strong.py on its prefix-distinct.cnf. These reproduce the source-pinned original DAG; they start no solver. The retained scripts' historical absolute scratch paths identify the tested layout.

`S06/probe.cpp` and generation scripts reproduce the RUP packages in their recorded scratch layout. Build with g++ -std=c++17 -O2 -Wall -Wextra, then run the root probe using all-vars.txt, build_probe_package.py, second_level.py, suffix_fanin.py, check_subcases.py and prepare_partition.py as documented in S06-report.md. Timings/timestamps may vary; proof and CNF bytes are bound in manifests. The archived RUP proofs can instead be checked directly with the pinned unchanged DSR binary, without rerunning generation.

`S06/serial_controller.py` is the frozen reviewed source bd2366dc9770fe35268092f06cbdbec0511a90585fee54bbd5fbb0b72cfc3e98. Final controller tests used simulated processes only; the completed production wave was separately launched by main. The default runner limit is20seconds and the total controller case budget is50seconds including up to30seconds cleanup/validation overhead. Hash pins, fresh-directory refusal, abort sentinel, strict four-log size/hash checks and SAT-stop/full-validator handling are retained. No second wave is authorized by this archive.

The package is prepared in S06 scratch for main's independent review/copy/push. Packaging itself starts no solver, checker, Lean or remote operation.
