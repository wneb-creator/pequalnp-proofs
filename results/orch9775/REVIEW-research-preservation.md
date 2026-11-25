# Independent preservation audit: remaining research

UTC: 2026-11-25T17:57:54.589261+00:00

Verdict: PASS for preservation of the selected frozen research files and complete diagnostic archives. This review checks containment, file types, integrity, provenance labels, and absence of recognizable credential patterns; semantic proof verdicts remain in the specific proof reviews.

All initial files are confined to results/orch9775, are regular files, and were hashed and rechecked after the archive audit. Seven cache files and the live standalone-build-first stdout/stderr pair were excluded. The two later PR18338 public status files were separately parsed/scanned and added. All selected external JSON files parse. The archive manifests exactly match1,525 and103 regular tar members with no duplicate, absolute, traversal, symlink, or unexpected entry. Member payload hashes and lengths all pass; nested gzip text scans pass. Complete audit stdout/stderr and detailed counts are preserved.

The exact staging payloads and hashes are recorded in checkpoint-research-manifest.json; checkpoint-research-stage.txt adds that manifest and itself. Nothing is staged or committed by this reviewer.
