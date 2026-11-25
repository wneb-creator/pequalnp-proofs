# Independent review: auxiliary14 rebuild kit

UTC: 2026-11-25T16:55:41.209368+00:00

Verdict: PASS static/provenance review. The complete script was not executed during this review, and no repeated large Lean compilation is claimed.

Independently checked bash syntax, the exact20-module export order, every direct source import against its listed project target or previously exported module, and every recorded source SHA256. The eight project targets are built before the short-name exports. The script derives paths from its own location, enters the pinned Lean project, prepends this checkout's helper directory to LEAN_PATH, supplies lean--root for each export, and retains complete stdout/stderr per command. It stops on a failing cache/build/export command. No lakeupdate, credentials, environment-secret reads, network clients, or git/gh writes occur in the script.

The script invokes the Mathlib cache fetch before builds, and the README explicitly distinguishes a future complete rebuild from the successful individual session commands. The final axiom query is read-only and records the standard propext/Classical.choice/Quot.sound dependency result. The README correctly identifies the14gate theorem as an auxiliary25-row monotone result and flags the nonpermitted final imports/need for a separate single-file submission assembly.

Files reviewed: rebuild-auxiliary14.sh, REBUILD-auxiliary14.md, auxiliary14-dependencies.json and auxiliary14-rebuild-static.json. The exact source hashes checked are recorded in auxiliary14-independent-static.json. No forbidden credential material was found. This review does not certify the root repository target statement or an upstream PR.
