# Native run archive/status review

Reviewer: global_normal_form, 2026-11-25 UTC. Verdict: PASS for archival
integrity, input correspondence, and the stated diagnostic scope. No solver
was rerun and no archive was changed.

`native-star-r1` has exactly six manifest-covered files. Every hash matches
manifest SHA256
`9cc0437d52990f4ec3c89b54af1b0446e43bb4a769af671c3d7ba3dc01cd848d`.
The run is UNKNOWN_TIME_LIMIT after 600.295324475 seconds, with peak child RSS
2,357,776 KiB. The complete log has exactly nine completed pair rounds and
an unfinished degree-six round selecting 4,111 pairs. There is no basis file
or mathematical verdict. The stated two-thread, 6-GiB and 1,202-second CPU
limits match the metadata and runner. The note correctly calls this a
finite-field diagnostic, not a characteristic-zero or Lean result.

`native-b32-control` has exactly ten manifest-covered files. Every hash
matches manifest SHA256
`fd8d9740378f3a99aafa8495ccfb0b55616b95192bf9beda2b7cf939abbb09f9`.
It records exit zero and exactly the basis [1] over F1009 in
0.03395626999918022 seconds. The log has fifteen completed pair-processing
rounds and final basis reduction; selections of both 32 and 33 appear.
The upstream `symbol.c` explicitly permits additional selections sharing
the boundary LCM, so the parameter is not a strict per-round count cap.

An independent parser checked all 31 source polynomials and 655 sparse terms
of the control input. Every source/metadata hash matches, the variable order
is preserved, and each actual sparse polynomial equals the stated primitive
rescaling modulo 1009. All denominator/content scalings are invertible.
The unit result concerns the already known nine-variable star-support
control only; it is not a result for the full chart or posted gap.

Reviewer source and complete output are `check.py` and `check.log`.
