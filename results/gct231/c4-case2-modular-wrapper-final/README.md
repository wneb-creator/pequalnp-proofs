# Bounded compact case2 norm-wrapper attempt

Final source SHA2566722a2c90af9d76cfb4259462a650a751b8777cc65a3db2be94aef0552beed67 (28,217bytes) did not finish checking: UNKNOWN_TIME_LIMIT after90.468s, peak4,118,516KiB under90s/5GiB. It has no observed Lean error before termination, but is UNCHECKED and must not replace the earlier checked201KiB norm theorem. No further run was attempted before the final deadline.

The final version rewrites the generic coefficient-list map/evaluation lemmas and changes to an explicit scalar Horner expression, then uses the original norm factorization. Its direct modular coprimality prerequisites are separately fully checked in ../c4-case2-modular-coprime-checked/, with independent review in ../case2-p11-review/. The generic modular resultant transfer is also separately checked. These components do not establish a full chart or gap result without the missing wrapper/necessity bridges.

The previous16384-recursion simp variant is preserved as Failed03 and complete build03 diagnostics; it also timed out90s. All stdout/stderr and resource metadata are retained. No binaries or credentials are included. The frozen named proof was not edited.
