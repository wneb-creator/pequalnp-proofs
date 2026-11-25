# Compact monomial-input trace review

Independent source and exact-control review: PASS for the frozen hashes printed
in `check.log`. The C change records an earlier output node and a nonnegative
monomial exponent shift instead of serializing a repeated matrix-input
polynomial. Coefficient-array keys track the prior output and its leading
exponents; rows with no tracked prior output retain the original full input
record. The generated overlay remains separate from validated engine trees.

The replay accepts an M record only when its referenced node is an already
verified output and its shift has the correct dimension and nonnegative
coordinates. It reconstructs that exact monomial multiple and retains all
previous exact output-identity checks. Thus the CAS's basis claim is not
trusted: every accepted output remains an explicit QQ polynomial consequence
of the original generators. A wrong C-side reference would cause replay
failure unless the resulting exact identity still proves the output.

The independent checker compared every compact M record with the corresponding
actual input polynomial in the previous uncompressed trace, using a separate
SymPy exact-polynomial reconstruction. All 154 M records across the unit,
nonunit, rational, and rowzero controls match. Every serialized certificate
step was also recomputed independently from its generator or earlier-parent
combination over QQ. All controls pass; unit and rowzero controls establish
nonzero constants, while the other two do not claim one.

The unchanged output polynomial sequences and exact identities validate the
compact metadata on these controls. Parent decompositions need not match the
old trace: a normalized earlier output can replace a scalar-equivalent earlier
generator. This changes certificate size, not its mathematical validity.

The bounded runner preserves complete stdout/stderr and has explicit wall,
address-space, and output-file limits, with core dumps disabled. Exceeding a
limit is UNKNOWN or FAILED_NO_VERDICT. This review does not claim a result for
any full chart and does not rerun a heavy CAS or Lean build.
