# Independent polynomial-bridge and orbit-table review

Both frozen sources pass mathematical and helper-file format review. Their successful Lean compiles were reported by the root agent; I did not duplicate those compiles while the single-build rule was active.

`PolyBridge.lean` SHA256:

    e50d1473a9d4528e2c36039a86cb23ea569d56081bc574ff3304804dcfc2252a

The entry polynomial is exactly `1 + Σ A[k,i,j] X[k]`. Evaluation produces the claimed affine entry. The permanent is a finite sum of finite products, so evaluation commutes with it. `MvPolynomial.funext` over the infinite field of complex numbers correctly converts equality at every evaluation into formal polynomial equality with the constant 24. No symmetry or rank assumption is needed for this general bridge, and none is smuggled into the statement.

`EdgeOrbitsTable.lean` SHA256:

    c3ddd441498587ace5f3e636d6ee7e9dd31acfa231af71dcac061b3bbe0d1680

The independent Python reviewer parses the actual frozen Lean source rather than regenerating a separate witness table. It checks all 24 vertex permutations, all six coordinate permutations, all 216 table entries' index bounds, and the three mapped edges for every one of the 120 injective ordered triples. Every check passes. The ordered-triple counts are 24 stars, 24 triangles, and 72 paths. The theorem only uses the table on pairwise-distinct triples, so default entries on the other 96 triples are irrelevant.

The transfer from an arbitrary injective `pick` to its three-entry vector is sound, as are the coordinate permutation direction and the unordered-endpoint convention. The canonical edge sets are exactly (01,02,03), (01,02,12), and (01,12,23).

The reviewer source and full output are:

    /tmp/oec/pequalnp-pilot-75/gct231/lean/independent_table_review.py
    /tmp/oec/pequalnp-pilot-75/gct231/lean/independent_table_review.log

Both Lean sources place imports first and all declarations inside the auxiliary namespace. They contain no admitted proofs, extra axioms, custom instances, or executable commands. The table's finite checks use ordinary `decide`, and its noncomputable permutation definitions only package explicit bijective maps. Both sources are helper material, not standalone submissions proving the posted target.

The later `PolyLinearBridge.lean` additions also pass source review. `linear_map_coordinate_expansion` is the standard expansion in the three `Pi.single` coordinate vectors followed by linearity. `linear_map_polynomial_permanent_identity` specializes the reviewed polynomial bridge to those three generator images; the final commutative multiplication simplification aligns the coefficient order correctly. The root agent reported a successful build of this source; no duplicate compile was needed.

The integrated 506-line, 23810-byte named file was independently checked at SHA256 `449df515d9a915699114a3680c21d9de5b4cbcf8e823143374ad52724ff48227`. Its prefix before `edgeEnds` matches commit `4969a2b744e4146b34b7acecdb6b6a9b9c975ccc` byte-for-byte. The exact reviewed orbit-table body, parameterization additions, and polynomial-bridge body each occur once, unchanged and in order. Allowed imports, namespace containment, helper format, and absence of a posted main theorem were checked. It remains partial helper work, not a proof of the requested existence theorem.

The integration reviewer and full output are `/tmp/oec/pequalnp-pilot-75/gct231/lean/integration_review.py` and `integration_review.log`; the recorded review time is 2026-11-25 10:16:02 UTC.
