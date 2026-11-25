# Independent theta-four adapter review

Approved: the adapter only adds the ten-input scenario and its supplied sample/orbit data to the audited global encoder. The generic gate, output, sensitivity and prefix-cover encodings are unchanged. The fixed baseline uses eleven successive joins of the twelve edge-singleton signatures.

Independent finite checks passed:

- The twelve positive edges are exactly the incidences induced by the specified ten global coordinates. All468global negative rows project to63distinct local masks; their maximal elements are exactly the19 supplied negative masks.
- Initial free meets give22nonempty signatures and207incomparable unordered pairs. The48 supplied coordinate permutations form a group and preserve every positive and maximal negative sample. They give exactly the18 stored first-OR orbits.
- Direct replay of the saved eleven-OR witness covered all1,024local assignments:910are forced positive,86forced negative, and28unconstrained. All required values passed. Every distinct global negative projection is rejected.
- Independent sensitivity counts reproduce bounds4,5,7 with multiplicities12,6,1 respectively.

The local symmetry need only preserve the local finite constraints; it need not extend to a global plane automorphism. A successful ten-OR local witness would still need Lean verification before use in a global refutation. No ten-OR solver run or Lean compilation was performed during this review.

Exact source/data hashes, reproducible checks and complete output are archived as `audit_theta4_adapter.py` and `theta4-adapter-independent-audit.{json,log}`.
