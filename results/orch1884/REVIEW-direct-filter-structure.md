UTC: 2026-11-25T17:05:00.335433+00:00

Independent semantic/provenance review: PASS. DirectFilterStructure SHA25687167501ccac988e2e0c3e3ea14471c36467f24f3cee9b0c41dc723a301f8107 and NoPositiveRailCore SHAc765ba6de87ed00e4178ec96157166a8b240871962cd5a7db47f759ec5dcf3e2 match the reported stable checked versions. No new build was run.

DirectFilterStructure.soleAfter explicitly requires a canonical AND[v,q] at one suffix list position, q=11+prefix length, with every other suffix gate omitting rawv. facts combines already reviewed fiber monotonicity, prefix/operand rawv independence, and actual sole-reader factorization. The prefix omission, NOT-list omission, output exclusion, nonzero-v and full computation premises are all explicit. The two suffix omission obligations follow from the exact split; rewriting only reassociates the existing circuit lists. No unproved structural extraction occurs.

NoPositiveRailCore is the byte-identical complete NoPositiveRail namespace from the reviewed root source, with only dependency imports replacing the large copied prefix. No statement/proof-term changes occur. The underlying proof review is REVIEW-no-positive-rail.md.

Both sources contain no prohibited root text, string literals, attributes, options, admitted proofs, new axioms or native decision procedure. These are local dependency helpers, not final permitted-import assemblies or complete posted-goal proofs.
