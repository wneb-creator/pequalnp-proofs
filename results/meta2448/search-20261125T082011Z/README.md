# Reviewed sensitivity/count controls and bounded seed repair

The v11/v12/v13 family adds full downstream shadow replay for operand bypass and false/true substitutions, tested at the earliest original exact target prefix. The mathematical necessity is for a global minimum nonconstant exact graph function, using symbolic constant propagation; it is not a claim about minima within a nonstar-only class. Independent model, polarity, count-DP and launch reviews are included.

Actual controls: P4nonstar5, C5star7 padded to8slots, and Petersenstar20 all pass complete truth/prefix/ownership replay and every saved substitution witness. Petersen20 uses6AND+14OR. v13 upgrades only Petersen's guardedAND lowerbound to6 via accepted635 plus the count-preserving collapse; it does not require exactly6AND or exactly13OR. The live Petersen19 search is intentionally excluded.

The accepted L584 seed has20gates with7AND+13OR. All430 direct aliases/constants fail to preserve it. A subsequent restricted two-edit search exhausts2,078,136 rewires across387 normalized bases in4.044seconds, finding no witness. It normalizes/dead-prunes the deletion BEFORE changing a surviving gate, so it does not cover all possible two-edit repairs. Complete counts, normalized bases, scripts/logs and independent source review are preserved.

CNF files are stored as lossless gzip. ORIGINAL-FILES.json records both original and compressed hashes/sizes; every decompressed SHA256 was verified against the original file. Complete stdout/stderr logs are stored uncompressed. No proof/cache artifact was deleted. The correction note records the already accepted13gate lower/upper bound for the smaller core. No full L-meta-2448 proof or refutation is claimed.
