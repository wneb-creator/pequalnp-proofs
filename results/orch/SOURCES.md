Original complete proof: jfsantoropereira, PR #6642, https://github.com/open-goat/pequalnp-proofs/pull/6642 at commit 353cbde7203e3b9e6ce35d7bb9577a318422ec51.

This job adapts comments and modulo spacing to the current plain-file guard; no mathematical changes before validation. Original proof itself credits live-wire extraction/restriction machinery from L-meta-1667.

Final candidate framework and certificate adapted from zakpgrove, PR10495, head 8397d94eefc6d8e9aef2a184fe946911f2104d1b: https://github.com/open-goat/pequalnp-proofs/pull/10495 . Existing attribution in that source is retained. Our changes separate each certificate state and its conjunctive conditions into individual kernel obligations, replacing grouped checks. Archived rank_not_prefix.lean and Alt10495Prefix.lean are identical; the second filename supports diagnostic imports.

Variant K incorporates zakpgrove PR10495 head 570ca4aa3bd1085ad0944150ae27a1f236c276bb, adding the proved ColorBits and PackedRows evaluators while preserving the certificate. Our split-state and split-conjunction proof organization is retained.
