Fresh mono18 first-OR-edge computational completion (strong mono16)

The reviewed proof exporter started from all ten original Petersen inputs plus OR(input0,input1), remaining budget17, with no imported memo. It returned finished found=0 and exit0 after 29449 visits, with1534 completed states and53839 subtree cuts. Reported total wall time was2.857seconds. This is one normalized first-gate case of the18-gate monotone problem, not the19-gate case, all first-gate classes or the posted gap.

Exact mode is strong mono16; command.json records whether mono-nine15 was enabled. Fixed matrix versionV3 is preserved; later V4/V5 matrices were not used. The source is byte-identical to the independently reviewed exporter b66739a56db722c470d02767c15b3e812f727546268d706df4a14c4442e8c021. Proof mode forbids imported memo data. Full proof/rectangle/bank traces, footer dictionaries, completed memo and all stdout/stderr are preserved with original and compressed hashes.

The search record contains gate histories, count-vector closure data, explicit pruning witnesses and child/memo references. Its finite replay, all cut instances and complete Lean search theorem still need kernel verification. This archive is a completed computational run, not a Lean certificate or proof of L-meta-2373. Independent whole-run audit is requested separately.
