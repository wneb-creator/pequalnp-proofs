# Checked partial checkpoints

The full posted theorem is not proved. These commits preserve the source and its compilation context.
Some scratch extensions duplicate names later integrated into the named file; reproduce their check at the listed commit, rather than compiling every historical extension against the latest target.

| Commit | Checked component |
| --- | --- |
| eab1f92a | ReplaceLast |
| 63667304 | SensitivityMask |
| 5d1aeae1 | Named binaryFloor16 |
| 57319de2 | BinaryFloor17Extension against named floor16 |
| bdf53642 | AntiDiagonal restricted circuit; computational search archive |
| 39fe64ae | EffectiveReads |
| 52832c52 | Named binaryFloor17; SensitivityExtension |

BinaryFloor18NonOrExtension is checked against the named floor17 in52832c52; it does not cover first OR gates.

| f668c02d | Checked firstnonOR18binary extension against namedfloor17 |

SecondGate and PrefixReplay compiled against namedfloor17; currentpreservationcommit stores their logs. SharedOrThird and BinaryFloor18Compact are UNCHECKED drafts, never a full-gapclaim.
