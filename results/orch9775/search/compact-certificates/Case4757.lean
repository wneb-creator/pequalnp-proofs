import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a4757 : Array Fact := #[(.res 0 3),(.res 1 3),(.res 2 3),(.res 0 5),(.res 1 5),(.res 2 5),(.res 0 6),(.res 1 6),(.res 2 6),(.res 0 8),(.res 1 8),(.res 2 8),(.res 0 10),(.res 1 10),(.res 2 10),(.res 0 13),(.res 1 13),(.res 2 13),(.lab 1 0 1),(.lab 1 1 1),(.lab 1 2 1),(.lab 1 3 1),(.lab 1 4 1),(.lab 2 0 2),(.lab 2 0 1),(.avoid 2 314 0),(.live 3 1),(.lab 3 0 1),(.lab 3 0 5),(.lab 3 0 8),(.common 3 8),(.lab 3 0 10),(.common 3 10),(.common 3 13),(.live 3 2),(.lab 3 1 1),(.lab 3 1 5),(.lab 3 1 8),(.lab 3 1 10),(.live 3 3),(.lab 3 2 1),(.lab 3 2 5),(.lab 3 2 8),(.lab 3 2 10),(.live 3 4),(.lab 3 3 1),(.lab 3 3 8),(.lab 3 3 10),(.avoid 3 2087 0),(.avoid 3 2087 1),(.avoid 3 2087 2),(.avoid 3 2087 3),(.avoid 3 2087 4),(.avoid 3 2338 0),(.avoid 3 2338 1),(.avoid 3 2338 2),(.avoid 3 2338 3),(.avoid 3 2338 4),(.avoid 3 5190 0),(.avoid 3 5190 1),(.avoid 3 5190 2),(.avoid 3 5190 3),(.avoid 3 5190 4),(.avoid 3 7426 0),(.avoid 3 7426 1),(.avoid 3 7426 2),(.avoid 3 7426 3),(.avoid 3 7426 4),(.see 3 7 127 0),(.see 3 7 127 1),(.see 3 7 127 2),(.see 3 7 127 3),(.see 3 7 127 4),(.see 3 7 314 0),(.see 3 7 314 1),(.see 3 7 314 2),(.see 3 7 314 3),(.see 3 7 314 4),(.see 3 7 1102 0),(.see 3 7 1102 1),(.see 3 7 1102 2),(.see 3 7 1102 3),(.see 3 7 1102 4),(.see 3 12 127 0),(.see 3 12 127 1),(.see 3 12 127 2),(.see 3 12 127 3),(.see 3 12 127 4),(.see 3 12 1290 0),(.see 3 12 1290 1),(.see 3 12 1290 2),(.see 3 12 1290 3),(.see 3 12 1290 4),(.see 3 12 8488 0),(.see 3 12 8488 1),(.see 3 12 8488 2),(.see 3 12 8488 3),(.see 3 12 8488 4),(.diff 0 3 8),(.diff 1 3 8),(.diff 2 3 8),(.diff 0 3 10),(.diff 1 3 10),(.diff 2 3 10),(.lab 4 0 1),(.lab 4 0 2),(.avoid 4 1102 0),(.live 5 1),(.lab 5 0 1),(.lab 5 0 3),(.lab 5 0 6),(.common 5 6),(.lab 5 0 10),(.common 5 10),(.live 5 2),(.lab 5 1 1),(.lab 5 1 3),(.lab 5 1 6),(.lab 5 1 10),(.live 5 3),(.lab 5 2 1),(.lab 5 2 3),(.lab 5 2 6),(.lab 5 2 10),(.live 5 4),(.lab 5 3 1),(.lab 5 3 3),(.lab 5 3 6),(.lab 5 3 10),(.lab 5 4 1),(.lab 5 4 3),(.lab 5 4 6),(.lab 5 4 10),(.avoid 5 1102 0),(.avoid 5 1102 1),(.avoid 5 1102 2),(.avoid 5 1102 3),(.avoid 5 1102 4),(.avoid 5 1290 0),(.avoid 5 1290 1),(.avoid 5 1290 2),(.avoid 5 1290 3),(.avoid 5 1290 4),(.see 5 9 314 0),(.see 5 9 314 1),(.see 5 9 314 2),(.see 5 9 314 3),(.see 5 9 314 4),(.see 5 12 127 0),(.see 5 12 127 1),(.see 5 12 127 2),(.see 5 12 127 3),(.see 5 12 127 4),(.diff 0 5 6),(.diff 1 5 6),(.diff 2 5 6),(.diff 0 5 10),(.diff 1 5 10),(.diff 2 5 10),(.lab 6 0 6),(.live 6 1),(.lab 6 0 1),(.lab 6 0 10),(.common 6 10),(.lab 6 1 6),(.live 6 2),(.lab 6 1 1),(.lab 6 1 10),(.lab 6 2 6),(.live 6 3),(.lab 6 2 1),(.lab 6 2 10),(.lab 6 3 6),(.live 6 4),(.lab 6 3 1),(.lab 6 3 10),(.avoid 6 314 0),(.avoid 6 314 1),(.avoid 6 314 2),(.avoid 6 314 3),(.avoid 6 314 4),(.avoid 6 1290 0),(.avoid 6 1290 1),(.avoid 6 1290 2),(.avoid 6 1290 3),(.avoid 6 1290 4),(.see 6 9 1102 0),(.see 6 9 1102 1),(.see 6 9 1102 2),(.see 6 9 1102 3),(.see 6 9 1102 4),(.see 6 9 5190 0),(.see 6 9 5190 1),(.see 6 9 5190 2),(.see 6 9 5190 3),(.see 6 9 5190 4),(.diff 0 6 10),(.diff 1 6 10),(.diff 2 6 10),(.live 8 1),(.lab 8 0 10),(.common 8 10),(.lab 8 0 13),(.common 8 13),(.live 8 2),(.lab 8 1 10),(.lab 8 1 13),(.live 8 3),(.lab 8 2 10),(.lab 8 2 13),(.live 8 4),(.lab 8 3 10),(.lab 8 3 13),(.avoid 8 9288 0),(.avoid 8 9288 1),(.avoid 8 9288 2),(.avoid 8 9288 3),(.avoid 8 9288 4),(.see 8 0 1290 0),(.see 8 0 1290 1),(.see 8 0 1290 2),(.see 8 0 1290 3),(.see 8 0 1290 4),(.see 8 0 9992 0),(.see 8 0 9992 1),(.see 8 0 9992 2),(.see 8 0 9992 3),(.see 8 0 9992 4),(.see 8 2 9992 0),(.see 8 2 9992 1),(.see 8 2 9992 2),(.see 8 2 9992 3),(.see 8 2 9992 4),(.diff 0 8 10),(.diff 1 8 10),(.diff 2 8 10),(.diff 0 8 13),(.diff 1 8 13),(.diff 2 8 13),(.live 10 1),(.lab 10 0 3),(.lab 10 0 8),(.lab 10 0 13),(.common 10 13),(.live 10 2),(.lab 10 1 3),(.lab 10 1 8),(.lab 10 1 13),(.live 10 3),(.lab 10 2 3),(.lab 10 2 8),(.lab 10 2 13),(.live 10 4),(.lab 10 3 3),(.lab 10 3 8),(.lab 10 3 13),(.avoid 10 8488 0),(.avoid 10 8488 1),(.avoid 10 8488 2),(.avoid 10 8488 3),(.avoid 10 8488 4),(.avoid 10 10656 0),(.avoid 10 10656 1),(.avoid 10 10656 2),(.avoid 10 10656 3),(.avoid 10 10656 4),(.see 10 0 1290 0),(.see 10 0 1290 1),(.see 10 0 1290 2),(.see 10 0 1290 3),(.see 10 0 1290 4),(.see 10 0 9992 0),(.see 10 0 9992 1),(.see 10 0 9992 2),(.see 10 0 9992 3),(.see 10 0 9992 4),(.see 10 4 9992 0),(.see 10 4 9992 1),(.see 10 4 9992 2),(.see 10 4 9992 3),(.see 10 4 9992 4),(.diff 0 10 3),(.diff 1 10 3),(.diff 2 10 3),(.diff 0 10 8),(.diff 1 10 8),(.diff 2 10 8),(.diff 0 10 13),(.diff 1 10 13),(.diff 2 10 13),(.live 13 1),(.lab 13 0 3),(.lab 13 0 8),(.lab 13 0 10),(.live 13 2),(.lab 13 1 3),(.lab 13 1 8),(.lab 13 1 10),(.live 13 3),(.lab 13 2 3),(.lab 13 2 8),(.lab 13 2 10),(.live 13 4),(.lab 13 3 3),(.lab 13 3 8),(.lab 13 3 10),(.avoid 13 1290 0),(.avoid 13 1290 1),(.avoid 13 1290 2),(.avoid 13 1290 3),(.avoid 13 1290 4),(.see 13 2 8488 0),(.see 13 2 8488 1),(.see 13 2 8488 2),(.see 13 2 8488 3),(.see 13 2 8488 4),(.see 13 2 9992 0),(.see 13 2 9992 1),(.see 13 2 9992 2),(.see 13 2 9992 3),(.see 13 2 9992 4),(.see 13 4 9992 0),(.see 13 4 9992 1),(.see 13 4 9992 2),(.see 13 4 9992 3),(.see 13 4 9992 4),(.diff 0 13 3),(.diff 1 13 3),(.diff 2 13 3),(.diff 0 13 8),(.diff 1 13 8),(.diff 2 13 8),(.diff 0 13 10),(.diff 1 13 10),(.diff 2 13 10),(.reader false 3 0),(.reader false 3 1),(.reader false 3 2),(.reader false 3 3),(.reader false 3 4),(.es false 3 1),(.reader false 4 0),(.reader false 4 1),(.reader false 4 2),(.reader false 4 3),(.reader false 4 4),(.es false 4 1),(.reader false 6 0),(.es false 6 1),(.es false 6 2),(.reader false 12 0),(.es false 12 1),(.es false 12 2),(.reader false 13 0),(.reader false 13 1),(.reader false 13 2),(.reader false 13 3),(.reader false 13 4),(.es false 13 1),(.es false 13 6),(.es false 13 10),(.reader false 17 0),(.reader false 17 1),(.reader false 17 2),(.reader false 17 3),(.reader false 17 4),(.es false 17 1),(.es false 17 6),(.es false 17 10),(.reader true 3 0),(.reader true 4 0),(.reader true 4 1),(.reader true 4 2),(.reader true 4 3),(.reader true 4 4),(.reader true 6 0),(.reader true 6 1),(.reader true 6 2),(.reader true 6 3),(.reader true 6 4),(.reader true 12 0),(.reader true 12 1),(.reader true 12 2),(.reader true 12 3),(.reader true 12 4),(.reader true 13 0),(.reader true 17 0),(.gate 3 13),(.gate 3 17),(.gate 4 6),(.gate 4 12),(.gate 6 12),(.gate 13 17)]
def r4757 : List Scheme := [(.self 1 0),(.self 1 1),(.self 1 2),(.self 1 3),(.self 1 4),(.self 2 0),(.exposure 2 314),(.avoidNot 2 1 314 0),(.earlier 3 1),(.earlier 3 2),(.someRes 3),(.allRes 3 0),(.allRes 3 1),(.allRes 3 2),(.exposure 3 2087),(.avoidNot 3 1 2087 0),(.avoidNot 3 5 2087 0),(.avoidNot 3 1 2087 1),(.avoidNot 3 5 2087 1),(.avoidLive 3 2087 2),(.avoidLive 3 2087 3),(.avoidLive 3 2087 4),(.exposure 3 2338),(.avoidNot 3 8 2338 0),(.avoidNot 3 1 2338 1),(.avoidNot 3 5 2338 1),(.avoidNot 3 8 2338 2),(.avoidLive 3 2338 3),(.avoidNot 3 8 2338 3),(.avoidLive 3 2338 4),(.exposure 3 5190),(.avoidNot 3 1 5190 0),(.avoidNot 3 10 5190 0),(.avoidNot 3 1 5190 1),(.avoidNot 3 10 5190 1),(.avoidNot 3 1 5190 2),(.avoidNot 3 10 5190 2),(.avoidLive 3 5190 3),(.avoidNot 3 10 5190 3),(.avoidLive 3 5190 4),(.exposure 3 7426),(.avoidNot 3 8 7426 0),(.avoidNot 3 8 7426 1),(.avoidNot 3 8 7426 2),(.avoidNot 3 1 7426 3),(.avoidLive 3 7426 4),(.exactAt 3 7 127),(.seeLab 3 7 1 127 0),(.seeLab 3 7 1 127 1),(.seeLab 3 7 5 127 1),(.seeLive 3 7 127 2),(.seeLive 3 7 127 3),(.seeLive 3 7 127 4),(.exactAt 3 7 314),(.seeLab 3 7 5 314 0),(.seeLab 3 7 8 314 0),(.seeLab 3 7 1 314 1),(.seeLab 3 7 8 314 1),(.seeLab 3 7 5 314 2),(.seeLab 3 7 8 314 2),(.seeLive 3 7 314 3),(.seeLab 3 7 1 314 3),(.seeLab 3 7 8 314 3),(.seeLive 3 7 314 4),(.exactAt 3 7 1102),(.seeLab 3 7 1 1102 0),(.seeLab 3 7 10 1102 0),(.seeLab 3 7 1 1102 1),(.seeLab 3 7 10 1102 1),(.seeLab 3 7 1 1102 2),(.seeLab 3 7 10 1102 2),(.seeLive 3 7 1102 3),(.seeLab 3 7 1 1102 3),(.seeLab 3 7 10 1102 3),(.seeLive 3 7 1102 4),(.exactAt 3 12 127),(.seeLab 3 12 1 127 0),(.seeLab 3 12 5 127 0),(.seeLab 3 12 5 127 1),(.seeLive 3 12 127 2),(.seeLive 3 12 127 3),(.seeLive 3 12 127 4),(.exactAt 3 12 1290),(.seeLab 3 12 10 1290 0),(.seeLab 3 12 10 1290 1),(.seeLab 3 12 10 1290 2),(.seeLab 3 12 1 1290 3),(.seeLive 3 12 1290 4),(.exactAt 3 12 8488),(.seeLab 3 12 5 8488 0),(.seeLab 3 12 8 8488 0),(.seeLab 3 12 5 8488 1),(.seeLab 3 12 8 8488 1),(.seeLab 3 12 5 8488 2),(.seeLab 3 12 8 8488 2),(.seeLive 3 12 8488 3),(.seeLab 3 12 8 8488 3),(.seeLive 3 12 8488 4),(.diffX 0 3 8),(.diffC 0 3 8),(.resCommon 3 8 0),(.diffX 1 3 8),(.diffC 1 3 8),(.resCommon 3 8 1),(.diffX 2 3 8),(.diffC 2 3 8),(.resCommon 3 8 2),(.residual 3 8 0 1),(.residual 3 8 0 2),(.residual 3 8 0 3),(.residual 3 8 1 2),(.residual 3 8 1 3),(.residual 3 8 2 3),(.diffX 0 3 10),(.diffC 0 3 10),(.resCommon 3 10 0),(.diffX 1 3 10),(.diffC 1 3 10),(.resCommon 3 10 1),(.diffX 2 3 10),(.diffC 2 3 10),(.resCommon 3 10 2),(.residual 3 10 0 1),(.residual 3 10 0 2),(.residual 3 10 0 3),(.residual 3 10 1 2),(.residual 3 10 1 3),(.residual 3 10 2 3),(.resCommon 3 13 0),(.resCommon 3 13 1),(.resCommon 3 13 2),(.exposure 4 1102),(.avoidNot 4 1 1102 0),(.avoidNot 4 2 1102 0),(.earlier 5 1),(.earlier 5 2),(.earlier 5 3),(.someRes 5),(.allRes 5 0),(.exposure 5 1102),(.avoidNot 5 1 1102 0),(.avoidNot 5 3 1102 0),(.avoidNot 5 6 1102 0),(.avoidNot 5 10 1102 0),(.avoidLive 5 1102 1),(.avoidNot 5 1 1102 1),(.avoidNot 5 3 1102 1),(.avoidNot 5 6 1102 1),(.avoidNot 5 10 1102 1),(.avoidLive 5 1102 2),(.avoidNot 5 1 1102 2),(.avoidNot 5 3 1102 2),(.avoidNot 5 6 1102 2),(.avoidNot 5 10 1102 2),(.avoidLive 5 1102 3),(.avoidNot 5 1 1102 3),(.avoidNot 5 3 1102 3),(.avoidNot 5 6 1102 3),(.avoidNot 5 10 1102 3),(.avoidLive 5 1102 4),(.avoidNot 5 3 1102 4),(.avoidNot 5 6 1102 4),(.avoidNot 5 10 1102 4),(.exposure 5 1290),(.avoidNot 5 10 1290 0),(.avoidNot 5 10 1290 1),(.avoidNot 5 1 1290 2),(.avoidNot 5 10 1290 2),(.avoidLive 5 1290 3),(.avoidNot 5 10 1290 3),(.avoidLive 5 1290 4),(.avoidNot 5 1 1290 4),(.exactAt 5 9 314),(.seeLab 5 9 1 314 0),(.seeLab 5 9 1 314 1),(.seeLab 5 9 3 314 1),(.seeLive 5 9 314 2),(.seeLive 5 9 314 3),(.seeLive 5 9 314 4),(.exactAt 5 12 127),(.seeLab 5 12 1 127 0),(.seeLab 5 12 3 127 0),(.seeLab 5 12 6 127 0),(.seeLive 5 12 127 1),(.seeLab 5 12 3 127 1),(.seeLab 5 12 6 127 1),(.seeLive 5 12 127 2),(.seeLab 5 12 3 127 2),(.seeLab 5 12 6 127 2),(.seeLive 5 12 127 3),(.seeLab 5 12 3 127 3),(.seeLab 5 12 6 127 3),(.seeLive 5 12 127 4),(.seeLab 5 12 3 127 4),(.seeLab 5 12 6 127 4),(.diffC 0 5 6),(.diffC 1 5 6),(.diffC 2 5 6),(.adjacentCommon 5 6 9),(.residual 5 6 0 1),(.residual 5 6 0 2),(.residual 5 6 0 3),(.residual 5 6 0 4),(.residual 5 6 1 2),(.residual 5 6 1 3),(.residual 5 6 1 4),(.residual 5 6 2 3),(.residual 5 6 2 4),(.residual 5 6 3 4),(.diffC 0 5 10),(.resCommon 5 10 0),(.diffC 1 5 10),(.resCommon 5 10 1),(.diffC 2 5 10),(.resCommon 5 10 2),(.residual 5 10 0 1),(.residual 5 10 0 2),(.residual 5 10 0 3),(.residual 5 10 0 4),(.residual 5 10 1 2),(.residual 5 10 1 3),(.residual 5 10 1 4),(.residual 5 10 2 3),(.residual 5 10 2 4),(.residual 5 10 3 4),(.self 6 0),(.self 6 1),(.earlier 6 1),(.self 6 2),(.earlier 6 2),(.self 6 3),(.someRes 6),(.allRes 6 0),(.allRes 6 1),(.allRes 6 2),(.exposure 6 314),(.avoidNot 6 1 314 0),(.avoidNot 6 1 314 1),(.avoidLive 6 314 2),(.avoidLive 6 314 3),(.avoidLive 6 314 4),(.exposure 6 1290),(.avoidNot 6 1 1290 0),(.avoidNot 6 10 1290 0),(.avoidNot 6 1 1290 1),(.avoidNot 6 10 1290 1),(.avoidNot 6 1 1290 2),(.avoidNot 6 10 1290 2),(.avoidLive 6 1290 3),(.avoidNot 6 1 1290 3),(.avoidNot 6 10 1290 3),(.avoidLive 6 1290 4),(.exactAt 6 9 1102),(.seeLab 6 9 1 1102 0),(.seeLab 6 9 10 1102 0),(.seeLab 6 9 1 1102 1),(.seeLab 6 9 10 1102 1),(.seeLive 6 9 1102 2),(.seeLab 6 9 1 1102 2),(.seeLab 6 9 10 1102 2),(.seeLive 6 9 1102 3),(.seeLab 6 9 1 1102 3),(.seeLab 6 9 10 1102 3),(.seeLive 6 9 1102 4),(.exactAt 6 9 5190),(.seeLab 6 9 10 5190 0),(.seeLab 6 9 10 5190 1),(.seeLab 6 9 1 5190 2),(.seeLive 6 9 5190 3),(.seeLive 6 9 5190 4),(.diffX 0 6 10),(.diffC 0 6 10),(.resCommon 6 10 0),(.diffC 1 6 10),(.resCommon 6 10 1),(.diffC 2 6 10),(.resCommon 6 10 2),(.residual 6 10 0 1),(.residual 6 10 0 2),(.residual 6 10 0 3),(.residual 6 10 1 2),(.residual 6 10 1 3),(.residual 6 10 2 3),(.earlier 8 1),(.earlier 8 2),(.allRes 8 0),(.allRes 8 1),(.allRes 8 2),(.exposure 8 9288),(.avoidNot 8 10 9288 0),(.avoidNot 8 13 9288 0),(.avoidNot 8 10 9288 1),(.avoidNot 8 13 9288 1),(.avoidLive 8 9288 2),(.avoidNot 8 10 9288 2),(.avoidNot 8 13 9288 2),(.avoidLive 8 9288 3),(.avoidNot 8 10 9288 3),(.avoidNot 8 13 9288 3),(.avoidLive 8 9288 4),(.exactAt 8 0 1290),(.seeLab 8 0 10 1290 0),(.seeLab 8 0 10 1290 1),(.seeLive 8 0 1290 2),(.seeLive 8 0 1290 3),(.seeLive 8 0 1290 4),(.exactAt 8 0 9992),(.seeLab 8 0 10 9992 0),(.seeLab 8 0 13 9992 0),(.seeLab 8 0 10 9992 1),(.seeLab 8 0 13 9992 1),(.seeLab 8 0 10 9992 2),(.seeLab 8 0 13 9992 2),(.seeLive 8 0 9992 3),(.seeLab 8 0 10 9992 3),(.seeLab 8 0 13 9992 3),(.seeLive 8 0 9992 4),(.exactAt 8 2 9992),(.seeLab 8 2 10 9992 0),(.seeLab 8 2 13 9992 0),(.seeLab 8 2 10 9992 1),(.seeLab 8 2 13 9992 1),(.seeLive 8 2 9992 2),(.seeLab 8 2 10 9992 2),(.seeLab 8 2 13 9992 2),(.seeLive 8 2 9992 3),(.seeLab 8 2 10 9992 3),(.seeLab 8 2 13 9992 3),(.seeLive 8 2 9992 4),(.diffX 0 8 10),(.diffC 0 8 10),(.diffX 1 8 10),(.diffC 1 8 10),(.diffX 2 8 10),(.diffC 2 8 10),(.adjacentCommon 8 10 0),(.residual 8 10 0 1),(.residual 8 10 0 2),(.residual 8 10 0 3),(.residual 8 10 1 2),(.residual 8 10 1 3),(.residual 8 10 2 3),(.diffX 0 8 13),(.diffC 0 8 13),(.diffX 1 8 13),(.diffC 1 8 13),(.diffX 2 8 13),(.diffC 2 8 13),(.adjacentCommon 8 13 2),(.residual 8 13 0 1),(.residual 8 13 0 2),(.residual 8 13 0 3),(.residual 8 13 1 2),(.residual 8 13 1 3),(.residual 8 13 2 3),(.earlier 10 1),(.earlier 10 2),(.someRes 10),(.allRes 10 0),(.allRes 10 1),(.allRes 10 2),(.exposure 10 8488),(.avoidNot 10 3 8488 0),(.avoidNot 10 8 8488 0),(.avoidNot 10 13 8488 0),(.avoidLive 10 8488 1),(.avoidNot 10 3 8488 1),(.avoidNot 10 8 8488 1),(.avoidNot 10 13 8488 1),(.avoidLive 10 8488 2),(.avoidNot 10 3 8488 2),(.avoidNot 10 8 8488 2),(.avoidNot 10 13 8488 2),(.avoidLive 10 8488 3),(.avoidNot 10 8 8488 3),(.avoidNot 10 13 8488 3),(.avoidLive 10 8488 4),(.exposure 10 10656),(.avoidNot 10 8 10656 0),(.avoidNot 10 13 10656 1),(.avoidNot 10 8 10656 2),(.avoidNot 10 8 10656 3),(.avoidLive 10 10656 4),(.exactAt 10 0 1290),(.seeLab 10 0 3 1290 0),(.seeLab 10 0 8 1290 0),(.seeLab 10 0 3 1290 1),(.seeLab 10 0 8 1290 1),(.seeLive 10 0 1290 2),(.seeLab 10 0 3 1290 2),(.seeLive 10 0 1290 3),(.seeLab 10 0 3 1290 3),(.seeLive 10 0 1290 4),(.exactAt 10 0 9992),(.seeLab 10 0 3 9992 0),(.seeLab 10 0 8 9992 0),(.seeLab 10 0 13 9992 0),(.seeLab 10 0 3 9992 1),(.seeLab 10 0 8 9992 1),(.seeLab 10 0 13 9992 1),(.seeLab 10 0 8 9992 2),(.seeLab 10 0 13 9992 2),(.seeLive 10 0 9992 3),(.seeLab 10 0 8 9992 3),(.seeLab 10 0 13 9992 3),(.seeLive 10 0 9992 4),(.exactAt 10 4 9992),(.seeLab 10 4 3 9992 0),(.seeLab 10 4 8 9992 0),(.seeLab 10 4 13 9992 0),(.seeLive 10 4 9992 1),(.seeLab 10 4 3 9992 1),(.seeLab 10 4 8 9992 1),(.seeLab 10 4 13 9992 1),(.seeLive 10 4 9992 2),(.seeLab 10 4 3 9992 2),(.seeLab 10 4 8 9992 2),(.seeLab 10 4 13 9992 2),(.seeLive 10 4 9992 3),(.seeLab 10 4 8 9992 3),(.seeLab 10 4 13 9992 3),(.seeLive 10 4 9992 4),(.diffX 0 10 3),(.diffC 0 10 3),(.diffX 1 10 3),(.diffC 1 10 3),(.diffX 2 10 3),(.diffC 2 10 3),(.residual 10 3 0 1),(.residual 10 3 0 2),(.residual 10 3 0 3),(.residual 10 3 1 2),(.residual 10 3 1 3),(.diffX 0 10 8),(.diffC 0 10 8),(.diffX 1 10 8),(.diffC 1 10 8),(.diffX 2 10 8),(.diffC 2 10 8),(.residual 10 8 0 1),(.residual 10 8 0 2),(.residual 10 8 0 3),(.residual 10 8 1 2),(.residual 10 8 1 3),(.residual 10 8 2 3),(.diffX 0 10 13),(.diffC 0 10 13),(.diffX 1 10 13),(.diffC 1 10 13),(.diffX 2 10 13),(.diffC 2 10 13),(.adjacentCommon 10 13 4),(.residual 10 13 0 1),(.residual 10 13 0 2),(.residual 10 13 0 3),(.residual 10 13 1 2),(.residual 10 13 1 3),(.residual 10 13 2 3),(.earlier 13 1),(.earlier 13 2),(.someRes 13),(.allRes 13 0),(.allRes 13 1),(.allRes 13 2),(.exposure 13 1290),(.avoidNot 13 3 1290 0),(.avoidNot 13 8 1290 0),(.avoidNot 13 10 1290 0),(.avoidNot 13 3 1290 1),(.avoidNot 13 8 1290 1),(.avoidNot 13 10 1290 1),(.avoidNot 13 3 1290 2),(.avoidNot 13 8 1290 2),(.avoidNot 13 10 1290 2),(.avoidLive 13 1290 3),(.avoidNot 13 8 1290 3),(.avoidNot 13 10 1290 3),(.avoidLive 13 1290 4),(.exactAt 13 2 8488),(.seeLab 13 2 3 8488 0),(.seeLab 13 2 8 8488 0),(.seeLab 13 2 3 8488 1),(.seeLab 13 2 8 8488 1),(.seeLab 13 2 3 8488 2),(.seeLab 13 2 8 8488 2),(.seeLive 13 2 8488 3),(.seeLab 13 2 3 8488 3),(.seeLab 13 2 8 8488 3),(.seeLive 13 2 8488 4),(.exactAt 13 2 9992),(.seeLab 13 2 8 9992 0),(.seeLab 13 2 10 9992 0),(.seeLab 13 2 8 9992 1),(.seeLab 13 2 10 9992 1),(.seeLab 13 2 8 9992 2),(.seeLab 13 2 10 9992 2),(.seeLive 13 2 9992 3),(.seeLab 13 2 8 9992 3),(.seeLab 13 2 10 9992 3),(.seeLive 13 2 9992 4),(.exactAt 13 4 9992),(.seeLab 13 4 3 9992 0),(.seeLab 13 4 8 9992 0),(.seeLab 13 4 10 9992 0),(.seeLab 13 4 3 9992 1),(.seeLab 13 4 8 9992 1),(.seeLab 13 4 10 9992 1),(.seeLive 13 4 9992 2),(.seeLab 13 4 3 9992 2),(.seeLab 13 4 8 9992 2),(.seeLab 13 4 10 9992 2),(.seeLive 13 4 9992 3),(.seeLab 13 4 8 9992 3),(.seeLab 13 4 10 9992 3),(.seeLive 13 4 9992 4),(.diffX 0 13 3),(.diffC 0 13 3),(.diffX 1 13 3),(.diffC 1 13 3),(.diffX 2 13 3),(.diffC 2 13 3),(.residual 13 3 0 1),(.residual 13 3 0 2),(.residual 13 3 0 3),(.residual 13 3 1 2),(.residual 13 3 2 3),(.diffX 0 13 8),(.diffX 1 13 8),(.diffC 1 13 8),(.diffX 2 13 8),(.diffC 2 13 8),(.residual 13 8 0 1),(.residual 13 8 0 2),(.residual 13 8 0 3),(.residual 13 8 1 2),(.residual 13 8 1 3),(.residual 13 8 2 3),(.diffX 0 13 10),(.diffC 0 13 10),(.diffX 1 13 10),(.diffC 1 13 10),(.diffX 2 13 10),(.diffC 2 13 10),(.residual 13 10 0 1),(.residual 13 10 0 2),(.residual 13 10 0 3),(.residual 13 10 1 2),(.residual 13 10 1 3),(.residual 13 10 2 3),(.readerAny false 3),(.readerLab false 3 0 1 true),(.readerLab false 3 1 1 true),(.readerLab false 3 2 1 true),(.readerLab false 3 3 1 true),(.readerLab false 3 4 1 true),(.readerAny false 4),(.readerLab false 4 0 1 true),(.readerLab false 4 1 1 true),(.readerLab false 4 2 1 true),(.readerLab false 4 3 1 true),(.readerLab false 4 4 1 true),(.readerAny false 6),(.readerLab false 6 0 1 false),(.readerLab false 6 0 2 true),(.readerAny false 12),(.readerLab false 12 0 1 false),(.readerLab false 12 0 2 false),(.readerAny false 13),(.readerLab false 13 0 1 false),(.readerLab false 13 0 10 true),(.readerLab false 13 1 1 false),(.readerLab false 13 1 10 true),(.readerLab false 13 2 1 false),(.readerLab false 13 2 6 false),(.readerLab false 13 2 10 true),(.readerLive false 13 3),(.readerLab false 13 3 1 false),(.readerLab false 13 3 10 true),(.readerLive false 13 4),(.readerLab false 13 4 1 false),(.readerLab false 13 4 6 false),(.readerLab false 13 4 10 true),(.readerAny false 17),(.readerLab false 17 0 1 false),(.readerLab false 17 0 6 true),(.readerLab false 17 0 10 false),(.readerLab false 17 1 1 false),(.readerLab false 17 1 6 true),(.readerLab false 17 1 10 false),(.readerLive false 17 2),(.readerLab false 17 2 6 true),(.readerLive false 17 3),(.readerLab false 17 3 6 true),(.readerLive false 17 4),(.readerAny true 3),(.readerAny true 4),(.readerLive true 4 2),(.readerLive true 4 3),(.readerLive true 4 4),(.readerAny true 6),(.readerLive true 6 2),(.readerLive true 6 3),(.readerLive true 6 4),(.readerAny true 12),(.readerLive true 12 2),(.readerLive true 12 3),(.readerLive true 12 4),(.readerAny true 13),(.readerAny true 17),(.eqLab false 3 13 1 true),(.gateEq true 3 13 0),(.eqLab false 3 17 1 true),(.gateEq true 3 17 0),(.eqLab false 4 6 1 true),(.gateEq true 4 6 0),(.gateEq true 4 6 1),(.eqLab false 4 12 1 true),(.gateEq true 4 12 0),(.gateEq true 4 12 1),(.eqLab false 6 12 2 true),(.gateEq true 6 12 0),(.gateEq true 6 12 1),(.eqLab false 13 17 6 false),(.eqLab false 13 17 10 true),(.gateEq true 13 17 0)]

def table4757_0 : List Nat := [0x941,0x9c1,0xa41,0xac1,0xb41,0xbc1,0xcc1,0x300c82,0x351102,0x451382,0x500c011104,0x11602,0x31602,0x51602,0x1a467194631845,0x361802]
def table4757_1 : List Nat := [0x381802,0x461882,0x481882,0x451902,0x4f1982,0x591a02,0x1cc711bc6d1ac5,0x3a1a82,0x461b02,0x481b02,0x541b82,0x4f1c02,0x5c1c02,0x591c82,0x1f47b1e4771d45,0x361d02]
def table4757_2 : List Nat := [0x3e1d02,0x461d82,0x4c1d82,0x501e02,0x561e02,0x4f1e82,0x5e1e82,0x591f02,0x21c8520c811fc5,0x3a1f82,0x4a2002,0x542082,0x5a2102,0x592182,0x2448f2348b2245,0x372202]
def table4757_3 : List Nat := [0x472282,0x482282,0x452302,0x4f2382,0x592402,0x26c9925c9524c5,0x382482,0x3a2482,0x472502,0x4a2502,0x522582,0x542582,0x4f2602,0x5b2602,0x5c2602,0x592682]
def table4757_4 : List Nat := [0x294a32849f2745,0x372702,0x3e2702,0x472782,0x4c2782,0x512802,0x562802,0x4f2882,0x5b2882,0x5e2882,0x592902,0x2bcad2aca929c5,0x362982,0x392982,0x492a02,0x452a82]
def table4757_5 : List Nat := [0x4f2b02,0x592b82,0x2e4b72d4b32c45,0x3e2c02,0x4c2c82,0x562d02,0x5a2d82,0x592e02,0x30cc12fcbd2ec5,0x392e82,0x3a2e82,0x492f02,0x4a2f02,0x532f82,0x542f82,0x4f3002]
def table4757_6 : List Nat := [0x5c3002,0x593082,0x13102,0x123102,0xf4120003,0x33182,0x143182,0xf4140083,0x53202,0x163202,0xf4160103,0x324c73144b0ec340f07,0x324c7314550ec440f07,0x324c73145d0ec4e0f07,0x324c73145512c440f07,0x324c73145d12c4e0f07]
def table4757_7 : List Nat := [0x324c73145d1544e0f07,0x13282,0x183282,0x104180003,0x33302,0x1a3302,0x1041a0083,0x53382,0x1c3382,0x1041c0103,0x33ccd32c4d0fc341007,0x33ccd32c570fc441007,0x33ccd32c5f0fc4e1007,0x33ccd32c57134441007,0x33ccd32c5f1344e1007,0x33ccd32c5f15c4e1007]
def table4757_8 : List Nat := [0x10c1e0003,0x10c200083,0x10c220103,0x3541,0xd03502,0xd23502,0xd73902,0xe53b82,0xef3e02,0xb024073904,0x73e02,0x44d1143d0d42c5,0xd84282,0xda4282,0xdc4282,0xe04282]
def table4757_9 : List Nat := [0xd74302,0xe64302,0xe84302,0xea4302,0xec4302,0xe54382,0xf04382,0xf24382,0xf44382,0xf64382,0xef4402,0xfa4402,0xfc4402,0xfe4402,0x1004402,0xf94482]
def table4757_10 : List Nat := [0x1044482,0x1064482,0x1084482,0x4751b465174545,0xe04502,0xec4582,0xf04602,0xf64602,0xef4682,0x1004682,0xf94702,0x1024702,0x49d2548d2147c5,0xd94782,0xe74802,0xe84802]
def table4757_11 : List Nat := [0xe54882,0xef4902,0xf94982,0x4c52f4b52b4a45,0xd84a02,0xdb4a02,0xdc4a02,0xd74a82,0xe94a82,0xea4a82,0xe54b02,0xf34b02,0xf44b02,0xef4b82,0xfd4b82,0xfe4b82]
def table4757_12 : List Nat := [0xf94c02,0x1054c02,0x1064c02,0xc4c82,0xe4d02,0x104d82,0x37c1,0x4dd354cceb374d63787,0x4dd354ccf5374e43787,0x4dd354ccff374ee3787,0x4dd354cd07374f83787,0x4dd354ccf53ace43787,0x4dd354ccff3acee3787,0x4dd354cd073acf83787,0x4dd354ccff3d4ee3787,0x4dd354cd073d4f83787]
def table4757_13 : List Nat := [0x4dd354cd073fcf83787,0x184e02,0x38c180183,0x1a4e82,0x38c1a0203,0x1c4f02,0x38c1c0283,0x4f53b4e4ed384d63887,0x4f53b4e4f7384e43887,0x4f53b4e501384ee3887,0x4f53b4e509384f83887,0x4f53b4e4f73b4e43887,0x4f53b4e5013b4ee3887,0x4f53b4e5093b4f83887,0x4f53b4e5013dcee3887,0x4f53b4e5093dcf83887]
def table4757_14 : List Nat := [0x4f53b4e509404f83887,0x4fc1,0x5241,0x1415282,0x5441,0x14b5482,0x5641,0x1103c0d5284,0xd5682,0xf5682,0x115682,0x5a567595635845,0x1425802,0x14c5882,0x14b5902,0x1535982]
def table4757_15 : List Nat := [0x15b5a02,0x5cd715bd6d5ac5,0x1425a82,0x1445a82,0x14c5b02,0x14e5b02,0x1545b82,0x1565b82,0x1535c02,0x15c5c02,0x15e5c02,0x15b5c82,0x5f57b5e5775d45,0x1435d02,0x1445d02,0x14d5d82]
def table4757_16 : List Nat := [0x14e5d82,0x14b5e02,0x1555e02,0x1565e02,0x1535e82,0x15d5e82,0x15e5e82,0x15b5f02,0x61d8560d815fc5,0x1445f82,0x14e6002,0x1556082,0x1536102,0x15b6182,0xd6202,0x186202]
def table4757_17 : List Nat := [0x51c180303,0x1a6282,0x51c1a0383,0x1c6302,0x51c1c0403,0x6358b6254f515405187,0x6358b625575154a5187,0x6358b6255f515525187,0x6358b6255753d4a5187,0x6358b6255f53d525187,0x6358b6255f55d525187,0x18f6602,0x1996782,0x136902,0x156902,0x176902]
def table4757_18 : List Nat := [0x6cdb16bdad6ac5,0x1906a82,0x1946a82,0x19a6b02,0x19c6b02,0x1996b82,0x1a06b82,0x1a26b82,0x19f6c02,0x1a66c02,0x1a86c02,0x1a56c82,0x6f5bb6e5b76d45,0x1916d02,0x19b6d82,0x1996e02]
def table4757_19 : List Nat := [0x19f6e82,0x1a56f02,0x71dc570dc16fc5,0x1916f82,0x1946f82,0x19b7002,0x19c7002,0x1a17082,0x1a27082,0x19f7102,0x1a77102,0x1a87102,0x1a57182,0x745cf735cb7245,0x1907202,0x1957202]
def table4757_20 : List Nat := [0x19a7282,0x19d7282,0x1997302,0x1a07302,0x1a37302,0x19f7382,0x1a67382,0x1a97382,0x1a57402,0x137482,0x187482,0x157502,0x1a7502,0x177582,0x1c7582,0x64c1]
def table4757_21 : List Nat := [0x75dd574d9b6458e6487,0x75dd574da1645986487,0x75dd574da76459e6487,0x75dd574da166d986487,0x75dd574da766d9e6487,0x75dd574da76859e6487,0x137602,0x1e7602,0x157682,0x207682,0x177702,0x227702,0x65c1,0x775db7659d6558e6587,0x775db765a3655986587,0x775db765a96559e6587]
def table4757_22 : List Nat := [0x775db765a3675986587,0x775db765a96759e6587,0x775db765a968d9e6587,0x1df7a02,0x1e97c02,0x1d06c197a04,0x197e02,0x1b7e02,0x1d7e02,0x82607816038045,0x1e08002,0x1e28002,0x1e48002,0x1df8082,0x1ea8082,0x1ec8082]
def table4757_23 : List Nat := [0x1ee8082,0x1e98102,0x1f28102,0x1f48102,0x1f68102,0x1f18182,0x1fc8182,0x1fe8182,0x1f98202,0x84e1183e0d82c5,0x1e28282,0x1ee8302,0x1f48382,0x1fc8402,0x1f98482,0x8761b866178545]
def table4757_24 : List Nat := [0x1e08502,0x1e38502,0x1ea8582,0x1ed8582,0x1e98602,0x1f28602,0x1f18682,0x1fa8682,0x1f98702,0x89e2588e2187c5,0x1e08782,0x1e38782,0x1e48782,0x1ea8802,0x1ed8802,0x1ee8802]
def table4757_25 : List Nat := [0x1f58882,0x1f68882,0x1f18902,0x1fd8902,0x1fe8902,0x1f98982,0x8c62f8b62b8a45,0x1e08a02,0x1e28a02,0x1e58a02,0x1df8a82,0x1ea8a82,0x1ec8a82,0x1ef8a82,0x1e98b02,0x1f28b02]
def table4757_26 : List Nat := [0x1f48b02,0x1f78b02,0x1f18b82,0x1fc8b82,0x1ff8b82,0x1f98c02,0x198c82,0x8c82,0x1b8d02,0x28d02,0x1d8d82,0x48d82,0x8de358cdeb785de1007,0x8de358cdf3785e81007,0x8de358cdfb785f01007,0x8de358cdf37ade81007]
def table4757_27 : List Nat := [0x8de358cdfb7adf01007,0x198e02,0x128e02,0x1b8e82,0x148e82,0x1d8f02,0x168f02,0x8f63b8e5ed78dde6487,0x8f63b8e5f578de86487,0x8f63b8e5fd78df06487,0x8f63b8e5f57b5e86487,0x8f63b8e5fd7b5f06487,0x8f63b8e5fd7d5f06487,0x198f82,0x1e8f82,0x1b9002]
def table4757_28 : List Nat := [0x209002,0x1d9082,0x229082,0x79c1,0x90e418fdef795de7987,0x90e418fdf7795e87987,0x90e418fdff795f07987,0x90e418fdf77bde87987,0x90e418fdff7bdf07987,0x90e418fdff7ddf07987,0x2459302,0x24d9502,0x230841f9304,0x1f9702,0x219702,0x239702]
def table4757_29 : List Nat := [0x9b66b9a6679945,0x2469902,0x2489902,0x24a9902,0x24e9982,0x2509982,0x2529982,0x2569a02,0x2589a02,0x25a9a02,0x2559a82,0x2609a82,0x2629a82,0x25d9b02,0x9de759ce719bc5,0x2469b82]
def table4757_30 : List Nat := [0x2499b82,0x24e9c02,0x2519c02,0x2569c82,0x2599c82,0x2559d02,0x25e9d02,0x2619d02,0x25d9d82,0xa067f9f67b9e45,0x2499e02,0x24a9e02,0x2519e82,0x2529e82,0x2599f02,0x25a9f02]
def table4757_31 : List Nat := [0x2559f82,0x2619f82,0x2629f82,0x25da002,0xa2e89a1e85a0c5,0x246a082,0x248a082,0x24ba082,0x24ea102,0x250a102,0x253a102,0x24da182,0x256a182,0x258a182,0x25ba182,0x255a202]
def table4757_32 : List Nat := [0x260a202,0x263a202,0x25da282,0x1fa302,0xa302,0x21a382,0x2a382,0x23a402,0x4a402,0xa468fa364f91e441087,0xa468fa365791e4c1087,0xa468fa365f91e541087,0xa468fa365793e4c1087,0xa468fa365f95e541087,0x1fa482,0x21a502]
def table4757_33 : List Nat := [0x14a502,0x23a582,0x16a582,0xa5e95a4e51926446587,0xa5e95a4e599264c6587,0xa5e95a4e61926546587,0xa5e95a4e599464c6587,0xa5e95a4e61946546587,0xa5e95a4e61966546587,0x1fa602,0x18a602,0x21a682,0x1aa682,0x23a702,0x1ca702,0xa769ba665392e447987]
def table4757_34 : List Nat := [0xa769ba665b92e4c7987,0xa769ba666392e547987,0xa769ba665b94e4c7987,0xa769ba666394e547987,0xa769ba666396e547987,0xa9ea5a8ea1a7c5,0xaa424a783,0xaa426a803,0xaa428a883,0xaa42aa903,0xaa42ca983,0xaceb1abeadaac5,0xad424aa83,0xad426ab03,0xad428ab83,0xad42aac03]
def table4757_35 : List Nat := [0xad42cac83,0xadc1,0xae031ad83,0xaec2ead83,0xaf41,0xaf8d1af03,0xb00d3af03,0xb2ec9b1ec5b0c5,0xb30d9b083,0xb44e0b083,0xb30e7b103,0xb44ecb103,0xb30f1b183,0xb38f5b183,0xb44f6b183,0xefb202]
def table4757_36 : List Nat := [0xb30fbb203,0xb4500b203,0xf9b282,0xb3103b283,0xb3907b283,0xb4508b283,0xb6ed9b5ed5b4c5,0xb7143b483,0xb7d3eb483,0xb8145b483,0xb714db503,0xb7d48b503,0xb814fb503,0x14bb582,0xb7d50b583,0x153b602]
def table4757_37 : List Nat := [0xb7d58b603,0x15bb682,0xb8c1,0xbb6ebba6e7b945,0x24dba02,0x255ba82,0x25dbb02,0xbdef5bcef1bbc5,0x24dbc82,0x255bd02,0x25dbd82,0xc06ffbf6fbbe45,0x24dbf02,0x255bf82,0x25dc002,0xc0c1]
def table4757_38 : List Nat := [0xc141,0xb36a8c183,0xc1f02b883,0xb76a8c203,0xc2704b883,0xae6b4c283,0xc2eeeb903,0xc2ef0b983,0xafeb4c303,0xc36f8b903,0xc36fab983,0xb06bac383,0xc3ef8bb83,0xc3efabc03,0xb7acfc403,0xb86d0c403]
def table4757_39 : List Nat := [0xc4704c083,0xc01,0x3401,0x3481,0x1374d5333acdd3586,0x1374d5333d4dd3906,0x1374d5333fcdd3b86,0x1374d53341cdd3e06,0x1374d5333d4eb3906,0x1374d5333fceb3b86,0x1374d53341ceb3e06,0x1374d5333fcf53b86,0x1374d53341cf53e06,0x1374d53341cff3e06,0x1d7755d366d916386,0x1d7755d3685916606]
def table4757_40 : List Nat := [0x1d7755d369d916786,0x1d7755d36859b6606,0x1d7755d369d9b6786,0x1d7755d369da16786,0x1dd76dd9675956386,0x1dd76dd968d956606,0x1dd76dd96a5956786,0x1dd76dd968d9d6606,0x1dd76dd96a59d6786,0x1dd76dd96a5a36786,0x23d8ee397b5e37786,0x23d8ee397d5e37a06,0x23d8ee397f5e37c06,0x23d8ee397d5ed7a06,0x23d8ee397f5ed7c06,0x23d8ee397f5f57c06]
def table4757_41 : List Nat := [0x2439063f7bde57786,0x2439063f7dde57a06,0x2439063f7fde57c06,0x2439063f7ddef7a06,0x2439063f7fdef7c06,0x2439063f7fdf77c06,0x297a5693946499106,0x297a5693966499306,0x297a5693986499506,0x297a5693966519306,0x297a5693986519506,0x297a5693986599506,0x29da6e9994e4b9106,0x29da6e9996e4b9306,0x29da6e9998e4b9506,0x29da6e9996e539306]
def table4757_42 : List Nat := [0x29da6e9998e539506,0x29da6e9998e5b9506,0x2a9a782,0x2a9a802,0x2a9a882,0x2a9a902,0x2a9a982,0x2b5aa82,0x2b5ab02,0x2b5ab82,0x2b5ac02,0x2b5ac82,0xae01,0xaec1,0xaf81,0xb001]
def table4757_43 : List Nat := [0x2dfb482,0x2dfb502,0x2dfb582,0x2dfb602,0xc1c1,0xc241,0x2b4c282,0x2b4c302,0xc381,0x2f8bb82,0x2fabc02,0xc441,0xad41,0xc281,0xc301,0x568ee4c52d4285]
def table4757_44 : List Nat := [0x15a44ce44450b3746,0x568ee44d314452f4b47,0x56913391114b05,0x568ee44d314445,0x15a4c52d4404,0x569314b5133a85,0x1314b51144d2f35c6,0x15a4c52d44c4,0x569314b43,0x568f54483,0x15a4b02,0x5681,0x5a01,0x5c81,0x5f01,0x6181]
def table4757_45 : List Nat := [0xb681,0x12d4ad293bc4,0x1d8ee39816078a86,0x741b0643,0x1f98ae2187e297c46,0x763b8e62b8105,0x763b8e62a7c05,0x97227886258105,0x25c7e62a7c44,0x25c826037c2057dc6,0x7e62a816237905,0x25c7e62a8144,0x971f98a83,0x972278103,0x25c7e5f77c04,0x971f97dc3]
def table4757_46 : List Nat := [0x8261d8c62b815f17a47,0x25c7e5f18084,0x971f97c43,0x25c7e6037944,0x971f980c3,0x25c7e42,0x695997283,0x1a56642,0x1f80354a51c4,0x5b5775ad755585,0x16d5dd5e5104,0x7e189529465b5775787,0x18b625466355257c6,0x7e18952946579795dc7,0x1f86254a5195e5586,0x7e00d5483]
def table4757_47 : List Nat := [0xb82dc54d4b5d85,0x2e0b715352c4,0x7e1895c5855294655c7,0x5c57b5bd795105,0x1f8b82dc0344,0x7e2e0b715654c5,0x1f8b82dc5584,0x1f8519575484,0x7e2e0b703,0xaa41,0xb341,0xb741,0x1f8b1ceeb2ce23dc6,0x1f84450d3e10fb086,0x7e111434d63e10f3b47,0x7e111434ee3e10f4047]
def table4757_48 : List Nat := [0x1f8b3ac74450d3b8f843c8,0x7e2ceb1d11434ee3e07,0x7e0e438c3,0x1f8b3ac74450d3b86,0x445133bd0d3945,0x1f8b1ecbb24e44286,0x1f8b1d11b2d13b24ef4348,0x7e2c7446cb44ec93bc7,0x7e2ceb1d11b2d13b247,0x7e2ceb1d11b205,0x7e2ceb1d114485,0x1f8b3ac74444,0x7e2ceb1c3,0x7e0ee4403,0x7e0e2b283,0x7e0e2b14f84245]
def table4757_49 : List Nat := [0xb4511b2cec44ec93807,0x7e0ee3b113b245,0x1f83b8ec3e04,0x7e0ee3b03,0xb7c1,0xb3c1,0x12d3942,0x1f83882,0x7e01,0x8201,0x8481,0x8701,0x8981,0x8c01,0x9701,0x9b01]
def table4757_50 : List Nat := [0x9d81,0xa001,0xa281,0xbb01,0xbd81,0xc001,0x23b691f08084,0x2038adfc7884,0x8eda47c22b7f05,0x23b691f08ac4,0x8eda47c03,0x23b691ee78c4,0x8eda47b83,0x8eda47883,0x7c62b7a43,0x23b6902]
def table4757_51 : List Nat := [0x22b7d2037c44,0x8ede38adf48e63d80c7,0x1e38adf48ee398f46,0xa569395297a205,0x295a4e4ca5e899906,0x295a4e4ca5e899986,0x295a4e4ca5e899a06,0x295a4e54a5c4,0xa669da6e549a85,0x26b9fe5a9484,0x299a769b9527f9686,0xa669da6e549fc5,0x29da669b9504,0xa669da6e5392c5,0x299a769b9684,0x9564dbe83]
def table4757_52 : List Nat := [0x2559342,0xa669da6c3,0x164451203,0x591142,0x314c70143c2f4bb13c7,0xc531c050f04e2f86,0xc531c050f0bd2ec6,0x314c70143c2e85,0xc531c050f04,0x48140143,0x32ccf100593344e1d47715c9,0x32ccf100593344e2dc751dc9,0x32ccf100593344e1d87,0x32ccf100593344e1d07,0xcb33c40164cd1386,0xcb33c40164cd1e06]
def table4757_53 : List Nat := [0x4cd33c401d05,0x4004cd0704,0x1334cf1d8a11006,0x23d8ee398ae057d06,0x8f63b8e62b816037887,0x8ae057a43,0x8ee398f62b8145,0x1d8ee398ac4,0x763b8e43,0x71d98765dd76dc16a87,0x71d98765dd76dc16b87,0x71dd9775db6c05,0x6cdd9775db6c59e6a47,0x695b1715a26505,0x1a5765dd76dc56886,0x6cdc7661d9775db68c7]
def table4757_54 : List Nat := [0x1a5765dd76c4,0xa468f10a8d932759a07,0xa468f10a8d99e4c9547,0xa468f10a8d932549907,0xa468f10a8d932549a07,0x291a3c42a36879328995c8,0xa1e75a26739385,0xa468f10a8da1e679307,0x9341,0x9141,0xa3c42a468da1c5,0x42a468fa344,0x1d3695d7755cf6b06,0x74da575dd56c5af73c7,0x1d3695d7755b16bc6,0x74da575dd56b85]
def table4757_55 : List Nat := [0x490c18695d9811e505c8,0x131c4e3243c2f06,0x131c95138c90f09712c8,0x1d375da57544,0x490c17061d98106,0x90e418fe05805e87dc7,0x205792237b84,0x205792237f84,0x2439063f815e488c6,0x2418fe0590e017dc6,0x90e418fe057905,0x90e418fe057dc5,0x90e418fe058805,0x90e418fde58185,0x90e418fe057c05,0x24190e3f8144]
def table4757_56 : List Nat := [0x4074170604,0x90e3f9043,0x101d05c3,0x3c00403138540e86,0xf00100c4e1505,0x3c004031384,0x3c004031544,0x591c4991bc970e86,0xf00100c3,0x80407c3,0x8d637102338105,0x2358dc408ce248a06,0x2358dc408ce248a86,0x8d637102338905,0x2358dc408cde88b06,0x8d637102337a22e7a87]
def table4757_57 : List Nat := [0x2358dc408cde88b86,0x8d637102338ac5,0x2378d4408cc4,0x28de9d0684,0x8150103,0x20541d06c4,0x47b33c403345,0x82307c3,0x2398f63b8144,0x8f6398ec3,0x20563d06c4,0x4021eccf0685,0x10087b0544,0x3c004bf0ecbb13c6,0x8d404695d905c5,0x3c004bf0ecbb0506]
def table4757_58 : List Nat := [0x5932c02138cf0686,0xf0012fc3b2ec5,0x3c0044e0144,0x3c0043b2604,0xf0010ec4b0105,0xf0010143,0x3c004540ec4,0x5920c971fc931286,0x3c004542544,0xf0011503,0xf0012603,0x3c0042,0x3c258c7138c93146,0x1602,0x40083,0x23304c040704]
def table4757_59 : List Nat := [0xa46430784,0x28d04c040884,0x130103,0xa469d0744,0xa5e95a4c3,0x4e04e9108c5,0x13813a444,0x90e9b06c4,0x4e04c3,0x3c258c71384,0x3c31c1c0844,0x75dd504c3,0xf09631cc53245,0xf09631c1c0685,0x164a3100cf32ccd1d07,0xf09631c400705]
def table4757_60 : List Nat := [0x5913c40334cb33c6,0xf09631c400605,0x768f0104,0x3c258c71004,0xf0c78e63f0745,0xf09631c3,0x28d00a3f0804,0xc60783,0xc6a6c3,0x3182,0xf0200083,0x33440164cb33c5,0xf095314c913c5,0xf0952fcbd1705,0x3c254c5324541286,0xf095314c912c5]
def table4757_61 : List Nat := [0xf095081a50885,0xf09576da5a741c1387,0xf09576da5a741c3147,0x3c254206944,0x6901,0xf0040843,0xf0c53243,0x3c3142,0x842307c3,0x765db7743,0x74dd77543,0x3c05c2,0x3c0842,0xf01,0x76e3ba603,0x723b0583]
def table4757_62 : List Nat := [0x70120503,0x801c7603,0x200702,0x18004cd0684,0x7c017703,0x200042,0x801,0xa381,0xa681,0x8c2,1,0x1601,0x3281,0x1141,193,0x501]
def table4757_63 : List Nat := [257,0x1ec1,0x7681,0x3381,0x13c1,0x681,0x8e81,0x741,0xa601,0xa701]

def encoded4757 (i : Nat) : Nat :=
  if i < 512 then
    if i < 256 then
      if i < 128 then
        if i < 64 then
          if i < 32 then
            if i < 16 then
              table4757_0.getD (i%16) 0
            else
              table4757_1.getD (i%16) 0
          else
            if i < 48 then
              table4757_2.getD (i%16) 0
            else
              table4757_3.getD (i%16) 0
        else
          if i < 96 then
            if i < 80 then
              table4757_4.getD (i%16) 0
            else
              table4757_5.getD (i%16) 0
          else
            if i < 112 then
              table4757_6.getD (i%16) 0
            else
              table4757_7.getD (i%16) 0
      else
        if i < 192 then
          if i < 160 then
            if i < 144 then
              table4757_8.getD (i%16) 0
            else
              table4757_9.getD (i%16) 0
          else
            if i < 176 then
              table4757_10.getD (i%16) 0
            else
              table4757_11.getD (i%16) 0
        else
          if i < 224 then
            if i < 208 then
              table4757_12.getD (i%16) 0
            else
              table4757_13.getD (i%16) 0
          else
            if i < 240 then
              table4757_14.getD (i%16) 0
            else
              table4757_15.getD (i%16) 0
    else
      if i < 384 then
        if i < 320 then
          if i < 288 then
            if i < 272 then
              table4757_16.getD (i%16) 0
            else
              table4757_17.getD (i%16) 0
          else
            if i < 304 then
              table4757_18.getD (i%16) 0
            else
              table4757_19.getD (i%16) 0
        else
          if i < 352 then
            if i < 336 then
              table4757_20.getD (i%16) 0
            else
              table4757_21.getD (i%16) 0
          else
            if i < 368 then
              table4757_22.getD (i%16) 0
            else
              table4757_23.getD (i%16) 0
      else
        if i < 448 then
          if i < 416 then
            if i < 400 then
              table4757_24.getD (i%16) 0
            else
              table4757_25.getD (i%16) 0
          else
            if i < 432 then
              table4757_26.getD (i%16) 0
            else
              table4757_27.getD (i%16) 0
        else
          if i < 480 then
            if i < 464 then
              table4757_28.getD (i%16) 0
            else
              table4757_29.getD (i%16) 0
          else
            if i < 496 then
              table4757_30.getD (i%16) 0
            else
              table4757_31.getD (i%16) 0
  else
    if i < 768 then
      if i < 640 then
        if i < 576 then
          if i < 544 then
            if i < 528 then
              table4757_32.getD (i%16) 0
            else
              table4757_33.getD (i%16) 0
          else
            if i < 560 then
              table4757_34.getD (i%16) 0
            else
              table4757_35.getD (i%16) 0
        else
          if i < 608 then
            if i < 592 then
              table4757_36.getD (i%16) 0
            else
              table4757_37.getD (i%16) 0
          else
            if i < 624 then
              table4757_38.getD (i%16) 0
            else
              table4757_39.getD (i%16) 0
      else
        if i < 704 then
          if i < 672 then
            if i < 656 then
              table4757_40.getD (i%16) 0
            else
              table4757_41.getD (i%16) 0
          else
            if i < 688 then
              table4757_42.getD (i%16) 0
            else
              table4757_43.getD (i%16) 0
        else
          if i < 736 then
            if i < 720 then
              table4757_44.getD (i%16) 0
            else
              table4757_45.getD (i%16) 0
          else
            if i < 752 then
              table4757_46.getD (i%16) 0
            else
              table4757_47.getD (i%16) 0
    else
      if i < 896 then
        if i < 832 then
          if i < 800 then
            if i < 784 then
              table4757_48.getD (i%16) 0
            else
              table4757_49.getD (i%16) 0
          else
            if i < 816 then
              table4757_50.getD (i%16) 0
            else
              table4757_51.getD (i%16) 0
        else
          if i < 864 then
            if i < 848 then
              table4757_52.getD (i%16) 0
            else
              table4757_53.getD (i%16) 0
          else
            if i < 880 then
              table4757_54.getD (i%16) 0
            else
              table4757_55.getD (i%16) 0
      else
        if i < 960 then
          if i < 928 then
            if i < 912 then
              table4757_56.getD (i%16) 0
            else
              table4757_57.getD (i%16) 0
          else
            if i < 944 then
              table4757_58.getD (i%16) 0
            else
              table4757_59.getD (i%16) 0
        else
          if i < 992 then
            if i < 976 then
              table4757_60.getD (i%16) 0
            else
              table4757_61.getD (i%16) 0
          else
            if i < 1008 then
              table4757_62.getD (i%16) 0
            else
              table4757_63.getD (i%16) 0
def book4757 (i : Nat) : Clause := let n := encoded4757 i; unpackLits 10 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses4757 : inputsOK 3 4757 a4757 r4757 (baseBook book4757 625).toList=true := by decide +kernel

def rows4757_0 : List Nat := [0x300e01,0x4190801,0x4190a01,0x6318e01,0x6319001,0x6319201,0x6319401,0x6319601,0x6319801,0x6319a01,0x6319c01,0x6319e01,0x631a001,0xa7aa001,0xa7aa201,0xa7aa401,0xa7aa601,0xa7aa801,0xa7aaa01,0xae2ba01,0xae2bc01,0xae2be01,0xae2c001,0xae2c201]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4757_0 : checkRows book4757 10 625 rows4757_0=true := by decide +kernel

def rows4757_1 : List Nat := [0xae2c401,0xa7b6e01,0xa7b7001,0xa7b7201,0xa7b7401,0xa7b7601,0xa7b7801,0xe1b8801,0xe1b8a01,0xe1b8c01,0xe1b8e01,0xe1b9001,0xe1b9201,0xae42601,0xae42801,0xae42a01,0xae42c01,0xae42e01,0xae43001,0xe1c3e01,0xe1c4001,0xe1c4201,0xe1c4401,0xe1c4601]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4757_1 : checkRows book4757 10 649 rows4757_1=true := by decide +kernel

def rows4757_2 : List Nat := [0xe1c4801,0x44c01,0xc4e01,0x145001,0x1c5201,0x245401,0x45801,0xc5a01,0x145c01,0x1c5e01,0x246001,0x4e318c6402,0xb18c6602,0x4e51a46a02,0x4e71a46c02,0x70c9001,0x7149601,0x7249c01,0x734a001,0x4bf294c402,0x4c1294c802,0x1564ca01,0x1574d001,0x55f56cd602]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4757_2 : checkRows book4757 10 673 rows4757_2=true := by decide +kernel

def rows4757_3 : List Nat := [0x15c4d801,0x15c4da01,0x4c12fce002,0x155d5554d5153c5605,0x15e56c01,0x15e56e01,0x5f9733b4e85a91c46986741887498a7510c439660f,0x4c1273ace8619d0621d2629d4431160b,0x1173c1245c9705996d6057e619d0621d2629d44393010,0x471273acf04b9785d986741887498a751160d,0x499313ccf65fd835fd84619d0621d2629d4439160f,0x1725b4f33b17c4e9384d186741887498a751660e,0x45d804696c5a9665c9265ed876212a0b,0x5a9165992a5b9204311a07,0x1304a916491705996c474e96358a5ed86619d0621d2629d5624f014,0x5f9725b4fb3d4ee5093f63986741887498a751660f,0x1424f986741887498a754f808,0x13a4d585649785d186741887498a754f60c,0x1304e926474f93e9413d4ee61182605916518a62186751d27411614,0x1659e001,0x1659f601,0x165a0e01,0x165a1a01,0x165ca201]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4757_3 : checkRows book4757 10 697 rows4757_3=true := by decide +kernel

def rows4757_4 : List Nat := [0x6017a4416603,0xb5ae14533ace334daaf0b42d209,0xc1ad2bfad8c0b32cc32d69344c32eacf308b8ac8b2b62bc310d2ad0d9ade17,0xc8b2cc4b44c932ad2b4207,0x346d132ccc34345ae8b9ae2dab4ab451e0c,0xb9aed46d1cb236ace5a407,0x31348b20ba2e6b8b7ce6b80e7384e7b180c,0xc8b08c4afec5b02b62d6b4daec930cbab7ce6b80e7384e7af0c432ac1b1cce2e0ced221b,0xbbad94ad22df39ae039ce139eb22d20b,0xbb312b4b18b62f0cab1cce2e0ceb260b,0x2d6c4ad2ca2ef495b4c8db2df39ae039ce139ebc32ac7338b833b6c31616,0x52b6bae96ddb0c7338df39ae039ce139ecab280e,0xca3256bb1f49ae8b8b7ce6b80e7384e7d2a0d,0x5276cac8df39ae039ce139ebc5bacaae00c,0x2ff49b06b82deb4ad8c0b32cc32cd130cbadbcd0b7ce6b80e7384e7af0c434b6e5bacab081c,0xc1ad2bfad8c0b32cc32ccf308bab0cd12de0d,0x3134831cb82dedf39ae039ce139ec8dbec92c7705bacadb8d2b10bc31816,0xc4d20c5ad8b5ad370ac770324bab7ce6b80e7384e7af0c434b6e5bacab236fb1e19,0x2d6c4ad2c7b28bbd214937ce6b80e7384e7af16eb2ac8dbeb1ac97131616,0xc4d28c9aeebb2d2c62d971b7ce6b80e7384e7af16eb2ac8dbf7131e15,0x328c65294831cb82df722c6b25c4c8dbecab7ce6b80e7384e7b1214,0x25a902589225ca0a8095a6292a5e942608e2420e,0x972409624496a7e9f27b7328a98250a125e92a3895a62a424613,0x228892ceb41ce04]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4757_4 : checkRows book4757 10 721 rows4757_4=true := by decide +kernel

def rows4757_5 : List Nat := [0x7c9f878a067bd9d66a0a07,0x7b1f8789fc799f48359d66a0409,0x791f878a067ba2d7520c7d222b3a26b459d669fa0f,0x801ea7f1e68ca2e8d5d207,0x7f1ea7e5d688ace89ad071a0d6722a0b,0x78a2a7a2007fdda819ee88ace89ad0719f5669e60f,0x2007aa31775d9741ca88ace89ad0875d60c,0x7648c75c9876a007f9df279dd26da16648e0d,0x1db231d7249d87f1fa7e5e126a02771de8249f685996749412,0x859e2842147aa1279a308b222b3a26b459b679ec0f,0x7a1f8789fc79d9d669fe07,0x1e47e1e2801ea8ade6819ef795d071de2862087c5de87222b3a26b459d669fa18,0x791f878a007aa2a71de778a087c222b3a26b421e882cd7a1ee81d9d669fa17,0x1761cb7aa22b3a26b421e882cd7a5dc0b,0x801ea8c5d872a22b3a26b421eb35d60b,0x178a187c5ef7b2217a21eb35e409,0x15354b525475144a05,0x5697ccc202,0x56b7ccc602,0x11cc831d9b06f1b668acc69ace6aad137df043d777dc6e11,0x1166d1191cc70689a6b39aab44df7c1a4452cd7d5777d94412,0x11e511ae6e9a269ace6aad069114b31160c,0x11e511b2701a269ace6aad069114b31160c,0x459b450c8b2246f20dff1ddfd7e9a269ace6aad137df04310e69114b35777d91e19]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4757_5 : checkRows book4757 10 745 rows4757_5=true := by decide +kernel

def rows4757_6 : List Nat := [0x5f86f933801a4451a2b31a6b39aab44df7c5777dc8a10,0x1ac6a1a4b32ceb411206,0x11dc826b9b31c11e461164cdf9814844fe024310e68acc69ace6aad137df17d5777dc6e1b,0x15f689585a95a46918459745812a58964441700e,0x46e6bc704791868acc69ace6aad137df0436057d5777dc7612,0x11cc766c1b64c91782e05821a2b31a6b39aab44df7c5777dc6e13,0x1815a26b9691cc711b9711d128491224860c68acc69ace6aad137df17d5777d97419,0x11cc746b92848e044360643e0e68acc69ace6aad137df17d5777dc6e15,0x1298160643c831f9a2b31a6b39aab44df7c5777d9b810,0x4a1a581914441444f9a2b31a6b39aab41ba0d,0x128696064511122c8584615849a2b31a6b39aab44df7c5777d9ba14,0x122c851bc771c9b86ce052010e4f1364d61668acc69ace6aad137df17d5777d9c019,0x122c851bc771cc7c6e1b26f4804f13668acc69ace6aad137df18110f7d5777d9c019,0x5214e529526d1be6e9c055c8b21c8468acc69ace6aad137df17d5777d94617,0x11cc7d209b46f9c068acc69ace6aad137df1875777dc6e11,0x12d1b9171c91e4a4777d47808,0x1171f1326c62068acc69ace6aad137df186e1d8110e4a5777de0a14,0x17f9bd20e225161e68acc69ace6aad18110f869291dcdf7c5777d93215,0x11e4c9b26f4838893f8912868acc69ace6aad137df18110f86d777d91616,0x159d6558d616848c05,0x5778a4dc02,0x56966561705712448e08601644f97a58934441604396811,0x51950441498994a6c1b668acc69ace6aad11f4df7c14d1e62c5e47b8662b7d5777d9541b,0x62f8b1791ee198ae0406]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4757_6 : checkRows book4757 10 769 rows4757_6=true := by decide +kernel

def rows4757_7 : List Nat := [0x18c2f001,0x18c2fc01,0x18c31001,0x18c32a01,0x18c34a01,0x18c5ca01,0x18f3ba01,0x18f3d001,0x18f3e601,0x18f40401,0x18f4ac01,0x18f4b401,0x18f4bc01,0x330d1b40ced154751ab82ded923adb23eb1ac98eb2c10,0xba32cb4b30b5aecd1e3b8cb4209,0xb632cb4b40b9d1793b46bb3648eb6c8fac99363b8cb3211,0xbbb2cb4b40b9b30b5d1f46650d923adb23f9363b8cb4811,0xbd2fabe2f74551d46b3ace652b1ac8d923adb23f8d2f211,0x338cd5a8ccad8b4ae6c8312c5b648eb6c8faeac9654b831f8c6338e51416,0x338d0d1aba2e6b8ad2cc2d795ae0d923adb23ebab459563b8cb2c14,0x2deba51ad0b40cf32ccc2d6d923adb23ebab459533b966338ead214,0x2e38ee378cdc004,0x332b4b2cb7b40b9d1545ac79765acee58d12eb9536cd923e8ee338ead816,0xb632cb4b44baae6d063b8cb3209]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4757_7 : checkRows book4757 10 793 rows4757_7=true := by decide +kernel

def rows4757_8 : List Nat := [0xb632cb4b46bb519982e6d063b8cb320b,0xb7adb98d1403,0x3b0eaba4ee5374d53100c018fba00a,0xfebf2fbd2f4b3a6e9395913e809,0xfb3fafd52d4cbaceab95913e809,0x3f2fb3fd4cd2eecbb1913e808,0xfebf2fb5374d530edba19b66b9a666e5e458fbe80f,0x3def6bd750d414f3e2ee3b790bd20a,0xe93d2e83daeb3b2f7e438fbd409,0x3aaf4ba0f5ba74e672f7bb2e53979c6438fbd80e,0x3b0f4ba0f6bacf5ba74fd3b9d3979c6438fbdc0e,0x3b2eb3a750d414f3e59de718fba00a,0x394fa538fbbff9e3f5913f608,0x3aaf4ba0f5ba79ee72f7bb2ed3e19e6438fbd80e,0x4af29d75354ab2cca92c57b926475f4cc0c,0x12bca75ccd32de7f2e4b12a4ab2ccbb5ee4991d7d92cce11,0x3b0f4ba0f6bacf5ba74fd3ba067cf83b59e63f90bdc10,0x1e1701c188240a868098640a0660485e0c,0x600705c0805e268982589da10a01982827864098120a8682882214,0x1b872360dc1d0bc2e8b02f8783407e30e860686a0f,0x1b8721f0d8370e01d0bc2e8d01fe860686a0d,0x1606a140721506e14876158de368e0300b1a2e883405a1f8c20687a15,0x1f0781a8761c8d83586c2d0b23407e04686068da0f,0xe0360b02e0d0d6370322e0b7a368e3403a04686068de11]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4757_8 : checkRows book4757 10 817 rows4757_8=true := by decide +kernel

def rows4757_9 : List Nat := [0x338c9a4686068c63301407,0x118800f08422092130f63e8fe13895a188a0d,0x2a0a63f0f81303c2a849a504e2b8a40b,0x842488c3d0fc3e8861104225011a18800c,0x92230883e0f63d0821003e25011a18800c,0x88210fc3e04c0f090230482b695a5e9ba604e2508010,0x210883d8fa2284811895a188fa70800b,0x8c220f63d0821003e25011a188fa7016388800e,0x2108c3d0fa218441083da808e12e9fa70f23c0e213894046860588015,0x84238f5a70e225011a181611086108800c,0xb7aef47348d1b44cb330b5e64d06338ead20d,0x51eb4e4eb5ea78caea06,0x2c98ee378cdc004,0x1aa51b45eaba9ade05,0x5aadaeac02,0x2e6b8da4badacce6aedad1a08,0x2769ca649c50a99a4490d0c08,0x2769ca649a50a9ba4e9351208,0x2709a26d44d0d4427495252942640a,0x24e9124944d0d4424006,0x91a6490268912569e24e9c26a09,0x9026c92509aea4e95a3773eb69e6b20b,0x9026c9224543d0badeb407,0x2769cebdafeb695a7973eb808]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4757_9 : checkRows book4757 10 841 rows4757_9=true := by decide +kernel

def rows4757_10 : List Nat := [0x3c2efbc906414ec3af903bc08,0x3c2f1bc104c14e93a2e86c2f2bb4e56418fbbc0e,0xf33c2f1bc105c13053a4e8b95903bc0b,0x106ec2ebbcc03,0xfc3eb06415913e805,0xf03e8ef3f0f0e45903ec07,0xf13e8ef3eaefc13b33c7b2c02f3bb8edba1b26c7b1395916418fbf215,0xe5e8001,0x1b439401,0x3cefa3bcfabbef1bf4f1413063aceaba9b3ed1b4e419140012,0x3b6ef3a0f0ba8efba2ecbc906414ff3fafe6d5b463f903ce12,0x27ca1a833f50292246a423773a7a0a,0xa1a809fcff3f24490a41b6256a423773a7a0d,0x24690d054028ca2eda95a4008,0x28ca2a7aa027ca25033fa4e9329173d060c,0xa02869f28f415074025494a51b76dea637f48b7d01ed64143ba0c3702ab3b02b4a6c10a5434a42e2ba27a21,0x380b834378d6370322e0b63103a046860582c0e,0x1f06e378d63107e046860586a09,0xa027ca1a8f4150141a5494a51b76dea427a0d,0xca324c4b1ec6526c86e0ba2e6b8b7ea66e6a529adf407b59050ee830dc350440aacec0ad23f8e52a1f,0x2eebaad2b85278cd2a06,0xbb312b4b1eb82d8c66398cb2609,0xb7b12b4b28bbad8c66398cb1c09,0x2dec4ad2c92eb4a6efbb2d8c66398cb1c0c]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4757_10 : checkRows book4757 10 865 rows4757_10=true := by decide +kernel

def rows4757_11 : List Nat := [0xb4b3abaeaab26eb8cae007,0xc8ef0b66f203,0x306c0b38c32d7aab08b26f348ef58dafe0c,0x6ab48338c7b1dbd2c606,0x2eebad2402,0x2d2c5ae0c4d20ca2c7492c8c8ef7be6fbbd6338e2d610,0xb82dab4ad6c5b12c96fdbeef8c8ef7bd6398cd200f,0x6e8df407b59050ee830dc0aacec0ab365ac37eda298a5ee70d295043828fa9aad6fe1a,0xca324c4b18c7d22c8526ba2e6b8eff8e52a0d,0x38102ed64143ba0c3301aafb02b0da439ac5a6deb63c02b48fc10e0f0216,0x1606a14072150de300b02d06e148c41687e30ee234f05a88e805686058ca158762f07a1b,0x6c2c06a3007c1c8da35f062f0763107e30811b88d3c16a23a015a1816328b218,0x742c06a2d06e1c8c01f0d8370e1c26e23107e308ca34f05a88e805686058ba18,0x1d0b01a8b41b8b81c8d8370c41f8c2328d3c16a23a015a18161e0bfc28ba17,0xc06a0b06e0b83a1f87007,0x1b0b01a8b81c8d7c38bc1d835c30be1e037c28d3c16a2050e8328c41f8c204686058b21b,0x41103b5c0703411b439807,0xd2312cb32ec5336c6b42c835ad7ae8b9ae4b8e398eb2811,0x2dcb6358ccb2fc52ecc9ac6b23258cad20c,0x2d4b8358ceb37c52ecc9ac6b23258cad20c,0x2d4b735ad7b3ecb719c5b46bb2c8c9b25c56338ead210,0xc531ac835ad7b40cff1b8e31209,0x30ec2b02d735ab5ad4b4b04b7714d12eed26378cafe10,0x306b4afec02d4c3b0ad6360d7f1ebbb48d1714b1e338dade12]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4757_11 : checkRows book4757 10 889 rows4757_11=true := by decide +kernel

def rows4757_12 : List Nat := [0xc3aeabfad2c12dcc2ad8c0b58d6b32cc32ecb721c72c7aaf158de338eb5c17,0x30ac3b5ed82c8baad2c02d4b8306d633ace336cd723c56338dafe14,0x34d0d6823b438d4f2406,0x295c96e63ca9ce0f02dff270eab7b037cabf12d5b528f296ac34c14,0x6d6e640eadec101aacdf365c0eb0dfb670323cac383b410212,0xfba90440f6a1a78e213e860588c0a,0x6d6e64070340fb410206,0xbb2eab4ad6b8514ceb38cd6ad8cd1c0b,0x34593b2cce2decc34346d16ba2e6b8f318ed1e0e,0x364a4ee6a772ad9a3ca5f3208,0xec3af2c02,0x1cbf02abb7bb0294ad6e6db29dcd72adff363bf28ac2968f38413,0x1a0b4d0df24ac8f30f6c1c12b4ab8d3c4b57978d7a4368337382e0b02f84a310c20468605b53c44341f,0x1a0b4d0df24ac8f30f6c1c12b4d5c340b,0x2c0dbb88d3cf2afc4e5fa4368330c430816d4f11ce8c011,0xec3ae9c02,0x72fc0aaedeec0a52b5b9b6ca7735cab7fd00efca2b0a5a3dcff3a058e3c438418,0x72fc0aaedeec0a52b5b9b6ca72b0a5a3dcd72adf8cdd06903b816310e3c438418,0xd3978dada0ccabf29c4f441f07831353c473c0e,0xd3978d6da0ccabf29c48c40468605b53c473c0e,0x4a33745a40c5c473806,0x1b0722cf49d1f421f817d28762f06a0b,0x1606a140721505a1f87a07,0x1b906a1f8cc34f3d97b69ca2afc4f4ad4f11d386e14f4c1d8560587815]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4757_12 : checkRows book4757 10 913 rows4757_12=true := by decide +kernel

def rows4757_13 : List Nat := [0x380d82c0c071d474e1b8520bf4c1d8560d0c40e816330d3cf65eda728abf13d2b53c40de1c,0x1f078310cc34f3d97b69ca2afc4f4ad4f11d48e00f,0xc02f8b02e8741af542d06e2e072360ddd48d3cf65eda0ccabf29c4f4ad4f11a18c21f8c4058e01e,0x6d7c4c0c060c22c0b42e0c1040d8370e1a4409d58762e8740490014,0x1b5c11c4c0c068190210007,0x1b5f13034090410005,0x299c96e63ca9c8ea92d5b5008,0x381b5f024037d0240a06,0x2b3b5ec0412b68eaad0440a08,0x1c95a6d4439a0c3bd8c33d8383d7c10d5b4f020e60f,0x72569b510e6830cf60e0b54d38e60a,0x66d9a66affbb59bed18fba008,0xe639363ccb6cad6c03a2b30340bb59010776908368a5ee6a77670ec230275a8ea92ab0efd969c1e,0x35039a98d8ee7ac354a6c3d09683da437083690cc1cacab1d86c0e12b7dab4e8ea92ab7241c,0x43dc968239c34def02dfb50d3b540a,0xe639363ac29db9a983af6f0db68acab1b0384adc0fdb0efd92aca4a3bd6e9c18,0xaced7b0100abc33a0c38d47243cc3dc12b48f8d304357d669031f70d3c09d5c0a19,0xa4a3aa60c7dbe90e141103ed640433a0c3702c09d5a9d0f6e613,0x2928eee602,0x2d0b8360dc30e87d6f561d8ba1d0bfdc8b00d,0xad23e34f7831f76abc33a0c38a629d0f2b3dd6c00f,0x8c220f63d0821003e25011a18800a,0x84230f43e886110420f77da78e9036d639100d8c1dccf6903c24db420adab4a5ec1ddaac31e90d5e5fc9366d477aacf74a70f0d3c081389404687d6f561288fdc88034,0x84230f43e886110420f77da784e25011a184a2388010]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4757_13 : checkRows book4757 10 937 rows4757_13=true := by decide +kernel

def rows4757_14 : List Nat := [0x348c7c17623bf810ee830d0e50275bdc8eb0e351c9355dfb4fd5f7815,0x10eed7d9c110210405,0x43b03ab7b02ac31e91e140aac23ce0369c0f32deb63e0b82daf7fd5f6616,0x10ec0eadec0ab0c7a478502ab08f380da703ac383d5f6611,0x6c0db2adcce5e31b66ace91def743cf88deb6239f87d5ab412,0x385b5f0240b810340e06,0xaded7b0100abc09030ca8f2b03340e0b,0x3543b43ddbe82d3b530cb85cbf8e32f240c,0xa529cdef2be34390df90a5a3c330cb026e60d,0x2b6ab23b038c7b5e9040f5d03409e4f56acec00e,0x1a778001,0xb82f0d6360b21b86c1a8be1e07e30811a1f5be2f93d58b012,0x1b0b01a8c01f07e30f5be2f93d58b20b,0x6e148dbe68b9d6f8be4f57e60562f74e0c,0x7c1b8de3587e04687d6f8be4f57e606a0c,0x1f06e380d9e779fe60d2a6ee6a6351c9357a40e6a50c6deaadc0ec0e12b6d387fa1f5be2f93d5ab2e006a21,0x1f06e380d9e779e34ab5b02af0ce830e351c90f2d5e9031f70d387fa1f5be2f93d586a1b,0x682abc39b0350ad724348f2d5f99a434fe4f57e8c3210,0xe639363ccb6cda2b4a5ec1ddaac31fa4a70f1d9c3b03fa1d6f56ac8e9e579618,0x65e8f36802,0x77502f93d5f8404,0x380d82c0d02e370d60e811a1f5a1c8301c7a7eae91e4f57ea0de14,0x682d4433c92ae3cc3db0704ad0d3eb2b3eab57a434fe4f57ea43814,0x1b439801]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4757_14 : checkRows book4757 10 961 rows4757_14=true := by decide +kernel

def rows4757_15 : List Nat := [0x1ea6c001,0x1ea6e601,0x76fdd436aca99ecf76ad29be4f56ab0c7ebb820e,0xe639363e20eadf76f07383da7750dc1fd6f923bf6431fafd5c25edf9616,0xe639363ccb68a5f76a77670ec0ead8e9ecf94acfb8db7b63bf64ab0c7d6fafd5f961a,0xad733ecb62abc350cb6c07,0x1e58143a0cea5f7639686d936206f323536c3c29dee8e611,0x1a88cfa48c9ee8e805,0x143a78cdea95ed297f068605c06322aeab29deeea210,0x1e5814388c9dda983ae86d981bef8d4ad7b3f0a9c3c2b3ee8ec13,0x796050ee3529bed29839295a1817ee8ec0c,0x1cb8d4adab5a1817ee81407,0xead9eb0d92adecfc8acb7adf702e0fc4e07c60e,0x796d40efc9764398c9d6b4ff28e4def02e0b55f1381ee8ea12,0x1f340a01,0x1f343601,0x6d7ec40f027cff310006,0xe639363ac29dddb68a60eaac76fecb84adfd23bf64ab0c9d6fd1eef9616,0x1f501601,0x1f50e201,0x1f5e8601,0x1a88d4050e9f57bbf6f0407,0x7bbf70ce02,0x7dff772802]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4757_15 : checkRows book4757 10 985 rows4757_15=true := by decide +kernel

def rows4757_16 : List Nat := [0x1f57dff773803,0x1f7ab001,0x1f80ee01,0x1f884a01,0x1f5fddf9fd9fa74005,0x1fab6601,0x1f77dffaf2a03,0x7e5fb7bc02,0x1fbc3c01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4757_16 : checkRows book4757 10 1009 rows4757_16=true := by decide +kernel

def lastUnits4757 := digits 10 3 0x3e8fe3f9
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict4757 : checkReasons book4757 1018 833 lastUnits4757 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude4757 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 4757=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=3) h hc bp eq (by decide +kernel)
  let v := truth Z a4757
  have hbase : ValidThrough v book4757 625 := book_start Z h hc z eq _ _ _ _ initialClauses4757
  have h0 : ValidThrough v book4757 649 := rows_sound hbase rows4757_0 rowsOk4757_0
  have h1 : ValidThrough v book4757 673 := rows_sound h0 rows4757_1 rowsOk4757_1
  have h2 : ValidThrough v book4757 697 := rows_sound h1 rows4757_2 rowsOk4757_2
  have h3 : ValidThrough v book4757 721 := rows_sound h2 rows4757_3 rowsOk4757_3
  have h4 : ValidThrough v book4757 745 := rows_sound h3 rows4757_4 rowsOk4757_4
  have h5 : ValidThrough v book4757 769 := rows_sound h4 rows4757_5 rowsOk4757_5
  have h6 : ValidThrough v book4757 793 := rows_sound h5 rows4757_6 rowsOk4757_6
  have h7 : ValidThrough v book4757 817 := rows_sound h6 rows4757_7 rowsOk4757_7
  have h8 : ValidThrough v book4757 841 := rows_sound h7 rows4757_8 rowsOk4757_8
  have h9 : ValidThrough v book4757 865 := rows_sound h8 rows4757_9 rowsOk4757_9
  have h10 : ValidThrough v book4757 889 := rows_sound h9 rows4757_10 rowsOk4757_10
  have h11 : ValidThrough v book4757 913 := rows_sound h10 rows4757_11 rowsOk4757_11
  have h12 : ValidThrough v book4757 937 := rows_sound h11 rows4757_12 rowsOk4757_12
  have h13 : ValidThrough v book4757 961 := rows_sound h12 rows4757_13 rowsOk4757_13
  have h14 : ValidThrough v book4757 985 := rows_sound h13 rows4757_14 rowsOk4757_14
  have h15 : ValidThrough v book4757 1009 := rows_sound h14 rows4757_15 rowsOk4757_15
  have h16 : ValidThrough v book4757 1018 := rows_sound h15 rows4757_16 rowsOk4757_16
  exact book_end h16 _ _ conflict4757
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
