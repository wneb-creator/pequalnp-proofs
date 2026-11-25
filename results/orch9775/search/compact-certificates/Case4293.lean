import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a4293 : Array Fact := #[(.lab 0 0 0),(.lab 0 0 4),(.lab 0 0 5),(.avoid 0 314 0),(.res 0 3),(.res 1 3),(.res 0 5),(.res 1 5),(.res 0 8),(.res 1 8),(.res 0 9),(.res 1 9),(.res 0 10),(.res 1 10),(.lab 1 0 1),(.lab 1 1 1),(.lab 1 2 1),(.lab 1 3 1),(.lab 2 0 2),(.lab 2 0 0),(.avoid 2 8297 0),(.live 3 1),(.lab 3 0 1),(.lab 3 0 5),(.common 3 5),(.lab 3 0 8),(.common 3 8),(.common 3 9),(.common 3 10),(.live 3 2),(.lab 3 1 1),(.lab 3 1 5),(.lab 3 1 8),(.live 3 3),(.lab 3 2 1),(.lab 3 2 5),(.lab 3 2 8),(.lab 3 3 1),(.lab 3 3 5),(.avoid 3 432 0),(.avoid 3 432 1),(.avoid 3 432 2),(.avoid 3 432 3),(.avoid 3 2087 0),(.avoid 3 2087 1),(.avoid 3 2087 2),(.avoid 3 2087 3),(.avoid 3 2338 0),(.avoid 3 2338 1),(.avoid 3 2338 2),(.avoid 3 2338 3),(.see 3 7 127 0),(.see 3 7 127 1),(.see 3 7 127 2),(.see 3 7 127 3),(.see 3 12 314 0),(.see 3 12 314 1),(.see 3 12 314 2),(.see 3 12 314 3),(.see 3 12 8488 0),(.see 3 12 8488 1),(.see 3 12 8488 2),(.see 3 12 8488 3),(.diff 0 3 5),(.diff 1 3 5),(.diff 0 3 8),(.diff 1 3 8),(.lab 4 0 4),(.lab 4 1 4),(.lab 4 2 4),(.lab 4 3 4),(.lab 5 0 5),(.live 5 1),(.lab 5 0 1),(.lab 5 0 3),(.lab 5 0 4),(.lab 5 0 8),(.common 5 8),(.lab 5 1 5),(.live 5 2),(.lab 5 1 1),(.lab 5 1 3),(.lab 5 1 4),(.lab 5 1 8),(.lab 5 2 5),(.live 5 3),(.lab 5 2 1),(.lab 5 2 3),(.lab 5 2 4),(.lab 5 2 8),(.lab 5 3 5),(.avoid 5 541 0),(.avoid 5 541 1),(.avoid 5 541 2),(.avoid 5 541 3),(.avoid 5 792 0),(.avoid 5 792 1),(.avoid 5 792 2),(.avoid 5 792 3),(.avoid 5 1102 0),(.avoid 5 1102 1),(.avoid 5 1102 2),(.avoid 5 1102 3),(.avoid 5 1290 0),(.avoid 5 1290 1),(.avoid 5 1290 2),(.avoid 5 1290 3),(.see 5 12 314 0),(.see 5 12 314 1),(.see 5 12 314 2),(.see 5 12 314 3),(.diff 0 5 3),(.diff 1 5 3),(.diff 0 5 8),(.diff 1 5 8),(.lab 6 0 0),(.lab 6 0 1),(.lab 6 0 2),(.lab 6 0 5),(.avoid 6 314 0),(.avoid 6 541 0),(.lab 7 0 7),(.lab 7 0 11),(.avoid 7 2087 0),(.lab 8 0 8),(.live 8 1),(.lab 8 0 9),(.common 8 9),(.lab 8 0 10),(.lab 8 1 8),(.live 8 2),(.lab 8 1 9),(.lab 8 1 10),(.lab 8 2 8),(.live 8 3),(.lab 8 2 9),(.lab 8 2 10),(.lab 8 3 8),(.avoid 8 1548 0),(.avoid 8 1548 1),(.avoid 8 1548 2),(.avoid 8 1548 3),(.see 8 0 9992 0),(.see 8 0 9992 1),(.see 8 0 9992 2),(.see 8 0 9992 3),(.diff 0 8 9),(.diff 1 8 9),(.lab 9 0 9),(.live 9 1),(.lab 9 0 3),(.lab 9 0 8),(.lab 9 0 10),(.lab 9 1 9),(.live 9 2),(.lab 9 1 3),(.lab 9 1 8),(.lab 9 1 10),(.lab 9 2 9),(.live 9 3),(.lab 9 2 3),(.lab 9 2 8),(.lab 9 3 9),(.avoid 9 314 0),(.avoid 9 314 1),(.avoid 9 314 2),(.avoid 9 314 3),(.avoid 9 1290 0),(.avoid 9 1290 1),(.avoid 9 1290 2),(.avoid 9 1290 3),(.see 9 6 792 0),(.see 9 6 792 1),(.see 9 6 792 2),(.see 9 6 792 3),(.diff 0 9 3),(.diff 1 9 3),(.lab 10 0 10),(.live 10 1),(.lab 10 0 3),(.lab 10 0 8),(.lab 10 1 10),(.live 10 2),(.lab 10 1 3),(.lab 10 1 8),(.lab 10 2 10),(.live 10 3),(.lab 10 2 3),(.lab 10 2 8),(.lab 10 3 10),(.lab 10 3 3),(.lab 10 3 8),(.avoid 10 314 0),(.avoid 10 314 1),(.avoid 10 314 2),(.avoid 10 314 3),(.avoid 10 792 0),(.avoid 10 792 1),(.avoid 10 792 2),(.avoid 10 792 3),(.see 10 0 1290 0),(.see 10 0 1290 1),(.see 10 0 1290 2),(.see 10 0 1290 3),(.diff 0 10 3),(.diff 1 10 3),(.lab 11 0 11),(.lab 11 1 11),(.lab 11 2 11),(.lab 11 3 11),(.lab 12 0 7),(.lab 12 0 9),(.lab 12 0 10),(.lab 12 0 11),(.avoid 12 245 0),(.avoid 12 541 0),(.avoid 12 1102 0),(.avoid 12 2087 0),(.reader false 0 0),(.es false 0 0),(.reader false 1 0),(.es false 1 4),(.es false 1 5),(.reader false 3 0),(.reader false 3 1),(.reader false 3 2),(.reader false 3 3),(.es false 3 1),(.reader false 5 0),(.es false 5 0),(.es false 5 2),(.reader false 7 0),(.reader false 7 1),(.reader false 7 2),(.reader false 7 3),(.reader false 8 0),(.reader false 8 1),(.reader false 8 2),(.reader false 8 3),(.reader false 9 0),(.reader false 9 1),(.reader false 9 2),(.reader false 9 3),(.reader false 10 0),(.reader false 10 1),(.reader false 10 2),(.reader false 10 3),(.es false 10 4),(.reader false 13 0),(.reader false 13 1),(.reader false 13 2),(.reader false 13 3),(.es false 13 1),(.es false 13 5),(.reader false 14 0),(.reader false 14 1),(.reader false 14 2),(.reader false 14 3),(.es false 14 4),(.es false 14 5),(.reader false 15 0),(.reader false 15 1),(.reader false 15 2),(.reader false 15 3),(.reader false 16 0),(.es false 16 0),(.es false 16 2),(.reader false 17 0),(.es false 17 1),(.es false 17 5),(.reader true 0 0),(.reader true 0 1),(.reader true 0 2),(.reader true 0 3),(.reader true 1 0),(.reader true 1 1),(.reader true 1 2),(.reader true 1 3),(.reader true 3 0),(.reader true 3 1),(.reader true 3 2),(.reader true 3 3),(.es true 3 10),(.reader true 5 0),(.reader true 5 1),(.reader true 5 2),(.reader true 5 3),(.reader true 7 0),(.es true 7 7),(.es true 7 11),(.reader true 8 0),(.reader true 8 1),(.reader true 8 2),(.reader true 8 3),(.es true 8 11),(.reader true 9 0),(.es true 9 7),(.es true 9 11),(.reader true 10 0),(.reader true 10 1),(.reader true 10 2),(.reader true 10 3),(.reader true 13 0),(.reader true 13 1),(.reader true 13 2),(.reader true 13 3),(.es true 13 9),(.es true 13 10),(.reader true 14 0),(.reader true 14 1),(.reader true 14 2),(.reader true 14 3),(.es true 14 10),(.reader true 15 0),(.es true 15 9),(.es true 15 10),(.reader true 16 0),(.reader true 16 1),(.reader true 16 2),(.reader true 16 3),(.es true 16 8),(.es true 16 9),(.reader true 17 0),(.reader true 17 1),(.reader true 17 2),(.reader true 17 3),(.es true 17 8),(.es true 17 9),(.gate 0 5),(.gate 0 16),(.gate 1 10),(.gate 1 14),(.gate 3 13),(.gate 3 17),(.gate 5 16),(.gate 7 8),(.gate 7 9),(.gate 8 9),(.gate 10 14),(.gate 13 14),(.gate 13 15),(.gate 13 17),(.gate 14 15),(.gate 16 17)]
def r4293 : List Scheme := [(.self 0 0),(.exposure 0 314),(.avoidNot 0 4 314 0),(.avoidNot 0 5 314 0),(.self 1 0),(.self 1 1),(.self 1 2),(.self 1 3),(.self 2 0),(.exposure 2 8297),(.avoidNot 2 0 8297 0),(.earlier 3 1),(.earlier 3 2),(.someRes 3),(.allRes 3 0),(.allRes 3 1),(.exposure 3 432),(.avoidNot 3 5 432 0),(.avoidNot 3 8 432 0),(.avoidNot 3 5 432 1),(.avoidNot 3 8 432 1),(.avoidNot 3 5 432 2),(.avoidNot 3 8 432 2),(.avoidLive 3 432 3),(.exposure 3 2087),(.avoidNot 3 1 2087 0),(.avoidNot 3 5 2087 0),(.avoidNot 3 1 2087 1),(.avoidNot 3 5 2087 1),(.avoidNot 3 1 2087 2),(.avoidNot 3 5 2087 2),(.avoidLive 3 2087 3),(.avoidNot 3 5 2087 3),(.exposure 3 2338),(.avoidNot 3 5 2338 0),(.avoidNot 3 5 2338 1),(.avoidNot 3 5 2338 2),(.avoidNot 3 1 2338 3),(.exactAt 3 7 127),(.seeLab 3 7 1 127 0),(.seeLab 3 7 5 127 0),(.seeLab 3 7 1 127 1),(.seeLab 3 7 5 127 1),(.seeLab 3 7 1 127 2),(.seeLab 3 7 5 127 2),(.seeLive 3 7 127 3),(.seeLab 3 7 1 127 3),(.seeLab 3 7 5 127 3),(.exactAt 3 12 314),(.seeLab 3 12 8 314 0),(.seeLab 3 12 5 314 1),(.seeLab 3 12 8 314 2),(.seeLive 3 12 314 3),(.exactAt 3 12 8488),(.seeLab 3 12 5 8488 0),(.seeLab 3 12 8 8488 0),(.seeLab 3 12 8 8488 1),(.seeLab 3 12 5 8488 2),(.seeLab 3 12 8 8488 2),(.seeLive 3 12 8488 3),(.diffX 0 3 5),(.diffC 0 3 5),(.diffX 1 3 5),(.diffC 1 3 5),(.adjacentCommon 3 5 12),(.residual 3 5 0 1),(.residual 3 5 0 2),(.residual 3 5 0 3),(.residual 3 5 1 2),(.residual 3 5 1 3),(.residual 3 5 2 3),(.diffX 0 3 8),(.diffC 0 3 8),(.resCommon 3 8 0),(.diffX 1 3 8),(.diffC 1 3 8),(.resCommon 3 8 1),(.residual 3 8 0 1),(.residual 3 8 0 2),(.residual 3 8 1 2),(.resCommon 3 9 0),(.resCommon 3 9 1),(.resCommon 3 10 0),(.resCommon 3 10 1),(.self 4 0),(.self 4 1),(.self 4 2),(.self 4 3),(.self 5 0),(.self 5 1),(.earlier 5 1),(.self 5 2),(.self 5 3),(.someRes 5),(.allRes 5 0),(.allRes 5 1),(.exposure 5 541),(.avoidNot 5 3 541 0),(.avoidNot 5 4 541 0),(.avoidNot 5 3 541 1),(.avoidNot 5 3 541 2),(.avoidNot 5 4 541 2),(.avoidLive 5 541 3),(.exposure 5 792),(.avoidNot 5 3 792 0),(.avoidNot 5 4 792 0),(.avoidNot 5 8 792 0),(.avoidNot 5 3 792 1),(.avoidNot 5 4 792 1),(.avoidNot 5 8 792 1),(.avoidLive 5 792 2),(.avoidNot 5 3 792 2),(.avoidNot 5 4 792 2),(.avoidNot 5 8 792 2),(.avoidLive 5 792 3),(.exposure 5 1102),(.avoidNot 5 1 1102 0),(.avoidNot 5 3 1102 0),(.avoidNot 5 1 1102 1),(.avoidNot 5 3 1102 1),(.avoidNot 5 1 1102 2),(.avoidNot 5 3 1102 2),(.avoidLive 5 1102 3),(.exposure 5 1290),(.avoidNot 5 1 1290 0),(.avoidNot 5 3 1290 1),(.avoidNot 5 3 1290 2),(.avoidLive 5 1290 3),(.exactAt 5 12 314),(.seeLab 5 12 1 314 0),(.seeLab 5 12 3 314 0),(.seeLab 5 12 4 314 0),(.seeLab 5 12 8 314 0),(.seeLab 5 12 1 314 1),(.seeLab 5 12 3 314 1),(.seeLab 5 12 4 314 1),(.seeLab 5 12 8 314 1),(.seeLive 5 12 314 2),(.seeLab 5 12 1 314 2),(.seeLab 5 12 3 314 2),(.seeLab 5 12 4 314 2),(.seeLab 5 12 8 314 2),(.seeLive 5 12 314 3),(.diffC 0 5 3),(.diffC 1 5 3),(.residual 5 3 0 1),(.residual 5 3 0 2),(.residual 5 3 1 2),(.diffX 0 5 8),(.diffC 0 5 8),(.resCommon 5 8 0),(.diffX 1 5 8),(.diffC 1 5 8),(.resCommon 5 8 1),(.residual 5 8 0 1),(.residual 5 8 0 2),(.residual 5 8 1 2),(.exposure 6 314),(.avoidNot 6 1 314 0),(.avoidNot 6 5 314 0),(.exposure 6 541),(.avoidNot 6 0 541 0),(.avoidNot 6 2 541 0),(.self 7 0),(.exposure 7 2087),(.avoidNot 7 11 2087 0),(.self 8 0),(.self 8 1),(.earlier 8 1),(.self 8 2),(.self 8 3),(.allRes 8 0),(.allRes 8 1),(.exposure 8 1548),(.avoidNot 8 9 1548 0),(.avoidNot 8 10 1548 0),(.avoidNot 8 9 1548 1),(.avoidNot 8 10 1548 1),(.avoidLive 8 1548 2),(.avoidNot 8 9 1548 2),(.avoidNot 8 10 1548 2),(.avoidLive 8 1548 3),(.exactAt 8 0 9992),(.seeLab 8 0 9 9992 0),(.seeLab 8 0 10 9992 0),(.seeLab 8 0 9 9992 1),(.seeLab 8 0 10 9992 1),(.seeLive 8 0 9992 2),(.seeLab 8 0 9 9992 2),(.seeLab 8 0 10 9992 2),(.seeLive 8 0 9992 3),(.diffX 0 8 9),(.diffC 0 8 9),(.diffX 1 8 9),(.diffC 1 8 9),(.adjacentCommon 8 9 6),(.residual 8 9 0 1),(.residual 8 9 0 2),(.residual 8 9 1 2),(.self 9 0),(.self 9 1),(.earlier 9 1),(.self 9 2),(.earlier 9 2),(.self 9 3),(.someRes 9),(.allRes 9 0),(.allRes 9 1),(.exposure 9 314),(.avoidNot 9 3 314 0),(.avoidNot 9 3 314 1),(.avoidNot 9 8 314 2),(.avoidLive 9 314 3),(.exposure 9 1290),(.avoidNot 9 3 1290 0),(.avoidNot 9 8 1290 0),(.avoidNot 9 10 1290 0),(.avoidNot 9 3 1290 1),(.avoidNot 9 8 1290 1),(.avoidNot 9 10 1290 1),(.avoidLive 9 1290 2),(.avoidNot 9 3 1290 2),(.avoidLive 9 1290 3),(.exactAt 9 6 792),(.seeLab 9 6 3 792 0),(.seeLab 9 6 8 792 0),(.seeLab 9 6 3 792 1),(.seeLab 9 6 8 792 1),(.seeLab 9 6 3 792 2),(.seeLab 9 6 8 792 2),(.seeLive 9 6 792 3),(.diffX 0 9 3),(.diffC 0 9 3),(.diffX 1 9 3),(.diffC 1 9 3),(.residual 9 3 0 1),(.residual 9 3 0 2),(.residual 9 3 1 2),(.self 10 0),(.self 10 1),(.earlier 10 1),(.self 10 2),(.earlier 10 2),(.self 10 3),(.someRes 10),(.allRes 10 0),(.allRes 10 1),(.exposure 10 314),(.avoidNot 10 3 314 0),(.avoidNot 10 8 314 0),(.avoidNot 10 3 314 1),(.avoidNot 10 3 314 2),(.avoidLive 10 314 3),(.avoidNot 10 3 314 3),(.avoidNot 10 8 314 3),(.exposure 10 792),(.avoidNot 10 3 792 0),(.avoidNot 10 3 792 1),(.avoidNot 10 8 792 1),(.avoidNot 10 3 792 2),(.avoidNot 10 8 792 2),(.avoidLive 10 792 3),(.avoidNot 10 3 792 3),(.exactAt 10 0 1290),(.seeLab 10 0 3 1290 0),(.seeLab 10 0 8 1290 0),(.seeLab 10 0 3 1290 1),(.seeLab 10 0 8 1290 1),(.seeLab 10 0 3 1290 2),(.seeLab 10 0 8 1290 2),(.seeLive 10 0 1290 3),(.seeLab 10 0 3 1290 3),(.seeLab 10 0 8 1290 3),(.diffC 0 10 3),(.diffC 1 10 3),(.residual 10 3 0 1),(.residual 10 3 0 2),(.residual 10 3 0 3),(.residual 10 3 1 2),(.residual 10 3 1 3),(.residual 10 3 2 3),(.self 11 0),(.self 11 1),(.self 11 2),(.self 11 3),(.exposure 12 245),(.avoidNot 12 7 245 0),(.exposure 12 541),(.avoidNot 12 9 541 0),(.exposure 12 1102),(.avoidNot 12 10 1102 0),(.exposure 12 2087),(.avoidNot 12 11 2087 0),(.readerAny false 0),(.readerLab false 0 0 0 true),(.readerAny false 1),(.readerLab false 1 0 4 false),(.readerLab false 1 0 5 false),(.readerAny false 3),(.readerLab false 3 0 1 true),(.readerLab false 3 1 1 true),(.readerLab false 3 2 1 true),(.readerLab false 3 3 1 true),(.readerAny false 5),(.readerLab false 5 0 0 false),(.readerLab false 5 0 2 true),(.readerAny false 7),(.readerLive false 7 2),(.readerLive false 7 3),(.readerAny false 8),(.readerLive false 8 2),(.readerLive false 8 3),(.readerAny false 9),(.readerLive false 9 2),(.readerLive false 9 3),(.readerAny false 10),(.readerLab false 10 0 4 true),(.readerLab false 10 1 4 true),(.readerLab false 10 2 4 true),(.readerLab false 10 3 4 true),(.readerAny false 13),(.readerLab false 13 0 1 false),(.readerLab false 13 0 5 true),(.readerLab false 13 1 1 false),(.readerLab false 13 1 5 true),(.readerLive false 13 2),(.readerLab false 13 2 1 false),(.readerLab false 13 2 5 true),(.readerLive false 13 3),(.readerLab false 13 3 5 true),(.readerAny false 14),(.readerLab false 14 0 4 false),(.readerLab false 14 0 5 true),(.readerLab false 14 1 4 false),(.readerLab false 14 1 5 true),(.readerLive false 14 2),(.readerLab false 14 2 4 false),(.readerLab false 14 2 5 true),(.readerLive false 14 3),(.readerLab false 14 3 5 true),(.readerAny false 15),(.readerLive false 15 2),(.readerLive false 15 3),(.readerAny false 16),(.readerLab false 16 0 0 false),(.readerLab false 16 0 2 false),(.readerAny false 17),(.readerLab false 17 0 1 false),(.readerLab false 17 0 5 false),(.readerAny true 0),(.readerLive true 0 2),(.readerLive true 0 3),(.readerAny true 1),(.readerLive true 1 2),(.readerLive true 1 3),(.readerAny true 3),(.readerLab true 3 0 10 false),(.readerLab true 3 1 10 false),(.readerLive true 3 2),(.readerLive true 3 3),(.readerAny true 5),(.readerLive true 5 2),(.readerLive true 5 3),(.readerAny true 7),(.readerLab true 7 0 7 true),(.readerLab true 7 0 11 false),(.readerAny true 8),(.readerLab true 8 0 11 true),(.readerLab true 8 1 11 true),(.readerLab true 8 2 11 true),(.readerLab true 8 3 11 true),(.readerAny true 9),(.readerLab true 9 0 7 false),(.readerLab true 9 0 11 false),(.readerAny true 10),(.readerLive true 10 2),(.readerLive true 10 3),(.readerAny true 13),(.readerLab true 13 0 9 true),(.readerLab true 13 1 9 true),(.readerLive true 13 2),(.readerLab true 13 2 9 true),(.readerLive true 13 3),(.readerLab true 13 3 9 true),(.readerAny true 14),(.readerLab true 14 0 10 true),(.readerLab true 14 1 10 true),(.readerLive true 14 2),(.readerLab true 14 2 10 true),(.readerLive true 14 3),(.readerLab true 14 3 10 true),(.readerAny true 15),(.readerLab true 15 0 9 false),(.readerLab true 15 0 10 false),(.readerAny true 16),(.readerLab true 16 0 8 true),(.readerLab true 16 0 9 false),(.readerLab true 16 1 8 true),(.readerLive true 16 2),(.readerLab true 16 2 8 true),(.readerLab true 16 2 9 false),(.readerLive true 16 3),(.readerLab true 16 3 8 true),(.readerAny true 17),(.readerLab true 17 0 8 false),(.readerLab true 17 0 9 true),(.readerLab true 17 1 8 false),(.readerLab true 17 1 9 true),(.readerLive true 17 2),(.readerLab true 17 2 9 true),(.readerLive true 17 3),(.readerLab true 17 3 9 true),(.eqLab false 0 5 0 true),(.gateEq true 0 5 0),(.eqLab false 0 16 0 true),(.gateEq true 0 16 1),(.eqLab false 1 10 4 false),(.gateEq true 1 10 0),(.gateEq true 1 10 1),(.eqLab false 1 14 5 false),(.gateEq true 1 14 0),(.gateEq true 1 14 1),(.eqLab false 3 13 1 true),(.gateEq true 3 13 0),(.gateEq true 3 13 1),(.eqLab true 3 13 10 false),(.eqLab false 3 17 1 true),(.gateEq true 3 17 0),(.gateEq true 3 17 1),(.eqLab false 5 16 2 true),(.gateEq true 5 16 1),(.gateEq false 7 8 0),(.gateEq false 7 8 1),(.eqLab true 7 8 11 false),(.gateEq false 7 9 0),(.gateEq false 7 9 1),(.eqLab true 7 9 7 true),(.gateEq false 8 9 0),(.gateEq false 8 9 1),(.eqLab true 8 9 11 true),(.eqLab false 10 14 4 true),(.gateEq true 10 14 0),(.gateEq true 10 14 1),(.gateEq false 13 14 0),(.gateEq false 13 14 1),(.gateEq false 13 14 2),(.eqLab true 13 14 10 false),(.gateEq false 13 15 0),(.gateEq false 13 15 1),(.eqLab true 13 15 9 true),(.eqLab false 13 17 5 true),(.gateEq true 13 17 0),(.gateEq true 13 17 1),(.gateEq false 14 15 0),(.gateEq false 14 15 1),(.eqLab true 14 15 10 true),(.gateEq false 16 17 0),(.eqLab true 16 17 8 true),(.eqLab true 16 17 9 false)]

def table4293_0 : List Nat := [65,449,0x20182,0x40182,0x741,0x7c1,0x841,0x8c1,0x941,0xa41,0x260a02,0x2b0e82,0x3b1082,0x2c090e83,0x91082,0xb1082]
def table4293_1 : List Nat := [0x5514c5113c4,0x2e1382,0x321382,0x3e1402,0x401402,0x461482,0x481482,0x431502,0x5d16c5915c4,0x2c1582,0x2e1582,0x3c1602,0x3e1602,0x441682,0x461682,0x431702]
def table4293_2 : List Nat := [0x4c1702,0x6518c6117c4,0x2e1782,0x3e1802,0x461882,0x4a1902,0x6d1ac6919c4,0x2d1982,0x2e1982,0x3d1a02,0x3e1a02,0x451a82,0x461a82,0x431b02,0x4b1b02,0x4c1b02]
def table4293_3 : List Nat := [0x751cc711bc4,0x321b82,0x3f1c02,0x481c82,0x431d02,0x7d1ec791dc4,0x2f1d82,0x321d82,0x401e02,0x471e82,0x481e82,0x431f02,0x91f82,0xc1f82,0xb2002,0xe2002]
def table4293_4 : List Nat := [0xc41,0x811fc3f0bc2a0c06,0x811fc470bc3a0c06,0x811fc4d0bc420c06,0x811fc470fc3a0c06,0x811fc4d0fc420c06,0x811fc4d11c420c06,0x92082,0x102082,0xd4100203,0xb2102,0x122102,0xd4120283,0x8520c410cc2a0d06,0x8520c490cc3a0d06,0x8520c491043a0d06]
def table4293_5 : List Nat := [0xdc140203,0xdc160283,0xe4180203,0xe41a0283,0x21c1,0x2241,0x22c1,0x2341,0x23c1,0x2741,0x912782,0x2a41,0x2d41,0x3c0d2783,0xd2a82,0xf2a82]
def table4293_6 : List Nat := [0xbd2ecb92dc4,0x942d82,0x962d82,0xa22e02,0xae2e82,0xb02e82,0xab2f02,0xc530cc12fc4,0x942f82,0x962f82,0x982f82,0xa23002,0xa43002,0xa63002,0x9f3082,0xae3082]
def table4293_7 : List Nat := [0xb03082,0xb23082,0xab3102,0xcd32cc931c4,0x923182,0x943182,0xa03202,0xa23202,0xac3282,0xae3282,0xab3302,0xd534cd133c4,0x923382,0xa23402,0xae3482,0xab3502]
def table4293_8 : List Nat := [0xdd36cd935c4,0x923582,0x953582,0x963582,0x983582,0xa03602,0xa33602,0xa43602,0xa63602,0x9f3682,0xac3682,0xaf3682,0xb03682,0xb23682,0xab3702,0x83782]
def table4293_9 : List Nat := [0xa3802,0xe137ca3254900c06,0xe137caf2549e0c06,0xe137caf28c9e0c06,0xd3882,0x103882,0x26c100303,0xf3902,0x123902,0x26c120383,0xe538ca7264902686,0xe538cb32649e2686,0xe538cb329c9e2686,0x3bc1,0xe83b82,0xec3b82]
def table4293_10 : List Nat := [0x3c41,0xe63c02,0xea3c02,0x3cc1,0x3dc1,0xf43d82,0x3e41,0x40c1,0xfb4102,0x42c1,0x44c1,0x114302,0x134302,0x11b465174544,0xfc4502,0x1004502]
def table4293_11 : List Nat := [0x1064582,0x1084582,0x1054602,0x10e4602,0x1104602,0x10d4682,0x1234851f4744,0xfc4702,0x1014702,0x1064782,0x1094782,0x1054802,0x10e4802,0x1114802,0x10d4882,0x114902]
def table4293_12 : List Nat := [0x144902,0x134982,0x164982,0x3fc1,0x127495073f4fa3f86,0x1274950f3f5043f86,0x1274950f41d043f86,0x4a41,0x4cc1,0x12b4d02,0x4f41,0x1354f82,0x5141,0x5c154d03,0x154f82,0x174f82]
def table4293_13 : List Nat := [0x14d52d4951c4,0x12c5182,0x1365202,0x1425282,0x13f5302,0x15554d5153c4,0x12c5382,0x12e5382,0x1305382,0x1365402,0x1385402,0x13a5402,0x1355482,0x1405482,0x13f5502,0x15d56d5955c4]
def table4293_14 : List Nat := [0x12c5582,0x12f5582,0x1365602,0x1395602,0x1405682,0x1435682,0x13f5702,0x155782,0x85782,0x175802,0xa5802,0x16157d374b52a0d86,0x16157d414b5340d86,0x16157d414dd340d86,0x58c1,0x5ac1]
def table4293_15 : List Nat := [0x1655b02,0x5cc1,0x16d5d02,0x5ec1,0x6c195b03,0x195d02,0x1b5d02,0x187615836044,0x1666002,0x1686002,0x16e6082,0x1766102,0x1756182,0x17c6182,0x17e6182,0x18f6358b6244]
def table4293_16 : List Nat := [0x1666202,0x16e6282,0x1706282,0x1766302,0x1786302,0x1756382,0x17c6382,0x197655936444,0x1666402,0x1696402,0x16e6482,0x1716482,0x1766502,0x1796502,0x1756582,0x17c6582]
def table4293_17 : List Nat := [0x17f6582,0x86602,0xa6682,0x19b6656f59d640e06,0x19b6657759d6c0e06,0x19b6657d59d740e06,0x19b665775bd6c0e06,0x19b6657d5bd740e06,0x19b6657d5dd740e06,0x6741,0x67c1,0x6841,0x68c1,0x6b41,0x1a46b02,0x6bc1]
def table4293_18 : List Nat := [0x1a66b82,0x6c41,0x1a86c02,0x6cc1,0x1aa6c82,0x6d41,0x6dc006d03,0x6e41,0x6e8036e03,0x6f0056e03,0x1c570dc16fc4,0x71c1c6f83,0x71c1e7003,0x71c207083,0x71c227103,0x7241]
def table4293_19 : List Nat := [0x728277203,0x734247203,0x1d574dd173c4,0x3b7482,0x437502,0x1dd76dd975c4,0x3b7682,0x437702,0x1e578de177c4,0x3b7882,0x437902,0x1ed7ade979c4,0x7bc867983,0x7bc887a03,0x7bc8a7a83,0x7bc8c7b03]
def table4293_20 : List Nat := [0x1f77d5f37c44,0x7e0937c03,0x7ec8e7c03,0x7e0a17c83,0x7ec9c7c83,0x9f7d02,0x7e0ad7d03,0x7eca87d03,0xab7d82,0x7ecb47d83,0x203805ff7f44,0x810977f03,0x81c8e7f03,0x810a57f83,0x81c9c7f83,0x9f8002]
def table4293_21 : List Nat := [0x810b18003,0x81ca88003,0xab8082,0x81cb48083,0x20f8360b8244,0x9f8302,0xab8382,0x8441,0x848e78403,0x850eb8403,0x85c1,0x860e98583,0x868ed8583,0x2238861f8744,0x1058802,0x10d8882]
def table4293_22 : List Nat := [0x22b8a6278944,0x16d8a02,0x1758a82,0x2338c62f8b44,0x8d1318b03,0x8d13b8b83,0x1358c02,0x13f8c82,0x23d8ee398dc4,0x1058e82,0x10d8f02,0x8fc1,0x904f28f83,0x908f58f83,0x24b926479144,0x9359c9103]
def table4293_23 : List Nat := [0x9359e9183,0x935a09203,0x935a29283,0x93c1,0x941a59383,0x949ab9383,0x25b966579544,0x16d9602,0x1759682,0x2639865f9744,0x995289703,0x995329783,0x1359802,0x9953c9803,0x13f9882,0x995449883]
def table4293_24 : List Nat := [0x26f9b66b9a44,0x9c5629a03,0x9c56a9a83,0x16d9b02,0x9c5729b03,0x1759b82,0x9c57a9b83,0x9cc1,0x9d1a79c83,0x9d9a99c83,0x27f9f67b9e44,0xa04f89e03,0xa08fd9e03,0xa05029e83,0x1059f02,0xa050a9f03]
def table4293_25 : List Nat := [0xa090f9f03,0x10d9f82,0xa05129f83,0x28ba2687a144,0xa312fa103,0xa3d28a103,0xa3139a183,0xa3d32a183,0x135a202,0xa3d3ca203,0x13fa282,0xa3d44a283,0x72db6a403,0xa46368703,0x84db6a483,0xa4e7a8783]
def table4293_26 : List Nat := [0x7b9bba503,0xa56548903,0xa56568983,0x819bda583,0xa5e688903,0xa5e6a8983,0x7e5c6a603,0xa665c8b03,0xa665e8b83,0x99a35a603,0x865c6a683,0xa6e848b03,0xa6e868b83,0x855cca703,0xa767a8e03,0xa7dd67383]
def table4293_27 : List Nat := [0xa7dd87403,0x93243a783,0xa85de7383,0xa85e07403,0x94640a803,0xa8dde7583,0xa8de07603,0x94e4ca883,0x815eea903,0xa96689503,0xa966a9583,0xa9dfc7c03,0xa9dfe7c83,0xa9e007d03,0x9c267a983,0xaa6087c03]
def table4293_28 : List Nat := [0xaa60a7c83,0x9d664aa03,0x86dfaaa83,0xaae849703,0xaae869783,0xab6087f03,0xab60a7f83,0x9de70ab03,0xabe168403,0xa3680ab83,0xa3a83ab83,129,257,0x981,0x2047f0fc2f0a85,0x2047f11c2f0e85]
def table4293_29 : List Nat := [0x2047f1342f1085,0x2047f11c3f0e85,0x2047f1343f1085,0x2047f134471085,0x384df28c952405,0x384df2bc952785,0x384df2bca32785,0x3a01,0x3b01,0x3981,0x3a81,0x3d01,0x49d2541cfd3e85,0x49d2543cfd4105,0x49d2543d074105,0x6901]
def table4293_30 : List Nat := [0x6981,0x6a01,0x6a81,0x6dc1,0x6e81,0x6f01,0x1c76f82,0x1c77002,0x1c77082,0x1c77102,0x7281,0x7341,0x1ef7982,0x1ef7a02,0x1ef7a82,0x1ef7b02]
def table4293_31 : List Nat := [0x1fb7c02,0x1fb7c82,0x1fb7d02,0x1fb7d82,0x2077f02,0x2077f82,0x2078002,0x2078082,0x8481,0x8501,0x8601,0x8681,0x9041,0x9081,0x24d9102,0x24d9182]
def table4293_32 : List Nat := [0x24d9202,0x24d9282,0x9401,0x9481,0x2659702,0x2659782,0x2659802,0x2659882,0x2719a02,0x2719a82,0x2719b02,0x2719b82,0x9d01,0x9d81,0x2819e02,0x2819e82]
def table4293_33 : List Nat := [0x2819f02,0x2819f82,0x28fa102,0x28fa182,0x28fa202,0x28fa282,0xa401,0x2368702,0xa481,0x27a8782,0x1eea502,0x206a582,0x1c6a682,0xa701,0x27a8e02,0x24ca782]
def table4293_34 : List Nat := [0xa801,0x24ca882,0x264aa02,0x1faaa82,0x270ab02,0xabc1,0x28da002,0x28ea0c2,0x9c41,0xab01,0x7ec1,0xaa81,0x9941,0xaa01,0x9341,0xa781]
def table4293_35 : List Nat := [0xa881,0x71c1,0xa681,0x81c1,0xa581,0x7bc1,0xa501,0x16c6643866d976006,0x755dd74ddb7805,0x395d02,0x550e883214341e86,0x4350e3f03,0x13a09259f04,0x4367a4143,0x13a09254704,0x55614d0365045]
def table4293_36 : List Nat := [0x155852a0d95b5386,0x540a4d03,0x10c460f83,0x1149d0441c4,0x1149d044804,0x45274103,0x21434024711dc2a0e87,0x430ec2,0x90d0851d84,0x24342143,0xa3c1,0xa0c1,0x130442,0x10d4142,0xaba9c9f8204,0x2aea727c3]
def table4293_37 : List Nat := [0x38c0f2789a3605,0x38c0f2789a3585,0x400f2783,0x23398e3198699a106,0x8ce63a2e3198689a647,0x5563354e318d28ca187,0x1558ce8b54e31a2634a308,0x28139990743c5,0xa04e6641c4,0x27fa042,0xa32664d43,0x28139983,0x4d254803,0x134942,0x42a703c3,0x10c460b83]
def table4293_38 : List Nat := [0x24810fc3,0x92042,0x10c3e0b83,0x904c2,0x90e82,577,0x3781,0x5781,0x6601,0x3940f2789a38c5,0x214340e8511544120c7,0x2a55d56d9a04,0xa95755b43,0x296c0e43,0x19b63d975b0385bc6,0x2aa55d43]
def table4293_39 : List Nat := [0x66d7462d896505,0x19b5d16e5984,0x66d745b83,0x19b5d02,0xa2aea77e0d92f86,0x810aba9df87fdf33687,0xa2aea77e0d93006,0x28aba9df83645,0x810aba9cdb7e2017c07,0x810aba9cdb7e2017c87,0x1fc0b0f83,0x7f02c2,0x2042aea7384db7e0b9325ff804a,0x2042aea7028db7e06,0x4fe994d43,0x5855d4d0365405]
def table4293_40 : List Nat := [0x5855d4d0365385,0x293f4d03,0x2ae0402aa77e05,0x280fa9c3,0xa041,0xa341,0x1270442,0x811f8314dd80e0f30cdb8060d7c0b,0x29f803c3,0x3949a38c993085,0xa314cd376033949a38cdb280a,0x2047e0ab36df327c6,0x314e5268e3240c33607,0xc5374e5268e336c9030c8,0xa7e0ab36c4,0x29f82ac3]
def table4293_41 : List Nat := [0x278c530cb3268e538c7,0x3883a0fc3,0xf82e1183,0xe20f8420b84,0x3883a1083,0xe20e82,0xec1,0xac1,0x3881,0x54ab0283,0xe41442f11c4,0x3903e0bc3,0xe40f82,0xfc811fc3,0x3904f1443,0xe41042]
def table4293_42 : List Nat := [0x3901,0x9e26c0a0344,0x2789b0283,0x43144791204,0x43144850d0831e46,0x10c512143420c5,0x9e26c2,0x2047f10c3,0x2047f0bc3,0x811fc2,0x278c530c3,0x9e3082,0x9e2682,0x2781,0x3081,0x3681]
def table4293_43 : List Nat := [0x8001,0x203294978104,0x2a50282,0x13405c2,0x1002c2,0x314ab3603,0xc52ac2,0x2a81,0x3101]

def encoded4293 (i : Nat) : Nat :=
  if i < 352 then
    if i < 176 then
      if i < 80 then
        if i < 32 then
          if i < 16 then
            table4293_0.getD (i%16) 0
          else
            table4293_1.getD (i%16) 0
        else
          if i < 48 then
            table4293_2.getD (i%16) 0
          else
            if i < 64 then
              table4293_3.getD (i%16) 0
            else
              table4293_4.getD (i%16) 0
      else
        if i < 128 then
          if i < 96 then
            table4293_5.getD (i%16) 0
          else
            if i < 112 then
              table4293_6.getD (i%16) 0
            else
              table4293_7.getD (i%16) 0
        else
          if i < 144 then
            table4293_8.getD (i%16) 0
          else
            if i < 160 then
              table4293_9.getD (i%16) 0
            else
              table4293_10.getD (i%16) 0
    else
      if i < 256 then
        if i < 208 then
          if i < 192 then
            table4293_11.getD (i%16) 0
          else
            table4293_12.getD (i%16) 0
        else
          if i < 224 then
            table4293_13.getD (i%16) 0
          else
            if i < 240 then
              table4293_14.getD (i%16) 0
            else
              table4293_15.getD (i%16) 0
      else
        if i < 304 then
          if i < 272 then
            table4293_16.getD (i%16) 0
          else
            if i < 288 then
              table4293_17.getD (i%16) 0
            else
              table4293_18.getD (i%16) 0
        else
          if i < 320 then
            table4293_19.getD (i%16) 0
          else
            if i < 336 then
              table4293_20.getD (i%16) 0
            else
              table4293_21.getD (i%16) 0
  else
    if i < 528 then
      if i < 432 then
        if i < 384 then
          if i < 368 then
            table4293_22.getD (i%16) 0
          else
            table4293_23.getD (i%16) 0
        else
          if i < 400 then
            table4293_24.getD (i%16) 0
          else
            if i < 416 then
              table4293_25.getD (i%16) 0
            else
              table4293_26.getD (i%16) 0
      else
        if i < 480 then
          if i < 448 then
            table4293_27.getD (i%16) 0
          else
            if i < 464 then
              table4293_28.getD (i%16) 0
            else
              table4293_29.getD (i%16) 0
        else
          if i < 496 then
            table4293_30.getD (i%16) 0
          else
            if i < 512 then
              table4293_31.getD (i%16) 0
            else
              table4293_32.getD (i%16) 0
    else
      if i < 608 then
        if i < 560 then
          if i < 544 then
            table4293_33.getD (i%16) 0
          else
            table4293_34.getD (i%16) 0
        else
          if i < 576 then
            table4293_35.getD (i%16) 0
          else
            if i < 592 then
              table4293_36.getD (i%16) 0
            else
              table4293_37.getD (i%16) 0
      else
        if i < 656 then
          if i < 624 then
            table4293_38.getD (i%16) 0
          else
            if i < 640 then
              table4293_39.getD (i%16) 0
            else
              table4293_40.getD (i%16) 0
        else
          if i < 672 then
            table4293_41.getD (i%16) 0
          else
            if i < 688 then
              table4293_42.getD (i%16) 0
            else
              table4293_43.getD (i%16) 0
def book4293 (i : Nat) : Clause := let n := encoded4293 i; unpackLits 10 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses4293 : inputsOK 2 4293 a4293 r4293 (baseBook book4293 459).toList=true := by decide +kernel

def rows4293_0 : List Nat := [0x80401,0x80601,0x481401,0x2008201,0x2008401,0x2008601,0x2008801,0x2008a01,0x2008c01,0x2012201,0x2012401,0x2012601,0x4e93c01,0x4e93e01,0x5014201,0x5014401,0x5214a01,0x6198801,0x6198a01,0x6198c01,0x8ea3c01,0x8fa4001,0x90a4401,0x91a4801]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4293_0 : checkRows book4293 10 459 rows4293_0=true := by decide +kernel

def rows4293_1 : List Nat := [0x92a4c02,0x39693a5002,0x39893a5202,0x225601,0x2a5801,0x325a01,0x3a5c01,0x39a97a6002,0x1097a6202,0x2a27801,0x2aa7a01,0x2b27c01,0x2ba7e01,0x2c28401,0x2ca8801,0x2da8e01,0x2e29201,0x2c29801,0x2ca9c01,0x2daa201,0x2e2a601,0x3b2abab002,0x3b4abab202,0x3aead2b602]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4293_1 : checkRows book4293 10 483 rows4293_1=true := by decide +kernel

def rows4293_2 : List Nat := [0x3b0ad2b802,0x146b5ad802,0x3b6b5ada02,0x8cade01,0x8d2e001,0x8dae201,0x8e2e401,0x3beb9ae802,0x3c4b9aea02,0x63af401,0x642f601,0x652fa01,0x662fe01,0x7730201,0x77b0401,0x78b0801,0x79b0c01,0x3c0c3b1002,0x3c2c3b1202,0x5331601,0x53b1a01,0x54b1e01,0x5532401,0x63b2a01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4293_2 : checkRows book4293 10 507 rows4293_2=true := by decide +kernel

def rows4293_3 : List Nat := [0x6432e01,0x6533201,0x6633601,0x3d4f1b3802,0x10b33a01,0x3f0f1b3c02,0x10c33e01,0xf234001,0xf2b4601,0xfd35401,0x3f2f5b5a02,0x10eb5c01,0xfeb6201,0x404fe36802,0x101b6e01,0x10638201,0xfdb8401,0x106b8e01,0x2b4abb9002,0x112b9201,0x112b9401,0x417054130430004,0x11444801,0x3e6f93e2f828004]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4293_3 : checkRows book4293 10 531 rows4293_3=true := by decide +kernel

def rows4293_4 : List Nat := [0x11544601,0x40f0340b022f204,0x11644401,0x403003feff2dc04,0x11743e01,0x11744201,0x3d2f43cef325404,0x118c3801,0x3eefb3eafa29404,0x119c3601,0x3def73daf627604,0x11ac3401,0x218852128a2267c9f07820e08,0x9aa64db36717c611035e07,0x9aa64dab649c4709ca6c99a749ba680681c298a47b1eb17c611036015,0x90282709e0a8741c82007,0x5896c5696e5716a5f1665e17409,0x15e5b15a5c960ee4765e16654320c71825a97c5617010,0x2d0aead2af2beb54330f42e08,0x16059bb8ee9511eb1457b185c16e6096ac89591e15a10,0x699be681c4691c0689da761ce6a1cc671ca0d,0x1c4709d66b9ac739cc671be08,0x1c0719d66d1b26ac80721bb1f8a266992739bc7319c751be12,0xc84c0c0540e03e1683c1604e09]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4293_4 : checkRows book4293 10 555 rows4293_4=true := by decide +kernel

def rows4293_5 : List Nat := [0xef3b85597e5447605,0x15c5a3ba5e9785f96a559612195a0a,0x16657bba5c16e5b4885c9612197e5a97c5595a0e,0x661889e268701ac742382e1a076070600c,0x9aa64dab649c4709ca6c99a689ba7517c61103600f,0x2c0a09c268221b86c2382e05c8e070200c,0xb0242789a098701906b234911d08e0b87605c8e0702011,0x42b0a4270932604,0x12544e01,0x57162c6174c516d1e9765947d1e48a5f9825a97cc89592595a13,0x5896c5696e57318c547ac71765916a5f323259740f,0x294a038adfa90a928aa7c5316b780a,0x294a038ce02a9272aaa7a8aa42a4ab45316b760e,0x350e24d138359104312e390be2d0ce0b,0x388da4d934341084112e390be2d0ce0b,0x350da4d9383791a4590128ca04b0ba4a92e3911c2f8ce11,0x2f2b1b86d5c571935006,0x2f2b1b88d632729c571934e08,0xb21aab19b4d632d191b007,0xb29aab19aed5b28c9cab191b609,0x41f0744d2b3532a330be2cc6e334bf2ce6f48267180c83bc60b232695925b1418,0x10841f134acd4ca8cc2f8b31b8cd2fcb39bd2099c603b8c64772b982c89512695925b141b,0x10841f0731403,0x12b4a8cd2fcb39bccc2f8b31b865b520b]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4293_5 : checkRows book4293 10 579 rows4293_5=true := by decide +kernel

def rows4293_6 : List Nat := [0x15c5a3ba5e9785b47c604832d172584b06096a5f49b134b2c89592595a16,0x5815c5a3bcee97a5e1825ac9a5615a0b,0x3b8ef1725b4b91f1825f1512695925c760c,0x4a42fc9e02,0xd84c0c0500d03e1683c1605209,0x4bee887805c8e0739c06,0xe84c0c0500d39f210540e4c01e03e16c8e070560f,0xe84c0c0500d03e168381505609,0x12f4b72601b2381c1fcc31437c09,0x9825cc606c9204,0x48e074c802,0x13291e01,0x1329d001,0x132a2201,0x350da4d9383791a4590128ca03911c2f8ce0d,0xb0242789a0582005,0x2ecb0372d22c4bc2c2bbc6d1a3440a,0x2ecb0374d2b0135b06bbac2b12f0c2c6d1a3420e,0x290a7329e803,0x8120e7fa1881a108022c899e1342160b,0x208839fe842008a1f67ba14809f53746f36cd88720a7e2253421a14,0x832088c21a86473341fe07,0x7d9fc8c22087a0f38210801f11c9f480a15341ee0f,0x7ba1e7e9f68aa29389f4794733446e0b]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4293_6 : checkRows book4293 10 603 rows4293_6=true := by decide +kernel

def rows4293_7 : List Nat := [0x87a0c8bce51c9e5344dc07,0xa8296de280a08e8a30e6461143c8ee403aaea104348d04837137ce6890f447290a90b527ccd1aa941f,0x294a02a0a311845290a937608,0xa5280a5a8241902404eaa18ec398ea3ca9aea3ac360d64837137ce6890f447290a90b527ccd1ab7a1f,0x378a32943c296a08e6419023b8ea402a0eb3aa458e0378cf3b4e84837137ce6890e43d11ca42a527ccd1aa8022,0x29a4029440b76a091ca910e08,0x2964029442b78a191ca910608,0x1314841f48e07b9e05,0xe8b9d3d0172387c07cbe07,0xc8313aaa58eaa50e63c28ca04f33c0cc3d290a949f330c012,0xf6ea8f830a823028032b7aa82873e29a3e8ee3190e4310b3b8cc3fa9127921330fc1a,0x330be2ccb3afccd4a806,0x721c0719da759b46c993339be09,0x721c4709d8759ae6b193339be09,0x729a06f9c4691c0689da761ba6ad013f8a1209d46a1bc734cf329a615,0x29aa190e42cef3ecea06,0x34d3f5026798522c9a55cbcdc4df39a242fc631ad0410,0x108cb201,0x14244c01,0x48a55c9a02,0x33a9635a944338c402a840b7ea0c53168d20d,0x33a9a342944138a402a842b80a1a8143aaaa7a8a448dd2950c6119f40cb4df2aca9290470e5418bedc4df39a2514c5b42c511a8d829,0xe23713602,0xa7a9aeb0d8358cf448f239a963a8d04210641100428ec4837137ce6894cd1aa9419]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4293_7 : checkRows book4293 10 627 rows4293_7=true := by decide +kernel

def rows4293_8 : List Nat := [0x280aaa9ea28dc3911ca42a4ab50e0a,0x3393435910430d405,0x339343410841101460da07,0x441084e51238d1a2d516a1d14390f4472a44c1332dd104ad0c6119f40cb4df504dc4df39a2542c511a90021,0x350da4d9383791a459134712b4318467d024c9312d4b6df5043937137ce68951142c511a8ce1d,0xda351384d8ce04,0x361303017840e94be1603c14034e8b9c1fd06df4b54099e6150c4acf61e92805c51428521c,0x1284c1085812046150441405c09,0xe84c0c05e103a7490500d07f41b7d2d502679854312b3d87a4a038154514285619,0xc84c0c05e100580f3a0e7d261fd06df4b54099e6150c4acf61e9280e05548c514284e1b,0x4c5215294887f41b7d2d502679854312b3d87a4a45142b9e12,0x648e01,0x14b01601,0x14b52a01,0x13f51f2099d18b4c05,0x6b350760b89407d322f07ae78721f92e24093261812e9301b52d3287016,0x321303017840e807a2f53207c841603d4d07e4b9812e930098381504e16,0x3a1303017840e987a2f53207d25310500d536150381f92e604ba4c05616,0xd84c0c05e103a52f8580f0500d3a2e752f4b0520f,0x6a270700b4d4080771d02e078954c8bc1ed3a1f92f4e1812e892244984c52d3286e1a,0x621989a2789024c98190941a01f4c8bc1ed3a1f92f4e1812e9314bd2d3286018,0x221ad3c1c0294fc741d82e2501f4c8bc1ed3b4e180248912ec981f9304bd2d3286c1a,0x601334c8ba2f4ba05,0x37c4ccb54099e6150d2612d50d0b145060c]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4293_8 : checkRows book4293 10 651 rows4293_8=true := by decide +kernel

def rows4293_9 : List Nat := [0x886a080740b02e1d86c07,0x2706b518771d02f4b06e07,0x4d55202f4b07004,0x621989a278640a0275289424891261321a0ba1ecf607d4532d2d4b86016,0x4c52153b4b39e04,0x3213030178401603ce839e0e0554ed4f4b04e0e,0x3a1303017840e9d24140355454e150394e8560e,0x51b480b4470bc1ed521fcd3535414c11a0c,0x1104213845d12388de470bc1ed521fcd3535315010010,0x395562f07b5487f34d315055409,0x15355801,0x1568dc01,0x15691201,0x156a9e01,0xa5a9b5829403,0x4de894e602,0x1a66f9a0711a4701a2769d86e9ab404fe281cc6f1a8669d267ccf329ca16,0x26180621989a27829528682501e240934bd2d3286410,0xcf588d64390ca9371595694318559cb4df49f5746b42c51568d214,0xcf588d0419044056adc5655a50c615672d37d27aa44755d57c6b42c51568d818,0x7e1e8be2f55204,0x15b8e401]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4293_9 : checkRows book4293 10 675 rows4293_9=true := by decide +kernel

def lastUnits4293 := digits 10 2 0xae2b7
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict4293 : checkReasons book4293 697 694 lastUnits4293 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude4293 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 4293=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=2) h hc bp eq (by decide +kernel)
  let v := truth Z a4293
  have hbase : ValidThrough v book4293 459 := book_start Z h hc z eq _ _ _ _ initialClauses4293
  have h0 : ValidThrough v book4293 483 := rows_sound hbase rows4293_0 rowsOk4293_0
  have h1 : ValidThrough v book4293 507 := rows_sound h0 rows4293_1 rowsOk4293_1
  have h2 : ValidThrough v book4293 531 := rows_sound h1 rows4293_2 rowsOk4293_2
  have h3 : ValidThrough v book4293 555 := rows_sound h2 rows4293_3 rowsOk4293_3
  have h4 : ValidThrough v book4293 579 := rows_sound h3 rows4293_4 rowsOk4293_4
  have h5 : ValidThrough v book4293 603 := rows_sound h4 rows4293_5 rowsOk4293_5
  have h6 : ValidThrough v book4293 627 := rows_sound h5 rows4293_6 rowsOk4293_6
  have h7 : ValidThrough v book4293 651 := rows_sound h6 rows4293_7 rowsOk4293_7
  have h8 : ValidThrough v book4293 675 := rows_sound h7 rows4293_8 rowsOk4293_8
  have h9 : ValidThrough v book4293 697 := rows_sound h8 rows4293_9 rowsOk4293_9
  exact book_end h9 _ _ conflict4293
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
