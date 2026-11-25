import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a2693 : Array Fact := #[(.lab 0 0 5),(.avoid 0 314 0),(.res 0 3),(.res 1 3),(.res 0 4),(.res 1 4),(.res 0 5),(.res 1 5),(.res 0 6),(.res 1 6),(.res 0 8),(.res 1 8),(.res 0 10),(.res 1 10),(.lab 1 0 1),(.lab 1 1 1),(.lab 1 2 1),(.lab 1 3 1),(.lab 3 0 3),(.live 3 1),(.lab 3 0 6),(.common 3 8),(.lab 3 0 10),(.common 3 10),(.lab 3 1 3),(.live 3 2),(.lab 3 1 6),(.lab 3 1 10),(.lab 3 2 3),(.live 3 3),(.lab 3 2 6),(.lab 3 2 10),(.lab 3 3 3),(.avoid 3 5190 0),(.avoid 3 5190 1),(.avoid 3 5190 2),(.avoid 3 5190 3),(.see 3 11 1102 0),(.see 3 11 1102 1),(.see 3 11 1102 2),(.see 3 11 1102 3),(.diff 0 3 10),(.diff 1 3 10),(.live 4 1),(.lab 4 0 3),(.lab 4 0 5),(.common 4 5),(.lab 4 0 6),(.common 4 6),(.lab 4 0 8),(.common 4 8),(.live 4 2),(.lab 4 1 3),(.lab 4 1 5),(.lab 4 1 8),(.live 4 3),(.lab 4 2 3),(.lab 4 2 5),(.lab 4 2 8),(.avoid 4 1102 0),(.avoid 4 1102 1),(.avoid 4 1102 2),(.avoid 4 1102 3),(.avoid 4 1290 0),(.avoid 4 1290 1),(.avoid 4 1290 2),(.avoid 4 1290 3),(.avoid 4 8297 0),(.avoid 4 8297 1),(.avoid 4 8297 2),(.avoid 4 8297 3),(.avoid 4 9992 0),(.avoid 4 9992 1),(.avoid 4 9992 2),(.avoid 4 9992 3),(.see 4 11 127 0),(.see 4 11 127 1),(.see 4 11 127 2),(.see 4 11 127 3),(.see 4 11 314 0),(.see 4 11 314 1),(.see 4 11 314 2),(.see 4 11 314 3),(.diff 0 4 5),(.diff 1 4 5),(.diff 0 4 8),(.diff 1 4 8),(.lab 5 0 5),(.common 5 8),(.lab 5 1 5),(.live 5 2),(.lab 5 2 5),(.live 5 3),(.lab 5 3 5),(.live 6 1),(.lab 6 0 1),(.lab 6 0 3),(.lab 6 0 4),(.lab 6 0 8),(.common 6 8),(.live 6 2),(.lab 6 1 1),(.lab 6 1 3),(.lab 6 1 4),(.lab 6 1 8),(.live 6 3),(.lab 6 2 1),(.lab 6 2 3),(.lab 6 2 4),(.lab 6 2 5),(.lab 6 2 8),(.lab 6 3 1),(.lab 6 3 3),(.lab 6 3 4),(.lab 6 3 8),(.avoid 6 314 0),(.avoid 6 314 1),(.avoid 6 314 2),(.avoid 6 314 3),(.avoid 6 4370 0),(.avoid 6 4370 1),(.avoid 6 4370 2),(.avoid 6 4370 3),(.see 6 9 127 0),(.see 6 9 127 1),(.see 6 9 127 2),(.see 6 9 127 3),(.diff 0 6 4),(.diff 1 6 4),(.diff 0 6 8),(.diff 1 6 8),(.lab 7 0 7),(.lab 7 0 12),(.avoid 7 4183 0),(.lab 8 0 8),(.live 8 1),(.lab 8 0 3),(.lab 8 0 5),(.lab 8 0 10),(.common 8 10),(.lab 8 0 13),(.lab 8 1 8),(.live 8 2),(.lab 8 1 3),(.lab 8 1 5),(.lab 8 1 10),(.lab 8 1 13),(.lab 8 2 8),(.live 8 3),(.lab 8 2 3),(.lab 8 2 5),(.lab 8 2 10),(.lab 8 2 13),(.lab 8 3 8),(.avoid 8 8297 0),(.avoid 8 8297 1),(.avoid 8 8297 2),(.avoid 8 8297 3),(.avoid 8 9288 0),(.avoid 8 9288 1),(.avoid 8 9288 2),(.avoid 8 9288 3),(.see 8 0 1290 0),(.see 8 0 1290 1),(.see 8 0 1290 2),(.see 8 0 1290 3),(.see 8 0 9992 0),(.see 8 0 9992 1),(.see 8 0 9992 2),(.see 8 0 9992 3),(.see 8 2 8488 0),(.see 8 2 8488 1),(.see 8 2 8488 2),(.see 8 2 8488 3),(.see 8 2 9992 0),(.see 8 2 9992 1),(.see 8 2 9992 2),(.see 8 2 9992 3),(.see 8 2 16256 0),(.see 8 2 16256 1),(.see 8 2 16256 2),(.see 8 2 16256 3),(.diff 0 8 3),(.diff 1 8 3),(.diff 0 8 5),(.diff 1 8 5),(.diff 0 8 10),(.diff 1 8 10),(.lab 9 0 9),(.lab 9 0 10),(.lab 9 0 12),(.avoid 9 1102 0),(.avoid 9 4183 0),(.lab 10 0 10),(.lab 10 0 8),(.lab 10 0 12),(.lab 10 0 13),(.lab 10 1 10),(.live 10 2),(.lab 10 1 8),(.lab 10 1 12),(.lab 10 1 13),(.lab 10 2 10),(.live 10 3),(.lab 10 3 10),(.avoid 10 4370 0),(.avoid 10 4370 1),(.avoid 10 4370 2),(.avoid 10 4370 3),(.avoid 10 5008 0),(.avoid 10 5008 1),(.avoid 10 5008 2),(.avoid 10 5008 3),(.avoid 10 8488 0),(.avoid 10 8488 1),(.avoid 10 8488 2),(.avoid 10 8488 3),(.see 10 0 7426 0),(.see 10 0 7426 1),(.see 10 0 7426 2),(.see 10 0 7426 3),(.see 10 0 9992 0),(.see 10 0 9992 1),(.see 10 0 9992 2),(.see 10 0 9992 3),(.lab 11 0 7),(.lab 11 0 9),(.lab 11 0 10),(.lab 11 0 12),(.lab 11 0 13),(.avoid 11 245 0),(.avoid 11 541 0),(.avoid 11 1102 0),(.avoid 11 4183 0),(.avoid 11 8297 0),(.lab 12 0 12),(.lab 12 1 12),(.lab 12 2 12),(.lab 12 3 12),(.lab 13 0 13),(.lab 13 1 13),(.lab 13 2 13),(.lab 13 3 13),(.reader false 0 0),(.reader false 1 0),(.es false 1 5),(.reader false 3 0),(.reader false 3 1),(.reader false 3 2),(.reader false 3 3),(.es false 3 1),(.reader false 7 0),(.reader false 7 1),(.reader false 7 2),(.reader false 7 3),(.reader false 8 0),(.reader false 8 1),(.reader false 8 2),(.reader false 8 3),(.es false 8 3),(.reader false 9 0),(.reader false 9 1),(.reader false 9 2),(.reader false 9 3),(.reader false 10 0),(.reader false 10 1),(.reader false 10 2),(.reader false 10 3),(.reader false 11 0),(.reader false 11 1),(.reader false 11 2),(.reader false 11 3),(.es false 11 8),(.reader false 12 0),(.reader false 12 1),(.reader false 12 2),(.reader false 12 3),(.reader false 13 0),(.reader false 13 1),(.reader false 13 2),(.reader false 13 3),(.reader false 14 0),(.reader false 14 1),(.reader false 14 2),(.reader false 14 3),(.es false 14 5),(.reader false 15 0),(.reader false 15 1),(.reader false 15 2),(.reader false 15 3),(.reader false 17 0),(.reader false 17 1),(.reader false 17 2),(.reader false 17 3),(.es false 17 1),(.reader false 18 0),(.reader false 18 1),(.reader false 18 2),(.reader false 18 3),(.es false 18 3),(.es false 18 8),(.reader true 0 0),(.reader true 0 1),(.reader true 0 2),(.reader true 0 3),(.es true 0 8),(.reader true 1 0),(.reader true 1 1),(.reader true 1 2),(.reader true 1 3),(.es true 1 8),(.reader true 3 0),(.reader true 7 0),(.es true 7 7),(.es true 7 12),(.reader true 8 0),(.es true 8 7),(.es true 8 12),(.reader true 9 0),(.reader true 9 1),(.reader true 9 2),(.reader true 9 3),(.es true 9 12),(.reader true 10 0),(.reader true 10 1),(.reader true 10 2),(.reader true 10 3),(.es true 10 10),(.es true 10 13),(.reader true 11 0),(.es true 11 10),(.es true 11 13),(.reader true 12 0),(.reader true 12 1),(.reader true 12 2),(.reader true 12 3),(.es true 12 13),(.reader true 13 0),(.es true 13 10),(.es true 13 12),(.reader true 14 0),(.reader true 14 1),(.reader true 14 2),(.reader true 14 3),(.es true 14 10),(.es true 14 12),(.reader true 15 0),(.reader true 15 1),(.reader true 15 2),(.reader true 15 3),(.es true 15 12),(.reader true 17 0),(.es true 17 9),(.reader true 18 0),(.es true 18 9),(.gate 0 1),(.gate 1 14),(.gate 3 17),(.gate 7 8),(.gate 7 9),(.gate 8 9),(.gate 8 18),(.gate 10 11),(.gate 10 12),(.gate 11 12),(.gate 11 18),(.gate 13 14),(.gate 13 15),(.gate 14 15),(.gate 17 18)]
def r2693 : List Scheme := [(.exposure 0 314),(.avoidNot 0 5 314 0),(.self 1 0),(.self 1 1),(.self 1 2),(.self 1 3),(.self 3 0),(.self 3 1),(.earlier 3 1),(.self 3 2),(.self 3 3),(.someRes 3),(.allRes 3 0),(.allRes 3 1),(.exposure 3 5190),(.avoidNot 3 6 5190 0),(.avoidNot 3 10 5190 0),(.avoidNot 3 6 5190 1),(.avoidNot 3 10 5190 1),(.avoidNot 3 6 5190 2),(.avoidNot 3 10 5190 2),(.avoidLive 3 5190 3),(.exactAt 3 11 1102),(.seeLab 3 11 6 1102 0),(.seeLab 3 11 10 1102 0),(.seeLab 3 11 6 1102 1),(.seeLab 3 11 10 1102 1),(.seeLab 3 11 6 1102 2),(.seeLab 3 11 10 1102 2),(.seeLive 3 11 1102 3),(.resCommon 3 8 0),(.resCommon 3 8 1),(.diffX 0 3 10),(.diffC 0 3 10),(.resCommon 3 10 0),(.diffX 1 3 10),(.diffC 1 3 10),(.resCommon 3 10 1),(.residual 3 10 0 1),(.residual 3 10 0 2),(.residual 3 10 1 2),(.earlier 4 1),(.someRes 4),(.allRes 4 0),(.allRes 4 1),(.exposure 4 1102),(.avoidNot 4 6 1102 0),(.avoidLive 4 1102 1),(.avoidLive 4 1102 2),(.avoidLive 4 1102 3),(.exposure 4 1290),(.avoidNot 4 3 1290 0),(.avoidNot 4 8 1290 0),(.avoidNot 4 8 1290 1),(.avoidNot 4 3 1290 2),(.avoidNot 4 8 1290 2),(.avoidLive 4 1290 3),(.exposure 4 8297),(.avoidNot 4 3 8297 0),(.avoidNot 4 5 8297 0),(.avoidNot 4 3 8297 1),(.avoidNot 4 5 8297 1),(.avoidNot 4 3 8297 2),(.avoidNot 4 5 8297 2),(.avoidLive 4 8297 3),(.exposure 4 9992),(.avoidNot 4 3 9992 0),(.avoidNot 4 8 9992 0),(.avoidNot 4 3 9992 1),(.avoidNot 4 8 9992 1),(.avoidLive 4 9992 2),(.avoidNot 4 8 9992 2),(.avoidLive 4 9992 3),(.exactAt 4 11 127),(.seeLab 4 11 6 127 0),(.seeLive 4 11 127 1),(.seeLive 4 11 127 2),(.seeLive 4 11 127 3),(.exactAt 4 11 314),(.seeLab 4 11 3 314 0),(.seeLab 4 11 5 314 0),(.seeLab 4 11 8 314 0),(.seeLab 4 11 3 314 1),(.seeLab 4 11 5 314 1),(.seeLab 4 11 8 314 1),(.seeLive 4 11 314 2),(.seeLab 4 11 3 314 2),(.seeLab 4 11 5 314 2),(.seeLab 4 11 8 314 2),(.seeLive 4 11 314 3),(.diffX 0 4 5),(.diffC 0 4 5),(.resCommon 4 5 0),(.diffX 1 4 5),(.diffC 1 4 5),(.resCommon 4 5 1),(.residual 4 5 0 1),(.residual 4 5 0 2),(.residual 4 5 1 2),(.adjacentCommon 4 6 11),(.diffX 0 4 8),(.diffC 0 4 8),(.resCommon 4 8 0),(.diffX 1 4 8),(.diffC 1 4 8),(.resCommon 4 8 1),(.residual 4 8 0 1),(.residual 4 8 0 2),(.residual 4 8 1 2),(.self 5 0),(.self 5 1),(.self 5 2),(.self 5 3),(.someRes 5),(.allRes 5 0),(.allRes 5 1),(.resCommon 5 8 0),(.resCommon 5 8 1),(.earlier 6 1),(.earlier 6 2),(.someRes 6),(.allRes 6 0),(.exposure 6 314),(.avoidNot 6 1 314 0),(.avoidNot 6 3 314 0),(.avoidNot 6 4 314 0),(.avoidNot 6 8 314 0),(.avoidNot 6 1 314 1),(.avoidNot 6 3 314 1),(.avoidNot 6 4 314 1),(.avoidNot 6 8 314 1),(.avoidLive 6 314 2),(.avoidNot 6 1 314 2),(.avoidNot 6 3 314 2),(.avoidNot 6 4 314 2),(.avoidNot 6 5 314 2),(.avoidNot 6 8 314 2),(.avoidLive 6 314 3),(.avoidNot 6 3 314 3),(.avoidNot 6 4 314 3),(.avoidNot 6 8 314 3),(.exposure 6 4370),(.avoidNot 6 4 4370 0),(.avoidNot 6 4 4370 1),(.avoidNot 6 4 4370 2),(.avoidNot 6 1 4370 3),(.exactAt 6 9 127),(.seeLab 6 9 1 127 0),(.seeLab 6 9 4 127 0),(.seeLab 6 9 1 127 1),(.seeLab 6 9 4 127 1),(.seeLab 6 9 1 127 2),(.seeLab 6 9 4 127 2),(.seeLab 6 9 5 127 2),(.seeLive 6 9 127 3),(.seeLab 6 9 1 127 3),(.seeLab 6 9 4 127 3),(.diffC 0 6 4),(.diffC 1 6 4),(.residual 6 4 0 1),(.residual 6 4 0 2),(.residual 6 4 0 3),(.residual 6 4 1 2),(.residual 6 4 1 3),(.residual 6 4 2 3),(.diffC 0 6 8),(.resCommon 6 8 0),(.diffC 1 6 8),(.resCommon 6 8 1),(.residual 6 8 0 1),(.residual 6 8 0 2),(.residual 6 8 0 3),(.residual 6 8 1 2),(.residual 6 8 1 3),(.residual 6 8 2 3),(.self 7 0),(.exposure 7 4183),(.avoidNot 7 12 4183 0),(.self 8 0),(.self 8 1),(.earlier 8 1),(.self 8 2),(.self 8 3),(.allRes 8 0),(.allRes 8 1),(.exposure 8 8297),(.avoidNot 8 5 8297 0),(.avoidNot 8 13 8297 0),(.avoidNot 8 5 8297 1),(.avoidNot 8 13 8297 1),(.avoidNot 8 5 8297 2),(.avoidNot 8 13 8297 2),(.avoidLive 8 8297 3),(.exposure 8 9288),(.avoidNot 8 3 9288 0),(.avoidNot 8 10 9288 0),(.avoidNot 8 13 9288 0),(.avoidNot 8 3 9288 1),(.avoidNot 8 10 9288 1),(.avoidNot 8 13 9288 1),(.avoidLive 8 9288 2),(.avoidNot 8 3 9288 2),(.avoidNot 8 10 9288 2),(.avoidNot 8 13 9288 2),(.avoidLive 8 9288 3),(.exactAt 8 0 1290),(.seeLab 8 0 3 1290 0),(.seeLab 8 0 10 1290 0),(.seeLab 8 0 3 1290 1),(.seeLab 8 0 10 1290 1),(.seeLive 8 0 1290 2),(.seeLab 8 0 3 1290 2),(.seeLab 8 0 10 1290 2),(.seeLive 8 0 1290 3),(.exactAt 8 0 9992),(.seeLab 8 0 10 9992 0),(.seeLab 8 0 13 9992 0),(.seeLab 8 0 10 9992 1),(.seeLab 8 0 13 9992 1),(.seeLive 8 0 9992 2),(.seeLab 8 0 10 9992 2),(.seeLab 8 0 13 9992 2),(.seeLive 8 0 9992 3),(.exactAt 8 2 8488),(.seeLab 8 2 3 8488 0),(.seeLab 8 2 5 8488 0),(.seeLab 8 2 13 8488 0),(.seeLab 8 2 3 8488 1),(.seeLab 8 2 5 8488 1),(.seeLab 8 2 13 8488 1),(.seeLive 8 2 8488 2),(.seeLab 8 2 3 8488 2),(.seeLab 8 2 5 8488 2),(.seeLab 8 2 13 8488 2),(.seeLive 8 2 8488 3),(.exactAt 8 2 9992),(.seeLab 8 2 10 9992 0),(.seeLab 8 2 13 9992 0),(.seeLab 8 2 10 9992 1),(.seeLab 8 2 13 9992 1),(.seeLive 8 2 9992 2),(.seeLab 8 2 10 9992 2),(.seeLab 8 2 13 9992 2),(.seeLive 8 2 9992 3),(.exactAt 8 2 16256),(.seeLab 8 2 13 16256 0),(.seeLive 8 2 16256 1),(.seeLive 8 2 16256 2),(.seeLab 8 2 10 16256 2),(.seeLive 8 2 16256 3),(.diffX 0 8 3),(.diffC 0 8 3),(.diffX 1 8 3),(.diffC 1 8 3),(.residual 8 3 0 1),(.residual 8 3 0 2),(.residual 8 3 1 2),(.diffX 0 8 5),(.diffC 0 8 5),(.diffX 1 8 5),(.diffC 1 8 5),(.residual 8 5 0 1),(.residual 8 5 0 2),(.residual 8 5 1 2),(.diffX 0 8 10),(.diffC 0 8 10),(.diffX 1 8 10),(.diffC 1 8 10),(.adjacentCommon 8 10 0),(.residual 8 10 0 1),(.residual 8 10 0 2),(.residual 8 10 1 2),(.self 9 0),(.exposure 9 1102),(.avoidNot 9 10 1102 0),(.exposure 9 4183),(.avoidNot 9 12 4183 0),(.self 10 0),(.self 10 1),(.self 10 2),(.self 10 3),(.someRes 10),(.allRes 10 0),(.exposure 10 4370),(.avoidNot 10 12 4370 0),(.avoidNot 10 8 4370 1),(.avoidLive 10 4370 2),(.avoidLive 10 4370 3),(.exposure 10 5008),(.avoidNot 10 8 5008 0),(.avoidNot 10 12 5008 1),(.avoidLive 10 5008 2),(.avoidLive 10 5008 3),(.exposure 10 8488),(.avoidNot 10 8 8488 0),(.avoidNot 10 13 8488 0),(.avoidNot 10 8 8488 1),(.avoidNot 10 13 8488 1),(.avoidLive 10 8488 2),(.avoidLive 10 8488 3),(.exactAt 10 0 7426),(.seeLab 10 0 12 7426 0),(.seeLab 10 0 8 7426 1),(.seeLive 10 0 7426 2),(.seeLive 10 0 7426 3),(.exactAt 10 0 9992),(.seeLab 10 0 8 9992 0),(.seeLab 10 0 13 9992 0),(.seeLab 10 0 8 9992 1),(.seeLab 10 0 13 9992 1),(.seeLive 10 0 9992 2),(.seeLive 10 0 9992 3),(.exposure 11 245),(.avoidNot 11 7 245 0),(.exposure 11 541),(.avoidNot 11 9 541 0),(.exposure 11 1102),(.avoidNot 11 10 1102 0),(.exposure 11 4183),(.avoidNot 11 12 4183 0),(.exposure 11 8297),(.avoidNot 11 13 8297 0),(.self 12 0),(.self 12 1),(.self 12 2),(.self 12 3),(.self 13 0),(.self 13 1),(.self 13 2),(.self 13 3),(.readerAny false 0),(.readerAny false 1),(.readerLab false 1 0 5 false),(.readerAny false 3),(.readerLab false 3 0 1 true),(.readerLab false 3 1 1 true),(.readerLab false 3 2 1 true),(.readerLab false 3 3 1 true),(.readerAny false 7),(.readerLive false 7 2),(.readerLive false 7 3),(.readerAny false 8),(.readerLab false 8 0 3 true),(.readerLab false 8 1 3 true),(.readerLive false 8 2),(.readerLab false 8 2 3 true),(.readerLive false 8 3),(.readerLab false 8 3 3 true),(.readerAny false 9),(.readerLive false 9 2),(.readerLive false 9 3),(.readerAny false 10),(.readerLive false 10 2),(.readerLive false 10 3),(.readerAny false 11),(.readerLab false 11 0 8 false),(.readerLab false 11 1 8 false),(.readerLive false 11 2),(.readerLive false 11 3),(.readerAny false 12),(.readerLive false 12 2),(.readerLive false 12 3),(.readerAny false 13),(.readerLive false 13 2),(.readerLive false 13 3),(.readerAny false 14),(.readerLab false 14 0 5 true),(.readerLab false 14 1 5 true),(.readerLive false 14 2),(.readerLab false 14 2 5 true),(.readerLive false 14 3),(.readerLab false 14 3 5 true),(.readerAny false 15),(.readerLive false 15 2),(.readerLive false 15 3),(.readerAny false 17),(.readerLab false 17 0 1 false),(.readerLab false 17 1 1 false),(.readerLive false 17 2),(.readerLive false 17 3),(.readerAny false 18),(.readerLab false 18 0 3 false),(.readerLab false 18 0 8 true),(.readerLab false 18 1 3 false),(.readerLab false 18 1 8 true),(.readerLive false 18 2),(.readerLab false 18 2 3 false),(.readerLab false 18 2 8 true),(.readerLive false 18 3),(.readerLab false 18 3 3 false),(.readerLab false 18 3 8 true),(.readerAny true 0),(.readerLab true 0 0 8 true),(.readerLab true 0 1 8 true),(.readerLab true 0 2 8 true),(.readerLab true 0 3 8 true),(.readerAny true 1),(.readerLab true 1 0 8 false),(.readerLive true 1 2),(.readerLive true 1 3),(.readerAny true 3),(.readerAny true 7),(.readerLab true 7 0 7 true),(.readerLab true 7 0 12 false),(.readerAny true 8),(.readerLab true 8 0 7 false),(.readerLab true 8 0 12 false),(.readerAny true 9),(.readerLab true 9 0 12 true),(.readerLab true 9 1 12 true),(.readerLab true 9 2 12 true),(.readerLab true 9 3 12 true),(.readerAny true 10),(.readerLab true 10 0 10 true),(.readerLab true 10 0 13 false),(.readerLab true 10 1 10 true),(.readerLab true 10 1 13 false),(.readerLive true 10 2),(.readerLab true 10 2 10 true),(.readerLive true 10 3),(.readerLab true 10 3 10 true),(.readerAny true 11),(.readerLab true 11 0 10 false),(.readerLab true 11 0 13 false),(.readerAny true 12),(.readerLab true 12 0 13 true),(.readerLab true 12 1 13 true),(.readerLab true 12 2 13 true),(.readerLab true 12 3 13 true),(.readerAny true 13),(.readerLab true 13 0 10 false),(.readerLab true 13 0 12 false),(.readerAny true 14),(.readerLab true 14 0 10 true),(.readerLab true 14 0 12 false),(.readerLab true 14 1 10 true),(.readerLab true 14 1 12 false),(.readerLive true 14 2),(.readerLab true 14 2 10 true),(.readerLive true 14 3),(.readerLab true 14 3 10 true),(.readerAny true 15),(.readerLab true 15 0 12 true),(.readerLab true 15 1 12 true),(.readerLab true 15 2 12 true),(.readerLab true 15 3 12 true),(.readerAny true 17),(.readerLab true 17 0 9 true),(.readerAny true 18),(.readerLab true 18 0 9 false),(.gateEq false 0 1 0),(.eqLab true 0 1 8 true),(.eqLab false 1 14 5 false),(.gateEq true 1 14 1),(.eqLab false 3 17 1 true),(.gateEq true 3 17 0),(.gateEq false 7 8 0),(.gateEq false 7 8 1),(.eqLab true 7 8 7 true),(.gateEq false 7 9 0),(.gateEq false 7 9 1),(.eqLab true 7 9 12 false),(.gateEq false 8 9 0),(.gateEq false 8 9 1),(.eqLab true 8 9 12 false),(.eqLab false 8 18 3 true),(.gateEq true 8 18 0),(.gateEq false 10 11 0),(.gateEq false 10 11 1),(.eqLab true 10 11 10 true),(.gateEq false 10 12 0),(.gateEq false 10 12 1),(.eqLab true 10 12 13 false),(.gateEq false 11 12 0),(.gateEq false 11 12 1),(.eqLab true 11 12 13 false),(.eqLab false 11 18 8 false),(.gateEq true 11 18 0),(.gateEq false 13 14 0),(.gateEq false 13 14 1),(.eqLab true 13 14 10 false),(.gateEq false 13 15 0),(.gateEq false 13 15 1),(.eqLab true 13 15 12 false),(.gateEq false 14 15 0),(.gateEq false 14 15 1),(.eqLab true 14 15 12 false),(.gateEq false 17 18 0),(.gateEq false 17 18 1),(.eqLab true 17 18 9 true)]

def table2693_0 : List Nat := [193,130,0x741,0x7c1,0x841,0x8c1,0x941,0xc41,0x270c82,0xe41,0x1041,0x1c050c83,0x50e82,0x70e82,0x4911c4510c4,0x281082]
def table2693_1 : List Nat := [0x2c1082,0x341102,0x361102,0x3c1182,0x3e1182,0x3b1202,0x5113c4d12c4,0x291282,0x2c1282,0x351302,0x361302,0x3d1382,0x3e1382,0x3b1402,0xac140103,0xac160183]
def table2693_2 : List Nat := [0x51482,0x181482,0xbc180103,0x71502,0x1a1502,0xbc1a0183,0x5514c370b4260b86,0x5514c3f0b4320b86,0x5514c3f0dc320b86,0x571982,0x2c091983,0x91b82,0xb1b82,0x7d1ec791dc4,0x5e1d82,0x571e02]
def table2693_3 : List Nat := [0x671e82,0x6f1f02,0x8520c811fc4,0x581f82,0x621f82,0x6c2002,0x702082,0x742082,0x6f2102,0x8d22c8921c4,0x582182,0x5a2182,0x682202,0x6a2202,0x702282,0x722282]
def table2693_4 : List Nat := [0x6f2302,0x9524c9123c4,0x582382,0x622382,0x682402,0x6c2402,0x672482,0x742482,0x6f2502,0x9d26c9925c4,0x5f2582,0x572602,0x672682,0x6f2702,0xa528ca127c4,0x592782]
def table2693_5 : List Nat := [0x5a2782,0x622782,0x692802,0x6a2802,0x6c2802,0x672882,0x712882,0x722882,0x742882,0x6f2902,0x92982,0xc2982,0x1740c0203,0xb2a02,0xe2a02,0x1740e0283]
def table2693_6 : List Nat := [0xa929c6b16c561706,0xa929c7316c661706,0xa929c731ac661706,0x1841,0x92a82,0x142a82,0x194140203,0xb2b02,0x162b02,0x194160283,0xad2ac6d18c561906,0xad2ac7518c661906,0xad2ac751b4661906,0x2bc1,0x2cc1,0x2dc1]
def table2693_7 : List Nat := [0x2ec1,0x3c0d2d03,0xd2e02,0xf2e02,0x2c4140303,0x2c4160383,0xbd3202,0xc93482,0x4c113203,0x113482,0xed3ace939c4,0xbe3982,0xc03982,0xc23982,0xc43982,0xca3a02]
def table2693_8 : List Nat := [0xcc3a02,0xce3a02,0xd03a02,0xc93a82,0xd43a82,0xd63a82,0xd83a82,0xda3a82,0xdc3a82,0xd33b02,0xe03b02,0xe23b02,0xe43b02,0xf53ccf13bc4,0xc23b82,0xce3c02]
def table2693_9 : List Nat := [0xd83c82,0xde3d02,0xfd3ecf93dc4,0xbf3d82,0xc23d82,0xcb3e02,0xce3e02,0xd53e82,0xd83e82,0xdb3e82,0xd33f02,0xdf3f02,0xe23f02,0x83f82,0xa4002,0x1013fccf30cbc1806]
def table2693_10 : List Nat := [0x1013fcd930cc81806,0x1013fce330cd21806,0x1013fcd933cc81806,0x1013fce333cd21806,0x1013fce3364d21806,0x144082,0x31c140403,0x164102,0x31c160483,0x10540cd1314bc3186,0x10540cdd314c83186,0x10540ce5314d23186,0x10540cdd344c83186,0x10540ce5344d23186,0x10540ce5374d23186,0x41c1]
def table2693_11 : List Nat := [0x42c1,0x1084282,0x4341,0x46c1,0x10f4702,0x49c1,0x4cc1,0x154a02,0x174a02,0x13b4e5374d44,0x1124d02,0x1184d02,0x1204d82,0x1244d82,0x12c4e02,0x1304e02]
def table2693_12 : List Nat := [0x1294e82,0x1435053f4f44,0x1104f02,0x1144f02,0x1184f02,0x11e4f82,0x1224f82,0x1244f82,0x11d5002,0x12a5002,0x12e5002,0x1305002,0x1295082,0x14b525475144,0x1105102,0x1155102]
def table2693_13 : List Nat := [0x11e5182,0x1235182,0x11d5202,0x12a5202,0x12f5202,0x1295282,0x1535454f5344,0x1155302,0x1185302,0x1235382,0x1245382,0x11d5402,0x12f5402,0x1305402,0x1295482,0x15b565575544]
def table2693_14 : List Nat := [0x1105502,0x1125502,0x1195502,0x11e5582,0x1205582,0x1255582,0x11d5602,0x12a5602,0x12c5602,0x1315602,0x1295682,0x1635855f5744,0x1145702,0x1195702,0x1225782,0x1255782]
def table2693_15 : List Nat := [0x11d5802,0x12e5802,0x1315802,0x1295882,0x16b5a5675944,0x1195902,0x10f5982,0x11d5a02,0x12e5a02,0x1295a82,0x155b02,0x45b02,0x175b82,0x65b82,0x16f5b51f4450e0a86,0x16f5b52b4451c0a86]
def table2693_16 : List Nat := [0x16f5b52b47d1c0a86,0x155c02,0xc5c02,0x175c82,0xe5c82,0x1735c52144d0e2c06,0x1735c52d44d1c2c06,0x1735c52d4851c2c06,0x155d02,0x185d02,0x175d82,0x1a5d82,0x45c1,0x1775d5234550e4586,0x1775d52f4551c4586,0x1775d52f48d1c4586]
def table2693_17 : List Nat := [0x5e41,0x5fc1,0x17a5f82,0x6041,0x17c6002,0x60c1,0x62c1,0x6541,0x6641,0x6c196303,0x196582,0x1a167d9d66c4,0x1866682,0x18e6702,0x18d6782,0x1976802]
def table2693_18 : List Nat := [0x1a969da568c4,0x1846882,0x1906902,0x18d6982,0x1976a02,0x1b16bdad6ac4,0x1846a82,0x1886a82,0x18e6b02,0x1926b02,0x18d6b82,0x1976c02,0x1b96ddb56cc4,0x1866c82,0x18f6d02,0x18d6d82]
def table2693_19 : List Nat := [0x1976e02,0x1c16fdbd6ec4,0x1856e82,0x1886e82,0x18f6f02,0x1926f02,0x18d6f82,0x1977002,0x7341,0x1c27302,0x73c1,0x1c47382,0x7441,0x1c67402,0x74c1,0x1c87482]
def table2693_20 : List Nat := [0x7541,0x1ca7502,0x75c1,0x7641,0x76c1,0x7741,0x77c1,0x7841,0x78c1,0x7941,0x79c1,0x7a41,0x7a8017a03,0x1f37c5ef7b44,0x7d41c7b03,0x7d41e7b83]
def table2693_21 : List Nat := [0x7d4207c03,0x7d4227c83,0x1fd7edf97dc4,0x337e82,0x3b7f02,0x20580e017fc4,0x81c247f83,0x81c308003,0x338082,0x81c388083,0x3b8102,0x81c408103,0x20f8360b8244,0x338302,0x3b8382,0x217856138444]
def table2693_22 : List Nat := [0x678502,0x6f8582,0x21f8761b8644,0x880638603,0x8806d8683,0x678702,0x6f8782,0x22989e2588c4,0x678982,0x6f8a02,0x2318be2d8ac4,0xb58b82,0xb98c02,0x2398de358cc4,0x8ecae8c83,0x8ecb28d03]
def table2693_23 : List Nat := [0xb58d82,0x8ecb68d83,0xb98e02,0x8ecba8e03,0x2439063f8f44,0xb59002,0xb99082,0x24b926479144,0x930bf9103,0x930cb9183,0xc99202,0xd39282,0x25594e5193c4,0x958c19383,0x964c49383,0x958cd9403]
def table2693_24 : List Nat := [0x964d09403,0xc99482,0x958d79483,0x964dc9483,0xd39502,0x958e19503,0x964e49503,0x26197e5d96c4,0x98d0c9683,0x98d1a9703,0x98d269783,0x98d329803,0x26b9a6679944,0x9b1859903,0x18d9a02,0x1979a82]
def table2693_25 : List Nat := [0x9bc1,0x9c41,0x9cd069c03,0x9d1099c03,0x9dc1,0x9e1c39d83,0x9e9c99d83,0x283a067f9f44,0xa15d69f03,0xa15d89f83,0xa15daa003,0xa15dca083,0x28da2e89a1c4,0xa3d82a183,0xa4189a183,0xa3d8aa203]
def table2693_26 : List Nat := [0xa4193a203,0x18da282,0xa3d94a283,0x197a302,0xa3d98a303,0xa4c1,0xa51c7a483,0xa59cba483,0x29fa769ba644,0xa85dea603,0xa85e0a683,0xa85e2a703,0xa85e4a783,0xa8c1,0xa917ba883,0xa997da883]
def table2693_27 : List Nat := [0x2afab6abaa44,0xac582aa03,0xac987aa03,0xac58aaa83,0xac991aa83,0x18dab02,0xac594ab03,0x197ab82,0xac598ab83,0x2bbae6b7ad44,0xaf5d6ad03,0xaf5d8ad83,0xaf5daae03,0xaf5dcae83,0xafc1,0xb0578af83]
def table2693_28 : List Nat := [0xb0c1,0xb11c5b083,0xb1de87983,0x9b662b183,0x8e9ebb203,0xb26aa9983,0x935f4b283,0xb2ebe9b83,0xb35fe7d83,0xb36007e03,0x9e672b303,0xb3e087d83,0xb3e0a7e03,0xa1275b383,0xb46087f83,0xb460a8003]
def table2693_29 : List Nat := [0xa127bb403,0x95e06b483,0xb4ec29d83,0xb56188403,0xb561a8483,0xa568eb503,0xb5e228403,0xb5e248483,0xa8291b583,0xb66228603,0xb66248683,0xa8297b603,0x96221b683,0xb6ec2a483,0xb76328a83,0xb76348b03]
def table2693_30 : List Nat := [0xac2a5b703,0xb7e3c8a83,0xb7e3e8b03,0xaf2a7b783,0xb863c8c83,0xb863e8d03,0xaf2b3b803,0xb8e4e9103,0xb8e509183,0xb16c0b883,1,0x404ff33cc32f05,0x404ff364c33205,0x404ff38cc33485,0x404ff364cf3205,0x404ff38ccf3485]
def table2693_31 : List Nat := [0x404ff38cd93485,0x4201,0x5dd7548d154385,0x5dd754bd154705,0x5dd754bd234705,0x5e81,0x5f01,0x7081,0x7101,0x7181,0x7201,0x7281,0x7a81,0x1f57b02,0x1f57b82,0x1f57c02]
def table2693_32 : List Nat := [0x1f57c82,0x2077f82,0x2078002,0x2078082,0x2078102,0x23b8c82,0x23b8d02,0x23b8d82,0x23b8e02,0x2639682,0x2639702,0x2639782,0x2639802,0x9cc1,0x9d01,0x9e01]
def table2693_33 : List Nat := [0x9e81,0x2859f02,0x2859f82,0x285a002,0x285a082,0x28fa182,0x28fa202,0x28fa282,0x28fa302,0xa501,0xa581,0x2a1a602,0x2a1a682,0x2a1a702,0x2a1a782,0xa901]
def table2693_34 : List Nat := [0xa981,0x2b1aa02,0x2b1aa82,0x2b1ab02,0x2b1ab82,0x2bdad02,0x2bdad82,0x2bdae02,0x2bdae82,0xb041,0xb101,0xb1c1,0x26d9882,0x23ab202,0xb2c1,0xb301]
def table2693_35 : List Nat := [0x284b382,0x284b402,0xb4c1,0x28eb502,0x2a0b602,0xb6c1,0x2b0b702,0x2bcb782,0xb881,0xaf41,0xb781,0xac41,0xb701,0xa841,0xb601,0xa3c1]
def table2693_36 : List Nat := [0xb501,0xa141,0xb381,0xb401,0x8ec1,0xb201,0xd2399013fc4,0x234b8170662885,0x294a72a45c158a32187,0x294a72a45c158a32207,0x6f2e05c1984,0x87e1d18c6d8805,0xa18c6d158ab0586,0x5d755a03,0x5d755803,0x5d754f03]
def table2693_37 : List Nat := [0x5d754f83,0x175d42,0xb805d405704,0xb805d615004,0xb805d415784,0x2e0175843,0x50d53545414605,0x2e0174b43,0xb805c2,0x2e15b439594d05,0x2e15b439594d85,0xb84a51c5644,0x2e1294703,0xb84a42,0x1bc6715c3,0x1bc671883]
def table2693_38 : List Nat := [0x1bc0a2e03,0x1bc6c19c3,0x1bc6c1d03,0x1bc661585b21ca329c5c2a49,0x101348ff3e04,0x101348ff30c4,0x101348ff3e84,0x404d23fc3,0x5d0e47d110105,0x65d866343,0x98c1,0x9b41,0xa35936268ba405,0x65d8dac83,0xb9b84b58f84,0x2e6e12d43]
def table2693_39 : List Nat := [0x17471560304,0x14550c82e1385,0x5154260b84f1086,0x5154260b84f1106,0x141a0c83,0xec338283,0x3b0cc2,0x1a0142,0x2e41703d1c5585,0x17471540104,0x2e41703d1c5505,0x5d1c4b5390305,0xb905c0f4704,0x1294742,0x34cd83383,0x7d41]
def table2693_40 : List Nat := [0x9341,0x81c1,0x95c1,0x1013fcd83d84,0x404ff3603,0x34cc93983,0xd33242,0x1013fc2,0x6f29ca9170662786,0x8d29ca9170662886,0x1bca72a45c1985,0x6f19ed78604,0x1bc67b5c3,0x7068da418d6b05,0x6c5c1a36906345,0x5c045583]
def table2693_41 : List Nat := [0x1bc0a05c3,0x1bc0a19c3,0x1bc0a1b43,0x6f0282,0x1bc6c1883,0x155dd5d4f84,0x55774c03,0x55774f03,0x55775743,0x155dc2,0x58154d5130385,0x1c530b84f0fc5,0x3b13c470d84,0x714c2e13c4,0x10070603,0x1bc660303]
def table2693_42 : List Nat := [0x6eb20643,0x58154ad1f0185,0x580d0553d4885,0x55235ccb05005,0x155ccb05604,0x58154f5230385,0x1801c2,0x581551c0647c5,0x16034154f44,0x596d52d1c445450187,0x580d0543,0x1bc662ac641b05,0x1bc161983,0x4165940e55320c63a87,0x4165940e55320c63987,0x16965030444]
def table2693_43 : List Nat := [0x4165940cc63acc834c7,0x10540cc63acbc348e73148,0x10596503318eb348e79408,0x4165940cc63acc89547,0x25940cc6414eb3206,0x3241,0x103964c64144,0x5a590503,0xa401b0643,0x58150193d5585,0x16054064404,0x58150183,0x6f0582,0x170102,0x1bc1,577]
def table2693_44 : List Nat := [705,0x3f81,0x4001]

def encoded2693 (i : Nat) : Nat :=
  if i < 352 then
    if i < 176 then
      if i < 80 then
        if i < 32 then
          if i < 16 then
            table2693_0.getD (i%16) 0
          else
            table2693_1.getD (i%16) 0
        else
          if i < 48 then
            table2693_2.getD (i%16) 0
          else
            if i < 64 then
              table2693_3.getD (i%16) 0
            else
              table2693_4.getD (i%16) 0
      else
        if i < 128 then
          if i < 96 then
            table2693_5.getD (i%16) 0
          else
            if i < 112 then
              table2693_6.getD (i%16) 0
            else
              table2693_7.getD (i%16) 0
        else
          if i < 144 then
            table2693_8.getD (i%16) 0
          else
            if i < 160 then
              table2693_9.getD (i%16) 0
            else
              table2693_10.getD (i%16) 0
    else
      if i < 256 then
        if i < 208 then
          if i < 192 then
            table2693_11.getD (i%16) 0
          else
            table2693_12.getD (i%16) 0
        else
          if i < 224 then
            table2693_13.getD (i%16) 0
          else
            if i < 240 then
              table2693_14.getD (i%16) 0
            else
              table2693_15.getD (i%16) 0
      else
        if i < 304 then
          if i < 272 then
            table2693_16.getD (i%16) 0
          else
            if i < 288 then
              table2693_17.getD (i%16) 0
            else
              table2693_18.getD (i%16) 0
        else
          if i < 320 then
            table2693_19.getD (i%16) 0
          else
            if i < 336 then
              table2693_20.getD (i%16) 0
            else
              table2693_21.getD (i%16) 0
  else
    if i < 528 then
      if i < 432 then
        if i < 384 then
          if i < 368 then
            table2693_22.getD (i%16) 0
          else
            table2693_23.getD (i%16) 0
        else
          if i < 400 then
            table2693_24.getD (i%16) 0
          else
            if i < 416 then
              table2693_25.getD (i%16) 0
            else
              table2693_26.getD (i%16) 0
      else
        if i < 480 then
          if i < 448 then
            table2693_27.getD (i%16) 0
          else
            if i < 464 then
              table2693_28.getD (i%16) 0
            else
              table2693_29.getD (i%16) 0
        else
          if i < 496 then
            table2693_30.getD (i%16) 0
          else
            if i < 512 then
              table2693_31.getD (i%16) 0
            else
              table2693_32.getD (i%16) 0
    else
      if i < 624 then
        if i < 576 then
          if i < 544 then
            table2693_33.getD (i%16) 0
          else
            if i < 560 then
              table2693_34.getD (i%16) 0
            else
              table2693_35.getD (i%16) 0
        else
          if i < 592 then
            table2693_36.getD (i%16) 0
          else
            if i < 608 then
              table2693_37.getD (i%16) 0
            else
              table2693_38.getD (i%16) 0
      else
        if i < 672 then
          if i < 640 then
            table2693_39.getD (i%16) 0
          else
            if i < 656 then
              table2693_40.getD (i%16) 0
            else
              table2693_41.getD (i%16) 0
        else
          if i < 688 then
            table2693_42.getD (i%16) 0
          else
            if i < 704 then
              table2693_43.getD (i%16) 0
            else
              table2693_44.getD (i%16) 0
def book2693 (i : Nat) : Clause := let n := encoded2693 i; unpackLits 10 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses2693 : inputsOK 2 2693 a2693 r2693 (baseBook book2693 490).toList=true := by decide +kernel

def rows2693_0 : List Nat := [513,0x3193e01,0x3194001,0x3194201,0x3194401,0x3194601,0x3194801,0x5816201,0x8621a01,0x8621c01,0x8621e01,0x88a2401,0x89a2801,0x9c27201,0x9d27601,0x9e27a01,0x9f27e01,0xa028201,0x3d4a5a9802,0x129c01,0x1a9e01,0x22a001,0x2aa201,0x32ac01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2693_0 : checkRows book2693 10 490 rows2693_0=true := by decide +kernel

def rows2693_1 : List Nat := [0x3aae01,0x4ab201,0x52b601,0x36adc01,0x372de01,0x37ae201,0x382e601,0x5931001,0x59b1201,0x5ab1401,0x5b31601,0x15ec8b2402,0x3e2c8b2602,0x3eeca32a02,0x3f4ca32c02,0xa133001,0xa1b3201,0xa233401,0xa2b3601,0x8ab3a01,0x8b33e01,0x8bb4401,0x8c34801,0x3f2d2b4c02]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2693_1 : checkRows book2693 10 514 rows2693_1=true := by decide +kernel

def rows2693_2 : List Nat := [0x3f6d2b4e02,0xa335201,0xa3b5401,0xa435601,0xa4b5801,0x3ead6b5c02,0x3ecd6b5e02,0x8ab6201,0x8b36601,0x8bb6c01,0x8c37001,0xa137401,0xa1b7601,0xa237801,0xa2b7a01,0x220df37e02,0x3f0e038202,0x296a538402,0x115b8601,0xfe38801,0x37cc838e02,0x41f06b9402,0x10739a01,0x1083a001]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2693_2 : checkRows book2693 10 538 rows2693_2=true := by decide +kernel

def rows2693_3 : List Nat := [0x380ca3a402,0x10cbaa01,0x10d3b601,0x380d2bba02,0x10fbc001,0x1103c601,0x45514bd202,0x45113c4d12b7204,0x11cc6e01,0x44911c4510b6004,0x11dc6c01,0x43d0ec390db5004,0x11ec6801,0x4310bc2d0ab3804,0x11fc6601,0x42909c2508b2e04,0x120c6001,0x120c6201,0x41103c0d02ada04,0x12245a01,0x4e1304b3daf63d63b0ee3e9263d9240b,0x1d87a308c41f0ae2b0b6390bc398720b,0x270c0278761d0a605,0x270c02907a1e0a005]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2693_3 : checkRows book2693 10 562 rows2693_3=true := by decide +kernel

def rows2693_4 : List Nat := [0xa0298c23107e1cc932448e148802c8b6390bc3989c10,0x2c8b1ac402,0xd2340d402,0x659d6609dc631d861be8f99f07ba14661e65c1e40f,0x6318665be8f99e4789e0851985c1820b,0x1ec771e8759ea7698861a14799f25c49b273e40e,0x5a19af919e761d6779a26398c851aa79971271a40f,0x1dc763e8f9994641832849f27214661e65c1d60e,0x17c5e20c829c26f9ca6d1ac5d9ae769d881208399806f1d45c0e8844a239168641b8651d2659721e,0x5d17c82a0e721be711b06b17a6c9de771d7291d26e1686599464204820e6601bc751e65c0e8844a23917221,0x5d17c82a0e721be749686e9a46b19a711ae67988619826397a6c9a2779dc8120839980661aa6f1d45c0e8844a23917225,0x5f1788320a709be749686e9a46b19a729b26898e63182621766b99e769d875ca929a04820e6601986a9bc751e65c0e8844a23917229,0x631ac609b0621b205,0x5e17483a0c81208399805c0e8844a2391e05f9e52a97211,0x1745ea0a729c86f9d12b9c52b1965f9b85a1e4789e12a8e8844a2751bc661805c20439208399721e,0x721c4829765d204392083acb0399be0b,0x709ca8297a5e204392083acb0399be0b,0x721c283a0c5f1732d4b2810e4820eb2c0e6601d45a1be11,0x5e1745fa0e831d2744b6810e4820eb2c0e6601720f,0x1866b1826d18e729be714ac731b6644b8751bc661ae10,0x170921689617862268602609409,0x2209c208a2218902c88c2a8a409,0x2109c208a8228d52fcbc3296f2e8d2344b02a88d250be398902c89e15,0x2109c208aa230902c88a2a09e09]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2693_4 : checkRows book2693 10 586 rows2693_4=true := by decide +kernel

def rows2693_5 : List Nat := [0x1989c190b01b8702c86a2a09e09,0x1fc92308802c87205,0x4590cf7bdc3f92c4a8ef230f409,0x4590c40bdaf63d63b0ef230f409,0x40916f73e0421304b8ef230f409,0x47920f7be0489384d92533128474cb3211a0d,0xf1f67e211289fc05,0x8ea588da5e8f23e9823896a5c09,0x41905c1504b0e04,0x13545801,0x33cd033802,0xc6a40c6244e2b68d83649231edba46c736b34cd722a4211,0x2dab53caf12d8b92d6b84791d3bc0a,0x2dab53c8f0ae9372eab82d6b62e4bb4791d3be0e,0x5d17c82a0e3a204819805c211289687217a729720f,0x200904e140260e0361002a0601c0a,0x2c1302e0801e1003a0603408,0x2c13032090221003a0603008,0xc034138500a01d39ce53884a058101002a0e8181202c11,0xaaaa4e7b98aa2b4a9ab117c87213900b,0xaaaa4e7396ae4eaaeab0a9aa8ad2bd17c87213920f,0x4ec064e802,0x64984804d00f1f73ba3336bcd378e33818e729c67e1985c2108d213289691c98219,0x6498a7fcd00f1f67e1985c2112896870188711820f]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2693_5 : checkRows book2693 10 610 rows2693_5=true := by decide +kernel

def rows2693_6 : List Nat := [0x5f1788320a3a20438cdef34da8ccef3c976711c2819805c2108d213289691c97219,0x5e17483a0c3a204819805c211289720b,0x18a612007f83c7dcee8ccdaf34de38cf66597e749d0739bf3d4f07e198751708423484ca31c9821e,0x619ac609b4639ca6f9c52b1cc6d990661bc751ae0f,0x3d9243d12c409124d10c4c12609,0x400ffbfcfea9a04,0x45d3fb8c02,0x40901c0500aaa04,0x46540ba202,0xbe2eebfaf2c0af4400fe3b0f4f58f64a12644af6c210d3f4cf1c505403ce17,0xbe2eec0af43b3d6beaf03e8f83d8f43f92a495073f130431124d2f6c24cf1c505403d01b,0xbe2eebeaf03e0f6bdb08bd3031c505403d00d,0xbe2eebfaf2400fe3d50ac0af441912bdb091c505403ce11,0x1323d1244a0fa4b102f63dd435084d1133390e0e,0x4c6308742809e148ae06,0x1d87a308c41f0ae2b07207,0x3107229c932409d44d10148802c87e0b,0x2ceafbb2e9ac2b4ac0b447d203ae0a,0x2ceafbb4ea2c545ac2b32d2b02cab447d203ac0e,0x98cd89a2529426cd0a6607,0x2633626493a4c92d1ad0a6c9526a0a,0x1926118e804d0729c67e1985a4fa5c1f60f2112898210,0x6298465a007f9d2739bf47cf20f1f73ba33473b146514d1a6e958be2f2353e212844fa75199289f85c4c02d13b4393d1e98227,0x4c32fcbc3213b4393d4849808]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2693_6 : checkRows book2693 10 634 rows2693_6=true := by decide +kernel

def rows2693_7 : List Nat := [0x8827082288862c08f260d8240b23213b4393c340d348053488a414,0x6c270642886835cc42a06b49522348d1480c84ed0e4f0702c8ac14,0x1b09c190a21a0702c86a2a0ac09,0x789defa18e6321079cfa5b9d609,0x1e2773e6f918660d2a76cac6e996841986f1e65a4fa5b9d612,0x1dc76be462186841e65a4fa5b9e54b1d60c,0x651dc609d74aa10661e73e96e7952d4bbe80d,0x194633e6f91d94c52e841985a4fa5b9820c,0x5e17c82a0c3aa08809805a4fa5b9720b,0x300d04e140460ecec0682c08,0x782c070340902a0e82e07,0x882c070300804d4e0294d8460a83a044ec068320f,0x200904e140260e0374e844108460acec0681c0e,0x2e0b62e85549d1405,0x2328d4da02,0xf9fa7d4fa5ba0005,0x4ed4f01b50d40f34de38d34709be729b4681ac669766b99e769d8759e4749b86a19665192609dc631986a9bc751e72e96e85d331c8162a,0x17c5d20e8297a721de6f9d6711d86c19e6b19a791d26e1a865994809806a9bc751e65a4fa5b9a26c97220,0x5d1785fa0c839d274202604fa5b9720b,0x534711c26fd487298e60d463aa08661d45b9760e,0x13b53c0681603,0x671a67f5427d1aa5a4fa5b9fa0f99a0b,0x671a87f9946498262d4e0f9fb53540f34de38d4a68d447d1986acbb3e96e85d331c99a1b,0x681a67f1fe0f9fa5a19a07]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2693_7 : checkRows book2693 10 658 rows2693_7=true := by decide +kernel

def rows2693_8 : List Nat := [0x5f1745ea0e829ca721bf520ea820e337bcd5054d549c46798861985542174c9693ecba751aa602027d16f1c97223,0x529310cf498d604,0x8827082288862c08e350d9558cc32d554f854148902c8cf498a414,0x300bf158553044410b412f808,0xc030654954be8fc3e0ed412f809,0xbf30654958bf904400f55755a540f03b50cc21123c94f412f813,0xbf30654958bf904400f557308448ed412f80d,0x10446152558f404,0xf456900c02ff4111806,0x1184115c56306be564bf563570ed580f40c,0x1043f15a55914c330b59d61410f40a,0x3bd0c01,0x30cc255a445695a95c06,0x14d5794a53d6c04,0xd1a6e95a328d51c05,0x6498f509ca719985b98207,0x18a65d42749ce6fd7270184661d45b9820c,0x1866498a679fe7f5535d03e7e9f4661aa5a4fa5b98210,0x5775c2174cd6eee3b125d1930cbeb2d58b346b1ed4c10,0x6298465a007f9d2739bf3c83d479f67e198754fa5c5328518213,0x2209c208a2218b0238d4365563305414d18ec5713bd7a32a134cca28557833d262c8911e8a41d,0x15f05601,0x15f05801,0x15f93a01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2693_8 : checkRows book2693 10 682 rows2693_8=true := by decide +kernel

def rows2693_9 : List Nat := [0x16013c01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2693_9 : checkRows book2693 10 706 rows2693_9=true := by decide +kernel

def lastUnits2693 := digits 10 2 0xb0ac1
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict2693 : checkReasons book2693 707 647 lastUnits2693 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude2693 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 2693=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=2) h hc bp eq (by decide +kernel)
  let v := truth Z a2693
  have hbase : ValidThrough v book2693 490 := book_start Z h hc z eq _ _ _ _ initialClauses2693
  have h0 : ValidThrough v book2693 514 := rows_sound hbase rows2693_0 rowsOk2693_0
  have h1 : ValidThrough v book2693 538 := rows_sound h0 rows2693_1 rowsOk2693_1
  have h2 : ValidThrough v book2693 562 := rows_sound h1 rows2693_2 rowsOk2693_2
  have h3 : ValidThrough v book2693 586 := rows_sound h2 rows2693_3 rowsOk2693_3
  have h4 : ValidThrough v book2693 610 := rows_sound h3 rows2693_4 rowsOk2693_4
  have h5 : ValidThrough v book2693 634 := rows_sound h4 rows2693_5 rowsOk2693_5
  have h6 : ValidThrough v book2693 658 := rows_sound h5 rows2693_6 rowsOk2693_6
  have h7 : ValidThrough v book2693 682 := rows_sound h6 rows2693_7 rowsOk2693_7
  have h8 : ValidThrough v book2693 706 := rows_sound h7 rows2693_8 rowsOk2693_8
  have h9 : ValidThrough v book2693 707 := rows_sound h8 rows2693_9 rowsOk2693_9
  exact book_end h9 _ _ conflict2693
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
