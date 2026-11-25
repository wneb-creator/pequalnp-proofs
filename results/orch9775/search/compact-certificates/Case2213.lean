import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a2213 : Array Fact := #[(.lab 0 0 0),(.lab 0 0 6),(.avoid 0 1102 0),(.res 0 4),(.res 1 4),(.res 0 8),(.res 1 8),(.res 0 9),(.res 1 9),(.res 0 10),(.res 1 10),(.res 0 13),(.res 1 13),(.lab 2 0 0),(.lab 2 0 6),(.avoid 2 8297 0),(.live 4 1),(.lab 4 0 3),(.lab 4 0 8),(.common 4 8),(.common 4 10),(.live 4 2),(.lab 4 1 3),(.lab 4 1 8),(.live 4 3),(.lab 4 2 3),(.lab 4 2 8),(.lab 4 3 3),(.lab 4 3 8),(.avoid 4 1290 0),(.avoid 4 1290 1),(.avoid 4 1290 2),(.avoid 4 1290 3),(.see 4 11 314 0),(.see 4 11 314 1),(.see 4 11 314 2),(.see 4 11 314 3),(.diff 0 4 8),(.diff 1 4 8),(.lab 6 0 6),(.lab 6 1 6),(.lab 6 2 6),(.lab 6 3 6),(.live 8 1),(.common 8 9),(.lab 8 0 10),(.common 8 10),(.lab 8 0 13),(.common 8 13),(.live 8 2),(.lab 8 1 10),(.lab 8 1 13),(.live 8 3),(.lab 8 2 10),(.lab 8 2 13),(.avoid 8 9288 0),(.avoid 8 9288 1),(.avoid 8 9288 2),(.avoid 8 9288 3),(.see 8 0 9992 0),(.see 8 0 9992 1),(.see 8 0 9992 2),(.see 8 0 9992 3),(.see 8 2 9992 0),(.see 8 2 9992 1),(.see 8 2 9992 2),(.see 8 2 9992 3),(.diff 0 8 10),(.diff 1 8 10),(.diff 0 8 13),(.diff 1 8 13),(.live 9 1),(.lab 9 0 4),(.lab 9 0 8),(.common 9 10),(.lab 9 0 12),(.live 9 2),(.lab 9 1 4),(.lab 9 1 8),(.lab 9 1 12),(.live 9 3),(.lab 9 2 8),(.lab 9 2 12),(.avoid 9 4183 0),(.avoid 9 4183 1),(.avoid 9 4183 2),(.avoid 9 4183 3),(.avoid 9 4370 0),(.avoid 9 4370 1),(.avoid 9 4370 2),(.avoid 9 4370 3),(.see 9 5 4757 0),(.see 9 5 4757 1),(.see 9 5 4757 2),(.see 9 5 4757 3),(.see 9 5 5008 0),(.see 9 5 5008 1),(.see 9 5 5008 2),(.see 9 5 5008 3),(.diff 0 9 8),(.diff 1 9 8),(.lab 10 0 10),(.live 10 1),(.lab 10 0 4),(.lab 10 0 8),(.lab 10 0 9),(.lab 10 0 12),(.lab 10 0 13),(.common 10 13),(.lab 10 1 10),(.live 10 2),(.lab 10 1 4),(.lab 10 1 8),(.lab 10 1 9),(.lab 10 1 12),(.lab 10 1 13),(.lab 10 2 10),(.live 10 3),(.lab 10 2 4),(.lab 10 2 8),(.lab 10 2 9),(.lab 10 2 12),(.lab 10 2 13),(.lab 10 3 10),(.lab 10 3 12),(.lab 10 3 13),(.avoid 10 541 0),(.avoid 10 541 1),(.avoid 10 541 2),(.avoid 10 541 3),(.avoid 10 792 0),(.avoid 10 792 1),(.avoid 10 792 2),(.avoid 10 792 3),(.avoid 10 4183 0),(.avoid 10 4183 1),(.avoid 10 4183 2),(.avoid 10 4183 3),(.avoid 10 4370 0),(.avoid 10 4370 1),(.avoid 10 4370 2),(.avoid 10 4370 3),(.avoid 10 5008 0),(.avoid 10 5008 1),(.avoid 10 5008 2),(.avoid 10 5008 3),(.avoid 10 8488 0),(.avoid 10 8488 1),(.avoid 10 8488 2),(.avoid 10 8488 3),(.avoid 10 12481 0),(.avoid 10 12481 1),(.avoid 10 12481 2),(.avoid 10 12481 3),(.see 10 0 1290 0),(.see 10 0 1290 1),(.see 10 0 1290 2),(.see 10 0 1290 3),(.see 10 0 7426 0),(.see 10 0 7426 1),(.see 10 0 7426 2),(.see 10 0 7426 3),(.see 10 0 9992 0),(.see 10 0 9992 1),(.see 10 0 9992 2),(.see 10 0 9992 3),(.see 10 5 7426 0),(.see 10 5 7426 1),(.see 10 5 7426 2),(.see 10 5 7426 3),(.see 10 5 7812 0),(.see 10 5 7812 1),(.see 10 5 7812 2),(.see 10 5 7812 3),(.see 10 5 13504 0),(.see 10 5 13504 1),(.see 10 5 13504 2),(.see 10 5 13504 3),(.see 10 5 16256 0),(.see 10 5 16256 1),(.see 10 5 16256 2),(.see 10 5 16256 3),(.diff 0 10 4),(.diff 1 10 4),(.diff 0 10 8),(.diff 1 10 8),(.diff 0 10 9),(.diff 1 10 9),(.diff 0 10 13),(.diff 1 10 13),(.lab 11 0 10),(.lab 11 0 13),(.avoid 11 1102 0),(.avoid 11 8297 0),(.lab 12 0 12),(.lab 12 1 12),(.lab 12 2 12),(.lab 12 3 12),(.lab 13 0 13),(.live 13 1),(.live 13 0),(.lab 13 0 8),(.lab 13 0 10),(.lab 13 1 13),(.live 13 2),(.lab 13 1 8),(.lab 13 1 10),(.lab 13 2 13),(.live 13 3),(.lab 13 2 8),(.lab 13 2 10),(.lab 13 3 13),(.avoid 13 314 0),(.avoid 13 314 1),(.avoid 13 314 2),(.avoid 13 314 3),(.avoid 13 1290 0),(.avoid 13 1290 1),(.avoid 13 1290 2),(.avoid 13 1290 3),(.avoid 13 7426 0),(.avoid 13 7426 1),(.avoid 13 7426 2),(.avoid 13 7426 3),(.see 13 2 8488 0),(.see 13 2 8488 1),(.see 13 2 8488 2),(.see 13 2 8488 3),(.see 13 2 9992 0),(.see 13 2 9992 1),(.see 13 2 9992 2),(.see 13 2 9992 3),(.diff 0 13 10),(.diff 1 13 10),(.reader false 0 0),(.es false 0 0),(.es false 0 6),(.reader false 5 0),(.es false 5 0),(.es false 5 6),(.reader false 10 0),(.reader false 10 1),(.reader false 10 2),(.reader false 10 3),(.reader false 11 0),(.reader false 11 1),(.reader false 11 2),(.reader false 11 3),(.reader false 12 0),(.reader false 12 1),(.reader false 12 2),(.reader false 12 3),(.reader false 13 0),(.reader false 14 0),(.reader false 15 0),(.reader false 16 0),(.reader false 16 1),(.reader false 16 2),(.reader false 16 3),(.es false 16 6),(.reader true 0 0),(.reader true 0 1),(.reader true 0 2),(.reader true 0 3),(.reader true 5 0),(.reader true 5 1),(.reader true 5 2),(.reader true 5 3),(.reader true 10 0),(.reader true 10 1),(.reader true 10 2),(.reader true 10 3),(.es true 10 10),(.reader true 11 0),(.es true 11 10),(.es true 11 13),(.reader true 12 0),(.reader true 12 1),(.reader true 12 2),(.reader true 12 3),(.es true 12 10),(.es true 12 13),(.reader true 13 0),(.reader true 13 1),(.reader true 13 2),(.reader true 13 3),(.es true 13 4),(.reader true 14 0),(.reader true 14 1),(.reader true 14 2),(.reader true 14 3),(.es true 14 4),(.es true 14 12),(.reader true 15 0),(.reader true 15 1),(.reader true 15 2),(.reader true 15 3),(.es true 15 12),(.reader true 16 0),(.reader true 16 1),(.reader true 16 2),(.reader true 16 3),(.gate 0 5),(.gate 0 16),(.gate 5 16),(.gate 10 11),(.gate 10 12),(.gate 11 12),(.gate 13 14),(.gate 14 15)]
def r2213 : List Scheme := [(.self 0 0),(.exposure 0 1102),(.avoidNot 0 6 1102 0),(.exposure 2 8297),(.avoidNot 2 0 8297 0),(.avoidNot 2 6 8297 0),(.earlier 4 1),(.earlier 4 2),(.someRes 4),(.allRes 4 0),(.allRes 4 1),(.exposure 4 1290),(.avoidNot 4 3 1290 0),(.avoidNot 4 8 1290 0),(.avoidNot 4 3 1290 1),(.avoidNot 4 8 1290 1),(.avoidNot 4 3 1290 2),(.avoidNot 4 8 1290 2),(.avoidLive 4 1290 3),(.avoidNot 4 3 1290 3),(.avoidNot 4 8 1290 3),(.exactAt 4 11 314),(.seeLab 4 11 3 314 0),(.seeLab 4 11 8 314 0),(.seeLab 4 11 3 314 1),(.seeLab 4 11 8 314 1),(.seeLab 4 11 3 314 2),(.seeLab 4 11 8 314 2),(.seeLive 4 11 314 3),(.seeLab 4 11 3 314 3),(.seeLab 4 11 8 314 3),(.diffX 0 4 8),(.diffC 0 4 8),(.resCommon 4 8 0),(.diffX 1 4 8),(.diffC 1 4 8),(.resCommon 4 8 1),(.residual 4 8 0 1),(.residual 4 8 0 2),(.residual 4 8 0 3),(.residual 4 8 1 2),(.residual 4 8 1 3),(.residual 4 8 2 3),(.resCommon 4 10 0),(.resCommon 4 10 1),(.self 6 0),(.self 6 1),(.self 6 2),(.self 6 3),(.earlier 8 1),(.someRes 8),(.allRes 8 0),(.allRes 8 1),(.exposure 8 9288),(.avoidNot 8 10 9288 0),(.avoidNot 8 13 9288 0),(.avoidNot 8 10 9288 1),(.avoidNot 8 13 9288 1),(.avoidNot 8 10 9288 2),(.avoidNot 8 13 9288 2),(.avoidLive 8 9288 3),(.exactAt 8 0 9992),(.seeLab 8 0 10 9992 0),(.seeLab 8 0 13 9992 0),(.seeLab 8 0 10 9992 1),(.seeLab 8 0 13 9992 1),(.seeLab 8 0 10 9992 2),(.seeLab 8 0 13 9992 2),(.seeLive 8 0 9992 3),(.exactAt 8 2 9992),(.seeLab 8 2 10 9992 0),(.seeLab 8 2 13 9992 0),(.seeLab 8 2 10 9992 1),(.seeLab 8 2 13 9992 1),(.seeLab 8 2 10 9992 2),(.seeLab 8 2 13 9992 2),(.seeLive 8 2 9992 3),(.resCommon 8 9 0),(.resCommon 8 9 1),(.diffX 0 8 10),(.diffC 0 8 10),(.diffX 1 8 10),(.diffC 1 8 10),(.adjacentCommon 8 10 0),(.residual 8 10 0 1),(.residual 8 10 0 2),(.residual 8 10 1 2),(.diffX 0 8 13),(.diffC 0 8 13),(.diffX 1 8 13),(.diffC 1 8 13),(.adjacentCommon 8 13 2),(.residual 8 13 0 1),(.residual 8 13 0 2),(.residual 8 13 1 2),(.earlier 9 1),(.someRes 9),(.allRes 9 0),(.allRes 9 1),(.exposure 9 4183),(.avoidNot 9 4 4183 0),(.avoidNot 9 12 4183 0),(.avoidNot 9 4 4183 1),(.avoidNot 9 12 4183 1),(.avoidLive 9 4183 2),(.avoidLive 9 4183 3),(.exposure 9 4370),(.avoidNot 9 8 4370 0),(.avoidNot 9 12 4370 0),(.avoidNot 9 8 4370 1),(.avoidNot 9 12 4370 1),(.avoidNot 9 8 4370 2),(.avoidNot 9 12 4370 2),(.avoidLive 9 4370 3),(.exactAt 9 5 4757),(.seeLab 9 5 4 4757 0),(.seeLab 9 5 12 4757 0),(.seeLab 9 5 4 4757 1),(.seeLab 9 5 12 4757 1),(.seeLive 9 5 4757 2),(.seeLive 9 5 4757 3),(.exactAt 9 5 5008),(.seeLab 9 5 8 5008 0),(.seeLab 9 5 12 5008 0),(.seeLab 9 5 8 5008 1),(.seeLab 9 5 12 5008 1),(.seeLab 9 5 8 5008 2),(.seeLab 9 5 12 5008 2),(.seeLive 9 5 5008 3),(.diffX 0 9 8),(.diffC 0 9 8),(.diffX 1 9 8),(.diffC 1 9 8),(.residual 9 8 0 1),(.residual 9 8 0 2),(.residual 9 8 1 2),(.adjacentCommon 9 10 5),(.self 10 0),(.self 10 1),(.earlier 10 1),(.self 10 2),(.earlier 10 2),(.self 10 3),(.allRes 10 0),(.allRes 10 1),(.exposure 10 541),(.avoidNot 10 4 541 0),(.avoidNot 10 4 541 1),(.avoidNot 10 9 541 2),(.avoidLive 10 541 3),(.exposure 10 792),(.avoidNot 10 8 792 0),(.avoidNot 10 9 792 0),(.avoidNot 10 8 792 1),(.avoidNot 10 9 792 1),(.avoidNot 10 4 792 2),(.avoidNot 10 8 792 2),(.avoidNot 10 9 792 2),(.avoidLive 10 792 3),(.exposure 10 4183),(.avoidNot 10 4 4183 0),(.avoidNot 10 12 4183 0),(.avoidNot 10 4 4183 1),(.avoidNot 10 12 4183 1),(.avoidNot 10 4 4183 2),(.avoidLive 10 4183 3),(.exposure 10 4370),(.avoidNot 10 8 4370 0),(.avoidNot 10 12 4370 0),(.avoidNot 10 8 4370 1),(.avoidNot 10 12 4370 1),(.avoidLive 10 4370 2),(.avoidNot 10 8 4370 2),(.avoidNot 10 12 4370 2),(.avoidLive 10 4370 3),(.exposure 10 5008),(.avoidNot 10 8 5008 0),(.avoidNot 10 4 5008 1),(.avoidNot 10 12 5008 2),(.avoidLive 10 5008 3),(.exposure 10 8488),(.avoidNot 10 13 8488 0),(.avoidNot 10 8 8488 1),(.avoidNot 10 13 8488 1),(.avoidNot 10 8 8488 2),(.avoidNot 10 13 8488 2),(.avoidNot 10 13 8488 3),(.exposure 10 12481),(.avoidNot 10 12 12481 0),(.avoidNot 10 13 12481 0),(.avoidNot 10 13 12481 1),(.avoidNot 10 13 12481 2),(.avoidNot 10 12 12481 3),(.avoidNot 10 13 12481 3),(.exactAt 10 0 1290),(.seeLab 10 0 8 1290 0),(.seeLab 10 0 8 1290 1),(.seeLab 10 0 8 1290 2),(.seeLive 10 0 1290 3),(.exactAt 10 0 7426),(.seeLab 10 0 8 7426 0),(.seeLab 10 0 12 7426 0),(.seeLab 10 0 8 7426 1),(.seeLab 10 0 12 7426 1),(.seeLive 10 0 7426 2),(.seeLab 10 0 8 7426 2),(.seeLab 10 0 12 7426 2),(.seeLive 10 0 7426 3),(.exactAt 10 0 9992),(.seeLab 10 0 8 9992 0),(.seeLab 10 0 9 9992 0),(.seeLab 10 0 13 9992 0),(.seeLab 10 0 8 9992 1),(.seeLab 10 0 9 9992 1),(.seeLab 10 0 13 9992 1),(.seeLab 10 0 8 9992 2),(.seeLab 10 0 9 9992 2),(.seeLab 10 0 13 9992 2),(.seeLive 10 0 9992 3),(.seeLab 10 0 13 9992 3),(.exactAt 10 5 7426),(.seeLab 10 5 8 7426 0),(.seeLab 10 5 12 7426 0),(.seeLab 10 5 8 7426 1),(.seeLab 10 5 12 7426 1),(.seeLab 10 5 8 7426 2),(.seeLab 10 5 12 7426 2),(.seeLive 10 5 7426 3),(.exactAt 10 5 7812),(.seeLab 10 5 12 7812 0),(.seeLab 10 5 12 7812 1),(.seeLab 10 5 9 7812 2),(.seeLive 10 5 7812 3),(.exactAt 10 5 13504),(.seeLab 10 5 12 13504 0),(.seeLive 10 5 13504 1),(.seeLab 10 5 12 13504 1),(.seeLab 10 5 13 13504 1),(.seeLive 10 5 13504 2),(.seeLab 10 5 13 13504 2),(.seeLive 10 5 13504 3),(.seeLab 10 5 13 13504 3),(.exactAt 10 5 16256),(.seeLab 10 5 12 16256 0),(.seeLab 10 5 13 16256 0),(.seeLab 10 5 8 16256 1),(.seeLab 10 5 13 16256 1),(.seeLive 10 5 16256 2),(.seeLab 10 5 9 16256 2),(.seeLab 10 5 13 16256 2),(.seeLive 10 5 16256 3),(.seeLab 10 5 12 16256 3),(.diffX 0 10 4),(.diffC 0 10 4),(.diffX 1 10 4),(.diffC 1 10 4),(.residual 10 4 0 1),(.residual 10 4 0 2),(.residual 10 4 1 2),(.diffX 0 10 8),(.diffC 0 10 8),(.diffX 1 10 8),(.diffC 1 10 8),(.residual 10 8 0 1),(.residual 10 8 0 2),(.residual 10 8 1 2),(.diffX 0 10 9),(.diffC 0 10 9),(.diffX 1 10 9),(.diffC 1 10 9),(.residual 10 9 0 1),(.residual 10 9 0 2),(.residual 10 9 1 2),(.diffC 0 10 13),(.diffC 1 10 13),(.resCommon 10 13 1),(.residual 10 13 0 1),(.residual 10 13 0 2),(.residual 10 13 0 3),(.residual 10 13 1 2),(.residual 10 13 1 3),(.residual 10 13 2 3),(.exposure 11 1102),(.avoidNot 11 10 1102 0),(.exposure 11 8297),(.avoidNot 11 13 8297 0),(.self 12 0),(.self 12 1),(.self 12 2),(.self 12 3),(.self 13 0),(.earlier 13 0),(.labCommon 13 10 0),(.self 13 1),(.earlier 13 1),(.labCommon 13 10 1),(.self 13 2),(.labCommon 13 10 2),(.self 13 3),(.allRes 13 0),(.allRes 13 1),(.exposure 13 314),(.avoidNot 13 8 314 0),(.avoidLive 13 314 1),(.avoidLive 13 314 2),(.avoidLive 13 314 3),(.exposure 13 1290),(.avoidNot 13 8 1290 0),(.avoidNot 13 10 1290 0),(.avoidNot 13 8 1290 1),(.avoidNot 13 10 1290 1),(.avoidLive 13 1290 2),(.avoidNot 13 8 1290 2),(.avoidNot 13 10 1290 2),(.avoidLive 13 1290 3),(.exposure 13 7426),(.avoidNot 13 10 7426 0),(.avoidNot 13 10 7426 1),(.avoidNot 13 8 7426 2),(.avoidLive 13 7426 3),(.exactAt 13 2 8488),(.seeLab 13 2 8 8488 0),(.seeLive 13 2 8488 1),(.seeLive 13 2 8488 2),(.seeLive 13 2 8488 3),(.exactAt 13 2 9992),(.seeLab 13 2 8 9992 0),(.seeLab 13 2 10 9992 0),(.seeLab 13 2 8 9992 1),(.seeLab 13 2 10 9992 1),(.seeLive 13 2 9992 2),(.seeLab 13 2 8 9992 2),(.seeLab 13 2 10 9992 2),(.seeLive 13 2 9992 3),(.diffX 0 13 10),(.diffC 0 13 10),(.diffX 1 13 10),(.diffC 1 13 10),(.residual 13 10 0 1),(.residual 13 10 0 2),(.residual 13 10 1 2),(.readerAny false 0),(.readerLab false 0 0 0 true),(.readerLab false 0 0 6 false),(.readerAny false 5),(.readerLab false 5 0 0 false),(.readerLab false 5 0 6 false),(.readerAny false 10),(.readerLive false 10 2),(.readerLive false 10 3),(.readerAny false 11),(.readerLive false 11 2),(.readerLive false 11 3),(.readerAny false 12),(.readerLive false 12 2),(.readerLive false 12 3),(.readerAny false 13),(.readerAny false 14),(.readerAny false 15),(.readerAny false 16),(.readerLab false 16 0 6 true),(.readerLab false 16 1 6 true),(.readerLab false 16 2 6 true),(.readerLab false 16 3 6 true),(.readerAny true 0),(.readerLive true 0 2),(.readerLive true 0 3),(.readerAny true 5),(.readerLive true 5 2),(.readerLive true 5 3),(.readerAny true 10),(.readerLab true 10 0 10 true),(.readerLab true 10 1 10 true),(.readerLab true 10 2 10 true),(.readerLab true 10 3 10 true),(.readerAny true 11),(.readerLab true 11 0 10 false),(.readerLab true 11 0 13 false),(.readerAny true 12),(.readerLab true 12 0 10 false),(.readerLab true 12 0 13 true),(.readerLab true 12 1 10 false),(.readerLab true 12 1 13 true),(.readerLive true 12 2),(.readerLab true 12 2 10 false),(.readerLab true 12 2 13 true),(.readerLive true 12 3),(.readerLab true 12 3 13 true),(.readerAny true 13),(.readerLab true 13 0 4 false),(.readerLab true 13 1 4 false),(.readerLive true 13 2),(.readerLive true 13 3),(.readerAny true 14),(.readerLab true 14 0 4 true),(.readerLab true 14 0 12 false),(.readerLab true 14 1 4 true),(.readerLab true 14 1 12 false),(.readerLab true 14 2 4 true),(.readerLab true 14 2 12 false),(.readerLive true 14 3),(.readerAny true 15),(.readerLab true 15 0 12 true),(.readerLab true 15 1 12 true),(.readerLab true 15 2 12 true),(.readerLab true 15 3 12 true),(.readerAny true 16),(.readerLive true 16 2),(.readerLive true 16 3),(.eqLab false 0 5 0 true),(.gateEq true 0 5 0),(.gateEq true 0 5 1),(.eqLab false 0 16 6 false),(.gateEq true 0 16 0),(.gateEq true 0 16 1),(.eqLab false 5 16 6 false),(.gateEq true 5 16 0),(.gateEq true 5 16 1),(.gateEq false 10 11 0),(.gateEq false 10 11 1),(.eqLab true 10 11 10 true),(.gateEq false 10 12 0),(.gateEq false 10 12 1),(.eqLab true 10 12 10 true),(.gateEq false 11 12 0),(.gateEq false 11 12 1),(.eqLab true 11 12 13 false),(.gateEq false 13 14 0),(.eqLab true 13 14 4 false),(.gateEq false 14 15 0),(.eqLab true 14 15 12 false)]

def table2213_0 : List Nat := [65,321,0x20102,0x7c1,0x1a0782,0x1c0782,0x210a82,0x2b0c02,0x24070a83,0x70c02,0x90c02,0x410fc3d0ec4,0x220e82,0x240e82,0x2c0f02,0x2e0f02]
def table2213_1 : List Nat := [0x320f82,0x340f82,0x311002,0x361002,0x381002,0x4911c4510c4,0x231082,0x241082,0x2d1102,0x2e1102,0x331182,0x341182,0x311202,0x371202,0x381202,0x71282]
def table2213_2 : List Nat := [0xa1282,0x9c0a0183,0x91302,0xc1302,0x9c0c0203,0x4d12c2f094200986,0x4d12c350942a0986,0x4d12c39094300986,0x4d12c350bc2a0986,0x4d12c390bc300986,0x4d12c390d4300986,0xa4120183,0xa4140203,0x13c1,0x1441,0x14c1]
def table2213_3 : List Nat := [0x1541,0x571882,0x340b1883,0xb1a02,0xd1a02,0x751cc711bc4,0x5a1b82,0x5e1b82,0x641c02,0x661c02,0x6a1c82,0x6c1c82,0x691d02,0x7d1ec791dc4,0x5b1d82,0x5e1d82]
def table2213_4 : List Nat := [0x651e02,0x661e02,0x6b1e82,0x6c1e82,0x691f02,0x8520c811fc4,0x5a1f82,0x5f1f82,0x642002,0x672002,0x6a2082,0x6d2082,0x692102,0x1640e0283,0x164100303,0xb2182]
def table2213_5 : List Nat := [0x122182,0xd2202,0x142202,0x1741,0x8921c6516c561706,0x8921c6b16c621706,0x8921c6b194621706,0xb2282,0x162282,0xd2302,0x182302,0x1841,0x8d22c6717c561806,0x8d22c6d17c621806,0x8d22c6d19c621806,0x8f2602]
def table2213_6 : List Nat := [0x440f2603,0xf2802,0x112802,0xad2aca929c4,0x902982,0x962982,0x9a2a02,0x9e2a02,0x992a82,0xa12b02,0xb52ccb12bc4,0x922b82,0x962b82,0x9c2c02,0x9e2c02,0xa22c82]
def table2213_7 : List Nat := [0xa42c82,0xa12d02,0xbd2ecb92dc4,0x902d82,0x972d82,0x9a2e02,0x9f2e02,0x992e82,0xa12f02,0xc530cc12fc4,0x922f82,0x972f82,0x9c3002,0x9f3002,0xa23082,0xa53082]
def table2213_8 : List Nat := [0xa13102,0xf3182,0xa3182,0x113202,0xc3202,0xc931c9d24c8e1606,0xc931ca324c981606,0xc931ca3274981606,0x2541,0x32c1,0x36c1,0xcd3702,0x3a41,0xdd3a82,0x3dc1,0x133a82]
def table2213_9 : List Nat := [0x153a82,0x103404ff3f44,0xce3f02,0xde3f82,0xf04002,0xeb4082,0x10b425074144,0xd04102,0xd24102,0xe04182,0xe24182,0xec4202,0xee4202,0xf04202,0xeb4282,0x1134450f4344]
def table2213_10 : List Nat := [0xce4302,0xd44302,0xde4382,0xe44382,0xec4402,0xeb4482,0x11b465174544,0xd04502,0xd44502,0xe04582,0xe44582,0xdd4602,0xee4602,0xf24602,0xeb4682,0x1234851f4744]
def table2213_11 : List Nat := [0xd04702,0xde4782,0xf24802,0xeb4882,0x12b4a5274944,0xd64902,0xe04982,0xe64982,0xee4a02,0xf44a02,0xfa4a82,0x1334c52f4b44,0xd44b02,0xd64b02,0xe64b82,0xf44c02]
def table2213_12 : List Nat := [0xf84c82,0xfa4c82,0x13b4e5374d44,0xd14d02,0xe14d82,0xef4e02,0xeb4e82,0x1435053f4f44,0xd14f02,0xd44f02,0xe14f82,0xe44f82,0xdd5002,0xef5002,0xf25002,0xeb5082]
def table2213_13 : List Nat := [0x14b525475144,0xd15102,0xd25102,0xd65102,0xe15182,0xe25182,0xe65182,0xef5202,0xf05202,0xf45202,0xeb5282,0xfa5282,0x1535454f5344,0xd05302,0xd55302,0xe05382]
def table2213_14 : List Nat := [0xe55382,0xee5402,0xf35402,0xeb5482,0x15b565575544,0xd55502,0xe55582,0xf15602,0xeb5682,0x1635855f5744,0xd55702,0xcd5782,0xe55782,0xe65782,0xdd5802,0xf45802]
def table2213_15 : List Nat := [0xeb5882,0xfa5882,0x16b5a5675944,0xd55902,0xd65902,0xe05982,0xe65982,0xdd5a02,0xf15a02,0xf45a02,0xeb5a82,0xf95a82,0x135b02,0x65b02,0x155b82,0x85b82]
def table2213_16 : List Nat := [0x16f5b4df33ccc0a06,0x16f5b4ed33cdc0a06,0x16f5b4ed37cdc0a06,0x135c02,0xa5c02,0x155c82,0xc5c82,0x1735c4e1344cc1706,0x1735c4ef344dc1706,0x1735c4ef384dc1706,0x135d02,0xe5d02,0x155d82,0x105d82,0x1775d4e334ccc2506,0x1775d4f134cdc2506]
def table2213_17 : List Nat := [0x1775d4f138cdc2506,0x165e02,0x185e82,0x364180503,0x17b5e4e735ccc3606,0x17b5e4f535cdc3606,0x17b5e4fb35cea3606,0x17b5e4f539cdc3606,0x17b5e4fb39cea3606,0x17b5e4fb3d4ea3606,0x6041,0x17c6002,0x60c1,0x17e6082,0x6141,0x61c1]
def table2213_18 : List Nat := [0x6241,0x62c1,0x6341,0x1916382,0x365946403,0x65c1,0x18f6602,0x3659c6383,0x67c1,0x365a46603,0x69c1,0x176802,0x196802,0x1af6b5ab6a44,0x1926a02,0x18f6a82]
def table2213_19 : List Nat := [0x1996b02,0x1a16b82,0x1b76d5b36c44,0x1926c02,0x1946c02,0x19a6c82,0x19c6c82,0x1996d02,0x1a26d02,0x1a46d02,0x1a16d82,0x1bf6f5bb6e44,0x1946e02,0x19c6e82,0x1a26f02,0x1a16f82]
def table2213_20 : List Nat := [0x1c7715c37044,0x1937002,0x18f7082,0x1997102,0x1a17182,0x1cf735cb7244,0x1937202,0x1947202,0x19b7282,0x19c7282,0x1997302,0x1a37302,0x1a47302,0x1a17382,0x177402,0x127402]
def table2213_21 : List Nat := [0x197482,0x147482,0x1d37459d6558e3606,0x1d3745a5655983606,0x1d3745a5675983606,0x7541,0x75c007503,0x760037503,0x76c1,0x7701b7683,0x7781d7683,0x1e7795e37844,0x2b7902,0x317982,0x1ef7b5eb7a44,0x2b7b02]
def table2213_22 : List Nat := [0x317b82,0x1f77d5f37c44,0x2b7d02,0x317d82,0x7e41,0x7ec1,0x7f41,0x20580e017fc4,0x81c4e7f83,0x81c508003,0x81c528083,0x81c548103,0x20f8360b8244,0x638302,0x698382,0x217856138444]
def table2213_23 : List Nat := [0x638502,0x698582,0x21f8761b8644,0x884ca8603,0x884da8683,0x884e88703,0x884f68783,0x88c1,0x8917d8883,0x8997f8883,0x22f8b62b8a44,0x8c1958a03,0x8cd8c8a03,0x8c19d8a83,0x8cd968a83,0x1998b02]
def table2213_24 : List Nat := [0x8c1a58b03,0x8cd9e8b03,0x1a18b82,0x8cda68b83,0x23b8e6378d44,0x8f0918d03,0x8f09b8d83,0x998e02,0xa18e82,0x24590e418fc4,0x91cce8f83,0x920d58f83,0x91cde9003,0x920e59003,0x91cec9083,0x920f39083]
def table2213_25 : List Nat := [0xeb9102,0x25193e4d92c4,0x94d849283,0x94d869303,0x94d889383,0x94d8a9403,0x25b966579544,0x639602,0x699682,0x775d69703,0x976108203,0x976128283,0x819d99783,0x97e548203,0x97e568283,0x819df9803]
def table2213_26 : List Nat := [0x986548403,0x986568483,0x98de87803,0x98dea7883,0x896209883,0x995f07803,0x995f27883,0x8c6209903,0x99df07a03,0x99df27a83,0x8ca279983,0x9a5fa7e03,0x91a3d9a03,0x9adfc7e83,0x94a499a83,129]
def table2213_27 : List Nat := [0x681,0x701,0x224871945b1585,0x224871ac5b1885,0x224871ac651885,0x2348b19c5f1585,0x2348b1b45f1885,0x2348b1b4671885,0x5cd71384d13305,0x5cd713bcd13705,0x5cd713bce13705,0x5dd7538cd33305,0x5dd753c4d33705,0x5dd753c4e33705,0x5f01,0x5f81]
def table2213_28 : List Nat := [0x75c1,0x7601,0x7701,0x7781,0x2077f82,0x2078002,0x2078082,0x2078102,0x2218602,0x2218682,0x2218702,0x2218782,0x8901,0x8981,0x2338a02,0x2338a82]
def table2213_29 : List Nat := [0x2338b02,0x2338b82,0x2539282,0x2539302,0x2539382,0x2539402,0x9701,0x2108202,0x2128282,0x2069782,0x2069802,0x2209882,0x2329982,0x9a41,0x2468f42,0x9ac1]
def table2213_30 : List Nat := [0x2529242,0x8cc1,0x9981,0x8841,0x9881,0x81c1,0x9781,0x9801,0x3a9a05a03,0x3712d5e57b3613335c7,0xea681255184,0xea681255204,0xea4b5a04cc4,0x3a92d6803,0x1a163c2,0x685946643]
def table2213_31 : List Nat := [0xea6ddb1361987286,0x3a9a16503,0x6859c6903,0x3a9a16703,0x8c0d98b03,0x8c0ea6843,0x2303a82,0x3acd43743,0xeb4554d3b84,0xeb1a0d43804,0x3ac683503,0xeb1a0dc3844,0x3ac683703,0xeb1a02,0xeb3742,0x744d8685d36545]
def table2213_32 : List Nat := [0x685946703,0x1d1361a174c4,0xeb43d6f5b42837c6,0x3240f260583085,0xc903c8e160c32b86,0xc903c8e160c32c06,0x300f2603,0x8ee3926c918f05,0x94c1,0x9241,0x1d487188892085,0x8521c56224831b86,0x8521c56224831c06,0x6921c622244,0x1f48b234621c85,0x691cc7b1984]
def table2213_33 : List Nat := [0x1a48b234621ec5,0x6922c8d1884,0x1a4639583,0x6918c2,0x2305c02,0x2305c82,0x2304502,0x2303442,0x8c01,0x9901,0xea1a42,0x79def795ed7c85,0x1a0410a8261185,0x6812420098470e86,0x6812420098470f06,0x1a0411242a0985]
def table2213_34 : List Nat := [0x1a0301043,0x680c02,0x680a82,0x1a01,0x18c1,0x3a81,0x4081,0x4281,0x4481,0x4681,0x4881,0x4e81,0x5081,0x5281,0x5481,0x5681]
def table2213_35 : List Nat := [0x5a81,0x9101,0xd03802,0x3741,0x310ac2,0x411242e0904,0x284992403,0x8f0a12643,0x31cc92d498160af24c7,0x31cc92d498160af3087,0x31cc92d4c5260582bc7,0x2a3c0443,0x330d03cc080285,0x330d03cc270205,0xcc341775d44,0xcc340f309c4]
def table2213_36 : List Nat := [0x10f048df0184,0x98411344b1242a0b87,0x9010f098415d05,0xcc340f31044,0x330d03cc3,0xdf908305d04,0x330d00c03,0x3112c261344,0xdf050ed0204,0xdf908315d84,0xdf048ed0184,0xcc3402,0x3440891cdf9085,0x20070303,0x331735c43,0xcc020df3b44]
def table2213_37 : List Nat := [0x3300891cdf5c05,0xcc0224737c4,0x16f91d0f0a16d8f86,0x4f40891cff43e410507,0x3300891c3,0x8f00c03c3,0xcc5dd753c84,0xd15dd753844,0xcc020de0484,0x330083783,0xcc425755dc4,0x23c5d82,0xcc0202,0xcc5d24337c4,0x3317490c3,0xcc5d02]
def table2213_38 : List Nat := [0x90282,0x3301]

def encoded2213 (i : Nat) : Nat :=
  if i < 304 then
    if i < 144 then
      if i < 64 then
        if i < 32 then
          if i < 16 then
            table2213_0.getD (i%16) 0
          else
            table2213_1.getD (i%16) 0
        else
          if i < 48 then
            table2213_2.getD (i%16) 0
          else
            table2213_3.getD (i%16) 0
      else
        if i < 96 then
          if i < 80 then
            table2213_4.getD (i%16) 0
          else
            table2213_5.getD (i%16) 0
        else
          if i < 112 then
            table2213_6.getD (i%16) 0
          else
            if i < 128 then
              table2213_7.getD (i%16) 0
            else
              table2213_8.getD (i%16) 0
    else
      if i < 224 then
        if i < 176 then
          if i < 160 then
            table2213_9.getD (i%16) 0
          else
            table2213_10.getD (i%16) 0
        else
          if i < 192 then
            table2213_11.getD (i%16) 0
          else
            if i < 208 then
              table2213_12.getD (i%16) 0
            else
              table2213_13.getD (i%16) 0
      else
        if i < 256 then
          if i < 240 then
            table2213_14.getD (i%16) 0
          else
            table2213_15.getD (i%16) 0
        else
          if i < 272 then
            table2213_16.getD (i%16) 0
          else
            if i < 288 then
              table2213_17.getD (i%16) 0
            else
              table2213_18.getD (i%16) 0
  else
    if i < 464 then
      if i < 384 then
        if i < 336 then
          if i < 320 then
            table2213_19.getD (i%16) 0
          else
            table2213_20.getD (i%16) 0
        else
          if i < 352 then
            table2213_21.getD (i%16) 0
          else
            if i < 368 then
              table2213_22.getD (i%16) 0
            else
              table2213_23.getD (i%16) 0
      else
        if i < 416 then
          if i < 400 then
            table2213_24.getD (i%16) 0
          else
            table2213_25.getD (i%16) 0
        else
          if i < 432 then
            table2213_26.getD (i%16) 0
          else
            if i < 448 then
              table2213_27.getD (i%16) 0
            else
              table2213_28.getD (i%16) 0
    else
      if i < 544 then
        if i < 496 then
          if i < 480 then
            table2213_29.getD (i%16) 0
          else
            table2213_30.getD (i%16) 0
        else
          if i < 512 then
            table2213_31.getD (i%16) 0
          else
            if i < 528 then
              table2213_32.getD (i%16) 0
            else
              table2213_33.getD (i%16) 0
      else
        if i < 576 then
          if i < 560 then
            table2213_34.getD (i%16) 0
          else
            table2213_35.getD (i%16) 0
        else
          if i < 592 then
            table2213_36.getD (i%16) 0
          else
            if i < 608 then
              table2213_37.getD (i%16) 0
            else
              table2213_38.getD (i%16) 0
def book2213 (i : Nat) : Clause := let n := encoded2213 i; unpackLits 10 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses2213 : inputsOK 2 2213 a2213 r2213 (baseBook book2213 431).toList=true := by decide +kernel

def rows2213_0 : List Nat := [0x80401,0x180801,0x180a01,0x298a801,0x298aa01,0x298ac01,0x2d8b801,0x2d8ba01,0x2d8bc01,0x29a0e01,0x29a1001,0x29a1201,0x4421c01,0x4421e01,0x4422001,0x8d23601,0x8e23a01,0xaaaac02,0x35eaaaae02,0x360ac2b202,0x362ac2b402,0x16ad001,0x172d201,0x17ad401]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2213_0 : checkRows book2213 10 431 rows2213_0=true := by decide +kernel

def rows2213_1 : List Nat := [0x182d601,0x44ae601,0x452e801,0x462ea01,0x472ec01,0x37cbbaf002,0x37ebbaf202,0x912f801,0x92afc01,0x9430201,0x9530601,0x8f32401,0x8fb2601,0x9032801,0x90b2a01,0x384e033202,0xeb33401,0xeb33601,0xe0b3801,0xe1b3e01,0xe634801,0xe6b5401,0x2cab235602,0xeeb5801]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2213_1 : checkRows book2213 10 455 rows2213_1=true := by decide +kernel

def rows2213_2 : List Nat := [0x2ccb2b5a02,0xefb5c01,0x3a2e839ee72f404,0xf0bb801,0x396e5392e42e404,0xf1bb601,0x38ee338ae22ce04,0xf2bb201,0xf2bb401,0x1ac699b68ba2a8c9b07c9f046a2295a2489a58481a010,0x5f97c8aa284597605,0x1745ca308b96c6b1a846a2295a2489a58481680e,0x16e5d22e8c9706c9ae46a2295a2489a58481680e,0x17e5f2328c1b6683d6f51a65abd246a2295a2489a584817612,0x7b1e88c22c7d982603d8f42268922296256481e40f,0x28296a80a1a60a125e93262a225c0a,0x9aa8a992949ba74a6a68a3a9009,0x992a89aa92a429e47aa24827209,0x9daa89f298a5a8af83de9228e9e268a791ea89209d27ea6a46f727a15,0x99a8a992989ca74a6a6ca4a8c09,0x266a2a64a526ea9be4a4a6c93a9e47aa248274a6bdcf8a8c12,0x300bfa5202,0x304fa2a4bebe6bdbe2f729e47aa2482f40c,0x789de76a2c8aa287517a5e22689222f6a5895bea45920469d213]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2213_2 : checkRows book2213 10 479 rows2213_2=true := by decide +kernel

def rows2213_3 : List Nat := [0x5498e531985595c679506499409,0x551b8531c25615c719c007,0x1ba7137256958531be5495c71a0819a0c1a150fb9b810,0xfc370dd3f245bee5420819a0c1a1ba0b,0x3f0dc37482066830686f3f44594e0a,0x5395adc9c4709b86f952fd95c71a0819a0c1a1bcfd14c11,0x14cdc1547a9d8759e4749ee77156fe1e6753f4832081a066571e07d14e16,0x5398e53196551d8749d4fb9dc661565719e781900f,0x99a8a992949baa6f92929b2a49d29af728c0d,0x9c28a992929b274a6a68a3a9609,0x9aa8a992989caa9003dea3a68ffa74a6a900d,0x501488020452916ff13e07,0xda358e04390c3f8fc408e2308d40a,0xf83d90a360d640900308f208,0xf43e90a370da40900308f208,0x3e0f44390c378d502c090189c300be4210238900308f211,0x30ac330802,0x3aaea3a6e932204,0x1043c001,0x1c06c1db68d98962506a07,0x2408ed906e1b08a05,0x23092d90721c08a05,0x9023368d98741ac1905c141e0981888a0c,0x2087edbb6c210761d07a07]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2213_3 : checkRows book2213 10 503 rows2213_3=true := by decide +kernel

def rows2213_4 : List Nat := [0x1b07a1a8821c8782207c07,0x1c07a1a87e1bb6b0787818c1c220800b,0x1c86edbb6c21c21070782206a09,0x2deb6342cf2dcb8adab83cef33ae0a,0x2deb6340ceb2d0932eb82dab72e2cc3cef33b00e,0x2f4bea48fa24e91c02f7304a82582d4222ba9e8220709bfafb2f614,0x2f4bea48fa24e91c02f7304a72562c4222caa28320b09bfafb2f614,0x6f9c2dc3726f150539c645bfcfb4290a9b80d,0x54958dc37257116ff3ed0a42b0b14c0b,0x15a6e14c6f952dd3f06ec2f0b42b0a3fc7195cfb1c410,0x3c70c34e02,0x1098a0478a44841a05,0xaf2b6d4b4cf23c50cb4407,0x681e13050080360d040198461a0160b,0xa84a0b01a06040198461a03209,0xa84a0c01e07040198461a02e09,0x2e0c84c1402205c3d0ec3810066118680302a0e,0x681e0884e148540f43e100461a00e10812198160f,0x2e0c836138521503a0a0271004204840198461a02a10,0x4810c3e19868090391081008,0xaf2b6d434ab0c36b12beae2c0aec44b1c42f23c50cb4611,0x111c2601,0x111c3401,0x11292a01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2213_4 : checkRows book2213 10 527 rows2213_4=true := by decide +kernel

def rows2213_5 : List Nat := [0x11293c01,0x11294a01,0x11295c01,0x11296601,0x11298c01,0x11299e01,0x1129b401,0x1129c601,0x1129d001,0x1129f401,0x112b2001,0x569b8531be5494e6ec5d149c409,0x112bfc01,0xaf2b6d434ab0c36b12beae2bab02c6f23c50cb460f,0x802a0582e0681e0c83407,0x338e4318e6320d23c0d03b8ec09,0x328e4318ea3340f1b30e3b8d0348f0c40e80d,0x368de4290c2f8d405,0x368e0438fe3f0d405,0x378dc438fa3e0f31c8f51c0d409,0x3e0fc3d90a430d835c74268c02fc6e400e2418c4410f211,0x4d13addb7886c76ef31901058851f82841a2920add2084b9a4681a86bb12c7b166498e6546466bf053946701b8711ba7fc4f19c4b124471746304c591692c31,0x124791206403,0x4d13addb784b9a4681a9191aefc14e6ec4f19c4b1692c11]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2213_5 : checkRows book2213 10 551 rows2213_5=true := by decide +kernel

def rows2213_6 : List Nat := [0x40c30a171f3bcc640415a06861fcdd0a48341a1909e109fa044680547ac4b1ec5992639951919afc14e519c06e1c46ec4b19c4911c5d18c131646e2e,0x159fa7f0a5068a112c471240409,0x602a058360884d1a8320782c09,0x702a0582e068360884a14482034680e03e04c80c63bd1bc0c118a3068c22821685449118301d,0x1c0a8160b81a0d822128512080d1a038110151e04027c1a292191f484c4b1ec5992639951919afc14e519c06e1c46ec7f124471746304c59128302e,0xef40c30b1885c811f206863742920d0686427c780501209486519c0c49b8c79c4c5992639951919afc14e6ec671244718c5d04c5912c6e2b,0x3bd0331c28a05068c2158a085a147e8127f81519c4911c6e12,0x11db1c27a05068582921a8647d229fe7e814049625796458312c69545315b223166498e6546466bf0539bb19c4911c6304c5912c53153bc2b,0x1c0a8160b81a0d82212851208240e00d1a0300e,0x161fe7e0a1068a519c471220409,0x48e040452431cef4761009f068a486a191a4491184210,0x159fa7f0a5068a119c471220409,0x48e0403f2531cef46f0304628c1a308a085a151f4931a48cc4b1a589545794c5915b223166498e66994fc4646e96053c4911c6304c5514c59128482e,0x120460f8121949482206dc9c26e1bc5414c6f9526520a63c906715ac731e6444919c5d14c5904c8e1f,0x48118120fc8e04,0x6f14c6e1be549c256370dcc9714c5d199500d,0x652520881c9c82c911249a08,0xc6b1451a01200567ec9a19208819ff2649718c131231211,0xc6b1451a01011f82841a160a482c9d28499259ff18c1312c4911b1215,0x14850a02c5b15144670493e08,0x791507c14c4a1ea549226512463a026715ac731ec4ca47e0a106858291ff184531345919c1318c49119e621,0x1e4541f0531287a952489944918e8099c56b1cc7b13290567ec9a1920881c9c82ca6c614449ca2644967fc6114c4d1646704c63121e62a,0x40c30c6e02,0x1306a92c6813a6b9ce709c86e1ca6f150531cc6f9524c9966518e6715a641a325c4f16c5f174531637620]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2213_6 : checkRows book2213 10 575 rows2213_6=true := by decide +kernel

def rows2213_7 : List Nat := [0x4d130deb784e1b0629a0611a86218668c4f19c5b1592c11,0x4a1aa489a0491ae809585214c4f950509bc6e1be54cae714ac85caa159fa8649a290a3068a068c967fbbd2a126514671345b14c511744911b7a2d,0x4a1aa489a0491ae809585214c4f950509bc6e1be549c52bcac86c76190588320b27214819f92c144499a3259feef4a919c4d16c531445d1237a2d,0x6c1aade3764c12c4ccae68c9716c67139a00d,0x106c762921a864491189e07,0x41b2a8a085a152d4b64dc9f2cbbd2a447120a20e,0x31251b15202007e85604468054b87f0a4ef4aa28c1a2821485c1318c471231a18,0x4a4c61452e9fa158111a0152e1fc293bd2a8a3068a08521718c471231216,0x1e4541f0531287a952489944912663a028119c56b1cc7cbcef1fd2a8a428c1a158a085a14644967e8111a0152e46114c4d1646704c49119e62c,0x4210044044680548e06,0x6837a6b93a4e4b4860a50689f304bf2e1a325c5b19c49119aa13]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2213_7 : checkRows book2213 10 599 rows2213_7=true := by decide +kernel

def lastUnits2213 := digits 10 2 0x98633
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict2213 : checkReasons book2213 610 139 lastUnits2213 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude2213 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 2213=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=2) h hc bp eq (by decide +kernel)
  let v := truth Z a2213
  have hbase : ValidThrough v book2213 431 := book_start Z h hc z eq _ _ _ _ initialClauses2213
  have h0 : ValidThrough v book2213 455 := rows_sound hbase rows2213_0 rowsOk2213_0
  have h1 : ValidThrough v book2213 479 := rows_sound h0 rows2213_1 rowsOk2213_1
  have h2 : ValidThrough v book2213 503 := rows_sound h1 rows2213_2 rowsOk2213_2
  have h3 : ValidThrough v book2213 527 := rows_sound h2 rows2213_3 rowsOk2213_3
  have h4 : ValidThrough v book2213 551 := rows_sound h3 rows2213_4 rowsOk2213_4
  have h5 : ValidThrough v book2213 575 := rows_sound h4 rows2213_5 rowsOk2213_5
  have h6 : ValidThrough v book2213 599 := rows_sound h5 rows2213_6 rowsOk2213_6
  have h7 : ValidThrough v book2213 610 := rows_sound h6 rows2213_7 rowsOk2213_7
  exact book_end h7 _ _ conflict2213
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
