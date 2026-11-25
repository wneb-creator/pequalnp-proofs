import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a111 : Array Fact := #[(.res 0 8),(.res 1 8),(.res 2 8),(.res 0 9),(.res 1 9),(.res 2 9),(.res 0 11),(.res 1 11),(.res 2 11),(.res 0 13),(.res 1 13),(.res 2 13),(.lab 1 0 1),(.lab 1 0 4),(.avoid 1 245 0),(.lab 2 0 1),(.lab 2 0 4),(.avoid 2 314 0),(.lab 3 0 3),(.lab 3 0 4),(.avoid 3 245 0),(.lab 4 0 4),(.lab 4 1 4),(.lab 4 2 4),(.lab 4 3 4),(.lab 4 4 4),(.lab 6 0 3),(.lab 6 0 4),(.avoid 6 314 0),(.live 8 1),(.lab 8 0 9),(.common 8 9),(.lab 8 0 10),(.lab 8 0 11),(.common 8 11),(.lab 8 0 13),(.common 8 13),(.live 8 2),(.lab 8 1 9),(.lab 8 1 10),(.lab 8 1 11),(.lab 8 1 13),(.live 8 3),(.lab 8 2 9),(.lab 8 2 10),(.lab 8 2 11),(.lab 8 2 13),(.live 8 4),(.lab 8 3 9),(.lab 8 3 10),(.lab 8 3 11),(.lab 8 3 13),(.avoid 8 1548 0),(.avoid 8 1548 1),(.avoid 8 1548 2),(.avoid 8 1548 3),(.avoid 8 1548 4),(.avoid 8 7174 0),(.avoid 8 7174 1),(.avoid 8 7174 2),(.avoid 8 7174 3),(.avoid 8 7174 4),(.avoid 8 8713 0),(.avoid 8 8713 1),(.avoid 8 8713 2),(.avoid 8 8713 3),(.avoid 8 8713 4),(.avoid 8 9288 0),(.avoid 8 9288 1),(.avoid 8 9288 2),(.avoid 8 9288 3),(.avoid 8 9288 4),(.avoid 8 10401 0),(.avoid 8 10401 1),(.avoid 8 10401 2),(.avoid 8 10401 3),(.avoid 8 10401 4),(.see 8 0 7426 0),(.see 8 0 7426 1),(.see 8 0 7426 2),(.see 8 0 7426 3),(.see 8 0 7426 4),(.see 8 0 9992 0),(.see 8 0 9992 1),(.see 8 0 9992 2),(.see 8 0 9992 3),(.see 8 0 9992 4),(.see 8 0 16256 0),(.see 8 0 16256 1),(.see 8 0 16256 2),(.see 8 0 16256 3),(.see 8 0 16256 4),(.see 8 2 8488 0),(.see 8 2 8488 1),(.see 8 2 8488 2),(.see 8 2 8488 3),(.see 8 2 8488 4),(.see 8 2 9992 0),(.see 8 2 9992 1),(.see 8 2 9992 2),(.see 8 2 9992 3),(.see 8 2 9992 4),(.see 8 2 10656 0),(.see 8 2 10656 1),(.see 8 2 10656 2),(.see 8 2 10656 3),(.see 8 2 10656 4),(.see 8 2 16256 0),(.see 8 2 16256 1),(.see 8 2 16256 2),(.see 8 2 16256 3),(.see 8 2 16256 4),(.see 8 6 9992 0),(.see 8 6 9992 1),(.see 8 6 9992 2),(.see 8 6 9992 3),(.see 8 6 9992 4),(.diff 0 8 9),(.diff 1 8 9),(.diff 2 8 9),(.diff 0 8 11),(.diff 1 8 11),(.diff 2 8 11),(.diff 0 8 13),(.diff 1 8 13),(.diff 2 8 13),(.live 9 1),(.lab 9 0 7),(.lab 9 0 8),(.lab 9 0 11),(.common 9 11),(.common 9 13),(.live 9 2),(.lab 9 1 7),(.lab 9 1 8),(.lab 9 1 11),(.lab 9 1 13),(.live 9 3),(.lab 9 2 7),(.lab 9 2 8),(.lab 9 2 11),(.lab 9 2 13),(.live 9 4),(.lab 9 3 7),(.lab 9 3 8),(.lab 9 3 11),(.lab 9 4 7),(.lab 9 4 8),(.avoid 9 432 0),(.avoid 9 432 1),(.avoid 9 432 2),(.avoid 9 432 3),(.avoid 9 432 4),(.avoid 9 2213 0),(.avoid 9 2213 1),(.avoid 9 2213 2),(.avoid 9 2213 3),(.avoid 9 2213 4),(.avoid 9 8488 0),(.avoid 9 8488 1),(.avoid 9 8488 2),(.avoid 9 8488 3),(.avoid 9 8488 4),(.avoid 9 10401 0),(.avoid 9 10401 1),(.avoid 9 10401 2),(.avoid 9 10401 3),(.avoid 9 10401 4),(.see 9 1 5008 0),(.see 9 1 5008 1),(.see 9 1 5008 2),(.see 9 1 5008 3),(.see 9 1 5008 4),(.see 9 1 6789 0),(.see 9 1 6789 1),(.see 9 1 6789 2),(.see 9 1 6789 3),(.see 9 1 6789 4),(.see 9 1 9992 0),(.see 9 1 9992 1),(.see 9 1 9992 2),(.see 9 1 9992 3),(.see 9 1 9992 4),(.see 9 5 16256 0),(.see 9 5 16256 1),(.see 9 5 16256 2),(.see 9 5 16256 3),(.see 9 5 16256 4),(.see 9 6 792 0),(.see 9 6 792 1),(.see 9 6 792 2),(.see 9 6 792 3),(.see 9 6 792 4),(.see 9 6 6789 0),(.see 9 6 6789 1),(.see 9 6 6789 2),(.see 9 6 6789 3),(.see 9 6 6789 4),(.see 9 6 9992 0),(.see 9 6 9992 1),(.see 9 6 9992 2),(.see 9 6 9992 3),(.see 9 6 9992 4),(.see 9 6 16256 0),(.see 9 6 16256 1),(.see 9 6 16256 2),(.see 9 6 16256 3),(.see 9 6 16256 4),(.diff 0 9 8),(.diff 1 9 8),(.diff 2 9 8),(.diff 0 9 11),(.diff 1 9 11),(.diff 2 9 11),(.live 11 1),(.lab 11 0 7),(.lab 11 0 8),(.lab 11 0 12),(.lab 11 0 13),(.common 11 13),(.live 11 2),(.lab 11 1 7),(.lab 11 1 8),(.lab 11 1 12),(.lab 11 1 13),(.live 11 3),(.lab 11 2 7),(.lab 11 2 8),(.lab 11 2 12),(.lab 11 2 13),(.live 11 4),(.lab 11 3 7),(.lab 11 3 8),(.lab 11 3 12),(.lab 11 3 13),(.avoid 11 4370 0),(.avoid 11 4370 1),(.avoid 11 4370 2),(.avoid 11 4370 3),(.avoid 11 4370 4),(.avoid 11 8417 0),(.avoid 11 8417 1),(.avoid 11 8417 2),(.avoid 11 8417 3),(.avoid 11 8417 4),(.see 11 3 7426 0),(.see 11 3 7426 1),(.see 11 3 7426 2),(.see 11 3 7426 3),(.see 11 3 7426 4),(.see 11 3 10401 0),(.see 11 3 10401 1),(.see 11 3 10401 2),(.see 11 3 10401 3),(.see 11 3 10401 4),(.see 11 6 16256 0),(.see 11 6 16256 1),(.see 11 6 16256 2),(.see 11 6 16256 3),(.see 11 6 16256 4),(.diff 0 11 8),(.diff 1 11 8),(.diff 2 11 8),(.diff 0 11 13),(.diff 1 11 13),(.diff 2 11 13),(.live 13 1),(.lab 13 0 8),(.lab 13 0 9),(.live 13 2),(.lab 13 1 8),(.lab 13 1 9),(.live 13 3),(.lab 13 2 8),(.lab 13 2 9),(.live 13 4),(.lab 13 3 8),(.lab 13 3 9),(.avoid 13 792 0),(.avoid 13 792 1),(.avoid 13 792 2),(.avoid 13 792 3),(.avoid 13 792 4),(.see 13 1 9992 0),(.see 13 1 9992 1),(.see 13 1 9992 2),(.see 13 1 9992 3),(.see 13 1 9992 4),(.see 13 2 9992 0),(.see 13 2 9992 1),(.see 13 2 9992 2),(.see 13 2 9992 3),(.see 13 2 9992 4),(.see 13 2 16256 0),(.see 13 2 16256 1),(.see 13 2 16256 2),(.see 13 2 16256 3),(.see 13 2 16256 4),(.diff 0 13 8),(.diff 1 13 8),(.diff 2 13 8),(.diff 0 13 9),(.diff 1 13 9),(.diff 2 13 9),(.reader false 4 0),(.es false 4 1),(.es false 4 4),(.reader false 6 0),(.es false 6 1),(.es false 6 4),(.reader false 8 0),(.es false 8 3),(.es false 8 4),(.reader false 11 0),(.reader false 11 1),(.reader false 11 2),(.reader false 11 3),(.reader false 11 4),(.es false 11 4),(.reader false 12 0),(.reader false 12 1),(.reader false 12 2),(.reader false 12 3),(.reader false 12 4),(.es false 12 4),(.reader false 18 0),(.es false 18 3),(.es false 18 4),(.reader true 4 0),(.reader true 4 1),(.reader true 4 2),(.reader true 4 3),(.reader true 4 4),(.reader true 6 0),(.reader true 6 1),(.reader true 6 2),(.reader true 6 3),(.reader true 6 4),(.reader true 8 0),(.reader true 8 1),(.reader true 8 2),(.reader true 8 3),(.reader true 8 4),(.reader true 11 0),(.reader true 11 1),(.reader true 11 2),(.reader true 11 3),(.reader true 11 4),(.reader true 12 0),(.reader true 12 1),(.reader true 12 2),(.reader true 12 3),(.reader true 12 4),(.reader true 18 0),(.reader true 18 1),(.reader true 18 2),(.reader true 18 3),(.reader true 18 4),(.gate 4 6),(.gate 4 12),(.gate 6 12),(.gate 8 11),(.gate 8 18),(.gate 11 18)]
def r111 : List Scheme := [(.self 1 0),(.exposure 1 245),(.avoidNot 1 4 245 0),(.exposure 2 314),(.avoidNot 2 1 314 0),(.avoidNot 2 4 314 0),(.self 3 0),(.exposure 3 245),(.avoidNot 3 4 245 0),(.self 4 0),(.self 4 1),(.self 4 2),(.self 4 3),(.self 4 4),(.exposure 6 314),(.avoidNot 6 3 314 0),(.avoidNot 6 4 314 0),(.earlier 8 1),(.earlier 8 2),(.allRes 8 0),(.allRes 8 1),(.allRes 8 2),(.exposure 8 1548),(.avoidNot 8 9 1548 0),(.avoidNot 8 10 1548 0),(.avoidNot 8 9 1548 1),(.avoidNot 8 10 1548 1),(.avoidNot 8 9 1548 2),(.avoidNot 8 10 1548 2),(.avoidLive 8 1548 3),(.avoidNot 8 9 1548 3),(.avoidNot 8 10 1548 3),(.avoidLive 8 1548 4),(.exposure 8 7174),(.avoidNot 8 11 7174 0),(.avoidNot 8 10 7174 1),(.avoidNot 8 11 7174 1),(.avoidNot 8 10 7174 2),(.avoidNot 8 11 7174 2),(.avoidNot 8 11 7174 3),(.avoidLive 8 7174 4),(.exposure 8 8713),(.avoidNot 8 13 8713 0),(.avoidNot 8 9 8713 1),(.avoidLive 8 8713 2),(.avoidLive 8 8713 3),(.avoidLive 8 8713 4),(.exposure 8 9288),(.avoidNot 8 10 9288 0),(.avoidNot 8 13 9288 0),(.avoidNot 8 10 9288 1),(.avoidNot 8 13 9288 1),(.avoidLive 8 9288 2),(.avoidNot 8 10 9288 2),(.avoidNot 8 13 9288 2),(.avoidLive 8 9288 3),(.avoidNot 8 10 9288 3),(.avoidNot 8 13 9288 3),(.avoidLive 8 9288 4),(.exposure 8 10401),(.avoidNot 8 11 10401 0),(.avoidNot 8 13 10401 0),(.avoidNot 8 11 10401 1),(.avoidNot 8 11 10401 2),(.avoidNot 8 13 10401 2),(.avoidLive 8 10401 3),(.avoidNot 8 11 10401 3),(.avoidNot 8 13 10401 3),(.avoidLive 8 10401 4),(.exactAt 8 0 7426),(.seeLab 8 0 11 7426 0),(.seeLab 8 0 10 7426 1),(.seeLab 8 0 11 7426 1),(.seeLab 8 0 10 7426 2),(.seeLab 8 0 11 7426 2),(.seeLab 8 0 11 7426 3),(.seeLive 8 0 7426 4),(.exactAt 8 0 9992),(.seeLab 8 0 9 9992 0),(.seeLab 8 0 10 9992 0),(.seeLab 8 0 13 9992 0),(.seeLab 8 0 9 9992 1),(.seeLab 8 0 10 9992 1),(.seeLab 8 0 13 9992 1),(.seeLive 8 0 9992 2),(.seeLab 8 0 9 9992 2),(.seeLab 8 0 10 9992 2),(.seeLab 8 0 13 9992 2),(.seeLive 8 0 9992 3),(.seeLab 8 0 9 9992 3),(.seeLab 8 0 10 9992 3),(.seeLab 8 0 13 9992 3),(.seeLive 8 0 9992 4),(.exactAt 8 0 16256),(.seeLab 8 0 9 16256 0),(.seeLab 8 0 11 16256 0),(.seeLab 8 0 13 16256 1),(.seeLab 8 0 9 16256 2),(.seeLab 8 0 11 16256 2),(.seeLive 8 0 16256 3),(.seeLive 8 0 16256 4),(.exactAt 8 2 8488),(.seeLab 8 2 13 8488 0),(.seeLab 8 2 13 8488 1),(.seeLive 8 2 8488 2),(.seeLive 8 2 8488 3),(.seeLive 8 2 8488 4),(.exactAt 8 2 9992),(.seeLab 8 2 9 9992 0),(.seeLab 8 2 13 9992 0),(.seeLive 8 2 9992 1),(.seeLab 8 2 9 9992 1),(.seeLab 8 2 13 9992 1),(.seeLive 8 2 9992 2),(.seeLab 8 2 9 9992 2),(.seeLab 8 2 13 9992 2),(.seeLive 8 2 9992 3),(.seeLab 8 2 9 9992 3),(.seeLive 8 2 9992 4),(.exactAt 8 2 10656),(.seeLab 8 2 13 10656 0),(.seeLab 8 2 11 10656 1),(.seeLab 8 2 11 10656 2),(.seeLab 8 2 11 10656 3),(.seeLive 8 2 10656 4),(.exactAt 8 2 16256),(.seeLab 8 2 11 16256 0),(.seeLab 8 2 13 16256 0),(.seeLab 8 2 11 16256 1),(.seeLab 8 2 13 16256 1),(.seeLab 8 2 9 16256 2),(.seeLab 8 2 11 16256 2),(.seeLab 8 2 13 16256 2),(.seeLive 8 2 16256 3),(.seeLab 8 2 13 16256 3),(.seeLive 8 2 16256 4),(.exactAt 8 6 9992),(.seeLab 8 6 9 9992 0),(.seeLab 8 6 13 9992 0),(.seeLab 8 6 9 9992 1),(.seeLab 8 6 13 9992 1),(.seeLive 8 6 9992 2),(.seeLab 8 6 9 9992 2),(.seeLive 8 6 9992 3),(.seeLab 8 6 9 9992 3),(.seeLive 8 6 9992 4),(.diffX 0 8 9),(.diffC 0 8 9),(.diffX 1 8 9),(.diffC 1 8 9),(.diffX 2 8 9),(.diffC 2 8 9),(.adjacentCommon 8 9 6),(.residual 8 9 0 1),(.residual 8 9 0 2),(.residual 8 9 0 3),(.residual 8 9 1 2),(.residual 8 9 1 3),(.residual 8 9 2 3),(.diffX 0 8 11),(.diffC 0 8 11),(.diffX 1 8 11),(.diffC 1 8 11),(.diffX 2 8 11),(.diffC 2 8 11),(.adjacentCommon 8 11 6),(.residual 8 11 0 1),(.residual 8 11 0 2),(.residual 8 11 0 3),(.residual 8 11 1 2),(.residual 8 11 1 3),(.residual 8 11 2 3),(.diffX 0 8 13),(.diffC 0 8 13),(.diffX 1 8 13),(.diffC 1 8 13),(.diffX 2 8 13),(.diffC 2 8 13),(.adjacentCommon 8 13 2),(.residual 8 13 0 1),(.residual 8 13 0 2),(.residual 8 13 0 3),(.residual 8 13 1 2),(.residual 8 13 1 3),(.residual 8 13 2 3),(.earlier 9 1),(.earlier 9 2),(.earlier 9 3),(.allRes 9 0),(.allRes 9 1),(.allRes 9 2),(.exposure 9 432),(.avoidNot 9 7 432 0),(.avoidNot 9 8 432 0),(.avoidNot 9 7 432 1),(.avoidNot 9 8 432 1),(.avoidNot 9 8 432 2),(.avoidLive 9 432 3),(.avoidNot 9 7 432 3),(.avoidNot 9 8 432 3),(.avoidLive 9 432 4),(.avoidNot 9 7 432 4),(.avoidNot 9 8 432 4),(.exposure 9 2213),(.avoidNot 9 7 2213 0),(.avoidNot 9 11 2213 0),(.avoidNot 9 7 2213 1),(.avoidNot 9 11 2213 1),(.avoidLive 9 2213 2),(.avoidNot 9 7 2213 2),(.avoidNot 9 11 2213 2),(.avoidLive 9 2213 3),(.avoidNot 9 7 2213 3),(.avoidNot 9 11 2213 3),(.avoidLive 9 2213 4),(.exposure 9 8488),(.avoidNot 9 8 8488 0),(.avoidNot 9 8 8488 1),(.avoidNot 9 13 8488 1),(.avoidLive 9 8488 2),(.avoidNot 9 13 8488 2),(.avoidLive 9 8488 3),(.avoidNot 9 8 8488 3),(.avoidLive 9 8488 4),(.exposure 9 10401),(.avoidNot 9 11 10401 0),(.avoidNot 9 11 10401 1),(.avoidNot 9 7 10401 2),(.avoidNot 9 11 10401 3),(.avoidLive 9 10401 4),(.exactAt 9 1 5008),(.seeLab 9 1 7 5008 0),(.seeLab 9 1 8 5008 0),(.seeLab 9 1 7 5008 1),(.seeLab 9 1 8 5008 1),(.seeLab 9 1 8 5008 2),(.seeLive 9 1 5008 3),(.seeLab 9 1 7 5008 3),(.seeLab 9 1 8 5008 3),(.seeLive 9 1 5008 4),(.seeLab 9 1 7 5008 4),(.seeLab 9 1 8 5008 4),(.exactAt 9 1 6789),(.seeLab 9 1 7 6789 0),(.seeLab 9 1 11 6789 0),(.seeLab 9 1 7 6789 1),(.seeLab 9 1 11 6789 1),(.seeLive 9 1 6789 2),(.seeLab 9 1 7 6789 2),(.seeLab 9 1 11 6789 2),(.seeLive 9 1 6789 3),(.seeLab 9 1 7 6789 3),(.seeLab 9 1 11 6789 3),(.seeLive 9 1 6789 4),(.exactAt 9 1 9992),(.seeLab 9 1 8 9992 0),(.seeLab 9 1 8 9992 1),(.seeLab 9 1 13 9992 1),(.seeLive 9 1 9992 2),(.seeLab 9 1 13 9992 2),(.seeLive 9 1 9992 3),(.seeLab 9 1 8 9992 3),(.seeLive 9 1 9992 4),(.seeLab 9 1 8 9992 4),(.exactAt 9 5 16256),(.seeLab 9 5 7 16256 0),(.seeLab 9 5 8 16256 0),(.seeLab 9 5 7 16256 1),(.seeLab 9 5 8 16256 1),(.seeLab 9 5 11 16256 1),(.seeLive 9 5 16256 2),(.seeLab 9 5 7 16256 2),(.seeLab 9 5 8 16256 2),(.seeLab 9 5 11 16256 2),(.seeLab 9 5 13 16256 2),(.seeLive 9 5 16256 3),(.seeLab 9 5 7 16256 3),(.seeLab 9 5 8 16256 3),(.seeLab 9 5 11 16256 3),(.seeLive 9 5 16256 4),(.seeLab 9 5 8 16256 4),(.exactAt 9 6 792),(.seeLab 9 6 8 792 0),(.seeLab 9 6 8 792 1),(.seeLab 9 6 8 792 2),(.seeLive 9 6 792 3),(.seeLive 9 6 792 4),(.exactAt 9 6 6789),(.seeLab 9 6 7 6789 0),(.seeLab 9 6 11 6789 0),(.seeLab 9 6 11 6789 1),(.seeLive 9 6 6789 2),(.seeLive 9 6 6789 3),(.seeLive 9 6 6789 4),(.exactAt 9 6 9992),(.seeLab 9 6 8 9992 0),(.seeLab 9 6 8 9992 1),(.seeLive 9 6 9992 2),(.seeLive 9 6 9992 3),(.seeLive 9 6 9992 4),(.exactAt 9 6 16256),(.seeLab 9 6 8 16256 0),(.seeLab 9 6 11 16256 1),(.seeLab 9 6 8 16256 2),(.seeLive 9 6 16256 3),(.seeLive 9 6 16256 4),(.diffX 0 9 8),(.diffC 0 9 8),(.diffX 1 9 8),(.diffC 1 9 8),(.diffX 2 9 8),(.diffC 2 9 8),(.residual 9 8 0 1),(.residual 9 8 0 2),(.residual 9 8 0 3),(.residual 9 8 0 4),(.residual 9 8 1 2),(.residual 9 8 1 3),(.residual 9 8 1 4),(.residual 9 8 2 3),(.residual 9 8 2 4),(.residual 9 8 3 4),(.diffX 0 9 11),(.diffC 0 9 11),(.diffX 1 9 11),(.diffC 1 9 11),(.diffX 2 9 11),(.diffC 2 9 11),(.adjacentCommon 9 11 6),(.residual 9 11 0 1),(.residual 9 11 0 2),(.residual 9 11 0 3),(.residual 9 11 1 2),(.residual 9 11 1 3),(.residual 9 11 2 3),(.adjacentCommon 9 13 1),(.earlier 11 1),(.earlier 11 2),(.someRes 11),(.allRes 11 0),(.allRes 11 1),(.allRes 11 2),(.exposure 11 4370),(.avoidNot 11 8 4370 0),(.avoidNot 11 12 4370 0),(.avoidNot 11 8 4370 1),(.avoidNot 11 12 4370 1),(.avoidNot 11 8 4370 2),(.avoidNot 11 12 4370 2),(.avoidLive 11 4370 3),(.avoidNot 11 8 4370 3),(.avoidNot 11 12 4370 3),(.avoidLive 11 4370 4),(.exposure 11 8417),(.avoidNot 11 13 8417 0),(.avoidNot 11 7 8417 1),(.avoidNot 11 13 8417 1),(.avoidNot 11 7 8417 2),(.avoidNot 11 13 8417 2),(.avoidLive 11 8417 3),(.avoidNot 11 13 8417 3),(.avoidLive 11 8417 4),(.exactAt 11 3 7426),(.seeLab 11 3 8 7426 0),(.seeLab 11 3 12 7426 0),(.seeLab 11 3 8 7426 1),(.seeLab 11 3 12 7426 1),(.seeLab 11 3 8 7426 2),(.seeLab 11 3 12 7426 2),(.seeLive 11 3 7426 3),(.seeLab 11 3 8 7426 3),(.seeLab 11 3 12 7426 3),(.seeLive 11 3 7426 4),(.exactAt 11 3 10401),(.seeLab 11 3 7 10401 0),(.seeLab 11 3 13 10401 0),(.seeLab 11 3 7 10401 1),(.seeLab 11 3 13 10401 1),(.seeLab 11 3 7 10401 2),(.seeLab 11 3 13 10401 2),(.seeLive 11 3 10401 3),(.seeLab 11 3 7 10401 3),(.seeLab 11 3 13 10401 3),(.seeLive 11 3 10401 4),(.exactAt 11 6 16256),(.seeLab 11 6 7 16256 0),(.seeLab 11 6 13 16256 0),(.seeLab 11 6 13 16256 1),(.seeLab 11 6 13 16256 2),(.seeLive 11 6 16256 3),(.seeLab 11 6 7 16256 3),(.seeLab 11 6 13 16256 3),(.seeLive 11 6 16256 4),(.diffX 0 11 8),(.diffC 0 11 8),(.diffX 1 11 8),(.diffC 1 11 8),(.diffX 2 11 8),(.diffC 2 11 8),(.residual 11 8 0 1),(.residual 11 8 0 2),(.residual 11 8 0 3),(.residual 11 8 1 2),(.residual 11 8 1 3),(.residual 11 8 2 3),(.diffX 0 11 13),(.diffC 0 11 13),(.resCommon 11 13 0),(.diffX 1 11 13),(.diffC 1 11 13),(.resCommon 11 13 1),(.diffX 2 11 13),(.diffC 2 11 13),(.resCommon 11 13 2),(.residual 11 13 0 1),(.residual 11 13 0 2),(.residual 11 13 0 3),(.residual 11 13 1 2),(.residual 11 13 1 3),(.residual 11 13 2 3),(.earlier 13 1),(.earlier 13 2),(.allRes 13 0),(.allRes 13 1),(.allRes 13 2),(.exposure 13 792),(.avoidNot 13 8 792 0),(.avoidNot 13 9 792 0),(.avoidNot 13 8 792 1),(.avoidNot 13 9 792 1),(.avoidNot 13 8 792 2),(.avoidNot 13 9 792 2),(.avoidLive 13 792 3),(.avoidNot 13 8 792 3),(.avoidNot 13 9 792 3),(.avoidLive 13 792 4),(.exactAt 13 1 9992),(.seeLab 13 1 8 9992 0),(.seeLab 13 1 9 9992 0),(.seeLab 13 1 8 9992 1),(.seeLab 13 1 9 9992 1),(.seeLab 13 1 8 9992 2),(.seeLab 13 1 9 9992 2),(.seeLive 13 1 9992 3),(.seeLab 13 1 8 9992 3),(.seeLab 13 1 9 9992 3),(.seeLive 13 1 9992 4),(.exactAt 13 2 9992),(.seeLab 13 2 8 9992 0),(.seeLab 13 2 9 9992 0),(.seeLab 13 2 9 9992 1),(.seeLab 13 2 8 9992 2),(.seeLab 13 2 9 9992 2),(.seeLive 13 2 9992 3),(.seeLab 13 2 9 9992 3),(.seeLive 13 2 9992 4),(.exactAt 13 2 16256),(.seeLab 13 2 9 16256 0),(.seeLab 13 2 8 16256 1),(.seeLab 13 2 9 16256 1),(.seeLab 13 2 9 16256 2),(.seeLive 13 2 16256 3),(.seeLab 13 2 8 16256 3),(.seeLab 13 2 9 16256 3),(.seeLive 13 2 16256 4),(.diffX 0 13 8),(.diffC 0 13 8),(.diffX 1 13 8),(.diffC 1 13 8),(.diffX 2 13 8),(.diffC 2 13 8),(.residual 13 8 0 1),(.residual 13 8 0 2),(.residual 13 8 0 3),(.residual 13 8 1 2),(.residual 13 8 1 3),(.residual 13 8 2 3),(.diffX 0 13 9),(.diffC 0 13 9),(.diffX 1 13 9),(.diffC 1 13 9),(.diffX 2 13 9),(.diffC 2 13 9),(.residual 13 9 0 1),(.residual 13 9 0 2),(.residual 13 9 0 3),(.residual 13 9 1 2),(.residual 13 9 1 3),(.residual 13 9 2 3),(.readerAny false 4),(.readerLab false 4 0 1 true),(.readerLab false 4 0 4 false),(.readerAny false 6),(.readerLab false 6 0 1 false),(.readerLab false 6 0 4 false),(.readerAny false 8),(.readerLab false 8 0 3 true),(.readerLab false 8 0 4 false),(.readerAny false 11),(.readerLab false 11 0 4 true),(.readerLab false 11 1 4 true),(.readerLab false 11 2 4 true),(.readerLab false 11 3 4 true),(.readerLab false 11 4 4 true),(.readerAny false 12),(.readerLab false 12 0 4 true),(.readerLab false 12 1 4 true),(.readerLab false 12 2 4 true),(.readerLab false 12 3 4 true),(.readerLab false 12 4 4 true),(.readerAny false 18),(.readerLab false 18 0 3 false),(.readerLab false 18 0 4 false),(.readerAny true 4),(.readerLive true 4 2),(.readerLive true 4 3),(.readerLive true 4 4),(.readerAny true 6),(.readerLive true 6 2),(.readerLive true 6 3),(.readerLive true 6 4),(.readerAny true 8),(.readerLive true 8 2),(.readerLive true 8 3),(.readerLive true 8 4),(.readerAny true 11),(.readerLive true 11 2),(.readerLive true 11 3),(.readerLive true 11 4),(.readerAny true 12),(.readerLive true 12 2),(.readerLive true 12 3),(.readerLive true 12 4),(.readerAny true 18),(.readerLive true 18 2),(.readerLive true 18 3),(.readerLive true 18 4),(.eqLab false 4 6 1 true),(.gateEq true 4 6 0),(.gateEq true 4 6 1),(.eqLab false 4 12 4 false),(.gateEq true 4 12 0),(.gateEq true 4 12 1),(.eqLab false 6 12 4 false),(.gateEq true 6 12 0),(.gateEq true 6 12 1),(.eqLab false 8 11 4 false),(.gateEq true 8 11 0),(.gateEq true 8 11 1),(.eqLab false 8 18 3 true),(.gateEq true 8 18 0),(.gateEq true 8 18 1),(.eqLab false 11 18 4 true),(.gateEq true 11 18 0),(.gateEq true 11 18 1)]

def table111_0 : List Nat := [0x641,0x741,0x1a0702,0x8c1,0x1e0882,0x200882,0x941,0xa41,0x260a02,0xac1,0xb41,0xbc1,0xc41,0xcc1,0xe41,0x340e02]
def table111_1 : List Nat := [0x360e02,0x3b1282,0x4b1502,0x11782,0x31782,0x51782,0x1c46f1b46b1a45,0x3c1a02,0x401a02,0x4c1a82,0x4e1a82,0x561b02,0x581b02,0x551b82,0x601b82,0x621b82]
def table111_2 : List Nat := [0x5f1c02,0x1ec791dc751cc5,0x421c82,0x4e1d02,0x501d02,0x581d82,0x5a1d82,0x641e02,0x5f1e82,0x214832047f1f45,0x461f02,0x4c1f82,0x4b2002,0x552082,0x5f2102,0x23c8d22c8921c5]
def table111_3 : List Nat := [0x402182,0x462182,0x4e2202,0x522202,0x4b2282,0x582282,0x5c2282,0x552302,0x622302,0x662302,0x5f2382,0x26497254932445,0x422402,0x462402,0x502482,0x5a2502]
def table111_4 : List Nat := [0x5c2502,0x552582,0x642582,0x662582,0x5f2602,0x28ca127c9d26c5,0x422682,0x4f2702,0x502702,0x592782,0x5a2782,0x642802,0x5f2882,0x2b4ab2a4a72945,0x3c2902,0x412902]
def table111_5 : List Nat := [0x462902,0x4c2982,0x4f2982,0x522982,0x4b2a02,0x562a02,0x592a02,0x5c2a02,0x552a82,0x602a82,0x632a82,0x662a82,0x5f2b02,0x2dcb52ccb12bc5,0x3c2b82,0x422b82]
def table111_6 : List Nat := [0x522c02,0x562c82,0x5a2c82,0x552d02,0x5f2d82,0x304bf2f4bb2e45,0x472e02,0x532e82,0x4b2f02,0x552f82,0x5f3002,0x32cc931cc530c5,0x3c3082,0x473082,0x3b3102,0x4c3102]
def table111_7 : List Nat := [0x533102,0x4b3182,0x563182,0x5d3182,0x553202,0x603202,0x5f3282,0x354d3344cf3345,0x473302,0x503382,0x5a3402,0x643482,0x5f3502,0x37cdd36cd935c5,0x423582,0x473582]
def table111_8 : List Nat := [0x503602,0x533602,0x563682,0x5a3682,0x5d3682,0x553702,0x673702,0x5f3782,0x3a4e7394e33845,0x3d3802,0x463802,0x4d3882,0x523882,0x4b3902,0x573902,0x553982]
def table111_9 : List Nat := [0x613982,0x5f3a02,0x13a82,0x63a82,0x33b02,0x83b02,0x53b82,0xa3b82,0xfc1,0x3bced3ac4d0f43a0f87,0x3bced3ac570f44a0f87,0x3bced3ac610f4540f87,0x3bced3ac571344a0f87,0x3bced3ac61134540f87,0x3bced3ac6115c540f87,0x13c02]
def table111_10 : List Nat := [0xc3c02,0x33c82,0xe3c82,0x53d02,0x103d02,0x1141,0x3d4f33c45110c3a1107,0x3d4f33c45b10c4a1107,0x3d4f33c46510c541107,0x3d4f33c45b1444a1107,0x3d4f33c465144541107,0x3d4f33c46516c541107,0x13d82,0x123d82,0x33e02,0x143e02]
def table111_11 : List Nat := [0x53e82,0x163e82,0x1241,0x3ecf93dc5311c3a1207,0x3ecf93dc5d11c4a1207,0x3ecf93dc6711c541207,0x3ecf93dc5d14c4a1207,0x3ecf93dc6714c541207,0x3ecf93dc67174541207,0xfd4202,0x1094482,0x1134702,0x74702,0x94702,0xb4702,0x4c52f4b52b4a45]
def table111_12 : List Nat := [0xfe4a02,0x1004a02,0x10a4a82,0x10c4a82,0x1164b02,0x1134b82,0x11e4b82,0x1204b82,0x11d4c02,0x1244c02,0x1264c02,0x4ed394dd354cc5,0xfe4c82,0x1024c82,0x10a4d02,0x10e4d02]
def table111_13 : List Nat := [0x1094d82,0x1144d82,0x1184d82,0x1134e02,0x11e4e02,0x1224e02,0x11d4e82,0x515435053f4f45,0x1004f02,0x10c4f82,0x1104f82,0x1095002,0x11a5002,0x1135082,0x1205082,0x11d5102]
def table111_14 : List Nat := [0x53d4d52d4951c5,0x1025182,0x10e5202,0x1145282,0x1225302,0x11d5382,0x56557555535445,0xff5402,0x1005402,0x10b5482,0x10c5482,0x1165502,0x1135582,0x11f5582,0x1205582,0x11d5602]
def table111_15 : List Nat := [0x1255602,0x1265602,0x58d6157d5d56c5,0xff5682,0x1025682,0x10b5702,0x10e5702,0x1095782,0x1155782,0x1185782,0x1135802,0x11f5802,0x1225802,0x11d5882,0x5b56b5a5675945,0x1005902]
def table111_16 : List Nat := [0x10c5982,0x1115982,0x1095a02,0x11b5a02,0x1135a82,0x1205a82,0x11d5b02,0x1265b02,0x5dd755cd715bc5,0xfe5b82,0x1005b82,0x10a5c02,0x10c5c02,0x10e5c02,0x1095c82,0x1145c82]
def table111_17 : List Nat := [0x1165c82,0x1185c82,0x11a5c82,0x1135d02,0x11e5d02,0x1205d02,0x1225d02,0x11d5d82,0x1265d82,0x6057f5f57b5e45,0x1015e02,0x10d5e82,0x1175f02,0x1135f82,0x11d6002,0x62d8961d8560c5]
def table111_18 : List Nat := [0xfe6082,0x1036082,0x10f6102,0x1096182,0x1136202,0x11d6282,0x655936458f6345,0x1016302,0x10d6382,0x1096402,0x1136482,0x11d6502,0x67d9d66d9965c5,0x1016582,0x10f6602,0x1176682]
def table111_19 : List Nat := [0x1136702,0x11d6782,0x76802,0x6802,0x96882,0x26882,0xb6902,0x46902,0x695a36850d404fc0f87,0x695a368517405080f87,0x695a368521405120f87,0x695a3685274051c0f87,0x695a368517435080f87,0x695a368521435120f87,0x695a3685274351c0f87,0x695a36852145d120f87]
def table111_20 : List Nat := [0x695a36852745d1c0f87,0x695a3685274851c0f87,0x76982,0xc6982,0x96a02,0xe6a02,0xb6a82,0x106a82,0x4141,0x6ada969d0f40cfc4107,0x6ada969d1940d084107,0x6ada969d2340d124107,0x6ada969d1943d084107,0x6ada969d2343d124107,0x6ada969d23465124107,0x41c1]
def table111_21 : List Nat := [0x1ad6e02,0x1b97082,0x1103c0d6e04,0xd7302,0xf7302,0x117302,0x77ddd76dd975c5,0x1b07582,0x1b27582,0x1bc7602,0x1be7602,0x1c67682,0x1c87682,0x1c37702,0x1d07702,0x1d27702]
def table111_22 : List Nat := [0x1cd7782,0x7a5e7795e37845,0x1b47802,0x1ba7882,0x1c07882,0x1c47902,0x1ca7902,0x1c37982,0x1d47982,0x1cd7a02,0x7cdf17bded7ac5,0x1b07a82,0x1b37a82,0x1bc7b02,0x1bf7b02,0x1c67b82]
def table111_23 : List Nat := [0x1c97b82,0x1c37c02,0x1d07c02,0x1d37c02,0x1cd7c82,0x7f5fb7e5f77d45,0x1af7d02,0x1b47d02,0x1bb7d82,0x1c07d82,0x1c57e02,0x1ca7e02,0x1c37e82,0x1cf7e82,0x1d47e82,0x1cd7f02]
def table111_24 : List Nat := [0x81e0580e017fc5,0x1ae7f82,0x1b47f82,0x1c08002,0x1ca8082,0x1c38102,0x1ce8102,0x1d48102,0x1cd8182,0xd8202,0x8202,0xf8282,0x28282,0x118302,0x48302,0x8360b825bd6c5ac1107]
def table111_25 : List Nat := [0x8360b825c76c5b81107,0x8360b825d16c5c21107,0x8360b825c76f5b81107,0x8360b825d16f5c21107,0x8360b825d171dc21107,0xd8382,0x128382,0x6dc120303,0xf8402,0x148402,0x6dc140383,0x118482,0x168482,0x6dc160403,0x84e1183dc16d5ac6d87,0x84e1183dcb6d5b86d87]
def table111_26 : List Nat := [0x84e1183dd56d5c26d87,0x84e1183dcb705b86d87,0x84e1183dd5705c26d87,0x84e1183dd572dc26d87,0x2158682,0x21b8802,0x138982,0x158982,0x178982,0x8d6338c62f8b45,0x2168b02,0x2188b02,0x21c8b82,0x21e8b82,0x2228c02,0x2248c02]
def table111_27 : List Nat := [0x2218c82,0x2288c82,0x22a8c82,0x2278d02,0x8fe3d8ee398dc5,0x2168d82,0x2198d82,0x21c8e02,0x21f8e02,0x2228e82,0x2258e82,0x2218f02,0x2288f02,0x22b8f02,0x2278f82,0x92647916439045]
def table111_28 : List Nat := [0x2179002,0x2189002,0x21e9082,0x2239102,0x2249102,0x2219182,0x22a9182,0x2279202,0x94e5193e4d92c5,0x2189282,0x21d9302,0x21e9302,0x2249382,0x2219402,0x2299402,0x22a9402]
def table111_29 : List Nat := [0x2279482,0x139502,0x9502,0x159582,0x29582,0x179602,0x49602,0x966579561d85e141207,0x966579562385e1a1207,0x966579562985e201207,0x96657956238761a1207,0x9665795629876201207,0x966579562988e201207,0x139682,0x69682,0x159702]
def table111_30 : List Nat := [0x89702,0x179782,0xa9782,0x97e5d96e1f866144187,0x97e5d96e258661a4187,0x97e5d96e2b866204187,0x97e5d96e2587e1a4187,0x97e5d96e2b87e204187,0x97e5d96e2b896204187,0x9841,0x98c189803,0x9901b9803,0x99c1,0x9a01f9983,0x9a8219983,0x9b41]
def table111_31 : List Nat := [0x9bc249b03,0x9c0279b03,0x9ee799de759cc5,0x9f42a9c83,0x9f42c9d03,0x9f42e9d83,0x9f4309e03,0x9f4329e83,0xa1e85a0e819fc5,0xa242a9f83,0xa242ca003,0xa242ea083,0xa2430a103,0xa2432a183,0xa2c1,0xa3035a283]
def table111_32 : List Nat := [0xa3837a283,0xa6697a5693a445,0x21ba502,0x221a582,0x227a602,0xa8ea1a7e9da6c5,0x21ba782,0x221a802,0x227a882,0xab6abaa6a7a945,0x1b9aa02,0x1c3aa82,0x1cdab02,0xadeb5aceb1abc5,0x1b9ac82,0x1c3ad02]
def table111_33 : List Nat := [0x1cdad82,0xb06bfaf6bbae45,0x21baf02,0x221af82,0x227b002,0xb2ec9b1ec5b0c5,0x1b9b182,0x1c3b202,0x1cdb282,0x9a662b303,0xb369aa403,0xb369ca483,0xa2265b383,0xb3eb8a403,0xb3ebaa483,0xa226bb403]
def table111_34 : List Nat := [0xb46b8a683,0xb46baa703,0x9f271b483,0xb4eaea903,0xb4eb0a983,0xa366eb503,0xb56c2a903,0xb56c4a983,0xa3e7cb583,0xb5ec2ab83,0xb5ec4ac03,0x681,0x781,0x801,0x981,0xd01]
def table111_35 : List Nat := [0xd81,0xef3b4eb1343d0e86,0xef3b4eb15c3d1286,0xef3b4eb1843d1506,0xef3b4eb15c4d1286,0xef3b4eb1844d1506,0xef3b4eb184571506,0xf53ccf1144430e86,0xf53ccf116c431286,0xf53ccf1194431506,0xf53ccf116c511286,0xf53ccf1194511506,0xf53ccf11945b1506,0xfb3e4f714c470e86,0xfb3e4f7174471286,0xfb3e4f719c471506]
def table111_36 : List Nat := [0xfb3e4f7174531286,0xfb3e4f719c531506,0xfb3e4f719c5d1506,0x1a568da1435013f06,0x1a568da145d014206,0x1a568da1485014486,0x1a568da149d014706,0x1a568da145d0d4206,0x1a568da14850d4486,0x1a568da149d0d4706,0x1a568da1485174486,0x1a568da149d174706,0x1a568da149d214706,0x1ab6a5a743d033f06,0x1ab6a5a7465034206,0x1ab6a5a748d034486]
def table111_37 : List Nat := [0x1ab6a5a74650f4206,0x1ab6a5a748d0f4486,0x1ab6a5a748d194486,0x20d82e096f5b16b06,0x20d82e0971db16e06,0x20d82e09745b17086,0x20d82e0971dbd6e06,0x20d82e09745bd7086,0x20d82e09745c77086,0x25995e55876178506,0x25995e5588e178686,0x25995e558a6178806,0x25995e5588e1d8686,0x25995e558a61d8806,0x25995e558a6238806,0x25f9765b87e198506]
def table111_38 : List Nat := [0x25f9765b896198686,0x25f9765b8ae198806,0x25f9765b8961f8686,0x25f9765b8ae1f8806,0x25f9765b8ae258806,0x98c1,0x9901,0x9a01,0x9a81,0x9bc1,0x9c01,0x27d9c82,0x27d9d02,0x27d9d82,0x27d9e02,0x27d9e82]
def table111_39 : List Nat := [0x2899f82,0x289a002,0x289a082,0x289a102,0x289a182,0xa301,0xa381,0xb301,0x29aa402,0x29ca482,0x288b382,0x288b402,0x27cb482,0xb501,0x2c2a902,0x2c4a982]
def table111_40 : List Nat := [0x27cb582,0x9f41,0xb481,0xb581,0xa241,0xb381,0xb401,0x2da368512459714007,0xb68da1449164046,0x2da3685124585,0xb68da14484,0x11d44d0c4004,0x2da3685174305,0xb68da145c4,0x11d4bd574b5554006,0xb68da14344]
def table111_41 : List Nat := [0x2da36843,0x11d4311644c4,0x1cc4ed084e5355786,0x1cc4751256d394386,0x1cc4751243c4,0x7313b449355685,0x7311d4483,0x1cc475355684,0x7311d4383,0x7310f5783,0x7311d4203,0x1cc4742,0x11c1c4e62904,0x11c1c4e62984,0x4705f3983,0x470572a83]
def table111_42 : List Nat := [0x11c17c572904,0x11c17ca915c4,0x11c17c4d0f44,0x11c17c6d2984,0x11c17c6d2904,0x11c179755cd7145c6,0x4705e4ad2d5605,0x4705e4ad2d4345,0x4705e4ad2d5585,0x4705e5d5734285,0x4705e54d164045,0x4485e5d57354d555456f4989,0x4705e5d5734585,0x7305e43c3,0x11c1797145c4,0x1cc1782]
def table111_43 : List Nat := [0x17ca71ac3c1585,0x1cc29c6b0f04,0x7303d15c3,0x730a70f43,0x4704d2a83,0x1cc29c2,0x17d1c2983,0x7301,0x7781,0x7a01,0x7c81,0x7f01,0x8181,0xab01,0xad81,0xb281]
def table111_44 : List Nat := [0x5dda1179735bd215487,0x11d6845e459004846,0x475a1179164005,0x11d6845e459203f86,0x655a1179014345,0x11d6845e4584,0x11d6845e4044,0x11d6845e44c4,0x475a11783,0x475a145d00449a36947,0x25f9763596e209406,0x25595e3f882598b06,0x25595e3f882598b86,0x25595e3f882598c06,0x9565789e209645,0x581203db86dc5]
def table111_45 : List Nat := [0x21383e11709b68106,0x21383e11709b67546,0x751b47283,0x83e13845d46e1b66d07,0x20f84e11751b86d86,0x70a098360b7c05,0x1b88260d82df17586,0x1b88260d82df17606,0x1b88360982df17686,0x1c28360982c4,0x33dcfb2a04,0x17ca922c521185,0x33dcfb22c541486,0x33dcfb0e88b1506,0x3e4533ecf72a85,0xca922c53118fb3dc7]
def table111_46 : List Nat := [0x1636a5a76ad125d06,0x1636a5a76ad125c86,0x11d6a5a76ad6f4486,0x2278861bae84,0x89e2186c3,0xf6966578b04,0xf6966578b84,0x3da5995c3,0x83e13845b67085,0x20f84e116d9b86d46,0x70db47283,0x83e13845b66e05,0xaaeb5aa6b3b105,0x21383e116d84,0xe83e130504,0x3aca61c4ed1506d3bc7]
def table111_47 : List Nat := [0x6e41,0x25b9265d97e1a8c06,0x25b8d65d97e1a8c6338948,0x25b8d6499765f8c63391620878a,0x25b8d64994e5d97e1a8ce45880a,0x751ecf3150773c4f516c8,0x5f1905a1084,0x17cf30e8f53c4641687,0x5f3cc543d4f11906,0x17cf3150f53c45,0x96e5d97e198c85,0x22786c2,0x25b976278861997c6,0xb69da96250f5686,0x2da76a5135c05,0xb69da944d6e43c6]
def table111_48 : List Nat := [0x2da76a5135b85,0xb69da944c4,0x2da76a50e4645,0xb69da94384,0x2da76a43,0x1617cf3844540406,0x580f0483,0xfb2b4f92acf72a44a1748,0xfb17c033dc8b1186,0xfb17c03154f71286,0x3ec5f00c553dc5,0x82e0d8243,0xfb17c0303cf50446,0x17c5522ca91485,0x264c132cdf3cc973d4bf324dd3c44714cd,0x5f3cc973d4553c48b11c8]
def table111_49 : List Nat := [0x17cf325cf5154f122c7,0x99304cb37cf325cf52fcc9374f1128db14ce,0x1617c0303c973d46,0xfb17c033dc4,0x25e01c2,0x585f25c0303c5,0x3accb324ed3bc8a2907,0xeb17c553b4ef2286,0xeb17c553b4ef0e8c52988,0x3ac5f154ed3bc3a2a47,0xeb1c46f3b4ef2a06,0x25e17c5500c4,0x17c550ec3,0x17c5512c3,0x25e17c55014462a46,0x9785f154052a05]
def table111_50 : List Nat := [0x25e17c550144,0x5f154f111cf53cc6,0x257966558fe1a8f6398b08,0x257966558d63f86a338f6318e4a,0x95e59956358fe1a8ce3d8c49,0x259956358fe1a8ce578f48,0x9785f1543,0x956359663395e1a8fc7,0x168982,0x22795e599544,0x25e17e579644,0xeb1c4543bced2986,0x3acad150ef3b4a71347,0x3ac5f150ef3b4c31587,0x3ac712b4543bced15c7,0x3ac5f150ef3b45]
def table111_51 : List Nat := [0x9785f0143,0x25e17c2,0x9781,0x20d1782,0x5f3b4ef3ac4,0x1a969d3b58dab4495b43c8,0x1a969d3b58dab4495b4608,0x6a51d69dab4485,0x1a969d3b6ad39465335788,0x6a5a74ed636ad39585194089,0x1a969d3b58d8b6ad3958589464a,0x6a5a762dab6250343c7,0x11d4e5614dd5f4386,0x1a9475a76ac4,0x22796e5d8cc4,0x89e5b9743]
def table111_52 : List Nat := [0x695a1475a344d0845c7,0x1a56851d68d134206,0x11d4e5614dd5f4086,0x695a1475a344c5,0x1a56855968d1254d554348,0x695a14c55968d1254d294589,0x695a1475a345c5,0x1a568531565a3449164048,0x1a56851d68c4,0x2599540e84e5d89c6,0x8981,0x125d0003,0x40202,0x40302,257,0x1781]
def table111_53 : List Nat := [0x3b81,0x3d01,0x3e81,0x2381,0x2601,0x2b01,0x3001,0x3281,0x3781,0xf93dca91544,0x3e4f71508b2985,0xf93dca92ac4,0x3dcf92a43,0xf73e42,0x2590182,0x2590202]
def table111_54 : List Nat := [0x1ab9642,0x166a02,0x1ab01c2,0x401,0x8301,0x8481,0x3c4553cc3,0xf13cc2,0x8201,0x82c1,961,129,0x3c81,0x3dc1,0x3c41,0x481]
def table111_55 : List Nat := [769,0x9681,0x8381,0x9741,0x501]

def encoded111 (i : Nat) : Nat :=
  if i < 448 then
    if i < 224 then
      if i < 112 then
        if i < 48 then
          if i < 16 then
            table111_0.getD (i%16) 0
          else
            if i < 32 then
              table111_1.getD (i%16) 0
            else
              table111_2.getD (i%16) 0
        else
          if i < 80 then
            if i < 64 then
              table111_3.getD (i%16) 0
            else
              table111_4.getD (i%16) 0
          else
            if i < 96 then
              table111_5.getD (i%16) 0
            else
              table111_6.getD (i%16) 0
      else
        if i < 160 then
          if i < 128 then
            table111_7.getD (i%16) 0
          else
            if i < 144 then
              table111_8.getD (i%16) 0
            else
              table111_9.getD (i%16) 0
        else
          if i < 192 then
            if i < 176 then
              table111_10.getD (i%16) 0
            else
              table111_11.getD (i%16) 0
          else
            if i < 208 then
              table111_12.getD (i%16) 0
            else
              table111_13.getD (i%16) 0
    else
      if i < 336 then
        if i < 272 then
          if i < 240 then
            table111_14.getD (i%16) 0
          else
            if i < 256 then
              table111_15.getD (i%16) 0
            else
              table111_16.getD (i%16) 0
        else
          if i < 304 then
            if i < 288 then
              table111_17.getD (i%16) 0
            else
              table111_18.getD (i%16) 0
          else
            if i < 320 then
              table111_19.getD (i%16) 0
            else
              table111_20.getD (i%16) 0
      else
        if i < 384 then
          if i < 352 then
            table111_21.getD (i%16) 0
          else
            if i < 368 then
              table111_22.getD (i%16) 0
            else
              table111_23.getD (i%16) 0
        else
          if i < 416 then
            if i < 400 then
              table111_24.getD (i%16) 0
            else
              table111_25.getD (i%16) 0
          else
            if i < 432 then
              table111_26.getD (i%16) 0
            else
              table111_27.getD (i%16) 0
  else
    if i < 672 then
      if i < 560 then
        if i < 496 then
          if i < 464 then
            table111_28.getD (i%16) 0
          else
            if i < 480 then
              table111_29.getD (i%16) 0
            else
              table111_30.getD (i%16) 0
        else
          if i < 528 then
            if i < 512 then
              table111_31.getD (i%16) 0
            else
              table111_32.getD (i%16) 0
          else
            if i < 544 then
              table111_33.getD (i%16) 0
            else
              table111_34.getD (i%16) 0
      else
        if i < 608 then
          if i < 576 then
            table111_35.getD (i%16) 0
          else
            if i < 592 then
              table111_36.getD (i%16) 0
            else
              table111_37.getD (i%16) 0
        else
          if i < 640 then
            if i < 624 then
              table111_38.getD (i%16) 0
            else
              table111_39.getD (i%16) 0
          else
            if i < 656 then
              table111_40.getD (i%16) 0
            else
              table111_41.getD (i%16) 0
    else
      if i < 784 then
        if i < 720 then
          if i < 688 then
            table111_42.getD (i%16) 0
          else
            if i < 704 then
              table111_43.getD (i%16) 0
            else
              table111_44.getD (i%16) 0
        else
          if i < 752 then
            if i < 736 then
              table111_45.getD (i%16) 0
            else
              table111_46.getD (i%16) 0
          else
            if i < 768 then
              table111_47.getD (i%16) 0
            else
              table111_48.getD (i%16) 0
      else
        if i < 832 then
          if i < 800 then
            table111_49.getD (i%16) 0
          else
            if i < 816 then
              table111_50.getD (i%16) 0
            else
              table111_51.getD (i%16) 0
        else
          if i < 864 then
            if i < 848 then
              table111_52.getD (i%16) 0
            else
              table111_53.getD (i%16) 0
          else
            if i < 880 then
              table111_54.getD (i%16) 0
            else
              table111_55.getD (i%16) 0
def book111 (i : Nat) : Clause := let n := encoded111 i; unpackLits 10 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses111 : inputsOK 3 111 a111 r111 (baseBook book111 555).toList=true := by decide +kernel

def rows111_0 : List Nat := [0x80401,0x180801,0x180a01,0x381001,0x701e01,0x702001,0x4c13201,0x4c13401,0x4c13601,0x4c13801,0x4c13a01,0x4c13c01,0x5294c01,0x5294e01,0x5295001,0x5295201,0x5295401,0x5295601,0x5916601,0x5916801,0x5916a01,0x5916c01,0x5916e01,0x5917001]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk111_0 : checkRows book111 10 555 rows111_0=true := by decide +kernel

def rows111_1 : List Nat := [0x4c27001,0x4c27201,0x4c27401,0x4c27601,0x4c27801,0x4c27a01,0x4c27c01,0x4c27e01,0x4c28001,0x4c28201,0xa429201,0xa429401,0xa429601,0xa429801,0xa429a01,0xa429c01,0x52b1e01,0x52b2001,0x52b2201,0x52b2401,0x52b2601,0x52b2801,0x593ae01,0x593b001]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk111_1 : checkRows book111 10 579 rows111_1=true := by decide +kernel

def rows111_2 : List Nat := [0x593b201,0x593b401,0x593b601,0x593b801,0xa7bc601,0xa7bc801,0xa7bca01,0xa7bcc01,0xa7bce01,0xa7bd001,0xf4bd402,0x456f4bd602,0x458f63da02,0x45af63dc02,0xcf7be002,0x45cf7be202,0x4be601,0x53e801,0x5bea01,0x63ec01,0x6bee01,0x4bf201,0x53f401,0x5bf601]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk111_2 : checkRows book111 10 603 rows111_2=true := by decide +kernel

def rows111_3 : List Nat := [0x63f801,0x6bfa01,0x45eff3fe02,0x460ff40002,0x4cf32c3202,0x13bc3401,0x13bc3601,0x13343801,0x13443e01,0x13544401,0x4eb34c4a02,0x13ec4c01,0x13ec4e01,0x13b45001,0x137cdd36cd935be405,0x140cf801,0x140d0001,0x13a4e7394e3383f005,0x1424f401,0x1424f601,0x1cd241da8aa28842147426c77a2e5f1d6881d40e,0x601cc5f9dc639d461c8b21a6c641de5f1725d188759ce11,0x1cd241d286217439d1441d69b1de5f1dc0c,0x1b87f1ae7f9b0801b2829bd2248f255125d26c6fa0c5f20612]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk111_3 : checkRows book111 10 627 rows111_3=true := by decide +kernel

def rows111_4 : List Nat := [0x6e1fc6b9fe6c1be831ba821b2802060b,0x1e4849ec8425c871ee9648896d168626c7ea2e9897c7d22698514979e616,0x1b47f1ae7f9b08d2046da3323a37462389b1be8323c5f1ba8223b4520216,0x611cc5f9d060990779d207,0x172934869426c95a5493d1c75989469d862d145f25210,0x601cc5f9d461d1e75989469d862d14641de5f1ce0f,0x601cc5f9d8629907798675188759ce0b,0x65c9c689f27c286a9a8aaa28eaa99a0b,0x19a6949f291f8795247b19ea1aa6a2aa8a3aaa6b1fa5d19612,0x1ea659e47a19a7e1aa7c9a526ca328286a9a8aaa28eaa9ac7e9725d19c16,0x1aa6949f271987a1e6a1aa6a2aa8a3aaa5d1960e,0x1f27dca46a9a949d2a7b19f4a286a9a8aaa28eaa9ac7e9e412,0x691a0659987a1e6a1aa6a2aa8a3aaa6b1a74b49c0f,0x1ee7952e7b19e6b1fa699f54b5240a,0x1f27ba86a9a8aaa28eaaca008,0x19c791967a19a6949b28172a1aa6a2aa8a3aaa6b1fa699f54b5334c1ea16,0x7a9967919a79a429023e919a14d53291530921f469d2c929fa6b19c15,0x360c831194622789c499784a97a4b97c0f120088244782c12,0x2e0d83518c68290a2499784a97a4b97c0f120088244782c12,0xb8320e4651a0ac2a89b4ed382c83c09120479265e12a5e92e5f0402e02c17,0xb22c1265e12a5e92e5f46c08,0x338d2460d00911033464448a0271265e12a5e92e5f0d448d3c470ca15,0x330d2450d00911033c68458a62889b5053e471265e12a5e92e5f0b8351234f0ca19,0x891118912499784a97a4b97c48d3c4591a0d]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk111_4 : checkRows book111 10 651 rows111_4=true := by decide +kernel

def rows111_5 : List Nat := [0xf03a0b02f51034290a2499784a97a4b97c1046a0f,0xf03a0b0320c5442789c499784a97a4b97c104660f,0x23085497221745da6609a6a0a26e0aa100c,0x6098f23498649e27826609a6a0a26e0a97e0d,0x6099463c8724c905c9745da6609a6a0a26e0a97e0f,0x1826548b2618c771da5da6609a6a0a26e0a97e0e,0x8448c849d0739cd541d553d4c7598952a166126609a6a0a26e0aa3015,0x1ce5f9cc789947718e61c8d22c865c9745da6609a6a0a26e0a9887598016,0x218772107323078a6609a6a0a26e0ac900c,0x1cc619dd24c9955a1474554759885da6609a6a0a26e0a9d354d4c14,0x54b23d5888a2d284a2a1aa6a2aa8a3aaa5d1774da6609a6a0a26e0aa1816,0x2247f54a839fe8aa0a8049722495239745da6609a6a0a26e0aa0614,0x751d078c9122c9876a2a8a558881d75721b56a6e9aa660a828099774d9cc17,0xf89a0b0aa0d8402e02e270b409,0xf03a0b0382b5435802e499784a97a4b97d4d84157c6c11,0x465509265e12a5e92e5f537578a80a,0xb22c09b520aa0dd64499784a97a4b97d4d8b957c6610,0xb22c1265e12a5e92e5f46a08,0x2a8a826d680cd6227566499784a97a4b97d4d8b957c6811,0x5420e037518ac04,0x15ad5f4dd6c03,0x15bac001,0x15bad201,0x15bae801]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk111_5 : checkRows book111 10 675 rows111_5=true := by decide +kernel

def rows111_6 : List Nat := [0x15bafe01,0x15bb1001,0x15bc1801,0x15bc2001,0x15bc3001,0x84490859d474a6a0a26e0aa2609,0x18663490769d873580641de8ba6a0a26e0a98875a20609d08517e14,0x7718f6098875d1c05,0x922465d17291486869868417e90212601908ba4a9a8289b82a622216118e8aa3e19,0x952525d17321a509a8289b82a93a4c0b,0x735867748b489d562584759de95a6a0a26e0a9ce0f,0x1ec79a5c84a5884260899f48621c7b97562488969fa8ba5698a6a0a26e0aa5f629e41a,0x6d1fc6ba046dc8f45a086e9be8326a0a26e0ad8a6c1ff6320213,0x6e1fc6ba006ca0a6f48f25175639fe6c58d62a6e9a82a0a1be8320615,0x1b87f1ae801b2829bd23c946fa0c6c1fe5d2060e,0xd7b5ad5cc931cc2d8b9ee735209,0xde372dbb6d2dcb52cb56d5348d2b680b,0xdab78dcb712ccbb2e35ad6348d2b680b,0x36edab78dd4b92d4bcd7b5cd2b680a,0xdcb6edab7b2f4bb2db64d8b5366d9965b66df3680f,0x33acbaa402,0x2f6bcaeed1b44d02fac3b0d5daea0a,0x308c1b04d1b44d05a15e30008,0xb1aeab0af6b32d0bf2c4bbd775caf00b]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk111_6 : checkRows book111 10 699 rows111_6=true := by decide +kernel

def rows111_7 : List Nat := [0xb2aeab0af2b2343692eeb12d0bf5775caf40d,0xbb300bab08bdb06bcb3ecf5a6bf30ea85795db020f,0x2b6acaaeafcb12bcaab9ae55c2ac0a,0xb7adab64a929ab0abaa15d2d409,0xb5adeb74a72b2b4acaa15d2d409,0x2dab5ae12b4a8ae2b75d2d408,0xb7adab5cb12bcaaaf2ad6c5af6b5aaa8d755c2d40f,0x721b85e198632006b1f0ae2b0a8570740a4840e,0x1c09a178a0188742e066298b409,0x602685e2d8731fdb629866570742e0296d09e0e,0x1909a178a0188b61cc7b20db8570742e0296d0a40f,0xb62c48202,0x1c86e178642909b6f15c1d0b80a062284820d,0x7c9ec7a4a528c9e7da2c8a1e409,0x1e87e1ed274a5281f088a1e5d1e40a,0x1f27e1e9284a3269ea86a16845c3701725d1fa8b9e410,0x40b00c430f4090440703c050350d42cf00c,0x102c031043b08dc70940d014090442901c0f09d0d42cf211,0x36edccb32d36cd5b54df376d25c9673a45634c56b6810,0x372dab712e4b2d6b58df376d25c9673a45634c56b6810,0x36edab752e4b4d7b5cd4dcd72dc8ddb61673a456366df34c56b6814,0x5a8a8da202,0xbb300bab08bdb06bcb3ecf2f8c2dd0a85795db020f,0xb1aeab0af6b32cebe2c4bbd775caf00b]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk111_7 : checkRows book111 10 723 rows111_7=true := by decide +kernel

def rows111_8 : List Nat := [0xb2aeab0af2b2343752eeb15d2b3af9745775caf40f,0x41b04c553fd055f57b41c4608,0x106c1314cfd0add90b41d055d70bc1f05dd15fd075ed7d4144813,0x334ccdda02,0xf02f1ac6228834290220902c09,0x41b04c533f42b7642f07c170b41d052a34157d5ed075fc4812,0x38ce2b7ee1383314c0e1b5ed74c80a,0x35ad5cc53035204,0x37f30b80d5b54d4b84d6b8c08,0x358e4352e4b572fde765348e65e578b940c,0x1104f1c4780904205,0x1188a1088c110502604e2584c2508e0b,0x1e8ee1d8f21f46f7b0f41f8883e0843d8f00d,0x4a22dea23090124711d5ee2585026022090920e,0x4190c218764007c3f0781fc771cc797c088438fa0f,0x364d84c202,0xd2dc801,0xd537ed4b88e135b304bf78b66e3b497db60e2b800f,0x1728fc9a901e879a8c9297c912460a,0x1f27b9e57e9ea86a16a31fa5f1f4924a00c,0x669a526ca05ca526724c74a507352275a5e9625ca31ac77a569897c699d89526073a1293a5a851961f,0x197271a27c9f07b9e47b19f7f9e684a8c6b1fa5f1a67d19a12,0x7a1ed274a07c22287a1c846017f2267d28c7ea2e5f1e411,0x7c1967919a7e1ab274a46b1fa5d1e684dc580a8c5f19e7b1a213]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk111_8 : checkRows book111 10 747 rows111_8=true := by decide +kernel

def rows111_9 : List Nat := [0x65c9e6a1f87d9e47c9a5811ec679ac7e9e684dc580a8c5f19a13,0x1ea659e4669f2691f86ac9b284a3819e6849737117580a8c6b1fa5f19c16,0x505d77cb3a523397832a07,0x167b2cce331785da05,0xa029c7d2009a04,0x5b76d5be02,0x602685e298671ee101b60e088742e15c1b8b16d09e10,0x1809a178a6198ce328cd840d01a6136d0742e0d41b8b03489e13,0x5b16bdacb8abb6cde15c2ac08,0x314566157c940a931a50b17786160a,0x1809a178a6198742e06e2c09e09,0x1e07d1c47420106398d03e8d632902380ce330da3f87611,0xbb1d0bc401123e9104211c2b8aa2a61a460c1870fe220c8350ec43922318d23a10a478c41c,0x1f87d1c46e3f0fa420222b8a826902290661905e2807a18e1e1d0882e10e1b8b0428761b,0x7e1f4711b8fc1e8fb87102088760a,0x2ec6e30900470fa440fe448a02709a460c029e22420ac0886c1a86988140ca91e428e8348c62c5d782b3b86162ce0882e0c8350ec4392250b31780be2f,0x60f2106d6e822096156d0b8570b60a,0x62582948c6e16c515989b30c5a8b821429ad216428499162f097cf108216,0x14785e24c5b145662658b1c08,0x378db188a0270221a0e61b0d609,0xd82e0d469188a42889b8b0ac0886a1a0402e0ec0e8b03a02c13,0xe20d8d60b0d80b835188a4288403b03a3a4680e,0xe4340d6328da330a02709b8c0e033e1a2e0d43b0b0348e98bc6414,0x320b8391a4642b0aa2a02c08]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk111_9 : checkRows book111 10 771 rows111_9=true := by decide +kernel

def rows111_10 : List Nat := [0x1909a178a0188cc328d0088cf8ce1b8d62e4b3ad73ba77732aa1e08a2e2b89928f1162ce3c249e28100742e0d40e86e208b0348a429,0x4585244054448da360d6468e2160dc0885c3b122168e84785613,0x642685e28062330ca33e1a340a81a0742e0d41b8b0348a412,0x330ce944c6e2385904cab12472864460845a88298a24a89b8cb38f09278a0882e0d43b10e488822c0d23a10a47b184fa674826b8dbc58e63a4b14628115785d632,0x176aa4caa86cc608512898812a1ae342b338f09278a0400e8824fa674826b8dbc44b1477833a1d,0x2f8c51bc74400fa420c01b61d88144cc5d6ceb1b85b2ac4a87822883f92b8f6338f9464b338f09278a088320d43b10e208c6348e842b184fa674826b8dbc58e63b780ba35,0xbe3146f1d1003e9083006d87620220c8350ec43882318d23a10b8e63a3f8ba18,0xdcb6d2d356d536805,0x372dacb92cb58d4e44d236808,0xd535b2cb70dbe46d235207,0x36edab752e4b4d7b5d9236808,0x376d859d7db7cd9ba2d360ca2e08a1b1385bacc7640ea3198dbc2f164a16,0x165d9966b7792b5205,0x18332cd3b4cce5dc05,0xd859cdf5f6d9e4e05,0xc4b1ca1947825f2a2945833a39493e99d20c626b89dcef1163943c39361617,0x469778a20903604,0xaa2c89d1a46b188220909a08,0x1198d7580e43b03237e59958402e0ea0b,0x634270b20f4651b0259589a08,0x280b236c6796d602ae5c0ce59958402e09a0d,0xceb30c694585df2cab124fa8699e0948288c626a4a929979464b3c4ce3c249e29935da1b,0xcae097728ac5e16c515989ba8e9e54eb31d983c458b38f0a8613,0x1640279897cf126605]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk111_10 : checkRows book111 10 795 rows111_10=true := by decide +kernel

def rows111_11 : List Nat := [0x318c502809e1604,0x18ce380ee5e1063405,0x671e46599a7c9a47e1ab26ca1289725d1ea0d,0x65c9e6a1f87d9e47c9a4679ed9a99a0b,0x719e4701c27e1c9274a59b1ec7166a79a13711746b1ca7e9f013,0x679a3281f07b99605,0x65ca0671ec7a9e59c1e8669a009,0x661e4659ec67a448fa467b9a1272439c9e60d,0x5ca3f26a4490a4605,0x661e4659ec679ac7e9e607,0x671e4659e866e779e1f269674921f469e6e6b1fa929ea11,0xd6390d4b92d5df8e6de8e638979366e85e37db8f9939411,0xe5b98e4cc7325957d364d867cd9ba1993900d,0x48923d1602,0x51d489d6626805c98a7648608,0x671e4659e8669ac7e9ea07,0x24490e79a12467b9a1a0a487d1a692a3e0c,0x1dc74491219725d1cc06,0x1cd229da6398c5f987a21d6621d00a,0x164975a1c8803,0x1807368a771d522c865c974759ce0a,0x84490859d474e8a85183a3a21a3686641de8ba2a0f,0x1773bae9e7f94b2c05,0xd465001]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk111_11 : checkRows book111 10 819 rows111_11=true := by decide +kernel

def rows111_12 : List Nat := [0xcde7ba4a8ac5e16e9314c73ac5e284ef67fa528e0f,0x18889a420ac1b06b880a18e90a3a0d22c08390df25233775b2ec4e16cc316a2e084be684f925a59429ae90a12645e32cef3bb9fbc04aa6e220b8350ec43e66c75e1a50a635,0xcbb2ce8e52ea128cde68a392f9ee08a1bad99b1ca2126ccbbf9fbbc996909a17ba626fa55da1d,0x622269082b06c1ae202863a428e8348b020e437c948cdddc5131785b2ac4e9aefe7e4fbbc99a65a42685ee98438ec350b822666c726fa50a62c,0x1a702a01,0x1a712c01,0x1a714601,0x1a716001,0x1a787401,0x1a788801,0x1a78b801,0x1a78d401,0x1a78ec01,0x1a790e01,0x1909a178a018c7b8686d83e3b8e0b01beaba9ea5a78a411,0x188731ec82190a629022096a7a905e0b,0x198731ec7e180a02789bad06d83822096b3a9ea5aa85e11,0x16dc851fdbc2deb7acea5a786c09,0x721b85e198632047c1a8ae2b0a9ae6a7a94840e,0x5ce57ba8ef9299fe68ef127a56a1a7eba0c,0x6279495ae93ba4967f9a3c04ae9fa9695a83a80e,0x19e979afa85af28805,0x67f833c0a2a89a53ba06,0xa1179b0babb067a05]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk111_12 : checkRows book111 10 843 rows111_12=true := by decide +kernel

def rows111_13 : List Nat := [0x28775e7acc97aef92b9fe68ef127b16c2ceb38eaec0a3de1a56a1a7b2a16,0x1b1b1a01,0x1b1b3601,0x622269082b06c1ae202863a428e8348b020e43a7eabaa6adabeb1a88a616,0x17ce9fa8ecc03,0x144cc5dacbb2ceee7eef95fae95850314c4ecba56ce10,0x6c9b461602,0x1b4b1601,0x1b4b1801,0x1b514401,0x1a969fb5e2603,0x1b66ce01,0x1b695a01,0x1b714001,0x1b7bba01,0x1b832a01,0x695b8e7e02,0x1b56cbb95dc03]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk111_13 : checkRows book111 10 867 rows111_13=true := by decide +kernel

def lastUnits111 := digits 10 2 0xdd373
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict111 : checkReasons book111 885 479 lastUnits111 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude111 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 111=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=3) h hc bp eq (by decide +kernel)
  let v := truth Z a111
  have hbase : ValidThrough v book111 555 := book_start Z h hc z eq _ _ _ _ initialClauses111
  have h0 : ValidThrough v book111 579 := rows_sound hbase rows111_0 rowsOk111_0
  have h1 : ValidThrough v book111 603 := rows_sound h0 rows111_1 rowsOk111_1
  have h2 : ValidThrough v book111 627 := rows_sound h1 rows111_2 rowsOk111_2
  have h3 : ValidThrough v book111 651 := rows_sound h2 rows111_3 rowsOk111_3
  have h4 : ValidThrough v book111 675 := rows_sound h3 rows111_4 rowsOk111_4
  have h5 : ValidThrough v book111 699 := rows_sound h4 rows111_5 rowsOk111_5
  have h6 : ValidThrough v book111 723 := rows_sound h5 rows111_6 rowsOk111_6
  have h7 : ValidThrough v book111 747 := rows_sound h6 rows111_7 rowsOk111_7
  have h8 : ValidThrough v book111 771 := rows_sound h7 rows111_8 rowsOk111_8
  have h9 : ValidThrough v book111 795 := rows_sound h8 rows111_9 rowsOk111_9
  have h10 : ValidThrough v book111 819 := rows_sound h9 rows111_10 rowsOk111_10
  have h11 : ValidThrough v book111 843 := rows_sound h10 rows111_11 rowsOk111_11
  have h12 : ValidThrough v book111 867 := rows_sound h11 rows111_12 rowsOk111_12
  have h13 : ValidThrough v book111 885 := rows_sound h12 rows111_13 rowsOk111_13
  exact book_end h13 _ _ conflict111
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
