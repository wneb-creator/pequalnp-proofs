import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a95 : Array Fact := #[(.lab 0 0 0),(.lab 0 0 5),(.avoid 0 314 0),(.res 0 8),(.res 1 8),(.res 2 8),(.res 0 9),(.res 1 9),(.res 2 9),(.res 0 10),(.res 1 10),(.res 2 10),(.res 0 11),(.res 1 11),(.res 2 11),(.lab 1 0 1),(.lab 1 0 5),(.avoid 1 245 0),(.lab 4 0 0),(.lab 4 0 5),(.avoid 4 2087 0),(.lab 5 0 5),(.lab 5 1 5),(.lab 5 2 5),(.lab 5 3 5),(.lab 5 4 5),(.lab 6 0 1),(.lab 6 0 5),(.avoid 6 314 0),(.live 8 1),(.lab 8 0 9),(.common 8 9),(.lab 8 0 10),(.common 8 10),(.lab 8 0 11),(.common 8 11),(.lab 8 0 13),(.live 8 2),(.lab 8 1 9),(.lab 8 1 10),(.lab 8 1 11),(.lab 8 1 13),(.live 8 3),(.lab 8 2 9),(.lab 8 2 10),(.lab 8 2 11),(.lab 8 2 13),(.live 8 4),(.lab 8 3 9),(.lab 8 3 10),(.lab 8 3 11),(.lab 8 4 10),(.lab 8 4 11),(.avoid 8 1548 0),(.avoid 8 1548 1),(.avoid 8 1548 2),(.avoid 8 1548 3),(.avoid 8 1548 4),(.avoid 8 7174 0),(.avoid 8 7174 1),(.avoid 8 7174 2),(.avoid 8 7174 3),(.avoid 8 7174 4),(.avoid 8 7812 0),(.avoid 8 7812 1),(.avoid 8 7812 2),(.avoid 8 7812 3),(.avoid 8 7812 4),(.avoid 8 9288 0),(.avoid 8 9288 1),(.avoid 8 9288 2),(.avoid 8 9288 3),(.avoid 8 9288 4),(.see 8 0 1290 0),(.see 8 0 1290 1),(.see 8 0 1290 2),(.see 8 0 1290 3),(.see 8 0 1290 4),(.see 8 0 7426 0),(.see 8 0 7426 1),(.see 8 0 7426 2),(.see 8 0 7426 3),(.see 8 0 7426 4),(.see 8 0 9992 0),(.see 8 0 9992 1),(.see 8 0 9992 2),(.see 8 0 9992 3),(.see 8 0 9992 4),(.see 8 2 9992 0),(.see 8 2 9992 1),(.see 8 2 9992 2),(.see 8 2 9992 3),(.see 8 2 9992 4),(.see 8 6 9992 0),(.see 8 6 9992 1),(.see 8 6 9992 2),(.see 8 6 9992 3),(.see 8 6 9992 4),(.see 8 6 16256 0),(.see 8 6 16256 1),(.see 8 6 16256 2),(.see 8 6 16256 3),(.see 8 6 16256 4),(.diff 0 8 9),(.diff 1 8 9),(.diff 2 8 9),(.diff 0 8 10),(.diff 1 8 10),(.diff 2 8 10),(.diff 0 8 11),(.diff 1 8 11),(.diff 2 8 11),(.live 9 1),(.lab 9 0 7),(.lab 9 0 8),(.common 9 10),(.lab 9 0 11),(.common 9 11),(.live 9 2),(.lab 9 1 7),(.lab 9 1 8),(.lab 9 1 11),(.live 9 3),(.lab 9 2 7),(.lab 9 2 8),(.lab 9 2 11),(.live 9 4),(.lab 9 3 7),(.lab 9 3 8),(.lab 9 3 11),(.avoid 9 432 0),(.avoid 9 432 1),(.avoid 9 432 2),(.avoid 9 432 3),(.avoid 9 432 4),(.avoid 9 2213 0),(.avoid 9 2213 1),(.avoid 9 2213 2),(.avoid 9 2213 3),(.avoid 9 2213 4),(.see 9 1 5008 0),(.see 9 1 5008 1),(.see 9 1 5008 2),(.see 9 1 5008 3),(.see 9 1 5008 4),(.see 9 1 6789 0),(.see 9 1 6789 1),(.see 9 1 6789 2),(.see 9 1 6789 3),(.see 9 1 6789 4),(.see 9 1 16256 0),(.see 9 1 16256 1),(.see 9 1 16256 2),(.see 9 1 16256 3),(.see 9 1 16256 4),(.diff 0 9 8),(.diff 1 9 8),(.diff 2 9 8),(.diff 0 9 11),(.diff 1 9 11),(.diff 2 9 11),(.live 10 1),(.lab 10 0 8),(.lab 10 0 9),(.lab 10 0 11),(.common 10 11),(.live 10 2),(.lab 10 1 8),(.lab 10 1 9),(.lab 10 1 11),(.live 10 3),(.lab 10 2 8),(.lab 10 2 9),(.lab 10 2 11),(.live 10 4),(.lab 10 3 8),(.lab 10 3 9),(.lab 10 3 11),(.avoid 10 792 0),(.avoid 10 792 1),(.avoid 10 792 2),(.avoid 10 792 3),(.avoid 10 792 4),(.avoid 10 2338 0),(.avoid 10 2338 1),(.avoid 10 2338 2),(.avoid 10 2338 3),(.avoid 10 2338 4),(.see 10 0 9992 0),(.see 10 0 9992 1),(.see 10 0 9992 2),(.see 10 0 9992 3),(.see 10 0 9992 4),(.see 10 4 7426 0),(.see 10 4 7426 1),(.see 10 4 7426 2),(.see 10 4 7426 3),(.see 10 4 7426 4),(.diff 0 10 8),(.diff 1 10 8),(.diff 2 10 8),(.diff 0 10 9),(.diff 1 10 9),(.diff 2 10 9),(.live 11 1),(.lab 11 0 8),(.lab 11 0 10),(.lab 11 0 12),(.live 11 2),(.lab 11 1 8),(.lab 11 1 10),(.lab 11 1 12),(.live 11 3),(.lab 11 2 8),(.lab 11 2 10),(.lab 11 2 12),(.live 11 4),(.lab 11 3 8),(.lab 11 3 10),(.lab 11 3 12),(.avoid 11 4370 0),(.avoid 11 4370 1),(.avoid 11 4370 2),(.avoid 11 4370 3),(.avoid 11 4370 4),(.avoid 11 5008 0),(.avoid 11 5008 1),(.avoid 11 5008 2),(.avoid 11 5008 3),(.avoid 11 5008 4),(.avoid 11 5190 0),(.avoid 11 5190 1),(.avoid 11 5190 2),(.avoid 11 5190 3),(.avoid 11 5190 4),(.see 11 3 7174 0),(.see 11 3 7174 1),(.see 11 3 7174 2),(.see 11 3 7174 3),(.see 11 3 7174 4),(.see 11 3 7426 0),(.see 11 3 7426 1),(.see 11 3 7426 2),(.see 11 3 7426 3),(.see 11 3 7426 4),(.see 11 3 16256 0),(.see 11 3 16256 1),(.see 11 3 16256 2),(.see 11 3 16256 3),(.see 11 3 16256 4),(.see 11 6 2338 0),(.see 11 6 2338 1),(.see 11 6 2338 2),(.see 11 6 2338 3),(.see 11 6 2338 4),(.diff 0 11 8),(.diff 1 11 8),(.diff 2 11 8),(.diff 0 11 10),(.diff 1 11 10),(.diff 2 11 10),(.reader false 1 0),(.es false 1 0),(.es false 1 5),(.reader false 3 0),(.es false 3 1),(.es false 3 5),(.reader false 10 0),(.es false 10 0),(.es false 10 5),(.reader false 13 0),(.reader false 13 1),(.reader false 13 2),(.reader false 13 3),(.reader false 13 4),(.es false 13 5),(.reader false 14 0),(.reader false 14 1),(.reader false 14 2),(.reader false 14 3),(.reader false 14 4),(.es false 14 5),(.reader false 17 0),(.es false 17 1),(.es false 17 5),(.reader true 1 0),(.reader true 1 1),(.reader true 1 2),(.reader true 1 3),(.reader true 1 4),(.reader true 3 0),(.reader true 3 1),(.reader true 3 2),(.reader true 3 3),(.reader true 3 4),(.reader true 10 0),(.reader true 10 1),(.reader true 10 2),(.reader true 10 3),(.reader true 10 4),(.reader true 13 0),(.reader true 13 1),(.reader true 13 2),(.reader true 13 3),(.reader true 13 4),(.reader true 14 0),(.reader true 14 1),(.reader true 14 2),(.reader true 14 3),(.reader true 14 4),(.reader true 17 0),(.reader true 17 1),(.reader true 17 2),(.reader true 17 3),(.reader true 17 4),(.gate 1 10),(.gate 1 14),(.gate 3 13),(.gate 3 17),(.gate 10 14),(.gate 13 17)]
def r95 : List Scheme := [(.self 0 0),(.exposure 0 314),(.avoidNot 0 5 314 0),(.self 1 0),(.exposure 1 245),(.avoidNot 1 5 245 0),(.exposure 4 2087),(.avoidNot 4 0 2087 0),(.avoidNot 4 5 2087 0),(.self 5 0),(.self 5 1),(.self 5 2),(.self 5 3),(.self 5 4),(.exposure 6 314),(.avoidNot 6 1 314 0),(.avoidNot 6 5 314 0),(.earlier 8 1),(.earlier 8 2),(.earlier 8 3),(.allRes 8 0),(.allRes 8 1),(.allRes 8 2),(.exposure 8 1548),(.avoidNot 8 9 1548 0),(.avoidNot 8 10 1548 0),(.avoidNot 8 9 1548 1),(.avoidNot 8 10 1548 1),(.avoidNot 8 9 1548 2),(.avoidNot 8 10 1548 2),(.avoidLive 8 1548 3),(.avoidNot 8 9 1548 3),(.avoidLive 8 1548 4),(.exposure 8 7174),(.avoidNot 8 10 7174 0),(.avoidNot 8 11 7174 0),(.avoidNot 8 10 7174 1),(.avoidNot 8 11 7174 1),(.avoidLive 8 7174 2),(.avoidNot 8 10 7174 2),(.avoidNot 8 11 7174 2),(.avoidLive 8 7174 3),(.avoidNot 8 10 7174 3),(.avoidNot 8 11 7174 3),(.avoidLive 8 7174 4),(.avoidNot 8 10 7174 4),(.avoidNot 8 11 7174 4),(.exposure 8 7812),(.avoidNot 8 9 7812 0),(.avoidNot 8 9 7812 1),(.avoidNot 8 9 7812 2),(.avoidNot 8 10 7812 3),(.avoidLive 8 7812 4),(.exposure 8 9288),(.avoidNot 8 10 9288 0),(.avoidNot 8 13 9288 0),(.avoidNot 8 10 9288 1),(.avoidNot 8 13 9288 1),(.avoidLive 8 9288 2),(.avoidNot 8 10 9288 2),(.avoidNot 8 13 9288 2),(.avoidLive 8 9288 3),(.avoidNot 8 10 9288 3),(.avoidLive 8 9288 4),(.exactAt 8 0 1290),(.seeLab 8 0 10 1290 0),(.seeLab 8 0 10 1290 1),(.seeLive 8 0 1290 2),(.seeLive 8 0 1290 3),(.seeLive 8 0 1290 4),(.exactAt 8 0 7426),(.seeLab 8 0 10 7426 0),(.seeLab 8 0 11 7426 0),(.seeLab 8 0 10 7426 1),(.seeLab 8 0 11 7426 1),(.seeLab 8 0 10 7426 2),(.seeLab 8 0 11 7426 2),(.seeLive 8 0 7426 3),(.seeLab 8 0 10 7426 3),(.seeLab 8 0 11 7426 3),(.seeLive 8 0 7426 4),(.seeLab 8 0 10 7426 4),(.seeLab 8 0 11 7426 4),(.exactAt 8 0 9992),(.seeLab 8 0 9 9992 0),(.seeLab 8 0 10 9992 0),(.seeLab 8 0 9 9992 1),(.seeLab 8 0 10 9992 1),(.seeLab 8 0 9 9992 2),(.seeLab 8 0 10 9992 2),(.seeLive 8 0 9992 3),(.seeLab 8 0 9 9992 3),(.seeLab 8 0 10 9992 3),(.seeLive 8 0 9992 4),(.exactAt 8 2 9992),(.seeLab 8 2 9 9992 0),(.seeLab 8 2 10 9992 0),(.seeLab 8 2 13 9992 0),(.seeLab 8 2 10 9992 1),(.seeLab 8 2 13 9992 1),(.seeLive 8 2 9992 2),(.seeLab 8 2 10 9992 2),(.seeLab 8 2 13 9992 2),(.seeLive 8 2 9992 3),(.seeLab 8 2 9 9992 3),(.seeLab 8 2 10 9992 3),(.seeLive 8 2 9992 4),(.exactAt 8 6 9992),(.seeLab 8 6 9 9992 0),(.seeLab 8 6 10 9992 1),(.seeLab 8 6 10 9992 2),(.seeLive 8 6 9992 3),(.seeLive 8 6 9992 4),(.exactAt 8 6 16256),(.seeLab 8 6 10 16256 0),(.seeLab 8 6 10 16256 1),(.seeLab 8 6 10 16256 2),(.seeLab 8 6 9 16256 3),(.seeLive 8 6 16256 4),(.diffX 0 8 9),(.diffC 0 8 9),(.diffX 1 8 9),(.diffC 1 8 9),(.diffX 2 8 9),(.diffC 2 8 9),(.adjacentCommon 8 9 6),(.residual 8 9 0 1),(.residual 8 9 0 2),(.residual 8 9 0 3),(.residual 8 9 1 2),(.residual 8 9 1 3),(.residual 8 9 2 3),(.diffX 0 8 10),(.diffC 0 8 10),(.diffX 1 8 10),(.diffC 1 8 10),(.diffX 2 8 10),(.diffC 2 8 10),(.adjacentCommon 8 10 0),(.residual 8 10 0 1),(.residual 8 10 0 2),(.residual 8 10 0 3),(.residual 8 10 1 2),(.residual 8 10 1 3),(.residual 8 10 2 3),(.diffX 0 8 11),(.diffC 0 8 11),(.diffX 1 8 11),(.diffC 1 8 11),(.diffX 2 8 11),(.diffC 2 8 11),(.adjacentCommon 8 11 6),(.residual 8 11 0 1),(.residual 8 11 0 2),(.residual 8 11 0 3),(.residual 8 11 0 4),(.residual 8 11 1 2),(.residual 8 11 1 3),(.residual 8 11 1 4),(.residual 8 11 2 3),(.residual 8 11 2 4),(.residual 8 11 3 4),(.earlier 9 1),(.earlier 9 2),(.allRes 9 0),(.allRes 9 1),(.allRes 9 2),(.exposure 9 432),(.avoidNot 9 7 432 0),(.avoidNot 9 8 432 0),(.avoidNot 9 7 432 1),(.avoidNot 9 8 432 1),(.avoidNot 9 7 432 2),(.avoidNot 9 8 432 2),(.avoidLive 9 432 3),(.avoidNot 9 7 432 3),(.avoidNot 9 8 432 3),(.avoidLive 9 432 4),(.exposure 9 2213),(.avoidNot 9 7 2213 0),(.avoidNot 9 11 2213 0),(.avoidNot 9 7 2213 1),(.avoidNot 9 11 2213 1),(.avoidNot 9 7 2213 2),(.avoidNot 9 11 2213 2),(.avoidLive 9 2213 3),(.avoidNot 9 7 2213 3),(.avoidNot 9 11 2213 3),(.avoidLive 9 2213 4),(.exactAt 9 1 5008),(.seeLab 9 1 7 5008 0),(.seeLab 9 1 8 5008 0),(.seeLab 9 1 7 5008 1),(.seeLab 9 1 8 5008 1),(.seeLab 9 1 7 5008 2),(.seeLab 9 1 8 5008 2),(.seeLab 9 1 7 5008 3),(.seeLab 9 1 8 5008 3),(.seeLive 9 1 5008 4),(.exactAt 9 1 6789),(.seeLab 9 1 11 6789 0),(.seeLab 9 1 11 6789 1),(.seeLab 9 1 7 6789 2),(.seeLab 9 1 11 6789 3),(.seeLive 9 1 6789 4),(.exactAt 9 1 16256),(.seeLab 9 1 7 16256 0),(.seeLab 9 1 8 16256 0),(.seeLab 9 1 11 16256 0),(.seeLab 9 1 7 16256 1),(.seeLab 9 1 8 16256 1),(.seeLab 9 1 11 16256 1),(.seeLab 9 1 7 16256 2),(.seeLab 9 1 8 16256 2),(.seeLab 9 1 11 16256 2),(.seeLive 9 1 16256 3),(.seeLab 9 1 7 16256 3),(.seeLab 9 1 11 16256 3),(.seeLive 9 1 16256 4),(.diffX 0 9 8),(.diffC 0 9 8),(.diffX 1 9 8),(.diffC 1 9 8),(.diffX 2 9 8),(.diffC 2 9 8),(.residual 9 8 0 1),(.residual 9 8 0 2),(.residual 9 8 0 3),(.residual 9 8 1 2),(.residual 9 8 1 3),(.residual 9 8 2 3),(.resCommon 9 10 0),(.resCommon 9 10 1),(.resCommon 9 10 2),(.diffX 0 9 11),(.diffC 0 9 11),(.diffX 1 9 11),(.diffC 1 9 11),(.diffX 2 9 11),(.diffC 2 9 11),(.adjacentCommon 9 11 6),(.residual 9 11 0 1),(.residual 9 11 0 2),(.residual 9 11 0 3),(.residual 9 11 1 2),(.residual 9 11 1 3),(.residual 9 11 2 3),(.earlier 10 1),(.earlier 10 2),(.allRes 10 0),(.allRes 10 1),(.allRes 10 2),(.exposure 10 792),(.avoidNot 10 8 792 0),(.avoidNot 10 9 792 0),(.avoidNot 10 8 792 1),(.avoidNot 10 9 792 1),(.avoidNot 10 8 792 2),(.avoidNot 10 9 792 2),(.avoidLive 10 792 3),(.avoidNot 10 8 792 3),(.avoidNot 10 9 792 3),(.avoidLive 10 792 4),(.exposure 10 2338),(.avoidNot 10 8 2338 0),(.avoidNot 10 11 2338 0),(.avoidNot 10 8 2338 1),(.avoidNot 10 11 2338 1),(.avoidNot 10 8 2338 2),(.avoidNot 10 11 2338 2),(.avoidLive 10 2338 3),(.avoidNot 10 8 2338 3),(.avoidNot 10 11 2338 3),(.avoidLive 10 2338 4),(.exactAt 10 0 9992),(.seeLab 10 0 8 9992 0),(.seeLab 10 0 9 9992 0),(.seeLab 10 0 8 9992 1),(.seeLab 10 0 9 9992 1),(.seeLab 10 0 8 9992 2),(.seeLab 10 0 9 9992 2),(.seeLive 10 0 9992 3),(.seeLab 10 0 8 9992 3),(.seeLab 10 0 9 9992 3),(.seeLive 10 0 9992 4),(.exactAt 10 4 7426),(.seeLab 10 4 8 7426 0),(.seeLab 10 4 11 7426 0),(.seeLab 10 4 8 7426 1),(.seeLab 10 4 11 7426 1),(.seeLab 10 4 8 7426 2),(.seeLab 10 4 11 7426 2),(.seeLive 10 4 7426 3),(.seeLab 10 4 8 7426 3),(.seeLab 10 4 11 7426 3),(.seeLive 10 4 7426 4),(.diffX 0 10 8),(.diffC 0 10 8),(.diffX 1 10 8),(.diffC 1 10 8),(.diffX 2 10 8),(.diffC 2 10 8),(.residual 10 8 0 1),(.residual 10 8 0 2),(.residual 10 8 0 3),(.residual 10 8 1 2),(.residual 10 8 1 3),(.residual 10 8 2 3),(.diffX 0 10 9),(.diffC 0 10 9),(.diffX 1 10 9),(.diffC 1 10 9),(.diffX 2 10 9),(.diffC 2 10 9),(.residual 10 9 0 1),(.residual 10 9 0 2),(.residual 10 9 0 3),(.residual 10 9 1 2),(.residual 10 9 1 3),(.residual 10 9 2 3),(.adjacentCommon 10 11 4),(.earlier 11 1),(.earlier 11 2),(.allRes 11 0),(.allRes 11 1),(.allRes 11 2),(.exposure 11 4370),(.avoidNot 11 8 4370 0),(.avoidNot 11 12 4370 0),(.avoidNot 11 8 4370 1),(.avoidNot 11 12 4370 1),(.avoidLive 11 4370 2),(.avoidNot 11 8 4370 2),(.avoidNot 11 12 4370 2),(.avoidLive 11 4370 3),(.avoidNot 11 8 4370 3),(.avoidLive 11 4370 4),(.exposure 11 5008),(.avoidNot 11 8 5008 0),(.avoidNot 11 8 5008 1),(.avoidNot 11 8 5008 2),(.avoidNot 11 12 5008 3),(.avoidLive 11 5008 4),(.exposure 11 5190),(.avoidNot 11 10 5190 0),(.avoidNot 11 12 5190 0),(.avoidNot 11 10 5190 1),(.avoidNot 11 12 5190 1),(.avoidNot 11 10 5190 2),(.avoidNot 11 12 5190 2),(.avoidLive 11 5190 3),(.avoidNot 11 10 5190 3),(.avoidNot 11 12 5190 3),(.avoidLive 11 5190 4),(.exactAt 11 3 7174),(.seeLab 11 3 10 7174 0),(.seeLab 11 3 12 7174 0),(.seeLab 11 3 10 7174 1),(.seeLab 11 3 12 7174 1),(.seeLab 11 3 10 7174 2),(.seeLab 11 3 12 7174 2),(.seeLive 11 3 7174 3),(.seeLab 11 3 10 7174 3),(.seeLab 11 3 12 7174 3),(.seeLive 11 3 7174 4),(.exactAt 11 3 7426),(.seeLab 11 3 8 7426 0),(.seeLab 11 3 12 7426 0),(.seeLab 11 3 8 7426 1),(.seeLab 11 3 12 7426 1),(.seeLive 11 3 7426 2),(.seeLab 11 3 8 7426 2),(.seeLab 11 3 12 7426 2),(.seeLive 11 3 7426 3),(.seeLab 11 3 8 7426 3),(.seeLive 11 3 7426 4),(.exactAt 11 3 16256),(.seeLab 11 3 8 16256 0),(.seeLab 11 3 8 16256 1),(.seeLab 11 3 10 16256 1),(.seeLab 11 3 8 16256 2),(.seeLab 11 3 12 16256 2),(.seeLive 11 3 16256 3),(.seeLab 11 3 12 16256 3),(.seeLive 11 3 16256 4),(.exactAt 11 6 2338),(.seeLab 11 6 8 2338 0),(.seeLab 11 6 8 2338 1),(.seeLive 11 6 2338 2),(.seeLive 11 6 2338 3),(.seeLive 11 6 2338 4),(.diffX 0 11 8),(.diffC 0 11 8),(.diffX 1 11 8),(.diffC 1 11 8),(.diffX 2 11 8),(.diffC 2 11 8),(.residual 11 8 0 1),(.residual 11 8 0 2),(.residual 11 8 0 3),(.residual 11 8 1 2),(.residual 11 8 1 3),(.residual 11 8 2 3),(.diffX 0 11 10),(.diffC 0 11 10),(.diffX 1 11 10),(.diffC 1 11 10),(.diffX 2 11 10),(.diffC 2 11 10),(.residual 11 10 0 1),(.residual 11 10 0 2),(.residual 11 10 0 3),(.residual 11 10 1 2),(.residual 11 10 1 3),(.residual 11 10 2 3),(.readerAny false 1),(.readerLab false 1 0 0 true),(.readerLab false 1 0 5 false),(.readerAny false 3),(.readerLab false 3 0 1 true),(.readerLab false 3 0 5 false),(.readerAny false 10),(.readerLab false 10 0 0 false),(.readerLab false 10 0 5 false),(.readerAny false 13),(.readerLab false 13 0 5 true),(.readerLab false 13 1 5 true),(.readerLab false 13 2 5 true),(.readerLab false 13 3 5 true),(.readerLab false 13 4 5 true),(.readerAny false 14),(.readerLab false 14 0 5 true),(.readerLab false 14 1 5 true),(.readerLab false 14 2 5 true),(.readerLab false 14 3 5 true),(.readerLab false 14 4 5 true),(.readerAny false 17),(.readerLab false 17 0 1 false),(.readerLab false 17 0 5 false),(.readerAny true 1),(.readerLive true 1 2),(.readerLive true 1 3),(.readerLive true 1 4),(.readerAny true 3),(.readerLive true 3 2),(.readerLive true 3 3),(.readerLive true 3 4),(.readerAny true 10),(.readerLive true 10 2),(.readerLive true 10 3),(.readerLive true 10 4),(.readerAny true 13),(.readerLive true 13 2),(.readerLive true 13 3),(.readerLive true 13 4),(.readerAny true 14),(.readerLive true 14 2),(.readerLive true 14 3),(.readerLive true 14 4),(.readerAny true 17),(.readerLive true 17 2),(.readerLive true 17 3),(.readerLive true 17 4),(.eqLab false 1 10 0 true),(.gateEq true 1 10 0),(.gateEq true 1 10 1),(.eqLab false 1 14 5 false),(.gateEq true 1 14 0),(.gateEq true 1 14 1),(.eqLab false 3 13 5 false),(.gateEq true 3 13 0),(.gateEq true 3 13 1),(.eqLab false 3 17 1 true),(.gateEq true 3 17 0),(.gateEq true 3 17 1),(.eqLab false 10 14 5 false),(.gateEq true 10 14 0),(.gateEq true 10 14 1),(.eqLab false 13 17 5 true),(.gateEq true 13 17 0),(.gateEq true 13 17 1)]

def table95_0 : List Nat := [65,321,0x20102,0x7c1,0x8c1,0x200882,0xa41,0x240a02,0x260a02,0xac1,0xb41,0xbc1,0xc41,0xcc1,0xe41,0x340e02]
def table95_1 : List Nat := [0x360e02,0x3b1282,0x4b1502,0x551782,0x71782,0x91782,0xb1782,0x1cc711bc6d1ac5,0x3c1a82,0x401a82,0x4c1b02,0x4e1b02,0x561b82,0x581b82,0x551c02,0x601c02]
def table95_2 : List Nat := [0x5f1c82,0x1f47b1e4771d45,0x401d02,0x441d02,0x4e1d82,0x501d82,0x4b1e02,0x581e02,0x5a1e02,0x551e82,0x621e82,0x641e82,0x5f1f02,0x661f02,0x681f02,0x21c8520c811fc5]
def table95_3 : List Nat := [0x3c1f82,0x4c2002,0x562082,0x622102,0x5f2182,0x2448f2348b2245,0x402202,0x482202,0x4e2282,0x522282,0x4b2302,0x582302,0x5c2302,0x552382,0x622382,0x5f2402]
def table95_4 : List Nat := [0x26c9925c9524c5,0x412482,0x4f2502,0x4b2582,0x552602,0x5f2682,0x294a32849f2745,0x412702,0x442702,0x4f2782,0x502782,0x592802,0x5a2802,0x552882,0x632882,0x642882]
def table95_5 : List Nat := [0x5f2902,0x672902,0x682902,0x2bcad2aca929c5,0x3c2982,0x412982,0x4c2a02,0x4f2a02,0x562a82,0x592a82,0x552b02,0x602b02,0x632b02,0x5f2b82,0x2e4b72d4b32c45,0x3c2c02]
def table95_6 : List Nat := [0x402c02,0x492c02,0x4e2c82,0x532c82,0x4b2d02,0x582d02,0x5d2d02,0x552d82,0x602d82,0x622d82,0x5f2e02,0x30cc12fcbd2ec5,0x3d2e82,0x4e2f02,0x582f82,0x553002]
def table95_7 : List Nat := [0x5f3082,0x334cb324c73145,0x403102,0x4e3182,0x583202,0x613282,0x5f3302,0x73382,0xc3382,0x93402,0xe3402,0xb3482,0x103482,0xfc1,0x34cd133c4d0f43a0f87,0x34cd133c570f44a0f87]
def table95_8 : List Nat := [0x34cd133c610f4540f87,0x34cd133c571344a0f87,0x34cd133c61134540f87,0x34cd133c6115c540f87,0x73502,0x123502,0x93582,0x143582,0xb3602,0x163602,0x10c1,0x364d73544f1043a1087,0x364d7354591044a1087,0x364d735463104541087,0x364d73545913c4a1087,0x364d73546313c541087]
def table95_9 : List Nat := [0x364d735463164541087,0x73682,0x183682,0x93702,0x1a3702,0xb3782,0x1c3782,0x11c1,0x37cdd36c511143a1187,0x37cdd36c5b1144a1187,0x37cdd36c65114541187,0x37cdd36c691145e1187,0x37cdd36c5b1444a1187,0x37cdd36c65144541187,0x37cdd36c691445e1187,0x37cdd36c6516c541187]
def table95_10 : List Nat := [0x37cdd36c6916c5e1187,0x37cdd36c691945e1187,0xe13b02,0xed3d02,0xd3f02,0xf3f02,0x113f02,0x4350b425074145,0xe24102,0xe44102,0xee4182,0xf04182,0xf64202,0xf84202,0xf54282,0xfe4282]
def table95_11 : List Nat := [0x1004282,0xfd4302,0x45d1544d1143c5,0xe24382,0xe84382,0xee4402,0xf24402,0xf64482,0xfa4482,0xf54502,0xfe4502,0x1024502,0xfd4582,0x4851f4751b4645,0xe34602,0xe44602]
def table95_12 : List Nat := [0xef4682,0xf04682,0xf74702,0xf84702,0xff4782,0x1004782,0xfd4802,0x4ad2949d2548c5,0xe84882,0xf24902,0xf74982,0x1024a02,0xfd4a82,0x4d5334c52f4b45,0xe34b02,0xe44b02]
def table95_13 : List Nat := [0xe84b02,0xef4b82,0xf04b82,0xf24b82,0xf74c02,0xf84c02,0xfa4c02,0xf54c82,0xff4c82,0x1024c82,0xfd4d02,0xd4d82,0x64d82,0xf4e02,0x84e02,0x114e82]
def table95_14 : List Nat := [0xa4e82,0x4ed394dcf1394e00f87,0x4ed394dcf9394ec0f87,0x4ed394dd01394f40f87,0x4ed394dcf93c4ec0f87,0x4ed394dd013c4f40f87,0x4ed394dd013e4f40f87,0x39c120303,0x39c140383,0x39c160403,0xd4f02,0x184f02,0xf4f82,0x1a4f82,0x115002,0x1c5002]
def table95_15 : List Nat := [0x3ac1,0x5053f4f4f33a4e03a87,0x5053f4f4fb3a4ec3a87,0x5053f4f5033a4f43a87,0x5053f4f4fb3ccec3a87,0x5053f4f5033ccf43a87,0x5053f4f5033ecf43a87,0x1435302,0x14d5502,0x135702,0x155702,0x175702,0x5b56b5a5675945,0x1445902,0x1465902,0x14e5982]
def table95_16 : List Nat := [0x1505982,0x1565a02,0x1585a02,0x1555a82,0x15e5a82,0x1605a82,0x15d5b02,0x5dd755cd715bc5,0x1445b82,0x1485b82,0x14e5c02,0x1525c02,0x1565c82,0x15a5c82,0x1555d02,0x15e5d02]
def table95_17 : List Nat := [0x1625d02,0x15d5d82,0x6057f5f57b5e45,0x1455e02,0x1465e02,0x14f5e82,0x1505e82,0x1575f02,0x1585f02,0x1555f82,0x15f5f82,0x1605f82,0x15d6002,0x62d8961d8560c5,0x1446082,0x1496082]
def table95_18 : List Nat := [0x14e6102,0x1536102,0x1566182,0x15b6182,0x1556202,0x15e6202,0x1636202,0x15d6282,0x136302,0x66302,0x156382,0x86382,0x176402,0xa6402,0x6458f6354f515421087,0x6458f635575154c1087]
def table95_19 : List Nat := [0x6458f6355f515541087,0x6458f6355753d4c1087,0x6458f6355f53d541087,0x6458f6355f55d541087,0x136482,0xc6482,0x156502,0xe6502,0x176582,0x106582,0x65d9564d5151d423987,0x65d9564d5951d4c3987,0x65d9564d6151d543987,0x65d9564d595454c3987,0x65d9564d61545543987,0x65d9564d61565543987]
def table95_20 : List Nat := [0x52c1,0x1996802,0x1a16a02,0x196c02,0x1b6c02,0x1d6c02,0x705bf6f5bb6e45,0x19a6e02,0x19e6e02,0x1a26e82,0x1a66e82,0x1a16f02,0x1aa6f02,0x1ae6f02,0x1a96f82,0x1b26f82]
def table95_21 : List Nat := [0x1b17002,0x72dc971dc570c5,0x19a7082,0x1a27102,0x1aa7182,0x1b67202,0x1b17282,0x755d3745cf7345,0x19c7302,0x19e7302,0x1a47382,0x1a67382,0x1ac7402,0x1ae7402,0x1a97482,0x1b47482]
def table95_22 : List Nat := [0x1b67482,0x1b17502,0x77ddd76dd975c5,0x19c7582,0x19f7582,0x1a47602,0x1a77602,0x1ac7682,0x1af7682,0x1a97702,0x1b47702,0x1b77702,0x1b17782,0x7a5e7795e37845,0x19a7802,0x19f7802]
def table95_23 : List Nat := [0x1a27882,0x1a77882,0x1a17902,0x1aa7902,0x1af7902,0x1a97982,0x1b27982,0x1b17a02,0x7cdf17bded7ac5,0x19a7a82,0x1a27b02,0x1a47b02,0x1aa7b82,0x1af7b82,0x1a97c02,0x1b77c02]
def table95_24 : List Nat := [0x1b17c82,0x7f5fb7e5f77d45,0x19b7d02,0x1a37d82,0x1a17e02,0x1a97e82,0x1b17f02,0x197f82,0x67f82,0x1b8002,0x88002,0x1d8082,0xa8082,0x80e017fda366d981187,0x80e017fdab66da01187,0x80e017fdb366da81187]
def table95_25 : List Nat := [0x80e017fdab68da01187,0x80e017fdb368da81187,0x80e017fdb36ada81187,0x198102,0x128102,0x1b8182,0x148182,0x1d8202,0x168202,0x82607815a5675985287,0x82607815ad675a05287,0x82607815b5675a85287,0x82607815ad695a05287,0x82607815b5695a85287,0x82607815b56b5a85287,0x82c1]
def table95_26 : List Nat := [0x834008283,0x838038283,0x8441,0x84c1e8403,0x850218403,0x85c1,0x860258583,0x868278583,0x896238861f8745,0x89c2a8703,0x89c2c8783,0x89c2e8803,0x89c308883,0x89c328903,0x8c62f8b62b8a45,0x8cc2a8a03]
def table95_27 : List Nat := [0x8cc2c8a83,0x8cc2e8b03,0x8cc308b83,0x8cc328c03,0x8d41,0x8d8358d03,0x8e0378d03,0x90e418fe3d8ec5,0x14d8f82,0x1559002,0x15d9082,0x9364b926479145,0xed9202,0xf59282,0xfd9302,0x95e5594e5193c5]
def table95_28 : List Nat := [0x14d9482,0x1559502,0x15d9582,0x9865f9765b9645,0xed9702,0xf59782,0xfd9802,0x9ae6999e6598c5,0x14d9982,0x1559a02,0x15d9a82,0x9d6739c66f9b45,0xed9c02,0xf59c82,0xfd9d02,0x8660c9d83]
def table95_29 : List Nat := [0x9de4e8e83,0x9de508f03,0x8ca0f9e03,0x9e6628e83,0x9e6648f03,0x89a159e83,0x9ee589103,0x9ee5a9183,0x8de129f03,0x9f66c9103,0x9f66e9183,0x8ca1b9f83,0x9fe629383,0x9fe649403,0x8e626a003,0xa066c9603]
def table95_30 : List Nat := [0xa066e9683,129,0x801,0x901,0x981,0xd01,0xd81,0xd3344cf1343d0e86,0xd3344cf15c3d1286,0xd3344cf1843d1506,0xd3344cf15c4d1286,0xd3344cf1844d1506,0xd3344cf184571506,0xd935cd513c410e86,0xd935cd5164411286,0xd935cd518c411506]
def table95_31 : List Nat := [0xd935cd51644f1286,0xd935cd518c4f1506,0xd935cd518c591506,0xdf374db144450e86,0xdf374db16c451286,0xdf374db194451506,0xdf374db1a4451786,0xdf374db16c511286,0xdf374db194511506,0xdf374db1a4511786,0xdf374db1945b1506,0xdf374db1a45b1786,0xdf374db1a4651786,0x13b4e5373c4e53806,0x13b4e5373e4e53b06,0x13b4e537404e53d06]
def table95_32 : List Nat := [0x13b4e5373e4f13b06,0x13b4e537404f13d06,0x13b4e537404f93d06,0x1414fd3d3cce93806,0x1414fd3d3ece93b06,0x1414fd3d40ce93d06,0x1414fd3d3ecf33b06,0x1414fd3d40cf33d06,0x1414fd3d40cfb3d06,0x19163d8d53d455086,0x19163d8d55d455306,0x19163d8d57d455506,0x19163d8d55d4f5306,0x19163d8d57d4f5506,0x19163d8d57d575506,0x203805ff68d9b6606]
def table95_33 : List Nat := [0x203805ff6ad9b6806,0x203805ff6cd9b6a06,0x203805ff6ada36806,0x203805ff6cda36a06,0x203805ff6cdab6a06,0x20981e056959d6606,0x20981e056b59d6806,0x20981e056d59d6a06,0x20981e056b5a56806,0x20981e056d5a56a06,0x20981e056d5ad6a06,0x8341,0x8381,0x84c1,0x8501,0x8601]
def table95_34 : List Nat := [0x8681,0x2278702,0x2278782,0x2278802,0x2278882,0x2278902,0x2338a02,0x2338a82,0x2338b02,0x2338b82,0x2338c02,0x8d81,0x8e01,0x9d81,0x24e8e82,0x2508f02]
def table95_35 : List Nat := [0x2329e02,0x2269e82,0x9f01,0x26c9102,0x26e9182,0x2329f82,0x226a002,0x89c1,0x9e81,0xa001,0x8cc1,0x9e01,0x9f81,0x3f0872bc611505,0x5e2845b6c04,0x1b16899a6c84]
def table95_36 : List Nat := [0x179b16a1a26685,0x5e6c5a86884,0x179b16a03,0x1c17a5bf79daa6686,0x5e6c59b68c4,0x179b16a83,0x179b166c3,0x705e96fde76e5e16887,0x5e6c42,0x178791d4772905,0x5e294a31d84,0x178791ec6828c5,0x5e1e47b1a04,0x178791a43,0x5e1e42,0x1781]
def table95_37 : List Nat := [0x1c81,0x1f01,0x2181,0x2401,0x2681,0x2901,0x2b81,0x2e01,0x3081,0x3301,0x7837cdd36c4,0xfc128712a04,0xfc1c02,0x3f04a2983,0xfc2b02,0xfc1282]
def table95_38 : List Nat := [0x4b1002,0x12c1,0xec1,0x3f01,0x4301,0x4581,0x4801,0x4a81,0x4d01,0x9301,0x9801,0x9d01,0x19826077adcf681ef6a48,0x660981dcf681a86947,0x660981ddb6a1d97307,0x1982607669bf6986]
def table95_39 : List Nat := [0x660981dd9681a87307,0x660981dd9681a86947,0x660981dd9681d16a07,0x660981dd9681dd7307,0x1982607785e769c6,0x660981d9a6985,0x19826076684,0x660981da875ddb7647,0x660981da87605,0x19826076a04,0x1982607681db7646,0x660981da07605,0x19826076804,0x660981c3,0x6c5a16883,0x1b16842]
def table95_40 : List Nat := [0x63415645546205,0x156454c635895b86,0x156454c635895c06,0x156454c635895c86,0x15645546344,0x354d7364412c05,0xd7354d91044,0xd535cd92d84,0xd92dc5418cd73546,0x150a3274dd36c6537c7,0x15d5554d9904,0x575555343,0x350156443,0x37ca3274dd36c7b1407,0xa32745437cdd36c6,0x4dcf44ed394105]
def table95_41 : List Nat := [0x4dcf44ed394185,0x4dcf44ed394205,0xf44dd3b4e44,0xf43a50f5053f4f46,0xd12b4d329ccf0f46,0x344d31b45433c6b1347,0x344ad34ca71b45433c7,0xd12b4d329ccf1b86,0x33cd134c572b05,0xcf344a734c6d15c6,0xcf344a734ca91306,0x344a733cd32a45,0xd133ca734c4,0x6458d62d895317263c7,0x19365417399555e06,0xd7364d52384]
def table95_42 : List Nat := [0x2dc8f224b11385,0x35cd93543,0x4d9539955595975f07,0x4d95399555957b65c7,0x15d555445584,0x1ff80c1b79dbf68c6,0x1ff80c1b79de16fc6,0x7fe0306de77845,0x1ff80c1b7804,0x7fe0306c3,0x1a26a99a6c44,0x375b027c9d28c5,0x375b02883,0x375b02703,0xdd6c02,0x6c01]
def table95_43 : List Nat := [0x7001,0x7501,0x7781,0x7a01,0x6841,0x6641,0x3745536cdf1445,0xdd154db37c4,0x689aa6c83,0x689aa6a43,0x3d4ed9b83,0xf53b42,0x4fd3d504f54b05,0x4fd3d504f54b85,0x13f4f5413d44,0x13f4f5413ec4]
def table95_44 : List Nat := [0x4fd3d5052d4405,0x13f4f54143c4,0x4fd3d5043,0x711ac3d34ccf3446,0x6458f04d555105,0x19163c135544,0x6458f04d715145,0x6458f04d715585,0x19163c135c44,0x6458f04c3,0x825a8815cd81dcf7687,0x209815dd81ddb6b46,0x825a8815cd7760773c7,0x1a8815cd825dd81c6,0x1565d545a56b64ce65848,0x481565d545ed695e56b0309]
def table95_45 : List Nat := [0x55975517b5a5795ace664c9,0x1374ed394c04,0x1374ed394b84,0x4dd3b4e43,0x344d333c3d1ac5,0x33cd33443,0x36c5437cdd27ca11447,0x36c75150df3749f2847,0x36c5437cdd16c5,0x36c75150df3745,0x81e05825a86945,0x207826056a1d17346,0x207826056a1db7306,0x81607825a87345,0x207826056a04,0x81e05776097305]
def table95_46 : List Nat := [0x81e056a6096b05,0x207815a98244,0x1265c15031545a56b5908,0x48170540c551695ac7,0x1765593399545a86,0x48170540c5505,0x1933981565d7f531795a08,0x64ce6055975ad7f531795409,0x120301505c4,0x64ce60555565d695447,0x19339815555975a46,0x64ce60555565c5,0xdd36cdf1504,0x36cdd37c3,0x805ff80da966c5,0x2017fe036a44]
def table95_47 : List Nat := [0x64ce665c155645,0x19339997655545b5695e88,0x64ce665c155e45,0x20780cdb0644,0x816078243,0x64ce605d545a5786547,0x81d3b80d4103c5,0x64ce665d81655545ed7951c9,0x19339817655545a46,0x64ce605d955505,0x64ce665d816557f531795a09,0x64ce665d6d6556b531695649,0x480c0503,0x20180dff68c4,0x20180dff6a84,0x806037fc3]
def table95_48 : List Nat := [0x1933981565c4,0x120302,0x120442,0x127f82,0x1280c2,0x481,0x5701,0x6481,0x5b01,0x6001,0x65597399555e05,0x65597399555e85,0x19565ce65544,0x65597399795ed695ac7,0x19565ce65e57b5a86,0x65597399795a05]
def table95_49 : List Nat := [0x197399796557b5a46,0x19565ce65e44,0x65d953983,0x80382,0x1ff0202,0x981d3f4e84,0x24e665c3,0x7fd960283,0x1ff6582,0xe73513d8184,0x1ff02c2,0x7fc1,0x641,385,0x4f01,0x3381]
def table95_50 : List Nat := [0x3501,0x401,0x5001,0x4fc1,961,0x3401,0x6501,513,0x34c1,0x3581,705,0x3641,0x6401,0x581,0x63c1,0x6581]
def table95_51 : List Nat := [0x541,0x3981]

def encoded95 (i : Nat) : Nat :=
  if i < 416 then
    if i < 208 then
      if i < 96 then
        if i < 48 then
          if i < 16 then
            table95_0.getD (i%16) 0
          else
            if i < 32 then
              table95_1.getD (i%16) 0
            else
              table95_2.getD (i%16) 0
        else
          if i < 64 then
            table95_3.getD (i%16) 0
          else
            if i < 80 then
              table95_4.getD (i%16) 0
            else
              table95_5.getD (i%16) 0
      else
        if i < 144 then
          if i < 112 then
            table95_6.getD (i%16) 0
          else
            if i < 128 then
              table95_7.getD (i%16) 0
            else
              table95_8.getD (i%16) 0
        else
          if i < 176 then
            if i < 160 then
              table95_9.getD (i%16) 0
            else
              table95_10.getD (i%16) 0
          else
            if i < 192 then
              table95_11.getD (i%16) 0
            else
              table95_12.getD (i%16) 0
    else
      if i < 304 then
        if i < 256 then
          if i < 224 then
            table95_13.getD (i%16) 0
          else
            if i < 240 then
              table95_14.getD (i%16) 0
            else
              table95_15.getD (i%16) 0
        else
          if i < 272 then
            table95_16.getD (i%16) 0
          else
            if i < 288 then
              table95_17.getD (i%16) 0
            else
              table95_18.getD (i%16) 0
      else
        if i < 352 then
          if i < 320 then
            table95_19.getD (i%16) 0
          else
            if i < 336 then
              table95_20.getD (i%16) 0
            else
              table95_21.getD (i%16) 0
        else
          if i < 384 then
            if i < 368 then
              table95_22.getD (i%16) 0
            else
              table95_23.getD (i%16) 0
          else
            if i < 400 then
              table95_24.getD (i%16) 0
            else
              table95_25.getD (i%16) 0
  else
    if i < 624 then
      if i < 512 then
        if i < 464 then
          if i < 432 then
            table95_26.getD (i%16) 0
          else
            if i < 448 then
              table95_27.getD (i%16) 0
            else
              table95_28.getD (i%16) 0
        else
          if i < 480 then
            table95_29.getD (i%16) 0
          else
            if i < 496 then
              table95_30.getD (i%16) 0
            else
              table95_31.getD (i%16) 0
      else
        if i < 560 then
          if i < 528 then
            table95_32.getD (i%16) 0
          else
            if i < 544 then
              table95_33.getD (i%16) 0
            else
              table95_34.getD (i%16) 0
        else
          if i < 592 then
            if i < 576 then
              table95_35.getD (i%16) 0
            else
              table95_36.getD (i%16) 0
          else
            if i < 608 then
              table95_37.getD (i%16) 0
            else
              table95_38.getD (i%16) 0
    else
      if i < 720 then
        if i < 672 then
          if i < 640 then
            table95_39.getD (i%16) 0
          else
            if i < 656 then
              table95_40.getD (i%16) 0
            else
              table95_41.getD (i%16) 0
        else
          if i < 688 then
            table95_42.getD (i%16) 0
          else
            if i < 704 then
              table95_43.getD (i%16) 0
            else
              table95_44.getD (i%16) 0
      else
        if i < 768 then
          if i < 736 then
            table95_45.getD (i%16) 0
          else
            if i < 752 then
              table95_46.getD (i%16) 0
            else
              table95_47.getD (i%16) 0
        else
          if i < 800 then
            if i < 784 then
              table95_48.getD (i%16) 0
            else
              table95_49.getD (i%16) 0
          else
            if i < 816 then
              table95_50.getD (i%16) 0
            else
              table95_51.getD (i%16) 0
def book95 (i : Nat) : Clause := let n := encoded95 i; unpackLits 10 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses95 : inputsOK 3 95 a95 r95 (baseBook book95 481).toList=true := by decide +kernel

def rows95_0 : List Nat := [0x80401,0x200a01,0x300e01,0x301001,0x701e01,0x702001,0x3e8fc01,0x3e8fe01,0x3e90001,0x3e90201,0x3e90401,0x3e90601,0x4511601,0x4511801,0x4511a01,0x4511c01,0x4511e01,0x4512001,0x4b93001,0x4b93201,0x4b93401,0x4b93601,0x4b93801,0x4b93a01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk95_0 : checkRows book95 10 481 rows95_0=true := by decide +kernel

def rows95_1 : List Nat := [0x4b93c01,0x4b93e01,0x4b94001,0x4b94201,0x3e9c201,0x3e9c401,0x3e9c601,0x3e9c801,0x3e9ca01,0x3e9cc01,0x781e201,0x781e401,0x781e601,0x781e801,0x781ea01,0x781ec01,0x4525c01,0x4525e01,0x4526001,0x4526201,0x4526401,0x4526601,0x4bb1a01,0x4bb1c01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk95_1 : checkRows book95 10 505 rows95_1=true := by decide +kernel

def rows95_2 : List Nat := [0x4bb1e01,0x4bb2001,0x4bb2201,0x4bb2401,0xa033201,0xa033401,0xa033601,0xa033801,0xa033a01,0xa033c01,0xcfb4002,0x3c2cfb4202,0x6d134602,0x3c4d134802,0x3c6d2b4c02,0x3c8d2b4e02,0x4b5201,0x535401,0x5b5601,0x635801,0x6b5a01,0x4b5e01,0x536001,0x5b6201]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk95_2 : checkRows book95 10 529 rows95_2=true := by decide +kernel

def rows95_3 : List Nat := [0x636401,0x6b6601,0x3cada36a02,0x3ccda36c02,0x43f0db9e02,0x116ba001,0x116ba201,0x10e3a401,0x10f3aa01,0x4570ebb002,0x1193b201,0x1193b401,0x1103b601,0x1163bc01,0x112c4911c4510b5005,0x11bc6201,0x11bc6c01,0x1154531444f1335c05,0x11d46001,0x11d46a01,0x662985e2b0622a0602c064f5bd2f60f0520f4528f8530b812,0x90250a427be8fbbf6fd12c4a124a2a88a18240988c10,0xa6adaa32eca7aa0bba92b828eb72e80b,0xaaaf0a8af8aa4291faf2a93100a3140ab180b2acc02a6bd2fe13]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk95_3 : checkRows book95 10 553 rows95_3=true := by decide +kernel

def rows95_4 : List Nat := [0xa42daa32eca7ae6a642308480b8292c4028c502ac602ca82eea12de15,0xa52daa32dca3aeca7ae6a641f09c2520a82a13100a3140ab180b2a0bbae217,0xa52daa32dca3a98b9ae207,0x282c0c1ec1b100a3140ab180b30cc2c84c13080e,0x290b6a8cb829322486b9a98a82eea72eb212de0e,0xa42daa32e0a4ae4a5c89083100a3140ab180b2a0bba9cbac8522ade15,0xa6adaa32e0a4ae805,0x294b6a8cb92970948eb728f2348abaa9d212eea83100a3140ab180b2e216,0x42fe05a290a2492864a2884b28b240560c,0x24098f9bee2484a1202209026492864a2884b28b2408c11,0x26094fa3e623846110432502209026492864a2884b28b2405c2908c15,0x12846fc3ea27c9617026492864a2884b28b240420f,0x49226094128901189efdbf2fb3f8492864a2884b28b2408c12,0x9424098fc3eafd09c15855260a526826492864a2884b28b2408c14,0x2585013c9d2447c05,0x12784001,0x12785801,0x12786801,0x12787e01,0x12788a01,0x1278a001,0x1278ba01,0x1278d401,0x1278e001]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk95_4 : checkRows book95 10 577 rows95_4=true := by decide +kernel

def rows95_5 : List Nat := [0x1278ec01,0x9e2688c24094fa3ee130502584f2abf40c,0xc0380dbcef50ae2b0f0520f4528f8530232802e0f,0x3e0f4ad2947a04,0x340e032f3bd02a8a83c1483d14a3e14d2e0232802e10,0xb62d4ad2947a04,0x300d03af43d42c8b029cbb2d8f0520f4528f8534b92f4a12b02e14,0x722f06a3006c1d0c81e8ce094af298c60c,0x1b8bc1a8c41c08420083300ce2207a320861d0252bca72a0c213,0x13082201,0x130cbe01,0x13196201,0x13197801,0x13198c01,0x13199801,0x1319b401,0x131b7c01,0x131b8c01,0x131b9c01,0xac2b90ac30bdaf0bf2bcc9ac2c0286a0aae0d,0x2b0afab90ac330c326b0a86a0aae0a,0x2d4b242eacab0c9ad8a1ac408,0xb1ad50b434ae2af372c0bfaf0bdacb36cd8bead0a6a96a32b6a5326a82c2b6300a1a8ebcac41d,0x42d372b0c9ace04]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk95_5 : checkRows book95 10 601 rows95_5=true := by decide +kernel

def rows95_6 : List Nat := [0x2c6b52cf0ac330c326b6286a0ac40a,0xb3ac6b5c350bac0afaaead4e338326b0ad8a1ac40f,0x2ceb242cacab0c9ad8a1ac408,0x2c6b3c2b0c2b4abce6b4abd392baa0ae8b92dab8accc9ac2b62eea1ac416,0xb1ad4b442d0d2baae4e4b2cdaa129d37ab6c9ad8a1ac411,0xb1ad4b442d0d2baae4e4a12eb3a2cd3aadcc9ad8a1ac411,0x2d4ae2c539326b6286a143408,0x4dab32caa12b604,0x13bc2cb42baae4e53c284c9ac609,0xae2b50b42ab1ac539b26b0ad8a1abcb4cf2a0aae0f,0xac2b8adc2b0c2ccb2b26b0a86af4f2a0aae0d,0x2b4aec30b42cf3d4e73db26b0a86af2d33caae0e,0xa42daa32e0a4b06c0b08b92973e30abaa9d3cb053b2a0bbb0ca1ade15,0x290b6a8cb8292a82eea5ae4a72eaa12de0c,0xa52daa32dca3b04c0b073f30abaa9cc22e4a5a84a82eec32e213,0x218852108841d06c169324a952227d20e0c,0x912408fc1504a1284254939f47ba3a0b,0x8f24490c130621685254939f47ba3a0b,0x2408f2470641486a189524e7d23a0a,0x912408f41d06c1687a0f41d0540d0095222939f47c23a11,0x7c3786a3586e360c22f876373dc1c0daf6ca72c4c530bde12,0x348ce2f50a310caf6bdd30cc52bbde0b,0x3a0e6f93e23a8d2340ce3950d2c8e20b,0x328c4303e4f8bdf2b8bc07]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk95_6 : checkRows book95 10 625 rows95_6=true := by decide +kernel

def rows95_7 : List Nat := [0x26094fd3f12a88c05,0x37edbbbaea374e1372e0b70e04791dc5c0c,0xdfb6eee3a6e3d14e4380dc374e1394dcb82e4c791dc5e11,0x20f4150345a488750894908889f242d060c,0x981188c1089412cb530cab28be80a,0x2484223046263e6fbd1a15cb544cc3314ab288480f,0x18a61982ffbfcfe97c54950511473317a0c,0x17e62986fec030018055954511473317a0c,0x6097e62c00ff4046115a561473317a0b,0x619825fc0500bfe621605794f48d2147cc93317a0f,0x5d9705b40b02406511473296409,0x2b0b0f3bd12b4c5308a607,0x3e0e3d6f54a13082e06,0x3e0ebd82c8b0298ad4a8314a4a12b02e0c,0x2b0b2f503a0e4ad308a607,0xb62d3d802,0x2f4b52f4c030f44a13083c08,0x6019bd22e0b62d0a62c0654c8620d4a52b05e0e,0xb62d0a62c3d54d4c32b3d608,0x14a82e0c0380dbcef50ae2b53730cc52803c0d,0x9023d064148624686a3a07,0x802049d2767ea2889a70832067bd167d9f80d,0x1f07b43d1003,0x1e0bc1a8c41c4af298cc07]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk95_7 : checkRows book95 10 649 rows95_7=true := by decide +kernel

def rows95_8 : List Nat := [0x1c8bc1a8ca1dbe1500c01b53f43d0d30ca72b8c60f,0x1f89ea028c22e9a20c81d167ca000a,0x802049d2768a225512688323881a327bd167c9f80f,0x85a3a83a448622293a1c922108f2420b,0x41f09312a82eea0cfea248608,0xb9a8eb6c8eb854ac4aa0bbcfea24200b,0x2e6b842909a9ea754cc4aeea22da0a,0xa7a9ca3298a4a910841eb7adcc4aa0a0cfea24220f,0x2aabc2a2be2a8bd2a6bcaa50a42708aecbad4f54300ab312a22fe14,0xaaaf0a8b00ab2a6bd2a8be2a4bcafe0b,0xfb8522651c23124a192ca2cc32ad1a0b,0x4612beafc0542789c26cb44b28a49287288420e,0x158521084af98442408f2d12ca2924a1ca3313ea0f,0x10be612052250934755756d592d12c4928aa1ca33104611,0x55ca212802,0x157aa001,0x157ac201,0x157ad801,0x157aee01,0x157cfe01,0x15a28201,0x1208c1089011898f9bee1489b2d4ab28cc5308920f,0x238434684b5b4b41489b2884409,0xa42daa32eca7a92b8298b9d67582de0b]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk95_8 : checkRows book95 10 673 rows95_8=true := by decide +kernel

def rows95_9 : List Nat := [0xa42daa32eaa7292b8298b9d67582de0b,0x386ddbc11a37ae2b78e2471354d31cbac0c,0xe1b76efc66e5d74e6388de37ae2b9b1c4d534c7335bae11,0x5b17101c08599a06717251577329640b,0x5a17101c0c5a9a66897251577329640b,0x5b169034085b9ac6a19b5ed795d9ae5cccb341640f,0x1945918e6496c641686597703409041475f4cb3396e10,0x66c0e6896c5ad7c6b57f341b209,0x66c0e6c1765d165601a149d7c5c1ad5fcd1329a60f,0x1b269c0b0199c5a167609ad5f94451d7d3419a0e,0xe034f43cf284c33102e07,0x21506548842228753b45a48939f29420e0c,0x2128ea0e9021491413055894e9ef45a488725088a4e7ca3e12,0x2128ea0e9024a87a448641305c1494222939f27b9f162a3e12,0x2409341a8821e83a448625088a4e7cd8a8423d6323a10,0x83a4a87c1d63a116325088a4e7c9f162d3a0d,0x2448f24a90c1904c1a85a15641ee7c58a93a507ca3a10,0x2beaec34b42cf58aae06,0x2cab1c310b5655a2c406,0xb2ac70cc2eafaaeae5976556558ac40b,0xb1aceb342b0c2b6ad5995a56b592c40b,0x801fc9f2789b20c7d1f807,0x801fc9ea768c2248dd9c73a6a9b20c8e1f47c1f80f,0x801fc9ea768c2248dd9c9b20c8e1f47c1f80d]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk95_9 : checkRows book95 10 697 rows95_9=true := by decide +kernel

def rows95_10 : List Nat := [0x55953003fc561aa6a15d5dd253214e0b,0x15256bfb00154691a2571455dd253214e0c,0x56956ff3fa5419e6719b695a2515766b95d494d13214e11,0xf83d61bd203,0x322a8a94e5a804,0x9e243f0f9cab3108c06,0x233ea270561504212dad2d4ab288900b,0x27890fd3e930d1c05,0x42fc048250936b8996c4b5288560a,0xac2d50ac335ad9a05,0x2d6abd9aad5b558ac006,0x2d4b242eacab0b2db5592c408,0x2b8b55b766c3404,0x10b5b8ac5bb5a2ce05,0x2ceb2ac90b42aacab1595695aac40a,0x2c6b342aadab4abaceae2bd6fad35956b58ac40e,0xabad0ad5970c5c16fabcb4d635a2ba0b,0x59e9d2267f1fa9b26a739ee7c22c0a,0x1682748aa007f9f971270831f69b26a739ee7c2280f,0x2308b2289fa7c9e23482a089c2387da240c,0x22c8a2369ea769fa2e8120371dc87c2708e1f69b26a73a2412,0x2249ea2e812029b2387d22c08,0x8c1fc891f88b2009b20c8e1f5732760b,0x1fe891f88c1fc9ea7573dcc7bd3d45a3281dca9c26a73a6c832387d22a16]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk95_10 : checkRows book95 10 721 rows95_10=true := by decide +kernel

def rows95_11 : List Nat := [0x1fe891f88c2287f27a9d26c8323881a327bd167d22a10,0x2267e5ce805d2832068cd167d1fa0a,0x277732057526c8cd167d22808,0x51cfa88e118456c89e06,0x15bdd801,0x42107d695ad7204,0x48f21adca3ddcbaa9d5a567584240a,0x8a23682a7a9da7e9b1f175dce09,0x7f20a9d27c7fa2c8a9ee7c1f809,0x208895a08e23178a057820c7d5d69b2340c,0x12c4a32f54cfac3dda06,0x16f5c201,0x7e27572270831f67b9f08a1fa89a000b,0x489d66e585699d86ede607,0x8c2369da787c22405,0x2368c27c9ea007e1fd7bdeb78a70832387d9f17222410,0x22c8a2369ea769fa2e812037c1f09c2387da240e,0x8927a8ba0480a2c05,0x2007f27a9d9f804,0x7e2747fa2c8aa248c5f77d1ef4f5168ca077ca6f7b1decbde88e20c9c1f6c61c04491150b2c4390aca26a739fc23,0x2eca7c2707c2577d675856b5a4860a,0x15c55577dfb57c2205,0x10a4217f5fb77d6957c7e07,0x20082a749e1fa7ba2889a047c5e5785d69b20c7d1f810]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk95_11 : checkRows book95 10 745 rows95_11=true := by decide +kernel

def rows95_12 : List Nat := [0x4adff76b0e489d66e585699dc6fa73801da4a3146f32a435e950b3044dd17e1ce9a90aca3181d,0x30f76dfe4b318cb9117a542cab124990c769bd615a6771be42b286d9d58092418,0x1297a5dacb92a779c1615a6761bc3d0f36a8ee49310c3b286d9d5808f98132a18,0x5034ed0545a488725493a234232c7da5a94de8449103bb2f50daa7790c3cd84c51db7fd5242b28756023e60581a0e24,0x5034ed0545a488750896252cc0ee93a237a5aa7d256ca8f44390c769d950d84441dec6317820f9811d580b2842a0e24,0x1829f201,0x182a6801,0x18320c01,0x18323801,0x5469d1fa8a2267bd1782e0f8322c0a,0x7f2747fa2c8aa067bdf5855168ce1183e13831f80f,0x2257de177d61545a3281e138460f832300c,0x8927c8c2017d9f87c1fd7be1984e0f842360d,0x2249fa3482a098661383a3008,0x9fdf4811f18660f84a3607,0x186e1c01,0x178e1f8661183e2005,0x8020482a749da787ea2889e227b9f18660f841f80f,0x1d29c9bf699b83bdaa9b8f46f2583da5b64a5782e2410,0x1d29c9bf699b848dda4a32ccacfa75d84766267792acc31696a597fd92c52566f60f82e001c,0x32f614fa751243c5db6a92a3e1c06f8f2499de0e,0x773183e0f76a8f06dda78a9d86ea6ecb625800f383dec11,0x5853e9dacb5534631896b3077273509129c10d8a1d610,0x32b614fa751243c5db6a92a3de2e773309ca703c9278a1da12]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk95_12 : checkRows book95 10 769 rows95_12=true := by decide +kernel

def rows95_13 : List Nat := [0x772596151876b2cca9d207,0x765196125877b30cbde98cb26751243c5db50daa4a9103d8f2431278b6318a1d019,0xf03e1b6775a77b1ba7432c95592c625a706358b6303ce2982daa14,0x18db0e01,0x18db1001,0x18e1d601,0x18e8ee01,0x18e90801,0x1805427491296592958f36aa723e60f9060b8f90e0f,0x1909dc01,0x63d9158402,0x1919d801,0x1920f401,0x19226e01,0x19262601,0x63f92daa02,0x19390c01,0x1940f601,0x64194d4202,0x19525a01,0x19591201,0x60b9659202,0x196a7001,0x19725401]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk95_13 : checkRows book95 10 793 rows95_13=true := by decide +kernel

def rows95_14 : List Nat := [0x64d97e2402]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk95_14 : checkRows book95 10 817 rows95_14=true := by decide +kernel

def lastUnits95 := digits 10 3 0x324cc730
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict95 : checkReasons book95 818 232 lastUnits95 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude95 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 95=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=3) h hc bp eq (by decide +kernel)
  let v := truth Z a95
  have hbase : ValidThrough v book95 481 := book_start Z h hc z eq _ _ _ _ initialClauses95
  have h0 : ValidThrough v book95 505 := rows_sound hbase rows95_0 rowsOk95_0
  have h1 : ValidThrough v book95 529 := rows_sound h0 rows95_1 rowsOk95_1
  have h2 : ValidThrough v book95 553 := rows_sound h1 rows95_2 rowsOk95_2
  have h3 : ValidThrough v book95 577 := rows_sound h2 rows95_3 rowsOk95_3
  have h4 : ValidThrough v book95 601 := rows_sound h3 rows95_4 rowsOk95_4
  have h5 : ValidThrough v book95 625 := rows_sound h4 rows95_5 rowsOk95_5
  have h6 : ValidThrough v book95 649 := rows_sound h5 rows95_6 rowsOk95_6
  have h7 : ValidThrough v book95 673 := rows_sound h6 rows95_7 rowsOk95_7
  have h8 : ValidThrough v book95 697 := rows_sound h7 rows95_8 rowsOk95_8
  have h9 : ValidThrough v book95 721 := rows_sound h8 rows95_9 rowsOk95_9
  have h10 : ValidThrough v book95 745 := rows_sound h9 rows95_10 rowsOk95_10
  have h11 : ValidThrough v book95 769 := rows_sound h10 rows95_11 rowsOk95_11
  have h12 : ValidThrough v book95 793 := rows_sound h11 rows95_12 rowsOk95_12
  have h13 : ValidThrough v book95 817 := rows_sound h12 rows95_13 rowsOk95_13
  have h14 : ValidThrough v book95 818 := rows_sound h13 rows95_14 rowsOk95_14
  exact book_end h14 _ _ conflict95
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
