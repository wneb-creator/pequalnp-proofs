import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a63 : Array Fact := #[(.res 0 8),(.res 1 8),(.res 2 8),(.res 0 9),(.res 1 9),(.res 2 9),(.res 0 10),(.res 1 10),(.res 2 10),(.res 0 11),(.res 1 11),(.res 2 11),(.lab 3 0 3),(.lab 3 0 6),(.avoid 3 245 0),(.lab 4 0 3),(.lab 4 0 6),(.avoid 4 1102 0),(.lab 6 0 6),(.lab 6 1 6),(.lab 6 2 6),(.lab 6 3 6),(.lab 6 4 6),(.live 8 1),(.lab 8 0 9),(.common 8 9),(.lab 8 0 10),(.common 8 10),(.lab 8 0 11),(.common 8 11),(.lab 8 0 13),(.live 8 2),(.lab 8 1 9),(.lab 8 1 10),(.lab 8 1 11),(.lab 8 1 13),(.live 8 3),(.lab 8 2 9),(.lab 8 2 10),(.lab 8 2 11),(.lab 8 2 13),(.live 8 4),(.lab 8 3 9),(.lab 8 3 10),(.lab 8 3 11),(.lab 8 3 13),(.avoid 8 1548 0),(.avoid 8 1548 1),(.avoid 8 1548 2),(.avoid 8 1548 3),(.avoid 8 1548 4),(.avoid 8 9288 0),(.avoid 8 9288 1),(.avoid 8 9288 2),(.avoid 8 9288 3),(.avoid 8 9288 4),(.avoid 8 10401 0),(.avoid 8 10401 1),(.avoid 8 10401 2),(.avoid 8 10401 3),(.avoid 8 10401 4),(.see 8 0 1290 0),(.see 8 0 1290 1),(.see 8 0 1290 2),(.see 8 0 1290 3),(.see 8 0 1290 4),(.see 8 0 7426 0),(.see 8 0 7426 1),(.see 8 0 7426 2),(.see 8 0 7426 3),(.see 8 0 7426 4),(.see 8 0 9992 0),(.see 8 0 9992 1),(.see 8 0 9992 2),(.see 8 0 9992 3),(.see 8 0 9992 4),(.see 8 2 9992 0),(.see 8 2 9992 1),(.see 8 2 9992 2),(.see 8 2 9992 3),(.see 8 2 9992 4),(.see 8 2 16256 0),(.see 8 2 16256 1),(.see 8 2 16256 2),(.see 8 2 16256 3),(.see 8 2 16256 4),(.diff 0 8 9),(.diff 1 8 9),(.diff 2 8 9),(.diff 0 8 10),(.diff 1 8 10),(.diff 2 8 10),(.diff 0 8 11),(.diff 1 8 11),(.diff 2 8 11),(.live 9 1),(.lab 9 0 7),(.lab 9 0 8),(.common 9 10),(.lab 9 0 11),(.common 9 11),(.lab 9 0 12),(.live 9 2),(.lab 9 1 7),(.lab 9 1 8),(.lab 9 1 11),(.lab 9 1 12),(.live 9 3),(.lab 9 2 7),(.lab 9 2 8),(.lab 9 2 10),(.lab 9 2 11),(.live 9 4),(.lab 9 3 7),(.lab 9 3 8),(.lab 9 3 11),(.avoid 9 432 0),(.avoid 9 432 1),(.avoid 9 432 2),(.avoid 9 432 3),(.avoid 9 432 4),(.avoid 9 2213 0),(.avoid 9 2213 1),(.avoid 9 2213 2),(.avoid 9 2213 3),(.avoid 9 2213 4),(.avoid 9 4309 0),(.avoid 9 4309 1),(.avoid 9 4309 2),(.avoid 9 4309 3),(.avoid 9 4309 4),(.see 9 1 4757 0),(.see 9 1 4757 1),(.see 9 1 4757 2),(.see 9 1 4757 3),(.see 9 1 4757 4),(.see 9 1 5008 0),(.see 9 1 5008 1),(.see 9 1 5008 2),(.see 9 1 5008 3),(.see 9 1 5008 4),(.see 9 1 6789 0),(.see 9 1 6789 1),(.see 9 1 6789 2),(.see 9 1 6789 3),(.see 9 1 6789 4),(.see 9 1 14977 0),(.see 9 1 14977 1),(.see 9 1 14977 2),(.see 9 1 14977 3),(.see 9 1 14977 4),(.see 9 1 16256 0),(.see 9 1 16256 1),(.see 9 1 16256 2),(.see 9 1 16256 3),(.see 9 1 16256 4),(.see 9 5 4757 0),(.see 9 5 4757 1),(.see 9 5 4757 2),(.see 9 5 4757 3),(.see 9 5 4757 4),(.see 9 5 9992 0),(.see 9 5 9992 1),(.see 9 5 9992 2),(.see 9 5 9992 3),(.see 9 5 9992 4),(.diff 0 9 8),(.diff 1 9 8),(.diff 2 9 8),(.diff 0 9 11),(.diff 1 9 11),(.diff 2 9 11),(.lab 10 0 10),(.live 10 1),(.lab 10 0 8),(.lab 10 0 9),(.lab 10 0 11),(.common 10 11),(.lab 10 1 10),(.live 10 2),(.lab 10 1 8),(.lab 10 1 9),(.lab 10 1 11),(.lab 10 2 10),(.live 10 3),(.lab 10 2 8),(.lab 10 2 9),(.lab 10 2 11),(.lab 10 3 10),(.live 10 4),(.lab 10 3 8),(.lab 10 3 9),(.lab 10 3 11),(.lab 10 3 12),(.lab 10 4 8),(.lab 10 4 11),(.avoid 10 2338 0),(.avoid 10 2338 1),(.avoid 10 2338 2),(.avoid 10 2338 3),(.avoid 10 2338 4),(.avoid 10 6789 0),(.avoid 10 6789 1),(.avoid 10 6789 2),(.avoid 10 6789 3),(.avoid 10 6789 4),(.see 10 0 1290 0),(.see 10 0 1290 1),(.see 10 0 1290 2),(.see 10 0 1290 3),(.see 10 0 1290 4),(.see 10 0 7426 0),(.see 10 0 7426 1),(.see 10 0 7426 2),(.see 10 0 7426 3),(.see 10 0 7426 4),(.see 10 0 9992 0),(.see 10 0 9992 1),(.see 10 0 9992 2),(.see 10 0 9992 3),(.see 10 0 9992 4),(.see 10 4 7426 0),(.see 10 4 7426 1),(.see 10 4 7426 2),(.see 10 4 7426 3),(.see 10 4 7426 4),(.see 10 4 16256 0),(.see 10 4 16256 1),(.see 10 4 16256 2),(.see 10 4 16256 3),(.see 10 4 16256 4),(.see 10 5 7174 0),(.see 10 5 7174 1),(.see 10 5 7174 2),(.see 10 5 7174 3),(.see 10 5 7174 4),(.diff 0 10 8),(.diff 1 10 8),(.diff 2 10 8),(.diff 0 10 9),(.diff 1 10 9),(.diff 2 10 9),(.diff 0 10 11),(.diff 1 10 11),(.diff 2 10 11),(.live 11 1),(.lab 11 0 8),(.lab 11 0 10),(.lab 11 0 12),(.live 11 2),(.lab 11 1 8),(.lab 11 1 10),(.lab 11 1 12),(.live 11 3),(.lab 11 2 8),(.lab 11 2 10),(.lab 11 2 12),(.live 11 4),(.lab 11 3 8),(.lab 11 3 10),(.lab 11 3 12),(.avoid 11 1290 0),(.avoid 11 1290 1),(.avoid 11 1290 2),(.avoid 11 1290 3),(.avoid 11 1290 4),(.avoid 11 4370 0),(.avoid 11 4370 1),(.avoid 11 4370 2),(.avoid 11 4370 3),(.avoid 11 4370 4),(.avoid 11 5190 0),(.avoid 11 5190 1),(.avoid 11 5190 2),(.avoid 11 5190 3),(.avoid 11 5190 4),(.see 11 3 7174 0),(.see 11 3 7174 1),(.see 11 3 7174 2),(.see 11 3 7174 3),(.see 11 3 7174 4),(.see 11 3 7426 0),(.see 11 3 7426 1),(.see 11 3 7426 2),(.see 11 3 7426 3),(.see 11 3 7426 4),(.see 11 4 7426 0),(.see 11 4 7426 1),(.see 11 4 7426 2),(.see 11 4 7426 3),(.see 11 4 7426 4),(.diff 0 11 8),(.diff 1 11 8),(.diff 2 11 8),(.diff 0 11 10),(.diff 1 11 10),(.diff 2 11 10),(.reader false 8 0),(.es false 8 3),(.es false 8 6),(.reader false 10 0),(.reader false 11 0),(.es false 11 3),(.es false 11 6),(.reader false 18 0),(.reader false 18 1),(.reader false 18 2),(.reader false 18 3),(.reader false 18 4),(.es false 18 6),(.reader true 8 0),(.reader true 8 1),(.reader true 8 2),(.reader true 8 3),(.reader true 8 4),(.reader true 10 0),(.reader true 10 1),(.reader true 10 2),(.reader true 10 3),(.reader true 10 4),(.es true 10 10),(.reader true 11 0),(.reader true 11 1),(.reader true 11 2),(.reader true 11 3),(.reader true 11 4),(.es true 11 10),(.reader true 18 0),(.reader true 18 1),(.reader true 18 2),(.reader true 18 3),(.reader true 18 4),(.gate 8 11),(.gate 8 18),(.gate 10 11),(.gate 11 18)]
def r63 : List Scheme := [(.self 3 0),(.exposure 3 245),(.avoidNot 3 6 245 0),(.exposure 4 1102),(.avoidNot 4 3 1102 0),(.avoidNot 4 6 1102 0),(.self 6 0),(.self 6 1),(.self 6 2),(.self 6 3),(.self 6 4),(.earlier 8 1),(.earlier 8 2),(.allRes 8 0),(.allRes 8 1),(.allRes 8 2),(.exposure 8 1548),(.avoidNot 8 9 1548 0),(.avoidNot 8 10 1548 0),(.avoidNot 8 9 1548 1),(.avoidNot 8 10 1548 1),(.avoidNot 8 9 1548 2),(.avoidNot 8 10 1548 2),(.avoidLive 8 1548 3),(.avoidNot 8 9 1548 3),(.avoidNot 8 10 1548 3),(.avoidLive 8 1548 4),(.exposure 8 9288),(.avoidNot 8 10 9288 0),(.avoidNot 8 13 9288 0),(.avoidNot 8 10 9288 1),(.avoidNot 8 13 9288 1),(.avoidLive 8 9288 2),(.avoidNot 8 10 9288 2),(.avoidNot 8 13 9288 2),(.avoidLive 8 9288 3),(.avoidNot 8 10 9288 3),(.avoidNot 8 13 9288 3),(.avoidLive 8 9288 4),(.exposure 8 10401),(.avoidNot 8 11 10401 0),(.avoidNot 8 13 10401 0),(.avoidNot 8 11 10401 1),(.avoidNot 8 13 10401 1),(.avoidNot 8 11 10401 2),(.avoidLive 8 10401 3),(.avoidNot 8 11 10401 3),(.avoidNot 8 13 10401 3),(.avoidLive 8 10401 4),(.exactAt 8 0 1290),(.seeLab 8 0 10 1290 0),(.seeLab 8 0 10 1290 1),(.seeLive 8 0 1290 2),(.seeLab 8 0 10 1290 2),(.seeLive 8 0 1290 3),(.seeLive 8 0 1290 4),(.exactAt 8 0 7426),(.seeLab 8 0 10 7426 0),(.seeLab 8 0 11 7426 0),(.seeLab 8 0 10 7426 1),(.seeLab 8 0 11 7426 1),(.seeLive 8 0 7426 2),(.seeLab 8 0 10 7426 2),(.seeLab 8 0 11 7426 2),(.seeLive 8 0 7426 3),(.seeLab 8 0 11 7426 3),(.seeLive 8 0 7426 4),(.exactAt 8 0 9992),(.seeLab 8 0 9 9992 0),(.seeLab 8 0 10 9992 0),(.seeLab 8 0 9 9992 1),(.seeLab 8 0 10 9992 1),(.seeLab 8 0 9 9992 2),(.seeLab 8 0 10 9992 2),(.seeLive 8 0 9992 3),(.seeLab 8 0 9 9992 3),(.seeLab 8 0 10 9992 3),(.seeLive 8 0 9992 4),(.exactAt 8 2 9992),(.seeLab 8 2 10 9992 0),(.seeLab 8 2 13 9992 0),(.seeLab 8 2 10 9992 1),(.seeLab 8 2 13 9992 1),(.seeLive 8 2 9992 2),(.seeLab 8 2 10 9992 2),(.seeLab 8 2 13 9992 2),(.seeLive 8 2 9992 3),(.seeLab 8 2 10 9992 3),(.seeLab 8 2 13 9992 3),(.seeLive 8 2 9992 4),(.exactAt 8 2 16256),(.seeLab 8 2 10 16256 0),(.seeLab 8 2 11 16256 0),(.seeLab 8 2 13 16256 0),(.seeLive 8 2 16256 1),(.seeLab 8 2 10 16256 1),(.seeLab 8 2 11 16256 1),(.seeLab 8 2 13 16256 1),(.seeLive 8 2 16256 2),(.seeLab 8 2 10 16256 2),(.seeLab 8 2 11 16256 2),(.seeLab 8 2 13 16256 2),(.seeLive 8 2 16256 3),(.seeLab 8 2 10 16256 3),(.seeLab 8 2 11 16256 3),(.seeLab 8 2 13 16256 3),(.seeLive 8 2 16256 4),(.diffX 0 8 9),(.diffC 0 8 9),(.resCommon 8 9 0),(.diffX 1 8 9),(.diffC 1 8 9),(.resCommon 8 9 1),(.diffX 2 8 9),(.diffC 2 8 9),(.resCommon 8 9 2),(.residual 8 9 0 1),(.residual 8 9 0 2),(.residual 8 9 0 3),(.residual 8 9 1 2),(.residual 8 9 1 3),(.residual 8 9 2 3),(.diffX 0 8 10),(.diffC 0 8 10),(.diffX 1 8 10),(.diffC 1 8 10),(.diffX 2 8 10),(.diffC 2 8 10),(.adjacentCommon 8 10 0),(.residual 8 10 0 1),(.residual 8 10 0 2),(.residual 8 10 0 3),(.residual 8 10 1 2),(.residual 8 10 1 3),(.residual 8 10 2 3),(.diffX 0 8 11),(.diffC 0 8 11),(.resCommon 8 11 0),(.diffX 1 8 11),(.diffC 1 8 11),(.resCommon 8 11 1),(.diffX 2 8 11),(.diffC 2 8 11),(.resCommon 8 11 2),(.residual 8 11 0 1),(.residual 8 11 0 2),(.residual 8 11 0 3),(.residual 8 11 1 2),(.residual 8 11 1 3),(.residual 8 11 2 3),(.earlier 9 1),(.earlier 9 2),(.someRes 9),(.allRes 9 0),(.allRes 9 1),(.allRes 9 2),(.exposure 9 432),(.avoidNot 9 7 432 0),(.avoidNot 9 8 432 0),(.avoidNot 9 7 432 1),(.avoidNot 9 8 432 1),(.avoidNot 9 7 432 2),(.avoidNot 9 8 432 2),(.avoidLive 9 432 3),(.avoidNot 9 7 432 3),(.avoidNot 9 8 432 3),(.avoidLive 9 432 4),(.exposure 9 2213),(.avoidNot 9 7 2213 0),(.avoidNot 9 11 2213 0),(.avoidNot 9 7 2213 1),(.avoidNot 9 11 2213 1),(.avoidNot 9 7 2213 2),(.avoidNot 9 11 2213 2),(.avoidLive 9 2213 3),(.avoidNot 9 7 2213 3),(.avoidNot 9 11 2213 3),(.avoidLive 9 2213 4),(.exposure 9 4309),(.avoidNot 9 7 4309 0),(.avoidNot 9 12 4309 0),(.avoidNot 9 7 4309 1),(.avoidNot 9 12 4309 1),(.avoidLive 9 4309 2),(.avoidLive 9 4309 3),(.avoidLive 9 4309 4),(.exactAt 9 1 4757),(.seeLab 9 1 7 4757 0),(.seeLab 9 1 7 4757 1),(.seeLive 9 1 4757 2),(.seeLive 9 1 4757 3),(.seeLive 9 1 4757 4),(.exactAt 9 1 5008),(.seeLab 9 1 7 5008 0),(.seeLab 9 1 8 5008 1),(.seeLab 9 1 8 5008 2),(.seeLab 9 1 8 5008 3),(.seeLive 9 1 5008 4),(.exactAt 9 1 6789),(.seeLab 9 1 7 6789 0),(.seeLab 9 1 11 6789 0),(.seeLab 9 1 11 6789 1),(.seeLab 9 1 11 6789 2),(.seeLive 9 1 6789 3),(.seeLab 9 1 7 6789 3),(.seeLive 9 1 6789 4),(.exactAt 9 1 14977),(.seeLab 9 1 7 14977 0),(.seeLab 9 1 11 14977 0),(.seeLab 9 1 7 14977 1),(.seeLab 9 1 11 14977 1),(.seeLab 9 1 7 14977 2),(.seeLab 9 1 11 14977 2),(.seeLive 9 1 14977 3),(.seeLab 9 1 11 14977 3),(.seeLive 9 1 14977 4),(.exactAt 9 1 16256),(.seeLab 9 1 7 16256 0),(.seeLab 9 1 8 16256 0),(.seeLab 9 1 11 16256 0),(.seeLab 9 1 7 16256 1),(.seeLab 9 1 8 16256 1),(.seeLab 9 1 11 16256 1),(.seeLab 9 1 7 16256 2),(.seeLab 9 1 8 16256 2),(.seeLab 9 1 10 16256 2),(.seeLab 9 1 11 16256 2),(.seeLive 9 1 16256 3),(.seeLab 9 1 7 16256 3),(.seeLab 9 1 8 16256 3),(.seeLab 9 1 11 16256 3),(.seeLive 9 1 16256 4),(.exactAt 9 5 4757),(.seeLab 9 5 7 4757 0),(.seeLab 9 5 12 4757 0),(.seeLab 9 5 7 4757 1),(.seeLab 9 5 12 4757 1),(.seeLive 9 5 4757 2),(.seeLive 9 5 4757 3),(.seeLive 9 5 4757 4),(.exactAt 9 5 9992),(.seeLab 9 5 8 9992 0),(.seeLab 9 5 8 9992 1),(.seeLab 9 5 10 9992 2),(.seeLab 9 5 8 9992 3),(.seeLive 9 5 9992 4),(.diffX 0 9 8),(.diffC 0 9 8),(.diffX 1 9 8),(.diffC 1 9 8),(.diffX 2 9 8),(.diffC 2 9 8),(.residual 9 8 0 1),(.residual 9 8 0 2),(.residual 9 8 0 3),(.residual 9 8 1 2),(.residual 9 8 1 3),(.residual 9 8 2 3),(.adjacentCommon 9 10 5),(.diffX 0 9 11),(.diffC 0 9 11),(.resCommon 9 11 0),(.diffX 1 9 11),(.diffC 1 9 11),(.resCommon 9 11 1),(.diffX 2 9 11),(.diffC 2 9 11),(.resCommon 9 11 2),(.residual 9 11 0 1),(.residual 9 11 0 2),(.residual 9 11 0 3),(.residual 9 11 1 2),(.residual 9 11 1 3),(.residual 9 11 2 3),(.self 10 0),(.self 10 1),(.earlier 10 1),(.self 10 2),(.earlier 10 2),(.self 10 3),(.earlier 10 3),(.allRes 10 0),(.allRes 10 1),(.allRes 10 2),(.exposure 10 2338),(.avoidNot 10 8 2338 0),(.avoidNot 10 11 2338 0),(.avoidNot 10 8 2338 1),(.avoidNot 10 11 2338 1),(.avoidLive 10 2338 2),(.avoidNot 10 8 2338 2),(.avoidNot 10 11 2338 2),(.avoidLive 10 2338 3),(.avoidNot 10 8 2338 3),(.avoidNot 10 11 2338 3),(.avoidLive 10 2338 4),(.avoidNot 10 8 2338 4),(.avoidNot 10 11 2338 4),(.exposure 10 6789),(.avoidNot 10 9 6789 0),(.avoidNot 10 11 6789 0),(.avoidNot 10 9 6789 1),(.avoidNot 10 11 6789 1),(.avoidNot 10 9 6789 2),(.avoidNot 10 11 6789 2),(.avoidLive 10 6789 3),(.avoidNot 10 9 6789 3),(.avoidNot 10 11 6789 3),(.avoidNot 10 12 6789 3),(.avoidLive 10 6789 4),(.exactAt 10 0 1290),(.seeLab 10 0 8 1290 0),(.seeLab 10 0 8 1290 1),(.seeLive 10 0 1290 2),(.seeLive 10 0 1290 3),(.seeLive 10 0 1290 4),(.exactAt 10 0 7426),(.seeLab 10 0 8 7426 0),(.seeLab 10 0 11 7426 0),(.seeLab 10 0 8 7426 1),(.seeLab 10 0 11 7426 1),(.seeLive 10 0 7426 2),(.seeLab 10 0 8 7426 2),(.seeLab 10 0 11 7426 2),(.seeLive 10 0 7426 3),(.seeLab 10 0 11 7426 3),(.seeLive 10 0 7426 4),(.exactAt 10 0 9992),(.seeLab 10 0 8 9992 0),(.seeLab 10 0 8 9992 1),(.seeLab 10 0 9 9992 2),(.seeLive 10 0 9992 3),(.seeLive 10 0 9992 4),(.exactAt 10 4 7426),(.seeLab 10 4 8 7426 0),(.seeLab 10 4 11 7426 0),(.seeLab 10 4 8 7426 1),(.seeLab 10 4 11 7426 1),(.seeLive 10 4 7426 2),(.seeLab 10 4 8 7426 2),(.seeLab 10 4 11 7426 2),(.seeLive 10 4 7426 3),(.seeLab 10 4 8 7426 3),(.seeLab 10 4 11 7426 3),(.seeLive 10 4 7426 4),(.seeLab 10 4 8 7426 4),(.seeLab 10 4 11 7426 4),(.exactAt 10 4 16256),(.seeLab 10 4 9 16256 0),(.seeLab 10 4 11 16256 0),(.seeLab 10 4 8 16256 1),(.seeLab 10 4 9 16256 1),(.seeLab 10 4 11 16256 1),(.seeLab 10 4 8 16256 2),(.seeLab 10 4 9 16256 2),(.seeLab 10 4 11 16256 2),(.seeLive 10 4 16256 3),(.seeLab 10 4 8 16256 3),(.seeLab 10 4 9 16256 3),(.seeLab 10 4 11 16256 3),(.seeLive 10 4 16256 4),(.seeLab 10 4 8 16256 4),(.exactAt 10 5 7174),(.seeLab 10 5 11 7174 0),(.seeLab 10 5 11 7174 1),(.seeLab 10 5 11 7174 2),(.seeLab 10 5 12 7174 3),(.seeLive 10 5 7174 4),(.diffX 0 10 8),(.diffC 0 10 8),(.diffX 1 10 8),(.diffC 1 10 8),(.diffX 2 10 8),(.diffC 2 10 8),(.residual 10 8 0 1),(.residual 10 8 0 2),(.residual 10 8 0 3),(.residual 10 8 0 4),(.residual 10 8 1 2),(.residual 10 8 1 3),(.residual 10 8 1 4),(.residual 10 8 2 3),(.residual 10 8 2 4),(.residual 10 8 3 4),(.diffX 0 10 9),(.diffC 0 10 9),(.diffX 1 10 9),(.diffC 1 10 9),(.diffX 2 10 9),(.diffC 2 10 9),(.residual 10 9 0 1),(.residual 10 9 0 2),(.residual 10 9 0 3),(.residual 10 9 1 2),(.residual 10 9 1 3),(.residual 10 9 2 3),(.diffC 0 10 11),(.diffC 1 10 11),(.diffC 2 10 11),(.adjacentCommon 10 11 4),(.residual 10 11 0 1),(.residual 10 11 0 2),(.residual 10 11 0 3),(.residual 10 11 1 2),(.residual 10 11 1 3),(.residual 10 11 2 3),(.earlier 11 1),(.earlier 11 2),(.allRes 11 0),(.allRes 11 1),(.allRes 11 2),(.exposure 11 1290),(.avoidNot 11 8 1290 0),(.avoidNot 11 8 1290 1),(.avoidNot 11 8 1290 2),(.avoidNot 11 10 1290 3),(.avoidLive 11 1290 4),(.exposure 11 4370),(.avoidNot 11 8 4370 0),(.avoidNot 11 12 4370 0),(.avoidNot 11 8 4370 1),(.avoidNot 11 12 4370 1),(.avoidNot 11 8 4370 2),(.avoidNot 11 12 4370 2),(.avoidLive 11 4370 3),(.avoidNot 11 8 4370 3),(.avoidLive 11 4370 4),(.exposure 11 5190),(.avoidNot 11 10 5190 0),(.avoidNot 11 12 5190 0),(.avoidNot 11 10 5190 1),(.avoidNot 11 12 5190 1),(.avoidLive 11 5190 2),(.avoidNot 11 10 5190 2),(.avoidNot 11 12 5190 2),(.avoidLive 11 5190 3),(.avoidNot 11 10 5190 3),(.avoidNot 11 12 5190 3),(.avoidLive 11 5190 4),(.exactAt 11 3 7174),(.seeLab 11 3 10 7174 0),(.seeLab 11 3 12 7174 0),(.seeLab 11 3 10 7174 1),(.seeLab 11 3 12 7174 1),(.seeLive 11 3 7174 2),(.seeLab 11 3 10 7174 2),(.seeLab 11 3 12 7174 2),(.seeLive 11 3 7174 3),(.seeLab 11 3 10 7174 3),(.seeLab 11 3 12 7174 3),(.seeLive 11 3 7174 4),(.exactAt 11 3 7426),(.seeLab 11 3 8 7426 0),(.seeLab 11 3 12 7426 0),(.seeLab 11 3 8 7426 1),(.seeLab 11 3 12 7426 1),(.seeLab 11 3 8 7426 2),(.seeLab 11 3 12 7426 2),(.seeLive 11 3 7426 3),(.seeLab 11 3 8 7426 3),(.seeLive 11 3 7426 4),(.exactAt 11 4 7426),(.seeLab 11 4 8 7426 0),(.seeLab 11 4 8 7426 1),(.seeLab 11 4 8 7426 2),(.seeLab 11 4 10 7426 3),(.seeLive 11 4 7426 4),(.diffX 0 11 8),(.diffC 0 11 8),(.diffX 1 11 8),(.diffC 1 11 8),(.diffX 2 11 8),(.diffC 2 11 8),(.residual 11 8 0 1),(.residual 11 8 0 2),(.residual 11 8 0 3),(.residual 11 8 1 2),(.residual 11 8 1 3),(.residual 11 8 2 3),(.diffX 0 11 10),(.diffC 0 11 10),(.diffX 1 11 10),(.diffC 1 11 10),(.diffX 2 11 10),(.diffC 2 11 10),(.residual 11 10 0 1),(.residual 11 10 0 2),(.residual 11 10 0 3),(.residual 11 10 1 2),(.residual 11 10 1 3),(.residual 11 10 2 3),(.readerAny false 8),(.readerLab false 8 0 3 true),(.readerLab false 8 0 6 false),(.readerAny false 10),(.readerAny false 11),(.readerLab false 11 0 3 false),(.readerLab false 11 0 6 false),(.readerAny false 18),(.readerLab false 18 0 6 true),(.readerLab false 18 1 6 true),(.readerLab false 18 2 6 true),(.readerLab false 18 3 6 true),(.readerLab false 18 4 6 true),(.readerAny true 8),(.readerLive true 8 2),(.readerLive true 8 3),(.readerLive true 8 4),(.readerAny true 10),(.readerLab true 10 0 10 true),(.readerLab true 10 1 10 true),(.readerLab true 10 2 10 true),(.readerLab true 10 3 10 true),(.readerLive true 10 4),(.readerAny true 11),(.readerLab true 11 0 10 false),(.readerLive true 11 2),(.readerLive true 11 3),(.readerLive true 11 4),(.readerAny true 18),(.readerLive true 18 2),(.readerLive true 18 3),(.readerLive true 18 4),(.eqLab false 8 11 3 true),(.gateEq true 8 11 1),(.eqLab false 8 18 6 false),(.gateEq true 8 18 0),(.gateEq false 10 11 0),(.eqLab true 10 11 10 true),(.eqLab false 11 18 6 false),(.gateEq true 11 18 1)]

def table63_0 : List Nat := [0x641,0x741,0x1a0702,0x8c1,0x1e0882,0x200882,0x941,0x9c1,0xa41,0xac1,0xb41,0x2f0f82,0x3f1202,0x11482,0x31482,0x51482]
def table63_1 : List Nat := [0x194631845f1745,0x301702,0x341702,0x401782,0x421782,0x4a1802,0x4c1802,0x491882,0x541882,0x561882,0x531902,0x1bc6d1ac6919c5,0x341982,0x3c1982,0x421a02,0x461a02]
def table63_2 : List Nat := [0x3f1a82,0x4c1a82,0x501a82,0x491b02,0x561b02,0x5a1b02,0x531b82,0x1e4771d4731c45,0x381c02,0x3c1c02,0x441c82,0x461c82,0x4e1d02,0x491d82,0x581d82,0x5a1d82]
def table63_3 : List Nat := [0x531e02,0x20c811fc7d1ec5,0x351e82,0x431f02,0x3f1f82,0x4d1f82,0x492002,0x532082,0x2348b224872145,0x352102,0x382102,0x432182,0x442182,0x3f2202,0x4d2202,0x4e2202]
def table63_4 : List Nat := [0x492282,0x582282,0x532302,0x25c9524c9123c5,0x302382,0x352382,0x402402,0x432402,0x4a2482,0x4d2482,0x492502,0x542502,0x572502,0x532582,0x2849f2749b2645,0x342602]
def table63_5 : List Nat := [0x3d2602,0x422682,0x472682,0x3f2702,0x4c2702,0x512702,0x492782,0x562782,0x5b2782,0x532802,0x2aca929ca528c5,0x342882,0x382882,0x3d2882,0x2f2902,0x422902]
def table63_6 : List Nat := [0x442902,0x472902,0x3f2982,0x4c2982,0x4e2982,0x512982,0x492a02,0x562a02,0x582a02,0x5b2a02,0x532a82,0x12b02,0x62b02,0xcc060003,0x32b82,0x82b82]
def table63_7 : List Nat := [0xcc080083,0x52c02,0xa2c02,0xcc0a0103,0x2c4af2b4410c42e0c87,0x2c4af2b44b0c43e0c87,0x2c4af2b4550c4480c87,0x2c4af2b44b1043e0c87,0x2c4af2b455104480c87,0x2c4af2b45512c480c87,0x12c82,0xc2c82,0x32d02,0xe2d02,0x52d82,0x102d82]
def table63_8 : List Nat := [0xdc1,0x2dcb52cc430d42e0d87,0x2dcb52cc4d0d43e0d87,0x2dcb52cc570d4480d87,0x2dcb52cc4d10c3e0d87,0x2dcb52cc5710c480d87,0x2dcb52cc57134480d87,0x12e02,0x122e02,0xec120003,0x32e82,0x142e82,0xec140083,0x52f02,0x162f02,0xec160103]
def table63_9 : List Nat := [0x2f4bb2e4450e42e0e87,0x2f4bb2e44f0e43e0e87,0x2f4bb2e4590e4480e87,0x2f4bb2e44f1143e0e87,0x2f4bb2e459114480e87,0x2f4bb2e45913c480e87,0xbf3302,0xcd3582,0xb024073304,0x73802,0x93802,0xb3802,0x3c4ef3b4eb3a45,0xc03a02,0xc23a02,0xce3a82]
def table63_10 : List Nat := [0xd03a82,0xd83b02,0xda3b02,0xd73b82,0xe23b82,0xe43b82,0xe13c02,0x3ecf93dcf53cc5,0xc03c82,0xc63c82,0xce3d02,0xd23d02,0xd83d82,0xde3d82,0xd73e02,0xe23e02]
def table63_11 : List Nat := [0xe63e02,0xe13e82,0x41503404ff3f45,0xc03f02,0xca3f02,0xce3f82,0xd43f82,0xcd4002,0xd74082,0xe14102,0x43d0d42d0941c5,0xc14182,0xcf4202,0xcd4282,0xd74302,0xe14382]
def table63_12 : List Nat := [0x46517455134445,0xc14402,0xd04482,0xda4502,0xe44582,0xe14602,0x48d2147d1d46c5,0xc14682,0xc64682,0xd24702,0xde4782,0xd74802,0xe34802,0xe14882,0x4b52b4a5274945,0xc14902]
def table63_13 : List Nat := [0xc64902,0xcf4982,0xd24982,0xd94a02,0xde4a02,0xd74a82,0xe64a82,0xe14b02,0x4dd354cd314bc5,0xc14b82,0xc24b82,0xc64b82,0xcf4c02,0xd04c02,0xd24c02,0xd94c82]
def table63_14 : List Nat := [0xda4c82,0xdc4c82,0xde4c82,0xd74d02,0xe34d02,0xe44d02,0xe64d02,0xe14d82,0x5053f4f53b4e45,0xc04e02,0xcb4e02,0xce4e82,0xd54e82,0xcd4f02,0xd74f82,0xe15002]
def table63_15 : List Nat := [0x52d4951d4550c5,0xc25082,0xd05102,0xdd5182,0xe45202,0xe15282,0x75302,0x5302,0x95382,0x25382,0xb5402,0x45402,0x5454f534d130cbe0c87,0x5454f534db30ccc0c87,0x5454f534e530cd60c87,0x5454f534db344cc0c87]
def table63_16 : List Nat := [0x5454f534e5344d60c87,0x5454f534e536cd60c87,0x3141,0x75482,0x125482,0x324120183,0x95502,0x145502,0x324140203,0xb5582,0x165582,0x324160283,0x55d5554cd331cbe3207,0x55d5554cdf31ccc3207,0x55d5554ce731cd63207,0x55d5554cdf34ccc3207]
def table63_17 : List Nat := [0x55d5554ce734cd63207,0x55d5554ce737cd63207,0x5641,0x5941,0x15b5982,0x5bc1,0x1675c02,0x5e41,0x1715e82,0xd5e82,0xf5e82,0x115e82,0x6458f6358b6245,0x15c6202,0x1606202,0x1686282]
def table63_18 : List Nat := [0x16c6282,0x1676302,0x1726302,0x1766302,0x1716382,0x17c6382,0x1806382,0x17b6402,0x1846402,0x1866402,0x66d9965d9564c5,0x15e6482,0x1606482,0x16a6502,0x16c6502,0x1746582]
def table63_19 : List Nat := [0x1766582,0x1716602,0x17e6602,0x1806602,0x1826602,0x17b6682,0x695a36859f6745,0x15d6702,0x1696782,0x1676802,0x1716882,0x17b6902,0x6bdad6ada969c5,0x15d6982,0x1606982,0x1696a02]
def table63_20 : List Nat := [0x16c6a02,0x1676a82,0x1736a82,0x1766a82,0x1716b02,0x1806b02,0x17b6b82,0x6e5b76d5b36c45,0x15d6c02,0x1696c82,0x1746d02,0x1716d82,0x17b6e02,0x70dc16fdbd6ec5,0x15c6e82,0x1616e82]
def table63_21 : List Nat := [0x1686f02,0x16d6f02,0x1676f82,0x1726f82,0x1776f82,0x1717002,0x17c7002,0x1817002,0x17b7082,0x1847082,0x1877082,0x735cb725c77145,0x15e7102,0x1617102,0x1687182,0x16a7182]
def table63_22 : List Nat := [0x16d7182,0x1727202,0x1747202,0x1777202,0x1717282,0x17c7282,0x17e7282,0x1817282,0x17b7302,0x1847302,0x75dd574dd173c5,0x1607382,0x16c7402,0x1767482,0x1837502,0x17b7582]
def table63_23 : List Nat := [0xd7602,0x7602,0xf7682,0x27682,0x117702,0x47702,0x775db765695755a0d87,0x775db76573575660d87,0x775db7657d575700d87,0x775db765855757a0d87,0x775db765735a5660d87,0x775db7657d5a5700d87,0x775db765855a57a0d87,0x775db7657d5cd700d87,0x775db765855cd7a0d87,0x775db765855f57a0d87]
def table63_24 : List Nat := [0xd7782,0x67782,0xf7802,0x87802,0x117882,0xa7882,0x78de177d6b57d5a3107,0x78de177d7557d663107,0x78de177d7f57d703107,0x78de177d755ad663107,0x78de177d7f5ad703107,0x78de177d7f5d5703107,0x127902,0x147982,0x167a02,0x58c1]
def table63_25 : List Nat := [0x7a5e77956d5855a5887,0x7a5e779577585665887,0x7a5e779581585705887,0x7a5e7795775b5665887,0x7a5e7795815b5705887,0x7a5e7795815dd705887,0x1eb7c82,0x1f37e82,0x138082,0x158082,0x178082,0x84e1183e0d82c5,0x1ec8282,0x1f48302,0x1fc8382,0x2068402]
def table63_26 : List Nat := [0x2038482,0x8761b866178545,0x1ec8502,0x1f08502,0x1f48582,0x1f88582,0x1fc8602,0x2008602,0x1fb8682,0x2048682,0x2038702,0x89e2588e2187c5,0x1ee8782,0x1f08782,0x1f68802,0x1f88802]
def table63_27 : List Nat := [0x1f38882,0x1fe8882,0x2008882,0x1fb8902,0x2068902,0x2088902,0x2038982,0x8c62f8b62b8a45,0x1ee8a02,0x1f18a02,0x1f68a82,0x1f98a82,0x1f38b02,0x1fe8b02,0x2018b02,0x1fb8b82]
def table63_28 : List Nat := [0x2068b82,0x2098b82,0x2038c02,0x8ee398de358cc5,0x1ec8c82,0x1f18c82,0x1f48d02,0x1f98d02,0x1fc8d82,0x2018d82,0x1fb8e02,0x2048e02,0x2038e82,0x916439063f8f45,0x1ec8f02,0x1f48f82]
def table63_29 : List Nat := [0x1fc9002,0x2079082,0x2039102,0x139182,0x9182,0x159202,0x29202,0x179282,0x49282,0x92e4991df57b5ea0e87,0x92e4991dfd7b5f20e87,0x92e4991e057b5fa0e87,0x92e4991dfd7d5f20e87,0x92e4991e057d5fa0e87,0x92e4991e057f5fa0e87,0x139302]
def table63_30 : List Nat := [0xc9302,0x159382,0xe9382,0x179402,0x109402,0x9464f935f77bdea5887,0x9464f935ff7bdf25887,0x9464f936077bdfa5887,0x9464f935ff7ddf25887,0x9464f936077ddfa5887,0x9464f936077fdfa5887,0x94c1,0x954189483,0x9581b9483,0x9641,0x96c1]
def table63_31 : List Nat := [0x9701f9683,0x978219683,0x9a667996639845,0x9ac249803,0x9ac269883,0x9ac289903,0x9ac2a9983,0x9ac2c9a03,0x9d6739c66f9b45,0x1f39c02,0x1fb9c82,0x2039d02,0x9fe7d9ee799dc5,0xa05589d83,0xa05649e03,0xa056e9e83]
def table63_32 : List Nat := [0xa05789f03,0x17b9f82,0xa2e89a1e85a0c5,0xa31efa083,0x1f3a182,0x1fba202,0x203a282,0xa5e95a4e91a3c5,0x1f3a482,0x1fba502,0x203a582,0x97654a603,0xa66849b83,0x9aa57a683,0xa6e8e9b03,0xa765a9603]
def table63_33 : List Nat := [0xa3680a703,0x9aa5fa783,0xa7e90a103,0x681,0x781,0x801,0xb72d4b310c350b86,0xb72d4b3134350f86,0xb72d4b315c351206,0xb72d4b3134430f86,0xb72d4b315c431206,0xb72d4b315c4d1206,0x1dd76dd95a55d5686,0x1dd76dd95cd5d5986,0x1dd76dd95f55d5c06,0x1dd76dd96155d5e86]
def table63_34 : List Nat := [0x1dd76dd95cd695986,0x1dd76dd95f5695c06,0x1dd76dd9615695e86,0x1dd76dd95f5735c06,0x1dd76dd9615735e86,0x1dd76dd96157d5e86,0x1e3785df5ad5f5686,0x1e3785df5d55f5986,0x1e3785df5fd5f5c06,0x1e3785df5d56b5986,0x1e3785df5fd6b5c06,0x1e3785df5fd755c06,0x1e979de55b5615686,0x1e979de55dd615986,0x1e979de5605615c06,0x1e979de55dd6d5986]
def table63_35 : List Nat := [0x1e979de56056d5c06,0x1e979de5605775c06,0x25193e4d7ddef7a86,0x25193e4d7fdef7c86,0x25193e4d81def7e86,0x25193e4d7fdf77c86,0x25193e4d81df77e86,0x25193e4d81dff7e86,0x9541,0x9581,0x9701,0x9781,0x26b9802,0x26b9882,0x26b9902,0x26b9982]
def table63_36 : List Nat := [0x26b9a02,0x2819d82,0x2819e02,0x2819e82,0x2819f02,0xa601,0x2849b82,0x26aa682,0xa741,0x28da002,0x26aa782,0x9ac1,0xa681,0xa781,0x384cd3383,0xe13342]
def table63_37 : List Nat := [0x5e86f2a03,0x5e8531989f1305,0x17a14c661244,0x5e8531983,0x17a20c430d44,0x5e8531a03,0x5e8531a83,0x17a14c2,0x17a6fd8f62d896146,0x8097a5dc3,0x5e98d6e83,0x5e98d6f03,0x5e98d5cc3,0x5e9c96203,0x5e9bb6f5bf5a45,0x635bb6f5bf6258b6107]
def table63_38 : List Nat := [0x2025e82,0x2026358b7004,0x2026358b5804,0x809616383,0x809616b03,0x202705616a04,0x8098d62c3,0x8096d5843,0x1af6a5a759c4,0x2026282,0x8081,0x8481,0x8701,0x8981,0x8c01,0x8e81]
def table63_39 : List Nat := [0x9101,0x9d01,0xa281,0xa581,0x2cca12dcb52649b1b07,0x2cc532dcb51a43426c7,0x2ccb72d4431a85,0xb314cb72d4690d06,0xb320cb72d43510c6,0x14c6926c490fc5,0xb314cb72d4691246,0x2cc532dcb51a45,0xb3284b72d44326c991208,0x284b72d4432cc9b2647,0xb314cb72d44,0x1174630f8312bc322c48]
def table63_40 : List Nat := [0x5454f01ce93583230c7,0x5454f01cd60c9434c87,0x5454f01ce94c4d60c87,0x4008070cc4,0x14f384325454d3bce94c88,0x14f384325454d35d313a48,0x53ce10c951534d74c47,0x14f384325454d35c6,0x53ce10c9513594d4c07,0x14f38432544d601c6,0x53ce10c951358e85347,0x1df735e3785c95c1cb5fc8,0x1df735e378566725cb5d48,0x77d7b78de164d667257072c9,0x1df5ede378593599c95c08,0x1df5ede3785605a58d5c88]
def table63_41 : List Nat := [0x77d7b78de164d665c07,0x1df5ede3785605a46,0x77de35ede1599715807,0x1df78d9b78566665937208,0x77de35ede15997164c7,0x1df78d7b785665c46,0x77de35ede15985,0x5ed676f03,0x1df78d7b7844,0x17b59c2,0x24992e477e83a7f46,0x24992e477e83a8c86,0x24992e477e83a8d06,0x92e47925fa0e85,0x9264b91e1b0e9f28c87,0x9264b91e1b0e9f28d07]
def table63_42 : List Nat := [0x24992e477ec3a7c86,0x27fa042,0x7edf3a103,0x17a6e82,0x5e9bd6303,0x17a5a02,0x5e81,0x6401,0x7081,0x9f81,0x59c1,0xa041,0x56c1,0xa341,0x1fb7cc2,0x765dd76d696385]
def table63_43 : List Nat := [0x6ed8d6fdd9775db5a47,0x18d6fdd96eddd76c6,0x2bc012c432174480c47,0x32b4b10c84823c931888,0x32b4b10c85d120631548,0x32b4b10c85d1208f24c8,0x3004b10c85d1206,0xcb10c8ad1248f1007,0x531243f1084,0xcb10c8ad124412487,0x32c4322b44923c6,0xcb10c8011245,0x32c4320044,0xcb10c8482b48f0c47,0x32c432120ad23c6,0xcb10c8482b45]
def table63_44 : List Nat := [0x24f9464d7ee1f8b06,0x93e51935fb7b85,0x24f9464d7ec4,0x24f9464d8a04,0x24f9464d8a84,0x24f9464d8b04,0x93e519343,0x40024f0ec4,0x544325340753c5,0xc481cc450e8bd2e47,0x755cc83e5554c06,0x755cc83e5554c86,0x1d57320d75545,0x1d57321554b85,0x755cc8555313dcf33e48,0x755cc8555313e06]
def table63_45 : List Nat := [0x1d57321554c45,0x7554c855c4,0x775d976d8d6205,0x775d976d8d5a05,0x1d9775db6344,0x775d976c3,0x92e470e9fb9245,0x24792c3a9244,0x5555732123358f854c7,0x544325340930c5,0x54432534094c85,0x1510c94d0244,0xc040283,0xb554c854cd639c6,0xb554c854cf94c06,0xb554c854cf94c86]
def table63_46 : List Nat := [0x2d55321533585,0x402c080004,0x157020070504,0xe135cd23784,0xcb92f43a124732907,0x32e4bd0e8771cc450f88,0x14c491a4a50fc5,0x14c49294871985,0x32e4bd0e8491186,0x32e4bd0e8492106,0x32e4bd0e8492206,0xcb92f43a1245,0xcb92f43a2185,0xcb92f43a2985,0xcb92f43a2a05,0xcb92f43a2885]
def table63_47 : List Nat := [0xc040203,0xcb91203a2f45,0xb554060484,0xb900cbd0e84,0xc040043,0x30102,0xb0243,0xe135cd23184,0xc062903,0x30182,0x30482,0x302c2,193,0x5381,0x7681,0x9201]
def table63_48 : List Nat := [0x14ad0c8af0f85d0c47,0x14c5d23c401285,0xb12b4322bc4b1886,0x14ad0c8af1748f1007,0xb12b4322bc412506,0x52b4322bc3e1746,0x14ad0c8af0f85,0x530fc2,0x255332157358d231c7,0x954cc855cd63486,0x2553321573585,0x25533215734c5,0x90183,0xec2,578,0xc82]
def table63_49 : List Nat := [1,0x1481,0x2b01,0x2c81,0x2e01,0x1b81,0x1e01,0x2301,0x2801,0x2a81,0xfc1,0xbc1,0x2bc070c83,0xbd050490d08711c6,0x2f4141243421c5,0xbd050490d04]
def table63_50 : List Nat := [0xbd050492984,0xbd050772884,0x2f4141243,0x2f4142903,0x2f4141143,0xa51cc4e0e04,0x2f4141383,0xbd0502,0xaf01c2,0x2be4f0143,0xaf93c2,0x2bc1,513,0x3801,0x5501,0x3341]
def table63_51 : List Nat := [0x140182,0x501,0x9381,0x70102,449,0x7781,0x7881,0x7841,961,0x2d01,0x2dc1,321,0x7701,0x9281,0x7641,833]
def table63_52 : List Nat := [0x9301,0x9441,0x5c1,0x5581,0xec1,0x91c1,0x4c1,0x5481,0x3241,0x3581,0x34c1,0x3781,0x3181]

def encoded63 (i : Nat) : Nat :=
  if i < 416 then
    if i < 208 then
      if i < 96 then
        if i < 48 then
          if i < 16 then
            table63_0.getD (i%16) 0
          else
            if i < 32 then
              table63_1.getD (i%16) 0
            else
              table63_2.getD (i%16) 0
        else
          if i < 64 then
            table63_3.getD (i%16) 0
          else
            if i < 80 then
              table63_4.getD (i%16) 0
            else
              table63_5.getD (i%16) 0
      else
        if i < 144 then
          if i < 112 then
            table63_6.getD (i%16) 0
          else
            if i < 128 then
              table63_7.getD (i%16) 0
            else
              table63_8.getD (i%16) 0
        else
          if i < 176 then
            if i < 160 then
              table63_9.getD (i%16) 0
            else
              table63_10.getD (i%16) 0
          else
            if i < 192 then
              table63_11.getD (i%16) 0
            else
              table63_12.getD (i%16) 0
    else
      if i < 304 then
        if i < 256 then
          if i < 224 then
            table63_13.getD (i%16) 0
          else
            if i < 240 then
              table63_14.getD (i%16) 0
            else
              table63_15.getD (i%16) 0
        else
          if i < 272 then
            table63_16.getD (i%16) 0
          else
            if i < 288 then
              table63_17.getD (i%16) 0
            else
              table63_18.getD (i%16) 0
      else
        if i < 352 then
          if i < 320 then
            table63_19.getD (i%16) 0
          else
            if i < 336 then
              table63_20.getD (i%16) 0
            else
              table63_21.getD (i%16) 0
        else
          if i < 384 then
            if i < 368 then
              table63_22.getD (i%16) 0
            else
              table63_23.getD (i%16) 0
          else
            if i < 400 then
              table63_24.getD (i%16) 0
            else
              table63_25.getD (i%16) 0
  else
    if i < 624 then
      if i < 512 then
        if i < 464 then
          if i < 432 then
            table63_26.getD (i%16) 0
          else
            if i < 448 then
              table63_27.getD (i%16) 0
            else
              table63_28.getD (i%16) 0
        else
          if i < 480 then
            table63_29.getD (i%16) 0
          else
            if i < 496 then
              table63_30.getD (i%16) 0
            else
              table63_31.getD (i%16) 0
      else
        if i < 560 then
          if i < 528 then
            table63_32.getD (i%16) 0
          else
            if i < 544 then
              table63_33.getD (i%16) 0
            else
              table63_34.getD (i%16) 0
        else
          if i < 592 then
            if i < 576 then
              table63_35.getD (i%16) 0
            else
              table63_36.getD (i%16) 0
          else
            if i < 608 then
              table63_37.getD (i%16) 0
            else
              table63_38.getD (i%16) 0
    else
      if i < 736 then
        if i < 672 then
          if i < 640 then
            table63_39.getD (i%16) 0
          else
            if i < 656 then
              table63_40.getD (i%16) 0
            else
              table63_41.getD (i%16) 0
        else
          if i < 704 then
            if i < 688 then
              table63_42.getD (i%16) 0
            else
              table63_43.getD (i%16) 0
          else
            if i < 720 then
              table63_44.getD (i%16) 0
            else
              table63_45.getD (i%16) 0
      else
        if i < 784 then
          if i < 752 then
            table63_46.getD (i%16) 0
          else
            if i < 768 then
              table63_47.getD (i%16) 0
            else
              table63_48.getD (i%16) 0
        else
          if i < 816 then
            if i < 800 then
              table63_49.getD (i%16) 0
            else
              table63_50.getD (i%16) 0
          else
            if i < 832 then
              table63_51.getD (i%16) 0
            else
              table63_52.getD (i%16) 0
def book63 (i : Nat) : Clause := let n := encoded63 i; unpackLits 10 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses63 : inputsOK 3 63 a63 r63 (baseBook book63 531).toList=true := by decide +kernel

def rows63_0 : List Nat := [0x80401,0x180801,0x180a01,0x4010201,0x4010401,0x4010601,0x4010801,0x4010a01,0x4010c01,0x402ec01,0x402ee01,0x402f001,0x402f201,0x402f401,0x402f601,0x402f801,0x402fa01,0x402fc01,0x402fe01,0x8130c01,0x8130e01,0x8131001,0x8131201,0x8131401]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk63_0 : checkRows book63 10 531 rows63_0=true := by decide +kernel

def rows63_1 : List Nat := [0x8131601,0xc7b2001,0xc7b2201,0xc7b2401,0xc7b2601,0xc7b2801,0xc7b2a01,0xc7bca01,0xc7bcc01,0xc7bce01,0xc7bd001,0xc7bd201,0xc7bd401,0xf5bd802,0x426f5bda02,0x428f7be002,0x42af7be202,0x33e601,0x3be801,0x43ea01,0x4bec01,0x53ee01,0x893fa01,0x89bfc01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk63_1 : checkRows book63 10 555 rows63_1=true := by decide +kernel

def rows63_2 : List Nat := [0x8abfe01,0x8bc0001,0x4751c41602,0x122c1801,0x11cc1a01,0x3def741e02,0x12442001,0x11dc2201,0x12047f1f47b1e3e405,0x125c8e01,0x125c9401,0x168741647596a5c9de5b9da5c1dc4b9d40c,0x5b1d0591d2599765d179271dc5f1707697a5b92e5c97e779d813,0x3c0e04212c350c436348ce330f68c8fa8d0fe8d83610,0xbc288b4270c62a0f68c8fa8d0fe8d8b2354a013038280ba0ec2c14,0x2d066310630b86b288ac1b0f68c8fa8d0fe8d86e354a0130640e0ba0e8be17,0xaf0bc30064a40e0f68c8fa8d0fe8dca20c,0x1b068060170b0643da323ea343fa36198620d,0xc6310b42dca83083e0f0f68c8fa8d0fe8d86e354a01343212,0x2f8b632c330b844108403da323ea343fa36354a0130b411,0xa82889e2c4370d43012848118372b4ab298b2130f68c8fa8d0fe8d89c16,0x2b48e29a912a0a72ad124450fc4ab881ab981cba81f2ba5212,0xa72a0ab43b1044691238aca512c23c9024d16c5f18aa8c6330c6b32c73348b230b881ab981cba81f2ba9a21,0x9424a8fa3d0fc3d0e29ea72288b230b881ab981cba81f2ba3813]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk63_2 : checkRows book63 10 579 rows63_2=true := by decide +kernel

def rows63_3 : List Nat := [0x8ea5092a410e44510aa2a82288b230b881ab981cba81f2ba3813,0x8ea3e9424b0ec41124468b230b881ab981cba81f2ba3811,0xb4acaaf2bb0fc3d0e23c8ea288b230b881ab981cba81f2bab613,0x2b2ab44510a30b881ab981cba81f2ba9a0c,0x9329a8e2b2942ae05,0x4b112cbe8fcbd2eac2a9cb92dcb491cb2baae6b881e0701b2ba4a14,0xa1a8116c589ea3c8ea388a28a9322cabaaac6330c6b32c733493a8d3027817,0x9a2d4952d8972da9846118a4c92238b5a588f318cc31accb1ccd24e9aadf302dc19,0x24c92318cc31accb1ccd45c08,0x28aa2318cc31accb1ccd45c08,0x8a29b162a0a027ec6330c6b32c7334ac4c0a7aa40f,0x286a0a7932cc89ea3a8e4c7314c2c6330c6b32c733493a8d3045a14,0xaaaa48b2291629ec6330c6b32c7334ac4c0a8a9a0f,0xa22828b27803,0xa2a889e28717cd09f4ce9fa408fb18cc31accb1ccd28d3046013,0xa2a889e27ca045b17a8491a4490ccd34a8d3031cc6b18cd332cc46215,0x13534001,0x13535401,0x13536c01,0x13538401,0x13539801,0x1353a401,0x1353f601,0x13540c01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk63_3 : checkRows book63 10 603 rows63_3=true := by decide +kernel

def rows63_4 : List Nat := [0x13541401,0xa82c436128481189c06,0xae2b09c2a844108373a04c2c83827c360c,0x421043202,0x48118373b0a33a8381343408,0x1b068060170b0661906207,0xe89c0d8a61004c2c8462b0a009,0xe89c0d8a810c2f3c8ac1184c2c8a33c4ee1b8a00f,0xe89c0d8a8108ae1242f0c0193d0a33c4ee1306e2c8a011,0x2a0af0cc340609c05,0x2a0a6270ad3e43205,0x9e294f00f83d3d86e2ccfa08,0x2a098ea3a0d60d01a0582008,0x5014a511f87f1fa7b14c4b49e4c9380b,0x7a1e479a027f9c2701ec7ac9e4c9e00b,0x1405120080948729c86c502789b5401ec531ce4c93810,0xe63849e4c93004,0x4e1fe509c06f94d2794007,0x501447e1fa6d1b14214c7392d27946719380d,0x6c1fa6c93c4ed0a73c9e719c009,0x13c511f87f93e6e9b9431465312d279380c,0x13c529447e2007f93e6e9b85312d279380c,0x61188619f87f1fa6093c4ed05441ec6292d279800f,0x184621867e1fc7e98a4b49e4f1824e9800c]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk63_4 : checkRows book63 10 627 rows63_4=true := by decide +kernel

def rows63_5 : List Nat := [0x2beae455142b604,0x2b8afc4f14ab604,0xae2c11325c96a5497d18995169aad08a2b60d,0x96a5e99c5515aceb351a9aa5409,0x290a6a8ea8a94905188e2c8aaa969251cb0aa693a98ac2d08f258a4cd09fa7ca329c1a,0x96a649845315ac6b151c9aa5409,0x244a1278a25213427ea32589f51e0a,0x113254ae25eadd18b1a468e2bc8fd229623c93a6ab422892262b225a15,0x96a6114ac6b125405,0x254b025eadd1949a6ab4262b22bb4925c0c,0xb12bf13c4c95d28aed24b22d08a2b60b,0xb32c4afabb1444f1325895d214aa28b42b60d,0x26e8e26c90270a8aa093a7690a72922748b23a0e,0x23948a3ca7a9b4baaa922a490a2d4b24eac23e0e,0x9c2389b23c9ba9ea729aaaa749252ea927290a2c93a76ac23e13,0xd3b86d0b8cd2388d1396d4bb8ed3bccbcdf363920f,0x352d2346edbb2e2b88cb32ed3535363420c,0x344d4b4aecbbae3b8ccb32ed3535363420c,0x33ee6b36e7338e7b3aedbbae5b874e536e8390cf53537cd7383a214,0xd3348d1bb4ecb8ae232d3634209,0xd134cd2bb2ee38ee332d3634209,0x348d134eee3b4e4b90e1d3f4f350e54d937b420e,0x48921c8520bf804,0x40efc425233f504bf30449939ce326c1c0c]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk63_5 : checkRows book63 10 651 rows63_5=true := by decide +kernel

def rows63_6 : List Nat := [0x43b2d29c8b230b881ab981cba81f2ba440c,0x2b2ab2a91244691a448c2e206ae6072ea07caf51a9a10,0x44b2c4bf2eac2a9cb9522a08fae206ae6072ea07caf51a4a12,0xa6aa6912b2ab4411144352d46baae6b881e0701a8b4ae8c4b613,0x15324e01,0x1532b001,0x15340201,0x15353201,0x154d4201,0x15522801,0x155c9201,0x35edbb56dc35901c0551408de360d9b7f02cdd36d5b3937612,0x24a9244202,0x2acaaa9aa8a408e55e8ec395454f564420c,0x23a9343cabaacaaa9aa823f5855153a380c,0xed3f8d60603004,0x8c260f00c8303709a0708608,0x982a3c0f2370340702007,0x2a0a0ee2388c218975a566370342681c060200e,0x98300b0ee3c8922456a22564060dc0d01c358200f,0xa20f06618868190ea090220802c248902188c098dc0d06e2681c0b86c254f218,0xa20f4f202,0xf89c0d89e0e064188675c0682a0423b892240dc1306e2c81c1186c2b0a417,0x882a3a0ee05d700a08e21d735b8dc0d09a0702e2502011]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk63_6 : checkRows book63 10 675 rows63_6=true := by decide +kernel

def rows63_7 : List Nat := [0x3e27036298413f89e0e024228895d0ac1182e3704c2c81c358a414,0x240962308a3a8ec3a024088175b0195d8d63709a0708611,0x23090258e83a8ec3709a07016060860b,0x260c02c3b8f2248915a8235e8dc0d01c060200e,0x982a0c0243a0ea3b08a2257c3703407016060200f,0x35cd946adf37ad9d5d36b5608,0x362d7c6addb74dbd80dc358d9b7f574db373560e,0x35adbb56dd35cdeb631946760b2d5737ed9cdd36b7210,0xd7368d8b5b1946919b72dc32ccbd8536b560d,0xd8b58da35f1ac651b376dd32ccbd8536b560d,0x35cd6368d946b19c6edf37acbd8536b560c,0x362d7358dac6f1b468e0b80dbd8b62587614dd36b5610,0x3bef191247d8c04,0x5124cd0e02,0x17050161284812645060070160604e0b,0x15a54a1e861546f1b8819624b49e4c94e0c,0x5595287a1a561c46fa0658c9e4c94e0b,0x15a55a1a861506d9b26c59765206589ce4b49e4c95c7194e12,0x569565821a8621c541b66ca065892d279336614e0f,0x731566c14f65a06589ce4cd9966a200b,0x1b0889c85815e819ce4cd99669c40a,0x5695288a1c731b165d9e819ce4cd9966d9c0d,0x221651bd685988196006,0x2a6a7c3a8f23b5556206]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk63_7 : checkRows book63 10 699 rows63_7=true := by decide +kernel

def rows63_8 : List Nat := [0x29ca9aaf0f4469324a92238a823f6955153a9a0e,0xa9a9d1043969d595556207,0xab2aaa6a9ca82a90ec4091a456a555544460d,0x15055c01,0x14edac01,0x649946422088a1c581985798c09,0x5014a511f87f1fa5312d27d15439347c1380d,0x80d0870515439347c14a07,0x1405120080948729c86c5b46d5b345511439ce531f04d13812,0x215635a2f0302c0530843076da0eeadaf63bc4b95aaea2e27bd7839b0a391f6babb1533c61c,0x5595a54a2088a1c58db0669368494e0b,0x15a54a1e861546f1b8849624b49e4d94e0c,0x5595287a1a561c46fa1258c9e4d94e0b,0x15a55a1a861506d9b26c5bf6f1cd6edb084962669ce4b49e4d94e14,0x5695686a18541b66c9b16fdbc7195d70208efd8cf23094c30368a1083bab6bd8ef12e56aba8b8aeaec212589ce4b49e4db075314e29,0x21083da202,0x5418c53994569626695c659566498e0b,0x1e8581c04e1d05048076300be2f114180840705a2012611,0x501612049816450600704e08,0xe8b40d8c41004c35046330ba09,0x1f0b41c0ba1c83a0e08435080330c60b,0x1c8b41c0ca1f044108377387972dcd720560f84c210d40704616880330b617,0x320a62d09c2d89e1d072450b23501c2b0cc290c37412211,0xb4488c61f87c1e9143501c330c3740b80c]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk63_8 : checkRows book63 10 723 rows63_8=true := by decide +kernel

def rows63_9 : List Nat := [0x2d1203201649d701e0761c5d5748c3740cc20114210d4070b813,0x2e0d0321204a1262f8781d9143501c05819758b40f,0x1d0824892a1f0c8319142101c065d7760700d,0x160541405e4a928490d2341141801d7584e0d,0x160541705248920490ba2e1141801c058197584e0f,0x1648c2300b577ddd76dd64791cf1d8cf0dc4f0302c0530c20ff3f10e3d5c2c18f83501c84db9530561f,0x1648c2300b577ddd768d40705609,0x21a861b66c5bf6f1c6575c082a08849ce4b49e4ddc610,0x175de201,0x11e473c7633c4c1530c20ff3f10e3d01c3e302efde44c49e4da0d785b9535e618,0x7b8db7a1317849e4ddb87ddb609,0x5b64c1ee7d49e4d8da06,0x5619c539a0549626b95c6a956691a60b,0xa840080360983e3a0c22f0dc0d04c0b846220240e08b5d57e360da3d4fc3f01c3e0e37a8ea1d,0x260a8e83a816310b57c0b60908a225743302f5f8da360dc0d0d4388f53f0fd7a81c3e0201c,0x44910468f53f0fd7a81c3e5e609,0x58cc23c34c5c4c1dec848f4c00f73f0fd7a81c3e5f2efdf5533c814,0x216853c76320cf1306c1530c2df6efdf57cb003dcfc3f5ea3e01d535a216,0x17e1f201,0x17e2e601,0x17e3ac01,0xc02e080260a8e83a8e20d01e058ec0b,0xc886080900a834268262309809,0x300b8f202]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk63_9 : checkRows book63 10 747 rows63_9=true := by decide +kernel

def rows63_10 : List Nat := [0x96250862482c086058088c098e20d09a078f20e,0x96250f002,0xc02e0802823887820900a8ef81889800e20d09a078f011,0x258942188c2408a3a0ea09023828163889a078ec0f,0xf89c0d89e0e064188662b06c11d7029868100181306e2c8a413,0x5419c539a8569ac86a1c589af27db066934831566919e11,0x6c2226f95a5614e6d953841bc5596273db066934831cc11,0x1546714e6a15a6b1a054a1e8821984db083162669ae4b49e4d1a214,0x1546714e6a15a6815287a18831626b92d27934571ab851a212,0x17bdc785e14853af6ba0a44a08efd8cf13054c302ea3c8ba5aab8a0d27934c2ded7fd4d7f21a1d,0x3c2ef91844bc8ba5aab8df97f58c0a,0x217865ec83214ebdaf86ba97fda20a,0x530f030b631f4f0d91710d9831eef22e98381ebadaab8a14ebdaf86ba837b078754d7edff7f3001e,0x187e1d7e0e003,0x18801a01,0x1880d601,0x1880f401,0x18810e01,0x18884c01,0x18886001,0x18888401,0x1888b201,0x1888d401,0x188e0e01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk63_10 : checkRows book63 10 771 rows63_10=true := by decide +kernel

def rows63_11 : List Nat := [0x18d01601,0x591831ed7ee35891f606,0x704887c320a82d09c308a445918200ac3309e2de2f8d6298ce317e07416,0xc01d0b41c0ca1f044108360fe3a4591811880330382de378a6338be2b7e12018,0xb4498be1e0778f0b645918336338d6297e0c80e,0x704987c320c645918200738fe2f8d6297e0780e,0x5416052481222e8b8459198b6378a6357e04e0e,0x7049876300be2d643900738f8cc2005a459198be358a6337e07e14,0x1605017056499204a0c230116466458b6358a6377e04e11,0x320b8341264812845919916478ce358a6377e0b40f,0x178b4138b814058326338b0d209,0x1908d017125928c84591991646156498ce297e0b40f,0x1f0b41c0d0208b81d12a48e4c1e64991e44461178ce2f8a6357e0c615,0x216853c7633c393bc0c0530c10fb3f30a468fc4c20d418e18e49e4cd4d88e277e5a21a,0x1635e4f230ac2530c120c3e8e13f60c3f3039454d7e62389e35893be15,0x5ef71c9f85e148313482a08c1ba74c5aec211e853c8f1d8cf02e16abb0bae52c0e51535ff7f21a1e,0x5e56bb0aec53046b059391883bc4f0e54c0e517fd4d7e3a612,0x1958de01,0x19613401,0x19620c01,0x196c9e01,0x14c5e4c0ba76bbb046304f158cf02e16aaea46bc64764f5365d7f5f97fb0a17,0x5067b6607d91b93dfb7e59008,0x198bc201]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk63_11 : checkRows book63 10 795 rows63_11=true := by decide +kernel

def rows63_12 : List Nat := [0x1419f67b5fb7e59005,0x85a14f1d8cf03014c3043ecfc3f666c2931976655362389e5997da215,0x19a30201,0x58d793c8c2b099965d9a3be08,0x19ad4d9b53003,0x19bb0401,0x19c0fa01,0x189e239ccfc03,0x19d0fc01,0x19daea01,0x19dbb001,0x5fd9e5aa02,0x19f2e001,0x19fbc001,0x665a058c02,0x1a0bc601,0x1a121401,0x677a111e02,0x19edffa25ae03,0x1a2ba601,0x1a320801,0x669a320a02,0x659a3e87a461404,0x659a3e87a461604]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk63_12 : checkRows book63 10 819 rows63_12=true := by decide +kernel

def rows63_13 : List Nat := [0x196e95a4dc603,0x196e95a4dee03]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk63_13 : checkRows book63 10 843 rows63_13=true := by decide +kernel

def lastUnits63 := digits 10 7 0x32ed0f47d232fd2f4c
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict63 : checkReasons book63 845 269 lastUnits63 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude63 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 63=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=3) h hc bp eq (by decide +kernel)
  let v := truth Z a63
  have hbase : ValidThrough v book63 531 := book_start Z h hc z eq _ _ _ _ initialClauses63
  have h0 : ValidThrough v book63 555 := rows_sound hbase rows63_0 rowsOk63_0
  have h1 : ValidThrough v book63 579 := rows_sound h0 rows63_1 rowsOk63_1
  have h2 : ValidThrough v book63 603 := rows_sound h1 rows63_2 rowsOk63_2
  have h3 : ValidThrough v book63 627 := rows_sound h2 rows63_3 rowsOk63_3
  have h4 : ValidThrough v book63 651 := rows_sound h3 rows63_4 rowsOk63_4
  have h5 : ValidThrough v book63 675 := rows_sound h4 rows63_5 rowsOk63_5
  have h6 : ValidThrough v book63 699 := rows_sound h5 rows63_6 rowsOk63_6
  have h7 : ValidThrough v book63 723 := rows_sound h6 rows63_7 rowsOk63_7
  have h8 : ValidThrough v book63 747 := rows_sound h7 rows63_8 rowsOk63_8
  have h9 : ValidThrough v book63 771 := rows_sound h8 rows63_9 rowsOk63_9
  have h10 : ValidThrough v book63 795 := rows_sound h9 rows63_10 rowsOk63_10
  have h11 : ValidThrough v book63 819 := rows_sound h10 rows63_11 rowsOk63_11
  have h12 : ValidThrough v book63 843 := rows_sound h11 rows63_12 rowsOk63_12
  have h13 : ValidThrough v book63 845 := rows_sound h12 rows63_13 rowsOk63_13
  exact book_end h13 _ _ conflict63
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
