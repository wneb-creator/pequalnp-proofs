import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a119 : Array Fact := #[(.res 0 8),(.res 1 8),(.res 2 8),(.res 0 9),(.res 1 9),(.res 2 9),(.res 0 10),(.res 1 10),(.res 2 10),(.res 0 11),(.res 1 11),(.res 2 11),(.live 8 1),(.lab 8 0 9),(.common 8 9),(.lab 8 0 10),(.common 8 10),(.lab 8 0 11),(.common 8 11),(.lab 8 0 13),(.live 8 2),(.lab 8 1 9),(.lab 8 1 10),(.lab 8 1 11),(.live 8 3),(.lab 8 2 9),(.lab 8 2 10),(.lab 8 2 11),(.lab 8 2 13),(.live 8 4),(.lab 8 3 9),(.lab 8 3 10),(.lab 8 3 11),(.lab 8 3 13),(.avoid 8 1548 0),(.avoid 8 1548 1),(.avoid 8 1548 2),(.avoid 8 1548 3),(.avoid 8 1548 4),(.avoid 8 7174 0),(.avoid 8 7174 1),(.avoid 8 7174 2),(.avoid 8 7174 3),(.avoid 8 7174 4),(.avoid 8 7812 0),(.avoid 8 7812 1),(.avoid 8 7812 2),(.avoid 8 7812 3),(.avoid 8 7812 4),(.avoid 8 9288 0),(.avoid 8 9288 1),(.avoid 8 9288 2),(.avoid 8 9288 3),(.avoid 8 9288 4),(.see 8 0 1290 0),(.see 8 0 1290 1),(.see 8 0 1290 2),(.see 8 0 1290 3),(.see 8 0 1290 4),(.see 8 0 7426 0),(.see 8 0 7426 1),(.see 8 0 7426 2),(.see 8 0 7426 3),(.see 8 0 7426 4),(.see 8 0 9992 0),(.see 8 0 9992 1),(.see 8 0 9992 2),(.see 8 0 9992 3),(.see 8 0 9992 4),(.see 8 0 16256 0),(.see 8 0 16256 1),(.see 8 0 16256 2),(.see 8 0 16256 3),(.see 8 0 16256 4),(.see 8 2 9992 0),(.see 8 2 9992 1),(.see 8 2 9992 2),(.see 8 2 9992 3),(.see 8 2 9992 4),(.see 8 2 16256 0),(.see 8 2 16256 1),(.see 8 2 16256 2),(.see 8 2 16256 3),(.see 8 2 16256 4),(.see 8 6 792 0),(.see 8 6 792 1),(.see 8 6 792 2),(.see 8 6 792 3),(.see 8 6 792 4),(.see 8 6 9992 0),(.see 8 6 9992 1),(.see 8 6 9992 2),(.see 8 6 9992 3),(.see 8 6 9992 4),(.see 8 6 16256 0),(.see 8 6 16256 1),(.see 8 6 16256 2),(.see 8 6 16256 3),(.see 8 6 16256 4),(.diff 0 8 9),(.diff 1 8 9),(.diff 2 8 9),(.diff 0 8 10),(.diff 1 8 10),(.diff 2 8 10),(.diff 0 8 11),(.diff 1 8 11),(.diff 2 8 11),(.live 9 1),(.lab 9 0 7),(.lab 9 0 8),(.lab 9 0 10),(.common 9 10),(.lab 9 0 11),(.common 9 11),(.live 9 2),(.lab 9 1 7),(.lab 9 1 8),(.lab 9 1 10),(.lab 9 1 11),(.live 9 3),(.lab 9 2 7),(.lab 9 2 8),(.lab 9 2 10),(.lab 9 2 13),(.live 9 4),(.lab 9 3 7),(.lab 9 3 8),(.lab 9 3 10),(.lab 9 3 11),(.avoid 9 1290 0),(.avoid 9 1290 1),(.avoid 9 1290 2),(.avoid 9 1290 3),(.avoid 9 1290 4),(.avoid 9 2213 0),(.avoid 9 2213 1),(.avoid 9 2213 2),(.avoid 9 2213 3),(.avoid 9 2213 4),(.avoid 9 7174 0),(.avoid 9 7174 1),(.avoid 9 7174 2),(.avoid 9 7174 3),(.avoid 9 7174 4),(.avoid 9 10656 0),(.avoid 9 10656 1),(.avoid 9 10656 2),(.avoid 9 10656 3),(.avoid 9 10656 4),(.see 9 1 4757 0),(.see 9 1 4757 1),(.see 9 1 4757 2),(.see 9 1 4757 3),(.see 9 1 4757 4),(.see 9 1 5008 0),(.see 9 1 5008 1),(.see 9 1 5008 2),(.see 9 1 5008 3),(.see 9 1 5008 4),(.see 9 1 7812 0),(.see 9 1 7812 1),(.see 9 1 7812 2),(.see 9 1 7812 3),(.see 9 1 7812 4),(.see 9 1 16256 0),(.see 9 1 16256 1),(.see 9 1 16256 2),(.see 9 1 16256 3),(.see 9 1 16256 4),(.see 9 5 16256 0),(.see 9 5 16256 1),(.see 9 5 16256 2),(.see 9 5 16256 3),(.see 9 5 16256 4),(.see 9 6 7812 0),(.see 9 6 7812 1),(.see 9 6 7812 2),(.see 9 6 7812 3),(.see 9 6 7812 4),(.diff 0 9 8),(.diff 1 9 8),(.diff 2 9 8),(.diff 0 9 10),(.diff 1 9 10),(.diff 2 9 10),(.live 10 1),(.lab 10 0 8),(.lab 10 0 11),(.common 10 11),(.live 10 2),(.lab 10 1 8),(.lab 10 1 11),(.live 10 3),(.lab 10 2 8),(.lab 10 2 11),(.live 10 4),(.lab 10 3 8),(.lab 10 3 11),(.lab 10 3 12),(.lab 10 4 8),(.lab 10 4 11),(.avoid 10 2338 0),(.avoid 10 2338 1),(.avoid 10 2338 2),(.avoid 10 2338 3),(.avoid 10 2338 4),(.see 10 0 1290 0),(.see 10 0 1290 1),(.see 10 0 1290 2),(.see 10 0 1290 3),(.see 10 0 1290 4),(.see 10 0 7426 0),(.see 10 0 7426 1),(.see 10 0 7426 2),(.see 10 0 7426 3),(.see 10 0 7426 4),(.see 10 4 7426 0),(.see 10 4 7426 1),(.see 10 4 7426 2),(.see 10 4 7426 3),(.see 10 4 7426 4),(.see 10 5 7174 0),(.see 10 5 7174 1),(.see 10 5 7174 2),(.see 10 5 7174 3),(.see 10 5 7174 4),(.see 10 5 16256 0),(.see 10 5 16256 1),(.see 10 5 16256 2),(.see 10 5 16256 3),(.see 10 5 16256 4),(.diff 0 10 8),(.diff 1 10 8),(.diff 2 10 8),(.diff 0 10 11),(.diff 1 10 11),(.diff 2 10 11),(.live 11 1),(.lab 11 0 8),(.lab 11 0 9),(.lab 11 0 10),(.live 11 2),(.lab 11 1 8),(.lab 11 1 9),(.lab 11 1 10),(.lab 11 1 13),(.live 11 3),(.lab 11 2 8),(.lab 11 2 9),(.lab 11 2 10),(.lab 11 2 13),(.live 11 4),(.lab 11 3 8),(.lab 11 3 9),(.lab 11 3 10),(.avoid 11 1290 0),(.avoid 11 1290 1),(.avoid 11 1290 2),(.avoid 11 1290 3),(.avoid 11 1290 4),(.avoid 11 8488 0),(.avoid 11 8488 1),(.avoid 11 8488 2),(.avoid 11 8488 3),(.avoid 11 8488 4),(.avoid 11 9992 0),(.avoid 11 9992 1),(.avoid 11 9992 2),(.avoid 11 9992 3),(.avoid 11 9992 4),(.see 11 4 7174 0),(.see 11 4 7174 1),(.see 11 4 7174 2),(.see 11 4 7174 3),(.see 11 4 7174 4),(.see 11 4 7426 0),(.see 11 4 7426 1),(.see 11 4 7426 2),(.see 11 4 7426 3),(.see 11 4 7426 4),(.see 11 4 7812 0),(.see 11 4 7812 1),(.see 11 4 7812 2),(.see 11 4 7812 3),(.see 11 4 7812 4),(.see 11 4 10656 0),(.see 11 4 10656 1),(.see 11 4 10656 2),(.see 11 4 10656 3),(.see 11 4 10656 4),(.see 11 4 16256 0),(.see 11 4 16256 1),(.see 11 4 16256 2),(.see 11 4 16256 3),(.see 11 4 16256 4),(.see 11 6 2338 0),(.see 11 6 2338 1),(.see 11 6 2338 2),(.see 11 6 2338 3),(.see 11 6 2338 4),(.see 11 6 7426 0),(.see 11 6 7426 1),(.see 11 6 7426 2),(.see 11 6 7426 3),(.see 11 6 7426 4),(.diff 0 11 8),(.diff 1 11 8),(.diff 2 11 8),(.diff 0 11 9),(.diff 1 11 9),(.diff 2 11 9)]
def r119 : List Scheme := [(.earlier 8 1),(.earlier 8 2),(.allRes 8 0),(.allRes 8 1),(.allRes 8 2),(.exposure 8 1548),(.avoidNot 8 9 1548 0),(.avoidNot 8 10 1548 0),(.avoidNot 8 9 1548 1),(.avoidNot 8 10 1548 1),(.avoidLive 8 1548 2),(.avoidNot 8 9 1548 2),(.avoidNot 8 10 1548 2),(.avoidLive 8 1548 3),(.avoidNot 8 9 1548 3),(.avoidNot 8 10 1548 3),(.avoidLive 8 1548 4),(.exposure 8 7174),(.avoidNot 8 10 7174 0),(.avoidNot 8 11 7174 0),(.avoidNot 8 10 7174 1),(.avoidNot 8 11 7174 1),(.avoidLive 8 7174 2),(.avoidNot 8 10 7174 2),(.avoidNot 8 11 7174 2),(.avoidLive 8 7174 3),(.avoidNot 8 10 7174 3),(.avoidNot 8 11 7174 3),(.avoidLive 8 7174 4),(.exposure 8 7812),(.avoidNot 8 10 7812 0),(.avoidNot 8 11 7812 0),(.avoidNot 8 10 7812 1),(.avoidNot 8 11 7812 1),(.avoidNot 8 9 7812 2),(.avoidLive 8 7812 3),(.avoidNot 8 11 7812 3),(.avoidLive 8 7812 4),(.exposure 8 9288),(.avoidNot 8 10 9288 0),(.avoidNot 8 13 9288 0),(.avoidNot 8 10 9288 1),(.avoidNot 8 10 9288 2),(.avoidNot 8 13 9288 2),(.avoidLive 8 9288 3),(.avoidNot 8 13 9288 3),(.avoidLive 8 9288 4),(.exactAt 8 0 1290),(.seeLab 8 0 10 1290 0),(.seeLab 8 0 10 1290 1),(.seeLive 8 0 1290 2),(.seeLab 8 0 10 1290 2),(.seeLive 8 0 1290 3),(.seeLive 8 0 1290 4),(.exactAt 8 0 7426),(.seeLab 8 0 10 7426 0),(.seeLab 8 0 11 7426 0),(.seeLab 8 0 10 7426 1),(.seeLab 8 0 11 7426 1),(.seeLab 8 0 10 7426 2),(.seeLab 8 0 11 7426 2),(.seeLive 8 0 7426 3),(.seeLab 8 0 10 7426 3),(.seeLab 8 0 11 7426 3),(.seeLive 8 0 7426 4),(.exactAt 8 0 9992),(.seeLab 8 0 9 9992 0),(.seeLab 8 0 10 9992 0),(.seeLab 8 0 9 9992 1),(.seeLab 8 0 10 9992 1),(.seeLive 8 0 9992 2),(.seeLab 8 0 9 9992 2),(.seeLab 8 0 10 9992 2),(.seeLive 8 0 9992 3),(.seeLab 8 0 9 9992 3),(.seeLab 8 0 10 9992 3),(.seeLive 8 0 9992 4),(.exactAt 8 0 16256),(.seeLab 8 0 9 16256 0),(.seeLab 8 0 10 16256 0),(.seeLab 8 0 11 16256 0),(.seeLab 8 0 9 16256 1),(.seeLab 8 0 11 16256 1),(.seeLab 8 0 9 16256 2),(.seeLab 8 0 10 16256 2),(.seeLive 8 0 16256 3),(.seeLive 8 0 16256 4),(.exactAt 8 2 9992),(.seeLab 8 2 9 9992 0),(.seeLab 8 2 10 9992 0),(.seeLab 8 2 13 9992 0),(.seeLab 8 2 10 9992 1),(.seeLive 8 2 9992 2),(.seeLab 8 2 10 9992 2),(.seeLab 8 2 13 9992 2),(.seeLive 8 2 9992 3),(.seeLive 8 2 9992 4),(.exactAt 8 2 16256),(.seeLab 8 2 9 16256 0),(.seeLab 8 2 10 16256 0),(.seeLab 8 2 9 16256 1),(.seeLab 8 2 10 16256 1),(.seeLab 8 2 9 16256 2),(.seeLab 8 2 10 16256 2),(.seeLab 8 2 10 16256 3),(.seeLab 8 2 11 16256 3),(.seeLab 8 2 13 16256 3),(.seeLive 8 2 16256 4),(.exactAt 8 6 792),(.seeLab 8 6 9 792 0),(.seeLab 8 6 9 792 1),(.seeLive 8 6 792 2),(.seeLive 8 6 792 3),(.seeLive 8 6 792 4),(.exactAt 8 6 9992),(.seeLab 8 6 9 9992 0),(.seeLab 8 6 10 9992 0),(.seeLab 8 6 9 9992 1),(.seeLab 8 6 10 9992 1),(.seeLab 8 6 9 9992 2),(.seeLab 8 6 10 9992 2),(.seeLive 8 6 9992 3),(.seeLab 8 6 10 9992 3),(.seeLab 8 6 13 9992 3),(.seeLive 8 6 9992 4),(.exactAt 8 6 16256),(.seeLab 8 6 9 16256 0),(.seeLab 8 6 10 16256 0),(.seeLab 8 6 11 16256 0),(.seeLab 8 6 9 16256 1),(.seeLab 8 6 10 16256 1),(.seeLab 8 6 11 16256 1),(.seeLive 8 6 16256 2),(.seeLab 8 6 9 16256 2),(.seeLab 8 6 10 16256 2),(.seeLive 8 6 16256 3),(.seeLab 8 6 10 16256 3),(.seeLab 8 6 11 16256 3),(.seeLive 8 6 16256 4),(.diffX 0 8 9),(.diffC 0 8 9),(.diffX 1 8 9),(.diffC 1 8 9),(.diffX 2 8 9),(.diffC 2 8 9),(.adjacentCommon 8 9 6),(.residual 8 9 0 1),(.residual 8 9 0 2),(.residual 8 9 0 3),(.residual 8 9 1 2),(.residual 8 9 1 3),(.residual 8 9 2 3),(.diffX 0 8 10),(.diffC 0 8 10),(.diffX 1 8 10),(.diffC 1 8 10),(.diffX 2 8 10),(.diffC 2 8 10),(.adjacentCommon 8 10 0),(.residual 8 10 0 1),(.residual 8 10 0 2),(.residual 8 10 0 3),(.residual 8 10 1 2),(.residual 8 10 1 3),(.residual 8 10 2 3),(.diffX 0 8 11),(.diffC 0 8 11),(.diffX 1 8 11),(.diffC 1 8 11),(.diffX 2 8 11),(.diffC 2 8 11),(.adjacentCommon 8 11 6),(.residual 8 11 0 1),(.residual 8 11 0 2),(.residual 8 11 0 3),(.residual 8 11 1 2),(.residual 8 11 1 3),(.residual 8 11 2 3),(.earlier 9 1),(.earlier 9 2),(.allRes 9 0),(.allRes 9 1),(.allRes 9 2),(.exposure 9 1290),(.avoidNot 9 10 1290 0),(.avoidNot 9 8 1290 1),(.avoidNot 9 8 1290 2),(.avoidNot 9 8 1290 3),(.avoidLive 9 1290 4),(.exposure 9 2213),(.avoidNot 9 7 2213 0),(.avoidNot 9 11 2213 0),(.avoidNot 9 7 2213 1),(.avoidNot 9 11 2213 1),(.avoidLive 9 2213 2),(.avoidLive 9 2213 3),(.avoidLive 9 2213 4),(.exposure 9 7174),(.avoidNot 9 10 7174 0),(.avoidNot 9 11 7174 0),(.avoidNot 9 10 7174 1),(.avoidNot 9 11 7174 1),(.avoidNot 9 10 7174 2),(.avoidLive 9 7174 3),(.avoidNot 9 10 7174 3),(.avoidNot 9 11 7174 3),(.avoidLive 9 7174 4),(.exposure 9 10656),(.avoidNot 9 8 10656 0),(.avoidNot 9 7 10656 1),(.avoidNot 9 8 10656 1),(.avoidNot 9 8 10656 2),(.avoidNot 9 13 10656 2),(.avoidLive 9 10656 3),(.avoidNot 9 8 10656 3),(.avoidLive 9 10656 4),(.exactAt 9 1 4757),(.seeLab 9 1 7 4757 0),(.seeLab 9 1 7 4757 1),(.seeLive 9 1 4757 2),(.seeLive 9 1 4757 3),(.seeLive 9 1 4757 4),(.exactAt 9 1 5008),(.seeLab 9 1 7 5008 0),(.seeLab 9 1 8 5008 0),(.seeLab 9 1 7 5008 1),(.seeLab 9 1 8 5008 1),(.seeLab 9 1 7 5008 2),(.seeLab 9 1 8 5008 2),(.seeLive 9 1 5008 3),(.seeLab 9 1 7 5008 3),(.seeLab 9 1 8 5008 3),(.seeLive 9 1 5008 4),(.exactAt 9 1 7812),(.seeLab 9 1 10 7812 0),(.seeLab 9 1 10 7812 1),(.seeLab 9 1 7 7812 2),(.seeLive 9 1 7812 3),(.seeLab 9 1 10 7812 3),(.seeLive 9 1 7812 4),(.exactAt 9 1 16256),(.seeLab 9 1 8 16256 0),(.seeLab 9 1 8 16256 1),(.seeLab 9 1 13 16256 2),(.seeLab 9 1 8 16256 3),(.seeLive 9 1 16256 4),(.exactAt 9 5 16256),(.seeLab 9 5 7 16256 0),(.seeLab 9 5 8 16256 0),(.seeLab 9 5 10 16256 0),(.seeLab 9 5 7 16256 1),(.seeLab 9 5 8 16256 1),(.seeLab 9 5 11 16256 1),(.seeLab 9 5 7 16256 2),(.seeLab 9 5 8 16256 2),(.seeLive 9 5 16256 3),(.seeLab 9 5 7 16256 3),(.seeLab 9 5 8 16256 3),(.seeLive 9 5 16256 4),(.exactAt 9 6 7812),(.seeLab 9 6 7 7812 0),(.seeLab 9 6 10 7812 0),(.seeLab 9 6 11 7812 0),(.seeLab 9 6 7 7812 1),(.seeLab 9 6 10 7812 1),(.seeLab 9 6 11 7812 1),(.seeLive 9 6 7812 2),(.seeLab 9 6 7 7812 2),(.seeLab 9 6 10 7812 2),(.seeLive 9 6 7812 3),(.seeLab 9 6 10 7812 3),(.seeLab 9 6 11 7812 3),(.seeLive 9 6 7812 4),(.diffX 0 9 8),(.diffC 0 9 8),(.diffX 1 9 8),(.diffC 1 9 8),(.diffX 2 9 8),(.diffC 2 9 8),(.residual 9 8 0 1),(.residual 9 8 0 2),(.residual 9 8 0 3),(.residual 9 8 1 2),(.residual 9 8 1 3),(.residual 9 8 2 3),(.diffX 0 9 10),(.diffC 0 9 10),(.diffX 1 9 10),(.diffC 1 9 10),(.diffX 2 9 10),(.diffC 2 9 10),(.adjacentCommon 9 10 5),(.residual 9 10 0 1),(.residual 9 10 0 2),(.residual 9 10 0 3),(.residual 9 10 1 2),(.residual 9 10 1 3),(.residual 9 10 2 3),(.adjacentCommon 9 11 6),(.earlier 10 1),(.earlier 10 2),(.earlier 10 3),(.allRes 10 0),(.allRes 10 1),(.allRes 10 2),(.exposure 10 2338),(.avoidNot 10 8 2338 0),(.avoidNot 10 11 2338 0),(.avoidLive 10 2338 1),(.avoidNot 10 8 2338 1),(.avoidNot 10 11 2338 1),(.avoidLive 10 2338 2),(.avoidNot 10 8 2338 2),(.avoidNot 10 11 2338 2),(.avoidLive 10 2338 3),(.avoidNot 10 8 2338 3),(.avoidNot 10 11 2338 3),(.avoidLive 10 2338 4),(.avoidNot 10 11 2338 4),(.exactAt 10 0 1290),(.seeLab 10 0 8 1290 0),(.seeLive 10 0 1290 1),(.seeLab 10 0 8 1290 1),(.seeLive 10 0 1290 2),(.seeLive 10 0 1290 3),(.seeLive 10 0 1290 4),(.exactAt 10 0 7426),(.seeLab 10 0 8 7426 0),(.seeLab 10 0 11 7426 0),(.seeLive 10 0 7426 1),(.seeLab 10 0 8 7426 1),(.seeLab 10 0 11 7426 1),(.seeLive 10 0 7426 2),(.seeLab 10 0 8 7426 2),(.seeLab 10 0 11 7426 2),(.seeLive 10 0 7426 3),(.seeLab 10 0 11 7426 3),(.seeLab 10 0 12 7426 3),(.seeLive 10 0 7426 4),(.seeLab 10 0 8 7426 4),(.seeLab 10 0 11 7426 4),(.exactAt 10 4 7426),(.seeLab 10 4 8 7426 0),(.seeLab 10 4 11 7426 0),(.seeLab 10 4 8 7426 1),(.seeLab 10 4 11 7426 1),(.seeLive 10 4 7426 2),(.seeLab 10 4 8 7426 2),(.seeLab 10 4 11 7426 2),(.seeLive 10 4 7426 3),(.seeLab 10 4 8 7426 3),(.seeLab 10 4 11 7426 3),(.seeLive 10 4 7426 4),(.exactAt 10 5 7174),(.seeLab 10 5 11 7174 0),(.seeLab 10 5 11 7174 1),(.seeLab 10 5 11 7174 2),(.seeLab 10 5 12 7174 3),(.seeLive 10 5 7174 4),(.seeLab 10 5 11 7174 4),(.exactAt 10 5 16256),(.seeLab 10 5 11 16256 0),(.seeLab 10 5 11 16256 1),(.seeLab 10 5 11 16256 2),(.seeLab 10 5 11 16256 3),(.seeLab 10 5 8 16256 4),(.diffX 0 10 8),(.diffC 0 10 8),(.diffX 1 10 8),(.diffC 1 10 8),(.diffX 2 10 8),(.diffC 2 10 8),(.residual 10 8 0 1),(.residual 10 8 0 2),(.residual 10 8 0 3),(.residual 10 8 1 2),(.residual 10 8 1 3),(.residual 10 8 2 3),(.diffX 0 10 11),(.diffC 0 10 11),(.diffX 1 10 11),(.diffC 1 10 11),(.diffX 2 10 11),(.diffC 2 10 11),(.adjacentCommon 10 11 4),(.residual 10 11 0 1),(.residual 10 11 0 2),(.residual 10 11 0 3),(.residual 10 11 0 4),(.residual 10 11 1 2),(.residual 10 11 1 3),(.residual 10 11 1 4),(.residual 10 11 2 3),(.residual 10 11 2 4),(.residual 10 11 3 4),(.earlier 11 1),(.earlier 11 2),(.allRes 11 0),(.allRes 11 1),(.allRes 11 2),(.exposure 11 1290),(.avoidNot 11 8 1290 0),(.avoidNot 11 10 1290 0),(.avoidNot 11 8 1290 1),(.avoidLive 11 1290 2),(.avoidNot 11 8 1290 2),(.avoidLive 11 1290 3),(.avoidNot 11 8 1290 3),(.avoidNot 11 10 1290 3),(.avoidLive 11 1290 4),(.exposure 11 8488),(.avoidNot 11 8 8488 0),(.avoidNot 11 8 8488 1),(.avoidNot 11 13 8488 1),(.avoidLive 11 8488 2),(.avoidNot 11 8 8488 2),(.avoidNot 11 13 8488 2),(.avoidLive 11 8488 3),(.avoidNot 11 8 8488 3),(.avoidLive 11 8488 4),(.exposure 11 9992),(.avoidNot 11 8 9992 0),(.avoidNot 11 9 9992 0),(.avoidNot 11 10 9992 0),(.avoidNot 11 8 9992 1),(.avoidNot 11 9 9992 1),(.avoidNot 11 10 9992 1),(.avoidNot 11 13 9992 1),(.avoidNot 11 9 9992 2),(.avoidNot 11 10 9992 2),(.avoidLive 11 9992 3),(.avoidNot 11 8 9992 3),(.avoidNot 11 9 9992 3),(.avoidNot 11 10 9992 3),(.avoidLive 11 9992 4),(.exactAt 11 4 7174),(.seeLab 11 4 10 7174 0),(.seeLab 11 4 10 7174 1),(.seeLive 11 4 7174 2),(.seeLive 11 4 7174 3),(.seeLive 11 4 7174 4),(.exactAt 11 4 7426),(.seeLab 11 4 8 7426 0),(.seeLab 11 4 10 7426 0),(.seeLab 11 4 8 7426 1),(.seeLab 11 4 8 7426 2),(.seeLive 11 4 7426 3),(.seeLab 11 4 8 7426 3),(.seeLab 11 4 10 7426 3),(.seeLive 11 4 7426 4),(.exactAt 11 4 7812),(.seeLab 11 4 9 7812 0),(.seeLab 11 4 10 7812 0),(.seeLab 11 4 9 7812 1),(.seeLab 11 4 10 7812 1),(.seeLab 11 4 9 7812 2),(.seeLab 11 4 10 7812 2),(.seeLive 11 4 7812 3),(.seeLab 11 4 9 7812 3),(.seeLive 11 4 7812 4),(.exactAt 11 4 10656),(.seeLab 11 4 8 10656 0),(.seeLab 11 4 8 10656 1),(.seeLab 11 4 13 10656 1),(.seeLive 11 4 10656 2),(.seeLab 11 4 8 10656 2),(.seeLab 11 4 13 10656 2),(.seeLive 11 4 10656 3),(.seeLab 11 4 8 10656 3),(.seeLive 11 4 10656 4),(.exactAt 11 4 16256),(.seeLab 11 4 9 16256 0),(.seeLab 11 4 10 16256 0),(.seeLab 11 4 8 16256 1),(.seeLab 11 4 9 16256 1),(.seeLab 11 4 13 16256 1),(.seeLab 11 4 8 16256 2),(.seeLab 11 4 9 16256 2),(.seeLive 11 4 16256 3),(.seeLab 11 4 10 16256 3),(.seeLive 11 4 16256 4),(.exactAt 11 6 2338),(.seeLab 11 6 8 2338 0),(.seeLab 11 6 8 2338 1),(.seeLab 11 6 8 2338 2),(.seeLive 11 6 2338 3),(.seeLive 11 6 2338 4),(.exactAt 11 6 7426),(.seeLab 11 6 8 7426 0),(.seeLab 11 6 10 7426 0),(.seeLab 11 6 8 7426 1),(.seeLab 11 6 10 7426 1),(.seeLive 11 6 7426 2),(.seeLab 11 6 8 7426 2),(.seeLab 11 6 10 7426 2),(.seeLive 11 6 7426 3),(.seeLab 11 6 8 7426 3),(.seeLive 11 6 7426 4),(.diffX 0 11 8),(.diffC 0 11 8),(.diffX 1 11 8),(.diffC 1 11 8),(.diffX 2 11 8),(.diffC 2 11 8),(.residual 11 8 0 1),(.residual 11 8 0 2),(.residual 11 8 0 3),(.residual 11 8 1 2),(.residual 11 8 1 3),(.residual 11 8 2 3),(.diffX 0 11 9),(.diffC 0 11 9),(.diffX 1 11 9),(.diffC 1 11 9),(.diffX 2 11 9),(.diffC 2 11 9),(.residual 11 9 0 1),(.residual 11 9 0 2),(.residual 11 9 0 3),(.residual 11 9 1 2),(.residual 11 9 1 3),(.residual 11 9 2 3)]

def table119_0 : List Nat := [0x190a02,0x290c02,0x10e82,0x30e82,0x50e82,0x1344b124471145,0x1a1102,0x1e1102,0x2a1182,0x2c1182,0x291202,0x321202,0x341202,0x311282,0x3c1282,0x3e1282]
def table119_1 : List Nat := [0x3b1302,0x15c5514c5113c5,0x1e1382,0x221382,0x2c1402,0x2e1402,0x291482,0x341482,0x361482,0x311502,0x3e1502,0x401502,0x3b1582,0x1845f1745b1645,0x1e1602,0x221602]
def table119_2 : List Nat := [0x2c1682,0x2e1682,0x321702,0x311782,0x401782,0x3b1802,0x1ac6919c6518c5,0x1e1882,0x261882,0x2c1902,0x341982,0x381982,0x311a02,0x421a02,0x3b1a82,0x1d4731c46f1b45]
def table119_3 : List Nat := [0x1f1b02,0x2d1b82,0x291c02,0x351c02,0x311c82,0x3b1d02,0x1fc7d1ec791dc5,0x1f1d82,0x221d82,0x2d1e02,0x2e1e02,0x351e82,0x361e82,0x311f02,0x3f1f02,0x401f02]
def table119_4 : List Nat := [0x3b1f82,0x22487214832045,0x1a2002,0x1f2002,0x2a2082,0x2d2082,0x292102,0x322102,0x352102,0x312182,0x3c2182,0x3f2182,0x3b2202,0x24c9123c8d22c5,0x1a2282,0x1f2282]
def table119_5 : List Nat := [0x222282,0x2a2302,0x2e2302,0x322382,0x352382,0x312402,0x3b2482,0x2749b264972545,0x1a2502,0x1e2502,0x272502,0x2c2582,0x292602,0x342602,0x392602,0x312682]
def table119_6 : List Nat := [0x3b2702,0x29ca528ca127c5,0x1a2782,0x1e2782,0x2a2802,0x2c2802,0x322882,0x342882,0x3e2902,0x402902,0x432902,0x3b2982,0x2c4af2b4ab2a45,0x1b2a02,0x2b2a82,0x292b02]
def table119_7 : List Nat := [0x312b82,0x3b2c02,0x2ecb92dcb52cc5,0x1b2c82,0x1e2c82,0x2b2d02,0x2c2d02,0x332d82,0x342d82,0x312e02,0x3e2e02,0x422e02,0x3b2e82,0x314c3304bf2f45,0x1b2f02,0x1e2f02]
def table119_8 : List Nat := [0x232f02,0x2b2f82,0x2c2f82,0x2f2f82,0x293002,0x333002,0x343002,0x313082,0x3e3082,0x413082,0x3b3102,0x13182,0x63182,0x33202,0x83202,0x53282]
def table119_9 : List Nat := [0xa3282,0x741,0x32cc931c2b06c180707,0x32cc931c3306c280707,0x32cc931c3d06c300707,0x32cc931c330ac280707,0x32cc931c3d0ac300707,0x32cc931c3d0cc300707,0x13302,0xc3302,0x33382,0xe3382,0x53402,0x103402,0x841,0x344cf3342d07c180807]
def table119_10 : List Nat := [0x344cf3343507c280807,0x344cf3343f07c300807,0x344cf334350b4280807,0x344cf3343f0b4300807,0x344cf3343f0d4300807,0x13482,0x123482,0x33502,0x143502,0x53582,0x163582,0x941,0x35cd534c2f08c180907,0x35cd534c3708c280907,0x35cd534c4108c300907,0x35cd534c370bc280907]
def table119_11 : List Nat := [0x35cd534c410bc300907,0x35cd534c410dc300907,0xd93982,0xe73c02,0x73e82,0x93e82,0xb3e82,0x4350b425074145,0xde4102,0xea4182,0xf44202,0xfe4282,0xfb4302,0x45d1544d1143c5,0xda4382,0xe24382]
def table119_12 : List Nat := [0xe84402,0xee4402,0xe74482,0xf14502,0xfb4582,0x4851f4751b4645,0xde4602,0xe24602,0xec4682,0xee4682,0xf64702,0xf14782,0x1004782,0x1024782,0xfb4802,0x4ad2949d2548c5]
def table119_13 : List Nat := [0xdc4882,0xe84902,0xea4902,0xf44982,0xf84982,0xf14a02,0xfe4a02,0xfb4a82,0x4d5334c52f4b45,0xdb4b02,0xe94b82,0xe74c02,0xf14c82,0xfb4d02,0x4fd3d4ed394dc5,0xdb4d82]
def table119_14 : List Nat := [0xdc4d82,0xe94e02,0xea4e02,0xf34e82,0xf44e82,0xf14f02,0xfd4f02,0xfe4f02,0xfb4f82,0x52547515435045,0xde5002,0xec5082,0xf35102,0xf15182,0x1005182,0xfb5202]
def table119_15 : List Nat := [0x54d5153d4d52c5,0xdc5282,0xea5302,0xf95382,0xfe5402,0xfb5482,0x5755b565575545,0xda5502,0xdc5502,0xdf5502,0xe85582,0xea5582,0xee5582,0xf25602,0xf45602,0xf15682]
def table119_16 : List Nat := [0xfc5682,0xfe5682,0xfb5702,0x59d6558d6157c5,0xda5782,0xde5782,0xe35782,0xe85802,0xec5802,0xef5802,0xe75882,0xf25882,0xf65882,0xf15902,0x1005902,0x1035902]
def table119_17 : List Nat := [0xfb5982,0x75a02,0x5a02,0x95a82,0x25a82,0xb5b02,0x45b02,0x5b56b5a4eb374d80707,0x5b56b5a4f5374e60707,0x5b56b5a4ff374f00707,0x5b56b5a4f53ace60707,0x5b56b5a4ff3acf00707,0x5b56b5a4ff3d4f00707,0x75b82,0xc5b82,0x95c02]
def table119_18 : List Nat := [0xe5c02,0xb5c82,0x105c82,0x3841,0x5cd715bced37cd83807,0x5cd715bcf737ce63807,0x5cd715bd0137cf03807,0x5cd715bcf73b4e63807,0x5cd715bd013b4f03807,0x5cd715bd013dcf03807,0x3941,0x1755f02,0x17d6082,0x1836202,0xd6202,0xf6202]
def table119_19 : List Nat := [0x116202,0x6759b665976545,0x1766502,0x1786502,0x1756582,0x17e6582,0x1806582,0x17d6602,0x1846602,0x1866602,0x1836682,0x18a6682,0x18c6682,0x1896702,0x1926702,0x69da568da167c5]
def table119_20 : List Nat := [0x1776782,0x1756802,0x17f6802,0x17d6882,0x1836902,0x1896982,0x6c5af6b5ab6a45,0x1776a02,0x1786a02,0x1756a82,0x17f6a82,0x1806a82,0x17d6b02,0x1856b02,0x1866b02,0x1836b82]
def table119_21 : List Nat := [0x18c6b82,0x18e6b82,0x1896c02,0x1916c02,0x1926c02,0x6edb96ddb56cc5,0x1766c82,0x1796c82,0x17e6d02,0x1816d02,0x17d6d82,0x1846d82,0x1876d82,0x1836e02,0x18a6e02,0x18d6e02]
def table119_22 : List Nat := [0x1896e82,0x715c3705bf6f45,0x1786f02,0x1806f82,0x1867002,0x18f7082,0x1897102,0x1927102,0x73dcd72dc971c5,0x1787182,0x1807202,0x1867282,0x18c7302,0x1907382,0xd7402,0x7402]
def table119_23 : List Nat := [0xf7482,0x27482,0x117502,0x47502,0x755d37457f5dd740807,0x755d3745855dd7c0807,0x755d37458b5dd820807,0x755d3745855fd7c0807,0x755d37458b5fd820807,0x755d37458b615820807,0xd7582,0x127582,0xf7602,0x147602,0x117682,0x167682]
def table119_24 : List Nat := [0x5ec1,0x76dd975d815e5745e87,0x76dd975d875e57c5e87,0x76dd975d8d5e5825e87,0x76dd975d935e5885e87,0x76dd975d876057c5e87,0x76dd975d8d605825e87,0x76dd975d93605885e87,0x76dd975d8d61d825e87,0x76dd975d9361d885e87,0x76dd975d93635885e87,0x1dd7902,0x1e57b82,0x137e02,0x157e02,0x177e02]
def table119_25 : List Nat := [0x82607816038045,0x1de8002,0x1e28002,0x1e68082,0x1e58102,0x1f08102,0x1ef8182,0x1fa8182,0x1fe8182,0x1f98202,0x84e1183e0d82c5,0x1de8282,0x1e68302,0x1ec8302,0x1e58382,0x1f08382]
def table119_26 : List Nat := [0x1f68382,0x1ef8402,0x1fa8402,0x1f98482,0x8761b866178545,0x1de8502,0x1e08502,0x1e28502,0x1e68582,0x1e88582,0x1ea8582,0x1ec8582,0x1f28602,0x1f48602,0x1ef8682,0x1fa8682]
def table119_27 : List Nat := [0x1fc8682,0x1fe8682,0x1f98702,0x89e2588e2187c5,0x1e38782,0x1eb8802,0x1e58882,0x1ef8902,0x1f98982,0x8c62f8b62b8a45,0x1de8a02,0x1e38a02,0x1e68a82,0x1f08b02,0x1ef8b82,0x1fa8b82]
def table119_28 : List Nat := [0x1ff8b82,0x1f98c02,0x8ee398de358cc5,0x1e08c82,0x1e38c82,0x1e88d02,0x1eb8d02,0x1f28d82,0x1f58d82,0x1ef8e02,0x1fc8e02,0x1f98e82,0x916439063f8f45,0x1de8f02,0x1e68f82,0x1ed8f82]
def table119_29 : List Nat := [0x1e59002,0x1f09002,0x1f79002,0x1ef9082,0x1fa9082,0x1f99102,0x93e4d92e4991c5,0x1e09182,0x1e39182,0x1e69202,0x1e89202,0x1ed9202,0x1f09282,0x1f29282,0x1ef9302,0x1ff9302]
def table119_30 : List Nat := [0x1f99382,0x96657956539445,0x1df9402,0x1e79482,0x1f19502,0x1ef9582,0x1f99602,0x98e6197e5d96c5,0x1df9682,0x1e29682,0x1e79702,0x1ea9702,0x1e59782,0x1f19782,0x1f49782,0x1ef9802]
def table119_31 : List Nat := [0x1fb9802,0x1f99882,0x139902,0x9902,0x159982,0x29982,0x179a02,0x49a02,0x9a667995e777ddc0907,0x9a667995f177de40907,0x9a667995fb77dee0907,0x9a667995f179de40907,0x9a667995fb79dee0907,0x9a667995fb7c5ee0907,0x139a82,0x69a82]
def table119_32 : List Nat := [0x159b02,0x89b02,0x179b82,0xa9b82,0x9be6d9ade9785dc3907,0x9be6d9adf3785e43907,0x9be6d9adfd785ee3907,0x9be6d9adf37a5e43907,0x9be6d9adfd7a5ee3907,0x9be6d9adfd7cdee3907,0xcb324c70ac1b0606,0xcb324c70cc1b0a06,0xcb324c70f41b0c06,0xcb324c70cc2b0a06,0xcb324c70f42b0c06,0xcb324c70f4330c06]
def table119_33 : List Nat := [0xd133ccd0b41f0606,0xd133ccd0d41f0a06,0xd133ccd0fc1f0c06,0xd133ccd0d42d0a06,0xd133ccd0fc2d0c06,0xd133ccd0fc350c06,0xd7354d30bc230606,0xd7354d30dc230a06,0xd7354d3104230c06,0xd7354d30dc2f0a06,0xd7354d31042f0c06,0xd7354d3104370c06,0x16d5ad693acdd3606,0x16d5ad693d4dd3986,0x16d5ad693fcdd3c06,0x16d5ad693d4eb3986]
def table119_34 : List Nat := [0x16d5ad693fceb3c06,0x16d5ad693fcf53c06,0x1735c56f3b4df3606,0x1735c56f3dcdf3986,0x1735c56f404df3c06,0x1735c56f3dced3986,0x1735c56f404ed3c06,0x1735c56f404f73c06,0x1d574dd15fd775d06,0x1d574dd1615775f06,0x1d574dd162d776086,0x1d574dd16157f5f06,0x1d574dd162d7f6086,0x1d574dd162d856086,0x1db765d7605795d06,0x1db765d761d795f06]
def table119_35 : List Nat := [0x1db765d7635796086,0x1db765d764d796206,0x1db765d761d815f06,0x1db765d7635816086,0x1db765d764d816206,0x1db765d7635876086,0x1db765d764d876206,0x1db765d764d8d6206,0x26999e6579ddf7706,0x26999e657c5df7906,0x26999e657eddf7b86,0x26999e657c5e77906,0x26999e657ede77b86,0x26999e657edf17b86,0x26f9b66b7a5e17706,0x26f9b66b7cde17906]
def table119_36 : List Nat := [0x26f9b66b7f5e17b86,0x26f9b66b7cde97906,0x26f9b66b7f5e97b86,0x26f9b66b7f5f37b86,0x1db03dd76e58766da56048,0x18966daf65dab6c86,0x76c0f75d876bdab6607,0x76c0f75d8d61c5,0x189619836004,0x76c0f75d9966d816a07,0x76c0f75d8660c5,0x1db03dd76344,0x1db03dd75f1976a06,0x76c0f75d7c6005,0x1db03dd75f04,0x76c0f75c3]
def table119_37 : List Nat := [0x1f97e9f07984,0x16f02d715904,0x5bc0b5c4df455335807,0x5bd735c4df5885,0x16f02d714604,0x5bc0b5c4df5805,0x3ed5e39c3,0x16f02d7137c4,0x16f02d715884,0x5bd735c4ed4785,0x5bc0b5c43,0xcd014cf3084,0xcd014cf07c872d06,0x3340533c9e0fc5,0xcd014cf278912d86,0x3340533c1f2d05]
def table119_38 : List Nat := [0xcd014cf2784,0x3340533c2d07c5,0xcd014cf2804,0x3340533ca20785,0xcd014cf2884,0x3b30c512fc550a46,0xcd014cf07c4,0xcd014cf0b04,0x3b2e4452cc4b0d06,0x3340533c3,0xec31114a90a45,0x3243b32cc70b4310d47,0xec4b2e4340785,0xc932c4d31c4b124330a08,0xc90eccb31c2d0c46,0x324cb29cc70c0a32187]
def table119_39 : List Nat := [0xc932c4d224a731c830c04b0d0a,0x324cb134c70a04b2007,0xc932ca731c302186,0xc932c4d31c302006,0x3243b32cc70b45,0xc932c4d31c302106,0xc932c4d224a731c470c08,0xc932c4d31c4712c280ac8,0x3356d324dd398f50147,0xc90043132c4,0xd7004d50c4330a08f2008,0x35c01354310cc280d47,0xec312dc492085,0x35c01354310cc280ac7,0xd7004d50c4330a06,0x35c01354310cc5]
def table119_40 : List Nat := [0x3b0c449214b32dc6,0xd7004d50c41b1146,0x35c013543106c5,0xd7004d50c44,0x35c01354790bc5,0x35c01354511d85,0xd7004d51e04,0xd7004d50d84,0x35c013543,0x4e6999e607c05,0x139a6679804,0x4e6999e117c60d9007,0x139a6677e9f17986,0x4e6999dfa7c45,0x4e6999de777c5,0x139a6677e84]
def table119_41 : List Nat := [0x4e6999df079c5,0x1f98162d80e2b7786,0x139a6677c04,0x139a6677984,0x14c90043,0xfb580f13704,0xfb580f13d04,0x334053ed6d325603c47,0xcd0156d4fd5d3253955cf03d4a,0xfb4e5574ed593706,0xcd014fb5b4c95806,0x5ad6d5a4dd4f05,0x5ad6d4fd675a5614ecdd5509,0x16b5b55d5a559375554e08,0x16b5b55d5a559375553c08,0x5ad6d4fd5d59d69584f43749]
def table119_42 : List Nat := [0xfb49d3b48d373c46,0x16b5b55d5a559554f04e08,0x16b3ed6d5a5613d06,0x16b5b53f5a4f54dd3b3c08,0x5acfb5b569585374ec7,0x5acfb5b569584dc3c47,0xcd014fb5b4c93706,0x300502c3,0x3c4fb39c3,0x139be6d855ee8ce357cc8,0x4e6f9b615925ee8ce478d49,0x139be6d97e5d77a417b48,0x139be6d85617791ee7a48,0x139be6d855ee8d64978c8,0x4e6f9b65f9761585de47b89,0x139be6d97e5d856177908]
def table119_43 : List Nat := [0x4e6f9b65f975de7b07,0x139be6d97e5d7786,0x9bc137ba6d8585,0x26f04dee9b6158cc6,0x9bc137ba6d8545,0x26f04dee9b44,0x32c13355f05a05,0xfb39c2,0xcb0ecc73244,0x3b0c42c0d04,0x745d36edd56605,0x1d174d9d7559965d7c6148,0x625995f9b75d85,0x625995f9b76285,0x1d174d897557e6dc6,0x745d3625d55f85]
def table119_44 : List Nat := [0x189665a15f44,0x745d37557f6e05,0x1d174d897544,0x256f5cd475885,0x256f5cd1f5785,0x95bd733c44,0x95bd735804,0x256f5cd5f3b45,0xfb5851957d1b3d86,0x95bd733784,0x256f5cc3,0x95a56d3744,0xfb371603d04,0x25695b4f05805,0x95a56d5844,0x25695b43]
def table119_45 : List Nat := [0x7640d76dab6fd826347,0x7640d76dab5f1af6507,0x1d9035db6ad806086,0x1896ad9766daf5e06,0x625a15f43,0x7640d76d7f5e45,0x7640d76dab6b85,0x1d9035db5fc4,0x7640d76d836ac5,0x1d9035db60c4,0x1d9035db6044,0x7640d76c3,0xcb04de4024d50106,0x13792679a44,0x4de4025d9015d10087,0x28137b83]
def table119_46 : List Nat := [0x32c1300de49b05,0x26f04e579b5f179c6,0x26f04e619b65f9746,0x26f9ae1d86de49b6178d88,0x9bc1386e3995e617926d7c49,0x2098c6078bdf07986,0x9be6b8761b7926d8d07,0xa04c037904,0x20989e07895e59706,0x8261389e4598e078462590e61794b,0x13790029b04,0xa04c2,0x26f7926d86e1d855e19ac8,0x1d774c070244,0x625ab6fd786185,0x75c5735804]
def table119_47 : List Nat := [0x5bd715ccdf5905,0x75c57337c4,0x1d715ccf04045,0x75c5734004,0x32cc90043,0x1d735c43,0x1f08461390e457786,0x1d7765db621ab65d7861c8,0x1d7765db621c971dcb6c08,0x75dd976d886ad805e07,0x1d7765db621ab6006,0x75dd976d886ac5,0x9be1d9b5ee9ae1b7f47,0x26f791f98de6d7ba6b86c8,0x9bde47e65e9b5ee9ac7,0x75dd976d816685]
def table119_48 : List Nat := [0x75dd9675db6a85,0x75dd976d816605,0x625995d43,0x75dd9625db6045,0x1d77658976d995e06,0x1d77658976d996186,0x75dd9625db6645,0x1d77658976c4,0x5e437ba6599dde7c07,0x5e43791ee996677787,0xd100ccd0c02c0d46,0xd100ccd0c02c1106,0x34403334300b05,0xd100ccd0c04,0x3334d10b4450d46,0xccd3442d07c5]
def table119_49 : List Nat := [0x3334d10b44,0xccd3443,0x3b0b01e0c44,0x177ba6d9ae1786c6,0x177ba4b9b66b7986,0x175cd8976dee96e4b75c8,0x26f5cdee7584,0x5dee9b66b7cc5,0x5d73625db7b85,0x9be1d86de49b66b9187,0x9be1d93e1b935e49b64b9ac9,0x5cddb9a83,0x26f8763b93e1b8e64d7926b9b4a,0x30042,0x39b02,0x26d05e6b86de49346]
def table119_50 : List Nat := [0x9b4179ae1b7905,0x1f97942,0x9b4179ac3,0xcd335c2c0787b0c87,0x334cd70b01e1ec6,0xcd335c2c0785,0x334cd70b0341006,0xcd335c2c0d05,0xcd335c51104531f07,0x334cd70b04114c6,0xcd335c2c1045,0xec512fc550a45,0x334cd70b04,0xcd335c400d85,0xcd335c370bc5,0xec6f154510a45]
def table119_51 : List Nat := [0x334cd71004,0xcd335c281485,0x334cd70a07d1386,0xcd335c510a05,0x334cd71444,0x37682,0xec291403,0x3b0a42,0xc0b0143,0x304c2,0x996697e66781de67c07,0x1f9779e67e84,0x996697e66781dde7987,0x1f9779f07bc4,0x26505e6999e077786,0x994179a66781c5]
def table119_52 : List Nat := [0x33582,193,0x5a81,0x7481,0x9981,0x1f9799de7c04,0x16d01cf15844,0x5b4073c43,0x16d01d393744,0x5b4075803,0x16d01c2,0x1d50342,0x170102,0x170042,0x5c1,0x7681]
def table119_53 : List Nat := [0x9ac159bdee86c5,0x26b0566f7b84,0x9ac159bc3,0x140902c3,0x166b0283,0x502c2,321,0x5b01,0x7501,0x9a01,449,833,0x9a81,0x5b81,0x765d76203,0x1d77642]
def table119_54 : List Nat := [641,0x5c41,897,0x75c1,0x481,0x7e01,0x7901]

def encoded119 (i : Nat) : Nat :=
  if i < 432 then
    if i < 208 then
      if i < 96 then
        if i < 48 then
          if i < 16 then
            table119_0.getD (i%16) 0
          else
            if i < 32 then
              table119_1.getD (i%16) 0
            else
              table119_2.getD (i%16) 0
        else
          if i < 64 then
            table119_3.getD (i%16) 0
          else
            if i < 80 then
              table119_4.getD (i%16) 0
            else
              table119_5.getD (i%16) 0
      else
        if i < 144 then
          if i < 112 then
            table119_6.getD (i%16) 0
          else
            if i < 128 then
              table119_7.getD (i%16) 0
            else
              table119_8.getD (i%16) 0
        else
          if i < 176 then
            if i < 160 then
              table119_9.getD (i%16) 0
            else
              table119_10.getD (i%16) 0
          else
            if i < 192 then
              table119_11.getD (i%16) 0
            else
              table119_12.getD (i%16) 0
    else
      if i < 320 then
        if i < 256 then
          if i < 224 then
            table119_13.getD (i%16) 0
          else
            if i < 240 then
              table119_14.getD (i%16) 0
            else
              table119_15.getD (i%16) 0
        else
          if i < 288 then
            if i < 272 then
              table119_16.getD (i%16) 0
            else
              table119_17.getD (i%16) 0
          else
            if i < 304 then
              table119_18.getD (i%16) 0
            else
              table119_19.getD (i%16) 0
      else
        if i < 368 then
          if i < 336 then
            table119_20.getD (i%16) 0
          else
            if i < 352 then
              table119_21.getD (i%16) 0
            else
              table119_22.getD (i%16) 0
        else
          if i < 400 then
            if i < 384 then
              table119_23.getD (i%16) 0
            else
              table119_24.getD (i%16) 0
          else
            if i < 416 then
              table119_25.getD (i%16) 0
            else
              table119_26.getD (i%16) 0
  else
    if i < 656 then
      if i < 544 then
        if i < 480 then
          if i < 448 then
            table119_27.getD (i%16) 0
          else
            if i < 464 then
              table119_28.getD (i%16) 0
            else
              table119_29.getD (i%16) 0
        else
          if i < 512 then
            if i < 496 then
              table119_30.getD (i%16) 0
            else
              table119_31.getD (i%16) 0
          else
            if i < 528 then
              table119_32.getD (i%16) 0
            else
              table119_33.getD (i%16) 0
      else
        if i < 592 then
          if i < 560 then
            table119_34.getD (i%16) 0
          else
            if i < 576 then
              table119_35.getD (i%16) 0
            else
              table119_36.getD (i%16) 0
        else
          if i < 624 then
            if i < 608 then
              table119_37.getD (i%16) 0
            else
              table119_38.getD (i%16) 0
          else
            if i < 640 then
              table119_39.getD (i%16) 0
            else
              table119_40.getD (i%16) 0
    else
      if i < 768 then
        if i < 704 then
          if i < 672 then
            table119_41.getD (i%16) 0
          else
            if i < 688 then
              table119_42.getD (i%16) 0
            else
              table119_43.getD (i%16) 0
        else
          if i < 736 then
            if i < 720 then
              table119_44.getD (i%16) 0
            else
              table119_45.getD (i%16) 0
          else
            if i < 752 then
              table119_46.getD (i%16) 0
            else
              table119_47.getD (i%16) 0
      else
        if i < 816 then
          if i < 784 then
            table119_48.getD (i%16) 0
          else
            if i < 800 then
              table119_49.getD (i%16) 0
            else
              table119_50.getD (i%16) 0
        else
          if i < 848 then
            if i < 832 then
              table119_51.getD (i%16) 0
            else
              table119_52.getD (i%16) 0
          else
            if i < 864 then
              table119_53.getD (i%16) 0
            else
              table119_54.getD (i%16) 0
def book119 (i : Nat) : Clause := let n := encoded119 i; unpackLits 10 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses119 : inputsOK 3 119 a119 r119 (baseBook book119 522).toList=true := by decide +kernel

def rows119_0 : List Nat := [0x4892401,0x4892601,0x4892801,0x4892a01,0x4892c01,0x4892e01,0x4f13e01,0x4f14001,0x4f14201,0x4f14401,0x4f14601,0x4f14801,0x5595801,0x5595a01,0x5595c01,0x5595e01,0x5596001,0x5596201,0x48a2e01,0x48a3001,0x48a3201,0x48a3401,0x48a3601,0x48a3801]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk119_0 : checkRows book119 10 522 rows119_0=true := by decide +kernel

def rows119_1 : List Nat := [0x91a4801,0x91a4a01,0x91a4c01,0x91a4e01,0x91a5001,0x91a5201,0x4f2e801,0x4f2ea01,0x4f2ec01,0x4f2ee01,0x4f2f001,0x4f2f201,0xc030201,0xc030401,0xc030601,0xc030801,0xc030a01,0xc030c01,0xc030e01,0xc031001,0xc031201,0xc031401,0x55bf001,0x55bf201]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk119_1 : checkRows book119 10 546 rows119_1=true := by decide +kernel

def rows119_2 : List Nat := [0x55bf401,0x55bf601,0x55bf801,0x55bfa01,0x9540801,0x9540a01,0x9540c01,0x9540e01,0x9541001,0x9541201,0x28498a7e99a80abaaca1a6eaac64acaf89ea8ab025eae26a12,0xa6a62a3266a3aaeab27aa927009,0x290a6c5e9c26ebe2a497a8c08,0xa345ea3a6699263232969b488a7a889d46abe27aa925eafa9813,0x9928c98a969b27aa9272a7274a7a8e0b,0x26317264a428ebe27a97a6808,0x2669ac5ca5292a34932429e9d2f89eaa497a72a726210,0xb2a8cb0ac6a5ac4a446718494b229d23af8a92cc97aa211,0x26317a64a428ebe27a97a7925a720a,0x26317a70a729aa3498a5a6cbe27aa925e9e2a125a6610,0x26aa3262a4266a72731746526a56be27aa925e9e2a125a9412,0x9928c98a969b489252baa22989ba59272a09e4969eaa497a8e13,0xc9372c8378c9b32e0b2edfb2adeb760b,0x651906319b13c4d1221e8721a9099c5b18a0d]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk119_2 : checkRows book119 10 570 rows119_2=true := by decide +kernel

def rows119_3 : List Nat := [0x17c6c17a6d98459183111b484a1083a42621ba5b1b210,0x2188544602,0x6e186599651121081ca68318e632428816d28ca40f,0x6e186599651121090ca407,0x1b45e9b06e1866d984599886e9b28217e831800e,0x1986598a6419511446594ac81cab29a42672205b4a32a44812,0x1dc769d275c4a7621885a14909de5b1d52bc4e0e,0x19865c4c02,0x1b25e9b06e1866d98459c4a6518b2c992609b484a1083a072c20b2bca928a426219c6ea205b17c1e,0x318ce328d30942b0a1124410e4e0d6020c20d,0x20c20220ec3a938260082188c0a,0xfa2210820c22238f03b8e52e0f3090964e0983e114024b6398fc310863190218,0x3e8a24209b088a63c0ee4e0ac450092d8fc3109e3190211,0x24c212e0ec4e00206,0xab08cbc3c0e52f8f52e8e6318c44e0f8020020e,0x681900200420181381a8081885e0a,0x10c420fa3fcc2408ca32138450092dc260c,0x220b0020ac26419043e8fe091380e114024b63390a3303212,0x2b8fc2f8fa2e002410b708cc33190a338cc4e0c0450092d8b013,0x98fa089080b0384510007,0x502b84c2e85508cca2f832410b614829094c24e05c304b63405a350c3324c5300d6020b41c,0x2f8bd0a8561504c2d8524e05c300d0168d430cc9314c035808138b3330ae17,0x3a80a390f0060203e01007,0xa8fa089080b4273403206c29338fe3a02403ccc3d8d4340c3324c5304b64e03835914021061d]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk119_3 : checkRows book119 10 594 rows119_3=true := by decide +kernel

def rows119_4 : List Nat := [0x40d8028de050203881a380dc09,0x1005c1505801350da038841808217890198201a8981888a068682480a16,0xe803cd002,0x100341b0580a04,0x4da2388217886184d8064d63c8921a01a0806a260622286412,0x320c43441d06096250c207,0x400f05086210833788f368ce060000080a0d,0x100580f05416218840000a08,0x107cde250cc03,0x419388840081c04,0x4e1078902388339ce53708a080983581c0c,0x1c0641e2408e00cda06,0x700c05c1d0541a220833a80139ce40080a0d,0x30170541a0000a05,0x4da2408e208893bce33290e2483206cec4102804ce8462230ea284d4d2358980811e020181c,0x4da2408e208893bce3329040a0133a116080980101a0c8924381814,0xc0a00889a0a8a2418ea3e8e4090fc398862114a0e0ac3e114010322a8f2438ee42c2e1b,0xc0a40889a0989c400e63e8e40a1023a88a220833d0a82414a0e0982b0f8450040c8922a8f2438ee42c3221,0x3980a390123a88a220203e01a3c80c0b,0x6d0c8720a8120880a0980c400e63e8e4408ea528200e0803e1140c87a438ee428180b86f364f63c81a0107822,0x98780886c0a872418ec3e8e43f0e60300a044fa1bcd80b8193d94a08038200f845004068321e8f2438ee42c2e23,0x38da2188420cf8230153f0ee2600424cd40d,0x3810218ea208e53e020260f8068923c80a0d,0xec2c0f0701806c178721880004cd40294a0804a1a880068461a07a110da198763c5003988e05cfe0104221]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk119_4 : checkRows book119 10 618 rows119_4=true := by decide +kernel

def rows119_5 : List Nat := [0xfcca0e904100281d0621b05e1b86003d021d8663c5003994a1286a200040c8461a07a438161108f3fc2c22,0x122080a2100d4108e05cfe2481a080980108a0e,0x701e07f0b4330d14a20004000034186c0c,0x300dc2f0c0241c06e5283801003418220c,0x98300dc2d0cc340a0741c94a0e00400003418220f,0x8c300d07e1f06c1e030528382000541d0a0ad094302611,0x1d8221b0261f8370bc3743d0a0ad09430034194a0e0800102e13,0xceb98cd39acdc71283a2cfbe4d1baac6b44ea3e0c5b18f7b9e13,0xd0398cd39acdb9cce4731dd12ea344c63e0f7be4d1baac6ba413,0x336d0472e93a0f9346c6b3408,0xc9366dab20dbbd6db328c63cf1cbd0e6b9945b9cce326f9332dc3aaf8b1b4532ed13a8f6b681d,0xceb98cd39acdbd0e833cf3c76f5518f6be4d1baaf8b1b45344ea39e15,0xc5bcf1c3d0f93e2c6d14f53d809,0xceb98cd39acdd1d283a2cfd1aea344d1baac6b9e0f,0x33ae6334e9b42e6b371e51cf9346eab1b47b3ee8b9e10,0xcc372c8374c8b32e0b8007,0xc9372c837ccb47548b78c9d20deb2af9332e0b1b47b7611,0xd9b24dab20f5b6cca3cf1cbd0e6b9945b9cce326ccb70eabe2c6d14f6b2cd0b6ee9c7b4951ef93681f,0x13b4e93c91647820260d60201209,0x719ec6f1f0701d0811c2839f8849ca7f9fa0d,0x6f9ec6f1fc721d0811c2839f8849ca7f9ee0d,0x17c6c17a6d9853c52d4a9b8619886e9b483982849b210,0x719ec6f1f07020273cf110a284d4d289528599fa0f,0x731ec6f1f0701d08120007]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk119_5 : checkRows book119 10 642 rows119_5=true := by decide +kernel

def rows119_6 : List Nat := [0x1707b16e5ca025dc390f5327f1c85d530591674b9f870a1283a284d4d25e1d0812254a1f21c,0x1ce72c3c02,0x21a8516659438711bc829be7c9ef4da060c,0x7f9647b4387d1c47096607,0x1ed0e2025943c599f606,0x438851f6819ec869ff4f2086f9bd4ed394d9c87f16410,0x689bc679ca6a9ae741c207,0x7b4407d1c470a0205,0x1f673d326f543501f0701a14f9fc721a6742048844010,0x711cf0fc42599bc05,0x12b2150f9c46f21a72d4674221512060b,0x12b1f6819ec869fe81221511f07ea1671d487043e0f,0x14c43f50967529fa71d487c1c07420551534895288a135349f613,0x86cac851670ed4d51534895284723f2d2208a96c8f2284d4d24ca0615,0x1b25e9b0609b484a0e81cac851b6611866e21a621ba8817c12,0xe4348e1352e536120c86ff364e5b1ac635a0d,0x352d8c84efb94eb384eeb8ed6552ff364e5bc0c6b4810,0x358d835520c84e338b553b0e23d2f3be0c63a8e9b98edb9eff364eabe2c6b4ae6b481a,0xd636120c84ff364c6b4807,0x3b0e255402,0x5531fb58d235ef83cef4d5aed38b563fcd93e2c6b8610,0x38ae239120bd2d6b58f3b48f7b92d755cff364e5be2c6b8412,0x342cf31957b56ceb46c6b36d2b340a,0x554e13aee1b8ee347d20b54d4d5ec5ba155bb75834aff396c6b9214]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk119_6 : checkRows book119 10 666 rows119_6=true := by decide +kernel

def rows119_7 : List Nat := [0x394e1b8ee34851f482d5352ff396c6b16c63840e,0x480d23aed655554bfcd931ae2bb556564c63600e,0xd83592047ee1d66ff364c6b19593480b,0xe538ee2b892047f1f34ed3568ff396c6b16c63840f,0x4ed3a4f246beb493ee548d62602144004462248881210,0x59d5001,0x4da2408e208893bce33290e2483206cec049040a4e8080983581814,0x140ae130ba1505c300582f8522d8b40b,0xaf2baaaab0ab2b915c529ca709bc5a0b,0x9da7498a6514c5a05,0x9e2aa98aac9927ab026aac2be09,0x99aaa98abc9da7ab026aac2ae09,0x99aaa98aba9d4555ed789ed74b026aac2ae0d,0xadab55f26a9ed74b057607,0x26caaa62ab264a027eaea889d2b4a1a589ea8ab02b210,0x2bcaec5802,0x9da7498a6cacaab60aac992b71445695d80a157f5d27ab045813,0x759d5129d929a1885a3e77d6e5a9d20b,0x1946418f11c448320a8f99c5956e5a98a0c,0x6319464c4512a128420762586869da65a3e672205956e5a98a13,0x6319464c4512cb284a108f99c5956e5a98a0d,0x21c8644d12a3e8856e5ad8b632060a,0x66a0662a186519c8821e07,0x586871dd13d906458e8298c8fa205ad8b632060e]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk119_7 : checkRows book119 10 690 rows119_7=true := by decide +kernel

def rows119_8 : List Nat := [0x16221c6644929d936358a8fa205aa060b,0x1bf4f1bd4b1c54f9fc724394dc3a899d0812205956e5a9ee12,0x1fc721c2839f884d3206,0x7ea0271c4351d987e212899d08116a701f1659ec0f,0x1fa809f671c430fd4952d4489a055b96a701f1659ec10,0x52b675965ad9a04,0xa8ac2a32c4a42c8a74611aaf4a92cc972ca0d,0x28d17a8e99a64bd2a49729c08,0xa345ea6a729c26368aa09e5a0962f49eaa49726cb1a9011,0x9c28c98a9099a7aa929a07,0x9bd8001,0x12445d17af4a52576a284975a409,0x466a829ebd5a404,0x98da49b4649c29ca6a8d6b29099dab6a294a12f49eaa49727413,0x49095ab8ad2ab22da6bd2c09726aac5ae9d29eaec5c10,0x2729ba6299c5ca5a936c274bd27a9726b6bc640e,0x27299a791945d19af49ea5c9adae95a596ca620e,0xa5db56cda403,0x149bea46d70011195b22488d9efba2cf94760d,0x149d24f947603,0x2e497a444dd9534a3c4cdb6bfbed6ebeab8d840e,0x2fd655b68e932464d35c13446dbcb7d10548096e2fa544030056ac612101a4418,0x2fc4ca4534d956e2fb00c004d14e8e9195c11a01db610,0x562f0bd4f1bccc6bc8f6bc408]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk119_8 : checkRows book119 10 714 rows119_8=true := by decide +kernel

def rows119_9 : List Nat := [0x562f3be2c6bd004,0xd335b1fb90e3b4805,0xd634f1fb88e1b8571b8cf5dc4d45c2f6bfcd9396c6b4811,0xc9372c8378c9b2adeb7607,0x34cd63551f482e338ac5b4808,0x358d4b4f1fc7ce2386e15cce43dd713d572dc97031648406ff332d9382e5b1acb35cdf392f2bdf6fb4820,0xc9366c836ac9bd6f5328db36809,0xceb98cd39acdbd0f3dd0f63a0cf39e0b,0x16f510be95100c00fb954fb5bafaade0b,0x358d4b4f1fc7ce2386e1390f75c4f55cb735c9755cec5dd2f7bcae9b92df36ed7342cb5bef8baae5b82dc364d1b32ff31b01b4828,0xd63531fc7cc5b4805,0x1324dadd27d84bf2e4982448b59567a228ecd20e,0xa8ac2a32c8a72a4b3290b12ca09,0x6319464c4512cb284a108e99c5956e5a18a0d,0x21c86c4802,0x661966298e832077819464447114a68e99c881655b96977c4813,0x6444f131688edde6320b78d9009,0x74c4a7621885a06871dc8e9de8856e5a5de7520b789d611,0x1160157002,0x74c4a7621885a06869db7920a755e778dde8e9de8856e5a1d613,0xceb98cd39acdb3ee8b9e07,0x270a3262a8278aa27d1ac6c96a66a429a0c,0xb446eb6aa8a9ad805,0xb3acb1baa2a828d7c2d6b229d7bad2b12909b2c6b52c211]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk119_9 : checkRows book119 10 738 rows119_9=true := by decide +kernel

def rows119_10 : List Nat := [0x264a3262a7272a8278aa27d17c6118df29b25896a8e10,0x29ca42a8a84651746919df495a5896a8c0c,0x358d335321c812134806,0x176388e1b84e55f973364e5b4e09,0xebbb4efc8121362d85faf03b8f6b90f73ac0d,0x2789d46602,0x2729ba637fa671726aa5a94a4c640a,0x2729bc6402,0x28295d8002,0x2a0a7a8ca74656a2849aa62a42671760580dfea96009ec6612,0x2789d263772678027a9b2c781c6a0a,0x264a3262a827918490a72a58027a9b6078228e0e,0xaaa84aed809645eae60aabe08b02b00b,0xa829ea329117a9a9ca709be0d8027aa946a0d,0x39cd13997b3a2fb346eab1ee6c780a,0xe9334e6344e73391ec778439acdbecd1baac7b400f,0x163900a3a00e3d01f08c2a4d0203e006008123b0ee10,0x3ec243f00e03134450064110d851100b,0x168c2130c613c240780b858ce15019850ca148124d020170d6018d415,0xf4078e803c290842786000008064d4d00c,0x214d420c26241342600624e1a228da0b,0x17c20181341a8061a61a188640a,0x13600f87806068f386e1c07,0x562b84c2c84f08ccb5c9042d8520a620438be1603386934170c0018bc16]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk119_10 : checkRows book119 10 762 rows119_10=true := by decide +kernel

def rows119_11 : List Nat := [0x158ae130be1605c300522d84e2c8bc0b,0x17ec04d931ec65c605,0xebbbf20362d8626ecb51013c0c7bac0b,0xd4b8f89dfad7be0f3bd58a5fcffdeb00240bec9f83c04f8b1ec648215,0x16556a8f2f6bd40205,0x352d848321c04c662606,0x3b4ec3bf213d2d8b618adfaeeb8f8bbff7ac00902fb27e0f8b319013c0c7bac18,0x1763b0ebb4e03,0x34cd63571f482edbb4eb632c5b480a,0x127deabdbfeff24005,0x5c6e1b531fc82eee357338408,0x16dd94bec03006398ddd2f7bbce9b92dbb5cd0b2d8c2fc9813b88be2f03aae5b70d9346cca430131e481557a5104c11a53a3c27,0x2fd7adb6461335c4d24822c8ad9e8fafb00c000191a4d2258ea4414,0xeeb938d63901364e5bc0c7e2e09,0x5fb8bbbd8fb1f0138e06,0xf7ba6dbb42cb318ccb46dc3aaf8dd20b,0xebbb4eebbf204858bb62d835d90404f0642c7bac0f,0x1d0710d4301f0480783a028440594e0804a200121000e0f6240186c15,0x1d0710cc2e0c0220d87c448f43e8e4428ef9194e0e0803e1140a0ec410243a0fe00e240186c1d,0xc30d8ce1e077926243194e35806328d20c,0x1e0750bc2c098221f83653838200281be4a0b80000d720186c13,0xd06c088781d0270dc350c64d5c82e53838200060a06f9287c13,0x260d4301f07a538380182208,0x9cca088330d0741b65053838200060a1041be4a1de4e44c2c14]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk119_11 : checkRows book119 10 786 rows119_11=true := by decide +kernel

def rows119_12 : List Nat := [0x741ec330d8300b652538800186f928779386c0e,0x4ca0090e02,0x98310b432006561d06c1f837950779386f929040a14e0e0800182215,0x10e420020042c4182a088fe090701b86c1e030538382011401873960361f8fa18,0x603e85e438684206400c324194e1a91401863960fe10,0x905e088681902c008381a86009,0xb86c0887009c2f9782b9765a1f8365383820006188739607613,0x1c07b0bc361d8300b94e200061ce599806c0d,0x6d0b86e098245388001873960780a,0x781c4370c03208e659466253838200061ce599806c10,0x65e00e66018639603206,0x3ec2c3f8701b86c1e07b974344182a448739a66196152b9d84b82417a94cffbfd9125c4ce229113abfafc5388045006b7e3b8f1082a,0x603e85e418620a8281a914191081a10e008fe0e,0x18ccb97e6c438320090407,0x17ac9e462f55c54e4780646e6a90a400b,0xb82609013b2d6228f1336dafafa5bafbae79c64375b1ab7e3b9ad8415,0x37d48ca172b7acab32e0b26de4740a,0xd0398cd3a8d1346eab36e6b38e73a40b,0x340e6334e9b431ee779d39cce346eab36e6ba40e,0x3a6d0b46eadec04,0x11e6139ec779e642c7ba807,0x4731c67cc5e42c7e7406,0xdeb78dd3811ec791d330cbb2d9fbe8bee0e982458db839131efb95454be78ee3d9aaf79cb721d,0x1e0701ee5d0b4341c82b9666998680536720066e2014e0186c13]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk119_12 : checkRows book119 10 810 rows119_12=true := by decide +kernel

def rows119_13 : List Nat := [0x1a0a2801,0x1a0ae201,0x1a0bea01,0x37acab26de52204,0x54b512235b969a143a06,0x14b52ba32235b969a143a07,0x1bf4f1bc7f1c94dc3a889d08156e5a68fa11ee0e,0x7ea0271c4351d987c1c1a41f870a1283a22742045a68fa11ec13,0x6a1e0679e86b1e4691e2684430fc3b51693a3d6e7a9ae88969a11e615,0xb725da1d8403,0x2fc982456523da5afb00c01913ffa52e68b2f76ebed90b1fa260e14,0x3ff005da5411d44528bddbafb642c7953a6687a264410,0x1a2c751eb2ecb67ef9e9afb31fa24780b,0x1a72fe01,0x48371b8f7ec00d9642c735208,0xeebaeed3bf21c8121362d86a1003c0c73ac0d,0x3bce4b5da8c00d9396f0642c76380a,0x4d93127a24bd59f53a2ba7cd209,0x1324ddb727afabdea575c07a7cd20a,0x4611da56a68a80847d7007,0x69734ae44da4527e36bdea975eaba79320c,0x1ab22c01,0x1ab2e601,0x1ab3ee01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk119_13 : checkRows book119 10 834 rows119_13=true := by decide +kernel

def rows119_14 : List Nat := [0x1abe9401,0x1ac69601,0x1ad3fe01,0x1ada3c01,0x11a600a5df7a7a7c05,0x60fa7ebc02,0x2fabdea575c07ae6be06,0x6bbb04b402,0x1b0a4001,0x69fb149e02,0x1b1af601,0x1b231a01,0x1a26b3b25ba03]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk119_14 : checkRows book119 10 858 rows119_14=true := by decide +kernel

def lastUnits119 := digits 10 2 0xd9766
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict119 : checkReasons book119 871 801 lastUnits119 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude119 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 119=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=3) h hc bp eq (by decide +kernel)
  let v := truth Z a119
  have hbase : ValidThrough v book119 522 := book_start Z h hc z eq _ _ _ _ initialClauses119
  have h0 : ValidThrough v book119 546 := rows_sound hbase rows119_0 rowsOk119_0
  have h1 : ValidThrough v book119 570 := rows_sound h0 rows119_1 rowsOk119_1
  have h2 : ValidThrough v book119 594 := rows_sound h1 rows119_2 rowsOk119_2
  have h3 : ValidThrough v book119 618 := rows_sound h2 rows119_3 rowsOk119_3
  have h4 : ValidThrough v book119 642 := rows_sound h3 rows119_4 rowsOk119_4
  have h5 : ValidThrough v book119 666 := rows_sound h4 rows119_5 rowsOk119_5
  have h6 : ValidThrough v book119 690 := rows_sound h5 rows119_6 rowsOk119_6
  have h7 : ValidThrough v book119 714 := rows_sound h6 rows119_7 rowsOk119_7
  have h8 : ValidThrough v book119 738 := rows_sound h7 rows119_8 rowsOk119_8
  have h9 : ValidThrough v book119 762 := rows_sound h8 rows119_9 rowsOk119_9
  have h10 : ValidThrough v book119 786 := rows_sound h9 rows119_10 rowsOk119_10
  have h11 : ValidThrough v book119 810 := rows_sound h10 rows119_11 rowsOk119_11
  have h12 : ValidThrough v book119 834 := rows_sound h11 rows119_12 rowsOk119_12
  have h13 : ValidThrough v book119 858 := rows_sound h12 rows119_13 rowsOk119_13
  have h14 : ValidThrough v book119 871 := rows_sound h13 rows119_14 rowsOk119_14
  exact book_end h14 _ _ conflict119
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
