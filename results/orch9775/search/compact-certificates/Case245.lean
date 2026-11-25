import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a245 : Array Fact := #[(.res 0 9),(.res 1 9),(.res 2 9),(.res 0 10),(.res 1 10),(.res 2 10),(.res 0 11),(.res 1 11),(.res 2 11),(.res 0 13),(.res 1 13),(.res 2 13),(.lab 3 0 3),(.lab 3 1 3),(.lab 3 2 3),(.lab 3 3 3),(.lab 3 4 3),(.lab 4 0 4),(.lab 4 0 3),(.avoid 4 1102 0),(.lab 6 0 3),(.lab 6 0 4),(.avoid 6 314 0),(.lab 9 0 9),(.live 9 1),(.lab 9 0 10),(.common 9 10),(.lab 9 0 11),(.common 9 11),(.lab 9 0 12),(.lab 9 0 13),(.common 9 13),(.lab 9 1 9),(.live 9 2),(.lab 9 1 8),(.lab 9 1 10),(.lab 9 1 11),(.lab 9 1 12),(.lab 9 1 13),(.lab 9 2 9),(.live 9 3),(.lab 9 2 10),(.lab 9 2 11),(.lab 9 2 12),(.lab 9 2 13),(.lab 9 3 9),(.live 9 4),(.lab 9 3 8),(.lab 9 3 10),(.lab 9 3 11),(.lab 9 3 13),(.lab 9 4 9),(.avoid 9 7174 0),(.avoid 9 7174 1),(.avoid 9 7174 2),(.avoid 9 7174 3),(.avoid 9 7174 4),(.avoid 9 10656 0),(.avoid 9 10656 1),(.avoid 9 10656 2),(.avoid 9 10656 3),(.avoid 9 10656 4),(.see 9 5 6789 0),(.see 9 5 6789 1),(.see 9 5 6789 2),(.see 9 5 6789 3),(.see 9 5 6789 4),(.see 9 6 7812 0),(.see 9 6 7812 1),(.see 9 6 7812 2),(.see 9 6 7812 3),(.see 9 6 7812 4),(.see 9 6 9992 0),(.see 9 6 9992 1),(.see 9 6 9992 2),(.see 9 6 9992 3),(.see 9 6 9992 4),(.see 9 6 14977 0),(.see 9 6 14977 1),(.see 9 6 14977 2),(.see 9 6 14977 3),(.see 9 6 14977 4),(.see 9 6 16256 0),(.see 9 6 16256 1),(.see 9 6 16256 2),(.see 9 6 16256 3),(.see 9 6 16256 4),(.diff 0 9 10),(.diff 1 9 10),(.diff 2 9 10),(.diff 0 9 11),(.diff 1 9 11),(.diff 2 9 11),(.diff 0 9 13),(.diff 1 9 13),(.diff 2 9 13),(.live 10 1),(.lab 10 0 8),(.lab 10 0 11),(.common 10 11),(.lab 10 0 12),(.lab 10 0 13),(.common 10 13),(.live 10 2),(.lab 10 1 8),(.lab 10 1 11),(.lab 10 1 12),(.lab 10 1 13),(.live 10 3),(.lab 10 2 8),(.lab 10 2 11),(.lab 10 2 12),(.lab 10 2 13),(.live 10 4),(.lab 10 3 8),(.lab 10 3 11),(.lab 10 3 12),(.lab 10 3 13),(.avoid 10 2338 0),(.avoid 10 2338 1),(.avoid 10 2338 2),(.avoid 10 2338 3),(.avoid 10 2338 4),(.avoid 10 10656 0),(.avoid 10 10656 1),(.avoid 10 10656 2),(.avoid 10 10656 3),(.avoid 10 10656 4),(.avoid 10 12481 0),(.avoid 10 12481 1),(.avoid 10 12481 2),(.avoid 10 12481 3),(.avoid 10 12481 4),(.see 10 0 7426 0),(.see 10 0 7426 1),(.see 10 0 7426 2),(.see 10 0 7426 3),(.see 10 0 7426 4),(.see 10 5 13504 0),(.see 10 5 13504 1),(.see 10 5 13504 2),(.see 10 5 13504 3),(.see 10 5 13504 4),(.see 10 5 16256 0),(.see 10 5 16256 1),(.see 10 5 16256 2),(.see 10 5 16256 3),(.see 10 5 16256 4),(.diff 0 10 11),(.diff 1 10 11),(.diff 2 10 11),(.diff 0 10 13),(.diff 1 10 13),(.diff 2 10 13),(.live 11 1),(.lab 11 0 8),(.lab 11 0 9),(.lab 11 0 10),(.lab 11 0 13),(.common 11 13),(.live 11 2),(.lab 11 1 8),(.lab 11 1 9),(.lab 11 1 10),(.lab 11 1 13),(.live 11 3),(.lab 11 2 8),(.lab 11 2 9),(.lab 11 2 10),(.lab 11 2 13),(.live 11 4),(.lab 11 3 8),(.lab 11 3 9),(.lab 11 3 10),(.lab 11 3 13),(.lab 11 4 9),(.lab 11 4 10),(.avoid 11 1548 0),(.avoid 11 1548 1),(.avoid 11 1548 2),(.avoid 11 1548 3),(.avoid 11 1548 4),(.avoid 11 8488 0),(.avoid 11 8488 1),(.avoid 11 8488 2),(.avoid 11 8488 3),(.avoid 11 8488 4),(.see 11 4 7812 0),(.see 11 4 7812 1),(.see 11 4 7812 2),(.see 11 4 7812 3),(.see 11 4 7812 4),(.see 11 6 10656 0),(.see 11 6 10656 1),(.see 11 6 10656 2),(.see 11 6 10656 3),(.see 11 6 10656 4),(.diff 0 11 9),(.diff 1 11 9),(.diff 2 11 9),(.diff 0 11 13),(.diff 1 11 13),(.diff 2 11 13),(.live 13 1),(.lab 13 0 8),(.lab 13 0 9),(.lab 13 0 10),(.lab 13 0 11),(.live 13 2),(.lab 13 1 8),(.lab 13 1 9),(.lab 13 1 10),(.lab 13 1 11),(.live 13 3),(.lab 13 2 8),(.lab 13 2 9),(.lab 13 2 10),(.lab 13 2 11),(.live 13 4),(.lab 13 3 8),(.lab 13 3 9),(.lab 13 3 10),(.lab 13 3 11),(.avoid 13 792 0),(.avoid 13 792 1),(.avoid 13 792 2),(.avoid 13 792 3),(.avoid 13 792 4),(.avoid 13 1290 0),(.avoid 13 1290 1),(.avoid 13 1290 2),(.avoid 13 1290 3),(.avoid 13 1290 4),(.avoid 13 2338 0),(.avoid 13 2338 1),(.avoid 13 2338 2),(.avoid 13 2338 3),(.avoid 13 2338 4),(.avoid 13 7426 0),(.avoid 13 7426 1),(.avoid 13 7426 2),(.avoid 13 7426 3),(.avoid 13 7426 4),(.see 13 2 8488 0),(.see 13 2 8488 1),(.see 13 2 8488 2),(.see 13 2 8488 3),(.see 13 2 8488 4),(.see 13 2 9992 0),(.see 13 2 9992 1),(.see 13 2 9992 2),(.see 13 2 9992 3),(.see 13 2 9992 4),(.see 13 2 10656 0),(.see 13 2 10656 1),(.see 13 2 10656 2),(.see 13 2 10656 3),(.see 13 2 10656 4),(.see 13 4 9992 0),(.see 13 4 9992 1),(.see 13 4 9992 2),(.see 13 4 9992 3),(.see 13 4 9992 4),(.see 13 4 16256 0),(.see 13 4 16256 1),(.see 13 4 16256 2),(.see 13 4 16256 3),(.see 13 4 16256 4),(.diff 0 13 9),(.diff 1 13 9),(.diff 2 13 9),(.diff 0 13 10),(.diff 1 13 10),(.diff 2 13 10),(.diff 0 13 11),(.diff 1 13 11),(.diff 2 13 11),(.reader false 8 0),(.reader false 8 1),(.reader false 8 2),(.reader false 8 3),(.reader false 8 4),(.es false 8 3),(.reader false 11 0),(.es false 11 3),(.es false 11 4),(.reader false 17 0),(.reader false 18 0),(.es false 18 3),(.es false 18 4),(.reader true 8 0),(.reader true 8 1),(.reader true 8 2),(.reader true 8 3),(.reader true 8 4),(.reader true 11 0),(.reader true 11 1),(.reader true 11 2),(.reader true 11 3),(.reader true 11 4),(.reader true 17 0),(.reader true 17 1),(.reader true 17 2),(.reader true 17 3),(.reader true 17 4),(.es true 17 9),(.reader true 18 0),(.reader true 18 1),(.reader true 18 2),(.reader true 18 3),(.reader true 18 4),(.es true 18 9),(.gate 8 11),(.gate 8 18),(.gate 11 18),(.gate 17 18)]
def r245 : List Scheme := [(.self 3 0),(.self 3 1),(.self 3 2),(.self 3 3),(.self 3 4),(.self 4 0),(.exposure 4 1102),(.avoidNot 4 3 1102 0),(.exposure 6 314),(.avoidNot 6 3 314 0),(.avoidNot 6 4 314 0),(.self 9 0),(.self 9 1),(.earlier 9 1),(.self 9 2),(.earlier 9 2),(.self 9 3),(.self 9 4),(.allRes 9 0),(.allRes 9 1),(.allRes 9 2),(.exposure 9 7174),(.avoidNot 9 10 7174 0),(.avoidNot 9 11 7174 0),(.avoidNot 9 12 7174 0),(.avoidLive 9 7174 1),(.avoidNot 9 10 7174 1),(.avoidNot 9 11 7174 1),(.avoidNot 9 12 7174 1),(.avoidLive 9 7174 2),(.avoidNot 9 10 7174 2),(.avoidNot 9 11 7174 2),(.avoidNot 9 12 7174 2),(.avoidLive 9 7174 3),(.avoidNot 9 10 7174 3),(.avoidNot 9 11 7174 3),(.avoidLive 9 7174 4),(.exposure 9 10656),(.avoidNot 9 11 10656 0),(.avoidNot 9 13 10656 0),(.avoidNot 9 8 10656 1),(.avoidNot 9 13 10656 1),(.avoidNot 9 11 10656 2),(.avoidNot 9 13 10656 2),(.avoidLive 9 10656 3),(.avoidNot 9 8 10656 3),(.avoidNot 9 13 10656 3),(.avoidLive 9 10656 4),(.exactAt 9 5 6789),(.seeLab 9 5 11 6789 0),(.seeLab 9 5 12 6789 0),(.seeLive 9 5 6789 1),(.seeLab 9 5 11 6789 1),(.seeLab 9 5 12 6789 1),(.seeLive 9 5 6789 2),(.seeLab 9 5 11 6789 2),(.seeLab 9 5 12 6789 2),(.seeLive 9 5 6789 3),(.seeLab 9 5 11 6789 3),(.seeLive 9 5 6789 4),(.exactAt 9 6 7812),(.seeLab 9 6 10 7812 0),(.seeLab 9 6 11 7812 0),(.seeLab 9 6 10 7812 1),(.seeLab 9 6 11 7812 1),(.seeLive 9 6 7812 2),(.seeLab 9 6 10 7812 2),(.seeLab 9 6 11 7812 2),(.seeLive 9 6 7812 3),(.seeLab 9 6 10 7812 3),(.seeLab 9 6 11 7812 3),(.seeLive 9 6 7812 4),(.exactAt 9 6 9992),(.seeLab 9 6 13 9992 0),(.seeLab 9 6 13 9992 1),(.seeLab 9 6 13 9992 2),(.seeLab 9 6 8 9992 3),(.seeLive 9 6 9992 4),(.exactAt 9 6 14977),(.seeLab 9 6 11 14977 0),(.seeLab 9 6 13 14977 1),(.seeLab 9 6 13 14977 2),(.seeLive 9 6 14977 3),(.seeLab 9 6 13 14977 3),(.seeLive 9 6 14977 4),(.exactAt 9 6 16256),(.seeLab 9 6 11 16256 0),(.seeLab 9 6 13 16256 0),(.seeLab 9 6 8 16256 1),(.seeLab 9 6 13 16256 1),(.seeLab 9 6 11 16256 2),(.seeLab 9 6 13 16256 2),(.seeLive 9 6 16256 3),(.seeLab 9 6 13 16256 3),(.seeLive 9 6 16256 4),(.diffX 0 9 10),(.diffC 0 9 10),(.diffX 1 9 10),(.diffC 1 9 10),(.diffX 2 9 10),(.diffC 2 9 10),(.adjacentCommon 9 10 5),(.residual 9 10 0 1),(.residual 9 10 0 2),(.residual 9 10 0 3),(.residual 9 10 1 2),(.residual 9 10 1 3),(.residual 9 10 2 3),(.diffC 0 9 11),(.diffC 1 9 11),(.diffC 2 9 11),(.adjacentCommon 9 11 6),(.residual 9 11 0 1),(.residual 9 11 0 2),(.residual 9 11 0 3),(.residual 9 11 1 2),(.residual 9 11 1 3),(.residual 9 11 2 3),(.diffX 0 9 13),(.diffC 0 9 13),(.resCommon 9 13 0),(.diffX 1 9 13),(.diffC 1 9 13),(.resCommon 9 13 1),(.diffX 2 9 13),(.diffC 2 9 13),(.resCommon 9 13 2),(.residual 9 13 0 1),(.residual 9 13 0 2),(.residual 9 13 0 3),(.residual 9 13 1 2),(.residual 9 13 1 3),(.residual 9 13 2 3),(.earlier 10 1),(.earlier 10 2),(.allRes 10 0),(.allRes 10 1),(.allRes 10 2),(.exposure 10 2338),(.avoidNot 10 8 2338 0),(.avoidNot 10 11 2338 0),(.avoidLive 10 2338 1),(.avoidNot 10 8 2338 1),(.avoidNot 10 11 2338 1),(.avoidLive 10 2338 2),(.avoidNot 10 11 2338 2),(.avoidLive 10 2338 3),(.avoidNot 10 11 2338 3),(.avoidLive 10 2338 4),(.exposure 10 10656),(.avoidNot 10 11 10656 0),(.avoidNot 10 11 10656 1),(.avoidNot 10 11 10656 2),(.avoidNot 10 8 10656 3),(.avoidLive 10 10656 4),(.exposure 10 12481),(.avoidNot 10 12 12481 0),(.avoidNot 10 13 12481 0),(.avoidNot 10 12 12481 1),(.avoidNot 10 13 12481 1),(.avoidLive 10 12481 2),(.avoidNot 10 12 12481 2),(.avoidNot 10 13 12481 2),(.avoidLive 10 12481 3),(.avoidNot 10 12 12481 3),(.avoidNot 10 13 12481 3),(.avoidLive 10 12481 4),(.exactAt 10 0 7426),(.seeLab 10 0 8 7426 0),(.seeLab 10 0 11 7426 0),(.seeLive 10 0 7426 1),(.seeLab 10 0 8 7426 1),(.seeLab 10 0 11 7426 1),(.seeLive 10 0 7426 2),(.seeLab 10 0 8 7426 2),(.seeLab 10 0 11 7426 2),(.seeLive 10 0 7426 3),(.seeLab 10 0 8 7426 3),(.seeLab 10 0 11 7426 3),(.seeLive 10 0 7426 4),(.exactAt 10 5 13504),(.seeLab 10 5 12 13504 0),(.seeLab 10 5 13 13504 0),(.seeLab 10 5 12 13504 1),(.seeLab 10 5 13 13504 1),(.seeLive 10 5 13504 2),(.seeLab 10 5 12 13504 2),(.seeLab 10 5 13 13504 2),(.seeLive 10 5 13504 3),(.seeLab 10 5 12 13504 3),(.seeLab 10 5 13 13504 3),(.seeLive 10 5 13504 4),(.exactAt 10 5 16256),(.seeLab 10 5 11 16256 0),(.seeLab 10 5 11 16256 1),(.seeLab 10 5 8 16256 2),(.seeLive 10 5 16256 3),(.seeLab 10 5 11 16256 3),(.seeLive 10 5 16256 4),(.diffX 0 10 11),(.diffC 0 10 11),(.diffX 1 10 11),(.diffC 1 10 11),(.diffX 2 10 11),(.diffC 2 10 11),(.adjacentCommon 10 11 4),(.residual 10 11 0 1),(.residual 10 11 0 2),(.residual 10 11 0 3),(.residual 10 11 1 2),(.residual 10 11 1 3),(.residual 10 11 2 3),(.diffX 0 10 13),(.diffC 0 10 13),(.diffX 1 10 13),(.diffC 1 10 13),(.diffX 2 10 13),(.diffC 2 10 13),(.adjacentCommon 10 13 4),(.residual 10 13 0 1),(.residual 10 13 0 2),(.residual 10 13 0 3),(.residual 10 13 1 2),(.residual 10 13 1 3),(.residual 10 13 2 3),(.earlier 11 1),(.earlier 11 2),(.earlier 11 3),(.allRes 11 0),(.allRes 11 1),(.allRes 11 2),(.exposure 11 1548),(.avoidNot 11 9 1548 0),(.avoidNot 11 10 1548 0),(.avoidNot 11 9 1548 1),(.avoidNot 11 10 1548 1),(.avoidLive 11 1548 2),(.avoidNot 11 9 1548 2),(.avoidNot 11 10 1548 2),(.avoidLive 11 1548 3),(.avoidNot 11 9 1548 3),(.avoidNot 11 10 1548 3),(.avoidLive 11 1548 4),(.avoidNot 11 9 1548 4),(.avoidNot 11 10 1548 4),(.exposure 11 8488),(.avoidNot 11 8 8488 0),(.avoidNot 11 13 8488 0),(.avoidNot 11 8 8488 1),(.avoidNot 11 13 8488 1),(.avoidNot 11 8 8488 2),(.avoidNot 11 13 8488 2),(.avoidLive 11 8488 3),(.avoidNot 11 8 8488 3),(.avoidNot 11 13 8488 3),(.avoidLive 11 8488 4),(.exactAt 11 4 7812),(.seeLab 11 4 9 7812 0),(.seeLab 11 4 10 7812 0),(.seeLab 11 4 9 7812 1),(.seeLab 11 4 10 7812 1),(.seeLive 11 4 7812 2),(.seeLab 11 4 9 7812 2),(.seeLab 11 4 10 7812 2),(.seeLive 11 4 7812 3),(.seeLab 11 4 9 7812 3),(.seeLab 11 4 10 7812 3),(.seeLive 11 4 7812 4),(.seeLab 11 4 9 7812 4),(.seeLab 11 4 10 7812 4),(.exactAt 11 6 10656),(.seeLab 11 6 8 10656 0),(.seeLab 11 6 13 10656 0),(.seeLab 11 6 8 10656 1),(.seeLab 11 6 13 10656 1),(.seeLab 11 6 8 10656 2),(.seeLab 11 6 13 10656 2),(.seeLive 11 6 10656 3),(.seeLab 11 6 8 10656 3),(.seeLab 11 6 13 10656 3),(.seeLive 11 6 10656 4),(.diffX 0 11 9),(.diffC 0 11 9),(.diffX 1 11 9),(.diffC 1 11 9),(.diffX 2 11 9),(.diffC 2 11 9),(.residual 11 9 0 1),(.residual 11 9 0 2),(.residual 11 9 0 3),(.residual 11 9 0 4),(.residual 11 9 1 2),(.residual 11 9 1 3),(.residual 11 9 1 4),(.residual 11 9 2 3),(.residual 11 9 2 4),(.residual 11 9 3 4),(.diffX 0 11 13),(.diffC 0 11 13),(.diffX 1 11 13),(.diffC 1 11 13),(.diffX 2 11 13),(.diffC 2 11 13),(.adjacentCommon 11 13 4),(.residual 11 13 0 1),(.residual 11 13 0 2),(.residual 11 13 0 3),(.residual 11 13 1 2),(.residual 11 13 1 3),(.residual 11 13 2 3),(.earlier 13 1),(.earlier 13 2),(.allRes 13 0),(.allRes 13 1),(.allRes 13 2),(.exposure 13 792),(.avoidNot 13 8 792 0),(.avoidNot 13 9 792 0),(.avoidNot 13 8 792 1),(.avoidNot 13 9 792 1),(.avoidNot 13 8 792 2),(.avoidNot 13 9 792 2),(.avoidLive 13 792 3),(.avoidNot 13 9 792 3),(.avoidLive 13 792 4),(.exposure 13 1290),(.avoidNot 13 8 1290 0),(.avoidNot 13 10 1290 0),(.avoidNot 13 8 1290 1),(.avoidNot 13 10 1290 1),(.avoidLive 13 1290 2),(.avoidNot 13 8 1290 2),(.avoidNot 13 10 1290 2),(.avoidLive 13 1290 3),(.avoidNot 13 10 1290 3),(.avoidLive 13 1290 4),(.exposure 13 2338),(.avoidNot 13 8 2338 0),(.avoidNot 13 11 2338 0),(.avoidNot 13 8 2338 1),(.avoidNot 13 11 2338 1),(.avoidNot 13 8 2338 2),(.avoidNot 13 11 2338 2),(.avoidLive 13 2338 3),(.avoidNot 13 11 2338 3),(.avoidLive 13 2338 4),(.exposure 13 7426),(.avoidNot 13 10 7426 0),(.avoidNot 13 11 7426 0),(.avoidNot 13 8 7426 1),(.avoidNot 13 10 7426 1),(.avoidNot 13 11 7426 1),(.avoidNot 13 10 7426 2),(.avoidNot 13 11 7426 2),(.avoidNot 13 8 7426 3),(.avoidNot 13 11 7426 3),(.avoidLive 13 7426 4),(.exactAt 13 2 8488),(.seeLab 13 2 8 8488 0),(.seeLive 13 2 8488 1),(.seeLive 13 2 8488 2),(.seeLive 13 2 8488 3),(.seeLive 13 2 8488 4),(.exactAt 13 2 9992),(.seeLab 13 2 8 9992 0),(.seeLab 13 2 9 9992 0),(.seeLab 13 2 10 9992 0),(.seeLab 13 2 8 9992 1),(.seeLab 13 2 9 9992 1),(.seeLab 13 2 10 9992 1),(.seeLive 13 2 9992 2),(.seeLab 13 2 8 9992 2),(.seeLab 13 2 9 9992 2),(.seeLab 13 2 10 9992 2),(.seeLive 13 2 9992 3),(.seeLab 13 2 8 9992 3),(.seeLab 13 2 9 9992 3),(.seeLab 13 2 10 9992 3),(.seeLive 13 2 9992 4),(.exactAt 13 2 10656),(.seeLab 13 2 8 10656 0),(.seeLab 13 2 11 10656 0),(.seeLab 13 2 8 10656 1),(.seeLab 13 2 11 10656 1),(.seeLab 13 2 8 10656 2),(.seeLab 13 2 11 10656 2),(.seeLive 13 2 10656 3),(.seeLab 13 2 8 10656 3),(.seeLab 13 2 11 10656 3),(.seeLive 13 2 10656 4),(.exactAt 13 4 9992),(.seeLab 13 4 8 9992 0),(.seeLab 13 4 9 9992 0),(.seeLab 13 4 10 9992 1),(.seeLive 13 4 9992 2),(.seeLive 13 4 9992 3),(.seeLive 13 4 9992 4),(.exactAt 13 4 16256),(.seeLab 13 4 8 16256 0),(.seeLab 13 4 9 16256 0),(.seeLab 13 4 10 16256 0),(.seeLab 13 4 11 16256 0),(.seeLab 13 4 9 16256 1),(.seeLab 13 4 10 16256 1),(.seeLab 13 4 11 16256 1),(.seeLab 13 4 9 16256 2),(.seeLab 13 4 11 16256 2),(.seeLive 13 4 16256 3),(.seeLab 13 4 8 16256 3),(.seeLive 13 4 16256 4),(.diffX 0 13 9),(.diffC 0 13 9),(.diffX 1 13 9),(.diffC 1 13 9),(.diffX 2 13 9),(.diffC 2 13 9),(.residual 13 9 0 1),(.residual 13 9 0 2),(.residual 13 9 0 3),(.residual 13 9 1 2),(.residual 13 9 1 3),(.residual 13 9 2 3),(.diffX 0 13 10),(.diffC 0 13 10),(.diffX 1 13 10),(.diffC 1 13 10),(.diffX 2 13 10),(.diffC 2 13 10),(.residual 13 10 0 1),(.residual 13 10 0 2),(.residual 13 10 0 3),(.residual 13 10 1 2),(.residual 13 10 1 3),(.residual 13 10 2 3),(.diffX 0 13 11),(.diffC 0 13 11),(.diffX 1 13 11),(.diffC 1 13 11),(.diffX 2 13 11),(.diffC 2 13 11),(.residual 13 11 0 1),(.residual 13 11 0 2),(.residual 13 11 0 3),(.residual 13 11 1 2),(.residual 13 11 1 3),(.residual 13 11 2 3),(.readerAny false 8),(.readerLab false 8 0 3 true),(.readerLab false 8 1 3 true),(.readerLab false 8 2 3 true),(.readerLab false 8 3 3 true),(.readerLab false 8 4 3 true),(.readerAny false 11),(.readerLab false 11 0 3 false),(.readerLab false 11 0 4 true),(.readerAny false 17),(.readerAny false 18),(.readerLab false 18 0 3 false),(.readerLab false 18 0 4 false),(.readerAny true 8),(.readerLive true 8 2),(.readerLive true 8 3),(.readerLive true 8 4),(.readerAny true 11),(.readerLive true 11 2),(.readerLive true 11 3),(.readerLive true 11 4),(.readerAny true 17),(.readerLab true 17 0 9 true),(.readerLab true 17 1 9 true),(.readerLab true 17 2 9 true),(.readerLab true 17 3 9 true),(.readerLab true 17 4 9 true),(.readerAny true 18),(.readerLab true 18 0 9 false),(.readerLive true 18 2),(.readerLab true 18 2 9 false),(.readerLive true 18 3),(.readerLive true 18 4),(.eqLab false 8 11 3 true),(.gateEq true 8 11 0),(.eqLab false 8 18 3 true),(.gateEq true 8 18 1),(.eqLab false 11 18 4 true),(.gateEq true 11 18 1),(.gateEq false 17 18 0),(.eqLab true 17 18 9 true)]

def table245_0 : List Nat := [0x641,0x6c1,0x741,0x7c1,0x841,0x8c1,0x9c1,0x240982,0xb41,0x280b02,0x2a0b02,0xbc1,0x1041,0x311082,0x13c1,0x431402]
def table245_1 : List Nat := [0x16c1,0x19c1,0x11702,0x31702,0x51702,0x1c46f1b46b1a45,0x321a02,0x361a02,0x3a1a02,0x311a82,0x461a82,0x481a82,0x4a1a82,0x431b02,0x521b02,0x541b02]
def table245_2 : List Nat := [0x561b02,0x511b82,0x601b82,0x621b82,0x5d1c02,0x1ec791dc751cc5,0x361c82,0x3c1c82,0x441d02,0x4c1d02,0x541d82,0x581d82,0x511e02,0x5e1e02,0x641e02,0x5d1e82]
def table245_3 : List Nat := [0x214832047f1f45,0x361f02,0x3b1f02,0x311f82,0x481f82,0x4b1f82,0x432002,0x542002,0x572002,0x512082,0x622082,0x5d2102,0x23c8d22c8921c5,0x322182,0x372182,0x462202]
def table245_4 : List Nat := [0x492202,0x432282,0x522282,0x552282,0x512302,0x602302,0x632302,0x5d2382,0x26497254932445,0x3c2402,0x4c2482,0x582502,0x5f2582,0x5d2602,0x28ca127c9d26c5,0x372682]
def table245_5 : List Nat := [0x4c2702,0x582782,0x512802,0x642802,0x5d2882,0x2b4ab2a4a72945,0x372902,0x3c2902,0x452982,0x4c2982,0x552a02,0x582a02,0x512a82,0x642a82,0x5d2b02,0x12b82]
def table245_6 : List Nat := [0x62b82,0x32c02,0x82c02,0x52c82,0xa2c82,0xd41,0x2ccb12bc470cc300d07,0x2ccb12bc530cc420d07,0x2ccb12bc610cc500d07,0x2ccb12bc5311c420d07,0x2ccb12bc6111c500d07,0x2ccb12bc6114c500d07,0xc2d02,0xe2d82,0x102e02,0xe41]
def table245_7 : List Nat := [0x2e4b72d4490dc300e07,0x2e4b72d4550dc420e07,0x2e4b72d4630dc500e07,0x2e4b72d455124420e07,0x2e4b72d463124500e07,0x2e4b72d463154500e07,0x12e82,0x122e82,0xfc120003,0x32f02,0x142f02,0xfc140083,0x52f82,0x162f82,0xfc160103,0x2fcbd2ec4d0f4300f87]
def table245_8 : List Nat := [0x2fcbd2ec590f4420f87,0x2fcbd2ec650f4500f87,0x2fcbd2ec59134420f87,0x2fcbd2ec65134500f87,0x2fcbd2ec65164500f87,0xc13382,0xcf3602,0x73882,0x93882,0xb3882,0x3d4f33c4ef3b45,0xc23b02,0xc43b02,0xc13b82,0xd03b82,0xd23b82]
def table245_9 : List Nat := [0xcf3c02,0xdc3c02,0xd93c82,0xe63c82,0xe33d02,0x3fcfd3ecf93dc5,0xc43d82,0xd23e02,0xdc3e82,0xe43f02,0xe33f82,0x42507415034045,0xc84002,0xca4002,0xd44082,0xd64082]
def table245_10 : List Nat := [0xcf4102,0xde4102,0xe04102,0xd94182,0xe84182,0xea4182,0xe34202,0x44d1143d0d42c5,0xc34282,0xc44282,0xc14302,0xd14302,0xd24302,0xcf4382,0xdb4382,0xdc4382]
def table245_11 : List Nat := [0xd94402,0xe54402,0xe64402,0xe34482,0x4751b465174545,0xc94502,0xca4502,0xd54582,0xd64582,0xcf4602,0xdf4602,0xe04602,0xd94682,0xe94682,0xea4682,0xe34702]
def table245_12 : List Nat := [0x49d2548d2147c5,0xc44782,0xd24802,0xda4882,0xd94902,0xe64902,0xe34982,0x74a02,0xc4a02,0x94a82,0xe4a82,0xb4b02,0x104b02,0x31c1,0x4b52b4a4d3314c03187,0x4b52b4a4dd314ce3187]
def table245_13 : List Nat := [0x4b52b4a4e7314d83187,0x4b52b4a4dd34cce3187,0x4b52b4a4e734cd83187,0x4b52b4a4e7374d83187,0x74b82,0x124b82,0x94c02,0x144c02,0xb4c82,0x164c82,0x3341,0x4cd314bcd732cc03307,0x4cd314bce132cce3307,0x4cd314bceb32cd83307,0x4cd314bce135cce3307,0x4cd314bceb35cd83307]
def table245_14 : List Nat := [0x4cd314bceb384d83307,0x1355002,0x1415282,0x14b5502,0xd5502,0xf5502,0x115502,0x5ad6959d6558c5,0x1385882,0x13a5882,0x1445902,0x1465902,0x1415982,0x14e5982,0x1505982,0x14b5a02]
def table245_15 : List Nat := [0x1585a02,0x15a5a02,0x1555a82,0x15e5a82,0x1605a82,0x5d5735c56f5b45,0x1365b02,0x13c5b02,0x1425b82,0x1485b82,0x14c5c02,0x1525c02,0x14b5c82,0x1565c82,0x15c5c82,0x1555d02]
def table245_16 : List Nat := [0x5fd7d5ed795dc5,0x1385d82,0x13b5d82,0x1445e02,0x1475e02,0x1415e82,0x14e5e82,0x1515e82,0x14b5f02,0x1585f02,0x15b5f02,0x1555f82,0x15e5f82,0x1615f82,0x62587615836045,0x1376002]
def table245_17 : List Nat := [0x13c6002,0x1436082,0x1486082,0x14d6102,0x1526102,0x14b6182,0x1576182,0x15c6182,0x1556202,0xd6282,0x6282,0xf6302,0x26302,0x116382,0x46382,0x63d8d62d454e5340e07]
def table245_18 : List Nat := [0x63d8d62d4f4e5400e07,0x63d8d62d594e54a0e07,0x63d8d62d5f4e5540e07,0x63d8d62d4f515400e07,0x63d8d62d595154a0e07,0x63d8d62d5f515540e07,0x63d8d62d5953d4a0e07,0x63d8d62d5f53d540e07,0x63d8d62d5f565540e07,0xd6402,0x126402,0xf6482,0x146482,0x116502,0x166502,0x4fc1]
def table245_19 : List Nat := [0x65593645494f5344f87,0x65593645534f5404f87,0x655936455d4f54a4f87,0x6559364553525404f87,0x655936455d5254a4f87,0x655936455d54d4a4f87,0x1976802,0x1a16a82,0x136d02,0x156d02,0x176d02,0x71dc570dc16fc5,0x1986f82,0x19a6f82,0x1a27002,0x1a47002]
def table245_20 : List Nat := [0x1ac7082,0x1ae7082,0x1ab7102,0x1b87102,0x1b57182,0x745cf735cb7245,0x1987202,0x19c7202,0x1a27282,0x1a67282,0x1a17302,0x1ac7302,0x1b07302,0x1ab7382,0x1ba7382,0x1b57402]
def table245_21 : List Nat := [0x76dd975dd574c5,0x1987482,0x19e7482,0x1a27502,0x1a87502,0x1ac7582,0x1b27582,0x1ab7602,0x1bc7602,0x1b57682,0x795e3785df7745,0x19c7702,0x19e7702,0x1a27782,0x1a67782,0x1a87782]
def table245_22 : List Nat := [0x1b07802,0x1b27802,0x1b67882,0x1bc7882,0x1b57902,0x7bded7ade979c5,0x1997982,0x1977a02,0x1a17a82,0x1ab7b02,0x1b57b82,0x7e5f77d5f37c45,0x1997c02,0x19a7c02,0x19c7c02,0x1a37c82]
def table245_23 : List Nat := [0x1a47c82,0x1a67c82,0x1a17d02,0x1ad7d02,0x1ae7d02,0x1b07d02,0x1ab7d82,0x1b77d82,0x1b87d82,0x1ba7d82,0x1b57e02,0x80e017fdfd7ec5,0x1997e82,0x19e7e82,0x1a37f02,0x1a87f02]
def table245_24 : List Nat := [0x1ad7f82,0x1b27f82,0x1ab8002,0x1b78002,0x1bc8002,0x1b58082,0x8360b826078145,0x1988102,0x19a8102,0x1a78182,0x1a18202,0x1ab8282,0x1b58302,0x85e1584e1183c5,0x1988382,0x19a8382]
def table245_25 : List Nat := [0x19d8382,0x19f8382,0x1a48402,0x1a78402,0x1a98402,0x1ae8482,0x1b38482,0x1ab8502,0x1b68502,0x1b58582,0x138602,0x8602,0x158682,0x28682,0x178702,0x48702]
def table245_26 : List Nat := [0x8761b865a566d960f87,0x8761b865af66da00f87,0x8761b865b966daa0f87,0x8761b865af695a00f87,0x8761b865b9695aa0f87,0x8761b865b96bdaa0f87,0x138782,0x68782,0x158802,0x88802,0x178882,0xa8882,0x88e2187da7675963307,0x88e2187db1675a03307,0x88e2187dbb675aa3307,0x88e2187db169da03307]
def table245_27 : List Nat := [0x88e2187dbb69daa3307,0x88e2187dbb6c5aa3307,0x138902,0xc8902,0x158982,0xe8982,0x178a02,0x108a02,0x8a627895a967d964f87,0x8a627895b367da04f87,0x8a627895bd67daa4f87,0x8a627895b36a5a04f87,0x8a627895bd6a5aa4f87,0x8a627895bd6cdaa4f87,0x8ce318be2d8ac5,0x8d4188a83]
def table245_28 : List Nat := [0x8d41a8b03,0x8d41c8b83,0x8d41e8c03,0x8d4208c83,0x8dc1,0x8e0258d83,0x8ec228d83,0x8f41,0x8fc1,0x900298f83,0x9082b8f83,0x9364b926479145,0x1419202,0x14b9282,0x1559302,0x95e5594e5193c5]
def table245_29 : List Nat := [0x1419482,0x14b9502,0x1559582,0x9865f9765b9645,0x98c2e9603,0x98c409683,0x98c4e9703,0x98c5a9783,0x98c669803,0x9b66b9a6679945,0x9b9399903,0x1419a02,0x9b94f9a03,0x14b9a82,0x1559b02,0x8e6349c03]
def table245_30 : List Nat := [0x9c64e9103,0x906349c83,0x9ce669183,0x90e3a9d03,0x9d6669403,0x9de3e8f03,0x9be629d83,0x901,0xa01,0xa81,0xb32c4af11c330c06,0xb32c4af14c331086,0xb32c4af184331406,0xb32c4af14c471086,0xb32c4af184471406,0xb32c4af184531406]
def table245_31 : List Nat := [0xb92dcb5124370c06,0xb92dcb5154371086,0xb92dcb518c371406,0xb92dcb5154491086,0xb92dcb518c491406,0xb92dcb518c551406,0x12d4ad2934cc53006,0x12d4ad29374c53386,0x12d4ad2939cc53606,0x12d4ad29374d33386,0x12d4ad2939cd33606,0x12d4ad2939cdd3606,0x1334c52f35ccb3006,0x1334c52f384cb3386,0x1334c52f3accb3606,0x1334c52f384d73386]
def table245_32 : List Nat := [0x1334c52f3acd73606,0x1334c52f3ace13606,0x18f6358b515394d06,0x18f6358b53d395006,0x18f6358b565395286,0x18f6358b57d395506,0x18f6358b53d455006,0x18f6358b565455286,0x18f6358b57d455506,0x18f6358b5654f5286,0x18f6358b57d4f5506,0x18f6358b57d595506,0x19564d915253d4d06,0x19564d9154d3d5006,0x19564d915753d5286,0x19564d9154d495006]
def table245_33 : List Nat := [0x19564d91575495286,0x19564d91575535286,0x2238861f69d9d6586,0x2238861f6c59d6806,0x2238861f6ed9d6a86,0x2238861f6c5a76806,0x2238861f6eda76a86,0x2238861f6edb16a86,0x22989e256a59f6586,0x22989e256cd9f6806,0x22989e256f59f6a86,0x22989e256cda96806,0x22989e256f5a96a86,0x22989e256f5b36a86,0x2358a82,0x2358b02]
def table245_34 : List Nat := [0x2358b82,0x2358c02,0x2358c82,0x8e01,0x8ec1,0x9001,0x9081,0x2639602,0x2639682,0x2639702,0x2639782,0x2639802,0x2349c02,0x2349c82,0x9d01,0x2669402]
def table245_35 : List Nat := [0x9dc1,0x26f9882,0x8d41,0x9c01,0x9c81,0x550e34903,0x550ff4403,0x11349d25444d23106,0x550e3374f33485,0x3d513444f33c50f3047,0x15438cdd3cc4,0x550e33743,0x15438cd839c4,0x3d513444f143cf33487,0x550e33603,0x15438c2]
def table245_36 : List Nat := [0x550712003,0x3888f1b83,0x154174631404,0x154174831a04,0x154174831a84,0x5505d20c3,0x1541742,0x15459d635f84,0x5517b5dd7f5905,0x5517b5dd7f5a05,0x5514e4e03,0x1545382,0x5501,0x5a81,0x5d01,0x5f81]
def table245_37 : List Nat := [0x6201,0x9301,0x9581,0x9b01,0x18f6358b5984,0x63d8d62d6953d7d5107,0x92e55926539985,0x9b98f6358b5a55953c7,0x59d695ed7d4e05,0x92e559ae655045,0x9b98f6358b5a57b52c7,0x26e63d8d62d695646,0x63d8d62d695f5404e07,0x18f6358b5a57d5006,0x63d8d9b98b5a45,0x18f9b98d62c4]
def table245_38 : List Nat := [0xe33ccf13044,0x895db8a6276a9d77e87,0x2256d62989e146c86,0x895b58a6278505,0x1b58a627895b37486,0x1b58a627895b37506,0x6d62989e257f85,0x6d62989e257605,0x1db8a627895d975daa6f48,0x1b58a627895b26a86,0x1b57fdd975e016786,0x6d5ab65c3,0x6d62989e256c85,0x1b58a627895ab67c6,0x6d62989e256ac5,0x1b58a6278944]
def table245_39 : List Nat := [0x98c1,0x9bc1,0x4b52b4a4d34405,0x4b4094a4f334d0f3387,0x12d025293ccd343c6,0x4b4094a4f334c5,0x3752d4ad294905,0xe223c42234871a86,0xe2174421a48d21c6,0xe223c501a84,0xe223c501b04,0x3885d1403,0xe2174421a04,0x3885d1083,0x3885d1a83,0xe21742]
def table245_40 : List Nat := [0x1701,0x1c01,0x1e81,0x2101,0x2381,0x2601,0x2881,0x2b01,0x3881,0x3d01,0x3f81,0x4201,0x4481,0x4701,0x4981,0x1f47f10c3]
def table245_41 : List Nat := [0x439214b52b4a45,0x87dd17d2238845,0x421e44d1d4bd0f8bf2ec8,0x645936554a6005,0x645936554a6085,0x645936554a6105,0x193645955284,0x14b5042,0x19164d956004,0x19164d956084,0x645936543,0xce4cd314bcd84506,0xce4cd314bcd84586,0xce4cd314bcd84606,0x4cd313392f3605,0x339334c52f4505]
def table245_42 : List Nat := [0x339334c52f4585,0x133339314bc4,0x219875c70fa1b7d06,0x8661d0fa1b7d5f97ddaa6e49,0x71df57e5f7715c36907,0x219875c70fa1b7e5f7659c570ca,0x8661d0fa1b7d5f97dda06bc9,0x2198743e86df57e5f77108,0x1b565c2,0x835f57e5f78260b6687,0x219875c77460d0fa1b659f97dca,0x219876170fa1b7d86,0x8661b6d43e8745,0x2bc332c4b32285,0x2bc68234b32c45,0x1a08d10c3]
def table245_43 : List Nat := [0x1b587e23885aa7c06,0x1b587e23885f76a86,0x6d61f88e2173da07c87,0x1b587e23885f76806,0x1b587e23885f77c06,0x6d61f88e217dc5,0x1b587e238844,0x3392b4b5294385,0xce43d2d4ad2934c6,0x10f348fb3104,0x10f348f13984,0x10f4b52b4a4d23706,0x43d2d3392b4a45,0x2f4420f8bb2fc792ac731309,0x2f4420f8bb2fc501347,0x2f4421403e2fc4c1e4bb1cc9]
def table245_44 : List Nat := [0xbd108500f8bf130792ec8,0x12d4a52b3384,0x4b5290243,0xcf3102,0x87e2105c3,0x422ecbf1403e2f46,0x108b12bcb31bc692207,0x108502c4af2cc871bc8b1a49,0x140b12bcb31a05,0x422c4af2cc692306,0x422c4af2cc692206,0x422c4af2cc692286,0x108b12bcb31a45,0xb12bcb31a04,0xb1108af2cc4,0x4b5294ac3]
def table245_45 : List Nat := [0x19563e1d0f92d2f06,0x19563e1d0f92d2e86,0x2fc3e2f4bb108a51347,0xbf0f8bd2ec420dc6,0x2fc3e2f4bb1085,0x10c1,0x4b4040583,0x12f4c5334504,0x4cd2f4c43,0x63c174a83,0x12d0102,0x12d4b82,0x12d4c02,0x4b4120543,0x12d0482,0x4b41]
def table245_46 : List Nat := [705,0x401,0x2c81,0x8881,0x6381,0x6501,0x130082,0x4c1,0x2e81,0x4b81,0x6401,0x64c1,961,0x501,0x8981,0x6d01]
def table245_47 : List Nat := [0x8681,1,0x2b81,0x2c41,193,513,0x6301,0x4c01,0x62c1,0x4cc1,833,0x581,0x8901,0x8a01]

def encoded245 (i : Nat) : Nat :=
  if i < 384 then
    if i < 192 then
      if i < 96 then
        if i < 48 then
          if i < 16 then
            table245_0.getD (i%16) 0
          else
            if i < 32 then
              table245_1.getD (i%16) 0
            else
              table245_2.getD (i%16) 0
        else
          if i < 64 then
            table245_3.getD (i%16) 0
          else
            if i < 80 then
              table245_4.getD (i%16) 0
            else
              table245_5.getD (i%16) 0
      else
        if i < 144 then
          if i < 112 then
            table245_6.getD (i%16) 0
          else
            if i < 128 then
              table245_7.getD (i%16) 0
            else
              table245_8.getD (i%16) 0
        else
          if i < 160 then
            table245_9.getD (i%16) 0
          else
            if i < 176 then
              table245_10.getD (i%16) 0
            else
              table245_11.getD (i%16) 0
    else
      if i < 288 then
        if i < 240 then
          if i < 208 then
            table245_12.getD (i%16) 0
          else
            if i < 224 then
              table245_13.getD (i%16) 0
            else
              table245_14.getD (i%16) 0
        else
          if i < 256 then
            table245_15.getD (i%16) 0
          else
            if i < 272 then
              table245_16.getD (i%16) 0
            else
              table245_17.getD (i%16) 0
      else
        if i < 336 then
          if i < 304 then
            table245_18.getD (i%16) 0
          else
            if i < 320 then
              table245_19.getD (i%16) 0
            else
              table245_20.getD (i%16) 0
        else
          if i < 352 then
            table245_21.getD (i%16) 0
          else
            if i < 368 then
              table245_22.getD (i%16) 0
            else
              table245_23.getD (i%16) 0
  else
    if i < 576 then
      if i < 480 then
        if i < 432 then
          if i < 400 then
            table245_24.getD (i%16) 0
          else
            if i < 416 then
              table245_25.getD (i%16) 0
            else
              table245_26.getD (i%16) 0
        else
          if i < 448 then
            table245_27.getD (i%16) 0
          else
            if i < 464 then
              table245_28.getD (i%16) 0
            else
              table245_29.getD (i%16) 0
      else
        if i < 528 then
          if i < 496 then
            table245_30.getD (i%16) 0
          else
            if i < 512 then
              table245_31.getD (i%16) 0
            else
              table245_32.getD (i%16) 0
        else
          if i < 544 then
            table245_33.getD (i%16) 0
          else
            if i < 560 then
              table245_34.getD (i%16) 0
            else
              table245_35.getD (i%16) 0
    else
      if i < 672 then
        if i < 624 then
          if i < 592 then
            table245_36.getD (i%16) 0
          else
            if i < 608 then
              table245_37.getD (i%16) 0
            else
              table245_38.getD (i%16) 0
        else
          if i < 640 then
            table245_39.getD (i%16) 0
          else
            if i < 656 then
              table245_40.getD (i%16) 0
            else
              table245_41.getD (i%16) 0
      else
        if i < 720 then
          if i < 688 then
            table245_42.getD (i%16) 0
          else
            if i < 704 then
              table245_43.getD (i%16) 0
            else
              table245_44.getD (i%16) 0
        else
          if i < 736 then
            table245_45.getD (i%16) 0
          else
            if i < 752 then
              table245_46.getD (i%16) 0
            else
              table245_47.getD (i%16) 0
def book245 (i : Nat) : Clause := let n := encoded245 i; unpackLits 10 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses245 : inputsOK 3 245 a245 r245 (baseBook book245 487).toList=true := by decide +kernel

def rows245_0 : List Nat := [0x300e01,0x401201,0x401401,0x328cc01,0x328ce01,0x328d001,0x328d201,0x328d401,0x328d601,0x378e001,0x378e201,0x378e401,0x378e601,0x378e801,0x378ea01,0x6699c01,0x6699e01,0x669a001,0x669a201,0x669a401,0x669a601,0x6d1b601,0x6d1b801,0x6d1ba01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk245_0 : checkRows book245 10 487 rows245_0=true := by decide +kernel

def rows245_1 : List Nat := [0x6d1bc01,0x6d1be01,0x6d1c001,0x37a3e01,0x37a4001,0x37a4201,0x37a4401,0x37a4601,0x37a4801,0x37a4a01,0x37a4c01,0x37a4e01,0x37a5001,0x97a6001,0x97a6201,0x97a6401,0x97a6601,0x97a6801,0x97a6a01,0x6d35801,0x6d35a01,0x6d35c01,0x6d35e01,0x6d36001]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk245_1 : checkRows book245 10 511 rows245_1=true := by decide +kernel

def rows245_2 : List Nat := [0x6d36201,0x97b7001,0x97b7201,0x97b7401,0x97b7601,0x97b7801,0x97b7a01,0x37e01,0xb8001,0x138201,0x1b8401,0x238601,0x3cee238a02,0xae238c02,0x3d0e439202,0x3d2e439402,0x5ba801,0x63aa01,0x73ac01,0x83ae01,0x8bb001,0x111bbe01,0x112bc201,0x44d123c602]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk245_2 : checkRows book245 10 535 rows245_2=true := by decide +kernel

def rows245_3 : List Nat := [0x1173c801,0x390e3bca02,0x1183cc01,0x1114431043f0f37c05,0x11945801,0x11945a01,0x1325392a579305612e5492cfdbf4fc18a621907219472998731345996216,0x12a4b92cfd932fd3f0591625819072194729987313010,0x5718053982549586118607,0x4594e4515a483ef1b958479907219472998731285998d1ac6c4d15015,0x4594e451544695005,0x4714e45152463ed1c95a483f31c19072194729987312859c6c4d15615,0x499251d1907219472998733f609,0xfd3f0641c8651ca661cc5998d1ac6c4d46e0d,0x4594e451584795005,0x11c5391454918fb47a49c784290c641c8651ca661cc4a1671b1344895f1d95618,0x4714e45152463ed1ec724947c579231dc6c599344a19072194729987315617,0x118420a82e0d840f8be61c06e1b0d8720da728dc733ea11,0x7a1f884233d8f73de11844108c0438c4440c84487810,0x3e0d82efabe8f90d8720da728dc730492088f1f82a10,0x1a066180640c02e361c8369ca371cc1dc80123e00f,0x1886af80380d832361c8369ca371cc1dc80120600f,0x18868f8be60f83a0ac89218d8720da728dc73077200492088f1f86015,0x1d07322c8403]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk245_3 : checkRows book245 10 559 rows245_3=true := by decide +kernel

def rows245_4 : List Nat := [0x1d4781e90441686a188d0248e0268f029231ce0e,0x84a09039d6751c68d0248e0268f029232000d,0x81a15039e2781c68d0248e0268f029232000d,0x20684c11059e673c932448e809d08d0248e0268f029231da8320014,0x811ce8021879a12782067540b024052520c769c2711c68d0248e0268f029231d219,0x7720073a02742067521879a12784070341504c968f2388d02809825231c471a0e19,0x1261e401,0x1261fe01,0x12621601,0x12623001,0x12639c01,0x1263a401,0x1263bc01,0x2128420080a0683c07031dc769d927c120c,0x82a05019d2741ce819d52a49f26a000b,0x39ee5c5ef1467294a31a3c008,0x75a0073a02743b4eccace839882c0d2abbae8b9a84412ee4a927c9b29a0817,0x75a0073a027449f26a0807,0x12b3b6e839929bb205,0x74a0073a067540470cb2ed4b0eeba2e6a112a49f26a0411,0x751d103c092d20d2bca9269ce09,0x7520c73cb0744a926c0c07,0x74a0073a067520d014072e1c32a49f26a040d,0x829c52ea132dcb405]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk245_4 : checkRows book245 10 583 rows245_4=true := by decide +kernel

def rows245_5 : List Nat := [0x20680a0c8540f02412789e077cbd27a000c,0x1605690c4292859c7206,0xac2a90d430a8afabe26c9baa009,0x2a4ac4310e2a6bfafcbdcc2c0aacacb0ac1b309b26ecbaa012,0x2aabdaa0bfaa8beaa4ac4370cc3b313069bb30cbab2c2b0012,0xb5aecc9ae49bb1b0cb22b62a4a8af4cccc6cb2e20f,0xb5aecc72e49bb1b0db28b7aa8a9af4cccc6cb2d80f,0xac2aea84cb322aac0b00acc3a09,0x2c4bdab4b0afeafafaae43b0e434ac2aeb230b3330610,0x2a8a94390d2a004,0xad430aeafebf2f6c22c73426d30a6eacac8c2ccd33aacb0ab813,0xa9af6a82faa92b2c2afc07,0x292c328ac3a8cb32cac52d0a52ce9b29eb5318a6ad2c5b1212,0xa8af6a82feaa43135cd4c14d2ab2b2c2ccd33af80f,0xa2af8a4af6c9afea531b0c432c8a9ec2b3331ccccb4d8a6b0535a8c15,0xa2b20a531b0db28a42febf2f6becdac129aa7b0acccc73332d3628e15,0xbfafac24370cc3a9bcdd364ccc2af60b,0x115c5514c5113ba605,0x13846201,0x164583f402,0x11c539145491848becfc90a4a166444e4649560e,0x11c5391454918fb4c0484e64a166444e4649560e,0x15e56ce864bf204,0x18a623f602]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk245_5 : checkRows book245 10 607 rows245_5=true := by decide +kernel

def rows245_6 : List Nat := [0x21080f68360d0c0438c4440c8448780b,0x7e21bda0f83c0acee3010e3111032112124822387810,0x2108a1e880f6bdcf50360d0c0438c4440c84481a0787811,0x8a1e87e21bdef5bda0f83c3010e31110321120787810,0x2107e2287cf5bd4f602e0b02b3d4f20681e3010e3111032112124822387817,0x2107e1f3d6f502e0b0c0438c4440c84488e224f60687811,0xf034f5bd41ecf13e01a3010e311103211212482238893d82a13,0x1e880f50360d0323010e3111032112238893d8833e87811,0x80180781907c0c02e0acfc2086c0ecfa220733dc82238761206814,0x12fa3c8e0280982538a3407,0x14004801,0x14005e01,0x14007601,0x14008e01,0x14009a01,0x1400a801,0x1400bc01,0x1404fe01,0x14412801,0x14413401,0x14414c01,0x14416601,0x14417e01,0x14418c01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk245_6 : checkRows book245 10 631 rows245_6=true := by decide +kernel

def rows245_7 : List Nat := [0x721b01f4186004,0x1833b3ee5695e6195d4718008,0xa729aa2a8ea4c270aae4baa96b9c2e0b,0x4e158fe4101b4104a06,0x1fc7d9f30741b061ec8821e709c5271ea0c,0x1ee7f1f706421079f089222709c5271ea0c,0x7b9f27f41b07c227d228899c5271ea0b,0x7c9ee7dc21074227ea2e8b21d4ad2949ca1271ea0f,0x4b12ca0a761de8439ae8bbb38bb40a,0x1f27dc19069ec8821e7e1c34bd2d271ea0c,0x1f67bc1f061f0892227e1c34bd2d271ea0c,0x1ee7cc1b079f48a226875334c52e8a9f94b4a1271ea10,0x529444fbfcfebf84e16c5a90b459360b,0x4e94a513f9003fe4f1705b90b459360b,0x13a4f94afebff009425d975459360a,0x4f93a51400ff4025217c5e9694ed394dd1b459360f,0x5113efebf84e16c5a90a51d3d459360b,0x4e944fe3fe4f1705b90a51d3d459360b,0x4e93efebfe509765d1695053e5e1474f51b459360f,0xa1a849da7a9fb42d1a80ba2e6b934a0b,0x2e0b6b48d12d604,0x9e2d69dae09fad805,0x27cb5a76b6a7ad0549512de08,0x2dab8342d1ad604]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk245_7 : checkRows book245 10 655 rows245_7=true := by decide +kernel

def rows245_8 : List Nat := [0x286a154602,0x4d69b26e02,0xb8b0cb5b10b6b1205,0x292c328ac3a8cb62d6b834154b16a6b14a526f5328352d4f5131214,0x324cab1ed234ad1330bc2eebb31a0a,0x155a88a7af4c63335455407,0x8420bd602,0x6868f50801f8795682c1f02e190314251e0d,0x1a079478821f02e190314208009,0x292a629d094270a28cb72d8a7d509ba8a0c,0x298a3a9d0ac250b290b8adeb5d609baf554522a7a8a10,0xa628f0ac24a42e2b7a9f5428a09,0xa4a9909426a32dcb62d7592f554522a7a9b58a8a0f,0xa2c24a32dcb629f5429b58a9559a920b,0xa2c24a42e2b7ad75a29559a9b58af554522a7a8e0f,0x2b6af2c10a42d0bac4bcaeebb56ab22b40c,0xfcd205798403,0x499244511c5594e5491848becfcce442d13463f40f,0x4c94e4a9524b12e565194516209,0x16449d1944c7a04,0x58124fc5755c93048d1944c7a09,0x591611bcecfbd775c519473f609,0xaa400b415854128b214d0f410ae0a,0x140aa128ba170ae138b6159063f90406d0f410b00f]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk245_8 : checkRows book245 10 679 rows245_8=true := by decide +kernel

def rows245_9 : List Nat := [0x562e84b5e8534110806,0xa6289024009e1384d5f8a14309c0a,0x15e56e01,0x4ea58124569204358264d1944c7a0a,0x11c53914549184815a4916043519449560c,0x3549d56c02,0x25892421022605c16d802557d428900b,0x3c0dbda2007f4082a06,0xd03cf73de22879635034202a09,0xf655c0b08a03,0x7a21046f63de2308a2258e08,0x4410d8c1fbdc04,0x110420a8340fbda2188540bde09,0x110420a83c0d3d6f507a1e5976559206d03423d80f,0x5915708802,0x16659a01,0x3ed30160495865692043583445134647a0c,0x652574d254643348cd592fa72cea383d0f338d9e0f,0x6453567a58653388dd592fa70cda343b8ed38a520f,0x2a8502dd24410582e58b438b009,0x2884e2757a285a42b09e160a42e58b431000d,0x1690ff5e84d698b81658a068ae09,0x7d478781a8800e0360ad5e220422083a07d094086210,0x5a3680fc970fa8f33f6ada808]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk245_9 : checkRows book245 10 703 rows245_9=true := by decide +kernel

def rows245_10 : List Nat := [0x136fe1385b16a50147301204910d50d174413e0e,0x4dbf84f1705b9696bcc05e1464917250120435434451b4593a13,0x6c1ae32369674de2fb666aa348cb4d2fd888db523119464a74db5ab38db017,0x6c1aa32365674de30b6a6ba388db512fd888cb4e3019063d9f6cb6c9d5ac8f5ab38db01b,0x975594d0f69636937b6e8ecbe94a3264584cea38310c367364cd270301aa6a0c76d4e36ab3c1d,0x25d565343c254d94dedba3b2fa568d9956798ecda34300bf67368ce272311ae6b0c76d4e36ab3c1e,0xf0cd8bf670c56118ed3d88d433831db49d33c6cdb16e5b76ad5814,0xc22f8f63c5a83d5ba3b8c63e5b56ad9c0c,0xf6ce8c3670c063d84d4b516234ccd5bccf2746cdb16e5b631db56ad5816,0x16f99601,0x16f99801,0x1700c801,0x17035601,0x170a3a01,0x170a5a01,0x3e8eccf235564be3db3a8e3343d3515b34c9c5ab724e371da813,0x36cda9b28ddb12f9a88d0c02fd9c30dcc6bb515b364d3271724e36adc571cde18,0x1738ee01,0x1739aa01,0x173a5401,0x5cb7553402,0x175a5601,0x175a5801,0x17636a01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk245_10 : checkRows book245 10 727 rows245_10=true := by decide +kernel

def rows245_11 : List Nat := [0x176a7201,0x176b3801,0xfa3cb3c8e5592f8f0cda356add1785df724e373da810,0x1788be01,0x1715ab7959c03,0x1798c201,0x1798c401,0x17a23801,0x17a9ac01,0x138dc97b4be03,0x5d37bdb002,0x17c23201,0x17c9b201,0x17d36601,0x17db6c01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk245_11 : checkRows book245 10 751 rows245_11=true := by decide +kernel

def lastUnits245 := digits 10 4 0xbbeeebf2fd
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict245 : checkReasons book245 766 623 lastUnits245 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude245 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 245=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=3) h hc bp eq (by decide +kernel)
  let v := truth Z a245
  have hbase : ValidThrough v book245 487 := book_start Z h hc z eq _ _ _ _ initialClauses245
  have h0 : ValidThrough v book245 511 := rows_sound hbase rows245_0 rowsOk245_0
  have h1 : ValidThrough v book245 535 := rows_sound h0 rows245_1 rowsOk245_1
  have h2 : ValidThrough v book245 559 := rows_sound h1 rows245_2 rowsOk245_2
  have h3 : ValidThrough v book245 583 := rows_sound h2 rows245_3 rowsOk245_3
  have h4 : ValidThrough v book245 607 := rows_sound h3 rows245_4 rowsOk245_4
  have h5 : ValidThrough v book245 631 := rows_sound h4 rows245_5 rowsOk245_5
  have h6 : ValidThrough v book245 655 := rows_sound h5 rows245_6 rowsOk245_6
  have h7 : ValidThrough v book245 679 := rows_sound h6 rows245_7 rowsOk245_7
  have h8 : ValidThrough v book245 703 := rows_sound h7 rows245_8 rowsOk245_8
  have h9 : ValidThrough v book245 727 := rows_sound h8 rows245_9 rowsOk245_9
  have h10 : ValidThrough v book245 751 := rows_sound h9 rows245_10 rowsOk245_10
  have h11 : ValidThrough v book245 766 := rows_sound h10 rows245_11 rowsOk245_11
  exact book_end h11 _ _ conflict245
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
