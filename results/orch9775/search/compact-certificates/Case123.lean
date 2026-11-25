import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a123 : Array Fact := #[(.lab 0 0 0),(.lab 0 0 2),(.avoid 0 1102 0),(.res 0 8),(.res 1 8),(.res 2 8),(.res 0 9),(.res 1 9),(.res 2 9),(.res 0 10),(.res 1 10),(.res 2 10),(.res 0 11),(.res 1 11),(.res 2 11),(.lab 1 0 1),(.lab 2 0 2),(.lab 2 1 2),(.lab 2 2 2),(.lab 2 3 2),(.lab 2 4 2),(.lab 5 0 5),(.lab 5 0 1),(.avoid 5 1102 0),(.lab 6 0 0),(.lab 6 0 1),(.lab 6 0 2),(.lab 6 0 5),(.avoid 6 314 0),(.avoid 6 541 0),(.live 8 1),(.lab 8 0 9),(.common 8 9),(.lab 8 0 10),(.common 8 10),(.lab 8 0 11),(.common 8 11),(.live 8 2),(.lab 8 1 9),(.lab 8 1 10),(.lab 8 1 11),(.live 8 3),(.lab 8 2 9),(.lab 8 2 10),(.lab 8 2 11),(.live 8 4),(.lab 8 3 9),(.lab 8 3 10),(.lab 8 3 11),(.lab 8 4 10),(.lab 8 4 11),(.avoid 8 1548 0),(.avoid 8 1548 1),(.avoid 8 1548 2),(.avoid 8 1548 3),(.avoid 8 1548 4),(.avoid 8 7174 0),(.avoid 8 7174 1),(.avoid 8 7174 2),(.avoid 8 7174 3),(.avoid 8 7174 4),(.avoid 8 7812 0),(.avoid 8 7812 1),(.avoid 8 7812 2),(.avoid 8 7812 3),(.avoid 8 7812 4),(.see 8 0 7426 0),(.see 8 0 7426 1),(.see 8 0 7426 2),(.see 8 0 7426 3),(.see 8 0 7426 4),(.see 8 0 9992 0),(.see 8 0 9992 1),(.see 8 0 9992 2),(.see 8 0 9992 3),(.see 8 0 9992 4),(.see 8 6 7426 0),(.see 8 6 7426 1),(.see 8 6 7426 2),(.see 8 6 7426 3),(.see 8 6 7426 4),(.see 8 6 9992 0),(.see 8 6 9992 1),(.see 8 6 9992 2),(.see 8 6 9992 3),(.see 8 6 9992 4),(.diff 0 8 9),(.diff 1 8 9),(.diff 2 8 9),(.diff 0 8 10),(.diff 1 8 10),(.diff 2 8 10),(.diff 0 8 11),(.diff 1 8 11),(.diff 2 8 11),(.live 9 1),(.lab 9 0 7),(.lab 9 0 8),(.lab 9 0 10),(.common 9 10),(.common 9 11),(.live 9 2),(.lab 9 1 7),(.lab 9 1 8),(.lab 9 1 10),(.lab 9 1 11),(.live 9 3),(.lab 9 2 7),(.lab 9 2 8),(.lab 9 2 10),(.live 9 4),(.lab 9 3 7),(.lab 9 3 8),(.lab 9 3 10),(.avoid 9 432 0),(.avoid 9 432 1),(.avoid 9 432 2),(.avoid 9 432 3),(.avoid 9 432 4),(.avoid 9 2213 0),(.avoid 9 2213 1),(.avoid 9 2213 2),(.avoid 9 2213 3),(.avoid 9 2213 4),(.avoid 9 5316 0),(.avoid 9 5316 1),(.avoid 9 5316 2),(.avoid 9 5316 3),(.avoid 9 5316 4),(.see 9 1 5008 0),(.see 9 1 5008 1),(.see 9 1 5008 2),(.see 9 1 5008 3),(.see 9 1 5008 4),(.see 9 1 6789 0),(.see 9 1 6789 1),(.see 9 1 6789 2),(.see 9 1 6789 3),(.see 9 1 6789 4),(.see 9 1 7812 0),(.see 9 1 7812 1),(.see 9 1 7812 2),(.see 9 1 7812 3),(.see 9 1 7812 4),(.see 9 1 16256 0),(.see 9 1 16256 1),(.see 9 1 16256 2),(.see 9 1 16256 3),(.see 9 1 16256 4),(.see 9 6 7812 0),(.see 9 6 7812 1),(.see 9 6 7812 2),(.see 9 6 7812 3),(.see 9 6 7812 4),(.diff 0 9 8),(.diff 1 9 8),(.diff 2 9 8),(.diff 0 9 10),(.diff 1 9 10),(.diff 2 9 10),(.live 10 1),(.lab 10 0 8),(.lab 10 0 11),(.common 10 11),(.live 10 2),(.lab 10 1 8),(.lab 10 1 11),(.live 10 3),(.lab 10 2 8),(.lab 10 2 11),(.live 10 4),(.lab 10 3 8),(.lab 10 3 11),(.avoid 10 2338 0),(.avoid 10 2338 1),(.avoid 10 2338 2),(.avoid 10 2338 3),(.avoid 10 2338 4),(.see 10 0 1290 0),(.see 10 0 1290 1),(.see 10 0 1290 2),(.see 10 0 1290 3),(.see 10 0 1290 4),(.see 10 0 7426 0),(.see 10 0 7426 1),(.see 10 0 7426 2),(.see 10 0 7426 3),(.see 10 0 7426 4),(.see 10 4 7426 0),(.see 10 4 7426 1),(.see 10 4 7426 2),(.see 10 4 7426 3),(.see 10 4 7426 4),(.diff 0 10 8),(.diff 1 10 8),(.diff 2 10 8),(.diff 0 10 11),(.diff 1 10 11),(.diff 2 10 11),(.lab 11 0 11),(.live 11 1),(.lab 11 0 7),(.lab 11 0 8),(.lab 11 0 9),(.lab 11 0 10),(.lab 11 0 12),(.lab 11 1 11),(.live 11 2),(.lab 11 1 8),(.lab 11 1 9),(.lab 11 1 10),(.lab 11 1 12),(.lab 11 2 11),(.live 11 3),(.lab 11 2 8),(.lab 11 2 9),(.lab 11 2 10),(.lab 11 2 12),(.lab 11 3 11),(.live 11 4),(.lab 11 3 7),(.lab 11 3 8),(.lab 11 3 9),(.lab 11 3 10),(.avoid 11 1290 0),(.avoid 11 1290 1),(.avoid 11 1290 2),(.avoid 11 1290 3),(.avoid 11 1290 4),(.avoid 11 4757 0),(.avoid 11 4757 1),(.avoid 11 4757 2),(.avoid 11 4757 3),(.avoid 11 4757 4),(.avoid 11 5190 0),(.avoid 11 5190 1),(.avoid 11 5190 2),(.avoid 11 5190 3),(.avoid 11 5190 4),(.see 11 3 6789 0),(.see 11 3 6789 1),(.see 11 3 6789 2),(.see 11 3 6789 3),(.see 11 3 6789 4),(.see 11 3 7174 0),(.see 11 3 7174 1),(.see 11 3 7174 2),(.see 11 3 7174 3),(.see 11 3 7174 4),(.see 11 4 7426 0),(.see 11 4 7426 1),(.see 11 4 7426 2),(.see 11 4 7426 3),(.see 11 4 7426 4),(.see 11 4 16256 0),(.see 11 4 16256 1),(.see 11 4 16256 2),(.see 11 4 16256 3),(.see 11 4 16256 4),(.see 11 6 2338 0),(.see 11 6 2338 1),(.see 11 6 2338 2),(.see 11 6 2338 3),(.see 11 6 2338 4),(.see 11 6 16256 0),(.see 11 6 16256 1),(.see 11 6 16256 2),(.see 11 6 16256 3),(.see 11 6 16256 4),(.diff 0 11 8),(.diff 1 11 8),(.diff 2 11 8),(.diff 0 11 9),(.diff 1 11 9),(.diff 2 11 9),(.reader false 0 0),(.es false 0 0),(.es false 0 2),(.reader false 3 0),(.es false 3 1),(.reader false 5 0),(.reader false 5 1),(.reader false 5 2),(.reader false 5 3),(.reader false 5 4),(.es false 5 2),(.reader false 13 0),(.es false 13 1),(.es false 13 5),(.reader false 16 0),(.es false 16 0),(.es false 16 2),(.reader false 17 0),(.es false 17 1),(.es false 17 5),(.reader false 18 0),(.reader true 0 0),(.reader true 0 1),(.reader true 0 2),(.reader true 0 3),(.reader true 0 4),(.reader true 3 0),(.reader true 3 1),(.reader true 3 2),(.reader true 3 3),(.reader true 3 4),(.reader true 5 0),(.reader true 5 1),(.reader true 5 2),(.reader true 5 3),(.reader true 5 4),(.reader true 13 0),(.reader true 13 1),(.reader true 13 2),(.reader true 13 3),(.reader true 13 4),(.reader true 16 0),(.reader true 16 1),(.reader true 16 2),(.reader true 16 3),(.reader true 16 4),(.reader true 17 0),(.reader true 17 1),(.reader true 17 2),(.reader true 17 3),(.reader true 17 4),(.es true 17 11),(.reader true 18 0),(.reader true 18 1),(.reader true 18 2),(.reader true 18 3),(.reader true 18 4),(.es true 18 11),(.gate 0 5),(.gate 0 16),(.gate 3 13),(.gate 3 17),(.gate 5 16),(.gate 13 17),(.gate 17 18)]
def r123 : List Scheme := [(.self 0 0),(.exposure 0 1102),(.avoidNot 0 2 1102 0),(.self 1 0),(.self 2 0),(.self 2 1),(.self 2 2),(.self 2 3),(.self 2 4),(.self 5 0),(.exposure 5 1102),(.avoidNot 5 1 1102 0),(.exposure 6 314),(.avoidNot 6 1 314 0),(.avoidNot 6 5 314 0),(.exposure 6 541),(.avoidNot 6 0 541 0),(.avoidNot 6 2 541 0),(.earlier 8 1),(.earlier 8 2),(.earlier 8 3),(.allRes 8 0),(.allRes 8 1),(.allRes 8 2),(.exposure 8 1548),(.avoidNot 8 9 1548 0),(.avoidNot 8 10 1548 0),(.avoidNot 8 9 1548 1),(.avoidNot 8 10 1548 1),(.avoidNot 8 9 1548 2),(.avoidNot 8 10 1548 2),(.avoidLive 8 1548 3),(.avoidNot 8 9 1548 3),(.avoidNot 8 10 1548 3),(.avoidLive 8 1548 4),(.avoidNot 8 10 1548 4),(.exposure 8 7174),(.avoidNot 8 10 7174 0),(.avoidNot 8 11 7174 0),(.avoidNot 8 10 7174 1),(.avoidNot 8 11 7174 1),(.avoidNot 8 10 7174 2),(.avoidNot 8 11 7174 2),(.avoidLive 8 7174 3),(.avoidNot 8 10 7174 3),(.avoidNot 8 11 7174 3),(.avoidLive 8 7174 4),(.avoidNot 8 10 7174 4),(.avoidNot 8 11 7174 4),(.exposure 8 7812),(.avoidNot 8 11 7812 0),(.avoidNot 8 10 7812 1),(.avoidNot 8 10 7812 2),(.avoidLive 8 7812 3),(.avoidLive 8 7812 4),(.exactAt 8 0 7426),(.seeLab 8 0 10 7426 0),(.seeLab 8 0 11 7426 0),(.seeLab 8 0 10 7426 1),(.seeLab 8 0 11 7426 1),(.seeLab 8 0 10 7426 2),(.seeLab 8 0 11 7426 2),(.seeLive 8 0 7426 3),(.seeLab 8 0 10 7426 3),(.seeLab 8 0 11 7426 3),(.seeLive 8 0 7426 4),(.exactAt 8 0 9992),(.seeLab 8 0 9 9992 0),(.seeLab 8 0 10 9992 0),(.seeLab 8 0 9 9992 1),(.seeLab 8 0 10 9992 1),(.seeLab 8 0 9 9992 2),(.seeLab 8 0 10 9992 2),(.seeLive 8 0 9992 3),(.seeLab 8 0 9 9992 3),(.seeLab 8 0 10 9992 3),(.seeLive 8 0 9992 4),(.exactAt 8 6 7426),(.seeLab 8 6 10 7426 0),(.seeLab 8 6 11 7426 0),(.seeLab 8 6 10 7426 1),(.seeLab 8 6 10 7426 2),(.seeLab 8 6 11 7426 2),(.seeLive 8 6 7426 3),(.seeLab 8 6 10 7426 3),(.seeLab 8 6 11 7426 3),(.seeLive 8 6 7426 4),(.seeLab 8 6 10 7426 4),(.seeLab 8 6 11 7426 4),(.exactAt 8 6 9992),(.seeLab 8 6 10 9992 0),(.seeLab 8 6 9 9992 1),(.seeLab 8 6 10 9992 2),(.seeLive 8 6 9992 3),(.seeLab 8 6 10 9992 3),(.seeLive 8 6 9992 4),(.seeLab 8 6 10 9992 4),(.diffX 0 8 9),(.diffC 0 8 9),(.diffX 1 8 9),(.diffC 1 8 9),(.diffX 2 8 9),(.diffC 2 8 9),(.adjacentCommon 8 9 6),(.residual 8 9 0 1),(.residual 8 9 0 2),(.residual 8 9 0 3),(.residual 8 9 1 2),(.residual 8 9 1 3),(.residual 8 9 2 3),(.diffX 0 8 10),(.diffC 0 8 10),(.diffX 1 8 10),(.diffC 1 8 10),(.diffX 2 8 10),(.diffC 2 8 10),(.adjacentCommon 8 10 0),(.residual 8 10 0 1),(.residual 8 10 0 2),(.residual 8 10 0 3),(.residual 8 10 0 4),(.residual 8 10 1 2),(.residual 8 10 1 3),(.residual 8 10 1 4),(.residual 8 10 2 3),(.residual 8 10 2 4),(.residual 8 10 3 4),(.diffX 0 8 11),(.diffC 0 8 11),(.diffX 1 8 11),(.diffC 1 8 11),(.diffX 2 8 11),(.diffC 2 8 11),(.adjacentCommon 8 11 6),(.residual 8 11 0 1),(.residual 8 11 0 2),(.residual 8 11 0 3),(.residual 8 11 1 2),(.residual 8 11 1 3),(.residual 8 11 2 3),(.earlier 9 1),(.earlier 9 2),(.earlier 9 3),(.allRes 9 0),(.allRes 9 1),(.allRes 9 2),(.exposure 9 432),(.avoidNot 9 7 432 0),(.avoidNot 9 8 432 0),(.avoidNot 9 7 432 1),(.avoidNot 9 8 432 1),(.avoidNot 9 7 432 2),(.avoidNot 9 8 432 2),(.avoidLive 9 432 3),(.avoidNot 9 7 432 3),(.avoidNot 9 8 432 3),(.avoidLive 9 432 4),(.exposure 9 2213),(.avoidNot 9 7 2213 0),(.avoidNot 9 11 2213 1),(.avoidLive 9 2213 2),(.avoidLive 9 2213 3),(.avoidLive 9 2213 4),(.exposure 9 5316),(.avoidNot 9 7 5316 0),(.avoidNot 9 10 5316 0),(.avoidNot 9 7 5316 1),(.avoidNot 9 10 5316 1),(.avoidNot 9 7 5316 2),(.avoidNot 9 10 5316 2),(.avoidLive 9 5316 3),(.avoidNot 9 10 5316 3),(.avoidLive 9 5316 4),(.exactAt 9 1 5008),(.seeLab 9 1 7 5008 0),(.seeLab 9 1 8 5008 0),(.seeLab 9 1 7 5008 1),(.seeLab 9 1 8 5008 1),(.seeLab 9 1 7 5008 2),(.seeLab 9 1 8 5008 2),(.seeLive 9 1 5008 3),(.seeLab 9 1 7 5008 3),(.seeLab 9 1 8 5008 3),(.seeLive 9 1 5008 4),(.exactAt 9 1 6789),(.seeLab 9 1 7 6789 0),(.seeLab 9 1 11 6789 1),(.seeLive 9 1 6789 2),(.seeLive 9 1 6789 3),(.seeLive 9 1 6789 4),(.exactAt 9 1 7812),(.seeLab 9 1 7 7812 0),(.seeLab 9 1 10 7812 0),(.seeLab 9 1 7 7812 1),(.seeLab 9 1 10 7812 1),(.seeLab 9 1 7 7812 2),(.seeLab 9 1 10 7812 2),(.seeLive 9 1 7812 3),(.seeLab 9 1 10 7812 3),(.seeLive 9 1 7812 4),(.exactAt 9 1 16256),(.seeLab 9 1 10 16256 0),(.seeLab 9 1 10 16256 1),(.seeLab 9 1 10 16256 2),(.seeLab 9 1 7 16256 3),(.seeLive 9 1 16256 4),(.exactAt 9 6 7812),(.seeLab 9 6 10 7812 0),(.seeLab 9 6 10 7812 1),(.seeLab 9 6 10 7812 2),(.seeLab 9 6 7 7812 3),(.seeLive 9 6 7812 4),(.diffX 0 9 8),(.diffC 0 9 8),(.diffX 1 9 8),(.diffC 1 9 8),(.diffX 2 9 8),(.diffC 2 9 8),(.residual 9 8 0 1),(.residual 9 8 0 2),(.residual 9 8 0 3),(.residual 9 8 1 2),(.residual 9 8 1 3),(.residual 9 8 2 3),(.diffX 0 9 10),(.diffC 0 9 10),(.diffX 1 9 10),(.diffC 1 9 10),(.diffX 2 9 10),(.diffC 2 9 10),(.adjacentCommon 9 10 5),(.residual 9 10 0 1),(.residual 9 10 0 2),(.residual 9 10 0 3),(.residual 9 10 1 2),(.residual 9 10 1 3),(.residual 9 10 2 3),(.adjacentCommon 9 11 6),(.earlier 10 1),(.earlier 10 2),(.allRes 10 0),(.allRes 10 1),(.allRes 10 2),(.exposure 10 2338),(.avoidNot 10 8 2338 0),(.avoidNot 10 11 2338 0),(.avoidNot 10 8 2338 1),(.avoidNot 10 11 2338 1),(.avoidLive 10 2338 2),(.avoidNot 10 8 2338 2),(.avoidNot 10 11 2338 2),(.avoidLive 10 2338 3),(.avoidNot 10 8 2338 3),(.avoidNot 10 11 2338 3),(.avoidLive 10 2338 4),(.exactAt 10 0 1290),(.seeLab 10 0 8 1290 0),(.seeLab 10 0 8 1290 1),(.seeLive 10 0 1290 2),(.seeLive 10 0 1290 3),(.seeLive 10 0 1290 4),(.exactAt 10 0 7426),(.seeLab 10 0 8 7426 0),(.seeLab 10 0 11 7426 0),(.seeLab 10 0 8 7426 1),(.seeLab 10 0 11 7426 1),(.seeLive 10 0 7426 2),(.seeLab 10 0 8 7426 2),(.seeLab 10 0 11 7426 2),(.seeLive 10 0 7426 3),(.seeLab 10 0 8 7426 3),(.seeLab 10 0 11 7426 3),(.seeLive 10 0 7426 4),(.exactAt 10 4 7426),(.seeLab 10 4 8 7426 0),(.seeLab 10 4 11 7426 0),(.seeLab 10 4 8 7426 1),(.seeLab 10 4 11 7426 1),(.seeLive 10 4 7426 2),(.seeLab 10 4 8 7426 2),(.seeLab 10 4 11 7426 2),(.seeLive 10 4 7426 3),(.seeLab 10 4 8 7426 3),(.seeLab 10 4 11 7426 3),(.seeLive 10 4 7426 4),(.diffX 0 10 8),(.diffC 0 10 8),(.diffX 1 10 8),(.diffC 1 10 8),(.diffX 2 10 8),(.diffC 2 10 8),(.residual 10 8 0 1),(.residual 10 8 0 2),(.residual 10 8 0 3),(.residual 10 8 1 2),(.residual 10 8 1 3),(.residual 10 8 2 3),(.diffX 0 10 11),(.diffC 0 10 11),(.diffX 1 10 11),(.diffC 1 10 11),(.diffX 2 10 11),(.diffC 2 10 11),(.adjacentCommon 10 11 4),(.residual 10 11 0 1),(.residual 10 11 0 2),(.residual 10 11 0 3),(.residual 10 11 1 2),(.residual 10 11 1 3),(.residual 10 11 2 3),(.self 11 0),(.self 11 1),(.earlier 11 1),(.self 11 2),(.earlier 11 2),(.self 11 3),(.allRes 11 0),(.allRes 11 1),(.allRes 11 2),(.exposure 11 1290),(.avoidNot 11 8 1290 0),(.avoidNot 11 10 1290 0),(.avoidNot 11 8 1290 1),(.avoidNot 11 10 1290 1),(.avoidNot 11 8 1290 2),(.avoidNot 11 10 1290 2),(.avoidLive 11 1290 3),(.avoidNot 11 8 1290 3),(.avoidNot 11 10 1290 3),(.avoidLive 11 1290 4),(.exposure 11 4757),(.avoidNot 11 9 4757 0),(.avoidNot 11 12 4757 0),(.avoidNot 11 9 4757 1),(.avoidNot 11 12 4757 1),(.avoidLive 11 4757 2),(.avoidNot 11 9 4757 2),(.avoidNot 11 12 4757 2),(.avoidLive 11 4757 3),(.avoidNot 11 9 4757 3),(.avoidLive 11 4757 4),(.exposure 11 5190),(.avoidNot 11 12 5190 0),(.avoidNot 11 10 5190 1),(.avoidLive 11 5190 2),(.avoidLive 11 5190 3),(.avoidLive 11 5190 4),(.exactAt 11 3 6789),(.seeLab 11 3 7 6789 0),(.seeLab 11 3 9 6789 0),(.seeLab 11 3 12 6789 0),(.seeLab 11 3 9 6789 1),(.seeLab 11 3 12 6789 1),(.seeLive 11 3 6789 2),(.seeLab 11 3 9 6789 2),(.seeLab 11 3 12 6789 2),(.seeLive 11 3 6789 3),(.seeLab 11 3 7 6789 3),(.seeLab 11 3 9 6789 3),(.seeLive 11 3 6789 4),(.exactAt 11 3 7174),(.seeLab 11 3 12 7174 0),(.seeLab 11 3 10 7174 1),(.seeLive 11 3 7174 2),(.seeLive 11 3 7174 3),(.seeLive 11 3 7174 4),(.exactAt 11 4 7426),(.seeLab 11 4 8 7426 0),(.seeLab 11 4 10 7426 0),(.seeLab 11 4 8 7426 1),(.seeLab 11 4 10 7426 1),(.seeLab 11 4 8 7426 2),(.seeLab 11 4 10 7426 2),(.seeLive 11 4 7426 3),(.seeLab 11 4 8 7426 3),(.seeLab 11 4 10 7426 3),(.seeLive 11 4 7426 4),(.exactAt 11 4 16256),(.seeLab 11 4 7 16256 0),(.seeLab 11 4 8 16256 0),(.seeLab 11 4 9 16256 0),(.seeLab 11 4 9 16256 1),(.seeLab 11 4 10 16256 1),(.seeLive 11 4 16256 2),(.seeLab 11 4 9 16256 2),(.seeLive 11 4 16256 3),(.seeLab 11 4 7 16256 3),(.seeLive 11 4 16256 4),(.exactAt 11 6 2338),(.seeLab 11 6 8 2338 0),(.seeLab 11 6 8 2338 1),(.seeLive 11 6 2338 2),(.seeLive 11 6 2338 3),(.seeLive 11 6 2338 4),(.exactAt 11 6 16256),(.seeLab 11 6 8 16256 0),(.seeLab 11 6 9 16256 1),(.seeLab 11 6 8 16256 2),(.seeLive 11 6 16256 3),(.seeLive 11 6 16256 4),(.diffX 0 11 8),(.diffC 0 11 8),(.diffX 1 11 8),(.diffC 1 11 8),(.diffX 2 11 8),(.diffC 2 11 8),(.residual 11 8 0 1),(.residual 11 8 0 2),(.residual 11 8 0 3),(.residual 11 8 1 2),(.residual 11 8 1 3),(.residual 11 8 2 3),(.diffX 0 11 9),(.diffC 0 11 9),(.diffX 1 11 9),(.diffC 1 11 9),(.diffX 2 11 9),(.diffC 2 11 9),(.residual 11 9 0 1),(.residual 11 9 0 2),(.residual 11 9 0 3),(.residual 11 9 1 2),(.residual 11 9 1 3),(.residual 11 9 2 3),(.readerAny false 0),(.readerLab false 0 0 0 true),(.readerLab false 0 0 2 false),(.readerAny false 3),(.readerLab false 3 0 1 true),(.readerAny false 5),(.readerLab false 5 0 2 true),(.readerLab false 5 1 2 true),(.readerLab false 5 2 2 true),(.readerLab false 5 3 2 true),(.readerLab false 5 4 2 true),(.readerAny false 13),(.readerLab false 13 0 1 false),(.readerLab false 13 0 5 true),(.readerAny false 16),(.readerLab false 16 0 0 false),(.readerLab false 16 0 2 false),(.readerAny false 17),(.readerLab false 17 0 1 false),(.readerLab false 17 0 5 false),(.readerAny false 18),(.readerAny true 0),(.readerLive true 0 2),(.readerLive true 0 3),(.readerLive true 0 4),(.readerAny true 3),(.readerLive true 3 2),(.readerLive true 3 3),(.readerLive true 3 4),(.readerAny true 5),(.readerLive true 5 2),(.readerLive true 5 3),(.readerLive true 5 4),(.readerAny true 13),(.readerLive true 13 2),(.readerLive true 13 3),(.readerLive true 13 4),(.readerAny true 16),(.readerLive true 16 2),(.readerLive true 16 3),(.readerLive true 16 4),(.readerAny true 17),(.readerLab true 17 1 11 false),(.readerLive true 17 2),(.readerLive true 17 3),(.readerLive true 17 4),(.readerAny true 18),(.readerLab true 18 0 11 true),(.readerLab true 18 1 11 true),(.readerLab true 18 2 11 true),(.readerLab true 18 3 11 true),(.readerLive true 18 4),(.eqLab false 0 5 2 false),(.gateEq true 0 5 0),(.gateEq true 0 5 1),(.eqLab false 0 16 0 true),(.gateEq true 0 16 0),(.gateEq true 0 16 1),(.eqLab false 3 13 1 true),(.gateEq true 3 13 1),(.eqLab false 3 17 1 true),(.gateEq true 3 17 0),(.eqLab false 5 16 2 true),(.gateEq true 5 16 0),(.gateEq true 5 16 1),(.eqLab false 13 17 5 true),(.gateEq true 13 17 0),(.gateEq false 17 18 0),(.eqLab true 17 18 11 false)]

def table123_0 : List Nat := [65,321,0x20102,0x7c1,0x841,0x8c1,0x941,0x9c1,0xa41,0xac1,0xbc1,0x2c0b82,0xe41,0x320e02,0x360e02,0xec1]
def table123_1 : List Nat := [0x300e82,0x340e82,0x3d1282,0x4b1482,0x531682,0x71682,0x91682,0xb1682,0x1bc6d1ac6919c5,0x3e1982,0x421982,0x4c1a02,0x4e1a02,0x541a82,0x561a82,0x531b02]
def table123_2 : List Nat := [0x5c1b02,0x5e1b02,0x5b1b82,0x621b82,0x1e4771d4731c45,0x421c02,0x461c02,0x4e1c82,0x501c82,0x561d02,0x581d02,0x531d82,0x5e1d82,0x601d82,0x5b1e02,0x621e02]
def table123_3 : List Nat := [0x641e02,0x20c811fc7d1ec5,0x461e82,0x4e1f02,0x561f82,0x532002,0x5b2082,0x2348b224872145,0x432102,0x462102,0x4f2182,0x502182,0x572202,0x582202,0x532282,0x5f2282]
def table123_4 : List Nat := [0x602282,0x5b2302,0x25c9524c9123c5,0x3e2382,0x432382,0x4c2402,0x4f2402,0x542482,0x572482,0x532502,0x5c2502,0x5f2502,0x5b2582,0x2849f2749b2645,0x422602,0x472602]
def table123_5 : List Nat := [0x4e2682,0x562702,0x592702,0x532782,0x5e2782,0x612782,0x5b2802,0x622802,0x652802,0x2aca929ca528c5,0x422882,0x4d2902,0x562982,0x532a02,0x5e2a02,0x5b2a82]
def table123_6 : List Nat := [0x622a82,0x72b02,0xc2b02,0x92b82,0xe2b82,0xb2c02,0x102c02,0x1041,0x2c4af2b44d0fc3c1007,0x2c4af2b4550fc4a1007,0x2c4af2b45d0fc521007,0x2c4af2b4551344a1007,0x2c4af2b45d134521007,0x2c4af2b45d154521007,0x72c82,0x122c82]
def table123_7 : List Nat := [0x92d02,0x142d02,0xb2d82,0x162d82,0x1141,0x2dcb52cc4f10c3c1107,0x2dcb52cc5710c4a1107,0x2dcb52cc5f10c521107,0x2dcb52cc6310c5a1107,0x2dcb52cc5713c4a1107,0x2dcb52cc5f13c521107,0x2dcb52cc6313c5a1107,0x2dcb52cc5f15c521107,0x2dcb52cc6315c5a1107,0x2dcb52cc6317c5a1107,0x72e02]
def table123_8 : List Nat := [0x182e02,0x92e82,0x1a2e82,0xb2f02,0x1c2f02,0x1241,0x2f4bb2e45111c3c1207,0x2f4bb2e45911c4a1207,0x2f4bb2e46111c521207,0x2f4bb2e4591444a1207,0x2f4bb2e461144521207,0x2f4bb2e461164521207,0xbf3282,0xcb3502,0xd53702,0xd3702]
def table123_9 : List Nat := [0xf3702,0x113702,0x3b4eb3a4e73945,0xc03902,0xc23902,0xcc3982,0xce3982,0xd63a02,0xd83a02,0xd53a82,0xde3a82,0xe03a82,0xdd3b02,0x3dcf53ccf13bc5,0xc03b82,0xd23c02]
def table123_10 : List Nat := [0xcb3c82,0xd53d02,0xdd3d82,0x404ff3f4fb3e45,0xc03e02,0xc43e02,0xcc3e82,0xd03e82,0xd63f02,0xda3f02,0xd53f82,0xe23f82,0xdd4002,0x42d0941d0540c5,0xc14082,0xc24082]
def table123_11 : List Nat := [0xcd4102,0xce4102,0xd74182,0xd84182,0xd54202,0xdf4202,0xe04202,0xdd4282,0x455134450f4345,0xc14302,0xd24382,0xcb4402,0xd54482,0xdd4502,0x47d1d46d1945c5,0xc14582]
def table123_12 : List Nat := [0xc44582,0xcd4602,0xd04602,0xd74682,0xda4682,0xd54702,0xe24702,0xdd4782,0x4a527495234845,0xc44802,0xd04882,0xda4902,0xdf4982,0xdd4a02,0x4cd314bd2d4ac5,0xc44a82]
def table123_13 : List Nat := [0xd04b02,0xda4b82,0xde4c02,0xdd4c82,0xd4d02,0x64d02,0xf4d82,0x84d82,0x114e02,0xa4e02,0x4e5374d4cf30cbe1007,0x4e5374d4d930cca1007,0x4e5374d4e130cd41007,0x4e5374d4d933cca1007,0x4e5374d4e133cd41007,0x4e5374d4e1364d41007]
def table123_14 : List Nat := [0xd4e82,0x124e82,0xf4f02,0x144f02,0x114f82,0x164f82,0x31c1,0x4fd3d4ecd1314be3187,0x4fd3d4ecdb314ca3187,0x4fd3d4ece3314d43187,0x4fd3d4ecdb344ca3187,0x4fd3d4ece3344d43187,0x4fd3d4ece336cd43187,0x3241,0x1415202,0x1495382]
def table123_15 : List Nat := [0x135502,0x155502,0x175502,0x58d6157d5d56c5,0x1425682,0x1445682,0x14a5702,0x14c5702,0x1495782,0x1505782,0x1525782,0x14f5802,0x1565802,0x1585802,0x1555882,0x5b56b5a5675945]
def table123_16 : List Nat := [0x1435902,0x14b5982,0x1495a02,0x14f5a82,0x1555b02,0x5dd755cd715bc5,0x1435b82,0x1445b82,0x14b5c02,0x14c5c02,0x1495c82,0x1515c82,0x1525c82,0x14f5d02,0x1575d02,0x1585d02]
def table123_17 : List Nat := [0x1555d82,0x6057f5f57b5e45,0x1425e02,0x1455e02,0x14a5e82,0x14d5e82,0x1495f02,0x1505f02,0x1535f02,0x14f5f82,0x1565f82,0x1595f82,0x1556002,0x136082,0x66082,0x156102]
def table123_18 : List Nat := [0x86102,0x176182,0xa6182,0x61d8560d4b50d401107,0x61d8560d5150d481107,0x61d8560d5750d4e1107,0x61d8560d5152d481107,0x61d8560d5752d4e1107,0x61d8560d575454e1107,0x136202,0x186202,0x156282,0x1a6282,0x176302,0x1c6302,0x51c1]
def table123_19 : List Nat := [0x6358b6254d515405187,0x6358b62553515485187,0x6358b625595154e5187,0x6358b62553535485187,0x6358b625595354e5187,0x6358b6255954d4e5187,0x63c1,0x6741,0x1916782,0x6a41,0x19f6a82,0x6d41,0x196d82,0x1b6d82,0x1d6d82,0x725c7715c37045]
def table123_20 : List Nat := [0x1947002,0x1987002,0x1a07082,0x1a47082,0x1ac7102,0x1b07102,0x1ab7182,0x1ba7182,0x1be7182,0x1b77202,0x74dd173dcd72c5,0x1967282,0x19a7282,0x1a27302,0x1a67302,0x19f7382]
def table123_21 : List Nat := [0x1ae7382,0x1b27382,0x1ab7402,0x1bc7402,0x1b77482,0x775db765d77545,0x19a7502,0x1a47582,0x19f7602,0x1ab7682,0x1b77702,0x79de578de177c5,0x1937782,0x1967782,0x19b7782,0x1a27802]
def table123_22 : List Nat := [0x1a77802,0x19f7882,0x1ae7882,0x1b37882,0x1ab7902,0x1b97902,0x1bc7902,0x1b77982,0x7c5ef7b5eb7a45,0x19b7a02,0x1a47a82,0x19f7b02,0x1ab7b82,0x1b77c02,0x7edf97ddf57cc5,0x1947c82]
def table123_23 : List Nat := [0x1997c82,0x1a07d02,0x1a57d02,0x1ac7d82,0x1b17d82,0x1ab7e02,0x1ba7e02,0x1bf7e02,0x1b77e82,0x81603805ff7f45,0x1927f02,0x1947f02,0x1967f02,0x1a27f82,0x1a57f82,0x19f8002]
def table123_24 : List Nat := [0x1ae8002,0x1ab8082,0x1b88082,0x1b78102,0x83e0d82e0981c5,0x1958182,0x1a18202,0x19f8282,0x1ab8302,0x1b78382,0x86617856138445,0x1958402,0x1a38482,0x1ad8502,0x1ab8582,0x1b78602]
def table123_25 : List Nat := [0x198682,0x68682,0x1b8702,0x88702,0x1d8782,0xa8782,0x87e1d86da1655901207,0x87e1d86dad6559e1207,0x87e1d86dbb655aa1207,0x87e1d86dad6859e1207,0x87e1d86dbb685aa1207,0x87e1d86dbb6b5aa1207,0x198802,0xc8802,0x1b8882,0xe8882]
def table123_26 : List Nat := [0x1d8902,0x108902,0x89623885a365d903207,0x89623885af65d9e3207,0x89623885bd65daa3207,0x89623885af68d9e3207,0x89623885bd68daa3207,0x89623885bd6bdaa3207,0x89c1,0x8a4008983,0x8a8038983,0x8b41,0x8bc1e8b03,0x8e6378d6338c45,0x8ec208c03,0x8ec228c83]
def table123_27 : List Nat := [0x8ec248d03,0x8ec268d83,0x8ec288e03,0x8f41,0x8f82d8f03,0x9042a8f03,0x90c1,0x910319083,0x918359083,0x9241,0x928339203,0x930379203,0x93c1,0x96657956539445,0x4b9502,0x539582]
def table123_28 : List Nat := [0x5b9602,0x98e6197e5d96c5,0xcb9782,0xd59802,0xdd9882,0x9b66b9a6679945,0x4b9a02,0x539a82,0x5b9b02,0x9de759ce719bc5,0xcb9c82,0xd59d02,0xdd9d82,0xa067f9f67b9e45,0x4b9f02,0x539f82]
def table123_29 : List Nat := [0x5ba002,0xa2e89a1e85a0c5,0xa30d3a103,0xcba182,0xd5a202,0xdda282,0xa5e95a4e91a3c5,0xa658ea383,0xa659ca403,0xa65a8a483,0xa65b4a503,0x1b7a582,0x8ea2ba683,0xa6e649403,0xa6e669483,0x91628a703]
def table123_30 : List Nat := [0xa76789403,0xa767a9483,0x8fe2ea783,0xa7e709703,0x92e2ea803,0xa86829683,0x91e3aa883,0xa8e789903,0xa8e7a9983,0x93640a903,0xa96829b83,0xa9e4e9203,0xa628da983,129,0xb01,0xc81]
def table123_31 : List Nat := [0xd81,0xc01,0xd01,0xb12bcad1343f0f06,0xb12bcad1543f1286,0xb12bcad1743f1486,0xb12bcad1544d1286,0xb12bcad1744d1486,0xb12bcad174551486,0xb72d4b313c430f06,0xb72d4b315c431286,0xb72d4b317c431486,0xb72d4b318c431686,0xb72d4b315c4f1286,0xb72d4b317c4f1486,0xb72d4b318c4f1686]
def table123_32 : List Nat := [0xb72d4b317c571486,0xb72d4b318c571686,0xb72d4b318c5f1686,0xbd2ecb9144470f06,0xbd2ecb9164471286,0xbd2ecb9184471486,0xbd2ecb9164511286,0xbd2ecb9184511486,0xbd2ecb9184591486,0x1394dd3533cc32f86,0x1394dd35364c33286,0x1394dd35384c33506,0x1394dd35364cf3286,0x1394dd35384cf3506,0x1394dd35384d93506,0x13f4f53b344c52f86]
def table123_33 : List Nat := [0x13f4f53b36cc53286,0x13f4f53b38cc53506,0x13f4f53b36cd13286,0x13f4f53b38cd13506,0x13f4f53b38cdb3506,0x1876158352d435006,0x18761583545435206,0x1876158355d435386,0x187615835454b5206,0x1876158355d4b5386,0x1876158355d515386,0x18d62d89535455006,0x18d62d8954d455206,0x18d62d89565455386,0x18d62d8954d4d5206,0x18d62d895654d5386]
def table123_34 : List Nat := [0x18d62d89565535386,0x21f8761b685956406,0x21f8761b6b5956786,0x21f8761b6ed956a86,0x21f8761b6b5a16786,0x21f8761b6eda16a86,0x21f8761b6edad6a86,0x22588e2168d976406,0x22588e216bd976786,0x22588e216f5976a86,0x22588e216bda36786,0x22588e216f5a36a86,0x22588e216f5af6a86,0x8a41,0x8a81,0x8bc1]
def table123_35 : List Nat := [0x23b8c02,0x23b8c82,0x23b8d02,0x23b8d82,0x23b8e02,0x8f81,0x9041,0x9101,0x9181,0x9281,0x9301,0x299a382,0x299a402,0x299a482,0x299a502,0x23aa682]
def table123_36 : List Nat := [0xa701,0x2789402,0x27a9482,0xa781,0x2709702,0xa801,0x2829682,0x23aa882,0xa901,0x2829b82,0xa9c1,0x298a342,0x8ec1,0xa681,0xa881,0x1695417c3]
def table123_37 : List Nat := [0x169542603,0x1695413c3,0x169542703,0x5a5502,0x148b72d4b326c79284561089,0x522dcb52cc9b1e4a11588,0x1b6555535344,0x5a5d54c5e04,0x1694b5803,0x6d85a54d4b5205,0x1b61695352c4,0x1b61697554c4,0x5a5ed4e5684,0x1b6169755ed615386,0x6d9555d5735ed7f5707,0x6d85a5d57b5845]
def table123_38 : List Nat := [0x1b6169755ec4,0x6d85a5d43,0x1b61682,0x16d541585f1485,0x5b14c4b9e84,0x16c5312c3,0x5b12c2,0x5b10c532dcb52cc6,0x1b62148b1c84,0x1b62148b11c4,0x6d88514c3,0x1b6214711644,0x1b62147122c4,0x6d8851c43,0x1b62142,0x6d81]
def table123_39 : List Nat := [0x7201,0x7481,0x7701,0x7981,0x7c01,0x7e81,0x8101,0x8381,0x8601,0xa581,0x1694e5683,0x169745783,0x5a5d02,0x1694b5f03,0x1694b5f83,0x5a5702]
def table123_40 : List Nat := [0x169615e03,0x169615f03,0x169615f83,0x1694b50c3,0x5a5842,0x1681,0x1b81,0x1e01,0x2081,0x2301,0x2581,0x2801,0x2a81,0x61d8560d515805,0x71148bd2ecb92286,0x522f4bb2e48b1846]
def table123_41 : List Nat := [0x99149541d04,0x4a2f4bb2e48b1c86,0x1c4522f4bb2e45,0x18358d876155b5f06,0x60d5561d8556d5d5447,0x183605876157d5806,0x183555876155b5746,0x5557d5c57b5245,0x60d5561d8556c5,0x1835b5876154352c6,0x1815e57b5244,0x183555876144,0x14893244552bcb12b47,0x6b1946803,0x21b8761f6a9ac6506,0x86e1d87daa6b05]
def table123_42 : List Nat := [0x21b8761f6a84,0x86e1d87dad6545,0x21b8761f7d84,0x21b8761f6b44,0x21b8761f7084,0x86e1d87c3,0x7dd9567c3,0x886238959e745cd7887,0x22188e25679aa7786,0x22188e25679aa7806,0x12c1,0xf41,0xb92f452224872ec6,0x353f4f4d438c5,0x353f4f4d43145,0xdd3fd1d3e5173406]
def table123_43 : List Nat := [0xd4fd3d3504,0xdd354da3104,0xdd354cba084,0xdd3568c32c4,0xd4fd3d2f9173686,0x353f4f4ca45c5,0xd4fd3d3284,0xa641,0xa341,0x353f4f43,0x6258d5754858d8b5395b5349,0x156258d5bd715806,0x156258d575445c46,0x156258d575485106,0x62d89635455805,0x62d89635455785]
def table123_44 : List Nat := [0x5589635455345,0x62d89635455d05,0x156258d5144,0x62d896354d5c85,0x156258d5c44,0x55896343,0xaf14893244ad1746d2c48,0x2bc5224c912b4b12507,0x93244af148ad2c46,0x60d870543,0x62d8d6254d5785,0xb55505215c4,0x2d5541483,0x1b4a919ca31585,0xb55502,0x14c421383]
def table123_45 : List Nat := [0x5dd89635715215a62c7,0x1354dced3acca394c34e48,0x22588623679aa7886,0x88e258859e6a85,0x8962188d9e7785,0x8962188d9e7805,0x225886236784,0x19f6902,0x67c1,0x635636258b5015b5147,0x635776258b5c56f5807,0x635776258b5c56f5787,0x18d5558962d715206,0x635556258b5c45,0x635636258b5355d56c7,0x636255553f6245]
def table123_46 : List Nat := [0xb72ccb514c4,0x2dcb32d44213c5,0xb72ccb51084,0x2dcb32d43,0x138561783,0xd53e53f4ed3d3686,0x60cd53e585636255547,0x5501,0x5881,0x6001,0x354f94fd3b4f45,0x135354e54dd394186,0x6354c00204,0x135354e54e5034dc6,0xaf2c4ad2548f0fc6,0xaf2c4ad138561c06]
def table123_47 : List Nat := [0x2bcb12b44e1585,0xaf2c4ad24c8f2446,0x2bcb12b44d1b05,0x2bcb12b4691345,0xaf2c4ad1384,0xaf2c4ad1a45310c6,0x2bcb12b46914c5,0xaf2c4ad1a44,0x2bcb12b43,0x94fd8d6184,0x6258d62c3,0x18d53013f6345,0x2ecbd2e4871485,0xbb2e4bd1388921c6,0x2ecb92f4731445,0xbb2e4bd1384]
def table123_48 : List Nat := [0x21c7722c731185,0xbd2ecb921c4,0x2ecb92f43,0x1832ed3f8804,0x6354c00444,0x60cbb8940d4fc5,0x135354e52d58d8886,0x18d53003,0x1a202ec3,0x1a258803,0x6356250204,0x13535503888b56346,0x18d58943,0x18d50243,0x63542,0x64dc113904]
def table123_49 : List Nat := [0x64dc1130c4,0xed42ce540ce03606,0x1937045033805,0x64dc1140c4,0x19370443,0xd44fd3b4f5013e4fd3148,0xd44fd3b4f50147d293e52746d19368c,0x3513f4ecdd4f4f936c7,0xd44fd3b4f5013e4fd4608,0xd44fd3b3753d3e46,0x60202,0x18dd45d3f4f45,0x6375174fc4,0x190b40d374e50730c7,0x6374c13ace741c6,0x18dd304eb39c5]
def table123_50 : List Nat := [0x6374c133c4,0x18dd3043,0x190b4dd073a85,0x6375373604,0x18dd4dc3,0x63742,385,0x2b01,0x2c81,0x2e01,0x3701,0x3b01,0x4281,0x4781,0x4d81,0xd44fd3b4f44]
def table123_51 : List Nat := [0x351394d5033645,0xbe4e53540cd83806,0xd44e53540c4,0x351394d43,0x87e214f03,0x3500a4fc3,0xd40282,0xb4f82,0x3501,0x3a81,0x4201,0x4701,0x32c1,0x2fc1,0x4f53f4ec3,705]
def table123_52 : List Nat := [0x4e01,0x6181,0x8781,0x13f04c2,0x13540c2,0x4d41,833,0x8801,0x4f01,0x4fc1,0x441,0x581,0x2c01,0x8901,0x6301,0x2bc1]
def table123_53 : List Nat := [0x88c1,577,0x6c1,0x8701,0x6281,0x86c1,0x6241,0x641]

def encoded123 (i : Nat) : Nat :=
  if i < 432 then
    if i < 208 then
      if i < 96 then
        if i < 48 then
          if i < 16 then
            table123_0.getD (i%16) 0
          else
            if i < 32 then
              table123_1.getD (i%16) 0
            else
              table123_2.getD (i%16) 0
        else
          if i < 64 then
            table123_3.getD (i%16) 0
          else
            if i < 80 then
              table123_4.getD (i%16) 0
            else
              table123_5.getD (i%16) 0
      else
        if i < 144 then
          if i < 112 then
            table123_6.getD (i%16) 0
          else
            if i < 128 then
              table123_7.getD (i%16) 0
            else
              table123_8.getD (i%16) 0
        else
          if i < 176 then
            if i < 160 then
              table123_9.getD (i%16) 0
            else
              table123_10.getD (i%16) 0
          else
            if i < 192 then
              table123_11.getD (i%16) 0
            else
              table123_12.getD (i%16) 0
    else
      if i < 320 then
        if i < 256 then
          if i < 224 then
            table123_13.getD (i%16) 0
          else
            if i < 240 then
              table123_14.getD (i%16) 0
            else
              table123_15.getD (i%16) 0
        else
          if i < 288 then
            if i < 272 then
              table123_16.getD (i%16) 0
            else
              table123_17.getD (i%16) 0
          else
            if i < 304 then
              table123_18.getD (i%16) 0
            else
              table123_19.getD (i%16) 0
      else
        if i < 368 then
          if i < 336 then
            table123_20.getD (i%16) 0
          else
            if i < 352 then
              table123_21.getD (i%16) 0
            else
              table123_22.getD (i%16) 0
        else
          if i < 400 then
            if i < 384 then
              table123_23.getD (i%16) 0
            else
              table123_24.getD (i%16) 0
          else
            if i < 416 then
              table123_25.getD (i%16) 0
            else
              table123_26.getD (i%16) 0
  else
    if i < 640 then
      if i < 528 then
        if i < 480 then
          if i < 448 then
            table123_27.getD (i%16) 0
          else
            if i < 464 then
              table123_28.getD (i%16) 0
            else
              table123_29.getD (i%16) 0
        else
          if i < 496 then
            table123_30.getD (i%16) 0
          else
            if i < 512 then
              table123_31.getD (i%16) 0
            else
              table123_32.getD (i%16) 0
      else
        if i < 576 then
          if i < 544 then
            table123_33.getD (i%16) 0
          else
            if i < 560 then
              table123_34.getD (i%16) 0
            else
              table123_35.getD (i%16) 0
        else
          if i < 608 then
            if i < 592 then
              table123_36.getD (i%16) 0
            else
              table123_37.getD (i%16) 0
          else
            if i < 624 then
              table123_38.getD (i%16) 0
            else
              table123_39.getD (i%16) 0
    else
      if i < 752 then
        if i < 688 then
          if i < 656 then
            table123_40.getD (i%16) 0
          else
            if i < 672 then
              table123_41.getD (i%16) 0
            else
              table123_42.getD (i%16) 0
        else
          if i < 720 then
            if i < 704 then
              table123_43.getD (i%16) 0
            else
              table123_44.getD (i%16) 0
          else
            if i < 736 then
              table123_45.getD (i%16) 0
            else
              table123_46.getD (i%16) 0
      else
        if i < 800 then
          if i < 768 then
            table123_47.getD (i%16) 0
          else
            if i < 784 then
              table123_48.getD (i%16) 0
            else
              table123_49.getD (i%16) 0
        else
          if i < 832 then
            if i < 816 then
              table123_50.getD (i%16) 0
            else
              table123_51.getD (i%16) 0
          else
            if i < 848 then
              table123_52.getD (i%16) 0
            else
              table123_53.getD (i%16) 0
def book123 (i : Nat) : Clause := let n := encoded123 i; unpackLits 10 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses123 : inputsOK 3 123 a123 r123 (baseBook book123 493).toList=true := by decide +kernel

def rows123_0 : List Nat := [0x80401,0x501601,0x601a01,0x601c01,0x782001,0x782201,0x338d001,0x338d201,0x338d401,0x338d601,0x338d801,0x338da01,0x3a0ea01,0x3a0ec01,0x3a0ee01,0x3a0f001,0x3a0f201,0x3a0f401,0x3a0f601,0x3a0f801,0x3a0fa01,0x3a0fc01,0x4290c01,0x4290e01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk123_0 : checkRows book123 10 493 rows123_0=true := by decide +kernel

def rows123_1 : List Nat := [0x4291001,0x4291201,0x4291401,0x4291601,0x339b401,0x339b601,0x339b801,0x339ba01,0x339bc01,0x339be01,0x731ce01,0x731d001,0x731d201,0x731d401,0x731d601,0x731d801,0x3a24601,0x3a24801,0x3a24a01,0x3a24c01,0x3a24e01,0x3a25001,0x97a6001,0x97a6201]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk123_1 : checkRows book123 10 517 rows123_1=true := by decide +kernel

def rows123_2 : List Nat := [0x97a6401,0x97a6601,0x97a6801,0x97a6a01,0x42b2c01,0x42b2e01,0x42b3001,0x42b3201,0x42b3401,0x42b3601,0x76b4401,0x76b4601,0x76b4801,0x76b4a01,0x76b4c01,0x76b4e01,0xd435202,0x3dad435402,0x6d5b5802,0x235c01,0x2b5e01,0x336001,0x3b6201,0x436401]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk123_2 : checkRows book123 10 541 rows123_2=true := by decide +kernel

def rows123_3 : List Nat := [0x3dcd9b6802,0x12d9b6a02,0x3e2db36e02,0x3e4db37002,0x3dedcb7402,0x3e0dcb7602,0x9b3ae01,0x9bbb001,0x9cbb201,0x9dbb401,0x1173b801,0x46f16bbe02,0x1203c001,0x1203c201,0x46b17bc402,0x121bc601,0x47317bc802,0x122bca01,0x11c3cc01,0x4751b3d202,0x1243d401,0x378dcbd602,0x1253d801,0x11a467194631835a05]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk123_3 : checkRows book123 10 565 rows123_3=true := by decide +kernel

def rows123_4 : List Nat := [0x12647e01,0x12648e01,0x5a268482804e2704a288522b85eff3f7004040a0de780e2788e6790aa16,0x521385e133f4fcbf82789c090260a0de780e2788e6790592784814,0x362c8302d034300462e03cfcbfefe82409828379e0389e2399e4108bd278b618,0x1285e153f5008a4288260a0de780e2788e6790592784f2884813,0x521286100bf82c0ae26ca42804f28ca02a059278e6388de791e27804816,0x4e16bfc2a8a82689c12852288480a,0x1309a120a81604efdbf32a0a2148240989e0d,0x202799fe7aa0089a2488a32819f6811f077c3c8aa549e2589ea5c9f1fc822388c1ec1a,0x7e1f6799f285a0a7aa0c89a248f02a9002c9102e7f221299ee84c2e15,0x1f87da3c0aa400b2440bc3208,0x7a9f30e430952789627a9727c8f02a9002c9102e7f1ef2b4a72c1e615,0x7a1fe79a06811f077cb32c2027f2087bcad29a000f,0x1e87c9fb0bc348da348ca228a4b52b9ef2b2308f02a9002c9102e7f239299e618,0x22e8d2270b42e7a9e88f02a9002c9102e8e4a677a2210,0x82c36841ee7b1e72e1dc77a549e2589ea5c9f1fc884a67d2192da0e15,0x1dc88c368920e8320a841ee7b2549e2589ea5c9f2208e22c12,0x4368b21288a0a89a0c7a9e879cbc8ccba952789627a9727c7f2208e4a67d2192d9dc1a,0x8ba248dc350b9fa7e1f72fa3c0aa400b2440ba3929a2211,0x831e6829ef2c2108aa29302187d4b67f221299e80f,0x7a9ee7d43b0fc407e21e8721b309fd29a549e2589ea5c9f1e613,0x3fd2a85c2b0de780e2788e6790a00a,0x38adebd121380e437ee3b7ce349b273ba0c]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk123_4 : checkRows book123 10 589 rows123_4=true := by decide +kernel

def rows123_5 : List Nat := [0xe2b7af3c82e6cc8e738cdf380e43a0dfb8ee7c9b273bc11,0x9cca01,0x1309a120a0138a214bf2fd05c2b025330562989e0f,0x6f030741404e402784127a4227c20ccd3107a0e,0x761ec07021009e1049e9089f082094cd3106e0e,0x1bc0c1e05414848134d33407c159009e1049e9089f05c20ccd3107615,0x521b8481d8502005b03410402784127a4227c17083334c53507814,0x5a1d8481bcd0402784127a4227c17083314d41507b35c0e12,0x1240e160801fcd8154d6402784127a4227c174c53505011,0x134c0a134db351009e1049e9089f0800b,0x1685612050154070204a1c871370253305d31108411009f27a9e40a15,0x137a9201,0x137aa801,0x137ab401,0x137ace01,0x137ada01,0x137af001,0x137b0601,0x137b1201,0x137b1e01,0x137bb601,0x10acb87a23c0aa400b2440b9dc77a280b,0x8a2248c4310b1f47ca3c0aa400b2440ba39299de86a348722213,0x8922e8ac2b0c1ee7b1e73dcf4772347e1de8721a8f02a9002c9102e7f23929a2219]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk123_5 : checkRows book123 10 613 rows123_5=true := by decide +kernel

def rows123_6 : List Nat := [0x22e8b23c0aa400b2440bc3008,0x2348ca3c0aa400b2440bc3208,0x1dc82c2a8322488cfd3ea2a841ee7b23c0aa400b2440ba208e4a73e21416,0x7c9f0799ea89a248f02a9002c9102e7f4a73fc2c0f,0x7a1f50b2308ba2c8f02a9002c9102e7f4a73f9e60f,0x1e70d4f48d2328f02a9002c9102e7f4a73f9f20e,0x1dc82c2a8323c0aa400b2440ba2129cf8842140e,0x1f27c1e67a5068a223415034023c0aa400b2440b9fc8e4a73fc3014,0x8ba248a2370d42f2c1fa7e1f742238912408f4a60b82c0aa2213,0x14284401,0x14285c01,0x14286c01,0x14288201,0x14289801,0x1428ac01,0x1428be01,0x1f87dc3402,0x501540f040582007f4384808,0x1d8721ec0f02c114486e07,0x280a8293fb0005414826379e0389e2399e54589a0f,0x1c87b01c0c1d050138254486e09,0x1c8770240c1e054148494885b47d1c09d134386e0f,0x7b1f546c308c22e8b1e607,0x8d23288a28894310b1f079d1a8e5267f4340d]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk123_6 : checkRows book123 10 637 rows123_6=true := by decide +kernel

def rows123_7 : List Nat := [0x228892370cc2e7e9f87da2208,0x1e74a52b499fc8e1f206,0x83a2282a3286a1477a208e22609,0x8d23288a250a9dd4ba2a841ee7b52d499fc8e4320f,0x81a04779dd0aa02801fe07,0x8ca2c77a2203,0x2348ca228bc2d4d2294ca267a9e94c2088e42e0e,0x86253e8fc0274508406,0xa42dc9fae2a1288b9a80b7ceb382ee0b,0xa1adc9faeca3c4b4eadea0288b9ceb382e40d,0x282b727ebb28eb8a8511c434f2e6a22709d4eb382e010,0x28ab727eb8a84b7a80bb28f124451353e9d4eb382e810,0xa62b6a52bea6b18b0a9ec5444c5aa4b231d5031b39ce33c2bc13,0xbfafd12286a127ebda8150a8aba2e6a3303504ed382f211,0xab2d0aaad6ac2d4abc48b92e2b72df50ab2b62eb505453a4e53aad215,0x270c2442c2adeb72e4c3286a12eac4541514ef3ab0e10,0x270c2442c32e2b72e0c2a82a027f5228951d44c42eaa3541384eb3bb0e16,0xa62b6a52bea6b18c531aa227ea0ae0b72e2a130cc231cc42eab22a4a330eb0a9e9d30ac5ce738cf1384eb3babc23,0x296a8c50b1ac538a9406,0xa9aa0a6a9914c5113abcaea7138a940b,0xa5aa6a829d13c57152c0afa7138a940b,0x142ccc01,0x15502401,0x1bc0a1c04c12d254488007]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk123_7 : checkRows book123 10 661 rows123_7=true := by decide +kernel

def rows123_8 : List Nat := [0x198671906899668194679930a427089c0669a6479a410,0x1485f146621526114f0841e701586391e4611a5598d5697e12,0x5417c51984539586398607,0x14c5f146621530955e6014b5718c55d5a469c05618e4798212,0x5317c51980529586395462952621820b,0x392e0c9323388e6386e5b84e54880a,0x4f1704e9744fba4e8d64e9976501445ebaa50978ea17211,0x10797d589887018e4798b5818409,0x14b094215a11e7015462d604655e0a,0x15253c21079486017f5a9187015847955581460e,0x11f47b1e4773cbac05,0x15bc9601,0x56d5811f5c56604,0x1f47ec3d0f9e604,0x82c40871fa7e1f695a2078a1809,0x21e86a0a859f47c9e75da567f220789ea83c400e,0x1f67d5750f2135e1ea959fc789e60a,0x1fa7dc3a02,0x1f47c43802,0x14d4368aa568e1e2899dc07,0x21e86c3a02,0x2188520b60a0c7a1e6849ef6057f5f2567f22078c3810,0x2188543c02,0x87a1a82d867bd7895a2078a0f6143e0b]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk123_8 : checkRows book123 10 685 rows123_8=true := by decide +kernel

def rows123_9 : List Nat := [0x7d9f077d7a7b211621eb611fc789e60b,0xd8320ebeefad394303007,0x1630962504203,0x400d834fabe6220862158e0ed3945557430300e,0x23e78d3602,0x1f47c43c02,0x5201609c1284f003f4fe8de780e67950f550480e,0x362c8302d034fc8a02f0432acc62e03d658de780e6795194355743d17428b618,0xd8b20c0b80f519430b607,0x1509a120a013bfb668b42704a0d4ce2e8a61583f660e6379e47851743d55428a419,0x1509a120a0138562984a27517438a40b,0x20b0e5827aa0c7a21806,0x4c12d054124612405,0x296a6aa6a8c5115458b1ac538a940a,0xc02fabe45915c52c12ccb2ab76955154ce73b2f20f,0xa829aa645113abcaea70a95a738a940b,0xa5aa0a744f152c0afa70a95a738a940b,0x45553ac4addab6a2c8a95a739a9a0a,0x2acb42aab52aeac2d6acad89d4e9392d20c,0x318c6abeb9ab753316ae2f6bd2f2bf5aec7302b22feb0a753c4e73b31416,0x1e70dd7f5f1ee04,0x20b1021c7e9f87da1806,0x21e86a0a859f47cc4006,0x21e86a0b619ee79db76d20f6cda0771fc8843e0e]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk123_9 : checkRows book123 10 709 rows123_9=true := by decide +kernel

def rows123_10 : List Nat := [0x7a1ee8322a82d2e869f68b2147c1df6e1fc881e60f,0x1de7d9e76557404,0x5350da267adbc8a1ec84a116ea58cf5acced7271d8a7f2396c1dc14,0x166d9e2d035338ba0fd5542bfa09,0xbc10bfaff5c00d0b55559a08,0x1509a120a8164012a8a013dc22704b70517438a40f,0x12abf2fd5c57055555d17438a009,0x1309a120a81604e2805228d174389e0b,0x41e51d6254954561195991d5c14e0a,0x60425085ca7133f6b33870a5494dbe72a434d95462d66475b15c55e15,0x59c788e202,0x1739fc01,0x173a3801,0x60425085ca5518b5991d5c55e09,0x1250612e599644cd664e11d5c12c0a,0x494184a9625815b7595f689b0d0dcc9732952b26901ae6aa3cc89325a5664e16e47126525cf5c1301f,0x1250612a5896056dd64c969599385b91d5c1300e,0x2288ef9be9455575508407,0x2388afc3ee100300cddc2989a278881304a0e0a00f0a225dc94550d4588417,0x8e22bf0fb8400c033770882709a2a85a1584977897720a21483c0e04e2851543517438841c,0x1640854509203,0x400fbee02,0x337903af9bed435575503008,0x59f78d9022de6245e00e08808]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk123_10 : checkRows book123 10 733 rows123_10=true := by decide +kernel

def rows123_11 : List Nat := [0x3c0c8797706e220701d5e80f87c24d0d448300e,0x178be82403b668302d0357a8ba0f88d7a555430860f,0x100320f3f0fa09023d917b08d7a50d550300d,0x8623be6fb0377b88d7a55555de20a,0x3157271d8a948df718ca39a44908c6385f00d,0x14d436899eb6f2287b212845bb73dd1749dc0d,0x9632552b2a32a537c1c2315d55c9c764df28f322520c7765f413,0x1307b495595540805,0x1bd9e1f5f94487005,0x125241305501c0d43d575505609,0x63020681e8781adfb7e0777f06613d11550640e,0x1486e12072135134387807,0x4a1b8481e855026014887c15df95550f448700e,0x757fe0202,0x1069159271d724033ace60408,0x5db689accfdad81b40975f6721b06aa3c4cd664e11c49903765b15c15e16,0x715ad5ce076c33e05,0x176da26c8e5718de94df46b258cfb3c4cd664e11d5c15e11,0x324caa5841df581254403396b60c969cb828c57c34233608408e031dd8499aa8f3236c54a1c,0x25952df4caa5a419cb816068f32240254ce3240e,0x971caca24352d36c9a4040e10953388f32373dbe0f,0x6118907c2070a5252dbf7325c72b2890d4b4db269023cc898a639195991c5fe0e7133f6b61373db15c17c21,0x16658c15049b2395c63792894e0d7d1685b9195991c9633c6b33f5c15a16,0x16658c1504929769b232df03157272a5b858e031e14711accfdad849aa5a16e465664715d83db15c15a20]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk123_11 : checkRows book123 10 757 rows123_11=true := by decide +kernel

def rows123_12 : List Nat := [0x1846241f0814b751c294df49632552b2a32df03157271d937c8c68f3226298e465664717f83a5cd01c8d0e195c17c24,0x16658c1504929769af869b0d0e185760e4616f59968471ab5c15a14,0x1665896d054130595c4a1266a91846e1c6c16e4895a10,0x168c166a91b871b04e1238793609,0x4a95a491664c1365b16007,0x4b95a491624b4198896c4d9aa46e1c6c1385b9238796411,0x4d15a491664c1624b41d06e246ae1c6c1385b9238796a11,0x6278815e02,0x14e55c1f089184694606,0x6518c6417c649818a99654c2609,0x6018c55c250842846d5e07,0x51c26531846095605,0x674266918c6617d8b1898c19e6062a689538b9586399a699a013,0x611886341f084225f94a52632639c4481c2cfa536b5bf84b438a25c72b2890d4b4db26901ae8f3224611b875b17397c25,0x1846218d07c210894b8c9c294df4973416b258cfb246b54b8a32a330cb7c0c55cb224611b870c7841038d18f6c17c24,0xd05f36b592cf9c6716368f61040e356c25c0d,0x1625b413059aa4611b8715a08,0x1625b41907130491298e9aa46e1c4e16e571accf9b2395c637a537d258cf5acd09c984102969cb8e17e386356c15a24,0x1250512e599658f1aa46e1c4e1accf9b2395c637a537d258cf5acd09c984102969cb8e17e386356c12820,0x188c1306c186a91846e1c4e16e571accf9b2395c637a537d258cf5acd09c984102969cb8e17e386356c12821,0x56c1c5a9364d63e5892d901b2395c637a537d1ac9633ecf5ac96b42729c98e17e571ab870e1841038d16f6c16623,0x5895f06c165a9364d1ab871b2395c637a537d25a72e0a315f0330c68f258cf5acd0e2984102386356c15a21,0x18892c5792568e44599306a91b871385b927909b2395c637a537d25a72e0a315f0330c68f258cf5acd0e2984102386356c41a27,0x4b95a491624b15e5b13706415076466c8e5718de94df4969ca9660acf0c56b5f0d08cd8a1aa8f11b870c63861040e344e16e49e436c1642b]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk123_12 : checkRows book123 10 781 rows123_12=true := by decide +kernel

def rows123_13 : List Nat := [0x54a9632b7d0ca94df0708c58cd7271d937c9c897342d05accf9ad9214990a3cc8e1c31e1040e356c32420,0x330c44891f928c78d5f007,0x1930c201,0x1930dc01,0x1930fe01,0x330c84892193df005,0x19513801,0x19516e01,0x19518e01,0x955ad6fb40969c8420e63360571df0408e0cf8c86b9ad6c5cf94e5193b3817,0x1846218d07c210897e529498c91846e5b9517c0e,0x4b95a491624b1285b137064150711b96657971640f,0x5892856e225b1679765995c1209,0x4d15a491624b12906c17989664c6604611b966579716a11,0x168c164995e5766446e579713609,0x320c9a5440df58125c423416b256cf9c6716536c54a10,0x16f90896e043990371a4038d3764a528e9c397a459a33a6a6666cb2b73e539434019,0x3217d54a96326cf0c76b5f096b42331ca7266ace9a999b2a6cdb193a5416,0xce58b6b25ad09ca720e3718e4cf105811076c6539425411,0x162b4094dac70b3b97d739bb3c71104388c9815c77c106390cb9b5b194e5193a5c19,0x19c13201,0x19c16801,0x19c18a01,0x1955719c56603]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk123_13 : checkRows book123 10 805 rows123_13=true := by decide +kernel

def rows123_14 : List Nat := [0x19e11801,0x6118907c205f94a525d59c6799ee5b9d97c0d,0x1c294d8a973416b33b5cb3c71104388c9815c77c66e418e432db194e5193e7c18,0x19f9b201,0x19fa4401,0x19fb2a01,0x16f90896e043990371a4038d3764a528edcf94e51a0b4011,0x59963054124a5db9c67ba065d9e6599d15a0d,0x4995e57689a067995e5d9cda209,0x1a29a801,0x1a333a01,0x685a3e6802,0x19f687a41c203,0x1a49c801,0x1a49ca01,0x1a50cc01,0x1a534201,0x1a5a5a01,0x64fa65f002,0x1a3db1a6dac03,0x1a78c601,0x1a833c01,0x1a8b2601,0x1a925801]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk123_14 : checkRows book123 10 829 rows123_14=true := by decide +kernel

def rows123_15 : List Nat := [0x685a9d4a02,0x69daa5f402,0x1aab2001]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk123_15 : checkRows book123 10 853 rows123_15=true := by decide +kernel

def lastUnits123 := digits 10 2 0xd5f56
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict123 : checkReasons book123 856 298 lastUnits123 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude123 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 123=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=3) h hc bp eq (by decide +kernel)
  let v := truth Z a123
  have hbase : ValidThrough v book123 493 := book_start Z h hc z eq _ _ _ _ initialClauses123
  have h0 : ValidThrough v book123 517 := rows_sound hbase rows123_0 rowsOk123_0
  have h1 : ValidThrough v book123 541 := rows_sound h0 rows123_1 rowsOk123_1
  have h2 : ValidThrough v book123 565 := rows_sound h1 rows123_2 rowsOk123_2
  have h3 : ValidThrough v book123 589 := rows_sound h2 rows123_3 rowsOk123_3
  have h4 : ValidThrough v book123 613 := rows_sound h3 rows123_4 rowsOk123_4
  have h5 : ValidThrough v book123 637 := rows_sound h4 rows123_5 rowsOk123_5
  have h6 : ValidThrough v book123 661 := rows_sound h5 rows123_6 rowsOk123_6
  have h7 : ValidThrough v book123 685 := rows_sound h6 rows123_7 rowsOk123_7
  have h8 : ValidThrough v book123 709 := rows_sound h7 rows123_8 rowsOk123_8
  have h9 : ValidThrough v book123 733 := rows_sound h8 rows123_9 rowsOk123_9
  have h10 : ValidThrough v book123 757 := rows_sound h9 rows123_10 rowsOk123_10
  have h11 : ValidThrough v book123 781 := rows_sound h10 rows123_11 rowsOk123_11
  have h12 : ValidThrough v book123 805 := rows_sound h11 rows123_12 rowsOk123_12
  have h13 : ValidThrough v book123 829 := rows_sound h12 rows123_13 rowsOk123_13
  have h14 : ValidThrough v book123 853 := rows_sound h13 rows123_14 rowsOk123_14
  have h15 : ValidThrough v book123 856 := rows_sound h14 rows123_15 rowsOk123_15
  exact book_end h15 _ _ conflict123
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
