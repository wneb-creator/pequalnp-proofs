import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a4309 : Array Fact := #[(.res 0 8),(.res 1 8),(.res 2 8),(.res 0 10),(.res 1 10),(.res 2 10),(.res 0 11),(.res 1 11),(.res 2 11),(.res 0 13),(.res 1 13),(.res 2 13),(.live 8 1),(.lab 8 0 9),(.lab 8 0 10),(.common 8 10),(.lab 8 0 11),(.common 8 11),(.lab 8 0 13),(.common 8 13),(.live 8 2),(.lab 8 1 9),(.lab 8 1 10),(.lab 8 1 11),(.lab 8 1 13),(.live 8 3),(.lab 8 2 10),(.lab 8 2 11),(.lab 8 2 13),(.live 8 4),(.lab 8 3 9),(.lab 8 3 10),(.lab 8 3 11),(.lab 8 3 13),(.avoid 8 1548 0),(.avoid 8 1548 1),(.avoid 8 1548 2),(.avoid 8 1548 3),(.avoid 8 1548 4),(.avoid 8 7174 0),(.avoid 8 7174 1),(.avoid 8 7174 2),(.avoid 8 7174 3),(.avoid 8 7174 4),(.avoid 8 8713 0),(.avoid 8 8713 1),(.avoid 8 8713 2),(.avoid 8 8713 3),(.avoid 8 8713 4),(.avoid 8 9288 0),(.avoid 8 9288 1),(.avoid 8 9288 2),(.avoid 8 9288 3),(.avoid 8 9288 4),(.see 8 0 7426 0),(.see 8 0 7426 1),(.see 8 0 7426 2),(.see 8 0 7426 3),(.see 8 0 7426 4),(.see 8 0 9992 0),(.see 8 0 9992 1),(.see 8 0 9992 2),(.see 8 0 9992 3),(.see 8 0 9992 4),(.see 8 0 16256 0),(.see 8 0 16256 1),(.see 8 0 16256 2),(.see 8 0 16256 3),(.see 8 0 16256 4),(.see 8 2 9992 0),(.see 8 2 9992 1),(.see 8 2 9992 2),(.see 8 2 9992 3),(.see 8 2 9992 4),(.see 8 6 2338 0),(.see 8 6 2338 1),(.see 8 6 2338 2),(.see 8 6 2338 3),(.see 8 6 2338 4),(.see 8 6 7426 0),(.see 8 6 7426 1),(.see 8 6 7426 2),(.see 8 6 7426 3),(.see 8 6 7426 4),(.see 8 6 16256 0),(.see 8 6 16256 1),(.see 8 6 16256 2),(.see 8 6 16256 3),(.see 8 6 16256 4),(.diff 0 8 10),(.diff 1 8 10),(.diff 2 8 10),(.diff 0 8 11),(.diff 1 8 11),(.diff 2 8 11),(.diff 0 8 13),(.diff 1 8 13),(.diff 2 8 13),(.live 10 1),(.lab 10 0 8),(.lab 10 0 11),(.common 10 11),(.common 10 13),(.live 10 2),(.lab 10 1 8),(.lab 10 1 11),(.live 10 3),(.lab 10 2 8),(.lab 10 2 11),(.live 10 4),(.lab 10 3 8),(.lab 10 3 11),(.avoid 10 2338 0),(.avoid 10 2338 1),(.avoid 10 2338 2),(.avoid 10 2338 3),(.avoid 10 2338 4),(.see 10 0 7426 0),(.see 10 0 7426 1),(.see 10 0 7426 2),(.see 10 0 7426 3),(.see 10 0 7426 4),(.see 10 4 7174 0),(.see 10 4 7174 1),(.see 10 4 7174 2),(.see 10 4 7174 3),(.see 10 4 7174 4),(.see 10 4 7426 0),(.see 10 4 7426 1),(.see 10 4 7426 2),(.see 10 4 7426 3),(.see 10 4 7426 4),(.diff 0 10 8),(.diff 1 10 8),(.diff 2 10 8),(.diff 0 10 11),(.diff 1 10 11),(.diff 2 10 11),(.live 11 1),(.lab 11 0 8),(.lab 11 0 10),(.lab 11 0 13),(.common 11 13),(.live 11 2),(.lab 11 1 8),(.lab 11 1 10),(.lab 11 1 13),(.live 11 3),(.lab 11 2 8),(.lab 11 2 10),(.lab 11 2 13),(.live 11 4),(.lab 11 3 8),(.lab 11 3 10),(.lab 11 3 13),(.lab 11 4 8),(.lab 11 4 13),(.avoid 11 1290 0),(.avoid 11 1290 1),(.avoid 11 1290 2),(.avoid 11 1290 3),(.avoid 11 1290 4),(.avoid 11 8488 0),(.avoid 11 8488 1),(.avoid 11 8488 2),(.avoid 11 8488 3),(.avoid 11 8488 4),(.see 11 4 7426 0),(.see 11 4 7426 1),(.see 11 4 7426 2),(.see 11 4 7426 3),(.see 11 4 7426 4),(.see 11 4 10656 0),(.see 11 4 10656 1),(.see 11 4 10656 2),(.see 11 4 10656 3),(.see 11 4 10656 4),(.see 11 6 10656 0),(.see 11 6 10656 1),(.see 11 6 10656 2),(.see 11 6 10656 3),(.see 11 6 10656 4),(.diff 0 11 8),(.diff 1 11 8),(.diff 2 11 8),(.diff 0 11 13),(.diff 1 11 13),(.diff 2 11 13),(.live 13 1),(.lab 13 0 8),(.lab 13 0 10),(.live 13 2),(.lab 13 1 8),(.lab 13 1 10),(.live 13 3),(.lab 13 2 8),(.lab 13 2 10),(.live 13 4),(.lab 13 3 8),(.lab 13 3 10),(.avoid 13 1290 0),(.avoid 13 1290 1),(.avoid 13 1290 2),(.avoid 13 1290 3),(.avoid 13 1290 4),(.see 13 2 8488 0),(.see 13 2 8488 1),(.see 13 2 8488 2),(.see 13 2 8488 3),(.see 13 2 8488 4),(.see 13 2 9992 0),(.see 13 2 9992 1),(.see 13 2 9992 2),(.see 13 2 9992 3),(.see 13 2 9992 4),(.see 13 2 16256 0),(.see 13 2 16256 1),(.see 13 2 16256 2),(.see 13 2 16256 3),(.see 13 2 16256 4),(.see 13 4 9992 0),(.see 13 4 9992 1),(.see 13 4 9992 2),(.see 13 4 9992 3),(.see 13 4 9992 4),(.diff 0 13 8),(.diff 1 13 8),(.diff 2 13 8),(.diff 0 13 10),(.diff 1 13 10),(.diff 2 13 10)]
def r4309 : List Scheme := [(.earlier 8 1),(.earlier 8 2),(.allRes 8 0),(.allRes 8 2),(.exposure 8 1548),(.avoidNot 8 9 1548 0),(.avoidNot 8 10 1548 1),(.avoidNot 8 10 1548 2),(.avoidLive 8 1548 3),(.avoidLive 8 1548 4),(.exposure 8 7174),(.avoidNot 8 10 7174 0),(.avoidNot 8 11 7174 0),(.avoidNot 8 10 7174 1),(.avoidNot 8 11 7174 1),(.avoidLive 8 7174 2),(.avoidNot 8 10 7174 2),(.avoidNot 8 11 7174 2),(.avoidLive 8 7174 3),(.avoidNot 8 10 7174 3),(.avoidNot 8 11 7174 3),(.avoidLive 8 7174 4),(.exposure 8 8713),(.avoidNot 8 9 8713 0),(.avoidNot 8 13 8713 0),(.avoidNot 8 9 8713 1),(.avoidNot 8 13 8713 1),(.avoidNot 8 13 8713 2),(.avoidLive 8 8713 3),(.avoidNot 8 13 8713 3),(.avoidLive 8 8713 4),(.exposure 8 9288),(.avoidNot 8 10 9288 0),(.avoidNot 8 13 9288 0),(.avoidNot 8 10 9288 1),(.avoidNot 8 13 9288 1),(.avoidNot 8 10 9288 2),(.avoidNot 8 13 9288 2),(.avoidLive 8 9288 3),(.avoidNot 8 10 9288 3),(.avoidNot 8 13 9288 3),(.avoidLive 8 9288 4),(.exactAt 8 0 7426),(.seeLab 8 0 10 7426 0),(.seeLab 8 0 11 7426 0),(.seeLive 8 0 7426 1),(.seeLab 8 0 10 7426 1),(.seeLab 8 0 11 7426 1),(.seeLive 8 0 7426 2),(.seeLab 8 0 10 7426 2),(.seeLab 8 0 11 7426 2),(.seeLive 8 0 7426 3),(.seeLab 8 0 10 7426 3),(.seeLab 8 0 11 7426 3),(.seeLive 8 0 7426 4),(.exactAt 8 0 9992),(.seeLab 8 0 10 9992 0),(.seeLab 8 0 13 9992 0),(.seeLab 8 0 13 9992 1),(.seeLab 8 0 10 9992 2),(.seeLab 8 0 13 9992 2),(.seeLive 8 0 9992 3),(.seeLab 8 0 13 9992 3),(.seeLive 8 0 9992 4),(.exactAt 8 0 16256),(.seeLab 8 0 13 16256 0),(.seeLab 8 0 13 16256 1),(.seeLab 8 0 13 16256 2),(.seeLab 8 0 9 16256 3),(.seeLive 8 0 16256 4),(.exactAt 8 2 9992),(.seeLab 8 2 10 9992 0),(.seeLab 8 2 13 9992 0),(.seeLab 8 2 10 9992 1),(.seeLab 8 2 13 9992 1),(.seeLab 8 2 10 9992 2),(.seeLab 8 2 13 9992 2),(.seeLive 8 2 9992 3),(.seeLab 8 2 10 9992 3),(.seeLive 8 2 9992 4),(.exactAt 8 6 2338),(.seeLab 8 6 11 2338 0),(.seeLab 8 6 11 2338 1),(.seeLive 8 6 2338 2),(.seeLive 8 6 2338 3),(.seeLive 8 6 2338 4),(.exactAt 8 6 7426),(.seeLab 8 6 10 7426 0),(.seeLab 8 6 10 7426 1),(.seeLab 8 6 10 7426 2),(.seeLab 8 6 11 7426 3),(.seeLive 8 6 7426 4),(.exactAt 8 6 16256),(.seeLab 8 6 9 16256 0),(.seeLab 8 6 11 16256 0),(.seeLab 8 6 13 16256 0),(.seeLive 8 6 16256 1),(.seeLab 8 6 9 16256 1),(.seeLab 8 6 10 16256 1),(.seeLab 8 6 11 16256 1),(.seeLab 8 6 13 16256 1),(.seeLive 8 6 16256 2),(.seeLab 8 6 10 16256 2),(.seeLab 8 6 11 16256 2),(.seeLab 8 6 13 16256 2),(.seeLive 8 6 16256 3),(.seeLab 8 6 9 16256 3),(.seeLab 8 6 13 16256 3),(.seeLive 8 6 16256 4),(.diffX 0 8 10),(.diffC 0 8 10),(.diffX 1 8 10),(.diffC 1 8 10),(.diffX 2 8 10),(.diffC 2 8 10),(.adjacentCommon 8 10 0),(.residual 8 10 0 1),(.residual 8 10 0 2),(.residual 8 10 0 3),(.residual 8 10 1 2),(.residual 8 10 1 3),(.residual 8 10 2 3),(.diffX 0 8 11),(.diffC 0 8 11),(.diffX 1 8 11),(.diffC 1 8 11),(.diffX 2 8 11),(.diffC 2 8 11),(.adjacentCommon 8 11 6),(.residual 8 11 0 1),(.residual 8 11 0 2),(.residual 8 11 0 3),(.residual 8 11 1 2),(.residual 8 11 1 3),(.residual 8 11 2 3),(.diffX 0 8 13),(.diffC 0 8 13),(.diffX 1 8 13),(.diffC 1 8 13),(.diffX 2 8 13),(.diffC 2 8 13),(.adjacentCommon 8 13 2),(.residual 8 13 0 1),(.residual 8 13 0 2),(.residual 8 13 0 3),(.residual 8 13 1 2),(.residual 8 13 1 3),(.residual 8 13 2 3),(.earlier 10 1),(.earlier 10 2),(.allRes 10 0),(.allRes 10 1),(.allRes 10 2),(.exposure 10 2338),(.avoidNot 10 8 2338 0),(.avoidNot 10 11 2338 0),(.avoidLive 10 2338 1),(.avoidNot 10 8 2338 1),(.avoidNot 10 11 2338 1),(.avoidLive 10 2338 2),(.avoidNot 10 8 2338 2),(.avoidNot 10 11 2338 2),(.avoidLive 10 2338 3),(.avoidNot 10 8 2338 3),(.avoidNot 10 11 2338 3),(.avoidLive 10 2338 4),(.exactAt 10 0 7426),(.seeLab 10 0 8 7426 0),(.seeLab 10 0 11 7426 0),(.seeLab 10 0 8 7426 1),(.seeLab 10 0 11 7426 1),(.seeLive 10 0 7426 2),(.seeLab 10 0 8 7426 2),(.seeLab 10 0 11 7426 2),(.seeLive 10 0 7426 3),(.seeLab 10 0 8 7426 3),(.seeLab 10 0 11 7426 3),(.seeLive 10 0 7426 4),(.exactAt 10 4 7174),(.seeLab 10 4 11 7174 0),(.seeLab 10 4 11 7174 1),(.seeLive 10 4 7174 2),(.seeLive 10 4 7174 3),(.seeLive 10 4 7174 4),(.exactAt 10 4 7426),(.seeLab 10 4 8 7426 0),(.seeLab 10 4 11 7426 0),(.seeLab 10 4 8 7426 1),(.seeLab 10 4 11 7426 1),(.seeLive 10 4 7426 2),(.seeLab 10 4 8 7426 2),(.seeLab 10 4 11 7426 2),(.seeLive 10 4 7426 3),(.seeLab 10 4 8 7426 3),(.seeLab 10 4 11 7426 3),(.seeLive 10 4 7426 4),(.diffX 0 10 8),(.diffC 0 10 8),(.diffX 1 10 8),(.diffC 1 10 8),(.diffX 2 10 8),(.diffC 2 10 8),(.residual 10 8 0 1),(.residual 10 8 0 2),(.residual 10 8 0 3),(.residual 10 8 1 2),(.residual 10 8 1 3),(.residual 10 8 2 3),(.diffX 0 10 11),(.diffC 0 10 11),(.diffX 1 10 11),(.diffC 1 10 11),(.diffX 2 10 11),(.diffC 2 10 11),(.adjacentCommon 10 11 4),(.residual 10 11 0 1),(.residual 10 11 0 2),(.residual 10 11 0 3),(.residual 10 11 1 2),(.residual 10 11 1 3),(.residual 10 11 2 3),(.adjacentCommon 10 13 4),(.earlier 11 1),(.earlier 11 2),(.earlier 11 3),(.allRes 11 0),(.allRes 11 1),(.allRes 11 2),(.exposure 11 1290),(.avoidNot 11 8 1290 0),(.avoidNot 11 10 1290 0),(.avoidNot 11 8 1290 1),(.avoidNot 11 10 1290 1),(.avoidLive 11 1290 2),(.avoidNot 11 8 1290 2),(.avoidNot 11 10 1290 2),(.avoidLive 11 1290 3),(.avoidNot 11 8 1290 3),(.avoidNot 11 10 1290 3),(.avoidLive 11 1290 4),(.exposure 11 8488),(.avoidNot 11 8 8488 0),(.avoidNot 11 13 8488 0),(.avoidLive 11 8488 1),(.avoidNot 11 8 8488 1),(.avoidNot 11 13 8488 1),(.avoidLive 11 8488 2),(.avoidNot 11 8 8488 2),(.avoidNot 11 13 8488 2),(.avoidLive 11 8488 3),(.avoidNot 11 8 8488 3),(.avoidNot 11 13 8488 3),(.avoidLive 11 8488 4),(.avoidNot 11 8 8488 4),(.avoidNot 11 13 8488 4),(.exactAt 11 4 7426),(.seeLab 11 4 8 7426 0),(.seeLab 11 4 10 7426 0),(.seeLab 11 4 8 7426 1),(.seeLab 11 4 10 7426 1),(.seeLive 11 4 7426 2),(.seeLab 11 4 8 7426 2),(.seeLab 11 4 10 7426 2),(.seeLive 11 4 7426 3),(.seeLab 11 4 8 7426 3),(.seeLab 11 4 10 7426 3),(.seeLive 11 4 7426 4),(.exactAt 11 4 10656),(.seeLab 11 4 13 10656 0),(.seeLab 11 4 8 10656 1),(.seeLive 11 4 10656 2),(.seeLive 11 4 10656 3),(.seeLive 11 4 10656 4),(.exactAt 11 6 10656),(.seeLab 11 6 8 10656 0),(.seeLab 11 6 13 10656 0),(.seeLab 11 6 8 10656 1),(.seeLab 11 6 13 10656 1),(.seeLive 11 6 10656 2),(.seeLab 11 6 8 10656 2),(.seeLab 11 6 13 10656 2),(.seeLive 11 6 10656 3),(.seeLab 11 6 8 10656 3),(.seeLab 11 6 13 10656 3),(.seeLive 11 6 10656 4),(.seeLab 11 6 8 10656 4),(.seeLab 11 6 13 10656 4),(.diffX 0 11 8),(.diffC 0 11 8),(.diffX 1 11 8),(.diffC 1 11 8),(.diffX 2 11 8),(.diffC 2 11 8),(.residual 11 8 0 1),(.residual 11 8 0 2),(.residual 11 8 0 3),(.residual 11 8 1 2),(.residual 11 8 1 3),(.residual 11 8 2 3),(.diffX 0 11 13),(.diffC 0 11 13),(.diffX 1 11 13),(.diffC 1 11 13),(.diffX 2 11 13),(.diffC 2 11 13),(.adjacentCommon 11 13 4),(.residual 11 13 0 1),(.residual 11 13 0 2),(.residual 11 13 0 3),(.residual 11 13 0 4),(.residual 11 13 1 2),(.residual 11 13 1 3),(.residual 11 13 1 4),(.residual 11 13 2 3),(.residual 11 13 2 4),(.residual 11 13 3 4),(.earlier 13 1),(.earlier 13 2),(.allRes 13 0),(.allRes 13 1),(.allRes 13 2),(.exposure 13 1290),(.avoidNot 13 8 1290 0),(.avoidNot 13 10 1290 0),(.avoidLive 13 1290 1),(.avoidNot 13 8 1290 1),(.avoidNot 13 10 1290 1),(.avoidLive 13 1290 2),(.avoidNot 13 8 1290 2),(.avoidNot 13 10 1290 2),(.avoidLive 13 1290 3),(.avoidNot 13 8 1290 3),(.avoidNot 13 10 1290 3),(.avoidLive 13 1290 4),(.exactAt 13 2 8488),(.seeLab 13 2 8 8488 0),(.seeLab 13 2 8 8488 1),(.seeLive 13 2 8488 2),(.seeLive 13 2 8488 3),(.seeLive 13 2 8488 4),(.exactAt 13 2 9992),(.seeLab 13 2 8 9992 0),(.seeLab 13 2 10 9992 0),(.seeLab 13 2 8 9992 1),(.seeLab 13 2 10 9992 1),(.seeLive 13 2 9992 2),(.seeLab 13 2 8 9992 2),(.seeLab 13 2 10 9992 2),(.seeLive 13 2 9992 3),(.seeLab 13 2 8 9992 3),(.seeLab 13 2 10 9992 3),(.seeLive 13 2 9992 4),(.exactAt 13 2 16256),(.seeLab 13 2 8 16256 0),(.seeLive 13 2 16256 1),(.seeLive 13 2 16256 2),(.seeLive 13 2 16256 3),(.seeLive 13 2 16256 4),(.exactAt 13 4 9992),(.seeLab 13 4 8 9992 0),(.seeLab 13 4 10 9992 0),(.seeLab 13 4 8 9992 1),(.seeLab 13 4 10 9992 1),(.seeLive 13 4 9992 2),(.seeLab 13 4 8 9992 2),(.seeLab 13 4 10 9992 2),(.seeLive 13 4 9992 3),(.seeLab 13 4 8 9992 3),(.seeLab 13 4 10 9992 3),(.seeLive 13 4 9992 4),(.diffX 0 13 8),(.diffC 0 13 8),(.diffX 1 13 8),(.diffC 1 13 8),(.diffX 2 13 8),(.diffC 2 13 8),(.residual 13 8 0 1),(.residual 13 8 0 2),(.residual 13 8 0 3),(.residual 13 8 1 2),(.residual 13 8 1 3),(.residual 13 8 2 3),(.diffX 0 13 10),(.diffC 0 13 10),(.diffX 1 13 10),(.diffC 1 13 10),(.diffX 2 13 10),(.diffC 2 13 10),(.residual 13 10 0 1),(.residual 13 10 0 2),(.residual 13 10 0 3),(.residual 13 10 1 2),(.residual 13 10 1 3),(.residual 13 10 2 3)]

def table4309_0 : List Nat := [0xc8a02,0x148c82,0x8e82,0x28e82,0x1349649239145,0xd1102,0x161182,0x1a1202,0x199282,0x1d9302,0x15caa532893c5,0xe1382,0x101382,0x161402,0x171402,0x149482]
def table4309_1 : List Nat := [0x1a1482,0x1b1482,0x199502,0x1f1502,0x201502,0x1d9582,0x184be5d2d9645,0xd1602,0x121602,0x151682,0x181682,0x1c1702,0x199782,0x211782,0x1d9802,0x1acd2673298c5]
def table4309_2 : List Nat := [0xe1882,0x121882,0x161902,0x181902,0x1a1982,0x1c1982,0x199a02,0x1f1a02,0x211a02,0x1d9a82,0x1d4e671379b45,0xe9b02,0x101b02,0xc9b82,0x169b82,0x171b82]
def table4309_3 : List Nat := [0x149c02,0x1a9c02,0x1b1c02,0x199c82,0x1f9c82,0x201c82,0x1d9d02,0x1fcfa7b3c9dc5,0xe9d82,0x121d82,0x181e02,0x1a9e82,0x1c1e82,0x199f02,0x211f02,0x1d9f82]
def table4309_4 : List Nat := [0x2250e8541a045,0x122002,0x182082,0x1c2102,0x1e2182,0x1da202,0x24d228f46a2c5,0xe2282,0x12a282,0x162302,0x18a302,0x1a2382,0x1ca382,0x19a402,0x1f2402,0x1da482]
def table4309_5 : List Nat := [0x27536994ba545,0x10a502,0x17a582,0x14a602,0x19a682,0x1da702,0x29d4aa350a7c5,0xe2782,0x162802,0x1a2882,0x20a902,0x1da982,0x2c55ead55aa45,0xdaa02,0x10aa02,0x122a02]
def table4309_6 : List Nat := [0xcaa82,0x15aa82,0x162a82,0x17aa82,0x182a82,0x14ab02,0x1a2b02,0x1bab02,0x1c2b02,0x19ab82,0x1eab82,0x212b82,0x1dac02,0xac82,0x32c82,0x1ad02]
def table4309_7 : List Nat := [0x42d02,0x2ad82,0x52d82,0x7c1,0xb75aacc5a1d0c0787,0xb75aacc6a1d140787,0xb75aacc7e1d190787,0xb75aacc6a2d140787,0xb75aacc7e2d190787,0xb75aacc7e35190787,0xae02,0x62e02,0x1ae82,0x72e82,0x2af02,0x82f02]
def table4309_8 : List Nat := [0x8c1,0xbd5dae45e210c0887,0xbd5dae46e21140887,0xbd5dae48221190887,0xbd5dae46e2f140887,0xbd5dae4822f190887,0xbd5dae48237190887,0xaf82,0x92f82,0x1b002,0xa3002,0x2b082,0xb3082,0x9c1,0xc360afc62250c0987,0xc360afc7225140987]
def table4309_9 : List Nat := [0xc360afc8625190987,0xc360afc7231140987,0xc360afc8631190987,0xc360afc8639190987,0x62b382,0x67b502,0x3b682,0x4b682,0x5b682,0x3a5cee571b845,0x633802,0x643802,0x62b882,0x683882,0x693882,0x67b902]
def table4309_10 : List Nat := [0x6b3902,0x6c3902,0x6ab982,0x6e3982,0x6f3982,0x6dba02,0x3cde2ef76bac5,0x63ba82,0x643a82,0x68bb02,0x693b02,0x67bb82,0x6bbb82,0x6c3b82,0x6abc02,0x6ebc02]
def table4309_11 : List Nat := [0x6f3c02,0x6dbc82,0x3f5f6f97bbd45,0x64bd02,0x69bd82,0x67be02,0x6abe82,0x6dbf02,0x41e0b0380bfc5,0x633f82,0x64bf82,0x684002,0x69c002,0x67c082,0x6b4082,0x6cc082]
def table4309_12 : List Nat := [0x6ac102,0x6e4102,0x6fc102,0x6dc182,0x3c202,0x4202,0x4c282,0x14282,0x5c302,0x24302,0x10d85c25a2c7620787,0x10d85c25aec7670787,0x10d85c25bac76a0787,0x10d85c25aed1670787,0x10d85c25bad16a0787,0x10d85c25bad76a0787]
def table4309_13 : List Nat := [0x3c382,0x64382,0x4c402,0x74402,0x5c482,0x84482,0x32c1,0x11388c3da6c9623287,0x11388c3db2c9673287,0x11388c3dbec96a3287,0x11388c3db2d3673287,0x11388c3dbed36a3287,0x11388c3dbed96a3287,0x3341,0x8ac782,0x8fc982]
def table4309_14 : List Nat := [0x93cb82,0x6cb82,0x7cb82,0x8cb82,0x50e833f9ecec5,0x8b4e82,0x8c4e82,0x904f02,0x914f02,0x8fcf82,0x944f82,0x954f82,0x93d002,0x985002,0x995002,0x97d082]
def table4309_15 : List Nat := [0x5369749a3d145,0x8b5102,0x8d5102,0x8ad182,0x905182,0x925182,0x8fd202,0x945202,0x965202,0x93d282,0x985282,0x9a5282,0x97d302,0x9b5302,0x9c5302,0x55eab53a8d3c5]
def table4309_16 : List Nat := [0x8b5382,0x8cd382,0x905402,0x91d402,0x8fd482,0x945482,0x95d482,0x93d502,0x985502,0x99d502,0x97d582,0x586bf5dadd645,0x8dd602,0x905682,0x8fd702,0x93d782]
def table4309_17 : List Nat := [0x97d802,0x5aed367b2d8c5,0x8bd882,0x8d5882,0x90d902,0x925902,0x8fd982,0x94d982,0x965982,0x93da02,0x98da02,0x9a5a02,0x97da82,0x9bda82,0x9c5a82,0x6db02]
def table4309_18 : List Nat := [0x5b02,0x7db82,0x15b82,0x8dc02,0x25c02,0x171b7db643178a0887,0x171b7db653178f0887,0x171b7db66317930887,0x171b7db653218f0887,0x171b7db66321930887,0x171b7db66329930887,0x6dc82,0x95c82,0x7dd02,0xa5d02,0x8dd82]
def table4309_19 : List Nat := [0xb5d82,0x4741,0x177badce4b1b8a4707,0x177badce5b1b8f4707,0x177badce6b1b934707,0x177badce731b974707,0x177badce5b258f4707,0x177badce6b25934707,0x177badce7325974707,0x177badce6b2d934707,0x177badce732d974707,0x177badce7335974707,0xbcdf82,0xbfe102,0x9e282,0xae282]
def table4309_20 : List Nat := [0xbe282,0x6672f95c9e445,0xbd6402,0xbe6402,0xbce482,0xc06482,0xc16482,0xbfe502,0xc36502,0xc46502,0xc2e582,0xc66582,0xc76582,0xc5e602,0x68f439fcee6c5,0xbde682]
def table4309_21 : List Nat := [0xc0e702,0xbfe782,0xc2e802,0xc5e882,0x6b757a9d3e945,0xbde902,0xbe6902,0xc0e982,0xc16982,0xbfea02,0xc3ea02,0xc46a02,0xc2ea82,0xc6ea82,0xc76a82,0xc5eb02]
def table4309_22 : List Nat := [0x6df6bb3d8ebc5,0xbdeb82,0xbcec02,0xbfec82,0xc2ed02,0xc5ed82,0x7077fbdddee45,0xbd6e02,0xbeee02,0xc06e82,0xc1ee82,0xbfef02,0xc36f02,0xc4ef02,0xc2ef82,0xc66f82]
def table4309_23 : List Nat := [0xc7ef82,0xc5f002,0x9f082,0x7082,0xaf102,0x17102,0xbf182,0x27182,0x1c7e2f0f037bbc0987,0x1c7e2f0f0f7bbf0987,0x1c7e2f0f1b7bc20987,0x1c7e2f0f0f81bf0987,0x1c7e2f0f1b81c20987,0x1c7e2f0f1b87c20987,0x9f202,0x37202]
def table4309_24 : List Nat := [0xaf282,0x47282,0xbf302,0x57302,0x1cde5f27077dbc3307,0x1cde5f27137dbf3307,0x1cde5f271f7dc23307,0x1cde5f271383bf3307,0x1cde5f271f83c23307,0x1cde5f271f89c23307,0x5bad5662d0e8606,0x5bad566350e8a06,0x5bad5663f0e8c86,0x5bad56635168a06,0x5bad5663f168c86,0x5bad5663f1a8c86]
def table4309_25 : List Nat := [0x5eaed722f108606,0x5eaed7237108a06,0x5eaed7241108c86,0x5eaed7237178a06,0x5eaed7241178c86,0x5eaed72411b8c86,0x61b057e31128606,0x61b057e39128a06,0x61b057e43128c86,0x61b057e39188a06,0x61b057e43188c86,0x61b057e431c8c86,0x86c2e12d163b106,0x86c2e12d763b386,0x86c2e12dd63b506,0x86c2e12d768b386]
def table4309_26 : List Nat := [0x86c2e12dd68b506,0x86c2e12dd6bb506,0x89c461ed364b106,0x89c461ed964b386,0x89c461edf64b506,0x89c461ed969b386,0x89c461edf69b506,0x89c461edf6cb506,0xb8dbedb218bc506,0xb8dbedb298bc786,0xb8dbedb318bc986,0xb8dbedb2990c786,0xb8dbedb3190c986,0xb8dbedb3194c986,0xbbdd6e7258dc506,0xbbdd6e72d8dc786]
def table4309_27 : List Nat := [0xbbdd6e7358dc986,0xbbdd6e7398dcb86,0xbbdd6e72d92c786,0xbbdd6e73592c986,0xbbdd6e73992cb86,0xbbdd6e73596c986,0xbbdd6e73996cb86,0xbbdd6e7399acb86,0xe3f178781bdde06,0xe3f178787bddf86,0xe3f17878dbde106,0xe3f178787c0df86,0xe3f17878dc0e106,0xe3f17878dc3e106,0xe6f2f9383bede06,0xe6f2f9389bedf86]
def table4309_28 : List Nat := [0xe6f2f938fbee106,0xe6f2f9389c1df86,0xe6f2f938fc1e106,0xe6f2f938fc4e106,0x2ef75b9da84,0xbbdd6e71bb0d906,0x5deeb738dd985,0x5deeb738dda05,0x2ef75b9d104,0x5deeb738dd305,0x5deeb738dc985,0x5deeb738dd185,0x2ef75b9c6c4,0x2ef75b9d204,0x5deeb73a34985,0x2ef75b9d184]
def table4309_29 : List Nat := [0x2ef75b9d284,0x177badcc3,0x170b84c104,0x5c2e12c778b446,0x436170963c085,0x170b84b804,0x170b84b884,0x170b84b904,0xb85c243,0x2e230f77b985,0x2e230f76b905,0x171187b984,0x44e230f69bb85,0x171187b884,0x171187b904,0x1e6eb76b3c4]
def table4309_30 : List Nat := [0x44e230f64bc05,0x171187bb44,0xb88c3c3,0x1faf77ab3c4,0x1860160ab84,0x7633180904,0x618058239198c06,0x30c02c11c8cc5,0x18601608e44,0x7638210c04,0x1dabcbaad2f8906,0x76af568644,0x18601608c44,0xc300b043,0x5d8057a4f191b86,0x5d8057a4f191c06]
def table4309_31 : List Nat := [0x2ec02bd100c85,0x5d8057a5b45aa06,0xbb00af4f28b560cc7,0x5d8057a7945ab06,0x176015e8c84,0x176015e8c04,0x2ec02bd54a385,0x2ec02bd36aa85,0x176015eaa44,0xbb00af43,0x2bc7e1ef84,0x7178fc3bdef05,0x2bc7e1e404,0x2bc7e1e484,0x2bc7e1e504,0x15e3f0c3]
def table4309_32 : List Nat := [0x6dbee349a3c586,0x36df718bc985,0xdb7dc69367b1d1c7,0x6dbee349b3d8c6,0xdb7dc6774f90c987,0x97cee9f41aaca06,0x36df71a4c585,0x1b6fb8d244,0x97cf6a33ba7c9c6,0x1860d5d8044,0x2ed7a2f5c9485,0x5daf4ae4f372e46,0xc3608ed7e25180c87,0x61b0476bf541b86,0x61b0476bf540a06,0x30d823b5faa05]
def table4309_33 : List Nat := [0xb35a8ed6ea9198a47,0x2cd6ab735a4cd291140b49,0x59ad476b7548cc6,0x166b55b9ac646531a388,0x59ad56e5735a4d4e3216070a,0x2cd6ab72b9ad26a7190b09,0x166b55b95cd693538c88,0xb35aadcd675499a4e691368b4b,0xe64382,0x2d40a33162cc5,0x5c81466515d8806,0x5c81466515d8a06,0x39805198b04,0x5c814666f5d9446,0x39805198844,0x1cc028cc3]
def table4309_34 : List Nat := [0x5caf4ea325d9406,0x2b9d4a26f101006,0x172bd2b9d464bb378808,0xb95e95cea325d9bc7,0xe60142,0x399269dd484,0x399268b5544,0x1cc934583,0xe64982,0x1cc8bd483,0x1cc8bc843,0xe645c2,0xe64802,0x7301,0x8fd402,0x47c1]
def table4309_35 : List Nat := [0x4541,0x70f8fc5c0e585,0xe1f1f3391e2ee86,0x1c3e3e2f7f91dcf147,0x39613d4e584,0x39613d3e504,0x1cb09e583,0x72c2791c263c5,0x72c277ed5e485,0x39613c8e104,0x1cb09e503,0x1cb09e443,0x39613dfe0c4,0x35ba5d3dfc4,0x1cb09ea83,0x1cb09e9c3]
def table4309_36 : List Nat := [0xe584c2,0x72f83a6e4df45,0x33393c8dfc4,0x3978bd37244,0x21f2e64b984,0x43e5cdb64b385,0x21f2e6db244,0x21f2e6db904,0x21f2e6db984,0x10f9736c3,0x36b17a5c26585,0x36b17a5c260c5,0x1b58bbe6104,0xdac5df03,0xdabee483,0x6675ba7c9dfc5]
def table4309_37 : List Nat := [0xdabeea83,0x6d62c2,0x3681,0x3a01,0x3c81,0x3f01,0x4181,0xb8dbedb3d9dc5c6,0x2e36fb6d469f57935008,0x171b7db6a33d9dcbc7,0x4b81,0x5081,0x5581,0x5c6df6da8ce85,0x5bedb71a8cec5,0x2df71b6d444]
def table4309_38 : List Nat := [0x171b7db43,0xe282,0xccdf797c9c8e106,0xccdf797c9c8df86,0x62efbcbe4e445,0x3177de5f244,0x42e1b0968c105,0x2170d84b884,0x42e1b0968b1c5,0x42e1b0968b985,0x2170d84b444,0x2170d84b904,0x2170d84b984,0x10d85c243,0x1be8583,0x2055bad44]
def table4309_39 : List Nat := [0x43e2711703385,0x21f1388b804,0xe171b3c3,0x43e271171b245,0x87c4e22eb6a3986,0x43e271171b505,0x21f1388b8c4,0x10f89c443,0x16c84c2c3,0xb64282,0x15bad43,0x1c1dcf1f87c5bc5ec7,0xc5ee78fc3e2e446,0xb65f42,0xb65fc2,0x16cc9f283]
def table4309_40 : List Nat := [0x2d9cbc26504,0x16cc9e103,0xb664c2,0xb66142,0xb67282,0x5b01,0x1cbc8e67937ec26a07,0x397a7c8e675bc9d2e108,0x44797a7c8dd85,0x72f4f91c5f245,0x2bac55233278b06,0x2b9d562a9198806,0x3057fc6198bc5,0x3057fc6199485,0x3057fc6199c05,0x182bfe30cc4]
def table4309_41 : List Nat := [0x182bfe32a84,0x182bfe32b04,0xc15ff183,0x2ddcbd38544,0x16ee5e9c3,0x223cbd35d84,0xb772c2,0x5daf4ae755c8c86,0x176055c8b84,0x176055c9444,0x3b578643,0xb701c2,0x16e198143,0xb70042,0x5b81,0x5c41]
def table4309_42 : List Nat := [0x441,257,0x4481,0xe81,0x2d81,0x3081,0x1581,0x1a81,0x1d01,0x1f81,0x2201,0x2481,0x2701,0x2981,0x2c01,0x5aacc2]
def table4309_43 : List Nat := [0x1553695278a45,0x2fd8233140e45,0x17ec1198704,0x17ec1198e04,0xbf608cc3,0xbf608e43,0x2a50aad408c05,0xbf608903,0x5fb042,0x2d41,193,513,0x7101,0x4401,0x43c1,449]
def table4309_44 : List Nat := [769,0x7201,0x5c81,0xc5f2c2,0x541,0x3001,0x5d01,65,0x2fc1,0x5dc1,0x7081,0x481,0x581,0x6281,0x7181,0x6601]
def table4309_45 : List Nat := [0x6b01,0x7001,0xd3e442,0x69c1,0x6041,0x6481,0x6e81,0x6401,0x6e41,0x5fc1,0x5e81,0x61c1,0x6501,0x65c1,0x6141,0x6301]

def encoded4309 (i : Nat) : Nat :=
  if i < 368 then
    if i < 176 then
      if i < 80 then
        if i < 32 then
          if i < 16 then
            table4309_0.getD (i%16) 0
          else
            table4309_1.getD (i%16) 0
        else
          if i < 48 then
            table4309_2.getD (i%16) 0
          else
            if i < 64 then
              table4309_3.getD (i%16) 0
            else
              table4309_4.getD (i%16) 0
      else
        if i < 128 then
          if i < 96 then
            table4309_5.getD (i%16) 0
          else
            if i < 112 then
              table4309_6.getD (i%16) 0
            else
              table4309_7.getD (i%16) 0
        else
          if i < 144 then
            table4309_8.getD (i%16) 0
          else
            if i < 160 then
              table4309_9.getD (i%16) 0
            else
              table4309_10.getD (i%16) 0
    else
      if i < 272 then
        if i < 224 then
          if i < 192 then
            table4309_11.getD (i%16) 0
          else
            if i < 208 then
              table4309_12.getD (i%16) 0
            else
              table4309_13.getD (i%16) 0
        else
          if i < 240 then
            table4309_14.getD (i%16) 0
          else
            if i < 256 then
              table4309_15.getD (i%16) 0
            else
              table4309_16.getD (i%16) 0
      else
        if i < 320 then
          if i < 288 then
            table4309_17.getD (i%16) 0
          else
            if i < 304 then
              table4309_18.getD (i%16) 0
            else
              table4309_19.getD (i%16) 0
        else
          if i < 336 then
            table4309_20.getD (i%16) 0
          else
            if i < 352 then
              table4309_21.getD (i%16) 0
            else
              table4309_22.getD (i%16) 0
  else
    if i < 544 then
      if i < 448 then
        if i < 400 then
          if i < 384 then
            table4309_23.getD (i%16) 0
          else
            table4309_24.getD (i%16) 0
        else
          if i < 416 then
            table4309_25.getD (i%16) 0
          else
            if i < 432 then
              table4309_26.getD (i%16) 0
            else
              table4309_27.getD (i%16) 0
      else
        if i < 496 then
          if i < 464 then
            table4309_28.getD (i%16) 0
          else
            if i < 480 then
              table4309_29.getD (i%16) 0
            else
              table4309_30.getD (i%16) 0
        else
          if i < 512 then
            table4309_31.getD (i%16) 0
          else
            if i < 528 then
              table4309_32.getD (i%16) 0
            else
              table4309_33.getD (i%16) 0
    else
      if i < 640 then
        if i < 592 then
          if i < 560 then
            table4309_34.getD (i%16) 0
          else
            if i < 576 then
              table4309_35.getD (i%16) 0
            else
              table4309_36.getD (i%16) 0
        else
          if i < 608 then
            table4309_37.getD (i%16) 0
          else
            if i < 624 then
              table4309_38.getD (i%16) 0
            else
              table4309_39.getD (i%16) 0
      else
        if i < 688 then
          if i < 656 then
            table4309_40.getD (i%16) 0
          else
            if i < 672 then
              table4309_41.getD (i%16) 0
            else
              table4309_42.getD (i%16) 0
        else
          if i < 704 then
            table4309_43.getD (i%16) 0
          else
            if i < 720 then
              table4309_44.getD (i%16) 0
            else
              table4309_45.getD (i%16) 0
def book4309 (i : Nat) : Clause := let n := encoded4309 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses4309 : inputsOK 3 4309 a4309 r4309 (baseBook book4309 394).toList=true := by decide +kernel

def rows4309_0 : List Nat := [0x398e801,0x398ea01,0x398ec01,0x398ee01,0x398f001,0x398f201,0x4010201,0x4010401,0x4010601,0x4010801,0x4010a01,0x4010c01,0x4691c01,0x4691e01,0x4692001,0x4692201,0x4692401,0x4692601,0x3999401,0x3999601,0x3999801,0x3999a01,0x3999c01,0x3999e01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4309_0 : checkRows book4309 10 394 rows4309_0=true := by decide +kernel

def rows4309_1 : List Nat := [0x6b1ae01,0x6b1b001,0x6b1b201,0x6b1b401,0x6b1b601,0x6b1b801,0x4024a01,0x4024c01,0x4024e01,0x4025001,0x4025201,0x4025401,0x98a6401,0x98a6601,0x98a6801,0x98a6a01,0x98a6c01,0x98a6e01,0x98a7001,0x98a7201,0x98a7401,0x98a7601,0x46af001,0x46af201]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4309_1 : checkRows book4309 10 418 rows4309_1=true := by decide +kernel

def rows4309_2 : List Nat := [0x46af401,0x46af601,0x46af801,0x46afa01,0x6eb0801,0x6eb0a01,0x6eb0c01,0x6eb0e01,0x6eb1001,0x6eb1201,0x1f67c1ea7936e7eb6cda3628f23a8e1e00c,0x87a1c6f9bcd721a8aa288621609,0x2308b35e02,0x2368cb6002,0x701bc8835ce2a2a88b8ee3224791e2e21be0d,0x1fc7e36202,0x1ea7c35c7db5e6f3606fb90e49e00a,0x1ea79b5c02,0x1f07b1e0e59f2e5392e435e08,0x2368ca228ab648b9f07b9ece2226e636a0c,0x8c236d93666fb8889b987aa287a2220b,0x8c22c88a32e72287a9e8e2226e63640b,0x8aa30d9b6a8d1f67d1f2e2226e62220b,0x2368c22adbb6cda1fc7e1e0e839ee6a26e6390e222210]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4309_2 : checkRows book4309 10 442 rows4309_2=true := by decide +kernel

def rows4309_3 : List Nat := [0x5013a4d148d0b40cf184609806414a4c1320d,0x1285333854990589305395608,0x17c5eb3a02,0x15c4a3a6ce1765c3a85d1364d19061930e912a0e,0x5f17a5c1725e3384f13a4e19061930e933e0d,0x1725d97eceb3e509404f99061930e91700c,0x5f1765cb42d033c519444cbaeeb3aae9190529864c17011,0x55150d334857948519446a1624c14c0b,0x1605714c54346561425013e6a1624c34e0c,0xd3bb2521446a15a05,0x15a55b4a02,0x5815c533b8543445493c4e9386a1624c34c0d,0xd2bb45093e6a15405,0x571564a94c03,0x1605734802,0xd194cef96253934f01364cbbcedbba529306a15a0f,0x16c5a92a4a166d11684d9544cbc2ef3baed9a85296e4c16412,0x5b16a4a96403,0x2008420b3622334cc0d6350d24388a010860d,0x1206e0f872108521f84c1e8461d0760b,0x150bc170b8248ca1808ccb890f28c84386c278d8013c8260662685815,0x5e2e0542f8562408e3286023332253cc268664386c278d8013c8260c616,0x481b83e1c8421d0461f050cbb32cd802f390e1487e0107612,0x1006e0f874118521f84a1e0501f0700b]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4309_3 : checkRows book4309 10 466 rows4309_3=true := by decide +kernel

def rows4309_4 : List Nat := [0xc8b80b0be0c03c360c207,0x150bc198b8180023005a0006c360580b,0xe838f532c43836f58d0f43c8013340b,0x382f82c0b8ba2e3d232034f60d00dbd0f210e0f0d80133012,0xa022ca3260685e170f40a804008140b,0x7028c9b2a08064188f40a804008140b,0x1c08b28ca8261a868153def70f40a86c010181601410,0x532608064188601505c2488c260360b09a19838093e0160180b8bc2e8f40a83c1b09e0101c1d,0x1601c1501417016248702306e2687a198243d02a1b07e27804000ca188763302233898343201d,0x58540506a0a05e07324c83e0f902218800338cc328f40a86c0105615,0x58540506a0a0640885e07324c8b20003e0008f40a86c0105613,0xf9be2243ca320740d0d8010d2fa0b80b,0x881e05016160561501c170c6310b834062260963d02a1b0d801024198d2fa32219,0x14c882019062180540705c318c43d02a1b00409066fa01812,0x53200685e1705408862000ce330ca2e3ee1588e233ec3d02a1b09e3600409066268d2fa094fa8181f,0x881e0501a1785c150622588c24058060be2f3f0253ea26866093e83d02a1b09e013261b,0xa1290a2b74deb78a62e0b7adcba29a9fa820d,0x2d8b5b7202,0x2a4a8a7a9e370a82d2b33f6b429ea1a84ba2a6b8a7efd29c12,0xb62d6b32ceb5370a328aa22e8b8a7efd3760d,0x2d2b3adaddb72a4a90a3ae8b8a7efd2cc0c,0xb62d2b3b7ade374a5a94a0bfcfebf8fd2e8a6ae29facc11,0x1dc7f9c8829d4811ced6b587d1f278200789ca8f9de7e21470a1214,0x1cc7f9c8811ce829d4d421076b526f3546fa3e77a1470a0212]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4309_4 : checkRows book4309 10 490 rows4309_4=true := by decide +kernel

def rows4309_5 : List Nat := [0x1cc7f9c8829d4d4a1c85a1a811ce86228792227823287a0e7c9d900c008f9de7e2148823870a021e,0x1d07f9c8829d4d5a10769be8d232801ca88b508a1e879c048f9de8523870a0618,0x1d07f9c8829d4841dad5b586fa3e77a1470a060e,0x741fe7220a751de8520607,0x1d07f9c8821d2d5c0a839d9021e90020072a3e77a1470a0612,0x731fe7220473b50829d46f22e8b20e7640700a250323e77a1470a0215,0x759fe7220e761de8520c07,0x1d67f9c8841dad6c10801ca811ced4b567b9ed03a483f3f291112f6a3e77a1470a0c1a,0x2207b2602,0xa024054141781a1732807,0xcbb3000bd203,0xd88c0b09a0e4180d092cb05c1683c2782e2e8902f89811,0xb4180d036cb32e0003c2f82e2e8380b,0x66180030741a160bc1b05408,0x581cc50c6313d62e0ca0782a36024348140d,0x462303e2584823840c6b14000940a,0x1608b16338cc2e0c406c23080d22684c0902a1489e3601412,0x1384ac78982583e05,0xa0ac050b20831e2708d098ae238400581a110922c0b411,0x1088c0f8961209c13b16c642824844008900d,0x2704ec742a00c2205,0x154221706003,0x4012b162601e0388c05008248440680d0b89016018028be2f0bb0909a1984c090110b0b62786c1482a048e2018e0bb98cffbb0b998b048fa9725ae8a56371a26830646260c103e38,0x4012b162601e0388c0500824018028be2f0bb090e20482a1489e018100904c2680c068442483e1e]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4309_5 : checkRows book4309 10 514 rows4309_5=true := by decide +kernel

def rows4309_6 : List Nat := [0x540841605058060fc0a86c01824198620c,0x16150141902217b22c80003f02a1b006090670d05610,0x10d8b82f4343e18eec18a36c323101a381a43da56e8a5a69bc50c3069830436006348ca1b,0x58540506007c360a86c01824198560b,0xa0c80a40743a3e18eec18a36c242f0a2381a43da56e8a5a69bc50c30698304388fc2a8062a05d0e0a621,0x3e01c63814ec0206286418860368550b8580643c174382686613024381a43da56e8a5a69bc50c30698304388fc0a8521b09e01b2629,0x1a86416328c9b201701c06800008540b,0x80540506a0a0181606207,0x261501419022cac4216019100680a,0x1615014190221a828c8b2511003100560c,0xc841617c463e18eec18a368010b0030f8b62786c1482a3f0e2018e0690f695ba2969a6f1430c1a60c101821,0x739da75b56d6a0c82a42779c492240f6914ffaef122e4963a2969a6f1430c1a60463046f9c81d,0x40ad6356811fe90a1471248903da453febbc48b9258e8a5a69bc50c30698118c11be8044a729da1e,0x1d4739dcd6b5884a11131ca909de71248903da453febbc48b9258e8a5a69bc50c30698118c11c81e,0x731fe7220473a1076a0a75350d5353139bc6fa4277a1471248903da453febbc48b9258e8a5a69bc50c30698118c120225,0x82a0890a48903da453febbc48b9258e8a5a69bc50c30698118c135215,0x1bc88b508a2428e1c492240f6914ffaef122e4963a2969a6f1430c1a60463048cc508922c1c,0x751d2721cc809fe811cf15452909de851c492240f6914ffaef122e4963a2969a6f1430c1a60463047620f1435223,0x811ce711a6f1430c1c5072a0115c100b,0x1d07f9c8821d2d5c5902a0072c56839d914240f6914ffaee92448b9258e8a1477a5a909c469bc50c26046306c120624,0x891c8889d08a206811d28b1d88c9de8e1c06f9ca0f,0x228722227322480a007fc5c8e21477a32839d87022c821d26f9ce14,0x1179bc01,0x296a537802]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4309_6 : checkRows book4309 10 538 rows4309_6=true := by decide +kernel

def rows4309_7 : List Nat := [0xa428ea0c62a32d4b4b7607,0xa5a94a0a8aa4b76b6ad8b5acd1929ab8b7a0d,0x2acac380e12baa6296a52fcafa7d16aa80c,0xaf2b8aa2acdfab4a4a90a3afcafa7d16b860d,0x3871a298a52fd16ab606,0xa4a8ce1b84bf29a9f46d16a8209,0x2b6ab382df2aea328abf2be9f27916aa80c,0xe0c6aa4a831c2bd1ba7abf29a9f46d16ab00d,0x3831aa92a3afd16ab006,0x2acacb7cabc70a328aa2282ae472bf29aafa7d1b47516aa812,0x9e2ccdf2d4bf2e29f2d0a1c7716ad60b,0xae2b29eaa803,0x2bcae2fca1c7716b8006,0x37eaa47abf2be9f286aaa851dc7d16ab60c,0x2dc9e478df2b11fa871dafd16a7a0a,0x2dcb5a7a9e37cb42b0b4aaf16acc0a,0xa528e9ea8203,0x298a5282a4b832128720a9ab8ab0a2aaf16b840e,0x148511a6711aa71b4806,0x134531325513c56942d13464a14a58bc0699c46a9c72214e12,0x134ef9325513c5a3c64fc8b22166529625b94e0e,0x1605714c5534a561425013e699c46a9c6589512334e10,0x5515ad334e5794851944699c46a9c6589512314c0f,0x5815c533b85493c4e9332448e5413723162529a6711aa71b4c13]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4309_7 : checkRows book4309 10 562 rows4309_7=true := by decide +kernel

def rows4309_8 : List Nat := [0x2a8e1abaa6296afc86bf92cc092f16ab60c,0x2bcadb84e0c7b21afe4b3024babf16aa80c,0xaa386ad292a4282a34972529aafc86bf92cc092ea1aad16abc13,0x282e0a90adab4aa2b8a54991eaaca1a9aafc86bf92cc092f16a8c14,0xa3288bf92cc092f16b7c07,0xaac851ea8403,0xaf2b8bf92cc092f16b8007,0xa6294a0a84aaaa9282b6a4b7f27c9d26c86afa9abf92cc092f16b8015,0x9825ca027f28a59203024bba209,0x12914a01,0x12916201,0x12916e01,0x12918601,0x1da761c877c9268c0e7b9d4d4ca517b540c,0x82a12d69dc769fe05,0x2108335a759d4724b10421477a012b9fe0c,0x1249c3291a203,0x12d1de01,0x12d21401,0x210839fe82a02d49cc72cb917b540a,0x8420e7fa0082b50d59cf2ccb517c612e3580d,0x12ecbc01,0x1da761c8729d474350d5a06814bf17c612db580e,0x118452809fbda04]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4309_8 : checkRows book4309 10 586 rows4309_8=true := by decide +kernel

def rows4309_9 : List Nat := [0xa3292df298dfa78e027b16a8209,0x28ca4b7cdfa78a54c516a8208,0x28cb3484b5cc6b74c4a6ae2b42d40a,0xaf2b8aa2b6dfc7aaaa8532482afae316b800d,0x1826034002,0x5f17a5c4cc5c978ce13c4e9392b33e0b,0xefb38539532a12805,0x1465134002,0x1404f93334935344cf29b3e08,0x182601705c97ece9425013e5dcd52b3420c,0x5f17261342cf148519445dcd52b1700b,0x609805c174ea1364d133364d65dcd533ca72b33c0f,0x622ff329923f3f23ea5ae8a59203006391444bda9811930cda13,0x10b8bd0cc24268661342c3682a1486c278b6010580f,0x15456b44d192853934f01372a14c0a,0x168efbc738166539364d4a92a9540a,0x1444f92b2993204,0x1485113250b47394e329b4808,0x15456b4cd395e521472a14c08,0x55160d2b4e56142501333a4e53895139ca92994c0f,0x5334a5614250132571453a95139ce538ca9299540f,0x1605714c543b8d11524f13a4e4ed2a34c0c,0x690e1379aa97ba296480c025a450faf6bf2458fc39192ec4da901a28fcee17,0x4012b162601e0388c05008248440680d0b89016018028be2f0bb0909a1984c090110b0e4f11a696ba2978fe963f3200f8c08e06398c68a3e368120a8521b09e2d8049003e36]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4309_9 : checkRows book4309 10 610 rows4309_9=true := by decide +kernel

def rows4309_10 : List Nat := [0x4012b162601e0388c05008248440680d0b89016018028be2f0bb0909a1984c090110b0da0482a1486c278b60103e24,0x2deb72ccb4b70fdb7406,0x290a2a98deb78b82deb7466a6a820a,0x2c0b1a7ab12793dac2a14f8ba8df3d2e4963a2979aa394eef11a497302c04cabb4dcb41a28facab8cc2902fe624f13cac826,0x2af2147aa6abf30a40a1aad3ea8a0a,0x296a5282a4372b3cf8b9258baba237a5f3d2ee6a8e445ceef13da6925c45302c01a28fa9b30a40a1cfb3f37422,0x2a8e1ab4a4a90afaad3ec8730a40bf9893c4f316abc10,0xaa386aea98a5a834029aafa86ab4fb21cff30a40bf9893c4f316ab615,0xa42a8a0ab8a550321cfea6abf30a40bf9893c4f2a1aad3eab413,0x370962eae88de97cf4bb9aa391173bbc4f69a497114b3b02c02cce0ad8adab4aa2dcae1a28fabeb8cc2902fe624f13caad3ea793f2aea2ad4a350516ae430,0xdc4f8b9258baba237a5f3d2ee6a8e445ceef13da6925c45302c01a28fcc2902873ea793f28b412ce1f,0xaf2b6e138342506aba8ca2d053f2ad3eafe624f13cabf30a4116aa815,0x28ca6382e1a90adab516a8208,0xa4a8ce1b84a5abcaeaa94347b16a820b,0x282e0a90adab4aa2b8a550f1eaad32afe682bea6ceea01aa9825f16a8c16,0xa0b82a42b6ad2a8ae29543c7aab4caa6abf16a8c0f,0x88b8050c406824348ce07,0x1c2e0143302018854175141601809066348c60e,0xccb2e340a62e0a0318a42a8a8348a345c1e462ec3606c0a806bbbca15,0xf5332cb0c82e0ce00022078d907806bb918bb0383483611,0xf5332cb0c82e0cc00062180d907806bb918bb0383483611,0x5f47056058154681d460660902a1b006bb8540e,0xe8360c334ccb2c0c8c830918bb03c01aee000034782c11,0x741f072ccb36cb876340cc462ec1f806bb8034786e10]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4309_10 : checkRows book4309 10 634 rows4309_10=true := by decide +kernel

def rows4309_11 : List Nat := [0x8421882cd336cc088358d42e5234851f078d822806462eebb08014,0x51332afe683c4394f4b9bfe9f9a6908df49111201129128612,0x1a132ceea1a806ad109825ee8a5d499a690a59202fe10,0x684873ba806aa6097afe07,0x391a13d2feb9c86ffa7e973a34ad29492584448069a4237912913c415,0x3210585e004460081806,0x1781d4b86c0a8063f43a07,0xc843b0d52e1b02a018fd4c05a09,0x3d6000ca02,0x1906015058c85341701b4cd30348674b8f695ba21b02a978fc019aa64cef369a0620fa69a4297300633034b32623,0xbd0bc242786c14c323880637a4437536130662685810,0x1a2e8bc4978e43fcf4fc8fa69a4237a44973014b25610,0x2d89e1482b4e006648e536bb062d3a37536633034b0de9142c13,0x50b4f4c002,0x14fa4601,0x14fa4801,0x1501aa01,0x15080601,0x1508e201,0x15091601,0x15182a01,0x15185201,0x15186c01,0x15187e01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4309_11 : checkRows book4309 10 658 rows4309_11=true := by decide +kernel

def rows4309_12 : List Nat := [0x15188a01,0x15189e01,0x1518aa01,0x1518b601,0x1518d801,0x42e2f4330909a1984d0b55b5354750d4953d515585810,0x70a0050a607d59530a407,0x332cbd4752bca04,0xcb03ef50d01283758d601001609038130a94d0d228d1707d4b53d47535515704619,0xcb06ef50d01e0360e07b4d0d21c56552d53518740f,0x5e280542986158d6615d6428d162a06707d595455d53547528a414,0x1206e0f874118721087c14332cbb3600d6954d4f5287611,0x220b8200c82155d550d407,0x3583acd56c20c1f5a036218d15ad4752bd40d,0x10656e000035a54752b2c07,0x260ffba2452595c1112025ac09a6694ee680dd57ae73d545522ec14,0x15c8de01,0x15c8e001,0x15d2ea01,0x15d9a401,0x5455ecee02,0x15f1a001,0x15f1a201,0x15fafe01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4309_12 : checkRows book4309 10 682 rows4309_12=true := by decide +kernel

def rows4309_13 : List Nat := [0x16025601,0x28721ccb60d1204,0x3009fd8602,0x16211401,0x16225c01,0x54b62bda02,0x162d7001,0x585633a202,0x163ae601,0x16411001,0x164a6001,0x165a7c01,0x1662ec01,0x166a9a01,0x166abe01,0x166ae201,0x296a5282a2a90dc3729e47aaaacf3e5955e59d67da166b7412,0x4f71ead0aaa86a15a55e59d655a3682780c,0x169aae01,0x16a28a01,0x16a2d201,0x9e2dd3daccb43f6a1a855e59d655a36b27a0d,0x166d95675796bcf805,0x167dab6bc8403]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4309_13 : checkRows book4309 10 706 rows4309_13=true := by decide +kernel

def rows4309_14 : List Nat := [0x16c2ce01,0x167579655b56cb7205,0x16da9001,0x5af6ad9f6e28204,0x16ea9401,0x16ea9601]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk4309_14 : checkRows book4309 10 730 rows4309_14=true := by decide +kernel

def lastUnits4309 := digits 10 6 0xb3abcb6acab7adf
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict4309 : checkReasons book4309 736 442 lastUnits4309 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude4309 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 4309=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=3) h hc bp eq (by decide +kernel)
  let v := truth Z a4309
  have hbase : ValidThrough v book4309 394 := book_start Z h hc z eq _ _ _ _ initialClauses4309
  have h0 : ValidThrough v book4309 418 := rows_sound hbase rows4309_0 rowsOk4309_0
  have h1 : ValidThrough v book4309 442 := rows_sound h0 rows4309_1 rowsOk4309_1
  have h2 : ValidThrough v book4309 466 := rows_sound h1 rows4309_2 rowsOk4309_2
  have h3 : ValidThrough v book4309 490 := rows_sound h2 rows4309_3 rowsOk4309_3
  have h4 : ValidThrough v book4309 514 := rows_sound h3 rows4309_4 rowsOk4309_4
  have h5 : ValidThrough v book4309 538 := rows_sound h4 rows4309_5 rowsOk4309_5
  have h6 : ValidThrough v book4309 562 := rows_sound h5 rows4309_6 rowsOk4309_6
  have h7 : ValidThrough v book4309 586 := rows_sound h6 rows4309_7 rowsOk4309_7
  have h8 : ValidThrough v book4309 610 := rows_sound h7 rows4309_8 rowsOk4309_8
  have h9 : ValidThrough v book4309 634 := rows_sound h8 rows4309_9 rowsOk4309_9
  have h10 : ValidThrough v book4309 658 := rows_sound h9 rows4309_10 rowsOk4309_10
  have h11 : ValidThrough v book4309 682 := rows_sound h10 rows4309_11 rowsOk4309_11
  have h12 : ValidThrough v book4309 706 := rows_sound h11 rows4309_12 rowsOk4309_12
  have h13 : ValidThrough v book4309 730 := rows_sound h12 rows4309_13 rowsOk4309_13
  have h14 : ValidThrough v book4309 736 := rows_sound h13 rows4309_14 rowsOk4309_14
  exact book_end h14 _ _ conflict4309
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
