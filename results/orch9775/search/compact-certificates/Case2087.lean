import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a2087 : Array Fact := #[(.res 0 9),(.res 1 9),(.res 0 10),(.res 1 10),(.res 0 13),(.res 1 13),(.lab 1 0 1),(.lab 1 0 4),(.avoid 1 245 0),(.lab 2 0 1),(.lab 2 0 4),(.avoid 2 314 0),(.lab 4 0 4),(.lab 4 1 4),(.lab 4 2 4),(.lab 4 3 4),(.live 9 1),(.lab 9 0 7),(.lab 9 0 10),(.common 9 10),(.lab 9 0 13),(.common 9 13),(.live 9 2),(.lab 9 1 7),(.lab 9 1 10),(.lab 9 1 13),(.live 9 3),(.lab 9 2 7),(.lab 9 2 10),(.lab 9 2 13),(.lab 9 3 7),(.lab 9 3 10),(.avoid 9 5316 0),(.avoid 9 5316 1),(.avoid 9 5316 2),(.avoid 9 5316 3),(.avoid 9 9288 0),(.avoid 9 9288 1),(.avoid 9 9288 2),(.avoid 9 9288 3),(.avoid 9 13504 0),(.avoid 9 13504 1),(.avoid 9 13504 2),(.avoid 9 13504 3),(.see 9 1 7812 0),(.see 9 1 7812 1),(.see 9 1 7812 2),(.see 9 1 7812 3),(.see 9 5 1548 0),(.see 9 5 1548 1),(.see 9 5 1548 2),(.see 9 5 1548 3),(.see 9 5 9992 0),(.see 9 5 9992 1),(.see 9 5 9992 2),(.see 9 5 9992 3),(.diff 0 9 10),(.diff 1 9 10),(.diff 0 9 13),(.diff 1 9 13),(.live 10 1),(.lab 10 0 8),(.lab 10 0 9),(.lab 10 0 12),(.lab 10 0 13),(.common 10 13),(.live 10 2),(.lab 10 1 8),(.lab 10 1 9),(.lab 10 1 12),(.lab 10 1 13),(.live 10 3),(.lab 10 2 8),(.lab 10 2 9),(.lab 10 2 12),(.lab 10 2 13),(.avoid 10 792 0),(.avoid 10 792 1),(.avoid 10 792 2),(.avoid 10 792 3),(.avoid 10 4370 0),(.avoid 10 4370 1),(.avoid 10 4370 2),(.avoid 10 4370 3),(.avoid 10 8488 0),(.avoid 10 8488 1),(.avoid 10 8488 2),(.avoid 10 8488 3),(.see 10 0 1290 0),(.see 10 0 1290 1),(.see 10 0 1290 2),(.see 10 0 1290 3),(.see 10 0 7426 0),(.see 10 0 7426 1),(.see 10 0 7426 2),(.see 10 0 7426 3),(.see 10 0 9992 0),(.see 10 0 9992 1),(.see 10 0 9992 2),(.see 10 0 9992 3),(.see 10 5 7426 0),(.see 10 5 7426 1),(.see 10 5 7426 2),(.see 10 5 7426 3),(.see 10 5 13504 0),(.see 10 5 13504 1),(.see 10 5 13504 2),(.see 10 5 13504 3),(.see 10 5 16256 0),(.see 10 5 16256 1),(.see 10 5 16256 2),(.see 10 5 16256 3),(.diff 0 10 9),(.diff 1 10 9),(.diff 0 10 13),(.diff 1 10 13),(.live 13 2),(.live 13 3),(.reader false 4 0),(.es false 4 1),(.es false 4 4),(.reader false 6 0),(.es false 6 1),(.es false 6 4),(.reader false 12 0),(.reader false 12 1),(.reader false 12 2),(.reader false 12 3),(.es false 12 4),(.reader true 4 0),(.reader true 4 1),(.reader true 4 2),(.reader true 4 3),(.reader true 6 0),(.reader true 6 1),(.reader true 6 2),(.reader true 6 3),(.reader true 12 0),(.reader true 12 1),(.reader true 12 2),(.reader true 12 3),(.gate 4 6),(.gate 4 12),(.gate 6 12)]
def r2087 : List Scheme := [(.self 1 0),(.exposure 1 245),(.avoidNot 1 4 245 0),(.exposure 2 314),(.avoidNot 2 1 314 0),(.avoidNot 2 4 314 0),(.self 4 0),(.self 4 1),(.self 4 2),(.self 4 3),(.earlier 9 1),(.earlier 9 2),(.allRes 9 0),(.allRes 9 1),(.exposure 9 5316),(.avoidNot 9 7 5316 0),(.avoidNot 9 10 5316 0),(.avoidNot 9 7 5316 1),(.avoidNot 9 10 5316 1),(.avoidLive 9 5316 2),(.avoidNot 9 7 5316 2),(.avoidNot 9 10 5316 2),(.avoidLive 9 5316 3),(.avoidNot 9 10 5316 3),(.exposure 9 9288),(.avoidNot 9 10 9288 0),(.avoidNot 9 13 9288 0),(.avoidNot 9 10 9288 1),(.avoidNot 9 13 9288 1),(.avoidNot 9 10 9288 2),(.avoidNot 9 13 9288 2),(.avoidLive 9 9288 3),(.exposure 9 13504),(.avoidNot 9 10 13504 0),(.avoidNot 9 10 13504 1),(.avoidNot 9 10 13504 2),(.avoidNot 9 7 13504 3),(.exactAt 9 1 7812),(.seeLab 9 1 7 7812 0),(.seeLab 9 1 10 7812 0),(.seeLab 9 1 7 7812 1),(.seeLab 9 1 10 7812 1),(.seeLive 9 1 7812 2),(.seeLab 9 1 7 7812 2),(.seeLab 9 1 10 7812 2),(.seeLive 9 1 7812 3),(.seeLab 9 1 7 7812 3),(.seeLab 9 1 10 7812 3),(.exactAt 9 5 1548),(.seeLab 9 5 10 1548 0),(.seeLab 9 5 10 1548 1),(.seeLive 9 5 1548 2),(.seeLab 9 5 10 1548 2),(.seeLive 9 5 1548 3),(.exactAt 9 5 9992),(.seeLab 9 5 10 9992 0),(.seeLab 9 5 13 9992 0),(.seeLab 9 5 10 9992 1),(.seeLab 9 5 13 9992 1),(.seeLab 9 5 10 9992 2),(.seeLab 9 5 13 9992 2),(.seeLive 9 5 9992 3),(.diffC 0 9 10),(.diffC 1 9 10),(.adjacentCommon 9 10 5),(.residual 9 10 0 1),(.residual 9 10 0 2),(.residual 9 10 0 3),(.residual 9 10 1 2),(.residual 9 10 1 3),(.residual 9 10 2 3),(.diffX 0 9 13),(.diffC 0 9 13),(.diffX 1 9 13),(.diffC 1 9 13),(.adjacentCommon 9 13 1),(.residual 9 13 0 1),(.residual 9 13 0 2),(.residual 9 13 1 2),(.earlier 10 1),(.someRes 10),(.allRes 10 0),(.allRes 10 1),(.exposure 10 792),(.avoidNot 10 8 792 0),(.avoidNot 10 9 792 0),(.avoidNot 10 8 792 1),(.avoidNot 10 9 792 1),(.avoidNot 10 8 792 2),(.avoidNot 10 9 792 2),(.avoidLive 10 792 3),(.exposure 10 4370),(.avoidNot 10 8 4370 0),(.avoidNot 10 12 4370 0),(.avoidNot 10 8 4370 1),(.avoidNot 10 12 4370 1),(.avoidLive 10 4370 2),(.avoidNot 10 8 4370 2),(.avoidNot 10 12 4370 2),(.avoidLive 10 4370 3),(.exposure 10 8488),(.avoidNot 10 13 8488 0),(.avoidNot 10 8 8488 1),(.avoidNot 10 13 8488 1),(.avoidNot 10 8 8488 2),(.avoidNot 10 13 8488 2),(.avoidLive 10 8488 3),(.exactAt 10 0 1290),(.seeLab 10 0 8 1290 0),(.seeLab 10 0 8 1290 1),(.seeLive 10 0 1290 2),(.seeLive 10 0 1290 3),(.exactAt 10 0 7426),(.seeLab 10 0 12 7426 0),(.seeLab 10 0 8 7426 1),(.seeLab 10 0 8 7426 2),(.seeLive 10 0 7426 3),(.exactAt 10 0 9992),(.seeLab 10 0 8 9992 0),(.seeLab 10 0 9 9992 0),(.seeLab 10 0 13 9992 0),(.seeLab 10 0 8 9992 1),(.seeLab 10 0 9 9992 1),(.seeLab 10 0 13 9992 1),(.seeLab 10 0 8 9992 2),(.seeLab 10 0 9 9992 2),(.seeLab 10 0 13 9992 2),(.seeLive 10 0 9992 3),(.exactAt 10 5 7426),(.seeLab 10 5 8 7426 0),(.seeLab 10 5 12 7426 0),(.seeLab 10 5 8 7426 1),(.seeLab 10 5 12 7426 1),(.seeLive 10 5 7426 2),(.seeLab 10 5 12 7426 2),(.seeLive 10 5 7426 3),(.exactAt 10 5 13504),(.seeLab 10 5 12 13504 0),(.seeLab 10 5 13 13504 1),(.seeLab 10 5 12 13504 2),(.seeLive 10 5 13504 3),(.exactAt 10 5 16256),(.seeLab 10 5 8 16256 0),(.seeLab 10 5 12 16256 1),(.seeLab 10 5 13 16256 2),(.seeLive 10 5 16256 3),(.diffX 0 10 9),(.diffC 0 10 9),(.diffX 1 10 9),(.diffC 1 10 9),(.residual 10 9 0 1),(.residual 10 9 0 2),(.residual 10 9 1 2),(.diffX 0 10 13),(.diffC 0 10 13),(.resCommon 10 13 0),(.diffX 1 10 13),(.diffC 1 10 13),(.resCommon 10 13 1),(.residual 10 13 0 1),(.residual 10 13 0 2),(.residual 10 13 1 2),(.someRes 13),(.allRes 13 0),(.allRes 13 1),(.readerAny false 4),(.readerLab false 4 0 1 true),(.readerLab false 4 0 4 false),(.readerAny false 6),(.readerLab false 6 0 1 false),(.readerLab false 6 0 4 false),(.readerAny false 12),(.readerLab false 12 0 4 true),(.readerLab false 12 1 4 true),(.readerLab false 12 2 4 true),(.readerLab false 12 3 4 true),(.readerAny true 4),(.readerLive true 4 2),(.readerLive true 4 3),(.readerAny true 6),(.readerLive true 6 2),(.readerLive true 6 3),(.readerAny true 12),(.readerLive true 12 2),(.readerLive true 12 3),(.eqLab false 4 6 1 true),(.gateEq true 4 6 0),(.gateEq true 4 6 1),(.eqLab false 4 12 4 false),(.gateEq true 4 12 0),(.gateEq true 4 12 1),(.eqLab false 6 12 4 false),(.gateEq true 6 12 0),(.gateEq true 6 12 1)]

def table2087_0 : List Nat := [833,0x441,0x70402,0x5c1,0x90582,0xa0582,0x641,0x6c1,0x741,0x7c1,0x108b02,0x168d02,0x8d02,0x18d02,0x8e45219044,0x111002]
def table2087_1 : List Nat := [0x121002,0x171082,0x181082,0x169102,0x1b1102,0x1c1102,0x1a9182,0x1f1182,0x9e4d259244,0x121202,0x141202,0x181282,0x191282,0x1c1302,0x1d1302,0x1a9382]
def table2087_2 : List Nat := [0xae55299444,0x121402,0x181482,0x1c1502,0x1e1582,0xbe5d2d9644,0x119602,0x121602,0x179682,0x181682,0x169702,0x1b9702,0x1c1702,0x1a9782,0x1e9782,0x1f1782]
def table2087_3 : List Nat := [0xce65319844,0x129802,0x189882,0x169902,0x1c9902,0x1a9982,0xde6d359a44,0x129a02,0x141a02,0x189a82,0x191a82,0x1c9b02,0x1d1b02,0x1a9b82,0x21c02,0x31c82]
def table2087_4 : List Nat := [0x9c1,0x399c46225100986,0x399c47225160986,0x399c47e251a0986,0x399c47231160986,0x399c47e311a0986,0x399c47e391a0986,0x9d02,0x41d02,0x19d82,0x51d82,0xac1,0x3b9d46629100a86,0x3b9d47629160a86,0x3b9d47633160a86,0x3ca102]
def table2087_5 : List Nat := [0x702a103,0x2a382,0x3a382,0x13e9d4da644,0x3d2602,0x3e2602,0x432682,0x442682,0x482702,0x492702,0x47a782,0x14ea551a844,0x3d2802,0x3f2802,0x432882,0x452882]
def table2087_6 : List Nat := [0x42a902,0x482902,0x4a2902,0x47a982,0x15ead55aa44,0x402a02,0x432a82,0x462a82,0x482b02,0x4b2b02,0x47ab82,0x16eb559ac44,0x3dac02,0x43ac82,0x42ad02,0x47ad82]
def table2087_7 : List Nat := [0x17ebd5dae44,0x3f2e02,0x43ae82,0x48af02,0x47af82,0x18ec561b044,0x3db002,0x3e3002,0x403002,0x43b082,0x443082,0x463082,0x48b102,0x493102,0x4b3102,0x47b182]
def table2087_8 : List Nat := [0x19ecd65b244,0x3d3202,0x3fb202,0x433282,0x45b282,0x42b302,0x4ab302,0x47b382,0x1aed569b444,0x3fb402,0x463482,0x4ab502,0x47b582,0x1bedd6db644,0x3d3602,0x45b682]
def table2087_9 : List Nat := [0x4b3702,0x47b782,0x2b802,0x3802,0x3b882,0x13882,0x71b85127d3c0986,0x71b85267d420986,0x71b852689420986,0x2b902,0x43902,0x83040103,0x3b982,0x53982,0x83050183,0x73b951a813c2086]
def table2087_10 : List Nat := [0x73b952e81422086,0x73b952e8d422086,0xb04ba03,0x4ba82,0x5ba82,0x3b41,0xef063b03,0xf007bb03,0x3cc1,0xf409bc83,0xf60abc83,0x1fefd7dbe44,0x1010c3e03,0x1010d3e83,0x1010e3f03,0x1010f3f83]
def table2087_11 : List Nat := [0x2130782c0c4,0x74c182,0x75c202,0x2230f86c2c4,0x74c382,0x75c402,0x233178ac4c4,0x74c582,0x75c602,0xf5774683,0x11b854083,0x11b864103,0x10078c703,0x11d894083,0x11d8a4103,0x1007bc783]
def table2087_12 : List Nat := [0x11f894283,0x11f8a4303,897,0x481,0x501,0x1cce231128805,0x1cce239128b05,0x1cce23f128d05,0x1cce239188b05,0x1cce23f188d05,0x1cce23f1c8d05,0x1dcea33148805,0x1dcea3b148b05,0x1dcea3b198b05,0x38dc2893e9e05,0x38dc2933ea105]
def table2087_13 : List Nat := [0x38dc29344a105,0x3bc1,0x3c01,0x3d01,0x3d81,0x80be02,0x80be82,0x80bf02,0x80bf82,0x4681,0x854082,0x864102,0x804702,0x804782,0x4041,0x4701]
def table2087_14 : List Nat := [0x4781,0x351c0c03,0x1c471188944,0xe2388e03,0x1c4712c8c44,0xe2389643,0x711c42,0x1d4352c0e44,0xea1a9603,0xea1a8e03,0x3a89e29248b05,0xea1a8c43,0x750d42,0x3a80a9746a105,0x11eb164a144,0x3a80a9760a105]
def table2087_15 : List Nat := [0x3a80a97519ec5,0x1d4054ba104,0x8f429e83,0xea02a5c3,0x47a142,0xea02b083,0x750142,0x3447b003,0x3447a683,0x34479f43,0x1a23c2,0x750942,0x24180e03,0x750c02,0x3a81,0x4201]
def table2087_16 : List Nat := [0x4401,0x4601,0x189182,0x63308b43,0x11ec14ca204,0x38d1ec170a645,0x1c68f60b844,0x74c502,0x3a41,0x7043083,0x1638c0e3b19b046,0x7600203,0xb1c6071d8cc5,0xe347b843,0x624d129c44,0x268b09e771d9d46]
def table2087_17 : List Nat := [0x1caaf63a11ce8260a5c8,0xe557b1d08e7413047,0x31268943,0x189782,0x188e02,0x624d160184,0x31219343,0x623b1601c4,0x311d8b03,0x1890c2,0x188b02,0xc41,0x1081,0x1281,0x1681,0xb41]
def table2087_18 : List Nat := [0x841,0x9a6d3481c4,0x9a6d12a3c4,0x73129c43,0x4d368943,0x268902,0x268942,0x1341,0xe01,0xe81,0x1b01,0x129c42,0x941,0x1001,0x1601,0xd41]
def table2087_19 : List Nat := [0x23c1,321,449,0x1c01,0x1c81,0xfc1,0x1181,0x1781,0x1141,0x1741,0xd81]

def encoded2087 (i : Nat) : Nat :=
  if i < 160 then
    if i < 80 then
      if i < 32 then
        if i < 16 then
          table2087_0.getD (i%16) 0
        else
          table2087_1.getD (i%16) 0
      else
        if i < 48 then
          table2087_2.getD (i%16) 0
        else
          if i < 64 then
            table2087_3.getD (i%16) 0
          else
            table2087_4.getD (i%16) 0
    else
      if i < 112 then
        if i < 96 then
          table2087_5.getD (i%16) 0
        else
          table2087_6.getD (i%16) 0
      else
        if i < 128 then
          table2087_7.getD (i%16) 0
        else
          if i < 144 then
            table2087_8.getD (i%16) 0
          else
            table2087_9.getD (i%16) 0
  else
    if i < 240 then
      if i < 192 then
        if i < 176 then
          table2087_10.getD (i%16) 0
        else
          table2087_11.getD (i%16) 0
      else
        if i < 208 then
          table2087_12.getD (i%16) 0
        else
          if i < 224 then
            table2087_13.getD (i%16) 0
          else
            table2087_14.getD (i%16) 0
    else
      if i < 272 then
        if i < 256 then
          table2087_15.getD (i%16) 0
        else
          table2087_16.getD (i%16) 0
      else
        if i < 288 then
          table2087_17.getD (i%16) 0
        else
          if i < 304 then
            table2087_18.getD (i%16) 0
          else
            table2087_19.getD (i%16) 0
def book2087 (i : Nat) : Clause := let n := encoded2087 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses2087 : inputsOK 2 2087 a2087 r2087 (baseBook book2087 194).toList=true := by decide +kernel

def rows2087_0 : List Nat := [0x40401,0xc0801,0xc0a01,0x1008201,0x1008401,0x1008601,0x1008801,0x1008a01,0x1008c01,0x12c9801,0x12c9a01,0x12c9c01,0x1012c01,0x1012e01,0x1013001,0x2954c02,0x612954e02,0x61aa15202,0x622a15402,0x195801,0x1d5a01,0x215c01,0x255e01,0x69b457202]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2087_0 : checkRows book2087 9 194 rows2087_0=true := by decide +kernel

def rows2087_1 : List Nat := [0x3657401,0x3657601,0x3497801,0x3517e01,0x1b0d76b3555604,0x379b801,0x379ba01,0x3c4a0e148482c2d0a8b04c09,0x50c18a311fa506a0d4a8c8660a,0x444a0e13841c4e1160542c2d06a54500d,0x2807094202a09b89903f4a0585a0d4ab8c220f,0x2014630ac542514849c83f4a0585a0d4ab8c1c10,0x904dc4c60789c4ce5718fd281606a541c0e,0x341e65b3414130706c243a190d8603b1a121464a520583e351e83c4c311b89c301c,0x1a0e3319a3c198d86039193843ae71b8c44e4851929481f1a8f43017,0x1a0e3319a3c198d86037188401c11140e46425708b03a152428c94a40b07c5a351eba0301f,0x703ccb6602890a3252903009,0x11128385413750642038188d86039190583e2d1a8f5d0341dba45017,0x683ccb668e86c3708038280a158a84a290d849d63b74ba07a2d0f85890a325290301d,0x5094134a34ea913c06,0x6d401ad0a6e37a1d0607,0x190f8653aa80f6674f3b4a09a51a75486a3f944d011,0x208b6ee303bcec6c31944ba09,0xf09e7794134a34ea914008]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2087_1 : checkRows book2087 9 218 rows2087_1=true := by decide +kernel

def rows2087_2 : List Nat := [0x17d005b40970c687302150809,0x178d6f0363c8dcf137944da09,0xbc5d36a08d6ee363c8dc60319bcb60c,0x1913e663d9e534a34e9a8d2f327a78a0f428a90ca11,0x15cb2ce67950ee763abd49ef43f3ccfe5a28a4c189506bb0a615,0x2b9659ccf2a1dcec93062541a5a27bd0a60e,0xead03c95cac93062541a7f7a3dcfa0c,0xf47d6733d260c4a834fe4f7a3dcea0c,0x1d5a07c2c960a6557cbe1eef43f969260c4a834f411,0x1e25070bc2e29090b02ac762b18140b1f3d87e527d3b04c14,0x904a201608c4227110a45c09,0xa0941c2f0bb29f829090f9ec3f293e9d81013bec5612,0x2225070bc2e2c0ab2590fd13841f63f293e87cf605bb05014,0x3f96401,0x3f96a01,0x3f97001,0x3f1f148a2fa0b8599207,0x351982c6003,0x583a94cf4572d1fcf807,0x2b1d4a67d2cb42085a3fbd0f20a,0x1e8face679560a7f27bd0ea09,0x59ac182be58ad200ff7037db40a,0x59ac180bd5b41d6eb458c01fee06fc05b60e,0x6534a7d42663d9e5386a27a6936507a148c80f]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2087_2 : checkRows book2087 9 242 rows2087_2=true := by decide +kernel

def rows2087_3 : List Nat := [0xca6750284d07e3e1d6129b4d28894cd23a4e0c9c351fca0f429420c818,0xe27244a0d108045a18e6623096cbe8f46a29209f5026d349c319d10e8c4893ca0f4291e0b881471d8e024,0x572cb399e9323b3494a285950ee76851689ef429420a613,0x572cb399e543b9da0c5a27bd0a60b,0x6533a8142683f1f0eb0b84a6d34a2253308e9386868301c860f06c3d0f941f4f43f9a938521fb15cc391b82a063119420c82b,0x341c663343004,0xf8643a994f66750284d008,0x3227ccc7b3c9d4fc698813cca0a,0x713922506884022d0c7331184b65f47a3514904fa811c812e1e0ed114f2754448878f092364a8f43e5027c35f4f448a310e7f3a1a8c699491447d0e818dc62321cc20e03b,0x3f1f148a2fa178b59207,0x27140441c10890b03a158144c4a0b,0x389c9128344201168639988c25b2fa3d1a8a4827d408e40970f07688a793aa22432c701c248d830951e87c9f0d7d3d1228c439fce86a31a6524511f3207e391dc50331205420e03e,0x10b4da69444a658e038471b061263d0f9421afa7a1fcd49c4a14a2a0a098383210890e6043b8a4222223,0x2169b4d28894cc1c11c6c931e9421afa7a1fcd49c4a148723b8a4222218,0x1c4e48941a21008b431ccc4612d97d1e8d452413ea047204b8783b4453c9d511219838248d92a3d27c35f4f448a310e7f3a1a8c699491447cc81fc5c723b8a420e039,0xc41d0309c603d16194082009,0x42d369a5112996380e11c6c18498f43e5086be9e87f3527128520cc56241e8c028723b8a4222221,0x18896062a8d0a02319898c84e0a,0x46c2401,0x46c3601,0x46c5201,0x78941c2d0b0a8260b8f4704c0a,0x47c1401,0x85a6d34a22532c741a238d830931e87ca10d7d3d0fe6a4e250a50890476221a]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2087_3 : checkRows book2087 9 266 rows2087_3=true := by decide +kernel

def rows2087_4 : List Nat := [0x389c9128344201168639988c25b2fa3d1a8a4827d408e40970f07688a793aa22432c929586a65243e1d0698c360c3847a1f27be9e8914621cfe743518c7f211bc22411f8ec6ce03e,0x78941c2f0bb1dc22c0ab1a3f1b8e4784c0e,0x1f146443f908de4606,0x504a0e1785d943f1f148a2fa0f861f8270c8423d1c8ec6c5615,0xfc7c5228be9c23b9246e4609,0x4964c01,0x49c3a01,0x49c3c01,0x4a07601,0x7a3a7d430a43f91b986f2a94c7c6c0c,0x1c4e48941a21008b431ccc4612d97d1e8d452413ea047204b8783b4453c9d511219a3a248d92a3d2813e1afa7a24518873f9d0d4634ca48a23e958de111f94ca8e039,0x4b02001,0x4b04e01,0x504a0e1685a5d1e96c705609,0x4bdf401,0x4c0a201,0x4c0a401,0x4c47c01,0x4c87e01,0x25f2899cd19404,0x4d42e01,0x4d45e01,0x11c96cd81c03,0x11e974dc4a03]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2087_4 : checkRows book2087 9 290 rows2087_4=true := by decide +kernel

def rows2087_5 : List Nat := [0x4e02801]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk2087_5 : checkRows book2087 9 314 rows2087_5=true := by decide +kernel

def lastUnits2087 := digits 9 2 0x27539
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict2087 : checkReasons book2087 315 43 lastUnits2087 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude2087 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 2087=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=2) h hc bp eq (by decide +kernel)
  let v := truth Z a2087
  have hbase : ValidThrough v book2087 194 := book_start Z h hc z eq _ _ _ _ initialClauses2087
  have h0 : ValidThrough v book2087 218 := rows_sound hbase rows2087_0 rowsOk2087_0
  have h1 : ValidThrough v book2087 242 := rows_sound h0 rows2087_1 rowsOk2087_1
  have h2 : ValidThrough v book2087 266 := rows_sound h1 rows2087_2 rowsOk2087_2
  have h3 : ValidThrough v book2087 290 := rows_sound h2 rows2087_3 rowsOk2087_3
  have h4 : ValidThrough v book2087 314 := rows_sound h3 rows2087_4 rowsOk2087_4
  have h5 : ValidThrough v book2087 315 := rows_sound h4 rows2087_5 rowsOk2087_5
  exact book_end h5 _ _ conflict2087
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
