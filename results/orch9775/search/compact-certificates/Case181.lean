import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a181 : Array Fact := #[(.lab 0 0 0),(.lab 0 0 6),(.avoid 0 1102 0),(.res 0 8),(.res 1 8),(.res 0 10),(.res 1 10),(.res 0 13),(.res 1 13),(.lab 2 0 2),(.lab 2 0 0),(.lab 2 0 6),(.avoid 2 8297 0),(.lab 4 0 2),(.avoid 4 1102 0),(.lab 6 0 6),(.lab 6 1 6),(.lab 6 2 6),(.lab 6 3 6),(.live 8 1),(.lab 8 0 10),(.common 8 10),(.lab 8 0 13),(.common 8 13),(.live 8 2),(.lab 8 1 10),(.lab 8 1 13),(.live 8 3),(.lab 8 2 10),(.lab 8 2 13),(.avoid 8 9288 0),(.avoid 8 9288 1),(.avoid 8 9288 2),(.avoid 8 9288 3),(.see 8 2 9992 0),(.see 8 2 9992 1),(.see 8 2 9992 2),(.see 8 2 9992 3),(.diff 0 8 10),(.diff 1 8 10),(.lab 10 0 10),(.live 10 1),(.lab 10 0 8),(.lab 10 0 12),(.lab 10 0 13),(.common 10 13),(.lab 10 1 10),(.live 10 2),(.lab 10 1 8),(.lab 10 1 12),(.lab 10 1 13),(.lab 10 2 10),(.live 10 3),(.lab 10 2 8),(.lab 10 2 12),(.lab 10 2 13),(.lab 10 3 8),(.lab 10 3 12),(.avoid 10 4370 0),(.avoid 10 4370 1),(.avoid 10 4370 2),(.avoid 10 4370 3),(.avoid 10 8488 0),(.avoid 10 8488 1),(.avoid 10 8488 2),(.avoid 10 8488 3),(.see 10 0 7426 0),(.see 10 0 7426 1),(.see 10 0 7426 2),(.see 10 0 7426 3),(.see 10 0 9992 0),(.see 10 0 9992 1),(.see 10 0 9992 2),(.see 10 0 9992 3),(.see 10 4 9992 0),(.see 10 4 9992 1),(.see 10 4 9992 2),(.see 10 4 9992 3),(.see 10 5 5190 0),(.see 10 5 5190 1),(.see 10 5 5190 2),(.see 10 5 5190 3),(.see 10 5 7426 0),(.see 10 5 7426 1),(.see 10 5 7426 2),(.see 10 5 7426 3),(.diff 0 10 8),(.diff 1 10 8),(.diff 0 10 13),(.diff 1 10 13),(.lab 13 0 13),(.live 13 1),(.lab 13 0 8),(.lab 13 0 10),(.lab 13 1 13),(.live 13 2),(.lab 13 1 8),(.lab 13 1 10),(.lab 13 2 13),(.live 13 3),(.lab 13 2 8),(.lab 13 2 10),(.lab 13 3 13),(.lab 13 3 8),(.lab 13 3 10),(.avoid 13 1290 0),(.avoid 13 1290 1),(.avoid 13 1290 2),(.avoid 13 1290 3),(.see 13 4 9992 0),(.see 13 4 9992 1),(.see 13 4 9992 2),(.see 13 4 9992 3),(.diff 0 13 8),(.diff 1 13 8),(.reader false 0 0),(.es false 0 0),(.es false 0 6),(.reader false 5 0),(.es false 5 0),(.es false 5 6),(.reader false 6 0),(.es false 6 2),(.reader false 10 0),(.reader false 12 0),(.es false 12 2),(.reader false 16 0),(.reader false 16 1),(.reader false 16 2),(.reader false 16 3),(.es false 16 6),(.reader true 0 0),(.reader true 0 1),(.reader true 0 2),(.reader true 0 3),(.reader true 5 0),(.reader true 5 1),(.reader true 5 2),(.reader true 5 3),(.reader true 6 0),(.reader true 6 1),(.reader true 6 2),(.reader true 6 3),(.reader true 10 0),(.reader true 10 1),(.reader true 10 2),(.reader true 10 3),(.es true 10 8),(.es true 10 10),(.es true 10 13),(.reader true 12 0),(.reader true 12 1),(.reader true 12 2),(.reader true 12 3),(.es true 12 8),(.es true 12 10),(.es true 12 13),(.reader true 16 0),(.reader true 16 1),(.reader true 16 2),(.reader true 16 3),(.gate 0 5),(.gate 0 16),(.gate 5 16),(.gate 6 12),(.gate 10 12)]
def r181 : List Scheme := [(.self 0 0),(.exposure 0 1102),(.avoidNot 0 6 1102 0),(.self 2 0),(.exposure 2 8297),(.avoidNot 2 0 8297 0),(.avoidNot 2 6 8297 0),(.exposure 4 1102),(.avoidNot 4 2 1102 0),(.self 6 0),(.self 6 1),(.self 6 2),(.self 6 3),(.earlier 8 1),(.allRes 8 0),(.allRes 8 1),(.exposure 8 9288),(.avoidNot 8 10 9288 0),(.avoidNot 8 13 9288 0),(.avoidNot 8 10 9288 1),(.avoidNot 8 13 9288 1),(.avoidNot 8 10 9288 2),(.avoidNot 8 13 9288 2),(.avoidLive 8 9288 3),(.exactAt 8 2 9992),(.seeLab 8 2 10 9992 0),(.seeLab 8 2 13 9992 0),(.seeLab 8 2 10 9992 1),(.seeLab 8 2 13 9992 1),(.seeLab 8 2 10 9992 2),(.seeLab 8 2 13 9992 2),(.seeLive 8 2 9992 3),(.diffX 0 8 10),(.diffC 0 8 10),(.diffX 1 8 10),(.diffC 1 8 10),(.adjacentCommon 8 10 0),(.residual 8 10 0 1),(.residual 8 10 0 2),(.residual 8 10 1 2),(.adjacentCommon 8 13 2),(.self 10 0),(.self 10 1),(.earlier 10 1),(.self 10 2),(.earlier 10 2),(.allRes 10 0),(.allRes 10 1),(.exposure 10 4370),(.avoidNot 10 8 4370 0),(.avoidNot 10 12 4370 0),(.avoidNot 10 8 4370 1),(.avoidNot 10 12 4370 1),(.avoidLive 10 4370 2),(.avoidNot 10 8 4370 2),(.avoidNot 10 12 4370 2),(.avoidLive 10 4370 3),(.avoidNot 10 8 4370 3),(.avoidNot 10 12 4370 3),(.exposure 10 8488),(.avoidNot 10 8 8488 0),(.avoidNot 10 13 8488 0),(.avoidNot 10 8 8488 1),(.avoidNot 10 13 8488 1),(.avoidNot 10 8 8488 2),(.avoidNot 10 13 8488 2),(.avoidLive 10 8488 3),(.exactAt 10 0 7426),(.seeLab 10 0 8 7426 0),(.seeLab 10 0 12 7426 0),(.seeLab 10 0 8 7426 1),(.seeLab 10 0 12 7426 1),(.seeLive 10 0 7426 2),(.seeLive 10 0 7426 3),(.exactAt 10 0 9992),(.seeLab 10 0 8 9992 0),(.seeLab 10 0 13 9992 0),(.seeLab 10 0 8 9992 1),(.seeLab 10 0 13 9992 1),(.seeLab 10 0 8 9992 2),(.seeLab 10 0 13 9992 2),(.seeLive 10 0 9992 3),(.exactAt 10 4 9992),(.seeLab 10 4 8 9992 0),(.seeLab 10 4 13 9992 0),(.seeLab 10 4 8 9992 1),(.seeLab 10 4 8 9992 2),(.seeLab 10 4 13 9992 2),(.seeLive 10 4 9992 3),(.exactAt 10 5 5190),(.seeLab 10 5 12 5190 0),(.seeLab 10 5 12 5190 1),(.seeLive 10 5 5190 2),(.seeLive 10 5 5190 3),(.exactAt 10 5 7426),(.seeLab 10 5 8 7426 0),(.seeLab 10 5 12 7426 0),(.seeLab 10 5 8 7426 1),(.seeLab 10 5 12 7426 1),(.seeLab 10 5 8 7426 2),(.seeLab 10 5 12 7426 2),(.seeLive 10 5 7426 3),(.seeLab 10 5 8 7426 3),(.seeLab 10 5 12 7426 3),(.diffC 0 10 8),(.diffC 1 10 8),(.residual 10 8 0 1),(.residual 10 8 0 2),(.residual 10 8 0 3),(.residual 10 8 1 2),(.residual 10 8 1 3),(.residual 10 8 2 3),(.diffX 0 10 13),(.diffC 0 10 13),(.diffX 1 10 13),(.diffC 1 10 13),(.adjacentCommon 10 13 4),(.residual 10 13 0 1),(.residual 10 13 0 2),(.residual 10 13 1 2),(.self 13 0),(.self 13 1),(.earlier 13 1),(.self 13 2),(.earlier 13 2),(.self 13 3),(.exposure 13 1290),(.avoidNot 13 8 1290 0),(.avoidNot 13 10 1290 0),(.avoidNot 13 8 1290 1),(.avoidNot 13 10 1290 1),(.avoidLive 13 1290 2),(.avoidNot 13 8 1290 2),(.avoidNot 13 10 1290 2),(.avoidLive 13 1290 3),(.avoidNot 13 8 1290 3),(.avoidNot 13 10 1290 3),(.exactAt 13 4 9992),(.seeLab 13 4 8 9992 0),(.seeLab 13 4 8 9992 1),(.seeLab 13 4 8 9992 2),(.seeLab 13 4 10 9992 3),(.diffX 0 13 8),(.diffC 0 13 8),(.diffX 1 13 8),(.diffC 1 13 8),(.residual 13 8 0 1),(.residual 13 8 0 2),(.residual 13 8 0 3),(.residual 13 8 1 2),(.residual 13 8 1 3),(.residual 13 8 2 3),(.readerAny false 0),(.readerLab false 0 0 0 true),(.readerLab false 0 0 6 false),(.readerAny false 5),(.readerLab false 5 0 0 false),(.readerLab false 5 0 6 false),(.readerAny false 6),(.readerLab false 6 0 2 true),(.readerAny false 10),(.readerAny false 12),(.readerLab false 12 0 2 false),(.readerAny false 16),(.readerLab false 16 0 6 true),(.readerLab false 16 1 6 true),(.readerLab false 16 2 6 true),(.readerLab false 16 3 6 true),(.readerAny true 0),(.readerLive true 0 2),(.readerLive true 0 3),(.readerAny true 5),(.readerLive true 5 2),(.readerLive true 5 3),(.readerAny true 6),(.readerLive true 6 1),(.readerLive true 6 2),(.readerLive true 6 3),(.readerAny true 10),(.readerLab true 10 0 8 false),(.readerLab true 10 0 10 true),(.readerLab true 10 0 13 false),(.readerLab true 10 1 8 false),(.readerLab true 10 1 10 true),(.readerLab true 10 1 13 false),(.readerLab true 10 2 8 false),(.readerLab true 10 2 10 true),(.readerLab true 10 2 13 false),(.readerLive true 10 3),(.readerAny true 12),(.readerLab true 12 0 8 true),(.readerLab true 12 0 10 false),(.readerLab true 12 0 13 true),(.readerLive true 12 1),(.readerLab true 12 1 8 true),(.readerLab true 12 1 10 false),(.readerLab true 12 1 13 true),(.readerLive true 12 2),(.readerLab true 12 2 8 true),(.readerLab true 12 2 10 false),(.readerLab true 12 2 13 true),(.readerLive true 12 3),(.readerLab true 12 3 8 true),(.readerLab true 12 3 13 true),(.readerAny true 16),(.readerLive true 16 2),(.readerLive true 16 3),(.eqLab false 0 5 0 true),(.gateEq true 0 5 0),(.gateEq true 0 5 1),(.eqLab false 0 16 6 false),(.gateEq true 0 16 0),(.gateEq true 0 16 1),(.eqLab false 5 16 6 false),(.gateEq true 5 16 0),(.gateEq true 5 16 1),(.eqLab false 6 12 2 true),(.gateEq true 6 12 0),(.gateEq false 10 12 0),(.eqLab true 10 12 8 false),(.eqLab true 10 12 10 true),(.eqLab true 10 12 13 false)]

def table181_0 : List Nat := [65,321,0x10102,0x4c1,0x641,0xa0602,0xb0602,0x741,0xd0702,0x7c1,0x841,0x8c1,0x941,0x138c02,0x38d82,0x48d82]
def table181_1 : List Nat := [0x86411f8f44,0x140f02,0x160f02,0x190f82,0x1a0f82,0x1c1002,0x1d1002,0x1b9082,0x9649239144,0x141102,0x169102,0x191182,0x1a9182,0x1c1202,0x1d9202,0x1b9282]
def table181_2 : List Nat := [0x39302,0x51302,0x49382,0x61382,0xac1,0x279346629130a86,0x279347229180a86,0x279347233180a86,0xbc1,0x1441,0x1741,0x299782,0x19c1,0x2f9a02,0x59a02,0x69a02]
def table181_3 : List Nat := [0xf6793b9d44,0x2a1d02,0x2b1d02,0x301d82,0x311d82,0x2f9e02,0x351e02,0x361e02,0x349e82,0x381e82,0x391e82,0x106813f9f44,0x2a1f02,0x2c1f02,0x301f82,0x321f82]
def table181_4 : List Nat := [0x352002,0x372002,0x34a082,0x1168943a144,0x2aa102,0x2b2102,0x30a182,0x312182,0x2fa202,0x34a282,0x1269147a344,0x2aa302,0x2c2302,0x30a382,0x322382,0x35a402]
def table181_5 : List Nat := [0x372402,0x34a482,0x136994ba544,0x2a2502,0x2ca502,0x302582,0x352602,0x37a602,0x34a682,0x146a14fa744,0x2ba702,0x31a782,0x2fa802,0x34a882,0x156a953a944,0x2a2902]
def table181_6 : List Nat := [0x2ba902,0x302982,0x31a982,0x352a02,0x36aa02,0x34aa82,0x382a82,0x39aa82,0x32b02,0x42b82,0x57ab4c255290a86,0x57ab4d6552f0a86,0x57ab4e255340a86,0x57ab4d6612f0a86,0x57ab4e261340a86,0x57ab4e26b340a86]
def table181_7 : List Nat := [0x5ac02,0x72c02,0x6ac82,0x82c82,0x16c1,0x59ac4ca59291686,0x59ac4de592f1686,0x59ac4de652f1686,0x2d41,0x2f41,0x5baf82,0x3141,0x5fb182,0x3341,0x1b2d76ab4c4,0x5c3482]
def table181_8 : List Nat := [0x5d3482,0x603502,0x613502,0x5fb582,0x643582,0x653582,0x63b602,0x673602,0x683602,0x1c2df6eb6c4,0x5c3682,0x603702,0x643782,0x68b802,0x7b882,0x33882]
def table181_9 : List Nat := [0x8b902,0x43902,0x72b8d82b95b0b86,0x72b8d92b95f0b86,0x72b8d9eb9630b86,0x72b8d92c15f0b86,0x72b8d9ec1630b86,0x72b8d9ec9630b86,0x39c1,0xe9003983,0xea01b983,0x3b41,0xee0abb03,0xf00bbb03,0x3cc1,0xf5093c83]
def table181_10 : List Nat := [0x3dc1,0x3e41,0xfa0dbe03,0x207017fbf44,0x1050f3f03,0x105103f83,0x105114003,0x105124083,0x21b0b84c1c4,0x18c282,0x1bc302,0x22b1388c3c4,0x18c482,0x1bc502,0x23b1b8cc5c4,0x5bc602]
def table181_11 : List Nat := [0x5fc682,0x63c702,0x24b2390c7c4,0x1262ac783,0x129284783,0x12a2cc783,0x12630c803,0x1292e4803,0x12a32c803,0x12635c883,0x129334883,0x12a37c883,0x34c902,0x2673197cb44,0x1355c4b03,0x1365dcb03]
def table181_12 : List Nat := [0x1395a4b03,0x5bcb82,0x135604b83,0x13661cb83,0x1395e4b83,0x5fcc02,0x135644c03,0x13665cc03,0x139624c03,0x63cc82,0x135674c83,0x139664c83,0x2833f9ecec4,0x18cf82,0x1bd002,0xef745083]
def table181_13 : List Nat := [0x143874183,0x143884203,0x10475d103,0x1459d4183,0x1459e4203,0x10478d183,0x1479d4383,0x1479e4403,0xfb7a5203,0x149964583,0x14b7c3d83,0x13493d283,0x137945283,0x13895d283,129,0x501]
def table181_14 : List Nat := [0x581,0x681,0x13c9a33148985,0x13c9a39148c05,0x13c9a39198c05,0x2bd5a612a9485,0x2bd5a6b2a9785,0x2bd5a712a9a05,0x2bd5a6b309785,0x2bd5a71309a05,0x2bd5a71359a05,0x2cd62652c9485,0x2cd626f2c9785,0x2cd626f329785,0x395c6c15cad85,0x395c6c95caf85]
def table181_15 : List Nat := [0x395c6cf5cb185,0x395c6c960af85,0x395c6cf60b185,0x395c6cf64b185,0x3a41,0x3a81,0x3b81,0x3c01,0x3d41,0x3e81,0x82bf02,0x82bf82,0x82c002,0x82c082,0x94c782,0x94c802]
def table181_16 : List Nat := [0x94c882,0x9ccb02,0x9ccb82,0x9ccc02,0x9ccc82,0x5081,0x874182,0x884202,0x825102,0x825182,0x5201,0x964582,0x52c1,0x9a49c2,0x9bca02,0x9c4ac2]
def table181_17 : List Nat := [0x4141,0x5101,0x5181,0x6a301503,0x6c68351804,0x36341a83,0x1b1a02,0x1a65526359545,0xd32a932a04,0x36549d83,0x362a9843,0x1b1d02,0x1b1542,0x1b1802,0x1b17c2,0xd81]
def table181_18 : List Nat := [0x1081,0x1281,0x4301,0x4501,0x5001,0x10e694f97c4,0x19ec672b8c4,0x9a4f181204,0x9a4f180f04,0x9a4f180f84,0x4d278c03,0x18cf02,0xc41,0x1cae39acc84,0x395c7355ccb85,0x395c7359b3485]
def table181_19 : List Nat := [0x72b8da6b98bafc6,0xe571b603,0x72b8e6ac197af86,0x395c7359b3505,0x1cae39acd84,0x92ca42,0x4e41,0x4ac1,0x47938d2a72f1506,0x59a0cbc6f40ac46,0xc24e3498c4,0x1864a6b8fc985,0xc275271a44,0x613a9383,0x16b3461784,0x10e753497c4]
def table181_20 : List Nat := [0x11e0b2f2cc4,0xea7b55c964ca990a408,0x309d42,0x6134c983,0x1369aac83,0x309a42,0x1a01,0x1e81,0x2081,0x2281,0x2481,0x2681,0x2881,0x2a81,0x4901,0x1841]
def table181_21 : List Nat := [0x4a41,0x1d81,0x1f81,0x2581,0x2981,0x4dc1,0x1a81,0x2401,0x17c1,0x14c1,0xb3589943,0x2723c2,0x9a9382,0x4d41,0x49c1,0x2a01]
def table181_22 : List Nat := [0x1541,0x2941]

def encoded181 (i : Nat) : Nat :=
  if i < 176 then
    if i < 80 then
      if i < 32 then
        if i < 16 then
          table181_0.getD (i%16) 0
        else
          table181_1.getD (i%16) 0
      else
        if i < 48 then
          table181_2.getD (i%16) 0
        else
          if i < 64 then
            table181_3.getD (i%16) 0
          else
            table181_4.getD (i%16) 0
    else
      if i < 128 then
        if i < 96 then
          table181_5.getD (i%16) 0
        else
          if i < 112 then
            table181_6.getD (i%16) 0
          else
            table181_7.getD (i%16) 0
      else
        if i < 144 then
          table181_8.getD (i%16) 0
        else
          if i < 160 then
            table181_9.getD (i%16) 0
          else
            table181_10.getD (i%16) 0
  else
    if i < 272 then
      if i < 224 then
        if i < 192 then
          table181_11.getD (i%16) 0
        else
          if i < 208 then
            table181_12.getD (i%16) 0
          else
            table181_13.getD (i%16) 0
      else
        if i < 240 then
          table181_14.getD (i%16) 0
        else
          if i < 256 then
            table181_15.getD (i%16) 0
          else
            table181_16.getD (i%16) 0
    else
      if i < 320 then
        if i < 288 then
          table181_17.getD (i%16) 0
        else
          if i < 304 then
            table181_18.getD (i%16) 0
          else
            table181_19.getD (i%16) 0
      else
        if i < 336 then
          table181_20.getD (i%16) 0
        else
          if i < 352 then
            table181_21.getD (i%16) 0
          else
            table181_22.getD (i%16) 0
def book181 (i : Nat) : Clause := let n := encoded181 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses181 : inputsOK 2 181 a181 r181 (baseBook book181 222).toList=true := by decide +kernel

def rows181_0 : List Nat := [0x40401,0x100a01,0x100c01,0x1c1001,0x904a01,0x904c01,0x904e01,0x90d401,0x90d601,0x90d801,0x90da01,0x90dc01,0x90de01,0x1d0ea01,0x1d0ec01,0x1d0ee01,0xa12401,0xa12601,0xa12801,0xa12a01,0xa12c01,0xa12e01,0x2613202,0x6f2613402]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk181_0 : checkRows book181 9 222 rows181_0=true := by decide +kernel

def rows181_1 : List Nat := [0x6fa6d3802,0x7026d3a02,0x1a793e02,0x70a854402,0x254801,0x294a01,0x2d4c01,0x314e01,0xa56801,0xa96e01,0xb17401,0x1e18001,0x1e58801,0x1ed9001,0x1f59601,0x7b3d19e02,0x415a001,0x415a201,0x3d5a401,0x3ddaa01,0x7cbe1b002,0x429b201,0x50a81b402,0x431b601]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk181_1 : checkRows book181 9 246 rows181_1=true := by decide +kernel

def rows181_2 : List Nat := [0x431b801,0x431ba01,0x1fafc7dbe94604,0x4421001,0x4421201,0xe8bc302f8c46c6319984ce09,0x322f0c0cc3973c4cc23334038d20f1b18cc00f,0x1a178605f1899872e574c50c63634038d20f158b4c412,0x1b978605f1898466661cb99d0ea8a8b4d00e3483cc812,0x139644a5992ca2bc27ae57009,0x131644a5b134663018c5c6eb927990c63828af16a11,0xac86e52217cbc62230d06668071a41e4932c589011,0x2b21b948c68071a41e498b110900b,0x472c90cb8487318cbc618d180b444190c4d00e3483c925d32c58b617,0x6c35180ce3468071a41e388b46dcc0c,0x41290ecaa3e211622c3c29c70ae0b,0xb45b228d086302e1206a38249762d1b23474b210,0xc0c6367447a3b1b1c458d2680783a320d,0x47c2e01,0x47c3e01,0x47d5401,0x47d5a01,0x47d9c01,0x452c90cb84824974b407]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk181_2 : checkRows book181 9 270 rows181_2=true := by decide +kernel

def rows181_3 : List Nat := [0x110893f231088b40a28fef3793c11a0c,0x22130b38dc81e0ec802008,0x361a71048220d93c843008,0x321c71050260d93c843008,0x190db8dc815084a6512790484300b,0x55aa1aed454ab24722894460c0a,0x55aa1acd3664ad9aac54c8e451288c920e0e,0x653264c02,0x61305dc02,0x18cc55ecb97e803fcb5de08,0x2055e7e572c50cb0419f1dc09,0x43a1a4c02,0x5f319dcf13d4b57a06,0x85af97ac59930d048196cbe600a,0x3097cc778bbd0a84419fa672f98cb57a0d,0x1007fbf96403,0x20903814057a04,0x4da1e01,0x823f763ace28e9a436304c2513cc65e2f8f122223908c845132c3a6abc15cdc761c,0x7e3d76bb07604,0x2cd6d0d9a238e3395d900a04f2512e71253116c8c4d48888e423211461d355e4dd641d,0x5cad96402,0xfc82eb761c51d3486ced6a3c2612c944f158d86a301a4ea1d355e144843826a44447211cdc7621,0x9e08c5e02]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk181_3 : checkRows book181 9 294 rows181_3=true := by decide +kernel

def rows181_4 : List Nat := [0x3f20badd82b381085c4c1e12c760b,0x16c61251a8e06805,0x100a04f254f8e042288ba7209,0x5f312cc68b2182ec6c5027cdcbc0b,0x341b18a765e5a97c984b255056d1886cd12073a04fe1d355e194a2381723c4220954f48c4d9bcb06023,0x166b65e2eca04a2892c634226cdd640c,0x4134952404673394b11e08,0x38cd27291114a84340a24368640871409e489a92886bc289248446269109631a14b11c1e,0x8c422f174b25405,0x5187001,0x5188401,0x5189201,0x518a201,0x518b001,0x518ba01,0x518ca01,0x5197801,0x51a8a01,0x53a6a01,0x53c6601,0x53c7c01,0x53caa01,0x53cc201,0x5421c01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk181_4 : checkRows book181 9 318 rows181_4=true := by decide +kernel

def rows181_5 : List Nat := [0xf4a43b2b1029753a4548a809,0x5589e01,0x472c90cb444190c4605c240d69949a8d1cb60f,0x5605601,0x7a4175bb6b159a95207608,0x4a9c562a946abd289607,0x13ab471474d12222a2556b609,0xad500e021955728958965549c0a,0x5761a01,0x1469bd7a3003,0x28d37ab57a2e04,0x14daa57cbc03]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk181_5 : checkRows book181 9 342 rows181_5=true := by decide +kernel

def lastUnits181 := digits 9 2 0x2c161
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict181 : checkReasons book181 354 95 lastUnits181 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude181 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 181=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=2) h hc bp eq (by decide +kernel)
  let v := truth Z a181
  have hbase : ValidThrough v book181 222 := book_start Z h hc z eq _ _ _ _ initialClauses181
  have h0 : ValidThrough v book181 246 := rows_sound hbase rows181_0 rowsOk181_0
  have h1 : ValidThrough v book181 270 := rows_sound h0 rows181_1 rowsOk181_1
  have h2 : ValidThrough v book181 294 := rows_sound h1 rows181_2 rowsOk181_2
  have h3 : ValidThrough v book181 318 := rows_sound h2 rows181_3 rowsOk181_3
  have h4 : ValidThrough v book181 342 := rows_sound h3 rows181_4 rowsOk181_4
  have h5 : ValidThrough v book181 354 := rows_sound h4 rows181_5 rowsOk181_5
  exact book_end h5 _ _ conflict181
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
