import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a5190 : Array Fact := #[(.lab 0 0 0),(.lab 0 1 0),(.lab 0 2 0),(.lab 0 3 0),(.res 0 8),(.res 1 8),(.res 0 9),(.res 1 9),(.res 0 13),(.res 1 13),(.lab 1 0 1),(.lab 2 0 2),(.lab 2 0 0),(.avoid 2 8297 0),(.lab 6 0 0),(.lab 6 0 1),(.lab 6 0 2),(.avoid 6 314 0),(.avoid 6 541 0),(.lab 7 0 7),(.lab 7 1 7),(.lab 7 2 7),(.lab 7 3 7),(.live 8 1),(.lab 8 0 9),(.common 8 9),(.lab 8 0 13),(.common 8 13),(.live 8 2),(.lab 8 1 9),(.lab 8 1 13),(.live 8 3),(.lab 8 2 9),(.lab 8 2 13),(.avoid 8 8713 0),(.avoid 8 8713 1),(.avoid 8 8713 2),(.avoid 8 8713 3),(.see 8 2 9992 0),(.see 8 2 9992 1),(.see 8 2 9992 2),(.see 8 2 9992 3),(.see 8 6 9992 0),(.see 8 6 9992 1),(.see 8 6 9992 2),(.see 8 6 9992 3),(.diff 0 8 13),(.diff 1 8 13),(.lab 9 0 9),(.live 9 1),(.lab 9 0 7),(.lab 9 0 8),(.lab 9 0 11),(.common 9 13),(.lab 9 1 9),(.live 9 2),(.lab 9 1 7),(.lab 9 1 8),(.lab 9 1 11),(.lab 9 1 13),(.lab 9 2 9),(.live 9 3),(.lab 9 2 7),(.lab 9 2 8),(.avoid 9 432 0),(.avoid 9 432 1),(.avoid 9 432 2),(.avoid 9 432 3),(.avoid 9 2213 0),(.avoid 9 2213 1),(.avoid 9 2213 2),(.avoid 9 2213 3),(.avoid 9 10656 0),(.avoid 9 10656 1),(.avoid 9 10656 2),(.avoid 9 10656 3),(.see 9 1 5008 0),(.see 9 1 5008 1),(.see 9 1 5008 2),(.see 9 1 5008 3),(.see 9 1 9992 0),(.see 9 1 9992 1),(.see 9 1 9992 2),(.see 9 1 9992 3),(.diff 0 9 8),(.diff 1 9 8),(.lab 11 0 11),(.lab 11 1 11),(.lab 11 2 11),(.lab 11 3 11),(.live 13 1),(.lab 13 0 8),(.lab 13 0 9),(.live 13 2),(.lab 13 1 8),(.lab 13 1 9),(.live 13 3),(.lab 13 2 8),(.lab 13 2 9),(.lab 13 3 8),(.lab 13 3 9),(.avoid 13 792 0),(.avoid 13 792 1),(.avoid 13 792 2),(.avoid 13 792 3),(.see 13 1 8713 0),(.see 13 1 8713 1),(.see 13 1 8713 2),(.see 13 1 8713 3),(.see 13 1 9992 0),(.see 13 1 9992 1),(.see 13 1 9992 2),(.see 13 1 9992 3),(.see 13 2 8488 0),(.see 13 2 8488 1),(.see 13 2 8488 2),(.see 13 2 8488 3),(.see 13 2 9992 0),(.see 13 2 9992 1),(.see 13 2 9992 2),(.see 13 2 9992 3),(.diff 0 13 8),(.diff 1 13 8),(.diff 0 13 9),(.diff 1 13 9),(.reader false 0 0),(.reader false 0 1),(.reader false 0 2),(.reader false 0 3),(.es false 0 0),(.reader false 2 0),(.reader false 3 0),(.es false 3 1),(.reader false 5 0),(.es false 5 0),(.es false 5 2),(.reader false 16 0),(.es false 16 0),(.es false 16 2),(.reader false 17 0),(.es false 17 1),(.reader false 18 0),(.reader true 0 0),(.reader true 0 1),(.reader true 0 2),(.reader true 0 3),(.reader true 2 0),(.reader true 2 1),(.reader true 2 2),(.reader true 2 3),(.es true 2 7),(.reader true 3 0),(.reader true 3 1),(.reader true 3 2),(.reader true 3 3),(.es true 3 7),(.reader true 5 0),(.reader true 5 1),(.reader true 5 2),(.reader true 5 3),(.reader true 16 0),(.reader true 16 1),(.reader true 16 2),(.reader true 16 3),(.es true 16 9),(.reader true 17 0),(.reader true 17 1),(.reader true 17 2),(.reader true 17 3),(.es true 17 9),(.es true 17 11),(.reader true 18 0),(.reader true 18 1),(.reader true 18 2),(.reader true 18 3),(.es true 18 11),(.gate 0 5),(.gate 0 16),(.gate 2 3),(.gate 3 17),(.gate 5 16),(.gate 16 17),(.gate 17 18)]
def r5190 : List Scheme := [(.self 0 0),(.self 0 1),(.self 0 2),(.self 0 3),(.self 1 0),(.self 2 0),(.exposure 2 8297),(.avoidNot 2 0 8297 0),(.exposure 6 314),(.avoidNot 6 1 314 0),(.exposure 6 541),(.avoidNot 6 0 541 0),(.avoidNot 6 2 541 0),(.self 7 0),(.self 7 1),(.self 7 2),(.self 7 3),(.earlier 8 1),(.someRes 8),(.allRes 8 0),(.allRes 8 1),(.exposure 8 8713),(.avoidNot 8 9 8713 0),(.avoidNot 8 13 8713 0),(.avoidLive 8 8713 1),(.avoidNot 8 9 8713 1),(.avoidNot 8 13 8713 1),(.avoidLive 8 8713 2),(.avoidNot 8 9 8713 2),(.avoidNot 8 13 8713 2),(.avoidLive 8 8713 3),(.exactAt 8 2 9992),(.seeLab 8 2 13 9992 0),(.seeLab 8 2 9 9992 1),(.seeLive 8 2 9992 2),(.seeLive 8 2 9992 3),(.exactAt 8 6 9992),(.seeLab 8 6 9 9992 0),(.seeLab 8 6 13 9992 0),(.seeLab 8 6 9 9992 1),(.seeLab 8 6 13 9992 1),(.seeLive 8 6 9992 2),(.seeLab 8 6 9 9992 2),(.seeLab 8 6 13 9992 2),(.seeLive 8 6 9992 3),(.adjacentCommon 8 9 6),(.diffX 0 8 13),(.diffC 0 8 13),(.diffC 1 8 13),(.adjacentCommon 8 13 2),(.residual 8 13 0 1),(.residual 8 13 0 2),(.residual 8 13 1 2),(.self 9 0),(.self 9 1),(.earlier 9 1),(.self 9 2),(.allRes 9 0),(.allRes 9 1),(.exposure 9 432),(.avoidNot 9 7 432 0),(.avoidNot 9 8 432 0),(.avoidNot 9 8 432 1),(.avoidNot 9 7 432 2),(.avoidNot 9 8 432 2),(.avoidLive 9 432 3),(.exposure 9 2213),(.avoidNot 9 7 2213 0),(.avoidNot 9 11 2213 0),(.avoidNot 9 7 2213 1),(.avoidNot 9 11 2213 1),(.avoidLive 9 2213 2),(.avoidLive 9 2213 3),(.exposure 9 10656),(.avoidNot 9 8 10656 0),(.avoidNot 9 13 10656 1),(.avoidNot 9 8 10656 2),(.avoidLive 9 10656 3),(.exactAt 9 1 5008),(.seeLab 9 1 7 5008 0),(.seeLab 9 1 8 5008 0),(.seeLab 9 1 8 5008 1),(.seeLab 9 1 7 5008 2),(.seeLab 9 1 8 5008 2),(.seeLive 9 1 5008 3),(.exactAt 9 1 9992),(.seeLab 9 1 8 9992 0),(.seeLab 9 1 13 9992 1),(.seeLab 9 1 8 9992 2),(.seeLive 9 1 9992 3),(.diffX 0 9 8),(.diffC 0 9 8),(.diffX 1 9 8),(.diffC 1 9 8),(.residual 9 8 0 1),(.residual 9 8 0 2),(.residual 9 8 1 2),(.adjacentCommon 9 13 1),(.self 11 0),(.self 11 1),(.self 11 2),(.self 11 3),(.earlier 13 1),(.earlier 13 2),(.allRes 13 0),(.allRes 13 1),(.exposure 13 792),(.avoidNot 13 8 792 0),(.avoidNot 13 9 792 0),(.avoidLive 13 792 1),(.avoidNot 13 8 792 1),(.avoidNot 13 9 792 1),(.avoidLive 13 792 2),(.avoidNot 13 8 792 2),(.avoidNot 13 9 792 2),(.avoidLive 13 792 3),(.avoidNot 13 8 792 3),(.avoidNot 13 9 792 3),(.exactAt 13 1 8713),(.seeLab 13 1 9 8713 0),(.seeLab 13 1 9 8713 1),(.seeLive 13 1 8713 2),(.seeLive 13 1 8713 3),(.exactAt 13 1 9992),(.seeLab 13 1 8 9992 0),(.seeLab 13 1 9 9992 0),(.seeLab 13 1 8 9992 1),(.seeLab 13 1 9 9992 1),(.seeLive 13 1 9992 2),(.seeLab 13 1 8 9992 2),(.seeLab 13 1 9 9992 2),(.seeLive 13 1 9992 3),(.seeLab 13 1 8 9992 3),(.seeLab 13 1 9 9992 3),(.exactAt 13 2 8488),(.seeLab 13 2 8 8488 0),(.seeLab 13 2 8 8488 1),(.seeLive 13 2 8488 2),(.seeLive 13 2 8488 3),(.exactAt 13 2 9992),(.seeLab 13 2 8 9992 0),(.seeLab 13 2 9 9992 0),(.seeLab 13 2 8 9992 1),(.seeLab 13 2 9 9992 1),(.seeLive 13 2 9992 2),(.seeLab 13 2 8 9992 2),(.seeLab 13 2 9 9992 2),(.seeLive 13 2 9992 3),(.diffC 0 13 8),(.diffX 1 13 8),(.diffC 1 13 8),(.residual 13 8 0 1),(.residual 13 8 0 2),(.residual 13 8 0 3),(.residual 13 8 1 2),(.residual 13 8 1 3),(.residual 13 8 2 3),(.diffX 0 13 9),(.diffC 0 13 9),(.diffX 1 13 9),(.diffC 1 13 9),(.residual 13 9 0 1),(.residual 13 9 0 2),(.residual 13 9 1 2),(.readerAny false 0),(.readerLab false 0 0 0 true),(.readerLab false 0 1 0 true),(.readerLab false 0 2 0 true),(.readerLab false 0 3 0 true),(.readerAny false 2),(.readerAny false 3),(.readerLab false 3 0 1 true),(.readerAny false 5),(.readerLab false 5 0 0 false),(.readerLab false 5 0 2 true),(.readerAny false 16),(.readerLab false 16 0 0 false),(.readerLab false 16 0 2 false),(.readerAny false 17),(.readerLab false 17 0 1 false),(.readerAny false 18),(.readerAny true 0),(.readerLive true 0 2),(.readerLive true 0 3),(.readerAny true 2),(.readerLab true 2 0 7 true),(.readerLab true 2 1 7 true),(.readerLab true 2 2 7 true),(.readerLab true 2 3 7 true),(.readerAny true 3),(.readerLab true 3 0 7 false),(.readerLab true 3 1 7 false),(.readerLive true 3 2),(.readerLive true 3 3),(.readerAny true 5),(.readerLive true 5 2),(.readerLive true 5 3),(.readerAny true 16),(.readerLab true 16 1 9 false),(.readerLive true 16 2),(.readerLive true 16 3),(.readerAny true 17),(.readerLab true 17 0 9 true),(.readerLab true 17 0 11 false),(.readerLab true 17 1 9 true),(.readerLab true 17 1 11 false),(.readerLive true 17 2),(.readerLab true 17 2 9 true),(.readerLive true 17 3),(.readerAny true 18),(.readerLab true 18 0 11 true),(.readerLab true 18 1 11 true),(.readerLab true 18 2 11 true),(.readerLab true 18 3 11 true),(.eqLab false 0 5 0 true),(.gateEq true 0 5 1),(.eqLab false 0 16 0 true),(.gateEq true 0 16 0),(.gateEq false 2 3 0),(.eqLab true 2 3 7 true),(.eqLab false 3 17 1 true),(.gateEq true 3 17 0),(.gateEq true 3 17 1),(.eqLab false 5 16 2 true),(.gateEq true 5 16 0),(.gateEq false 16 17 0),(.eqLab true 16 17 9 false),(.gateEq false 17 18 0),(.eqLab true 17 18 11 false)]

def table5190_0 : List Nat := [65,193,321,449,0x541,0x5c1,0x6c1,0xc0682,0x8c1,0xf0882,0x941,0xe0902,0x100902,0x9c1,0xa41,0xac1]
def table5190_1 : List Nat := [0xb41,0x178e02,0xb048e03,0x48f82,0x58f82,0x9649239144,0x181102,0x1a1102,0x179182,0x1d1182,0x1e1182,0x1c9202,0x201202,0x211202,0x1f9282,0xa651279344]
def table5190_2 : List Nat := [0x1a9302,0x1d1382,0x1c9402,0x1f9482,0xb6592b9544,0x189502,0x1a1502,0x1d9582,0x1e1582,0x1c9602,0x209602,0x211602,0x1f9682,0xcc1,0x49702,0x81702]
def table5190_3 : List Nat := [0x91782,0xdc1,0x2f9747a35170d86,0x2f97486351c0d86,0x2f974863d1c0d86,0x1841,0x1b41,0x319b82,0x1e41,0x69e82,0x79e82,0x10e8541a044,0x322002,0x332002,0x392082,0x3e2102]
def table5190_4 : List Nat := [0x3f2102,0x3da182,0x11e8d45a244,0x322202,0x342202,0x382282,0x3a2282,0x37a302,0x3da382,0x12e9549a444,0x332402,0x3b2482,0x3f2502,0x3da582,0x13e9d4da644,0x32a602]
def table5190_5 : List Nat := [0x332602,0x392682,0x3ea702,0x3f2702,0x3da782,0x14ea551a844,0x332802,0x3ba882,0x3f2902,0x3da982,0x6aa02,0x42a02,0x7aa82,0x52a82,0x55aa4e667310c86,0x55aa4fe67370c86]
def table5190_6 : List Nat := [0x55aa4fe73370c86,0x1ac1,0x2b41,0x2bc1,0x2c41,0x2cc1,0x5aae82,0x5db002,0x8b002,0x9b002,0x1a2cf66b2c4,0x5b3282,0x5c3282,0x5ab302,0x5e3302,0x5f3302]
def table5190_7 : List Nat := [0x5db382,0x613382,0x623382,0x60b402,0x633402,0x643402,0x1b2d76ab4c4,0x5cb482,0x5fb502,0x5db582,0x60b602,0x1c2df6eb6c4,0x5b3682,0x5cb682,0x5e3702,0x5fb702]
def table5190_8 : List Nat := [0x5db782,0x613782,0x62b782,0x60b802,0x633802,0x64b802,0x1d2e772b8c4,0x5bb882,0x5eb902,0x5db982,0x60ba02,0x1e2ef76bac4,0x5bba82,0x5c3a82,0x5ebb02,0x5f3b02]
def table5190_9 : List Nat := [0x5dbb82,0x61bb82,0x623b82,0x60bc02,0x43c82,0x9bd02,0x53d02,0x7abcd7ab75a0d86,0x7abcd86b75d0d86,0x7abcd8eb7600d86,0x7abcd86bd5d0d86,0x7abcd8ebd600d86,0x7abcd8ec3600d86,0x8bd82,0x63d82,0x9be02]
def table5190_10 : List Nat := [0x73e02,0x7cbdd7eb95a1a86,0x7cbdd8ab95d1a86,0x7cbdd8abf5d1a86,0x202ff7ebec4,0x103003e83,0x103013f03,0x103023f83,0x103034003,0x4141,0x41c1,0x1090a4183,0x42c1,0x10c0cc283,0x10f0b4283,0x4441]
def table5190_11 : List Nat := [0x1120ec403,0x11410c403,0x45c1,0x1180fc583,0x46c1,0x247218fc744,0x1cc802,0x1fc882,0x2572993c944,0x12d134903,0x12d144983,0x12d154a03,0x12d164a83,0x26b3398cbc4,0x13632cb83,0x13638cc03]
def table5190_12 : List Nat := [0x37cc82,0x3dcd02,0x27f3d9dce44,0x1ccf02,0x1fcf82,0x28f45a1d044,0x1481dd083,0x1cd102,0x1fd182,0x2a34fa6d2c4,0x153305283,0x15434d283,0x153365303,0x1543ad303,0x37d382,0x1533c5383]
def table5190_13 : List Nat := [0x3dd402,0x2bb5bacd5c4,0x15f565583,0x15f575603,0x15f585683,0x15f595703,0x10d815803,0x1619d4783,0x113815883,0x163a04703,0x165834103,0x137965903,0x119845983,0x167a54b83,0x167a64c03,0x115875a03]
def table5190_14 : List Nat := [0x169a04e03,0x16b8b4403,0x152a4da83,0x16d8d4583,0x15eaadb03,0x601,0x781,0x701,0x801,0x17cba3d1a8b85,0x17cba431a8e05,0x17cba431e8e05,0x2ad5273339885,0x2ad527f339b85,0x2ad527f399b85,0x3d5e6bd5bad05]
def table5190_15 : List Nat := [0x3d5e6c35bae85,0x3d5e6c75bb005,0x3d5e6c35eae85,0x3d5e6c75eb005,0x3d5e6c761b005,0x3e5eebf5cad05,0x3e5eec55cae85,0x3e5eec55fae85,0x81be82,0x81bf02,0x81bf82,0x81c002,0x4241,0x4301,0x43c1,0x4481]
def table5190_16 : List Nat := [0x4501,0x4601,0x96c902,0x96c982,0x96ca02,0x96ca82,0xa9d282,0xa9d302,0xa9d382,0xafd582,0xafd602,0xafd682,0xafd702,0x815802,0x815882,0x5941]
def table5190_17 : List Nat := [0x9bcb02,0x5981,0xa54b82,0xa64c02,0x5a01,0xa04e02,0x5ac1,0xa95242,0x5b41,0xaf5542,0x40c1,0x5801,0x5881,0x3e603683,0x3e603703,0x3e603783]
def table5190_18 : List Nat := [0x1f3002,0x3e5bb303,0x1f3682,0x3e5eb383,0x1f3702,0xf81,0x1281,0x1481,0x1681,0x4881,0x4f81,0x5181,0x7abcdbaba6dadc6,0xf579b3dbaba66b6c7,0x79b3dbaf55d3346,0x3d5e6cf6eae85]
def table5190_19 : List Nat := [0x1e6f567b744,0x19ee566aec4,0xf579b3c3,0x7abcc2,0x174be38239605,0x174be2e2c9105,0xba5f1c11c4,0x5d2f8e03,0x5d2f9183,0x2e97c2,0xf4f15d3384,0xf4f15d3304,0x7a60ae83,0x345e2cf77af85,0x3d3042,0x3001]
def table5190_20 : List Nat := [0x3401,0x3601,0x3c01,0x1e81,0x2181,0x2381,0x2581,0x2781,0x2981,0x4d01,0x5401,0x152ab371fc4,0x152ab372604,0xa9559b83,0x4b41,0x4dc1]
def table5190_21 : List Nat := [0x15437a283,0xaa1bc2,0x168bf5caa04,0x1c9102,0xa40e42,0xcf77ae03,0x1b870b45fae45,0xe174bf62aa85,0x1b870ba67afc5,0x174c55caa04,0x706e5d33c4,0xe174c577aa85,0x6e1c2e83,0x2ec1,0x54c1,0x5241]
def table5190_22 : List Nat := [0xe41,0x1b81,0x5501,0x5781,0x5581,0x5601,0x5681,0x5701]

def encoded5190 (i : Nat) : Nat :=
  if i < 176 then
    if i < 80 then
      if i < 32 then
        if i < 16 then
          table5190_0.getD (i%16) 0
        else
          table5190_1.getD (i%16) 0
      else
        if i < 48 then
          table5190_2.getD (i%16) 0
        else
          if i < 64 then
            table5190_3.getD (i%16) 0
          else
            table5190_4.getD (i%16) 0
    else
      if i < 128 then
        if i < 96 then
          table5190_5.getD (i%16) 0
        else
          if i < 112 then
            table5190_6.getD (i%16) 0
          else
            table5190_7.getD (i%16) 0
      else
        if i < 144 then
          table5190_8.getD (i%16) 0
        else
          if i < 160 then
            table5190_9.getD (i%16) 0
          else
            table5190_10.getD (i%16) 0
  else
    if i < 272 then
      if i < 224 then
        if i < 192 then
          table5190_11.getD (i%16) 0
        else
          if i < 208 then
            table5190_12.getD (i%16) 0
          else
            table5190_13.getD (i%16) 0
      else
        if i < 240 then
          table5190_14.getD (i%16) 0
        else
          if i < 256 then
            table5190_15.getD (i%16) 0
          else
            table5190_16.getD (i%16) 0
    else
      if i < 320 then
        if i < 288 then
          table5190_17.getD (i%16) 0
        else
          if i < 304 then
            table5190_18.getD (i%16) 0
          else
            table5190_19.getD (i%16) 0
      else
        if i < 336 then
          table5190_20.getD (i%16) 0
        else
          if i < 352 then
            table5190_21.getD (i%16) 0
          else
            table5190_22.getD (i%16) 0
def book5190 (i : Nat) : Clause := let n := encoded5190 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses5190 : inputsOK 2 5190 a5190 r5190 (baseBook book5190 229).toList=true := by decide +kernel

def rows5190_0 : List Nat := [0x180e01,0x201201,0x281601,0x281801,0xc46401,0xc46601,0xc46801,0xb4bc01,0xb4be01,0xb4c001,0xc52e01,0xc53001,0xc53201,0xc53401,0xc53601,0xc53801,0x1854201,0x1854401,0x1854601,0x14a01,0x54c01,0x94e01,0xd5001,0x22a95602]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk5190_0 : checkRows book5190 9 229 rows5190_0=true := by decide +kernel

def rows5190_1 : List Nat := [0x72ab15a02,0x2ab15c02,0x73abd6002,0x742bd6202,0x732c96602,0x357201,0x397401,0x3d7601,0x417801,0xd59401,0xd99801,0xe19e01,0x189a401,0x18da601,0x191a801,0x195aa01,0x3f5ac01,0x3fdb001,0x552a5b402,0x43db601,0x80bf1b802,0x445ba01,0x445bc01,0x803f9be02]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk5190_1 : checkRows book5190 9 253 rows5190_1=true := by decide +kernel

def rows5190_2 : List Nat := [0x451c001,0x592bdc202,0x459c401,0x5a2c9c602,0x461c801,0x1f6fa7cbe14804,0x46a1a01,0x46a1c01,0x74389b8d8f1783bcfa7c4a04d2c143319cd40f,0x6b3a1c4deef79bc8fe7e4a04d2c143319cd40f,0x359b8e872783c9e88240a5026960a19cd40e,0x1b8d6713abcde2f442a10f71f8f47528134b050d411,0x371b528134b051de06,0x1c4e06a909b0fa7c4a04d2c1439c81e00d,0x389c128134b051e406,0x33219de87359aa466f441fcfc9409a582873454811212,0x359b8e4f07920902803dc92448339c812c940a04cd412,0x4943c01,0x4944601,0x4945801,0x4956e01,0x4958801,0x4959001,0x211067b40bc1e205]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk5190_2 : checkRows book5190 9 277 rows5190_2=true := by decide +kernel

def rows5190_3 : List Nat := [0x2050af43a9d0e66a35cb0f609,0x74399a8d87d3e4b5e207,0x4220cf67c40bbde46e97199e60a,0x8835218d8873e9f0f68a419cd128033cbcdc0f,0x873521914734499cd607,0xe873351adde66989bd107f3f4c1e60c,0x108833d9f0fc82783c8e471384c9e80c,0xaba8382b154982e06,0x123a44a170b4a05006,0x26143a9d61d0acd6681194498480b,0x130add2eb13868333608ca0480a,0x91d2270d06430299bca04c09,0x4e1f120804a170b05670291106e6f269449c4210,0x8d47bd9ee91391c53c39500e9160b,0x11a927abdd1c6f3727872a01d199160c,0x2491ef67aa30d86b354ee74664f0e5403a39a4d1611,0x1ad166a479bd1805,0xdc8b35234d8773b1e27a903c9c278933d1cd1c10,0x602f349a27204,0x4fce601,0x4fcf401,0x4fd2601,0x4fe7c01,0x50c8201]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk5190_3 : checkRows book5190 9 301 rows5190_3=true := by decide +kernel

def rows5190_4 : List Nat := [0x50c9001,0x50c9a01,0x50ca801,0x50cb201,0x50d8201,0x50da001,0x3f270eca03d288f9daeea251ca40b,0xedd83c2813c6e40a5d107c09,0x12caa492b129d85127530b0532652c6f48a351cae11,0x20b0481c097004,0x53a2001,0xc95eb357e4622b019d4aa4d3e240b,0xc95eb2d7c442190aa0ce6011e9549a7d16260f,0x9f9cbd45c9e2d9686007,0x270f89040250b858442993ca0420b,0xc25ac55b2c5630642b5363b0d6c1b8dcaa531c95c99ae13,0x6e459a91a6ca15011c07,0x4e52a2f99a7528f509280ba5ca6d48600d,0x1394a8be669d4a3dc24a02e970600b,0x27e72f717278b65aa6d5d2555ab198600d,0x9f9cbd85c9e2d9686007,0x4e52a2f99a7528f609280ba5ca6d64d892354f4df58a15006015,0x2729d183d92a8d99a2d288f09282ae5d2e5085e10,0x4fa3c608b9ca345c9eac96cb54dada44e471ad509ee12]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk5190_4 : checkRows book5190 9 325 rows5190_4=true := by decide +kernel

def rows5190_5 : List Nat := [0x3b9e2ab3d481e4e141a1500ec0a,0x21107835299204,0x57a2e01,0x57ea801,0xaed82b802,0x586a201,0x58a3201,0x58e1201,0x58e1401,0x58e1601,0x58e1801]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk5190_5 : checkRows book5190 9 349 rows5190_5=true := by decide +kernel

def lastUnits5190 := digits 9 4 0xb3d9acb64
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict5190 : checkReasons book5190 360 209 lastUnits5190 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude5190 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 5190=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=2) h hc bp eq (by decide +kernel)
  let v := truth Z a5190
  have hbase : ValidThrough v book5190 229 := book_start Z h hc z eq _ _ _ _ initialClauses5190
  have h0 : ValidThrough v book5190 253 := rows_sound hbase rows5190_0 rowsOk5190_0
  have h1 : ValidThrough v book5190 277 := rows_sound h0 rows5190_1 rowsOk5190_1
  have h2 : ValidThrough v book5190 301 := rows_sound h1 rows5190_2 rowsOk5190_2
  have h3 : ValidThrough v book5190 325 := rows_sound h2 rows5190_3 rowsOk5190_3
  have h4 : ValidThrough v book5190 349 := rows_sound h3 rows5190_4 rowsOk5190_4
  have h5 : ValidThrough v book5190 360 := rows_sound h4 rows5190_5 rowsOk5190_5
  exact book_end h5 _ _ conflict5190
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
