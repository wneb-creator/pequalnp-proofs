import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a298 : Array Fact := #[(.res 0 6),(.res 0 9),(.res 0 11),(.res 0 13),(.lab 1 0 1),(.lab 1 0 6),(.avoid 1 245 0),(.lab 5 0 1),(.lab 5 0 6),(.avoid 5 1102 0),(.lab 6 0 6),(.common 6 9),(.lab 6 1 6),(.live 6 2),(.lab 6 2 6),(.lab 7 0 7),(.lab 7 1 7),(.lab 7 2 7),(.lab 8 0 9),(.lab 8 0 11),(.avoid 8 541 0),(.avoid 8 2087 0),(.lab 9 0 9),(.live 9 1),(.lab 9 0 6),(.lab 9 0 7),(.common 9 11),(.lab 9 0 12),(.lab 9 0 13),(.common 9 13),(.lab 9 1 9),(.live 9 2),(.lab 9 1 6),(.lab 9 1 7),(.lab 9 1 12),(.lab 9 1 13),(.lab 9 2 9),(.lab 9 2 6),(.lab 9 2 7),(.lab 9 2 12),(.lab 9 2 13),(.avoid 9 4309 0),(.avoid 9 4309 1),(.avoid 9 4309 2),(.avoid 9 8297 0),(.avoid 9 8297 1),(.avoid 9 8297 2),(.avoid 9 12481 0),(.avoid 9 12481 1),(.avoid 9 12481 2),(.see 9 1 4757 0),(.see 9 1 4757 1),(.see 9 1 4757 2),(.see 9 5 14977 0),(.see 9 5 14977 1),(.see 9 5 14977 2),(.diff 0 9 6),(.diff 0 9 13),(.lab 11 0 11),(.live 11 1),(.lab 11 0 7),(.lab 11 0 9),(.lab 11 1 11),(.live 11 2),(.lab 11 1 7),(.lab 11 1 9),(.lab 11 1 12),(.lab 11 2 11),(.lab 11 2 7),(.lab 11 2 9),(.avoid 11 4757 0),(.avoid 11 4757 1),(.avoid 11 4757 2),(.see 11 3 6789 0),(.see 11 3 6789 1),(.see 11 3 6789 2),(.see 11 3 16256 0),(.see 11 3 16256 1),(.see 11 3 16256 2),(.diff 0 11 9),(.lab 12 0 12),(.lab 12 1 12),(.lab 12 2 12),(.lab 13 0 6),(.lab 13 0 7),(.live 13 2),(.lab 13 1 6),(.lab 13 1 7),(.lab 13 1 9),(.avoid 13 245 0),(.avoid 13 245 1),(.avoid 13 245 2),(.avoid 13 4757 0),(.avoid 13 4757 1),(.avoid 13 4757 2),(.see 13 1 8417 0),(.see 13 1 8417 1),(.see 13 1 8417 2),(.reader false 2 0),(.reader false 3 0),(.es false 3 1),(.es false 3 6),(.reader false 4 0),(.reader false 13 0),(.es false 13 1),(.es false 13 6),(.reader false 15 0),(.reader false 16 0),(.reader false 16 1),(.reader false 16 2),(.reader false 17 0),(.reader false 17 1),(.reader false 17 2),(.es false 17 6),(.reader false 18 0),(.reader false 18 1),(.reader false 18 2),(.reader true 2 0),(.reader true 2 1),(.reader true 2 2),(.es true 2 7),(.reader true 3 0),(.reader true 3 1),(.reader true 3 2),(.es true 3 6),(.es true 3 7),(.es true 3 9),(.reader true 4 0),(.reader true 4 1),(.reader true 4 2),(.es true 4 6),(.es true 4 7),(.es true 4 9),(.reader true 13 0),(.reader true 13 1),(.reader true 13 2),(.es true 13 12),(.reader true 15 0),(.reader true 15 1),(.reader true 15 2),(.es true 15 12),(.reader true 16 0),(.es true 16 9),(.es true 16 11),(.reader true 17 0),(.reader true 17 1),(.reader true 17 2),(.es true 17 9),(.reader true 18 0),(.reader true 18 1),(.reader true 18 2),(.es true 18 9),(.es true 18 11),(.gate 2 3),(.gate 2 4),(.gate 3 4),(.gate 3 13),(.gate 3 17),(.gate 13 15),(.gate 13 17),(.gate 16 17),(.gate 16 18),(.gate 17 18)]
def r298 : List Scheme := [(.self 1 0),(.exposure 1 245),(.avoidNot 1 6 245 0),(.exposure 5 1102),(.avoidNot 5 1 1102 0),(.avoidNot 5 6 1102 0),(.self 6 0),(.self 6 1),(.self 6 2),(.someRes 6),(.resCommon 6 9 0),(.self 7 0),(.self 7 1),(.self 7 2),(.exposure 8 541),(.avoidNot 8 9 541 0),(.exposure 8 2087),(.avoidNot 8 11 2087 0),(.self 9 0),(.self 9 1),(.earlier 9 1),(.self 9 2),(.someRes 9),(.exposure 9 4309),(.avoidNot 9 6 4309 0),(.avoidNot 9 7 4309 0),(.avoidNot 9 12 4309 0),(.avoidNot 9 6 4309 1),(.avoidNot 9 7 4309 1),(.avoidNot 9 12 4309 1),(.avoidNot 9 6 4309 2),(.avoidNot 9 7 4309 2),(.avoidNot 9 12 4309 2),(.exposure 9 8297),(.avoidNot 9 6 8297 0),(.avoidNot 9 13 8297 0),(.avoidNot 9 6 8297 1),(.avoidNot 9 13 8297 1),(.avoidNot 9 6 8297 2),(.exposure 9 12481),(.avoidNot 9 7 12481 0),(.avoidNot 9 12 12481 0),(.avoidNot 9 13 12481 0),(.avoidNot 9 7 12481 1),(.avoidNot 9 12 12481 1),(.avoidNot 9 13 12481 1),(.avoidNot 9 7 12481 2),(.avoidNot 9 13 12481 2),(.exactAt 9 1 4757),(.seeLab 9 1 7 4757 0),(.seeLab 9 1 7 4757 1),(.seeLab 9 1 12 4757 2),(.exactAt 9 5 14977),(.seeLab 9 5 7 14977 0),(.seeLab 9 5 12 14977 0),(.seeLab 9 5 13 14977 0),(.seeLab 9 5 7 14977 1),(.seeLab 9 5 12 14977 1),(.seeLab 9 5 13 14977 1),(.seeLab 9 5 7 14977 2),(.seeLab 9 5 12 14977 2),(.seeLab 9 5 13 14977 2),(.diffC 0 9 6),(.residual 9 6 0 1),(.residual 9 6 0 2),(.residual 9 6 1 2),(.resCommon 9 11 0),(.diffC 0 9 13),(.adjacentCommon 9 13 1),(.residual 9 13 0 1),(.residual 9 13 0 2),(.residual 9 13 1 2),(.self 11 0),(.self 11 1),(.earlier 11 1),(.self 11 2),(.someRes 11),(.exposure 11 4757),(.avoidNot 11 7 4757 0),(.avoidNot 11 9 4757 0),(.avoidNot 11 7 4757 1),(.avoidNot 11 9 4757 1),(.avoidNot 11 12 4757 1),(.avoidLive 11 4757 2),(.avoidNot 11 7 4757 2),(.avoidNot 11 9 4757 2),(.exactAt 11 3 6789),(.seeLab 11 3 7 6789 0),(.seeLab 11 3 9 6789 0),(.seeLab 11 3 9 6789 1),(.seeLab 11 3 12 6789 1),(.seeLive 11 3 6789 2),(.exactAt 11 3 16256),(.seeLab 11 3 7 16256 0),(.seeLab 11 3 9 16256 0),(.seeLab 11 3 7 16256 1),(.seeLab 11 3 9 16256 1),(.seeLab 11 3 7 16256 2),(.seeLab 11 3 9 16256 2),(.diffC 0 11 9),(.residual 11 9 0 1),(.residual 11 9 0 2),(.residual 11 9 1 2),(.self 12 0),(.self 12 1),(.self 12 2),(.someRes 13),(.exposure 13 245),(.avoidNot 13 7 245 0),(.avoidNot 13 7 245 1),(.avoidLive 13 245 2),(.exposure 13 4757),(.avoidNot 13 7 4757 0),(.avoidNot 13 9 4757 1),(.avoidLive 13 4757 2),(.exactAt 13 1 8417),(.seeLab 13 1 6 8417 0),(.seeLab 13 1 7 8417 0),(.seeLab 13 1 6 8417 1),(.seeLab 13 1 7 8417 1),(.seeLive 13 1 8417 2),(.readerAny false 2),(.readerAny false 3),(.readerLab false 3 0 1 true),(.readerLab false 3 0 6 false),(.readerAny false 4),(.readerAny false 13),(.readerLab false 13 0 1 false),(.readerLab false 13 0 6 false),(.readerAny false 15),(.readerAny false 16),(.readerLive false 16 2),(.readerAny false 17),(.readerLab false 17 0 6 true),(.readerLab false 17 1 6 true),(.readerLive false 17 2),(.readerLab false 17 2 6 true),(.readerAny false 18),(.readerLive false 18 2),(.readerAny true 2),(.readerLab true 2 0 7 true),(.readerLab true 2 1 7 true),(.readerLab true 2 2 7 true),(.readerAny true 3),(.readerLab true 3 0 6 true),(.readerLab true 3 0 7 false),(.readerLab true 3 0 9 true),(.readerLab true 3 1 6 true),(.readerLab true 3 1 7 false),(.readerLab true 3 1 9 true),(.readerLive true 3 2),(.readerLab true 3 2 6 true),(.readerLab true 3 2 7 false),(.readerLab true 3 2 9 true),(.readerAny true 4),(.readerLab true 4 0 6 false),(.readerLab true 4 0 7 false),(.readerLab true 4 1 6 false),(.readerLab true 4 1 9 false),(.readerLive true 4 2),(.readerAny true 13),(.readerLab true 13 0 12 false),(.readerLab true 13 1 12 false),(.readerLive true 13 2),(.readerLab true 13 2 12 false),(.readerAny true 15),(.readerLab true 15 0 12 true),(.readerLab true 15 1 12 true),(.readerLab true 15 2 12 true),(.readerAny true 16),(.readerLab true 16 0 9 false),(.readerLab true 16 0 11 false),(.readerAny true 17),(.readerLab true 17 0 9 true),(.readerLab true 17 1 9 true),(.readerLive true 17 2),(.readerLab true 17 2 9 true),(.readerAny true 18),(.readerLab true 18 0 9 false),(.readerLab true 18 0 11 true),(.readerLab true 18 1 9 false),(.readerLab true 18 1 11 true),(.readerLive true 18 2),(.readerLab true 18 2 11 true),(.gateEq false 2 3 0),(.eqLab true 2 3 7 true),(.gateEq false 2 4 0),(.eqLab true 2 4 7 true),(.gateEq false 3 4 0),(.eqLab true 3 4 6 true),(.eqLab true 3 4 9 true),(.eqLab false 3 13 1 true),(.gateEq true 3 13 0),(.gateEq true 3 13 1),(.gateEq true 3 13 2),(.eqLab false 3 17 6 false),(.gateEq true 3 17 0),(.gateEq true 3 17 1),(.gateEq true 3 17 2),(.gateEq false 13 15 0),(.eqLab true 13 15 12 false),(.eqLab false 13 17 6 false),(.gateEq true 13 17 0),(.gateEq true 13 17 1),(.gateEq false 16 17 0),(.gateEq false 16 17 1),(.eqLab true 16 17 9 false),(.gateEq false 16 18 0),(.gateEq false 16 18 1),(.eqLab true 16 18 11 false),(.gateEq false 17 18 0),(.gateEq false 17 18 1),(.eqLab true 17 18 9 true)]

def table298_0 : List Nat := [577,833,0x50302,0x4c1,0x70482,0x80482,0x541,0x641,0x741,0x8682,0x17010003,0x7c1,0x841,0x8c1,0xa41,0x120a02]
def table298_1 : List Nat := [0xac1,0x130a82,0xb41,0xf41,0x178f82,0x1241,0x18f82,0x572a94c3,0x181482,0x191482,0x1b1482,0x201502,0x211502,0x221502,0x251582,0x261582]
def table298_2 : List Nat := [0x271582,0x5d2d9643,0x181602,0x1c1602,0x201682,0x231682,0x251702,0x633097c3,0x191782,0x1b1782,0x1c1782,0x211802,0x221802,0x231802,0x261882,0x281882]
def table298_3 : List Nat := [0x69339943,0x199902,0x219982,0x271a02,0x6f369ac3,0x191a82,0x1b9a82,0x1c1a82,0x211b02,0x229b02,0x231b02,0x261b82,0x279b82,0x281b82,0x1c02,0x1c48231170585]
def table298_4 : List Nat := [0x1c496311f0585,0x1c496411f0585,0x35020083,0x31c82,0xec1,0x1cc8e39170e85,0x1cca2391f0e85,0x1cca2471f0e85,0x1d41,0x1f41,0x3b9f82,0x21c1,0x29f82,0x9147a343,0x3c2302,0x3d2302]
def table298_5 : List Nat := [0x402382,0x412382,0x422382,0x3fa402,0x442402,0x452402,0x974aa4c3,0x3ca482,0x3d2482,0x412502,0x42a502,0x3fa582,0x9d4da643,0x3ca602,0x3d2602,0x40a682]
def table298_6 : List Nat := [0x412682,0x44a702,0x452702,0x12782,0x27d067b3b0d05,0x27d167b3f0d05,0x27d16833f0d05,0x2841,0x28c1,0x2941,0x3aa82,0xb75aacc3,0x542c82,0x572d02,0x55ad82,0xbd5dae43]
def table298_7 : List Nat := [0x542e02,0x582e82,0x55af02,0xc360afc3,0x532f82,0x54af82,0x563002,0x57b002,0x55b082,0x3141,0x31c1,0xc9043183,0xca05b183,0x3341,0x33c1,0xd007b383]
def table298_8 : List Nat := [0xd208b383,0x3541,0xdb6cb5c3,0xdb682,0xe16fb743,0xe30a3703,0xe30c3783,0xdb802,0xe30e3803,0xe973b943,0xdba02,0xef76bac3,0xf10f3a83,0xf1103b03,0xf1113b83,0xf77abcc3]
def table298_9 : List Nat := [0xf9183c83,0xfa19bc83,0xfd163c83,0xf9203d03,0xfa21bd03,0xfd1e3d03,0x1fbd82,0xf9253d83,0xfa26bd83,0xfd243d83,0x10380bfc3,0x10453bf83,0x10654bf83,0x10456c003,0x10858c003,0x55c082]
def table298_10 : List Nat := [0x10f86c2c3,0x1101bc283,0x11022c303,0x1fc382,0x11027c383,0x1178ac4c3,0x119504483,0x119514503,0x119524583,0x46c1,0x11c12c683,0x11e13c683,0x12591c843,0x127164803,0x1271e4883,0x1fc902]
def table298_11 : List Nat := [0x127244903,0x12d95ca43,0x12e3dca03,0x1313a4a03,0x12e41ca83,0x1313e4a83,0x3fcb02,0x131434b03,0x133633103,0xfb784c83,0x135663103,0x107784d03,0x137663183,0x1057c4d83,0x1097e4d83,0xd1644e03]
def table298_12 : List Nat := [0x139853c83,0x139863d03,0x139873d83,0xe265ce83,0x13b903c83,0x13b913d03,0x13b923d83,0x13d6a3383,0x11888cf03,0xe269cf83,0x13f904283,0x13f914303,0x1416e3583,0x1416f3603,0x1268ed003,0x143723583]
def table298_13 : List Nat := [0x143733603,0x1308fd083,0x145723703,0x145733783,0x12f935103,641,897,0x401,0x901,0x981,0xe6471c8b84,0xe6511c8f84,0xe651238f84,0x3241,0x3281,0x3401]
def table298_14 : List Nat := [0x3481,0x71b702,0x71b782,0x71b802,0x78ba82,0x78bb02,0x78bb82,0x7ebc82,0x7ebd02,0x7ebd82,0x8cc482,0x8cc502,0x8cc582,0x4701,0x4781,0x93c802]
def table298_15 : List Nat := [0x93c882,0x93c902,0x98ca02,0x98ca82,0x98cb02,0x4cc1,0x7dbc02,0x4d41,0x83bc02,0x4dc1,0x82be02,0x84bf02,0x4e01,0x853c82,0x863d02,0x873d82]
def table298_16 : List Nat := [0x714e82,0x4f41,0x8c4442,0x714f82,0x935002,0x985082,0x4c41,0x5081,0x49c1,0x5001,0x38c1,0x4e81,0x4f81,0x7c31258004,0x7a012703,0x3d0082]
def table298_17 : List Nat := [0x1fc802,0x1fc882,0xfc1,0xbc1,193,0x2781,0x1e81,0x2401,0x2081,0x1f81,0x4b01,0x4b81,0x5101,0xd661399304,0x3c41,0x3ec1]
def table298_18 : List Nat := [0x41c1,0x4c399b03,0x261cc2,0x4641,0x4441,0xf6824003,0x7b4102,0xdb982,0x6c1,65,0x87c802,0x1c01,0x5c1,0x87c882,0x208b761bf84,0x87bc82]
def table298_19 : List Nat := [0x43c1,0x13c1,0x3d81,0x1581,0x1a01,0x3f41,0x4241,0x398c82,0x1cc1,385,0x2a81,0x2d81,0x2f01,0x3081,0x4081,0x824002]
def table298_20 : List Nat := [0x4101,0x3e01,0x3d01,0x3cc1,0xcc1,0xc01,0x1481,0x1041,0x1541]

def encoded298 (i : Nat) : Nat :=
  if i < 160 then
    if i < 80 then
      if i < 32 then
        if i < 16 then
          table298_0.getD (i%16) 0
        else
          table298_1.getD (i%16) 0
      else
        if i < 48 then
          table298_2.getD (i%16) 0
        else
          if i < 64 then
            table298_3.getD (i%16) 0
          else
            table298_4.getD (i%16) 0
    else
      if i < 112 then
        if i < 96 then
          table298_5.getD (i%16) 0
        else
          table298_6.getD (i%16) 0
      else
        if i < 128 then
          table298_7.getD (i%16) 0
        else
          if i < 144 then
            table298_8.getD (i%16) 0
          else
            table298_9.getD (i%16) 0
  else
    if i < 240 then
      if i < 192 then
        if i < 176 then
          table298_10.getD (i%16) 0
        else
          table298_11.getD (i%16) 0
      else
        if i < 208 then
          table298_12.getD (i%16) 0
        else
          if i < 224 then
            table298_13.getD (i%16) 0
          else
            table298_14.getD (i%16) 0
    else
      if i < 288 then
        if i < 256 then
          table298_15.getD (i%16) 0
        else
          if i < 272 then
            table298_16.getD (i%16) 0
          else
            table298_17.getD (i%16) 0
      else
        if i < 304 then
          table298_18.getD (i%16) 0
        else
          if i < 320 then
            table298_19.getD (i%16) 0
          else
            table298_20.getD (i%16) 0
def book298 (i : Nat) : Clause := let n := encoded298 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses298 : inputsOK 1 298 a298 r298 (baseBook book298 213).toList=true := by decide +kernel

def rows298_0 : List Nat := [0x40401,0xc0801,0xc0a01,0x381e01,0x402201,0x1108a01,0x1108c01,0x1108e01,0x1e8f602,0x6a9e8f802,0x6b1f8fe02,0x6b9f90002,0x190a01,0x1d0c01,0x211001,0x2d1801,0x311a01,0x351c01,0x492401,0x4d2a01,0x553201,0x19d4c01,0x1a14e01,0x1a55001]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk298_0 : checkRows book298 9 213 rows298_0=true := by decide +kernel

def rows298_1 : List Nat := [0x6c2a55402,0x6caa55602,0x495a01,0x4d5c01,0x556001,0x1216601,0x1256a01,0x12d6e01,0x3d1e57002,0x3d57201,0x3e9e57402,0x3dd7601,0x3e9e97802,0x3e57a01,0x3e57c01,0x6fb757e02,0x3f18001,0x3f18201,0x3f18401,0x3798601,0x409f98e02,0x4059001,0x3819201,0x3b59c01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk298_1 : checkRows book298 9 237 rows298_1=true := by decide +kernel

def rows298_2 : List Nat := [0x3b9a201,0xf479bc96203,0x41a0a01,0xf1783bd5803,0x4220801,0xe3713850803,0x42a0001,0x42a0601,0xa1f0588003,0x33130b6562d148a24d2a188c24f2c18c840e,0x198985529934a0602f9721c6327978840d,0x1408f653112ca38642dfc08,0x1408f65b152ca38642dfa08,0xaf88c415803,0x4482801,0x4482c01,0x450c601,0x4521e01,0x6526154a7148b4548407,0x19498622d970ac5d2b9389a602c94629168ac5c8411,0x642612a29168c4548407,0x4656c01,0x2d1651a8c4596205,0x8446da802]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk298_2 : checkRows book298 9 261 rows298_2=true := by decide +kernel

def rows298_3 : List Nat := [0x3a150d04e3b1744db407,0xe672b911603,0x479ec01,0x479f001,0x8eb68583a1cc4c6e06,0x13b6852371b0d2422e1dc4c5a0a,0xec75ba94a03,0x48e0401,0xea6f399c4ec9e4ebedd2723c1a887224c47ce010,0x3b9ace66c3a271369a929b8f09f3510e44989047cda12,0x21104d36820d0f098e41d9809,0x108826933d13274521d07098e41d9a0c,0x4a01201,0x12efa930602e1d5107d308f7f28194c494c4a491f8642e1a14,0x4a47c01,0x8a4a41402,0x1042e970fbe9312647869faa15032d8b2b894b23f248642c3615,0xee6b399b0e89c4dc80da08,0x3a9bce6713b2793a9a9727cf072371a886dc1d3e868901e4345e200f09c2e2c0ea886a280ca81f6917eb9e25299247ce02a,0x3a9bce6713b2793a9a9727cf072371a886db1bbe868931e1045e200f09c2e290d284702b0e281f6947f3a11f2f632b25b2a894ae59248fc2ce032,0x924c14802,0x4c1fe01,0x4c44001,0x4c46601]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk298_3 : checkRows book298 9 285 rows298_3=true := by decide +kernel

def rows298_4 : List Nat := [0xe873cc91e03,0x4d5f601,0x251e8846822130e47e410e86c2e350cc4a5713964cdb813,0x8c7a211a0904c361fc3434180b8e03832180c66f1295c4e592999cd1b619,0x4e08601,0x4e4d401,0x4e8dc01,0x4e8e401,0x4e8f001,0x4e93e01,0x381ccde713b2793b369e4f4ea0a,0x4fe5d3e9dcf53405,0x501f401,0x171f871269499cae272ca0c7c300b,0x995091e02,0x8fd0d2202,0xa0d0d2002,0x5103201,0x2591395d147e04,0x99d182e02]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk298_4 : checkRows book298 9 309 rows298_4=true := by decide +kernel

def lastUnits298 := digits 9 2 0x28f48
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict298 : checkReasons book298 329 27 lastUnits298 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude298 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 298=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z a298
  have hbase : ValidThrough v book298 213 := book_start Z h hc z eq _ _ _ _ initialClauses298
  have h0 : ValidThrough v book298 237 := rows_sound hbase rows298_0 rowsOk298_0
  have h1 : ValidThrough v book298 261 := rows_sound h0 rows298_1 rowsOk298_1
  have h2 : ValidThrough v book298 285 := rows_sound h1 rows298_2 rowsOk298_2
  have h3 : ValidThrough v book298 309 := rows_sound h2 rows298_3 rowsOk298_3
  have h4 : ValidThrough v book298 329 := rows_sound h3 rows298_4 rowsOk298_4
  exact book_end h4 _ _ conflict298
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
