import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a197 : Array Fact := #[(.lab 0 0 0),(.lab 0 0 5),(.avoid 0 314 0),(.res 0 5),(.res 0 8),(.res 0 9),(.res 0 10),(.lab 2 0 2),(.lab 2 0 0),(.avoid 2 8297 0),(.lab 5 0 5),(.common 5 8),(.lab 5 1 5),(.live 5 2),(.lab 5 2 5),(.lab 6 0 0),(.lab 6 0 2),(.lab 6 0 5),(.avoid 6 314 0),(.avoid 6 541 0),(.lab 8 0 8),(.live 8 1),(.lab 8 0 5),(.lab 8 0 9),(.common 8 9),(.lab 8 0 10),(.common 8 10),(.lab 8 0 13),(.lab 8 1 8),(.live 8 2),(.lab 8 1 5),(.lab 8 1 9),(.lab 8 1 10),(.lab 8 1 11),(.lab 8 1 13),(.lab 8 2 8),(.lab 8 2 5),(.lab 8 2 9),(.lab 8 2 10),(.lab 8 2 13),(.avoid 8 1548 0),(.avoid 8 1548 1),(.avoid 8 1548 2),(.avoid 8 8297 0),(.avoid 8 8297 1),(.avoid 8 8297 2),(.see 8 0 9992 0),(.see 8 0 9992 1),(.see 8 0 9992 2),(.see 8 2 8488 0),(.see 8 2 8488 1),(.see 8 2 8488 2),(.see 8 2 9992 0),(.see 8 2 9992 1),(.see 8 2 9992 2),(.see 8 2 16256 0),(.see 8 2 16256 1),(.see 8 2 16256 2),(.see 8 6 7426 0),(.see 8 6 7426 1),(.see 8 6 7426 2),(.see 8 6 16256 0),(.see 8 6 16256 1),(.see 8 6 16256 2),(.diff 0 8 5),(.diff 0 8 9),(.diff 0 8 10),(.lab 9 0 8),(.lab 9 0 10),(.lab 9 0 12),(.live 9 2),(.lab 9 1 8),(.lab 9 1 10),(.lab 9 1 12),(.avoid 9 1290 0),(.avoid 9 1290 1),(.avoid 9 1290 2),(.avoid 9 4370 0),(.avoid 9 4370 1),(.avoid 9 4370 2),(.lab 10 0 10),(.lab 10 0 8),(.lab 10 0 12),(.lab 10 1 10),(.live 10 2),(.lab 10 1 8),(.lab 10 1 12),(.avoid 10 4370 0),(.avoid 10 4370 1),(.avoid 10 4370 2),(.avoid 10 5008 0),(.avoid 10 5008 1),(.avoid 10 5008 2),(.see 10 0 7426 0),(.see 10 0 7426 1),(.see 10 0 7426 2),(.lab 12 0 12),(.lab 12 1 12),(.lab 12 2 12),(.reader false 0 0),(.es false 0 0),(.reader false 1 0),(.es false 1 5),(.reader false 5 0),(.es false 5 0),(.es false 5 2),(.reader false 13 0),(.reader false 13 1),(.reader false 13 2),(.es false 13 5),(.reader false 14 0),(.reader false 14 1),(.reader false 14 2),(.es false 14 5),(.reader false 15 0),(.reader false 15 1),(.reader false 15 2),(.reader false 16 0),(.es false 16 0),(.es false 16 2),(.reader false 17 0),(.es false 17 5),(.reader true 0 0),(.reader true 0 1),(.reader true 0 2),(.es true 0 8),(.reader true 1 0),(.reader true 1 1),(.reader true 1 2),(.es true 1 8),(.reader true 5 0),(.reader true 5 1),(.reader true 5 2),(.reader true 13 0),(.reader true 13 1),(.reader true 13 2),(.es true 13 10),(.es true 13 12),(.reader true 14 0),(.reader true 14 1),(.reader true 14 2),(.es true 14 10),(.es true 14 12),(.reader true 15 0),(.reader true 15 1),(.reader true 15 2),(.es true 15 12),(.reader true 16 0),(.reader true 16 1),(.reader true 16 2),(.es true 16 8),(.reader true 17 0),(.reader true 17 1),(.reader true 17 2),(.es true 17 8),(.gate 0 1),(.gate 0 5),(.gate 0 16),(.gate 1 14),(.gate 5 16),(.gate 13 14),(.gate 13 15),(.gate 13 17),(.gate 14 15),(.gate 16 17)]
def r197 : List Scheme := [(.self 0 0),(.exposure 0 314),(.avoidNot 0 5 314 0),(.self 2 0),(.exposure 2 8297),(.avoidNot 2 0 8297 0),(.self 5 0),(.self 5 1),(.self 5 2),(.someRes 5),(.resCommon 5 8 0),(.exposure 6 314),(.avoidNot 6 5 314 0),(.exposure 6 541),(.avoidNot 6 0 541 0),(.avoidNot 6 2 541 0),(.self 8 0),(.self 8 1),(.earlier 8 1),(.self 8 2),(.someRes 8),(.exposure 8 1548),(.avoidNot 8 9 1548 0),(.avoidNot 8 10 1548 0),(.avoidNot 8 9 1548 1),(.avoidNot 8 10 1548 1),(.avoidNot 8 9 1548 2),(.avoidNot 8 10 1548 2),(.exposure 8 8297),(.avoidNot 8 5 8297 0),(.avoidNot 8 13 8297 0),(.avoidNot 8 5 8297 1),(.avoidNot 8 13 8297 1),(.avoidNot 8 5 8297 2),(.avoidNot 8 13 8297 2),(.exactAt 8 0 9992),(.seeLab 8 0 9 9992 0),(.seeLab 8 0 10 9992 0),(.seeLab 8 0 9 9992 1),(.seeLab 8 0 10 9992 1),(.seeLab 8 0 9 9992 2),(.seeLab 8 0 10 9992 2),(.exactAt 8 2 8488),(.seeLab 8 2 5 8488 0),(.seeLab 8 2 13 8488 0),(.seeLab 8 2 5 8488 1),(.seeLab 8 2 13 8488 1),(.seeLab 8 2 5 8488 2),(.seeLab 8 2 13 8488 2),(.exactAt 8 2 9992),(.seeLab 8 2 10 9992 0),(.seeLab 8 2 10 9992 1),(.seeLab 8 2 13 9992 2),(.exactAt 8 2 16256),(.seeLab 8 2 10 16256 0),(.seeLab 8 2 11 16256 1),(.seeLab 8 2 10 16256 2),(.exactAt 8 6 7426),(.seeLab 8 6 10 7426 0),(.seeLab 8 6 11 7426 1),(.seeLab 8 6 10 7426 2),(.exactAt 8 6 16256),(.seeLab 8 6 9 16256 0),(.seeLab 8 6 10 16256 0),(.seeLab 8 6 10 16256 1),(.seeLab 8 6 10 16256 2),(.seeLab 8 6 13 16256 2),(.diffC 0 8 5),(.residual 8 5 0 1),(.residual 8 5 0 2),(.residual 8 5 1 2),(.diffC 0 8 9),(.adjacentCommon 8 9 6),(.residual 8 9 0 1),(.residual 8 9 0 2),(.residual 8 9 1 2),(.diffC 0 8 10),(.adjacentCommon 8 10 0),(.residual 8 10 0 1),(.residual 8 10 0 2),(.residual 8 10 1 2),(.someRes 9),(.exposure 9 1290),(.avoidNot 9 8 1290 0),(.avoidNot 9 10 1290 0),(.avoidNot 9 8 1290 1),(.avoidNot 9 10 1290 1),(.avoidLive 9 1290 2),(.exposure 9 4370),(.avoidNot 9 8 4370 0),(.avoidNot 9 12 4370 0),(.avoidNot 9 8 4370 1),(.avoidNot 9 12 4370 1),(.avoidLive 9 4370 2),(.self 10 0),(.self 10 1),(.someRes 10),(.exposure 10 4370),(.avoidNot 10 8 4370 0),(.avoidNot 10 12 4370 1),(.avoidLive 10 4370 2),(.exposure 10 5008),(.avoidNot 10 12 5008 0),(.avoidNot 10 8 5008 1),(.avoidLive 10 5008 2),(.exactAt 10 0 7426),(.seeLab 10 0 8 7426 0),(.seeLab 10 0 12 7426 1),(.seeLive 10 0 7426 2),(.self 12 0),(.self 12 1),(.self 12 2),(.readerAny false 0),(.readerLab false 0 0 0 true),(.readerAny false 1),(.readerLab false 1 0 5 false),(.readerAny false 5),(.readerLab false 5 0 0 false),(.readerLab false 5 0 2 true),(.readerAny false 13),(.readerLab false 13 0 5 true),(.readerLab false 13 1 5 true),(.readerLive false 13 2),(.readerLab false 13 2 5 true),(.readerAny false 14),(.readerLab false 14 0 5 true),(.readerLab false 14 1 5 true),(.readerLive false 14 2),(.readerLab false 14 2 5 true),(.readerAny false 15),(.readerLive false 15 2),(.readerAny false 16),(.readerLab false 16 0 0 false),(.readerLab false 16 0 2 false),(.readerAny false 17),(.readerLab false 17 0 5 false),(.readerAny true 0),(.readerLab true 0 0 8 true),(.readerLab true 0 1 8 true),(.readerLive true 0 2),(.readerLab true 0 2 8 true),(.readerAny true 1),(.readerLab true 1 1 8 false),(.readerLive true 1 2),(.readerAny true 5),(.readerLive true 5 2),(.readerAny true 13),(.readerLab true 13 0 10 false),(.readerLab true 13 0 12 false),(.readerLab true 13 1 10 false),(.readerLab true 13 1 12 false),(.readerLive true 13 2),(.readerAny true 14),(.readerLab true 14 0 10 true),(.readerLab true 14 0 12 false),(.readerLab true 14 1 10 true),(.readerLab true 14 1 12 false),(.readerLive true 14 2),(.readerAny true 15),(.readerLab true 15 0 12 true),(.readerLab true 15 1 12 true),(.readerLab true 15 2 12 true),(.readerAny true 16),(.readerLab true 16 0 8 true),(.readerLab true 16 1 8 true),(.readerLive true 16 2),(.readerLab true 16 2 8 true),(.readerAny true 17),(.readerLab true 17 0 8 false),(.readerLab true 17 1 8 false),(.readerLive true 17 2),(.gateEq false 0 1 0),(.eqLab true 0 1 8 true),(.eqLab false 0 5 0 true),(.gateEq true 0 5 0),(.gateEq true 0 5 1),(.eqLab false 0 16 0 true),(.gateEq true 0 16 0),(.gateEq true 0 16 1),(.eqLab false 1 14 5 false),(.gateEq true 1 14 0),(.eqLab false 5 16 2 true),(.gateEq true 5 16 0),(.gateEq true 5 16 1),(.gateEq false 13 14 0),(.gateEq false 13 14 1),(.eqLab true 13 14 10 false),(.gateEq false 13 15 0),(.gateEq false 13 15 1),(.eqLab true 13 15 12 false),(.eqLab false 13 17 5 true),(.gateEq true 13 17 0),(.gateEq true 13 17 1),(.gateEq false 14 15 0),(.gateEq false 14 15 1),(.eqLab true 14 15 12 false),(.gateEq false 16 17 0),(.eqLab true 16 17 8 true)]

def table197_0 : List Nat := [65,321,0x10102,961,0x4c1,0x80482,0x541,0x641,0x741,0x38682,0x17040183,0x941,0x110902,0x9c1,0xf0982,0x100982]
def table197_1 : List Nat := [0xa41,0xe41,0x158e82,0x11c1,0x48e82,0x55299443,0x171402,0x191402,0x1f1482,0x201482,0x251502,0x261502,0x5b2c95c3,0x161582,0x1b1582,0x1e1602]
def table197_2 : List Nat := [0x221602,0x241682,0x271682,0x612f9743,0x171702,0x199702,0x1f1782,0x209782,0x251802,0x269802,0x673298c3,0x161882,0x1b9882,0x1e1902,0x229902,0x241982]
def table197_3 : List Nat := [0x279982,0x6d359a43,0x191a02,0x201a82,0x279b02,0x73389bc3,0x191b82,0x211c02,0x261c82,0x793b9d43,0x191d02,0x219d82,0x261e02,0x7f3e9ec3,0x179e82,0x191e82]
def table197_4 : List Nat := [0x201f02,0x261f82,0x271f82,0x32002,0x2047a2d150585,0x204922d1d0585,0x204923d1d0585,0x52082,0xc41,0x20c7e2f150c05,0x20c962f1d0c05,0x20c963f1d0c05,0x62102,0xd41,0x2148233150d05,0x2149a331d0d05]
def table197_5 : List Nat := [0x2149a411d0d05,0x5a302,0x994ba543,0x432502,0x442502,0x472582,0x482582,0x46a602,0x9f4ea6c3,0x432682,0x452682,0x472702,0x492702,0x46a782,0x2841,0x29c1]
def table197_6 : List Nat := [0x6aa02,0xb358abc3,0x512b82,0x562c02,0x54ac82,0xb95bad43,0x522d02,0x552d82,0x54ae02,0xbf5eaec3,0x51ae82,0x562f02,0x54af82,0x3041,0x30c1,0x3141]
def table197_7 : List Nat := [0x31c1,0xc9003183,0x32c1,0xcc01b283,0x33c1,0xd008b383,0xd3073383,0xd96bb543,0xdb0a3503,0xdb0c3583,0xdb602,0xdb0e3603,0xe16fb743,0xe30a3703,0xe30c3783,0xdb802]
def table197_8 : List Nat := [0xe30e3803,0xe973b943,0xdba02,0x3ac1,0xec0fba83,0xee10ba83,0x3c41,0xf211bc03,0xf97bbd43,0xfb143d03,0xfb1c3d83,0x1dbe02,0xfb233e03,0x1017fbf43,0x10255bf83,0x54c002]
def table197_9 : List Nat := [0x10983c143,0x1dc202,0x10f86c2c3,0x11044c283,0x11245c283,0x11048c303,0x11249c303,0x46c382,0x1198bc543,0x11b504503,0x11c52c503,0x11b534583,0x11c56c583,0x54c602,0x12390c7c3,0x125604783]
def table197_10 : List Nat := [0x125614803,0x125624883,0x12b94c9c3,0x12d144983,0x12d1c4a03,0x1dca82,0x12d234a83,0x13398cbc3,0x13443cb83,0x13447cc03,0x46cc82,0x137653183,0x1037d4d83,0xd1644e03,0x139823d03,0x139833d83]
def table197_11 : List Nat := [0xed644e83,0x13b933d03,0x13b943d83,0xe266cf03,0x13d8a3f03,0xef694f83,0x13f934103,0x13f944183,0x1416e3503,0x1416f3583,0x11a88d003,0x143723503,0x143733583,0x12489d083,0xf36d5103,0x145974283]
def table197_12 : List Nat := [0x145984303,0x147723703,0x147733783,0x1248ed183,0x149783a83,0x135965203,129,0x401,0x881,0x781,0x801,0x1063f178a84,0x1064b178e84,0x1064b1f8e84,0x10a41198a84,0x10a4d198e84]
def table197_13 : List Nat := [0x10a4d208e84,0x3241,0x3301,0x3401,0x34c1,0x6db502,0x6db582,0x6db602,0x71b702,0x71b782,0x71b802,0x3b01,0x3b81,0x3c81,0x7dbd02,0x7dbd82]
def table197_14 : List Nat := [0x7dbe02,0x8dc502,0x8dc582,0x92c782,0x92c802,0x92c882,0x96c982,0x96ca02,0x96ca82,0x4dc1,0x81be82,0x4e01,0x823d02,0x833d82,0x4e81,0x933d02]
def table197_15 : List Nat := [0x943d82,0x714f02,0x4f81,0x934102,0x944182,0x6d5102,0x5241,0x9acb02,0x36c1,0x5101,0x38c1,0x4f01,0x3a429f83,0x3a428cc3,0x1d2142,0x260c82]
def table197_16 : List Nat := [0x1063a2a92c4,0x831d1303,0x831d1403,0x831d1483,0x418e82,0x1dca02,0xec1,0xac1,577,0x2141,0x20c1,769,641,0x2a01,0x2301,0x2c81]
def table197_17 : List Nat := [0x2e01,0x2f81,0x4001,0x4601,0x2601,0x2781,0x4381,0x4c81,0x46c1,0x1109a4c03,0x884d02,0x4b41,0x4d41,0x4401,0x5001,0x4941]
def table197_18 : List Nat := [0x894b82,0x4481,0x5081,0x11c814503,0x2b01,0x3ec1,0x40c1,0x4701,0x5181,0x2c0182,0xdb982,0x6c1,449,0x2001,0x5c1,0x1601]
def table197_19 : List Nat := [0x1681,0x15c1,0xb01,0xd81,0xf41,0x1241,0x1881,0x1901,0x1981]

def encoded197 (i : Nat) : Nat :=
  if i < 160 then
    if i < 80 then
      if i < 32 then
        if i < 16 then
          table197_0.getD (i%16) 0
        else
          table197_1.getD (i%16) 0
      else
        if i < 48 then
          table197_2.getD (i%16) 0
        else
          if i < 64 then
            table197_3.getD (i%16) 0
          else
            table197_4.getD (i%16) 0
    else
      if i < 112 then
        if i < 96 then
          table197_5.getD (i%16) 0
        else
          table197_6.getD (i%16) 0
      else
        if i < 128 then
          table197_7.getD (i%16) 0
        else
          if i < 144 then
            table197_8.getD (i%16) 0
          else
            table197_9.getD (i%16) 0
  else
    if i < 240 then
      if i < 192 then
        if i < 176 then
          table197_10.getD (i%16) 0
        else
          table197_11.getD (i%16) 0
      else
        if i < 208 then
          table197_12.getD (i%16) 0
        else
          if i < 224 then
            table197_13.getD (i%16) 0
          else
            table197_14.getD (i%16) 0
    else
      if i < 272 then
        if i < 256 then
          table197_15.getD (i%16) 0
        else
          table197_16.getD (i%16) 0
      else
        if i < 288 then
          table197_17.getD (i%16) 0
        else
          if i < 304 then
            table197_18.getD (i%16) 0
          else
            table197_19.getD (i%16) 0
def book197 (i : Nat) : Clause := let n := encoded197 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses197 : inputsOK 1 197 a197 r197 (baseBook book197 198).toList=true := by decide +kernel

def rows197_0 : List Nat := [0x40401,0x100a01,0x2c1801,0x341c01,0x341e01,0x1209201,0x1209401,0x1209601,0x1349c01,0x1349e01,0x134a001,0x1c0e202,0x631c8e602,0x639d0ea02,0x19d0ec02,0x18f001,0x1cf201,0x20f601,0x18fa01,0x1cfc01,0x210001,0x64a0d0802,0x6520d0a02,0x642190e02]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk197_0 : checkRows book197 9 198 rows197_0=true := by decide +kernel

def rows197_1 : List Nat := [0x411201,0x451401,0x4d1801,0x1793201,0x17d3601,0x1b53e01,0x1b94001,0x1bd4201,0x414601,0x454801,0x4d4c01,0x391c15602,0x3a55801,0x69b455a02,0x3ad5c01,0x3ad5e01,0x6db456002,0x3b96201,0x3b96401,0x3496601,0x6e3516a02,0x3c96c01,0x3c96e01,0x3757c01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk197_1 : checkRows book197 9 222 rows197_1=true := by decide +kernel

def rows197_2 : List Nat := [0x4320d8802,0x3d98a01,0xd76b354ee03,0x3e1ea01,0xda6cb60f803,0x3e9e201,0x32198d19ed0211046207,0xb0f42a1b200659ece093f07c0a,0xdc72351e0e1a0401e8fc74367ebf0760d,0x371c8d474361c0f07607,0x2c18663342a04,0x2c196589c4c23144004aff0d8482a0c,0x4c256585c2c1214c044608,0x482765864301214c044608,0x1209998cd0d056070214c04460a,0x48221e8f045a45d806,0x24110f377a8a0aa548a2dda09,0x4182401,0x4182801,0x419fc01,0x41a0801,0x4249801,0x4288e01,0x42cc001]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk197_2 : checkRows book197 9 246 rows197_2=true := by decide +kernel

def rows197_3 : List Nat := [0x430a201,0x434c801,0x434d001,0x434d801,0x4351e01,0x4353a01,0x438ae01,0x438ba01,0x4392e01,0x4395401,0xe270c4d3003,0x24ca4922ab0153148b3e4a809,0x12a524914d7ea853c662ef98b450ac0c,0xe873b994403,0x46dee01,0x4723401,0x8c4757402,0xe57238d3c03,0x4b16124595faa22b167cc70b80a,0x250b0922db0152a7904562cf98e45cb40d,0x8fc857a02,0x238ca8d332d13510893ecce09,0x6234984d66388c3cd407,0xe06fb791003]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk197_3 : checkRows book197 9 270 rows197_3=true := by decide +kernel

def rows197_4 : List Nat := [0x495d401,0x48d3913934913005,0x8fc9d8602,0x5e2b2311014430f8b8410683c20540c,0x1f0eec25e1e8ff1e944897009,0xf87760aed032a411fcf51e94489720c,0x4ac1201,0x4b08601,0x844b01402,0x4b25201,0x158b46045230884306974b4540a,0x97cc03802,0x4c43a01,0x4c43c01,0x25d0796cc88804,0x25b2e834c88a04,0x4cc5801,0x4d05a01,0x4d45e01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk197_4 : checkRows book197 9 294 rows197_4=true := by decide +kernel

def lastUnits197 := digits 9 3 0x4de7136
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict197 : checkReasons book197 313 42 lastUnits197 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude197 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 197=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z a197
  have hbase : ValidThrough v book197 198 := book_start Z h hc z eq _ _ _ _ initialClauses197
  have h0 : ValidThrough v book197 222 := rows_sound hbase rows197_0 rowsOk197_0
  have h1 : ValidThrough v book197 246 := rows_sound h0 rows197_1 rowsOk197_1
  have h2 : ValidThrough v book197 270 := rows_sound h1 rows197_2 rowsOk197_2
  have h3 : ValidThrough v book197 294 := rows_sound h2 rows197_3 rowsOk197_3
  have h4 : ValidThrough v book197 313 := rows_sound h3 rows197_4 rowsOk197_4
  exact book_end h4 _ _ conflict197
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
