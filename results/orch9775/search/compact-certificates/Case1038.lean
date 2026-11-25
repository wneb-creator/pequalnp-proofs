import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a1038 : Array Fact := #[(.res 0 6),(.res 0 8),(.res 0 9),(.res 0 13),(.lab 1 0 1),(.lab 1 0 4),(.avoid 1 245 0),(.lab 2 0 1),(.lab 2 0 4),(.lab 2 0 6),(.avoid 2 314 0),(.avoid 2 8297 0),(.lab 4 0 4),(.lab 4 1 4),(.lab 4 2 4),(.lab 6 0 6),(.common 6 13),(.lab 6 1 6),(.live 6 2),(.lab 6 2 6),(.lab 8 0 8),(.lab 8 0 9),(.lab 8 0 11),(.lab 8 0 13),(.common 8 13),(.lab 8 1 8),(.live 8 2),(.lab 8 1 9),(.lab 8 1 11),(.lab 8 1 13),(.avoid 8 8297 0),(.avoid 8 8297 1),(.avoid 8 8297 2),(.avoid 8 8713 0),(.avoid 8 8713 1),(.avoid 8 8713 2),(.avoid 8 10401 0),(.avoid 8 10401 1),(.avoid 8 10401 2),(.see 8 2 9992 0),(.see 8 2 9992 1),(.see 8 2 9992 2),(.lab 9 0 9),(.lab 9 0 7),(.lab 9 0 11),(.common 9 13),(.lab 9 1 9),(.live 9 2),(.lab 9 1 7),(.lab 9 1 11),(.lab 9 2 9),(.avoid 9 2213 0),(.avoid 9 2213 1),(.avoid 9 2213 2),(.see 9 1 6789 0),(.see 9 1 6789 1),(.see 9 1 6789 2),(.lab 11 0 11),(.lab 11 1 11),(.lab 11 2 11),(.lab 13 0 13),(.live 13 1),(.lab 13 0 6),(.lab 13 0 7),(.lab 13 0 8),(.lab 13 0 9),(.lab 13 1 13),(.live 13 2),(.lab 13 1 6),(.lab 13 1 7),(.lab 13 1 8),(.lab 13 1 9),(.lab 13 2 13),(.lab 13 2 6),(.lab 13 2 7),(.lab 13 2 8),(.lab 13 2 9),(.avoid 13 245 0),(.avoid 13 245 1),(.avoid 13 245 2),(.avoid 13 432 0),(.avoid 13 432 1),(.avoid 13 432 2),(.avoid 13 792 0),(.avoid 13 792 1),(.avoid 13 792 2),(.see 13 1 8417 0),(.see 13 1 8417 1),(.see 13 1 8417 2),(.see 13 1 9992 0),(.see 13 1 9992 1),(.see 13 1 9992 2),(.see 13 1 13504 0),(.see 13 1 13504 1),(.see 13 1 13504 2),(.see 13 2 10656 0),(.see 13 2 10656 1),(.see 13 2 10656 2),(.diff 0 13 6),(.diff 0 13 8),(.diff 0 13 9),(.reader false 4 0),(.es false 4 1),(.es false 4 4),(.reader false 5 0),(.es false 5 6),(.reader false 6 0),(.es false 6 1),(.es false 6 4),(.reader false 12 0),(.reader false 12 1),(.reader false 12 2),(.es false 12 4),(.reader false 16 0),(.reader false 16 1),(.reader false 16 2),(.es false 16 6),(.reader false 17 0),(.reader false 17 1),(.reader false 17 2),(.reader false 18 0),(.reader false 18 1),(.reader false 18 2),(.reader true 4 0),(.reader true 4 1),(.reader true 4 2),(.reader true 5 0),(.reader true 5 1),(.reader true 5 2),(.es true 5 8),(.es true 5 9),(.es true 5 13),(.reader true 6 0),(.reader true 6 1),(.reader true 6 2),(.es true 6 8),(.es true 6 9),(.es true 6 13),(.reader true 12 0),(.reader true 12 1),(.reader true 12 2),(.reader true 16 0),(.reader true 16 1),(.reader true 16 2),(.es true 16 9),(.es true 16 11),(.reader true 17 0),(.reader true 17 1),(.reader true 17 2),(.es true 17 9),(.es true 17 11),(.reader true 18 0),(.reader true 18 1),(.reader true 18 2),(.es true 18 11),(.gate 4 6),(.gate 4 12),(.gate 5 6),(.gate 5 16),(.gate 6 12),(.gate 16 17),(.gate 16 18),(.gate 17 18)]
def r1038 : List Scheme := [(.self 1 0),(.exposure 1 245),(.avoidNot 1 4 245 0),(.exposure 2 314),(.avoidNot 2 1 314 0),(.avoidNot 2 4 314 0),(.exposure 2 8297),(.avoidNot 2 6 8297 0),(.self 4 0),(.self 4 1),(.self 4 2),(.self 6 0),(.self 6 1),(.self 6 2),(.someRes 6),(.resCommon 6 13 0),(.self 8 0),(.self 8 1),(.someRes 8),(.exposure 8 8297),(.avoidNot 8 13 8297 0),(.avoidNot 8 13 8297 1),(.avoidLive 8 8297 2),(.exposure 8 8713),(.avoidNot 8 9 8713 0),(.avoidNot 8 13 8713 0),(.avoidNot 8 9 8713 1),(.avoidNot 8 13 8713 1),(.avoidLive 8 8713 2),(.exposure 8 10401),(.avoidNot 8 11 10401 0),(.avoidNot 8 13 10401 0),(.avoidNot 8 11 10401 1),(.avoidNot 8 13 10401 1),(.avoidLive 8 10401 2),(.exactAt 8 2 9992),(.seeLab 8 2 9 9992 0),(.seeLab 8 2 13 9992 0),(.seeLab 8 2 9 9992 1),(.seeLab 8 2 13 9992 1),(.seeLive 8 2 9992 2),(.adjacentCommon 8 13 2),(.self 9 0),(.self 9 1),(.self 9 2),(.someRes 9),(.exposure 9 2213),(.avoidNot 9 7 2213 0),(.avoidNot 9 11 2213 0),(.avoidNot 9 7 2213 1),(.avoidNot 9 11 2213 1),(.avoidLive 9 2213 2),(.exactAt 9 1 6789),(.seeLab 9 1 7 6789 0),(.seeLab 9 1 11 6789 0),(.seeLab 9 1 7 6789 1),(.seeLab 9 1 11 6789 1),(.seeLive 9 1 6789 2),(.adjacentCommon 9 13 1),(.self 11 0),(.self 11 1),(.self 11 2),(.self 13 0),(.self 13 1),(.earlier 13 1),(.self 13 2),(.someRes 13),(.exposure 13 245),(.avoidNot 13 6 245 0),(.avoidNot 13 7 245 0),(.avoidNot 13 6 245 1),(.avoidNot 13 7 245 1),(.avoidNot 13 6 245 2),(.avoidNot 13 7 245 2),(.exposure 13 432),(.avoidNot 13 7 432 0),(.avoidNot 13 8 432 1),(.avoidNot 13 7 432 2),(.exposure 13 792),(.avoidNot 13 8 792 0),(.avoidNot 13 9 792 0),(.avoidNot 13 8 792 1),(.avoidNot 13 9 792 1),(.avoidNot 13 8 792 2),(.avoidNot 13 9 792 2),(.exactAt 13 1 8417),(.seeLab 13 1 6 8417 0),(.seeLab 13 1 7 8417 0),(.seeLab 13 1 6 8417 1),(.seeLab 13 1 6 8417 2),(.seeLab 13 1 7 8417 2),(.exactAt 13 1 9992),(.seeLab 13 1 8 9992 0),(.seeLab 13 1 9 9992 0),(.seeLab 13 1 8 9992 1),(.seeLab 13 1 9 9992 1),(.seeLab 13 1 8 9992 2),(.seeLab 13 1 9 9992 2),(.exactAt 13 1 13504),(.seeLab 13 1 6 13504 0),(.seeLab 13 1 7 13504 1),(.seeLab 13 1 6 13504 2),(.seeLab 13 1 7 13504 2),(.exactAt 13 2 10656),(.seeLab 13 2 7 10656 0),(.seeLab 13 2 8 10656 1),(.seeLab 13 2 7 10656 2),(.diffC 0 13 6),(.residual 13 6 0 1),(.residual 13 6 0 2),(.residual 13 6 1 2),(.diffC 0 13 8),(.residual 13 8 0 1),(.residual 13 8 0 2),(.residual 13 8 1 2),(.diffC 0 13 9),(.residual 13 9 0 1),(.residual 13 9 0 2),(.residual 13 9 1 2),(.readerAny false 4),(.readerLab false 4 0 1 true),(.readerLab false 4 0 4 false),(.readerAny false 5),(.readerLab false 5 0 6 false),(.readerAny false 6),(.readerLab false 6 0 1 false),(.readerLab false 6 0 4 false),(.readerAny false 12),(.readerLab false 12 0 4 true),(.readerLab false 12 1 4 true),(.readerLab false 12 2 4 true),(.readerAny false 16),(.readerLab false 16 0 6 true),(.readerLab false 16 1 6 true),(.readerLive false 16 2),(.readerLab false 16 2 6 true),(.readerAny false 17),(.readerLive false 17 2),(.readerAny false 18),(.readerLive false 18 2),(.readerAny true 4),(.readerLive true 4 2),(.readerAny true 5),(.readerLab true 5 0 8 true),(.readerLab true 5 0 9 false),(.readerLab true 5 0 13 false),(.readerLab true 5 1 8 true),(.readerLab true 5 1 9 false),(.readerLab true 5 1 13 false),(.readerLive true 5 2),(.readerAny true 6),(.readerLab true 6 0 8 false),(.readerLab true 6 0 9 true),(.readerLab true 6 0 13 true),(.readerLab true 6 1 8 false),(.readerLab true 6 1 9 true),(.readerLab true 6 1 13 true),(.readerLive true 6 2),(.readerLab true 6 2 8 false),(.readerLab true 6 2 9 true),(.readerLab true 6 2 13 true),(.readerAny true 12),(.readerLive true 12 2),(.readerAny true 16),(.readerLab true 16 0 9 false),(.readerLab true 16 0 11 false),(.readerLab true 16 1 9 false),(.readerLab true 16 1 11 false),(.readerLive true 16 2),(.readerAny true 17),(.readerLab true 17 0 9 true),(.readerLab true 17 0 11 false),(.readerLab true 17 1 9 true),(.readerLab true 17 1 11 false),(.readerLive true 17 2),(.readerLab true 17 2 9 true),(.readerAny true 18),(.readerLab true 18 0 11 true),(.readerLab true 18 1 11 true),(.readerLab true 18 2 11 true),(.eqLab false 4 6 1 true),(.gateEq true 4 6 0),(.gateEq true 4 6 1),(.eqLab false 4 12 4 false),(.gateEq true 4 12 0),(.gateEq true 4 12 1),(.gateEq false 5 6 0),(.eqLab true 5 6 8 true),(.eqLab true 5 6 9 false),(.eqLab true 5 6 13 false),(.eqLab false 5 16 6 false),(.gateEq true 5 16 0),(.gateEq true 5 16 1),(.eqLab false 6 12 4 false),(.gateEq true 6 12 0),(.gateEq true 6 12 1),(.gateEq false 16 17 0),(.gateEq false 16 17 1),(.eqLab true 16 17 9 false),(.gateEq false 16 18 0),(.gateEq false 16 18 1),(.eqLab true 16 18 11 false),(.gateEq false 17 18 0),(.gateEq false 17 18 1),(.eqLab true 17 18 11 false)]

def table1038_0 : List Nat := [577,833,0x50302,0x541,0x70502,0x80502,0x5c1,0x90582,0x641,0x6c1,0x741,0x7c1,0x8c1,0x9c1,0x8902,0x21030003]
def table1038_1 : List Nat := [0xa41,0xcc1,0x18d02,0x411f8f43,0x170f02,0x1d0f82,0x1a9002,0x472290c3,0x151082,0x171082,0x1b1102,0x1d1102,0x1a9182,0x4d259243,0x161202,0x171202]
def table1038_2 : List Nat := [0x1c1282,0x1d1282,0x1a9302,0x532893c3,0x151382,0x179382,0x1b1402,0x1d9402,0x1a9482,0xc41,0x1541,0x1741,0x1941,0x29782,0x6b3499c3,0x2b1982]
def table1038_3 : List Nat := [0x2c1982,0x301a02,0x311a02,0x2f9a82,0x71379b43,0x2b9b02,0x2c1b02,0x309b82,0x311b82,0x2f9c02,0x16c1,0x1cc1,0x1d41,0x1dc1,0x1e41,0x2141]
def table1038_4 : List Nat := [0x3da182,0x2441,0x3a182,0x9f4ea6c3,0x3e2682,0x3f2682,0x442702,0x452702,0x492782,0x4a2782,0xa551a843,0x3f2802,0x462882,0x4a2902,0xab54a9c3,0x402982]
def table1038_5 : List Nat := [0x412982,0x462a02,0x472a02,0x4b2a82,0x4c2a82,0xb157ab43,0x3e2b02,0x3fab02,0x442b82,0x492c02,0x4aac02,0xb75aacc3,0x402c82,0x41ac82,0x462d02,0x47ad02]
def table1038_6 : List Nat := [0x4b2d82,0x4cad82,0xbd5dae43,0x3e2e02,0x45ae82,0x492f02,0x4aaf02,0xc360afc3,0x3f2f82,0x46b002,0x4a3082,0x3102,0x315127d3d0805,0x315267d430805,0x3152689430805,0x13182]
def table1038_7 : List Nat := [0x31d1a813d0c05,0x31d2e81430c05,0x31d2e8d430c05,0x23202,0x3251e833d1685,0x3253283431685,0x325328f431685,0x32c1,0xcd043283,0xce05b283,0x3441,0xd209b403,0x3541,0xd607b503,0xd808b503,0xdf6eb6c3]
def table1038_8 : List Nat := [0xe10c3683,0xe10d3703,0xe10e3783,0xe772b8c3,0xe90f3883,0xe9113903,0x12b982,0xe9133983,0xef76bac3,0x12bb82,0xf579bc43,0x12bd02,0xfb7cbdc3,0x43be82,0x1017fbf43,0x103143f03]
def table1038_9 : List Nat := [0x10415bf03,0x10617bf03,0x103193f83,0x1041bbf83,0x1061dbf83,0x1ac002,0x10d85c243,0x10e40c203,0x111414203,0x1133c4203,0x10e46c283,0x111474283,0x113424283,0x43c302,0x10e4bc303,0x1114c4303]
def table1038_10 : List Nat := [0x113484303,0x1198bc543,0x43c602,0x11f8ec6c3,0x12015c683,0x12216c683,0x1201bc703,0x1221cc703,0x1ac782,0x12993c943,0x12b2a4903,0x12c2cc903,0x12b2e4983,0x12c31c983,0x2fca02,0x12b324a03]
def table1038_11 : List Nat := [0x13398cbc3,0x135394b83,0x1353a4c03,0x1353b4c83,0xd7664d83,0x137843d83,0x137853e03,0xe067ce03,0x1398a3d83,0x1398b3e03,0x13b6a3403,0x10f814e83,0x11082ce83,0x11283ce83,0xe869cf03,0x13d8d3f03]
def table1038_12 : List Nat := [0x13d8e3f83,0xe06ccf83,0x13f8a4203,0x13f8b4283,0x141753883,0x141763903,0x12a90d003,0x143783883,0x143793903,0x13491d083,0x145783a83,0x145793b03,0x13496d103,641,897,0x401]
def table1038_13 : List Nat := [0x481,0x18e8d409e84,0x18e9740a184,0x18e9746a184,0x1928f419e84,0x1929941a184,0x1929947a184,0x3341,0x3381,0x3481,0x3581,0x3601,0x70b682,0x70b702,0x70b782,0x74b882]
def table1038_14 : List Nat := [0x74b902,0x74b982,0x81bf02,0x81bf82,0x89c202,0x89c282,0x89c302,0x95c902,0x95c982,0x95ca02,0x9acb82,0x9acc02,0x9acc82,0x4d81,0x843d82,0x853e02]
def table1038_15 : List Nat := [0x704e02,0x4ec1,0x87c082,0x884142,0x8941c2,0x744f02,0x704f82,0x3841,0x4e01,0x4f81,0x3a41,0x4f01,0x4b2302,0xc73d2583,0xc74325c3,0x63a182]
def table1038_16 : List Nat := [0x43c582,0x21c1,0x1ec1,449,0x31c1,129,0xd01,0x1001,0x1181,0x1301,0x1481,0x4001,0x4781,0x40c1,0x43c1,0x120834703]
def table1038_17 : List Nat := [0x904182,0x44c1,0x41c1,0x4801,0x4ac1,0x5001,0x4d41,0x914682,0x914702,0x4881,0x5081,0x2f9602,0x9617c2,0xc988c303,0xc988aa03,0xc954a3c3]
def table1038_18 : List Nat := [0x64c442,0x823f02,0x4101,0x4401,0x3241,257,0x1781,0x4b01,0x5101,0x5ea243,0x2542,0x314409f56a205,0x608002,0x12bc82,0x941,65]
def table1038_19 : List Nat := [0x3101,0x841,0x2541,0x3041,0x2781,0x2901,0x2341,0x2881,0x2841,0x1f81,0x2b01,0x2201,0x24c1,0x2f41]

def encoded1038 (i : Nat) : Nat :=
  if i < 160 then
    if i < 80 then
      if i < 32 then
        if i < 16 then
          table1038_0.getD (i%16) 0
        else
          table1038_1.getD (i%16) 0
      else
        if i < 48 then
          table1038_2.getD (i%16) 0
        else
          if i < 64 then
            table1038_3.getD (i%16) 0
          else
            table1038_4.getD (i%16) 0
    else
      if i < 112 then
        if i < 96 then
          table1038_5.getD (i%16) 0
        else
          table1038_6.getD (i%16) 0
      else
        if i < 128 then
          table1038_7.getD (i%16) 0
        else
          if i < 144 then
            table1038_8.getD (i%16) 0
          else
            table1038_9.getD (i%16) 0
  else
    if i < 240 then
      if i < 192 then
        if i < 176 then
          table1038_10.getD (i%16) 0
        else
          table1038_11.getD (i%16) 0
      else
        if i < 208 then
          table1038_12.getD (i%16) 0
        else
          if i < 224 then
            table1038_13.getD (i%16) 0
          else
            table1038_14.getD (i%16) 0
    else
      if i < 272 then
        if i < 256 then
          table1038_15.getD (i%16) 0
        else
          table1038_16.getD (i%16) 0
      else
        if i < 288 then
          table1038_17.getD (i%16) 0
        else
          if i < 304 then
            table1038_18.getD (i%16) 0
          else
            table1038_19.getD (i%16) 0
def book1038 (i : Nat) : Clause := let n := encoded1038 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses1038 : inputsOK 1 1038 a1038 r1038 (baseBook book1038 205).toList=true := by decide +kernel

def rows1038_0 : List Nat := [0x40401,0xc0801,0xc0a01,0x180e01,0xa4e001,0xa4e201,0xa4e401,0xe8e801,0xe8ea01,0xe8ec01,0x1dcf002,0x669dcf202,0x681e8f602,0x671f0fa02,0x679f0fc02,0x210001,0x250201,0x290401,0x2d0801,0x310a01,0x350e01,0x411e01,0x452401,0xf93201]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1038_0 : checkRows book1038 9 205 rows1038_0=true := by decide +kernel

def rows1038_1 : List Nat := [0xfd3801,0x1054001,0xa95401,0xad5801,0xb15e01,0xed6201,0xf16401,0xf56601,0x6d35d6802,0x3b56a01,0x3b56c01,0x3616e01,0x3e1e97402,0x3c57601,0x3c57801,0x3c57a01,0x3657c01,0x36d8201,0xde6eb70fe03,0x3dde001,0x3ddec01,0xe17037d0603,0x3e9ea01,0x502d938bc5129980ba07]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1038_1 : checkRows book1038 9 229 rows1038_1=true := by decide +kernel

def rows1038_2 : List Nat := [0x148b64e2e13da2fc3014cbe09,0x150b64e2e13cbc516934cc209,0x7e901fc02,0x12c8c61ae51a9d7cbe1dc08,0x964630970a1802893a8d7cbe1de0b,0x4048001,0x4048401,0x405fe01,0x410de01,0x4142401,0x4182c01,0x4183801,0x4184401,0x4185001,0x4192a01,0x4195001,0xe37142d1c03,0x435e401,0x2442e8e0d3014d0885bec3209,0x12817470617ea451c3e18fb85c20360c,0x9672b91cc03,0x445e801,0x44a2001,0xe97439d5203]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1038_2 : checkRows book1038 9 253 rows1038_2=true := by decide +kernel

def rows1038_3 : List Nat := [0x89c518c02,0xec75ba96003,0xea503c8e52afe131285bec420a,0x488751c206029df70b84c483e0a,0xa38bc323003,0x8b4659202,0x311a0b86c30198e46e07,0x5e34170e064ad54aae36ae1c8cc6a0c,0x140a4d56b14d3e9e80c389c09,0x12cd44d148a31d814393008,0x28151a8d6814049c06,0x9cd527a612e964dc7e3d1d87404a80c,0xa88c26240a241230a83c484e0a,0x5046131305526944748615078942c4a0d,0x489e601,0x48e4001,0x490e601,0x4945a01,0x49a3801,0x8b49d9802,0x11cc44331910906c371ac1f0280c0cc80d,0x48229b4ae562a9608d2933168d60f80c0c860f,0x5922154865823404da07,0x4a4dd2b2b9a0ce6a24ca81e6b80c0cca0d]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1038_3 : checkRows book1038 9 277 rows1038_3=true := by decide +kernel

def rows1038_4 : List Nat := [0x22106cb642191315944698809,0x110836531d152d45a250d15944698a0c,0x4b81c01,0x4bcd601,0x81cbc1e02,0x4be5401,0x4be5801,0x4c89201,0x4c89a01,0x4ccd201,0x4d89801,0x9acdc9402,0x4e09601,0x4e4ae01,0x261319a4ea5604,0x2610198cecdc04,0x97cee5202]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1038_4 : checkRows book1038 9 301 rows1038_4=true := by decide +kernel

def lastUnits1038 := digits 9 2 0x2793d
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict1038 : checkReasons book1038 318 101 lastUnits1038 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude1038 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 1038=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z a1038
  have hbase : ValidThrough v book1038 205 := book_start Z h hc z eq _ _ _ _ initialClauses1038
  have h0 : ValidThrough v book1038 229 := rows_sound hbase rows1038_0 rowsOk1038_0
  have h1 : ValidThrough v book1038 253 := rows_sound h0 rows1038_1 rowsOk1038_1
  have h2 : ValidThrough v book1038 277 := rows_sound h1 rows1038_2 rowsOk1038_2
  have h3 : ValidThrough v book1038 301 := rows_sound h2 rows1038_3 rowsOk1038_3
  have h4 : ValidThrough v book1038 318 := rows_sound h3 rows1038_4 rowsOk1038_4
  exact book_end h4 _ _ conflict1038
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
