import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a645 : Array Fact := #[(.lab 0 0 4),(.lab 0 0 5),(.avoid 0 314 0),(.res 0 5),(.res 0 8),(.res 0 10),(.lab 4 0 4),(.lab 4 1 4),(.lab 4 2 4),(.lab 5 0 5),(.common 5 8),(.lab 5 1 5),(.live 5 2),(.lab 5 2 5),(.lab 8 0 8),(.live 8 1),(.lab 8 0 5),(.lab 8 0 10),(.common 8 10),(.lab 8 0 13),(.lab 8 1 8),(.live 8 2),(.lab 8 1 5),(.lab 8 1 10),(.lab 8 1 13),(.lab 8 2 8),(.lab 8 2 5),(.lab 8 2 10),(.lab 8 2 13),(.avoid 8 8297 0),(.avoid 8 8297 1),(.avoid 8 8297 2),(.avoid 8 9288 0),(.avoid 8 9288 1),(.avoid 8 9288 2),(.see 8 0 1290 0),(.see 8 0 1290 1),(.see 8 0 1290 2),(.see 8 0 9992 0),(.see 8 0 9992 1),(.see 8 0 9992 2),(.see 8 2 8488 0),(.see 8 2 8488 1),(.see 8 2 8488 2),(.see 8 2 9992 0),(.see 8 2 9992 1),(.see 8 2 9992 2),(.diff 0 8 5),(.diff 0 8 10),(.lab 9 0 10),(.lab 9 0 12),(.avoid 9 1102 0),(.avoid 9 4183 0),(.lab 10 0 10),(.lab 10 0 8),(.lab 10 0 12),(.lab 10 1 10),(.live 10 2),(.lab 10 1 8),(.lab 10 1 12),(.lab 10 2 10),(.avoid 10 4370 0),(.avoid 10 4370 1),(.avoid 10 4370 2),(.avoid 10 5008 0),(.avoid 10 5008 1),(.avoid 10 5008 2),(.lab 12 0 12),(.lab 12 1 12),(.lab 12 2 12),(.reader false 0 0),(.reader false 1 0),(.es false 1 4),(.es false 1 5),(.reader false 10 0),(.reader false 10 1),(.reader false 10 2),(.es false 10 4),(.reader false 13 0),(.reader false 13 1),(.reader false 13 2),(.reader false 14 0),(.reader false 14 1),(.reader false 14 2),(.es false 14 5),(.reader false 15 0),(.reader false 15 1),(.reader false 15 2),(.reader true 0 0),(.reader true 0 1),(.reader true 0 2),(.es true 0 8),(.reader true 1 0),(.reader true 1 1),(.reader true 1 2),(.es true 1 8),(.reader true 10 0),(.reader true 10 1),(.reader true 10 2),(.es true 10 12),(.reader true 13 0),(.es true 13 10),(.es true 13 12),(.reader true 14 0),(.reader true 14 1),(.reader true 14 2),(.es true 14 10),(.es true 14 12),(.reader true 15 0),(.reader true 15 1),(.reader true 15 2),(.es true 15 12),(.gate 0 1),(.gate 1 10),(.gate 1 14),(.gate 10 14),(.gate 13 14),(.gate 13 15),(.gate 14 15)]
def r645 : List Scheme := [(.exposure 0 314),(.avoidNot 0 4 314 0),(.avoidNot 0 5 314 0),(.self 4 0),(.self 4 1),(.self 4 2),(.self 5 0),(.self 5 1),(.self 5 2),(.someRes 5),(.resCommon 5 8 0),(.self 8 0),(.self 8 1),(.earlier 8 1),(.self 8 2),(.someRes 8),(.exposure 8 8297),(.avoidNot 8 5 8297 0),(.avoidNot 8 13 8297 0),(.avoidNot 8 5 8297 1),(.avoidNot 8 13 8297 1),(.avoidNot 8 5 8297 2),(.avoidNot 8 13 8297 2),(.exposure 8 9288),(.avoidNot 8 10 9288 0),(.avoidNot 8 13 9288 0),(.avoidNot 8 10 9288 1),(.avoidNot 8 13 9288 1),(.avoidLive 8 9288 2),(.avoidNot 8 10 9288 2),(.avoidNot 8 13 9288 2),(.exactAt 8 0 1290),(.seeLab 8 0 10 1290 0),(.seeLab 8 0 10 1290 1),(.seeLive 8 0 1290 2),(.exactAt 8 0 9992),(.seeLab 8 0 13 9992 0),(.seeLab 8 0 10 9992 1),(.seeLive 8 0 9992 2),(.exactAt 8 2 8488),(.seeLab 8 2 5 8488 0),(.seeLab 8 2 13 8488 0),(.seeLab 8 2 5 8488 1),(.seeLab 8 2 13 8488 1),(.seeLive 8 2 8488 2),(.seeLab 8 2 5 8488 2),(.seeLab 8 2 13 8488 2),(.exactAt 8 2 9992),(.seeLab 8 2 10 9992 0),(.seeLab 8 2 13 9992 0),(.seeLab 8 2 10 9992 1),(.seeLab 8 2 13 9992 1),(.seeLive 8 2 9992 2),(.seeLab 8 2 10 9992 2),(.seeLab 8 2 13 9992 2),(.diffC 0 8 5),(.residual 8 5 0 1),(.residual 8 5 0 2),(.residual 8 5 1 2),(.diffC 0 8 10),(.adjacentCommon 8 10 0),(.residual 8 10 0 1),(.residual 8 10 0 2),(.residual 8 10 1 2),(.exposure 9 1102),(.avoidNot 9 10 1102 0),(.exposure 9 4183),(.avoidNot 9 12 4183 0),(.self 10 0),(.self 10 1),(.self 10 2),(.someRes 10),(.exposure 10 4370),(.avoidNot 10 8 4370 0),(.avoidNot 10 12 4370 1),(.avoidLive 10 4370 2),(.exposure 10 5008),(.avoidNot 10 12 5008 0),(.avoidNot 10 8 5008 1),(.avoidLive 10 5008 2),(.self 12 0),(.self 12 1),(.self 12 2),(.readerAny false 0),(.readerAny false 1),(.readerLab false 1 0 4 false),(.readerLab false 1 0 5 false),(.readerAny false 10),(.readerLab false 10 0 4 true),(.readerLab false 10 1 4 true),(.readerLab false 10 2 4 true),(.readerAny false 13),(.readerLive false 13 2),(.readerAny false 14),(.readerLab false 14 0 5 true),(.readerLab false 14 1 5 true),(.readerLive false 14 2),(.readerLab false 14 2 5 true),(.readerAny false 15),(.readerLive false 15 2),(.readerAny true 0),(.readerLab true 0 0 8 true),(.readerLab true 0 1 8 true),(.readerLab true 0 2 8 true),(.readerAny true 1),(.readerLab true 1 0 8 false),(.readerLab true 1 1 8 false),(.readerLive true 1 2),(.readerAny true 10),(.readerLab true 10 0 12 false),(.readerLive true 10 2),(.readerAny true 13),(.readerLab true 13 0 10 false),(.readerLab true 13 0 12 false),(.readerAny true 14),(.readerLab true 14 0 10 true),(.readerLab true 14 1 10 true),(.readerLab true 14 1 12 false),(.readerLive true 14 2),(.readerLab true 14 2 10 true),(.readerAny true 15),(.readerLab true 15 0 12 true),(.readerLab true 15 1 12 true),(.readerLab true 15 2 12 true),(.gateEq false 0 1 0),(.eqLab true 0 1 8 true),(.eqLab false 1 10 4 false),(.gateEq true 1 10 1),(.eqLab false 1 14 5 false),(.gateEq true 1 14 0),(.gateEq true 1 14 1),(.gateEq true 10 14 0),(.eqLab true 10 14 12 false),(.gateEq false 13 14 0),(.gateEq false 13 14 1),(.eqLab true 13 14 10 false),(.gateEq false 13 15 0),(.gateEq false 13 15 1),(.eqLab true 13 15 12 false),(.gateEq false 14 15 0),(.gateEq false 14 15 1),(.eqLab true 14 15 12 false)]

def table645_0 : List Nat := [321,258,0x8102,833,961,0x441,0x4c1,0x5c1,0x6c1,0x1c602,0x5420183,0x741,0xa41,0x7ca82,0xcc1,0x24a82]
def table645_1 : List Nat := [0xfcf4ec3,0x80e82,0x98e82,0xb0f02,0xc0f02,0xd0f82,0xe0f82,0x1150d043,0x89002,0x99002,0xb9082,0xc1082,0xad102,0xd9102,0xe1102,0x12d251c3]
def table645_2 : List Nat := [0x8d182,0xbd202,0xad282,0x1453d343,0x99302,0xbd382,0xad402,0x15d554c3,0x81482,0x9d482,0xb1502,0xc5502,0xad582,0xd1582,0xe5582,0x1756d643]
def table645_3 : List Nat := [0x89602,0x9d602,0xb9682,0xc5682,0xad702,0xd9702,0xe5702,0x19782,0x17cb48478505,0x17cd484a8505,0x17cd4b4a8505,0x29802,0x941,0x184bc8c78905,0x184dc8ca8905,0x184dcbca8905]
def table645_4 : List Nat := [0x19c1,0x189982,0x1a41,0x191a02,0x1ac1,0x1c41,0x1e41,0x2dc82,0x1fdf5ec3,0x1b1e82,0x1d9f02,0x1cdf82,0x2160e043,0x1ba002,0x1d2082,0x1ce102]
def table645_5 : List Nat := [0x21c1,0x2241,0x22c1,0x2341,0x23c1,0x24006383,0x2480e383,0x2665e543,0x26c32503,0x26c3a583,0x26c42603,0x2867e743,0x66802,0x29e968c3,0x2a44a883,0x2a45a903]
def table645_6 : List Nat := [0x66982,0x2a46a983,0x2beb6ac3,0x66b82,0x2d6cec43,0x2dc72c03,0x2dca2c83,0x2dccad03,0x2f6eee43,0x2f9b6e03,0x2f9d6e83,0x1cef02,0x3170f043,0x319bf003,0x1cf102,0x3241]
def table645_7 : List Nat := [0x3298f203,0x33197203,0x34f473c3,0x355ab383,0x355c3403,0x359df403,0x1cf482,0x355e3483,0x3776f643,0x37e1b603,0x37e23683,0x37e2b703,0x3863a303,0x2fedb803,0x26a47883,0x38f0ae83]
def table645_8 : List Nat := [0x2a24f903,0x3973ae03,0x39742e83,0x39f3b003,0x35b1f983,0x3a68a703,0x3a692783,0x3532fa03,0x3aeaa703,0x3aeb2783,0x37b37a83,0x3b6aa883,0x3b6b2903,0x37b5fb03,1,129]
def table645_9 : List Nat := [0x184bc8c784,0x184dc8ca84,0x184dcbca84,0x1881,0x1901,0x2401,0x2481,0x26e502,0x26e582,0x26e602,0x2a6882,0x2a6902,0x2a6982,0x2dec02,0x2dec82,0x2ded02]
def table645_10 : List Nat := [0x3281,0x3301,0x357382,0x357402,0x357482,0x37f602,0x37f682,0x37f702,0x3841,0x2fed82,0x26b882,0x2a3902,0x353a02,0x37ba82,0x37c1,0x3a81]
def table645_11 : List Nat := [0x3541,0x3a01,0x2a41,0x3901,0x26c1,0x3881,0x185702,0x185002,0x185082,0x1841,641,0x1c81,0x1f81,0x2101,0x2f01,0x3101]
def table645_12 : List Nat := [0x2dc1,0x2fc1,0x31ae82,0x3481,0x35ae02,0x3581,0x3b01,0xa8ec84184,0x66b02,0x641,449,0x1781,0x110ec2,0x1101,0xa94c843,0x174a89c3]
def table645_13 : List Nat := [0x174a82,0x144982,0x1741,0xac1,0xe41,577,0xf81,0x541,0x14c1,0x801,0x9c1,0xec1]

def encoded645 (i : Nat) : Nat :=
  if i < 112 then
    if i < 48 then
      if i < 16 then
        table645_0.getD (i%16) 0
      else
        if i < 32 then
          table645_1.getD (i%16) 0
        else
          table645_2.getD (i%16) 0
    else
      if i < 80 then
        if i < 64 then
          table645_3.getD (i%16) 0
        else
          table645_4.getD (i%16) 0
      else
        if i < 96 then
          table645_5.getD (i%16) 0
        else
          table645_6.getD (i%16) 0
  else
    if i < 160 then
      if i < 128 then
        table645_7.getD (i%16) 0
      else
        if i < 144 then
          table645_8.getD (i%16) 0
        else
          table645_9.getD (i%16) 0
    else
      if i < 192 then
        if i < 176 then
          table645_10.getD (i%16) 0
        else
          table645_11.getD (i%16) 0
      else
        if i < 208 then
          table645_12.getD (i%16) 0
        else
          table645_13.getD (i%16) 0
def book645 (i : Nat) : Clause := let n := encoded645 i; unpackLits 8 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses645 : inputsOK 1 645 a645 r645 (baseBook book645 142).toList=true := by decide +kernel

def rows645_0 : List Nat := [513,0x401,0x787a01,0x787c01,0x787e01,0x808201,0x848601,0x11ca8aa02,0x11ea8ac02,0x6b001,0x8b201,0xab401,0xcbc01,0xebe01,0x10c201,0x16ca01,0x18cc01,0x1cce01,0x126dee002,0x128dee202,0x88e601,0x8ae801,0x8cee01,0xa0f201]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk645_0 : checkRows book645 8 142 rows645_0=true := by decide +kernel

def rows645_1 : List Nat := [0xa2f401,0xa4f601,0xa8a6f802,0x150fa01,0x12afc01,0x12d0001,0x1410e01,0x1431401,0x14f4d4af003,0x15d5a01,0x1494744e403,0x1615801,0x1393734ba03,0x1655601,0x133312eae03,0x1695401,0x30343d23246c6a682e08,0x1a3f2042645e624032316c440b,0x1a3f2040605e664236356c440b,0x606523243a382f716f6c5e0a,0x1727601,0x1748e01,0x1769601,0x1769e01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk645_1 : checkRows book645 8 166 rows645_1=true := by decide +kernel

def rows645_2 : List Nat := [0x176d601,0x176dc01,0x13f3d3ac803,0x1815201,0x98da9cd8d4ff7b7f836a9a0a,0x176ec01,0xe494909302d387796782ea0a,0x108e4d98504fed189877f676b7d060d,0x15d8b1a02,0x2a267270146e1a1e2008,0xbab71912b8c1638d5f0a09,0xbab71710c590c6c0b9638d5f0c0c,0x1921201,0x1946e01,0x2a287456544e518e5c3c141e399794200f,0x545270242398145c1e1a3c3997944e0e,0x545a70721a141f97944e09,0x545c742c2a20239c28665e6252141f97944e11,0x262c745c5a4e5636502f8e32259e141f979b942013,0x34462e48339a4a06,0x303e2e423664565e4e6253a2584c45a19a4011,0x1a46801,0x1a46c01,0x1a61e01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk645_2 : checkRows book645 8 190 rows645_2=true := by decide +kernel

def rows645_3 : List Nat := [0x1a82c01,0x195aa1402,0x5a5674282620239dafa797ac4e0c,0x1b05001,0x1b05201,0x1a795b38e03]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk645_3 : checkRows book645 8 214 rows645_3=true := by decide +kernel

def lastUnits645 := digits 8 2 0xdadb
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict645 : checkReasons book645 220 18 lastUnits645 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude645 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 645=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z a645
  have hbase : ValidThrough v book645 142 := book_start Z h hc z eq _ _ _ _ initialClauses645
  have h0 : ValidThrough v book645 166 := rows_sound hbase rows645_0 rowsOk645_0
  have h1 : ValidThrough v book645 190 := rows_sound h0 rows645_1 rowsOk645_1
  have h2 : ValidThrough v book645 214 := rows_sound h1 rows645_2 rowsOk645_2
  have h3 : ValidThrough v book645 220 := rows_sound h2 rows645_3 rowsOk645_3
  exact book_end h3 _ _ conflict645
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
