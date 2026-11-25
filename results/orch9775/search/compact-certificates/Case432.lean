import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a432 : Array Fact := #[(.lab 0 0 0),(.lab 0 1 0),(.lab 0 2 0),(.res 0 6),(.res 0 10),(.res 0 11),(.lab 3 0 3),(.lab 3 1 3),(.lab 3 2 3),(.lab 4 0 4),(.lab 4 0 0),(.lab 4 0 3),(.lab 4 0 6),(.avoid 4 1102 0),(.avoid 4 2087 0),(.lab 5 0 0),(.lab 5 0 4),(.avoid 5 541 0),(.lab 6 0 6),(.live 6 1),(.lab 6 0 0),(.lab 6 0 2),(.lab 6 0 3),(.lab 6 0 10),(.common 6 10),(.lab 6 1 6),(.live 6 2),(.lab 6 1 0),(.lab 6 1 2),(.lab 6 1 3),(.lab 6 1 10),(.lab 6 2 6),(.lab 6 2 2),(.lab 6 2 3),(.lab 6 2 10),(.avoid 6 541 0),(.avoid 6 541 1),(.avoid 6 541 2),(.avoid 6 1548 0),(.avoid 6 1548 1),(.avoid 6 1548 2),(.see 6 8 127 0),(.see 6 8 127 1),(.see 6 8 127 2),(.see 6 8 1102 0),(.see 6 8 1102 1),(.see 6 8 1102 2),(.see 6 8 5316 0),(.see 6 8 5316 1),(.see 6 8 5316 2),(.diff 0 6 10),(.live 10 1),(.lab 10 0 9),(.lab 10 0 11),(.common 10 11),(.live 10 2),(.lab 10 1 11),(.lab 10 1 12),(.lab 10 2 9),(.lab 10 2 11),(.avoid 10 6151 0),(.avoid 10 6151 1),(.avoid 10 6151 2),(.avoid 10 14977 0),(.avoid 10 14977 1),(.avoid 10 14977 2),(.see 10 5 7174 0),(.see 10 5 7174 1),(.see 10 5 7174 2),(.see 10 5 16256 0),(.see 10 5 16256 1),(.see 10 5 16256 2),(.diff 0 10 11),(.live 11 2),(.reader false 1 0),(.reader false 1 1),(.reader false 1 2),(.es false 1 0),(.reader false 8 0),(.reader false 8 1),(.reader false 8 2),(.es false 8 3),(.reader false 10 0),(.es false 10 0),(.es false 10 4),(.reader false 11 0),(.es false 11 3),(.es false 11 6),(.reader false 14 0),(.es false 14 0),(.es false 14 4),(.reader false 18 0),(.reader false 18 1),(.reader false 18 2),(.es false 18 3),(.es false 18 6),(.reader true 1 0),(.reader true 1 1),(.reader true 1 2),(.reader true 8 0),(.reader true 8 1),(.reader true 8 2),(.reader true 10 0),(.reader true 10 1),(.reader true 10 2),(.reader true 11 0),(.reader true 11 1),(.reader true 11 2),(.reader true 14 0),(.reader true 14 1),(.reader true 14 2),(.reader true 18 0),(.reader true 18 1),(.reader true 18 2),(.gate 1 10),(.gate 1 14),(.gate 8 11),(.gate 8 18),(.gate 10 14),(.gate 11 18)]
def r432 : List Scheme := [(.self 0 0),(.self 0 1),(.self 0 2),(.self 3 0),(.self 3 1),(.self 3 2),(.self 4 0),(.exposure 4 1102),(.avoidNot 4 3 1102 0),(.avoidNot 4 6 1102 0),(.exposure 4 2087),(.avoidNot 4 0 2087 0),(.exposure 5 541),(.avoidNot 5 0 541 0),(.avoidNot 5 4 541 0),(.self 6 0),(.self 6 1),(.earlier 6 1),(.self 6 2),(.someRes 6),(.exposure 6 541),(.avoidNot 6 0 541 0),(.avoidNot 6 3 541 0),(.avoidNot 6 0 541 1),(.avoidNot 6 2 541 1),(.avoidNot 6 3 541 1),(.avoidLive 6 541 2),(.avoidNot 6 2 541 2),(.exposure 6 1548),(.avoidNot 6 2 1548 0),(.avoidNot 6 10 1548 0),(.avoidNot 6 2 1548 1),(.avoidNot 6 3 1548 1),(.avoidNot 6 10 1548 1),(.avoidNot 6 2 1548 2),(.avoidNot 6 3 1548 2),(.avoidNot 6 10 1548 2),(.exactAt 6 8 127),(.seeLab 6 8 0 127 0),(.seeLab 6 8 2 127 0),(.seeLab 6 8 3 127 0),(.seeLive 6 8 127 1),(.seeLab 6 8 0 127 1),(.seeLab 6 8 2 127 1),(.seeLab 6 8 3 127 1),(.seeLive 6 8 127 2),(.seeLab 6 8 2 127 2),(.exactAt 6 8 1102),(.seeLab 6 8 10 1102 0),(.seeLab 6 8 3 1102 1),(.seeLab 6 8 10 1102 1),(.seeLab 6 8 2 1102 2),(.exactAt 6 8 5316),(.seeLab 6 8 2 5316 0),(.seeLab 6 8 10 5316 0),(.seeLab 6 8 2 5316 1),(.seeLab 6 8 10 5316 1),(.seeLab 6 8 2 5316 2),(.seeLab 6 8 10 5316 2),(.diffC 0 6 10),(.resCommon 6 10 0),(.residual 6 10 0 1),(.residual 6 10 0 2),(.residual 6 10 1 2),(.earlier 10 1),(.someRes 10),(.exposure 10 6151),(.avoidNot 10 11 6151 0),(.avoidNot 10 12 6151 1),(.avoidNot 10 11 6151 2),(.exposure 10 14977),(.avoidNot 10 9 14977 0),(.avoidNot 10 11 14977 0),(.avoidNot 10 11 14977 1),(.avoidNot 10 9 14977 2),(.avoidNot 10 11 14977 2),(.exactAt 10 5 7174),(.seeLab 10 5 11 7174 0),(.seeLab 10 5 12 7174 1),(.seeLab 10 5 11 7174 2),(.exactAt 10 5 16256),(.seeLab 10 5 9 16256 0),(.seeLab 10 5 11 16256 0),(.seeLab 10 5 11 16256 1),(.seeLab 10 5 9 16256 2),(.seeLab 10 5 11 16256 2),(.diffC 0 10 11),(.adjacentCommon 10 11 4),(.residual 10 11 0 1),(.residual 10 11 0 2),(.residual 10 11 1 2),(.someRes 11),(.readerAny false 1),(.readerLab false 1 0 0 true),(.readerLab false 1 1 0 true),(.readerLab false 1 2 0 true),(.readerAny false 8),(.readerLab false 8 0 3 true),(.readerLab false 8 1 3 true),(.readerLab false 8 2 3 true),(.readerAny false 10),(.readerLab false 10 0 0 false),(.readerLab false 10 0 4 true),(.readerAny false 11),(.readerLab false 11 0 3 false),(.readerLab false 11 0 6 false),(.readerAny false 14),(.readerLab false 14 0 0 false),(.readerLab false 14 0 4 false),(.readerAny false 18),(.readerLab false 18 0 3 false),(.readerLab false 18 0 6 true),(.readerLab false 18 1 3 false),(.readerLab false 18 1 6 true),(.readerLive false 18 2),(.readerLab false 18 2 3 false),(.readerLab false 18 2 6 true),(.readerAny true 1),(.readerLive true 1 2),(.readerAny true 8),(.readerLive true 8 2),(.readerAny true 10),(.readerLive true 10 2),(.readerAny true 11),(.readerLive true 11 2),(.readerAny true 14),(.readerLive true 14 2),(.readerAny true 18),(.readerLive true 18 2),(.eqLab false 1 10 0 true),(.gateEq true 1 10 0),(.gateEq true 1 10 1),(.eqLab false 1 14 0 true),(.gateEq true 1 14 0),(.gateEq true 1 14 1),(.eqLab false 8 11 3 true),(.gateEq true 8 11 0),(.gateEq true 8 11 1),(.eqLab false 8 18 3 true),(.gateEq true 8 18 0),(.gateEq true 8 18 1),(.eqLab false 10 14 4 true),(.gateEq true 10 14 0),(.gateEq true 10 14 1),(.eqLab false 11 18 6 false),(.gateEq true 11 18 0),(.gateEq true 11 18 1)]

def table432_0 : List Nat := [65,193,321,833,961,0x441,0x4c1,0x6c1,0x58682,0x60682,0x741,0x50702,0x8c1,0x78882,0x80882,0x941]
def table432_1 : List Nat := [0xcc1,0x9cd02,0xfc1,0x1cd02,0x12d251c3,0xa1182,0xb1182,0xd9202,0xe1202,0xe9202,0xd5282,0x101282,0x1453d343,0xa9302,0xb9302,0xe1382]
def table432_2 : List Nat := [0xe9382,0xf1382,0x101402,0x109402,0x111402,0x15d554c3,0xa5482,0xad482,0xb1482,0x9d502,0xdd502,0xe5502,0xe9502,0xd5582,0x105582,0x1756d643]
def table432_3 : List Nat := [0xb9602,0xe9682,0xf1682,0x105702,0x18d857c3,0xad782,0xb9782,0xe5802,0xf1802,0x105882,0x111882,0x21902,0xc420183,0x194f4bc98c05,0x19514bcd0c05,0x19514f4d0c05]
def table432_4 : List Nat := [0x19db82,0x25b82,0x1f5ede43,0x1a9e02,0x1c9e82,0x1d9f02,0x20e05fc3,0x1a1f82,0x1a9f82,0x1c2002,0x1d2082,0x1da082,0x2261e143,0x1aa102,0x1ce182,0x1da202]
def table432_5 : List Nat := [0x23e362c3,0x1a6282,0x1aa282,0x1c2302,0x1d6382,0x1da382,0x2a402,0x1b41,0x245c5ad99b05,0x245ddadb9b05,0x245ddc5b9b05,0x2e482,0x2665e543,0x26c02503,0x26c0a583,0x26c12603]
def table432_6 : List Nat := [0x2867e743,0x28c32703,0x28c3a783,0x28c42803,0x2941,0x29856903,0x2a44a903,0x2ac1,0x2b05ea83,0x2b866a83,0x2c41,0x2c87ec03,0x2d086c03,0x2eee6dc3,0x2f0b6d83,0x2fc92d83]
def table432_7 : List Nat := [0x2f0eee03,0x2fccae03,0xd6e82,0x2f10ee83,0x2fcfae83,0x3170f043,0x1bf102,0x32f271c3,0x24f282,0x3473f343,0x1bf402,0x35f574c3,0x24f582,0x3776f643,0x1bf702,0x38f877c3]
def table432_8 : List Nat := [0x24f882,0x29e6b903,0x39733003,0x3973b083,0x2ce6b983,0x39f63003,0x39f6b083,0x2b68ba03,0x3a74b183,0x3a753203,0x2f68ba83,0x3af7b183,0x3af83203,0x2d6a3b03,0x3b763303,0x3b76b383]
def table432_9 : List Nat := [0x2fabfb83,0x3bf7b483,0x3bf83503,0x581,0x601,0x501,0x781,0x801,0x245c5ad984,0x245ddadb84,0x245ddc5b84,0x26e502,0x26e582,0x26e602,0x28e702,0x28e782]
def table432_10 : List Nat := [0x28e802,0x2981,0x2a41,0x2b01,0x2b81,0x2c81,0x2d01,0x2fed82,0x2fee02,0x2fee82,0x26b902,0x26b982,0x28ba02,0x3b01,0x363302,0x36b382]
def table432_11 : List Nat := [0x2fbb82,0x2fc1,0x3b81,0x28c1,0x3a01,0x26c1,0x3901,0x3981,0x245ba383,0x245b9f83,0x245b9c43,0x245b82,0x1bf682,0x1bc1,577,0x2441]
def table432_12 : List Nat := [0x1901,641,0x2481,0x3281,0x3581,0x3881,0xb1882,0xb1582,0xb1302,0xb01,0x2f1402,0x2f0d42,0xd18d383,0x2f18c2,0x2f01,0x3a81]
def table432_13 : List Nat := [0x3801,0x37c1,0x3181,0x3481,0x3241,0x3541]

def encoded432 (i : Nat) : Nat :=
  if i < 112 then
    if i < 48 then
      if i < 16 then
        table432_0.getD (i%16) 0
      else
        if i < 32 then
          table432_1.getD (i%16) 0
        else
          table432_2.getD (i%16) 0
    else
      if i < 80 then
        if i < 64 then
          table432_3.getD (i%16) 0
        else
          table432_4.getD (i%16) 0
      else
        if i < 96 then
          table432_5.getD (i%16) 0
        else
          table432_6.getD (i%16) 0
  else
    if i < 160 then
      if i < 128 then
        table432_7.getD (i%16) 0
      else
        if i < 144 then
          table432_8.getD (i%16) 0
        else
          table432_9.getD (i%16) 0
    else
      if i < 192 then
        if i < 176 then
          table432_10.getD (i%16) 0
        else
          table432_11.getD (i%16) 0
      else
        if i < 208 then
          table432_12.getD (i%16) 0
        else
          table432_13.getD (i%16) 0
def book432 (i : Nat) : Clause := let n := encoded432 i; unpackLits 8 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses432 : inputsOK 1 432 a432 r432 (baseBook book432 147).toList=true := by decide +kernel

def rows432_0 : List Nat := [0xe1001,0xe1201,0x141601,0x181a01,0x181c01,0xaeb001,0xaeb201,0xaeb401,0xba01,0x2bc01,0x4be01,0x6c201,0x8c401,0xac601,0x12ac8ca02,0xcc8cc02,0x126ced002,0x128ced202,0x12cd4d602,0x12ed4d802,0x1ede01,0x20e201,0x24e801,0x1430201]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk432_0 : checkRows book432 8 147 rows432_0=true := by decide +kernel

def rows432_1 : List Nat := [0x14b0801,0x1470e01,0x14d451a02,0x15b1c01,0x15b1e01,0x1492001,0x153514eda03,0x1636001,0x1413f3cc003,0x1675801,0x13b3936b803,0x16b5401,0x16b5601,0x9291353294aaa88c07,0xa130a2908e8170a607,0x8898849a869e8b3134809c0a,0xa496a08ca6937573713209,0xf2eb5f0cecf56d6f0408,0xf2eb5d0afb78fcf4ed6d6f060b,0x17a8201,0x17b7601,0x17c7601,0x17eac01,0x182b601]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk432_1 : checkRows book432 8 171 rows432_1=true := by decide +kernel

def rows432_2 : List Nat := [0x184f001,0x184f801,0x1850001,0x423c7e7c78265a4a542e28443674722c51817c3813,0x387a3a6c6a686e302878443626225c5a2d8d817c4214,0x687a6a3c3b8c52782634282e544b8e502d817c7013,0x64607e7c4839907866263634283e2e56544b8e502d817c5e17,0x7c2634282a604c5e4a625832e0dae6665c484644dd7d81927818,0x3a4a385840e0dae45add95924e0c,0x687a6e423e227827817c6c0a,0x687a6a3c3a39999422782797817c700e,0x423c7e7c759a78279795817c380c,0x1679d1402,0xf6ef2519698987659f1009,0x18ba0fe02,0x19fa31602,0x165a32202,0x187a4ee02,0x189a6f602]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk432_2 : checkRows book432 8 195 rows432_2=true := by decide +kernel

def lastUnits432 := digits 8 3 0xb4d5d4
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict432 : checkReasons book432 214 137 lastUnits432 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude432 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 432=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z a432
  have hbase : ValidThrough v book432 147 := book_start Z h hc z eq _ _ _ _ initialClauses432
  have h0 : ValidThrough v book432 171 := rows_sound hbase rows432_0 rowsOk432_0
  have h1 : ValidThrough v book432 195 := rows_sound h0 rows432_1 rowsOk432_1
  have h2 : ValidThrough v book432 214 := rows_sound h1 rows432_2 rowsOk432_2
  exact book_end h2 _ _ conflict432
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
