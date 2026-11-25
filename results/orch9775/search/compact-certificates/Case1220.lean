import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a1220 : Array Fact := #[(.res 0 4),(.res 0 8),(.res 0 13),(.lab 1 0 1),(.lab 1 1 1),(.lab 1 2 1),(.lab 2 0 1),(.lab 2 0 4),(.avoid 2 314 0),(.lab 4 0 4),(.live 4 1),(.lab 4 0 1),(.lab 4 0 5),(.lab 4 0 8),(.common 4 8),(.lab 4 1 4),(.live 4 2),(.lab 4 1 1),(.lab 4 1 5),(.lab 4 1 8),(.lab 4 2 4),(.lab 4 2 1),(.lab 4 2 5),(.lab 4 2 8),(.avoid 4 2087 0),(.avoid 4 2087 1),(.avoid 4 2087 2),(.avoid 4 2338 0),(.avoid 4 2338 1),(.avoid 4 2338 2),(.see 4 10 314 0),(.see 4 10 314 1),(.see 4 10 314 2),(.diff 0 4 8),(.lab 5 0 5),(.lab 5 1 5),(.lab 5 2 5),(.live 8 1),(.lab 8 0 9),(.lab 8 0 13),(.common 8 13),(.live 8 2),(.lab 8 1 9),(.lab 8 1 13),(.lab 8 2 9),(.lab 8 2 13),(.avoid 8 8713 0),(.avoid 8 8713 1),(.avoid 8 8713 2),(.see 8 2 8488 0),(.see 8 2 8488 1),(.see 8 2 8488 2),(.see 8 6 9992 0),(.see 8 6 9992 1),(.see 8 6 9992 2),(.diff 0 8 13),(.lab 10 0 13),(.avoid 10 8297 0),(.lab 13 0 13),(.lab 13 1 13),(.live 13 2),(.lab 13 2 13),(.reader false 4 0),(.reader false 4 1),(.reader false 4 2),(.es false 4 1),(.reader false 6 0),(.es false 6 1),(.es false 6 4),(.reader false 10 0),(.reader false 10 1),(.reader false 10 2),(.es false 10 5),(.reader false 12 0),(.reader false 12 1),(.reader false 12 2),(.es false 12 1),(.es false 12 4),(.reader false 14 0),(.reader false 14 1),(.reader false 14 2),(.es false 14 5),(.reader true 4 0),(.reader true 4 1),(.reader true 4 2),(.reader true 6 0),(.reader true 6 1),(.reader true 6 2),(.reader true 10 0),(.es true 10 13),(.reader true 12 0),(.reader true 12 1),(.reader true 12 2),(.es true 12 13),(.reader true 14 0),(.gate 4 6),(.gate 4 12),(.gate 6 12),(.gate 10 12),(.gate 10 14)]
def r1220 : List Scheme := [(.self 1 0),(.self 1 1),(.self 1 2),(.exposure 2 314),(.avoidNot 2 1 314 0),(.avoidNot 2 4 314 0),(.self 4 0),(.self 4 1),(.earlier 4 1),(.self 4 2),(.someRes 4),(.exposure 4 2087),(.avoidNot 4 1 2087 0),(.avoidNot 4 5 2087 0),(.avoidNot 4 1 2087 1),(.avoidNot 4 5 2087 1),(.avoidLive 4 2087 2),(.avoidNot 4 5 2087 2),(.exposure 4 2338),(.avoidNot 4 1 2338 0),(.avoidNot 4 5 2338 0),(.avoidNot 4 8 2338 0),(.avoidNot 4 1 2338 1),(.avoidNot 4 5 2338 1),(.avoidNot 4 8 2338 1),(.avoidNot 4 1 2338 2),(.avoidNot 4 5 2338 2),(.avoidNot 4 8 2338 2),(.exactAt 4 10 314),(.seeLab 4 10 1 314 0),(.seeLab 4 10 5 314 0),(.seeLab 4 10 8 314 0),(.seeLab 4 10 1 314 1),(.seeLab 4 10 5 314 1),(.seeLab 4 10 8 314 1),(.seeLab 4 10 1 314 2),(.seeLab 4 10 5 314 2),(.seeLab 4 10 8 314 2),(.diffC 0 4 8),(.resCommon 4 8 0),(.residual 4 8 0 1),(.residual 4 8 0 2),(.residual 4 8 1 2),(.self 5 0),(.self 5 1),(.self 5 2),(.earlier 8 1),(.exposure 8 8713),(.avoidNot 8 9 8713 0),(.avoidNot 8 13 8713 0),(.avoidNot 8 9 8713 1),(.avoidNot 8 13 8713 1),(.avoidLive 8 8713 2),(.avoidNot 8 9 8713 2),(.avoidNot 8 13 8713 2),(.exactAt 8 2 8488),(.seeLab 8 2 13 8488 0),(.seeLab 8 2 13 8488 1),(.seeLive 8 2 8488 2),(.exactAt 8 6 9992),(.seeLab 8 6 9 9992 0),(.seeLab 8 6 13 9992 0),(.seeLab 8 6 9 9992 1),(.seeLab 8 6 13 9992 1),(.seeLive 8 6 9992 2),(.seeLab 8 6 9 9992 2),(.seeLab 8 6 13 9992 2),(.diffX 0 8 13),(.diffC 0 8 13),(.adjacentCommon 8 13 2),(.residual 8 13 0 1),(.residual 8 13 0 2),(.residual 8 13 1 2),(.exposure 10 8297),(.avoidNot 10 13 8297 0),(.self 13 0),(.self 13 1),(.self 13 2),(.someRes 13),(.readerAny false 4),(.readerLab false 4 0 1 true),(.readerLab false 4 1 1 true),(.readerLab false 4 2 1 true),(.readerAny false 6),(.readerLab false 6 0 1 false),(.readerLab false 6 0 4 false),(.readerAny false 10),(.readerLab false 10 0 5 false),(.readerLab false 10 1 5 false),(.readerLive false 10 2),(.readerLab false 10 2 5 false),(.readerAny false 12),(.readerLab false 12 0 1 false),(.readerLab false 12 0 4 true),(.readerLab false 12 1 1 false),(.readerLab false 12 1 4 true),(.readerLive false 12 2),(.readerLab false 12 2 1 false),(.readerLab false 12 2 4 true),(.readerAny false 14),(.readerLab false 14 0 5 true),(.readerLab false 14 1 5 true),(.readerLab false 14 2 5 true),(.readerAny true 4),(.readerLive true 4 2),(.readerAny true 6),(.readerLive true 6 2),(.readerAny true 10),(.readerLab true 10 0 13 false),(.readerAny true 12),(.readerLab true 12 0 13 true),(.readerLab true 12 1 13 true),(.readerLive true 12 2),(.readerLab true 12 2 13 true),(.readerAny true 14),(.eqLab false 4 6 1 true),(.gateEq true 4 6 0),(.gateEq true 4 6 1),(.eqLab false 4 12 1 true),(.gateEq true 4 12 0),(.gateEq true 4 12 1),(.eqLab false 6 12 4 false),(.gateEq true 6 12 0),(.gateEq true 6 12 1),(.gateEq false 10 12 0),(.gateEq false 10 12 1),(.eqLab true 10 12 13 false),(.eqLab false 10 14 5 false),(.gateEq true 10 14 0)]

def table1220_0 : List Nat := [449,577,705,0x441,0x30402,0x38402,0x4c1,0x7c1,0x54802,0xa41,0x4802,0xd4ccc43,0x58c02,0x60c02,0x88c82,0x90c82]
def table1220_1 : List Nat := [0x84d02,0xb0d02,0xece4dc3,0x58d82,0x60d82,0x68d82,0x88e02,0x90e02,0x98e02,0xa8e82,0xb0e82,0xb8e82,0x104fcf43,0x58f02,0x64f02,0x68f02]
def table1220_2 : List Nat := [0x88f82,0x94f82,0x98f82,0xa9002,0xb5002,0xb9002,0x9082,0x7408003,0x10c9c6c50705,0x10cbc6c80705,0x10cbc9c80705,0x1141,0x11c1,0x1241,0x12d482,0x1857d743]
def table1220_3 : List Nat := [0x131702,0x139702,0x151782,0x159782,0x14d802,0x161802,0x169802,0x19d958c3,0x13d882,0x15d902,0x14d982,0x1b5ada43,0x135a02,0x139a02,0x155a82,0x159a82]
def table1220_4 : List Nat := [0x14db02,0x165b02,0x169b02,0xdb82,0x11b82,0x1441,0x1bd5d3d29405,0x1bd6d3d49405,0x1bd6d5d49405,0x1cc1,0x1c1c82,0x1d41,0x1dc1,0x1ec1,0x15e02,0x205fdf43]
def table1220_5 : List Nat := [0x20c19f03,0x20c21f83,0x20c2a003,0x2141,0x21836103,0x2203e103,0x23e362c3,0x24066283,0x24096303,0x86382,0x240b6383,0x25e564c3,0x2605e483,0x26c4a483,0x2608e503,0x26c7a503]
def table1220_6 : List Nat := [0x86582,0x260ae583,0x26ca2583,0x2867e743,0x28d12703,0x28d1a783,0x28d22803,0x2a69e943,0x1e6a02,0x2beb6ac3,0x1e6b82,0x2c41,0x2c9c6c03,0x2e6ded43,0x2edd2d03,0x2eddad83]
def table1220_7 : List Nat := [0x1e6e02,0x2edeae03,0x2f41,0x21e0af83,0x2feaa903,0x2feb2983,0x2660b003,0x306d2903,0x306da983,0x26a27083,0x30ed2a83,0x30edab03,0x3164a283,0x31652303,0x2eacf103,0x28a47183]
def table1220_8 : List Nat := [0x31ef2c03,769,897,0x1bd5d3d284,0x1bd6d3d484,0x1bd6d5d484,0x1c01,0x20df02,0x20df82,0x20e002,0x2181,0x2201,0x26e482,0x26e502,0x26e582,0x28e702]
def table1220_9 : List Nat := [0x28e782,0x28e802,0x2c81,0x2eed02,0x2eed82,0x2eee02,0x20af82,0x26b082,0x2eb102,0x31c1,0x2ec1,0x3101,0x26c1,0x3081,0x20c1,0x2f81]
def table1220_10 : List Nat := [0x1bdb02,0x1bd702,0x1bd782,0x1bc1,193,257,0x1081,0x1e01,0x2a01,0x2b81,0x2405a383,0x26242483,0x88602,0x26242503,0x50ec70f04,0x262582]
def table1220_11 : List Nat := [0x28c1,0x2441,0x2601,0x2e01,0x3001,0x2d01,0x2dc1,0x2981,0x2b01,0x2941,0x2ac1]

def encoded1220 (i : Nat) : Nat :=
  if i < 96 then
    if i < 48 then
      if i < 16 then
        table1220_0.getD (i%16) 0
      else
        if i < 32 then
          table1220_1.getD (i%16) 0
        else
          table1220_2.getD (i%16) 0
    else
      if i < 64 then
        table1220_3.getD (i%16) 0
      else
        if i < 80 then
          table1220_4.getD (i%16) 0
        else
          table1220_5.getD (i%16) 0
  else
    if i < 144 then
      if i < 112 then
        table1220_6.getD (i%16) 0
      else
        if i < 128 then
          table1220_7.getD (i%16) 0
        else
          table1220_8.getD (i%16) 0
    else
      if i < 160 then
        table1220_9.getD (i%16) 0
      else
        if i < 176 then
          table1220_10.getD (i%16) 0
        else
          table1220_11.getD (i%16) 0
def book1220 (i : Nat) : Clause := let n := encoded1220 i; unpackLits 8 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses1220 : inputsOK 1 1220 a1220 r1220 (baseBook book1220 129).toList=true := by decide +kernel

def rows1220_0 : List Nat := [0x60801,0x60a01,0x8a8c01,0x8a8e01,0x8a9001,0x929401,0xa001,0x2a201,0x4a401,0x102a6a802,0x104a6aa02,0xcba01,0xebe01,0x12c401,0x56c801,0x58ca01,0x5acc01,0x10cd6d802,0x96dc01,0x98de01,0x9ae201,0x114e601,0x116f201,0x124fc01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1220_0 : checkRows book1220 8 129 rows1220_0=true := by decide +kernel

def rows1220_1 : List Nat := [0xe4d70002,0x12b2926da03,0x1353001,0x11d1b18b603,0x1392e01,0x113110e9e03,0x13d2c01,0x66626b0b088482805e08,0x5c6f06727e767078626140740b,0x5c6f06707a76727c666540740b,0x7e7b0b086c685f454340760a,0x1468601,0x1468801,0x1484c01,0x14a9c01,0x14ed001,0x14ed401,0x385442301e24164e342214b4b218263b4d484a12,0x54384e481436222024162e1eb0ad543a2618f8b94d49364417,0x52384e48143622202416281a1c2c414d483e11,0x2a4e241434b24a48ac38ae3d58402cfabd4d49365214,0x2450283e3d4c3006,0x24502e4442395c4e46321410c2c14d482a10,0x123211ec603]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1220_1 : checkRows book1220 8 153 rows1220_1=true := by decide +kernel

def rows1220_2 : List Nat := [0x13360fe02,0x15b575f62b604,0x14ee001,0x13d64ec02,0xd2cef4ef3f53513b68ea09,0x1676ada02,0x1696cf002,0x13b6cf602,0x1516ece02,0x15370d202]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1220_2 : checkRows book1220 8 177 rows1220_2=true := by decide +kernel

def lastUnits1220 := digits 8 3 0x9fbab9
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict1220 : checkReasons book1220 187 116 lastUnits1220 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude1220 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 1220=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=1) h hc bp eq (by decide +kernel)
  let v := truth Z a1220
  have hbase : ValidThrough v book1220 129 := book_start Z h hc z eq _ _ _ _ initialClauses1220
  have h0 : ValidThrough v book1220 153 := rows_sound hbase rows1220_0 rowsOk1220_0
  have h1 : ValidThrough v book1220 177 := rows_sound h0 rows1220_1 rowsOk1220_1
  have h2 : ValidThrough v book1220 187 := rows_sound h1 rows1220_2 rowsOk1220_2
  exact book_end h2 _ _ conflict1220
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
