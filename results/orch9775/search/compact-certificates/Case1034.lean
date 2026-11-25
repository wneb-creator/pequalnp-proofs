import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a1034 : Array Fact := #[(.lab 3 0 6),(.avoid 3 245 0),(.lab 6 0 6),(.lab 6 1 6),(.lab 7 0 7),(.common 7 11),(.lab 7 1 7),(.lab 8 0 8),(.lab 8 1 8),(.lab 9 0 7),(.lab 9 0 8),(.lab 9 0 11),(.lab 9 1 7),(.lab 9 1 8),(.lab 9 1 11),(.avoid 9 432 0),(.avoid 9 432 1),(.avoid 9 10656 0),(.avoid 9 10656 1),(.see 9 1 5008 0),(.see 9 1 5008 1),(.lab 11 0 11),(.live 11 1),(.lab 11 0 7),(.lab 11 0 8),(.lab 11 0 12),(.lab 11 1 11),(.lab 11 1 7),(.lab 11 1 8),(.lab 11 1 12),(.avoid 11 245 0),(.avoid 11 245 1),(.avoid 11 432 0),(.avoid 11 432 1),(.avoid 11 4309 0),(.avoid 11 4309 1),(.see 11 3 2213 0),(.see 11 3 2213 1),(.see 11 3 7426 0),(.see 11 3 7426 1),(.reader false 7 0),(.reader false 8 0),(.es false 8 6),(.reader false 16 0),(.reader false 16 1),(.reader false 17 0),(.reader false 17 1),(.reader false 18 0),(.reader false 18 1),(.es false 18 6),(.reader true 7 0),(.reader true 7 1),(.es true 7 7),(.reader true 8 0),(.reader true 8 1),(.es true 8 7),(.reader true 16 0),(.reader true 16 1),(.es true 16 8),(.reader true 17 0),(.reader true 17 1),(.es true 17 7),(.es true 17 8),(.es true 17 11),(.reader true 18 0),(.reader true 18 1),(.es true 18 7),(.es true 18 8),(.es true 18 11),(.gate 7 8),(.gate 8 18),(.gate 16 17),(.gate 16 18),(.gate 17 18)]
def r1034 : List Scheme := [(.exposure 3 245),(.avoidNot 3 6 245 0),(.self 6 0),(.self 6 1),(.self 7 0),(.self 7 1),(.adjacentCommon 7 11 3),(.self 8 0),(.self 8 1),(.exposure 9 432),(.avoidNot 9 7 432 0),(.avoidNot 9 8 432 0),(.avoidNot 9 7 432 1),(.avoidNot 9 8 432 1),(.exposure 9 10656),(.avoidNot 9 7 10656 0),(.avoidNot 9 11 10656 0),(.avoidNot 9 7 10656 1),(.avoidNot 9 11 10656 1),(.exactAt 9 1 5008),(.seeLab 9 1 7 5008 0),(.seeLab 9 1 8 5008 0),(.seeLab 9 1 7 5008 1),(.seeLab 9 1 8 5008 1),(.self 11 0),(.self 11 1),(.exposure 11 245),(.avoidNot 11 7 245 0),(.avoidNot 11 7 245 1),(.exposure 11 432),(.avoidNot 11 7 432 0),(.avoidNot 11 8 432 0),(.avoidNot 11 7 432 1),(.avoidNot 11 8 432 1),(.exposure 11 4309),(.avoidNot 11 7 4309 0),(.avoidNot 11 12 4309 0),(.avoidNot 11 7 4309 1),(.avoidNot 11 12 4309 1),(.exactAt 11 3 2213),(.seeLab 11 3 7 2213 0),(.seeLab 11 3 7 2213 1),(.exactAt 11 3 7426),(.seeLab 11 3 8 7426 0),(.seeLab 11 3 12 7426 0),(.seeLab 11 3 8 7426 1),(.seeLab 11 3 12 7426 1),(.residual 11 7 0 1),(.readerAny false 7),(.readerAny false 8),(.readerLab false 8 0 6 false),(.readerAny false 16),(.readerAny false 17),(.readerAny false 18),(.readerLab false 18 0 6 true),(.readerLab false 18 1 6 true),(.readerAny true 7),(.readerLab true 7 0 7 true),(.readerLab true 7 1 7 true),(.readerAny true 8),(.readerLab true 8 0 7 false),(.readerLab true 8 1 7 false),(.readerAny true 16),(.readerLab true 16 0 8 true),(.readerLab true 16 1 8 true),(.readerAny true 17),(.readerLab true 17 0 7 true),(.readerLab true 17 0 8 false),(.readerLab true 17 0 11 false),(.readerLab true 17 1 7 true),(.readerLab true 17 1 8 false),(.readerLab true 17 1 11 false),(.readerAny true 18),(.readerLab true 18 0 7 false),(.readerLab true 18 0 7 true),(.readerLab true 18 0 8 false),(.readerLab true 18 0 11 true),(.readerLive true 18 1),(.readerLab true 18 1 7 false),(.readerLab true 18 1 7 true),(.readerLab true 18 1 8 false),(.readerLab true 18 1 11 true),(.gateEq false 7 8 0),(.eqLab true 7 8 7 true),(.eqLab false 8 18 6 false),(.gateEq true 8 18 0),(.gateEq true 8 18 1),(.gateEq false 16 17 0),(.gateEq false 16 17 1),(.eqLab true 16 17 8 true),(.gateEq false 16 18 0),(.gateEq false 16 18 1),(.eqLab true 16 18 8 true),(.gateEq false 17 18 0),(.gateEq false 17 18 1),(.eqLab true 17 18 7 true),(.eqLab true 17 18 11 false)]

def table1034_0 : List Nat := [193,130,321,449,577,833,705,961,0x441,0x847c2,0x48782,0x50782,0x60802,0x68802,0x948c2,0x48882]
def table1034_1 : List Nat := [0x58882,0x60902,0x70902,0xa49c2,0x4c982,0x50982,0x64a02,0x68a02,0xac1,0xd41,0xfcf42,0xb8f02,0xd8f82,0x10d042,0xb9002,0xc1002]
def table1034_2 : List Nat := [0xd9082,0xe1082,0x11d142,0xb9102,0xc9102,0xd9182,0xe9182,0x12d242,0xbd202,0xdd282,0x13d342,0xc1302,0xcd302,0xe1382,0xed382,0xdcbcb0284]
def table1034_3 : List Nat := [0x1441,0x14c1,0x15005483,0x1655c2,0x1756c2,0x1857c2,0x18c11783,0x18c19803,0x19d942,0x1a421903,0x1a431983,0x1b5ac2,0x1b8bda83,0x1b8ddb03,0x1cdc42,0x1d439c03]
def table1034_4 : List Nat := [0x1d441c83,0x1e5dc2,0x1ec49d83,0x1f055d83,0x1f85dd83,0x1ec61e03,0x1f06de03,0x1f875e03,0x20e042,0x210be003,0x214ba003,0x218c6003,0x224aa003,0xb6082,0x210de083,0x214da083]
def table1034_5 : List Nat := [0x218e6083,0x224d2083,0x22d49403,0x1bda2283,0x18956303,0x23601a83,0x23609b03,0x23d69583,0x23d71603,0x1f5d2383,0x24579583,0x24581603,0x21dd2403,0x24d79683,0x24d81703,0x215ea483]
def table1034_6 : List Nat := [0x221fe483,1,0xdcbcb03,0x1501,0x18d782,0x18d802,0x1a5902,0x1a5982,0x1d5c02,0x1d5c82,0x226002,0x226082,0x22c1,0x1bda02,0x18a302,0x18c1]
def table1034_7 : List Nat := [0x2301,0x21a12083,0x21a102,0x21a002,0x2181,0x1d41,0x2401,0x1edf9d83,0x1edf82,0x2241,0x1a41,0x1bc1,0x212002,0x212082,0x2101,0x2481]
def table1034_8 : List Nat := [0x23d782,0x23c1,0x1f41,0x681,0x1e01,0x1dc1,0x541,0x781,0x981,0x841,0xa41,0x601]

def encoded1034 (i : Nat) : Nat :=
  if i < 64 then
    if i < 32 then
      if i < 16 then
        table1034_0.getD (i%16) 0
      else
        table1034_1.getD (i%16) 0
    else
      if i < 48 then
        table1034_2.getD (i%16) 0
      else
        table1034_3.getD (i%16) 0
  else
    if i < 96 then
      if i < 80 then
        table1034_4.getD (i%16) 0
      else
        table1034_5.getD (i%16) 0
    else
      if i < 112 then
        table1034_6.getD (i%16) 0
      else
        if i < 128 then
          table1034_7.getD (i%16) 0
        else
          table1034_8.getD (i%16) 0
def book1034 (i : Nat) : Clause := let n := encoded1034 i; unpackLits 8 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses1034 : inputsOK 0 1034 a1034 r1034 (baseBook book1034 97).toList=true := by decide +kernel

def rows1034_0 : List Nat := [513,0xc5e01,0xc2626402,0x46c01,0x66e01,0x87201,0xa7401,0xe7e01,0x108001,0x309801,0x32a201,0x6260a402,0xd8a601,0xc6a801,0xcac86a02,0xdedc01,0x4854445a4aa09c5807,0x4c54445646969290e25c09,0x404e3a503e9496e45208,0x3c42c4a09e9a90e6e43a09,0xd2d07c02,0xe8eab802,0x2c1c26202888842207,0x281c26242c8e8a82ee1e09]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1034_0 : checkRows book1034 8 97 rows1034_0=true := by decide +kernel

def rows1034_1 : List Nat := [0xd6d49002,0xcecc7002,0xf4da01,0x447a467692aaf6e04a08,0x78347638ac9ce0f63608,0x90f8fa02,0xbec0fcf2f004,0x6866bab4feecb006,0x6866bcb66b00feecae08,0xeb02b202,0x1426122e1a2805,0x105068c02,0x1088201,0x1050a8602,0x10c1601,0x10c2a01,0x10e1201,0x1102601,0x1121801]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1034_1 : checkRows book1034 8 121 rows1034_1=true := by decide +kernel

def lastUnits1034 := digits 8 2 0x8b8a
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict1034 : checkReasons book1034 140 22 lastUnits1034 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude1034 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 1034=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=0) h hc bp eq (by decide +kernel)
  let v := truth Z a1034
  have hbase : ValidThrough v book1034 97 := book_start Z h hc z eq _ _ _ _ initialClauses1034
  have h0 : ValidThrough v book1034 121 := rows_sound hbase rows1034_0 rowsOk1034_0
  have h1 : ValidThrough v book1034 140 := rows_sound h0 rows1034_1 rowsOk1034_1
  exact book_end h1 _ _ conflict1034
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
