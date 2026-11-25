import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a164 : Array Fact := #[(.lab 2 0 6),(.avoid 2 8297 0),(.lab 5 0 6),(.avoid 5 1102 0),(.lab 6 0 6),(.lab 6 1 6),(.lab 8 0 8),(.lab 8 0 11),(.lab 8 0 13),(.lab 8 1 8),(.lab 8 1 11),(.lab 8 1 13),(.avoid 8 10401 0),(.avoid 8 10401 1),(.live 9 1),(.lab 9 0 8),(.lab 9 0 10),(.common 9 10),(.lab 9 0 11),(.lab 9 0 12),(.lab 9 1 8),(.lab 9 1 10),(.lab 9 1 11),(.lab 9 1 12),(.avoid 9 4370 0),(.avoid 9 4370 1),(.avoid 9 5190 0),(.avoid 9 5190 1),(.avoid 9 6151 0),(.avoid 9 6151 1),(.avoid 9 7174 0),(.avoid 9 7174 1),(.see 9 5 5008 0),(.see 9 5 5008 1),(.see 9 5 6789 0),(.see 9 5 6789 1),(.lab 11 0 11),(.lab 11 1 11),(.lab 13 0 13),(.lab 13 1 13),(.reader false 5 0),(.es false 5 6),(.reader false 6 0),(.reader false 13 0),(.es false 13 6),(.reader false 16 0),(.reader false 16 1),(.es false 16 6),(.reader false 17 0),(.reader false 17 1),(.es false 17 6),(.reader false 18 0),(.reader false 18 1),(.es false 18 6),(.reader true 5 0),(.reader true 5 1),(.es true 5 13),(.reader true 6 0),(.reader true 6 1),(.es true 6 13),(.reader true 13 0),(.reader true 13 1),(.reader true 16 0),(.reader true 16 1),(.es true 16 8),(.es true 16 11),(.reader true 17 0),(.reader true 17 1),(.es true 17 8),(.es true 17 10),(.es true 17 11),(.reader true 18 0),(.reader true 18 1),(.es true 18 11),(.gate 5 6),(.gate 5 16),(.gate 13 17),(.gate 16 17),(.gate 16 18),(.gate 17 18)]
def r164 : List Scheme := [(.exposure 2 8297),(.avoidNot 2 6 8297 0),(.exposure 5 1102),(.avoidNot 5 6 1102 0),(.self 6 0),(.self 6 1),(.self 8 0),(.self 8 1),(.exposure 8 10401),(.avoidNot 8 11 10401 0),(.avoidNot 8 13 10401 0),(.avoidNot 8 11 10401 1),(.avoidNot 8 13 10401 1),(.exposure 9 4370),(.avoidNot 9 8 4370 0),(.avoidNot 9 12 4370 0),(.avoidNot 9 8 4370 1),(.avoidNot 9 12 4370 1),(.exposure 9 5190),(.avoidNot 9 10 5190 0),(.avoidNot 9 12 5190 1),(.exposure 9 6151),(.avoidNot 9 12 6151 0),(.avoidNot 9 11 6151 1),(.exposure 9 7174),(.avoidNot 9 11 7174 0),(.avoidNot 9 10 7174 1),(.exactAt 9 5 5008),(.seeLab 9 5 8 5008 0),(.seeLab 9 5 12 5008 0),(.seeLab 9 5 8 5008 1),(.seeLab 9 5 12 5008 1),(.exactAt 9 5 6789),(.seeLab 9 5 11 6789 0),(.seeLab 9 5 12 6789 0),(.seeLab 9 5 11 6789 1),(.seeLab 9 5 12 6789 1),(.adjacentCommon 9 10 5),(.residual 9 10 0 1),(.self 11 0),(.self 11 1),(.self 13 0),(.self 13 1),(.readerAny false 5),(.readerLab false 5 0 6 false),(.readerAny false 6),(.readerAny false 13),(.readerLab false 13 0 6 false),(.readerAny false 16),(.readerAny false 17),(.readerAny false 18),(.readerLab false 18 0 6 true),(.readerLab false 18 1 6 true),(.readerAny true 5),(.readerLab true 5 0 13 false),(.readerLab true 5 1 13 false),(.readerAny true 6),(.readerLab true 6 0 13 true),(.readerLab true 6 1 13 true),(.readerAny true 13),(.readerLive true 13 1),(.readerAny true 16),(.readerLab true 16 0 8 true),(.readerLab true 16 0 11 false),(.readerLab true 16 1 8 true),(.readerLab true 16 1 11 false),(.readerAny true 17),(.readerLab true 17 0 8 false),(.readerLab true 17 0 10 false),(.readerLab true 17 0 10 true),(.readerLab true 17 0 11 false),(.readerLab true 17 1 8 false),(.readerLab true 17 1 11 false),(.readerAny true 18),(.readerLab true 18 0 11 true),(.readerLab true 18 1 11 true),(.gateEq false 5 6 0),(.eqLab true 5 6 13 false),(.eqLab false 5 16 6 false),(.gateEq true 5 16 0),(.gateEq true 5 16 1),(.eqLab false 13 17 6 false),(.gateEq true 13 17 0),(.gateEq false 16 17 0),(.gateEq false 16 17 1),(.eqLab true 16 17 8 true),(.gateEq false 16 18 0),(.gateEq false 16 18 1),(.eqLab false 16 18 6 false),(.eqLab true 16 18 11 false),(.gateEq false 17 18 0),(.gateEq false 17 18 1),(.eqLab false 17 18 6 false),(.eqLab true 17 18 11 false)]

def table164_0 : List Nat := [193,130,449,0x10182,577,705,833,0x4c1,0x6c642,0x38602,0x40602,0x50682,0x58682,0xccc42,0x78c02,0x98c02]
def table164_1 : List Nat := [0xa0c82,0xb8c82,0xdcd42,0x80d02,0xb8d82,0xece42,0x98e02,0xb0e82,0xfcf42,0x90f02,0xa8f82,0x10d042,0x79002,0x9d002,0xa1082,0xbd082]
def table164_2 : List Nat := [0x11d142,0x91102,0x9d102,0xb1182,0xbd182,0x8c1,0xac8470884,0x1241,0x12c1,0x1341,0x13c1,0x1441,0x14805403,0x1541,0x15c1,0x16015583]
def table164_3 : List Nat := [0x1756c2,0x18d842,0x1a59c2,0x1ac21983,0x1ac29a03,0x1bdb42,0x1c045b03,0x1c05db83,0x1d5cc2,0x1dd31c83,0x1dd39d03,0x1ede42,0x75e82,0x1fdf42,0x20431f03,0x2083df03]
def table164_4 : List Nat := [0x20449f83,0x20855f83,0x21e142,0x2207e103,0x22886103,0x22c82103,0x23096103,0x220a6183,0x230b6183,0x2463c2,0x24d22383,0x24d2a403,0x25551403,0x1d9c6503,0x1794e583,0x25df1b03]
def table164_5 : List Nat := [0x25df9b83,0x19166603,0x26611e03,0x26d81683,0x26d89703,0x22602683,0x27599683,0x275a1703,0x1a97e703,0x24a0e703,0x27d99803,0x27da1883,0x1a996783,0x24a36783,1,257]
def table164_6 : List Nat := [0xac84703,0x1481,0x1601,0x1ad982,0x1ada02,0x1ddc82,0x1ddd02,0x205f02,0x205f82,0x24e382,0x24e402,0x2541,0x1d9c42,0x17a582,0x192602,0x1ac1]
def table164_7 : List Nat := [0xa01,0x781,0x2201,0x2041,0x2681,0x2322a103,0xb01,0x266302,0x24c1,0x2781,0x1dc1,0x1c41,0x271f02,0x2701,0x1981,0x1a41]
def table164_8 : List Nat := [0x1701,0x1881,0x16c1,0x1841]

def encoded164 (i : Nat) : Nat :=
  if i < 64 then
    if i < 32 then
      if i < 16 then
        table164_0.getD (i%16) 0
      else
        table164_1.getD (i%16) 0
    else
      if i < 48 then
        table164_2.getD (i%16) 0
      else
        table164_3.getD (i%16) 0
  else
    if i < 96 then
      if i < 80 then
        table164_4.getD (i%16) 0
      else
        table164_5.getD (i%16) 0
    else
      if i < 112 then
        table164_6.getD (i%16) 0
      else
        if i < 128 then
          table164_7.getD (i%16) 0
        else
          table164_8.getD (i%16) 0
def book164 (i : Nat) : Clause := let n := encoded164 i; unpackLits 8 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses164 : inputsOK 0 164 a164 r164 (baseBook book164 94).toList=true := by decide +kernel

def rows164_0 : List Nat := [513,0x40601,0x4a4c01,0xbc565802,0xbe5c5e02,0x86601,0xa6801,0x527201,0x547401,0xc7c01,0xe8001,0x4e9401,0x509601,0x5a569802,0xd69a01,0xc29c01,0xc4a201,0xc8c66402,0x1e361a3c203a05,0x22361a381c3e05,0x868ee2e08404,0xd0ce7a02,0xe4e6aa02,0x28402442268c884807]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk164_0 : checkRows book164 8 94 rows164_0=true := by decide +kernel

def rows164_1 : List Nat := [0x2c402a462e4405,0xc078308a7632eaa48c8490ec340c,0xd4d29202,0xdcbab8f0deee05,0xccca7002,0xf4d801,0x6e106a129e7eb2dab0f6def0180c,0x6c106a16a0827af8dab2b0f6f0de140e,0x6260b4ace8f2faa807,0xfc6401,0xfafeae02,0xf2feb602,0x1006001,0x1026201]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk164_1 : checkRows book164 8 118 rows164_1=true := by decide +kernel

def lastUnits164 := digits 8 3 0x748382
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict164 : checkReasons book164 132 83 lastUnits164 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude164 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 164=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=0) h hc bp eq (by decide +kernel)
  let v := truth Z a164
  have hbase : ValidThrough v book164 94 := book_start Z h hc z eq _ _ _ _ initialClauses164
  have h0 : ValidThrough v book164 118 := rows_sound hbase rows164_0 rowsOk164_0
  have h1 : ValidThrough v book164 132 := rows_sound h0 rows164_1 rowsOk164_1
  exact book_end h1 _ _ conflict164
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
