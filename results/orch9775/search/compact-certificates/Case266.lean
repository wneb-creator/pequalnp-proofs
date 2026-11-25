import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a266 : Array Fact := #[(.lab 1 0 5),(.lab 1 0 6),(.avoid 1 245 0),(.lab 5 0 5),(.lab 5 1 5),(.lab 6 0 6),(.lab 6 0 2),(.lab 6 0 5),(.lab 6 1 6),(.lab 6 1 2),(.lab 6 1 5),(.avoid 6 2087 0),(.avoid 6 2087 1),(.see 6 8 127 0),(.see 6 8 127 1),(.reader false 3 0),(.es false 3 5),(.es false 3 6),(.reader false 13 0),(.reader false 13 1),(.es false 13 5),(.reader false 17 0),(.reader false 17 1),(.es false 17 5),(.es false 17 6),(.reader true 3 0),(.reader true 3 1),(.reader true 13 0),(.reader true 13 1),(.reader true 17 0),(.reader true 17 1),(.gate 3 13),(.gate 3 17),(.gate 13 17)]
def r266 : List Scheme := [(.exposure 1 245),(.avoidNot 1 5 245 0),(.avoidNot 1 6 245 0),(.self 5 0),(.self 5 1),(.self 6 0),(.self 6 1),(.exposure 6 2087),(.avoidNot 6 2 2087 0),(.avoidNot 6 5 2087 0),(.avoidNot 6 2 2087 1),(.avoidNot 6 5 2087 1),(.exactAt 6 8 127),(.seeLab 6 8 2 127 0),(.seeLab 6 8 5 127 0),(.seeLab 6 8 2 127 1),(.seeLab 6 8 5 127 1),(.readerAny false 3),(.readerLab false 3 0 5 false),(.readerLab false 3 0 6 false),(.readerAny false 13),(.readerLab false 13 0 5 true),(.readerLab false 13 1 5 true),(.readerAny false 17),(.readerLab false 17 0 5 false),(.readerLab false 17 0 6 true),(.readerLab false 17 1 5 false),(.readerLab false 17 1 6 true),(.readerAny true 3),(.readerAny true 13),(.readerAny true 17),(.eqLab false 3 13 5 false),(.gateEq true 3 13 0),(.gateEq true 3 13 1),(.eqLab false 3 17 6 false),(.gateEq true 3 17 0),(.gateEq true 3 17 1),(.eqLab false 13 17 5 true),(.gateEq true 13 17 0),(.gateEq true 13 17 1)]

def table266_0 : List Nat := [321,258,0x4102,449,577,705,0x441,0x325c2,0x18582,0x1c582,0x24602,0x28602,0x3a6c2,0x1a682,0x1c682,0x26702]
def table266_1 : List Nat := [0x28702,0x7c1,0x2002783,0x2206783,0x4e942,0x290c903,0x2910983,0x5aac2,0x2e1ea83,0x3114a83,0x2e2ab03,0x3120b03,0x6acc2,0x72dc2,0x7aec2,0x2842f83]
def table266_2 : List Nat := [0x3f6cc83,0x3f70d03,0x3047003,0x4174c83,0x4178d03,0x2f51083,0x4374d83,0x4378e03,1,129,0x801,0x881,0x52902,0x52982,0x62a82,0x62b02]
def table266_3 : List Nat := [0x50f82,0x61002,0xc41,0x1001,0xa41,0xf81,897,0x501,0xb81,0x1081,0xf01,0xec1,0xc81,0xd81,0xd41,0xe41]

def encoded266 (i : Nat) : Nat :=
  if i < 32 then
    if i < 16 then
      table266_0.getD (i%16) 0
    else
      table266_1.getD (i%16) 0
  else
    if i < 48 then
      table266_2.getD (i%16) 0
    else
      table266_3.getD (i%16) 0
def book266 (i : Nat) : Clause := let n := encoded266 i; unpackLits 7 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses266 : inputsOK 0 266 a266 r266 (baseBook book266 40).toList=true := by decide +kernel

def rows266_0 : List Nat := [513,0x401,0x508a402,0x528a602,0x1aa01,0x22c01,0x2b201,0x33601,0x153e01,0x15c401,0x5f72e02,0x196201,0x5b62802,0x1a6001,0x51839c49e05,0x4183a059a05,0x34c6fb2e04,0x69c4a02,0xeb93c9af39c007,0x1d3c01,0x67dc602,0x73dcc02,0x1e3801,0x1eba01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk266_0 : checkRows book266 6 40 rows266_0=true := by decide +kernel

def lastUnits266 := digits 6 3 0x35ffe
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict266 : checkReasons book266 64 33 lastUnits266 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude266 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 266=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=0) h hc bp eq (by decide +kernel)
  let v := truth Z a266
  have hbase : ValidThrough v book266 40 := book_start Z h hc z eq _ _ _ _ initialClauses266
  have h0 : ValidThrough v book266 64 := rows_sound hbase rows266_0 rowsOk266_0
  exact book_end h0 _ _ conflict266
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
