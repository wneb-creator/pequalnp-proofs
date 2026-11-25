import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a1216 : Array Fact := #[(.lab 1 0 1),(.lab 1 1 1),(.lab 5 0 5),(.lab 5 0 1),(.lab 5 0 4),(.lab 5 1 5),(.lab 5 1 1),(.lab 5 1 4),(.avoid 5 4183 0),(.avoid 5 4183 1),(.see 5 10 127 0),(.see 5 10 127 1),(.lab 6 0 1),(.lab 6 0 5),(.avoid 6 314 0),(.reader false 3 0),(.reader false 3 1),(.es false 3 1),(.reader false 13 0),(.reader false 13 1),(.es false 13 1),(.es false 13 5),(.reader false 17 0),(.es false 17 1),(.es false 17 5),(.reader true 3 0),(.reader true 3 1),(.reader true 13 0),(.reader true 13 1),(.reader true 17 0),(.reader true 17 1),(.gate 3 13),(.gate 3 17),(.gate 13 17)]
def r1216 : List Scheme := [(.self 1 0),(.self 1 1),(.self 5 0),(.self 5 1),(.exposure 5 4183),(.avoidNot 5 1 4183 0),(.avoidNot 5 4 4183 0),(.avoidNot 5 1 4183 1),(.avoidNot 5 4 4183 1),(.exactAt 5 10 127),(.seeLab 5 10 1 127 0),(.seeLab 5 10 4 127 0),(.seeLab 5 10 1 127 1),(.seeLab 5 10 4 127 1),(.exposure 6 314),(.avoidNot 6 1 314 0),(.avoidNot 6 5 314 0),(.readerAny false 3),(.readerLab false 3 0 1 true),(.readerLab false 3 1 1 true),(.readerAny false 13),(.readerLab false 13 0 1 false),(.readerLab false 13 0 5 true),(.readerLab false 13 1 1 false),(.readerLab false 13 1 5 true),(.readerAny false 17),(.readerLab false 17 0 1 false),(.readerLab false 17 0 5 false),(.readerAny true 3),(.readerAny true 13),(.readerAny true 17),(.eqLab false 3 13 1 true),(.gateEq true 3 13 0),(.gateEq true 3 13 1),(.eqLab false 3 17 1 true),(.gateEq true 3 17 0),(.gateEq true 3 17 1),(.eqLab false 13 17 5 true),(.gateEq true 13 17 0),(.gateEq true 13 17 1)]

def table1216_0 : List Nat := [65,193,321,705,0x26442,0xc402,0x10402,0x18482,0x1c482,0x2e542,0xc502,0x12502,0x18582,0x1e582,0x741,0x30702]
def table1216_1 : List Nat := [0x34702,0x427c2,0x2300783,0x2304803,0x4e942,0x280e903,0x2b08903,0x281a983,0x2b14983,0xb41,0x2e32b03,0x3036b03,0x6acc2,0x72dc2,0x7aec2,0x2944f83]
def table1216_2 : List Nat := [0x3f6cc83,0x3f70d03,0x2f45003,0x4174c83,0x4178d03,0x3155083,0x4374d83,0x4378e03,0x601,0x681,0x46782,0x46802,0x56902,0x56982,0xb81,0xc01]
def table1216_3 : List Nat := [0x45002,0x55082,0xac1,0x1081,0x8c1,0x1001,385,769,0xa01,0xf81,0xf01,0xec1,0xc81,0xd81,0xd41,0xe41]

def encoded1216 (i : Nat) : Nat :=
  if i < 32 then
    if i < 16 then
      table1216_0.getD (i%16) 0
    else
      table1216_1.getD (i%16) 0
  else
    if i < 48 then
      table1216_2.getD (i%16) 0
    else
      table1216_3.getD (i%16) 0
def book1216 (i : Nat) : Clause := let n := encoded1216 i; unpackLits 7 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses1216 : inputsOK 0 1216 a1216 r1216 (baseBook book1216 40).toList=true := by decide +kernel

def rows1216_0 : List Nat := [0x71e01,0x72001,0x2401,0xa601,0x12c01,0x1b001,0x50cb402,0x52cb602,0x174401,0x17ca01,0x5b62802,0x196201,0x5752202,0x1a6001,0x41221429a05,0x31221839605,0x2eaefb2804,0x69c3e02,0xeb93c9ce7ac007,0x1d3c01,0x6bdc602,0x67dcc02,0x1e3801,0x1eba01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk1216_0 : checkRows book1216 6 40 rows1216_0=true := by decide +kernel

def lastUnits1216 := digits 6 3 0x39ffe
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict1216 : checkReasons book1216 64 33 lastUnits1216 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude1216 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 1216=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=0) h hc bp eq (by decide +kernel)
  let v := truth Z a1216
  have hbase : ValidThrough v book1216 40 := book_start Z h hc z eq _ _ _ _ initialClauses1216
  have h0 : ValidThrough v book1216 64 := rows_sound hbase rows1216_0 rowsOk1216_0
  exact book_end h0 _ _ conflict1216
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
