import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a400 : Array Fact := #[(.lab 8 0 9),(.lab 8 0 11),(.avoid 8 541 0),(.avoid 8 2087 0),(.lab 9 0 9),(.lab 9 1 9),(.lab 11 0 11),(.lab 11 0 9),(.lab 11 0 10),(.lab 11 1 11),(.lab 11 1 9),(.lab 11 1 10),(.avoid 11 1548 0),(.avoid 11 1548 1),(.see 11 4 7812 0),(.see 11 4 7812 1),(.reader false 16 0),(.reader false 16 1),(.reader false 17 0),(.reader false 17 1),(.reader false 18 0),(.reader false 18 1),(.reader true 16 0),(.es true 16 9),(.es true 16 11),(.reader true 17 0),(.reader true 17 1),(.es true 17 9),(.reader true 18 0),(.reader true 18 1),(.es true 18 9),(.es true 18 11),(.gate 16 17),(.gate 16 18),(.gate 17 18)]
def r400 : List Scheme := [(.exposure 8 541),(.avoidNot 8 9 541 0),(.exposure 8 2087),(.avoidNot 8 11 2087 0),(.self 9 0),(.self 9 1),(.self 11 0),(.self 11 1),(.exposure 11 1548),(.avoidNot 11 9 1548 0),(.avoidNot 11 10 1548 0),(.avoidNot 11 9 1548 1),(.avoidNot 11 10 1548 1),(.exactAt 11 4 7812),(.seeLab 11 4 9 7812 0),(.seeLab 11 4 10 7812 0),(.seeLab 11 4 9 7812 1),(.seeLab 11 4 10 7812 1),(.readerAny false 16),(.readerAny false 17),(.readerAny false 18),(.readerAny true 16),(.readerLab true 16 0 9 false),(.readerLab true 16 0 11 false),(.readerAny true 17),(.readerLab true 17 0 9 true),(.readerLab true 17 1 9 true),(.readerAny true 18),(.readerLab true 18 0 9 false),(.readerLab true 18 0 11 true),(.readerLab true 18 1 9 false),(.readerLab true 18 1 11 true),(.gateEq false 16 17 0),(.gateEq false 16 17 1),(.eqLab true 16 17 9 false),(.gateEq false 16 18 0),(.gateEq false 16 18 1),(.eqLab true 16 18 11 false),(.gateEq false 17 18 0),(.gateEq false 17 18 1),(.eqLab true 17 18 9 true)]

def table400_0 : List Nat := [321,258,449,0x4182,577,705,833,0x4c1,0x36642,0x1c602,0x20602,0x28682,0x2c682,0x3e742,0x1c702,0x22702]
def table400_1 : List Nat := [0x28782,0x2e782,0x46842,0x4e942,0x56a42,0xb41,0x2e02b03,0x3006b03,0x6acc2,0x3710c83,0x3714d03,0x76e42,0x3c1ee03,0x3f18e03,0x3c2ae83,0x3f24e83]
def table400_2 : List Nat := [0x4148803,0x414c883,0x365f003,0x4350803,0x4354883,0x3e63083,0x4550903,0x4554983,0x3d6d103,1,129,0xb81,0xc01,0x6ec82,0x6ed02,0x7ee02]
def table400_3 : List Nat := [0x7ee82,0x6d002,0x7d082,0xfc1,0x1081,0xdc1,0x1001,897,0x501,0xf01,0x1101,0xa81,0xa41,0x801,0x901,0x8c1]
def table400_4 : List Nat := [0x9c1]

def encoded400 (i : Nat) : Nat :=
  if i < 32 then
    if i < 16 then
      table400_0.getD (i%16) 0
    else
      table400_1.getD (i%16) 0
  else
    if i < 48 then
      table400_2.getD (i%16) 0
    else
      if i < 64 then
        table400_3.getD (i%16) 0
      else
        table400_4.getD (i%16) 0
def book400 (i : Nat) : Clause := let n := encoded400 i; unpackLits 7 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses400 : inputsOK 0 400 a400 r400 (baseBook book400 41).toList=true := by decide +kernel

def rows400_0 : List Nat := [513,0x20601,0x14952c02,0x15152e02,0x43201,0x53401,0x63a01,0x73e01,0x2b4401,0x2c4a01,0x182f3602,0x336401,0x172d3002,0x356201,0xc1a207092205,0xa1a2080b1e05,0x3c71c373604,0x1ab95002,0x4c92748d9d344007,0x3b2801,0x1a3c4602,0x1d3c4c02,0x3d2401,0x3e2601]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk400_0 : checkRows book400 7 41 rows400_0=true := by decide +kernel

def lastUnits400 := digits 7 3 0xd9fc0
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict400 : checkReasons book400 65 33 lastUnits400 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude400 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 400=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=0) h hc bp eq (by decide +kernel)
  let v := truth Z a400
  have hbase : ValidThrough v book400 41 := book_start Z h hc z eq _ _ _ _ initialClauses400
  have h0 : ValidThrough v book400 65 := rows_sound hbase rows400_0 rowsOk400_0
  exact book_end h0 _ _ conflict400
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
