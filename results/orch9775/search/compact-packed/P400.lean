import CompactPacking

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aP400 := ([0x120101,0x160101,0x2107,0x4907,0x120121,0x120921,0x160161,0x120161,0x140161,0x160961,0x120961,0x140961,0x4167,0x24167,0x2e2168,0xae2168,0x8005,0x28005,0x8805,0x28805,0x9005,0x29005,0x8025,0x128026,0x168026,0x8825,0x28825,0x128826,0x9025,0x29025,0x129026,0x169026,0x8a04,0x9204,0x9224] : List Nat).toArray.map readPackedFact
def rP400 := ([0x2105,0x84909,0x4905,0x125909,288,0x920,352,0x960,0x4165,0x104969,0x105169,0x904969,0x905169,0x2e2166,0xb92216a,0xb94216a,0x2b92216a,0x2b94216a,0x8010,0x8810,0x9010,0x8030,0x4808032,0x5808032,0x8830,0x24808832,0x24828832,0x9030,0x4809032,0x25809032,0x4829032,0x25829032,0x228014,0xa28014,0x4a28033,0x248014,0xa48014,0x5a48033,0x248814,0xa48814,0x24a48833] : List Nat).map readPackedScheme

def tableP400_0 : List Nat := [321,258,449,0x4182,577,705,833,0x4c1,0x36642,0x1c602,0x20602,0x28682,0x2c682,0x3e742,0x1c702,0x22702]
def tableP400_1 : List Nat := [0x28782,0x2e782,0x46842,0x4e942,0x56a42,0xb41,0x2e02b03,0x3006b03,0x6acc2,0x3710c83,0x3714d03,0x76e42,0x3c1ee03,0x3f18e03,0x3c2ae83,0x3f24e83]
def tableP400_2 : List Nat := [0x4148803,0x414c883,0x365f003,0x4350803,0x4354883,0x3e63083,0x4550903,0x4554983,0x3d6d103,1,129,0xb81,0xc01,0x6ec82,0x6ed02,0x7ee02]
def tableP400_3 : List Nat := [0x7ee82,0x6d002,0x7d082,0xfc1,0x1081,0xdc1,0x1001,897,0x501,0xf01,0x1101,0xa81,0xa41,0x801,0x901,0x8c1]
def tableP400_4 : List Nat := [0x9c1]

def encodedP400 (i : Nat) : Nat :=
  if i < 32 then
    if i < 16 then
      tableP400_0.getD (i%16) 0
    else
      tableP400_1.getD (i%16) 0
  else
    if i < 48 then
      tableP400_2.getD (i%16) 0
    else
      if i < 64 then
        tableP400_3.getD (i%16) 0
      else
        tableP400_4.getD (i%16) 0
def bookP400 (i : Nat) : Clause := let n := encodedP400 i; unpackLits 7 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesP400 : inputsOK 0 400 aP400 rP400 (baseBook bookP400 41).toList=true := by decide +kernel

def rowsP400_0 : List Nat := [513,0x20601,0x14952c02,0x15152e02,0x43201,0x53401,0x63a01,0x73e01,0x2b4401,0x2c4a01,0x182f3602,0x336401,0x172d3002,0x356201,0xc1a207092205,0xa1a2080b1e05,0x3c71c373604,0x1ab95002,0x4c92748d9d344007,0x3b2801,0x1a3c4602,0x1d3c4c02,0x3d2401,0x3e2601]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP400_0 : checkRows bookP400 7 41 rowsP400_0=true := by decide +kernel

def lastUnitsP400 := digits 7 3 0xd9fc0
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictP400 : checkReasons bookP400 65 33 lastUnitsP400 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeP400 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 400=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=0) h hc bp eq (by decide +kernel)
  let v := truth Z aP400
  have hbase : ValidThrough v bookP400 41 := book_start Z h hc z eq _ _ _ _ initialClausesP400
  have h0 : ValidThrough v bookP400 65 := rows_sound hbase rowsP400_0 rowsOkP400_0
  exact book_end h0 _ _ conflictP400
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
