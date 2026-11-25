import CompactPacking

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def aP266 := ([0xa0021,0xc0021,0x827,0xa00a1,0xa08a1,0xc00c1,0x400c1,0xa00c1,0xc08c1,0x408c1,0xa08c1,0x48c7,0x248c7,0x40c8,0x8040c8,0x1805,0xa1806,0xc1806,0x6805,0x26805,0xa6806,0x8805,0x28805,0xa8806,0xc8806,0x1825,0x21825,0x6825,0x26825,0x8825,0x28825,0x6864,0x8864,0x89a4] : List Nat).toArray.map readPackedFact
def rP266 := ([0x825,0x22829,0x23029,160,0x8a0,192,0x8c0,0x48c5,0x1210c9,0x1228c9,0x9210c9,0x9228c9,0x40c6,0x440ca,0xa40ca,0x200440ca,0x200a40ca,0x1810,0x2801812,0x3001812,0x6810,0x22806812,0x22826812,0x8810,0x2808812,0x23008812,0x2828812,0x23028812,0x1830,0x6830,0x8830,0x29a1813,0x1a1834,0x9a1834,0x3221813,0x221834,0xa21834,0x22a26813,0x226834,0xa26834] : List Nat).map readPackedScheme

def tableP266_0 : List Nat := [321,258,0x4102,449,577,705,0x441,0x325c2,0x18582,0x1c582,0x24602,0x28602,0x3a6c2,0x1a682,0x1c682,0x26702]
def tableP266_1 : List Nat := [0x28702,0x7c1,0x2002783,0x2206783,0x4e942,0x290c903,0x2910983,0x5aac2,0x2e1ea83,0x3114a83,0x2e2ab03,0x3120b03,0x6acc2,0x72dc2,0x7aec2,0x2842f83]
def tableP266_2 : List Nat := [0x3f6cc83,0x3f70d03,0x3047003,0x4174c83,0x4178d03,0x2f51083,0x4374d83,0x4378e03,1,129,0x801,0x881,0x52902,0x52982,0x62a82,0x62b02]
def tableP266_3 : List Nat := [0x50f82,0x61002,0xc41,0x1001,0xa41,0xf81,897,0x501,0xb81,0x1081,0xf01,0xec1,0xc81,0xd81,0xd41,0xe41]

def encodedP266 (i : Nat) : Nat :=
  if i < 32 then
    if i < 16 then
      tableP266_0.getD (i%16) 0
    else
      tableP266_1.getD (i%16) 0
  else
    if i < 48 then
      tableP266_2.getD (i%16) 0
    else
      tableP266_3.getD (i%16) 0
def bookP266 (i : Nat) : Clause := let n := encodedP266 i; unpackLits 7 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClausesP266 : inputsOK 0 266 aP266 rP266 (baseBook bookP266 40).toList=true := by decide +kernel

def rowsP266_0 : List Nat := [513,0x401,0x508a402,0x528a602,0x1aa01,0x22c01,0x2b201,0x33601,0x153e01,0x15c401,0x5f72e02,0x196201,0x5b62802,0x1a6001,0x51839c49e05,0x4183a059a05,0x34c6fb2e04,0x69c4a02,0xeb93c9af39c007,0x1d3c01,0x67dc602,0x73dcc02,0x1e3801,0x1eba01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOkP266_0 : checkRows bookP266 6 40 rowsP266_0=true := by decide +kernel

def lastUnitsP266 := digits 6 3 0x35ffe
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflictP266 : checkReasons bookP266 64 33 lastUnitsP266 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem excludeP266 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 266=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=0) h hc bp eq (by decide +kernel)
  let v := truth Z aP266
  have hbase : ValidThrough v bookP266 40 := book_start Z h hc z eq _ _ _ _ initialClausesP266
  have h0 : ValidThrough v bookP266 64 := rows_sound hbase rowsP266_0 rowsOkP266_0
  exact book_end h0 _ _ conflictP266
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
