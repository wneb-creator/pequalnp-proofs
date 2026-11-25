import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a416 : Array Fact := #[(.lab 8 0 9),(.lab 8 0 11),(.avoid 8 541 0),(.avoid 8 2087 0),(.lab 9 0 9),(.live 9 1),(.lab 9 0 10),(.common 9 10),(.lab 9 0 11),(.lab 9 0 12),(.lab 9 1 9),(.lab 9 1 10),(.lab 9 1 11),(.lab 9 1 12),(.avoid 9 5190 0),(.avoid 9 5190 1),(.avoid 9 6151 0),(.avoid 9 6151 1),(.avoid 9 7174 0),(.avoid 9 7174 1),(.see 9 5 6789 0),(.see 9 5 6789 1),(.lab 11 0 11),(.lab 11 1 11),(.reader false 16 0),(.reader false 16 1),(.reader false 17 0),(.reader false 17 1),(.reader false 18 0),(.reader false 18 1),(.reader true 16 0),(.es true 16 9),(.es true 16 11),(.reader true 17 0),(.reader true 17 1),(.es true 17 9),(.es true 17 10),(.es true 17 11),(.reader true 18 0),(.reader true 18 1),(.es true 18 11),(.gate 16 17),(.gate 16 18),(.gate 17 18)]
def r416 : List Scheme := [(.exposure 8 541),(.avoidNot 8 9 541 0),(.exposure 8 2087),(.avoidNot 8 11 2087 0),(.self 9 0),(.self 9 1),(.exposure 9 5190),(.avoidNot 9 10 5190 0),(.avoidNot 9 12 5190 0),(.avoidNot 9 10 5190 1),(.avoidNot 9 12 5190 1),(.exposure 9 6151),(.avoidNot 9 11 6151 0),(.avoidNot 9 12 6151 1),(.exposure 9 7174),(.avoidNot 9 10 7174 0),(.avoidNot 9 11 7174 1),(.exactAt 9 5 6789),(.seeLab 9 5 11 6789 0),(.seeLab 9 5 12 6789 0),(.seeLab 9 5 11 6789 1),(.seeLab 9 5 12 6789 1),(.adjacentCommon 9 10 5),(.residual 9 10 0 1),(.self 11 0),(.self 11 1),(.readerAny false 16),(.readerAny false 17),(.readerAny false 18),(.readerAny true 16),(.readerLab true 16 0 9 false),(.readerLab true 16 0 11 false),(.readerAny true 17),(.readerLab true 17 0 9 true),(.readerLab true 17 0 10 false),(.readerLab true 17 0 11 false),(.readerLive true 17 1),(.readerLab true 17 1 9 true),(.readerLab true 17 1 10 false),(.readerLab true 17 1 10 true),(.readerLab true 17 1 11 false),(.readerAny true 18),(.readerLab true 18 0 11 true),(.readerLab true 18 1 11 true),(.gateEq false 16 17 0),(.gateEq false 16 17 1),(.eqLab true 16 17 9 false),(.gateEq false 16 18 0),(.gateEq false 16 18 1),(.eqLab true 16 18 11 false),(.gateEq false 17 18 0),(.gateEq false 17 18 1),(.eqLab true 17 18 11 false)]

def table416_0 : List Nat := [321,258,449,0x4182,577,0x541,0x3e742,0x18702,0x24702,0x2c782,0x34782,0x46842,0x20802,0x34882,0x4e942,0x18902]
def table416_1 : List Nat := [0x30982,0x56a42,0x20a02,0x26a02,0x30a82,0x36a82,961,0xb8d14384,0xb41,0xbc1,0x66c42,0x6ed42,0x76e42,0xf41,0x3e02f03,0x4006f03]
def table416_2 : List Nat := [0x8b0c2,0x4711083,0x481b083,0x4a23083,0x17102,0x4729103,0x482f103,0x492d103,0x4a33103,0x9f342,0x5159303,0x515d383,0x5368c03,0x536cc83,0x467f483,0x5570c03]
def table416_3 : List Nat := [0x5574c83,0x5083503,0x5770d03,0x5774d83,0x5097583,1,129,0x171a283,0xf81,0x1001,0x8f082,0x8f102,0xa3302,0xa3382,0x8d482,0xa1502]
def table416_4 : List Nat := [0x1441,0x1501,0x11c1,0x1481,0x4a91083,0x95202,0x95102,0x401,0x1281,0x1581,0xe81,0xe41,0xc01,0xd01,0xcc1,0xdc1]

def encoded416 (i : Nat) : Nat :=
  if i < 32 then
    if i < 16 then
      table416_0.getD (i%16) 0
    else
      table416_1.getD (i%16) 0
  else
    if i < 48 then
      table416_2.getD (i%16) 0
    else
      if i < 64 then
        table416_3.getD (i%16) 0
      else
        table416_4.getD (i%16) 0
def book416 (i : Nat) : Clause := let n := encoded416 i; unpackLits 7 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses416 : inputsOK 0 416 a416 r416 (baseBook book416 53).toList=true := by decide +kernel

def rows416_0 : List Nat := [513,0x20601,0x162e01,0x1a9d3c02,0x1b1d3e02,0x44201,0x54a01,0x185401,0x195601,0x385c01,0x396201,0x1ebc5202,0x407e01,0x1dba4002,0x427c01,0x28886241d1a22a07,0x82218a0950990442609,0x3c837509d2451c07,0xd222c90c2a05,0x8e3474003,0x20486802,0x6cd33610e4c15807,0x4a3801,0x20cb5e02]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk416_0 : checkRows book416 7 53 rows416_0=true := by decide +kernel

def rows416_1 : List Nat := [0x24cb6402,0x4c3401,0x4d3601]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk416_1 : checkRows book416 7 77 rows416_1=true := by decide +kernel

def lastUnits416 := digits 7 3 0x10e74f
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict416 : checkReasons book416 80 45 lastUnits416 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude416 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 416=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=0) h hc bp eq (by decide +kernel)
  let v := truth Z a416
  have hbase : ValidThrough v book416 53 := book_start Z h hc z eq _ _ _ _ initialClauses416
  have h0 : ValidThrough v book416 77 := rows_sound hbase rows416_0 rowsOk416_0
  have h1 : ValidThrough v book416 80 := rows_sound h0 rows416_1 rowsOk416_1
  exact book_end h1 _ _ conflict416
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
