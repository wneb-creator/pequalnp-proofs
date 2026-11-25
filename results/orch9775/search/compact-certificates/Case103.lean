import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a103 : Array Fact := #[(.lab 0 0 0),(.lab 0 0 4),(.avoid 0 314 0),(.res 0 8),(.res 1 8),(.res 0 9),(.res 1 9),(.res 0 10),(.res 1 10),(.lab 4 0 4),(.lab 4 1 4),(.lab 4 2 4),(.lab 4 3 4),(.lab 5 0 0),(.lab 5 0 4),(.avoid 5 541 0),(.live 8 1),(.lab 8 0 9),(.common 8 9),(.lab 8 0 10),(.common 8 10),(.live 8 2),(.lab 8 1 9),(.lab 8 1 10),(.live 8 3),(.lab 8 2 9),(.lab 8 2 10),(.avoid 8 1548 0),(.avoid 8 1548 1),(.avoid 8 1548 2),(.avoid 8 1548 3),(.see 8 0 1290 0),(.see 8 0 1290 1),(.see 8 0 1290 2),(.see 8 0 1290 3),(.see 8 0 9992 0),(.see 8 0 9992 1),(.see 8 0 9992 2),(.see 8 0 9992 3),(.see 8 6 9992 0),(.see 8 6 9992 1),(.see 8 6 9992 2),(.see 8 6 9992 3),(.diff 0 8 9),(.diff 1 8 9),(.diff 0 8 10),(.diff 1 8 10),(.live 9 1),(.lab 9 0 7),(.lab 9 0 8),(.lab 9 0 10),(.common 9 10),(.live 9 2),(.lab 9 1 7),(.lab 9 1 8),(.lab 9 1 10),(.lab 9 1 13),(.live 9 3),(.lab 9 2 7),(.lab 9 2 8),(.lab 9 2 10),(.lab 9 3 8),(.lab 9 3 10),(.avoid 9 432 0),(.avoid 9 432 1),(.avoid 9 432 2),(.avoid 9 432 3),(.avoid 9 1290 0),(.avoid 9 1290 1),(.avoid 9 1290 2),(.avoid 9 1290 3),(.avoid 9 8488 0),(.avoid 9 8488 1),(.avoid 9 8488 2),(.avoid 9 8488 3),(.see 9 1 5008 0),(.see 9 1 5008 1),(.see 9 1 5008 2),(.see 9 1 5008 3),(.see 9 1 16256 0),(.see 9 1 16256 1),(.see 9 1 16256 2),(.see 9 1 16256 3),(.see 9 5 9992 0),(.see 9 5 9992 1),(.see 9 5 9992 2),(.see 9 5 9992 3),(.see 9 6 792 0),(.see 9 6 792 1),(.see 9 6 792 2),(.see 9 6 792 3),(.see 9 6 9992 0),(.see 9 6 9992 1),(.see 9 6 9992 2),(.see 9 6 9992 3),(.see 9 6 16256 0),(.see 9 6 16256 1),(.see 9 6 16256 2),(.see 9 6 16256 3),(.diff 0 9 8),(.diff 1 9 8),(.diff 0 9 10),(.diff 1 9 10),(.live 10 2),(.live 10 3),(.reader false 1 0),(.es false 1 0),(.es false 1 4),(.reader false 10 0),(.reader false 10 1),(.reader false 10 2),(.reader false 10 3),(.es false 10 4),(.reader false 14 0),(.es false 14 0),(.es false 14 4),(.reader true 1 0),(.reader true 1 1),(.reader true 1 2),(.reader true 1 3),(.reader true 10 0),(.reader true 10 1),(.reader true 10 2),(.reader true 10 3),(.reader true 14 0),(.reader true 14 1),(.reader true 14 2),(.reader true 14 3),(.gate 1 10),(.gate 1 14),(.gate 10 14)]
def r103 : List Scheme := [(.self 0 0),(.exposure 0 314),(.avoidNot 0 4 314 0),(.self 4 0),(.self 4 1),(.self 4 2),(.self 4 3),(.exposure 5 541),(.avoidNot 5 0 541 0),(.avoidNot 5 4 541 0),(.earlier 8 1),(.allRes 8 0),(.allRes 8 1),(.exposure 8 1548),(.avoidNot 8 9 1548 0),(.avoidNot 8 10 1548 0),(.avoidLive 8 1548 1),(.avoidNot 8 9 1548 1),(.avoidNot 8 10 1548 1),(.avoidLive 8 1548 2),(.avoidNot 8 9 1548 2),(.avoidNot 8 10 1548 2),(.avoidLive 8 1548 3),(.exactAt 8 0 1290),(.seeLab 8 0 10 1290 0),(.seeLab 8 0 10 1290 1),(.seeLive 8 0 1290 2),(.seeLive 8 0 1290 3),(.exactAt 8 0 9992),(.seeLab 8 0 9 9992 0),(.seeLab 8 0 10 9992 0),(.seeLab 8 0 9 9992 1),(.seeLab 8 0 10 9992 1),(.seeLive 8 0 9992 2),(.seeLab 8 0 9 9992 2),(.seeLab 8 0 10 9992 2),(.seeLive 8 0 9992 3),(.exactAt 8 6 9992),(.seeLab 8 6 9 9992 0),(.seeLab 8 6 10 9992 0),(.seeLab 8 6 9 9992 1),(.seeLab 8 6 10 9992 1),(.seeLive 8 6 9992 2),(.seeLab 8 6 9 9992 2),(.seeLab 8 6 10 9992 2),(.seeLive 8 6 9992 3),(.diffC 0 8 9),(.diffC 1 8 9),(.adjacentCommon 8 9 6),(.residual 8 9 0 1),(.residual 8 9 0 2),(.residual 8 9 1 2),(.diffX 0 8 10),(.diffC 0 8 10),(.diffX 1 8 10),(.diffC 1 8 10),(.adjacentCommon 8 10 0),(.residual 8 10 0 1),(.residual 8 10 0 2),(.residual 8 10 1 2),(.earlier 9 1),(.earlier 9 2),(.allRes 9 0),(.allRes 9 1),(.exposure 9 432),(.avoidNot 9 7 432 0),(.avoidNot 9 8 432 0),(.avoidNot 9 7 432 1),(.avoidNot 9 8 432 1),(.avoidLive 9 432 2),(.avoidNot 9 7 432 2),(.avoidNot 9 8 432 2),(.avoidLive 9 432 3),(.avoidNot 9 8 432 3),(.exposure 9 1290),(.avoidNot 9 8 1290 0),(.avoidNot 9 10 1290 0),(.avoidNot 9 8 1290 1),(.avoidNot 9 8 1290 2),(.avoidNot 9 10 1290 2),(.avoidLive 9 1290 3),(.avoidNot 9 10 1290 3),(.exposure 9 8488),(.avoidNot 9 8 8488 0),(.avoidNot 9 13 8488 1),(.avoidNot 9 8 8488 2),(.avoidNot 9 8 8488 3),(.exactAt 9 1 5008),(.seeLab 9 1 7 5008 0),(.seeLab 9 1 8 5008 1),(.seeLive 9 1 5008 2),(.seeLive 9 1 5008 3),(.exactAt 9 1 16256),(.seeLab 9 1 7 16256 0),(.seeLab 9 1 8 16256 0),(.seeLab 9 1 10 16256 0),(.seeLive 9 1 16256 1),(.seeLab 9 1 7 16256 1),(.seeLab 9 1 8 16256 1),(.seeLab 9 1 10 16256 1),(.seeLab 9 1 13 16256 1),(.seeLive 9 1 16256 2),(.seeLab 9 1 7 16256 2),(.seeLab 9 1 8 16256 2),(.seeLab 9 1 10 16256 2),(.seeLive 9 1 16256 3),(.seeLab 9 1 8 16256 3),(.exactAt 9 5 9992),(.seeLab 9 5 8 9992 0),(.seeLab 9 5 8 9992 1),(.seeLab 9 5 8 9992 2),(.seeLab 9 5 10 9992 3),(.exactAt 9 6 792),(.seeLab 9 6 8 792 0),(.seeLab 9 6 8 792 1),(.seeLive 9 6 792 2),(.seeLab 9 6 8 792 2),(.seeLive 9 6 792 3),(.exactAt 9 6 9992),(.seeLab 9 6 8 9992 0),(.seeLab 9 6 10 9992 0),(.seeLab 9 6 8 9992 1),(.seeLab 9 6 8 9992 2),(.seeLab 9 6 10 9992 2),(.seeLive 9 6 9992 3),(.exactAt 9 6 16256),(.seeLab 9 6 8 16256 0),(.seeLab 9 6 10 16256 1),(.seeLab 9 6 8 16256 2),(.seeLive 9 6 16256 3),(.diffX 0 9 8),(.diffC 0 9 8),(.diffX 1 9 8),(.diffC 1 9 8),(.residual 9 8 0 1),(.residual 9 8 0 2),(.residual 9 8 0 3),(.residual 9 8 1 2),(.residual 9 8 1 3),(.residual 9 8 2 3),(.diffX 0 9 10),(.diffC 0 9 10),(.diffX 1 9 10),(.diffC 1 9 10),(.adjacentCommon 9 10 5),(.residual 9 10 0 1),(.residual 9 10 0 2),(.residual 9 10 1 2),(.someRes 10),(.allRes 10 0),(.allRes 10 1),(.readerAny false 1),(.readerLab false 1 0 0 true),(.readerLab false 1 0 4 false),(.readerAny false 10),(.readerLab false 10 0 4 true),(.readerLab false 10 1 4 true),(.readerLab false 10 2 4 true),(.readerLab false 10 3 4 true),(.readerAny false 14),(.readerLab false 14 0 0 false),(.readerLab false 14 0 4 false),(.readerAny true 1),(.readerLive true 1 2),(.readerLive true 1 3),(.readerAny true 10),(.readerLive true 10 2),(.readerLive true 10 3),(.readerAny true 14),(.readerLive true 14 2),(.readerLive true 14 3),(.eqLab false 1 10 4 false),(.gateEq true 1 10 0),(.gateEq true 1 10 1),(.eqLab false 1 14 0 true),(.gateEq true 1 14 0),(.gateEq true 1 14 1),(.eqLab false 10 14 4 true),(.gateEq true 10 14 0),(.gateEq true 10 14 1)]

def table103_0 : List Nat := [65,321,0x10102,0x4c1,0x541,0x5c1,0x641,0x7c1,0xd0782,0xe0782,0x108a82,0x38c02,0x48c02,0x7a3b1c8dc4,0x110d82,0x130d82]
def table103_1 : List Nat := [0x108e02,0x160e02,0x170e02,0x158e82,0x190e82,0x1a0e82,0x188f02,0x8a43208fc4,0x138f82,0x179002,0x159082,0x189102,0x9a4b2491c4,0x111182,0x139182,0x161202]
def table103_2 : List Nat := [0x179202,0x159282,0x191282,0x1a9282,0x189302,0xaa532893c4,0x119382,0x131382,0x169402,0x171402,0x159482,0x199482,0x1a1482,0x189502,0x51582,0x61602]
def table103_3 : List Nat := [0x941,0x2c95c5a23100906,0x2c95c6623150906,0x2c95c662d150906,0x39682,0x71682,0x49702,0x81702,0xa41,0x2e96c5e27100a06,0x2e96c6a27150a06,0x2e96c6a2f150a06,0x2f9a02,0x349c82,0x59c82,0x69c82]
def table103_4 : List Nat := [0x10a83409fc4,0x301f82,0x311f82,0x352002,0x362002,0x34a082,0x3a2082,0x3b2082,0x39a102,0x3d2102,0x11a8b44a1c4,0x312182,0x322182,0x362202,0x3b2282,0x3c2282]
def table103_5 : List Nat := [0x39a302,0x3e2302,0x12a9348a3c4,0x312382,0x382402,0x3b2482,0x3d2502,0x13a9b4ca5c4,0x30a582,0x362602,0x34a682,0x39a702,0x14aa350a7c4,0x30a782,0x312782,0x322782]
def table103_6 : List Nat := [0x2fa802,0x35a802,0x362802,0x372802,0x38a802,0x34a882,0x3aa882,0x3b2882,0x3c2882,0x39a902,0x3d2902,0x15aab54a9c4,0x312982,0x362a02,0x3b2a82,0x3eab02]
def table103_7 : List Nat := [0x16ab358abc4,0x31ab82,0x36ac02,0x34ac82,0x3bac82,0x39ad02,0x17abb5cadc4,0x31ad82,0x322d82,0x36ae02,0x3bae82,0x3c2e82,0x39af02,0x18ac360afc4,0x31af82,0x373002]
def table103_8 : List Nat := [0x3bb082,0x39b102,0x5b182,0x33182,0x6b202,0x43202,0x64b1cda632f0906,0x64b1cee63340906,0x64b1cf663390906,0x64b1cee6d340906,0x64b1cf66d390906,0x64b1cf677390906,0x5b282,0x73282,0x6b302,0x83302]
def table103_9 : List Nat := [0x19c1,0x66b2cde652f1986,0x66b2cf265341986,0x66b2cf26f341986,0x1107b383,0x7b402,0x8b402,0x34c1,0xd5003483,0xd601b483,0x1bedd6db644,0xe1093603,0xe10a3683,0xe10b3703,0xe10c3783,0x38c1]
def table103_10 : List Nat := [0xe40db883,0xe60eb883,0x1deed75ba44,0x67bb02,0x68bb82,0x1eef579bc44,0x67bd02,0x68bd82,0x1fefd7dbe44,0x67bf02,0x68bf82,0xe06bc003,0x101783a03,0x101793a83,0xe56a4083,0x1037c3a03]
def table103_11 : List Nat := [0x1037d3a83,0xe7704103,0x1057c3c03,0x1057d3c83,129,0x681,0x701,0x164ae2d118805,0x164ae33118a85,0x164ae33168a85,0x174b62f138805,0x174b635138a85,0x174b635178a85,0x3258e6d319785,0x3258e77319a05,0x3258e7b319c85]
def table103_12 : List Nat := [0x3258e77369a05,0x3258e7b369c85,0x3258e7b3b9c85,0x335966f329785,0x3359679329a05,0x3359679379a05,0x3541,0x3581,0x70b602,0x70b682,0x70b702,0x70b782,0x3901,0x3981,0x704002,0x4081]
def table103_13 : List Nat := [0x7c3a02,0x7d3a82,0x704102,0x3841,0x4001,0x4101,0x76311b03,0x3931d9276509886,0x1c98ec93b2845,0xe4c7649d84,0x73361883,0x2154a83519885,0x5d038e83,0xba07150d44,0xf4aa3b298b85,0x5d038a83]
def table103_14 : List Nat := [0x2e81c2,0xaec8248e04,0xaec81d8bc4,0x57640ec3,0x2bb202,0xd167be83,0x68b3c2,0x31110b03,0xb2c6150884,0x59630a83,0x2cb182,0x188ac2,0x2d974aa2a288bc6,0x5b2e8f4aa2a1d8b87,0x2d9747a55150ec6,0x1747a552d8a85]
def table103_15 : List Nat := [0x2f572cd65a885,0x8552af4c4b966b2c7,0xdac764a084,0x42a94c46d63b246,0xce42a957a62369747,0x1c81,0x2101,0x2301,0x2701,0x2901,0x2d01,0x2f01,0x3101,0x361d82,0x361a42,0x363202]
def table103_16 : List Nat := [0x1b01,0x2c01,0x2e01,0x313182,0x3131c2,0x1881,0x2b81,0x2d81,0x2cc1,0x2ec1,0x1a41,0x1dc1,0x1e01,0x17c1,0x2881,0x65b342]
def table103_17 : List Nat := [0x3201,0x31c1,385,0x1641,0x1741,769,0x401,0x3301,0x3401,0x32c1,0x33c1,897]

def encoded103 (i : Nat) : Nat :=
  if i < 144 then
    if i < 64 then
      if i < 32 then
        if i < 16 then
          table103_0.getD (i%16) 0
        else
          table103_1.getD (i%16) 0
      else
        if i < 48 then
          table103_2.getD (i%16) 0
        else
          table103_3.getD (i%16) 0
    else
      if i < 96 then
        if i < 80 then
          table103_4.getD (i%16) 0
        else
          table103_5.getD (i%16) 0
      else
        if i < 112 then
          table103_6.getD (i%16) 0
        else
          if i < 128 then
            table103_7.getD (i%16) 0
          else
            table103_8.getD (i%16) 0
  else
    if i < 208 then
      if i < 176 then
        if i < 160 then
          table103_9.getD (i%16) 0
        else
          table103_10.getD (i%16) 0
      else
        if i < 192 then
          table103_11.getD (i%16) 0
        else
          table103_12.getD (i%16) 0
    else
      if i < 240 then
        if i < 224 then
          table103_13.getD (i%16) 0
        else
          table103_14.getD (i%16) 0
      else
        if i < 256 then
          table103_15.getD (i%16) 0
        else
          if i < 272 then
            table103_16.getD (i%16) 0
          else
            table103_17.getD (i%16) 0
def book103 (i : Nat) : Clause := let n := encoded103 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses103 : inputsOK 2 103 a103 r103 (baseBook book103 180).toList=true := by decide +kernel

def rows103_0 : List Nat := [0x40401,0x1c1001,0x1c1201,0xc06201,0xc06401,0xc06601,0xe07201,0xe07401,0xe07601,0xc10c01,0xc10e01,0xc11001,0xc11201,0xc11401,0xc11601,0x2412201,0x2412401,0x2412601,0x25d3002,0x5a25d3202,0xd3601,0x113801,0x153a01,0x193c01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk103_0 : checkRows book103 9 180 rows103_0=true := by decide +kernel

def rows103_1 : List Nat := [0x5aa7d4002,0x5b27d4202,0x31d5601,0x663195c02,0x33d5e01,0x33d6001,0x3356201,0x196ca64b213404,0x34d9c01,0x34da401,0x144d64a369349c6e259b0de09,0x358d45c2f19d8205,0x104b8403512488bf5eb5c783d2399cba0d,0x562995182bd32189b0551e0f4a40b,0x118b8402f108906922188cc09,0x10cb8402f108c205,0x2714aed782b0a85026341682c4a0b,0x1e125daf0681605b701a08,0x384a0d148484c05,0x11128344e0f5d37858dd050d02c2d05b70500f,0x444a0d1383c30170cb78541a6fb705a1b0b02c5011,0x44210e0756e11080bd082406215720c,0x220d0702e1e0c03c1c0d70880322f420583624062157013,0x38b70f088140f070ac540d6f049c42f42058482d062143e14]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk103_1 : checkRows book103 9 204 rows103_1=true := by decide +kernel

def rows103_2 : List Nat := [0xe87c46b85c854281371890182f42a10380e,0x52a8966d15229d46a66a355580a,0x52a8964d05439552a651a914eaa6a3555a0e,0x54380d0f8442c24070744609,0x120e03444145cb9c3a0e172082c2405a0c400f,0x3c380d0f84444145bae1d00a172082c2405a0c3c11,0x88941a27078602e196f0a83413748b4361605a0c5012,0x11128344e0f0c05c32de1506826160d8b4500f,0x9c58ba5e0284a05,0x3c580d6f0497605,0xd1403dd8ba768282207,0x52275e2ec56150a3b84a08,0x3b310f46833994f006,0x301e0ec7a3191cb8db78179860a,0x239158002,0xce656dbc98004,0x11e3578bbd18eb168585c0c72215e683701e52810,0x8c5c20188885e211a892c05f309b2ea720bc5c3f1f0f4cc14,0x3d49001,0x3d4a001,0x3d4b601,0x3d4d201,0x3d4ea01,0x3d4f801]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk103_2 : checkRows book103 9 228 rows103_2=true := by decide +kernel

def rows103_3 : List Nat := [0x3d50201,0x104b8403391c88627cbd8ba09,0x104ae402d11488597c3d8b009,0x4c27b0d8a8f4a3992a3577a31d62d0b0b86c0c722149a7f3ea01fa7e6d0f1fcf77e3d4941f,0x984f61b151a94732591c3717b81d4835f3fc78fe3f9f500fd3f3689af77e3d4941c,0x400e401,0x400f201,0x46b99e296470dc5ee07520e04fb7cbd9280e,0x35733bde8eb168586c0c42bcdecf97dc012a0f,0x40e0801,0x414e201,0x414ee01,0xfa80c18e003,0xfb8141cec03,0x420e601,0x420e801,0x424f601,0x4287801,0x42cce01,0xbe6362316190a7cc38b808,0x8f4a3992a3577a31d62d0b0b86c0c722161e0f,0x2010d82c417a04,0x4450601,0x445d401]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk103_3 : checkRows book103 9 252 rows103_3=true := by decide +kernel

def rows103_4 : List Nat := [0x449c001,0x44c5e01,0x4506e01,0x4551c01,0x4592c01,0x45e1e01,0x461cc01,0x4651a01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk103_4 : checkRows book103 9 276 rows103_4=true := by decide +kernel

def lastUnits103 := digits 9 3 0x45a371a
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict103 : checkReasons book103 284 148 lastUnits103 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude103 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 103=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=2) h hc bp eq (by decide +kernel)
  let v := truth Z a103
  have hbase : ValidThrough v book103 180 := book_start Z h hc z eq _ _ _ _ initialClauses103
  have h0 : ValidThrough v book103 204 := rows_sound hbase rows103_0 rowsOk103_0
  have h1 : ValidThrough v book103 228 := rows_sound h0 rows103_1 rowsOk103_1
  have h2 : ValidThrough v book103 252 := rows_sound h1 rows103_2 rowsOk103_2
  have h3 : ValidThrough v book103 276 := rows_sound h2 rows103_3 rowsOk103_3
  have h4 : ValidThrough v book103 284 := rows_sound h3 rows103_4 rowsOk103_4
  exact book_end h4 _ _ conflict103
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
