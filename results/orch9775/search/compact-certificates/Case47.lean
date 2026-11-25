import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a47 : Array Fact := #[(.lab 0 0 0),(.lab 0 0 6),(.avoid 0 1102 0),(.res 0 8),(.res 1 8),(.res 0 9),(.res 1 9),(.res 0 10),(.res 1 10),(.lab 2 0 0),(.lab 2 0 6),(.avoid 2 8297 0),(.lab 6 0 6),(.lab 6 1 6),(.lab 6 2 6),(.lab 6 3 6),(.lab 8 0 8),(.live 8 1),(.lab 8 0 9),(.common 8 9),(.lab 8 0 10),(.common 8 10),(.lab 8 0 13),(.lab 8 1 8),(.live 8 2),(.lab 8 1 9),(.lab 8 1 10),(.lab 8 1 13),(.lab 8 2 8),(.live 8 3),(.lab 8 2 9),(.lab 8 2 10),(.lab 8 2 13),(.lab 8 3 10),(.lab 8 3 13),(.avoid 8 1548 0),(.avoid 8 1548 1),(.avoid 8 1548 2),(.avoid 8 1548 3),(.avoid 8 9288 0),(.avoid 8 9288 1),(.avoid 8 9288 2),(.avoid 8 9288 3),(.see 8 0 9992 0),(.see 8 0 9992 1),(.see 8 0 9992 2),(.see 8 0 9992 3),(.see 8 2 9992 0),(.see 8 2 9992 1),(.see 8 2 9992 2),(.see 8 2 9992 3),(.diff 0 8 9),(.diff 1 8 9),(.diff 0 8 10),(.diff 1 8 10),(.lab 9 0 7),(.common 9 10),(.lab 9 0 12),(.live 9 2),(.lab 9 1 7),(.lab 9 1 12),(.live 9 3),(.avoid 9 4309 0),(.avoid 9 4309 1),(.avoid 9 4309 2),(.avoid 9 4309 3),(.see 9 1 4757 0),(.see 9 1 4757 1),(.see 9 1 4757 2),(.see 9 1 4757 3),(.see 9 5 4757 0),(.see 9 5 4757 1),(.see 9 5 4757 2),(.see 9 5 4757 3),(.live 10 1),(.lab 10 0 8),(.lab 10 0 9),(.lab 10 0 12),(.live 10 2),(.lab 10 1 8),(.lab 10 1 9),(.lab 10 1 12),(.lab 10 2 10),(.live 10 3),(.lab 10 2 8),(.lab 10 2 9),(.lab 10 2 12),(.avoid 10 792 0),(.avoid 10 792 1),(.avoid 10 792 2),(.avoid 10 792 3),(.avoid 10 4370 0),(.avoid 10 4370 1),(.avoid 10 4370 2),(.avoid 10 4370 3),(.see 10 0 1290 0),(.see 10 0 1290 1),(.see 10 0 1290 2),(.see 10 0 1290 3),(.see 10 0 9992 0),(.see 10 0 9992 1),(.see 10 0 9992 2),(.see 10 0 9992 3),(.see 10 5 7426 0),(.see 10 5 7426 1),(.see 10 5 7426 2),(.see 10 5 7426 3),(.see 10 5 9992 0),(.see 10 5 9992 1),(.see 10 5 9992 2),(.see 10 5 9992 3),(.diff 0 10 8),(.diff 1 10 8),(.diff 0 10 9),(.diff 1 10 9),(.reader false 0 0),(.es false 0 0),(.es false 0 6),(.reader false 1 0),(.reader false 5 0),(.es false 5 0),(.es false 5 6),(.reader false 16 0),(.reader false 16 1),(.reader false 16 2),(.reader false 16 3),(.es false 16 6),(.reader true 0 0),(.reader true 0 1),(.reader true 0 2),(.reader true 0 3),(.es true 0 8),(.es true 0 9),(.es true 0 10),(.reader true 1 0),(.reader true 1 1),(.reader true 1 2),(.reader true 1 3),(.es true 1 8),(.es true 1 9),(.es true 1 10),(.reader true 5 0),(.reader true 5 1),(.reader true 5 2),(.reader true 5 3),(.reader true 16 0),(.reader true 16 1),(.reader true 16 2),(.reader true 16 3),(.gate 0 1),(.gate 0 5),(.gate 0 16),(.gate 5 16)]
def r47 : List Scheme := [(.self 0 0),(.exposure 0 1102),(.avoidNot 0 6 1102 0),(.exposure 2 8297),(.avoidNot 2 0 8297 0),(.avoidNot 2 6 8297 0),(.self 6 0),(.self 6 1),(.self 6 2),(.self 6 3),(.self 8 0),(.self 8 1),(.earlier 8 1),(.self 8 2),(.earlier 8 2),(.someRes 8),(.allRes 8 0),(.allRes 8 1),(.exposure 8 1548),(.avoidNot 8 9 1548 0),(.avoidNot 8 10 1548 0),(.avoidNot 8 9 1548 1),(.avoidNot 8 10 1548 1),(.avoidNot 8 9 1548 2),(.avoidNot 8 10 1548 2),(.avoidLive 8 1548 3),(.exposure 8 9288),(.avoidNot 8 10 9288 0),(.avoidNot 8 13 9288 0),(.avoidNot 8 10 9288 1),(.avoidNot 8 13 9288 1),(.avoidNot 8 10 9288 2),(.avoidNot 8 13 9288 2),(.avoidLive 8 9288 3),(.avoidNot 8 10 9288 3),(.avoidNot 8 13 9288 3),(.exactAt 8 0 9992),(.seeLab 8 0 9 9992 0),(.seeLab 8 0 10 9992 0),(.seeLab 8 0 9 9992 1),(.seeLab 8 0 10 9992 1),(.seeLab 8 0 9 9992 2),(.seeLab 8 0 10 9992 2),(.seeLive 8 0 9992 3),(.exactAt 8 2 9992),(.seeLab 8 2 10 9992 0),(.seeLab 8 2 13 9992 0),(.seeLab 8 2 10 9992 1),(.seeLab 8 2 13 9992 1),(.seeLab 8 2 10 9992 2),(.seeLab 8 2 13 9992 2),(.seeLive 8 2 9992 3),(.seeLab 8 2 10 9992 3),(.seeLab 8 2 13 9992 3),(.diffX 0 8 9),(.diffC 0 8 9),(.resCommon 8 9 0),(.diffX 1 8 9),(.diffC 1 8 9),(.resCommon 8 9 1),(.residual 8 9 0 1),(.residual 8 9 0 2),(.residual 8 9 1 2),(.diffX 0 8 10),(.diffC 0 8 10),(.diffX 1 8 10),(.diffC 1 8 10),(.adjacentCommon 8 10 0),(.residual 8 10 0 1),(.residual 8 10 0 2),(.residual 8 10 0 3),(.residual 8 10 1 2),(.residual 8 10 1 3),(.residual 8 10 2 3),(.someRes 9),(.allRes 9 0),(.allRes 9 1),(.exposure 9 4309),(.avoidNot 9 7 4309 0),(.avoidNot 9 12 4309 0),(.avoidNot 9 7 4309 1),(.avoidNot 9 12 4309 1),(.avoidLive 9 4309 2),(.avoidLive 9 4309 3),(.exactAt 9 1 4757),(.seeLab 9 1 7 4757 0),(.seeLab 9 1 7 4757 1),(.seeLive 9 1 4757 2),(.seeLive 9 1 4757 3),(.exactAt 9 5 4757),(.seeLab 9 5 7 4757 0),(.seeLab 9 5 12 4757 0),(.seeLab 9 5 7 4757 1),(.seeLab 9 5 12 4757 1),(.seeLive 9 5 4757 2),(.seeLive 9 5 4757 3),(.adjacentCommon 9 10 5),(.earlier 10 1),(.self 10 2),(.allRes 10 0),(.allRes 10 1),(.exposure 10 792),(.avoidNot 10 8 792 0),(.avoidNot 10 9 792 0),(.avoidNot 10 8 792 1),(.avoidNot 10 9 792 1),(.avoidLive 10 792 2),(.avoidNot 10 8 792 2),(.avoidNot 10 9 792 2),(.avoidLive 10 792 3),(.exposure 10 4370),(.avoidNot 10 8 4370 0),(.avoidNot 10 12 4370 0),(.avoidNot 10 8 4370 1),(.avoidNot 10 12 4370 1),(.avoidNot 10 8 4370 2),(.avoidNot 10 12 4370 2),(.avoidLive 10 4370 3),(.exactAt 10 0 1290),(.seeLab 10 0 8 1290 0),(.seeLab 10 0 8 1290 1),(.seeLive 10 0 1290 2),(.seeLab 10 0 8 1290 2),(.seeLive 10 0 1290 3),(.exactAt 10 0 9992),(.seeLab 10 0 8 9992 0),(.seeLab 10 0 9 9992 0),(.seeLab 10 0 8 9992 1),(.seeLab 10 0 9 9992 1),(.seeLab 10 0 8 9992 2),(.seeLive 10 0 9992 3),(.exactAt 10 5 7426),(.seeLab 10 5 8 7426 0),(.seeLab 10 5 12 7426 0),(.seeLab 10 5 8 7426 1),(.seeLab 10 5 12 7426 1),(.seeLab 10 5 8 7426 2),(.seeLab 10 5 12 7426 2),(.seeLive 10 5 7426 3),(.exactAt 10 5 9992),(.seeLab 10 5 8 9992 0),(.seeLab 10 5 9 9992 0),(.seeLab 10 5 8 9992 1),(.seeLab 10 5 9 9992 1),(.seeLive 10 5 9992 2),(.seeLive 10 5 9992 3),(.diffC 0 10 8),(.diffC 1 10 8),(.residual 10 8 0 1),(.residual 10 8 0 2),(.residual 10 8 1 2),(.diffX 0 10 9),(.diffC 0 10 9),(.diffX 1 10 9),(.diffC 1 10 9),(.residual 10 9 0 1),(.residual 10 9 0 2),(.residual 10 9 1 2),(.readerAny false 0),(.readerLab false 0 0 0 true),(.readerLab false 0 0 6 false),(.readerAny false 1),(.readerAny false 5),(.readerLab false 5 0 0 false),(.readerLab false 5 0 6 false),(.readerAny false 16),(.readerLab false 16 0 6 true),(.readerLab false 16 1 6 true),(.readerLab false 16 2 6 true),(.readerLab false 16 3 6 true),(.readerAny true 0),(.readerLab true 0 0 8 true),(.readerLab true 0 0 9 false),(.readerLab true 0 0 10 false),(.readerLab true 0 1 8 true),(.readerLab true 0 1 9 false),(.readerLab true 0 1 10 false),(.readerLive true 0 2),(.readerLab true 0 2 8 true),(.readerLab true 0 2 9 false),(.readerLab true 0 2 10 false),(.readerLive true 0 3),(.readerAny true 1),(.readerLab true 1 0 8 false),(.readerLab true 1 1 8 false),(.readerLab true 1 2 9 true),(.readerLab true 1 2 10 true),(.readerLive true 1 3),(.readerAny true 5),(.readerLive true 5 2),(.readerLive true 5 3),(.readerAny true 16),(.readerLive true 16 2),(.readerLive true 16 3),(.gateEq false 0 1 0),(.eqLab true 0 1 8 true),(.eqLab true 0 1 9 false),(.eqLab true 0 1 10 false),(.eqLab false 0 5 0 true),(.gateEq true 0 5 0),(.gateEq true 0 5 1),(.eqLab false 0 16 6 false),(.gateEq true 0 16 0),(.gateEq true 0 16 1),(.eqLab false 5 16 6 false),(.gateEq true 5 16 0),(.gateEq true 5 16 1)]

def table47_0 : List Nat := [65,321,0x10102,0x5c1,0x90582,0xa0582,0x641,0x6c1,0x741,0x7c1,0x841,0xbc1,0x118c02,0xe41,0x188e82,0x9038c03]
def table47_1 : List Nat := [0x38e82,0x48e82,0x9a4b2491c4,0x121182,0x141182,0x191202,0x1a1202,0x1e1282,0x1f1282,0x1d9302,0xaa532893c4,0x141382,0x161382,0x1a1402,0x1b1402,0x1f1482]
def table47_2 : List Nat := [0x201482,0x1d9502,0x211502,0x221502,0xba5b2c95c4,0x121582,0x149582,0x191602,0x1a9602,0x1e1682,0x1f9682,0x1d9702,0xca633097c4,0x141782,0x169782,0x1a1802]
def table47_3 : List Nat := [0x1b9802,0x1f1882,0x209882,0x1d9902,0x211902,0x229902,0x39982,0x51982,0x27050183,0x49a02,0x61a02,0x27060203,0x3499c6625110986,0x3499c7a25180986,0x3499c7a33180986,0x39a82]
def table47_4 : List Nat := [0x71a82,0x49b02,0x81b02,0xac1,0x369ac6a29110a86,0x369ac7e29180a86,0x369ac86291d0a86,0x369ac7e35180a86,0x369ac86351d0a86,0x369ac863f1d0a86,0xd059d03,0x59e82,0x69e82,0x106813f9f44,0x371f02,0x391f02]
def table47_5 : List Nat := [0x3b1f82,0x3c1f82,0x3aa002,0x3da082,0x1168943a144,0x37a102,0x3ba182,0x3aa202,0x3da282,0x1269147a344,0x372302,0x39a302,0x3b2382,0x3ca382,0x3aa402,0x3da482]
def table47_6 : List Nat := [0x1c41,0x4aa702,0x2941,0x7a982,0x8a982,0x16ab358abc4,0x4b2b82,0x4c2b82,0x4f2c02,0x502c02,0x4eac82,0x542c82,0x552c82,0x53ad02,0x17abb5cadc4,0x4b2d82]
def table47_7 : List Nat := [0x4d2d82,0x4f2e02,0x512e02,0x542e82,0x562e82,0x53af02,0x18ac360afc4,0x4baf82,0x4fb002,0x4eb082,0x54b082,0x53b102,0x19acb64b1c4,0x4bb182,0x4c3182,0x4fb202]
def table47_8 : List Nat := [0x503202,0x54b282,0x53b302,0x1aad368b3c4,0x4b3382,0x4db382,0x4f3402,0x51b402,0x543482,0x56b482,0x53b502,0x1badb6cb5c4,0x4b3582,0x4cb582,0x4f3602,0x50b602]
def table47_9 : List Nat := [0x4eb682,0x53b702,0x33782,0x43802,0x70b7d3e974a0a86,0x70b7d52974e0a86,0x70b7d529f4e0a86,0x7b882,0x53882,0x8b902,0x63902,0x72b8d42994a1c06,0x72b8d56994e1c06,0x72b8d56a14e1c06,0x39c1,0xe9003983]
def table47_10 : List Nat := [0xea01b983,0x3b41,0x3bc1,0xf009bb83,0xf20abb83,0x1f6f97bbd44,0xfd0c3d03,0xfd0d3d83,0xfd0e3e03,0xfd0f3e83,0x20b0380bfc4,0x107103f83,0x10812bf83,0x10a14bf83,0x107174003,0x10819c003]
def table47_11 : List Nat := [0x10a1ac003,0x18c082,0x1071c4083,0x1081ec083,0x10a1fc083,0x1dc102,0x2271187c344,0x1144bc303,0x1144fc383,0x117554403,0x119524403,0x53c482,0x2431f8ec6c4,0x18c782,0x1dc802,0x2532792c8c4]
def table47_12 : List Nat := [0x18c982,0x1dca02,0x12b763983,0x115834a83,0x11684ca83,0x11885ca83,0xf1744b03,0x12d8d3f83,0x12d8e4003,0xfc75cb83,0x12f913f83,0x12f924003,0xfc79cc03,0x131914683,0x131924703,129]
def table47_13 : List Nat := [0x481,0x501,0x1b4d635148885,0x1b4d63f148c05,0x1b4d643148e85,0x1b4d63f1a8c05,0x1b4d6431a8e85,0x1b4d6431f8e85,0x385be9f4ba505,0x385bea94ba705,0x385bea94fa705,0x395c6a14ca505,0x395c6ab4ca705,0x395c6ab50a705,0x3a41,0x3a81]
def table47_14 : List Nat := [0x3c01,0x3c81,0x7ebd02,0x7ebd82,0x7ebe02,0x7ebe82,0x83bf82,0x83c002,0x83c082,0x8cc402,0x4ac1,0x8ac182,0x8b4242,0x8c42c2,0x4b01,0x8d3f82]
def table47_15 : List Nat := [0x8e4002,0x7e4b82,0x7e4c02,0x3f41,0x4b81,0x4c01,0x7b3aa383,0x3d9d42,0x74a6299904,0x894c63329385,0x894c63329405,0x3a530f83,0x1d2982,0xc0da6b329485,0x181b4d6532a8fc6,0x194a655318d05]
def table47_16 : List Nat := [0xc0da6b329545,0xa74f2583,0xa74f2743,0x1d2782,0x1d25c2,0x1d2742,0xe81,0x1301,0x1501,0x1701,0x1901,0x4101,0x4801,0x4a01,0x18bf82,0xc41]
def table47_17 : List Nat := [0x8c1,0x1a0f82,0x4e2640f10800cc6,0x2713207884005,0x9c4c81e20fe2c9287,0x9c4c81e20fe198947,0x140f82,0x4e2640f107f1646,0x2713207883f85,0x1389903c404,0x27d2f1189c505,0x41c1,0x4541,0x4e26620097f0946,0x271331004bf85,0x4e2662009239606]
def table47_18 : List Nat := [0x4e26620092b91c6,0x4e2662009129686,0x27133100495c5,0x13899880244,0x1a0a02,0x2981,0x2d01,0x2f01,0x3101,0x3301,0x3501,0x3701,0x9c574403,0x4481,0x4f2a02,0xce69130d04]
def table47_19 : List Nat := [0xce69131684,0x69338983,0x9c570203,0x4e2b82,0x271c6e54baa45,0x10a841583,0x215087f8d44,0x10a843fc3,0x854202,0x138e372a5c4,0x4b2a02,0x9c138243,0x4e09c2,0x9c332583,0x4e1982,0x4e25c2]
def table47_20 : List Nat := [0x2701,0x2c81,0x3081,0x3681,0x2781,0x3001,0x2fc1,0x25c1,0x2b81,0x3581,0x2c41,0x3641,0x2801]

def encoded47 (i : Nat) : Nat :=
  if i < 160 then
    if i < 80 then
      if i < 32 then
        if i < 16 then
          table47_0.getD (i%16) 0
        else
          table47_1.getD (i%16) 0
      else
        if i < 48 then
          table47_2.getD (i%16) 0
        else
          if i < 64 then
            table47_3.getD (i%16) 0
          else
            table47_4.getD (i%16) 0
    else
      if i < 112 then
        if i < 96 then
          table47_5.getD (i%16) 0
        else
          table47_6.getD (i%16) 0
      else
        if i < 128 then
          table47_7.getD (i%16) 0
        else
          if i < 144 then
            table47_8.getD (i%16) 0
          else
            table47_9.getD (i%16) 0
  else
    if i < 240 then
      if i < 192 then
        if i < 176 then
          table47_10.getD (i%16) 0
        else
          table47_11.getD (i%16) 0
      else
        if i < 208 then
          table47_12.getD (i%16) 0
        else
          if i < 224 then
            table47_13.getD (i%16) 0
          else
            table47_14.getD (i%16) 0
    else
      if i < 288 then
        if i < 256 then
          table47_15.getD (i%16) 0
        else
          if i < 272 then
            table47_16.getD (i%16) 0
          else
            table47_17.getD (i%16) 0
      else
        if i < 304 then
          table47_18.getD (i%16) 0
        else
          if i < 320 then
            table47_19.getD (i%16) 0
          else
            table47_20.getD (i%16) 0
def book47 (i : Nat) : Clause := let n := encoded47 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses47 : inputsOK 2 47 a47 r47 (baseBook book47 207).toList=true := by decide +kernel

def rows47_0 : List Nat := [0x40401,0xc0801,0xc0a01,0x10c8801,0x10c8a01,0x10c8c01,0x10c8e01,0x10c9001,0x10c9201,0x10d2801,0x10d2a01,0x10d2c01,0x1813601,0x1813801,0x1813a01,0x2793e02,0x67a794002,0x682894602,0x68a894802,0x194c01,0x1d4e01,0x215001,0x255201,0x295601]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk47_0 : checkRows book47 9 207 rows47_0=true := by decide +kernel

def rows47_1 : List Nat := [0x2d5c01,0x356401,0x1897401,0x50a798402,0x3a98601,0x3a98801,0x3a98a01,0x703798c02,0x3b98e01,0x3b99001,0x37d9201,0x3859801,0x1cae471b894a04,0x3cde201,0x3cde401,0x5526950a2562e970a6582915c9c0b,0x56269509e552d968b2f62f15ca4532c17ca00f,0x1d0d88dacd41a8d0806321190340b,0xbc5cd20e06c8063211905809,0xb460d20f0748063211905809,0xbc5ad66a08834fa7cbe0621f060388063211905811,0x100b0342d0d8bc3a341134daad77d9088064318386412,0x2d178c9a6d51007c5807,0x361d69b543404]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk47_1 : checkRows book47 9 231 rows47_1=true := by decide +kernel

def rows47_2 : List Nat := [0x70581a178745c05,0x1e160685a1b693fc62fe063f4600b,0x1d1066e421bcea8a38a191209,0x19d1665481a8da91342391a09,0x1c1066e441cdb30280a18e2920824c2275453f10a11,0xc2766c1dd241049844f6fc3c40cf20c,0x6945995206a36a45f866464111e0b,0x3920cdc8839b6a0a8437c12068a3abf12692088410e12,0x4183201,0x4184201,0x4185601,0x4186601,0x4196a01,0x4197c01,0x4198201,0x5faf194ef5eb01eb0d863d19c0a,0x5faf196f05543980bd58bd61b0c7a42d9a0e,0x43c1801,0x621f84429fe04,0x5c263e1e0ec744a7b92d30dc5cbb15e3607a6485001f85960ed74c1e1f1085420241d,0x20160685a1b130904f12154445e1d583b5d30a844246413,0xec744a7b92d30dc5cbb15825120a830171b03d3242800fe1f09854207a19,0x763a253dc96986e2e5d8ac1b03d3242800fe210a8443c7814,0x78581a1887c362d854206009]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk47_2 : checkRows book47 9 255 rows47_2=true := by decide +kernel

def rows47_3 : List Nat := [0x544a1212450282a8b2b5dae983c262a0d,0x100b0342f0e8a22e2d0dab5dae985420640e,0x15098f87a3b1d129ee4b4c37172ec598a448261445a22185a2aa311376ba46c0f4c90a003f83c3e130b854202427,0x5bae16c02,0x154e873c2dcc04,0x46dd601,0x542e3c1e8e06e4a7b93134dc5cbb159191ca5c8100208515aed74c1e210f85420241d,0x20160685e1d140904b1d154585a1b56bb5d30a844246413,0x7037253dc989a6e2e5d8af5505d68128885850278cbb5d2394b90200418f43e1707854207c20,0x381b929ee4c4d37172ec59aa82ab009444302a148923f1976ba4729720400831e87c2e0f09854207c23,0x7037253dc989a6e2e5d8b3552c2222a14c65dae91ca5c810020c7a1f0b854207a1c,0x1c0dc94f726269b8b9762bd54b4888a04e249084e411976ba4729720400831e8842e130f854207822,0x20160685e1d582a969161686c4d228f3b5d30a8442c6413,0x80581a1686c3a2f854206409,0x4220190c7088543e0007,0x494da01,0x494ea01,0x494f601,0x4950401,0x4951401,0x4952201,0x3820cdc8839a18e2d96c24e46928c984cc679549d0a12,0x4957601,0x1c1066e441cce2869549d0a09]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk47_3 : checkRows book47 9 279 rows47_3=true := by decide +kernel

def rows47_4 : List Nat := [0x17098f878271209855248885a0f0f88424240f,0x5426181f0f4542983c3c2409,0x150b850783d130944930144be130f8841c240f,0x3b1d129ee4b4c36d3242800fc6c926ca4cc267401f1032e8d4b0fa668442a1f2996c72621f,0x1c0dc94f726269b697204001e411ccc9007c40cba352c3e99ccc618442a1f298e4b6621e,0x656e9a100783e1d9027a999dcfb2694ca0d80f,0x160b492459582612c2d5408,0x52aa122c0513585c256608,0x13aa848b4154466d3585c255e0a,0x502a924595b379ac244808,0xec5cbb5bae934c68cb2e35cd2671c96c9a700f,0x1c9066e441ccde849549d0e09,0x1b0d2dc6d9f8f8819d1fe03394d129ee9725900710007904c333934a64b088543cca1d,0x361a5b8db3f1f1027f9d4067299214007e981c129ee4c1dcecc333934a64b088543cca1e,0x6c34b71b69720400827e499f1b4813fcea026199a486c9a253dc963793422150f94c94ca1f,0x1b2d84990600404bce67a9a253dc96921b8d8c3088543e5c14,0x6cb61243f80109333930a4c7298253dc983a98cfa79088543e5c16,0x6c34b71b699214007e7e491f1b4813fcea033f4c129ee4c498e873319f4f2666193422150f94c94ca23,0x500d401,0x500f201,0x5012001,0x92d020402,0x510f001,0x14294514ec03]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk47_4 : checkRows book47 9 303 rows47_4=true := by decide +kernel

def rows47_5 : List Nat := [0x518ee01,0x51ccc01,0x51d1801,0x126a0d20ca03,0x12ba1d251603,0x528d201]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk47_5 : checkRows book47 9 327 rows47_5=true := by decide +kernel

def lastUnits47 := digits 9 2 0x2994b
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict47 : checkReasons book47 333 143 lastUnits47 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude47 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 47=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=2) h hc bp eq (by decide +kernel)
  let v := truth Z a47
  have hbase : ValidThrough v book47 207 := book_start Z h hc z eq _ _ _ _ initialClauses47
  have h0 : ValidThrough v book47 231 := rows_sound hbase rows47_0 rowsOk47_0
  have h1 : ValidThrough v book47 255 := rows_sound h0 rows47_1 rowsOk47_1
  have h2 : ValidThrough v book47 279 := rows_sound h1 rows47_2 rowsOk47_2
  have h3 : ValidThrough v book47 303 := rows_sound h2 rows47_3 rowsOk47_3
  have h4 : ValidThrough v book47 327 := rows_sound h3 rows47_4 rowsOk47_4
  have h5 : ValidThrough v book47 333 := rows_sound h4 rows47_5 rowsOk47_5
  exact book_end h5 _ _ conflict47
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
