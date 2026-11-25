import CompactFramework

namespace PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
open PEqualNP.Outside.L_meta_9775.UpstreamCore.DagTools PEqualNP.Outside.L_meta_9775.UpstreamCore.Resolution

def a229 : Array Fact := #[(.lab 0 0 0),(.lab 0 0 4),(.avoid 0 314 0),(.res 0 8),(.res 1 8),(.res 0 9),(.res 1 9),(.res 0 10),(.res 1 10),(.lab 2 0 2),(.lab 2 0 0),(.avoid 2 8297 0),(.lab 4 0 4),(.lab 4 1 4),(.lab 4 2 4),(.lab 4 3 4),(.lab 5 0 0),(.lab 5 0 4),(.avoid 5 541 0),(.lab 6 0 0),(.lab 6 0 2),(.avoid 6 541 0),(.lab 8 0 8),(.live 8 1),(.lab 8 0 9),(.common 8 9),(.lab 8 0 10),(.common 8 10),(.lab 8 1 8),(.live 8 2),(.lab 8 1 9),(.lab 8 1 10),(.lab 8 1 11),(.lab 8 2 8),(.live 8 3),(.lab 8 2 9),(.lab 8 2 10),(.lab 8 3 8),(.lab 8 3 9),(.lab 8 3 10),(.avoid 8 1548 0),(.avoid 8 1548 1),(.avoid 8 1548 2),(.avoid 8 1548 3),(.see 8 0 7426 0),(.see 8 0 7426 1),(.see 8 0 7426 2),(.see 8 0 7426 3),(.see 8 0 9992 0),(.see 8 0 9992 1),(.see 8 0 9992 2),(.see 8 0 9992 3),(.see 8 6 9992 0),(.see 8 6 9992 1),(.see 8 6 9992 2),(.see 8 6 9992 3),(.diff 0 8 9),(.diff 1 8 9),(.diff 0 8 10),(.diff 1 8 10),(.lab 9 0 9),(.live 9 1),(.lab 9 0 8),(.lab 9 0 10),(.common 9 10),(.lab 9 0 12),(.lab 9 1 9),(.live 9 2),(.lab 9 1 8),(.lab 9 1 10),(.lab 9 1 12),(.lab 9 2 9),(.live 9 3),(.lab 9 2 8),(.lab 9 2 10),(.lab 9 2 11),(.lab 9 2 12),(.lab 9 3 9),(.avoid 9 4370 0),(.avoid 9 4370 1),(.avoid 9 4370 2),(.avoid 9 4370 3),(.avoid 9 7426 0),(.avoid 9 7426 1),(.avoid 9 7426 2),(.avoid 9 7426 3),(.see 9 5 5008 0),(.see 9 5 5008 1),(.see 9 5 5008 2),(.see 9 5 5008 3),(.see 9 6 792 0),(.see 9 6 792 1),(.see 9 6 792 2),(.see 9 6 792 3),(.see 9 6 7812 0),(.see 9 6 7812 1),(.see 9 6 7812 2),(.see 9 6 7812 3),(.see 9 6 9992 0),(.see 9 6 9992 1),(.see 9 6 9992 2),(.see 9 6 9992 3),(.diff 0 9 8),(.diff 1 9 8),(.diff 0 9 10),(.diff 1 9 10),(.live 10 2),(.live 10 3),(.lab 11 0 11),(.lab 11 1 11),(.lab 11 2 11),(.lab 11 3 11),(.reader false 0 0),(.es false 0 0),(.reader false 1 0),(.es false 1 0),(.es false 1 4),(.reader false 5 0),(.es false 5 0),(.es false 5 2),(.reader false 10 0),(.reader false 10 1),(.reader false 10 2),(.reader false 10 3),(.es false 10 4),(.reader false 14 0),(.es false 14 0),(.es false 14 4),(.reader false 16 0),(.es false 16 0),(.es false 16 2),(.reader false 17 0),(.reader false 18 0),(.reader true 0 0),(.reader true 0 1),(.reader true 0 2),(.reader true 0 3),(.reader true 1 0),(.reader true 1 1),(.reader true 1 2),(.reader true 1 3),(.reader true 5 0),(.reader true 5 1),(.reader true 5 2),(.reader true 5 3),(.reader true 10 0),(.reader true 10 1),(.reader true 10 2),(.reader true 10 3),(.reader true 14 0),(.reader true 14 1),(.reader true 14 2),(.reader true 14 3),(.reader true 16 0),(.reader true 16 1),(.reader true 16 2),(.reader true 16 3),(.es true 16 8),(.es true 16 9),(.es true 16 10),(.es true 16 11),(.reader true 17 0),(.reader true 17 1),(.reader true 17 2),(.reader true 17 3),(.es true 17 8),(.es true 17 9),(.es true 17 10),(.reader true 18 0),(.reader true 18 1),(.reader true 18 2),(.reader true 18 3),(.es true 18 11),(.gate 0 5),(.gate 0 16),(.gate 1 10),(.gate 1 14),(.gate 5 16),(.gate 10 14),(.gate 16 17),(.gate 16 18)]
def r229 : List Scheme := [(.self 0 0),(.exposure 0 314),(.avoidNot 0 4 314 0),(.self 2 0),(.exposure 2 8297),(.avoidNot 2 0 8297 0),(.self 4 0),(.self 4 1),(.self 4 2),(.self 4 3),(.exposure 5 541),(.avoidNot 5 0 541 0),(.avoidNot 5 4 541 0),(.exposure 6 541),(.avoidNot 6 0 541 0),(.avoidNot 6 2 541 0),(.self 8 0),(.self 8 1),(.earlier 8 1),(.self 8 2),(.earlier 8 2),(.self 8 3),(.allRes 8 0),(.allRes 8 1),(.exposure 8 1548),(.avoidNot 8 9 1548 0),(.avoidNot 8 10 1548 0),(.avoidNot 8 9 1548 1),(.avoidNot 8 10 1548 1),(.avoidLive 8 1548 2),(.avoidNot 8 9 1548 2),(.avoidNot 8 10 1548 2),(.avoidLive 8 1548 3),(.avoidNot 8 9 1548 3),(.avoidNot 8 10 1548 3),(.exactAt 8 0 7426),(.seeLab 8 0 10 7426 0),(.seeLab 8 0 11 7426 1),(.seeLive 8 0 7426 2),(.seeLive 8 0 7426 3),(.exactAt 8 0 9992),(.seeLab 8 0 9 9992 0),(.seeLab 8 0 10 9992 0),(.seeLab 8 0 9 9992 1),(.seeLab 8 0 10 9992 1),(.seeLab 8 0 9 9992 2),(.seeLab 8 0 10 9992 2),(.seeLive 8 0 9992 3),(.seeLab 8 0 9 9992 3),(.seeLab 8 0 10 9992 3),(.exactAt 8 6 9992),(.seeLab 8 6 9 9992 0),(.seeLab 8 6 10 9992 1),(.seeLab 8 6 9 9992 2),(.seeLive 8 6 9992 3),(.diffC 0 8 9),(.diffX 1 8 9),(.diffC 1 8 9),(.adjacentCommon 8 9 6),(.residual 8 9 0 1),(.residual 8 9 0 2),(.residual 8 9 0 3),(.residual 8 9 1 2),(.residual 8 9 1 3),(.residual 8 9 2 3),(.diffX 0 8 10),(.diffC 0 8 10),(.diffX 1 8 10),(.diffC 1 8 10),(.adjacentCommon 8 10 0),(.residual 8 10 0 1),(.residual 8 10 0 2),(.residual 8 10 1 2),(.self 9 0),(.self 9 1),(.earlier 9 1),(.self 9 2),(.self 9 3),(.allRes 9 0),(.allRes 9 1),(.exposure 9 4370),(.avoidNot 9 8 4370 0),(.avoidNot 9 12 4370 0),(.avoidNot 9 8 4370 1),(.avoidNot 9 12 4370 1),(.avoidLive 9 4370 2),(.avoidNot 9 8 4370 2),(.avoidNot 9 12 4370 2),(.avoidLive 9 4370 3),(.exposure 9 7426),(.avoidNot 9 8 7426 0),(.avoidNot 9 10 7426 0),(.avoidNot 9 12 7426 0),(.avoidNot 9 8 7426 1),(.avoidNot 9 10 7426 1),(.avoidNot 9 12 7426 1),(.avoidNot 9 8 7426 2),(.avoidNot 9 10 7426 2),(.avoidNot 9 11 7426 2),(.avoidNot 9 12 7426 2),(.avoidLive 9 7426 3),(.exactAt 9 5 5008),(.seeLab 9 5 8 5008 0),(.seeLab 9 5 12 5008 0),(.seeLab 9 5 8 5008 1),(.seeLab 9 5 12 5008 1),(.seeLive 9 5 5008 2),(.seeLab 9 5 8 5008 2),(.seeLab 9 5 12 5008 2),(.seeLive 9 5 5008 3),(.exactAt 9 6 792),(.seeLab 9 6 8 792 0),(.seeLab 9 6 8 792 1),(.seeLive 9 6 792 2),(.seeLab 9 6 8 792 2),(.seeLive 9 6 792 3),(.exactAt 9 6 7812),(.seeLab 9 6 10 7812 0),(.seeLab 9 6 12 7812 1),(.seeLab 9 6 11 7812 2),(.seeLive 9 6 7812 3),(.exactAt 9 6 9992),(.seeLab 9 6 8 9992 0),(.seeLab 9 6 10 9992 0),(.seeLive 9 6 9992 1),(.seeLab 9 6 8 9992 1),(.seeLab 9 6 10 9992 1),(.seeLab 9 6 8 9992 2),(.seeLab 9 6 10 9992 2),(.seeLive 9 6 9992 3),(.diffX 0 9 8),(.diffC 0 9 8),(.diffX 1 9 8),(.diffC 1 9 8),(.residual 9 8 0 1),(.residual 9 8 0 2),(.residual 9 8 1 2),(.diffX 0 9 10),(.diffC 0 9 10),(.diffX 1 9 10),(.diffC 1 9 10),(.adjacentCommon 9 10 5),(.residual 9 10 0 1),(.residual 9 10 0 2),(.residual 9 10 1 2),(.someRes 10),(.allRes 10 0),(.allRes 10 1),(.self 11 0),(.self 11 1),(.self 11 2),(.self 11 3),(.readerAny false 0),(.readerLab false 0 0 0 true),(.readerAny false 1),(.readerLab false 1 0 0 true),(.readerLab false 1 0 4 false),(.readerAny false 5),(.readerLab false 5 0 0 false),(.readerLab false 5 0 2 true),(.readerAny false 10),(.readerLab false 10 0 4 true),(.readerLab false 10 1 4 true),(.readerLab false 10 2 4 true),(.readerLab false 10 3 4 true),(.readerAny false 14),(.readerLab false 14 0 0 false),(.readerLab false 14 0 4 false),(.readerAny false 16),(.readerLab false 16 0 0 false),(.readerLab false 16 0 2 false),(.readerAny false 17),(.readerAny false 18),(.readerAny true 0),(.readerLive true 0 2),(.readerLive true 0 3),(.readerAny true 1),(.readerLive true 1 2),(.readerLive true 1 3),(.readerAny true 5),(.readerLive true 5 2),(.readerLive true 5 3),(.readerAny true 10),(.readerLive true 10 2),(.readerLive true 10 3),(.readerAny true 14),(.readerLive true 14 2),(.readerLive true 14 3),(.readerAny true 16),(.readerLab true 16 0 8 true),(.readerLab true 16 0 9 false),(.readerLab true 16 0 10 true),(.readerLab true 16 1 8 true),(.readerLab true 16 1 9 false),(.readerLab true 16 1 10 true),(.readerLab true 16 1 11 false),(.readerLive true 16 2),(.readerLab true 16 2 8 true),(.readerLab true 16 2 9 false),(.readerLab true 16 2 10 true),(.readerLive true 16 3),(.readerLab true 16 3 8 true),(.readerAny true 17),(.readerLab true 17 0 8 false),(.readerLab true 17 0 9 true),(.readerLab true 17 0 10 false),(.readerLab true 17 1 8 false),(.readerLab true 17 1 9 true),(.readerLab true 17 1 10 false),(.readerLab true 17 2 8 false),(.readerLab true 17 2 9 true),(.readerLab true 17 2 10 false),(.readerLive true 17 3),(.readerLab true 17 3 9 true),(.readerAny true 18),(.readerLab true 18 0 11 true),(.readerLab true 18 1 11 true),(.readerLab true 18 2 11 true),(.readerLab true 18 3 11 true),(.eqLab false 0 5 0 true),(.gateEq true 0 5 1),(.eqLab false 0 16 0 true),(.gateEq true 0 16 0),(.eqLab false 1 10 4 false),(.gateEq true 1 10 0),(.gateEq true 1 10 1),(.eqLab false 1 14 0 true),(.gateEq true 1 14 0),(.gateEq true 1 14 1),(.eqLab false 5 16 2 true),(.gateEq true 5 16 0),(.eqLab false 10 14 4 true),(.gateEq true 10 14 0),(.gateEq true 10 14 1),(.gateEq false 16 17 0),(.eqLab true 16 17 8 true),(.eqLab true 16 17 9 false),(.eqLab true 16 17 10 true),(.gateEq false 16 18 0),(.eqLab true 16 18 11 false)]

def table229_0 : List Nat := [65,321,0x10102,0x4c1,0x5c1,0xa0582,0x641,0x6c1,0x741,0x7c1,0x941,0x100902,0x110902,0xac1,0x130a82,0x140a82]
def table229_1 : List Nat := [0xb41,0xe41,0x178e82,0x10c1,0x1d9102,0x12c1,0x39102,0x49102,0xae55299444,0x181402,0x1a1402,0x1e1482,0x1f1482,0x1d9502,0x231502,0x241502]
def table229_2 : List Nat := [0x229582,0x261582,0x271582,0xbe5d2d9644,0x1a9602,0x201682,0x1d9702,0x229782,0xce65319844,0x181802,0x1a9802,0x1e1882,0x1f9882,0x231902,0x249902,0x229982]
def table229_3 : List Nat := [0x261982,0x279982,0xde6d359a44,0x189a02,0x1f1a82,0x239b02,0x229b82,0x51c02,0x49c82,0x61c82,0xcc1,0x399c47a31170c86,0x399c48e311d0c86,0x399c49a31220c86,0x399c48e3d1d0c86,0x399c49a3d220c86]
def table229_4 : List Nat := [0x399c49a47220c86,0x39d02,0x71d02,0x49d82,0x81d82,0xdc1,0x3b9d47e35170d86,0x3b9d492351d0d86,0x3b9d4923f1d0d86,0x1e41,0x2141,0x3da182,0x23c1,0x26c1,0x5a402,0x6a402]
def table229_5 : List Nat := [0x146a14fa744,0x3e2702,0x412702,0x442782,0x462782,0x43a802,0x492802,0x4c2802,0x48a882,0x156a953a944,0x3e2902,0x3f2902,0x412902,0x442982,0x452982,0x462982]
def table229_6 : List Nat := [0x492a02,0x4a2a02,0x4b2a02,0x4c2a02,0x48aa82,0x166b157ab44,0x3e2b02,0x41ab02,0x442b82,0x46ab82,0x43ac02,0x492c02,0x4cac02,0x48ac82,0x176b95bad44,0x3ead02]
def table229_7 : List Nat := [0x44ad82,0x43ae02,0x49ae02,0x48ae82,0x186c15faf44,0x3f2f02,0x462f82,0x4bb002,0x48b082,0x196c963b144,0x3eb102,0x3f3102,0x3db182,0x44b182,0x453182,0x49b202]
def table229_8 : List Nat := [0x4a3202,0x48b282,0x5b302,0x33302,0x6b382,0x43382,0x67b35127d3d0c86,0x67b35267d430c86,0x67b352689430c86,0x5b402,0x73402,0x6b482,0x83482,0x2041,0x69b45167f3d2006,0x69b452a7f432006]
def table229_9 : List Nat := [0x69b452a8b432006,0x1107b503,0x7b582,0x8b582,0x3641,0x36c1,0x3741,0x37c1,0x3841,0xe3003803,0x3941,0xe7003903,0xe801b903,0x3ac1,0xec0aba83,0xef093a83]
def table229_10 : List Nat := [0x1eef579bc44,0xf90c3c03,0xf90d3c83,0xf90e3d03,0xf90f3d83,0x3ec1,0xfc10be83,0xfe11be83,0x4041,0x10213c003,0x10414c003,0x41c1,0x4241,0x2230f86c2c4,0x1dc382,0x22c402]
def table229_11 : List Nat := [0x233178ac4c4,0x6ac582,0x6bc602,0x2431f8ec6c4,0x1dc782,0x22c802,0x2532792c8c4,0x6ac982,0x6bca02,0x2632f96cac4,0x6acb82,0x6bcc02,0x273379accc4,0x13b164c83,0x13c18cc83,0x13f1a4c83]
def table229_12 : List Nat := [0x13b1c4d03,0x13c1ecd03,0x13f1f4d03,0x14020cd03,0x1dcd82,0x13b214d83,0x13c23cd83,0x13f244d83,0x22ce02,0x13b254e03,0x29347a2d0c4,0x14a3ed083,0x14d3c5083,0x14e3fd083,0x14a44d103,0x14d425103]
def table229_13 : List Nat := [0x14e45d103,0x14a49d183,0x14d475183,0x14e4ad183,0x48d202,0x14d4d5203,0x2af55a9d444,0x1596c5403,0x1596d5483,0x1596e5503,0x1596f5583,0xed715683,0x15b8e4303,0x103715703,0x15d994283,0xf874d783]
def table229_14 : List Nat := [0x15f914483,0x15f924503,0xfd735803,0x161954483,0x161964503,0x105775883,0x163994683,0xff7c5903,0x165954883,0x165964903,0x167834003,0x14b9d5983,0x14c9ed983,0x14f9f5983,0x169844003,0x158a0da03]
def table229_15 : List Nat := [129,0x501,0x801,0x881,0x981,0xa01,0x1cce23d188b85,0x1cce247188e85,0x1cce24d189105,0x1cce2471e8e85,0x1cce24d1e9105,0x1cce24d239105,0x1dcea3f1a8b85,0x1dcea491a8e85,0x1dcea491f8e85,0x33d9a893e9e85]
def table229_16 : List Nat := [0x33d9a933ea185,0x33d9a9344a185,0x34da28b3f9e85,0x34da2953fa185,0x34da29545a185,0x38c1,0x39c1,0x3a01,0x3b01,0x3bc1,0x7cbc02,0x7cbc82,0x7cbd02,0x7cbd82,0x3f01,0x3f81]
def table229_17 : List Nat := [0x4081,0x4101,0x9dcc82,0x9dcd02,0x9dcd82,0x9dce02,0xa6d082,0xa6d102,0xa6d182,0xa6d202,0xacd402,0xacd482,0xacd502,0xacd582,0x5681,0x8e4302]
def table229_18 : List Nat := [0x5701,0x994282,0x7c5782,0x5801,0x954482,0x964502,0x5881,0x994682,0x7c5902,0x59c1,0xa5ce82,0xa64f42,0xa7cf82,0x5a41,0xac5042,0x3e41]
def table229_19 : List Nat := [0x5781,0x5901,0x461e0c03,0x12044230f04,0x90221183,0x481102,0x5027890239405,0x2813c481904,0x13c389cccf39329487,0x2813c480ec4,0x389ccae531d1806,0x1409e2403,0xe8c254399c45,0x91492203,0x29c91a55184,0x29c91a52b84]
def table229_20 : List Nat := [0x29c91a52244,0x122af4f9f04,0x14e48d283,0x4ec1,0x52c1,0x5341,0x4f41,0x466531793cb05,0x9fa4cfa8b4325474612a02ca,0x4fd267d45a192a3a309509,0x1267d431104,0x4fd267d45a192a531d0c09,0x22d0c95378e862cc6a1509,0x45a192a671d0c598d41a924a,0x4fd16864a95cce6f9c94c743166350d,0x116864ab584]
def table229_21 : List Nat := [0xd76aca83,0x6bb542,0x2294c7431399c46,0x13f9c8ea66773a8d47,0x27e933ea2d0c95298e88,0xa024cfa864a94c6,0x44643399a8ec5,0x499f516864a8f47e3523838a,0x4fd267d45a192a3d1fcc89,0x499f516864a8f47e4918840a,0xa027d4e933ea086,0x228e87a52399c46,0x13f499f4f48b431fc743d29038b,0x9fa4cfa7a45a18fe3a1e948a,0x2b8e8a6753b8fc6,0x4fc8b35299205]
def table229_22 : List Nat := [0x4fc8b35298d05,0x499f4f48b431fc74491a9c8a,0x228e8a661399c46,0x4fd267d3d22d0c7f1d0f49,0x499f4f48b431fc74531f82ca,0x4fd267d3d22d0c7f1d1249,0x27e933e9e916863f8e88,0x14057a203,0xa00ec2,0x5015e531f95c8a31431f49,0x122af5ba1c4,0x1405794cae7d1f9147,0x1127a3e9104,0xe90c534aa2c8a491ab389,0x5015e532bab05,0xa014cae453a9dc6]
def table229_23 : List Nat := [0x2807a2995cfe8b22b308,0x5015e532b9145,0x280af2995c4,0x2cd5e89431105,0x59a199aaf44b3c6,0xa04e47f353b9d46,0x91432bd8ed169a487,0x5008a8666abc5,0xe88a73389485,0x7445399c44,0x5008a8666a4c5,0x28045433344,0x48a19a6d163a486,0x2450cd368a245,0xa02202,0x14022a183]
def table229_24 : List Nat := [0xa021c2,0x5001,0x5601,0x5401,0x5481,0x5501,0x5581]

def encoded229 (i : Nat) : Nat :=
  if i < 192 then
    if i < 96 then
      if i < 48 then
        if i < 16 then
          table229_0.getD (i%16) 0
        else
          if i < 32 then
            table229_1.getD (i%16) 0
          else
            table229_2.getD (i%16) 0
      else
        if i < 64 then
          table229_3.getD (i%16) 0
        else
          if i < 80 then
            table229_4.getD (i%16) 0
          else
            table229_5.getD (i%16) 0
    else
      if i < 144 then
        if i < 112 then
          table229_6.getD (i%16) 0
        else
          if i < 128 then
            table229_7.getD (i%16) 0
          else
            table229_8.getD (i%16) 0
      else
        if i < 160 then
          table229_9.getD (i%16) 0
        else
          if i < 176 then
            table229_10.getD (i%16) 0
          else
            table229_11.getD (i%16) 0
  else
    if i < 288 then
      if i < 240 then
        if i < 208 then
          table229_12.getD (i%16) 0
        else
          if i < 224 then
            table229_13.getD (i%16) 0
          else
            table229_14.getD (i%16) 0
      else
        if i < 256 then
          table229_15.getD (i%16) 0
        else
          if i < 272 then
            table229_16.getD (i%16) 0
          else
            table229_17.getD (i%16) 0
    else
      if i < 336 then
        if i < 304 then
          table229_18.getD (i%16) 0
        else
          if i < 320 then
            table229_19.getD (i%16) 0
          else
            table229_20.getD (i%16) 0
      else
        if i < 368 then
          if i < 352 then
            table229_21.getD (i%16) 0
          else
            table229_22.getD (i%16) 0
        else
          if i < 384 then
            table229_23.getD (i%16) 0
          else
            table229_24.getD (i%16) 0
def book229 (i : Nat) : Clause := let n := encoded229 i; unpackLits 9 (n%64) (n>>>6)

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem initialClauses229 : inputsOK 2 229 a229 r229 (baseBook book229 240).toList=true := by decide +kernel

def rows229_0 : List Nat := [0x40401,0x100a01,0x281601,0x281801,0x341c01,0x341e01,0xe87601,0xe87801,0xe87a01,0xe87c01,0xe87e01,0xe88001,0x1148c01,0x1148e01,0x1149001,0xe90c01,0xe90e01,0xe91001,0x2351c01,0x2351e01,0x2352001,0x2613202,0x2693602,0x782693802]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk229_0 : checkRows book229 9 240 rows229_0=true := by decide +kernel

def rows229_1 : List Nat := [0x78a753c02,0x1a753e02,0x194201,0x1d4401,0x214601,0x254801,0x792954c02,0x79a954e02,0x7a2a15202,0x7aaa15402,0x417a01,0x458001,0x4d8a01,0x559201,0x1259801,0x1299e01,0x131a401,0x135aa01,0x251ae01,0x255b001,0x259b201,0x25db401,0x84415b602,0x479b801]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk229_1 : checkRows book229 9 264 rows229_1=true := by decide +kernel

def rows229_2 : List Nat := [0x88415ba02,0x481bc01,0x41dbe01,0x87419c402,0x48dc601,0x48dc801,0x88c25ca02,0x499cc01,0x43dce01,0x55aa1d402,0x4a5d601,0x4a5d801,0x4a5da01,0x562a1dc02,0x4b5de01,0x21b0c85c294004,0x4be4401,0x4be5001,0x885018148643c2d0d8ac6209,0x1a1406060217c4c8561b1b938724f0f0b4540f,0xe0a03030108a432fa7b4cc5a1e1b938724f090505812,0xf8a030290c8ac363010bddf2fb9a0506e4e1c93c5c12,0x30c46bc130917cf70d0646e4e1c93c4ec89ab184a11,0x2cd5b2790ad15cbc7cb0436189b07d8c2e168dc9c39278815eb5644d63e19]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk229_2 : checkRows book229 9 288 rows229_2=true := by decide +kernel

def rows229_3 : List Nat := [0x92f1ecbe148a058c10e06d880a,0x6188d78245f0683218620983a2013ce26ec817cd4724f1b9384a16,0x7834f7150a43005,0x1e0cbe5ec2b144e825399c4dd902f104d47237279383013,0x602f140adf21e1707df608,0x148ca503414cb06d2b1acce09,0x150ca5033144f4793ecf5006b2b34da25836a04d211,0x188e8593a9699acb651d8bece349a0c8786a4f8ee11,0x6b3c994f66666b2d94ce3e9b502d49f4fcfe0f,0x5732940cc512c1b4d807,0x3f328f2cb3d504ff3d29d027f3e40b51a00e,0x22b1489c497804,0x50e5401,0x233188bc599404,0x5165601,0x5b2c1d325984c5c006,0x5b2c1d1245cd1d74b758a4484fd5faf1822b142ed70b2640bd26430ba310b048022504c60f0b83f3098d19c226,0xb6583a248b9a3ae96eb148911fabf5e30456285dae164c817a4882164520e090045a1472389e0de902e6307c3d3098d19c22b,0x10a830b85a0004,0x6052191052a9205,0x22889047f22c6839193dc6a1f0f0cc6e8220a0d2211,0x20839453d9222b220a1fa2e090dd0441418a91610,0x820e514f7488b488287e0ad84c15e31e9a2a0d06298125f0dd044141d19161a,0x1188a49a4a0804]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk229_3 : checkRows book229 9 312 rows229_3=true := by decide +kernel

def rows229_4 : List Nat := [0x70ba16124592e162b7984c56c0a,0x28f505bac574bb592e17208,0x562d7b3de7420178485008,0x3098efc7e8497805,0x64fe1a87c3c180d54c8491464111237a910c7285424029cbe19d2c402f1b3229551a7d186820,0x6188d78245f0683218620983b5496508fc793d1fd033b1009d914aa35104a1a,0x166ad93c8578c45a2ba3e08,0x827cc0072854590e08fc45108255660b216aafa55186e13,0x423e6003741a2483047e2308891ab8b450295faf85f51a78b0255660b216aafa5518721e,0x847b4006e834490608fe46110255660b216aafa55187213,0x829c40072854590e08fe451092359148a05ac7632f2b15616304381baad469ec85aabc5f4a30954b2502e148b06496508fc793d1fd033ba35106e33,0x4e1f22f645185a05,0x31d7efe7e10d0b00410deb63945c0914426452824c10e5197815,0x31d7efe7e1050700428e2b63744c09184448d45255c0e322941260d197819,0x7c34fe7e0483005,0x32bc0c31c3e20645197c08,0x3cbc0c2fc3420645198c08,0x112a2fd4910514838140116851c8e1220d,0x333ca90803004,0x10aa2fd4990d18858140112821bd8ac22ab057ebac1a55192215,0x10aa35e4990d188581401128210529220d,0x44a8bf924414520e050045a1472389d0dec8c2b00a8502e100be941b15d8d221b,0x44a8d7924414520e050045a147238b10dc55640d308315f0fd94376310529221b,0xd08c30250db0d835613076cc5b2cb216aaf13880c74a361a8ca67ad1f8f8793d1fe833d2e94cc86d40cb2853ba3510482a]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk229_4 : checkRows book229 9 336 rows229_4=true := by decide +kernel

def rows229_5 : List Nat := [0x6846181286d86c1ab3216aaf138804c1d0a5184811,0x4112289210debd52218e50a847fd3aa34f2f164b867329acc080391e4dc7a37990da7340cb2853bb41c0fb67178d9904ba2519182d,0x6637194e26a369ccde07,0x7c501814866d22fb51c2cf3b165185c0d,0x10a830b859fe04,0x8224512421bbf6c4431ca150951a78a9180e,0x10448a2c88397ed88823741a09ff6d15582bec2b5db2a34f2f164c080391e4dc5c3d1bcce66321cd032ca15a0fa4bb51c2cf3ba3511142f,0xb057d855e9650a7768a2519fa0a,0x13a1ca2e048a48d452644b79046e83415a2c40f,0x9d0dd130246246a292215bc863942a120370b412ed47b3c9fcfa812f164b46f371c8d670b39ccc66c32db8da649dd1ac42a,0x42a0c2e16b89accb6e36da8e1679dd1a020e,0x196026642a0ed8170b12cd609,0x1accd017f92cca05,0xbf63bf1fc12b44b2853ba2519780b,0x2f200b2792e1e8ce66329acc06436a06080e,0x612f40e045a3d9bcf26e3f9caec8c48d452442baa246f5b218e50a84ba304381b3e9c2e567b4190da7340cec40c825d18b22b,0x6eb601,0x13abc082c403,0x304381bb7909235149a3206891bde4c2592d10c727b37a15087937404fe72b4190e6819d88190703e9a0be69bbd1aea29,0xc10e06ede4248d45268c81a246f79218e50085421e5fe7a2d944b2503015af45f2a1f4d268bbda0b06440cec40c825d1aea2b,0xf3033d16ca2592817ca869bb180ac58322050010,0x2f18605032d1ecde79371fce57c3e9c0c8734092cb212,0x1a2ce01,0x1821c0ddbc8891a8a49157d458e6f2411ba0d057bb44eefc206451aea18]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk229_5 : checkRows book229 9 360 rows229_5=true := by decide +kernel

def rows229_6 : List Nat := [0x28950de69375a8e2552c1ce7670bf518a00e,0x562a404d25142a0ee76c0b85afe4bc05f8da589dd18a013,0x6065c01,0x60a3401,0x60a3601,0x60a3801,0x60a3a01]
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem rowsOk229_6 : checkRows book229 9 384 rows229_6=true := by decide +kernel

def lastUnits229 := digits 9 4 0xc36170983
set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem conflict229 : checkReasons book229 391 214 lastUnits229 0=true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 200000 in
theorem exclude229 {D : Dag} (h : StrictLive 14 D) (hc : sem_Comp 14 adj D) (z : Bzero 14 D=0) (bp : Bplus 14 D=11) (eq : mask 229=ineligSet 14 D) : False := by
  obtain ⟨Z⟩ := construct_layout (k:=2) h hc bp eq (by decide +kernel)
  let v := truth Z a229
  have hbase : ValidThrough v book229 240 := book_start Z h hc z eq _ _ _ _ initialClauses229
  have h0 : ValidThrough v book229 264 := rows_sound hbase rows229_0 rowsOk229_0
  have h1 : ValidThrough v book229 288 := rows_sound h0 rows229_1 rowsOk229_1
  have h2 : ValidThrough v book229 312 := rows_sound h1 rows229_2 rowsOk229_2
  have h3 : ValidThrough v book229 336 := rows_sound h2 rows229_3 rowsOk229_3
  have h4 : ValidThrough v book229 360 := rows_sound h3 rows229_4 rowsOk229_4
  have h5 : ValidThrough v book229 384 := rows_sound h4 rows229_5 rowsOk229_5
  have h6 : ValidThrough v book229 391 := rows_sound h5 rows229_6 rowsOk229_6
  exact book_end h6 _ _ conflict229
end PEqualNP.Outside.L_meta_9775.UpstreamCore.Compact
