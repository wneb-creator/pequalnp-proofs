import Mathlib

namespace PEqualNP.Outside.L_meta_982_aux.Checkpoint

def getPacked (width block : Nat) (data : Array Nat) (i : Nat) : Nat :=
  (data.getD (i / block) 0 >>> ((i % block) * width)) % 2 ^ width

def values (width block : Nat) (data : Array Nat) (count : Nat) : List Nat :=
  (List.range count).map (getPacked width block data)

def generators (k count width block : Nat) (data : Array Nat) : Array (List Nat) :=
  ((List.range count).map fun g =>
    (List.range k).map fun j => getPacked width block data (g*k+j)).toArray

def group (k parentWidth recipeWidth recipeBlock count : Nat)
    (gens : Array (List Nat)) (recipes : Array Nat) : Array (List Nat) :=
  (List.range count).foldl (fun acc i =>
    let code := getPacked recipeWidth recipeBlock recipes i
    let old := acc.getD (code % 2 ^ parentWidth) []
    let gen := gens.getD (code / 2 ^ parentWidth) []
    acc.push (gen.map (old.getD · 0))) #[(List.range k)]

def actions (refWidth refBlock count : Nat) (refs : Array Nat)
    (gs : Array (List Nat)) : Array (List Nat) :=
  ((List.range count).map fun i => gs.getD (getPacked refWidth refBlock refs i) []).toArray

def permute (k : Nat) (p : List Nat) (w : Nat) : Nat :=
  ((List.range (k+k)).map fun j =>
    w.testBit (if j < k then p.getD j 0 else k + p.getD (j-k) 0)).foldr Nat.bit 0

def move (mask : Nat) (ws : List Nat) (tag : Nat) : List Nat :=
  if tag < 48 then
    let i := tag / 4
    let a := ws.getD i 0
    [a ^^^ mask] ++ (if tag % 4 = 3 then [a] else []) ++ ws.take i ++ ws.drop (i+1)
  else
    let t := (tag-48) / 8
    let b := (List.range 16).foldl (fun old j => if j*(j+1)/2 ≤ t then j else old) 0
    let a := t - b*(b+1)/2
    let x := ws.getD a 0
    let y := ws.getD b 0
    let v := if (tag-48) / 4 % 2 = 1 then x &&& y else x ||| y
    [v] ++ (if (tag-48) / 2 % 2 = 1 then [x] else []) ++
      (if (tag-48) % 2 = 1 then [y] else []) ++
      (ws.zipIdx.filterMap fun (w,i) => if i = a ∨ i = b then none else some w)

def ins (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b::bs => if a ≤ b then a::b::bs else b::ins a bs

def state (k mask parentWidth recipeWidth recipeBlock : Nat)
    (perms : Array (List Nat)) (upper : Nat → List Nat) (recipes : Array Nat) (i : Nat) :
    List Nat :=
  let code := getPacked recipeWidth recipeBlock recipes i
  let parent := code % 2 ^ parentWidth
  let tag := code / 2 ^ parentWidth % 1024
  let g := code / 2 ^ (parentWidth+10)
  ((move mask (upper parent) tag).map (permute k (perms.getD g []))).foldr ins []

def advice (symmetryWidth lengthWidth lengthBlock adviceWidth adviceBlock : Nat)
    (lengths data : Array Nat) (i : Nat) : Array Nat :=
  let count := getPacked lengthWidth lengthBlock lengths i
  let offset := ((List.range i).map (getPacked lengthWidth lengthBlock lengths)).sum
  ((List.range count).map fun j =>
    let v := getPacked adviceWidth adviceBlock data (offset+j)
    v % 1024 + 1024*(1+(v/1024) % 2 ^ symmetryWidth+64*(v/1024/2 ^ symmetryWidth))).toArray

end PEqualNP.Outside.L_meta_982_aux.Checkpoint
namespace PEqualNP.Outside.L_meta_982_aux.CheckpointData
def c8R8 : Array Nat := #[0x15c05390fe43b01dc073700d002]
def c8R8Info : Nat × Nat × Nat := (14,73,8)
def c8R7 : Array Nat := #[0x1740eb8073d038f454f0207801d8066d462e02776173800aa0275012ab0a54091a00f4045a0225191e9296c04ba4a593052982540009815ac0aa6054b02a1807ad03a601cb40e181bae0da606cb8361e0d4f0f5600b20339019480ae4055204150202a4f158269c124e87a743938429c204900c10160c070]
def c8R7Info : Nat × Nat × Nat := (17,60,57)
def c8R6 : Array Nat := #[0x40f38924300332e9202894b26032256182331a2362aa2818a203f2104f2042b2002b1f40f1f8371f40e1e8361e02a1a1121a5441a8361a11419148191121640e161121534415520156181522153149120121262a125201200e11636118410c03f0940e0883d07]
def c8R6Info : Nat × Nat × Nat := (20,51,41)
def c8R5 : Array Nat := #[0x412200301f23c1f13f1c20e0a0390842f0741204]
def c8R5Info : Nat × Nat × Nat := (20,51,8)
def c8R4 : Array Nat := #[0x1c4]
def c8R4Info : Nat × Nat × Nat := (17,60,1)
def c8R3 : Array Nat := #[]
def c8R3Info : Nat × Nat × Nat := (14,73,0)
def c8R2 : Array Nat := #[]
def c8R2Info : Nat × Nat × Nat := (15,68,0)
def c8R1 : Array Nat := #[]
def c8R1Info : Nat × Nat × Nat := (15,68,0)
def c8R0 : Array Nat := #[]
def c8R0Info : Nat × Nat × Nat := (15,68,0)
def c8A1 : Array Nat := #[]
def c8A1Info : Nat × Nat × Nat := (15,68,0)
def c8L1 : Array Nat := #[]
def c8L1Info : Nat × Nat × Nat := (1,1024,0)
def c8A2 : Array Nat := #[]
def c8A2Info : Nat × Nat × Nat := (15,68,0)
def c8L2 : Array Nat := #[]
def c8L2Info : Nat × Nat × Nat := (1,1024,0)
def c8A3 : Array Nat := #[]
def c8A3Info : Nat × Nat × Nat := (15,68,0)
def c8L3 : Array Nat := #[]
def c8L3Info : Nat × Nat × Nat := (1,1024,0)
def c8A4 : Array Nat := #[]
def c8A4Info : Nat × Nat × Nat := (15,68,0)
def c8L4 : Array Nat := #[0x0]
def c8L4Info : Nat × Nat × Nat := (1,1024,1)
def c8A5 : Array Nat := #[0x38]
def c8A5Info : Nat × Nat × Nat := (14,73,1)
def c8L5 : Array Nat := #[0x10]
def c8L5Info : Nat × Nat × Nat := (1,1024,8)
def c8A6 : Array Nat := #[0xc26c30203a09148f0c060413f190704c90402420390a1781048]
def c8A6Info : Nat × Nat × Nat := (17,60,12)
def c8L6 : Array Nat := #[0x38100000000194100]
def c8L6Info : Nat × Nat × Nat := (2,512,41)
def c8A7 : Array Nat := #[0x7413c7051c710ac65514660dc6c0ac6844c6903c5d5105e0d8604486103834510350d8480484883818c6a1984a515104e0d8580a8544484452030c9048450388483d510400a8404483d03834d10314802d86038448170ec1d0c2110be2888521039245241d8a8194802004810d18118d8140380e1040a4c0080fc05038020f4,0xa103c9e4909845078448980cc96480770609213c9252c795388c0c809528868f0880c00b07084c6889860240ed80cda248b5818aa700917d482708697e0622844a2903a780fc]
def c8A7Info : Nat × Nat × Nat := (20,51,79)
def c8L7 : Array Nat := #[0x1000000021100000112206a1354402440044144300001101110000000]
def c8L7Info : Nat × Nat × Nat := (4,256,57)
def c8A8 : Array Nat := #[0x470f5580dd560da500d94e0d8780ad740aa700a96c0a84a4924b06a6884d6444a608495c4486803d6503a600395d0387c0022c93d28939271212c10528101264f13c0ce380ca348b6308b2340ae300aa400161b11517111134dd0f4d9234ad1f4a9130850f0812304d1f0491b43d174390441a0501600c120180e0800a08806,0x3212987121c00f5384f1b84e1c28c53b0c1bb0b9bc09d3089984489c406699c62c800e684eda80e9b18bdad8b958895a40916a056a9852b004eac04ab400a9413e3053a9d936999328c12e9252d8a52c2892a9591e3211a9c1169811285502814fa254f249ce64b4bd27071870528304aa001e465355891555512509114d510,0x6a115ce911784ddd00d97b0add28a968885cc081b1c3ddd03ad8039d5038e0002be92d]
def c8A8Info : Nat × Nat × Nat := (20,51,116)
def c8L8 : Array Nat := #[0x6bd75cb586]
def c8L8Info : Nat × Nat × Nat := (5,204,8)
def c8A9 : Array Nat := #[0xe683e340ec1ff20fb687ba43ce81df00eb7073a838fc1bfa0dbaa67c532e918f08c3625fa12efa96f94b36a57a52afa13f909be24be124de11eb08b7243a920d80ee8073a837c41af90cf8863e02be014e889f044bb21fc90ecb036141a260b88058d82600122407890388016300a340381018b8061002]
def c8A9Info : Nat × Nat × Nat := (17,60,56)
def c8L9 : Array Nat := #[0x38]
def c8L9Info : Nat × Nat × Nat := (6,170,1)
def c8rows : Array Nat := #[0x112242850a14280c993264c993260c18306091224489112244890183060c182448912203060c182020200000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000,0x3365c98f161c17ef5db96ed59b15eb55a94e951a13e74d972a3c586fdf3d78edd3970ddb3568cd7ae5ab15aa52a13a5467cf1d386cd172c54a131e3868b141c283993264c993264993264c9932644891223468d1a3468d12244890a142850a0c183060c064c993264c993162c58b162c583060c13264c993264c912244891122,0xff3a6a828386ffc1668cd8a0ffe8c0a3fe6c54274a07fea5029ff052862bfe1a10c2ffff41b332c4c57fc0e59a94617ff0c143fe6c8d9a280bff02c4a53faa502bfe150941ffff66c39705057fa0a0e1aff48d1407fca940bfffac38282ff16281fffe1c283ffffffffdf7e7bf5e7c77edd7a73e5c786fddb766bd5a7467]
def c8rowsInfo : Nat × Nat × Nat := (7,146,436)
def c8pool : Array Nat := #[]
def c8poolInfo : Nat × Nat × Nat := (60,17,0)
def c8vertex_perms : Array Nat := #[0x14e5c4356608c7aa10e74b1568cd19450635c5852dd38455e3029950ce95306e70a1ac688]
def c8vertex_permsInfo : Nat × Nat × Nat := (3,341,98)
def c8root_indices : Array Nat := #[0xd622c]
def c8root_indicesInfo : Nat × Nat × Nat := (3,341,7)
def c8generator_data : Array Nat := #[0x7e7f737271706f6e6d6c6b6a7d7c7b7a7978777675746968666764656362615e5d605f5c5b52514e4d504f4c4b5a595655585754534a494645484744432a292625282724231d1c19181b1a171622211e201f15131442413e3d403f3c3b32312f2e303a393635383734332d2b2c12110e0d100f07060403050c0b080a09020001,0x20211f262425231e1210110f0c0a0b090e0d081d1b1c1a151419171816130705060201040300b1afaeb0abadacaaa9a8a6a7a5a4a3a2a1a09f9e9d9a9c9b999392919098979695948f8e8d8c8b8ad9d6d8d7d4d3d5d2d1d0cecfcdcccbcac9c8c7c6c5c3c2c4c1bcbbbab9b8c0bfbebdb7b6b5b4b3b289868588878384828081,0xacaba3a2a0a18988878685848382817f7e80787776757d7c7a7b79749f9e9d9c9b9a9998979496958f8e8c8d8b939291908a7371726f7069686766656e6d6c6b6a63646260615f5a5859575e5c5d5b565455534240413f3a3839373e3c3d3b363435335250514f4a4849474e4c4d4b464445433230312d2c2f2e2b2a28292722,0xd9d7d8d5d6d3d4c7c4c6c5c3c2c1c0bfbebdd2d0cfd1cecdcccbcac9c8b7b5b6b4b3bcbabbb9b8b2aaa9a8a7a6a5a4b1b0afaead]
def c8generator_dataInfo : Nat × Nat × Nat := (8,128,436)
def c8recipe_data : Array Nat := #[0xb567073568314600]
def c8recipe_dataInfo : Nat × Nat × Nat := (5,204,13)
def c8reference_data : Array Nat := #[0xdcba9876543210]
def c8reference_dataInfo : Nat × Nat × Nat := (4,256,14)
def c8inputs : List Nat := [0xa37e20c4b7957e20ca37d108ee3bff5555555555556f555aaf556dc07f00000f807f00000fbf801e07808000000000000000000000000,0xc5063bc5e5bf2a344363831ec65fdf999999999999bb999ccb9e7740000fe1f03f800fe0f00003e0003d0000000000000000000000000,0xef1a326c23a9063ede2585297fb1efe1e1e1e1e1e1cde1ef0de7b9bf800ffe0000000fff00000000f83e0000000000000000000000000,0xf75363446183522153e9fb7a47dd8ffe01fe01fe01f1fe0ff1f83e3ffff0000000000000003ffc00ffc00000000000000000000000000,0x8962247d29fd63664621fdbf76918ffffe0001fffe01fff001ffc000000000003ffff000003fffff00000000000000000000000000000,0x9183f84631b1fbbf7bbd994847118ffffffffe000001fffffe000000000000003fffffffffc0000000000000000000000000000000000,0xe1fbbf77bdc183f86231e18c46118ffffffffffffffe00000000003fffffffffc00000000000000000000000000000000000000000000]
open PEqualNP.Outside.L_meta_982_aux.Checkpoint
def c8K : Nat := 218
def c8Mask : Nat := 2^(c8K+c8K)-1
def c8Gens := generators c8K 2 8 128 c8generator_data
def c8Perms := actions 4 256 14 c8reference_data (group c8K 4 5 204 13 c8Gens c8recipe_data)
def c8Rows := values 7 146 c8rows 436
def c8Pool := values 60 17 c8pool 0
def c8Root := (values 3 341 c8root_indices 7).map (c8inputs.getD · 0)
def c8S9 (i : Nat) := if i=0 then c8Root else []
def c8S8 := state c8K c8Mask 0 14 73 c8Perms c8S9 c8R8
def c8S7 := state c8K c8Mask 3 17 60 c8Perms c8S8 c8R7
def c8S6 := state c8K c8Mask 6 20 51 c8Perms c8S7 c8R6
def c8S5 := state c8K c8Mask 6 20 51 c8Perms c8S6 c8R5
def c8S4 := state c8K c8Mask 3 17 60 c8Perms c8S5 c8R4
def c8S3 := state c8K c8Mask 0 14 73 c8Perms c8S4 c8R3
def c8S2 := state c8K c8Mask 1 15 68 c8Perms c8S3 c8R2
def c8S1 := state c8K c8Mask 1 15 68 c8Perms c8S2 c8R1
def c8S0 := state c8K c8Mask 1 15 68 c8Perms c8S1 c8R0
def c8States (s i : Nat) : List Nat := match s with
| 4 => c8S4 i
| 5 => c8S5 i
| 6 => c8S6 i
| 7 => c8S7 i
| 8 => c8S8 i
| 9 => c8S9 i
| _ => []
def c8Count (s : Nat) : Nat := match s with
| 4 => 1
| 5 => 8
| 6 => 41
| 7 => 57
| 8 => 8
| 9 => 1
| _ => 0
def c8Advice (s i : Nat) : Array Nat := match s with
| 4 => advice 4 1 1024 15 68 c8L4 c8A4 i
| 5 => advice 4 1 1024 14 73 c8L5 c8A5 i
| 6 => advice 4 2 512 17 60 c8L6 c8A6 i
| 7 => advice 4 4 256 20 51 c8L7 c8A7 i
| 8 => advice 4 5 204 20 51 c8L8 c8A8 i
| 9 => advice 4 6 170 17 60 c8L9 c8A9 i
| _ => #[]
end PEqualNP.Outside.L_meta_982_aux.CheckpointData

namespace PEqualNP.Outside.L_meta_982_aux.CheckpointData
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
example : c8States 8 0 = [0x1e044088423e7c079dce1e73b9ee7000000000000001ffffffffffc0000000003ffffffffffffffffffffffffffffffffffffffffffff,0x8962247d29fd63664621fdbf76918ffffe0001fffe01fff001ffc000000000003ffff000003fffff00000000000000000000000000000,0x9183f84631b1fbbf7bbd994847118ffffffffe000001fffffe000000000000003fffffffffc0000000000000000000000000000000000,0xa37e20c4b7957e20ca37d108ee3bff5555555555556f555aaf556dc07f00000f807f00000fbf801e07808000000000000000000000000,0xc5063bc5e5bf2a344363831ec65fdf999999999999bb999ccb9e7740000fe1f03f800fe0f00003e0003d0000000000000000000000000,0xef1a326c23a9063ede2585297fb1efe1e1e1e1e1e1cde1ef0de7b9bf800ffe0000000fff00000000f83e0000000000000000000000000,0xf75363446183522153e9fb7a47dd8ffe01fe01fe01f1fe0ff1f83e3ffff0000000000000003ffc00ffc00000000000000000000000000] := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
example : c8Advice 9 0 = #[5122,73731,2054,76807,13322,66571,10254,68623,1042,77843,9238,69655,6170,72731,272443,337983,264267,329807,394323,459863,396387,461927,267371,332911,132211,197751,141443,206983,144523,210063,395411,460951,398491,464031,137387,202927,399539,465079,133307,198847,265411,330951,268491,334031,402651,468191,140515,206055,263403,328943,136435,201975,271611,337151,397571,463111] := by decide +kernel
end PEqualNP.Outside.L_meta_982_aux.CheckpointData
