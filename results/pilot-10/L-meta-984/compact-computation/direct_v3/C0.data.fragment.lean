def C0_initial : List Nat := [0x724, 0x949, 0xa92, 0x3403, 0x501c, 0x60e0]

def C0_values : Nat := 0x77fcee49d38fa70741fe839d00fa0070fce1c1c0738006af2d5c1a7a74f068e0cfc99c932f064e0c7c18782fbedbdfb4396576c0e573ca83944728004a9292931c920003fdb7edefa4df01bd4b7a06f00db93b7036c06d40cca497241ffe3ed87b68f241d2435245ed8b92169228004ac894d12962420480890010102004400072c0e4a1c00280040108000c0008401040202040000c00090010000c0008000

def C0_patterns : Nat := 0x559556555551545541515155

def C0_N : Nat → Nat
  | 4 => 2
  | 5 => 20
  | 6 => 54
  | 7 => 71
  | 8 => 13
  | 9 => 1
  | _ => 0

def C0_countBits : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 2
  | 8 => 2
  | 9 => 1
  | _ => 0

def C0_patternBits : Nat → Nat
  | 7 => 3
  | 8 => 3
  | 9 => 3
  | _ => 0

def C0_slots : Nat → Nat
  | 4 => 2
  | 5 => 3
  | 6 => 3
  | 7 => 2
  | 8 => 1
  | _ => 0

def C0_recordBits : Nat → Nat
  | 4 => 20
  | 5 => 27
  | 6 => 27
  | 7 => 17
  | 8 => 10
  | 9 => 3
  | _ => 0

def C0_records : Nat → List Nat
  | 4 => [0xa93c601387]
  | 5 => [0x9f3598c027c35a2ab3c8809e9669f11c8c027ca1c0282b880243f80121e17157ad4404f9a380a740700a496200d8ee27cd6a1800128f013e58e02acf1e2ba3c48090b93]
  | 6 => [0x2fe800115f00bcaf2015a1d800098f800119f00020be000427c04f88b803c4b90000afa00e12e40210fe0000b37000293e00f15e404f6b980624b9009cee600029de29e24c808c55d0088778020b83c053967809eda700fd3ae00000fc01b0fc808abdb013e69f3e6b21d59e2588000fdf013e6af4e8cd1c01217c80003fe00fdb9e01423cc04556b803a5790115d1e000407c04140d805857500027ee00027dc00057baf5a4b10000b7a01412cc04f9a3807e75b]
  | 7 => [0x11538720065a744809829c40027900aa80175592201250052a20f23c40000500869e24df870002d00f680574f124008d009a805664c70000700c6803d403ba008546562f5a401594e680003000f4018b1490000e80254019a0228008a80094001a016d5e498027400da004d00d2807e0e87600e5002a800d4025a00ad01040035400ea0185009c803f4002ab55182304f64403ea483c]
  | 8 => [0x150f56d775153d4060155501c9509465]
  | 9 => [0x5]
  | _ => []

def C0_buckets : Nat → Nat
  | 4 => 1
  | 5 => 5
  | 6 => 14
  | 7 => 18
  | 8 => 4
  | 9 => 1
  | _ => 0

def C0_flag : Nat → Nat
  | 4 => 16
  | 5 => 128
  | 6 => 256
  | 7 => 0x400
  | 8 => 16
  | 9 => 2
  | _ => 0

def C0_seedBits : Nat → Nat
  | 4 => 5
  | 5 => 8
  | 6 => 9
  | 7 => 11
  | 8 => 5
  | 9 => 2
  | _ => 0

def C0_seeds : Nat → Nat
  | 4 => 8
  | 5 => 0x7510500126
  | 6 => 0xc1300f8c01809012864004070305a05
  | 7 => 0x101ac51560401881b040048ad00518800c0081601001002961
  | 8 => 0x4e183
  | 9 => 2
  | _ => 0

def C0_S (s j : Nat) : List Nat :=
  qDirectStatePattern C0_initial (C0_countBits s) (C0_patternBits s) C0_patterns 15 7 (C0_slots s) C0_values
    (fld ((C0_records s).getD (j / 256) 0) (C0_recordBits s) (j % 256))

def C0_idx : Nat → List Nat → Nat :=
  qIndex C0_N C0_buckets C0_flag C0_seedBits C0_seeds
