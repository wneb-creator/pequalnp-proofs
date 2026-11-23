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

def C0_counts : Nat → Nat
  | 4 => 0x1001000
  | 5 => 0x600d001000
  | 6 => 0x501f011001
  | 7 => 0x14030003
  | 8 => 0xa003
  | 9 => 1
  | _ => 0

def C0_specs : Nat → Nat
  | 4 => 0x101101000
  | 5 => 0x481301101000
  | 6 => 0x20180150110d
  | 7 => 0x60d58d18e
  | 8 => 0x28d18e
  | 9 => 269
  | _ => 0

def C0_seeds : Nat → List Nat
  | 4 => [0x0, 0x2, 0x2, 0x0]
  | 5 => [0x0, 0x2, 0x44234d, 0x1ea09]
  | 6 => [0x2, 0x14f0185801802, 0x55c80007000501cf0004000200050026, 0x14]
  | 7 => [0x1, 0x44e0593d00984b08c0c01217009800803, 0x18130af7e7001, 0x0]
  | 8 => [0x1, 0xe03, 0x0, 0x0]
  | 9 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C0_records : Nat → List (List Nat)
  | 4 => [[], [0x1387], [0xa93c6], []]
  | 5 => [[], [0x128f], [0x9f2c7243f8a74079e966363b890b939f3479f28790f0b9f0d6524b150571ab3c7], [0x27c4723455eb518ae8f131559e467cd6a1cf9acc6]]
  | 6 => [[0x5], [0x9f78af96f47fd31f2feabde0bf3f72beacde03efdf84fa9de33f49f], [0x3c579443bc3a5794e7735e579242f99f3479ed7356876624b99eda77e9d78abdb421fc8aad7a72cf9f357361f958575504b37edcf9f34f8281b384b93c4b9508f382e0f9f1177e75b8c55d8ae8f], [0x2f5a4b18a789333e6b21e9d19a3ab3c4b1]]
  | 7 => [[0x1ee], [0xb6282b0255747505485635f5274fd4341d235855655535435175f89e56d3d4cd494ad4e52d775a5981357b40d8206d1144d154a50f49531515194e5], [0x82304f6469cd126384e1c9e248f1274e205aa8a20f15922743b5eb4a32b179274e897e1c4524090791e20], []]
  | 8 => [[0x1ee], [0x3d555194150f495454255b5dd], [], []]
  | 9 => [[0x5], [], [], []]
  | _ => []

def C0_S (s j : Nat) : List Nat :=
  qGroupedState C0_initial 4 15 7 C0_patterns C0_values (C0_counts s) (C0_specs s) (C0_records s) j

def C0_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C0_initial (C0_counts s) (C0_specs s) (C0_seeds s) ws
