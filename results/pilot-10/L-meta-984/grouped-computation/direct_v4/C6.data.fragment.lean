def C6_initial : List Nat := [0x9b6, 0xe49, 0x1292, 0x1524, 0x6007, 0xa038, 0xc1c0]

def C6_values : Nat := 0xe1f8e1c0e03fe007e000d1c0c9c0c3c0c000a83872976e4f69b7600035242e4929b620001fb61f6d1f241edb1e921e491e001db61d241bb61a9219b617b617241400120010000fff0e000bb60a0008920806080002000092000600020001

def C6_patterns : Nat := 0x0

def C6_N : Nat → Nat
  | 4 => 1
  | 5 => 5
  | 6 => 13
  | 7 => 29
  | 8 => 23
  | 9 => 1
  | _ => 0

def C6_counts : Nat → Nat
  | 4 => 0x1000
  | 5 => 0x4001000
  | 6 => 0xa003000
  | 7 => 0x6016001
  | 8 => 0x12005
  | 9 => 1
  | _ => 0

def C6_specs : Nat → Nat
  | 4 => 0x101000
  | 5 => 0x281101000
  | 6 => 0x301301000
  | 7 => 0x301681101
  | 8 => 0x481202
  | 9 => 257
  | _ => 0

def C6_seeds : Nat → List Nat
  | 4 => [0x0, 0x2, 0x0]
  | 5 => [0x0, 0x2, 0xb]
  | 6 => [0x0, 0x10, 0x14086]
  | 7 => [0x2, 0x10fc021002000c532001, 0x45e]
  | 8 => [0xa2, 0xe1008320411, 0x0]
  | 9 => [0x2, 0x0, 0x0]
  | _ => []

def C6_records : Nat → List (List Nat)
  | 4 => [[], [0xbf0], []]
  | 5 => [[], [0x158f], [0x34be0eb1c1c6781e4f0]]
  | 6 => [[], [0x2bd8bf8df6], [0x18478d2ab6689f0e9bc963b930b74bec1eaa7ca7787d331e]]
  | 7 => [[0x7f], [0x2a7e4fe43babdae7ec7d83e9deddfcffe1bf43dd3fc97ea1f8ff8afd16f53f52fc8fcaf7], [0x151bb38b7658ded48cf91379daf4f]]
  | 8 => [[0x155555955565565655], [0x2fe6ff53f23fc5fe1ff07fdbfc4fe37e1bfcbfccfea7f8ffbdfe4fed7f], []]
  | 9 => [[0x7f], [], []]
  | _ => []

def C6_S (s j : Nat) : List Nat :=
  qGroupedState C6_initial 3 16 6 C6_patterns C6_values (C6_counts s) (C6_specs s) (C6_records s) j

def C6_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C6_initial (C6_counts s) (C6_specs s) (C6_seeds s) ws
