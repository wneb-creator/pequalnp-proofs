def C8_initial : List Nat := [0x1a5, 0x29a, 0x552, 0xa61, 0x140d, 0x280e, 0x3070]

def C8_values : Nat := 0xd1c3170c3c0f731f683bf06000800014001

def C8_patterns : Nat := 0x5559555

def C8_N : Nat → Nat
  | 7 => 5
  | 8 => 8
  | 9 => 1
  | _ => 0

def C8_counts : Nat → Nat
  | 7 => 0x4001
  | 8 => 0x6002
  | 9 => 1
  | _ => 0

def C8_specs : Nat → Nat
  | 7 => 0x281105
  | 8 => 0x305206
  | 9 => 261
  | _ => 0

def C8_seeds : Nat → List Nat
  | 7 => [0x2, 0x9]
  | 8 => [0x6, 0x463]
  | 9 => [0x2, 0x0]
  | _ => []

def C8_records : Nat → List (List Nat)
  | 7 => [[0x0], [0x87e9fa9fcbf]]
  | 8 => [[0x1], [0x4c329c4]]
  | 9 => [[0x0], []]
  | _ => []

def C8_S (s j : Nat) : List Nat :=
  qGroupedState C8_initial 2 14 4 C8_patterns C8_values (C8_counts s) (C8_specs s) (C8_records s) j

def C8_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C8_initial (C8_counts s) (C8_specs s) (C8_seeds s) ws
