def C0_initial : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

def C0_values : Nat := 0xffffaaaaffaaffaaffaaaaaaffaa0000ff00aa00ff000000f0f0a0a0f0f00000f0a0f0a0f0a0a0a0f000f000f0000000cccc8888cccc0000cc88cc88cc888888cc00cc00cc00000055555555333333330f0f0f0f00ffffff00ff00ff0000ffff

def C0_patterns : Nat := 0x0

def C0_N : Nat → Nat
  | 2 => 2
  | 3 => 14
  | 4 => 15
  | 5 => 1
  | _ => 0

def C0_counts : Nat → Nat
  | 2 => 0x2000
  | 3 => 0x300b000
  | 4 => 0xe001
  | 5 => 1
  | _ => 0

def C0_specs : Nat → Nat
  | 2 => 0x181000
  | 3 => 0x181501000
  | 4 => 0x381101
  | 5 => 257
  | _ => 0

def C0_seeds : Nat → List Nat
  | 2 => [0x0, 0x3, 0x0]
  | 3 => [0x0, 0x743801, 0x2]
  | 4 => [0x2, 0x212537, 0x0]
  | 5 => [0x2, 0x0, 0x0]
  | _ => []

def C0_records : Nat → List (List Nat)
  | 2 => [[], [0x78d25], []]
  | 3 => [[], [0x287635a784e4b99ce7a9d5519ec7], [0x13296641ccc6]]
  | 4 => [[0x1f], [0x15dd79de6f37917c3cbd26c2f5be2f99ef7], []]
  | 5 => [[0x1f], [], []]
  | _ => []

def C0_S (s j : Nat) : List Nat :=
  qGroupedState C0_initial 3 32 5 C0_patterns C0_values (C0_counts s) (C0_specs s) (C0_records s) j

def C0_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C0_initial (C0_counts s) (C0_specs s) (C0_seeds s) ws
