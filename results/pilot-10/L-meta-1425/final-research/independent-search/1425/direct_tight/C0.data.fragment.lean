def C0_initial : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

def C0_values : Nat := 0xffffaaaaffaaffaaffaaaaaaffaa0000ff00aa00ff000000f0f0a0a0f0f00000f0a0f0a0f0a0a0a0f000f000f0000000cccc8888cccc0000cc88cc88cc888888cc00cc00cc000000

def C0_patterns : Nat := 0x0

def C0_N : Nat → Nat
  | 2 => 2
  | 3 => 10
  | 4 => 10
  | 5 => 1
  | _ => 0

def C0_counts : Nat → Nat
  | 2 => 0x2000
  | 3 => 0xa000
  | 4 => 0x9001
  | 5 => 1
  | _ => 0

def C0_specs : Nat → Nat
  | 2 => 0x181000
  | 3 => 0x481000
  | 4 => 0x401101
  | 5 => 257
  | _ => 0

def C0_seeds : Nat → List Nat
  | 2 => [0x0, 0x3]
  | 3 => [0x0, 0x196c10]
  | 4 => [0x2, 0xb4312]
  | 5 => [0x2, 0x0]
  | _ => []

def C0_records : Nat → List (List Nat)
  | 2 => [[], [0x48c65]]
  | 3 => [[], [0x81c9554dc769c273358b79ce7]]
  | 4 => [[0x1f], [0x23715d6f69e4f45db76bcaf]]
  | 5 => [[0x1f], []]
  | _ => []

def C0_S (s j : Nat) : List Nat :=
  qGroupedState C0_initial 2 32 5 C0_patterns C0_values (C0_counts s) (C0_specs s) (C0_records s) j

def C0_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C0_initial (C0_counts s) (C0_specs s) (C0_seeds s) ws
