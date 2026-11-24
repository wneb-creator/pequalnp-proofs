def C7_initial : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

def C7_values : Nat := 0xfffff0f0ffffccccff000000faf0f0f0eeccccccaaaa0000aa00aa00aa000000

def C7_patterns : Nat := 0x0

def C7_N : Nat → Nat
  | 2 => 2
  | 3 => 6
  | 4 => 8
  | 5 => 1
  | _ => 0

def C7_counts : Nat → Nat
  | 2 => 0x2000000
  | 3 => 0x5001000
  | 4 => 0x7001
  | 5 => 1
  | _ => 0

def C7_specs : Nat → Nat
  | 2 => 0x181000000
  | 3 => 0x201101000
  | 4 => 0x301101
  | 5 => 257
  | _ => 0

def C7_seeds : Nat → List Nat
  | 2 => [0x0, 0x0, 0x1]
  | 3 => [0x0, 0x2, 0x21]
  | 4 => [0x2, 0xd7, 0x0]
  | 5 => [0x2, 0x0, 0x0]
  | _ => []

def C7_records : Nat → List (List Nat)
  | 2 => [[], [], [0x1484844]]
  | 3 => [[], [0x56], [0x426723411988c646]]
  | 4 => [[0x1f], [0x178de562bb3ddf0f], []]
  | 5 => [[0x1f], [], []]
  | _ => []

def C7_S (s j : Nat) : List Nat :=
  qGroupedState C7_initial 3 32 4 C7_patterns C7_values (C7_counts s) (C7_specs s) (C7_records s) j

def C7_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C7_initial (C7_counts s) (C7_specs s) (C7_seeds s) ws
