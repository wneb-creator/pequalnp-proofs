def C8_initial : List Nat := [0xaaaaaaaa, 0xcccccccc, 0xf0f0f0f0, 0xff00ff00, 0xffff0000]

def C8_values : Nat := 0x0

def C8_patterns : Nat := 0x0

def C8_N : Nat → Nat
  | 4 => 1
  | _ => 0

def C8_counts : Nat → Nat
  | 4 => 1
  | _ => 0

def C8_specs : Nat → Nat
  | 4 => 257
  | _ => 0

def C8_seeds : Nat → List Nat
  | 4 => [0x2]
  | _ => []

def C8_records : Nat → List (List Nat)
  | 4 => [[0x1f]]
  | _ => []

def C8_S (s j : Nat) : List Nat :=
  qGroupedState C8_initial 1 32 1 C8_patterns C8_values (C8_counts s) (C8_specs s) (C8_records s) j

def C8_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C8_initial (C8_counts s) (C8_specs s) (C8_seeds s) ws
