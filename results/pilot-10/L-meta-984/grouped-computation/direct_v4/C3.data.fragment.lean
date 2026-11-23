def C3_initial : List Nat := [0x722, 0xa95, 0x1948, 0x20e6, 0x2419, 0x40f8, 0x5007]

def C3_values : Nat := 0x3a0ff419e80fd003803f000c9f393e320ce0fec1f1839b0005a97b52b67e2ca7d948b00f5c9eb915407a40f441e87c5000952b23e239144f885f107e20003d597a90e7b9ca42e9d5d2aabdd54aa7e64e769c8927fa40041c082110202022400c8000fb51d4836903edc74a8b9514001000100010001c002100110020000c00140010001

def C3_patterns : Nat := 0x0

def C3_N : Nat → Nat
  | 4 => 1
  | 5 => 9
  | 6 => 23
  | 7 => 45
  | 8 => 31
  | 9 => 1
  | _ => 0

def C3_counts : Nat → Nat
  | 4 => 0x1000
  | 5 => 0x8001000
  | 6 => 0x14003000
  | 7 => 0xd01f001
  | 8 => 0x1a005
  | 9 => 1
  | _ => 0

def C3_specs : Nat → Nat
  | 4 => 0x101000
  | 5 => 0x381101000
  | 6 => 0x481181000
  | 7 => 0x381481101
  | 8 => 0x501202
  | 9 => 257
  | _ => 0

def C3_seeds : Nat → List Nat
  | 4 => [0x0, 0x2, 0x0]
  | 5 => [0x0, 0x2, 0x1501]
  | 6 => [0x0, 0x1, 0xd0108401001]
  | 7 => [0x2, 0x289cc090500ae81613, 0x8c5ceae]
  | 8 => [0x33, 0x3490020900a04c05, 0x0]
  | 9 => [0x2, 0x0, 0x0]
  | _ => []

def C3_records : Nat → List (List Nat)
  | 4 => [[], [0x2187], []]
  | 5 => [[], [0x2097], [0x48830c47e1d6990ed4dd270d4cc4488dab234d4cc3]]
  | 6 => [[], [0x169f6b6dd57], [0x6ab4dad265da93a6fccc726471b85a75cb5364c76548671a23dc613c2edccc76aaad35666df3596d4ed376d69c244cdaacb31568f]]
  | 7 => [[0x7f], [0x87b84fcf7d537dadb4f7d69f45ec77d2dddadf60fc8fb5d7d45f797cc7768fc67d6f7dafb5efd8bf29dc9f733bc6fd577d6df2bdcbf7], [0xdd69f784ebb54d6c98bceddb5b3c4fac226dd113e6dced76e4eba6275d293ce849e7]]
  | 8 => [[0x165556555565565555], [0x1ffc57f81fc97f0bfc17f43fc9f78dfc1ff27fc37f3ffc47f6f7cd7f3bfd2ff0ffc4ff03fce7f09fd1ff17fdeff], []]
  | 9 => [[0x7f], [], []]
  | _ => []

def C3_S (s j : Nat) : List Nat :=
  qGroupedState C3_initial 3 15 7 C3_patterns C3_values (C3_counts s) (C3_specs s) (C3_records s) j

def C3_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C3_initial (C3_counts s) (C3_specs s) (C3_seeds s) ws
