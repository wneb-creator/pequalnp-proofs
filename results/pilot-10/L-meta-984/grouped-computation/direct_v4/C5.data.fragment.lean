def C5_initial : List Nat := [0x721, 0x94a, 0xa94, 0x141e, 0x30e0, 0x40f8, 0x6007]

def C5_values : Nat := 0xe83fd07ba0070f8e1cfc383803f000d529a53f4a56807ce4f9c87203e107c1ff83e300054fea83d43e254a49fa929523e23fcc72189f107e207040488041006200039ea71c0df85a7f34e0683cc7818002a944e428000eaf1c1e35285cfcb90951e280040007b58f211d282f785ca09001000100008000e0009001000100018001400180010001

def C5_patterns : Nat := 0x0

def C5_N : Nat → Nat
  | 4 => 1
  | 5 => 7
  | 6 => 21
  | 7 => 52
  | 8 => 40
  | 9 => 1
  | _ => 0

def C5_counts : Nat → Nat
  | 4 => 0x1000
  | 5 => 0x6001000
  | 6 => 0x13002000
  | 7 => 0xb028001
  | 8 => 0x21007
  | 9 => 1
  | _ => 0

def C5_specs : Nat → Nat
  | 4 => 0x101000
  | 5 => 0x401101000
  | 6 => 0x481181000
  | 7 => 0x281481101
  | 8 => 0x501482
  | 9 => 257
  | _ => 0

def C5_seeds : Nat → List Nat
  | 4 => [0x0, 0x2, 0x0]
  | 5 => [0x0, 0x2, 0x5e01]
  | 6 => [0x0, 0x1, 0x16599340a0f]
  | 7 => [0x2, 0xb11e330040c0a72b0c367b, 0x2425]
  | 8 => [0x10202, 0x205006012134600581c15, 0x0]
  | 9 => [0x2, 0x0, 0x0]
  | _ => []

def C5_records : Nat → List (List Nat)
  | 4 => [[], [0x2307], []]
  | 5 => [[], [0x208f], [0x203e331dd966c58747861db140f01d9a]]
  | 6 => [[], [0x6c7e1cf], [0x325b6931e1f0db0f8a5a7476c5d930b30d6ce223fc406c6e4431ed918f86d23c5291da2dad1610f6c4c7a6405ddb63d0d94b]]
  | 7 => [[0x7f], [0x677cfef29dc8fe577d65f2bddcbf87bd4df6cfd077877d35f6f7cefb6d7d97b84fd55f21ee1cf517c6fd3dbd0ef1ded6fe69dcb7e8b7debf33dd7df6c7dd3f4f7ce7e49bcc7b], [0xf19e5926b71624f5a9af434d3e2b63f2131f8a8e7a6367da26af149cf]]
  | 8 => [[0x1655555655565555565565595], [0x137f47fdfff0ffc17f15fc67f89fe47f07fe2ff5dfc27f4d7c37f79fdc7f03fe2df45fc7ff4bfd8ff0bfcdff27fc4ff6bfcd7f11fc97f2ffc5ff], []]
  | 9 => [[0x7f], [], []]
  | _ => []

def C5_S (s j : Nat) : List Nat :=
  qGroupedState C5_initial 3 15 7 C5_patterns C5_values (C5_counts s) (C5_specs s) (C5_records s) j

def C5_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C5_initial (C5_counts s) (C5_specs s) (C5_seeds s) ws
