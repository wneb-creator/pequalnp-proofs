def C1_initial : List Nat := [0x3c21, 0x454a, 0x4a94, 0x90c6, 0xa318, 0x1001f, 0x103e0]

def C1_values : Nat := 0x1a318d0006431b00014a94a2afd152a87c140009e1fcf0860fc1040081ffc001a00030000718c357397842b3de598c29c60fad67c2127ef110008000040000210001800020000

def C1_patterns : Nat := 0x655555955595555551551515515515541590558155

def C1_N : Nat → Nat
  | 5 => 8
  | 6 => 22
  | 7 => 36
  | 8 => 18
  | 9 => 1
  | _ => 0

def C1_counts : Nat → Nat
  | 5 => 0x4003001000
  | 6 => 0x400f003000
  | 7 => 0x1400f001
  | 8 => 0xe004
  | 9 => 1
  | _ => 0

def C1_specs : Nat → Nat
  | 5 => 0x201181101000
  | 6 => 0x201501191000
  | 7 => 0x401412111
  | 8 => 0x591212
  | 9 => 273
  | _ => 0

def C1_seeds : Nat → List Nat
  | 5 => [0x0, 0x2, 0x2, 0x7]
  | 6 => [0x0, 0x3, 0x6440303002, 0x3]
  | 7 => [0x2, 0x4014201, 0x3c0601662d, 0x0]
  | 8 => [0x4, 0x1080400827, 0x0, 0x0]
  | 9 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C1_records : Nat → List (List Nat)
  | 5 => [[], [0x100f], [0x10ae39e343c2f87], [0x44e34342eae2a17d70d0bee83]]
  | 6 => [[], [0x15064110], [0x10ae3e15c742f874493d0a23d744f2239d44c1f0be3e17d39c6e68575c8a03db5cf2258f], [0x85744742ea22d1206330be887]]
  | 7 => [[0x8], [0x1122d577444c54d215490764416325d1368d05], [0x6113f0a23d444fa209f4513e8887d114fae8be6d13e40de5128fa241f5d13c89e7d118fb889f8515eba27d10cfa211f], []]
  | 8 => [[0x9ba8], [0x3e06844058460882a1880e148121c844c28], [], []]
  | 9 => [[0x8], [], [], []]
  | _ => []

def C1_S (s j : Nat) : List Nat :=
  qGroupedState C1_initial 4 17 6 C1_patterns C1_values (C1_counts s) (C1_specs s) (C1_records s) j

def C1_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C1_initial (C1_counts s) (C1_specs s) (C1_seeds s) ws
