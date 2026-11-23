def C1_initial : List Nat := [0x3c21, 0x454a, 0x4a94, 0x90c6, 0xa318, 0x1001f, 0x103e0]

def C1_values : Nat := 0x1a318d0006431b00014a94a2afd152a87c140009e1fcf0860fc1040081ffc001a00030000718c357397842b3de598c29c60fad67c2127ef110008000040000210001800020000

def C1_N : Nat → Nat
  | 5 => 8
  | 6 => 22
  | 7 => 36
  | 8 => 18
  | 9 => 1
  | _ => 0

def C1_countBits : Nat → Nat
  | 5 => 1
  | 6 => 1
  | 7 => 2
  | 8 => 2
  | 9 => 1
  | _ => 0

def C1_slots : Nat → Nat
  | 5 => 3
  | 6 => 3
  | 7 => 2
  | 8 => 1
  | _ => 0

def C1_recordBits : Nat → Nat
  | 5 => 25
  | 6 => 25
  | 7 => 26
  | 8 => 20
  | 9 => 7
  | _ => 0

def C1_records : Nat → List Nat
  | 5 => [0x215c742fae1a17571400100f44e34342fba0c078d0e042f87]
  | 6 => [0x193e000a9f0217c3810ae3804493c01c6e6011307810be9c085f1e89031985f443808963c08571f0ba88b00044f810aeb805d13c02280f8574470088e7406d73c04288f]
  | 7 => [0x441055408545520655040441565d1055513c1550105155744154013455511015544305551181550111555c4415501105554441555d1155006855500955511441556d10555128155442055401d551016155400155500b51551141550110566144055611055405d554012455614445500c5155120155]
  | 8 => [0x155551155521555455550155961555019550955501556441553d55551555445550d55519555015552955571555]
  | 9 => [0x7f]
  | _ => []

def C1_buckets : Nat → Nat
  | 5 => 2
  | 6 => 6
  | 7 => 9
  | 8 => 5
  | 9 => 1
  | _ => 0

def C1_flag : Nat → Nat
  | 5 => 256
  | 6 => 128
  | 7 => 0x400
  | 8 => 256
  | 9 => 2
  | _ => 0

def C1_seedBits : Nat → Nat
  | 5 => 9
  | 6 => 8
  | 7 => 11
  | 8 => 9
  | 9 => 2
  | _ => 0

def C1_seeds : Nat → Nat
  | 5 => 0x16805
  | 6 => 0x600a07011b5d
  | 7 => 0xc31a0800200c00800d848a8
  | 8 => 0x90625c3006
  | 9 => 2
  | _ => 0

def C1_S (s j : Nat) : List Nat :=
  qDirectState C1_initial (C1_countBits s) 17 6 (C1_slots s) C1_values
    (fld ((C1_records s).getD (j / 256) 0) (C1_recordBits s) (j % 256))

def C1_idx : Nat → List Nat → Nat :=
  qIndex C1_N C1_buckets C1_flag C1_seedBits C1_seeds
