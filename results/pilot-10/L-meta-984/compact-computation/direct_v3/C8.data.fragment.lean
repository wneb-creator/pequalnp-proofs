def C8_initial : List Nat := [0x1a5, 0x29a, 0x552, 0xa61, 0x140d, 0x280e, 0x3070]

def C8_values : Nat := 0xd1c3170c3c0f731f683bf06000800014001

def C8_N : Nat → Nat
  | 7 => 5
  | 8 => 8
  | 9 => 1
  | _ => 0

def C8_countBits : Nat → Nat
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | _ => 0

def C8_slots : Nat → Nat
  | 7 => 1
  | 8 => 1
  | _ => 0

def C8_recordBits : Nat → Nat
  | 7 => 11
  | 8 => 18
  | 9 => 7
  | _ => 0

def C8_records : Nat → List Nat
  | 7 => [0x43f4fd4fe5f87f]
  | 8 => [0x5555955515554d555755549555055595555]
  | 9 => [0x7f]
  | _ => []

def C8_buckets : Nat → Nat
  | 7 => 2
  | 8 => 2
  | 9 => 1
  | _ => 0

def C8_flag : Nat → Nat
  | 7 => 8
  | 8 => 64
  | 9 => 2
  | _ => 0

def C8_seedBits : Nat → Nat
  | 7 => 4
  | 8 => 7
  | 9 => 2
  | _ => 0

def C8_seeds : Nat → Nat
  | 7 => 53
  | 8 => 0x7a4
  | 9 => 2
  | _ => 0

def C8_S (s j : Nat) : List Nat :=
  qDirectState C8_initial (C8_countBits s) 14 4 (C8_slots s) C8_values
    (fld ((C8_records s).getD (j / 256) 0) (C8_recordBits s) (j % 256))

def C8_idx : Nat → List Nat → Nat :=
  qIndex C8_N C8_buckets C8_flag C8_seedBits C8_seeds
