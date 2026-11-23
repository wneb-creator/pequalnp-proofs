def C6_initial : List Nat := [0x9b6, 0xe49, 0x1292, 0x1524, 0x6007, 0xa038, 0xc1c0]

def C6_values : Nat := 0xe1f8e1c0e03fe007e000d1c0c9c0c3c0c000a83872976e4f69b7600035242e4929b620001fb61f6d1f241edb1e921e491e001db61d241bb61a9219b617b617241400120010000fff0e000bb60a0008920806080002000092000600020001

def C6_N : Nat → Nat
  | 4 => 1
  | 5 => 5
  | 6 => 13
  | 7 => 29
  | 8 => 23
  | 9 => 1
  | _ => 0

def C6_countBits : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | _ => 0

def C6_slots : Nat → Nat
  | 4 => 1
  | 5 => 2
  | 6 => 2
  | 7 => 2
  | 8 => 1
  | _ => 0

def C6_recordBits : Nat → Nat
  | 4 => 13
  | 5 => 19
  | 6 => 19
  | 7 => 19
  | 8 => 20
  | 9 => 7
  | _ => 0

def C6_records : Nat → List Nat
  | 4 => [0xbf0]
  | 5 => [0x1e4f002b1eeb1c0d2f838cf0]
  | 6 => [0x308f1bec1eaa7ca7787805fc015ecb1dca998f52ab674de4c2dd006fb344f8]
  | 7 => [0x153f009fc050fd637b009fe022de025f8077f00af7021ee03ff951bb5233e018fa015f8057b226f3006fc00ff80a5f80877014fc011f8003f8107d02e7f6bd3c03bdb8b76]
  | 8 => [0x5155501556b55550d55519555515544555501559015650955501655355557955569555115558d55505555955550155531555155551955491555]
  | 9 => [0x7f]
  | _ => []

def C6_buckets : Nat → Nat
  | 4 => 1
  | 5 => 2
  | 6 => 4
  | 7 => 8
  | 8 => 6
  | 9 => 1
  | _ => 0

def C6_flag : Nat → Nat
  | 4 => 2
  | 5 => 8
  | 6 => 128
  | 7 => 256
  | 8 => 0x800
  | 9 => 2
  | _ => 0

def C6_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 4
  | 6 => 8
  | 7 => 9
  | 8 => 12
  | 9 => 2
  | _ => 0

def C6_seeds : Nat → Nat
  | 4 => 2
  | 5 => 98
  | 6 => 0x4f4a0611
  | 7 => 0x708cc6a100082c0219
  | 8 => 0x81700452f0010060d3
  | 9 => 2
  | _ => 0

def C6_S (s j : Nat) : List Nat :=
  qDirectState C6_initial (C6_countBits s) 16 6 (C6_slots s) C6_values
    (fld ((C6_records s).getD (j / 256) 0) (C6_recordBits s) (j % 256))

def C6_idx : Nat → List Nat → Nat :=
  qIndex C6_N C6_buckets C6_flag C6_seedBits C6_seeds
