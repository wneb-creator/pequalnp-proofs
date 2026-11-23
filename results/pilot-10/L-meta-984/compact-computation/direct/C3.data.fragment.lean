def C3_initial : List Nat := [0x722, 0xa95, 0x1948, 0x20e6, 0x2419, 0x40f8, 0x5007]

def C3_values : Nat := 0x3a0ff419e80fd003803f000c9f393e320ce0fec1f1839b0005a97b52b67e2ca7d948b00f5c9eb915407a40f441e87c5000952b23e239144f885f107e20003d597a90e7b9ca42e9d5d2aabdd54aa7e64e769c8927fa40041c082110202022400c8000fb51d4836903edc74a8b9514001000100010001c002100110020000c00140010001

def C3_N : Nat → Nat
  | 4 => 1
  | 5 => 9
  | 6 => 23
  | 7 => 45
  | 8 => 31
  | 9 => 1
  | _ => 0

def C3_countBits : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | _ => 0

def C3_slots : Nat → Nat
  | 4 => 1
  | 5 => 2
  | 6 => 2
  | 7 => 2
  | 8 => 1
  | _ => 0

def C3_recordBits : Nat → Nat
  | 4 => 14
  | 5 => 21
  | 6 => 21
  | 7 => 21
  | 8 => 21
  | 9 => 7
  | _ => 0

def C3_records : Nat → Nat
  | 4 => 0x2187
  | 5 => 0xd591a5a64380825d220c31122388fc3b5330da9ba4e1a99
  | 6 => 0x385a7613c2ef9acb76d69806b6dcb536d49d35a4cb805a7c98ecad4ed384899bf331e2ad1ed555a2647180755daad3688f716ab2cb5666db998e90ce3
  | 7 => 0xf09d700f2f802fde1136e4c5e76e76b802bdc0427e01adf6a9ad805efc0347e889f30047d804f7dbb6b600cef00aef80517c02dbe849e76e4eb802ddc00cfa00f7d0037ea6275c035f60007f4a4f39e27d402ebe0077d00b4f8021ec035b6014df008bd8062fc018ee009f700def8029dc0307edd69f
  | 8 => 0xa55552aaaa195550aaaa84555402aaa0555500b2a9f55550aaaa0155926a8a82555402aac695558caaa93555602aaa1d55510aaa9c55551aaaa3d5556e8aabd5554eaaaa2555500aca8b555492aaa0d555
  | 9 => 127
  | _ => 0

def C3_buckets : Nat → Nat
  | 4 => 1
  | 5 => 3
  | 6 => 6
  | 7 => 12
  | 8 => 8
  | 9 => 1
  | _ => 0

def C3_flag : Nat → Nat
  | 4 => 2
  | 5 => 256
  | 6 => 256
  | 7 => 256
  | 8 => 64
  | 9 => 2
  | _ => 0

def C3_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 9
  | 6 => 9
  | 7 => 9
  | 8 => 7
  | 9 => 2
  | _ => 0

def C3_seeds : Nat → Nat
  | 4 => 2
  | 5 => 0x2e00c01
  | 6 => 0x22a81160080c01
  | 7 => 0x658281a0501acc2724008040c1b
  | 8 => 0x135410408e0254
  | 9 => 2
  | _ => 0

def C3_S (s j : Nat) : List Nat :=
  qDirectState C3_initial (C3_countBits s) 15 7 (C3_slots s) C3_values
    (fld (C3_records s) (C3_recordBits s) j)

def C3_idx : Nat → List Nat → Nat :=
  qIndex C3_N C3_buckets C3_flag C3_seedBits C3_seeds
