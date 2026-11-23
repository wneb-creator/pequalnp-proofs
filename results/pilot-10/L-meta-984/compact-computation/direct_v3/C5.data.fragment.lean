def C5_initial : List Nat := [0x721, 0x94a, 0xa94, 0x141e, 0x30e0, 0x40f8, 0x6007]

def C5_values : Nat := 0xe83fd07ba0070f8e1cfc383803f000d529a53f4a56807ce4f9c87203e107c1ff83e300054fea83d43e254a49fa929523e23fcc72189f107e207040488041006200039ea71c0df85a7f34e0683cc7818002a944e428000eaf1c1e35285cfcb90951e280040007b58f211d282f785ca09001000100008000e0009001000100018001400180010001

def C5_N : Nat → Nat
  | 4 => 1
  | 5 => 7
  | 6 => 21
  | 7 => 52
  | 8 => 40
  | 9 => 1
  | _ => 0

def C5_countBits : Nat → Nat
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | 8 => 2
  | 9 => 1
  | _ => 0

def C5_slots : Nat → Nat
  | 4 => 1
  | 5 => 2
  | 6 => 2
  | 7 => 2
  | 8 => 1
  | _ => 0

def C5_recordBits : Nat → Nat
  | 4 => 14
  | 5 => 21
  | 6 => 21
  | 7 => 21
  | 8 => 21
  | 9 => 7
  | _ => 0

def C5_records : Nat → List Nat
  | 4 => [0x2307]
  | 5 => [0x362c3a03e320208f8f0c3b6281e3bb2d01d9a]
  | 6 => [0x10da478a523a6405d92db4d16d680d8d806c7e2c21f0db0f6c8c7b6263c88ff0021cf910c7c52d3931e1ec985986b67476c5ddb63d0d94b]
  | 7 => [0x37e806cfe2a39e022df010f78f19e4019ee016fe005bf0039fa1a69e021df009af8031ec014ee014df9098f802bdc01fde01a7700cbd8043bc02bbe019df007b780597c00ef601b1f0109fc5273c037beb535e4c6cf80873da26ae0126f009efb24d6c02abe0007f00bef807afc01df60107700dafc5893c011fd15b1f00a2f8021ec03a7e01cbf]
  | 8 => [0x34aaa80595492aaa3d5558aaaa8b555532aaa6d5550eaaabc5555c2aaa955555caaab5555452aaa0155600acac8555432aaa8955526aaabf555412aaa8d55518aaa80556442aab115558a8aa806555322aac555500aaa8455542aaaa2555506aaa81555404aaa5d555]
  | 9 => [0x7f]
  | _ => []

def C5_buckets : Nat → Nat
  | 4 => 1
  | 5 => 2
  | 6 => 6
  | 7 => 13
  | 8 => 10
  | 9 => 1
  | _ => 0

def C5_flag : Nat → Nat
  | 4 => 2
  | 5 => 128
  | 6 => 128
  | 7 => 0x400
  | 8 => 0x400
  | 9 => 2
  | _ => 0

def C5_seedBits : Nat → Nat
  | 4 => 2
  | 5 => 8
  | 6 => 8
  | 7 => 11
  | 8 => 11
  | 9 => 2
  | _ => 0

def C5_seeds : Nat → Nat
  | 4 => 2
  | 5 => 0x5608
  | 6 => 0xb6f2d020187
  | 7 => 0x14ec2ec0f80700e718018014ca00814c23
  | 8 => 0x4d840002970020cf05e0181bc14
  | 9 => 2
  | _ => 0

def C5_S (s j : Nat) : List Nat :=
  qDirectState C5_initial (C5_countBits s) 15 7 (C5_slots s) C5_values
    (fld ((C5_records s).getD (j / 256) 0) (C5_recordBits s) (j % 256))

def C5_idx : Nat → List Nat → Nat :=
  qIndex C5_N C5_buckets C5_flag C5_seedBits C5_seeds
