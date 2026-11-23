def C16_initial : List Nat := [0x235, 0x3ca, 0x4a4, 0xc51, 0x1105, 0x2806, 0x3038]

def C16_values : Nat := 0xf1e7907e0fb838e01b4bcd0e33fac8f7238c4f7138c4170b8c1e3000b29ac57b146c06af3aa37a81a906a21a846a0024a48f2a2358001f757555c5164157b5569550552913cf4f293854d153354c15235461514544010003f6cf513bd4ed139d4e513544cf53344ca42f28a3520007ee1f287a41b906b51a9063516904e412004000ffc3350c002b50a002750900230089021108142040800100020004000c00240080011004000800140040008001

def C16_patterns : Nat := 0x0

def C16_N : Nat → Nat
  | 6 => 24
  | 7 => 78
  | 8 => 51
  | 9 => 1
  | _ => 0

def C16_counts : Nat → Nat
  | 6 => 0xf009000
  | 7 => 0xc041001
  | 8 => 0x2b008
  | 9 => 1
  | _ => 0

def C16_specs : Nat → Nat
  | 6 => 0x701401000
  | 7 => 0x401601101
  | 8 => 0x681382
  | 9 => 257
  | _ => 0

def C16_seeds : Nat → List Nat
  | 6 => [0x0, 0x24504, 0x49900810004006]
  | 7 => [0x2, 0x6420010010670273fd03f00a01801b03000a00183d05d010004, 0x430207]
  | 8 => [0x2bc, 0x270814400e02c805800c001803801c04c011, 0x0]
  | 9 => [0x2, 0x0, 0x0]
  | _ => []

def C16_records : Nat → List (List Nat)
  | 6 => [[], [0x107a45e9dee47e9d6e5fd98f671b96f6], [0x2d41ca7389d3905aaae57385b9a72dad81cce4887c5b70badce3d6d6b6b681d3c73b28a1b4e106a]]
  | 7 => [[0x7f], [0x15777fbc97e4ff887ea5dd4fb61f947dbcfd07a5df927d73fabbfc17e55faafeb3f83fa47d59dd6fe7dec7fe71bcb7e93ee5df85bdc7e3ffa1f72bf8efb8bf8a7e33f96f743fa65f6ff907b2ff96f69b7daef23f9e7db2fe75f31fb0bf8ff907eb6fe8df69bdc6e39eec6f1df9b6f3dec9fe], [0x72cf73d73bb1b9dc8077ab639f381db92a1f5510fa64bbb4e1d7968eec84dfa]]
  | 8 => [[0x6555559595655555555955595556], [0x5ff0bfd2ff07fe9ff67ff1ff5dfeeff65fe37f57fc17fc5fee7f03fc37f43ff27f13fe07f1bfe7ffa9fcdff73fc47fbffed7f19fcd7f5df9cfe09fd37f0ffd0fe1dfc57f7bfc77e89fe87f], []]
  | 9 => [[0x7f], [], []]
  | _ => []

def C16_S (s j : Nat) : List Nat :=
  qGroupedState C16_initial 3 14 7 C16_patterns C16_values (C16_counts s) (C16_specs s) (C16_records s) j

def C16_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C16_initial (C16_counts s) (C16_specs s) (C16_seeds s) ws
