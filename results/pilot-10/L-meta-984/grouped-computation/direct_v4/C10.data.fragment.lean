def C10_initial : List Nat := [0x21b, 0x3e4, 0x458, 0x81c, 0xc23, 0x1089, 0x1112]

def C10_values : Nat := 0x1ebbe55f08f22589dc44e072db7512a6cd1627ed3ed9f24e6e7253529994c6e62529b944c86e3371928a944ca1010007fe3f9dfc8ea373db9e1cc6e5c72db961c76e23651b1ed8f0c6362e316187ec2060e30017f8be451c287d438a1b50022710b883c41020610108044001ff0fc86d833c196ccb061b26c11e08804001ff8a6c50025b12008ec440218104880c40008002000800300090040010006001

def C10_patterns : Nat := 0x0

def C10_N : Nat → Nat
  | 4 => 1
  | 5 => 15
  | 6 => 67
  | 7 => 101
  | 8 => 43
  | 9 => 1
  | _ => 0

def C10_counts : Nat → Nat
  | 4 => 0x1000000
  | 5 => 0xd002000
  | 6 => 0x1031011000
  | 7 => 0x23041001
  | 8 => 0x24007
  | 9 => 1
  | _ => 0

def C10_specs : Nat → Nat
  | 4 => 0x101000000
  | 5 => 0x501181000
  | 6 => 0x101581301000
  | 7 => 0x501681101
  | 8 => 0x501282
  | 9 => 257
  | _ => 0

def C10_seeds : Nat → List Nat
  | 4 => [0x0, 0x0, 0x2, 0x0]
  | 5 => [0x0, 0x1, 0x6aa0901802, 0x0]
  | 6 => [0x0, 0x102273c1, 0x9200402c0abb40540521082706c0445401e, 0x2]
  | 7 => [0x2, 0x11622800405a0dc00d408000600f00782b00260120008060018019, 0x4201532118040dc0a06a1f, 0x0]
  | 8 => [0x1f6, 0x10a28c06054242a80d0d00a, 0x0, 0x0]
  | 9 => [0x2, 0x0, 0x0, 0x0]
  | _ => []

def C10_records : Nat → List (List Nat)
  | 4 => [[], [], [0x10a060], []]
  | 5 => [[], [0x7fc9df2], [0xe59e2846f8426f8613ac9396b480bf13e698989bc55299c5a6b84e66ca8b464e56e4], []]
  | 6 => [[], [0x1ceea0fa73e5bd58e76dcd9f3a4f94767db967639ea0ee35ea1753bea8be], [0x15251d684394d67c9e9ae4e50669cd1b4d5bd29c53ce99f272bb33c67caf3366ccdf29ca9b4069caf2d6b527bc726b53353c9cb4ccd5a633c6fc4868cdd2fccb8d725a2ba39559998ae538d3a606f92d53d2f5c2ecd6f1686f93a5bd101ae4bcdf29cb9b375f8d51ae539cae686b94e40da21be4d08f2b4d392d37d274c3d3e31e], [0x86e9764]]
  | 7 => [[0x7f], [0x2f3fb5f88fe47debfb35ea6fe2fed77792fc97e8d7ecbf1bf96f56bbd17773fadf737fa9fe9cf85fe1df9cef75f87fe35f8b7b19f96f73df63bf31ee07e53f887ec3f9a7733fa43f55de5fe49de2774ddd6fd41de73f5fdd0f767cd9f761dea7d35eefef67ec57e4bde67e27f9cee4fddc6f], [0x4d5dd9a1be680df6542bb1f37eac34e7790379a83b1a15e99a0e73e2be686fd4a8a7e6b4ece91f6402bb4e14f9d20ece9a76722b7569ef9bb4e6a5076682bb3a5dd9a1becb8df63657d4375ba1aeeab50755c2bb3437c9a08e6b86f6], []]
  | 8 => [[0x1555595595556555565565565], [0x65fc57f09fc3ff15f907757fcaff6ffc1ffabfc47f5ddda7741ff07f5dfc2ff8bfc4ff9bf8dff37fa6ffb1fda7fbbfc17f29fdd7e95fc37f75fc0ff87fcfff], [], []]
  | 9 => [[0x7f], [], [], []]
  | _ => []

def C10_S (s j : Nat) : List Nat :=
  qGroupedState C10_initial 4 13 7 C10_patterns C10_values (C10_counts s) (C10_specs s) (C10_records s) j

def C10_idx (s : Nat) (ws : List Nat) : Nat :=
  qGroupedIndex C10_initial (C10_counts s) (C10_specs s) (C10_seeds s) ws
