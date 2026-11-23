def C16_routeCodes : Nat := 0x0
def C16_masks (auto : Nat) : List Nat := (List.range 9).map (fun i => fld C16_routeCodes 32 (9*auto+i))
def C16_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 10, 11, 12, 13]
def C16_rankPool : List Nat := [5376940, 4413814, 3284107, 5458279, 5511017]
def C16_inputActions : Nat := 0x1ac688
