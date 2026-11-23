def C20_routeCodes : Nat := 0x0
def C20_masks (auto : Nat) : List Nat := (List.range 9).map (fun i => fld C20_routeCodes 32 (9*auto+i))
def C20_coords : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14]
def C20_rankPool : List Nat := [6637690, 6368924, 2104215, 4262552, 2178441, 5311678, 2121081, 3156874, 6445688, 5336747, 5532295, 5394043, 6373084, 4414072]
def C20_inputActions : Nat := 0x1ac688
