import PEqualNP.Outside.L_meta_10760
namespace PEqualNP.Outside.L_meta_10760
def initL : Nat := AA
def initM : Nat := Nat.lor (Nat.lor AA FPM) (Nat.shiftLeft AA NN)
def initG : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [623206300500902416, 586501818987791009, 983013849822025310, 27829622366090])
def initB : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [199399373622595187, 551347227570801641, 449854011628258799, 43483784895180])
def initZ : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [257656616232503890, 829471751099623830, 415205677891363302, 36526379355494])
def initW0 : W := ⟨rawP.getD 6 0, (List.foldr (fun a b => a + b * 1000000000000000000) 0 [120334134919823360, 830120494839523312, 855250304338135712, 1737652864367]), 0, (List.foldr (fun a b => a + b * 1000000000000000000) 0 [120334134919823360, 830120494839523312, 855250304338135712, 1737652864367]), 3⟩
def initW1 : W := ⟨rawP.getD 4 0, (List.foldr (fun a b => a + b * 1000000000000000000) 0 [74063309805715456, 830425468208864597, 383718679226926389, 54354680916]), 0, (List.foldr (fun a b => a + b * 1000000000000000000) 0 [74063309805715456, 830425468208864597, 383718679226926389, 54354680916]), 3⟩
def initW2 : W := ⟨rawP.getD 1 0, (List.foldr (fun a b => a + b * 1000000000000000000) 0 [359567522738208800, 717711943750158483, 785985766192984993, 1686695200258]), 0, (List.foldr (fun a b => a + b * 1000000000000000000) 0 [359567522738208800, 717711943750158483, 785985766192984993, 1686695200258]), 3⟩
def initW3 : W := ⟨rawP.getD 5 0, (List.foldr (fun a b => a + b * 1000000000000000000) 0 [228346779924692992, 154599939986577495, 99463365618252235, 1686642221471]), 0, (List.foldr (fun a b => a + b * 1000000000000000000) 0 [228346779924692992, 154599939986577495, 99463365618252235, 1686642221471]), 3⟩
def initW4 : W := ⟨rawP.getD 2 0, (List.foldr (fun a b => a + b * 1000000000000000000) 0 [679793644683396096, 282372146581158413, 547116230740940654, 52709176360]), 0, (List.foldr (fun a b => a + b * 1000000000000000000) 0 [679793644683396096, 282372146581158413, 547116230740940654, 52709176360]), 3⟩
def initW5 : W := ⟨rawP.getD 3 0, (List.foldr (fun a b => a + b * 1000000000000000000) 0 [568352024878940160, 516421932309839646, 507766106047361665, 1686693643537]), 0, (List.foldr (fun a b => a + b * 1000000000000000000) 0 [568352024878940160, 516421932309839646, 507766106047361665, 1686693643537]), 3⟩
def initW6 : W := ⟨rawP.getD 0 0, (List.foldr (fun a b => a + b * 1000000000000000000) 0 [911285340439314433, 390223550795055862, 855347881572293845, 52657752773]), 0, (List.foldr (fun a b => a + b * 1000000000000000000) 0 [911285340439314433, 390223550795055862, 855347881572293845, 52657752773]), 3⟩
def initV : List W := [initW0, initW1, initW2, initW3, initW4, initW5, initW6]


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma initL_eq : lz 0 = initL := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma initM_eq : mz 0 = initM := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma initG_eq : pL ((pr ac4 0).map fun _ => 16) = initG := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma initB_eq : pL ((pr ac4 0).map fun e => 16 + (13 - e.2)) = initB := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma initV_eq : avl (PZ (pr ac4 0)) (mz 0) (rawL []) = initV := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma initZ_eq : initB - sumc initV = initZ := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma init_tst (F : Nat → Bool) : tst true initL 13 initV F = F 0 := by rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma init_sub (h : List W → Bool) : anySub true initL initV 0 h = h initV := by
  change Bool.rec (motive := fun _ => Bool) false true (Bool.rec (motive := fun _ => Bool) false true (Bool.rec (motive := fun _ => Bool) false true (Bool.rec (motive := fun _ => Bool) false true (Bool.rec (motive := fun _ => Bool) false true (Bool.rec (motive := fun _ => Bool) false true (Bool.rec (motive := fun _ => Bool) false true (h initV))))))) = h initV
  cases h initV <;> rfl

example
    (lower13Case0 : chk [] (pr ac4 0) 0 12 0 FF 1 = false)
    (lower13Case1 : chk [] (pr ac4 0) 0 12 1 FF 1 = false)
    (lower13Case2 : chk [] (pr ac4 0) 0 12 2 FF 1 = false)
    (lower13Case3 : chk [] (pr ac4 0) 0 12 3 FF 1 = false)
    (lower13Case4 : chk [] (pr ac4 0) 0 12 4 FF 1 = false)
    (lower13Case5 : chk [] (pr ac4 0) 0 12 5 FF 1 = false)
    (lower13Case6 : chk [] (pr ac4 0) 0 12 6 FF 1 = false)
    (lower13Case7 : chk [] (pr ac4 0) 0 12 7 FF 1 = false)
    (lower13Case8 : chk [] (pr ac4 0) 0 12 8 FF 1 = false)
    (lower13Case9 : chk [] (pr ac4 0) 0 12 9 FF 1 = false)
    (lower13Case10 : chk [] (pr ac4 0) 0 12 10 FF 1 = false)
    (lower13Case11 : chk [] (pr ac4 0) 0 12 11 FF 1 = false)
    (lower13Case12 : chk [] (pr ac4 0) 0 12 12 FF 1 = false) : m0_0.all (okS ac4 0 12) = true := by
  apply List.all_eq_true.mpr
  intro p hp
  simp only [m0_0, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · simpa only [okS, Bool.not_eq_true'] using lower13Case0
  · simpa only [okS, Bool.not_eq_true'] using lower13Case1
  · simpa only [okS, Bool.not_eq_true'] using lower13Case2
  · simpa only [okS, Bool.not_eq_true'] using lower13Case3
  · simpa only [okS, Bool.not_eq_true'] using lower13Case4
  · simpa only [okS, Bool.not_eq_true'] using lower13Case5
  · simpa only [okS, Bool.not_eq_true'] using lower13Case6
  · simpa only [okS, Bool.not_eq_true'] using lower13Case7
  · simpa only [okS, Bool.not_eq_true'] using lower13Case8
  · simpa only [okS, Bool.not_eq_true'] using lower13Case9
  · simpa only [okS, Bool.not_eq_true'] using lower13Case10
  · simpa only [okS, Bool.not_eq_true'] using lower13Case11
  · simpa only [okS, Bool.not_eq_true'] using lower13Case12

end PEqualNP.Outside.L_meta_10760
