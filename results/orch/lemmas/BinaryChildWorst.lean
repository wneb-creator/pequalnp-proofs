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
def binW0 : W := initW0
def binW1 : W := initW1
def binW2 : W := initW2
def binW3 : W := initW3
def binW4 : W := initW4
def binW5 : W := initW5
def binW6 : W := initW6
def binW46 : W := ⟨binW3.s &&& binW5.s, (binW3.a ||| binW5.a), (binW3.b &&& binW5.b), (binW3.a ||| binW5.a) ||| (binW3.b &&& binW5.b), 0⟩
def binW47 : W := ⟨binW3.s ||| binW5.s, (binW3.a &&& binW5.a), (binW3.b ||| binW5.b), (binW3.a &&& binW5.a) ||| (binW3.b ||| binW5.b), 0⟩
noncomputable def forceLook1 (fuel k t z : ℕ) (v : List W) : Bool :=
  st initL (fun l => st initM (fun m => st initG (fun g => st z (fun z =>
    frc v (fun v => look1 l m g 13 fuel k t z v)))))
lemma forceLook1_eq (fuel k t z : ℕ) (v : List W) :
    forceLook1 fuel k t z v = look1 initL initM initG 13 fuel k t z v := by
  simp only [forceLook1, st_eq, frc_eq]
def worstBudget : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [273148639080368722, 863218225616575137, 303892494492434805, 33152992068419])
def worstState : List W := [binW0, binW1, binW2, binW47, binW4, binW6, binW46]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def binaryWorstChecked : look1 initL initM initG 13 12 11 1 worstBudget worstState = false := by
  have h : forceLook1 12 11 1 worstBudget worstState = false := by decide +kernel
  simpa only [forceLook1_eq] using h
end PEqualNP.Outside.L_meta_10760
