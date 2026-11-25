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

def cutW0 : W := initW0
def cutW1 : W := initW1
def cutW2 : W := initW2
def cutW3 : W := initW3
def cutW4 : W := initW4
def cutW5 : W := initW5
def cutW6 : W := initW6
def cutW7 : W := ⟨cutW0.s ^^^ initM, cutW0.b, cutW0.a, cutW0.c, 0⟩
def cutW8 : W := ⟨cutW1.s ^^^ initM, cutW1.b, cutW1.a, cutW1.c, 0⟩
def cutW9 : W := ⟨cutW2.s ^^^ initM, cutW2.b, cutW2.a, cutW2.c, 0⟩
def cutW10 : W := ⟨cutW3.s ^^^ initM, cutW3.b, cutW3.a, cutW3.c, 0⟩
def cutW11 : W := ⟨cutW4.s ^^^ initM, cutW4.b, cutW4.a, cutW4.c, 0⟩
def cutW12 : W := ⟨cutW5.s ^^^ initM, cutW5.b, cutW5.a, cutW5.c, 0⟩
def cutW13 : W := ⟨cutW6.s ^^^ initM, cutW6.b, cutW6.a, cutW6.c, 0⟩
def cutW14 : W := ⟨cutW7.s &&& cutW1.s, (cutW7.a ||| cutW1.a), (cutW7.b &&& cutW1.b), (cutW7.a ||| cutW1.a) ||| (cutW7.b &&& cutW1.b), 0⟩
def cutW15 : W := ⟨cutW7.s ||| cutW1.s, (cutW7.a &&& cutW1.a), (cutW7.b ||| cutW1.b), (cutW7.a &&& cutW1.a) ||| (cutW7.b ||| cutW1.b), 0⟩
def cutW16 : W := ⟨cutW7.s &&& cutW2.s, (cutW7.a ||| cutW2.a), (cutW7.b &&& cutW2.b), (cutW7.a ||| cutW2.a) ||| (cutW7.b &&& cutW2.b), 0⟩
def cutW17 : W := ⟨cutW7.s ||| cutW2.s, (cutW7.a &&& cutW2.a), (cutW7.b ||| cutW2.b), (cutW7.a &&& cutW2.a) ||| (cutW7.b ||| cutW2.b), 0⟩
def cutW18 : W := ⟨cutW7.s &&& cutW3.s, (cutW7.a ||| cutW3.a), (cutW7.b &&& cutW3.b), (cutW7.a ||| cutW3.a) ||| (cutW7.b &&& cutW3.b), 0⟩
def cutW19 : W := ⟨cutW7.s ||| cutW3.s, (cutW7.a &&& cutW3.a), (cutW7.b ||| cutW3.b), (cutW7.a &&& cutW3.a) ||| (cutW7.b ||| cutW3.b), 0⟩
def cutW20 : W := ⟨cutW7.s &&& cutW4.s, (cutW7.a ||| cutW4.a), (cutW7.b &&& cutW4.b), (cutW7.a ||| cutW4.a) ||| (cutW7.b &&& cutW4.b), 0⟩
def cutW21 : W := ⟨cutW7.s ||| cutW4.s, (cutW7.a &&& cutW4.a), (cutW7.b ||| cutW4.b), (cutW7.a &&& cutW4.a) ||| (cutW7.b ||| cutW4.b), 0⟩
def cutW22 : W := ⟨cutW7.s &&& cutW5.s, (cutW7.a ||| cutW5.a), (cutW7.b &&& cutW5.b), (cutW7.a ||| cutW5.a) ||| (cutW7.b &&& cutW5.b), 0⟩
def cutW23 : W := ⟨cutW7.s ||| cutW5.s, (cutW7.a &&& cutW5.a), (cutW7.b ||| cutW5.b), (cutW7.a &&& cutW5.a) ||| (cutW7.b ||| cutW5.b), 0⟩
def cutW24 : W := ⟨cutW7.s &&& cutW6.s, (cutW7.a ||| cutW6.a), (cutW7.b &&& cutW6.b), (cutW7.a ||| cutW6.a) ||| (cutW7.b &&& cutW6.b), 0⟩
def cutW25 : W := ⟨cutW7.s ||| cutW6.s, (cutW7.a &&& cutW6.a), (cutW7.b ||| cutW6.b), (cutW7.a &&& cutW6.a) ||| (cutW7.b ||| cutW6.b), 0⟩
def cutW26 : W := ⟨cutW8.s &&& cutW0.s, (cutW8.a ||| cutW0.a), (cutW8.b &&& cutW0.b), (cutW8.a ||| cutW0.a) ||| (cutW8.b &&& cutW0.b), 0⟩
def cutW27 : W := ⟨cutW8.s &&& cutW2.s, (cutW8.a ||| cutW2.a), (cutW8.b &&& cutW2.b), (cutW8.a ||| cutW2.a) ||| (cutW8.b &&& cutW2.b), 0⟩
def cutW28 : W := ⟨cutW8.s &&& cutW3.s, (cutW8.a ||| cutW3.a), (cutW8.b &&& cutW3.b), (cutW8.a ||| cutW3.a) ||| (cutW8.b &&& cutW3.b), 0⟩
def cutW29 : W := ⟨cutW8.s &&& cutW4.s, (cutW8.a ||| cutW4.a), (cutW8.b &&& cutW4.b), (cutW8.a ||| cutW4.a) ||| (cutW8.b &&& cutW4.b), 0⟩
def cutW30 : W := ⟨cutW8.s &&& cutW5.s, (cutW8.a ||| cutW5.a), (cutW8.b &&& cutW5.b), (cutW8.a ||| cutW5.a) ||| (cutW8.b &&& cutW5.b), 0⟩
def cutW31 : W := ⟨cutW8.s &&& cutW6.s, (cutW8.a ||| cutW6.a), (cutW8.b &&& cutW6.b), (cutW8.a ||| cutW6.a) ||| (cutW8.b &&& cutW6.b), 0⟩
def cutW32 : W := ⟨cutW9.s &&& cutW0.s, (cutW9.a ||| cutW0.a), (cutW9.b &&& cutW0.b), (cutW9.a ||| cutW0.a) ||| (cutW9.b &&& cutW0.b), 0⟩
def cutW33 : W := ⟨cutW9.s &&& cutW1.s, (cutW9.a ||| cutW1.a), (cutW9.b &&& cutW1.b), (cutW9.a ||| cutW1.a) ||| (cutW9.b &&& cutW1.b), 0⟩
def cutW34 : W := ⟨cutW9.s &&& cutW3.s, (cutW9.a ||| cutW3.a), (cutW9.b &&& cutW3.b), (cutW9.a ||| cutW3.a) ||| (cutW9.b &&& cutW3.b), 0⟩
def cutW35 : W := ⟨cutW9.s &&& cutW4.s, (cutW9.a ||| cutW4.a), (cutW9.b &&& cutW4.b), (cutW9.a ||| cutW4.a) ||| (cutW9.b &&& cutW4.b), 0⟩
def cutW36 : W := ⟨cutW9.s &&& cutW5.s, (cutW9.a ||| cutW5.a), (cutW9.b &&& cutW5.b), (cutW9.a ||| cutW5.a) ||| (cutW9.b &&& cutW5.b), 0⟩
def cutW37 : W := ⟨cutW9.s &&& cutW6.s, (cutW9.a ||| cutW6.a), (cutW9.b &&& cutW6.b), (cutW9.a ||| cutW6.a) ||| (cutW9.b &&& cutW6.b), 0⟩
def cutW38 : W := ⟨cutW10.s &&& cutW0.s, (cutW10.a ||| cutW0.a), (cutW10.b &&& cutW0.b), (cutW10.a ||| cutW0.a) ||| (cutW10.b &&& cutW0.b), 0⟩
def cutW39 : W := ⟨cutW10.s &&& cutW1.s, (cutW10.a ||| cutW1.a), (cutW10.b &&& cutW1.b), (cutW10.a ||| cutW1.a) ||| (cutW10.b &&& cutW1.b), 0⟩
def cutW40 : W := ⟨cutW10.s &&& cutW2.s, (cutW10.a ||| cutW2.a), (cutW10.b &&& cutW2.b), (cutW10.a ||| cutW2.a) ||| (cutW10.b &&& cutW2.b), 0⟩
def cutW41 : W := ⟨cutW10.s &&& cutW4.s, (cutW10.a ||| cutW4.a), (cutW10.b &&& cutW4.b), (cutW10.a ||| cutW4.a) ||| (cutW10.b &&& cutW4.b), 0⟩
def cutW42 : W := ⟨cutW10.s &&& cutW5.s, (cutW10.a ||| cutW5.a), (cutW10.b &&& cutW5.b), (cutW10.a ||| cutW5.a) ||| (cutW10.b &&& cutW5.b), 0⟩
def cutW43 : W := ⟨cutW10.s &&& cutW6.s, (cutW10.a ||| cutW6.a), (cutW10.b &&& cutW6.b), (cutW10.a ||| cutW6.a) ||| (cutW10.b &&& cutW6.b), 0⟩
def cutW44 : W := ⟨cutW11.s &&& cutW0.s, (cutW11.a ||| cutW0.a), (cutW11.b &&& cutW0.b), (cutW11.a ||| cutW0.a) ||| (cutW11.b &&& cutW0.b), 0⟩
def cutW45 : W := ⟨cutW11.s &&& cutW1.s, (cutW11.a ||| cutW1.a), (cutW11.b &&& cutW1.b), (cutW11.a ||| cutW1.a) ||| (cutW11.b &&& cutW1.b), 0⟩
def cutW46 : W := ⟨cutW11.s &&& cutW2.s, (cutW11.a ||| cutW2.a), (cutW11.b &&& cutW2.b), (cutW11.a ||| cutW2.a) ||| (cutW11.b &&& cutW2.b), 0⟩
def cutW47 : W := ⟨cutW11.s &&& cutW3.s, (cutW11.a ||| cutW3.a), (cutW11.b &&& cutW3.b), (cutW11.a ||| cutW3.a) ||| (cutW11.b &&& cutW3.b), 0⟩
def cutW48 : W := ⟨cutW11.s &&& cutW5.s, (cutW11.a ||| cutW5.a), (cutW11.b &&& cutW5.b), (cutW11.a ||| cutW5.a) ||| (cutW11.b &&& cutW5.b), 0⟩
def cutW49 : W := ⟨cutW11.s &&& cutW6.s, (cutW11.a ||| cutW6.a), (cutW11.b &&& cutW6.b), (cutW11.a ||| cutW6.a) ||| (cutW11.b &&& cutW6.b), 0⟩
def cutW50 : W := ⟨cutW12.s &&& cutW0.s, (cutW12.a ||| cutW0.a), (cutW12.b &&& cutW0.b), (cutW12.a ||| cutW0.a) ||| (cutW12.b &&& cutW0.b), 0⟩
def cutW51 : W := ⟨cutW12.s &&& cutW1.s, (cutW12.a ||| cutW1.a), (cutW12.b &&& cutW1.b), (cutW12.a ||| cutW1.a) ||| (cutW12.b &&& cutW1.b), 0⟩
def cutW52 : W := ⟨cutW12.s &&& cutW2.s, (cutW12.a ||| cutW2.a), (cutW12.b &&& cutW2.b), (cutW12.a ||| cutW2.a) ||| (cutW12.b &&& cutW2.b), 0⟩
def cutW53 : W := ⟨cutW12.s &&& cutW3.s, (cutW12.a ||| cutW3.a), (cutW12.b &&& cutW3.b), (cutW12.a ||| cutW3.a) ||| (cutW12.b &&& cutW3.b), 0⟩
def cutW54 : W := ⟨cutW12.s &&& cutW4.s, (cutW12.a ||| cutW4.a), (cutW12.b &&& cutW4.b), (cutW12.a ||| cutW4.a) ||| (cutW12.b &&& cutW4.b), 0⟩
def cutW55 : W := ⟨cutW12.s &&& cutW6.s, (cutW12.a ||| cutW6.a), (cutW12.b &&& cutW6.b), (cutW12.a ||| cutW6.a) ||| (cutW12.b &&& cutW6.b), 0⟩
def cutW56 : W := ⟨cutW13.s &&& cutW0.s, (cutW13.a ||| cutW0.a), (cutW13.b &&& cutW0.b), (cutW13.a ||| cutW0.a) ||| (cutW13.b &&& cutW0.b), 0⟩
def cutW57 : W := ⟨cutW13.s &&& cutW1.s, (cutW13.a ||| cutW1.a), (cutW13.b &&& cutW1.b), (cutW13.a ||| cutW1.a) ||| (cutW13.b &&& cutW1.b), 0⟩
def cutW58 : W := ⟨cutW13.s &&& cutW2.s, (cutW13.a ||| cutW2.a), (cutW13.b &&& cutW2.b), (cutW13.a ||| cutW2.a) ||| (cutW13.b &&& cutW2.b), 0⟩
def cutW59 : W := ⟨cutW13.s &&& cutW3.s, (cutW13.a ||| cutW3.a), (cutW13.b &&& cutW3.b), (cutW13.a ||| cutW3.a) ||| (cutW13.b &&& cutW3.b), 0⟩
def cutW60 : W := ⟨cutW13.s &&& cutW4.s, (cutW13.a ||| cutW4.a), (cutW13.b &&& cutW4.b), (cutW13.a ||| cutW4.a) ||| (cutW13.b &&& cutW4.b), 0⟩
def cutW61 : W := ⟨cutW13.s &&& cutW5.s, (cutW13.a ||| cutW5.a), (cutW13.b &&& cutW5.b), (cutW13.a ||| cutW5.a) ||| (cutW13.b &&& cutW5.b), 0⟩
def cutW62 : W := ⟨cutW0.s &&& cutW1.s, (cutW0.a ||| cutW1.a), (cutW0.b &&& cutW1.b), (cutW0.a ||| cutW1.a) ||| (cutW0.b &&& cutW1.b), 0⟩
def cutW63 : W := ⟨cutW0.s ||| cutW1.s, (cutW0.a &&& cutW1.a), (cutW0.b ||| cutW1.b), (cutW0.a &&& cutW1.a) ||| (cutW0.b ||| cutW1.b), 0⟩
def cutW64 : W := ⟨cutW0.s &&& cutW2.s, (cutW0.a ||| cutW2.a), (cutW0.b &&& cutW2.b), (cutW0.a ||| cutW2.a) ||| (cutW0.b &&& cutW2.b), 0⟩
def cutW65 : W := ⟨cutW0.s ||| cutW2.s, (cutW0.a &&& cutW2.a), (cutW0.b ||| cutW2.b), (cutW0.a &&& cutW2.a) ||| (cutW0.b ||| cutW2.b), 0⟩
def cutW66 : W := ⟨cutW0.s &&& cutW3.s, (cutW0.a ||| cutW3.a), (cutW0.b &&& cutW3.b), (cutW0.a ||| cutW3.a) ||| (cutW0.b &&& cutW3.b), 0⟩
def cutW67 : W := ⟨cutW0.s ||| cutW3.s, (cutW0.a &&& cutW3.a), (cutW0.b ||| cutW3.b), (cutW0.a &&& cutW3.a) ||| (cutW0.b ||| cutW3.b), 0⟩
def cutW68 : W := ⟨cutW0.s &&& cutW4.s, (cutW0.a ||| cutW4.a), (cutW0.b &&& cutW4.b), (cutW0.a ||| cutW4.a) ||| (cutW0.b &&& cutW4.b), 0⟩
def cutW69 : W := ⟨cutW0.s ||| cutW4.s, (cutW0.a &&& cutW4.a), (cutW0.b ||| cutW4.b), (cutW0.a &&& cutW4.a) ||| (cutW0.b ||| cutW4.b), 0⟩
def cutW70 : W := ⟨cutW0.s &&& cutW5.s, (cutW0.a ||| cutW5.a), (cutW0.b &&& cutW5.b), (cutW0.a ||| cutW5.a) ||| (cutW0.b &&& cutW5.b), 0⟩
def cutW71 : W := ⟨cutW0.s ||| cutW5.s, (cutW0.a &&& cutW5.a), (cutW0.b ||| cutW5.b), (cutW0.a &&& cutW5.a) ||| (cutW0.b ||| cutW5.b), 0⟩
def cutW72 : W := ⟨cutW0.s &&& cutW6.s, (cutW0.a ||| cutW6.a), (cutW0.b &&& cutW6.b), (cutW0.a ||| cutW6.a) ||| (cutW0.b &&& cutW6.b), 0⟩
def cutW73 : W := ⟨cutW0.s ||| cutW6.s, (cutW0.a &&& cutW6.a), (cutW0.b ||| cutW6.b), (cutW0.a &&& cutW6.a) ||| (cutW0.b ||| cutW6.b), 0⟩
def cutW74 : W := ⟨cutW1.s &&& cutW2.s, (cutW1.a ||| cutW2.a), (cutW1.b &&& cutW2.b), (cutW1.a ||| cutW2.a) ||| (cutW1.b &&& cutW2.b), 0⟩
def cutW75 : W := ⟨cutW1.s ||| cutW2.s, (cutW1.a &&& cutW2.a), (cutW1.b ||| cutW2.b), (cutW1.a &&& cutW2.a) ||| (cutW1.b ||| cutW2.b), 0⟩
def cutW76 : W := ⟨cutW1.s &&& cutW3.s, (cutW1.a ||| cutW3.a), (cutW1.b &&& cutW3.b), (cutW1.a ||| cutW3.a) ||| (cutW1.b &&& cutW3.b), 0⟩
def cutW77 : W := ⟨cutW1.s ||| cutW3.s, (cutW1.a &&& cutW3.a), (cutW1.b ||| cutW3.b), (cutW1.a &&& cutW3.a) ||| (cutW1.b ||| cutW3.b), 0⟩
def cutW78 : W := ⟨cutW1.s &&& cutW4.s, (cutW1.a ||| cutW4.a), (cutW1.b &&& cutW4.b), (cutW1.a ||| cutW4.a) ||| (cutW1.b &&& cutW4.b), 0⟩
def cutW79 : W := ⟨cutW1.s ||| cutW4.s, (cutW1.a &&& cutW4.a), (cutW1.b ||| cutW4.b), (cutW1.a &&& cutW4.a) ||| (cutW1.b ||| cutW4.b), 0⟩
def cutW80 : W := ⟨cutW1.s &&& cutW5.s, (cutW1.a ||| cutW5.a), (cutW1.b &&& cutW5.b), (cutW1.a ||| cutW5.a) ||| (cutW1.b &&& cutW5.b), 0⟩
def cutW81 : W := ⟨cutW1.s ||| cutW5.s, (cutW1.a &&& cutW5.a), (cutW1.b ||| cutW5.b), (cutW1.a &&& cutW5.a) ||| (cutW1.b ||| cutW5.b), 0⟩
def cutW82 : W := ⟨cutW1.s &&& cutW6.s, (cutW1.a ||| cutW6.a), (cutW1.b &&& cutW6.b), (cutW1.a ||| cutW6.a) ||| (cutW1.b &&& cutW6.b), 0⟩
def cutW83 : W := ⟨cutW1.s ||| cutW6.s, (cutW1.a &&& cutW6.a), (cutW1.b ||| cutW6.b), (cutW1.a &&& cutW6.a) ||| (cutW1.b ||| cutW6.b), 0⟩
def cutW84 : W := ⟨cutW2.s &&& cutW3.s, (cutW2.a ||| cutW3.a), (cutW2.b &&& cutW3.b), (cutW2.a ||| cutW3.a) ||| (cutW2.b &&& cutW3.b), 0⟩
def cutW85 : W := ⟨cutW2.s ||| cutW3.s, (cutW2.a &&& cutW3.a), (cutW2.b ||| cutW3.b), (cutW2.a &&& cutW3.a) ||| (cutW2.b ||| cutW3.b), 0⟩
def cutW86 : W := ⟨cutW2.s &&& cutW4.s, (cutW2.a ||| cutW4.a), (cutW2.b &&& cutW4.b), (cutW2.a ||| cutW4.a) ||| (cutW2.b &&& cutW4.b), 0⟩
def cutW87 : W := ⟨cutW2.s ||| cutW4.s, (cutW2.a &&& cutW4.a), (cutW2.b ||| cutW4.b), (cutW2.a &&& cutW4.a) ||| (cutW2.b ||| cutW4.b), 0⟩
def cutW88 : W := ⟨cutW2.s &&& cutW5.s, (cutW2.a ||| cutW5.a), (cutW2.b &&& cutW5.b), (cutW2.a ||| cutW5.a) ||| (cutW2.b &&& cutW5.b), 0⟩
def cutW89 : W := ⟨cutW2.s ||| cutW5.s, (cutW2.a &&& cutW5.a), (cutW2.b ||| cutW5.b), (cutW2.a &&& cutW5.a) ||| (cutW2.b ||| cutW5.b), 0⟩
def cutW90 : W := ⟨cutW2.s &&& cutW6.s, (cutW2.a ||| cutW6.a), (cutW2.b &&& cutW6.b), (cutW2.a ||| cutW6.a) ||| (cutW2.b &&& cutW6.b), 0⟩
def cutW91 : W := ⟨cutW2.s ||| cutW6.s, (cutW2.a &&& cutW6.a), (cutW2.b ||| cutW6.b), (cutW2.a &&& cutW6.a) ||| (cutW2.b ||| cutW6.b), 0⟩
def cutW92 : W := ⟨cutW3.s &&& cutW4.s, (cutW3.a ||| cutW4.a), (cutW3.b &&& cutW4.b), (cutW3.a ||| cutW4.a) ||| (cutW3.b &&& cutW4.b), 0⟩
def cutW93 : W := ⟨cutW3.s ||| cutW4.s, (cutW3.a &&& cutW4.a), (cutW3.b ||| cutW4.b), (cutW3.a &&& cutW4.a) ||| (cutW3.b ||| cutW4.b), 0⟩
def cutW94 : W := ⟨cutW3.s &&& cutW5.s, (cutW3.a ||| cutW5.a), (cutW3.b &&& cutW5.b), (cutW3.a ||| cutW5.a) ||| (cutW3.b &&& cutW5.b), 0⟩
def cutW95 : W := ⟨cutW3.s ||| cutW5.s, (cutW3.a &&& cutW5.a), (cutW3.b ||| cutW5.b), (cutW3.a &&& cutW5.a) ||| (cutW3.b ||| cutW5.b), 0⟩
def cutW96 : W := ⟨cutW3.s &&& cutW6.s, (cutW3.a ||| cutW6.a), (cutW3.b &&& cutW6.b), (cutW3.a ||| cutW6.a) ||| (cutW3.b &&& cutW6.b), 0⟩
def cutW97 : W := ⟨cutW3.s ||| cutW6.s, (cutW3.a &&& cutW6.a), (cutW3.b ||| cutW6.b), (cutW3.a &&& cutW6.a) ||| (cutW3.b ||| cutW6.b), 0⟩
def cutW98 : W := ⟨cutW4.s &&& cutW5.s, (cutW4.a ||| cutW5.a), (cutW4.b &&& cutW5.b), (cutW4.a ||| cutW5.a) ||| (cutW4.b &&& cutW5.b), 0⟩
def cutW99 : W := ⟨cutW4.s ||| cutW5.s, (cutW4.a &&& cutW5.a), (cutW4.b ||| cutW5.b), (cutW4.a &&& cutW5.a) ||| (cutW4.b ||| cutW5.b), 0⟩
def cutW100 : W := ⟨cutW4.s &&& cutW6.s, (cutW4.a ||| cutW6.a), (cutW4.b &&& cutW6.b), (cutW4.a ||| cutW6.a) ||| (cutW4.b &&& cutW6.b), 0⟩
def cutW101 : W := ⟨cutW4.s ||| cutW6.s, (cutW4.a &&& cutW6.a), (cutW4.b ||| cutW6.b), (cutW4.a &&& cutW6.a) ||| (cutW4.b ||| cutW6.b), 0⟩
def cutW102 : W := ⟨cutW5.s &&& cutW6.s, (cutW5.a ||| cutW6.a), (cutW5.b &&& cutW6.b), (cutW5.a ||| cutW6.a) ||| (cutW5.b &&& cutW6.b), 0⟩
def cutW103 : W := ⟨cutW5.s ||| cutW6.s, (cutW5.a &&& cutW6.a), (cutW5.b ||| cutW6.b), (cutW5.a &&& cutW6.a) ||| (cutW5.b ||| cutW6.b), 0⟩

noncomputable def forceLook (fuel k t z : ℕ) (v : List W) : Bool :=
  st initL (fun l => st initM (fun m => st initG (fun g => st z (fun z =>
    frc v (fun v => look l m g fuel k t z v)))))
lemma forceLook_eq (fuel k t z : ℕ) (v : List W) :
    forceLook fuel k t z v = look initL initM initG fuel k t z v := by
  simp only [forceLook, st_eq, frc_eq]

def unaryBudget18 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [230708197018389074, 420419470120853591, 491294906390445259, 32995020412329])
def unaryState18 : List W := [cutW0, cutW1, cutW26, cutW2, cutW3, cutW4, cutW5, cutW6]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def unaryOK18 : look initL initM initG 13 11 0 unaryBudget18 unaryState18 = false := by
  have h : forceLook 13 11 0 unaryBudget18 unaryState18 = false := by decide +kernel
  simpa only [forceLook_eq] using h

end PEqualNP.Outside.L_meta_10760
