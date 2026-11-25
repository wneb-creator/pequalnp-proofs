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
def unaryBudget0 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [230708197018389074, 420419470120853591, 491294906390445259, 32995020412329])
def unaryState0 : List W := [cutW0, cutW1, cutW2, cutW3, cutW14, cutW4, cutW5, cutW6]
def unaryBudget1 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [110374062098565714, 590298975281330279, 636044602052309546, 31257367547961])
def unaryState1 : List W := [cutW0, cutW1, cutW2, cutW7, cutW3, cutW14, cutW4, cutW5, cutW6]
def unaryBudget2 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [184437371904281170, 420724443490194876, 19763281279235936, 31311722228878])
def unaryState2 : List W := [cutW0, cutW15, cutW1, cutW2, cutW3, cutW4, cutW5, cutW6]
def unaryBudget3 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [911529250401110546, 969367219919959144, 87578011226008295, 31362679892987])
def unaryState3 : List W := [cutW0, cutW1, cutW2, cutW3, cutW4, cutW5, cutW6, cutW16]
def unaryBudget4 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [791195115481287186, 139246725080435832, 232327706887872583, 29625027028619])
def unaryState4 : List W := [cutW0, cutW1, cutW2, cutW7, cutW3, cutW4, cutW5, cutW6, cutW16]
def unaryBudget5 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [150762638219495986, 856958668830594316, 18313473080857576, 31311722228878])
def unaryState5 : List W := [cutW0, cutW1, cutW17, cutW2, cutW3, cutW4, cutW5, cutW6]
def unaryBudget6 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [139381834126281298, 45299525223600755, 234648598113184588, 31362785900730])
def unaryState6 : List W := [cutW0, cutW1, cutW2, cutW3, cutW18, cutW4, cutW5, cutW6]
def unaryBudget7 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [19047699206457938, 215179030384077443, 379398293775048875, 29625133036362])
def unaryState7 : List W := [cutW0, cutW1, cutW2, cutW7, cutW3, cutW18, cutW4, cutW5, cutW6]
def unaryBudget8 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [247394479131150930, 369778970370654938, 478861659393301110, 31311775257833])
def unaryState8 : List W := [cutW0, cutW1, cutW2, cutW19, cutW3, cutW4, cutW5, cutW6]
def unaryBudget9 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [43363982654128722, 74633452557637161, 696995344228304229, 32998311421442])
def unaryState9 : List W := [cutW0, cutW1, cutW2, cutW3, cutW4, cutW20, cutW5, cutW6]
def unaryBudget10 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [923029847734305362, 244512957718113848, 841745039890168516, 31260658557074])
def unaryState10 : List W := [cutW0, cutW1, cutW2, cutW7, cutW3, cutW4, cutW20, cutW5, cutW6]
def unaryBudget11 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [602823492417701458, 526885104299272262, 388861270631109170, 31313367733435])
def unaryState11 : List W := [cutW0, cutW1, cutW2, cutW21, cutW3, cutW4, cutW5, cutW6]
def unaryBudget12 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [231097916733016658, 181090394380954949, 457900424963365681, 31362683056646])
def unaryState12 : List W := [cutW0, cutW1, cutW2, cutW3, cutW4, cutW5, cutW22, cutW6]
def unaryBudget13 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [110763781813193298, 350969899541431637, 602650120625229968, 29625030192278])
def unaryState13 : List W := [cutW0, cutW1, cutW2, cutW7, cutW3, cutW4, cutW5, cutW22, cutW6]
def unaryBudget14 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [679115806692133458, 867391831851271283, 110416226672591633, 31311723835816])
def unaryState14 : List W := [cutW0, cutW1, cutW2, cutW23, cutW3, cutW4, cutW5, cutW6]
def unaryBudget15 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [994845038935624272, 583644920642956070, 805098195895406886, 32998414267046])
def unaryState15 : List W := [cutW0, cutW1, cutW2, cutW3, cutW4, cutW5, cutW6, cutW24]
def unaryBudget16 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [874510904015800912, 753524425803432758, 949847891557271173, 31260761402678])
def unaryState16 : List W := [cutW0, cutW1, cutW2, cutW7, cutW3, cutW4, cutW5, cutW6, cutW24]
def unaryBudget17 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [785796244455115345, 143747976598488621, 805195773129565019, 31313419155452])
def unaryState17 : List W := [cutW0, cutW1, cutW2, cutW25, cutW3, cutW4, cutW5, cutW6]
def unaryBudget18 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [230708197018389074, 420419470120853591, 491294906390445259, 32995020412329])
def unaryState18 : List W := [cutW0, cutW1, cutW26, cutW2, cutW3, cutW4, cutW5, cutW6]
def unaryBudget19 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [610674036230146578, 52199786479049751, 905441501169618482, 33045978126656])
def unaryState19 : List W := [cutW0, cutW1, cutW2, cutW27, cutW3, cutW4, cutW5, cutW6]
def unaryBudget20 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [615349792191105618, 240510349109129976, 817938116008034262, 33046031055276])
def unaryState20 : List W := [cutW0, cutW1, cutW2, cutW3, cutW28, cutW4, cutW5, cutW6]
def unaryBudget21 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [230023061617066578, 623765441605083925, 568156547829287212, 36364960817299])
def unaryState21 : List W := [cutW0, cutW1, cutW2, cutW3, cutW4, cutW29, cutW5, cutW6]
def unaryBudget22 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [566718455890070098, 444345379926350267, 369778067869131081, 33045979633161])
def unaryState22 : List W := [cutW0, cutW1, cutW2, cutW3, cutW4, cutW5, cutW30, cutW6]
def unaryBudget23 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [443577742547044944, 418752162483210256, 259924896999327819, 36365012240886])
def unaryState23 : List W := [cutW0, cutW1, cutW2, cutW3, cutW4, cutW5, cutW6, cutW31]
def unaryBudget24 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [911529250401110546, 969367219919959144, 87578011226008295, 31362679892987])
def unaryState24 : List W := [cutW0, cutW32, cutW1, cutW2, cutW3, cutW4, cutW5, cutW6]
def unaryBudget25 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [610674036230146578, 52199786479049751, 905441501169618482, 33045978126656])
def unaryState25 : List W := [cutW0, cutW1, cutW33, cutW2, cutW3, cutW4, cutW5, cutW6]
def unaryBudget26 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [586781490622319122, 781054510035502822, 929887686440986837, 31466346683288])
def unaryState26 : List W := [cutW0, cutW1, cutW2, cutW3, cutW34, cutW4, cutW5, cutW6]
def unaryBudget27 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [749686516168344082, 42186294131719739, 209548408789716719, 33047623631211])
def unaryState27 : List W := [cutW0, cutW1, cutW2, cutW3, cutW4, cutW35, cutW5, cutW6]
def unaryBudget28 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [945095384397007378, 133560619274374388, 521538177959526332, 31466295261222])
def unaryState28 : List W := [cutW0, cutW1, cutW2, cutW3, cutW4, cutW5, cutW36, cutW6]
def unaryBudget29 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [255030440084458000, 103003170894788777, 176797372680949077, 33047675056367])
def unaryState29 : List W := [cutW0, cutW1, cutW2, cutW3, cutW4, cutW5, cutW6, cutW37]
def unaryBudget30 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [139381834126281298, 45299525223600755, 234648598113184588, 31362785900730])
def unaryState30 : List W := [cutW0, cutW38, cutW1, cutW2, cutW3, cutW4, cutW5, cutW6]
def unaryBudget31 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [615349792191105618, 240510349109129976, 817938116008034262, 33046031055276])
def unaryState31 : List W := [cutW0, cutW1, cutW39, cutW2, cutW3, cutW4, cutW5, cutW6]
def unaryBudget32 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [586781490622319122, 781054510035502822, 929887686440986837, 31466346683288])
def unaryState32 : List W := [cutW0, cutW1, cutW2, cutW40, cutW3, cutW4, cutW5, cutW6]
def unaryBudget33 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [573544563788300882, 955527617578233269, 122046485172977523, 33047676559831])
def unaryState33 : List W := [cutW0, cutW1, cutW2, cutW3, cutW4, cutW5, cutW41, cutW6]
def unaryBudget34 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [968703822852803154, 675323116061682341, 252319614526285153, 31466349846948])
def unaryState34 : List W := [cutW0, cutW1, cutW2, cutW3, cutW4, cutW5, cutW42, cutW6]
def unaryBudget35 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [206060509095086672, 739824769575042740, 505583183510271141, 33047779407004])
def unaryState35 : List W := [cutW0, cutW1, cutW2, cutW3, cutW4, cutW5, cutW6, cutW43]
def unaryBudget36 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [43363982654128722, 74633452557637161, 696995344228304229, 32998311421442])
def unaryState36 : List W := [cutW0, cutW44, cutW1, cutW2, cutW3, cutW4, cutW5, cutW6]
def unaryBudget37 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [230023061617066578, 623765441605083925, 568156547829287212, 36364960817299])
def unaryState37 : List W := [cutW0, cutW1, cutW45, cutW2, cutW3, cutW4, cutW5, cutW6]
def unaryBudget38 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [749686516168344082, 42186294131719739, 209548408789716719, 33047623631211])
def unaryState38 : List W := [cutW0, cutW1, cutW2, cutW46, cutW3, cutW4, cutW5, cutW6]
def unaryBudget39 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [573544563788300882, 955527617578233269, 122046485172977523, 33047676559831])
def unaryState39 : List W := [cutW0, cutW1, cutW2, cutW3, cutW47, cutW4, cutW5, cutW6]
def unaryBudget40 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [164005664879821394, 655091478459331110, 721775461185889835, 33047625137715])
def unaryState40 : List W := [cutW0, cutW1, cutW2, cutW3, cutW4, cutW5, cutW48, cutW6]
def unaryBudget41 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [412072424055849552, 476144586605860333, 465625334792586658, 36368303249999])
def unaryState41 : List W := [cutW0, cutW1, cutW2, cutW3, cutW4, cutW5, cutW6, cutW49]
def unaryBudget42 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [231097916733016658, 181090394380954949, 457900424963365681, 31362683056646])
def unaryState42 : List W := [cutW0, cutW50, cutW1, cutW2, cutW3, cutW4, cutW5, cutW6]
def unaryBudget43 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [566718455890070098, 444345379926350267, 369778067869131081, 33045979633161])
def unaryState43 : List W := [cutW0, cutW1, cutW51, cutW2, cutW3, cutW4, cutW5, cutW6]
def unaryBudget44 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [945095384397007378, 133560619274374388, 521538177959526332, 31466295261222])
def unaryState44 : List W := [cutW0, cutW1, cutW2, cutW52, cutW3, cutW4, cutW5, cutW6]
def unaryBudget45 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [968703822852803154, 675323116061682341, 252319614526285153, 31466349846948])
def unaryState45 : List W := [cutW0, cutW1, cutW2, cutW3, cutW53, cutW4, cutW5, cutW6]
def unaryBudget46 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [164005664879821394, 655091478459331110, 721775461185889835, 33047625137715])
def unaryState46 : List W := [cutW0, cutW1, cutW2, cutW3, cutW4, cutW54, cutW5, cutW6]
def unaryBudget47 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [299507785502837328, 16180784889832811, 688977702652052281, 33047676562871])
def unaryState47 : List W := [cutW0, cutW1, cutW2, cutW3, cutW4, cutW5, cutW6, cutW55]
def unaryBudget48 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [994845038935624272, 583644920642956070, 805098195895406886, 32998414267046])
def unaryState48 : List W := [cutW0, cutW56, cutW1, cutW2, cutW3, cutW4, cutW5, cutW6]
def unaryBudget49 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [443577742547044944, 418752162483210256, 259924896999327819, 36365012240886])
def unaryState49 : List W := [cutW0, cutW1, cutW57, cutW2, cutW3, cutW4, cutW5, cutW6]
def unaryBudget50 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [255030440084458000, 103003170894788777, 176797372680949077, 33047675056367])
def unaryState50 : List W := [cutW0, cutW1, cutW2, cutW58, cutW3, cutW4, cutW5, cutW6]
def unaryBudget51 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [206060509095086672, 739824769575042740, 505583183510271141, 33047779407004])
def unaryState51 : List W := [cutW0, cutW1, cutW2, cutW3, cutW59, cutW4, cutW5, cutW6]
def unaryBudget52 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [412072424055849552, 476144586605860333, 465625334792586658, 36368303249999])
def unaryState52 : List W := [cutW0, cutW1, cutW2, cutW3, cutW4, cutW60, cutW5, cutW6]
def unaryBudget53 : ℕ := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [299507785502837328, 16180784889832811, 688977702652052281, 33047676562871])
def unaryState53 : List W := [cutW0, cutW1, cutW2, cutW3, cutW4, cutW5, cutW61, cutW6]

def unaryRows : List (ℕ × ℕ × ℕ × List W) := [(11, 0, unaryBudget0, unaryState0), (11, 0, unaryBudget1, unaryState1), (11, 0, unaryBudget2, unaryState2), (11, 0, unaryBudget3, unaryState3), (11, 0, unaryBudget4, unaryState4), (11, 0, unaryBudget5, unaryState5), (11, 0, unaryBudget6, unaryState6), (11, 0, unaryBudget7, unaryState7), (11, 0, unaryBudget8, unaryState8), (11, 0, unaryBudget9, unaryState9), (11, 0, unaryBudget10, unaryState10), (11, 0, unaryBudget11, unaryState11), (11, 0, unaryBudget12, unaryState12), (11, 0, unaryBudget13, unaryState13), (11, 0, unaryBudget14, unaryState14), (11, 0, unaryBudget15, unaryState15), (11, 0, unaryBudget16, unaryState16), (11, 0, unaryBudget17, unaryState17), (11, 0, unaryBudget18, unaryState18), (11, 0, unaryBudget19, unaryState19), (11, 0, unaryBudget20, unaryState20), (11, 0, unaryBudget21, unaryState21), (11, 0, unaryBudget22, unaryState22), (11, 0, unaryBudget23, unaryState23), (11, 0, unaryBudget24, unaryState24), (11, 0, unaryBudget25, unaryState25), (11, 0, unaryBudget26, unaryState26), (11, 0, unaryBudget27, unaryState27), (11, 0, unaryBudget28, unaryState28), (11, 0, unaryBudget29, unaryState29), (11, 0, unaryBudget30, unaryState30), (11, 0, unaryBudget31, unaryState31), (11, 0, unaryBudget32, unaryState32), (11, 0, unaryBudget33, unaryState33), (11, 0, unaryBudget34, unaryState34), (11, 0, unaryBudget35, unaryState35), (11, 0, unaryBudget36, unaryState36), (11, 0, unaryBudget37, unaryState37), (11, 0, unaryBudget38, unaryState38), (11, 0, unaryBudget39, unaryState39), (11, 0, unaryBudget40, unaryState40), (11, 0, unaryBudget41, unaryState41), (11, 0, unaryBudget42, unaryState42), (11, 0, unaryBudget43, unaryState43), (11, 0, unaryBudget44, unaryState44), (11, 0, unaryBudget45, unaryState45), (11, 0, unaryBudget46, unaryState46), (11, 0, unaryBudget47, unaryState47), (11, 0, unaryBudget48, unaryState48), (11, 0, unaryBudget49, unaryState49), (11, 0, unaryBudget50, unaryState50), (11, 0, unaryBudget51, unaryState51), (11, 0, unaryBudget52, unaryState52), (11, 0, unaryBudget53, unaryState53)]

noncomputable def forceLook (fuel k t z : ℕ) (v : List W) : Bool :=
  st initL (fun l => st initM (fun m => st initG (fun g => st z (fun z =>
    frc v (fun v => look l m g fuel k t z v)))))
lemma forceLook_eq (fuel k t z : ℕ) (v : List W) :
    forceLook fuel k t z v = look initL initM initG fuel k t z v := by
  simp only [forceLook, st_eq, frc_eq]


set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def unaryTableChecked : ∀ p ∈ unaryRows,
    look initL initM initG 13 p.1 p.2.1 p.2.2.1 p.2.2.2 = false := by
  intro p hp
  simp only [unaryRows, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    rw [← forceLook_eq]
    decide +kernel

end PEqualNP.Outside.L_meta_10760
