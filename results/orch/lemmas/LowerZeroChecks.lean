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


noncomputable section cutCore
def topCut (F G : Nat → Nat → Nat → List W → Bool) (l m g K H ph k t z : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) (tst (pos t) l (Nat.sub (Nat.succ k) t) v (fun y =>
    Bool.rec (motive := fun _ => Bool) (Bool.rec (motive := fun _ => Bool) false (mv F l m g k t z v y) (Nat.beq ph 1)) true
      (node (G (Nat.sub k 1) t) (pos t) l m g (Nat.sub (Nat.sub k t) y) v.length z v (fun h xs => pairsC H h (fs xs))))) true (Nat.ble v.length 1)
def startCut (F G : Nat → Nat → Nat → List W → Bool) (l m g B K t p H ph : ℕ) (v : List W) : Bool :=
  Bool.rec (motive := fun _ => Bool) false (Bool.rec (motive := fun _ => Bool) false
    (child (fun z r => topCut F G l m g K H ph K t z r) g (fun h => h v) (Nat.sub B (sumc v)))
    (Nat.ble v.length (Nat.sub (Nat.succ K) t))) (hasP p v)
end cutCore
noncomputable def chkCut (F G : Nat → Nat → Nat → List W → Bool) (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) : Bool :=
  (fun l => (fun m => (fun P => (fun g => (fun B => (fun p =>
    frc (avl P m (rawL E)) (fun v => st l fun l => st m fun m => st g fun g => st B fun B => st p fun p =>
      anySub (pos t) l v 0 (fun r => startCut F G l m g B K t p H ph r)))
    (pwr E Z)) (pL (Q.map fun e => 16 + (K - e.2)))) (pL (Q.map fun _ => 16))) (PZ Q)) (mz Z)) (lz Z)

lemma chkCut_eq (E Q : List (ℕ × ℕ)) (Z K t H ph : ℕ) :
    chkCut (look (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K)
      (look1 (lz Z) (mz Z) (pL (Q.map fun _ => 16)) K K) E Q Z K t H ph =
      chk E Q Z K t H ph := by
  simp only [chkCut, chk, frc_eq, st_eq, startCut, startv, topCut, topC]

lemma orFold_append {α : Type} (p : α → Bool) (xs ys : List α) :
    List.rec false (fun a _ ih => Bool.rec ih true (p a)) (xs ++ ys) =
      (List.rec false (fun a _ ih => Bool.rec ih true (p a)) xs ||
        List.rec false (fun a _ ih => Bool.rec ih true (p a)) ys) := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simp only [List.cons_append]
    rw [ih]
    cases p a <;> rfl

lemma nots_append (f : Nat → Nat → List W → Bool) (m g e n z q : Nat)
    (v xs ys : List W) :
    nots f m g e n z q v (xs ++ ys) =
      (nots f m g e n z q v xs || nots f m g e n z q v ys) := by
  exact orFold_append _ xs ys

lemma nots_false_of_singletons (f : Nat → Nat → List W → Bool) (m g e n z q : Nat)
    (v xs : List W) (h : ∀ w ∈ xs, nots f m g e n z q v [w] = false) :
    nots f m g e n z q v xs = false := by
  revert h
  induction xs with
  | nil => intro _; rfl
  | cons a xs ih =>
    intro h
    have ha := h a (List.mem_cons_self)
    have hr := ih (fun w hw => h w (List.mem_cons_of_mem _ hw))
    change nots f m g e n z q v ([a] ++ xs) = false
    rw [nots_append, ha, hr]
    rfl

abbrev WKey := Nat × Nat × Nat × Nat × Nat
abbrev CutState := Nat × Nat × Nat × List W
abbrev CutKey := Nat × Nat × Nat × List WKey

def wKey (w : W) : WKey := (w.s, w.a, w.b, w.c, w.r)
def wUnkey (w : WKey) : W := ⟨w.1, w.2.1, w.2.2.1, w.2.2.2.1, w.2.2.2.2⟩
def cutKey (s : CutState) : CutKey := (s.1, s.2.1, s.2.2.1, s.2.2.2.map wKey)
def cutUnkey (s : CutKey) : CutState := (s.1, s.2.1, s.2.2.1, s.2.2.2.map wUnkey)

lemma wUnkey_key (w : W) : wUnkey (wKey w) = w := by cases w; rfl
lemma cutUnkey_key (s : CutState) : cutUnkey (cutKey s) = s := by
  rcases s with ⟨k, t, z, v⟩
  simp only [cutUnkey, cutKey, List.map_map, Function.comp_def, wUnkey_key]
  change (k, t, z, List.map id v) = (k, t, z, v)
  rw [List.map_id]

lemma cutKey_injective : Function.Injective cutKey := by
  intro s t h
  have h' := congrArg cutUnkey h
  simpa only [cutUnkey_key] using h'

def patchCut (F : Nat → Nat → Nat → List W → Bool) (states : List CutState)
    (k t z : Nat) (v : List W) : Bool :=
  if cutKey (k, t, z, v) ∈ states.map cutKey then false else F k t z v

lemma patchCut_eq (F : Nat → Nat → Nat → List W → Bool) (states : List CutState)
    (h : ∀ s ∈ states, F s.1 s.2.1 s.2.2.1 s.2.2.2 = false) :
    patchCut F states = F := by
  funext k t z v
  unfold patchCut
  split_ifs with hm
  · obtain ⟨s, hs, he⟩ := List.mem_map.1 hm
    have he := cutKey_injective he
    subst s
    exact (h (k, t, z, v) hs).symm
  · rfl

def low0W0 : W := initW0
def low0W1 : W := initW1
def low0W2 : W := initW2
def low0W3 : W := initW3
def low0W4 : W := initW4
def low0W5 : W := initW5
def low0W6 : W := initW6
def low0W7 : W := ⟨low0W0.s ||| low0W1.s, (low0W0.a &&& low0W1.a), (low0W0.b ||| low0W1.b), (low0W0.a &&& low0W1.a) ||| (low0W0.b ||| low0W1.b), 0⟩
def low0W8 : W := ⟨low0W0.s ||| low0W2.s, (low0W0.a &&& low0W2.a), (low0W0.b ||| low0W2.b), (low0W0.a &&& low0W2.a) ||| (low0W0.b ||| low0W2.b), 0⟩
def low0W9 : W := ⟨low0W0.s ||| low0W3.s, (low0W0.a &&& low0W3.a), (low0W0.b ||| low0W3.b), (low0W0.a &&& low0W3.a) ||| (low0W0.b ||| low0W3.b), 0⟩
def low0W10 : W := ⟨low0W0.s ||| low0W4.s, (low0W0.a &&& low0W4.a), (low0W0.b ||| low0W4.b), (low0W0.a &&& low0W4.a) ||| (low0W0.b ||| low0W4.b), 0⟩
def low0W11 : W := ⟨low0W0.s ||| low0W5.s, (low0W0.a &&& low0W5.a), (low0W0.b ||| low0W5.b), (low0W0.a &&& low0W5.a) ||| (low0W0.b ||| low0W5.b), 0⟩
def low0W12 : W := ⟨low0W0.s ||| low0W6.s, (low0W0.a &&& low0W6.a), (low0W0.b ||| low0W6.b), (low0W0.a &&& low0W6.a) ||| (low0W0.b ||| low0W6.b), 0⟩
def low0W13 : W := ⟨low0W1.s ||| low0W2.s, (low0W1.a &&& low0W2.a), (low0W1.b ||| low0W2.b), (low0W1.a &&& low0W2.a) ||| (low0W1.b ||| low0W2.b), 0⟩
def low0W14 : W := ⟨low0W1.s ||| low0W3.s, (low0W1.a &&& low0W3.a), (low0W1.b ||| low0W3.b), (low0W1.a &&& low0W3.a) ||| (low0W1.b ||| low0W3.b), 0⟩
def low0W15 : W := ⟨low0W1.s ||| low0W4.s, (low0W1.a &&& low0W4.a), (low0W1.b ||| low0W4.b), (low0W1.a &&& low0W4.a) ||| (low0W1.b ||| low0W4.b), 0⟩
def low0W16 : W := ⟨low0W1.s ||| low0W5.s, (low0W1.a &&& low0W5.a), (low0W1.b ||| low0W5.b), (low0W1.a &&& low0W5.a) ||| (low0W1.b ||| low0W5.b), 0⟩
def low0W17 : W := ⟨low0W1.s ||| low0W6.s, (low0W1.a &&& low0W6.a), (low0W1.b ||| low0W6.b), (low0W1.a &&& low0W6.a) ||| (low0W1.b ||| low0W6.b), 0⟩
def low0W18 : W := ⟨low0W2.s ||| low0W3.s, (low0W2.a &&& low0W3.a), (low0W2.b ||| low0W3.b), (low0W2.a &&& low0W3.a) ||| (low0W2.b ||| low0W3.b), 0⟩
def low0W19 : W := ⟨low0W2.s ||| low0W4.s, (low0W2.a &&& low0W4.a), (low0W2.b ||| low0W4.b), (low0W2.a &&& low0W4.a) ||| (low0W2.b ||| low0W4.b), 0⟩
def low0W20 : W := ⟨low0W2.s ||| low0W5.s, (low0W2.a &&& low0W5.a), (low0W2.b ||| low0W5.b), (low0W2.a &&& low0W5.a) ||| (low0W2.b ||| low0W5.b), 0⟩
def low0W21 : W := ⟨low0W2.s ||| low0W6.s, (low0W2.a &&& low0W6.a), (low0W2.b ||| low0W6.b), (low0W2.a &&& low0W6.a) ||| (low0W2.b ||| low0W6.b), 0⟩
def low0W22 : W := ⟨low0W3.s ||| low0W4.s, (low0W3.a &&& low0W4.a), (low0W3.b ||| low0W4.b), (low0W3.a &&& low0W4.a) ||| (low0W3.b ||| low0W4.b), 0⟩
def low0W23 : W := ⟨low0W3.s ||| low0W5.s, (low0W3.a &&& low0W5.a), (low0W3.b ||| low0W5.b), (low0W3.a &&& low0W5.a) ||| (low0W3.b ||| low0W5.b), 0⟩
def low0W24 : W := ⟨low0W3.s ||| low0W6.s, (low0W3.a &&& low0W6.a), (low0W3.b ||| low0W6.b), (low0W3.a &&& low0W6.a) ||| (low0W3.b ||| low0W6.b), 0⟩
def low0W25 : W := ⟨low0W4.s ||| low0W5.s, (low0W4.a &&& low0W5.a), (low0W4.b ||| low0W5.b), (low0W4.a &&& low0W5.a) ||| (low0W4.b ||| low0W5.b), 0⟩
def low0W26 : W := ⟨low0W4.s ||| low0W6.s, (low0W4.a &&& low0W6.a), (low0W4.b ||| low0W6.b), (low0W4.a &&& low0W6.a) ||| (low0W4.b ||| low0W6.b), 0⟩
def low0W27 : W := ⟨low0W5.s ||| low0W6.s, (low0W5.a &&& low0W6.a), (low0W5.b ||| low0W6.b), (low0W5.a &&& low0W6.a) ||| (low0W5.b ||| low0W6.b), 0⟩
def low0Budget0 : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [961808777725658673, 257269424364498982, 489798328712424618, 32995020412329])
def low0State0 : List W := [low0W7, low0W0, low0W1, low0W2, low0W3, low0W4, low0W5, low0W6]
def low0Budget1 : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [676304564793165329, 369982948823205096, 87531241746366014, 31362679892987])
def low0State1 : List W := [low0W8, low0W0, low0W1, low0W2, low0W3, low0W4, low0W5, low0W6]
def low0Budget2 : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [807525307606681137, 933094952586786084, 774053642321098772, 31362732871774])
def low0State2 : List W := [low0W9, low0W0, low0W1, low0W2, low0W3, low0W4, low0W5, low0W6]
def low0Budget3 : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [356078442847978033, 805322745992205166, 326400777198410353, 32996665916885])
def low0State3 : List W := [low0W10, low0W0, low0W1, low0W2, low0W3, low0W4, low0W5, low0W6]
def low0Budget4 : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [467520062652433969, 571272960263523933, 365750901891989342, 31362681449708])
def low0State4 : List W := [low0W11, low0W0, low0W1, low0W2, low0W3, low0W4, low0W5, low0W6]
def low0Budget5 : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [124586747092059696, 697471341778307717, 18169126367057162, 32996717340472])
def low0State5 : List W := [low0W12, low0W0, low0W1, low0W2, low0W3, low0W4, low0W5, low0W6]
def low0Budget6 : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [722575389907273233, 369677975453863811, 559062866857575337, 33045978076438])
def low0State6 : List W := [low0W0, low0W13, low0W1, low0W2, low0W3, low0W4, low0W5, low0W6]
def low0Budget7 : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [853796132720789041, 932789979217444799, 245585267432308095, 33046031055226])
def low0State7 : List W := [low0W0, low0W14, low0W1, low0W2, low0W3, low0W4, low0W5, low0W6]
def low0Budget8 : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [402349267962085937, 805017772622863881, 797932402309619676, 34679964100336])
def low0State8 : List W := [low0W0, low0W15, low0W1, low0W2, low0W3, low0W4, low0W5, low0W6]
def low0Budget9 : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [513790887766541873, 570967986894182648, 837282527003198665, 33045979633159])
def low0State9 : List W := [low0W0, low0W16, low0W1, low0W2, low0W3, low0W4, low0W5, low0W6]
def low0Budget10 : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [170857572206167600, 697166368408966432, 489700751478266485, 34680015523923])
def low0State10 : List W := [low0W0, low0W17, low0W1, low0W2, low0W3, low0W4, low0W5, low0W6]
def low0Budget11 : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [568291919788295697, 45503503676150913, 843318180466249492, 31413690535883])
def low0State11 : List W := [low0W0, low0W1, low0W18, low0W2, low0W3, low0W4, low0W5, low0W6]
def low0Budget12 : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [116845055029592593, 917731297081569995, 395665315343561072, 33047623580994])
def low0State12 : List W := [low0W0, low0W1, low0W19, low0W2, low0W3, low0W4, low0W5, low0W6]
def low0Budget13 : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [228286674834048529, 683681511352888762, 435015440037140061, 31413639113817])
def low0State13 : List W := [low0W0, low0W1, low0W20, low0W2, low0W3, low0W4, low0W5, low0W6]
def low0Budget14 : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [885353359273674256, 809879892867672545, 87433664512207881, 33047675004581])
def low0State14 : List W := [low0W0, low0W1, low0W21, low0W2, low0W3, low0W4, low0W5, low0W6]
def low0Budget15 : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [248065797843108401, 480843300845150983, 82187715918293831, 33047676559782])
def low0State15 : List W := [low0W0, low0W1, low0W2, low0W22, low0W3, low0W4, low0W5, low0W6]
def low0Budget16 : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [359507417647564337, 246793515116469750, 121537840611872820, 31413692092605])
def low0State16 : List W := [low0W0, low0W1, low0W2, low0W23, low0W3, low0W4, low0W5, low0W6]
def low0Budget17 : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [16574102087190064, 372991896631253534, 773956065086940640, 33047727983368])
def low0State17 : List W := [low0W0, low0W1, low0W2, low0W24, low0W3, low0W4, low0W5, low0W6]
def low0Budget18 : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [908060552888861233, 119021308521888831, 673884975489184401, 33047625137715])
def low0State18 : List W := [low0W0, low0W1, low0W2, low0W3, low0W25, low0W4, low0W5, low0W6]
def low0Budget19 : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [565127237328486960, 245219690036672615, 326303199964252221, 34681661028479])
def low0State19 : List W := [low0W0, low0W1, low0W2, low0W3, low0W26, low0W4, low0W5, low0W6]
def low0Budget20 : Nat := (List.foldr (fun a b => a + b * 1000000000000000000) 0 [676568857132942896, 11169904307991382, 365653324657831210, 33047676561302])
def low0State20 : List W := [low0W0, low0W1, low0W2, low0W3, low0W4, low0W27, low0W5, low0W6]
def low0Rows : List CutState := [(11, 0, low0Budget0, low0State0), (11, 0, low0Budget1, low0State1), (11, 0, low0Budget2, low0State2), (11, 0, low0Budget3, low0State3), (11, 0, low0Budget4, low0State4), (11, 0, low0Budget5, low0State5), (11, 0, low0Budget6, low0State6), (11, 0, low0Budget7, low0State7), (11, 0, low0Budget8, low0State8), (11, 0, low0Budget9, low0State9), (11, 0, low0Budget10, low0State10), (11, 0, low0Budget11, low0State11), (11, 0, low0Budget12, low0State12), (11, 0, low0Budget13, low0State13), (11, 0, low0Budget14, low0State14), (11, 0, low0Budget15, low0State15), (11, 0, low0Budget16, low0State16), (11, 0, low0Budget17, low0State17), (11, 0, low0Budget18, low0State18), (11, 0, low0Budget19, low0State19), (11, 0, low0Budget20, low0State20)]

noncomputable def lowForceLook1 (K fuel k t z : Nat) (v : List W) : Bool :=
  st initL (fun l => st initM (fun m => st initG (fun g => st z (fun z =>
    frc v (fun v => look1 l m g K fuel k t z v)))))
lemma lowForceLook1_eq (K fuel k t z : Nat) (v : List W) :
    lowForceLook1 K fuel k t z v = look1 initL initM initG K fuel k t z v := by
  simp only [lowForceLook1, st_eq, frc_eq]
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def low0OK0 : look1 initL initM initG 12 12 11 0 low0Budget0 low0State0 = false := by
  have h : lowForceLook1 12 12 11 0 low0Budget0 low0State0 = false := by decide +kernel
  simpa only [lowForceLook1_eq] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def low0OK1 : look1 initL initM initG 12 12 11 0 low0Budget1 low0State1 = false := by
  have h : lowForceLook1 12 12 11 0 low0Budget1 low0State1 = false := by decide +kernel
  simpa only [lowForceLook1_eq] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def low0OK2 : look1 initL initM initG 12 12 11 0 low0Budget2 low0State2 = false := by
  have h : lowForceLook1 12 12 11 0 low0Budget2 low0State2 = false := by decide +kernel
  simpa only [lowForceLook1_eq] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def low0OK3 : look1 initL initM initG 12 12 11 0 low0Budget3 low0State3 = false := by
  have h : lowForceLook1 12 12 11 0 low0Budget3 low0State3 = false := by decide +kernel
  simpa only [lowForceLook1_eq] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def low0OK4 : look1 initL initM initG 12 12 11 0 low0Budget4 low0State4 = false := by
  have h : lowForceLook1 12 12 11 0 low0Budget4 low0State4 = false := by decide +kernel
  simpa only [lowForceLook1_eq] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def low0OK5 : look1 initL initM initG 12 12 11 0 low0Budget5 low0State5 = false := by
  have h : lowForceLook1 12 12 11 0 low0Budget5 low0State5 = false := by decide +kernel
  simpa only [lowForceLook1_eq] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def low0OK6 : look1 initL initM initG 12 12 11 0 low0Budget6 low0State6 = false := by
  have h : lowForceLook1 12 12 11 0 low0Budget6 low0State6 = false := by decide +kernel
  simpa only [lowForceLook1_eq] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def low0OK7 : look1 initL initM initG 12 12 11 0 low0Budget7 low0State7 = false := by
  have h : lowForceLook1 12 12 11 0 low0Budget7 low0State7 = false := by decide +kernel
  simpa only [lowForceLook1_eq] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def low0OK8 : look1 initL initM initG 12 12 11 0 low0Budget8 low0State8 = false := by
  have h : lowForceLook1 12 12 11 0 low0Budget8 low0State8 = false := by decide +kernel
  simpa only [lowForceLook1_eq] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def low0OK9 : look1 initL initM initG 12 12 11 0 low0Budget9 low0State9 = false := by
  have h : lowForceLook1 12 12 11 0 low0Budget9 low0State9 = false := by decide +kernel
  simpa only [lowForceLook1_eq] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def low0OK10 : look1 initL initM initG 12 12 11 0 low0Budget10 low0State10 = false := by
  have h : lowForceLook1 12 12 11 0 low0Budget10 low0State10 = false := by decide +kernel
  simpa only [lowForceLook1_eq] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def low0OK11 : look1 initL initM initG 12 12 11 0 low0Budget11 low0State11 = false := by
  have h : lowForceLook1 12 12 11 0 low0Budget11 low0State11 = false := by decide +kernel
  simpa only [lowForceLook1_eq] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def low0OK12 : look1 initL initM initG 12 12 11 0 low0Budget12 low0State12 = false := by
  have h : lowForceLook1 12 12 11 0 low0Budget12 low0State12 = false := by decide +kernel
  simpa only [lowForceLook1_eq] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def low0OK13 : look1 initL initM initG 12 12 11 0 low0Budget13 low0State13 = false := by
  have h : lowForceLook1 12 12 11 0 low0Budget13 low0State13 = false := by decide +kernel
  simpa only [lowForceLook1_eq] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def low0OK14 : look1 initL initM initG 12 12 11 0 low0Budget14 low0State14 = false := by
  have h : lowForceLook1 12 12 11 0 low0Budget14 low0State14 = false := by decide +kernel
  simpa only [lowForceLook1_eq] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def low0OK15 : look1 initL initM initG 12 12 11 0 low0Budget15 low0State15 = false := by
  have h : lowForceLook1 12 12 11 0 low0Budget15 low0State15 = false := by decide +kernel
  simpa only [lowForceLook1_eq] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def low0OK16 : look1 initL initM initG 12 12 11 0 low0Budget16 low0State16 = false := by
  have h : lowForceLook1 12 12 11 0 low0Budget16 low0State16 = false := by decide +kernel
  simpa only [lowForceLook1_eq] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def low0OK17 : look1 initL initM initG 12 12 11 0 low0Budget17 low0State17 = false := by
  have h : lowForceLook1 12 12 11 0 low0Budget17 low0State17 = false := by decide +kernel
  simpa only [lowForceLook1_eq] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def low0OK18 : look1 initL initM initG 12 12 11 0 low0Budget18 low0State18 = false := by
  have h : lowForceLook1 12 12 11 0 low0Budget18 low0State18 = false := by decide +kernel
  simpa only [lowForceLook1_eq] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def low0OK19 : look1 initL initM initG 12 12 11 0 low0Budget19 low0State19 = false := by
  have h : lowForceLook1 12 12 11 0 low0Budget19 low0State19 = false := by decide +kernel
  simpa only [lowForceLook1_eq] using h

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def low0OK20 : look1 initL initM initG 12 12 11 0 low0Budget20 low0State20 = false := by
  have h : lowForceLook1 12 12 11 0 low0Budget20 low0State20 = false := by decide +kernel
  simpa only [lowForceLook1_eq] using h

lemma low0Checked : ∀ s ∈ low0Rows,
    look1 initL initM initG 12 12 s.1 s.2.1 s.2.2.1 s.2.2.2 = false := by
  intro s hs
  simp only [low0Rows, List.mem_cons, List.not_mem_nil, or_false] at hs
  rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact low0OK0
  · exact low0OK1
  · exact low0OK2
  · exact low0OK3
  · exact low0OK4
  · exact low0OK5
  · exact low0OK6
  · exact low0OK7
  · exact low0OK8
  · exact low0OK9
  · exact low0OK10
  · exact low0OK11
  · exact low0OK12
  · exact low0OK13
  · exact low0OK14
  · exact low0OK15
  · exact low0OK16
  · exact low0OK17
  · exact low0OK18
  · exact low0OK19
  · exact low0OK20
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
def low0Coverage (F G : Nat → Nat → Nat → List W → Bool) :
    chkCut F (patchCut G low0Rows) [] (pr ac4 0) 0 12 0 FF 1 = false := by
  rfl
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma low0Root : chk [] (pr ac4 0) 0 12 0 FF 1 = false := by
  have hl : lz 0 = initL := by rfl
  have hm : mz 0 = initM := by rfl
  have hg : pL ((pr ac4 0).map fun _ => 16) = initG := by rfl
  have hG : ∀ s ∈ low0Rows,
      look1 (lz 0) (mz 0) (pL ((pr ac4 0).map fun _ => 16)) 12 12
        s.1 s.2.1 s.2.2.1 s.2.2.2 = false := by
    rw [hl, hm, hg]
    exact low0Checked
  have h := low0Coverage
    (look (lz 0) (mz 0) (pL ((pr ac4 0).map fun _ => 16)) 12)
    (look1 (lz 0) (mz 0) (pL ((pr ac4 0).map fun _ => 16)) 12 12)
  rw [patchCut_eq _ low0Rows hG] at h
  exact (chkCut_eq [] (pr ac4 0) 0 12 0 FF 1).symm.trans h

end PEqualNP.Outside.L_meta_10760
