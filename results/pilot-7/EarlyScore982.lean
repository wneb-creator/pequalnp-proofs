import Fast982

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Early
open PEqualNP.Outside.L_meta_982_aux.Finite

def sumLT (f : Nat → Nat) : Nat → List Nat → Bool
  | b,[] => decide (0 < b)
  | b,a::ws => if f a < b then sumLT f (b-f a) ws else false

theorem sumLT_eq (f : Nat → Nat) (b : Nat) (ws : List Nat) :
    sumLT f b ws = decide ((ws.map f).sum < b) := by
  induction ws generalizing b with
  | nil => simp [sumLT]
  | cons a ws ih =>
    simp only [sumLT,List.map_cons,List.sum_cons]
    split
    · rw [ih]
      by_cases hs : (ws.map f).sum < b-f a
      · have ht : f a + (ws.map f).sum < b := by omega
        simp [hs,ht]
      · have ht : ¬ f a + (ws.map f).sum < b := by omega
        simp [hs,ht]
    · symm
      apply decide_eq_false
      omega

def scoreCheck (k width s : Nat) (ws : List Nat) (code : Nat) : Bool :=
  if code = 0 then false else
    ws.length == s+1 &&
      sumLT (Fast.eval6 (Fast.fld code width 0) (Fast.fld code width 1)
        (Fast.fld code width 2) (Fast.fld code width 3) (Fast.fld code width 4)
        (Fast.fld code width 5))
        (Fast.eval6 (Fast.fld code width 0) (Fast.fld code width 1)
          (Fast.fld code width 2) (Fast.fld code width 3) (Fast.fld code width 4)
          (Fast.fld code width 5) (Live.goal k)) ws

theorem scoreCheck_eq (k width s : Nat) (ws : List Nat) (code : Nat) :
    scoreCheck k width s ws code = Reduced.scoreCheckW k width s ws code := by
  rw [←Fast.scoreCheck_eq]
  simp [scoreCheck,Fast.scoreCheck,sumLT_eq]

def scr (k width s : Nat) (pool : List Nat) (ws : List Nat) : Bool :=
  ws.length == s+1 && pool.any (scoreCheck k width s ws)

theorem scr_eq (k width s : Nat) (pool : List Nat) (ws : List Nat) :
    scr k width s pool ws = Reduced.scrW k width s pool ws := by
  have he : scoreCheck k width s ws = Reduced.scoreCheckW k width s ws := by
    funext code
    exact scoreCheck_eq k width s ws code
  simp only [scr,Reduced.scrW,he]

end PEqualNP.Outside.L_meta_982_aux.Finite.Early
