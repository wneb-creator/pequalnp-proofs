import Mathlib.Data.List.GetD

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
theorem PEqualNP.Outside.R_meta_4930_719
    (search : let xs : List (BitVec 58) := [95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752]
      ∃ gs : List (Bool × ℕ × ℕ), gs.length = 19 ∧
        (∀ j : Fin gs.length, (gs.getD j.val (false,0,0)).2.1 < (gs.getD j.val (false,0,0)).2.2 ∧
          (gs.getD j.val (false,0,0)).2.2 < 14+j.val) ∧
        ((gs.foldl (fun (w : List (BitVec 58)) (g : Bool × ℕ × ℕ) => w ++ [if g.1 = true then w.getD g.2.1 0 &&& w.getD g.2.2 0 else w.getD g.2.1 0 ||| w.getD g.2.2 0]) xs).getD 32 0 &&& 288230376149614591) = (2097151 : BitVec 58))
    (mask : (288160007407550752 : BitVec 58) ||| ((270286071508633728 : BitVec 58) ||| ((229736628138025984 : BitVec 58) ||| ((183565875465490436 : BitVec 58) ||| ((218994303132270608 : BitVec 58) ||| ((189297016294081033 : BitVec 58) ||| (155696362464477250 : BitVec 58)))))) = 288230376149614591) :
    have x1 : List (BitVec (58 : ℕ)) := [(95229015649943559 : BitVec (58 : ℕ)), (63038587666488 : BitVec (58 : ℕ)), (256462815680 : BitVec (58 : ℕ)), (4292497062759936 : BitVec (58 : ℕ)), (8521481482240 : BitVec (58 : ℕ)), (14003410187812864 : BitVec (58 : ℕ)), (55389823207997440 : BitVec (58 : ℕ)), (189297016294081033 : BitVec (58 : ℕ)), (155696362464477250 : BitVec (58 : ℕ)), (218994303132270608 : BitVec (58 : ℕ)), (183565875465490436 : BitVec (58 : ℕ)), (229736628138025984 : BitVec (58 : ℕ)), (270286071508633728 : BitVec (58 : ℕ)), (288160007407550752 : BitVec (58 : ℕ))]; ∃ (x2 : List (Bool × ℕ × ℕ)), x2.length = (26 : ℕ) ∧ (∀ (x3 : Fin x2.length), (x2.getD ↑x3 (Bool.false, (0 : ℕ), (0 : ℕ))).2.1 < (x2.getD ↑x3 (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 ∧ (x2.getD ↑x3 (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 < (14 : ℕ) + ↑x3) ∧ (2097151 : BitVec (58 : ℕ)) ∈ List.foldl (fun (x3 : List (BitVec (58 : ℕ))) (x4 : Bool × ℕ × ℕ) => x3 ++ [if x4.1 = Bool.true then x3.getD x4.2.1 (0 : BitVec (58 : ℕ)) &&& x3.getD x4.2.2 (0 : BitVec (58 : ℕ)) else x3.getD x4.2.1 (0 : BitVec (58 : ℕ)) ||| x3.getD x4.2.2 (0 : BitVec (58 : ℕ))]) x1 x2 := by
  let xs : List (BitVec 58) := [95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752]
  let step := (fun (w : List (BitVec 58)) (g : Bool × ℕ × ℕ) => w ++ [if g.1 = true then w.getD g.2.1 0 &&& w.getD g.2.2 0 else w.getD g.2.1 0 ||| w.getD g.2.2 0])
  change ∃ gs : List (Bool × ℕ × ℕ), gs.length = 19 ∧
      (∀ j : Fin gs.length, (gs.getD j.val (false,0,0)).2.1 < (gs.getD j.val (false,0,0)).2.2 ∧
        (gs.getD j.val (false,0,0)).2.2 < 14+j.val) ∧
      ((gs.foldl step xs).getD 32 0 &&& 288230376149614591) = (2097151 : BitVec 58) at search
  obtain ⟨gs, hlen, hvalid, hvalue⟩ := search
  let tail : List (Bool × ℕ × ℕ) := [(false,7,8),(false,9,33),(false,10,34),
    (false,11,35),(false,12,36),(false,13,37),(true,32,38)]
  have extend (ts : List (Bool × ℕ × ℕ)) (w : List (BitVec 58)) :
      ∃ u, ts.foldl step w = w ++ u ∧ u.length = ts.length := by
    induction ts generalizing w with
    | nil => exact ⟨[], by simp, rfl⟩
    | cons g ts ih =>
      obtain ⟨u, hu, hsize⟩ := ih (step w g)
      refine ⟨(if g.1 = true then w.getD g.2.1 0 &&& w.getD g.2.2 0 else
        w.getD g.2.1 0 ||| w.getD g.2.2 0) :: u, ?_, by simp [hsize]⟩
      simpa [List.foldl_cons, step, List.append_assoc] using hu
  obtain ⟨u, hu, hulen⟩ := extend gs xs
  have hwlen : (gs.foldl step xs).length = 33 := by rw [hu, List.length_append, hulen, hlen]; rfl
  have hkeep (i : ℕ) (hi : i < 14) : (gs.foldl step xs).getD i 0 = xs.getD i 0 := by
    rw [hu, List.getD_append _ _ _ _ (by exact hi)]
  have htail : ∀ j : Fin tail.length,
      (tail.getD j.val (false,0,0)).2.1 < (tail.getD j.val (false,0,0)).2.2 ∧
      (tail.getD j.val (false,0,0)).2.2 < 33+j.val := by decide
  change ∃ ops : List (Bool × ℕ × ℕ), ops.length = 26 ∧
    (∀ j : Fin ops.length, (ops.getD j.val (false,0,0)).2.1 < (ops.getD j.val (false,0,0)).2.2 ∧
      (ops.getD j.val (false,0,0)).2.2 < 14+j.val) ∧
    (2097151 : BitVec 58) ∈ ops.foldl step xs
  refine ⟨gs ++ tail, by simp [tail, hlen], ?_, ?_⟩
  · intro j
    by_cases hj : j.val < gs.length
    · simpa only [List.getD_append _ _ _ _ hj] using hvalid ⟨j.val,hj⟩
    · have hle : gs.length ≤ j.val := by omega
      have hk : j.val - gs.length < tail.length := by have := j.isLt; simp only [List.length_append] at this; omega
      have hh := htail ⟨j.val-gs.length,hk⟩
      rw [List.getD_append_right _ _ _ _ hle]
      dsimp only at hh
      constructor
      · exact hh.1
      · have := hh.2; omega
  · rw [List.foldl_append]
    have heval (w : List (BitVec 58)) (hw : w.length = 33) :
        tail.foldl step w = w ++ [w.getD 7 0 ||| w.getD 8 0,w.getD 9 0 ||| (w.getD 7 0 ||| w.getD 8 0),w.getD 10 0 ||| (w.getD 9 0 ||| (w.getD 7 0 ||| w.getD 8 0)),w.getD 11 0 ||| (w.getD 10 0 ||| (w.getD 9 0 ||| (w.getD 7 0 ||| w.getD 8 0))),w.getD 12 0 ||| (w.getD 11 0 ||| (w.getD 10 0 ||| (w.getD 9 0 ||| (w.getD 7 0 ||| w.getD 8 0)))),w.getD 13 0 ||| (w.getD 12 0 ||| (w.getD 11 0 ||| (w.getD 10 0 ||| (w.getD 9 0 ||| (w.getD 7 0 ||| w.getD 8 0))))),w.getD 32 0 &&& (w.getD 13 0 ||| (w.getD 12 0 ||| (w.getD 11 0 ||| (w.getD 10 0 ||| (w.getD 9 0 ||| (w.getD 7 0 ||| w.getD 8 0))))))] := by
      simp [tail, step, hw, List.append_assoc]
    rw [heval _ hwlen]
    have hr : (gs.foldl step xs).getD 13 0 ||| ((gs.foldl step xs).getD 12 0 ||| ((gs.foldl step xs).getD 11 0 ||| ((gs.foldl step xs).getD 10 0 ||| ((gs.foldl step xs).getD 9 0 ||| ((gs.foldl step xs).getD 7 0 ||| (gs.foldl step xs).getD 8 0))))) = 288230376149614591 := by
      simp only [hkeep 13 (by decide), hkeep 12 (by decide), hkeep 11 (by decide),
        hkeep 10 (by decide), hkeep 9 (by decide), hkeep 7 (by decide), hkeep 8 (by decide)]
      simpa only [xs, List.getD_cons_succ, List.getD_cons_zero] using mask
    rw [hr, hvalue]
    simp
