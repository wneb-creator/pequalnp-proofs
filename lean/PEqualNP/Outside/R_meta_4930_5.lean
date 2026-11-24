import Mathlib.Data.BitVec
import Mathlib.Data.List.GetD
import Mathlib.Tactic.NormNum

set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.R_meta_4930_5
    (search : let a : List (BitVec 24) := [4788227,2641932,208944,348352,62208,1588224,9609285,10798098,13043976,16253600]
    ∃ gs : List (Bool × ℕ × ℕ), gs.length = 14 ∧
      (∀ i : Fin gs.length, (gs.getD i (false,0,0)).2.1 < (gs.getD i (false,0,0)).2.2 ∧
        (gs.getD i (false,0,0)).2.2 < 10 + i.val) ∧
      (gs.foldl (fun (xs : List (BitVec 24)) (g : Bool × ℕ × ℕ) => xs ++ [if g.1 = true then xs.getD g.2.1 0 &&& xs.getD g.2.2 0 else xs.getD g.2.1 0 ||| xs.getD g.2.2 0]) a).getD 23 0 = 4095)
    (rows : let a : List (BitVec 24) := [4788227,2641932,208944,348352,62208,1588224,9609285,10798098,13043976,16253600]
    let b : List (BitVec 58) := [95229015649943559,63038587666488,256462815680,4292497062759936,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,270286071508633728]
    ∀ j : Fin 58, ∃ k : Fin 24,
      if (953051 : BitVec 58).getLsbD j then
        (4095 : BitVec 24).getLsbD k = true ∧
          ∀ i : Fin 10, (a.getD i 0).getLsbD k ≤ (b.getD i 0).getLsbD j
      else
        (4095 : BitVec 24).getLsbD k = false ∧
          ∀ i : Fin 10, (b.getD i 0).getLsbD j ≤ (a.getD i 0).getLsbD k) :
    have x1 : List (BitVec (58 : ℕ)) := [(95229015649943559 : BitVec (58 : ℕ)), (63038587666488 : BitVec (58 : ℕ)), (256462815680 : BitVec (58 : ℕ)), (4292497062759936 : BitVec (58 : ℕ)), (8521481482240 : BitVec (58 : ℕ)), (14003410187812864 : BitVec (58 : ℕ)), (55389823207997440 : BitVec (58 : ℕ)), (189297016294081033 : BitVec (58 : ℕ)), (155696362464477250 : BitVec (58 : ℕ)), (218994303132270608 : BitVec (58 : ℕ)), (183565875465490436 : BitVec (58 : ℕ)), (229736628138025984 : BitVec (58 : ℕ)), (270286071508633728 : BitVec (58 : ℕ)), (288160007407550752 : BitVec (58 : ℕ))]; ∃ (x2 : List (Bool × ℕ × ℕ)), x2.length = (26 : ℕ) ∧ (∀ (x3 : Fin x2.length), (x2.getD ↑x3 (Bool.false, (0 : ℕ), (0 : ℕ))).2.1 < (x2.getD ↑x3 (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 ∧ (x2.getD ↑x3 (Bool.false, (0 : ℕ), (0 : ℕ))).2.2 < (14 : ℕ) + ↑x3) ∧ (2097151 : BitVec (58 : ℕ)) ∈ List.foldl (fun (x3 : List (BitVec (58 : ℕ))) (x4 : Bool × ℕ × ℕ) => x3 ++ [if x4.1 = Bool.true then x3.getD x4.2.1 (0 : BitVec (58 : ℕ)) &&& x3.getD x4.2.2 (0 : BitVec (58 : ℕ)) else x3.getD x4.2.1 (0 : BitVec (58 : ℕ)) ||| x3.getD x4.2.2 (0 : BitVec (58 : ℕ))]) x1 x2 := by
  let step {w : ℕ} (xs : List (BitVec w)) (g : Bool × ℕ × ℕ) : List (BitVec w) :=
    xs ++ [if g.1 = true then xs.getD g.2.1 0 &&& xs.getD g.2.2 0
      else xs.getD g.2.1 0 ||| xs.getD g.2.2 0]

  have step_length {w : ℕ} (xs : List (BitVec w)) (g : Bool × ℕ × ℕ) :
      (step xs g).length = xs.length + 1 := by simp [step]

  have step_mono {v w : ℕ} (xs : List (BitVec v)) (ys : List (BitVec w))
      (i j : ℕ) (g : Bool × ℕ × ℕ)
      (hlen : xs.length = ys.length)
      (h : ∀ k, (xs.getD k 0).getLsbD i ≤ (ys.getD k 0).getLsbD j) :
      ∀ k, ((step xs g).getD k 0).getLsbD i ≤ ((step ys g).getD k 0).getLsbD j := by
    have hb : ∀ a b c d : Bool, a ≤ b → c ≤ d →
        (a && c) ≤ (b && d) ∧ (a || c) ≤ (b || d) := by decide
    have hv : (if g.1 = true then xs.getD g.2.1 0 &&& xs.getD g.2.2 0
          else xs.getD g.2.1 0 ||| xs.getD g.2.2 0).getLsbD i ≤
        (if g.1 = true then ys.getD g.2.1 0 &&& ys.getD g.2.2 0
          else ys.getD g.2.1 0 ||| ys.getD g.2.2 0).getLsbD j := by
      split <;> simp only [BitVec.getLsbD_and, BitVec.getLsbD_or]
      · exact (hb _ _ _ _ (h g.2.1) (h g.2.2)).1
      · exact (hb _ _ _ _ (h g.2.1) (h g.2.2)).2
    intro k
    by_cases hk : k < xs.length
    · simpa only [step, List.getD_append _ _ _ _ hk,
        List.getD_append _ _ _ _ (by omega : k < ys.length)] using h k
    · simp only [step, List.getD_append_right _ _ _ _ (by omega : xs.length ≤ k),
        List.getD_append_right _ _ _ _ (by omega : ys.length ≤ k), ← hlen]
      by_cases he : k = xs.length
      · simpa only [he, Nat.sub_self, List.getD_cons_zero] using hv
      · have hn : 1 ≤ k - xs.length := by omega
        rw [List.getD_eq_default _ _ hn, List.getD_eq_default _ _ hn]
        simp

  have fold_mono {v w : ℕ} (xs : List (BitVec v)) (ys : List (BitVec w))
      (i j : ℕ) (gs : List (Bool × ℕ × ℕ))
      (hlen : xs.length = ys.length)
      (h : ∀ k, (xs.getD k 0).getLsbD i ≤ (ys.getD k 0).getLsbD j) :
      ∀ k, ((gs.foldl step xs).getD k 0).getLsbD i ≤
        ((gs.foldl step ys).getD k 0).getLsbD j := by
    induction gs generalizing xs ys with
    | nil => exact h
    | cons g gs ih =>
      simp only [List.foldl_cons]
      exact ih (step xs g) (step ys g) (by simp [step_length, hlen])
        (step_mono xs ys i j g hlen h)

  let small : List (BitVec 24) := [4788227,2641932,208944,348352,62208,1588224,9609285,10798098,13043976,16253600]

  let large : List (BitVec 58) := [95229015649943559,63038587666488,256462815680,4292497062759936,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,270286071508633728]

  let cover : Prop := ∀ j : Fin 58, ∃ k : Fin 24,
    if (953051 : BitVec 58).getLsbD j then
      (4095 : BitVec 24).getLsbD k = true ∧
        ∀ i : Fin 10, (small.getD i 0).getLsbD k ≤ (large.getD i 0).getLsbD j
    else
      (4095 : BitVec 24).getLsbD k = false ∧
        ∀ i : Fin 10, (large.getD i 0).getLsbD j ≤ (small.getD i 0).getLsbD k

  have lift_output (hcover : cover) (gs : List (Bool × ℕ × ℕ))
      (hsmall : (gs.foldl step small).getD 23 0 = 4095) :
      (gs.foldl step large).getD 23 0 = 953051 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    obtain ⟨k,hk⟩ := hcover ⟨j,hj⟩
    cases ht : (953051 : BitVec 58).getLsbD j with
    | false =>
      simp only [ht, Bool.false_eq_true, ite_false] at hk
      have hinit : ∀ n, (large.getD n 0).getLsbD j ≤ (small.getD n 0).getLsbD k := by
        intro n
        by_cases hn : n < 10
        · exact hk.2 ⟨n,hn⟩
        · rw [List.getD_eq_default _ _ (by simpa [large] using Nat.le_of_not_gt hn),
            List.getD_eq_default _ _ (by simpa [small] using Nat.le_of_not_gt hn)]
          simp
      have h := fold_mono large small j k gs rfl hinit 23
      rw [hsmall, hk.1] at h
      exact (show ∀ b : Bool, b ≤ false → b = false by decide) _ h
    | true =>
      simp only [ht, ite_true] at hk
      have hinit : ∀ n, (small.getD n 0).getLsbD k ≤ (large.getD n 0).getLsbD j := by
        intro n
        by_cases hn : n < 10
        · exact hk.2 ⟨n,hn⟩
        · rw [List.getD_eq_default _ _ (by simpa [small] using Nat.le_of_not_gt hn),
            List.getD_eq_default _ _ (by simpa [large] using Nat.le_of_not_gt hn)]
          simp
      have h := fold_mono small large k j gs rfl hinit 23
      rw [hsmall, hk.1] at h
      exact (show ∀ b : Bool, true ≤ b → b = true by decide) _ h

  let gateMap (f : Nat → Nat) (g : Bool × Nat × Nat) := (g.1, f g.2.1, f g.2.2)

  have fold_length {w : Nat} (gs : List (Bool × Nat × Nat)) (xs : List (BitVec w)) :
      (gs.foldl step xs).length = xs.length + gs.length := by
    induction gs generalizing xs with
    | nil => simp
    | cons g gs ih => simp [ih, step_length, Nat.add_comm, Nat.add_left_comm]

  have step_map {w : Nat} (A B : List (BitVec w)) (f : Nat → Nat)
      (g : Bool × Nat × Nat)
      (hleft : g.2.1 < A.length) (hright : g.2.2 < A.length)
      (hbound : ∀ i < A.length, f i < B.length)
      (hlen : f A.length = B.length)
      (hmap : ∀ i < A.length, A.getD i 0 = B.getD (f i) 0) :
      ∀ i < (step A g).length,
        (step A g).getD i 0 = (step B (gateMap f g)).getD (f i) 0 := by
    intro i hi
    have hv : (if g.1 = true then A.getD g.2.1 0 &&& A.getD g.2.2 0
      else A.getD g.2.1 0 ||| A.getD g.2.2 0) =
      (if g.1 = true then B.getD (f g.2.1) 0 &&& B.getD (f g.2.2) 0
      else B.getD (f g.2.1) 0 ||| B.getD (f g.2.2) 0) := by
        rw [hmap _ hleft, hmap _ hright]
    by_cases hiA : i < A.length
    · unfold step gateMap
      rw [List.getD_append _ _ _ _ hiA, List.getD_append _ _ _ _ (hbound _ hiA)]
      exact hmap _ hiA
    · have heq : i = A.length := by rw [step_length] at hi; omega
      subst i
      unfold step gateMap
      rw [hlen, List.getD_append_right _ _ _ _ (by omega),
        List.getD_append_right _ _ _ _ (by omega)]
      simpa using hv

  have fold_map {w : Nat} (gs : List (Bool × Nat × Nat))
      (A B : List (BitVec w)) (f : Nat → Nat)
      (hwf : ∀ i, i < gs.length →
        (gs.getD i (false, 0, 0)).2.1 < A.length + i ∧
        (gs.getD i (false, 0, 0)).2.2 < A.length + i)
      (hbound : ∀ i < A.length, f i < B.length)
      (hfuture : ∀ k, f (A.length + k) = B.length + k)
      (hmap : ∀ i < A.length, A.getD i 0 = B.getD (f i) 0) :
      ∀ i < (gs.foldl step A).length,
        (gs.foldl step A).getD i 0 =
          ((gs.map (gateMap f)).foldl step B).getD (f i) 0 := by
    induction gs generalizing A B with
    | nil => simpa using hmap
    | cons g gs ih =>
      simp only [List.foldl_cons, List.map_cons]
      apply ih (step A g) (step B (gateMap f g))
      · intro i hi
        have h := hwf (i + 1) (by simp only [List.length_cons]; omega)
        simp only [List.getD_cons_succ] at h
        simpa only [step_length, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using h
      · intro i hi
        rw [step_length] at hi ⊢
        by_cases hiA : i < A.length
        · exact Nat.lt_trans (hbound _ hiA) (Nat.lt_succ_self _)
        · have heq : i = A.length := by omega
          subst i
          have hh := hfuture 0
          simp only [Nat.add_zero] at hh
          omega
      · intro k
        rw [step_length, step_length]
        simpa only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hfuture (k + 1)
      · apply step_map A B f g
        · simpa using (hwf 0 (by simp)).1
        · simpa using (hwf 0 (by simp)).2
        · exact hbound
        · simpa using hfuture 0
        · exact hmap

  have map_wf (gs : List (Bool × Nat × Nat)) (n m : Nat) (f : Nat → Nat)
      (hf0 : f 0 = 0) (hf : StrictMono f)
      (hfuture : ∀ k, f (n + k) = m + k)
      (hwf : ∀ i, i < gs.length →
        (gs.getD i (false, 0, 0)).2.1 < (gs.getD i (false, 0, 0)).2.2 ∧
        (gs.getD i (false, 0, 0)).2.2 < n + i) :
      ∀ i, i < (gs.map (gateMap f)).length →
        ((gs.map (gateMap f)).getD i (false, 0, 0)).2.1 <
          ((gs.map (gateMap f)).getD i (false, 0, 0)).2.2 ∧
        ((gs.map (gateMap f)).getD i (false, 0, 0)).2.2 < m + i := by
    intro i hi
    have hm : (gs.map (gateMap f)).getD i (false, 0, 0) =
        gateMap f (gs.getD i (false, 0, 0)) := by
      simpa only [gateMap, hf0] using
        (List.getD_map gs (false, 0, 0) (gateMap f) (n := i))
    rw [hm]
    obtain ⟨h1, h2⟩ := hwf i (by simpa using hi)
    constructor
    · exact hf h1
    · simpa only [gateMap, hfuture] using hf h2

  let embed (i : Nat) : Nat :=
    if i < 10 then ([0,1,2,3,5,6,7,8,9,12] : List Nat).getD i 0 else i + 4

  have embed_bound : ∀ i < 10, embed i < 14 := by
    have hh : ∀ i : Fin 10, embed i.val < 14 := by decide
    intro i hi
    exact hh ⟨i, hi⟩

  have embed_future (k : Nat) : embed (10 + k) = 14 + k := by
    simp only [embed]
    split <;> omega

  have embed_strict : StrictMono embed := by
    have hh : ∀ i j : Fin 10, i.val < j.val → embed i.val < embed j.val := by decide
    intro i j hij
    by_cases hj : j < 10
    · exact hh ⟨i, by omega⟩ ⟨j, hj⟩ hij
    · by_cases hi : i < 10
      · have hb := embed_bound i hi
        simpa only [embed, ite_eq_right hj] using (show embed i < j + 4 by omega)
      · simp only [embed, ite_eq_right hj, ite_eq_right hi]
        omega

  have output_23 (gs : List (Bool × Nat × Nat))
      (A B : List (BitVec 58))
      (hAlen : A.length = 10) (hBlen : B.length = 14) (hgs : gs.length = 14)
      (hwf : ∀ i, i < gs.length →
        (gs.getD i (false, 0, 0)).2.1 < (gs.getD i (false, 0, 0)).2.2 ∧
        (gs.getD i (false, 0, 0)).2.2 < 10 + i)
      (hmap : ∀ i < 10, A.getD i 0 = B.getD (embed i) 0) :
      (gs.foldl step A).getD 23 0 =
        ((gs.map (gateMap embed)).foldl step B).getD 27 0 := by
    have h := fold_map gs A B embed
      (by
        intro i hi
        obtain ⟨ha, hb⟩ := hwf i hi
        rw [hAlen]
        exact ⟨Nat.lt_trans ha hb, hb⟩)
      (by simpa only [hAlen, hBlen] using embed_bound)
      (by simpa only [hAlen, hBlen] using embed_future)
      (by simpa only [hAlen] using hmap)
    exact h 23 (by rw [fold_length, hAlen, hgs]; decide)

  let tailOps : List (Bool × ℕ × ℕ) :=
    [(false,0,4),(false,5,28),(true,10,29),(false,3,4),(false,6,31),(true,11,32),
     (false,1,2),(false,4,34),(true,13,35),(false,27,30),(false,33,37),(false,36,38)]

  have suffix_wf : tailOps.length = 12 ∧ ∀ j : Fin tailOps.length,
      (tailOps.getD j.val (false,0,0)).2.1 < (tailOps.getD j.val (false,0,0)).2.2 ∧
      (tailOps.getD j.val (false,0,0)).2.2 < 28 + j.val := by
    decide +kernel

  have suffix_run (xs : List (BitVec 58)) (hlen : xs.length = 28)
      (h0 : xs.getD 0 0 = 95229015649943559)
      (h1 : xs.getD 1 0 = 63038587666488)
      (h2 : xs.getD 2 0 = 256462815680)
      (h3 : xs.getD 3 0 = 4292497062759936)
      (h4 : xs.getD 4 0 = 8521481482240)
      (h5 : xs.getD 5 0 = 14003410187812864)
      (h6 : xs.getD 6 0 = 55389823207997440)
      (h10 : xs.getD 10 0 = 183565875465490436)
      (h11 : xs.getD 11 0 = 229736628138025984)
      (h13 : xs.getD 13 0 = 288160007407550752)
      (h27 : xs.getD 27 0 = 953051)
      : tailOps.foldl step xs = xs ++ [95235063194611719,104664500684451847,69636,4301018365984256,58493748014513664,1057792,63221765505528,70368742109688,16672,1022687,2080479,2097151] := by
    simp only [List.getD_eq_getElem _ _ (show 0 < xs.length by omega)] at h0
    simp only [List.getD_eq_getElem _ _ (show 1 < xs.length by omega)] at h1
    simp only [List.getD_eq_getElem _ _ (show 2 < xs.length by omega)] at h2
    simp only [List.getD_eq_getElem _ _ (show 3 < xs.length by omega)] at h3
    simp only [List.getD_eq_getElem _ _ (show 4 < xs.length by omega)] at h4
    simp only [List.getD_eq_getElem _ _ (show 5 < xs.length by omega)] at h5
    simp only [List.getD_eq_getElem _ _ (show 6 < xs.length by omega)] at h6
    simp only [List.getD_eq_getElem _ _ (show 10 < xs.length by omega)] at h10
    simp only [List.getD_eq_getElem _ _ (show 11 < xs.length by omega)] at h11
    simp only [List.getD_eq_getElem _ _ (show 13 < xs.length by omega)] at h13
    simp only [List.getD_eq_getElem _ _ (show 27 < xs.length by omega)] at h27
    simp [tailOps, step, List.append_assoc, hlen, h0,h1,h2,h3,h4,h5,h6,h10,h11,h13,h27]

  have fold_preserve {w : ℕ} (gs : List (Bool × ℕ × ℕ)) (xs : List (BitVec w)) :
      ∀ i < xs.length, (gs.foldl step xs).getD i 0 = xs.getD i 0 := by
    induction gs generalizing xs with
    | nil => simp
    | cons g gs ih =>
      intro i hi
      simp only [List.foldl_cons]
      rw [ih _ i (by rw [step_length]; omega)]
      exact List.getD_append _ _ _ _ hi
  let inputs : List (BitVec 58) := [95229015649943559,63038587666488,256462815680,4292497062759936,8521481482240,14003410187812864,55389823207997440,189297016294081033,155696362464477250,218994303132270608,183565875465490436,229736628138025984,270286071508633728,288160007407550752]
  have inputmap : ∀ i < 10, large.getD i 0 = inputs.getD (embed i) 0 := by
    have hh : ∀ i : Fin 10, large.getD i.val 0 = inputs.getD (embed i.val) 0 := by decide
    intro i hi
    exact hh ⟨i,hi⟩
  obtain ⟨gs,hgs,hwf,hsmall⟩ := search
  have hwide := lift_output rows gs hsmall
  have hwfNat : ∀ i, i < gs.length →
      (gs.getD i (false,0,0)).2.1 < (gs.getD i (false,0,0)).2.2 ∧
      (gs.getD i (false,0,0)).2.2 < 10 + i := by
    intro i hi
    exact hwf ⟨i,hi⟩
  let initialOps := gs.map (gateMap embed)
  have hp_len : initialOps.length = 14 := by simp [initialOps,hgs]
  have hp_wf := map_wf gs 10 14 embed rfl embed_strict embed_future hwfNat
  have hout27 : (initialOps.foldl step inputs).getD 27 0 = 953051 := by
    rw [← output_23 gs large inputs rfl rfl hgs hwfNat inputmap]
    exact hwide
  have pre_facts : ∀ i < 14, (initialOps.foldl step inputs).getD i 0 = inputs.getD i 0 :=
    fold_preserve initialOps inputs
  have hrun := suffix_run (initialOps.foldl step inputs)
    (by simp only [fold_length,hp_len]; rfl)
    (pre_facts 0 (by decide))
    (pre_facts 1 (by decide))
    (pre_facts 2 (by decide))
    (pre_facts 3 (by decide))
    (pre_facts 4 (by decide))
    (pre_facts 5 (by decide))
    (pre_facts 6 (by decide))
    (pre_facts 10 (by decide))
    (pre_facts 11 (by decide))
    (pre_facts 13 (by decide))
    hout27
  refine ⟨initialOps ++ tailOps, ?_, ?_, ?_⟩
  · simp only [List.length_append,hp_len,suffix_wf.1]
  · intro i
    by_cases hi : i.val < initialOps.length
    · rw [List.getD_append _ _ _ _ hi]
      exact hp_wf i.val hi
    · have hi' : i.val - initialOps.length < tailOps.length := by
        have hh := i.isLt
        simp only [List.length_append] at hh
        omega
      rw [List.getD_append_right _ _ _ _ (Nat.le_of_not_gt hi)]
      obtain ⟨ha,hb⟩ := suffix_wf.2 ⟨i.val - initialOps.length,hi'⟩
      exact ⟨ha, by simp only at hb; omega⟩
  · change (2097151 : BitVec 58) ∈ (initialOps ++ tailOps).foldl step inputs
    rw [List.foldl_append,hrun]
    simp
