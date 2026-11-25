import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_5471_aux
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stepC (pool : List ℕ) : List ℕ :=
  65535 :: 0 :: (pool ++ pool.flatMap (fun a => pool.flatMap (fun b => [a &&& b, a ||| b])))

def myDedup : List ℕ → List ℕ
  | [] => []
  | a :: l => if l.contains a then myDedup l else a :: myDedup l

theorem mem_myDedup : ∀ (l : List ℕ) (c : ℕ), c ∈ l → c ∈ myDedup l
  | [], c, h => by simp at h
  | a :: l, c, h => by
    unfold myDedup
    rcases List.mem_cons.mp h with rfl | h
    · split
      · rename_i hc; exact mem_myDedup l _ (by simpa using hc)
      · simp
    · split
      · exact mem_myDedup l c h
      · exact List.mem_cons_of_mem _ (mem_myDedup l c h)

def hitP (T : ℕ) (pool : List ℕ) : Bool := pool.any (fun m => m % 65536 == T)

def hit2 (T : ℕ) (pool : List ℕ) : Bool :=
  T == 65535 || T == 0 || hitP T pool ||
    pool.any (fun a => pool.any (fun b => (a &&& b) % 65536 == T || (a ||| b) % 65536 == T))

theorem hit2_of (T : ℕ) (pool : List ℕ) (c : ℕ) (hc : c ∈ stepC pool) (h : c % 65536 = T) :
    hit2 T pool = true := by
  simp only [stepC, List.mem_cons, List.mem_append, List.mem_flatMap] at hc
  simp only [hit2, hitP, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
  rcases hc with rfl | rfl | hc | ⟨a, ha, b, hb, hc⟩
  · left; left; left; omega
  · left; left; right; omega
  · left; right; exact ⟨c, hc, h⟩
  · right; refine ⟨a, ha, b, hb, ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · left; exact h
    · right; exact h

def reach (T : ℕ) : List ℕ → ℕ → Bool
  | pool, 0 => hitP T pool
  | pool, 1 => hitP T pool || hit2 T pool
  | pool, k + 2 => hitP T pool || reach T pool (k + 1) ||
      (myDedup (stepC pool)).any (fun c => !pool.contains c && reach T (pool ++ [c]) (k + 1))

theorem reach_split (T : ℕ) (pool : List ℕ) (k : ℕ) (h1 : hitP T pool = false)
    (h2 : reach T pool (k + 1) = false)
    (h3 : ∀ c ∈ myDedup (stepC pool), pool.contains c = false →
      reach T (pool ++ [c]) (k + 1) = false) :
    reach T pool (k + 2) = false := by
  simp only [reach, h1, h2, Bool.false_or]
  apply List.any_eq_false.mpr
  intro c hc
  cases hcc : pool.contains c
  · simp [h3 c hc hcc]
  · simp

theorem reach_of_hit (T : ℕ) (pool : List ℕ) (h : hitP T pool = true) :
    ∀ k, reach T pool k = true
  | 0 => by simp only [reach]; exact h
  | 1 => by simp only [reach, Bool.or_eq_true]; exact Or.inl h
  | k + 2 => by simp only [reach, Bool.or_eq_true]; exact Or.inl (Or.inl h)

def Inv (pool : List ℕ) (ws : Fin 16 → List Bool) : Prop :=
  ∀ i : ℕ, ∃ m ∈ pool, ∀ p : Fin 16, m.testBit p = (ws p).getD i false

theorem getD_snoc (l : List Bool) (x : Bool) (i : ℕ) :
    (l ++ [x]).getD i false = if i = l.length then x else l.getD i false := by
  rcases lt_trichotomy i l.length with h | h | h
  · rw [if_neg (by omega)]
    simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]
  · subst h; simp [List.getD_eq_getElem?_getD]
  · rw [if_neg (by omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by omega)]

theorem testBit_65535 : ∀ p : Fin 16, (65535 : ℕ).testBit p = true := by decide

theorem gate_vec (pool : List ℕ) (ws : Fin 16 → List Bool) (h : Inv pool ws) (g : Gate)
    (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp)) (hlen : g.inputs.length ≤ 2) :
    ∃ c ∈ stepC pool, ∀ p : Fin 16,
      c.testBit p = g.op.eval (g.inputs.map fun i => (ws p).getD i false) := by
  obtain ⟨op, ins⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  simp only at hlen ⊢
  match ins, hlen with
  | [], _ =>
    rcases hop with rfl | rfl
    · exact ⟨65535, by simp [stepC], fun p => by simp [GateOp.eval, testBit_65535 p]⟩
    · exact ⟨0, by simp [stepC], fun p => by simp [GateOp.eval]⟩
  | [a], _ =>
    obtain ⟨ma, hma, ha⟩ := h a
    refine ⟨ma, by simp [stepC, hma], fun p => ?_⟩
    rcases hop with rfl | rfl <;> simp [GateOp.eval, ha p]
  | [a, b], _ =>
    obtain ⟨ma, hma, ha⟩ := h a
    obtain ⟨mb, hmb, hb⟩ := h b
    rcases hop with rfl | rfl
    · refine ⟨ma &&& mb, ?_, fun p => ?_⟩
      · simp only [stepC, List.mem_cons, List.mem_append, List.mem_flatMap]
        exact Or.inr (Or.inr (Or.inr ⟨ma, hma, mb, hmb, by simp⟩))
      · simp [GateOp.eval, ha p, hb p]
    · refine ⟨ma ||| mb, ?_, fun p => ?_⟩
      · simp only [stepC, List.mem_cons, List.mem_append, List.mem_flatMap]
        exact Or.inr (Or.inr (Or.inr ⟨ma, hma, mb, hmb, by simp⟩))
      · simp [GateOp.eval, ha p, hb p]
  | _ :: _ :: _ :: _, hl => simp at hl

theorem out_hit (T : ℕ) (hT : T < 65536) (pool : List ℕ) (ws : Fin 16 → List Bool) (o : ℕ)
    (hI : Inv pool ws) (hout : ∀ p : Fin 16, (ws p).getD o false = T.testBit p) :
    hitP T pool = true := by
  obtain ⟨m, hm, hmb⟩ := hI o
  have hmT : m % 65536 = T := by
    apply Nat.eq_of_testBit_eq; intro i
    rw [show (65536 : ℕ) = 2 ^ 16 from rfl, Nat.testBit_mod_two_pow]
    by_cases hi : i < 16
    · simp only [hi, decide_true, Bool.true_and]
      exact (hmb ⟨i, hi⟩).trans (hout ⟨i, hi⟩)
    · simp only [hi, decide_false, Bool.false_and]
      symm; apply Nat.testBit_eq_false_of_lt
      calc T < 2 ^ 16 := hT
        _ ≤ 2 ^ i := Nat.pow_le_pow_right (by norm_num) (by omega)
  exact List.any_eq_true.mpr ⟨m, hm, by simp [hmT]⟩

theorem inv_step (pool pool' : List ℕ) (ws : Fin 16 → List Bool) (L : ℕ)
    (hL : ∀ p, (ws p).length = L) (hI : Inv pool ws) (b : Fin 16 → Bool) (c : ℕ)
    (hcv : ∀ p : Fin 16, c.testBit p = b p) (hsub : ∀ m ∈ pool, m ∈ pool') (hcp : c ∈ pool') :
    Inv pool' (fun p => ws p ++ [b p]) := by
  intro i
  obtain ⟨m, hm, hmb⟩ := hI i
  by_cases hi : i = L
  · subst hi
    exact ⟨c, hcp, fun p => by rw [getD_snoc, if_pos (hL p).symm, hcv p]⟩
  · exact ⟨m, hsub m hm, fun p => by rw [getD_snoc, if_neg (by rw [hL p]; exact hi), hmb p]⟩

theorem main (T : ℕ) (hT : T < 65536) : ∀ (gs : List Gate) (pool : List ℕ)
    (ws : Fin 16 → List Bool) (L k o : ℕ),
    (∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) →
    gs.length ≤ k → (∀ p, (ws p).length = L) → Inv pool ws →
    (∀ p : Fin 16, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (ws p)).getD o false = T.testBit p) →
    reach T pool k = true
  | [], pool, ws, L, k, o, _, _, _, hI, hout =>
    reach_of_hit T pool (out_hit T hT pool ws o hI (fun p => hout p)) k
  | g :: gs, pool, ws, L, k, o, hg, hk, hL, hI, hout => by
    obtain ⟨hop, hlen⟩ := hg g (by simp)
    obtain ⟨c, hc, hcv⟩ := gate_vec pool ws hI g hop hlen
    have hout' : ∀ p : Fin 16, (gs.foldl
        (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        (ws p ++ [g.op.eval (g.inputs.map fun i => (ws p).getD i false)])).getD o false =
          T.testBit p :=
      fun p => by have h3 := hout p; rw [List.foldl_cons] at h3; exact h3
    have hg' : ∀ g' ∈ gs, g'.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧
        g'.inputs.length ≤ 2 :=
      fun g' hg' => hg g' (by simp [hg'])
    have hL' : ∀ p, (ws p ++ [g.op.eval (g.inputs.map fun i => (ws p).getD i false)]).length =
        L + 1 :=
      fun p => by simp [hL p]
    have hkl : gs.length + 1 ≤ k := by simp only [List.length_cons] at hk; omega
    match k, hkl with
    | 0, hkl => omega
    | 1, hkl =>
      have hgs : gs = [] := List.eq_nil_of_length_eq_zero (by omega)
      subst hgs
      have hh := out_hit T hT (pool ++ [c]) _ o
        (inv_step pool (pool ++ [c]) ws L hL hI _ c hcv (fun m hm => by simp [hm]) (by simp))
        (fun p => hout' p)
      rw [hitP, List.any_append, Bool.or_eq_true] at hh
      simp only [reach, Bool.or_eq_true]
      rcases hh with hh | hh
      · exact Or.inl hh
      · simp at hh
        exact Or.inr (hit2_of T pool c hc hh)
    | k + 2, hkl =>
      by_cases hcin : c ∈ pool
      · have IH := main T hT gs pool _ (L + 1) (k + 1) o hg' (by omega) hL'
          (inv_step pool pool ws L hL hI _ c hcv (fun m hm => hm) hcin) hout'
        simp only [reach, Bool.or_eq_true]
        exact Or.inl (Or.inr IH)
      · have IH := main T hT gs (pool ++ [c]) _ (L + 1) (k + 1) o hg' (by omega) hL'
          (inv_step pool (pool ++ [c]) ws L hL hI _ c hcv (fun m hm => by simp [hm]) (by simp))
          hout'
        simp only [reach, Bool.or_eq_true, List.any_eq_true]
        refine Or.inr ⟨c, mem_myDedup _ c hc, ?_⟩
        simp [hcin, IH]

def pool0 : List ℕ := [15, 240, 3840, 61440, 4369, 8738, 17476, 34952, 0]

def X (p : Fin 16) : List Bool :=
  oneEach (⟨p.val / 4, by omega⟩ : Fin 4) (⟨p.val % 4, by omega⟩ : Fin 4)

theorem X_len (p : Fin 16) : (X p).length = 8 := by simp [X, oneEach]

theorem inv0 : Inv pool0 X := by
  intro i
  by_cases hi : i < 8
  · have key : ∀ j : Fin 8, ∀ p : Fin 16, (pool0.getD j 0).testBit p = (X p).getD j false := by
      decide
    exact ⟨pool0.getD i 0, by interval_cases i <;> simp [pool0], fun p => key ⟨i, hi⟩ p⟩
  · refine ⟨0, by simp [pool0], fun p => ?_⟩
    rw [Nat.zero_testBit, List.getD_eq_default _ _ (by rw [X_len]; omega)]

theorem lower (T : ℕ) (hT : T < 65536) (k : ℕ) (hr : reach T pool0 k = false) :
    ¬ RepSizeAtMost (fun u v : Fin 4 => T.testBit (4 * u.val + v.val)) k := by
  rintro ⟨C, hC, hs, hrep⟩
  have := main T hT C.gates pool0 X 8 k C.output hC hs X_len inv0 (fun p => by
    have h := hrep ⟨p.val / 4, by omega⟩ ⟨p.val % 4, by omega⟩
    have he : T.testBit (4 * (p.val / 4) + p.val % 4) = T.testBit p := by
      rw [Nat.div_add_mod p.val 4]
    exact h.trans he)
  rw [hr] at this; exact absurd this (by simp)

theorem upper : RepSizeAtMost (fun u v : Fin 4 => (22 : ℕ).testBit (4 * u.val + v.val)) 4 := by
  refine ⟨⟨[⟨GateOp.or, [0, 4]⟩, ⟨GateOp.or, [1, 5]⟩, ⟨GateOp.or, [6, 9]⟩, ⟨GateOp.and, [8, 10]⟩], 11⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl <;> simp

def LIT : List ℕ := [1, 2, 4, 8, 16, 32, 64, 128, 255, 256, 512, 1024, 2048, 3855, 4080, 4096, 4383, 4593, 7953, 8192, 8751, 8946, 12066, 13107, 16384, 17487, 17652, 20292, 21845, 26214, 32768, 34959, 35064, 36744, 39321, 43690, 52428, 61455, 61680, 61713, 61986, 62532, 63624, 65280, 65535]

theorem lit_mem : ∀ c ∈ myDedup (stepC pool0), pool0.contains c = false → c ∈ LIT := by decide +kernel

theorem top_hit : hitP 22 pool0 = false := by decide +kernel

theorem top_prev : reach 22 pool0 2 = false := by decide +kernel

theorem r_0 : reach 22 (pool0 ++ [1]) 2 = false := by decide +kernel

theorem r_1 : reach 22 (pool0 ++ [2]) 2 = false := by decide +kernel

theorem r_2 : reach 22 (pool0 ++ [4]) 2 = false := by decide +kernel

theorem r_3 : reach 22 (pool0 ++ [8]) 2 = false := by decide +kernel

theorem r_4 : reach 22 (pool0 ++ [16]) 2 = false := by decide +kernel

theorem r_5 : reach 22 (pool0 ++ [32]) 2 = false := by decide +kernel

theorem r_6 : reach 22 (pool0 ++ [64]) 2 = false := by decide +kernel

theorem r_7 : reach 22 (pool0 ++ [128]) 2 = false := by decide +kernel

theorem r_8 : reach 22 (pool0 ++ [255]) 2 = false := by decide +kernel

theorem r_9 : reach 22 (pool0 ++ [256]) 2 = false := by decide +kernel

theorem r_10 : reach 22 (pool0 ++ [512]) 2 = false := by decide +kernel

theorem r_11 : reach 22 (pool0 ++ [1024]) 2 = false := by decide +kernel

theorem r_12 : reach 22 (pool0 ++ [2048]) 2 = false := by decide +kernel

theorem r_13 : reach 22 (pool0 ++ [3855]) 2 = false := by decide +kernel

theorem r_14 : reach 22 (pool0 ++ [4080]) 2 = false := by decide +kernel

theorem r_15 : reach 22 (pool0 ++ [4096]) 2 = false := by decide +kernel

theorem r_16 : reach 22 (pool0 ++ [4383]) 2 = false := by decide +kernel

theorem r_17 : reach 22 (pool0 ++ [4593]) 2 = false := by decide +kernel

theorem r_18 : reach 22 (pool0 ++ [7953]) 2 = false := by decide +kernel

theorem r_19 : reach 22 (pool0 ++ [8192]) 2 = false := by decide +kernel

theorem r_20 : reach 22 (pool0 ++ [8751]) 2 = false := by decide +kernel

theorem r_21 : reach 22 (pool0 ++ [8946]) 2 = false := by decide +kernel

theorem r_22 : reach 22 (pool0 ++ [12066]) 2 = false := by decide +kernel

theorem r_23 : reach 22 (pool0 ++ [13107]) 2 = false := by decide +kernel

theorem r_24 : reach 22 (pool0 ++ [16384]) 2 = false := by decide +kernel

theorem r_25 : reach 22 (pool0 ++ [17487]) 2 = false := by decide +kernel

theorem r_26 : reach 22 (pool0 ++ [17652]) 2 = false := by decide +kernel

theorem r_27 : reach 22 (pool0 ++ [20292]) 2 = false := by decide +kernel

theorem r_28 : reach 22 (pool0 ++ [21845]) 2 = false := by decide +kernel

theorem r_29 : reach 22 (pool0 ++ [26214]) 2 = false := by decide +kernel

theorem r_30 : reach 22 (pool0 ++ [32768]) 2 = false := by decide +kernel

theorem r_31 : reach 22 (pool0 ++ [34959]) 2 = false := by decide +kernel

theorem r_32 : reach 22 (pool0 ++ [35064]) 2 = false := by decide +kernel

theorem r_33 : reach 22 (pool0 ++ [36744]) 2 = false := by decide +kernel

theorem r_34 : reach 22 (pool0 ++ [39321]) 2 = false := by decide +kernel

theorem r_35 : reach 22 (pool0 ++ [43690]) 2 = false := by decide +kernel

theorem r_36 : reach 22 (pool0 ++ [52428]) 2 = false := by decide +kernel

theorem r_37 : reach 22 (pool0 ++ [61455]) 2 = false := by decide +kernel

theorem r_38 : reach 22 (pool0 ++ [61680]) 2 = false := by decide +kernel

theorem r_39 : reach 22 (pool0 ++ [61713]) 2 = false := by decide +kernel

theorem r_40 : reach 22 (pool0 ++ [61986]) 2 = false := by decide +kernel

theorem r_41 : reach 22 (pool0 ++ [62532]) 2 = false := by decide +kernel

theorem r_42 : reach 22 (pool0 ++ [63624]) 2 = false := by decide +kernel

theorem r_43 : reach 22 (pool0 ++ [65280]) 2 = false := by decide +kernel

theorem r_44 : reach 22 (pool0 ++ [65535]) 2 = false := by decide +kernel

theorem all_c : ∀ c ∈ LIT, reach 22 (pool0 ++ [c]) 2 = false := by
  simp only [LIT, List.forall_mem_cons, List.not_mem_nil, false_imp_iff, implies_true, and_true]
  exact ⟨r_0, r_1, r_2, r_3, r_4, r_5, r_6, r_7, r_8, r_9, r_10, r_11, r_12, r_13, r_14, r_15, r_16, r_17, r_18, r_19, r_20, r_21, r_22, r_23, r_24, r_25, r_26, r_27, r_28, r_29, r_30, r_31, r_32, r_33, r_34, r_35, r_36, r_37, r_38, r_39, r_40, r_41, r_42, r_43, r_44⟩

theorem low_reach : reach 22 pool0 3 = false :=
  reach_split _ _ _ top_hit top_prev (fun c hc hn => all_c c (lit_mem c hc hn))

end PEqualNP.Outside.L_meta_5471_aux

set_option maxHeartbeats 8000000 in
theorem PEqualNP.Outside.L_meta_5471 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (22 : ℕ).testBit (4 * u.val + v.val)) 4 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (22 : ℕ).testBit (4 * u.val + v.val)) 3 := by
  exact ⟨PEqualNP.Outside.L_meta_5471_aux.upper, PEqualNP.Outside.L_meta_5471_aux.lower 22 (by norm_num) 3 PEqualNP.Outside.L_meta_5471_aux.low_reach⟩
