import Fast982

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Reduced
open PEqualNP.Outside.L_meta_982_aux.Finite.Live

theorem next_monoSlack {forbidden m a b ws f} (hab : a ≤ b)
    (h : next forbidden m a ws f = true) : next forbidden m b ws f = true := by
  have h1 : 1 ≤ a → 1 ≤ b := by omega
  have h2 : 2 ≤ a → 2 ≤ b := by omega
  simp only [next,Live.next,List.any_eq_true,Bool.or_eq_true,Bool.and_eq_true,
    decide_eq_true_eq] at h ⊢
  obtain ⟨x,hx,hu | hb⟩ := h
  · refine ⟨x,hx,Or.inl ?_⟩
    obtain ⟨ha,neg,hn,hu⟩ := hu
    refine ⟨h1 ha,neg,hn,?_⟩
    tauto
  · refine ⟨x,hx,Or.inr ?_⟩
    obtain ⟨y,hy,hxy,conj,hc,hb⟩ := hb
    refine ⟨y,hy,hxy,conj,hc,?_⟩
    tauto

theorem covers_ok_le {k t s ws} (h : NatRun (mask k) (goal k) t ws) (ht : t ≤ s) :
    covers k s ws = true := by
  by_cases hl : ws.length = s+1
  · have hh := run_len h
    have he : t = s := by omega
    subst t
    exact covers_ok h
  · simp [covers,hl,required h]

theorem scrW_no_le {k t s ws} (width : Nat) (pool : List Nat)
    (h : NatRun (mask k) (goal k) t ws) (ht : t ≤ s) : scrW k width s pool ws = false := by
  by_cases hl : ws.length = s+1
  · have hh := run_len h
    have he : t = s := by omega
    subst t
    exact scrW_no width pool h
  · simp [scrW,hl]

def rejectLeDepth (forbidden : List Nat) (k width : Nat) (pool : List Nat) :
    Nat → Nat → List Nat → Bool
  | 0,s,ws => if ws == [goal k] then false else !(covers k s ws) || scrW k width s pool ws
  | d+1,s,ws => if ws == [goal k] then false else
      !(covers k s ws) || scrW k width s pool ws ||
        match s with
        | 0 => true
        | s+1 => !(next forbidden (mask k) (s+2-ws.length) ws fun _ zs =>
            !(rejectLeDepth forbidden k width pool d s zs))

theorem rejectLeDepth_no {forbidden k width pool} (d : Nat) {t s ws}
    (h : RNatRun forbidden (mask k) (goal k) t ws) (ht : t ≤ s) :
    rejectLeDepth forbidden k width pool d s ws = false := by
  induction d generalizing t s ws with
  | zero =>
    by_cases hw : ws = [goal k]
    · simp [rejectLeDepth,hw]
    · simp [rejectLeDepth,hw,covers_ok_le h.toRun ht,scrW_no_le width pool h.toRun ht]
  | succ d ih =>
    by_cases hw : ws = [goal k]
    · simp [rejectLeDepth,hw]
    · cases t with
      | zero => exact False.elim (hw (zero_done h.toRun rfl))
      | succ t =>
        cases s with
        | zero => omega
        | succ s =>
          let F (_ : Nat) (zs : List Nat) : Bool := !(rejectLeDepth forbidden k width pool d s zs)
          have hF (tag : Nat) (zs : List Nat) (hz : RNatRun forbidden (mask k) (goal k) t zs) :
              F tag zs = true := by simp [F,ih hz (show t ≤ s by omega)]
          have hN := next_complete h t rfl _ (List.Perm.refl _) F hF
          have hN' := next_monoSlack (show t+2-ws.length ≤ s+2-ws.length by omega) hN
          simpa [rejectLeDepth,hw,covers_ok_le h.toRun ht,scrW_no_le width pool h.toRun ht,F] using hN'

theorem pairedBar_all_le {forbidden k width S N idx ori pool} {cap : Nat}
    (hr : ∀ p i tag {u ys}, RNatRun forbidden (mask k) (goal k) u ys →
      RNatRun forbidden (mask k) (goal k) u (ori p i tag ys))
    (hc : ∀ s ≤ cap, ∀ i < N s, pairedBar forbidden k width S N idx ori pool s i = true)
    (hng : ∀ s ≤ cap, ∀ i < N s, S s i ≠ [goal k]) :
    ∀ s ≤ cap, ∀ i < N s, ∀ t ≤ s,
      ¬ RNatRun forbidden (mask k) (goal k) t (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi t ht h
    cases t with
    | zero => exact hng s hs i hi (zero_done h.toRun rfl)
    | succ t =>
      cases s with
      | zero => omega
      | succ s =>
        let F (tag : Nat) (zs : List Nat) :=
          covers k s zs && !(scrW k width s pool zs) &&
            !(decide (idx (s+1) i tag < N s) &&
              (ori (s+1) i tag zs).isPerm (S s (idx (s+1) i tag)))
        have hF (tag : Nat) (zs) (hz : RNatRun forbidden (mask k) (goal k) t zs) :
            F tag zs = true := by
          simp only [F,covers_ok_le hz.toRun (show t ≤ s by omega),
            scrW_no_le width pool hz.toRun (show t ≤ s by omega),
            Bool.not_false,Bool.true_and]
          simp only [Bool.not_eq_true',Bool.and_eq_false_imp,decide_eq_true_eq]
          intro hj
          by_contra! hp
          have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
          exact ih s (by omega) (by omega) _ hj t (by omega)
            (RRun.perm p (hr (s+1) i tag hz))
        have hN := next_complete h t rfl _ (List.Perm.refl _) F hF
        have hN' := next_monoSlack (show t+2-(S (s+1) i).length ≤
            s+2-(S (s+1) i).length by omega) hN
        have hb := hc (s+1) hs i hi
        change !(next _ _ _ _ F) = true at hb
        rw [hN'] at hb
        contradiction

end PEqualNP.Outside.L_meta_982_aux.Finite.Reduced

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
namespace PEqualNP.Outside.L_meta_982_aux.Finite.Early
open PEqualNP.Outside.L_meta_982_aux.Finite

def rejectLeDepth (forbidden : List Nat) (k width : Nat) (pool : List Nat) :
    Nat → Nat → List Nat → Bool
  | 0,s,ws => if ws == [Live.goal k] then false else !(Fast.covers k s ws) || scr k width s pool ws
  | d+1,s,ws => if ws == [Live.goal k] then false else
      !(Fast.covers k s ws) || scr k width s pool ws ||
        match s with
        | 0 => true
        | s+1 => !(Reduced.next forbidden (Live.mask k) (s+2-ws.length) ws fun _ zs =>
            !(rejectLeDepth forbidden k width pool d s zs))

theorem rejectLeDepth_eq (forbidden : List Nat) (k width : Nat) (pool : List Nat)
    (d s : Nat) (ws : List Nat) :
    rejectLeDepth forbidden k width pool d s ws =
      Reduced.rejectLeDepth forbidden k width pool d s ws := by
  induction d generalizing s ws with
  | zero => simp [rejectLeDepth, Reduced.rejectLeDepth, Fast.covers_eq, scr_eq]
  | succ d ih => cases s <;> simp [rejectLeDepth, Reduced.rejectLeDepth, Fast.covers_eq, scr_eq, ih]

def pairedBar (forbidden : List Nat) (k width : Nat)
    (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (idx : Nat → Nat → Nat → Nat)
    (ori : Nat → Nat → Nat → List Nat → List Nat)
    (pool : List Nat) : Nat → Nat → Bool
  | 0, i => !(S 0 i == [Live.goal k])
  | s+1, i =>
    let ws := S (s+1) i
    !(Reduced.next forbidden (Live.mask k) (s+2-ws.length) ws fun tag zs =>
      Fast.covers k s zs && !(scr k width s pool zs) &&
        !(decide (idx (s+1) i tag < N s) &&
          (ori (s+1) i tag zs).isPerm (S s (idx (s+1) i tag))))

theorem pairedBar_eq (forbidden : List Nat) (k width : Nat)
    (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (idx : Nat → Nat → Nat → Nat)
    (ori : Nat → Nat → Nat → List Nat → List Nat)
    (pool : List Nat) (s i : Nat) :
    pairedBar forbidden k width S N idx ori pool s i =
      Reduced.pairedBar forbidden k width S N idx ori pool s i := by
  cases s <;> simp [pairedBar, Reduced.pairedBar, Fast.covers_eq, scr_eq]

end PEqualNP.Outside.L_meta_982_aux.Finite.Early
