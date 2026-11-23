import C7Closure
import C7NoGoal
import Seed8Symmetry
open PEqualNP.MetaComplexity

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

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Reduced
open PEqualNP.Outside.L_meta_982_aux.Finite.Live

theorem lower_from_rows {n bound : Nat} (f : BFn n) (rows : List Nat)
    (initial forbidden : List Nat) (m y : Nat)
    (hnc : ∃ x z, f x ≠ f z)
    (hcover : ∀ x : Fin n → Bool, ∃ v ∈ rows, pt n v = x)
    (hi : (List.ofFn (fun i : Fin n => fun x : Fin n → Bool => x i)).map
      (fun g => encL g rows) = initial)
    (hf : (forbiddenFns n).map (fun g => encL g rows) = forbidden)
    (hm : 2^rows.length-1 = m) (hy : encL f rows = y)
    (hn : initial.Nodup)
    (he : ∀ a ∈ initial, ∃ i j : Nat, m.testBit i = m.testBit j ∧
      y.testBit i ≠ y.testBit j ∧ ∀ b ∈ initial, b ≠ a → b.testBit i = b.testBit j)
    (hno : ∀ t < bound, ¬ RNatRun forbidden m y t initial) :
    ∀ s, HasCircuitSize n f s → bound ≤ s := by
  intro s hs
  by_contra! hlt
  obtain ⟨t,ht,ws,hsub,hrun⟩ := exists_run f hnc s hs
  have hr := encoded_run_rows rows hcover hrun
  rw [hf,hm,hy] at hr
  have hsub' : (ws.map (fun g => encL g rows)).Sublist initial := by
    rw [←hi]
    exact hsub.map _
  have hp := initial_full hn hsub' he hr.toRun
  exact hno t (by omega) (RRun.perm hp hr)

end PEqualNP.Outside.L_meta_982_aux.Finite.Reduced
namespace PEqualNP.Outside.L_meta_982_aux.Finite
open Live Reduced

def seed8Fn : BFn 7 := fun x => (x 0 && x 1) || (x 0 && x 2) || (x 1 && x 3) || (x 2 && x 4) || (x 3 && x 5) || (x 4 && x 6) || (x 5 && x 6)
def seed8Pack (x : Fin 7 → Bool) : Nat := (List.ofFn x).foldr Nat.bit 0

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed8Pack_spec (x : Fin 7 → Bool) :
    seed8Pack x < 128 ∧ pt 7 (seed8Pack x) = x := by
  revert x
  decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed8Rows_cover : ∀ x : Fin 7 → Bool, ∃ v ∈ seed8Rows, pt 7 v = x := by
  have hmem : ∀ v : Fin 128, v.val ∈ seed8Rows := by decide +kernel
  intro x
  obtain ⟨hb,he⟩ := seed8Pack_spec x
  exact ⟨seed8Pack x,hmem ⟨_,hb⟩,he⟩

def seed8Witnesses : List (Nat × Nat) := [(100, 218), (99, 218), (99, 219), (100, 221), (101, 227), (106, 240), (116, 269)]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed8Essential : ∀ a ∈ seed8Inputs, ∃ i j : Nat,
    seed8Mask.testBit i = seed8Mask.testBit j ∧
    seed8Goal.testBit i ≠ seed8Goal.testBit j ∧
    ∀ b ∈ seed8Inputs, b ≠ a → b.testBit i = b.testBit j := by
  have hc : ∀ a ∈ seed8Inputs, ∃ p : Fin 7,
      seed8Mask.testBit (seed8Witnesses.getD p.val (0,0)).1 =
        seed8Mask.testBit (seed8Witnesses.getD p.val (0,0)).2 ∧
      seed8Goal.testBit (seed8Witnesses.getD p.val (0,0)).1 ≠
        seed8Goal.testBit (seed8Witnesses.getD p.val (0,0)).2 ∧
      ∀ b ∈ seed8Inputs, b ≠ a →
        b.testBit (seed8Witnesses.getD p.val (0,0)).1 =
          b.testBit (seed8Witnesses.getD p.val (0,0)).2 := by decide +kernel
  intro a ha
  obtain ⟨p,hp⟩ := hc a ha
  exact ⟨(seed8Witnesses.getD p.val (0,0)).1,(seed8Witnesses.getD p.val (0,0)).2,hp⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem seed8Lower_of_noRun
    (hno : ∀ t < 10, ¬ RNatRun seed8Forbidden seed8Mask seed8Goal t seed8Inputs) :
    ∀ s, HasCircuitSize 7 seed8Fn s → 10 ≤ s := by
  apply lower_from_rows seed8Fn seed8Rows seed8Inputs seed8Forbidden seed8Mask seed8Goal
  · exact ⟨(fun _ => false),(fun _ => true),by decide +kernel⟩
  · exact seed8Rows_cover
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · exact seed8Essential
  · exact hno

end PEqualNP.Outside.L_meta_982_aux.Finite

namespace PEqualNP.Outside.L_meta_982_aux.Finite
open Reduced
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
theorem seed8_lower : ∀ s, HasCircuitSize 7 seed8Fn s → 10 ≤ s := by
  apply seed8Lower_of_noRun
  intro t ht h
  have hn := pairedBar_all_le (cap := 9) seed8Orient_preserves seed8_checked seed8_noGoal
  apply hn 9 (by omega) 0 (by decide +kernel) t (by omega)
  have hm : seed8Mask = Live.mask seed8K := by decide +kernel
  have hy : seed8Goal = Live.goal seed8K := by decide +kernel
  rw [hm,hy] at h
  exact RRun.perm seed8_root_perm.symm h

end PEqualNP.Outside.L_meta_982_aux.Finite
