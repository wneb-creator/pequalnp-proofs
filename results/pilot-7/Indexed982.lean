import EarlyUpper982
namespace PEqualNP.Outside.L_meta_982_aux.Finite.Reduced
open PEqualNP.Outside.L_meta_982_aux.Finite.Live

def lookupBar (forbidden : List Nat) (m y : Nat)
    (S : Nat → Nat → List Nat) (N : Nat → Nat)
    (hint : Nat → Nat → Nat → List Nat → Nat × List Nat)
    (bad : Nat → List Nat → Bool) : Nat → Nat → Bool
  | 0,i => !(S 0 i == [y])
  | s+1,i =>
    let ws := S (s+1) i
    !(next forbidden m (s+2-ws.length) ws fun tag zs =>
      !(bad s zs) &&
        (let a := hint (s+1) i tag zs
         !(decide (a.1 < N s) && a.2.isPerm (S s a.1))))

theorem lookupBar_all_le_from_leaves {forbidden m y S N hint bad} {cap cutoff : Nat}
    (hr : ∀ p i tag {u ys}, RNatRun forbidden m y u ys →
      RNatRun forbidden m y u (hint p i tag ys).2)
    (hbad : ∀ s {t ws}, t ≤ s → RNatRun forbidden m y t ws → bad s ws = false)
    (hc : ∀ s ≤ cap, cutoff < s → ∀ i < N s,
      lookupBar forbidden m y S N hint bad s i = true)
    (hng : ∀ s ≤ cap, cutoff < s → ∀ i < N s, S s i ≠ [y])
    (hleaf : ∀ s ≤ cutoff, ∀ i < N s, ∀ t ≤ s, ¬ RNatRun forbidden m y t (S s i)) :
    ∀ s ≤ cap, ∀ i < N s, ∀ t ≤ s, ¬ RNatRun forbidden m y t (S s i) := by
  intro s
  induction s using Nat.strong_induction_on with
  | ind s ih =>
    intro hs i hi t ht h
    by_cases hl : s ≤ cutoff
    · exact hleaf s hl i hi t ht h
    have hlt : cutoff < s := by omega
    cases t with
    | zero => exact hng s hs hlt i hi (zero_done h.toRun rfl)
    | succ t =>
      cases s with
      | zero => omega
      | succ s =>
        let F (tag : Nat) (zs : List Nat) :=
          !(bad s zs) && (let a := hint (s+1) i tag zs
            !(decide (a.1 < N s) && a.2.isPerm (S s a.1)))
        have hF (tag : Nat) (zs) (hz : RNatRun forbidden m y t zs) : F tag zs = true := by
          simp only [F,hbad s (show t ≤ s by omega) hz,Bool.not_false,Bool.true_and]
          simp only [Bool.not_eq_true',Bool.and_eq_false_imp,decide_eq_true_eq]
          intro hj
          by_contra! hp
          have p := List.isPerm_iff.1 (Bool.eq_true_of_not_eq_false hp)
          exact ih s (by omega) (by omega) _ hj t (by omega)
            (RRun.perm p (hr (s+1) i tag hz))
        have hN := next_complete h t rfl _ (List.Perm.refl _) F hF
        have hN' := next_monoSlack (show t+2-(S (s+1) i).length ≤
            s+2-(S (s+1) i).length by omega) hN
        have hb := hc (s+1) hs hlt i hi
        change !(next _ _ _ _ F) = true at hb
        rw [hN'] at hb
        contradiction

theorem lookupBar_all_le {forbidden m y S N hint bad} {cap : Nat}
    (hr : ∀ p i tag {u ys}, RNatRun forbidden m y u ys →
      RNatRun forbidden m y u (hint p i tag ys).2)
    (hbad : ∀ s {t ws}, t ≤ s → RNatRun forbidden m y t ws → bad s ws = false)
    (hc : ∀ s ≤ cap, ∀ i < N s, lookupBar forbidden m y S N hint bad s i = true)
    (hng : ∀ s ≤ cap, ∀ i < N s, S s i ≠ [y]) :
    ∀ s ≤ cap, ∀ i < N s, ∀ t ≤ s, ¬ RNatRun forbidden m y t (S s i) := by
  apply lookupBar_all_le_from_leaves (cutoff:=0) hr hbad
  · intro s hs _ i hi; exact hc s hs i hi
  · intro s hs _ i hi; exact hng s hs i hi
  · intro s hs i hi t ht h
    have hs0 : s = 0 := by omega
    have ht0 : t = 0 := by omega
    subst s t
    exact hng 0 (by omega) i hi (zero_done h.toRun rfl)

end PEqualNP.Outside.L_meta_982_aux.Finite.Reduced

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Early

def bad (k width : Nat) (pool : List Nat) (s : Nat) (ws : List Nat) : Bool :=
  !(Fast.covers k s ws) || scr k width s pool ws

theorem bad_no {forbidden k width pool} (s : Nat) {t ws} (ht : t ≤ s)
    (h : Reduced.RNatRun forbidden (Live.mask k) (Live.goal k) t ws) :
    bad k width pool s ws = false := by
  simp [bad,Fast.covers_eq,scr_eq,Reduced.covers_ok_le h.toRun ht,
    Reduced.scrW_no_le width pool h.toRun ht]

end PEqualNP.Outside.L_meta_982_aux.Finite.Early
