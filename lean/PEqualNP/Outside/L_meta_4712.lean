import Mathlib
import PEqualNP.Defs
import PEqualNP.MetaComplexity.Helpers.LowerPart

namespace PEqualNP.Outside.L_meta_4712

open PEqualNP.CircuitLowerBounds
open PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.NestedCover
open PEqualNP.MetaComplexity.FoldProg
open PEqualNP.MetaComplexity.LowerPart
open PEqualNP.TopForm
open PEqualNP.CleanedNonEdge
open PEqualNP.SplitCount (unitInput)
open PEqualNP.EdgeOwnership (gateVal pairInput)

variable {n : ℕ}

abbrev U (C : Circuit) (L : ℕ) (y : Fin n) : Prop := wireVal n C L (unitInput y) = true

abbrev HasPt (C : Circuit) (s : Fin n → Bool) (w : Fin n) (L : ℕ) : Prop := ∃ y, U C L y ∧ s y ≠ s w

abbrev GLike (C : Circuit) (g : ℕ) (L : ℕ) : Prop := OrReaches n C L g ∧ ∀ y : Fin n, ¬ U C L y

abbrev N (C : Circuit) (g : ℕ) (s : Fin n → Bool) (w : Fin n) (L : ℕ) (x : Fin n → Bool) : Prop :=
  (∃ y, x y = true ∧ U C L y ∧ (HasPt C s w L → s y ≠ s w)) ∨
    (OrReaches n C L g ∧ x w = true ∧ ¬ HasPt C s w L)

open Classical in
noncomputable def rho (C : Circuit) (g : ℕ) (s : Fin n → Bool) (w : Fin n) (k : ℕ) (b : Fin 2) : Src n ℕ :=
  if (gateAt C k).op = GateOp.and then
    (if GLike (n := n) C g (opnd C k b) then
      (if HasPt C s w (opnd C k (1 - b)) then some (Sum.inl w) else none)
    else srcOf n (opnd C k b))
  else
    (if HasPt C s w (n + k) ∧ ¬ HasPt C s w (opnd C k b) then none
    else if GLike (n := n) C g (opnd C k b) then some (Sum.inl w) else srcOf n (opnd C k b))

structure Hyp (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ) (s : Fin n → Bool)
    (w : Fin n) : Prop where
  H : OneDirty G C g
  bip : ∀ u v : Fin n, G.Adj u v → s u ≠ s v
  g1 : ∀ x : Fin n → Bool, gateVal n C g x = true → x w = true
  g3 : ∃ a0 : Fin n, s a0 ≠ s w ∧ ¬ G.Adj w a0 ∧
    ∀ x : Fin n → Bool, x w = true → x a0 = true → gateVal n C g x = true
  gu : ∀ y : Fin n, gateVal n C g (unitInput y) = false

theorem bool3 (a b c : Bool) (h1 : a ≠ c) (h2 : b ≠ c) : a = b := by
  cases a <;> cases b <;> cases c <;> simp_all

theorem sub_sub (b : Fin 2) : 1 - (1 - b) = b := by
  fin_cases b <;> rfl

theorem U_in (C : Circuit) (L : ℕ) (hL : L < n) (y : Fin n) : U C L y ↔ y = ⟨L, hL⟩ := by
  show wireVal n C L (unitInput y) = true ↔ _
  rw [wireVal_lt C L hL]
  simp only [unitInput, decide_eq_true_eq]
  exact eq_comm

theorem N_in (C : Circuit) (g : ℕ) (s : Fin n → Bool) (w : Fin n) (L : ℕ) (hL : L < n) (x : Fin n → Bool) :
    N C g s w L x ↔ x ⟨L, hL⟩ = true := by
  constructor
  · rintro (⟨y, hxy, hU, _⟩ | ⟨hR, _, _⟩)
    · rw [U_in C L hL] at hU
      rw [← hU]; exact hxy
    · exact absurd hR (reach_input C L g hL)
  · intro h
    refine Or.inl ⟨⟨L, hL⟩, h, (U_in C L hL _).2 rfl, ?_⟩
    rintro ⟨y, hU, hp⟩
    rw [U_in C L hL] at hU
    rw [← hU]; exact hp

theorem srcN (C : Circuit) (g : ℕ) (s : Fin n → Bool) (w : Fin n) (x : Fin n → Bool) (u : ℕ → Bool)
    (hu : ∀ j, u j = true ↔ N C g s w (n + j) x) (L : ℕ) :
    srcAt x u (srcOf n L) = true ↔ N C g s w L x := by
  unfold srcOf
  split_ifs with hL
  · exact (N_in C g s w L hL x).symm
  · show u (L - n) = true ↔ _
    rw [hu, show n + (L - n) = L by omega]

theorem srcN' (C : Circuit) (g : ℕ) (s : Fin n → Bool) (w : Fin n) (x : Fin n → Bool) (u : ℕ → Bool)
    (hu : ∀ j, N C g s w (n + j) x → u j = true) (L : ℕ) (h : N C g s w L x) :
    srcAt x u (srcOf n L) = true := by
  unfold srcOf
  split_ifs with hL
  · exact (N_in C g s w L hL x).1 h
  · show u (L - n) = true
    apply hu
    rw [show n + (L - n) = L by omega]
    exact h

section

variable {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {g : ℕ} {s : Fin n → Bool} {w : Fin n}

theorem reach_low (P : Hyp G C g s w) (j : ℕ) (hj : j < C.gates.length) (hr : OrReaches n C (n + j) g) :
    ¬ BelowF G C j := fun hb =>
  P.H.dirty (fun x hx => hb x ((reach_le C P.H.ao g _ (by omega) hr).2 x hx))

theorem below_noU (j : ℕ) (hb : BelowF G C j) (y : Fin n) : ¬ U C (n + j) y := by
  intro h
  have h2 := hb _ h
  rw [unit_false] at h2
  exact Bool.false_ne_true h2

theorem and_bc (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.and)
    (b : Fin 2) (x : Fin n → Bool) : gateVal n C k x = true ↔
      wireVal n C (opnd C k b) x = true ∧ wireVal n C (opnd C k (1 - b)) x = true := by
  rw [val_and C hC k hk ho x]
  fin_cases b
  · exact Iff.rfl
  · exact and_comm

theorem pair_adj (P : Hyp G C g s w) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.and) (hkg : k ≠ g) (b : Fin 2) (y z : Fin n)
    (hy : U C (opnd C k b) y) (hz : U C (opnd C k (1 - b)) z) : G.Adj y z := by
  fin_cases b
  · exact and_pair P.H k hk ho hkg y z hy hz
  · exact (and_pair P.H k hk ho hkg z y hz hy).symm

theorem nb (P : Hyp G C g s w) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.and) (b : Fin 2) :
    ¬ (OrReaches n C (opnd C k b) g ∧ OrReaches n C (opnd C k (1 - b)) g) := by
  fin_cases b
  · exact not_both P.H k hk ho
  · exact fun h => not_both P.H k hk ho ⟨h.2, h.1⟩

theorem U_or (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.or)
    (y : Fin n) : U C (n + k) y ↔ ∃ b, U C (opnd C k b) y := by
  show gateVal n C k _ = true ↔ _
  rw [val_or C hC k hk ho]
  constructor
  · rintro (h | h)
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  · rintro ⟨b, h⟩
    fin_cases b
    · exact Or.inl h
    · exact Or.inr h

theorem top_true (P : Hyp G C g s w) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.and) (hkg : k ≠ g) (b : Fin 2)
    (hr : OrReaches n C (opnd C k b) g) (y : Fin n) (hy : U C (opnd C k (1 - b)) y)
    (x : Fin n → Bool) (hg : gateVal n C g x = true) (hxy : x y = true) : graphFun G ∅ x = true := by
  have hb := opnd_lt C P.H.ao k hk b
  have hc := opnd_lt C P.H.ao k hk (1 - b)
  refine P.H.others k hk ho hkg x ((and_bc P.H.ao k hk ho b x).2 ⟨?_, ?_⟩)
  · exact (reach_le C P.H.ao g _ (by omega) hr).2 x hg
  · refine mono C P.H.ao (unitInput y) x ?_ _ (by omega) hy
    intro a ha
    simp only [unitInput, decide_eq_true_eq] at ha
    rw [ha]; exact hxy

theorem wy (P : Hyp G C g s w) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.and) (hkg : k ≠ g) (b : Fin 2)
    (hr : OrReaches n C (opnd C k b) g) (y : Fin n) (hy : U C (opnd C k (1 - b)) y)
    (hp : s y ≠ s w) : G.Adj w y := by
  obtain ⟨a0, ha, hna, hg⟩ := P.g3
  have hF := top_true P k hk ho hkg b hr y hy (fun v => decide (v = w ∨ v = a0 ∨ v = y))
    (hg _ (by simp) (by simp)) (by simp)
  obtain ⟨u, v, huv, hu, hv⟩ := (graphFun_empty G _).1 hF
  simp only [decide_eq_true_eq] at hu hv
  have hb := P.bip u v huv
  rcases hu with rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl
  · exact absurd rfl hb
  · exact absurd huv hna
  · exact huv
  · exact absurd huv.symm hna
  · exact absurd rfl hb
  · exact absurd (bool3 _ _ _ ha hp) hb
  · exact huv.symm
  · exact absurd (bool3 _ _ _ hp ha) hb
  · exact absurd rfl hb

theorem notUw (P : Hyp G C g s w) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.and) (hkg : k ≠ g) (b : Fin 2)
    (hr : OrReaches n C (opnd C k b) g) : ¬ U C (opnd C k (1 - b)) w := by
  intro hy
  obtain ⟨a0, ha, hna, hg⟩ := P.g3
  have hF := top_true P k hk ho hkg b hr w hy (pairInput w a0)
    (hg _ (by simp [pairInput]) (by simp [pairInput])) (by simp [pairInput])
  obtain ⟨u, v, huv, hu, hv⟩ := (graphFun_empty G _).1 hF
  simp only [pairInput, decide_eq_true_eq] at hu hv
  have hb := P.bip u v huv
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact absurd rfl hb
  · exact absurd huv hna
  · exact absurd huv.symm hna
  · exact absurd rfl hb

theorem rho_and_gl_pt (ho : (gateAt C k).op = GateOp.and) (b : Fin 2) (h : GLike (n := n) C g (opnd C k b))
    (h2 : HasPt C s w (opnd C k (1 - b))) : rho C g s w k b = some (Sum.inl w) := by
  unfold rho
  rw [if_pos ho, if_pos h, if_pos h2]

theorem rho_and_gl_npt (ho : (gateAt C k).op = GateOp.and) (b : Fin 2) (h : GLike (n := n) C g (opnd C k b))
    (h2 : ¬ HasPt C s w (opnd C k (1 - b))) : rho C g s w k b = none := by
  unfold rho
  rw [if_pos ho, if_pos h, if_neg h2]

theorem rho_and_ngl (ho : (gateAt C k).op = GateOp.and) (b : Fin 2) (h : ¬ GLike (n := n) C g (opnd C k b)) :
    rho C g s w k b = srcOf n (opnd C k b) := by
  unfold rho
  rw [if_pos ho, if_neg h]

theorem op_ne (ho : (gateAt C k).op = GateOp.or) : ¬ (gateAt C k).op = GateOp.and := by
  rw [ho]; exact fun h => by cases h

theorem rho_or_1 (ho : (gateAt C k).op = GateOp.or) (b : Fin 2)
    (h : HasPt C s w (n + k) ∧ ¬ HasPt C s w (opnd C k b)) : rho C g s w k b = none := by
  unfold rho
  rw [if_neg (op_ne ho), if_pos h]

theorem rho_or_2 (ho : (gateAt C k).op = GateOp.or) (b : Fin 2)
    (h : ¬ (HasPt C s w (n + k) ∧ ¬ HasPt C s w (opnd C k b))) (h2 : GLike (n := n) C g (opnd C k b)) :
    rho C g s w k b = some (Sum.inl w) := by
  unfold rho
  rw [if_neg (op_ne ho), if_neg h, if_pos h2]

theorem rho_or_3 (ho : (gateAt C k).op = GateOp.or) (b : Fin 2)
    (h : ¬ (HasPt C s w (n + k) ∧ ¬ HasPt C s w (opnd C k b))) (h2 : ¬ GLike (n := n) C g (opnd C k b)) :
    rho C g s w k b = srcOf n (opnd C k b) := by
  unfold rho
  rw [if_neg (op_ne ho), if_neg h, if_neg h2]

theorem rho_inr (k : ℕ) (b : Fin 2) (j : ℕ) (h : rho C g s w k b = some (Sum.inr j)) :
    opnd C k b = n + j ∧ ¬ GLike (n := n) C g (opnd C k b) := by
  classical
  unfold rho at h
  split_ifs at h with h1 h2 h3 h4 h5
  · cases h
  · exact ⟨srcOf_inr _ _ h, h2⟩
  · cases h
  · exact ⟨srcOf_inr _ _ h, h5⟩

theorem hup_or (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.or)
    (x : Fin n → Bool) (u : ℕ → Bool) (hu : ∀ j, u j = true ↔ N C g s w (n + j) x) (b : Fin 2)
    (h : srcAt x u (rho C g s w k b) = true) : N C g s w (n + k) x := by
  by_cases h1 : HasPt C s w (n + k) ∧ ¬ HasPt C s w (opnd C k b)
  · rw [rho_or_1 ho b h1] at h
    exact absurd h Bool.false_ne_true
  · by_cases h2 : GLike (n := n) C g (opnd C k b)
    · rw [rho_or_2 ho b h1 h2] at h
      refine Or.inr ⟨(reach_gate C hC k g hk).2 (Or.inr ⟨ho, b, h2.1⟩), h, fun hk' => h1 ⟨hk', ?_⟩⟩
      rintro ⟨y, hU, _⟩
      exact h2.2 y hU
    · rw [rho_or_3 ho b h1 h2, srcN C g s w x u hu] at h
      rcases h with ⟨y, hxy, hU, hpt⟩ | ⟨hR, hxw, hnp⟩
      · exact Or.inl ⟨y, hxy, (U_or hC k hk ho y).2 ⟨b, hU⟩,
          fun hk' => hpt (by_contra fun hnl => h1 ⟨hk', hnl⟩)⟩
      · exact Or.inr ⟨(reach_gate C hC k g hk).2 (Or.inr ⟨ho, b, hR⟩), hxw, fun hk' => h1 ⟨hk', hnp⟩⟩

theorem F_of (x : Fin n → Bool) (a c : Fin n) (h : G.Adj a c) (ha : x a = true) (hc : x c = true) :
    graphFun G ∅ x = true := (graphFun_empty G x).2 ⟨a, c, h, ha, hc⟩

theorem core2 (P : Hyp G C g s w) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.and) (hkg : k ≠ g) (b : Fin 2) (x : Fin n → Bool)
    (hgl : ¬ GLike (n := n) C g (opnd C k b))
    (hb : OrReaches n C (opnd C k b) g ∧ x w = true ∧ ¬ HasPt C s w (opnd C k b))
    (hc : N C g s w (opnd C k (1 - b)) x) : graphFun G ∅ x = true := by
  obtain ⟨hR, hxw, hnp⟩ := hb
  rcases hc with ⟨y, hxy, hU, _⟩ | ⟨hR', _, _⟩
  · have hl : ∃ l : Fin n, U C (opnd C k b) l := by
      by_contra hne
      exact hgl ⟨hR, fun l hl => hne ⟨l, hl⟩⟩
    obtain ⟨l, hl⟩ := hl
    have hsl : s l = s w := by
      by_contra hne
      exact hnp ⟨l, hl, hne⟩
    have hly := P.bip l y (pair_adj P k hk ho hkg b l y hl hU)
    have hp : s y ≠ s w := by
      rw [← hsl]; exact fun e => hly e.symm
    exact F_of x w y (wy P k hk ho hkg b hR y hU hp) hxw hxy
  · exact absurd ⟨hR, hR'⟩ (nb P k hk ho b)

theorem hup_and (P : Hyp G C g s w) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.and) (hkg : k ≠ g)
    (x : Fin n → Bool) (u : ℕ → Bool) (hu : ∀ j, u j = true ↔ N C g s w (n + j) x) (b : Fin 2)
    (hb : srcAt x u (rho C g s w k b) = true) (hc : srcAt x u (rho C g s w k (1 - b)) = true) :
    GLike (n := n) C g (opnd C k (1 - b)) ∨ graphFun G ∅ x = true := by
  by_cases h2 : GLike (n := n) C g (opnd C k (1 - b))
  · exact Or.inl h2
  right
  rw [rho_and_ngl ho (1 - b) h2, srcN C g s w x u hu] at hc
  by_cases h1 : GLike (n := n) C g (opnd C k b)
  · by_cases h3 : HasPt C s w (opnd C k (1 - b))
    · rw [rho_and_gl_pt ho b h1 h3] at hb
      rcases hc with ⟨y, hxy, hU, hpt⟩ | ⟨hR', _, _⟩
      · exact F_of x w y (wy P k hk ho hkg b h1.1 y hU (hpt h3)) hb hxy
      · exact absurd ⟨h1.1, hR'⟩ (nb P k hk ho b)
    · rw [rho_and_gl_npt ho b h1 h3] at hb
      exact absurd hb Bool.false_ne_true
  · rw [rho_and_ngl ho b h1, srcN C g s w x u hu] at hb
    rcases hb with ⟨y, hxy, hU, hpt⟩ | hb
    · rcases hc with ⟨z, hxz, hUz, _⟩ | hc
      · exact F_of x y z (pair_adj P k hk ho hkg b y z hU hUz) hxy hxz
      · have e := sub_sub b
        refine core2 P k hk ho hkg (1 - b) x h2 hc ?_
        rw [e]
        exact Or.inl ⟨y, hxy, hU, hpt⟩
    · exact core2 P k hk ho hkg b x h1 hb hc

theorem hup_and' (P : Hyp G C g s w) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.and) (hkg : k ≠ g)
    (x : Fin n → Bool) (u : ℕ → Bool) (hu : ∀ j, u j = true ↔ N C g s w (n + j) x)
    (h0 : srcAt x u (rho C g s w k 0) = true) (h1 : srcAt x u (rho C g s w k 1) = true) :
    graphFun G ∅ x = true := by
  rcases hup_and P k hk ho hkg x u hu 0 h0 h1 with h | h
  · rcases hup_and P k hk ho hkg x u hu 1 h1 h0 with h' | h'
    · exact absurd ⟨h'.1, h.1⟩ (not_both P.H k hk ho)
    · exact h'
  · exact h

theorem hsub_or (hC : IsAO2 n C) (k : ℕ) (hk : k < C.gates.length) (ho : (gateAt C k).op = GateOp.or)
    (hkg : g ≠ k) (x : Fin n → Bool) (u : ℕ → Bool) (hu : ∀ L, N C g s w L x → srcAt x u (srcOf n L) = true)
    (h : N C g s w (n + k) x) : ∃ b, srcAt x u (rho C g s w k b) = true := by
  rcases h with ⟨y, hxy, hU, hpt⟩ | ⟨hR, hxw, hnp⟩
  · obtain ⟨b, hUb⟩ := (U_or hC k hk ho y).1 hU
    refine ⟨b, ?_⟩
    have h1 : ¬ (HasPt C s w (n + k) ∧ ¬ HasPt C s w (opnd C k b)) :=
      fun h1 => h1.2 ⟨y, hUb, hpt h1.1⟩
    have h2 : ¬ GLike (n := n) C g (opnd C k b) := fun h2 => h2.2 y hUb
    rw [rho_or_3 ho b h1 h2]
    refine hu _ (Or.inl ⟨y, hxy, hUb, fun hL => hpt ?_⟩)
    obtain ⟨y', hU', hp'⟩ := hL
    exact ⟨y', (U_or hC k hk ho y').2 ⟨b, hU'⟩, hp'⟩
  · rcases (reach_gate C hC k g hk).1 hR with h | ⟨_, b, hRb⟩
    · exact absurd h hkg
    · refine ⟨b, ?_⟩
      have hnb : ¬ HasPt C s w (opnd C k b) := by
        rintro ⟨y', hU', hp'⟩
        exact hnp ⟨y', (U_or hC k hk ho y').2 ⟨b, hU'⟩, hp'⟩
      have h1 : ¬ (HasPt C s w (n + k) ∧ ¬ HasPt C s w (opnd C k b)) := fun h1 => hnp h1.1
      by_cases h2 : GLike (n := n) C g (opnd C k b)
      · rw [rho_or_2 ho b h1 h2]
        exact hxw
      · rw [rho_or_3 ho b h1 h2]
        exact hu _ (Or.inr ⟨hRb, hxw, hnb⟩)

theorem caseA (P : Hyp G C g s w) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.and) (hkg : k ≠ g) (x : Fin n → Bool) (u : ℕ → Bool)
    (hu : ∀ L, N C g s w L x → srcAt x u (srcOf n L) = true) (b : Fin 2) (y z : Fin n)
    (hxy : x y = true) (hU : U C (opnd C k b) y) (hUz : U C (opnd C k (1 - b)) z) :
    srcAt x u (rho C g s w k b) = true := by
  have h2 : ¬ GLike (n := n) C g (opnd C k b) := fun h2 => h2.2 y hU
  rw [rho_and_ngl ho b h2]
  refine hu _ (Or.inl ⟨y, hxy, hU, ?_⟩)
  rintro ⟨y', hU', hp'⟩
  have e1 := P.bip _ _ (pair_adj P k hk ho hkg b y' z hU' hUz)
  have e2 := P.bip _ _ (pair_adj P k hk ho hkg b y z hU hUz)
  rw [bool3 _ _ _ e2 e1]
  exact hp'

theorem caseB (P : Hyp G C g s w) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.and) (hkg : k ≠ g) (p q : Fin n) (hpq : G.Adj p q) (u : ℕ → Bool)
    (hu : ∀ L, N C g s w L (pairInput p q) → srcAt (pairInput p q) u (srcOf n L) = true) (b : Fin 2)
    (z : Fin n) (hR : OrReaches n C (opnd C k b) g) (hg : gateVal n C g (pairInput p q) = true)
    (hxz : pairInput p q z = true) (hUz : U C (opnd C k (1 - b)) z) :
    srcAt (pairInput p q) u (rho C g s w k b) = true ∧
      srcAt (pairInput p q) u (rho C g s w k (1 - b)) = true := by
  have hxw := P.g1 _ hg
  have hzw : z ≠ w := by
    rintro rfl
    exact notUw P k hk ho hkg b hR hUz
  have hsz : s z ≠ s w := by
    have h1 := P.bip p q hpq
    have hxz' := hxz
    have hxw' := hxw
    simp only [pairInput, decide_eq_true_eq] at hxz' hxw'
    rcases hxz' with rfl | rfl <;> rcases hxw' with rfl | rfl
    · exact absurd rfl hzw
    · exact h1
    · exact fun e => h1 e.symm
    · exact absurd rfl hzw
  have h2 : ¬ GLike (n := n) C g (opnd C k (1 - b)) := fun h2 => h2.2 z hUz
  constructor
  · by_cases h1 : GLike (n := n) C g (opnd C k b)
    · rw [rho_and_gl_pt ho b h1 ⟨z, hUz, hsz⟩]
      exact hxw
    · rw [rho_and_ngl ho b h1]
      refine hu _ (Or.inr ⟨hR, hxw, ?_⟩)
      rintro ⟨y', hU', hp'⟩
      have e1 := P.bip _ _ (pair_adj P k hk ho hkg b y' z hU' hUz)
      have e3 := bool3 _ _ _ hp' hsz
      exact e1 e3
  · rw [rho_and_ngl ho (1 - b) h2]
    exact hu _ (Or.inl ⟨z, hxz, hUz, fun _ => hsz⟩)

theorem top_src (P : Hyp G C g s w) (k : ℕ) (hk : k < C.gates.length)
    (ho : (gateAt C k).op = GateOp.and) (hkg : k ≠ g) (p q : Fin n) (hpq : G.Adj p q) (u : ℕ → Bool)
    (hu : ∀ L, N C g s w L (pairInput p q) → srcAt (pairInput p q) u (srcOf n L) = true)
    (hv : gateVal n C k (pairInput p q) = true) :
    srcAt (pairInput p q) u (rho C g s w k 0) = true ∧ srcAt (pairInput p q) u (rho C g s w k 1) = true := by
  obtain ⟨hv0, hv1⟩ := (val_and C P.H.ao k hk ho _).1 hv
  have hl0 := opnd_lt C P.H.ao k hk 0
  have hl1 := opnd_lt C P.H.ao k hk 1
  rw [val_low P.H _ (by omega) (low_opnd P.H k hk 0 (Or.inr ho))] at hv0
  rw [val_low P.H _ (by omega) (low_opnd P.H k hk 1 (Or.inr ho))] at hv1
  rcases hv0 with ⟨y0, hx0, hU0⟩ | ⟨hR0, hg0⟩
  · rcases hv1 with ⟨y1, hx1, hU1⟩ | ⟨hR1, hg1⟩
    · exact ⟨caseA P k hk ho hkg _ u hu 0 y0 y1 hx0 hU0 hU1, caseA P k hk ho hkg _ u hu 1 y1 y0 hx1 hU1 hU0⟩
    · have h := caseB P k hk ho hkg p q hpq u hu 1 y0 hR1 hg1 hx0 hU0
      exact ⟨h.2, h.1⟩
  · rcases hv1 with ⟨y1, hx1, hU1⟩ | ⟨hR1, hg1⟩
    · exact caseB P k hk ho hkg p q hpq u hu 0 y1 hR0 hg0 hx1 hU1
    · exact absurd ⟨hR0, hR1⟩ (not_both P.H k hk ho)

theorem isAnd_and (ρ : ℕ → Fin 2 → Src n ℕ) (ho : (gateAt C k).op = GateOp.and) :
    (progOf C ρ).isAnd k = true := by
  show isA (gateAt C k).op = true
  rw [ho]; rfl

theorem isAnd_or (ρ : ℕ → Fin 2 → Src n ℕ) (ho : (gateAt C k).op = GateOp.or) :
    (progOf C ρ).isAnd k = false := by
  show isA (gateAt C k).op = false
  rw [ho]; rfl

theorem N_below (P : Hyp G C g s w) (j : ℕ) (hj : j < C.gates.length) (hb : BelowF G C j)
    (x : Fin n → Bool) : ¬ N C g s w (n + j) x := by
  rintro (⟨y, _, hU, _⟩ | ⟨hR, _, _⟩)
  · exact below_noU j hb y hU
  · exact reach_low P j hj hR hb

theorem main (P : Hyp G C g s w) :
    ∃ D : Circuit, IsAO2 n D ∧ D.size < C.size ∧ circuitFun n D = graphFun G ∅ := by
  classical
  have hC := P.H.ao
  obtain ⟨o, hol, hout, hob⟩ := out_gate P.H
  have hGLg : GLike (n := n) C g (n + g) :=
    ⟨(reach_gate C hC g g P.H.hg).2 (Or.inl rfl), fun y hy => by
      have h := P.gu y
      have hy' : gateVal n C g (unitInput y) = true := hy
      rw [h] at hy'
      exact Bool.false_ne_true hy'⟩
  refine redirect_lt G C ((Finset.range C.gates.length).filter fun k => ¬ GLike (n := n) C g (n + k))
    (fun k hk => Finset.mem_range.1 (Finset.mem_filter.1 hk).1) (rho C g s w) ?_ (srcOf n C.output) ?_
    (adj_of_AO G C hC P.H.comp (by omega)) ?_ ?_ ⟨g, P.H.hg, Or.inl ?_⟩
  · intro k hk b j hj
    obtain ⟨hkl, _⟩ := Finset.mem_filter.1 hk
    have hkl := Finset.mem_range.1 hkl
    obtain ⟨e, hgl⟩ := rho_inr k b j hj
    have hlt := opnd_lt C hC k hkl b
    rw [e] at hgl
    exact ⟨Finset.mem_filter.2 ⟨Finset.mem_range.2 (by omega), hgl⟩, by omega⟩
  · intro j hj
    have e := srcOf_inr _ _ hj
    have ej : j = o := by omega
    subst ej
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hol, fun h => reach_low P j hol h.1 hob⟩
  · intro x hx
    refine ⟨fun j => decide (N C g s w (n + j) x), ?_, ?_⟩
    · intro k hk hv
      obtain ⟨hkl, hkg⟩ := Finset.mem_filter.1 hk
      have hkl := Finset.mem_range.1 hkl
      have hu : ∀ j, (fun j => decide (N C g s w (n + j) x)) j = true ↔ N C g s w (n + j) x :=
        fun j => decide_eq_true_iff
      rcases LeafBound.ao_op hC hkl with ho | ho
      · have hne : k ≠ g := by
          rintro rfl
          exact hkg hGLg
        rw [isAnd_and _ ho, opv_and] at hv
        have hF := hup_and' P k hkl ho hne x _ hu hv.1 hv.2
        rw [hx] at hF
        exact absurd hF Bool.false_ne_true
      · rw [isAnd_or _ ho, opv_or] at hv
        rw [hu]
        rcases hv with hv | hv
        · exact hup_or hC k hkl ho x _ hu 0 hv
        · exact hup_or hC k hkl ho x _ hu 1 hv
    · rw [hout]
      have hf : ¬ N C g s w (n + o) x := N_below P o hol hob x
      by_contra hne
      have ht : srcAt x (fun j => decide (N C g s w (n + j) x)) (srcOf n (n + o)) = true := by
        simpa using hne
      exact hf ((srcN C g s w x _ (fun j => decide_eq_true_iff) (n + o)).1 ht)
  · intro p q hpq
    have hF : graphFun G ∅ (pairInput p q) = true :=
      F_of _ p q hpq (by simp [pairInput]) (by simp [pairInput])
    obtain ⟨p0, hp0, ho0, hb0, hv0⟩ := top_down P.H _ hF
    have hp0g : p0 ≠ g := by
      rintro rfl
      exact P.H.dirty hb0
    let u : ℕ → Bool := fun j =>
      decide ((BelowF G C j ∧ OrReaches n C (n + j) p0) ∨ N C g s w (n + j) (pairInput p q))
    have hu : ∀ j, u j = true ↔
        ((BelowF G C j ∧ OrReaches n C (n + j) p0) ∨ N C g s w (n + j) (pairInput p q)) :=
      fun j => decide_eq_true_iff
    have huN : ∀ L, N C g s w L (pairInput p q) → srcAt (pairInput p q) u (srcOf n L) = true :=
      fun L h => srcN' C g s w _ u (fun j hj => (hu j).2 (Or.inr hj)) L h
    have hgate : ∀ i, srcAt (pairInput p q) u (srcOf n (n + i)) = u i := by
      intro i
      unfold srcOf
      rw [dif_neg (by omega)]
      show u (n + i - n) = u i
      rw [Nat.add_sub_cancel_left]
    refine ⟨u, ?_, ?_⟩
    · intro k hk hv
      obtain ⟨hkl, hkg⟩ := Finset.mem_filter.1 hk
      have hkl := Finset.mem_range.1 hkl
      have hne : g ≠ k := by
        rintro rfl
        exact hkg hGLg
      have htop : k = p0 → opv ((progOf C (rho C g s w)).isAnd k)
          (srcAt (pairInput p q) u (rho C g s w k 0)) (srcAt (pairInput p q) u (rho C g s w k 1)) = true := by
        rintro rfl
        rw [isAnd_and _ ho0, opv_and]
        exact top_src P k hkl ho0 hp0g p q hpq u huN hv0
      have hor : (gateAt C k).op = GateOp.or → (∃ b, srcAt (pairInput p q) u (rho C g s w k b) = true) →
          opv ((progOf C (rho C g s w)).isAnd k)
          (srcAt (pairInput p q) u (rho C g s w k 0)) (srcAt (pairInput p q) u (rho C g s w k 1)) = true := by
        rintro ho ⟨b, hb⟩
        rw [isAnd_or _ ho, opv_or]
        fin_cases b
        · exact Or.inl hb
        · exact Or.inr hb
      rcases (hu k).1 hv with ⟨hbk, hRk⟩ | hN
      · rcases (reach_gate C hC k p0 hkl).1 hRk with h | ⟨ho, b, hRb⟩
        · exact htop h.symm
        · refine hor ho ⟨b, ?_⟩
          have hlt := opnd_lt C hC k hkl b
          have hnb := hRb.1
          have e : opnd C k b = n + (opnd C k b - n) := by omega
          have hbi : BelowF G C (opnd C k b - n) := by
            intro z hz
            refine below_or hC k hkl ho hbk b z ?_
            rw [e]; exact hz
          have h1 : ¬ (HasPt C s w (n + k) ∧ ¬ HasPt C s w (opnd C k b)) := by
            rintro ⟨⟨y, hU, _⟩, _⟩
            exact below_noU k hbk y hU
          have h2 : ¬ GLike (n := n) C g (opnd C k b) := by
            intro h2
            have h3 := h2.1
            rw [e] at h3
            exact reach_low P _ (by omega) h3 hbi
          rw [rho_or_3 ho b h1 h2, e, hgate, hu]
          refine Or.inl ⟨hbi, ?_⟩
          rw [← e]; exact hRb
      · rcases LeafBound.ao_op hC hkl with ho | ho
        · exact absurd hN (N_below P k hkl (P.H.others k hkl ho (fun e => hne e.symm)) _)
        · exact hor ho (hsub_or hC k hkl ho hne _ u huN hN)
    · have ht : ∀ j < C.gates.length, (gateAt C j).op = GateOp.or → BelowF G C j → ∀ b i,
          opnd C j b = n + i → BelowF G C i → u i = true → u j = true := by
        intro j hj ho hbj b i hbi hbel hui
        have hlt := opnd_lt C hC j hj b
        rw [hu] at hui ⊢
        rcases hui with ⟨_, hR⟩ | hN
        · refine Or.inl ⟨hbj, (reach_gate C hC j p0 hj).2 (Or.inr ⟨ho, b, ?_⟩)⟩
          rw [hbi]; exact hR
        · exact absurd hN (N_below P i (by omega) hbel _)
      obtain ⟨o', ho', hto⟩ := top_up P.H u ht p0 hp0 hb0
        ((hu p0).2 (Or.inl ⟨hb0, (reach_gate C hC p0 p0 hp0).2 (Or.inl rfl)⟩))
      rw [ho', hgate]
      exact hto
  · intro hg
    exact (Finset.mem_filter.1 hg).2 hGLg

theorem mkHyp (H : OneDirty G C g) (hs : ∀ u v : Fin n, G.Adj u v → s u ≠ s v)
    (hunit : ∀ y : Fin n, gateVal n C g (unitInput y) = false) (b : Fin 2)
    (h1 : ∀ y : Fin n, wireVal n C (opnd C g b) (unitInput y) = true ↔ y = w)
    (h2 : ∀ y : Fin n, wireVal n C (opnd C g (1 - b)) (unitInput y) = true → s y ≠ s w) :
    Hyp G C g s w := by
  have hg1 : ∀ x : Fin n → Bool, gateVal n C g x = true → x w = true := by
    intro x hx
    obtain ⟨hb, _⟩ := (and_bc H.ao g H.hg H.gand b x).1 hx
    obtain ⟨y, hxy, hy⟩ := (opnd_val H b x).1 hb
    rw [(h1 y).1 hy] at hxy
    exact hxy
  refine ⟨H, hs, hg1, ?_, hunit⟩
  have hd : ∃ x : Fin n → Bool, gateVal n C g x = true ∧ ¬ graphFun G ∅ x = true := by
    by_contra hne
    apply H.dirty
    intro x hx
    by_contra hF
    exact hne ⟨x, hx, hF⟩
  obtain ⟨x, hx, hF⟩ := hd
  obtain ⟨_, hc⟩ := (and_bc H.ao g H.hg H.gand b x).1 hx
  obtain ⟨a, hxa, ha⟩ := (opnd_val H (1 - b) x).1 hc
  refine ⟨a, h2 a ha, fun hadj => hF (F_of x w a hadj (hg1 x hx) hxa), ?_⟩
  intro x' hw' ha'
  exact (and_bc H.ao g H.hg H.gand b x').2
    ⟨(opnd_val H b x').2 ⟨w, hw', (h1 w).2 rfl⟩, (opnd_val H (1 - b) x').2 ⟨a, ha', ha⟩⟩

end

end PEqualNP.Outside.L_meta_4712

theorem PEqualNP.Outside.L_meta_4712 : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : PEqualNP.CircuitLowerBounds.Circuit) (s : Fin n → Bool) (g : ℕ), (∀ u v : Fin n, G.Adj u v → s u ≠ s v) → PEqualNP.TopForm.NoFourCycle G → PEqualNP.TopForm.IsAO2 n C → PEqualNP.MetaComplexity.circuitFun n C = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ → PEqualNP.Core.IsLiftFixedPoint G C → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∀ t ∈ (PEqualNP.MetaComplexity.NestedCover.gateAt C k).inputs, ¬ (∀ x : Fin n → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨C.gates, t⟩ (List.ofFn x) = true → PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x = true)) → (∀ k < C.gates.length, PEqualNP.Core.InOutputCone n C k) → g < C.gates.length → (PEqualNP.MetaComplexity.NestedCover.gateAt C g).op = PEqualNP.CircuitLowerBounds.GateOp.and → ¬ PEqualNP.TopForm.BelowF G C g → (∀ k < C.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt C k).op = PEqualNP.CircuitLowerBounds.GateOp.and → k ≠ g → PEqualNP.TopForm.BelowF G C k) → (∀ w : Fin n, PEqualNP.EdgeOwnership.gateVal n C g (PEqualNP.SplitCount.unitInput w) = false) → ((∃ w : Fin n, (∀ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 1) (PEqualNP.SplitCount.unitInput y) = true ↔ y = w) ∧ ∀ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 0) (PEqualNP.SplitCount.unitInput y) = true → s y ≠ s w) ∨ (∃ w : Fin n, (∀ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 0) (PEqualNP.SplitCount.unitInput y) = true ↔ y = w) ∧ ∀ y : Fin n, PEqualNP.CleanedNonEdge.wireVal n C (PEqualNP.TopForm.opnd C g 1) (PEqualNP.SplitCount.unitInput y) = true → s y ≠ s w)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 n D ∧ D.size < C.size ∧ PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ := by
  intro n G _ C s g hs _ hAO hcomp hlift handL hcone hg hgand hdirty hothers hunit hw
  have H : PEqualNP.MetaComplexity.LowerPart.OneDirty G C g :=
    ⟨hAO, hcomp, hlift, handL, hcone, hg, hgand, hdirty, hothers⟩
  rcases hw with ⟨w, h1, h2⟩ | ⟨w, h1, h2⟩
  · exact PEqualNP.Outside.L_meta_4712.main (PEqualNP.Outside.L_meta_4712.mkHyp H hs hunit 1 h1 h2)
  · exact PEqualNP.Outside.L_meta_4712.main (PEqualNP.Outside.L_meta_4712.mkHyp H hs hunit 0 h1 h2)
