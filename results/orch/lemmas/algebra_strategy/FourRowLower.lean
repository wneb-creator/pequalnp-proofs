import Mathlib
import PEqualNP.Outside.L_meta_723
import PEqualNP.MetaComplexity.Helpers.PermInputs
import PEqualNP.MetaComplexity.Helpers.Elim

-- Research-only: extra checked imports are not allowed by final L-meta-650.
-- The next generic elimination proof is copied from ResearchMonoElim.lean.

-- Research artifact using additional project modules.
-- This file is not eligible as the final L-meta-650 proof file.

namespace PEqualNP.Outside.L_meta_650.Research

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.Helpers

def MonoGate (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def HasMonoSize (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x

lemma monoGate_ok (g : Gate) (hm : MonoGate g) : Ok g := by
  rcases hm.1 with h | h
  · exact ⟨Or.inl h, hm.2⟩
  · exact ⟨Or.inr (Or.inl h), hm.2⟩

lemma normGate_mono (g : Gate) (hm : MonoGate g) : MonoGate (normGate g) := by
  obtain ⟨op, ins⟩ := g
  rcases hm.1 with h | h
  · have : op = GateOp.and := h
    subst op
    exact hm
  · have : op = GateOp.or := h
    subst op
    exact hm

lemma simplify_same_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

lemma elim_mono (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, MonoGate g) → (∀ g ∈ acc.2, MonoGate g) →
    ∀ g ∈ (elim n gs acc).2, MonoGate g := by
  induction gs with
  | nil => intro acc _ h; exact h
  | cons g gs ih =>
    intro acc hgs h
    apply ih (elimStep n acc g) (fun a ha => hgs a (List.mem_cons_of_mem _ ha))
    intro a ha
    rcases List.mem_append.mp ha with old | fresh
    · exact h a old
    · refine ⟨?_, (simplify_ok _ _ _ a (by simpa using fresh)).2⟩
      rw [simplify_same_op _ _ _ a (by simpa using fresh)]
      exact (hgs g List.mem_cons_self).1

theorem gate_elim_mono (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasMonoSize (n + 1) f (s + 1)) :
    HasMonoSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (monoGate_ok g0 (ok g0 hg0))
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hmono : ∀ g ∈ gs, MonoGate g := by
    intro g hg
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hg
    exact normGate_mono a (ok a ha)
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨⟨acc.2, j⟩, elim_mono n gs _ hmono (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

end PEqualNP.Outside.L_meta_650.Research

namespace PEqualNP.Outside.L_meta_650_aux.FourRow

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_650.Research

def f14 (x : Fin 14 → Bool) : Bool :=
  (x 0 && (x 4 || x 5 || x 6 || x 10)) ||
  (x 1 && (x 4 || x 7 || x 8 || x 11)) ||
  (x 2 && (x 5 || x 7 || x 9 || x 12)) ||
  (x 3 && (x 6 || x 8 || x 9 || x 13))

def f13 (x : Fin 13 → Bool) : Bool := f14 (Fin.snoc x false)
def f12 (x : Fin 12 → Bool) : Bool := f13 (Fin.snoc x false)
def f11 (x : Fin 11 → Bool) : Bool := f12 (Fin.snoc x false)
def f10 (x : Fin 10 → Bool) : Bool := f11 (Fin.snoc x false)

theorem kernel_eq : f10 = L_meta_723_aux.edgeFn := by
  funext x
  change ((x 0 && (x 4 || x 5 || x 6 || false)) ||
    (x 1 && (x 4 || x 7 || x 8 || false)) ||
    (x 2 && (x 5 || x 7 || x 9 || false)) ||
    (x 3 && (x 6 || x 8 || x 9 || false))) = L_meta_723_aux.edgeFn x
  simp only [L_meta_723_aux.edgeFn, Bool.or_false, Bool.and_or_distrib_left]
  ac_rfl

def original14 (x : Fin 14 → Bool) : Bool :=
  (x 0 && (x 4 || x 5 || x 7 || x 11)) ||
  (x 1 && (x 4 || x 6 || x 10 || x 13)) ||
  (x 2 && (x 5 || x 9 || x 12 || x 13)) ||
  (x 3 && (x 8 || x 10 || x 11 || x 12))

def canonicalToOriginal : Fin 14 → Fin 14 :=
  ![0, 1, 2, 3, 4, 5, 11, 13, 10, 12, 7, 6, 9, 8]

theorem original_eq (x : Fin 14 → Bool) :
    f14 (x ∘ canonicalToOriginal) = original14 x := by
  dsimp [f14, original14, Function.comp_apply, canonicalToOriginal]
  ac_rfl

def originalToCanonical : Fin 14 → Fin 14 :=
  ![0, 1, 2, 3, 4, 5, 11, 10, 13, 12, 8, 6, 9, 7]

theorem original_to_canonical (x : Fin 14 → Bool) :
    original14 (x ∘ originalToCanonical) = f14 x := by
  dsimp [f14, original14, Function.comp_apply, originalToCanonical]
  ac_rfl

theorem no_eighteen : ¬ HasMonoSize 14 f14 18 := by
  intro h
  have h13 : HasMonoSize 13 f13 17 :=
    gate_elim_mono 13 f14 false 17
      (by refine ⟨fun i => decide (i.val = 3), ?_⟩; decide)
      (by
        refine ⟨fun i => decide (i.val = 0 ∨ i.val = 4), fun _ => false, ?_⟩
        decide)
      h
  have h12 : HasMonoSize 12 f12 16 :=
    gate_elim_mono 12 f13 false 16
      (by refine ⟨fun i => decide (i.val = 2), ?_⟩; decide)
      (by
        refine ⟨fun i => decide (i.val = 0 ∨ i.val = 4), fun _ => false, ?_⟩
        decide)
      h13
  have h11 : HasMonoSize 11 f11 15 :=
    gate_elim_mono 11 f12 false 15
      (by refine ⟨fun i => decide (i.val = 1), ?_⟩; decide)
      (by
        refine ⟨fun i => decide (i.val = 0 ∨ i.val = 4), fun _ => false, ?_⟩
        decide)
      h12
  have h10 : HasMonoSize 10 f10 14 :=
    gate_elim_mono 10 f11 false 14
      (by refine ⟨fun i => decide (i.val = 0), ?_⟩; decide)
      (by
        refine ⟨fun i => decide (i.val = 0 ∨ i.val = 4), fun _ => false, ?_⟩
        decide)
      h11
  obtain ⟨C, hm, hsize, heval⟩ := h10
  have lower := PEqualNP.Outside.L_meta_723 C hm (by
    intro x
    rw [heval x, kernel_eq]
    exact L_meta_723_aux.edgeFn_spec x)
  omega

theorem relabel_hasMonoSize {n m : ℕ} (π : Fin n → Fin m)
    (f : (Fin n → Bool) → Bool) (s : ℕ)
    (h : HasMonoSize n f s) : HasMonoSize m (fun x => f (x ∘ π)) s := by
  obtain ⟨C, hm, hs, he⟩ := h
  refine ⟨Helpers.PermInputs.relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(hm g0 hg0).1,
      by simpa [Helpers.PermInputs.relGate] using (hm g0 hg0).2⟩
  · simpa [Helpers.PermInputs.relabel, Circuit.size] using hs
  · intro x
    change _ = f (x ∘ π)
    rw [← he (x ∘ π)]
    exact (Helpers.PermInputs.rel_fold n m π C.gates _ _
      (Helpers.PermInputs.rel_init n m π x)).2.2 C.output

theorem original_no_eighteen : ¬ HasMonoSize 14 original14 18 := by
  intro h
  have hc := relabel_hasMonoSize originalToCanonical original14 18 h
  have eqf : (fun x : Fin 14 → Bool => original14 (x ∘ originalToCanonical)) = f14 :=
    funext original_to_canonical
  rw [eqf] at hc
  exact no_eighteen hc

theorem original_lower (C : Circuit) (hm : Monotone2 C)
    (he : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = original14 x) :
    19 ≤ C.size := by
  by_contra hn
  exact original_no_eighteen ⟨C, hm, by omega, he⟩

end PEqualNP.Outside.L_meta_650_aux.FourRow
