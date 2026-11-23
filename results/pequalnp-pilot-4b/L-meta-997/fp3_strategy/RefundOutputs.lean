import Mathlib
import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_997.Window
open PEqualNP.CircuitLowerBounds
def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

lemma run_cons (g : Gate) (gs : List Gate) (x : List Bool) :
    run (g :: gs) x = run gs (x ++ [g.op.eval (g.inputs.map fun i => x.getD i false)]) :=
  rfl

lemma run_length (gs : List Gate) (x : List Bool) :
    (run gs x).length = x.length + gs.length := by
  induction gs generalizing x with
  | nil => simp [run]
  | cons g gs ih => rw [run_cons, ih]; simp; omega

lemma run_getD (gs : List Gate) (x : List Bool) (w : ℕ) (hw : w < x.length) :
    (run gs x).getD w false = x.getD w false := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [run_cons, ih _ (by simp; omega), List.getD_append _ _ _ _ hw]

lemma run_split (gs : List Gate) (x : List Bool) (j : ℕ) :
    run gs x = run (gs.drop j) (run (gs.take j) x) := by
  simpa only [run, List.foldl_append] using
    congrArg (fun l : List Gate => run l x) (List.take_append_drop j gs).symm

def value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (C.wires (List.ofFn x)).getD w false

lemma input_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (p : Fin n) :
    value C x p = x p := by
  change (run C.gates (List.ofFn x)).getD p false = x p
  have hp : (p : ℕ) < (List.ofFn x).length := by simp
  rw [run_getD _ _ _ hp, List.getD_eq_getElem _ _ hp]
  simp

lemma missing_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hw : n + C.size ≤ w) : value C x w = false := by
  change (run C.gates (List.ofFn x)).getD w false = false
  exact List.getD_eq_default _ _ (by simpa [run_length, Circuit.size] using hw)

lemma gate_value {n : ℕ} (C : Circuit) (x : Fin n → Bool) (w : ℕ)
    (hn : n ≤ w) (hw : w < n + C.size) :
    let g := C.gates[w - n]'(by unfold Circuit.size at hw; omega)
    value C x w = g.op.eval (g.inputs.map fun r => if r < w then value C x r else false) := by
  let j := w - n
  have hj : j < C.gates.length := by unfold j Circuit.size at *; omega
  let g := C.gates[j]
  let earlier := run (C.gates.take j) (List.ofFn x)
  have plen : earlier.length = w := by
    simp [earlier, run_length, Nat.min_eq_left hj.le, j]; omega
  have split : run C.gates (List.ofFn x) = run (g :: C.gates.drop (j + 1)) earlier := by
    rw [run_split C.gates (List.ofFn x) j, List.drop_eq_getElem_cons hj]
  have read (r : ℕ) : earlier.getD r false = if r < w then value C x r else false := by
    by_cases hr : r < w
    · rw [ite_eq_left hr]
      change earlier.getD r false = (run C.gates (List.ofFn x)).getD r false
      rw [split]
      exact (run_getD _ earlier r (by simpa only [plen] using hr)).symm
    · rw [ite_eq_right hr]
      exact List.getD_eq_default _ _ (by omega)
  change (run C.gates (List.ofFn x)).getD w false =
    g.op.eval (g.inputs.map fun r => if r < w then value C x r else false)
  rw (occs := [1]) [split]
  rw (occs := [1]) [run_cons]
  rw [run_getD _ _ _ (by simp [plen]), List.getD_append_right _ _ _ _ (by omega)]
  simp only [plen, Nat.sub_self, List.getD_cons_zero, read]


end PEqualNP.Outside.L_meta_997.Window
namespace PEqualNP.Outside.L_meta_997.RefundOutputs

open PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_997.Window

def refund {n m : ℕ} (S : Fin m → Finset (Fin n)) (C : Circuit)
    (y : Finset (Fin n)) : Finset (Fin C.gates.length) :=
  Finset.univ.filter fun g =>
    (∃ i, ∀ p, value C (fun v => decide (v = p)) (n + g) = true ↔ p ∈ S i) ∧
    (∃ i, Disjoint (S i) y ∧ ∀ p, p ∉ y →
      (value C (fun v => decide (v ∈ y ∨ v = p)) (n + g) = true ↔ p ∈ S i))

def largeHeavy {n m : ℕ} (S : Fin m → Finset (Fin n))
    (y : Finset (Fin n)) (k : ℕ) : Finset (Fin m) :=
  Finset.univ.filter fun i => Disjoint (S i) y ∧ k < (S i).card

theorem singleton_signature {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ)
    (hfun : ∀ i x, value C x (o i) = decide (∃ p ∈ S i, x p = true)) :
    ∀ i p, value C (fun v => decide (v = p)) (o i) = true ↔ p ∈ S i := by
  intro i p
  rw [hfun]
  simp

theorem output_gate_bounds {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ)
    (hfun : ∀ i x, value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (i : Fin m) (hi : 2 ≤ (S i).card) :
    n ≤ o i ∧ o i < n + C.gates.length := by
  obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < (S i).card)
  have hsp := (singleton_signature S C o hfun i p).mpr hp
  have hsq := (singleton_signature S C o hfun i q).mpr hq
  constructor
  · by_contra! ho
    let r : Fin n := ⟨o i, ho⟩
    change value C (fun v => decide (v = p)) r.val = true at hsp
    change value C (fun v => decide (v = q)) r.val = true at hsq
    rw [input_value] at hsp hsq
    have hrp : r = p := of_decide_eq_true hsp
    have hrq : r = q := of_decide_eq_true hsq
    exact hpq (hrp.symm.trans hrq)
  · by_contra! ho
    rw [missing_value C _ (o i) (by simpa [Circuit.size] using ho)] at hsp
    exact Bool.false_ne_true hsp

theorem disjoint_output_refunded {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (y : Finset (Fin n))
    (hfun : ∀ i x, value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (i : Fin m) (hi : 2 ≤ (S i).card) (hiy : Disjoint (S i) y) :
    ∃ g ∈ refund S C y, n + (g : ℕ) = o i := by
  have hb := output_gate_bounds S C o hfun i hi
  let g : Fin C.gates.length := ⟨o i - n, by omega⟩
  have hg : n + (g : ℕ) = o i := by dsimp [g]; omega
  refine ⟨g, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, hg⟩
  constructor
  · exact ⟨i, fun p => hg ▸ singleton_signature S C o hfun i p⟩
  · refine ⟨i, hiy, ?_⟩
    intro p _
    rw [hg, hfun, decide_eq_true_eq]
    constructor
    · rintro ⟨q, hq, hval⟩
      have hv : q ∈ y ∨ q = p := of_decide_eq_true hval
      rcases hv with hqy | rfl
      · exact False.elim (Finset.disjoint_left.mp hiy hq hqy)
      · exact hq
    · intro hp
      exact ⟨p, hp, by simp⟩

theorem large_heavy_refund_bound {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (y : Finset (Fin n)) (k : ℕ)
    (hk : 1 ≤ k)
    (hint : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hfun : ∀ i x, value C x (o i) = decide (∃ p ∈ S i, x p = true)) :
    (largeHeavy S y k).card ≤ (refund S C y).card := by
  classical
  have hinj : Set.InjOn o (↑(largeHeavy S y k) : Set (Fin m)) := by
    intro i hi j hj hij
    by_contra hne
    have hset : S i = S j := by
      ext p
      rw [← singleton_signature S C o hfun i p, hij,
        singleton_signature S C o hfun j p]
    have hlarge := (Finset.mem_filter.mp hi).2.2
    have hsmall := hint i j hne
    rw [hset, Finset.inter_self] at hsmall
    rw [hset] at hlarge
    omega
  have hsub : (largeHeavy S y k).image o ⊆
      (refund S C y).image (fun g : Fin C.gates.length => n + (g : ℕ)) := by
    intro w hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hw
    have hd := (Finset.mem_filter.mp hi).2
    obtain ⟨g, hg, heq⟩ := disjoint_output_refunded S C o y hfun i (by omega) hd.1
    exact Finset.mem_image.mpr ⟨g, hg, heq⟩
  calc
    (largeHeavy S y k).card = ((largeHeavy S y k).image o).card :=
      (Finset.card_image_iff.mpr hinj).symm
    _ ≤ ((refund S C y).image (fun g : Fin C.gates.length => n + (g : ℕ))).card := Finset.card_le_card hsub
    _ ≤ (refund S C y).card := Finset.card_image_le

theorem bounded_heavy_size_finish {n m : ℕ} (S : Fin m → Finset (Fin n))
    (C : Circuit) (o : Fin m → ℕ) (y : Finset (Fin n)) (k : ℕ)
    (hk : 1 ≤ k)
    (hint : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (hfun : ∀ i x, value C x (o i) = decide (∃ p ∈ S i, x p = true))
    (hsize : ∀ i, Disjoint (S i) y → (S i).card ≤ k + 1)
    (hlight : (∑ i, min k (S i).card) ≤ C.gates.length + m) :
    (∑ i, if Disjoint (S i) y then (S i).card else min k (S i).card) ≤
      C.gates.length + (refund S C y).card + m := by
  classical
  have hterm : ∀ i : Fin m,
      (if Disjoint (S i) y then (S i).card else min k (S i).card) ≤
      min k (S i).card + (if Disjoint (S i) y ∧ k < (S i).card then 1 else 0) := by
    intro i
    by_cases hd : Disjoint (S i) y
    · have hs := hsize i hd
      by_cases hbig : k < (S i).card
      · simp [hd, hbig, Nat.min_eq_left (by omega : k ≤ (S i).card)]
        omega
      · simp [hd, hbig, Nat.min_eq_right (by omega : (S i).card ≤ k)]
    · simp [hd]
  have hs := Finset.sum_le_sum (s := Finset.univ) (fun i _ => hterm i)
  simp only [Finset.sum_add_distrib] at hs
  have hcount : (∑ i : Fin m, if Disjoint (S i) y ∧ k < (S i).card then 1 else 0) =
      (largeHeavy S y k).card := by simp [largeHeavy]
  rw [hcount] at hs
  have hr := large_heavy_refund_bound S C o y k hk hint hfun
  omega

end PEqualNP.Outside.L_meta_997.RefundOutputs
