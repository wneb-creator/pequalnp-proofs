import Mathlib
import PEqualNP.MetaComplexity.Helpers.Elim
import PEqualNP.MetaComplexity.Helpers.PermInputs
import PEqualNP.MetaComplexity.Helpers.Hardwire
import PEqualNP.MetaComplexity.L106

namespace PEqualNP.Outside.L_meta_650_aux.FourOwnerFreeRestriction

open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds

theorem gate_elim_false_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool)
    (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y, f (Function.update x p false) ≠ f (Function.update y p false))
    (h : HasCircuitSize (n + 1) f (s + 1)) :
    HasCircuitSize (n + 1) (fun x => f (Function.update x p false)) s := by
  let σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n)
  have hg := Helpers.PermInputs.relabel_size (⇑σ) f (s + 1) h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [σ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    simp [σ, Equiv.symm_swap]
  have hd : ∃ x : Fin (n + 1) → Bool,
      (fun y => f (y ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun y => f (y ∘ σ)) x := by
    obtain ⟨x, hx⟩ := hdep
    refine ⟨x ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    simpa [σ] using hx
  have hn : ∃ x y : Fin n → Bool,
      f (Fin.snoc x false ∘ σ) ≠ f (Fin.snoc y false ∘ σ) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simpa [σ, Helpers.PermInputs.snoc_swap] using hxy
  have he := Helpers.gate_elim n (fun x => f (x ∘ σ)) false s hd hn hg
  have hr := Helpers.PermInputs.relabel_size (fun j : Fin n => σ j.castSucc) _ s he
  have e : (fun x : Fin (n + 1) → Bool =>
      f (Fin.snoc (x ∘ fun j : Fin n => σ j.castSucc) false ∘ σ)) =
      (fun x => f (Function.update x p false)) := by
    funext x
    exact congrArg f (Helpers.PermInputs.snoc_swap n p x false)
  rwa [e] at hr

def HasEncoded {R N : ℕ} (E : (Fin R → Bool) → Fin N → Bool)
    (f : (Fin R → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ C.size ≤ s ∧ ∀ x, C.eval (List.ofFn (E x)) = f x

theorem encoded_elim {R n : ℕ}
    (E E' : (Fin R → Bool) → Fin (n + 1) → Bool)
    (f f' : (Fin R → Bool) → Bool) (σ : Fin (n + 1) → Fin (n + 1))
    (p : Fin (n + 1)) (ρ : (Fin R → Bool) → Fin R → Bool)
    (hfix : ∀ x, E x ∘ σ = E x)
    (hnext : ∀ x, E' x = E (ρ x)) (hfnext : ∀ x, f' x = f (ρ x))
    (hzero : ∀ x, E' x p = false)
    (x0 x1 : Fin R → Bool)
    (hw : Function.update (E x0) p (!(E x0 p)) ∘ σ = E x1)
    (hf : f x1 ≠ f x0)
    (hnc : ∃ x y, f' x ≠ f' y)
    (s : ℕ) (h : HasEncoded E f (s + 1)) : HasEncoded E' f' s := by
  obtain ⟨C, hfan, hsize, hev⟩ := h
  let g : (Fin (n + 1) → Bool) → Bool := fun y => C.eval (List.ofFn (y ∘ σ))
  have hg : HasCircuitSize (n + 1) g (s + 1) :=
    Helpers.PermInputs.relabel_size σ _ (s + 1) ⟨C, hfan, hsize, fun _ => rfl⟩
  have hc : ∀ x, g (E x) = f x := by
    intro x
    change C.eval (List.ofFn (E x ∘ σ)) = f x
    rw [hfix, hev]
  have hc' : ∀ x, g (Function.update (E' x) p false) = f' x := by
    intro x
    rw [← hzero x, Function.update_eq_self, hnext, hc, ← hfnext]
  have hd : ∃ y, g (Function.update y p (!y p)) ≠ g y := by
    refine ⟨E x0, ?_⟩
    change C.eval (List.ofFn (Function.update (E x0) p (!(E x0 p)) ∘ σ)) ≠ g (E x0)
    rw [hw, hev, hc]
    exact hf
  have hn : ∃ x y, g (Function.update x p false) ≠ g (Function.update y p false) := by
    obtain ⟨x, y, hxy⟩ := hnc
    exact ⟨E' x, E' y, by simpa only [hc'] using hxy⟩
  obtain ⟨D, hdFan, hdSize, hdEval⟩ := gate_elim_false_at n g p s hd hn hg
  exact ⟨D, hdFan, hdSize, fun x => (hdEval (E' x)).trans (hc' x)⟩

end PEqualNP.Outside.L_meta_650_aux.FourOwnerFreeRestriction

namespace PEqualNP.Outside.L_meta_650_aux.FourOwnerFreeRestriction.Arc

open PEqualNP.MetaComplexity
open PEqualNP.CircuitLowerBounds

def restrict (t : ℕ) (x : Fin 14 → Bool) : Fin 14 → Bool :=
  fun i => if i.val < 14 - t then x i else false

def base (x : Fin 14 → Bool) : Bool :=
  (x 0 && (x 4 || x 5 || x 6 || x 11)) ||
  (x 1 && (x 4 || x 8 || x 9 || x 10)) ||
  (x 2 && (x 5 || x 7 || x 9 || x 13)) ||
  (x 3 && (x 6 || x 7 || x 8 || x 12))

def f (t : ℕ) (x : Fin 14 → Bool) : Bool := base (restrict t x)

def input (x : Fin 14 → Bool) : Fin 42 → Bool :=
  ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9, x 10, x 11, x 12, x 13, false, x 4 || x 7, x 4 || x 12, x 4 || x 12 || x 13, x 4 || x 13, x 5 || x 10, x 5 || x 10 || x 12, x 5 || x 8, x 5 || x 12, x 10 || x 6, x 10 || x 6 || x 13, x 10 || x 7, x 10 || x 7 || x 11, x 10 || x 11, x 10 || x 12, x 10 || x 13, x 6 || x 13, x 6 || x 9, x 7 || x 11, x 8 || x 11, x 8 || x 11 || x 13, x 8 || x 13, x 11 || x 12, x 11 || x 12 || x 9, x 11 || x 13, x 11 || x 9, x 12 || x 13, x 12 || x 9]

def encode (t : ℕ) (x : Fin 14 → Bool) : Fin 42 → Bool := input (restrict t x)

def normalizer : Fin 4 → Fin 42 → Fin 42 :=
  ![![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 4, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 10, 6, 31, 32, 33, 34, 8, 36, 37, 11, 39, 12, 41], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 4, 4, 4, 19, 20, 21, 5, 23, 24, 25, 26, 27, 10, 10, 6, 31, 32, 33, 34, 8, 11, 37, 11, 39, 14, 9], ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 4, 4, 4, 19, 20, 21, 5, 23, 24, 25, 26, 10, 10, 10, 6, 31, 7, 8, 8, 8, 14, 9, 14, 9, 14, 9]]

def point : Fin 4 → Fin 42 := ![13, 12, 11, 10]

def w0 : Fin 4 → Fin 14 → Bool :=
  ![![false, false, true, false, true, false, true, false, true, false, true, true, true, false], ![false, false, false, true, true, true, false, false, false, true, true, true, false, false], ![true, false, false, false, false, false, false, true, true, true, true, false, false, false], ![false, true, false, false, false, true, true, true, false, false, false, false, false, false]]

def w1 (t : Fin 4) : Fin 14 → Bool :=
  Function.update (w0 t) ⟨13 - t.val, by omega⟩ true

theorem normalize_correct (t : Fin 4) (x : Fin 14 → Bool) :
    encode t.val x ∘ normalizer t = encode t.val x := by
  fin_cases t <;> funext k <;> fin_cases k <;>
    simp [encode, input, restrict, normalizer]

theorem restrict_twice (t : Fin 4) (x : Fin 14 → Bool) :
    restrict t.val (restrict (t.val + 1) x) = restrict (t.val + 1) x := by
  fin_cases t <;> funext k <;> fin_cases k <;> simp [restrict]

theorem next_encode (t : Fin 4) (x : Fin 14 → Bool) :
    encode (t.val + 1) x = encode t.val (restrict (t.val + 1) x) := by
  simp only [encode, restrict_twice]

theorem next_f (t : Fin 4) (x : Fin 14 → Bool) :
    f (t.val + 1) x = f t.val (restrict (t.val + 1) x) := by
  simp only [f, restrict_twice]

theorem next_zero (t : Fin 4) (x : Fin 14 → Bool) :
    encode (t.val + 1) x (point t) = false := by
  fin_cases t <;> simp [encode, input, restrict, point]

theorem witnesses : ∀ t : Fin 4,
    Function.update (encode t.val (w0 t)) (point t)
      (!(encode t.val (w0 t) (point t))) ∘ normalizer t = encode t.val (w1 t) := by
  decide +kernel

theorem witness_changes : ∀ t : Fin 4, f t.val (w1 t) ≠ f t.val (w0 t) := by
  decide +kernel

theorem next_nonconstant (t : Fin 4) :
    ∃ x y : Fin 14 → Bool, f (t.val + 1) x ≠ f (t.val + 1) y := by
  refine ⟨fun i => decide (i.val = 0 ∨ i.val = 4), fun _ => false, ?_⟩
  fin_cases t <;> decide

theorem step (t : Fin 4) (s : ℕ)
    (h : HasEncoded (encode t.val) (f t.val) (s + 1)) :
    HasEncoded (encode (t.val + 1)) (f (t.val + 1)) s :=
  encoded_elim _ _ _ _ (normalizer t) (point t) (restrict (t.val + 1))
    (normalize_correct t) (next_encode t) (next_f t) (next_zero t)
    (w0 t) (w1 t) (witnesses t) (witness_changes t) (next_nonconstant t) s h

def collapse : Fin 42 → Fin 14 :=
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 13, 13, 13, 13, 13, 11, 4, 4, 4, 5, 5, 10, 5, 6, 6, 7, 7, 13, 13, 13, 6, 12, 7, 8, 8, 8, 13, 9, 13, 9, 13, 9]

def kernel (x : Fin 10 → Bool) : Bool :=
  (x 0 && (x 4 || x 5 || x 6)) ||
  (x 1 && (x 4 || x 8 || x 9)) ||
  (x 2 && (x 5 || x 7 || x 9)) ||
  (x 3 && (x 6 || x 7 || x 8))

def kernelEncode (x : Fin 10 → Bool) : Fin 13 → Bool :=
  ![x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9,
    x 5 || x 8, x 4 || x 7, x 6 || x 9]

theorem collapse_correct (x : Fin 10 → Bool) :
    Fin.snoc (kernelEncode x) false ∘ collapse =
      encode 4 (Fin.append x (fun _ : Fin 4 => false)) := by
  funext k
  fin_cases k <;> simp [collapse, encode, input, restrict, kernelEncode, Fin.append,
    Fin.addCases]

theorem final_f (x : Fin 10 → Bool) :
    f 4 (Fin.append x (fun _ : Fin 4 => false)) = kernel x := by
  simp [f, base, restrict, kernel, Fin.append, Fin.addCases]

theorem necessary_fourteen
    (h : HasEncoded (encode 0) (f 0) 18) : HasEncoded kernelEncode kernel 14 := by
  have h1 : HasEncoded (encode 1) (f 1) 17 := step 0 17 h
  have h2 : HasEncoded (encode 2) (f 2) 16 := step 1 16 h1
  have h3 : HasEncoded (encode 3) (f 3) 15 := step 2 15 h2
  have h4 : HasEncoded (encode 4) (f 4) 14 := step 3 14 h3
  obtain ⟨C, hfan, hsize, hev⟩ := h4
  have hr := Helpers.PermInputs.relabel_size collapse
    (fun y : Fin 42 → Bool => C.eval (List.ofFn y)) 14 ⟨C, hfan, hsize, fun _ => rfl⟩
  have hh := Helpers.fix_last 13 _ false 14 hr
  change HasCircuitSize 13
    (fun x : Fin 13 → Bool => C.eval (List.ofFn (Fin.snoc x false ∘ collapse))) 14 at hh
  obtain ⟨D, hdfan, hdsize, hdeval⟩ := hh
  refine ⟨D, hdfan, hdsize, ?_⟩
  intro x
  rw [hdeval]
  change C.eval (List.ofFn (Fin.snoc (kernelEncode x) false ∘ collapse)) = kernel x
  rw [collapse_correct, hev, final_f]

end PEqualNP.Outside.L_meta_650_aux.FourOwnerFreeRestriction.Arc
