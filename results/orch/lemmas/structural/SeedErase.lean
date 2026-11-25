import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1890_aux.SeedErase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
   (3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

def target (x : Fin 10 → Bool) : Bool :=
  edges.any fun e => x e.1 && x e.2

def onPair (e : Fin 10 × Fin 10) (i : Fin 10) : Bool :=
  decide (i = e.1 ∨ i = e.2)

lemma pair_target (e : Fin 10 × Fin 10) (he : e ∈ edges) :
    target (onPair e) = true := by
  apply List.any_eq_true.mpr
  exact ⟨e, he, by simp [onPair]⟩

lemma pair_seed : ∀ e ∈ edges, (onPair e 0 && onPair e 2) = false := by
  decide

lemma find_pair (x : Fin 10 → Bool) (h : target x = true) :
    ∃ e ∈ edges, ∀ i, onPair e i = true → x i = true := by
  obtain ⟨e, he, hv⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true] at hv
  refine ⟨e, he, ?_⟩
  intro i hi
  simp only [onPair, decide_eq_true_eq] at hi
  rcases hi with rfl | rfl
  · exact hv.1
  · exact hv.2

lemma erase_seed (H : (Fin 10 → Bool) → Bool → Bool)
    (mono : ∀ x y b c, (∀ i, x i = true → y i = true) →
      (b = true → c = true) → H x b = true → H y c = true)
    (correct : ∀ x, H x (x 0 && x 2) = target x) :
    ∀ x, H x false = target x := by
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    rw [← correct x]
    exact mono x x false (x 0 && x 2) (fun _ => id) (by simp) hx
  · intro hx
    obtain ⟨e, he, sub⟩ := find_pair x hx
    have hp : H (onPair e) false = true := by
      rw [← pair_seed e he, correct, pair_target e he]
    exact mono (onPair e) x false false sub (by simp) hp

lemma gate_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List Nat) (f g : Nat → Bool)
    (h : ∀ i ∈ l, f i = true → g i = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · intro ht
    change (l.map f).all id = true at ht
    change (l.map g).all id = true
    rw [List.all_eq_true] at ht ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact h i hi (ht _ (List.mem_map_of_mem hi))
  · intro ht
    change (l.map f).any id = true at ht
    change (l.map g).any id = true
    rw [List.any_eq_true] at ht ⊢
    obtain ⟨b, hb, ht⟩ := ht
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨g i, List.mem_map_of_mem hi, h i hi ht⟩

lemma eval_mono (C : Circuit) (hc : Monotone2 C) (x y : List Bool)
    (len : x.length = y.length)
    (sub : ∀ i, x.getD i false = true → y.getD i false = true) :
    C.eval x = true → C.eval y = true := by
  have run (gs : List Gate) (legal : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
      (x y : List Bool) (len : x.length = y.length)
      (sub : ∀ i, x.getD i false = true → y.getD i false = true) :
      ∀ i, ((⟨gs,0⟩ : Circuit).wires x).getD i false = true →
        ((⟨gs,0⟩ : Circuit).wires y).getD i false = true := by
    induction gs generalizing x y with
    | nil => exact sub
    | cons g gs ih =>
      let a := g.op.eval (g.inputs.map fun i => x.getD i false)
      let b := g.op.eval (g.inputs.map fun i => y.getD i false)
      have ab : a = true → b = true :=
        gate_mono g.op (legal g List.mem_cons_self) g.inputs _ _ (fun i _ => sub i)
      change ∀ i, ((⟨gs,0⟩ : Circuit).wires (x ++ [a])).getD i false = true →
        ((⟨gs,0⟩ : Circuit).wires (y ++ [b])).getD i false = true
      apply ih (fun g hg => legal g (List.mem_cons_of_mem _ hg)) _ _ (by simp [len])
      intro i
      by_cases hi : i < x.length
      · rw [List.getD_append _ _ _ _ hi,
          List.getD_append _ _ _ _ (by omega)]
        exact sub i
      · rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), len]
        cases k : i - y.length with
        | zero => simpa using ab
        | succ j => simp
  exact run C.gates (fun g hg => by simpa using (hc g hg).1) x y len sub C.output

lemma circuit_erase_seed (C : Circuit) (hc : Monotone2 C) (p : Fin 10 → Fin 10)
    (correct : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ p) ++ [x 0 && x 2]) = target x) :
    ∀ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ p) ++ [false]) = target x := by
  apply erase_seed (fun x b => C.eval (List.ofFn (x ∘ p) ++ [b])) _ correct
  intro x y b c sub bc
  apply eval_mono C hc _ _ (by simp)
  intro i
  by_cases hi : i < 10
  · rw [List.getD_append _ _ _ _ (by simpa using hi),
      List.getD_append _ _ _ _ (by simpa using hi)]
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi,
      ↓reduceDIte, Option.getD_some, Function.comp_apply] using sub (p ⟨i,hi⟩)
  · rw [List.getD_append_right _ _ _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_ofFn]
    cases k : i - 10 with
    | zero => simpa using bc
    | succ j => simp

end PEqualNP.Outside.L_meta_1890_aux.SeedErase
