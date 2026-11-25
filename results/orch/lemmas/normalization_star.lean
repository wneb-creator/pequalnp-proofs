import PEqualNP.Defs
import Mathlib.Tactic

namespace PEqualNP.Outside.L_meta_3451_aux.Star

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma run_append (gs hs : List Gate) (w : List Bool) :
    run (gs ++ hs) w = run hs (run gs w) := by
  simp [run, List.foldl_append]

lemma run_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, run gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [run], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    change run gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) = _
    rw [ht]
    simp

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := run_prefix gs w
  rw [ht]
  simp [hl]

lemma run_input (gs : List Gate) (w : List Bool) (i : ℕ) (hi : i < w.length) :
    (run gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := run_prefix gs w
  rw [ht, List.getD_append _ _ _ _ hi]

def chain (n out : ℕ) : List ℕ → List Gate
  | [] => []
  | i :: xs => ⟨.or, [out, i]⟩ :: chain (n + 1) n xs

def chainOut (n out : ℕ) : List ℕ → ℕ
  | [] => out
  | _ :: xs => chainOut (n + 1) n xs

lemma chain_length (xs : List ℕ) (n out : ℕ) : (chain n out xs).length = xs.length := by
  induction xs generalizing n out with
  | nil => rfl
  | cons i xs ih => simp [chain, ih]

lemma chain_pure (xs : List ℕ) (n out : ℕ) :
    ∀ g ∈ chain n out xs, g.op = GateOp.or ∧ g.inputs.length = 2 := by
  induction xs generalizing n out with
  | nil => simp [chain]
  | cons i xs ih =>
    intro g hg
    rcases List.mem_cons.mp hg with rfl | hg
    · simp
    · exact ih (n + 1) n g hg

lemma chain_out_lt (xs : List ℕ) (n out : ℕ) (ho : out < n) :
    chainOut n out xs < n + xs.length := by
  induction xs generalizing n out with
  | nil => simpa [chainOut] using ho
  | cons i xs ih =>
    have h := ih (n + 1) n (by omega)
    simp only [chainOut, List.length_cons]
    omega

lemma chain_back (xs : List ℕ) (n out : ℕ) (ho : out < n) (hx : ∀ i ∈ xs, i < n) :
    ∀ j < (chain n out xs).length,
      ∀ i ∈ ((chain n out xs).getD j ⟨.or, []⟩).inputs, i < n + j := by
  induction xs generalizing n out with
  | nil => simp [chain]
  | cons x xs ih =>
    intro j hj i hi
    cases j with
    | zero =>
      simp only [chain, List.getD_cons_zero, List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with hi | hi
      · omega
      · have h := hx x List.mem_cons_self
        omega
    | succ j =>
      have h := ih (n + 1) n (by omega)
        (fun i hi => Nat.lt_succ_of_lt (hx i (List.mem_cons_of_mem x hi))) j
        (by simpa [chain] using hj) i (by simpa [chain] using hi)
      omega

lemma chain_op (xs : List ℕ) (n out j : ℕ) (hj : j < (chain n out xs).length) :
    ((chain n out xs).getD j ⟨.or, []⟩).op = GateOp.or := by
  rw [List.getD_eq_getElem _ _ hj]
  exact (chain_pure xs n out _ (List.getElem_mem hj)).1

lemma chain_eval (xs : List ℕ) : ∀ (n out : ℕ) (w : List Bool), w.length = n →
    out < n → (∀ i ∈ xs, i < n) →
    (run (chain n out xs) w).getD (chainOut n out xs) false =
      (w.getD out false || xs.any (fun i => w.getD i false)) := by
  induction xs with
  | nil => intro n out w hw ho hx; simp [chain, chainOut, run]
  | cons i xs ih =>
    intro n out w hw ho hx
    let v := w ++ [w.getD out false || w.getD i false]
    have hv : v.length = n + 1 := by simp [v, hw]
    have hn : v.getD n false = (w.getD out false || w.getD i false) := by
      rw [show n = w.length from hw.symm]
      simp [v]
    have hxs : xs.any (fun i => v.getD i false) = xs.any (fun i => w.getD i false) := by
      have hm : xs.map (fun i => v.getD i false) = xs.map (fun i => w.getD i false) := by
        apply List.map_congr_left
        intro k hk
        exact List.getD_append _ _ _ _ (by rw [hw]; exact hx k (List.mem_cons_of_mem i hk))
      have hh := congrArg (fun l : List Bool => l.any id) hm
      simpa only [List.any_map, Function.comp_def, id] using hh
    have hrec := ih (n + 1) n v hv (by omega)
      (fun k hk => Nat.lt_succ_of_lt (hx k (List.mem_cons_of_mem i hk)))
    change (run (chain (n + 1) n xs)
      (w ++ [GateOp.or.eval ([out, i].map fun k => w.getD k false)] )).getD
        (chainOut (n + 1) n xs) false = _
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
      List.any_nil, Bool.or_false, id]
    rw [hrec, hn, hxs]
    exact Bool.or_assoc _ _ _

lemma construct (n : ℕ) (p : Fin n) (xs : List (Fin n)) :
    ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack n D ∧ D.size ≤ xs.length ∧
      (∀ z : Fin n → Bool, circuitFun n D z = (z p && xs.any z)) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        ∀ z : Fin n → Bool, PEqualNP.EdgeOwnership.gateVal n D j z = true →
          circuitFun n D z = true) := by
  cases xs with
  | nil =>
    refine ⟨⟨[], n⟩, ?_, ?_, ?_, ?_, ?_⟩
    · simp [Monotone2]
    · simp [NestedCover.ReadsBack]
    · simp [Circuit.size]
    · intro z
      simp [circuitFun, Circuit.eval, Circuit.wires]
    · simp
  | cons x xs =>
    let ys := xs.map Fin.val
    let gs := chain n x.val ys
    let out := chainOut n x.val ys
    let D : Circuit := ⟨gs ++ [⟨.and, [p.val, out]⟩], n + gs.length⟩
    have hys : ∀ i ∈ ys, i < n := by
      intro i hi
      obtain ⟨q, _, rfl⟩ := List.mem_map.mp hi
      exact q.isLt
    have hout : out < n + gs.length := by
      simpa only [out, gs, chain_length] using chain_out_lt ys n x.val x.isLt
    refine ⟨D, ?_, ?_, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with hg | hg
      · obtain ⟨hop, hlen⟩ := chain_pure ys n x.val g hg
        simp [hop, hlen]
      · simp only [List.mem_singleton] at hg
        subst g
        simp
    · intro j hj i hi
      change i ∈ ((gs ++ [(⟨.and, [p.val, out]⟩ : Gate)]).getD j (⟨.or, []⟩ : Gate)).inputs at hi
      by_cases hj' : j < gs.length
      · rw [List.getD_append _ _ _ _ hj'] at hi
        exact chain_back ys n x.val x.isLt hys j hj' i hi
      · have he : j = gs.length := by
          simp only [D, List.length_append, List.length_singleton] at hj
          omega
        subst j
        rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        simp only [Nat.sub_self, List.getD_cons_zero, List.mem_cons,
          List.not_mem_nil, or_false] at hi
        rcases hi with rfl | rfl
        · omega
        · exact hout
    · simp [D, Circuit.size, gs, chain_length, ys]
    · intro z
      let v := run gs (List.ofFn z)
      have hv : v.length = n + gs.length := by simp [v, run_length]
      have hp : v.getD p.val false = z p := by
        rw [run_input _ _ _ (by simp)]
        simp
      have hor : v.getD out false = (z x || xs.any z) := by
        have h := chain_eval ys n x.val (List.ofFn z) (by simp) x.isLt hys
        have hxs : ys.any (fun i => (List.ofFn z).getD i false) = xs.any z := by
          dsimp [ys]
          rw [List.any_map]
          apply List.any_congr rfl
          intro q
          simp
        simpa only [hxs, show (List.ofFn z).getD x.val false = z x by simp] using h
      change (run (gs ++ [⟨.and, [p.val, out]⟩]) (List.ofFn z)).getD
        (n + gs.length) false = _
      rw [run_append]
      change (v ++ [GateOp.and.eval ([p.val, out].map fun i => v.getD i false)]).getD
        (n + gs.length) false = _
      rw [← hv, List.getD_append_right _ _ _ _ (by omega)]
      simp only [Nat.sub_self, List.getD_cons_zero, GateOp.eval, List.map_cons,
        List.map_nil, List.all_cons, List.all_nil, id, Bool.and_true, hp, hor, List.any_cons]
    · intro j hj hand z hz
      by_cases hj' : j < gs.length
      · have hor : (NestedCover.gateAt D j).op = GateOp.or := by
          unfold NestedCover.gateAt
          change ((gs ++ [(⟨.and, [p.val, out]⟩ : Gate)]).getD j (⟨.or, []⟩ : Gate)).op = GateOp.or
          rw [List.getD_append _ _ _ _ hj']
          exact chain_op ys n x.val j hj'
        rw [hor] at hand
        cases hand
      · have he : j = gs.length := by
          simp only [D, List.length_append, List.length_singleton] at hj
          omega
        subst j
        exact hz

end PEqualNP.Outside.L_meta_3451_aux.Star
