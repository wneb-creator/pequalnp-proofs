import PEqualNP.Defs
import Mathlib.Tactic.Ring

namespace PEqualNP.Outside.L_meta_18183

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def stepWire (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem foldl_stepWire_len (gs : List Gate) :
    ∀ xs : List Bool, (gs.foldl stepWire xs).length = xs.length + gs.length := by
  induction gs with
  | nil => intro xs; simp
  | cons g gs ih =>
      intro xs
      simp only [List.foldl_cons, List.length_cons, ih, stepWire, List.length_append, List.length_nil]
      omega

theorem foldl_stepWire_getD_lt (gs : List Gate) :
    ∀ (xs : List Bool) (i : ℕ), i < xs.length →
      (gs.foldl stepWire xs).getD i false = xs.getD i false := by
  induction gs with
  | nil => intro xs i _; rfl
  | cons g gs ih =>
      intro xs i hi
      simp only [List.foldl_cons]
      rw [ih (stepWire xs g) i (by simp [stepWire]; omega)]
      exact List.getD_append _ _ _ _ hi

theorem getD_append_add (p w : List Bool) (i : ℕ) :
    (p ++ w).getD (i + p.length) false = w.getD i false := by
  by_cases hi : i < w.length
  · rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by omega)]
    rw [List.getD_eq_getElem _ _ hi]
    simp
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_self (l : List Bool) (x : Bool) (n : ℕ) (h : l.length = n) :
    (l ++ [x]).getD n false = x := by
  subst h; simp

-- Helper: chain of OR gates over a list of wire indices of length >= 1.
-- Given base index `base` (current wire count) and a non-empty list of wire indices `ws`,
-- `orChainGates base ws` appends `ws.length - 1` OR gates computing the OR of `ws`,
-- whose output wire is `orChainOut base ws`.
def orChainAux : ℕ → ℕ → List ℕ → List Gate
  | _, _, [] => []
  | base, acc, x :: xs => ⟨.or, [acc, x]⟩ :: orChainAux (base + 1) base xs

def orChainGates (base : ℕ) : List ℕ → List Gate
  | [] => []
  | x :: xs => orChainAux base x xs

def orChainOut (base : ℕ) : List ℕ → ℕ
  | [] => 0
  | [x] => x
  | _ :: xs => base + xs.length - 1

theorem orChainAux_len (base acc : ℕ) (xs : List ℕ) :
    (orChainAux base acc xs).length = xs.length := by
  induction xs generalizing base acc with
  | nil => rfl
  | cons x xs ih => simp [orChainAux, ih]

theorem orChainGates_len (base : ℕ) (ws : List ℕ) :
    (orChainGates base ws).length = ws.length - 1 := by
  cases ws with
  | nil => rfl
  | cons x xs => simp [orChainGates, orChainAux_len]

theorem orChainAux_mono (base acc : ℕ) (xs : List ℕ) :
    ∀ g ∈ orChainAux base acc xs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction xs generalizing base acc with
  | nil => intro g hg; cases hg
  | cons x xs ih =>
      intro g hg
      simp only [orChainAux, List.mem_cons] at hg
      rcases hg with rfl | hg
      · exact ⟨by simp, by simp⟩
      · exact ih _ _ g hg

theorem orChainGates_mono (base : ℕ) (ws : List ℕ) :
    ∀ g ∈ orChainGates base ws, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  cases ws with
  | nil => intro g hg; cases hg
  | cons x xs => exact orChainAux_mono base x xs

theorem foldl_orChainAux (base acc : ℕ) (xs : List ℕ) :
    ∀ (w : List Bool), w.length = base →
      (∀ x ∈ xs, x < base) →
      acc < base →
      ((orChainAux base acc xs).foldl stepWire w).getD (if xs.isEmpty then acc else base + xs.length - 1) false =
        xs.foldl (fun b x => b || w.getD x false) (w.getD acc false) := by
  induction xs generalizing base acc with
  | nil =>
      intro w _ _ _
      simp [orChainAux]
  | cons x xs ih =>
      intro w hlen hxs hacc
      simp only [orChainAux, List.foldl_cons, List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte,
        List.length_cons]
      have hx : x < base := hxs x List.mem_cons_self
      let w' := stepWire w ⟨.or, [acc, x]⟩
      have hw'_len : w'.length = base + 1 := by simp [w', stepWire, hlen]
      have hw'_acc : w'.getD base false = (w.getD acc false || w.getD x false) := by
        simp only [w', stepWire, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, getD_snoc_self w _ base hlen]
      have hxs' : ∀ y ∈ xs, y < base + 1 := fun y hy => by
        have := hxs y (List.mem_cons_of_mem _ hy); omega
      have hsub := ih (base + 1) base w' hw'_len hxs' (by omega)
      have hfold_eq : xs.foldl (fun b y => b || w'.getD y false) (w'.getD base false) =
          xs.foldl (fun b y => b || w.getD y false) (w.getD acc false || w.getD x false) := by
        rw [hw'_acc]
        have hcong : ∀ (l : List ℕ) (b0 : Bool), (∀ y ∈ l, y < base) →
            l.foldl (fun b y => b || w'.getD y false) b0 =
            l.foldl (fun b y => b || w.getD y false) b0 := by
          intro l
          induction l with
          | nil => intro b0 _; rfl
          | cons y ys ihl =>
              intro b0 hyl
              simp only [List.foldl_cons]
              have hy : y < base := hyl y List.mem_cons_self
              have hget : w'.getD y false = w.getD y false := by
                simpa [w', stepWire] using List.getD_append w _ false y (by omega)
              rw [hget]
              exact ihl _ (fun z hz => hyl z (List.mem_cons_of_mem _ hz))
        exact hcong xs _ (fun y hy => hxs y (List.mem_cons_of_mem _ hy))
      cases xs with
      | nil =>
          simp only [List.isEmpty_nil, ↓reduceIte, List.length_nil] at hsub ⊢
          have hidx : base + 1 - 1 = base := by omega
          rw [hidx, hsub, hfold_eq]
      | cons y ys =>
          simp only [List.isEmpty_cons, Bool.false_eq_true, ↓reduceIte, List.length_cons] at hsub ⊢
          have hidx : base + (ys.length + 1 + 1) - 1 = base + 1 + (ys.length + 1) - 1 := by omega
          rw [hidx, hsub, hfold_eq]

theorem foldl_orChainGates (base : ℕ) (ws : List ℕ) (w : List Bool)
    (hlen : w.length = base) (hne : ws ≠ []) (hlt : ∀ x ∈ ws, x < base) :
    ((orChainGates base ws).foldl stepWire w).getD (orChainOut base ws) false =
      ws.any (fun x => w.getD x false) := by
  cases ws with
  | nil => exact absurd rfl hne
  | cons x xs =>
      have h1 := foldl_orChainAux base x xs w hlen
        (fun y hy => hlt y (List.mem_cons_of_mem _ hy)) (hlt x List.mem_cons_self)
      have hout : orChainOut base (x :: xs) = if xs.isEmpty then x else base + xs.length - 1 := by
        cases xs <;> simp [orChainOut]
      rw [orChainGates, hout, h1]
      have hany : ∀ (l : List ℕ) (b : Bool),
          l.foldl (fun acc y => acc || w.getD y false) b = (b || l.any (fun y => w.getD y false)) := by
        intro l
        induction l with
        | nil => intro b; simp
        | cons y ys ihl =>
            intro b
            simp only [List.foldl_cons, List.any_cons, ihl, Bool.or_assoc]
      rw [hany, List.any_cons]

-- Threshold-2 circuit on a list of wires `xs` of length >= 2, starting at wire index `base`.
-- Cost: 3 * xs.length - 5 gates!
-- For [a, b]: 1 gate: AND(a, b), out = base.
-- For a :: b :: c :: rest:
--   gate base: OR(a, b) = t1
--   gate base+1: AND(a, b) = t2
--   then `t2Loop (base + 2) t1 t2 (c :: rest)`:
--     on [z]: AND(t1, z) at p, OR(t2, p) at p+1 -> out = p+1 (2 gates)
--     on z :: zs (zs non-empty):
--       p: OR(t1, z)
--       p+1: AND(t1, z)
--       p+2: OR(t2, p+1)
--       recurse with base=p+3, t1=p, t2=p+2, zs! (3 gates)
def t2Loop : ℕ → ℕ → ℕ → List ℕ → List Gate
  | _, _, _, [] => []
  | p, t1, t2, [z] => [⟨.and, [t1, z]⟩, ⟨.or, [t2, p]⟩]
  | p, t1, t2, z :: y :: ys =>
      ⟨.or, [t1, z]⟩ :: ⟨.and, [t1, z]⟩ :: ⟨.or, [t2, p + 1]⟩ ::
        t2Loop (p + 3) p (p + 2) (y :: ys)

def t2Gates (base : ℕ) : List ℕ → List Gate
  | [] => []
  | [_] => []
  | [a, b] => [⟨.and, [a, b]⟩]
  | a :: b :: c :: rest => ⟨.or, [a, b]⟩ :: ⟨.and, [a, b]⟩ :: t2Loop (base + 2) base (base + 1) (c :: rest)

def t2Out (base : ℕ) (xs : List ℕ) : ℕ :=
  base + (3 * xs.length - 5) - 1

theorem t2Loop_len (p t1 t2 : ℕ) : ∀ zs : List ℕ, zs ≠ [] →
    (t2Loop p t1 t2 zs).length = 3 * zs.length - 1
  | [], h => absurd rfl h
  | [_], _ => by simp [t2Loop]
  | _ :: y :: ys, _ => by
      have ih := t2Loop_len (p + 3) p (p + 2) (y :: ys) (by simp)
      simp only [t2Loop, List.length_cons, ih]
      omega

theorem t2Gates_len (base : ℕ) (xs : List ℕ) (h : 2 ≤ xs.length) :
    (t2Gates base xs).length = 3 * xs.length - 5 := by
  match xs with
  | [] => simp at h
  | [_] => simp at h
  | [_, _] => simp [t2Gates]
  | _ :: _ :: c :: rest =>
      have hl := t2Loop_len (base + 2) base (base + 1) (c :: rest) (by simp)
      simp only [t2Gates, List.length_cons, hl]
      omega

theorem t2Loop_mono (p t1 t2 : ℕ) : ∀ zs : List ℕ,
    ∀ g ∈ t2Loop p t1 t2 zs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2
  | [], g, hg => by cases hg
  | [_], g, hg => by
      simp only [t2Loop, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with rfl | rfl <;> exact ⟨by simp, by simp⟩
  | _ :: y :: ys, g, hg => by
      simp only [t2Loop, List.mem_cons] at hg
      rcases hg with rfl | rfl | rfl | hg
      · exact ⟨by simp, by simp⟩
      · exact ⟨by simp, by simp⟩
      · exact ⟨by simp, by simp⟩
      · exact t2Loop_mono (p + 3) p (p + 2) (y :: ys) g hg

theorem t2Gates_mono (base : ℕ) (xs : List ℕ) :
    ∀ g ∈ t2Gates base xs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  match xs with
  | [] => intro g hg; cases hg
  | [_] => intro g hg; cases hg
  | [_, _] =>
      intro g hg
      simp only [t2Gates, List.mem_cons, List.not_mem_nil, or_false] at hg
      subst hg; exact ⟨by simp, by simp⟩
  | _ :: _ :: c :: rest =>
      intro g hg
      simp only [t2Gates, List.mem_cons] at hg
      rcases hg with rfl | rfl | hg
      · exact ⟨by simp, by simp⟩
      · exact ⟨by simp, by simp⟩
      · exact t2Loop_mono (base + 2) base (base + 1) (c :: rest) g hg

theorem t1_step_bool (cnt : ℕ) (b : Bool) :
    (decide (1 ≤ cnt) || b) = decide (1 ≤ cnt + if b then 1 else 0) := by
  rcases cnt with _ | n <;> cases b <;> simp

theorem t2_step_bool (cnt : ℕ) (b : Bool) :
    (decide (2 ≤ cnt) || (decide (1 ≤ cnt) && b)) = decide (2 ≤ cnt + if b then 1 else 0) := by
  rcases cnt with _ | _ | n <;> cases b <;> simp

-- Semantic spec of t2Loop: given initial counts `c1 = (1 <= cnt)` at `t1` and `c2 = (2 <= cnt)` at `t2`,
-- computes `2 <= cnt + count true on zs` at wire `p + (3 * zs.length - 1) - 1`!
def countTrue (w : List Bool) (xs : List ℕ) : ℕ :=
  (xs.map fun i => w.getD i false).count true

theorem countTrue_cons (w : List Bool) (a : ℕ) (xs : List ℕ) :
    countTrue w (a :: xs) = (if w.getD a false then 1 else 0) + countTrue w xs := by
  unfold countTrue
  rw [List.map_cons, List.count_cons]
  cases w.getD a false <;> simp [Nat.add_comm]

theorem countTrue_nil (w : List Bool) : countTrue w [] = 0 := rfl

theorem t2Loop_eval (p t1 t2 : ℕ) :
    ∀ (zs : List ℕ) (hne : zs ≠ []) (w : List Bool) (cnt : ℕ),
      w.length = p →
      t1 < p → t2 < p →
      (∀ z ∈ zs, z < p) →
      w.getD t1 false = decide (1 ≤ cnt) →
      w.getD t2 false = decide (2 ≤ cnt) →
      ((t2Loop p t1 t2 zs).foldl stepWire w).getD (p + (3 * zs.length - 1) - 1) false =
        decide (2 ≤ cnt + countTrue w zs)
  | [], hne, _, _, _, _, _, _, _, _ => absurd rfl hne
  | [z], _, w, cnt, hlen, ht1, ht2, hzs, h1, h2 => by
      have hz : z < p := hzs z List.mem_cons_self
      let w1 := stepWire w ⟨.and, [t1, z]⟩
      let w2 := stepWire w1 ⟨.or, [t2, p]⟩
      have hw1_len : w1.length = p + 1 := by simp [w1, stepWire, hlen]
      have hw1_p : w1.getD p false = (decide (1 ≤ cnt) && w.getD z false) := by
        simp only [w1, stepWire, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, getD_snoc_self w _ p hlen, h1]
      have hw1_t2 : w1.getD t2 false = decide (2 ≤ cnt) := by
        rw [show w1.getD t2 false = w.getD t2 false from List.getD_append w _ false t2 (by omega), h2]
      have hidx : p + (3 * [z].length - 1) - 1 = p + 1 := by simp
      simp only [t2Loop, List.foldl_cons, List.foldl_nil, hidx]
      change w2.getD (p + 1) false = decide (2 ≤ cnt + countTrue w [z])
      have hw2_out : w2.getD (p + 1) false = (decide (2 ≤ cnt) || (decide (1 ≤ cnt) && w.getD z false)) := by
        simp only [w2, stepWire, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, getD_snoc_self w1 _ (p + 1) hw1_len, hw1_t2, hw1_p]
      rw [hw2_out, t2_step_bool]
      have hct : countTrue w [z] = if w.getD z false then 1 else 0 := by
        rw [countTrue_cons, countTrue_nil]; omega
      rw [hct]
  | z :: y :: ys, _, w, cnt, hlen, ht1, ht2, hzs, h1, h2 => by
      have hz : z < p := hzs z List.mem_cons_self
      let w1 := stepWire w ⟨.or, [t1, z]⟩
      let w2 := stepWire w1 ⟨.and, [t1, z]⟩
      let w3 := stepWire w2 ⟨.or, [t2, p + 1]⟩
      have hw1_len : w1.length = p + 1 := by simp [w1, stepWire, hlen]
      have hw2_len : w2.length = p + 2 := by simp [w2, stepWire, hw1_len]
      have hw3_len : w3.length = p + 3 := by simp [w3, stepWire, hw2_len]
      have hw1_lt : ∀ i < p, w1.getD i false = w.getD i false := fun i hi =>
        List.getD_append w _ false i (by omega)
      have hw2_lt : ∀ i < p + 1, w2.getD i false = w1.getD i false := fun i hi =>
        List.getD_append w1 _ false i (by omega)
      have hw3_lt : ∀ i < p + 2, w3.getD i false = w2.getD i false := fun i hi =>
        List.getD_append w2 _ false i (by omega)
      have hw3_old : ∀ i < p, w3.getD i false = w.getD i false := fun i hi => by
        rw [hw3_lt i (by omega), hw2_lt i (by omega), hw1_lt i hi]
      have hw1_p : w1.getD p false = (decide (1 ≤ cnt) || w.getD z false) := by
        simp only [w1, stepWire, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, getD_snoc_self w _ p hlen, h1]
      have hw2_p1 : w2.getD (p + 1) false = (decide (1 ≤ cnt) && w.getD z false) := by
        simp only [w2, stepWire, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, getD_snoc_self w1 _ (p + 1) hw1_len, hw1_lt t1 ht1, hw1_lt z hz, h1]
      have hw3_p : w3.getD p false = decide (1 ≤ cnt + (if w.getD z false then 1 else 0)) := by
        rw [hw3_lt p (by omega), hw2_lt p (by omega), hw1_p, t1_step_bool]
      have hw3_p2 : w3.getD (p + 2) false = decide (2 ≤ cnt + (if w.getD z false then 1 else 0)) := by
        have ht2' : w2.getD t2 false = decide (2 ≤ cnt) := by
          rw [hw2_lt t2 (by omega), hw1_lt t2 ht2, h2]
        simp only [w3, stepWire, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, getD_snoc_self w2 _ (p + 2) hw2_len, ht2', hw2_p1, t2_step_bool]
      have ih := t2Loop_eval (p + 3) p (p + 2) (y :: ys) (by simp) w3
        (cnt + if w.getD z false then 1 else 0) hw3_len (by omega) (by omega)
        (fun q hq => by have := hzs q (List.mem_cons_of_mem _ hq); omega) hw3_p hw3_p2
      have hidx : p + (3 * (z :: y :: ys).length - 1) - 1 = (p + 3) + (3 * (y :: ys).length - 1) - 1 := by
        simp; omega
      have hct : countTrue w3 (y :: ys) = countTrue w (y :: ys) := by
        unfold countTrue
        congr 1
        apply List.map_congr_left
        intro q hq
        exact hw3_old q (hzs q (List.mem_cons_of_mem _ hq))
      have hct_cons : countTrue w (z :: y :: ys) = (if w.getD z false then 1 else 0) + countTrue w (y :: ys) :=
        countTrue_cons w z (y :: ys)
      simp only [t2Loop, List.foldl_cons, hidx]
      change ((t2Loop (p + 3) p (p + 2) (y :: ys)).foldl stepWire w3).getD
        ((p + 3) + (3 * (y :: ys).length - 1) - 1) false = _
      rw [ih, hct, hct_cons, Nat.add_assoc]

theorem or_eq_ge1 (ba bb : Bool) :
    (ba || bb) = decide (1 ≤ (if ba then 1 else 0) + (if bb then 1 else 0)) := by
  cases ba <;> cases bb <;> rfl

theorem and_eq_ge2 (ba bb : Bool) :
    (ba && bb) = decide (2 ≤ (if ba then 1 else 0) + (if bb then 1 else 0)) := by
  cases ba <;> cases bb <;> rfl

theorem t2Gates_eval (base : ℕ) (xs : List ℕ) (w : List Bool)
    (hlen : w.length = base) (h2 : 2 ≤ xs.length) (hlt : ∀ x ∈ xs, x < base) :
    ((t2Gates base xs).foldl stepWire w).getD (t2Out base xs) false =
      decide (2 ≤ countTrue w xs) := by
  match xs with
  | [] => simp at h2
  | [_] => simp at h2
  | [a, b] =>
      have hidx : t2Out base [a, b] = base := by simp [t2Out]
      rw [t2Gates, hidx, List.foldl_cons, List.foldl_nil]
      simp only [stepWire, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
        id_eq, Bool.and_true, getD_snoc_self w _ base hlen]
      rw [countTrue_cons, countTrue_cons, countTrue_nil, Nat.add_zero]
      exact and_eq_ge2 _ _
  | a :: b :: c :: rest =>
      have ha : a < base := hlt a List.mem_cons_self
      have hb : b < base := hlt b (List.mem_cons_of_mem _ List.mem_cons_self)
      let w1 := stepWire w ⟨.or, [a, b]⟩
      let w2 := stepWire w1 ⟨.and, [a, b]⟩
      have hw1_len : w1.length = base + 1 := by simp [w1, stepWire, hlen]
      have hw2_len : w2.length = base + 2 := by simp [w2, stepWire, hw1_len]
      have hw1_lt : ∀ i < base, w1.getD i false = w.getD i false := fun i hi =>
        List.getD_append w _ false i (by omega)
      have hw2_lt : ∀ i < base + 1, w2.getD i false = w1.getD i false := fun i hi =>
        List.getD_append w1 _ false i (by omega)
      let cnt0 := (if w.getD a false then 1 else 0) + (if w.getD b false then 1 else 0)
      have hw2_b0 : w2.getD base false = decide (1 ≤ cnt0) := by
        rw [hw2_lt base (by omega)]
        simp only [w1, stepWire, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
          id_eq, Bool.or_false, getD_snoc_self w _ base hlen]
        exact or_eq_ge1 _ _
      have hw2_b1 : w2.getD (base + 1) false = decide (2 ≤ cnt0) := by
        simp only [w2, stepWire, GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil,
          id_eq, Bool.and_true, getD_snoc_self w1 _ (base + 1) hw1_len, hw1_lt a ha, hw1_lt b hb]
        exact and_eq_ge2 _ _
      have hloop := t2Loop_eval (base + 2) base (base + 1) (c :: rest) (by simp) w2 cnt0 hw2_len
        (by omega) (by omega)
        (fun q hq => by have := hlt q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)); omega)
        hw2_b0 hw2_b1
      have hidx : t2Out base (a :: b :: c :: rest) = (base + 2) + (3 * (c :: rest).length - 1) - 1 := by
        simp only [t2Out, List.length_cons]; omega
      have hct : countTrue w2 (c :: rest) = countTrue w (c :: rest) := by
        unfold countTrue
        congr 1
        apply List.map_congr_left
        intro q hq
        rw [hw2_lt q (by have := hlt q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)); omega),
            hw1_lt q (hlt q (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hq)))]
      have hct_all : countTrue w (a :: b :: c :: rest) = cnt0 + countTrue w (c :: rest) := by
        rw [countTrue_cons, countTrue_cons]
        dsimp only [cnt0]; omega
      simp only [t2Gates, List.foldl_cons, hidx]
      change ((t2Loop (base + 2) base (base + 1) (c :: rest)).foldl stepWire w2).getD
        ((base + 2) + (3 * (c :: rest).length - 1) - 1) false = _
      rw [hloop, hct, hct_all]

-- Now assemble the r x c product crown circuit on 2*(r*c) inputs!
-- Stage 1 (rc gates): w[k] = u[k] | v[k] at wire 2*rc + k
def uvGates (rc : ℕ) : List Gate :=
  List.ofFn (fun k : Fin rc => ⟨.or, [k.1, rc + k.1]⟩)

-- Stage 2 (r*(c-1) gates): row ORs, each row i in Fin r ORs wires [2*rc + i*c + j | j in Fin c]
def rowWires (r c i : ℕ) : List ℕ :=
  (List.range c).map (fun j => 2 * (r * c) + i * c + j)

def rowBase (r c i : ℕ) : ℕ :=
  3 * (r * c) + i * (c - 1)

def rowGates (r c : ℕ) : List Gate :=
  (List.range r).flatMap (fun i => orChainGates (rowBase r c i) (rowWires r c i))

def rowOut (r c i : ℕ) : ℕ :=
  orChainOut (rowBase r c i) (rowWires r c i)

-- Stage 3 (c*(r-1) gates): col ORs, each col j in Fin c ORs wires [2*rc + i*c + j | i in Fin r]
def colWires (r c j : ℕ) : List ℕ :=
  (List.range r).map (fun i => 2 * (r * c) + i * c + j)

def colBase (r c j : ℕ) : ℕ :=
  3 * (r * c) + r * (c - 1) + j * (r - 1)

def colGates (r c : ℕ) : List Gate :=
  (List.range c).flatMap (fun j => orChainGates (colBase r c j) (colWires r c j))

def colOut (r c j : ℕ) : ℕ :=
  orChainOut (colBase r c j) (colWires r c j)

-- Stage 4 (3r - 5 gates): T_2^r on rowOuts
def t2RowBase (r c : ℕ) : ℕ :=
  3 * (r * c) + r * (c - 1) + c * (r - 1)

def rowOutList (r c : ℕ) : List ℕ :=
  (List.range r).map (rowOut r c)

def t2RowGates (r c : ℕ) : List Gate :=
  t2Gates (t2RowBase r c) (rowOutList r c)

def t2RowOut (r c : ℕ) : ℕ :=
  t2Out (t2RowBase r c) (rowOutList r c)

-- Stage 5 (3c - 5 gates): T_2^c on colOuts
def t2ColBase (r c : ℕ) : ℕ :=
  t2RowBase r c + (3 * r - 5)

def colOutList (r c : ℕ) : List ℕ :=
  (List.range c).map (colOut r c)

def t2ColGates (r c : ℕ) : List Gate :=
  t2Gates (t2ColBase r c) (colOutList r c)

def t2ColOut (r c : ℕ) : ℕ :=
  t2Out (t2ColBase r c) (colOutList r c)

-- Stage 6 (1 gate): OR(t2RowOut, t2ColOut)
def prodCrownGates (r c : ℕ) : List Gate :=
  uvGates (r * c) ++ rowGates r c ++ colGates r c ++ t2RowGates r c ++ t2ColGates r c ++
    [⟨.or, [t2RowOut r c, t2ColOut r c]⟩]

def prodCrownOut (r c : ℕ) : ℕ :=
  t2ColBase r c + (3 * c - 5)

def prodCrown (r c : ℕ) : Circuit :=
  ⟨prodCrownGates r c, prodCrownOut r c⟩

theorem rowGates_len (r c : ℕ) : (rowGates r c).length = r * (c - 1) := by
  unfold rowGates
  have : ∀ k, ((List.range k).flatMap (fun i => orChainGates (rowBase r c i) (rowWires r c i))).length = k * (c - 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [List.range_succ, List.flatMap_append, List.length_append, ih,
            List.flatMap_singleton, orChainGates_len]
        simp [rowWires]; ring
  exact this r

theorem colGates_len (r c : ℕ) : (colGates r c).length = c * (r - 1) := by
  unfold colGates
  have : ∀ k, ((List.range k).flatMap (fun j => orChainGates (colBase r c j) (colWires r c j))).length = k * (r - 1) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [List.range_succ, List.flatMap_append, List.length_append, ih,
            List.flatMap_singleton, orChainGates_len]
        simp [colWires]; ring
  exact this c

theorem prodCrown_size (r c : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) :
    (prodCrown r c).size ≤ 3 * r * c + 2 * (r + c) - 9 := by
  simp only [Circuit.size, prodCrown, prodCrownGates, List.length_append, List.length_cons, List.length_nil,
    uvGates, List.length_ofFn, rowGates_len, colGates_len, t2RowGates, t2ColGates]
  rw [t2Gates_len _ _ (by simp [rowOutList]; omega), t2Gates_len _ _ (by simp [colOutList]; omega)]
  simp only [rowOutList, colOutList, List.length_map, List.length_range]
  have h1 : r * (c - 1) + r = r * c := by
    calc r * (c - 1) + r = r * ((c - 1) + 1) := by ring
    _ = r * c := by rw [Nat.sub_add_cancel (by omega)]
  have h2 : c * (r - 1) + c = c * r := by
    calc c * (r - 1) + c = c * ((r - 1) + 1) := by ring
    _ = c * r := by rw [Nat.sub_add_cancel (by omega)]
  have h3 : c * r = r * c := Nat.mul_comm c r
  have h4 : 3 * r * c = 3 * (r * c) := by ring
  omega

theorem prodCrown_mono (r c : ℕ) : Monotone2 (prodCrown r c) := by
  intro g hg
  simp only [prodCrown, prodCrownGates, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with ((((hg | hg) | hg) | hg) | hg) | rfl
  · simp only [uvGates, List.mem_ofFn] at hg
    obtain ⟨_, rfl⟩ := hg; exact ⟨by simp, by simp⟩
  · simp only [rowGates, List.mem_flatMap] at hg
    obtain ⟨_, _, hg⟩ := hg; exact orChainGates_mono _ _ g hg
  · simp only [colGates, List.mem_flatMap] at hg
    obtain ⟨_, _, hg⟩ := hg; exact orChainGates_mono _ _ g hg
  · exact t2Gates_mono _ _ g hg
  · exact t2Gates_mono _ _ g hg
  · exact ⟨by simp, by simp⟩

-- Semantic evaluation on `oneEach u v`!
theorem oneEach_len (n : ℕ) (u v : Fin n) : (oneEach u v).length = 2 * n := by
  simp [oneEach]; omega

theorem oneEach_getD_left (n : ℕ) (u v : Fin n) (i : ℕ) (hi : i < n) :
    (oneEach u v).getD i false = decide (i = u.1) := by
  unfold oneEach
  rw [List.getD_append _ _ _ _ (by simp; omega)]
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  by_cases h : i = u.1
  · rw [decide_eq_true (Fin.ext h : (⟨i, hi⟩ : Fin n) = u), decide_eq_true h]
  · rw [decide_eq_false (fun he => h (congrArg Fin.val he)), decide_eq_false h]

theorem oneEach_getD_right (n : ℕ) (u v : Fin n) (i : ℕ) (hi1 : n ≤ i) (hi2 : i < 2 * n) :
    (oneEach u v).getD i false = decide (i - n = v.1) := by
  unfold oneEach
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getElem_append_right (by simp; omega)]
  simp only [List.length_ofFn, List.getElem_ofFn]
  have hj : i - n < n := by omega
  by_cases h : i - n = v.1
  · rw [decide_eq_true (Fin.ext h : (⟨i - n, hj⟩ : Fin n) = v), decide_eq_true h]
  · rw [decide_eq_false (fun he => h (congrArg Fin.val he)), decide_eq_false h]

def uvVal (n : ℕ) (u v : Fin n) (k : Fin n) : Bool :=
  decide (k.1 = u.1) || decide (k.1 = v.1)

theorem foldl_uvGates_take (n : ℕ) (u v : Fin n) :
    ∀ k ≤ n, ((uvGates n).take k).foldl stepWire (oneEach u v) =
      oneEach u v ++ (List.ofFn (uvVal n u v)).take k
  | 0, _ => by simp
  | k + 1, hk => by
      have ih := foldl_uvGates_take n u v k (by omega)
      have hlen_g : (uvGates n).length = n := by simp [uvGates]
      have hlen_v : (List.ofFn (uvVal n u v)).length = n := by simp
      rw [List.take_succ_eq_append_getElem (by omega), List.foldl_append, List.foldl_cons, List.foldl_nil, ih]
      rw [List.take_succ_eq_append_getElem (by omega), ← List.append_assoc]
      simp only [stepWire, uvGates, List.getElem_ofFn, uvVal, GateOp.eval,
        List.map_cons, List.map_nil, List.any_cons, List.any_nil, id_eq, Bool.or_false]
      have hlen_oe := oneEach_len n u v
      rw [List.getD_append _ _ _ _ (by omega), List.getD_append _ _ _ _ (by omega)]
      rw [oneEach_getD_left n u v k (by omega), oneEach_getD_right n u v (n + k) (by omega) (by omega)]
      have hsub : n + k - n = k := by omega
      rw [hsub]

theorem foldl_uvGates (n : ℕ) (u v : Fin n) :
    (uvGates n).foldl stepWire (oneEach u v) = oneEach u v ++ List.ofFn (uvVal n u v) := by
  have h := foldl_uvGates_take n u v n (Nat.le_refl n)
  rw [List.take_of_length_le (by simp [uvGates]), List.take_of_length_le (by simp)] at h
  exact h

theorem uv_wire_getD (n : ℕ) (u v : Fin n) (k : ℕ) (hk : k < n) :
    (oneEach u v ++ List.ofFn (uvVal n u v)).getD (2 * n + k) false =
      (decide (k = u.1) || decide (k = v.1)) := by
  have h := getD_append_add (oneEach u v) (List.ofFn (uvVal n u v)) k
  rw [oneEach_len] at h
  have hcomm : k + 2 * n = 2 * n + k := by omega
  rw [hcomm] at h
  rw [h, List.getD_eq_getElem _ _ (by simp; omega), List.getElem_ofFn]
  rfl

-- Row gates evaluation
theorem rowGates_prefix (r c : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) (u v : Fin (r * c)) :
    ∀ k ≤ r,
      let w0 := oneEach u v ++ List.ofFn (uvVal (r * c) u v)
      let wk := ((List.range k).flatMap (fun i => orChainGates (rowBase r c i) (rowWires r c i))).foldl stepWire w0
      wk.length = rowBase r c k ∧
      (∀ i < k, wk.getD (rowOut r c i) false = (decide (i = u.1 / c) || decide (i = v.1 / c))) ∧
      (∀ t < r * c, wk.getD (2 * (r * c) + t) false = (decide (t = u.1) || decide (t = v.1)))
  | 0, _ => by
      refine ⟨?_, fun i hi => by omega, fun t ht => uv_wire_getD (r * c) u v t ht⟩
      simp [oneEach_len, rowBase]; omega
  | k + 1, hk => by
      have ih := rowGates_prefix r c hr hc u v k (by omega)
      dsimp only at ih ⊢
      obtain ⟨hlen, hprev, huv⟩ := ih
      let w0 := oneEach u v ++ List.ofFn (uvVal (r * c) u v)
      let wk := ((List.range k).flatMap (fun i => orChainGates (rowBase r c i) (rowWires r c i))).foldl stepWire w0
      have hsplit : ((List.range (k + 1)).flatMap (fun i => orChainGates (rowBase r c i) (rowWires r c i))).foldl stepWire w0 =
          (orChainGates (rowBase r c k) (rowWires r c k)).foldl stepWire wk := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.foldl_append]
      rw [hsplit]
      have hne : rowWires r c k ≠ [] := by
        simp [rowWires]; omega
      have hlt : ∀ x ∈ rowWires r c k, x < rowBase r c k := by
        intro x hx
        simp only [rowWires, List.mem_map, List.mem_range] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        have hkc : k * c + j < r * c := by
          calc k * c + j < k * c + c := by omega
          _ = (k + 1) * c := by ring
          _ ≤ r * c := Nat.mul_le_mul_right c (by omega)
        simp only [rowBase]; omega
      have heval := foldl_orChainGates (rowBase r c k) (rowWires r c k) wk hlen hne hlt
      have hlen' : ((orChainGates (rowBase r c k) (rowWires r c k)).foldl stepWire wk).length = rowBase r c (k + 1) := by
        rw [foldl_stepWire_len, hlen, orChainGates_len]
        simp only [rowWires, List.length_map, List.length_range, rowBase]
        rw [Nat.add_mul, Nat.one_mul]; omega
      refine ⟨hlen', ?_, ?_⟩
      · intro i hi
        by_cases hik : i < k
        · have hout_lt : rowOut r c i < rowBase r c k := by
            unfold rowOut rowWires
            cases hc0 : c with
            | zero => omega
            | succ c' =>
                cases c' with
                | zero => omega
                | succ c'' =>
                    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, orChainOut,
                      List.length_cons, List.length_map, List.length_range, rowBase]
                    have hsub : c'' + 1 + 1 - 1 = c'' + 1 := by omega
                    rw [hsub]
                    have : (i + 1) * (c'' + 1) ≤ k * (c'' + 1) := Nat.mul_le_mul_right _ (by omega)
                    rw [Nat.add_mul, Nat.one_mul] at this
                    omega
          rw [foldl_stepWire_getD_lt _ wk _ (by rw [hlen]; exact hout_lt)]
          exact hprev i hik
        · have heq : i = k := by omega
          subst heq
          rw [rowOut, heval]
          simp only [rowWires, List.any_map]
          have hany : (List.range c).any (fun j => wk.getD (2 * (r * c) + i * c + j) false) =
              (decide (i = u.1 / c) || decide (i = v.1 / c)) := by
            apply Bool.eq_iff_iff.mpr
            simp only [List.any_eq_true, Function.comp_apply, List.mem_range, Bool.or_eq_true, decide_eq_true_eq]
            constructor
            · rintro ⟨j, hj, hbit⟩
              have hkc : i * c + j < r * c := by
                calc i * c + j < i * c + c := by omega
                _ = (i + 1) * c := by ring
                _ ≤ r * c := Nat.mul_le_mul_right c (by omega)
              have hadd : 2 * (r * c) + i * c + j = 2 * (r * c) + (i * c + j) := by omega
              rw [hadd, huv (i * c + j) hkc] at hbit
              simp only [Bool.or_eq_true, decide_eq_true_eq] at hbit
              rcases hbit with h | h
              · left
                have hdiv : (i * c + j) / c = i := by
                  rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj]; omega
                rw [← h, hdiv]
              · right
                have hdiv : (i * c + j) / c = i := by
                  rw [Nat.mul_comm, Nat.mul_add_div (by omega), Nat.div_eq_of_lt hj]; omega
                rw [← h, hdiv]
            · rintro (hu | hv)
              · refine ⟨u.1 % c, Nat.mod_lt _ (by omega), ?_⟩
                have hkc : i * c + u.1 % c = u.1 := by
                  rw [hu, Nat.mul_comm]; exact Nat.div_add_mod u.1 c
                have hadd : 2 * (r * c) + i * c + u.1 % c = 2 * (r * c) + u.1 := by omega
                rw [hadd, huv u.1 u.2]
                simp
              · refine ⟨v.1 % c, Nat.mod_lt _ (by omega), ?_⟩
                have hkc : i * c + v.1 % c = v.1 := by
                  rw [hv, Nat.mul_comm]; exact Nat.div_add_mod v.1 c
                have hadd : 2 * (r * c) + i * c + v.1 % c = 2 * (r * c) + v.1 := by omega
                rw [hadd, huv v.1 v.2]
                simp
          exact hany
      · intro t ht
        rw [foldl_stepWire_getD_lt _ wk _ (by rw [hlen]; simp only [rowBase]; omega)]
        exact huv t ht

-- Col gates evaluation
theorem colGates_prefix (r c : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) (u v : Fin (r * c))
    (w1 : List Bool) (hw1_len : w1.length = colBase r c 0)
    (hw1_uv : ∀ t < r * c, w1.getD (2 * (r * c) + t) false = (decide (t = u.1) || decide (t = v.1))) :
    ∀ k ≤ c,
      let wk := ((List.range k).flatMap (fun j => orChainGates (colBase r c j) (colWires r c j))).foldl stepWire w1
      wk.length = colBase r c k ∧
      (∀ j < k, wk.getD (colOut r c j) false = (decide (j = u.1 % c) || decide (j = v.1 % c))) ∧
      (∀ t < r * c, wk.getD (2 * (r * c) + t) false = (decide (t = u.1) || decide (t = v.1)))
  | 0, _ => ⟨by simpa using hw1_len, fun j hj => by omega, hw1_uv⟩
  | k + 1, hk => by
      have ih := colGates_prefix r c hr hc u v w1 hw1_len hw1_uv k (by omega)
      dsimp only at ih ⊢
      obtain ⟨hlen, hprev, huv⟩ := ih
      let wk := ((List.range k).flatMap (fun j => orChainGates (colBase r c j) (colWires r c j))).foldl stepWire w1
      have hsplit : ((List.range (k + 1)).flatMap (fun j => orChainGates (colBase r c j) (colWires r c j))).foldl stepWire w1 =
          (orChainGates (colBase r c k) (colWires r c k)).foldl stepWire wk := by
        rw [List.range_succ, List.flatMap_append, List.flatMap_singleton, List.foldl_append]
      rw [hsplit]
      have hne : colWires r c k ≠ [] := by simp [colWires]; omega
      have hlt : ∀ x ∈ colWires r c k, x < colBase r c k := by
        intro x hx
        simp only [colWires, List.mem_map, List.mem_range] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        have hic : i * c + k < r * c := by
          calc i * c + k < i * c + c := by omega
          _ = (i + 1) * c := by ring
          _ ≤ r * c := Nat.mul_le_mul_right c (by omega)
        simp only [colBase]; omega
      have heval := foldl_orChainGates (colBase r c k) (colWires r c k) wk hlen hne hlt
      have hlen' : ((orChainGates (colBase r c k) (colWires r c k)).foldl stepWire wk).length = colBase r c (k + 1) := by
        rw [foldl_stepWire_len, hlen, orChainGates_len]
        simp only [colWires, List.length_map, List.length_range, colBase]
        rw [Nat.add_mul, Nat.one_mul]; omega
      refine ⟨hlen', ?_, ?_⟩
      · intro j hj
        by_cases hjk : j < k
        · have hout_lt : colOut r c j < colBase r c k := by
            unfold colOut colWires
            cases hr0 : r with
            | zero => omega
            | succ r' =>
                cases r' with
                | zero => omega
                | succ r'' =>
                    simp only [List.range_succ_eq_map, List.map_cons, List.map_map, orChainOut,
                      List.length_cons, List.length_map, List.length_range, colBase]
                    have hsub : r'' + 1 + 1 - 1 = r'' + 1 := by omega
                    rw [hsub]
                    have : (j + 1) * (r'' + 1) ≤ k * (r'' + 1) := Nat.mul_le_mul_right _ (by omega)
                    rw [Nat.add_mul, Nat.one_mul] at this
                    omega
          rw [foldl_stepWire_getD_lt _ wk _ (by rw [hlen]; exact hout_lt)]
          exact hprev j hjk
        · have heq : j = k := by omega
          subst heq
          rw [colOut, heval]
          simp only [colWires, List.any_map]
          apply Bool.eq_iff_iff.mpr
          simp only [List.any_eq_true, Function.comp_apply, List.mem_range, Bool.or_eq_true, decide_eq_true_eq]
          constructor
          · rintro ⟨i, hi, hbit⟩
            have hic : i * c + j < r * c := by
              calc i * c + j < i * c + c := by omega
              _ = (i + 1) * c := by ring
              _ ≤ r * c := Nat.mul_le_mul_right c (by omega)
            have hadd : 2 * (r * c) + i * c + j = 2 * (r * c) + (i * c + j) := by omega
            rw [hadd, huv (i * c + j) hic] at hbit
            simp only [Bool.or_eq_true, decide_eq_true_eq] at hbit
            rcases hbit with h | h
            · left
              have hmod : (i * c + j) % c = j := by
                rw [Nat.mul_comm i c, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
              rw [← h, hmod]
            · right
              have hmod : (i * c + j) % c = j := by
                rw [Nat.mul_comm i c, Nat.mul_add_mod, Nat.mod_eq_of_lt (by omega)]
              rw [← h, hmod]
          · rintro (hu | hv)
            · refine ⟨u.1 / c, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq u.2 (Nat.mul_comm r c)), ?_⟩
              have hic : (u.1 / c) * c + j = u.1 := by
                rw [hu, Nat.mul_comm]; exact Nat.div_add_mod u.1 c
              have hadd : 2 * (r * c) + (u.1 / c) * c + j = 2 * (r * c) + u.1 := by omega
              rw [hadd, huv u.1 u.2]; simp
            · refine ⟨v.1 / c, Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq v.2 (Nat.mul_comm r c)), ?_⟩
              have hic : (v.1 / c) * c + j = v.1 := by
                rw [hv, Nat.mul_comm]; exact Nat.div_add_mod v.1 c
              have hadd : 2 * (r * c) + (v.1 / c) * c + j = 2 * (r * c) + v.1 := by omega
              rw [hadd, huv v.1 v.2]; simp
      · intro t ht
        rw [foldl_stepWire_getD_lt _ wk _ (by rw [hlen]; simp only [colBase]; omega)]
        exact huv t ht

-- Counting true entries of `(fun i => decide (i = a) || decide (i = b))` over `List.range m`
theorem count_two_eq (m a b : ℕ) (ha : a < m) (hb : b < m) :
    ((List.range m).map (fun i => decide (i = a) || decide (i = b))).count true =
      if a = b then 1 else 2 := by
  have hgen : ∀ k,
      ((List.range k).map (fun i => decide (i = a) || decide (i = b))).count true =
        if a = b then (if a < k then 1 else 0)
        else (if a < k then 1 else 0) + (if b < k then 1 else 0) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
        rw [List.range_succ, List.map_append, List.count_append, ih, List.map_singleton, List.count_singleton]
        by_cases hab : a = b
        · subst hab
          by_cases hka : k = a
          · subst hka; simp
          · by_cases hlt : a < k
            · have hlt2 : a < k + 1 := by omega
              simp [hlt, hlt2, hka]
            · have hlt2 : ¬ a < k + 1 := by omega
              simp [hlt, hlt2, hka]
        · by_cases hka : k = a
          · subst hka
            have hkb : k ≠ b := hab
            by_cases hbk : b < k
            · have hbk2 : b < k + 1 := by omega
              simp [hab, hkb, hbk, hbk2]
            · have hbk2 : ¬ b < k + 1 := by omega
              simp [hab, hkb, hbk, hbk2]
          · by_cases hkb : k = b
            · subst hkb
              by_cases hak : a < k
              · have hak2 : a < k + 1 := by omega
                simp [hab, hka, hak, hak2]
              · have hak2 : ¬ a < k + 1 := by omega
                simp [hab, hka, hak, hak2]
            · by_cases hak : a < k <;> by_cases hbk : b < k
              · have hak2 : a < k + 1 := by omega
                have hbk2 : b < k + 1 := by omega
                simp [hab, hka, hkb, hak, hak2, hbk, hbk2]
              · have hak2 : a < k + 1 := by omega
                have hbk2 : ¬ b < k + 1 := by omega
                simp [hab, hka, hkb, hak, hak2, hbk, hbk2]
              · have hak2 : ¬ a < k + 1 := by omega
                have hbk2 : b < k + 1 := by omega
                simp [hab, hka, hkb, hak, hak2, hbk, hbk2]
              · have hak2 : ¬ a < k + 1 := by omega
                have hbk2 : ¬ b < k + 1 := by omega
                simp [hab, hka, hkb, hak, hak2, hbk, hbk2]
  rw [hgen m]
  simp [ha, hb]

theorem rowOut_lt (r c i : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) (hi : i < r) :
    rowOut r c i < rowBase r c r := by
  unfold rowOut rowWires
  cases hc0 : c with
  | zero => omega
  | succ c' =>
      cases c' with
      | zero => omega
      | succ c'' =>
          simp only [List.range_succ_eq_map, List.map_cons, List.map_map, orChainOut,
            List.length_cons, List.length_map, List.length_range, rowBase]
          have hsub : c'' + 1 + 1 - 1 = c'' + 1 := by omega
          rw [hsub]
          have : (i + 1) * (c'' + 1) ≤ r * (c'' + 1) := Nat.mul_le_mul_right _ (by omega)
          rw [Nat.add_mul, Nat.one_mul] at this
          omega

theorem colOut_lt (r c j : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) (hj : j < c) :
    colOut r c j < colBase r c c := by
  unfold colOut colWires
  cases hr0 : r with
  | zero => omega
  | succ r' =>
      cases r' with
      | zero => omega
      | succ r'' =>
          simp only [List.range_succ_eq_map, List.map_cons, List.map_map, orChainOut,
            List.length_cons, List.length_map, List.length_range, colBase]
          have hsub : r'' + 1 + 1 - 1 = r'' + 1 := by omega
          rw [hsub]
          have : (j + 1) * (r'' + 1) ≤ c * (r'' + 1) := Nat.mul_le_mul_right _ (by omega)
          rw [Nat.add_mul, Nat.one_mul] at this
          omega

theorem prodCrown_rep (r c : ℕ) (hr : 2 ≤ r) (hc : 2 ≤ c) :
    Represents (fun u v : Fin (r * c) => decide (u ≠ v)) (prodCrown r c) := by
  intro u v
  unfold Circuit.eval Circuit.wires prodCrown prodCrownGates
  change (((uvGates (r * c) ++ rowGates r c ++ colGates r c ++ t2RowGates r c ++ t2ColGates r c ++
    [({ op := .or, inputs := [t2RowOut r c, t2ColOut r c] } : Gate)]).foldl stepWire (oneEach u v)).getD (prodCrownOut r c) false) = decide (u ≠ v)
  simp only [List.foldl_append]
  rw [foldl_uvGates]
  -- Stage 2: rowGates
  have hrow := rowGates_prefix r c hr hc u v r (Nat.le_refl r)
  dsimp only at hrow
  obtain ⟨hw1_len, hw1_row, hw1_uv⟩ := hrow
  let w1 := (rowGates r c).foldl stepWire (oneEach u v ++ List.ofFn (uvVal (r * c) u v))
  have hw1_len' : w1.length = colBase r c 0 := by
    simpa [w1, rowGates, rowBase, colBase] using hw1_len
  -- Stage 3: colGates
  have hcol := colGates_prefix r c hr hc u v w1 hw1_len' hw1_uv c (Nat.le_refl c)
  dsimp only at hcol
  obtain ⟨hw2_len, hw2_col, _⟩ := hcol
  let w2 := (colGates r c).foldl stepWire w1
  have hw2_len' : w2.length = t2RowBase r c := by
    simpa [w2, colGates, colBase, t2RowBase] using hw2_len
  have hw2_row : ∀ i < r, w2.getD (rowOut r c i) false = (decide (i = u.1 / c) || decide (i = v.1 / c)) := by
    intro i hi
    have hlt := rowOut_lt r c i hr hc hi
    rw [show w2.getD (rowOut r c i) false = w1.getD (rowOut r c i) false from
      foldl_stepWire_getD_lt (colGates r c) w1 (rowOut r c i) (by rw [hw1_len']; simp [rowBase, colBase] at hlt ⊢; omega)]
    exact hw1_row i hi
  -- Stage 4: t2RowGates
  let w3 := (t2RowGates r c).foldl stepWire w2
  have hw3_len : w3.length = t2ColBase r c := by
    simp only [w3, t2RowGates, foldl_stepWire_len, hw2_len', t2ColBase]
    rw [t2Gates_len _ _ (by simp [rowOutList]; omega)]
    simp [rowOutList]
  have hw3_row_out : w3.getD (t2RowOut r c) false = decide (u.1 / c ≠ v.1 / c) := by
    have he := t2Gates_eval (t2RowBase r c) (rowOutList r c) w2 hw2_len'
      (by simp [rowOutList]; omega)
      (by
        intro x hx
        simp only [rowOutList, List.mem_map, List.mem_range] at hx
        obtain ⟨i, hi, rfl⟩ := hx
        have hlt := rowOut_lt r c i hr hc hi
        simp only [rowBase, t2RowBase] at hlt ⊢; omega)
    rw [show w3.getD (t2RowOut r c) false = decide (2 ≤ countTrue w2 (rowOutList r c)) from he]
    have hct : countTrue w2 (rowOutList r c) =
        ((List.range r).map (fun i => decide (i = u.1 / c) || decide (i = v.1 / c))).count true := by
      unfold countTrue rowOutList
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact hw2_row i (List.mem_range.mp hi)
    rw [hct, count_two_eq r (u.1 / c) (v.1 / c)
      (Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq u.2 (Nat.mul_comm r c)))
      (Nat.div_lt_of_lt_mul (Nat.lt_of_lt_of_eq v.2 (Nat.mul_comm r c)))]
    by_cases h : u.1 / c = v.1 / c <;> simp [h]
  -- Stage 5: t2ColGates
  let w4 := (t2ColGates r c).foldl stepWire w3
  have hw4_len : w4.length = prodCrownOut r c := by
    simp only [w4, t2ColGates, foldl_stepWire_len, hw3_len, prodCrownOut]
    rw [t2Gates_len _ _ (by simp [colOutList]; omega)]
    simp [colOutList]
  have hw3_col : ∀ j < c, w3.getD (colOut r c j) false = (decide (j = u.1 % c) || decide (j = v.1 % c)) := by
    intro j hj
    have hlt := colOut_lt r c j hr hc hj
    rw [show w3.getD (colOut r c j) false = w2.getD (colOut r c j) false from
      foldl_stepWire_getD_lt (t2RowGates r c) w2 (colOut r c j) (by rw [hw2_len']; simp [colBase, t2RowBase] at hlt ⊢; omega)]
    exact hw2_col j hj
  have hw4_col_out : w4.getD (t2ColOut r c) false = decide (u.1 % c ≠ v.1 % c) := by
    have he := t2Gates_eval (t2ColBase r c) (colOutList r c) w3 hw3_len
      (by simp [colOutList]; omega)
      (by
        intro x hx
        simp only [colOutList, List.mem_map, List.mem_range] at hx
        obtain ⟨j, hj, rfl⟩ := hx
        have hlt := colOut_lt r c j hr hc hj
        simp only [colBase, t2RowBase, t2ColBase] at hlt ⊢; omega)
    rw [show w4.getD (t2ColOut r c) false = decide (2 ≤ countTrue w3 (colOutList r c)) from he]
    have hct : countTrue w3 (colOutList r c) =
        ((List.range c).map (fun j => decide (j = u.1 % c) || decide (j = v.1 % c))).count true := by
      unfold countTrue colOutList
      rw [List.map_map]
      congr 1
      apply List.map_congr_left
      intro j hj
      exact hw3_col j (List.mem_range.mp hj)
    rw [hct, count_two_eq c (u.1 % c) (v.1 % c)
      (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))]
    by_cases h : u.1 % c = v.1 % c <;> simp [h]
  have hw4_row_out : w4.getD (t2RowOut r c) false = decide (u.1 / c ≠ v.1 / c) := by
    have hlt : t2RowOut r c < t2ColBase r c := by
      simp only [t2RowOut, t2Out, rowOutList, List.length_map, List.length_range, t2ColBase]
      omega
    rw [show w4.getD (t2RowOut r c) false = w3.getD (t2RowOut r c) false from
      foldl_stepWire_getD_lt (t2ColGates r c) w3 (t2RowOut r c) (by omega)]
    exact hw3_row_out
  -- Stage 6: final OR gate
  change ((stepWire w4 ⟨.or, [t2RowOut r c, t2ColOut r c]⟩)).getD (prodCrownOut r c) false = decide (u ≠ v)
  simp only [stepWire, GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil,
    id_eq, Bool.or_false, getD_snoc_self w4 _ (prodCrownOut r c) hw4_len, hw4_row_out, hw4_col_out]
  apply Bool.eq_iff_iff.mpr
  simp only [Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro h heq
    subst heq
    rcases h with h | h <;> exact h rfl
  · intro hne
    by_cases hd : u.1 / c = v.1 / c
    · right
      intro hm
      apply hne
      apply Fin.ext
      have hu := Nat.div_add_mod u.1 c
      have hv := Nat.div_add_mod v.1 c
      rw [hd, hm] at hu
      omega
    · left; exact hd

end PEqualNP.Outside.L_meta_18183

theorem PEqualNP.Outside.L_meta_18183 : ∀ r c : ℕ, 2 ≤ r → 2 ≤ c → PEqualNP.Represents.RepSizeAtMost (fun u v : Fin (r * c) => decide (u ≠ v)) (3 * r * c + 2 * (r + c) - 9) :=
  fun r c hr hc =>
    ⟨PEqualNP.Outside.L_meta_18183.prodCrown r c,
     PEqualNP.Outside.L_meta_18183.prodCrown_mono r c,
     PEqualNP.Outside.L_meta_18183.prodCrown_size r c hr hc,
     PEqualNP.Outside.L_meta_18183.prodCrown_rep r c hr hc⟩
