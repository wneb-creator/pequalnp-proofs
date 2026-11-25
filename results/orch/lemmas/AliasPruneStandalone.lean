import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.Prune

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Classical

def shift (k i : ℕ) : ℕ := if i < k then i else i - 1

def shiftGate (k : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (shift k)⟩

def run (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma run_length (gs : List Gate) (w : List Bool) :
    (run gs w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w ++ [_])).length = w.length + (g :: gs).length
    rw [ih]
    simp
    omega

lemma getD_snoc (l : List Bool) (b : Bool) (k : ℕ) :
    (l ++ [b]).getD k false =
      if k < l.length then l.getD k false else if k = l.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2
    simp
  · rw [List.getElem?_eq_none]
    · rfl
    · simp
      omega

def Related (k : ℕ) (u v : List Bool) : Prop :=
  u.length + 1 = v.length ∧ k < v.length ∧
    ∀ i, i ≠ k → u.getD (shift k i) false = v.getD i false

lemma related_start (u : List Bool) (b : Bool) : Related u.length u (u ++ [b]) := by
  refine ⟨by simp, by simp, ?_⟩
  intro i hi
  rw [getD_snoc]
  by_cases h : i < u.length
  · simp [shift, h]
  · have he : u.length ≤ shift u.length i := by simp [shift, h]; omega
    rw [List.getD_eq_default _ _ he]
    simp [h, hi]

lemma related_snoc {k : ℕ} {u v : List Bool} (h : Related k u v) (b : Bool) :
    Related k (u ++ [b]) (v ++ [b]) := by
  rcases h with ⟨hl, hk, hr⟩
  refine ⟨by simp; omega, by simp; omega, ?_⟩
  intro i hi
  rw [getD_snoc, getD_snoc]
  have he : shift k i < u.length ↔ i < v.length := by unfold shift; split_ifs <;> omega
  have heq : shift k i = u.length ↔ i = v.length := by unfold shift; split_ifs <;> omega
  simp only [he, heq]
  split_ifs with h1 h2
  · exact hr i hi
  · rfl
  · rfl

lemma run_related (gs : List Gate) (k : ℕ)
    (noRead : ∀ g ∈ gs, k ∉ g.inputs) {u v : List Bool} (hr : Related k u v) :
    Related k (run (gs.map (shiftGate k)) u) (run gs v) := by
  induction gs generalizing u v with
  | nil => exact hr
  | cons g gs ih =>
    have hv : (shiftGate k g).op.eval ((shiftGate k g).inputs.map fun i => u.getD i false) =
        g.op.eval (g.inputs.map fun i => v.getD i false) := by
      congr 1
      simp only [shiftGate, List.map_map]
      apply List.map_congr_left
      intro i hi
      exact hr.2.2 i (fun e => noRead g (by simp) (e ▸ hi))
    change Related k
      (run (gs.map (shiftGate k)) (u ++ [(shiftGate k g).op.eval ((shiftGate k g).inputs.map fun i => u.getD i false)]))
      (run gs (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]))
    rw [hv]
    exact ih (fun q hq => noRead q (List.mem_cons_of_mem _ hq)) (related_snoc hr _)

def drop (n : ℕ) (pre post : List Gate) (out : ℕ) : Circuit :=
  ⟨pre ++ post.map (shiftGate (n + pre.length)), shift (n + pre.length) out⟩

lemma drop_eval (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (out : ℕ)
    (noRead : ∀ q ∈ post, n + pre.length ∉ q.inputs) (notOut : out ≠ n + pre.length)
    (x : List Bool) (hlen : x.length = n) :
    (drop n pre post out).eval x = (⟨pre ++ g :: post, out⟩ : Circuit).eval x := by
  let w := run pre x
  let b := g.op.eval (g.inputs.map fun i => w.getD i false)
  have hw : w.length = n + pre.length := by simpa [w, hlen] using run_length pre x
  have hr := related_start w b
  rw [hw] at hr
  have hf := run_related post (n + pre.length) noRead hr
  simpa only [Circuit.eval, Circuit.wires, drop, run, List.foldl_append, List.foldl_cons, w, b]
    using hf.2.2 out notOut

lemma drop_fan (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (out : ℕ)
    (fan : FanInTwo (⟨pre ++ g :: post, out⟩ : Circuit)) :
    FanInTwo (drop n pre post out) := by
  intro q hq
  rcases List.mem_append.mp hq with hp | hs
  · exact fan q (List.mem_append_left _ hp)
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
    obtain ⟨hop, hlen⟩ := fan r (List.mem_append_right _ (List.mem_cons_of_mem _ hr))
    exact ⟨hop, by simpa [shiftGate] using hlen⟩

lemma drop_size (n : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ) :
    (drop n pre post out).size + 1 = (⟨pre ++ g :: post, out⟩ : Circuit).size := by
  simp [drop, Circuit.size]
  omega

lemma drop_notCount (n : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ) :
    NotBracket.notCount (drop n pre post out) + (if g.op = GateOp.not then 1 else 0) =
      NotBracket.notCount (⟨pre ++ g :: post, out⟩ : Circuit) := by
  letI : DecidableEq GateOp := lineDegreeGateOpDecEq
  simp only [NotBracket.notCount, drop, List.filter_append, List.filter_map, List.length_append,
    List.length_map]
  have he : (fun q => decide (q.op = GateOp.not)) ∘ shiftGate (n + pre.length) =
      (fun q => decide (q.op = GateOp.not)) := rfl
  rw [he]
  by_cases hg : g.op = GateOp.not <;> simp [hg] <;> omega

def weight (C : Circuit) : ℕ := C.size + if NotBracket.notCount C = 0 then 1 else 0

lemma drop_weight (n : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ) :
    weight (drop n pre post out) ≤ weight (⟨pre ++ g :: post, out⟩ : Circuit) := by
  have hs := drop_size n pre post g out
  have hn := drop_notCount n pre post g out
  unfold weight
  split_ifs at * <;> omega

end PEqualNP.Outside.L_meta_2592_aux.Prune


namespace PEqualNP.Outside.L_meta_2592_aux.AliasPrune

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open Prune Classical

def redirect (k a i : ℕ) : ℕ := if i = k then a else shift k i

def redirectGate (k a : ℕ) (g : Gate) : Gate := ⟨g.op, g.inputs.map (redirect k a)⟩

def Related (k a : ℕ) (u v : List Bool) : Prop :=
  u.length + 1 = v.length ∧ a < k ∧ k < v.length ∧
    ∀ i, u.getD (redirect k a i) false = v.getD i false

lemma related_start (u : List Bool) (a : ℕ) (ha : a < u.length) :
    Related u.length a u (u ++ [u.getD a false]) := by
  refine ⟨by simp, ha, by simp, ?_⟩
  intro i
  by_cases hi : i = u.length
  · simp [redirect, hi, getD_snoc]
  · simpa [redirect, hi] using (Prune.related_start u (u.getD a false)).2.2 i hi

lemma related_snoc {k a : ℕ} {u v : List Bool} (h : Related k a u v) (b : Bool) :
    Related k a (u ++ [b]) (v ++ [b]) := by
  rcases h with ⟨hl, ha, hk, hr⟩
  refine ⟨by simp; omega, ha, by simp; omega, ?_⟩
  intro i
  rw [getD_snoc, getD_snoc]
  have he : redirect k a i < u.length ↔ i < v.length := by
    unfold redirect shift
    split_ifs <;> omega
  have heq : redirect k a i = u.length ↔ i = v.length := by
    unfold redirect shift
    split_ifs <;> omega
  simp only [he, heq]
  split_ifs with h1 h2
  · exact hr i
  · rfl
  · rfl

lemma run_related (gs : List Gate) (k a : ℕ) {u v : List Bool} (hr : Related k a u v) :
    Related k a (Prune.run (gs.map (redirectGate k a)) u) (Prune.run gs v) := by
  induction gs generalizing u v with
  | nil => exact hr
  | cons g gs ih =>
    have hv : (redirectGate k a g).op.eval ((redirectGate k a g).inputs.map fun i => u.getD i false) =
        g.op.eval (g.inputs.map fun i => v.getD i false) := by
      congr 1
      simp only [redirectGate, List.map_map]
      apply List.map_congr_left
      intro i hi
      exact hr.2.2.2 i
    change Related k a
      (Prune.run (gs.map (redirectGate k a)) (u ++ [(redirectGate k a g).op.eval ((redirectGate k a g).inputs.map fun i => u.getD i false)]))
      (Prune.run gs (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]))
    rw [hv]
    exact ih (related_snoc hr _)

def drop (n a : ℕ) (pre post : List Gate) (out : ℕ) : Circuit :=
  ⟨pre ++ post.map (redirectGate (n + pre.length) a), redirect (n + pre.length) a out⟩

lemma drop_eval (n a : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (out : ℕ)
    (ha : a < n + pre.length) (x : List Bool) (hlen : x.length = n)
    (aliasEq : g.op.eval (g.inputs.map fun i => (Prune.run pre x).getD i false) =
      (Prune.run pre x).getD a false) :
    (drop n a pre post out).eval x = (⟨pre ++ g :: post, out⟩ : Circuit).eval x := by
  let w := Prune.run pre x
  have hw : w.length = n + pre.length := by simpa [w, hlen] using Prune.run_length pre x
  have hr := related_start w a (by omega)
  rw [hw] at hr
  have hf := run_related post (n + pre.length) a hr
  have he := hf.2.2.2 out
  have hal : g.op.eval (g.inputs.map fun i => w.getD i false) = w.getD a false := aliasEq
  simp only [Circuit.eval, Circuit.wires, drop, List.foldl_append, List.foldl_cons]
  change (Prune.run (post.map (redirectGate (n + pre.length) a)) w).getD
    (redirect (n + pre.length) a out) false =
    (Prune.run post (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])).getD out false
  rw [hal]
  exact he

lemma drop_fan (n a : ℕ) (pre : List Gate) (g : Gate) (post : List Gate) (out : ℕ)
    (fan : FanInTwo (⟨pre ++ g :: post, out⟩ : Circuit)) :
    FanInTwo (drop n a pre post out) := by
  intro q hq
  rcases List.mem_append.mp hq with hp | hs
  · exact fan q (List.mem_append_left _ hp)
  · obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hs
    obtain ⟨hop, hlen⟩ := fan r (List.mem_append_right _ (List.mem_cons_of_mem _ hr))
    exact ⟨hop, by simpa [redirectGate] using hlen⟩

lemma drop_size (n a : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ) :
    (drop n a pre post out).size + 1 = (⟨pre ++ g :: post, out⟩ : Circuit).size := by
  simp [drop, Circuit.size]
  omega

lemma drop_notCount (n a : ℕ) (pre post : List Gate) (g : Gate) (out : ℕ) :
    NotBracket.notCount (drop n a pre post out) + (if g.op = GateOp.not then 1 else 0) =
      NotBracket.notCount (⟨pre ++ g :: post, out⟩ : Circuit) := by
  letI : DecidableEq GateOp := lineDegreeGateOpDecEq
  simp only [NotBracket.notCount, drop, List.filter_append, List.filter_map, List.length_append,
    List.length_map]
  have he : (fun q => decide (q.op = GateOp.not)) ∘ redirectGate (n + pre.length) a =
      (fun q => decide (q.op = GateOp.not)) := rfl
  rw [he]
  by_cases hg : g.op = GateOp.not <;> simp [hg] <;> omega

end PEqualNP.Outside.L_meta_2592_aux.AliasPrune
