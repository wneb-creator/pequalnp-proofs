import Prune

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
