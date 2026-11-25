import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.Prune

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
local instance : DecidableEq GateOp := lineDegreeGateOpDecEq

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
