import CompactSymmetryReplay

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Symmetry.Full
open Reduced Checkpoint

def fast (w : Nat) (p : List Nat) (x : Nat) : Nat :=
  (p.map (fun j => Fast.bit x j)).foldr Nat.bit (x / 2^w)

theorem fast_eq {w : Nat} {p : List Nat} (hp : p.length = w) (x : Nat) :
    fast w p x = permWord w (p.getD · 0) x := by
  apply Nat.eq_of_testBit_eq
  intro j
  change (putBits (p.map (fun i => Fast.bit x i)) (x / 2^w)).testBit j = _
  rw [putBits_testBit, permWord_testBit]
  simp only [List.length_map, hp]
  by_cases hj : j < w
  · rw [if_pos hj, if_pos hj, getD_map_lt _ (fun i => Fast.bit x i) 0 false j (by omega),
      Fast.bit_eq]
  · rw [if_neg hj, if_neg hj, ←Nat.shiftRight_eq_div_pow, Nat.testBit_shiftRight]
    congr 1
    omega

def Check (k : Nat) (pool p q : List Nat) : Bool :=
  decide (p.length = k+k) &&
  (List.range (k+k)).all (fun j => decide (p.getD j 0 < k+k ∧ q.getD j 0 < k+k ∧
    p.getD (q.getD j 0) 0 = j ∧ (k ≤ p.getD j 0 ↔ k ≤ j))) &&
  pool.all (fun a => (pool.map (fast (k+k) p)).contains a)

def Good (k : Nat) (pool p : List Nat) : Prop :=
  p.length = k+k ∧ (∀ j < k+k, p.getD j 0 < k+k) ∧
  (∀ j < k+k, k ≤ p.getD j 0 ↔ k ≤ j) ∧
  ∀ {s : Nat} {ws : List Nat}, RNatRun pool (Live.mask k) (Live.goal k) s ws →
    RNatRun pool (Live.mask k) (Live.goal k) s (ws.map (fast (k+k) p))

theorem check_good {k : Nat} {pool p q : List Nat} (hc : Check k pool p q = true) :
    Good k pool p := by
  simp only [Check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true,
    List.mem_range] at hc
  have hp := fun j hj => (hc.1.2 j hj).1
  have hh := fun j hj => (hc.1.2 j hj).2.2.2
  refine ⟨hc.1.1, hp, hh, ?_⟩
  intro s ws h
  have he : fast (k+k) p = permWord (k+k) (p.getD · 0) := funext (fast_eq hc.1.1)
  have hf : pool.Subset (pool.map (fast (k+k) p)) := by
    intro a ha
    simpa using hc.2 a ha
  rw [he] at hf ⊢
  apply run_map (permWord (k+k) (p.getD · 0))
    (permWord_injective (k+k) (p.getD · 0) (q.getD · 0)
      (fun j hj => (hc.1.2 j hj).2.1) (fun j hj => (hc.1.2 j hj).2.2.1)) _
    (permWord_and _ _) (permWord_or _ _) (permWord_halfGoal k _ hp hh) hf h
  intro a
  change permWord (k+k) (p.getD · 0) (a ^^^ (2^(k+k)-1)) = _
  rw [permWord_xor, permWord_mask _ _ hp]
  rfl

theorem fast_id (w x : Nat) : fast w (List.range w) x = x := by
  rw [fast_eq List.length_range]
  apply Nat.eq_of_testBit_eq
  intro j
  rw [permWord_testBit]
  by_cases hj : j < w
  · rw [if_pos hj, range_getD hj]
  · rw [if_neg hj]

theorem good_id (k : Nat) (pool : List Nat) : Good k pool (List.range (k+k)) := by
  refine ⟨List.length_range, ?_, ?_, ?_⟩
  · intro j hj
    simpa only [range_getD hj] using hj
  · intro j hj
    rw [range_getD hj]
  · intro s ws h
    have he : fast (k+k) (List.range (k+k)) = id := funext (fast_id (k+k))
    simpa only [he, List.map_id] using h

theorem fast_comp {w : Nat} {p q : List Nat}
    (hp : p.length = w) (hq : q.length = w) (hb : ∀ j < w, q.getD j 0 < w) (x : Nat) :
    fast w (q.map (p.getD · 0)) x = fast w q (fast w p x) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [fast_eq (by simpa using hq), permWord_testBit, fast_eq hq, permWord_testBit,
    fast_eq hp, permWord_testBit]
  by_cases hj : j < w
  · simp only [if_pos hj, if_pos (hb j hj)]
    rw [getD_map_lt q (p.getD · 0) 0 0 j (by omega)]
  · simp only [if_neg hj]

theorem good_comp {k : Nat} {pool p q : List Nat}
    (hp : Good k pool p) (hq : Good k pool q) : Good k pool (q.map (p.getD · 0)) := by
  refine ⟨by simpa using hq.1, ?_, ?_, ?_⟩
  · intro j hj
    rw [getD_map_lt q (p.getD · 0) 0 0 j (by simpa [hq.1] using hj)]
    exact hp.2.1 _ (hq.2.1 j hj)
  · intro j hj
    rw [getD_map_lt q (p.getD · 0) 0 0 j (by simpa [hq.1] using hj)]
    exact (hp.2.2.1 _ (hq.2.1 j hj)).trans (hq.2.2.1 j hj)
  · intro s ws h
    have hh := hq.2.2.2 (hp.2.2.2 h)
    have he : fast (k+k) (q.map (p.getD · 0)) = (fun w => fast (k+k) q (fast (k+k) p w)) :=
      funext (fast_comp hp.1 hq.1 hq.2.1)
    simpa only [he, List.map_map, Function.comp_def] using hh

def packedCheck (k pw rw rb n fw fb count : Nat) (pool : List Nat)
    (gs : Array (List Nat)) (q : Nat → List Nat) (rs refs : Array Nat) : Bool :=
  (List.range gs.size).all (fun i => Check k pool (gs.getD i []) (q i)) &&
  recipeCheck pw rw rb n gs.size rs && actionCheck fw fb count (n+1) refs

theorem checked_actions {k pw rw rb n fw fb count : Nat} {pool : List Nat}
    {gs : Array (List Nat)} {rs refs : Array Nat} (q : Nat → List Nat)
    (hc : packedCheck k pw rw rb n fw fb count pool gs q rs refs = true) :
    ∀ p ∈ actions fw fb count refs (group (k+k) pw rw rb n gs rs), Good k pool p := by
  simp only [packedCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  apply actions_preserves
  · exact group_preserves (Good k pool) (k+k) pw rw rb n gs rs (good_id k pool)
      (array_all (xs := gs) (P := Good k pool) [] rfl (fun i => check_good (hc.1.1 i i.2)))
      (fun _ _ hp hq => good_comp hp hq) hc.1.2
  · simpa only [group_size] using hc.2

def word (k n : Nat) (ps : Array (List Nat)) (g : Nat) : Nat → Nat :=
  if g % n = 0 then id else fast (k+k) (ps.getD (g % n) [])

theorem word_run {k n : Nat} {pool : List Nat} {ps : Array (List Nat)}
    (hn : 0 < n) (hs : ps.size = n) (hp : ∀ p ∈ ps, Good k pool p)
    (g : Nat) {u : Nat} {ws : List Nat}
    (h : RNatRun pool (Live.mask k) (Live.goal k) u ws) :
    RNatRun pool (Live.mask k) (Live.goal k) u (ws.map (word k n ps g)) := by
  unfold word
  split
  · simpa only [List.map_id] using h
  · exact (hp _ (array_getD_mem _ [] (by rw [hs]; exact Nat.mod_lt _ hn))).2.2.2 h

def orient (k n : Nat) (ps : Array (List Nat)) (payload : Nat) (ws : List Nat) :=
  if payload = 0 then ws else ws.map (word k n ps ((payload-1)%64))

theorem orient_run {k n : Nat} {pool : List Nat} {ps : Array (List Nat)}
    (hn : 0 < n) (hs : ps.size = n) (hp : ∀ p ∈ ps, Good k pool p)
    (payload : Nat) {u : Nat} {ws : List Nat}
    (h : RNatRun pool (Live.mask k) (Live.goal k) u ws) :
    RNatRun pool (Live.mask k) (Live.goal k) u (orient k n ps payload ws) := by
  unfold orient
  split
  · exact h
  · exact word_run hn hs hp _ h

end PEqualNP.Outside.L_meta_982_aux.Finite.Symmetry.Full
