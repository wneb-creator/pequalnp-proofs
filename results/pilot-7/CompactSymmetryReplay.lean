import CompactSymmetry
import CompactSymmetryDecoder

namespace PEqualNP.Outside.L_meta_982_aux.Checkpoint

theorem group_succ (k pw rw rb n : Nat) (gs : Array (List Nat)) (rs : Array Nat) :
    group k pw rw rb (n+1) gs rs =
      let code := getPacked rw rb rs n
      let acc := group k pw rw rb n gs rs
      acc.push ((gs.getD (code / 2^pw) []).map ((acc.getD (code % 2^pw) []).getD · 0)) := by
  simp only [group, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]

theorem group_size (k pw rw rb n : Nat) (gs : Array (List Nat)) (rs : Array Nat) :
    (group k pw rw rb n gs rs).size = n+1 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [group_succ, Array.size_push, ih]

theorem array_getD_mem {α : Type} (xs : Array α) (d : α) {j : Nat} (hj : j < xs.size) :
    xs.getD j d ∈ xs := by
  simpa [Array.getD, hj] using Array.getElem_mem hj

def recipeCheck (pw rw rb n ng : Nat) (rs : Array Nat) : Bool :=
  (List.range n).all (fun i =>
    decide (getPacked rw rb rs i % 2^pw < i+1 ∧ getPacked rw rb rs i / 2^pw < ng))

theorem group_preserves (P : List Nat → Prop) (k pw rw rb n : Nat)
    (gs : Array (List Nat)) (rs : Array Nat)
    (hid : P (List.range k)) (hgs : ∀ p ∈ gs, P p)
    (hcomp : ∀ p q, P p → P q → P (q.map (p.getD · 0)))
    (hc : recipeCheck pw rw rb n gs.size rs = true) :
    ∀ p ∈ group k pw rw rb n gs rs, P p := by
  simp only [recipeCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  induction n with
  | zero => simpa [group] using hid
  | succ n ih =>
    have hh := ih (fun i hi => hc i (by omega))
    intro p hp
    rw [group_succ] at hp
    rcases Array.mem_push.1 hp with hp | hp
    · exact hh p hp
    · subst p
      exact hcomp _ _
        (hh _ (array_getD_mem _ [] (by rw [group_size]; exact (hc n (by omega)).1)))
        (hgs _ (array_getD_mem _ [] (hc n (by omega)).2))

def actionCheck (fw fb n ng : Nat) (refs : Array Nat) : Bool :=
  (List.range n).all (fun i => decide (getPacked fw fb refs i < ng))

theorem actions_preserves (P : List Nat → Prop) (fw fb n : Nat)
    (refs : Array Nat) (gs : Array (List Nat))
    (hg : ∀ p ∈ gs, P p) (hc : actionCheck fw fb n gs.size refs = true) :
    ∀ p ∈ actions fw fb n refs gs, P p := by
  simp only [actionCheck, List.all_eq_true, List.mem_range, decide_eq_true_eq] at hc
  intro p hp
  simp only [actions, List.mem_toArray, List.mem_map, List.mem_range] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  exact hg _ (array_getD_mem _ [] (hc i hi))

theorem actions_size (fw fb n : Nat) (refs : Array Nat) (gs : Array (List Nat)) :
    (actions fw fb n refs gs).size = n := by simp [actions]

end PEqualNP.Outside.L_meta_982_aux.Checkpoint

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Symmetry
open Reduced Checkpoint

theorem good_actions {k pw rw rb n fw fb count : Nat} {pool : List Nat}
    {gs : Array (List Nat)} {rs refs : Array Nat}
    (hg : ∀ p ∈ gs, Good k pool p)
    (hr : recipeCheck pw rw rb n gs.size rs = true)
    (ha : actionCheck fw fb count (n+1) refs = true) :
    ∀ p ∈ actions fw fb count refs (group k pw rw rb n gs rs), Good k pool p := by
  apply actions_preserves
  · exact group_preserves (Good k pool) k pw rw rb n gs rs (good_id k pool) hg
      (fun _ _ hp hq => good_comp hp hq) hr
  · simpa only [group_size] using ha

theorem array_all {α : Type} {n : Nat} {xs : Array α} {P : α → Prop} (d : α)
    (hs : xs.size = n) (h : ∀ i : Fin n, P (xs.getD i d)) : ∀ p ∈ xs, P p := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.1 hp
  have hh := h ⟨i, by omega⟩
  simpa [Array.getD, hi] using hh

def packedCheck (k pw rw rb n fw fb count : Nat) (pool : List Nat)
    (gs : Array (List Nat)) (q : Nat → List Nat) (rs refs : Array Nat) : Bool :=
  (List.range gs.size).all (fun i => Check k pool (gs.getD i []) (q i)) &&
  recipeCheck pw rw rb n gs.size rs && actionCheck fw fb count (n+1) refs

theorem checked_actions {k pw rw rb n fw fb count : Nat} {pool : List Nat}
    {gs : Array (List Nat)} {rs refs : Array Nat} (q : Nat → List Nat)
    (hc : packedCheck k pw rw rb n fw fb count pool gs q rs refs = true) :
    ∀ p ∈ actions fw fb count refs (group k pw rw rb n gs rs), Good k pool p := by
  simp only [packedCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  apply good_actions
  · exact array_all (xs := gs) (P := Good k pool) [] rfl
      (fun i => check_good (hc.1.1 i i.2))
  · exact hc.1.2
  · exact hc.2

def word (k n : Nat) (ps : Array (List Nat)) (g : Nat) : Nat → Nat :=
  if g % n = 0 then id else fastHalfPerm k (ps.getD (g % n) [])

theorem word_run {k n : Nat} {pool : List Nat} {ps : Array (List Nat)}
    (hn : 0 < n) (hs : ps.size = n) (hp : ∀ p ∈ ps, Good k pool p)
    (g : Nat) {u : Nat} {ws : List Nat}
    (h : RNatRun pool (Live.mask k) (Live.goal k) u ws) :
    RNatRun pool (Live.mask k) (Live.goal k) u (ws.map (word k n ps g)) := by
  unfold word
  split
  · simpa only [List.map_id] using h
  · exact (hp _ (array_getD_mem _ [] (by rw [hs]; exact Nat.mod_lt _ hn))).2.2 h

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

end PEqualNP.Outside.L_meta_982_aux.Finite.Symmetry
