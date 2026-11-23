import LinearSymmetry

namespace PEqualNP.Outside.L_meta_982_aux.Finite.Symmetry.Radix
open Checkpoint

def step (bit : Nat) (p : List Nat) : List Nat :=
  p.filter (fun j => !(Fast.bit j bit)) ++ p.filter (fun j => Fast.bit j bit)

def sort : Nat → List Nat → List Nat
  | 0, p => p
  | b+1, p => step b (sort b p)

theorem mem_step (bit j : Nat) (p : List Nat) : j ∈ step bit p ↔ j ∈ p := by
  simp only [step, List.mem_append, List.mem_filter]
  cases hb : Fast.bit j bit <;> simp [hb]

theorem mem_sort (bits j : Nat) (p : List Nat) : j ∈ sort bits p ↔ j ∈ p := by
  induction bits with
  | zero => rfl
  | succ b ih => simpa only [sort, mem_step] using ih

def Check (k bits : Nat) (pool p : List Nat) : Bool :=
  decide (p.length = k+k) && decide (sort bits p = List.range (k+k)) &&
  p.zipIdx.all (fun (s,j) => decide (k ≤ s ↔ k ≤ j)) &&
  pool.all (fun a => (pool.map (Masked.fast (k+k) p)).contains a)

theorem check_good {k bits : Nat} {pool p : List Nat}
    (hc : Check k bits pool p = true) : Full.Good k pool p := by
  simp only [Check, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hc
  obtain ⟨⟨⟨hl,hs⟩,hh⟩,hf⟩ := hc
  have hm : ∀ j, j ∈ p ↔ j < k+k := by
    intro j
    rw [←mem_sort bits j p, hs, List.mem_range]
  have hp : ∀ j < k+k, p.getD j 0 < k+k := by
    intro j hj
    exact (hm _).1 (Linear.getD_mem (by omega))
  have hq : ∀ j < k+k, p.idxOf j < k+k := by
    intro j hj
    have he := List.idxOf_lt_length_of_mem ((hm j).2 hj)
    omega
  have hi : ∀ j < k+k, p.getD (p.idxOf j) 0 = j := by
    intro j hj
    have he : p.idxOf j < p.length := by simpa [hl] using hq j hj
    rw [List.getD_eq_getElem p 0 he, List.getElem_idxOf he]
  have ht : ∀ j < k+k, k ≤ p.getD j 0 ↔ k ≤ j :=
    fun j hj => hh _ (Linear.zip_mem (by omega))
  refine ⟨hl, hp, ht, ?_⟩
  intro s ws h
  have he : Masked.fast (k+k) p = permWord (k+k) (p.getD · 0) := by
    funext x
    rw [Masked.fast_eq hl, Full.fast_eq hl]
  have hfp : pool.Subset (pool.map (permWord (k+k) (p.getD · 0))) := by
    intro a ha
    have hx := hf a ha
    rw [he] at hx
    simpa using hx
  have hf' : Full.fast (k+k) p = permWord (k+k) (p.getD · 0) := funext (Full.fast_eq hl)
  rw [hf']
  apply run_map (permWord (k+k) (p.getD · 0))
    (permWord_injective (k+k) (p.getD · 0) p.idxOf hq hi) _
    (permWord_and _ _) (permWord_or _ _) (permWord_halfGoal k _ hp ht) hfp h
  intro a
  change permWord (k+k) (p.getD · 0) (a ^^^ (2^(k+k)-1)) = _
  rw [permWord_xor, permWord_mask _ _ hp]
  rfl

def packedCheck (k bits pw rw rb n fw fb count : Nat) (pool : List Nat)
    (gs : Array (List Nat)) (rs refs : Array Nat) : Bool :=
  (List.range gs.size).all (fun i => Check k bits pool (gs.getD i [])) &&
  recipeCheck pw rw rb n gs.size rs && actionCheck fw fb count (n+1) refs

theorem checked_actions {k bits pw rw rb n fw fb count : Nat} {pool : List Nat}
    {gs : Array (List Nat)} {rs refs : Array Nat}
    (hc : packedCheck k bits pw rw rb n fw fb count pool gs rs refs = true) :
    ∀ p ∈ actions fw fb count refs (group (k+k) pw rw rb n gs rs), Full.Good k pool p := by
  simp only [packedCheck, Bool.and_eq_true, List.all_eq_true, List.mem_range] at hc
  apply actions_preserves
  · exact group_preserves (Full.Good k pool) (k+k) pw rw rb n gs rs (Full.good_id k pool)
      (array_all (xs := gs) (P := Full.Good k pool) [] rfl (fun i => check_good (hc.1.1 i i.2)))
      (fun _ _ hp hq => Full.good_comp hp hq) hc.1.2
  · simpa only [group_size] using hc.2

end PEqualNP.Outside.L_meta_982_aux.Finite.Symmetry.Radix
