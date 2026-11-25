def q2_decode (m : Fin 128) : Finset (Fin 7) :=
  Finset.univ.filter (fun t => q2_bit m t = true)

def q2_sum (S : Finset (Fin 7)) : ℕ := S.sum (fun i => 2^i.val)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_sum_bound : ∀ S : Finset (Fin 7), q2_sum S < 128 := by decide +kernel

def q2_encode (S : Finset (Fin 7)) : Fin 128 := ⟨q2_sum S,q2_sum_bound S⟩

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_encode_decode : ∀ m : Fin 128, q2_encode (q2_decode m) = m := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_decode_encode : ∀ S : Finset (Fin 7), q2_decode (q2_encode S) = S := by decide +kernel

def q2_super (s : Fin 15) : Fin 128 := ![99,102,103,106,107,110,111,114,115,118,119,122,123,126,127] s

def q2_small (k : Fin 29) : Fin 128 := ![0,1,2,3,4,5,6,8,9,10,12,16,17,18,20,24,32,33,34,36,40,48,64,65,66,68,72,80,96] k

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_super_complete : ∀ m : Fin 128, q2_decode 98 ⊂ q2_decode m →
    ∃ s : Fin 15, q2_super s = m := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_small_complete : ∀ m : Fin 128, (q2_decode m).card ≤ 2 →
    ∃ k : Fin 29, q2_small k = m := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_small_unit : ∀ c : Fin 34, ∀ k : Fin 29,
    q2_unit c ⟨k.val, by omega⟩ = q2_small k := by decide +kernel

lemma q2_unit_complete (c : Fin 34) (U : Finset (Fin 7))
    (h : U.card ≤ 2 ∨ U = q2_decode 11 ∨ U = q2_decode 69 ∨
      U = q2_decode 49 ∨ U = q2_decode (q2_ctx c 0)) :
    ∃ k : Fin 33, q2_decode (q2_unit c k) = U := by
  rcases h with h|h|h|h|h
  · obtain ⟨k,hk⟩ := q2_small_complete (q2_encode U) (by simpa only [q2_decode_encode] using h)
    refine ⟨⟨k.val,by omega⟩, ?_⟩
    rw [q2_small_unit, hk, q2_decode_encode]
  · exact ⟨29,h.symm⟩
  · exact ⟨30,h.symm⟩
  · exact ⟨31,h.symm⟩
  · exact ⟨32,h.symm⟩

def q2_choices (s : Fin 15) (a b d : Fin 2) : Fin 4 → Fin 128 :=
  ![if a = 0 then 11 else q2_super s, if b = 0 then 69 else q2_super s,
    q2_super s, if d = 0 then 49 else q2_super s]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_context_complete : ∀ s : Fin 15, ∀ a b d : Fin 2,
    (∀ i : Fin 4, q2_decode (q2_nb i) ⊆ q2_decode (q2_choices s a b d i)) →
      ∃ c : Fin 34, q2_ctx c 0 = q2_super s ∧
        ∀ i : Fin 4, q2_ctx c i.succ = q2_choices s a b d i := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma q2_required_choices : ∀ i : Fin 3, ∀ j : Fin 3,
    q2_decode (![11,69,49] i) ⊆ q2_decode (![11,69,49] j) → i = j := by decide +kernel

lemma q2_bit_mem (m : Fin 128) (t : Fin 7) :
    q2_bit m t = true ↔ t ∈ q2_decode m := by simp [q2_decode]

def q2_res (u v w : Fin 128) (t : Fin 7) : Finset (Fin 3) :=
  Finset.univ.filter (fun j => (![q2_bit u t,q2_bit v t,q2_bit w t] j) = true)

lemma q2_count_card (u v w : Fin 128) (t : Fin 7) :
    q2_count u v w t = (q2_res u v w t).card := by
  have h : ∀ a b d : Bool, a.toNat+b.toNat+d.toNat =
      (Finset.univ.filter (fun j : Fin 3 => (![a,b,d] j) = true)).card := by decide +kernel
  exact h (q2_bit u t) (q2_bit v t) (q2_bit w t)

lemma q2_sub_iff (u v w : Fin 128) (x t : Fin 7) :
    q2_sub u v w x t = true ↔ q2_res u v w x ⊆ q2_res u v w t := by
  have h : ∀ a b d e f g : Bool,
      ((!a || e) && (!b || f) && (!d || g)) = true ↔
      (Finset.univ.filter (fun j : Fin 3 => (![a,b,d] j) = true)) ⊆
      (Finset.univ.filter (fun j : Fin 3 => (![e,f,g] j) = true)) := by decide +kernel
  exact h (q2_bit u x) (q2_bit v x) (q2_bit w x)
    (q2_bit u t) (q2_bit v t) (q2_bit w t)

lemma q2_empty_iff (u v w : Fin 128) (x : Fin 7) :
    q2_empty u v w x = true ↔ q2_res u v w x = ∅ := by
  have h : ∀ a b d : Bool, (!a && !b && !d) = true ↔
      (Finset.univ.filter (fun j : Fin 3 => (![a,b,d] j) = true)) = ∅ := by decide +kernel
  exact h (q2_bit u x) (q2_bit v x) (q2_bit w x)
