import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17727_aux
abbrev Group (n : Nat) := Fin n × List (Fin n)
def val {n : Nat} (s : Nat) (g : Group n) : Bool :=
  s.testBit g.1.val && g.2.any fun j => s.testBit j.val
def eval {n : Nat} (gs : List (Group n)) (s : Nat) := gs.any (val s)
def cost {n : Nat} (gs : List (Group n)) := (gs.map fun g => g.2.length+1).sum
def misses {n : Nat} (gs : List (Group n)) (samples : List Nat) :=
  (samples.filter fun s => !eval gs s).length

theorem split_misses {n : Nat} (gs : List (Group n)) {a b src : List Nat}
    (part : (a++b).Perm src) : misses gs a + misses gs b = misses gs src := by
  simpa only [misses,List.filter_append,List.length_append] using
    (part.filter (fun s => !eval gs s)).length_eq

theorem assign {n : Nat} (pos neg : List Nat)
    (apart : ∀ u∈pos, u∉neg)
    (isolate : ∀ u ∈ pos, ∀ j : Fin n, u.testBit j.val = true →
      ∃ k : Fin n, ∀ s∈pos++neg, (s.testBit j.val && s.testBit k.val) = decide (s=u))
    (keys : List (Fin n)) :
    ∀ (src : List Nat), (∀ s∈src, s∈pos) → (∀ s∈src, ∃ j∈keys, s.testBit j.val=true) →
    ∃ gs : List (Group n), (∀ g∈gs, 2≤g.2.length) ∧
      cost gs + 2*misses gs src ≤ src.length+keys.length ∧ ∀ s∈neg, eval gs s = false := by
  classical
  induction keys with
  | nil =>
    intro src _ cover
    have empty : src=[] := by
      cases src with
      | nil => rfl
      | cons u us => simpa using cover u List.mem_cons_self
    subst src
    exact ⟨[],by simp,by simp [cost,misses],by simp [eval]⟩
  | cons j ks ih =>
    intro src sub cover
    let hit := src.filter fun s => s.testBit j.val
    let rest := src.filter fun s => !s.testBit j.val
    have part : (hit++rest).Perm src := List.filter_append_perm _ _
    have sizes := part.length_eq
    rw [List.length_append] at sizes
    obtain ⟨gs,wide,budget,noNeg⟩ := ih rest
      (fun s hs => sub s (List.mem_filter.mp hs).1) (by
        intro s hs
        obtain ⟨m,hm,bit⟩ := cover s (List.mem_filter.mp hs).1
        rcases List.mem_cons.mp hm with rfl | hm
        · have := (List.mem_filter.mp hs).2
          simp [bit] at this
        · exact ⟨m,hm,bit⟩)
    change cost gs + 2*misses gs rest ≤ rest.length+ks.length at budget
    by_cases large : 2≤hit.length
    · let partner (u : Nat) := if h : u∈hit then Classical.choose
          (isolate u (sub u (List.mem_filter.mp h).1) j (List.mem_filter.mp h).2) else j
      have spec (u : Nat) (h : u∈hit) : ∀ s∈pos++neg,
          (s.testBit j.val && s.testBit (partner u).val) = decide (s=u) := by
        simp only [partner,dif_pos h]
        exact Classical.choose_spec (isolate u (sub u (List.mem_filter.mp h).1) j (List.mem_filter.mp h).2)
      let g : Group n := (j,hit.map partner)
      have costEq : cost (g::gs) = hit.length+1+cost gs := by simp [cost,g]
      have covered (s : Nat) (hs : s∈hit) : eval (g::gs) s = true := by
        have h := spec s hs s (List.mem_append_left _ (sub s (List.mem_filter.mp hs).1))
        simp only [decide_true,Bool.and_eq_true] at h
        have right : (hit.map partner).any (fun k => s.testBit k.val) = true :=
          List.any_eq_true.mpr ⟨_,List.mem_map_of_mem hs,h.2⟩
        simp [eval,val,g,h.1,right]
      have free : misses (g::gs) hit = 0 := by
        have z : (hit.filter fun s => !eval (g::gs) s)=[] := by
          apply List.filter_eq_nil_iff.mpr
          intro s hs
          simp [covered s hs]
        simp [misses,z]
      have same : misses (g::gs) rest = misses gs rest := by
        unfold misses
        congr 1
        apply List.filter_congr
        intro s hs
        have hz : s.testBit j.val = false := by simpa using (List.mem_filter.mp hs).2
        simp [eval,val,g,hz]
      refine ⟨g::gs,?_,?_,?_⟩
      · intro t ht
        rcases List.mem_cons.mp ht with rfl | ht
        · simpa [g] using large
        · exact wide _ ht
      · have hh := split_misses (g::gs) part
        rw [free,same] at hh
        rw [costEq,List.length_cons]
        omega
      · intro s hs
        have h : val s g = false := by
          apply Bool.eq_false_iff.mpr
          intro yes
          change (_ && _) = true at yes
          simp only [Bool.and_eq_true] at yes
          obtain ⟨hj,hk⟩ := yes
          obtain ⟨k,hkm,hbit⟩ := List.any_eq_true.mp hk
          obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hkm
          change s.testBit j.val = true at hj
          have h := spec u hu s (List.mem_append_right _ hs)
          have eq : s=u := of_decide_eq_true (by rw [← h,hj,hbit]; rfl)
          exact apart u (sub _ (List.mem_filter.mp hu).1) (eq ▸ hs)
        change (val s g || eval gs s) = false
        rw [h,noNeg s hs]; rfl
    · refine ⟨gs,wide,?_,noNeg⟩
      have h := split_misses gs part
      have le : misses gs hit≤hit.length := List.length_filter_le _ _
      rw [List.length_cons]
      omega

end PEqualNP.Outside.L_meta_17727_aux

open PEqualNP.Outside.L_meta_17727_aux in
theorem PEqualNP.Outside.L_meta_17727 : ∀ (x1 : ℕ) (x2 x3 : List ℕ) (x4 : Finset (Fin x1)),   (∀ x5 ∈ x2, x5 ∉ x3) →     (∀ x6 ∈ x2, ∃ x8 ∈ x4, x6.testBit ↑x8 = Bool.true) →       (∀ x7 ∈ x2, ∀ (x9 : Fin x1), x7.testBit ↑x9 = Bool.true → ∃ (x11 : Fin x1), ∀ x12 ∈ x2 ++ x3, (x12.testBit ↑x9 && x12.testBit ↑x11) = Decidable.decide (x12 = x7)) →         ∃ (x8 : List (Fin x1 × List (Fin x1))),           (∀ x9 ∈ x8, (2 : ℕ) ≤ x9.2.length) ∧             have x9 : ℕ → Bool := fun (x9 : ℕ) => x8.any fun (x10 : Fin x1 × List (Fin x1)) => x9.testBit ↑x10.1 && x10.2.any fun (x11 : Fin x1) => x9.testBit ↑x11;             (List.map (fun (x10 : Fin x1 × List (Fin x1)) => x10.2.length + (1 : ℕ)) x8).sum + (2 : ℕ) * (List.filter (fun (x10 : ℕ) => !x9 x10) x2).length ≤ x2.length + x4.card ∧ ∀ x10 ∈ x3, x9 x10 = Bool.false := by
  intro n pos neg keys apart covered isolate
  obtain ⟨gs,wide,budget,noNeg⟩ := assign pos neg apart isolate keys.toList pos (fun _ h => h)
    (fun s hs => by simpa using covered s hs)
  refine ⟨gs,wide,?_,noNeg⟩
  change cost gs + 2*misses gs pos ≤ pos.length + keys.card
  rwa [Finset.length_toList] at budget
