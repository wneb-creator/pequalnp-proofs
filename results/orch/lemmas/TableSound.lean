import PEqualNP.Defs

-- The live-set search and its completeness proof are adapted from
-- lean/PEqualNP/Outside/L_meta_6345.lean in this repository, widened from 64 to 36
-- (true entry, false entry) pairs; the rows, the 10-gate search and the conclusion are new.

namespace PEqualNP.Outside.L_meta_9502.TableSound

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

theorem compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

theorem live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

theorem live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

theorem first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

abbrev W := BitVec 72

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 36 := ((x >>> 36) &&& ~~~x).setWidth 36

def cuts (ws : List W) : BitVec 36 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 36) ++ (0 : BitVec 36)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [0x3f0c30c30c3, 0x3ffc0104104104, 0x3ffc0000208208208, 0xfc0000000c30c30c30, 0xfff618618618, 0xfff000861861861, 0xfff000000186186186]

def inputs : List W := rawInputs

theorem pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

abbrev basicOps (a b : W) : Finset W := (ops a b).toFinset

def differs (i : Fin 36) (w : W) : Prop :=
  w.getLsbD (36 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 36) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (36 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (36 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 36, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 36) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 72 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 36)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, BitVec.and_comm, BitVec.or_comm]

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

theorem singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def checkEntry (known : ℕ → List W → Bool) (n : ℕ) (ws : List W) : Bool :=
  decide ws.Nodup && !(ws == [goal]) && match n with
  | 0 => true
  | k + 1 => (pairs ws).all fun (a, b, r) => (ops a b).all fun z =>
      ws.contains z || (keepChoices a b r).all fun kept =>
        !(decide (kept.length ≤ k)) || !(cuts (z :: kept) == -1) || known k (z :: kept)

lemma checkEntry_step {known : ℕ → List W → Bool} {k : ℕ}
    {ws : List W} {a b z : W} {r : List W} {needed : Finset W}
    (hc : checkEntry known (k + 1) ws = true)
    (hp : (a, b, r) ∈ pairs ws) (hperm : ws.Perm (a :: b :: r))
    (hz : z ∈ basicOps a b) (hzout : z ∉ ws.toFinset)
    (hs : ws.toFinset = insert a (insert b needed))
    (hl : live basicOps goal k (insert z needed)) :
    ∃ kept : List W, known k (z :: kept) = true ∧ (z :: kept).toFinset = insert z needed := by
  have hparts := Bool.and_eq_true_iff.mp hc
  have hn : ws.Nodup := of_decide_eq_true (Bool.and_eq_true_iff.mp hparts.1).1
  obtain ⟨kept, hmem, hkn, hkept⟩ := recover_kept hperm hn hs
  have hzkept : z ∉ kept := by
    intro hh
    apply hzout
    rw [hs]
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hkept ▸ List.mem_toFinset.mpr hh))
  have hnnext : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hzkept, hkn⟩
  have hnext : (z :: kept).toFinset = insert z needed := by simp [hkept]
  have hlive : live basicOps goal k (z :: kept).toFinset := hnext.symm ▸ hl
  have hcard := live_card hlive
  rw [List.toFinset_card_of_nodup hnnext] at hcard
  have hlen : kept.length ≤ k := by simp only [List.length_cons] at hcard; omega
  have hcuts := cuts_full hlive
  have hcontains : ws.contains z = false := by simpa using hzout
  have hcheck : (pairs ws).all (fun (a, b, r) => (ops a b).all fun z =>
      ws.contains z || (keepChoices a b r).all fun kept =>
        !(decide (kept.length ≤ k)) || !(cuts (z :: kept) == -1) || known k (z :: kept)) = true := hparts.2
  have hpair := List.all_eq_true.mp hcheck (a, b, r) hp
  have hop := List.all_eq_true.mp hpair z (List.mem_toFinset.mp hz)
  simp only [hcontains, Bool.false_or] at hop
  have hbranch := List.all_eq_true.mp hop kept hmem
  refine ⟨kept, ?_, hnext⟩
  simpa [hlen, hcuts] using hbranch

lemma known_no_live (known : ℕ → List W → Bool)
    (lookup_canon : ∀ n ws, known n ws = true →
      ∃ canon, canon.toFinset = ws.toFinset ∧ checkEntry known n canon = true)
    {n : ℕ} {ws : List W} (hk : known n ws = true) :
    ¬ live basicOps goal n ws.toFinset := by
  induction n generalizing ws with
  | zero =>
    obtain ⟨canon, heq, hc⟩ := lookup_canon 0 ws hk
    have hparts := Bool.and_eq_true_iff.mp hc
    have hn : canon.Nodup := of_decide_eq_true (Bool.and_eq_true_iff.mp hparts.1).1
    have hnot : canon ≠ [goal] := by simpa using (Bool.and_eq_true_iff.mp hparts.1).2
    intro hl
    apply hnot
    apply singleton_list hn
    exact heq.trans hl
  | succ k ih =>
    obtain ⟨canon, heq, hc⟩ := lookup_canon (k + 1) ws hk
    have hparts := Bool.and_eq_true_iff.mp hc
    have hn : canon.Nodup := of_decide_eq_true (Bool.and_eq_true_iff.mp hparts.1).1
    have hnot : canon ≠ [goal] := by simpa using (Bool.and_eq_true_iff.mp hparts.1).2
    intro hl
    have hlc : live basicOps goal (k + 1) canon.toFinset := heq.symm ▸ hl
    rcases first_live hlc with hdone | ⟨a, ha, b, hb, hab, z, hz, hzout, needed, hs, hnext⟩
    · exact hnot (singleton_list hn hdone)
    · obtain ⟨r, hp, hperm⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      rcases hp with hp | hp
      · obtain ⟨kept, hknown, hkept⟩ := checkEntry_step hc hp hperm hz hzout hs hnext
        exact ih hknown (hkept.symm ▸ hnext)
      · have hperm' : canon.Perm (b :: a :: r) := hperm.trans (List.Perm.swap b a r)
        have hz' : z ∈ basicOps b a := by rw [ops_swap]; exact hz
        have hs' : canon.toFinset = insert b (insert a needed) := by rw [Finset.insert_comm]; exact hs
        obtain ⟨kept, hknown, hkept⟩ := checkEntry_step hc hp hperm' hz' hzout hs' hnext
        exact ih hknown (hkept.symm ▸ hnext)


def tableKnown (table : Array ℕ) (budget : ℕ → ℕ) (decode : ℕ → List W)
    (choose : ℕ → List W → ℕ) (n : ℕ) (ws : List W) : Bool :=
  if h : choose n ws < table.size then
    decide (budget table[choose n ws] = n) &&
      decide ((decode table[choose n ws]).toFinset = ws.toFinset)
  else false

lemma table_lookup_canon (table : Array ℕ) (budget : ℕ → ℕ) (decode : ℕ → List W)
    (choose : ℕ → List W → ℕ)
    (hall : ∀ i (hi : i < table.size),
      checkEntry (tableKnown table budget decode choose) (budget table[i]) (decode table[i]) = true)
    (n : ℕ) (ws : List W) (hk : tableKnown table budget decode choose n ws = true) :
    ∃ canon, canon.toFinset = ws.toFinset ∧
      checkEntry (tableKnown table budget decode choose) n canon = true := by
  unfold tableKnown at hk
  split at hk
  next h =>
    have hp := Bool.and_eq_true_iff.mp hk
    have hb := of_decide_eq_true hp.1
    have hs := of_decide_eq_true hp.2
    refine ⟨decode table[choose n ws], hs, ?_⟩
    have hc := hall (choose n ws) h
    rw [hb] at hc
    exact hc
  next h => simp at hk

lemma table_no_live (table : Array ℕ) (budget : ℕ → ℕ) (decode : ℕ → List W)
    (choose : ℕ → List W → ℕ)
    (hall : ∀ i (hi : i < table.size),
      checkEntry (tableKnown table budget decode choose) (budget table[i]) (decode table[i]) = true)
    {n : ℕ} {ws : List W} (hk : tableKnown table budget decode choose n ws = true) :
    ¬ live basicOps goal n ws.toFinset :=
  known_no_live (tableKnown table budget decode choose)
    (table_lookup_canon table budget decode choose hall) hk

end PEqualNP.Outside.L_meta_9502.TableSound
