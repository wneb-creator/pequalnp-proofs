import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1423_aux

-- The live-wire compression argument follows the project proof of L-meta-703.
-- The live-wire reduction and circuit semantics follow the merged L-meta-1429.
-- Each finite search layer below is checked against the next layer of smaller states.
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

-- The upper and lower halves represent opposite target labels on 30 pairs of assignments.
abbrev W := BitVec 60
-- Free complementation leaves four binary choices up to output polarity.
def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 30 := ((x >>> 30) ^^^ x).setWidth 30
def cuts (ws : List W) : BitVec 30 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 30) ++ (0 : BitVec 30)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

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

def differs (i : Fin 30) (w : W) : Prop :=
  w.getLsbD (30+i.val) ≠ w.getLsbD i.val

theorem ops_differs (i : Fin 30) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 30+i.val < 60 := by omega
  have hi' : i.val < 60 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

theorem cuts_spec (ws : List W) (i : Fin 30) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

theorem cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 30)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

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

theorem singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def insertW (v : W) : List W → List W
  | [] => [v]
  | x :: xs => if v ≤ x then v :: x :: xs else x :: insertW v xs

def ordered (ws : List W) := ws.foldr insertW []

theorem insertW_perm (v : W) (ws : List W) : (insertW v ws).Perm (v :: ws) := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih =>
    simp only [insertW]
    split
    · exact .refl _
    · exact (ih.cons x).trans (.swap _ _ _)

theorem ordered_perm (ws : List W) : (ordered ws).Perm ws := by
  induction ws with
  | nil => exact .refl _
  | cons x xs ih => exact (insertW_perm x (ordered xs)).trans (ih.cons x)

def children (k : ℕ) (ws : List W) : List (List W) := (pairs ws).flatMap fun (a,b,r) =>
  (ops a b).flatMap fun z =>
    (keepChoices a b r).filterMap fun kept =>
      if kept.length ≤ k ∧ cuts (z :: kept) = -1 then some (ordered (z :: kept)) else none

def earlier : List W → List W → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: l, b :: r => if a = b then earlier l r else decide (a.toNat < b.toNat)

def containsKey (q : List W) : BinaryTree (List W) → Bool
  | .nil => false
  | .node a l r => if q = a then true else if earlier q a then containsKey q l else containsKey q r

def everyKey (f : List W → Bool) : BinaryTree (List W) → Bool
  | .nil => true
  | .node a l r => f a && everyKey f l && everyKey f r

theorem every_at {f : List W → Bool} {q : List W} (tr : BinaryTree (List W))
    (ha : everyKey f tr = true) (hm : containsKey q tr = true) : f q = true := by
  induction tr with
  | nil => contradiction
  | node a l r il ir =>
    simp only [everyKey,Bool.and_eq_true] at ha
    simp only [containsKey] at hm
    split at hm
    next e => simpa [e] using ha.1.1
    next e =>
      split at hm
      · exact il ha.1.2 hm
      · exact ir ha.2 hm

def Closed (k : Nat) (tr : BinaryTree (List W)) : Prop :=
  ∀ (g : W), g = goal ∨ g = ~~~goal → ∀ ws : List W,
    ws.Nodup → ws.length ≤ 9 → containsKey ws tr = true → ¬ live basicOps g k ws.toFinset

def doneTest (s : List W) : Bool := s == [goal] || s == [~~~goal]

theorem closed_nil (tr : BinaryTree (List W)) (hc : everyKey (fun q => !doneTest q) tr = true) :
    Closed 0 tr := by
  intro g hg ws hn hl hm h
  have hy := every_at tr hc hm
  have eq := singleton_list hn h
  rcases hg with rfl | rfl <;> simp [eq,doneTest] at hy

def rowOK (k : Nat) (tr : BinaryTree (List W)) (ws : List W) :=
  !doneTest ws && (children k ws).all (fun child => containsKey child tr)

theorem perm_set {u v : List W} (p : u.Perm v) : u.toFinset = v.toFinset := by
  ext a
  simpa only [List.mem_toFinset] using (p.mem_iff : a ∈ u ↔ a ∈ v)

theorem closed_next (k : Nat) (hk : k < 9) (tr next : BinaryTree (List W))
    (hnext : Closed k next) (hc : everyKey (rowOK k next) tr = true) :
    Closed (k+1) tr := by
  intro g hg ws hn hl hm h
  have hy := every_at tr hc hm
  simp only [rowOK,Bool.and_eq_true,List.all_eq_true] at hy
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · have eq := singleton_list hn done
    rcases hg with rfl | rfl <;> simp [eq,doneTest] at hy
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : W} (hp : ws.Perm (a :: b :: r)) (hmem : (a,b,r) ∈ pairs ws)
        (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) : False := by
      obtain ⟨kept, hkeep, hnk, hfin⟩ := recover_kept hp hn hset
      have hznew : z ∉ kept := by
        intro hu
        apply hout
        rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
      have hraw : live basicOps g k (z :: kept).toFinset := by simpa [hfin] using tail
      have hc := live_card hraw
      rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
      have hp' := ordered_perm (z :: kept)
      have mem : ordered (z :: kept) ∈ children k ws := by
        apply List.mem_flatMap.mpr
        refine ⟨(a,b,r),hmem,List.mem_flatMap.mpr ⟨z,List.mem_toFinset.mp hop,?_⟩⟩
        exact List.mem_filterMap.mpr ⟨kept,hkeep,by simp [show kept.length ≤ k by omega,cuts_full hg hraw]⟩
      have sz : (ordered (z :: kept)).length ≤ 9 := by rw [hp'.length_eq]; simp only [List.length_cons]; omega
      apply hnext g hg _ (hp'.nodup_iff.mpr hnd) sz (hy.2 _ mem)
      rwa [perm_set hp']
    rcases hm with direct | swap
    · exact go hp direct hs hz
    · exact go (hp.trans (.swap _ _ _)) swap (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)

def startOK (n : Nat) (tr : BinaryTree (List W)) (ws : List W) : Bool :=
  !(decide (ws.length ≤ n+1) && (cuts ws == -1)) || containsKey (ordered ws) tr

theorem no_build (n : Nat) (tr : BinaryTree (List W)) (ins : List W) (nd : ins.Nodup)
    (small : ins.length ≤ 9) (hc : Closed n tr) (hi : ins.sublists.all (startOK n tr) = true)
    (g : W) (hg : g = goal ∨ g = ~~~goal) : ¬ build basicOps g n ins.toFinset := by
  intro hb
  classical
  obtain ⟨s,hs,hl⟩ := compress hb
  let ws := ins.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws,List.mem_toFinset,List.mem_filter,decide_eq_true_eq,and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd := nd.filter (fun u => decide (u ∈ s))
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have size := live_card hl'
  rw [List.toFinset_card_of_nodup (show ws.Nodup from hnd)] at size
  have sub : ws.Sublist ins := List.filter_sublist ..
  have key := List.all_eq_true.mp hi ws (List.mem_sublists.mpr sub)
  have perm := ordered_perm ws
  apply hc g hg (ordered ws) (perm.nodup_iff.mpr hnd) (by rw [perm.length_eq]; exact sub.length_le.trans small) ?_
  · rwa [perm_set perm]
  · simpa [startOK,size,cuts_full hg hl'] using key

open PEqualNP.CircuitLowerBounds

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

theorem holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

theorem holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

theorem reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
theorem and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 60 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 60)
    rw [BitVec.and_allOnes]; exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : W) (hw : w ∈ basicOps a b) (z : W) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

theorem or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 60) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 60) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List W) (g : Gate) : W := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

set_option maxRecDepth 5000 in
theorem action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 60) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#60)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      BitVec.getElem_zero,bit0,Bool.not_false] <;> rfl

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

theorem available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
theorem gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : W, x ||| (0 : W) = x from fun x => BitVec.or_zero,
    show ∀ x : W, x &&& ~~~0 = x from fun x => BitVec.and_allOnes]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : goal ≠ 0) zero)
    · exact False.elim ((by decide : goal ≠ ~~~0) ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset W) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩
theorem bound_from_search (T n : ℕ) (ins : List W) (nd : ins.Nodup)
    (row : ∀ j : Fin 60, Nat.testBit T (∑ i : Fin 5, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 5) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z n ins.toFinset)
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0)) : n < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ ins, holds ins.toFinset u := fun u hu =>
    .inr (.inr ⟨u,List.mem_toFinset.mpr hu,.inl rfl⟩)
  have evaluate (k : Fin 60) :
      (gs.foldl step (ins.map (bit k))).getD o false = bit k goal := by
    let x (i : Fin 5) : Bool := bit k (ins.getD i.val 0)
    have same : List.ofFn x = ins.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < ins.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (ins.map (bit k)) = bit k goal
    rw [← same, he]
    exact row k
  obtain ⟨t,ht,run⟩ := compile gs o hg ins ins.toFinset init evaluate
  have lift {a b : ℕ} (h : a ≤ b) (hr : build basicOps t a ins.toFinset) : build basicOps t b ins.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact rejection t ht (lift low run)

theorem replace (T m : ℕ) (ins : List W) (nd : ins.Nodup)
    (row : ∀ j : Fin 60, Nat.testBit T (∑ i : Fin 5, if (ins.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val])
    (width : ins.length = 5) (rejection : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z (m-2) ins.toFinset)
    (upper : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ gs.length = m ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0))
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) =
      Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0)) :
    ∃ (ds : List Gate) (p : ℕ), (∀ g ∈ ds, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
      ∧ ds.length ≤ gs.length ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨ds,p⟩ (List.ofFn x) =
        Nat.testBit T (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  by_cases present : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g,hm,hn⟩ := present
    have cut : binaryCost gs < gs.length := (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr ⟨g,hm,by simp [isBinary, hn]⟩
    have b := bound_from_search T (m-2) ins nd row width rejection gs o hg he
    obtain ⟨ds,p,ok,size,ev⟩ := upper
    exact ⟨ds,p,ok,by omega,ev⟩
  · refine ⟨gs,o,?_,le_rfl,he⟩
    intro g hm
    obtain ⟨hop,cap⟩ := hg g hm
    exact ⟨hop.elim Or.inl (fun h => h.elim Or.inr (fun eq => (present ⟨g,hm,eq⟩).elim)),cap⟩

def v0 : W := 0x5ad468300a01804
def v1 : W := 0xb72f25fe089816e
def v2 : W := 0xedfbdfdcb566611
def v3 : W := 0xff34f32e00918ca
def v4 : W := 0x5a14f32200118c0
def v5 : W := 0x7fde68380a0980e
def v6 : W := 0x12cf2cf3c1b5eda
def v7 : W := 0x5ad5ff320a15fc4
def v8 : W := 0x7fde6839cf6980e
def v9 : W := 0x120525320810144
def v10 : W := 0xedfbdfdc0004600
def v11 : W := 0xff34f32f74d38cb
def v12 : W := 0x7fd468394e4180e
def v13 : W := 0x5ad468314a0980e
def v14 : W := 0x7f14f32b44518ca
def v15 : W := 0x5a14f32340918ca
def v16 : W := 0x5ad4fb320a118c4
def v17 : W := 0x7f146029444180a
def v18 : W := 0x5ad4fb2202118c0
def v19 : W := 0x5ad4fa300a01884
def v20 : W := 0x5ad4fa22bdfe77f
def v21 : W := 0x5ad4fb3200118c0
def v22 : W := 0x5ad4fb300a01804
def v23 : W := 0x9225b7e57a0fe1f
def v24 : W := 0x80ea9b16bbba0c5
def v25 : W := 0x5ad5ff320814744
def v26 : W := 0xa52b05dc0000000
def v27 : W := 0xa5e10c1d7ec670f
def v28 : W := 0xcb0cd08b24714
def v29 : W := 0xc10c100a04704
def v30 : W := 0x1970200147c0
def v31 : W := 0xcb0cd00a0c724
def v32 : W := 0xca08108b28004
def v33 : W := 0x8020930630920c1
def v34 : W := 0xa520000d74c200b
def v35 : W := 0xcb0c108b2c704
def v36 : W := 0xcb0cd0892c734
def v37 : W := 0xcb0cd08124610
def v38 : W := 0x1204202340918ca
def v39 : W := 0x250a0009c56800a
def v40 : W := 0x120420220a999ee
def v41 : W := 0x120420214a0980e
def v42 : W := 0x802197c43006611
def v43 : W := 0xcb0cd08b2c614
def v44 : W := 0x12042022089816e
def v45 : W := 0x48d0da00b566611
def v46 : W := 0x12ce2831cb2980e
def v47 : W := 0xfffffffe0a9dfee
def v48 : W := 0x48d0da000205e80
def v49 : W := 0x37ce28388b2800e
def v50 : W := 0x370e2038080800e
def v51 : W := 0xffff6dffcff996e
def v52 : W := 0x48d0da01f567e91
def v53 : W := 0x48d0da00b767e91
def v54 : W := 0x5ad46821cf6980e
def v55 : W := 0x48d1df100004600
def v56 : W := 0x5a14f22374d38cb
def v57 : W := 0xa52a00ccb562011
def v58 : W := 0xfff5ff3f7ed7fcf
def v59 : W := 0x5a14f32374538c1
def v60 : W := 0x5ad46831cf61804
def v61 : W := 0x7fdfff3bcf7dfce
def v62 : W := 0x5ad4fb220215ec0
def v63 : W := 0x5ad4fa300a05e84
def v64 : W := 0x5ad4fa220a15fc4
def v65 : W := 0x5ad5ff300a05e04
def v66 : W := 0x48d0da01f767e11
def v67 : W := 0xfffffffebdfe77f
def v68 : W := 0x7fd46829c76180a
def v69 : W := 0xfffefb3ffffb8cf
def v70 : W := 0x5ade68308b29804
def v71 : W := 0x6dda48188560000
def v72 : W := 0xfffffffdff6fe1f
def v73 : W := 0x7f14f229744388b
def v74 : W := 0x7fde68388f61804
def v75 : W := 0x7fde68388d6800e
def v76 : W := 0x9224b32770938cb
def v77 : W := 0x7fde6839c56180a
def v78 : W := 0xed30d30c3442001
def v79 : W := 0xfffffffff5f7edb
def v80 : W := 0xb72f25fe009004a
def v81 : W := 0xb724b32e30920cb
def v82 : W := 0xb724212e009004a
def v83 : W := 0xff3ff7ff7cdb9ef
def v84 : W := 0xb72f25fc080800e
def v85 : W := 0xda34f32630938c1
def v86 : W := 0xb72f25fe0810144
def v87 : W := 0xff34f32d744380b
def v88 : W := 0xff34f32e34d204b
def v89 : W := 0xff34f32e34538c1
def v90 : W := 0x802197c63096771
def v91 : W := 0xfffefb3ff5f38cb
def v92 : W := 0xff3ef3eff5f38db
def v93 : W := 0xff3ef32ff5fb8cb
def v94 : W := 0xff35f7ef74d39eb
def v95 : W := 0xff3ef3ef74db8eb
def v96 : W := 0xfff4fb2ff7f38cb
def v97 : W := 0xff3ff7ff74d38cb
def v98 : W := 0x802197c600947e0
def v99 : W := 0x7fdf6cf9cf6992e
def v100 : W := 0x7fdefa39ff6b88f
def v101 : W := 0x8021970630967c1
def v102 : W := 0x802197c630966d1
def v103 : W := 0x802197c630167d1
def v104 : W := 0xa52a000df5ea00b
def v105 : W := 0xfffefb3dff6b80f
def v106 : W := 0xfffe68fdcfe982e
def v107 : W := 0xfffe683dffeb80f
def v108 : W := 0xfffe68fdff6b81f
def v109 : W := 0x5adffff20a1dfe4
def v110 : W := 0xffff6dfdcf6980e
def v111 : W := 0xa52a00cdf5e201b
def v112 : W := 0xa52a00cdf56a01b
def v113 : W := 0xa52a00ccb5ea03b
def v114 : W := 0xfffffffe0a15fc4
def v115 : W := 0xdaf5fff60a95fe4
def v116 : W := 0x5ad5ff320015ec0
def v117 : W := 0xb04d00808124
def v118 : W := 0x120420220a119c4
def v119 : W := 0x4810d2017443881
def v120 : W := 0x48d04801c761800
def v121 : W := 0x802105c60090160
def v122 : W := 0xa52a00cc008802a
def v123 : W := 0xfffffffebf77fd5
def v124 : W := 0xcc77ed0721cfb4
def v125 : W := 0x6e5fffa40933e08
def v126 : W := 0xddedce5f57a7191
def v127 : W := 0xfbb3d859e8cf616
def v128 : W := 0xfbbab3fc36480e7
def v129 : W := 0x7ed69f743b5045c
def v130 : W := 0xbb2b63fc4089083
def v131 : W := 0xc5fdfc980026b20
def v132 : W := 0x7ed69f743a10050
def v133 : W := 0xc5fdfc9a0566f24
def v134 : W := 0xfffffffdfabfbf3
def v135 : W := 0x2f03d0bcdc0b42f
def v136 : W := 0x7ed69f742340444
def v137 : W := 0x81b968980004a00
def v138 : W := 0xf66ef7c1d8bb1b0
def v139 : W := 0x44d49c100140404
def v140 : W := 0xbbbb6bfc2204a40
def v141 : W := 0x3a920b742200040
def v142 : W := 0xc5fdfc980144e04
def v143 : W := 0x33930b5bdddde94
def v144 : W := 0xbbbb6bfc628dac3
def v145 : W := 0x7e46976667eb5e7
def v146 : W := 0xff6ff7fddcbb5bf
def v147 : W := 0x88b868b5e3eb5ec
def v148 : W := 0x94b8bb40be86eec
def v149 : W := 0xff6ff7fdd8bb1b3
def v150 : W := 0xd96d277d04b059f
def v151 : W := 0xff6ff7eddcbb1bb
def v152 : W := 0xff6ff7fddcbb1b3
def v153 : W := 0xff6ff7fdd8bb1bb
def v154 : W := 0xeafe2c26d96db0b
def v155 : W := 0x901003c040040f
def v156 : W := 0x501d0980402424
def v157 : W := 0xeffffcbedd6ff2f
def v158 : W := 0x191081a0544e04
def v159 : W := 0x32020341d899090
def v160 : W := 0x1014088c40b023
def v161 : W := 0x50d40f402350050
def v162 : W := 0x9008002204a40
def v163 : W := 0x40090009c0242c
def v164 : W := 0x90b82b402284ac0
def v165 : W := 0x901003c0000003
def v166 : W := 0x8900834234044c
def v167 : W := 0x80286081c0ab1a0
def v168 : W := 0xd06c274100b0190
def v169 : W := 0xd01903c9c0242f
def v170 : W := 0x991083c2344e4f
def v171 : W := 0x90140bcc40b42f
def v172 : W := 0x991083e2744e4c
def v173 : W := 0x991083e2744e47
def v174 : W := 0x2a020024d80900b
def v175 : W := 0xc0fc2c020164b00
def v176 : W := 0x2602d080d80b020
def v177 : W := 0xd01d0bc040242f
def v178 : W := 0x2b03003cdc0940f
def v179 : W := 0x2f03d0bc440b427
def v180 : W := 0x2b0340bc440940f
def v181 : W := 0x2b0340bc4009003
def v182 : W := 0xd46cb74198b21b0
def v183 : W := 0xbfbbfbfcfe8feef
def v184 : W := 0x2f03903c1c0040f
def v185 : W := 0x2b0340bcd80900b
def v186 : W := 0x2b0340bcc40b023
def v187 : W := 0x2f03d0bc1c0242c
def v188 : W := 0xfffffffc7bddedf
def v189 : W := 0x3a02036462890c3
def v190 : W := 0x444494020562524
def v191 : W := 0x2f03d0bcd80b023
def v192 : W := 0x2f03d0bc580940f
def v193 : W := 0x3a020365fa990d3
def v194 : W := 0x3a0203647a990db
def v195 : W := 0x764697401810010
def v196 : W := 0xfefefff5fbfb5fc
def v197 : W := 0xfffffffe3f76f7c
def v198 : W := 0x444494021d7253c
def v199 : W := 0x2b0340acdc0b02b
def v200 : W := 0xf66ef7c040ab1a0
def v201 : W := 0xb22a63c04089080
def v202 : W := 0xfffffffe67effe7
def v203 : W := 0xc46cf4800022120
def v204 : W := 0xf7ffffdbddfffb4
def v205 : W := 0xf66eb74118b0190
def v206 : W := 0xd46cf7c100b21b0
def v207 : W := 0xf66ef7c01832130
def v208 : W := 0x81296089c0afba3
def v209 : W := 0xf76ff7c9dcbb1b3
def v210 : W := 0xf66ef7c05899090
def v211 : W := 0xfe6ef7e5d8bb1bb
def v212 : W := 0x444494019832130
def v213 : W := 0x3f03d3fddc9b4bf
def v214 : W := 0x8129608a44afba3
def v215 : W := 0x6f47d4bcdd5b43f
def v216 : W := 0xd0fc2f4023d4ad0
def v217 : W := 0xaf2bf0bddcab5af
def v218 : W := 0x6fd7dcbcdd4b42f
def v219 : W := 0x6f47d4bedd6b52f
def v220 : W := 0x7f47d7fcdc1b43f
def v221 : W := 0xbf2bf3fcdc8b4af
def v222 : W := 0xb2ba6bc0628dac0
def v223 : W := 0xf6feffc1fabfbf0
def v224 : W := 0xd0fc2f4223e4bc0
def v225 : W := 0xd0fc2f422374b50
def v226 : W := 0xd0fc2f4122b4bd0
def v227 : W := 0xef6ff4bcdc2b52f
def v228 : W := 0x6f47d4bddc3b53f
def v229 : W := 0x991083c2204a43
def v230 : W := 0x44449400195041c
def v231 : W := 0x3a0203643a10058
def v232 : W := 0x2e029034180040c
def v233 : W := 0x81296088408da83
def v234 : W := 0x7fd7dffcff5b47f
def v235 : W := 0x8129608a0426b20
def v236 : W := 0x7f3d6fa5f0c5ae8
def v237 : W := 0xb6e3dedd0b033b5
def v238 : W := 0xc9def37b043bc9a
def v239 : W := 0xfffffffcfffc547
def v240 : W := 0x6f5bb294fd6c405
def v241 : W := 0x97b45d78ded0546
def v242 : W := 0x3a3cecdc00f1b36
def v243 : W := 0x596599e821de7d0
def v244 : W := 0x775d3d37dc54f09
def v245 : W := 0xfdeffbec652a0eb
def v246 : W := 0x31cb5d7dee72ef
def v247 : W := 0xa796d7d39a135d4
def v248 : W := 0xc5c31323ff0e0c9
def v249 : W := 0xa796d7d39a030c4
def v250 : W := 0x5869282c65ec22b
def v251 : W := 0x3a3cecdc00e1226
def v252 : W := 0x775d3d37dc44209
def v253 : W := 0x88a2c2c823ab0e6
def v254 : W := 0x382ce8cc0020022
def v255 : W := 0xa796d7d000131d4
def v256 : W := 0xfef34e3821c9204
def v257 : W := 0x775d3d344450b09
def v258 : W := 0xfef34e3bbbcd204
def v259 : W := 0x2f34151bb938522
def v260 : W := 0xfce34a282108000
def v261 : W := 0x6255c4f0651911d
def v262 : W := 0x89ae730c6799d0d
def v263 : W := 0x76518cf398662e2
def v264 : W := 0xa69a6617de2102f
def v265 : W := 0x4d61d1ebdca543f
def v266 : W := 0xd0cbeae44647add
def v267 : W := 0xc7d3173065dbbdd
def v268 : W := 0x9daa3b0f9ae2ee2
def v269 : W := 0xb29e2e14215abc0
def v270 : W := 0x10cb1c444220eb
def v271 : W := 0x10491c000125d0
def v272 : W := 0xa79ef7d7de335ff
def v273 : W := 0x100110044020c9
def v274 : W := 0x3a304c1800c1204
def v275 : W := 0x82004442002b
def v276 : W := 0xa69246139a01004
def v277 : W := 0x80c000220e2
def v278 : W := 0x76510c339844200
def v279 : W := 0x5861082821cc200
def v280 : W := 0x10c31044410d09
def v281 : W := 0x88a242082389004
def v282 : W := 0x775dbdf7dc76feb
def v283 : W := 0x21004139ac5204
def v284 : W := 0x10cb1c444321fb
def v285 : W := 0xfdeffbec653a5fb
def v286 : W := 0xfdeffbec653adeb
def v287 : W := 0xfdeffbec653a9fb
def v288 : W := 0x10cb1c444325fb
def v289 : W := 0x775d3d37dc10509
def v290 : W := 0x3a3cecdc0031136
def v291 : W := 0x10cb1c444325eb
def v292 : W := 0x10cb1c44432deb
def v293 : W := 0x10cb1c444329fb
def v294 : W := 0xfffffffc65fbbff
def v295 : W := 0x10cb1c444329eb
def v296 : W := 0xc5c31323ff0a4c9
def v297 : W := 0x5869282c65e8a2b
def v298 : W := 0x3a3cecdc0070b22
def v299 : W := 0x88a2c2c821ab0f6
def v300 : W := 0xa796d7d398125c0
def v301 : W := 0x5869282c656ca2b
def v302 : W := 0x21004139a11514
def v303 : W := 0x5a792c3fff3953f
def v304 : W := 0x21004139854f00
def v305 : W := 0x88a2c2c8212a0e2
def v306 : W := 0x10cb1c44432dfb
def v307 : W := 0xc5c31323fd0e4c9
def v308 : W := 0x5869282c652802b
def v309 : W := 0x8ab2c6dbb97efe2
def v310 : W := 0x21004139ad5f14
def v311 : W := 0x88a2c2c8232b0f6
def v312 : W := 0x1a3cacdc00f1b36
def v313 : W := 0x820c0c800a1036
def v314 : W := 0xbabeeedc21fbbf6
def v315 : W := 0x82000082128022
def v316 : W := 0x271415139810500
def v317 : W := 0xffffffffffef2ef
def v318 : W := 0x45411123dc04409
def v319 : W := 0x1828280c00e0a22
def v320 : W := 0x858213039a024c0
def v321 : W := 0x7a7decfc65f9b3f
def v322 : W := 0xa3ce4dc00f1b36
def v323 : W := 0x1a38ecdc00f1b36
def v324 : W := 0x2214c4d00011114
def v325 : W := 0xbfbeffdf9af3ff6
def v326 : W := 0xbdaefbcc00220e2
def v327 : W := 0x404100206508009
def v328 : W := 0xbfbeffdf9a335f6
def v329 : W := 0xbfbeffdc00f3bf6
def v330 : W := 0xf7dffff7dc56fc9
def v331 : W := 0xf5cffbe444020c9
def v332 : W := 0xf7dffff7de135dd
def v333 : W := 0x321c2c140050b00
def v334 : W := 0x7f7dfdffdcf5f3f
def v335 : W := 0x7d6df9ec442002b
def v336 : W := 0x2a3ce4dc00b1936
def v337 : W := 0x7f7dfdffdc74f2b
def v338 : W := 0x7f7dfdfc44f1b3f
def v339 : W := 0x80820200210a0c0
def v340 : W := 0xfffffffc65eb2ef
def v341 : W := 0xfffffffc657abeb
def v342 : W := 0xfffffffc653b1ff
def v343 : W := 0xc4cfa2e7bb3c932
def v344 : W := 0xfcefeaec2128022
def v345 : W := 0xf7dffff7de57fdd
def v346 : W := 0x3a3cecdc0030122
def v347 : W := 0x3a38ecdc00e1a36
def v348 : W := 0xfeffeeffbbfdb36
def v349 : W := 0xfeffeeffbbed226
def v350 : W := 0x3a3cecdc0021026
def v351 : W := 0x3a3cacdc00f0b32
def v352 : W := 0xa586d3c000020c0
def v353 : W := 0xfef34e3bbb09004
def v354 : W := 0xfef34e3bb94c200
def v355 : W := 0x3a3cecdc0060222
def v356 : W := 0x3a3cecdc0031936
def v357 : W := 0x754d39244400009
def v358 : W := 0x3a3cecdc0070b32
def v359 : W := 0x3a3cecdc0071b36
def v360 : W := 0x3a3cecdc00f1336
def v361 : W := 0x3a3cecdc00d1b14
def v362 : W := 0x3a3cecdc00e1236
def v363 : W := 0x3a3cecdc00f0b22
def v364 : W := 0x3a3cecdc00e1a26
def v365 : W := 0x504928244444a09
def v366 : W := 0x475d3537dc54f09
def v367 : W := 0x3a3cecdc00f1b26
def v368 : W := 0x8082c2c002030d4
def v369 : W := 0x7f7d3d3ffd7cf2b
def v370 : W := 0x57593d37dc54f09
def v371 : W := 0x535d3d37dc54f09
def v372 : W := 0xfefb6e3fffed22f
def v373 : W := 0x3a3cecdc00b1136
def v374 : W := 0x5869282c6568a2b
def v375 : W := 0xfdeffbec656eaeb
def v376 : W := 0xfdeffbec65ee2eb
def v377 : W := 0xfdeffbec65eaaeb
def v378 : W := 0x5869282c656c22b
def v379 : W := 0x5869282c65e822b
def v380 : W := 0x5869282c65eca2b
def v381 : W := 0xffff7f3fffcd20d
def v382 : W := 0xfff7dffbbbdf7d4
def v383 : W := 0x735d3d344454f09
def v384 : W := 0x675d3537dc14d09
def v385 : W := 0xffff7f3ffd5cf09
def v386 : W := 0xfdef7b2c6508009
def v387 : W := 0x775d3d344410109
def v388 : W := 0x77593d37dc44e09
def v389 : W := 0xffff7f3fffddf0d
def v390 : W := 0x775d3d344440209
def v391 : W := 0x775d3d344454b09
def v392 : W := 0x775d3d344450f09
def v393 : W := 0x775d3d379854f00
def v394 : W := 0xfeffeefc21f9b36
def v395 : W := 0x775d3d37dc50f09
def v396 : W := 0x775d3d37dc14509
def v397 : W := 0x775d3d37dc10d09
def v398 : W := 0x775d3d37dc44a09
def v399 : W := 0x775d3d37dc44609
def v400 : W := 0x8396d7d39a135d4
def v401 : W := 0x775d3d37dc54b09
def v402 : W := 0x775d3d37dc54709
def v403 : W := 0x879697d39a135d4
def v404 : W := 0x8792d7d39a135d4
def v405 : W := 0xa396d7d002135d4
def v406 : W := 0xa796d7d002131d4
def v407 : W := 0xa79697d39a125d0
def v408 : W := 0xfff7dffbbbcf2c4
def v409 : W := 0xfff7dffbbb1b5d4
def v410 : W := 0xfde7dbe8210a0c0
def v411 : W := 0xa792d7d39a034d4
def v412 : W := 0xa796d7d000121c0
def v413 : W := 0xa796d7d000030c4
def v414 : W := 0xa796d7d000135d4
def v415 : W := 0xa796d7d398020c0
def v416 : W := 0xa796d7d398135d4
def v417 : W := 0xa796d7d398125d0
def v418 : W := 0xa796d7d39a030d4
def v419 : W := 0xa796d7d39a034c4
def v420 : W := 0xfffffffffd6e2eb
def v421 : W := 0xcef3463bbbcd204
def v422 : W := 0xa796d7d39a135c4
def v423 : W := 0xa796d7d39a131d4
def v424 : W := 0xa796d7d39a125c0
def v425 : W := 0xeef3463bbb8d004
def v426 : W := 0xdef30e3bbbcd204
def v427 : W := 0xdaf34e3bbbcd204
def v428 : W := 0xfaf34e3823cd204
def v429 : W := 0xfdeffbec652802b
def v430 : W := 0xfdeffbec212a0e2
def v431 : W := 0xffffffffff2b0ef
def v432 : W := 0xfdeffbec650a0c9
def v433 : W := 0xfdeffbec44220eb
def v434 : W := 0xfef34e382148200
def v435 : W := 0xfef34e382109004
def v436 : W := 0xfef30e3bbbcc200
def v437 : W := 0xfef34e3bbbc9204
def v438 : W := 0xfef34e3bb9cd204
def v439 : W := 0xfef34e3bb908000
def v440 : W := 0xfef34e3b9ac5204
def v441 : W := 0xfef34e3823c9204
def v442 : W := 0xfef34e3bb9cc200
def v443 : W := 0xfef34e3bbb4c200
def v444 : W := 0xfef34e3bbb0d004
def v445 : W := 0xfef34e3bbb89004
def v446 : W := 0xfef34e3bbb4d204
def v447 : W := 0xfef7cefbbbcd204
def v448 : W := 0xfef34e3bbbcd604
def v449 : W := 0xfef34e3bbbcd214
def v450 : W := 0xfef3cefbbbcd214
def v451 : W := 0xfef34e3bbbcda04
def v452 : W := 0xfff35f3bbbcd604
def v453 : W := 0xfeff6e3fbbcd204
def v454 : W := 0xfefb6e3fbbcda04
def v455 : W := 0xfff75f3bbbcd204
def v456 : W := 0xfef34e3821cd204
def v457 : W := 0xa796d7d39a11514
def v458 : W := 0x775d3d37de54f09
def v459 : W := 0xbfb6dfdb9a135d4
def v460 : W := 0xa79ef7d79a13dd4
def v461 : W := 0xa796d7d39a935d4
def v462 : W := 0xa796d7d39a175d4
def v463 : W := 0xb79effd79a135d4
def v464 : W := 0xafb6d7db9a935d4
def v465 : W := 0xf7d7dff39a135d4
def v466 : W := 0xe7d7d7f39a175d4
def v467 : W := 0x775d3d37dcd4f09
def v468 : W := 0x775d3d37dc54f19
def v469 : W := 0x7f7d3d3fdcd4f09
def v470 : W := 0x775dfdf7dc54f09
def v471 : W := 0x775dbdf7dc54f19
def v472 : W := 0xafb6d7dbbb3b5f6
def v473 : W := 0x7f7d7d3fdc54f09
def v474 : W := 0xfef3cefbbbef2e6
def v475 : W := 0xfdeffbec67ab0ef
def v476 : W := 0xfdeffbec672b0ff
def v477 : W := 0xfdeffbec65ab0ff
def v478 : W := 0x88a2c2c821ab0e6
def v479 : W := 0x88a2c2c8212b0f6
def v480 : W := 0x88a2c2c8232b0e6
def v481 : W := 0x88a2c2c823ab0f6
def v482 : W := 0xf7df3f37de54f09
def v483 : W := 0xf7df7f37dc54f09
def v484 : W := 0x3f3cfddc00f1b36
def v485 : W := 0x3a3cecdc00f5b36
def v486 : W := 0x3a3cecdc00f1f36
def v487 : W := 0x3b3cfddc00f1f36
def v488 : W := 0x3a3cecdc02f1b36
def v489 : W := 0xf7df3f37fd5efc9
def v490 : W := 0x7e7decfc00f1b36
def v491 : W := 0xc5c31320650a0c9
def v492 : W := 0x7a7decfc00f5b36
def v493 : W := 0xe7d7d7f3ff1b5dd
def v494 : W := 0xbebeeedc00f1b36
def v495 : W := 0xbabeeedc02f1b36
def v496 : W := 0xc5c31323fd0a4c9
def v497 : W := 0xc5c31323fd0e0c9
def v498 : W := 0xc5c31323ff0e4c9
def v499 : W := 0xc5c31323ff0a0c9
def v500 : W := 0xa796d7d39a13dd4
def v501 : W := 0x775d3d37dc00009
def v502 : W := 0x201014
def v503 : W := 0x44a00
def v504 : W := 0x10910
def v505 : W := 0x10510
def v506 : W := 0x0
def v507 : W := 0x10d00
def v508 : W := 0xc0a00
def v509 : W := 0x81014
def v510 : W := 0xc4200
def v511 : W := 0x80c000020d0
def v512 : W := 0x39a00400
def v513 : W := 0x39804400
def v514 : W := 0x281004
def v515 : W := 0x39a04000
def v516 : W := 0x80c00020032
def v517 : W := 0xc0c00001014
def v518 : W := 0xca0c40030932
def v519 : W := 0xca0c40020022
def v520 : W := 0x820044400809
def v521 : W := 0x820040020822
def v522 : W := 0xc20040010900
def v523 : W := 0xc4c30223bb0c000
def v524 : W := 0x100110000024c0
def v525 : W := 0x10011004400409
def v526 : W := 0x10411000010500
def v527 : W := 0x480c00010110
def v528 : W := 0x10c31044400009
def v529 : W := 0x10cb1c44412dd9
def v530 : W := 0x10cb1c44430d3b
def v531 : W := 0xffffffffff3b5ff
def v532 : W := 0x10cb1c40032df2
def v533 : W := 0x10491c000020c0
def v534 : W := 0x210041000d1b14
def v535 : W := 0x21004100050b00
def v536 : W := 0xfffffffffd7efeb
def v537 : W := 0x21004100011114
def v538 : W := 0x210041000c1204
def v539 : W := 0x21004139810500
def v540 : W := 0x21004139844200
def v541 : W := 0x21004139a01004
def v542 : W := 0x210041398d5f14
def v543 : W := 0x21004139a55f14
def v544 : W := 0x21004139ad5714
def v545 : W := 0x21004139ad1f14
def v546 : W := 0x21004139ad5b14
def v547 : W := 0x820c0c80020022
def v548 : W := 0x820000800a0022
def v549 : W := 0x31c3517dc54f09
def v550 : W := 0x31495d39a135d4
def v551 : W := 0x21ca4d400f1b36
def v552 : W := 0x50011039800400
def v553 : W := 0x82000082188000
def v554 : W := 0x82040080081004
def v555 : W := 0x1820080800c0200
def v556 : W := 0x100828040040a00
def v557 : W := 0xa30c4d800f1b36
def v558 : W := 0x1828280c0020022
def v559 : W := 0x1828e8cc00e1a36
def v560 : W := 0x1a382c1c00f1b36
def v561 : W := 0x182ca8cc00f0b32
def v562 : W := 0x2004c0c00000000
def v563 : W := 0x82ce0cc00b1936
def v564 : W := 0x21004139ad5f04
def v565 : W := 0x221404100010100
def v566 : W := 0x2314d5d000135d4
def v567 : W := 0x2214c4d39a11514
def v568 : W := 0x2214c4d000d1b14
def v569 : W := 0x221ce4d40031936
def v570 : W := 0x261004139800000
def v571 : W := 0x250411000000000
def v572 : W := 0x271415139854f00
def v573 : W := 0x271c3517dc10d09
def v574 : W := 0x271495d398125d0
def v575 : W := 0x271415139a11514
def v576 : W := 0x2714d5d39811514
def v577 : W := 0x300c28040000000
def v578 : W := 0x2a34c4d800b1136
def v579 : W := 0x32100c100040200
def v580 : W := 0x321c2c1400d1b14
def v581 : W := 0x371c3d179850f00
def v582 : W := 0x321cecd40051b14
def v583 : W := 0x321cacd40070b32
def v584 : W := 0x321c2c179854f00
def v585 : W := 0x331c3d144450f09
def v586 : W := 0x382048080000000
def v587 : W := 0x382ce8cc00e0a22
def v588 : W := 0x382ce8cc0030932
def v589 : W := 0x382ce8cc00a1036
def v590 : W := 0x392cf9cc44220eb
def v591 : W := 0x3a386c1c00e1a26
def v592 : W := 0x3a30ccd800e1236
def v593 : W := 0x3a304c1b9ac5204
def v594 : W := 0x3a304c1800d1b14
def v595 : W := 0x3a34ccd800d1314
def v596 : W := 0x3a3c6c1c00d1b04
def v597 : W := 0x3a3c2c1c00f0b22
def v598 : W := 0x3b3cfddc44f3bff
def v599 : W := 0x3b3cfddc00f3ff6
def v600 : W := 0x3a3cecdf9af5b36
def v601 : W := 0x3a3cecdf9af1f36
def v602 : W := 0x3b3cfddc44f1f3f
def v603 : W := 0x40410020210c000
def v604 : W := 0x3f3cfddf98f1f36
def v605 : W := 0x404100204404009
def v606 : W := 0x454d3127dc14d09
def v607 : W := 0x454111204400009
def v608 : W := 0x444100239804000
def v609 : W := 0x504108200044200
def v610 : W := 0x47511533dc54f09
def v611 : W := 0x504928244400009
def v612 : W := 0x3a3cecdf98f5f36
def v613 : W := 0x55493927dc44e09
def v614 : W := 0x514d39244454f09
def v615 : W := 0x52592c37dc54f09
def v616 : W := 0x586108282108000
def v617 : W := 0x5869282c21eca22
def v618 : W := 0x5869282c44e4a2b
def v619 : W := 0x5869282c65cca09
def v620 : W := 0x5a710c3bbbcd204
def v621 : W := 0x596db9ec652a0eb
def v622 : W := 0x67551533dc14509
def v623 : W := 0x221044100001004
def v624 : W := 0x754d39244410d09
def v625 : W := 0x744108200000000
def v626 : W := 0x754db9e444220eb
def v627 : W := 0x754d3927dc04409
def v628 : W := 0x754d39244444a09
def v629 : W := 0x765d2c379854b00
def v630 : W := 0x76510c339ac5204
def v631 : W := 0x76510c339854f00
def v632 : W := 0x76592c37dc44a09
def v633 : W := 0x77551d339854700
def v634 : W := 0x77511d33dc44609
def v635 : W := 0x7a714c3821cd204
def v636 : W := 0x775dbdf7dc74f3b
def v637 : W := 0x775d3d37ded5f0d
def v638 : W := 0x775d3d37de55f1d
def v639 : W := 0x775d3d37dcd5f1d
def v640 : W := 0x775dbdf7dc56fd9
def v641 : W := 0x775dfdf7dc55f1d
def v642 : W := 0x786de8ec652802b
def v643 : W := 0x7a7decfc44f5b3f
def v644 : W := 0x7a7decfc21fdb36
def v645 : W := 0x7d6d392c652802b
def v646 : W := 0x7e714c3b98c5204
def v647 : W := 0x7e710c3bb9cc200
def v648 : W := 0x7e7decff98f5b36
def v649 : W := 0x808202002308000
def v650 : W := 0x7f7d7d3fdcd5f0d
def v651 : W := 0x7f7d3d3ffddcf09
def v652 : W := 0x8082020002020c0
def v653 : W := 0x8186d3c002135d4
def v654 : W := 0x8082c2c000020c0
def v655 : W := 0x808242000201004
def v656 : W := 0x848202039a00000
def v657 : W := 0x8292c6d39a135d4
def v658 : W := 0x8582130000020c0
def v659 : W := 0x7f7d3d3fdcf4f2b
def v660 : W := 0x879217139a135d4
def v661 : W := 0x858693c39a125d0
def v662 : W := 0x8582d3c39a034d4
def v663 : W := 0x88a242082108000
def v664 : W := 0x88a2c2c802a30f6
def v665 : W := 0x8ab2461bbbcd204
def v666 : W := 0x88a2c2c823a9036
def v667 : W := 0x88a2c2c8238b0d4
def v668 : W := 0x89aef3cc652a0eb
def v669 : W := 0xa48242000000000
def v670 : W := 0xa296c6d002131d4
def v671 : W := 0xa586d3c39a024c0
def v672 : W := 0xa586d3c000125d0
def v673 : W := 0xa586d3c002030d4
def v674 : W := 0xa58ef3c444220eb
def v675 : W := 0xa69246139ac5204
def v676 : W := 0xa69246139a11514
def v677 : W := 0xa696c6d39a11114
def v678 : W := 0xa692c6d39a030d4
def v679 : W := 0xa79257139a034c4
def v680 : W := 0xa79657139a11504
def v681 : W := 0xa796d7d39ad77d4
def v682 : W := 0xa796d7d39a57fd4
def v683 : W := 0xa796d7d39ad3fd4
def v684 : W := 0xa79ef7d7de13ddd
def v685 : W := 0xa79ef7d79a33df6
def v686 : W := 0xb79effd79a53fd4
def v687 : W := 0xafb6d7db9ab35f6
def v688 : W := 0xaeb2461bbb89004
def v689 : W := 0xafb6d7dbbb9b5d4
def v690 : W := 0xbab24e1823c9204
def v691 : W := 0xb8aeeacc212a0e2
def v692 : W := 0xbabeeedc02f3bf6
def v693 : W := 0xbebeeedf9af1b36
def v694 : W := 0xbabeeedc23f9b36
def v695 : W := 0xbeb24e1b9ac1204
def v696 : W := 0xbfb6dfdb9ad37d4
def v697 : W := 0xada6d3c8212a0e2
def v698 : W := 0xa79617139a125c0
def v699 : W := 0xc5c31323de064c9
def v700 : W := 0xc4c302202108000
def v701 : W := 0xc5c31323bb0e4c0
def v702 : W := 0xc5c31323ff0c409
def v703 : W := 0xd8e34a2823cd204
def v704 : W := 0xcce3422bbb8d004
def v705 : W := 0xc6d30633bbcd204
def v706 : W := 0xc5cfb3e4652a0eb
def v707 : W := 0xcde3d3e8652a0eb
def v708 : W := 0xdce30a2bbbcc200
def v709 : W := 0xd8ebeaec652a0eb
def v710 : W := 0xddeb3b2c652a0eb
def v711 : W := 0xf7d7dff39a577d4
def v712 : W := 0xf5cf3b24650a0c9
def v713 : W := 0xe7d7d7f3de175dd
def v714 : W := 0xe7d7d7f3bb1f5d4
def v715 : W := 0xe6d34633bb0d004
def v716 : W := 0xf6d30e33bb4c200
def v717 : W := 0xf6d34e339a45204
def v718 : W := 0xf7df7f37de55f0d
def v719 : W := 0xf7df3f37de56fc9
def v720 : W := 0xf7df3f37ff5cf09
def v721 : W := 0xe5c7d3e0650a0c9
def v722 : W := 0xfce34a282389004
def v723 : W := 0xfce34a2821cc200
def v724 : W := 0xfce3cae8212a0e2
def v725 : W := 0xfce34a2bbb0c000
def v726 : W := 0xfceb6a2c652802b
def v727 : W := 0xfde35b28650a0c9
def v728 : W := 0xfdeffbeffd2e4eb
def v729 : W := 0xfdeffbefff2e0eb
def v730 : W := 0xfdeffbefff2a4eb
def v731 : W := 0xfefb6e3fbbeda26
def v732 : W := 0xfef3cefbbbcf2d4
def v733 : W := 0xfef34e3bbbddb14
def v734 : W := 0xfef34e3bbbdd714
def v735 : W := 0xfef34e3bbbddf04
def v736 : W := 0xfef3cefbbbed236
def v737 : W := 0xfef7cefbbbdd314
def v738 : W := 0xfeff6e3fbbddb04
def v739 : W := 0xfefb6e3fffcda0d
def v740 : W := 0xfff35f3bbbcf6c4
def v741 : W := 0xfff35f3bffcd60d
def v742 : W := 0xfff75f3bbbdd704
def v743 : W := 0xffffffffdef7fff
def v744 : W := 0xffffffffbbffff6
def v745 : W := 0xfffffffffd3a5eb
def v746 : W := 0xfff35f3bffcf2cd
def v747 : W := 0xffffffffffffbff
def v748 : W := 0xffffffffff7ffff
def v749 : W := 0xffffffffffdffdd
def v750 : W := 0xfffffffffffdf3f
def v751 : W := 0xfffffffffffbfff
def v752 : W := 0xffffffffffff7ff
def v753 : W := 0xfffffffffffffef
def v754 : W := 0xfffffffffdfffff
def v755 : W := 0x725d2c344454b09
def v756 : W := 0x7ff5ffdd1a870a0
def v757 : W := 0xf0ae67340018800
def v758 : W := 0xff5b99fae56065e
def v759 : W := 0x79f5e7950287020
def v760 : W := 0xf2ae6f760818bdd
def v761 : W := 0xff5b99f84460000
def v762 : W := 0x6d0ffc81b031f2
def v763 : W := 0xf9ff83b546e6000
def v764 : W := 0xffafff7ea018e04
def v765 : W := 0x7fa59a5fba86685
def v766 : W := 0xf6fefffc0118852
def v767 : W := 0xf9dbe7b04663020
def v768 : W := 0x7ff5ffdfba876a5
def v769 : W := 0xff5b99f84560052
def v770 : W := 0x7ff5ffdd1b871f2
def v771 : W := 0xff5b99fae460604
def v772 : W := 0x7ff5ffdfbb877f7
def v773 : W := 0x6a47e4fa39fe7e
def v774 : W := 0x951808146e7020
def v775 : W := 0x65099c80100052
def v776 : W := 0xd0e7800203020
def v777 : W := 0x7fa59a5d1a86080
def v778 : W := 0xa466051a9f9a0
def v779 : W := 0xff2f187d5dfc9d2
def v780 : W := 0xf2ae6f7408189d0
def v781 : W := 0x67499cd019c852
def v782 : W := 0xf9ffe7b546ff820
def v783 : W := 0x650fdc80101172
def v784 : W := 0x80fe03a55fe60db
def v785 : W := 0xf95b81b04460000
def v786 : W := 0x6d0ffc80303072
def v787 : W := 0x6809a481a02080
def v788 : W := 0xf6ae7f7ea918fdf
def v789 : W := 0xf0ae67340818981
def v790 : W := 0x7fa59a5fa286604
def v791 : W := 0xd519089e7e7422
def v792 : W := 0xf2ae6f760018a5c
def v793 : W := 0x6d0ffc80100052
def v794 : W := 0xf92f0037e4fce0c
def v795 : W := 0x805a65a0457987a
def v796 : W := 0x79a582150286000
def v797 : W := 0x6d0ffc809001d2
def v798 : W := 0xf20a0972000025c
def v799 : W := 0xf9ffe7b44478800
def v800 : W := 0x7fa59a5ea800685
def v801 : W := 0x6d0ffc81a030a0
def v802 : W := 0xdf5f68ced78d83
def v803 : W := 0x7f25985fa084605
def v804 : W := 0x7f01fc5aa019e24
def v805 : W := 0x7f01985aa000604
def v806 : W := 0x7fa59a5ea000604
def v807 : W := 0xf65a99fa010025e
def v808 : W := 0xf60a197aa10065e
def v809 : W := 0xf6ae7f7ea118e5e
def v810 : W := 0x80ae672408189d9
def v811 : W := 0xff0b997aa00065c
def v812 : W := 0xf9ffe7b40018800
def v813 : W := 0x79756597a185777
def v814 : W := 0xffff9bffffe66df
def v815 : W := 0x865a7deafc79ea5
def v816 : W := 0xf0ae67340018958
def v817 : W := 0xffaf9b7fba86685
def v818 : W := 0xfffffffee578e5e
def v819 : W := 0x6f4ffcd1b871f3
def v820 : W := 0xffafff7fba9ee85
def v821 : W := 0xffff9bfee56065e
def v822 : W := 0xd51908957e7022
def v823 : W := 0xf98b6632fe637ac
def v824 : W := 0xf817f495de41d2
def v825 : W := 0xf92f0036e478e0d
def v826 : W := 0x7f25185fb884685
def v827 : W := 0xfffffffd5eff8a0
def v828 : W := 0x79f56797bb877f7
def v829 : W := 0x7f25185d1884080
def v830 : W := 0x79f5e797a387777
def v831 : W := 0xf0ae66360818b8d
def v832 : W := 0xf6ae7f7e1918bdf
def v833 : W := 0xf67e98fc1b1b9f2
def v834 : W := 0xf47e90be131ba2f
def v835 : W := 0xf6fefffc1b1b9f2
def v836 : W := 0xffdbfffae56065e
def v837 : W := 0xffdbfffaff637fe
def v838 : W := 0xf6dafff81b031f2
def v839 : W := 0x7fa5fe5fba877a5
def v840 : W := 0xf6fefffe0918bdf
def v841 : W := 0xfffffffffeffea5
def v842 : W := 0xfffffffd5fff9f2
def v843 : W := 0xfffffffd47ff872
def v844 : W := 0x800a00204578952
def v845 : W := 0xfffffffd46ff820
def v846 : W := 0x868a9a685e7a880
def v847 : W := 0x805a65a04579972
def v848 : W := 0xf0ae67360018a0d
def v849 : W := 0xffafff7ea818fdd
def v850 : W := 0x5065800101172
def v851 : W := 0x79a58217a286605
def v852 : W := 0x79250017a084605
def v853 : W := 0x240005009c800
def v854 : W := 0x64000019820
def v855 : W := 0x10287020
def v856 : W := 0x50008146e7020
def v857 : W := 0x5000804461020
def v858 : W := 0x76a41a5eb800685
def v859 : W := 0x79a50217ba86685
def v860 : W := 0x5080800203020
def v861 : W := 0xfd1ffc95fe71f2
def v862 : W := 0x86daffe85f7b9f2
def v863 : W := 0x8066001a031a0
def v864 : W := 0xf90b0032e46060c
def v865 : W := 0x6f4ffcd1b9f9f2
def v866 : W := 0xa402051a86081
def v867 : W := 0x805a01a0456005a
def v868 : W := 0x8067000000000
def v869 : W := 0x7fa5fe5fba9fea5
def v870 : W := 0xa46605029f820
def v871 : W := 0x600184aa10065e
def v872 : W := 0xa466040818981
def v873 : W := 0x7f5198dae560606
def v874 : W := 0xa466051a9f8a1
def v875 : W := 0xa466051a871a1
def v876 : W := 0xf9ffe7b55eff8a1
def v877 : W := 0xf9ffe7b55eff9a0
def v878 : W := 0xa466051a9f8a0
def v879 : W := 0xd519089f6e7420
def v880 : W := 0xf92f0037e4fce05
def v881 : W := 0xf2ae6f760818a85
def v882 : W := 0xd067801b031f2
def v883 : W := 0xa466051a9f9a1
def v884 : W := 0xd0e7800303172
def v885 : W := 0x2806f4008001d0
def v886 : W := 0x600184819001d2
def v887 : W := 0xf92f003544fc800
def v888 : W := 0x45090881303022
def v889 : W := 0x4001008a100402
def v890 : W := 0xf6fefffe1b1bbff
def v891 : W := 0xf02e00360018a0d
def v892 : W := 0x60018481800080
def v893 : W := 0xf9af823546fe800
def v894 : W := 0xff5b99faed607df
def v895 : W := 0x600184ab800685
def v896 : W := 0x805a65a04479820
def v897 : W := 0x600184aa9007df
def v898 : W := 0xfffffffeed78fdf
def v899 : W := 0x805a65a0457895a
def v900 : W := 0xf6ae7f7eb818fdd
def v901 : W := 0x80dae7a0467b820
def v902 : W := 0x600184ab9006df
def v903 : W := 0x600184ab8007dd
def v904 : W := 0x600184ab9007d7
def v905 : W := 0x6507dc819011f2
def v906 : W := 0x6507dc80101172
def v907 : W := 0x60098480000000
def v908 : W := 0x600184ab9007df
def v909 : W := 0x65098c81b031f2
def v910 : W := 0xf02e00340018800
def v911 : W := 0xffdbfff85f631f2
def v912 : W := 0xff5bfdfae56177e
def v913 : W := 0xffdbfffaed607de
def v914 : W := 0xffdbfffae76367e
def v915 : W := 0x650fdc81b031f2
def v916 : W := 0x650fdc80100152
def v917 : W := 0x65099c81303072
def v918 : W := 0x650fdc80101072
def v919 : W := 0x650fdc81303172
def v920 : W := 0x650fdc819011f2
def v921 : W := 0x6807f4819001d2
def v922 : W := 0x901000144e4000
def v923 : W := 0x600184ab9007de
def v924 : W := 0x6d07fc81b031f2
def v925 : W := 0x680fe481a031a0
def v926 : W := 0x800a00204478800
def v927 : W := 0x6d07fc819011f2
def v928 : W := 0x6a49a4d1a86081
def v929 : W := 0xffffffffe7ffe7e
def v930 : W := 0x6d0fec81b031f2
def v931 : W := 0x6d0fec81b031a2
def v932 : W := 0x6d0ffc80203020
def v933 : W := 0x6d0ffc80303172
def v934 : W := 0x6d0ffc81303072
def v935 : W := 0x6d0ffc80b031f2
def v936 : W := 0x6d0ffc809011f2
def v937 : W := 0x6d0ffc819001d2
def v938 : W := 0x6d0ffc81b030f2
def v939 : W := 0x6d0ffc81b021d2
def v940 : W := 0x6d0ffc81a031f0
def v941 : W := 0x6d0ffc81a031a0
def v942 : W := 0x6d0ffc81b030a2
def v943 : W := 0x95180804460000
def v944 : W := 0x901000146e7020
def v945 : W := 0x7fa51a5fb884685
def v946 : W := 0x7fa59a5eb800685
def v947 : W := 0xf0fe67b44479820
def v948 : W := 0xf0ae6735029f820
def v949 : W := 0xf0fee7b4021b820
def v950 : W := 0xf9afe735029e800
def v951 : W := 0xf9af673544fc800
def v952 : W := 0x7fa59a5fba876a5
def v953 : W := 0xfdfff7bd57ff822
def v954 : W := 0xb5188c34ee73fd
def v955 : W := 0x951808156e7020
def v956 : W := 0x951808147e7022
def v957 : W := 0x9d1e78146e7020
def v958 : W := 0x951818146e7020
def v959 : W := 0x9518081e6e7420
def v960 : W := 0x9f5e68546ff820
def v961 : W := 0xd51908947e7022
def v962 : W := 0xfbffeff74effbfd
def v963 : W := 0xd519088e560402
def v964 : W := 0xd51908956e7020
def v965 : W := 0xd519089e6e7420
def v966 : W := 0xd519089f7e7422
def v967 : W := 0xf5198cbfee76a5
def v968 : W := 0xf5198cae56065e
def v969 : W := 0xf5198c95fe71f2
def v970 : W := 0xf5198cbe7e767e
def v971 : W := 0xfa59a4fba86685
def v972 : W := 0xfa59a4dba86481
def v973 : W := 0xf5199c947e7072
def v974 : W := 0x72a40a560800285
def v975 : W := 0x8d0bf529b29ed58
def v976 : W := 0xffafff7fba9efdd
def v977 : W := 0x7951809146e7020
def v978 : W := 0x79f5e7950387172
def v979 : W := 0x79f5829546e7020
def v980 : W := 0xff7f99ffe5e465f
def v981 : W := 0x7f25185fa084605
def v982 : W := 0xffff9bfffee6685
def v983 : W := 0xffff9bffe7e665e
def v984 : W := 0x7f01985bb286604
def v985 : W := 0x800a65200018958
def v986 : W := 0x7f25985ea000605
def v987 : W := 0x7f25985fa084604
def v988 : W := 0x7f25985fba86685
def v989 : W := 0x7f25985fb286605
def v990 : W := 0x7f25985fb884685
def v991 : W := 0x7f5198dbe6e7624
def v992 : W := 0x7fa51a5fba86685
def v993 : W := 0xffff9bfeed606df
def v994 : W := 0x70a402140000000
def v995 : W := 0x7ff59adfba876a5
def v996 : W := 0x7fa59a5dba86480
def v997 : W := 0x7fa59a5d1a86081
def v998 : W := 0x7fa59a5f1a86285
def v999 : W := 0x7fa59a5eba02685
def v1000 : W := 0x80ae67240018958
def v1001 : W := 0x7fa59a5fb286604
def v1002 : W := 0x7fa59a5fa286605
def v1003 : W := 0x7fa59a5faa86685
def v1004 : W := 0x7fa59a5fa884685
def v1005 : W := 0x80ae66240818989
def v1006 : W := 0x7fa59a5fba86684
def v1007 : W := 0x80ae67240018800
def v1008 : W := 0x82ae6f660818bdd
def v1009 : W := 0x80ae67240818981
def v1010 : W := 0x82ae6f6408189d9
def v1011 : W := 0x895be5a146ff820
def v1012 : W := 0x8f5b99e8e56045a
def v1013 : W := 0xf0ae66360018a0d
def v1014 : W := 0xf00a01300000000
def v1015 : W := 0x8f5b99eae56065e
def v1016 : W := 0xf0ae66340818981
def v1017 : W := 0xf0ae66340018800
def v1018 : W := 0xf97f65b544fd820
def v1019 : W := 0xf95b81b146e7020
def v1020 : W := 0xf95be5b04479820
def v1021 : W := 0xf97f81b544fc800
def v1022 : W := 0xf97f80b546ff820
def v1023 : W := 0xf9ffe7b746ffa2d
def v1024 : W := 0xff5b98fae56065e
def v1025 : W := 0xf9ffe7b54eff9a1
def v1026 : W := 0xf9ffe7b546ff978
def v1027 : W := 0xfbffeff74effaa5
def v1028 : W := 0xfbffeff64c78bdd
def v1029 : W := 0xfbffeff54eff9f0
def v1030 : W := 0xfb5b89f2446025c
def v1031 : W := 0xfbffeff746ffa7c
def v1032 : W := 0xf0ae67340018801
def v1033 : W := 0xf0ae67340018808
def v1034 : W := 0xf0ae67360018b5d
def v1035 : W := 0xf0ae67340018950
def v1036 : W := 0xf0ae67340018900
def v1037 : W := 0xf0ae67340818980
def v1038 : W := 0xf0ae67340818881
def v1039 : W := 0xf0ae67360018a0c
def v1040 : W := 0xf0ae67360018a05
def v1041 : W := 0xf0ae673408189d9
def v1042 : W := 0xf0fee7b40018800
def v1043 : W := 0xf0ae67360818bdd
def v1044 : W := 0xf0ae67360818b8d
def v1045 : W := 0xf2ae6e760818b8d
def v1046 : W := 0xf2ae6e760818bdd
def v1047 : W := 0xf2ae6f760018b5c
def v1048 : W := 0xf2ae6f760018a04
def v1049 : W := 0xf2ae6f740818880
def v1050 : W := 0xf2ae6f7408189d8
def v1051 : W := 0xf2ae6f7408189d1
def v1052 : W := 0xf2ae6f760018a5d
def v1053 : W := 0xf2ae6f760818add
def v1054 : W := 0xf2ae6f7608003dd
def v1055 : W := 0xf2ae6f760818a8d
def v1056 : W := 0xf2ae6f760818bdc
def v1057 : W := 0xf2ae6f760818bd5
def v1058 : W := 0xf2ae6f760818b85
def v1059 : W := 0xf2ae6f740018850
def v1060 : W := 0xf9ffe7b546e7020
def v1061 : W := 0xffffffffe6ffe24
def v1062 : W := 0xf9ff67b546ff820
def v1063 : W := 0xf9ff67b544fd820
def v1064 : W := 0xf9ffe7b5029f820
def v1065 : W := 0xf9ffe7b4467b820
def v1066 : W := 0xf9ffe7b44479820
def v1067 : W := 0xf9ffe7b544fc800
def v1068 : W := 0xff5b98fae56060e
def v1069 : W := 0xf9ffe7b546fe800
def v1070 : W := 0xff5b99fa456025e
def v1071 : W := 0xff5b99f8e560452
def v1072 : W := 0xff5b99f8456005a
def v1073 : W := 0xff5b99faa10065e
def v1074 : W := 0xff5b99fae56065f
def v1075 : W := 0xff5b99fae560606
def v1076 : W := 0xff5b99fae46065c
def v1077 : W := 0xff5b99fae46060c
def v1078 : W := 0xff5b99fae560656
def v1079 : W := 0xff7f99fee56065f
def v1080 : W := 0xff5bfdfae56075e
def v1081 : W := 0xff5b99fae56075e
def v1082 : W := 0xf2ae6f760918bdf
def v1083 : W := 0xfdfff7bd56ff820
def v1084 : W := 0xf9ffe7b556ff820
def v1085 : W := 0xf2fe6ff60918bdf
def v1086 : W := 0xf2ae6f76a818fdd
def v1087 : W := 0xf2ae6f761818bdd
def v1088 : W := 0xf2feeff60818bdd
def v1089 : W := 0xf0ae67340018858
def v1090 : W := 0xf6ae7f7c19189d2
def v1091 : W := 0xf6ae7f7e1818bdd
def v1092 : W := 0xf6ae7f7e0918bdf
def v1093 : W := 0xf6ae7f7ea818fdd
def v1094 : W := 0xf6ae7f7eb818e85
def v1095 : W := 0xf6fefffe1918bdf
def v1096 : W := 0xf6aeff7e0818bdd
def v1097 : W := 0xf6ae7f7eb918fdf
def v1098 : W := 0xf9afe7340018800
def v1099 : W := 0xf6fefffea918fdf
def v1100 : W := 0x7fa5fe5fba86785
def v1101 : W := 0xffafff7eb818fdd
def v1102 : W := 0xfbafef760818bdd
def v1103 : W := 0xffafff7ea918fdf
def v1104 : W := 0x7fa59a5fba86785
def v1105 : W := 0x7fa59a5fba8668d
def v1106 : W := 0xfffffffea918fdf
def v1107 : W := 0x7fa5ff5fba86685
def v1108 : W := 0x7fa5fe5fba876a5
def v1109 : W := 0x7ff59bdfba86685
def v1110 : W := 0xfbaf6f76a818fdd
def v1111 : W := 0x805a65a0457885a
def v1112 : W := 0x805a01a0457885a
def v1113 : W := 0xff5bfdfae579e7e
def v1114 : W := 0xff5bfdfae578f5e
def v1115 : W := 0xf9ffe7b547ff87a
def v1116 : W := 0xf9ffe7b547ff972
def v1117 : W := 0x805a65a04579872
def v1118 : W := 0x805a65a0457997a
def v1119 : W := 0x86daffe85e7b8a0
def v1120 : W := 0x6d0ffc81b031f3
def v1121 : W := 0xffaf9a7fba8668d
def v1122 : W := 0x6d0ffc91b871f2
def v1123 : W := 0x6d0ffc81b031fa
def v1124 : W := 0x6f4ffcc1b031f3
def v1125 : W := 0x7ff5ffdfba877a5
def v1126 : W := 0xfd1ffc91b871f2
def v1127 : W := 0x76f4ffdc1b031f2
def v1128 : W := 0xffaf9a7ffefee85
def v1129 : W := 0x79f5e797a287625
def v1130 : W := 0x7fd1ffd81b031f2
def v1131 : W := 0x86daffe81b031fa
def v1132 : W := 0x7ff5ffdd1b871f3
def v1133 : W := 0xf92f0036e478e0c
def v1134 : W := 0xfbaf6f76ec78fdd
def v1135 : W := 0xff7f99ffe5fce5e
def v1136 : W := 0xff7f99fee578e5f
def v1137 : W := 0xf90b0032e478e0c
def v1138 : W := 0xf9ffe7b7e6ffe2c
def v1139 : W := 0xf9ffe7b7e6ffe25
def v1140 : W := 0xf92f0037e4fce04
def v1141 : W := 0xf92f0037e4fce0d
def v1142 : W := 0xffaf9a7d5efe880
def v1143 : W := 0xf95b01b2e56065e
def v1144 : W := 0x6f4ffcd1b871f2
def v1145 : W := 0x7fa59a5d0286000
def v1146 : W := 0x100152
def v1147 : W := 0x10005a
def v1148 : W := 0x158
def v1149 : W := 0x1800081
def v1150 : W := 0x1203020
def v1151 : W := 0x800181
def v1152 : W := 0x1800180
def v1153 : W := 0x64000018900
def v1154 : W := 0x2a000605
def v1155 : W := 0x2000020d
def v1156 : W := 0x11286000
def v1157 : W := 0x64000001120
def v1158 : W := 0x2a00060c
def v1159 : W := 0x2400040018801
def v1160 : W := 0x65000000150
def v1161 : W := 0x2400050084001
def v1162 : W := 0x5065800001020
def v1163 : W := 0x5000800101022
def v1164 : W := 0x5001800100052
def v1165 : W := 0x5000804560002
def v1166 : W := 0x8066000203020
def v1167 : W := 0x8002001a02080
def v1168 : W := 0x5081800000000
def v1169 : W := 0x8066000800180
def v1170 : W := 0xa402050286000
def v1171 : W := 0xa402040800081
def v1172 : W := 0x8082000202000
def v1173 : W := 0xa466040018800
def v1174 : W := 0xa466041a1b9a1
def v1175 : W := 0xa466051a9e981
def v1176 : W := 0xa466050a9f9a1
def v1177 : W := 0x200084008001d0
def v1178 : W := 0xf4e785029f820
def v1179 : W := 0xd0e7801a031a0
def v1180 : W := 0x200084208003dd
def v1181 : W := 0x20008420800285
def v1182 : W := 0x2000842000025c
def v1183 : W := 0x2800a400800080
def v1184 : W := 0x20009400000050
def v1185 : W := 0x2806f401a031f0
def v1186 : W := 0x2a46f4408189d1
def v1187 : W := 0x2a46e460818bdd
def v1188 : W := 0x2806f4208003dd
def v1189 : W := 0x2d06fc009011f2
def v1190 : W := 0x4001008b000400
def v1191 : W := 0x40010081100002
def v1192 : W := 0x45090880100002
def v1193 : W := 0x40090081202000
def v1194 : W := 0x4d0f6881b031a2
def v1195 : W := 0x450f5881303172
def v1196 : W := 0x60018480100052
def v1197 : W := 0x4d0f7881303022
def v1198 : W := 0x2d0efc00a031f0
def v1199 : W := 0x600184a19003df
def v1200 : W := 0x600184aa000604
def v1201 : W := 0x65099caa10065e
def v1202 : W := 0x65099c819001d2
def v1203 : W := 0x6807e481b031f2
def v1204 : W := 0x6d09ac81b030a2
def v1205 : W := 0x6809a4aba02685
def v1206 : W := 0x6809a481b021d2
def v1207 : W := 0x6a41a4fba86685
def v1208 : W := 0x680ff481a021d0
def v1209 : W := 0x6d09bc81b020d2
def v1210 : W := 0x90180010286000
def v1211 : W := 0x6d0ffcabb037fe
def v1212 : W := 0x6d0ffcabb037f7
def v1213 : W := 0x6d0ffca1b033ff
def v1214 : W := 0x6f4ffcc1b1b9f3
def v1215 : W := 0x9010000e460400
def v1216 : W := 0x9010001a084400
def v1217 : W := 0xd019009b286400
def v1218 : W := 0x7ff59adffee76a5
def v1219 : W := 0xff5b99fbe7e767e
def v1220 : W := 0xd019008a000400
def v1221 : W := 0xd519088f763422
def v1222 : W := 0xf01984bba86685
def v1223 : W := 0xd519089b387422
def v1224 : W := 0xda5920dba86481
def v1225 : W := 0xd519089f7e6402
def v1226 : W := 0xf5199c8e560452
def v1227 : W := 0xfd1ffc8ff635f2
def v1228 : W := 0xf819a49ba86480
def v1229 : W := 0x702400160000205
def v1230 : W := 0xfd1ffc9bb875f2
def v1231 : W := 0x72a46f5608003d5
def v1232 : W := 0x72a40a5608003dd
def v1233 : W := 0x72a46e560818b85
def v1234 : W := 0x72a40a571a86285
def v1235 : W := 0x792500150084000
def v1236 : W := 0x76f4ffde1b033f7
def v1237 : W := 0x76a49a5e1a02285
def v1238 : W := 0x790180100000000
def v1239 : W := 0x79010012a000604
def v1240 : W := 0x79a5e615029f820
def v1241 : W := 0x79a582151a86081
def v1242 : W := 0x7da5921db286400
def v1243 : W := 0x7ba50a57a884685
def v1244 : W := 0x7d25901fb286605
def v1245 : W := 0x7ba58a570a86285
def v1246 : W := 0x7f01985ab800685
def v1247 : W := 0x7f01985aa10065e
def v1248 : W := 0x7f819a5aba02684
def v1249 : W := 0x7f5199daa100656
def v1250 : W := 0x7fa5ff5fba867d5
def v1251 : W := 0x7fa59a5fbb866df
def v1252 : W := 0x7fa59a5fba867dd
def v1253 : W := 0x7fa5fe5fba9ef85
def v1254 : W := 0x7fa59a5fbb867d7
def v1255 : W := 0x7ff59adfbb876a7
def v1256 : W := 0x7fd1ffdabb037f6
def v1257 : W := 0x7ff59bdfbb866d7
def v1258 : W := 0x7ff59adfffe6687
def v1259 : W := 0x800a00200018808
def v1260 : W := 0x800a65200018800
def v1261 : W := 0x800a01200000058
def v1262 : W := 0x805a01a04460000
def v1263 : W := 0x805a65a0011997a
def v1264 : W := 0x805a65a0456117a
def v1265 : W := 0x805a65a04479978
def v1266 : W := 0x80fe67a546ff820
def v1267 : W := 0x865a99e8456005a
def v1268 : W := 0x865a19eae56065e
def v1269 : W := 0x828a6f6008189d8
def v1270 : W := 0x86daffe85f631fa
def v1271 : W := 0x86daffe81b1b9fa
def v1272 : W := 0xf00a0032000020c
def v1273 : W := 0x8d5b91a8e56045a
def v1274 : W := 0xf02e65360018b5d
def v1275 : W := 0x820a6d620818bdd
def v1276 : W := 0xf25a09f2456025e
def v1277 : W := 0xf20a6d720018b5c
def v1278 : W := 0xf20a097208003dd
def v1279 : W := 0xf22e09760018a5d
def v1280 : W := 0xf22e08760818bdd
def v1281 : W := 0xf2ae0b7608002dd
def v1282 : W := 0xf2ae0a760818a8d
def v1283 : W := 0xf28a6f7208003dc
def v1284 : W := 0x800a00204460008
def v1285 : W := 0xf2fe6ff60919bff
def v1286 : W := 0xf2ae6f761a1bbfd
def v1287 : W := 0xf2ae6f771a9ebdd
def v1288 : W := 0xf2ae6f770a9fbfd
def v1289 : W := 0xf2feeff60a1bbfd
def v1290 : W := 0xf2fe6ff64d78bdf
def v1291 : W := 0xf2fe6ff64c79bfd
def v1292 : W := 0xf6aeff7e1a1abdd
def v1293 : W := 0xf6dafffa1b033fe
def v1294 : W := 0xf90b00304460000
def v1295 : W := 0xf92f0037e4e460d
def v1296 : W := 0xf92f0037a09ce0d
def v1297 : W := 0xf92f003744fca0d
def v1298 : W := 0xf95b81b0456005a
def v1299 : W := 0xf95b81b2e46060c
def v1300 : W := 0xf9af663546ff820
def v1301 : W := 0xfb0b0972e46065c
def v1302 : W := 0xfbafef770a9ebdd
def v1303 : W := 0xfbaf6f77a89cfdd
def v1304 : W := 0xfbaf6f774cfcbdd
def v1305 : W := 0xfd5b90bae56060e
def v1306 : W := 0xfd5b91b8e560402
def v1307 : W := 0xff0b187ae56065e
def v1308 : W := 0xfdfff7bdf6ffc20
def v1309 : W := 0xfdfff7bde7ffc22
def v1310 : W := 0xff0b987ae46060c
def v1311 : W := 0xff5b99fafd607de
def v1312 : W := 0xff5b99fafd606df
def v1313 : W := 0xff5b99faf76367e
def v1314 : W := 0xff5b99fbf7e665e
def v1315 : W := 0xffaf9b7fba866dd
def v1316 : W := 0xffaf9a7fba9ee8d
def v1317 : W := 0xffaf9a7ffee668d
def v1318 : W := 0xffdb9bfaff626de
def v1319 : W := 0xffffffff5fffbff
def v1320 : W := 0xfffffffeff7bfff
def v1321 : W := 0xffffffffbb9ffff
def v1322 : W := 0xfffffffffeffffd
def v1323 : W := 0xffffffffeffffff
def v1324 : W := 0xffffffffffe77ff
def v1325 : W := 0xffffffffffffffe
def v1326 : W := 0xffffffffffffff7
def v1327 : W := 0xffffffffffffeff
def v1328 : W := 0xfffffffffffefdf
def v1329 : W := 0x720008520000204
def v1330 : W := 0x42f4fc5d53c1b17
def v1331 : W := 0x83dcfdc22c72770
def v1332 : W := 0xe74e7c381d39c0e
def v1333 : W := 0xfd2b3bfce028ed5
def v1334 : W := 0xfdbfc3ff169702a
def v1335 : W := 0x875dd6d3faae4b7
def v1336 : W := 0x913dd1ea04d745a
def v1337 : W := 0xd77f1f5455fc181
def v1338 : W := 0xefc5f6b92f11526
def v1339 : W := 0x4642cebe512b5db
def v1340 : W := 0x79a3efbd4286aed
def v1341 : W := 0xfefe396eb828e5a
def v1342 : W := 0x113bcfd79739b7c
def v1343 : W := 0x7ef827532bc617c
def v1344 : W := 0xe89e3e574651eb7
def v1345 : W := 0xaedcf0e9177ab6c
def v1346 : W := 0x68822e154200aa5
def v1347 : W := 0x801c10420451412
def v1348 : W := 0x103a0946d0aead9
def v1349 : W := 0x101c69147d61a5
def v1350 : W := 0x101c69142860a5
def v1351 : W := 0x865c1042b828412
def v1352 : W := 0x101c6910711124
def v1353 : W := 0x103a09469028a58
def v1354 : W := 0xc0aa000345a
def v1355 : W := 0x46420e145128181
def v1356 : W := 0x101c69147d51a5
def v1357 : W := 0x1038c1ea00c745a
def v1358 : W := 0x1038014200c6058
def v1359 : W := 0x6ec026112b00124
def v1360 : W := 0x103a094450eeac9
def v1361 : W := 0x2880e0a90202a6c
def v1362 : W := 0x865c10401578100
def v1363 : W := 0x1139c1c204d7058
def v1364 : W := 0x1121c1a80086048
def v1365 : W := 0xf9bfffff46d7eff
def v1366 : W := 0x1139c1ea00c6058
def v1367 : W := 0x2880e0abaa02e7e
def v1368 : W := 0x2880e0abaa01e7e
def v1369 : W := 0x51230f144084081
def v1370 : W := 0xfffffffd57febed
def v1371 : W := 0x78a2292c0000a48
def v1372 : W := 0xfffffffffaaeeff
def v1373 : W := 0x6ec22e157b281a5
def v1374 : W := 0x6983eebd4200aa5
def v1375 : W := 0x6981e6b90200024
def v1376 : W := 0xffe7ffbd6f97fef
def v1377 : W := 0x6ec22e155328ba5
def v1378 : W := 0x6ec22e15fa28aa5
def v1379 : W := 0x6ec22e15bb28b24
def v1380 : W := 0x6fc1e6b92b00124
def v1381 : W := 0x8105d0a80411402
def v1382 : W := 0xfffdf7fb2fd757e
def v1383 : W := 0x79a3efbd42840a5
def v1384 : W := 0x79a3efbd0200a6c
def v1385 : W := 0x801cd0ea045345a
def v1386 : W := 0x811dd0ea0451412
def v1387 : W := 0x811dd0c204d7412
def v1388 : W := 0x903c116a000045a
def v1389 : W := 0xfffff9eebcffe5a
def v1390 : W := 0xfefe396c3828402
def v1391 : W := 0xd67e1f545128181
def v1392 : W := 0x913dd1ea008645a
def v1393 : W := 0x913dd1e804d5402
def v1394 : W := 0x913dd1c004d7000
def v1395 : W := 0x913d114004d4000
def v1396 : W := 0xd77fdffe55ff5db
def v1397 : W := 0x913dd1e804d6048
def v1398 : W := 0xc74516100510100
def v1399 : W := 0xfffffffd7ffd5a7
def v1400 : W := 0x913dd1ea041145a
def v1401 : W := 0xd67e19441028000
def v1402 : W := 0xffff3f7efdfcfdb
def v1403 : W := 0xefc5f6b90710124
def v1404 : W := 0xd77f1f5450ac081
def v1405 : W := 0xd77f1f541538100
def v1406 : W := 0xeec430282800402
def v1407 : W := 0xffffffffbf39f7e
def v1408 : W := 0xfefe3944b828a00
def v1409 : W := 0xefc5f6b92a00426
def v1410 : W := 0xfefe396c1028a48
def v1411 : W := 0xb9bdf1eaacd7e5a
def v1412 : W := 0xd77fdfd455ff181
def v1413 : W := 0xfefef9eeb82be5a
def v1414 : W := 0xefddf6fb2f51536
def v1415 : W := 0x913fd9ee44d7edb
def v1416 : W := 0x913dd7fa45d75db
def v1417 : W := 0x977dd1ea2dd755a
def v1418 : W := 0xfffdf1ea2cd745a
def v1419 : W := 0xd77dd7fa05d755a
def v1420 : W := 0xd13fdffe44d74db
def v1421 : W := 0xf9bff9ee04d7e5a
def v1422 : W := 0x865c10403d79502
def v1423 : W := 0x79bbefff42c6afd
def v1424 : W := 0x865c1042bd39512
def v1425 : W := 0x903cd1ea000345a
def v1426 : W := 0x2880202aa800e5a
def v1427 : W := 0x102209044086ac9
def v1428 : W := 0x101c08004d7000
def v1429 : W := 0x101061045d4181
def v1430 : W := 0x103a094450ec081
def v1431 : W := 0x2880e0a92a01426
def v1432 : W := 0x6ec22804b828a00
def v1433 : W := 0x864410002d11502
def v1434 : W := 0x773bc6ff0c2d1b9
def v1435 : W := 0xe18c96ba8e17b6f
def v1436 : W := 0xfdc6bfce501afc3
def v1437 : W := 0xffae1c79bea0616
def v1438 : W := 0xa79ebbc21c6a2e
def v1439 : W := 0x145b617f1171757
def v1440 : W := 0x268a3b7eeba9d5
def v1441 : W := 0xebf57d06afd1141
def v1442 : W := 0x9ccebbf9a3fc0f8
def v1443 : W := 0xf7bf547271dc5ed
def v1444 : W := 0xf5d7f7c59f66c38
def v1445 : W := 0x7d422d432debb97
def v1446 : W := 0xa71690421c0000
def v1447 : W := 0xebfdffbeafd7b6f
def v1448 : W := 0x2394031afe403c
def v1449 : W := 0x51e386015d1e9
def v1450 : W := 0x5161060151141
def v1451 : W := 0x140a00791020616
def v1452 : W := 0x40a386401a9c1
def v1453 : W := 0x2280031aea0014
def v1454 : W := 0x882b80006a2e
def v1455 : W := 0xe18414028e11141
def v1456 : W := 0x51e3840146828
def v1457 : W := 0xf58614419e20410
def v1458 : W := 0x51e386415e9e9
def v1459 : W := 0x51e386401f9e9
def v1460 : W := 0x239403021c402c
def v1461 : W := 0xf586144250185c1
def v1462 : W := 0x279e3bc0146828
def v1463 : W := 0x239c2bc0004028
def v1464 : W := 0x7f7befff2defbbf
def v1465 : W := 0x2394031afe5038
def v1466 : W := 0x279e3b421c682c
def v1467 : W := 0x840ab8c0002a02
def v1468 : W := 0xfffffffe71defef
def v1469 : W := 0x840290021c2a06
def v1470 : W := 0x750204430c29191
def v1471 : W := 0xa2808382080206
def v1472 : W := 0xfffffffdbfe6e3e
def v1473 : W := 0x163bc2fd002c0b8
def v1474 : W := 0x140a82f9002c0b8
def v1475 : W := 0x88c43900a3d0040
def v1476 : W := 0xa79ebbc21c4028
def v1477 : W := 0xa79ebbc0006a2a
def v1478 : W := 0x140a82f8500eeae
def v1479 : W := 0x140a82f9502eeba
def v1480 : W := 0x140a82f91026e3e
def v1481 : W := 0x163bc2f90c2d0b8
def v1482 : W := 0x773bc6fe000c1a9
def v1483 : W := 0x750286ce0008181
def v1484 : W := 0xffffffff5c3fffb
def v1485 : W := 0x633144060c01101
def v1486 : W := 0xffffffffaffd1f9
def v1487 : W := 0x773bc6fd0c24038
def v1488 : W := 0x8af57900afd1040
def v1489 : W := 0x88d57906a3d1141
def v1490 : W := 0x8af57904a3d0040
def v1491 : W := 0xffbf5c79bfe1616
def v1492 : W := 0xfd861c481000602
def v1493 : W := 0xffeebffffebafd7
def v1494 : W := 0xebf57d0621d0141
def v1495 : W := 0xebf57d04afc0000
def v1496 : W := 0xeba41c00ae80000
def v1497 : W := 0xffff7d7fbff1757
def v1498 : W := 0xe9d57d060151141
def v1499 : W := 0xebf57d060c11141
def v1500 : W := 0xf7ae1471bea0414
def v1501 : W := 0xf58e14799e20616
def v1502 : W := 0xf7ae14799e20410
def v1503 : W := 0xffae1c783080606
def v1504 : W := 0xfdc6bfcc1002e02
def v1505 : W := 0xfd8e1c791020616
def v1506 : W := 0xfdc6bfce00181c1
def v1507 : W := 0xffae1c79aea0010
def v1508 : W := 0xffae1c791c20612
def v1509 : W := 0x88c4390071d2e46
def v1510 : W := 0xebfd7d37aff1155
def v1511 : W := 0xffeebffdbea2e16
def v1512 : W := 0xffee3d79bfe2e16
def v1513 : W := 0xffff7d7dbfe0616
def v1514 : W := 0xfff7ffceafd91c1
def v1515 : W := 0xfff77d47aff91d1
def v1516 : W := 0xffff7d7faff1151
def v1517 : W := 0x8afdfbbcb3c6e2e
def v1518 : W := 0xf7bfd6ff8e3d1f9
def v1519 : W := 0x88c43900b3c2e06
def v1520 : W := 0xffffffff0c3d1f9
def v1521 : W := 0xf58614438e391d1
def v1522 : W := 0xf58614435c395d1
def v1523 : W := 0xfffffffc31c6e2e
def v1524 : W := 0xe9c43d060010141
def v1525 : W := 0xfff7ffceffdbfc3
def v1526 : W := 0x11c286000d1a9
def v1527 : W := 0x23940310c25038
def v1528 : W := 0x2314000afc1000
def v1529 : W := 0x140282c8500ae82
def v1530 : W := 0x88c439005012e42
def v1531 : W := 0x88841800b280606
def v1532 : W := 0xffbfdeffbead7bf
def v1533 : W := 0x772a04790c20010
def v1534 : W := 0x1da64eac7219323
def v1535 : W := 0x489ab43c766ad0b
def v1536 : W := 0xb2df514a407d012
def v1537 : W := 0xeed0e6d893431b6
def v1538 : W := 0xfffffffd0d80ccc

def ins_e8a8a888 : List W := [0xedfbdfdcb566611, 0xb72f25fe089816e, 0x5ad5ff320a15fc4, 0x7fde6839cf6980e, 0xff34f32f74d38cb]
theorem nd_e8a8a888 : ins_e8a8a888.Nodup := by decide +kernel
theorem rows_e8a8a888 : ∀ j : Fin 60, Nat.testBit 0xe8a8a888 (∑ i : Fin 5, if (ins_e8a8a888.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
def tree_e8a8a888_0 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_0 : everyKey (fun q => !doneTest q) tree_e8a8a888_0 = true := by decide +kernel
theorem closed_e8a8a888_0 : Closed 0 tree_e8a8a888_0 := closed_nil tree_e8a8a888_0 ok_tree_e8a8a888_0
def tree_e8a8a888_1 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_1 : everyKey (rowOK 0 tree_e8a8a888_0) tree_e8a8a888_1 = true := by decide +kernel
theorem closed_e8a8a888_1 : Closed 1 tree_e8a8a888_1 := closed_next 0 (by decide) tree_e8a8a888_1 tree_e8a8a888_0 closed_e8a8a888_0 ok_tree_e8a8a888_1
def tree_e8a8a888_2 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_2 : everyKey (rowOK 1 tree_e8a8a888_1) tree_e8a8a888_2 = true := by decide +kernel
theorem closed_e8a8a888_2 : Closed 2 tree_e8a8a888_2 := closed_next 1 (by decide) tree_e8a8a888_2 tree_e8a8a888_1 closed_e8a8a888_1 ok_tree_e8a8a888_2
def tree_e8a8a888_3 : BinaryTree (List W) := (.node [v0,v1,v2,v3] (.node [v4,v5,v1,v2] (.node [v4,v0,v1,v2] (.node [v6,v7,v8,v1] (.node [v9,v8,v10,v11] .nil .nil) .nil) (.node [v4,v12,v1,v2] (.node [v4,v13,v1,v2] .nil .nil) .nil)) (.node [v0,v14,v1,v2] (.node [v15,v0,v1,v2] (.node [v4,v8,v1,v10] .nil .nil) .nil) (.node [v0,v1,v10,v11] .nil .nil))) (.node [v16,v17,v1,v2] (.node [v18,v8,v1,v2] (.node [v19,v1,v2,v11] (.node [v20,v7,v8,v11] .nil .nil) .nil) (.node [v21,v8,v1,v2] (.node [v22,v1,v2,v11] .nil .nil) .nil)) (.node [v7,v23,v1,v11] (.node [v7,v24,v1,v2] (.node [v25,v8,v26,v11] .nil .nil) .nil) (.node [v8,v27,v1,v2] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_3 : everyKey (rowOK 2 tree_e8a8a888_2) tree_e8a8a888_3 = true := by decide +kernel
theorem closed_e8a8a888_3 : Closed 3 tree_e8a8a888_3 := closed_next 2 (by decide) tree_e8a8a888_3 tree_e8a8a888_2 closed_e8a8a888_2 ok_tree_e8a8a888_3
def tree_e8a8a888_4ll : BinaryTree (List W) := (.node [v28,v7,v8,v1,v2] (.node [v29,v7,v8,v1,v2] (.node [v30,v7,v1,v2,v11] (.node [v30,v4,v7,v1,v2] (.node [v30,v29,v7,v1,v2] .nil .nil) (.node [v30,v0,v1,v2,v11] .nil .nil)) (.node [v29,v0,v7,v1,v2] (.node [v29,v4,v8,v1,v2] .nil .nil) .nil)) (.node [v31,v7,v8,v1,v2] (.node [v32,v7,v33,v1,v2] (.node [v29,v8,v34,v1,v2] .nil .nil) (.node [v35,v7,v8,v1,v2] .nil .nil)) (.node [v36,v7,v8,v1,v2] (.node [v37,v38,v7,v8,v1] .nil .nil) .nil))) (.node [v39,v4,v8,v1,v2] (.node [v40,v7,v8,v1,v11] (.node [v41,v7,v42,v1,v11] (.node [v43,v7,v8,v1,v2] .nil .nil) (.node [v44,v45,v7,v8,v11] .nil .nil)) (.node [v46,v7,v1,v2,v11] (.node [v9,v8,v2,v11,v47] .nil .nil) .nil)) (.node [v48,v0,v1,v2,v11] (.node [v49,v7,v1,v2,v11] (.node [v50,v7,v2,v11,v51] .nil .nil) (.node [v48,v4,v8,v1,v2] .nil .nil)) (.node [v52,v7,v8,v2,v11] (.node [v53,v7,v8,v2,v11] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_4ll : everyKey (rowOK 3 tree_e8a8a888_3) tree_e8a8a888_4ll = true := by decide +kernel
def tree_e8a8a888_4lr : BinaryTree (List W) := (.node [v54,v7,v1,v2,v11] (.node [v4,v0,v1,v2,v11] (.node [v4,v0,v7,v1,v2] (.node [v55,v0,v1,v2,v11] (.node [v55,v4,v8,v1,v2] .nil .nil) (.node [v56,v7,v8,v1,v2] .nil .nil)) (.node [v4,v0,v1,v2] (.node [v4,v0,v8,v1,v2] .nil .nil) .nil)) (.node [v4,v8,v1,v2,v47] (.node [v4,v8,v57,v1,v2] (.node [v4,v7,v8,v1,v2] .nil .nil) (.node [v4,v8,v1,v2,v58] .nil .nil)) (.node [v59,v7,v8,v1,v2] (.node [v15,v7,v8,v1,v2] .nil .nil) .nil))) (.node [v60,v7,v1,v2,v11] (.node [v0,v57,v1,v2,v11] (.node [v0,v61,v1,v2,v11] (.node [v0,v7,v1,v2,v11] .nil .nil) (.node [v0,v34,v1,v2,v11] .nil .nil)) (.node [v13,v7,v1,v2,v11] (.node [v0,v1,v2,v11,v47] .nil .nil) .nil)) (.node [v62,v8,v1,v2,v11] (.node [v63,v8,v1,v2,v11] (.node [v64,v8,v1,v2,v11] .nil .nil) .nil) (.node [v65,v8,v1,v2,v11] (.node [v16,v8,v1,v2,v11] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_4lr : everyKey (rowOK 3 tree_e8a8a888_3) tree_e8a8a888_4lr = true := by decide +kernel
def tree_e8a8a888_4l : BinaryTree (List W) := .node [v66,v7,v8,v2,v11] tree_e8a8a888_4ll tree_e8a8a888_4lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_4l : everyKey (rowOK 3 tree_e8a8a888_3) tree_e8a8a888_4l = true := by
  change (_ && everyKey _ tree_e8a8a888_4ll && everyKey _ tree_e8a8a888_4lr) = true
  rw [ok_tree_e8a8a888_4ll, ok_tree_e8a8a888_4lr]
  decide +kernel
def tree_e8a8a888_4rl : BinaryTree (List W) := (.node [v7,v8,v26,v11,v67] (.node [v7,v68,v1,v2,v11] (.node [v7,v17,v1,v2,v69] (.node [v7,v70,v1,v2,v11] (.node [v25,v8,v1,v2,v11] .nil .nil) (.node [v7,v71,v1,v11,v72] .nil .nil)) (.node [v7,v14,v8,v1,v2] (.node [v7,v73,v8,v1,v2] .nil .nil) .nil)) (.node [v7,v74,v1,v2,v11] (.node [v7,v5,v1,v2,v11] (.node [v7,v12,v1,v2,v11] .nil .nil) (.node [v7,v75,v1,v2,v11] .nil .nil)) (.node [v7,v8,v76,v1,v2] (.node [v7,v77,v1,v2,v11] .nil .nil) .nil))) (.node [v7,v8,v1,v78,v79] (.node [v7,v8,v80,v2,v11] (.node [v7,v8,v81,v1,v2] (.node [v7,v8,v82,v2,v83] .nil .nil) (.node [v7,v8,v84,v2,v11] .nil .nil)) (.node [v7,v8,v1,v85,v2] (.node [v7,v8,v86,v2,v11] .nil .nil) .nil)) (.node [v7,v8,v1,v2,v3] (.node [v7,v8,v1,v2,v87] (.node [v7,v8,v1,v10,v11] .nil .nil) .nil) (.node [v7,v8,v1,v2,v88] (.node [v7,v8,v1,v2,v89] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_4rl : everyKey (rowOK 3 tree_e8a8a888_3) tree_e8a8a888_4rl = true := by decide +kernel
def tree_e8a8a888_4rr : BinaryTree (List W) := (.node [v7,v90,v1,v2,v11] (.node [v7,v8,v1,v2,v91] (.node [v7,v8,v1,v2,v92] (.node [v7,v8,v1,v2,v93] (.node [v7,v8,v1,v2,v94] .nil .nil) (.node [v7,v8,v1,v2,v95] .nil .nil)) (.node [v7,v8,v1,v2,v96] (.node [v7,v8,v1,v2,v97] .nil .nil) .nil)) (.node [v7,v98,v1,v2,v11] (.node [v7,v99,v1,v2,v11] (.node [v7,v100,v1,v2,v11] .nil .nil) (.node [v7,v101,v1,v2,v11] .nil .nil)) (.node [v7,v102,v1,v2,v11] (.node [v7,v103,v1,v2,v11] .nil .nil) .nil))) (.node [v8,v104,v1,v2,v11] (.node [v7,v1,v2,v11,v105] (.node [v7,v1,v2,v11,v106] (.node [v7,v1,v2,v11,v107] .nil .nil) (.node [v7,v1,v2,v11,v108] .nil .nil)) (.node [v109,v8,v1,v2,v11] (.node [v7,v1,v2,v11,v110] .nil .nil) .nil)) (.node [v8,v111,v1,v2,v11] (.node [v8,v112,v1,v2,v11] (.node [v8,v113,v1,v2,v11] .nil .nil) .nil) (.node [v8,v1,v2,v11,v114] (.node [v8,v1,v115,v2,v11] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_4rr : everyKey (rowOK 3 tree_e8a8a888_3) tree_e8a8a888_4rr = true := by decide +kernel
def tree_e8a8a888_4r : BinaryTree (List W) := .node [v7,v8,v1,v2,v11] tree_e8a8a888_4rl tree_e8a8a888_4rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_4r : everyKey (rowOK 3 tree_e8a8a888_3) tree_e8a8a888_4r = true := by
  change (_ && everyKey _ tree_e8a8a888_4rl && everyKey _ tree_e8a8a888_4rr) = true
  rw [ok_tree_e8a8a888_4rl, ok_tree_e8a8a888_4rr]
  decide +kernel
def tree_e8a8a888_4 : BinaryTree (List W) := .node [v116,v8,v1,v2,v11] tree_e8a8a888_4l tree_e8a8a888_4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_4 : everyKey (rowOK 3 tree_e8a8a888_3) tree_e8a8a888_4 = true := by
  change (_ && everyKey _ tree_e8a8a888_4l && everyKey _ tree_e8a8a888_4r) = true
  rw [ok_tree_e8a8a888_4l, ok_tree_e8a8a888_4r]
  decide +kernel
theorem closed_e8a8a888_4 : Closed 4 tree_e8a8a888_4 := closed_next 3 (by decide) tree_e8a8a888_4 tree_e8a8a888_3 closed_e8a8a888_3 ok_tree_e8a8a888_4
def tree_e8a8a888_5l : BinaryTree (List W) := (.node [v9,v7,v8,v1,v2,v11] (.node [v32,v7,v8,v1,v2,v11] (.node [v117,v7,v8,v1,v2,v11] (.node [v30,v7,v1,v2,v11] (.node [v30,v7,v8,v1,v2,v11] .nil .nil) .nil) (.node [v29,v7,v8,v1,v2,v11] (.node [v29,v7,v8,v1,v2] .nil .nil) .nil)) (.node [v44,v7,v8,v1,v2,v11] (.node [v41,v7,v8,v1,v2,v11] (.node [v37,v7,v8,v1,v2,v11] .nil .nil) .nil) (.node [v38,v7,v8,v1,v2,v11] (.node [v118,v7,v8,v1,v2,v11] .nil .nil) .nil))) (.node [v45,v7,v8,v1,v2,v11] (.node [v119,v7,v8,v1,v2,v11] (.node [v50,v7,v8,v1,v2,v11] (.node [v39,v7,v8,v1,v2,v11] .nil .nil) .nil) (.node [v48,v7,v8,v1,v2,v11] (.node [v120,v7,v8,v1,v2,v11] .nil .nil) .nil)) (.node [v4,v7,v8,v1,v2,v11] (.node [v4,v7,v8,v1,v2] (.node [v55,v7,v8,v1,v2,v11] .nil .nil) .nil) (.node [v0,v7,v8,v1,v2,v11] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_5l : everyKey (rowOK 4 tree_e8a8a888_4) tree_e8a8a888_5l = true := by decide +kernel
def tree_e8a8a888_5r : BinaryTree (List W) := (.node [v7,v8,v82,v1,v2,v11] (.node [v7,v8,v42,v1,v2,v11] (.node [v7,v8,v61,v1,v2,v11] (.node [v7,v17,v8,v1,v2,v11] (.node [v7,v71,v8,v1,v2,v11] .nil .nil) .nil) (.node [v7,v8,v121,v1,v2,v11] (.node [v7,v8,v33,v1,v2,v11] .nil .nil) .nil)) (.node [v7,v8,v57,v1,v2,v11] (.node [v7,v8,v122,v1,v2,v11] (.node [v7,v8,v34,v1,v2,v11] .nil .nil) .nil) (.node [v7,v8,v26,v1,v2,v11] .nil .nil))) (.node [v7,v8,v1,v2,v11,v72] (.node [v7,v8,v1,v2,v11,v58] (.node [v7,v8,v1,v2,v11,v83] (.node [v7,v8,v1,v78,v2,v11] .nil .nil) .nil) (.node [v7,v8,v1,v2,v11,v51] (.node [v7,v8,v1,v2,v11,v69] .nil .nil) .nil)) (.node [v7,v8,v1,v2,v11,v123] (.node [v7,v8,v1,v2,v11,v67] (.node [v7,v8,v1,v2,v11,v47] .nil .nil) .nil) (.node [v7,v8,v1,v2,v11,v79] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_5r : everyKey (rowOK 4 tree_e8a8a888_4) tree_e8a8a888_5r = true := by decide +kernel
def tree_e8a8a888_5 : BinaryTree (List W) := .node [v0,v7,v1,v2,v11] tree_e8a8a888_5l tree_e8a8a888_5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_5 : everyKey (rowOK 4 tree_e8a8a888_4) tree_e8a8a888_5 = true := by
  change (_ && everyKey _ tree_e8a8a888_5l && everyKey _ tree_e8a8a888_5r) = true
  rw [ok_tree_e8a8a888_5l, ok_tree_e8a8a888_5r]
  decide +kernel
theorem closed_e8a8a888_5 : Closed 5 tree_e8a8a888_5 := closed_next 4 (by decide) tree_e8a8a888_5 tree_e8a8a888_4 closed_e8a8a888_4 ok_tree_e8a8a888_5
def tree_e8a8a888_6 : BinaryTree (List W) := (.node [v7,v8,v1,v2,v11] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8a888_6 : everyKey (rowOK 5 tree_e8a8a888_5) tree_e8a8a888_6 = true := by decide +kernel
theorem closed_e8a8a888_6 : Closed 6 tree_e8a8a888_6 := closed_next 5 (by decide) tree_e8a8a888_6 tree_e8a8a888_5 closed_e8a8a888_5 ok_tree_e8a8a888_6
theorem lower_e8a8a888 : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 6 ins_e8a8a888.toFinset := @no_build 6 tree_e8a8a888_6 ins_e8a8a888 nd_e8a8a888 (by decide) closed_e8a8a888_6 (by decide +kernel)
def gates_e8a8a888 : List Gate := [⟨.and, [0, 1]⟩, ⟨.and, [0, 3]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [0, 7]⟩, ⟨.and, [4, 8]⟩, ⟨.or, [6, 9]⟩, ⟨.and, [2, 10]⟩, ⟨.or, [5, 11]⟩]
theorem upper_e8a8a888 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 8 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xe8a8a888 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  exact ⟨gates_e8a8a888, 12, by simp [gates_e8a8a888], rfl, by decide +kernel⟩

def ins_e8a8c888 : List W := [0xfbbab3fc36480e7, 0x6e5fffa40933e08, 0xddedce5f57a7191, 0xcc77ed0721cfb4, 0xfbb3d859e8cf616]
theorem nd_e8a8c888 : ins_e8a8c888.Nodup := by decide +kernel
theorem rows_e8a8c888 : ∀ j : Fin 60, Nat.testBit 0xe8a8c888 (∑ i : Fin 5, if (ins_e8a8c888.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
def tree_e8a8c888_0 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8c888_0 : everyKey (fun q => !doneTest q) tree_e8a8c888_0 = true := by decide +kernel
theorem closed_e8a8c888_0 : Closed 0 tree_e8a8c888_0 := closed_nil tree_e8a8c888_0 ok_tree_e8a8c888_0
def tree_e8a8c888_1 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8c888_1 : everyKey (rowOK 0 tree_e8a8c888_0) tree_e8a8c888_1 = true := by decide +kernel
theorem closed_e8a8c888_1 : Closed 1 tree_e8a8c888_1 := closed_next 0 (by decide) tree_e8a8c888_1 tree_e8a8c888_0 closed_e8a8c888_0 ok_tree_e8a8c888_1
def tree_e8a8c888_2 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8c888_2 : everyKey (rowOK 1 tree_e8a8c888_1) tree_e8a8c888_2 = true := by decide +kernel
theorem closed_e8a8c888_2 : Closed 2 tree_e8a8c888_2 := closed_next 1 (by decide) tree_e8a8c888_2 tree_e8a8c888_1 closed_e8a8c888_1 ok_tree_e8a8c888_2
def tree_e8a8c888_3 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8c888_3 : everyKey (rowOK 2 tree_e8a8c888_2) tree_e8a8c888_3 = true := by decide +kernel
theorem closed_e8a8c888_3 : Closed 3 tree_e8a8c888_3 := closed_next 2 (by decide) tree_e8a8c888_3 tree_e8a8c888_2 closed_e8a8c888_2 ok_tree_e8a8c888_3
def tree_e8a8c888_4 : BinaryTree (List W) := (.node [v124,v125,v126,v127,v128] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8c888_4 : everyKey (rowOK 3 tree_e8a8c888_3) tree_e8a8c888_4 = true := by decide +kernel
theorem closed_e8a8c888_4 : Closed 4 tree_e8a8c888_4 := closed_next 3 (by decide) tree_e8a8c888_4 tree_e8a8c888_3 closed_e8a8c888_3 ok_tree_e8a8c888_4
theorem lower_e8a8c888 : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 4 ins_e8a8c888.toFinset := @no_build 4 tree_e8a8c888_4 ins_e8a8c888 nd_e8a8c888 (by decide) closed_e8a8c888_4 (by decide +kernel)
def gates_e8a8c888 : List Gate := [⟨.and, [0, 1]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [1, 3]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [2, 8]⟩, ⟨.or, [5, 9]⟩]
theorem upper_e8a8c888 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 6 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xe8a8c888 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  exact ⟨gates_e8a8c888, 10, by simp [gates_e8a8c888], rfl, by decide +kernel⟩

def ins_e8a8e880 : List W := [0xbbbb6bfc628dac3, 0xc5fdfc9a0566f24, 0x7ed69f743b5045c, 0xf66ef7c1d8bb1b0, 0x2f03d0bcdc0b42f]
theorem nd_e8a8e880 : ins_e8a8e880.Nodup := by decide +kernel
theorem rows_e8a8e880 : ∀ j : Fin 60, Nat.testBit 0xe8a8e880 (∑ i : Fin 5, if (ins_e8a8e880.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
def tree_e8a8e880_0 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8e880_0 : everyKey (fun q => !doneTest q) tree_e8a8e880_0 = true := by decide +kernel
theorem closed_e8a8e880_0 : Closed 0 tree_e8a8e880_0 := closed_nil tree_e8a8e880_0 ok_tree_e8a8e880_0
def tree_e8a8e880_1 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8e880_1 : everyKey (rowOK 0 tree_e8a8e880_0) tree_e8a8e880_1 = true := by decide +kernel
theorem closed_e8a8e880_1 : Closed 1 tree_e8a8e880_1 := closed_next 0 (by decide) tree_e8a8e880_1 tree_e8a8e880_0 closed_e8a8e880_0 ok_tree_e8a8e880_1
def tree_e8a8e880_2 : BinaryTree (List W) := (.node [v129,v130,v131] (.node [v132,v130,v133] .nil .nil) .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8e880_2 : everyKey (rowOK 1 tree_e8a8e880_1) tree_e8a8e880_2 = true := by decide +kernel
theorem closed_e8a8e880_2 : Closed 2 tree_e8a8e880_2 := closed_next 1 (by decide) tree_e8a8e880_2 tree_e8a8e880_1 closed_e8a8e880_1 ok_tree_e8a8e880_2
def tree_e8a8e880_3 : BinaryTree (List W) := (.node [v129,v130,v133,v134] (.node [v135,v136,v137,v138] (.node [v135,v139,v140,v138] (.node [v135,v141,v142,v138] (.node [v135,v143,v129,v144] .nil .nil) .nil) (.node [v135,v145,v129,v138] .nil .nil)) (.node [v132,v144,v133,v146] (.node [v135,v147,v144,v133] .nil .nil) (.node [v129,v148,v133,v138] .nil .nil))) (.node [v129,v144,v133,v149] (.node [v129,v144,v133,v150] (.node [v129,v144,v131,v146] .nil .nil) (.node [v129,v144,v133,v151] .nil .nil)) (.node [v129,v144,v133,v152] (.node [v129,v144,v133,v153] .nil .nil) (.node [v129,v144,v154,v138] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8e880_3 : everyKey (rowOK 2 tree_e8a8e880_2) tree_e8a8e880_3 = true := by decide +kernel
theorem closed_e8a8e880_3 : Closed 3 tree_e8a8e880_3 := closed_next 2 (by decide) tree_e8a8e880_3 tree_e8a8e880_2 closed_e8a8e880_2 ok_tree_e8a8e880_3
def tree_e8a8e880_4ll : BinaryTree (List W) := (.node [v155,v129,v144,v133,v138] (.node [v156,v129,v144,v157,v138] (.node [v158,v135,v159,v129,v144] (.node [v160,v161,v144,v133,v138] (.node [v162,v129,v144,v133,v138] .nil .nil) .nil) (.node [v163,v129,v164,v133,v138] (.node [v158,v129,v144,v133,v146] .nil .nil) .nil)) (.node [v165,v129,v144,v133,v138] (.node [v166,v129,v144,v133,v146] (.node [v166,v135,v167,v144,v133] .nil .nil) .nil) (.node [v155,v129,v144,v133,v168] .nil .nil))) (.node [v169,v129,v144,v133,v138] (.node [v170,v135,v129,v144,v133] (.node [v171,v129,v144,v133,v138] (.node [v155,v129,v144,v133,v146] .nil .nil) .nil) (.node [v172,v135,v129,v144,v133] (.node [v173,v135,v129,v144,v133] .nil .nil) .nil)) (.node [v174,v129,v144,v175,v138] (.node [v176,v129,v144,v133,v146] (.node [v177,v129,v144,v133,v138] .nil .nil) .nil) (.node [v178,v129,v144,v133,v138] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8e880_4ll : everyKey (rowOK 3 tree_e8a8e880_3) tree_e8a8e880_4ll = true := by decide +kernel
def tree_e8a8e880_4lr : BinaryTree (List W) := (.node [v179,v129,v144,v133,v138] (.node [v180,v129,v144,v133,v138] (.node [v181,v129,v144,v133,v138] (.node [v181,v129,v144,v133,v182] (.node [v181,v129,v164,v133,v138] .nil .nil) .nil) (.node [v181,v129,v183,v133,v138] (.node [v181,v129,v144,v133,v149] .nil .nil) .nil)) (.node [v184,v129,v144,v133,v138] (.node [v185,v129,v144,v133,v138] (.node [v186,v129,v144,v133,v138] .nil .nil) .nil) (.node [v187,v129,v144,v133,v138] .nil .nil))) (.node [v135,v141,v133,v138,v188] (.node [v135,v189,v190,v129,v138] (.node [v191,v129,v144,v133,v138] (.node [v192,v129,v144,v133,v138] .nil .nil) .nil) (.node [v135,v193,v129,v144,v138] (.node [v135,v194,v129,v144,v138] .nil .nil) .nil)) (.node [v135,v195,v144,v133,v196] (.node [v135,v139,v144,v138,v197] (.node [v135,v198,v129,v133,v138] .nil .nil) .nil) (.node [v135,v136,v144,v133,v138] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8e880_4lr : everyKey (rowOK 3 tree_e8a8e880_3) tree_e8a8e880_4lr = true := by decide +kernel
def tree_e8a8e880_4l : BinaryTree (List W) := .node [v199,v129,v144,v133,v138] tree_e8a8e880_4ll tree_e8a8e880_4lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8e880_4l : everyKey (rowOK 3 tree_e8a8e880_3) tree_e8a8e880_4l = true := by
  change (_ && everyKey _ tree_e8a8e880_4ll && everyKey _ tree_e8a8e880_4lr) = true
  rw [ok_tree_e8a8e880_4ll, ok_tree_e8a8e880_4lr]
  decide +kernel
def tree_e8a8e880_4rl : BinaryTree (List W) := (.node [v135,v129,v144,v133,v200] (.node [v135,v129,v144,v142,v138] (.node [v135,v129,v140,v133,v138] (.node [v135,v129,v201,v133,v134] (.node [v135,v129,v137,v138,v202] .nil .nil) .nil) (.node [v135,v129,v144,v131,v138] (.node [v135,v129,v144,v203,v204] .nil .nil) .nil)) (.node [v135,v129,v144,v133,v205] (.node [v135,v129,v144,v133,v206] (.node [v135,v129,v144,v133,v182] .nil .nil) .nil) (.node [v135,v129,v144,v133,v207] .nil .nil))) (.node [v135,v208,v144,v133,v138] (.node [v135,v129,v144,v133,v209] (.node [v135,v129,v144,v133,v138] (.node [v135,v129,v144,v133,v210] .nil .nil) .nil) (.node [v135,v129,v144,v133,v149] (.node [v135,v129,v144,v133,v211] .nil .nil) .nil)) (.node [v212,v129,v144,v133,v146] (.node [v213,v129,v144,v133,v138] (.node [v135,v214,v144,v133,v138] .nil .nil) .nil) (.node [v215,v129,v144,v133,v138] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8e880_4rl : everyKey (rowOK 3 tree_e8a8e880_3) tree_e8a8e880_4rl = true := by decide +kernel
def tree_e8a8e880_4rr : BinaryTree (List W) := (.node [v129,v144,v133,v216,v138] (.node [v129,v217,v144,v133,v138] (.node [v195,v129,v144,v133,v146] (.node [v218,v129,v144,v133,v138] (.node [v219,v129,v144,v133,v138] .nil .nil) .nil) (.node [v129,v164,v144,v133,v138] (.node [v129,v220,v144,v133,v138] .nil .nil) .nil)) (.node [v129,v144,v221,v133,v138] (.node [v129,v130,v144,v133,v138] (.node [v129,v222,v144,v133,v138] .nil .nil) .nil) (.node [v129,v144,v203,v133,v146] .nil .nil))) (.node [v129,v144,v133,v138,v223] (.node [v129,v144,v133,v224,v138] (.node [v129,v144,v133,v225,v138] (.node [v129,v144,v133,v226,v138] .nil .nil) .nil) (.node [v129,v144,v133,v227,v138] .nil .nil)) (.node [v129,v144,v133,v149] (.node [v129,v144,v133,v138,v146] (.node [v129,v144,v133,v138,v149] .nil .nil) .nil) (.node [v129,v144,v133,v146,v134] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8e880_4rr : everyKey (rowOK 3 tree_e8a8e880_3) tree_e8a8e880_4rr = true := by decide +kernel
def tree_e8a8e880_4r : BinaryTree (List W) := .node [v228,v129,v144,v133,v138] tree_e8a8e880_4rl tree_e8a8e880_4rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8e880_4r : everyKey (rowOK 3 tree_e8a8e880_3) tree_e8a8e880_4r = true := by
  change (_ && everyKey _ tree_e8a8e880_4rl && everyKey _ tree_e8a8e880_4rr) = true
  rw [ok_tree_e8a8e880_4rl, ok_tree_e8a8e880_4rr]
  decide +kernel
def tree_e8a8e880_4 : BinaryTree (List W) := .node [v135,v132,v144,v133,v138] tree_e8a8e880_4l tree_e8a8e880_4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8e880_4 : everyKey (rowOK 3 tree_e8a8e880_3) tree_e8a8e880_4 = true := by
  change (_ && everyKey _ tree_e8a8e880_4l && everyKey _ tree_e8a8e880_4r) = true
  rw [ok_tree_e8a8e880_4l, ok_tree_e8a8e880_4r]
  decide +kernel
theorem closed_e8a8e880_4 : Closed 4 tree_e8a8e880_4 := closed_next 3 (by decide) tree_e8a8e880_4 tree_e8a8e880_3 closed_e8a8e880_3 ok_tree_e8a8e880_4
def tree_e8a8e880_5l : BinaryTree (List W) := (.node [v181,v129,v144,v133,v138] (.node [v155,v135,v129,v144,v133,v138] (.node [v163,v135,v129,v144,v133,v138] (.node [v158,v135,v129,v144,v133,v138] (.node [v160,v135,v129,v144,v133,v138] .nil .nil) .nil) (.node [v166,v135,v129,v144,v133,v138] (.node [v156,v135,v129,v144,v133,v138] .nil .nil) .nil)) (.node [v176,v135,v129,v144,v133,v138] (.node [v229,v135,v129,v144,v133,v138] (.node [v155,v129,v144,v133,v138] .nil .nil) .nil) (.node [v181,v135,v129,v144,v133,v138] (.node [v174,v135,v129,v144,v133,v138] .nil .nil) .nil))) (.node [v135,v230,v129,v144,v133,v138] (.node [v135,v231,v129,v144,v133,v138] (.node [v135,v159,v129,v144,v133,v138] (.node [v232,v135,v129,v144,v133,v138] .nil .nil) .nil) (.node [v135,v141,v129,v144,v133,v138] (.node [v135,v189,v129,v144,v133,v138] .nil .nil) .nil)) (.node [v135,v139,v129,v144,v133,v138] (.node [v135,v190,v129,v144,v133,v138] (.node [v135,v212,v129,v144,v133,v138] .nil .nil) .nil) (.node [v135,v161,v129,v144,v133,v138] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8e880_5l : everyKey (rowOK 4 tree_e8a8e880_4) tree_e8a8e880_5l = true := by decide +kernel
def tree_e8a8e880_5r : BinaryTree (List W) := (.node [v135,v129,v144,v133,v168,v138] (.node [v135,v129,v164,v144,v133,v138] (.node [v135,v129,v233,v144,v133,v138] (.node [v135,v129,v167,v144,v133,v138] (.node [v135,v129,v234,v144,v133,v138] .nil .nil) .nil) (.node [v135,v129,v137,v144,v133,v138] (.node [v135,v129,v235,v144,v133,v138] .nil .nil) .nil)) (.node [v135,v129,v144,v175,v133,v138] (.node [v135,v129,v144,v183,v133,v138] (.node [v135,v129,v201,v144,v133,v138] .nil .nil) .nil) (.node [v135,v129,v144,v203,v133,v138] .nil .nil))) (.node [v135,v129,v144,v133,v138,v134] (.node [v135,v129,v144,v133,v138,v196] (.node [v135,v129,v144,v133,v138,v204] (.node [v135,v129,v144,v133,v157,v138] .nil .nil) .nil) (.node [v135,v129,v144,v133,v138,v188] (.node [v135,v129,v144,v133,v138,v146] .nil .nil) .nil)) (.node [v129,v164,v144,v133,v138] (.node [v135,v129,v144,v133,v138,v202] (.node [v135,v129,v144,v133,v138,v197] .nil .nil) .nil) (.node [v129,v144,v133,v138,v146] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8e880_5r : everyKey (rowOK 4 tree_e8a8e880_4) tree_e8a8e880_5r = true := by decide +kernel
def tree_e8a8e880_5 : BinaryTree (List W) := .node [v135,v195,v129,v144,v133,v138] tree_e8a8e880_5l tree_e8a8e880_5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8e880_5 : everyKey (rowOK 4 tree_e8a8e880_4) tree_e8a8e880_5 = true := by
  change (_ && everyKey _ tree_e8a8e880_5l && everyKey _ tree_e8a8e880_5r) = true
  rw [ok_tree_e8a8e880_5l, ok_tree_e8a8e880_5r]
  decide +kernel
theorem closed_e8a8e880_5 : Closed 5 tree_e8a8e880_5 := closed_next 4 (by decide) tree_e8a8e880_5 tree_e8a8e880_4 closed_e8a8e880_4 ok_tree_e8a8e880_5
def tree_e8a8e880_6 : BinaryTree (List W) := (.node [v135,v129,v144,v133,v138] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8a8e880_6 : everyKey (rowOK 5 tree_e8a8e880_5) tree_e8a8e880_6 = true := by decide +kernel
theorem closed_e8a8e880_6 : Closed 6 tree_e8a8e880_6 := closed_next 5 (by decide) tree_e8a8e880_6 tree_e8a8e880_5 closed_e8a8e880_5 ok_tree_e8a8e880_6
theorem lower_e8a8e880 : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 6 ins_e8a8e880.toFinset := @no_build 6 tree_e8a8e880_6 ins_e8a8e880 nd_e8a8e880 (by decide) closed_e8a8e880_6 (by decide +kernel)
def gates_e8a8e880 : List Gate := [⟨.or, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [1, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [7, 8]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [6, 10]⟩, ⟨.and, [5, 11]⟩]
theorem upper_e8a8e880 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 8 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xe8a8e880 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  exact ⟨gates_e8a8e880, 12, by simp [gates_e8a8e880], rfl, by decide +kernel⟩

def ins_e8e8e800 : List W := [0x7f3d6fa5f0c5ae8, 0xb6e3dedd0b033b5, 0xc9def37b043bc9a, 0x6f5bb294fd6c405, 0x97b45d78ded0546]
theorem nd_e8e8e800 : ins_e8e8e800.Nodup := by decide +kernel
theorem rows_e8e8e800 : ∀ j : Fin 60, Nat.testBit 0xe8e8e800 (∑ i : Fin 5, if (ins_e8e8e800.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
def tree_e8e8e800_0 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8e8e800_0 : everyKey (fun q => !doneTest q) tree_e8e8e800_0 = true := by decide +kernel
theorem closed_e8e8e800_0 : Closed 0 tree_e8e8e800_0 := closed_nil tree_e8e8e800_0 ok_tree_e8e8e800_0
def tree_e8e8e800_1 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8e8e800_1 : everyKey (rowOK 0 tree_e8e8e800_0) tree_e8e8e800_1 = true := by decide +kernel
theorem closed_e8e8e800_1 : Closed 1 tree_e8e8e800_1 := closed_next 0 (by decide) tree_e8e8e800_1 tree_e8e8e800_0 closed_e8e8e800_0 ok_tree_e8e8e800_1
def tree_e8e8e800_2 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8e8e800_2 : everyKey (rowOK 1 tree_e8e8e800_1) tree_e8e8e800_2 = true := by decide +kernel
theorem closed_e8e8e800_2 : Closed 2 tree_e8e8e800_2 := closed_next 1 (by decide) tree_e8e8e800_2 tree_e8e8e800_1 closed_e8e8e800_1 ok_tree_e8e8e800_2
def tree_e8e8e800_3 : BinaryTree (List W) := (.node [v236,v237,v238,v239] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8e8e800_3 : everyKey (rowOK 2 tree_e8e8e800_2) tree_e8e8e800_3 = true := by decide +kernel
theorem closed_e8e8e800_3 : Closed 3 tree_e8e8e800_3 := closed_next 2 (by decide) tree_e8e8e800_3 tree_e8e8e800_2 closed_e8e8e800_2 ok_tree_e8e8e800_3
def tree_e8e8e800_4 : BinaryTree (List W) := (.node [v240,v236,v241,v237,v238] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_e8e8e800_4 : everyKey (rowOK 3 tree_e8e8e800_3) tree_e8e8e800_4 = true := by decide +kernel
theorem closed_e8e8e800_4 : Closed 4 tree_e8e8e800_4 := closed_next 3 (by decide) tree_e8e8e800_4 tree_e8e8e800_3 closed_e8e8e800_3 ok_tree_e8e8e800_4
theorem lower_e8e8e800 : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 4 ins_e8e8e800.toFinset := @no_build 4 tree_e8e8e800_4 ins_e8e8e800 nd_e8e8e800 (by decide) closed_e8e8e800_4 (by decide +kernel)
def gates_e8e8e800 : List Gate := [⟨.or, [0, 1]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 1]⟩, ⟨.or, [2, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.and, [5, 9]⟩]
theorem upper_e8e8e800 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 6 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xe8e8e800 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  exact ⟨gates_e8e8e800, 10, by simp [gates_e8e8e800], rfl, by decide +kernel⟩

def ins_eaa8a880 : List W := [0xfdeffbec652a0eb, 0x3a3cecdc00f1b36, 0x775d3d37dc54f09, 0xa796d7d39a135d4, 0xfef34e3bbbcd204]
theorem nd_eaa8a880 : ins_eaa8a880.Nodup := by decide +kernel
theorem rows_eaa8a880 : ∀ j : Fin 60, Nat.testBit 0xeaa8a880 (∑ i : Fin 5, if (ins_eaa8a880.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
def tree_eaa8a880_0 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_0 : everyKey (fun q => !doneTest q) tree_eaa8a880_0 = true := by decide +kernel
theorem closed_eaa8a880_0 : Closed 0 tree_eaa8a880_0 := closed_nil tree_eaa8a880_0 ok_tree_eaa8a880_0
def tree_eaa8a880_1 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_1 : everyKey (rowOK 0 tree_eaa8a880_0) tree_eaa8a880_1 = true := by decide +kernel
theorem closed_eaa8a880_1 : Closed 1 tree_eaa8a880_1 := closed_next 0 (by decide) tree_eaa8a880_1 tree_eaa8a880_0 closed_eaa8a880_0 ok_tree_eaa8a880_1
def tree_eaa8a880_2 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_2 : everyKey (rowOK 1 tree_eaa8a880_1) tree_eaa8a880_2 = true := by decide +kernel
theorem closed_eaa8a880_2 : Closed 2 tree_eaa8a880_2 := closed_next 1 (by decide) tree_eaa8a880_2 tree_eaa8a880_1 closed_eaa8a880_1 ok_tree_eaa8a880_2
def tree_eaa8a880_3 : BinaryTree (List W) := (.node [v242,v243,v244,v245] (.node [v246,v244,v247,v248] (.node [v246,v242,v244,v249] (.node [v246,v242,v250,v244] (.node [v246,v251,v244,v247] .nil .nil) (.node [v246,v242,v252,v247] .nil .nil)) (.node [v246,v242,v253,v247] (.node [v246,v242,v244,v247] .nil .nil) .nil)) (.node [v254,v244,v255,v256] (.node [v254,v257,v255,v258] (.node [v259,v242,v245,v258] .nil .nil) (.node [v254,v257,v247,v256] .nil .nil)) (.node [v251,v244,v249,v260] (.node [v251,v252,v247,v260] .nil .nil) .nil))) (.node [v261,v244,v245,v258] (.node [v242,v262,v247,v245] (.node [v242,v252,v249,v260] (.node [v242,v263,v247,v245] .nil .nil) (.node [v242,v244,v264,v245] .nil .nil)) (.node [v265,v247,v245,v258] (.node [v242,v266,v245,v258] .nil .nil) .nil)) (.node [v244,v255,v267,v258] (.node [v244,v268,v245,v258] (.node [v257,v247,v267,v258] .nil .nil) .nil) (.node [v247,v269,v245,v258] (.node [v244,v247,v267,v256] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_3 : everyKey (rowOK 2 tree_eaa8a880_2) tree_eaa8a880_3 = true := by decide +kernel
theorem closed_eaa8a880_3 : Closed 3 tree_eaa8a880_3 := closed_next 2 (by decide) tree_eaa8a880_3 tree_eaa8a880_2 closed_eaa8a880_2 ok_tree_eaa8a880_3
def tree_eaa8a880_4llll : BinaryTree (List W) := (.node [v270,v251,v244,v247,v245] (.node [v271,v242,v244,v272,v245] (.node [v273,v274,v244,v247,v245] (.node [v275,v242,v244,v276,v245] (.node [v277,v242,v278,v247,v245] .nil .nil) .nil) (.node [v271,v242,v243,v244,v245] (.node [v271,v242,v279,v244,v245] .nil .nil) .nil)) (.node [v280,v242,v262,v247,v245] (.node [v280,v242,v281,v247,v245] (.node [v280,v242,v282,v247,v245] .nil .nil) .nil) (.node [v270,v246,v242,v244,v247] (.node [v270,v283,v242,v244,v247] .nil .nil) .nil))) (.node [v284,v242,v244,v247,v245] (.node [v270,v242,v244,v247,v285] (.node [v270,v242,v244,v249,v245] (.node [v270,v242,v252,v247,v245] .nil .nil) .nil) (.node [v270,v242,v244,v247,v286] (.node [v270,v242,v244,v247,v287] .nil .nil) .nil)) (.node [v288,v242,v289,v247,v245] (.node [v288,v290,v244,v247,v245] (.node [v291,v242,v244,v247,v245] .nil .nil) .nil) (.node [v288,v242,v244,v247,v245] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4llll : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4llll = true := by decide +kernel
def tree_eaa8a880_4lllr : BinaryTree (List W) := (.node [v292,v242,v244,v247,v245] (.node [v293,v242,v244,v255,v245] (.node [v293,v254,v244,v247,v294] (.node [v295,v242,v244,v247,v245] (.node [v288,v244,v247,v296,v245] .nil .nil) .nil) (.node [v293,v242,v257,v247,v245] (.node [v293,v242,v297,v244,v245] .nil .nil) .nil)) (.node [v292,v298,v244,v247,v245] (.node [v293,v242,v299,v247,v245] (.node [v293,v242,v244,v247,v245] .nil .nil) .nil) (.node [v292,v242,v244,v300,v245] (.node [v292,v242,v301,v244,v245] .nil .nil) .nil))) (.node [v302,v242,v303,v244,v258] (.node [v304,v242,v305,v247,v258] (.node [v306,v242,v244,v247,v245] (.node [v292,v244,v247,v307,v245] .nil .nil) .nil) (.node [v302,v242,v308,v244,v258] (.node [v304,v242,v309,v247,v258] .nil .nil) .nil)) (.node [v246,v242,v244,v247] (.node [v310,v242,v244,v247,v258] (.node [v283,v246,v242,v244,v247] .nil .nil) .nil) (.node [v246,v242,v244,v247,v260] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4lllr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4lllr = true := by decide +kernel
def tree_eaa8a880_4lll : BinaryTree (List W) := .node [v288,v242,v311,v247,v245] tree_eaa8a880_4llll tree_eaa8a880_4lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4lll : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4lll = true := by
  change (_ && everyKey _ tree_eaa8a880_4llll && everyKey _ tree_eaa8a880_4lllr) = true
  rw [ok_tree_eaa8a880_4llll, ok_tree_eaa8a880_4lllr]
  decide +kernel
def tree_eaa8a880_4llrl : BinaryTree (List W) := (.node [v312,v244,v247,v245,v258] (.node [v313,v247,v314,v245,v258] (.node [v315,v316,v242,v245,v258] (.node [v246,v242,v244,v247,v317] (.node [v246,v242,v244,v247,v258] .nil .nil) .nil) (.node [v313,v265,v247,v245,v258] (.node [v313,v318,v247,v245,v258] .nil .nil) .nil)) (.node [v319,v244,v320,v245,v258] (.node [v319,v244,v321,v245,v258] (.node [v322,v244,v247,v245,v258] .nil .nil) .nil) (.node [v323,v244,v247,v245,v258] (.node [v319,v244,v268,v245,v258] .nil .nil) .nil))) (.node [v324,v244,v325,v245,v258] (.node [v324,v244,v326,v245,v258] (.node [v324,v244,v268,v245,v258] (.node [v324,v327,v244,v245,v258] .nil .nil) .nil) (.node [v324,v244,v328,v245,v258] (.node [v324,v244,v329,v245,v258] .nil .nil) .nil)) (.node [v316,v242,v330,v245,v258] (.node [v316,v242,v331,v245,v258] (.node [v316,v242,v266,v245,v258] .nil .nil) .nil) (.node [v316,v242,v332,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4llrl : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4llrl = true := by decide +kernel
def tree_eaa8a880_4llrr : BinaryTree (List W) := (.node [v254,v244,v255,v258,v294] (.node [v333,v334,v247,v245,v258] (.node [v333,v335,v247,v245,v258] (.node [v333,v265,v247,v245,v258] (.node [v336,v244,v247,v245,v258] .nil .nil) .nil) (.node [v333,v337,v247,v245,v258] (.node [v333,v338,v247,v245,v258] .nil .nil) .nil)) (.node [v254,v257,v247,v245,v258] (.node [v254,v297,v244,v258,v294] (.node [v333,v339,v247,v245,v258] .nil .nil) .nil) (.node [v254,v244,v255,v245,v258] (.node [v254,v257,v247,v258,v294] .nil .nil) .nil))) (.node [v254,v244,v247,v258,v340] (.node [v254,v244,v247,v256,v294] (.node [v254,v244,v247,v245,v256] (.node [v254,v244,v247,v267,v258] .nil .nil) .nil) (.node [v254,v244,v247,v258,v341] (.node [v254,v244,v247,v258,v342] .nil .nil) .nil)) (.node [v274,v244,v247,v343,v245] (.node [v254,v299,v247,v258,v294] (.node [v254,v244,v247,v258,v294] .nil .nil) .nil) (.node [v274,v244,v247,v344,v245] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4llrr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4llrr = true := by decide +kernel
def tree_eaa8a880_4llr : BinaryTree (List W) := .node [v316,v242,v345,v245,v258] tree_eaa8a880_4llrl tree_eaa8a880_4llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4llr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4llr = true := by
  change (_ && everyKey _ tree_eaa8a880_4llrl && everyKey _ tree_eaa8a880_4llrr) = true
  rw [ok_tree_eaa8a880_4llrl, ok_tree_eaa8a880_4llrr]
  decide +kernel
def tree_eaa8a880_4ll : BinaryTree (List W) := .node [v246,v242,v244,v247,v245] tree_eaa8a880_4lll tree_eaa8a880_4llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4ll : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4ll = true := by
  change (_ && everyKey _ tree_eaa8a880_4lll && everyKey _ tree_eaa8a880_4llr) = true
  rw [ok_tree_eaa8a880_4lll, ok_tree_eaa8a880_4llr]
  decide +kernel
def tree_eaa8a880_4lrll : BinaryTree (List W) := (.node [v290,v311,v247,v245,v258] (.node [v346,v244,v247,v245,v258] (.node [v347,v244,v247,v245,v258] (.node [v274,v244,v247,v245,v348] (.node [v274,v244,v247,v245,v349] .nil .nil) .nil) (.node [v350,v244,v247,v245,v258] (.node [v351,v244,v247,v245,v258] .nil .nil) .nil)) (.node [v290,v244,v352,v245,v258] (.node [v290,v289,v247,v245,v258] (.node [v290,v308,v244,v245,v258] .nil .nil) .nil) (.node [v290,v244,v247,v245,v258] (.node [v290,v244,v247,v245,v353] .nil .nil) .nil))) (.node [v298,v244,v247,v245,v354] (.node [v298,v301,v244,v245,v258] (.node [v355,v244,v247,v245,v258] (.node [v356,v244,v247,v245,v258] .nil .nil) .nil) (.node [v298,v244,v300,v245,v258] (.node [v298,v357,v247,v245,v258] .nil .nil) .nil)) (.node [v358,v244,v247,v245,v258] (.node [v298,v305,v247,v245,v258] (.node [v298,v244,v247,v245,v258] .nil .nil) .nil) (.node [v359,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4lrll : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4lrll = true := by decide +kernel
def tree_eaa8a880_4lrlr : BinaryTree (List W) := (.node [v360,v244,v247,v245,v258] (.node [v251,v244,v247,v260,v317] (.node [v251,v252,v247,v245,v258] (.node [v251,v250,v244,v245,v258] (.node [v361,v244,v247,v245,v258] .nil .nil) .nil) (.node [v251,v244,v247,v260,v245] (.node [v251,v244,v249,v245,v258] .nil .nil) .nil)) (.node [v362,v244,v247,v245,v258] (.node [v251,v253,v247,v245,v258] (.node [v251,v244,v247,v245,v258] .nil .nil) .nil) (.node [v363,v244,v247,v245,v258] (.node [v364,v244,v247,v245,v258] .nil .nil) .nil))) (.node [v242,v365,v266,v245,v258] (.node [v242,v265,v247,v245,v258] (.node [v242,v366,v247,v245,v258] (.node [v367,v244,v247,v245,v258] .nil .nil) .nil) (.node [v242,v365,v368,v245,v258] (.node [v242,v365,v369,v245,v258] .nil .nil) .nil)) (.node [v242,v279,v243,v244,v245] (.node [v242,v370,v247,v245,v258] (.node [v242,v371,v247,v245,v258] .nil .nil) .nil) (.node [v242,v279,v244,v245,v372] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4lrlr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4lrlr = true := by decide +kernel
def tree_eaa8a880_4lrl : BinaryTree (List W) := .node [v373,v244,v247,v245,v258] tree_eaa8a880_4lrll tree_eaa8a880_4lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4lrl : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4lrl = true := by
  change (_ && everyKey _ tree_eaa8a880_4lrll && everyKey _ tree_eaa8a880_4lrlr) = true
  rw [ok_tree_eaa8a880_4lrll, ok_tree_eaa8a880_4lrlr]
  decide +kernel
def tree_eaa8a880_4lrrl : BinaryTree (List W) := (.node [v242,v297,v244,v245,v256] (.node [v242,v374,v244,v245,v258] (.node [v242,v308,v244,v375,v258] (.node [v242,v308,v244,v245,v353] (.node [v242,v308,v289,v245,v258] .nil .nil) .nil) (.node [v242,v308,v244,v376,v258] (.node [v242,v308,v244,v377,v258] .nil .nil) .nil)) (.node [v242,v301,v244,v245,v258] (.node [v242,v301,v244,v245,v354] (.node [v242,v378,v244,v245,v258] .nil .nil) .nil) (.node [v242,v297,v257,v245,v258] (.node [v242,v379,v244,v245,v258] .nil .nil) .nil))) (.node [v242,v250,v253,v245,v258] (.node [v242,v250,v252,v245,v258] (.node [v242,v297,v299,v245,v258] (.node [v242,v297,v244,v245,v258] .nil .nil) .nil) (.node [v242,v250,v244,v245,v258] (.node [v242,v250,v244,v260,v317] .nil .nil) .nil)) (.node [v242,v243,v244,v247,v245] (.node [v242,v243,v244,v276,v245] (.node [v242,v380,v244,v245,v258] .nil .nil) .nil) (.node [v242,v243,v244,v245] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4lrrl : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4lrrl = true := by decide +kernel
def tree_eaa8a880_4lrrr : BinaryTree (List W) := (.node [v242,v278,v247,v245,v381] (.node [v242,v357,v300,v245,v258] (.node [v242,v303,v244,v245,v258] (.node [v242,v303,v244,v247,v258] (.node [v242,v243,v244,v245,v382] .nil .nil) .nil) (.node [v242,v383,v247,v245,v258] (.node [v242,v384,v247,v245,v258] .nil .nil) .nil)) (.node [v242,v278,v262,v247,v245] (.node [v242,v357,v247,v258,v341] (.node [v242,v357,v247,v245,v354] .nil .nil) .nil) (.node [v242,v278,v247,v245,v385] (.node [v242,v278,v247,v386,v245] .nil .nil) .nil))) (.node [v242,v257,v247,v245,v256] (.node [v242,v387,v247,v245,v258] (.node [v242,v388,v247,v245,v258] (.node [v242,v278,v247,v245,v389] .nil .nil) .nil) (.node [v242,v257,v255,v245,v258] (.node [v242,v390,v247,v245,v258] .nil .nil) .nil)) (.node [v242,v391,v247,v245,v258] (.node [v242,v392,v247,v245,v258] (.node [v242,v257,v247,v245,v258] .nil .nil) .nil) (.node [v242,v393,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4lrrr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4lrrr = true := by decide +kernel
def tree_eaa8a880_4lrr : BinaryTree (List W) := .node [v242,v243,v244,v245,v258] tree_eaa8a880_4lrrl tree_eaa8a880_4lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4lrr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4lrr = true := by
  change (_ && everyKey _ tree_eaa8a880_4lrrl && everyKey _ tree_eaa8a880_4lrrr) = true
  rw [ok_tree_eaa8a880_4lrrl, ok_tree_eaa8a880_4lrrr]
  decide +kernel
def tree_eaa8a880_4lr : BinaryTree (List W) := .node [v242,v308,v303,v244,v258] tree_eaa8a880_4lrl tree_eaa8a880_4lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4lr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4lr = true := by
  change (_ && everyKey _ tree_eaa8a880_4lrl && everyKey _ tree_eaa8a880_4lrr) = true
  rw [ok_tree_eaa8a880_4lrl, ok_tree_eaa8a880_4lrr]
  decide +kernel
def tree_eaa8a880_4l : BinaryTree (List W) := .node [v274,v244,v247,v245,v394] tree_eaa8a880_4ll tree_eaa8a880_4lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4l : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4l = true := by
  change (_ && everyKey _ tree_eaa8a880_4ll && everyKey _ tree_eaa8a880_4lr) = true
  rw [ok_tree_eaa8a880_4ll, ok_tree_eaa8a880_4lr]
  decide +kernel
def tree_eaa8a880_4rlll : BinaryTree (List W) := (.node [v242,v395,v247,v245,v258] (.node [v242,v252,v249,v245,v258] (.node [v242,v289,v247,v245,v258] (.node [v242,v289,v247,v245,v353] (.node [v242,v289,v352,v245,v258] .nil .nil) .nil) (.node [v242,v396,v247,v245,v258] (.node [v242,v397,v247,v245,v258] .nil .nil) .nil)) (.node [v242,v252,v247,v245,v258] (.node [v242,v252,v247,v260,v317] (.node [v242,v252,v247,v260,v245] .nil .nil) .nil) (.node [v242,v398,v247,v245,v258] (.node [v242,v399,v247,v245,v258] .nil .nil) .nil))) (.node [v242,v244,v262,v247,v245] (.node [v242,v244,v400,v245,v258] (.node [v242,v401,v247,v245,v258] (.node [v242,v402,v247,v245,v258] .nil .nil) .nil) (.node [v242,v244,v403,v245,v258] (.node [v242,v244,v404,v245,v258] .nil .nil) .nil)) (.node [v242,v244,v405,v245,v258] (.node [v242,v244,v268,v245,v258] (.node [v242,v244,v309,v247,v258] .nil .nil) .nil) (.node [v242,v244,v352,v245,v353] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rlll : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rlll = true := by decide +kernel
def tree_eaa8a880_4rllr : BinaryTree (List W) := (.node [v242,v244,v406,v245,v258] (.node [v242,v244,v407,v245,v258] (.node [v242,v244,v276,v245,v408] (.node [v242,v244,v276,v245,v409] (.node [v242,v244,v276,v410,v245] .nil .nil) .nil) (.node [v242,v244,v411,v245,v258] (.node [v242,v244,v276,v245,v382] .nil .nil) .nil)) (.node [v242,v244,v255,v245,v256] (.node [v242,v244,v412,v245,v258] (.node [v242,v244,v413,v245,v258] .nil .nil) .nil) (.node [v242,v244,v414,v245,v258] (.node [v242,v244,v255,v245,v258] .nil .nil) .nil))) (.node [v242,v244,v249,v260,v245] (.node [v242,v244,v300,v245,v258] (.node [v242,v244,v300,v245,v354] (.node [v242,v244,v415,v245,v258] .nil .nil) .nil) (.node [v242,v244,v416,v245,v258] (.node [v242,v244,v417,v245,v258] .nil .nil) .nil)) (.node [v242,v244,v418,v245,v258] (.node [v242,v244,v249,v245,v258] (.node [v242,v244,v249,v260,v317] .nil .nil) .nil) (.node [v242,v244,v419,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rllr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rllr = true := by decide +kernel
def tree_eaa8a880_4rll : BinaryTree (List W) := .node [v242,v244,v352,v258,v342] tree_eaa8a880_4rlll tree_eaa8a880_4rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rll : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rll = true := by
  change (_ && everyKey _ tree_eaa8a880_4rlll && everyKey _ tree_eaa8a880_4rllr) = true
  rw [ok_tree_eaa8a880_4rlll, ok_tree_eaa8a880_4rllr]
  decide +kernel
def tree_eaa8a880_4rlrl : BinaryTree (List W) := (.node [v242,v244,v247,v260,v420] (.node [v242,v244,v247,v421,v245] (.node [v242,v244,v422,v245,v258] (.node [v242,v244,v423,v245,v258] (.node [v242,v244,v424,v245,v258] .nil .nil) .nil) (.node [v242,v244,v247,v267,v258] (.node [v242,v244,v247,v343,v245] .nil .nil) .nil)) (.node [v242,v244,v247,v425,v245] (.node [v242,v244,v247,v426,v245] (.node [v242,v244,v247,v427,v245] .nil .nil) .nil) (.node [v242,v244,v247,v260,v340] (.node [v242,v244,v247,v428,v245] .nil .nil) .nil))) (.node [v242,v244,v247,v429,v258] (.node [v242,v244,v247,v430,v258] (.node [v242,v244,v247,v260,v317] (.node [v242,v244,v247,v260,v431] .nil .nil) .nil) (.node [v242,v244,v247,v432,v258] (.node [v242,v244,v247,v433,v258] .nil .nil) .nil)) (.node [v242,v244,v247,v245,v434] (.node [v242,v244,v247,v245,v435] (.node [v242,v244,v247,v245,v436] .nil .nil) .nil) (.node [v242,v244,v247,v245,v256] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rlrl : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rlrl = true := by decide +kernel
def tree_eaa8a880_4rlrr : BinaryTree (List W) := (.node [v242,v244,v247,v245,v437] (.node [v242,v244,v247,v245,v438] (.node [v242,v244,v247,v245,v439] (.node [v242,v244,v247,v245,v440] (.node [v242,v244,v247,v245,v441] .nil .nil) .nil) (.node [v242,v244,v247,v245,v442] (.node [v242,v244,v247,v245,v354] .nil .nil) .nil)) (.node [v242,v244,v247,v245,v443] (.node [v242,v244,v247,v245,v444] (.node [v242,v244,v247,v245,v353] .nil .nil) .nil) (.node [v242,v244,v247,v245,v445] (.node [v242,v244,v247,v245,v446] .nil .nil) .nil))) (.node [v242,v244,v247,v245,v447] (.node [v242,v244,v247,v245,v448] (.node [v242,v244,v247,v245,v449] (.node [v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v242,v244,v247,v245,v450] (.node [v242,v244,v247,v245,v451] .nil .nil) .nil)) (.node [v242,v244,v247,v245,v452] (.node [v242,v244,v247,v245,v453] (.node [v242,v244,v247,v245,v454] .nil .nil) .nil) (.node [v242,v244,v247,v245,v455] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rlrr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rlrr = true := by decide +kernel
def tree_eaa8a880_4rlr : BinaryTree (List W) := .node [v242,v244,v247,v245,v456] tree_eaa8a880_4rlrl tree_eaa8a880_4rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rlr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rlr = true := by
  change (_ && everyKey _ tree_eaa8a880_4rlrl && everyKey _ tree_eaa8a880_4rlrr) = true
  rw [ok_tree_eaa8a880_4rlrl, ok_tree_eaa8a880_4rlrr]
  decide +kernel
def tree_eaa8a880_4rl : BinaryTree (List W) := .node [v242,v244,v457,v245,v258] tree_eaa8a880_4rll tree_eaa8a880_4rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rl : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rl = true := by
  change (_ && everyKey _ tree_eaa8a880_4rll && everyKey _ tree_eaa8a880_4rlr) = true
  rw [ok_tree_eaa8a880_4rll, ok_tree_eaa8a880_4rlr]
  decide +kernel
def tree_eaa8a880_4rrll : BinaryTree (List W) := (.node [v242,v458,v247,v245,v258] (.node [v242,v244,v459,v245,v258] (.node [v242,v244,v460,v245,v258] (.node [v242,v244,v461,v245,v258] (.node [v242,v244,v462,v245,v258] .nil .nil) .nil) (.node [v242,v244,v463,v245,v258] (.node [v242,v244,v464,v245,v258] .nil .nil) .nil)) (.node [v242,v244,v465,v245,v258] (.node [v242,v244,v466,v245,v258] (.node [v242,v244,v266,v245,v258] .nil .nil) .nil) (.node [v242,v467,v247,v245,v258] (.node [v242,v468,v247,v245,v258] .nil .nil) .nil))) (.node [v242,v368,v266,v245,v258] (.node [v242,v469,v247,v245,v258] (.node [v242,v470,v247,v245,v258] (.node [v242,v471,v247,v245,v258] .nil .nil) .nil) (.node [v242,v368,v472,v245,v258] (.node [v242,v473,v247,v245,v258] .nil .nil) .nil)) (.node [v242,v305,v309,v247,v258] (.node [v242,v281,v247,v245,v474] (.node [v242,v281,v262,v247,v245] .nil .nil) .nil) (.node [v242,v305,v300,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rrll : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rrll = true := by decide +kernel
def tree_eaa8a880_4rrlr : BinaryTree (List W) := (.node [v242,v253,v249,v245,v258] (.node [v242,v299,v255,v245,v258] (.node [v242,v305,v247,v475,v258] (.node [v242,v305,v247,v476,v258] (.node [v242,v305,v247,v477,v258] .nil .nil) .nil) (.node [v242,v478,v247,v245,v258] (.node [v242,v479,v247,v245,v258] .nil .nil) .nil)) (.node [v242,v480,v247,v245,v258] (.node [v242,v299,v247,v245,v258] (.node [v242,v299,v247,v245,v256] .nil .nil) .nil) (.node [v242,v311,v247,v245,v258] (.node [v242,v311,v247,v245,v353] .nil .nil) .nil))) (.node [v242,v262,v247,v245,v389] (.node [v242,v481,v247,v245,v258] (.node [v242,v253,v247,v245,v258] (.node [v242,v253,v247,v260,v317] .nil .nil) .nil) (.node [v242,v262,v247,v245,v258] (.node [v242,v262,v247,v245] .nil .nil) .nil)) (.node [v242,v247,v482,v245,v258] (.node [v242,v247,v266,v245,v258] (.node [v242,v309,v247,v245,v258] .nil .nil) .nil) (.node [v242,v247,v483,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rrlr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rrlr = true := by decide +kernel
def tree_eaa8a880_4rrl : BinaryTree (List W) := .node [v242,v305,v247,v245,v354] tree_eaa8a880_4rrll tree_eaa8a880_4rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rrl : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rrl = true := by
  change (_ && everyKey _ tree_eaa8a880_4rrll && everyKey _ tree_eaa8a880_4rrlr) = true
  rw [ok_tree_eaa8a880_4rrll, ok_tree_eaa8a880_4rrlr]
  decide +kernel
def tree_eaa8a880_4rrrl : BinaryTree (List W) := (.node [v301,v244,v307,v245,v258] (.node [v484,v244,v247,v245,v258] (.node [v485,v244,v247,v245,v258] (.node [v486,v244,v247,v245,v258] (.node [v242,v266,v245,v258] .nil .nil) .nil) (.node [v487,v244,v247,v245,v258] (.node [v488,v244,v247,v245,v258] .nil .nil) .nil)) (.node [v265,v244,v247,v245,v258] (.node [v318,v247,v489,v245,v258] (.node [v318,v265,v247,v245,v258] .nil .nil) .nil) (.node [v265,v247,v245,v258] (.node [v265,v334,v247,v245,v258] .nil .nil) .nil))) (.node [v244,v490,v247,v245,v258] (.node [v289,v247,v296,v245,v258] (.node [v257,v247,v491,v245,v258] (.node [v250,v244,v248,v245,v258] .nil .nil) .nil) (.node [v244,v492,v247,v245,v258] (.node [v252,v247,v248,v245,v258] .nil .nil) .nil)) (.node [v244,v268,v247,v245,v258] (.node [v244,v320,v493,v245,v258] (.node [v244,v320,v268,v245,v258] .nil .nil) .nil) (.node [v244,v268,v325,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rrrl : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rrrl = true := by decide +kernel
def tree_eaa8a880_4rrrr : BinaryTree (List W) := (.node [v244,v247,v307,v245,v258] (.node [v244,v247,v343,v245,v258] (.node [v244,v249,v248,v245,v258] (.node [v244,v300,v307,v245,v258] (.node [v244,v255,v491,v245,v258] .nil .nil) .nil) (.node [v244,v247,v494,v245,v258] (.node [v244,v247,v495,v245,v258] .nil .nil) .nil)) (.node [v244,v247,v496,v245,v258] (.node [v244,v247,v491,v245,v256] (.node [v244,v247,v343,v245,v348] .nil .nil) .nil) (.node [v244,v247,v307,v245,v354] (.node [v244,v247,v497,v245,v258] .nil .nil) .nil))) (.node [v244,v247,v498,v245,v258] (.node [v244,v247,v296,v245,v258] (.node [v244,v247,v296,v245,v353] (.node [v244,v247,v499,v245,v258] .nil .nil) .nil) (.node [v244,v247,v248,v245,v258] (.node [v244,v247,v248,v260,v317] .nil .nil) .nil)) (.node [v311,v247,v296,v245,v258] (.node [v244,v247,v267,v258,v294] (.node [v244,v247,v267,v245,v258] .nil .nil) .nil) (.node [v253,v247,v248,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rrrr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rrrr = true := by decide +kernel
def tree_eaa8a880_4rrr : BinaryTree (List W) := .node [v244,v268,v245,v258] tree_eaa8a880_4rrrl tree_eaa8a880_4rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rrr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rrr = true := by
  change (_ && everyKey _ tree_eaa8a880_4rrrl && everyKey _ tree_eaa8a880_4rrrr) = true
  rw [ok_tree_eaa8a880_4rrrl, ok_tree_eaa8a880_4rrrr]
  decide +kernel
def tree_eaa8a880_4rr : BinaryTree (List W) := .node [v242,v266,v345,v245,v258] tree_eaa8a880_4rrl tree_eaa8a880_4rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4rr : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4rr = true := by
  change (_ && everyKey _ tree_eaa8a880_4rrl && everyKey _ tree_eaa8a880_4rrr) = true
  rw [ok_tree_eaa8a880_4rrl, ok_tree_eaa8a880_4rrr]
  decide +kernel
def tree_eaa8a880_4r : BinaryTree (List W) := .node [v242,v244,v500,v245,v258] tree_eaa8a880_4rl tree_eaa8a880_4rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4r : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4r = true := by
  change (_ && everyKey _ tree_eaa8a880_4rl && everyKey _ tree_eaa8a880_4rr) = true
  rw [ok_tree_eaa8a880_4rl, ok_tree_eaa8a880_4rr]
  decide +kernel
def tree_eaa8a880_4 : BinaryTree (List W) := .node [v242,v501,v247,v245,v258] tree_eaa8a880_4l tree_eaa8a880_4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_4 : everyKey (rowOK 3 tree_eaa8a880_3) tree_eaa8a880_4 = true := by
  change (_ && everyKey _ tree_eaa8a880_4l && everyKey _ tree_eaa8a880_4r) = true
  rw [ok_tree_eaa8a880_4l, ok_tree_eaa8a880_4r]
  decide +kernel
theorem closed_eaa8a880_4 : Closed 4 tree_eaa8a880_4 := closed_next 3 (by decide) tree_eaa8a880_4 tree_eaa8a880_3 closed_eaa8a880_3 ok_tree_eaa8a880_4
def tree_eaa8a880_5lllll : BinaryTree (List W) := (.node [v502,v242,v244,v247,v245,v258] (.node [v503,v242,v244,v247,v245,v258] (.node [v504,v242,v244,v247,v245,v258] (.node [v505,v242,v244,v247,v245,v258] (.node [v506,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v507,v242,v244,v247,v245,v258] .nil .nil)) (.node [v508,v242,v244,v247,v245,v258] (.node [v509,v242,v244,v247,v245,v258] .nil .nil) (.node [v510,v242,v244,v247,v245,v258] .nil .nil))) (.node [v511,v242,v244,v247,v245,v258] (.node [v512,v242,v244,v247,v245,v258] (.node [v513,v242,v244,v247,v245,v258] (.node [v514,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v515,v242,v244,v247,v245,v258] .nil .nil)) (.node [v277,v242,v244,v247,v245,v258] (.node [v516,v242,v244,v247,v245,v258] .nil .nil) (.node [v517,v242,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lllll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lllll = true := by decide +kernel
def tree_eaa8a880_5llllr : BinaryTree (List W) := (.node [v518,v242,v244,v247,v260,v245] (.node [v519,v242,v244,v247,v245,v258] (.node [v275,v242,v244,v247,v245,v258] (.node [v520,v242,v244,v247,v245,v258] (.node [v521,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v522,v242,v244,v247,v245,v258] .nil .nil)) (.node [v518,v274,v244,v247,v245,v258] (.node [v518,v270,v242,v244,v247,v245] .nil .nil) (.node [v518,v242,v244,v247,v523,v245] .nil .nil))) (.node [v524,v242,v244,v247,v245,v258] (.node [v518,v242,v244,v247,v245,v348] (.node [v518,v242,v244,v247,v245,v258] .nil .nil) (.node [v518,v244,v247,v523,v245,v258] .nil .nil)) (.node [v273,v242,v244,v247,v245,v258] (.node [v525,v242,v244,v247,v245,v258] .nil .nil) (.node [v526,v242,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5llllr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5llllr = true := by decide +kernel
def tree_eaa8a880_5llll : BinaryTree (List W) := .node [v527,v242,v244,v247,v245,v258] tree_eaa8a880_5lllll tree_eaa8a880_5llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5llll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5llll = true := by
  change (_ && everyKey _ tree_eaa8a880_5lllll && everyKey _ tree_eaa8a880_5llllr) = true
  rw [ok_tree_eaa8a880_5lllll, ok_tree_eaa8a880_5llllr]
  decide +kernel
def tree_eaa8a880_5lllrl : BinaryTree (List W) := (.node [v528,v242,v244,v247,v245,v258] (.node [v271,v242,v244,v276,v245,v258] (.node [v271,v242,v279,v244,v245] (.node [v271,v242,v279,v244,v247,v245] (.node [v271,v270,v242,v244,v247,v245] .nil .nil) .nil) (.node [v271,v242,v279,v244,v245,v258] .nil .nil)) (.node [v271,v242,v244,v247,v245,v258] (.node [v271,v242,v244,v247,v260,v245] .nil .nil) (.node [v271,v242,v244,v247,v245,v382] .nil .nil))) (.node [v280,v242,v244,v247,v245,v258] (.node [v280,v242,v244,v281,v247,v245] (.node [v280,v242,v278,v247,v245,v258] (.node [v280,v270,v242,v244,v247,v245] .nil .nil) .nil) (.node [v280,v242,v244,v247,v260,v245] .nil .nil)) (.node [v280,v242,v281,v247,v245] (.node [v280,v242,v244,v247,v245,v389] .nil .nil) (.node [v280,v242,v281,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lllrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lllrl = true := by decide +kernel
def tree_eaa8a880_5lllrr : BinaryTree (List W) := (.node [v270,v242,v244,v247,v245,v258] (.node [v270,v274,v242,v244,v247,v245] (.node [v270,v283,v242,v244,v247,v245] (.node [v270,v283,v242,v244,v247] (.node [v529,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v270,v283,v242,v244,v247,v258] .nil .nil)) (.node [v270,v242,v244,v276,v247,v245] (.node [v270,v242,v278,v244,v247,v245] .nil .nil) (.node [v270,v242,v244,v247,v260,v258] .nil .nil))) (.node [v288,v242,v244,v247,v245,v258] (.node [v530,v242,v244,v247,v245,v258] (.node [v270,v242,v244,v247,v245,v317] .nil .nil) (.node [v288,v242,v244,v247,v245] .nil .nil)) (.node [v293,v242,v244,v247,v245] (.node [v288,v242,v244,v247,v245,v531] .nil .nil) (.node [v293,v242,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lllrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lllrr = true := by decide +kernel
def tree_eaa8a880_5lllr : BinaryTree (List W) := .node [v532,v242,v244,v247,v245,v258] tree_eaa8a880_5lllrl tree_eaa8a880_5lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lllr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lllr = true := by
  change (_ && everyKey _ tree_eaa8a880_5lllrl && everyKey _ tree_eaa8a880_5lllrr) = true
  rw [ok_tree_eaa8a880_5lllrl, ok_tree_eaa8a880_5lllrr]
  decide +kernel
def tree_eaa8a880_5lll : BinaryTree (List W) := .node [v533,v242,v244,v247,v245,v258] tree_eaa8a880_5llll tree_eaa8a880_5lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lll = true := by
  change (_ && everyKey _ tree_eaa8a880_5llll && everyKey _ tree_eaa8a880_5lllr) = true
  rw [ok_tree_eaa8a880_5llll, ok_tree_eaa8a880_5lllr]
  decide +kernel
def tree_eaa8a880_5llrll : BinaryTree (List W) := (.node [v534,v242,v244,v247,v245,v258] (.node [v535,v242,v244,v247,v245,v258] (.node [v292,v242,v244,v247,v245,v536] (.node [v292,v242,v244,v247,v245,v258] (.node [v292,v242,v244,v247,v245] .nil .nil) .nil) (.node [v537,v242,v244,v247,v245,v258] .nil .nil)) (.node [v534,v254,v244,v247,v245,v258] (.node [v538,v242,v244,v247,v245,v258] .nil .nil) (.node [v534,v242,v244,v247,v491,v258] .nil .nil))) (.node [v304,v242,v357,v247,v245,v258] (.node [v539,v242,v244,v247,v245,v258] (.node [v534,v244,v247,v491,v245,v258] (.node [v534,v242,v244,v247,v258,v294] .nil .nil) .nil) (.node [v540,v242,v244,v247,v245,v258] .nil .nil)) (.node [v304,v242,v244,v247,v245,v258] (.node [v304,v242,v244,v305,v247,v258] .nil .nil) (.node [v304,v242,v244,v247,v258,v536] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5llrll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5llrll = true := by decide +kernel
def tree_eaa8a880_5llrlr : BinaryTree (List W) := (.node [v302,v242,v244,v247,v258,v531] (.node [v302,v242,v308,v244,v245,v258] (.node [v541,v242,v244,v247,v245,v258] (.node [v542,v242,v244,v247,v245,v258] (.node [v304,v242,v305,v247,v258] .nil .nil) .nil) (.node [v302,v242,v308,v244,v247,v258] .nil .nil)) (.node [v302,v242,v244,v352,v245,v258] (.node [v302,v242,v308,v244,v258] .nil .nil) (.node [v302,v242,v244,v247,v245,v258] .nil .nil))) (.node [v283,v242,v244,v247,v258,v317] (.node [v283,v242,v244,v247,v260,v245] (.node [v543,v242,v244,v247,v245,v258] .nil .nil) (.node [v283,v242,v244,v247,v245,v258] .nil .nil)) (.node [v544,v242,v244,v247,v245,v258] (.node [v545,v242,v244,v247,v245,v258] .nil .nil) (.node [v546,v242,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5llrlr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5llrlr = true := by decide +kernel
def tree_eaa8a880_5llrl : BinaryTree (List W) := .node [v304,v242,v305,v247,v245,v258] tree_eaa8a880_5llrll tree_eaa8a880_5llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5llrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5llrl = true := by
  change (_ && everyKey _ tree_eaa8a880_5llrll && everyKey _ tree_eaa8a880_5llrlr) = true
  rw [ok_tree_eaa8a880_5llrll, ok_tree_eaa8a880_5llrlr]
  decide +kernel
def tree_eaa8a880_5llrrl : BinaryTree (List W) := (.node [v547,v242,v244,v247,v245,v258] (.node [v548,v242,v244,v247,v245,v258] (.node [v549,v242,v244,v247,v245,v258] (.node [v550,v242,v244,v247,v245,v258] (.node [v551,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v552,v242,v244,v247,v245,v258] .nil .nil)) (.node [v553,v242,v244,v247,v245,v258] (.node [v315,v242,v244,v247,v245,v258] .nil .nil) (.node [v554,v242,v244,v247,v245,v258] .nil .nil))) (.node [v313,v242,v334,v247,v245,v258] (.node [v313,v242,v357,v247,v245,v258] (.node [v313,v242,v318,v247,v245,v258] (.node [v313,v333,v244,v247,v245,v258] .nil .nil) .nil) (.node [v313,v242,v244,v247,v245,v258] .nil .nil)) (.node [v313,v318,v244,v247,v245,v258] (.node [v313,v242,v305,v247,v245,v258] .nil .nil) (.node [v313,v318,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5llrrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5llrrl = true := by decide +kernel
def tree_eaa8a880_5llrrr : BinaryTree (List W) := (.node [v319,v242,v244,v247,v245,v258] (.node [v319,v324,v244,v247,v245,v258] (.node [v555,v242,v244,v247,v245,v258] (.node [v556,v242,v244,v247,v245,v258] (.node [v557,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v558,v242,v244,v247,v245,v258] .nil .nil)) (.node [v319,v242,v244,v320,v245,v258] (.node [v319,v242,v308,v244,v245,v258] .nil .nil) (.node [v319,v242,v244,v352,v245,v258] .nil .nil))) (.node [v559,v242,v244,v247,v245,v258] (.node [v319,v244,v320,v247,v245,v258] (.node [v319,v242,v244,v325,v245,v258] .nil .nil) (.node [v319,v244,v320,v245,v258] .nil .nil)) (.node [v560,v242,v244,v247,v245,v258] (.node [v561,v242,v244,v247,v245,v258] .nil .nil) (.node [v562,v242,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5llrrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5llrrr = true := by decide +kernel
def tree_eaa8a880_5llrr : BinaryTree (List W) := .node [v563,v242,v244,v247,v245,v258] tree_eaa8a880_5llrrl tree_eaa8a880_5llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5llrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5llrr = true := by
  change (_ && everyKey _ tree_eaa8a880_5llrrl && everyKey _ tree_eaa8a880_5llrrr) = true
  rw [ok_tree_eaa8a880_5llrrl, ok_tree_eaa8a880_5llrrr]
  decide +kernel
def tree_eaa8a880_5llr : BinaryTree (List W) := .node [v564,v242,v244,v247,v245,v258] tree_eaa8a880_5llrl tree_eaa8a880_5llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5llr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5llr = true := by
  change (_ && everyKey _ tree_eaa8a880_5llrl && everyKey _ tree_eaa8a880_5llrr) = true
  rw [ok_tree_eaa8a880_5llrl, ok_tree_eaa8a880_5llrr]
  decide +kernel
def tree_eaa8a880_5ll : BinaryTree (List W) := .node [v293,v242,v244,v247,v245,v294] tree_eaa8a880_5lll tree_eaa8a880_5llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5ll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5ll = true := by
  change (_ && everyKey _ tree_eaa8a880_5lll && everyKey _ tree_eaa8a880_5llr) = true
  rw [ok_tree_eaa8a880_5lll, ok_tree_eaa8a880_5llr]
  decide +kernel
def tree_eaa8a880_5lrlll : BinaryTree (List W) := (.node [v324,v244,v247,v491,v245,v258] (.node [v324,v242,v244,v352,v245,v258] (.node [v324,v242,v308,v244,v245,v258] (.node [v324,v254,v244,v247,v245,v258] (.node [v565,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v324,v242,v244,v320,v245,v258] .nil .nil)) (.node [v324,v242,v244,v325,v245,v258] (.node [v324,v242,v244,v247,v245,v258] .nil .nil) (.node [v324,v244,v247,v325,v245,v258] .nil .nil))) (.node [v566,v242,v244,v247,v245,v258] (.node [v567,v242,v244,v247,v245,v258] (.node [v568,v242,v244,v247,v245,v258] (.node [v324,v244,v325,v245,v258] .nil .nil) .nil) (.node [v569,v242,v244,v247,v245,v258] .nil .nil)) (.node [v570,v242,v244,v247,v245,v258] (.node [v571,v242,v244,v247,v245,v258] .nil .nil) (.node [v316,v242,v365,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrlll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrlll = true := by decide +kernel
def tree_eaa8a880_5lrllr : BinaryTree (List W) := (.node [v572,v242,v244,v247,v245,v258] (.node [v316,v242,v244,v345,v245,v258] (.node [v316,v242,v244,v352,v245,v258] (.node [v316,v242,v244,v368,v245,v258] (.node [v316,v242,v357,v247,v245,v258] .nil .nil) .nil) (.node [v316,v242,v244,v247,v245,v258] .nil .nil)) (.node [v316,v242,v247,v345,v245,v258] (.node [v316,v242,v305,v247,v245,v258] .nil .nil) (.node [v316,v242,v345,v245,v258] .nil .nil))) (.node [v573,v242,v244,v247,v245,v258] (.node [v574,v242,v244,v247,v245,v258] (.node [v575,v242,v244,v247,v245,v258] .nil .nil) (.node [v576,v242,v244,v247,v245,v258] .nil .nil)) (.node [v577,v242,v244,v247,v245,v258] (.node [v578,v242,v244,v247,v245,v258] .nil .nil) (.node [v579,v242,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrllr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrllr = true := by decide +kernel
def tree_eaa8a880_5lrll : BinaryTree (List W) := .node [v316,v242,v308,v244,v245,v258] tree_eaa8a880_5lrlll tree_eaa8a880_5lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrll = true := by
  change (_ && everyKey _ tree_eaa8a880_5lrlll && everyKey _ tree_eaa8a880_5lrllr) = true
  rw [ok_tree_eaa8a880_5lrlll, ok_tree_eaa8a880_5lrllr]
  decide +kernel
def tree_eaa8a880_5lrlrl : BinaryTree (List W) := (.node [v580,v242,v244,v247,v245,v258] (.node [v333,v242,v305,v247,v245,v258] (.node [v333,v242,v244,v247,v245,v258] (.node [v333,v242,v357,v247,v245,v258] (.node [v333,v242,v318,v247,v245,v258] .nil .nil) .nil) (.node [v333,v242,v334,v247,v245,v258] .nil .nil)) (.node [v333,v244,v247,v491,v245,v258] (.node [v333,v244,v334,v247,v245,v258] .nil .nil) (.node [v333,v334,v247,v245,v258] .nil .nil))) (.node [v581,v242,v244,v247,v245,v258] (.node [v582,v242,v244,v247,v245,v258] (.node [v583,v242,v244,v247,v245,v258] (.node [v584,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v585,v242,v244,v247,v245,v258] .nil .nil)) (.node [v254,v274,v244,v247,v245,v258] (.node [v586,v242,v244,v247,v245,v258] .nil .nil) (.node [v254,v242,v244,v247,v491,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrlrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrlrl = true := by decide +kernel
def tree_eaa8a880_5lrlrr : BinaryTree (List W) := (.node [v587,v242,v244,v247,v245,v258] (.node [v254,v244,v247,v245,v258,v294] (.node [v254,v244,v320,v247,v245,v258] (.node [v254,v318,v244,v247,v245,v258] (.node [v254,v242,v244,v247,v258,v294] .nil .nil) .nil) (.node [v254,v244,v247,v523,v245,v258] .nil .nil)) (.node [v588,v242,v244,v247,v245,v258] (.node [v254,v244,v247,v258,v294] .nil .nil) (.node [v589,v242,v244,v247,v245,v258] .nil .nil))) (.node [v274,v242,v244,v247,v245,v258] (.node [v274,v242,v244,v247,v523,v245] (.node [v590,v242,v244,v247,v245,v258] .nil .nil) (.node [v274,v242,v244,v247,v260,v245] .nil .nil)) (.node [v274,v244,v247,v491,v245,v258] (.node [v274,v242,v244,v247,v245,v348] .nil .nil) (.node [v274,v244,v247,v245,v258,v348] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrlrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrlrr = true := by decide +kernel
def tree_eaa8a880_5lrlr : BinaryTree (List W) := .node [v254,v242,v244,v247,v245,v258] tree_eaa8a880_5lrlrl tree_eaa8a880_5lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrlr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrlr = true := by
  change (_ && everyKey _ tree_eaa8a880_5lrlrl && everyKey _ tree_eaa8a880_5lrlrr) = true
  rw [ok_tree_eaa8a880_5lrlrl, ok_tree_eaa8a880_5lrlrr]
  decide +kernel
def tree_eaa8a880_5lrl : BinaryTree (List W) := .node [v333,v254,v244,v247,v245,v258] tree_eaa8a880_5lrll tree_eaa8a880_5lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrl = true := by
  change (_ && everyKey _ tree_eaa8a880_5lrll && everyKey _ tree_eaa8a880_5lrlr) = true
  rw [ok_tree_eaa8a880_5lrll, ok_tree_eaa8a880_5lrlr]
  decide +kernel
def tree_eaa8a880_5lrrll : BinaryTree (List W) := (.node [v290,v244,v247,v245,v258] (.node [v591,v242,v244,v247,v245,v258] (.node [v592,v242,v244,v247,v245,v258] (.node [v593,v242,v244,v247,v245,v258] (.node [v594,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v595,v242,v244,v247,v245,v258] .nil .nil)) (.node [v596,v242,v244,v247,v245,v258] (.node [v597,v242,v244,v247,v245,v258] .nil .nil) (.node [v290,v242,v244,v247,v245,v258] .nil .nil))) (.node [v251,v242,v244,v247,v245,v258] (.node [v298,v244,v247,v245,v258] (.node [v298,v242,v244,v247,v245,v258] (.node [v290,v244,v247,v245,v258,v531] .nil .nil) .nil) (.node [v298,v244,v247,v245,v258,v536] .nil .nil)) (.node [v251,v244,v247,v245,v258,v317] (.node [v251,v244,v247,v245,v258] .nil .nil) (.node [v242,v242,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrrll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrrll = true := by decide +kernel
def tree_eaa8a880_5lrrlr : BinaryTree (List W) := (.node [v242,v327,v244,v247,v245,v258] (.node [v242,v598,v244,v247,v245,v258] (.node [v242,v599,v244,v247,v245,v258] (.node [v242,v600,v244,v247,v245,v258] (.node [v242,v601,v244,v247,v245,v258] .nil .nil) .nil) (.node [v242,v602,v244,v247,v245,v258] .nil .nil)) (.node [v242,v603,v244,v247,v245,v258] (.node [v242,v604,v244,v247,v245,v258] .nil .nil) (.node [v242,v605,v244,v247,v245,v258] .nil .nil))) (.node [v242,v606,v244,v247,v245,v258] (.node [v242,v607,v244,v247,v245,v258] (.node [v242,v608,v244,v247,v245,v258] .nil .nil) (.node [v242,v318,v244,v247,v245,v258] .nil .nil)) (.node [v242,v609,v244,v247,v245,v258] (.node [v242,v610,v244,v247,v245,v258] .nil .nil) (.node [v242,v611,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrrlr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrrlr = true := by decide +kernel
def tree_eaa8a880_5lrrl : BinaryTree (List W) := .node [v242,v612,v244,v247,v245,v258] tree_eaa8a880_5lrrll tree_eaa8a880_5lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrrl = true := by
  change (_ && everyKey _ tree_eaa8a880_5lrrll && everyKey _ tree_eaa8a880_5lrrlr) = true
  rw [ok_tree_eaa8a880_5lrrll, ok_tree_eaa8a880_5lrrlr]
  decide +kernel
def tree_eaa8a880_5lrrrl : BinaryTree (List W) := (.node [v242,v613,v244,v247,v245,v258] (.node [v242,v365,v368,v247,v245,v258] (.node [v242,v365,v244,v247,v245,v258] (.node [v242,v365,v244,v352,v245,v258] (.node [v242,v365,v244,v368,v245,v258] .nil .nil) .nil) (.node [v242,v365,v244,v345,v245,v258] .nil .nil)) (.node [v242,v614,v244,v247,v245,v258] (.node [v242,v365,v368,v245,v258] .nil .nil) (.node [v242,v615,v244,v247,v245,v258] .nil .nil))) (.node [v242,v279,v244,v247,v245,v258] (.node [v242,v279,v244,v352,v245,v258] (.node [v242,v279,v308,v244,v245,v258] (.node [v242,v616,v244,v247,v245,v258] .nil .nil) .nil) (.node [v242,v279,v244,v276,v247,v245] .nil .nil)) (.node [v242,v617,v244,v247,v245,v258] (.node [v242,v279,v244,v245,v258,v382] .nil .nil) (.node [v242,v618,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrrrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrrrl = true := by decide +kernel
def tree_eaa8a880_5lrrrr : BinaryTree (List W) := (.node [v242,v297,v244,v245,v258] (.node [v242,v301,v244,v245,v258] (.node [v242,v308,v244,v245,v258,v531] (.node [v242,v308,v244,v247,v245,v258] (.node [v242,v308,v244,v276,v245,v258] .nil .nil) .nil) (.node [v242,v301,v244,v247,v245,v258] .nil .nil)) (.node [v242,v619,v244,v247,v245,v258] (.node [v242,v301,v244,v245,v258,v536] .nil .nil) (.node [v242,v297,v244,v247,v245,v258] .nil .nil))) (.node [v242,v250,v244,v245,v258,v317] (.node [v242,v250,v244,v247,v245,v258] (.node [v242,v297,v244,v245,v258,v294] .nil .nil) (.node [v242,v250,v244,v245,v258] .nil .nil)) (.node [v242,v620,v244,v247,v245,v258] (.node [v242,v621,v244,v247,v245,v258] .nil .nil) (.node [v242,v622,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrrrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrrrr = true := by decide +kernel
def tree_eaa8a880_5lrrr : BinaryTree (List W) := .node [v242,v308,v244,v352,v247,v258] tree_eaa8a880_5lrrrl tree_eaa8a880_5lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrrr = true := by
  change (_ && everyKey _ tree_eaa8a880_5lrrrl && everyKey _ tree_eaa8a880_5lrrrr) = true
  rw [ok_tree_eaa8a880_5lrrrl, ok_tree_eaa8a880_5lrrrr]
  decide +kernel
def tree_eaa8a880_5lrr : BinaryTree (List W) := .node [v242,v365,v308,v244,v245,v258] tree_eaa8a880_5lrrl tree_eaa8a880_5lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lrr = true := by
  change (_ && everyKey _ tree_eaa8a880_5lrrl && everyKey _ tree_eaa8a880_5lrrr) = true
  rw [ok_tree_eaa8a880_5lrrl, ok_tree_eaa8a880_5lrrr]
  decide +kernel
def tree_eaa8a880_5lr : BinaryTree (List W) := .node [v274,v244,v247,v245,v348] tree_eaa8a880_5lrl tree_eaa8a880_5lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5lr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5lr = true := by
  change (_ && everyKey _ tree_eaa8a880_5lrl && everyKey _ tree_eaa8a880_5lrr) = true
  rw [ok_tree_eaa8a880_5lrl, ok_tree_eaa8a880_5lrr]
  decide +kernel
def tree_eaa8a880_5l : BinaryTree (List W) := .node [v623,v242,v244,v247,v245,v258] tree_eaa8a880_5ll tree_eaa8a880_5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5l : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5l = true := by
  change (_ && everyKey _ tree_eaa8a880_5ll && everyKey _ tree_eaa8a880_5lr) = true
  rw [ok_tree_eaa8a880_5ll, ok_tree_eaa8a880_5lr]
  decide +kernel
def tree_eaa8a880_5rllll : BinaryTree (List W) := (.node [v242,v624,v244,v247,v245,v258] (.node [v242,v357,v244,v247,v258,v536] (.node [v242,v357,v244,v305,v247,v258] (.node [v242,v357,v278,v247,v245,v258] (.node [v242,v625,v244,v247,v245,v258] .nil .nil) .nil) (.node [v242,v357,v244,v247,v245,v258] .nil .nil)) (.node [v242,v357,v281,v247,v245,v258] (.node [v242,v357,v368,v247,v245,v258] .nil .nil) (.node [v242,v357,v247,v245,v258,v536] .nil .nil))) (.node [v242,v278,v244,v247,v260,v245] (.node [v242,v626,v244,v247,v245,v258] (.node [v242,v627,v244,v247,v245,v258] (.node [v242,v628,v244,v247,v245,v258] .nil .nil) .nil) (.node [v242,v278,v244,v281,v247,v245] .nil .nil)) (.node [v242,v278,v244,v247,v245,v389] (.node [v242,v278,v244,v247,v245,v258] .nil .nil) (.node [v242,v278,v305,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rllll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rllll = true := by decide +kernel
def tree_eaa8a880_5rlllr : BinaryTree (List W) := (.node [v242,v257,v247,v245,v258] (.node [v242,v629,v244,v247,v245,v258] (.node [v242,v630,v244,v247,v245,v258] (.node [v242,v631,v244,v247,v245,v258] (.node [v242,v278,v247,v245,v389] .nil .nil) .nil) (.node [v242,v632,v244,v247,v245,v258] .nil .nil)) (.node [v242,v633,v244,v247,v245,v258] (.node [v242,v634,v244,v247,v245,v258] .nil .nil) (.node [v242,v257,v244,v247,v245,v258] .nil .nil))) (.node [v242,v289,v247,v245,v258,v531] (.node [v242,v289,v244,v247,v245,v258] (.node [v242,v257,v247,v245,v258,v294] .nil .nil) (.node [v242,v289,v247,v245,v258] .nil .nil)) (.node [v242,v252,v247,v245,v258] (.node [v242,v252,v244,v247,v245,v258] .nil .nil) (.node [v242,v252,v247,v245,v258,v317] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rlllr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rlllr = true := by decide +kernel
def tree_eaa8a880_5rlll : BinaryTree (List W) := .node [v242,v278,v247,v245,v258,v389] tree_eaa8a880_5rllll tree_eaa8a880_5rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rlll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rlll = true := by
  change (_ && everyKey _ tree_eaa8a880_5rllll && everyKey _ tree_eaa8a880_5rlllr) = true
  rw [ok_tree_eaa8a880_5rllll, ok_tree_eaa8a880_5rlllr]
  decide +kernel
def tree_eaa8a880_5rllrl : BinaryTree (List W) := (.node [v242,v244,v635,v247,v245,v258] (.node [v242,v244,v636,v247,v245,v258] (.node [v242,v244,v637,v247,v245,v258] (.node [v242,v244,v638,v247,v245,v258] (.node [v242,v244,v639,v247,v245,v258] .nil .nil) .nil) (.node [v242,v244,v640,v247,v245,v258] .nil .nil)) (.node [v242,v244,v641,v247,v245,v258] (.node [v242,v244,v282,v247,v245,v258] .nil .nil) (.node [v242,v244,v642,v247,v245,v258] .nil .nil))) (.node [v242,v244,v335,v247,v245,v258] (.node [v242,v244,v321,v247,v245,v258] (.node [v242,v244,v643,v247,v245,v258] (.node [v242,v244,v644,v247,v245,v258] .nil .nil) .nil) (.node [v242,v244,v645,v247,v245,v258] .nil .nil)) (.node [v242,v244,v646,v247,v245,v258] (.node [v242,v244,v647,v247,v245,v258] .nil .nil) (.node [v242,v244,v648,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rllrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rllrl = true := by decide +kernel
def tree_eaa8a880_5rllrr : BinaryTree (List W) := (.node [v242,v244,v649,v247,v245,v258] (.node [v242,v244,v337,v247,v245,v258] (.node [v242,v244,v650,v247,v245,v258] (.node [v242,v244,v651,v247,v245,v258] (.node [v242,v244,v369,v247,v245,v258] .nil .nil) .nil) (.node [v242,v244,v338,v247,v245,v258] .nil .nil)) (.node [v242,v244,v652,v247,v245,v258] (.node [v242,v244,v334,v247,v245,v258] .nil .nil) (.node [v242,v244,v339,v247,v245,v258] .nil .nil))) (.node [v242,v244,v653,v247,v245,v258] (.node [v242,v244,v654,v247,v245,v258] (.node [v242,v244,v655,v247,v245,v258] .nil .nil) (.node [v242,v244,v368,v247,v245,v258] .nil .nil)) (.node [v242,v244,v656,v247,v245,v258] (.node [v242,v244,v657,v247,v245,v258] .nil .nil) (.node [v242,v244,v658,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rllrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rllrr = true := by decide +kernel
def tree_eaa8a880_5rllr : BinaryTree (List W) := .node [v242,v244,v659,v247,v245,v258] tree_eaa8a880_5rllrl tree_eaa8a880_5rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rllr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rllr = true := by
  change (_ && everyKey _ tree_eaa8a880_5rllrl && everyKey _ tree_eaa8a880_5rllrr) = true
  rw [ok_tree_eaa8a880_5rllrl, ok_tree_eaa8a880_5rllrr]
  decide +kernel
def tree_eaa8a880_5rll : BinaryTree (List W) := .node [v242,v244,v244,v247,v245,v258] tree_eaa8a880_5rlll tree_eaa8a880_5rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rll = true := by
  change (_ && everyKey _ tree_eaa8a880_5rlll && everyKey _ tree_eaa8a880_5rllr) = true
  rw [ok_tree_eaa8a880_5rlll, ok_tree_eaa8a880_5rllr]
  decide +kernel
def tree_eaa8a880_5rlrll : BinaryTree (List W) := (.node [v242,v244,v311,v247,v245,v258] (.node [v242,v244,v281,v247,v245,v258] (.node [v242,v244,v660,v247,v245,v258] (.node [v242,v244,v661,v247,v245,v258] (.node [v242,v244,v662,v247,v245,v258] .nil .nil) .nil) (.node [v242,v244,v663,v247,v245,v258] .nil .nil)) (.node [v242,v244,v305,v247,v245,v258] (.node [v242,v244,v664,v247,v245,v258] .nil .nil) (.node [v242,v244,v299,v247,v245,v258] .nil .nil))) (.node [v242,v244,v665,v247,v245,v258] (.node [v242,v244,v253,v247,v245,v258] (.node [v242,v244,v666,v247,v245,v258] (.node [v242,v244,v667,v247,v245,v258] .nil .nil) .nil) (.node [v242,v244,v668,v247,v245,v258] .nil .nil)) (.node [v242,v244,v669,v247,v245,v258] (.node [v242,v244,v670,v247,v245,v258] .nil .nil) (.node [v242,v244,v352,v276,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rlrll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rlrll = true := by decide +kernel
def tree_eaa8a880_5rlrlr : BinaryTree (List W) := (.node [v242,v244,v276,v247,v245,v382] (.node [v242,v244,v671,v247,v245,v258] (.node [v242,v244,v672,v247,v245,v258] (.node [v242,v244,v352,v245,v258,v531] (.node [v242,v244,v352,v247,v258,v531] .nil .nil) .nil) (.node [v242,v244,v673,v247,v245,v258] .nil .nil)) (.node [v242,v244,v276,v247,v260,v245] (.node [v242,v244,v674,v247,v245,v258] .nil .nil) (.node [v242,v244,v276,v247,v245,v258] .nil .nil))) (.node [v242,v244,v675,v247,v245,v258] (.node [v242,v244,v276,v245,v382] (.node [v242,v244,v276,v245,v258,v382] .nil .nil) (.node [v242,v244,v676,v247,v245,v258] .nil .nil)) (.node [v242,v244,v677,v247,v245,v258] (.node [v242,v244,v678,v247,v245,v258] .nil .nil) (.node [v242,v244,v679,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rlrlr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rlrlr = true := by decide +kernel
def tree_eaa8a880_5rlrl : BinaryTree (List W) := .node [v242,v244,v352,v247,v245,v258] tree_eaa8a880_5rlrll tree_eaa8a880_5rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rlrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rlrl = true := by
  change (_ && everyKey _ tree_eaa8a880_5rlrll && everyKey _ tree_eaa8a880_5rlrlr) = true
  rw [ok_tree_eaa8a880_5rlrll, ok_tree_eaa8a880_5rlrlr]
  decide +kernel
def tree_eaa8a880_5rlrrl : BinaryTree (List W) := (.node [v242,v244,v249,v245,v258] (.node [v242,v244,v300,v247,v245,v258] (.node [v242,v244,v255,v245,v258] (.node [v242,v244,v255,v247,v245,v258] (.node [v242,v244,v680,v247,v245,v258] .nil .nil) .nil) (.node [v242,v244,v255,v245,v258,v294] .nil .nil)) (.node [v242,v244,v300,v245,v258,v536] (.node [v242,v244,v300,v245,v258] .nil .nil) (.node [v242,v244,v249,v247,v245,v258] .nil .nil))) (.node [v242,v244,v247,v681,v245,v258] (.node [v242,v244,v247,v682,v245,v258] (.node [v242,v244,v247,v247,v245,v258] (.node [v242,v244,v249,v245,v258,v317] .nil .nil) .nil) (.node [v242,v244,v247,v683,v245,v258] .nil .nil)) (.node [v242,v244,v247,v684,v245,v258] (.node [v242,v244,v247,v685,v245,v258] .nil .nil) (.node [v242,v244,v247,v272,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rlrrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rlrrl = true := by decide +kernel
def tree_eaa8a880_5rlrrr : BinaryTree (List W) := (.node [v242,v244,v247,v314,v245,v258] (.node [v242,v244,v247,v686,v245,v258] (.node [v242,v244,v247,v472,v245,v258] (.node [v242,v244,v247,v687,v245,v258] (.node [v242,v244,v247,v688,v245,v258] .nil .nil) .nil) (.node [v242,v244,v247,v689,v245,v258] .nil .nil)) (.node [v242,v244,v247,v690,v245,v258] (.node [v242,v244,v247,v691,v245,v258] .nil .nil) (.node [v242,v244,v247,v692,v245,v258] .nil .nil))) (.node [v242,v244,v247,v693,v245,v258] (.node [v242,v244,v247,v326,v245,v258] (.node [v242,v244,v247,v694,v245,v258] .nil .nil) (.node [v242,v244,v247,v695,v245,v258] .nil .nil)) (.node [v242,v244,v247,v329,v245,v258] (.node [v242,v244,v247,v696,v245,v258] .nil .nil) (.node [v242,v244,v247,v328,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rlrrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rlrrr = true := by decide +kernel
def tree_eaa8a880_5rlrr : BinaryTree (List W) := .node [v242,v244,v247,v697,v245,v258] tree_eaa8a880_5rlrrl tree_eaa8a880_5rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rlrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rlrr = true := by
  change (_ && everyKey _ tree_eaa8a880_5rlrrl && everyKey _ tree_eaa8a880_5rlrrr) = true
  rw [ok_tree_eaa8a880_5rlrrl, ok_tree_eaa8a880_5rlrrr]
  decide +kernel
def tree_eaa8a880_5rlr : BinaryTree (List W) := .node [v242,v244,v698,v247,v245,v258] tree_eaa8a880_5rlrl tree_eaa8a880_5rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rlr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rlr = true := by
  change (_ && everyKey _ tree_eaa8a880_5rlrl && everyKey _ tree_eaa8a880_5rlrr) = true
  rw [ok_tree_eaa8a880_5rlrl, ok_tree_eaa8a880_5rlrr]
  decide +kernel
def tree_eaa8a880_5rl : BinaryTree (List W) := .node [v242,v244,v320,v247,v245,v258] tree_eaa8a880_5rll tree_eaa8a880_5rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rl = true := by
  change (_ && everyKey _ tree_eaa8a880_5rll && everyKey _ tree_eaa8a880_5rlr) = true
  rw [ok_tree_eaa8a880_5rll, ok_tree_eaa8a880_5rlr]
  decide +kernel
def tree_eaa8a880_5rrlll : BinaryTree (List W) := (.node [v242,v244,v247,v248,v245,v258] (.node [v242,v244,v247,v699,v245,v258] (.node [v242,v244,v247,v491,v245,v258] (.node [v242,v244,v247,v523,v245,v258] (.node [v242,v244,v247,v700,v245,v258] .nil .nil) .nil) (.node [v242,v244,v247,v701,v245,v258] .nil .nil)) (.node [v242,v244,v247,v296,v245,v258] (.node [v242,v244,v247,v307,v245,v258] .nil .nil) (.node [v242,v244,v247,v702,v245,v258] .nil .nil))) (.node [v242,v244,v247,v703,v245,v258] (.node [v242,v244,v247,v704,v245,v258] (.node [v242,v244,v247,v705,v245,v258] (.node [v242,v244,v247,v706,v245,v258] .nil .nil) .nil) (.node [v242,v244,v247,v707,v245,v258] .nil .nil)) (.node [v242,v244,v247,v708,v245,v258] (.node [v242,v244,v247,v709,v245,v258] .nil .nil) (.node [v242,v244,v247,v710,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrlll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrlll = true := by decide +kernel
def tree_eaa8a880_5rrllr : BinaryTree (List W) := (.node [v242,v244,v247,v711,v245,v258] (.node [v242,v244,v247,v712,v245,v258] (.node [v242,v244,v247,v713,v245,v258] (.node [v242,v244,v247,v714,v245,v258] (.node [v242,v244,v247,v715,v245,v258] .nil .nil) .nil) (.node [v242,v244,v247,v493,v245,v258] .nil .nil)) (.node [v242,v244,v247,v716,v245,v258] (.node [v242,v244,v247,v331,v245,v258] .nil .nil) (.node [v242,v244,v247,v717,v245,v258] .nil .nil))) (.node [v242,v244,v247,v718,v245,v258] (.node [v242,v244,v247,v489,v245,v258] (.node [v242,v244,v247,v719,v245,v258] .nil .nil) (.node [v242,v244,v247,v720,v245,v258] .nil .nil)) (.node [v242,v244,v247,v332,v245,v258] (.node [v242,v244,v247,v330,v245,v258] .nil .nil) (.node [v242,v244,v247,v345,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrllr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrllr = true := by decide +kernel
def tree_eaa8a880_5rrll : BinaryTree (List W) := .node [v242,v244,v247,v721,v245,v258] tree_eaa8a880_5rrlll tree_eaa8a880_5rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrll = true := by
  change (_ && everyKey _ tree_eaa8a880_5rrlll && everyKey _ tree_eaa8a880_5rrllr) = true
  rw [ok_tree_eaa8a880_5rrlll, ok_tree_eaa8a880_5rrllr]
  decide +kernel
def tree_eaa8a880_5rrlrl : BinaryTree (List W) := (.node [v242,v244,v247,v344,v245,v258] (.node [v242,v244,v247,v722,v245,v258] (.node [v242,v244,v247,v260,v317] (.node [v242,v244,v247,v260,v258,v317] (.node [v242,v244,v247,v260,v245,v317] .nil .nil) .nil) (.node [v242,v244,v247,v723,v245,v258] .nil .nil)) (.node [v242,v244,v247,v724,v245,v258] (.node [v242,v244,v247,v725,v245,v258] .nil .nil) (.node [v242,v244,v247,v726,v245,v258] .nil .nil))) (.node [v242,v244,v247,v245,v285,v258] (.node [v242,v244,v247,v386,v245,v258] (.node [v242,v244,v247,v410,v245,v258] (.node [v242,v244,v247,v727,v245,v258] .nil .nil) .nil) (.node [v242,v244,v247,v245,v245,v258] .nil .nil)) (.node [v242,v244,v247,v245,v286,v258] (.node [v242,v244,v247,v245,v287,v258] .nil .nil) (.node [v242,v244,v247,v245,v375,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrlrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrlrl = true := by decide +kernel
def tree_eaa8a880_5rrlrr : BinaryTree (List W) := (.node [v242,v244,v247,v245,v256,v258] (.node [v242,v244,v247,v245,v728,v258] (.node [v242,v244,v247,v245,v476,v258] (.node [v242,v244,v247,v245,v376,v258] (.node [v242,v244,v247,v245,v377,v258] .nil .nil) .nil) (.node [v242,v244,v247,v245,v475,v258] .nil .nil)) (.node [v242,v244,v247,v245,v729,v258] (.node [v242,v244,v247,v245,v730,v258] .nil .nil) (.node [v242,v244,v247,v245,v256] .nil .nil))) (.node [v242,v244,v247,v245,v354,v536] (.node [v242,v244,v247,v245,v354] (.node [v242,v244,v247,v245,v256,v294] .nil .nil) (.node [v242,v244,v247,v245,v354,v258] .nil .nil)) (.node [v242,v244,v247,v245,v353,v258] (.node [v242,v244,v247,v245,v353] .nil .nil) (.node [v242,v244,v247,v245,v353,v531] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrlrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrlrr = true := by decide +kernel
def tree_eaa8a880_5rrlr : BinaryTree (List W) := .node [v242,v244,v247,v245,v477,v258] tree_eaa8a880_5rrlrl tree_eaa8a880_5rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrlr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrlr = true := by
  change (_ && everyKey _ tree_eaa8a880_5rrlrl && everyKey _ tree_eaa8a880_5rrlrr) = true
  rw [ok_tree_eaa8a880_5rrlrl, ok_tree_eaa8a880_5rrlrr]
  decide +kernel
def tree_eaa8a880_5rrl : BinaryTree (List W) := .node [v242,v244,v247,v260,v245,v258] tree_eaa8a880_5rrll tree_eaa8a880_5rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrl = true := by
  change (_ && everyKey _ tree_eaa8a880_5rrll && everyKey _ tree_eaa8a880_5rrlr) = true
  rw [ok_tree_eaa8a880_5rrll, ok_tree_eaa8a880_5rrlr]
  decide +kernel
def tree_eaa8a880_5rrrll : BinaryTree (List W) := (.node [v242,v244,v247,v245,v258,v731] (.node [v242,v244,v247,v245,v258,v732] (.node [v242,v244,v247,v245,v258,v733] (.node [v242,v244,v247,v245,v258,v734] (.node [v242,v244,v247,v245,v258,v258] .nil .nil) .nil) (.node [v242,v244,v247,v245,v258,v735] .nil .nil)) (.node [v242,v244,v247,v245,v258,v474] (.node [v242,v244,v247,v245,v258,v736] .nil .nil) (.node [v242,v244,v247,v245,v258,v737] .nil .nil))) (.node [v242,v244,v247,v245,v258,v349] (.node [v242,v244,v247,v245,v258,v738] (.node [v242,v244,v247,v245,v258,v372] (.node [v242,v244,v247,v245,v258,v739] .nil .nil) .nil) (.node [v242,v244,v247,v245,v258,v394] .nil .nil)) (.node [v242,v244,v247,v245,v258,v740] (.node [v242,v244,v247,v245,v258,v348] .nil .nil) (.node [v242,v244,v247,v245,v258,v741] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrrll : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrrll = true := by decide +kernel
def tree_eaa8a880_5rrrlr : BinaryTree (List W) := (.node [v242,v244,v247,v245,v258,v341] (.node [v242,v244,v247,v245,v258,v385] (.node [v242,v244,v247,v245,v258,v408] (.node [v242,v244,v247,v245,v258,v409] (.node [v242,v244,v247,v245,v258,v742] .nil .nil) .nil) (.node [v242,v244,v247,v245,v258,v382] .nil .nil)) (.node [v242,v244,v247,v245,v258,v389] (.node [v242,v244,v247,v245,v258,v381] .nil .nil) (.node [v242,v244,v247,v245,v258,v342] .nil .nil))) (.node [v242,v244,v247,v245,v258,v743] (.node [v242,v244,v247,v245,v258,v294] (.node [v242,v244,v247,v245,v258,v340] .nil .nil) (.node [v242,v244,v247,v245,v258,v744] .nil .nil)) (.node [v242,v244,v247,v245,v258,v420] (.node [v242,v244,v247,v245,v258,v745] .nil .nil) (.node [v242,v244,v247,v245,v258,v536] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrrlr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrrlr = true := by decide +kernel
def tree_eaa8a880_5rrrl : BinaryTree (List W) := .node [v242,v244,v247,v245,v258,v746] tree_eaa8a880_5rrrll tree_eaa8a880_5rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrrl = true := by
  change (_ && everyKey _ tree_eaa8a880_5rrrll && everyKey _ tree_eaa8a880_5rrrlr) = true
  rw [ok_tree_eaa8a880_5rrrll, ok_tree_eaa8a880_5rrrlr]
  decide +kernel
def tree_eaa8a880_5rrrrl : BinaryTree (List W) := (.node [v242,v244,v247,v245,v258,v747] (.node [v242,v244,v247,v245,v258,v317] (.node [v242,v244,v247,v245,v258,v748] (.node [v242,v244,v247,v245,v258,v531] (.node [v242,v244,v247,v245,v258,v431] .nil .nil) .nil) (.node [v242,v244,v247,v245,v258,v749] .nil .nil)) (.node [v242,v244,v247,v245,v258,v750] (.node [v242,v244,v247,v245,v258,v751] .nil .nil) (.node [v242,v244,v247,v245,v258,v752] .nil .nil))) (.node [v242,v281,v247,v245,v258,v389] (.node [v242,v368,v247,v345,v245,v258] (.node [v242,v368,v305,v247,v245,v258] (.node [v242,v244,v247,v245,v258,v753] .nil .nil) .nil) (.node [v242,v281,v305,v247,v245,v258] .nil .nil)) (.node [v242,v299,v247,v245,v258] (.node [v242,v305,v247,v245,v258,v536] .nil .nil) (.node [v242,v299,v247,v245,v258,v294] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrrrl : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrrrl = true := by decide +kernel
def tree_eaa8a880_5rrrrr : BinaryTree (List W) := (.node [v244,v247,v523,v245,v258,v348] (.node [v318,v244,v247,v491,v245,v258] (.node [v242,v253,v247,v245,v258,v317] (.node [v242,v253,v247,v245,v258] (.node [v242,v311,v247,v245,v258,v531] .nil .nil) .nil) (.node [v318,v244,v334,v247,v245,v258] .nil .nil)) (.node [v244,v320,v247,v491,v245,v258] (.node [v244,v320,v247,v325,v245,v258] .nil .nil) (.node [v244,v247,v523,v491,v245,v258] .nil .nil))) (.node [v244,v247,v296,v245,v258] (.node [v244,v247,v307,v245,v258] (.node [v244,v247,v491,v245,v258,v294] .nil .nil) (.node [v244,v247,v307,v245,v258,v536] .nil .nil)) (.node [v244,v247,v248,v245,v258] (.node [v244,v247,v296,v245,v258,v531] .nil .nil) (.node [v244,v247,v248,v245,v258,v317] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrrrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrrrr = true := by decide +kernel
def tree_eaa8a880_5rrrr : BinaryTree (List W) := .node [v242,v311,v247,v245,v258] tree_eaa8a880_5rrrrl tree_eaa8a880_5rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrrr = true := by
  change (_ && everyKey _ tree_eaa8a880_5rrrrl && everyKey _ tree_eaa8a880_5rrrrr) = true
  rw [ok_tree_eaa8a880_5rrrrl, ok_tree_eaa8a880_5rrrrr]
  decide +kernel
def tree_eaa8a880_5rrr : BinaryTree (List W) := .node [v242,v244,v247,v245,v258,v754] tree_eaa8a880_5rrrl tree_eaa8a880_5rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rrr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rrr = true := by
  change (_ && everyKey _ tree_eaa8a880_5rrrl && everyKey _ tree_eaa8a880_5rrrr) = true
  rw [ok_tree_eaa8a880_5rrrl, ok_tree_eaa8a880_5rrrr]
  decide +kernel
def tree_eaa8a880_5rr : BinaryTree (List W) := .node [v242,v244,v247,v245,v258] tree_eaa8a880_5rrl tree_eaa8a880_5rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5rr : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5rr = true := by
  change (_ && everyKey _ tree_eaa8a880_5rrl && everyKey _ tree_eaa8a880_5rrr) = true
  rw [ok_tree_eaa8a880_5rrl, ok_tree_eaa8a880_5rrr]
  decide +kernel
def tree_eaa8a880_5r : BinaryTree (List W) := .node [v242,v244,v247,v325,v245,v258] tree_eaa8a880_5rl tree_eaa8a880_5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5r : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5r = true := by
  change (_ && everyKey _ tree_eaa8a880_5rl && everyKey _ tree_eaa8a880_5rr) = true
  rw [ok_tree_eaa8a880_5rl, ok_tree_eaa8a880_5rr]
  decide +kernel
def tree_eaa8a880_5 : BinaryTree (List W) := .node [v242,v755,v244,v247,v245,v258] tree_eaa8a880_5l tree_eaa8a880_5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_5 : everyKey (rowOK 4 tree_eaa8a880_4) tree_eaa8a880_5 = true := by
  change (_ && everyKey _ tree_eaa8a880_5l && everyKey _ tree_eaa8a880_5r) = true
  rw [ok_tree_eaa8a880_5l, ok_tree_eaa8a880_5r]
  decide +kernel
theorem closed_eaa8a880_5 : Closed 5 tree_eaa8a880_5 := closed_next 4 (by decide) tree_eaa8a880_5 tree_eaa8a880_4 closed_eaa8a880_4 ok_tree_eaa8a880_5
def tree_eaa8a880_6l : BinaryTree (List W) := (.node [v324,v242,v244,v247,v245,v258] (.node [v304,v242,v244,v247,v245,v258] (.node [v280,v242,v244,v247,v245,v258] (.node [v271,v242,v244,v247,v245,v258] (.node [v518,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v534,v242,v244,v247,v245,v258] (.node [v270,v242,v244,v247,v245,v258] .nil .nil) .nil)) (.node [v313,v242,v244,v247,v245,v258] (.node [v283,v242,v244,v247,v245,v258] (.node [v302,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v319,v242,v244,v247,v245,v258] .nil .nil))) (.node [v242,v318,v244,v247,v245,v258] (.node [v254,v242,v244,v247,v245,v258] (.node [v333,v242,v244,v247,v245,v258] (.node [v316,v242,v244,v247,v245,v258] .nil .nil) .nil) (.node [v274,v242,v244,v247,v245,v258] .nil .nil)) (.node [v242,v308,v244,v247,v245,v258] (.node [v242,v279,v244,v247,v245,v258] (.node [v242,v365,v244,v247,v245,v258] .nil .nil) .nil) (.node [v242,v357,v244,v247,v245,v258] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_6l : everyKey (rowOK 5 tree_eaa8a880_5) tree_eaa8a880_6l = true := by decide +kernel
def tree_eaa8a880_6r : BinaryTree (List W) := (.node [v242,v244,v247,v491,v245,v258] (.node [v242,v244,v305,v247,v245,v258] (.node [v242,v244,v320,v247,v245,v258] (.node [v242,v244,v368,v247,v245,v258] (.node [v242,v244,v334,v247,v245,v258] .nil .nil) .nil) (.node [v242,v244,v281,v247,v245,v258] .nil .nil)) (.node [v242,v244,v247,v325,v245,v258] (.node [v242,v244,v276,v247,v245,v258] (.node [v242,v244,v352,v247,v245,v258] .nil .nil) .nil) (.node [v242,v244,v247,v523,v245,v258] .nil .nil))) (.node [v242,v244,v247,v245,v258,v389] (.node [v242,v244,v247,v245,v258,v348] (.node [v242,v244,v247,v260,v245,v258] (.node [v242,v244,v247,v345,v245,v258] .nil .nil) .nil) (.node [v242,v244,v247,v245,v258,v382] .nil .nil)) (.node [v242,v244,v247,v245,v258,v531] (.node [v242,v244,v247,v245,v258,v536] (.node [v242,v244,v247,v245,v258,v294] .nil .nil) .nil) (.node [v242,v244,v247,v245,v258,v317] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_6r : everyKey (rowOK 5 tree_eaa8a880_5) tree_eaa8a880_6r = true := by decide +kernel
def tree_eaa8a880_6 : BinaryTree (List W) := .node [v242,v278,v244,v247,v245,v258] tree_eaa8a880_6l tree_eaa8a880_6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_6 : everyKey (rowOK 5 tree_eaa8a880_5) tree_eaa8a880_6 = true := by
  change (_ && everyKey _ tree_eaa8a880_6l && everyKey _ tree_eaa8a880_6r) = true
  rw [ok_tree_eaa8a880_6l, ok_tree_eaa8a880_6r]
  decide +kernel
theorem closed_eaa8a880_6 : Closed 6 tree_eaa8a880_6 := closed_next 5 (by decide) tree_eaa8a880_6 tree_eaa8a880_5 closed_eaa8a880_5 ok_tree_eaa8a880_6
def tree_eaa8a880_7 : BinaryTree (List W) := (.node [v242,v244,v247,v245,v258] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8a880_7 : everyKey (rowOK 6 tree_eaa8a880_6) tree_eaa8a880_7 = true := by decide +kernel
theorem closed_eaa8a880_7 : Closed 7 tree_eaa8a880_7 := closed_next 6 (by decide) tree_eaa8a880_7 tree_eaa8a880_6 closed_eaa8a880_6 ok_tree_eaa8a880_7
theorem lower_eaa8a880 : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 7 ins_eaa8a880.toFinset := @no_build 7 tree_eaa8a880_7 ins_eaa8a880 nd_eaa8a880 (by decide) closed_eaa8a880_7 (by decide +kernel)
def gates_eaa8a880 : List Gate := [⟨.and, [1, 2]⟩, ⟨.or, [3, 4]⟩, ⟨.and, [0, 6]⟩, ⟨.or, [5, 7]⟩, ⟨.and, [3, 4]⟩, ⟨.or, [1, 2]⟩, ⟨.and, [0, 10]⟩, ⟨.or, [9, 11]⟩, ⟨.and, [8, 12]⟩]
theorem upper_eaa8a880 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeaa8a880 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  exact ⟨gates_eaa8a880, 13, by simp [gates_eaa8a880], rfl, by decide +kernel⟩

def ins_eaa8c880 : List W := [0xf9ffe7b546ff820, 0xff5b99fae56065e, 0x7fa59a5fba86685, 0x6d0ffc81b031f2, 0xf2ae6f760818bdd]
theorem nd_eaa8c880 : ins_eaa8c880.Nodup := by decide +kernel
theorem rows_eaa8c880 : ∀ j : Fin 60, Nat.testBit 0xeaa8c880 (∑ i : Fin 5, if (ins_eaa8c880.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
def tree_eaa8c880_0 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_0 : everyKey (fun q => !doneTest q) tree_eaa8c880_0 = true := by decide +kernel
theorem closed_eaa8c880_0 : Closed 0 tree_eaa8c880_0 := closed_nil tree_eaa8c880_0 ok_tree_eaa8c880_0
def tree_eaa8c880_1 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_1 : everyKey (rowOK 0 tree_eaa8c880_0) tree_eaa8c880_1 = true := by decide +kernel
theorem closed_eaa8c880_1 : Closed 1 tree_eaa8c880_1 := closed_next 0 (by decide) tree_eaa8c880_1 tree_eaa8c880_0 closed_eaa8c880_0 ok_tree_eaa8c880_1
def tree_eaa8c880_2 : BinaryTree (List W) := (.node [v756,v757,v758] (.node [v759,v760,v761] (.node [v762,v763,v764] .nil .nil) (.node [v765,v766,v767] .nil .nil)) (.node [v768,v757,v769] (.node [v770,v757,v771] .nil .nil) (.node [v772,v757,v761] .nil .nil)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_2 : everyKey (rowOK 1 tree_eaa8c880_1) tree_eaa8c880_2 = true := by decide +kernel
theorem closed_eaa8c880_2 : Closed 2 tree_eaa8c880_2 := closed_next 1 (by decide) tree_eaa8c880_2 tree_eaa8c880_1 closed_eaa8c880_1 ok_tree_eaa8c880_2
def tree_eaa8c880_3ll : BinaryTree (List W) := (.node [v773,v762,v774,v765] (.node [v775,v765,v757,v767] (.node [v776,v777,v760,v769] (.node [v776,v777,v757,v758] (.node [v778,v765,v760,v779] .nil .nil) (.node [v776,v777,v780,v758] .nil .nil)) (.node [v776,v765,v780,v769] (.node [v776,v765,v757,v769] .nil .nil) .nil)) (.node [v781,v765,v760,v782] (.node [v783,v784,v760,v782] (.node [v783,v765,v757,v785] .nil .nil) .nil) (.node [v773,v786,v765,v760] (.node [v787,v759,v757,v758] .nil .nil) .nil))) (.node [v773,v762,v765,v788] (.node [v773,v762,v765,v789] (.node [v773,v762,v790,v760] (.node [v773,v762,v791,v765] .nil .nil) (.node [v773,v762,v765,v757] .nil .nil)) (.node [v773,v762,v765,v760] (.node [v773,v762,v765,v792] .nil .nil) .nil)) (.node [v793,v765,v757,v785] (.node [v773,v765,v760,v794] (.node [v773,v762,v795,v760] .nil .nil) .nil) (.node [v786,v765,v757,v785] (.node [v786,v790,v760,v785] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_3ll : everyKey (rowOK 2 tree_eaa8c880_2) tree_eaa8c880_3ll = true := by decide +kernel
def tree_eaa8c880_3lr : BinaryTree (List W) := (.node [v762,v790,v757,v785] (.node [v762,v796,v757,v771] (.node [v762,v774,v784,v782] (.node [v797,v765,v798,v799] (.node [v797,v800,v798,v782] .nil .nil) (.node [v801,v796,v757,v758] .nil .nil)) (.node [v762,v802,v765,v799] (.node [v762,v802,v800,v782] .nil .nil) .nil)) (.node [v762,v803,v757,v785] (.node [v762,v804,v760,v782] (.node [v762,v805,v757,v763] .nil .nil) .nil) (.node [v762,v800,v798,v799] (.node [v762,v806,v757,v785] .nil .nil) .nil))) (.node [v762,v765,v785,v764] (.node [v762,v765,v807,v799] (.node [v762,v765,v757,v761] (.node [v762,v790,v792,v785] .nil .nil) (.node [v762,v765,v808,v799] .nil .nil)) (.node [v762,v765,v766,v785] (.node [v762,v765,v809,v785] .nil .nil) .nil)) (.node [v762,v810,v784,v782] (.node [v762,v765,v799,v811] (.node [v762,v765,v812,v758] .nil .nil) .nil) (.node [v762,v784,v760,v782] (.node [v762,v784,v757,v782] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_3lr : everyKey (rowOK 2 tree_eaa8c880_2) tree_eaa8c880_3lr = true := by decide +kernel
def tree_eaa8c880_3l : BinaryTree (List W) := .node [v786,v765,v792,v785] tree_eaa8c880_3ll tree_eaa8c880_3lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_3l : everyKey (rowOK 2 tree_eaa8c880_2) tree_eaa8c880_3l = true := by
  change (_ && everyKey _ tree_eaa8c880_3ll && everyKey _ tree_eaa8c880_3lr) = true
  rw [ok_tree_eaa8c880_3ll, ok_tree_eaa8c880_3lr]
  decide +kernel
def tree_eaa8c880_3rl : BinaryTree (List W) := (.node [v813,v757,v782,v758] (.node [v774,v813,v782,v758] (.node [v762,v782,v764,v814] (.node [v762,v815,v816,v758] (.node [v762,v815,v757,v758] .nil .nil) (.node [v762,v782,v817,v818] .nil .nil)) (.node [v819,v784,v760,v782] (.node [v762,v782,v820,v821] .nil .nil) .nil)) (.node [v822,v765,v779,v758] (.node [v774,v765,v779,v758] (.node [v774,v765,v823,v782] .nil .nil) .nil) (.node [v824,v765,v782,v758] (.node [v802,v765,v825,v782] .nil .nil) .nil))) (.node [v826,v760,v779,v758] (.node [v759,v760,v758,v827] (.node [v828,v760,v782,v758] (.node [v813,v760,v782,v758] .nil .nil) (.node [v759,v765,v760,v769] .nil .nil)) (.node [v829,v760,v779,v758] (.node [v830,v760,v782,v758] .nil .nil) .nil)) (.node [v765,v831,v823,v782] (.node [v777,v760,v779,v758] (.node [v803,v760,v823,v782] .nil .nil) .nil) (.node [v765,v757,v779,v758] (.node [v765,v757,v823,v782] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_3rl : everyKey (rowOK 2 tree_eaa8c880_2) tree_eaa8c880_3rl = true := by decide +kernel
def tree_eaa8c880_3rr : BinaryTree (List W) := (.node [v756,v760,v782,v758] (.node [v765,v832,v779,v758] (.node [v765,v760,v779,v758] (.node [v765,v760,v823,v782] (.node [v765,v780,v779,v758] .nil .nil) (.node [v765,v760,v779,v769] .nil .nil)) (.node [v765,v833,v782,v758] (.node [v765,v834,v782,v758] .nil .nil) .nil)) (.node [v765,v835,v782,v836] (.node [v765,v766,v782,v837] (.node [v765,v838,v782,v818] .nil .nil) .nil) (.node [v839,v760,v823,v782] (.node [v765,v840,v823,v782] .nil .nil) .nil))) (.node [v772,v757,v758,v827] (.node [v768,v760,v782,v769] (.node [v770,v760,v782,v771] (.node [v770,v757,v758,v841] .nil .nil) (.node [v768,v757,v758,v842] .nil .nil)) (.node [v768,v760,v758,v843] (.node [v768,v760,v779,v758] .nil .nil) .nil)) (.node [v844,v760,v779,v758] (.node [v772,v760,v758,v845] (.node [v772,v760,v782,v761] .nil .nil) .nil) (.node [v846,v760,v782,v758] (.node [v847,v760,v779,v758] .nil .nil) .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_3rr : everyKey (rowOK 2 tree_eaa8c880_2) tree_eaa8c880_3rr = true := by decide +kernel
def tree_eaa8c880_3r : BinaryTree (List W) := .node [v765,v848,v779,v758] tree_eaa8c880_3rl tree_eaa8c880_3rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_3r : everyKey (rowOK 2 tree_eaa8c880_2) tree_eaa8c880_3r = true := by
  change (_ && everyKey _ tree_eaa8c880_3rl && everyKey _ tree_eaa8c880_3rr) = true
  rw [ok_tree_eaa8c880_3rl, ok_tree_eaa8c880_3rr]
  decide +kernel
def tree_eaa8c880_3 : BinaryTree (List W) := .node [v762,v784,v782,v849] tree_eaa8c880_3l tree_eaa8c880_3r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_3 : everyKey (rowOK 2 tree_eaa8c880_2) tree_eaa8c880_3 = true := by
  change (_ && everyKey _ tree_eaa8c880_3l && everyKey _ tree_eaa8c880_3r) = true
  rw [ok_tree_eaa8c880_3l, ok_tree_eaa8c880_3r]
  decide +kernel
theorem closed_eaa8c880_3 : Closed 3 tree_eaa8c880_3 := closed_next 2 (by decide) tree_eaa8c880_3 tree_eaa8c880_2 closed_eaa8c880_2 ok_tree_eaa8c880_3
def tree_eaa8c880_4lllll : BinaryTree (List W) := (.node [v850,v851,v760,v782,v758] (.node [v850,v774,v852,v782,v758] (.node [v853,v775,v765,v760,v782] (.node [v854,v762,v805,v760,v782] (.node [v855,v762,v765,v808,v782] .nil .nil) .nil) (.node [v856,v762,v765,v782,v758] (.node [v857,v762,v858,v782,v758] .nil .nil) .nil)) (.node [v850,v813,v760,v782,v758] (.node [v850,v852,v760,v782,v758] (.node [v850,v852,v757,v782,v758] .nil .nil) .nil) (.node [v850,v859,v760,v782,v758] .nil .nil))) (.node [v860,v861,v765,v782,v758] (.node [v850,v770,v760,v782,v758] (.node [v850,v765,v760,v782,v769] (.node [v850,v777,v760,v782,v758] .nil .nil) .nil) (.node [v850,v862,v760,v782,v758] .nil .nil)) (.node [v863,v774,v765,v864,v782] (.node [v863,v865,v765,v760,v782] (.node [v863,v762,v765,v757,v785] .nil .nil) .nil) (.node [v863,v803,v760,v864,v782] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4lllll : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4lllll = true := by decide +kernel
def tree_eaa8c880_4llllr : BinaryTree (List W) := (.node [v866,v762,v784,v760,v782] (.node [v866,v762,v774,v867,v782] (.node [v863,v839,v760,v864,v782] (.node [v863,v765,v760,v823,v782] (.node [v863,v765,v760,v864,v782] .nil .nil) .nil) (.node [v866,v783,v867,v760,v782] (.node [v868,v765,v835,v782,v758] .nil .nil) .nil)) (.node [v866,v762,v867,v757,v782] (.node [v866,v762,v869,v760,v782] (.node [v866,v762,v765,v757,v785] .nil .nil) .nil) (.node [v866,v762,v867,v760,v782] .nil .nil))) (.node [v870,v871,v762,v765,v789] (.node [v870,v871,v762,v774,v765] (.node [v872,v762,v873,v765,v782] (.node [v866,v819,v867,v760,v782] .nil .nil) .nil) (.node [v870,v871,v762,v765,v757] .nil .nil)) (.node [v870,v783,v765,v760,v782] (.node [v870,v871,v762,v765,v788] (.node [v870,v871,v762,v765,v760] .nil .nil) .nil) (.node [v870,v773,v762,v765,v760] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4llllr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4llllr = true := by decide +kernel
def tree_eaa8c880_4llll : BinaryTree (List W) := .node [v863,v765,v757,v864,v782] tree_eaa8c880_4lllll tree_eaa8c880_4llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4llll : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4llll = true := by
  change (_ && everyKey _ tree_eaa8c880_4lllll && everyKey _ tree_eaa8c880_4llllr) = true
  rw [ok_tree_eaa8c880_4lllll, ok_tree_eaa8c880_4llllr]
  decide +kernel
def tree_eaa8c880_4lllrl : BinaryTree (List W) := (.node [v874,v762,v765,v757,v782] (.node [v875,v765,v760,v864,v782] (.node [v870,v762,v765,v760,v876] (.node [v870,v762,v790,v760,v782] (.node [v870,v762,v803,v760,v782] .nil .nil) .nil) (.node [v875,v762,v867,v760,v782] (.node [v870,v762,v765,v760,v877] .nil .nil) .nil)) (.node [v874,v762,v774,v765,v782] (.node [v874,v801,v765,v760,v782] (.node [v878,v762,v765,v760,v782] .nil .nil) .nil) (.node [v874,v762,v879,v765,v782] .nil .nil))) (.node [v778,v762,v774,v765,v782] (.node [v874,v765,v760,v880,v782] (.node [v874,v762,v765,v760,v782] (.node [v874,v762,v765,v881,v782] .nil .nil) .nil) (.node [v778,v776,v765,v760,v842] .nil .nil)) (.node [v778,v762,v765,v757,v782] (.node [v778,v762,v777,v760,v782] (.node [v778,v762,v822,v765,v782] .nil .nil) .nil) (.node [v778,v762,v765,v780,v782] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4lllrl : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4lllrl = true := by decide +kernel
def tree_eaa8c880_4lllrr : BinaryTree (List W) := (.node [v776,v765,v760,v782,v769] (.node [v776,v826,v760,v758,v842] (.node [v882,v852,v760,v782,v758] (.node [v883,v762,v765,v760,v782] (.node [v778,v762,v847,v760,v782] .nil .nil) .nil) (.node [v776,v822,v765,v758,v842] (.node [v776,v774,v765,v758,v842] .nil .nil) .nil)) (.node [v776,v765,v757,v758,v842] (.node [v776,v777,v760,v758,v842] (.node [v776,v777,v760,v782,v758] .nil .nil) .nil) (.node [v776,v765,v780,v758,v842] .nil .nil))) (.node [v776,v765,v760,v758,v842] (.node [v776,v765,v760,v758,v843] (.node [v776,v765,v760,v769,v842] (.node [v776,v765,v760,v779,v758] .nil .nil) .nil) (.node [v776,v765,v760,v758,v827] .nil .nil)) (.node [v884,v852,v760,v782,v758] (.node [v776,v847,v760,v758,v842] (.node [v776,v768,v760,v758,v842] .nil .nil) .nil) (.node [v885,v765,v834,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4lllrr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4lllrr = true := by decide +kernel
def tree_eaa8c880_4lllr : BinaryTree (List W) := .node [v778,v762,v765,v760,v782] tree_eaa8c880_4lllrl tree_eaa8c880_4lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4lllr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4lllr = true := by
  change (_ && everyKey _ tree_eaa8c880_4lllrl && everyKey _ tree_eaa8c880_4lllrr) = true
  rw [ok_tree_eaa8c880_4lllrl, ok_tree_eaa8c880_4lllrr]
  decide +kernel
def tree_eaa8c880_4lll : BinaryTree (List W) := .node [v870,v786,v765,v760,v782] tree_eaa8c880_4llll tree_eaa8c880_4lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4lll : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4lll = true := by
  change (_ && everyKey _ tree_eaa8c880_4llll && everyKey _ tree_eaa8c880_4lllr) = true
  rw [ok_tree_eaa8c880_4llll, ok_tree_eaa8c880_4lllr]
  decide +kernel
def tree_eaa8c880_4llrll : BinaryTree (List W) := (.node [v886,v765,v760,v887,v758] (.node [v888,v765,v834,v782,v758] (.node [v889,v762,v765,v757,v758] (.node [v885,v765,v890,v782,v758] (.node [v885,v765,v840,v782,v758] .nil .nil) .nil) (.node [v888,v765,v891,v782,v758] (.node [v888,v861,v765,v782,v758] .nil .nil) .nil)) (.node [v886,v765,v757,v887,v758] (.node [v886,v774,v765,v887,v758] (.node [v892,v772,v760,v782,v758] .nil .nil) .nil) (.node [v886,v765,v848,v887,v758] .nil .nil))) (.node [v871,v773,v762,v765,v760] (.node [v886,v765,v832,v887,v758] (.node [v886,v765,v760,v779,v758] (.node [v886,v765,v760,v893,v758] .nil .nil) .nil) (.node [v886,v768,v760,v782,v758] .nil .nil)) (.node [v871,v762,v765,v792,v758] (.node [v871,v762,v765,v757,v758] (.node [v871,v762,v765,v757,v785] .nil .nil) .nil) (.node [v871,v762,v765,v760,v894] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4llrll : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4llrll = true := by decide +kernel
def tree_eaa8c880_4llrlr : BinaryTree (List W) := (.node [v895,v762,v896,v757,v758] (.node [v897,v762,v765,v760,v758] (.node [v897,v762,v800,v760,v758] (.node [v897,v762,v774,v765,v758] (.node [v897,v797,v765,v760,v758] .nil .nil) .nil) (.node [v897,v762,v765,v798,v898] (.node [v897,v762,v765,v757,v758] .nil .nil) .nil)) (.node [v897,v765,v760,v825,v758] (.node [v897,v762,v899,v760,v758] (.node [v897,v762,v765,v788,v758] .nil .nil) .nil) (.node [v895,v762,v774,v896,v758] .nil .nil))) (.node [v895,v762,v815,v760,v758] (.node [v895,v762,v896,v900,v758] (.node [v895,v762,v896,v760,v758] (.node [v895,v762,v896,v816,v758] .nil .nil) .nil) (.node [v895,v762,v901,v760,v758] .nil .nil)) (.node [v902,v762,v765,v757,v758] (.node [v903,v762,v774,v765,v758] (.node [v895,v770,v760,v782,v758] .nil .nil) .nil) (.node [v904,v762,v765,v757,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4llrlr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4llrlr = true := by decide +kernel
def tree_eaa8c880_4llrl : BinaryTree (List W) := .node [v871,v762,v765,v809,v758] tree_eaa8c880_4llrll tree_eaa8c880_4llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4llrl : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4llrl = true := by
  change (_ && everyKey _ tree_eaa8c880_4llrll && everyKey _ tree_eaa8c880_4llrlr) = true
  rw [ok_tree_eaa8c880_4llrll, ok_tree_eaa8c880_4llrlr]
  decide +kernel
def tree_eaa8c880_4llrrl : BinaryTree (List W) := (.node [v775,v765,v831,v782,v837] (.node [v905,v765,v760,v782,v758] (.node [v906,v765,v760,v782,v758] (.node [v907,v772,v760,v782,v758] (.node [v908,v762,v765,v760,v758] .nil .nil) .nil) (.node [v905,v765,v757,v782,v758] (.node [v905,v774,v765,v782,v758] .nil .nil) .nil)) (.node [v775,v762,v765,v757,v785] (.node [v909,v765,v891,v782,v758] (.node [v909,v765,v910,v782,v758] .nil .nil) .nil) (.node [v775,v774,v765,v782,v837] .nil .nil))) (.node [v775,v765,v760,v782,v911] (.node [v775,v765,v760,v767,v782] (.node [v775,v765,v760,v823,v782] (.node [v775,v765,v757,v782,v837] .nil .nil) .nil) (.node [v775,v765,v760,v782,v912] .nil .nil)) (.node [v775,v765,v760,v782,v837] (.node [v775,v765,v760,v782,v913] (.node [v775,v765,v760,v782,v914] .nil .nil) .nil) (.node [v775,v765,v840,v782,v837] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4llrrl : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4llrrl = true := by decide +kernel
def tree_eaa8c880_4llrrr : BinaryTree (List W) := (.node [v915,v765,v757,v782,v758] (.node [v783,v765,v757,v782,v758] (.node [v916,v765,v760,v782,v758] (.node [v917,v765,v891,v782,v758] (.node [v775,v768,v760,v782,v758] .nil .nil) .nil) (.node [v783,v774,v765,v782,v758] (.node [v918,v765,v760,v782,v758] .nil .nil) .nil)) (.node [v919,v765,v760,v782,v758] (.node [v783,v765,v760,v782,v758] (.node [v783,v765,v760,v785,v782] .nil .nil) .nil) (.node [v920,v765,v760,v782,v758] .nil .nil))) (.node [v787,v813,v760,v782,v758] (.node [v921,v765,v890,v782,v758] (.node [v921,v922,v765,v782,v758] (.node [v915,v765,v760,v782,v758] .nil .nil) .nil) (.node [v787,v774,v772,v782,v758] .nil .nil)) (.node [v787,v768,v760,v782,v758] (.node [v787,v770,v760,v782,v758] (.node [v787,v759,v760,v782,v758] .nil .nil) .nil) (.node [v787,v772,v757,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4llrrr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4llrrr = true := by decide +kernel
def tree_eaa8c880_4llrr : BinaryTree (List W) := .node [v775,v839,v760,v782,v758] tree_eaa8c880_4llrrl tree_eaa8c880_4llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4llrr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4llrr = true := by
  change (_ && everyKey _ tree_eaa8c880_4llrrl && everyKey _ tree_eaa8c880_4llrrr) = true
  rw [ok_tree_eaa8c880_4llrrl, ok_tree_eaa8c880_4llrrr]
  decide +kernel
def tree_eaa8c880_4llr : BinaryTree (List W) := .node [v923,v762,v765,v757,v758] tree_eaa8c880_4llrl tree_eaa8c880_4llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4llr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4llr = true := by
  change (_ && everyKey _ tree_eaa8c880_4llrl && everyKey _ tree_eaa8c880_4llrr) = true
  rw [ok_tree_eaa8c880_4llrl, ok_tree_eaa8c880_4llrr]
  decide +kernel
def tree_eaa8c880_4ll : BinaryTree (List W) := .node [v885,v765,v835,v782,v758] tree_eaa8c880_4lll tree_eaa8c880_4llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4ll : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4ll = true := by
  change (_ && everyKey _ tree_eaa8c880_4lll && everyKey _ tree_eaa8c880_4llr) = true
  rw [ok_tree_eaa8c880_4lll, ok_tree_eaa8c880_4llr]
  decide +kernel
def tree_eaa8c880_4lrlll : BinaryTree (List W) := (.node [v924,v765,v760,v782,v758] (.node [v773,v762,v765,v760,v758] (.node [v773,v762,v765,v760] (.node [v925,v772,v760,v782,v758] (.node [v787,v926,v760,v782,v758] .nil .nil) .nil) (.node [v773,v762,v765,v760,v782] (.node [v773,v762,v765,v760,v785] .nil .nil) .nil)) (.node [v927,v774,v765,v782,v758] (.node [v928,v772,v760,v782,v758] (.node [v773,v762,v765,v760,v929] .nil .nil) .nil) (.node [v927,v765,v760,v782,v758] .nil .nil))) (.node [v793,v765,v760,v782,v758] (.node [v930,v765,v760,v782,v758] (.node [v930,v765,v757,v782,v758] (.node [v931,v765,v760,v782,v758] .nil .nil) .nil) (.node [v793,v765,v757,v782,v758] .nil .nil)) (.node [v786,v791,v765,v782,v758] (.node [v786,v774,v765,v782,v758] (.node [v932,v765,v760,v782,v758] .nil .nil) .nil) (.node [v786,v790,v760,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4lrlll : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4lrlll = true := by decide +kernel
def tree_eaa8c880_4lrllr : BinaryTree (List W) := (.node [v797,v765,v798,v782,v898] (.node [v933,v765,v760,v782,v758] (.node [v786,v765,v760,v785,v929] (.node [v786,v765,v760,v785,v782] (.node [v786,v765,v792,v782,v758] .nil .nil) .nil) (.node [v786,v795,v760,v782,v758] (.node [v786,v765,v760,v782,v758] .nil .nil) .nil)) (.node [v797,v765,v891,v782,v758] (.node [v797,v800,v760,v782,v758] (.node [v797,v774,v765,v782,v758] .nil .nil) .nil) (.node [v797,v765,v757,v782,v758] .nil .nil))) (.node [v797,v899,v760,v782,v758] (.node [v797,v765,v840,v782,v758] (.node [v797,v765,v760,v782,v758] (.node [v797,v765,v760,v799,v758] .nil .nil) .nil) (.node [v797,v765,v890,v782,v758] .nil .nil)) (.node [v934,v765,v760,v782,v758] (.node [v935,v765,v760,v782,v758] (.node [v936,v765,v760,v782,v758] .nil .nil) .nil) (.node [v937,v774,v765,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4lrllr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4lrllr = true := by decide +kernel
def tree_eaa8c880_4lrll : BinaryTree (List W) := .node [v786,v765,v757,v782,v758] tree_eaa8c880_4lrlll tree_eaa8c880_4lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4lrll : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4lrll = true := by
  change (_ && everyKey _ tree_eaa8c880_4lrlll && everyKey _ tree_eaa8c880_4lrllr) = true
  rw [ok_tree_eaa8c880_4lrlll, ok_tree_eaa8c880_4lrllr]
  decide +kernel
def tree_eaa8c880_4lrlrl : BinaryTree (List W) := (.node [v801,v896,v760,v782,v758] (.node [v801,v765,v881,v782,v758] (.node [v801,v852,v760,v782,v758] (.node [v801,v879,v765,v782,v758] (.node [v801,v774,v765,v782,v758] .nil .nil) .nil) (.node [v801,v765,v757,v782,v758] (.node [v801,v796,v760,v782,v758] .nil .nil) .nil)) (.node [v801,v768,v760,v782,v758] (.node [v801,v765,v760,v782,v758] (.node [v801,v765,v760,v782,v771] .nil .nil) .nil) (.node [v801,v772,v760,v782,v758] .nil .nil))) (.node [v938,v765,v760,v782,v758] (.node [v939,v765,v760,v782,v758] (.node [v940,v765,v760,v782,v758] (.node [v941,v765,v760,v782,v758] .nil .nil) .nil) (.node [v942,v765,v760,v782,v758] .nil .nil)) (.node [v762,v943,v765,v799,v758] (.node [v762,v943,v765,v757,v758] (.node [v762,v944,v765,v782,v758] .nil .nil) .nil) (.node [v762,v774,v805,v782,v814] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4lrlrl : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4lrlrl = true := by decide +kernel
def tree_eaa8c880_4lrlrr : BinaryTree (List W) := (.node [v762,v774,v765,v785,v929] (.node [v762,v774,v790,v782,v758] (.node [v762,v774,v777,v782,v758] (.node [v762,v774,v945,v782,v758] (.node [v762,v774,v803,v782,v758] .nil .nil) .nil) (.node [v762,v774,v946,v782,v758] (.node [v762,v774,v800,v782,v758] .nil .nil) .nil)) (.node [v762,v774,v765,v947,v758] (.node [v762,v774,v765,v948,v758] (.node [v762,v774,v765,v757,v758] .nil .nil) .nil) (.node [v762,v774,v765,v949,v758] .nil .nil))) (.node [v762,v774,v765,v782,v771] (.node [v762,v774,v765,v799,v758] (.node [v762,v774,v765,v950,v758] (.node [v762,v774,v765,v951,v758] .nil .nil) .nil) (.node [v762,v774,v765,v782,v769] .nil .nil)) (.node [v762,v774,v952,v782,v758] (.node [v762,v774,v765,v953,v758] (.node [v762,v774,v765,v782,v758] .nil .nil) .nil) (.node [v762,v774,v839,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4lrlrr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4lrlrr = true := by decide +kernel
def tree_eaa8c880_4lrlr : BinaryTree (List W) := .node [v762,v774,v826,v782,v758] tree_eaa8c880_4lrlrl tree_eaa8c880_4lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4lrlr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4lrlr = true := by
  change (_ && everyKey _ tree_eaa8c880_4lrlrl && everyKey _ tree_eaa8c880_4lrlrr) = true
  rw [ok_tree_eaa8c880_4lrlrl, ok_tree_eaa8c880_4lrlrr]
  decide +kernel
def tree_eaa8c880_4lrl : BinaryTree (List W) := .node [v937,v765,v760,v782,v758] tree_eaa8c880_4lrll tree_eaa8c880_4lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4lrl : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4lrl = true := by
  change (_ && everyKey _ tree_eaa8c880_4lrll && everyKey _ tree_eaa8c880_4lrlr) = true
  rw [ok_tree_eaa8c880_4lrll, ok_tree_eaa8c880_4lrlr]
  decide +kernel
def tree_eaa8c880_4lrrll : BinaryTree (List W) := (.node [v762,v954,v765,v757,v758] (.node [v762,v955,v765,v782,v758] (.node [v762,v774,v795,v782,v758] (.node [v762,v774,v899,v782,v758] (.node [v762,v774,v768,v782,v758] .nil .nil) .nil) (.node [v762,v956,v765,v782,v758] (.node [v762,v774,v847,v782,v758] .nil .nil) .nil)) (.node [v762,v957,v765,v757,v758] (.node [v762,v958,v765,v782,v758] (.node [v762,v959,v765,v782,v758] .nil .nil) .nil) (.node [v762,v960,v765,v757,v758] .nil .nil))) (.node [v762,v961,v765,v782,v758] (.node [v762,v954,v765,v962,v758] (.node [v762,v954,v765,v782,v758] (.node [v762,v954,v765,v760,v758] .nil .nil) .nil) (.node [v762,v963,v765,v799,v758] .nil .nil)) (.node [v762,v822,v765,v782,v769] (.node [v762,v822,v777,v782,v758] (.node [v762,v964,v765,v782,v758] .nil .nil) .nil) (.node [v762,v822,v765,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4lrrll : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4lrrll = true := by decide +kernel
def tree_eaa8c880_4lrrlr : BinaryTree (List W) := (.node [v762,v802,v765,v782,v758] (.node [v762,v879,v765,v782,v771] (.node [v762,v791,v765,v785,v929] (.node [v762,v791,v790,v782,v758] (.node [v762,v965,v765,v782,v758] .nil .nil) .nil) (.node [v762,v791,v795,v782,v758] (.node [v762,v791,v765,v782,v758] .nil .nil) .nil)) (.node [v762,v802,v765,v798,v782] (.node [v762,v966,v765,v782,v758] (.node [v762,v879,v765,v782,v758] .nil .nil) .nil) (.node [v762,v802,v765,v760,v782] .nil .nil))) (.node [v762,v967,v765,v782,v758] (.node [v762,v968,v765,v757,v785] (.node [v762,v969,v765,v782,v758] (.node [v762,v802,v765,v782,v898] .nil .nil) .nil) (.node [v762,v970,v765,v782,v758] .nil .nil)) (.node [v762,v971,v757,v782,v758] (.node [v762,v972,v760,v782,v758] (.node [v762,v973,v765,v782,v758] .nil .nil) .nil) (.node [v762,v971,v760,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4lrrlr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4lrrlr = true := by decide +kernel
def tree_eaa8c880_4lrrl : BinaryTree (List W) := .node [v762,v822,v847,v782,v758] tree_eaa8c880_4lrrll tree_eaa8c880_4lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4lrrl : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4lrrl = true := by
  change (_ && everyKey _ tree_eaa8c880_4lrrll && everyKey _ tree_eaa8c880_4lrrlr) = true
  rw [ok_tree_eaa8c880_4lrrll, ok_tree_eaa8c880_4lrrlr]
  decide +kernel
def tree_eaa8c880_4lrrrl : BinaryTree (List W) := (.node [v762,v796,v760,v758,v827] (.node [v762,v852,v760,v782,v771] (.node [v762,v974,v782,v758,v820] (.node [v762,v974,v782,v758,v849] (.node [v762,v974,v975,v782,v758] .nil .nil) .nil) (.node [v762,v858,v782,v758,v976] (.node [v762,v974,v782,v758,v976] .nil .nil) .nil)) (.node [v762,v796,v757,v758,v841] (.node [v762,v813,v760,v782,v758] (.node [v762,v977,v765,v782,v758] .nil .nil) .nil) (.node [v762,v796,v760,v782,v771] .nil .nil))) (.node [v762,v805,v810,v782,v814] (.node [v762,v978,v760,v782,v758] (.node [v762,v759,v765,v757,v758] (.node [v762,v979,v765,v757,v758] .nil .nil) .nil) (.node [v762,v805,v765,v757,v785] .nil .nil)) (.node [v762,v805,v760,v763,v782] (.node [v762,v805,v757,v782,v814] (.node [v762,v805,v784,v760,v782] .nil .nil) .nil) (.node [v762,v805,v760,v782,v980] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4lrrrl : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4lrrrl = true := by decide +kernel
def tree_eaa8c880_4lrrrr : BinaryTree (List W) := (.node [v762,v803,v757,v782,v758] (.node [v762,v981,v760,v782,v758] (.node [v762,v805,v760,v782,v814] (.node [v762,v805,v760,v782,v982] (.node [v762,v805,v760,v782,v983] .nil .nil) .nil) (.node [v762,v984,v985,v782,v758] (.node [v762,v805,v782,v849,v814] .nil .nil) .nil)) (.node [v762,v986,v760,v782,v758] (.node [v762,v826,v760,v782,v758] (.node [v762,v826,v757,v782,v758] .nil .nil) .nil) (.node [v762,v987,v760,v782,v758] .nil .nil))) (.node [v762,v988,v757,v782,v758] (.node [v762,v989,v760,v782,v758] (.node [v762,v803,v760,v782,v758] (.node [v762,v803,v760,v785,v782] .nil .nil) .nil) (.node [v762,v990,v760,v782,v758] .nil .nil)) (.node [v762,v945,v760,v782,v758] (.node [v762,v991,v765,v782,v758] (.node [v762,v988,v760,v782,v758] .nil .nil) .nil) (.node [v762,v992,v760,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4lrrrr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4lrrrr = true := by decide +kernel
def tree_eaa8c880_4lrrr : BinaryTree (List W) := .node [v762,v805,v760,v782,v993] tree_eaa8c880_4lrrrl tree_eaa8c880_4lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4lrrr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4lrrr = true := by
  change (_ && everyKey _ tree_eaa8c880_4lrrrl && everyKey _ tree_eaa8c880_4lrrrr) = true
  rw [ok_tree_eaa8c880_4lrrrl, ok_tree_eaa8c880_4lrrrr]
  decide +kernel
def tree_eaa8c880_4lrr : BinaryTree (List W) := .node [v762,v994,v782,v758,v820] tree_eaa8c880_4lrrl tree_eaa8c880_4lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4lrr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4lrr = true := by
  change (_ && everyKey _ tree_eaa8c880_4lrrl && everyKey _ tree_eaa8c880_4lrrr) = true
  rw [ok_tree_eaa8c880_4lrrl, ok_tree_eaa8c880_4lrrr]
  decide +kernel
def tree_eaa8c880_4lr : BinaryTree (List W) := .node [v762,v774,v995,v782,v758] tree_eaa8c880_4lrl tree_eaa8c880_4lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4lr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4lr = true := by
  change (_ && everyKey _ tree_eaa8c880_4lrl && everyKey _ tree_eaa8c880_4lrr) = true
  rw [ok_tree_eaa8c880_4lrl, ok_tree_eaa8c880_4lrr]
  decide +kernel
def tree_eaa8c880_4l : BinaryTree (List W) := .node [v787,v772,v760,v782,v758] tree_eaa8c880_4ll tree_eaa8c880_4lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4l : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4l = true := by
  change (_ && everyKey _ tree_eaa8c880_4ll && everyKey _ tree_eaa8c880_4lr) = true
  rw [ok_tree_eaa8c880_4ll, ok_tree_eaa8c880_4lr]
  decide +kernel
def tree_eaa8c880_4rllll : BinaryTree (List W) := (.node [v762,v800,v798,v782,v898] (.node [v762,v996,v760,v782,v758] (.node [v762,v777,v760,v782,v769] (.node [v762,v777,v780,v782,v758] (.node [v762,v777,v757,v782,v758] .nil .nil) .nil) (.node [v762,v997,v760,v782,v758] (.node [v762,v777,v760,v782,v758] .nil .nil) .nil)) (.node [v762,v800,v985,v782,v758] (.node [v762,v806,v760,v782,v758] (.node [v762,v806,v757,v782,v758] .nil .nil) .nil) (.node [v762,v800,v757,v782,v758] .nil .nil))) (.node [v762,v946,v760,v782,v758] (.node [v762,v800,v782,v758,v849] (.node [v762,v800,v760,v782,v758] (.node [v762,v800,v760,v799,v758] .nil .nil) .nil) (.node [v762,v800,v782,v758,v976] .nil .nil)) (.node [v762,v790,v757,v782,v758] (.node [v762,v998,v760,v782,v758] (.node [v762,v999,v760,v782,v758] .nil .nil) .nil) (.node [v762,v790,v792,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rllll : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rllll = true := by decide +kernel
def tree_eaa8c880_4rlllr : BinaryTree (List W) := (.node [v762,v765,v1000,v782,v758] (.node [v762,v1001,v760,v782,v758] (.node [v762,v1002,v760,v782,v758] (.node [v762,v790,v760,v782,v758] (.node [v762,v790,v760,v785,v929] .nil .nil) .nil) (.node [v762,v1003,v760,v782,v758] (.node [v762,v1004,v760,v782,v758] .nil .nil) .nil)) (.node [v762,v765,v1005,v782,v758] (.node [v762,v765,v985,v799,v758] (.node [v762,v1006,v760,v782,v758] .nil .nil) .nil) (.node [v762,v765,v1007,v782,v758] .nil .nil))) (.node [v762,v765,v1008,v782,v758] (.node [v762,v765,v784,v760,v782] (.node [v762,v765,v810,v782,v758] (.node [v762,v765,v1009,v782,v758] .nil .nil) .nil) (.node [v762,v765,v1010,v782,v758] .nil .nil)) (.node [v762,v765,v975,v782,v758] (.node [v762,v765,v1011,v757,v758] (.node [v762,v765,v815,v760,v758] .nil .nil) .nil) (.node [v762,v765,v1012,v760,v782] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rlllr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rlllr = true := by decide +kernel
def tree_eaa8c880_4rlll : BinaryTree (List W) := .node [v762,v790,v760,v785,v782] tree_eaa8c880_4rllll tree_eaa8c880_4rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rlll : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rlll = true := by
  change (_ && everyKey _ tree_eaa8c880_4rllll && everyKey _ tree_eaa8c880_4rlllr) = true
  rw [ok_tree_eaa8c880_4rllll, ok_tree_eaa8c880_4rlllr]
  decide +kernel
def tree_eaa8c880_4rllrl : BinaryTree (List W) := (.node [v762,v765,v757,v785,v758] (.node [v762,v765,v1013,v782,v758] (.node [v762,v765,v891,v799,v758] (.node [v762,v765,v1014,v782,v818] (.node [v762,v765,v1015,v760,v782] .nil .nil) .nil) (.node [v762,v765,v1016,v782,v758] (.node [v762,v765,v1017,v782,v758] .nil .nil) .nil)) (.node [v762,v765,v757,v809,v758] (.node [v762,v765,v757,v808,v758] (.node [v762,v765,v831,v782,v758] .nil .nil) .nil) (.node [v762,v765,v757,v788,v758] .nil .nil))) (.node [v762,v765,v757,v1018,v758] (.node [v762,v765,v757,v1019,v758] (.node [v762,v765,v757,v785,v929] (.node [v762,v765,v757,v785,v818] .nil .nil) .nil) (.node [v762,v765,v757,v1020,v758] .nil .nil)) (.node [v762,v765,v757,v767,v758] (.node [v762,v765,v757,v1021,v758] (.node [v762,v765,v757,v1022,v758] .nil .nil) .nil) (.node [v762,v765,v757,v763,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rllrl : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rllrl = true := by decide +kernel
def tree_eaa8c880_4rllrr : BinaryTree (List W) := (.node [v762,v765,v757,v1023,v758] (.node [v762,v765,v757,v782,v821] (.node [v762,v765,v757,v782,v771] (.node [v762,v765,v757,v782,v769] (.node [v762,v765,v757,v782,v1024] .nil .nil) .nil) (.node [v762,v765,v757,v782,v836] (.node [v762,v765,v757,v782,v758] .nil .nil) .nil)) (.node [v762,v765,v757,v876,v758] (.node [v762,v765,v757,v1025,v758] (.node [v762,v765,v757,v1026,v758] .nil .nil) .nil) (.node [v762,v765,v757,v877,v758] .nil .nil))) (.node [v762,v765,v757,v1027,v758] (.node [v762,v765,v757,v1028,v758] (.node [v762,v765,v757,v1029,v758] (.node [v762,v765,v757,v1030,v758] .nil .nil) .nil) (.node [v762,v765,v757,v1031,v758] .nil .nil)) (.node [v762,v765,v1032,v782,v758] (.node [v762,v765,v757,v758,v827] (.node [v762,v765,v757,v962,v758] .nil .nil) .nil) (.node [v762,v765,v1033,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rllrr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rllrr = true := by decide +kernel
def tree_eaa8c880_4rllr : BinaryTree (List W) := .node [v762,v765,v757,v799,v758] tree_eaa8c880_4rllrl tree_eaa8c880_4rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rllr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rllr = true := by
  change (_ && everyKey _ tree_eaa8c880_4rllrl && everyKey _ tree_eaa8c880_4rllrr) = true
  rw [ok_tree_eaa8c880_4rllrl, ok_tree_eaa8c880_4rllrr]
  decide +kernel
def tree_eaa8c880_4rll : BinaryTree (List W) := .node [v762,v765,v1015,v757,v782] tree_eaa8c880_4rlll tree_eaa8c880_4rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rll : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rll = true := by
  change (_ && everyKey _ tree_eaa8c880_4rlll && everyKey _ tree_eaa8c880_4rllr) = true
  rw [ok_tree_eaa8c880_4rlll, ok_tree_eaa8c880_4rllr]
  decide +kernel
def tree_eaa8c880_4rlrll : BinaryTree (List W) := (.node [v762,v765,v1034,v782,v758] (.node [v762,v765,v789,v782,v758] (.node [v762,v765,v816,v782,v758] (.node [v762,v765,v1035,v782,v758] (.node [v762,v765,v1036,v782,v758] .nil .nil) .nil) (.node [v762,v765,v1037,v782,v758] (.node [v762,v765,v1038,v782,v758] .nil .nil) .nil)) (.node [v762,v765,v1039,v782,v758] (.node [v762,v765,v1040,v782,v758] (.node [v762,v765,v1041,v782,v758] .nil .nil) .nil) (.node [v762,v765,v848,v782,v758] .nil .nil))) (.node [v762,v765,v798,v799,v898] (.node [v762,v765,v1042,v782,v758] (.node [v762,v765,v1043,v782,v758] (.node [v762,v765,v1044,v782,v758] .nil .nil) .nil) (.node [v762,v765,v798,v799,v758] .nil .nil)) (.node [v762,v765,v1045,v782,v758] (.node [v762,v765,v798,v782,v898] (.node [v762,v765,v798,v782,v818] .nil .nil) .nil) (.node [v762,v765,v1046,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rlrll : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rlrll = true := by decide +kernel
def tree_eaa8c880_4rlrlr : BinaryTree (List W) := (.node [v762,v765,v1047,v782,v758] (.node [v762,v765,v1048,v782,v758] (.node [v762,v765,v780,v782,v758] (.node [v762,v765,v780,v782,v769] (.node [v762,v765,v1049,v782,v758] .nil .nil) .nil) (.node [v762,v765,v1050,v782,v758] (.node [v762,v765,v1051,v782,v758] .nil .nil) .nil)) (.node [v762,v765,v792,v782,v758] (.node [v762,v765,v792,v785,v929] (.node [v762,v765,v792,v785,v758] .nil .nil) .nil) (.node [v762,v765,v1052,v782,v758] .nil .nil))) (.node [v762,v765,v1053,v782,v758] (.node [v762,v765,v881,v782,v758] (.node [v762,v765,v881,v782,v771] (.node [v762,v765,v1054,v782,v758] .nil .nil) .nil) (.node [v762,v765,v1055,v782,v758] .nil .nil)) (.node [v762,v765,v1056,v782,v758] (.node [v762,v765,v1057,v782,v758] (.node [v762,v765,v1058,v782,v758] .nil .nil) .nil) (.node [v762,v765,v760,v785,v843] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rlrlr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rlrlr = true := by decide +kernel
def tree_eaa8c880_4rlrl : BinaryTree (List W) := .node [v762,v765,v1059,v782,v758] tree_eaa8c880_4rlrll tree_eaa8c880_4rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rlrl : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rlrl = true := by
  change (_ && everyKey _ tree_eaa8c880_4rlrll && everyKey _ tree_eaa8c880_4rlrlr) = true
  rw [ok_tree_eaa8c880_4rlrll, ok_tree_eaa8c880_4rlrlr]
  decide +kernel
def tree_eaa8c880_4rlrrl : BinaryTree (List W) := (.node [v762,v765,v760,v1060,v758] (.node [v762,v765,v760,v799,v758] (.node [v762,v765,v760,v823,v782] (.node [v762,v765,v760,v785,v929] (.node [v762,v765,v760,v785,v1061] .nil .nil) .nil) (.node [v762,v765,v760,v1062,v758] (.node [v762,v765,v760,v1063,v758] .nil .nil) .nil)) (.node [v762,v765,v760,v1064,v758] (.node [v762,v765,v760,v1065,v758] (.node [v762,v765,v760,v1066,v758] .nil .nil) .nil) (.node [v762,v765,v760,v1067,v758] .nil .nil))) (.node [v762,v765,v760,v782,v769] (.node [v762,v765,v760,v782,v1024] (.node [v762,v765,v760,v782,v1068] (.node [v762,v765,v760,v1069,v758] .nil .nil) .nil) (.node [v762,v765,v760,v782,v761] .nil .nil)) (.node [v762,v765,v760,v782,v1070] (.node [v762,v765,v760,v782,v1071] (.node [v762,v765,v760,v782,v1072] .nil .nil) .nil) (.node [v762,v765,v760,v782,v1073] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rlrrl : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rlrrl = true := by decide +kernel
def tree_eaa8c880_4rlrrr : BinaryTree (List W) := (.node [v762,v765,v760,v782,v821] (.node [v762,v765,v760,v782,v1074] (.node [v762,v765,v760,v782,v1075] (.node [v762,v765,v760,v782,v1076] (.node [v762,v765,v760,v782,v1077] .nil .nil) .nil) (.node [v762,v765,v760,v782,v758] (.node [v762,v765,v760,v782,v1078] .nil .nil) .nil)) (.node [v762,v765,v760,v782,v1079] (.node [v762,v765,v760,v782,v1080] (.node [v762,v765,v760,v782,v1081] .nil .nil) .nil) (.node [v762,v765,v760,v782,v836] .nil .nil))) (.node [v762,v765,v1082,v782,v758] (.node [v762,v765,v760,v779,v758] (.node [v762,v765,v760,v1083,v758] (.node [v762,v765,v760,v1084,v758] .nil .nil) .nil) (.node [v762,v765,v760,v758,v845] .nil .nil)) (.node [v762,v765,v1085,v782,v758] (.node [v762,v765,v1086,v782,v758] (.node [v762,v765,v1087,v782,v758] .nil .nil) .nil) (.node [v762,v765,v1088,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rlrrr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rlrrr = true := by decide +kernel
def tree_eaa8c880_4rlrr : BinaryTree (List W) := .node [v762,v765,v760,v782,v771] tree_eaa8c880_4rlrrl tree_eaa8c880_4rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rlrr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rlrr = true := by
  change (_ && everyKey _ tree_eaa8c880_4rlrrl && everyKey _ tree_eaa8c880_4rlrrr) = true
  rw [ok_tree_eaa8c880_4rlrrl, ok_tree_eaa8c880_4rlrrr]
  decide +kernel
def tree_eaa8c880_4rlr : BinaryTree (List W) := .node [v762,v765,v760,v785,v818] tree_eaa8c880_4rlrl tree_eaa8c880_4rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rlr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rlr = true := by
  change (_ && everyKey _ tree_eaa8c880_4rlrl && everyKey _ tree_eaa8c880_4rlrr) = true
  rw [ok_tree_eaa8c880_4rlrl, ok_tree_eaa8c880_4rlrr]
  decide +kernel
def tree_eaa8c880_4rl : BinaryTree (List W) := .node [v762,v765,v1089,v782,v758] tree_eaa8c880_4rll tree_eaa8c880_4rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rl : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rl = true := by
  change (_ && everyKey _ tree_eaa8c880_4rll && everyKey _ tree_eaa8c880_4rlr) = true
  rw [ok_tree_eaa8c880_4rll, ok_tree_eaa8c880_4rlr]
  decide +kernel
def tree_eaa8c880_4rrlll : BinaryTree (List W) := (.node [v762,v765,v900,v782,v758] (.node [v762,v765,v832,v782,v758] (.node [v762,v765,v1090,v782,v758] (.node [v762,v765,v807,v782,v898] (.node [v762,v765,v808,v782,v898] .nil .nil) .nil) (.node [v762,v765,v1091,v782,v758] (.node [v762,v765,v1092,v782,v758] .nil .nil) .nil)) (.node [v762,v765,v788,v782,v758] (.node [v762,v765,v1093,v782,v758] (.node [v762,v765,v809,v782,v758] .nil .nil) .nil) (.node [v762,v765,v1094,v782,v758] .nil .nil))) (.node [v762,v765,v1095,v782,v758] (.node [v762,v765,v766,v782,v758] (.node [v762,v765,v1096,v782,v758] (.node [v762,v765,v1097,v782,v758] .nil .nil) .nil) (.node [v762,v765,v840,v782,v758] .nil .nil)) (.node [v762,v765,v1098,v782,v758] (.node [v762,v765,v1099,v782,v758] (.node [v762,v765,v890,v799,v758] .nil .nil) .nil) (.node [v762,v765,v799,v758,v976] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rrlll : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rrlll = true := by decide +kernel
def tree_eaa8c880_4rrllr : BinaryTree (List W) := (.node [v762,v1100,v760,v782,v758] (.node [v762,v765,v782,v758,v1101] (.node [v762,v765,v782,v758,v764] (.node [v762,v765,v782,v811,v898] (.node [v762,v765,v782,v1102,v758] .nil .nil) .nil) (.node [v762,v765,v782,v758,v1103] (.node [v762,v765,v782,v758,v849] .nil .nil) .nil)) (.node [v762,v1104,v760,v782,v758] (.node [v762,v1105,v760,v782,v758] (.node [v762,v765,v782,v758,v1106] .nil .nil) .nil) (.node [v762,v952,v760,v782,v758] .nil .nil))) (.node [v762,v1107,v760,v782,v758] (.node [v762,v839,v760,v782,v758] (.node [v762,v839,v757,v782,v758] (.node [v762,v1108,v760,v782,v758] .nil .nil) .nil) (.node [v762,v1107,v757,v782,v758] .nil .nil)) (.node [v762,v768,v757,v782,v758] (.node [v762,v1109,v760,v782,v758] (.node [v762,v995,v760,v782,v758] .nil .nil) .nil) (.node [v762,v768,v760,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rrllr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rrllr = true := by decide +kernel
def tree_eaa8c880_4rrll : BinaryTree (List W) := .node [v762,v765,v782,v1110,v758] tree_eaa8c880_4rrlll tree_eaa8c880_4rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rrll : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rrll = true := by
  change (_ && everyKey _ tree_eaa8c880_4rrlll && everyKey _ tree_eaa8c880_4rrllr) = true
  rw [ok_tree_eaa8c880_4rrlll, ok_tree_eaa8c880_4rrllr]
  decide +kernel
def tree_eaa8c880_4rrlrl : BinaryTree (List W) := (.node [v762,v1111,v757,v782,v758] (.node [v762,v1112,v760,v782,v758] (.node [v762,v867,v784,v760,v782] (.node [v762,v985,v782,v758,v849] (.node [v762,v772,v760,v782,v771] .nil .nil) .nil) (.node [v762,v867,v760,v782,v1113] (.node [v762,v867,v760,v782,v1114] .nil .nil) .nil)) (.node [v762,v896,v760,v1115,v758] (.node [v762,v896,v760,v782,v771] (.node [v762,v896,v815,v760,v758] .nil .nil) .nil) (.node [v762,v896,v760,v1116,v758] .nil .nil))) (.node [v762,v899,v760,v782,v758] (.node [v762,v899,v798,v782,v898] (.node [v762,v899,v757,v782,v758] (.node [v762,v1111,v760,v782,v758] .nil .nil) .nil) (.node [v762,v899,v760,v799,v758] .nil .nil)) (.node [v762,v795,v792,v782,v758] (.node [v762,v795,v757,v782,v758] (.node [v762,v1117,v760,v782,v758] .nil .nil) .nil) (.node [v762,v795,v760,v785,v929] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rrlrl : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rrlrl = true := by decide +kernel
def tree_eaa8c880_4rrlrr : BinaryTree (List W) := (.node [v762,v975,v760,v782,v758] (.node [v762,v784,v760,v782] (.node [v762,v847,v760,v782,v769] (.node [v762,v847,v780,v782,v758] (.node [v762,v847,v757,v782,v758] .nil .nil) .nil) (.node [v762,v1118,v760,v782,v758] (.node [v762,v847,v760,v782,v758] .nil .nil) .nil)) (.node [v762,v815,v760,v782,v758] (.node [v762,v784,v760,v782,v814] (.node [v762,v784,v760,v782,v758] .nil .nil) .nil) (.node [v762,v1119,v760,v782,v758] .nil .nil))) (.node [v1120,v765,v760,v782,v758] (.node [v762,v760,v782,v758,v1121] (.node [v762,v757,v782,v758,v817] (.node [v762,v975,v782,v758,v976] .nil .nil) .nil) (.node [v762,v760,v782,v758,v817] .nil .nil)) (.node [v1122,v765,v760,v782,v758] (.node [v1122,v774,v765,v782,v758] (.node [v1123,v765,v760,v782,v758] .nil .nil) .nil) (.node [v1124,v765,v760,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rrlrr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rrlrr = true := by decide +kernel
def tree_eaa8c880_4rrlr : BinaryTree (List W) := .node [v762,v795,v760,v782,v758] tree_eaa8c880_4rrlrl tree_eaa8c880_4rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rrlr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rrlr = true := by
  change (_ && everyKey _ tree_eaa8c880_4rrlrl && everyKey _ tree_eaa8c880_4rrlrr) = true
  rw [ok_tree_eaa8c880_4rrlrl, ok_tree_eaa8c880_4rrlrr]
  decide +kernel
def tree_eaa8c880_4rrl : BinaryTree (List W) := .node [v762,v1125,v760,v782,v758] tree_eaa8c880_4rrll tree_eaa8c880_4rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rrl : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rrl = true := by
  change (_ && everyKey _ tree_eaa8c880_4rrll && everyKey _ tree_eaa8c880_4rrlr) = true
  rw [ok_tree_eaa8c880_4rrll, ok_tree_eaa8c880_4rrlr]
  decide +kernel
def tree_eaa8c880_4rrrll : BinaryTree (List W) := (.node [v791,v765,v794,v782,v758] (.node [v774,v1126,v765,v782,v758] (.node [v819,v765,v757,v782,v758] (.node [v819,v805,v760,v782,v758] (.node [v819,v774,v765,v782,v758] .nil .nil) .nil) (.node [v819,v867,v760,v782,v758] (.node [v819,v765,v760,v782,v758] .nil .nil) .nil)) (.node [v774,v765,v880,v782,v758] (.node [v774,v765,v825,v782,v758] (.node [v774,v765,v770,v782,v758] .nil .nil) .nil) (.node [v774,v765,v794,v782,v758] .nil .nil))) (.node [v852,v813,v760,v782,v758] (.node [v1127,v765,v757,v782,v758] (.node [v1126,v765,v760,v782,v758] (.node [v879,v765,v880,v782,v758] .nil .nil) .nil) (.node [v1127,v765,v760,v782,v758] .nil .nil)) (.node [v813,v765,v760,v782,v758] (.node [v852,v760,v782,v758,v1128] (.node [v852,v768,v760,v782,v758] .nil .nil) .nil) (.node [v813,v772,v760,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rrrll : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rrrll = true := by decide +kernel
def tree_eaa8c880_4rrrlr : BinaryTree (List W) := (.node [v765,v770,v760,v782,v758] (.node [v777,v760,v887,v782,v758] (.node [v805,v770,v760,v782,v758] (.node [v1129,v765,v760,v782,v758] (.node [v759,v765,v760,v758,v842] .nil .nil) .nil) (.node [v777,v772,v760,v782,v758] (.node [v777,v770,v760,v782,v758] .nil .nil) .nil)) (.node [v765,v1130,v760,v782,v758] (.node [v790,v760,v794,v782,v758] (.node [v800,v760,v825,v782,v758] .nil .nil) .nil) (.node [v765,v770,v757,v782,v758] .nil .nil))) (.node [v765,v891,v840,v782,v758] (.node [v765,v1131,v760,v782,v758] (.node [v765,v772,v760,v782,v769] (.node [v765,v1132,v760,v782,v758] .nil .nil) .nil) (.node [v765,v891,v834,v782,v758] .nil .nil)) (.node [v765,v757,v1133,v782,v758] (.node [v765,v757,v838,v782,v758] (.node [v765,v891,v782,v1134,v758] .nil .nil) .nil) (.node [v765,v757,v825,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rrrlr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rrrlr = true := by decide +kernel
def tree_eaa8c880_4rrrl : BinaryTree (List W) := .node [v813,v760,v782,v758] tree_eaa8c880_4rrrll tree_eaa8c880_4rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rrrl : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rrrl = true := by
  change (_ && everyKey _ tree_eaa8c880_4rrrll && everyKey _ tree_eaa8c880_4rrrlr) = true
  rw [ok_tree_eaa8c880_4rrrll, ok_tree_eaa8c880_4rrrlr]
  decide +kernel
def tree_eaa8c880_4rrrrl : BinaryTree (List W) := (.node [v765,v760,v887,v782,v769] (.node [v765,v760,v838,v782,v758] (.node [v765,v792,v794,v782,v758] (.node [v765,v798,v825,v782,v898] (.node [v765,v757,v794,v782,v758] .nil .nil) .nil) (.node [v765,v760,v834,v782,v758] (.node [v765,v881,v880,v782,v758] .nil .nil) .nil)) (.node [v765,v760,v864,v782,v1135] (.node [v765,v760,v864,v782,v1136] (.node [v765,v760,v864,v823,v782] .nil .nil) .nil) (.node [v765,v760,v1137,v782,v758] .nil .nil))) (.node [v765,v760,v825,v799,v758] (.node [v765,v760,v887,v779,v758] (.node [v765,v760,v887,v1138,v758] (.node [v765,v760,v887,v1139,v758] .nil .nil) .nil) (.node [v765,v760,v1133,v782,v758] .nil .nil)) (.node [v765,v760,v880,v782,v771] (.node [v765,v760,v1140,v782,v758] (.node [v765,v760,v825,v782,v758] .nil .nil) .nil) (.node [v765,v760,v880,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rrrrl : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rrrrl = true := by decide +kernel
def tree_eaa8c880_4rrrrr : BinaryTree (List W) := (.node [v765,v834,v782,v758] (.node [v765,v760,v782,v779,v758] (.node [v765,v760,v823,v782] (.node [v765,v760,v1141,v782,v758] (.node [v765,v760,v794,v782,v758] .nil .nil) .nil) (.node [v765,v760,v823,v782,v837] (.node [v765,v760,v823,v782,v758] .nil .nil) .nil)) (.node [v765,v760,v779,v758,v842] (.node [v765,v760,v779,v758] (.node [v765,v760,v782,v758,v1142] .nil .nil) .nil) (.node [v765,v834,v890,v782,v758] .nil .nil))) (.node [v768,v760,v782,v758,v842] (.node [v770,v760,v782,v758,v841] (.node [v770,v867,v760,v782,v758] (.node [v839,v760,v864,v782,v758] .nil .nil) .nil) (.node [v768,v760,v864,v782,v758] .nil .nil)) (.node [v899,v760,v825,v782,v758] (.node [v772,v760,v782,v758,v827] (.node [v772,v760,v1143,v782,v758] .nil .nil) .nil) (.node [v795,v760,v794,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rrrrr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rrrrr = true := by decide +kernel
def tree_eaa8c880_4rrrr : BinaryTree (List W) := .node [v765,v760,v794,v785,v929] tree_eaa8c880_4rrrrl tree_eaa8c880_4rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rrrr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rrrr = true := by
  change (_ && everyKey _ tree_eaa8c880_4rrrrl && everyKey _ tree_eaa8c880_4rrrrr) = true
  rw [ok_tree_eaa8c880_4rrrrl, ok_tree_eaa8c880_4rrrrr]
  decide +kernel
def tree_eaa8c880_4rrr : BinaryTree (List W) := .node [v765,v757,v880,v782,v758] tree_eaa8c880_4rrrl tree_eaa8c880_4rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rrr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rrr = true := by
  change (_ && everyKey _ tree_eaa8c880_4rrrl && everyKey _ tree_eaa8c880_4rrrr) = true
  rw [ok_tree_eaa8c880_4rrrl, ok_tree_eaa8c880_4rrrr]
  decide +kernel
def tree_eaa8c880_4rr : BinaryTree (List W) := .node [v1144,v765,v760,v782,v758] tree_eaa8c880_4rrl tree_eaa8c880_4rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4rr : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4rr = true := by
  change (_ && everyKey _ tree_eaa8c880_4rrl && everyKey _ tree_eaa8c880_4rrr) = true
  rw [ok_tree_eaa8c880_4rrl, ok_tree_eaa8c880_4rrr]
  decide +kernel
def tree_eaa8c880_4r : BinaryTree (List W) := .node [v762,v765,v834,v782,v758] tree_eaa8c880_4rl tree_eaa8c880_4rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4r : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4r = true := by
  change (_ && everyKey _ tree_eaa8c880_4rl && everyKey _ tree_eaa8c880_4rr) = true
  rw [ok_tree_eaa8c880_4rl, ok_tree_eaa8c880_4rr]
  decide +kernel
def tree_eaa8c880_4 : BinaryTree (List W) := .node [v762,v1145,v760,v782,v758] tree_eaa8c880_4l tree_eaa8c880_4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_4 : everyKey (rowOK 3 tree_eaa8c880_3) tree_eaa8c880_4 = true := by
  change (_ && everyKey _ tree_eaa8c880_4l && everyKey _ tree_eaa8c880_4r) = true
  rw [ok_tree_eaa8c880_4l, ok_tree_eaa8c880_4r]
  decide +kernel
theorem closed_eaa8c880_4 : Closed 4 tree_eaa8c880_4 := closed_next 3 (by decide) tree_eaa8c880_4 tree_eaa8c880_3 closed_eaa8c880_3 ok_tree_eaa8c880_4
def tree_eaa8c880_5lllll : BinaryTree (List W) := (.node [v855,v762,v765,v760,v782,v758] (.node [v1146,v762,v765,v760,v782,v758] (.node [v506,v762,v765,v760,v782,v758] (.node [v506,v762,v765,v757,v782,v758] (.node [v506,v762,v774,v765,v782,v758] .nil .nil) .nil) (.node [v1147,v762,v765,v760,v782,v758] (.node [v1148,v762,v765,v760,v782,v758] .nil .nil) .nil)) (.node [v1149,v762,v765,v760,v782,v758] (.node [v1150,v762,v765,v760,v782,v758] (.node [v1151,v762,v765,v760,v782,v758] .nil .nil) .nil) (.node [v855,v762,v774,v765,v782,v758] (.node [v1152,v762,v765,v760,v782,v758] .nil .nil) .nil))) (.node [v1153,v762,v765,v760,v782,v758] (.node [v1154,v762,v765,v760,v782,v758] (.node [v1155,v762,v765,v760,v782,v758] (.node [v1156,v762,v765,v760,v782,v758] .nil .nil) .nil) (.node [v1157,v762,v765,v760,v782,v758] (.node [v1158,v762,v765,v760,v782,v758] .nil .nil) .nil)) (.node [v1159,v762,v765,v760,v782,v758] (.node [v1160,v762,v765,v760,v782,v758] (.node [v854,v762,v765,v760,v782,v758] .nil .nil) .nil) (.node [v1161,v762,v765,v760,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5lllll : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5lllll = true := by decide +kernel
def tree_eaa8c880_5llllr : BinaryTree (List W) := (.node [v850,v762,v852,v760,v782,v758] (.node [v1162,v762,v765,v760,v782,v758] (.node [v857,v762,v765,v760,v782,v758] (.node [v857,v762,v774,v765,v782,v758] (.node [v1163,v762,v765,v760,v782,v758] .nil .nil) .nil) (.node [v1164,v762,v765,v760,v782,v758] (.node [v1165,v762,v765,v760,v782,v758] .nil .nil) .nil)) (.node [v850,v787,v765,v760,v782,v758] (.node [v850,v775,v765,v760,v782,v758] (.node [v850,v886,v765,v760,v782,v758] .nil .nil) .nil) (.node [v850,v762,v774,v765,v782,v758] .nil .nil))) (.node [v850,v852,v765,v760,v782,v758] (.node [v850,v762,v765,v760,v782,v758] (.node [v850,v762,v765,v757,v782,v758] (.node [v850,v762,v796,v760,v782,v758] .nil .nil) .nil) (.node [v850,v762,v896,v760,v782,v758] (.node [v850,v762,v772,v760,v782,v758] .nil .nil) .nil)) (.node [v850,v765,v760,v782,v758,v842] (.node [v850,v765,v760,v864,v782,v758] (.node [v850,v852,v760,v782,v758] .nil .nil) .nil) (.node [v860,v762,v774,v765,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5llllr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5llllr = true := by decide +kernel
def tree_eaa8c880_5llll : BinaryTree (List W) := .node [v853,v762,v765,v760,v782,v758] tree_eaa8c880_5lllll tree_eaa8c880_5llllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5llll : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5llll = true := by
  change (_ && everyKey _ tree_eaa8c880_5lllll && everyKey _ tree_eaa8c880_5llllr) = true
  rw [ok_tree_eaa8c880_5lllll, ok_tree_eaa8c880_5llllr]
  decide +kernel
def tree_eaa8c880_5lllrl : BinaryTree (List W) := (.node [v863,v762,v765,v760,v782,v758] (.node [v863,v775,v765,v760,v782,v758] (.node [v1166,v762,v765,v760,v782,v758] (.node [v1167,v762,v765,v760,v782,v758] (.node [v1168,v762,v765,v760,v782,v758] .nil .nil) .nil) (.node [v863,v870,v762,v765,v760,v782] (.node [v1169,v762,v765,v760,v782,v758] .nil .nil) .nil)) (.node [v863,v762,v765,v757,v782,v758] (.node [v863,v762,v803,v760,v782,v758] (.node [v863,v762,v774,v765,v782,v758] .nil .nil) .nil) (.node [v863,v762,v765,v760,v785,v782] (.node [v863,v762,v765,v760,v864,v782] .nil .nil) .nil))) (.node [v868,v762,v765,v760,v782,v758] (.node [v863,v765,v760,v864,v782] (.node [v863,v762,v839,v760,v782,v758] (.node [v863,v762,v765,v760,v782,v837] .nil .nil) .nil) (.node [v868,v762,v765,v757,v782,v758] (.node [v863,v765,v760,v864,v782,v758] .nil .nil) .nil)) (.node [v1170,v762,v765,v760,v782,v758] (.node [v1171,v762,v765,v760,v782,v758] (.node [v1172,v762,v765,v760,v782,v758] .nil .nil) .nil) (.node [v866,v870,v762,v765,v760,v782] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5lllrl : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5lllrl = true := by decide +kernel
def tree_eaa8c880_5lllrr : BinaryTree (List W) := (.node [v1173,v762,v765,v757,v782,v758] (.node [v866,v762,v765,v760,v782,v758] (.node [v866,v762,v765,v867,v760,v782] (.node [v866,v762,v805,v760,v782,v758] (.node [v866,v762,v774,v765,v782,v758] .nil .nil) .nil) (.node [v866,v762,v765,v760,v785,v782] (.node [v866,v762,v765,v757,v782,v758] .nil .nil) .nil)) (.node [v866,v762,v867,v760,v782,v758] (.node [v866,v762,v867,v760,v782] (.node [v866,v762,v765,v760,v782,v814] .nil .nil) .nil) (.node [v866,v819,v765,v760,v782,v758] .nil .nil))) (.node [v872,v762,v765,v891,v782,v758] (.node [v872,v762,v963,v765,v760,v782] (.node [v872,v762,v774,v765,v782,v758] (.node [v1173,v762,v765,v760,v782,v758] .nil .nil) .nil) (.node [v872,v762,v765,v985,v782,v758] (.node [v872,v762,v963,v765,v782,v758] .nil .nil) .nil)) (.node [v872,v762,v765,v760,v782,v758] (.node [v872,v762,v765,v798,v782,v758] (.node [v872,v762,v765,v757,v782,v758] .nil .nil) .nil) (.node [v872,v762,v765,v760,v782,v898] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5lllrr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5lllrr = true := by decide +kernel
def tree_eaa8c880_5lllr : BinaryTree (List W) := .node [v866,v783,v765,v760,v782,v758] tree_eaa8c880_5lllrl tree_eaa8c880_5lllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5lllr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5lllr = true := by
  change (_ && everyKey _ tree_eaa8c880_5lllrl && everyKey _ tree_eaa8c880_5lllrr) = true
  rw [ok_tree_eaa8c880_5lllrl, ok_tree_eaa8c880_5lllrr]
  decide +kernel
def tree_eaa8c880_5lll : BinaryTree (List W) := .node [v860,v762,v765,v760,v782,v758] tree_eaa8c880_5llll tree_eaa8c880_5lllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5lll : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5lll = true := by
  change (_ && everyKey _ tree_eaa8c880_5llll && everyKey _ tree_eaa8c880_5lllr) = true
  rw [ok_tree_eaa8c880_5llll, ok_tree_eaa8c880_5lllr]
  decide +kernel
def tree_eaa8c880_5llrll : BinaryTree (List W) := (.node [v870,v762,v765,v760,v782,v929] (.node [v870,v775,v762,v765,v760,v782] (.node [v870,v871,v762,v765,v760] (.node [v1174,v762,v765,v760,v782,v758] (.node [v872,v762,v765,v782,v758,v976] .nil .nil) .nil) (.node [v870,v871,v762,v765,v760,v758] (.node [v870,v871,v762,v765,v760,v782] .nil .nil) .nil)) (.node [v870,v762,v765,v757,v782,v758] (.node [v870,v762,v805,v765,v760,v782] (.node [v870,v762,v774,v765,v782,v758] .nil .nil) .nil) (.node [v870,v762,v765,v760,v782,v758] (.node [v870,v762,v765,v760,v785,v758] .nil .nil) .nil))) (.node [v874,v762,v765,v760,v782,v841] (.node [v1175,v762,v765,v760,v782,v758] (.node [v875,v762,v765,v760,v782,v758] (.node [v1176,v762,v765,v760,v782,v758] .nil .nil) .nil) (.node [v874,v762,v765,v760,v782,v758] (.node [v874,v762,v765,v760,v782] .nil .nil) .nil)) (.node [v778,v762,v765,v760,v782,v842] (.node [v778,v762,v765,v760,v782,v758] (.node [v778,v762,v765,v760,v782] .nil .nil) .nil) (.node [v882,v762,v765,v760,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5llrll : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5llrll = true := by decide +kernel
def tree_eaa8c880_5llrlr : BinaryTree (List W) := (.node [v776,v765,v760,v864,v782,v758] (.node [v776,v762,v765,v760,v887,v758] (.node [v776,v762,v774,v765,v782,v758] (.node [v776,v787,v765,v760,v782,v758] (.node [v776,v775,v765,v760,v782,v758] .nil .nil) .nil) (.node [v776,v762,v765,v757,v782,v758] (.node [v776,v762,v826,v760,v782,v758] .nil .nil) .nil)) (.node [v776,v762,v768,v760,v782,v758] (.node [v776,v762,v765,v760,v758,v842] (.node [v776,v762,v765,v760,v782,v758] .nil .nil) .nil) (.node [v776,v852,v765,v760,v782,v758] .nil .nil))) (.node [v1177,v762,v765,v760,v782,v758] (.node [v884,v762,v765,v760,v782,v758] (.node [v776,v765,v760,v758,v842] (.node [v776,v765,v760,v782,v758,v842] .nil .nil) .nil) (.node [v1178,v762,v765,v760,v782,v758] (.node [v1179,v762,v765,v760,v782,v758] .nil .nil) .nil)) (.node [v1180,v871,v762,v765,v760,v758] (.node [v1181,v762,v765,v760,v782,v758] (.node [v1182,v762,v765,v760,v782,v758] .nil .nil) .nil) (.node [v1180,v762,v774,v765,v760,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5llrlr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5llrlr = true := by decide +kernel
def tree_eaa8c880_5llrl : BinaryTree (List W) := .node [v776,v886,v765,v760,v782,v758] tree_eaa8c880_5llrll tree_eaa8c880_5llrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5llrl : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5llrl = true := by
  change (_ && everyKey _ tree_eaa8c880_5llrll && everyKey _ tree_eaa8c880_5llrlr) = true
  rw [ok_tree_eaa8c880_5llrll, ok_tree_eaa8c880_5llrlr]
  decide +kernel
def tree_eaa8c880_5llrrl : BinaryTree (List W) := (.node [v885,v762,v765,v757,v782,v758] (.node [v1183,v762,v765,v760,v782,v758] (.node [v1180,v762,v765,v760,v782,v758] (.node [v1180,v762,v765,v760,v785,v758] (.node [v1180,v762,v765,v757,v782,v758] .nil .nil) .nil) (.node [v1184,v762,v765,v760,v782,v758] (.node [v1180,v762,v765,v760,v962,v758] .nil .nil) .nil)) (.node [v885,v762,v774,v765,v782,v758] (.node [v885,v775,v765,v760,v782,v758] (.node [v885,v888,v765,v760,v782,v758] .nil .nil) .nil) (.node [v885,v762,v765,v891,v782,v758] .nil .nil))) (.node [v1185,v762,v765,v760,v782,v758] (.node [v885,v765,v760,v890,v782,v758] (.node [v885,v762,v765,v890,v782,v758] (.node [v885,v762,v765,v760,v782,v758] .nil .nil) .nil) (.node [v885,v765,v890,v782,v758] (.node [v885,v765,v760,v864,v782,v758] .nil .nil) .nil)) (.node [v1186,v762,v765,v760,v782,v758] (.node [v1187,v762,v765,v760,v782,v758] (.node [v1188,v762,v765,v760,v782,v758] .nil .nil) .nil) (.node [v1189,v762,v765,v760,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5llrrl : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5llrrl = true := by decide +kernel
def tree_eaa8c880_5llrrr : BinaryTree (List W) := (.node [v888,v765,v891,v760,v782,v758] (.node [v888,v762,v774,v765,v782,v758] (.node [v1190,v762,v765,v760,v782,v758] (.node [v889,v762,v765,v760,v782,v758] (.node [v1191,v762,v765,v760,v782,v758] .nil .nil) .nil) (.node [v1192,v762,v765,v760,v782,v758] (.node [v1193,v762,v765,v760,v782,v758] .nil .nil) .nil)) (.node [v888,v762,v765,v760,v782,v758] (.node [v888,v762,v765,v757,v782,v758] (.node [v888,v762,v765,v891,v782,v758] .nil .nil) .nil) (.node [v888,v762,v765,v890,v782,v758] .nil .nil))) (.node [v892,v762,v765,v760,v782,v758] (.node [v1194,v762,v765,v760,v782,v758] (.node [v1195,v762,v765,v760,v782,v758] (.node [v888,v765,v891,v782,v758] .nil .nil) .nil) (.node [v1196,v762,v765,v760,v782,v758] (.node [v1197,v762,v765,v760,v782,v758] .nil .nil) .nil)) (.node [v886,v762,v765,v848,v782,v758] (.node [v886,v762,v765,v757,v782,v758] (.node [v886,v762,v774,v765,v782,v758] .nil .nil) .nil) (.node [v886,v762,v765,v760,v887,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5llrrr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5llrrr = true := by decide +kernel
def tree_eaa8c880_5llrr : BinaryTree (List W) := .node [v1198,v762,v765,v760,v782,v758] tree_eaa8c880_5llrrl tree_eaa8c880_5llrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5llrr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5llrr = true := by
  change (_ && everyKey _ tree_eaa8c880_5llrrl && everyKey _ tree_eaa8c880_5llrrr) = true
  rw [ok_tree_eaa8c880_5llrrl, ok_tree_eaa8c880_5llrrr]
  decide +kernel
def tree_eaa8c880_5llr : BinaryTree (List W) := .node [v1180,v762,v774,v765,v782,v758] tree_eaa8c880_5llrl tree_eaa8c880_5llrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5llr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5llr = true := by
  change (_ && everyKey _ tree_eaa8c880_5llrl && everyKey _ tree_eaa8c880_5llrr) = true
  rw [ok_tree_eaa8c880_5llrl, ok_tree_eaa8c880_5llrr]
  decide +kernel
def tree_eaa8c880_5ll : BinaryTree (List W) := .node [v872,v762,v765,v890,v782,v758] tree_eaa8c880_5lll tree_eaa8c880_5llr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5ll : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5ll = true := by
  change (_ && everyKey _ tree_eaa8c880_5lll && everyKey _ tree_eaa8c880_5llr) = true
  rw [ok_tree_eaa8c880_5lll, ok_tree_eaa8c880_5llr]
  decide +kernel
def tree_eaa8c880_5lrlll : BinaryTree (List W) := (.node [v871,v762,v765,v789,v782,v758] (.node [v1199,v762,v765,v760,v782,v758] (.node [v886,v765,v772,v760,v782,v758] (.node [v886,v762,v765,v832,v782,v758] (.node [v886,v762,v765,v760,v758,v842] .nil .nil) .nil) (.node [v886,v765,v760,v887,v758] (.node [v886,v765,v760,v887,v782,v758] .nil .nil) .nil)) (.node [v871,v762,v765,v757,v760,v758] (.node [v871,v762,v774,v765,v782,v758] (.node [v1200,v762,v765,v760,v782,v758] .nil .nil) .nil) (.node [v871,v762,v765,v757,v758] (.node [v871,v762,v765,v757,v782,v758] .nil .nil) .nil))) (.node [v897,v762,v765,v760,v758] (.node [v871,v762,v765,v760,v758,v929] (.node [v871,v762,v765,v760,v782,v758] (.node [v871,v762,v765,v760,v785,v782] .nil .nil) .nil) (.node [v897,v762,v765,v760,v782,v758] (.node [v871,v762,v765,v788,v782,v758] .nil .nil) .nil)) (.node [v895,v762,v852,v760,v782,v758] (.node [v895,v762,v774,v765,v782,v758] (.node [v897,v762,v765,v760,v758,v898] .nil .nil) .nil) (.node [v895,v762,v796,v760,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5lrlll : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5lrlll = true := by decide +kernel
def tree_eaa8c880_5lrllr : BinaryTree (List W) := (.node [v904,v762,v765,v760,v782,v758] (.node [v895,v762,v772,v760,v782,v758] (.node [v895,v762,v765,v760,v782,v758] (.node [v895,v762,v765,v816,v782,v758] (.node [v895,v762,v765,v757,v782,v758] .nil .nil) .nil) (.node [v895,v762,v765,v900,v782,v758] (.node [v895,v762,v765,v760,v758,v841] .nil .nil) .nil)) (.node [v903,v762,v765,v760,v782,v758] (.node [v895,v762,v896,v760,v758] (.node [v895,v762,v896,v760,v782,v758] .nil .nil) .nil) (.node [v902,v762,v765,v760,v782,v758] .nil .nil))) (.node [v909,v762,v765,v757,v782,v758] (.node [v905,v762,v765,v760,v782,v758] (.node [v907,v762,v765,v760,v782,v758] (.node [v923,v762,v765,v760,v782,v758] .nil .nil) .nil) (.node [v905,v765,v760,v782,v758] (.node [v905,v796,v765,v760,v782,v758] .nil .nil) .nil)) (.node [v775,v762,v765,v831,v782,v758] (.node [v775,v762,v774,v765,v782,v758] (.node [v909,v762,v765,v760,v782,v758] .nil .nil) .nil) (.node [v775,v762,v765,v757,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5lrllr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5lrllr = true := by decide +kernel
def tree_eaa8c880_5lrll : BinaryTree (List W) := .node [v895,v762,v765,v896,v760,v758] tree_eaa8c880_5lrlll tree_eaa8c880_5lrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5lrll : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5lrll = true := by
  change (_ && everyKey _ tree_eaa8c880_5lrlll && everyKey _ tree_eaa8c880_5lrllr) = true
  rw [ok_tree_eaa8c880_5lrlll, ok_tree_eaa8c880_5lrllr]
  decide +kernel
def tree_eaa8c880_5lrlrl : BinaryTree (List W) := (.node [v1201,v762,v765,v760,v782,v758] (.node [v775,v765,v891,v760,v782,v758] (.node [v775,v762,v765,v760,v782,v837] (.node [v775,v762,v765,v760,v782,v758] (.node [v775,v762,v765,v760,v785,v782] .nil .nil) .nil) (.node [v775,v765,v772,v760,v782,v758] (.node [v775,v762,v765,v840,v782,v758] .nil .nil) .nil)) (.node [v775,v765,v760,v782,v837] (.node [v775,v765,v760,v782,v758,v837] (.node [v775,v765,v760,v887,v782,v758] .nil .nil) .nil) (.node [v1202,v762,v765,v760,v782,v758] (.node [v917,v762,v765,v760,v782,v758] .nil .nil) .nil))) (.node [v787,v762,v774,v765,v782,v758] (.node [v1203,v762,v765,v760,v782,v758] (.node [v783,v765,v760,v782,v758] (.node [v783,v762,v765,v760,v782,v758] .nil .nil) .nil) (.node [v921,v762,v765,v760,v782,v758] (.node [v921,v762,v774,v765,v782,v758] .nil .nil) .nil)) (.node [v787,v762,v765,v757,v782,v758] (.node [v787,v762,v796,v760,v782,v758] (.node [v787,v762,v852,v760,v782,v758] .nil .nil) .nil) (.node [v787,v762,v765,v760,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5lrlrl : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5lrlrl = true := by decide +kernel
def tree_eaa8c880_5lrlrr : BinaryTree (List W) := (.node [v1204,v762,v765,v760,v782,v758] (.node [v1205,v762,v765,v760,v782,v758] (.node [v787,v765,v760,v887,v782,v758] (.node [v787,v765,v772,v760,v782,v758] (.node [v787,v762,v896,v760,v782,v758] .nil .nil) .nil) (.node [v1206,v762,v765,v760,v782,v758] (.node [v787,v772,v760,v782,v758] .nil .nil) .nil)) (.node [v1207,v762,v765,v760,v782,v758] (.node [v1208,v762,v765,v760,v782,v758] (.node [v925,v762,v765,v760,v782,v758] .nil .nil) .nil) (.node [v928,v762,v765,v760,v782,v758] .nil .nil))) (.node [v797,v765,v760,v782,v758] (.node [v786,v765,v760,v782,v758] (.node [v786,v762,v765,v760,v782,v758] (.node [v1209,v762,v765,v760,v782,v758] .nil .nil) .nil) (.node [v797,v762,v765,v760,v782,v758] (.node [v786,v765,v760,v782,v758,v929] .nil .nil) .nil)) (.node [v801,v765,v760,v782,v758] (.node [v801,v762,v765,v760,v782,v758] (.node [v797,v765,v760,v782,v758,v898] .nil .nil) .nil) (.node [v801,v765,v760,v782,v758,v841] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5lrlrr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5lrlrr = true := by decide +kernel
def tree_eaa8c880_5lrlr : BinaryTree (List W) := .node [v787,v762,v772,v760,v782,v758] tree_eaa8c880_5lrlrl tree_eaa8c880_5lrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5lrlr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5lrlr = true := by
  change (_ && everyKey _ tree_eaa8c880_5lrlrl && everyKey _ tree_eaa8c880_5lrlrr) = true
  rw [ok_tree_eaa8c880_5lrlrl, ok_tree_eaa8c880_5lrlrr]
  decide +kernel
def tree_eaa8c880_5lrl : BinaryTree (List W) := .node [v775,v762,v765,v760,v864,v782] tree_eaa8c880_5lrll tree_eaa8c880_5lrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5lrl : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5lrl = true := by
  change (_ && everyKey _ tree_eaa8c880_5lrll && everyKey _ tree_eaa8c880_5lrlr) = true
  rw [ok_tree_eaa8c880_5lrll, ok_tree_eaa8c880_5lrlr]
  decide +kernel
def tree_eaa8c880_5lrrll : BinaryTree (List W) := (.node [v762,v1210,v765,v760,v782,v758] (.node [v762,v865,v765,v760,v782,v758] (.node [v762,v1211,v765,v760,v782,v758] (.node [v762,v1212,v765,v760,v782,v758] (.node [v762,v1213,v765,v760,v782,v758] .nil .nil) .nil) (.node [v762,v819,v765,v760,v782,v758] (.node [v762,v1214,v765,v760,v782,v758] .nil .nil) .nil)) (.node [v762,v922,v765,v760,v782,v758] (.node [v762,v922,v774,v765,v782,v758] (.node [v762,v1215,v765,v760,v782,v758] .nil .nil) .nil) (.node [v762,v1210,v774,v765,v782,v758] (.node [v762,v1216,v765,v760,v782,v758] .nil .nil) .nil))) (.node [v762,v774,v861,v765,v782,v758] (.node [v762,v774,v774,v765,v782,v758] (.node [v762,v943,v765,v760,v782,v758] (.node [v762,v943,v774,v765,v782,v758] .nil .nil) .nil) (.node [v762,v774,v963,v765,v782,v758] (.node [v762,v774,v1217,v765,v782,v758] .nil .nil) .nil)) (.node [v762,v774,v852,v765,v782,v758] (.node [v762,v774,v858,v765,v782,v758] (.node [v762,v774,v974,v765,v782,v758] .nil .nil) .nil) (.node [v762,v774,v796,v765,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5lrrll : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5lrrll = true := by decide +kernel
def tree_eaa8c880_5lrrlr : BinaryTree (List W) := (.node [v762,v774,v765,v760,v782,v758] (.node [v762,v774,v765,v891,v782,v758] (.node [v762,v774,v765,v985,v782,v758] (.node [v762,v774,v765,v772,v782,v758] (.node [v762,v774,v765,v1218,v782,v758] .nil .nil) .nil) (.node [v762,v774,v765,v896,v782,v758] (.node [v762,v774,v765,v867,v782,v758] .nil .nil) .nil)) (.node [v762,v774,v765,v757,v758] (.node [v762,v774,v765,v757,v782,v758] (.node [v762,v774,v765,v757,v760,v758] .nil .nil) .nil) (.node [v762,v774,v765,v798,v782,v758] .nil .nil))) (.node [v762,v774,v765,v782,v782,v758] (.node [v762,v774,v765,v864,v782,v758] (.node [v762,v774,v765,v890,v782,v758] (.node [v762,v774,v765,v808,v782,v758] .nil .nil) .nil) (.node [v762,v774,v765,v785,v782,v758] (.node [v762,v774,v765,v887,v782,v758] .nil .nil) .nil)) (.node [v762,v774,v765,v782,v758,v1219] (.node [v762,v774,v765,v782,v758] (.node [v762,v774,v765,v782,v962,v758] .nil .nil) .nil) (.node [v762,v774,v765,v782,v758,v976] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5lrrlr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5lrrlr = true := by decide +kernel
def tree_eaa8c880_5lrrl : BinaryTree (List W) := .node [v762,v774,v805,v765,v782,v758] tree_eaa8c880_5lrrll tree_eaa8c880_5lrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5lrrl : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5lrrl = true := by
  change (_ && everyKey _ tree_eaa8c880_5lrrll && everyKey _ tree_eaa8c880_5lrrlr) = true
  rw [ok_tree_eaa8c880_5lrrll, ok_tree_eaa8c880_5lrrlr]
  decide +kernel
def tree_eaa8c880_5lrrrl : BinaryTree (List W) := (.node [v762,v1217,v765,v757,v782,v758] (.node [v762,v957,v765,v760,v782,v758] (.node [v762,v774,v765,v782,v758,v898] (.node [v762,v774,v765,v782,v758,v842] (.node [v762,v774,v765,v782,v758,v814] .nil .nil) .nil) (.node [v762,v774,v765,v782,v758,v841] (.node [v762,v774,v765,v782,v758,v929] .nil .nil) .nil)) (.node [v762,v1217,v974,v760,v782,v758] (.node [v762,v1220,v765,v760,v782,v758] (.node [v762,v960,v765,v760,v782,v758] .nil .nil) .nil) (.node [v762,v1217,v765,v985,v782,v758] .nil .nil))) (.node [v762,v963,v765,v760,v782,v758] (.node [v762,v1217,v985,v760,v782,v758] (.node [v762,v1217,v765,v782,v758,v976] (.node [v762,v1217,v765,v760,v782,v758] .nil .nil) .nil) (.node [v762,v963,v765,v798,v760,v782] (.node [v762,v963,v765,v757,v782,v758] .nil .nil) .nil)) (.node [v762,v822,v765,v760,v782,v758] (.node [v762,v1221,v765,v760,v782,v758] (.node [v762,v963,v765,v782,v758,v898] .nil .nil) .nil) (.node [v762,v822,v765,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5lrrrl : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5lrrrl = true := by decide +kernel
def tree_eaa8c880_5lrrrr : BinaryTree (List W) := (.node [v762,v1222,v765,v760,v782,v758] (.node [v762,v879,v765,v782,v758] (.node [v762,v791,v765,v782,v758] (.node [v762,v791,v765,v760,v782,v758] (.node [v762,v1223,v765,v760,v782,v758] .nil .nil) .nil) (.node [v762,v879,v765,v760,v782,v758] (.node [v762,v791,v765,v782,v758,v929] .nil .nil) .nil)) (.node [v762,v1224,v765,v760,v782,v758] (.node [v762,v1225,v765,v760,v782,v758] (.node [v762,v879,v765,v782,v758,v841] .nil .nil) .nil) (.node [v762,v1222,v765,v757,v782,v758] .nil .nil))) (.node [v762,v861,v765,v760,v782,v758] (.node [v762,v1226,v765,v760,v782,v758] (.node [v762,v968,v765,v760,v782,v758] (.node [v762,v968,v765,v757,v782,v758] .nil .nil) .nil) (.node [v762,v1227,v765,v760,v782,v758] (.node [v762,v1228,v765,v760,v782,v758] .nil .nil) .nil)) (.node [v762,v994,v765,v757,v782,v758] (.node [v762,v1229,v765,v760,v782,v758] (.node [v762,v1230,v765,v760,v782,v758] .nil .nil) .nil) (.node [v762,v994,v765,v760,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5lrrrr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5lrrrr = true := by decide +kernel
def tree_eaa8c880_5lrrr : BinaryTree (List W) := .node [v762,v822,v765,v782,v758,v842] tree_eaa8c880_5lrrrl tree_eaa8c880_5lrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5lrrr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5lrrr = true := by
  change (_ && everyKey _ tree_eaa8c880_5lrrrl && everyKey _ tree_eaa8c880_5lrrrr) = true
  rw [ok_tree_eaa8c880_5lrrrl, ok_tree_eaa8c880_5lrrrr]
  decide +kernel
def tree_eaa8c880_5lrr : BinaryTree (List W) := .node [v762,v774,v765,v782,v758,v837] tree_eaa8c880_5lrrl tree_eaa8c880_5lrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5lrr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5lrr = true := by
  change (_ && everyKey _ tree_eaa8c880_5lrrl && everyKey _ tree_eaa8c880_5lrrr) = true
  rw [ok_tree_eaa8c880_5lrrl, ok_tree_eaa8c880_5lrrr]
  decide +kernel
def tree_eaa8c880_5lr : BinaryTree (List W) := .node [v762,v762,v765,v760,v782,v758] tree_eaa8c880_5lrl tree_eaa8c880_5lrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5lr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5lr = true := by
  change (_ && everyKey _ tree_eaa8c880_5lrl && everyKey _ tree_eaa8c880_5lrr) = true
  rw [ok_tree_eaa8c880_5lrl, ok_tree_eaa8c880_5lrr]
  decide +kernel
def tree_eaa8c880_5l : BinaryTree (List W) := .node [v886,v762,v765,v760,v782,v758] tree_eaa8c880_5ll tree_eaa8c880_5lr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5l : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5l = true := by
  change (_ && everyKey _ tree_eaa8c880_5ll && everyKey _ tree_eaa8c880_5lr) = true
  rw [ok_tree_eaa8c880_5ll, ok_tree_eaa8c880_5lr]
  decide +kernel
def tree_eaa8c880_5rllll : BinaryTree (List W) := (.node [v762,v1231,v765,v760,v782,v758] (.node [v762,v974,v867,v760,v782,v758] (.node [v762,v974,v765,v757,v782,v758] (.node [v762,v974,v765,v985,v782,v758] (.node [v762,v974,v805,v760,v782,v758] .nil .nil) .nil) (.node [v762,v974,v765,v782,v758,v976] (.node [v762,v974,v765,v760,v782,v758] .nil .nil) .nil)) (.node [v762,v1232,v765,v760,v782,v758] (.node [v762,v974,v782,v758,v976] (.node [v762,v974,v760,v782,v758,v976] .nil .nil) .nil) (.node [v762,v1233,v765,v760,v782,v758] (.node [v762,v1234,v765,v760,v782,v758] .nil .nil) .nil))) (.node [v762,v1235,v765,v760,v782,v758] (.node [v762,v1236,v765,v760,v782,v758] (.node [v762,v1237,v765,v760,v782,v758] (.node [v762,v858,v765,v760,v782,v758] .nil .nil) .nil) (.node [v762,v1238,v765,v760,v782,v758] (.node [v762,v1239,v765,v760,v782,v758] .nil .nil) .nil)) (.node [v762,v852,v765,v760,v782,v758] (.node [v762,v852,v765,v757,v782,v758] (.node [v762,v852,v805,v760,v782,v758] .nil .nil) .nil) (.node [v762,v852,v867,v760,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rllll : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rllll = true := by decide +kernel
def tree_eaa8c880_5rlllr : BinaryTree (List W) := (.node [v762,v1240,v765,v760,v782,v758] (.node [v762,v796,v765,v760,v758,v841] (.node [v762,v796,v765,v896,v760,v758] (.node [v762,v796,v805,v760,v782,v758] (.node [v762,v859,v765,v760,v782,v758] .nil .nil) .nil) (.node [v762,v796,v765,v760,v782,v758] (.node [v762,v796,v765,v757,v782,v758] .nil .nil) .nil)) (.node [v762,v1241,v765,v760,v782,v758] (.node [v762,v796,v760,v782,v758,v841] (.node [v762,v796,v867,v760,v782,v758] .nil .nil) .nil) (.node [v762,v851,v765,v760,v782,v758] .nil .nil))) (.node [v762,v1242,v765,v760,v782,v758] (.node [v762,v1243,v765,v760,v782,v758] (.node [v762,v759,v765,v760,v782,v758] (.node [v762,v979,v765,v760,v782,v758] .nil .nil) .nil) (.node [v762,v1244,v765,v760,v782,v758] (.node [v762,v1245,v765,v760,v782,v758] .nil .nil) .nil)) (.node [v762,v805,v765,v757,v782,v758] (.node [v762,v805,v765,v810,v782,v758] (.node [v762,v805,v765,v867,v760,v782] .nil .nil) .nil) (.node [v762,v805,v765,v760,v785,v782] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rlllr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rlllr = true := by decide +kernel
def tree_eaa8c880_5rlll : BinaryTree (List W) := .node [v762,v852,v760,v782,v758,v841] tree_eaa8c880_5rllll tree_eaa8c880_5rlllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rlll : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rlll = true := by
  change (_ && everyKey _ tree_eaa8c880_5rllll && everyKey _ tree_eaa8c880_5rlllr) = true
  rw [ok_tree_eaa8c880_5rllll, ok_tree_eaa8c880_5rlllr]
  decide +kernel
def tree_eaa8c880_5rllrl : BinaryTree (List W) := (.node [v762,v826,v760,v782,v758] (.node [v762,v805,v760,v782,v758,v814] (.node [v762,v805,v772,v760,v782,v758] (.node [v762,v805,v765,v782,v758,v849] (.node [v762,v805,v765,v760,v782,v814] .nil .nil) .nil) (.node [v762,v805,v896,v760,v782,v758] (.node [v762,v805,v985,v760,v782,v758] .nil .nil) .nil)) (.node [v762,v1246,v765,v760,v782,v758] (.node [v762,v1247,v765,v760,v782,v758] (.node [v762,v805,v760,v782,v814] .nil .nil) .nil) (.node [v762,v826,v765,v760,v782,v758] (.node [v762,v984,v765,v760,v782,v758] .nil .nil) .nil))) (.node [v762,v777,v765,v760,v782,v758] (.node [v762,v873,v765,v760,v782,v758] (.node [v762,v803,v760,v782,v758] (.node [v762,v803,v765,v760,v782,v758] .nil .nil) .nil) (.node [v762,v1248,v765,v760,v782,v758] (.node [v762,v1249,v765,v760,v782,v758] .nil .nil) .nil)) (.node [v762,v800,v765,v760,v782,v758] (.node [v762,v777,v760,v782,v758,v842] (.node [v762,v777,v760,v782,v758] .nil .nil) .nil) (.node [v762,v800,v760,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rllrl : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rllrl = true := by decide +kernel
def tree_eaa8c880_5rllrr : BinaryTree (List W) := (.node [v762,v765,v1250,v760,v782,v758] (.node [v762,v765,v1251,v760,v782,v758] (.node [v762,v790,v760,v782,v758,v929] (.node [v762,v790,v760,v782,v758] (.node [v762,v790,v765,v760,v782,v758] .nil .nil) .nil) (.node [v762,v765,v1252,v760,v782,v758] (.node [v762,v765,v765,v760,v782,v758] .nil .nil) .nil)) (.node [v762,v765,v1253,v760,v782,v758] (.node [v762,v765,v839,v760,v782,v758] (.node [v762,v765,v1254,v760,v782,v758] .nil .nil) .nil) (.node [v762,v765,v869,v760,v782,v758] .nil .nil))) (.node [v762,v765,v770,v760,v782,v758] (.node [v762,v765,v1218,v760,v782,v758] (.node [v762,v765,v1255,v760,v782,v758] (.node [v762,v765,v1256,v760,v782,v758] .nil .nil) .nil) (.node [v762,v765,v1257,v760,v782,v758] (.node [v762,v765,v1258,v760,v782,v758] .nil .nil) .nil)) (.node [v762,v765,v772,v760,v782,v758] (.node [v762,v765,v772,v757,v782,v758] (.node [v762,v765,v768,v760,v782,v758] .nil .nil) .nil) (.node [v762,v765,v1259,v760,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rllrr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rllrr = true := by decide +kernel
def tree_eaa8c880_5rllr : BinaryTree (List W) := .node [v762,v800,v760,v782,v758,v898] tree_eaa8c880_5rllrl tree_eaa8c880_5rllrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rllr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rllr = true := by
  change (_ && everyKey _ tree_eaa8c880_5rllrl && everyKey _ tree_eaa8c880_5rllrr) = true
  rw [ok_tree_eaa8c880_5rllrl, ok_tree_eaa8c880_5rllrr]
  decide +kernel
def tree_eaa8c880_5rll : BinaryTree (List W) := .node [v762,v805,v765,v760,v782,v758] tree_eaa8c880_5rlll tree_eaa8c880_5rllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rll : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rll = true := by
  change (_ && everyKey _ tree_eaa8c880_5rlll && everyKey _ tree_eaa8c880_5rllr) = true
  rw [ok_tree_eaa8c880_5rlll, ok_tree_eaa8c880_5rllr]
  decide +kernel
def tree_eaa8c880_5rlrll : BinaryTree (List W) := (.node [v762,v765,v896,v757,v782,v758] (.node [v762,v765,v985,v760,v782,v758] (.node [v762,v765,v1260,v757,v782,v758] (.node [v762,v765,v1261,v760,v782,v758] (.node [v762,v765,v926,v760,v782,v758] .nil .nil) .nil) (.node [v762,v765,v985,v757,v782,v758] (.node [v762,v765,v1260,v760,v782,v758] .nil .nil) .nil)) (.node [v762,v765,v867,v757,v782,v758] (.node [v762,v765,v1262,v760,v782,v758] (.node [v762,v765,v985,v782,v758,v898] .nil .nil) .nil) (.node [v762,v765,v1263,v760,v782,v758] (.node [v762,v765,v867,v760,v782,v758] .nil .nil) .nil))) (.node [v762,v765,v847,v760,v782,v758] (.node [v762,v765,v1264,v760,v782,v758] (.node [v762,v765,v1265,v760,v782,v758] (.node [v762,v765,v896,v760,v782,v758] .nil .nil) .nil) (.node [v762,v765,v795,v760,v782,v758] (.node [v762,v765,v899,v760,v782,v758] .nil .nil) .nil)) (.node [v762,v765,v901,v760,v782,v758] (.node [v762,v765,v810,v782,v758] (.node [v762,v765,v810,v760,v782,v758] .nil .nil) .nil) (.node [v762,v765,v1266,v760,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rlrll : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rlrll = true := by decide +kernel
def tree_eaa8c880_5rlrlr : BinaryTree (List W) := (.node [v762,v765,v1014,v760,v782,v758] (.node [v762,v765,v862,v760,v782,v758] (.node [v762,v765,v1267,v760,v782,v758] (.node [v762,v765,v1268,v760,v782,v758] (.node [v762,v765,v1269,v760,v782,v758] .nil .nil) .nil) (.node [v762,v765,v1270,v760,v782,v758] (.node [v762,v765,v1271,v760,v782,v758] .nil .nil) .nil)) (.node [v762,v765,v1272,v760,v782,v758] (.node [v762,v765,v1273,v760,v782,v758] (.node [v762,v765,v1011,v760,v782,v758] .nil .nil) .nil) (.node [v762,v765,v1014,v757,v782,v758] .nil .nil))) (.node [v762,v765,v1274,v760,v782,v758] (.node [v762,v765,v891,v757,v782,v758] (.node [v762,v765,v910,v760,v782,v758] (.node [v762,v765,v910,v757,v782,v758] .nil .nil) .nil) (.node [v762,v765,v891,v782,v758,v898] (.node [v762,v765,v891,v760,v782,v758] .nil .nil) .nil)) (.node [v762,v765,v757,v757,v782,v758] (.node [v762,v765,v831,v782,v758] (.node [v762,v765,v831,v760,v782,v758] .nil .nil) .nil) (.node [v762,v765,v757,v798,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rlrlr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rlrlr = true := by decide +kernel
def tree_eaa8c880_5rlrl : BinaryTree (List W) := .node [v762,v765,v1275,v760,v782,v758] tree_eaa8c880_5rlrll tree_eaa8c880_5rlrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rlrl : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rlrl = true := by
  change (_ && everyKey _ tree_eaa8c880_5rlrll && everyKey _ tree_eaa8c880_5rlrlr) = true
  rw [ok_tree_eaa8c880_5rlrll, ok_tree_eaa8c880_5rlrlr]
  decide +kernel
def tree_eaa8c880_5rlrrl : BinaryTree (List W) := (.node [v762,v765,v757,v782,v758] (.node [v762,v765,v757,v887,v782,v758] (.node [v762,v765,v757,v835,v782,v758] (.node [v762,v765,v757,v760,v962,v758] (.node [v762,v765,v757,v760,v782,v758] .nil .nil) .nil) (.node [v762,v765,v757,v864,v782,v758] (.node [v762,v765,v757,v890,v782,v758] .nil .nil) .nil)) (.node [v762,v765,v757,v782,v782,v758] (.node [v762,v765,v757,v785,v758] (.node [v762,v765,v757,v785,v782,v758] .nil .nil) .nil) (.node [v762,v765,v757,v782,v962,v758] .nil .nil))) (.node [v762,v765,v757,v782,v758,v818] (.node [v762,v765,v757,v782,v758,v837] (.node [v762,v765,v757,v782,v758,v976] (.node [v762,v765,v757,v782,v758,v820] .nil .nil) .nil) (.node [v762,v765,v757,v782,v758,v842] (.node [v762,v765,v757,v782,v758,v814] .nil .nil) .nil)) (.node [v762,v765,v757,v782,v758,v841] (.node [v762,v765,v757,v782,v758,v929] (.node [v762,v765,v757,v782,v758,v898] .nil .nil) .nil) (.node [v762,v765,v757,v962,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rlrrl : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rlrrl = true := by decide +kernel
def tree_eaa8c880_5rlrrr : BinaryTree (List W) := (.node [v762,v765,v798,v782,v758,v898] (.node [v762,v765,v848,v782,v758] (.node [v762,v765,v789,v782,v758] (.node [v762,v765,v789,v760,v782,v758] (.node [v762,v765,v816,v782,v758] .nil .nil) .nil) (.node [v762,v765,v848,v760,v782,v758] (.node [v762,v765,v948,v760,v782,v758] .nil .nil) .nil)) (.node [v762,v765,v798,v760,v782,v758] (.node [v762,v765,v949,v760,v782,v758] (.node [v762,v765,v947,v760,v782,v758] .nil .nil) .nil) (.node [v762,v765,v798,v760,v782,v898] .nil .nil))) (.node [v762,v765,v1276,v760,v782,v758] (.node [v762,v765,v1277,v760,v782,v758] (.node [v762,v765,v1278,v760,v782,v758] (.node [v762,v765,v798,v782,v898] .nil .nil) .nil) (.node [v762,v765,v1279,v760,v782,v758] (.node [v762,v765,v1280,v760,v782,v758] .nil .nil) .nil)) (.node [v762,v765,v1281,v760,v782,v758] (.node [v762,v765,v1282,v760,v782,v758] (.node [v762,v765,v1283,v760,v782,v758] .nil .nil) .nil) (.node [v762,v765,v780,v760,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rlrrr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rlrrr = true := by decide +kernel
def tree_eaa8c880_5rlrr : BinaryTree (List W) := .node [v762,v765,v816,v760,v782,v758] tree_eaa8c880_5rlrrl tree_eaa8c880_5rlrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rlrr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rlrr = true := by
  change (_ && everyKey _ tree_eaa8c880_5rlrrl && everyKey _ tree_eaa8c880_5rlrrr) = true
  rw [ok_tree_eaa8c880_5rlrrl, ok_tree_eaa8c880_5rlrrr]
  decide +kernel
def tree_eaa8c880_5rlr : BinaryTree (List W) := .node [v762,v765,v757,v760,v785,v758] tree_eaa8c880_5rlrl tree_eaa8c880_5rlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rlr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rlr = true := by
  change (_ && everyKey _ tree_eaa8c880_5rlrl && everyKey _ tree_eaa8c880_5rlrr) = true
  rw [ok_tree_eaa8c880_5rlrl, ok_tree_eaa8c880_5rlrr]
  decide +kernel
def tree_eaa8c880_5rl : BinaryTree (List W) := .node [v762,v765,v1284,v760,v782,v758] tree_eaa8c880_5rll tree_eaa8c880_5rlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rl : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rl = true := by
  change (_ && everyKey _ tree_eaa8c880_5rll && everyKey _ tree_eaa8c880_5rlr) = true
  rw [ok_tree_eaa8c880_5rll, ok_tree_eaa8c880_5rlr]
  decide +kernel
def tree_eaa8c880_5rrlll : BinaryTree (List W) := (.node [v762,v765,v760,v1285,v782,v758] (.node [v762,v765,v881,v782,v758] (.node [v762,v765,v792,v782,v758] (.node [v762,v765,v792,v760,v782,v758] (.node [v762,v765,v780,v782,v758,v842] .nil .nil) .nil) (.node [v762,v765,v881,v760,v782,v758] (.node [v762,v765,v792,v782,v758,v929] .nil .nil) .nil)) (.node [v762,v765,v760,v1286,v782,v758] (.node [v762,v765,v760,v760,v782,v758] (.node [v762,v765,v881,v782,v758,v841] .nil .nil) .nil) (.node [v762,v765,v760,v1287,v782,v758] (.node [v762,v765,v760,v1288,v782,v758] .nil .nil) .nil))) (.node [v762,v765,v760,v832,v782,v758] (.node [v762,v765,v760,v1289,v782,v758] (.node [v762,v765,v760,v1290,v782,v758] (.node [v762,v765,v760,v1291,v782,v758] .nil .nil) .nil) (.node [v762,v765,v760,v807,v782,v758] (.node [v762,v765,v760,v808,v782,v758] .nil .nil) .nil)) (.node [v762,v765,v760,v1292,v782,v758] (.node [v762,v765,v760,v900,v782,v758] (.node [v762,v765,v760,v788,v782,v758] .nil .nil) .nil) (.node [v762,v765,v760,v1293,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rrlll : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rrlll = true := by decide +kernel
def tree_eaa8c880_5rrllr : BinaryTree (List W) := (.node [v762,v765,v760,v794,v782,v758] (.node [v762,v765,v760,v825,v782,v758] (.node [v762,v765,v760,v1294,v782,v758] (.node [v762,v765,v760,v890,v782,v758] (.node [v762,v765,v760,v840,v782,v758] .nil .nil) .nil) (.node [v762,v765,v760,v887,v782,v758] (.node [v762,v765,v760,v864,v782,v758] .nil .nil) .nil)) (.node [v762,v765,v760,v1295,v782,v758] (.node [v762,v765,v760,v1296,v782,v758] (.node [v762,v765,v760,v1297,v782,v758] .nil .nil) .nil) (.node [v762,v765,v760,v880,v782,v758] .nil .nil))) (.node [v762,v765,v760,v1298,v782,v758] (.node [v762,v765,v760,v785,v782,v929] (.node [v762,v765,v760,v785,v782,v758] (.node [v762,v765,v760,v1143,v782,v758] .nil .nil) .nil) (.node [v762,v765,v760,v785,v929] (.node [v762,v765,v760,v785,v758,v929] .nil .nil) .nil)) (.node [v762,v765,v760,v1020,v782,v758] (.node [v762,v765,v760,v1299,v782,v758] (.node [v762,v765,v760,v1019,v782,v758] .nil .nil) .nil) (.node [v762,v765,v760,v1018,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rrllr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rrllr = true := by decide +kernel
def tree_eaa8c880_5rrll : BinaryTree (List W) := .node [v762,v765,v760,v835,v782,v758] tree_eaa8c880_5rrlll tree_eaa8c880_5rrllr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rrll : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rrll = true := by
  change (_ && everyKey _ tree_eaa8c880_5rrlll && everyKey _ tree_eaa8c880_5rrllr) = true
  rw [ok_tree_eaa8c880_5rrlll, ok_tree_eaa8c880_5rrllr]
  decide +kernel
def tree_eaa8c880_5rrlrl : BinaryTree (List W) := (.node [v762,v765,v760,v782,v1026,v758] (.node [v762,v765,v760,v767,v782,v758] (.node [v762,v765,v760,v951,v782,v758] (.node [v762,v765,v760,v1300,v782,v758] (.node [v762,v765,v760,v1021,v782,v758] .nil .nil) .nil) (.node [v762,v765,v760,v950,v782,v758] (.node [v762,v765,v760,v893,v782,v758] .nil .nil) .nil)) (.node [v762,v765,v760,v799,v758] (.node [v762,v765,v760,v799,v782,v758] (.node [v762,v765,v760,v763,v782,v758] .nil .nil) .nil) (.node [v762,v765,v760,v782,v782,v758] (.node [v762,v765,v760,v799,v758,v898] .nil .nil) .nil))) (.node [v762,v765,v760,v782,v1023,v758] (.node [v762,v765,v760,v782,v1025,v758] (.node [v762,v765,v760,v782,v1116,v758] (.node [v762,v765,v760,v782,v1115,v758] .nil .nil) .nil) (.node [v762,v765,v760,v782,v877,v758] (.node [v762,v765,v760,v782,v876,v758] .nil .nil) .nil)) (.node [v762,v765,v760,v782,v1301,v758] (.node [v762,v765,v760,v782,v1138,v758] (.node [v762,v765,v760,v782,v1139,v758] .nil .nil) .nil) (.node [v762,v765,v760,v782,v1030,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rrlrl : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rrlrl = true := by decide +kernel
def tree_eaa8c880_5rrlrr : BinaryTree (List W) := (.node [v762,v765,v760,v782,v953,v758] (.node [v762,v765,v760,v782,v1031,v758] (.node [v762,v765,v760,v782,v1302,v758] (.node [v762,v765,v760,v782,v1303,v758] (.node [v762,v765,v760,v782,v1304,v758] .nil .nil) .nil) (.node [v762,v765,v760,v782,v1028,v758] (.node [v762,v765,v760,v782,v1029,v758] .nil .nil) .nil)) (.node [v762,v765,v760,v782,v1305,v758] (.node [v762,v765,v760,v782,v962,v758] (.node [v762,v765,v760,v782,v1027,v758] .nil .nil) .nil) (.node [v762,v765,v760,v782,v1306,v758] .nil .nil))) (.node [v762,v765,v760,v782,v769] (.node [v762,v765,v760,v782,v1307,v758] (.node [v762,v765,v760,v782,v1308,v758] (.node [v762,v765,v760,v782,v1309,v758] .nil .nil) .nil) (.node [v762,v765,v760,v782,v811,v758] (.node [v762,v765,v760,v782,v1310,v758] .nil .nil) .nil)) (.node [v762,v765,v760,v782,v771] (.node [v762,v765,v760,v782,v769,v842] (.node [v762,v765,v760,v782,v769,v758] .nil .nil) .nil) (.node [v762,v765,v760,v782,v771,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rrlrr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rrlrr = true := by decide +kernel
def tree_eaa8c880_5rrlr : BinaryTree (List W) := .node [v762,v765,v760,v782,v1134,v758] tree_eaa8c880_5rrlrl tree_eaa8c880_5rrlrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rrlr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rrlr = true := by
  change (_ && everyKey _ tree_eaa8c880_5rrlrl && everyKey _ tree_eaa8c880_5rrlrr) = true
  rw [ok_tree_eaa8c880_5rrlrl, ok_tree_eaa8c880_5rrlrr]
  decide +kernel
def tree_eaa8c880_5rrl : BinaryTree (List W) := .node [v762,v765,v760,v1022,v782,v758] tree_eaa8c880_5rrll tree_eaa8c880_5rrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rrl : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rrl = true := by
  change (_ && everyKey _ tree_eaa8c880_5rrll && everyKey _ tree_eaa8c880_5rrlr) = true
  rw [ok_tree_eaa8c880_5rrll, ok_tree_eaa8c880_5rrlr]
  decide +kernel
def tree_eaa8c880_5rrrll : BinaryTree (List W) := (.node [v762,v765,v760,v782,v758,v1136] (.node [v762,v765,v760,v782,v758,v1311] (.node [v762,v765,v760,v782,v758,v894] (.node [v762,v765,v760,v782,v758,v758] (.node [v762,v765,v760,v782,v758] .nil .nil) .nil) (.node [v762,v765,v760,v782,v758,v1312] (.node [v762,v765,v760,v782,v758,v1313] .nil .nil) .nil)) (.node [v762,v765,v760,v782,v758,v912] (.node [v762,v765,v760,v782,v758,v1314] (.node [v762,v765,v760,v782,v758,v1219] .nil .nil) .nil) (.node [v762,v765,v760,v782,v758,v1113] (.node [v762,v765,v760,v782,v758,v1114] .nil .nil) .nil))) (.node [v762,v765,v760,v782,v758,v1315] (.node [v762,v765,v760,v782,v758,v1316] (.node [v762,v765,v760,v782,v758,v1135] (.node [v762,v765,v760,v782,v758,v980] .nil .nil) .nil) (.node [v762,v765,v760,v782,v758,v1128] (.node [v762,v765,v760,v782,v758,v1317] .nil .nil) .nil)) (.node [v762,v765,v760,v782,v758,v976] (.node [v762,v765,v760,v782,v758,v820] (.node [v762,v765,v760,v782,v758,v849] .nil .nil) .nil) (.node [v762,v765,v760,v782,v758,v1318] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rrrll : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rrrll = true := by decide +kernel
def tree_eaa8c880_5rrrlr : BinaryTree (List W) := (.node [v762,v765,v760,v782,v758,v818] (.node [v762,v765,v760,v782,v758,v982] (.node [v762,v765,v760,v782,v758,v837] (.node [v762,v765,v760,v782,v758,v913] (.node [v762,v765,v760,v782,v758,v914] .nil .nil) .nil) (.node [v762,v765,v760,v782,v758,v983] (.node [v762,v765,v760,v782,v758,v993] .nil .nil) .nil)) (.node [v762,v765,v760,v782,v758,v827] (.node [v762,v765,v760,v782,v758,v843] (.node [v762,v765,v760,v782,v758,v814] .nil .nil) .nil) (.node [v762,v765,v760,v782,v758,v842] .nil .nil))) (.node [v762,v765,v760,v782,v758,v929] (.node [v762,v765,v760,v782,v758,v1319] (.node [v762,v765,v760,v782,v758,v1320] (.node [v762,v765,v760,v782,v758,v898] .nil .nil) .nil) (.node [v762,v765,v760,v782,v758,v1061] (.node [v762,v765,v760,v782,v758,v1321] .nil .nil) .nil)) (.node [v762,v765,v760,v782,v758,v1322] (.node [v762,v765,v760,v782,v758,v841] (.node [v762,v765,v760,v782,v758,v1323] .nil .nil) .nil) (.node [v762,v765,v760,v782,v758,v1324] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rrrlr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rrrlr = true := by decide +kernel
def tree_eaa8c880_5rrrl : BinaryTree (List W) := .node [v762,v765,v760,v782,v758,v911] tree_eaa8c880_5rrrll tree_eaa8c880_5rrrlr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rrrl : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rrrl = true := by
  change (_ && everyKey _ tree_eaa8c880_5rrrll && everyKey _ tree_eaa8c880_5rrrlr) = true
  rw [ok_tree_eaa8c880_5rrrll, ok_tree_eaa8c880_5rrrlr]
  decide +kernel
def tree_eaa8c880_5rrrrl : BinaryTree (List W) := (.node [v762,v839,v760,v782,v758] (.node [v762,v765,v900,v782,v758] (.node [v762,v765,v760,v782,v758,v1325] (.node [v762,v765,v760,v782,v758,v1326] (.node [v762,v765,v760,v782,v758,v1327] .nil .nil) .nil) (.node [v762,v765,v788,v782,v758] (.node [v762,v765,v832,v782,v758] .nil .nil) .nil)) (.node [v762,v765,v782,v758,v849] (.node [v762,v765,v890,v782,v758,v898] (.node [v762,v765,v840,v782,v758] .nil .nil) .nil) (.node [v762,v765,v782,v758,v976,v898] .nil .nil))) (.node [v762,v867,v896,v760,v782,v758] (.node [v762,v772,v760,v782,v758,v841] (.node [v762,v772,v867,v760,v782,v758] (.node [v762,v768,v760,v782,v758] .nil .nil) .nil) (.node [v762,v985,v760,v782,v758,v976] (.node [v762,v985,v867,v760,v782,v758] .nil .nil) .nil)) (.node [v762,v899,v760,v782,v758] (.node [v762,v896,v760,v782,v758,v841] (.node [v762,v867,v760,v782,v758,v814] .nil .nil) .nil) (.node [v762,v899,v760,v782,v758,v898] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rrrrl : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rrrrl = true := by decide +kernel
def tree_eaa8c880_5rrrrr : BinaryTree (List W) := (.node [v765,v891,v760,v890,v782,v758] (.node [v852,v765,v760,v887,v782,v758] (.node [v762,v847,v760,v782,v758,v842] (.node [v762,v847,v760,v782,v758] (.node [v762,v795,v760,v782,v758,v929] .nil .nil) .nil) (.node [v852,v765,v772,v760,v782,v758] (.node [v819,v765,v760,v782,v758] .nil .nil) .nil)) (.node [v765,v772,v760,v864,v782,v758] (.node [v765,v770,v760,v782,v758] (.node [v796,v765,v770,v760,v782,v758] .nil .nil) .nil) (.node [v765,v772,v760,v782,v758,v842] .nil .nil))) (.node [v765,v760,v825,v782,v758,v898] (.node [v765,v760,v864,v782,v758,v837] (.node [v765,v760,v864,v887,v782,v758] (.node [v765,v891,v760,v864,v782,v758] .nil .nil) .nil) (.node [v765,v760,v825,v782,v758] (.node [v765,v760,v887,v782,v758,v842] .nil .nil) .nil)) (.node [v765,v760,v794,v782,v758] (.node [v765,v760,v880,v782,v758,v841] (.node [v765,v760,v880,v782,v758] .nil .nil) .nil) (.node [v765,v760,v794,v782,v758,v929] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rrrrr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rrrrr = true := by decide +kernel
def tree_eaa8c880_5rrrr : BinaryTree (List W) := .node [v762,v795,v760,v782,v758] tree_eaa8c880_5rrrrl tree_eaa8c880_5rrrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rrrr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rrrr = true := by
  change (_ && everyKey _ tree_eaa8c880_5rrrrl && everyKey _ tree_eaa8c880_5rrrrr) = true
  rw [ok_tree_eaa8c880_5rrrrl, ok_tree_eaa8c880_5rrrrr]
  decide +kernel
def tree_eaa8c880_5rrr : BinaryTree (List W) := .node [v762,v765,v760,v782,v758,v1328] tree_eaa8c880_5rrrl tree_eaa8c880_5rrrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rrr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rrr = true := by
  change (_ && everyKey _ tree_eaa8c880_5rrrl && everyKey _ tree_eaa8c880_5rrrr) = true
  rw [ok_tree_eaa8c880_5rrrl, ok_tree_eaa8c880_5rrrr]
  decide +kernel
def tree_eaa8c880_5rr : BinaryTree (List W) := .node [v762,v765,v760,v782,v771,v841] tree_eaa8c880_5rrl tree_eaa8c880_5rrr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5rr : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5rr = true := by
  change (_ && everyKey _ tree_eaa8c880_5rrl && everyKey _ tree_eaa8c880_5rrr) = true
  rw [ok_tree_eaa8c880_5rrl, ok_tree_eaa8c880_5rrr]
  decide +kernel
def tree_eaa8c880_5r : BinaryTree (List W) := .node [v762,v765,v780,v782,v758] tree_eaa8c880_5rl tree_eaa8c880_5rr
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5r : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5r = true := by
  change (_ && everyKey _ tree_eaa8c880_5rl && everyKey _ tree_eaa8c880_5rr) = true
  rw [ok_tree_eaa8c880_5rl, ok_tree_eaa8c880_5rr]
  decide +kernel
def tree_eaa8c880_5 : BinaryTree (List W) := .node [v762,v1329,v765,v760,v782,v758] tree_eaa8c880_5l tree_eaa8c880_5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_5 : everyKey (rowOK 4 tree_eaa8c880_4) tree_eaa8c880_5 = true := by
  change (_ && everyKey _ tree_eaa8c880_5l && everyKey _ tree_eaa8c880_5r) = true
  rw [ok_tree_eaa8c880_5l, ok_tree_eaa8c880_5r]
  decide +kernel
theorem closed_eaa8c880_5 : Closed 5 tree_eaa8c880_5 := closed_next 4 (by decide) tree_eaa8c880_5 tree_eaa8c880_4 closed_eaa8c880_4 ok_tree_eaa8c880_5
def tree_eaa8c880_6l : BinaryTree (List W) := (.node [v871,v762,v765,v760,v782,v758] (.node [v776,v762,v765,v760,v782,v758] (.node [v866,v762,v765,v760,v782,v758] (.node [v863,v762,v765,v760,v782,v758] (.node [v850,v762,v765,v760,v782,v758] .nil .nil) .nil) (.node [v870,v762,v765,v760,v782,v758] (.node [v872,v762,v765,v760,v782,v758] .nil .nil) .nil)) (.node [v888,v762,v765,v760,v782,v758] (.node [v885,v762,v765,v760,v782,v758] (.node [v1180,v762,v765,v760,v782,v758] .nil .nil) .nil) (.node [v886,v762,v765,v760,v782,v758] .nil .nil))) (.node [v762,v1217,v765,v760,v782,v758] (.node [v787,v762,v765,v760,v782,v758] (.node [v775,v762,v765,v760,v782,v758] (.node [v895,v762,v765,v760,v782,v758] .nil .nil) .nil) (.node [v762,v774,v765,v782,v758] (.node [v762,v774,v765,v760,v782,v758] .nil .nil) .nil)) (.node [v762,v852,v765,v760,v782,v758] (.node [v762,v974,v765,v760,v782,v758] (.node [v762,v963,v765,v760,v782,v758] .nil .nil) .nil) (.node [v762,v796,v765,v760,v782,v758] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_6l : everyKey (rowOK 5 tree_eaa8c880_5) tree_eaa8c880_6l = true := by decide +kernel
def tree_eaa8c880_6r : BinaryTree (List W) := (.node [v762,v765,v760,v887,v782,v758] (.node [v762,v765,v757,v760,v782,v758] (.node [v762,v765,v867,v760,v782,v758] (.node [v762,v765,v985,v760,v782,v758] (.node [v762,v765,v772,v760,v782,v758] .nil .nil) .nil) (.node [v762,v765,v891,v760,v782,v758] (.node [v762,v765,v896,v760,v782,v758] .nil .nil) .nil)) (.node [v762,v765,v760,v890,v782,v758] (.node [v762,v765,v798,v760,v782,v758] (.node [v762,v765,v757,v782,v758] .nil .nil) .nil) (.node [v762,v765,v760,v864,v782,v758] .nil .nil))) (.node [v762,v765,v760,v782,v758,v814] (.node [v762,v765,v760,v782,v758,v976] (.node [v762,v765,v760,v782,v962,v758] (.node [v762,v765,v760,v785,v782,v758] .nil .nil) .nil) (.node [v762,v765,v760,v782,v758,v837] .nil .nil)) (.node [v762,v765,v760,v782,v758,v929] (.node [v762,v765,v760,v782,v758,v898] (.node [v762,v765,v760,v782,v758,v842] .nil .nil) .nil) (.node [v762,v765,v760,v782,v758,v841] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_6r : everyKey (rowOK 5 tree_eaa8c880_5) tree_eaa8c880_6r = true := by decide +kernel
def tree_eaa8c880_6 : BinaryTree (List W) := .node [v762,v805,v765,v760,v782,v758] tree_eaa8c880_6l tree_eaa8c880_6r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_6 : everyKey (rowOK 5 tree_eaa8c880_5) tree_eaa8c880_6 = true := by
  change (_ && everyKey _ tree_eaa8c880_6l && everyKey _ tree_eaa8c880_6r) = true
  rw [ok_tree_eaa8c880_6l, ok_tree_eaa8c880_6r]
  decide +kernel
theorem closed_eaa8c880_6 : Closed 6 tree_eaa8c880_6 := closed_next 5 (by decide) tree_eaa8c880_6 tree_eaa8c880_5 closed_eaa8c880_5 ok_tree_eaa8c880_6
def tree_eaa8c880_7 : BinaryTree (List W) := (.node [v762,v765,v760,v782,v758] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaa8c880_7 : everyKey (rowOK 6 tree_eaa8c880_6) tree_eaa8c880_7 = true := by decide +kernel
theorem closed_eaa8c880_7 : Closed 7 tree_eaa8c880_7 := closed_next 6 (by decide) tree_eaa8c880_7 tree_eaa8c880_6 closed_eaa8c880_6 ok_tree_eaa8c880_7
theorem lower_eaa8c880 : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 7 ins_eaa8c880.toFinset := @no_build 7 tree_eaa8c880_7 ins_eaa8c880 nd_eaa8c880 (by decide) closed_eaa8c880_7 (by decide +kernel)
def gates_eaa8c880 : List Gate := [⟨.or, [0, 2]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [1, 4]⟩, ⟨.or, [2, 8]⟩, ⟨.and, [0, 9]⟩, ⟨.or, [3, 10]⟩, ⟨.and, [7, 11]⟩, ⟨.and, [5, 12]⟩]
theorem upper_eaa8c880 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 9 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeaa8c880 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  exact ⟨gates_eaa8c880, 13, by simp [gates_eaa8c880], rfl, by decide +kernel⟩

def ins_eaaac080 : List W := [0xfdbfc3ff169702a, 0x83dcfdc22c72770, 0x42f4fc5d53c1b17, 0xe74e7c381d39c0e, 0xfd2b3bfce028ed5]
theorem nd_eaaac080 : ins_eaaac080.Nodup := by decide +kernel
theorem rows_eaaac080 : ∀ j : Fin 60, Nat.testBit 0xeaaac080 (∑ i : Fin 5, if (ins_eaaac080.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
def tree_eaaac080_0 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaaac080_0 : everyKey (fun q => !doneTest q) tree_eaaac080_0 = true := by decide +kernel
theorem closed_eaaac080_0 : Closed 0 tree_eaaac080_0 := closed_nil tree_eaaac080_0 ok_tree_eaaac080_0
def tree_eaaac080_1 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaaac080_1 : everyKey (rowOK 0 tree_eaaac080_0) tree_eaaac080_1 = true := by decide +kernel
theorem closed_eaaac080_1 : Closed 1 tree_eaaac080_1 := closed_next 0 (by decide) tree_eaaac080_1 tree_eaaac080_0 closed_eaaac080_0 ok_tree_eaaac080_1
def tree_eaaac080_2 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaaac080_2 : everyKey (rowOK 1 tree_eaaac080_1) tree_eaaac080_2 = true := by decide +kernel
theorem closed_eaaac080_2 : Closed 2 tree_eaaac080_2 := closed_next 1 (by decide) tree_eaaac080_2 tree_eaaac080_1 closed_eaaac080_1 ok_tree_eaaac080_2
def tree_eaaac080_3 : BinaryTree (List W) := (.node [v1330,v1331,v1332,v1333,v1334] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eaaac080_3 : everyKey (rowOK 2 tree_eaaac080_2) tree_eaaac080_3 = true := by decide +kernel
theorem closed_eaaac080_3 : Closed 3 tree_eaaac080_3 := closed_next 2 (by decide) tree_eaaac080_3 tree_eaaac080_2 closed_eaaac080_2 ok_tree_eaaac080_3
theorem lower_eaaac080 : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 3 ins_eaaac080.toFinset := @no_build 3 tree_eaaac080_3 ins_eaaac080 nd_eaaac080 (by decide) closed_eaaac080_3 (by decide +kernel)
def gates_eaaac080 : List Gate := [⟨.or, [0, 3]⟩, ⟨.and, [0, 4]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [6, 7]⟩, ⟨.and, [5, 8]⟩]
theorem upper_eaaac080 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 5 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeaaac080 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  exact ⟨gates_eaaac080, 9, by simp [gates_eaaac080], rfl, by decide +kernel⟩

def ins_eac0e880 : List W := [0x79a3efbd4286aed, 0xd77f1f5455fc181, 0xfefe396eb828e5a, 0xefc5f6b92f11526, 0x913dd1ea04d745a]
theorem nd_eac0e880 : ins_eac0e880.Nodup := by decide +kernel
theorem rows_eac0e880 : ∀ j : Fin 60, Nat.testBit 0xeac0e880 (∑ i : Fin 5, if (ins_eac0e880.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
def tree_eac0e880_0 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eac0e880_0 : everyKey (fun q => !doneTest q) tree_eac0e880_0 = true := by decide +kernel
theorem closed_eac0e880_0 : Closed 0 tree_eac0e880_0 := closed_nil tree_eac0e880_0 ok_tree_eac0e880_0
def tree_eac0e880_1 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eac0e880_1 : everyKey (rowOK 0 tree_eac0e880_0) tree_eac0e880_1 = true := by decide +kernel
theorem closed_eac0e880_1 : Closed 1 tree_eac0e880_1 := closed_next 0 (by decide) tree_eac0e880_1 tree_eac0e880_0 closed_eac0e880_0 ok_tree_eac0e880_1
def tree_eac0e880_2 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eac0e880_2 : everyKey (rowOK 1 tree_eac0e880_1) tree_eac0e880_2 = true := by decide +kernel
theorem closed_eac0e880_2 : Closed 2 tree_eac0e880_2 := closed_next 1 (by decide) tree_eac0e880_2 tree_eac0e880_1 closed_eac0e880_1 ok_tree_eac0e880_2
def tree_eac0e880_3 : BinaryTree (List W) := (.node [v1335,v1336,v1337,v1338] (.node [v1339,v1340,v1338,v1341] (.node [v1342,v1340,v1336,v1337] .nil .nil) (.node [v1340,v1343,v1337,v1341] .nil .nil)) (.node [v1337,v1344,v1338,v1341] (.node [v1336,v1345,v1338,v1341] .nil .nil) .nil))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eac0e880_3 : everyKey (rowOK 2 tree_eac0e880_2) tree_eac0e880_3 = true := by decide +kernel
theorem closed_eac0e880_3 : Closed 3 tree_eac0e880_3 := closed_next 2 (by decide) tree_eac0e880_3 tree_eac0e880_2 closed_eac0e880_2 ok_tree_eac0e880_3
def tree_eac0e880_4l : BinaryTree (List W) := (.node [v1346,v1347,v1337,v1338,v1341] (.node [v1348,v1340,v1336,v1337,v1341] (.node [v1349,v1340,v1336,v1337,v1338] (.node [v1350,v1351,v1336,v1337,v1338] (.node [v1352,v1353,v1340,v1336,v1337] (.node [v1354,v1355,v1340,v1338,v1341] .nil .nil) .nil) (.node [v1356,v1340,v1336,v1337,v1338] .nil .nil)) (.node [v1357,v1340,v1337,v1338,v1341] (.node [v1358,v1359,v1340,v1337,v1341] .nil .nil) (.node [v1360,v1340,v1336,v1337,v1341] .nil .nil))) (.node [v1361,v1362,v1336,v1338,v1341] (.node [v1363,v1340,v1337,v1338,v1341] (.node [v1364,v1337,v1338,v1365,v1341] .nil .nil) (.node [v1366,v1340,v1337,v1338,v1341] .nil .nil)) (.node [v1367,v1340,v1336,v1338,v1341] (.node [v1368,v1340,v1336,v1338,v1341] .nil .nil) (.node [v1369,v1336,v1338,v1341,v1370] .nil .nil)))) (.node [v1371,v1336,v1337,v1338,v1372] (.node [v1373,v1340,v1337,v1338,v1341] (.node [v1374,v1336,v1337,v1338,v1341] (.node [v1375,v1336,v1337,v1341,v1376] .nil .nil) (.node [v1377,v1340,v1337,v1338,v1341] .nil .nil)) (.node [v1378,v1340,v1337,v1338,v1341] (.node [v1379,v1340,v1337,v1338,v1341] .nil .nil) (.node [v1380,v1340,v1336,v1337,v1341] .nil .nil))) (.node [v1340,v1381,v1337,v1341,v1382] (.node [v1383,v1336,v1337,v1338,v1341] (.node [v1384,v1336,v1337,v1338,v1341] .nil .nil) (.node [v1340,v1385,v1337,v1338,v1341] .nil .nil)) (.node [v1340,v1386,v1337,v1338,v1341] (.node [v1340,v1387,v1337,v1338,v1341] .nil .nil) (.node [v1340,v1388,v1337,v1338,v1389] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eac0e880_4l : everyKey (rowOK 3 tree_eac0e880_3) tree_eac0e880_4l = true := by decide +kernel
def tree_eac0e880_4r : BinaryTree (List W) := (.node [v1340,v1336,v1337,v1338,v1390] (.node [v1340,v1336,v1391,v1338,v1341] (.node [v1340,v1392,v1337,v1338,v1341] (.node [v1340,v1393,v1337,v1338,v1341] (.node [v1340,v1394,v1337,v1338,v1341] (.node [v1340,v1395,v1396,v1338,v1341] .nil .nil) .nil) (.node [v1340,v1397,v1337,v1338,v1341] .nil .nil)) (.node [v1340,v1336,v1398,v1341,v1399] (.node [v1340,v1400,v1337,v1338,v1341] .nil .nil) (.node [v1340,v1336,v1401,v1338,v1402] .nil .nil))) (.node [v1340,v1336,v1337,v1403,v1341] (.node [v1340,v1336,v1404,v1338,v1341] (.node [v1340,v1336,v1405,v1338,v1341] .nil .nil) (.node [v1340,v1336,v1337,v1406,v1407] .nil .nil)) (.node [v1340,v1336,v1337,v1338,v1408] (.node [v1340,v1336,v1337,v1409,v1341] .nil .nil) (.node [v1340,v1336,v1337,v1338,v1410] .nil .nil)))) (.node [v1340,v1411,v1337,v1338,v1341] (.node [v1340,v1336,v1412,v1338,v1341] (.node [v1340,v1336,v1337,v1338,v1413] (.node [v1340,v1336,v1337,v1338,v1341] .nil .nil) (.node [v1340,v1336,v1337,v1414,v1341] .nil .nil)) (.node [v1340,v1415,v1337,v1338,v1341] (.node [v1340,v1416,v1337,v1338,v1341] .nil .nil) (.node [v1340,v1417,v1337,v1338,v1341] .nil .nil))) (.node [v1340,v1337,v1338,v1341,v1418] (.node [v1340,v1419,v1337,v1338,v1341] (.node [v1340,v1420,v1337,v1338,v1341] .nil .nil) (.node [v1340,v1337,v1338,v1421,v1341] .nil .nil)) (.node [v1422,v1336,v1337,v1338,v1341] (.node [v1423,v1336,v1337,v1338,v1341] .nil .nil) (.node [v1424,v1336,v1337,v1338,v1341] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eac0e880_4r : everyKey (rowOK 3 tree_eac0e880_3) tree_eac0e880_4r = true := by decide +kernel
def tree_eac0e880_4 : BinaryTree (List W) := .node [v1340,v1425,v1337,v1338,v1341] tree_eac0e880_4l tree_eac0e880_4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eac0e880_4 : everyKey (rowOK 3 tree_eac0e880_3) tree_eac0e880_4 = true := by
  change (_ && everyKey _ tree_eac0e880_4l && everyKey _ tree_eac0e880_4r) = true
  rw [ok_tree_eac0e880_4l, ok_tree_eac0e880_4r]
  decide +kernel
theorem closed_eac0e880_4 : Closed 4 tree_eac0e880_4 := closed_next 3 (by decide) tree_eac0e880_4 tree_eac0e880_3 closed_eac0e880_3 ok_tree_eac0e880_4
def tree_eac0e880_5l : BinaryTree (List W) := (.node [v1426,v1340,v1336,v1337,v1338,v1341] (.node [v1427,v1340,v1336,v1337,v1338,v1341] (.node [v1428,v1340,v1336,v1337,v1338,v1341] (.node [v1429,v1340,v1336,v1337,v1338,v1341] (.node [v1354,v1340,v1336,v1337,v1338,v1341] .nil .nil) .nil) (.node [v1350,v1340,v1336,v1337,v1338,v1341] (.node [v1352,v1340,v1336,v1337,v1338,v1341] .nil .nil) .nil)) (.node [v1353,v1340,v1336,v1337,v1338,v1341] (.node [v1430,v1340,v1336,v1337,v1338,v1341] (.node [v1358,v1340,v1336,v1337,v1338,v1341] .nil .nil) .nil) (.node [v1364,v1340,v1336,v1337,v1338,v1341] .nil .nil))) (.node [v1346,v1340,v1336,v1337,v1338,v1341] (.node [v1355,v1340,v1336,v1337,v1338,v1341] (.node [v1431,v1340,v1336,v1337,v1338,v1341] (.node [v1361,v1340,v1336,v1337,v1338,v1341] .nil .nil) .nil) (.node [v1369,v1340,v1336,v1337,v1338,v1341] .nil .nil)) (.node [v1432,v1340,v1336,v1337,v1338,v1341] (.node [v1359,v1340,v1336,v1337,v1338,v1341] (.node [v1375,v1340,v1336,v1337,v1338,v1341] .nil .nil) .nil) (.node [v1371,v1340,v1336,v1337,v1338,v1341] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eac0e880_5l : everyKey (rowOK 4 tree_eac0e880_4) tree_eac0e880_5l = true := by decide +kernel
def tree_eac0e880_5r : BinaryTree (List W) := (.node [v1340,v1336,v1337,v1406,v1338,v1341] (.node [v1340,v1388,v1336,v1337,v1338,v1341] (.node [v1340,v1362,v1336,v1337,v1338,v1341] (.node [v1340,v1433,v1336,v1337,v1338,v1341] (.node [v1340,v1381,v1336,v1337,v1338,v1341] .nil .nil) .nil) (.node [v1340,v1351,v1336,v1337,v1338,v1341] .nil .nil)) (.node [v1340,v1336,v1401,v1337,v1338,v1341] (.node [v1340,v1336,v1398,v1337,v1338,v1341] (.node [v1340,v1395,v1336,v1337,v1338,v1341] .nil .nil) .nil) (.node [v1340,v1336,v1337,v1396,v1338,v1341] .nil .nil))) (.node [v1340,v1336,v1337,v1338,v1341,v1389] (.node [v1340,v1336,v1337,v1338,v1341,v1382] (.node [v1340,v1336,v1337,v1338,v1341,v1376] (.node [v1340,v1336,v1337,v1338,v1365,v1341] .nil .nil) .nil) (.node [v1340,v1336,v1337,v1338,v1341,v1402] .nil .nil)) (.node [v1340,v1336,v1337,v1338,v1341,v1407] (.node [v1340,v1336,v1337,v1338,v1341,v1399] (.node [v1340,v1336,v1337,v1338,v1341,v1370] .nil .nil) .nil) (.node [v1340,v1336,v1337,v1338,v1341,v1372] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eac0e880_5r : everyKey (rowOK 4 tree_eac0e880_4) tree_eac0e880_5r = true := by decide +kernel
def tree_eac0e880_5 : BinaryTree (List W) := .node [v1340,v1347,v1336,v1337,v1338,v1341] tree_eac0e880_5l tree_eac0e880_5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eac0e880_5 : everyKey (rowOK 4 tree_eac0e880_4) tree_eac0e880_5 = true := by
  change (_ && everyKey _ tree_eac0e880_5l && everyKey _ tree_eac0e880_5r) = true
  rw [ok_tree_eac0e880_5l, ok_tree_eac0e880_5r]
  decide +kernel
theorem closed_eac0e880_5 : Closed 5 tree_eac0e880_5 := closed_next 4 (by decide) tree_eac0e880_5 tree_eac0e880_4 closed_eac0e880_4 ok_tree_eac0e880_5
def tree_eac0e880_6 : BinaryTree (List W) := (.node [v1340,v1336,v1337,v1338,v1341] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eac0e880_6 : everyKey (rowOK 5 tree_eac0e880_5) tree_eac0e880_6 = true := by decide +kernel
theorem closed_eac0e880_6 : Closed 6 tree_eac0e880_6 := closed_next 5 (by decide) tree_eac0e880_6 tree_eac0e880_5 closed_eac0e880_5 ok_tree_eac0e880_6
theorem lower_eac0e880 : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 6 ins_eac0e880.toFinset := @no_build 6 tree_eac0e880_6 ins_eac0e880 nd_eac0e880 (by decide) closed_eac0e880_6 (by decide +kernel)
def gates_eac0e880 : List Gate := [⟨.and, [0, 3]⟩, ⟨.and, [1, 2]⟩, ⟨.or, [5, 6]⟩, ⟨.and, [0, 1]⟩, ⟨.and, [2, 3]⟩, ⟨.or, [8, 9]⟩, ⟨.or, [4, 10]⟩, ⟨.and, [7, 11]⟩]
theorem upper_eac0e880 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 8 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeac0e880 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  exact ⟨gates_eac0e880, 12, by simp [gates_eac0e880], rfl, by decide +kernel⟩

def ins_eac8e080 : List W := [0xfdc6bfce501afc3, 0x773bc6ff0c2d1b9, 0xa79ebbc21c6a2e, 0xebf57d06afd1141, 0xffae1c79bea0616]
theorem nd_eac8e080 : ins_eac8e080.Nodup := by decide +kernel
theorem rows_eac8e080 : ∀ j : Fin 60, Nat.testBit 0xeac8e080 (∑ i : Fin 5, if (ins_eac8e080.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
def tree_eac8e080_0 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eac8e080_0 : everyKey (fun q => !doneTest q) tree_eac8e080_0 = true := by decide +kernel
theorem closed_eac8e080_0 : Closed 0 tree_eac8e080_0 := closed_nil tree_eac8e080_0 ok_tree_eac8e080_0
def tree_eac8e080_1 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eac8e080_1 : everyKey (rowOK 0 tree_eac8e080_0) tree_eac8e080_1 = true := by decide +kernel
theorem closed_eac8e080_1 : Closed 1 tree_eac8e080_1 := closed_next 0 (by decide) tree_eac8e080_1 tree_eac8e080_0 closed_eac8e080_0 ok_tree_eac8e080_1
def tree_eac8e080_2 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eac8e080_2 : everyKey (rowOK 1 tree_eac8e080_1) tree_eac8e080_2 = true := by decide +kernel
theorem closed_eac8e080_2 : Closed 2 tree_eac8e080_2 := closed_next 1 (by decide) tree_eac8e080_2 tree_eac8e080_1 closed_eac8e080_1 ok_tree_eac8e080_2
def tree_eac8e080_3 : BinaryTree (List W) := (.node [v1434,v1435,v1436,v1437] (.node [v1438,v1439,v1434,v1436] (.node [v1440,v1438,v1434,v1441] .nil .nil) (.node [v1438,v1442,v1436,v1437] .nil .nil)) (.node [v1434,v1441,v1443,v1437] (.node [v1434,v1441,v1444,v1436] .nil .nil) (.node [v1445,v1441,v1436,v1437] .nil .nil)))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eac8e080_3 : everyKey (rowOK 2 tree_eac8e080_2) tree_eac8e080_3 = true := by decide +kernel
theorem closed_eac8e080_3 : Closed 3 tree_eac8e080_3 := closed_next 2 (by decide) tree_eac8e080_3 tree_eac8e080_2 closed_eac8e080_2 ok_tree_eac8e080_3
def tree_eac8e080_4l : BinaryTree (List W) := (.node [v1446,v1434,v1447,v1436,v1437] (.node [v1448,v1438,v1434,v1441,v1437] (.node [v1449,v1438,v1434,v1441,v1436] (.node [v1450,v1438,v1451,v1434,v1436] (.node [v1452,v1453,v1438,v1434,v1441] (.node [v1454,v1434,v1455,v1436,v1437] .nil .nil) .nil) (.node [v1456,v1434,v1441,v1457,v1436] .nil .nil)) (.node [v1458,v1438,v1434,v1441,v1436] (.node [v1459,v1438,v1434,v1441,v1436] .nil .nil) (.node [v1460,v1434,v1441,v1461,v1437] .nil .nil))) (.node [v1462,v1434,v1441,v1436,v1437] (.node [v1463,v1464,v1441,v1436,v1437] (.node [v1465,v1438,v1434,v1441,v1437] .nil .nil) (.node [v1466,v1434,v1441,v1436,v1437] .nil .nil)) (.node [v1467,v1434,v1441,v1437,v1468] (.node [v1469,v1470,v1441,v1436,v1437] .nil .nil) (.node [v1471,v1434,v1441,v1436,v1472] .nil .nil)))) (.node [v1438,v1473,v1441,v1436,v1437] (.node [v1438,v1474,v1475,v1436,v1437] (.node [v1476,v1434,v1441,v1436,v1437] (.node [v1477,v1434,v1441,v1436,v1437] .nil .nil) (.node [v1438,v1478,v1434,v1436,v1437] .nil .nil)) (.node [v1438,v1479,v1434,v1436,v1437] (.node [v1438,v1480,v1434,v1436,v1437] .nil .nil) (.node [v1438,v1481,v1441,v1436,v1437] .nil .nil))) (.node [v1438,v1482,v1441,v1436,v1437] (.node [v1438,v1483,v1441,v1437,v1484] (.node [v1438,v1485,v1436,v1437,v1486] .nil .nil) (.node [v1438,v1487,v1441,v1436,v1437] .nil .nil)) (.node [v1438,v1434,v1488,v1436,v1437] (.node [v1438,v1434,v1489,v1436,v1437] .nil .nil) (.node [v1438,v1434,v1490,v1436,v1437] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eac8e080_4l : everyKey (rowOK 3 tree_eac8e080_3) tree_eac8e080_4l = true := by decide +kernel
def tree_eac8e080_4r : BinaryTree (List W) := (.node [v1438,v1434,v1441,v1436,v1491] (.node [v1438,v1434,v1441,v1492,v1493] (.node [v1438,v1434,v1494,v1436,v1437] (.node [v1438,v1434,v1495,v1436,v1437] (.node [v1438,v1434,v1496,v1436,v1497] (.node [v1438,v1434,v1498,v1436,v1437] .nil .nil) .nil) (.node [v1438,v1434,v1499,v1436,v1437] .nil .nil)) (.node [v1438,v1434,v1441,v1500,v1436] (.node [v1438,v1434,v1441,v1501,v1436] .nil .nil) (.node [v1438,v1434,v1441,v1502,v1436] .nil .nil))) (.node [v1438,v1434,v1441,v1436,v1503] (.node [v1438,v1434,v1441,v1504,v1437] (.node [v1438,v1434,v1441,v1505,v1436] .nil .nil) (.node [v1438,v1434,v1441,v1506,v1437] .nil .nil)) (.node [v1438,v1434,v1441,v1436,v1507] (.node [v1438,v1434,v1441,v1436,v1508] .nil .nil) (.node [v1438,v1434,v1441,v1436,v1437] .nil .nil)))) (.node [v1438,v1509,v1441,v1436,v1437] (.node [v1438,v1434,v1510,v1436,v1437] (.node [v1438,v1434,v1441,v1436,v1511] (.node [v1438,v1434,v1441,v1436,v1512] .nil .nil) (.node [v1438,v1434,v1441,v1436,v1513] .nil .nil)) (.node [v1438,v1434,v1436,v1437,v1514] (.node [v1438,v1434,v1436,v1437,v1515] .nil .nil) (.node [v1438,v1434,v1436,v1437,v1516] .nil .nil))) (.node [v1434,v1517,v1441,v1436,v1437] (.node [v1438,v1441,v1518,v1436,v1437] (.node [v1438,v1519,v1441,v1436,v1437] .nil .nil) (.node [v1438,v1441,v1436,v1437,v1520] .nil .nil)) (.node [v1434,v1441,v1521,v1436,v1437] (.node [v1434,v1441,v1522,v1436,v1437] .nil .nil) (.node [v1434,v1441,v1436,v1437,v1523] .nil .nil)))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eac8e080_4r : everyKey (rowOK 3 tree_eac8e080_3) tree_eac8e080_4r = true := by decide +kernel
def tree_eac8e080_4 : BinaryTree (List W) := .node [v1438,v1434,v1524,v1437,v1525] tree_eac8e080_4l tree_eac8e080_4r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eac8e080_4 : everyKey (rowOK 3 tree_eac8e080_3) tree_eac8e080_4 = true := by
  change (_ && everyKey _ tree_eac8e080_4l && everyKey _ tree_eac8e080_4r) = true
  rw [ok_tree_eac8e080_4l, ok_tree_eac8e080_4r]
  decide +kernel
theorem closed_eac8e080_4 : Closed 4 tree_eac8e080_4 := closed_next 3 (by decide) tree_eac8e080_4 tree_eac8e080_3 closed_eac8e080_3 ok_tree_eac8e080_4
def tree_eac8e080_5l : BinaryTree (List W) := (.node [v1469,v1438,v1434,v1441,v1436,v1437] (.node [v1453,v1438,v1434,v1441,v1436,v1437] (.node [v1452,v1438,v1434,v1441,v1436,v1437] (.node [v1526,v1438,v1434,v1441,v1436,v1437] (.node [v1454,v1438,v1434,v1441,v1436,v1437] .nil .nil) .nil) (.node [v1456,v1438,v1434,v1441,v1436,v1437] (.node [v1450,v1438,v1434,v1441,v1436,v1437] .nil .nil) .nil)) (.node [v1527,v1438,v1434,v1441,v1436,v1437] (.node [v1460,v1438,v1434,v1441,v1436,v1437] (.node [v1528,v1438,v1434,v1441,v1436,v1437] .nil .nil) .nil) (.node [v1463,v1438,v1434,v1441,v1436,v1437] .nil .nil))) (.node [v1438,v1451,v1434,v1441,v1436,v1437] (.node [v1446,v1438,v1434,v1441,v1436,v1437] (.node [v1471,v1438,v1434,v1441,v1436,v1437] (.node [v1467,v1438,v1434,v1441,v1436,v1437] .nil .nil) .nil) (.node [v1438,v1529,v1434,v1441,v1436,v1437] .nil .nil)) (.node [v1438,v1470,v1434,v1441,v1436,v1437] (.node [v1438,v1485,v1434,v1441,v1436,v1437] (.node [v1438,v1474,v1434,v1441,v1436,v1437] .nil .nil) .nil) (.node [v1438,v1483,v1434,v1441,v1436,v1437] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eac8e080_5l : everyKey (rowOK 4 tree_eac8e080_4) tree_eac8e080_5l = true := by decide +kernel
def tree_eac8e080_5r : BinaryTree (List W) := (.node [v1438,v1434,v1441,v1461,v1436,v1437] (.node [v1438,v1434,v1455,v1441,v1436,v1437] (.node [v1438,v1434,v1530,v1441,v1436,v1437] (.node [v1438,v1434,v1531,v1441,v1436,v1437] (.node [v1438,v1434,v1464,v1441,v1436,v1437] .nil .nil) .nil) (.node [v1438,v1434,v1475,v1441,v1436,v1437] .nil .nil)) (.node [v1438,v1434,v1441,v1447,v1436,v1437] (.node [v1438,v1434,v1496,v1441,v1436,v1437] (.node [v1438,v1434,v1524,v1441,v1436,v1437] .nil .nil) .nil) (.node [v1438,v1434,v1441,v1457,v1436,v1437] .nil .nil))) (.node [v1438,v1434,v1441,v1436,v1437,v1497] (.node [v1438,v1434,v1441,v1436,v1437,v1493] (.node [v1438,v1434,v1441,v1436,v1437,v1532] (.node [v1438,v1434,v1441,v1492,v1436,v1437] .nil .nil) .nil) (.node [v1438,v1434,v1441,v1436,v1437,v1525] .nil .nil)) (.node [v1438,v1434,v1441,v1436,v1437,v1484] (.node [v1438,v1434,v1441,v1436,v1437,v1468] (.node [v1438,v1434,v1441,v1436,v1437,v1472] .nil .nil) .nil) (.node [v1438,v1434,v1441,v1436,v1437,v1486] .nil .nil))))
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eac8e080_5r : everyKey (rowOK 4 tree_eac8e080_4) tree_eac8e080_5r = true := by decide +kernel
def tree_eac8e080_5 : BinaryTree (List W) := .node [v1438,v1533,v1434,v1441,v1436,v1437] tree_eac8e080_5l tree_eac8e080_5r
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eac8e080_5 : everyKey (rowOK 4 tree_eac8e080_4) tree_eac8e080_5 = true := by
  change (_ && everyKey _ tree_eac8e080_5l && everyKey _ tree_eac8e080_5r) = true
  rw [ok_tree_eac8e080_5l, ok_tree_eac8e080_5r]
  decide +kernel
theorem closed_eac8e080_5 : Closed 5 tree_eac8e080_5 := closed_next 4 (by decide) tree_eac8e080_5 tree_eac8e080_4 closed_eac8e080_4 ok_tree_eac8e080_5
def tree_eac8e080_6 : BinaryTree (List W) := (.node [v1438,v1434,v1441,v1436,v1437] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_eac8e080_6 : everyKey (rowOK 5 tree_eac8e080_5) tree_eac8e080_6 = true := by decide +kernel
theorem closed_eac8e080_6 : Closed 6 tree_eac8e080_6 := closed_next 5 (by decide) tree_eac8e080_6 tree_eac8e080_5 closed_eac8e080_5 ok_tree_eac8e080_6
theorem lower_eac8e080 : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 6 ins_eac8e080.toFinset := @no_build 6 tree_eac8e080_6 ins_eac8e080 nd_eac8e080 (by decide) closed_eac8e080_6 (by decide +kernel)
def gates_eac8e080 : List Gate := [⟨.or, [0, 1]⟩, ⟨.and, [0, 4]⟩, ⟨.or, [2, 6]⟩, ⟨.or, [0, 4]⟩, ⟨.and, [1, 8]⟩, ⟨.or, [3, 9]⟩, ⟨.and, [7, 10]⟩, ⟨.and, [5, 11]⟩]
theorem upper_eac8e080 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 8 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xeac8e080 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  exact ⟨gates_eac8e080, 12, by simp [gates_eac8e080], rfl, by decide +kernel⟩

def ins_aaa8a8a8 : List W := [0xfffffffd0d80ccc, 0x1da64eac7219323, 0xb2df514a407d012, 0xeed0e6d893431b6, 0x489ab43c766ad0b]
theorem nd_aaa8a8a8 : ins_aaa8a8a8.Nodup := by decide +kernel
theorem rows_aaa8a8a8 : ∀ j : Fin 60, Nat.testBit 0xaaa8a8a8 (∑ i : Fin 5, if (ins_aaa8a8a8.getD i.val 0)[j.val] then 2^(i : ℕ) else 0) = goal[j.val] := by decide +kernel
def tree_aaa8a8a8_0 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_aaa8a8a8_0 : everyKey (fun q => !doneTest q) tree_aaa8a8a8_0 = true := by decide +kernel
theorem closed_aaa8a8a8_0 : Closed 0 tree_aaa8a8a8_0 := closed_nil tree_aaa8a8a8_0 ok_tree_aaa8a8a8_0
def tree_aaa8a8a8_1 : BinaryTree (List W) := .nil
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_aaa8a8a8_1 : everyKey (rowOK 0 tree_aaa8a8a8_0) tree_aaa8a8a8_1 = true := by decide +kernel
theorem closed_aaa8a8a8_1 : Closed 1 tree_aaa8a8a8_1 := closed_next 0 (by decide) tree_aaa8a8a8_1 tree_aaa8a8a8_0 closed_aaa8a8a8_0 ok_tree_aaa8a8a8_1
def tree_aaa8a8a8_2 : BinaryTree (List W) := (.node [v1534,v1535,v1536,v1537,v1538] .nil .nil)
set_option maxRecDepth 16000 in
set_option maxHeartbeats 8000000 in
theorem ok_tree_aaa8a8a8_2 : everyKey (rowOK 1 tree_aaa8a8a8_1) tree_aaa8a8a8_2 = true := by decide +kernel
theorem closed_aaa8a8a8_2 : Closed 2 tree_aaa8a8a8_2 := closed_next 1 (by decide) tree_aaa8a8a8_2 tree_aaa8a8a8_1 closed_aaa8a8a8_1 ok_tree_aaa8a8a8_2
theorem lower_aaa8a8a8 : ∀ z, z = goal ∨ z = ~~~goal → ¬ build basicOps z 2 ins_aaa8a8a8.toFinset := @no_build 2 tree_aaa8a8a8_2 ins_aaa8a8a8 nd_aaa8a8a8 (by decide) closed_aaa8a8a8_2 (by decide +kernel)
def gates_aaa8a8a8 : List Gate := [⟨.and, [3, 4]⟩, ⟨.or, [2, 5]⟩, ⟨.or, [1, 6]⟩, ⟨.and, [0, 7]⟩]
theorem upper_aaa8a8a8 : ∃ (gs : List Gate) (o : ℕ), (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧ gs.length = 4 ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = Nat.testBit 0xaaa8a8a8 (∑ i : Fin 5, if x i then 2^(i : ℕ) else 0) := by
  exact ⟨gates_aaa8a8a8, 8, by simp [gates_aaa8a8a8], rfl, by decide +kernel⟩

end PEqualNP.Outside.L_meta_1423_aux
open PEqualNP.Outside.L_meta_1423_aux in
set_option maxRecDepth 6000 in
theorem PEqualNP.Outside.L_meta_1423 : ∀ T ∈ ({0xe8a8a888, 0xe8a8c888, 0xe8a8e880, 0xe8e8e800, 0xeaa8a880, 0xeaa8c880, 0xeaaac080, 0xeac0e880, 0xeac8e080, 0xaaa8a8a8} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro T mem gs o hg _ he
  simp only [Finset.mem_insert, Finset.mem_singleton] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact replace 0xe8a8a888 8 ins_e8a8a888 nd_e8a8a888 rows_e8a8a888 rfl lower_e8a8a888 upper_e8a8a888 gs o hg he
  · exact replace 0xe8a8c888 6 ins_e8a8c888 nd_e8a8c888 rows_e8a8c888 rfl lower_e8a8c888 upper_e8a8c888 gs o hg he
  · exact replace 0xe8a8e880 8 ins_e8a8e880 nd_e8a8e880 rows_e8a8e880 rfl lower_e8a8e880 upper_e8a8e880 gs o hg he
  · exact replace 0xe8e8e800 6 ins_e8e8e800 nd_e8e8e800 rows_e8e8e800 rfl lower_e8e8e800 upper_e8e8e800 gs o hg he
  · exact replace 0xeaa8a880 9 ins_eaa8a880 nd_eaa8a880 rows_eaa8a880 rfl lower_eaa8a880 upper_eaa8a880 gs o hg he
  · exact replace 0xeaa8c880 9 ins_eaa8c880 nd_eaa8c880 rows_eaa8c880 rfl lower_eaa8c880 upper_eaa8c880 gs o hg he
  · exact replace 0xeaaac080 5 ins_eaaac080 nd_eaaac080 rows_eaaac080 rfl lower_eaaac080 upper_eaaac080 gs o hg he
  · exact replace 0xeac0e880 8 ins_eac0e880 nd_eac0e880 rows_eac0e880 rfl lower_eac0e880 upper_eac0e880 gs o hg he
  · exact replace 0xeac8e080 8 ins_eac8e080 nd_eac8e080 rows_eac8e080 rfl lower_eac8e080 upper_eac8e080 gs o hg he
  · exact replace 0xaaa8a8a8 4 ins_aaa8a8a8 nd_aaa8a8a8 rows_aaa8a8a8 rfl lower_aaa8a8a8 upper_aaa8a8a8 gs o hg he
