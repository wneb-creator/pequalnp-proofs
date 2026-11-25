import PEqualNP.Defs

-- Adapted from L_meta_16045 and the L_meta_12827 proof by k-sandhu.
-- The signed search derives from L-meta-9146 and L-meta-8633.
-- Gate elimination derives from L-meta-9543 and L-meta-927.


namespace PEqualNP.Outside.L_meta_16664
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace Signed

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

set_option maxRecDepth 100000 in
lemma compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
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

set_option maxRecDepth 100000 in
lemma live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
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

set_option maxRecDepth 100000 in
lemma live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
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

set_option maxRecDepth 100000 in
lemma first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
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

abbrev W := BitVec 240

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 120 := ((x >>> 120) ^^^ x).setWidth 120
def cuts (ws : List W) : BitVec 120 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 120) ++ (0 : BitVec 120)
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
lemma pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

set_option maxRecDepth 100000 in
lemma pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
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

def differs (i : Fin 120) (w : W) : Prop :=
  w.getLsbD (120+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 100000 in
lemma ops_differs (i : Fin 120) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 120+i.val < 240 := by omega
  have hi' : i.val < 240 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 100000 in
lemma cuts_spec (ws : List W) (i : Fin 120) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have bx (p q : Bool) : Bool.xor p q = true ↔ p ≠ q := by cases p <;> cases q <;> decide
    simp [sep, i.isLt, differs, Nat.add_comm, bx]

set_option maxRecDepth 100000 in
lemma cuts_full {g : W} (hg : g = goal ∨ g = ~~~goal) {k : ℕ} {ws : List W}
    (h : live basicOps g k ws.toFinset) : cuts ws = -1 := by
  have hd : ∀ i, differs i g := by rcases hg with rfl | rfl <;> unfold differs <;> decide +kernel
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (hd ⟨j,hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 120)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

set_option maxRecDepth 100000 in
lemma ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 100000 in
lemma recover_kept {ws r : List W} {a b : W} {needed : Finset W}
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

set_option maxRecDepth 100000 in
lemma singleton_list {goal : W} {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    !((a :: b :: r).contains w) && (((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r)))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

set_option maxRecDepth 100000 in
lemma dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (hnew : z ∉ a :: b :: r) (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨by simp [hnew], ?_⟩
  simp [keepChoices] at hk
  rcases hk with rfl | rfl | rfl | rfl <;>
    simp only [cuts, List.foldr_cons] at hc ⊢ <;>
    (try simp only [List.length_cons] at *) <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, bne_iff_ne]
  · left; left; exact ⟨hc, by convert ht using 2; omega⟩
  · left; right; exact ⟨by omega, .inl ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · left; right; exact ⟨by omega, .inr ⟨by convert hc using 1; ac_rfl, by convert ht using 2; omega⟩⟩
  · right; exact ⟨⟨by omega, by convert hc using 1; ac_rfl⟩, by convert ht using 2; omega⟩

set_option maxRecDepth 100000 in
lemma optimized_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch extra (optimized k) a b r = true := by
        have absent : z ∉ a :: b :: r := fun hz =>
          hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hz))
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk absent (by omega) (by omega) (cuts_full hg hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def search (n : ℕ) (inputs : List W) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && (cuts ws == -1) && optimized n (n+1-ws.length) ws

set_option maxRecDepth 100000 in
lemma search_complete {g : W} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List W)
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, cuts_full hg hl', optimized_complete hg n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def holds (av : Finset W) (z : W) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

set_option maxRecDepth 100000 in
lemma holds_insert {av : Finset W} {z a : W} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

set_option maxRecDepth 100000 in
lemma holds_not {av : Finset W} {z : W} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset W) (z : W) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

set_option maxRecDepth 100000 in
lemma reachable_not {av : Finset W} {z : W} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 100000 in
lemma and_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : W) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : W) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · change reachable av (BitVec.allOnes 240 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 240)
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

set_option maxRecDepth 100000 in
lemma or_reach {av : Finset W} {x y : W} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin 240) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private lemma read_bit (w : List W) (i : ℕ) (k : Fin 240) :
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

set_option maxRecDepth 100000 in
lemma action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 240) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0 : W)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, GateOp.eval, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      bit0,Bool.not_false]

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

set_option maxRecDepth 100000 in
lemma available_read {av : Finset W} {w : List W} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 100000 in
lemma gate_reach (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
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

set_option maxRecDepth 100000 in
lemma compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k (~~~goal)) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = ~~~goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim ((by decide : ~~~goal ≠ 0) zero)
    · exact False.elim ((by decide : ~~~goal ≠ ~~~0) ones)
    · exact ⟨t, .inr eq.symm, ht⟩
    · exact ⟨t, .inl (by simpa only [BitVec.not_not] using congrArg (fun w : W => ~~~w) eq.symm), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k (~~~goal) := by
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

def F (x : Fin 5 → Bool) : Bool := (4276808936 : ℕ).testBit (∑ i : Fin 5, if x i then 2 ^ i.val else 0)

lemma bound_from_search (inputs : List W) (width : inputs.length = 5)
    (nd : inputs.Nodup) (reject : search 7 inputs = false)
    (sample : ∀ k : Fin 240, F (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) :
    7 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 240) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 5) : Bool := bit k (inputs.getD i.val 0)
    have same : List.ofFn x = inputs.map (bit k) := by
      apply List.ext_getElem
      · simp [width]
      · intro i hi hj
        have hlt : i < inputs.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs,o⟩ (inputs.map (bit k)) = bit k (~~~goal)
    rw [← same, he]
    exact sample k
  obtain ⟨t, ht, run⟩ := compile gs o hg inputs inputs.toFinset init evaluate
  have lift {a c : ℕ} (h : a ≤ c) (hr : build basicOps t a inputs.toFinset) :
      build basicOps t c inputs.toFinset := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 7 inputs nd (lift low run)))


def rows : List W :=
  [55214405208618729467034520380839570690669382403384614339707185604607796,
   221941235689046003970522323171767282998876794266510458948512754036236505,
   1332117931867639019780548853069657189553651376118466973095916591110823307,
   635085915085975334765247761183074419441811179324996912037079836828880582,
   1045431751894572903946538904828429715066363458501417034287905705055973934]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def maskN : Nat := 1329227995784915872903807060280344575

def sepN (w : Nat) : Nat := (w >>> 120) % 1329227995784915872903807060280344576 ^^^ w % 1329227995784915872903807060280344576

def cutsN (ws : List Nat) : Nat := ws.foldr (fun w acc => sepN w ||| acc) 0

def opsN (a b : Nat) : List Nat :=
  [a &&& b, a ||| b, a &&& (1766847064778384329583297500742918515827483896875618958121606201292619775 - b), b &&& (1766847064778384329583297500742918515827483896875618958121606201292619775 - a)]

def dispatchN (extra : Nat) (next : Nat → List Nat → Bool) (a b : Nat) (r : List Nat) : Bool :=
  let base := cutsN r
  (opsN a b).any fun w =>
    let v := sepN w ||| base
    !((a :: b :: r).contains w) && (((v == maskN) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sepN a == maskN) && next (extra - 1) (w :: a :: r)) ||
                      ((v ||| sepN b == maskN) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sepN a ||| sepN b == maskN) && next (extra - 2) (w :: a :: b :: r)))

def reachedN (ws : List Nat) : Bool :=
  ws == [goal.toNat] || ws == [(~~~goal).toNat]

def optimizeN : Nat → Nat → List Nat → Bool
  | 0, _, ws => reachedN ws
  | k + 1, extra, ws => reachedN ws ||
    (pairs ws).any (fun (a, b, r) => dispatchN extra (optimizeN k) a b r)

def searchN (n : Nat) (inputs : List Nat) : Bool :=
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n + 1) && (cutsN ws == maskN) && optimizeN n (n + 1 - ws.length) ws

lemma singleMap (f : W → Nat) (xs : List W) :
    singles (xs.map f) = (singles xs).map (fun (a, r) => (f a, r.map f)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [singles, ih, List.map_map, Function.comp_def]

lemma pairMap (f : W → Nat) (xs : List W) :
    pairs (xs.map f) = (pairs xs).map (fun (a, b, r) => (f a, f b, r.map f)) := by
  induction xs with
  | nil => rfl
  | cons a xs ih => simp [pairs, singleMap, ih, List.map_map, Function.comp_def]

lemma maskMap : maskN = (-1 : BitVec 120).toNat := by decide

lemma sepMap (w : W) : sepN w.toNat = (sep w).toNat := by
  simp [sepN, sep, BitVec.toNat_setWidth]

lemma cutsMap (ws : List W) : cutsN (ws.map BitVec.toNat) = (cuts ws).toNat := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    change sepN w.toNat ||| cutsN (ws.map BitVec.toNat) = (sep w ||| cuts ws).toNat
    rw [sepMap, ih, BitVec.toNat_or]

lemma opsMap (a b : W) : (ops a b).map BitVec.toNat = opsN a.toNat b.toNat := by
  simp [ops, opsN]

lemma equalBits {n : Nat} (a b : BitVec n) : (a.toNat == b.toNat) = (a == b) := by
  apply Bool.eq_iff_iff.mpr
  simp only [beq_iff_eq, BitVec.toNat_inj]

lemma containsMap (ws : List W) (w : W) :
    (ws.map BitVec.toNat).contains w.toNat = ws.contains w := by
  apply Bool.eq_iff_iff.mpr
  simp [List.contains_iff_mem, List.mem_map, BitVec.toNat_inj]

lemma reachedMap (ws : List W) : reachedN (ws.map BitVec.toNat) = (ws == [goal] || ws == [~~~goal]) := by
  have same (w : W) : (ws.map BitVec.toNat == [w.toNat]) = (ws == [w]) := by
    change (ws.map BitVec.toNat == ([w] : List W).map BitVec.toNat) = _
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact List.map_inj_right (fun _ _ h => BitVec.toNat_inj.mp h)
  simp only [reachedN, same]

lemma dispatchMap (extra : Nat) (nextN : Nat → List Nat → Bool) (next : Nat → List W → Bool)
    (agree : ∀ e ws, nextN e (ws.map BitVec.toNat) = next e ws) (a b : W) (r : List W) :
    dispatchN extra nextN a.toNat b.toNat (r.map BitVec.toNat) = dispatch extra next a b r := by
  simp only [dispatchN, dispatch, ← opsMap, List.any_map]
  apply List.any_congr rfl
  intro w
  simpa only [Function.comp_apply, sepMap, cutsMap, ← BitVec.toNat_or, maskMap, equalBits,
    ← List.map_cons, containsMap, agree]

lemma optimizeMap (depth extra : Nat) (ws : List W) :
    optimizeN depth extra (ws.map BitVec.toNat) = optimized depth extra ws := by
  induction depth generalizing extra ws with
  | zero => exact reachedMap ws
  | succ n ih =>
    simp only [optimizeN, optimized, reachedMap, pairMap, List.any_map]
    congr 1
    apply List.any_congr rfl
    rintro ⟨a, b, r⟩
    exact dispatchMap extra (optimizeN n) (optimized n) ih a b r

lemma searchMap (n : Nat) (ws : List W) :
    searchN n (ws.map BitVec.toNat) = search n ws := by
  simp only [searchN, search, List.sublists_map, List.any_map]
  apply List.any_congr rfl
  intro a
  simp only [Function.comp_apply, List.length_map, cutsMap, maskMap, equalBits, optimizeMap]


def rowsN : List Nat := [55214405208618729467034520380839570690669382403384614339707185604607796, 221941235689046003970522323171767282998876794266510458948512754036236505, 1332117931867639019780548853069657189553651376118466973095916591110823307, 635085915085975334765247761183074419441811179324996912037079836828880582, 1045431751894572903946538904828429715066363458501417034287905705055973934]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma checkPair0 : dispatchN 3 (optimizeN 6) 55214405208618729467034520380839570690669382403384614339707185604607796 221941235689046003970522323171767282998876794266510458948512754036236505 [1332117931867639019780548853069657189553651376118466973095916591110823307, 635085915085975334765247761183074419441811179324996912037079836828880582, 1045431751894572903946538904828429715066363458501417034287905705055973934] = false :=
  by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma checkPair1 : dispatchN 3 (optimizeN 6) 55214405208618729467034520380839570690669382403384614339707185604607796 1332117931867639019780548853069657189553651376118466973095916591110823307 [221941235689046003970522323171767282998876794266510458948512754036236505, 635085915085975334765247761183074419441811179324996912037079836828880582, 1045431751894572903946538904828429715066363458501417034287905705055973934] = false :=
  by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma checkPair2 : dispatchN 3 (optimizeN 6) 55214405208618729467034520380839570690669382403384614339707185604607796 635085915085975334765247761183074419441811179324996912037079836828880582 [221941235689046003970522323171767282998876794266510458948512754036236505, 1332117931867639019780548853069657189553651376118466973095916591110823307, 1045431751894572903946538904828429715066363458501417034287905705055973934] = false :=
  by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma checkPair3 : dispatchN 3 (optimizeN 6) 55214405208618729467034520380839570690669382403384614339707185604607796 1045431751894572903946538904828429715066363458501417034287905705055973934 [221941235689046003970522323171767282998876794266510458948512754036236505, 1332117931867639019780548853069657189553651376118466973095916591110823307, 635085915085975334765247761183074419441811179324996912037079836828880582] = false :=
  by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma checkPair4 : dispatchN 3 (optimizeN 6) 221941235689046003970522323171767282998876794266510458948512754036236505 1332117931867639019780548853069657189553651376118466973095916591110823307 [55214405208618729467034520380839570690669382403384614339707185604607796, 635085915085975334765247761183074419441811179324996912037079836828880582, 1045431751894572903946538904828429715066363458501417034287905705055973934] = false :=
  by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma checkPair5 : dispatchN 3 (optimizeN 6) 221941235689046003970522323171767282998876794266510458948512754036236505 635085915085975334765247761183074419441811179324996912037079836828880582 [55214405208618729467034520380839570690669382403384614339707185604607796, 1332117931867639019780548853069657189553651376118466973095916591110823307, 1045431751894572903946538904828429715066363458501417034287905705055973934] = false :=
  by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma checkPair6 : dispatchN 3 (optimizeN 6) 221941235689046003970522323171767282998876794266510458948512754036236505 1045431751894572903946538904828429715066363458501417034287905705055973934 [55214405208618729467034520380839570690669382403384614339707185604607796, 1332117931867639019780548853069657189553651376118466973095916591110823307, 635085915085975334765247761183074419441811179324996912037079836828880582] = false :=
  by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma checkPair7 : dispatchN 3 (optimizeN 6) 1332117931867639019780548853069657189553651376118466973095916591110823307 635085915085975334765247761183074419441811179324996912037079836828880582 [55214405208618729467034520380839570690669382403384614339707185604607796, 221941235689046003970522323171767282998876794266510458948512754036236505, 1045431751894572903946538904828429715066363458501417034287905705055973934] = false :=
  by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma checkPair8 : dispatchN 3 (optimizeN 6) 1332117931867639019780548853069657189553651376118466973095916591110823307 1045431751894572903946538904828429715066363458501417034287905705055973934 [55214405208618729467034520380839570690669382403384614339707185604607796, 221941235689046003970522323171767282998876794266510458948512754036236505, 635085915085975334765247761183074419441811179324996912037079836828880582] = false :=
  by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma checkPair9 : dispatchN 3 (optimizeN 6) 635085915085975334765247761183074419441811179324996912037079836828880582 1045431751894572903946538904828429715066363458501417034287905705055973934 [55214405208618729467034520380839570690669382403384614339707185604607796, 221941235689046003970522323171767282998876794266510458948512754036236505, 1332117931867639019780548853069657189553651376118466973095916591110823307] = false :=
  by decide +kernel

set_option maxRecDepth 16000 in
lemma rejectN : searchN 7 rowsN = false := by
  have pairList : pairs rowsN =
    [(55214405208618729467034520380839570690669382403384614339707185604607796, 221941235689046003970522323171767282998876794266510458948512754036236505, [1332117931867639019780548853069657189553651376118466973095916591110823307, 635085915085975334765247761183074419441811179324996912037079836828880582, 1045431751894572903946538904828429715066363458501417034287905705055973934]),
     (55214405208618729467034520380839570690669382403384614339707185604607796, 1332117931867639019780548853069657189553651376118466973095916591110823307, [221941235689046003970522323171767282998876794266510458948512754036236505, 635085915085975334765247761183074419441811179324996912037079836828880582, 1045431751894572903946538904828429715066363458501417034287905705055973934]),
     (55214405208618729467034520380839570690669382403384614339707185604607796, 635085915085975334765247761183074419441811179324996912037079836828880582, [221941235689046003970522323171767282998876794266510458948512754036236505, 1332117931867639019780548853069657189553651376118466973095916591110823307, 1045431751894572903946538904828429715066363458501417034287905705055973934]),
     (55214405208618729467034520380839570690669382403384614339707185604607796, 1045431751894572903946538904828429715066363458501417034287905705055973934, [221941235689046003970522323171767282998876794266510458948512754036236505, 1332117931867639019780548853069657189553651376118466973095916591110823307, 635085915085975334765247761183074419441811179324996912037079836828880582]),
     (221941235689046003970522323171767282998876794266510458948512754036236505, 1332117931867639019780548853069657189553651376118466973095916591110823307, [55214405208618729467034520380839570690669382403384614339707185604607796, 635085915085975334765247761183074419441811179324996912037079836828880582, 1045431751894572903946538904828429715066363458501417034287905705055973934]),
     (221941235689046003970522323171767282998876794266510458948512754036236505, 635085915085975334765247761183074419441811179324996912037079836828880582, [55214405208618729467034520380839570690669382403384614339707185604607796, 1332117931867639019780548853069657189553651376118466973095916591110823307, 1045431751894572903946538904828429715066363458501417034287905705055973934]),
     (221941235689046003970522323171767282998876794266510458948512754036236505, 1045431751894572903946538904828429715066363458501417034287905705055973934, [55214405208618729467034520380839570690669382403384614339707185604607796, 1332117931867639019780548853069657189553651376118466973095916591110823307, 635085915085975334765247761183074419441811179324996912037079836828880582]),
     (1332117931867639019780548853069657189553651376118466973095916591110823307, 635085915085975334765247761183074419441811179324996912037079836828880582, [55214405208618729467034520380839570690669382403384614339707185604607796, 221941235689046003970522323171767282998876794266510458948512754036236505, 1045431751894572903946538904828429715066363458501417034287905705055973934]),
     (1332117931867639019780548853069657189553651376118466973095916591110823307, 1045431751894572903946538904828429715066363458501417034287905705055973934, [55214405208618729467034520380839570690669382403384614339707185604607796, 221941235689046003970522323171767282998876794266510458948512754036236505, 635085915085975334765247761183074419441811179324996912037079836828880582]),
     (635085915085975334765247761183074419441811179324996912037079836828880582, 1045431751894572903946538904828429715066363458501417034287905705055973934, [55214405208618729467034520380839570690669382403384614339707185604607796, 221941235689046003970522323171767282998876794266510458948512754036236505, 1332117931867639019780548853069657189553651376118466973095916591110823307])] := by decide
  have parts : (pairs rowsN).any (fun (a, b, r) => dispatchN 3 (optimizeN 6) a b r) = false := by
    rw [pairList]
    simp only [List.any_cons, List.any_nil, checkPair0, checkPair1, checkPair2, checkPair3, checkPair4, checkPair5, checkPair6, checkPair7, checkPair8, checkPair9, Bool.false_or]
  have root : optimizeN 7 3 rowsN = false := by
    rw [optimizeN, parts] <;> decide
  have full : rowsN.sublists.filter (fun ws => cutsN ws == maskN) = [rowsN] := by decide
  unfold searchN
  apply List.any_eq_false.mpr
  intro ws hw
  by_cases hc : (cutsN ws == maskN) = true
  · have kept : ws ∈ rowsN.sublists.filter (fun w => cutsN w == maskN) :=
      List.mem_filter.mpr ⟨hw, hc⟩
    rw [full] at kept
    obtain rfl := List.mem_singleton.mp kept
    rw [show 7 + 1 - rowsN.length = 3 by decide, root] <;> simp
  · have noCut : (cutsN ws == maskN) = false := by simpa using hc
    simp [noCut]

lemma reject : search 7 rows = false := by
  rw [← searchMap, show rows.map BitVec.toNat = rowsN by decide]
  exact rejectN

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma lower (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) :
    7 < binaryCost gs :=
  bound_from_search rows rfl (by decide) reject (by decide +kernel) gs o hg he

end Signed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity



abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool

lemma getD_snoc_eq {α : Type} (xs : List α) (x d : α) :
    (xs ++ [x]).getD xs.length d = x := by
  simp [List.getD_eq_getElem?_getD]

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

lemma rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]
namespace Restrict

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool


def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_initial (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, wiresFrom gs w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp [wiresFrom], rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    have : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [this, ht]; simp

lemma length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_initial gs w
  rw [ht]; simp [hl]

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_initial gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

lemma normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

lemma wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

lemma simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

lemma simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

lemma elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

lemma elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

lemma elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

lemma statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

lemma statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

lemma inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_initial r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

lemma initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

lemma inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

lemma ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp


open Signed (binaryCost isBinary)

lemma binaryCost_append (gs hs : List Gate) :
    binaryCost (gs ++ hs) = binaryCost gs + binaryCost hs := by
  simp [binaryCost]

lemma binaryCost_cons (g : Gate) (gs : List Gate) :
    binaryCost (g :: gs) = binaryCost [g] + binaryCost gs := by
  exact binaryCost_append [g] gs

lemma binaryCost_singleton (g : Gate) :
    binaryCost [g] = (if isBinary g then 1 else 0) := by
  cases h : isBinary g <;> simp [binaryCost, h]

lemma simplify_op (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, g.op = op := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; rfl)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg <;> (subst hg; rfl)
  · simp at hg
  · simp at hg

lemma step_cost (n : ℕ) (acc : List Stat × List Gate) (g : Gate) :
    binaryCost (elimStep n acc g).2 ≤ binaryCost acc.2 + binaryCost [g] := by
  let res := simplify g.op (n + acc.2.length) (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
  change binaryCost (acc.2 ++ res.1.toList) ≤ _
  rw [binaryCost_append]
  cases h : res.1 with
  | none => simp [binaryCost]
  | some old =>
    have hop := simplify_op g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) old (by change old ∈ res.1; simp [h])
    have hb : isBinary old = isBinary g := by unfold isBinary; rw [hop]
    change binaryCost acc.2 + binaryCost [old] ≤ _
    rw [binaryCost_singleton, binaryCost_singleton, hb]

lemma elim_cost (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) :
    binaryCost (elim n gs acc).2 ≤ binaryCost acc.2 + binaryCost gs := by
  induction gs generalizing acc with
  | nil => simp [elim, binaryCost]
  | cons g gs ih =>
    rw [elim_cons, binaryCost_cons]
    have h₁ := ih (elimStep n acc g)
    have h₂ := step_cost n acc g
    omega

def Stable (acc : List Stat × List Gate) (w v : List Bool) : Prop :=
  acc.1.length = w.length ∧ acc.1.length = v.length ∧
    ∀ i j, acc.1.getD i (Sum.inl false) = Sum.inr j → w.getD i false = v.getD i false

lemma stable_step (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g)
    (w v : List Bool) (h : Stable acc w v)
    (cost : binaryCost (elimStep n acc g).2 = binaryCost acc.2 + binaryCost [g]) :
    Stable (elimStep n acc g)
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]) := by
  let get := fun i => acc.1.getD i (Sum.inl false)
  let ins := g.inputs.map get
  let res := simplify g.op (n + acc.2.length) ins
  let wval := g.op.eval (g.inputs.map fun i => w.getD i false)
  let vval := g.op.eval (g.inputs.map fun i => v.getD i false)
  have live (j : ℕ) (hj : res.2 = Sum.inr j) : wval = vval := by
    have noConst : ∀ c, Sum.inl c ∉ ins := by
      intro c hc
      rcases hg.1.1 with ha | ho | hn
      · have gone := simplify_count g.op (n + acc.2.length) ins (Or.inl ha)
          (by simpa [ins] using hg.1.2) (fun he => by simpa [ins] using hg.2 he) ⟨c, hc⟩
        change res.1 = none at gone
        change binaryCost (acc.2 ++ res.1.toList) = _ at cost
        simp [gone, binaryCost, isBinary, ha] at cost
      · have gone := simplify_count g.op (n + acc.2.length) ins (Or.inr (Or.inl ho))
          (by simpa [ins] using hg.1.2) (fun he => by simpa [ins] using hg.2 he) ⟨c, hc⟩
        change res.1 = none at gone
        change binaryCost (acc.2 ++ res.1.toList) = _ at cost
        simp [gone, binaryCost, isBinary, ho] at cost
      · have hn' : g.op = GateOp.not := by simpa using hn
        have len : ins.length ≤ 1 := by simpa [ins] using hg.2 hn'
        rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩
        · simp at hc
        · simp at hc
          subst a
          simp [res, hn', simplify, simpNot] at hj
        · simp at len
    have same : g.inputs.map (fun i => w.getD i false) = g.inputs.map (fun i => v.getD i false) := by
      apply List.map_congr_left
      intro i hi
      cases e : get i with
      | inl c => exact (noConst c (List.mem_map.2 ⟨i, hi, e⟩)).elim
      | inr r => exact h.2.2 i r e
    exact congrArg (g.op.eval) same
  refine ⟨by simp [elimStep, h.1], by simp [elimStep, h.2.1], ?_⟩
  intro i j hj
  change (acc.1 ++ [res.2]).getD i (Sum.inl false) = Sum.inr j at hj
  change (w ++ [wval]).getD i false = (v ++ [vval]).getD i false
  by_cases e : i = acc.1.length
  · subst i
    rw [getD_snoc_eq] at hj
    rw [getD_snoc_len _ _ _ _ h.1.symm, getD_snoc_len _ _ _ _ h.2.1.symm]
    exact live j hj
  · rw [getD_snoc_ne _ _ _ _ e] at hj
    have ew : i ≠ w.length := fun hw => e (hw.trans h.1.symm)
    have ev : i ≠ v.length := fun hv => e (hv.trans h.2.1.symm)
    rw [getD_snoc_ne _ _ _ _ ew, getD_snoc_ne _ _ _ _ ev]
    exact h.2.2 i j hj

lemma stable_elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (w v : List Bool)
    (hok : ∀ g ∈ gs, NOk g) (h : Stable acc w v)
    (cost : binaryCost (elim n gs acc).2 = binaryCost acc.2 + binaryCost gs) :
    Stable (elim n gs acc) (wiresFrom gs w) (wiresFrom gs v) := by
  induction gs generalizing acc w v with
  | nil => exact h
  | cons g gs ih =>
    rw [elim_cons, binaryCost_cons] at cost
    have h₁ := elim_cost n gs (elimStep n acc g)
    have h₂ := step_cost n acc g
    have hstep : binaryCost (elimStep n acc g).2 = binaryCost acc.2 + binaryCost [g] := by omega
    rw [elim_cons, wiresFrom_cons, wiresFrom_cons]
    apply ih (elimStep n acc g) _ _ (fun g' hg' => hok g' (by simp [hg']))
    · exact stable_step n acc g (hok g (by simp)) w v h hstep
    · omega

lemma stable_init (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    Stable (initStats n b, []) (List.ofFn y ++ [b]) (List.ofFn y ++ [!b]) := by
  refine ⟨by simp [initStats], by simp [initStats], ?_⟩
  intro i j h
  by_cases eq : i = n
  · subst i
    change (initStats n b).getD n (Sum.inl false) = Sum.inr j at h
    rw [initStats_last] at h
    cases h
  · rw [getD_snoc_ne _ _ _ _ (by simpa using eq), getD_snoc_ne _ _ _ _ (by simpa using eq)]

lemma normalize_cost (gs : List Gate) :
    binaryCost (gs.map normGate) = binaryCost gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, binaryCost_cons (normGate g), binaryCost_cons g, ih]
    have equal : (normGate g).op = g.op := by cases h : g.op <;> simp [normGate, h]
    have hb : isBinary (normGate g) = isBinary g := by unfold isBinary; rw [equal]
    rw [binaryCost_singleton, binaryCost_singleton, hb]

lemma restrict_binary (n : ℕ) (gs : List Gate) (out : ℕ) (f : BFn (n + 1)) (b : Bool)
    (hok : ∀ g ∈ gs, Ok g)
    (hev : ∀ x : Fin (n + 1) → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) = f x)
    (hdep : ∃ y : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y (!b)))
    (hnc : ∃ y z : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc z b)) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', Ok g) ∧ binaryCost gs' < binaryCost gs ∧
      ∀ y : Fin n → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn y) = f (Fin.snoc y b) := by
  let norm := gs.map normGate
  have normOK : ∀ g ∈ norm, NOk g := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g' (hok g' hg')
  have normEval (x : Fin (n + 1) → Bool) :
      (wiresFrom norm (List.ofFn x)).getD out false = f x := by
    rw [show norm = gs.map normGate from rfl, wiresFrom_norm]
    exact hev x
  let start : List Stat × List Gate := (initStats n b, [])
  let acc := elim n norm start
  have atOut (y : Fin n → Bool) :
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD out (Sum.inl false)) =
        f (Fin.snoc y b) := by
    have h := inv_elim n (List.ofFn y) (by simp) norm _ _
      (fun g hg => (normOK g hg).1) (inv_init n b y)
    have e := (h.2 out).2
    change statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD out (Sum.inl false)) = _ at e
    rw [← ofFn_snoc] at e
    exact e.trans (normEval _)
  cases he : acc.1.getD out (Sum.inl false) with
  | inl c =>
    obtain ⟨y, z, hne⟩ := hnc
    exact (hne (by rw [← atOut y, ← atOut z, he]; rfl)).elim
  | inr j =>
    have hle : binaryCost acc.2 ≤ binaryCost gs := by
      have h := elim_cost n norm start
      change binaryCost acc.2 ≤ binaryCost start.2 + binaryCost norm at h
      rw [show binaryCost start.2 = 0 from rfl, zero_add,
        show norm = gs.map normGate from rfl, normalize_cost] at h
      exact h
    have hlt : binaryCost acc.2 < binaryCost gs := by
      by_contra! hge
      have e : binaryCost (elim n norm start).2 = binaryCost start.2 + binaryCost norm := by
        change binaryCost acc.2 = _
        rw [show norm = gs.map normGate from rfl, normalize_cost]
        have z : binaryCost start.2 = 0 := rfl
        omega
      obtain ⟨y, hy⟩ := hdep
      apply hy
      have hstable := stable_elim n norm start (List.ofFn y ++ [b]) (List.ofFn y ++ [!b])
        normOK (stable_init n y b) e
      have e' := hstable.2.2 out j he
      rw [← ofFn_snoc, ← ofFn_snoc, normEval, normEval] at e'
      exact e'
    refine ⟨acc.2, j, elim_ok n norm start (by simp [start]), hlt, ?_⟩
    intro y
    have e := atOut y
    rw [he] at e
    exact e

end Restrict

open Signed (binaryCost isBinary)
open Restrict (binaryCost_cons)

lemma relabel_cost {n m : ℕ} (π : Fin n → Fin m) (gs : List Gate) :
    binaryCost (gs.map (relGate n m π)) = binaryCost gs := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    rw [List.map_cons, binaryCost_cons (relGate n m π g), binaryCost_cons g, ih]
    rw [Restrict.binaryCost_singleton, Restrict.binaryCost_singleton]
    rfl



def target6 (x : Fin 6 → Bool) : Bool := Nat.testBit 18368754515637234920 (tableIndex x)

def order : Fin 6 → Fin 6 := ![0, 1, 2, 3, 4, 5]

set_option maxRecDepth 12000 in
set_option maxHeartbeats 0 in
lemma binaryLower (gs : List Gate) (o : ℕ) (fits : ∀ g ∈ gs, Restrict.Ok g)
    (computes : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = target6 x) :
    9 ≤ Signed.binaryCost gs := by
  let f : BFn 6 := fun x => target6 (x ∘ order)
  let C := relabel 6 6 order ⟨gs, o⟩
  have ok : ∀ g ∈ C.gates, Restrict.Ok g := by
    intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.1 hg
    have h := fits g' hg'
    exact ⟨h.1, by simpa [relGate] using h.2⟩
  have hv : ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = f x := by
    intro x
    change C.eval (List.ofFn x) = target6 (x ∘ order)
    rw [← computes (x ∘ order)]
    exact (rel_fold 6 6 order gs _ _ (rel_init 6 6 order x)).2.2 o
  have dep : ∃ y : Fin 5 → Bool, f (Fin.snoc y true) ≠ f (Fin.snoc y (!true)) :=
    ⟨fun i => (17 : ℕ).testBit i.val, by decide +kernel⟩
  have varies : ∃ y z : Fin 5 → Bool, f (Fin.snoc y true) ≠ f (Fin.snoc z true) :=
    ⟨fun i => (0 : ℕ).testBit i.val, fun i => (3 : ℕ).testBit i.val, by decide +kernel⟩
  obtain ⟨new, out, legal, cost, eval⟩ := Restrict.restrict_binary 5 C.gates C.output f true ok hv dep varies
  have eq : ∀ x : Fin 5 → Bool, f (Fin.snoc x true) =
      Nat.testBit 4276808936 (tableIndex x) := by decide +kernel
  have cut := Signed.lower new out legal (fun x => (eval x).trans (eq x))
  have same : Signed.binaryCost C.gates = Signed.binaryCost gs := relabel_cost order gs
  omega

def witness : Circuit := ⟨[⟨.or, [0, 2]⟩, ⟨.and, [3, 4]⟩,
  ⟨.or, [1, 7]⟩, ⟨.and, [6, 8]⟩, ⟨.and, [4, 5]⟩,
  ⟨.or, [2, 10]⟩, ⟨.and, [0, 11]⟩, ⟨.and, [1, 3]⟩,
  ⟨.or, [9, 12]⟩, ⟨.or, [14, 13]⟩], 15⟩

lemma witnessCorrect : ∀ x : Fin 6 → Bool,
    witness.eval (List.ofFn x) = target6 x := by decide +kernel

lemma positive : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4276677864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4276677864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s ⟨C, legal, size, computes⟩
  by_cases present : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g, mem, op⟩ := present
    have cheaper : Signed.binaryCost C.gates < C.size :=
      List.length_filter_lt_length_iff_exists.mpr ⟨g, mem, by simp [Signed.isBinary, op]⟩
    have lower := binaryLower C.gates C.output legal computes
    refine ⟨witness, by simp [Monotone2, witness], ?_, witnessCorrect⟩
    change 10 ≤ s
    omega
  · refine ⟨C, ?_, size, computes⟩
    intro g mem
    obtain ⟨op, cap⟩ := legal g mem
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr (fun eq => (present ⟨g, mem, eq⟩).elim)), cap⟩

end PEqualNP.Outside.L_meta_16664

theorem PEqualNP.Outside.L_meta_16664 : ¬ (¬ (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4276808936 * 2 ^ 32 + 4276677864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4276808936 * 2 ^ 32 + 4276677864) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) := by
  intro h
  exact h PEqualNP.Outside.L_meta_16664.positive
