import PEqualNP.Defs

-- Signed search and binary gate elimination adapted from L-meta-11641.
-- Deleting vertex six gives the six-input graph checked below.
namespace PEqualNP.Outside.L_meta_10760_aux.Signed


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

abbrev W := BitVec 1400

def ops (x y : W) : List W := [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]
def sep (x : W) : BitVec 700 := ((x >>> 700) ^^^ x).setWidth 700
def cuts (ws : List W) : BitVec 700 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := (-1 : BitVec 700) ++ (0 : BitVec 700)
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

def differs (i : Fin 700) (w : W) : Prop :=
  w.getLsbD (700+i.val) ≠ w.getLsbD i.val

set_option maxRecDepth 100000 in
lemma ops_differs (i : Fin 700) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  by_contra! fail
  obtain ⟨ha,hb⟩ := fail
  apply hd
  unfold differs at ha hb
  simp only [not_not] at ha hb
  have hi : 700+i.val < 1400 := by omega
  have hi' : i.val < 1400 := by omega
  rcases hz with rfl | rfl | rfl | rfl <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, hi, hi', decide_true,
      Bool.true_and, ha, hb]

set_option maxRecDepth 100000 in
lemma cuts_spec (ws : List W) (i : Fin 700) :
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
  change (cuts ws)[j] = (BitVec.allOnes 700)[j]
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
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

set_option maxRecDepth 100000 in
lemma dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
    (next : ℕ → List W → Bool)
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
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
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hg hl)
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
  · change reachable av (BitVec.allOnes 1400 &&& y)
    rw [BitVec.allOnes_and]; exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : W) = 0 from BitVec.and_zero]; exact .inl const
  · change reachable av (x &&& BitVec.allOnes 1400)
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

private def bit (k : Fin 1400) (z : W) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

set_option maxRecDepth 100000 in
private lemma read_bit (w : List W) (i : ℕ) (k : Fin 1400) :
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
lemma action_spec (w : List W) (g : Gate) (hg : legal g) (k : Fin 1400) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> simp at cap
  all_goals have bit0 : (0 : W)[k.val] = false := by change (0#1400)[k.val] = false; simp
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

def F (x : Fin 6 → Bool) : Bool := (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) || (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5)

lemma bound_from_search (inputs : List W) (width : inputs.length = 6)
    (nd : inputs.Nodup) (reject : search 8 inputs = false)
    (sample : ∀ k : Fin 1400, F (fun i => (inputs.getD i.val 0)[k.val]) = (~~~goal)[k.val])
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) :
    8 < binaryCost gs := by
  by_contra! low
  have init : ∀ u ∈ inputs, holds inputs.toFinset u := by
    intro u hu
    exact .inr (.inr ⟨u, List.mem_toFinset.mpr hu, .inl rfl⟩)
  have evaluate (k : Fin 1400) :
      (gs.foldl step (inputs.map (bit k))).getD o false = bit k (~~~goal) := by
    let x (i : Fin 6) : Bool := bit k (inputs.getD i.val 0)
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
  exact Bool.noConfusion (reject.symm.trans (search_complete ht 8 inputs nd (lift low run)))

def packWords (xs : List ℕ) : ℕ := xs.foldl (fun acc x => acc * 2 ^ 64 + x) 0

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def input0 : W := BitVec.ofNat 1400
  (show {n : ℕ // n = packWords [0x22808a022808a, 0x22808a022808a02, 0x2808a022808a0228, 0x8a022808a022808, 0xa022808a022808a0, 0x22808a022808a022, 0x808a022808a02280, 0x8a022808a022808a, 0x22808a022808a02, 0x2808a022808a0228, 0x8a022808a022808, 0xafffc000fffc000f, 0xffc000fffc000fff, 0xc000fffc000fffc0, 0xfffffff0003fff, 0x3fff0003fff00, 0x3fff0003ffffffc, 0xfffffff0003ff, 0xf0003fff0003ffff, 0xffc000fffc000fff, 0xc000fffffff0003f, 0xfffffc000fffffff]} from ⟨_, by norm_num [packWords]; rfl⟩).val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def input1 : W := BitVec.ofNat 1400
  (show {n : ℕ // n = packWords [0xb002c00b002c, 0xb002c00b002c00, 0xb002c00b002c00b0, 0x2c00b002c00b002, 0xc00b002c00b002c0, 0xb002c00b002c00b, 0x2c00b002c00b00, 0x2c00b002c00b002c, 0xb002c00b002c00, 0xb002c00b002c00b0, 0x2c00b002c00b002, 0xcfffffff0000000f, 0xffffff0000000fff, 0xffff0000000fffff, 0xff0003ffffffc000, 0x3ffffffc00000, 0x3ffffffc000ffff, 0xfff0003ffffffc00, 0x3ffffffc000f, 0xffffff0000000fff, 0xffff0003ffffffc0, 0xffffffffffc000]} from ⟨_, by norm_num [packWords]; rfl⟩).val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def input2 : W := BitVec.ofNat 1400
  (show {n : ℕ // n = packWords [0x44c113044c1130, 0x44c113044c113044, 0xc113044c113044c1, 0x13044c113044c113, 0x44c113044c11304, 0x4c113044c113044c, 0x113044c113044c11, 0x3044c113044c1130, 0x44c113044c113044, 0xc113044c113044c1, 0x13044c113044c113, 0xffffffffffffff0, 0xfff, 0xfffffffffff00000, 0x3ffffffffff, 0xfffc000000000000, 0x3ffffffffff0000, 0x3fffffffff, 0xffffc0000000000f, 0xfffffffffffff000, 0x3ffffffff, 0xff0000000fffffff]} from ⟨_, by norm_num [packWords]; rfl⟩).val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def input3 : W := BitVec.ofNat 1400
  (show {n : ℕ // n = packWords [0x17005c017005c0, 0x17005c017005c017, 0x5c017005c01700, 0x5c017005c017005c, 0x17005c017005c01, 0x7005c017005c0170, 0x5c017005c017005, 0xc017005c017005c0, 0x17005c017005c017, 0x5c017005c01700, 0x5c017005c017005c, 0xfffffffffffffff, 0xfffffffffffff000, 0x0, 0x3ffffffffff, 0xffffffffffffffff, 0xfc00000000000000, 0x3fffffffff, 0xfffffffffffffff0, 0x0, 0x3ffffffff, 0xfffffffff0000000]} from ⟨_, by norm_num [packWords]; rfl⟩).val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def input4 : W := BitVec.ofNat 1400
  (show {n : ℕ // n = packWords [0x98026009802600, 0x9802600980260098, 0x260098026009802, 0x6009802600980260, 0x980260098026009, 0x8026009802600980, 0x2600980260098026, 0x98026009802600, 0x9802600980260098, 0x260098026009802, 0x6009802600980260, 0xfffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xfffffc0000000000, 0x0, 0x0, 0x3fffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xfffffffc00000000, 0x0]} from ⟨_, by norm_num [packWords]; rfl⟩).val
set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
def input5 : W := BitVec.ofNat 1400
  (show {n : ℕ // n = packWords [0xe003800e003800, 0xe003800e003800e0, 0x3800e003800e003, 0x800e003800e00380, 0xe003800e003800e, 0x3800e003800e00, 0x3800e003800e0038, 0xe003800e003800, 0xe003800e003800e0, 0x3800e003800e003, 0x800e003800e00380, 0xfffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffffffffffff, 0xffffffc000000000, 0x0, 0x0, 0x0, 0x0]} from ⟨_, by norm_num [packWords]; rfl⟩).val

def rows : List W := [input0, input1, input2, input3, input4, input5]

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma first0_1 : dispatch 3 (optimized 7) input0 input1 [input2, input3, input4, input5] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma first0_2 : dispatch 3 (optimized 7) input0 input2 [input1, input3, input4, input5] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma first0_3 : dispatch 3 (optimized 7) input0 input3 [input1, input2, input4, input5] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma first0_4 : dispatch 3 (optimized 7) input0 input4 [input1, input2, input3, input5] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma first0_5 : dispatch 3 (optimized 7) input0 input5 [input1, input2, input3, input4] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma first1_2 : dispatch 3 (optimized 7) input1 input2 [input0, input3, input4, input5] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma first1_3 : dispatch 3 (optimized 7) input1 input3 [input0, input2, input4, input5] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma first1_4 : dispatch 3 (optimized 7) input1 input4 [input0, input2, input3, input5] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma first1_5 : dispatch 3 (optimized 7) input1 input5 [input0, input2, input3, input4] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma first2_3 : dispatch 3 (optimized 7) input2 input3 [input0, input1, input4, input5] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma first2_4 : dispatch 3 (optimized 7) input2 input4 [input0, input1, input3, input5] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma first2_5 : dispatch 3 (optimized 7) input2 input5 [input0, input1, input3, input4] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma first3_4 : dispatch 3 (optimized 7) input3 input4 [input0, input1, input2, input5] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma first3_5 : dispatch 3 (optimized 7) input3 input5 [input0, input1, input2, input4] = false := by decide +kernel

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma first4_5 : dispatch 3 (optimized 7) input4 input5 [input0, input1, input2, input3] = false := by decide +kernel

lemma starts : ∀ t ∈ pairs rows, dispatch 3 (optimized 7) t.1 t.2.1 t.2.2 = false := by
  intro t h
  change t ∈ [(input0, input1, [input2, input3, input4, input5]), (input0, input2, [input1, input3, input4, input5]), (input0, input3, [input1, input2, input4, input5]), (input0, input4, [input1, input2, input3, input5]), (input0, input5, [input1, input2, input3, input4]), (input1, input2, [input0, input3, input4, input5]), (input1, input3, [input0, input2, input4, input5]), (input1, input4, [input0, input2, input3, input5]), (input1, input5, [input0, input2, input3, input4]), (input2, input3, [input0, input1, input4, input5]), (input2, input4, [input0, input1, input3, input5]), (input2, input5, [input0, input1, input3, input4]), (input3, input4, [input0, input1, input2, input5]), (input3, input5, [input0, input1, input2, input4]), (input4, input5, [input0, input1, input2, input3])] at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact first0_1
  · exact first0_2
  · exact first0_3
  · exact first0_4
  · exact first0_5
  · exact first1_2
  · exact first1_3
  · exact first1_4
  · exact first1_5
  · exact first2_3
  · exact first2_4
  · exact first2_5
  · exact first3_4
  · exact first3_5
  · exact first4_5

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma reject : search 8 rows = false := by
  have prior : rows.sublists.all (fun w => w == rows || cuts w != -1) = true := by decide +kernel
  have allRows : optimized 8 3 rows = false := by
    change (false || (pairs rows).any _) = false
    rw [Bool.false_or]
    exact List.any_eq_false.mpr (fun t ht => by simp [starts t ht])
  unfold search
  apply List.any_eq_false.mpr
  intro w hw
  by_cases eq : w = rows
  · subst w
    change ¬ ((true && true && optimized 8 3 rows) = true)
    simp [allRows]
  · have h := List.all_eq_true.mp prior w hw
    simp [eq] at h
    simp [h]

set_option maxRecDepth 8000 in
lemma bound (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 6 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = F x) : 8 < binaryCost gs :=
  bound_from_search rows rfl (by decide) reject (by decide +kernel) gs o hg he

end PEqualNP.Outside.L_meta_10760_aux.Signed

namespace PEqualNP.Outside.L_meta_10760_aux

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_10760_aux.Signed (legal isBinary binaryCost)


def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

lemma wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

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

lemma simplify_legal (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1.toList, legal g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg; exact ⟨Or.inl rfl, by simp⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg; exact ⟨Or.inr (Or.inl rfl), by simp⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg; exact ⟨Or.inr (Or.inr rfl), by simp⟩
  · simp at hg
  · simp at hg

lemma isBinary_and (l : List ℕ) : isBinary ⟨GateOp.and, l⟩ = true := rfl
lemma isBinary_or (l : List ℕ) : isBinary ⟨GateOp.or, l⟩ = true := rfl
lemma isBinary_not (l : List ℕ) : isBinary ⟨GateOp.not, l⟩ = false := rfl

lemma simplify_binCost_le (op : GateOp) (m : ℕ) (ins : List Stat) :
    binaryCost (simplify op m ins).1.toList ≤ if isBinary ⟨op, []⟩ then 1 else 0 := by
  have hlen : ∀ o : Option Gate, binaryCost o.toList ≤ 1 := by
    intro o
    cases o with
    | none => simp [binaryCost]
    | some g => exact (List.length_filter_le _ _).trans (by simp)
  cases op
  · exact hlen _
  · exact hlen _
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simplify, simpNot, binaryCost, isBinary_not]
  · simp [simplify, binaryCost]
  · simp [simplify, binaryCost]

lemma simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · rcases a with c | j <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · rcases a with c | j <;> rcases b with d | k <;> (try cases c) <;> (try cases d) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · rcases a with c | j <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · rcases a with c | j <;> rcases b with d | k <;> (try cases c) <;> (try cases d) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · rcases a with c | j <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

lemma elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

lemma binaryCost_append (l1 l2 : List Gate) :
    binaryCost (l1 ++ l2) = binaryCost l1 + binaryCost l2 := by
  simp [binaryCost, List.filter_append]

lemma binaryCost_cons (g : Gate) (gs : List Gate) :
    binaryCost (g :: gs) = (if isBinary g then 1 else 0) + binaryCost gs := by
  simp only [binaryCost, List.filter_cons]
  cases isBinary g <;> simp [Nat.add_comm]

lemma elim_legal (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, legal g) → (∀ g ∈ (elim n gs acc).2, legal g) := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih
    intro g' hg'
    simp only [elimStep, List.mem_append] at hg'
    rcases hg' with hg' | hg'
    · exact h g' hg'
    · exact simplify_legal _ _ _ g' hg'

lemma elim_binCost_le (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    binaryCost (elim n gs acc).2 ≤ binaryCost acc.2 + binaryCost gs := by
  induction gs with
  | nil => intro acc; simp [elim, binaryCost]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : binaryCost (elimStep n acc g).2 ≤ binaryCost acc.2 + (if isBinary g then 1 else 0) := by
      simp only [elimStep, binaryCost_append]
      have hb := simplify_binCost_le g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
      have heq : isBinary ⟨g.op, []⟩ = isBinary g := rfl
      rw [heq] at hb
      omega
    rw [elim_cons, binaryCost_cons]
    omega

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
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, legal g) → Inv n y w acc →
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
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
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

def AgreeNonConst (st : List Stat) (w1 w2 : List Bool) : Prop :=
  st.length = w1.length ∧ st.length = w2.length ∧
  ∀ i : ℕ, (∃ j : ℕ, st.getD i (Sum.inl false) = Sum.inr j) → w1.getD i false = w2.getD i false

lemma elim_agree_of_eq_binCost (n : ℕ) (gs : List Gate) :
    ∀ (w1 w2 : List Bool) (acc : List Stat × List Gate),
      (∀ g ∈ gs, legal g) →
      AgreeNonConst acc.1 w1 w2 →
      binaryCost (elim n gs acc).2 = binaryCost acc.2 + binaryCost gs →
      AgreeNonConst (elim n gs acc).1 (wiresFrom gs w1) (wiresFrom gs w2) := by
  induction gs with
  | nil => intro w1 w2 acc _ hag _; exact hag
  | cons g gs ih =>
    intro w1 w2 acc hok hag heq
    have hstep_le : binaryCost (elimStep n acc g).2 ≤ binaryCost acc.2 + (if isBinary g then 1 else 0) := by
      simp only [elimStep, binaryCost_append]
      have hb := simplify_binCost_le g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
      have heq' : isBinary ⟨g.op, []⟩ = isBinary g := rfl
      rw [heq'] at hb; omega
    have htail_le := elim_binCost_le n gs (elimStep n acc g)
    rw [elim_cons, binaryCost_cons] at heq
    have hstep_eq : binaryCost (elimStep n acc g).2 = binaryCost acc.2 + (if isBinary g then 1 else 0) := by omega
    have htail_eq : binaryCost (elim n gs (elimStep n acc g)).2 = binaryCost (elimStep n acc g).2 + binaryCost gs := by omega
    apply ih (w1 ++ [g.op.eval (g.inputs.map fun i => w1.getD i false)])
             (w2 ++ [g.op.eval (g.inputs.map fun i => w2.getD i false)])
             (elimStep n acc g)
             (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) _ htail_eq
    obtain ⟨hl1, hl2, hwi⟩ := hag
    refine ⟨by simp [elimStep, hl1], by simp [elimStep, hl2], ?_⟩
    intro i hi
    by_cases hil : i = acc.1.length
    · subst hil
      simp only [elimStep] at hi ⊢
      rw [getD_snoc_eq] at hi
      rw [hl1, getD_snoc_eq, ← hl1, hl2, getD_snoc_eq]
      have hgok := hok g List.mem_cons_self
      obtain ⟨op, args⟩ := g
      obtain ⟨hop, hlen⟩ := hgok
      dsimp only [elimStep] at hi hstep_eq
      rw [binaryCost_append] at hstep_eq
      rcases hop with rfl | rfl | rfl
      · rw [isBinary_and] at hstep_eq
        rcases args with _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, l⟩⟩⟩
        · simp [simplify, simpAnd, binaryCost] at hstep_eq
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rw [List.map_cons, List.map_nil, h1] at hstep_eq
            simp [simplify, simpAnd, binaryCost] at hstep_eq
          · rw [List.map_cons, List.map_nil, h1] at hstep_eq
            simp [simplify, simpAnd, binaryCost] at hstep_eq
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rcases h2 : acc.1.getD k2 (Sum.inl false) with d | b <;>
              (rw [List.map_cons, List.map_cons, List.map_nil, h1, h2] at hstep_eq;
               simp [simplify, simpAnd, binaryCost] at hstep_eq)
          · rcases h2 : acc.1.getD k2 (Sum.inl false) with d | b
            · rw [List.map_cons, List.map_cons, List.map_nil, h1, h2] at hstep_eq
              simp [simplify, simpAnd, binaryCost] at hstep_eq
            · have e1 := hwi k1 ⟨a, h1⟩
              have e2 := hwi k2 ⟨b, h2⟩
              simp [GateOp.eval, List.getD_eq_getElem?_getD] at e1 e2 ⊢
              rw [e1, e2]
        · simp at hlen
      · rw [isBinary_or] at hstep_eq
        rcases args with _ | ⟨k1, _ | ⟨k2, _ | ⟨k3, l⟩⟩⟩
        · simp [simplify, simpOr, binaryCost] at hstep_eq
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rw [List.map_cons, List.map_nil, h1] at hstep_eq
            simp [simplify, simpOr, binaryCost] at hstep_eq
          · rw [List.map_cons, List.map_nil, h1] at hstep_eq
            simp [simplify, simpOr, binaryCost] at hstep_eq
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rcases h2 : acc.1.getD k2 (Sum.inl false) with d | b <;>
              (rw [List.map_cons, List.map_cons, List.map_nil, h1, h2] at hstep_eq;
               simp [simplify, simpOr, binaryCost] at hstep_eq)
          · rcases h2 : acc.1.getD k2 (Sum.inl false) with d | b
            · rw [List.map_cons, List.map_cons, List.map_nil, h1, h2] at hstep_eq
              simp [simplify, simpOr, binaryCost] at hstep_eq
            · have e1 := hwi k1 ⟨a, h1⟩
              have e2 := hwi k2 ⟨b, h2⟩
              simp [GateOp.eval, List.getD_eq_getElem?_getD] at e1 e2 ⊢
              rw [e1, e2]
        · simp at hlen
      · rcases args with _ | ⟨k1, l⟩
        · simp [simplify, simpNot] at hi
        · rcases h1 : acc.1.getD k1 (Sum.inl false) with c | a
          · rw [List.map_cons, h1] at hi
            simp [simplify, simpNot] at hi
          · have e1 := hwi k1 ⟨a, h1⟩
            simp [GateOp.eval, List.getD_eq_getElem?_getD] at e1 ⊢
            rw [e1]
    · simp only [elimStep] at hi ⊢
      rw [getD_snoc_ne _ _ _ _ hil] at hi
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact hwi i hi

def insAt {α : Type} {n : ℕ} (idx : Fin (n + 1)) (v : α) (y : Fin n → α) (k : Fin (n + 1)) : α :=
  if h1 : k.val < idx.val then y ⟨k.val, by omega⟩
  else if h2 : k.val = idx.val then v
  else y ⟨k.val - 1, by omega⟩

lemma drop_one_var {n : ℕ} (idx : Fin (n + 1)) (F : (Fin (n + 1) → Bool) → Bool)
    (y_diff y0 y1 : Fin n → Bool)
    (hdiff : F (insAt idx false y_diff) ≠ F (insAt idx true y_diff))
    (hnc : F (insAt idx false y0) ≠ F (insAt idx false y1))
    (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin (n + 1) → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = F x) :
    ∃ (gs' : List Gate) (o' : ℕ), (∀ g ∈ gs', legal g) ∧ binaryCost gs' < binaryCost gs ∧
      ∀ y : Fin n → Bool, Circuit.eval ⟨gs', o'⟩ (List.ofFn y) = F (insAt idx false y) := by
  let initFn : Fin (n + 1) → Stat := insAt idx (Sum.inl false) (fun i : Fin n => Sum.inr i.val)
  let initSt : List Stat := List.ofFn initFn
  let res := elim n gs (initSt, [])
  have hgetFn : ∀ {α : Type} (f : Fin (n + 1) → α) (d : α) (i : ℕ) (hi : i < n + 1),
      (List.ofFn f).getD i d = f ⟨i, hi⟩ := by
    intro α f d i hi
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp [hi]), Option.getD_some,
      List.getElem_ofFn]
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (List.ofFn (insAt idx false y)) (initSt, []) := by
    intro y
    refine ⟨by simp [initSt], ?_⟩
    intro i
    by_cases hi : i < n + 1
    · rw [show initSt.getD i (Sum.inl false) = initFn ⟨i, hi⟩ from hgetFn initFn _ i hi,
          hgetFn (insAt idx false y) false i hi]
      dsimp only [initFn, insAt]
      by_cases h1 : i < idx.val
      · simp only [h1, ↓reduceDIte, statValid, statVal, wiresFrom, List.foldl_nil, List.length_nil, Nat.add_zero]
        refine ⟨by omega, ?_⟩
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega),
          Option.getD_some, List.getElem_ofFn]
      · by_cases h2 : i = idx.val
        · simp [h2, statValid, statVal]
        · simp only [h1, h2, ↓reduceDIte, statValid, statVal, wiresFrom, List.foldl_nil, List.length_nil, Nat.add_zero]
          refine ⟨by omega, ?_⟩
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by simp; omega),
            Option.getD_some, List.getElem_ofFn]
    · have h1 : initSt.getD i (Sum.inl false) = Sum.inl false :=
        List.getD_eq_default _ _ (by simp [initSt]; omega)
      have h2 : (List.ofFn (insAt idx false y)).getD i false = false :=
        List.getD_eq_default _ _ (by simp; omega)
      rw [h1, h2]; simp [statValid, statVal]
  have heval : ∀ y : Fin n → Bool,
      statVal (wiresFrom res.2 (List.ofFn y)) (res.1.getD o (Sum.inl false)) =
        F (insAt idx false y) := by
    intro y
    have hi := inv_elim n (List.ofFn y) (by simp) gs (List.ofFn (insAt idx false y)) (initSt, []) hg (hinv y)
    have h2 := (hi.2 o).2
    have h3 : (wiresFrom gs (List.ofFn (insAt idx false y))).getD o false =
        F (insAt idx false y) := he (insAt idx false y)
    exact h2.trans h3
  have hout_inr : ∃ o', res.1.getD o (Sum.inl false) = Sum.inr o' := by
    cases hst : res.1.getD o (Sum.inl false) with
    | inl c =>
      have e0 := heval y0; rw [hst] at e0
      have e1 := heval y1; rw [hst] at e1
      exact (hnc (e0.symm.trans e1)).elim
    | inr o' => exact ⟨o', rfl⟩
  obtain ⟨o', ho'⟩ := hout_inr
  have hlt : binaryCost res.2 < binaryCost gs := by
    have hle : binaryCost res.2 ≤ binaryCost ([] : List Gate) + binaryCost gs :=
      elim_binCost_le n gs (initSt, [])
    have h0 : binaryCost ([] : List Gate) = 0 := rfl
    by_contra hnot
    have heq : binaryCost res.2 = binaryCost ([] : List Gate) + binaryCost gs := by omega
    have hag0 : AgreeNonConst initSt
        (List.ofFn (insAt idx false y_diff)) (List.ofFn (insAt idx true y_diff)) := by
      refine ⟨by simp [initSt], by simp [initSt], ?_⟩
      intro i ⟨j, hj⟩
      by_cases hi : i < n + 1
      · rw [show initSt.getD i (Sum.inl false) = initFn ⟨i, hi⟩ from hgetFn initFn _ i hi] at hj
        rw [hgetFn (insAt idx false y_diff) false i hi, hgetFn (insAt idx true y_diff) false i hi]
        dsimp only [initFn, insAt] at hj ⊢
        by_cases h1 : i < idx.val
        · simp [h1]
        · by_cases h2 : i = idx.val
          · simp [h2] at hj
          · simp [h1, h2]
      · rw [List.getD_eq_default _ _ (by simp [initSt]; omega)] at hj
        cases hj
    have hag := elim_agree_of_eq_binCost n gs
      (List.ofFn (insAt idx false y_diff)) (List.ofFn (insAt idx true y_diff))
      (initSt, []) hg hag0 heq
    have hsame := hag.2.2 o ⟨o', ho'⟩
    have hf0 : (wiresFrom gs (List.ofFn (insAt idx false y_diff))).getD o false =
        F (insAt idx false y_diff) := he _
    have hf1 : (wiresFrom gs (List.ofFn (insAt idx true y_diff))).getD o false =
        F (insAt idx true y_diff) := he _
    exact hdiff (hf0.symm.trans (hsame.trans hf1))
  refine ⟨res.2, o', elim_legal n gs (initSt, []) (by simp), hlt, ?_⟩
  intro y
  have h := heval y
  rw [ho'] at h
  exact h

def target (x : Fin 7 → Bool) : Bool :=
  (x 0 && x 2) || (x 1 && x 3) || (x 0 && x 4) || (x 1 && x 4) ||
  (x 2 && x 4) || (x 0 && x 5) || (x 1 && x 5) || (x 3 && x 5) ||
  (x 0 && x 6) || (x 2 && x 6) || (x 3 && x 6) || (x 5 && x 6)

set_option maxRecDepth 16000 in
set_option maxHeartbeats 0 in
lemma lower_binary (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = target x) :
    10 ≤ binaryCost gs := by
  obtain ⟨rs, u, ok, lt, ev⟩ := drop_one_var (6 : Fin 7) target
    (fun i => decide (i = 0)) (fun _ => false) (fun _ => true)
    (by decide +kernel) (by decide +kernel) gs o hg he
  have restricts : ∀ y : Fin 6 → Bool, target (insAt (6 : Fin 7) false y) = Signed.F y :=
    by decide +kernel
  have low := Signed.bound rs u ok (fun y => (ev y).trans (restricts y))
  omega

lemma lower_with_not (gs : List Gate) (o : ℕ) (hg : ∀ g ∈ gs, legal g)
    (he : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = target x)
    (hn : ∃ g ∈ gs, g.op = GateOp.not) : 11 ≤ gs.length := by
  obtain ⟨g, hmem, hop⟩ := hn
  have hc : binaryCost gs < gs.length :=
    (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
      ⟨g, hmem, by simp [isBinary, hop]⟩
  have hb := lower_binary gs o hg he
  omega

end PEqualNP.Outside.L_meta_10760_aux
