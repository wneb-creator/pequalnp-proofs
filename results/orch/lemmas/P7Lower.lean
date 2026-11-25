import PEqualNP.Defs

-- The live-set search and its completeness proof are adapted from
-- lean/PEqualNP/Outside/L_meta_6345.lean in this repository, widened from 64 to 36
-- (true entry, false entry) pairs; the rows, the 10-gate search and the conclusion are new.

namespace PEqualNP.Outside.L_meta_9502.P7Lower

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

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == BitVec.allOnes 72 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 72) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 72) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private theorem read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) : possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inl rfl⟩

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using atom hy
  rcases hy with rfl | hy
  · simpa [possible] using atom (.inr hx)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 2000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws :=
    (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨BitVec.allOnes 72, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, atom (mem i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩

def represents (available : Finset W) (w : List W) : Prop :=
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 72 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 72 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 72 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 72 ∨ t ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ t ∈ basicOps a b :=
    h.imp_right (Or.imp_right Or.inl)
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x, hx, h | ⟨y, hy, h | h⟩⟩)
  · exact .inl h
  · exact .inr (.inl h)
  · subst z; exact lift (hw _ hx)
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · left; simp
    · rw [BitVec.allOnes_and]; exact lift (hw _ hy)
    rcases hw _ hy with rfl | rfl | hv
    · left; simp
    · rw [BitVec.and_allOnes]; exact .inr (.inr (.inl hu))
    by_cases h : x = y
    · subst h; rw [BitVec.and_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [show (0 : W) ||| y = y by ext i hi; simp]; exact lift (hw _ hy)
    · right; left; exact BitVec.allOnes_or
    rcases hw _ hy with rfl | rfl | hv
    · rw [show x ||| (0 : W) = x by ext i hi; simp]; exact .inr (.inr (.inl hu))
    · right; left; exact BitVec.or_allOnes
    by_cases h : x = y
    · subst h; rw [BitVec.or_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x, hu, y, hv, h, by simp [basicOps, ops]⟩))

private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i, hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim ((by decide : goal ≠ (0 : W)) hz)
    · rcases hw _ hm with h | h | h
      · exact False.elim ((by decide : goal ≠ (0 : W)) h)
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 72) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 72 ∨ z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h | h | h | ⟨a, ha, b, hb, hab, hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr (.inl h))) he')
    · exact Or.inl (fn av (appendOK (.inr (.inr h))) he')
    · refine Or.inr ⟨a, ha, b, hb, hab, z, hop, fn (insert z av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu | hu
      · exact (hw _ hu).imp_right (Or.imp_right (Finset.mem_insert_of_mem ·))
      · simp_all

def dispatch (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) : Bool :=
  let base := cuts r
  (ops a b).any fun w =>
    let v := sep w ||| base
    ((v == -1) && next extra (w :: r)) ||
    ((extra != 0) && (((v ||| sep a == -1) && next (extra - 1) (w :: a :: r)) ||
                       ((v ||| sep b == -1) && next (extra - 1) (w :: b :: r)))) ||
    ((extra ≥ 2) && (v ||| sep a ||| sep b == -1) && next (extra - 2) (w :: a :: b :: r))

def optimized : ℕ → ℕ → List W → Bool
  | 0, _, ws => ws == [goal]
  | k + 1, extra, ws => ws == [goal] ||
    (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)

theorem dispatch_complete {k extra : ℕ} {a b z : W} {r kept : List W}
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

theorem optimized_complete (n : ℕ) (ws : List W) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps goal n ws.toFinset) :
    optimized n extra ws = true := by
  induction n generalizing ws extra with
  | zero => simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · simp [optimized, singleton_list hn done]
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
        have hl : live basicOps goal k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hk (by omega) (by omega) (cuts_full hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def A : Fin 4 → Fin 3 → Bool := fun u v => (2457 : ℕ).testBit (3 * u.val + v.val)

def posL : List (Fin 4 × Fin 3) :=
  [(0, 0), (1, 0), (1, 1), (2, 1), (2, 2), (3, 2)]

def negL : List (Fin 4 × Fin 3) :=
  [(0, 1), (0, 2), (1, 2), (2, 0), (3, 0), (3, 1)]

def samp (k : Fin 72) : Fin 4 × Fin 3 :=
  if k.val < 36 then negL.getD (k.val % 6) (0, 0) else posL.getD ((k.val - 36) / 6) (0, 0)

theorem input_rows : ∀ k : Fin 72,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 72, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 72) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false = bit k goal := by
  rw [input_rows k, goal_rows k]
  exact hr (samp k).1 (samp k).2

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  exact .inr (.inr (List.mem_toFinset.mpr hu))

theorem get_build (C : Circuit) (hg : Monotone2 C) (hr : PEqualNP.Represents.Represents A C) :
    build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C hr)

theorem extend_live {m n : ℕ} {s : Finset W} (le : m ≤ n) (h : live basicOps goal m s) :
    live basicOps goal n s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

theorem inputs_nodup : inputs.Nodup := by decide +kernel

theorem inputs_length : inputs.length = 7 := by decide +kernel

def probes : List (W × Fin 36) :=
  inputs.zip [3,9,18,31,0,14,27]

lemma probes_cover : probes.map Prod.fst = inputs := by decide +kernel

lemma probes_ok : probes.all (fun p =>
    (inputs.filter (fun z => z.getLsbD (36 + p.2.val) && !z.getLsbD p.2.val)) == [p.1]) = true := by
  decide +kernel

lemma all_live_inputs {k : ℕ} {S : Finset W} (hsub : S ⊆ inputs.toFinset)
    (h : live basicOps goal k S) : inputs.toFinset ⊆ S := by
  intro w hw
  have hm : w ∈ probes.map Prod.fst := by
    rw [probes_cover]
    exact List.mem_toFinset.mp hw
  obtain ⟨⟨v,i⟩, hvi, hvw⟩ := List.mem_map.mp hm
  simp only at hvw
  subst v
  have heq := List.all_eq_true.mp probes_ok (w,i) hvi
  have heq' : (inputs.filter (fun z => z.getLsbD (36 + i.val) && !z.getLsbD i.val)) = [w] := by
    simpa only [beq_iff_eq] using heq
  obtain ⟨z,hz,hd⟩ := live_separates (differs i) (goal_differs i) (ops_differs i) h
  have hz' : z ∈ inputs.filter (fun z => z.getLsbD (36 + i.val) && !z.getLsbD i.val) := by
    apply List.mem_filter.mpr
    refine ⟨List.mem_toFinset.mp (hsub hz), ?_⟩
    simp only [differs] at hd
    simp [hd.1,hd.2]
  rw [heq',List.mem_singleton] at hz'
  exact hz' ▸ hz

theorem opt_unfold (k extra : ℕ) (ws : List W) : optimized (k + 1) extra ws =
    (ws == [goal] || (pairs ws).any (fun (a, b, r) => dispatch extra (optimized k) a b r)) := by
  rw [optimized]

def topG : W × W × List W → Bool := fun (a, b, r) => !(dispatch 1 (optimized 6) a b r)

def D (i : ℕ) : List (W × W × List W) := (pairs inputs).drop i

lemma D_succ (i : ℕ) : (D i).drop 1 = D (i + 1) := by
  simp only [D, List.drop_drop]

lemma all_split {α : Type} (g : α → Bool) (M : List α) (n : ℕ)
    (h1 : (M.take n).all g = true) (h2 : (M.drop n).all g = true) : M.all g = true := by
  rw [← List.take_append_drop n M, List.all_append, h1, h2]
  rfl

lemma d_end : (D 21).all topG = true := by decide +kernel

set_option maxRecDepth 100000 in
lemma chunk_0 : ((D 0).take 1).all topG = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chunk_1 : ((D 1).take 1).all topG = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chunk_2 : ((D 2).take 1).all topG = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chunk_3 : ((D 3).take 1).all topG = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chunk_4 : ((D 4).take 1).all topG = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chunk_5 : ((D 5).take 1).all topG = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chunk_6 : ((D 6).take 1).all topG = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chunk_7 : ((D 7).take 1).all topG = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chunk_8 : ((D 8).take 1).all topG = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chunk_9 : ((D 9).take 1).all topG = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chunk_10 : ((D 10).take 1).all topG = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chunk_11 : ((D 11).take 1).all topG = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chunk_12 : ((D 12).take 1).all topG = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chunk_13 : ((D 13).take 1).all topG = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chunk_14 : ((D 14).take 1).all topG = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chunk_15 : ((D 15).take 1).all topG = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chunk_16 : ((D 16).take 1).all topG = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chunk_17 : ((D 17).take 1).all topG = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chunk_18 : ((D 18).take 1).all topG = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chunk_19 : ((D 19).take 1).all topG = true := by
  decide +kernel

set_option maxRecDepth 100000 in
lemma chunk_20 : ((D 20).take 1).all topG = true := by
  decide +kernel

lemma pairs_all : (D 0).all topG = true := by
  have e21 := d_end
  have e20 : (D 20).all topG = true := all_split topG (D 20) 1 chunk_20 (by rw [D_succ]; exact e21)
  have e19 : (D 19).all topG = true := all_split topG (D 19) 1 chunk_19 (by rw [D_succ]; exact e20)
  have e18 : (D 18).all topG = true := all_split topG (D 18) 1 chunk_18 (by rw [D_succ]; exact e19)
  have e17 : (D 17).all topG = true := all_split topG (D 17) 1 chunk_17 (by rw [D_succ]; exact e18)
  have e16 : (D 16).all topG = true := all_split topG (D 16) 1 chunk_16 (by rw [D_succ]; exact e17)
  have e15 : (D 15).all topG = true := all_split topG (D 15) 1 chunk_15 (by rw [D_succ]; exact e16)
  have e14 : (D 14).all topG = true := all_split topG (D 14) 1 chunk_14 (by rw [D_succ]; exact e15)
  have e13 : (D 13).all topG = true := all_split topG (D 13) 1 chunk_13 (by rw [D_succ]; exact e14)
  have e12 : (D 12).all topG = true := all_split topG (D 12) 1 chunk_12 (by rw [D_succ]; exact e13)
  have e11 : (D 11).all topG = true := all_split topG (D 11) 1 chunk_11 (by rw [D_succ]; exact e12)
  have e10 : (D 10).all topG = true := all_split topG (D 10) 1 chunk_10 (by rw [D_succ]; exact e11)
  have e9 : (D 9).all topG = true := all_split topG (D 9) 1 chunk_9 (by rw [D_succ]; exact e10)
  have e8 : (D 8).all topG = true := all_split topG (D 8) 1 chunk_8 (by rw [D_succ]; exact e9)
  have e7 : (D 7).all topG = true := all_split topG (D 7) 1 chunk_7 (by rw [D_succ]; exact e8)
  have e6 : (D 6).all topG = true := all_split topG (D 6) 1 chunk_6 (by rw [D_succ]; exact e7)
  have e5 : (D 5).all topG = true := all_split topG (D 5) 1 chunk_5 (by rw [D_succ]; exact e6)
  have e4 : (D 4).all topG = true := all_split topG (D 4) 1 chunk_4 (by rw [D_succ]; exact e5)
  have e3 : (D 3).all topG = true := all_split topG (D 3) 1 chunk_3 (by rw [D_succ]; exact e4)
  have e2 : (D 2).all topG = true := all_split topG (D 2) 1 chunk_2 (by rw [D_succ]; exact e3)
  have e1 : (D 1).all topG = true := all_split topG (D 1) 1 chunk_1 (by rw [D_succ]; exact e2)
  have e0 : (D 0).all topG = true := all_split topG (D 0) 1 chunk_0 (by rw [D_succ]; exact e1)
  exact e0

lemma full_none : optimized (6 + 1) 1 inputs = false := by
  rw [opt_unfold, Bool.or_eq_false_iff]
  refine ⟨by decide +kernel, ?_⟩
  rw [List.any_eq_false]
  intro x hx hd
  have hg : topG x = true := List.all_eq_true.mp pairs_all x (by simpa [D] using hx)
  obtain ⟨a, b, r⟩ := x
  simp only [topG, Bool.not_eq_true'] at hg
  simp only [hg] at hd
  exact Bool.noConfusion hd

theorem no_small (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 7)
    (hr : PEqualNP.Represents.Represents A C) : False := by
  obtain ⟨S, hsub, hl⟩ := compress (get_build C hm hr)
  have heq : S = inputs.toFinset := Finset.Subset.antisymm hsub (all_live_inputs hsub hl)
  subst S
  have hl3 := extend_live hs hl
  have hsearch := optimized_complete 7 inputs 1 inputs_nodup (by rw [inputs_length]) hl3
  rw [full_none] at hsearch
  exact Bool.noConfusion hsearch

end PEqualNP.Outside.L_meta_9502.P7Lower

theorem PEqualNP.Outside.L_meta_9502.P7Lower :
    ¬ PEqualNP.Represents.RepSizeAtMost (fun u : Fin 4 => fun v : Fin 3 => (2457 : ℕ).testBit (3*u.val+v.val)) 7 := by
  rintro ⟨C,hm,hs,hr⟩
  exact PEqualNP.Outside.L_meta_9502.P7Lower.no_small C hm hs hr
