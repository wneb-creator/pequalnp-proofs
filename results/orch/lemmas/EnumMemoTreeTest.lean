import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6349.Enum

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

abbrev W := BitVec 128

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 64 := ((x >>> 64) &&& ~~~x).setWidth 64

def cuts (ws : List W) : BitVec 64 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 64) ++ (0 : BitVec 64)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [0xffffff0101010101010101, 0xffff0000000606060606060606, 0xffff00000000001818181818181818, 0xff00000000000000e0e0e0e0e0e0e0e0, 0xff000000000000ff0a0a0a0a0a0a0a0a, 0xff00ff0000002121212121212121, 0xff00000000ff004444444444444444, 0xff00ff00009090909090909090]

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

def differs (i : Fin 64) (w : W) : Prop :=
  w.getLsbD (64 + i.val) = true ∧ w.getLsbD i.val = false

theorem ops_differs (i : Fin 64) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (64 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (64 + i.val) <;> cases b.getLsbD i.val <;> simp

theorem goal_differs : ∀ i : Fin 64, differs i goal := by
  unfold differs
  decide

theorem cuts_spec (ws : List W) (i : Fin 64) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 128 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

theorem cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 64)[j]
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
  z == 0 || z == BitVec.allOnes 128 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 128) (z : W) : Bool := z[k.val]

private theorem read_bit (w : List W) (i : ℕ) (k : Fin 128) :
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
    · exact ⟨BitVec.allOnes 128, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
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
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 128 ∨ u ∈ available

theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 128 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 128 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 128 ∨ t ∈ available ∨
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
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 128) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 128 ∨ z ∈ av) : represents av (w ++ [z]) := by
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

def A : Fin 4 → Fin 4 → Bool := fun u v : Fin 4 => (5805 : ℕ).testBit (4 * u.val + v.val)

def posL : List (Fin 4 × Fin 4) :=
  [(0, 0), (0, 2), (0, 3), (1, 1), (1, 3), (2, 1), (2, 2), (3, 0)]

def negL : List (Fin 4 × Fin 4) :=
  [(0, 1), (1, 0), (1, 2), (2, 0), (2, 3), (3, 1), (3, 2), (3, 3)]

def samp (k : Fin 128) : Fin 4 × Fin 4 :=
  if k.val < 64 then negL.getD (k.val % 8) (0, 0) else posL.getD ((k.val - 64) / 8) (0, 0)

theorem input_rows : ∀ k : Fin 128,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

theorem goal_rows : ∀ k : Fin 128, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

theorem rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 128) :
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

theorem essential_inputs : inputs.sublists.all
    (fun l => (cuts l != -1) || (l == inputs)) = true := by
  decide +kernel

theorem lower_of_search (hfalse : optimized 9 2 inputs = false) :
    ¬ PEqualNP.Represents.RepSizeAtMost A 9 := by
  rintro ⟨C, hm, hs, hr⟩
  obtain ⟨S, hsub, hl⟩ := compress (get_build C hm hr)
  have hl3 : live basicOps goal 9 S := extend_live hs hl
  let l := inputs.filter (fun w => decide (w ∈ S))
  have hlS : l.toFinset = S := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩
  have hnd : l.Nodup := inputs_nodup.filter _
  have hcard := live_card hl3
  rw [← hlS, List.toFinset_card_of_nodup hnd] at hcard
  have hsearch := optimized_complete 9 l (10 - l.length) hnd (by omega) (hlS ▸ hl3)
  have hmem : l ∈ inputs.sublists := List.mem_sublists.mpr List.filter_sublist
  have hrow := List.all_eq_true.mp essential_inputs l hmem
  have hcuts : cuts l = -1 := cuts_full (hlS ▸ hl3)
  have hli : l = inputs := by simpa [hcuts] using hrow
  rw [hli] at hsearch
  have hlen : 10 - inputs.length = 2 := by decide +kernel
  rw [hlen, hfalse] at hsearch
  exact Bool.noConfusion hsearch


abbrev State := ℕ × List W
abbrev Tree := BinaryTree State

def wireLt : List W → List W → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: aa, b :: bb => if a = b then wireLt aa bb else a.toNat < b.toNat

def stateLt (a b : State) : Bool :=
  if a.1 = b.1 then wireLt a.2 b.2 else a.1 < b.1

def treeMem : Tree → State → Bool
  | .nil, _ => false
  | .node x l r, y => if y = x then true else if stateLt y x then treeMem l y else treeMem r y

def entries : Tree → List State
  | .nil => []
  | .node x l r => entries l ++ [x] ++ entries r

theorem treeMem_sound {T : Tree} {x : State} (h : treeMem T x = true) : x ∈ entries T := by
  induction T with
  | nil => simp [treeMem] at h
  | node y l r il ir =>
    simp only [treeMem] at h
    split_ifs at h with he ho
    · simp [entries, he]
    · have hh := il h
      simp [entries, hh]
    · have hh := ir h
      simp [entries, hh]

def sorted (ws : List W) : List W := ws.insertionSort (fun a b => a.toNat ≤ b.toNat)

theorem sorted_finset (ws : List W) : (sorted ws).toFinset = ws.toFinset := by
  ext x
  simp only [List.mem_toFinset]
  exact (List.perm_insertionSort (fun a b : W => a.toNat ≤ b.toNat) ws).mem_iff

def checkNode (T : Tree) (st : State) : Bool :=
  let k := st.1
  let ws := st.2
  if k = 0 then ws != [goal] else
    !(ws == [goal] || (pairs ws).any (fun (a,b,r) =>
      dispatch (k+1-ws.length)
        (fun _ zs => !treeMem T (k-1, sorted zs)) a b r))


def nodeOK (T : Tree) (st : State) : Bool := checkNode T st

theorem certificate_sound (T : Tree)
    (hT : ∀ st ∈ entries T, nodeOK T st = true) :
    ∀ k ws, ws.Nodup → (k, ws) ∈ entries T → ¬ live basicOps goal k ws.toFinset := by
  intro k
  induction k with
  | zero =>
    intro ws hn hm hl
    have hh := hT (0,ws) hm
    have he := singleton_list hn hl
    simp [nodeOK, checkNode, he] at hh
  | succ k ih =>
    intro ws hn hm hl
    have hc := hT (k+1,ws) hm
    change checkNode T (k+1,ws) = true at hc
    have hv : (ws == [goal] || (pairs ws).any (fun (a,b,r) =>
        dispatch (k+2-ws.length) (fun _ zs => !treeMem T (k, sorted zs)) a b r)) = true := by
      rcases first_live hl with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
      · simp [singleton_list hn done]
      · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
        have go {a b : W} (perm : ws.Perm (a :: b :: r))
            (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
            dispatch (k+2-ws.length) (fun _ zs => !treeMem T (k, sorted zs)) a b r = true := by
          obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
          have hznew : z ∉ kept := by
            intro hu
            apply hout
            rw [hset]
            exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
          have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
          have hnext : live basicOps goal k (z :: kept).toFinset := by simpa [hfin] using tail
          have hnlen := live_card hnext
          rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hnlen
          have hwlen := live_card hl
          rw [List.toFinset_card_of_nodup hn] at hwlen
          have hplen := perm.length_eq
          simp only [List.length_cons] at hplen
          apply dispatch_complete (k := k) (extra := k+2-ws.length)
            (fun _ zs => !treeMem T (k, sorted zs)) hop hk (by omega) (by omega) (cuts_full hnext)
          cases hm : treeMem T (k, sorted (z :: kept)) with
          | false => rfl
          | true =>
            exact False.elim (ih (sorted (z :: kept))
              ((List.perm_insertionSort (fun a b : W => a.toNat ≤ b.toNat) (z :: kept)).nodup_iff.mpr hnd) (treeMem_sound hm)
              (by simpa only [sorted_finset] using hnext))
        simp only [Bool.or_eq_true, List.any_eq_true]
        right
        rcases hm with direct | swap
        · exact ⟨(a,b,r), direct, go hp hs hz⟩
        · exact ⟨(b,a,r), swap, go (hp.trans (.swap _ _ _))
            (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩
    have he : k+1+1 = k+2 := by omega
    simp only [checkNode, Nat.succ_ne_zero, ite_false, Nat.add_sub_cancel, he] at hc
    rw [hv] at hc
    exact Bool.noConfusion hc


theorem lower_of_certificate (T : Tree)
    (hT : ∀ st ∈ entries T, nodeOK T st = true)
    (hroot : treeMem T (9, sorted inputs) = true) :
    ¬ PEqualNP.Represents.RepSizeAtMost A 9 := by
  rintro ⟨C, hm, hs, hr⟩
  obtain ⟨S, hsub, hl⟩ := compress (get_build C hm hr)
  have hl3 : live basicOps goal 9 S := extend_live hs hl
  let l := inputs.filter (fun w => decide (w ∈ S))
  have hlS : l.toFinset = S := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩
  have hmem : l ∈ inputs.sublists := List.mem_sublists.mpr List.filter_sublist
  have hrow := List.all_eq_true.mp essential_inputs l hmem
  have hcuts : cuts l = -1 := cuts_full (hlS ▸ hl3)
  have hli : l = inputs := by simpa [hcuts] using hrow
  apply certificate_sound T hT 9 (sorted inputs)
    ((List.perm_insertionSort (fun a b : W => a.toNat ≤ b.toNat) inputs).nodup_iff.mpr inputs_nodup)
    (treeMem_sound hroot)
  rw [sorted_finset, ← hli, hlS]
  exact hl3

theorem all_of_chunks {β : Type} (F : β → Bool) (n : ℕ) : ∀ (m : ℕ) (L : List β), L.length ≤ n * m →
    (∀ j < m, ((L.drop (n * j)).take n).all F = true) → L.all F = true := by
  intro m
  induction m with
  | zero =>
    intro L hl _
    have h0 : L = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
    simp [h0]
  | succ m ih =>
    intro L hl h
    rw [← List.take_append_drop n L, List.all_append, Bool.and_eq_true]
    refine ⟨by simpa using h 0 (by omega), ih (L.drop n) ?_ ?_⟩
    · rw [List.length_drop]
      rw [Nat.mul_succ] at hl
      generalize n * m = t at *
      omega
    · intro j hj
      have e : List.drop (n * j) (List.drop n L) = List.drop (n * (j + 1)) L := by
        rw [List.drop_drop]
        congr 1
        ring
      rw [e]
      exact h (j + 1) (by omega)


theorem all_entry_node (T : Tree) (x : State) (l r : Tree)
    (hl : (entries l).all (nodeOK T) = true) (hx : nodeOK T x = true)
    (hr : (entries r).all (nodeOK T) = true) :
    (entries (.node x l r)).all (nodeOK T) = true := by
  simp only [entries, List.all_append, List.all_cons, List.all_nil, Bool.and_true]
  simp [hl, hx, hr]
def v0 : W := 0x0
def v1 : W := 0x101010101010101
def v2 : W := 0x202020202020202
def v3 : W := 0x404040404040404
def v4 : W := 0x808080808080808
def v5 : W := 0x1010101010101010
def v6 : W := 0x2020202020202020
def v7 : W := 0x4040404040404040
def v8 : W := 0x8080808080808080
def v9 : W := 0xff0000000000000000
def v10 : W := 0xff000000000000000000
def v11 : W := 0xff00000000000000000000
def v12 : W := 0xffffff0101010101010101
def v13 : W := 0xffffff2121212121212121
def v14 : W := 0xff0000000000000000000000
def v15 : W := 0xff0000ff0000000000000000
def v16 : W := 0xff00ff000000000000000000
def v17 : W := 0xffffffff0101010101010101
def v18 : W := 0xff000000000000000000000000
def v19 : W := 0xff00ff00000000000000000000
def v20 : W := 0xff00ff00009090909090909090
def v21 : W := 0xff00ff00009898989898989898
def v22 : W := 0xff00ff0000b0b0b0b0b0b0b0b0
def v23 : W := 0xff00ff0000d0d0d0d0d0d0d0d0
def v24 : W := 0xff00ff00ff9090909090909090
def v25 : W := 0xff00ffff009090909090909090
def v26 : W := 0xff00ffffff0101010101010101
def v27 : W := 0xff00ffffff9191919191919191
def v28 : W := 0xffff0000000000000000000000
def v29 : W := 0xffff0000000606060606060606
def v30 : W := 0xffff0000000e0e0e0e0e0e0e0e
def v31 : W := 0xffff0000004646464646464646
def v32 : W := 0xffff0000ff0606060606060606
def v33 : W := 0xffff00ff000606060606060606
def v34 : W := 0xffffff00000606060606060606
def v35 : W := 0xffffff00009090909090909090
def v36 : W := 0xffffff00009696969696969696
def v37 : W := 0xffffff00ff9090909090909090
def v38 : W := 0xffffffff009090909090909090
def v39 : W := 0xffffffffff0707070707070707
def v40 : W := 0xff00000000000000000000000000
def v41 : W := 0xff00000000ff0000000000000000
def v42 : W := 0xff0000ff00000000000000000000
def v43 : W := 0xff0000ffffff0101010101010101
def v44 : W := 0xff00ff0000000000000000000000
def v45 : W := 0xff00ff0000002121212121212121
def v46 : W := 0xff00ff0000006161616161616161
def v47 : W := 0xff00ff000000a1a1a1a1a1a1a1a1
def v48 : W := 0xff00ff0000ff2121212121212121
def v49 : W := 0xff00ff00ff002121212121212121
def v50 : W := 0xff00ffff00002121212121212121
def v51 : W := 0xff00ffffffff0101010101010101
def v52 : W := 0xff00ffffffff2121212121212121
def v53 : W := 0xffff00ff00009090909090909090
def v54 : W := 0xffff00ff00ff9090909090909090
def v55 : W := 0xffffff0000000606060606060606
def v56 : W := 0xffffff0000002121212121212121
def v57 : W := 0xffffff0000002727272727272727
def v58 : W := 0xffffff0000ff0606060606060606
def v59 : W := 0xffffffff00000606060606060606
def v60 : W := 0xffffffff0000b1b1b1b1b1b1b1b1
def v61 : W := 0xffffffffffff2121212121212121
def v62 : W := 0xffffffffffff2727272727272727
def v63 : W := 0xffffffffffffb1b1b1b1b1b1b1b1
def v64 : W := 0xff0000000000000000000000000000
def v65 : W := 0xff00000000ff000000000000000000
def v66 : W := 0xff00000000ff004444444444444444
def v67 : W := 0xff00000000ff004646464646464646
def v68 : W := 0xff00000000ff006464646464646464
def v69 : W := 0xff00000000ff00c4c4c4c4c4c4c4c4
def v70 : W := 0xff00000000ffff4444444444444444
def v71 : W := 0xff000000ffff004444444444444444
def v72 : W := 0xff000000ffffff0101010101010101
def v73 : W := 0xff000000ffffff4545454545454545
def v74 : W := 0xff0000ff00ff004444444444444444
def v75 : W := 0xff0000ff00ffff4444444444444444
def v76 : W := 0xff00ff000000000000000000000000
def v77 : W := 0xff00ff0000ff004444444444444444
def v78 : W := 0xff00ff00ff00009090909090909090
def v79 : W := 0xff00ff00ffff00d4d4d4d4d4d4d4d4
def v80 : W := 0xff00ff00ffffff0101010101010101
def v81 : W := 0xff00ffff0000000606060606060606
def v82 : W := 0xff00ffff00ff000000000000000000
def v83 : W := 0xff00ffff00ff000606060606060606
def v84 : W := 0xff00ffff00ff004444444444444444
def v85 : W := 0xff00ffff00ff004646464646464646
def v86 : W := 0xff00ffff00ffff4646464646464646
def v87 : W := 0xff00ffffffff004646464646464646
def v88 : W := 0xff00ffffffff00d6d6d6d6d6d6d6d6
def v89 : W := 0xff00ffffffffff4747474747474747
def v90 : W := 0xffff00000000000000000000000000
def v91 : W := 0xffff00000000001818181818181818
def v92 : W := 0xffff00000000001a1a1a1a1a1a1a1a
def v93 : W := 0xffff00000000009898989898989898
def v94 : W := 0xffff00000000ff1818181818181818
def v95 : W := 0xffff000000ff001818181818181818
def v96 : W := 0xffff000000ff004444444444444444
def v97 : W := 0xffff000000ff005c5c5c5c5c5c5c5c
def v98 : W := 0xffff000000ffff4444444444444444
def v99 : W := 0xffff0000ff00001818181818181818
def v100 : W := 0xffff0000ffff004444444444444444
def v101 : W := 0xffff0000ffffff1919191919191919
def v102 : W := 0xffff00ff0000001818181818181818
def v103 : W := 0xffff00ff0000002121212121212121
def v104 : W := 0xffff00ff0000003939393939393939
def v105 : W := 0xffff00ff0000ff1818181818181818
def v106 : W := 0xffff00ff00ff001818181818181818
def v107 : W := 0xffff00ff00ff006565656565656565
def v108 : W := 0xffff00ffffffff2121212121212121
def v109 : W := 0xffff00ffffffff3939393939393939
def v110 : W := 0xffff00ffffffff6565656565656565
def v111 : W := 0xffffff000000001818181818181818
def v112 : W := 0xffffff00ff00000000000000000000
def v113 : W := 0xffffff00ff00001818181818181818
def v114 : W := 0xffffff00ff00009090909090909090
def v115 : W := 0xffffff00ff00009898989898989898
def v116 : W := 0xffffff00ff00ff9898989898989898
def v117 : W := 0xffffff00ffff009898989898989898
def v118 : W := 0xffffff00ffff00dcdcdcdcdcdcdcdc
def v119 : W := 0xffffff00ffffff9999999999999999
def v120 : W := 0xffffffff0000001e1e1e1e1e1e1e1e
def v121 : W := 0xffffffff0000002121212121212121
def v122 : W := 0xffffffff00ff004646464646464646
def v123 : W := 0xffffffff00ff005e5e5e5e5e5e5e5e
def v124 : W := 0xffffffff00ff006767676767676767
def v125 : W := 0xffffffffff00009898989898989898
def v126 : W := 0xffffffffff00009e9e9e9e9e9e9e9e
def v127 : W := 0xffffffffff0000b9b9b9b9b9b9b9b9
def v128 : W := 0xffffffffffff004646464646464646
def v129 : W := 0xffffffffffff009898989898989898
def v130 : W := 0xffffffffffff00dededededededede
def v131 : W := 0xffffffffffffff2121212121212121
def v132 : W := 0xffffffffffffff6767676767676767
def v133 : W := 0xffffffffffffffb9b9b9b9b9b9b9b9
def v134 : W := 0xff000000000000000000000000000000
def v135 : W := 0xff000000000000002020202020202020
def v136 : W := 0xff000000000000004040404040404040
def v137 : W := 0xff000000000000008080808080808080
def v138 : W := 0xff00000000000000e0e0e0e0e0e0e0e0
def v139 : W := 0xff00000000000000e1e1e1e1e1e1e1e1
def v140 : W := 0xff00000000000000e4e4e4e4e4e4e4e4
def v141 : W := 0xff00000000000000f0f0f0f0f0f0f0f0
def v142 : W := 0xff000000000000ff0000000000000000
def v143 : W := 0xff000000000000ff0a0a0a0a0a0a0a0a
def v144 : W := 0xff000000000000ff0e0e0e0e0e0e0e0e
def v145 : W := 0xff000000000000ff1a1a1a1a1a1a1a1a
def v146 : W := 0xff000000000000ffe0e0e0e0e0e0e0e0
def v147 : W := 0xff000000000000ffeaeaeaeaeaeaeaea
def v148 : W := 0xff0000000000ff00e0e0e0e0e0e0e0e0
def v149 : W := 0xff0000000000ffff0a0a0a0a0a0a0a0a
def v150 : W := 0xff00000000ff0000e0e0e0e0e0e0e0e0
def v151 : W := 0xff00000000ff00ff0a0a0a0a0a0a0a0a
def v152 : W := 0xff00000000ffffff0101010101010101
def v153 : W := 0xff00000000ffffff0b0b0b0b0b0b0b0b
def v154 : W := 0xff00000000ffffff2121212121212121
def v155 : W := 0xff00000000ffffffe1e1e1e1e1e1e1e1
def v156 : W := 0xff000000ff0000000000000000000000
def v157 : W := 0xff000000ff000000e0e0e0e0e0e0e0e0
def v158 : W := 0xff000000ff0000ff0000000000000000
def v159 : W := 0xff000000ff0000ff0a0a0a0a0a0a0a0a
def v160 : W := 0xff000000ff0000ffe0e0e0e0e0e0e0e0
def v161 : W := 0xff000000ff00ff00e0e0e0e0e0e0e0e0
def v162 : W := 0xff000000ff00ffff0a0a0a0a0a0a0a0a
def v163 : W := 0xff000000ffffffff0101010101010101
def v164 : W := 0xff0000ff000000000000000000000000
def v165 : W := 0xff0000ff00000000e0e0e0e0e0e0e0e0
def v166 : W := 0xff0000ff000000ff0a0a0a0a0a0a0a0a
def v167 : W := 0xff0000ff00ff00000000000000000000
def v168 : W := 0xff0000ff00ff00009090909090909090
def v169 : W := 0xff0000ff00ff0000b0b0b0b0b0b0b0b0
def v170 : W := 0xff0000ff00ff0000d0d0d0d0d0d0d0d0
def v171 : W := 0xff0000ff00ff0000e0e0e0e0e0e0e0e0
def v172 : W := 0xff0000ff00ff0000f0f0f0f0f0f0f0f0
def v173 : W := 0xff0000ff00ff00ff9090909090909090
def v174 : W := 0xff0000ff00ff00ff9a9a9a9a9a9a9a9a
def v175 : W := 0xff0000ff00ff00fff0f0f0f0f0f0f0f0
def v176 : W := 0xff0000ff00ff00fffafafafafafafafa
def v177 : W := 0xff0000ff00ffff00f0f0f0f0f0f0f0f0
def v178 : W := 0xff0000ff00ffffff0101010101010101
def v179 : W := 0xff0000ff00fffffff1f1f1f1f1f1f1f1
def v180 : W := 0xff0000ffff0000000606060606060606
def v181 : W := 0xff0000ffff000000e6e6e6e6e6e6e6e6
def v182 : W := 0xff0000ffff0000ff0000000000000000
def v183 : W := 0xff0000ffff0000ff0606060606060606
def v184 : W := 0xff0000ffff0000ff0a0a0a0a0a0a0a0a
def v185 : W := 0xff0000ffff0000ff0e0e0e0e0e0e0e0e
def v186 : W := 0xff0000ffff0000ffeeeeeeeeeeeeeeee
def v187 : W := 0xff0000ffff00ffff0e0e0e0e0e0e0e0e
def v188 : W := 0xff0000ffffff00009090909090909090
def v189 : W := 0xff0000ffffff0000f0f0f0f0f0f0f0f0
def v190 : W := 0xff0000ffffff0000f6f6f6f6f6f6f6f6
def v191 : W := 0xff0000ffffff00ff0e0e0e0e0e0e0e0e
def v192 : W := 0xff0000ffffff00ff9090909090909090
def v193 : W := 0xff0000ffffff00ff9e9e9e9e9e9e9e9e
def v194 : W := 0xff0000ffffff00fffefefefefefefefe
def v195 : W := 0xff0000ffffffffff0f0f0f0f0f0f0f0f
def v196 : W := 0xff00ff00000000000000000000000000
def v197 : W := 0xff00ff0000000000e0e0e0e0e0e0e0e0
def v198 : W := 0xff00ff00000000ff0000000000000000
def v199 : W := 0xff00ff00000000ff0a0a0a0a0a0a0a0a
def v200 : W := 0xff00ff00000000ffe0e0e0e0e0e0e0e0
def v201 : W := 0xff00ff0000ff0000e0e0e0e0e0e0e0e0
def v202 : W := 0xff00ff0000ff00ff0a0a0a0a0a0a0a0a
def v203 : W := 0xff00ff0000ffffff0101010101010101
def v204 : W := 0xff00ff00ff0000000000000000000000
def v205 : W := 0xff00ff00ff0000002121212121212121
def v206 : W := 0xff00ff00ff0000006161616161616161
def v207 : W := 0xff00ff00ff000000a1a1a1a1a1a1a1a1
def v208 : W := 0xff00ff00ff000000e0e0e0e0e0e0e0e0
def v209 : W := 0xff00ff00ff000000e1e1e1e1e1e1e1e1
def v210 : W := 0xff00ff00ff0000ff2121212121212121
def v211 : W := 0xff00ff00ff0000ff2b2b2b2b2b2b2b2b
def v212 : W := 0xff00ff00ff0000ffe1e1e1e1e1e1e1e1
def v213 : W := 0xff00ff00ff0000ffebebebebebebebeb
def v214 : W := 0xff00ff00ff00ff00e1e1e1e1e1e1e1e1
def v215 : W := 0xff00ff00ffff0000e1e1e1e1e1e1e1e1
def v216 : W := 0xff00ff00ffffffff0101010101010101
def v217 : W := 0xff00ff00ffffffff2121212121212121
def v218 : W := 0xff00ff00ffffffff2b2b2b2b2b2b2b2b
def v219 : W := 0xff00ff00ffffffffe1e1e1e1e1e1e1e1
def v220 : W := 0xff00ffff00ff00009090909090909090
def v221 : W := 0xff00ffff00ff0000f0f0f0f0f0f0f0f0
def v222 : W := 0xff00ffffff0000000606060606060606
def v223 : W := 0xff00ffffff0000002121212121212121
def v224 : W := 0xff00ffffff000000e1e1e1e1e1e1e1e1
def v225 : W := 0xff00ffffff000000e7e7e7e7e7e7e7e7
def v226 : W := 0xff00ffffff0000ff0e0e0e0e0e0e0e0e
def v227 : W := 0xff00ffffff0000ff2f2f2f2f2f2f2f2f
def v228 : W := 0xff00ffffff0000ffefefefefefefefef
def v229 : W := 0xff00ffffffff0000f1f1f1f1f1f1f1f1
def v230 : W := 0xff00ffffffffffff2121212121212121
def v231 : W := 0xff00ffffffffffff2f2f2f2f2f2f2f2f
def v232 : W := 0xff00fffffffffffff1f1f1f1f1f1f1f1
def v233 : W := 0xffff0000000000000000000000000000
def v234 : W := 0xffff000000000000e0e0e0e0e0e0e0e0
def v235 : W := 0xffff0000000000ff0a0a0a0a0a0a0a0a
def v236 : W := 0xffff00000000ff000000000000000000
def v237 : W := 0xffff00000000ff004444444444444444
def v238 : W := 0xffff00000000ff006464646464646464
def v239 : W := 0xffff00000000ff00c4c4c4c4c4c4c4c4
def v240 : W := 0xffff00000000ff00e0e0e0e0e0e0e0e0
def v241 : W := 0xffff00000000ff00e4e4e4e4e4e4e4e4
def v242 : W := 0xffff00000000ffff4444444444444444
def v243 : W := 0xffff00000000ffff4e4e4e4e4e4e4e4e
def v244 : W := 0xffff00000000ffffe4e4e4e4e4e4e4e4
def v245 : W := 0xffff00000000ffffeeeeeeeeeeeeeeee
def v246 : W := 0xffff000000ffff00e4e4e4e4e4e4e4e4
def v247 : W := 0xffff000000ffffff0101010101010101
def v248 : W := 0xffff000000ffffffe5e5e5e5e5e5e5e5
def v249 : W := 0xffff0000ff00ff004444444444444444
def v250 : W := 0xffff0000ff00ff00e4e4e4e4e4e4e4e4
def v251 : W := 0xffff00ff00000000e0e0e0e0e0e0e0e0
def v252 : W := 0xffff00ff000000ff0a0a0a0a0a0a0a0a
def v253 : W := 0xffff00ff0000ff004444444444444444
def v254 : W := 0xffff00ff0000ff00e4e4e4e4e4e4e4e4
def v255 : W := 0xffff00ff00ff00009090909090909090
def v256 : W := 0xffff00ff00ff0000f0f0f0f0f0f0f0f0
def v257 : W := 0xffff00ff00ffff00f4f4f4f4f4f4f4f4
def v258 : W := 0xffff00ffff0000000606060606060606
def v259 : W := 0xffff00ffff0000ff0e0e0e0e0e0e0e0e
def v260 : W := 0xffff00ffff00ff004646464646464646
def v261 : W := 0xffff00ffff00ff00e6e6e6e6e6e6e6e6
def v262 : W := 0xffff00ffff00ffff4646464646464646
def v263 : W := 0xffff00ffff00ffff4e4e4e4e4e4e4e4e
def v264 : W := 0xffffff00000000001818181818181818
def v265 : W := 0xffffff0000000000f8f8f8f8f8f8f8f8
def v266 : W := 0xffffff00000000ff0000000000000000
def v267 : W := 0xffffff00000000ff0a0a0a0a0a0a0a0a
def v268 : W := 0xffffff00000000ff1818181818181818
def v269 : W := 0xffffff00000000ff1a1a1a1a1a1a1a1a
def v270 : W := 0xffffff00000000fffafafafafafafafa
def v271 : W := 0xffffff000000ff004444444444444444
def v272 : W := 0xffffff000000ff00e4e4e4e4e4e4e4e4
def v273 : W := 0xffffff000000ff00fcfcfcfcfcfcfcfc
def v274 : W := 0xffffff000000ffff1a1a1a1a1a1a1a1a
def v275 : W := 0xffffff000000ffff4444444444444444
def v276 : W := 0xffffff000000ffff5e5e5e5e5e5e5e5e
def v277 : W := 0xffffff000000fffffefefefefefefefe
def v278 : W := 0xffffff0000ff00ff1a1a1a1a1a1a1a1a
def v279 : W := 0xffffff0000ffffff1b1b1b1b1b1b1b1b
def v280 : W := 0xffffff00ff0000001818181818181818
def v281 : W := 0xffffff00ff0000002121212121212121
def v282 : W := 0xffffff00ff000000e1e1e1e1e1e1e1e1
def v283 : W := 0xffffff00ff000000f9f9f9f9f9f9f9f9
def v284 : W := 0xffffff00ff0000ff1a1a1a1a1a1a1a1a
def v285 : W := 0xffffff00ff0000ff3b3b3b3b3b3b3b3b
def v286 : W := 0xffffff00ff0000fffbfbfbfbfbfbfbfb
def v287 : W := 0xffffff00ff00ff00e5e5e5e5e5e5e5e5
def v288 : W := 0xffffff00ffffffff2121212121212121
def v289 : W := 0xffffff00ffffffff3b3b3b3b3b3b3b3b
def v290 : W := 0xffffff00ffffffffe5e5e5e5e5e5e5e5
def v291 : W := 0xffffffff000000001818181818181818
def v292 : W := 0xffffffff000000ff1a1a1a1a1a1a1a1a
def v293 : W := 0xffffffff00ff00009898989898989898
def v294 : W := 0xffffffff00ff0000f8f8f8f8f8f8f8f8
def v295 : W := 0xffffffff00ff00ff9898989898989898
def v296 : W := 0xffffffff00ff00ff9a9a9a9a9a9a9a9a
def v297 : W := 0xffffffffff0000ff1e1e1e1e1e1e1e1e
noncomputable def block_0 : Tree := (.node (3,[v20,v52,v262,v268]) (.node (3,[v12,v85,v210,v295]) (.node (2,[v115,v217,v262]) (.node (2,[v85,v217,v295]) (.node (2,[v52,v262,v295]) .nil .nil) .nil) (.node (3,[v12,v45,v262,v295]) .nil .nil)) (.node (3,[v20,v29,v276,v288]) (.node (3,[v12,v115,v210,v262]) .nil .nil) (.node (3,[v20,v52,v85,v266]) .nil .nil))) (.node (3,[v29,v52,v242,v295]) (.node (3,[v20,v85,v269,v288]) (.node (3,[v20,v85,v217,v268]) .nil .nil) (.node (3,[v20,v91,v217,v262]) .nil .nil)) (.node (3,[v29,v115,v217,v242]) (.node (3,[v29,v66,v217,v295]) .nil .nil) (.node (3,[v45,v85,v152,v295]) .nil .nil))))
noncomputable def block_1 : Tree := (.node (3,[v52,v91,v173,v262]) (.node (3,[v52,v85,v115,v198]) (.node (3,[v52,v85,v115,v142]) (.node (3,[v52,v66,v183,v295]) (.node (3,[v52,v66,v115,v182]) .nil .nil) .nil) (.node (3,[v52,v85,v115,v158]) .nil .nil)) (.node (3,[v52,v85,v142,v295]) (.node (3,[v52,v85,v116,v134]) .nil .nil) (.node (3,[v52,v86,v115,v134]) .nil .nil))) (.node (3,[v66,v115,v183,v217]) (.node (3,[v52,v143,v260,v293]) (.node (3,[v52,v115,v142,v262]) .nil .nil) (.node (3,[v66,v91,v193,v230]) .nil .nil)) (.node (3,[v85,v91,v173,v217]) (.node (3,[v66,v115,v185,v230]) .nil .nil) (.node (3,[v85,v115,v142,v217]) .nil .nil))))
noncomputable def stem_0 : Tree := .node (3,[v45,v115,v152,v262]) block_0 block_1
noncomputable def block_2 : Tree := (.node (4,[v12,v29,v66,v210,v295]) (.node (3,[v130,v131,v138,v143]) (.node (3,[v85,v115,v217,v269]) (.node (3,[v85,v115,v217,v243]) (.node (3,[v85,v115,v185,v217]) (.node (3,[v85,v115,v174,v217]) .nil .nil) .nil) (.node (3,[v85,v115,v217,v263]) .nil .nil)) (.node (3,[v85,v143,v217,v293]) (.node (3,[v85,v115,v217,v296]) .nil .nil) (.node (3,[v115,v143,v217,v260]) .nil .nil))) (.node (4,[v12,v20,v85,v210,v268]) (.node (4,[v12,v20,v29,v276,v281]) (.node (4,[v9,v52,v85,v115,v134]) .nil .nil) (.node (4,[v12,v20,v45,v262,v268]) .nil .nil)) (.node (4,[v12,v20,v91,v210,v262]) (.node (4,[v12,v20,v85,v269,v281]) .nil .nil) (.node (4,[v12,v29,v45,v242,v295]) .nil .nil)))) (.node (4,[v12,v45,v91,v173,v262]) (.node (4,[v12,v45,v85,v115,v142]) (.node (4,[v12,v36,v56,v241,v269]) (.node (4,[v12,v29,v115,v210,v242]) .nil .nil) (.node (4,[v12,v45,v66,v183,v295]) .nil .nil)) (.node (4,[v12,v45,v85,v142,v295]) (.node (4,[v12,v45,v85,v116,v134]) .nil .nil) (.node (4,[v12,v45,v86,v115,v134]) .nil .nil))) (.node (4,[v12,v66,v91,v193,v223]) (.node (4,[v12,v45,v143,v260,v293]) (.node (4,[v12,v45,v115,v142,v262]) .nil .nil) (.node (4,[v12,v52,v85,v115,v142]) .nil .nil)) (.node (4,[v12,v66,v115,v185,v223]) (.node (4,[v12,v66,v115,v183,v210]) .nil .nil) (.node (4,[v12,v85,v91,v173,v210]) .nil .nil)))))
noncomputable def stem_1 : Tree := .node (3,[v85,v115,v143,v217]) stem_0 block_2
noncomputable def block_3 : Tree := (.node (4,[v12,v85,v115,v205,v296]) (.node (4,[v12,v85,v115,v185,v205]) (.node (4,[v12,v85,v115,v143,v217]) (.node (4,[v12,v85,v115,v143,v210]) (.node (4,[v12,v85,v115,v143,v205]) .nil .nil) .nil) (.node (4,[v12,v85,v115,v174,v205]) .nil .nil)) (.node (4,[v12,v85,v115,v205,v263]) (.node (4,[v12,v85,v115,v205,v243]) .nil .nil) (.node (4,[v12,v85,v115,v205,v269]) .nil .nil))) (.node (4,[v12,v115,v143,v205,v260]) (.node (4,[v12,v85,v143,v205,v293]) (.node (4,[v12,v85,v115,v209,v297]) .nil .nil) (.node (4,[v12,v97,v103,v172,v185]) .nil .nil)) (.node (4,[v20,v29,v45,v247,v276]) (.node (4,[v12,v121,v130,v138,v143]) .nil .nil) (.node (4,[v20,v29,v51,v241,v269]) .nil .nil))))
noncomputable def block_4 : Tree := (.node (4,[v20,v29,v52,v269,v271]) (.node (4,[v20,v29,v52,v239,v269]) (.node (4,[v20,v29,v52,v237,v269]) (.node (4,[v20,v29,v52,v236,v269]) (.node (4,[v20,v29,v52,v233,v276]) .nil .nil) .nil) (.node (4,[v20,v29,v52,v237,v296]) .nil .nil)) (.node (4,[v20,v29,v52,v242,v268]) (.node (4,[v20,v29,v52,v241,v274]) .nil .nil) (.node (4,[v20,v29,v52,v242,v269]) .nil .nil))) (.node (4,[v20,v29,v66,v217,v269]) (.node (4,[v20,v29,v66,v216,v269]) (.node (4,[v20,v29,v52,v269,v275]) .nil .nil) (.node (4,[v20,v29,v66,v217,v268]) .nil .nil)) (.node (4,[v20,v29,v66,v269,v288]) (.node (4,[v20,v29,v66,v217,v296]) .nil .nil) (.node (4,[v20,v29,v73,v209,v274]) .nil .nil))))
noncomputable def stem_2 : Tree := .node (4,[v20,v29,v52,v66,v266]) block_3 block_4
noncomputable def block_5 : Tree := (.node (4,[v20,v52,v85,v219,v268]) (.node (4,[v20,v52,v85,v91,v142]) (.node (4,[v20,v45,v91,v152,v262]) (.node (4,[v20,v45,v85,v152,v268]) (.node (4,[v20,v33,v52,v241,v269]) (.node (4,[v20,v29,v217,v237,v269]) .nil .nil) .nil) (.node (4,[v20,v45,v85,v247,v269]) .nil .nil)) (.node (4,[v20,v52,v66,v183,v268]) (.node (4,[v20,v52,v66,v91,v182]) .nil .nil) (.node (4,[v20,v52,v84,v138,v269]) .nil .nil))) (.node (4,[v20,v52,v85,v115,v142]) (.node (4,[v20,v52,v85,v91,v198]) (.node (4,[v20,v52,v85,v91,v158]) .nil .nil) (.node (4,[v20,v52,v85,v94,v134]) .nil .nil)) (.node (4,[v20,v52,v85,v142,v268]) (.node (4,[v20,v52,v85,v138,v268]) .nil .nil) (.node (4,[v20,v52,v85,v155,v268]) .nil .nil)))) (.node (4,[v20,v52,v86,v91,v134]) (.node (4,[v20,v52,v85,v241,v269]) (.node (4,[v20,v52,v85,v234,v269]) (.node (4,[v20,v52,v85,v233,v269]) .nil .nil) (.node (4,[v20,v52,v85,v237,v269]) .nil .nil)) (.node (4,[v20,v52,v85,v269,v287]) (.node (4,[v20,v52,v85,v248,v269]) .nil .nil) (.node (4,[v20,v52,v85,v269,v290]) .nil .nil))) (.node (4,[v20,v52,v185,v237,v264]) (.node (4,[v20,v52,v143,v260,v264]) (.node (4,[v20,v52,v91,v142,v262]) .nil .nil) (.node (4,[v20,v52,v180,v237,v269]) .nil .nil)) (.node (4,[v20,v52,v237,v260,v269]) (.node (4,[v20,v52,v185,v237,v269]) .nil .nil) (.node (4,[v20,v52,v241,v263,v269]) .nil .nil)))))
noncomputable def stem_3 : Tree := .node (4,[v20,v29,v91,v217,v242]) stem_2 block_5
noncomputable def stem_4 : Tree := .node (4,[v12,v85,v115,v142,v210]) stem_1 stem_3
noncomputable def block_6 : Tree := (.node (4,[v20,v66,v185,v217,v269]) (.node (4,[v20,v66,v91,v217,v263]) (.node (4,[v20,v66,v91,v185,v217]) (.node (4,[v20,v66,v91,v185,v216]) (.node (4,[v20,v66,v91,v183,v217]) .nil .nil) .nil) (.node (4,[v20,v66,v91,v185,v230]) .nil .nil)) (.node (4,[v20,v66,v180,v217,v269]) (.node (4,[v20,v66,v115,v185,v217]) .nil .nil) (.node (4,[v20,v66,v185,v217,v264]) .nil .nil))) (.node (4,[v20,v85,v91,v185,v217]) (.node (4,[v20,v85,v91,v143,v217]) (.node (4,[v20,v85,v91,v142,v217]) .nil .nil) (.node (4,[v20,v85,v91,v174,v217]) .nil .nil)) (.node (4,[v20,v85,v91,v217,v263]) (.node (4,[v20,v85,v91,v217,v243]) .nil .nil) (.node (4,[v20,v85,v91,v217,v269]) .nil .nil))))
noncomputable def block_7 : Tree := (.node (4,[v25,v29,v73,v209,v269]) (.node (4,[v20,v91,v185,v217,v237]) (.node (4,[v20,v85,v143,v217,v264]) (.node (4,[v20,v85,v115,v143,v217]) (.node (4,[v20,v85,v109,v219,v269]) .nil .nil) .nil) (.node (4,[v20,v91,v143,v217,v260]) .nil .nil)) (.node (4,[v24,v52,v85,v91,v134]) (.node (4,[v20,v97,v108,v138,v185]) .nil .nil) (.node (4,[v25,v29,v52,v241,v269]) .nil .nil))) (.node (4,[v29,v45,v66,v152,v295]) (.node (4,[v27,v66,v91,v191,v209]) (.node (4,[v26,v36,v45,v241,v269]) .nil .nil) (.node (4,[v27,v71,v91,v185,v209]) .nil .nil)) (.node (4,[v29,v52,v66,v115,v142]) (.node (4,[v29,v45,v115,v152,v242]) .nil .nil) (.node (4,[v29,v52,v66,v115,v158]) .nil .nil))))
noncomputable def stem_5 : Tree := .node (4,[v20,v85,v108,v138,v269]) block_6 block_7
noncomputable def block_8 : Tree := (.node (4,[v29,v66,v115,v174,v217]) (.node (4,[v29,v52,v115,v174,v237]) (.node (4,[v29,v52,v91,v173,v242]) (.node (4,[v29,v52,v70,v115,v134]) (.node (4,[v29,v52,v66,v142,v295]) (.node (4,[v29,v52,v66,v116,v134]) .nil .nil) .nil) (.node (4,[v29,v52,v85,v115,v142]) .nil .nil)) (.node (4,[v29,v52,v115,v143,v237]) (.node (4,[v29,v52,v115,v142,v242]) .nil .nil) (.node (4,[v29,v52,v115,v143,v242]) .nil .nil))) (.node (4,[v29,v52,v168,v237,v269]) (.node (4,[v29,v52,v115,v237,v296]) (.node (4,[v29,v52,v115,v237,v269]) .nil .nil) (.node (4,[v29,v52,v143,v237,v293]) .nil .nil)) (.node (4,[v29,v66,v115,v142,v217]) (.node (4,[v29,v66,v91,v173,v217]) .nil .nil) (.node (4,[v29,v66,v115,v143,v217]) .nil .nil)))) (.node (4,[v29,v115,v143,v217,v237]) (.node (4,[v29,v66,v115,v217,v296]) (.node (4,[v29,v66,v115,v217,v243]) (.node (4,[v29,v66,v115,v185,v217]) .nil .nil) (.node (4,[v29,v66,v115,v217,v269]) .nil .nil)) (.node (4,[v29,v66,v168,v217,v269]) (.node (4,[v29,v66,v143,v217,v293]) .nil .nil) (.node (4,[v29,v85,v115,v143,v217]) .nil .nil))) (.node (4,[v45,v66,v91,v178,v193]) (.node (4,[v36,v61,v66,v138,v269]) (.node (4,[v32,v52,v66,v115,v134]) .nil .nil) (.node (4,[v45,v52,v85,v115,v142]) .nil .nil)) (.node (4,[v45,v66,v115,v178,v185]) (.node (4,[v45,v66,v115,v152,v183]) .nil .nil) (.node (4,[v45,v72,v97,v172,v185]) .nil .nil)))))
noncomputable def stem_6 : Tree := .node (4,[v29,v52,v66,v115,v198]) stem_5 block_8
noncomputable def block_9 : Tree := (.node (4,[v52,v66,v85,v115,v142]) (.node (4,[v45,v85,v115,v152,v243]) (.node (4,[v45,v85,v115,v143,v217]) (.node (4,[v45,v85,v115,v143,v152]) (.node (4,[v45,v85,v115,v142,v152]) (.node (4,[v45,v85,v91,v152,v173]) .nil .nil) .nil) (.node (4,[v45,v85,v115,v143,v154]) .nil .nil)) (.node (4,[v45,v85,v115,v152,v174]) (.node (4,[v45,v85,v115,v147,v152]) .nil .nil) (.node (4,[v45,v85,v115,v152,v185]) .nil .nil))) (.node (4,[v45,v85,v143,v152,v293]) (.node (4,[v45,v85,v115,v152,v269]) (.node (4,[v45,v85,v115,v152,v263]) .nil .nil) (.node (4,[v45,v85,v115,v152,v296]) .nil .nil)) (.node (4,[v51,v66,v91,v172,v185]) (.node (4,[v45,v115,v143,v152,v260]) .nil .nil) (.node (4,[v51,v85,v115,v138,v143]) .nil .nil)))) (.node (4,[v52,v66,v91,v173,v185]) (.node (4,[v52,v66,v91,v168,v263]) (.node (4,[v52,v66,v91,v167,v185]) (.node (4,[v52,v66,v91,v164,v193]) .nil .nil) (.node (4,[v52,v66,v91,v168,v185]) .nil .nil)) (.node (4,[v52,v66,v91,v172,v191]) (.node (4,[v52,v66,v91,v170,v185]) .nil .nil) (.node (4,[v52,v66,v91,v173,v183]) .nil .nil))) (.node (4,[v52,v66,v114,v138,v185]) (.node (4,[v52,v66,v91,v185,v192]) (.node (4,[v52,v66,v91,v185,v188]) .nil .nil) (.node (4,[v52,v66,v99,v172,v185]) .nil .nil)) (.node (4,[v52,v66,v115,v142,v183]) (.node (4,[v52,v66,v115,v138,v183]) .nil .nil) (.node (4,[v52,v66,v115,v155,v183]) .nil .nil)))))
noncomputable def block_10 : Tree := (.node (4,[v52,v78,v85,v138,v269]) (.node (4,[v52,v66,v168,v180,v269]) (.node (4,[v52,v66,v115,v183,v219]) (.node (4,[v52,v66,v115,v172,v185]) (.node (4,[v52,v66,v115,v168,v185]) (.node (4,[v52,v66,v115,v165,v185]) .nil .nil) .nil) (.node (4,[v52,v66,v115,v179,v185]) .nil .nil)) (.node (4,[v52,v66,v115,v185,v232]) (.node (4,[v52,v66,v115,v185,v229]) .nil .nil) (.node (4,[v52,v66,v143,v180,v293]) .nil .nil))) (.node (4,[v52,v66,v172,v185,v296]) (.node (4,[v52,v66,v168,v185,v269]) (.node (4,[v52,v66,v168,v185,v264]) .nil .nil) (.node (4,[v52,v66,v168,v185,v293]) .nil .nil)) (.node (4,[v52,v76,v130,v138,v143]) (.node (4,[v52,v71,v91,v172,v185]) .nil .nil) (.node (4,[v52,v77,v115,v138,v185]) .nil .nil)))) (.node (4,[v52,v85,v91,v168,v185]) (.node (4,[v52,v85,v91,v115,v142]) (.node (4,[v52,v83,v115,v138,v143]) (.node (4,[v52,v82,v115,v138,v143]) .nil .nil) (.node (4,[v52,v84,v115,v138,v143]) .nil .nil)) (.node (4,[v52,v85,v91,v143,v168]) (.node (4,[v52,v85,v91,v142,v173]) .nil .nil) (.node (4,[v52,v85,v91,v143,v173]) .nil .nil))) (.node (4,[v52,v85,v113,v138,v143]) (.node (4,[v52,v85,v91,v168,v263]) (.node (4,[v52,v85,v91,v168,v243]) .nil .nil) (.node (4,[v52,v85,v112,v138,v143]) .nil .nil)) (.node (4,[v52,v85,v115,v134,v143]) (.node (4,[v52,v85,v114,v138,v143]) .nil .nil) (.node (4,[v52,v85,v115,v134,v174]) .nil .nil)))))
noncomputable def stem_7 : Tree := .node (4,[v52,v66,v115,v164,v185]) block_9 block_10
noncomputable def stem_8 : Tree := .node (4,[v45,v80,v130,v138,v143]) stem_6 stem_7
noncomputable def stem_9 : Tree := .node (4,[v20,v66,v85,v217,v269]) stem_4 stem_8
noncomputable def block_11 : Tree := (.node (4,[v52,v85,v115,v138,v143]) (.node (4,[v52,v85,v115,v135,v143]) (.node (4,[v52,v85,v115,v134,v269]) (.node (4,[v52,v85,v115,v134,v263]) (.node (4,[v52,v85,v115,v134,v243]) .nil .nil) .nil) (.node (4,[v52,v85,v115,v134,v296]) .nil .nil)) (.node (4,[v52,v85,v115,v137,v143]) (.node (4,[v52,v85,v115,v136,v143]) .nil .nil) (.node (4,[v52,v85,v115,v138,v142]) .nil .nil))) (.node (4,[v52,v85,v115,v138,v151]) (.node (4,[v52,v85,v115,v138,v145]) (.node (4,[v52,v85,v115,v138,v144]) .nil .nil) (.node (4,[v52,v85,v115,v138,v149]) .nil .nil)) (.node (4,[v52,v85,v115,v138,v162]) (.node (4,[v52,v85,v115,v138,v159]) .nil .nil) (.node (4,[v52,v85,v115,v138,v166]) .nil .nil))))
noncomputable def block_12 : Tree := (.node (4,[v52,v85,v115,v141,v143]) (.node (4,[v52,v85,v115,v138,v269]) (.node (4,[v52,v85,v115,v138,v235]) (.node (4,[v52,v85,v115,v138,v202]) (.node (4,[v52,v85,v115,v138,v199]) .nil .nil) .nil) (.node (4,[v52,v85,v115,v138,v252]) .nil .nil)) (.node (4,[v52,v85,v115,v139,v143]) (.node (4,[v52,v85,v115,v138,v297]) .nil .nil) (.node (4,[v52,v85,v115,v140,v143]) .nil .nil))) (.node (4,[v52,v85,v115,v142,v219]) (.node (4,[v52,v85,v115,v142,v143]) (.node (4,[v52,v85,v115,v142]) .nil .nil) (.node (4,[v52,v85,v115,v142,v155]) .nil .nil)) (.node (4,[v52,v85,v115,v143,v148]) (.node (4,[v52,v85,v115,v143,v146]) .nil .nil) (.node (4,[v52,v85,v115,v143,v150]) .nil .nil))))
noncomputable def stem_10 : Tree := .node (4,[v52,v85,v115,v138,v185]) block_11 block_12
noncomputable def block_13 : Tree := (.node (4,[v52,v85,v115,v143,v237]) (.node (4,[v52,v85,v115,v143,v201]) (.node (4,[v52,v85,v115,v143,v168]) (.node (4,[v52,v85,v115,v143,v161]) (.node (4,[v52,v85,v115,v143,v157]) (.node (4,[v52,v85,v115,v143,v155]) .nil .nil) .nil) (.node (4,[v52,v85,v115,v143,v165]) .nil .nil)) (.node (4,[v52,v85,v115,v143,v179]) (.node (4,[v52,v85,v115,v143,v172]) .nil .nil) (.node (4,[v52,v85,v115,v143,v197]) .nil .nil))) (.node (4,[v52,v85,v115,v143,v219]) (.node (4,[v52,v85,v115,v143,v209]) (.node (4,[v52,v85,v115,v143,v205]) .nil .nil) (.node (4,[v52,v85,v115,v143,v217]) .nil .nil)) (.node (4,[v52,v85,v115,v143,v232]) (.node (4,[v52,v85,v115,v143,v229]) .nil .nil) (.node (4,[v52,v85,v115,v143,v234]) .nil .nil)))) (.node (4,[v52,v85,v115,v155,v269]) (.node (4,[v52,v85,v115,v143,v257]) (.node (4,[v52,v85,v115,v143,v248]) (.node (4,[v52,v85,v115,v143,v241]) .nil .nil) (.node (4,[v52,v85,v115,v143,v251]) .nil .nil)) (.node (4,[v52,v85,v115,v143,v290]) (.node (4,[v52,v85,v115,v143,v287]) .nil .nil) (.node (4,[v52,v85,v115,v155,v185]) .nil .nil))) (.node (4,[v52,v85,v115,v209,v269]) (.node (4,[v52,v85,v115,v185,v209]) (.node (4,[v52,v85,v115,v172,v185]) .nil .nil) (.node (4,[v52,v85,v115,v185,v219]) .nil .nil)) (.node (4,[v52,v85,v115,v241,v269]) (.node (4,[v52,v85,v115,v219,v269]) .nil .nil) (.node (4,[v52,v85,v116,v138,v143]) .nil .nil)))))
noncomputable def stem_11 : Tree := .node (4,[v52,v85,v115,v143,v152]) stem_10 block_13
noncomputable def block_14 : Tree := (.node (4,[v52,v91,v143,v168,v260]) (.node (4,[v52,v85,v143,v168,v264]) (.node (4,[v52,v85,v134,v143,v293]) (.node (4,[v52,v85,v129,v138,v143]) (.node (4,[v52,v85,v125,v138,v143]) .nil .nil) .nil) (.node (4,[v52,v85,v138,v143,v293]) .nil .nil)) (.node (4,[v52,v86,v115,v138,v143]) (.node (4,[v52,v85,v143,v168,v293]) .nil .nil) (.node (4,[v52,v87,v115,v138,v143]) .nil .nil))) (.node (4,[v52,v115,v134,v143,v260]) (.node (4,[v52,v115,v122,v138,v143]) (.node (4,[v52,v91,v168,v185,v237]) .nil .nil) (.node (4,[v52,v115,v128,v138,v143]) .nil .nil)) (.node (4,[v52,v115,v143,v180,v237]) (.node (4,[v52,v115,v138,v143,v260]) .nil .nil) (.node (4,[v52,v115,v143,v237,v260]) .nil .nil))))
noncomputable def block_15 : Tree := (.node (4,[v85,v108,v115,v138,v143]) (.node (4,[v66,v91,v168,v185,v217]) (.node (4,[v62,v85,v115,v143,v219]) (.node (4,[v62,v66,v115,v185,v219]) (.node (4,[v61,v85,v115,v138,v143]) .nil .nil) .nil) (.node (4,[v66,v85,v115,v143,v217]) .nil .nil)) (.node (4,[v85,v91,v115,v143,v217]) (.node (4,[v66,v115,v143,v180,v217]) .nil .nil) (.node (4,[v85,v91,v143,v168,v217]) .nil .nil))) (.node (4,[v85,v115,v138,v143,v217]) (.node (4,[v85,v115,v131,v138,v143]) (.node (4,[v85,v109,v115,v143,v219]) .nil .nil) (.node (4,[v85,v115,v134,v143,v217]) .nil .nil)) (.node (4,[v85,v115,v143,v152,v217]) (.node (4,[v85,v115,v143,v152,v205]) .nil .nil) (.node (4,[v85,v115,v143,v205,v217]) .nil .nil))))
noncomputable def stem_12 : Tree := .node (4,[v61,v66,v115,v138,v185]) block_14 block_15
noncomputable def block_16 : Tree := (.node (5,[v10,v52,v85,v115,v138,v143]) (.node (5,[v7,v52,v85,v115,v138,v143]) (.node (5,[v3,v52,v85,v115,v138,v143]) (.node (5,[v1,v52,v85,v115,v138,v143]) (.node (5,[v0,v52,v85,v115,v138,v143]) (.node (4,[v85,v115,v143,v218,v219]) .nil .nil) .nil) (.node (5,[v2,v52,v85,v115,v138,v143]) .nil .nil)) (.node (5,[v5,v52,v85,v115,v138,v143]) (.node (5,[v4,v52,v85,v115,v138,v143]) .nil .nil) (.node (5,[v6,v52,v85,v115,v138,v143]) .nil .nil))) (.node (5,[v9,v29,v52,v66,v115,v134]) (.node (5,[v9,v12,v45,v85,v115,v134]) (.node (5,[v8,v52,v85,v115,v138,v143]) .nil .nil) (.node (5,[v9,v20,v52,v85,v91,v134]) .nil .nil)) (.node (5,[v10,v20,v29,v52,v241,v269]) (.node (5,[v9,v52,v85,v115,v138,v143]) .nil .nil) (.node (5,[v10,v20,v29,v73,v209,v269]) .nil .nil)))) (.node (5,[v12,v20,v28,v45,v241,v269]) (.node (5,[v12,v18,v36,v45,v241,v269]) (.node (5,[v11,v52,v66,v91,v172,v185]) (.node (5,[v11,v27,v66,v91,v185,v209]) .nil .nil) (.node (5,[v11,v52,v85,v115,v138,v143]) .nil .nil)) (.node (5,[v12,v19,v29,v66,v209,v269]) (.node (5,[v12,v19,v29,v45,v241,v269]) .nil .nil) (.node (5,[v12,v19,v66,v91,v185,v209]) .nil .nil))) (.node (5,[v12,v20,v29,v45,v236,v269]) (.node (5,[v12,v20,v29,v44,v241,v269]) (.node (5,[v12,v20,v28,v66,v209,v269]) .nil .nil) (.node (5,[v12,v20,v29,v45,v233,v276]) .nil .nil)) (.node (5,[v12,v20,v29,v45,v237,v296]) (.node (5,[v12,v20,v29,v45,v237,v269]) .nil .nil) (.node (5,[v12,v20,v29,v45,v238,v269]) .nil .nil)))))
noncomputable def stem_13 : Tree := .node (4,[v85,v115,v143,v217]) stem_12 block_16
noncomputable def stem_14 : Tree := .node (4,[v52,v85,v117,v138,v143]) stem_11 stem_13
noncomputable def block_17 : Tree := (.node (5,[v12,v20,v29,v45,v242,v268]) (.node (5,[v12,v20,v29,v45,v241,v274]) (.node (5,[v12,v20,v29,v45,v241,v268]) (.node (5,[v12,v20,v29,v45,v241,v267]) (.node (5,[v12,v20,v29,v45,v240,v269]) .nil .nil) .nil) (.node (5,[v12,v20,v29,v45,v241,v269]) .nil .nil)) (.node (5,[v12,v20,v29,v45,v241,v284]) (.node (5,[v12,v20,v29,v45,v241,v278]) .nil .nil) (.node (5,[v12,v20,v29,v45,v241,v292]) .nil .nil))) (.node (5,[v12,v20,v29,v45,v250,v269]) (.node (5,[v12,v20,v29,v45,v244,v269]) (.node (5,[v12,v20,v29,v45,v242,v269]) .nil .nil) (.node (5,[v12,v20,v29,v45,v246,v269]) .nil .nil)) (.node (5,[v12,v20,v29,v45,v269,v271]) (.node (5,[v12,v20,v29,v45,v254,v269]) .nil .nil) (.node (5,[v12,v20,v29,v45,v269,v272]) .nil .nil))))
noncomputable def block_18 : Tree := (.node (5,[v12,v20,v29,v66,v204,v269]) (.node (5,[v12,v20,v29,v52,v237,v269]) (.node (5,[v12,v20,v29,v49,v241,v269]) (.node (5,[v12,v20,v29,v48,v241,v269]) (.node (5,[v12,v20,v29,v47,v241,v269]) .nil .nil) .nil) (.node (5,[v12,v20,v29,v50,v241,v269]) .nil .nil)) (.node (5,[v12,v20,v29,v56,v241,v269]) (.node (5,[v12,v20,v29,v52,v241,v269]) .nil .nil) (.node (5,[v12,v20,v29,v65,v209,v269]) .nil .nil))) (.node (5,[v12,v20,v29,v66,v207,v269]) (.node (5,[v12,v20,v29,v66,v205,v296]) (.node (5,[v12,v20,v29,v66,v205,v269]) .nil .nil) (.node (5,[v12,v20,v29,v66,v206,v269]) .nil .nil)) (.node (5,[v12,v20,v29,v66,v209,v267]) (.node (5,[v12,v20,v29,v66,v208,v269]) .nil .nil) (.node (5,[v12,v20,v29,v66,v209,v268]) .nil .nil))))
noncomputable def stem_15 : Tree := .node (5,[v12,v20,v29,v46,v241,v269]) block_17 block_18
noncomputable def block_19 : Tree := (.node (5,[v12,v20,v29,v69,v209,v269]) (.node (5,[v12,v20,v29,v66,v215,v269]) (.node (5,[v12,v20,v29,v66,v210,v268]) (.node (5,[v12,v20,v29,v66,v209,v284]) (.node (5,[v12,v20,v29,v66,v209,v278]) (.node (5,[v12,v20,v29,v66,v209,v274]) .nil .nil) .nil) (.node (5,[v12,v20,v29,v66,v209,v292]) .nil .nil)) (.node (5,[v12,v20,v29,v66,v212,v269]) (.node (5,[v12,v20,v29,v66,v210,v269]) .nil .nil) (.node (5,[v12,v20,v29,v66,v214,v269]) .nil .nil))) (.node (5,[v12,v20,v29,v66,v224,v269]) (.node (5,[v12,v20,v29,v66,v219,v268]) (.node (5,[v12,v20,v29,v66,v217,v269]) .nil .nil) (.node (5,[v12,v20,v29,v66,v219,v269]) .nil .nil)) (.node (5,[v12,v20,v29,v66,v269,v282]) (.node (5,[v12,v20,v29,v66,v269,v281]) .nil .nil) (.node (5,[v12,v20,v29,v68,v209,v269]) .nil .nil)))) (.node (5,[v12,v20,v29,v205,v237,v269]) (.node (5,[v12,v20,v29,v77,v209,v269]) (.node (5,[v12,v20,v29,v71,v209,v269]) (.node (5,[v12,v20,v29,v70,v209,v269]) .nil .nil) (.node (5,[v12,v20,v29,v74,v209,v269]) .nil .nil)) (.node (5,[v12,v20,v29,v96,v209,v269]) (.node (5,[v12,v20,v29,v91,v210,v242]) .nil .nil) (.node (5,[v12,v20,v29,v103,v241,v269]) .nil .nil))) (.node (5,[v12,v20,v29,v209,v269,v271]) (.node (5,[v12,v20,v29,v209,v237,v269]) (.node (5,[v12,v20,v29,v205,v241,v269]) .nil .nil) (.node (5,[v12,v20,v29,v209,v241,v269]) .nil .nil)) (.node (5,[v12,v20,v29,v241,v269,v281]) (.node (5,[v12,v20,v29,v219,v241,v269]) .nil .nil) (.node (5,[v12,v20,v30,v45,v241,v269]) .nil .nil)))))
noncomputable def stem_16 : Tree := .node (5,[v12,v20,v29,v66,v209,v269]) stem_15 block_19
noncomputable def block_20 : Tree := (.node (5,[v12,v20,v45,v85,v155,v268]) (.node (5,[v12,v20,v45,v66,v183,v268]) (.node (5,[v12,v20,v33,v66,v209,v269]) (.node (5,[v12,v20,v32,v66,v209,v269]) (.node (5,[v12,v20,v32,v45,v241,v269]) (.node (5,[v12,v20,v31,v45,v241,v269]) .nil .nil) .nil) (.node (5,[v12,v20,v33,v45,v241,v269]) .nil .nil)) (.node (5,[v12,v20,v34,v66,v209,v269]) (.node (5,[v12,v20,v34,v45,v241,v269]) .nil .nil) (.node (5,[v12,v20,v45,v55,v241,v269]) .nil .nil))) (.node (5,[v12,v20,v45,v85,v94,v134]) (.node (5,[v12,v20,v45,v84,v138,v269]) (.node (5,[v12,v20,v45,v81,v241,v269]) .nil .nil) (.node (5,[v12,v20,v45,v85,v91,v142]) .nil .nil)) (.node (5,[v12,v20,v45,v85,v138,v268]) (.node (5,[v12,v20,v45,v85,v115,v142]) .nil .nil) (.node (5,[v12,v20,v45,v85,v142,v268]) .nil .nil)))) (.node (5,[v12,v20,v45,v91,v142,v262]) (.node (5,[v12,v20,v45,v85,v241,v269]) (.node (5,[v12,v20,v45,v85,v234,v269]) (.node (5,[v12,v20,v45,v85,v233,v269]) .nil .nil) (.node (5,[v12,v20,v45,v85,v237,v269]) .nil .nil)) (.node (5,[v12,v20,v45,v85,v269,v287]) (.node (5,[v12,v20,v45,v85,v248,v269]) .nil .nil) (.node (5,[v12,v20,v45,v86,v91,v134]) .nil .nil))) (.node (5,[v12,v20,v45,v180,v237,v269]) (.node (5,[v12,v20,v45,v91,v185,v240]) (.node (5,[v12,v20,v45,v91,v184,v241]) .nil .nil) (.node (5,[v12,v20,v45,v143,v260,v264]) .nil .nil)) (.node (5,[v12,v20,v45,v185,v237,v264]) (.node (5,[v12,v20,v45,v180,v241,v269]) .nil .nil) (.node (5,[v12,v20,v45,v185,v237,v269]) .nil .nil)))))
noncomputable def block_21 : Tree := (.node (5,[v12,v20,v66,v91,v184,v209]) (.node (5,[v12,v20,v57,v102,v143,v241]) (.node (5,[v12,v20,v52,v85,v91,v142]) (.node (5,[v12,v20,v45,v241,v258,v269]) (.node (5,[v12,v20,v45,v237,v260,v269]) (.node (5,[v12,v20,v45,v185,v241,v269]) .nil .nil) .nil) (.node (5,[v12,v20,v45,v241,v263,v269]) .nil .nil)) (.node (5,[v12,v20,v52,v185,v241,v269]) (.node (5,[v12,v20,v52,v85,v241,v269]) .nil .nil) (.node (5,[v12,v20,v55,v66,v209,v269]) .nil .nil))) (.node (5,[v12,v20,v66,v90,v185,v209]) (.node (5,[v12,v20,v66,v81,v209,v269]) (.node (5,[v12,v20,v65,v91,v185,v209]) .nil .nil) (.node (5,[v12,v20,v66,v85,v205,v269]) .nil .nil)) (.node (5,[v12,v20,v66,v91,v183,v210]) (.node (5,[v12,v20,v66,v91,v183,v209]) .nil .nil) (.node (5,[v12,v20,v66,v91,v183,v219]) .nil .nil)))) (.node (5,[v12,v20,v66,v91,v185,v212]) (.node (5,[v12,v20,v66,v91,v185,v207]) (.node (5,[v12,v20,v66,v91,v185,v205]) (.node (5,[v12,v20,v66,v91,v185,v204]) .nil .nil) (.node (5,[v12,v20,v66,v91,v185,v206]) .nil .nil)) (.node (5,[v12,v20,v66,v91,v185,v209]) (.node (5,[v12,v20,v66,v91,v185,v208]) .nil .nil) (.node (5,[v12,v20,v66,v91,v185,v210]) .nil .nil))) (.node (5,[v12,v20,v66,v91,v185,v219]) (.node (5,[v12,v20,v66,v91,v185,v215]) (.node (5,[v12,v20,v66,v91,v185,v214]) .nil .nil) (.node (5,[v12,v20,v66,v91,v185,v217]) .nil .nil)) (.node (5,[v12,v20,v66,v91,v185,v224]) (.node (5,[v12,v20,v66,v91,v185,v223]) .nil .nil) (.node (5,[v12,v20,v66,v91,v185,v282]) .nil .nil)))))
noncomputable def stem_17 : Tree := .node (5,[v12,v20,v45,v185,v241,v264]) block_20 block_21
noncomputable def stem_18 : Tree := .node (5,[v12,v20,v30,v66,v209,v269]) stem_16 stem_17
noncomputable def stem_19 : Tree := .node (5,[v12,v20,v29,v45,v239,v269]) stem_14 stem_18
noncomputable def stem_20 : Tree := .node (4,[v52,v85,v115,v134,v185]) stem_9 stem_19
noncomputable def block_22 : Tree := (.node (5,[v12,v20,v66,v102,v185,v209]) (.node (5,[v12,v20,v66,v92,v185,v209]) (.node (5,[v12,v20,v66,v91,v209,v226]) (.node (5,[v12,v20,v66,v91,v205,v263]) (.node (5,[v12,v20,v66,v91,v191,v209]) .nil .nil) .nil) (.node (5,[v12,v20,v66,v91,v209,v259]) .nil .nil)) (.node (5,[v12,v20,v66,v95,v185,v209]) (.node (5,[v12,v20,v66,v94,v185,v209]) .nil .nil) (.node (5,[v12,v20,v66,v99,v185,v209]) .nil .nil))) (.node (5,[v12,v20,v66,v180,v209,v269]) (.node (5,[v12,v20,v66,v115,v185,v205]) (.node (5,[v12,v20,v66,v111,v185,v209]) .nil .nil) (.node (5,[v12,v20,v66,v180,v205,v269]) .nil .nil)) (.node (5,[v12,v20,v66,v185,v205,v269]) (.node (5,[v12,v20,v66,v185,v205,v264]) .nil .nil) (.node (5,[v12,v20,v66,v185,v209,v264]) .nil .nil))))
noncomputable def block_23 : Tree := (.node (5,[v12,v20,v74,v91,v185,v209]) (.node (5,[v12,v20,v68,v91,v185,v209]) (.node (5,[v12,v20,v66,v209,v222,v269]) (.node (5,[v12,v20,v66,v185,v219,v269]) (.node (5,[v12,v20,v66,v185,v209,v280]) .nil .nil) .nil) (.node (5,[v12,v20,v67,v91,v185,v209]) .nil .nil)) (.node (5,[v12,v20,v70,v91,v185,v209]) (.node (5,[v12,v20,v69,v91,v185,v209]) .nil .nil) (.node (5,[v12,v20,v71,v91,v185,v209]) .nil .nil))) (.node (5,[v12,v20,v85,v91,v143,v205]) (.node (5,[v12,v20,v83,v91,v143,v209]) (.node (5,[v12,v20,v77,v91,v185,v209]) .nil .nil) (.node (5,[v12,v20,v85,v91,v142,v210]) .nil .nil)) (.node (5,[v12,v20,v85,v91,v143,v210]) (.node (5,[v12,v20,v85,v91,v143,v207]) .nil .nil) (.node (5,[v12,v20,v85,v91,v143,v217]) .nil .nil))))
noncomputable def stem_21 : Tree := .node (5,[v12,v20,v66,v185,v209,v269]) block_22 block_23
noncomputable def block_24 : Tree := (.node (5,[v12,v20,v91,v185,v205,v241]) (.node (5,[v12,v20,v85,v102,v143,v209]) (.node (5,[v12,v20,v85,v91,v205,v243]) (.node (5,[v12,v20,v85,v91,v185,v209]) (.node (5,[v12,v20,v85,v91,v185,v205]) (.node (5,[v12,v20,v85,v91,v174,v205]) .nil .nil) .nil) (.node (5,[v12,v20,v85,v91,v185,v219]) .nil .nil)) (.node (5,[v12,v20,v85,v91,v205,v269]) (.node (5,[v12,v20,v85,v91,v205,v263]) .nil .nil) (.node (5,[v12,v20,v85,v91,v209,v297]) .nil .nil))) (.node (5,[v12,v20,v85,v143,v205,v264]) (.node (5,[v12,v20,v85,v104,v209,v269]) (.node (5,[v12,v20,v85,v103,v138,v269]) .nil .nil) (.node (5,[v12,v20,v85,v115,v143,v205]) .nil .nil)) (.node (5,[v12,v20,v91,v143,v205,v260]) (.node (5,[v12,v20,v91,v96,v185,v209]) .nil .nil) (.node (5,[v12,v20,v91,v185,v205,v237]) .nil .nil)))) (.node (5,[v12,v20,v185,v209,v241,v269]) (.node (5,[v12,v20,v91,v185,v209,v261]) (.node (5,[v12,v20,v91,v185,v209,v241]) (.node (5,[v12,v20,v91,v185,v209,v237]) .nil .nil) (.node (5,[v12,v20,v91,v185,v209,v249]) .nil .nil)) (.node (5,[v12,v20,v97,v103,v138,v185]) (.node (5,[v12,v20,v91,v185,v219,v241]) .nil .nil) (.node (5,[v12,v20,v104,v122,v138,v143]) .nil .nil))) (.node (5,[v12,v22,v29,v66,v209,v269]) (.node (5,[v12,v21,v29,v66,v209,v269]) (.node (5,[v12,v21,v29,v45,v241,v269]) .nil .nil) (.node (5,[v12,v22,v29,v45,v241,v269]) .nil .nil)) (.node (5,[v12,v23,v29,v45,v241,v269]) (.node (5,[v12,v22,v66,v91,v185,v209]) .nil .nil) (.node (5,[v12,v23,v29,v66,v209,v269]) .nil .nil)))))
noncomputable def stem_22 : Tree := .node (5,[v12,v20,v85,v91,v159,v209]) stem_21 block_24
noncomputable def block_25 : Tree := (.node (5,[v12,v29,v35,v66,v209,v269]) (.node (5,[v12,v25,v29,v45,v241,v269]) (.node (5,[v12,v24,v45,v85,v91,v134]) (.node (5,[v12,v24,v29,v66,v209,v269]) (.node (5,[v12,v24,v29,v45,v241,v269]) .nil .nil) .nil) (.node (5,[v12,v24,v66,v91,v185,v209]) .nil .nil)) (.node (5,[v12,v25,v66,v91,v185,v209]) (.node (5,[v12,v25,v29,v66,v209,v269]) .nil .nil) (.node (5,[v12,v29,v35,v45,v241,v269]) .nil .nil))) (.node (5,[v12,v29,v45,v66,v142,v295]) (.node (5,[v12,v29,v45,v66,v115,v142]) (.node (5,[v12,v29,v45,v53,v241,v269]) .nil .nil) (.node (5,[v12,v29,v45,v66,v116,v134]) .nil .nil)) (.node (5,[v12,v29,v45,v66,v172,v267]) (.node (5,[v12,v29,v45,v66,v171,v269]) .nil .nil) (.node (5,[v12,v29,v45,v70,v115,v134]) .nil .nil))))
noncomputable def block_26 : Tree := (.node (5,[v12,v29,v45,v115,v235,v241]) (.node (5,[v12,v29,v45,v115,v143,v237]) (.node (5,[v12,v29,v45,v113,v143,v241]) (.node (5,[v12,v29,v45,v91,v173,v242]) (.node (5,[v12,v29,v45,v85,v115,v142]) .nil .nil) .nil) (.node (5,[v12,v29,v45,v115,v142,v242]) .nil .nil)) (.node (5,[v12,v29,v45,v115,v143,v242]) (.node (5,[v12,v29,v45,v115,v143,v238]) .nil .nil) (.node (5,[v12,v29,v45,v115,v174,v237]) .nil .nil))) (.node (5,[v12,v29,v45,v143,v237,v293]) (.node (5,[v12,v29,v45,v115,v237,v296]) (.node (5,[v12,v29,v45,v115,v237,v269]) .nil .nil) (.node (5,[v12,v29,v45,v115,v241,v269]) .nil .nil)) (.node (5,[v12,v29,v45,v168,v241,v269]) (.node (5,[v12,v29,v45,v168,v237,v269]) .nil .nil) (.node (5,[v12,v29,v45,v172,v237,v269]) .nil .nil))))
noncomputable def stem_23 : Tree := .node (5,[v12,v29,v45,v78,v241,v269]) block_25 block_26
noncomputable def block_27 : Tree := (.node (5,[v12,v29,v66,v115,v185,v205]) (.node (5,[v12,v29,v66,v91,v173,v210]) (.node (5,[v12,v29,v52,v115,v241,v269]) (.node (5,[v12,v29,v52,v66,v115,v142]) (.node (5,[v12,v29,v45,v241,v269,v294]) (.node (5,[v12,v29,v45,v241,v255,v269]) .nil .nil) .nil) (.node (5,[v12,v29,v52,v115,v143,v237]) .nil .nil)) (.node (5,[v12,v29,v53,v66,v209,v269]) (.node (5,[v12,v29,v52,v172,v241,v269]) .nil .nil) (.node (5,[v12,v29,v66,v78,v209,v269]) .nil .nil))) (.node (5,[v12,v29,v66,v115,v143,v206]) (.node (5,[v12,v29,v66,v115,v142,v210]) (.node (5,[v12,v29,v66,v113,v143,v209]) .nil .nil) (.node (5,[v12,v29,v66,v115,v143,v205]) .nil .nil)) (.node (5,[v12,v29,v66,v115,v143,v217]) (.node (5,[v12,v29,v66,v115,v143,v210]) .nil .nil) (.node (5,[v12,v29,v66,v115,v174,v205]) .nil .nil)))) (.node (5,[v12,v29,v66,v143,v205,v293]) (.node (5,[v12,v29,v66,v115,v205,v296]) (.node (5,[v12,v29,v66,v115,v205,v243]) (.node (5,[v12,v29,v66,v115,v199,v209]) .nil .nil) (.node (5,[v12,v29,v66,v115,v205,v269]) .nil .nil)) (.node (5,[v12,v29,v66,v115,v209,v297]) (.node (5,[v12,v29,v66,v115,v209,v269]) .nil .nil) (.node (5,[v12,v29,v66,v115,v219,v269]) .nil .nil))) (.node (5,[v12,v29,v66,v172,v209,v269]) (.node (5,[v12,v29,v66,v168,v209,v269]) (.node (5,[v12,v29,v66,v168,v205,v269]) .nil .nil) (.node (5,[v12,v29,v66,v172,v205,v269]) .nil .nil)) (.node (5,[v12,v29,v66,v209,v220,v269]) (.node (5,[v12,v29,v66,v172,v219,v269]) .nil .nil) (.node (5,[v12,v29,v66,v209,v269,v294]) .nil .nil)))))
noncomputable def stem_24 : Tree := .node (5,[v12,v29,v45,v172,v241,v269]) stem_23 block_27
noncomputable def stem_25 : Tree := .node (5,[v12,v23,v66,v91,v185,v209]) stem_22 stem_24
noncomputable def block_28 : Tree := (.node (5,[v12,v32,v45,v66,v115,v134]) (.node (5,[v12,v29,v103,v115,v143,v241]) (.node (5,[v12,v29,v96,v115,v143,v209]) (.node (5,[v12,v29,v96,v104,v143,v172]) (.node (5,[v12,v29,v85,v115,v209,v269]) .nil .nil) .nil) (.node (5,[v12,v29,v97,v103,v143,v172]) .nil .nil)) (.node (5,[v12,v29,v115,v209,v241,v269]) (.node (5,[v12,v29,v115,v143,v205,v237]) .nil .nil) (.node (5,[v12,v29,v172,v209,v241,v269]) .nil .nil))) (.node (5,[v12,v36,v56,v66,v138,v269]) (.node (5,[v12,v35,v66,v91,v185,v209]) (.node (5,[v12,v35,v57,v91,v143,v241]) .nil .nil) (.node (5,[v12,v35,v85,v91,v143,v209]) .nil .nil)) (.node (5,[v12,v44,v66,v91,v172,v185]) (.node (5,[v12,v36,v56,v91,v143,v241]) .nil .nil) (.node (5,[v12,v44,v85,v115,v138,v143]) .nil .nil))))
noncomputable def block_29 : Tree := (.node (5,[v12,v45,v66,v91,v170,v185]) (.node (5,[v12,v45,v66,v91,v167,v185]) (.node (5,[v12,v45,v66,v90,v172,v185]) (.node (5,[v12,v45,v66,v85,v115,v142]) (.node (5,[v12,v45,v65,v91,v172,v185]) .nil .nil) .nil) (.node (5,[v12,v45,v66,v91,v164,v193]) .nil .nil)) (.node (5,[v12,v45,v66,v91,v168,v263]) (.node (5,[v12,v45,v66,v91,v168,v185]) .nil .nil) (.node (5,[v12,v45,v66,v91,v169,v185]) .nil .nil))) (.node (5,[v12,v45,v66,v91,v172,v185]) (.node (5,[v12,v45,v66,v91,v172,v183]) (.node (5,[v12,v45,v66,v91,v171,v185]) .nil .nil) (.node (5,[v12,v45,v66,v91,v172,v184]) .nil .nil)) (.node (5,[v12,v45,v66,v91,v172,v191]) (.node (5,[v12,v45,v66,v91,v172,v187]) .nil .nil) (.node (5,[v12,v45,v66,v91,v172,v226]) .nil .nil))))
noncomputable def stem_26 : Tree := .node (5,[v12,v45,v64,v97,v172,v185]) block_28 block_29
noncomputable def block_30 : Tree := (.node (5,[v12,v45,v66,v115,v138,v183]) (.node (5,[v12,v45,v66,v92,v172,v185]) (.node (5,[v12,v45,v66,v91,v185,v188]) (.node (5,[v12,v45,v66,v91,v175,v185]) (.node (5,[v12,v45,v66,v91,v173,v185]) (.node (5,[v12,v45,v66,v91,v173,v183]) .nil .nil) .nil) (.node (5,[v12,v45,v66,v91,v177,v185]) .nil .nil)) (.node (5,[v12,v45,v66,v91,v185,v221]) (.node (5,[v12,v45,v66,v91,v185,v189]) .nil .nil) (.node (5,[v12,v45,v66,v91,v185,v256]) .nil .nil))) (.node (5,[v12,v45,v66,v99,v172,v185]) (.node (5,[v12,v45,v66,v94,v172,v185]) (.node (5,[v12,v45,v66,v93,v172,v185]) .nil .nil) (.node (5,[v12,v45,v66,v95,v172,v185]) .nil .nil)) (.node (5,[v12,v45,v66,v111,v172,v185]) (.node (5,[v12,v45,v66,v102,v172,v185]) .nil .nil) (.node (5,[v12,v45,v66,v114,v138,v185]) .nil .nil)))) (.node (5,[v12,v45,v66,v115,v185,v229]) (.node (5,[v12,v45,v66,v115,v165,v185]) (.node (5,[v12,v45,v66,v115,v155,v183]) (.node (5,[v12,v45,v66,v115,v142,v183]) .nil .nil) (.node (5,[v12,v45,v66,v115,v164,v185]) .nil .nil)) (.node (5,[v12,v45,v66,v115,v172,v185]) (.node (5,[v12,v45,v66,v115,v168,v185]) .nil .nil) (.node (5,[v12,v45,v66,v115,v179,v185]) .nil .nil))) (.node (5,[v12,v45,v66,v168,v185,v269]) (.node (5,[v12,v45,v66,v168,v180,v269]) (.node (5,[v12,v45,v66,v143,v180,v293]) .nil .nil) (.node (5,[v12,v45,v66,v168,v185,v264]) .nil .nil)) (.node (5,[v12,v45,v66,v172,v180,v269]) (.node (5,[v12,v45,v66,v168,v185,v293]) .nil .nil) (.node (5,[v12,v45,v66,v172,v185,v264]) .nil .nil)))))
noncomputable def stem_27 : Tree := .node (5,[v12,v45,v66,v91,v172,v259]) stem_26 block_30
noncomputable def block_31 : Tree := (.node (5,[v12,v45,v85,v91,v115,v142]) (.node (5,[v12,v45,v76,v130,v138,v143]) (.node (5,[v12,v45,v69,v91,v172,v185]) (.node (5,[v12,v45,v67,v91,v172,v185]) (.node (5,[v12,v45,v66,v172,v185,v296]) (.node (5,[v12,v45,v66,v172,v185,v291]) .nil .nil) .nil) (.node (5,[v12,v45,v68,v91,v172,v185]) .nil .nil)) (.node (5,[v12,v45,v71,v91,v172,v185]) (.node (5,[v12,v45,v70,v91,v172,v185]) .nil .nil) (.node (5,[v12,v45,v74,v91,v172,v185]) .nil .nil))) (.node (5,[v12,v45,v81,v115,v143,v241]) (.node (5,[v12,v45,v77,v115,v138,v185]) (.node (5,[v12,v45,v77,v91,v172,v185]) .nil .nil) (.node (5,[v12,v45,v78,v85,v138,v269]) .nil .nil)) (.node (5,[v12,v45,v83,v115,v138,v143]) (.node (5,[v12,v45,v83,v91,v143,v172]) .nil .nil) (.node (5,[v12,v45,v84,v115,v138,v143]) .nil .nil)))) (.node (5,[v12,v45,v85,v91,v168,v263]) (.node (5,[v12,v45,v85,v91,v143,v173]) (.node (5,[v12,v45,v85,v91,v143,v168]) (.node (5,[v12,v45,v85,v91,v142,v173]) .nil .nil) (.node (5,[v12,v45,v85,v91,v143,v169]) .nil .nil)) (.node (5,[v12,v45,v85,v91,v168,v185]) (.node (5,[v12,v45,v85,v91,v166,v172]) .nil .nil) (.node (5,[v12,v45,v85,v91,v168,v243]) .nil .nil))) (.node (5,[v12,v45,v85,v114,v138,v143]) (.node (5,[v12,v45,v85,v111,v143,v172]) (.node (5,[v12,v45,v85,v91,v172,v185]) .nil .nil) (.node (5,[v12,v45,v85,v113,v138,v143]) .nil .nil)) (.node (5,[v12,v45,v85,v115,v134,v147]) (.node (5,[v12,v45,v85,v115,v134,v143]) .nil .nil) (.node (5,[v12,v45,v85,v115,v134,v174]) .nil .nil)))))
noncomputable def block_32 : Tree := (.node (5,[v12,v45,v85,v115,v138,v199]) (.node (5,[v12,v45,v85,v115,v138,v143]) (.node (5,[v12,v45,v85,v115,v135,v143]) (.node (5,[v12,v45,v85,v115,v134,v269]) (.node (5,[v12,v45,v85,v115,v134,v263]) (.node (5,[v12,v45,v85,v115,v134,v243]) .nil .nil) .nil) (.node (5,[v12,v45,v85,v115,v134,v296]) .nil .nil)) (.node (5,[v12,v45,v85,v115,v137,v143]) (.node (5,[v12,v45,v85,v115,v136,v143]) .nil .nil) (.node (5,[v12,v45,v85,v115,v138,v142]) .nil .nil))) (.node (5,[v12,v45,v85,v115,v138,v151]) (.node (5,[v12,v45,v85,v115,v138,v145]) (.node (5,[v12,v45,v85,v115,v138,v144]) .nil .nil) (.node (5,[v12,v45,v85,v115,v138,v149]) .nil .nil)) (.node (5,[v12,v45,v85,v115,v138,v166]) (.node (5,[v12,v45,v85,v115,v138,v159]) .nil .nil) (.node (5,[v12,v45,v85,v115,v138,v185]) .nil .nil)))) (.node (5,[v12,v45,v85,v115,v142]) (.node (5,[v12,v45,v85,v115,v138,v297]) (.node (5,[v12,v45,v85,v115,v138,v252]) (.node (5,[v12,v45,v85,v115,v138,v235]) .nil .nil) (.node (5,[v12,v45,v85,v115,v138,v269]) .nil .nil)) (.node (5,[v12,v45,v85,v115,v140,v143]) (.node (5,[v12,v45,v85,v115,v139,v143]) .nil .nil) (.node (5,[v12,v45,v85,v115,v141,v143]) .nil .nil))) (.node (5,[v12,v45,v85,v115,v143,v148]) (.node (5,[v12,v45,v85,v115,v142,v155]) (.node (5,[v12,v45,v85,v115,v142,v143]) .nil .nil) (.node (5,[v12,v45,v85,v115,v143,v146]) .nil .nil)) (.node (5,[v12,v45,v85,v115,v143,v152]) (.node (5,[v12,v45,v85,v115,v143,v150]) .nil .nil) (.node (5,[v12,v45,v85,v115,v143,v155]) .nil .nil)))))
noncomputable def stem_28 : Tree := .node (5,[v12,v45,v85,v115,v134,v185]) block_31 block_32
noncomputable def stem_29 : Tree := .node (5,[v12,v45,v66,v172,v185,v269]) stem_27 stem_28
noncomputable def stem_30 : Tree := .node (5,[v12,v29,v85,v115,v143,v205]) stem_25 stem_29
noncomputable def block_33 : Tree := (.node (5,[v12,v45,v85,v115,v143,v229]) (.node (5,[v12,v45,v85,v115,v143,v197]) (.node (5,[v12,v45,v85,v115,v143,v172]) (.node (5,[v12,v45,v85,v115,v143,v168]) (.node (5,[v12,v45,v85,v115,v143,v165]) .nil .nil) .nil) (.node (5,[v12,v45,v85,v115,v143,v179]) .nil .nil)) (.node (5,[v12,v45,v85,v115,v143,v209]) (.node (5,[v12,v45,v85,v115,v143,v205]) .nil .nil) (.node (5,[v12,v45,v85,v115,v143,v219]) .nil .nil))) (.node (5,[v12,v45,v85,v115,v143,v248]) (.node (5,[v12,v45,v85,v115,v143,v237]) (.node (5,[v12,v45,v85,v115,v143,v234]) .nil .nil) (.node (5,[v12,v45,v85,v115,v143,v241]) .nil .nil)) (.node (5,[v12,v45,v85,v115,v143,v257]) (.node (5,[v12,v45,v85,v115,v143,v251]) .nil .nil) (.node (5,[v12,v45,v85,v115,v143,v287]) .nil .nil))))
noncomputable def block_34 : Tree := (.node (5,[v12,v45,v85,v134,v143,v293]) (.node (5,[v12,v45,v85,v115,v241,v269]) (.node (5,[v12,v45,v85,v115,v185,v209]) (.node (5,[v12,v45,v85,v115,v172,v185]) (.node (5,[v12,v45,v85,v115,v155,v269]) .nil .nil) .nil) (.node (5,[v12,v45,v85,v115,v209,v269]) .nil .nil)) (.node (5,[v12,v45,v85,v117,v138,v143]) (.node (5,[v12,v45,v85,v116,v138,v143]) .nil .nil) (.node (5,[v12,v45,v85,v125,v138,v143]) .nil .nil))) (.node (5,[v12,v45,v86,v115,v138,v143]) (.node (5,[v12,v45,v85,v143,v168,v264]) (.node (5,[v12,v45,v85,v138,v143,v293]) .nil .nil) (.node (5,[v12,v45,v85,v143,v168,v293]) .nil .nil)) (.node (5,[v12,v45,v91,v96,v172,v185]) (.node (5,[v12,v45,v87,v115,v138,v143]) .nil .nil) (.node (5,[v12,v45,v91,v143,v168,v260]) .nil .nil))))
noncomputable def stem_31 : Tree := .node (5,[v12,v45,v85,v115,v155,v185]) block_33 block_34
noncomputable def block_35 : Tree := (.node (5,[v12,v49,v85,v115,v138,v143]) (.node (5,[v12,v45,v115,v143,v180,v237]) (.node (5,[v12,v45,v91,v172,v185,v261]) (.node (5,[v12,v45,v91,v172,v185,v241]) (.node (5,[v12,v45,v91,v172,v185,v237]) (.node (5,[v12,v45,v91,v168,v185,v241]) .nil .nil) .nil) (.node (5,[v12,v45,v91,v172,v185,v253]) .nil .nil)) (.node (5,[v12,v45,v115,v134,v143,v260]) (.node (5,[v12,v45,v115,v122,v138,v143]) .nil .nil) (.node (5,[v12,v45,v115,v138,v143,v260]) .nil .nil))) (.node (5,[v12,v47,v66,v91,v172,v185]) (.node (5,[v12,v45,v172,v185,v241,v269]) (.node (5,[v12,v45,v115,v143,v237,v260]) .nil .nil) (.node (5,[v12,v46,v66,v91,v172,v185]) .nil .nil)) (.node (5,[v12,v48,v85,v115,v138,v143]) (.node (5,[v12,v48,v66,v91,v172,v185]) .nil .nil) (.node (5,[v12,v49,v66,v91,v172,v185]) .nil .nil)))) (.node (5,[v12,v52,v85,v91,v172,v185]) (.node (5,[v12,v52,v66,v91,v172,v185]) (.node (5,[v12,v50,v85,v115,v138,v143]) (.node (5,[v12,v50,v66,v91,v172,v185]) .nil .nil) (.node (5,[v12,v52,v66,v91,v168,v185]) .nil .nil)) (.node (5,[v12,v52,v66,v172,v185,v269]) (.node (5,[v12,v52,v66,v115,v172,v185]) .nil .nil) (.node (5,[v12,v52,v85,v91,v143,v168]) .nil .nil))) (.node (5,[v12,v52,v85,v115,v138,v269]) (.node (5,[v12,v52,v85,v115,v138,v143]) (.node (5,[v12,v52,v85,v115,v134,v143]) .nil .nil) (.node (5,[v12,v52,v85,v115,v138,v185]) .nil .nil)) (.node (5,[v12,v52,v85,v115,v143,v172]) (.node (5,[v12,v52,v85,v115,v143,v155]) .nil .nil) (.node (5,[v12,v52,v85,v115,v143,v209]) .nil .nil)))))
noncomputable def stem_32 : Tree := .node (5,[v12,v45,v91,v168,v185,v237]) stem_31 block_35
noncomputable def block_36 : Tree := (.node (5,[v12,v56,v85,v115,v138,v143]) (.node (5,[v12,v55,v66,v115,v143,v209]) (.node (5,[v12,v53,v66,v91,v185,v209]) (.node (5,[v12,v52,v91,v172,v185,v241]) (.node (5,[v12,v52,v85,v115,v143,v241]) .nil .nil) .nil) (.node (5,[v12,v55,v66,v104,v143,v172]) .nil .nil)) (.node (5,[v12,v56,v66,v115,v138,v185]) (.node (5,[v12,v56,v66,v91,v172,v185]) .nil .nil) (.node (5,[v12,v56,v85,v91,v143,v172]) .nil .nil))) (.node (5,[v12,v66,v78,v91,v185,v209]) (.node (5,[v12,v57,v66,v125,v138,v143]) (.node (5,[v12,v57,v66,v115,v185,v209]) .nil .nil) (.node (5,[v12,v57,v85,v115,v143,v209]) .nil .nil)) (.node (5,[v12,v66,v91,v103,v172,v185]) (.node (5,[v12,v66,v85,v115,v143,v205]) .nil .nil) (.node (5,[v12,v66,v91,v168,v185,v205]) .nil .nil))))
noncomputable def block_37 : Tree := (.node (5,[v12,v85,v91,v115,v185,v209]) (.node (5,[v12,v66,v91,v185,v188,v209]) (.node (5,[v12,v66,v91,v172,v185,v219]) (.node (5,[v12,v66,v91,v172,v185,v209]) (.node (5,[v12,v66,v91,v172,v185,v205]) .nil .nil) .nil) (.node (5,[v12,v66,v91,v172,v185,v223]) .nil .nil)) (.node (5,[v12,v66,v172,v185,v209,v269]) (.node (5,[v12,v66,v115,v143,v180,v205]) .nil .nil) (.node (5,[v12,v85,v91,v115,v143,v205]) .nil .nil))) (.node (5,[v12,v85,v104,v115,v143,v209]) (.node (5,[v12,v85,v91,v172,v185,v209]) (.node (5,[v12,v85,v91,v143,v168,v205]) .nil .nil) (.node (5,[v12,v85,v103,v115,v138,v143]) .nil .nil)) (.node (5,[v12,v85,v115,v121,v138,v143]) (.node (5,[v12,v85,v115,v120,v143,v209]) .nil .nil) (.node (5,[v12,v85,v115,v134,v143,v205]) .nil .nil))))
noncomputable def stem_33 : Tree := .node (5,[v12,v66,v91,v168,v185,v209]) block_36 block_37
noncomputable def block_38 : Tree := (.node (5,[v18,v52,v85,v115,v138,v143]) (.node (5,[v17,v20,v29,v45,v241,v269]) (.node (5,[v13,v20,v66,v91,v185,v209]) (.node (5,[v12,v91,v172,v185,v209,v241]) (.node (5,[v12,v85,v115,v143,v209,v211]) (.node (5,[v12,v85,v115,v143,v205]) .nil .nil) .nil) (.node (5,[v13,v20,v29,v66,v209,v269]) .nil .nil)) (.node (5,[v14,v52,v85,v115,v138,v143]) (.node (5,[v13,v45,v85,v115,v138,v143]) .nil .nil) (.node (5,[v16,v52,v85,v115,v138,v143]) .nil .nil))) (.node (5,[v17,v45,v66,v91,v172,v185]) (.node (5,[v17,v20,v66,v91,v185,v209]) (.node (5,[v17,v20,v29,v66,v209,v269]) .nil .nil) (.node (5,[v17,v20,v85,v91,v143,v209]) .nil .nil)) (.node (5,[v18,v36,v52,v66,v138,v269]) (.node (5,[v17,v45,v85,v115,v138,v143]) .nil .nil) (.node (5,[v18,v52,v66,v115,v138,v185]) .nil .nil)))) (.node (5,[v20,v28,v52,v66,v138,v269]) (.node (5,[v20,v26,v29,v45,v241,v269]) (.node (5,[v19,v52,v66,v91,v138,v185]) (.node (5,[v19,v29,v52,v66,v138,v269]) .nil .nil) (.node (5,[v19,v52,v85,v91,v138,v143]) .nil .nil)) (.node (5,[v20,v26,v66,v91,v185,v209]) (.node (5,[v20,v26,v29,v66,v209,v269]) .nil .nil) (.node (5,[v20,v27,v29,v52,v241,v269]) .nil .nil))) (.node (5,[v20,v29,v43,v66,v209,v269]) (.node (5,[v20,v29,v39,v66,v219,v269]) (.node (5,[v20,v29,v39,v52,v241,v269]) .nil .nil) (.node (5,[v20,v29,v43,v45,v241,v269]) .nil .nil)) (.node (5,[v20,v29,v45,v66,v152,v268]) (.node (5,[v20,v29,v45,v52,v237,v269]) .nil .nil) (.node (5,[v20,v29,v45,v66,v152,v269]) .nil .nil)))))
noncomputable def stem_34 : Tree := .node (5,[v12,v85,v115,v138,v143,v205]) stem_33 block_38
noncomputable def stem_35 : Tree := .node (5,[v12,v52,v85,v115,v143,v219]) stem_32 stem_34
noncomputable def block_39 : Tree := (.node (5,[v20,v29,v45,v91,v153,v244]) (.node (5,[v20,v29,v45,v72,v241,v269]) (.node (5,[v20,v29,v45,v66,v217,v269]) (.node (5,[v20,v29,v45,v66,v203,v269]) (.node (5,[v20,v29,v45,v66,v154,v269]) .nil .nil) .nil) (.node (5,[v20,v29,v45,v66,v247,v269]) .nil .nil)) (.node (5,[v20,v29,v45,v91,v152,v242]) (.node (5,[v20,v29,v45,v73,v138,v274]) .nil .nil) (.node (5,[v20,v29,v45,v91,v153,v242]) .nil .nil))) (.node (5,[v20,v29,v51,v66,v138,v269]) (.node (5,[v20,v29,v45,v152,v241,v269]) (.node (5,[v20,v29,v45,v152,v237,v269]) .nil .nil) (.node (5,[v20,v29,v45,v241,v247,v269]) .nil .nil)) (.node (5,[v20,v29,v52,v65,v138,v269]) (.node (5,[v20,v29,v51,v91,v143,v241]) .nil .nil) (.node (5,[v20,v29,v52,v66,v91,v142]) .nil .nil))))
noncomputable def block_40 : Tree := (.node (5,[v20,v29,v52,v66,v138,v267]) (.node (5,[v20,v29,v52,v66,v134,v296]) (.node (5,[v20,v29,v52,v66,v115,v142]) (.node (5,[v20,v29,v52,v66,v94,v134]) (.node (5,[v20,v29,v52,v66,v91,v198]) .nil .nil) .nil) (.node (5,[v20,v29,v52,v66,v134,v269]) .nil .nil)) (.node (5,[v20,v29,v52,v66,v136,v269]) (.node (5,[v20,v29,v52,v66,v135,v269]) .nil .nil) (.node (5,[v20,v29,v52,v66,v137,v269]) .nil .nil))) (.node (5,[v20,v29,v52,v66,v138,v278]) (.node (5,[v20,v29,v52,v66,v138,v269]) (.node (5,[v20,v29,v52,v66,v138,v268]) .nil .nil) (.node (5,[v20,v29,v52,v66,v138,v274]) .nil .nil)) (.node (5,[v20,v29,v52,v66,v138,v292]) (.node (5,[v20,v29,v52,v66,v138,v284]) .nil .nil) (.node (5,[v20,v29,v52,v66,v139,v269]) .nil .nil))))
noncomputable def stem_36 : Tree := .node (5,[v20,v29,v52,v66,v91,v158]) block_39 block_40
noncomputable def block_41 : Tree := (.node (5,[v20,v29,v52,v66,v217,v269]) (.node (5,[v20,v29,v52,v66,v157,v269]) (.node (5,[v20,v29,v52,v66,v150,v269]) (.node (5,[v20,v29,v52,v66,v146,v269]) (.node (5,[v20,v29,v52,v66,v142,v269]) (.node (5,[v20,v29,v52,v66,v142,v268]) .nil .nil) .nil) (.node (5,[v20,v29,v52,v66,v148,v269]) .nil .nil)) (.node (5,[v20,v29,v52,v66,v155,v268]) (.node (5,[v20,v29,v52,v66,v152,v269]) .nil .nil) (.node (5,[v20,v29,v52,v66,v155,v269]) .nil .nil))) (.node (5,[v20,v29,v52,v66,v198,v269]) (.node (5,[v20,v29,v52,v66,v196,v269]) (.node (5,[v20,v29,v52,v66,v165,v269]) .nil .nil) (.node (5,[v20,v29,v52,v66,v197,v269]) .nil .nil)) (.node (5,[v20,v29,v52,v66,v205,v269]) (.node (5,[v20,v29,v52,v66,v200,v269]) .nil .nil) (.node (5,[v20,v29,v52,v66,v209,v269]) .nil .nil)))) (.node (5,[v20,v29,v52,v66,v269,v287]) (.node (5,[v20,v29,v52,v66,v234,v269]) (.node (5,[v20,v29,v52,v66,v219,v269]) (.node (5,[v20,v29,v52,v66,v219,v268]) .nil .nil) (.node (5,[v20,v29,v52,v66,v233,v269]) .nil .nil)) (.node (5,[v20,v29,v52,v66,v241,v269]) (.node (5,[v20,v29,v52,v66,v237,v269]) .nil .nil) (.node (5,[v20,v29,v52,v66,v248,v269]) .nil .nil))) (.node (5,[v20,v29,v52,v70,v138,v269]) (.node (5,[v20,v29,v52,v69,v138,v269]) (.node (5,[v20,v29,v52,v66,v269,v290]) .nil .nil) (.node (5,[v20,v29,v52,v70,v91,v134]) .nil .nil)) (.node (5,[v20,v29,v52,v73,v241,v269]) (.node (5,[v20,v29,v52,v71,v138,v269]) .nil .nil) (.node (5,[v20,v29,v52,v74,v138,v269]) .nil .nil)))))
noncomputable def stem_37 : Tree := .node (5,[v20,v29,v52,v66,v140,v269]) stem_36 block_41
noncomputable def block_42 : Tree := (.node (5,[v20,v29,v52,v134,v237,v269]) (.node (5,[v20,v29,v52,v91,v174,v237]) (.node (5,[v20,v29,v52,v91,v143,v237]) (.node (5,[v20,v29,v52,v85,v241,v269]) (.node (5,[v20,v29,v52,v85,v91,v142]) (.node (5,[v20,v29,v52,v79,v241,v269]) .nil .nil) .nil) (.node (5,[v20,v29,v52,v91,v142,v242]) .nil .nil)) (.node (5,[v20,v29,v52,v91,v143,v242]) (.node (5,[v20,v29,v52,v91,v143,v239]) .nil .nil) (.node (5,[v20,v29,v52,v91,v149,v241]) .nil .nil))) (.node (5,[v20,v29,v52,v97,v241,v269]) (.node (5,[v20,v29,v52,v95,v143,v241]) (.node (5,[v20,v29,v52,v91,v237,v269]) .nil .nil) (.node (5,[v20,v29,v52,v96,v138,v269]) .nil .nil)) (.node (5,[v20,v29,v52,v101,v241,v269]) (.node (5,[v20,v29,v52,v98,v138,v269]) .nil .nil) (.node (5,[v20,v29,v52,v115,v143,v237]) .nil .nil)))) (.node (5,[v20,v29,v52,v241,v269,v279]) (.node (5,[v20,v29,v52,v153,v241,v269]) (.node (5,[v20,v29,v52,v143,v237,v264]) (.node (5,[v20,v29,v52,v138,v237,v269]) .nil .nil) (.node (5,[v20,v29,v52,v143,v237,v269]) .nil .nil)) (.node (5,[v20,v29,v52,v241,v243,v269]) (.node (5,[v20,v29,v52,v237,v269]) .nil .nil) (.node (5,[v20,v29,v52,v241,v269,v276]) .nil .nil))) (.node (5,[v20,v29,v66,v91,v142,v217]) (.node (5,[v20,v29,v62,v66,v219,v269]) (.node (5,[v20,v29,v61,v66,v138,v269]) .nil .nil) (.node (5,[v20,v29,v66,v72,v209,v269]) .nil .nil)) (.node (5,[v20,v29,v66,v91,v174,v217]) (.node (5,[v20,v29,v66,v91,v143,v217]) .nil .nil) (.node (5,[v20,v29,v66,v91,v185,v217]) .nil .nil)))))
noncomputable def block_43 : Tree := (.node (5,[v20,v29,v66,v218,v219,v269]) (.node (5,[v20,v29,v66,v143,v217,v269]) (.node (5,[v20,v29,v66,v115,v143,v217]) (.node (5,[v20,v29,v66,v108,v138,v269]) (.node (5,[v20,v29,v66,v101,v219,v269]) (.node (5,[v20,v29,v66,v91,v217,v269]) .nil .nil) .nil) (.node (5,[v20,v29,v66,v109,v219,v269]) .nil .nil)) (.node (5,[v20,v29,v66,v138,v217,v269]) (.node (5,[v20,v29,v66,v134,v217,v269]) .nil .nil) (.node (5,[v20,v29,v66,v143,v217,v264]) .nil .nil))) (.node (5,[v20,v29,v66,v153,v219,v269]) (.node (5,[v20,v29,v66,v152,v209,v269]) (.node (5,[v20,v29,v66,v152,v205,v269]) .nil .nil) (.node (5,[v20,v29,v66,v152,v217,v269]) .nil .nil)) (.node (5,[v20,v29,v66,v205,v217,v269]) (.node (5,[v20,v29,v66,v203,v209,v269]) .nil .nil) (.node (5,[v20,v29,v66,v217,v269]) .nil .nil)))) (.node (5,[v20,v30,v52,v66,v138,v269]) (.node (5,[v20,v29,v73,v95,v143,v209]) (.node (5,[v20,v29,v66,v219,v269,v289]) (.node (5,[v20,v29,v66,v219,v269,v279]) .nil .nil) (.node (5,[v20,v29,v73,v91,v149,v209]) .nil .nil)) (.node (5,[v20,v29,v91,v143,v217,v237]) (.node (5,[v20,v29,v85,v91,v143,v217]) .nil .nil) (.node (5,[v20,v29,v97,v108,v138,v143]) .nil .nil))) (.node (5,[v20,v33,v52,v66,v138,v269]) (.node (5,[v20,v32,v52,v66,v91,v134]) (.node (5,[v20,v31,v52,v66,v138,v269]) .nil .nil) (.node (5,[v20,v32,v52,v66,v138,v269]) .nil .nil)) (.node (5,[v20,v34,v52,v66,v138,v269]) (.node (5,[v20,v33,v52,v91,v143,v241]) .nil .nil) (.node (5,[v20,v39,v66,v91,v185,v219]) .nil .nil)))))
noncomputable def stem_38 : Tree := .node (5,[v20,v29,v66,v91,v217,v243]) block_42 block_43
noncomputable def stem_39 : Tree := .node (5,[v20,v29,v52,v77,v138,v269]) stem_37 stem_38
noncomputable def stem_40 : Tree := .node (5,[v20,v29,v45,v66,v152,v296]) stem_35 stem_39
noncomputable def stem_41 : Tree := .node (5,[v12,v45,v85,v115,v143,v157]) stem_30 stem_40
noncomputable def stem_42 : Tree := .node (5,[v12,v20,v66,v91,v187,v209]) stem_20 stem_41
noncomputable def block_44 : Tree := (.node (5,[v20,v45,v66,v91,v163,v185]) (.node (5,[v20,v45,v66,v91,v152,v183]) (.node (5,[v20,v45,v52,v85,v241,v269]) (.node (5,[v20,v45,v52,v85,v91,v142]) (.node (5,[v20,v43,v66,v91,v185,v209]) .nil .nil) .nil) (.node (5,[v20,v45,v66,v85,v152,v269]) .nil .nil)) (.node (5,[v20,v45,v66,v91,v152,v263]) (.node (5,[v20,v45,v66,v91,v152,v185]) .nil .nil) (.node (5,[v20,v45,v66,v91,v154,v185]) .nil .nil))) (.node (5,[v20,v45,v66,v152,v180,v269]) (.node (5,[v20,v45,v66,v91,v185,v217]) (.node (5,[v20,v45,v66,v91,v178,v185]) .nil .nil) (.node (5,[v20,v45,v66,v115,v152,v185]) .nil .nil)) (.node (5,[v20,v45,v66,v152,v185,v269]) (.node (5,[v20,v45,v66,v152,v185,v264]) .nil .nil) (.node (5,[v20,v45,v72,v85,v138,v269]) .nil .nil))))
noncomputable def block_45 : Tree := (.node (5,[v20,v45,v85,v91,v152,v263]) (.node (5,[v20,v45,v85,v91,v147,v152]) (.node (5,[v20,v45,v85,v91,v143,v154]) (.node (5,[v20,v45,v85,v91,v143,v152]) (.node (5,[v20,v45,v85,v91,v142,v152]) .nil .nil) .nil) (.node (5,[v20,v45,v85,v91,v143,v217]) .nil .nil)) (.node (5,[v20,v45,v85,v91,v152,v185]) (.node (5,[v20,v45,v85,v91,v152,v174]) .nil .nil) (.node (5,[v20,v45,v85,v91,v152,v243]) .nil .nil))) (.node (5,[v20,v45,v85,v143,v152,v264]) (.node (5,[v20,v45,v85,v101,v155,v269]) (.node (5,[v20,v45,v85,v91,v152,v269]) .nil .nil) (.node (5,[v20,v45,v85,v115,v143,v152]) .nil .nil)) (.node (5,[v20,v45,v91,v152,v185,v237]) (.node (5,[v20,v45,v91,v143,v152,v260]) .nil .nil) (.node (5,[v20,v45,v91,v152,v185,v241]) .nil .nil))))
noncomputable def stem_43 : Tree := .node (5,[v20,v45,v72,v97,v138,v185]) block_44 block_45
noncomputable def block_46 : Tree := (.node (5,[v20,v52,v66,v91,v134,v263]) (.node (5,[v20,v52,v66,v85,v134,v269]) (.node (5,[v20,v52,v64,v97,v138,v185]) (.node (5,[v20,v52,v58,v66,v138,v269]) (.node (5,[v20,v52,v55,v66,v138,v269]) (.node (5,[v20,v51,v85,v91,v138,v143]) .nil .nil) .nil) (.node (5,[v20,v52,v64,v85,v138,v269]) .nil .nil)) (.node (5,[v20,v52,v66,v81,v138,v269]) (.node (5,[v20,v52,v65,v91,v138,v185]) .nil .nil) (.node (5,[v20,v52,v66,v85,v91,v142]) .nil .nil))) (.node (5,[v20,v52,v66,v85,v219,v269]) (.node (5,[v20,v52,v66,v85,v155,v269]) (.node (5,[v20,v52,v66,v85,v138,v269]) .nil .nil) (.node (5,[v20,v52,v66,v85,v209,v269]) .nil .nil)) (.node (5,[v20,v52,v66,v90,v138,v185]) (.node (5,[v20,v52,v66,v85,v241,v269]) .nil .nil) (.node (5,[v20,v52,v66,v91,v134,v185]) .nil .nil)))) (.node (5,[v20,v52,v66,v91,v138,v191]) (.node (5,[v20,v52,v66,v91,v138,v183]) (.node (5,[v20,v52,v66,v91,v136,v185]) (.node (5,[v20,v52,v66,v91,v135,v185]) .nil .nil) (.node (5,[v20,v52,v66,v91,v137,v185]) .nil .nil)) (.node (5,[v20,v52,v66,v91,v138,v185]) (.node (5,[v20,v52,v66,v91,v138,v184]) .nil .nil) (.node (5,[v20,v52,v66,v91,v138,v187]) .nil .nil))) (.node (5,[v20,v52,v66,v91,v141,v185]) (.node (5,[v20,v52,v66,v91,v138,v259]) (.node (5,[v20,v52,v66,v91,v138,v226]) .nil .nil) (.node (5,[v20,v52,v66,v91,v139,v185]) .nil .nil)) (.node (5,[v20,v52,v66,v91,v142,v185]) (.node (5,[v20,v52,v66,v91,v142,v183]) .nil .nil) (.node (5,[v20,v52,v66,v91,v146,v185]) .nil .nil)))))
noncomputable def stem_44 : Tree := .node (5,[v20,v51,v66,v91,v138,v185]) stem_43 block_46
noncomputable def block_47 : Tree := (.node (5,[v20,v52,v66,v91,v164,v185]) (.node (5,[v20,v52,v66,v91,v156,v185]) (.node (5,[v20,v52,v66,v91,v155,v183]) (.node (5,[v20,v52,v66,v91,v152,v185]) (.node (5,[v20,v52,v66,v91,v150,v185]) .nil .nil) .nil) (.node (5,[v20,v52,v66,v91,v155,v185]) .nil .nil)) (.node (5,[v20,v52,v66,v91,v158,v185]) (.node (5,[v20,v52,v66,v91,v157,v185]) .nil .nil) (.node (5,[v20,v52,v66,v91,v160,v185]) .nil .nil))) (.node (5,[v20,v52,v66,v91,v179,v185]) (.node (5,[v20,v52,v66,v91,v168,v185]) (.node (5,[v20,v52,v66,v91,v165,v185]) .nil .nil) (.node (5,[v20,v52,v66,v91,v172,v185]) .nil .nil)) (.node (5,[v20,v52,v66,v91,v185,v197]) (.node (5,[v20,v52,v66,v91,v183,v219]) .nil .nil) (.node (5,[v20,v52,v66,v91,v185,v205]) .nil .nil))))
noncomputable def block_48 : Tree := (.node (5,[v20,v52,v66,v95,v138,v185]) (.node (5,[v20,v52,v66,v91,v185,v234]) (.node (5,[v20,v52,v66,v91,v185,v229]) (.node (5,[v20,v52,v66,v91,v185,v219]) (.node (5,[v20,v52,v66,v91,v185,v217]) .nil .nil) .nil) (.node (5,[v20,v52,v66,v91,v185,v232]) .nil .nil)) (.node (5,[v20,v52,v66,v93,v138,v185]) (.node (5,[v20,v52,v66,v92,v138,v185]) .nil .nil) (.node (5,[v20,v52,v66,v94,v138,v185]) .nil .nil))) (.node (5,[v20,v52,v66,v111,v138,v185]) (.node (5,[v20,v52,v66,v102,v138,v185]) (.node (5,[v20,v52,v66,v99,v138,v185]) .nil .nil) (.node (5,[v20,v52,v66,v105,v138,v185]) .nil .nil)) (.node (5,[v20,v52,v66,v115,v138,v185]) (.node (5,[v20,v52,v66,v115,v134,v185]) .nil .nil) (.node (5,[v20,v52,v66,v115,v155,v185]) .nil .nil))))
noncomputable def stem_45 : Tree := .node (5,[v20,v52,v66,v91,v185,v209]) block_47 block_48
noncomputable def block_49 : Tree := (.node (5,[v20,v52,v67,v91,v138,v185]) (.node (5,[v20,v52,v66,v138,v185,v296]) (.node (5,[v20,v52,v66,v134,v185,v269]) (.node (5,[v20,v52,v66,v134,v180,v269]) (.node (5,[v20,v52,v66,v115,v185,v219]) (.node (5,[v20,v52,v66,v115,v185,v209]) .nil .nil) .nil) (.node (5,[v20,v52,v66,v134,v185,v264]) .nil .nil)) (.node (5,[v20,v52,v66,v138,v185,v264]) (.node (5,[v20,v52,v66,v138,v180,v269]) .nil .nil) (.node (5,[v20,v52,v66,v138,v185,v269]) .nil .nil))) (.node (5,[v20,v52,v66,v172,v185,v269]) (.node (5,[v20,v52,v66,v143,v180,v264]) (.node (5,[v20,v52,v66,v138,v263,v269]) .nil .nil) (.node (5,[v20,v52,v66,v155,v185,v269]) .nil .nil)) (.node (5,[v20,v52,v66,v185,v219,v269]) (.node (5,[v20,v52,v66,v185,v209,v269]) .nil .nil) (.node (5,[v20,v52,v66,v185,v241,v269]) .nil .nil)))) (.node (5,[v20,v52,v79,v85,v138,v269]) (.node (5,[v20,v52,v73,v85,v138,v269]) (.node (5,[v20,v52,v70,v91,v138,v185]) (.node (5,[v20,v52,v69,v91,v138,v185]) .nil .nil) (.node (5,[v20,v52,v71,v91,v138,v185]) .nil .nil)) (.node (5,[v20,v52,v75,v91,v138,v185]) (.node (5,[v20,v52,v74,v91,v138,v185]) .nil .nil) (.node (5,[v20,v52,v77,v91,v138,v185]) .nil .nil))) (.node (5,[v20,v52,v85,v91,v134,v143]) (.node (5,[v20,v52,v84,v91,v138,v143]) (.node (5,[v20,v52,v83,v91,v138,v143]) .nil .nil) (.node (5,[v20,v52,v85,v90,v138,v143]) .nil .nil)) (.node (5,[v20,v52,v85,v91,v134,v185]) (.node (5,[v20,v52,v85,v91,v134,v174]) .nil .nil) (.node (5,[v20,v52,v85,v91,v134,v243]) .nil .nil)))))
noncomputable def stem_46 : Tree := .node (5,[v20,v52,v66,v115,v172,v185]) stem_45 block_49
noncomputable def stem_47 : Tree := .node (5,[v20,v52,v66,v91,v148,v185]) stem_44 stem_46
noncomputable def block_50 : Tree := (.node (5,[v20,v52,v85,v91,v138,v149]) (.node (5,[v20,v52,v85,v91,v138,v142]) (.node (5,[v20,v52,v85,v91,v136,v143]) (.node (5,[v20,v52,v85,v91,v135,v143]) (.node (5,[v20,v52,v85,v91,v134,v269]) .nil .nil) .nil) (.node (5,[v20,v52,v85,v91,v137,v143]) .nil .nil)) (.node (5,[v20,v52,v85,v91,v138,v144]) (.node (5,[v20,v52,v85,v91,v138,v143]) .nil .nil) (.node (5,[v20,v52,v85,v91,v138,v145]) .nil .nil))) (.node (5,[v20,v52,v85,v91,v138,v166]) (.node (5,[v20,v52,v85,v91,v138,v159]) (.node (5,[v20,v52,v85,v91,v138,v151]) .nil .nil) (.node (5,[v20,v52,v85,v91,v138,v162]) .nil .nil)) (.node (5,[v20,v52,v85,v91,v138,v199]) (.node (5,[v20,v52,v85,v91,v138,v185]) .nil .nil) (.node (5,[v20,v52,v85,v91,v138,v235]) .nil .nil))))
noncomputable def block_51 : Tree := (.node (5,[v20,v52,v85,v91,v143,v146]) (.node (5,[v20,v52,v85,v91,v142]) (.node (5,[v20,v52,v85,v91,v140,v143]) (.node (5,[v20,v52,v85,v91,v139,v143]) (.node (5,[v20,v52,v85,v91,v138,v297]) .nil .nil) .nil) (.node (5,[v20,v52,v85,v91,v141,v143]) .nil .nil)) (.node (5,[v20,v52,v85,v91,v142,v155]) (.node (5,[v20,v52,v85,v91,v142,v143]) .nil .nil) (.node (5,[v20,v52,v85,v91,v142,v219]) .nil .nil))) (.node (5,[v20,v52,v85,v91,v143,v155]) (.node (5,[v20,v52,v85,v91,v143,v150]) (.node (5,[v20,v52,v85,v91,v143,v148]) .nil .nil) (.node (5,[v20,v52,v85,v91,v143,v152]) .nil .nil)) (.node (5,[v20,v52,v85,v91,v143,v161]) (.node (5,[v20,v52,v85,v91,v143,v157]) .nil .nil) (.node (5,[v20,v52,v85,v91,v143,v165]) .nil .nil))))
noncomputable def stem_48 : Tree := .node (5,[v20,v52,v85,v91,v138,v269]) block_50 block_51
noncomputable def block_52 : Tree := (.node (5,[v20,v52,v85,v91,v155,v185]) (.node (5,[v20,v52,v85,v91,v143,v232]) (.node (5,[v20,v52,v85,v91,v143,v209]) (.node (5,[v20,v52,v85,v91,v143,v197]) (.node (5,[v20,v52,v85,v91,v143,v179]) (.node (5,[v20,v52,v85,v91,v143,v172]) .nil .nil) .nil) (.node (5,[v20,v52,v85,v91,v143,v205]) .nil .nil)) (.node (5,[v20,v52,v85,v91,v143,v219]) (.node (5,[v20,v52,v85,v91,v143,v217]) .nil .nil) (.node (5,[v20,v52,v85,v91,v143,v229]) .nil .nil))) (.node (5,[v20,v52,v85,v91,v143,v248]) (.node (5,[v20,v52,v85,v91,v143,v237]) (.node (5,[v20,v52,v85,v91,v143,v234]) .nil .nil) (.node (5,[v20,v52,v85,v91,v143,v241]) .nil .nil)) (.node (5,[v20,v52,v85,v91,v143,v287]) (.node (5,[v20,v52,v85,v91,v143,v257]) .nil .nil) (.node (5,[v20,v52,v85,v91,v143,v290]) .nil .nil)))) (.node (5,[v20,v52,v85,v93,v138,v143]) (.node (5,[v20,v52,v85,v91,v185,v219]) (.node (5,[v20,v52,v85,v91,v172,v185]) (.node (5,[v20,v52,v85,v91,v155,v269]) .nil .nil) (.node (5,[v20,v52,v85,v91,v185,v209]) .nil .nil)) (.node (5,[v20,v52,v85,v91,v219,v269]) (.node (5,[v20,v52,v85,v91,v209,v269]) .nil .nil) (.node (5,[v20,v52,v85,v91,v241,v269]) .nil .nil))) (.node (5,[v20,v52,v85,v99,v138,v143]) (.node (5,[v20,v52,v85,v95,v138,v143]) (.node (5,[v20,v52,v85,v94,v138,v143]) .nil .nil) (.node (5,[v20,v52,v85,v97,v138,v269]) .nil .nil)) (.node (5,[v20,v52,v85,v102,v138,v143]) (.node (5,[v20,v52,v85,v101,v138,v269]) .nil .nil) (.node (5,[v20,v52,v85,v104,v138,v269]) .nil .nil)))))
noncomputable def stem_49 : Tree := .node (5,[v20,v52,v85,v91,v143,v168]) stem_48 block_52
noncomputable def block_53 : Tree := (.node (5,[v20,v52,v85,v138,v265,v269]) (.node (5,[v20,v52,v85,v115,v143,v155]) (.node (5,[v20,v52,v85,v115,v134,v143]) (.node (5,[v20,v52,v85,v110,v138,v269]) (.node (5,[v20,v52,v85,v109,v138,v269]) (.node (5,[v20,v52,v85,v107,v138,v269]) .nil .nil) .nil) (.node (5,[v20,v52,v85,v111,v138,v143]) .nil .nil)) (.node (5,[v20,v52,v85,v115,v138,v185]) (.node (5,[v20,v52,v85,v115,v138,v143]) .nil .nil) (.node (5,[v20,v52,v85,v115,v138,v269]) .nil .nil))) (.node (5,[v20,v52,v85,v115,v143,v241]) (.node (5,[v20,v52,v85,v115,v143,v209]) (.node (5,[v20,v52,v85,v115,v143,v172]) .nil .nil) (.node (5,[v20,v52,v85,v115,v143,v219]) .nil .nil)) (.node (5,[v20,v52,v85,v138,v143,v264]) (.node (5,[v20,v52,v85,v134,v143,v264]) .nil .nil) (.node (5,[v20,v52,v85,v138,v241,v269]) .nil .nil)))) (.node (5,[v20,v52,v91,v134,v185,v237]) (.node (5,[v20,v52,v87,v91,v138,v143]) (.node (5,[v20,v52,v85,v241,v269]) (.node (5,[v20,v52,v85,v143,v241,v269]) .nil .nil) (.node (5,[v20,v52,v86,v91,v138,v143]) .nil .nil)) (.node (5,[v20,v52,v91,v122,v138,v143]) (.node (5,[v20,v52,v91,v96,v138,v185]) .nil .nil) (.node (5,[v20,v52,v91,v134,v143,v260]) .nil .nil))) (.node (5,[v20,v52,v91,v143,v185,v237]) (.node (5,[v20,v52,v91,v138,v185,v237]) (.node (5,[v20,v52,v91,v138,v143,v260]) .nil .nil) (.node (5,[v20,v52,v91,v143,v180,v237]) .nil .nil)) (.node (5,[v20,v52,v91,v143,v241,v263]) (.node (5,[v20,v52,v91,v143,v237,v260]) .nil .nil) (.node (5,[v20,v52,v91,v153,v185,v241]) .nil .nil)))))
noncomputable def block_54 : Tree := (.node (5,[v20,v66,v91,v163,v185,v209]) (.node (5,[v20,v66,v91,v134,v185,v217]) (.node (5,[v20,v66,v85,v91,v143,v217]) (.node (5,[v20,v62,v85,v91,v143,v219]) (.node (5,[v20,v62,v66,v91,v185,v219]) (.node (5,[v20,v61,v85,v91,v138,v143]) .nil .nil) .nil) (.node (5,[v20,v66,v72,v91,v185,v209]) .nil .nil)) (.node (5,[v20,v66,v91,v108,v138,v185]) (.node (5,[v20,v66,v91,v101,v185,v219]) .nil .nil) (.node (5,[v20,v66,v91,v109,v185,v219]) .nil .nil))) (.node (5,[v20,v66,v91,v152,v185,v205]) (.node (5,[v20,v66,v91,v143,v180,v217]) (.node (5,[v20,v66,v91,v138,v185,v217]) .nil .nil) (.node (5,[v20,v66,v91,v143,v185,v217]) .nil .nil)) (.node (5,[v20,v66,v91,v152,v185,v217]) (.node (5,[v20,v66,v91,v152,v185,v209]) .nil .nil) (.node (5,[v20,v66,v91,v153,v185,v219]) .nil .nil)))) (.node (5,[v20,v85,v91,v134,v143,v217]) (.node (5,[v20,v66,v91,v185,v218,v219]) (.node (5,[v20,v66,v91,v185,v205,v217]) (.node (5,[v20,v66,v91,v185,v195,v219]) .nil .nil) (.node (5,[v20,v66,v91,v185,v217]) .nil .nil)) (.node (5,[v20,v85,v91,v108,v138,v143]) (.node (5,[v20,v66,v91,v185,v219,v231]) .nil .nil) (.node (5,[v20,v85,v91,v109,v143,v219]) .nil .nil))) (.node (5,[v20,v85,v91,v143,v205,v217]) (.node (5,[v20,v85,v91,v143,v152,v205]) (.node (5,[v20,v85,v91,v138,v143,v217]) .nil .nil) (.node (5,[v20,v85,v91,v143,v152,v217]) .nil .nil)) (.node (5,[v20,v85,v91,v143,v218,v219]) (.node (5,[v20,v85,v91,v143,v217]) .nil .nil) (.node (5,[v21,v29,v52,v66,v138,v269]) .nil .nil)))))
noncomputable def stem_50 : Tree := .node (5,[v20,v61,v66,v91,v138,v185]) block_53 block_54
noncomputable def stem_51 : Tree := .node (5,[v20,v52,v85,v106,v138,v143]) stem_49 stem_50
noncomputable def stem_52 : Tree := .node (5,[v20,v52,v85,v91,v134,v263]) stem_47 stem_51
noncomputable def block_55 : Tree := (.node (5,[v25,v29,v52,v66,v138,v269]) (.node (5,[v24,v29,v52,v66,v138,v269]) (.node (5,[v24,v29,v45,v91,v153,v241]) (.node (5,[v23,v52,v66,v91,v138,v185]) (.node (5,[v23,v29,v52,v66,v138,v269]) .nil .nil) .nil) (.node (5,[v24,v29,v52,v66,v91,v134]) .nil .nil)) (.node (5,[v24,v52,v85,v91,v138,v143]) (.node (5,[v24,v52,v66,v91,v138,v185]) .nil .nil) (.node (5,[v25,v29,v45,v73,v138,v269]) .nil .nil))) (.node (5,[v25,v52,v85,v91,v138,v143]) (.node (5,[v25,v29,v73,v91,v143,v209]) (.node (5,[v25,v29,v52,v91,v143,v241]) .nil .nil) (.node (5,[v25,v52,v66,v91,v138,v185]) .nil .nil)) (.node (5,[v26,v36,v45,v91,v143,v241]) (.node (5,[v26,v36,v45,v66,v138,v269]) .nil .nil) (.node (5,[v26,v45,v66,v91,v172,v185]) .nil .nil))))
noncomputable def block_56 : Tree := (.node (5,[v27,v45,v87,v91,v138,v143]) (.node (5,[v27,v34,v66,v91,v143,v209]) (.node (5,[v27,v29,v66,v91,v151,v209]) (.node (5,[v26,v45,v85,v115,v138,v143]) (.node (5,[v26,v45,v85,v91,v143,v172]) .nil .nil) .nil) (.node (5,[v27,v29,v71,v91,v143,v209]) .nil .nil)) (.node (5,[v27,v45,v71,v91,v138,v185]) (.node (5,[v27,v45,v66,v91,v138,v191]) .nil .nil) (.node (5,[v27,v45,v85,v91,v138,v151]) .nil .nil))) (.node (5,[v27,v52,v85,v115,v138,v143]) (.node (5,[v27,v52,v66,v115,v138,v185]) (.node (5,[v27,v52,v66,v91,v172,v185]) .nil .nil) (.node (5,[v27,v52,v85,v91,v143,v172]) .nil .nil)) (.node (5,[v29,v35,v52,v66,v138,v269]) (.node (5,[v28,v52,v66,v115,v138,v143]) .nil .nil) (.node (5,[v29,v43,v66,v115,v143,v209]) .nil .nil))))
noncomputable def stem_53 : Tree := .node (5,[v26,v45,v66,v115,v138,v185]) block_55 block_56
noncomputable def block_57 : Tree := (.node (5,[v29,v45,v66,v152,v172,v269]) (.node (5,[v29,v45,v66,v115,v147,v152]) (.node (5,[v29,v45,v66,v115,v142,v152]) (.node (5,[v29,v45,v66,v91,v153,v173]) (.node (5,[v29,v45,v66,v91,v152,v173]) (.node (5,[v29,v45,v52,v115,v143,v237]) .nil .nil) .nil) (.node (5,[v29,v45,v66,v91,v153,v175]) .nil .nil)) (.node (5,[v29,v45,v66,v115,v143,v154]) (.node (5,[v29,v45,v66,v115,v143,v152]) .nil .nil) (.node (5,[v29,v45,v66,v115,v143,v217]) .nil .nil))) (.node (5,[v29,v45,v66,v115,v152,v269]) (.node (5,[v29,v45,v66,v115,v152,v185]) (.node (5,[v29,v45,v66,v115,v152,v174]) .nil .nil) (.node (5,[v29,v45,v66,v115,v152,v243]) .nil .nil)) (.node (5,[v29,v45,v66,v143,v152,v293]) (.node (5,[v29,v45,v66,v115,v152,v296]) .nil .nil) (.node (5,[v29,v45,v66,v152,v168,v269]) .nil .nil)))) (.node (5,[v29,v51,v66,v91,v143,v172]) (.node (5,[v29,v45,v73,v115,v138,v149]) (.node (5,[v29,v45,v72,v97,v143,v172]) (.node (5,[v29,v45,v70,v91,v153,v172]) .nil .nil) (.node (5,[v29,v45,v72,v115,v143,v241]) .nil .nil)) (.node (5,[v29,v45,v85,v115,v143,v152]) (.node (5,[v29,v45,v73,v117,v138,v143]) .nil .nil) (.node (5,[v29,v45,v115,v143,v152,v237]) .nil .nil))) (.node (5,[v29,v52,v65,v115,v138,v143]) (.node (5,[v29,v52,v53,v66,v138,v269]) (.node (5,[v29,v51,v66,v115,v138,v143]) .nil .nil) (.node (5,[v29,v52,v54,v66,v138,v269]) .nil .nil)) (.node (5,[v29,v52,v66,v91,v115,v142]) (.node (5,[v29,v52,v66,v78,v138,v269]) .nil .nil) (.node (5,[v29,v52,v66,v91,v142,v173]) .nil .nil)))))
noncomputable def stem_54 : Tree := .node (5,[v29,v45,v52,v66,v115,v142]) stem_53 block_57
noncomputable def block_58 : Tree := (.node (5,[v29,v52,v66,v115,v134,v143]) (.node (5,[v29,v52,v66,v91,v168,v243]) (.node (5,[v29,v52,v66,v91,v151,v172]) (.node (5,[v29,v52,v66,v91,v143,v173]) (.node (5,[v29,v52,v66,v91,v143,v170]) .nil .nil) .nil) (.node (5,[v29,v52,v66,v91,v168,v185]) .nil .nil)) (.node (5,[v29,v52,v66,v113,v138,v143]) (.node (5,[v29,v52,v66,v99,v143,v172]) .nil .nil) (.node (5,[v29,v52,v66,v114,v138,v143]) .nil .nil))) (.node (5,[v29,v52,v66,v115,v134,v269]) (.node (5,[v29,v52,v66,v115,v134,v185]) (.node (5,[v29,v52,v66,v115,v134,v174]) .nil .nil) (.node (5,[v29,v52,v66,v115,v134,v243]) .nil .nil)) (.node (5,[v29,v52,v66,v115,v135,v143]) (.node (5,[v29,v52,v66,v115,v134,v296]) .nil .nil) (.node (5,[v29,v52,v66,v115,v136,v143]) .nil .nil))))
noncomputable def block_59 : Tree := (.node (5,[v29,v52,v66,v115,v138,v185]) (.node (5,[v29,v52,v66,v115,v138,v149]) (.node (5,[v29,v52,v66,v115,v138,v144]) (.node (5,[v29,v52,v66,v115,v138,v143]) (.node (5,[v29,v52,v66,v115,v138,v142]) .nil .nil) .nil) (.node (5,[v29,v52,v66,v115,v138,v145]) .nil .nil)) (.node (5,[v29,v52,v66,v115,v138,v159]) (.node (5,[v29,v52,v66,v115,v138,v151]) .nil .nil) (.node (5,[v29,v52,v66,v115,v138,v166]) .nil .nil))) (.node (5,[v29,v52,v66,v115,v138,v269]) (.node (5,[v29,v52,v66,v115,v138,v202]) (.node (5,[v29,v52,v66,v115,v138,v199]) .nil .nil) (.node (5,[v29,v52,v66,v115,v138,v235]) .nil .nil)) (.node (5,[v29,v52,v66,v115,v139,v143]) (.node (5,[v29,v52,v66,v115,v138,v297]) .nil .nil) (.node (5,[v29,v52,v66,v115,v140,v143]) .nil .nil))))
noncomputable def stem_55 : Tree := .node (5,[v29,v52,v66,v115,v137,v143]) block_58 block_59
noncomputable def block_60 : Tree := (.node (5,[v29,v52,v66,v115,v143,v205]) (.node (5,[v29,v52,v66,v115,v143,v155]) (.node (5,[v29,v52,v66,v115,v143,v146]) (.node (5,[v29,v52,v66,v115,v142,v155]) (.node (5,[v29,v52,v66,v115,v142,v143]) (.node (5,[v29,v52,v66,v115,v142]) .nil .nil) .nil) (.node (5,[v29,v52,v66,v115,v142,v219]) .nil .nil)) (.node (5,[v29,v52,v66,v115,v143,v150]) (.node (5,[v29,v52,v66,v115,v143,v148]) .nil .nil) (.node (5,[v29,v52,v66,v115,v143,v152]) .nil .nil))) (.node (5,[v29,v52,v66,v115,v143,v172]) (.node (5,[v29,v52,v66,v115,v143,v165]) (.node (5,[v29,v52,v66,v115,v143,v157]) .nil .nil) (.node (5,[v29,v52,v66,v115,v143,v168]) .nil .nil)) (.node (5,[v29,v52,v66,v115,v143,v197]) (.node (5,[v29,v52,v66,v115,v143,v179]) .nil .nil) (.node (5,[v29,v52,v66,v115,v143,v201]) .nil .nil)))) (.node (5,[v29,v52,v66,v115,v143,v241]) (.node (5,[v29,v52,v66,v115,v143,v229]) (.node (5,[v29,v52,v66,v115,v143,v217]) (.node (5,[v29,v52,v66,v115,v143,v209]) .nil .nil) (.node (5,[v29,v52,v66,v115,v143,v219]) .nil .nil)) (.node (5,[v29,v52,v66,v115,v143,v234]) (.node (5,[v29,v52,v66,v115,v143,v232]) .nil .nil) (.node (5,[v29,v52,v66,v115,v143,v237]) .nil .nil))) (.node (5,[v29,v52,v66,v115,v143,v290]) (.node (5,[v29,v52,v66,v115,v143,v257]) (.node (5,[v29,v52,v66,v115,v143,v248]) .nil .nil) (.node (5,[v29,v52,v66,v115,v143,v287]) .nil .nil)) (.node (5,[v29,v52,v66,v115,v155,v269]) (.node (5,[v29,v52,v66,v115,v155,v185]) .nil .nil) (.node (5,[v29,v52,v66,v115,v172,v185]) .nil .nil)))))
noncomputable def stem_56 : Tree := .node (5,[v29,v52,v66,v115,v141,v143]) stem_55 block_60
noncomputable def stem_57 : Tree := .node (5,[v29,v52,v66,v91,v143,v168]) stem_54 stem_56
noncomputable def block_61 : Tree := (.node (5,[v29,v52,v66,v134,v168,v269]) (.node (5,[v29,v52,v66,v116,v138,v143]) (.node (5,[v29,v52,v66,v115,v219,v269]) (.node (5,[v29,v52,v66,v115,v209,v269]) (.node (5,[v29,v52,v66,v115,v185,v219]) .nil .nil) .nil) (.node (5,[v29,v52,v66,v115,v241,v269]) .nil .nil)) (.node (5,[v29,v52,v66,v125,v138,v143]) (.node (5,[v29,v52,v66,v117,v138,v143]) .nil .nil) (.node (5,[v29,v52,v66,v134,v143,v293]) .nil .nil))) (.node (5,[v29,v52,v66,v143,v168,v269]) (.node (5,[v29,v52,v66,v138,v168,v269]) (.node (5,[v29,v52,v66,v138,v143,v293]) .nil .nil) (.node (5,[v29,v52,v66,v143,v168,v264]) .nil .nil)) (.node (5,[v29,v52,v66,v143,v172,v296]) (.node (5,[v29,v52,v66,v143,v168,v293]) .nil .nil) (.node (5,[v29,v52,v66,v153,v172,v269]) .nil .nil))))
noncomputable def block_62 : Tree := (.node (5,[v29,v52,v85,v115,v138,v143]) (.node (5,[v29,v52,v74,v115,v138,v143]) (.node (5,[v29,v52,v71,v115,v138,v143]) (.node (5,[v29,v52,v71,v91,v143,v172]) (.node (5,[v29,v52,v70,v115,v138,v143]) .nil .nil) .nil) (.node (5,[v29,v52,v73,v115,v143,v241]) .nil .nil)) (.node (5,[v29,v52,v85,v91,v143,v168]) (.node (5,[v29,v52,v77,v115,v138,v143]) .nil .nil) (.node (5,[v29,v52,v85,v115,v134,v143]) .nil .nil))) (.node (5,[v29,v52,v85,v115,v143,v172]) (.node (5,[v29,v52,v85,v115,v138,v269]) (.node (5,[v29,v52,v85,v115,v138,v185]) .nil .nil) (.node (5,[v29,v52,v85,v115,v143,v155]) .nil .nil)) (.node (5,[v29,v52,v85,v115,v143,v219]) (.node (5,[v29,v52,v85,v115,v143,v209]) .nil .nil) (.node (5,[v29,v52,v85,v115,v143,v241]) .nil .nil))))
noncomputable def stem_58 : Tree := .node (5,[v29,v52,v67,v115,v138,v143]) block_61 block_62
noncomputable def block_63 : Tree := (.node (5,[v29,v66,v115,v134,v143,v217]) (.node (5,[v29,v52,v115,v143,v241,v243]) (.node (5,[v29,v52,v101,v115,v143,v241]) (.node (5,[v29,v52,v97,v115,v143,v241]) (.node (5,[v29,v52,v96,v115,v138,v143]) (.node (5,[v29,v52,v91,v143,v168,v237]) .nil .nil) .nil) (.node (5,[v29,v52,v100,v115,v138,v143]) .nil .nil)) (.node (5,[v29,v52,v115,v138,v143,v237]) (.node (5,[v29,v52,v115,v134,v143,v237]) .nil .nil) (.node (5,[v29,v52,v115,v143,v237]) .nil .nil))) (.node (5,[v29,v66,v91,v143,v168,v217]) (.node (5,[v29,v62,v66,v115,v143,v219]) (.node (5,[v29,v61,v66,v115,v138,v143]) .nil .nil) (.node (5,[v29,v66,v91,v115,v143,v217]) .nil .nil)) (.node (5,[v29,v66,v108,v115,v138,v143]) (.node (5,[v29,v66,v101,v115,v143,v219]) .nil .nil) (.node (5,[v29,v66,v109,v115,v143,v219]) .nil .nil)))) (.node (5,[v32,v52,v66,v115,v138,v143]) (.node (5,[v29,v66,v115,v143,v205,v217]) (.node (5,[v29,v66,v115,v143,v152,v205]) (.node (5,[v29,v66,v115,v138,v143,v217]) .nil .nil) (.node (5,[v29,v66,v115,v143,v152,v217]) .nil .nil)) (.node (5,[v29,v66,v115,v143,v218,v219]) (.node (5,[v29,v66,v115,v143,v217]) .nil .nil) (.node (5,[v31,v52,v66,v115,v138,v143]) .nil .nil))) (.node (5,[v35,v52,v66,v91,v138,v185]) (.node (5,[v34,v52,v66,v91,v143,v172]) (.node (5,[v33,v52,v66,v115,v138,v143]) .nil .nil) (.node (5,[v34,v52,v66,v115,v138,v143]) .nil .nil)) (.node (5,[v36,v52,v66,v91,v172,v185]) (.node (5,[v35,v52,v85,v91,v138,v143]) .nil .nil) (.node (5,[v36,v52,v66,v115,v138,v185]) .nil .nil)))))
noncomputable def stem_59 : Tree := .node (5,[v29,v52,v91,v115,v143,v237]) stem_58 block_63
noncomputable def block_64 : Tree := (.node (5,[v45,v52,v85,v91,v143,v168]) (.node (5,[v39,v52,v85,v91,v143,v172]) (.node (5,[v39,v45,v66,v115,v155,v185]) (.node (5,[v37,v52,v66,v91,v138,v185]) (.node (5,[v36,v61,v66,v91,v138,v143]) (.node (5,[v36,v52,v85,v115,v138,v143]) .nil .nil) .nil) (.node (5,[v38,v52,v85,v91,v138,v143]) .nil .nil)) (.node (5,[v39,v52,v66,v91,v172,v185]) (.node (5,[v39,v45,v85,v115,v143,v155]) .nil .nil) (.node (5,[v39,v52,v66,v115,v138,v185]) .nil .nil))) (.node (5,[v43,v45,v66,v91,v172,v185]) (.node (5,[v40,v52,v85,v115,v138,v143]) (.node (5,[v39,v52,v85,v115,v138,v143]) .nil .nil) (.node (5,[v42,v52,v85,v115,v138,v143]) .nil .nil)) (.node (5,[v45,v52,v66,v91,v168,v185]) (.node (5,[v43,v45,v85,v115,v138,v143]) .nil .nil) (.node (5,[v45,v52,v66,v115,v172,v185]) .nil .nil)))) (.node (5,[v45,v52,v85,v115,v143,v219]) (.node (5,[v45,v52,v85,v115,v138,v269]) (.node (5,[v45,v52,v85,v115,v138,v143]) (.node (5,[v45,v52,v85,v115,v134,v143]) .nil .nil) (.node (5,[v45,v52,v85,v115,v138,v185]) .nil .nil)) (.node (5,[v45,v52,v85,v115,v143,v172]) (.node (5,[v45,v52,v85,v115,v143,v155]) .nil .nil) (.node (5,[v45,v52,v85,v115,v143,v209]) .nil .nil))) (.node (5,[v45,v66,v91,v152,v168,v185]) (.node (5,[v45,v66,v72,v91,v172,v185]) (.node (5,[v45,v52,v85,v115,v143,v241]) .nil .nil) (.node (5,[v45,v66,v85,v115,v143,v152]) .nil .nil)) (.node (5,[v45,v66,v91,v172,v178,v185]) (.node (5,[v45,v66,v91,v152,v172,v185]) .nil .nil) (.node (5,[v45,v66,v115,v143,v152,v180]) .nil .nil)))))
noncomputable def block_65 : Tree := (.node (5,[v52,v60,v85,v115,v138,v143]) (.node (5,[v52,v52,v85,v115,v138,v143]) (.node (5,[v45,v85,v115,v134,v143,v152]) (.node (5,[v45,v85,v91,v143,v152,v168]) (.node (5,[v45,v85,v91,v115,v143,v152]) (.node (5,[v45,v80,v85,v115,v138,v143]) .nil .nil) .nil) (.node (5,[v45,v85,v101,v115,v143,v155]) .nil .nil)) (.node (5,[v45,v85,v115,v143,v152]) (.node (5,[v45,v85,v115,v138,v143,v152]) .nil .nil) (.node (5,[v45,v85,v115,v143,v153,v155]) .nil .nil))) (.node (5,[v52,v57,v66,v115,v138,v185]) (.node (5,[v52,v53,v85,v91,v138,v143]) (.node (5,[v52,v53,v66,v91,v138,v185]) .nil .nil) (.node (5,[v52,v55,v66,v115,v138,v143]) .nil .nil)) (.node (5,[v52,v59,v66,v115,v138,v143]) (.node (5,[v52,v57,v85,v115,v138,v143]) .nil .nil) (.node (5,[v52,v60,v66,v115,v138,v185]) .nil .nil)))) (.node (5,[v52,v66,v79,v91,v172,v185]) (.node (5,[v52,v63,v85,v115,v138,v143]) (.node (5,[v52,v62,v85,v115,v138,v143]) (.node (5,[v52,v62,v66,v115,v138,v185]) .nil .nil) (.node (5,[v52,v63,v66,v115,v138,v185]) .nil .nil)) (.node (5,[v52,v66,v73,v91,v172,v185]) (.node (5,[v52,v64,v85,v115,v138,v143]) .nil .nil) (.node (5,[v52,v66,v78,v91,v138,v185]) .nil .nil))) (.node (5,[v52,v66,v85,v115,v134,v143]) (.node (5,[v52,v66,v81,v115,v138,v143]) (.node (5,[v52,v66,v79,v115,v138,v185]) .nil .nil) (.node (5,[v52,v66,v85,v91,v143,v168]) .nil .nil)) (.node (5,[v52,v66,v85,v115,v138,v185]) (.node (5,[v52,v66,v85,v115,v138,v143]) .nil .nil) (.node (5,[v52,v66,v85,v115,v138,v269]) .nil .nil)))))
noncomputable def stem_60 : Tree := .node (5,[v45,v72,v85,v115,v138,v143]) block_64 block_65
noncomputable def stem_61 : Tree := .node (5,[v36,v52,v85,v91,v143,v172]) stem_59 stem_60
noncomputable def stem_62 : Tree := .node (5,[v29,v52,v66,v115,v185,v209]) stem_57 stem_61
noncomputable def stem_63 : Tree := .node (5,[v21,v52,v85,v91,v138,v143]) stem_52 stem_62
noncomputable def block_66 : Tree := (.node (5,[v52,v66,v91,v143,v168,v180]) (.node (5,[v52,v66,v91,v101,v172,v185]) (.node (5,[v52,v66,v85,v115,v143,v219]) (.node (5,[v52,v66,v85,v115,v143,v209]) (.node (5,[v52,v66,v85,v115,v143,v172]) .nil .nil) .nil) (.node (5,[v52,v66,v85,v115,v143,v241]) .nil .nil)) (.node (5,[v52,v66,v91,v134,v168,v185]) (.node (5,[v52,v66,v91,v115,v172,v185]) .nil .nil) (.node (5,[v52,v66,v91,v138,v168,v185]) .nil .nil))) (.node (5,[v52,v66,v91,v172,v174,v185]) (.node (5,[v52,v66,v91,v153,v172,v185]) (.node (5,[v52,v66,v91,v143,v168,v185]) .nil .nil) (.node (5,[v52,v66,v91,v168,v185]) .nil .nil)) (.node (5,[v52,v66,v91,v172,v185,v195]) (.node (5,[v52,v66,v91,v172,v185,v193]) .nil .nil) (.node (5,[v52,v66,v115,v134,v143,v180]) .nil .nil))))
noncomputable def block_67 : Tree := (.node (5,[v52,v85,v85,v115,v138,v143]) (.node (5,[v52,v73,v85,v115,v138,v143]) (.node (5,[v52,v66,v115,v143,v172,v185]) (.node (5,[v52,v66,v115,v138,v181,v185]) (.node (5,[v52,v66,v115,v138,v172,v185]) .nil .nil) .nil) (.node (5,[v52,v66,v115,v172,v185]) .nil .nil)) (.node (5,[v52,v78,v85,v91,v138,v143]) (.node (5,[v52,v76,v85,v115,v138,v143]) .nil .nil) (.node (5,[v52,v79,v85,v115,v138,v143]) .nil .nil))) (.node (5,[v52,v85,v91,v115,v138,v143]) (.node (5,[v52,v85,v89,v115,v138,v143]) (.node (5,[v52,v85,v88,v115,v138,v143]) .nil .nil) (.node (5,[v52,v85,v91,v115,v134,v143]) .nil .nil)) (.node (5,[v52,v85,v91,v115,v138,v269]) (.node (5,[v52,v85,v91,v115,v138,v185]) .nil .nil) (.node (5,[v52,v85,v91,v115,v143,v155]) .nil .nil))))
noncomputable def stem_64 : Tree := .node (5,[v52,v66,v115,v138,v143,v180]) block_66 block_67
noncomputable def block_68 : Tree := (.node (5,[v52,v85,v115,v120,v138,v143]) (.node (5,[v52,v85,v101,v115,v138,v143]) (.node (5,[v52,v85,v91,v138,v143,v168]) (.node (5,[v52,v85,v91,v115,v143,v241]) (.node (5,[v52,v85,v91,v115,v143,v219]) (.node (5,[v52,v85,v91,v115,v143,v209]) .nil .nil) .nil) (.node (5,[v52,v85,v91,v134,v143,v168]) .nil .nil)) (.node (5,[v52,v85,v91,v143,v172,v174]) (.node (5,[v52,v85,v91,v143,v168]) .nil .nil) (.node (5,[v52,v85,v97,v115,v138,v143]) .nil .nil))) (.node (5,[v52,v85,v110,v115,v138,v143]) (.node (5,[v52,v85,v107,v115,v138,v143]) (.node (5,[v52,v85,v104,v115,v138,v143]) .nil .nil) (.node (5,[v52,v85,v109,v115,v138,v143]) .nil .nil)) (.node (5,[v52,v85,v115,v118,v138,v143]) (.node (5,[v52,v85,v115,v115,v138,v143]) .nil .nil) (.node (5,[v52,v85,v115,v119,v138,v143]) .nil .nil)))) (.node (5,[v52,v85,v115,v134,v138,v143]) (.node (5,[v52,v85,v115,v127,v138,v143]) (.node (5,[v52,v85,v115,v124,v138,v143]) (.node (5,[v52,v85,v115,v123,v138,v143]) .nil .nil) (.node (5,[v52,v85,v115,v126,v138,v143]) .nil .nil)) (.node (5,[v52,v85,v115,v132,v138,v143]) (.node (5,[v52,v85,v115,v130,v138,v143]) .nil .nil) (.node (5,[v52,v85,v115,v133,v138,v143]) .nil .nil))) (.node (5,[v52,v85,v115,v138,v143,v153]) (.node (5,[v52,v85,v115,v138,v143]) (.node (5,[v52,v85,v115,v134,v143]) .nil .nil) (.node (5,[v52,v85,v115,v138,v143,v147]) .nil .nil)) (.node (5,[v52,v85,v115,v138,v143,v172]) (.node (5,[v52,v85,v115,v138,v143,v155]) .nil .nil) (.node (5,[v52,v85,v115,v138,v143,v174]) .nil .nil)))))
noncomputable def stem_65 : Tree := .node (5,[v52,v85,v91,v115,v143,v172]) stem_64 block_68
noncomputable def block_69 : Tree := (.node (5,[v52,v85,v115,v138,v143,v263]) (.node (5,[v52,v85,v115,v138,v143,v219]) (.node (5,[v52,v85,v115,v138,v143,v211]) (.node (5,[v52,v85,v115,v138,v143,v209]) (.node (5,[v52,v85,v115,v138,v143,v185]) .nil .nil) .nil) (.node (5,[v52,v85,v115,v138,v143,v218]) .nil .nil)) (.node (5,[v52,v85,v115,v138,v143,v243]) (.node (5,[v52,v85,v115,v138,v143,v241]) .nil .nil) (.node (5,[v52,v85,v115,v138,v143,v261]) .nil .nil))) (.node (5,[v52,v85,v115,v138,v143,v296]) (.node (5,[v52,v85,v115,v138,v143,v269]) (.node (5,[v52,v85,v115,v138,v143,v265]) .nil .nil) (.node (5,[v52,v85,v115,v138,v143,v294]) .nil .nil)) (.node (5,[v52,v85,v115,v138,v269]) (.node (5,[v52,v85,v115,v138,v185]) .nil .nil) (.node (5,[v52,v85,v115,v143,v155]) .nil .nil))))
noncomputable def block_70 : Tree := (.node (6,[v0,v20,v29,v52,v66,v138,v269]) (.node (6,[v0,v12,v20,v29,v66,v209,v269]) (.node (5,[v52,v85,v115,v143,v241]) (.node (5,[v52,v85,v115,v143,v219]) (.node (5,[v52,v85,v115,v143,v209]) .nil .nil) .nil) (.node (6,[v0,v12,v20,v29,v45,v241,v269]) .nil .nil)) (.node (6,[v0,v12,v45,v66,v91,v172,v185]) (.node (6,[v0,v12,v20,v66,v91,v185,v209]) .nil .nil) (.node (6,[v0,v12,v45,v85,v115,v138,v143]) .nil .nil))) (.node (6,[v1,v12,v20,v29,v45,v241,v269]) (.node (6,[v0,v20,v52,v85,v91,v138,v143]) (.node (6,[v0,v20,v52,v66,v91,v138,v185]) .nil .nil) (.node (6,[v0,v29,v52,v66,v115,v138,v143]) .nil .nil)) (.node (6,[v1,v12,v20,v66,v91,v185,v209]) (.node (6,[v1,v12,v20,v29,v66,v209,v269]) .nil .nil) (.node (6,[v1,v12,v45,v66,v91,v172,v185]) .nil .nil))))
noncomputable def stem_66 : Tree := .node (5,[v52,v85,v115,v143,v172]) block_69 block_70
noncomputable def block_71 : Tree := (.node (6,[v3,v12,v45,v66,v91,v172,v185]) (.node (6,[v2,v12,v45,v85,v115,v138,v143]) (.node (6,[v2,v12,v20,v29,v45,v241,v269]) (.node (6,[v1,v20,v52,v85,v91,v138,v143]) (.node (6,[v1,v20,v52,v66,v91,v138,v185]) (.node (6,[v1,v20,v29,v52,v66,v138,v269]) .nil .nil) .nil) (.node (6,[v1,v29,v52,v66,v115,v138,v143]) .nil .nil)) (.node (6,[v2,v12,v20,v66,v91,v185,v209]) (.node (6,[v2,v12,v20,v29,v66,v209,v269]) .nil .nil) (.node (6,[v2,v12,v45,v66,v91,v172,v185]) .nil .nil))) (.node (6,[v2,v29,v52,v66,v115,v138,v143]) (.node (6,[v2,v20,v52,v66,v91,v138,v185]) (.node (6,[v2,v20,v29,v52,v66,v138,v269]) .nil .nil) (.node (6,[v2,v20,v52,v85,v91,v138,v143]) .nil .nil)) (.node (6,[v3,v12,v20,v29,v66,v209,v269]) (.node (6,[v3,v12,v20,v29,v45,v241,v269]) .nil .nil) (.node (6,[v3,v12,v20,v66,v91,v185,v209]) .nil .nil)))) (.node (6,[v4,v12,v20,v66,v91,v185,v209]) (.node (6,[v3,v20,v52,v85,v91,v138,v143]) (.node (6,[v3,v20,v29,v52,v66,v138,v269]) (.node (6,[v3,v12,v45,v85,v115,v138,v143]) .nil .nil) (.node (6,[v3,v20,v52,v66,v91,v138,v185]) .nil .nil)) (.node (6,[v4,v12,v20,v29,v45,v241,v269]) (.node (6,[v3,v29,v52,v66,v115,v138,v143]) .nil .nil) (.node (6,[v4,v12,v20,v29,v66,v209,v269]) .nil .nil))) (.node (6,[v4,v20,v52,v66,v91,v138,v185]) (.node (6,[v4,v12,v45,v85,v115,v138,v143]) (.node (6,[v4,v12,v45,v66,v91,v172,v185]) .nil .nil) (.node (6,[v4,v20,v29,v52,v66,v138,v269]) .nil .nil)) (.node (6,[v4,v29,v52,v66,v115,v138,v143]) (.node (6,[v4,v20,v52,v85,v91,v138,v143]) .nil .nil) (.node (6,[v5,v12,v20,v29,v45,v241,v269]) .nil .nil)))))
noncomputable def stem_67 : Tree := .node (6,[v1,v12,v45,v85,v115,v138,v143]) stem_66 block_71
noncomputable def stem_68 : Tree := .node (5,[v52,v85,v115,v138,v143,v181]) stem_65 stem_67
noncomputable def block_72 : Tree := (.node (6,[v6,v12,v20,v29,v66,v209,v269]) (.node (6,[v5,v20,v52,v66,v91,v138,v185]) (.node (6,[v5,v12,v45,v85,v115,v138,v143]) (.node (6,[v5,v12,v45,v66,v91,v172,v185]) (.node (6,[v5,v12,v20,v66,v91,v185,v209]) .nil .nil) .nil) (.node (6,[v5,v20,v29,v52,v66,v138,v269]) .nil .nil)) (.node (6,[v5,v29,v52,v66,v115,v138,v143]) (.node (6,[v5,v20,v52,v85,v91,v138,v143]) .nil .nil) (.node (6,[v6,v12,v20,v29,v45,v241,v269]) .nil .nil))) (.node (6,[v6,v20,v29,v52,v66,v138,v269]) (.node (6,[v6,v12,v45,v66,v91,v172,v185]) (.node (6,[v6,v12,v20,v66,v91,v185,v209]) .nil .nil) (.node (6,[v6,v12,v45,v85,v115,v138,v143]) .nil .nil)) (.node (6,[v6,v20,v52,v85,v91,v138,v143]) (.node (6,[v6,v20,v52,v66,v91,v138,v185]) .nil .nil) (.node (6,[v6,v29,v52,v66,v115,v138,v143]) .nil .nil))))
noncomputable def block_73 : Tree := (.node (6,[v8,v12,v20,v29,v45,v241,v269]) (.node (6,[v7,v20,v29,v52,v66,v138,v269]) (.node (6,[v7,v12,v45,v66,v91,v172,v185]) (.node (6,[v7,v12,v20,v66,v91,v185,v209]) (.node (6,[v7,v12,v20,v29,v66,v209,v269]) .nil .nil) .nil) (.node (6,[v7,v12,v45,v85,v115,v138,v143]) .nil .nil)) (.node (6,[v7,v20,v52,v85,v91,v138,v143]) (.node (6,[v7,v20,v52,v66,v91,v138,v185]) .nil .nil) (.node (6,[v7,v29,v52,v66,v115,v138,v143]) .nil .nil))) (.node (6,[v8,v12,v45,v85,v115,v138,v143]) (.node (6,[v8,v12,v20,v66,v91,v185,v209]) (.node (6,[v8,v12,v20,v29,v66,v209,v269]) .nil .nil) (.node (6,[v8,v12,v45,v66,v91,v172,v185]) .nil .nil)) (.node (6,[v8,v20,v52,v66,v91,v138,v185]) (.node (6,[v8,v20,v29,v52,v66,v138,v269]) .nil .nil) (.node (6,[v8,v20,v52,v85,v91,v138,v143]) .nil .nil))))
noncomputable def stem_69 : Tree := .node (6,[v7,v12,v20,v29,v45,v241,v269]) block_72 block_73
noncomputable def block_74 : Tree := (.node (6,[v10,v12,v20,v66,v91,v185,v209]) (.node (6,[v9,v20,v29,v52,v66,v91,v134]) (.node (6,[v9,v12,v29,v45,v66,v115,v134]) (.node (6,[v9,v12,v20,v45,v85,v91,v134]) (.node (6,[v9,v12,v20,v29,v66,v209,v269]) (.node (6,[v9,v12,v20,v29,v45,v241,v269]) .nil .nil) .nil) (.node (6,[v9,v12,v20,v66,v91,v185,v209]) .nil .nil)) (.node (6,[v9,v12,v45,v85,v115,v138,v143]) (.node (6,[v9,v12,v45,v66,v91,v172,v185]) .nil .nil) (.node (6,[v9,v20,v29,v45,v91,v153,v241]) .nil .nil))) (.node (6,[v9,v29,v45,v66,v91,v153,v172]) (.node (6,[v9,v20,v52,v66,v91,v138,v185]) (.node (6,[v9,v20,v29,v52,v66,v138,v269]) .nil .nil) (.node (6,[v9,v20,v52,v85,v91,v138,v143]) .nil .nil)) (.node (6,[v10,v12,v20,v29,v45,v241,v269]) (.node (6,[v9,v29,v52,v66,v115,v138,v143]) .nil .nil) (.node (6,[v10,v12,v20,v29,v66,v209,v269]) .nil .nil)))) (.node (6,[v10,v20,v52,v85,v91,v138,v143]) (.node (6,[v10,v20,v29,v52,v66,v138,v269]) (.node (6,[v10,v12,v45,v85,v115,v138,v143]) (.node (6,[v10,v12,v45,v66,v91,v172,v185]) .nil .nil) (.node (6,[v10,v20,v29,v45,v73,v138,v269]) .nil .nil)) (.node (6,[v10,v20,v29,v73,v91,v143,v209]) (.node (6,[v10,v20,v29,v52,v91,v143,v241]) .nil .nil) (.node (6,[v10,v20,v52,v66,v91,v138,v185]) .nil .nil))) (.node (6,[v11,v12,v20,v29,v66,v209,v269]) (.node (6,[v10,v29,v52,v66,v115,v138,v143]) (.node (6,[v10,v29,v45,v73,v115,v138,v143]) .nil .nil) (.node (6,[v11,v12,v20,v29,v45,v241,v269]) .nil .nil)) (.node (6,[v11,v12,v45,v66,v91,v172,v185]) (.node (6,[v11,v12,v20,v66,v91,v185,v209]) .nil .nil) (.node (6,[v11,v12,v45,v85,v115,v138,v143]) .nil .nil)))))
noncomputable def stem_70 : Tree := .node (6,[v8,v29,v52,v66,v115,v138,v143]) stem_69 block_74
noncomputable def block_75 : Tree := (.node (6,[v12,v18,v20,v29,v66,v209,v269]) (.node (6,[v12,v14,v20,v29,v66,v209,v269]) (.node (6,[v11,v27,v45,v85,v91,v138,v143]) (.node (6,[v11,v27,v29,v66,v91,v143,v209]) (.node (6,[v11,v20,v52,v85,v91,v138,v143]) (.node (6,[v11,v20,v52,v66,v91,v138,v185]) .nil .nil) .nil) (.node (6,[v11,v27,v45,v66,v91,v138,v185]) .nil .nil)) (.node (6,[v11,v29,v52,v66,v115,v138,v143]) (.node (6,[v11,v29,v52,v66,v91,v143,v172]) .nil .nil) (.node (6,[v12,v14,v20,v29,v45,v241,v269]) .nil .nil))) (.node (6,[v12,v14,v45,v66,v91,v172,v185]) (.node (6,[v12,v14,v20,v66,v91,v185,v209]) (.node (6,[v12,v14,v20,v57,v91,v143,v241]) .nil .nil) (.node (6,[v12,v14,v20,v85,v91,v143,v209]) .nil .nil)) (.node (6,[v12,v14,v57,v66,v115,v138,v143]) (.node (6,[v12,v14,v45,v85,v115,v138,v143]) .nil .nil) (.node (6,[v12,v18,v20,v29,v45,v241,v269]) .nil .nil)))) (.node (6,[v12,v19,v29,v45,v66,v138,v269]) (.node (6,[v12,v18,v45,v66,v91,v172,v185]) (.node (6,[v12,v18,v36,v45,v66,v138,v269]) (.node (6,[v12,v18,v20,v66,v91,v185,v209]) .nil .nil) (.node (6,[v12,v18,v36,v45,v91,v143,v241]) .nil .nil)) (.node (6,[v12,v18,v45,v85,v91,v143,v172]) (.node (6,[v12,v18,v45,v66,v115,v138,v185]) .nil .nil) (.node (6,[v12,v18,v45,v85,v115,v138,v143]) .nil .nil))) (.node (6,[v12,v19,v45,v85,v91,v138,v143]) (.node (6,[v12,v19,v29,v66,v91,v143,v209]) (.node (6,[v12,v19,v29,v45,v91,v143,v241]) .nil .nil) (.node (6,[v12,v19,v45,v66,v91,v138,v185]) .nil .nil)) (.node (6,[v12,v20,v27,v29,v66,v209,v269]) (.node (6,[v12,v20,v27,v29,v45,v241,v269]) .nil .nil) (.node (6,[v12,v20,v27,v66,v91,v185,v209]) .nil .nil)))))
noncomputable def block_76 : Tree := (.node (6,[v12,v20,v29,v45,v66,v94,v134]) (.node (6,[v12,v20,v29,v44,v66,v138,v269]) (.node (6,[v12,v20,v29,v39,v45,v241,v269]) (.node (6,[v12,v20,v29,v36,v45,v241,v269]) (.node (6,[v12,v20,v28,v66,v91,v143,v209]) (.node (6,[v12,v20,v28,v45,v91,v143,v241]) .nil .nil) .nil) (.node (6,[v12,v20,v29,v36,v66,v209,v269]) .nil .nil)) (.node (6,[v12,v20,v29,v40,v45,v241,v269]) (.node (6,[v12,v20,v29,v39,v66,v209,v269]) .nil .nil) (.node (6,[v12,v20,v29,v40,v66,v209,v269]) .nil .nil))) (.node (6,[v12,v20,v29,v45,v60,v241,v269]) (.node (6,[v12,v20,v29,v45,v52,v241,v269]) (.node (6,[v12,v20,v29,v44,v91,v143,v241]) .nil .nil) (.node (6,[v12,v20,v29,v45,v57,v241,v269]) .nil .nil)) (.node (6,[v12,v20,v29,v45,v65,v138,v269]) (.node (6,[v12,v20,v29,v45,v64,v241,v269]) .nil .nil) (.node (6,[v12,v20,v29,v45,v66,v91,v142]) .nil .nil)))) (.node (6,[v12,v20,v29,v45,v66,v138,v268]) (.node (6,[v12,v20,v29,v45,v66,v135,v269]) (.node (6,[v12,v20,v29,v45,v66,v134,v269]) (.node (6,[v12,v20,v29,v45,v66,v115,v142]) .nil .nil) (.node (6,[v12,v20,v29,v45,v66,v134,v296]) .nil .nil)) (.node (6,[v12,v20,v29,v45,v66,v137,v269]) (.node (6,[v12,v20,v29,v45,v66,v136,v269]) .nil .nil) (.node (6,[v12,v20,v29,v45,v66,v138,v267]) .nil .nil))) (.node (6,[v12,v20,v29,v45,v66,v138,v284]) (.node (6,[v12,v20,v29,v45,v66,v138,v274]) (.node (6,[v12,v20,v29,v45,v66,v138,v269]) .nil .nil) (.node (6,[v12,v20,v29,v45,v66,v138,v278]) .nil .nil)) (.node (6,[v12,v20,v29,v45,v66,v139,v269]) (.node (6,[v12,v20,v29,v45,v66,v138,v292]) .nil .nil) (.node (6,[v12,v20,v29,v45,v66,v140,v269]) .nil .nil)))))
noncomputable def stem_71 : Tree := .node (6,[v12,v20,v28,v45,v66,v138,v269]) block_75 block_76
noncomputable def stem_72 : Tree := .node (6,[v11,v20,v29,v52,v66,v138,v269]) stem_70 stem_71
noncomputable def stem_73 : Tree := .node (6,[v5,v12,v20,v29,v66,v209,v269]) stem_68 stem_72
noncomputable def block_77 : Tree := (.node (6,[v12,v20,v29,v45,v66,v165,v269]) (.node (6,[v12,v20,v29,v45,v66,v152,v269]) (.node (6,[v12,v20,v29,v45,v66,v148,v269]) (.node (6,[v12,v20,v29,v45,v66,v146,v269]) (.node (6,[v12,v20,v29,v45,v66,v142,v269]) .nil .nil) .nil) (.node (6,[v12,v20,v29,v45,v66,v150,v269]) .nil .nil)) (.node (6,[v12,v20,v29,v45,v66,v155,v269]) (.node (6,[v12,v20,v29,v45,v66,v155,v268]) .nil .nil) (.node (6,[v12,v20,v29,v45,v66,v157,v269]) .nil .nil))) (.node (6,[v12,v20,v29,v45,v66,v209,v269]) (.node (6,[v12,v20,v29,v45,v66,v197,v269]) (.node (6,[v12,v20,v29,v45,v66,v196,v269]) .nil .nil) (.node (6,[v12,v20,v29,v45,v66,v205,v269]) .nil .nil)) (.node (6,[v12,v20,v29,v45,v66,v233,v269]) (.node (6,[v12,v20,v29,v45,v66,v219,v269]) .nil .nil) (.node (6,[v12,v20,v29,v45,v66,v234,v269]) .nil .nil))))
noncomputable def block_78 : Tree := (.node (6,[v12,v20,v29,v45,v73,v241,v269]) (.node (6,[v12,v20,v29,v45,v69,v138,v269]) (.node (6,[v12,v20,v29,v45,v66,v269,v287]) (.node (6,[v12,v20,v29,v45,v66,v248,v269]) (.node (6,[v12,v20,v29,v45,v66,v241,v269]) .nil .nil) .nil) (.node (6,[v12,v20,v29,v45,v68,v138,v269]) .nil .nil)) (.node (6,[v12,v20,v29,v45,v70,v138,v269]) (.node (6,[v12,v20,v29,v45,v70,v91,v134]) .nil .nil) (.node (6,[v12,v20,v29,v45,v71,v138,v269]) .nil .nil))) (.node (6,[v12,v20,v29,v45,v85,v91,v142]) (.node (6,[v12,v20,v29,v45,v77,v138,v269]) (.node (6,[v12,v20,v29,v45,v74,v138,v269]) .nil .nil) (.node (6,[v12,v20,v29,v45,v79,v241,v269]) .nil .nil)) (.node (6,[v12,v20,v29,v45,v90,v143,v241]) (.node (6,[v12,v20,v29,v45,v85,v241,v269]) .nil .nil) (.node (6,[v12,v20,v29,v45,v91,v142,v241]) .nil .nil))))
noncomputable def stem_74 : Tree := .node (6,[v12,v20,v29,v45,v66,v237,v269]) block_77 block_78
noncomputable def block_79 : Tree := (.node (6,[v12,v20,v29,v45,v91,v174,v237]) (.node (6,[v12,v20,v29,v45,v91,v143,v250]) (.node (6,[v12,v20,v29,v45,v91,v143,v241]) (.node (6,[v12,v20,v29,v45,v91,v143,v239]) (.node (6,[v12,v20,v29,v45,v91,v143,v238]) (.node (6,[v12,v20,v29,v45,v91,v143,v237]) .nil .nil) .nil) (.node (6,[v12,v20,v29,v45,v91,v143,v240]) .nil .nil)) (.node (6,[v12,v20,v29,v45,v91,v143,v244]) (.node (6,[v12,v20,v29,v45,v91,v143,v242]) .nil .nil) (.node (6,[v12,v20,v29,v45,v91,v143,v246]) .nil .nil))) (.node (6,[v12,v20,v29,v45,v91,v149,v241]) (.node (6,[v12,v20,v29,v45,v91,v143,v272]) (.node (6,[v12,v20,v29,v45,v91,v143,v254]) .nil .nil) (.node (6,[v12,v20,v29,v45,v91,v145,v241]) .nil .nil)) (.node (6,[v12,v20,v29,v45,v91,v159,v241]) (.node (6,[v12,v20,v29,v45,v91,v151,v241]) .nil .nil) (.node (6,[v12,v20,v29,v45,v91,v166,v241]) .nil .nil)))) (.node (6,[v12,v20,v29,v45,v96,v138,v269]) (.node (6,[v12,v20,v29,v45,v91,v241,v269]) (.node (6,[v12,v20,v29,v45,v91,v235,v241]) (.node (6,[v12,v20,v29,v45,v91,v199,v241]) .nil .nil) (.node (6,[v12,v20,v29,v45,v91,v237,v269]) .nil .nil)) (.node (6,[v12,v20,v29,v45,v94,v143,v241]) (.node (6,[v12,v20,v29,v45,v92,v143,v241]) .nil .nil) (.node (6,[v12,v20,v29,v45,v95,v143,v241]) .nil .nil))) (.node (6,[v12,v20,v29,v45,v102,v143,v241]) (.node (6,[v12,v20,v29,v45,v99,v143,v241]) (.node (6,[v12,v20,v29,v45,v97,v241,v269]) .nil .nil) (.node (6,[v12,v20,v29,v45,v101,v241,v269]) .nil .nil)) (.node (6,[v12,v20,v29,v45,v107,v241,v269]) (.node (6,[v12,v20,v29,v45,v104,v241,v269]) .nil .nil) (.node (6,[v12,v20,v29,v45,v111,v143,v241]) .nil .nil)))))
noncomputable def stem_75 : Tree := .node (6,[v12,v20,v29,v45,v91,v142,v242]) stem_74 block_79
noncomputable def block_80 : Tree := (.node (6,[v12,v20,v29,v45,v143,v241,v264]) (.node (6,[v12,v20,v29,v45,v138,v237,v269]) (.node (6,[v12,v20,v29,v45,v134,v237,v269]) (.node (6,[v12,v20,v29,v45,v120,v241,v269]) (.node (6,[v12,v20,v29,v45,v115,v241,v269]) .nil .nil) .nil) (.node (6,[v12,v20,v29,v45,v134,v241,v269]) .nil .nil)) (.node (6,[v12,v20,v29,v45,v143,v237,v264]) (.node (6,[v12,v20,v29,v45,v138,v241,v269]) .nil .nil) (.node (6,[v12,v20,v29,v45,v143,v237,v269]) .nil .nil))) (.node (6,[v12,v20,v29,v45,v155,v241,v269]) (.node (6,[v12,v20,v29,v45,v147,v241,v269]) (.node (6,[v12,v20,v29,v45,v143,v241,v269]) .nil .nil) (.node (6,[v12,v20,v29,v45,v153,v241,v269]) .nil .nil)) (.node (6,[v12,v20,v29,v45,v174,v241,v269]) (.node (6,[v12,v20,v29,v45,v172,v241,v269]) .nil .nil) (.node (6,[v12,v20,v29,v45,v181,v241,v269]) .nil .nil))))
noncomputable def block_81 : Tree := (.node (6,[v12,v20,v29,v45,v241,v257,v269]) (.node (6,[v12,v20,v29,v45,v241,v241,v269]) (.node (6,[v12,v20,v29,v45,v233,v241,v269]) (.node (6,[v12,v20,v29,v45,v211,v241,v269]) (.node (6,[v12,v20,v29,v45,v209,v241,v269]) .nil .nil) .nil) (.node (6,[v12,v20,v29,v45,v237,v269]) .nil .nil)) (.node (6,[v12,v20,v29,v45,v241,v245,v269]) (.node (6,[v12,v20,v29,v45,v241,v243,v269]) .nil .nil) (.node (6,[v12,v20,v29,v45,v241,v248,v269]) .nil .nil))) (.node (6,[v12,v20,v29,v45,v241,v269,v269]) (.node (6,[v12,v20,v29,v45,v241,v265,v269]) (.node (6,[v12,v20,v29,v45,v241,v261,v269]) .nil .nil) (.node (6,[v12,v20,v29,v45,v241,v269]) .nil .nil)) (.node (6,[v12,v20,v29,v45,v241,v269,v273]) (.node (6,[v12,v20,v29,v45,v241,v269,v270]) .nil .nil) (.node (6,[v12,v20,v29,v45,v241,v269,v276]) .nil .nil))))
noncomputable def stem_76 : Tree := .node (6,[v12,v20,v29,v45,v185,v241,v269]) block_80 block_81
noncomputable def block_82 : Tree := (.node (6,[v12,v20,v29,v52,v66,v134,v269]) (.node (6,[v12,v20,v29,v47,v91,v143,v241]) (.node (6,[v12,v20,v29,v45,v241,v269,v297]) (.node (6,[v12,v20,v29,v45,v241,v269,v287]) (.node (6,[v12,v20,v29,v45,v241,v269,v285]) (.node (6,[v12,v20,v29,v45,v241,v269,v279]) .nil .nil) .nil) (.node (6,[v12,v20,v29,v45,v241,v269,v296]) .nil .nil)) (.node (6,[v12,v20,v29,v46,v91,v143,v241]) (.node (6,[v12,v20,v29,v46,v66,v138,v269]) .nil .nil) (.node (6,[v12,v20,v29,v47,v66,v138,v269]) .nil .nil))) (.node (6,[v12,v20,v29,v49,v91,v143,v241]) (.node (6,[v12,v20,v29,v48,v91,v143,v241]) (.node (6,[v12,v20,v29,v48,v66,v138,v269]) .nil .nil) (.node (6,[v12,v20,v29,v49,v66,v138,v269]) .nil .nil)) (.node (6,[v12,v20,v29,v50,v91,v143,v241]) (.node (6,[v12,v20,v29,v50,v66,v138,v269]) .nil .nil) (.node (6,[v12,v20,v29,v52,v66,v91,v142]) .nil .nil)))) (.node (6,[v12,v20,v29,v52,v91,v241,v269]) (.node (6,[v12,v20,v29,v52,v66,v219,v269]) (.node (6,[v12,v20,v29,v52,v66,v155,v269]) (.node (6,[v12,v20,v29,v52,v66,v138,v269]) .nil .nil) (.node (6,[v12,v20,v29,v52,v66,v209,v269]) .nil .nil)) (.node (6,[v12,v20,v29,v52,v91,v143,v237]) (.node (6,[v12,v20,v29,v52,v66,v241,v269]) .nil .nil) (.node (6,[v12,v20,v29,v52,v91,v143,v241]) .nil .nil))) (.node (6,[v12,v20,v29,v56,v66,v138,v269]) (.node (6,[v12,v20,v29,v52,v143,v241,v269]) (.node (6,[v12,v20,v29,v52,v138,v241,v269]) .nil .nil) (.node (6,[v12,v20,v29,v52,v241,v269]) .nil .nil)) (.node (6,[v12,v20,v29,v57,v66,v209,v269]) (.node (6,[v12,v20,v29,v56,v91,v143,v241]) .nil .nil) (.node (6,[v12,v20,v29,v60,v66,v209,v269]) .nil .nil)))))
noncomputable def stem_77 : Tree := .node (6,[v12,v20,v29,v45,v241,v269,v277]) stem_76 block_82
noncomputable def stem_78 : Tree := .node (6,[v12,v20,v29,v45,v115,v143,v237]) stem_75 stem_77
noncomputable def block_83 : Tree := (.node (6,[v12,v20,v29,v66,v91,v143,v205]) (.node (6,[v12,v20,v29,v66,v90,v143,v209]) (.node (6,[v12,v20,v29,v66,v79,v209,v269]) (.node (6,[v12,v20,v29,v66,v73,v209,v269]) (.node (6,[v12,v20,v29,v65,v91,v143,v209]) .nil .nil) .nil) (.node (6,[v12,v20,v29,v66,v85,v209,v269]) .nil .nil)) (.node (6,[v12,v20,v29,v66,v91,v142,v210]) (.node (6,[v12,v20,v29,v66,v91,v142,v209]) .nil .nil) (.node (6,[v12,v20,v29,v66,v91,v142,v219]) .nil .nil))) (.node (6,[v12,v20,v29,v66,v91,v143,v209]) (.node (6,[v12,v20,v29,v66,v91,v143,v207]) (.node (6,[v12,v20,v29,v66,v91,v143,v206]) .nil .nil) (.node (6,[v12,v20,v29,v66,v91,v143,v208]) .nil .nil)) (.node (6,[v12,v20,v29,v66,v91,v143,v212]) (.node (6,[v12,v20,v29,v66,v91,v143,v210]) .nil .nil) (.node (6,[v12,v20,v29,v66,v91,v143,v214]) .nil .nil))))
noncomputable def block_84 : Tree := (.node (6,[v12,v20,v29,v66,v91,v159,v209]) (.node (6,[v12,v20,v29,v66,v91,v144,v209]) (.node (6,[v12,v20,v29,v66,v91,v143,v224]) (.node (6,[v12,v20,v29,v66,v91,v143,v219]) (.node (6,[v12,v20,v29,v66,v91,v143,v217]) .nil .nil) .nil) (.node (6,[v12,v20,v29,v66,v91,v143,v282]) .nil .nil)) (.node (6,[v12,v20,v29,v66,v91,v149,v209]) (.node (6,[v12,v20,v29,v66,v91,v145,v209]) .nil .nil) (.node (6,[v12,v20,v29,v66,v91,v151,v209]) .nil .nil))) (.node (6,[v12,v20,v29,v66,v91,v185,v209]) (.node (6,[v12,v20,v29,v66,v91,v174,v205]) (.node (6,[v12,v20,v29,v66,v91,v166,v209]) .nil .nil) (.node (6,[v12,v20,v29,v66,v91,v185,v205]) .nil .nil)) (.node (6,[v12,v20,v29,v66,v91,v199,v209]) (.node (6,[v12,v20,v29,v66,v91,v185,v219]) .nil .nil) (.node (6,[v12,v20,v29,v66,v91,v205,v243]) .nil .nil))))
noncomputable def stem_79 : Tree := .node (6,[v12,v20,v29,v66,v91,v143,v215]) block_83 block_84
noncomputable def block_85 : Tree := (.node (6,[v12,v20,v29,v66,v115,v209,v269]) (.node (6,[v12,v20,v29,v66,v99,v143,v209]) (.node (6,[v12,v20,v29,v66,v92,v143,v209]) (.node (6,[v12,v20,v29,v66,v91,v209,v297]) (.node (6,[v12,v20,v29,v66,v91,v209,v269]) (.node (6,[v12,v20,v29,v66,v91,v209,v235]) .nil .nil) .nil) (.node (6,[v12,v20,v29,v66,v91,v219,v269]) .nil .nil)) (.node (6,[v12,v20,v29,v66,v95,v143,v209]) (.node (6,[v12,v20,v29,v66,v94,v143,v209]) .nil .nil) (.node (6,[v12,v20,v29,v66,v97,v209,v269]) .nil .nil))) (.node (6,[v12,v20,v29,v66,v104,v209,v269]) (.node (6,[v12,v20,v29,v66,v102,v143,v209]) (.node (6,[v12,v20,v29,v66,v101,v209,v269]) .nil .nil) (.node (6,[v12,v20,v29,v66,v103,v138,v269]) .nil .nil)) (.node (6,[v12,v20,v29,v66,v111,v143,v209]) (.node (6,[v12,v20,v29,v66,v107,v209,v269]) .nil .nil) (.node (6,[v12,v20,v29,v66,v115,v143,v205]) .nil .nil)))) (.node (6,[v12,v20,v29,v66,v143,v205,v269]) (.node (6,[v12,v20,v29,v66,v138,v205,v269]) (.node (6,[v12,v20,v29,v66,v134,v205,v269]) (.node (6,[v12,v20,v29,v66,v120,v209,v269]) .nil .nil) (.node (6,[v12,v20,v29,v66,v134,v209,v269]) .nil .nil)) (.node (6,[v12,v20,v29,v66,v138,v219,v269]) (.node (6,[v12,v20,v29,v66,v138,v209,v269]) .nil .nil) (.node (6,[v12,v20,v29,v66,v143,v205,v264]) .nil .nil))) (.node (6,[v12,v20,v29,v66,v147,v209,v269]) (.node (6,[v12,v20,v29,v66,v143,v209,v269]) (.node (6,[v12,v20,v29,v66,v143,v209,v264]) .nil .nil) (.node (6,[v12,v20,v29,v66,v143,v219,v269]) .nil .nil)) (.node (6,[v12,v20,v29,v66,v155,v209,v269]) (.node (6,[v12,v20,v29,v66,v153,v209,v269]) .nil .nil) (.node (6,[v12,v20,v29,v66,v155,v219,v269]) .nil .nil)))))
noncomputable def stem_80 : Tree := .node (6,[v12,v20,v29,v66,v91,v205,v269]) stem_79 block_85
noncomputable def block_86 : Tree := (.node (6,[v12,v20,v29,v66,v209,v269,v270]) (.node (6,[v12,v20,v29,v66,v209,v219,v269]) (.node (6,[v12,v20,v29,v66,v205,v269]) (.node (6,[v12,v20,v29,v66,v185,v209,v269]) (.node (6,[v12,v20,v29,v66,v181,v209,v269]) (.node (6,[v12,v20,v29,v66,v174,v209,v269]) .nil .nil) .nil) (.node (6,[v12,v20,v29,v66,v196,v209,v269]) .nil .nil)) (.node (6,[v12,v20,v29,v66,v209,v211,v269]) (.node (6,[v12,v20,v29,v66,v209,v209,v269]) .nil .nil) (.node (6,[v12,v20,v29,v66,v209,v213,v269]) .nil .nil))) (.node (6,[v12,v20,v29,v66,v209,v243,v269]) (.node (6,[v12,v20,v29,v66,v209,v229,v269]) (.node (6,[v12,v20,v29,v66,v209,v225,v269]) .nil .nil) (.node (6,[v12,v20,v29,v66,v209,v241,v269]) .nil .nil)) (.node (6,[v12,v20,v29,v66,v209,v269]) (.node (6,[v12,v20,v29,v66,v209,v265,v269]) .nil .nil) (.node (6,[v12,v20,v29,v66,v209,v269,v269]) .nil .nil)))) (.node (6,[v12,v20,v29,v66,v209,v269,v297]) (.node (6,[v12,v20,v29,v66,v209,v269,v285]) (.node (6,[v12,v20,v29,v66,v209,v269,v279]) (.node (6,[v12,v20,v29,v66,v209,v269,v276]) .nil .nil) (.node (6,[v12,v20,v29,v66,v209,v269,v283]) .nil .nil)) (.node (6,[v12,v20,v29,v66,v209,v269,v287]) (.node (6,[v12,v20,v29,v66,v209,v269,v286]) .nil .nil) (.node (6,[v12,v20,v29,v66,v209,v269,v296]) .nil .nil))) (.node (6,[v12,v20,v29,v69,v91,v143,v209]) (.node (6,[v12,v20,v29,v67,v91,v143,v209]) (.node (6,[v12,v20,v29,v66,v219,v269]) .nil .nil) (.node (6,[v12,v20,v29,v68,v91,v143,v209]) .nil .nil)) (.node (6,[v12,v20,v29,v71,v91,v143,v209]) (.node (6,[v12,v20,v29,v70,v91,v143,v209]) .nil .nil) (.node (6,[v12,v20,v29,v74,v91,v143,v209]) .nil .nil)))))
noncomputable def block_87 : Tree := (.node (6,[v12,v20,v29,v97,v103,v138,v143]) (.node (6,[v12,v20,v29,v91,v143,v205,v241]) (.node (6,[v12,v20,v29,v85,v91,v209,v269]) (.node (6,[v12,v20,v29,v85,v91,v143,v219]) (.node (6,[v12,v20,v29,v85,v91,v143,v209]) (.node (6,[v12,v20,v29,v85,v91,v143,v205]) .nil .nil) .nil) (.node (6,[v12,v20,v29,v85,v91,v185,v209]) .nil .nil)) (.node (6,[v12,v20,v29,v91,v103,v143,v241]) (.node (6,[v12,v20,v29,v91,v96,v143,v209]) .nil .nil) (.node (6,[v12,v20,v29,v91,v143,v205,v237]) .nil .nil))) (.node (6,[v12,v20,v29,v91,v143,v219,v241]) (.node (6,[v12,v20,v29,v91,v143,v209,v241]) (.node (6,[v12,v20,v29,v91,v143,v209,v237]) .nil .nil) (.node (6,[v12,v20,v29,v91,v143,v209,v261]) .nil .nil)) (.node (6,[v12,v20,v29,v91,v209,v241,v269]) (.node (6,[v12,v20,v29,v91,v185,v209,v241]) .nil .nil) (.node (6,[v12,v20,v29,v96,v104,v138,v143]) .nil .nil)))) (.node (6,[v12,v20,v31,v45,v91,v143,v241]) (.node (6,[v12,v20,v30,v45,v66,v138,v269]) (.node (6,[v12,v20,v29,v143,v209,v241,v269]) (.node (6,[v12,v20,v29,v138,v209,v241,v269]) .nil .nil) (.node (6,[v12,v20,v29,v209,v241,v269]) .nil .nil)) (.node (6,[v12,v20,v30,v66,v91,v143,v209]) (.node (6,[v12,v20,v30,v45,v91,v143,v241]) .nil .nil) (.node (6,[v12,v20,v31,v45,v66,v138,v269]) .nil .nil))) (.node (6,[v12,v20,v32,v66,v91,v143,v209]) (.node (6,[v12,v20,v32,v45,v66,v138,v269]) (.node (6,[v12,v20,v32,v45,v66,v91,v134]) .nil .nil) (.node (6,[v12,v20,v32,v45,v91,v143,v241]) .nil .nil)) (.node (6,[v12,v20,v33,v45,v91,v143,v241]) (.node (6,[v12,v20,v33,v45,v66,v138,v269]) .nil .nil) (.node (6,[v12,v20,v33,v66,v91,v143,v209]) .nil .nil)))))
noncomputable def stem_81 : Tree := .node (6,[v12,v20,v29,v77,v91,v143,v209]) block_86 block_87
noncomputable def stem_82 : Tree := .node (6,[v12,v20,v29,v66,v172,v209,v269]) stem_80 stem_81
noncomputable def stem_83 : Tree := .node (6,[v12,v20,v29,v64,v66,v209,v269]) stem_78 stem_82
noncomputable def stem_84 : Tree := .node (6,[v12,v20,v29,v45,v66,v142,v268]) stem_73 stem_83
noncomputable def stem_85 : Tree := .node (5,[v52,v66,v85,v115,v143,v155]) stem_63 stem_84
noncomputable def stem_86 : Tree := .node (5,[v20,v39,v85,v91,v143,v219]) stem_42 stem_85
noncomputable def block_88 : Tree := (.node (6,[v12,v20,v44,v66,v91,v138,v185]) (.node (6,[v12,v20,v39,v66,v91,v185,v209]) (.node (6,[v12,v20,v36,v66,v91,v185,v209]) (.node (6,[v12,v20,v34,v66,v91,v143,v209]) (.node (6,[v12,v20,v34,v45,v91,v143,v241]) .nil .nil) .nil) (.node (6,[v12,v20,v36,v85,v91,v143,v209]) .nil .nil)) (.node (6,[v12,v20,v40,v66,v91,v185,v209]) (.node (6,[v12,v20,v39,v85,v91,v143,v209]) .nil .nil) (.node (6,[v12,v20,v40,v85,v104,v138,v143]) .nil .nil))) (.node (6,[v12,v20,v45,v64,v85,v138,v269]) (.node (6,[v12,v20,v45,v55,v66,v138,v269]) (.node (6,[v12,v20,v44,v85,v91,v138,v143]) .nil .nil) (.node (6,[v12,v20,v45,v55,v91,v143,v241]) .nil .nil)) (.node (6,[v12,v20,v45,v65,v91,v138,v185]) (.node (6,[v12,v20,v45,v64,v97,v138,v185]) .nil .nil) (.node (6,[v12,v20,v45,v66,v81,v138,v269]) .nil .nil))))
noncomputable def block_89 : Tree := (.node (6,[v12,v20,v45,v66,v91,v135,v185]) (.node (6,[v12,v20,v45,v66,v85,v241,v269]) (.node (6,[v12,v20,v45,v66,v85,v155,v269]) (.node (6,[v12,v20,v45,v66,v85,v138,v269]) (.node (6,[v12,v20,v45,v66,v85,v134,v269]) .nil .nil) .nil) (.node (6,[v12,v20,v45,v66,v85,v209,v269]) .nil .nil)) (.node (6,[v12,v20,v45,v66,v91,v134,v185]) (.node (6,[v12,v20,v45,v66,v90,v138,v185]) .nil .nil) (.node (6,[v12,v20,v45,v66,v91,v134,v263]) .nil .nil))) (.node (6,[v12,v20,v45,v66,v91,v138,v184]) (.node (6,[v12,v20,v45,v66,v91,v137,v185]) (.node (6,[v12,v20,v45,v66,v91,v136,v185]) .nil .nil) (.node (6,[v12,v20,v45,v66,v91,v138,v183]) .nil .nil)) (.node (6,[v12,v20,v45,v66,v91,v138,v187]) (.node (6,[v12,v20,v45,v66,v91,v138,v185]) .nil .nil) (.node (6,[v12,v20,v45,v66,v91,v138,v191]) .nil .nil))))
noncomputable def stem_87 : Tree := .node (6,[v12,v20,v45,v66,v85,v91,v142]) block_88 block_89
noncomputable def block_90 : Tree := (.node (6,[v12,v20,v45,v66,v91,v172,v185]) (.node (6,[v12,v20,v45,v66,v91,v152,v185]) (.node (6,[v12,v20,v45,v66,v91,v142,v185]) (.node (6,[v12,v20,v45,v66,v91,v141,v185]) (.node (6,[v12,v20,v45,v66,v91,v139,v185]) (.node (6,[v12,v20,v45,v66,v91,v138,v259]) .nil .nil) .nil) (.node (6,[v12,v20,v45,v66,v91,v142,v183]) .nil .nil)) (.node (6,[v12,v20,v45,v66,v91,v148,v185]) (.node (6,[v12,v20,v45,v66,v91,v146,v185]) .nil .nil) (.node (6,[v12,v20,v45,v66,v91,v150,v185]) .nil .nil))) (.node (6,[v12,v20,v45,v66,v91,v157,v185]) (.node (6,[v12,v20,v45,v66,v91,v155,v185]) (.node (6,[v12,v20,v45,v66,v91,v155,v183]) .nil .nil) (.node (6,[v12,v20,v45,v66,v91,v156,v185]) .nil .nil)) (.node (6,[v12,v20,v45,v66,v91,v165,v185]) (.node (6,[v12,v20,v45,v66,v91,v164,v185]) .nil .nil) (.node (6,[v12,v20,v45,v66,v91,v168,v185]) .nil .nil)))) (.node (6,[v12,v20,v45,v66,v92,v138,v185]) (.node (6,[v12,v20,v45,v66,v91,v185,v209]) (.node (6,[v12,v20,v45,v66,v91,v185,v197]) (.node (6,[v12,v20,v45,v66,v91,v179,v185]) .nil .nil) (.node (6,[v12,v20,v45,v66,v91,v185,v205]) .nil .nil)) (.node (6,[v12,v20,v45,v66,v91,v185,v229]) (.node (6,[v12,v20,v45,v66,v91,v185,v219]) .nil .nil) (.node (6,[v12,v20,v45,v66,v91,v185,v234]) .nil .nil))) (.node (6,[v12,v20,v45,v66,v99,v138,v185]) (.node (6,[v12,v20,v45,v66,v94,v138,v185]) (.node (6,[v12,v20,v45,v66,v93,v138,v185]) .nil .nil) (.node (6,[v12,v20,v45,v66,v95,v138,v185]) .nil .nil)) (.node (6,[v12,v20,v45,v66,v111,v138,v185]) (.node (6,[v12,v20,v45,v66,v102,v138,v185]) .nil .nil) (.node (6,[v12,v20,v45,v66,v115,v134,v185]) .nil .nil)))))
noncomputable def stem_88 : Tree := .node (6,[v12,v20,v45,v66,v91,v138,v226]) stem_87 block_90
noncomputable def block_91 : Tree := (.node (6,[v12,v20,v45,v66,v138,v185,v269]) (.node (6,[v12,v20,v45,v66,v134,v185,v264]) (.node (6,[v12,v20,v45,v66,v115,v185,v209]) (.node (6,[v12,v20,v45,v66,v115,v172,v185]) (.node (6,[v12,v20,v45,v66,v115,v155,v185]) .nil .nil) .nil) (.node (6,[v12,v20,v45,v66,v134,v180,v269]) .nil .nil)) (.node (6,[v12,v20,v45,v66,v138,v180,v269]) (.node (6,[v12,v20,v45,v66,v134,v185,v269]) .nil .nil) (.node (6,[v12,v20,v45,v66,v138,v185,v264]) .nil .nil))) (.node (6,[v12,v20,v45,v66,v155,v185,v269]) (.node (6,[v12,v20,v45,v66,v138,v263,v269]) (.node (6,[v12,v20,v45,v66,v138,v185,v296]) .nil .nil) (.node (6,[v12,v20,v45,v66,v143,v180,v264]) .nil .nil)) (.node (6,[v12,v20,v45,v66,v185,v209,v269]) (.node (6,[v12,v20,v45,v66,v172,v185,v269]) .nil .nil) (.node (6,[v12,v20,v45,v66,v185,v241,v269]) .nil .nil))))
noncomputable def block_92 : Tree := (.node (6,[v12,v20,v45,v81,v91,v143,v241]) (.node (6,[v12,v20,v45,v73,v85,v138,v269]) (.node (6,[v12,v20,v45,v70,v91,v138,v185]) (.node (6,[v12,v20,v45,v69,v91,v138,v185]) (.node (6,[v12,v20,v45,v68,v91,v138,v185]) .nil .nil) .nil) (.node (6,[v12,v20,v45,v71,v91,v138,v185]) .nil .nil)) (.node (6,[v12,v20,v45,v77,v91,v138,v185]) (.node (6,[v12,v20,v45,v74,v91,v138,v185]) .nil .nil) (.node (6,[v12,v20,v45,v79,v85,v138,v269]) .nil .nil))) (.node (6,[v12,v20,v45,v85,v91,v134,v143]) (.node (6,[v12,v20,v45,v84,v91,v138,v143]) (.node (6,[v12,v20,v45,v83,v91,v138,v143]) .nil .nil) (.node (6,[v12,v20,v45,v85,v90,v138,v143]) .nil .nil)) (.node (6,[v12,v20,v45,v85,v91,v134,v174]) (.node (6,[v12,v20,v45,v85,v91,v134,v147]) .nil .nil) (.node (6,[v12,v20,v45,v85,v91,v134,v185]) .nil .nil))))
noncomputable def stem_89 : Tree := .node (6,[v12,v20,v45,v67,v91,v138,v185]) block_91 block_92
noncomputable def block_93 : Tree := (.node (6,[v12,v20,v45,v85,v91,v138,v269]) (.node (6,[v12,v20,v45,v85,v91,v138,v145]) (.node (6,[v12,v20,v45,v85,v91,v137,v143]) (.node (6,[v12,v20,v45,v85,v91,v135,v143]) (.node (6,[v12,v20,v45,v85,v91,v134,v269]) (.node (6,[v12,v20,v45,v85,v91,v134,v263]) .nil .nil) .nil) (.node (6,[v12,v20,v45,v85,v91,v136,v143]) .nil .nil)) (.node (6,[v12,v20,v45,v85,v91,v138,v143]) (.node (6,[v12,v20,v45,v85,v91,v138,v142]) .nil .nil) (.node (6,[v12,v20,v45,v85,v91,v138,v144]) .nil .nil))) (.node (6,[v12,v20,v45,v85,v91,v138,v166]) (.node (6,[v12,v20,v45,v85,v91,v138,v151]) (.node (6,[v12,v20,v45,v85,v91,v138,v149]) .nil .nil) (.node (6,[v12,v20,v45,v85,v91,v138,v159]) .nil .nil)) (.node (6,[v12,v20,v45,v85,v91,v138,v199]) (.node (6,[v12,v20,v45,v85,v91,v138,v185]) .nil .nil) (.node (6,[v12,v20,v45,v85,v91,v138,v235]) .nil .nil)))) (.node (6,[v12,v20,v45,v85,v91,v143,v146]) (.node (6,[v12,v20,v45,v85,v91,v141,v143]) (.node (6,[v12,v20,v45,v85,v91,v139,v143]) (.node (6,[v12,v20,v45,v85,v91,v138,v297]) .nil .nil) (.node (6,[v12,v20,v45,v85,v91,v140,v143]) .nil .nil)) (.node (6,[v12,v20,v45,v85,v91,v142,v143]) (.node (6,[v12,v20,v45,v85,v91,v142]) .nil .nil) (.node (6,[v12,v20,v45,v85,v91,v142,v155]) .nil .nil))) (.node (6,[v12,v20,v45,v85,v91,v143,v155]) (.node (6,[v12,v20,v45,v85,v91,v143,v150]) (.node (6,[v12,v20,v45,v85,v91,v143,v148]) .nil .nil) (.node (6,[v12,v20,v45,v85,v91,v143,v152]) .nil .nil)) (.node (6,[v12,v20,v45,v85,v91,v143,v165]) (.node (6,[v12,v20,v45,v85,v91,v143,v157]) .nil .nil) (.node (6,[v12,v20,v45,v85,v91,v143,v168]) .nil .nil)))))
noncomputable def stem_90 : Tree := .node (6,[v12,v20,v45,v85,v91,v134,v243]) stem_89 block_93
noncomputable def stem_91 : Tree := .node (6,[v12,v20,v45,v66,v115,v138,v185]) stem_88 stem_90
noncomputable def block_94 : Tree := (.node (6,[v12,v20,v45,v85,v91,v143,v241]) (.node (6,[v12,v20,v45,v85,v91,v143,v219]) (.node (6,[v12,v20,v45,v85,v91,v143,v205]) (.node (6,[v12,v20,v45,v85,v91,v143,v197]) (.node (6,[v12,v20,v45,v85,v91,v143,v179]) .nil .nil) .nil) (.node (6,[v12,v20,v45,v85,v91,v143,v209]) .nil .nil)) (.node (6,[v12,v20,v45,v85,v91,v143,v234]) (.node (6,[v12,v20,v45,v85,v91,v143,v229]) .nil .nil) (.node (6,[v12,v20,v45,v85,v91,v143,v237]) .nil .nil))) (.node (6,[v12,v20,v45,v85,v91,v155,v185]) (.node (6,[v12,v20,v45,v85,v91,v143,v257]) (.node (6,[v12,v20,v45,v85,v91,v143,v248]) .nil .nil) (.node (6,[v12,v20,v45,v85,v91,v143,v287]) .nil .nil)) (.node (6,[v12,v20,v45,v85,v91,v172,v185]) (.node (6,[v12,v20,v45,v85,v91,v155,v269]) .nil .nil) (.node (6,[v12,v20,v45,v85,v91,v185,v209]) .nil .nil))))
noncomputable def block_95 : Tree := (.node (6,[v12,v20,v45,v85,v104,v138,v269]) (.node (6,[v12,v20,v45,v85,v97,v138,v269]) (.node (6,[v12,v20,v45,v85,v94,v138,v143]) (.node (6,[v12,v20,v45,v85,v93,v138,v143]) (.node (6,[v12,v20,v45,v85,v91,v241,v269]) .nil .nil) .nil) (.node (6,[v12,v20,v45,v85,v95,v138,v143]) .nil .nil)) (.node (6,[v12,v20,v45,v85,v101,v138,v269]) (.node (6,[v12,v20,v45,v85,v99,v138,v143]) .nil .nil) (.node (6,[v12,v20,v45,v85,v102,v138,v143]) .nil .nil))) (.node (6,[v12,v20,v45,v85,v115,v138,v143]) (.node (6,[v12,v20,v45,v85,v111,v138,v143]) (.node (6,[v12,v20,v45,v85,v107,v138,v269]) .nil .nil) (.node (6,[v12,v20,v45,v85,v115,v134,v143]) .nil .nil)) (.node (6,[v12,v20,v45,v85,v115,v138,v269]) (.node (6,[v12,v20,v45,v85,v115,v138,v185]) .nil .nil) (.node (6,[v12,v20,v45,v85,v115,v143,v155]) .nil .nil))))
noncomputable def stem_92 : Tree := .node (6,[v12,v20,v45,v85,v91,v209,v269]) block_94 block_95
noncomputable def block_96 : Tree := (.node (6,[v12,v20,v45,v91,v138,v185,v237]) (.node (6,[v12,v20,v45,v86,v91,v138,v143]) (.node (6,[v12,v20,v45,v85,v138,v241,v269]) (.node (6,[v12,v20,v45,v85,v134,v143,v264]) (.node (6,[v12,v20,v45,v85,v115,v143,v241]) (.node (6,[v12,v20,v45,v85,v115,v143,v209]) .nil .nil) .nil) (.node (6,[v12,v20,v45,v85,v138,v143,v264]) .nil .nil)) (.node (6,[v12,v20,v45,v85,v143,v241,v269]) (.node (6,[v12,v20,v45,v85,v138,v265,v269]) .nil .nil) (.node (6,[v12,v20,v45,v85,v241,v269]) .nil .nil))) (.node (6,[v12,v20,v45,v91,v134,v143,v260]) (.node (6,[v12,v20,v45,v91,v96,v138,v185]) (.node (6,[v12,v20,v45,v87,v91,v138,v143]) .nil .nil) (.node (6,[v12,v20,v45,v91,v122,v138,v143]) .nil .nil)) (.node (6,[v12,v20,v45,v91,v134,v185,v241]) (.node (6,[v12,v20,v45,v91,v134,v185,v237]) .nil .nil) (.node (6,[v12,v20,v45,v91,v138,v143,v260]) .nil .nil)))) (.node (6,[v12,v20,v45,v91,v143,v241,v263]) (.node (6,[v12,v20,v45,v91,v143,v180,v241]) (.node (6,[v12,v20,v45,v91,v138,v185,v261]) (.node (6,[v12,v20,v45,v91,v138,v185,v241]) .nil .nil) (.node (6,[v12,v20,v45,v91,v143,v180,v237]) .nil .nil)) (.node (6,[v12,v20,v45,v91,v143,v185,v241]) (.node (6,[v12,v20,v45,v91,v143,v185,v237]) .nil .nil) (.node (6,[v12,v20,v45,v91,v143,v237,v260]) .nil .nil))) (.node (6,[v12,v20,v45,v91,v172,v185,v241]) (.node (6,[v12,v20,v45,v91,v153,v185,v241]) (.node (6,[v12,v20,v45,v91,v147,v185,v241]) .nil .nil) (.node (6,[v12,v20,v45,v91,v155,v185,v241]) .nil .nil)) (.node (6,[v12,v20,v45,v91,v185,v209,v241]) (.node (6,[v12,v20,v45,v91,v174,v185,v241]) .nil .nil) (.node (6,[v12,v20,v45,v91,v185,v211,v241]) .nil .nil)))))
noncomputable def stem_93 : Tree := .node (6,[v12,v20,v45,v85,v115,v143,v172]) stem_92 block_96
noncomputable def block_97 : Tree := (.node (6,[v12,v20,v52,v66,v91,v155,v185]) (.node (6,[v12,v20,v48,v85,v91,v138,v143]) (.node (6,[v12,v20,v46,v66,v91,v138,v185]) (.node (6,[v12,v20,v45,v143,v185,v241,v269]) (.node (6,[v12,v20,v45,v138,v185,v241,v269]) (.node (6,[v12,v20,v45,v91,v185,v241,v269]) .nil .nil) .nil) (.node (6,[v12,v20,v45,v185,v241,v269]) .nil .nil)) (.node (6,[v12,v20,v47,v85,v91,v138,v143]) (.node (6,[v12,v20,v47,v66,v91,v138,v185]) .nil .nil) (.node (6,[v12,v20,v48,v66,v91,v138,v185]) .nil .nil))) (.node (6,[v12,v20,v50,v85,v91,v138,v143]) (.node (6,[v12,v20,v49,v85,v91,v138,v143]) (.node (6,[v12,v20,v49,v66,v91,v138,v185]) .nil .nil) (.node (6,[v12,v20,v50,v66,v91,v138,v185]) .nil .nil)) (.node (6,[v12,v20,v52,v66,v91,v134,v185]) (.node (6,[v12,v20,v52,v66,v85,v138,v269]) .nil .nil) (.node (6,[v12,v20,v52,v66,v91,v138,v185]) .nil .nil)))) (.node (6,[v12,v20,v52,v85,v91,v138,v185]) (.node (6,[v12,v20,v52,v66,v115,v138,v185]) (.node (6,[v12,v20,v52,v66,v91,v185,v209]) (.node (6,[v12,v20,v52,v66,v91,v172,v185]) .nil .nil) (.node (6,[v12,v20,v52,v66,v91,v185,v219]) .nil .nil)) (.node (6,[v12,v20,v52,v85,v91,v134,v143]) (.node (6,[v12,v20,v52,v66,v138,v185,v269]) .nil .nil) (.node (6,[v12,v20,v52,v85,v91,v138,v143]) .nil .nil))) (.node (6,[v12,v20,v52,v85,v91,v143,v209]) (.node (6,[v12,v20,v52,v85,v91,v143,v155]) (.node (6,[v12,v20,v52,v85,v91,v138,v269]) .nil .nil) (.node (6,[v12,v20,v52,v85,v91,v143,v172]) .nil .nil)) (.node (6,[v12,v20,v52,v85,v91,v143,v241]) (.node (6,[v12,v20,v52,v85,v91,v143,v219]) .nil .nil) (.node (6,[v12,v20,v52,v85,v115,v138,v143]) .nil .nil)))))
noncomputable def block_98 : Tree := (.node (6,[v12,v20,v66,v91,v97,v185,v209]) (.node (6,[v12,v20,v60,v66,v91,v185,v209]) (.node (6,[v12,v20,v56,v85,v91,v138,v143]) (.node (6,[v12,v20,v55,v66,v104,v138,v143]) (.node (6,[v12,v20,v55,v66,v91,v143,v209]) (.node (6,[v12,v20,v52,v91,v143,v185,v241]) .nil .nil) .nil) (.node (6,[v12,v20,v56,v66,v91,v138,v185]) .nil .nil)) (.node (6,[v12,v20,v57,v66,v102,v138,v143]) (.node (6,[v12,v20,v57,v66,v91,v185,v209]) .nil .nil) (.node (6,[v12,v20,v57,v85,v91,v143,v209]) .nil .nil))) (.node (6,[v12,v20,v66,v79,v91,v185,v209]) (.node (6,[v12,v20,v64,v66,v91,v185,v209]) (.node (6,[v12,v20,v60,v85,v91,v143,v209]) .nil .nil) (.node (6,[v12,v20,v66,v73,v91,v185,v209]) .nil .nil)) (.node (6,[v12,v20,v66,v85,v91,v143,v205]) (.node (6,[v12,v20,v66,v81,v91,v143,v209]) .nil .nil) (.node (6,[v12,v20,v66,v85,v91,v185,v209]) .nil .nil)))) (.node (6,[v12,v20,v66,v91,v134,v185,v209]) (.node (6,[v12,v20,v66,v91,v107,v185,v209]) (.node (6,[v12,v20,v66,v91,v103,v138,v185]) (.node (6,[v12,v20,v66,v91,v101,v185,v209]) .nil .nil) (.node (6,[v12,v20,v66,v91,v104,v185,v209]) .nil .nil)) (.node (6,[v12,v20,v66,v91,v120,v185,v209]) (.node (6,[v12,v20,v66,v91,v115,v185,v209]) .nil .nil) (.node (6,[v12,v20,v66,v91,v134,v185,v205]) .nil .nil))) (.node (6,[v12,v20,v66,v91,v143,v180,v205]) (.node (6,[v12,v20,v66,v91,v138,v185,v209]) (.node (6,[v12,v20,v66,v91,v138,v185,v205]) .nil .nil) (.node (6,[v12,v20,v66,v91,v138,v185,v219]) .nil .nil)) (.node (6,[v12,v20,v66,v91,v143,v185,v205]) (.node (6,[v12,v20,v66,v91,v143,v180,v209]) .nil .nil) (.node (6,[v12,v20,v66,v91,v143,v185,v209]) .nil .nil)))))
noncomputable def stem_94 : Tree := .node (6,[v12,v20,v52,v91,v138,v185,v241]) block_97 block_98
noncomputable def stem_95 : Tree := .node (6,[v12,v20,v45,v91,v185,v241,v265]) stem_93 stem_94
noncomputable def stem_96 : Tree := .node (6,[v12,v20,v45,v85,v91,v143,v172]) stem_91 stem_95
noncomputable def block_99 : Tree := (.node (6,[v12,v20,v66,v91,v185,v185,v209]) (.node (6,[v12,v20,v66,v91,v156,v185,v209]) (.node (6,[v12,v20,v66,v91,v155,v185,v209]) (.node (6,[v12,v20,v66,v91,v153,v185,v209]) (.node (6,[v12,v20,v66,v91,v147,v185,v209]) .nil .nil) .nil) (.node (6,[v12,v20,v66,v91,v155,v185,v219]) .nil .nil)) (.node (6,[v12,v20,v66,v91,v174,v185,v209]) (.node (6,[v12,v20,v66,v91,v172,v185,v209]) .nil .nil) (.node (6,[v12,v20,v66,v91,v181,v185,v209]) .nil .nil))) (.node (6,[v12,v20,v66,v91,v185,v205]) (.node (6,[v12,v20,v66,v91,v185,v193,v209]) (.node (6,[v12,v20,v66,v91,v185,v186,v209]) .nil .nil) (.node (6,[v12,v20,v66,v91,v185,v195,v209]) .nil .nil)) (.node (6,[v12,v20,v66,v91,v185,v209,v209]) (.node (6,[v12,v20,v66,v91,v185,v209]) .nil .nil) (.node (6,[v12,v20,v66,v91,v185,v209,v211]) .nil .nil))))
noncomputable def block_100 : Tree := (.node (6,[v12,v20,v66,v91,v185,v209,v265]) (.node (6,[v12,v20,v66,v91,v185,v209,v229]) (.node (6,[v12,v20,v66,v91,v185,v209,v227]) (.node (6,[v12,v20,v66,v91,v185,v209,v225]) (.node (6,[v12,v20,v66,v91,v185,v209,v219]) .nil .nil) .nil) (.node (6,[v12,v20,v66,v91,v185,v209,v228]) .nil .nil)) (.node (6,[v12,v20,v66,v91,v185,v209,v243]) (.node (6,[v12,v20,v66,v91,v185,v209,v241]) .nil .nil) (.node (6,[v12,v20,v66,v91,v185,v209,v263]) .nil .nil))) (.node (6,[v12,v20,v66,v91,v185,v209,v297]) (.node (6,[v12,v20,v66,v91,v185,v209,v283]) (.node (6,[v12,v20,v66,v91,v185,v209,v269]) .nil .nil) (.node (6,[v12,v20,v66,v91,v185,v209,v287]) .nil .nil)) (.node (6,[v12,v20,v66,v138,v185,v209,v269]) (.node (6,[v12,v20,v66,v91,v185,v219]) .nil .nil) (.node (6,[v12,v20,v66,v143,v185,v209,v269]) .nil .nil))))
noncomputable def stem_97 : Tree := .node (6,[v12,v20,v66,v91,v185,v209,v213]) block_99 block_100
noncomputable def block_101 : Tree := (.node (6,[v12,v21,v45,v85,v91,v138,v143]) (.node (6,[v12,v20,v85,v91,v143,v209,v211]) (.node (6,[v12,v20,v85,v91,v138,v143,v205]) (.node (6,[v12,v20,v85,v91,v120,v143,v209]) (.node (6,[v12,v20,v85,v91,v104,v143,v209]) (.node (6,[v12,v20,v85,v91,v103,v138,v143]) .nil .nil) .nil) (.node (6,[v12,v20,v85,v91,v134,v143,v205]) .nil .nil)) (.node (6,[v12,v20,v85,v91,v143,v185,v209]) (.node (6,[v12,v20,v85,v91,v138,v185,v209]) .nil .nil) (.node (6,[v12,v20,v85,v91,v143,v205]) .nil .nil))) (.node (6,[v12,v20,v91,v185,v209,v241]) (.node (6,[v12,v20,v91,v138,v185,v209,v241]) (.node (6,[v12,v20,v85,v91,v185,v209]) .nil .nil) (.node (6,[v12,v20,v91,v143,v185,v209,v241]) .nil .nil)) (.node (6,[v12,v21,v29,v45,v91,v143,v241]) (.node (6,[v12,v21,v29,v45,v66,v138,v269]) .nil .nil) (.node (6,[v12,v21,v29,v66,v91,v143,v209]) .nil .nil)))) (.node (6,[v12,v23,v29,v66,v91,v143,v209]) (.node (6,[v12,v22,v45,v66,v91,v138,v185]) (.node (6,[v12,v22,v29,v45,v91,v143,v241]) (.node (6,[v12,v22,v29,v45,v66,v138,v269]) .nil .nil) (.node (6,[v12,v22,v29,v66,v91,v143,v209]) .nil .nil)) (.node (6,[v12,v23,v29,v45,v66,v138,v269]) (.node (6,[v12,v22,v45,v85,v91,v138,v143]) .nil .nil) (.node (6,[v12,v23,v29,v45,v91,v143,v241]) .nil .nil))) (.node (6,[v12,v24,v29,v45,v91,v143,v241]) (.node (6,[v12,v24,v29,v45,v66,v91,v134]) (.node (6,[v12,v23,v45,v66,v91,v138,v185]) .nil .nil) (.node (6,[v12,v24,v29,v45,v66,v138,v269]) .nil .nil)) (.node (6,[v12,v24,v45,v66,v91,v138,v185]) (.node (6,[v12,v24,v29,v66,v91,v143,v209]) .nil .nil) (.node (6,[v12,v24,v45,v85,v91,v138,v143]) .nil .nil)))))
noncomputable def stem_98 : Tree := .node (6,[v12,v20,v66,v185,v209,v269]) stem_97 block_101
noncomputable def block_102 : Tree := (.node (6,[v12,v28,v45,v66,v91,v143,v172]) (.node (6,[v12,v27,v45,v66,v91,v172,v185]) (.node (6,[v12,v25,v45,v66,v91,v138,v185]) (.node (6,[v12,v25,v29,v66,v91,v143,v209]) (.node (6,[v12,v25,v29,v45,v91,v143,v241]) .nil .nil) .nil) (.node (6,[v12,v25,v45,v85,v91,v138,v143]) .nil .nil)) (.node (6,[v12,v27,v45,v85,v91,v143,v172]) (.node (6,[v12,v27,v45,v66,v115,v138,v185]) .nil .nil) (.node (6,[v12,v27,v45,v85,v115,v138,v143]) .nil .nil))) (.node (6,[v12,v29,v35,v66,v91,v143,v209]) (.node (6,[v12,v29,v35,v45,v66,v138,v269]) (.node (6,[v12,v28,v45,v66,v115,v138,v143]) .nil .nil) (.node (6,[v12,v29,v35,v45,v91,v143,v241]) .nil .nil)) (.node (6,[v12,v29,v40,v66,v115,v143,v209]) (.node (6,[v12,v29,v40,v66,v104,v143,v172]) .nil .nil) (.node (6,[v12,v29,v44,v66,v91,v143,v172]) .nil .nil))))
noncomputable def block_103 : Tree := (.node (6,[v12,v29,v45,v66,v91,v115,v142]) (.node (6,[v12,v29,v45,v65,v91,v143,v172]) (.node (6,[v12,v29,v45,v64,v97,v143,v172]) (.node (6,[v12,v29,v45,v53,v91,v143,v241]) (.node (6,[v12,v29,v45,v53,v66,v138,v269]) .nil .nil) .nil) (.node (6,[v12,v29,v45,v64,v115,v143,v241]) .nil .nil)) (.node (6,[v12,v29,v45,v66,v78,v138,v269]) (.node (6,[v12,v29,v45,v65,v115,v138,v143]) .nil .nil) (.node (6,[v12,v29,v45,v66,v90,v143,v172]) .nil .nil))) (.node (6,[v12,v29,v45,v66,v91,v143,v169]) (.node (6,[v12,v29,v45,v66,v91,v142,v173]) (.node (6,[v12,v29,v45,v66,v91,v142,v172]) .nil .nil) (.node (6,[v12,v29,v45,v66,v91,v143,v168]) .nil .nil)) (.node (6,[v12,v29,v45,v66,v91,v143,v171]) (.node (6,[v12,v29,v45,v66,v91,v143,v170]) .nil .nil) (.node (6,[v12,v29,v45,v66,v91,v143,v172]) .nil .nil))))
noncomputable def stem_99 : Tree := .node (6,[v12,v29,v44,v66,v115,v138,v143]) block_102 block_103
noncomputable def block_104 : Tree := (.node (6,[v12,v29,v45,v66,v93,v143,v172]) (.node (6,[v12,v29,v45,v66,v91,v159,v172]) (.node (6,[v12,v29,v45,v66,v91,v143,v256]) (.node (6,[v12,v29,v45,v66,v91,v143,v189]) (.node (6,[v12,v29,v45,v66,v91,v143,v177]) (.node (6,[v12,v29,v45,v66,v91,v143,v175]) .nil .nil) .nil) (.node (6,[v12,v29,v45,v66,v91,v143,v221]) .nil .nil)) (.node (6,[v12,v29,v45,v66,v91,v149,v172]) (.node (6,[v12,v29,v45,v66,v91,v144,v172]) .nil .nil) (.node (6,[v12,v29,v45,v66,v91,v151,v172]) .nil .nil))) (.node (6,[v12,v29,v45,v66,v91,v172,v185]) (.node (6,[v12,v29,v45,v66,v91,v168,v185]) (.node (6,[v12,v29,v45,v66,v91,v166,v172]) .nil .nil) (.node (6,[v12,v29,v45,v66,v91,v168,v243]) .nil .nil)) (.node (6,[v12,v29,v45,v66,v91,v172,v235]) (.node (6,[v12,v29,v45,v66,v91,v172,v199]) .nil .nil) (.node (6,[v12,v29,v45,v66,v92,v143,v172]) .nil .nil)))) (.node (6,[v12,v29,v45,v66,v115,v134,v143]) (.node (6,[v12,v29,v45,v66,v102,v143,v172]) (.node (6,[v12,v29,v45,v66,v95,v143,v172]) (.node (6,[v12,v29,v45,v66,v94,v143,v172]) .nil .nil) (.node (6,[v12,v29,v45,v66,v99,v143,v172]) .nil .nil)) (.node (6,[v12,v29,v45,v66,v113,v138,v143]) (.node (6,[v12,v29,v45,v66,v111,v143,v172]) .nil .nil) (.node (6,[v12,v29,v45,v66,v114,v138,v143]) .nil .nil))) (.node (6,[v12,v29,v45,v66,v115,v134,v243]) (.node (6,[v12,v29,v45,v66,v115,v134,v174]) (.node (6,[v12,v29,v45,v66,v115,v134,v147]) .nil .nil) (.node (6,[v12,v29,v45,v66,v115,v134,v185]) .nil .nil)) (.node (6,[v12,v29,v45,v66,v115,v134,v296]) (.node (6,[v12,v29,v45,v66,v115,v134,v269]) .nil .nil) (.node (6,[v12,v29,v45,v66,v115,v135,v143]) .nil .nil)))))
noncomputable def stem_100 : Tree := .node (6,[v12,v29,v45,v66,v91,v143,v173]) stem_99 block_104
noncomputable def stem_101 : Tree := .node (6,[v12,v25,v29,v45,v66,v138,v269]) stem_98 stem_100
noncomputable def block_105 : Tree := (.node (6,[v12,v29,v45,v66,v115,v138,v166]) (.node (6,[v12,v29,v45,v66,v115,v138,v145]) (.node (6,[v12,v29,v45,v66,v115,v138,v143]) (.node (6,[v12,v29,v45,v66,v115,v138,v142]) (.node (6,[v12,v29,v45,v66,v115,v137,v143]) .nil .nil) .nil) (.node (6,[v12,v29,v45,v66,v115,v138,v144]) .nil .nil)) (.node (6,[v12,v29,v45,v66,v115,v138,v151]) (.node (6,[v12,v29,v45,v66,v115,v138,v149]) .nil .nil) (.node (6,[v12,v29,v45,v66,v115,v138,v159]) .nil .nil))) (.node (6,[v12,v29,v45,v66,v115,v138,v269]) (.node (6,[v12,v29,v45,v66,v115,v138,v199]) (.node (6,[v12,v29,v45,v66,v115,v138,v185]) .nil .nil) (.node (6,[v12,v29,v45,v66,v115,v138,v235]) .nil .nil)) (.node (6,[v12,v29,v45,v66,v115,v139,v143]) (.node (6,[v12,v29,v45,v66,v115,v138,v297]) .nil .nil) (.node (6,[v12,v29,v45,v66,v115,v140,v143]) .nil .nil))))
noncomputable def block_106 : Tree := (.node (6,[v12,v29,v45,v66,v115,v143,v157]) (.node (6,[v12,v29,v45,v66,v115,v143,v148]) (.node (6,[v12,v29,v45,v66,v115,v142,v155]) (.node (6,[v12,v29,v45,v66,v115,v142,v143]) (.node (6,[v12,v29,v45,v66,v115,v142]) .nil .nil) .nil) (.node (6,[v12,v29,v45,v66,v115,v143,v146]) .nil .nil)) (.node (6,[v12,v29,v45,v66,v115,v143,v152]) (.node (6,[v12,v29,v45,v66,v115,v143,v150]) .nil .nil) (.node (6,[v12,v29,v45,v66,v115,v143,v155]) .nil .nil))) (.node (6,[v12,v29,v45,v66,v115,v143,v179]) (.node (6,[v12,v29,v45,v66,v115,v143,v168]) (.node (6,[v12,v29,v45,v66,v115,v143,v165]) .nil .nil) (.node (6,[v12,v29,v45,v66,v115,v143,v172]) .nil .nil)) (.node (6,[v12,v29,v45,v66,v115,v143,v205]) (.node (6,[v12,v29,v45,v66,v115,v143,v197]) .nil .nil) (.node (6,[v12,v29,v45,v66,v115,v143,v209]) .nil .nil))))
noncomputable def stem_102 : Tree := .node (6,[v12,v29,v45,v66,v115,v141,v143]) block_105 block_106
noncomputable def block_107 : Tree := (.node (6,[v12,v29,v45,v66,v134,v143,v293]) (.node (6,[v12,v29,v45,v66,v115,v155,v269]) (.node (6,[v12,v29,v45,v66,v115,v143,v248]) (.node (6,[v12,v29,v45,v66,v115,v143,v237]) (.node (6,[v12,v29,v45,v66,v115,v143,v234]) (.node (6,[v12,v29,v45,v66,v115,v143,v229]) .nil .nil) .nil) (.node (6,[v12,v29,v45,v66,v115,v143,v241]) .nil .nil)) (.node (6,[v12,v29,v45,v66,v115,v143,v287]) (.node (6,[v12,v29,v45,v66,v115,v143,v257]) .nil .nil) (.node (6,[v12,v29,v45,v66,v115,v155,v185]) .nil .nil))) (.node (6,[v12,v29,v45,v66,v115,v241,v269]) (.node (6,[v12,v29,v45,v66,v115,v185,v209]) (.node (6,[v12,v29,v45,v66,v115,v172,v185]) .nil .nil) (.node (6,[v12,v29,v45,v66,v115,v209,v269]) .nil .nil)) (.node (6,[v12,v29,v45,v66,v117,v138,v143]) (.node (6,[v12,v29,v45,v66,v116,v138,v143]) .nil .nil) (.node (6,[v12,v29,v45,v66,v125,v138,v143]) .nil .nil)))) (.node (6,[v12,v29,v45,v66,v143,v168,v269]) (.node (6,[v12,v29,v45,v66,v138,v168,v269]) (.node (6,[v12,v29,v45,v66,v134,v172,v269]) (.node (6,[v12,v29,v45,v66,v134,v168,v269]) .nil .nil) (.node (6,[v12,v29,v45,v66,v138,v143,v293]) .nil .nil)) (.node (6,[v12,v29,v45,v66,v138,v269,v294]) (.node (6,[v12,v29,v45,v66,v138,v172,v269]) .nil .nil) (.node (6,[v12,v29,v45,v66,v143,v168,v264]) .nil .nil))) (.node (6,[v12,v29,v45,v66,v143,v172,v296]) (.node (6,[v12,v29,v45,v66,v143,v172,v264]) (.node (6,[v12,v29,v45,v66,v143,v168,v293]) .nil .nil) (.node (6,[v12,v29,v45,v66,v143,v172,v269]) .nil .nil)) (.node (6,[v12,v29,v45,v66,v153,v172,v269]) (.node (6,[v12,v29,v45,v66,v147,v172,v269]) .nil .nil) (.node (6,[v12,v29,v45,v66,v155,v172,v269]) .nil .nil)))))
noncomputable def stem_103 : Tree := .node (6,[v12,v29,v45,v66,v115,v143,v219]) stem_102 block_107
noncomputable def block_108 : Tree := (.node (6,[v12,v29,v45,v74,v115,v138,v143]) (.node (6,[v12,v29,v45,v68,v115,v138,v143]) (.node (6,[v12,v29,v45,v66,v172,v243,v269]) (.node (6,[v12,v29,v45,v66,v172,v211,v269]) (.node (6,[v12,v29,v45,v66,v172,v209,v269]) (.node (6,[v12,v29,v45,v66,v172,v185,v269]) .nil .nil) .nil) (.node (6,[v12,v29,v45,v66,v172,v241,v269]) .nil .nil)) (.node (6,[v12,v29,v45,v67,v115,v138,v143]) (.node (6,[v12,v29,v45,v67,v91,v143,v172]) .nil .nil) (.node (6,[v12,v29,v45,v68,v91,v143,v172]) .nil .nil))) (.node (6,[v12,v29,v45,v71,v91,v143,v172]) (.node (6,[v12,v29,v45,v70,v91,v143,v172]) (.node (6,[v12,v29,v45,v69,v91,v143,v172]) .nil .nil) (.node (6,[v12,v29,v45,v70,v115,v138,v143]) .nil .nil)) (.node (6,[v12,v29,v45,v73,v115,v143,v241]) (.node (6,[v12,v29,v45,v71,v115,v138,v143]) .nil .nil) (.node (6,[v12,v29,v45,v74,v91,v143,v172]) .nil .nil)))) (.node (6,[v12,v29,v45,v85,v115,v138,v143]) (.node (6,[v12,v29,v45,v85,v91,v143,v168]) (.node (6,[v12,v29,v45,v77,v115,v138,v143]) (.node (6,[v12,v29,v45,v77,v91,v143,v172]) .nil .nil) (.node (6,[v12,v29,v45,v78,v91,v143,v241]) .nil .nil)) (.node (6,[v12,v29,v45,v85,v91,v172,v185]) (.node (6,[v12,v29,v45,v85,v91,v143,v172]) .nil .nil) (.node (6,[v12,v29,v45,v85,v115,v134,v143]) .nil .nil))) (.node (6,[v12,v29,v45,v85,v115,v143,v172]) (.node (6,[v12,v29,v45,v85,v115,v138,v269]) (.node (6,[v12,v29,v45,v85,v115,v138,v185]) .nil .nil) (.node (6,[v12,v29,v45,v85,v115,v143,v155]) .nil .nil)) (.node (6,[v12,v29,v45,v85,v115,v143,v241]) (.node (6,[v12,v29,v45,v85,v115,v143,v209]) .nil .nil) (.node (6,[v12,v29,v45,v91,v96,v143,v172]) .nil .nil)))))
noncomputable def block_109 : Tree := (.node (6,[v12,v29,v45,v115,v134,v143,v237]) (.node (6,[v12,v29,v45,v91,v172,v185,v241]) (.node (6,[v12,v29,v45,v91,v143,v172,v237]) (.node (6,[v12,v29,v45,v91,v143,v168,v237]) (.node (6,[v12,v29,v45,v91,v115,v241,v269]) (.node (6,[v12,v29,v45,v91,v115,v143,v241]) .nil .nil) .nil) (.node (6,[v12,v29,v45,v91,v143,v168,v241]) .nil .nil)) (.node (6,[v12,v29,v45,v91,v143,v172,v261]) (.node (6,[v12,v29,v45,v91,v143,v172,v241]) .nil .nil) (.node (6,[v12,v29,v45,v91,v143,v241,v294]) .nil .nil))) (.node (6,[v12,v29,v45,v101,v115,v143,v241]) (.node (6,[v12,v29,v45,v96,v115,v138,v143]) (.node (6,[v12,v29,v45,v91,v172,v241,v269]) .nil .nil) (.node (6,[v12,v29,v45,v97,v115,v143,v241]) .nil .nil)) (.node (6,[v12,v29,v45,v107,v115,v143,v241]) (.node (6,[v12,v29,v45,v104,v115,v143,v241]) .nil .nil) (.node (6,[v12,v29,v45,v115,v120,v143,v241]) .nil .nil)))) (.node (6,[v12,v29,v45,v143,v172,v241,v269]) (.node (6,[v12,v29,v45,v115,v143,v241,v243]) (.node (6,[v12,v29,v45,v115,v138,v241,v269]) (.node (6,[v12,v29,v45,v115,v138,v143,v237]) .nil .nil) (.node (6,[v12,v29,v45,v115,v143,v237]) .nil .nil)) (.node (6,[v12,v29,v45,v115,v241,v269]) (.node (6,[v12,v29,v45,v115,v143,v241,v269]) .nil .nil) (.node (6,[v12,v29,v45,v138,v172,v241,v269]) .nil .nil))) (.node (6,[v12,v29,v47,v66,v91,v143,v172]) (.node (6,[v12,v29,v46,v66,v91,v143,v172]) (.node (6,[v12,v29,v45,v172,v241,v269]) .nil .nil) (.node (6,[v12,v29,v46,v66,v115,v138,v143]) .nil .nil)) (.node (6,[v12,v29,v48,v66,v115,v138,v143]) (.node (6,[v12,v29,v48,v66,v91,v143,v172]) .nil .nil) (.node (6,[v12,v29,v49,v66,v91,v143,v172]) .nil .nil)))))
noncomputable def stem_104 : Tree := .node (6,[v12,v29,v45,v91,v115,v143,v237]) block_108 block_109
noncomputable def stem_105 : Tree := .node (6,[v12,v29,v45,v66,v172,v181,v269]) stem_103 stem_104
noncomputable def stem_106 : Tree := .node (6,[v12,v29,v45,v66,v115,v136,v143]) stem_101 stem_105
noncomputable def stem_107 : Tree := .node (6,[v12,v20,v66,v91,v143,v185,v219]) stem_96 stem_106
noncomputable def block_110 : Tree := (.node (6,[v12,v29,v52,v66,v115,v138,v269]) (.node (6,[v12,v29,v52,v66,v91,v172,v185]) (.node (6,[v12,v29,v52,v66,v91,v143,v168]) (.node (6,[v12,v29,v50,v66,v115,v138,v143]) (.node (6,[v12,v29,v50,v66,v91,v143,v172]) .nil .nil) .nil) (.node (6,[v12,v29,v52,v66,v91,v143,v172]) .nil .nil)) (.node (6,[v12,v29,v52,v66,v115,v138,v143]) (.node (6,[v12,v29,v52,v66,v115,v134,v143]) .nil .nil) (.node (6,[v12,v29,v52,v66,v115,v138,v185]) .nil .nil))) (.node (6,[v12,v29,v52,v66,v115,v143,v219]) (.node (6,[v12,v29,v52,v66,v115,v143,v172]) (.node (6,[v12,v29,v52,v66,v115,v143,v155]) .nil .nil) (.node (6,[v12,v29,v52,v66,v115,v143,v209]) .nil .nil)) (.node (6,[v12,v29,v52,v66,v138,v172,v269]) (.node (6,[v12,v29,v52,v66,v115,v143,v241]) .nil .nil) (.node (6,[v12,v29,v52,v66,v143,v172,v269]) .nil .nil))))
noncomputable def block_111 : Tree := (.node (6,[v12,v29,v66,v91,v103,v143,v172]) (.node (6,[v12,v29,v56,v66,v91,v143,v172]) (.node (6,[v12,v29,v52,v91,v143,v172,v241]) (.node (6,[v12,v29,v52,v91,v115,v143,v241]) (.node (6,[v12,v29,v52,v85,v115,v138,v143]) .nil .nil) .nil) (.node (6,[v12,v29,v53,v66,v91,v143,v209]) .nil .nil)) (.node (6,[v12,v29,v57,v66,v115,v143,v209]) (.node (6,[v12,v29,v56,v66,v115,v138,v143]) .nil .nil) (.node (6,[v12,v29,v66,v78,v91,v143,v209]) .nil .nil))) (.node (6,[v12,v29,v66,v91,v115,v185,v209]) (.node (6,[v12,v29,v66,v91,v115,v143,v209]) (.node (6,[v12,v29,v66,v91,v115,v143,v205]) .nil .nil) (.node (6,[v12,v29,v66,v91,v115,v143,v219]) .nil .nil)) (.node (6,[v12,v29,v66,v91,v143,v168,v205]) (.node (6,[v12,v29,v66,v91,v115,v209,v269]) .nil .nil) (.node (6,[v12,v29,v66,v91,v143,v168,v209]) .nil .nil))))
noncomputable def stem_108 : Tree := .node (6,[v12,v29,v52,v85,v91,v143,v172]) block_110 block_111
noncomputable def block_112 : Tree := (.node (6,[v12,v29,v66,v115,v143,v209,v269]) (.node (6,[v12,v29,v66,v104,v115,v143,v209]) (.node (6,[v12,v29,v66,v91,v172,v209,v269]) (.node (6,[v12,v29,v66,v91,v143,v209,v294]) (.node (6,[v12,v29,v66,v91,v143,v172,v219]) (.node (6,[v12,v29,v66,v91,v143,v172,v209]) .nil .nil) .nil) (.node (6,[v12,v29,v66,v91,v172,v185,v209]) .nil .nil)) (.node (6,[v12,v29,v66,v101,v115,v143,v209]) (.node (6,[v12,v29,v66,v97,v115,v143,v209]) .nil .nil) (.node (6,[v12,v29,v66,v103,v115,v138,v143]) .nil .nil))) (.node (6,[v12,v29,v66,v115,v138,v143,v205]) (.node (6,[v12,v29,v66,v115,v120,v143,v209]) (.node (6,[v12,v29,v66,v107,v115,v143,v209]) .nil .nil) (.node (6,[v12,v29,v66,v115,v134,v143,v205]) .nil .nil)) (.node (6,[v12,v29,v66,v115,v143,v205]) (.node (6,[v12,v29,v66,v115,v138,v209,v269]) .nil .nil) (.node (6,[v12,v29,v66,v115,v143,v209,v211]) .nil .nil)))) (.node (6,[v12,v29,v91,v143,v172,v209,v241]) (.node (6,[v12,v29,v66,v172,v209,v269]) (.node (6,[v12,v29,v66,v138,v172,v209,v269]) (.node (6,[v12,v29,v66,v115,v209,v269]) .nil .nil) (.node (6,[v12,v29,v66,v143,v172,v209,v269]) .nil .nil)) (.node (6,[v12,v29,v85,v91,v143,v172,v209]) (.node (6,[v12,v29,v85,v91,v115,v143,v209]) .nil .nil) (.node (6,[v12,v29,v91,v115,v143,v209,v241]) .nil .nil))) (.node (6,[v12,v32,v45,v66,v115,v138,v143]) (.node (6,[v12,v31,v45,v66,v115,v138,v143]) (.node (6,[v12,v30,v45,v66,v91,v143,v172]) .nil .nil) (.node (6,[v12,v32,v45,v66,v91,v143,v172]) .nil .nil)) (.node (6,[v12,v33,v45,v66,v115,v138,v143]) (.node (6,[v12,v33,v45,v66,v91,v143,v172]) .nil .nil) (.node (6,[v12,v34,v45,v66,v91,v143,v172]) .nil .nil)))))
noncomputable def stem_109 : Tree := .node (6,[v12,v29,v66,v91,v143,v172,v205]) stem_108 block_112
noncomputable def block_113 : Tree := (.node (6,[v12,v39,v45,v66,v91,v172,v185]) (.node (6,[v12,v36,v45,v66,v115,v138,v185]) (.node (6,[v12,v35,v57,v66,v91,v138,v143]) (.node (6,[v12,v35,v45,v85,v91,v138,v143]) (.node (6,[v12,v35,v45,v66,v91,v138,v185]) .nil .nil) .nil) (.node (6,[v12,v36,v45,v66,v91,v172,v185]) .nil .nil)) (.node (6,[v12,v36,v45,v85,v115,v138,v143]) (.node (6,[v12,v36,v45,v85,v91,v143,v172]) .nil .nil) (.node (6,[v12,v36,v56,v66,v91,v138,v143]) .nil .nil))) (.node (6,[v12,v40,v45,v66,v91,v172,v185]) (.node (6,[v12,v39,v45,v85,v91,v143,v172]) (.node (6,[v12,v39,v45,v66,v115,v138,v185]) .nil .nil) (.node (6,[v12,v39,v45,v85,v115,v138,v143]) .nil .nil)) (.node (6,[v12,v45,v52,v66,v91,v172,v185]) (.node (6,[v12,v40,v45,v85,v115,v138,v143]) .nil .nil) (.node (6,[v12,v45,v52,v85,v115,v138,v143]) .nil .nil))))
noncomputable def block_114 : Tree := (.node (6,[v12,v45,v60,v66,v115,v138,v185]) (.node (6,[v12,v45,v57,v66,v115,v138,v185]) (.node (6,[v12,v45,v55,v66,v115,v138,v143]) (.node (6,[v12,v45,v55,v66,v91,v143,v172]) (.node (6,[v12,v45,v53,v85,v91,v138,v143]) .nil .nil) .nil) (.node (6,[v12,v45,v57,v66,v91,v172,v185]) .nil .nil)) (.node (6,[v12,v45,v57,v85,v115,v138,v143]) (.node (6,[v12,v45,v57,v85,v91,v143,v172]) .nil .nil) (.node (6,[v12,v45,v60,v66,v91,v172,v185]) .nil .nil))) (.node (6,[v12,v45,v64,v85,v115,v138,v143]) (.node (6,[v12,v45,v60,v85,v115,v138,v143]) (.node (6,[v12,v45,v60,v85,v91,v143,v172]) .nil .nil) (.node (6,[v12,v45,v64,v66,v91,v172,v185]) .nil .nil)) (.node (6,[v12,v45,v66,v78,v91,v138,v185]) (.node (6,[v12,v45,v66,v73,v91,v172,v185]) .nil .nil) (.node (6,[v12,v45,v66,v79,v91,v172,v185]) .nil .nil))))
noncomputable def stem_110 : Tree := .node (6,[v12,v45,v53,v66,v91,v138,v185]) block_113 block_114
noncomputable def block_115 : Tree := (.node (6,[v12,v45,v66,v91,v115,v172,v185]) (.node (6,[v12,v45,v66,v85,v115,v143,v155]) (.node (6,[v12,v45,v66,v85,v115,v134,v143]) (.node (6,[v12,v45,v66,v85,v91,v143,v168]) (.node (6,[v12,v45,v66,v81,v115,v138,v143]) (.node (6,[v12,v45,v66,v81,v91,v143,v172]) .nil .nil) .nil) (.node (6,[v12,v45,v66,v85,v91,v172,v185]) .nil .nil)) (.node (6,[v12,v45,v66,v85,v115,v138,v185]) (.node (6,[v12,v45,v66,v85,v115,v138,v143]) .nil .nil) (.node (6,[v12,v45,v66,v85,v115,v138,v269]) .nil .nil))) (.node (6,[v12,v45,v66,v91,v97,v172,v185]) (.node (6,[v12,v45,v66,v85,v115,v143,v209]) (.node (6,[v12,v45,v66,v85,v115,v143,v172]) .nil .nil) (.node (6,[v12,v45,v66,v85,v115,v143,v241]) .nil .nil)) (.node (6,[v12,v45,v66,v91,v104,v172,v185]) (.node (6,[v12,v45,v66,v91,v101,v172,v185]) .nil .nil) (.node (6,[v12,v45,v66,v91,v107,v172,v185]) .nil .nil)))) (.node (6,[v12,v45,v66,v91,v143,v172,v180]) (.node (6,[v12,v45,v66,v91,v138,v168,v185]) (.node (6,[v12,v45,v66,v91,v134,v168,v185]) (.node (6,[v12,v45,v66,v91,v120,v172,v185]) .nil .nil) (.node (6,[v12,v45,v66,v91,v134,v172,v185]) .nil .nil)) (.node (6,[v12,v45,v66,v91,v143,v168,v180]) (.node (6,[v12,v45,v66,v91,v138,v172,v185]) .nil .nil) (.node (6,[v12,v45,v66,v91,v143,v168,v185]) .nil .nil))) (.node (6,[v12,v45,v66,v91,v155,v172,v185]) (.node (6,[v12,v45,v66,v91,v147,v172,v185]) (.node (6,[v12,v45,v66,v91,v143,v172,v185]) .nil .nil) (.node (6,[v12,v45,v66,v91,v153,v172,v185]) .nil .nil)) (.node (6,[v12,v45,v66,v91,v168,v185]) (.node (6,[v12,v45,v66,v91,v164,v172,v185]) .nil .nil) (.node (6,[v12,v45,v66,v91,v172,v172,v185]) .nil .nil)))))
noncomputable def stem_111 : Tree := .node (6,[v12,v45,v66,v79,v115,v138,v185]) stem_110 block_115
noncomputable def stem_112 : Tree := .node (6,[v12,v34,v45,v66,v115,v138,v143]) stem_109 stem_111
noncomputable def block_116 : Tree := (.node (6,[v12,v45,v66,v91,v172,v185,v194]) (.node (6,[v12,v45,v66,v91,v172,v185,v185]) (.node (6,[v12,v45,v66,v91,v172,v181,v185]) (.node (6,[v12,v45,v66,v91,v172,v179,v185]) (.node (6,[v12,v45,v66,v91,v172,v176,v185]) .nil .nil) .nil) (.node (6,[v12,v45,v66,v91,v172,v185]) .nil .nil)) (.node (6,[v12,v45,v66,v91,v172,v185,v190]) (.node (6,[v12,v45,v66,v91,v172,v185,v186]) .nil .nil) (.node (6,[v12,v45,v66,v91,v172,v185,v193]) .nil .nil))) (.node (6,[v12,v45,v66,v91,v172,v185,v227]) (.node (6,[v12,v45,v66,v91,v172,v185,v209]) (.node (6,[v12,v45,v66,v91,v172,v185,v195]) .nil .nil) (.node (6,[v12,v45,v66,v91,v172,v185,v211]) .nil .nil)) (.node (6,[v12,v45,v66,v91,v172,v185,v241]) (.node (6,[v12,v45,v66,v91,v172,v185,v229]) .nil .nil) (.node (6,[v12,v45,v66,v91,v172,v185,v243]) .nil .nil))))
noncomputable def block_117 : Tree := (.node (6,[v12,v45,v66,v115,v138,v181,v185]) (.node (6,[v12,v45,v66,v91,v172,v185,v297]) (.node (6,[v12,v45,v66,v91,v172,v185,v269]) (.node (6,[v12,v45,v66,v91,v172,v185,v265]) (.node (6,[v12,v45,v66,v91,v172,v185,v263]) .nil .nil) .nil) (.node (6,[v12,v45,v66,v91,v172,v185,v294]) .nil .nil)) (.node (6,[v12,v45,v66,v115,v138,v143,v180]) (.node (6,[v12,v45,v66,v115,v134,v143,v180]) .nil .nil) (.node (6,[v12,v45,v66,v115,v138,v172,v185]) .nil .nil))) (.node (6,[v12,v45,v66,v143,v172,v185,v269]) (.node (6,[v12,v45,v66,v115,v172,v185]) (.node (6,[v12,v45,v66,v115,v143,v172,v185]) .nil .nil) (.node (6,[v12,v45,v66,v138,v172,v185,v269]) .nil .nil)) (.node (6,[v12,v45,v73,v85,v115,v138,v143]) (.node (6,[v12,v45,v66,v172,v185,v269]) .nil .nil) (.node (6,[v12,v45,v76,v85,v115,v138,v143]) .nil .nil))))
noncomputable def stem_113 : Tree := .node (6,[v12,v45,v66,v91,v172,v185,v257]) block_116 block_117
noncomputable def block_118 : Tree := (.node (6,[v12,v45,v85,v91,v143,v168]) (.node (6,[v12,v45,v85,v91,v115,v143,v155]) (.node (6,[v12,v45,v85,v91,v115,v134,v143]) (.node (6,[v12,v45,v85,v88,v115,v138,v143]) (.node (6,[v12,v45,v85,v85,v115,v138,v143]) (.node (6,[v12,v45,v79,v85,v115,v138,v143]) .nil .nil) .nil) (.node (6,[v12,v45,v85,v89,v115,v138,v143]) .nil .nil)) (.node (6,[v12,v45,v85,v91,v115,v138,v185]) (.node (6,[v12,v45,v85,v91,v115,v138,v143]) .nil .nil) (.node (6,[v12,v45,v85,v91,v115,v138,v269]) .nil .nil))) (.node (6,[v12,v45,v85,v91,v120,v143,v172]) (.node (6,[v12,v45,v85,v91,v115,v143,v209]) (.node (6,[v12,v45,v85,v91,v115,v143,v172]) .nil .nil) (.node (6,[v12,v45,v85,v91,v115,v143,v241]) .nil .nil)) (.node (6,[v12,v45,v85,v91,v138,v143,v168]) (.node (6,[v12,v45,v85,v91,v134,v143,v168]) .nil .nil) (.node (6,[v12,v45,v85,v91,v138,v172,v185]) .nil .nil)))) (.node (6,[v12,v45,v85,v115,v115,v138,v143]) (.node (6,[v12,v45,v85,v97,v115,v138,v143]) (.node (6,[v12,v45,v85,v91,v143,v172,v185]) (.node (6,[v12,v45,v85,v91,v143,v172,v174]) .nil .nil) (.node (6,[v12,v45,v85,v91,v172,v185]) .nil .nil)) (.node (6,[v12,v45,v85,v104,v115,v138,v143]) (.node (6,[v12,v45,v85,v101,v115,v138,v143]) .nil .nil) (.node (6,[v12,v45,v85,v107,v115,v138,v143]) .nil .nil))) (.node (6,[v12,v45,v85,v115,v123,v138,v143]) (.node (6,[v12,v45,v85,v115,v119,v138,v143]) (.node (6,[v12,v45,v85,v115,v118,v138,v143]) .nil .nil) (.node (6,[v12,v45,v85,v115,v120,v138,v143]) .nil .nil)) (.node (6,[v12,v45,v85,v115,v126,v138,v143]) (.node (6,[v12,v45,v85,v115,v124,v138,v143]) .nil .nil) (.node (6,[v12,v45,v85,v115,v127,v138,v143]) .nil .nil)))))
noncomputable def stem_114 : Tree := .node (6,[v12,v45,v78,v85,v91,v138,v143]) stem_113 block_118
noncomputable def block_119 : Tree := (.node (6,[v12,v45,v85,v115,v138,v143,v265]) (.node (6,[v12,v45,v85,v115,v138,v143,v181]) (.node (6,[v12,v45,v85,v115,v138,v143,v153]) (.node (6,[v12,v45,v85,v115,v138,v143]) (.node (6,[v12,v45,v85,v115,v134,v143]) (.node (6,[v12,v45,v85,v115,v134,v138,v143]) .nil .nil) .nil) (.node (6,[v12,v45,v85,v115,v138,v143,v147]) .nil .nil)) (.node (6,[v12,v45,v85,v115,v138,v143,v172]) (.node (6,[v12,v45,v85,v115,v138,v143,v155]) .nil .nil) (.node (6,[v12,v45,v85,v115,v138,v143,v174]) .nil .nil))) (.node (6,[v12,v45,v85,v115,v138,v143,v241]) (.node (6,[v12,v45,v85,v115,v138,v143,v209]) (.node (6,[v12,v45,v85,v115,v138,v143,v185]) .nil .nil) (.node (6,[v12,v45,v85,v115,v138,v143,v211]) .nil .nil)) (.node (6,[v12,v45,v85,v115,v138,v143,v261]) (.node (6,[v12,v45,v85,v115,v138,v143,v243]) .nil .nil) (.node (6,[v12,v45,v85,v115,v138,v143,v263]) .nil .nil)))) (.node (6,[v12,v45,v85,v115,v143,v209]) (.node (6,[v12,v45,v85,v115,v138,v185]) (.node (6,[v12,v45,v85,v115,v138,v143,v294]) (.node (6,[v12,v45,v85,v115,v138,v143,v269]) .nil .nil) (.node (6,[v12,v45,v85,v115,v138,v143,v296]) .nil .nil)) (.node (6,[v12,v45,v85,v115,v143,v155]) (.node (6,[v12,v45,v85,v115,v138,v269]) .nil .nil) (.node (6,[v12,v45,v85,v115,v143,v172]) .nil .nil))) (.node (6,[v12,v45,v91,v172,v185,v241]) (.node (6,[v12,v45,v91,v138,v172,v185,v241]) (.node (6,[v12,v45,v85,v115,v143,v241]) .nil .nil) (.node (6,[v12,v45,v91,v143,v172,v185,v241]) .nil .nil)) (.node (6,[v12,v52,v66,v91,v138,v172,v185]) (.node (6,[v12,v52,v66,v85,v115,v138,v143]) .nil .nil) (.node (6,[v12,v52,v66,v91,v143,v172,v185]) .nil .nil)))))
noncomputable def block_120 : Tree := (.node (6,[v17,v20,v29,v45,v66,v138,v269]) (.node (6,[v13,v20,v45,v85,v91,v138,v143]) (.node (6,[v12,v66,v91,v172,v185,v209]) (.node (6,[v12,v66,v91,v138,v172,v185,v209]) (.node (6,[v12,v52,v85,v115,v138,v143]) (.node (6,[v12,v52,v85,v91,v115,v138,v143]) .nil .nil) .nil) (.node (6,[v12,v66,v91,v143,v172,v185,v209]) .nil .nil)) (.node (6,[v13,v20,v29,v66,v91,v143,v209]) (.node (6,[v13,v20,v29,v45,v66,v138,v269]) .nil .nil) (.node (6,[v13,v20,v45,v66,v91,v138,v185]) .nil .nil))) (.node (6,[v14,v20,v52,v85,v91,v138,v143]) (.node (6,[v14,v20,v29,v52,v66,v138,v269]) (.node (6,[v13,v29,v45,v66,v115,v138,v143]) .nil .nil) (.node (6,[v14,v20,v52,v66,v91,v138,v185]) .nil .nil)) (.node (6,[v15,v20,v52,v66,v91,v138,v185]) (.node (6,[v14,v29,v52,v66,v115,v138,v143]) .nil .nil) (.node (6,[v16,v20,v52,v85,v91,v138,v143]) .nil .nil)))) (.node (6,[v18,v20,v52,v66,v91,v138,v185]) (.node (6,[v17,v20,v45,v85,v91,v138,v143]) (.node (6,[v17,v20,v29,v66,v91,v143,v209]) (.node (6,[v17,v20,v29,v45,v91,v143,v241]) .nil .nil) (.node (6,[v17,v20,v45,v66,v91,v138,v185]) .nil .nil)) (.node (6,[v17,v29,v45,v66,v115,v138,v143]) (.node (6,[v17,v29,v45,v66,v91,v143,v172]) .nil .nil) (.node (6,[v18,v20,v29,v52,v66,v138,v269]) .nil .nil))) (.node (6,[v19,v29,v52,v66,v91,v138,v143]) (.node (6,[v18,v29,v52,v66,v115,v138,v143]) (.node (6,[v18,v20,v52,v85,v91,v138,v143]) .nil .nil) (.node (6,[v18,v36,v52,v66,v91,v138,v143]) .nil .nil)) (.node (6,[v20,v26,v29,v45,v91,v143,v241]) (.node (6,[v20,v26,v29,v45,v66,v138,v269]) .nil .nil) (.node (6,[v20,v26,v29,v66,v91,v143,v209]) .nil .nil)))))
noncomputable def stem_115 : Tree := .node (6,[v12,v52,v66,v91,v172,v185]) block_119 block_120
noncomputable def stem_116 : Tree := .node (6,[v12,v45,v85,v115,v130,v138,v143]) stem_114 stem_115
noncomputable def stem_117 : Tree := .node (6,[v12,v45,v66,v91,v172,v174,v185]) stem_112 stem_116
noncomputable def block_121 : Tree := (.node (6,[v20,v29,v39,v52,v66,v138,v269]) (.node (6,[v20,v27,v52,v85,v91,v138,v143]) (.node (6,[v20,v27,v29,v52,v91,v143,v241]) (.node (6,[v20,v27,v29,v52,v66,v138,v269]) (.node (6,[v20,v26,v45,v85,v91,v138,v143]) .nil .nil) .nil) (.node (6,[v20,v27,v52,v66,v91,v138,v185]) .nil .nil)) (.node (6,[v20,v29,v36,v52,v66,v138,v269]) (.node (6,[v20,v28,v52,v66,v91,v138,v143]) .nil .nil) (.node (6,[v20,v29,v39,v45,v66,v155,v269]) .nil .nil))) (.node (6,[v20,v29,v41,v52,v66,v138,v269]) (.node (6,[v20,v29,v39,v66,v91,v143,v219]) (.node (6,[v20,v29,v39,v52,v91,v143,v241]) .nil .nil) (.node (6,[v20,v29,v40,v52,v66,v138,v269]) .nil .nil)) (.node (6,[v20,v29,v43,v45,v91,v143,v241]) (.node (6,[v20,v29,v43,v45,v66,v138,v269]) .nil .nil) (.node (6,[v20,v29,v43,v66,v91,v143,v209]) .nil .nil))))
noncomputable def block_122 : Tree := (.node (6,[v20,v29,v45,v66,v91,v142,v152]) (.node (6,[v20,v29,v45,v52,v66,v219,v269]) (.node (6,[v20,v29,v45,v52,v66,v155,v269]) (.node (6,[v20,v29,v45,v52,v66,v138,v269]) (.node (6,[v20,v29,v45,v52,v66,v134,v269]) .nil .nil) .nil) (.node (6,[v20,v29,v45,v52,v66,v209,v269]) .nil .nil)) (.node (6,[v20,v29,v45,v52,v91,v143,v237]) (.node (6,[v20,v29,v45,v52,v66,v241,v269]) .nil .nil) (.node (6,[v20,v29,v45,v66,v72,v138,v269]) .nil .nil))) (.node (6,[v20,v29,v45,v66,v91,v143,v217]) (.node (6,[v20,v29,v45,v66,v91,v143,v152]) (.node (6,[v20,v29,v45,v66,v91,v142,v153]) .nil .nil) (.node (6,[v20,v29,v45,v66,v91,v143,v154]) .nil .nil)) (.node (6,[v20,v29,v45,v66,v91,v147,v152]) (.node (6,[v20,v29,v45,v66,v91,v146,v153]) .nil .nil) (.node (6,[v20,v29,v45,v66,v91,v152,v174]) .nil .nil))))
noncomputable def stem_118 : Tree := .node (6,[v20,v29,v45,v52,v66,v91,v142]) block_121 block_122
noncomputable def block_123 : Tree := (.node (6,[v20,v29,v45,v85,v91,v143,v152]) (.node (6,[v20,v29,v45,v66,v152,v269]) (.node (6,[v20,v29,v45,v66,v134,v152,v269]) (.node (6,[v20,v29,v45,v66,v101,v155,v269]) (.node (6,[v20,v29,v45,v66,v91,v152,v269]) (.node (6,[v20,v29,v45,v66,v91,v152,v243]) .nil .nil) .nil) (.node (6,[v20,v29,v45,v66,v115,v143,v152]) .nil .nil)) (.node (6,[v20,v29,v45,v66,v143,v152,v264]) (.node (6,[v20,v29,v45,v66,v138,v152,v269]) .nil .nil) (.node (6,[v20,v29,v45,v66,v143,v152,v269]) .nil .nil))) (.node (6,[v20,v29,v45,v72,v91,v143,v241]) (.node (6,[v20,v29,v45,v66,v155,v269,v279]) (.node (6,[v20,v29,v45,v66,v153,v155,v269]) .nil .nil) (.node (6,[v20,v29,v45,v70,v91,v138,v153]) .nil .nil)) (.node (6,[v20,v29,v45,v73,v91,v138,v149]) (.node (6,[v20,v29,v45,v72,v97,v138,v143]) .nil .nil) (.node (6,[v20,v29,v45,v73,v95,v138,v143]) .nil .nil)))) (.node (6,[v20,v29,v52,v63,v66,v138,v269]) (.node (6,[v20,v29,v52,v52,v66,v138,v269]) (.node (6,[v20,v29,v45,v91,v143,v152,v241]) (.node (6,[v20,v29,v45,v91,v143,v152,v237]) .nil .nil) (.node (6,[v20,v29,v51,v66,v91,v138,v143]) .nil .nil)) (.node (6,[v20,v29,v52,v60,v66,v138,v269]) (.node (6,[v20,v29,v52,v57,v66,v138,v269]) .nil .nil) (.node (6,[v20,v29,v52,v62,v66,v138,v269]) .nil .nil))) (.node (6,[v20,v29,v52,v66,v73,v138,v269]) (.node (6,[v20,v29,v52,v64,v97,v138,v143]) (.node (6,[v20,v29,v52,v64,v66,v138,v269]) .nil .nil) (.node (6,[v20,v29,v52,v65,v91,v138,v143]) .nil .nil)) (.node (6,[v20,v29,v52,v66,v85,v138,v269]) (.node (6,[v20,v29,v52,v66,v79,v138,v269]) .nil .nil) (.node (6,[v20,v29,v52,v66,v90,v138,v143]) .nil .nil)))))
noncomputable def stem_119 : Tree := .node (6,[v20,v29,v45,v66,v91,v152,v185]) stem_118 block_123
noncomputable def block_124 : Tree := (.node (6,[v20,v29,v52,v66,v91,v138,v143]) (.node (6,[v20,v29,v52,v66,v91,v135,v143]) (.node (6,[v20,v29,v52,v66,v91,v134,v243]) (.node (6,[v20,v29,v52,v66,v91,v134,v185]) (.node (6,[v20,v29,v52,v66,v91,v134,v174]) .nil .nil) .nil) (.node (6,[v20,v29,v52,v66,v91,v134,v269]) .nil .nil)) (.node (6,[v20,v29,v52,v66,v91,v137,v143]) (.node (6,[v20,v29,v52,v66,v91,v136,v143]) .nil .nil) (.node (6,[v20,v29,v52,v66,v91,v138,v142]) .nil .nil))) (.node (6,[v20,v29,v52,v66,v91,v138,v151]) (.node (6,[v20,v29,v52,v66,v91,v138,v145]) (.node (6,[v20,v29,v52,v66,v91,v138,v144]) .nil .nil) (.node (6,[v20,v29,v52,v66,v91,v138,v149]) .nil .nil)) (.node (6,[v20,v29,v52,v66,v91,v138,v166]) (.node (6,[v20,v29,v52,v66,v91,v138,v159]) .nil .nil) (.node (6,[v20,v29,v52,v66,v91,v138,v185]) .nil .nil))))
noncomputable def block_125 : Tree := (.node (6,[v20,v29,v52,v66,v91,v142,v155]) (.node (6,[v20,v29,v52,v66,v91,v140,v143]) (.node (6,[v20,v29,v52,v66,v91,v138,v297]) (.node (6,[v20,v29,v52,v66,v91,v138,v269]) (.node (6,[v20,v29,v52,v66,v91,v138,v235]) .nil .nil) .nil) (.node (6,[v20,v29,v52,v66,v91,v139,v143]) .nil .nil)) (.node (6,[v20,v29,v52,v66,v91,v142]) (.node (6,[v20,v29,v52,v66,v91,v141,v143]) .nil .nil) (.node (6,[v20,v29,v52,v66,v91,v142,v143]) .nil .nil))) (.node (6,[v20,v29,v52,v66,v91,v143,v150]) (.node (6,[v20,v29,v52,v66,v91,v143,v146]) (.node (6,[v20,v29,v52,v66,v91,v142,v219]) .nil .nil) (.node (6,[v20,v29,v52,v66,v91,v143,v148]) .nil .nil)) (.node (6,[v20,v29,v52,v66,v91,v143,v155]) (.node (6,[v20,v29,v52,v66,v91,v143,v152]) .nil .nil) (.node (6,[v20,v29,v52,v66,v91,v143,v157]) .nil .nil))))
noncomputable def stem_120 : Tree := .node (6,[v20,v29,v52,v66,v91,v138,v199]) block_124 block_125
noncomputable def block_126 : Tree := (.node (6,[v20,v29,v52,v66,v91,v143,v290]) (.node (6,[v20,v29,v52,v66,v91,v143,v229]) (.node (6,[v20,v29,v52,v66,v91,v143,v205]) (.node (6,[v20,v29,v52,v66,v91,v143,v179]) (.node (6,[v20,v29,v52,v66,v91,v143,v172]) (.node (6,[v20,v29,v52,v66,v91,v143,v168]) .nil .nil) .nil) (.node (6,[v20,v29,v52,v66,v91,v143,v197]) .nil .nil)) (.node (6,[v20,v29,v52,v66,v91,v143,v217]) (.node (6,[v20,v29,v52,v66,v91,v143,v209]) .nil .nil) (.node (6,[v20,v29,v52,v66,v91,v143,v219]) .nil .nil))) (.node (6,[v20,v29,v52,v66,v91,v143,v241]) (.node (6,[v20,v29,v52,v66,v91,v143,v234]) (.node (6,[v20,v29,v52,v66,v91,v143,v232]) .nil .nil) (.node (6,[v20,v29,v52,v66,v91,v143,v237]) .nil .nil)) (.node (6,[v20,v29,v52,v66,v91,v143,v257]) (.node (6,[v20,v29,v52,v66,v91,v143,v248]) .nil .nil) (.node (6,[v20,v29,v52,v66,v91,v143,v287]) .nil .nil)))) (.node (6,[v20,v29,v52,v66,v91,v241,v269]) (.node (6,[v20,v29,v52,v66,v91,v185,v209]) (.node (6,[v20,v29,v52,v66,v91,v155,v269]) (.node (6,[v20,v29,v52,v66,v91,v155,v185]) .nil .nil) (.node (6,[v20,v29,v52,v66,v91,v172,v185]) .nil .nil)) (.node (6,[v20,v29,v52,v66,v91,v209,v269]) (.node (6,[v20,v29,v52,v66,v91,v185,v219]) .nil .nil) (.node (6,[v20,v29,v52,v66,v91,v219,v269]) .nil .nil))) (.node (6,[v20,v29,v52,v66,v95,v138,v143]) (.node (6,[v20,v29,v52,v66,v93,v138,v143]) (.node (6,[v20,v29,v52,v66,v92,v138,v143]) .nil .nil) (.node (6,[v20,v29,v52,v66,v94,v138,v143]) .nil .nil)) (.node (6,[v20,v29,v52,v66,v99,v138,v143]) (.node (6,[v20,v29,v52,v66,v97,v138,v269]) .nil .nil) (.node (6,[v20,v29,v52,v66,v101,v138,v269]) .nil .nil)))))
noncomputable def stem_121 : Tree := .node (6,[v20,v29,v52,v66,v91,v143,v165]) stem_120 block_126
noncomputable def stem_122 : Tree := .node (6,[v20,v29,v52,v66,v91,v134,v143]) stem_119 stem_121
noncomputable def block_127 : Tree := (.node (6,[v20,v29,v52,v66,v115,v138,v269]) (.node (6,[v20,v29,v52,v66,v111,v138,v143]) (.node (6,[v20,v29,v52,v66,v109,v138,v269]) (.node (6,[v20,v29,v52,v66,v107,v138,v269]) (.node (6,[v20,v29,v52,v66,v104,v138,v269]) .nil .nil) .nil) (.node (6,[v20,v29,v52,v66,v110,v138,v269]) .nil .nil)) (.node (6,[v20,v29,v52,v66,v115,v138,v143]) (.node (6,[v20,v29,v52,v66,v115,v134,v143]) .nil .nil) (.node (6,[v20,v29,v52,v66,v115,v138,v185]) .nil .nil))) (.node (6,[v20,v29,v52,v66,v115,v143,v219]) (.node (6,[v20,v29,v52,v66,v115,v143,v172]) (.node (6,[v20,v29,v52,v66,v115,v143,v155]) .nil .nil) (.node (6,[v20,v29,v52,v66,v115,v143,v209]) .nil .nil)) (.node (6,[v20,v29,v52,v66,v120,v138,v269]) (.node (6,[v20,v29,v52,v66,v115,v143,v241]) .nil .nil) (.node (6,[v20,v29,v52,v66,v134,v138,v269]) .nil .nil))))
noncomputable def block_128 : Tree := (.node (6,[v20,v29,v52,v66,v138,v172,v269]) (.node (6,[v20,v29,v52,v66,v138,v143,v296]) (.node (6,[v20,v29,v52,v66,v138,v143,v264]) (.node (6,[v20,v29,v52,v66,v134,v269]) (.node (6,[v20,v29,v52,v66,v134,v143,v269]) .nil .nil) .nil) (.node (6,[v20,v29,v52,v66,v138,v143,v269]) .nil .nil)) (.node (6,[v20,v29,v52,v66,v138,v153,v269]) (.node (6,[v20,v29,v52,v66,v138,v147,v269]) .nil .nil) (.node (6,[v20,v29,v52,v66,v138,v155,v269]) .nil .nil))) (.node (6,[v20,v29,v52,v66,v138,v209,v269]) (.node (6,[v20,v29,v52,v66,v138,v181,v269]) (.node (6,[v20,v29,v52,v66,v138,v174,v269]) .nil .nil) (.node (6,[v20,v29,v52,v66,v138,v185,v269]) .nil .nil)) (.node (6,[v20,v29,v52,v66,v138,v218,v269]) (.node (6,[v20,v29,v52,v66,v138,v211,v269]) .nil .nil) (.node (6,[v20,v29,v52,v66,v138,v219,v269]) .nil .nil))))
noncomputable def stem_123 : Tree := .node (6,[v20,v29,v52,v66,v134,v143,v264]) block_127 block_128
noncomputable def block_129 : Tree := (.node (6,[v20,v29,v52,v66,v155,v269]) (.node (6,[v20,v29,v52,v66,v138,v269,v289]) (.node (6,[v20,v29,v52,v66,v138,v269,v270]) (.node (6,[v20,v29,v52,v66,v138,v269]) (.node (6,[v20,v29,v52,v66,v138,v265,v269]) (.node (6,[v20,v29,v52,v66,v138,v243,v269]) .nil .nil) .nil) (.node (6,[v20,v29,v52,v66,v138,v269,v269]) .nil .nil)) (.node (6,[v20,v29,v52,v66,v138,v269,v279]) (.node (6,[v20,v29,v52,v66,v138,v269,v276]) .nil .nil) (.node (6,[v20,v29,v52,v66,v138,v269,v285]) .nil .nil))) (.node (6,[v20,v29,v52,v66,v143,v172,v269]) (.node (6,[v20,v29,v52,v66,v138,v269,v297]) (.node (6,[v20,v29,v52,v66,v138,v269,v296]) .nil .nil) (.node (6,[v20,v29,v52,v66,v143,v155,v269]) .nil .nil)) (.node (6,[v20,v29,v52,v66,v143,v219,v269]) (.node (6,[v20,v29,v52,v66,v143,v209,v269]) .nil .nil) (.node (6,[v20,v29,v52,v66,v143,v241,v269]) .nil .nil)))) (.node (6,[v20,v29,v52,v73,v91,v143,v241]) (.node (6,[v20,v29,v52,v67,v91,v138,v143]) (.node (6,[v20,v29,v52,v66,v219,v269]) (.node (6,[v20,v29,v52,v66,v209,v269]) .nil .nil) (.node (6,[v20,v29,v52,v66,v241,v269]) .nil .nil)) (.node (6,[v20,v29,v52,v70,v91,v138,v143]) (.node (6,[v20,v29,v52,v69,v91,v138,v143]) .nil .nil) (.node (6,[v20,v29,v52,v71,v91,v138,v143]) .nil .nil))) (.node (6,[v20,v29,v52,v85,v91,v134,v143]) (.node (6,[v20,v29,v52,v77,v91,v138,v143]) (.node (6,[v20,v29,v52,v74,v91,v138,v143]) .nil .nil) (.node (6,[v20,v29,v52,v79,v91,v143,v241]) .nil .nil)) (.node (6,[v20,v29,v52,v85,v91,v138,v185]) (.node (6,[v20,v29,v52,v85,v91,v138,v143]) .nil .nil) (.node (6,[v20,v29,v52,v85,v91,v138,v269]) .nil .nil)))))
noncomputable def stem_124 : Tree := .node (6,[v20,v29,v52,v66,v138,v241,v269]) stem_123 block_129
noncomputable def block_130 : Tree := (.node (6,[v20,v29,v66,v91,v101,v143,v219]) (.node (6,[v20,v29,v52,v91,v134,v143,v237]) (.node (6,[v20,v29,v52,v85,v115,v138,v143]) (.node (6,[v20,v29,v52,v85,v91,v143,v219]) (.node (6,[v20,v29,v52,v85,v91,v143,v209]) (.node (6,[v20,v29,v52,v85,v91,v143,v172]) .nil .nil) .nil) (.node (6,[v20,v29,v52,v85,v91,v143,v241]) .nil .nil)) (.node (6,[v20,v29,v52,v91,v97,v143,v241]) (.node (6,[v20,v29,v52,v91,v96,v138,v143]) .nil .nil) (.node (6,[v20,v29,v52,v91,v101,v143,v241]) .nil .nil))) (.node (6,[v20,v29,v52,v91,v143,v241,v243]) (.node (6,[v20,v29,v52,v91,v143,v153,v241]) (.node (6,[v20,v29,v52,v91,v138,v143,v237]) .nil .nil) (.node (6,[v20,v29,v52,v91,v143,v237]) .nil .nil)) (.node (6,[v20,v29,v62,v66,v91,v143,v219]) (.node (6,[v20,v29,v61,v66,v91,v138,v143]) .nil .nil) (.node (6,[v20,v29,v66,v72,v91,v143,v209]) .nil .nil)))) (.node (6,[v20,v29,v66,v91,v143,v153,v219]) (.node (6,[v20,v29,v66,v91,v138,v143,v217]) (.node (6,[v20,v29,v66,v91,v109,v143,v219]) (.node (6,[v20,v29,v66,v91,v108,v138,v143]) .nil .nil) (.node (6,[v20,v29,v66,v91,v134,v143,v217]) .nil .nil)) (.node (6,[v20,v29,v66,v91,v143,v152,v209]) (.node (6,[v20,v29,v66,v91,v143,v152,v205]) .nil .nil) (.node (6,[v20,v29,v66,v91,v143,v152,v217]) .nil .nil))) (.node (6,[v20,v30,v52,v66,v91,v138,v143]) (.node (6,[v20,v29,v66,v91,v143,v217]) (.node (6,[v20,v29,v66,v91,v143,v205,v217]) .nil .nil) (.node (6,[v20,v29,v66,v91,v143,v218,v219]) .nil .nil)) (.node (6,[v20,v32,v52,v66,v91,v138,v143]) (.node (6,[v20,v31,v52,v66,v91,v138,v143]) .nil .nil) (.node (6,[v20,v33,v52,v66,v91,v138,v143]) .nil .nil)))))
noncomputable def block_131 : Tree := (.node (6,[v20,v45,v52,v66,v91,v185,v219]) (.node (6,[v20,v43,v45,v66,v91,v138,v185]) (.node (6,[v20,v39,v52,v66,v91,v138,v185]) (.node (6,[v20,v39,v45,v66,v91,v155,v185]) (.node (6,[v20,v36,v52,v85,v91,v138,v143]) (.node (6,[v20,v36,v52,v66,v91,v138,v185]) .nil .nil) .nil) (.node (6,[v20,v39,v45,v85,v91,v143,v155]) .nil .nil)) (.node (6,[v20,v40,v52,v66,v91,v138,v185]) (.node (6,[v20,v39,v52,v85,v91,v138,v143]) .nil .nil) (.node (6,[v20,v40,v52,v85,v91,v138,v143]) .nil .nil))) (.node (6,[v20,v45,v52,v66,v91,v138,v185]) (.node (6,[v20,v45,v52,v66,v85,v138,v269]) (.node (6,[v20,v43,v45,v85,v91,v138,v143]) .nil .nil) (.node (6,[v20,v45,v52,v66,v91,v134,v185]) .nil .nil)) (.node (6,[v20,v45,v52,v66,v91,v172,v185]) (.node (6,[v20,v45,v52,v66,v91,v155,v185]) .nil .nil) (.node (6,[v20,v45,v52,v66,v91,v185,v209]) .nil .nil)))) (.node (6,[v20,v45,v52,v85,v91,v143,v172]) (.node (6,[v20,v45,v52,v85,v91,v138,v143]) (.node (6,[v20,v45,v52,v66,v138,v185,v269]) (.node (6,[v20,v45,v52,v66,v115,v138,v185]) .nil .nil) (.node (6,[v20,v45,v52,v85,v91,v134,v143]) .nil .nil)) (.node (6,[v20,v45,v52,v85,v91,v138,v269]) (.node (6,[v20,v45,v52,v85,v91,v138,v185]) .nil .nil) (.node (6,[v20,v45,v52,v85,v91,v143,v155]) .nil .nil))) (.node (6,[v20,v45,v52,v85,v115,v138,v143]) (.node (6,[v20,v45,v52,v85,v91,v143,v219]) (.node (6,[v20,v45,v52,v85,v91,v143,v209]) .nil .nil) (.node (6,[v20,v45,v52,v85,v91,v143,v241]) .nil .nil)) (.node (6,[v20,v45,v66,v85,v91,v143,v152]) (.node (6,[v20,v45,v66,v72,v91,v138,v185]) .nil .nil) (.node (6,[v20,v45,v66,v91,v101,v155,v185]) .nil .nil)))))
noncomputable def stem_125 : Tree := .node (6,[v20,v34,v52,v66,v91,v138,v143]) block_130 block_131
noncomputable def stem_126 : Tree := .node (6,[v20,v29,v52,v85,v91,v143,v155]) stem_124 stem_125
noncomputable def stem_127 : Tree := .node (6,[v20,v29,v52,v66,v102,v138,v143]) stem_122 stem_126
noncomputable def stem_128 : Tree := .node (6,[v20,v26,v45,v66,v91,v138,v185]) stem_117 stem_127
noncomputable def stem_129 : Tree := .node (6,[v12,v29,v49,v66,v115,v138,v143]) stem_107 stem_128
noncomputable def block_132 : Tree := (.node (6,[v20,v45,v85,v91,v134,v143,v152]) (.node (6,[v20,v45,v66,v91,v153,v155,v185]) (.node (6,[v20,v45,v66,v91,v143,v152,v185]) (.node (6,[v20,v45,v66,v91,v143,v152,v180]) (.node (6,[v20,v45,v66,v91,v138,v152,v185]) .nil .nil) .nil) (.node (6,[v20,v45,v66,v91,v152,v185]) .nil .nil)) (.node (6,[v20,v45,v72,v85,v91,v138,v143]) (.node (6,[v20,v45,v66,v91,v155,v185,v195]) .nil .nil) (.node (6,[v20,v45,v85,v91,v101,v143,v155]) .nil .nil))) (.node (6,[v20,v52,v52,v66,v91,v138,v185]) (.node (6,[v20,v45,v85,v91,v143,v152]) (.node (6,[v20,v45,v85,v91,v138,v143,v152]) .nil .nil) (.node (6,[v20,v45,v85,v91,v143,v153,v155]) .nil .nil)) (.node (6,[v20,v52,v55,v66,v91,v138,v143]) (.node (6,[v20,v52,v52,v85,v91,v138,v143]) .nil .nil) (.node (6,[v20,v52,v57,v66,v91,v138,v185]) .nil .nil))))
noncomputable def block_133 : Tree := (.node (6,[v20,v52,v66,v73,v91,v138,v185]) (.node (6,[v20,v52,v63,v66,v91,v138,v185]) (.node (6,[v20,v52,v62,v66,v91,v138,v185]) (.node (6,[v20,v52,v60,v85,v91,v138,v143]) (.node (6,[v20,v52,v60,v66,v91,v138,v185]) .nil .nil) .nil) (.node (6,[v20,v52,v62,v85,v91,v138,v143]) .nil .nil)) (.node (6,[v20,v52,v64,v66,v91,v138,v185]) (.node (6,[v20,v52,v63,v85,v91,v138,v143]) .nil .nil) (.node (6,[v20,v52,v64,v85,v91,v138,v143]) .nil .nil))) (.node (6,[v20,v52,v66,v85,v91,v138,v143]) (.node (6,[v20,v52,v66,v81,v91,v138,v143]) (.node (6,[v20,v52,v66,v79,v91,v138,v185]) .nil .nil) (.node (6,[v20,v52,v66,v85,v91,v134,v143]) .nil .nil)) (.node (6,[v20,v52,v66,v85,v91,v138,v269]) (.node (6,[v20,v52,v66,v85,v91,v138,v185]) .nil .nil) (.node (6,[v20,v52,v66,v85,v91,v143,v155]) .nil .nil))))
noncomputable def stem_130 : Tree := .node (6,[v20,v52,v57,v85,v91,v138,v143]) block_132 block_133
noncomputable def block_134 : Tree := (.node (6,[v20,v52,v66,v91,v134,v143,v185]) (.node (6,[v20,v52,v66,v91,v104,v138,v185]) (.node (6,[v20,v52,v66,v85,v138,v143,v269]) (.node (6,[v20,v52,v66,v85,v91,v143,v241]) (.node (6,[v20,v52,v66,v85,v91,v143,v219]) (.node (6,[v20,v52,v66,v85,v91,v143,v209]) .nil .nil) .nil) (.node (6,[v20,v52,v66,v85,v115,v138,v143]) .nil .nil)) (.node (6,[v20,v52,v66,v91,v97,v138,v185]) (.node (6,[v20,v52,v66,v85,v138,v269]) .nil .nil) (.node (6,[v20,v52,v66,v91,v101,v138,v185]) .nil .nil))) (.node (6,[v20,v52,v66,v91,v115,v138,v185]) (.node (6,[v20,v52,v66,v91,v109,v138,v185]) (.node (6,[v20,v52,v66,v91,v107,v138,v185]) .nil .nil) (.node (6,[v20,v52,v66,v91,v110,v138,v185]) .nil .nil)) (.node (6,[v20,v52,v66,v91,v134,v138,v185]) (.node (6,[v20,v52,v66,v91,v120,v138,v185]) .nil .nil) (.node (6,[v20,v52,v66,v91,v134,v143,v180]) .nil .nil)))) (.node (6,[v20,v52,v66,v91,v138,v172,v185]) (.node (6,[v20,v52,v66,v91,v138,v143,v263]) (.node (6,[v20,v52,v66,v91,v138,v143,v180]) (.node (6,[v20,v52,v66,v91,v134,v185]) .nil .nil) (.node (6,[v20,v52,v66,v91,v138,v143,v185]) .nil .nil)) (.node (6,[v20,v52,v66,v91,v138,v153,v185]) (.node (6,[v20,v52,v66,v91,v138,v147,v185]) .nil .nil) (.node (6,[v20,v52,v66,v91,v138,v155,v185]) .nil .nil))) (.node (6,[v20,v52,v66,v91,v138,v185,v185]) (.node (6,[v20,v52,v66,v91,v138,v181,v185]) (.node (6,[v20,v52,v66,v91,v138,v174,v185]) .nil .nil) (.node (6,[v20,v52,v66,v91,v138,v185]) .nil .nil)) (.node (6,[v20,v52,v66,v91,v138,v185,v193]) (.node (6,[v20,v52,v66,v91,v138,v185,v186]) .nil .nil) (.node (6,[v20,v52,v66,v91,v138,v185,v195]) .nil .nil)))))
noncomputable def stem_131 : Tree := .node (6,[v20,v52,v66,v85,v91,v143,v172]) stem_130 block_134
noncomputable def block_135 : Tree := (.node (6,[v20,v52,v66,v91,v138,v185,v265]) (.node (6,[v20,v52,v66,v91,v138,v185,v231]) (.node (6,[v20,v52,v66,v91,v138,v185,v219]) (.node (6,[v20,v52,v66,v91,v138,v185,v218]) (.node (6,[v20,v52,v66,v91,v138,v185,v211]) .nil .nil) .nil) (.node (6,[v20,v52,v66,v91,v138,v185,v227]) .nil .nil)) (.node (6,[v20,v52,v66,v91,v138,v185,v243]) (.node (6,[v20,v52,v66,v91,v138,v185,v241]) .nil .nil) (.node (6,[v20,v52,v66,v91,v138,v185,v263]) .nil .nil))) (.node (6,[v20,v52,v66,v91,v143,v172,v185]) (.node (6,[v20,v52,v66,v91,v138,v185,v297]) (.node (6,[v20,v52,v66,v91,v138,v185,v269]) .nil .nil) (.node (6,[v20,v52,v66,v91,v143,v155,v185]) .nil .nil)) (.node (6,[v20,v52,v66,v91,v143,v185,v219]) (.node (6,[v20,v52,v66,v91,v143,v185,v209]) .nil .nil) (.node (6,[v20,v52,v66,v91,v143,v185,v241]) .nil .nil))))
noncomputable def block_136 : Tree := (.node (6,[v20,v52,v79,v85,v91,v138,v143]) (.node (6,[v20,v52,v66,v115,v138,v185]) (.node (6,[v20,v52,v66,v91,v185,v219]) (.node (6,[v20,v52,v66,v91,v185,v209]) (.node (6,[v20,v52,v66,v91,v172,v185]) .nil .nil) .nil) (.node (6,[v20,v52,v66,v115,v138,v143,v185]) .nil .nil)) (.node (6,[v20,v52,v66,v138,v185,v269]) (.node (6,[v20,v52,v66,v138,v143,v185,v269]) .nil .nil) (.node (6,[v20,v52,v73,v85,v91,v138,v143]) .nil .nil))) (.node (6,[v20,v52,v85,v91,v97,v138,v143]) (.node (6,[v20,v52,v85,v88,v91,v138,v143]) (.node (6,[v20,v52,v85,v85,v91,v138,v143]) .nil .nil) (.node (6,[v20,v52,v85,v89,v91,v138,v143]) .nil .nil)) (.node (6,[v20,v52,v85,v91,v104,v138,v143]) (.node (6,[v20,v52,v85,v91,v101,v138,v143]) .nil .nil) (.node (6,[v20,v52,v85,v91,v107,v138,v143]) .nil .nil))))
noncomputable def stem_132 : Tree := .node (6,[v20,v52,v66,v91,v155,v185]) block_135 block_136
noncomputable def block_137 : Tree := (.node (6,[v20,v52,v85,v91,v138,v143,v209]) (.node (6,[v20,v52,v85,v91,v138,v143]) (.node (6,[v20,v52,v85,v91,v124,v138,v143]) (.node (6,[v20,v52,v85,v91,v120,v138,v143]) (.node (6,[v20,v52,v85,v91,v115,v138,v143]) (.node (6,[v20,v52,v85,v91,v110,v138,v143]) .nil .nil) .nil) (.node (6,[v20,v52,v85,v91,v123,v138,v143]) .nil .nil)) (.node (6,[v20,v52,v85,v91,v134,v138,v143]) (.node (6,[v20,v52,v85,v91,v132,v138,v143]) .nil .nil) (.node (6,[v20,v52,v85,v91,v134,v143]) .nil .nil))) (.node (6,[v20,v52,v85,v91,v138,v143,v172]) (.node (6,[v20,v52,v85,v91,v138,v143,v153]) (.node (6,[v20,v52,v85,v91,v138,v143,v147]) .nil .nil) (.node (6,[v20,v52,v85,v91,v138,v143,v155]) .nil .nil)) (.node (6,[v20,v52,v85,v91,v138,v143,v181]) (.node (6,[v20,v52,v85,v91,v138,v143,v174]) .nil .nil) (.node (6,[v20,v52,v85,v91,v138,v143,v185]) .nil .nil)))) (.node (6,[v20,v52,v85,v91,v138,v143,v265]) (.node (6,[v20,v52,v85,v91,v138,v143,v241]) (.node (6,[v20,v52,v85,v91,v138,v143,v218]) (.node (6,[v20,v52,v85,v91,v138,v143,v211]) .nil .nil) (.node (6,[v20,v52,v85,v91,v138,v143,v219]) .nil .nil)) (.node (6,[v20,v52,v85,v91,v138,v143,v261]) (.node (6,[v20,v52,v85,v91,v138,v143,v243]) .nil .nil) (.node (6,[v20,v52,v85,v91,v138,v143,v263]) .nil .nil))) (.node (6,[v20,v52,v85,v91,v143,v155]) (.node (6,[v20,v52,v85,v91,v138,v185]) (.node (6,[v20,v52,v85,v91,v138,v143,v269]) .nil .nil) (.node (6,[v20,v52,v85,v91,v138,v269]) .nil .nil)) (.node (6,[v20,v52,v85,v91,v143,v209]) (.node (6,[v20,v52,v85,v91,v143,v172]) .nil .nil) (.node (6,[v20,v52,v85,v91,v143,v219]) .nil .nil)))))
noncomputable def stem_133 : Tree := .node (6,[v20,v52,v85,v91,v109,v138,v143]) stem_132 block_137
noncomputable def stem_134 : Tree := .node (6,[v20,v52,v66,v91,v138,v185,v209]) stem_131 stem_133
noncomputable def block_138 : Tree := (.node (6,[v26,v29,v45,v66,v115,v138,v143]) (.node (6,[v24,v29,v52,v66,v91,v138,v143]) (.node (6,[v23,v29,v52,v66,v91,v138,v143]) (.node (6,[v21,v29,v52,v66,v91,v138,v143]) (.node (6,[v20,v52,v85,v115,v138,v143]) .nil .nil) .nil) (.node (6,[v24,v29,v45,v66,v91,v138,v153]) .nil .nil)) (.node (6,[v25,v29,v52,v66,v91,v138,v143]) (.node (6,[v25,v29,v45,v73,v91,v138,v143]) .nil .nil) (.node (6,[v26,v29,v45,v66,v91,v143,v172]) .nil .nil))) (.node (6,[v27,v29,v52,v66,v91,v143,v172]) (.node (6,[v27,v29,v45,v66,v91,v138,v151]) (.node (6,[v26,v36,v45,v66,v91,v138,v143]) .nil .nil) (.node (6,[v27,v29,v45,v71,v91,v138,v143]) .nil .nil)) (.node (6,[v27,v34,v45,v66,v91,v138,v143]) (.node (6,[v27,v29,v52,v66,v115,v138,v143]) .nil .nil) (.node (6,[v29,v35,v52,v66,v91,v138,v143]) .nil .nil))))
noncomputable def block_139 : Tree := (.node (6,[v29,v45,v52,v66,v91,v143,v168]) (.node (6,[v29,v40,v52,v66,v115,v138,v143]) (.node (6,[v29,v39,v52,v66,v91,v143,v172]) (.node (6,[v29,v39,v45,v66,v115,v143,v155]) (.node (6,[v29,v36,v52,v66,v115,v138,v143]) .nil .nil) .nil) (.node (6,[v29,v39,v52,v66,v115,v138,v143]) .nil .nil)) (.node (6,[v29,v43,v45,v66,v91,v143,v172]) (.node (6,[v29,v42,v52,v66,v115,v138,v143]) .nil .nil) (.node (6,[v29,v43,v45,v66,v115,v138,v143]) .nil .nil))) (.node (6,[v29,v45,v52,v66,v115,v138,v269]) (.node (6,[v29,v45,v52,v66,v115,v138,v143]) (.node (6,[v29,v45,v52,v66,v115,v134,v143]) .nil .nil) (.node (6,[v29,v45,v52,v66,v115,v138,v185]) .nil .nil)) (.node (6,[v29,v45,v52,v66,v115,v143,v172]) (.node (6,[v29,v45,v52,v66,v115,v143,v155]) .nil .nil) (.node (6,[v29,v45,v52,v66,v115,v143,v209]) .nil .nil))))
noncomputable def stem_135 : Tree := .node (6,[v29,v36,v52,v66,v91,v143,v172]) block_138 block_139
noncomputable def block_140 : Tree := (.node (6,[v29,v52,v62,v66,v115,v138,v143]) (.node (6,[v29,v45,v66,v115,v134,v143,v152]) (.node (6,[v29,v45,v66,v91,v115,v143,v152]) (.node (6,[v29,v45,v66,v72,v91,v143,v172]) (.node (6,[v29,v45,v52,v85,v115,v138,v143]) (.node (6,[v29,v45,v52,v66,v115,v143,v241]) .nil .nil) .nil) (.node (6,[v29,v45,v66,v72,v115,v138,v143]) .nil .nil)) (.node (6,[v29,v45,v66,v91,v143,v152,v172]) (.node (6,[v29,v45,v66,v91,v143,v152,v168]) .nil .nil) (.node (6,[v29,v45,v66,v101,v115,v143,v155]) .nil .nil))) (.node (6,[v29,v52,v52,v66,v115,v138,v143]) (.node (6,[v29,v45,v66,v115,v143,v152]) (.node (6,[v29,v45,v66,v115,v138,v143,v152]) .nil .nil) (.node (6,[v29,v45,v66,v115,v143,v153,v155]) .nil .nil)) (.node (6,[v29,v52,v57,v66,v115,v138,v143]) (.node (6,[v29,v52,v53,v66,v91,v138,v143]) .nil .nil) (.node (6,[v29,v52,v60,v66,v115,v138,v143]) .nil .nil)))) (.node (6,[v29,v52,v66,v85,v115,v138,v143]) (.node (6,[v29,v52,v66,v73,v115,v138,v143]) (.node (6,[v29,v52,v64,v66,v115,v138,v143]) (.node (6,[v29,v52,v63,v66,v115,v138,v143]) .nil .nil) (.node (6,[v29,v52,v66,v73,v91,v143,v172]) .nil .nil)) (.node (6,[v29,v52,v66,v79,v91,v143,v172]) (.node (6,[v29,v52,v66,v78,v91,v138,v143]) .nil .nil) (.node (6,[v29,v52,v66,v79,v115,v138,v143]) .nil .nil))) (.node (6,[v29,v52,v66,v91,v115,v138,v185]) (.node (6,[v29,v52,v66,v91,v115,v134,v143]) (.node (6,[v29,v52,v66,v91,v101,v143,v172]) .nil .nil) (.node (6,[v29,v52,v66,v91,v115,v138,v143]) .nil .nil)) (.node (6,[v29,v52,v66,v91,v115,v143,v155]) (.node (6,[v29,v52,v66,v91,v115,v138,v269]) .nil .nil) (.node (6,[v29,v52,v66,v91,v115,v143,v172]) .nil .nil)))))
noncomputable def stem_136 : Tree := .node (6,[v29,v45,v52,v66,v115,v143,v219]) stem_135 block_140
noncomputable def block_141 : Tree := (.node (6,[v29,v52,v66,v115,v120,v138,v143]) (.node (6,[v29,v52,v66,v101,v115,v138,v143]) (.node (6,[v29,v52,v66,v91,v143,v153,v172]) (.node (6,[v29,v52,v66,v91,v134,v143,v168]) (.node (6,[v29,v52,v66,v91,v115,v143,v241]) (.node (6,[v29,v52,v66,v91,v115,v143,v219]) .nil .nil) .nil) (.node (6,[v29,v52,v66,v91,v138,v143,v168]) .nil .nil)) (.node (6,[v29,v52,v66,v91,v143,v172,v174]) (.node (6,[v29,v52,v66,v91,v143,v168]) .nil .nil) (.node (6,[v29,v52,v66,v97,v115,v138,v143]) .nil .nil))) (.node (6,[v29,v52,v66,v110,v115,v138,v143]) (.node (6,[v29,v52,v66,v107,v115,v138,v143]) (.node (6,[v29,v52,v66,v104,v115,v138,v143]) .nil .nil) (.node (6,[v29,v52,v66,v109,v115,v138,v143]) .nil .nil)) (.node (6,[v29,v52,v66,v115,v118,v138,v143]) (.node (6,[v29,v52,v66,v115,v115,v138,v143]) .nil .nil) (.node (6,[v29,v52,v66,v115,v119,v138,v143]) .nil .nil)))) (.node (6,[v29,v52,v66,v115,v138,v143,v153]) (.node (6,[v29,v52,v66,v115,v134,v138,v143]) (.node (6,[v29,v52,v66,v115,v127,v138,v143]) (.node (6,[v29,v52,v66,v115,v126,v138,v143]) .nil .nil) (.node (6,[v29,v52,v66,v115,v133,v138,v143]) .nil .nil)) (.node (6,[v29,v52,v66,v115,v138,v143]) (.node (6,[v29,v52,v66,v115,v134,v143]) .nil .nil) (.node (6,[v29,v52,v66,v115,v138,v143,v147]) .nil .nil))) (.node (6,[v29,v52,v66,v115,v138,v143,v181]) (.node (6,[v29,v52,v66,v115,v138,v143,v172]) (.node (6,[v29,v52,v66,v115,v138,v143,v155]) .nil .nil) (.node (6,[v29,v52,v66,v115,v138,v143,v174]) .nil .nil)) (.node (6,[v29,v52,v66,v115,v138,v143,v209]) (.node (6,[v29,v52,v66,v115,v138,v143,v185]) .nil .nil) (.node (6,[v29,v52,v66,v115,v138,v143,v211]) .nil .nil)))))
noncomputable def block_142 : Tree := (.node (6,[v45,v52,v66,v85,v115,v138,v143]) (.node (6,[v29,v52,v66,v115,v138,v269]) (.node (6,[v29,v52,v66,v115,v138,v143,v269]) (.node (6,[v29,v52,v66,v115,v138,v143,v243]) (.node (6,[v29,v52,v66,v115,v138,v143,v241]) (.node (6,[v29,v52,v66,v115,v138,v143,v219]) .nil .nil) .nil) (.node (6,[v29,v52,v66,v115,v138,v143,v265]) .nil .nil)) (.node (6,[v29,v52,v66,v115,v138,v143,v296]) (.node (6,[v29,v52,v66,v115,v138,v143,v294]) .nil .nil) (.node (6,[v29,v52,v66,v115,v138,v185]) .nil .nil))) (.node (6,[v29,v52,v66,v115,v143,v219]) (.node (6,[v29,v52,v66,v115,v143,v172]) (.node (6,[v29,v52,v66,v115,v143,v155]) .nil .nil) (.node (6,[v29,v52,v66,v115,v143,v209]) .nil .nil)) (.node (6,[v29,v52,v85,v91,v115,v138,v143]) (.node (6,[v29,v52,v66,v115,v143,v241]) .nil .nil) (.node (6,[v29,v52,v85,v115,v138,v143]) .nil .nil)))) (.node (7,[v0,v12,v20,v29,v45,v91,v143,v241]) (.node (6,[v52,v66,v85,v115,v138,v143]) (.node (6,[v45,v52,v85,v115,v138,v143]) (.node (6,[v45,v52,v85,v91,v115,v138,v143]) .nil .nil) (.node (6,[v52,v66,v85,v91,v115,v138,v143]) .nil .nil)) (.node (6,[v52,v85,v115,v138,v143]) (.node (6,[v52,v85,v91,v115,v138,v143]) .nil .nil) (.node (7,[v0,v12,v20,v29,v45,v66,v138,v269]) .nil .nil))) (.node (7,[v0,v12,v29,v45,v66,v91,v143,v172]) (.node (7,[v0,v12,v20,v45,v66,v91,v138,v185]) (.node (7,[v0,v12,v20,v29,v66,v91,v143,v209]) .nil .nil) (.node (7,[v0,v12,v20,v45,v85,v91,v138,v143]) .nil .nil)) (.node (7,[v0,v20,v29,v52,v66,v91,v138,v143]) (.node (7,[v0,v12,v29,v45,v66,v115,v138,v143]) .nil .nil) (.node (7,[v1,v12,v20,v29,v45,v66,v138,v269]) .nil .nil)))))
noncomputable def stem_137 : Tree := .node (6,[v29,v52,v66,v115,v138,v143,v218]) block_141 block_142
noncomputable def stem_138 : Tree := .node (6,[v29,v52,v66,v91,v115,v143,v209]) stem_136 stem_137
noncomputable def stem_139 : Tree := .node (6,[v20,v52,v85,v91,v143,v241]) stem_134 stem_138
noncomputable def block_143 : Tree := (.node (7,[v2,v12,v20,v29,v66,v91,v143,v209]) (.node (7,[v1,v12,v29,v45,v66,v115,v138,v143]) (.node (7,[v1,v12,v20,v45,v85,v91,v138,v143]) (.node (7,[v1,v12,v20,v45,v66,v91,v138,v185]) (.node (7,[v1,v12,v20,v29,v66,v91,v143,v209]) .nil .nil) .nil) (.node (7,[v1,v12,v29,v45,v66,v91,v143,v172]) .nil .nil)) (.node (7,[v2,v12,v20,v29,v45,v66,v138,v269]) (.node (7,[v1,v20,v29,v52,v66,v91,v138,v143]) .nil .nil) (.node (7,[v2,v12,v20,v29,v45,v91,v143,v241]) .nil .nil))) (.node (7,[v2,v12,v29,v45,v66,v115,v138,v143]) (.node (7,[v2,v12,v20,v45,v85,v91,v138,v143]) (.node (7,[v2,v12,v20,v45,v66,v91,v138,v185]) .nil .nil) (.node (7,[v2,v12,v29,v45,v66,v91,v143,v172]) .nil .nil)) (.node (7,[v3,v12,v20,v29,v45,v66,v138,v269]) (.node (7,[v2,v20,v29,v52,v66,v91,v138,v143]) .nil .nil) (.node (7,[v3,v12,v20,v29,v45,v91,v143,v241]) .nil .nil))))
noncomputable def block_144 : Tree := (.node (7,[v4,v12,v20,v45,v66,v91,v138,v185]) (.node (7,[v3,v20,v29,v52,v66,v91,v138,v143]) (.node (7,[v3,v12,v29,v45,v66,v91,v143,v172]) (.node (7,[v3,v12,v20,v45,v85,v91,v138,v143]) (.node (7,[v3,v12,v20,v45,v66,v91,v138,v185]) .nil .nil) .nil) (.node (7,[v3,v12,v29,v45,v66,v115,v138,v143]) .nil .nil)) (.node (7,[v4,v12,v20,v29,v45,v91,v143,v241]) (.node (7,[v4,v12,v20,v29,v45,v66,v138,v269]) .nil .nil) (.node (7,[v4,v12,v20,v29,v66,v91,v143,v209]) .nil .nil))) (.node (7,[v4,v20,v29,v52,v66,v91,v138,v143]) (.node (7,[v4,v12,v29,v45,v66,v91,v143,v172]) (.node (7,[v4,v12,v20,v45,v85,v91,v138,v143]) .nil .nil) (.node (7,[v4,v12,v29,v45,v66,v115,v138,v143]) .nil .nil)) (.node (7,[v5,v12,v20,v29,v45,v91,v143,v241]) (.node (7,[v5,v12,v20,v29,v45,v66,v138,v269]) .nil .nil) (.node (7,[v5,v12,v20,v29,v66,v91,v143,v209]) .nil .nil))))
noncomputable def stem_140 : Tree := .node (7,[v3,v12,v20,v29,v66,v91,v143,v209]) block_143 block_144
noncomputable def block_145 : Tree := (.node (7,[v7,v12,v20,v45,v85,v91,v138,v143]) (.node (7,[v6,v12,v20,v45,v85,v91,v138,v143]) (.node (7,[v6,v12,v20,v29,v45,v66,v138,v269]) (.node (7,[v5,v12,v29,v45,v66,v115,v138,v143]) (.node (7,[v5,v12,v29,v45,v66,v91,v143,v172]) (.node (7,[v5,v12,v20,v45,v85,v91,v138,v143]) .nil .nil) .nil) (.node (7,[v5,v20,v29,v52,v66,v91,v138,v143]) .nil .nil)) (.node (7,[v6,v12,v20,v29,v66,v91,v143,v209]) (.node (7,[v6,v12,v20,v29,v45,v91,v143,v241]) .nil .nil) (.node (7,[v6,v12,v20,v45,v66,v91,v138,v185]) .nil .nil))) (.node (7,[v7,v12,v20,v29,v45,v66,v138,v269]) (.node (7,[v6,v12,v29,v45,v66,v115,v138,v143]) (.node (7,[v6,v12,v29,v45,v66,v91,v143,v172]) .nil .nil) (.node (7,[v6,v20,v29,v52,v66,v91,v138,v143]) .nil .nil)) (.node (7,[v7,v12,v20,v29,v66,v91,v143,v209]) (.node (7,[v7,v12,v20,v29,v45,v91,v143,v241]) .nil .nil) (.node (7,[v7,v12,v20,v45,v66,v91,v138,v185]) .nil .nil)))) (.node (7,[v8,v12,v20,v45,v85,v91,v138,v143]) (.node (7,[v8,v12,v20,v29,v45,v66,v138,v269]) (.node (7,[v7,v12,v29,v45,v66,v115,v138,v143]) (.node (7,[v7,v12,v29,v45,v66,v91,v143,v172]) .nil .nil) (.node (7,[v7,v20,v29,v52,v66,v91,v138,v143]) .nil .nil)) (.node (7,[v8,v12,v20,v29,v66,v91,v143,v209]) (.node (7,[v8,v12,v20,v29,v45,v91,v143,v241]) .nil .nil) (.node (7,[v8,v12,v20,v45,v66,v91,v138,v185]) .nil .nil))) (.node (7,[v9,v12,v20,v29,v45,v66,v91,v134]) (.node (7,[v8,v12,v29,v45,v66,v115,v138,v143]) (.node (7,[v8,v12,v29,v45,v66,v91,v143,v172]) .nil .nil) (.node (7,[v8,v20,v29,v52,v66,v91,v138,v143]) .nil .nil)) (.node (7,[v9,v12,v20,v29,v45,v91,v143,v241]) (.node (7,[v9,v12,v20,v29,v45,v66,v138,v269]) .nil .nil) (.node (7,[v9,v12,v20,v29,v66,v91,v143,v209]) .nil .nil)))))
noncomputable def stem_141 : Tree := .node (7,[v5,v12,v20,v45,v66,v91,v138,v185]) stem_140 block_145
noncomputable def block_146 : Tree := (.node (7,[v10,v12,v20,v45,v66,v91,v138,v185]) (.node (7,[v9,v20,v29,v52,v66,v91,v138,v143]) (.node (7,[v9,v12,v29,v45,v66,v115,v138,v143]) (.node (7,[v9,v12,v29,v45,v66,v91,v143,v172]) (.node (7,[v9,v12,v20,v45,v85,v91,v138,v143]) .nil .nil) .nil) (.node (7,[v9,v20,v29,v45,v66,v91,v138,v153]) .nil .nil)) (.node (7,[v10,v12,v20,v29,v45,v91,v143,v241]) (.node (7,[v10,v12,v20,v29,v45,v66,v138,v269]) .nil .nil) (.node (7,[v10,v12,v20,v29,v66,v91,v143,v209]) .nil .nil))) (.node (7,[v10,v20,v29,v45,v73,v91,v138,v143]) (.node (7,[v10,v12,v29,v45,v66,v91,v143,v172]) (.node (7,[v10,v12,v20,v45,v85,v91,v138,v143]) .nil .nil) (.node (7,[v10,v12,v29,v45,v66,v115,v138,v143]) .nil .nil)) (.node (7,[v11,v12,v20,v29,v45,v66,v138,v269]) (.node (7,[v10,v20,v29,v52,v66,v91,v138,v143]) .nil .nil) (.node (7,[v11,v12,v20,v29,v45,v91,v143,v241]) .nil .nil))))
noncomputable def block_147 : Tree := (.node (7,[v12,v14,v20,v29,v66,v91,v143,v209]) (.node (7,[v11,v20,v29,v52,v66,v91,v138,v143]) (.node (7,[v11,v12,v29,v45,v66,v91,v143,v172]) (.node (7,[v11,v12,v20,v45,v85,v91,v138,v143]) (.node (7,[v11,v12,v20,v45,v66,v91,v138,v185]) .nil .nil) .nil) (.node (7,[v11,v12,v29,v45,v66,v115,v138,v143]) .nil .nil)) (.node (7,[v12,v14,v20,v29,v45,v66,v138,v269]) (.node (7,[v11,v27,v29,v45,v66,v91,v138,v143]) .nil .nil) (.node (7,[v12,v14,v20,v29,v45,v91,v143,v241]) .nil .nil))) (.node (7,[v12,v14,v29,v45,v66,v91,v143,v172]) (.node (7,[v12,v14,v20,v45,v85,v91,v138,v143]) (.node (7,[v12,v14,v20,v45,v66,v91,v138,v185]) .nil .nil) (.node (7,[v12,v14,v20,v57,v66,v91,v138,v143]) .nil .nil)) (.node (7,[v12,v18,v20,v29,v45,v66,v138,v269]) (.node (7,[v12,v14,v29,v45,v66,v115,v138,v143]) .nil .nil) (.node (7,[v12,v18,v20,v29,v45,v91,v143,v241]) .nil .nil))))
noncomputable def stem_142 : Tree := .node (7,[v11,v12,v20,v29,v66,v91,v143,v209]) block_146 block_147
noncomputable def block_148 : Tree := (.node (7,[v12,v20,v29,v39,v45,v91,v143,v241]) (.node (7,[v12,v20,v27,v29,v66,v91,v143,v209]) (.node (7,[v12,v18,v36,v45,v66,v91,v138,v143]) (.node (7,[v12,v18,v29,v45,v66,v91,v143,v172]) (.node (7,[v12,v18,v20,v45,v85,v91,v138,v143]) (.node (7,[v12,v18,v20,v45,v66,v91,v138,v185]) .nil .nil) .nil) (.node (7,[v12,v18,v29,v45,v66,v115,v138,v143]) .nil .nil)) (.node (7,[v12,v20,v27,v29,v45,v66,v138,v269]) (.node (7,[v12,v19,v29,v45,v66,v91,v138,v143]) .nil .nil) (.node (7,[v12,v20,v27,v29,v45,v91,v143,v241]) .nil .nil))) (.node (7,[v12,v20,v29,v36,v45,v66,v138,v269]) (.node (7,[v12,v20,v27,v45,v85,v91,v138,v143]) (.node (7,[v12,v20,v27,v45,v66,v91,v138,v185]) .nil .nil) (.node (7,[v12,v20,v28,v45,v66,v91,v138,v143]) .nil .nil)) (.node (7,[v12,v20,v29,v36,v66,v91,v143,v209]) (.node (7,[v12,v20,v29,v36,v45,v91,v143,v241]) .nil .nil) (.node (7,[v12,v20,v29,v39,v45,v66,v138,v269]) .nil .nil)))) (.node (7,[v12,v20,v29,v45,v52,v91,v143,v241]) (.node (7,[v12,v20,v29,v40,v66,v91,v143,v209]) (.node (7,[v12,v20,v29,v40,v45,v66,v138,v269]) (.node (7,[v12,v20,v29,v39,v66,v91,v143,v209]) .nil .nil) (.node (7,[v12,v20,v29,v40,v45,v91,v143,v241]) .nil .nil)) (.node (7,[v12,v20,v29,v44,v66,v91,v138,v143]) (.node (7,[v12,v20,v29,v40,v66,v104,v138,v143]) .nil .nil) (.node (7,[v12,v20,v29,v45,v52,v66,v138,v269]) .nil .nil))) (.node (7,[v12,v20,v29,v45,v60,v91,v143,v241]) (.node (7,[v12,v20,v29,v45,v57,v91,v143,v241]) (.node (7,[v12,v20,v29,v45,v57,v66,v138,v269]) .nil .nil) (.node (7,[v12,v20,v29,v45,v60,v66,v138,v269]) .nil .nil)) (.node (7,[v12,v20,v29,v45,v64,v91,v143,v241]) (.node (7,[v12,v20,v29,v45,v64,v66,v138,v269]) .nil .nil) (.node (7,[v12,v20,v29,v45,v64,v97,v138,v143]) .nil .nil)))))
noncomputable def stem_143 : Tree := .node (7,[v12,v18,v20,v29,v66,v91,v143,v209]) stem_142 block_148
noncomputable def stem_144 : Tree := .node (7,[v9,v12,v20,v45,v66,v91,v138,v185]) stem_141 stem_143
noncomputable def block_149 : Tree := (.node (7,[v12,v20,v29,v45,v66,v91,v134,v243]) (.node (7,[v12,v20,v29,v45,v66,v91,v134,v143]) (.node (7,[v12,v20,v29,v45,v66,v85,v138,v269]) (.node (7,[v12,v20,v29,v45,v66,v79,v138,v269]) (.node (7,[v12,v20,v29,v45,v66,v73,v138,v269]) .nil .nil) .nil) (.node (7,[v12,v20,v29,v45,v66,v90,v138,v143]) .nil .nil)) (.node (7,[v12,v20,v29,v45,v66,v91,v134,v174]) (.node (7,[v12,v20,v29,v45,v66,v91,v134,v147]) .nil .nil) (.node (7,[v12,v20,v29,v45,v66,v91,v134,v185]) .nil .nil))) (.node (7,[v12,v20,v29,v45,v66,v91,v137,v143]) (.node (7,[v12,v20,v29,v45,v66,v91,v135,v143]) (.node (7,[v12,v20,v29,v45,v66,v91,v134,v269]) .nil .nil) (.node (7,[v12,v20,v29,v45,v66,v91,v136,v143]) .nil .nil)) (.node (7,[v12,v20,v29,v45,v66,v91,v138,v143]) (.node (7,[v12,v20,v29,v45,v66,v91,v138,v142]) .nil .nil) (.node (7,[v12,v20,v29,v45,v66,v91,v138,v144]) .nil .nil))))
noncomputable def block_150 : Tree := (.node (7,[v12,v20,v29,v45,v66,v91,v138,v297]) (.node (7,[v12,v20,v29,v45,v66,v91,v138,v185]) (.node (7,[v12,v20,v29,v45,v66,v91,v138,v159]) (.node (7,[v12,v20,v29,v45,v66,v91,v138,v151]) (.node (7,[v12,v20,v29,v45,v66,v91,v138,v149]) .nil .nil) .nil) (.node (7,[v12,v20,v29,v45,v66,v91,v138,v166]) .nil .nil)) (.node (7,[v12,v20,v29,v45,v66,v91,v138,v235]) (.node (7,[v12,v20,v29,v45,v66,v91,v138,v199]) .nil .nil) (.node (7,[v12,v20,v29,v45,v66,v91,v138,v269]) .nil .nil))) (.node (7,[v12,v20,v29,v45,v66,v91,v142]) (.node (7,[v12,v20,v29,v45,v66,v91,v140,v143]) (.node (7,[v12,v20,v29,v45,v66,v91,v139,v143]) .nil .nil) (.node (7,[v12,v20,v29,v45,v66,v91,v141,v143]) .nil .nil)) (.node (7,[v12,v20,v29,v45,v66,v91,v142,v155]) (.node (7,[v12,v20,v29,v45,v66,v91,v142,v143]) .nil .nil) (.node (7,[v12,v20,v29,v45,v66,v91,v143,v146]) .nil .nil))))
noncomputable def stem_145 : Tree := .node (7,[v12,v20,v29,v45,v66,v91,v138,v145]) block_149 block_150
noncomputable def block_151 : Tree := (.node (7,[v12,v20,v29,v45,v66,v91,v143,v248]) (.node (7,[v12,v20,v29,v45,v66,v91,v143,v197]) (.node (7,[v12,v20,v29,v45,v66,v91,v143,v165]) (.node (7,[v12,v20,v29,v45,v66,v91,v143,v155]) (.node (7,[v12,v20,v29,v45,v66,v91,v143,v152]) (.node (7,[v12,v20,v29,v45,v66,v91,v143,v150]) .nil .nil) .nil) (.node (7,[v12,v20,v29,v45,v66,v91,v143,v157]) .nil .nil)) (.node (7,[v12,v20,v29,v45,v66,v91,v143,v172]) (.node (7,[v12,v20,v29,v45,v66,v91,v143,v168]) .nil .nil) (.node (7,[v12,v20,v29,v45,v66,v91,v143,v179]) .nil .nil))) (.node (7,[v12,v20,v29,v45,v66,v91,v143,v229]) (.node (7,[v12,v20,v29,v45,v66,v91,v143,v209]) (.node (7,[v12,v20,v29,v45,v66,v91,v143,v205]) .nil .nil) (.node (7,[v12,v20,v29,v45,v66,v91,v143,v219]) .nil .nil)) (.node (7,[v12,v20,v29,v45,v66,v91,v143,v237]) (.node (7,[v12,v20,v29,v45,v66,v91,v143,v234]) .nil .nil) (.node (7,[v12,v20,v29,v45,v66,v91,v143,v241]) .nil .nil)))) (.node (7,[v12,v20,v29,v45,v66,v91,v241,v269]) (.node (7,[v12,v20,v29,v45,v66,v91,v155,v269]) (.node (7,[v12,v20,v29,v45,v66,v91,v143,v287]) (.node (7,[v12,v20,v29,v45,v66,v91,v143,v257]) .nil .nil) (.node (7,[v12,v20,v29,v45,v66,v91,v155,v185]) .nil .nil)) (.node (7,[v12,v20,v29,v45,v66,v91,v185,v209]) (.node (7,[v12,v20,v29,v45,v66,v91,v172,v185]) .nil .nil) (.node (7,[v12,v20,v29,v45,v66,v91,v209,v269]) .nil .nil))) (.node (7,[v12,v20,v29,v45,v66,v95,v138,v143]) (.node (7,[v12,v20,v29,v45,v66,v93,v138,v143]) (.node (7,[v12,v20,v29,v45,v66,v92,v138,v143]) .nil .nil) (.node (7,[v12,v20,v29,v45,v66,v94,v138,v143]) .nil .nil)) (.node (7,[v12,v20,v29,v45,v66,v99,v138,v143]) (.node (7,[v12,v20,v29,v45,v66,v97,v138,v269]) .nil .nil) (.node (7,[v12,v20,v29,v45,v66,v101,v138,v269]) .nil .nil)))))
noncomputable def stem_146 : Tree := .node (7,[v12,v20,v29,v45,v66,v91,v143,v148]) stem_145 block_151
noncomputable def block_152 : Tree := (.node (7,[v12,v20,v29,v45,v66,v138,v143,v264]) (.node (7,[v12,v20,v29,v45,v66,v115,v143,v172]) (.node (7,[v12,v20,v29,v45,v66,v115,v138,v143]) (.node (7,[v12,v20,v29,v45,v66,v111,v138,v143]) (.node (7,[v12,v20,v29,v45,v66,v107,v138,v269]) (.node (7,[v12,v20,v29,v45,v66,v104,v138,v269]) .nil .nil) .nil) (.node (7,[v12,v20,v29,v45,v66,v115,v134,v143]) .nil .nil)) (.node (7,[v12,v20,v29,v45,v66,v115,v138,v269]) (.node (7,[v12,v20,v29,v45,v66,v115,v138,v185]) .nil .nil) (.node (7,[v12,v20,v29,v45,v66,v115,v143,v155]) .nil .nil))) (.node (7,[v12,v20,v29,v45,v66,v134,v138,v269]) (.node (7,[v12,v20,v29,v45,v66,v115,v143,v241]) (.node (7,[v12,v20,v29,v45,v66,v115,v143,v209]) .nil .nil) (.node (7,[v12,v20,v29,v45,v66,v120,v138,v269]) .nil .nil)) (.node (7,[v12,v20,v29,v45,v66,v134,v143,v269]) (.node (7,[v12,v20,v29,v45,v66,v134,v143,v264]) .nil .nil) (.node (7,[v12,v20,v29,v45,v66,v134,v269]) .nil .nil)))) (.node (7,[v12,v20,v29,v45,v66,v138,v181,v269]) (.node (7,[v12,v20,v29,v45,v66,v138,v153,v269]) (.node (7,[v12,v20,v29,v45,v66,v138,v143,v296]) (.node (7,[v12,v20,v29,v45,v66,v138,v143,v269]) .nil .nil) (.node (7,[v12,v20,v29,v45,v66,v138,v147,v269]) .nil .nil)) (.node (7,[v12,v20,v29,v45,v66,v138,v172,v269]) (.node (7,[v12,v20,v29,v45,v66,v138,v155,v269]) .nil .nil) (.node (7,[v12,v20,v29,v45,v66,v138,v174,v269]) .nil .nil))) (.node (7,[v12,v20,v29,v45,v66,v138,v241,v269]) (.node (7,[v12,v20,v29,v45,v66,v138,v209,v269]) (.node (7,[v12,v20,v29,v45,v66,v138,v185,v269]) .nil .nil) (.node (7,[v12,v20,v29,v45,v66,v138,v211,v269]) .nil .nil)) (.node (7,[v12,v20,v29,v45,v66,v138,v265,v269]) (.node (7,[v12,v20,v29,v45,v66,v138,v243,v269]) .nil .nil) (.node (7,[v12,v20,v29,v45,v66,v138,v269]) .nil .nil)))))
noncomputable def block_153 : Tree := (.node (7,[v12,v20,v29,v45,v70,v91,v138,v143]) (.node (7,[v12,v20,v29,v45,v66,v143,v209,v269]) (.node (7,[v12,v20,v29,v45,v66,v138,v269,v296]) (.node (7,[v12,v20,v29,v45,v66,v138,v269,v279]) (.node (7,[v12,v20,v29,v45,v66,v138,v269,v276]) (.node (7,[v12,v20,v29,v45,v66,v138,v269,v270]) .nil .nil) .nil) (.node (7,[v12,v20,v29,v45,v66,v138,v269,v285]) .nil .nil)) (.node (7,[v12,v20,v29,v45,v66,v143,v155,v269]) (.node (7,[v12,v20,v29,v45,v66,v138,v269,v297]) .nil .nil) (.node (7,[v12,v20,v29,v45,v66,v143,v172,v269]) .nil .nil))) (.node (7,[v12,v20,v29,v45,v66,v241,v269]) (.node (7,[v12,v20,v29,v45,v66,v155,v269]) (.node (7,[v12,v20,v29,v45,v66,v143,v241,v269]) .nil .nil) (.node (7,[v12,v20,v29,v45,v66,v209,v269]) .nil .nil)) (.node (7,[v12,v20,v29,v45,v68,v91,v138,v143]) (.node (7,[v12,v20,v29,v45,v67,v91,v138,v143]) .nil .nil) (.node (7,[v12,v20,v29,v45,v69,v91,v138,v143]) .nil .nil)))) (.node (7,[v12,v20,v29,v45,v85,v91,v138,v185]) (.node (7,[v12,v20,v29,v45,v77,v91,v138,v143]) (.node (7,[v12,v20,v29,v45,v73,v91,v143,v241]) (.node (7,[v12,v20,v29,v45,v71,v91,v138,v143]) .nil .nil) (.node (7,[v12,v20,v29,v45,v74,v91,v138,v143]) .nil .nil)) (.node (7,[v12,v20,v29,v45,v85,v91,v134,v143]) (.node (7,[v12,v20,v29,v45,v79,v91,v143,v241]) .nil .nil) (.node (7,[v12,v20,v29,v45,v85,v91,v138,v143]) .nil .nil))) (.node (7,[v12,v20,v29,v45,v85,v91,v143,v209]) (.node (7,[v12,v20,v29,v45,v85,v91,v143,v155]) (.node (7,[v12,v20,v29,v45,v85,v91,v138,v269]) .nil .nil) (.node (7,[v12,v20,v29,v45,v85,v91,v143,v172]) .nil .nil)) (.node (7,[v12,v20,v29,v45,v85,v115,v138,v143]) (.node (7,[v12,v20,v29,v45,v85,v91,v143,v241]) .nil .nil) (.node (7,[v12,v20,v29,v45,v91,v96,v138,v143]) .nil .nil)))))
noncomputable def stem_147 : Tree := .node (7,[v12,v20,v29,v45,v66,v138,v269,v269]) block_152 block_153
noncomputable def stem_148 : Tree := .node (7,[v12,v20,v29,v45,v66,v102,v138,v143]) stem_146 stem_147
noncomputable def stem_149 : Tree := .node (7,[v12,v20,v29,v45,v65,v91,v138,v143]) stem_144 stem_148
noncomputable def stem_150 : Tree := .node (7,[v1,v12,v20,v29,v45,v91,v143,v241]) stem_139 stem_149
noncomputable def block_154 : Tree := (.node (7,[v12,v20,v29,v45,v91,v138,v143,v241]) (.node (7,[v12,v20,v29,v45,v91,v120,v143,v241]) (.node (7,[v12,v20,v29,v45,v91,v107,v143,v241]) (.node (7,[v12,v20,v29,v45,v91,v104,v143,v241]) (.node (7,[v12,v20,v29,v45,v91,v101,v143,v241]) .nil .nil) .nil) (.node (7,[v12,v20,v29,v45,v91,v115,v143,v241]) .nil .nil)) (.node (7,[v12,v20,v29,v45,v91,v134,v143,v241]) (.node (7,[v12,v20,v29,v45,v91,v134,v143,v237]) .nil .nil) (.node (7,[v12,v20,v29,v45,v91,v138,v143,v237]) .nil .nil))) (.node (7,[v12,v20,v29,v45,v91,v143,v147,v241]) (.node (7,[v12,v20,v29,v45,v91,v138,v185,v241]) (.node (7,[v12,v20,v29,v45,v91,v138,v143,v261]) .nil .nil) (.node (7,[v12,v20,v29,v45,v91,v138,v241,v269]) .nil .nil)) (.node (7,[v12,v20,v29,v45,v91,v143,v155,v241]) (.node (7,[v12,v20,v29,v45,v91,v143,v153,v241]) .nil .nil) (.node (7,[v12,v20,v29,v45,v91,v143,v172,v241]) .nil .nil))))
noncomputable def block_155 : Tree := (.node (7,[v12,v20,v29,v45,v91,v143,v241,v245]) (.node (7,[v12,v20,v29,v45,v91,v143,v237]) (.node (7,[v12,v20,v29,v45,v91,v143,v209,v241]) (.node (7,[v12,v20,v29,v45,v91,v143,v185,v241]) (.node (7,[v12,v20,v29,v45,v91,v143,v181,v241]) .nil .nil) .nil) (.node (7,[v12,v20,v29,v45,v91,v143,v211,v241]) .nil .nil)) (.node (7,[v12,v20,v29,v45,v91,v143,v241,v241]) (.node (7,[v12,v20,v29,v45,v91,v143,v241]) .nil .nil) (.node (7,[v12,v20,v29,v45,v91,v143,v241,v243]) .nil .nil))) (.node (7,[v12,v20,v29,v45,v91,v143,v241,v265]) (.node (7,[v12,v20,v29,v45,v91,v143,v241,v257]) (.node (7,[v12,v20,v29,v45,v91,v143,v241,v248]) .nil .nil) (.node (7,[v12,v20,v29,v45,v91,v143,v241,v261]) .nil .nil)) (.node (7,[v12,v20,v29,v45,v91,v143,v241,v273]) (.node (7,[v12,v20,v29,v45,v91,v143,v241,v269]) .nil .nil) (.node (7,[v12,v20,v29,v45,v91,v143,v241,v287]) .nil .nil))))
noncomputable def stem_151 : Tree := .node (7,[v12,v20,v29,v45,v91,v143,v174,v241]) block_154 block_155
noncomputable def block_156 : Tree := (.node (7,[v12,v20,v29,v52,v66,v91,v143,v219]) (.node (7,[v12,v20,v29,v50,v66,v91,v138,v143]) (.node (7,[v12,v20,v29,v46,v66,v91,v138,v143]) (.node (7,[v12,v20,v29,v45,v143,v241,v269]) (.node (7,[v12,v20,v29,v45,v138,v241,v269]) (.node (7,[v12,v20,v29,v45,v138,v143,v241,v269]) .nil .nil) .nil) (.node (7,[v12,v20,v29,v45,v241,v269]) .nil .nil)) (.node (7,[v12,v20,v29,v48,v66,v91,v138,v143]) (.node (7,[v12,v20,v29,v47,v66,v91,v138,v143]) .nil .nil) (.node (7,[v12,v20,v29,v49,v66,v91,v138,v143]) .nil .nil))) (.node (7,[v12,v20,v29,v52,v66,v91,v138,v269]) (.node (7,[v12,v20,v29,v52,v66,v91,v138,v143]) (.node (7,[v12,v20,v29,v52,v66,v91,v134,v143]) .nil .nil) (.node (7,[v12,v20,v29,v52,v66,v91,v138,v185]) .nil .nil)) (.node (7,[v12,v20,v29,v52,v66,v91,v143,v172]) (.node (7,[v12,v20,v29,v52,v66,v91,v143,v155]) .nil .nil) (.node (7,[v12,v20,v29,v52,v66,v91,v143,v209]) .nil .nil)))) (.node (7,[v12,v20,v29,v56,v66,v91,v138,v143]) (.node (7,[v12,v20,v29,v52,v66,v138,v269]) (.node (7,[v12,v20,v29,v52,v66,v115,v138,v143]) (.node (7,[v12,v20,v29,v52,v66,v91,v143,v241]) .nil .nil) (.node (7,[v12,v20,v29,v52,v66,v138,v143,v269]) .nil .nil)) (.node (7,[v12,v20,v29,v52,v91,v138,v143,v241]) (.node (7,[v12,v20,v29,v52,v85,v91,v138,v143]) .nil .nil) (.node (7,[v12,v20,v29,v52,v91,v143,v241]) .nil .nil))) (.node (7,[v12,v20,v29,v66,v73,v91,v143,v209]) (.node (7,[v12,v20,v29,v60,v66,v91,v143,v209]) (.node (7,[v12,v20,v29,v57,v66,v91,v143,v209]) .nil .nil) (.node (7,[v12,v20,v29,v64,v66,v91,v143,v209]) .nil .nil)) (.node (7,[v12,v20,v29,v66,v85,v91,v143,v209]) (.node (7,[v12,v20,v29,v66,v79,v91,v143,v209]) .nil .nil) (.node (7,[v12,v20,v29,v66,v91,v97,v143,v209]) .nil .nil)))))
noncomputable def stem_152 : Tree := .node (7,[v12,v20,v29,v45,v91,v241,v269]) stem_151 block_156
noncomputable def block_157 : Tree := (.node (7,[v12,v20,v29,v66,v91,v138,v143,v209]) (.node (7,[v12,v20,v29,v66,v91,v120,v143,v209]) (.node (7,[v12,v20,v29,v66,v91,v107,v143,v209]) (.node (7,[v12,v20,v29,v66,v91,v104,v143,v209]) (.node (7,[v12,v20,v29,v66,v91,v103,v138,v143]) .nil .nil) .nil) (.node (7,[v12,v20,v29,v66,v91,v115,v143,v209]) .nil .nil)) (.node (7,[v12,v20,v29,v66,v91,v134,v143,v209]) (.node (7,[v12,v20,v29,v66,v91,v134,v143,v205]) .nil .nil) (.node (7,[v12,v20,v29,v66,v91,v138,v143,v205]) .nil .nil))) (.node (7,[v12,v20,v29,v66,v91,v143,v147,v209]) (.node (7,[v12,v20,v29,v66,v91,v138,v185,v209]) (.node (7,[v12,v20,v29,v66,v91,v138,v143,v219]) .nil .nil) (.node (7,[v12,v20,v29,v66,v91,v138,v209,v269]) .nil .nil)) (.node (7,[v12,v20,v29,v66,v91,v143,v155,v209]) (.node (7,[v12,v20,v29,v66,v91,v143,v153,v209]) .nil .nil) (.node (7,[v12,v20,v29,v66,v91,v143,v155,v219]) .nil .nil))))
noncomputable def block_158 : Tree := (.node (7,[v12,v20,v29,v66,v91,v143,v209,v219]) (.node (7,[v12,v20,v29,v66,v91,v143,v209]) (.node (7,[v12,v20,v29,v66,v91,v143,v185,v209]) (.node (7,[v12,v20,v29,v66,v91,v143,v181,v209]) (.node (7,[v12,v20,v29,v66,v91,v143,v174,v209]) .nil .nil) .nil) (.node (7,[v12,v20,v29,v66,v91,v143,v205]) .nil .nil)) (.node (7,[v12,v20,v29,v66,v91,v143,v209,v211]) (.node (7,[v12,v20,v29,v66,v91,v143,v209,v209]) .nil .nil) (.node (7,[v12,v20,v29,v66,v91,v143,v209,v213]) .nil .nil))) (.node (7,[v12,v20,v29,v66,v91,v143,v209,v243]) (.node (7,[v12,v20,v29,v66,v91,v143,v209,v229]) (.node (7,[v12,v20,v29,v66,v91,v143,v209,v225]) .nil .nil) (.node (7,[v12,v20,v29,v66,v91,v143,v209,v241]) .nil .nil)) (.node (7,[v12,v20,v29,v66,v91,v143,v209,v269]) (.node (7,[v12,v20,v29,v66,v91,v143,v209,v265]) .nil .nil) (.node (7,[v12,v20,v29,v66,v91,v143,v209,v283]) .nil .nil))))
noncomputable def stem_153 : Tree := .node (7,[v12,v20,v29,v66,v91,v143,v172,v209]) block_157 block_158
noncomputable def block_159 : Tree := (.node (7,[v12,v20,v36,v45,v66,v91,v138,v185]) (.node (7,[v12,v20,v29,v85,v91,v143,v209]) (.node (7,[v12,v20,v29,v66,v138,v209,v269]) (.node (7,[v12,v20,v29,v66,v91,v209,v269]) (.node (7,[v12,v20,v29,v66,v91,v185,v209]) (.node (7,[v12,v20,v29,v66,v91,v143,v219]) .nil .nil) .nil) (.node (7,[v12,v20,v29,v66,v138,v143,v209,v269]) .nil .nil)) (.node (7,[v12,v20,v29,v66,v209,v269]) (.node (7,[v12,v20,v29,v66,v143,v209,v269]) .nil .nil) (.node (7,[v12,v20,v29,v85,v91,v138,v143,v209]) .nil .nil))) (.node (7,[v12,v20,v31,v45,v66,v91,v138,v143]) (.node (7,[v12,v20,v29,v91,v143,v209,v241]) (.node (7,[v12,v20,v29,v91,v138,v143,v209,v241]) .nil .nil) (.node (7,[v12,v20,v30,v45,v66,v91,v138,v143]) .nil .nil)) (.node (7,[v12,v20,v33,v45,v66,v91,v138,v143]) (.node (7,[v12,v20,v32,v45,v66,v91,v138,v143]) .nil .nil) (.node (7,[v12,v20,v34,v45,v66,v91,v138,v143]) .nil .nil)))) (.node (7,[v12,v20,v45,v55,v66,v91,v138,v143]) (.node (7,[v12,v20,v40,v45,v66,v91,v138,v185]) (.node (7,[v12,v20,v39,v45,v66,v91,v138,v185]) (.node (7,[v12,v20,v36,v45,v85,v91,v138,v143]) .nil .nil) (.node (7,[v12,v20,v39,v45,v85,v91,v138,v143]) .nil .nil)) (.node (7,[v12,v20,v45,v52,v66,v91,v138,v185]) (.node (7,[v12,v20,v40,v45,v85,v91,v138,v143]) .nil .nil) (.node (7,[v12,v20,v45,v52,v85,v91,v138,v143]) .nil .nil))) (.node (7,[v12,v20,v45,v60,v85,v91,v138,v143]) (.node (7,[v12,v20,v45,v57,v85,v91,v138,v143]) (.node (7,[v12,v20,v45,v57,v66,v91,v138,v185]) .nil .nil) (.node (7,[v12,v20,v45,v60,v66,v91,v138,v185]) .nil .nil)) (.node (7,[v12,v20,v45,v64,v85,v91,v138,v143]) (.node (7,[v12,v20,v45,v64,v66,v91,v138,v185]) .nil .nil) (.node (7,[v12,v20,v45,v66,v73,v91,v138,v185]) .nil .nil)))))
noncomputable def stem_154 : Tree := .node (7,[v12,v20,v29,v66,v91,v143,v209,v287]) stem_153 block_159
noncomputable def stem_155 : Tree := .node (7,[v12,v20,v29,v66,v91,v101,v143,v209]) stem_152 stem_154
noncomputable def block_160 : Tree := (.node (7,[v12,v20,v45,v66,v85,v91,v143,v241]) (.node (7,[v12,v20,v45,v66,v85,v91,v138,v269]) (.node (7,[v12,v20,v45,v66,v85,v91,v138,v143]) (.node (7,[v12,v20,v45,v66,v85,v91,v134,v143]) (.node (7,[v12,v20,v45,v66,v81,v91,v138,v143]) .nil .nil) .nil) (.node (7,[v12,v20,v45,v66,v85,v91,v138,v185]) .nil .nil)) (.node (7,[v12,v20,v45,v66,v85,v91,v143,v172]) (.node (7,[v12,v20,v45,v66,v85,v91,v143,v155]) .nil .nil) (.node (7,[v12,v20,v45,v66,v85,v91,v143,v209]) .nil .nil))) (.node (7,[v12,v20,v45,v66,v91,v97,v138,v185]) (.node (7,[v12,v20,v45,v66,v85,v138,v143,v269]) (.node (7,[v12,v20,v45,v66,v85,v115,v138,v143]) .nil .nil) (.node (7,[v12,v20,v45,v66,v85,v138,v269]) .nil .nil)) (.node (7,[v12,v20,v45,v66,v91,v104,v138,v185]) (.node (7,[v12,v20,v45,v66,v91,v101,v138,v185]) .nil .nil) (.node (7,[v12,v20,v45,v66,v91,v107,v138,v185]) .nil .nil))))
noncomputable def block_161 : Tree := (.node (7,[v12,v20,v45,v66,v91,v138,v147,v185]) (.node (7,[v12,v20,v45,v66,v91,v134,v185]) (.node (7,[v12,v20,v45,v66,v91,v134,v143,v180]) (.node (7,[v12,v20,v45,v66,v91,v134,v138,v185]) (.node (7,[v12,v20,v45,v66,v91,v120,v138,v185]) .nil .nil) .nil) (.node (7,[v12,v20,v45,v66,v91,v134,v143,v185]) .nil .nil)) (.node (7,[v12,v20,v45,v66,v91,v138,v143,v185]) (.node (7,[v12,v20,v45,v66,v91,v138,v143,v180]) .nil .nil) (.node (7,[v12,v20,v45,v66,v91,v138,v143,v263]) .nil .nil))) (.node (7,[v12,v20,v45,v66,v91,v138,v174,v185]) (.node (7,[v12,v20,v45,v66,v91,v138,v155,v185]) (.node (7,[v12,v20,v45,v66,v91,v138,v153,v185]) .nil .nil) (.node (7,[v12,v20,v45,v66,v91,v138,v172,v185]) .nil .nil)) (.node (7,[v12,v20,v45,v66,v91,v138,v185]) (.node (7,[v12,v20,v45,v66,v91,v138,v181,v185]) .nil .nil) (.node (7,[v12,v20,v45,v66,v91,v138,v185,v185]) .nil .nil))))
noncomputable def stem_156 : Tree := .node (7,[v12,v20,v45,v66,v91,v115,v138,v185]) block_160 block_161
noncomputable def block_162 : Tree := (.node (7,[v12,v20,v45,v66,v91,v172,v185]) (.node (7,[v12,v20,v45,v66,v91,v138,v185,v265]) (.node (7,[v12,v20,v45,v66,v91,v138,v185,v227]) (.node (7,[v12,v20,v45,v66,v91,v138,v185,v209]) (.node (7,[v12,v20,v45,v66,v91,v138,v185,v195]) (.node (7,[v12,v20,v45,v66,v91,v138,v185,v193]) .nil .nil) .nil) (.node (7,[v12,v20,v45,v66,v91,v138,v185,v211]) .nil .nil)) (.node (7,[v12,v20,v45,v66,v91,v138,v185,v243]) (.node (7,[v12,v20,v45,v66,v91,v138,v185,v241]) .nil .nil) (.node (7,[v12,v20,v45,v66,v91,v138,v185,v263]) .nil .nil))) (.node (7,[v12,v20,v45,v66,v91,v143,v172,v185]) (.node (7,[v12,v20,v45,v66,v91,v138,v185,v297]) (.node (7,[v12,v20,v45,v66,v91,v138,v185,v269]) .nil .nil) (.node (7,[v12,v20,v45,v66,v91,v143,v155,v185]) .nil .nil)) (.node (7,[v12,v20,v45,v66,v91,v143,v185,v241]) (.node (7,[v12,v20,v45,v66,v91,v143,v185,v209]) .nil .nil) (.node (7,[v12,v20,v45,v66,v91,v155,v185]) .nil .nil)))) (.node (7,[v12,v20,v45,v85,v85,v91,v138,v143]) (.node (7,[v12,v20,v45,v66,v138,v143,v185,v269]) (.node (7,[v12,v20,v45,v66,v115,v138,v143,v185]) (.node (7,[v12,v20,v45,v66,v91,v185,v209]) .nil .nil) (.node (7,[v12,v20,v45,v66,v115,v138,v185]) .nil .nil)) (.node (7,[v12,v20,v45,v73,v85,v91,v138,v143]) (.node (7,[v12,v20,v45,v66,v138,v185,v269]) .nil .nil) (.node (7,[v12,v20,v45,v79,v85,v91,v138,v143]) .nil .nil))) (.node (7,[v12,v20,v45,v85,v91,v101,v138,v143]) (.node (7,[v12,v20,v45,v85,v89,v91,v138,v143]) (.node (7,[v12,v20,v45,v85,v88,v91,v138,v143]) .nil .nil) (.node (7,[v12,v20,v45,v85,v91,v97,v138,v143]) .nil .nil)) (.node (7,[v12,v20,v45,v85,v91,v107,v138,v143]) (.node (7,[v12,v20,v45,v85,v91,v104,v138,v143]) .nil .nil) (.node (7,[v12,v20,v45,v85,v91,v115,v138,v143]) .nil .nil)))))
noncomputable def stem_157 : Tree := .node (7,[v12,v20,v45,v66,v91,v138,v185,v186]) stem_156 block_162
noncomputable def block_163 : Tree := (.node (7,[v12,v20,v45,v85,v91,v138,v143,v261]) (.node (7,[v12,v20,v45,v85,v91,v138,v143,v172]) (.node (7,[v12,v20,v45,v85,v91,v138,v143]) (.node (7,[v12,v20,v45,v85,v91,v134,v138,v143]) (.node (7,[v12,v20,v45,v85,v91,v124,v138,v143]) (.node (7,[v12,v20,v45,v85,v91,v123,v138,v143]) .nil .nil) .nil) (.node (7,[v12,v20,v45,v85,v91,v134,v143]) .nil .nil)) (.node (7,[v12,v20,v45,v85,v91,v138,v143,v153]) (.node (7,[v12,v20,v45,v85,v91,v138,v143,v147]) .nil .nil) (.node (7,[v12,v20,v45,v85,v91,v138,v143,v155]) .nil .nil))) (.node (7,[v12,v20,v45,v85,v91,v138,v143,v209]) (.node (7,[v12,v20,v45,v85,v91,v138,v143,v181]) (.node (7,[v12,v20,v45,v85,v91,v138,v143,v174]) .nil .nil) (.node (7,[v12,v20,v45,v85,v91,v138,v143,v185]) .nil .nil)) (.node (7,[v12,v20,v45,v85,v91,v138,v143,v241]) (.node (7,[v12,v20,v45,v85,v91,v138,v143,v211]) .nil .nil) (.node (7,[v12,v20,v45,v85,v91,v138,v143,v243]) .nil .nil)))) (.node (7,[v12,v20,v45,v85,v91,v143,v209]) (.node (7,[v12,v20,v45,v85,v91,v138,v185]) (.node (7,[v12,v20,v45,v85,v91,v138,v143,v265]) (.node (7,[v12,v20,v45,v85,v91,v138,v143,v263]) .nil .nil) (.node (7,[v12,v20,v45,v85,v91,v138,v143,v269]) .nil .nil)) (.node (7,[v12,v20,v45,v85,v91,v143,v155]) (.node (7,[v12,v20,v45,v85,v91,v138,v269]) .nil .nil) (.node (7,[v12,v20,v45,v85,v91,v143,v172]) .nil .nil))) (.node (7,[v12,v20,v45,v91,v138,v185,v241]) (.node (7,[v12,v20,v45,v85,v115,v138,v143]) (.node (7,[v12,v20,v45,v85,v91,v143,v241]) .nil .nil) (.node (7,[v12,v20,v45,v91,v138,v143,v185,v241]) .nil .nil)) (.node (7,[v12,v20,v52,v66,v85,v91,v138,v143]) (.node (7,[v12,v20,v45,v91,v143,v185,v241]) .nil .nil) (.node (7,[v12,v20,v52,v66,v91,v138,v143,v185]) .nil .nil)))))
noncomputable def block_164 : Tree := (.node (7,[v12,v29,v39,v45,v66,v115,v138,v143]) (.node (7,[v12,v24,v29,v45,v66,v91,v138,v143]) (.node (7,[v12,v20,v66,v91,v185,v209]) (.node (7,[v12,v20,v66,v91,v138,v185,v209]) (.node (7,[v12,v20,v66,v91,v138,v143,v185,v209]) (.node (7,[v12,v20,v52,v85,v91,v138,v143]) .nil .nil) .nil) (.node (7,[v12,v20,v66,v91,v143,v185,v209]) .nil .nil)) (.node (7,[v12,v22,v29,v45,v66,v91,v138,v143]) (.node (7,[v12,v21,v29,v45,v66,v91,v138,v143]) .nil .nil) (.node (7,[v12,v23,v29,v45,v66,v91,v138,v143]) .nil .nil))) (.node (7,[v12,v29,v35,v45,v66,v91,v138,v143]) (.node (7,[v12,v27,v29,v45,v66,v91,v143,v172]) (.node (7,[v12,v25,v29,v45,v66,v91,v138,v143]) .nil .nil) (.node (7,[v12,v27,v29,v45,v66,v115,v138,v143]) .nil .nil)) (.node (7,[v12,v29,v36,v45,v66,v115,v138,v143]) (.node (7,[v12,v29,v36,v45,v66,v91,v143,v172]) .nil .nil) (.node (7,[v12,v29,v39,v45,v66,v91,v143,v172]) .nil .nil)))) (.node (7,[v12,v29,v45,v60,v66,v91,v143,v172]) (.node (7,[v12,v29,v45,v52,v66,v115,v138,v143]) (.node (7,[v12,v29,v40,v45,v66,v115,v138,v143]) (.node (7,[v12,v29,v40,v45,v66,v91,v143,v172]) .nil .nil) (.node (7,[v12,v29,v45,v52,v66,v91,v143,v172]) .nil .nil)) (.node (7,[v12,v29,v45,v57,v66,v91,v143,v172]) (.node (7,[v12,v29,v45,v53,v66,v91,v138,v143]) .nil .nil) (.node (7,[v12,v29,v45,v57,v66,v115,v138,v143]) .nil .nil))) (.node (7,[v12,v29,v45,v66,v73,v91,v143,v172]) (.node (7,[v12,v29,v45,v64,v66,v91,v143,v172]) (.node (7,[v12,v29,v45,v60,v66,v115,v138,v143]) .nil .nil) (.node (7,[v12,v29,v45,v64,v66,v115,v138,v143]) .nil .nil)) (.node (7,[v12,v29,v45,v66,v78,v91,v138,v143]) (.node (7,[v12,v29,v45,v66,v73,v115,v138,v143]) .nil .nil) (.node (7,[v12,v29,v45,v66,v79,v91,v143,v172]) .nil .nil)))))
noncomputable def stem_158 : Tree := .node (7,[v12,v20,v52,v66,v91,v138,v185]) block_163 block_164
noncomputable def stem_159 : Tree := .node (7,[v12,v20,v45,v85,v91,v120,v138,v143]) stem_157 stem_158
noncomputable def stem_160 : Tree := .node (7,[v12,v20,v45,v66,v79,v91,v138,v185]) stem_155 stem_159
noncomputable def block_165 : Tree := (.node (7,[v12,v29,v45,v66,v91,v115,v138,v185]) (.node (7,[v12,v29,v45,v66,v91,v104,v143,v172]) (.node (7,[v12,v29,v45,v66,v91,v97,v143,v172]) (.node (7,[v12,v29,v45,v66,v85,v115,v138,v143]) (.node (7,[v12,v29,v45,v66,v85,v91,v143,v172]) .nil .nil) .nil) (.node (7,[v12,v29,v45,v66,v91,v101,v143,v172]) .nil .nil)) (.node (7,[v12,v29,v45,v66,v91,v115,v134,v143]) (.node (7,[v12,v29,v45,v66,v91,v107,v143,v172]) .nil .nil) (.node (7,[v12,v29,v45,v66,v91,v115,v138,v143]) .nil .nil))) (.node (7,[v12,v29,v45,v66,v91,v115,v143,v209]) (.node (7,[v12,v29,v45,v66,v91,v115,v143,v155]) (.node (7,[v12,v29,v45,v66,v91,v115,v138,v269]) .nil .nil) (.node (7,[v12,v29,v45,v66,v91,v115,v143,v172]) .nil .nil)) (.node (7,[v12,v29,v45,v66,v91,v120,v143,v172]) (.node (7,[v12,v29,v45,v66,v91,v115,v143,v241]) .nil .nil) (.node (7,[v12,v29,v45,v66,v91,v134,v143,v168]) .nil .nil))))
noncomputable def block_166 : Tree := (.node (7,[v12,v29,v45,v66,v91,v143,v168]) (.node (7,[v12,v29,v45,v66,v91,v138,v172,v269]) (.node (7,[v12,v29,v45,v66,v91,v138,v143,v294]) (.node (7,[v12,v29,v45,v66,v91,v138,v143,v172]) (.node (7,[v12,v29,v45,v66,v91,v138,v143,v168]) .nil .nil) .nil) (.node (7,[v12,v29,v45,v66,v91,v138,v172,v185]) .nil .nil)) (.node (7,[v12,v29,v45,v66,v91,v143,v153,v172]) (.node (7,[v12,v29,v45,v66,v91,v143,v147,v172]) .nil .nil) (.node (7,[v12,v29,v45,v66,v91,v143,v155,v172]) .nil .nil))) (.node (7,[v12,v29,v45,v66,v91,v143,v172,v176]) (.node (7,[v12,v29,v45,v66,v91,v143,v172,v172]) (.node (7,[v12,v29,v45,v66,v91,v143,v172]) .nil .nil) (.node (7,[v12,v29,v45,v66,v91,v143,v172,v174]) .nil .nil)) (.node (7,[v12,v29,v45,v66,v91,v143,v172,v181]) (.node (7,[v12,v29,v45,v66,v91,v143,v172,v179]) .nil .nil) (.node (7,[v12,v29,v45,v66,v91,v143,v172,v185]) .nil .nil))))
noncomputable def stem_161 : Tree := .node (7,[v12,v29,v45,v66,v91,v134,v143,v172]) block_165 block_166
noncomputable def block_167 : Tree := (.node (7,[v12,v29,v45,v66,v115,v119,v138,v143]) (.node (7,[v12,v29,v45,v66,v91,v143,v172,v294]) (.node (7,[v12,v29,v45,v66,v91,v143,v172,v243]) (.node (7,[v12,v29,v45,v66,v91,v143,v172,v229]) (.node (7,[v12,v29,v45,v66,v91,v143,v172,v211]) (.node (7,[v12,v29,v45,v66,v91,v143,v172,v209]) .nil .nil) .nil) (.node (7,[v12,v29,v45,v66,v91,v143,v172,v241]) .nil .nil)) (.node (7,[v12,v29,v45,v66,v91,v143,v172,v265]) (.node (7,[v12,v29,v45,v66,v91,v143,v172,v257]) .nil .nil) (.node (7,[v12,v29,v45,v66,v91,v143,v172,v269]) .nil .nil))) (.node (7,[v12,v29,v45,v66,v104,v115,v138,v143]) (.node (7,[v12,v29,v45,v66,v97,v115,v138,v143]) (.node (7,[v12,v29,v45,v66,v91,v172,v185]) .nil .nil) (.node (7,[v12,v29,v45,v66,v101,v115,v138,v143]) .nil .nil)) (.node (7,[v12,v29,v45,v66,v115,v115,v138,v143]) (.node (7,[v12,v29,v45,v66,v107,v115,v138,v143]) .nil .nil) (.node (7,[v12,v29,v45,v66,v115,v118,v138,v143]) .nil .nil)))) (.node (7,[v12,v29,v45,v66,v115,v138,v143,v153]) (.node (7,[v12,v29,v45,v66,v115,v134,v138,v143]) (.node (7,[v12,v29,v45,v66,v115,v126,v138,v143]) (.node (7,[v12,v29,v45,v66,v115,v120,v138,v143]) .nil .nil) (.node (7,[v12,v29,v45,v66,v115,v127,v138,v143]) .nil .nil)) (.node (7,[v12,v29,v45,v66,v115,v138,v143]) (.node (7,[v12,v29,v45,v66,v115,v134,v143]) .nil .nil) (.node (7,[v12,v29,v45,v66,v115,v138,v143,v147]) .nil .nil))) (.node (7,[v12,v29,v45,v66,v115,v138,v143,v181]) (.node (7,[v12,v29,v45,v66,v115,v138,v143,v172]) (.node (7,[v12,v29,v45,v66,v115,v138,v143,v155]) .nil .nil) (.node (7,[v12,v29,v45,v66,v115,v138,v143,v174]) .nil .nil)) (.node (7,[v12,v29,v45,v66,v115,v138,v143,v209]) (.node (7,[v12,v29,v45,v66,v115,v138,v143,v185]) .nil .nil) (.node (7,[v12,v29,v45,v66,v115,v138,v143,v211]) .nil .nil)))))
noncomputable def stem_162 : Tree := .node (7,[v12,v29,v45,v66,v91,v143,v172,v190]) stem_161 block_167
noncomputable def block_168 : Tree := (.node (7,[v12,v29,v45,v85,v91,v143,v172]) (.node (7,[v12,v29,v45,v66,v115,v143,v172]) (.node (7,[v12,v29,v45,v66,v115,v138,v143,v296]) (.node (7,[v12,v29,v45,v66,v115,v138,v143,v269]) (.node (7,[v12,v29,v45,v66,v115,v138,v143,v265]) (.node (7,[v12,v29,v45,v66,v115,v138,v143,v243]) .nil .nil) .nil) (.node (7,[v12,v29,v45,v66,v115,v138,v143,v294]) .nil .nil)) (.node (7,[v12,v29,v45,v66,v115,v138,v269]) (.node (7,[v12,v29,v45,v66,v115,v138,v185]) .nil .nil) (.node (7,[v12,v29,v45,v66,v115,v143,v155]) .nil .nil))) (.node (7,[v12,v29,v45,v66,v138,v172,v269]) (.node (7,[v12,v29,v45,v66,v115,v143,v241]) (.node (7,[v12,v29,v45,v66,v115,v143,v209]) .nil .nil) (.node (7,[v12,v29,v45,v66,v138,v143,v172,v269]) .nil .nil)) (.node (7,[v12,v29,v45,v85,v91,v115,v138,v143]) (.node (7,[v12,v29,v45,v66,v143,v172,v269]) .nil .nil) (.node (7,[v12,v29,v45,v85,v91,v138,v143,v172]) .nil .nil)))) (.node (7,[v12,v29,v52,v66,v91,v143,v172]) (.node (7,[v12,v29,v45,v91,v138,v143,v172,v241]) (.node (7,[v12,v29,v45,v91,v115,v138,v143,v241]) (.node (7,[v12,v29,v45,v85,v115,v138,v143]) .nil .nil) (.node (7,[v12,v29,v45,v91,v115,v143,v241]) .nil .nil)) (.node (7,[v12,v29,v52,v66,v91,v115,v138,v143]) (.node (7,[v12,v29,v45,v91,v143,v172,v241]) .nil .nil) (.node (7,[v12,v29,v52,v66,v91,v138,v143,v172]) .nil .nil))) (.node (7,[v12,v29,v66,v91,v138,v143,v172,v209]) (.node (7,[v12,v29,v66,v91,v115,v138,v143,v209]) (.node (7,[v12,v29,v52,v66,v115,v138,v143]) .nil .nil) (.node (7,[v12,v29,v66,v91,v115,v143,v209]) .nil .nil)) (.node (7,[v12,v45,v66,v85,v91,v115,v138,v143]) (.node (7,[v12,v29,v66,v91,v143,v172,v209]) .nil .nil) (.node (7,[v12,v45,v66,v85,v115,v138,v143]) .nil .nil)))))
noncomputable def block_169 : Tree := (.node (7,[v20,v29,v45,v52,v66,v91,v134,v143]) (.node (7,[v18,v20,v29,v52,v66,v91,v138,v143]) (.node (7,[v12,v45,v85,v115,v138,v143]) (.node (7,[v12,v45,v66,v91,v172,v185]) (.node (7,[v12,v45,v66,v91,v143,v172,v185]) (.node (7,[v12,v45,v66,v91,v138,v172,v185]) .nil .nil) .nil) (.node (7,[v12,v45,v85,v91,v115,v138,v143]) .nil .nil)) (.node (7,[v14,v20,v29,v52,v66,v91,v138,v143]) (.node (7,[v13,v20,v29,v45,v66,v91,v138,v143]) .nil .nil) (.node (7,[v17,v20,v29,v45,v66,v91,v138,v143]) .nil .nil))) (.node (7,[v20,v29,v39,v45,v66,v91,v143,v155]) (.node (7,[v20,v27,v29,v52,v66,v91,v138,v143]) (.node (7,[v20,v26,v29,v45,v66,v91,v138,v143]) .nil .nil) (.node (7,[v20,v29,v36,v52,v66,v91,v138,v143]) .nil .nil)) (.node (7,[v20,v29,v40,v52,v66,v91,v138,v143]) (.node (7,[v20,v29,v39,v52,v66,v91,v138,v143]) .nil .nil) (.node (7,[v20,v29,v43,v45,v66,v91,v138,v143]) .nil .nil)))) (.node (7,[v20,v29,v45,v52,v66,v91,v143,v241]) (.node (7,[v20,v29,v45,v52,v66,v91,v143,v155]) (.node (7,[v20,v29,v45,v52,v66,v91,v138,v185]) (.node (7,[v20,v29,v45,v52,v66,v91,v138,v143]) .nil .nil) (.node (7,[v20,v29,v45,v52,v66,v91,v138,v269]) .nil .nil)) (.node (7,[v20,v29,v45,v52,v66,v91,v143,v209]) (.node (7,[v20,v29,v45,v52,v66,v91,v143,v172]) .nil .nil) (.node (7,[v20,v29,v45,v52,v66,v91,v143,v219]) .nil .nil))) (.node (7,[v20,v29,v45,v52,v85,v91,v138,v143]) (.node (7,[v20,v29,v45,v52,v66,v138,v143,v269]) (.node (7,[v20,v29,v45,v52,v66,v115,v138,v143]) .nil .nil) (.node (7,[v20,v29,v45,v52,v66,v138,v269]) .nil .nil)) (.node (7,[v20,v29,v45,v66,v91,v101,v143,v155]) (.node (7,[v20,v29,v45,v66,v72,v91,v138,v143]) .nil .nil) (.node (7,[v20,v29,v45,v66,v91,v134,v143,v152]) .nil .nil)))))
noncomputable def stem_163 : Tree := .node (7,[v12,v45,v66,v91,v138,v143,v172,v185]) block_168 block_169
noncomputable def stem_164 : Tree := .node (7,[v12,v29,v45,v66,v115,v138,v143,v241]) stem_162 stem_163
noncomputable def block_170 : Tree := (.node (7,[v20,v29,v52,v66,v73,v91,v138,v143]) (.node (7,[v20,v29,v52,v60,v66,v91,v138,v143]) (.node (7,[v20,v29,v52,v52,v66,v91,v138,v143]) (.node (7,[v20,v29,v45,v66,v91,v143,v153,v155]) (.node (7,[v20,v29,v45,v66,v91,v143,v152]) .nil .nil) .nil) (.node (7,[v20,v29,v52,v57,v66,v91,v138,v143]) .nil .nil)) (.node (7,[v20,v29,v52,v63,v66,v91,v138,v143]) (.node (7,[v20,v29,v52,v62,v66,v91,v138,v143]) .nil .nil) (.node (7,[v20,v29,v52,v64,v66,v91,v138,v143]) .nil .nil))) (.node (7,[v20,v29,v52,v66,v91,v101,v138,v143]) (.node (7,[v20,v29,v52,v66,v85,v91,v138,v143]) (.node (7,[v20,v29,v52,v66,v79,v91,v138,v143]) .nil .nil) (.node (7,[v20,v29,v52,v66,v91,v97,v138,v143]) .nil .nil)) (.node (7,[v20,v29,v52,v66,v91,v107,v138,v143]) (.node (7,[v20,v29,v52,v66,v91,v104,v138,v143]) .nil .nil) (.node (7,[v20,v29,v52,v66,v91,v109,v138,v143]) .nil .nil))))
noncomputable def block_171 : Tree := (.node (7,[v20,v29,v52,v66,v91,v138,v143,v172]) (.node (7,[v20,v29,v52,v66,v91,v138,v143]) (.node (7,[v20,v29,v52,v66,v91,v134,v138,v143]) (.node (7,[v20,v29,v52,v66,v91,v120,v138,v143]) (.node (7,[v20,v29,v52,v66,v91,v115,v138,v143]) .nil .nil) .nil) (.node (7,[v20,v29,v52,v66,v91,v134,v143]) .nil .nil)) (.node (7,[v20,v29,v52,v66,v91,v138,v143,v153]) (.node (7,[v20,v29,v52,v66,v91,v138,v143,v147]) .nil .nil) (.node (7,[v20,v29,v52,v66,v91,v138,v143,v155]) .nil .nil))) (.node (7,[v20,v29,v52,v66,v91,v138,v143,v209]) (.node (7,[v20,v29,v52,v66,v91,v138,v143,v181]) (.node (7,[v20,v29,v52,v66,v91,v138,v143,v174]) .nil .nil) (.node (7,[v20,v29,v52,v66,v91,v138,v143,v185]) .nil .nil)) (.node (7,[v20,v29,v52,v66,v91,v138,v143,v218]) (.node (7,[v20,v29,v52,v66,v91,v138,v143,v211]) .nil .nil) (.node (7,[v20,v29,v52,v66,v91,v138,v143,v219]) .nil .nil))))
noncomputable def stem_165 : Tree := .node (7,[v20,v29,v52,v66,v91,v110,v138,v143]) block_170 block_171
noncomputable def block_172 : Tree := (.node (7,[v20,v45,v52,v66,v91,v138,v185]) (.node (7,[v20,v29,v52,v66,v91,v143,v219]) (.node (7,[v20,v29,v52,v66,v91,v138,v269]) (.node (7,[v20,v29,v52,v66,v91,v138,v143,v269]) (.node (7,[v20,v29,v52,v66,v91,v138,v143,v265]) (.node (7,[v20,v29,v52,v66,v91,v138,v143,v243]) .nil .nil) .nil) (.node (7,[v20,v29,v52,v66,v91,v138,v185]) .nil .nil)) (.node (7,[v20,v29,v52,v66,v91,v143,v172]) (.node (7,[v20,v29,v52,v66,v91,v143,v155]) .nil .nil) (.node (7,[v20,v29,v52,v66,v91,v143,v209]) .nil .nil))) (.node (7,[v20,v29,v52,v66,v138,v269]) (.node (7,[v20,v29,v52,v66,v115,v138,v143]) (.node (7,[v20,v29,v52,v66,v91,v143,v241]) .nil .nil) (.node (7,[v20,v29,v52,v66,v138,v143,v269]) .nil .nil)) (.node (7,[v20,v45,v52,v66,v85,v91,v138,v143]) (.node (7,[v20,v29,v52,v85,v91,v138,v143]) .nil .nil) (.node (7,[v20,v45,v52,v66,v91,v138,v143,v185]) .nil .nil)))) (.node (7,[v29,v52,v66,v91,v115,v138,v143]) (.node (7,[v20,v52,v66,v91,v138,v185]) (.node (7,[v20,v52,v66,v85,v91,v138,v143]) (.node (7,[v20,v45,v52,v85,v91,v138,v143]) .nil .nil) (.node (7,[v20,v52,v66,v91,v138,v143,v185]) .nil .nil)) (.node (7,[v29,v45,v52,v66,v91,v115,v138,v143]) (.node (7,[v20,v52,v85,v91,v138,v143]) .nil .nil) (.node (7,[v29,v45,v52,v66,v115,v138,v143]) .nil .nil))) (.node (8,[v2,v12,v20,v29,v45,v66,v91,v138,v143]) (.node (8,[v0,v12,v20,v29,v45,v66,v91,v138,v143]) (.node (7,[v29,v52,v66,v115,v138,v143]) .nil .nil) (.node (8,[v1,v12,v20,v29,v45,v66,v91,v138,v143]) .nil .nil)) (.node (8,[v4,v12,v20,v29,v45,v66,v91,v138,v143]) (.node (8,[v3,v12,v20,v29,v45,v66,v91,v138,v143]) .nil .nil) (.node (8,[v5,v12,v20,v29,v45,v66,v91,v138,v143]) .nil .nil)))))
noncomputable def stem_166 : Tree := .node (7,[v20,v29,v52,v66,v91,v138,v143,v241]) stem_165 block_172
noncomputable def block_173 : Tree := (.node (8,[v12,v20,v29,v45,v66,v79,v91,v138,v143]) (.node (8,[v12,v20,v29,v36,v45,v66,v91,v138,v143]) (.node (8,[v11,v12,v20,v29,v45,v66,v91,v138,v143]) (.node (8,[v9,v12,v20,v29,v45,v66,v91,v138,v143]) (.node (8,[v8,v12,v20,v29,v45,v66,v91,v138,v143]) (.node (8,[v7,v12,v20,v29,v45,v66,v91,v138,v143]) .nil .nil) .nil) (.node (8,[v10,v12,v20,v29,v45,v66,v91,v138,v143]) .nil .nil)) (.node (8,[v12,v18,v20,v29,v45,v66,v91,v138,v143]) (.node (8,[v12,v14,v20,v29,v45,v66,v91,v138,v143]) .nil .nil) (.node (8,[v12,v20,v27,v29,v45,v66,v91,v138,v143]) .nil .nil))) (.node (8,[v12,v20,v29,v45,v57,v66,v91,v138,v143]) (.node (8,[v12,v20,v29,v40,v45,v66,v91,v138,v143]) (.node (8,[v12,v20,v29,v39,v45,v66,v91,v138,v143]) .nil .nil) (.node (8,[v12,v20,v29,v45,v52,v66,v91,v138,v143]) .nil .nil)) (.node (8,[v12,v20,v29,v45,v64,v66,v91,v138,v143]) (.node (8,[v12,v20,v29,v45,v60,v66,v91,v138,v143]) .nil .nil) (.node (8,[v12,v20,v29,v45,v66,v73,v91,v138,v143]) .nil .nil)))) (.node (8,[v12,v20,v29,v45,v66,v91,v134,v138,v143]) (.node (8,[v12,v20,v29,v45,v66,v91,v104,v138,v143]) (.node (8,[v12,v20,v29,v45,v66,v91,v97,v138,v143]) (.node (8,[v12,v20,v29,v45,v66,v85,v91,v138,v143]) .nil .nil) (.node (8,[v12,v20,v29,v45,v66,v91,v101,v138,v143]) .nil .nil)) (.node (8,[v12,v20,v29,v45,v66,v91,v115,v138,v143]) (.node (8,[v12,v20,v29,v45,v66,v91,v107,v138,v143]) .nil .nil) (.node (8,[v12,v20,v29,v45,v66,v91,v120,v138,v143]) .nil .nil))) (.node (8,[v12,v20,v29,v45,v66,v91,v138,v143,v155]) (.node (8,[v12,v20,v29,v45,v66,v91,v138,v143,v147]) (.node (8,[v12,v20,v29,v45,v66,v91,v134,v143]) .nil .nil) (.node (8,[v12,v20,v29,v45,v66,v91,v138,v143,v153]) .nil .nil)) (.node (8,[v12,v20,v29,v45,v66,v91,v138,v143,v174]) (.node (8,[v12,v20,v29,v45,v66,v91,v138,v143,v172]) .nil .nil) (.node (8,[v12,v20,v29,v45,v66,v91,v138,v143,v181]) .nil .nil)))))
noncomputable def block_174 : Tree := (.node (8,[v12,v20,v29,v45,v91,v138,v143,v241]) (.node (8,[v12,v20,v29,v45,v66,v91,v143,v155]) (.node (8,[v12,v20,v29,v45,v66,v91,v138,v143,v265]) (.node (8,[v12,v20,v29,v45,v66,v91,v138,v143,v241]) (.node (8,[v12,v20,v29,v45,v66,v91,v138,v143,v211]) (.node (8,[v12,v20,v29,v45,v66,v91,v138,v143,v209]) .nil .nil) .nil) (.node (8,[v12,v20,v29,v45,v66,v91,v138,v143,v243]) .nil .nil)) (.node (8,[v12,v20,v29,v45,v66,v91,v138,v185]) (.node (8,[v12,v20,v29,v45,v66,v91,v138,v143,v269]) .nil .nil) (.node (8,[v12,v20,v29,v45,v66,v91,v138,v269]) .nil .nil))) (.node (8,[v12,v20,v29,v45,v66,v115,v138,v143]) (.node (8,[v12,v20,v29,v45,v66,v91,v143,v209]) (.node (8,[v12,v20,v29,v45,v66,v91,v143,v172]) .nil .nil) (.node (8,[v12,v20,v29,v45,v66,v91,v143,v241]) .nil .nil)) (.node (8,[v12,v20,v29,v45,v66,v138,v269]) (.node (8,[v12,v20,v29,v45,v66,v138,v143,v269]) .nil .nil) (.node (8,[v12,v20,v29,v45,v85,v91,v138,v143]) .nil .nil)))) (.node (8,[v12,v20,v45,v85,v91,v138,v143]) (.node (8,[v12,v20,v29,v66,v91,v143,v209]) (.node (8,[v12,v20,v29,v52,v66,v91,v138,v143]) (.node (8,[v12,v20,v29,v45,v91,v143,v241]) .nil .nil) (.node (8,[v12,v20,v29,v66,v91,v138,v143,v209]) .nil .nil)) (.node (8,[v12,v20,v45,v66,v91,v138,v143,v185]) (.node (8,[v12,v20,v45,v66,v85,v91,v138,v143]) .nil .nil) (.node (8,[v12,v20,v45,v66,v91,v138,v185]) .nil .nil))) (.node (8,[v12,v29,v45,v66,v115,v138,v143]) (.node (8,[v12,v29,v45,v66,v91,v138,v143,v172]) (.node (8,[v12,v29,v45,v66,v91,v115,v138,v143]) .nil .nil) (.node (8,[v12,v29,v45,v66,v91,v143,v172]) .nil .nil)) (.node (8,[v20,v29,v52,v66,v91,v138,v143]) (.node (8,[v20,v29,v45,v52,v66,v91,v138,v143]) .nil .nil) (.node (9,[v12,v20,v29,v45,v66,v91,v138,v143]) .nil .nil)))))
noncomputable def stem_167 : Tree := .node (8,[v12,v20,v29,v45,v66,v91,v138,v143,v185]) block_173 block_174
noncomputable def stem_168 : Tree := .node (8,[v6,v12,v20,v29,v45,v66,v91,v138,v143]) stem_166 stem_167
noncomputable def stem_169 : Tree := .node (7,[v20,v29,v45,v66,v91,v138,v143,v152]) stem_164 stem_168
noncomputable def stem_170 : Tree := .node (7,[v12,v29,v45,v66,v79,v115,v138,v143]) stem_160 stem_169
noncomputable def stem_171 : Tree := .node (7,[v12,v20,v29,v45,v91,v97,v143,v241]) stem_150 stem_170
noncomputable def stem_172 : Tree := .node (6,[v20,v45,v66,v91,v134,v152,v185]) stem_129 stem_171
noncomputable def stem_173 : Tree := .node (6,[v12,v20,v34,v45,v66,v138,v269]) stem_86 stem_172
noncomputable def table : Tree := stem_173

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem test_block_0 : (entries block_0).all (nodeOK table) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem test_block_60 : (entries block_60).all (nodeOK table) = true := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
theorem test_block_127 : (entries block_127).all (nodeOK table) = true := by
  decide +kernel

end PEqualNP.Outside.L_meta_6349.Enum
