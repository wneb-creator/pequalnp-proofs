import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_6349

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
    if (a :: b :: r).contains w then false else
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
    (hz : z ∈ basicOps a b) (hnew : z ∉ a :: b :: r) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : cuts (z :: kept) = -1) (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  simp only [List.contains_iff_mem, if_neg hnew]
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
        have hzfresh : z ∉ a :: b :: r := by
          intro hzmem
          exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hzmem))
        apply dispatch_complete (k := k) (extra := extra) (optimized k) hop hzfresh hk (by omega) (by omega) (cuts_full hl)
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

def nextStates (extra : ℕ) (a b : W) (r : List W) (w : W) : List (ℕ × List W) :=
  if (a :: b :: r).contains w then [] else
  let v := sep w ||| cuts r
  (if v == -1 then [(extra, w :: r)] else []) ++
  (if extra != 0 && (v ||| sep a == -1) then [(extra - 1, w :: a :: r)] else []) ++
  (if extra != 0 && (v ||| sep b == -1) then [(extra - 1, w :: b :: r)] else []) ++
  (if decide (extra ≥ 2) && (v ||| sep a ||| sep b == -1) then [(extra - 2, w :: a :: b :: r)] else [])

lemma any_if_singleton {α : Type} (b : Bool) (x : α) (f : α → Bool) :
    (if b then [x] else []).any f = (b && f x) := by
  cases b <;> simp

lemma dispatch_nextStates (extra : ℕ) (next : ℕ → List W → Bool) (a b : W) (r : List W) :
    dispatch extra next a b r =
      ((ops a b).flatMap (nextStates extra a b r)).any (fun t => next t.1 t.2) := by
  simp only [dispatch, List.any_flatMap]
  congr 1
  funext w
  by_cases hw : (a :: b :: r).contains w = true
  · simp only [nextStates, hw, ↓reduceIte, List.any_nil]
  · simp only [nextStates, if_neg hw, List.any_append, any_if_singleton]
    cases h : (extra != 0) <;> simp [Bool.or_assoc, Bool.and_assoc]

def expand (extra : ℕ) (ws : List W) : List (ℕ × List W) :=
  (pairs ws).flatMap fun p => (ops p.1 p.2.1).flatMap (nextStates extra p.1 p.2.1 p.2.2)

lemma optimized_expand (k extra : ℕ) (ws : List W) :
    optimized (k + 1) extra ws =
      ((ws == [goal]) || (expand extra ws).any (fun t => optimized k t.1 t.2)) := by
  simp only [optimized, expand, dispatch_nextStates, List.any_flatMap]

def val0 : W := 0x0
def val1 : W := 0xff0000000000000000
def val2 : W := 0x101010101010101
def val3 : W := 0xff000000000000000000
def val4 : W := 0xff00000000000000000000
def val5 : W := 0xffffff0101010101010101
def val6 : W := 0x202020202020202
def val7 : W := 0xff0000000000000000000000
def val8 : W := 0xff00ff000000000000000000
def val9 : W := 0xffffffff0101010101010101
def val10 : W := 0x404040404040404
def val11 : W := 0xff000000000000000000000000
def val12 : W := 0xff00ffffff0101010101010101
def val13 : W := 0xffff0000000606060606060606
def val14 : W := 0xffff0000ff0606060606060606
def val15 : W := 0xffff00ff000606060606060606
def val16 : W := 0xffffff00000606060606060606
def val17 : W := 0xffffffffff0707070707070707
def val18 : W := 0x808080808080808
def val19 : W := 0xff00000000000000000000000000
def val20 : W := 0xff0000ff00000000000000000000
def val21 : W := 0xff0000ffffff0101010101010101
def val22 : W := 0xffffff0000000606060606060606
def val23 : W := 0xff0000000000000000000000000000
def val24 : W := 0xff000000ffffff0101010101010101
def val25 : W := 0xff00ff000000000000000000000000
def val26 : W := 0xff00ffff0000000606060606060606
def val27 : W := 0x1010101010101010
def val28 : W := 0xffff00000000001818181818181818
def val29 : W := 0xffff00000000ff1818181818181818
def val30 : W := 0xffff000000ff001818181818181818
def val31 : W := 0xffff0000ff00001818181818181818
def val32 : W := 0xffff0000ffffff1919191919191919
def val33 : W := 0xffff00ff0000001818181818181818
def val34 : W := 0xffffff000000001818181818181818
def val35 : W := 0xffffffff0000001e1e1e1e1e1e1e1e
def val36 : W := 0xff000000000000000000000000000000
def val37 : W := 0xff000000000000ff0000000000000000
def val38 : W := 0xff00000000ffffff0101010101010101
def val39 : W := 0xff0000ffff0000000606060606060606
def val40 : W := 0xff0000ffff0000ff0606060606060606
def val41 : W := 0xff000000000000ff0a0a0a0a0a0a0a0a
def val42 : W := 0xff0000000000ffff0a0a0a0a0a0a0a0a
def val43 : W := 0xff00000000ff00ff0a0a0a0a0a0a0a0a
def val44 : W := 0xff00000000ffffff0b0b0b0b0b0b0b0b
def val45 : W := 0xff000000ff0000ff0a0a0a0a0a0a0a0a
def val46 : W := 0xff0000ff000000ff0a0a0a0a0a0a0a0a
def val47 : W := 0xff0000ffff0000ff0e0e0e0e0e0e0e0e
def val48 : W := 0xff0000ffffffffff0f0f0f0f0f0f0f0f
def val49 : W := 0xff00ff00000000ff0a0a0a0a0a0a0a0a
def val50 : W := 0xffff0000000000ff0a0a0a0a0a0a0a0a
def val51 : W := 0xffffff00000000001818181818181818
def val52 : W := 0xffffff00000000ff1818181818181818
def val53 : W := 0xffffff00000000ff1a1a1a1a1a1a1a1a
def val54 : W := 0xffffff0000ffffff1b1b1b1b1b1b1b1b
def val55 : W := 0xffffffffff0000ff1e1e1e1e1e1e1e1e
def val56 : W := 0x2020202020202020
def val57 : W := 0xff00ff0000002121212121212121
def val58 : W := 0xff00ff0000ff2121212121212121
def val59 : W := 0xff00ff00ff002121212121212121
def val60 : W := 0xff00ffff00002121212121212121
def val61 : W := 0xff00ffffffff2121212121212121
def val62 : W := 0xffffff0000002121212121212121
def val63 : W := 0xffffff0000002727272727272727
def val64 : W := 0xffffffffffff2727272727272727
def val65 : W := 0xffff00ff0000002121212121212121
def val66 : W := 0xffff00ff0000003939393939393939
def val67 : W := 0xffff00ffffffff3939393939393939
def val68 : W := 0xff00ff00ff0000002121212121212121
def val69 : W := 0xff00ff00ff0000ff2121212121212121
def val70 : W := 0xff00ff00ffffffff2121212121212121
def val71 : W := 0xff00ff00ff0000ff2b2b2b2b2b2b2b2b
def val72 : W := 0xff00ff00ffffffff2b2b2b2b2b2b2b2b
def val73 : W := 0xff00ffffff0000ff2f2f2f2f2f2f2f2f
def val74 : W := 0xffffff00ff0000ff3b3b3b3b3b3b3b3b
def val75 : W := 0x4040404040404040
def val76 : W := 0xff00000000ff004444444444444444
def val77 : W := 0xff00000000ffff4444444444444444
def val78 : W := 0xff000000ffff004444444444444444
def val79 : W := 0xff000000ffffff4545454545454545
def val80 : W := 0xff0000ff00ff004444444444444444
def val81 : W := 0xff00ff0000ff004444444444444444
def val82 : W := 0xff00ffff00ff004646464646464646
def val83 : W := 0xff00ffffffffff4747474747474747
def val84 : W := 0xffff000000ff004444444444444444
def val85 : W := 0xffff000000ff005c5c5c5c5c5c5c5c
def val86 : W := 0xffffffff00ff005e5e5e5e5e5e5e5e
def val87 : W := 0xff000000000000004040404040404040
def val88 : W := 0xffff00000000ff004444444444444444
def val89 : W := 0xffff00000000ffff4444444444444444
def val90 : W := 0xffff00ffff00ff004646464646464646
def val91 : W := 0xffff00000000ffff4e4e4e4e4e4e4e4e
def val92 : W := 0xffff00ffff00ffff4e4e4e4e4e4e4e4e
def val93 : W := 0xffffff000000ffff5e5e5e5e5e5e5e5e
def val94 : W := 0xffff00ff00ff006565656565656565
def val95 : W := 0xffff00ffffffff6565656565656565
def val96 : W := 0xffffffff00ff006767676767676767
def val97 : W := 0xffffffffffffff6767676767676767
def val98 : W := 0x8080808080808080
def val99 : W := 0xff00ff00009090909090909090
def val100 : W := 0xff00ff00ff9090909090909090
def val101 : W := 0xff00ffff009090909090909090
def val102 : W := 0xff00ffffff9191919191919191
def val103 : W := 0xffffff00009090909090909090
def val104 : W := 0xffffff00009696969696969696
def val105 : W := 0xffff00ff00009090909090909090
def val106 : W := 0xff00ff00ff00009090909090909090
def val107 : W := 0xffffff00ff00009898989898989898
def val108 : W := 0xffffff00ffffff9999999999999999
def val109 : W := 0xffffffffff00009e9e9e9e9e9e9e9e
def val110 : W := 0xff000000000000008080808080808080
def val111 : W := 0xff0000ff00ff00009090909090909090
def val112 : W := 0xff0000ff00ff00ff9090909090909090
def val113 : W := 0xff0000ff00ff00ff9a9a9a9a9a9a9a9a
def val114 : W := 0xff0000ffffff00ff9e9e9e9e9e9e9e9e
def val115 : W := 0xffffffff00ff00009898989898989898
def val116 : W := 0xffffffff00ff00ff9a9a9a9a9a9a9a9a
def val117 : W := 0xffffffff0000b1b1b1b1b1b1b1b1
def val118 : W := 0xffffffffffffb1b1b1b1b1b1b1b1
def val119 : W := 0xffffffffff0000b9b9b9b9b9b9b9b9
def val120 : W := 0xffffffffffffffb9b9b9b9b9b9b9b9
def val121 : W := 0xff00ff00ffff00d4d4d4d4d4d4d4d4
def val122 : W := 0xff00ffffffff00d6d6d6d6d6d6d6d6
def val123 : W := 0xffffff00ffff00dcdcdcdcdcdcdcdc
def val124 : W := 0xffffffffffff00dededededededede
def val125 : W := 0xff00000000000000e0e0e0e0e0e0e0e0
def val126 : W := 0xff000000000000ffe0e0e0e0e0e0e0e0
def val127 : W := 0xff0000000000ff00e0e0e0e0e0e0e0e0
def val128 : W := 0xff00000000ff0000e0e0e0e0e0e0e0e0
def val129 : W := 0xff00000000ffffffe1e1e1e1e1e1e1e1
def val130 : W := 0xff000000ff000000e0e0e0e0e0e0e0e0
def val131 : W := 0xff0000ff00000000e0e0e0e0e0e0e0e0
def val132 : W := 0xff0000ffff000000e6e6e6e6e6e6e6e6
def val133 : W := 0xff000000000000ffeaeaeaeaeaeaeaea
def val134 : W := 0xff0000ffff0000ffeeeeeeeeeeeeeeee
def val135 : W := 0xff00ff0000000000e0e0e0e0e0e0e0e0
def val136 : W := 0xff00ff00ff000000e1e1e1e1e1e1e1e1
def val137 : W := 0xff00ff00ffffffffe1e1e1e1e1e1e1e1
def val138 : W := 0xff00ffffff000000e7e7e7e7e7e7e7e7
def val139 : W := 0xff00ff00ff0000ffebebebebebebebeb
def val140 : W := 0xffff000000000000e0e0e0e0e0e0e0e0
def val141 : W := 0xffff00000000ff00e4e4e4e4e4e4e4e4
def val142 : W := 0xffff000000ffffffe5e5e5e5e5e5e5e5
def val143 : W := 0xffff00ffff00ff00e6e6e6e6e6e6e6e6
def val144 : W := 0xffff00000000ffffeeeeeeeeeeeeeeee
def val145 : W := 0xffffff00ff00ff00e5e5e5e5e5e5e5e5
def val146 : W := 0xffffff00ffffffffe5e5e5e5e5e5e5e5
def val147 : W := 0xff0000ff00ff0000f0f0f0f0f0f0f0f0
def val148 : W := 0xff0000ff00fffffff1f1f1f1f1f1f1f1
def val149 : W := 0xff0000ffffff0000f6f6f6f6f6f6f6f6
def val150 : W := 0xff0000ff00ff00fffafafafafafafafa
def val151 : W := 0xff00ffffffff0000f1f1f1f1f1f1f1f1
def val152 : W := 0xff00fffffffffffff1f1f1f1f1f1f1f1
def val153 : W := 0xffff00ff00ffff00f4f4f4f4f4f4f4f4
def val154 : W := 0xffffff0000000000f8f8f8f8f8f8f8f8
def val155 : W := 0xffffff00000000fffafafafafafafafa
def val156 : W := 0xffffff00ff000000f9f9f9f9f9f9f9f9
def val157 : W := 0xffffff000000ff00fcfcfcfcfcfcfcfc
def val158 : W := 0xffffffff00ff0000f8f8f8f8f8f8f8f8

def state0 : List W := [val5, val13, val28, val125, val41, val57, val76, val99]
def state1 : List W := [val0, val5, val13, val28, val125, val41, val57, val76, val99]
def state2 : List W := [val17, val5, val13, val28, val125, val41, val57, val76, val99]
def state3 : List W := [val0, val5, val28, val13, val125, val41, val57, val76, val99]
def state4 : List W := [val32, val5, val28, val13, val125, val41, val57, val76, val99]
def state5 : List W := [val0, val5, val125, val13, val28, val41, val57, val76, val99]
def state6 : List W := [val129, val5, val13, val28, val41, val57, val76, val99]
def state7 : List W := [val37, val5, val13, val28, val57, val76, val99]
def state8 : List W := [val38, val37, val13, val28, val57, val76, val99]
def state9 : List W := [val40, val37, val5, val28, val57, val76, val99]
def state10 : List W := [val52, val37, val5, val13, val57, val76, val99]
def state11 : List W := [val69, val37, val5, val13, val28, val76, val99]
def state12 : List W := [val89, val37, val5, val13, val28, val57, val99]
def state13 : List W := [val112, val37, val5, val13, val28, val57, val76]
def state14 : List W := [val61, val37, val13, val28, val76, val99]
def state15 : List W := [val61, val5, val37, val13, val28, val76, val99]
def state16 : List W := [val61, val57, val37, val13, val28, val76, val99]
def state17 : List W := [val82, val37, val5, val28, val57, val99]
def state18 : List W := [val82, val13, val37, val5, val28, val57, val99]
def state19 : List W := [val82, val76, val37, val5, val28, val57, val99]
def state20 : List W := [val107, val37, val5, val13, val57, val76]
def state21 : List W := [val107, val28, val37, val5, val13, val57, val76]
def state22 : List W := [val107, val99, val37, val5, val13, val57, val76]
def state23 : List W := [val37, val129, val5, val13, val28, val57, val76, val99]
def state24 : List W := [val37, val41, val5, val13, val28, val57, val76, val99]
def state25 : List W := [val137, val5, val13, val28, val41, val76, val99]
def state26 : List W := [val137, val129, val5, val13, val28, val41, val76, val99]
def state27 : List W := [val137, val57, val5, val13, val28, val41, val76, val99]
def state28 : List W := [val142, val76, val5, val13, val28, val41, val57, val99]
def state29 : List W := [val148, val99, val5, val13, val28, val41, val57, val76]
def state30 : List W := [val17, val13, val129, val28, val41, val57, val76, val99]
def state31 : List W := [val32, val28, val129, val13, val41, val57, val76, val99]
def state32 : List W := [val44, val41, val129, val13, val28, val57, val76, val99]
def state33 : List W := [val61, val129, val13, val28, val41, val76, val99]
def state34 : List W := [val137, val61, val13, val28, val41, val76, val99]
def state35 : List W := [val37, val61, val13, val28, val76, val99]
def state36 : List W := [val37, val129, val61, val13, val28, val76, val99]
def state37 : List W := [val37, val41, val61, val13, val28, val76, val99]
def state38 : List W := [val142, val76, val61, val13, val28, val41, val99]
def state39 : List W := [val148, val99, val61, val13, val28, val41, val76]
def state40 : List W := [val47, val61, val129, val28, val76, val99]
def state41 : List W := [val47, val13, val61, val129, val28, val76, val99]
def state42 : List W := [val47, val41, val61, val129, val28, val76, val99]
def state43 : List W := [val82, val61, val129, val28, val41, val99]
def state44 : List W := [val82, val13, val61, val129, val28, val41, val99]
def state45 : List W := [val82, val76, val61, val129, val28, val41, val99]
def state46 : List W := [val53, val61, val129, val13, val76, val99]
def state47 : List W := [val53, val28, val61, val129, val13, val76, val99]
def state48 : List W := [val53, val41, val61, val129, val13, val76, val99]
def state49 : List W := [val107, val61, val129, val13, val41, val76]
def state50 : List W := [val107, val28, val61, val129, val13, val41, val76]
def state51 : List W := [val107, val99, val61, val129, val13, val41, val76]
def state52 : List W := [val61, val5, val129, val13, val28, val41, val76, val99]
def state53 : List W := [val61, val57, val129, val13, val28, val41, val76, val99]
def state54 : List W := [val47, val129, val5, val28, val57, val76, val99]
def state55 : List W := [val47, val13, val129, val5, val28, val57, val76, val99]
def state56 : List W := [val47, val41, val129, val5, val28, val57, val76, val99]
def state57 : List W := [val82, val129, val5, val28, val41, val57, val99]
def state58 : List W := [val82, val13, val129, val5, val28, val41, val57, val99]
def state59 : List W := [val82, val76, val129, val5, val28, val41, val57, val99]
def state60 : List W := [val53, val129, val5, val13, val57, val76, val99]
def state61 : List W := [val53, val28, val129, val5, val13, val57, val76, val99]
def state62 : List W := [val53, val41, val129, val5, val13, val57, val76, val99]
def state63 : List W := [val107, val129, val5, val13, val41, val57, val76]
def state64 : List W := [val107, val28, val129, val5, val13, val41, val57, val76]
def state65 : List W := [val107, val99, val129, val5, val13, val41, val57, val76]
def state66 : List W := [val129, val5, val125, val13, val28, val41, val57, val76, val99]
def state67 : List W := [val1, val5, val41, val13, val28, val125, val57, val76, val99]
def state68 : List W := [val14, val5, val41, val28, val125, val57, val76, val99]
def state69 : List W := [val29, val5, val41, val13, val125, val57, val76, val99]
def state70 : List W := [val126, val5, val41, val13, val28, val57, val76, val99]
def state71 : List W := [val58, val5, val41, val13, val28, val125, val76, val99]
def state72 : List W := [val77, val5, val41, val13, val28, val125, val57, val99]
def state73 : List W := [val100, val5, val41, val13, val28, val125, val57, val76]
def state74 : List W := [val44, val1, val13, val28, val125, val57, val76, val99]
def state75 : List W := [val61, val1, val41, val13, val28, val125, val76, val99]
def state76 : List W := [val47, val1, val5, val28, val125, val57, val76, val99]
def state77 : List W := [val53, val1, val5, val13, val125, val57, val76, val99]
def state78 : List W := [val36, val1, val5, val13, val28, val57, val76, val99]
def state79 : List W := [val82, val1, val5, val41, val28, val125, val57, val99]
def state80 : List W := [val107, val1, val5, val41, val13, val125, val57, val76]
def state81 : List W := [val136, val1, val5, val41, val13, val28, val76, val99]
def state82 : List W := [val141, val1, val5, val41, val13, val28, val57, val99]
def state83 : List W := [val147, val1, val5, val41, val13, val28, val57, val76]
def state84 : List W := [val44, val5, val41, val13, val28, val125, val57, val76, val99]
def state85 : List W := [val36, val5, val41, val13, val28, val57, val76, val99]
def state86 : List W := [val1, val44, val13, val28, val125, val57, val76, val99]
def state87 : List W := [val129, val44, val41, val13, val28, val57, val76, val99]
def state88 : List W := [val61, val44, val41, val13, val28, val125, val76, val99]
def state89 : List W := [val47, val44, val5, val28, val125, val57, val76, val99]
def state90 : List W := [val53, val44, val5, val13, val125, val57, val76, val99]
def state91 : List W := [val82, val44, val5, val41, val28, val125, val57, val99]
def state92 : List W := [val107, val44, val5, val41, val13, val125, val57, val76]
def state93 : List W := [val136, val44, val5, val41, val13, val28, val76, val99]
def state94 : List W := [val141, val44, val5, val41, val13, val28, val57, val99]
def state95 : List W := [val147, val44, val5, val41, val13, val28, val57, val76]
def state96 : List W := [val2, val5, val57, val13, val28, val125, val41, val76, val99]
def state97 : List W := [val61, val13, val28, val125, val41, val76, val99]
def state98 : List W := [val7, val61, val13, val28, val125, val41, val76, val99]
def state99 : List W := [val64, val61, val13, val28, val125, val41, val76, val99]
def state100 : List W := [val19, val61, val28, val13, val125, val41, val76, val99]
def state101 : List W := [val67, val61, val28, val13, val125, val41, val76, val99]
def state102 : List W := [val56, val61, val125, val13, val28, val41, val76, val99]
def state103 : List W := [val137, val61, val13, val28, val41, val76, val99]
def state104 : List W := [val37, val137, val61, val13, val28, val76, val99]
def state105 : List W := [val146, val76, val61, val13, val28, val41, val99]
def state106 : List W := [val152, val99, val61, val13, val28, val41, val76]
def state107 : List W := [val64, val13, val137, val28, val41, val76, val99]
def state108 : List W := [val67, val28, val137, val13, val41, val76, val99]
def state109 : List W := [val72, val41, val137, val13, val28, val76, val99]
def state110 : List W := [val47, val137, val61, val28, val76, val99]
def state111 : List W := [val47, val13, val137, val61, val28, val76, val99]
def state112 : List W := [val47, val41, val137, val61, val28, val76, val99]
def state113 : List W := [val82, val137, val61, val28, val41, val99]
def state114 : List W := [val82, val13, val137, val61, val28, val41, val99]
def state115 : List W := [val82, val76, val137, val61, val28, val41, val99]
def state116 : List W := [val53, val137, val61, val13, val76, val99]
def state117 : List W := [val53, val28, val137, val61, val13, val76, val99]
def state118 : List W := [val53, val41, val137, val61, val13, val76, val99]
def state119 : List W := [val107, val137, val61, val13, val41, val76]
def state120 : List W := [val107, val28, val137, val61, val13, val41, val76]
def state121 : List W := [val107, val99, val137, val61, val13, val41, val76]
def state122 : List W := [val137, val61, val125, val13, val28, val41, val76, val99]
def state123 : List W := [val1, val61, val41, val13, val28, val125, val76, val99]
def state124 : List W := [val72, val61, val41, val13, val28, val125, val76, val99]
def state125 : List W := [val3, val61, val76, val13, val28, val125, val41, val99]
def state126 : List W := [val95, val61, val76, val13, val28, val125, val41, val99]
def state127 : List W := [val4, val61, val99, val13, val28, val125, val41, val76]
def state128 : List W := [val118, val61, val99, val13, val28, val125, val41, val76]
def state129 : List W := [val0, val13, val28, val61, val125, val41, val76, val99]
def state130 : List W := [val35, val13, val28, val61, val125, val41, val76, val99]
def state131 : List W := [val0, val13, val125, val61, val28, val41, val76, val99]
def state132 : List W := [val132, val13, val125, val61, val28, val41, val76, val99]
def state133 : List W := [val6, val13, val41, val61, val28, val125, val76, val99]
def state134 : List W := [val47, val61, val28, val125, val76, val99]
def state135 : List W := [val47, val13, val61, val28, val125, val76, val99]
def state136 : List W := [val47, val41, val61, val28, val125, val76, val99]
def state137 : List W := [val47, val13, val41, val61, val28, val125, val76, val99]
def state138 : List W := [val10, val13, val76, val61, val28, val125, val41, val99]
def state139 : List W := [val82, val61, val28, val125, val41, val99]
def state140 : List W := [val8, val82, val61, val28, val125, val41, val99]
def state141 : List W := [val97, val82, val61, val28, val125, val41, val99]
def state142 : List W := [val23, val82, val28, val61, val125, val41, val99]
def state143 : List W := [val86, val82, val28, val61, val125, val41, val99]
def state144 : List W := [val75, val82, val125, val61, val28, val41, val99]
def state145 : List W := [val143, val82, val125, val61, val28, val41, val99]
def state146 : List W := [val6, val82, val41, val61, val28, val125, val99]
def state147 : List W := [val92, val82, val41, val61, val28, val125, val99]
def state148 : List W := [val11, val82, val99, val61, val28, val125, val41]
def state149 : List W := [val122, val82, val99, val61, val28, val125, val41]
def state150 : List W := [val19, val61, val28, val82, val125, val41, val99]
def state151 : List W := [val67, val61, val28, val82, val125, val41, val99]
def state152 : List W := [val56, val61, val125, val82, val28, val41, val99]
def state153 : List W := [val137, val61, val82, val28, val41, val99]
def state154 : List W := [val137, val61, val125, val82, val28, val41, val99]
def state155 : List W := [val1, val61, val41, val82, val28, val125, val99]
def state156 : List W := [val72, val61, val41, val82, val28, val125, val99]
def state157 : List W := [val4, val61, val99, val82, val28, val125, val41]
def state158 : List W := [val118, val61, val99, val82, val28, val125, val41]
def state159 : List W := [val0, val28, val125, val82, val61, val41, val99]
def state160 : List W := [val154, val28, val125, val82, val61, val41, val99]
def state161 : List W := [val18, val28, val41, val82, val61, val125, val99]
def state162 : List W := [val53, val28, val82, val61, val125, val99]
def state163 : List W := [val53, val28, val41, val82, val61, val125, val99]
def state164 : List W := [val27, val28, val99, val82, val61, val125, val41]
def state165 : List W := [val107, val82, val61, val125, val41]
def state166 : List W := [val107, val28, val82, val61, val125, val41]
def state167 : List W := [val107, val99, val82, val61, val125, val41]
def state168 : List W := [val107, val28, val99, val82, val61, val125, val41]
def state169 : List W := [val36, val41, val82, val61, val28, val99]
def state170 : List W := [val36, val125, val41, val82, val61, val28, val99]
def state171 : List W := [val133, val125, val41, val82, val61, val28, val99]
def state172 : List W := [val98, val125, val99, val82, val61, val28, val41]
def state173 : List W := [val147, val99, val82, val61, val28, val41]
def state174 : List W := [val147, val125, val99, val82, val61, val28, val41]
def state175 : List W := [val0, val41, val99, val82, val61, val28, val125]
def state176 : List W := [val113, val41, val99, val82, val61, val28, val125]
def state177 : List W := [val82, val13, val61, val28, val125, val41, val99]
def state178 : List W := [val82, val76, val61, val28, val125, val41, val99]
def state179 : List W := [val82, val13, val76, val61, val28, val125, val41, val99]
def state180 : List W := [val11, val13, val99, val61, val28, val125, val41, val76]
def state181 : List W := [val104, val13, val99, val61, val28, val125, val41, val76]
def state182 : List W := [val0, val28, val125, val61, val13, val41, val76, val99]
def state183 : List W := [val154, val28, val125, val61, val13, val41, val76, val99]
def state184 : List W := [val18, val28, val41, val61, val13, val125, val76, val99]
def state185 : List W := [val53, val61, val13, val125, val76, val99]
def state186 : List W := [val53, val28, val61, val13, val125, val76, val99]
def state187 : List W := [val53, val41, val61, val13, val125, val76, val99]
def state188 : List W := [val53, val28, val41, val61, val13, val125, val76, val99]
def state189 : List W := [val23, val28, val76, val61, val13, val125, val41, val99]
def state190 : List W := [val85, val28, val76, val61, val13, val125, val41, val99]
def state191 : List W := [val27, val28, val99, val61, val13, val125, val41, val76]
def state192 : List W := [val107, val61, val13, val125, val41, val76]
def state193 : List W := [val20, val107, val61, val13, val125, val41, val76]
def state194 : List W := [val120, val107, val61, val13, val125, val41, val76]
def state195 : List W := [val11, val107, val13, val61, val125, val41, val76]
def state196 : List W := [val109, val107, val13, val61, val125, val41, val76]
def state197 : List W := [val98, val107, val125, val61, val13, val41, val76]
def state198 : List W := [val158, val107, val125, val61, val13, val41, val76]
def state199 : List W := [val18, val107, val41, val61, val13, val125, val76]
def state200 : List W := [val116, val107, val41, val61, val13, val125, val76]
def state201 : List W := [val23, val107, val76, val61, val13, val125, val41]
def state202 : List W := [val123, val107, val76, val61, val13, val125, val41]
def state203 : List W := [val7, val61, val13, val107, val125, val41, val76]
def state204 : List W := [val64, val61, val13, val107, val125, val41, val76]
def state205 : List W := [val56, val61, val125, val107, val13, val41, val76]
def state206 : List W := [val137, val61, val107, val13, val41, val76]
def state207 : List W := [val137, val61, val125, val107, val13, val41, val76]
def state208 : List W := [val1, val61, val41, val107, val13, val125, val76]
def state209 : List W := [val72, val61, val41, val107, val13, val125, val76]
def state210 : List W := [val3, val61, val76, val107, val13, val125, val41]
def state211 : List W := [val95, val61, val76, val107, val13, val125, val41]
def state212 : List W := [val0, val13, val125, val107, val61, val41, val76]
def state213 : List W := [val132, val13, val125, val107, val61, val41, val76]
def state214 : List W := [val6, val13, val41, val107, val61, val125, val76]
def state215 : List W := [val47, val13, val107, val61, val125, val76]
def state216 : List W := [val47, val13, val41, val107, val61, val125, val76]
def state217 : List W := [val10, val13, val76, val107, val61, val125, val41]
def state218 : List W := [val82, val107, val61, val125, val41]
def state219 : List W := [val82, val13, val107, val61, val125, val41]
def state220 : List W := [val82, val76, val107, val61, val125, val41]
def state221 : List W := [val82, val13, val76, val107, val61, val125, val41]
def state222 : List W := [val36, val41, val107, val61, val13, val76]
def state223 : List W := [val36, val125, val41, val107, val61, val13, val76]
def state224 : List W := [val133, val125, val41, val107, val61, val13, val76]
def state225 : List W := [val75, val125, val76, val107, val61, val13, val41]
def state226 : List W := [val141, val76, val107, val61, val13, val41]
def state227 : List W := [val141, val125, val76, val107, val61, val13, val41]
def state228 : List W := [val0, val41, val76, val107, val61, val13, val125]
def state229 : List W := [val91, val41, val76, val107, val61, val13, val125]
def state230 : List W := [val107, val28, val61, val13, val125, val41, val76]
def state231 : List W := [val107, val99, val61, val13, val125, val41, val76]
def state232 : List W := [val107, val28, val99, val61, val13, val125, val41, val76]
def state233 : List W := [val36, val41, val61, val13, val28, val76, val99]
def state234 : List W := [val70, val41, val13, val28, val76, val99]
def state235 : List W := [val70, val36, val41, val13, val28, val76, val99]
def state236 : List W := [val70, val61, val41, val13, val28, val76, val99]
def state237 : List W := [val39, val36, val41, val61, val28, val76, val99]
def state238 : List W := [val51, val36, val41, val61, val13, val76, val99]
def state239 : List W := [val88, val41, val61, val13, val28, val99]
def state240 : List W := [val88, val36, val41, val61, val13, val28, val99]
def state241 : List W := [val88, val76, val41, val61, val13, val28, val99]
def state242 : List W := [val111, val41, val61, val13, val28, val76]
def state243 : List W := [val111, val36, val41, val61, val13, val28, val76]
def state244 : List W := [val111, val99, val41, val61, val13, val28, val76]
def state245 : List W := [val1, val61, val36, val13, val28, val76, val99]
def state246 : List W := [val47, val36, val61, val28, val76, val99]
def state247 : List W := [val47, val41, val36, val61, val28, val76, val99]
def state248 : List W := [val47, val13, val36, val61, val28, val76, val99]
def state249 : List W := [val53, val36, val61, val13, val76, val99]
def state250 : List W := [val53, val41, val36, val61, val13, val76, val99]
def state251 : List W := [val53, val28, val36, val61, val13, val76, val99]
def state252 : List W := [val91, val76, val36, val61, val13, val28, val99]
def state253 : List W := [val113, val99, val36, val61, val13, val28, val76]
def state254 : List W := [val82, val36, val41, val61, val28, val99]
def state255 : List W := [val82, val13, val36, val41, val61, val28, val99]
def state256 : List W := [val82, val76, val36, val41, val61, val28, val99]
def state257 : List W := [val107, val36, val41, val61, val13, val76]
def state258 : List W := [val107, val28, val36, val41, val61, val13, val76]
def state259 : List W := [val107, val99, val36, val41, val61, val13, val76]
def state260 : List W := [val36, val125, val41, val61, val13, val28, val76, val99]
def state261 : List W := [val133, val125, val41, val61, val13, val28, val76, val99]
def state262 : List W := [val75, val125, val76, val61, val13, val28, val41, val99]
def state263 : List W := [val141, val76, val61, val13, val28, val41, val99]
def state264 : List W := [val141, val125, val76, val61, val13, val28, val41, val99]
def state265 : List W := [val98, val125, val99, val61, val13, val28, val41, val76]
def state266 : List W := [val147, val99, val61, val13, val28, val41, val76]
def state267 : List W := [val147, val125, val99, val61, val13, val28, val41, val76]
def state268 : List W := [val0, val41, val76, val61, val13, val28, val125, val99]
def state269 : List W := [val91, val41, val76, val61, val13, val28, val125, val99]
def state270 : List W := [val0, val41, val99, val61, val13, val28, val125, val76]
def state271 : List W := [val113, val41, val99, val61, val13, val28, val125, val76]
def state272 : List W := [val0, val76, val99, val61, val13, val28, val125, val41]
def state273 : List W := [val121, val76, val99, val61, val13, val28, val125, val41]
def state274 : List W := [val61, val5, val13, val28, val125, val41, val76, val99]
def state275 : List W := [val137, val61, val5, val13, val28, val41, val76, val99]
def state276 : List W := [val137, val125, val5, val13, val28, val41, val76, val99]
def state277 : List W := [val0, val13, val61, val28, val125, val41, val76, val99]
def state278 : List W := [val17, val13, val61, val28, val125, val41, val76, val99]
def state279 : List W := [val0, val28, val61, val13, val125, val41, val76, val99]
def state280 : List W := [val32, val28, val61, val13, val125, val41, val76, val99]
def state281 : List W := [val0, val125, val61, val13, val28, val41, val76, val99]
def state282 : List W := [val129, val61, val13, val28, val41, val76, val99]
def state283 : List W := [val47, val129, val61, val28, val76, val99]
def state284 : List W := [val47, val13, val129, val61, val28, val76, val99]
def state285 : List W := [val47, val41, val129, val61, val28, val76, val99]
def state286 : List W := [val82, val129, val61, val28, val41, val99]
def state287 : List W := [val82, val13, val129, val61, val28, val41, val99]
def state288 : List W := [val82, val76, val129, val61, val28, val41, val99]
def state289 : List W := [val53, val129, val61, val13, val76, val99]
def state290 : List W := [val53, val28, val129, val61, val13, val76, val99]
def state291 : List W := [val53, val41, val129, val61, val13, val76, val99]
def state292 : List W := [val107, val129, val61, val13, val41, val76]
def state293 : List W := [val107, val28, val129, val61, val13, val41, val76]
def state294 : List W := [val107, val99, val129, val61, val13, val41, val76]
def state295 : List W := [val129, val5, val61, val13, val28, val41, val76, val99]
def state296 : List W := [val129, val125, val61, val13, val28, val41, val76, val99]
def state297 : List W := [val1, val41, val61, val13, val28, val125, val76, val99]
def state298 : List W := [val44, val41, val61, val13, val28, val125, val76, val99]
def state299 : List W := [val3, val76, val61, val13, val28, val125, val41, val99]
def state300 : List W := [val79, val76, val61, val13, val28, val125, val41, val99]
def state301 : List W := [val4, val99, val61, val13, val28, val125, val41, val76]
def state302 : List W := [val102, val99, val61, val13, val28, val125, val41, val76]
def state303 : List W := [val47, val61, val5, val28, val125, val76, val99]
def state304 : List W := [val47, val13, val61, val5, val28, val125, val76, val99]
def state305 : List W := [val47, val41, val61, val5, val28, val125, val76, val99]
def state306 : List W := [val82, val61, val5, val28, val125, val41, val99]
def state307 : List W := [val82, val13, val61, val5, val28, val125, val41, val99]
def state308 : List W := [val82, val76, val61, val5, val28, val125, val41, val99]
def state309 : List W := [val53, val61, val5, val13, val125, val76, val99]
def state310 : List W := [val53, val28, val61, val5, val13, val125, val76, val99]
def state311 : List W := [val53, val41, val61, val5, val13, val125, val76, val99]
def state312 : List W := [val107, val61, val5, val13, val125, val41, val76]
def state313 : List W := [val107, val28, val61, val5, val13, val125, val41, val76]
def state314 : List W := [val107, val99, val61, val5, val13, val125, val41, val76]
def state315 : List W := [val36, val41, val61, val5, val13, val28, val76, val99]
def state316 : List W := [val141, val61, val5, val13, val28, val41, val99]
def state317 : List W := [val141, val125, val61, val5, val13, val28, val41, val99]
def state318 : List W := [val141, val76, val61, val5, val13, val28, val41, val99]
def state319 : List W := [val147, val61, val5, val13, val28, val41, val76]
def state320 : List W := [val147, val125, val61, val5, val13, val28, val41, val76]
def state321 : List W := [val147, val99, val61, val5, val13, val28, val41, val76]
def state322 : List W := [val61, val57, val13, val28, val125, val41, val76, val99]
def state323 : List W := [val137, val61, val57, val13, val28, val41, val76, val99]
def state324 : List W := [val7, val13, val61, val28, val125, val41, val76, val99]
def state325 : List W := [val63, val13, val61, val28, val125, val41, val76, val99]
def state326 : List W := [val19, val28, val61, val13, val125, val41, val76, val99]
def state327 : List W := [val66, val28, val61, val13, val125, val41, val76, val99]
def state328 : List W := [val56, val125, val61, val13, val28, val41, val76, val99]
def state329 : List W := [val136, val61, val13, val28, val41, val76, val99]
def state330 : List W := [val136, val57, val61, val13, val28, val41, val76, val99]
def state331 : List W := [val136, val125, val61, val13, val28, val41, val76, val99]
def state332 : List W := [val0, val41, val61, val13, val28, val125, val76, val99]
def state333 : List W := [val71, val41, val61, val13, val28, val125, val76, val99]
def state334 : List W := [val0, val76, val61, val13, val28, val125, val41, val99]
def state335 : List W := [val94, val76, val61, val13, val28, val125, val41, val99]
def state336 : List W := [val0, val99, val61, val13, val28, val125, val41, val76]
def state337 : List W := [val117, val99, val61, val13, val28, val125, val41, val76]
def state338 : List W := [val47, val61, val57, val28, val125, val76, val99]
def state339 : List W := [val47, val13, val61, val57, val28, val125, val76, val99]
def state340 : List W := [val47, val41, val61, val57, val28, val125, val76, val99]
def state341 : List W := [val82, val61, val57, val28, val125, val41, val99]
def state342 : List W := [val82, val13, val61, val57, val28, val125, val41, val99]
def state343 : List W := [val82, val76, val61, val57, val28, val125, val41, val99]
def state344 : List W := [val53, val61, val57, val13, val125, val76, val99]
def state345 : List W := [val53, val28, val61, val57, val13, val125, val76, val99]
def state346 : List W := [val53, val41, val61, val57, val13, val125, val76, val99]
def state347 : List W := [val107, val61, val57, val13, val125, val41, val76]
def state348 : List W := [val107, val28, val61, val57, val13, val125, val41, val76]
def state349 : List W := [val107, val99, val61, val57, val13, val125, val41, val76]
def state350 : List W := [val36, val41, val61, val57, val13, val28, val76, val99]
def state351 : List W := [val141, val76, val61, val57, val13, val28, val41, val99]
def state352 : List W := [val147, val99, val61, val57, val13, val28, val41, val76]
def state353 : List W := [val61, val5, val57, val13, val28, val125, val41, val76, val99]
def state354 : List W := [val3, val5, val76, val13, val28, val125, val41, val57, val99]
def state355 : List W := [val15, val5, val76, val28, val125, val41, val57, val99]
def state356 : List W := [val30, val5, val76, val13, val125, val41, val57, val99]
def state357 : List W := [val127, val5, val76, val13, val28, val41, val57, val99]
def state358 : List W := [val42, val5, val76, val13, val28, val125, val57, val99]
def state359 : List W := [val59, val5, val76, val13, val28, val125, val41, val99]
def state360 : List W := [val101, val5, val76, val13, val28, val125, val41, val57]
def state361 : List W := [val79, val3, val13, val28, val125, val41, val57, val99]
def state362 : List W := [val61, val3, val76, val13, val28, val125, val41, val99]
def state363 : List W := [val82, val3, val5, val28, val125, val41, val57, val99]
def state364 : List W := [val141, val3, val5, val13, val28, val41, val57, val99]
def state365 : List W := [val47, val3, val5, val76, val28, val125, val57, val99]
def state366 : List W := [val53, val3, val5, val76, val13, val125, val57, val99]
def state367 : List W := [val107, val3, val5, val76, val13, val125, val41, val57]
def state368 : List W := [val136, val3, val5, val76, val13, val28, val41, val99]
def state369 : List W := [val147, val3, val5, val76, val13, val28, val41, val57]
def state370 : List W := [val79, val5, val76, val13, val28, val125, val41, val57, val99]
def state371 : List W := [val4, val5, val99, val13, val28, val125, val41, val57, val76]
def state372 : List W := [val16, val5, val99, val28, val125, val41, val57, val76]
def state373 : List W := [val31, val5, val99, val13, val125, val41, val57, val76]
def state374 : List W := [val128, val5, val99, val13, val28, val41, val57, val76]
def state375 : List W := [val43, val5, val99, val13, val28, val125, val57, val76]
def state376 : List W := [val60, val5, val99, val13, val28, val125, val41, val76]
def state377 : List W := [val78, val5, val99, val13, val28, val125, val41, val57]
def state378 : List W := [val102, val4, val13, val28, val125, val41, val57, val76]
def state379 : List W := [val61, val4, val99, val13, val28, val125, val41, val76]
def state380 : List W := [val107, val4, val5, val13, val125, val41, val57, val76]
def state381 : List W := [val147, val4, val5, val13, val28, val41, val57, val76]
def state382 : List W := [val47, val4, val5, val99, val28, val125, val57, val76]
def state383 : List W := [val82, val4, val5, val99, val28, val125, val41, val57]
def state384 : List W := [val53, val4, val5, val99, val13, val125, val57, val76]
def state385 : List W := [val136, val4, val5, val99, val13, val28, val41, val76]
def state386 : List W := [val141, val4, val5, val99, val13, val28, val41, val57]
def state387 : List W := [val102, val5, val99, val13, val28, val125, val41, val57, val76]
def state388 : List W := [val0, val13, val28, val5, val125, val41, val57, val76, val99]
def state389 : List W := [val35, val13, val28, val5, val125, val41, val57, val76, val99]
def state390 : List W := [val0, val13, val125, val5, val28, val41, val57, val76, val99]
def state391 : List W := [val132, val13, val125, val5, val28, val41, val57, val76, val99]
def state392 : List W := [val6, val13, val41, val5, val28, val125, val57, val76, val99]
def state393 : List W := [val47, val5, val28, val125, val57, val76, val99]
def state394 : List W := [val1, val47, val5, val28, val125, val57, val76, val99]
def state395 : List W := [val48, val47, val5, val28, val125, val57, val76, val99]
def state396 : List W := [val18, val47, val28, val5, val125, val57, val76, val99]
def state397 : List W := [val55, val47, val28, val5, val125, val57, val76, val99]
def state398 : List W := [val36, val47, val5, val28, val57, val76, val99]
def state399 : List W := [val36, val47, val125, val5, val28, val57, val76, val99]
def state400 : List W := [val134, val47, val125, val5, val28, val57, val76, val99]
def state401 : List W := [val7, val47, val57, val5, val28, val125, val76, val99]
def state402 : List W := [val73, val47, val57, val5, val28, val125, val76, val99]
def state403 : List W := [val10, val47, val76, val5, val28, val125, val57, val99]
def state404 : List W := [val92, val47, val76, val5, val28, val125, val57, val99]
def state405 : List W := [val11, val47, val99, val5, val28, val125, val57, val76]
def state406 : List W := [val114, val47, val99, val5, val28, val125, val57, val76]
def state407 : List W := [val0, val5, val28, val47, val125, val57, val76, val99]
def state408 : List W := [val32, val5, val28, val47, val125, val57, val76, val99]
def state409 : List W := [val0, val5, val125, val47, val28, val57, val76, val99]
def state410 : List W := [val129, val5, val47, val28, val57, val76, val99]
def state411 : List W := [val129, val5, val125, val47, val28, val57, val76, val99]
def state412 : List W := [val2, val5, val57, val47, val28, val125, val76, val99]
def state413 : List W := [val61, val47, val28, val125, val76, val99]
def state414 : List W := [val61, val5, val47, val28, val125, val76, val99]
def state415 : List W := [val61, val57, val47, val28, val125, val76, val99]
def state416 : List W := [val61, val5, val57, val47, val28, val125, val76, val99]
def state417 : List W := [val3, val5, val76, val47, val28, val125, val57, val99]
def state418 : List W := [val79, val5, val76, val47, val28, val125, val57, val99]
def state419 : List W := [val4, val5, val99, val47, val28, val125, val57, val76]
def state420 : List W := [val102, val5, val99, val47, val28, val125, val57, val76]
def state421 : List W := [val0, val28, val125, val47, val5, val57, val76, val99]
def state422 : List W := [val154, val28, val125, val47, val5, val57, val76, val99]
def state423 : List W := [val19, val28, val57, val47, val5, val125, val76, val99]
def state424 : List W := [val66, val28, val57, val47, val5, val125, val76, val99]
def state425 : List W := [val23, val28, val76, val47, val5, val125, val57, val99]
def state426 : List W := [val85, val28, val76, val47, val5, val125, val57, val99]
def state427 : List W := [val27, val28, val99, val47, val5, val125, val57, val76]
def state428 : List W := [val107, val99, val47, val5, val125, val57, val76]
def state429 : List W := [val107, val28, val99, val47, val5, val125, val57, val76]
def state430 : List W := [val56, val125, val57, val47, val5, val28, val76, val99]
def state431 : List W := [val136, val47, val5, val28, val76, val99]
def state432 : List W := [val136, val125, val47, val5, val28, val76, val99]
def state433 : List W := [val136, val57, val47, val5, val28, val76, val99]
def state434 : List W := [val136, val125, val57, val47, val5, val28, val76, val99]
def state435 : List W := [val75, val125, val76, val47, val5, val28, val57, val99]
def state436 : List W := [val141, val125, val47, val5, val28, val57, val99]
def state437 : List W := [val141, val125, val76, val47, val5, val28, val57, val99]
def state438 : List W := [val98, val125, val99, val47, val5, val28, val57, val76]
def state439 : List W := [val147, val47, val5, val28, val57, val76]
def state440 : List W := [val147, val125, val47, val5, val28, val57, val76]
def state441 : List W := [val147, val99, val47, val5, val28, val57, val76]
def state442 : List W := [val147, val125, val99, val47, val5, val28, val57, val76]
def state443 : List W := [val0, val57, val76, val47, val5, val28, val125, val99]
def state444 : List W := [val94, val57, val76, val47, val5, val28, val125, val99]
def state445 : List W := [val0, val57, val99, val47, val5, val28, val125, val76]
def state446 : List W := [val117, val57, val99, val47, val5, val28, val125, val76]
def state447 : List W := [val0, val76, val99, val47, val5, val28, val125, val57]
def state448 : List W := [val121, val76, val99, val47, val5, val28, val125, val57]
def state449 : List W := [val47, val13, val5, val28, val125, val57, val76, val99]
def state450 : List W := [val55, val28, val13, val5, val125, val57, val76, val99]
def state451 : List W := [val36, val47, val13, val5, val28, val57, val76, val99]
def state452 : List W := [val0, val5, val47, val28, val125, val57, val76, val99]
def state453 : List W := [val17, val5, val47, val28, val125, val57, val76, val99]
def state454 : List W := [val0, val28, val47, val5, val125, val57, val76, val99]
def state455 : List W := [val35, val28, val47, val5, val125, val57, val76, val99]
def state456 : List W := [val0, val125, val47, val5, val28, val57, val76, val99]
def state457 : List W := [val132, val125, val47, val5, val28, val57, val76, val99]
def state458 : List W := [val7, val57, val47, val5, val28, val125, val76, val99]
def state459 : List W := [val63, val57, val47, val5, val28, val125, val76, val99]
def state460 : List W := [val10, val76, val47, val5, val28, val125, val57, val99]
def state461 : List W := [val82, val47, val5, val28, val125, val57, val99]
def state462 : List W := [val82, val13, val47, val5, val28, val125, val57, val99]
def state463 : List W := [val82, val76, val47, val5, val28, val125, val57, val99]
def state464 : List W := [val11, val99, val47, val5, val28, val125, val57, val76]
def state465 : List W := [val104, val99, val47, val5, val28, val125, val57, val76]
def state466 : List W := [val129, val5, val47, val13, val28, val57, val76, val99]
def state467 : List W := [val61, val47, val13, val28, val125, val76, val99]
def state468 : List W := [val61, val5, val47, val13, val28, val125, val76, val99]
def state469 : List W := [val61, val57, val47, val13, val28, val125, val76, val99]
def state470 : List W := [val107, val47, val13, val5, val125, val57, val76]
def state471 : List W := [val107, val28, val47, val13, val5, val125, val57, val76]
def state472 : List W := [val107, val99, val47, val13, val5, val125, val57, val76]
def state473 : List W := [val136, val47, val13, val5, val28, val76, val99]
def state474 : List W := [val136, val125, val47, val13, val5, val28, val76, val99]
def state475 : List W := [val136, val57, val47, val13, val5, val28, val76, val99]
def state476 : List W := [val141, val125, val47, val13, val5, val28, val57, val99]
def state477 : List W := [val147, val47, val13, val5, val28, val57, val76]
def state478 : List W := [val147, val125, val47, val13, val5, val28, val57, val76]
def state479 : List W := [val147, val99, val47, val13, val5, val28, val57, val76]
def state480 : List W := [val47, val41, val5, val28, val125, val57, val76, val99]
def state481 : List W := [val36, val47, val41, val5, val28, val57, val76, val99]
def state482 : List W := [val92, val76, val41, val5, val28, val125, val57, val99]
def state483 : List W := [val1, val5, val47, val28, val125, val57, val76, val99]
def state484 : List W := [val44, val5, val47, val28, val125, val57, val76, val99]
def state485 : List W := [val18, val28, val47, val5, val125, val57, val76, val99]
def state486 : List W := [val53, val47, val5, val125, val57, val76, val99]
def state487 : List W := [val53, val41, val47, val5, val125, val57, val76, val99]
def state488 : List W := [val53, val28, val47, val5, val125, val57, val76, val99]
def state489 : List W := [val36, val41, val47, val5, val28, val57, val76, val99]
def state490 : List W := [val36, val125, val47, val5, val28, val57, val76, val99]
def state491 : List W := [val133, val125, val47, val5, val28, val57, val76, val99]
def state492 : List W := [val0, val57, val47, val5, val28, val125, val76, val99]
def state493 : List W := [val71, val57, val47, val5, val28, val125, val76, val99]
def state494 : List W := [val0, val76, val47, val5, val28, val125, val57, val99]
def state495 : List W := [val91, val76, val47, val5, val28, val125, val57, val99]
def state496 : List W := [val0, val99, val47, val5, val28, val125, val57, val76]
def state497 : List W := [val113, val99, val47, val5, val28, val125, val57, val76]
def state498 : List W := [val129, val5, val47, val41, val28, val57, val76, val99]
def state499 : List W := [val61, val47, val41, val28, val125, val76, val99]
def state500 : List W := [val61, val5, val47, val41, val28, val125, val76, val99]
def state501 : List W := [val61, val57, val47, val41, val28, val125, val76, val99]
def state502 : List W := [val107, val99, val47, val41, val5, val125, val57, val76]
def state503 : List W := [val136, val47, val41, val5, val28, val76, val99]
def state504 : List W := [val136, val125, val47, val41, val5, val28, val76, val99]
def state505 : List W := [val136, val57, val47, val41, val5, val28, val76, val99]
def state506 : List W := [val141, val47, val41, val5, val28, val57, val99]
def state507 : List W := [val141, val125, val47, val41, val5, val28, val57, val99]
def state508 : List W := [val141, val76, val47, val41, val5, val28, val57, val99]
def state509 : List W := [val147, val47, val41, val5, val28, val57, val76]
def state510 : List W := [val147, val125, val47, val41, val5, val28, val57, val76]
def state511 : List W := [val147, val99, val47, val41, val5, val28, val57, val76]
def state512 : List W := [val47, val13, val41, val5, val28, val125, val57, val76, val99]
def state513 : List W := [val36, val13, val41, val5, val28, val57, val76, val99]
def state514 : List W := [val6, val47, val5, val28, val125, val57, val76, val99]
def state515 : List W := [val82, val47, val41, val5, val28, val125, val57, val99]
def state516 : List W := [val53, val47, val13, val5, val125, val57, val76, val99]
def state517 : List W := [val61, val47, val13, val41, val28, val125, val76, val99]
def state518 : List W := [val107, val47, val13, val41, val5, val125, val57, val76]
def state519 : List W := [val136, val47, val13, val41, val5, val28, val76, val99]
def state520 : List W := [val141, val47, val13, val41, val5, val28, val57, val99]
def state521 : List W := [val147, val47, val13, val41, val5, val28, val57, val76]
def state522 : List W := [val7, val13, val57, val5, val28, val125, val41, val76, val99]
def state523 : List W := [val9, val13, val57, val28, val125, val41, val76, val99]
def state524 : List W := [val33, val13, val57, val5, val125, val41, val76, val99]
def state525 : List W := [val130, val13, val57, val5, val28, val41, val76, val99]
def state526 : List W := [val45, val13, val57, val5, val28, val125, val76, val99]
def state527 : List W := [val80, val13, val57, val5, val28, val125, val41, val99]
def state528 : List W := [val103, val13, val57, val5, val28, val125, val41, val76]
def state529 : List W := [val63, val7, val5, val28, val125, val41, val76, val99]
def state530 : List W := [val47, val7, val57, val5, val28, val125, val76, val99]
def state531 : List W := [val82, val7, val57, val5, val28, val125, val41, val99]
def state532 : List W := [val61, val7, val13, val28, val125, val41, val76, val99]
def state533 : List W := [val136, val7, val13, val5, val28, val41, val76, val99]
def state534 : List W := [val53, val7, val13, val57, val5, val125, val76, val99]
def state535 : List W := [val107, val7, val13, val57, val5, val125, val41, val76]
def state536 : List W := [val141, val7, val13, val57, val5, val28, val41, val99]
def state537 : List W := [val147, val7, val13, val57, val5, val28, val41, val76]
def state538 : List W := [val63, val13, val57, val5, val28, val125, val41, val76, val99]
def state539 : List W := [val10, val13, val76, val5, val28, val125, val41, val57, val99]
def state540 : List W := [val82, val5, val28, val125, val41, val57, val99]
def state541 : List W := [val3, val82, val5, val28, val125, val41, val57, val99]
def state542 : List W := [val83, val82, val5, val28, val125, val41, val57, val99]
def state543 : List W := [val23, val82, val28, val5, val125, val41, val57, val99]
def state544 : List W := [val86, val82, val28, val5, val125, val41, val57, val99]
def state545 : List W := [val75, val82, val125, val5, val28, val41, val57, val99]
def state546 : List W := [val143, val82, val125, val5, val28, val41, val57, val99]
def state547 : List W := [val6, val82, val41, val5, val28, val125, val57, val99]
def state548 : List W := [val92, val82, val41, val5, val28, val125, val57, val99]
def state549 : List W := [val7, val82, val57, val5, val28, val125, val41, val99]
def state550 : List W := [val96, val82, val57, val5, val28, val125, val41, val99]
def state551 : List W := [val11, val82, val99, val5, val28, val125, val41, val57]
def state552 : List W := [val122, val82, val99, val5, val28, val125, val41, val57]
def state553 : List W := [val0, val5, val28, val82, val125, val41, val57, val99]
def state554 : List W := [val32, val5, val28, val82, val125, val41, val57, val99]
def state555 : List W := [val0, val5, val125, val82, val28, val41, val57, val99]
def state556 : List W := [val129, val5, val82, val28, val41, val57, val99]
def state557 : List W := [val129, val5, val125, val82, val28, val41, val57, val99]
def state558 : List W := [val1, val5, val41, val82, val28, val125, val57, val99]
def state559 : List W := [val44, val5, val41, val82, val28, val125, val57, val99]
def state560 : List W := [val2, val5, val57, val82, val28, val125, val41, val99]
def state561 : List W := [val61, val82, val28, val125, val41, val99]
def state562 : List W := [val8, val61, val82, val28, val125, val41, val99]
def state563 : List W := [val97, val61, val82, val28, val125, val41, val99]
def state564 : List W := [val0, val28, val125, val61, val82, val41, val99]
def state565 : List W := [val154, val28, val125, val61, val82, val41, val99]
def state566 : List W := [val18, val28, val41, val61, val82, val125, val99]
def state567 : List W := [val53, val28, val61, val82, val125, val99]
def state568 : List W := [val53, val28, val41, val61, val82, val125, val99]
def state569 : List W := [val27, val28, val99, val61, val82, val125, val41]
def state570 : List W := [val107, val61, val82, val125, val41]
def state571 : List W := [val107, val28, val61, val82, val125, val41]
def state572 : List W := [val107, val99, val61, val82, val125, val41]
def state573 : List W := [val107, val28, val99, val61, val82, val125, val41]
def state574 : List W := [val36, val41, val61, val82, val28, val99]
def state575 : List W := [val36, val125, val41, val61, val82, val28, val99]
def state576 : List W := [val133, val125, val41, val61, val82, val28, val99]
def state577 : List W := [val98, val125, val99, val61, val82, val28, val41]
def state578 : List W := [val147, val99, val61, val82, val28, val41]
def state579 : List W := [val147, val125, val99, val61, val82, val28, val41]
def state580 : List W := [val0, val41, val99, val61, val82, val28, val125]
def state581 : List W := [val113, val41, val99, val61, val82, val28, val125]
def state582 : List W := [val61, val5, val82, val28, val125, val41, val99]
def state583 : List W := [val61, val57, val82, val28, val125, val41, val99]
def state584 : List W := [val61, val5, val57, val82, val28, val125, val41, val99]
def state585 : List W := [val4, val5, val99, val82, val28, val125, val41, val57]
def state586 : List W := [val102, val5, val99, val82, val28, val125, val41, val57]
def state587 : List W := [val0, val28, val125, val82, val5, val41, val57, val99]
def state588 : List W := [val154, val28, val125, val82, val5, val41, val57, val99]
def state589 : List W := [val18, val28, val41, val82, val5, val125, val57, val99]
def state590 : List W := [val53, val28, val82, val5, val125, val57, val99]
def state591 : List W := [val53, val28, val41, val82, val5, val125, val57, val99]
def state592 : List W := [val19, val28, val57, val82, val5, val125, val41, val99]
def state593 : List W := [val66, val28, val57, val82, val5, val125, val41, val99]
def state594 : List W := [val27, val28, val99, val82, val5, val125, val41, val57]
def state595 : List W := [val107, val82, val5, val125, val41, val57]
def state596 : List W := [val25, val107, val82, val5, val125, val41, val57]
def state597 : List W := [val124, val107, val82, val5, val125, val41, val57]
def state598 : List W := [val4, val107, val5, val82, val125, val41, val57]
def state599 : List W := [val108, val107, val5, val82, val125, val41, val57]
def state600 : List W := [val98, val107, val125, val82, val5, val41, val57]
def state601 : List W := [val158, val107, val125, val82, val5, val41, val57]
def state602 : List W := [val18, val107, val41, val82, val5, val125, val57]
def state603 : List W := [val116, val107, val41, val82, val5, val125, val57]
def state604 : List W := [val19, val107, val57, val82, val5, val125, val41]
def state605 : List W := [val119, val107, val57, val82, val5, val125, val41]
def state606 : List W := [val3, val82, val5, val107, val125, val41, val57]
def state607 : List W := [val83, val82, val5, val107, val125, val41, val57]
def state608 : List W := [val75, val82, val125, val107, val5, val41, val57]
def state609 : List W := [val143, val82, val125, val107, val5, val41, val57]
def state610 : List W := [val6, val82, val41, val107, val5, val125, val57]
def state611 : List W := [val92, val82, val41, val107, val5, val125, val57]
def state612 : List W := [val7, val82, val57, val107, val5, val125, val41]
def state613 : List W := [val96, val82, val57, val107, val5, val125, val41]
def state614 : List W := [val0, val5, val125, val107, val82, val41, val57]
def state615 : List W := [val129, val5, val107, val82, val41, val57]
def state616 : List W := [val129, val5, val125, val107, val82, val41, val57]
def state617 : List W := [val1, val5, val41, val107, val82, val125, val57]
def state618 : List W := [val44, val5, val41, val107, val82, val125, val57]
def state619 : List W := [val2, val5, val57, val107, val82, val125, val41]
def state620 : List W := [val61, val107, val82, val125, val41]
def state621 : List W := [val61, val5, val107, val82, val125, val41]
def state622 : List W := [val61, val57, val107, val82, val125, val41]
def state623 : List W := [val61, val5, val57, val107, val82, val125, val41]
def state624 : List W := [val36, val41, val107, val82, val5, val57]
def state625 : List W := [val36, val125, val41, val107, val82, val5, val57]
def state626 : List W := [val133, val125, val41, val107, val82, val5, val57]
def state627 : List W := [val56, val125, val57, val107, val82, val5, val41]
def state628 : List W := [val136, val57, val107, val82, val5, val41]
def state629 : List W := [val136, val125, val57, val107, val82, val5, val41]
def state630 : List W := [val0, val41, val57, val107, val82, val5, val125]
def state631 : List W := [val71, val41, val57, val107, val82, val5, val125]
def state632 : List W := [val107, val28, val82, val5, val125, val41, val57]
def state633 : List W := [val107, val99, val82, val5, val125, val41, val57]
def state634 : List W := [val107, val28, val99, val82, val5, val125, val41, val57]
def state635 : List W := [val36, val41, val82, val5, val28, val57, val99]
def state636 : List W := [val90, val36, val41, val5, val28, val57, val99]
def state637 : List W := [val38, val41, val82, val28, val57, val99]
def state638 : List W := [val38, val36, val41, val82, val28, val57, val99]
def state639 : List W := [val38, val5, val41, val82, val28, val57, val99]
def state640 : List W := [val51, val36, val41, val82, val5, val57, val99]
def state641 : List W := [val68, val41, val82, val5, val28, val99]
def state642 : List W := [val68, val36, val41, val82, val5, val28, val99]
def state643 : List W := [val68, val57, val41, val82, val5, val28, val99]
def state644 : List W := [val111, val41, val82, val5, val28, val57]
def state645 : List W := [val111, val36, val41, val82, val5, val28, val57]
def state646 : List W := [val111, val99, val41, val82, val5, val28, val57]
def state647 : List W := [val92, val82, val36, val5, val28, val57, val99]
def state648 : List W := [val1, val5, val36, val82, val28, val57, val99]
def state649 : List W := [val53, val28, val36, val82, val5, val57, val99]
def state650 : List W := [val113, val99, val36, val82, val5, val28, val57]
def state651 : List W := [val61, val36, val41, val82, val28, val99]
def state652 : List W := [val61, val5, val36, val41, val82, val28, val99]
def state653 : List W := [val61, val57, val36, val41, val82, val28, val99]
def state654 : List W := [val107, val36, val41, val82, val5, val57]
def state655 : List W := [val107, val28, val36, val41, val82, val5, val57]
def state656 : List W := [val107, val99, val36, val41, val82, val5, val57]
def state657 : List W := [val36, val125, val41, val82, val5, val28, val57, val99]
def state658 : List W := [val133, val125, val41, val82, val5, val28, val57, val99]
def state659 : List W := [val56, val125, val57, val82, val5, val28, val41, val99]
def state660 : List W := [val136, val57, val82, val5, val28, val41, val99]
def state661 : List W := [val136, val125, val57, val82, val5, val28, val41, val99]
def state662 : List W := [val98, val125, val99, val82, val5, val28, val41, val57]
def state663 : List W := [val147, val99, val82, val5, val28, val41, val57]
def state664 : List W := [val147, val125, val99, val82, val5, val28, val41, val57]
def state665 : List W := [val0, val41, val57, val82, val5, val28, val125, val99]
def state666 : List W := [val71, val41, val57, val82, val5, val28, val125, val99]
def state667 : List W := [val0, val41, val99, val82, val5, val28, val125, val57]
def state668 : List W := [val113, val41, val99, val82, val5, val28, val125, val57]
def state669 : List W := [val0, val57, val99, val82, val5, val28, val125, val41]
def state670 : List W := [val117, val57, val99, val82, val5, val28, val125, val41]
def state671 : List W := [val82, val13, val5, val28, val125, val41, val57, val99]
def state672 : List W := [val143, val125, val13, val5, val28, val41, val57, val99]
def state673 : List W := [val0, val5, val82, val28, val125, val41, val57, val99]
def state674 : List W := [val17, val5, val82, val28, val125, val41, val57, val99]
def state675 : List W := [val0, val28, val82, val5, val125, val41, val57, val99]
def state676 : List W := [val35, val28, val82, val5, val125, val41, val57, val99]
def state677 : List W := [val0, val125, val82, val5, val28, val41, val57, val99]
def state678 : List W := [val132, val125, val82, val5, val28, val41, val57, val99]
def state679 : List W := [val6, val41, val82, val5, val28, val125, val57, val99]
def state680 : List W := [val47, val82, val5, val28, val125, val57, val99]
def state681 : List W := [val47, val13, val82, val5, val28, val125, val57, val99]
def state682 : List W := [val47, val41, val82, val5, val28, val125, val57, val99]
def state683 : List W := [val7, val57, val82, val5, val28, val125, val41, val99]
def state684 : List W := [val63, val57, val82, val5, val28, val125, val41, val99]
def state685 : List W := [val11, val99, val82, val5, val28, val125, val41, val57]
def state686 : List W := [val104, val99, val82, val5, val28, val125, val41, val57]
def state687 : List W := [val129, val5, val82, val13, val28, val41, val57, val99]
def state688 : List W := [val61, val82, val13, val28, val125, val41, val99]
def state689 : List W := [val61, val5, val82, val13, val28, val125, val41, val99]
def state690 : List W := [val61, val57, val82, val13, val28, val125, val41, val99]
def state691 : List W := [val53, val28, val82, val13, val5, val125, val57, val99]
def state692 : List W := [val107, val82, val13, val5, val125, val41, val57]
def state693 : List W := [val107, val28, val82, val13, val5, val125, val41, val57]
def state694 : List W := [val107, val99, val82, val13, val5, val125, val41, val57]
def state695 : List W := [val36, val41, val82, val13, val5, val28, val57, val99]
def state696 : List W := [val136, val82, val13, val5, val28, val41, val99]
def state697 : List W := [val136, val125, val82, val13, val5, val28, val41, val99]
def state698 : List W := [val136, val57, val82, val13, val5, val28, val41, val99]
def state699 : List W := [val147, val82, val13, val5, val28, val41, val57]
def state700 : List W := [val147, val125, val82, val13, val5, val28, val41, val57]
def state701 : List W := [val147, val99, val82, val13, val5, val28, val41, val57]
def state702 : List W := [val82, val76, val5, val28, val125, val41, val57, val99]
def state703 : List W := [val92, val41, val76, val5, val28, val125, val57, val99]
def state704 : List W := [val3, val5, val82, val28, val125, val41, val57, val99]
def state705 : List W := [val79, val5, val82, val28, val125, val41, val57, val99]
def state706 : List W := [val23, val28, val82, val5, val125, val41, val57, val99]
def state707 : List W := [val85, val28, val82, val5, val125, val41, val57, val99]
def state708 : List W := [val75, val125, val82, val5, val28, val41, val57, val99]
def state709 : List W := [val141, val82, val5, val28, val41, val57, val99]
def state710 : List W := [val141, val76, val82, val5, val28, val41, val57, val99]
def state711 : List W := [val141, val125, val82, val5, val28, val41, val57, val99]
def state712 : List W := [val0, val41, val82, val5, val28, val125, val57, val99]
def state713 : List W := [val91, val41, val82, val5, val28, val125, val57, val99]
def state714 : List W := [val0, val57, val82, val5, val28, val125, val41, val99]
def state715 : List W := [val94, val57, val82, val5, val28, val125, val41, val99]
def state716 : List W := [val0, val99, val82, val5, val28, val125, val41, val57]
def state717 : List W := [val121, val99, val82, val5, val28, val125, val41, val57]
def state718 : List W := [val129, val5, val82, val76, val28, val41, val57, val99]
def state719 : List W := [val61, val82, val76, val28, val125, val41, val99]
def state720 : List W := [val61, val5, val82, val76, val28, val125, val41, val99]
def state721 : List W := [val61, val57, val82, val76, val28, val125, val41, val99]
def state722 : List W := [val53, val82, val76, val5, val125, val57, val99]
def state723 : List W := [val53, val28, val82, val76, val5, val125, val57, val99]
def state724 : List W := [val53, val41, val82, val76, val5, val125, val57, val99]
def state725 : List W := [val107, val82, val76, val5, val125, val41, val57]
def state726 : List W := [val107, val28, val82, val76, val5, val125, val41, val57]
def state727 : List W := [val107, val99, val82, val76, val5, val125, val41, val57]
def state728 : List W := [val36, val41, val82, val76, val5, val28, val57, val99]
def state729 : List W := [val136, val57, val82, val76, val5, val28, val41, val99]
def state730 : List W := [val147, val99, val82, val76, val5, val28, val41, val57]
def state731 : List W := [val82, val13, val76, val5, val28, val125, val41, val57, val99]
def state732 : List W := [val11, val13, val99, val5, val28, val125, val41, val57, val76]
def state733 : List W := [val12, val13, val99, val28, val125, val41, val57, val76]
def state734 : List W := [val34, val13, val99, val5, val125, val41, val57, val76]
def state735 : List W := [val131, val13, val99, val5, val28, val41, val57, val76]
def state736 : List W := [val46, val13, val99, val5, val28, val125, val57, val76]
def state737 : List W := [val62, val13, val99, val5, val28, val125, val41, val76]
def state738 : List W := [val81, val13, val99, val5, val28, val125, val41, val57]
def state739 : List W := [val104, val11, val5, val28, val125, val41, val57, val76]
def state740 : List W := [val47, val11, val99, val5, val28, val125, val57, val76]
def state741 : List W := [val82, val11, val99, val5, val28, val125, val41, val57]
def state742 : List W := [val107, val11, val13, val5, val125, val41, val57, val76]
def state743 : List W := [val147, val11, val13, val5, val28, val41, val57, val76]
def state744 : List W := [val61, val11, val13, val99, val28, val125, val41, val76]
def state745 : List W := [val53, val11, val13, val99, val5, val125, val57, val76]
def state746 : List W := [val136, val11, val13, val99, val5, val28, val41, val76]
def state747 : List W := [val141, val11, val13, val99, val5, val28, val41, val57]
def state748 : List W := [val104, val13, val99, val5, val28, val125, val41, val57, val76]
def state749 : List W := [val0, val28, val125, val5, val13, val41, val57, val76, val99]
def state750 : List W := [val154, val28, val125, val5, val13, val41, val57, val76, val99]
def state751 : List W := [val18, val28, val41, val5, val13, val125, val57, val76, val99]
def state752 : List W := [val53, val5, val13, val125, val57, val76, val99]
def state753 : List W := [val1, val53, val5, val13, val125, val57, val76, val99]
def state754 : List W := [val54, val53, val5, val13, val125, val57, val76, val99]
def state755 : List W := [val6, val53, val13, val5, val125, val57, val76, val99]
def state756 : List W := [val55, val53, val13, val5, val125, val57, val76, val99]
def state757 : List W := [val36, val53, val5, val13, val57, val76, val99]
def state758 : List W := [val36, val53, val125, val5, val13, val57, val76, val99]
def state759 : List W := [val155, val53, val125, val5, val13, val57, val76, val99]
def state760 : List W := [val19, val53, val57, val5, val13, val125, val76, val99]
def state761 : List W := [val74, val53, val57, val5, val13, val125, val76, val99]
def state762 : List W := [val23, val53, val76, val5, val13, val125, val57, val99]
def state763 : List W := [val93, val53, val76, val5, val13, val125, val57, val99]
def state764 : List W := [val27, val53, val99, val5, val13, val125, val57, val76]
def state765 : List W := [val116, val53, val99, val5, val13, val125, val57, val76]
def state766 : List W := [val0, val5, val13, val53, val125, val57, val76, val99]
def state767 : List W := [val17, val5, val13, val53, val125, val57, val76, val99]
def state768 : List W := [val0, val5, val125, val53, val13, val57, val76, val99]
def state769 : List W := [val129, val5, val53, val13, val57, val76, val99]
def state770 : List W := [val129, val5, val125, val53, val13, val57, val76, val99]
def state771 : List W := [val2, val5, val57, val53, val13, val125, val76, val99]
def state772 : List W := [val61, val53, val13, val125, val76, val99]
def state773 : List W := [val61, val5, val53, val13, val125, val76, val99]
def state774 : List W := [val61, val57, val53, val13, val125, val76, val99]
def state775 : List W := [val61, val5, val57, val53, val13, val125, val76, val99]
def state776 : List W := [val3, val5, val76, val53, val13, val125, val57, val99]
def state777 : List W := [val79, val5, val76, val53, val13, val125, val57, val99]
def state778 : List W := [val4, val5, val99, val53, val13, val125, val57, val76]
def state779 : List W := [val102, val5, val99, val53, val13, val125, val57, val76]
def state780 : List W := [val0, val13, val125, val53, val5, val57, val76, val99]
def state781 : List W := [val132, val13, val125, val53, val5, val57, val76, val99]
def state782 : List W := [val7, val13, val57, val53, val5, val125, val76, val99]
def state783 : List W := [val63, val13, val57, val53, val5, val125, val76, val99]
def state784 : List W := [val10, val13, val76, val53, val5, val125, val57, val99]
def state785 : List W := [val82, val76, val53, val5, val125, val57, val99]
def state786 : List W := [val82, val13, val76, val53, val5, val125, val57, val99]
def state787 : List W := [val11, val13, val99, val53, val5, val125, val57, val76]
def state788 : List W := [val104, val13, val99, val53, val5, val125, val57, val76]
def state789 : List W := [val56, val125, val57, val53, val5, val13, val76, val99]
def state790 : List W := [val136, val53, val5, val13, val76, val99]
def state791 : List W := [val136, val125, val53, val5, val13, val76, val99]
def state792 : List W := [val136, val57, val53, val5, val13, val76, val99]
def state793 : List W := [val136, val125, val57, val53, val5, val13, val76, val99]
def state794 : List W := [val75, val125, val76, val53, val5, val13, val57, val99]
def state795 : List W := [val141, val53, val5, val13, val57, val99]
def state796 : List W := [val141, val125, val53, val5, val13, val57, val99]
def state797 : List W := [val141, val76, val53, val5, val13, val57, val99]
def state798 : List W := [val141, val125, val76, val53, val5, val13, val57, val99]
def state799 : List W := [val98, val125, val99, val53, val5, val13, val57, val76]
def state800 : List W := [val147, val125, val53, val5, val13, val57, val76]
def state801 : List W := [val147, val125, val99, val53, val5, val13, val57, val76]
def state802 : List W := [val0, val57, val76, val53, val5, val13, val125, val99]
def state803 : List W := [val94, val57, val76, val53, val5, val13, val125, val99]
def state804 : List W := [val0, val57, val99, val53, val5, val13, val125, val76]
def state805 : List W := [val117, val57, val99, val53, val5, val13, val125, val76]
def state806 : List W := [val0, val76, val99, val53, val5, val13, val125, val57]
def state807 : List W := [val121, val76, val99, val53, val5, val13, val125, val57]
def state808 : List W := [val53, val28, val5, val13, val125, val57, val76, val99]
def state809 : List W := [val55, val13, val28, val5, val125, val57, val76, val99]
def state810 : List W := [val36, val53, val28, val5, val13, val57, val76, val99]
def state811 : List W := [val0, val5, val53, val13, val125, val57, val76, val99]
def state812 : List W := [val32, val5, val53, val13, val125, val57, val76, val99]
def state813 : List W := [val0, val13, val53, val5, val125, val57, val76, val99]
def state814 : List W := [val35, val13, val53, val5, val125, val57, val76, val99]
def state815 : List W := [val0, val125, val53, val5, val13, val57, val76, val99]
def state816 : List W := [val154, val125, val53, val5, val13, val57, val76, val99]
def state817 : List W := [val19, val57, val53, val5, val13, val125, val76, val99]
def state818 : List W := [val66, val57, val53, val5, val13, val125, val76, val99]
def state819 : List W := [val23, val76, val53, val5, val13, val125, val57, val99]
def state820 : List W := [val85, val76, val53, val5, val13, val125, val57, val99]
def state821 : List W := [val27, val99, val53, val5, val13, val125, val57, val76]
def state822 : List W := [val107, val53, val5, val13, val125, val57, val76]
def state823 : List W := [val107, val28, val53, val5, val13, val125, val57, val76]
def state824 : List W := [val107, val99, val53, val5, val13, val125, val57, val76]
def state825 : List W := [val129, val5, val53, val28, val13, val57, val76, val99]
def state826 : List W := [val61, val53, val28, val13, val125, val76, val99]
def state827 : List W := [val61, val5, val53, val28, val13, val125, val76, val99]
def state828 : List W := [val61, val57, val53, val28, val13, val125, val76, val99]
def state829 : List W := [val82, val53, val28, val5, val125, val57, val99]
def state830 : List W := [val82, val13, val53, val28, val5, val125, val57, val99]
def state831 : List W := [val82, val76, val53, val28, val5, val125, val57, val99]
def state832 : List W := [val136, val53, val28, val5, val13, val76, val99]
def state833 : List W := [val136, val125, val53, val28, val5, val13, val76, val99]
def state834 : List W := [val136, val57, val53, val28, val5, val13, val76, val99]
def state835 : List W := [val141, val53, val28, val5, val13, val57, val99]
def state836 : List W := [val141, val125, val53, val28, val5, val13, val57, val99]
def state837 : List W := [val141, val76, val53, val28, val5, val13, val57, val99]
def state838 : List W := [val147, val125, val53, val28, val5, val13, val57, val76]
def state839 : List W := [val53, val41, val5, val13, val125, val57, val76, val99]
def state840 : List W := [val36, val53, val41, val5, val13, val57, val76, val99]
def state841 : List W := [val116, val99, val41, val5, val13, val125, val57, val76]
def state842 : List W := [val1, val5, val53, val13, val125, val57, val76, val99]
def state843 : List W := [val44, val5, val53, val13, val125, val57, val76, val99]
def state844 : List W := [val6, val13, val53, val5, val125, val57, val76, val99]
def state845 : List W := [val47, val53, val5, val125, val57, val76, val99]
def state846 : List W := [val47, val41, val53, val5, val125, val57, val76, val99]
def state847 : List W := [val47, val13, val53, val5, val125, val57, val76, val99]
def state848 : List W := [val36, val41, val53, val5, val13, val57, val76, val99]
def state849 : List W := [val36, val125, val53, val5, val13, val57, val76, val99]
def state850 : List W := [val133, val125, val53, val5, val13, val57, val76, val99]
def state851 : List W := [val0, val57, val53, val5, val13, val125, val76, val99]
def state852 : List W := [val71, val57, val53, val5, val13, val125, val76, val99]
def state853 : List W := [val0, val76, val53, val5, val13, val125, val57, val99]
def state854 : List W := [val91, val76, val53, val5, val13, val125, val57, val99]
def state855 : List W := [val0, val99, val53, val5, val13, val125, val57, val76]
def state856 : List W := [val113, val99, val53, val5, val13, val125, val57, val76]
def state857 : List W := [val129, val5, val53, val41, val13, val57, val76, val99]
def state858 : List W := [val61, val53, val41, val13, val125, val76, val99]
def state859 : List W := [val61, val5, val53, val41, val13, val125, val76, val99]
def state860 : List W := [val61, val57, val53, val41, val13, val125, val76, val99]
def state861 : List W := [val82, val76, val53, val41, val5, val125, val57, val99]
def state862 : List W := [val136, val53, val41, val5, val13, val76, val99]
def state863 : List W := [val136, val125, val53, val41, val5, val13, val76, val99]
def state864 : List W := [val136, val57, val53, val41, val5, val13, val76, val99]
def state865 : List W := [val141, val53, val41, val5, val13, val57, val99]
def state866 : List W := [val141, val125, val53, val41, val5, val13, val57, val99]
def state867 : List W := [val141, val76, val53, val41, val5, val13, val57, val99]
def state868 : List W := [val147, val53, val41, val5, val13, val57, val76]
def state869 : List W := [val147, val125, val53, val41, val5, val13, val57, val76]
def state870 : List W := [val147, val99, val53, val41, val5, val13, val57, val76]
def state871 : List W := [val53, val28, val41, val5, val13, val125, val57, val76, val99]
def state872 : List W := [val36, val28, val41, val5, val13, val57, val76, val99]
def state873 : List W := [val18, val53, val5, val13, val125, val57, val76, val99]
def state874 : List W := [val107, val53, val41, val5, val13, val125, val57, val76]
def state875 : List W := [val47, val53, val28, val5, val125, val57, val76, val99]
def state876 : List W := [val61, val53, val28, val41, val13, val125, val76, val99]
def state877 : List W := [val82, val53, val28, val41, val5, val125, val57, val99]
def state878 : List W := [val136, val53, val28, val41, val5, val13, val76, val99]
def state879 : List W := [val141, val53, val28, val41, val5, val13, val57, val99]
def state880 : List W := [val147, val53, val28, val41, val5, val13, val57, val76]
def state881 : List W := [val19, val28, val57, val5, val13, val125, val41, val76, val99]
def state882 : List W := [val21, val28, val57, val13, val125, val41, val76, val99]
def state883 : List W := [val22, val28, val57, val5, val125, val41, val76, val99]
def state884 : List W := [val135, val28, val57, val5, val13, val41, val76, val99]
def state885 : List W := [val49, val28, val57, val5, val13, val125, val76, val99]
def state886 : List W := [val84, val28, val57, val5, val13, val125, val41, val99]
def state887 : List W := [val105, val28, val57, val5, val13, val125, val41, val76]
def state888 : List W := [val66, val19, val5, val13, val125, val41, val76, val99]
def state889 : List W := [val53, val19, val57, val5, val13, val125, val76, val99]
def state890 : List W := [val107, val19, val57, val5, val13, val125, val41, val76]
def state891 : List W := [val61, val19, val28, val13, val125, val41, val76, val99]
def state892 : List W := [val136, val19, val28, val5, val13, val41, val76, val99]
def state893 : List W := [val47, val19, val28, val57, val5, val125, val76, val99]
def state894 : List W := [val82, val19, val28, val57, val5, val125, val41, val99]
def state895 : List W := [val141, val19, val28, val57, val5, val13, val41, val99]
def state896 : List W := [val147, val19, val28, val57, val5, val13, val41, val76]
def state897 : List W := [val66, val28, val57, val5, val13, val125, val41, val76, val99]
def state898 : List W := [val23, val28, val76, val5, val13, val125, val41, val57, val99]
def state899 : List W := [val24, val28, val76, val13, val125, val41, val57, val99]
def state900 : List W := [val26, val28, val76, val5, val125, val41, val57, val99]
def state901 : List W := [val140, val28, val76, val5, val13, val41, val57, val99]
def state902 : List W := [val50, val28, val76, val5, val13, val125, val57, val99]
def state903 : List W := [val65, val28, val76, val5, val13, val125, val41, val99]
def state904 : List W := [val106, val28, val76, val5, val13, val125, val41, val57]
def state905 : List W := [val85, val23, val5, val13, val125, val41, val57, val99]
def state906 : List W := [val53, val23, val76, val5, val13, val125, val57, val99]
def state907 : List W := [val107, val23, val76, val5, val13, val125, val41, val57]
def state908 : List W := [val82, val23, val28, val5, val125, val41, val57, val99]
def state909 : List W := [val141, val23, val28, val5, val13, val41, val57, val99]
def state910 : List W := [val61, val23, val28, val76, val13, val125, val41, val99]
def state911 : List W := [val47, val23, val28, val76, val5, val125, val57, val99]
def state912 : List W := [val136, val23, val28, val76, val5, val13, val41, val99]
def state913 : List W := [val147, val23, val28, val76, val5, val13, val41, val57]
def state914 : List W := [val85, val28, val76, val5, val13, val125, val41, val57, val99]
def state915 : List W := [val27, val28, val99, val5, val13, val125, val41, val57, val76]
def state916 : List W := [val107, val5, val13, val125, val41, val57, val76]
def state917 : List W := [val4, val107, val5, val13, val125, val41, val57, val76]
def state918 : List W := [val108, val107, val5, val13, val125, val41, val57, val76]
def state919 : List W := [val11, val107, val13, val5, val125, val41, val57, val76]
def state920 : List W := [val109, val107, val13, val5, val125, val41, val57, val76]
def state921 : List W := [val98, val107, val125, val5, val13, val41, val57, val76]
def state922 : List W := [val158, val107, val125, val5, val13, val41, val57, val76]
def state923 : List W := [val18, val107, val41, val5, val13, val125, val57, val76]
def state924 : List W := [val116, val107, val41, val5, val13, val125, val57, val76]
def state925 : List W := [val19, val107, val57, val5, val13, val125, val41, val76]
def state926 : List W := [val119, val107, val57, val5, val13, val125, val41, val76]
def state927 : List W := [val23, val107, val76, val5, val13, val125, val41, val57]
def state928 : List W := [val123, val107, val76, val5, val13, val125, val41, val57]
def state929 : List W := [val0, val5, val13, val107, val125, val41, val57, val76]
def state930 : List W := [val17, val5, val13, val107, val125, val41, val57, val76]
def state931 : List W := [val0, val5, val125, val107, val13, val41, val57, val76]
def state932 : List W := [val129, val5, val107, val13, val41, val57, val76]
def state933 : List W := [val129, val5, val125, val107, val13, val41, val57, val76]
def state934 : List W := [val1, val5, val41, val107, val13, val125, val57, val76]
def state935 : List W := [val44, val5, val41, val107, val13, val125, val57, val76]
def state936 : List W := [val2, val5, val57, val107, val13, val125, val41, val76]
def state937 : List W := [val61, val107, val13, val125, val41, val76]
def state938 : List W := [val20, val61, val107, val13, val125, val41, val76]
def state939 : List W := [val120, val61, val107, val13, val125, val41, val76]
def state940 : List W := [val0, val13, val125, val61, val107, val41, val76]
def state941 : List W := [val132, val13, val125, val61, val107, val41, val76]
def state942 : List W := [val6, val13, val41, val61, val107, val125, val76]
def state943 : List W := [val47, val13, val61, val107, val125, val76]
def state944 : List W := [val47, val13, val41, val61, val107, val125, val76]
def state945 : List W := [val10, val13, val76, val61, val107, val125, val41]
def state946 : List W := [val82, val61, val107, val125, val41]
def state947 : List W := [val82, val13, val61, val107, val125, val41]
def state948 : List W := [val82, val76, val61, val107, val125, val41]
def state949 : List W := [val82, val13, val76, val61, val107, val125, val41]
def state950 : List W := [val36, val41, val61, val107, val13, val76]
def state951 : List W := [val36, val125, val41, val61, val107, val13, val76]
def state952 : List W := [val133, val125, val41, val61, val107, val13, val76]
def state953 : List W := [val75, val125, val76, val61, val107, val13, val41]
def state954 : List W := [val141, val76, val61, val107, val13, val41]
def state955 : List W := [val141, val125, val76, val61, val107, val13, val41]
def state956 : List W := [val0, val41, val76, val61, val107, val13, val125]
def state957 : List W := [val91, val41, val76, val61, val107, val13, val125]
def state958 : List W := [val61, val5, val107, val13, val125, val41, val76]
def state959 : List W := [val61, val57, val107, val13, val125, val41, val76]
def state960 : List W := [val61, val5, val57, val107, val13, val125, val41, val76]
def state961 : List W := [val3, val5, val76, val107, val13, val125, val41, val57]
def state962 : List W := [val79, val5, val76, val107, val13, val125, val41, val57]
def state963 : List W := [val0, val13, val125, val107, val5, val41, val57, val76]
def state964 : List W := [val132, val13, val125, val107, val5, val41, val57, val76]
def state965 : List W := [val6, val13, val41, val107, val5, val125, val57, val76]
def state966 : List W := [val47, val13, val107, val5, val125, val57, val76]
def state967 : List W := [val47, val13, val41, val107, val5, val125, val57, val76]
def state968 : List W := [val7, val13, val57, val107, val5, val125, val41, val76]
def state969 : List W := [val63, val13, val57, val107, val5, val125, val41, val76]
def state970 : List W := [val10, val13, val76, val107, val5, val125, val41, val57]
def state971 : List W := [val82, val107, val5, val125, val41, val57]
def state972 : List W := [val25, val82, val107, val5, val125, val41, val57]
def state973 : List W := [val124, val82, val107, val5, val125, val41, val57]
def state974 : List W := [val0, val5, val125, val82, val107, val41, val57]
def state975 : List W := [val129, val5, val82, val107, val41, val57]
def state976 : List W := [val129, val5, val125, val82, val107, val41, val57]
def state977 : List W := [val1, val5, val41, val82, val107, val125, val57]
def state978 : List W := [val44, val5, val41, val82, val107, val125, val57]
def state979 : List W := [val2, val5, val57, val82, val107, val125, val41]
def state980 : List W := [val61, val82, val107, val125, val41]
def state981 : List W := [val61, val5, val82, val107, val125, val41]
def state982 : List W := [val61, val57, val82, val107, val125, val41]
def state983 : List W := [val61, val5, val57, val82, val107, val125, val41]
def state984 : List W := [val36, val41, val82, val107, val5, val57]
def state985 : List W := [val36, val125, val41, val82, val107, val5, val57]
def state986 : List W := [val133, val125, val41, val82, val107, val5, val57]
def state987 : List W := [val56, val125, val57, val82, val107, val5, val41]
def state988 : List W := [val136, val57, val82, val107, val5, val41]
def state989 : List W := [val136, val125, val57, val82, val107, val5, val41]
def state990 : List W := [val0, val41, val57, val82, val107, val5, val125]
def state991 : List W := [val71, val41, val57, val82, val107, val5, val125]
def state992 : List W := [val82, val13, val107, val5, val125, val41, val57]
def state993 : List W := [val82, val76, val107, val5, val125, val41, val57]
def state994 : List W := [val82, val13, val76, val107, val5, val125, val41, val57]
def state995 : List W := [val36, val41, val107, val5, val13, val57, val76]
def state996 : List W := [val115, val36, val41, val5, val13, val57, val76]
def state997 : List W := [val38, val41, val107, val13, val57, val76]
def state998 : List W := [val38, val36, val41, val107, val13, val57, val76]
def state999 : List W := [val38, val5, val41, val107, val13, val57, val76]
def state1000 : List W := [val39, val36, val41, val107, val5, val57, val76]
def state1001 : List W := [val68, val41, val107, val5, val13, val76]
def state1002 : List W := [val68, val36, val41, val107, val5, val13, val76]
def state1003 : List W := [val68, val57, val41, val107, val5, val13, val76]
def state1004 : List W := [val88, val41, val107, val5, val13, val57]
def state1005 : List W := [val88, val36, val41, val107, val5, val13, val57]
def state1006 : List W := [val88, val76, val41, val107, val5, val13, val57]
def state1007 : List W := [val116, val107, val36, val5, val13, val57, val76]
def state1008 : List W := [val1, val5, val36, val107, val13, val57, val76]
def state1009 : List W := [val47, val13, val36, val107, val5, val57, val76]
def state1010 : List W := [val91, val76, val36, val107, val5, val13, val57]
def state1011 : List W := [val61, val36, val41, val107, val13, val76]
def state1012 : List W := [val61, val5, val36, val41, val107, val13, val76]
def state1013 : List W := [val61, val57, val36, val41, val107, val13, val76]
def state1014 : List W := [val82, val36, val41, val107, val5, val57]
def state1015 : List W := [val82, val13, val36, val41, val107, val5, val57]
def state1016 : List W := [val82, val76, val36, val41, val107, val5, val57]
def state1017 : List W := [val36, val125, val41, val107, val5, val13, val57, val76]
def state1018 : List W := [val133, val125, val41, val107, val5, val13, val57, val76]
def state1019 : List W := [val56, val125, val57, val107, val5, val13, val41, val76]
def state1020 : List W := [val136, val57, val107, val5, val13, val41, val76]
def state1021 : List W := [val136, val125, val57, val107, val5, val13, val41, val76]
def state1022 : List W := [val75, val125, val76, val107, val5, val13, val41, val57]
def state1023 : List W := [val141, val76, val107, val5, val13, val41, val57]
def state1024 : List W := [val141, val125, val76, val107, val5, val13, val41, val57]
def state1025 : List W := [val0, val41, val57, val107, val5, val13, val125, val76]
def state1026 : List W := [val71, val41, val57, val107, val5, val13, val125, val76]
def state1027 : List W := [val0, val41, val76, val107, val5, val13, val125, val57]
def state1028 : List W := [val91, val41, val76, val107, val5, val13, val125, val57]
def state1029 : List W := [val0, val57, val76, val107, val5, val13, val125, val41]
def state1030 : List W := [val94, val57, val76, val107, val5, val13, val125, val41]
def state1031 : List W := [val107, val28, val5, val13, val125, val41, val57, val76]
def state1032 : List W := [val158, val125, val28, val5, val13, val41, val57, val76]
def state1033 : List W := [val0, val5, val107, val13, val125, val41, val57, val76]
def state1034 : List W := [val32, val5, val107, val13, val125, val41, val57, val76]
def state1035 : List W := [val0, val13, val107, val5, val125, val41, val57, val76]
def state1036 : List W := [val35, val13, val107, val5, val125, val41, val57, val76]
def state1037 : List W := [val0, val125, val107, val5, val13, val41, val57, val76]
def state1038 : List W := [val154, val125, val107, val5, val13, val41, val57, val76]
def state1039 : List W := [val18, val41, val107, val5, val13, val125, val57, val76]
def state1040 : List W := [val53, val107, val5, val13, val125, val57, val76]
def state1041 : List W := [val53, val28, val107, val5, val13, val125, val57, val76]
def state1042 : List W := [val53, val41, val107, val5, val13, val125, val57, val76]
def state1043 : List W := [val19, val57, val107, val5, val13, val125, val41, val76]
def state1044 : List W := [val66, val57, val107, val5, val13, val125, val41, val76]
def state1045 : List W := [val23, val76, val107, val5, val13, val125, val41, val57]
def state1046 : List W := [val85, val76, val107, val5, val13, val125, val41, val57]
def state1047 : List W := [val129, val5, val107, val28, val13, val41, val57, val76]
def state1048 : List W := [val61, val107, val28, val13, val125, val41, val76]
def state1049 : List W := [val61, val5, val107, val28, val13, val125, val41, val76]
def state1050 : List W := [val61, val57, val107, val28, val13, val125, val41, val76]
def state1051 : List W := [val47, val13, val107, val28, val5, val125, val57, val76]
def state1052 : List W := [val82, val107, val28, val5, val125, val41, val57]
def state1053 : List W := [val82, val13, val107, val28, val5, val125, val41, val57]
def state1054 : List W := [val82, val76, val107, val28, val5, val125, val41, val57]
def state1055 : List W := [val36, val41, val107, val28, val5, val13, val57, val76]
def state1056 : List W := [val136, val107, val28, val5, val13, val41, val76]
def state1057 : List W := [val136, val125, val107, val28, val5, val13, val41, val76]
def state1058 : List W := [val136, val57, val107, val28, val5, val13, val41, val76]
def state1059 : List W := [val141, val107, val28, val5, val13, val41, val57]
def state1060 : List W := [val141, val125, val107, val28, val5, val13, val41, val57]
def state1061 : List W := [val141, val76, val107, val28, val5, val13, val41, val57]
def state1062 : List W := [val107, val99, val5, val13, val125, val41, val57, val76]
def state1063 : List W := [val116, val41, val99, val5, val13, val125, val57, val76]
def state1064 : List W := [val4, val5, val107, val13, val125, val41, val57, val76]
def state1065 : List W := [val102, val5, val107, val13, val125, val41, val57, val76]
def state1066 : List W := [val11, val13, val107, val5, val125, val41, val57, val76]
def state1067 : List W := [val104, val13, val107, val5, val125, val41, val57, val76]
def state1068 : List W := [val98, val125, val107, val5, val13, val41, val57, val76]
def state1069 : List W := [val147, val107, val5, val13, val41, val57, val76]
def state1070 : List W := [val147, val99, val107, val5, val13, val41, val57, val76]
def state1071 : List W := [val147, val125, val107, val5, val13, val41, val57, val76]
def state1072 : List W := [val0, val41, val107, val5, val13, val125, val57, val76]
def state1073 : List W := [val113, val41, val107, val5, val13, val125, val57, val76]
def state1074 : List W := [val0, val57, val107, val5, val13, val125, val41, val76]
def state1075 : List W := [val117, val57, val107, val5, val13, val125, val41, val76]
def state1076 : List W := [val0, val76, val107, val5, val13, val125, val41, val57]
def state1077 : List W := [val121, val76, val107, val5, val13, val125, val41, val57]
def state1078 : List W := [val129, val5, val107, val99, val13, val41, val57, val76]
def state1079 : List W := [val61, val107, val99, val13, val125, val41, val76]
def state1080 : List W := [val61, val5, val107, val99, val13, val125, val41, val76]
def state1081 : List W := [val61, val57, val107, val99, val13, val125, val41, val76]
def state1082 : List W := [val47, val107, val99, val5, val125, val57, val76]
def state1083 : List W := [val47, val13, val107, val99, val5, val125, val57, val76]
def state1084 : List W := [val47, val41, val107, val99, val5, val125, val57, val76]
def state1085 : List W := [val82, val107, val99, val5, val125, val41, val57]
def state1086 : List W := [val82, val13, val107, val99, val5, val125, val41, val57]
def state1087 : List W := [val82, val76, val107, val99, val5, val125, val41, val57]
def state1088 : List W := [val36, val41, val107, val99, val5, val13, val57, val76]
def state1089 : List W := [val136, val57, val107, val99, val5, val13, val41, val76]
def state1090 : List W := [val141, val76, val107, val99, val5, val13, val41, val57]
def state1091 : List W := [val107, val28, val99, val5, val13, val125, val41, val57, val76]
def state1092 : List W := [val36, val41, val5, val13, val28, val57, val76, val99]
def state1093 : List W := [val38, val41, val13, val28, val57, val76, val99]
def state1094 : List W := [val37, val38, val13, val28, val57, val76, val99]
def state1095 : List W := [val70, val38, val41, val13, val28, val76, val99]
def state1096 : List W := [val70, val57, val41, val13, val28, val76, val99]
def state1097 : List W := [val47, val38, val28, val57, val76, val99]
def state1098 : List W := [val47, val41, val38, val28, val57, val76, val99]
def state1099 : List W := [val47, val13, val38, val28, val57, val76, val99]
def state1100 : List W := [val53, val38, val13, val57, val76, val99]
def state1101 : List W := [val53, val41, val38, val13, val57, val76, val99]
def state1102 : List W := [val53, val28, val38, val13, val57, val76, val99]
def state1103 : List W := [val91, val76, val38, val13, val28, val57, val99]
def state1104 : List W := [val113, val99, val38, val13, val28, val57, val76]
def state1105 : List W := [val82, val38, val41, val28, val57, val99]
def state1106 : List W := [val82, val13, val38, val41, val28, val57, val99]
def state1107 : List W := [val82, val76, val38, val41, val28, val57, val99]
def state1108 : List W := [val107, val38, val41, val13, val57, val76]
def state1109 : List W := [val107, val28, val38, val41, val13, val57, val76]
def state1110 : List W := [val107, val99, val38, val41, val13, val57, val76]
def state1111 : List W := [val38, val36, val41, val13, val28, val57, val76, val99]
def state1112 : List W := [val38, val5, val41, val13, val28, val57, val76, val99]
def state1113 : List W := [val39, val36, val41, val5, val28, val57, val76, val99]
def state1114 : List W := [val51, val36, val41, val5, val13, val57, val76, val99]
def state1115 : List W := [val68, val41, val5, val13, val28, val76, val99]
def state1116 : List W := [val68, val36, val41, val5, val13, val28, val76, val99]
def state1117 : List W := [val68, val57, val41, val5, val13, val28, val76, val99]
def state1118 : List W := [val88, val41, val5, val13, val28, val57, val99]
def state1119 : List W := [val88, val36, val41, val5, val13, val28, val57, val99]
def state1120 : List W := [val88, val76, val41, val5, val13, val28, val57, val99]
def state1121 : List W := [val111, val41, val5, val13, val28, val57, val76]
def state1122 : List W := [val111, val36, val41, val5, val13, val28, val57, val76]
def state1123 : List W := [val111, val99, val41, val5, val13, val28, val57, val76]
def state1124 : List W := [val1, val5, val36, val13, val28, val57, val76, val99]
def state1125 : List W := [val47, val36, val5, val28, val57, val76, val99]
def state1126 : List W := [val47, val41, val36, val5, val28, val57, val76, val99]
def state1127 : List W := [val47, val13, val36, val5, val28, val57, val76, val99]
def state1128 : List W := [val53, val36, val5, val13, val57, val76, val99]
def state1129 : List W := [val53, val41, val36, val5, val13, val57, val76, val99]
def state1130 : List W := [val53, val28, val36, val5, val13, val57, val76, val99]
def state1131 : List W := [val91, val76, val36, val5, val13, val28, val57, val99]
def state1132 : List W := [val113, val99, val36, val5, val13, val28, val57, val76]
def state1133 : List W := [val61, val36, val41, val13, val28, val76, val99]
def state1134 : List W := [val39, val36, val61, val41, val28, val76, val99]
def state1135 : List W := [val51, val36, val61, val41, val13, val76, val99]
def state1136 : List W := [val88, val61, val41, val13, val28, val99]
def state1137 : List W := [val88, val36, val61, val41, val13, val28, val99]
def state1138 : List W := [val88, val76, val61, val41, val13, val28, val99]
def state1139 : List W := [val111, val61, val41, val13, val28, val76]
def state1140 : List W := [val111, val36, val61, val41, val13, val28, val76]
def state1141 : List W := [val111, val99, val61, val41, val13, val28, val76]
def state1142 : List W := [val47, val61, val36, val28, val76, val99]
def state1143 : List W := [val47, val41, val61, val36, val28, val76, val99]
def state1144 : List W := [val47, val13, val61, val36, val28, val76, val99]
def state1145 : List W := [val53, val61, val36, val13, val76, val99]
def state1146 : List W := [val53, val41, val61, val36, val13, val76, val99]
def state1147 : List W := [val53, val28, val61, val36, val13, val76, val99]
def state1148 : List W := [val91, val76, val61, val36, val13, val28, val99]
def state1149 : List W := [val113, val99, val61, val36, val13, val28, val76]
def state1150 : List W := [val82, val61, val36, val41, val28, val99]
def state1151 : List W := [val82, val13, val61, val36, val41, val28, val99]
def state1152 : List W := [val82, val76, val61, val36, val41, val28, val99]
def state1153 : List W := [val107, val61, val36, val41, val13, val76]
def state1154 : List W := [val107, val28, val61, val36, val41, val13, val76]
def state1155 : List W := [val107, val99, val61, val36, val41, val13, val76]
def state1156 : List W := [val61, val5, val36, val41, val13, val28, val76, val99]
def state1157 : List W := [val61, val57, val36, val41, val13, val28, val76, val99]
def state1158 : List W := [val82, val36, val41, val5, val28, val57, val99]
def state1159 : List W := [val38, val82, val41, val28, val57, val99]
def state1160 : List W := [val38, val36, val82, val41, val28, val57, val99]
def state1161 : List W := [val38, val5, val82, val41, val28, val57, val99]
def state1162 : List W := [val51, val36, val82, val41, val5, val57, val99]
def state1163 : List W := [val68, val82, val41, val5, val28, val99]
def state1164 : List W := [val68, val36, val82, val41, val5, val28, val99]
def state1165 : List W := [val68, val57, val82, val41, val5, val28, val99]
def state1166 : List W := [val111, val82, val41, val5, val28, val57]
def state1167 : List W := [val111, val36, val82, val41, val5, val28, val57]
def state1168 : List W := [val111, val99, val82, val41, val5, val28, val57]
def state1169 : List W := [val1, val5, val82, val36, val28, val57, val99]
def state1170 : List W := [val53, val28, val82, val36, val5, val57, val99]
def state1171 : List W := [val113, val99, val82, val36, val5, val28, val57]
def state1172 : List W := [val61, val82, val36, val41, val28, val99]
def state1173 : List W := [val61, val5, val82, val36, val41, val28, val99]
def state1174 : List W := [val61, val57, val82, val36, val41, val28, val99]
def state1175 : List W := [val107, val82, val36, val41, val5, val57]
def state1176 : List W := [val107, val28, val82, val36, val41, val5, val57]
def state1177 : List W := [val107, val99, val82, val36, val41, val5, val57]
def state1178 : List W := [val82, val13, val36, val41, val5, val28, val57, val99]
def state1179 : List W := [val82, val76, val36, val41, val5, val28, val57, val99]
def state1180 : List W := [val107, val36, val41, val5, val13, val57, val76]
def state1181 : List W := [val38, val107, val41, val13, val57, val76]
def state1182 : List W := [val38, val36, val107, val41, val13, val57, val76]
def state1183 : List W := [val38, val5, val107, val41, val13, val57, val76]
def state1184 : List W := [val39, val36, val107, val41, val5, val57, val76]
def state1185 : List W := [val68, val107, val41, val5, val13, val76]
def state1186 : List W := [val68, val36, val107, val41, val5, val13, val76]
def state1187 : List W := [val68, val57, val107, val41, val5, val13, val76]
def state1188 : List W := [val88, val107, val41, val5, val13, val57]
def state1189 : List W := [val88, val36, val107, val41, val5, val13, val57]
def state1190 : List W := [val88, val76, val107, val41, val5, val13, val57]
def state1191 : List W := [val1, val5, val107, val36, val13, val57, val76]
def state1192 : List W := [val47, val13, val107, val36, val5, val57, val76]
def state1193 : List W := [val91, val76, val107, val36, val5, val13, val57]
def state1194 : List W := [val61, val107, val36, val41, val13, val76]
def state1195 : List W := [val61, val5, val107, val36, val41, val13, val76]
def state1196 : List W := [val61, val57, val107, val36, val41, val13, val76]
def state1197 : List W := [val82, val107, val36, val41, val5, val57]
def state1198 : List W := [val82, val13, val107, val36, val41, val5, val57]
def state1199 : List W := [val82, val76, val107, val36, val41, val5, val57]
def state1200 : List W := [val107, val28, val36, val41, val5, val13, val57, val76]
def state1201 : List W := [val107, val99, val36, val41, val5, val13, val57, val76]
def state1202 : List W := [val36, val125, val41, val5, val13, val28, val57, val76, val99]
def state1203 : List W := [val38, val125, val41, val13, val28, val57, val76, val99]
def state1204 : List W := [val39, val125, val41, val5, val28, val57, val76, val99]
def state1205 : List W := [val51, val125, val41, val5, val13, val57, val76, val99]
def state1206 : List W := [val68, val125, val41, val5, val13, val28, val76, val99]
def state1207 : List W := [val88, val125, val41, val5, val13, val28, val57, val99]
def state1208 : List W := [val111, val125, val41, val5, val13, val28, val57, val76]
def state1209 : List W := [val133, val36, val5, val13, val28, val57, val76, val99]
def state1210 : List W := [val136, val36, val41, val5, val13, val28, val76, val99]
def state1211 : List W := [val141, val36, val41, val5, val13, val28, val57, val99]
def state1212 : List W := [val147, val36, val41, val5, val13, val28, val57, val76]
def state1213 : List W := [val47, val36, val125, val5, val28, val57, val76, val99]
def state1214 : List W := [val53, val36, val125, val5, val13, val57, val76, val99]
def state1215 : List W := [val61, val36, val125, val41, val13, val28, val76, val99]
def state1216 : List W := [val82, val36, val125, val41, val5, val28, val57, val99]
def state1217 : List W := [val107, val36, val125, val41, val5, val13, val57, val76]
def state1218 : List W := [val133, val125, val41, val5, val13, val28, val57, val76, val99]
def state1219 : List W := [val56, val125, val57, val5, val13, val28, val41, val76, val99]
def state1220 : List W := [val136, val5, val13, val28, val41, val76, val99]
def state1221 : List W := [val2, val136, val5, val13, val28, val41, val76, val99]
def state1222 : List W := [val137, val136, val5, val13, val28, val41, val76, val99]
def state1223 : List W := [val7, val136, val13, val5, val28, val41, val76, val99]
def state1224 : List W := [val138, val136, val13, val5, val28, val41, val76, val99]
def state1225 : List W := [val19, val136, val28, val5, val13, val41, val76, val99]
def state1226 : List W := [val156, val136, val28, val5, val13, val41, val76, val99]
def state1227 : List W := [val36, val136, val41, val5, val13, val28, val76, val99]
def state1228 : List W := [val139, val136, val41, val5, val13, val28, val76, val99]
def state1229 : List W := [val75, val136, val76, val5, val13, val28, val41, val99]
def state1230 : List W := [val145, val136, val76, val5, val13, val28, val41, val99]
def state1231 : List W := [val98, val136, val99, val5, val13, val28, val41, val76]
def state1232 : List W := [val151, val136, val99, val5, val13, val28, val41, val76]
def state1233 : List W := [val0, val5, val13, val136, val28, val41, val76, val99]
def state1234 : List W := [val17, val5, val13, val136, val28, val41, val76, val99]
def state1235 : List W := [val0, val5, val28, val136, val13, val41, val76, val99]
def state1236 : List W := [val32, val5, val28, val136, val13, val41, val76, val99]
def state1237 : List W := [val1, val5, val41, val136, val13, val28, val76, val99]
def state1238 : List W := [val44, val5, val41, val136, val13, val28, val76, val99]
def state1239 : List W := [val3, val5, val76, val136, val13, val28, val41, val99]
def state1240 : List W := [val79, val5, val76, val136, val13, val28, val41, val99]
def state1241 : List W := [val4, val5, val99, val136, val13, val28, val41, val76]
def state1242 : List W := [val102, val5, val99, val136, val13, val28, val41, val76]
def state1243 : List W := [val0, val13, val28, val136, val5, val41, val76, val99]
def state1244 : List W := [val35, val13, val28, val136, val5, val41, val76, val99]
def state1245 : List W := [val6, val13, val41, val136, val5, val28, val76, val99]
def state1246 : List W := [val47, val136, val5, val28, val76, val99]
def state1247 : List W := [val47, val13, val136, val5, val28, val76, val99]
def state1248 : List W := [val47, val41, val136, val5, val28, val76, val99]
def state1249 : List W := [val47, val13, val41, val136, val5, val28, val76, val99]
def state1250 : List W := [val10, val13, val76, val136, val5, val28, val41, val99]
def state1251 : List W := [val82, val13, val136, val5, val28, val41, val99]
def state1252 : List W := [val82, val13, val76, val136, val5, val28, val41, val99]
def state1253 : List W := [val11, val13, val99, val136, val5, val28, val41, val76]
def state1254 : List W := [val104, val13, val99, val136, val5, val28, val41, val76]
def state1255 : List W := [val18, val28, val41, val136, val5, val13, val76, val99]
def state1256 : List W := [val53, val136, val5, val13, val76, val99]
def state1257 : List W := [val53, val28, val136, val5, val13, val76, val99]
def state1258 : List W := [val53, val41, val136, val5, val13, val76, val99]
def state1259 : List W := [val53, val28, val41, val136, val5, val13, val76, val99]
def state1260 : List W := [val23, val28, val76, val136, val5, val13, val41, val99]
def state1261 : List W := [val85, val28, val76, val136, val5, val13, val41, val99]
def state1262 : List W := [val27, val28, val99, val136, val5, val13, val41, val76]
def state1263 : List W := [val107, val28, val136, val5, val13, val41, val76]
def state1264 : List W := [val107, val28, val99, val136, val5, val13, val41, val76]
def state1265 : List W := [val0, val41, val76, val136, val5, val13, val28, val99]
def state1266 : List W := [val91, val41, val76, val136, val5, val13, val28, val99]
def state1267 : List W := [val0, val41, val99, val136, val5, val13, val28, val76]
def state1268 : List W := [val113, val41, val99, val136, val5, val13, val28, val76]
def state1269 : List W := [val0, val76, val99, val136, val5, val13, val28, val41]
def state1270 : List W := [val121, val76, val99, val136, val5, val13, val28, val41]
def state1271 : List W := [val136, val125, val5, val13, val28, val41, val76, val99]
def state1272 : List W := [val137, val5, val125, val13, val28, val41, val76, val99]
def state1273 : List W := [val0, val5, val136, val13, val28, val41, val76, val99]
def state1274 : List W := [val129, val5, val136, val13, val28, val41, val76, val99]
def state1275 : List W := [val0, val13, val136, val5, val28, val41, val76, val99]
def state1276 : List W := [val132, val13, val136, val5, val28, val41, val76, val99]
def state1277 : List W := [val0, val28, val136, val5, val13, val41, val76, val99]
def state1278 : List W := [val154, val28, val136, val5, val13, val41, val76, val99]
def state1279 : List W := [val36, val41, val136, val5, val13, val28, val76, val99]
def state1280 : List W := [val133, val41, val136, val5, val13, val28, val76, val99]
def state1281 : List W := [val75, val76, val136, val5, val13, val28, val41, val99]
def state1282 : List W := [val141, val136, val5, val13, val28, val41, val99]
def state1283 : List W := [val141, val125, val136, val5, val13, val28, val41, val99]
def state1284 : List W := [val141, val76, val136, val5, val13, val28, val41, val99]
def state1285 : List W := [val98, val99, val136, val5, val13, val28, val41, val76]
def state1286 : List W := [val147, val136, val5, val13, val28, val41, val76]
def state1287 : List W := [val147, val125, val136, val5, val13, val28, val41, val76]
def state1288 : List W := [val147, val99, val136, val5, val13, val28, val41, val76]
def state1289 : List W := [val47, val136, val125, val5, val28, val76, val99]
def state1290 : List W := [val47, val13, val136, val125, val5, val28, val76, val99]
def state1291 : List W := [val47, val41, val136, val125, val5, val28, val76, val99]
def state1292 : List W := [val82, val13, val136, val125, val5, val28, val41, val99]
def state1293 : List W := [val53, val136, val125, val5, val13, val76, val99]
def state1294 : List W := [val53, val28, val136, val125, val5, val13, val76, val99]
def state1295 : List W := [val53, val41, val136, val125, val5, val13, val76, val99]
def state1296 : List W := [val107, val28, val136, val125, val5, val13, val41, val76]
def state1297 : List W := [val136, val57, val5, val13, val28, val41, val76, val99]
def state1298 : List W := [val137, val5, val57, val13, val28, val41, val76, val99]
def state1299 : List W := [val36, val41, val57, val5, val13, val28, val76, val99]
def state1300 : List W := [val145, val76, val57, val5, val13, val28, val41, val99]
def state1301 : List W := [val151, val99, val57, val5, val13, val28, val41, val76]
def state1302 : List W := [val2, val5, val136, val13, val28, val41, val76, val99]
def state1303 : List W := [val61, val136, val13, val28, val41, val76, val99]
def state1304 : List W := [val61, val57, val136, val13, val28, val41, val76, val99]
def state1305 : List W := [val61, val5, val136, val13, val28, val41, val76, val99]
def state1306 : List W := [val7, val13, val136, val5, val28, val41, val76, val99]
def state1307 : List W := [val63, val13, val136, val5, val28, val41, val76, val99]
def state1308 : List W := [val19, val28, val136, val5, val13, val41, val76, val99]
def state1309 : List W := [val66, val28, val136, val5, val13, val41, val76, val99]
def state1310 : List W := [val0, val41, val136, val5, val13, val28, val76, val99]
def state1311 : List W := [val71, val41, val136, val5, val13, val28, val76, val99]
def state1312 : List W := [val0, val76, val136, val5, val13, val28, val41, val99]
def state1313 : List W := [val94, val76, val136, val5, val13, val28, val41, val99]
def state1314 : List W := [val0, val99, val136, val5, val13, val28, val41, val76]
def state1315 : List W := [val117, val99, val136, val5, val13, val28, val41, val76]
def state1316 : List W := [val47, val136, val57, val5, val28, val76, val99]
def state1317 : List W := [val47, val13, val136, val57, val5, val28, val76, val99]
def state1318 : List W := [val47, val41, val136, val57, val5, val28, val76, val99]
def state1319 : List W := [val82, val136, val57, val5, val28, val41, val99]
def state1320 : List W := [val82, val13, val136, val57, val5, val28, val41, val99]
def state1321 : List W := [val82, val76, val136, val57, val5, val28, val41, val99]
def state1322 : List W := [val53, val136, val57, val5, val13, val76, val99]
def state1323 : List W := [val53, val28, val136, val57, val5, val13, val76, val99]
def state1324 : List W := [val53, val41, val136, val57, val5, val13, val76, val99]
def state1325 : List W := [val107, val136, val57, val5, val13, val41, val76]
def state1326 : List W := [val107, val28, val136, val57, val5, val13, val41, val76]
def state1327 : List W := [val107, val99, val136, val57, val5, val13, val41, val76]
def state1328 : List W := [val136, val125, val57, val5, val13, val28, val41, val76, val99]
def state1329 : List W := [val75, val125, val76, val5, val13, val28, val41, val57, val99]
def state1330 : List W := [val141, val5, val13, val28, val41, val57, val99]
def state1331 : List W := [val3, val141, val5, val13, val28, val41, val57, val99]
def state1332 : List W := [val142, val141, val5, val13, val28, val41, val57, val99]
def state1333 : List W := [val10, val141, val13, val5, val28, val41, val57, val99]
def state1334 : List W := [val143, val141, val13, val5, val28, val41, val57, val99]
def state1335 : List W := [val23, val141, val28, val5, val13, val41, val57, val99]
def state1336 : List W := [val157, val141, val28, val5, val13, val41, val57, val99]
def state1337 : List W := [val36, val141, val41, val5, val13, val28, val57, val99]
def state1338 : List W := [val144, val141, val41, val5, val13, val28, val57, val99]
def state1339 : List W := [val56, val141, val57, val5, val13, val28, val41, val99]
def state1340 : List W := [val145, val141, val57, val5, val13, val28, val41, val99]
def state1341 : List W := [val98, val141, val99, val5, val13, val28, val41, val57]
def state1342 : List W := [val153, val141, val99, val5, val13, val28, val41, val57]
def state1343 : List W := [val0, val5, val13, val141, val28, val41, val57, val99]
def state1344 : List W := [val17, val5, val13, val141, val28, val41, val57, val99]
def state1345 : List W := [val0, val5, val28, val141, val13, val41, val57, val99]
def state1346 : List W := [val32, val5, val28, val141, val13, val41, val57, val99]
def state1347 : List W := [val1, val5, val41, val141, val13, val28, val57, val99]
def state1348 : List W := [val44, val5, val41, val141, val13, val28, val57, val99]
def state1349 : List W := [val2, val5, val57, val141, val13, val28, val41, val99]
def state1350 : List W := [val61, val5, val141, val13, val28, val41, val99]
def state1351 : List W := [val61, val5, val57, val141, val13, val28, val41, val99]
def state1352 : List W := [val4, val5, val99, val141, val13, val28, val41, val57]
def state1353 : List W := [val102, val5, val99, val141, val13, val28, val41, val57]
def state1354 : List W := [val0, val13, val28, val141, val5, val41, val57, val99]
def state1355 : List W := [val35, val13, val28, val141, val5, val41, val57, val99]
def state1356 : List W := [val6, val13, val41, val141, val5, val28, val57, val99]
def state1357 : List W := [val47, val41, val141, val5, val28, val57, val99]
def state1358 : List W := [val47, val13, val41, val141, val5, val28, val57, val99]
def state1359 : List W := [val7, val13, val57, val141, val5, val28, val41, val99]
def state1360 : List W := [val63, val13, val57, val141, val5, val28, val41, val99]
def state1361 : List W := [val11, val13, val99, val141, val5, val28, val41, val57]
def state1362 : List W := [val104, val13, val99, val141, val5, val28, val41, val57]
def state1363 : List W := [val18, val28, val41, val141, val5, val13, val57, val99]
def state1364 : List W := [val53, val141, val5, val13, val57, val99]
def state1365 : List W := [val53, val28, val141, val5, val13, val57, val99]
def state1366 : List W := [val53, val41, val141, val5, val13, val57, val99]
def state1367 : List W := [val53, val28, val41, val141, val5, val13, val57, val99]
def state1368 : List W := [val19, val28, val57, val141, val5, val13, val41, val99]
def state1369 : List W := [val66, val28, val57, val141, val5, val13, val41, val99]
def state1370 : List W := [val27, val28, val99, val141, val5, val13, val41, val57]
def state1371 : List W := [val107, val28, val141, val5, val13, val41, val57]
def state1372 : List W := [val107, val28, val99, val141, val5, val13, val41, val57]
def state1373 : List W := [val0, val41, val57, val141, val5, val13, val28, val99]
def state1374 : List W := [val71, val41, val57, val141, val5, val13, val28, val99]
def state1375 : List W := [val0, val41, val99, val141, val5, val13, val28, val57]
def state1376 : List W := [val113, val41, val99, val141, val5, val13, val28, val57]
def state1377 : List W := [val0, val57, val99, val141, val5, val13, val28, val41]
def state1378 : List W := [val117, val57, val99, val141, val5, val13, val28, val41]
def state1379 : List W := [val141, val125, val5, val13, val28, val41, val57, val99]
def state1380 : List W := [val141, val76, val5, val13, val28, val41, val57, val99]
def state1381 : List W := [val142, val5, val76, val13, val28, val41, val57, val99]
def state1382 : List W := [val36, val41, val76, val5, val13, val28, val57, val99]
def state1383 : List W := [val145, val57, val76, val5, val13, val28, val41, val99]
def state1384 : List W := [val153, val99, val76, val5, val13, val28, val41, val57]
def state1385 : List W := [val3, val5, val141, val13, val28, val41, val57, val99]
def state1386 : List W := [val79, val5, val141, val13, val28, val41, val57, val99]
def state1387 : List W := [val10, val13, val141, val5, val28, val41, val57, val99]
def state1388 : List W := [val82, val141, val5, val28, val41, val57, val99]
def state1389 : List W := [val82, val76, val141, val5, val28, val41, val57, val99]
def state1390 : List W := [val82, val13, val141, val5, val28, val41, val57, val99]
def state1391 : List W := [val23, val28, val141, val5, val13, val41, val57, val99]
def state1392 : List W := [val85, val28, val141, val5, val13, val41, val57, val99]
def state1393 : List W := [val0, val41, val141, val5, val13, val28, val57, val99]
def state1394 : List W := [val91, val41, val141, val5, val13, val28, val57, val99]
def state1395 : List W := [val0, val57, val141, val5, val13, val28, val41, val99]
def state1396 : List W := [val94, val57, val141, val5, val13, val28, val41, val99]
def state1397 : List W := [val0, val99, val141, val5, val13, val28, val41, val57]
def state1398 : List W := [val121, val99, val141, val5, val13, val28, val41, val57]
def state1399 : List W := [val61, val141, val76, val13, val28, val41, val99]
def state1400 : List W := [val61, val5, val141, val76, val13, val28, val41, val99]
def state1401 : List W := [val61, val57, val141, val76, val13, val28, val41, val99]
def state1402 : List W := [val47, val41, val141, val76, val5, val28, val57, val99]
def state1403 : List W := [val53, val141, val76, val5, val13, val57, val99]
def state1404 : List W := [val53, val28, val141, val76, val5, val13, val57, val99]
def state1405 : List W := [val53, val41, val141, val76, val5, val13, val57, val99]
def state1406 : List W := [val107, val141, val76, val5, val13, val41, val57]
def state1407 : List W := [val107, val28, val141, val76, val5, val13, val41, val57]
def state1408 : List W := [val107, val99, val141, val76, val5, val13, val41, val57]
def state1409 : List W := [val141, val125, val76, val5, val13, val28, val41, val57, val99]
def state1410 : List W := [val98, val125, val99, val5, val13, val28, val41, val57, val76]
def state1411 : List W := [val147, val5, val13, val28, val41, val57, val76]
def state1412 : List W := [val4, val147, val5, val13, val28, val41, val57, val76]
def state1413 : List W := [val148, val147, val5, val13, val28, val41, val57, val76]
def state1414 : List W := [val11, val147, val13, val5, val28, val41, val57, val76]
def state1415 : List W := [val149, val147, val13, val5, val28, val41, val57, val76]
def state1416 : List W := [val27, val147, val28, val5, val13, val41, val57, val76]
def state1417 : List W := [val158, val147, val28, val5, val13, val41, val57, val76]
def state1418 : List W := [val36, val147, val41, val5, val13, val28, val57, val76]
def state1419 : List W := [val150, val147, val41, val5, val13, val28, val57, val76]
def state1420 : List W := [val56, val147, val57, val5, val13, val28, val41, val76]
def state1421 : List W := [val151, val147, val57, val5, val13, val28, val41, val76]
def state1422 : List W := [val75, val147, val76, val5, val13, val28, val41, val57]
def state1423 : List W := [val153, val147, val76, val5, val13, val28, val41, val57]
def state1424 : List W := [val0, val5, val13, val147, val28, val41, val57, val76]
def state1425 : List W := [val17, val5, val13, val147, val28, val41, val57, val76]
def state1426 : List W := [val0, val5, val28, val147, val13, val41, val57, val76]
def state1427 : List W := [val32, val5, val28, val147, val13, val41, val57, val76]
def state1428 : List W := [val1, val5, val41, val147, val13, val28, val57, val76]
def state1429 : List W := [val44, val5, val41, val147, val13, val28, val57, val76]
def state1430 : List W := [val2, val5, val57, val147, val13, val28, val41, val76]
def state1431 : List W := [val61, val5, val147, val13, val28, val41, val76]
def state1432 : List W := [val61, val5, val57, val147, val13, val28, val41, val76]
def state1433 : List W := [val3, val5, val76, val147, val13, val28, val41, val57]
def state1434 : List W := [val79, val5, val76, val147, val13, val28, val41, val57]
def state1435 : List W := [val0, val13, val28, val147, val5, val41, val57, val76]
def state1436 : List W := [val35, val13, val28, val147, val5, val41, val57, val76]
def state1437 : List W := [val6, val13, val41, val147, val5, val28, val57, val76]
def state1438 : List W := [val47, val147, val5, val28, val57, val76]
def state1439 : List W := [val47, val13, val147, val5, val28, val57, val76]
def state1440 : List W := [val47, val41, val147, val5, val28, val57, val76]
def state1441 : List W := [val47, val13, val41, val147, val5, val28, val57, val76]
def state1442 : List W := [val7, val13, val57, val147, val5, val28, val41, val76]
def state1443 : List W := [val63, val13, val57, val147, val5, val28, val41, val76]
def state1444 : List W := [val10, val13, val76, val147, val5, val28, val41, val57]
def state1445 : List W := [val82, val13, val147, val5, val28, val41, val57]
def state1446 : List W := [val82, val13, val76, val147, val5, val28, val41, val57]
def state1447 : List W := [val18, val28, val41, val147, val5, val13, val57, val76]
def state1448 : List W := [val53, val41, val147, val5, val13, val57, val76]
def state1449 : List W := [val53, val28, val41, val147, val5, val13, val57, val76]
def state1450 : List W := [val19, val28, val57, val147, val5, val13, val41, val76]
def state1451 : List W := [val66, val28, val57, val147, val5, val13, val41, val76]
def state1452 : List W := [val23, val28, val76, val147, val5, val13, val41, val57]
def state1453 : List W := [val85, val28, val76, val147, val5, val13, val41, val57]
def state1454 : List W := [val0, val41, val57, val147, val5, val13, val28, val76]
def state1455 : List W := [val71, val41, val57, val147, val5, val13, val28, val76]
def state1456 : List W := [val0, val41, val76, val147, val5, val13, val28, val57]
def state1457 : List W := [val91, val41, val76, val147, val5, val13, val28, val57]
def state1458 : List W := [val0, val57, val76, val147, val5, val13, val28, val41]
def state1459 : List W := [val94, val57, val76, val147, val5, val13, val28, val41]
def state1460 : List W := [val147, val125, val5, val13, val28, val41, val57, val76]
def state1461 : List W := [val147, val99, val5, val13, val28, val41, val57, val76]
def state1462 : List W := [val148, val5, val99, val13, val28, val41, val57, val76]
def state1463 : List W := [val36, val41, val99, val5, val13, val28, val57, val76]
def state1464 : List W := [val151, val57, val99, val5, val13, val28, val41, val76]
def state1465 : List W := [val153, val76, val99, val5, val13, val28, val41, val57]
def state1466 : List W := [val4, val5, val147, val13, val28, val41, val57, val76]
def state1467 : List W := [val102, val5, val147, val13, val28, val41, val57, val76]
def state1468 : List W := [val11, val13, val147, val5, val28, val41, val57, val76]
def state1469 : List W := [val104, val13, val147, val5, val28, val41, val57, val76]
def state1470 : List W := [val27, val28, val147, val5, val13, val41, val57, val76]
def state1471 : List W := [val107, val147, val5, val13, val41, val57, val76]
def state1472 : List W := [val107, val99, val147, val5, val13, val41, val57, val76]
def state1473 : List W := [val107, val28, val147, val5, val13, val41, val57, val76]
def state1474 : List W := [val0, val41, val147, val5, val13, val28, val57, val76]
def state1475 : List W := [val113, val41, val147, val5, val13, val28, val57, val76]
def state1476 : List W := [val0, val57, val147, val5, val13, val28, val41, val76]
def state1477 : List W := [val117, val57, val147, val5, val13, val28, val41, val76]
def state1478 : List W := [val0, val76, val147, val5, val13, val28, val41, val57]
def state1479 : List W := [val121, val76, val147, val5, val13, val28, val41, val57]
def state1480 : List W := [val61, val147, val99, val13, val28, val41, val76]
def state1481 : List W := [val61, val5, val147, val99, val13, val28, val41, val76]
def state1482 : List W := [val61, val57, val147, val99, val13, val28, val41, val76]
def state1483 : List W := [val47, val147, val99, val5, val28, val57, val76]
def state1484 : List W := [val47, val13, val147, val99, val5, val28, val57, val76]
def state1485 : List W := [val47, val41, val147, val99, val5, val28, val57, val76]
def state1486 : List W := [val82, val147, val99, val5, val28, val41, val57]
def state1487 : List W := [val82, val13, val147, val99, val5, val28, val41, val57]
def state1488 : List W := [val82, val76, val147, val99, val5, val28, val41, val57]
def state1489 : List W := [val53, val41, val147, val99, val5, val13, val57, val76]
def state1490 : List W := [val147, val125, val99, val5, val13, val28, val41, val57, val76]
def state1491 : List W := [val0, val41, val57, val5, val13, val28, val125, val76, val99]
def state1492 : List W := [val71, val41, val57, val5, val13, val28, val125, val76, val99]
def state1493 : List W := [val0, val41, val76, val5, val13, val28, val125, val57, val99]
def state1494 : List W := [val91, val41, val76, val5, val13, val28, val125, val57, val99]
def state1495 : List W := [val87, val41, val76, val5, val13, val28, val57, val99]
def state1496 : List W := [val47, val91, val76, val5, val28, val125, val57, val99]
def state1497 : List W := [val53, val91, val76, val5, val13, val125, val57, val99]
def state1498 : List W := [val36, val91, val76, val5, val13, val28, val57, val99]
def state1499 : List W := [val82, val91, val41, val5, val28, val125, val57, val99]
def state1500 : List W := [val141, val91, val41, val5, val13, val28, val57, val99]
def state1501 : List W := [val61, val91, val41, val76, val13, val28, val125, val99]
def state1502 : List W := [val107, val91, val41, val76, val5, val13, val125, val57]
def state1503 : List W := [val136, val91, val41, val76, val5, val13, val28, val99]
def state1504 : List W := [val147, val91, val41, val76, val5, val13, val28, val57]
def state1505 : List W := [val0, val41, val99, val5, val13, val28, val125, val57, val76]
def state1506 : List W := [val113, val41, val99, val5, val13, val28, val125, val57, val76]
def state1507 : List W := [val110, val41, val99, val5, val13, val28, val57, val76]
def state1508 : List W := [val47, val113, val99, val5, val28, val125, val57, val76]
def state1509 : List W := [val53, val113, val99, val5, val13, val125, val57, val76]
def state1510 : List W := [val36, val113, val99, val5, val13, val28, val57, val76]
def state1511 : List W := [val107, val113, val41, val5, val13, val125, val57, val76]
def state1512 : List W := [val147, val113, val41, val5, val13, val28, val57, val76]
def state1513 : List W := [val61, val113, val41, val99, val13, val28, val125, val76]
def state1514 : List W := [val82, val113, val41, val99, val5, val28, val125, val57]
def state1515 : List W := [val136, val113, val41, val99, val5, val13, val28, val76]
def state1516 : List W := [val141, val113, val41, val99, val5, val13, val28, val57]
def state1517 : List W := [val0, val57, val76, val5, val13, val28, val125, val41, val99]
def state1518 : List W := [val94, val57, val76, val5, val13, val28, val125, val41, val99]
def state1519 : List W := [val0, val57, val99, val5, val13, val28, val125, val41, val76]
def state1520 : List W := [val117, val57, val99, val5, val13, val28, val125, val41, val76]
def state1521 : List W := [val0, val76, val99, val5, val13, val28, val125, val41, val57]
def state1522 : List W := [val121, val76, val99, val5, val13, val28, val125, val41, val57]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1 : optimized 8 0 state1 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check2 : optimized 8 0 state2 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check3 : optimized 8 0 state3 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check4 : optimized 8 0 state4 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check5 : optimized 8 0 state5 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check8 : optimized 6 0 state8 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check9 : optimized 6 0 state9 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check10 : optimized 6 0 state10 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check11 : optimized 6 0 state11 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check12 : optimized 6 0 state12 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check13 : optimized 6 0 state13 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check14 : optimized 6 1 state14 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check15 : optimized 6 0 state15 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check16 : optimized 6 0 state16 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check17 : optimized 6 1 state17 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check18 : optimized 6 0 state18 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check19 : optimized 6 0 state19 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check20 : optimized 6 1 state20 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check21 : optimized 6 0 state21 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check22 : optimized 6 0 state22 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check7 : optimized 7 1 state7 = false := by
  rw [optimized_expand]
  have hg : (state7 == [goal]) = false := by decide +kernel
  have he : expand 1 state7 = [(0, state8), (0, state9), (0, state10), (0, state11), (0, state12), (0, state13), (1, state14), (0, state15), (0, state16), (1, state17), (0, state18), (0, state19), (1, state20), (0, state21), (0, state22)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check8, check9, check10, check11, check12, check13, check14, check15, check16, check17, check18, check19, check20, check21, check22]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check23 : optimized 7 0 state23 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check24 : optimized 7 0 state24 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check25 : optimized 7 1 state25 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check26 : optimized 7 0 state26 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check27 : optimized 7 0 state27 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check28 : optimized 7 0 state28 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check29 : optimized 7 0 state29 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check30 : optimized 7 0 state30 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check31 : optimized 7 0 state31 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check32 : optimized 7 0 state32 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check34 : optimized 6 0 state34 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check35 : optimized 6 1 state35 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check36 : optimized 6 0 state36 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check37 : optimized 6 0 state37 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check38 : optimized 6 0 state38 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check39 : optimized 6 0 state39 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check40 : optimized 6 1 state40 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check41 : optimized 6 0 state41 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check42 : optimized 6 0 state42 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check43 : optimized 6 1 state43 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check44 : optimized 6 0 state44 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check45 : optimized 6 0 state45 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check46 : optimized 6 1 state46 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check47 : optimized 6 0 state47 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check48 : optimized 6 0 state48 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check49 : optimized 6 1 state49 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check50 : optimized 6 0 state50 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check51 : optimized 6 0 state51 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check33 : optimized 7 1 state33 = false := by
  rw [optimized_expand]
  have hg : (state33 == [goal]) = false := by decide +kernel
  have he : expand 1 state33 = [(0, state34), (1, state35), (0, state36), (0, state37), (0, state38), (0, state39), (1, state40), (0, state41), (0, state42), (1, state43), (0, state44), (0, state45), (1, state46), (0, state47), (0, state48), (1, state49), (0, state50), (0, state51)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check34, check35, check36, check37, check38, check39, check40, check41, check42, check43, check44, check45, check46, check47, check48, check49, check50, check51]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check52 : optimized 7 0 state52 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check53 : optimized 7 0 state53 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check54 : optimized 7 1 state54 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check55 : optimized 7 0 state55 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check56 : optimized 7 0 state56 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check57 : optimized 7 1 state57 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check58 : optimized 7 0 state58 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check59 : optimized 7 0 state59 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check60 : optimized 7 1 state60 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check61 : optimized 7 0 state61 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check62 : optimized 7 0 state62 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check63 : optimized 7 1 state63 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check64 : optimized 7 0 state64 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check65 : optimized 7 0 state65 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check6 : optimized 8 1 state6 = false := by
  rw [optimized_expand]
  have hg : (state6 == [goal]) = false := by decide +kernel
  have he : expand 1 state6 = [(1, state7), (0, state23), (0, state24), (1, state25), (0, state26), (0, state27), (0, state28), (0, state29), (0, state30), (0, state31), (0, state32), (1, state33), (0, state52), (0, state53), (1, state54), (0, state55), (0, state56), (1, state57), (0, state58), (0, state59), (1, state60), (0, state61), (0, state62), (1, state63), (0, state64), (0, state65)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check7, check23, check24, check25, check26, check27, check28, check29, check30, check31, check32, check33, check52, check53, check54, check55, check56, check57, check58, check59, check60, check61, check62, check63, check64, check65]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check66 : optimized 8 0 state66 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check68 : optimized 7 0 state68 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check69 : optimized 7 0 state69 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check70 : optimized 7 0 state70 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check71 : optimized 7 0 state71 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check72 : optimized 7 0 state72 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check73 : optimized 7 0 state73 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check74 : optimized 7 0 state74 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check75 : optimized 7 0 state75 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check76 : optimized 7 0 state76 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check77 : optimized 7 0 state77 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check78 : optimized 7 0 state78 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check79 : optimized 7 0 state79 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check80 : optimized 7 0 state80 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check81 : optimized 7 0 state81 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check82 : optimized 7 0 state82 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check83 : optimized 7 0 state83 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check67 : optimized 8 0 state67 = false := by
  rw [optimized_expand]
  have hg : (state67 == [goal]) = false := by decide +kernel
  have he : expand 0 state67 = [(0, state68), (0, state69), (0, state70), (0, state71), (0, state72), (0, state73), (0, state74), (0, state75), (0, state76), (0, state77), (0, state78), (0, state79), (0, state80), (0, state81), (0, state82), (0, state83)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check68, check69, check70, check71, check72, check73, check74, check75, check76, check77, check78, check79, check80, check81, check82, check83]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check85 : optimized 7 0 state85 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check86 : optimized 7 0 state86 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check87 : optimized 7 0 state87 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check88 : optimized 7 0 state88 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check89 : optimized 7 0 state89 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check90 : optimized 7 0 state90 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check91 : optimized 7 0 state91 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check92 : optimized 7 0 state92 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check93 : optimized 7 0 state93 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check94 : optimized 7 0 state94 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check95 : optimized 7 0 state95 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check84 : optimized 8 0 state84 = false := by
  rw [optimized_expand]
  have hg : (state84 == [goal]) = false := by decide +kernel
  have he : expand 0 state84 = [(0, state85), (0, state86), (0, state87), (0, state88), (0, state89), (0, state90), (0, state91), (0, state92), (0, state93), (0, state94), (0, state95)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check85, check86, check87, check88, check89, check90, check91, check92, check93, check94, check95]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check96 : optimized 8 0 state96 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check98 : optimized 7 0 state98 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check99 : optimized 7 0 state99 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check100 : optimized 7 0 state100 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check101 : optimized 7 0 state101 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check102 : optimized 7 0 state102 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check104 : optimized 6 0 state104 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check105 : optimized 6 0 state105 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check106 : optimized 6 0 state106 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check107 : optimized 6 0 state107 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check108 : optimized 6 0 state108 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check109 : optimized 6 0 state109 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check110 : optimized 6 1 state110 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check111 : optimized 6 0 state111 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check112 : optimized 6 0 state112 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check113 : optimized 6 1 state113 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check114 : optimized 6 0 state114 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check115 : optimized 6 0 state115 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check116 : optimized 6 1 state116 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check117 : optimized 6 0 state117 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check118 : optimized 6 0 state118 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check119 : optimized 6 1 state119 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check120 : optimized 6 0 state120 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check121 : optimized 6 0 state121 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check103 : optimized 7 1 state103 = false := by
  rw [optimized_expand]
  have hg : (state103 == [goal]) = false := by decide +kernel
  have he : expand 1 state103 = [(1, state35), (0, state104), (0, state37), (0, state105), (0, state106), (0, state107), (0, state108), (0, state109), (1, state110), (0, state111), (0, state112), (1, state113), (0, state114), (0, state115), (1, state116), (0, state117), (0, state118), (1, state119), (0, state120), (0, state121)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check35, check104, check37, check105, check106, check107, check108, check109, check110, check111, check112, check113, check114, check115, check116, check117, check118, check119, check120, check121]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check122 : optimized 7 0 state122 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check123 : optimized 7 0 state123 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check124 : optimized 7 0 state124 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check125 : optimized 7 0 state125 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check126 : optimized 7 0 state126 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check127 : optimized 7 0 state127 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check128 : optimized 7 0 state128 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check129 : optimized 7 0 state129 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check130 : optimized 7 0 state130 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check131 : optimized 7 0 state131 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check132 : optimized 7 0 state132 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check133 : optimized 7 0 state133 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check134 : optimized 7 2 state134 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check135 : optimized 7 1 state135 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check136 : optimized 7 1 state136 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check137 : optimized 7 0 state137 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check138 : optimized 7 0 state138 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check140 : optimized 6 0 state140 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check141 : optimized 6 0 state141 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check142 : optimized 6 0 state142 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check143 : optimized 6 0 state143 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check144 : optimized 6 0 state144 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check145 : optimized 6 0 state145 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check146 : optimized 6 0 state146 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check147 : optimized 6 0 state147 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check148 : optimized 6 0 state148 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check149 : optimized 6 0 state149 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check150 : optimized 6 0 state150 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check151 : optimized 6 0 state151 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check152 : optimized 6 0 state152 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check153 : optimized 6 1 state153 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check154 : optimized 6 0 state154 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check155 : optimized 6 0 state155 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check156 : optimized 6 0 state156 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check157 : optimized 6 0 state157 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check158 : optimized 6 0 state158 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check159 : optimized 6 0 state159 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check160 : optimized 6 0 state160 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check161 : optimized 6 0 state161 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check162 : optimized 6 1 state162 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check163 : optimized 6 0 state163 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check164 : optimized 6 0 state164 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check165 : optimized 6 2 state165 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check166 : optimized 6 1 state166 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check167 : optimized 6 1 state167 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check168 : optimized 6 0 state168 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check169 : optimized 6 1 state169 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check170 : optimized 6 0 state170 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check171 : optimized 6 0 state171 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check172 : optimized 6 0 state172 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check173 : optimized 6 1 state173 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check174 : optimized 6 0 state174 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check175 : optimized 6 0 state175 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check176 : optimized 6 0 state176 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check139 : optimized 7 2 state139 = false := by
  rw [optimized_expand]
  have hg : (state139 == [goal]) = false := by decide +kernel
  have he : expand 2 state139 = [(0, state140), (0, state141), (0, state142), (0, state143), (0, state144), (0, state145), (0, state146), (0, state147), (0, state148), (0, state149), (0, state150), (0, state151), (0, state152), (1, state153), (0, state154), (0, state155), (0, state156), (0, state157), (0, state158), (0, state159), (0, state160), (0, state161), (1, state162), (0, state163), (0, state164), (2, state165), (1, state166), (1, state167), (0, state168), (1, state169), (0, state170), (0, state171), (0, state172), (1, state173), (0, state174), (0, state175), (0, state176)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check140, check141, check142, check143, check144, check145, check146, check147, check148, check149, check150, check151, check152, check153, check154, check155, check156, check157, check158, check159, check160, check161, check162, check163, check164, check165, check166, check167, check168, check169, check170, check171, check172, check173, check174, check175, check176]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check177 : optimized 7 1 state177 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check178 : optimized 7 1 state178 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check179 : optimized 7 0 state179 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check180 : optimized 7 0 state180 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check181 : optimized 7 0 state181 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check182 : optimized 7 0 state182 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check183 : optimized 7 0 state183 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check184 : optimized 7 0 state184 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check185 : optimized 7 2 state185 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check186 : optimized 7 1 state186 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check187 : optimized 7 1 state187 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check188 : optimized 7 0 state188 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check189 : optimized 7 0 state189 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check190 : optimized 7 0 state190 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check191 : optimized 7 0 state191 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check193 : optimized 6 0 state193 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check194 : optimized 6 0 state194 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check195 : optimized 6 0 state195 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check196 : optimized 6 0 state196 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check197 : optimized 6 0 state197 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check198 : optimized 6 0 state198 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check199 : optimized 6 0 state199 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check200 : optimized 6 0 state200 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check201 : optimized 6 0 state201 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check202 : optimized 6 0 state202 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check203 : optimized 6 0 state203 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check204 : optimized 6 0 state204 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check205 : optimized 6 0 state205 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check206 : optimized 6 1 state206 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check207 : optimized 6 0 state207 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check208 : optimized 6 0 state208 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check209 : optimized 6 0 state209 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check210 : optimized 6 0 state210 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check211 : optimized 6 0 state211 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check212 : optimized 6 0 state212 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check213 : optimized 6 0 state213 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check214 : optimized 6 0 state214 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check215 : optimized 6 1 state215 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check216 : optimized 6 0 state216 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check217 : optimized 6 0 state217 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check218 : optimized 6 2 state218 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check219 : optimized 6 1 state219 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check220 : optimized 6 1 state220 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check221 : optimized 6 0 state221 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check222 : optimized 6 1 state222 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check223 : optimized 6 0 state223 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check224 : optimized 6 0 state224 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check225 : optimized 6 0 state225 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check226 : optimized 6 1 state226 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check227 : optimized 6 0 state227 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check228 : optimized 6 0 state228 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check229 : optimized 6 0 state229 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check192 : optimized 7 2 state192 = false := by
  rw [optimized_expand]
  have hg : (state192 == [goal]) = false := by decide +kernel
  have he : expand 2 state192 = [(0, state193), (0, state194), (0, state195), (0, state196), (0, state197), (0, state198), (0, state199), (0, state200), (0, state201), (0, state202), (0, state203), (0, state204), (0, state205), (1, state206), (0, state207), (0, state208), (0, state209), (0, state210), (0, state211), (0, state212), (0, state213), (0, state214), (1, state215), (0, state216), (0, state217), (2, state218), (1, state219), (1, state220), (0, state221), (1, state222), (0, state223), (0, state224), (0, state225), (1, state226), (0, state227), (0, state228), (0, state229)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check193, check194, check195, check196, check197, check198, check199, check200, check201, check202, check203, check204, check205, check206, check207, check208, check209, check210, check211, check212, check213, check214, check215, check216, check217, check218, check219, check220, check221, check222, check223, check224, check225, check226, check227, check228, check229]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check230 : optimized 7 1 state230 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check231 : optimized 7 1 state231 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check232 : optimized 7 0 state232 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check234 : optimized 6 1 state234 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check235 : optimized 6 0 state235 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check236 : optimized 6 0 state236 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check237 : optimized 6 0 state237 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check238 : optimized 6 0 state238 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check239 : optimized 6 1 state239 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check240 : optimized 6 0 state240 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check241 : optimized 6 0 state241 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check242 : optimized 6 1 state242 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check243 : optimized 6 0 state243 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check244 : optimized 6 0 state244 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check245 : optimized 6 0 state245 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check246 : optimized 6 1 state246 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check247 : optimized 6 0 state247 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check248 : optimized 6 0 state248 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check249 : optimized 6 1 state249 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check250 : optimized 6 0 state250 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check251 : optimized 6 0 state251 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check252 : optimized 6 0 state252 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check253 : optimized 6 0 state253 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check254 : optimized 6 1 state254 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check255 : optimized 6 0 state255 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check256 : optimized 6 0 state256 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check257 : optimized 6 1 state257 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check258 : optimized 6 0 state258 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check259 : optimized 6 0 state259 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check233 : optimized 7 1 state233 = false := by
  rw [optimized_expand]
  have hg : (state233 == [goal]) = false := by decide +kernel
  have he : expand 1 state233 = [(1, state234), (0, state235), (0, state236), (0, state237), (0, state238), (1, state239), (0, state240), (0, state241), (1, state242), (0, state243), (0, state244), (0, state245), (1, state246), (0, state247), (0, state248), (1, state249), (0, state250), (0, state251), (0, state252), (0, state253), (1, state254), (0, state255), (0, state256), (1, state257), (0, state258), (0, state259)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check234, check235, check236, check237, check238, check239, check240, check241, check242, check243, check244, check245, check246, check247, check248, check249, check250, check251, check252, check253, check254, check255, check256, check257, check258, check259]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check260 : optimized 7 0 state260 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check261 : optimized 7 0 state261 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check262 : optimized 7 0 state262 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check263 : optimized 7 1 state263 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check264 : optimized 7 0 state264 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check265 : optimized 7 0 state265 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check266 : optimized 7 1 state266 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check267 : optimized 7 0 state267 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check268 : optimized 7 0 state268 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check269 : optimized 7 0 state269 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check270 : optimized 7 0 state270 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check271 : optimized 7 0 state271 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check272 : optimized 7 0 state272 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check273 : optimized 7 0 state273 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check97 : optimized 8 2 state97 = false := by
  rw [optimized_expand]
  have hg : (state97 == [goal]) = false := by decide +kernel
  have he : expand 2 state97 = [(0, state98), (0, state99), (0, state100), (0, state101), (0, state102), (1, state103), (0, state122), (0, state123), (0, state124), (0, state125), (0, state126), (0, state127), (0, state128), (0, state129), (0, state130), (0, state131), (0, state132), (0, state133), (2, state134), (1, state135), (1, state136), (0, state137), (0, state138), (2, state139), (1, state177), (1, state178), (0, state179), (0, state180), (0, state181), (0, state182), (0, state183), (0, state184), (2, state185), (1, state186), (1, state187), (0, state188), (0, state189), (0, state190), (0, state191), (2, state192), (1, state230), (1, state231), (0, state232), (1, state233), (0, state260), (0, state261), (0, state262), (1, state263), (0, state264), (0, state265), (1, state266), (0, state267), (0, state268), (0, state269), (0, state270), (0, state271), (0, state272), (0, state273)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check98, check99, check100, check101, check102, check103, check122, check123, check124, check125, check126, check127, check128, check129, check130, check131, check132, check133, check134, check135, check136, check137, check138, check139, check177, check178, check179, check180, check181, check182, check183, check184, check185, check186, check187, check188, check189, check190, check191, check192, check230, check231, check232, check233, check260, check261, check262, check263, check264, check265, check266, check267, check268, check269, check270, check271, check272, check273]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check275 : optimized 7 0 state275 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check276 : optimized 7 0 state276 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check277 : optimized 7 0 state277 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check278 : optimized 7 0 state278 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check279 : optimized 7 0 state279 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check280 : optimized 7 0 state280 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check281 : optimized 7 0 state281 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check283 : optimized 6 1 state283 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check284 : optimized 6 0 state284 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check285 : optimized 6 0 state285 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check286 : optimized 6 1 state286 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check287 : optimized 6 0 state287 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check288 : optimized 6 0 state288 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check289 : optimized 6 1 state289 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check290 : optimized 6 0 state290 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check291 : optimized 6 0 state291 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check292 : optimized 6 1 state292 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check293 : optimized 6 0 state293 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check294 : optimized 6 0 state294 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check282 : optimized 7 1 state282 = false := by
  rw [optimized_expand]
  have hg : (state282 == [goal]) = false := by decide +kernel
  have he : expand 1 state282 = [(0, state34), (1, state35), (0, state36), (0, state37), (0, state38), (0, state39), (1, state283), (0, state284), (0, state285), (1, state286), (0, state287), (0, state288), (1, state289), (0, state290), (0, state291), (1, state292), (0, state293), (0, state294)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check34, check35, check36, check37, check38, check39, check283, check284, check285, check286, check287, check288, check289, check290, check291, check292, check293, check294]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check295 : optimized 7 0 state295 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check296 : optimized 7 0 state296 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check297 : optimized 7 0 state297 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check298 : optimized 7 0 state298 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check299 : optimized 7 0 state299 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check300 : optimized 7 0 state300 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check301 : optimized 7 0 state301 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check302 : optimized 7 0 state302 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check303 : optimized 7 1 state303 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check304 : optimized 7 0 state304 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check305 : optimized 7 0 state305 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check306 : optimized 7 1 state306 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check307 : optimized 7 0 state307 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check308 : optimized 7 0 state308 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check309 : optimized 7 1 state309 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check310 : optimized 7 0 state310 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check311 : optimized 7 0 state311 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check312 : optimized 7 1 state312 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check313 : optimized 7 0 state313 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check314 : optimized 7 0 state314 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check315 : optimized 7 0 state315 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check316 : optimized 7 1 state316 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check317 : optimized 7 0 state317 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check318 : optimized 7 0 state318 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check319 : optimized 7 1 state319 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check320 : optimized 7 0 state320 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check321 : optimized 7 0 state321 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check274 : optimized 8 1 state274 = false := by
  rw [optimized_expand]
  have hg : (state274 == [goal]) = false := by decide +kernel
  have he : expand 1 state274 = [(1, state25), (0, state275), (0, state276), (0, state277), (0, state278), (0, state279), (0, state280), (0, state281), (1, state282), (0, state295), (0, state296), (0, state297), (0, state298), (0, state299), (0, state300), (0, state301), (0, state302), (1, state303), (0, state304), (0, state305), (1, state306), (0, state307), (0, state308), (1, state309), (0, state310), (0, state311), (1, state312), (0, state313), (0, state314), (0, state315), (1, state316), (0, state317), (0, state318), (1, state319), (0, state320), (0, state321)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check25, check275, check276, check277, check278, check279, check280, check281, check282, check295, check296, check297, check298, check299, check300, check301, check302, check303, check304, check305, check306, check307, check308, check309, check310, check311, check312, check313, check314, check315, check316, check317, check318, check319, check320, check321]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check323 : optimized 7 0 state323 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check324 : optimized 7 0 state324 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check325 : optimized 7 0 state325 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check326 : optimized 7 0 state326 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check327 : optimized 7 0 state327 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check328 : optimized 7 0 state328 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check329 : optimized 7 1 state329 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check330 : optimized 7 0 state330 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check331 : optimized 7 0 state331 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check332 : optimized 7 0 state332 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check333 : optimized 7 0 state333 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check334 : optimized 7 0 state334 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check335 : optimized 7 0 state335 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check336 : optimized 7 0 state336 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check337 : optimized 7 0 state337 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check338 : optimized 7 1 state338 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check339 : optimized 7 0 state339 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check340 : optimized 7 0 state340 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check341 : optimized 7 1 state341 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check342 : optimized 7 0 state342 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check343 : optimized 7 0 state343 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check344 : optimized 7 1 state344 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check345 : optimized 7 0 state345 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check346 : optimized 7 0 state346 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check347 : optimized 7 1 state347 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check348 : optimized 7 0 state348 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check349 : optimized 7 0 state349 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check350 : optimized 7 0 state350 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check351 : optimized 7 0 state351 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check352 : optimized 7 0 state352 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check322 : optimized 8 1 state322 = false := by
  rw [optimized_expand]
  have hg : (state322 == [goal]) = false := by decide +kernel
  have he : expand 1 state322 = [(0, state323), (0, state324), (0, state325), (0, state326), (0, state327), (0, state328), (1, state329), (0, state330), (0, state331), (0, state332), (0, state333), (0, state334), (0, state335), (0, state336), (0, state337), (1, state338), (0, state339), (0, state340), (1, state341), (0, state342), (0, state343), (1, state344), (0, state345), (0, state346), (1, state347), (0, state348), (0, state349), (0, state350), (0, state351), (0, state352)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check323, check324, check325, check326, check327, check328, check329, check330, check331, check332, check333, check334, check335, check336, check337, check338, check339, check340, check341, check342, check343, check344, check345, check346, check347, check348, check349, check350, check351, check352]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check353 : optimized 8 0 state353 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check355 : optimized 7 0 state355 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check356 : optimized 7 0 state356 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check357 : optimized 7 0 state357 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check358 : optimized 7 0 state358 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check359 : optimized 7 0 state359 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check360 : optimized 7 0 state360 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check361 : optimized 7 0 state361 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check362 : optimized 7 0 state362 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check363 : optimized 7 0 state363 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check364 : optimized 7 0 state364 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check365 : optimized 7 0 state365 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check366 : optimized 7 0 state366 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check367 : optimized 7 0 state367 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check368 : optimized 7 0 state368 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check369 : optimized 7 0 state369 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check354 : optimized 8 0 state354 = false := by
  rw [optimized_expand]
  have hg : (state354 == [goal]) = false := by decide +kernel
  have he : expand 0 state354 = [(0, state355), (0, state356), (0, state357), (0, state358), (0, state359), (0, state360), (0, state361), (0, state362), (0, state363), (0, state364), (0, state365), (0, state366), (0, state367), (0, state368), (0, state369)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check355, check356, check357, check358, check359, check360, check361, check362, check363, check364, check365, check366, check367, check368, check369]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check370 : optimized 8 0 state370 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check372 : optimized 7 0 state372 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check373 : optimized 7 0 state373 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check374 : optimized 7 0 state374 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check375 : optimized 7 0 state375 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check376 : optimized 7 0 state376 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check377 : optimized 7 0 state377 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check378 : optimized 7 0 state378 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check379 : optimized 7 0 state379 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check380 : optimized 7 0 state380 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check381 : optimized 7 0 state381 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check382 : optimized 7 0 state382 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check383 : optimized 7 0 state383 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check384 : optimized 7 0 state384 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check385 : optimized 7 0 state385 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check386 : optimized 7 0 state386 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check371 : optimized 8 0 state371 = false := by
  rw [optimized_expand]
  have hg : (state371 == [goal]) = false := by decide +kernel
  have he : expand 0 state371 = [(0, state372), (0, state373), (0, state374), (0, state375), (0, state376), (0, state377), (0, state378), (0, state379), (0, state380), (0, state381), (0, state382), (0, state383), (0, state384), (0, state385), (0, state386)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check372, check373, check374, check375, check376, check377, check378, check379, check380, check381, check382, check383, check384, check385, check386]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check387 : optimized 8 0 state387 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check388 : optimized 8 0 state388 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check389 : optimized 8 0 state389 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check390 : optimized 8 0 state390 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check391 : optimized 8 0 state391 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check392 : optimized 8 0 state392 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check394 : optimized 7 0 state394 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check395 : optimized 7 0 state395 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check396 : optimized 7 0 state396 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check397 : optimized 7 0 state397 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check398 : optimized 7 1 state398 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check399 : optimized 7 0 state399 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check400 : optimized 7 0 state400 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check401 : optimized 7 0 state401 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check402 : optimized 7 0 state402 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check403 : optimized 7 0 state403 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check404 : optimized 7 0 state404 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check405 : optimized 7 0 state405 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check406 : optimized 7 0 state406 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check407 : optimized 7 0 state407 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check408 : optimized 7 0 state408 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check409 : optimized 7 0 state409 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check410 : optimized 7 1 state410 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check411 : optimized 7 0 state411 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check412 : optimized 7 0 state412 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check413 : optimized 7 2 state413 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check414 : optimized 7 1 state414 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check415 : optimized 7 1 state415 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check416 : optimized 7 0 state416 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check417 : optimized 7 0 state417 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check418 : optimized 7 0 state418 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check419 : optimized 7 0 state419 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check420 : optimized 7 0 state420 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check421 : optimized 7 0 state421 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check422 : optimized 7 0 state422 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check423 : optimized 7 0 state423 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check424 : optimized 7 0 state424 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check425 : optimized 7 0 state425 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check426 : optimized 7 0 state426 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check427 : optimized 7 0 state427 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check428 : optimized 7 1 state428 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check429 : optimized 7 0 state429 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check430 : optimized 7 0 state430 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check431 : optimized 7 2 state431 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check432 : optimized 7 1 state432 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check433 : optimized 7 1 state433 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check434 : optimized 7 0 state434 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check435 : optimized 7 0 state435 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check436 : optimized 7 1 state436 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check437 : optimized 7 0 state437 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check438 : optimized 7 0 state438 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check439 : optimized 7 2 state439 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check440 : optimized 7 1 state440 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check441 : optimized 7 1 state441 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check442 : optimized 7 0 state442 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check443 : optimized 7 0 state443 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check444 : optimized 7 0 state444 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check445 : optimized 7 0 state445 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check446 : optimized 7 0 state446 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check447 : optimized 7 0 state447 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check448 : optimized 7 0 state448 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check393 : optimized 8 2 state393 = false := by
  rw [optimized_expand]
  have hg : (state393 == [goal]) = false := by decide +kernel
  have he : expand 2 state393 = [(0, state394), (0, state395), (0, state396), (0, state397), (1, state398), (0, state399), (0, state400), (0, state401), (0, state402), (0, state403), (0, state404), (0, state405), (0, state406), (0, state407), (0, state408), (0, state409), (1, state410), (0, state411), (0, state412), (2, state413), (1, state414), (1, state415), (0, state416), (0, state417), (0, state418), (0, state419), (0, state420), (0, state421), (0, state422), (0, state423), (0, state424), (0, state425), (0, state426), (0, state427), (1, state428), (0, state429), (0, state430), (2, state431), (1, state432), (1, state433), (0, state434), (0, state435), (1, state436), (0, state437), (0, state438), (2, state439), (1, state440), (1, state441), (0, state442), (0, state443), (0, state444), (0, state445), (0, state446), (0, state447), (0, state448)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check394, check395, check396, check397, check398, check399, check400, check401, check402, check403, check404, check405, check406, check407, check408, check409, check410, check411, check412, check413, check414, check415, check416, check417, check418, check419, check420, check421, check422, check423, check424, check425, check426, check427, check428, check429, check430, check431, check432, check433, check434, check435, check436, check437, check438, check439, check440, check441, check442, check443, check444, check445, check446, check447, check448]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check450 : optimized 7 0 state450 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check451 : optimized 7 0 state451 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check452 : optimized 7 0 state452 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check453 : optimized 7 0 state453 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check454 : optimized 7 0 state454 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check455 : optimized 7 0 state455 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check456 : optimized 7 0 state456 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check457 : optimized 7 0 state457 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check458 : optimized 7 0 state458 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check459 : optimized 7 0 state459 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check460 : optimized 7 0 state460 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check461 : optimized 7 1 state461 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check462 : optimized 7 0 state462 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check463 : optimized 7 0 state463 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check464 : optimized 7 0 state464 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check465 : optimized 7 0 state465 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check466 : optimized 7 0 state466 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check467 : optimized 7 1 state467 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check468 : optimized 7 0 state468 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check469 : optimized 7 0 state469 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check470 : optimized 7 1 state470 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check471 : optimized 7 0 state471 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check472 : optimized 7 0 state472 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check473 : optimized 7 1 state473 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check474 : optimized 7 0 state474 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check475 : optimized 7 0 state475 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check476 : optimized 7 0 state476 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check477 : optimized 7 1 state477 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check478 : optimized 7 0 state478 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check479 : optimized 7 0 state479 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check449 : optimized 8 1 state449 = false := by
  rw [optimized_expand]
  have hg : (state449 == [goal]) = false := by decide +kernel
  have he : expand 1 state449 = [(0, state450), (0, state451), (0, state452), (0, state453), (0, state454), (0, state455), (0, state456), (0, state457), (0, state458), (0, state459), (0, state460), (1, state461), (0, state462), (0, state463), (0, state464), (0, state465), (0, state466), (1, state467), (0, state468), (0, state469), (1, state470), (0, state471), (0, state472), (1, state473), (0, state474), (0, state475), (0, state476), (1, state477), (0, state478), (0, state479)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check450, check451, check452, check453, check454, check455, check456, check457, check458, check459, check460, check461, check462, check463, check464, check465, check466, check467, check468, check469, check470, check471, check472, check473, check474, check475, check476, check477, check478, check479]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check481 : optimized 7 0 state481 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check482 : optimized 7 0 state482 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check483 : optimized 7 0 state483 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check484 : optimized 7 0 state484 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check485 : optimized 7 0 state485 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check486 : optimized 7 1 state486 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check487 : optimized 7 0 state487 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check488 : optimized 7 0 state488 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check489 : optimized 7 0 state489 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check490 : optimized 7 0 state490 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check491 : optimized 7 0 state491 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check492 : optimized 7 0 state492 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check493 : optimized 7 0 state493 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check494 : optimized 7 0 state494 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check495 : optimized 7 0 state495 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check496 : optimized 7 0 state496 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check497 : optimized 7 0 state497 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check498 : optimized 7 0 state498 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check499 : optimized 7 1 state499 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check500 : optimized 7 0 state500 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check501 : optimized 7 0 state501 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check502 : optimized 7 0 state502 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check503 : optimized 7 1 state503 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check504 : optimized 7 0 state504 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check505 : optimized 7 0 state505 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check506 : optimized 7 1 state506 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check507 : optimized 7 0 state507 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check508 : optimized 7 0 state508 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check509 : optimized 7 1 state509 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check510 : optimized 7 0 state510 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check511 : optimized 7 0 state511 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check480 : optimized 8 1 state480 = false := by
  rw [optimized_expand]
  have hg : (state480 == [goal]) = false := by decide +kernel
  have he : expand 1 state480 = [(0, state481), (0, state482), (0, state483), (0, state484), (0, state485), (1, state486), (0, state487), (0, state488), (1, state398), (0, state489), (0, state490), (0, state491), (0, state492), (0, state493), (0, state494), (0, state495), (0, state496), (0, state497), (0, state498), (1, state499), (0, state500), (0, state501), (0, state502), (1, state503), (0, state504), (0, state505), (1, state506), (0, state507), (0, state508), (1, state509), (0, state510), (0, state511)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check481, check482, check483, check484, check485, check486, check487, check488, check398, check489, check490, check491, check492, check493, check494, check495, check496, check497, check498, check499, check500, check501, check502, check503, check504, check505, check506, check507, check508, check509, check510, check511]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check513 : optimized 7 0 state513 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check514 : optimized 7 0 state514 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check515 : optimized 7 0 state515 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check516 : optimized 7 0 state516 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check517 : optimized 7 0 state517 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check518 : optimized 7 0 state518 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check519 : optimized 7 0 state519 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check520 : optimized 7 0 state520 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check521 : optimized 7 0 state521 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check512 : optimized 8 0 state512 = false := by
  rw [optimized_expand]
  have hg : (state512 == [goal]) = false := by decide +kernel
  have he : expand 0 state512 = [(0, state513), (0, state514), (0, state515), (0, state516), (0, state451), (0, state517), (0, state518), (0, state519), (0, state520), (0, state521)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check513, check514, check515, check516, check451, check517, check518, check519, check520, check521]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check523 : optimized 7 0 state523 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check524 : optimized 7 0 state524 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check525 : optimized 7 0 state525 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check526 : optimized 7 0 state526 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check527 : optimized 7 0 state527 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check528 : optimized 7 0 state528 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check529 : optimized 7 0 state529 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check530 : optimized 7 0 state530 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check531 : optimized 7 0 state531 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check532 : optimized 7 0 state532 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check533 : optimized 7 0 state533 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check534 : optimized 7 0 state534 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check535 : optimized 7 0 state535 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check536 : optimized 7 0 state536 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check537 : optimized 7 0 state537 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check522 : optimized 8 0 state522 = false := by
  rw [optimized_expand]
  have hg : (state522 == [goal]) = false := by decide +kernel
  have he : expand 0 state522 = [(0, state523), (0, state524), (0, state525), (0, state526), (0, state527), (0, state528), (0, state529), (0, state530), (0, state531), (0, state532), (0, state533), (0, state534), (0, state535), (0, state536), (0, state537)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check523, check524, check525, check526, check527, check528, check529, check530, check531, check532, check533, check534, check535, check536, check537]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check538 : optimized 8 0 state538 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check539 : optimized 8 0 state539 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check541 : optimized 7 0 state541 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check542 : optimized 7 0 state542 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check543 : optimized 7 0 state543 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check544 : optimized 7 0 state544 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check545 : optimized 7 0 state545 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check546 : optimized 7 0 state546 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check547 : optimized 7 0 state547 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check548 : optimized 7 0 state548 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check549 : optimized 7 0 state549 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check550 : optimized 7 0 state550 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check551 : optimized 7 0 state551 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check552 : optimized 7 0 state552 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check553 : optimized 7 0 state553 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check554 : optimized 7 0 state554 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check555 : optimized 7 0 state555 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check556 : optimized 7 1 state556 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check557 : optimized 7 0 state557 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check558 : optimized 7 0 state558 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check559 : optimized 7 0 state559 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check560 : optimized 7 0 state560 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check562 : optimized 6 0 state562 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check563 : optimized 6 0 state563 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check564 : optimized 6 0 state564 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check565 : optimized 6 0 state565 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check566 : optimized 6 0 state566 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check567 : optimized 6 1 state567 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check568 : optimized 6 0 state568 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check569 : optimized 6 0 state569 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check570 : optimized 6 2 state570 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check571 : optimized 6 1 state571 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check572 : optimized 6 1 state572 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check573 : optimized 6 0 state573 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check574 : optimized 6 1 state574 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check575 : optimized 6 0 state575 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check576 : optimized 6 0 state576 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check577 : optimized 6 0 state577 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check578 : optimized 6 1 state578 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check579 : optimized 6 0 state579 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check580 : optimized 6 0 state580 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check581 : optimized 6 0 state581 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check561 : optimized 7 2 state561 = false := by
  rw [optimized_expand]
  have hg : (state561 == [goal]) = false := by decide +kernel
  have he : expand 2 state561 = [(0, state562), (0, state563), (0, state150), (0, state151), (0, state152), (1, state153), (0, state154), (0, state155), (0, state156), (0, state157), (0, state158), (0, state142), (0, state143), (0, state144), (0, state145), (0, state146), (0, state147), (0, state148), (0, state149), (0, state564), (0, state565), (0, state566), (1, state567), (0, state568), (0, state569), (2, state570), (1, state571), (1, state572), (0, state573), (1, state574), (0, state575), (0, state576), (0, state577), (1, state578), (0, state579), (0, state580), (0, state581)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check562, check563, check150, check151, check152, check153, check154, check155, check156, check157, check158, check142, check143, check144, check145, check146, check147, check148, check149, check564, check565, check566, check567, check568, check569, check570, check571, check572, check573, check574, check575, check576, check577, check578, check579, check580, check581]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check582 : optimized 7 1 state582 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check583 : optimized 7 1 state583 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check584 : optimized 7 0 state584 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check585 : optimized 7 0 state585 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check586 : optimized 7 0 state586 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check587 : optimized 7 0 state587 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check588 : optimized 7 0 state588 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check589 : optimized 7 0 state589 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check590 : optimized 7 1 state590 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check591 : optimized 7 0 state591 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check592 : optimized 7 0 state592 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check593 : optimized 7 0 state593 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check594 : optimized 7 0 state594 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check596 : optimized 6 0 state596 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check597 : optimized 6 0 state597 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check598 : optimized 6 0 state598 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check599 : optimized 6 0 state599 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check600 : optimized 6 0 state600 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check601 : optimized 6 0 state601 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check602 : optimized 6 0 state602 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check603 : optimized 6 0 state603 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check604 : optimized 6 0 state604 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check605 : optimized 6 0 state605 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check606 : optimized 6 0 state606 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check607 : optimized 6 0 state607 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check608 : optimized 6 0 state608 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check609 : optimized 6 0 state609 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check610 : optimized 6 0 state610 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check611 : optimized 6 0 state611 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check612 : optimized 6 0 state612 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check613 : optimized 6 0 state613 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check614 : optimized 6 0 state614 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check615 : optimized 6 1 state615 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check616 : optimized 6 0 state616 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check617 : optimized 6 0 state617 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check618 : optimized 6 0 state618 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check619 : optimized 6 0 state619 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check620 : optimized 6 2 state620 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check621 : optimized 6 1 state621 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check622 : optimized 6 1 state622 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check623 : optimized 6 0 state623 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check624 : optimized 6 1 state624 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check625 : optimized 6 0 state625 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check626 : optimized 6 0 state626 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check627 : optimized 6 0 state627 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check628 : optimized 6 1 state628 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check629 : optimized 6 0 state629 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check630 : optimized 6 0 state630 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check631 : optimized 6 0 state631 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check595 : optimized 7 2 state595 = false := by
  rw [optimized_expand]
  have hg : (state595 == [goal]) = false := by decide +kernel
  have he : expand 2 state595 = [(0, state596), (0, state597), (0, state598), (0, state599), (0, state600), (0, state601), (0, state602), (0, state603), (0, state604), (0, state605), (0, state606), (0, state607), (0, state608), (0, state609), (0, state610), (0, state611), (0, state612), (0, state613), (0, state614), (1, state615), (0, state616), (0, state617), (0, state618), (0, state619), (2, state620), (1, state621), (1, state622), (0, state623), (1, state624), (0, state625), (0, state626), (0, state627), (1, state628), (0, state629), (0, state630), (0, state631)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check596, check597, check598, check599, check600, check601, check602, check603, check604, check605, check606, check607, check608, check609, check610, check611, check612, check613, check614, check615, check616, check617, check618, check619, check620, check621, check622, check623, check624, check625, check626, check627, check628, check629, check630, check631]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check632 : optimized 7 1 state632 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check633 : optimized 7 1 state633 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check634 : optimized 7 0 state634 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check636 : optimized 6 0 state636 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check637 : optimized 6 1 state637 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check638 : optimized 6 0 state638 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check639 : optimized 6 0 state639 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check640 : optimized 6 0 state640 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check641 : optimized 6 1 state641 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check642 : optimized 6 0 state642 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check643 : optimized 6 0 state643 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check644 : optimized 6 1 state644 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check645 : optimized 6 0 state645 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check646 : optimized 6 0 state646 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check647 : optimized 6 0 state647 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check648 : optimized 6 0 state648 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check649 : optimized 6 0 state649 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check650 : optimized 6 0 state650 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check651 : optimized 6 1 state651 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check652 : optimized 6 0 state652 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check653 : optimized 6 0 state653 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check654 : optimized 6 1 state654 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check655 : optimized 6 0 state655 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check656 : optimized 6 0 state656 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check635 : optimized 7 1 state635 = false := by
  rw [optimized_expand]
  have hg : (state635 == [goal]) = false := by decide +kernel
  have he : expand 1 state635 = [(0, state636), (1, state637), (0, state638), (0, state639), (0, state640), (1, state641), (0, state642), (0, state643), (1, state644), (0, state645), (0, state646), (0, state647), (0, state648), (0, state649), (0, state650), (1, state651), (0, state652), (0, state653), (1, state654), (0, state655), (0, state656)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check636, check637, check638, check639, check640, check641, check642, check643, check644, check645, check646, check647, check648, check649, check650, check651, check652, check653, check654, check655, check656]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check657 : optimized 7 0 state657 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check658 : optimized 7 0 state658 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check659 : optimized 7 0 state659 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check660 : optimized 7 1 state660 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check661 : optimized 7 0 state661 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check662 : optimized 7 0 state662 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check663 : optimized 7 1 state663 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check664 : optimized 7 0 state664 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check665 : optimized 7 0 state665 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check666 : optimized 7 0 state666 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check667 : optimized 7 0 state667 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check668 : optimized 7 0 state668 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check669 : optimized 7 0 state669 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check670 : optimized 7 0 state670 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check540 : optimized 8 2 state540 = false := by
  rw [optimized_expand]
  have hg : (state540 == [goal]) = false := by decide +kernel
  have he : expand 2 state540 = [(0, state541), (0, state542), (0, state543), (0, state544), (0, state545), (0, state546), (0, state547), (0, state548), (0, state549), (0, state550), (0, state551), (0, state552), (0, state553), (0, state554), (0, state555), (1, state556), (0, state557), (0, state558), (0, state559), (0, state560), (2, state561), (1, state582), (1, state583), (0, state584), (0, state585), (0, state586), (0, state587), (0, state588), (0, state589), (1, state590), (0, state591), (0, state592), (0, state593), (0, state594), (2, state595), (1, state632), (1, state633), (0, state634), (1, state635), (0, state657), (0, state658), (0, state659), (1, state660), (0, state661), (0, state662), (1, state663), (0, state664), (0, state665), (0, state666), (0, state667), (0, state668), (0, state669), (0, state670)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check541, check542, check543, check544, check545, check546, check547, check548, check549, check550, check551, check552, check553, check554, check555, check556, check557, check558, check559, check560, check561, check582, check583, check584, check585, check586, check587, check588, check589, check590, check591, check592, check593, check594, check595, check632, check633, check634, check635, check657, check658, check659, check660, check661, check662, check663, check664, check665, check666, check667, check668, check669, check670]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check672 : optimized 7 0 state672 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check673 : optimized 7 0 state673 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check674 : optimized 7 0 state674 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check675 : optimized 7 0 state675 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check676 : optimized 7 0 state676 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check677 : optimized 7 0 state677 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check678 : optimized 7 0 state678 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check679 : optimized 7 0 state679 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check680 : optimized 7 1 state680 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check681 : optimized 7 0 state681 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check682 : optimized 7 0 state682 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check683 : optimized 7 0 state683 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check684 : optimized 7 0 state684 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check685 : optimized 7 0 state685 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check686 : optimized 7 0 state686 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check687 : optimized 7 0 state687 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check688 : optimized 7 1 state688 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check689 : optimized 7 0 state689 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check690 : optimized 7 0 state690 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check691 : optimized 7 0 state691 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check692 : optimized 7 1 state692 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check693 : optimized 7 0 state693 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check694 : optimized 7 0 state694 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check695 : optimized 7 0 state695 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check696 : optimized 7 1 state696 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check697 : optimized 7 0 state697 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check698 : optimized 7 0 state698 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check699 : optimized 7 1 state699 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check700 : optimized 7 0 state700 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check701 : optimized 7 0 state701 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check671 : optimized 8 1 state671 = false := by
  rw [optimized_expand]
  have hg : (state671 == [goal]) = false := by decide +kernel
  have he : expand 1 state671 = [(0, state672), (0, state673), (0, state674), (0, state675), (0, state676), (0, state677), (0, state678), (0, state679), (1, state680), (0, state681), (0, state682), (0, state683), (0, state684), (0, state685), (0, state686), (0, state687), (1, state688), (0, state689), (0, state690), (0, state691), (1, state692), (0, state693), (0, state694), (0, state695), (1, state696), (0, state697), (0, state698), (1, state699), (0, state700), (0, state701)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check672, check673, check674, check675, check676, check677, check678, check679, check680, check681, check682, check683, check684, check685, check686, check687, check688, check689, check690, check691, check692, check693, check694, check695, check696, check697, check698, check699, check700, check701]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check703 : optimized 7 0 state703 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check704 : optimized 7 0 state704 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check705 : optimized 7 0 state705 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check706 : optimized 7 0 state706 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check707 : optimized 7 0 state707 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check708 : optimized 7 0 state708 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check709 : optimized 7 1 state709 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check710 : optimized 7 0 state710 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check711 : optimized 7 0 state711 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check712 : optimized 7 0 state712 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check713 : optimized 7 0 state713 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check714 : optimized 7 0 state714 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check715 : optimized 7 0 state715 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check716 : optimized 7 0 state716 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check717 : optimized 7 0 state717 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check718 : optimized 7 0 state718 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check719 : optimized 7 1 state719 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check720 : optimized 7 0 state720 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check721 : optimized 7 0 state721 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check722 : optimized 7 1 state722 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check723 : optimized 7 0 state723 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check724 : optimized 7 0 state724 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check725 : optimized 7 1 state725 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check726 : optimized 7 0 state726 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check727 : optimized 7 0 state727 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check728 : optimized 7 0 state728 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check729 : optimized 7 0 state729 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check730 : optimized 7 0 state730 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check702 : optimized 8 1 state702 = false := by
  rw [optimized_expand]
  have hg : (state702 == [goal]) = false := by decide +kernel
  have he : expand 1 state702 = [(0, state703), (0, state704), (0, state705), (0, state706), (0, state707), (0, state708), (1, state709), (0, state710), (0, state711), (0, state712), (0, state713), (0, state714), (0, state715), (0, state716), (0, state717), (0, state718), (1, state719), (0, state720), (0, state721), (1, state722), (0, state723), (0, state724), (1, state725), (0, state726), (0, state727), (0, state728), (0, state729), (0, state730)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check703, check704, check705, check706, check707, check708, check709, check710, check711, check712, check713, check714, check715, check716, check717, check718, check719, check720, check721, check722, check723, check724, check725, check726, check727, check728, check729, check730]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check731 : optimized 8 0 state731 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check733 : optimized 7 0 state733 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check734 : optimized 7 0 state734 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check735 : optimized 7 0 state735 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check736 : optimized 7 0 state736 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check737 : optimized 7 0 state737 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check738 : optimized 7 0 state738 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check739 : optimized 7 0 state739 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check740 : optimized 7 0 state740 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check741 : optimized 7 0 state741 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check742 : optimized 7 0 state742 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check743 : optimized 7 0 state743 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check744 : optimized 7 0 state744 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check745 : optimized 7 0 state745 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check746 : optimized 7 0 state746 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check747 : optimized 7 0 state747 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check732 : optimized 8 0 state732 = false := by
  rw [optimized_expand]
  have hg : (state732 == [goal]) = false := by decide +kernel
  have he : expand 0 state732 = [(0, state733), (0, state734), (0, state735), (0, state736), (0, state737), (0, state738), (0, state739), (0, state740), (0, state741), (0, state742), (0, state743), (0, state744), (0, state745), (0, state746), (0, state747)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check733, check734, check735, check736, check737, check738, check739, check740, check741, check742, check743, check744, check745, check746, check747]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check748 : optimized 8 0 state748 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check749 : optimized 8 0 state749 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check750 : optimized 8 0 state750 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check751 : optimized 8 0 state751 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check753 : optimized 7 0 state753 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check754 : optimized 7 0 state754 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check755 : optimized 7 0 state755 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check756 : optimized 7 0 state756 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check757 : optimized 7 1 state757 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check758 : optimized 7 0 state758 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check759 : optimized 7 0 state759 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check760 : optimized 7 0 state760 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check761 : optimized 7 0 state761 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check762 : optimized 7 0 state762 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check763 : optimized 7 0 state763 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check764 : optimized 7 0 state764 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check765 : optimized 7 0 state765 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check766 : optimized 7 0 state766 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check767 : optimized 7 0 state767 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check768 : optimized 7 0 state768 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check769 : optimized 7 1 state769 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check770 : optimized 7 0 state770 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check771 : optimized 7 0 state771 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check772 : optimized 7 2 state772 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check773 : optimized 7 1 state773 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check774 : optimized 7 1 state774 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check775 : optimized 7 0 state775 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check776 : optimized 7 0 state776 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check777 : optimized 7 0 state777 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check778 : optimized 7 0 state778 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check779 : optimized 7 0 state779 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check780 : optimized 7 0 state780 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check781 : optimized 7 0 state781 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check782 : optimized 7 0 state782 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check783 : optimized 7 0 state783 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check784 : optimized 7 0 state784 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check785 : optimized 7 1 state785 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check786 : optimized 7 0 state786 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check787 : optimized 7 0 state787 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check788 : optimized 7 0 state788 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check789 : optimized 7 0 state789 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check790 : optimized 7 2 state790 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check791 : optimized 7 1 state791 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check792 : optimized 7 1 state792 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check793 : optimized 7 0 state793 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check794 : optimized 7 0 state794 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check795 : optimized 7 2 state795 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check796 : optimized 7 1 state796 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check797 : optimized 7 1 state797 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check798 : optimized 7 0 state798 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check799 : optimized 7 0 state799 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check800 : optimized 7 1 state800 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check801 : optimized 7 0 state801 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check802 : optimized 7 0 state802 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check803 : optimized 7 0 state803 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check804 : optimized 7 0 state804 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check805 : optimized 7 0 state805 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check806 : optimized 7 0 state806 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check807 : optimized 7 0 state807 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check752 : optimized 8 2 state752 = false := by
  rw [optimized_expand]
  have hg : (state752 == [goal]) = false := by decide +kernel
  have he : expand 2 state752 = [(0, state753), (0, state754), (0, state755), (0, state756), (1, state757), (0, state758), (0, state759), (0, state760), (0, state761), (0, state762), (0, state763), (0, state764), (0, state765), (0, state766), (0, state767), (0, state768), (1, state769), (0, state770), (0, state771), (2, state772), (1, state773), (1, state774), (0, state775), (0, state776), (0, state777), (0, state778), (0, state779), (0, state780), (0, state781), (0, state782), (0, state783), (0, state784), (1, state785), (0, state786), (0, state787), (0, state788), (0, state789), (2, state790), (1, state791), (1, state792), (0, state793), (0, state794), (2, state795), (1, state796), (1, state797), (0, state798), (0, state799), (1, state800), (0, state801), (0, state802), (0, state803), (0, state804), (0, state805), (0, state806), (0, state807)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check753, check754, check755, check756, check757, check758, check759, check760, check761, check762, check763, check764, check765, check766, check767, check768, check769, check770, check771, check772, check773, check774, check775, check776, check777, check778, check779, check780, check781, check782, check783, check784, check785, check786, check787, check788, check789, check790, check791, check792, check793, check794, check795, check796, check797, check798, check799, check800, check801, check802, check803, check804, check805, check806, check807]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check809 : optimized 7 0 state809 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check810 : optimized 7 0 state810 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check811 : optimized 7 0 state811 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check812 : optimized 7 0 state812 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check813 : optimized 7 0 state813 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check814 : optimized 7 0 state814 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check815 : optimized 7 0 state815 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check816 : optimized 7 0 state816 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check817 : optimized 7 0 state817 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check818 : optimized 7 0 state818 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check819 : optimized 7 0 state819 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check820 : optimized 7 0 state820 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check821 : optimized 7 0 state821 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check822 : optimized 7 1 state822 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check823 : optimized 7 0 state823 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check824 : optimized 7 0 state824 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check825 : optimized 7 0 state825 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check826 : optimized 7 1 state826 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check827 : optimized 7 0 state827 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check828 : optimized 7 0 state828 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check829 : optimized 7 1 state829 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check830 : optimized 7 0 state830 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check831 : optimized 7 0 state831 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check832 : optimized 7 1 state832 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check833 : optimized 7 0 state833 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check834 : optimized 7 0 state834 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check835 : optimized 7 1 state835 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check836 : optimized 7 0 state836 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check837 : optimized 7 0 state837 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check838 : optimized 7 0 state838 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check808 : optimized 8 1 state808 = false := by
  rw [optimized_expand]
  have hg : (state808 == [goal]) = false := by decide +kernel
  have he : expand 1 state808 = [(0, state809), (0, state810), (0, state811), (0, state812), (0, state813), (0, state814), (0, state815), (0, state816), (0, state817), (0, state818), (0, state819), (0, state820), (0, state821), (1, state822), (0, state823), (0, state824), (0, state825), (1, state826), (0, state827), (0, state828), (1, state829), (0, state830), (0, state831), (1, state832), (0, state833), (0, state834), (1, state835), (0, state836), (0, state837), (0, state838)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check809, check810, check811, check812, check813, check814, check815, check816, check817, check818, check819, check820, check821, check822, check823, check824, check825, check826, check827, check828, check829, check830, check831, check832, check833, check834, check835, check836, check837, check838]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check840 : optimized 7 0 state840 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check841 : optimized 7 0 state841 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check842 : optimized 7 0 state842 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check843 : optimized 7 0 state843 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check844 : optimized 7 0 state844 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check845 : optimized 7 1 state845 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check846 : optimized 7 0 state846 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check847 : optimized 7 0 state847 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check848 : optimized 7 0 state848 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check849 : optimized 7 0 state849 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check850 : optimized 7 0 state850 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check851 : optimized 7 0 state851 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check852 : optimized 7 0 state852 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check853 : optimized 7 0 state853 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check854 : optimized 7 0 state854 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check855 : optimized 7 0 state855 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check856 : optimized 7 0 state856 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check857 : optimized 7 0 state857 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check858 : optimized 7 1 state858 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check859 : optimized 7 0 state859 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check860 : optimized 7 0 state860 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check861 : optimized 7 0 state861 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check862 : optimized 7 1 state862 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check863 : optimized 7 0 state863 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check864 : optimized 7 0 state864 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check865 : optimized 7 1 state865 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check866 : optimized 7 0 state866 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check867 : optimized 7 0 state867 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check868 : optimized 7 1 state868 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check869 : optimized 7 0 state869 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check870 : optimized 7 0 state870 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check839 : optimized 8 1 state839 = false := by
  rw [optimized_expand]
  have hg : (state839 == [goal]) = false := by decide +kernel
  have he : expand 1 state839 = [(0, state840), (0, state841), (0, state842), (0, state843), (0, state844), (1, state845), (0, state846), (0, state847), (1, state757), (0, state848), (0, state849), (0, state850), (0, state851), (0, state852), (0, state853), (0, state854), (0, state855), (0, state856), (0, state857), (1, state858), (0, state859), (0, state860), (0, state861), (1, state862), (0, state863), (0, state864), (1, state865), (0, state866), (0, state867), (1, state868), (0, state869), (0, state870)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check840, check841, check842, check843, check844, check845, check846, check847, check757, check848, check849, check850, check851, check852, check853, check854, check855, check856, check857, check858, check859, check860, check861, check862, check863, check864, check865, check866, check867, check868, check869, check870]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check872 : optimized 7 0 state872 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check873 : optimized 7 0 state873 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check874 : optimized 7 0 state874 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check875 : optimized 7 0 state875 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check876 : optimized 7 0 state876 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check877 : optimized 7 0 state877 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check878 : optimized 7 0 state878 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check879 : optimized 7 0 state879 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check880 : optimized 7 0 state880 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check871 : optimized 8 0 state871 = false := by
  rw [optimized_expand]
  have hg : (state871 == [goal]) = false := by decide +kernel
  have he : expand 0 state871 = [(0, state872), (0, state873), (0, state874), (0, state875), (0, state810), (0, state876), (0, state877), (0, state878), (0, state879), (0, state880)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check872, check873, check874, check875, check810, check876, check877, check878, check879, check880]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check882 : optimized 7 0 state882 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check883 : optimized 7 0 state883 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check884 : optimized 7 0 state884 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check885 : optimized 7 0 state885 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check886 : optimized 7 0 state886 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check887 : optimized 7 0 state887 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check888 : optimized 7 0 state888 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check889 : optimized 7 0 state889 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check890 : optimized 7 0 state890 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check891 : optimized 7 0 state891 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check892 : optimized 7 0 state892 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check893 : optimized 7 0 state893 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check894 : optimized 7 0 state894 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check895 : optimized 7 0 state895 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check896 : optimized 7 0 state896 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check881 : optimized 8 0 state881 = false := by
  rw [optimized_expand]
  have hg : (state881 == [goal]) = false := by decide +kernel
  have he : expand 0 state881 = [(0, state882), (0, state883), (0, state884), (0, state885), (0, state886), (0, state887), (0, state888), (0, state889), (0, state890), (0, state891), (0, state892), (0, state893), (0, state894), (0, state895), (0, state896)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check882, check883, check884, check885, check886, check887, check888, check889, check890, check891, check892, check893, check894, check895, check896]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check897 : optimized 8 0 state897 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check899 : optimized 7 0 state899 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check900 : optimized 7 0 state900 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check901 : optimized 7 0 state901 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check902 : optimized 7 0 state902 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check903 : optimized 7 0 state903 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check904 : optimized 7 0 state904 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check905 : optimized 7 0 state905 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check906 : optimized 7 0 state906 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check907 : optimized 7 0 state907 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check908 : optimized 7 0 state908 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check909 : optimized 7 0 state909 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check910 : optimized 7 0 state910 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check911 : optimized 7 0 state911 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check912 : optimized 7 0 state912 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check913 : optimized 7 0 state913 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check898 : optimized 8 0 state898 = false := by
  rw [optimized_expand]
  have hg : (state898 == [goal]) = false := by decide +kernel
  have he : expand 0 state898 = [(0, state899), (0, state900), (0, state901), (0, state902), (0, state903), (0, state904), (0, state905), (0, state906), (0, state907), (0, state908), (0, state909), (0, state910), (0, state911), (0, state912), (0, state913)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check899, check900, check901, check902, check903, check904, check905, check906, check907, check908, check909, check910, check911, check912, check913]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check914 : optimized 8 0 state914 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check915 : optimized 8 0 state915 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check917 : optimized 7 0 state917 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check918 : optimized 7 0 state918 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check919 : optimized 7 0 state919 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check920 : optimized 7 0 state920 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check921 : optimized 7 0 state921 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check922 : optimized 7 0 state922 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check923 : optimized 7 0 state923 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check924 : optimized 7 0 state924 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check925 : optimized 7 0 state925 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check926 : optimized 7 0 state926 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check927 : optimized 7 0 state927 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check928 : optimized 7 0 state928 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check929 : optimized 7 0 state929 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check930 : optimized 7 0 state930 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check931 : optimized 7 0 state931 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check932 : optimized 7 1 state932 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check933 : optimized 7 0 state933 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check934 : optimized 7 0 state934 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check935 : optimized 7 0 state935 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check936 : optimized 7 0 state936 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check938 : optimized 6 0 state938 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check939 : optimized 6 0 state939 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check940 : optimized 6 0 state940 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check941 : optimized 6 0 state941 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check942 : optimized 6 0 state942 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check943 : optimized 6 1 state943 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check944 : optimized 6 0 state944 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check945 : optimized 6 0 state945 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check946 : optimized 6 2 state946 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check947 : optimized 6 1 state947 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check948 : optimized 6 1 state948 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check949 : optimized 6 0 state949 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check950 : optimized 6 1 state950 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check951 : optimized 6 0 state951 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check952 : optimized 6 0 state952 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check953 : optimized 6 0 state953 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check954 : optimized 6 1 state954 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check955 : optimized 6 0 state955 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check956 : optimized 6 0 state956 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check957 : optimized 6 0 state957 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check937 : optimized 7 2 state937 = false := by
  rw [optimized_expand]
  have hg : (state937 == [goal]) = false := by decide +kernel
  have he : expand 2 state937 = [(0, state938), (0, state939), (0, state203), (0, state204), (0, state205), (1, state206), (0, state207), (0, state208), (0, state209), (0, state210), (0, state211), (0, state195), (0, state196), (0, state197), (0, state198), (0, state199), (0, state200), (0, state201), (0, state202), (0, state940), (0, state941), (0, state942), (1, state943), (0, state944), (0, state945), (2, state946), (1, state947), (1, state948), (0, state949), (1, state950), (0, state951), (0, state952), (0, state953), (1, state954), (0, state955), (0, state956), (0, state957)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check938, check939, check203, check204, check205, check206, check207, check208, check209, check210, check211, check195, check196, check197, check198, check199, check200, check201, check202, check940, check941, check942, check943, check944, check945, check946, check947, check948, check949, check950, check951, check952, check953, check954, check955, check956, check957]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check958 : optimized 7 1 state958 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check959 : optimized 7 1 state959 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check960 : optimized 7 0 state960 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check961 : optimized 7 0 state961 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check962 : optimized 7 0 state962 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check963 : optimized 7 0 state963 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check964 : optimized 7 0 state964 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check965 : optimized 7 0 state965 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check966 : optimized 7 1 state966 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check967 : optimized 7 0 state967 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check968 : optimized 7 0 state968 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check969 : optimized 7 0 state969 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check970 : optimized 7 0 state970 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check972 : optimized 6 0 state972 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check973 : optimized 6 0 state973 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check974 : optimized 6 0 state974 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check975 : optimized 6 1 state975 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check976 : optimized 6 0 state976 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check977 : optimized 6 0 state977 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check978 : optimized 6 0 state978 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check979 : optimized 6 0 state979 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check980 : optimized 6 2 state980 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check981 : optimized 6 1 state981 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check982 : optimized 6 1 state982 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check983 : optimized 6 0 state983 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check984 : optimized 6 1 state984 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check985 : optimized 6 0 state985 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check986 : optimized 6 0 state986 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check987 : optimized 6 0 state987 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check988 : optimized 6 1 state988 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check989 : optimized 6 0 state989 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check990 : optimized 6 0 state990 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check991 : optimized 6 0 state991 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check971 : optimized 7 2 state971 = false := by
  rw [optimized_expand]
  have hg : (state971 == [goal]) = false := by decide +kernel
  have he : expand 2 state971 = [(0, state972), (0, state973), (0, state606), (0, state607), (0, state608), (0, state609), (0, state610), (0, state611), (0, state612), (0, state613), (0, state598), (0, state599), (0, state600), (0, state601), (0, state602), (0, state603), (0, state604), (0, state605), (0, state974), (1, state975), (0, state976), (0, state977), (0, state978), (0, state979), (2, state980), (1, state981), (1, state982), (0, state983), (1, state984), (0, state985), (0, state986), (0, state987), (1, state988), (0, state989), (0, state990), (0, state991)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check972, check973, check606, check607, check608, check609, check610, check611, check612, check613, check598, check599, check600, check601, check602, check603, check604, check605, check974, check975, check976, check977, check978, check979, check980, check981, check982, check983, check984, check985, check986, check987, check988, check989, check990, check991]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check992 : optimized 7 1 state992 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check993 : optimized 7 1 state993 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check994 : optimized 7 0 state994 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check996 : optimized 6 0 state996 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check997 : optimized 6 1 state997 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check998 : optimized 6 0 state998 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check999 : optimized 6 0 state999 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1000 : optimized 6 0 state1000 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1001 : optimized 6 1 state1001 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1002 : optimized 6 0 state1002 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1003 : optimized 6 0 state1003 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1004 : optimized 6 1 state1004 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1005 : optimized 6 0 state1005 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1006 : optimized 6 0 state1006 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1007 : optimized 6 0 state1007 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1008 : optimized 6 0 state1008 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1009 : optimized 6 0 state1009 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1010 : optimized 6 0 state1010 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1011 : optimized 6 1 state1011 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1012 : optimized 6 0 state1012 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1013 : optimized 6 0 state1013 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1014 : optimized 6 1 state1014 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1015 : optimized 6 0 state1015 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1016 : optimized 6 0 state1016 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check995 : optimized 7 1 state995 = false := by
  rw [optimized_expand]
  have hg : (state995 == [goal]) = false := by decide +kernel
  have he : expand 1 state995 = [(0, state996), (1, state997), (0, state998), (0, state999), (0, state1000), (1, state1001), (0, state1002), (0, state1003), (1, state1004), (0, state1005), (0, state1006), (0, state1007), (0, state1008), (0, state1009), (0, state1010), (1, state1011), (0, state1012), (0, state1013), (1, state1014), (0, state1015), (0, state1016)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check996, check997, check998, check999, check1000, check1001, check1002, check1003, check1004, check1005, check1006, check1007, check1008, check1009, check1010, check1011, check1012, check1013, check1014, check1015, check1016]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1017 : optimized 7 0 state1017 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1018 : optimized 7 0 state1018 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1019 : optimized 7 0 state1019 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1020 : optimized 7 1 state1020 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1021 : optimized 7 0 state1021 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1022 : optimized 7 0 state1022 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1023 : optimized 7 1 state1023 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1024 : optimized 7 0 state1024 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1025 : optimized 7 0 state1025 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1026 : optimized 7 0 state1026 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1027 : optimized 7 0 state1027 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1028 : optimized 7 0 state1028 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1029 : optimized 7 0 state1029 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1030 : optimized 7 0 state1030 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check916 : optimized 8 2 state916 = false := by
  rw [optimized_expand]
  have hg : (state916 == [goal]) = false := by decide +kernel
  have he : expand 2 state916 = [(0, state917), (0, state918), (0, state919), (0, state920), (0, state921), (0, state922), (0, state923), (0, state924), (0, state925), (0, state926), (0, state927), (0, state928), (0, state929), (0, state930), (0, state931), (1, state932), (0, state933), (0, state934), (0, state935), (0, state936), (2, state937), (1, state958), (1, state959), (0, state960), (0, state961), (0, state962), (0, state963), (0, state964), (0, state965), (1, state966), (0, state967), (0, state968), (0, state969), (0, state970), (2, state971), (1, state992), (1, state993), (0, state994), (1, state995), (0, state1017), (0, state1018), (0, state1019), (1, state1020), (0, state1021), (0, state1022), (1, state1023), (0, state1024), (0, state1025), (0, state1026), (0, state1027), (0, state1028), (0, state1029), (0, state1030)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check917, check918, check919, check920, check921, check922, check923, check924, check925, check926, check927, check928, check929, check930, check931, check932, check933, check934, check935, check936, check937, check958, check959, check960, check961, check962, check963, check964, check965, check966, check967, check968, check969, check970, check971, check992, check993, check994, check995, check1017, check1018, check1019, check1020, check1021, check1022, check1023, check1024, check1025, check1026, check1027, check1028, check1029, check1030]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1032 : optimized 7 0 state1032 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1033 : optimized 7 0 state1033 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1034 : optimized 7 0 state1034 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1035 : optimized 7 0 state1035 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1036 : optimized 7 0 state1036 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1037 : optimized 7 0 state1037 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1038 : optimized 7 0 state1038 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1039 : optimized 7 0 state1039 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1040 : optimized 7 1 state1040 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1041 : optimized 7 0 state1041 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1042 : optimized 7 0 state1042 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1043 : optimized 7 0 state1043 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1044 : optimized 7 0 state1044 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1045 : optimized 7 0 state1045 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1046 : optimized 7 0 state1046 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1047 : optimized 7 0 state1047 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1048 : optimized 7 1 state1048 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1049 : optimized 7 0 state1049 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1050 : optimized 7 0 state1050 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1051 : optimized 7 0 state1051 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1052 : optimized 7 1 state1052 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1053 : optimized 7 0 state1053 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1054 : optimized 7 0 state1054 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1055 : optimized 7 0 state1055 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1056 : optimized 7 1 state1056 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1057 : optimized 7 0 state1057 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1058 : optimized 7 0 state1058 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1059 : optimized 7 1 state1059 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1060 : optimized 7 0 state1060 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1061 : optimized 7 0 state1061 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1031 : optimized 8 1 state1031 = false := by
  rw [optimized_expand]
  have hg : (state1031 == [goal]) = false := by decide +kernel
  have he : expand 1 state1031 = [(0, state1032), (0, state1033), (0, state1034), (0, state1035), (0, state1036), (0, state1037), (0, state1038), (0, state1039), (1, state1040), (0, state1041), (0, state1042), (0, state1043), (0, state1044), (0, state1045), (0, state1046), (0, state1047), (1, state1048), (0, state1049), (0, state1050), (0, state1051), (1, state1052), (0, state1053), (0, state1054), (0, state1055), (1, state1056), (0, state1057), (0, state1058), (1, state1059), (0, state1060), (0, state1061)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check1032, check1033, check1034, check1035, check1036, check1037, check1038, check1039, check1040, check1041, check1042, check1043, check1044, check1045, check1046, check1047, check1048, check1049, check1050, check1051, check1052, check1053, check1054, check1055, check1056, check1057, check1058, check1059, check1060, check1061]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1063 : optimized 7 0 state1063 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1064 : optimized 7 0 state1064 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1065 : optimized 7 0 state1065 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1066 : optimized 7 0 state1066 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1067 : optimized 7 0 state1067 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1068 : optimized 7 0 state1068 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1069 : optimized 7 1 state1069 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1070 : optimized 7 0 state1070 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1071 : optimized 7 0 state1071 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1072 : optimized 7 0 state1072 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1073 : optimized 7 0 state1073 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1074 : optimized 7 0 state1074 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1075 : optimized 7 0 state1075 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1076 : optimized 7 0 state1076 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1077 : optimized 7 0 state1077 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1078 : optimized 7 0 state1078 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1079 : optimized 7 1 state1079 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1080 : optimized 7 0 state1080 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1081 : optimized 7 0 state1081 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1082 : optimized 7 1 state1082 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1083 : optimized 7 0 state1083 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1084 : optimized 7 0 state1084 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1085 : optimized 7 1 state1085 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1086 : optimized 7 0 state1086 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1087 : optimized 7 0 state1087 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1088 : optimized 7 0 state1088 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1089 : optimized 7 0 state1089 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1090 : optimized 7 0 state1090 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1062 : optimized 8 1 state1062 = false := by
  rw [optimized_expand]
  have hg : (state1062 == [goal]) = false := by decide +kernel
  have he : expand 1 state1062 = [(0, state1063), (0, state1064), (0, state1065), (0, state1066), (0, state1067), (0, state1068), (1, state1069), (0, state1070), (0, state1071), (0, state1072), (0, state1073), (0, state1074), (0, state1075), (0, state1076), (0, state1077), (0, state1078), (1, state1079), (0, state1080), (0, state1081), (1, state1082), (0, state1083), (0, state1084), (1, state1085), (0, state1086), (0, state1087), (0, state1088), (0, state1089), (0, state1090)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check1063, check1064, check1065, check1066, check1067, check1068, check1069, check1070, check1071, check1072, check1073, check1074, check1075, check1076, check1077, check1078, check1079, check1080, check1081, check1082, check1083, check1084, check1085, check1086, check1087, check1088, check1089, check1090]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1091 : optimized 8 0 state1091 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1094 : optimized 6 0 state1094 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1095 : optimized 6 0 state1095 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1096 : optimized 6 0 state1096 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1097 : optimized 6 1 state1097 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1098 : optimized 6 0 state1098 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1099 : optimized 6 0 state1099 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1100 : optimized 6 1 state1100 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1101 : optimized 6 0 state1101 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1102 : optimized 6 0 state1102 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1103 : optimized 6 0 state1103 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1104 : optimized 6 0 state1104 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1105 : optimized 6 1 state1105 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1106 : optimized 6 0 state1106 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1107 : optimized 6 0 state1107 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1108 : optimized 6 1 state1108 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1109 : optimized 6 0 state1109 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1110 : optimized 6 0 state1110 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1093 : optimized 7 1 state1093 = false := by
  rw [optimized_expand]
  have hg : (state1093 == [goal]) = false := by decide +kernel
  have he : expand 1 state1093 = [(0, state1094), (1, state234), (0, state1095), (0, state1096), (1, state1097), (0, state1098), (0, state1099), (1, state1100), (0, state1101), (0, state1102), (0, state1103), (0, state1104), (1, state1105), (0, state1106), (0, state1107), (1, state1108), (0, state1109), (0, state1110)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check1094, check234, check1095, check1096, check1097, check1098, check1099, check1100, check1101, check1102, check1103, check1104, check1105, check1106, check1107, check1108, check1109, check1110]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1111 : optimized 7 0 state1111 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1112 : optimized 7 0 state1112 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1113 : optimized 7 0 state1113 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1114 : optimized 7 0 state1114 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1115 : optimized 7 1 state1115 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1116 : optimized 7 0 state1116 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1117 : optimized 7 0 state1117 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1118 : optimized 7 1 state1118 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1119 : optimized 7 0 state1119 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1120 : optimized 7 0 state1120 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1121 : optimized 7 1 state1121 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1122 : optimized 7 0 state1122 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1123 : optimized 7 0 state1123 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1124 : optimized 7 0 state1124 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1125 : optimized 7 1 state1125 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1126 : optimized 7 0 state1126 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1127 : optimized 7 0 state1127 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1128 : optimized 7 1 state1128 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1129 : optimized 7 0 state1129 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1130 : optimized 7 0 state1130 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1131 : optimized 7 0 state1131 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1132 : optimized 7 0 state1132 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1134 : optimized 6 0 state1134 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1135 : optimized 6 0 state1135 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1136 : optimized 6 1 state1136 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1137 : optimized 6 0 state1137 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1138 : optimized 6 0 state1138 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1139 : optimized 6 1 state1139 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1140 : optimized 6 0 state1140 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1141 : optimized 6 0 state1141 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1142 : optimized 6 1 state1142 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1143 : optimized 6 0 state1143 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1144 : optimized 6 0 state1144 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1145 : optimized 6 1 state1145 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1146 : optimized 6 0 state1146 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1147 : optimized 6 0 state1147 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1148 : optimized 6 0 state1148 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1149 : optimized 6 0 state1149 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1150 : optimized 6 1 state1150 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1151 : optimized 6 0 state1151 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1152 : optimized 6 0 state1152 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1153 : optimized 6 1 state1153 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1154 : optimized 6 0 state1154 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1155 : optimized 6 0 state1155 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1133 : optimized 7 1 state1133 = false := by
  rw [optimized_expand]
  have hg : (state1133 == [goal]) = false := by decide +kernel
  have he : expand 1 state1133 = [(1, state234), (0, state236), (0, state235), (0, state245), (0, state1134), (0, state1135), (1, state1136), (0, state1137), (0, state1138), (1, state1139), (0, state1140), (0, state1141), (1, state1142), (0, state1143), (0, state1144), (1, state1145), (0, state1146), (0, state1147), (0, state1148), (0, state1149), (1, state1150), (0, state1151), (0, state1152), (1, state1153), (0, state1154), (0, state1155)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check234, check236, check235, check245, check1134, check1135, check1136, check1137, check1138, check1139, check1140, check1141, check1142, check1143, check1144, check1145, check1146, check1147, check1148, check1149, check1150, check1151, check1152, check1153, check1154, check1155]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1156 : optimized 7 0 state1156 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1157 : optimized 7 0 state1157 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1159 : optimized 6 1 state1159 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1160 : optimized 6 0 state1160 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1161 : optimized 6 0 state1161 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1162 : optimized 6 0 state1162 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1163 : optimized 6 1 state1163 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1164 : optimized 6 0 state1164 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1165 : optimized 6 0 state1165 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1166 : optimized 6 1 state1166 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1167 : optimized 6 0 state1167 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1168 : optimized 6 0 state1168 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1169 : optimized 6 0 state1169 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1170 : optimized 6 0 state1170 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1171 : optimized 6 0 state1171 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1172 : optimized 6 1 state1172 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1173 : optimized 6 0 state1173 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1174 : optimized 6 0 state1174 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1175 : optimized 6 1 state1175 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1176 : optimized 6 0 state1176 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1177 : optimized 6 0 state1177 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1158 : optimized 7 1 state1158 = false := by
  rw [optimized_expand]
  have hg : (state1158 == [goal]) = false := by decide +kernel
  have he : expand 1 state1158 = [(0, state636), (0, state647), (1, state1159), (0, state1160), (0, state1161), (0, state1162), (1, state1163), (0, state1164), (0, state1165), (1, state1166), (0, state1167), (0, state1168), (0, state1169), (0, state1170), (0, state1171), (1, state1172), (0, state1173), (0, state1174), (1, state1175), (0, state1176), (0, state1177)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check636, check647, check1159, check1160, check1161, check1162, check1163, check1164, check1165, check1166, check1167, check1168, check1169, check1170, check1171, check1172, check1173, check1174, check1175, check1176, check1177]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1178 : optimized 7 0 state1178 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1179 : optimized 7 0 state1179 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1181 : optimized 6 1 state1181 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1182 : optimized 6 0 state1182 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1183 : optimized 6 0 state1183 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1184 : optimized 6 0 state1184 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1185 : optimized 6 1 state1185 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1186 : optimized 6 0 state1186 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1187 : optimized 6 0 state1187 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1188 : optimized 6 1 state1188 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1189 : optimized 6 0 state1189 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1190 : optimized 6 0 state1190 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1191 : optimized 6 0 state1191 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1192 : optimized 6 0 state1192 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1193 : optimized 6 0 state1193 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1194 : optimized 6 1 state1194 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1195 : optimized 6 0 state1195 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1196 : optimized 6 0 state1196 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1197 : optimized 6 1 state1197 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1198 : optimized 6 0 state1198 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1199 : optimized 6 0 state1199 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1180 : optimized 7 1 state1180 = false := by
  rw [optimized_expand]
  have hg : (state1180 == [goal]) = false := by decide +kernel
  have he : expand 1 state1180 = [(0, state996), (0, state1007), (1, state1181), (0, state1182), (0, state1183), (0, state1184), (1, state1185), (0, state1186), (0, state1187), (1, state1188), (0, state1189), (0, state1190), (0, state1191), (0, state1192), (0, state1193), (1, state1194), (0, state1195), (0, state1196), (1, state1197), (0, state1198), (0, state1199)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check996, check1007, check1181, check1182, check1183, check1184, check1185, check1186, check1187, check1188, check1189, check1190, check1191, check1192, check1193, check1194, check1195, check1196, check1197, check1198, check1199]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1200 : optimized 7 0 state1200 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1201 : optimized 7 0 state1201 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1092 : optimized 8 1 state1092 = false := by
  rw [optimized_expand]
  have hg : (state1092 == [goal]) = false := by decide +kernel
  have he : expand 1 state1092 = [(1, state1093), (0, state1111), (0, state1112), (0, state1113), (0, state1114), (1, state1115), (0, state1116), (0, state1117), (1, state1118), (0, state1119), (0, state1120), (1, state1121), (0, state1122), (0, state1123), (0, state1124), (1, state1125), (0, state1126), (0, state1127), (1, state1128), (0, state1129), (0, state1130), (0, state1131), (0, state1132), (1, state1133), (0, state1156), (0, state1157), (1, state1158), (0, state1178), (0, state1179), (1, state1180), (0, state1200), (0, state1201)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check1093, check1111, check1112, check1113, check1114, check1115, check1116, check1117, check1118, check1119, check1120, check1121, check1122, check1123, check1124, check1125, check1126, check1127, check1128, check1129, check1130, check1131, check1132, check1133, check1156, check1157, check1158, check1178, check1179, check1180, check1200, check1201]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1203 : optimized 7 0 state1203 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1204 : optimized 7 0 state1204 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1205 : optimized 7 0 state1205 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1206 : optimized 7 0 state1206 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1207 : optimized 7 0 state1207 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1208 : optimized 7 0 state1208 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1209 : optimized 7 0 state1209 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1210 : optimized 7 0 state1210 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1211 : optimized 7 0 state1211 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1212 : optimized 7 0 state1212 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1213 : optimized 7 0 state1213 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1214 : optimized 7 0 state1214 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1215 : optimized 7 0 state1215 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1216 : optimized 7 0 state1216 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1217 : optimized 7 0 state1217 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1202 : optimized 8 0 state1202 = false := by
  rw [optimized_expand]
  have hg : (state1202 == [goal]) = false := by decide +kernel
  have he : expand 0 state1202 = [(0, state1203), (0, state1204), (0, state1205), (0, state1206), (0, state1207), (0, state1208), (0, state1209), (0, state1210), (0, state1211), (0, state1212), (0, state1213), (0, state1214), (0, state1215), (0, state1216), (0, state1217)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check1203, check1204, check1205, check1206, check1207, check1208, check1209, check1210, check1211, check1212, check1213, check1214, check1215, check1216, check1217]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1218 : optimized 8 0 state1218 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1219 : optimized 8 0 state1219 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1221 : optimized 7 0 state1221 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1222 : optimized 7 0 state1222 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1223 : optimized 7 0 state1223 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1224 : optimized 7 0 state1224 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1225 : optimized 7 0 state1225 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1226 : optimized 7 0 state1226 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1227 : optimized 7 0 state1227 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1228 : optimized 7 0 state1228 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1229 : optimized 7 0 state1229 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1230 : optimized 7 0 state1230 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1231 : optimized 7 0 state1231 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1232 : optimized 7 0 state1232 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1233 : optimized 7 0 state1233 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1234 : optimized 7 0 state1234 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1235 : optimized 7 0 state1235 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1236 : optimized 7 0 state1236 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1237 : optimized 7 0 state1237 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1238 : optimized 7 0 state1238 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1239 : optimized 7 0 state1239 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1240 : optimized 7 0 state1240 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1241 : optimized 7 0 state1241 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1242 : optimized 7 0 state1242 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1243 : optimized 7 0 state1243 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1244 : optimized 7 0 state1244 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1245 : optimized 7 0 state1245 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1246 : optimized 7 2 state1246 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1247 : optimized 7 1 state1247 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1248 : optimized 7 1 state1248 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1249 : optimized 7 0 state1249 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1250 : optimized 7 0 state1250 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1251 : optimized 7 1 state1251 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1252 : optimized 7 0 state1252 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1253 : optimized 7 0 state1253 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1254 : optimized 7 0 state1254 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1255 : optimized 7 0 state1255 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1256 : optimized 7 2 state1256 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1257 : optimized 7 1 state1257 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1258 : optimized 7 1 state1258 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1259 : optimized 7 0 state1259 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1260 : optimized 7 0 state1260 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1261 : optimized 7 0 state1261 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1262 : optimized 7 0 state1262 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1263 : optimized 7 1 state1263 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1264 : optimized 7 0 state1264 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1265 : optimized 7 0 state1265 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1266 : optimized 7 0 state1266 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1267 : optimized 7 0 state1267 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1268 : optimized 7 0 state1268 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1269 : optimized 7 0 state1269 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1270 : optimized 7 0 state1270 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1220 : optimized 8 2 state1220 = false := by
  rw [optimized_expand]
  have hg : (state1220 == [goal]) = false := by decide +kernel
  have he : expand 2 state1220 = [(0, state1221), (1, state25), (0, state1222), (0, state1223), (0, state1224), (0, state1225), (0, state1226), (0, state1227), (0, state1228), (0, state1229), (0, state1230), (0, state1231), (0, state1232), (0, state1233), (0, state1234), (0, state1235), (0, state1236), (0, state1237), (0, state1238), (0, state1239), (0, state1240), (0, state1241), (0, state1242), (0, state1243), (0, state1244), (0, state1245), (2, state1246), (1, state1247), (1, state1248), (0, state1249), (0, state1250), (1, state1251), (0, state1252), (0, state1253), (0, state1254), (0, state1255), (2, state1256), (1, state1257), (1, state1258), (0, state1259), (0, state1260), (0, state1261), (0, state1262), (1, state1263), (0, state1264), (0, state1265), (0, state1266), (0, state1267), (0, state1268), (0, state1269), (0, state1270)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check1221, check25, check1222, check1223, check1224, check1225, check1226, check1227, check1228, check1229, check1230, check1231, check1232, check1233, check1234, check1235, check1236, check1237, check1238, check1239, check1240, check1241, check1242, check1243, check1244, check1245, check1246, check1247, check1248, check1249, check1250, check1251, check1252, check1253, check1254, check1255, check1256, check1257, check1258, check1259, check1260, check1261, check1262, check1263, check1264, check1265, check1266, check1267, check1268, check1269, check1270]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1272 : optimized 7 0 state1272 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1273 : optimized 7 0 state1273 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1274 : optimized 7 0 state1274 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1275 : optimized 7 0 state1275 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1276 : optimized 7 0 state1276 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1277 : optimized 7 0 state1277 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1278 : optimized 7 0 state1278 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1279 : optimized 7 0 state1279 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1280 : optimized 7 0 state1280 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1281 : optimized 7 0 state1281 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1282 : optimized 7 1 state1282 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1283 : optimized 7 0 state1283 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1284 : optimized 7 0 state1284 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1285 : optimized 7 0 state1285 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1286 : optimized 7 1 state1286 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1287 : optimized 7 0 state1287 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1288 : optimized 7 0 state1288 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1289 : optimized 7 1 state1289 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1290 : optimized 7 0 state1290 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1291 : optimized 7 0 state1291 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1292 : optimized 7 0 state1292 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1293 : optimized 7 1 state1293 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1294 : optimized 7 0 state1294 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1295 : optimized 7 0 state1295 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1296 : optimized 7 0 state1296 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1271 : optimized 8 1 state1271 = false := by
  rw [optimized_expand]
  have hg : (state1271 == [goal]) = false := by decide +kernel
  have he : expand 1 state1271 = [(0, state1272), (0, state1273), (0, state1274), (0, state1275), (0, state1276), (0, state1277), (0, state1278), (0, state1279), (0, state1280), (0, state1281), (1, state1282), (0, state1283), (0, state1284), (0, state1285), (1, state1286), (0, state1287), (0, state1288), (1, state1289), (0, state1290), (0, state1291), (0, state1292), (1, state1293), (0, state1294), (0, state1295), (0, state1296)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check1272, check1273, check1274, check1275, check1276, check1277, check1278, check1279, check1280, check1281, check1282, check1283, check1284, check1285, check1286, check1287, check1288, check1289, check1290, check1291, check1292, check1293, check1294, check1295, check1296]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1298 : optimized 7 0 state1298 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1299 : optimized 7 0 state1299 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1300 : optimized 7 0 state1300 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1301 : optimized 7 0 state1301 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1302 : optimized 7 0 state1302 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1303 : optimized 7 1 state1303 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1304 : optimized 7 0 state1304 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1305 : optimized 7 0 state1305 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1306 : optimized 7 0 state1306 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1307 : optimized 7 0 state1307 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1308 : optimized 7 0 state1308 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1309 : optimized 7 0 state1309 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1310 : optimized 7 0 state1310 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1311 : optimized 7 0 state1311 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1312 : optimized 7 0 state1312 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1313 : optimized 7 0 state1313 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1314 : optimized 7 0 state1314 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1315 : optimized 7 0 state1315 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1316 : optimized 7 1 state1316 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1317 : optimized 7 0 state1317 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1318 : optimized 7 0 state1318 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1319 : optimized 7 1 state1319 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1320 : optimized 7 0 state1320 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1321 : optimized 7 0 state1321 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1322 : optimized 7 1 state1322 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1323 : optimized 7 0 state1323 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1324 : optimized 7 0 state1324 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1325 : optimized 7 1 state1325 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1326 : optimized 7 0 state1326 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1327 : optimized 7 0 state1327 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1297 : optimized 8 1 state1297 = false := by
  rw [optimized_expand]
  have hg : (state1297 == [goal]) = false := by decide +kernel
  have he : expand 1 state1297 = [(0, state1298), (0, state1299), (0, state1300), (0, state1301), (0, state1302), (1, state1303), (0, state1304), (0, state1305), (0, state1306), (0, state1307), (0, state1308), (0, state1309), (0, state1310), (0, state1311), (0, state1312), (0, state1313), (0, state1314), (0, state1315), (1, state1316), (0, state1317), (0, state1318), (1, state1319), (0, state1320), (0, state1321), (1, state1322), (0, state1323), (0, state1324), (1, state1325), (0, state1326), (0, state1327)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check1298, check1299, check1300, check1301, check1302, check1303, check1304, check1305, check1306, check1307, check1308, check1309, check1310, check1311, check1312, check1313, check1314, check1315, check1316, check1317, check1318, check1319, check1320, check1321, check1322, check1323, check1324, check1325, check1326, check1327]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1328 : optimized 8 0 state1328 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1329 : optimized 8 0 state1329 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1331 : optimized 7 0 state1331 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1332 : optimized 7 0 state1332 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1333 : optimized 7 0 state1333 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1334 : optimized 7 0 state1334 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1335 : optimized 7 0 state1335 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1336 : optimized 7 0 state1336 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1337 : optimized 7 0 state1337 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1338 : optimized 7 0 state1338 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1339 : optimized 7 0 state1339 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1340 : optimized 7 0 state1340 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1341 : optimized 7 0 state1341 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1342 : optimized 7 0 state1342 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1343 : optimized 7 0 state1343 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1344 : optimized 7 0 state1344 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1345 : optimized 7 0 state1345 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1346 : optimized 7 0 state1346 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1347 : optimized 7 0 state1347 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1348 : optimized 7 0 state1348 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1349 : optimized 7 0 state1349 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1350 : optimized 7 1 state1350 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1351 : optimized 7 0 state1351 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1352 : optimized 7 0 state1352 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1353 : optimized 7 0 state1353 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1354 : optimized 7 0 state1354 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1355 : optimized 7 0 state1355 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1356 : optimized 7 0 state1356 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1357 : optimized 7 1 state1357 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1358 : optimized 7 0 state1358 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1359 : optimized 7 0 state1359 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1360 : optimized 7 0 state1360 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1361 : optimized 7 0 state1361 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1362 : optimized 7 0 state1362 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1363 : optimized 7 0 state1363 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1364 : optimized 7 2 state1364 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1365 : optimized 7 1 state1365 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1366 : optimized 7 1 state1366 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1367 : optimized 7 0 state1367 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1368 : optimized 7 0 state1368 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1369 : optimized 7 0 state1369 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1370 : optimized 7 0 state1370 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1371 : optimized 7 1 state1371 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1372 : optimized 7 0 state1372 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1373 : optimized 7 0 state1373 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1374 : optimized 7 0 state1374 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1375 : optimized 7 0 state1375 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1376 : optimized 7 0 state1376 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1377 : optimized 7 0 state1377 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1378 : optimized 7 0 state1378 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1330 : optimized 8 2 state1330 = false := by
  rw [optimized_expand]
  have hg : (state1330 == [goal]) = false := by decide +kernel
  have he : expand 2 state1330 = [(0, state1331), (0, state1332), (0, state1333), (0, state1334), (0, state1335), (0, state1336), (0, state1337), (0, state1338), (0, state1339), (0, state1340), (0, state1341), (0, state1342), (0, state1343), (0, state1344), (0, state1345), (0, state1346), (0, state1347), (0, state1348), (0, state1349), (1, state1350), (0, state1351), (0, state1352), (0, state1353), (0, state1354), (0, state1355), (0, state1356), (1, state1357), (0, state1358), (0, state1359), (0, state1360), (0, state1361), (0, state1362), (0, state1363), (2, state1364), (1, state1365), (1, state1366), (0, state1367), (0, state1368), (0, state1369), (0, state1370), (1, state1371), (0, state1372), (0, state1373), (0, state1374), (0, state1375), (0, state1376), (0, state1377), (0, state1378)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check1331, check1332, check1333, check1334, check1335, check1336, check1337, check1338, check1339, check1340, check1341, check1342, check1343, check1344, check1345, check1346, check1347, check1348, check1349, check1350, check1351, check1352, check1353, check1354, check1355, check1356, check1357, check1358, check1359, check1360, check1361, check1362, check1363, check1364, check1365, check1366, check1367, check1368, check1369, check1370, check1371, check1372, check1373, check1374, check1375, check1376, check1377, check1378]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1379 : optimized 8 1 state1379 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1381 : optimized 7 0 state1381 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1382 : optimized 7 0 state1382 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1383 : optimized 7 0 state1383 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1384 : optimized 7 0 state1384 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1385 : optimized 7 0 state1385 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1386 : optimized 7 0 state1386 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1387 : optimized 7 0 state1387 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1388 : optimized 7 1 state1388 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1389 : optimized 7 0 state1389 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1390 : optimized 7 0 state1390 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1391 : optimized 7 0 state1391 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1392 : optimized 7 0 state1392 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1393 : optimized 7 0 state1393 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1394 : optimized 7 0 state1394 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1395 : optimized 7 0 state1395 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1396 : optimized 7 0 state1396 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1397 : optimized 7 0 state1397 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1398 : optimized 7 0 state1398 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1399 : optimized 7 1 state1399 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1400 : optimized 7 0 state1400 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1401 : optimized 7 0 state1401 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1402 : optimized 7 0 state1402 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1403 : optimized 7 1 state1403 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1404 : optimized 7 0 state1404 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1405 : optimized 7 0 state1405 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1406 : optimized 7 1 state1406 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1407 : optimized 7 0 state1407 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1408 : optimized 7 0 state1408 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1380 : optimized 8 1 state1380 = false := by
  rw [optimized_expand]
  have hg : (state1380 == [goal]) = false := by decide +kernel
  have he : expand 1 state1380 = [(0, state1381), (0, state1382), (0, state1383), (0, state1384), (0, state1385), (0, state1386), (0, state1387), (1, state1388), (0, state1389), (0, state1390), (0, state1391), (0, state1392), (0, state1393), (0, state1394), (0, state1395), (0, state1396), (0, state1397), (0, state1398), (1, state1399), (0, state1400), (0, state1401), (0, state1402), (1, state1403), (0, state1404), (0, state1405), (1, state1406), (0, state1407), (0, state1408)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check1381, check1382, check1383, check1384, check1385, check1386, check1387, check1388, check1389, check1390, check1391, check1392, check1393, check1394, check1395, check1396, check1397, check1398, check1399, check1400, check1401, check1402, check1403, check1404, check1405, check1406, check1407, check1408]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1409 : optimized 8 0 state1409 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1410 : optimized 8 0 state1410 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1412 : optimized 7 0 state1412 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1413 : optimized 7 0 state1413 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1414 : optimized 7 0 state1414 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1415 : optimized 7 0 state1415 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1416 : optimized 7 0 state1416 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1417 : optimized 7 0 state1417 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1418 : optimized 7 0 state1418 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1419 : optimized 7 0 state1419 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1420 : optimized 7 0 state1420 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1421 : optimized 7 0 state1421 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1422 : optimized 7 0 state1422 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1423 : optimized 7 0 state1423 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1424 : optimized 7 0 state1424 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1425 : optimized 7 0 state1425 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1426 : optimized 7 0 state1426 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1427 : optimized 7 0 state1427 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1428 : optimized 7 0 state1428 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1429 : optimized 7 0 state1429 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1430 : optimized 7 0 state1430 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1431 : optimized 7 1 state1431 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1432 : optimized 7 0 state1432 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1433 : optimized 7 0 state1433 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1434 : optimized 7 0 state1434 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1435 : optimized 7 0 state1435 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1436 : optimized 7 0 state1436 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1437 : optimized 7 0 state1437 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1438 : optimized 7 2 state1438 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1439 : optimized 7 1 state1439 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1440 : optimized 7 1 state1440 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1441 : optimized 7 0 state1441 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1442 : optimized 7 0 state1442 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1443 : optimized 7 0 state1443 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1444 : optimized 7 0 state1444 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1445 : optimized 7 1 state1445 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1446 : optimized 7 0 state1446 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1447 : optimized 7 0 state1447 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1448 : optimized 7 1 state1448 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1449 : optimized 7 0 state1449 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1450 : optimized 7 0 state1450 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1451 : optimized 7 0 state1451 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1452 : optimized 7 0 state1452 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1453 : optimized 7 0 state1453 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1454 : optimized 7 0 state1454 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1455 : optimized 7 0 state1455 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1456 : optimized 7 0 state1456 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1457 : optimized 7 0 state1457 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1458 : optimized 7 0 state1458 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1459 : optimized 7 0 state1459 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1411 : optimized 8 2 state1411 = false := by
  rw [optimized_expand]
  have hg : (state1411 == [goal]) = false := by decide +kernel
  have he : expand 2 state1411 = [(0, state1412), (0, state1413), (0, state1414), (0, state1415), (0, state1416), (0, state1417), (0, state1418), (0, state1419), (0, state1420), (0, state1421), (0, state1422), (0, state1423), (0, state1424), (0, state1425), (0, state1426), (0, state1427), (0, state1428), (0, state1429), (0, state1430), (1, state1431), (0, state1432), (0, state1433), (0, state1434), (0, state1435), (0, state1436), (0, state1437), (2, state1438), (1, state1439), (1, state1440), (0, state1441), (0, state1442), (0, state1443), (0, state1444), (1, state1445), (0, state1446), (0, state1447), (1, state1448), (0, state1449), (0, state1450), (0, state1451), (0, state1452), (0, state1453), (0, state1454), (0, state1455), (0, state1456), (0, state1457), (0, state1458), (0, state1459)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check1412, check1413, check1414, check1415, check1416, check1417, check1418, check1419, check1420, check1421, check1422, check1423, check1424, check1425, check1426, check1427, check1428, check1429, check1430, check1431, check1432, check1433, check1434, check1435, check1436, check1437, check1438, check1439, check1440, check1441, check1442, check1443, check1444, check1445, check1446, check1447, check1448, check1449, check1450, check1451, check1452, check1453, check1454, check1455, check1456, check1457, check1458, check1459]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1460 : optimized 8 1 state1460 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1462 : optimized 7 0 state1462 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1463 : optimized 7 0 state1463 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1464 : optimized 7 0 state1464 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1465 : optimized 7 0 state1465 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1466 : optimized 7 0 state1466 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1467 : optimized 7 0 state1467 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1468 : optimized 7 0 state1468 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1469 : optimized 7 0 state1469 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1470 : optimized 7 0 state1470 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1471 : optimized 7 1 state1471 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1472 : optimized 7 0 state1472 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1473 : optimized 7 0 state1473 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1474 : optimized 7 0 state1474 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1475 : optimized 7 0 state1475 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1476 : optimized 7 0 state1476 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1477 : optimized 7 0 state1477 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1478 : optimized 7 0 state1478 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1479 : optimized 7 0 state1479 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1480 : optimized 7 1 state1480 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1481 : optimized 7 0 state1481 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1482 : optimized 7 0 state1482 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1483 : optimized 7 1 state1483 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1484 : optimized 7 0 state1484 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1485 : optimized 7 0 state1485 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1486 : optimized 7 1 state1486 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1487 : optimized 7 0 state1487 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1488 : optimized 7 0 state1488 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1489 : optimized 7 0 state1489 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1461 : optimized 8 1 state1461 = false := by
  rw [optimized_expand]
  have hg : (state1461 == [goal]) = false := by decide +kernel
  have he : expand 1 state1461 = [(0, state1462), (0, state1463), (0, state1464), (0, state1465), (0, state1466), (0, state1467), (0, state1468), (0, state1469), (0, state1470), (1, state1471), (0, state1472), (0, state1473), (0, state1474), (0, state1475), (0, state1476), (0, state1477), (0, state1478), (0, state1479), (1, state1480), (0, state1481), (0, state1482), (1, state1483), (0, state1484), (0, state1485), (1, state1486), (0, state1487), (0, state1488), (0, state1489)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check1462, check1463, check1464, check1465, check1466, check1467, check1468, check1469, check1470, check1471, check1472, check1473, check1474, check1475, check1476, check1477, check1478, check1479, check1480, check1481, check1482, check1483, check1484, check1485, check1486, check1487, check1488, check1489]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1490 : optimized 8 0 state1490 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1491 : optimized 8 0 state1491 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1492 : optimized 8 0 state1492 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1493 : optimized 8 0 state1493 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1495 : optimized 7 0 state1495 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1496 : optimized 7 0 state1496 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1497 : optimized 7 0 state1497 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1498 : optimized 7 0 state1498 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1499 : optimized 7 0 state1499 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1500 : optimized 7 0 state1500 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1501 : optimized 7 0 state1501 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1502 : optimized 7 0 state1502 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1503 : optimized 7 0 state1503 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1504 : optimized 7 0 state1504 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1494 : optimized 8 0 state1494 = false := by
  rw [optimized_expand]
  have hg : (state1494 == [goal]) = false := by decide +kernel
  have he : expand 0 state1494 = [(0, state703), (0, state1495), (0, state1496), (0, state1497), (0, state1498), (0, state1499), (0, state1500), (0, state1501), (0, state1502), (0, state1503), (0, state1504)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check703, check1495, check1496, check1497, check1498, check1499, check1500, check1501, check1502, check1503, check1504]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1505 : optimized 8 0 state1505 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1507 : optimized 7 0 state1507 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1508 : optimized 7 0 state1508 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1509 : optimized 7 0 state1509 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1510 : optimized 7 0 state1510 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1511 : optimized 7 0 state1511 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1512 : optimized 7 0 state1512 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1513 : optimized 7 0 state1513 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1514 : optimized 7 0 state1514 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1515 : optimized 7 0 state1515 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1516 : optimized 7 0 state1516 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1506 : optimized 8 0 state1506 = false := by
  rw [optimized_expand]
  have hg : (state1506 == [goal]) = false := by decide +kernel
  have he : expand 0 state1506 = [(0, state1063), (0, state1507), (0, state1508), (0, state1509), (0, state1510), (0, state1511), (0, state1512), (0, state1513), (0, state1514), (0, state1515), (0, state1516)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check1063, check1507, check1508, check1509, check1510, check1511, check1512, check1513, check1514, check1515, check1516]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1517 : optimized 8 0 state1517 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1518 : optimized 8 0 state1518 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1519 : optimized 8 0 state1519 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1520 : optimized 8 0 state1520 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1521 : optimized 8 0 state1521 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check1522 : optimized 8 0 state1522 = false := by
  decide +kernel

set_option maxRecDepth 8000 in
set_option maxHeartbeats 40000000 in
lemma check0 : optimized 9 2 state0 = false := by
  rw [optimized_expand]
  have hg : (state0 == [goal]) = false := by decide +kernel
  have he : expand 2 state0 = [(0, state1), (0, state2), (0, state3), (0, state4), (0, state5), (1, state6), (0, state66), (0, state67), (0, state84), (0, state96), (2, state97), (1, state274), (1, state322), (0, state353), (0, state354), (0, state370), (0, state371), (0, state387), (0, state388), (0, state389), (0, state390), (0, state391), (0, state392), (2, state393), (1, state449), (1, state480), (0, state512), (0, state522), (0, state538), (0, state539), (2, state540), (1, state671), (1, state702), (0, state731), (0, state732), (0, state748), (0, state749), (0, state750), (0, state751), (2, state752), (1, state808), (1, state839), (0, state871), (0, state881), (0, state897), (0, state898), (0, state914), (0, state915), (2, state916), (1, state1031), (1, state1062), (0, state1091), (1, state1092), (0, state1202), (0, state1218), (0, state1219), (2, state1220), (1, state1271), (1, state1297), (0, state1328), (0, state1329), (2, state1330), (1, state1379), (1, state1380), (0, state1409), (0, state1410), (2, state1411), (1, state1460), (1, state1461), (0, state1490), (0, state1491), (0, state1492), (0, state1493), (0, state1494), (0, state1505), (0, state1506), (0, state1517), (0, state1518), (0, state1519), (0, state1520), (0, state1521), (0, state1522)] := by decide +kernel
  rw [hg, he]
  simp only [Bool.false_or, List.any_cons, List.any_nil, check1, check2, check3, check4, check5, check6, check66, check67, check84, check96, check97, check274, check322, check353, check354, check370, check371, check387, check388, check389, check390, check391, check392, check393, check449, check480, check512, check522, check538, check539, check540, check671, check702, check731, check732, check748, check749, check750, check751, check752, check808, check839, check871, check881, check897, check898, check914, check915, check916, check1031, check1062, check1091, check1092, check1202, check1218, check1219, check1220, check1271, check1297, check1328, check1329, check1330, check1379, check1380, check1409, check1410, check1411, check1460, check1461, check1490, check1491, check1492, check1493, check1494, check1505, check1506, check1517, check1518, check1519, check1520, check1521, check1522]

lemma full_false : optimized 9 2 inputs = false := by
  have hi : inputs = state0 := by decide +kernel
  rw [hi]; exact check0

lemma initial_cuts : inputs.sublists.all
    (fun l => (cuts l != -1) || (l == inputs)) = true := by
  decide +kernel

lemma no_small_of_full_false (full_false : optimized 9 2 inputs = false)
    (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 9)
    (hr : PEqualNP.Represents.Represents A C) : False := by
  obtain ⟨S, hsub, hl⟩ := compress (get_build C hm hr)
  have hl9 : live basicOps goal 9 S := extend_live hs hl
  let l := inputs.filter (fun w => decide (w ∈ S))
  have hlS : l.toFinset = S := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · exact fun h => h.2
    · exact fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩
  have hlL : live basicOps goal 9 l.toFinset := by
    rw [hlS]
    exact hl9
  have hcuts : cuts l = -1 := cuts_full hlL
  have hmem : l ∈ inputs.sublists := List.mem_sublists.mpr List.filter_sublist
  have hrow := List.all_eq_true.mp initial_cuts l hmem
  have he : l = inputs := by simpa [hcuts] using hrow
  have hlI : live basicOps goal 9 inputs.toFinset := by
    rw [← he]
    exact hlL
  have hsearch := optimized_complete 9 inputs 2 inputs_nodup (by decide) hlI
  rw [full_false] at hsearch
  exact Bool.noConfusion hsearch


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

lemma upper : RepSizeAtMost (fun u v : Fin 4 => (5805 : ℕ).testBit (4 * u.val + v.val)) 10 := by
  refine ⟨⟨[⟨GateOp.or, [2, 7]⟩, ⟨GateOp.or, [4, 8]⟩, ⟨GateOp.or, [0, 5]⟩, ⟨GateOp.and, [3, 4]⟩, ⟨GateOp.or, [10, 11]⟩, ⟨GateOp.and, [9, 12]⟩, ⟨GateOp.or, [6, 13]⟩, ⟨GateOp.or, [8, 12]⟩, ⟨GateOp.or, [1, 14]⟩, ⟨GateOp.and, [15, 16]⟩], 17⟩, ?_, by decide, by decide⟩
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp


end PEqualNP.Outside.L_meta_6349

theorem PEqualNP.Outside.L_meta_6349 : PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (5805 : ℕ).testBit (4 * u.val + v.val)) 10 ∧
  ¬ PEqualNP.Represents.RepSizeAtMost (fun u v : Fin 4 => (5805 : ℕ).testBit (4 * u.val + v.val)) 9 := by
  refine ⟨PEqualNP.Outside.L_meta_6349.upper, ?_⟩
  rintro ⟨C, hm, hs, hr⟩
  exact PEqualNP.Outside.L_meta_6349.no_small_of_full_false
    PEqualNP.Outside.L_meta_6349.full_false C hm hs hr
