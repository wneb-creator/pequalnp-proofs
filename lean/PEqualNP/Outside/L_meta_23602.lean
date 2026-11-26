import PEqualNP.Defs
import Mathlib.Data.Tree.Basic

namespace PEqualNP.Outside.L_meta_23602_aux.Cert

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

abbrev W := BitVec 126

def ops (x y : W) : List W := [x &&& y, x ||| y]

def sep (x : W) : BitVec 63 := ((x >>> 63) &&& ~~~x).setWidth 63

def cuts (ws : List W) : BitVec 63 := ws.foldr (fun w v => sep w ||| v) 0

def goal : W := (-1 : BitVec 63) ++ (0 : BitVec 63)

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

def rawInputs : List W :=
  [0x1ffff80c06030180c0603, 0xffffffe00000100804020100804, 0x1ff000000000000e070381c0e07038, 0x3fe000000000000070381c0e070381c0, 0x3fe0000003fe00000241209048241209, 0x1ff007fc0000001088442211088442, 0xff8000000ffa412090482412090, 0x1ff004924924924924924]

def inputs : List W := rawInputs

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

def differs (i : Fin 63) (w : W) : Prop :=
  w.getLsbD (63 + i.val) = true ∧ w.getLsbD i.val = false

lemma ops_differs (i : Fin 63) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  unfold differs at hd ⊢
  rcases hz with rfl | rfl <;> revert hd <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or] <;>
    cases a.getLsbD (63 + i.val) <;> cases a.getLsbD i.val <;>
    cases b.getLsbD (63 + i.val) <;> cases b.getLsbD i.val <;> simp

lemma goal_differs : ∀ i : Fin 63, differs i goal := by
  unfold differs
  decide

lemma cuts_spec (ws : List W) (i : Fin 63) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    have hi : i.val < 126 := by omega
    simp [sep, i.isLt, differs, hi, Nat.add_comm]

lemma cuts_full {k : ℕ} {ws : List W} (h : live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := live_separates (differs ⟨j, hj⟩) (goal_differs ⟨j, hj⟩) (ops_differs ⟨j, hj⟩) h
  have hbit := (cuts_spec ws ⟨j, hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 63)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

lemma ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, BitVec.and_comm, BitVec.or_comm]

def keepChoices (a b : W) (r : List W) : List (List W) := [r, a :: r, b :: r, a :: b :: r]

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

lemma singleton_list {ws : List W} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
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
  z == 0 || z == BitVec.allOnes 126 || w.any (fun u => z == u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 126) (z : W) : Bool := z[k.val]

private lemma read_bit (w : List W) (i : ℕ) (k : Fin 126) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

private lemma read_wire (w : List W) (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

private lemma atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) : possible ws x := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    exact .inr ⟨x, hx, .inl rfl⟩

private lemma pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
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
private lemma gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
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
    · exact ⟨BitVec.allOnes 126, by simp [possible], by simp [step, GateOp.eval, bit]; decide⟩
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
  ∀ u ∈ w, u = 0 ∨ u = BitVec.allOnes 126 ∨ u ∈ available

lemma classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    z = 0 ∨ z = BitVec.allOnes 126 ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W} (h : t = 0 ∨ t = BitVec.allOnes 126 ∨ t ∈ available) :
      t = 0 ∨ t = BitVec.allOnes 126 ∨ t ∈ available ∨
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

private lemma compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
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
      · exact False.elim ((by decide : goal ≠ BitVec.allOnes 126) h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = 0 ∨ z = BitVec.allOnes 126 ∨ z ∈ av) : represents av (w ++ [z]) := by
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

def tryStep (next : ℕ → List W → Bool) (extra : ℕ) (ws : List W) : Bool :=
  ws == [goal] || (pairs ws).any (fun (a,b,r) => dispatch extra next a b r)

lemma step_complete {k extra : ℕ} {ws : List W} (hn : ws.Nodup)
    (room : extra + ws.length = k + 2) (h : live basicOps goal (k+1) ws.toFinset)
    (next : ℕ → List W → Bool)
    (child : ∀ l e, l.Nodup → e + l.length = k + 1 → live basicOps goal k l.toFinset → next e l = true) :
    tryStep next extra ws = true := by
  rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
  · simp [tryStep, singleton_list hn done]
  · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : W} (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
        dispatch extra next a b r = true := by
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
      apply dispatch_complete (k := k) (extra := extra) next hop hk (by omega) (by omega) (cuts_full hl)
      exact child _ _ hnd (by simp; omega) hl
    simp only [tryStep, Bool.or_eq_true, List.any_eq_true]
    right
    rcases hm with direct | swap
    · exact ⟨(a, b, r), direct, go hp hs hz⟩
    · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

abbrev ReplayTree := BinaryTree (List W)

def ReplayTree.all (f : List W → Bool) : ReplayTree → Bool
  | .nil => true
  | .node w l r => ReplayTree.all f l && f w && ReplayTree.all f r

def ReplayTree.find (key : List W) : ReplayTree → Bool
  | .nil => false
  | .node w l r => if key == w then true else if key < w then ReplayTree.find key l else ReplayTree.find key r

lemma find_valid {f : List W → Bool} {key : List W} (t : ReplayTree) (h : t.all f = true)
    (hm : t.find key = true) : f key = true := by
  induction t with
  | nil => simp [ReplayTree.find] at hm
  | node w l r il ir =>
    simp only [ReplayTree.all, Bool.and_eq_true] at h
    simp only [ReplayTree.find] at hm
    split at hm
    · rename_i heq
      exact (eq_of_beq heq) ▸ h.1.2
    · split at hm
      · exact il h.1.1 hm
      · exact ir h.2 hm

def ins (x : W) : List W → List W
  | [] => [x]
  | y :: ys => if x ≤ y then x :: y :: ys else y :: ins x ys

def sortedW : List W → List W
  | [] => []
  | x :: xs => ins x (sortedW xs)

lemma ins_perm (x : W) (l : List W) : (ins x l).Perm (x :: l) := by
  induction l with
  | nil => exact .refl _
  | cons y ys ih =>
    simp only [ins]
    split
    · exact .refl _
    · exact (ih.cons y).trans (.swap _ _ _)

lemma sorted_perm (l : List W) : (sortedW l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons x xs ih => exact (ins_perm x _).trans (ih.cons x)


def missed (t : ReplayTree) (_ : ℕ) (l : List W) : Bool := !(t.find (sortedW l))

def blocked (k : ℕ) (t : ReplayTree) (l : List W) : Bool :=
  !(tryStep (missed t) (k+2-l.length) l)

def sound (k : ℕ) (t : ReplayTree) : Prop :=
  ∀ l : List W, t.find l = true → l.Nodup → ¬live basicOps goal k l.toFinset

lemma empty_sound (k : ℕ) : sound k (.nil : ReplayTree) := by
  intro l h
  cases h

lemma layer_sound {k : ℕ} {prev curr : ReplayTree} (hp : sound k prev)
    (hc : curr.all (blocked k prev) = true) : sound (k+1) curr := by
  intro l hm hn hl
  have len := live_card hl
  rw [List.toFinset_card_of_nodup hn] at len
  have h := step_complete hn (by omega : k+2-l.length+l.length = k+2) hl (missed prev) (by
    intro xs e nd room liveX
    unfold missed
    cases hh : prev.find (sortedW xs) with
    | false => rfl
    | true =>
      have perm := sorted_perm xs
      exact False.elim (hp _ hh (perm.nodup_iff.mpr nd) (by simpa only [List.toFinset_eq_of_perm _ _ perm] using liveX)))
  have hb := find_valid curr hc hm
  simp [blocked,h] at hb
def A : Fin 4 → Fin 4 → Bool := fun u v : Fin 4 => (4732 : ℕ).testBit (4 * u.val + v.val)

def posL : List (Fin 4 × Fin 4) :=
  [(0, 2), (0, 3), (1, 0), (1, 1), (1, 2), (2, 1), (3, 0)]

def negL : List (Fin 4 × Fin 4) :=
  [(0, 0), (0, 1), (1, 3), (2, 0), (2, 2), (2, 3), (3, 1), (3, 2), (3, 3)]

def samp (k : Fin 126) : Fin 4 × Fin 4 :=
  if k.val < 63 then negL.getD (k.val % 9) (0, 0) else posL.getD ((k.val - 63) / 9) (0, 0)

lemma input_rows : ∀ k : Fin 126,
    rawInputs.map (bit k) = PEqualNP.Represents.oneEach (samp k).1 (samp k).2 := by
  decide +kernel

lemma goal_rows : ∀ k : Fin 126, bit k goal = A (samp k).1 (samp k).2 := by
  decide +kernel

lemma rows_eval (C : Circuit) (hr : PEqualNP.Represents.Represents A C) (k : Fin 126) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false = bit k goal := by
  rw [input_rows k, goal_rows k]
  exact hr (samp k).1 (samp k).2

lemma initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  exact .inr (.inr (List.mem_toFinset.mpr hu))

lemma get_build (C : Circuit) (hg : Monotone2 C) (hr : PEqualNP.Represents.Represents A C) :
    build basicOps goal C.gates.length inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C hr)

lemma extend_live {m n : ℕ} {s : Finset W} (le : m ≤ n) (h : live basicOps goal m s) :
    live basicOps goal n s := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

lemma inputs_nodup : inputs.Nodup := by decide +kernel

abbrev n (l : ReplayTree) (key : List W) (r : ReplayTree) : ReplayTree := BinaryTree.node key l r
abbrev z : ReplayTree := BinaryTree.nil
def w0 : W := 0x0
def w1 : W := 0x40201008040201
def w2 : W := 0x80402010080402
def w3 : W := 0x100804020100804
def w4 : W := 0x201008040201008
def w5 : W := 0x402010080402010
def w6 : W := 0x804020100804020
def w7 : W := 0x1008040201008040
def w8 : W := 0x2010080402010080
def w9 : W := 0x28140a05028140a0
def w10 : W := 0x4020100804020100
def w11 : W := 0x4422110884422110
def w12 : W := 0xff8000000000000000
def w13 : W := 0x1ff000000000000000000
def w14 : W := 0x1ff000100804020100804
def w15 : W := 0x1ff000804020100804020
def w16 : W := 0x1ff004020100804020100
def w17 : W := 0x1ff004924924924924924
def w18 : W := 0x1ff004b2592c964b2592c
def w19 : W := 0x1ff004d269349a4d26934
def w20 : W := 0x1ff00592c964b2592c964
def w21 : W := 0x1ff0069349a4d269349a4
def w22 : W := 0x1ffff8000000000000000
def w23 : W := 0x1ffff80c06030180c0603
def w24 : W := 0x1ffff82c160b0582c160b
def w25 : W := 0x1ffff90c86432190c8643
def w26 : W := 0x1ffffc924924924924924
def w27 : W := 0x1ffffc9e4f2793c9e4f27
def w28 : W := 0x3fe00000000000000000000
def w29 : W := 0x3ffff000000000000000000
def w30 : W := 0x3ffff004924924924924924
def w31 : W := 0x3ffffff80c06030180c0603
def w32 : W := 0x7fc0000000000000000000000
def w33 : W := 0x7fc01ff000000000000000000
def w34 : W := 0x7fc01ff004924924924924924
def w35 : W := 0x7fc01ffff80c06030180c0603
def w36 : W := 0xff8000000000000000000000000
def w37 : W := 0xff8000000ff8000000000000000
def w38 : W := 0xff8000000ffa412090482412090
def w39 : W := 0xff8000000ffa6130984c2613098
def w40 : W := 0xff8000000ffac160b0582c160b0
def w41 : W := 0xff8000000ffb41a0d068341a0d0
def w42 : W := 0xff8000000ffe432190c86432190
def w43 : W := 0xff80001ff004924924924924924
def w44 : W := 0xff80001ffff8000000000000000
def w45 : W := 0xff80001ffff80c06030180c0603
def w46 : W := 0xff80001ffffa412090482412090
def w47 : W := 0xff80001ffffa4d269349a4d2693
def w48 : W := 0xff80001ffffac160b0582c160b0
def w49 : W := 0xff80001ffffe432190c86432190
def w50 : W := 0xff80001ffffed369b4da6d369b4
def w51 : W := 0xff803fe00ffa412090482412090
def w52 : W := 0xff803ffffffa412090482412090
def w53 : W := 0xffffc0000ffa412090482412090
def w54 : W := 0xffffc01ffffa412090482412090
def w55 : W := 0xffffffe00000100804020100804
def w56 : W := 0xffffffe00000904824120904824
def w57 : W := 0xffffffe00004120904824120904
def w58 : W := 0xffffffe00ff8100804020100804
def w59 : W := 0xffffffe00ffa5128944a2512894
def w60 : W := 0xfffffffff000100804020100804
def w61 : W := 0xfffffffff000904824120904824
def w62 : W := 0xfffffffff004120904824120904
def w63 : W := 0xfffffffff004924924924924924
def w64 : W := 0xfffffffffff8100804020100804
def w65 : W := 0xfffffffffff81c0e070381c0e07
def w66 : W := 0xfffffffffffc924924924924924
def w67 : W := 0xfffffffffffc9e4f2793c9e4f27
def w68 : W := 0xfffffffffffed369b4da6d369b4
def w69 : W := 0x1ff000000000000000000000000000
def w70 : W := 0x1ff000000000000201008040201008
def w71 : W := 0x1ff000000000000402010080402010
def w72 : W := 0x1ff000000000000804020100804020
def w73 : W := 0x1ff000000000000e070381c0e07038
def w74 : W := 0x1ff000000000000e472391c8e47239
def w75 : W := 0x1ff000000000000f0783c1e0f0783c
def w76 : W := 0x1ff000000000002e170b85c2e170b8
def w77 : W := 0x1ff000000000004e271389c4e27138
def w78 : W := 0x1ff000000000ff8000000000000000
def w79 : W := 0x1ff000000000ff8e070381c0e07038
def w80 : W := 0x1ff0000001ff000000000000000000
def w81 : W := 0x1ff0000001ff000100804020100804
def w82 : W := 0x1ff0000001ff000201008040201008
def w83 : W := 0x1ff0000001ff000402010080402010
def w84 : W := 0x1ff0000001ff000e070381c0e07038
def w85 : W := 0x1ff0000001ff000f0783c1e0f0783c
def w86 : W := 0x1ff0000001ff004020100804020100
def w87 : W := 0x1ff0000001ff004924924924924924
def w88 : W := 0x1ff0000001ff004b2592c964b2592c
def w89 : W := 0x1ff0000001ff004d269349a4d26934
def w90 : W := 0x1ff0000001ff004e271389c4e27138
def w91 : W := 0x1ff0000001ff004f2793c9e4f2793c
def w92 : W := 0x1ff0000001ff006f379bcde6f379bc
def w93 : W := 0x1ff0000001ffff8000000000000000
def w94 : W := 0x1ff0000001ffff80c06030180c0603
def w95 : W := 0x1ff0000001ffff8e070381c0e07038
def w96 : W := 0x1ff0000001ffff8ec763b1d8ec763b
def w97 : W := 0x1ff0000001ffffc924924924924924
def w98 : W := 0x1ff0000001ffffcf2793c9e4f2793c
def w99 : W := 0x1ff0000001ffffcfe7f3f9fcfe7f3f
def w100 : W := 0x1ff00003fe00000e070381c0e07038
def w101 : W := 0x1ff00003ffff000e070381c0e07038
def w102 : W := 0x1ff00003ffff004f2793c9e4f2793c
def w103 : W := 0x1ff007fc0000000000000000000000
def w104 : W := 0x1ff007fc0000000e070381c0e07038
def w105 : W := 0x1ff007fc0000001088442211088442
def w106 : W := 0x1ff007fc00000010c86432190c8643
def w107 : W := 0x1ff007fc0000001e8f47a3d1e8f47a
def w108 : W := 0x1ff007fc00000030984c26130984c2
def w109 : W := 0x1ff007fc00000050a8542a150a8542
def w110 : W := 0x1ff007fc0000ff9088442211088442
def w111 : W := 0x1ff007fc01ff000000000000000000
def w112 : W := 0x1ff007fc01ff000e070381c0e07038
def w113 : W := 0x1ff007fc01ff001088442211088442
def w114 : W := 0x1ff007fc01ff004924924924924924
def w115 : W := 0x1ff007fc01ff004f2793c9e4f2793c
def w116 : W := 0x1ff007fc01ff0059acd66b359acd66
def w117 : W := 0x1ff007fc01ff005fafd7ebf5fafd7e
def w118 : W := 0x1ff007fc01ffff8000000000000000
def w119 : W := 0x1ff007fc01ffff80c06030180c0603
def w120 : W := 0x1ff007fc01ffff9088442211088442
def w121 : W := 0x1ff007fc01ffff90c86432190c8643
def w122 : W := 0x1ff007fc01ffff9ecf67b3d9ecf67b
def w123 : W := 0x1ff007fc01ffffd9ecf67b3d9ecf67
def w124 : W := 0x1ff007fc01ffffdfeff7fbfdfeff7f
def w125 : W := 0x1ff007fffe00001088442211088442
def w126 : W := 0x1ff007ffffff001088442211088442
def w127 : W := 0x1ff007ffffffff90c86432190c8643
def w128 : W := 0x1ffff8000000000e070381c0e07038
def w129 : W := 0x1ffff8000000ff8000000000000000
def w130 : W := 0x1ffff8000000ff8e070381c0e07038
def w131 : W := 0x1ffff8000000ffa412090482412090
def w132 : W := 0x1ffff8000000ffa6130984c2613098
def w133 : W := 0x1ffff8000000ffac160b0582c160b0
def w134 : W := 0x1ffff8000000ffae170b85c2e170b8
def w135 : W := 0x1ffff8000000ffee371b8dc6e371b8
def w136 : W := 0x1ffff80001ff004f2793c9e4f2793c
def w137 : W := 0x1ffff80001ffffa412090482412090
def w138 : W := 0x1ffff80001ffffa6130984c2613098
def w139 : W := 0x1ffff80001ffffae170b85c2e170b8
def w140 : W := 0x1ffff80001ffffaed76bb5daed76bb
def w141 : W := 0x1ffff80001ffffe432190c86432190
def w142 : W := 0x1ffff80001ffffed369b4da6d369b4
def w143 : W := 0x1ffff80001ffffee371b8dc6e371b8
def w144 : W := 0x1ffff80001ffffef379bcde6f379bc
def w145 : W := 0x1ffff803fe00ffae170b85c2e170b8
def w146 : W := 0x1ffffffc0000001088442211088442
def w147 : W := 0x1ffffffc0000ffa412090482412090
def w148 : W := 0x1ffffffc0000ffae170b85c2e170b8
def w149 : W := 0x1ffffffc0000ffb49a4d269349a4d2
def w150 : W := 0x1ffffffc0000ffbe9f4fa7d3e9f4fa
def w151 : W := 0x1ffffffc01ffff90c86432190c8643
def w152 : W := 0x1ffffffc01ffffa412090482412090
def w153 : W := 0x1ffffffc01ffffae170b85c2e170b8
def w154 : W := 0x1ffffffc01ffffb4da6d369b4da6d3
def w155 : W := 0x1ffffffc01ffffbedf6fb7dbedf6fb
def w156 : W := 0x1ffffffffe00000100804020100804
def w157 : W := 0x1ffffffffe00000904824120904824
def w158 : W := 0x1ffffffffe00000f0783c1e0f0783c
def w159 : W := 0x1ffffffffe00001188c46231188c46
def w160 : W := 0x1ffffffffe00ff8100804020100804
def w161 : W := 0x1ffffffffe00ffaf178bc5e2f178bc
def w162 : W := 0x1fffffffffff000100804020100804
def w163 : W := 0x1fffffffffff000f0783c1e0f0783c
def w164 : W := 0x1fffffffffff004120904824120904
def w165 : W := 0x1fffffffffff004924924924924924
def w166 : W := 0x1fffffffffff004f2793c9e4f2793c
def w167 : W := 0x1fffffffffff0059acd66b359acd66
def w168 : W := 0x1fffffffffffff8100804020100804
def w169 : W := 0x1fffffffffffff91c8e472391c8e47
def w170 : W := 0x1fffffffffffffc924924924924924
def w171 : W := 0x1fffffffffffffd9ecf67b3d9ecf67
def w172 : W := 0x1fffffffffffffef379bcde6f379bc
def w173 : W := 0x3fe00000000000000000000000000000
def w174 : W := 0x3fe00000000000001008040201008040
def w175 : W := 0x3fe00000000000002010080402010080
def w176 : W := 0x3fe00000000000004020100804020100
def w177 : W := 0x3fe000000000000070381c0e070381c0
def w178 : W := 0x3fe000000000000070b85c2e170b85c2
def w179 : W := 0x3fe000000000000071389c4e271389c4
def w180 : W := 0x3fe0000000000000743a1d0e8743a1d0
def w181 : W := 0x3fe0000000000000783c1e0f0783c1e0
def w182 : W := 0x3fe00000000000ff8000000000000000
def w183 : W := 0x3fe00000000000fff0381c0e070381c0
def w184 : W := 0x3fe000000001ff000000000000000000
def w185 : W := 0x3fe000000001ff000100804020100804
def w186 : W := 0x3fe000000001ff000804020100804020
def w187 : W := 0x3fe000000001ff001008040201008040
def w188 : W := 0x3fe000000001ff002010080402010080
def w189 : W := 0x3fe000000001ff004924924924924924
def w190 : W := 0x3fe000000001ff00592c964b2592c964
def w191 : W := 0x3fe000000001ff0069349a4d269349a4
def w192 : W := 0x3fe000000001ff0070381c0e070381c0
def w193 : W := 0x3fe000000001ff0071389c4e271389c4
def w194 : W := 0x3fe000000001ff00783c1e0f0783c1e0
def w195 : W := 0x3fe000000001ff00793c9e4f2793c9e4
def w196 : W := 0x3fe000000001ff007d3e9f4fa7d3e9f4
def w197 : W := 0x3fe000000001ffff8000000000000000
def w198 : W := 0x3fe000000001ffff80c06030180c0603
def w199 : W := 0x3fe000000001ffffc924924924924924
def w200 : W := 0x3fe000000001fffff0381c0e070381c0
def w201 : W := 0x3fe000000001fffff0f87c3e1f0f87c3
def w202 : W := 0x3fe000000001fffff93c9e4f2793c9e4
def w203 : W := 0x3fe000000001fffff9fcfe7f3f9fcfe7
def w204 : W := 0x3fe0000003fe00000000000000000000
def w205 : W := 0x3fe0000003fe00000241209048241209
def w206 : W := 0x3fe0000003fe000002c160b0582c160b
def w207 : W := 0x3fe0000003fe000006432190c8643219
def w208 : W := 0x3fe0000003fe00000a45229148a45229
def w209 : W := 0x3fe0000003fe000070381c0e070381c0
def w210 : W := 0x3fe0000003fe000072793c9e4f2793c9
def w211 : W := 0x3fe0000003fe00ff8241209048241209
def w212 : W := 0x3fe0000003ffff000000000000000000
def w213 : W := 0x3fe0000003ffff000241209048241209
def w214 : W := 0x3fe0000003ffff004924924924924924
def w215 : W := 0x3fe0000003ffff004b65b2d96cb65b2d
def w216 : W := 0x3fe0000003ffff0070381c0e070381c0
def w217 : W := 0x3fe0000003ffff00793c9e4f2793c9e4
def w218 : W := 0x3fe0000003ffff007b7dbedf6fb7dbed
def w219 : W := 0x3fe0000003ffffff8000000000000000
def w220 : W := 0x3fe0000003ffffff80c06030180c0603
def w221 : W := 0x3fe0000003ffffff8241209048241209
def w222 : W := 0x3fe0000003ffffff82c160b0582c160b
def w223 : W := 0x3fe0000003ffffffcbe5f2f97cbe5f2f
def w224 : W := 0x3fe0000003fffffff2f97cbe5f2f97cb
def w225 : W := 0x3fe0000003fffffffbfdfeff7fbfdfef
def w226 : W := 0x3fe00007fc00000070381c0e070381c0
def w227 : W := 0x3fe00007fc01ff0070381c0e070381c0
def w228 : W := 0x3fe00007fc01ff00793c9e4f2793c9e4
def w229 : W := 0x3fe00007fffe00000241209048241209
def w230 : W := 0x3fe00007ffffff000241209048241209
def w231 : W := 0x3fe00007ffffffff82c160b0582c160b
def w232 : W := 0x3fe00ff80000000070381c0e070381c0
def w233 : W := 0x3fe00ff8000000ff8000000000000000
def w234 : W := 0x3fe00ff8000000ffa412090482412090
def w235 : W := 0x3fe00ff8000000ffb41a0d068341a0d0
def w236 : W := 0x3fe00ff8000000ffe432190c86432190
def w237 : W := 0x3fe00ff8000000fff0381c0e070381c0
def w238 : W := 0x3fe00ff8000000fff43a1d0e8743a1d0
def w239 : W := 0x3fe00ff8000000fffc3e1f0f87c3e1f0
def w240 : W := 0x3fe00ff80001ff00793c9e4f2793c9e4
def w241 : W := 0x3fe00ff80001ffffa412090482412090
def w242 : W := 0x3fe00ff80001ffffac160b0582c160b0
def w243 : W := 0x3fe00ff80001ffffb41a0d068341a0d0
def w244 : W := 0x3fe00ff80001ffffed369b4da6d369b4
def w245 : W := 0x3fe00ff80001fffff43a1d0e8743a1d0
def w246 : W := 0x3fe00ff80001fffff4fa7d3e9f4fa7d3
def w247 : W := 0x3fe00ff80001fffffc3e1f0f87c3e1f0
def w248 : W := 0x3fe00ff80001fffffd3e9f4fa7d3e9f4
def w249 : W := 0x3fe00ff803fe00000241209048241209
def w250 : W := 0x3fe00ff803fe00ffa412090482412090
def w251 : W := 0x3fe00ff803fe00ffa6532994ca653299
def w252 : W := 0x3fe00ff803fe00fff43a1d0e8743a1d0
def w253 : W := 0x3fe00ff803fe00fff67b3d9ecf67b3d9
def w254 : W := 0x3fe00ff803ffffff82c160b0582c160b
def w255 : W := 0x3fe00ff803ffffffa412090482412090
def w256 : W := 0x3fe00ff803ffffffa6d369b4da6d369b
def w257 : W := 0x3fe00ff803fffffff43a1d0e8743a1d0
def w258 : W := 0x3fe00ff803fffffff6fb7dbedf6fb7db
def w259 : W := 0x3fe00ffffc0000fff43a1d0e8743a1d0
def w260 : W := 0x3fe00ffffffe00000100804020100804
def w261 : W := 0x3fe00ffffffe00000341a0d068341a0d
def w262 : W := 0x3fe00ffffffe00004120904824120904
def w263 : W := 0x3fe00ffffffe000071389c4e271389c4
def w264 : W := 0x3fe00ffffffe00ff8100804020100804
def w265 : W := 0x3fe00ffffffe00fff53a9d4ea753a9d4
def w266 : W := 0x3fe00fffffffff000100804020100804
def w267 : W := 0x3fe00fffffffff000904824120904824
def w268 : W := 0x3fe00fffffffff004924924924924924
def w269 : W := 0x3fe00fffffffff004b65b2d96cb65b2d
def w270 : W := 0x3fe00fffffffff0071389c4e271389c4
def w271 : W := 0x3fe00fffffffff00793c9e4f2793c9e4
def w272 : W := 0x3fe00fffffffffff8100804020100804
def w273 : W := 0x3fe00fffffffffff83c1e0f0783c1e0f
def w274 : W := 0x3fe00fffffffffffc924924924924924
def w275 : W := 0x3fe00fffffffffffcbe5f2f97cbe5f2f
def w276 : W := 0x3fe00ffffffffffffd3e9f4fa7d3e9f4
def w277 : W := 0x3ffff000000000000000000000000000
def w278 : W := 0x3ffff000000000000e070381c0e07038
def w279 : W := 0x3ffff0000000000070381c0e070381c0
def w280 : W := 0x3ffff000000000007e3f1f8fc7e3f1f8
def w281 : W := 0x3ffff000000000ff8e070381c0e07038
def w282 : W := 0x3ffff000000000fff0381c0e070381c0
def w283 : W := 0x3ffff0000001ff000000000000000000
def w284 : W := 0x3ffff0000001ff000e070381c0e07038
def w285 : W := 0x3ffff0000001ff004924924924924924
def w286 : W := 0x3ffff0000001ff004f2793c9e4f2793c
def w287 : W := 0x3ffff0000001ff0070381c0e070381c0
def w288 : W := 0x3ffff0000001ff00793c9e4f2793c9e4
def w289 : W := 0x3ffff0000001ff007f3f9fcfe7f3f9fc
def w290 : W := 0x3ffff0000001ffff80c06030180c0603
def w291 : W := 0x3ffff00003fe00000000000000000000
def w292 : W := 0x3ffff00003fe00000241209048241209
def w293 : W := 0x3ffff00003fe000006432190c8643219
def w294 : W := 0x3ffff00003fe00000a45229148a45229
def w295 : W := 0x3ffff00003fe00000e070381c0e07038
def w296 : W := 0x3ffff00003fe00000e472391c8e47239
def w297 : W := 0x3ffff00003fe00007e7f3f9fcfe7f3f9
def w298 : W := 0x3ffff00003fe00ff8241209048241209
def w299 : W := 0x3ffff00003fe00ff8e472391c8e47239
def w300 : W := 0x3ffff00003ffff000000000000000000
def w301 : W := 0x3ffff00003ffff000241209048241209
def w302 : W := 0x3ffff00003ffff000e472391c8e47239
def w303 : W := 0x3ffff00003ffff004f2793c9e4f2793c
def w304 : W := 0x3ffff00003ffff004f67b3d9ecf67b3d
def w305 : W := 0x3ffff00003ffffff82c160b0582c160b
def w306 : W := 0x3ffff00003ffffff8e472391c8e47239
def w307 : W := 0x3ffff00003ffffff8ec763b1d8ec763b
def w308 : W := 0x3ffff007fc0000000000000000000000
def w309 : W := 0x3ffff007fc0000001088442211088442
def w310 : W := 0x3ffff007fc00000030984c26130984c2
def w311 : W := 0x3ffff007fc00000050a8542a150a8542
def w312 : W := 0x3ffff007fc00000070381c0e070381c0
def w313 : W := 0x3ffff007fc00000070b85c2e170b85c2
def w314 : W := 0x3ffff007fc0000007ebf5fafd7ebf5fa
def w315 : W := 0x3ffff007fc0000ff9088442211088442
def w316 : W := 0x3ffff007fc0000fff0b85c2e170b85c2
def w317 : W := 0x3ffff007fc01ff000000000000000000
def w318 : W := 0x3ffff007fc01ff001088442211088442
def w319 : W := 0x3ffff007fc01ff0070b85c2e170b85c2
def w320 : W := 0x3ffff007fc01ff00793c9e4f2793c9e4
def w321 : W := 0x3ffff007fc01ff0079bcde6f379bcde6
def w322 : W := 0x3ffff007fc01ffff90c86432190c8643
def w323 : W := 0x3ffff007fc01fffff0b85c2e170b85c2
def w324 : W := 0x3ffff007fc01fffff0f87c3e1f0f87c3
def w325 : W := 0x3ffff007fffe00000000000000000000
def w326 : W := 0x3ffff007fffe00000241209048241209
def w327 : W := 0x3ffff007fffe00000e472391c8e47239
def w328 : W := 0x3ffff007fffe00001088442211088442
def w329 : W := 0x3ffff007fffe000012c964b2592c964b
def w330 : W := 0x3ffff007fffe00001ecf67b3d9ecf67b
def w331 : W := 0x3ffff007fffe000070b85c2e170b85c2
def w332 : W := 0x3ffff007fffe000072f97cbe5f2f97cb
def w333 : W := 0x3ffff007fffe00007eff7fbfdfeff7fb
def w334 : W := 0x3ffff007ffffffff82c160b0582c160b
def w335 : W := 0x3ffff007ffffffff90c86432190c8643
def w336 : W := 0x3ffff007ffffffff92c964b2592c964b
def w337 : W := 0x3ffffff8000000ffa412090482412090
def w338 : W := 0x3ffffff8000000ffae170b85c2e170b8
def w339 : W := 0x3ffffff8000000fff43a1d0e8743a1d0
def w340 : W := 0x3ffffff8000000fffe3f1f8fc7e3f1f8
def w341 : W := 0x3ffffff80001ffffa412090482412090
def w342 : W := 0x3ffffff80001ffffae170b85c2e170b8
def w343 : W := 0x3ffffff80001ffffef379bcde6f379bc
def w344 : W := 0x3ffffff80001fffff43a1d0e8743a1d0
def w345 : W := 0x3ffffff80001fffffd3e9f4fa7d3e9f4
def w346 : W := 0x3ffffff80001ffffff3f9fcfe7f3f9fc
def w347 : W := 0x3ffffff803fe00000e472391c8e47239
def w348 : W := 0x3ffffff803fe00ffae170b85c2e170b8
def w349 : W := 0x3ffffff803fe00ffae572b95cae572b9
def w350 : W := 0x3ffffffffc00000070b85c2e170b85c2
def w351 : W := 0x3ffffffffc0000fff43a1d0e8743a1d0
def w352 : W := 0x3ffffffffc0000fff4ba5d2e974ba5d2
def w353 : W := 0x3ffffffffffe00000100804020100804
def w354 : W := 0x3ffffffffffe00000f0783c1e0f0783c
def w355 : W := 0x3ffffffffffe00000f47a3d1e8f47a3d
def w356 : W := 0x3ffffffffffe000071389c4e271389c4
def w357 : W := 0x3ffffffffffe000071b8dc6e371b8dc6
def w358 : W := 0x3fffffffffffff000100804020100804
def w359 : W := 0x3fffffffffffff000f0783c1e0f0783c
def w360 : W := 0x3fffffffffffff004924924924924924
def w361 : W := 0x3fffffffffffff004f2793c9e4f2793c
def w362 : W := 0x3fffffffffffff004f67b3d9ecf67b3d
def w363 : W := 0x3fffffffffffff0071389c4e271389c4
def w364 : W := 0x3fffffffffffff00793c9e4f2793c9e4
def w365 : W := 0x3fffffffffffff0079bcde6f379bcde6
def t2 := (n (n (n (n z [w38,w336,w358] z) [w38,w336,w360] z) [w55,w336,w341] (n (n z [w63,w336,w337] z) [w131,w266,w336] z)) [w131,w268,w336] (n (n (n z [w137,w260,w336] z) [w156,w241,w336] z) [w162,w234,w336] (n z [w165,w234,w336] z)))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht2 : t2.all (blocked 1 z) = true := by
  decide +kernel
lemma s2 : sound 2 t2 := layer_sound (empty_sound 1) ht2
def t3aa := (n (n (n (n (n z [w17,w38,w336,w353] z) [w17,w55,w334,w351] (n z [w17,w55,w335,w348] z)) [w17,w55,w336,w337] (n (n z [w17,w121,w260,w348] z) [w17,w131,w260,w336] (n z [w17,w134,w260,w335] z))) [w17,w156,w222,w351] (n (n (n z [w17,w156,w234,w336] z) [w17,w156,w238,w334] (n z [w22,w55,w292,w352] z)) [w22,w55,w296,w350] (n (n z [w22,w55,w309,w349] z) [w22,w55,w313,w347] (n z [w22,w105,w260,w349] z)))) [w22,w156,w205,w352] (n (n (n (n z [w23,w38,w63,w325] z) [w23,w38,w329,w360] (n z [w23,w63,w329,w337] z)) [w23,w131,w268,w329] (n (n z [w23,w165,w234,w329] z) [w38,w55,w121,w300] (n z [w38,w55,w222,w317] z))) [w38,w55,w283,w336] (n (n (n z [w38,w55,w285,w336] z) [w38,w55,w303,w335] (n z [w38,w55,w306,w323] z)) [w38,w55,w320,w334] (n (n z [w38,w63,w121,w291] z) [w38,w63,w222,w308] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht3aa : t3aa.all (blocked 2 t2) = true := by
  decide +kernel
def t3ab := (n (n (n (n (n z [w38,w63,w295,w335] z) [w38,w63,w312,w334] (n z [w38,w64,w296,w323] z)) [w38,w64,w306,w313] (n (n z [w38,w69,w266,w336] z) [w38,w69,w268,w336] (n z [w38,w73,w268,w335] z))) [w38,w80,w260,w336] (n (n (n z [w38,w87,w260,w336] z) [w38,w91,w260,w335] (n z [w38,w103,w222,w266] z)) [w38,w103,w222,w268] (n (n z [w38,w105,w222,w358] z) [w38,w105,w222,w360] (n z [w38,w121,w162,w204] z)))) [w38,w121,w165,w204] (n (n (n (n z [w38,w121,w205,w358] z) [w38,w121,w205,w360] (n z [w38,w156,w184,w336] z)) [w38,w156,w189,w336] (n (n z [w38,w156,w195,w334] z) [w38,w162,w173,w336] (n z [w38,w165,w173,w336] z))) [w38,w165,w177,w334] (n (n (n z [w44,w55,w296,w313] z) [w46,w64,w296,w313] (n z [w47,w64,w296,w313] z)) [w55,w69,w241,w336] (n (n z [w55,w80,w234,w336] z) [w55,w87,w234,w336] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht3ab : t3ab.all (blocked 2 t2) = true := by
  decide +kernel
def t3a := (n t3aa [w38,w63,w277,w336] t3ab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht3a : t3a.all (blocked 2 t2) = true := by
  simp only [t3a, ReplayTree.all, n, ht3aa, ht3ab, Bool.true_and, Bool.and_true]
  decide +kernel
def t3ba := (n (n (n (n (n z [w55,w93,w205,w352] z) [w55,w103,w222,w241] (n z [w55,w103,w222,w245] z)) [w55,w105,w134,w219] (n (n z [w55,w105,w197,w349] z) [w55,w105,w222,w341] (n z [w55,w111,w222,w238] z))) [w55,w114,w238,w334] (n (n (n z [w55,w118,w205,w238] z) [w55,w121,w134,w212] (n z [w55,w121,w137,w204] z)) [w55,w121,w139,w204] (n (n z [w55,w121,w205,w341] z) [w55,w131,w184,w336] (n z [w55,w131,w189,w336] z)))) [w55,w134,w214,w335] (n (n (n (n z [w55,w137,w173,w336] z) [w55,w147,w195,w334] (n z [w60,w103,w222,w238] z)) [w60,w121,w134,w204] (n (n z [w63,w69,w234,w336] z) [w63,w73,w250,w335] (n z [w63,w103,w222,w234] z))) [w63,w105,w222,w337] (n (n (n z [w63,w121,w131,w204] z) [w63,w121,w205,w337] (n z [w63,w131,w173,w336] z)) [w63,w147,w177,w334] (n (n z [w73,w105,w256,w272] z) [w73,w105,w256,w274] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht3ba : t3ba.all (blocked 2 t2) = true := by
  decide +kernel
def t3bb := (n (n (n (n (n z [w73,w121,w250,w268] z) [w91,w121,w250,w260] (n z [w105,w131,w222,w266] z)) [w105,w131,w222,w268] (n (n z [w105,w134,w222,w272] z) [w105,w156,w222,w241] (n z [w105,w156,w222,w245] z))) [w105,w162,w222,w238] (n (n (n z [w105,w165,w222,w234] z) [w121,w131,w205,w268] (n z [w121,w134,w205,w266] z)) [w121,w134,w222,w266] (n (n z [w121,w134,w251,w268] z) [w121,w137,w205,w260] z))) [w121,w139,w205,w260] (n (n (n (n z [w121,w144,w251,w260] z) [w121,w144,w260,w349] (n z [w121,w162,w205,w234] z)) [w121,w162,w222,w238] (n (n z [w121,w165,w205,w234] z) [w121,w168,w205,w238] (n z [w147,w156,w195,w222] z))) [w147,w165,w177,w222] (n (n (n z [w149,w156,w222,w248] z) [w149,w165,w222,w238] (n z [w154,w168,w177,w205] z)) [w154,w170,w177,w205] (n (n z [w155,w168,w177,w205] z) [w156,w222,w248,w352] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht3bb : t3bb.all (blocked 2 t2) = true := by
  decide +kernel
def t3b := (n t3ba [w73,w105,w258,w272] t3bb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht3b : t3b.all (blocked 2 t2) = true := by
  simp only [t3b, ReplayTree.all, n, ht3ba, ht3bb, Bool.true_and, Bool.and_true]
  decide +kernel
def t3 := (n t3a [w55,w91,w250,w335] t3b)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht3 : t3.all (blocked 2 t2) = true := by
  simp only [t3, ReplayTree.all, n, ht3a, ht3b, Bool.true_and, Bool.and_true]
  decide +kernel
lemma s3 : sound 3 t3 := layer_sound s2 ht3
def t4aaaaa := (n (n (n (n (n z [w13,w37,w55,w296,w313] z) [w13,w38,w58,w296,w313] (n z [w13,w55,w103,w222,w238] z)) [w13,w55,w121,w134,w204] (n (n z [w13,w105,w156,w222,w238] z) [w13,w121,w134,w205,w260] (n z [w17,w23,w38,w55,w325] z))) [w17,w23,w38,w329,w353] (n (n (n z [w17,w23,w38,w330,w353] z) [w17,w23,w38,w332,w353] (n z [w17,w23,w38,w333,w353] z)) [w17,w23,w55,w326,w351] (n (n z [w17,w23,w55,w328,w348] z) [w17,w23,w55,w329,w337] z))) [w17,w23,w105,w260,w348] (n (n (n (n z [w17,w23,w131,w260,w329] z) [w17,w23,w134,w260,w328] (n z [w17,w23,w156,w205,w351] z)) [w17,w23,w156,w234,w329] (n (n z [w17,w23,w156,w238,w326] z) [w17,w38,w55,w121,w291] z)) [w17,w38,w55,w222,w308] (n (n (n z [w17,w38,w55,w277,w336] z) [w17,w38,w55,w295,w335] (n z [w17,w38,w55,w312,w334] z)) [w17,w38,w69,w260,w336] (n (n z [w17,w38,w73,w260,w335] z) [w17,w38,w103,w222,w260] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4aaaaa : t4aaaaa.all (blocked 3 t3) = true := by
  decide +kernel
def t4aaaab := (n (n (n (n (n z [w17,w38,w121,w156,w204] z) [w17,w38,w121,w205,w353] (n z [w17,w38,w121,w260,w295] z)) [w17,w38,w121,w296,w353] (n (n z [w17,w38,w156,w173,w336] z) [w17,w38,w156,w177,w334] z)) [w17,w38,w156,w222,w312] (n (n (n z [w17,w38,w222,w313,w353] z) [w17,w47,w58,w296,w313] (n z [w17,w55,w69,w222,w259] z)) [w17,w55,w69,w231,w238] (n (n z [w17,w55,w69,w234,w336] z) [w17,w55,w73,w250,w335] z))) [w17,w55,w103,w222,w234] (n (n (n (n z [w17,w55,w103,w222,w238] z) [w17,w55,w103,w222,w351] (n z [w17,w55,w103,w238,w334] z)) [w17,w55,w105,w220,w348] (n (n z [w17,w55,w105,w222,w337] z) [w17,w55,w105,w305,w339] z)) [w17,w55,w119,w205,w351] (n (n (n z [w17,w55,w121,w131,w204] z) [w17,w55,w121,w134,w204] (n z [w17,w55,w121,w145,w173] z)) [w17,w55,w121,w204,w348] (n (n z [w17,w55,w121,w205,w337] z) [w17,w55,w127,w134,w173] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4aaaab : t4aaaab.all (blocked 3 t3) = true := by
  decide +kernel
def t4aaaa := (n t4aaaaa [w17,w38,w105,w222,w353] t4aaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4aaaa : t4aaaa.all (blocked 3 t3) = true := by
  simp only [t4aaaa, ReplayTree.all, n, ht4aaaaa, ht4aaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t4aaaba := (n (n (n (n (n z [w17,w55,w134,w204,w335] z) [w17,w55,w147,w177,w334] (n z [w17,w55,w205,w322,w338] z)) [w17,w73,w105,w256,w264] (n (n z [w17,w73,w121,w250,w260] z) [w17,w103,w156,w222,w238] (n z [w17,w105,w131,w222,w260] z))) [w17,w105,w134,w220,w260] (n (n (n z [w17,w105,w134,w222,w264] z) [w17,w105,w156,w222,w234] (n z [w17,w105,w156,w222,w238] z)) [w17,w105,w156,w222,w339] (n (n z [w17,w105,w156,w238,w305] z) [w17,w105,w157,w222,w238] z))) [w17,w107,w156,w222,w238] (n (n (n (n z [w17,w119,w156,w205,w238] z) [w17,w121,w131,w205,w260] (n z [w17,w121,w134,w204,w260] z)) [w17,w121,w134,w205,w260] (n (n z [w17,w121,w134,w205,w262] z) [w17,w121,w134,w210,w260] z)) [w17,w121,w134,w222,w260] (n (n (n z [w17,w121,w134,w251,w260] z) [w17,w121,w134,w260,w296] (n z [w17,w121,w134,w260,w329] z)) [w17,w121,w134,w260,w336] (n (n z [w17,w121,w134,w260,w349] z) [w17,w121,w156,w205,w234] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4aaaba : t4aaaba.all (blocked 3 t3) = true := by
  decide +kernel
def t4aaabb := (n (n (n (n (n z [w17,w121,w160,w205,w238] z) [w17,w121,w205,w260,w338] (n z [w17,w134,w205,w260,w322] z)) [w17,w147,w156,w177,w222] (n (n z [w17,w149,w156,w222,w238] z) [w17,w154,w160,w177,w205] z)) [w17,w156,w222,w238,w313] (n (n (n z [w17,w156,w222,w238,w329] z) [w17,w156,w222,w238,w336] (n z [w17,w156,w222,w238,w352] z)) [w22,w36,w55,w296,w313] (n (n z [w22,w38,w55,w292,w313] z) [w22,w38,w55,w296,w309] z))) [w22,w38,w55,w296,w313] (n (n (n (n z [w22,w38,w55,w296,w323] z) [w22,w38,w55,w306,w313] (n z [w22,w38,w64,w296,w313] z)) [w22,w38,w105,w260,w296] (n (n z [w22,w38,w156,w205,w313] z) [w22,w46,w55,w296,w313] z)) [w22,w47,w55,w296,w313] (n (n (n z [w22,w55,w69,w205,w352] z) [w22,w55,w73,w205,w350] (n z [w22,w55,w73,w249,w313] z)) [w22,w55,w73,w251,w309] (n (n z [w22,w55,w103,w205,w238] z) [w22,w55,w105,w134,w204] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4aaabb : t4aaabb.all (blocked 3 t3) = true := by
  decide +kernel
def t4aaab := (n t4aaaba [w17,w121,w156,w222,w238] t4aaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4aaab : t4aaab.all (blocked 3 t3) = true := by
  simp only [t4aaab, ReplayTree.all, n, ht4aaaba, ht4aaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t4aaa := (n t4aaaa [w17,w55,w131,w173,w336] t4aaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4aaa : t4aaa.all (blocked 3 t3) = true := by
  simp only [t4aaa, ReplayTree.all, n, ht4aaaa, ht4aaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t4aabaa := (n (n (n (n (n z [w22,w55,w105,w177,w347] z) [w22,w55,w105,w232,w296] (n z [w22,w55,w105,w238,w292] z)) [w22,w55,w128,w205,w313] (n (n z [w22,w55,w134,w205,w309] z) [w22,w55,w134,w296,w313] (n z [w22,w55,w146,w177,w296] z))) [w22,w55,w149,w177,w292] (n (n (n z [w22,w55,w149,w296,w313] z) [w22,w55,w238,w296,w313] (n z [w22,w55,w251,w296,w313] z)) [w22,w55,w296,w313,w349] (n (n z [w22,w55,w296,w313,w352] z) [w22,w73,w105,w251,w260] z))) [w22,w105,w134,w205,w260] (n (n (n (n z [w22,w105,w156,w205,w238] z) [w22,w149,w156,w177,w205] (n z [w23,w38,w55,w285,w329] z)) [w23,w38,w55,w302,w319] (n (n z [w23,w38,w55,w303,w328] z) [w23,w38,w55,w320,w326] z)) [w23,w38,w60,w292,w313] (n (n (n z [w23,w38,w60,w296,w309] z) [w23,w38,w60,w296,w313] (n z [w23,w38,w60,w296,w319] z)) [w23,w38,w60,w302,w313] (n (n z [w23,w38,w63,w103,w204] z) [w23,w38,w63,w105,w291] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4aabaa : t4aabaa.all (blocked 3 t3) = true := by
  decide +kernel
def t4aabab := (n (n (n (n (n z [w23,w38,w63,w277,w329] z) [w23,w38,w63,w292,w309] (n z [w23,w38,w63,w295,w328] z)) [w23,w38,w63,w296,w328] (n (n z [w23,w38,w63,w312,w326] z) [w23,w38,w63,w313,w326] z)) [w23,w38,w64,w296,w313] (n (n (n z [w23,w38,w69,w268,w329] z) [w23,w38,w73,w268,w328] (n z [w23,w38,w87,w260,w329] z)) [w23,w38,w91,w260,w328] (n (n z [w23,w38,w91,w261,w328] z) [w23,w38,w103,w205,w268] z))) [w23,w38,w105,w165,w204] (n (n (n (n z [w23,w38,w105,w205,w360] z) [w23,w38,w105,w266,w296] (n z [w23,w38,w105,w268,w292] z)) [w23,w38,w156,w189,w329] (n (n z [w23,w38,w156,w195,w326] z) [w23,w38,w159,w195,w326] z)) [w23,w38,w162,w205,w313] (n (n (n z [w23,w38,w165,w173,w329] z) [w23,w38,w165,w177,w326] (n z [w23,w38,w165,w205,w309] z)) [w23,w46,w55,w292,w313] (n (n z [w23,w46,w55,w296,w309] z) [w23,w46,w55,w296,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4aabab : t4aabab.all (blocked 3 t3) = true := by
  decide +kernel
def t4aaba := (n t4aabaa [w23,w38,w63,w205,w308] t4aabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4aaba : t4aaba.all (blocked 3 t3) = true := by
  simp only [t4aaba, ReplayTree.all, n, ht4aabaa, ht4aabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t4aabba := (n (n (n (n (n z [w23,w46,w55,w302,w313] z) [w23,w46,w60,w296,w313] (n z [w23,w46,w105,w260,w296] z)) [w23,w46,w156,w205,w313] (n (n z [w23,w48,w55,w296,w313] z) [w23,w49,w55,w296,w313] (n z [w23,w50,w55,w292,w352] z))) [w23,w50,w55,w296,w350] (n (n (n z [w23,w50,w55,w309,w349] z) [w23,w50,w55,w313,w347] (n z [w23,w50,w105,w260,w349] z)) [w23,w50,w156,w205,w352] (n (n z [w23,w55,w87,w234,w329] z) [w23,w55,w91,w250,w328] z))) [w23,w55,w103,w205,w245] (n (n (n (n z [w23,w55,w105,w134,w212] z) [w23,w55,w105,w139,w204] (n z [w23,w55,w105,w245,w292] z)) [w23,w55,w111,w205,w238] (n (n z [w23,w55,w114,w238,w326] z) [w23,w55,w131,w189,w329] z)) [w23,w55,w134,w214,w328] (n (n (n z [w23,w55,w139,w205,w309] z) [w23,w55,w139,w296,w313] (n z [w23,w55,w139,w302,w313] z)) [w23,w55,w144,w251,w309] (n (n z [w23,w55,w144,w309,w349] z) [w23,w55,w147,w195,w326] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4aabba : t4aabba.all (blocked 3 t3) = true := by
  decide +kernel
def t4aabbb := (n (n (n (n (n z [w23,w55,w245,w296,w313] z) [w23,w55,w245,w296,w319] (n z [w23,w55,w248,w292,w352] z)) [w23,w60,w103,w205,w238] (n (n z [w23,w60,w105,w134,w204] z) [w23,w60,w105,w238,w292] z)) [w23,w60,w134,w205,w309] (n (n (n z [w23,w60,w134,w296,w313] z) [w23,w60,w238,w296,w313] (n z [w23,w63,w69,w234,w329] z)) [w23,w63,w73,w250,w328] (n (n z [w23,w63,w103,w205,w234] z) [w23,w63,w105,w131,w204] z))) [w23,w63,w105,w205,w337] (n (n (n (n z [w23,w63,w105,w234,w292] z) [w23,w63,w131,w173,w329] (n z [w23,w63,w131,w205,w309] z)) [w23,w63,w134,w251,w309] (n (n z [w23,w63,w147,w177,w326] z) [w23,w63,w149,w238,w292] z)) [w23,w73,w105,w250,w268] (n (n (n z [w23,w91,w105,w250,w260] z) [w23,w91,w105,w250,w261] (n z [w23,w91,w105,w252,w261] z)) [w23,w91,w125,w238,w261] (n (n z [w23,w105,w131,w205,w268] z) [w23,w105,w134,w205,w266] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4aabbb : t4aabbb.all (blocked 3 t3) = true := by
  decide +kernel
def t4aabb := (n t4aabba [w23,w55,w149,w248,w292] t4aabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4aabb : t4aabb.all (blocked 3 t3) = true := by
  simp only [t4aabb, ReplayTree.all, n, ht4aabba, ht4aabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t4aab := (n t4aaba [w23,w46,w55,w296,w319] t4aabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4aab : t4aab.all (blocked 3 t3) = true := by
  simp only [t4aab, ReplayTree.all, n, ht4aaba, ht4aabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t4aa := (n t4aaa [w22,w55,w105,w173,w349] t4aab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4aa : t4aa.all (blocked 3 t3) = true := by
  simp only [t4aa, ReplayTree.all, n, ht4aaa, ht4aab, Bool.true_and, Bool.and_true]
  decide +kernel
def t4abaaa := (n (n (n (n (n z [w23,w105,w134,w251,w268] z) [w23,w105,w139,w205,w260] (n z [w23,w105,w144,w251,w260] z)) [w23,w105,w144,w260,w349] (n (n z [w23,w105,w156,w205,w245] z) [w23,w105,w162,w205,w238] (n z [w23,w105,w165,w205,w234] z))) [w23,w121,w162,w205,w238] (n (n (n z [w23,w134,w159,w195,w229] z) [w23,w147,w156,w195,w205] (n z [w23,w147,w159,w195,w205] z)) [w23,w147,w165,w177,w205] (n (n z [w23,w148,w159,w195,w205] z) [w23,w149,w156,w205,w248] z))) [w23,w149,w165,w205,w238] (n (n (n (n z [w23,w156,w205,w248,w352] z) [w26,w47,w55,w296,w313] (n z [w27,w46,w55,w296,w313] z)) [w38,w55,w69,w184,w336] (n (n z [w38,w55,w69,w189,w336] z) [w38,w55,w69,w195,w231] z)) [w38,w55,w73,w105,w219] (n (n (n z [w38,w55,w73,w121,w212] z) [w38,w55,w73,w214,w335] (n z [w38,w55,w73,w221,w323] z)) [w38,w55,w80,w121,w204] (n (n z [w38,w55,w80,w173,w336] z) [w38,w55,w84,w121,w204] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4abaaa : t4abaaa.all (blocked 3 t3) = true := by
  decide +kernel
def t4abaab := (n (n (n (n (n z [w38,w55,w87,w173,w336] z) [w38,w55,w91,w121,w204] (n z [w38,w55,w91,w127,w173] z)) [w38,w55,w91,w204,w335] (n (n z [w38,w55,w93,w205,w313] z) [w38,w55,w95,w205,w323] z)) [w38,w55,w103,w184,w222] (n (n (n z [w38,w55,w103,w189,w222] z) [w38,w55,w103,w192,w222] (n z [w38,w55,w103,w195,w222] z)) [w38,w55,w103,w195,w334] (n (n z [w38,w55,w103,w222,w248] z) [w38,w55,w103,w222,w271] z))) [w38,w55,w103,w222,w320] (n (n (n (n z [w38,w55,w105,w197,w296] z) [w38,w55,w105,w200,w306] (n z [w38,w55,w105,w220,w303] z)) [w38,w55,w105,w222,w283] (n (n z [w38,w55,w105,w222,w285] z) [w38,w55,w105,w288,w305] z)) [w38,w55,w111,w177,w222] (n (n (n z [w38,w55,w114,w177,w334] z) [w38,w55,w118,w177,w205] (n z [w38,w55,w119,w205,w320] z)) [w38,w55,w120,w177,w306] (n (n z [w38,w55,w121,w144,w204] z) [w38,w55,w121,w166,w204] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4abaab : t4abaab.all (blocked 3 t3) = true := by
  decide +kernel
def t4abaa := (n t4abaaa [w38,w55,w87,w121,w204] t4abaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4abaa : t4abaa.all (blocked 3 t3) = true := by
  simp only [t4abaa, ReplayTree.all, n, ht4abaaa, ht4abaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t4ababa := (n (n (n (n (n z [w38,w55,w121,w205,w283] z) [w38,w55,w121,w205,w285] (n z [w38,w55,w121,w287,w301] z)) [w38,w55,w205,w286,w322] (n (n z [w38,w55,w222,w284,w318] z) [w38,w60,w73,w121,w204] (n z [w38,w60,w103,w177,w222] z))) [w38,w60,w121,w296,w313] (n (n (n z [w38,w60,w222,w296,w313] z) [w38,w63,w69,w121,w204] (n z [w38,w63,w69,w173,w336] z)) [w38,w63,w69,w177,w231] (n (n z [w38,w63,w73,w105,w219] z) [w38,w63,w73,w121,w204] z))) [w38,w63,w73,w121,w212] (n (n (n (n z [w38,w63,w73,w127,w173] z) [w38,w63,w73,w204,w335] (n z [w38,w63,w91,w121,w204] z)) [w38,w63,w103,w173,w222] (n (n z [w38,w63,w103,w177,w222] z) [w38,w63,w103,w177,w334] z)) [w38,w63,w103,w195,w222] (n (n (n z [w38,w63,w103,w222,w238] z) [w38,w63,w103,w222,w263] (n z [w38,w63,w103,w222,w271] z)) [w38,w63,w103,w222,w312] (n (n z [w38,w63,w105,w220,w295] z) [w38,w63,w105,w222,w277] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4ababa : t4ababa.all (blocked 3 t3) = true := by
  decide +kernel
def t4ababb := (n (n (n (n (n z [w38,w63,w111,w177,w222] z) [w38,w63,w118,w177,w205] (n z [w38,w63,w119,w205,w312] z)) [w38,w63,w121,w134,w204] (n (n z [w38,w63,w121,w158,w204] z) [w38,w63,w121,w166,w204] z)) [w38,w63,w121,w204,w295] (n (n (n z [w38,w63,w121,w205,w277] z) [w38,w63,w121,w263,w295] (n z [w38,w63,w121,w279,w292] z)) [w38,w63,w121,w292,w313] (n (n z [w38,w63,w121,w296,w357] z) [w38,w63,w158,w222,w312] z))) [w38,w63,w205,w278,w322] (n (n (n (n z [w38,w63,w222,w278,w309] z) [w38,w63,w222,w296,w309] (n z [w38,w63,w222,w313,w355] z)) [w38,w63,w296,w313,w336] (n (n z [w38,w64,w73,w205,w323] z) [w38,w64,w73,w221,w313] z)) [w38,w64,w95,w205,w313] (n (n (n z [w38,w64,w105,w177,w306] z) [w38,w64,w105,w200,w296] (n z [w38,w64,w120,w177,w296] z)) [w38,w69,w105,w222,w266] (n (n z [w38,w69,w105,w222,w268] z) [w38,w69,w121,w205,w268] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4ababb : t4ababb.all (blocked 3 t3) = true := by
  decide +kernel
def t4abab := (n t4ababa [w38,w63,w105,w279,w305] t4ababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4abab : t4abab.all (blocked 3 t3) = true := by
  simp only [t4abab, ReplayTree.all, n, ht4ababa, ht4ababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t4aba := (n t4abaa [w38,w55,w121,w204,w303] t4abab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4aba : t4aba.all (blocked 3 t3) = true := by
  simp only [t4aba, ReplayTree.all, n, ht4abaa, ht4abab, Bool.true_and, Bool.and_true]
  decide +kernel
def t4abbaa := (n (n (n (n (n z [w38,w73,w105,w222,w266] z) [w38,w73,w105,w222,w267] (n z [w38,w73,w105,w222,w268] z)) [w38,w73,w105,w222,w272] (n (n z [w38,w73,w105,w222,w274] z) [w38,w73,w105,w266,w336] (n z [w38,w73,w105,w268,w336] z))) [w38,w73,w121,w204,w268] (n (n (n z [w38,w73,w121,w205,w266] z) [w38,w73,w121,w205,w268] (n z [w38,w73,w121,w222,w266] z)) [w38,w73,w121,w222,w268] (n (n z [w38,w73,w121,w251,w268] z) [w38,w73,w121,w268,w329] z))) [w38,w73,w121,w268,w336] (n (n (n (n z [w38,w73,w205,w268,w322] z) [w38,w73,w222,w266,w313] (n z [w38,w73,w222,w266,w318] z)) [w38,w73,w222,w268,w309] (n (n z [w38,w80,w121,w205,w260] z) [w38,w84,w121,w205,w260] z)) [w38,w87,w105,w222,w260] (n (n (n z [w38,w87,w121,w205,w260] z) [w38,w91,w105,w220,w260] (n z [w38,w91,w105,w222,w266] z)) [w38,w91,w105,w222,w268] (n (n z [w38,w91,w121,w204,w260] z) [w38,w91,w121,w205,w260] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4abbaa : t4abbaa.all (blocked 3 t3) = true := by
  decide +kernel
def t4abbab := (n (n (n (n (n z [w38,w91,w121,w205,w268] z) [w38,w91,w121,w210,w260] (n z [w38,w91,w121,w222,w260] z)) [w38,w91,w121,w251,w260] (n (n z [w38,w91,w121,w260,w296] z) [w38,w91,w121,w260,w329] z)) [w38,w91,w121,w260,w336] (n (n (n z [w38,w91,w205,w260,w322] z) [w38,w103,w156,w195,w222] (n z [w38,w103,w158,w222,w271] z)) [w38,w103,w165,w177,w222] (n (n z [w38,w103,w166,w222,w271] z) [w38,w105,w134,w222,w266] z))) [w38,w105,w134,w222,w268] (n (n (n (n z [w38,w105,w156,w184,w222] z) [w38,w105,w156,w189,w222] (n z [w38,w105,w156,w192,w222] z)) [w38,w105,w156,w195,w222] (n (n z [w38,w105,w156,w195,w305] z) [w38,w105,w156,w222,w248] z)) [w38,w105,w156,w222,w271] (n (n (n z [w38,w105,w156,w222,w288] z) [w38,w105,w156,w222,w364] (n z [w38,w105,w157,w195,w222] z)) [w38,w105,w158,w220,w271] (n (n z [w38,w105,w158,w222,w266] z) [w38,w105,w158,w222,w268] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4abbab : t4abbab.all (blocked 3 t3) = true := by
  decide +kernel
def t4abba := (n t4abbaa [w38,w91,w121,w205,w262] t4abbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4abba : t4abba.all (blocked 3 t3) = true := by
  simp only [t4abba, ReplayTree.all, n, ht4abbaa, ht4abbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t4abbba := (n (n (n (n (n z [w38,w105,w158,w222,w271] z) [w38,w105,w162,w177,w222] (n z [w38,w105,w163,w222,w270] z)) [w38,w105,w165,w173,w222] (n (n z [w38,w105,w165,w177,w222] z) [w38,w105,w165,w177,w305] (n z [w38,w105,w165,w195,w222] z))) [w38,w105,w165,w222,w238] (n (n (n z [w38,w105,w165,w222,w263] z) [w38,w105,w165,w222,w271] (n z [w38,w105,w165,w222,w279] z)) [w38,w105,w165,w222,w288] (n (n z [w38,w105,w165,w222,w356] z) [w38,w105,w165,w222,w364] z))) [w38,w105,w166,w220,w263] (n (n (n (n z [w38,w105,w166,w220,w271] z) [w38,w105,w166,w222,w268] (n z [w38,w105,w166,w222,w271] z)) [w38,w105,w222,w266,w284] (n (n z [w38,w105,w222,w266,w296] z) [w38,w105,w222,w266,w359] z)) [w38,w105,w222,w268,w278] (n (n (n z [w38,w105,w222,w268,w286] z) [w38,w105,w222,w268,w296] (n z [w38,w105,w222,w268,w354] z)) [w38,w105,w222,w268,w361] (n (n z [w38,w105,w222,w271,w355] z) [w38,w105,w222,w271,w362] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4abbba : t4abbba.all (blocked 3 t3) = true := by
  decide +kernel
def t4abbbb := (n (n (n (n (n z [w38,w119,w156,w195,w205] z) [w38,w119,w158,w205,w271] (n z [w38,w119,w165,w177,w205] z)) [w38,w119,w166,w205,w263] (n (n z [w38,w119,w166,w205,w271] z) [w38,w121,w134,w205,w268] z)) [w38,w121,w144,w205,w260] (n (n (n z [w38,w121,w156,w189,w205] z) [w38,w121,w156,w195,w222] (n z [w38,w121,w158,w205,w268] z)) [w38,w121,w158,w222,w271] (n (n z [w38,w121,w162,w173,w205] z) [w38,w121,w162,w177,w205] z))) [w38,w121,w162,w177,w222] (n (n (n (n z [w38,w121,w162,w177,w296] z) [w38,w121,w162,w177,w301] (n z [w38,w121,w162,w195,w205] z)) [w38,w121,w162,w205,w238] (n (n z [w38,w121,w162,w205,w263] z) [w38,w121,w162,w205,w287] z)) [w38,w121,w162,w205,w313] (n (n (n z [w38,w121,w162,w205,w363] z) [w38,w121,w163,w205,w263] (n z [w38,w121,w163,w205,w270] z)) [w38,w121,w164,w177,w205] (n (n z [w38,w121,w165,w173,w205] z) [w38,w121,w165,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4abbbb : t4abbbb.all (blocked 3 t3) = true := by
  decide +kernel
def t4abbb := (n t4abbba [w38,w107,w156,w195,w222] t4abbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4abbb : t4abbb.all (blocked 3 t3) = true := by
  simp only [t4abbb, ReplayTree.all, n, ht4abbba, ht4abbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t4abb := (n t4abba [w38,w105,w158,w222,w270] t4abbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4abb : t4abb.all (blocked 3 t3) = true := by
  simp only [t4abb, ReplayTree.all, n, ht4abba, ht4abbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t4ab := (n t4aba [w38,w73,w105,w220,w268] t4abb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4ab : t4ab.all (blocked 3 t3) = true := by
  simp only [t4ab, ReplayTree.all, n, ht4aba, ht4abb, Bool.true_and, Bool.and_true]
  decide +kernel
def t4a := (n t4aa [w23,w105,w134,w222,w266] t4ab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4a : t4a.all (blocked 3 t3) = true := by
  simp only [t4a, ReplayTree.all, n, ht4aa, ht4ab, Bool.true_and, Bool.and_true]
  decide +kernel
def t4baaaa := (n (n (n (n (n z [w38,w121,w165,w177,w292] z) [w38,w121,w165,w195,w205] (n z [w38,w121,w165,w205,w238] z)) [w38,w121,w165,w205,w263] (n (n z [w38,w121,w165,w205,w271] z) [w38,w121,w165,w205,w279] (n z [w38,w121,w165,w205,w288] z))) [w38,w121,w165,w205,w313] (n (n (n z [w38,w121,w165,w205,w356] z) [w38,w121,w165,w205,w364] (n z [w38,w121,w166,w204,w263] z)) [w38,w121,w166,w204,w271] (n (n z [w38,w121,w166,w205,w260] z) [w38,w121,w166,w205,w263] z))) [w38,w121,w166,w205,w268] (n (n (n (n z [w38,w121,w166,w205,w271] z) [w38,w121,w166,w205,w357] (n z [w38,w121,w166,w205,w365] z)) [w38,w121,w166,w222,w263] (n (n z [w38,w121,w166,w222,w271] z) [w38,w121,w166,w263,w296] z)) [w38,w121,w168,w177,w205] (n (n (n z [w38,w121,w170,w177,w205] z) [w38,w121,w205,w260,w286] (n z [w38,w121,w205,w260,w361] z)) [w38,w121,w205,w268,w278] (n (n z [w38,w121,w205,w268,w286] z) [w38,w121,w205,w268,w354] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4baaaa : t4baaaa.all (blocked 3 t3) = true := by
  decide +kernel
def t4baaab := (n (n (n (n (n z [w38,w149,w156,w195,w222] z) [w38,w149,w165,w177,w222] (n z [w38,w156,w195,w222,w313] z)) [w38,w156,w195,w222,w329] (n (n z [w38,w156,w195,w222,w336] z) [w38,w158,w222,w271,w313] z)) [w38,w162,w177,w205,w336] (n (n (n z [w38,w165,w177,w205,w336] z) [w38,w165,w177,w222,w329] (n z [w38,w165,w177,w222,w336] z)) [w44,w55,w73,w205,w313] (n (n z [w44,w55,w105,w177,w296] z) [w45,w50,w55,w296,w313] z))) [w46,w55,w65,w296,w313] (n (n (n (n z [w46,w55,w73,w121,w204] z) [w46,w55,w73,w221,w313] (n z [w46,w55,w103,w177,w222] z)) [w46,w55,w120,w177,w296] (n (n z [w46,w55,w121,w296,w313] z) [w46,w55,w222,w296,w313] z)) [w46,w64,w73,w205,w313] (n (n (n z [w46,w64,w105,w177,w296] z) [w46,w65,w105,w263,w296] (n z [w46,w65,w158,w205,w313] z)) [w46,w73,w105,w222,w260] (n (n z [w46,w73,w121,w205,w260] z) [w46,w105,w156,w177,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4baaab : t4baaab.all (blocked 3 t3) = true := by
  decide +kernel
def t4baaa := (n t4baaaa [w38,w121,w205,w268,w361] t4baaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4baaa : t4baaa.all (blocked 3 t3) = true := by
  simp only [t4baaa, ReplayTree.all, n, ht4baaaa, ht4baaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t4baaba := (n (n (n (n (n z [w46,w121,w156,w177,w205] z) [w46,w121,w158,w205,w263] (n z [w47,w64,w73,w205,w313] z)) [w47,w64,w105,w177,w296] (n (n z [w50,w55,w103,w222,w238] z) [w50,w55,w121,w134,w204] (n z [w50,w73,w121,w251,w260] z))) [w50,w105,w134,w222,w260] (n (n (n z [w50,w105,w156,w222,w238] z) [w50,w121,w134,w205,w260] (n z [w50,w121,w156,w205,w238] z)) [w50,w149,w156,w177,w222] (n (n z [w51,w55,w91,w121,w173] z) [w51,w63,w73,w121,w173] z))) [w53,w55,w69,w195,w222] (n (n (n (n z [w53,w63,w69,w177,w222] z) [w55,w63,w103,w222,w238] (n z [w55,w63,w121,w134,w204] z)) [w55,w69,w105,w222,w241] (n (n z [w55,w69,w105,w222,w245] z) [w55,w69,w149,w222,w248] z)) [w55,w69,w222,w248,w352] (n (n (n z [w55,w73,w105,w197,w251] z) [w55,w73,w105,w197,w253] (n z [w55,w73,w105,w197,w256] z)) [w55,w73,w105,w197,w258] (n (n z [w55,w73,w105,w199,w256] z) [w55,w73,w105,w219,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4baaba : t4baaba.all (blocked 3 t3) = true := by
  decide +kernel
def t4baabb := (n (n (n (n (n z [w55,w73,w105,w222,w241] z) [w55,w73,w105,w222,w242] (n z [w55,w73,w105,w222,w243] z)) [w55,w73,w105,w222,w245] (n (n z [w55,w73,w105,w222,w247] z) [w55,w73,w105,w222,w255] z)) [w55,w73,w105,w222,w257] (n (n (n z [w55,w73,w105,w241,w336] z) [w55,w73,w105,w248,w254] (n z [w55,w73,w113,w222,w245] z)) [w55,w73,w120,w221,w238] (n (n z [w55,w73,w121,w205,w241] z) [w55,w73,w121,w214,w250] z))) [w55,w73,w121,w222,w241] (n (n (n (n z [w55,w73,w121,w222,w245] z) [w55,w73,w146,w222,w248] (n z [w55,w73,w222,w241,w313] z)) [w55,w73,w222,w241,w318] (n (n z [w55,w73,w222,w245,w313] z) [w55,w73,w222,w245,w319] z)) [w55,w80,w105,w222,w238] (n (n (n z [w55,w80,w121,w205,w234] z) [w55,w80,w121,w222,w238] (n z [w55,w84,w105,w222,w245] z)) [w55,w84,w113,w222,w238] (n (n z [w55,w84,w121,w205,w234] z) [w55,w84,w121,w222,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4baabb : t4baabb.all (blocked 3 t3) = true := by
  decide +kernel
def t4baab := (n t4baaba [w55,w73,w105,w221,w245] t4baabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4baab : t4baab.all (blocked 3 t3) = true := by
  simp only [t4baab, ReplayTree.all, n, ht4baaba, ht4baabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t4baa := (n t4baaa [w46,w105,w158,w222,w263] t4baab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4baa : t4baa.all (blocked 3 t3) = true := by
  simp only [t4baa, ReplayTree.all, n, ht4baaa, ht4baab, Bool.true_and, Bool.and_true]
  decide +kernel
def t4babaa := (n (n (n (n (n z [w55,w87,w105,w222,w238] z) [w55,w87,w105,w222,w339] (n z [w55,w87,w105,w238,w305] z)) [w55,w87,w121,w205,w234] (n (n z [w55,w87,w121,w222,w238] z) [w55,w87,w149,w222,w238] (n z [w55,w87,w222,w238,w329] z))) [w55,w87,w222,w238,w336] (n (n (n z [w55,w89,w105,w222,w238] z) [w55,w91,w105,w220,w238] (n z [w55,w91,w105,w220,w250] z)) [w55,w91,w105,w222,w241] (n (n z [w55,w91,w105,w222,w245] z) [w55,w91,w113,w222,w238] z))) [w55,w91,w119,w205,w238] (n (n (n (n z [w55,w91,w121,w134,w204] z) [w55,w91,w121,w204,w250] (n z [w55,w91,w121,w205,w234] z)) [w55,w91,w121,w205,w236] (n (n z [w55,w91,w121,w205,w250] z) [w55,w91,w121,w211,w238] z)) [w55,w91,w121,w222,w234] (n (n (n z [w55,w91,w121,w222,w238] z) [w55,w91,w121,w234,w329] (n z [w55,w91,w121,w234,w336] z)) [w55,w91,w205,w234,w322] (n (n z [w55,w93,w105,w205,w238] z) [w55,w93,w121,w205,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4babaa : t4babaa.all (blocked 3 t3) = true := by
  decide +kernel
def t4babab := (n (n (n (n (n z [w55,w93,w149,w177,w205] z) [w55,w93,w150,w177,w205] (n z [w55,w93,w154,w177,w205] z)) [w55,w93,w155,w177,w205] (n (n z [w55,w95,w120,w205,w238] z) [w55,w95,w121,w205,w238] z)) [w55,w97,w121,w205,w238] (n (n (n z [w55,w97,w154,w177,w205] z) [w55,w98,w121,w205,w238] (n z [w55,w103,w114,w222,w238] z)) [w55,w103,w147,w195,w222] (n (n z [w55,w103,w195,w222,w238] z) [w55,w103,w222,w238,w248] z))) [w55,w105,w114,w222,w238] (n (n (n (n z [w55,w105,w128,w222,w248] z) [w55,w105,w131,w184,w222] (n z [w55,w105,w131,w189,w222] z)) [w55,w105,w131,w192,w222] (n (n z [w55,w105,w131,w195,w222] z) [w55,w105,w131,w195,w305] z)) [w55,w105,w131,w222,w248] (n (n (n z [w55,w105,w131,w222,w271] z) [w55,w105,w131,w222,w288] (n z [w55,w105,w131,w222,w345] z)) [w55,w105,w133,w195,w222] (n (n z [w55,w105,w134,w195,w220] z) [w55,w105,w134,w197,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4babab : t4babab.all (blocked 3 t3) = true := by
  decide +kernel
def t4baba := (n t4babaa [w55,w93,w134,w205,w313] t4babab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4baba : t4baba.all (blocked 3 t3) = true := by
  simp only [t4baba, ReplayTree.all, n, ht4babaa, ht4babab, Bool.true_and, Bool.and_true]
  decide +kernel
def t4babba := (n (n (n (n (n z [w55,w105,w134,w199,w222] z) [w55,w105,w134,w200,w221] (n z [w55,w105,w134,w200,w222] z)) [w55,w105,w134,w202,w222] (n (n z [w55,w105,w134,w214,w220] z) [w55,w105,w134,w220,w271] (n z [w55,w105,w134,w221,w248] z))) [w55,w105,w134,w222,w241] (n (n (n z [w55,w105,w134,w222,w244] z) [w55,w105,w134,w222,w245] (n z [w55,w105,w134,w222,w248] z)) [w55,w105,w134,w222,w276] (n (n z [w55,w105,w137,w177,w222] z) [w55,w105,w139,w222,w245] z))) [w55,w105,w142,w222,w238] (n (n (n (n z [w55,w105,w142,w222,w339] z) [w55,w105,w147,w195,w222] (n z [w55,w105,w158,w222,w241] z)) [w55,w105,w158,w222,w245] (n (n z [w55,w105,w165,w222,w238] z) [w55,w105,w197,w238,w296] z)) [w55,w105,w222,w241,w284] (n (n (n z [w55,w105,w222,w241,w296] z) [w55,w105,w222,w241,w342] (n z [w55,w105,w222,w244,w338] z)) [w55,w105,w222,w245,w296] (n (n z [w55,w105,w222,w248,w349] z) [w55,w110,w134,w195,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4babba : t4babba.all (blocked 3 t3) = true := by
  decide +kernel
def t4babbb := (n (n (n (n (n z [w55,w114,w147,w177,w222] z) [w55,w118,w134,w177,w205] (n z [w55,w119,w134,w195,w205] z)) [w55,w119,w147,w195,w205] (n (n z [w55,w119,w166,w205,w238] z) [w55,w120,w134,w177,w221] z)) [w55,w120,w139,w177,w205] (n (n (n z [w55,w120,w144,w205,w238] z) [w55,w121,w131,w189,w205] (n z [w55,w121,w131,w195,w222] z)) [w55,w121,w134,w144,w204] (n (n z [w55,w121,w134,w184,w205] z) [w55,w121,w134,w184,w222] z))) [w55,w121,w134,w189,w205] (n (n (n (n z [w55,w121,w134,w189,w222] z) [w55,w121,w134,w189,w251] (n z [w55,w121,w134,w189,w329] z)) [w55,w121,w134,w189,w336] (n (n z [w55,w121,w134,w191,w205] z) [w55,w121,w134,w192,w213] z)) [w55,w121,w134,w192,w222] (n (n (n z [w55,w121,w134,w195,w213] z) [w55,w121,w134,w195,w222] (n z [w55,w121,w134,w204,w214] z)) [w55,w121,w134,w205,w214] (n (n z [w55,w121,w134,w205,w244] z) [w55,w121,w134,w205,w268] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4babbb : t4babbb.all (blocked 3 t3) = true := by
  decide +kernel
def t4babb := (n t4babba [w55,w114,w119,w205,w238] t4babbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4babb : t4babb.all (blocked 3 t3) = true := by
  simp only [t4babb, ReplayTree.all, n, ht4babba, ht4babbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t4bab := (n t4baba [w55,w105,w134,w197,w222] t4babb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4bab : t4bab.all (blocked 3 t3) = true := by
  simp only [t4bab, ReplayTree.all, n, ht4baba, ht4babb, Bool.true_and, Bool.and_true]
  decide +kernel
def t4ba := (n t4baa [w55,w87,w105,w222,w234] t4bab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4ba : t4ba.all (blocked 3 t3) = true := by
  simp only [t4ba, ReplayTree.all, n, ht4baa, ht4bab, Bool.true_and, Bool.and_true]
  decide +kernel
def t4bbaaa := (n (n (n (n (n z [w55,w121,w134,w222,w271] z) [w55,w121,w137,w173,w205] (n z [w55,w121,w137,w177,w205] z)) [w55,w121,w137,w177,w222] (n (n z [w55,w121,w137,w177,w296] z) [w55,w121,w137,w177,w301] (n z [w55,w121,w137,w195,w205] z))) [w55,w121,w137,w205,w238] (n (n (n z [w55,w121,w137,w205,w263] z) [w55,w121,w137,w205,w287] (n z [w55,w121,w137,w205,w313] z)) [w55,w121,w137,w205,w344] (n (n z [w55,w121,w138,w177,w205] z) [w55,w121,w139,w173,w205] z))) [w55,w121,w139,w177,w205] (n (n (n (n z [w55,w121,w139,w177,w213] z) [w55,w121,w139,w177,w222] (n z [w55,w121,w139,w177,w296] z)) [w55,w121,w139,w177,w302] (n (n z [w55,w121,w139,w192,w205] z) [w55,w121,w139,w195,w205] z)) [w55,w121,w139,w205,w238] (n (n (n z [w55,w121,w139,w205,w245] z) [w55,w121,w139,w205,w263] (n z [w55,w121,w139,w205,w313] z)) [w55,w121,w141,w177,w205] (n (n z [w55,w121,w142,w205,w238] z) [w55,w121,w142,w205,w339] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4bbaaa : t4bbaaa.all (blocked 3 t3) = true := by
  decide +kernel
def t4bbaab := (n (n (n (n (n z [w55,w121,w144,w173,w251] z) [w55,w121,w144,w173,w349] (n z [w55,w121,w144,w177,w249] z)) [w55,w121,w144,w205,w232] (n (n z [w55,w121,w144,w205,w234] z) [w55,w121,w144,w205,w238] z)) [w55,w121,w144,w205,w352] (n (n (n z [w55,w121,w144,w222,w238] z) [w55,w121,w152,w177,w205] (n z [w55,w121,w153,w177,w205] z)) [w55,w121,w166,w205,w234] (n (n z [w55,w121,w166,w222,w238] z) [w55,w121,w172,w205,w238] z))) [w55,w121,w189,w205,w338] (n (n (n (n z [w55,w121,w205,w234,w286] z) [w55,w121,w205,w234,w343] (n z [w55,w121,w205,w244,w338] z)) [w55,w131,w195,w222,w329] (n (n z [w55,w131,w195,w222,w336] z) [w55,w134,w189,w205,w322] z)) [w55,w137,w177,w205,w336] (n (n (n z [w55,w144,w151,w177,w205] z) [w58,w91,w121,w205,w238] (n z [w58,w105,w134,w195,w222] z)) [w59,w73,w105,w195,w254] (n (n z [w59,w73,w146,w195,w222] z) [w59,w91,w121,w177,w249] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4bbaab : t4bbaab.all (blocked 3 t3) = true := by
  decide +kernel
def t4bbaa := (n t4bbaaa [w55,w121,w143,w177,w205] t4bbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4bbaa : t4bbaa.all (blocked 3 t3) = true := by
  simp only [t4bbaa, ReplayTree.all, n, ht4bbaaa, ht4bbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t4bbaba := (n (n (n (n (n z [w60,w69,w105,w222,w238] z) [w60,w73,w105,w222,w234] (n z [w60,w73,w105,w222,w238] z)) [w60,w73,w105,w222,w245] (n (n z [w60,w73,w113,w222,w238] z) [w60,w73,w121,w205,w234] (n z [w60,w73,w121,w222,w238] z))) [w60,w73,w222,w238,w313] (n (n (n z [w60,w84,w105,w222,w238] z) [w60,w91,w105,w222,w238] (n z [w60,w105,w131,w177,w222] z)) [w60,w105,w134,w222,w238] (n (n z [w60,w105,w158,w222,w238] z) [w60,w105,w163,w222,w238] z))) [w60,w105,w222,w238,w296] (n (n (n (n z [w60,w121,w131,w177,w205] z) [w60,w121,w134,w173,w205] (n z [w60,w121,w134,w177,w205] z)) [w60,w121,w134,w177,w213] (n (n z [w60,w121,w134,w177,w222] z) [w60,w121,w134,w177,w296] z)) [w60,w121,w134,w192,w205] (n (n (n z [w60,w121,w134,w195,w205] z) [w60,w121,w134,w205,w238] (n z [w60,w121,w134,w205,w263] z)) [w60,w121,w134,w205,w270] (n (n z [w60,w121,w134,w205,w313] z) [w60,w121,w139,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4bbaba : t4bbaba.all (blocked 3 t3) = true := by
  decide +kernel
def t4bbabb := (n (n (n (n (n z [w62,w121,w134,w177,w205] z) [w63,w69,w105,w222,w234] (n z [w63,w69,w121,w205,w234] z)) [w63,w69,w149,w222,w238] (n (n z [w63,w73,w105,w182,w256] z) [w63,w73,w105,w220,w250] z)) [w63,w73,w105,w222,w233] (n (n (n z [w63,w73,w105,w222,w234] z) [w63,w73,w105,w222,w235] (n z [w63,w73,w105,w222,w241] z)) [w63,w73,w105,w222,w250] (n (n z [w63,w73,w105,w222,w255] z) [w63,w73,w105,w234,w336] z))) [w63,w73,w105,w238,w254] (n (n (n (n z [w63,w73,w121,w204,w250] z) [w63,w73,w121,w205,w234] (n z [w63,w73,w121,w205,w250] z)) [w63,w73,w121,w222,w234] (n (n z [w63,w73,w121,w234,w329] z) [w63,w73,w121,w234,w336] z)) [w63,w73,w146,w222,w238] (n (n (n z [w63,w73,w205,w234,w322] z) [w63,w73,w222,w234,w309] (n z [w63,w78,w154,w177,w205] z)) [w63,w91,w105,w222,w234] (n (n z [w63,w91,w121,w205,w234] z) [w63,w103,w147,w177,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4bbabb : t4bbabb.all (blocked 3 t3) = true := by
  decide +kernel
def t4bbab := (n t4bbaba [w61,w73,w105,w222,w238] t4bbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4bbab : t4bbab.all (blocked 3 t3) = true := by
  simp only [t4bbab, ReplayTree.all, n, ht4bbaba, ht4bbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t4bba := (n t4bbaa [w59,w91,w151,w177,w205] t4bbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4bba : t4bba.all (blocked 3 t3) = true := by
  simp only [t4bba, ReplayTree.all, n, ht4bbaa, ht4bbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t4bbbaa := (n (n (n (n (n z [w63,w105,w128,w222,w238] z) [w63,w105,w131,w173,w222] (n z [w63,w105,w131,w177,w222] z)) [w63,w105,w131,w177,w305] (n (n z [w63,w105,w131,w195,w222] z) [w63,w105,w131,w222,w238] (n z [w63,w105,w131,w222,w263] z))) [w63,w105,w131,w222,w271] (n (n (n z [w63,w105,w131,w222,w279] z) [w63,w105,w131,w222,w339] (n z [w63,w105,w134,w220,w263] z)) [w63,w105,w134,w222,w234] (n (n z [w63,w105,w134,w222,w238] z) [w63,w105,w134,w222,w265] z))) [w63,w105,w147,w177,w222] (n (n (n (n z [w63,w105,w156,w222,w238] z) [w63,w105,w158,w222,w234] (n z [w63,w105,w158,w222,w238] z)) [w63,w105,w161,w222,w238] (n (n z [w63,w105,w166,w222,w234] z) [w63,w105,w222,w234,w278] z)) [w63,w105,w222,w234,w296] (n (n (n z [w63,w105,w222,w234,w338] z) [w63,w105,w222,w238,w349] (n z [w63,w105,w222,w238,w355] z)) [w63,w119,w147,w177,w205] (n (n z [w63,w119,w158,w205,w238] z) [w63,w121,w129,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4bbbaa : t4bbbaa.all (blocked 3 t3) = true := by
  decide +kernel
def t4bbbab := (n (n (n (n (n z [w63,w121,w131,w177,w205] z) [w63,w121,w131,w177,w222] (n z [w63,w121,w131,w177,w292] z)) [w63,w121,w131,w195,w205] (n (n z [w63,w121,w131,w205,w238] z) [w63,w121,w131,w205,w263] z)) [w63,w121,w131,w205,w271] (n (n (n z [w63,w121,w131,w205,w279] z) [w63,w121,w131,w205,w313] (n z [w63,w121,w131,w205,w339] z)) [w63,w121,w132,w177,w205] (n (n z [w63,w121,w134,w173,w251] z) [w63,w121,w134,w177,w249] z))) [w63,w121,w134,w204,w263] (n (n (n (n z [w63,w121,w134,w205,w232] z) [w63,w121,w134,w205,w234] (n z [w63,w121,w134,w205,w238] z)) [w63,w121,w134,w205,w260] (n (n z [w63,w121,w134,w205,w263] z) [w63,w121,w134,w205,w265] z)) [w63,w121,w134,w205,w352] (n (n (n z [w63,w121,w134,w205,w357] z) [w63,w121,w134,w222,w238] (n z [w63,w121,w134,w222,w263] z)) [w63,w121,w134,w263,w296] (n (n z [w63,w121,w137,w177,w205] z) [w63,w121,w147,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4bbbab : t4bbbab.all (blocked 3 t3) = true := by
  decide +kernel
def t4bbba := (n t4bbbaa [w63,w121,w131,w173,w205] t4bbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4bbba : t4bbba.all (blocked 3 t3) = true := by
  simp only [t4bbba, ReplayTree.all, n, ht4bbbaa, ht4bbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t4bbbba := (n (n (n (n (n z [w63,w121,w158,w205,w234] z) [w63,w121,w158,w222,w238] (n z [w63,w121,w161,w205,w238] z)) [w63,w121,w166,w205,w234] (n (n z [w63,w121,w205,w234,w278] z) [w63,w121,w205,w234,w338] z)) [w63,w131,w177,w205,w336] (n (n (n z [w63,w131,w177,w222,w329] z) [w63,w131,w177,w222,w336] (n z [w63,w134,w151,w177,w205] z)) [w63,w158,w222,w238,w313] (n (n z [w64,w73,w105,w205,w245] z) [w64,w73,w105,w221,w238] z))) [w64,w73,w105,w222,w238] (n (n (n (n z [w64,w73,w120,w205,w238] z) [w64,w73,w121,w205,w238] (n z [w64,w95,w105,w205,w238] z)) [w64,w105,w134,w177,w221] (n (n z [w64,w105,w134,w177,w222] z) [w64,w105,w134,w200,w205] z)) [w64,w105,w139,w177,w205] (n (n (n z [w64,w120,w134,w177,w205] z) [w64,w121,w134,w177,w205] (n z [w65,w105,w134,w222,w271] z)) [w65,w105,w139,w205,w263] (n (n z [w65,w105,w158,w205,w245] z) [w65,w105,w166,w222,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4bbbba : t4bbbba.all (blocked 3 t3) = true := by
  decide +kernel
def t4bbbbb := (n (n (n (n (n z [w65,w121,w166,w205,w238] z) [w68,w73,w105,w177,w254] (n z [w68,w73,w121,w177,w249] z)) [w68,w73,w146,w177,w222] (n (n z [w68,w73,w151,w177,w205] z) [w73,w105,w222,w234,w268] z)) [w73,w105,w222,w238,w266] (n (n (n z [w73,w105,w222,w238,w272] z) [w73,w105,w222,w241,w266] (n z [w73,w121,w205,w234,w268] z)) [w87,w105,w156,w222,w238] (n (n z [w91,w121,w134,w205,w260] z) [w91,w121,w205,w234,w260] z))) [w105,w131,w156,w195,w222] (n (n (n (n z [w105,w131,w165,w177,w222] z) [w105,w156,w165,w222,w238] (n z [w105,w156,w195,w222,w238] z)) [w105,w156,w222,w238,w248] (n (n z [w105,w158,w222,w238,w271] z) [w121,w131,w165,w177,w205] z)) [w121,w134,w144,w205,w260] (n (n (n z [w121,w134,w162,w177,w205] z) [w121,w134,w166,w205,w263] (n z [w121,w134,w168,w177,w205] z)) [w121,w134,w189,w205,w260] (n (n z [w121,w134,w205,w260,w268] z) [w121,w137,w162,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4bbbbb : t4bbbbb.all (blocked 3 t3) = true := by
  decide +kernel
def t4bbbb := (n t4bbbba [w65,w121,w134,w205,w271] t4bbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4bbbb : t4bbbb.all (blocked 3 t3) = true := by
  simp only [t4bbbb, ReplayTree.all, n, ht4bbbba, ht4bbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t4bbb := (n t4bbba [w63,w121,w152,w177,w205] t4bbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4bbb : t4bbb.all (blocked 3 t3) = true := by
  simp only [t4bbb, ReplayTree.all, n, ht4bbba, ht4bbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t4bb := (n t4bba [w63,w103,w158,w222,w238] t4bbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4bb : t4bb.all (blocked 3 t3) = true := by
  simp only [t4bb, ReplayTree.all, n, ht4bba, ht4bbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t4b := (n t4ba [w55,w121,w134,w222,w248] t4bb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4b : t4b.all (blocked 3 t3) = true := by
  simp only [t4b, ReplayTree.all, n, ht4ba, ht4bb, Bool.true_and, Bool.and_true]
  decide +kernel
def t4 := (n t4a [w38,w121,w165,w177,w222] t4b)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht4 : t4.all (blocked 3 t3) = true := by
  simp only [t4, ReplayTree.all, n, ht4a, ht4b, Bool.true_and, Bool.and_true]
  decide +kernel
lemma s4 : sound 4 t4 := layer_sound s3 ht4
def t5aaaaaaa := (n (n (n (n (n z [w12,w13,w38,w55,w296,w313] z) [w12,w17,w47,w55,w296,w313] z) [w12,w55,w91,w121,w205,w238] (n (n z [w12,w55,w105,w134,w195,w222] z) [w13,w23,w38,w55,w292,w313] z)) [w13,w23,w38,w55,w296,w309] (n (n (n z [w13,w23,w38,w55,w296,w313] z) [w13,w23,w38,w55,w296,w319] z) [w13,w23,w38,w55,w302,w313] (n z [w13,w23,w38,w60,w296,w313] z))) [w13,w23,w38,w105,w260,w296] (n (n (n (n z [w13,w23,w38,w156,w205,w313] z) [w13,w23,w46,w55,w296,w313] z) [w13,w23,w55,w103,w205,w238] (n (n z [w13,w23,w55,w105,w134,w204] z) [w13,w23,w55,w105,w238,w292] z)) [w13,w23,w55,w134,w205,w309] (n (n (n z [w13,w23,w55,w134,w296,w313] z) [w13,w23,w55,w238,w296,w313] z) [w13,w23,w105,w134,w205,w260] (n z [w13,w23,w105,w156,w205,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaaaaaa : t5aaaaaaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5aaaaaab := (n (n (n (n (n z [w13,w37,w55,w73,w205,w313] z) [w13,w37,w55,w105,w177,w296] z) [w13,w38,w55,w65,w296,w313] (n (n z [w13,w38,w55,w73,w121,w204] z) [w13,w38,w55,w73,w211,w313] z)) [w13,w38,w55,w103,w177,w222] (n (n (n z [w13,w38,w55,w110,w177,w296] z) [w13,w38,w55,w121,w296,w313] z) [w13,w38,w55,w222,w296,w313] (n z [w13,w38,w58,w73,w205,w313] z))) [w13,w38,w58,w105,w177,w296] (n (n (n (n z [w13,w38,w65,w105,w263,w296] z) [w13,w38,w65,w158,w205,w313] z) [w13,w38,w73,w105,w222,w260] (n (n z [w13,w38,w73,w121,w205,w260] z) [w13,w38,w105,w156,w177,w222] z)) [w13,w38,w105,w158,w222,w263] (n (n (n z [w13,w38,w121,w156,w177,w205] z) [w13,w38,w121,w158,w205,w263] z) [w13,w55,w69,w105,w222,w238] (n z [w13,w55,w73,w105,w211,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaaaaab : t5aaaaaab.all (blocked 4 t4) = true := by
  decide +kernel
def t5aaaaaa := (n t5aaaaaaa [w13,w27,w38,w55,w296,w313] t5aaaaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaaaaa : t5aaaaaa.all (blocked 4 t4) = true := by
  simp only [t5aaaaaa, ReplayTree.all, n, ht5aaaaaaa, ht5aaaaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aaaaaba := (n (n (n (n (n z [w13,w55,w73,w105,w222,w238] z) [w13,w55,w73,w105,w222,w245] z) [w13,w55,w73,w113,w222,w238] (n (n z [w13,w55,w73,w121,w205,w234] z) [w13,w55,w73,w121,w222,w238] z)) [w13,w55,w73,w222,w238,w313] (n (n (n z [w13,w55,w84,w105,w222,w238] z) [w13,w55,w91,w105,w222,w238] z) [w13,w55,w105,w131,w177,w222] (n z [w13,w55,w105,w134,w222,w238] z))) [w13,w55,w105,w158,w222,w238] (n (n (n (n z [w13,w55,w105,w222,w238,w296] z) [w13,w55,w110,w134,w177,w205] z) [w13,w55,w121,w131,w177,w205] (n (n z [w13,w55,w121,w134,w173,w205] z) [w13,w55,w121,w134,w177,w205] z)) [w13,w55,w121,w134,w177,w213] (n (n (n z [w13,w55,w121,w134,w177,w222] z) [w13,w55,w121,w134,w177,w296] z) [w13,w55,w121,w134,w192,w205] (n z [w13,w55,w121,w134,w195,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaaaaba : t5aaaaaba.all (blocked 4 t4) = true := by
  decide +kernel
def t5aaaaabb := (n (n (n (n (n z [w13,w55,w121,w134,w205,w263] z) [w13,w55,w121,w134,w205,w313] z) [w13,w55,w121,w139,w177,w205] (n (n z [w13,w58,w73,w105,w205,w238] z) [w13,w58,w105,w134,w177,w205] z)) [w13,w60,w73,w105,w222,w238] (n (n (n z [w13,w60,w121,w134,w177,w205] z) [w13,w65,w105,w134,w205,w263] z) [w13,w65,w105,w158,w205,w238] (n z [w14,w23,w38,w55,w296,w313] z))) [w14,w55,w73,w105,w222,w238] (n (n (n (n z [w14,w55,w121,w134,w177,w205] z) [w15,w23,w38,w55,w296,w313] z) [w15,w55,w73,w105,w222,w238] (n z [w15,w55,w121,w134,w177,w205] z)) [w16,w23,w38,w55,w296,w313] (n (n (n z [w16,w55,w73,w105,w222,w238] z) [w16,w55,w121,w134,w177,w205] z) [w17,w22,w38,w55,w296,w313] (n z [w17,w23,w37,w55,w296,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaaaabb : t5aaaaabb.all (blocked 4 t4) = true := by
  decide +kernel
def t5aaaaab := (n t5aaaaaba [w13,w55,w121,w134,w205,w238] t5aaaaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaaaab : t5aaaaab.all (blocked 4 t4) = true := by
  simp only [t5aaaaab, ReplayTree.all, n, ht5aaaaaba, ht5aaaaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aaaaa := (n t5aaaaaa [w13,w55,w73,w105,w222,w234] t5aaaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaaaa : t5aaaaa.all (blocked 4 t4) = true := by
  simp only [t5aaaaa, ReplayTree.all, n, ht5aaaaaa, ht5aaaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aaaabaa := (n (n (n (n (n z [w17,w23,w38,w55,w105,w291] z) [w17,w23,w38,w55,w205,w308] z) [w17,w23,w38,w55,w277,w329] (n (n z [w17,w23,w38,w55,w277,w330] z) [w17,w23,w38,w55,w277,w332] z)) [w17,w23,w38,w55,w277,w333] (n (n (n z [w17,w23,w38,w55,w291,w313] z) [w17,w23,w38,w55,w292,w309] z) [w17,w23,w38,w55,w292,w313] (n z [w17,w23,w38,w55,w292,w352] z))) [w17,w23,w38,w55,w293,w313] (n (n (n (n z [w17,w23,w38,w55,w294,w313] z) [w17,w23,w38,w55,w295,w313] z) [w17,w23,w38,w55,w295,w328] (n (n z [w17,w23,w38,w55,w296,w308] z) [w17,w23,w38,w55,w296,w309] z)) [w17,w23,w38,w55,w296,w310] (n (n (n z [w17,w23,w38,w55,w296,w311] z) [w17,w23,w38,w55,w296,w312] z) [w17,w23,w38,w55,w296,w313] (n z [w17,w23,w38,w55,w296,w316] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaaabaa : t5aaaabaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5aaaabab := (n (n (n (n (n z [w17,w23,w38,w55,w296,w328] z) [w17,w23,w38,w55,w296,w331] z) [w17,w23,w38,w55,w296,w350] (n (n z [w17,w23,w38,w55,w299,w313] z) [w17,w23,w38,w55,w302,w313] z)) [w17,w23,w38,w55,w309,w349] (n (n (n z [w17,w23,w38,w55,w312,w326] z) [w17,w23,w38,w55,w313,w326] z) [w17,w23,w38,w55,w313,w327] (n z [w17,w23,w38,w55,w313,w347] z))) [w17,w23,w38,w58,w296,w313] (n (n (n (n z [w17,w23,w38,w60,w296,w313] z) [w17,w23,w38,w69,w260,w329] z) [w17,w23,w38,w73,w260,w328] (n z [w17,w23,w38,w73,w261,w328] z)) [w17,w23,w38,w73,w261,w331] (n (n (n z [w17,w23,w38,w103,w205,w260] z) [w17,w23,w38,w105,w156,w204] z) [w17,w23,w38,w105,w205,w353] (n z [w17,w23,w38,w105,w260,w292] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaaabab : t5aaaabab.all (blocked 4 t4) = true := by
  decide +kernel
def t5aaaaba := (n t5aaaabaa [w17,w23,w38,w55,w296,w319] t5aaaabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaaaba : t5aaaaba.all (blocked 4 t4) = true := by
  simp only [t5aaaaba, ReplayTree.all, n, ht5aaaabaa, ht5aaaabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aaaabba := (n (n (n (n (n z [w17,w23,w38,w105,w260,w296] z) [w17,w23,w38,w105,w260,w349] z) [w17,w23,w38,w105,w262,w296] (n (n z [w17,w23,w38,w105,w296,w353] z) [w17,w23,w38,w156,w173,w329] z)) [w17,w23,w38,w156,w177,w326] (n (n (n z [w17,w23,w38,w156,w205,w309] z) [w17,w23,w38,w156,w205,w312] z) [w17,w23,w38,w156,w205,w313] (n z [w17,w23,w38,w156,w205,w352] z))) [w17,w23,w38,w156,w292,w313] (n (n (n (n z [w17,w23,w38,w156,w296,w313] z) [w17,w23,w38,w157,w205,w313] z) [w17,w23,w38,w159,w177,w326] (n (n z [w17,w23,w38,w159,w177,w327] z) [w17,w23,w38,w205,w313,w353] z)) [w17,w23,w38,w260,w296,w309] (n (n (n z [w17,w23,w38,w260,w296,w313] z) [w17,w23,w38,w296,w313,w353] z) [w17,w23,w39,w55,w296,w313] (n z [w17,w23,w40,w55,w296,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaaabba : t5aaaabba.all (blocked 4 t4) = true := by
  decide +kernel
def t5aaaabbb := (n (n (n (n (n z [w17,w23,w42,w55,w296,w313] z) [w17,w23,w46,w55,w296,w313] z) [w17,w23,w51,w55,w296,w313] (n (n z [w17,w23,w51,w73,w261,w313] z) [w17,w23,w53,w55,w296,w313] z)) [w17,w23,w53,w159,w177,w296] (n (n (n z [w17,w23,w55,w69,w205,w259] z) [w17,w23,w55,w69,w229,w238] z) [w17,w23,w55,w69,w234,w329] (n z [w17,w23,w55,w73,w250,w328] z))) [w17,w23,w55,w103,w205,w234] (n (n (n (n z [w17,w23,w55,w103,w205,w238] z) [w17,w23,w55,w103,w205,w351] z) [w17,w23,w55,w103,w222,w238] (n z [w17,w23,w55,w103,w238,w326] z)) [w17,w23,w55,w105,w131,w204] (n (n (n z [w17,w23,w55,w105,w134,w204] z) [w17,w23,w55,w105,w145,w173] z) [w17,w23,w55,w105,w204,w348] (n z [w17,w23,w55,w105,w205,w337] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaaabbb : t5aaaabbb.all (blocked 4 t4) = true := by
  decide +kernel
def t5aaaabb := (n t5aaaabba [w17,w23,w41,w55,w296,w313] t5aaaabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaaabb : t5aaaabb.all (blocked 4 t4) = true := by
  simp only [t5aaaabb, ReplayTree.all, n, ht5aaaabba, ht5aaaabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aaaab := (n t5aaaaba [w17,w23,w38,w105,w260,w295] t5aaaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaaab : t5aaaab.all (blocked 4 t4) = true := by
  simp only [t5aaaab, ReplayTree.all, n, ht5aaaaba, ht5aaaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aaaa := (n t5aaaaa [w17,w23,w38,w55,w103,w204] t5aaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaaa : t5aaaa.all (blocked 4 t4) = true := by
  simp only [t5aaaa, ReplayTree.all, n, ht5aaaaa, ht5aaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aaabaaa := (n (n (n (n (n z [w17,w23,w55,w105,w237,w296] z) [w17,w23,w55,w105,w238,w292] z) [w17,w23,w55,w105,w238,w294] (n (n z [w17,w23,w55,w105,w238,w326] z) [w17,w23,w55,w105,w292,w339] z)) [w17,w23,w55,w121,w134,w204] (n (n (n z [w17,w23,w55,w125,w134,w173] z) [w17,w23,w55,w130,w205,w313] z) [w17,w23,w55,w131,w173,w329] (n z [w17,w23,w55,w131,w205,w309] z))) [w17,w23,w55,w131,w292,w313] (n (n (n (n z [w17,w23,w55,w131,w296,w313] z) [w17,w23,w55,w134,w204,w328] z) [w17,w23,w55,w134,w205,w309] (n (n z [w17,w23,w55,w134,w205,w311] z) [w17,w23,w55,w134,w205,w328] z)) [w17,w23,w55,w134,w251,w309] (n (n (n z [w17,w23,w55,w134,w292,w313] z) [w17,w23,w55,w134,w296,w309] z) [w17,w23,w55,w134,w296,w313] (n z [w17,w23,w55,w134,w309,w349] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaabaaa : t5aaabaaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5aaabaab := (n (n (n (n (n z [w17,w23,w55,w149,w238,w292] z) [w17,w23,w55,w205,w309,w338] z) [w17,w23,w55,w234,w296,w309] (n (n z [w17,w23,w55,w234,w296,w313] z) [w17,w23,w55,w238,w292,w313] z)) [w17,w23,w55,w238,w292,w352] (n (n (n z [w17,w23,w55,w238,w296,w309] z) [w17,w23,w55,w238,w296,w313] z) [w17,w23,w55,w296,w313,w337] (n z [w17,w23,w55,w296,w313,w340] z))) [w17,w23,w73,w105,w250,w260] (n (n (n (n z [w17,w23,w73,w105,w250,w261] z) [w17,w23,w73,w105,w252,w261] z) [w17,w23,w73,w125,w238,w261] (n z [w17,w23,w103,w156,w205,w238] z)) [w17,w23,w105,w131,w205,w260] (n (n (n z [w17,w23,w105,w134,w204,w260] z) [w17,w23,w105,w134,w205,w260] z) [w17,w23,w105,w134,w205,w262] (n z [w17,w23,w105,w134,w210,w260] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaabaab : t5aaabaab.all (blocked 4 t4) = true := by
  decide +kernel
def t5aaabaa := (n t5aaabaaa [w17,w23,w55,w147,w177,w326] t5aaabaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaabaa : t5aaabaa.all (blocked 4 t4) = true := by
  simp only [t5aaabaa, ReplayTree.all, n, ht5aaabaaa, ht5aaabaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aaababa := (n (n (n (n (n z [w17,w23,w105,w134,w251,w260] z) [w17,w23,w105,w134,w260,w296] z) [w17,w23,w105,w134,w260,w329] (n (n z [w17,w23,w105,w134,w260,w349] z) [w17,w23,w105,w156,w205,w234] z)) [w17,w23,w105,w156,w205,w238] (n (n (n z [w17,w23,w105,w156,w205,w339] z) [w17,w23,w105,w156,w222,w238] z) [w17,w23,w105,w156,w238,w292] (n z [w17,w23,w105,w157,w205,w238] z))) [w17,w23,w105,w205,w260,w338] (n (n (n (n z [w17,w23,w105,w234,w260,w296] z) [w17,w23,w105,w238,w260,w296] z) [w17,w23,w107,w156,w205,w238] (n (n z [w17,w23,w121,w134,w205,w260] z) [w17,w23,w121,w156,w205,w238] z)) [w17,w23,w131,w156,w205,w313] (n (n (n z [w17,w23,w134,w156,w205,w313] z) [w17,w23,w134,w159,w177,w229] z) [w17,w23,w134,w205,w260,w309] (n z [w17,w23,w147,w156,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaababa : t5aaababa.all (blocked 4 t4) = true := by
  decide +kernel
def t5aaababb := (n (n (n (n (n z [w17,w23,w148,w159,w177,w205] z) [w17,w23,w149,w156,w205,w238] z) [w17,w23,w156,w205,w238,w313] (n (n z [w17,w23,w156,w205,w238,w329] z) [w17,w23,w156,w205,w238,w352] z)) [w17,w24,w38,w55,w296,w313] (n (n (n z [w17,w25,w38,w55,w296,w313] z) [w17,w28,w55,w121,w134,w173] z) [w17,w31,w38,w55,w296,w313] (n z [w17,w31,w55,w105,w134,w173] z))) [w17,w32,w55,w69,w222,w238] (n (n (n (n z [w17,w35,w38,w55,w296,w313] z) [w17,w35,w55,w69,w205,w238] z) [w17,w38,w45,w55,w296,w313] (n z [w17,w38,w55,w69,w121,w204] z)) [w17,w38,w55,w69,w173,w336] (n (n (n z [w17,w38,w55,w69,w177,w231] z) [w17,w38,w55,w69,w222,w226] z) [w17,w38,w55,w73,w121,w204] (n z [w17,w38,w55,w73,w127,w173] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaababb : t5aaababb.all (blocked 4 t4) = true := by
  decide +kernel
def t5aaabab := (n t5aaababa [w17,w23,w147,w159,w177,w205] t5aaababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaabab : t5aaabab.all (blocked 4 t4) = true := by
  simp only [t5aaabab, ReplayTree.all, n, ht5aaababa, ht5aaababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aaaba := (n t5aaabaa [w17,w23,w105,w134,w222,w260] t5aaabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaaba : t5aaaba.all (blocked 4 t4) = true := by
  simp only [t5aaaba, ReplayTree.all, n, ht5aaabaa, ht5aaabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aaabbaa := (n (n (n (n (n z [w17,w38,w55,w73,w221,w313] z) [w17,w38,w55,w73,w222,w312] z) [w17,w38,w55,w91,w121,w204] (n (n z [w17,w38,w55,w94,w292,w313] z) [w17,w38,w55,w94,w296,w313] z)) [w17,w38,w55,w100,w121,w173] (n (n (n z [w17,w38,w55,w103,w173,w222] z) [w17,w38,w55,w103,w177,w222] z) [w17,w38,w55,w103,w177,w334] (n z [w17,w38,w55,w103,w195,w222] z))) [w17,w38,w55,w103,w222,w238] (n (n (n (n z [w17,w38,w55,w103,w222,w263] z) [w17,w38,w55,w103,w222,w312] z) [w17,w38,w55,w105,w220,w295] (n (n z [w17,w38,w55,w105,w222,w277] z) [w17,w38,w55,w105,w279,w305] z)) [w17,w38,w55,w119,w205,w312] (n (n (n z [w17,w38,w55,w120,w177,w296] z) [w17,w38,w55,w121,w134,w204] z) [w17,w38,w55,w121,w158,w204] (n z [w17,w38,w55,w121,w177,w295] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaabbaa : t5aaabbaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5aaabbab := (n (n (n (n (n z [w17,w38,w55,w121,w205,w277] z) [w17,w38,w55,w121,w263,w295] z) [w17,w38,w55,w121,w277,w296] (n (n z [w17,w38,w55,w121,w279,w292] z) [w17,w38,w55,w121,w279,w296] z)) [w17,w38,w55,w121,w292,w313] (n (n (n z [w17,w38,w55,w121,w296,w309] z) [w17,w38,w55,w121,w296,w313] z) [w17,w38,w55,w121,w296,w357] (n z [w17,w38,w55,w158,w222,w312] z))) [w17,w38,w55,w198,w296,w309] (n (n (n (n z [w17,w38,w55,w198,w296,w313] z) [w17,w38,w55,w205,w278,w322] z) [w17,w38,w55,w222,w277,w313] (n z [w17,w38,w55,w222,w278,w309] z)) [w17,w38,w55,w222,w278,w313] (n (n (n z [w17,w38,w55,w222,w292,w313] z) [w17,w38,w55,w222,w296,w309] z) [w17,w38,w55,w222,w296,w313] (n z [w17,w38,w55,w222,w313,w355] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaabbab : t5aaabbab.all (blocked 4 t4) = true := by
  decide +kernel
def t5aaabba := (n t5aaabbaa [w17,w38,w55,w121,w204,w295] t5aaabbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaabba : t5aaabba.all (blocked 4 t4) = true := by
  simp only [t5aaabba, ReplayTree.all, n, ht5aaabbaa, ht5aaabbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aaabbba := (n (n (n (n (n z [w17,w38,w55,w292,w305,w313] z) [w17,w38,w55,w296,w309,w322] z) [w17,w38,w55,w296,w313,w336] (n (n z [w17,w38,w63,w73,w121,w204] z) [w17,w38,w63,w103,w177,w222] z)) [w17,w38,w69,w105,w222,w260] (n (n (n z [w17,w38,w69,w121,w205,w260] z) [w17,w38,w73,w105,w220,w260] z) [w17,w38,w73,w105,w222,w260] (n z [w17,w38,w73,w105,w222,w262] z))) [w17,w38,w73,w105,w222,w264] (n (n (n (n z [w17,w38,w73,w105,w222,w266] z) [w17,w38,w73,w105,w222,w268] z) [w17,w38,w73,w105,w260,w336] (n (n z [w17,w38,w73,w121,w204,w260] z) [w17,w38,w73,w121,w205,w260] z)) [w17,w38,w73,w121,w205,w262] (n (n (n z [w17,w38,w73,w121,w205,w268] z) [w17,w38,w73,w121,w210,w260] z) [w17,w38,w73,w121,w222,w260] (n z [w17,w38,w73,w121,w251,w260] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaabbba : t5aaabbba.all (blocked 4 t4) = true := by
  decide +kernel
def t5aaabbbb := (n (n (n (n (n z [w17,w38,w73,w121,w260,w329] z) [w17,w38,w73,w121,w260,w336] z) [w17,w38,w73,w205,w260,w322] (n (n z [w17,w38,w73,w222,w260,w309] z) [w17,w38,w73,w222,w260,w313] z)) [w17,w38,w91,w105,w222,w260] (n (n (n z [w17,w38,w91,w121,w205,w260] z) [w17,w38,w94,w156,w205,w313] z) [w17,w38,w103,w156,w177,w222] (n z [w17,w38,w103,w158,w222,w263] z))) [w17,w38,w105,w121,w260,w296] (n (n (n (n z [w17,w38,w105,w134,w222,w260] z) [w17,w38,w105,w156,w173,w222] z) [w17,w38,w105,w156,w177,w222] (n z [w17,w38,w105,w156,w177,w305] z)) [w17,w38,w105,w156,w195,w222] (n (n (n z [w17,w38,w105,w156,w222,w238] z) [w17,w38,w105,w156,w222,w263] z) [w17,w38,w105,w156,w222,w279] (n z [w17,w38,w105,w156,w222,w356] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaabbbb : t5aaabbbb.all (blocked 4 t4) = true := by
  decide +kernel
def t5aaabbb := (n t5aaabbba [w17,w38,w73,w121,w260,w296] t5aaabbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaabbb : t5aaabbb.all (blocked 4 t4) = true := by
  simp only [t5aaabbb, ReplayTree.all, n, ht5aaabbba, ht5aaabbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aaabb := (n t5aaabba [w17,w38,w55,w290,w296,w313] t5aaabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaabb : t5aaabb.all (blocked 4 t4) = true := by
  simp only [t5aaabb, ReplayTree.all, n, ht5aaabba, ht5aaabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aaab := (n t5aaaba [w17,w38,w55,w73,w204,w335] t5aaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaab : t5aaab.all (blocked 4 t4) = true := by
  simp only [t5aaab, ReplayTree.all, n, ht5aaaba, ht5aaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aaa := (n t5aaaa [w17,w23,w55,w105,w234,w292] t5aaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaa : t5aaa.all (blocked 4 t4) = true := by
  simp only [t5aaa, ReplayTree.all, n, ht5aaaa, ht5aaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aabaaaa := (n (n (n (n (n z [w17,w38,w105,w158,w220,w263] z) [w17,w38,w105,w158,w222,w260] z) [w17,w38,w105,w158,w222,w263] (n (n z [w17,w38,w105,w158,w222,w271] z) [w17,w38,w105,w165,w177,w222] z)) [w17,w38,w105,w166,w222,w263] (n (n (n z [w17,w38,w105,w166,w222,w271] z) [w17,w38,w105,w198,w260,w296] z) [w17,w38,w105,w222,w260,w278] (n z [w17,w38,w105,w222,w260,w296] z))) [w17,w38,w105,w222,w260,w354] (n (n (n (n z [w17,w38,w105,w222,w263,w355] z) [w17,w38,w107,w156,w177,w222] z) [w17,w38,w119,w156,w177,w205] (n (n z [w17,w38,w119,w158,w205,w263] z) [w17,w38,w121,w134,w205,w260] z)) [w17,w38,w121,w156,w173,w205] (n (n (n z [w17,w38,w121,w156,w177,w205] z) [w17,w38,w121,w156,w177,w222] z) [w17,w38,w121,w156,w177,w292] (n z [w17,w38,w121,w156,w177,w296] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aabaaaa : t5aabaaaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5aabaaab := (n (n (n (n (n z [w17,w38,w121,w156,w205,w238] z) [w17,w38,w121,w156,w205,w263] z) [w17,w38,w121,w156,w205,w279] (n (n z [w17,w38,w121,w156,w205,w313] z) [w17,w38,w121,w156,w205,w356] z)) [w17,w38,w121,w157,w177,w205] (n (n (n z [w17,w38,w121,w158,w204,w263] z) [w17,w38,w121,w158,w205,w260] z) [w17,w38,w121,w158,w205,w263] (n z [w17,w38,w121,w158,w205,w271] z))) [w17,w38,w121,w158,w205,w357] (n (n (n (n z [w17,w38,w121,w158,w222,w263] z) [w17,w38,w121,w158,w263,w296] z) [w17,w38,w121,w160,w177,w205] (n z [w17,w38,w121,w162,w177,w205] z)) [w17,w38,w121,w165,w177,w205] (n (n (n z [w17,w38,w121,w166,w205,w263] z) [w17,w38,w121,w166,w205,w271] z) [w17,w38,w121,w205,w260,w278] (n z [w17,w38,w121,w205,w260,w354] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aabaaab : t5aabaaab.all (blocked 4 t4) = true := by
  decide +kernel
def t5aabaaa := (n t5aabaaaa [w17,w38,w121,w156,w195,w205] t5aabaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aabaaa : t5aabaaa.all (blocked 4 t4) = true := by
  simp only [t5aabaaa, ReplayTree.all, n, ht5aabaaaa, ht5aabaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aabaaba := (n (n (n (n (n z [w17,w38,w156,w177,w205,w336] z) [w17,w38,w156,w177,w222,w313] z) [w17,w38,w156,w177,w222,w329] (n (n z [w17,w38,w156,w177,w222,w336] z) [w17,w38,w156,w205,w222,w313] z)) [w17,w38,w158,w222,w263,w313] (n (n (n z [w17,w47,w58,w73,w205,w313] z) [w17,w47,w58,w105,w177,w296] z) [w17,w51,w55,w73,w121,w173] (n z [w17,w53,w55,w69,w177,w222] z))) [w17,w55,w69,w105,w222,w234] (n (n (n (n z [w17,w55,w69,w105,w222,w238] z) [w17,w55,w69,w105,w222,w339] z) [w17,w55,w69,w105,w238,w305] (n (n z [w17,w55,w69,w107,w222,w238] z) [w17,w55,w69,w121,w205,w234] z)) [w17,w55,w69,w121,w222,w238] (n (n (n z [w17,w55,w69,w149,w222,w238] z) [w17,w55,w69,w222,w238,w313] z) [w17,w55,w69,w222,w238,w329] (n z [w17,w55,w69,w222,w238,w336] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aabaaba : t5aabaaba.all (blocked 4 t4) = true := by
  decide +kernel
def t5aabaabb := (n (n (n (n (n z [w17,w55,w70,w105,w222,w238] z) [w17,w55,w71,w105,w222,w238] z) [w17,w55,w72,w105,w222,w238] (n (n z [w17,w55,w73,w103,w222,w238] z) [w17,w55,w73,w105,w182,w256] z)) [w17,w55,w73,w105,w220,w238] (n (n (n z [w17,w55,w73,w105,w220,w250] z) [w17,w55,w73,w105,w221,w238] z) [w17,w55,w73,w105,w222,w233] (n z [w17,w55,w73,w105,w222,w234] z))) [w17,w55,w73,w105,w222,w235] (n (n (n (n z [w17,w55,w73,w105,w222,w236] z) [w17,w55,w73,w105,w222,w237] z) [w17,w55,w73,w105,w222,w238] (n z [w17,w55,w73,w105,w222,w239] z)) [w17,w55,w73,w105,w222,w241] (n (n (n z [w17,w55,w73,w105,w222,w245] z) [w17,w55,w73,w105,w222,w250] z) [w17,w55,w73,w105,w222,w252] (n z [w17,w55,w73,w105,w222,w259] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aabaabb : t5aabaabb.all (blocked 4 t4) = true := by
  decide +kernel
def t5aabaab := (n t5aabaaba [w17,w55,w69,w222,w238,w352] t5aabaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aabaab : t5aabaab.all (blocked 4 t4) = true := by
  simp only [t5aabaab, ReplayTree.all, n, ht5aabaaba, ht5aabaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aabaa := (n t5aabaaa [w17,w38,w149,w156,w177,w222] t5aabaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aabaa : t5aabaa.all (blocked 4 t4) = true := by
  simp only [t5aabaa, ReplayTree.all, n, ht5aabaaa, ht5aabaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aababaa := (n (n (n (n (n z [w17,w55,w73,w105,w231,w238] z) [w17,w55,w73,w105,w234,w336] z) [w17,w55,w73,w105,w238,w254] (n (n z [w17,w55,w73,w105,w238,w305] z) [w17,w55,w73,w106,w222,w238] z)) [w17,w55,w73,w108,w222,w238] (n (n (n z [w17,w55,w73,w109,w222,w238] z) [w17,w55,w73,w110,w222,w238] z) [w17,w55,w73,w113,w222,w238] (n z [w17,w55,w73,w119,w205,w238] z))) [w17,w55,w73,w121,w134,w204] (n (n (n (n z [w17,w55,w73,w121,w204,w250] z) [w17,w55,w73,w121,w205,w234] z) [w17,w55,w73,w121,w205,w236] (n (n z [w17,w55,w73,w121,w205,w250] z) [w17,w55,w73,w121,w211,w238] z)) [w17,w55,w73,w121,w222,w234] (n (n (n z [w17,w55,w73,w121,w222,w238] z) [w17,w55,w73,w121,w234,w329] z) [w17,w55,w73,w121,w234,w336] (n z [w17,w55,w73,w125,w222,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aababaa : t5aababaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5aababab := (n (n (n (n (n z [w17,w55,w73,w205,w234,w322] z) [w17,w55,w73,w222,w234,w309] z) [w17,w55,w73,w222,w234,w313] (n (n z [w17,w55,w73,w222,w238,w309] z) [w17,w55,w73,w222,w238,w313] z)) [w17,w55,w73,w222,w238,w315] (n (n (n z [w17,w55,w73,w222,w238,w324] z) [w17,w55,w74,w105,w222,w238] z) [w17,w55,w75,w105,w222,w238] (n z [w17,w55,w76,w105,w222,w238] z))) [w17,w55,w77,w105,w222,w238] (n (n (n (n z [w17,w55,w78,w121,w205,w238] z) [w17,w55,w78,w154,w177,w205] z) [w17,w55,w79,w105,w222,w238] (n z [w17,w55,w79,w121,w205,w238] z)) [w17,w55,w84,w105,w222,w238] (n (n (n z [w17,w55,w87,w105,w222,w238] z) [w17,w55,w91,w105,w222,w234] z) [w17,w55,w91,w105,w222,w238] (n z [w17,w55,w91,w121,w205,w234] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aababab : t5aababab.all (blocked 4 t4) = true := by
  decide +kernel
def t5aababa := (n t5aababaa [w17,w55,w73,w146,w222,w238] t5aababab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aababa : t5aababa.all (blocked 4 t4) = true := by
  simp only [t5aababa, ReplayTree.all, n, ht5aababaa, ht5aababab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aababba := (n (n (n (n (n z [w17,w55,w94,w105,w205,w339] z) [w17,w55,w94,w105,w238,w292] z) [w17,w55,w94,w131,w205,w313] (n (n z [w17,w55,w94,w134,w205,w313] z) [w17,w55,w100,w105,w222,w238] z)) [w17,w55,w103,w105,w222,w238] (n (n (n z [w17,w55,w103,w119,w205,w238] z) [w17,w55,w103,w147,w177,w222] z) [w17,w55,w103,w158,w222,w238] (n z [w17,w55,w103,w177,w222,w238] z))) [w17,w55,w103,w205,w222,w238] (n (n (n (n z [w17,w55,w103,w222,w238] z) [w17,w55,w104,w105,w222,w238] z) [w17,w55,w105,w121,w134,w204] (n (n z [w17,w55,w105,w128,w222,w238] z) [w17,w55,w105,w131,w173,w222] z)) [w17,w55,w105,w131,w177,w222] (n (n (n z [w17,w55,w105,w131,w177,w305] z) [w17,w55,w105,w131,w195,w222] z) [w17,w55,w105,w131,w222,w238] (n z [w17,w55,w105,w131,w222,w263] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aababba : t5aababba.all (blocked 4 t4) = true := by
  decide +kernel
def t5aababbb := (n (n (n (n (n z [w17,w55,w105,w131,w222,w339] z) [w17,w55,w105,w133,w177,w222] z) [w17,w55,w105,w134,w177,w220] (n (n z [w17,w55,w105,w134,w182,w222] z) [w17,w55,w105,w134,w183,w222] z)) [w17,w55,w105,w134,w204,w220] (n (n (n z [w17,w55,w105,w134,w220,w263] z) [w17,w55,w105,w134,w222,w234] z) [w17,w55,w105,w134,w222,w238] (n z [w17,w55,w105,w134,w222,w248] z))) [w17,w55,w105,w134,w222,w265] (n (n (n (n z [w17,w55,w105,w144,w222,w238] z) [w17,w55,w105,w147,w177,w222] z) [w17,w55,w105,w156,w222,w238] (n z [w17,w55,w105,w158,w222,w234] z)) [w17,w55,w105,w158,w222,w238] (n (n (n z [w17,w55,w105,w161,w222,w238] z) [w17,w55,w105,w166,w222,w238] z) [w17,w55,w105,w198,w205,w338] (n z [w17,w55,w105,w198,w234,w296] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aababbb : t5aababbb.all (blocked 4 t4) = true := by
  decide +kernel
def t5aababb := (n t5aababba [w17,w55,w105,w131,w222,w279] t5aababbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aababb : t5aababb.all (blocked 4 t4) = true := by
  simp only [t5aababb, ReplayTree.all, n, ht5aababba, ht5aababbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aabab := (n t5aababa [w17,w55,w91,w121,w222,w238] t5aababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aabab : t5aabab.all (blocked 4 t4) = true := by
  simp only [t5aabab, ReplayTree.all, n, ht5aababa, ht5aababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aaba := (n t5aabaa [w17,w55,w73,w105,w222,w339] t5aabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aaba : t5aaba.all (blocked 4 t4) = true := by
  simp only [t5aaba, ReplayTree.all, n, ht5aabaa, ht5aabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aabbaaa := (n (n (n (n (n z [w17,w55,w105,w222,w234,w278] z) [w17,w55,w105,w222,w234,w296] z) [w17,w55,w105,w222,w234,w338] (n (n z [w17,w55,w105,w222,w238,w278] z) [w17,w55,w105,w222,w238,w281] z)) [w17,w55,w105,w222,w238,w292] (n (n (n z [w17,w55,w105,w222,w238,w296] z) [w17,w55,w105,w222,w238,w304] z) [w17,w55,w105,w222,w238,w349] (n z [w17,w55,w105,w222,w238,w355] z))) [w17,w55,w105,w238,w292,w305] (n (n (n (n z [w17,w55,w110,w134,w177,w222] z) [w17,w55,w119,w134,w177,w205] z) [w17,w55,w119,w147,w177,w205] (n (n z [w17,w55,w119,w158,w205,w238] z) [w17,w55,w120,w134,w177,w205] z)) [w17,w55,w121,w129,w177,w205] (n (n (n z [w17,w55,w121,w130,w177,w205] z) [w17,w55,w121,w131,w173,w205] z) [w17,w55,w121,w131,w177,w205] (n z [w17,w55,w121,w131,w177,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aabbaaa : t5aabbaaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5aabbaab := (n (n (n (n (n z [w17,w55,w121,w131,w177,w296] z) [w17,w55,w121,w131,w195,w205] z) [w17,w55,w121,w131,w205,w238] (n (n z [w17,w55,w121,w131,w205,w263] z) [w17,w55,w121,w131,w205,w279] z)) [w17,w55,w121,w131,w205,w313] (n (n (n z [w17,w55,w121,w131,w205,w339] z) [w17,w55,w121,w132,w177,w205] z) [w17,w55,w121,w133,w177,w205] (n z [w17,w55,w121,w134,w173,w205] z))) [w17,w55,w121,w134,w173,w210] (n (n (n (n z [w17,w55,w121,w134,w173,w222] z) [w17,w55,w121,w134,w173,w251] z) [w17,w55,w121,w134,w173,w296] (n z [w17,w55,w121,w134,w173,w329] z)) [w17,w55,w121,w134,w173,w336] (n (n (n z [w17,w55,w121,w134,w173,w349] z) [w17,w55,w121,w134,w174,w205] z) [w17,w55,w121,w134,w175,w205] (n z [w17,w55,w121,w134,w176,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aabbaab : t5aabbaab.all (blocked 4 t4) = true := by
  decide +kernel
def t5aabbaa := (n t5aabbaaa [w17,w55,w121,w131,w177,w292] t5aabbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aabbaa : t5aabbaa.all (blocked 4 t4) = true := by
  simp only [t5aabbaa, ReplayTree.all, n, ht5aabbaaa, ht5aabbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aabbaba := (n (n (n (n (n z [w17,w55,w121,w134,w177,w205] z) [w17,w55,w121,w134,w177,w206] z) [w17,w55,w121,w134,w177,w207] (n (n z [w17,w55,w121,w134,w177,w208] z) [w17,w55,w121,w134,w177,w211] z)) [w17,w55,w121,w134,w177,w213] (n (n (n z [w17,w55,w121,w134,w177,w222] z) [w17,w55,w121,w134,w177,w229] z) [w17,w55,w121,w134,w177,w249] (n z [w17,w55,w121,w134,w177,w292] z))) [w17,w55,w121,w134,w177,w296] (n (n (n (n z [w17,w55,w121,w134,w177,w298] z) [w17,w55,w121,w134,w177,w307] z) [w17,w55,w121,w134,w178,w205] (n (n z [w17,w55,w121,w134,w179,w205] z) [w17,w55,w121,w134,w180,w205] z)) [w17,w55,w121,w134,w181,w205] (n (n (n z [w17,w55,w121,w134,w183,w205] z) [w17,w55,w121,w134,w189,w205] z) [w17,w55,w121,w134,w192,w205] (n z [w17,w55,w121,w134,w195,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aabbaba : t5aabbaba.all (blocked 4 t4) = true := by
  decide +kernel
def t5aabbabb := (n (n (n (n (n z [w17,w55,w121,w134,w204] z) [w17,w55,w121,w134,w204,w205] z) [w17,w55,w121,w134,w204,w263] (n (n z [w17,w55,w121,w134,w205,w209] z) [w17,w55,w121,w134,w205,w226] z)) [w17,w55,w121,w134,w205,w232] (n (n (n z [w17,w55,w121,w134,w205,w234] z) [w17,w55,w121,w134,w205,w238] z) [w17,w55,w121,w134,w205,w248] (n z [w17,w55,w121,w134,w205,w260] z))) [w17,w55,w121,w134,w205,w263] (n (n (n (n z [w17,w55,w121,w134,w205,w265] z) [w17,w55,w121,w134,w205,w271] z) [w17,w55,w121,w134,w205,w279] (n z [w17,w55,w121,w134,w205,w282] z)) [w17,w55,w121,w134,w205,w309] (n (n (n z [w17,w55,w121,w134,w205,w313] z) [w17,w55,w121,w134,w205,w321] z) [w17,w55,w121,w134,w205,w352] (n z [w17,w55,w121,w134,w205,w357] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aabbabb : t5aabbabb.all (blocked 4 t4) = true := by
  decide +kernel
def t5aabbab := (n t5aabbaba [w17,w55,w121,w134,w195,w222] t5aabbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aabbab : t5aabbab.all (blocked 4 t4) = true := by
  simp only [t5aabbab, ReplayTree.all, n, ht5aabbaba, ht5aabbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aabba := (n t5aabbaa [w17,w55,w121,w134,w177,w204] t5aabbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aabba : t5aabba.all (blocked 4 t4) = true := by
  simp only [t5aabba, ReplayTree.all, n, ht5aabbaa, ht5aabbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aabbbaa := (n (n (n (n (n z [w17,w55,w121,w134,w222,w263] z) [w17,w55,w121,w134,w263,w296] z) [w17,w55,w121,w134,w296,w313] (n (n z [w17,w55,w121,w135,w177,w205] z) [w17,w55,w121,w137,w177,w205] z)) [w17,w55,w121,w139,w177,w205] (n (n (n z [w17,w55,w121,w144,w205,w238] z) [w17,w55,w121,w145,w177,w205] z) [w17,w55,w121,w147,w177,w205] (n z [w17,w55,w121,w148,w177,w205] z))) [w17,w55,w121,w158,w205,w234] (n (n (n (n z [w17,w55,w121,w158,w222,w238] z) [w17,w55,w121,w161,w205,w238] z) [w17,w55,w121,w173,w205,w338] (n (n z [w17,w55,w121,w177,w205,w338] z) [w17,w55,w121,w205,w234,w278] z)) [w17,w55,w121,w205,w234,w338] (n (n (n z [w17,w55,w127,w134,w177,w205] z) [w17,w55,w131,w177,w205,w336] z) [w17,w55,w131,w177,w222,w329] (n z [w17,w55,w131,w177,w222,w336] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aabbbaa : t5aabbbaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5aabbbab := (n (n (n (n (n z [w17,w55,w134,w173,w205,w322] z) [w17,w55,w134,w177,w205,w322] z) [w17,w55,w134,w198,w205,w309] (n (n z [w17,w55,w134,w205,w309,w322] z) [w17,w55,w158,w222,w238,w313] z)) [w17,w55,w222,w238,w296,w313] (n (n (n z [w17,w56,w73,w105,w222,w238] z) [w17,w57,w121,w134,w177,w205] z) [w17,w58,w73,w105,w222,w238] (n z [w17,w58,w73,w121,w205,w238] z))) [w17,w58,w105,w134,w177,w222] (n (n (n (n z [w17,w58,w121,w134,w177,w205] z) [w17,w59,w73,w105,w177,w254] z) [w17,w59,w73,w121,w177,w249] (n z [w17,w59,w73,w146,w177,w222] z)) [w17,w59,w73,w151,w177,w205] (n (n (n z [w17,w60,w73,w105,w222,w238] z) [w17,w60,w121,w134,w177,w205] z) [w17,w63,w73,w105,w222,w234] (n z [w17,w63,w73,w121,w205,w234] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aabbbab : t5aabbbab.all (blocked 4 t4) = true := by
  decide +kernel
def t5aabbba := (n t5aabbbaa [w17,w55,w134,w151,w177,w205] t5aabbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aabbba : t5aabbba.all (blocked 4 t4) = true := by
  simp only [t5aabbba, ReplayTree.all, n, ht5aabbbaa, ht5aabbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aabbbba := (n (n (n (n (n z [w17,w63,w105,w134,w222,w238] z) [w17,w63,w105,w158,w222,w238] z) [w17,w63,w121,w131,w177,w205] (n (n z [w17,w63,w121,w134,w205,w238] z) [w17,w63,w121,w134,w205,w263] z)) [w17,w65,w105,w134,w222,w263] (n (n (n z [w17,w65,w105,w158,w222,w238] z) [w17,w65,w121,w134,w205,w263] z) [w17,w65,w121,w158,w205,w238] (n z [w17,w69,w105,w156,w222,w238] z))) [w17,w73,w105,w156,w222,w238] (n (n (n (n z [w17,w73,w105,w222,w234,w260] z) [w17,w73,w105,w222,w238,w260] z) [w17,w73,w105,w222,w238,w264] (n (n z [w17,w73,w121,w134,w205,w260] z) [w17,w73,w121,w205,w234,w260] z)) [w17,w94,w105,w156,w205,w238] (n (n (n z [w17,w105,w121,w134,w205,w260] z) [w17,w105,w131,w156,w177,w222] z) [w17,w105,w134,w198,w205,w260] (n z [w17,w105,w156,w177,w222,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aabbbba : t5aabbbba.all (blocked 4 t4) = true := by
  decide +kernel
def t5aabbbbb := (n (n (n (n (n z [w17,w105,w156,w222,w238] z) [w17,w105,w158,w159,w222,w238] z) [w17,w105,w158,w222,w238,w263] (n (n z [w17,w121,w131,w156,w177,w205] z) [w17,w121,w134,w156,w177,w205] z)) [w17,w121,w134,w158,w205,w263] (n (n (n z [w17,w121,w134,w160,w177,w205] z) [w17,w121,w134,w173,w205,w260] z) [w17,w121,w134,w177,w205,w260] (n z [w17,w121,w134,w205,w260] z))) [w17,w121,w134,w205,w261,w263] (n (n (n (n z [w18,w23,w38,w55,w296,w313] z) [w18,w55,w121,w134,w177,w205] z) [w19,w23,w38,w55,w296,w313] (n z [w19,w55,w73,w105,w222,w238] z)) [w19,w55,w121,w134,w177,w205] (n (n (n z [w20,w23,w38,w55,w296,w313] z) [w20,w55,w73,w105,w222,w238] z) [w21,w23,w38,w55,w296,w313] (n z [w21,w55,w73,w105,w222,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aabbbbb : t5aabbbbb.all (blocked 4 t4) = true := by
  decide +kernel
def t5aabbbb := (n t5aabbbba [w17,w105,w156,w205,w222,w238] t5aabbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aabbbb : t5aabbbb.all (blocked 4 t4) = true := by
  simp only [t5aabbbb, ReplayTree.all, n, ht5aabbbba, ht5aabbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aabbb := (n t5aabbba [w17,w63,w105,w131,w177,w222] t5aabbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aabbb : t5aabbb.all (blocked 4 t4) = true := by
  simp only [t5aabbb, ReplayTree.all, n, ht5aabbba, ht5aabbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aabb := (n t5aabba [w17,w55,w121,w134,w222,w238] t5aabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aabb : t5aabb.all (blocked 4 t4) = true := by
  simp only [t5aabb, ReplayTree.all, n, ht5aabba, ht5aabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aab := (n t5aaba [w17,w55,w105,w198,w238,w296] t5aabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aab : t5aab.all (blocked 4 t4) = true := by
  simp only [t5aab, ReplayTree.all, n, ht5aaba, ht5aabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aa := (n t5aaa [w17,w38,w105,w157,w177,w222] t5aab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aa : t5aa.all (blocked 4 t4) = true := by
  simp only [t5aa, ReplayTree.all, n, ht5aaa, ht5aab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abaaaaa := (n (n (n (n (n z [w22,w23,w38,w55,w296,w313] z) [w22,w36,w55,w73,w205,w313] z) [w22,w36,w55,w105,w177,w296] (n (n z [w22,w38,w50,w55,w296,w313] z) [w22,w38,w55,w69,w205,w313] z)) [w22,w38,w55,w73,w105,w204] (n (n (n z [w22,w38,w55,w73,w205,w309] z) [w22,w38,w55,w73,w205,w313] z) [w22,w38,w55,w73,w205,w323] (n z [w22,w38,w55,w73,w221,w313] z))) [w22,w38,w55,w73,w296,w313] (n (n (n (n z [w22,w38,w55,w95,w205,w313] z) [w22,w38,w55,w103,w177,w205] z) [w22,w38,w55,w105,w173,w296] (n (n z [w22,w38,w55,w105,w177,w292] z) [w22,w38,w55,w105,w177,w296] z)) [w22,w38,w55,w105,w177,w306] (n (n (n z [w22,w38,w55,w105,w200,w296] z) [w22,w38,w55,w105,w263,w296] z) [w22,w38,w55,w105,w296,w313] (n z [w22,w38,w55,w120,w177,w296] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abaaaaa : t5abaaaaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5abaaaab := (n (n (n (n (n z [w22,w38,w55,w177,w296,w313] z) [w22,w38,w55,w205,w296,w313] z) [w22,w38,w55,w296,w313] (n (n z [w22,w38,w64,w73,w205,w313] z) [w22,w38,w64,w105,w177,w296] z)) [w22,w38,w73,w105,w205,w260] (n (n (n z [w22,w38,w105,w156,w177,w205] z) [w22,w38,w105,w158,w205,w263] z) [w22,w46,w55,w73,w205,w313] (n z [w22,w46,w55,w105,w177,w296] z))) [w22,w47,w55,w73,w205,w313] (n (n (n (n z [w22,w47,w55,w105,w177,w296] z) [w22,w55,w69,w105,w205,w238] z) [w22,w55,w69,w149,w177,w205] (n z [w22,w55,w73,w105,w173,w251] z)) [w22,w55,w73,w105,w177,w249] (n (n (n z [w22,w55,w73,w105,w205,w232] z) [w22,w55,w73,w105,w205,w234] z) [w22,w55,w73,w105,w205,w238] (n z [w22,w55,w73,w105,w205,w245] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abaaaab : t5abaaaab.all (blocked 4 t4) = true := by
  decide +kernel
def t5abaaaa := (n t5abaaaaa [w22,w38,w55,w158,w205,w313] t5abaaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abaaaa : t5abaaaa.all (blocked 4 t4) = true := by
  simp only [t5abaaaa, ReplayTree.all, n, ht5abaaaaa, ht5abaaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abaaaba := (n (n (n (n (n z [w22,w55,w73,w105,w221,w238] z) [w22,w55,w73,w105,w222,w238] z) [w22,w55,w73,w120,w205,w238] (n (n z [w22,w55,w73,w121,w205,w238] z) [w22,w55,w73,w134,w205,w313] z)) [w22,w55,w73,w146,w177,w205] (n (n (n z [w22,w55,w73,w149,w205,w313] z) [w22,w55,w73,w205,w238,w313] z) [w22,w55,w73,w205,w251,w313] (n z [w22,w55,w73,w205,w313,w352] z))) [w22,w55,w91,w105,w205,w238] (n (n (n (n z [w22,w55,w95,w105,w205,w238] z) [w22,w55,w105,w128,w177,w205] z) [w22,w55,w105,w131,w177,w205] (n (n z [w22,w55,w105,w134,w173,w205] z) [w22,w55,w105,w134,w177,w205] z)) [w22,w55,w105,w134,w177,w221] (n (n (n z [w22,w55,w105,w134,w177,w222] z) [w22,w55,w105,w134,w177,w296] z) [w22,w55,w105,w134,w195,w205] (n z [w22,w55,w105,w134,w200,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abaaaba : t5abaaaba.all (blocked 4 t4) = true := by
  decide +kernel
def t5abaaabb := (n (n (n (n (n z [w22,w55,w105,w134,w205,w248] z) [w22,w55,w105,w134,w205,w263] z) [w22,w55,w105,w134,w205,w313] (n (n z [w22,w55,w105,w139,w177,w205] z) [w22,w55,w105,w144,w205,w238] z)) [w22,w55,w105,w149,w177,w296] (n (n (n z [w22,w55,w105,w158,w205,w238] z) [w22,w55,w105,w177,w205,w349] z) [w22,w55,w105,w177,w238,w296] (n z [w22,w55,w105,w177,w251,w296] z))) [w22,w55,w105,w177,w296,w349] (n (n (n (n z [w22,w55,w105,w205,w238,w296] z) [w22,w55,w120,w134,w177,w205] z) [w22,w55,w121,w134,w177,w205] (n z [w22,w64,w73,w105,w205,w238] z)) [w22,w64,w105,w134,w177,w205] (n (n (n z [w23,w26,w38,w55,w296,w313] z) [w23,w28,w91,w105,w238,w261] z) [w23,w30,w38,w55,w296,w313] (n z [w23,w32,w134,w159,w195,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abaaabb : t5abaaabb.all (blocked 4 t4) = true := by
  decide +kernel
def t5abaaab := (n t5abaaaba [w22,w55,w105,w134,w205,w238] t5abaaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abaaab : t5abaaab.all (blocked 4 t4) = true := by
  simp only [t5abaaab, ReplayTree.all, n, ht5abaaaba, ht5abaaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abaaa := (n t5abaaaa [w22,w55,w73,w105,w205,w352] t5abaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abaaa : t5abaaa.all (blocked 4 t4) = true := by
  simp only [t5abaaa, ReplayTree.all, n, ht5abaaaa, ht5abaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abaabaa := (n (n (n (n (n z [w23,w36,w50,w55,w296,w313] z) [w23,w38,w43,w55,w296,w313] z) [w23,w38,w46,w55,w296,w313] (n (n z [w23,w38,w50,w55,w292,w313] z) [w23,w38,w50,w55,w296,w309] z)) [w23,w38,w50,w55,w296,w313] (n (n (n z [w23,w38,w50,w105,w260,w296] z) [w23,w38,w50,w156,w205,w313] z) [w23,w38,w55,w60,w296,w313] (n z [w23,w38,w55,w63,w292,w313] z))) [w23,w38,w55,w63,w296,w309] (n (n (n (n z [w23,w38,w55,w63,w296,w313] z) [w23,w38,w55,w68,w296,w313] z) [w23,w38,w55,w69,w189,w329] (n (n z [w23,w38,w55,w69,w195,w229] z) [w23,w38,w55,w73,w105,w212] z)) [w23,w38,w55,w73,w213,w319] (n (n (n z [w23,w38,w55,w73,w214,w328] z) [w23,w38,w55,w80,w205,w313] z) [w23,w38,w55,w84,w105,w204] (n z [w23,w38,w55,w84,w205,w309] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abaabaa : t5abaabaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5abaabab := (n (n (n (n (n z [w23,w38,w55,w84,w205,w319] z) [w23,w38,w55,w84,w213,w313] z) [w23,w38,w55,w84,w296,w313] (n (n z [w23,w38,w55,w84,w302,w313] z) [w23,w38,w55,w85,w205,w313] z)) [w23,w38,w55,w87,w105,w204] (n (n (n z [w23,w38,w55,w87,w173,w329] z) [w23,w38,w55,w87,w205,w309] z) [w23,w38,w55,w87,w292,w313] (n z [w23,w38,w55,w87,w296,w313] z))) [w23,w38,w55,w91,w105,w204] (n (n (n (n z [w23,w38,w55,w91,w121,w204] z) [w23,w38,w55,w91,w125,w173] z) [w23,w38,w55,w91,w204,w328] (n z [w23,w38,w55,w91,w205,w309] z)) [w23,w38,w55,w91,w205,w310] (n (n (n z [w23,w38,w55,w91,w205,w328] z) [w23,w38,w55,w91,w251,w309] z) [w23,w38,w55,w91,w292,w313] (n z [w23,w38,w55,w91,w296,w309] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abaabab : t5abaabab.all (blocked 4 t4) = true := by
  decide +kernel
def t5abaaba := (n t5abaabaa [w23,w38,w55,w84,w205,w313] t5abaabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abaaba : t5abaaba.all (blocked 4 t4) = true := by
  simp only [t5abaaba, ReplayTree.all, n, ht5abaabaa, ht5abaabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abaabba := (n (n (n (n (n z [w23,w38,w55,w95,w205,w313] z) [w23,w38,w55,w103,w189,w205] z) [w23,w38,w55,w103,w192,w205] (n (n z [w23,w38,w55,w103,w195,w205] z) [w23,w38,w55,w103,w195,w222] z)) [w23,w38,w55,w103,w195,w326] (n (n (n z [w23,w38,w55,w103,w205,w248] z) [w23,w38,w55,w103,w205,w271] z) [w23,w38,w55,w103,w205,w320] (n z [w23,w38,w55,w105,w144,w204] z))) [w23,w38,w55,w105,w166,w204] (n (n (n (n z [w23,w38,w55,w105,w184,w296] z) [w23,w38,w55,w105,w189,w292] z) [w23,w38,w55,w105,w192,w292] (n (n z [w23,w38,w55,w105,w192,w296] z) [w23,w38,w55,w105,w192,w302] z)) [w23,w38,w55,w105,w193,w296] (n (n (n z [w23,w38,w55,w105,w195,w292] z) [w23,w38,w55,w105,w195,w293] z) [w23,w38,w55,w105,w195,w326] (n z [w23,w38,w55,w105,w200,w296] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abaabba : t5abaabba.all (blocked 4 t4) = true := by
  decide +kernel
def t5abaabbb := (n (n (n (n (n z [w23,w38,w55,w105,w205,w285] z) [w23,w38,w55,w105,w248,w292] z) [w23,w38,w55,w105,w270,w296] (n (n z [w23,w38,w55,w105,w271,w292] z) [w23,w38,w55,w105,w288,w292] z)) [w23,w38,w55,w111,w177,w205] (n (n (n z [w23,w38,w55,w113,w177,w302] z) [w23,w38,w55,w113,w192,w296] z) [w23,w38,w55,w114,w177,w326] (n z [w23,w38,w55,w144,w205,w309] z))) [w23,w38,w55,w144,w296,w313] (n (n (n (n z [w23,w38,w55,w149,w195,w292] z) [w23,w38,w55,w163,w205,w313] z) [w23,w38,w55,w166,w205,w309] (n z [w23,w38,w55,w166,w296,w313] z)) [w23,w38,w55,w189,w296,w309] (n (n (n z [w23,w38,w55,w189,w296,w313] z) [w23,w38,w55,w192,w296,w313] z) [w23,w38,w55,w192,w296,w319] (n z [w23,w38,w55,w195,w292,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abaabbb : t5abaabbb.all (blocked 4 t4) = true := by
  decide +kernel
def t5abaabb := (n t5abaabba [w23,w38,w55,w105,w204,w303] t5abaabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abaabb : t5abaabb.all (blocked 4 t4) = true := by
  simp only [t5abaabb, ReplayTree.all, n, ht5abaabba, ht5abaabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abaab := (n t5abaaba [w23,w38,w55,w91,w296,w313] t5abaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abaab : t5abaab.all (blocked 4 t4) = true := by
  simp only [t5abaab, ReplayTree.all, n, ht5abaaba, ht5abaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abaa := (n t5abaaa [w23,w34,w38,w55,w296,w313] t5abaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abaa : t5abaa.all (blocked 4 t4) = true := by
  simp only [t5abaa, ReplayTree.all, n, ht5abaaa, ht5abaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5ababaaa := (n (n (n (n (n z [w23,w38,w55,w195,w296,w313] z) [w23,w38,w55,w205,w286,w309] z) [w23,w38,w55,w248,w296,w313] (n (n z [w23,w38,w55,w271,w296,w313] z) [w23,w38,w55,w285,w296,w313] z)) [w23,w38,w55,w289,w296,w313] (n (n (n z [w23,w38,w59,w63,w296,w313] z) [w23,w38,w60,w69,w205,w313] z) [w23,w38,w60,w73,w105,w204] (n z [w23,w38,w60,w73,w205,w309] z))) [w23,w38,w60,w73,w205,w313] (n (n (n (n z [w23,w38,w60,w73,w205,w319] z) [w23,w38,w60,w73,w213,w313] z) [w23,w38,w60,w73,w296,w313] (n (n z [w23,w38,w60,w84,w205,w313] z) [w23,w38,w60,w103,w177,w205] z)) [w23,w38,w60,w105,w173,w296] (n (n (n z [w23,w38,w60,w105,w177,w292] z) [w23,w38,w60,w105,w177,w296] z) [w23,w38,w60,w105,w177,w302] (n z [w23,w38,w60,w105,w192,w296] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5ababaaa : t5ababaaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5ababaab := (n (n (n (n (n z [w23,w38,w60,w105,w270,w296] z) [w23,w38,w60,w105,w296,w313] z) [w23,w38,w60,w113,w177,w296] (n (n z [w23,w38,w60,w158,w205,w313] z) [w23,w38,w60,w163,w205,w313] z)) [w23,w38,w60,w177,w296,w313] (n (n (n z [w23,w38,w60,w205,w296,w313] z) [w23,w38,w60,w296,w313] z) [w23,w38,w61,w73,w205,w313] (n z [w23,w38,w62,w105,w177,w296] z))) [w23,w38,w63,w65,w296,w313] (n (n (n (n z [w23,w38,w63,w69,w105,w204] z) [w23,w38,w63,w69,w173,w329] z) [w23,w38,w63,w69,w177,w229] (n z [w23,w38,w63,w69,w205,w309] z)) [w23,w38,w63,w73,w105,w204] (n (n (n z [w23,w38,w63,w73,w105,w212] z) [w23,w38,w63,w73,w121,w204] z) [w23,w38,w63,w73,w125,w173] (n z [w23,w38,w63,w73,w204,w328] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5ababaab : t5ababaab.all (blocked 4 t4) = true := by
  decide +kernel
def t5ababaa := (n t5ababaaa [w23,w38,w60,w105,w263,w296] t5ababaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5ababaa : t5ababaa.all (blocked 4 t4) = true := by
  simp only [t5ababaa, ReplayTree.all, n, ht5ababaaa, ht5ababaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abababa := (n (n (n (n (n z [w23,w38,w63,w73,w205,w310] z) [w23,w38,w63,w73,w205,w328] z) [w23,w38,w63,w73,w229,w313] (n (n z [w23,w38,w63,w73,w251,w309] z) [w23,w38,w63,w91,w105,w204] z)) [w23,w38,w63,w91,w205,w309] (n (n (n z [w23,w38,w63,w103,w173,w205] z) [w23,w38,w63,w103,w177,w205] z) [w23,w38,w63,w103,w177,w222] (n z [w23,w38,w63,w103,w177,w326] z))) [w23,w38,w63,w103,w195,w205] (n (n (n (n z [w23,w38,w63,w103,w205,w238] z) [w23,w38,w63,w103,w205,w263] z) [w23,w38,w63,w103,w205,w271] (n (n z [w23,w38,w63,w103,w205,w312] z) [w23,w38,w63,w103,w205,w313] z)) [w23,w38,w63,w104,w205,w313] (n (n (n z [w23,w38,w63,w105,w134,w204] z) [w23,w38,w63,w105,w158,w204] z) [w23,w38,w63,w105,w166,w204] (n z [w23,w38,w63,w105,w173,w292] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abababa : t5abababa.all (blocked 4 t4) = true := by
  decide +kernel
def t5abababb := (n (n (n (n (n z [w23,w38,w63,w105,w177,w293] z) [w23,w38,w63,w105,w177,w326] z) [w23,w38,w63,w105,w195,w292] (n (n z [w23,w38,w63,w105,w204,w295] z) [w23,w38,w63,w105,w204,w296] z)) [w23,w38,w63,w105,w205,w277] (n (n (n z [w23,w38,w63,w105,w209,w296] z) [w23,w38,w63,w105,w238,w292] z) [w23,w38,w63,w105,w260,w296] (n z [w23,w38,w63,w105,w263,w292] z))) [w23,w38,w63,w105,w263,w295] (n (n (n (n z [w23,w38,w63,w105,w263,w296] z) [w23,w38,w63,w105,w271,w292] z) [w23,w38,w63,w105,w279,w292] (n z [w23,w38,w63,w105,w292,w313] z)) [w23,w38,w63,w105,w296,w357] (n (n (n z [w23,w38,w63,w111,w177,w205] z) [w23,w38,w63,w125,w177,w296] z) [w23,w38,w63,w134,w205,w309] (n z [w23,w38,w63,w149,w177,w292] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abababb : t5abababb.all (blocked 4 t4) = true := by
  decide +kernel
def t5ababab := (n t5abababa [w23,w38,w63,w105,w177,w292] t5abababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5ababab : t5ababab.all (blocked 4 t4) = true := by
  simp only [t5ababab, ReplayTree.all, n, ht5abababa, ht5abababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5ababa := (n t5ababaa [w23,w38,w63,w73,w205,w309] t5ababab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5ababa : t5ababa.all (blocked 4 t4) = true := by
  simp only [t5ababa, ReplayTree.all, n, ht5ababaa, ht5ababab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5ababbaa := (n (n (n (n (n z [w23,w38,w63,w158,w205,w309] z) [w23,w38,w63,w158,w205,w312] z) [w23,w38,w63,w158,w205,w313] (n (n z [w23,w38,w63,w159,w296,w313] z) [w23,w38,w63,w166,w205,w309] z)) [w23,w38,w63,w205,w278,w309] (n (n (n z [w23,w38,w63,w205,w296,w309] z) [w23,w38,w63,w205,w313,w355] z) [w23,w38,w63,w261,w296,w313] (n z [w23,w38,w63,w296,w313,w329] z))) [w23,w38,w64,w73,w205,w313] (n (n (n (n z [w23,w38,w64,w105,w177,w296] z) [w23,w38,w69,w105,w205,w268] z) [w23,w38,w73,w105,w204,w268] (n (n z [w23,w38,w73,w105,w205,w266] z) [w23,w38,w73,w105,w205,w268] z)) [w23,w38,w73,w105,w222,w266] (n (n (n z [w23,w38,w73,w105,w222,w268] z) [w23,w38,w73,w105,w251,w268] z) [w23,w38,w73,w105,w268,w329] (n z [w23,w38,w73,w121,w205,w268] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5ababbaa : t5ababbaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5ababbab := (n (n (n (n (n z [w23,w38,w73,w205,w268,w309] z) [w23,w38,w84,w105,w205,w260] z) [w23,w38,w87,w105,w205,w260] (n (n z [w23,w38,w87,w156,w205,w313] z) [w23,w38,w91,w105,w204,w260] z)) [w23,w38,w91,w105,w204,w261] (n (n (n z [w23,w38,w91,w105,w205,w260] z) [w23,w38,w91,w105,w205,w262] z) [w23,w38,w91,w105,w205,w268] (n z [w23,w38,w91,w105,w209,w261] z))) [w23,w38,w91,w105,w210,w260] (n (n (n (n z [w23,w38,w91,w105,w222,w260] z) [w23,w38,w91,w105,w251,w260] z) [w23,w38,w91,w105,w260,w296] (n z [w23,w38,w91,w105,w260,w329] z)) [w23,w38,w91,w121,w205,w260] (n (n (n z [w23,w38,w91,w125,w177,w261] z) [w23,w38,w91,w156,w205,w313] z) [w23,w38,w91,w205,w260,w309] (n z [w23,w38,w103,w156,w195,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5ababbab : t5ababbab.all (blocked 4 t4) = true := by
  decide +kernel
def t5ababba := (n t5ababbaa [w23,w38,w73,w159,w195,w229] t5ababbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5ababba : t5ababba.all (blocked 4 t4) = true := by
  simp only [t5ababba, ReplayTree.all, n, ht5ababbaa, ht5ababbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5ababbba := (n (n (n (n (n z [w23,w38,w103,w159,w195,w205] z) [w23,w38,w103,w165,w177,w205] z) [w23,w38,w103,w166,w205,w263] (n (n z [w23,w38,w103,w166,w205,w271] z) [w23,w38,w104,w159,w195,w205] z)) [w23,w38,w105,w134,w205,w268] (n (n (n z [w23,w38,w105,w144,w205,w260] z) [w23,w38,w105,w156,w189,w205] z) [w23,w38,w105,w156,w192,w205] (n z [w23,w38,w105,w156,w195,w205] z))) [w23,w38,w105,w156,w195,w222] (n (n (n (n z [w23,w38,w105,w156,w195,w292] z) [w23,w38,w105,w156,w205,w248] z) [w23,w38,w105,w156,w205,w271] (n (n z [w23,w38,w105,w156,w205,w288] z) [w23,w38,w105,w156,w205,w364] z)) [w23,w38,w105,w157,w195,w205] (n (n (n z [w23,w38,w105,w158,w204,w271] z) [w23,w38,w105,w158,w205,w268] z) [w23,w38,w105,w158,w205,w270] (n z [w23,w38,w105,w158,w205,w271] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5ababbba : t5ababbba.all (blocked 4 t4) = true := by
  decide +kernel
def t5ababbbb := (n (n (n (n (n z [w23,w38,w105,w162,w177,w205] z) [w23,w38,w105,w163,w205,w263] z) [w23,w38,w105,w163,w205,w270] (n (n z [w23,w38,w105,w165,w173,w205] z) [w23,w38,w105,w165,w177,w205] z)) [w23,w38,w105,w165,w177,w222] (n (n (n z [w23,w38,w105,w165,w177,w292] z) [w23,w38,w105,w165,w195,w205] z) [w23,w38,w105,w165,w205,w238] (n z [w23,w38,w105,w165,w205,w263] z))) [w23,w38,w105,w165,w205,w271] (n (n (n (n z [w23,w38,w105,w165,w205,w279] z) [w23,w38,w105,w165,w205,w288] z) [w23,w38,w105,w165,w205,w313] (n z [w23,w38,w105,w165,w205,w356] z)) [w23,w38,w105,w165,w205,w364] (n (n (n z [w23,w38,w105,w166,w204,w263] z) [w23,w38,w105,w166,w204,w271] z) [w23,w38,w105,w166,w205,w260] (n z [w23,w38,w105,w166,w205,w263] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5ababbbb : t5ababbbb.all (blocked 4 t4) = true := by
  decide +kernel
def t5ababbb := (n t5ababbba [w23,w38,w105,w158,w222,w271] t5ababbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5ababbb : t5ababbb.all (blocked 4 t4) = true := by
  simp only [t5ababbb, ReplayTree.all, n, ht5ababbba, ht5ababbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5ababb := (n t5ababba [w23,w38,w103,w158,w205,w271] t5ababbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5ababb : t5ababb.all (blocked 4 t4) = true := by
  simp only [t5ababb, ReplayTree.all, n, ht5ababba, ht5ababbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abab := (n t5ababa [w23,w38,w63,w156,w205,w313] t5ababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abab : t5abab.all (blocked 4 t4) = true := by
  simp only [t5abab, ReplayTree.all, n, ht5ababa, ht5ababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5aba := (n t5abaa [w23,w38,w55,w195,w296,w309] t5abab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5aba : t5aba.all (blocked 4 t4) = true := by
  simp only [t5aba, ReplayTree.all, n, ht5abaa, ht5abab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abbaaaa := (n (n (n (n (n z [w23,w38,w105,w166,w205,w271] z) [w23,w38,w105,w166,w205,w357] z) [w23,w38,w105,w166,w205,w365] (n (n z [w23,w38,w105,w166,w222,w263] z) [w23,w38,w105,w166,w222,w271] z)) [w23,w38,w105,w166,w263,w296] (n (n (n z [w23,w38,w105,w189,w260,w296] z) [w23,w38,w105,w195,w260,w296] z) [w23,w38,w105,w205,w260,w286] (n z [w23,w38,w105,w205,w260,w361] z))) [w23,w38,w105,w205,w268,w278] (n (n (n (n z [w23,w38,w105,w205,w268,w286] z) [w23,w38,w105,w205,w268,w296] z) [w23,w38,w105,w205,w268,w354] (n (n z [w23,w38,w105,w205,w268,w361] z) [w23,w38,w105,w205,w271,w355] z)) [w23,w38,w105,w205,w271,w362] (n (n (n z [w23,w38,w105,w260,w268,w296] z) [w23,w38,w105,w261,w271,w296] z) [w23,w38,w107,w156,w195,w205] (n z [w23,w38,w121,w156,w195,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbaaaa : t5abbaaaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5abbaaab := (n (n (n (n (n z [w23,w38,w121,w162,w177,w205] z) [w23,w38,w121,w165,w177,w205] z) [w23,w38,w121,w166,w205,w263] (n (n z [w23,w38,w121,w166,w205,w271] z) [w23,w38,w149,w156,w195,w205] z)) [w23,w38,w149,w165,w177,w205] (n (n (n z [w23,w38,w156,w165,w205,w313] z) [w23,w38,w156,w195,w205,w313] z) [w23,w38,w156,w195,w205,w329] (n z [w23,w38,w158,w205,w271,w313] z))) [w23,w38,w159,w166,w205,w313] (n (n (n (n z [w23,w38,w165,w177,w205,w329] z) [w23,w46,w55,w69,w205,w313] z) [w23,w46,w55,w73,w105,w204] (n z [w23,w46,w55,w73,w205,w309] z)) [w23,w46,w55,w73,w205,w313] (n (n (n z [w23,w46,w55,w73,w205,w319] z) [w23,w46,w55,w73,w213,w313] z) [w23,w46,w55,w73,w296,w313] (n z [w23,w46,w55,w84,w205,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbaaab : t5abbaaab.all (blocked 4 t4) = true := by
  decide +kernel
def t5abbaaa := (n t5abbaaaa [w23,w38,w121,w158,w205,w271] t5abbaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbaaa : t5abbaaa.all (blocked 4 t4) = true := by
  simp only [t5abbaaa, ReplayTree.all, n, ht5abbaaaa, ht5abbaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abbaaba := (n (n (n (n (n z [w23,w46,w55,w105,w173,w296] z) [w23,w46,w55,w105,w177,w292] z) [w23,w46,w55,w105,w177,w296] (n (n z [w23,w46,w55,w105,w177,w302] z) [w23,w46,w55,w105,w192,w296] z)) [w23,w46,w55,w105,w263,w296] (n (n (n z [w23,w46,w55,w105,w296,w313] z) [w23,w46,w55,w113,w177,w296] z) [w23,w46,w55,w158,w205,w313] (n z [w23,w46,w55,w177,w296,w313] z))) [w23,w46,w55,w205,w296,w313] (n (n (n (n z [w23,w46,w55,w296,w313] z) [w23,w46,w60,w73,w205,w313] z) [w23,w46,w60,w105,w177,w296] (n (n z [w23,w46,w73,w105,w205,w260] z) [w23,w46,w105,w156,w177,w205] z)) [w23,w46,w105,w158,w205,w263] (n (n (n z [w23,w47,w50,w55,w296,w313] z) [w23,w48,w55,w73,w205,w313] z) [w23,w48,w55,w105,w177,w296] (n z [w23,w49,w55,w73,w205,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbaaba : t5abbaaba.all (blocked 4 t4) = true := by
  decide +kernel
def t5abbaabb := (n (n (n (n (n z [w23,w50,w55,w69,w205,w352] z) [w23,w50,w55,w73,w205,w350] z) [w23,w50,w55,w73,w249,w313] (n (n z [w23,w50,w55,w73,w251,w309] z) [w23,w50,w55,w103,w205,w238] z)) [w23,w50,w55,w105,w134,w204] (n (n (n z [w23,w50,w55,w105,w173,w349] z) [w23,w50,w55,w105,w177,w347] z) [w23,w50,w55,w105,w232,w296] (n z [w23,w50,w55,w105,w238,w292] z))) [w23,w50,w55,w128,w205,w313] (n (n (n (n z [w23,w50,w55,w134,w205,w309] z) [w23,w50,w55,w134,w296,w313] z) [w23,w50,w55,w146,w177,w296] (n z [w23,w50,w55,w149,w177,w292] z)) [w23,w50,w55,w149,w296,w313] (n (n (n z [w23,w50,w55,w238,w296,w313] z) [w23,w50,w55,w251,w296,w313] z) [w23,w50,w55,w296,w313,w349] (n z [w23,w50,w55,w296,w313,w352] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbaabb : t5abbaabb.all (blocked 4 t4) = true := by
  decide +kernel
def t5abbaab := (n t5abbaaba [w23,w49,w55,w105,w177,w296] t5abbaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbaab : t5abbaab.all (blocked 4 t4) = true := by
  simp only [t5abbaab, ReplayTree.all, n, ht5abbaaba, ht5abbaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abbaa := (n t5abbaaa [w23,w46,w55,w103,w177,w205] t5abbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbaa : t5abbaa.all (blocked 4 t4) = true := by
  simp only [t5abbaa, ReplayTree.all, n, ht5abbaaa, ht5abbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abbabaa := (n (n (n (n (n z [w23,w50,w105,w134,w205,w260] z) [w23,w50,w105,w156,w205,w238] z) [w23,w50,w149,w156,w177,w205] (n (n z [w23,w51,w55,w91,w105,w173] z) [w23,w51,w63,w73,w105,w173] z)) [w23,w51,w63,w105,w177,w296] (n (n (n z [w23,w51,w91,w105,w177,w261] z) [w23,w53,w55,w69,w195,w205] z) [w23,w53,w63,w69,w177,w205] (n z [w23,w53,w63,w73,w205,w313] z))) [w23,w53,w73,w159,w195,w205] (n (n (n (n z [w23,w55,w63,w103,w205,w238] z) [w23,w55,w63,w105,w134,w204] z) [w23,w55,w63,w105,w238,w292] (n (n z [w23,w55,w63,w134,w205,w309] z) [w23,w55,w63,w134,w296,w313] z)) [w23,w55,w63,w238,w296,w313] (n (n (n z [w23,w55,w69,w105,w205,w245] z) [w23,w55,w69,w149,w205,w248] z) [w23,w55,w69,w205,w248,w352] (n z [w23,w55,w73,w105,w205,w241] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbabaa : t5abbabaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5abbabab := (n (n (n (n (n z [w23,w55,w73,w105,w205,w247] z) [w23,w55,w73,w105,w213,w245] z) [w23,w55,w73,w105,w214,w250] (n (n z [w23,w55,w73,w105,w222,w241] z) [w23,w55,w73,w105,w222,w245] z)) [w23,w55,w73,w105,w248,w249] (n (n (n z [w23,w55,w73,w113,w205,w245] z) [w23,w55,w73,w113,w213,w238] z) [w23,w55,w73,w121,w205,w245] (n z [w23,w55,w73,w139,w205,w313] z))) [w23,w55,w73,w146,w205,w248] (n (n (n (n z [w23,w55,w73,w205,w245,w313] z) [w23,w55,w73,w205,w245,w319] z) [w23,w55,w80,w105,w205,w238] (n z [w23,w55,w80,w121,w205,w238] z)) [w23,w55,w84,w105,w205,w234] (n (n (n z [w23,w55,w84,w105,w205,w238] z) [w23,w55,w84,w105,w205,w245] z) [w23,w55,w84,w105,w213,w238] (n z [w23,w55,w84,w105,w222,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbabab : t5abbabab.all (blocked 4 t4) = true := by
  decide +kernel
def t5abbaba := (n t5abbabaa [w23,w55,w73,w105,w205,w245] t5abbabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbaba : t5abbaba.all (blocked 4 t4) = true := by
  simp only [t5abbaba, ReplayTree.all, n, ht5abbabaa, ht5abbabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abbabba := (n (n (n (n (n z [w23,w55,w84,w121,w205,w238] z) [w23,w55,w84,w134,w205,w313] z) [w23,w55,w84,w139,w205,w313] (n (n z [w23,w55,w84,w205,w238,w313] z) [w23,w55,w85,w105,w205,w238] z)) [w23,w55,w87,w105,w205,w234] (n (n (n z [w23,w55,w87,w105,w205,w238] z) [w23,w55,w87,w105,w205,w339] z) [w23,w55,w87,w105,w222,w238] (n z [w23,w55,w87,w105,w238,w292] z))) [w23,w55,w87,w121,w205,w238] (n (n (n (n z [w23,w55,w87,w131,w205,w313] z) [w23,w55,w87,w134,w205,w313] z) [w23,w55,w87,w149,w205,w238] (n (n z [w23,w55,w87,w205,w238,w329] z) [w23,w55,w88,w105,w205,w238] z)) [w23,w55,w89,w105,w205,w238] (n (n (n z [w23,w55,w90,w105,w205,w238] z) [w23,w55,w91,w103,w205,w238] z) [w23,w55,w91,w105,w134,w204] (n z [w23,w55,w91,w105,w204,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbabba : t5abbabba.all (blocked 4 t4) = true := by
  decide +kernel
def t5abbabbb := (n (n (n (n (n z [w23,w55,w91,w105,w205,w234] z) [w23,w55,w91,w105,w205,w235] z) [w23,w55,w91,w105,w205,w236] (n (n z [w23,w55,w91,w105,w205,w237] z) [w23,w55,w91,w105,w205,w238] z)) [w23,w55,w91,w105,w205,w239] (n (n (n z [w23,w55,w91,w105,w205,w245] z) [w23,w55,w91,w105,w205,w250] z) [w23,w55,w91,w105,w205,w252] (n z [w23,w55,w91,w105,w205,w259] z))) [w23,w55,w91,w105,w205,w339] (n (n (n (n z [w23,w55,w91,w105,w206,w238] z) [w23,w55,w91,w105,w208,w238] z) [w23,w55,w91,w105,w211,w238] (n z [w23,w55,w91,w105,w213,w238] z)) [w23,w55,w91,w105,w222,w234] (n (n (n z [w23,w55,w91,w105,w222,w238] z) [w23,w55,w91,w105,w229,w238] z) [w23,w55,w91,w105,w234,w329] (n z [w23,w55,w91,w105,w238,w249] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbabbb : t5abbabbb.all (blocked 4 t4) = true := by
  decide +kernel
def t5abbabb := (n t5abbabba [w23,w55,w91,w105,w204,w250] t5abbabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbabb : t5abbabb.all (blocked 4 t4) = true := by
  simp only [t5abbabb, ReplayTree.all, n, ht5abbabba, ht5abbabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abbab := (n t5abbaba [w23,w55,w84,w113,w205,w238] t5abbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbab : t5abbab.all (blocked 4 t4) = true := by
  simp only [t5abbab, ReplayTree.all, n, ht5abbaba, ht5abbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abba := (n t5abbaa [w23,w50,w73,w105,w251,w260] t5abbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abba : t5abba.all (blocked 4 t4) = true := by
  simp only [t5abba, ReplayTree.all, n, ht5abbaa, ht5abbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abbbaaa := (n (n (n (n (n z [w23,w55,w91,w106,w205,w238] z) [w23,w55,w91,w108,w205,w238] z) [w23,w55,w91,w110,w205,w238] (n (n z [w23,w55,w91,w113,w205,w238] z) [w23,w55,w91,w121,w205,w234] z)) [w23,w55,w91,w121,w205,w238] (n (n (n z [w23,w55,w91,w121,w222,w238] z) [w23,w55,w91,w125,w205,w238] z) [w23,w55,w91,w131,w205,w313] (n z [w23,w55,w91,w134,w205,w309] z))) [w23,w55,w91,w134,w205,w313] (n (n (n (n z [w23,w55,w91,w134,w296,w313] z) [w23,w55,w91,w146,w205,w238] z) [w23,w55,w91,w205,w234,w309] (n (n z [w23,w55,w91,w205,w238,w309] z) [w23,w55,w91,w238,w296,w313] z)) [w23,w55,w92,w105,w205,w238] (n (n (n z [w23,w55,w95,w105,w205,w238] z) [w23,w55,w98,w105,w205,w238] z) [w23,w55,w102,w105,w205,w238] (n z [w23,w55,w103,w114,w205,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbbaaa : t5abbbaaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5abbbaab := (n (n (n (n (n z [w23,w55,w103,w147,w195,w205] z) [w23,w55,w103,w166,w205,w238] z) [w23,w55,w103,w195,w205,w238] (n (n z [w23,w55,w103,w205,w238,w248] z) [w23,w55,w105,w114,w205,w238] z)) [w23,w55,w105,w115,w205,w238] (n (n (n z [w23,w55,w105,w128,w205,w248] z) [w23,w55,w105,w130,w195,w205] z) [w23,w55,w105,w131,w189,w205] (n z [w23,w55,w105,w131,w192,w205] z))) [w23,w55,w105,w131,w195,w205] (n (n (n (n z [w23,w55,w105,w131,w195,w222] z) [w23,w55,w105,w131,w195,w292] z) [w23,w55,w105,w131,w205,w248] (n z [w23,w55,w105,w131,w205,w271] z)) [w23,w55,w105,w131,w205,w288] (n (n (n z [w23,w55,w105,w131,w205,w345] z) [w23,w55,w105,w132,w195,w205] z) [w23,w55,w105,w133,w195,w205] (n z [w23,w55,w105,w134,w144,w204] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbbaab : t5abbbaab.all (blocked 4 t4) = true := by
  decide +kernel
def t5abbbaa := (n t5abbbaaa [w23,w55,w103,w134,w195,w205] t5abbbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbbaa : t5abbbaa.all (blocked 4 t4) = true := by
  simp only [t5abbbaa, ReplayTree.all, n, ht5abbbaaa, ht5abbbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abbbaba := (n (n (n (n (n z [w23,w55,w105,w134,w184,w222] z) [w23,w55,w105,w134,w189,w205] z) [w23,w55,w105,w134,w189,w222] (n (n z [w23,w55,w105,w134,w189,w251] z) [w23,w55,w105,w134,w189,w329] z)) [w23,w55,w105,w134,w190,w205] (n (n (n z [w23,w55,w105,w134,w191,w205] z) [w23,w55,w105,w134,w192,w205] z) [w23,w55,w105,w134,w192,w213] (n z [w23,w55,w105,w134,w192,w222] z))) [w23,w55,w105,w134,w192,w296] (n (n (n (n z [w23,w55,w105,w134,w193,w205] z) [w23,w55,w105,w134,w194,w205] z) [w23,w55,w105,w134,w195,w204] (n (n z [w23,w55,w105,w134,w195,w205] z) [w23,w55,w105,w134,w195,w206] z)) [w23,w55,w105,w134,w195,w207] (n (n (n z [w23,w55,w105,w134,w195,w211] z) [w23,w55,w105,w134,w195,w213] z) [w23,w55,w105,w134,w195,w222] (n z [w23,w55,w105,w134,w195,w229] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbbaba : t5abbbaba.all (blocked 4 t4) = true := by
  decide +kernel
def t5abbbabb := (n (n (n (n (n z [w23,w55,w105,w134,w195,w292] z) [w23,w55,w105,w134,w196,w205] z) [w23,w55,w105,w134,w200,w205] (n (n z [w23,w55,w105,w134,w202,w205] z) [w23,w55,w105,w134,w204,w214] z)) [w23,w55,w105,w134,w204,w271] (n (n (n z [w23,w55,w105,w134,w205,w214] z) [w23,w55,w105,w134,w205,w217] z) [w23,w55,w105,w134,w205,w228] (n z [w23,w55,w105,w134,w205,w240] z))) [w23,w55,w105,w134,w205,w244] (n (n (n (n z [w23,w55,w105,w134,w205,w245] z) [w23,w55,w105,w134,w205,w248] z) [w23,w55,w105,w134,w205,w268] (n z [w23,w55,w105,w134,w205,w270] z)) [w23,w55,w105,w134,w205,w271] (n (n (n z [w23,w55,w105,w134,w205,w276] z) [w23,w55,w105,w134,w205,w288] z) [w23,w55,w105,w134,w222,w248] (n z [w23,w55,w105,w134,w222,w271] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbbabb : t5abbbabb.all (blocked 4 t4) = true := by
  decide +kernel
def t5abbbab := (n t5abbbaba [w23,w55,w105,w134,w195,w249] t5abbbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbbab : t5abbbab.all (blocked 4 t4) = true := by
  simp only [t5abbbab, ReplayTree.all, n, ht5abbbaba, ht5abbbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abbba := (n t5abbbaa [w23,w55,w105,w134,w184,w205] t5abbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbba : t5abbba.all (blocked 4 t4) = true := by
  simp only [t5abbba, ReplayTree.all, n, ht5abbbaa, ht5abbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abbbbaa := (n (n (n (n (n z [w23,w55,w105,w136,w205,w238] z) [w23,w55,w105,w137,w177,w205] z) [w23,w55,w105,w139,w173,w205] (n (n z [w23,w55,w105,w139,w177,w205] z) [w23,w55,w105,w139,w177,w213] z)) [w23,w55,w105,w139,w177,w222] (n (n (n z [w23,w55,w105,w139,w177,w296] z) [w23,w55,w105,w139,w177,w302] z) [w23,w55,w105,w139,w192,w205] (n z [w23,w55,w105,w139,w195,w205] z))) [w23,w55,w105,w139,w205,w238] (n (n (n (n z [w23,w55,w105,w139,w205,w245] z) [w23,w55,w105,w139,w205,w263] z) [w23,w55,w105,w139,w205,w313] (n (n z [w23,w55,w105,w142,w205,w238] z) [w23,w55,w105,w142,w205,w339] z)) [w23,w55,w105,w143,w177,w205] (n (n (n z [w23,w55,w105,w144,w173,w251] z) [w23,w55,w105,w144,w173,w349] z) [w23,w55,w105,w144,w177,w249] (n z [w23,w55,w105,w144,w205,w232] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbbbaa : t5abbbbaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5abbbbab := (n (n (n (n (n z [w23,w55,w105,w144,w205,w238] z) [w23,w55,w105,w144,w205,w352] z) [w23,w55,w105,w144,w222,w238] (n (n z [w23,w55,w105,w145,w195,w205] z) [w23,w55,w105,w147,w195,w205] z)) [w23,w55,w105,w148,w195,w205] (n (n (n z [w23,w55,w105,w158,w205,w245] z) [w23,w55,w105,w163,w205,w238] z) [w23,w55,w105,w165,w205,w238] (n z [w23,w55,w105,w166,w205,w234] z))) [w23,w55,w105,w166,w205,w238] (n (n (n (n z [w23,w55,w105,w166,w222,w238] z) [w23,w55,w105,w172,w205,w238] z) [w23,w55,w105,w177,w245,w296] (n z [w23,w55,w105,w189,w205,w338] z)) [w23,w55,w105,w189,w234,w296] (n (n (n z [w23,w55,w105,w189,w238,w296] z) [w23,w55,w105,w192,w238,w296] z) [w23,w55,w105,w192,w245,w296] (n z [w23,w55,w105,w195,w205,w338] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbbbab : t5abbbbab.all (blocked 4 t4) = true := by
  decide +kernel
def t5abbbba := (n t5abbbbaa [w23,w55,w105,w144,w205,w234] t5abbbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbbba : t5abbbba.all (blocked 4 t4) = true := by
  simp only [t5abbbba, ReplayTree.all, n, ht5abbbbaa, ht5abbbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abbbbba := (n (n (n (n (n z [w23,w55,w105,w195,w238,w292] z) [w23,w55,w105,w195,w238,w296] z) [w23,w55,w105,w205,w234,w286] (n (n z [w23,w55,w105,w205,w234,w343] z) [w23,w55,w105,w205,w238,w286] z)) [w23,w55,w105,w205,w244,w338] (n (n (n z [w23,w55,w105,w205,w245,w296] z) [w23,w55,w105,w205,w248,w349] z) [w23,w55,w105,w238,w248,w292] (n z [w23,w55,w105,w238,w271,w296] z))) [w23,w55,w106,w134,w195,w205] (n (n (n (n z [w23,w55,w109,w134,w195,w205] z) [w23,w55,w110,w134,w195,w205] z) [w23,w55,w113,w134,w177,w213] (n (n z [w23,w55,w113,w134,w192,w205] z) [w23,w55,w113,w134,w195,w205] z)) [w23,w55,w113,w139,w177,w205] (n (n (n z [w23,w55,w114,w147,w177,w205] z) [w23,w55,w121,w131,w195,w205] z) [w23,w55,w121,w134,w189,w205] (n z [w23,w55,w121,w134,w192,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbbbba : t5abbbbba.all (blocked 4 t4) = true := by
  decide +kernel
def t5abbbbbb := (n (n (n (n (n z [w23,w55,w121,w134,w195,w222] z) [w23,w55,w121,w134,w205,w248] z) [w23,w55,w121,w134,w205,w271] (n (n z [w23,w55,w121,w137,w177,w205] z) [w23,w55,w121,w139,w177,w205] z)) [w23,w55,w121,w144,w205,w238] (n (n (n z [w23,w55,w121,w166,w205,w238] z) [w23,w55,w125,w134,w195,w205] z) [w23,w55,w131,w195,w205,w329] (n z [w23,w55,w134,w144,w205,w309] z))) [w23,w55,w134,w144,w296,w313] (n (n (n (n z [w23,w55,w134,w146,w195,w205] z) [w23,w55,w134,w166,w205,w313] z) [w23,w55,w134,w189,w205,w309] (n z [w23,w55,w134,w195,w205,w309] z)) [w23,w55,w134,w195,w296,w313] (n (n (n z [w23,w55,w144,w146,w177,w205] z) [w23,w55,w195,w238,w296,w313] z) [w23,w55,w238,w248,w296,w313] (n z [w23,w56,w91,w105,w205,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbbbbb : t5abbbbbb.all (blocked 4 t4) = true := by
  decide +kernel
def t5abbbbb := (n t5abbbbba [w23,w55,w121,w134,w195,w205] t5abbbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbbbb : t5abbbbb.all (blocked 4 t4) = true := by
  simp only [t5abbbbb, ReplayTree.all, n, ht5abbbbba, ht5abbbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abbbb := (n t5abbbba [w23,w55,w105,w195,w234,w296] t5abbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbbb : t5abbbb.all (blocked 4 t4) = true := by
  simp only [t5abbbb, ReplayTree.all, n, ht5abbbba, ht5abbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abbb := (n t5abbba [w23,w55,w105,w135,w195,w205] t5abbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abbb : t5abbb.all (blocked 4 t4) = true := by
  simp only [t5abbb, ReplayTree.all, n, ht5abbba, ht5abbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5abb := (n t5abba [w23,w55,w91,w105,w238,w292] t5abbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5abb : t5abb.all (blocked 4 t4) = true := by
  simp only [t5abb, ReplayTree.all, n, ht5abba, ht5abbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5ab := (n t5aba [w23,w38,w105,w166,w205,w268] t5abb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5ab : t5ab.all (blocked 4 t4) = true := by
  simp only [t5ab, ReplayTree.all, n, ht5aba, ht5abb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5a := (n t5aa [w21,w55,w121,w134,w177,w205] t5ab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5a : t5a.all (blocked 4 t4) = true := by
  simp only [t5a, ReplayTree.all, n, ht5aa, ht5ab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5baaaaaa := (n (n (n (n (n z [w23,w58,w91,w105,w205,w238] z) [w23,w58,w105,w134,w195,w205] z) [w23,w59,w73,w105,w195,w249] (n (n z [w23,w59,w73,w146,w195,w205] z) [w23,w59,w91,w105,w177,w249] z)) [w23,w59,w91,w146,w177,w205] (n (n (n z [w23,w60,w69,w105,w205,w238] z) [w23,w60,w73,w105,w205,w234] z) [w23,w60,w73,w105,w205,w238] (n z [w23,w60,w73,w105,w205,w245] z))) [w23,w60,w73,w105,w213,w238] (n (n (n (n z [w23,w60,w73,w105,w222,w238] z) [w23,w60,w73,w113,w205,w238] z) [w23,w60,w73,w121,w205,w238] (n (n z [w23,w60,w73,w134,w205,w313] z) [w23,w60,w73,w205,w238,w313] z)) [w23,w60,w84,w105,w205,w238] (n (n (n z [w23,w60,w91,w105,w205,w238] z) [w23,w60,w105,w131,w177,w205] z) [w23,w60,w105,w134,w173,w205] (n z [w23,w60,w105,w134,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baaaaaa : t5baaaaaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5baaaaab := (n (n (n (n (n z [w23,w60,w105,w134,w177,w222] z) [w23,w60,w105,w134,w177,w296] z) [w23,w60,w105,w134,w192,w205] (n (n z [w23,w60,w105,w134,w195,w205] z) [w23,w60,w105,w134,w205,w238] z)) [w23,w60,w105,w134,w205,w263] (n (n (n z [w23,w60,w105,w134,w205,w270] z) [w23,w60,w105,w134,w205,w313] z) [w23,w60,w105,w139,w177,w205] (n z [w23,w60,w105,w158,w205,w238] z))) [w23,w60,w105,w163,w205,w238] (n (n (n (n z [w23,w60,w105,w177,w238,w296] z) [w23,w60,w105,w205,w238,w296] z) [w23,w60,w113,w134,w177,w205] (n z [w23,w60,w121,w134,w177,w205] z)) [w23,w61,w73,w105,w205,w238] (n (n (n z [w23,w62,w105,w134,w177,w205] z) [w23,w63,w69,w105,w205,w234] z) [w23,w63,w69,w149,w205,w238] (n z [w23,w63,w73,w105,w204,w250] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baaaaab : t5baaaaab.all (blocked 4 t4) = true := by
  decide +kernel
def t5baaaaa := (n t5baaaaaa [w23,w60,w105,w134,w177,w213] t5baaaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baaaaa : t5baaaaa.all (blocked 4 t4) = true := by
  simp only [t5baaaaa, ReplayTree.all, n, ht5baaaaaa, ht5baaaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5baaaaba := (n (n (n (n (n z [w23,w63,w73,w105,w205,w235] z) [w23,w63,w73,w105,w205,w250] z) [w23,w63,w73,w105,w222,w234] (n (n z [w23,w63,w73,w105,w234,w329] z) [w23,w63,w73,w105,w238,w249] z)) [w23,w63,w73,w121,w205,w234] (n (n (n z [w23,w63,w73,w146,w205,w238] z) [w23,w63,w73,w205,w234,w309] z) [w23,w63,w91,w105,w205,w234] (n z [w23,w63,w103,w147,w177,w205] z))) [w23,w63,w103,w158,w205,w238] (n (n (n (n z [w23,w63,w105,w128,w205,w238] z) [w23,w63,w105,w131,w173,w205] z) [w23,w63,w105,w131,w177,w205] (n (n z [w23,w63,w105,w131,w177,w222] z) [w23,w63,w105,w131,w177,w292] z)) [w23,w63,w105,w131,w195,w205] (n (n (n z [w23,w63,w105,w131,w205,w238] z) [w23,w63,w105,w131,w205,w263] z) [w23,w63,w105,w131,w205,w271] (n z [w23,w63,w105,w131,w205,w279] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baaaaba : t5baaaaba.all (blocked 4 t4) = true := by
  decide +kernel
def t5baaaabb := (n (n (n (n (n z [w23,w63,w105,w131,w205,w339] z) [w23,w63,w105,w132,w177,w205] z) [w23,w63,w105,w134,w173,w251] (n (n z [w23,w63,w105,w134,w177,w249] z) [w23,w63,w105,w134,w204,w263] z)) [w23,w63,w105,w134,w205,w232] (n (n (n z [w23,w63,w105,w134,w205,w234] z) [w23,w63,w105,w134,w205,w238] z) [w23,w63,w105,w134,w205,w260] (n z [w23,w63,w105,w134,w205,w263] z))) [w23,w63,w105,w134,w205,w265] (n (n (n (n z [w23,w63,w105,w134,w205,w352] z) [w23,w63,w105,w134,w205,w357] z) [w23,w63,w105,w134,w222,w238] (n z [w23,w63,w105,w134,w222,w263] z)) [w23,w63,w105,w134,w263,w296] (n (n (n z [w23,w63,w105,w147,w177,w205] z) [w23,w63,w105,w156,w205,w238] z) [w23,w63,w105,w158,w205,w234] (n z [w23,w63,w105,w158,w205,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baaaabb : t5baaaabb.all (blocked 4 t4) = true := by
  decide +kernel
def t5baaaab := (n t5baaaaba [w23,w63,w105,w131,w205,w313] t5baaaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baaaab : t5baaaab.all (blocked 4 t4) = true := by
  simp only [t5baaaab, ReplayTree.all, n, ht5baaaaba, ht5baaaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5baaaa := (n t5baaaaa [w23,w63,w73,w105,w205,w234] t5baaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baaaa : t5baaaa.all (blocked 4 t4) = true := by
  simp only [t5baaaa, ReplayTree.all, n, ht5baaaaa, ht5baaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5baaabaa := (n (n (n (n (n z [w23,w63,w105,w161,w205,w238] z) [w23,w63,w105,w166,w205,w234] z) [w23,w63,w105,w205,w234,w278] (n (n z [w23,w63,w105,w205,w234,w296] z) [w23,w63,w105,w205,w234,w338] z)) [w23,w63,w105,w205,w238,w349] (n (n (n z [w23,w63,w105,w205,w238,w355] z) [w23,w63,w105,w238,w261,w296] z) [w23,w63,w121,w131,w177,w205] (n z [w23,w63,w121,w134,w205,w238] z))) [w23,w63,w121,w134,w205,w263] (n (n (n (n z [w23,w63,w121,w158,w205,w238] z) [w23,w63,w131,w177,w205,w329] z) [w23,w63,w134,w146,w177,w205] (n (n z [w23,w63,w134,w159,w205,w313] z) [w23,w63,w158,w205,w238,w313] z)) [w23,w64,w73,w105,w205,w238] (n (n (n z [w23,w64,w105,w134,w177,w205] z) [w23,w65,w105,w134,w205,w271] z) [w23,w65,w105,w166,w205,w238] (n z [w23,w68,w73,w105,w177,w249] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baaabaa : t5baaabaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5baaabab := (n (n (n (n (n z [w23,w73,w105,w205,w234,w268] z) [w23,w87,w105,w156,w205,w238] z) [w23,w91,w105,w134,w205,w260] (n (n z [w23,w91,w105,w156,w205,w238] z) [w23,w91,w105,w205,w234,w260] z)) [w23,w91,w105,w205,w238,w260] (n (n (n z [w23,w105,w131,w156,w195,w205] z) [w23,w105,w131,w165,w177,w205] z) [w23,w105,w134,w144,w205,w260] (n z [w23,w105,w134,w156,w195,w205] z))) [w23,w105,w134,w166,w205,w263] (n (n (n (n z [w23,w105,w134,w189,w205,w260] z) [w23,w105,w134,w195,w205,w260] z) [w23,w105,w134,w205,w260,w268] (n z [w23,w105,w134,w205,w261,w271] z)) [w23,w105,w156,w165,w205,w238] (n (n (n z [w23,w105,w156,w195,w205,w238] z) [w23,w105,w156,w205,w238,w248] z) [w23,w105,w158,w205,w238,w271] (n z [w23,w105,w159,w166,w205,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baaabab : t5baaabab.all (blocked 4 t4) = true := by
  decide +kernel
def t5baaaba := (n t5baaabaa [w23,w68,w73,w146,w177,w205] t5baaabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baaaba : t5baaaba.all (blocked 4 t4) = true := by
  simp only [t5baaaba, ReplayTree.all, n, ht5baaabaa, ht5baaabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5baaabba := (n (n (n (n (n z [w26,w47,w55,w105,w177,w296] z) [w26,w55,w73,w105,w222,w238] z) [w26,w55,w73,w121,w205,w238] (n (n z [w26,w55,w105,w134,w177,w222] z) [w26,w55,w121,w134,w177,w205] z)) [w27,w46,w55,w73,w205,w313] (n (n (n z [w27,w46,w55,w105,w177,w296] z) [w27,w55,w91,w105,w222,w238] z) [w27,w55,w91,w121,w205,w238] (n z [w27,w55,w105,w134,w195,w222] z))) [w27,w55,w121,w134,w195,w205] (n (n (n (n z [w28,w38,w55,w91,w121,w173] z) [w28,w38,w63,w73,w121,w173] z) [w29,w55,w73,w105,w222,w238] (n (n z [w30,w55,w73,w105,w222,w238] z) [w30,w55,w121,w134,w177,w205] z)) [w31,w38,w55,w91,w105,w173] (n (n (n z [w31,w38,w63,w73,w105,w173] z) [w31,w38,w63,w105,w177,w296] z) [w31,w55,w91,w105,w205,w238] (n z [w31,w55,w105,w134,w195,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baaabba : t5baaabba.all (blocked 4 t4) = true := by
  decide +kernel
def t5baaabbb := (n (n (n (n (n z [w32,w38,w63,w69,w177,w222] z) [w33,w55,w121,w134,w177,w205] z) [w34,w55,w73,w105,w222,w238] (n (n z [w34,w55,w121,w134,w177,w205] z) [w35,w38,w55,w69,w195,w205] z)) [w35,w38,w63,w69,w177,w205] (n (n (n z [w35,w38,w63,w73,w205,w313] z) [w35,w55,w91,w105,w205,w238] z) [w35,w55,w105,w134,w195,w205] (n z [w36,w55,w73,w105,w222,w248] z))) [w36,w55,w121,w144,w177,w205] (n (n (n (n z [w36,w59,w73,w105,w195,w222] z) [w36,w59,w91,w121,w177,w205] z) [w36,w63,w73,w105,w222,w238] (n z [w36,w63,w121,w134,w177,w205] z)) [w36,w68,w73,w105,w177,w222] (n (n (n z [w36,w68,w73,w121,w177,w205] z) [w37,w55,w73,w105,w195,w222] z) [w37,w55,w91,w121,w177,w205] (n z [w37,w63,w73,w105,w177,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baaabbb : t5baaabbb.all (blocked 4 t4) = true := by
  decide +kernel
def t5baaabb := (n t5baaabba [w32,w38,w55,w69,w195,w222] t5baaabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baaabb : t5baaabb.all (blocked 4 t4) = true := by
  simp only [t5baaabb, ReplayTree.all, n, ht5baaabba, ht5baaabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5baaab := (n t5baaaba [w26,w47,w55,w73,w205,w313] t5baaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baaab : t5baaab.all (blocked 4 t4) = true := by
  simp only [t5baaab, ReplayTree.all, n, ht5baaaba, ht5baaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5baaa := (n t5baaaa [w23,w63,w105,w158,w222,w238] t5baaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baaa : t5baaa.all (blocked 4 t4) = true := by
  simp only [t5baaa, ReplayTree.all, n, ht5baaaa, ht5baaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5baabaaa := (n (n (n (n (n z [w38,w50,w55,w73,w121,w204] z) [w38,w50,w55,w73,w221,w313] z) [w38,w50,w55,w103,w177,w222] (n (n z [w38,w50,w55,w120,w177,w296] z) [w38,w50,w55,w121,w296,w313] z)) [w38,w50,w55,w222,w296,w313] (n (n (n z [w38,w50,w73,w105,w222,w260] z) [w38,w50,w73,w121,w205,w260] z) [w38,w50,w105,w156,w177,w222] (n z [w38,w50,w105,w158,w222,w263] z))) [w38,w50,w121,w156,w177,w205] (n (n (n (n z [w38,w50,w121,w158,w205,w263] z) [w38,w55,w63,w73,w121,w204] z) [w38,w55,w63,w103,w177,w222] (n (n z [w38,w55,w63,w121,w296,w313] z) [w38,w55,w63,w222,w296,w313] z)) [w38,w55,w65,w84,w205,w313] (n (n (n z [w38,w55,w65,w105,w192,w296] z) [w38,w55,w69,w105,w184,w222] z) [w38,w55,w69,w105,w189,w222] (n z [w38,w55,w69,w105,w192,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baabaaa : t5baabaaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5baabaab := (n (n (n (n (n z [w38,w55,w69,w105,w195,w305] z) [w38,w55,w69,w105,w222,w248] z) [w38,w55,w69,w105,w222,w271] (n (n z [w38,w55,w69,w105,w222,w288] z) [w38,w55,w69,w107,w195,w222] z)) [w38,w55,w69,w121,w189,w205] (n (n (n z [w38,w55,w69,w121,w195,w222] z) [w38,w55,w69,w149,w195,w222] z) [w38,w55,w69,w195,w222,w313] (n z [w38,w55,w69,w195,w222,w329] z))) [w38,w55,w69,w195,w222,w336] (n (n (n (n z [w38,w55,w70,w105,w195,w222] z) [w38,w55,w71,w105,w195,w222] z) [w38,w55,w72,w105,w195,w222] (n z [w38,w55,w73,w91,w121,w204] z)) [w38,w55,w73,w103,w195,w222] (n (n (n z [w38,w55,w73,w105,w184,w222] z) [w38,w55,w73,w105,w184,w336] z) [w38,w55,w73,w105,w185,w222] (n z [w38,w55,w73,w105,w186,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baabaab : t5baabaab.all (blocked 4 t4) = true := by
  decide +kernel
def t5baabaa := (n t5baabaaa [w38,w55,w69,w105,w195,w222] t5baabaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baabaa : t5baabaa.all (blocked 4 t4) = true := by
  simp only [t5baabaa, ReplayTree.all, n, ht5baabaaa, ht5baabaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5baababa := (n (n (n (n (n z [w38,w55,w73,w105,w188,w222] z) [w38,w55,w73,w105,w189,w222] z) [w38,w55,w73,w105,w189,w336] (n (n z [w38,w55,w73,w105,w190,w222] z) [w38,w55,w73,w105,w191,w222] z)) [w38,w55,w73,w105,w192,w222] (n (n (n z [w38,w55,w73,w105,w193,w222] z) [w38,w55,w73,w105,w194,w222] z) [w38,w55,w73,w105,w195,w220] (n z [w38,w55,w73,w105,w195,w221] z))) [w38,w55,w73,w105,w195,w222] (n (n (n (n z [w38,w55,w73,w105,w195,w231] z) [w38,w55,w73,w105,w195,w254] z) [w38,w55,w73,w105,w195,w305] (n (n z [w38,w55,w73,w105,w196,w222] z) [w38,w55,w73,w105,w197,w205] z)) [w38,w55,w73,w105,w197,w222] (n (n (n z [w38,w55,w73,w105,w199,w222] z) [w38,w55,w73,w105,w200,w221] z) [w38,w55,w73,w105,w200,w222] (n z [w38,w55,w73,w105,w202,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baababa : t5baababa.all (blocked 4 t4) = true := by
  decide +kernel
def t5baababb := (n (n (n (n (n z [w38,w55,w73,w105,w214,w220] z) [w38,w55,w73,w105,w214,w222] z) [w38,w55,w73,w105,w216,w222] (n (n z [w38,w55,w73,w105,w217,w222] z) [w38,w55,w73,w105,w220,w271] z)) [w38,w55,w73,w105,w221,w248] (n (n (n z [w38,w55,w73,w105,w222,w228] z) [w38,w55,w73,w105,w222,w240] z) [w38,w55,w73,w105,w222,w241] (n z [w38,w55,w73,w105,w222,w244] z))) [w38,w55,w73,w105,w222,w245] (n (n (n (n z [w38,w55,w73,w105,w222,w248] z) [w38,w55,w73,w105,w222,w266] z) [w38,w55,w73,w105,w222,w268] (n z [w38,w55,w73,w105,w222,w270] z)) [w38,w55,w73,w105,w222,w271] (n (n (n z [w38,w55,w73,w105,w222,w276] z) [w38,w55,w73,w105,w222,w288] z) [w38,w55,w73,w106,w195,w222] (n z [w38,w55,w73,w108,w195,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baababb : t5baababb.all (blocked 4 t4) = true := by
  decide +kernel
def t5baabab := (n t5baababa [w38,w55,w73,w105,w212,w222] t5baababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baabab : t5baabab.all (blocked 4 t4) = true := by
  simp only [t5baabab, ReplayTree.all, n, ht5baababa, ht5baababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5baaba := (n t5baabaa [w38,w55,w73,w105,w187,w222] t5baabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baaba : t5baaba.all (blocked 4 t4) = true := by
  simp only [t5baaba, ReplayTree.all, n, ht5baabaa, ht5baabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5baabbaa := (n (n (n (n (n z [w38,w55,w73,w110,w195,w222] z) [w38,w55,w73,w113,w192,w222] z) [w38,w55,w73,w113,w195,w222] (n (n z [w38,w55,w73,w119,w195,w205] z) [w38,w55,w73,w120,w177,w221] z)) [w38,w55,w73,w121,w184,w205] (n (n (n z [w38,w55,w73,w121,w184,w222] z) [w38,w55,w73,w121,w189,w205] z) [w38,w55,w73,w121,w189,w222] (n z [w38,w55,w73,w121,w189,w251] z))) [w38,w55,w73,w121,w189,w329] (n (n (n (n z [w38,w55,w73,w121,w189,w336] z) [w38,w55,w73,w121,w191,w205] z) [w38,w55,w73,w121,w192,w213] (n (n z [w38,w55,w73,w121,w192,w222] z) [w38,w55,w73,w121,w195,w213] z)) [w38,w55,w73,w121,w195,w222] (n (n (n z [w38,w55,w73,w121,w204,w214] z) [w38,w55,w73,w121,w205,w214] z) [w38,w55,w73,w121,w205,w244] (n z [w38,w55,w73,w121,w205,w268] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baabbaa : t5baabbaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5baabbab := (n (n (n (n (n z [w38,w55,w73,w121,w222,w271] z) [w38,w55,w73,w125,w195,w222] z) [w38,w55,w73,w146,w195,w222] (n (n z [w38,w55,w73,w184,w222,w313] z) [w38,w55,w73,w184,w222,w318] z)) [w38,w55,w73,w189,w205,w322] (n (n (n z [w38,w55,w73,w189,w222,w309] z) [w38,w55,w73,w189,w222,w313] z) [w38,w55,w73,w192,w222,w313] (n z [w38,w55,w73,w192,w222,w319] z))) [w38,w55,w73,w195,w222,w309] (n (n (n (n z [w38,w55,w73,w195,w222,w313] z) [w38,w55,w73,w195,w222,w318] z) [w38,w55,w73,w195,w222,w324] (n z [w38,w55,w73,w222,w248,w313] z)) [w38,w55,w73,w222,w271,w313] (n (n (n z [w38,w55,w74,w105,w195,w222] z) [w38,w55,w75,w105,w195,w222] z) [w38,w55,w76,w105,w195,w222] (n z [w38,w55,w77,w105,w195,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baabbab : t5baabbab.all (blocked 4 t4) = true := by
  decide +kernel
def t5baabba := (n t5baabbaa [w38,w55,w73,w121,w222,w248] t5baabbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baabba : t5baabba.all (blocked 4 t4) = true := by
  simp only [t5baabba, ReplayTree.all, n, ht5baabbaa, ht5baabbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5baabbba := (n (n (n (n (n z [w38,w55,w80,w105,w177,w222] z) [w38,w55,w80,w121,w173,w205] z) [w38,w55,w80,w121,w177,w205] (n (n z [w38,w55,w80,w121,w177,w222] z) [w38,w55,w80,w121,w177,w296] z)) [w38,w55,w80,w121,w177,w301] (n (n (n z [w38,w55,w80,w121,w195,w205] z) [w38,w55,w80,w121,w205,w238] z) [w38,w55,w80,w121,w205,w263] (n z [w38,w55,w80,w121,w205,w287] z))) [w38,w55,w80,w121,w205,w313] (n (n (n (n z [w38,w55,w80,w177,w205,w336] z) [w38,w55,w81,w121,w177,w205] z) [w38,w55,w82,w121,w177,w205] (n (n z [w38,w55,w83,w121,w177,w205] z) [w38,w55,w84,w105,w192,w222] z)) [w38,w55,w84,w105,w195,w222] (n (n (n z [w38,w55,w84,w113,w177,w222] z) [w38,w55,w84,w121,w173,w205] z) [w38,w55,w84,w121,w177,w205] (n z [w38,w55,w84,w121,w177,w213] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baabbba : t5baabbba.all (blocked 4 t4) = true := by
  decide +kernel
def t5baabbbb := (n (n (n (n (n z [w38,w55,w84,w121,w177,w296] z) [w38,w55,w84,w121,w177,w302] z) [w38,w55,w84,w121,w192,w205] (n (n z [w38,w55,w84,w121,w195,w205] z) [w38,w55,w84,w121,w205,w238] z)) [w38,w55,w84,w121,w205,w263] (n (n (n z [w38,w55,w84,w121,w205,w313] z) [w38,w55,w85,w121,w177,w205] z) [w38,w55,w86,w121,w177,w205] (n z [w38,w55,w87,w94,w205,w313] z))) [w38,w55,w87,w105,w173,w222] (n (n (n (n z [w38,w55,w87,w105,w177,w222] z) [w38,w55,w87,w105,w177,w305] z) [w38,w55,w87,w105,w195,w222] (n z [w38,w55,w87,w105,w222,w238] z)) [w38,w55,w87,w105,w222,w263] (n (n (n z [w38,w55,w87,w105,w222,w279] z) [w38,w55,w87,w105,w222,w288] z) [w38,w55,w87,w121,w173,w205] (n z [w38,w55,w87,w121,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baabbbb : t5baabbbb.all (blocked 4 t4) = true := by
  decide +kernel
def t5baabbb := (n t5baabbba [w38,w55,w84,w121,w177,w222] t5baabbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baabbb : t5baabbb.all (blocked 4 t4) = true := by
  simp only [t5baabbb, ReplayTree.all, n, ht5baabbba, ht5baabbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5baabb := (n t5baabba [w38,w55,w79,w105,w195,w222] t5baabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baabb : t5baabb.all (blocked 4 t4) = true := by
  simp only [t5baabb, ReplayTree.all, n, ht5baabba, ht5baabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5baab := (n t5baaba [w38,w55,w73,w109,w195,w222] t5baabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baab : t5baab.all (blocked 4 t4) = true := by
  simp only [t5baab, ReplayTree.all, n, ht5baaba, ht5baabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5baa := (n t5baaa [w37,w63,w73,w121,w177,w205] t5baab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baa : t5baa.all (blocked 4 t4) = true := by
  simp only [t5baa, ReplayTree.all, n, ht5baaa, ht5baab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5babaaaa := (n (n (n (n (n z [w38,w55,w87,w121,w177,w292] z) [w38,w55,w87,w121,w177,w296] z) [w38,w55,w87,w121,w195,w205] (n (n z [w38,w55,w87,w121,w205,w238] z) [w38,w55,w87,w121,w205,w263] z)) [w38,w55,w87,w121,w205,w279] (n (n (n z [w38,w55,w87,w121,w205,w288] z) [w38,w55,w87,w121,w205,w313] z) [w38,w55,w87,w149,w177,w222] (n z [w38,w55,w87,w177,w205,w336] z))) [w38,w55,w87,w177,w222,w329] (n (n (n (n z [w38,w55,w87,w177,w222,w336] z) [w38,w55,w88,w121,w177,w205] z) [w38,w55,w89,w105,w177,w222] (n (n z [w38,w55,w89,w121,w177,w205] z) [w38,w55,w90,w121,w177,w205] z)) [w38,w55,w91,w94,w205,w313] (n (n (n z [w38,w55,w91,w105,w121,w204] z) [w38,w55,w91,w105,w177,w220] z) [w38,w55,w91,w105,w184,w222] (n z [w38,w55,w91,w105,w189,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5babaaaa : t5babaaaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5babaaab := (n (n (n (n (n z [w38,w55,w91,w105,w195,w222] z) [w38,w55,w91,w105,w204,w220] z) [w38,w55,w91,w105,w220,w263] (n (n z [w38,w55,w91,w105,w222,w248] z) [w38,w55,w91,w105,w222,w271] z)) [w38,w55,w91,w113,w177,w222] (n (n (n z [w38,w55,w91,w119,w177,w205] z) [w38,w55,w91,w120,w177,w205] z) [w38,w55,w91,w121,w173,w205] (n z [w38,w55,w91,w121,w173,w210] z))) [w38,w55,w91,w121,w173,w222] (n (n (n (n z [w38,w55,w91,w121,w173,w251] z) [w38,w55,w91,w121,w173,w296] z) [w38,w55,w91,w121,w173,w329] (n z [w38,w55,w91,w121,w173,w336] z)) [w38,w55,w91,w121,w174,w205] (n (n (n z [w38,w55,w91,w121,w175,w205] z) [w38,w55,w91,w121,w176,w205] z) [w38,w55,w91,w121,w177,w204] (n z [w38,w55,w91,w121,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5babaaab : t5babaaab.all (blocked 4 t4) = true := by
  decide +kernel
def t5babaaa := (n t5babaaaa [w38,w55,w91,w105,w192,w222] t5babaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5babaaa : t5babaaa.all (blocked 4 t4) = true := by
  simp only [t5babaaa, ReplayTree.all, n, ht5babaaaa, ht5babaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5babaaba := (n (n (n (n (n z [w38,w55,w91,w121,w177,w207] z) [w38,w55,w91,w121,w177,w208] z) [w38,w55,w91,w121,w177,w211] (n (n z [w38,w55,w91,w121,w177,w213] z) [w38,w55,w91,w121,w177,w222] z)) [w38,w55,w91,w121,w177,w229] (n (n (n z [w38,w55,w91,w121,w177,w249] z) [w38,w55,w91,w121,w177,w292] z) [w38,w55,w91,w121,w177,w296] (n z [w38,w55,w91,w121,w177,w301] z))) [w38,w55,w91,w121,w177,w307] (n (n (n (n z [w38,w55,w91,w121,w178,w205] z) [w38,w55,w91,w121,w179,w205] z) [w38,w55,w91,w121,w180,w205] (n (n z [w38,w55,w91,w121,w181,w205] z) [w38,w55,w91,w121,w183,w205] z)) [w38,w55,w91,w121,w189,w205] (n (n (n z [w38,w55,w91,w121,w192,w205] z) [w38,w55,w91,w121,w195,w205] z) [w38,w55,w91,w121,w195,w222] (n z [w38,w55,w91,w121,w204] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5babaaba : t5babaaba.all (blocked 4 t4) = true := by
  decide +kernel
def t5babaabb := (n (n (n (n (n z [w38,w55,w91,w121,w204,w263] z) [w38,w55,w91,w121,w205,w209] z) [w38,w55,w91,w121,w205,w226] (n (n z [w38,w55,w91,w121,w205,w232] z) [w38,w55,w91,w121,w205,w234] z)) [w38,w55,w91,w121,w205,w238] (n (n (n z [w38,w55,w91,w121,w205,w248] z) [w38,w55,w91,w121,w205,w260] z) [w38,w55,w91,w121,w205,w263] (n z [w38,w55,w91,w121,w205,w265] z))) [w38,w55,w91,w121,w205,w271] (n (n (n (n z [w38,w55,w91,w121,w205,w279] z) [w38,w55,w91,w121,w205,w287] z) [w38,w55,w91,w121,w205,w309] (n z [w38,w55,w91,w121,w205,w313] z)) [w38,w55,w91,w121,w205,w321] (n (n (n z [w38,w55,w91,w121,w205,w352] z) [w38,w55,w91,w121,w205,w357] z) [w38,w55,w91,w121,w222,w238] (n z [w38,w55,w91,w121,w222,w263] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5babaabb : t5babaabb.all (blocked 4 t4) = true := by
  decide +kernel
def t5babaab := (n t5babaaba [w38,w55,w91,w121,w204,w205] t5babaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5babaab : t5babaab.all (blocked 4 t4) = true := by
  simp only [t5babaab, ReplayTree.all, n, ht5babaaba, ht5babaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5babaa := (n t5babaaa [w38,w55,w91,w121,w177,w206] t5babaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5babaa : t5babaa.all (blocked 4 t4) = true := by
  simp only [t5babaa, ReplayTree.all, n, ht5babaaa, ht5babaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bababaa := (n (n (n (n (n z [w38,w55,w91,w121,w296,w313] z) [w38,w55,w91,w127,w177,w205] z) [w38,w55,w91,w151,w177,w205] (n (n z [w38,w55,w91,w173,w205,w322] z) [w38,w55,w91,w177,w205,w322] z)) [w38,w55,w91,w198,w205,w309] (n (n (n z [w38,w55,w91,w205,w309,w322] z) [w38,w55,w92,w121,w177,w205] z) [w38,w55,w93,w105,w177,w205] (n z [w38,w55,w93,w121,w177,w205] z))) [w38,w55,w94,w105,w195,w292] (n (n (n (n z [w38,w55,w94,w105,w205,w288] z) [w38,w55,w95,w105,w200,w205] z) [w38,w55,w95,w120,w177,w205] (n (n z [w38,w55,w95,w121,w177,w205] z) [w38,w55,w97,w121,w177,w205] z)) [w38,w55,w98,w121,w177,w205] (n (n (n z [w38,w55,w100,w105,w195,w222] z) [w38,w55,w102,w121,w177,w205] z) [w38,w55,w103,w105,w195,w222] (n z [w38,w55,w103,w114,w177,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bababaa : t5bababaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5bababab := (n (n (n (n (n z [w38,w55,w103,w158,w195,w222] z) [w38,w55,w103,w177,w195,w222] z) [w38,w55,w103,w195,w205,w222] (n (n z [w38,w55,w103,w195,w222] z) [w38,w55,w104,w105,w195,w222] z)) [w38,w55,w105,w114,w177,w222] (n (n (n z [w38,w55,w105,w128,w195,w222] z) [w38,w55,w105,w131,w195,w222] z) [w38,w55,w105,w134,w184,w222] (n z [w38,w55,w105,w134,w189,w222] z))) [w38,w55,w105,w134,w192,w222] (n (n (n (n z [w38,w55,w105,w134,w195,w222] z) [w38,w55,w105,w134,w222,w248] z) [w38,w55,w105,w134,w222,w271] (n z [w38,w55,w105,w142,w177,w222] z)) [w38,w55,w105,w144,w195,w222] (n (n (n z [w38,w55,w105,w144,w222,w248] z) [w38,w55,w105,w156,w195,w222] z) [w38,w55,w105,w158,w184,w222] (n z [w38,w55,w105,w158,w189,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bababab : t5bababab.all (blocked 4 t4) = true := by
  decide +kernel
def t5bababa := (n t5bababaa [w38,w55,w103,w119,w195,w205] t5bababab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bababa : t5bababa.all (blocked 4 t4) = true := by
  simp only [t5bababa, ReplayTree.all, n, ht5bababaa, ht5bababab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bababba := (n (n (n (n (n z [w38,w55,w105,w158,w195,w222] z) [w38,w55,w105,w158,w222,w248] z) [w38,w55,w105,w158,w222,w271] (n (n z [w38,w55,w105,w161,w195,w222] z) [w38,w55,w105,w165,w177,w222] z)) [w38,w55,w105,w166,w195,w222] (n (n (n z [w38,w55,w105,w166,w222,w271] z) [w38,w55,w105,w184,w222,w284] z) [w38,w55,w105,w184,w222,w296] (n z [w38,w55,w105,w189,w198,w296] z))) [w38,w55,w105,w189,w222,w278] (n (n (n (n z [w38,w55,w105,w189,w222,w286] z) [w38,w55,w105,w189,w222,w296] z) [w38,w55,w105,w192,w222,w296] (n (n z [w38,w55,w105,w195,w198,w296] z) [w38,w55,w105,w195,w222,w278] z)) [w38,w55,w105,w195,w222,w284] (n (n (n z [w38,w55,w105,w195,w222,w292] z) [w38,w55,w105,w195,w222,w296] z) [w38,w55,w105,w195,w222,w304] (n z [w38,w55,w105,w195,w222,w349] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bababba : t5bababba.all (blocked 4 t4) = true := by
  decide +kernel
def t5bababbb := (n (n (n (n (n z [w38,w55,w105,w195,w292,w305] z) [w38,w55,w105,w198,w205,w286] z) [w38,w55,w105,w222,w248,w296] (n (n z [w38,w55,w105,w222,w271,w296] z) [w38,w55,w111,w121,w177,w205] z)) [w38,w55,w112,w121,w177,w205] (n (n (n z [w38,w55,w114,w119,w177,w205] z) [w38,w55,w114,w121,w177,w205] z) [w38,w55,w115,w121,w177,w205] (n z [w38,w55,w119,w158,w195,w205] z))) [w38,w55,w119,w166,w177,w205] (n (n (n (n z [w38,w55,w120,w144,w177,w205] z) [w38,w55,w121,w134,w189,w205] z) [w38,w55,w121,w134,w195,w222] (n z [w38,w55,w121,w136,w177,w205] z)) [w38,w55,w121,w137,w177,w205] (n (n (n z [w38,w55,w121,w139,w177,w205] z) [w38,w55,w121,w142,w177,w205] z) [w38,w55,w121,w144,w173,w205] (n z [w38,w55,w121,w144,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bababbb : t5bababbb.all (blocked 4 t4) = true := by
  decide +kernel
def t5bababb := (n t5bababba [w38,w55,w105,w195,w222,w355] t5bababbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bababb : t5bababb.all (blocked 4 t4) = true := by
  simp only [t5bababb, ReplayTree.all, n, ht5bababba, ht5bababbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5babab := (n t5bababa [w38,w55,w105,w158,w192,w222] t5bababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5babab : t5babab.all (blocked 4 t4) = true := by
  simp only [t5babab, ReplayTree.all, n, ht5bababa, ht5bababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5baba := (n t5babaa [w38,w55,w91,w121,w263,w296] t5babab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5baba : t5baba.all (blocked 4 t4) = true := by
  simp only [t5baba, ReplayTree.all, n, ht5babaa, ht5babab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5babbaaa := (n (n (n (n (n z [w38,w55,w121,w144,w177,w296] z) [w38,w55,w121,w144,w195,w205] z) [w38,w55,w121,w144,w205,w238] (n (n z [w38,w55,w121,w144,w205,w248] z) [w38,w55,w121,w144,w205,w263] z)) [w38,w55,w121,w144,w205,w313] (n (n (n z [w38,w55,w121,w158,w189,w205] z) [w38,w55,w121,w158,w195,w222] z) [w38,w55,w121,w162,w177,w205] (n z [w38,w55,w121,w163,w177,w205] z))) [w38,w55,w121,w165,w177,w205] (n (n (n (n z [w38,w55,w121,w166,w173,w205] z) [w38,w55,w121,w166,w177,w205] z) [w38,w55,w121,w166,w177,w222] (n (n z [w38,w55,w121,w166,w177,w296] z) [w38,w55,w121,w166,w195,w205] z)) [w38,w55,w121,w166,w205,w238] (n (n (n z [w38,w55,w121,w166,w205,w263] z) [w38,w55,w121,w166,w205,w271] z) [w38,w55,w121,w166,w205,w313] (n z [w38,w55,w121,w172,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5babbaaa : t5babbaaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5babbaab := (n (n (n (n (n z [w38,w55,w121,w177,w205,w286] z) [w38,w55,w121,w189,w205,w278] z) [w38,w55,w121,w189,w205,w286] (n (n z [w38,w55,w158,w195,w222,w313] z) [w38,w55,w195,w222,w296,w313] z)) [w38,w56,w73,w105,w195,w222] (n (n (n z [w38,w56,w91,w121,w177,w205] z) [w38,w57,w73,w105,w195,w222] z) [w38,w57,w91,w121,w177,w205] (n z [w38,w58,w73,w105,w195,w222] z))) [w38,w58,w91,w121,w177,w205] (n (n (n (n z [w38,w60,w69,w105,w177,w222] z) [w38,w60,w69,w121,w177,w205] z) [w38,w60,w73,w105,w173,w222] (n z [w38,w60,w73,w105,w177,w222] z)) [w38,w60,w73,w105,w192,w222] (n (n (n z [w38,w60,w73,w105,w195,w222] z) [w38,w60,w73,w105,w222,w238] z) [w38,w60,w73,w105,w222,w263] (n z [w38,w60,w73,w105,w222,w270] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5babbaab : t5babbaab.all (blocked 4 t4) = true := by
  decide +kernel
def t5babbaa := (n t5babbaaa [w38,w55,w121,w173,w205,w286] t5babbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5babbaa : t5babbaa.all (blocked 4 t4) = true := by
  simp only [t5babbaa, ReplayTree.all, n, ht5babbaaa, ht5babbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5babbaba := (n (n (n (n (n z [w38,w60,w73,w121,w173,w205] z) [w38,w60,w73,w121,w177,w205] z) [w38,w60,w73,w121,w177,w213] (n (n z [w38,w60,w73,w121,w177,w222] z) [w38,w60,w73,w121,w177,w296] z)) [w38,w60,w73,w121,w192,w205] (n (n (n z [w38,w60,w73,w121,w195,w205] z) [w38,w60,w73,w121,w205,w238] z) [w38,w60,w73,w121,w205,w263] (n z [w38,w60,w73,w121,w205,w270] z))) [w38,w60,w73,w121,w205,w313] (n (n (n (n z [w38,w60,w73,w177,w222,w313] z) [w38,w60,w73,w205,w222,w313] z) [w38,w60,w84,w105,w177,w222] (n (n z [w38,w60,w84,w121,w177,w205] z) [w38,w60,w91,w105,w177,w222] z)) [w38,w60,w91,w121,w177,w205] (n (n (n z [w38,w60,w105,w121,w177,w296] z) [w38,w60,w105,w134,w177,w222] z) [w38,w60,w105,w158,w177,w222] (n z [w38,w60,w105,w163,w177,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5babbaba : t5babbaba.all (blocked 4 t4) = true := by
  decide +kernel
def t5babbabb := (n (n (n (n (n z [w38,w60,w121,w134,w177,w205] z) [w38,w60,w121,w158,w177,w205] z) [w38,w60,w121,w163,w177,w205] (n (n z [w38,w61,w73,w105,w177,w222] z) [w38,w61,w73,w121,w177,w205] z)) [w38,w62,w73,w105,w177,w222] (n (n (n z [w38,w62,w73,w121,w177,w205] z) [w38,w63,w69,w105,w173,w222] z) [w38,w63,w69,w105,w177,w222] (n z [w38,w63,w69,w105,w177,w305] z))) [w38,w63,w69,w105,w195,w222] (n (n (n (n z [w38,w63,w69,w105,w222,w238] z) [w38,w63,w69,w105,w222,w263] z) [w38,w63,w69,w105,w222,w271] (n z [w38,w63,w69,w105,w222,w279] z)) [w38,w63,w69,w121,w173,w205] (n (n (n z [w38,w63,w69,w121,w177,w205] z) [w38,w63,w69,w121,w177,w222] z) [w38,w63,w69,w121,w177,w292] (n z [w38,w63,w69,w121,w195,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5babbabb : t5babbabb.all (blocked 4 t4) = true := by
  decide +kernel
def t5babbab := (n t5babbaba [w38,w60,w105,w177,w222,w296] t5babbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5babbab : t5babbab.all (blocked 4 t4) = true := by
  simp only [t5babbab, ReplayTree.all, n, ht5babbaba, ht5babbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5babba := (n t5babbaa [w38,w60,w73,w113,w177,w222] t5babbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5babba : t5babba.all (blocked 4 t4) = true := by
  simp only [t5babba, ReplayTree.all, n, ht5babbaa, ht5babbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5babbbaa := (n (n (n (n (n z [w38,w63,w69,w121,w205,w263] z) [w38,w63,w69,w121,w205,w271] z) [w38,w63,w69,w121,w205,w279] (n (n z [w38,w63,w69,w121,w205,w313] z) [w38,w63,w69,w149,w177,w222] z)) [w38,w63,w69,w177,w205,w336] (n (n (n z [w38,w63,w69,w177,w222,w329] z) [w38,w63,w69,w177,w222,w336] z) [w38,w63,w70,w105,w177,w222] (n z [w38,w63,w70,w121,w177,w205] z))) [w38,w63,w71,w105,w177,w222] (n (n (n (n z [w38,w63,w71,w121,w177,w205] z) [w38,w63,w72,w105,w177,w222] z) [w38,w63,w72,w121,w177,w205] (n (n z [w38,w63,w73,w103,w177,w222] z) [w38,w63,w73,w105,w121,w204] z)) [w38,w63,w73,w105,w173,w222] (n (n (n z [w38,w63,w73,w105,w173,w336] z) [w38,w63,w73,w105,w174,w222] z) [w38,w63,w73,w105,w175,w222] (n z [w38,w63,w73,w105,w176,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5babbbaa : t5babbbaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5babbbab := (n (n (n (n (n z [w38,w63,w73,w105,w177,w221] z) [w38,w63,w73,w105,w177,w222] z) [w38,w63,w73,w105,w177,w231] (n (n z [w38,w63,w73,w105,w177,w254] z) [w38,w63,w73,w105,w177,w305] z)) [w38,w63,w73,w105,w179,w222] (n (n (n z [w38,w63,w73,w105,w180,w222] z) [w38,w63,w73,w105,w181,w222] z) [w38,w63,w73,w105,w182,w222] (n z [w38,w63,w73,w105,w183,w222] z))) [w38,w63,w73,w105,w184,w222] (n (n (n (n z [w38,w63,w73,w105,w189,w222] z) [w38,w63,w73,w105,w192,w222] z) [w38,w63,w73,w105,w195,w222] (n z [w38,w63,w73,w105,w204,w220] z)) [w38,w63,w73,w105,w204,w222] (n (n (n z [w38,w63,w73,w105,w209,w222] z) [w38,w63,w73,w105,w212,w222] z) [w38,w63,w73,w105,w216,w222] (n z [w38,w63,w73,w105,w220,w263] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5babbbab : t5babbbab.all (blocked 4 t4) = true := by
  decide +kernel
def t5babbba := (n t5babbbaa [w38,w63,w73,w105,w177,w220] t5babbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5babbba : t5babbba.all (blocked 4 t4) = true := by
  simp only [t5babbba, ReplayTree.all, n, ht5babbbaa, ht5babbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5babbbba := (n (n (n (n (n z [w38,w63,w73,w105,w222,w226] z) [w38,w63,w73,w105,w222,w232] z) [w38,w63,w73,w105,w222,w234] (n (n z [w38,w63,w73,w105,w222,w238] z) [w38,w63,w73,w105,w222,w248] z)) [w38,w63,w73,w105,w222,w260] (n (n (n z [w38,w63,w73,w105,w222,w263] z) [w38,w63,w73,w105,w222,w265] z) [w38,w63,w73,w105,w222,w268] (n z [w38,w63,w73,w105,w222,w271] z))) [w38,w63,w73,w105,w222,w276] (n (n (n (n z [w38,w63,w73,w105,w222,w279] z) [w38,w63,w73,w106,w177,w222] z) [w38,w63,w73,w108,w177,w222] (n (n z [w38,w63,w73,w110,w177,w222] z) [w38,w63,w73,w113,w177,w222] z)) [w38,w63,w73,w119,w177,w205] (n (n (n z [w38,w63,w73,w120,w177,w205] z) [w38,w63,w73,w121,w173,w205] z) [w38,w63,w73,w121,w173,w222] (n z [w38,w63,w73,w121,w173,w251] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5babbbba : t5babbbba.all (blocked 4 t4) = true := by
  decide +kernel
def t5babbbbb := (n (n (n (n (n z [w38,w63,w73,w121,w173,w336] z) [w38,w63,w73,w121,w174,w205] z) [w38,w63,w73,w121,w175,w205] (n (n z [w38,w63,w73,w121,w176,w205] z) [w38,w63,w73,w121,w177,w204] z)) [w38,w63,w73,w121,w177,w205] (n (n (n z [w38,w63,w73,w121,w177,w206] z) [w38,w63,w73,w121,w177,w207] z) [w38,w63,w73,w121,w177,w211] (n z [w38,w63,w73,w121,w177,w213] z))) [w38,w63,w73,w121,w177,w222] (n (n (n (n z [w38,w63,w73,w121,w177,w229] z) [w38,w63,w73,w121,w177,w230] z) [w38,w63,w73,w121,w177,w249] (n z [w38,w63,w73,w121,w177,w292] z)) [w38,w63,w73,w121,w178,w205] (n (n (n z [w38,w63,w73,w121,w179,w205] z) [w38,w63,w73,w121,w180,w205] z) [w38,w63,w73,w121,w181,w205] (n z [w38,w63,w73,w121,w183,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5babbbbb : t5babbbbb.all (blocked 4 t4) = true := by
  decide +kernel
def t5babbbb := (n t5babbbba [w38,w63,w73,w121,w173,w329] t5babbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5babbbb : t5babbbb.all (blocked 4 t4) = true := by
  simp only [t5babbbb, ReplayTree.all, n, ht5babbbba, ht5babbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5babbb := (n t5babbba [w38,w63,w73,w105,w220,w271] t5babbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5babbb : t5babbb.all (blocked 4 t4) = true := by
  simp only [t5babbb, ReplayTree.all, n, ht5babbba, ht5babbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5babb := (n t5babba [w38,w63,w69,w121,w205,w238] t5babbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5babb : t5babb.all (blocked 4 t4) = true := by
  simp only [t5babb, ReplayTree.all, n, ht5babba, ht5babbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bab := (n t5baba [w38,w55,w121,w144,w177,w222] t5babb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bab : t5bab.all (blocked 4 t4) = true := by
  simp only [t5bab, ReplayTree.all, n, ht5baba, ht5babb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5ba := (n t5baa [w38,w55,w87,w121,w177,w222] t5bab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5ba : t5ba.all (blocked 4 t4) = true := by
  simp only [t5ba, ReplayTree.all, n, ht5baa, ht5bab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbaaaaa := (n (n (n (n (n z [w38,w63,w73,w121,w192,w205] z) [w38,w63,w73,w121,w195,w205] z) [w38,w63,w73,w121,w195,w222] (n (n z [w38,w63,w73,w121,w204] z) [w38,w63,w73,w121,w204,w205] z)) [w38,w63,w73,w121,w204,w263] (n (n (n z [w38,w63,w73,w121,w204,w271] z) [w38,w63,w73,w121,w205,w209] z) [w38,w63,w73,w121,w205,w226] (n z [w38,w63,w73,w121,w205,w227] z))) [w38,w63,w73,w121,w205,w232] (n (n (n (n z [w38,w63,w73,w121,w205,w234] z) [w38,w63,w73,w121,w205,w238] z) [w38,w63,w73,w121,w205,w248] (n (n z [w38,w63,w73,w121,w205,w260] z) [w38,w63,w73,w121,w205,w263] z)) [w38,w63,w73,w121,w205,w265] (n (n (n z [w38,w63,w73,w121,w205,w268] z) [w38,w63,w73,w121,w205,w271] z) [w38,w63,w73,w121,w205,w276] (n z [w38,w63,w73,w121,w205,w279] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbaaaaa : t5bbaaaaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbaaaab := (n (n (n (n (n z [w38,w63,w73,w121,w205,w313] z) [w38,w63,w73,w121,w205,w321] z) [w38,w63,w73,w121,w205,w352] (n (n z [w38,w63,w73,w121,w205,w357] z) [w38,w63,w73,w121,w205,w365] z)) [w38,w63,w73,w121,w222,w238] (n (n (n z [w38,w63,w73,w121,w222,w263] z) [w38,w63,w73,w121,w222,w271] z) [w38,w63,w73,w121,w263,w296] (n z [w38,w63,w73,w125,w177,w222] z))) [w38,w63,w73,w126,w177,w222] (n (n (n (n z [w38,w63,w73,w127,w177,w205] z) [w38,w63,w73,w146,w177,w222] z) [w38,w63,w73,w151,w177,w205] (n z [w38,w63,w73,w173,w205,w322] z)) [w38,w63,w73,w173,w222,w309] (n (n (n z [w38,w63,w73,w177,w205,w322] z) [w38,w63,w73,w177,w222,w309] z) [w38,w63,w73,w198,w205,w309] (n z [w38,w63,w73,w205,w222,w309] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbaaaab : t5bbaaaab.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbaaaa := (n t5bbaaaaa [w38,w63,w73,w121,w205,w309] t5bbaaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbaaaa : t5bbaaaa.all (blocked 4 t4) = true := by
  simp only [t5bbaaaa, ReplayTree.all, n, ht5bbaaaaa, ht5bbaaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbaaaba := (n (n (n (n (n z [w38,w63,w73,w205,w313,w336] z) [w38,w63,w73,w222,w261,w313] z) [w38,w63,w74,w105,w177,w222] (n (n z [w38,w63,w75,w105,w177,w222] z) [w38,w63,w75,w121,w177,w205] z)) [w38,w63,w76,w105,w177,w222] (n (n (n z [w38,w63,w76,w121,w177,w205] z) [w38,w63,w77,w105,w177,w222] z) [w38,w63,w77,w121,w177,w205] (n z [w38,w63,w78,w121,w177,w205] z))) [w38,w63,w79,w105,w177,w222] (n (n (n (n z [w38,w63,w79,w121,w177,w205] z) [w38,w63,w80,w121,w177,w205] z) [w38,w63,w84,w105,w177,w222] (n (n z [w38,w63,w84,w121,w177,w205] z) [w38,w63,w87,w105,w177,w222] z)) [w38,w63,w87,w121,w177,w205] (n (n (n z [w38,w63,w91,w105,w173,w222] z) [w38,w63,w91,w105,w177,w222] z) [w38,w63,w91,w105,w195,w222] (n z [w38,w63,w91,w105,w222,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbaaaba : t5bbaaaba.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbaaabb := (n (n (n (n (n z [w38,w63,w91,w105,w222,w271] z) [w38,w63,w91,w121,w173,w205] z) [w38,w63,w91,w121,w177,w205] (n (n z [w38,w63,w91,w121,w177,w222] z) [w38,w63,w91,w121,w195,w205] z)) [w38,w63,w91,w121,w205,w238] (n (n (n z [w38,w63,w91,w121,w205,w263] z) [w38,w63,w91,w121,w205,w271] z) [w38,w63,w91,w121,w205,w313] (n z [w38,w63,w94,w105,w177,w292] z))) [w38,w63,w94,w105,w205,w279] (n (n (n (n z [w38,w63,w100,w105,w177,w222] z) [w38,w63,w100,w121,w177,w205] z) [w38,w63,w101,w105,w177,w222] (n z [w38,w63,w103,w105,w177,w222] z)) [w38,w63,w103,w119,w177,w205] (n (n (n z [w38,w63,w103,w121,w177,w205] z) [w38,w63,w103,w158,w177,w222] z) [w38,w63,w103,w166,w177,w222] (n z [w38,w63,w103,w177,w205,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbaaabb : t5bbaaabb.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbaaab := (n t5bbaaaba [w38,w63,w91,w105,w222,w263] t5bbaaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbaaab : t5bbaaab.all (blocked 4 t4) = true := by
  simp only [t5bbaaab, ReplayTree.all, n, ht5bbaaaba, ht5bbaaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbaaa := (n t5bbaaaa [w38,w63,w73,w205,w309,w322] t5bbaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbaaa : t5bbaaa.all (blocked 4 t4) = true := by
  simp only [t5bbaaa, ReplayTree.all, n, ht5bbaaaa, ht5bbaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbaabaa := (n (n (n (n (n z [w38,w63,w104,w105,w177,w222] z) [w38,w63,w104,w121,w177,w205] z) [w38,w63,w105,w121,w177,w292] (n (n z [w38,w63,w105,w121,w263,w296] z) [w38,w63,w105,w128,w177,w222] z)) [w38,w63,w105,w131,w177,w222] (n (n (n z [w38,w63,w105,w134,w173,w222] z) [w38,w63,w105,w134,w177,w222] z) [w38,w63,w105,w134,w195,w222] (n z [w38,w63,w105,w134,w222,w238] z))) [w38,w63,w105,w134,w222,w263] (n (n (n (n z [w38,w63,w105,w134,w222,w271] z) [w38,w63,w105,w144,w177,w222] z) [w38,w63,w105,w156,w177,w222] (n (n z [w38,w63,w105,w158,w173,w222] z) [w38,w63,w105,w158,w177,w222] z)) [w38,w63,w105,w158,w195,w222] (n (n (n z [w38,w63,w105,w158,w222,w238] z) [w38,w63,w105,w158,w222,w263] z) [w38,w63,w105,w158,w222,w271] (n z [w38,w63,w105,w161,w177,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbaabaa : t5bbaabaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbaabab := (n (n (n (n (n z [w38,w63,w105,w166,w173,w222] z) [w38,w63,w105,w166,w177,w222] z) [w38,w63,w105,w166,w195,w222] (n (n z [w38,w63,w105,w166,w222,w238] z) [w38,w63,w105,w166,w222,w263] z)) [w38,w63,w105,w166,w222,w271] (n (n (n z [w38,w63,w105,w172,w177,w222] z) [w38,w63,w105,w173,w222,w278] z) [w38,w63,w105,w173,w222,w296] (n z [w38,w63,w105,w177,w222,w278] z))) [w38,w63,w105,w177,w222,w292] (n (n (n (n z [w38,w63,w105,w177,w222,w296] z) [w38,w63,w105,w177,w222,w304] z) [w38,w63,w105,w177,w222,w349] (n z [w38,w63,w105,w177,w222,w355] z)) [w38,w63,w105,w177,w222,w362] (n (n (n z [w38,w63,w105,w177,w292,w305] z) [w38,w63,w105,w177,w296,w336] z) [w38,w63,w105,w195,w222,w296] (n z [w38,w63,w105,w198,w205,w278] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbaabab : t5bbaabab.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbaaba := (n t5bbaabaa [w38,w63,w105,w165,w177,w222] t5bbaabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbaaba : t5bbaaba.all (blocked 4 t4) = true := by
  simp only [t5bbaaba, ReplayTree.all, n, ht5bbaabaa, ht5bbaabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbaabba := (n (n (n (n (n z [w38,w63,w105,w222,w263,w296] z) [w38,w63,w105,w222,w271,w296] z) [w38,w63,w105,w222,w296,w313] (n (n z [w38,w63,w111,w121,w177,w205] z) [w38,w63,w112,w121,w177,w205] z)) [w38,w63,w119,w158,w177,w205] (n (n (n z [w38,w63,w119,w166,w177,w205] z) [w38,w63,w121,w128,w177,w205] z) [w38,w63,w121,w131,w177,w205] (n z [w38,w63,w121,w134,w173,w205] z))) [w38,w63,w121,w134,w177,w205] (n (n (n (n z [w38,w63,w121,w134,w177,w222] z) [w38,w63,w121,w134,w195,w205] z) [w38,w63,w121,w134,w205,w238] (n (n z [w38,w63,w121,w134,w205,w263] z) [w38,w63,w121,w134,w205,w271] z)) [w38,w63,w121,w134,w205,w313] (n (n (n z [w38,w63,w121,w144,w177,w205] z) [w38,w63,w121,w156,w177,w205] z) [w38,w63,w121,w158,w173,w205] (n z [w38,w63,w121,w158,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbaabba : t5bbaabba.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbaabbb := (n (n (n (n (n z [w38,w63,w121,w158,w195,w205] z) [w38,w63,w121,w158,w205,w238] z) [w38,w63,w121,w158,w205,w263] (n (n z [w38,w63,w121,w158,w205,w271] z) [w38,w63,w121,w158,w205,w313] z)) [w38,w63,w121,w159,w177,w296] (n (n (n z [w38,w63,w121,w161,w177,w205] z) [w38,w63,w121,w165,w177,w205] z) [w38,w63,w121,w166,w173,w205] (n z [w38,w63,w121,w166,w177,w205] z))) [w38,w63,w121,w166,w177,w222] (n (n (n (n z [w38,w63,w121,w166,w195,w205] z) [w38,w63,w121,w166,w205,w238] z) [w38,w63,w121,w166,w205,w263] (n z [w38,w63,w121,w166,w205,w271] z)) [w38,w63,w121,w166,w205,w313] (n (n (n z [w38,w63,w121,w172,w177,w205] z) [w38,w63,w121,w173,w205,w278] z) [w38,w63,w121,w177,w205,w278] (n z [w38,w63,w121,w205,w296,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbaabbb : t5bbaabbb.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbaabb := (n t5bbaabba [w38,w63,w121,w158,w177,w222] t5bbaabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbaabb : t5bbaabb.all (blocked 4 t4) = true := by
  simp only [t5bbaabb, ReplayTree.all, n, ht5bbaabba, ht5bbaabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbaab := (n t5bbaaba [w38,w63,w105,w222,w238,w296] t5bbaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbaab : t5bbaab.all (blocked 4 t4) = true := by
  simp only [t5bbaab, ReplayTree.all, n, ht5bbaaba, ht5bbaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbaa := (n t5bbaaa [w38,w63,w103,w177,w222] t5bbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbaa : t5bbaa.all (blocked 4 t4) = true := by
  simp only [t5bbaa, ReplayTree.all, n, ht5bbaaa, ht5bbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbabaaa := (n (n (n (n (n z [w38,w63,w158,w205,w222,w313] z) [w38,w64,w73,w105,w177,w221] z) [w38,w64,w73,w105,w177,w222] (n (n z [w38,w64,w73,w105,w200,w205] z) [w38,w64,w73,w120,w177,w205] z)) [w38,w64,w73,w121,w177,w205] (n (n (n z [w38,w64,w95,w105,w177,w205] z) [w38,w65,w73,w105,w222,w271] z) [w38,w65,w73,w121,w205,w271] (n z [w38,w65,w84,w105,w205,w263] z))) [w38,w65,w91,w105,w222,w263] (n (n (n (n z [w38,w65,w91,w121,w205,w263] z) [w38,w65,w105,w158,w192,w205] z) [w38,w65,w105,w158,w195,w222] (n (n z [w38,w65,w105,w166,w177,w222] z) [w38,w65,w121,w158,w195,w205] z)) [w38,w65,w121,w166,w177,w205] (n (n (n z [w38,w66,w73,w105,w177,w222] z) [w38,w66,w73,w121,w177,w205] z) [w38,w67,w73,w105,w222,w271] (n z [w38,w67,w73,w121,w205,w271] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbabaaa : t5bbabaaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbabaab := (n (n (n (n (n z [w38,w67,w121,w166,w177,w205] z) [w38,w69,w105,w156,w195,w222] z) [w38,w69,w105,w165,w177,w222] (n (n z [w38,w69,w121,w165,w177,w205] z) [w38,w73,w91,w121,w205,w260] z)) [w38,w73,w105,w121,w205,w268] (n (n (n z [w38,w73,w105,w156,w195,w222] z) [w38,w73,w105,w158,w222,w271] z) [w38,w73,w105,w165,w177,w222] (n z [w38,w73,w105,w166,w222,w271] z))) [w38,w73,w105,w173,w222,w268] (n (n (n (n z [w38,w73,w105,w177,w222,w266] z) [w38,w73,w105,w177,w222,w268] z) [w38,w73,w105,w184,w222,w266] (n z [w38,w73,w105,w189,w222,w260] z)) [w38,w73,w105,w189,w222,w268] (n (n (n z [w38,w73,w105,w195,w222,w260] z) [w38,w73,w105,w195,w222,w266] z) [w38,w73,w105,w198,w205,w268] (n z [w38,w73,w105,w205,w222,w266] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbabaab : t5bbabaab.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbabaa := (n t5bbabaaa [w38,w67,w105,w166,w177,w222] t5bbabaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbabaa : t5bbabaa.all (blocked 4 t4) = true := by
  simp only [t5bbabaa, ReplayTree.all, n, ht5bbabaaa, ht5bbabaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbababa := (n (n (n (n (n z [w38,w73,w105,w222,w260,w268] z) [w38,w73,w105,w222,w261,w271] z) [w38,w73,w105,w222,w266] (n (n z [w38,w73,w105,w222,w268] z) [w38,w73,w105,w222,w269,w271] z)) [w38,w73,w105,w222,w271,w273] (n (n (n z [w38,w73,w105,w222,w271,w275] z) [w38,w73,w121,w162,w177,w205] z) [w38,w73,w121,w165,w177,w205] (n z [w38,w73,w121,w166,w205,w263] z))) [w38,w73,w121,w166,w205,w271] (n (n (n (n z [w38,w73,w121,w173,w205,w268] z) [w38,w73,w121,w177,w205,w268] z) [w38,w73,w121,w189,w205,w260] (n (n z [w38,w73,w121,w189,w205,w268] z) [w38,w73,w121,w205,w260,w268] z)) [w38,w73,w121,w205,w268] (n (n (n z [w38,w73,w121,w205,w269,w271] z) [w38,w80,w121,w162,w177,w205] z) [w38,w87,w105,w156,w177,w222] (n z [w38,w87,w105,w165,w177,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbababa : t5bbababa.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbababb := (n (n (n (n (n z [w38,w87,w121,w165,w177,w205] z) [w38,w91,w105,w121,w205,w260] z) [w38,w91,w105,w198,w205,w260] (n (n z [w38,w91,w121,w156,w177,w205] z) [w38,w91,w121,w158,w205,w263] z)) [w38,w91,w121,w162,w177,w205] (n (n (n z [w38,w91,w121,w166,w205,w263] z) [w38,w91,w121,w173,w205,w260] z) [w38,w91,w121,w177,w205,w260] (n z [w38,w91,w121,w205,w260] z))) [w38,w91,w121,w205,w261,w263] (n (n (n (n z [w38,w94,w105,w156,w195,w205] z) [w38,w94,w105,w165,w177,w205] z) [w38,w105,w121,w162,w177,w205] (n z [w38,w105,w121,w165,w177,w205] z)) [w38,w105,w121,w166,w205,w263] (n (n (n z [w38,w105,w121,w166,w205,w271] z) [w38,w105,w156,w165,w177,w222] z) [w38,w105,w156,w177,w195,w222] (n z [w38,w105,w156,w195,w205,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbababb : t5bbababb.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbabab := (n t5bbababa [w38,w87,w121,w156,w177,w205] t5bbababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbabab : t5bbabab.all (blocked 4 t4) = true := by
  simp only [t5bbabab, ReplayTree.all, n, ht5bbababa, ht5bbababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbaba := (n t5bbabaa [w38,w73,w105,w205,w222,w268] t5bbabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbaba : t5bbaba.all (blocked 4 t4) = true := by
  simp only [t5bbaba, ReplayTree.all, n, ht5bbabaa, ht5bbabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbabbaa := (n (n (n (n (n z [w38,w105,w158,w159,w195,w222] z) [w38,w105,w158,w177,w222,w271] z) [w38,w105,w158,w195,w222,w263] (n (n z [w38,w105,w158,w195,w222,w271] z) [w38,w105,w158,w205,w222,w271] z)) [w38,w105,w158,w222,w263,w271] (n (n (n z [w38,w105,w158,w222,w271] z) [w38,w105,w165,w177,w205,w222] z) [w38,w105,w165,w177,w222] (n z [w38,w105,w166,w167,w177,w222] z))) [w38,w105,w166,w177,w222,w271] (n (n (n (n z [w38,w105,w166,w205,w222,w271] z) [w38,w105,w166,w222,w271] z) [w38,w121,w156,w165,w177,w205] (n (n z [w38,w121,w158,w166,w205,w263] z) [w38,w121,w159,w166,w177,w205] z)) [w38,w121,w162,w177,w205] (n (n (n z [w38,w121,w165,w177,w205] z) [w38,w121,w166,w167,w177,w205] z) [w38,w121,w166,w169,w177,w205] (n z [w38,w121,w166,w171,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbabbaa : t5bbabbaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbabbab := (n (n (n (n (n z [w38,w121,w166,w177,w205,w271] z) [w38,w121,w166,w205,w263] z) [w38,w121,w166,w205,w271] (n (n z [w39,w55,w91,w121,w177,w205] z) [w39,w63,w73,w121,w177,w205] z)) [w40,w55,w73,w105,w195,w222] (n (n (n z [w40,w55,w91,w121,w177,w205] z) [w41,w55,w73,w105,w195,w222] z) [w41,w63,w73,w105,w177,w222] (n z [w42,w55,w73,w105,w195,w222] z))) [w42,w55,w91,w121,w177,w205] (n (n (n (n z [w43,w55,w73,w105,w222,w238] z) [w43,w55,w121,w134,w177,w205] z) [w44,w55,w73,w105,w177,w205] (n z [w45,w50,w55,w73,w205,w313] z)) [w45,w50,w55,w105,w177,w296] (n (n (n z [w45,w55,w73,w105,w205,w248] z) [w45,w55,w91,w105,w205,w238] z) [w45,w55,w105,w134,w195,w205] (n z [w45,w55,w105,w144,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbabbab : t5bbabbab.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbabba := (n t5bbabbaa [w38,w121,w166,w177,w205,w263] t5bbabbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbabba : t5bbabba.all (blocked 4 t4) = true := by
  simp only [t5bbabba, ReplayTree.all, n, ht5bbabbaa, ht5bbabbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbabbba := (n (n (n (n (n z [w45,w59,w91,w105,w177,w205] z) [w45,w63,w73,w105,w205,w238] z) [w45,w63,w105,w134,w177,w205] (n (n z [w45,w68,w73,w105,w177,w205] z) [w46,w55,w65,w73,w205,w313] z)) [w46,w55,w65,w105,w177,w296] (n (n (n z [w46,w55,w69,w105,w177,w222] z) [w46,w55,w69,w121,w177,w205] z) [w46,w55,w73,w105,w173,w222] (n z [w46,w55,w73,w105,w177,w221] z))) [w46,w55,w73,w105,w177,w222] (n (n (n (n z [w46,w55,w73,w105,w192,w222] z) [w46,w55,w73,w105,w195,w222] z) [w46,w55,w73,w105,w222,w238] (n (n z [w46,w55,w73,w105,w222,w245] z) [w46,w55,w73,w105,w222,w263] z)) [w46,w55,w73,w113,w177,w222] (n (n (n z [w46,w55,w73,w120,w177,w205] z) [w46,w55,w73,w121,w173,w205] z) [w46,w55,w73,w121,w177,w205] (n z [w46,w55,w73,w121,w177,w213] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbabbba : t5bbabbba.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbabbbb := (n (n (n (n (n z [w46,w55,w73,w121,w177,w296] z) [w46,w55,w73,w121,w192,w205] z) [w46,w55,w73,w121,w195,w205] (n (n z [w46,w55,w73,w121,w205,w238] z) [w46,w55,w73,w121,w205,w245] z)) [w46,w55,w73,w121,w205,w263] (n (n (n z [w46,w55,w73,w121,w205,w313] z) [w46,w55,w73,w177,w222,w313] z) [w46,w55,w73,w205,w222,w313] (n z [w46,w55,w84,w105,w177,w222] z))) [w46,w55,w84,w121,w177,w205] (n (n (n (n z [w46,w55,w91,w105,w177,w222] z) [w46,w55,w91,w121,w177,w205] z) [w46,w55,w105,w121,w177,w296] (n z [w46,w55,w105,w134,w177,w222] z)) [w46,w55,w105,w139,w177,w222] (n (n (n z [w46,w55,w105,w158,w177,w222] z) [w46,w55,w105,w177,w222,w296] z) [w46,w55,w121,w134,w177,w205] (n z [w46,w55,w121,w139,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbabbbb : t5bbabbbb.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbabbb := (n t5bbabbba [w46,w55,w73,w121,w177,w222] t5bbabbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbabbb : t5bbabbb.all (blocked 4 t4) = true := by
  simp only [t5bbabbb, ReplayTree.all, n, ht5bbabbba, ht5bbabbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbabb := (n t5bbabba [w45,w59,w73,w105,w195,w205] t5bbabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbabb : t5bbabb.all (blocked 4 t4) = true := by
  simp only [t5bbabb, ReplayTree.all, n, ht5bbabba, ht5bbabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbab := (n t5bbaba [w38,w105,w156,w195,w222] t5bbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbab : t5bbab.all (blocked 4 t4) = true := by
  simp only [t5bbab, ReplayTree.all, n, ht5bbaba, ht5bbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bba := (n t5bbaa [w38,w63,w158,w177,w222,w313] t5bbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bba : t5bba.all (blocked 4 t4) = true := by
  simp only [t5bba, ReplayTree.all, n, ht5bbaa, ht5bbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbbaaaa := (n (n (n (n (n z [w46,w60,w73,w105,w177,w222] z) [w46,w60,w73,w121,w177,w205] z) [w46,w63,w73,w105,w177,w222] (n (n z [w46,w63,w73,w121,w177,w205] z) [w46,w64,w73,w105,w177,w205] z)) [w46,w65,w73,w105,w205,w263] (n (n (n z [w46,w65,w105,w158,w177,w205] z) [w47,w55,w73,w105,w222,w248] z) [w47,w55,w73,w121,w205,w248] (n z [w47,w55,w91,w105,w222,w238] z))) [w47,w55,w91,w121,w205,w238] (n (n (n (n z [w47,w55,w105,w134,w195,w222] z) [w47,w55,w105,w144,w177,w222] z) [w47,w55,w121,w134,w195,w205] (n (n z [w47,w55,w121,w144,w177,w205] z) [w47,w63,w73,w105,w222,w238] z)) [w47,w63,w73,w121,w205,w238] (n (n (n z [w47,w63,w105,w134,w177,w222] z) [w47,w63,w121,w134,w177,w205] z) [w47,w64,w73,w105,w177,w205] (n z [w47,w66,w73,w105,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbaaaa : t5bbbaaaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbbaaab := (n (n (n (n (n z [w48,w55,w73,w121,w177,w205] z) [w49,w55,w73,w105,w177,w222] z) [w49,w55,w73,w121,w177,w205] (n (n z [w50,w55,w69,w105,w222,w238] z) [w50,w55,w69,w121,w205,w238] z)) [w50,w55,w69,w149,w177,w222] (n (n (n z [w50,w55,w73,w105,w177,w254] z) [w50,w55,w73,w105,w221,w238] z) [w50,w55,w73,w105,w222,w232] (n z [w50,w55,w73,w105,w222,w234] z))) [w50,w55,w73,w105,w222,w238] (n (n (n (n z [w50,w55,w73,w120,w205,w238] z) [w50,w55,w73,w121,w173,w251] z) [w50,w55,w73,w121,w177,w249] (n z [w50,w55,w73,w121,w205,w232] z)) [w50,w55,w73,w121,w205,w234] (n (n (n z [w50,w55,w73,w121,w205,w238] z) [w50,w55,w73,w121,w205,w352] z) [w50,w55,w73,w121,w222,w238] (n z [w50,w55,w73,w146,w177,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbaaab : t5bbbaaab.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbbaaa := (n t5bbbaaaa [w48,w55,w73,w105,w177,w222] t5bbbaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbaaa : t5bbbaaa.all (blocked 4 t4) = true := by
  simp only [t5bbbaaa, ReplayTree.all, n, ht5bbbaaaa, ht5bbbaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbbaaba := (n (n (n (n (n z [w50,w55,w73,w222,w238,w313] z) [w50,w55,w73,w222,w251,w313] z) [w50,w55,w91,w105,w222,w238] (n (n z [w50,w55,w91,w121,w205,w238] z) [w50,w55,w105,w128,w177,w222] z)) [w50,w55,w105,w131,w177,w222] (n (n (n z [w50,w55,w105,w134,w173,w222] z) [w50,w55,w105,w134,w177,w221] z) [w50,w55,w105,w134,w177,w222] (n z [w50,w55,w105,w134,w195,w222] z))) [w50,w55,w105,w134,w222,w238] (n (n (n (n z [w50,w55,w105,w134,w222,w248] z) [w50,w55,w105,w134,w222,w263] z) [w50,w55,w105,w144,w222,w238] (n (n z [w50,w55,w105,w158,w222,w238] z) [w50,w55,w105,w177,w222,w349] z)) [w50,w55,w105,w222,w238,w296] (n (n (n z [w50,w55,w120,w134,w177,w205] z) [w50,w55,w121,w128,w177,w205] z) [w50,w55,w121,w131,w177,w205] (n z [w50,w55,w121,w134,w173,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbaaba : t5bbbaaba.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbbaabb := (n (n (n (n (n z [w50,w55,w121,w134,w177,w222] z) [w50,w55,w121,w134,w177,w296] z) [w50,w55,w121,w134,w195,w205] (n (n z [w50,w55,w121,w134,w205,w238] z) [w50,w55,w121,w134,w205,w248] z)) [w50,w55,w121,w134,w205,w263] (n (n (n z [w50,w55,w121,w134,w205,w313] z) [w50,w55,w121,w144,w205,w238] z) [w50,w55,w121,w149,w177,w296] (n z [w50,w55,w121,w158,w205,w238] z))) [w51,w55,w73,w105,w195,w222] (n (n (n (n z [w51,w55,w91,w121,w177,w205] z) [w51,w63,w73,w105,w177,w222] z) [w51,w63,w73,w121,w177,w205] (n z [w52,w55,w73,w105,w177,w222] z)) [w52,w63,w73,w105,w177,w222] (n (n (n z [w53,w55,w73,w105,w195,w222] z) [w53,w55,w91,w121,w177,w205] z) [w53,w63,w73,w105,w177,w222] (n z [w53,w63,w73,w121,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbaabb : t5bbbaabb.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbbaab := (n t5bbbaaba [w50,w55,w121,w134,w177,w205] t5bbbaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbaab : t5bbbaab.all (blocked 4 t4) = true := by
  simp only [t5bbbaab, ReplayTree.all, n, ht5bbbaaba, ht5bbbaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbbaa := (n t5bbbaaa [w50,w55,w73,w151,w177,w205] t5bbbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbaa : t5bbbaa.all (blocked 4 t4) = true := by
  simp only [t5bbbaa, ReplayTree.all, n, ht5bbbaaa, ht5bbbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbbabaa := (n (n (n (n (n z [w54,w63,w73,w121,w177,w205] z) [w55,w59,w91,w121,w205,w238] z) [w55,w59,w105,w134,w195,w222] (n (n z [w55,w60,w73,w105,w222,w238] z) [w55,w60,w121,w134,w177,w205] z)) [w55,w63,w69,w105,w222,w238] (n (n (n z [w55,w63,w73,w105,w222,w234] z) [w55,w63,w73,w105,w222,w238] z) [w55,w63,w73,w121,w205,w234] (n z [w55,w63,w73,w121,w222,w238] z))) [w55,w63,w73,w222,w238,w313] (n (n (n (n z [w55,w63,w91,w105,w222,w238] z) [w55,w63,w105,w131,w177,w222] z) [w55,w63,w105,w134,w222,w238] (n (n z [w55,w63,w105,w158,w222,w238] z) [w55,w63,w105,w166,w222,w238] z)) [w55,w63,w105,w222,w238,w296] (n (n (n z [w55,w63,w121,w131,w177,w205] z) [w55,w63,w121,w134,w173,w205] z) [w55,w63,w121,w134,w177,w205] (n z [w55,w63,w121,w134,w177,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbabaa : t5bbbabaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbbabab := (n (n (n (n (n z [w55,w63,w121,w134,w195,w205] z) [w55,w63,w121,w134,w205,w238] z) [w55,w63,w121,w134,w205,w263] (n (n z [w55,w63,w121,w134,w205,w271] z) [w55,w63,w121,w134,w205,w313] z)) [w55,w65,w73,w105,w205,w245] (n (n (n z [w55,w65,w84,w105,w205,w238] z) [w55,w65,w91,w105,w222,w238] z) [w55,w65,w91,w121,w205,w238] (n z [w55,w65,w105,w134,w192,w205] z))) [w55,w65,w105,w134,w195,w222] (n (n (n (n z [w55,w65,w105,w139,w177,w205] z) [w55,w65,w121,w134,w195,w205] z) [w55,w68,w73,w105,w222,w238] (n z [w55,w68,w73,w121,w205,w238] z)) [w55,w68,w105,w134,w177,w222] (n (n (n z [w55,w68,w121,w134,w177,w205] z) [w55,w69,w87,w105,w222,w238] z) [w55,w69,w105,w131,w195,w222] (n z [w55,w69,w105,w195,w222,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbabab : t5bbbabab.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbbaba := (n t5bbbabaa [w55,w63,w121,w134,w177,w296] t5bbbabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbaba : t5bbbaba.all (blocked 4 t4) = true := by
  simp only [t5bbbaba, ReplayTree.all, n, ht5bbbabaa, ht5bbbabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbbabba := (n (n (n (n (n z [w55,w73,w87,w105,w222,w238] z) [w55,w73,w91,w121,w205,w234] z) [w55,w73,w91,w121,w222,w238] (n (n z [w55,w73,w105,w131,w195,w222] z) [w55,w73,w105,w134,w222,w248] z)) [w55,w73,w105,w149,w222,w248] (n (n (n z [w55,w73,w105,w177,w222,w241] z) [w55,w73,w105,w177,w222,w245] z) [w55,w73,w105,w184,w222,w238] (n z [w55,w73,w105,w184,w222,w241] z))) [w55,w73,w105,w189,w222,w234] (n (n (n (n z [w55,w73,w105,w189,w222,w238] z) [w55,w73,w105,w192,w222,w238] z) [w55,w73,w105,w192,w222,w245] (n (n z [w55,w73,w105,w195,w222,w234] z) [w55,w73,w105,w195,w222,w238] z)) [w55,w73,w105,w195,w222,w241] (n (n (n z [w55,w73,w105,w197,w205,w238] z) [w55,w73,w105,w197,w222,w238] z) [w55,w73,w105,w199,w222,w238] (n z [w55,w73,w105,w205,w222,w241] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbabba : t5bbbabba.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbbabbb := (n (n (n (n (n z [w55,w73,w105,w221,w238,w248] z) [w55,w73,w105,w222,w234,w244] z) [w55,w73,w105,w222,w238,w245] (n (n z [w55,w73,w105,w222,w238,w248] z) [w55,w73,w105,w222,w238,w271] z)) [w55,w73,w105,w222,w238,w276] (n (n (n z [w55,w73,w105,w222,w241] z) [w55,w73,w105,w222,w245] z) [w55,w73,w105,w222,w246,w248] (n z [w55,w73,w105,w222,w248,w251] z))) [w55,w73,w105,w222,w248,w253] (n (n (n (n z [w55,w73,w105,w222,w248,w256] z) [w55,w73,w105,w222,w248,w258] z) [w55,w73,w105,w222,w248,w340] (n z [w55,w73,w105,w222,w248,w352] z)) [w55,w73,w121,w134,w189,w205] (n (n (n z [w55,w73,w121,w134,w195,w222] z) [w55,w73,w121,w137,w177,w205] z) [w55,w73,w121,w139,w177,w205] (n z [w55,w73,w121,w144,w205,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbabbb : t5bbbabbb.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbbabb := (n t5bbbabba [w55,w73,w105,w205,w222,w245] t5bbbabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbabb : t5bbbabb.all (blocked 4 t4) = true := by
  simp only [t5bbbabb, ReplayTree.all, n, ht5bbbabba, ht5bbbabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbbab := (n t5bbbaba [w55,w69,w105,w222,w238,w248] t5bbbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbab : t5bbbab.all (blocked 4 t4) = true := by
  simp only [t5bbbab, ReplayTree.all, n, ht5bbbaba, ht5bbbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbba := (n t5bbbaa [w54,w55,w73,w121,w177,w205] t5bbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbba : t5bbba.all (blocked 4 t4) = true := by
  simp only [t5bbba, ReplayTree.all, n, ht5bbbaa, ht5bbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbbbaaa := (n (n (n (n (n z [w55,w73,w121,w195,w222,w238] z) [w55,w73,w121,w205,w234,w244] z) [w55,w73,w121,w222,w238,w248] (n (n z [w55,w73,w195,w222,w238,w313] z) [w55,w73,w222,w238,w248,w313] z)) [w55,w80,w121,w134,w177,w205] (n (n (n z [w55,w80,w121,w137,w177,w205] z) [w55,w84,w121,w134,w177,w205] z) [w55,w84,w121,w139,w177,w205] (n z [w55,w87,w94,w105,w205,w238] z))) [w55,w87,w105,w131,w177,w222] (n (n (n (n z [w55,w87,w105,w177,w222,w238] z) [w55,w87,w105,w205,w222,w238] z) [w55,w87,w105,w222,w238] (n (n z [w55,w87,w121,w131,w177,w205] z) [w55,w87,w121,w134,w177,w205] z)) [w55,w91,w94,w105,w205,w238] (n (n (n z [w55,w91,w96,w121,w205,w238] z) [w55,w91,w99,w121,w205,w238] z) [w55,w91,w105,w116,w222,w238] (n z [w55,w91,w105,w121,w205,w234] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbbaaa : t5bbbbaaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbbbaab := (n (n (n (n (n z [w55,w91,w105,w195,w222,w238] z) [w55,w91,w105,w198,w205,w234] z) [w55,w91,w105,w198,w205,w238] (n (n z [w55,w91,w105,w201,w222,w238] z) [w55,w91,w105,w222,w238,w246] z)) [w55,w91,w105,w222,w238,w248] (n (n (n z [w55,w91,w121,w131,w177,w205] z) [w55,w91,w121,w134,w173,w205] z) [w55,w91,w121,w134,w177,w205] (n z [w55,w91,w121,w134,w177,w222] z))) [w55,w91,w121,w134,w177,w296] (n (n (n (n z [w55,w91,w121,w134,w195,w205] z) [w55,w91,w121,w134,w205,w238] z) [w55,w91,w121,w134,w205,w263] (n z [w55,w91,w121,w134,w205,w313] z)) [w55,w91,w121,w137,w177,w205] (n (n (n z [w55,w91,w121,w144,w205,w238] z) [w55,w91,w121,w173,w205,w234] z) [w55,w91,w121,w177,w205,w234] (n z [w55,w91,w121,w177,w222,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbbaab : t5bbbbaab.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbbbaa := (n t5bbbbaaa [w55,w91,w105,w121,w222,w238] t5bbbbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbbaa : t5bbbbaa.all (blocked 4 t4) = true := by
  simp only [t5bbbbaa, ReplayTree.all, n, ht5bbbbaaa, ht5bbbbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbbbaba := (n (n (n (n (n z [w55,w91,w121,w205,w234] z) [w55,w91,w121,w205,w238,w251] z) [w55,w91,w121,w222,w238] (n (n z [w55,w93,w105,w134,w177,w205] z) [w55,w93,w121,w134,w177,w205] z)) [w55,w94,w105,w131,w195,w205] (n (n (n z [w55,w94,w105,w134,w195,w205] z) [w55,w96,w121,w134,w195,w205] z) [w55,w97,w121,w134,w177,w205] (n z [w55,w105,w121,w134,w189,w205] z))) [w55,w105,w121,w134,w195,w222] (n (n (n (n z [w55,w105,w121,w137,w177,w205] z) [w55,w105,w121,w139,w177,w205] z) [w55,w105,w121,w144,w205,w238] (n (n z [w55,w105,w131,w142,w177,w222] z) [w55,w105,w131,w177,w195,w222] z)) [w55,w105,w131,w195,w205,w222] (n (n (n z [w55,w105,w131,w195,w222] z) [w55,w105,w134,w149,w195,w222] z) [w55,w105,w134,w177,w222,w248] (n z [w55,w105,w134,w189,w198,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbbaba : t5bbbbaba.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbbbabb := (n (n (n (n (n z [w55,w105,w134,w195,w201,w222] z) [w55,w105,w134,w195,w203,w222] z) [w55,w105,w134,w195,w222,w238] (n (n z [w55,w105,w134,w195,w222,w248] z) [w55,w105,w134,w205,w222,w248] z)) [w55,w105,w134,w222,w238,w248] (n (n (n z [w55,w105,w134,w222,w248] z) [w55,w105,w158,w195,w222,w238] z) [w55,w105,w158,w222,w238,w248] (n z [w55,w105,w195,w222,w238,w296] z))) [w55,w105,w222,w238,w248,w296] (n (n (n (n z [w55,w120,w134,w144,w177,w205] z) [w55,w121,w131,w142,w177,w205] z) [w55,w121,w134,w139,w177,w205] (n z [w55,w121,w134,w140,w195,w205] z)) [w55,w121,w134,w144,w173,w205] (n (n (n z [w55,w121,w134,w144,w177,w205] z) [w55,w121,w134,w144,w177,w222] z) [w55,w121,w134,w144,w177,w296] (n z [w55,w121,w134,w144,w195,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbbabb : t5bbbbabb.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbbbab := (n t5bbbbaba [w55,w105,w134,w195,w198,w205] t5bbbbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbbab : t5bbbbab.all (blocked 4 t4) = true := by
  simp only [t5bbbbab, ReplayTree.all, n, ht5bbbbaba, ht5bbbbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbbba := (n t5bbbbaa [w55,w91,w121,w205,w222,w238] t5bbbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbba : t5bbbba.all (blocked 4 t4) = true := by
  simp only [t5bbbba, ReplayTree.all, n, ht5bbbbaa, ht5bbbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbbbbaa := (n (n (n (n (n z [w55,w121,w134,w144,w205,w263] z) [w55,w121,w134,w144,w205,w313] z) [w55,w121,w134,w166,w177,w205] (n (n z [w55,w121,w134,w172,w177,w205] z) [w55,w121,w134,w173,w189,w205] z)) [w55,w121,w134,w177,w189,w205] (n (n (n z [w55,w121,w134,w177,w195,w222] z) [w55,w121,w134,w189,w205] z) [w55,w121,w134,w195,w205,w215] (n z [w55,w121,w134,w195,w205,w222] z))) [w55,w121,w134,w195,w222] (n (n (n (n z [w55,w121,w137,w177,w205] z) [w55,w121,w139,w177,w205] z) [w55,w121,w140,w144,w177,w205] (n (n z [w55,w121,w144,w149,w177,w205] z) [w55,w121,w144,w150,w177,w205] z)) [w55,w121,w144,w154,w177,w205] (n (n (n z [w55,w121,w144,w155,w177,w205] z) [w55,w121,w144,w177,w205,w238] z) [w55,w121,w144,w177,w205,w251] (n z [w55,w121,w144,w177,w205,w340] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbbbaa : t5bbbbbaa.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbbbbab := (n (n (n (n (n z [w55,w121,w144,w205,w238] z) [w59,w63,w73,w105,w222,w238] z) [w59,w63,w73,w121,w205,w238] (n (n z [w59,w63,w105,w134,w177,w222] z) [w59,w63,w121,w134,w177,w205] z)) [w60,w73,w105,w177,w222,w238] (n (n (n z [w60,w73,w105,w205,w222,w238] z) [w60,w73,w105,w222,w238] z) [w60,w73,w121,w134,w177,w205] (n z [w60,w105,w121,w134,w177,w205] z))) [w60,w121,w134,w177,w205] (n (n (n (n z [w63,w65,w73,w105,w222,w238] z) [w63,w65,w73,w121,w205,w238] z) [w63,w65,w105,w134,w177,w222] (n z [w63,w65,w121,w134,w177,w205] z)) [w63,w69,w105,w131,w177,w222] (n (n (n z [w63,w69,w121,w131,w177,w205] z) [w63,w73,w105,w121,w205,w234] z) [w63,w73,w105,w131,w177,w222] (n z [w63,w73,w105,w134,w222,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbbbab : t5bbbbbab.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbbbba := (n t5bbbbbaa [w55,w121,w144,w177,w205,w349] t5bbbbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbbba : t5bbbbba.all (blocked 4 t4) = true := by
  simp only [t5bbbbba, ReplayTree.all, n, ht5bbbbbaa, ht5bbbbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbbbbba := (n (n (n (n (n z [w63,w73,w105,w158,w222,w238] z) [w63,w73,w105,w159,w222,w238] z) [w63,w73,w105,w173,w222,w234] (n (n z [w63,w73,w105,w177,w222,w234] z) [w63,w73,w105,w198,w205,w234] z)) [w63,w73,w105,w205,w222,w234] (n (n (n z [w63,w73,w105,w222,w234] z) [w63,w73,w105,w222,w238,w251] z) [w63,w73,w105,w222,w238,w256] (n z [w63,w73,w105,w222,w238,w261] z))) [w63,w73,w105,w222,w238,w273] (n (n (n (n z [w63,w73,w121,w131,w177,w205] z) [w63,w73,w121,w134,w205,w238] z) [w63,w73,w121,w134,w205,w263] (n (n z [w63,w73,w121,w173,w205,w234] z) [w63,w73,w121,w177,w205,w234] z)) [w63,w73,w121,w205,w234] (n (n (n z [w63,w73,w121,w205,w238,w251] z) [w63,w94,w105,w131,w177,w205] z) [w63,w105,w121,w131,w177,w205] (n z [w63,w105,w121,w134,w205,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbbbba : t5bbbbbba.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbbbbbb := (n (n (n (n (n z [w63,w105,w131,w177,w205,w222] z) [w63,w105,w131,w177,w222] z) [w63,w105,w134,w149,w177,w222] (n (n z [w63,w105,w134,w177,w222,w238] z) [w63,w105,w134,w205,w222,w238] z)) [w63,w105,w134,w222,w238] (n (n (n z [w63,w105,w158,w177,w222,w238] z) [w63,w105,w158,w205,w222,w238] z) [w63,w105,w158,w222,w238] (n z [w63,w121,w131,w177,w205] z))) [w63,w121,w134,w149,w177,w205] (n (n (n (n z [w63,w121,w134,w154,w177,w205] z) [w63,w121,w134,w159,w177,w205] z) [w63,w121,w134,w169,w177,w205] (n z [w63,w121,w134,w177,w205,w238] z)) [w63,w121,w134,w177,w205,w251] (n (n (n z [w63,w121,w134,w177,w205,w261] z) [w63,w121,w134,w177,w205,w263] z) [w63,w121,w134,w205,w238] (n z [w63,w121,w134,w205,w263] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbbbbb : t5bbbbbbb.all (blocked 4 t4) = true := by
  decide +kernel
def t5bbbbbb := (n t5bbbbbba [w63,w105,w121,w134,w205,w263] t5bbbbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbbbb : t5bbbbbb.all (blocked 4 t4) = true := by
  simp only [t5bbbbbb, ReplayTree.all, n, ht5bbbbbba, ht5bbbbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbbbb := (n t5bbbbba [w63,w73,w105,w149,w222,w238] t5bbbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbbb : t5bbbbb.all (blocked 4 t4) = true := by
  simp only [t5bbbbb, ReplayTree.all, n, ht5bbbbba, ht5bbbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbbb := (n t5bbbba [w55,w121,w134,w144,w205,w238] t5bbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbbb : t5bbbb.all (blocked 4 t4) = true := by
  simp only [t5bbbb, ReplayTree.all, n, ht5bbbba, ht5bbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bbb := (n t5bbba [w55,w73,w121,w189,w205,w234] t5bbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bbb : t5bbb.all (blocked 4 t4) = true := by
  simp only [t5bbb, ReplayTree.all, n, ht5bbba, ht5bbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5bb := (n t5bba [w46,w55,w121,w158,w177,w205] t5bbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5bb : t5bb.all (blocked 4 t4) = true := by
  simp only [t5bb, ReplayTree.all, n, ht5bba, ht5bbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5b := (n t5ba [w38,w63,w73,w121,w189,w205] t5bb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5b : t5b.all (blocked 4 t4) = true := by
  simp only [t5b, ReplayTree.all, n, ht5ba, ht5bb, Bool.true_and, Bool.and_true]
  decide +kernel
def t5 := (n t5a [w23,w57,w105,w134,w195,w205] t5b)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht5 : t5.all (blocked 4 t4) = true := by
  simp only [t5, ReplayTree.all, n, ht5a, ht5b, Bool.true_and, Bool.and_true]
  decide +kernel
lemma s5 : sound 5 t5 := layer_sound s4 ht5
def t6aaaaaaa := (n (n (n (n (n z [w0,w17,w23,w38,w55,w296,w313] z) [w0,w17,w55,w73,w105,w222,w238] z) [w0,w17,w55,w121,w134,w177,w205] (n (n z [w0,w23,w55,w91,w105,w205,w238] z) [w0,w23,w55,w105,w134,w195,w205] z)) [w0,w38,w55,w73,w105,w195,w222] (n (n (n z [w0,w38,w55,w91,w121,w177,w205] z) [w0,w38,w63,w73,w105,w177,w222] z) [w0,w38,w63,w73,w121,w177,w205] (n (n z [w1,w17,w23,w38,w55,w296,w313] z) [w1,w17,w55,w73,w105,w222,w238] z))) [w1,w17,w55,w121,w134,w177,w205] (n (n (n (n z [w1,w23,w55,w91,w105,w205,w238] z) [w1,w23,w55,w105,w134,w195,w205] z) [w1,w38,w55,w73,w105,w195,w222] (n (n z [w1,w38,w55,w91,w121,w177,w205] z) [w1,w38,w63,w73,w105,w177,w222] z)) [w1,w38,w63,w73,w121,w177,w205] (n (n (n z [w2,w17,w23,w38,w55,w296,w313] z) [w2,w17,w55,w73,w105,w222,w238] z) [w2,w17,w55,w121,w134,w177,w205] (n z [w2,w23,w55,w91,w105,w205,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaaaaaa : t6aaaaaaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6aaaaaab := (n (n (n (n (n z [w2,w38,w55,w73,w105,w195,w222] z) [w2,w38,w55,w91,w121,w177,w205] z) [w2,w38,w63,w73,w105,w177,w222] (n (n z [w2,w38,w63,w73,w121,w177,w205] z) [w3,w17,w23,w38,w55,w296,w313] z)) [w3,w17,w55,w73,w105,w222,w238] (n (n (n z [w3,w17,w55,w121,w134,w177,w205] z) [w3,w23,w55,w91,w105,w205,w238] z) [w3,w23,w55,w105,w134,w195,w205] (n (n z [w3,w38,w55,w73,w105,w195,w222] z) [w3,w38,w55,w91,w121,w177,w205] z))) [w3,w38,w63,w73,w105,w177,w222] (n (n (n (n z [w3,w38,w63,w73,w121,w177,w205] z) [w4,w17,w23,w38,w55,w296,w313] z) [w4,w17,w55,w73,w105,w222,w238] (n (n z [w4,w17,w55,w121,w134,w177,w205] z) [w4,w23,w55,w91,w105,w205,w238] z)) [w4,w23,w55,w105,w134,w195,w205] (n (n (n z [w4,w38,w55,w73,w105,w195,w222] z) [w4,w38,w55,w91,w121,w177,w205] z) [w4,w38,w63,w73,w105,w177,w222] (n z [w4,w38,w63,w73,w121,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaaaaab : t6aaaaaab.all (blocked 5 t5) = true := by
  decide +kernel
def t6aaaaaa := (n t6aaaaaaa [w2,w23,w55,w105,w134,w195,w205] t6aaaaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaaaaa : t6aaaaaa.all (blocked 5 t5) = true := by
  simp only [t6aaaaaa, ReplayTree.all, n, ht6aaaaaaa, ht6aaaaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aaaaaba := (n (n (n (n (n z [w5,w17,w55,w73,w105,w222,w238] z) [w5,w17,w55,w121,w134,w177,w205] z) [w5,w23,w55,w91,w105,w205,w238] (n (n z [w5,w23,w55,w105,w134,w195,w205] z) [w5,w38,w55,w73,w105,w195,w222] z)) [w5,w38,w55,w91,w121,w177,w205] (n (n (n z [w5,w38,w63,w73,w105,w177,w222] z) [w5,w38,w63,w73,w121,w177,w205] z) [w6,w17,w23,w38,w55,w296,w313] (n (n z [w6,w17,w55,w73,w105,w222,w238] z) [w6,w17,w55,w121,w134,w177,w205] z))) [w6,w23,w55,w91,w105,w205,w238] (n (n (n (n z [w6,w23,w55,w105,w134,w195,w205] z) [w6,w38,w55,w73,w105,w195,w222] z) [w6,w38,w55,w91,w121,w177,w205] (n (n z [w6,w38,w63,w73,w105,w177,w222] z) [w6,w38,w63,w73,w121,w177,w205] z)) [w7,w17,w23,w38,w55,w296,w313] (n (n (n z [w7,w17,w55,w73,w105,w222,w238] z) [w7,w17,w55,w121,w134,w177,w205] z) [w7,w23,w55,w91,w105,w205,w238] (n z [w7,w23,w55,w105,w134,w195,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaaaaba : t6aaaaaba.all (blocked 5 t5) = true := by
  decide +kernel
def t6aaaaabb := (n (n (n (n (n z [w7,w38,w55,w91,w121,w177,w205] z) [w7,w38,w63,w73,w105,w177,w222] z) [w7,w38,w63,w73,w121,w177,w205] (n (n z [w8,w17,w23,w38,w55,w296,w313] z) [w8,w17,w55,w73,w105,w222,w238] z)) [w8,w17,w55,w121,w134,w177,w205] (n (n (n z [w8,w23,w55,w91,w105,w205,w238] z) [w8,w23,w55,w105,w134,w195,w205] z) [w8,w38,w55,w73,w105,w195,w222] (n (n z [w8,w38,w55,w91,w121,w177,w205] z) [w8,w38,w63,w73,w105,w177,w222] z))) [w8,w38,w63,w73,w121,w177,w205] (n (n (n (n z [w9,w23,w55,w105,w134,w195,w205] z) [w10,w17,w23,w38,w55,w296,w313] z) [w10,w17,w55,w73,w105,w222,w238] (n (n z [w10,w17,w55,w121,w134,w177,w205] z) [w10,w23,w55,w91,w105,w205,w238] z)) [w10,w23,w55,w105,w134,w195,w205] (n (n (n z [w10,w38,w55,w73,w105,w195,w222] z) [w10,w38,w55,w91,w121,w177,w205] z) [w10,w38,w63,w73,w105,w177,w222] (n z [w10,w38,w63,w73,w121,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaaaabb : t6aaaaabb.all (blocked 5 t5) = true := by
  decide +kernel
def t6aaaaab := (n t6aaaaaba [w7,w38,w55,w73,w105,w195,w222] t6aaaaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaaaab : t6aaaaab.all (blocked 5 t5) = true := by
  simp only [t6aaaaab, ReplayTree.all, n, ht6aaaaaba, ht6aaaaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aaaaa := (n t6aaaaaa [w5,w17,w23,w38,w55,w296,w313] t6aaaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaaaa : t6aaaaa.all (blocked 5 t5) = true := by
  simp only [t6aaaaa, ReplayTree.all, n, ht6aaaaaa, ht6aaaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aaaabaa := (n (n (n (n (n z [w12,w13,w38,w55,w73,w205,w313] z) [w12,w13,w38,w55,w105,w177,w296] z) [w12,w13,w55,w73,w105,w205,w238] (n (n z [w12,w13,w55,w105,w134,w177,w205] z) [w12,w17,w23,w38,w55,w296,w313] z)) [w12,w17,w47,w55,w73,w205,w313] (n (n (n z [w12,w17,w47,w55,w105,w177,w296] z) [w12,w17,w55,w73,w105,w222,w238] z) [w12,w17,w55,w73,w121,w205,w238] (n (n z [w12,w17,w55,w105,w134,w177,w222] z) [w12,w17,w55,w121,w134,w177,w205] z))) [w12,w23,w55,w91,w105,w205,w238] (n (n (n (n z [w12,w23,w55,w105,w134,w195,w205] z) [w12,w38,w55,w73,w105,w195,w222] z) [w12,w38,w55,w91,w121,w177,w205] (n (n z [w12,w38,w63,w73,w105,w177,w222] z) [w12,w38,w63,w73,w121,w177,w205] z)) [w12,w47,w63,w73,w105,w177,w205] (n (n (n z [w13,w17,w23,w38,w55,w296,w313] z) [w13,w17,w55,w73,w105,w222,w238] z) [w13,w17,w55,w121,w134,w177,w205] (n z [w13,w23,w38,w55,w69,w205,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaaabaa : t6aaaabaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6aaaabab := (n (n (n (n (n z [w13,w23,w38,w55,w73,w205,w309] z) [w13,w23,w38,w55,w73,w205,w313] z) [w13,w23,w38,w55,w73,w205,w319] (n (n z [w13,w23,w38,w55,w73,w213,w313] z) [w13,w23,w38,w55,w73,w296,w313] z)) [w13,w23,w38,w55,w84,w205,w313] (n (n (n z [w13,w23,w38,w55,w103,w177,w205] z) [w13,w23,w38,w55,w105,w173,w296] z) [w13,w23,w38,w55,w105,w177,w292] (n (n z [w13,w23,w38,w55,w105,w177,w296] z) [w13,w23,w38,w55,w105,w177,w302] z))) [w13,w23,w38,w55,w105,w192,w296] (n (n (n (n z [w13,w23,w38,w55,w105,w263,w296] z) [w13,w23,w38,w55,w105,w296,w313] z) [w13,w23,w38,w55,w113,w177,w296] (n (n z [w13,w23,w38,w55,w158,w205,w313] z) [w13,w23,w38,w55,w177,w296,w313] z)) [w13,w23,w38,w55,w205,w296,w313] (n (n (n z [w13,w23,w38,w55,w296,w313] z) [w13,w23,w38,w60,w73,w205,w313] z) [w13,w23,w38,w60,w105,w177,w296] (n z [w13,w23,w38,w73,w105,w205,w260] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaaabab : t6aaaabab.all (blocked 5 t5) = true := by
  decide +kernel
def t6aaaaba := (n t6aaaabaa [w13,w23,w38,w55,w73,w105,w204] t6aaaabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaaaba : t6aaaaba.all (blocked 5 t5) = true := by
  simp only [t6aaaaba, ReplayTree.all, n, ht6aaaabaa, ht6aaaabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aaaabba := (n (n (n (n (n z [w13,w23,w38,w105,w158,w205,w263] z) [w13,w23,w46,w55,w73,w205,w313] z) [w13,w23,w46,w55,w105,w177,w296] (n (n z [w13,w23,w55,w69,w105,w205,w238] z) [w13,w23,w55,w73,w105,w205,w234] z)) [w13,w23,w55,w73,w105,w205,w238] (n (n (n z [w13,w23,w55,w73,w105,w205,w245] z) [w13,w23,w55,w73,w105,w213,w238] z) [w13,w23,w55,w73,w105,w222,w238] (n (n z [w13,w23,w55,w73,w113,w205,w238] z) [w13,w23,w55,w73,w121,w205,w238] z))) [w13,w23,w55,w73,w134,w205,w313] (n (n (n (n z [w13,w23,w55,w73,w205,w238,w313] z) [w13,w23,w55,w84,w105,w205,w238] z) [w13,w23,w55,w91,w105,w205,w238] (n (n z [w13,w23,w55,w105,w131,w177,w205] z) [w13,w23,w55,w105,w134,w173,w205] z)) [w13,w23,w55,w105,w134,w177,w205] (n (n (n z [w13,w23,w55,w105,w134,w177,w213] z) [w13,w23,w55,w105,w134,w177,w222] z) [w13,w23,w55,w105,w134,w177,w296] (n z [w13,w23,w55,w105,w134,w192,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaaabba : t6aaaabba.all (blocked 5 t5) = true := by
  decide +kernel
def t6aaaabbb := (n (n (n (n (n z [w13,w23,w55,w105,w134,w205,w238] z) [w13,w23,w55,w105,w134,w205,w263] z) [w13,w23,w55,w105,w134,w205,w313] (n (n z [w13,w23,w55,w105,w139,w177,w205] z) [w13,w23,w55,w105,w158,w205,w238] z)) [w13,w23,w55,w105,w177,w238,w296] (n (n (n z [w13,w23,w55,w105,w205,w238,w296] z) [w13,w23,w55,w113,w134,w177,w205] z) [w13,w23,w55,w121,w134,w177,w205] (n z [w13,w23,w60,w73,w105,w205,w238] z))) [w13,w23,w60,w105,w134,w177,w205] (n (n (n (n z [w13,w27,w38,w55,w73,w205,w313] z) [w13,w27,w38,w55,w105,w177,w296] z) [w13,w37,w55,w73,w105,w177,w205] (n (n z [w13,w38,w55,w65,w73,w205,w313] z) [w13,w38,w55,w65,w105,w177,w296] z)) [w13,w38,w55,w69,w105,w177,w222] (n (n (n z [w13,w38,w55,w69,w121,w177,w205] z) [w13,w38,w55,w73,w105,w173,w222] z) [w13,w38,w55,w73,w105,w177,w211] (n z [w13,w38,w55,w73,w105,w177,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaaabbb : t6aaaabbb.all (blocked 5 t5) = true := by
  decide +kernel
def t6aaaabb := (n t6aaaabba [w13,w23,w55,w105,w134,w195,w205] t6aaaabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaaabb : t6aaaabb.all (blocked 5 t5) = true := by
  simp only [t6aaaabb, ReplayTree.all, n, ht6aaaabba, ht6aaaabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aaaab := (n t6aaaaba [w13,w23,w38,w105,w156,w177,w205] t6aaaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaaab : t6aaaab.all (blocked 5 t5) = true := by
  simp only [t6aaaab, ReplayTree.all, n, ht6aaaaba, ht6aaaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aaaa := (n t6aaaaa [w11,w23,w55,w91,w105,w205,w238] t6aaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaaa : t6aaaa.all (blocked 5 t5) = true := by
  simp only [t6aaaa, ReplayTree.all, n, ht6aaaaa, ht6aaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aaabaaa := (n (n (n (n (n z [w13,w38,w55,w73,w105,w195,w222] z) [w13,w38,w55,w73,w105,w222,w238] z) [w13,w38,w55,w73,w105,w222,w263] (n (n z [w13,w38,w55,w73,w110,w177,w205] z) [w13,w38,w55,w73,w113,w177,w222] z)) [w13,w38,w55,w73,w121,w173,w205] (n (n (n z [w13,w38,w55,w73,w121,w177,w205] z) [w13,w38,w55,w73,w121,w177,w213] z) [w13,w38,w55,w73,w121,w177,w222] (n (n z [w13,w38,w55,w73,w121,w177,w296] z) [w13,w38,w55,w73,w121,w192,w205] z))) [w13,w38,w55,w73,w121,w195,w205] (n (n (n (n z [w13,w38,w55,w73,w121,w205,w238] z) [w13,w38,w55,w73,w121,w205,w263] z) [w13,w38,w55,w73,w121,w205,w313] (n (n z [w13,w38,w55,w73,w177,w222,w313] z) [w13,w38,w55,w73,w205,w222,w313] z)) [w13,w38,w55,w84,w105,w177,w222] (n (n (n z [w13,w38,w55,w84,w121,w177,w205] z) [w13,w38,w55,w91,w105,w177,w222] z) [w13,w38,w55,w91,w121,w177,w205] (n z [w13,w38,w55,w105,w121,w177,w296] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaabaaa : t6aaabaaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6aaabaab := (n (n (n (n (n z [w13,w38,w55,w105,w158,w177,w222] z) [w13,w38,w55,w105,w177,w222,w296] z) [w13,w38,w55,w121,w134,w177,w205] (n (n z [w13,w38,w55,w121,w158,w177,w205] z) [w13,w38,w58,w73,w105,w177,w205] z)) [w13,w38,w60,w73,w105,w177,w222] (n (n (n z [w13,w38,w60,w73,w121,w177,w205] z) [w13,w38,w63,w73,w105,w177,w222] z) [w13,w38,w63,w73,w121,w177,w205] (n (n z [w13,w38,w65,w73,w105,w205,w263] z) [w13,w38,w65,w105,w158,w177,w205] z))) [w13,w46,w55,w73,w105,w177,w222] (n (n (n (n z [w13,w46,w55,w73,w121,w177,w205] z) [w13,w55,w65,w73,w105,w205,w238] z) [w13,w55,w65,w105,w134,w177,w205] (n (n z [w13,w55,w73,w105,w177,w222,w238] z) [w13,w55,w73,w105,w205,w222,w238] z)) [w13,w55,w73,w105,w222,w238] (n (n (n z [w13,w55,w73,w121,w134,w177,w205] z) [w13,w55,w105,w121,w134,w177,w205] z) [w13,w55,w121,w134,w177,w205] (n z [w14,w23,w38,w55,w73,w205,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaabaab : t6aaabaab.all (blocked 5 t5) = true := by
  decide +kernel
def t6aaabaa := (n t6aaabaaa [w13,w38,w55,w105,w134,w177,w222] t6aaabaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaabaa : t6aaabaa.all (blocked 5 t5) = true := by
  simp only [t6aaabaa, ReplayTree.all, n, ht6aaabaaa, ht6aaabaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aaababa := (n (n (n (n (n z [w14,w23,w55,w73,w105,w205,w238] z) [w14,w23,w55,w105,w134,w177,w205] z) [w14,w38,w55,w73,w105,w177,w222] (n (n z [w14,w38,w55,w73,w121,w177,w205] z) [w15,w23,w38,w55,w73,w205,w313] z)) [w15,w23,w38,w55,w105,w177,w296] (n (n (n z [w15,w23,w55,w73,w105,w205,w238] z) [w15,w23,w55,w105,w134,w177,w205] z) [w15,w38,w55,w73,w105,w177,w222] (n (n z [w15,w38,w55,w73,w121,w177,w205] z) [w16,w23,w38,w55,w73,w205,w313] z))) [w16,w23,w38,w55,w105,w177,w296] (n (n (n (n z [w16,w23,w55,w73,w105,w205,w238] z) [w16,w23,w55,w105,w134,w177,w205] z) [w16,w38,w55,w73,w105,w177,w222] (n (n z [w16,w38,w55,w73,w121,w177,w205] z) [w17,w22,w38,w55,w73,w205,w313] z)) [w17,w22,w38,w55,w105,w177,w296] (n (n (n z [w17,w22,w55,w73,w105,w205,w238] z) [w17,w22,w55,w105,w134,w177,w205] z) [w17,w23,w27,w38,w55,w296,w313] (n z [w17,w23,w28,w38,w55,w296,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaababa : t6aaababa.all (blocked 5 t5) = true := by
  decide +kernel
def t6aaababb := (n (n (n (n (n z [w17,w23,w28,w55,w105,w134,w173] z) [w17,w23,w28,w73,w105,w238,w261] z) [w17,w23,w32,w38,w55,w296,w313] (n (n z [w17,w23,w32,w38,w159,w177,w296] z) [w17,w23,w32,w55,w69,w205,w238] z)) [w17,w23,w32,w134,w159,w177,w205] (n (n (n z [w17,w23,w36,w38,w55,w296,w313] z) [w17,w23,w37,w55,w73,w205,w313] z) [w17,w23,w37,w55,w105,w177,w296] (n (n z [w17,w23,w38,w47,w55,w296,w313] z) [w17,w23,w38,w50,w55,w296,w313] z))) [w17,w23,w38,w55,w59,w296,w313] (n (n (n (n z [w17,w23,w38,w55,w63,w296,w313] z) [w17,w23,w38,w55,w65,w296,w313] z) [w17,w23,w38,w55,w69,w105,w204] (n (n z [w17,w23,w38,w55,w69,w173,w329] z) [w17,w23,w38,w55,w69,w177,w229] z)) [w17,w23,w38,w55,w69,w205,w226] (n (n (n z [w17,w23,w38,w55,w69,w205,w309] z) [w17,w23,w38,w55,w69,w205,w313] z) [w17,w23,w38,w55,w69,w205,w352] (n z [w17,w23,w38,w55,w69,w292,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaababb : t6aaababb.all (blocked 5 t5) = true := by
  decide +kernel
def t6aaabab := (n t6aaababa [w17,w23,w28,w38,w73,w261,w313] t6aaababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaabab : t6aaabab.all (blocked 5 t5) = true := by
  simp only [t6aaabab, ReplayTree.all, n, ht6aaababa, ht6aaababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aaaba := (n t6aaabaa [w14,w23,w38,w55,w105,w177,w296] t6aaabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaaba : t6aaaba.all (blocked 5 t5) = true := by
  simp only [t6aaaba, ReplayTree.all, n, ht6aaabaa, ht6aaabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aaabbaa := (n (n (n (n (n z [w17,w23,w38,w55,w70,w205,w313] z) [w17,w23,w38,w55,w71,w205,w313] z) [w17,w23,w38,w55,w72,w205,w313] (n (n z [w17,w23,w38,w55,w73,w105,w204] z) [w17,w23,w38,w55,w73,w121,w204] z)) [w17,w23,w38,w55,w73,w125,w173] (n (n (n z [w17,w23,w38,w55,w73,w204,w313] z) [w17,w23,w38,w55,w73,w204,w328] z) [w17,w23,w38,w55,w73,w205,w309] (n (n z [w17,w23,w38,w55,w73,w205,w310] z) [w17,w23,w38,w55,w73,w205,w311] z))) [w17,w23,w38,w55,w73,w205,w312] (n (n (n (n z [w17,w23,w38,w55,w73,w205,w313] z) [w17,w23,w38,w55,w73,w205,w316] z) [w17,w23,w38,w55,w73,w205,w319] (n (n z [w17,w23,w38,w55,w73,w205,w328] z) [w17,w23,w38,w55,w73,w205,w331] z)) [w17,w23,w38,w55,w73,w205,w350] (n (n (n z [w17,w23,w38,w55,w73,w207,w313] z) [w17,w23,w38,w55,w73,w208,w313] z) [w17,w23,w38,w55,w73,w211,w313] (n z [w17,w23,w38,w55,w73,w213,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaabbaa : t6aaabbaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6aaabbab := (n (n (n (n (n z [w17,w23,w38,w55,w73,w249,w313] z) [w17,w23,w38,w55,w73,w251,w309] z) [w17,w23,w38,w55,w73,w292,w313] (n (n z [w17,w23,w38,w55,w73,w296,w309] z) [w17,w23,w38,w55,w73,w296,w313] z)) [w17,w23,w38,w55,w74,w205,w313] (n (n (n z [w17,w23,w38,w55,w75,w205,w313] z) [w17,w23,w38,w55,w79,w205,w313] z) [w17,w23,w38,w55,w84,w205,w313] (n (n z [w17,w23,w38,w55,w91,w105,w204] z) [w17,w23,w38,w55,w91,w205,w309] z))) [w17,w23,w38,w55,w91,w296,w313] (n (n (n (n z [w17,w23,w38,w55,w96,w296,w313] z) [w17,w23,w38,w55,w100,w105,w173] z) [w17,w23,w38,w55,w100,w205,w313] (n (n z [w17,w23,w38,w55,w103,w173,w205] z) [w17,w23,w38,w55,w103,w177,w205] z)) [w17,w23,w38,w55,w103,w177,w222] (n (n (n z [w17,w23,w38,w55,w103,w177,w296] z) [w17,w23,w38,w55,w103,w177,w326] z) [w17,w23,w38,w55,w103,w195,w205] (n z [w17,w23,w38,w55,w103,w205,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaabbab : t6aaabbab.all (blocked 5 t5) = true := by
  decide +kernel
def t6aaabba := (n t6aaabbaa [w17,w23,w38,w55,w73,w229,w313] t6aaabbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaabba : t6aaabba.all (blocked 5 t5) = true := by
  simp only [t6aaabba, ReplayTree.all, n, ht6aaabbaa, ht6aaabbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aaabbba := (n (n (n (n (n z [w17,w23,w38,w55,w103,w205,w312] z) [w17,w23,w38,w55,w103,w205,w313] z) [w17,w23,w38,w55,w104,w205,w313] (n (n z [w17,w23,w38,w55,w105,w134,w204] z) [w17,w23,w38,w55,w105,w158,w204] z)) [w17,w23,w38,w55,w105,w173,w292] (n (n (n z [w17,w23,w38,w55,w105,w173,w296] z) [w17,w23,w38,w55,w105,w173,w349] z) [w17,w23,w38,w55,w105,w174,w296] (n (n z [w17,w23,w38,w55,w105,w175,w296] z) [w17,w23,w38,w55,w105,w176,w296] z))) [w17,w23,w38,w55,w105,w177,w292] (n (n (n (n z [w17,w23,w38,w55,w105,w177,w293] z) [w17,w23,w38,w55,w105,w177,w294] z) [w17,w23,w38,w55,w105,w177,w295] (n (n z [w17,w23,w38,w55,w105,w177,w296] z) [w17,w23,w38,w55,w105,w177,w299] z)) [w17,w23,w38,w55,w105,w177,w302] (n (n (n z [w17,w23,w38,w55,w105,w177,w326] z) [w17,w23,w38,w55,w105,w177,w327] z) [w17,w23,w38,w55,w105,w177,w347] (n z [w17,w23,w38,w55,w105,w178,w296] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaabbba : t6aaabbba.all (blocked 5 t5) = true := by
  decide +kernel
def t6aaabbbb := (n (n (n (n (n z [w17,w23,w38,w55,w105,w183,w296] z) [w17,w23,w38,w55,w105,w192,w296] z) [w17,w23,w38,w55,w105,w195,w292] (n (n z [w17,w23,w38,w55,w105,w204,w295] z) [w17,w23,w38,w55,w105,w204,w296] z)) [w17,w23,w38,w55,w105,w205,w277] (n (n (n z [w17,w23,w38,w55,w105,w209,w296] z) [w17,w23,w38,w55,w105,w226,w296] z) [w17,w23,w38,w55,w105,w232,w296] (n z [w17,w23,w38,w55,w105,w238,w292] z))) [w17,w23,w38,w55,w105,w260,w296] (n (n (n (n z [w17,w23,w38,w55,w105,w263,w292] z) [w17,w23,w38,w55,w105,w263,w295] z) [w17,w23,w38,w55,w105,w263,w296] (n (n z [w17,w23,w38,w55,w105,w277,w296] z) [w17,w23,w38,w55,w105,w279,w292] z)) [w17,w23,w38,w55,w105,w279,w296] (n (n (n z [w17,w23,w38,w55,w105,w292,w313] z) [w17,w23,w38,w55,w105,w296,w309] z) [w17,w23,w38,w55,w105,w296,w313] (n z [w17,w23,w38,w55,w105,w296,w357] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaabbbb : t6aaabbbb.all (blocked 5 t5) = true := by
  decide +kernel
def t6aaabbb := (n t6aaabbba [w17,w23,w38,w55,w105,w179,w296] t6aaabbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaabbb : t6aaabbb.all (blocked 5 t5) = true := by
  simp only [t6aaabbb, ReplayTree.all, n, ht6aaabbba, ht6aaabbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aaabb := (n t6aaabba [w17,w23,w38,w55,w103,w205,w263] t6aaabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaabb : t6aaabb.all (blocked 5 t5) = true := by
  simp only [t6aaabb, ReplayTree.all, n, ht6aaabba, ht6aaabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aaab := (n t6aaaba [w17,w23,w38,w55,w69,w296,w313] t6aaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaab : t6aaab.all (blocked 5 t5) = true := by
  simp only [t6aaab, ReplayTree.all, n, ht6aaaba, ht6aaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aaa := (n t6aaaa [w13,w38,w55,w73,w105,w192,w222] t6aaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaa : t6aaa.all (blocked 5 t5) = true := by
  simp only [t6aaa, ReplayTree.all, n, ht6aaaa, ht6aaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aabaaaa := (n (n (n (n (n z [w17,w23,w38,w55,w108,w177,w296] z) [w17,w23,w38,w55,w109,w177,w296] z) [w17,w23,w38,w55,w110,w177,w296] (n (n z [w17,w23,w38,w55,w113,w177,w296] z) [w17,w23,w38,w55,w116,w296,w313] z)) [w17,w23,w38,w55,w121,w296,w313] (n (n (n z [w17,w23,w38,w55,w125,w177,w296] z) [w17,w23,w38,w55,w128,w205,w313] z) [w17,w23,w38,w55,w134,w205,w309] (n (n z [w17,w23,w38,w55,w134,w296,w313] z) [w17,w23,w38,w55,w146,w177,w296] z))) [w17,w23,w38,w55,w149,w177,w292] (n (n (n (n z [w17,w23,w38,w55,w149,w296,w313] z) [w17,w23,w38,w55,w156,w205,w313] z) [w17,w23,w38,w55,w158,w205,w309] (n (n z [w17,w23,w38,w55,w158,w205,w312] z) [w17,w23,w38,w55,w158,w205,w313] z)) [w17,w23,w38,w55,w158,w296,w313] (n (n (n z [w17,w23,w38,w55,w159,w296,w313] z) [w17,w23,w38,w55,w173,w296,w309] z) [w17,w23,w38,w55,w173,w296,w313] (n z [w17,w23,w38,w55,w177,w292,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aabaaaa : t6aabaaaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6aabaaab := (n (n (n (n (n z [w17,w23,w38,w55,w177,w296,w313] z) [w17,w23,w38,w55,w195,w296,w313] z) [w17,w23,w38,w55,w201,w296,w313] (n (n z [w17,w23,w38,w55,w205,w277,w313] z) [w17,w23,w38,w55,w205,w278,w309] z)) [w17,w23,w38,w55,w205,w278,w313] (n (n (n z [w17,w23,w38,w55,w205,w292,w313] z) [w17,w23,w38,w55,w205,w296,w309] z) [w17,w23,w38,w55,w205,w296,w313] (n (n z [w17,w23,w38,w55,w205,w313,w355] z) [w17,w23,w38,w55,w210,w296,w313] z))) [w17,w23,w38,w55,w215,w296,w313] (n (n (n (n z [w17,w23,w38,w55,w222,w296,w313] z) [w17,w23,w38,w55,w238,w296,w313] z) [w17,w23,w38,w55,w251,w296,w313] (n (n z [w17,w23,w38,w55,w261,w296,w313] z) [w17,w23,w38,w55,w263,w296,w313] z)) [w17,w23,w38,w55,w277,w296,w313] (n (n (n z [w17,w23,w38,w55,w280,w296,w313] z) [w17,w23,w38,w55,w292,w313] z) [w17,w23,w38,w55,w296,w296,w313] (n z [w17,w23,w38,w55,w296,w297,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aabaaab : t6aabaaab.all (blocked 5 t5) = true := by
  decide +kernel
def t6aabaaa := (n t6aabaaaa [w17,w23,w38,w55,w177,w296,w309] t6aabaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aabaaa : t6aabaaa.all (blocked 5 t5) = true := by
  simp only [t6aabaaa, ReplayTree.all, n, ht6aabaaaa, ht6aabaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aabaaba := (n (n (n (n (n z [w17,w23,w38,w55,w296,w307,w313] z) [w17,w23,w38,w55,w296,w309] z) [w17,w23,w38,w55,w296,w313] (n (n z [w17,w23,w38,w55,w296,w313,w313] z) [w17,w23,w38,w55,w296,w313,w314] z)) [w17,w23,w38,w55,w296,w313,w321] (n (n (n z [w17,w23,w38,w55,w296,w313,w324] z) [w17,w23,w38,w55,w296,w313,w329] z) [w17,w23,w38,w55,w296,w313,w330] (n (n z [w17,w23,w38,w55,w296,w313,w332] z) [w17,w23,w38,w55,w296,w313,w333] z))) [w17,w23,w38,w55,w296,w313,w349] (n (n (n (n z [w17,w23,w38,w55,w296,w313,w352] z) [w17,w23,w38,w55,w296,w313,w355] z) [w17,w23,w38,w55,w296,w313,w357] (n (n z [w17,w23,w38,w56,w73,w205,w313] z) [w17,w23,w38,w57,w105,w177,w296] z)) [w17,w23,w38,w58,w73,w205,w313] (n (n (n z [w17,w23,w38,w58,w105,w177,w296] z) [w17,w23,w38,w60,w73,w205,w313] z) [w17,w23,w38,w60,w105,w177,w296] (n z [w17,w23,w38,w63,w73,w105,w204] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aabaaba : t6aabaaba.all (blocked 5 t5) = true := by
  decide +kernel
def t6aabaabb := (n (n (n (n (n z [w17,w23,w38,w63,w103,w177,w205] z) [w17,w23,w38,w63,w105,w177,w292] z) [w17,w23,w38,w63,w105,w263,w296] (n (n z [w17,w23,w38,w63,w158,w205,w313] z) [w17,w23,w38,w65,w105,w263,w296] z)) [w17,w23,w38,w65,w158,w205,w313] (n (n (n z [w17,w23,w38,w69,w105,w205,w260] z) [w17,w23,w38,w69,w156,w205,w313] z) [w17,w23,w38,w73,w105,w204,w260] (n (n z [w17,w23,w38,w73,w105,w204,w261] z) [w17,w23,w38,w73,w105,w205,w260] z))) [w17,w23,w38,w73,w105,w205,w262] (n (n (n (n z [w17,w23,w38,w73,w105,w205,w268] z) [w17,w23,w38,w73,w105,w209,w261] z) [w17,w23,w38,w73,w105,w210,w260] (n (n z [w17,w23,w38,w73,w105,w222,w260] z) [w17,w23,w38,w73,w105,w251,w260] z)) [w17,w23,w38,w73,w105,w260,w296] (n (n (n z [w17,w23,w38,w73,w105,w260,w329] z) [w17,w23,w38,w73,w121,w205,w260] z) [w17,w23,w38,w73,w125,w177,w261] (n z [w17,w23,w38,w73,w156,w205,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aabaabb : t6aabaabb.all (blocked 5 t5) = true := by
  decide +kernel
def t6aabaab := (n t6aabaaba [w17,w23,w38,w63,w73,w205,w309] t6aabaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aabaab : t6aabaab.all (blocked 5 t5) = true := by
  simp only [t6aabaab, ReplayTree.all, n, ht6aabaaba, ht6aabaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aabaa := (n t6aabaaa [w17,w23,w38,w55,w296,w304,w313] t6aabaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aabaa : t6aabaa.all (blocked 5 t5) = true := by
  simp only [t6aabaa, ReplayTree.all, n, ht6aabaaa, ht6aabaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aababaa := (n (n (n (n (n z [w17,w23,w38,w73,w205,w260,w309] z) [w17,w23,w38,w73,w205,w260,w313] z) [w17,w23,w38,w91,w105,w205,w260] (n (n z [w17,w23,w38,w103,w156,w177,w205] z) [w17,w23,w38,w103,w158,w205,w263] z)) [w17,w23,w38,w103,w159,w177,w205] (n (n (n z [w17,w23,w38,w104,w159,w177,w205] z) [w17,w23,w38,w105,w134,w205,w260] z) [w17,w23,w38,w105,w156,w173,w205] (n (n z [w17,w23,w38,w105,w156,w177,w205] z) [w17,w23,w38,w105,w156,w177,w222] z))) [w17,w23,w38,w105,w156,w177,w292] (n (n (n (n z [w17,w23,w38,w105,w156,w177,w296] z) [w17,w23,w38,w105,w156,w195,w205] z) [w17,w23,w38,w105,w156,w205,w238] (n (n z [w17,w23,w38,w105,w156,w205,w263] z) [w17,w23,w38,w105,w156,w205,w279] z)) [w17,w23,w38,w105,w156,w205,w313] (n (n (n z [w17,w23,w38,w105,w156,w205,w356] z) [w17,w23,w38,w105,w157,w177,w205] z) [w17,w23,w38,w105,w158,w204,w263] (n z [w17,w23,w38,w105,w158,w205,w260] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aababaa : t6aababaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6aababab := (n (n (n (n (n z [w17,w23,w38,w105,w158,w205,w271] z) [w17,w23,w38,w105,w158,w205,w357] z) [w17,w23,w38,w105,w158,w222,w263] (n (n z [w17,w23,w38,w105,w158,w263,w296] z) [w17,w23,w38,w105,w165,w177,w205] z)) [w17,w23,w38,w105,w166,w205,w263] (n (n (n z [w17,w23,w38,w105,w166,w205,w271] z) [w17,w23,w38,w105,w173,w260,w296] z) [w17,w23,w38,w105,w177,w260,w296] (n (n z [w17,w23,w38,w105,w205,w260,w278] z) [w17,w23,w38,w105,w205,w260,w296] z))) [w17,w23,w38,w105,w205,w260,w354] (n (n (n (n z [w17,w23,w38,w105,w205,w263,w355] z) [w17,w23,w38,w105,w260,w296] z) [w17,w23,w38,w105,w261,w263,w296] (n (n z [w17,w23,w38,w105,w263,w296,w355] z) [w17,w23,w38,w107,w156,w177,w205] z)) [w17,w23,w38,w121,w156,w177,w205] (n (n (n z [w17,w23,w38,w121,w158,w205,w263] z) [w17,w23,w38,w149,w156,w177,w205] z) [w17,w23,w38,w156,w177,w205,w313] (n z [w17,w23,w38,w156,w177,w205,w329] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aababab : t6aababab.all (blocked 5 t5) = true := by
  decide +kernel
def t6aababa := (n t6aababaa [w17,w23,w38,w105,w158,w205,w263] t6aababab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aababa : t6aababa.all (blocked 5 t5) = true := by
  simp only [t6aababa, ReplayTree.all, n, ht6aababaa, ht6aababab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aababba := (n (n (n (n (n z [w17,w23,w38,w158,w159,w205,w313] z) [w17,w23,w38,w158,w205,w263,w313] z) [w17,w23,w38,w158,w205,w313,w357] (n (n z [w17,w23,w39,w55,w73,w205,w313] z) [w17,w23,w39,w55,w105,w177,w296] z)) [w17,w23,w40,w55,w73,w205,w313] (n (n (n z [w17,w23,w40,w55,w105,w177,w296] z) [w17,w23,w41,w55,w73,w205,w313] z) [w17,w23,w41,w55,w105,w177,w296] (n (n z [w17,w23,w42,w55,w73,w205,w313] z) [w17,w23,w42,w55,w105,w177,w296] z))) [w17,w23,w46,w55,w73,w205,w313] (n (n (n (n z [w17,w23,w46,w55,w105,w177,w296] z) [w17,w23,w51,w55,w73,w105,w173] z) [w17,w23,w51,w55,w73,w205,w313] (n (n z [w17,w23,w51,w55,w105,w177,w296] z) [w17,w23,w51,w73,w105,w177,w261] z)) [w17,w23,w53,w55,w69,w177,w205] (n (n (n z [w17,w23,w53,w55,w73,w205,w313] z) [w17,w23,w53,w55,w105,w177,w296] z) [w17,w23,w53,w73,w159,w177,w205] (n z [w17,w23,w55,w69,w105,w205,w234] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aababba : t6aababba.all (blocked 5 t5) = true := by
  decide +kernel
def t6aababbb := (n (n (n (n (n z [w17,w23,w55,w69,w105,w205,w339] z) [w17,w23,w55,w69,w105,w222,w238] z) [w17,w23,w55,w69,w105,w238,w292] (n (n z [w17,w23,w55,w69,w107,w205,w238] z) [w17,w23,w55,w69,w121,w205,w238] z)) [w17,w23,w55,w69,w131,w205,w313] (n (n (n z [w17,w23,w55,w69,w134,w205,w313] z) [w17,w23,w55,w69,w149,w205,w238] z) [w17,w23,w55,w69,w205,w238,w313] (n z [w17,w23,w55,w69,w205,w238,w329] z))) [w17,w23,w55,w69,w205,w238,w352] (n (n (n (n z [w17,w23,w55,w70,w105,w205,w238] z) [w17,w23,w55,w71,w105,w205,w238] z) [w17,w23,w55,w72,w105,w205,w238] (n (n z [w17,w23,w55,w73,w103,w205,w238] z) [w17,w23,w55,w73,w105,w134,w204] z)) [w17,w23,w55,w73,w105,w204,w238] (n (n (n z [w17,w23,w55,w73,w105,w204,w250] z) [w17,w23,w55,w73,w105,w205,w234] z) [w17,w23,w55,w73,w105,w205,w235] (n z [w17,w23,w55,w73,w105,w205,w236] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aababbb : t6aababbb.all (blocked 5 t5) = true := by
  decide +kernel
def t6aababb := (n t6aababba [w17,w23,w55,w69,w105,w205,w238] t6aababbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aababb : t6aababb.all (blocked 5 t5) = true := by
  simp only [t6aababb, ReplayTree.all, n, ht6aababba, ht6aababbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aabab := (n t6aababa [w17,w23,w38,w156,w205,w313] t6aababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aabab : t6aabab.all (blocked 5 t5) = true := by
  simp only [t6aabab, ReplayTree.all, n, ht6aababa, ht6aababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aaba := (n t6aabaa [w17,w23,w38,w73,w159,w177,w229] t6aabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aaba : t6aaba.all (blocked 5 t5) = true := by
  simp only [t6aaba, ReplayTree.all, n, ht6aabaa, ht6aabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aabbaaa := (n (n (n (n (n z [w17,w23,w55,w73,w105,w205,w238] z) [w17,w23,w55,w73,w105,w205,w239] z) [w17,w23,w55,w73,w105,w205,w245] (n (n z [w17,w23,w55,w73,w105,w205,w250] z) [w17,w23,w55,w73,w105,w205,w252] z)) [w17,w23,w55,w73,w105,w205,w259] (n (n (n z [w17,w23,w55,w73,w105,w205,w339] z) [w17,w23,w55,w73,w105,w206,w238] z) [w17,w23,w55,w73,w105,w208,w238] (n (n z [w17,w23,w55,w73,w105,w211,w238] z) [w17,w23,w55,w73,w105,w213,w238] z))) [w17,w23,w55,w73,w105,w222,w234] (n (n (n (n z [w17,w23,w55,w73,w105,w222,w238] z) [w17,w23,w55,w73,w105,w229,w238] z) [w17,w23,w55,w73,w105,w234,w329] (n (n z [w17,w23,w55,w73,w105,w238,w249] z) [w17,w23,w55,w73,w105,w238,w292] z)) [w17,w23,w55,w73,w106,w205,w238] (n (n (n z [w17,w23,w55,w73,w108,w205,w238] z) [w17,w23,w55,w73,w109,w205,w238] z) [w17,w23,w55,w73,w110,w205,w238] (n z [w17,w23,w55,w73,w113,w205,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aabbaaa : t6aabbaaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6aabbaab := (n (n (n (n (n z [w17,w23,w55,w73,w121,w205,w238] z) [w17,w23,w55,w73,w121,w222,w238] z) [w17,w23,w55,w73,w125,w205,w238] (n (n z [w17,w23,w55,w73,w131,w205,w313] z) [w17,w23,w55,w73,w134,w205,w309] z)) [w17,w23,w55,w73,w134,w205,w313] (n (n (n z [w17,w23,w55,w73,w134,w296,w313] z) [w17,w23,w55,w73,w146,w205,w238] z) [w17,w23,w55,w73,w205,w234,w309] (n (n z [w17,w23,w55,w73,w205,w234,w313] z) [w17,w23,w55,w73,w205,w238,w309] z))) [w17,w23,w55,w73,w205,w238,w313] (n (n (n (n z [w17,w23,w55,w73,w205,w238,w324] z) [w17,w23,w55,w73,w205,w313,w340] z) [w17,w23,w55,w73,w222,w238,w313] (n (n z [w17,w23,w55,w73,w238,w296,w313] z) [w17,w23,w55,w74,w105,w205,w238] z)) [w17,w23,w55,w75,w105,w205,w238] (n (n (n z [w17,w23,w55,w76,w105,w205,w238] z) [w17,w23,w55,w77,w105,w205,w238] z) [w17,w23,w55,w79,w105,w205,w238] (n z [w17,w23,w55,w84,w105,w205,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aabbaab : t6aabbaab.all (blocked 5 t5) = true := by
  decide +kernel
def t6aabbaa := (n t6aabbaaa [w17,w23,w55,w73,w121,w205,w234] t6aabbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aabbaa : t6aabbaa.all (blocked 5 t5) = true := by
  simp only [t6aabbaa, ReplayTree.all, n, ht6aabbaaa, ht6aabbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aabbaba := (n (n (n (n (n z [w17,w23,w55,w91,w105,w205,w234] z) [w17,w23,w55,w91,w105,w205,w238] z) [w17,w23,w55,w91,w105,w222,w238] (n (n z [w17,w23,w55,w91,w121,w205,w238] z) [w17,w23,w55,w91,w134,w205,w313] z)) [w17,w23,w55,w96,w134,w205,w313] (n (n (n z [w17,w23,w55,w100,w105,w205,w238] z) [w17,w23,w55,w103,w105,w205,w238] z) [w17,w23,w55,w103,w134,w177,w205] (n (n z [w17,w23,w55,w103,w147,w177,w205] z) [w17,w23,w55,w103,w158,w205,w238] z))) [w17,w23,w55,w103,w177,w205,w238] (n (n (n (n z [w17,w23,w55,w103,w205,w238] z) [w17,w23,w55,w104,w105,w205,w238] z) [w17,w23,w55,w105,w128,w205,w238] (n (n z [w17,w23,w55,w105,w130,w177,w205] z) [w17,w23,w55,w105,w131,w173,w205] z)) [w17,w23,w55,w105,w131,w177,w205] (n (n (n z [w17,w23,w55,w105,w131,w177,w222] z) [w17,w23,w55,w105,w131,w177,w292] z) [w17,w23,w55,w105,w131,w177,w296] (n z [w17,w23,w55,w105,w131,w195,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aabbaba : t6aabbaba.all (blocked 5 t5) = true := by
  decide +kernel
def t6aabbabb := (n (n (n (n (n z [w17,w23,w55,w105,w131,w205,w263] z) [w17,w23,w55,w105,w131,w205,w279] z) [w17,w23,w55,w105,w131,w205,w313] (n (n z [w17,w23,w55,w105,w131,w205,w339] z) [w17,w23,w55,w105,w132,w177,w205] z)) [w17,w23,w55,w105,w133,w177,w205] (n (n (n z [w17,w23,w55,w105,w134,w173,w205] z) [w17,w23,w55,w105,w134,w173,w210] z) [w17,w23,w55,w105,w134,w173,w222] (n z [w17,w23,w55,w105,w134,w173,w251] z))) [w17,w23,w55,w105,w134,w173,w296] (n (n (n (n z [w17,w23,w55,w105,w134,w173,w329] z) [w17,w23,w55,w105,w134,w173,w349] z) [w17,w23,w55,w105,w134,w174,w205] (n (n z [w17,w23,w55,w105,w134,w175,w205] z) [w17,w23,w55,w105,w134,w176,w205] z)) [w17,w23,w55,w105,w134,w177,w204] (n (n (n z [w17,w23,w55,w105,w134,w177,w205] z) [w17,w23,w55,w105,w134,w177,w206] z) [w17,w23,w55,w105,w134,w177,w207] (n z [w17,w23,w55,w105,w134,w177,w208] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aabbabb : t6aabbabb.all (blocked 5 t5) = true := by
  decide +kernel
def t6aabbab := (n t6aabbaba [w17,w23,w55,w105,w131,w205,w238] t6aabbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aabbab : t6aabbab.all (blocked 5 t5) = true := by
  simp only [t6aabbab, ReplayTree.all, n, ht6aabbaba, ht6aabbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aabba := (n t6aabbaa [w17,w23,w55,w87,w105,w205,w238] t6aabbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aabba : t6aabba.all (blocked 5 t5) = true := by
  simp only [t6aabba, ReplayTree.all, n, ht6aabbaa, ht6aabbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aabbbaa := (n (n (n (n (n z [w17,w23,w55,w105,w134,w177,w213] z) [w17,w23,w55,w105,w134,w177,w222] z) [w17,w23,w55,w105,w134,w177,w229] (n (n z [w17,w23,w55,w105,w134,w177,w249] z) [w17,w23,w55,w105,w134,w177,w292] z)) [w17,w23,w55,w105,w134,w177,w296] (n (n (n z [w17,w23,w55,w105,w134,w177,w307] z) [w17,w23,w55,w105,w134,w178,w205] z) [w17,w23,w55,w105,w134,w179,w205] (n (n z [w17,w23,w55,w105,w134,w180,w205] z) [w17,w23,w55,w105,w134,w181,w205] z))) [w17,w23,w55,w105,w134,w183,w205] (n (n (n (n z [w17,w23,w55,w105,w134,w189,w205] z) [w17,w23,w55,w105,w134,w192,w205] z) [w17,w23,w55,w105,w134,w195,w205] (n (n z [w17,w23,w55,w105,w134,w195,w222] z) [w17,w23,w55,w105,w134,w204] z)) [w17,w23,w55,w105,w134,w204,w205] (n (n (n z [w17,w23,w55,w105,w134,w204,w263] z) [w17,w23,w55,w105,w134,w205,w209] z) [w17,w23,w55,w105,w134,w205,w226] (n z [w17,w23,w55,w105,w134,w205,w232] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aabbbaa : t6aabbbaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6aabbbab := (n (n (n (n (n z [w17,w23,w55,w105,w134,w205,w238] z) [w17,w23,w55,w105,w134,w205,w248] z) [w17,w23,w55,w105,w134,w205,w260] (n (n z [w17,w23,w55,w105,w134,w205,w263] z) [w17,w23,w55,w105,w134,w205,w265] z)) [w17,w23,w55,w105,w134,w205,w271] (n (n (n z [w17,w23,w55,w105,w134,w205,w279] z) [w17,w23,w55,w105,w134,w205,w309] z) [w17,w23,w55,w105,w134,w205,w313] (n (n z [w17,w23,w55,w105,w134,w205,w321] z) [w17,w23,w55,w105,w134,w205,w352] z))) [w17,w23,w55,w105,w134,w205,w357] (n (n (n (n z [w17,w23,w55,w105,w134,w222,w238] z) [w17,w23,w55,w105,w134,w222,w263] z) [w17,w23,w55,w105,w134,w263,w296] (n (n z [w17,w23,w55,w105,w134,w296,w313] z) [w17,w23,w55,w105,w135,w177,w205] z)) [w17,w23,w55,w105,w139,w177,w205] (n (n (n z [w17,w23,w55,w105,w144,w205,w238] z) [w17,w23,w55,w105,w145,w177,w205] z) [w17,w23,w55,w105,w147,w177,w205] (n z [w17,w23,w55,w105,w148,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aabbbab : t6aabbbab.all (blocked 5 t5) = true := by
  decide +kernel
def t6aabbba := (n t6aabbbaa [w17,w23,w55,w105,w134,w205,w234] t6aabbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aabbba : t6aabbba.all (blocked 5 t5) = true := by
  simp only [t6aabbba, ReplayTree.all, n, ht6aabbbaa, ht6aabbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aabbbba := (n (n (n (n (n z [w17,w23,w55,w105,w158,w205,w234] z) [w17,w23,w55,w105,w158,w205,w238] z) [w17,w23,w55,w105,w158,w222,w238] (n (n z [w17,w23,w55,w105,w161,w205,w238] z) [w17,w23,w55,w105,w166,w205,w238] z)) [w17,w23,w55,w105,w173,w205,w338] (n (n (n z [w17,w23,w55,w105,w173,w234,w296] z) [w17,w23,w55,w105,w173,w238,w296] z) [w17,w23,w55,w105,w177,w205,w338] (n (n z [w17,w23,w55,w105,w177,w234,w296] z) [w17,w23,w55,w105,w177,w238,w292] z))) [w17,w23,w55,w105,w177,w238,w296] (n (n (n (n z [w17,w23,w55,w105,w177,w296,w340] z) [w17,w23,w55,w105,w195,w238,w296] z) [w17,w23,w55,w105,w201,w238,w296] (n (n z [w17,w23,w55,w105,w205,w234,w278] z) [w17,w23,w55,w105,w205,w234,w296] z)) [w17,w23,w55,w105,w205,w234,w338] (n (n (n z [w17,w23,w55,w105,w205,w238,w278] z) [w17,w23,w55,w105,w205,w238,w292] z) [w17,w23,w55,w105,w205,w238,w296] (n z [w17,w23,w55,w105,w205,w238,w304] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aabbbba : t6aabbbba.all (blocked 5 t5) = true := by
  decide +kernel
def t6aabbbbb := (n (n (n (n (n z [w17,w23,w55,w105,w205,w238,w355] z) [w17,w23,w55,w105,w210,w238,w296] z) [w17,w23,w55,w105,w215,w238,w296] (n (n z [w17,w23,w55,w105,w222,w238,w296] z) [w17,w23,w55,w105,w238,w261,w296] z)) [w17,w23,w55,w105,w238,w263,w296] (n (n (n z [w17,w23,w55,w105,w238,w292] z) [w17,w23,w55,w105,w238,w296,w313] z) [w17,w23,w55,w105,w238,w296,w329] (n z [w17,w23,w55,w106,w134,w177,w205] z))) [w17,w23,w55,w107,w134,w205,w313] (n (n (n (n z [w17,w23,w55,w109,w134,w177,w205] z) [w17,w23,w55,w110,w134,w177,w205] z) [w17,w23,w55,w113,w134,w177,w205] (n (n z [w17,w23,w55,w116,w134,w205,w313] z) [w17,w23,w55,w121,w131,w177,w205] z)) [w17,w23,w55,w121,w134,w173,w205] (n (n (n z [w17,w23,w55,w121,w134,w177,w205] z) [w17,w23,w55,w121,w134,w177,w222] z) [w17,w23,w55,w121,w134,w177,w296] (n z [w17,w23,w55,w121,w134,w195,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aabbbbb : t6aabbbbb.all (blocked 5 t5) = true := by
  decide +kernel
def t6aabbbb := (n t6aabbbba [w17,w23,w55,w105,w205,w238,w349] t6aabbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aabbbb : t6aabbbb.all (blocked 5 t5) = true := by
  simp only [t6aabbbb, ReplayTree.all, n, ht6aabbbba, ht6aabbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aabbb := (n t6aabbba [w17,w23,w55,w105,w156,w205,w238] t6aabbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aabbb : t6aabbb.all (blocked 5 t5) = true := by
  simp only [t6aabbb, ReplayTree.all, n, ht6aabbba, ht6aabbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aabb := (n t6aabba [w17,w23,w55,w105,w134,w177,w211] t6aabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aabb : t6aabb.all (blocked 5 t5) = true := by
  simp only [t6aabb, ReplayTree.all, n, ht6aabba, ht6aabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aab := (n t6aaba [w17,w23,w55,w73,w105,w205,w237] t6aabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aab : t6aab.all (blocked 5 t5) = true := by
  simp only [t6aab, ReplayTree.all, n, ht6aaba, ht6aabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aa := (n t6aaa [w17,w23,w38,w55,w107,w296,w313] t6aab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aa : t6aa.all (blocked 5 t5) = true := by
  simp only [t6aa, ReplayTree.all, n, ht6aaa, ht6aab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abaaaaa := (n (n (n (n (n z [w17,w23,w55,w121,w134,w205,w263] z) [w17,w23,w55,w121,w134,w205,w313] z) [w17,w23,w55,w121,w158,w205,w238] (n (n z [w17,w23,w55,w125,w134,w177,w205] z) [w17,w23,w55,w131,w177,w205,w329] z)) [w17,w23,w55,w134,w146,w177,w205] (n (n (n z [w17,w23,w55,w134,w158,w205,w313] z) [w17,w23,w55,w134,w159,w205,w313] z) [w17,w23,w55,w134,w173,w205,w309] (n (n z [w17,w23,w55,w134,w177,w205,w309] z) [w17,w23,w55,w134,w177,w296,w313] z))) [w17,w23,w55,w134,w205,w296,w313] (n (n (n (n z [w17,w23,w55,w134,w205,w309] z) [w17,w23,w55,w134,w205,w313,w329] z) [w17,w23,w55,w134,w296,w313] (n (n z [w17,w23,w55,w158,w205,w238,w313] z) [w17,w23,w55,w177,w238,w296,w313] z)) [w17,w23,w55,w205,w238,w296,w313] (n (n (n z [w17,w23,w55,w238,w296,w313] z) [w17,w23,w56,w73,w105,w205,w238] z) [w17,w23,w57,w105,w134,w177,w205] (n z [w17,w23,w58,w73,w105,w205,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abaaaaa : t6abaaaaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6abaaaab := (n (n (n (n (n z [w17,w23,w59,w73,w105,w177,w249] z) [w17,w23,w59,w73,w146,w177,w205] z) [w17,w23,w60,w73,w105,w205,w238] (n (n z [w17,w23,w60,w105,w134,w177,w205] z) [w17,w23,w63,w73,w105,w205,w234] z)) [w17,w23,w63,w105,w131,w177,w205] (n (n (n z [w17,w23,w63,w105,w134,w205,w238] z) [w17,w23,w63,w105,w134,w205,w263] z) [w17,w23,w63,w105,w158,w205,w238] (n (n z [w17,w23,w65,w105,w134,w205,w263] z) [w17,w23,w65,w105,w158,w205,w238] z))) [w17,w23,w69,w105,w156,w205,w238] (n (n (n (n z [w17,w23,w73,w105,w134,w205,w260] z) [w17,w23,w73,w105,w156,w205,w238] z) [w17,w23,w73,w105,w205,w234,w260] (n (n z [w17,w23,w73,w105,w205,w238,w260] z) [w17,w23,w105,w131,w156,w177,w205] z)) [w17,w23,w105,w134,w156,w177,w205] (n (n (n z [w17,w23,w105,w134,w158,w205,w263] z) [w17,w23,w105,w134,w173,w205,w260] z) [w17,w23,w105,w134,w177,w205,w260] (n z [w17,w23,w105,w134,w205,w260] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abaaaab : t6abaaaab.all (blocked 5 t5) = true := by
  decide +kernel
def t6abaaaa := (n t6abaaaaa [w17,w23,w58,w105,w134,w177,w205] t6abaaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abaaaa : t6abaaaa.all (blocked 5 t5) = true := by
  simp only [t6abaaaa, ReplayTree.all, n, ht6abaaaaa, ht6abaaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abaaaba := (n (n (n (n (n z [w17,w23,w105,w156,w177,w205,w238] z) [w17,w23,w105,w156,w205,w238] z) [w17,w23,w105,w158,w159,w205,w238] (n (n z [w17,w23,w105,w158,w205,w238,w263] z) [w17,w24,w38,w55,w73,w205,w313] z)) [w17,w24,w38,w55,w105,w177,w296] (n (n (n z [w17,w24,w55,w73,w105,w205,w238] z) [w17,w25,w38,w55,w73,w205,w313] z) [w17,w25,w38,w55,w105,w177,w296] (n (n z [w17,w25,w55,w105,w134,w177,w205] z) [w17,w27,w55,w73,w105,w222,w238] z))) [w17,w27,w55,w73,w121,w205,w238] (n (n (n (n z [w17,w27,w55,w105,w134,w177,w222] z) [w17,w27,w55,w121,w134,w177,w205] z) [w17,w28,w38,w55,w73,w121,w173] (n (n z [w17,w28,w55,w73,w105,w222,w238] z) [w17,w28,w55,w121,w134,w177,w205] z)) [w17,w31,w38,w55,w73,w105,w173] (n (n (n z [w17,w31,w38,w55,w73,w205,w313] z) [w17,w31,w38,w55,w105,w177,w296] z) [w17,w31,w55,w73,w105,w205,w238] (n z [w17,w31,w55,w105,w134,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abaaaba : t6abaaaba.all (blocked 5 t5) = true := by
  decide +kernel
def t6abaaabb := (n (n (n (n (n z [w17,w32,w55,w73,w105,w222,w238] z) [w17,w32,w55,w121,w134,w177,w205] z) [w17,w35,w38,w55,w69,w177,w205] (n (n z [w17,w35,w38,w55,w73,w205,w313] z) [w17,w35,w38,w55,w105,w177,w296] z)) [w17,w35,w55,w73,w105,w205,w238] (n (n (n z [w17,w35,w55,w105,w134,w177,w205] z) [w17,w36,w55,w73,w105,w222,w238] z) [w17,w36,w55,w121,w134,w177,w205] (n (n z [w17,w36,w59,w73,w105,w177,w222] z) [w17,w36,w59,w73,w121,w177,w205] z))) [w17,w37,w55,w73,w105,w177,w222] (n (n (n (n z [w17,w37,w55,w73,w121,w177,w205] z) [w17,w38,w45,w55,w73,w205,w313] z) [w17,w38,w45,w55,w105,w177,w296] (n (n z [w17,w38,w55,w69,w94,w205,w313] z) [w17,w38,w55,w69,w105,w173,w222] z)) [w17,w38,w55,w69,w105,w177,w222] (n (n (n z [w17,w38,w55,w69,w105,w177,w305] z) [w17,w38,w55,w69,w105,w195,w222] z) [w17,w38,w55,w69,w105,w222,w238] (n z [w17,w38,w55,w69,w105,w222,w263] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abaaabb : t6abaaabb.all (blocked 5 t5) = true := by
  decide +kernel
def t6abaaab := (n t6abaaaba [w17,w32,w38,w55,w69,w177,w222] t6abaaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abaaab : t6abaaab.all (blocked 5 t5) = true := by
  simp only [t6abaaab, ReplayTree.all, n, ht6abaaaba, ht6abaaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abaaa := (n t6abaaaa [w17,w23,w105,w134,w205,w261,w263] t6abaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abaaa : t6abaaa.all (blocked 5 t5) = true := by
  simp only [t6abaaa, ReplayTree.all, n, ht6abaaaa, ht6abaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abaabaa := (n (n (n (n (n z [w17,w38,w55,w69,w107,w177,w222] z) [w17,w38,w55,w69,w121,w173,w205] z) [w17,w38,w55,w69,w121,w177,w205] (n (n z [w17,w38,w55,w69,w121,w177,w222] z) [w17,w38,w55,w69,w121,w177,w292] z)) [w17,w38,w55,w69,w121,w177,w296] (n (n (n z [w17,w38,w55,w69,w121,w195,w205] z) [w17,w38,w55,w69,w121,w205,w238] z) [w17,w38,w55,w69,w121,w205,w263] (n (n z [w17,w38,w55,w69,w121,w205,w279] z) [w17,w38,w55,w69,w121,w205,w313] z))) [w17,w38,w55,w69,w149,w177,w222] (n (n (n (n z [w17,w38,w55,w69,w177,w205,w336] z) [w17,w38,w55,w69,w177,w222,w313] z) [w17,w38,w55,w69,w177,w222,w329] (n (n z [w17,w38,w55,w69,w177,w222,w336] z) [w17,w38,w55,w69,w205,w222,w313] z)) [w17,w38,w55,w70,w105,w177,w222] (n (n (n z [w17,w38,w55,w70,w121,w177,w205] z) [w17,w38,w55,w71,w105,w177,w222] z) [w17,w38,w55,w71,w121,w177,w205] (n z [w17,w38,w55,w72,w105,w177,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abaabaa : t6abaabaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6abaabab := (n (n (n (n (n z [w17,w38,w55,w73,w94,w205,w313] z) [w17,w38,w55,w73,w103,w177,w222] z) [w17,w38,w55,w73,w105,w121,w204] (n (n z [w17,w38,w55,w73,w105,w173,w222] z) [w17,w38,w55,w73,w105,w173,w336] z)) [w17,w38,w55,w73,w105,w174,w222] (n (n (n z [w17,w38,w55,w73,w105,w175,w222] z) [w17,w38,w55,w73,w105,w176,w222] z) [w17,w38,w55,w73,w105,w177,w220] (n (n z [w17,w38,w55,w73,w105,w177,w221] z) [w17,w38,w55,w73,w105,w177,w222] z))) [w17,w38,w55,w73,w105,w177,w231] (n (n (n (n z [w17,w38,w55,w73,w105,w177,w254] z) [w17,w38,w55,w73,w105,w177,w305] z) [w17,w38,w55,w73,w105,w179,w222] (n (n z [w17,w38,w55,w73,w105,w180,w222] z) [w17,w38,w55,w73,w105,w181,w222] z)) [w17,w38,w55,w73,w105,w182,w222] (n (n (n z [w17,w38,w55,w73,w105,w183,w222] z) [w17,w38,w55,w73,w105,w184,w222] z) [w17,w38,w55,w73,w105,w189,w222] (n z [w17,w38,w55,w73,w105,w192,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abaabab : t6abaabab.all (blocked 5 t5) = true := by
  decide +kernel
def t6abaaba := (n t6abaabaa [w17,w38,w55,w72,w121,w177,w205] t6abaabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abaaba : t6abaaba.all (blocked 5 t5) = true := by
  simp only [t6abaaba, ReplayTree.all, n, ht6abaabaa, ht6abaabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abaabba := (n (n (n (n (n z [w17,w38,w55,w73,w105,w204,w220] z) [w17,w38,w55,w73,w105,w204,w222] z) [w17,w38,w55,w73,w105,w209,w222] (n (n z [w17,w38,w55,w73,w105,w220,w263] z) [w17,w38,w55,w73,w105,w222,w226] z)) [w17,w38,w55,w73,w105,w222,w232] (n (n (n z [w17,w38,w55,w73,w105,w222,w234] z) [w17,w38,w55,w73,w105,w222,w238] z) [w17,w38,w55,w73,w105,w222,w248] (n (n z [w17,w38,w55,w73,w105,w222,w260] z) [w17,w38,w55,w73,w105,w222,w263] z))) [w17,w38,w55,w73,w105,w222,w265] (n (n (n (n z [w17,w38,w55,w73,w105,w222,w271] z) [w17,w38,w55,w73,w105,w222,w279] z) [w17,w38,w55,w73,w106,w177,w222] (n (n z [w17,w38,w55,w73,w108,w177,w222] z) [w17,w38,w55,w73,w109,w177,w222] z)) [w17,w38,w55,w73,w110,w177,w222] (n (n (n z [w17,w38,w55,w73,w113,w177,w222] z) [w17,w38,w55,w73,w119,w177,w205] z) [w17,w38,w55,w73,w120,w177,w205] (n z [w17,w38,w55,w73,w121,w173,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abaabba : t6abaabba.all (blocked 5 t5) = true := by
  decide +kernel
def t6abaabbb := (n (n (n (n (n z [w17,w38,w55,w73,w121,w173,w222] z) [w17,w38,w55,w73,w121,w173,w251] z) [w17,w38,w55,w73,w121,w173,w296] (n (n z [w17,w38,w55,w73,w121,w173,w329] z) [w17,w38,w55,w73,w121,w173,w336] z)) [w17,w38,w55,w73,w121,w174,w205] (n (n (n z [w17,w38,w55,w73,w121,w175,w205] z) [w17,w38,w55,w73,w121,w176,w205] z) [w17,w38,w55,w73,w121,w177,w204] (n z [w17,w38,w55,w73,w121,w177,w205] z))) [w17,w38,w55,w73,w121,w177,w206] (n (n (n (n z [w17,w38,w55,w73,w121,w177,w207] z) [w17,w38,w55,w73,w121,w177,w208] z) [w17,w38,w55,w73,w121,w177,w211] (n (n z [w17,w38,w55,w73,w121,w177,w213] z) [w17,w38,w55,w73,w121,w177,w222] z)) [w17,w38,w55,w73,w121,w177,w229] (n (n (n z [w17,w38,w55,w73,w121,w177,w249] z) [w17,w38,w55,w73,w121,w177,w292] z) [w17,w38,w55,w73,w121,w177,w296] (n z [w17,w38,w55,w73,w121,w177,w307] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abaabbb : t6abaabbb.all (blocked 5 t5) = true := by
  decide +kernel
def t6abaabb := (n t6abaabba [w17,w38,w55,w73,w121,w173,w210] t6abaabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abaabb : t6abaabb.all (blocked 5 t5) = true := by
  simp only [t6abaabb, ReplayTree.all, n, ht6abaabba, ht6abaabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abaab := (n t6abaaba [w17,w38,w55,w73,w105,w195,w222] t6abaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abaab : t6abaab.all (blocked 5 t5) = true := by
  simp only [t6abaab, ReplayTree.all, n, ht6abaaba, ht6abaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abaa := (n t6abaaa [w17,w38,w55,w69,w105,w222,w279] t6abaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abaa : t6abaa.all (blocked 5 t5) = true := by
  simp only [t6abaa, ReplayTree.all, n, ht6abaaa, ht6abaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6ababaaa := (n (n (n (n (n z [w17,w38,w55,w73,w121,w179,w205] z) [w17,w38,w55,w73,w121,w180,w205] z) [w17,w38,w55,w73,w121,w181,w205] (n (n z [w17,w38,w55,w73,w121,w183,w205] z) [w17,w38,w55,w73,w121,w189,w205] z)) [w17,w38,w55,w73,w121,w192,w205] (n (n (n z [w17,w38,w55,w73,w121,w195,w205] z) [w17,w38,w55,w73,w121,w195,w222] z) [w17,w38,w55,w73,w121,w204] (n (n z [w17,w38,w55,w73,w121,w204,w205] z) [w17,w38,w55,w73,w121,w204,w263] z))) [w17,w38,w55,w73,w121,w205,w209] (n (n (n (n z [w17,w38,w55,w73,w121,w205,w226] z) [w17,w38,w55,w73,w121,w205,w232] z) [w17,w38,w55,w73,w121,w205,w234] (n (n z [w17,w38,w55,w73,w121,w205,w238] z) [w17,w38,w55,w73,w121,w205,w248] z)) [w17,w38,w55,w73,w121,w205,w260] (n (n (n z [w17,w38,w55,w73,w121,w205,w263] z) [w17,w38,w55,w73,w121,w205,w265] z) [w17,w38,w55,w73,w121,w205,w271] (n z [w17,w38,w55,w73,w121,w205,w279] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6ababaaa : t6ababaaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6ababaab := (n (n (n (n (n z [w17,w38,w55,w73,w121,w205,w313] z) [w17,w38,w55,w73,w121,w205,w321] z) [w17,w38,w55,w73,w121,w205,w352] (n (n z [w17,w38,w55,w73,w121,w205,w357] z) [w17,w38,w55,w73,w121,w222,w238] z)) [w17,w38,w55,w73,w121,w222,w263] (n (n (n z [w17,w38,w55,w73,w121,w263,w296] z) [w17,w38,w55,w73,w121,w296,w313] z) [w17,w38,w55,w73,w125,w177,w222] (n (n z [w17,w38,w55,w73,w127,w177,w205] z) [w17,w38,w55,w73,w146,w177,w222] z))) [w17,w38,w55,w73,w151,w177,w205] (n (n (n (n z [w17,w38,w55,w73,w173,w205,w322] z) [w17,w38,w55,w73,w173,w222,w309] z) [w17,w38,w55,w73,w173,w222,w313] (n (n z [w17,w38,w55,w73,w177,w205,w322] z) [w17,w38,w55,w73,w177,w222,w309] z)) [w17,w38,w55,w73,w177,w222,w313] (n (n (n z [w17,w38,w55,w73,w177,w222,w324] z) [w17,w38,w55,w73,w195,w222,w313] z) [w17,w38,w55,w73,w198,w205,w309] (n z [w17,w38,w55,w73,w198,w205,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6ababaab : t6ababaab.all (blocked 5 t5) = true := by
  decide +kernel
def t6ababaa := (n t6ababaaa [w17,w38,w55,w73,w121,w205,w309] t6ababaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6ababaa : t6ababaa.all (blocked 5 t5) = true := by
  simp only [t6ababaa, ReplayTree.all, n, ht6ababaaa, ht6ababaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abababa := (n (n (n (n (n z [w17,w38,w55,w73,w205,w222,w313] z) [w17,w38,w55,w73,w205,w309,w322] z) [w17,w38,w55,w73,w205,w313,w336] (n (n z [w17,w38,w55,w73,w210,w222,w313] z) [w17,w38,w55,w73,w215,w222,w313] z)) [w17,w38,w55,w73,w222,w238,w313] (n (n (n z [w17,w38,w55,w73,w222,w251,w313] z) [w17,w38,w55,w73,w222,w261,w313] z) [w17,w38,w55,w73,w222,w263,w313] (n (n z [w17,w38,w55,w73,w222,w280,w313] z) [w17,w38,w55,w73,w222,w296,w313] z))) [w17,w38,w55,w74,w105,w177,w222] (n (n (n (n z [w17,w38,w55,w75,w105,w177,w222] z) [w17,w38,w55,w75,w121,w177,w205] z) [w17,w38,w55,w76,w105,w177,w222] (n (n z [w17,w38,w55,w76,w121,w177,w205] z) [w17,w38,w55,w77,w105,w177,w222] z)) [w17,w38,w55,w77,w121,w177,w205] (n (n (n z [w17,w38,w55,w78,w121,w177,w205] z) [w17,w38,w55,w79,w105,w177,w222] z) [w17,w38,w55,w79,w121,w177,w205] (n z [w17,w38,w55,w80,w121,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abababa : t6abababa.all (blocked 5 t5) = true := by
  decide +kernel
def t6abababb := (n (n (n (n (n z [w17,w38,w55,w84,w121,w177,w205] z) [w17,w38,w55,w87,w105,w177,w222] z) [w17,w38,w55,w87,w121,w177,w205] (n (n z [w17,w38,w55,w91,w105,w173,w222] z) [w17,w38,w55,w91,w105,w177,w222] z)) [w17,w38,w55,w91,w105,w195,w222] (n (n (n z [w17,w38,w55,w91,w105,w222,w238] z) [w17,w38,w55,w91,w105,w222,w263] z) [w17,w38,w55,w91,w121,w173,w205] (n (n z [w17,w38,w55,w91,w121,w177,w205] z) [w17,w38,w55,w91,w121,w177,w222] z))) [w17,w38,w55,w91,w121,w177,w296] (n (n (n (n z [w17,w38,w55,w91,w121,w195,w205] z) [w17,w38,w55,w91,w121,w205,w238] z) [w17,w38,w55,w91,w121,w205,w263] (n (n z [w17,w38,w55,w91,w121,w205,w313] z) [w17,w38,w55,w94,w105,w177,w292] z)) [w17,w38,w55,w94,w105,w177,w296] (n (n (n z [w17,w38,w55,w94,w105,w205,w279] z) [w17,w38,w55,w100,w105,w177,w222] z) [w17,w38,w55,w100,w121,w177,w205] (n z [w17,w38,w55,w103,w105,w177,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abababb : t6abababb.all (blocked 5 t5) = true := by
  decide +kernel
def t6ababab := (n t6abababa [w17,w38,w55,w84,w105,w177,w222] t6abababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6ababab : t6ababab.all (blocked 5 t5) = true := by
  simp only [t6ababab, ReplayTree.all, n, ht6abababa, ht6abababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6ababa := (n t6ababaa [w17,w38,w55,w73,w205,w222,w309] t6ababab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6ababa : t6ababa.all (blocked 5 t5) = true := by
  simp only [t6ababa, ReplayTree.all, n, ht6ababaa, ht6ababab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6ababbaa := (n (n (n (n (n z [w17,w38,w55,w103,w121,w177,w205] z) [w17,w38,w55,w103,w158,w177,w222] z) [w17,w38,w55,w103,w177,w205,w222] (n (n z [w17,w38,w55,w103,w177,w222] z) [w17,w38,w55,w104,w105,w177,w222] z)) [w17,w38,w55,w104,w121,w177,w205] (n (n (n z [w17,w38,w55,w105,w121,w173,w296] z) [w17,w38,w55,w105,w121,w177,w292] z) [w17,w38,w55,w105,w121,w177,w296] (n (n z [w17,w38,w55,w105,w121,w263,w296] z) [w17,w38,w55,w105,w121,w296,w313] z))) [w17,w38,w55,w105,w128,w177,w222] (n (n (n (n z [w17,w38,w55,w105,w131,w177,w222] z) [w17,w38,w55,w105,w134,w173,w222] z) [w17,w38,w55,w105,w134,w177,w222] (n (n z [w17,w38,w55,w105,w134,w195,w222] z) [w17,w38,w55,w105,w134,w222,w238] z)) [w17,w38,w55,w105,w134,w222,w263] (n (n (n z [w17,w38,w55,w105,w144,w177,w222] z) [w17,w38,w55,w105,w156,w177,w222] z) [w17,w38,w55,w105,w158,w173,w222] (n z [w17,w38,w55,w105,w158,w177,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6ababbaa : t6ababbaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6ababbab := (n (n (n (n (n z [w17,w38,w55,w105,w158,w222,w238] z) [w17,w38,w55,w105,w158,w222,w263] z) [w17,w38,w55,w105,w161,w177,w222] (n (n z [w17,w38,w55,w105,w166,w177,w222] z) [w17,w38,w55,w105,w173,w198,w296] z)) [w17,w38,w55,w105,w173,w222,w278] (n (n (n z [w17,w38,w55,w105,w173,w222,w296] z) [w17,w38,w55,w105,w177,w198,w296] z) [w17,w38,w55,w105,w177,w222,w278] (n (n z [w17,w38,w55,w105,w177,w222,w292] z) [w17,w38,w55,w105,w177,w222,w296] z))) [w17,w38,w55,w105,w177,w222,w304] (n (n (n (n z [w17,w38,w55,w105,w177,w222,w349] z) [w17,w38,w55,w105,w177,w222,w355] z) [w17,w38,w55,w105,w177,w292,w305] (n (n z [w17,w38,w55,w105,w177,w296,w336] z) [w17,w38,w55,w105,w195,w222,w296] z)) [w17,w38,w55,w105,w198,w205,w278] (n (n (n z [w17,w38,w55,w105,w222,w238,w296] z) [w17,w38,w55,w105,w222,w263,w296] z) [w17,w38,w55,w105,w222,w296,w313] (n z [w17,w38,w55,w107,w121,w177,w296] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6ababbab : t6ababbab.all (blocked 5 t5) = true := by
  decide +kernel
def t6ababba := (n t6ababbaa [w17,w38,w55,w105,w158,w195,w222] t6ababbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6ababba : t6ababba.all (blocked 5 t5) = true := by
  simp only [t6ababba, ReplayTree.all, n, ht6ababbaa, ht6ababbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6ababbba := (n (n (n (n (n z [w17,w38,w55,w119,w158,w177,w205] z) [w17,w38,w55,w121,w128,w177,w205] z) [w17,w38,w55,w121,w131,w177,w205] (n (n z [w17,w38,w55,w121,w134,w173,w205] z) [w17,w38,w55,w121,w134,w177,w205] z)) [w17,w38,w55,w121,w134,w177,w222] (n (n (n z [w17,w38,w55,w121,w134,w177,w296] z) [w17,w38,w55,w121,w134,w195,w205] z) [w17,w38,w55,w121,w134,w205,w238] (n (n z [w17,w38,w55,w121,w134,w205,w263] z) [w17,w38,w55,w121,w134,w205,w313] z))) [w17,w38,w55,w121,w144,w177,w205] (n (n (n (n z [w17,w38,w55,w121,w149,w177,w296] z) [w17,w38,w55,w121,w156,w177,w205] z) [w17,w38,w55,w121,w158,w173,w205] (n (n z [w17,w38,w55,w121,w158,w177,w205] z) [w17,w38,w55,w121,w158,w177,w222] z)) [w17,w38,w55,w121,w158,w177,w296] (n (n (n z [w17,w38,w55,w121,w158,w195,w205] z) [w17,w38,w55,w121,w158,w205,w238] z) [w17,w38,w55,w121,w158,w205,w263] (n z [w17,w38,w55,w121,w158,w205,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6ababbba : t6ababbba.all (blocked 5 t5) = true := by
  decide +kernel
def t6ababbbb := (n (n (n (n (n z [w17,w38,w55,w121,w161,w177,w205] z) [w17,w38,w55,w121,w166,w177,w205] z) [w17,w38,w55,w121,w173,w205,w278] (n (n z [w17,w38,w55,w121,w177,w205,w278] z) [w17,w38,w55,w121,w177,w280,w296] z)) [w17,w38,w55,w121,w177,w296,w313] (n (n (n z [w17,w38,w55,w121,w205,w296,w313] z) [w17,w38,w55,w121,w296,w313] z) [w17,w38,w55,w158,w177,w222,w313] (n z [w17,w38,w55,w158,w205,w222,w313] z))) [w17,w38,w55,w177,w222,w296,w313] (n (n (n (n z [w17,w38,w55,w205,w222,w296,w313] z) [w17,w38,w55,w222,w296,w313] z) [w17,w38,w56,w73,w105,w177,w222] (n (n z [w17,w38,w56,w73,w121,w177,w205] z) [w17,w38,w57,w73,w105,w177,w222] z)) [w17,w38,w57,w73,w121,w177,w205] (n (n (n z [w17,w38,w58,w73,w105,w177,w222] z) [w17,w38,w58,w73,w121,w177,w205] z) [w17,w38,w60,w73,w105,w177,w222] (n z [w17,w38,w60,w73,w121,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6ababbbb : t6ababbbb.all (blocked 5 t5) = true := by
  decide +kernel
def t6ababbb := (n t6ababbba [w17,w38,w55,w121,w159,w177,w296] t6ababbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6ababbb : t6ababbb.all (blocked 5 t5) = true := by
  simp only [t6ababbb, ReplayTree.all, n, ht6ababbba, ht6ababbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6ababb := (n t6ababba [w17,w38,w55,w116,w121,w177,w296] t6ababbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6ababb : t6ababb.all (blocked 5 t5) = true := by
  simp only [t6ababb, ReplayTree.all, n, ht6ababba, ht6ababbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abab := (n t6ababa [w17,w38,w55,w103,w119,w177,w205] t6ababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abab : t6abab.all (blocked 5 t5) = true := by
  simp only [t6abab, ReplayTree.all, n, ht6ababa, ht6ababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6aba := (n t6abaa [w17,w38,w55,w73,w121,w178,w205] t6abab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6aba : t6aba.all (blocked 5 t5) = true := by
  simp only [t6aba, ReplayTree.all, n, ht6abaa, ht6abab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abbaaaa := (n (n (n (n (n z [w17,w38,w63,w69,w121,w177,w205] z) [w17,w38,w63,w73,w105,w173,w222] z) [w17,w38,w63,w73,w105,w177,w222] (n (n z [w17,w38,w63,w73,w105,w195,w222] z) [w17,w38,w63,w73,w105,w222,w238] z)) [w17,w38,w63,w73,w105,w222,w263] (n (n (n z [w17,w38,w63,w73,w105,w222,w271] z) [w17,w38,w63,w73,w121,w173,w205] z) [w17,w38,w63,w73,w121,w177,w205] (n (n z [w17,w38,w63,w73,w121,w177,w222] z) [w17,w38,w63,w73,w121,w195,w205] z))) [w17,w38,w63,w73,w121,w205,w238] (n (n (n (n z [w17,w38,w63,w73,w121,w205,w263] z) [w17,w38,w63,w73,w121,w205,w271] z) [w17,w38,w63,w73,w121,w205,w313] (n (n z [w17,w38,w63,w91,w105,w177,w222] z) [w17,w38,w63,w91,w121,w177,w205] z)) [w17,w38,w63,w105,w134,w177,w222] (n (n (n z [w17,w38,w63,w105,w158,w177,w222] z) [w17,w38,w63,w105,w166,w177,w222] z) [w17,w38,w63,w105,w177,w222,w296] (n z [w17,w38,w63,w121,w134,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbaaaa : t6abbaaaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6abbaaab := (n (n (n (n (n z [w17,w38,w63,w121,w166,w177,w205] z) [w17,w38,w65,w73,w105,w222,w263] z) [w17,w38,w65,w73,w121,w205,w263] (n (n z [w17,w38,w65,w105,w158,w177,w222] z) [w17,w38,w65,w121,w158,w177,w205] z)) [w17,w38,w69,w105,w156,w177,w222] (n (n (n z [w17,w38,w69,w121,w156,w177,w205] z) [w17,w38,w73,w105,w121,w205,w260] z) [w17,w38,w73,w105,w156,w177,w222] (n (n z [w17,w38,w73,w105,w158,w222,w263] z) [w17,w38,w73,w105,w173,w222,w260] z))) [w17,w38,w73,w105,w177,w222,w260] (n (n (n (n z [w17,w38,w73,w105,w198,w205,w260] z) [w17,w38,w73,w105,w205,w222,w260] z) [w17,w38,w73,w105,w222,w260] (n (n z [w17,w38,w73,w105,w222,w261,w263] z) [w17,w38,w73,w105,w222,w263,w273] z)) [w17,w38,w73,w121,w156,w177,w205] (n (n (n z [w17,w38,w73,w121,w158,w205,w263] z) [w17,w38,w73,w121,w173,w205,w260] z) [w17,w38,w73,w121,w177,w205,w260] (n z [w17,w38,w73,w121,w205,w260] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbaaab : t6abbaaab.all (blocked 5 t5) = true := by
  decide +kernel
def t6abbaaa := (n t6abbaaaa [w17,w38,w63,w121,w158,w177,w205] t6abbaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbaaa : t6abbaaa.all (blocked 5 t5) = true := by
  simp only [t6abbaaa, ReplayTree.all, n, ht6abbaaaa, ht6abbaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abbaaba := (n (n (n (n (n z [w17,w38,w94,w105,w156,w177,w205] z) [w17,w38,w105,w121,w156,w177,w205] z) [w17,w38,w105,w121,w158,w205,w263] (n (n z [w17,w38,w105,w156,w177,w205,w222] z) [w17,w38,w105,w156,w177,w222] z)) [w17,w38,w105,w158,w159,w177,w222] (n (n (n z [w17,w38,w105,w158,w177,w222,w263] z) [w17,w38,w105,w158,w205,w222,w263] z) [w17,w38,w105,w158,w222,w263] (n (n z [w17,w38,w121,w156,w177,w205] z) [w17,w38,w121,w158,w159,w177,w205] z))) [w17,w38,w121,w158,w169,w177,w205] (n (n (n (n z [w17,w38,w121,w158,w177,w205,w263] z) [w17,w38,w121,w158,w205,w263] z) [w17,w39,w55,w73,w121,w177,w205] (n (n z [w17,w40,w55,w73,w105,w177,w222] z) [w17,w40,w55,w73,w121,w177,w205] z)) [w17,w41,w55,w73,w105,w177,w222] (n (n (n z [w17,w42,w55,w73,w105,w177,w222] z) [w17,w42,w55,w73,w121,w177,w205] z) [w17,w45,w55,w73,w105,w205,w238] (n z [w17,w45,w55,w105,w134,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbaaba : t6abbaaba.all (blocked 5 t5) = true := by
  decide +kernel
def t6abbaabb := (n (n (n (n (n z [w17,w46,w55,w73,w105,w177,w222] z) [w17,w46,w55,w73,w121,w177,w205] z) [w17,w47,w55,w73,w105,w222,w238] (n (n z [w17,w47,w55,w73,w121,w205,w238] z) [w17,w47,w55,w105,w134,w177,w222] z)) [w17,w47,w55,w121,w134,w177,w205] (n (n (n z [w17,w47,w58,w73,w105,w177,w205] z) [w17,w50,w55,w73,w105,w222,w238] z) [w17,w50,w55,w73,w121,w205,w238] (n (n z [w17,w50,w55,w105,w134,w177,w222] z) [w17,w50,w55,w121,w134,w177,w205] z))) [w17,w51,w55,w73,w105,w177,w222] (n (n (n (n z [w17,w51,w55,w73,w121,w177,w205] z) [w17,w53,w55,w73,w105,w177,w222] z) [w17,w53,w55,w73,w121,w177,w205] (n (n z [w17,w55,w59,w73,w105,w222,w238] z) [w17,w55,w59,w73,w121,w205,w238] z)) [w17,w55,w59,w105,w134,w177,w222] (n (n (n z [w17,w55,w59,w121,w134,w177,w205] z) [w17,w55,w63,w73,w105,w222,w238] z) [w17,w55,w63,w121,w134,w177,w205] (n z [w17,w55,w65,w73,w105,w222,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbaabb : t6abbaabb.all (blocked 5 t5) = true := by
  decide +kernel
def t6abbaab := (n t6abbaaba [w17,w45,w59,w73,w105,w177,w205] t6abbaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbaab : t6abbaab.all (blocked 5 t5) = true := by
  simp only [t6abbaab, ReplayTree.all, n, ht6abbaaba, ht6abbaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abbaa := (n t6abbaaa [w17,w38,w73,w121,w205,w261,w263] t6abbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbaa : t6abbaa.all (blocked 5 t5) = true := by
  simp only [t6abbaa, ReplayTree.all, n, ht6abbaaa, ht6abbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abbabaa := (n (n (n (n (n z [w17,w55,w65,w105,w134,w177,w222] z) [w17,w55,w65,w121,w134,w177,w205] z) [w17,w55,w69,w73,w105,w222,w238] (n (n z [w17,w55,w69,w94,w105,w205,w238] z) [w17,w55,w69,w105,w131,w177,w222] z)) [w17,w55,w69,w105,w177,w222,w238] (n (n (n z [w17,w55,w69,w105,w205,w222,w238] z) [w17,w55,w69,w105,w222,w238] z) [w17,w55,w69,w121,w131,w177,w205] (n (n z [w17,w55,w69,w121,w134,w177,w205] z) [w17,w55,w73,w91,w105,w222,w238] z))) [w17,w55,w73,w94,w105,w205,w238] (n (n (n (n z [w17,w55,w73,w96,w105,w222,w238] z) [w17,w55,w73,w96,w121,w205,w238] z) [w17,w55,w73,w105,w107,w222,w238] (n (n z [w17,w55,w73,w105,w116,w222,w238] z) [w17,w55,w73,w105,w121,w205,w234] z)) [w17,w55,w73,w105,w121,w222,w238] (n (n (n z [w17,w55,w73,w105,w131,w177,w222] z) [w17,w55,w73,w105,w134,w222,w238] z) [w17,w55,w73,w105,w149,w222,w238] (n z [w17,w55,w73,w105,w158,w222,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbabaa : t6abbabaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6abbabab := (n (n (n (n (n z [w17,w55,w73,w105,w173,w222,w234] z) [w17,w55,w73,w105,w173,w222,w238] z) [w17,w55,w73,w105,w177,w222,w234] (n (n z [w17,w55,w73,w105,w177,w222,w238] z) [w17,w55,w73,w105,w182,w222,w238] z)) [w17,w55,w73,w105,w195,w222,w238] (n (n (n z [w17,w55,w73,w105,w198,w205,w234] z) [w17,w55,w73,w105,w198,w205,w238] z) [w17,w55,w73,w105,w201,w222,w238] (n (n z [w17,w55,w73,w105,w205,w222,w234] z) [w17,w55,w73,w105,w205,w222,w238] z))) [w17,w55,w73,w105,w210,w222,w238] (n (n (n (n z [w17,w55,w73,w105,w215,w222,w238] z) [w17,w55,w73,w105,w222,w222,w238] z) [w17,w55,w73,w105,w222,w223,w238] (n (n z [w17,w55,w73,w105,w222,w224,w238] z) [w17,w55,w73,w105,w222,w234] z)) [w17,w55,w73,w105,w222,w238] (n (n (n z [w17,w55,w73,w105,w222,w238,w238] z) [w17,w55,w73,w105,w222,w238,w246] z) [w17,w55,w73,w105,w222,w238,w248] (n z [w17,w55,w73,w105,w222,w238,w251] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbabab : t6abbabab.all (blocked 5 t5) = true := by
  decide +kernel
def t6abbaba := (n t6abbabaa [w17,w55,w73,w105,w159,w222,w238] t6abbabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbaba : t6abbaba.all (blocked 5 t5) = true := by
  simp only [t6abbaba, ReplayTree.all, n, ht6abbabaa, ht6abbabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abbabba := (n (n (n (n (n z [w17,w55,w73,w105,w222,w238,w256] z) [w17,w55,w73,w105,w222,w238,w258] z) [w17,w55,w73,w105,w222,w238,w261] (n (n z [w17,w55,w73,w105,w222,w238,w263] z) [w17,w55,w73,w105,w222,w238,w265] z)) [w17,w55,w73,w105,w222,w238,w273] (n (n (n z [w17,w55,w73,w105,w222,w238,w280] z) [w17,w55,w73,w105,w222,w238,w296] z) [w17,w55,w73,w105,w222,w238,w307] (n (n z [w17,w55,w73,w105,w222,w238,w313] z) [w17,w55,w73,w105,w222,w238,w329] z))) [w17,w55,w73,w105,w222,w238,w336] (n (n (n (n z [w17,w55,w73,w105,w222,w238,w340] z) [w17,w55,w73,w105,w222,w238,w352] z) [w17,w55,w73,w121,w131,w177,w205] (n (n z [w17,w55,w73,w121,w134,w173,w205] z) [w17,w55,w73,w121,w134,w177,w205] z)) [w17,w55,w73,w121,w134,w177,w222] (n (n (n z [w17,w55,w73,w121,w134,w177,w296] z) [w17,w55,w73,w121,w134,w195,w205] z) [w17,w55,w73,w121,w134,w205,w238] (n z [w17,w55,w73,w121,w134,w205,w263] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbabba : t6abbabba.all (blocked 5 t5) = true := by
  decide +kernel
def t6abbabbb := (n (n (n (n (n z [w17,w55,w73,w121,w173,w205,w234] z) [w17,w55,w73,w121,w177,w205,w234] z) [w17,w55,w73,w121,w177,w222,w238] (n (n z [w17,w55,w73,w121,w205,w222,w238] z) [w17,w55,w73,w121,w205,w234] z)) [w17,w55,w73,w121,w205,w238,w251] (n (n (n z [w17,w55,w73,w121,w222,w238] z) [w17,w55,w73,w177,w222,w238,w313] z) [w17,w55,w73,w205,w222,w238,w313] (n z [w17,w55,w73,w222,w238,w313] z))) [w17,w55,w78,w121,w134,w177,w205] (n (n (n (n z [w17,w55,w91,w105,w177,w222,w238] z) [w17,w55,w91,w105,w205,w222,w238] z) [w17,w55,w91,w105,w222,w238] (n (n z [w17,w55,w91,w121,w134,w177,w205] z) [w17,w55,w94,w105,w131,w177,w205] z)) [w17,w55,w94,w105,w134,w177,w205] (n (n (n z [w17,w55,w96,w121,w134,w177,w205] z) [w17,w55,w105,w121,w131,w177,w205] z) [w17,w55,w105,w121,w134,w173,w205] (n z [w17,w55,w105,w121,w134,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbabbb : t6abbabbb.all (blocked 5 t5) = true := by
  decide +kernel
def t6abbabb := (n t6abbabba [w17,w55,w73,w121,w134,w205,w313] t6abbabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbabb : t6abbabb.all (blocked 5 t5) = true := by
  simp only [t6abbabb, ReplayTree.all, n, ht6abbabba, ht6abbabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abbab := (n t6abbaba [w17,w55,w73,w105,w222,w238,w253] t6abbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbab : t6abbab.all (blocked 5 t5) = true := by
  simp only [t6abbab, ReplayTree.all, n, ht6abbaba, ht6abbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abba := (n t6abbaa [w17,w55,w65,w73,w121,w205,w238] t6abbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abba : t6abba.all (blocked 5 t5) = true := by
  simp only [t6abba, ReplayTree.all, n, ht6abbaa, ht6abbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abbbaaa := (n (n (n (n (n z [w17,w55,w105,w121,w134,w177,w296] z) [w17,w55,w105,w121,w134,w195,w205] z) [w17,w55,w105,w121,w134,w205,w238] (n (n z [w17,w55,w105,w121,w134,w205,w263] z) [w17,w55,w105,w121,w134,w205,w313] z)) [w17,w55,w105,w131,w177,w205,w222] (n (n (n z [w17,w55,w105,w131,w177,w222] z) [w17,w55,w105,w134,w149,w177,w222] z) [w17,w55,w105,w134,w173,w198,w205] (n (n z [w17,w55,w105,w134,w177,w198,w205] z) [w17,w55,w105,w134,w177,w201,w222] z))) [w17,w55,w105,w134,w177,w222,w238] (n (n (n (n z [w17,w55,w105,w134,w205,w222,w238] z) [w17,w55,w105,w134,w222,w238] z) [w17,w55,w105,w158,w177,w222,w238] (n (n z [w17,w55,w105,w158,w205,w222,w238] z) [w17,w55,w105,w158,w222,w238] z)) [w17,w55,w105,w177,w222,w238,w296] (n (n (n z [w17,w55,w105,w205,w222,w238,w296] z) [w17,w55,w105,w222,w238,w296] z) [w17,w55,w107,w121,w134,w177,w205] (n z [w17,w55,w116,w121,w134,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbbaaa : t6abbbaaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6abbbaab := (n (n (n (n (n z [w17,w55,w121,w122,w134,w177,w205] z) [w17,w55,w121,w123,w134,w177,w205] z) [w17,w55,w121,w131,w177,w205] (n (n z [w17,w55,w121,w134,w134,w177,w205] z) [w17,w55,w121,w134,w140,w177,w205] z)) [w17,w55,w121,w134,w144,w177,w205] (n (n (n z [w17,w55,w121,w134,w149,w177,w205] z) [w17,w55,w121,w134,w150,w177,w205] z) [w17,w55,w121,w134,w154,w177,w205] (n (n z [w17,w55,w121,w134,w155,w177,w205] z) [w17,w55,w121,w134,w158,w177,w205] z))) [w17,w55,w121,w134,w159,w177,w205] (n (n (n (n z [w17,w55,w121,w134,w161,w177,w205] z) [w17,w55,w121,w134,w169,w177,w205] z) [w17,w55,w121,w134,w173,w177,w205] (n (n z [w17,w55,w121,w134,w173,w205] z) [w17,w55,w121,w134,w177,w195,w205] z)) [w17,w55,w121,w134,w177,w201,w205] (n (n (n z [w17,w55,w121,w134,w177,w205] z) [w17,w55,w121,w134,w177,w205,w210] z) [w17,w55,w121,w134,w177,w205,w215] (n z [w17,w55,w121,w134,w177,w205,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbbaab : t6abbbaab.all (blocked 5 t5) = true := by
  decide +kernel
def t6abbbaa := (n t6abbbaaa [w17,w55,w121,w121,w134,w177,w205] t6abbbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbbaa : t6abbbaa.all (blocked 5 t5) = true := by
  simp only [t6abbbaa, ReplayTree.all, n, ht6abbbaaa, ht6abbbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abbbaba := (n (n (n (n (n z [w17,w55,w121,w134,w177,w205,w251] z) [w17,w55,w121,w134,w177,w205,w261] z) [w17,w55,w121,w134,w177,w205,w263] (n (n z [w17,w55,w121,w134,w177,w205,w280] z) [w17,w55,w121,w134,w177,w205,w296] z)) [w17,w55,w121,w134,w177,w205,w313] (n (n (n z [w17,w55,w121,w134,w177,w205,w324] z) [w17,w55,w121,w134,w177,w205,w329] z) [w17,w55,w121,w134,w177,w205,w336] (n (n z [w17,w55,w121,w134,w177,w205,w340] z) [w17,w55,w121,w134,w177,w205,w349] z))) [w17,w55,w121,w134,w177,w222] (n (n (n (n z [w17,w55,w121,w134,w177,w296] z) [w17,w55,w121,w134,w195,w205] z) [w17,w55,w121,w134,w205,w238] (n (n z [w17,w55,w121,w134,w205,w263] z) [w17,w55,w121,w134,w205,w313] z)) [w18,w23,w38,w55,w73,w205,w313] (n (n (n z [w18,w23,w38,w55,w105,w177,w296] z) [w18,w23,w55,w73,w105,w205,w238] z) [w18,w23,w55,w105,w134,w177,w205] (n z [w18,w38,w55,w73,w121,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbbaba : t6abbbaba.all (blocked 5 t5) = true := by
  decide +kernel
def t6abbbabb := (n (n (n (n (n z [w19,w23,w38,w55,w105,w177,w296] z) [w19,w23,w55,w73,w105,w205,w238] z) [w19,w23,w55,w105,w134,w177,w205] (n (n z [w19,w38,w55,w73,w105,w177,w222] z) [w19,w38,w55,w73,w121,w177,w205] z)) [w20,w23,w38,w55,w73,w205,w313] (n (n (n z [w20,w23,w38,w55,w105,w177,w296] z) [w20,w23,w55,w73,w105,w205,w238] z) [w20,w23,w55,w105,w134,w177,w205] (n z [w20,w38,w55,w73,w105,w177,w222] z))) [w21,w23,w38,w55,w73,w205,w313] (n (n (n (n z [w21,w23,w38,w55,w105,w177,w296] z) [w21,w23,w55,w73,w105,w205,w238] z) [w21,w23,w55,w105,w134,w177,w205] (n (n z [w21,w38,w55,w73,w105,w177,w222] z) [w21,w38,w55,w73,w121,w177,w205] z)) [w22,w23,w38,w55,w73,w205,w313] (n (n (n z [w22,w23,w38,w55,w105,w177,w296] z) [w22,w23,w55,w73,w105,w205,w238] z) [w22,w23,w55,w105,w134,w177,w205] (n z [w22,w36,w55,w73,w105,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbbabb : t6abbbabb.all (blocked 5 t5) = true := by
  decide +kernel
def t6abbbab := (n t6abbbaba [w19,w23,w38,w55,w73,w205,w313] t6abbbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbbab : t6abbbab.all (blocked 5 t5) = true := by
  simp only [t6abbbab, ReplayTree.all, n, ht6abbbaba, ht6abbbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abbba := (n t6abbbaa [w17,w55,w121,w134,w177,w205,w238] t6abbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbba : t6abbba.all (blocked 5 t5) = true := by
  simp only [t6abbba, ReplayTree.all, n, ht6abbbaa, ht6abbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abbbbaa := (n (n (n (n (n z [w22,w38,w50,w55,w105,w177,w296] z) [w22,w38,w55,w69,w105,w177,w205] z) [w22,w38,w55,w73,w105,w173,w205] (n (n z [w22,w38,w55,w73,w105,w177,w205] z) [w22,w38,w55,w73,w105,w177,w221] z)) [w22,w38,w55,w73,w105,w177,w222] (n (n (n z [w22,w38,w55,w73,w105,w177,w296] z) [w22,w38,w55,w73,w105,w195,w205] z) [w22,w38,w55,w73,w105,w200,w205] (n (n z [w22,w38,w55,w73,w105,w205,w238] z) [w22,w38,w55,w73,w105,w205,w248] z))) [w22,w38,w55,w73,w105,w205,w263] (n (n (n (n z [w22,w38,w55,w73,w105,w205,w313] z) [w22,w38,w55,w73,w120,w177,w205] z) [w22,w38,w55,w73,w121,w177,w205] (n (n z [w22,w38,w55,w73,w177,w205,w313] z) [w22,w38,w55,w73,w205,w313] z)) [w22,w38,w55,w91,w105,w177,w205] (n (n (n z [w22,w38,w55,w95,w105,w177,w205] z) [w22,w38,w55,w105,w134,w177,w205] z) [w22,w38,w55,w105,w144,w177,w205] (n z [w22,w38,w55,w105,w158,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbbbaa : t6abbbbaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6abbbbab := (n (n (n (n (n z [w22,w38,w55,w105,w177,w296] z) [w22,w38,w63,w73,w105,w177,w205] z) [w22,w38,w64,w73,w105,w177,w205] (n (n z [w22,w46,w55,w73,w105,w177,w205] z) [w22,w47,w55,w73,w105,w177,w205] z)) [w22,w50,w55,w73,w105,w205,w238] (n (n (n z [w22,w50,w55,w105,w134,w177,w205] z) [w22,w55,w73,w105,w134,w177,w205] z) [w22,w55,w73,w105,w149,w177,w205] (n (n z [w22,w55,w73,w105,w177,w205,w238] z) [w22,w55,w73,w105,w177,w205,w251] z))) [w22,w55,w73,w105,w205,w238] (n (n (n (n z [w22,w55,w73,w105,w205,w238,w248] z) [w22,w55,w105,w134,w144,w177,w205] z) [w22,w55,w105,w134,w177,w205] (n (n z [w23,w26,w38,w55,w73,w205,w313] z) [w23,w26,w38,w55,w105,w177,w296] z)) [w23,w26,w55,w73,w105,w205,w238] (n (n (n z [w23,w26,w55,w105,w134,w177,w205] z) [w23,w27,w55,w91,w105,w205,w238] z) [w23,w27,w55,w105,w134,w195,w205] (n z [w23,w28,w38,w55,w91,w105,w173] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbbbab : t6abbbbab.all (blocked 5 t5) = true := by
  decide +kernel
def t6abbbba := (n t6abbbbaa [w22,w38,w55,w105,w177,w205,w296] t6abbbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbbba : t6abbbba.all (blocked 5 t5) = true := by
  simp only [t6abbbba, ReplayTree.all, n, ht6abbbbaa, ht6abbbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abbbbba := (n (n (n (n (n z [w23,w28,w38,w63,w105,w177,w296] z) [w23,w28,w38,w91,w105,w177,w261] z) [w23,w28,w55,w91,w105,w205,w238] (n (n z [w23,w28,w55,w105,w134,w195,w205] z) [w23,w30,w38,w55,w73,w205,w313] z)) [w23,w30,w38,w55,w105,w177,w296] (n (n (n z [w23,w30,w55,w73,w105,w205,w238] z) [w23,w30,w55,w105,w134,w177,w205] z) [w23,w32,w38,w55,w69,w195,w205] (n (n z [w23,w32,w38,w63,w69,w177,w205] z) [w23,w32,w38,w63,w73,w205,w313] z))) [w23,w32,w38,w73,w159,w195,w205] (n (n (n (n z [w23,w32,w55,w91,w105,w205,w238] z) [w23,w32,w55,w105,w134,w195,w205] z) [w23,w34,w38,w55,w73,w205,w313] (n (n z [w23,w34,w38,w55,w105,w177,w296] z) [w23,w34,w55,w73,w105,w205,w238] z)) [w23,w34,w55,w105,w134,w177,w205] (n (n (n z [w23,w36,w50,w55,w73,w205,w313] z) [w23,w36,w50,w55,w105,w177,w296] z) [w23,w36,w55,w73,w105,w205,w248] (n z [w23,w36,w55,w91,w105,w205,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbbbba : t6abbbbba.all (blocked 5 t5) = true := by
  decide +kernel
def t6abbbbbb := (n (n (n (n (n z [w23,w36,w55,w105,w144,w177,w205] z) [w23,w36,w59,w73,w105,w195,w205] z) [w23,w36,w59,w91,w105,w177,w205] (n (n z [w23,w36,w63,w73,w105,w205,w238] z) [w23,w36,w63,w105,w134,w177,w205] z)) [w23,w36,w68,w73,w105,w177,w205] (n (n (n z [w23,w37,w55,w73,w105,w195,w205] z) [w23,w37,w55,w91,w105,w177,w205] z) [w23,w37,w63,w73,w105,w177,w205] (n z [w23,w38,w43,w55,w73,w205,w313] z))) [w23,w38,w43,w55,w105,w177,w296] (n (n (n (n z [w23,w38,w46,w55,w73,w205,w313] z) [w23,w38,w46,w55,w105,w177,w296] z) [w23,w38,w50,w55,w69,w205,w313] (n (n z [w23,w38,w50,w55,w73,w105,w204] z) [w23,w38,w50,w55,w73,w205,w309] z)) [w23,w38,w50,w55,w73,w205,w313] (n (n (n z [w23,w38,w50,w55,w73,w296,w313] z) [w23,w38,w50,w55,w103,w177,w205] z) [w23,w38,w50,w55,w105,w173,w296] (n z [w23,w38,w50,w55,w105,w177,w292] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbbbbb : t6abbbbbb.all (blocked 5 t5) = true := by
  decide +kernel
def t6abbbbb := (n t6abbbbba [w23,w36,w55,w105,w134,w195,w205] t6abbbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbbbb : t6abbbbb.all (blocked 5 t5) = true := by
  simp only [t6abbbbb, ReplayTree.all, n, ht6abbbbba, ht6abbbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abbbb := (n t6abbbba [w23,w28,w38,w63,w73,w105,w173] t6abbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbbb : t6abbbb.all (blocked 5 t5) = true := by
  simp only [t6abbbb, ReplayTree.all, n, ht6abbbba, ht6abbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abbb := (n t6abbba [w22,w38,w50,w55,w73,w205,w313] t6abbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abbb : t6abbb.all (blocked 5 t5) = true := by
  simp only [t6abbb, ReplayTree.all, n, ht6abbba, ht6abbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6abb := (n t6abba [w17,w55,w105,w121,w134,w177,w222] t6abbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6abb : t6abb.all (blocked 5 t5) = true := by
  simp only [t6abb, ReplayTree.all, n, ht6abba, ht6abbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6ab := (n t6aba [w17,w38,w63,w69,w105,w177,w222] t6abb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6ab : t6ab.all (blocked 5 t5) = true := by
  simp only [t6ab, ReplayTree.all, n, ht6aba, ht6abb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6a := (n t6aa [w17,w23,w55,w121,w134,w205,w238] t6ab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6a : t6a.all (blocked 5 t5) = true := by
  simp only [t6a, ReplayTree.all, n, ht6aa, ht6ab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baaaaaa := (n (n (n (n (n z [w23,w38,w50,w55,w105,w263,w296] z) [w23,w38,w50,w55,w105,w296,w313] z) [w23,w38,w50,w55,w158,w205,w313] (n (n z [w23,w38,w50,w55,w177,w296,w313] z) [w23,w38,w50,w55,w205,w296,w313] z)) [w23,w38,w50,w55,w296,w313] (n (n (n z [w23,w38,w50,w73,w105,w205,w260] z) [w23,w38,w50,w105,w156,w177,w205] z) [w23,w38,w50,w105,w158,w205,w263] (n (n z [w23,w38,w55,w60,w73,w205,w313] z) [w23,w38,w55,w60,w105,w177,w296] z))) [w23,w38,w55,w63,w69,w205,w313] (n (n (n (n z [w23,w38,w55,w63,w73,w105,w204] z) [w23,w38,w55,w63,w73,w205,w309] z) [w23,w38,w55,w63,w73,w205,w313] (n (n z [w23,w38,w55,w63,w73,w296,w313] z) [w23,w38,w55,w63,w103,w177,w205] z)) [w23,w38,w55,w63,w105,w173,w296] (n (n (n z [w23,w38,w55,w63,w105,w177,w292] z) [w23,w38,w55,w63,w105,w177,w296] z) [w23,w38,w55,w63,w105,w263,w296] (n z [w23,w38,w55,w63,w105,w296,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baaaaaa : t6baaaaaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6baaaaab := (n (n (n (n (n z [w23,w38,w55,w63,w177,w296,w313] z) [w23,w38,w55,w63,w205,w296,w313] z) [w23,w38,w55,w63,w296,w313] (n (n z [w23,w38,w55,w68,w73,w205,w313] z) [w23,w38,w55,w68,w105,w177,w296] z)) [w23,w38,w55,w69,w87,w205,w313] (n (n (n z [w23,w38,w55,w69,w91,w205,w313] z) [w23,w38,w55,w69,w105,w189,w205] z) [w23,w38,w55,w69,w105,w192,w205] (n (n z [w23,w38,w55,w69,w105,w195,w205] z) [w23,w38,w55,w69,w105,w195,w222] z))) [w23,w38,w55,w69,w105,w195,w292] (n (n (n (n z [w23,w38,w55,w69,w105,w205,w248] z) [w23,w38,w55,w69,w105,w205,w271] z) [w23,w38,w55,w69,w105,w205,w288] (n (n z [w23,w38,w55,w69,w107,w195,w205] z) [w23,w38,w55,w69,w121,w195,w205] z)) [w23,w38,w55,w69,w149,w195,w205] (n (n (n z [w23,w38,w55,w69,w195,w205,w313] z) [w23,w38,w55,w69,w195,w205,w329] z) [w23,w38,w55,w70,w105,w195,w205] (n z [w23,w38,w55,w71,w105,w195,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baaaaab : t6baaaaab.all (blocked 5 t5) = true := by
  decide +kernel
def t6baaaaa := (n t6baaaaaa [w23,w38,w55,w63,w158,w205,w313] t6baaaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baaaaa : t6baaaaa.all (blocked 5 t5) = true := by
  simp only [t6baaaaa, ReplayTree.all, n, ht6baaaaaa, ht6baaaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baaaaba := (n (n (n (n (n z [w23,w38,w55,w73,w84,w205,w313] z) [w23,w38,w55,w73,w87,w205,w313] z) [w23,w38,w55,w73,w91,w105,w204] (n (n z [w23,w38,w55,w73,w91,w205,w309] z) [w23,w38,w55,w73,w91,w205,w313] z)) [w23,w38,w55,w73,w91,w296,w313] (n (n (n z [w23,w38,w55,w73,w103,w195,w205] z) [w23,w38,w55,w73,w105,w184,w205] z) [w23,w38,w55,w73,w105,w184,w222] (n (n z [w23,w38,w55,w73,w105,w189,w205] z) [w23,w38,w55,w73,w105,w189,w222] z))) [w23,w38,w55,w73,w105,w189,w251] (n (n (n (n z [w23,w38,w55,w73,w105,w189,w329] z) [w23,w38,w55,w73,w105,w190,w205] z) [w23,w38,w55,w73,w105,w191,w205] (n (n z [w23,w38,w55,w73,w105,w192,w205] z) [w23,w38,w55,w73,w105,w192,w213] z)) [w23,w38,w55,w73,w105,w192,w222] (n (n (n z [w23,w38,w55,w73,w105,w192,w296] z) [w23,w38,w55,w73,w105,w193,w205] z) [w23,w38,w55,w73,w105,w194,w205] (n z [w23,w38,w55,w73,w105,w195,w204] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baaaaba : t6baaaaba.all (blocked 5 t5) = true := by
  decide +kernel
def t6baaaabb := (n (n (n (n (n z [w23,w38,w55,w73,w105,w195,w206] z) [w23,w38,w55,w73,w105,w195,w207] z) [w23,w38,w55,w73,w105,w195,w211] (n (n z [w23,w38,w55,w73,w105,w195,w213] z) [w23,w38,w55,w73,w105,w195,w222] z)) [w23,w38,w55,w73,w105,w195,w229] (n (n (n z [w23,w38,w55,w73,w105,w195,w249] z) [w23,w38,w55,w73,w105,w195,w292] z) [w23,w38,w55,w73,w105,w196,w205] (n (n z [w23,w38,w55,w73,w105,w200,w205] z) [w23,w38,w55,w73,w105,w202,w205] z))) [w23,w38,w55,w73,w105,w204,w214] (n (n (n (n z [w23,w38,w55,w73,w105,w204,w271] z) [w23,w38,w55,w73,w105,w205,w214] z) [w23,w38,w55,w73,w105,w205,w217] (n (n z [w23,w38,w55,w73,w105,w205,w228] z) [w23,w38,w55,w73,w105,w205,w240] z)) [w23,w38,w55,w73,w105,w205,w244] (n (n (n z [w23,w38,w55,w73,w105,w205,w245] z) [w23,w38,w55,w73,w105,w205,w248] z) [w23,w38,w55,w73,w105,w205,w268] (n z [w23,w38,w55,w73,w105,w205,w270] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baaaabb : t6baaaabb.all (blocked 5 t5) = true := by
  decide +kernel
def t6baaaab := (n t6baaaaba [w23,w38,w55,w73,w105,w195,w205] t6baaaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baaaab : t6baaaab.all (blocked 5 t5) = true := by
  simp only [t6baaaab, ReplayTree.all, n, ht6baaaaba, ht6baaaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baaaa := (n t6baaaaa [w23,w38,w55,w72,w105,w195,w205] t6baaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baaaa : t6baaaa.all (blocked 5 t5) = true := by
  simp only [t6baaaa, ReplayTree.all, n, ht6baaaaa, ht6baaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baaabaa := (n (n (n (n (n z [w23,w38,w55,w73,w105,w205,w276] z) [w23,w38,w55,w73,w105,w205,w288] z) [w23,w38,w55,w73,w105,w222,w248] (n (n z [w23,w38,w55,w73,w105,w222,w271] z) [w23,w38,w55,w73,w106,w195,w205] z)) [w23,w38,w55,w73,w108,w195,w205] (n (n (n z [w23,w38,w55,w73,w109,w195,w205] z) [w23,w38,w55,w73,w110,w195,w205] z) [w23,w38,w55,w73,w113,w177,w213] (n (n z [w23,w38,w55,w73,w113,w192,w205] z) [w23,w38,w55,w73,w113,w195,w205] z))) [w23,w38,w55,w73,w121,w189,w205] (n (n (n (n z [w23,w38,w55,w73,w121,w192,w205] z) [w23,w38,w55,w73,w121,w195,w205] z) [w23,w38,w55,w73,w121,w195,w222] (n (n z [w23,w38,w55,w73,w121,w205,w248] z) [w23,w38,w55,w73,w121,w205,w271] z)) [w23,w38,w55,w73,w125,w195,w205] (n (n (n z [w23,w38,w55,w73,w144,w205,w313] z) [w23,w38,w55,w73,w146,w195,w205] z) [w23,w38,w55,w73,w166,w205,w313] (n z [w23,w38,w55,w73,w189,w205,w309] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baaabaa : t6baaabaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6baaabab := (n (n (n (n (n z [w23,w38,w55,w73,w192,w205,w313] z) [w23,w38,w55,w73,w192,w205,w319] z) [w23,w38,w55,w73,w195,w205,w309] (n (n z [w23,w38,w55,w73,w195,w205,w313] z) [w23,w38,w55,w73,w195,w205,w324] z)) [w23,w38,w55,w73,w195,w222,w313] (n (n (n z [w23,w38,w55,w73,w195,w296,w313] z) [w23,w38,w55,w73,w205,w248,w313] z) [w23,w38,w55,w73,w205,w271,w313] (n (n z [w23,w38,w55,w73,w205,w289,w313] z) [w23,w38,w55,w74,w105,w195,w205] z))) [w23,w38,w55,w75,w105,w195,w205] (n (n (n (n z [w23,w38,w55,w76,w105,w195,w205] z) [w23,w38,w55,w77,w105,w195,w205] z) [w23,w38,w55,w79,w105,w195,w205] (n (n z [w23,w38,w55,w80,w105,w177,w205] z) [w23,w38,w55,w80,w121,w177,w205] z)) [w23,w38,w55,w84,w105,w173,w205] (n (n (n z [w23,w38,w55,w84,w105,w177,w205] z) [w23,w38,w55,w84,w105,w177,w213] z) [w23,w38,w55,w84,w105,w177,w222] (n z [w23,w38,w55,w84,w105,w177,w296] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baaabab : t6baaabab.all (blocked 5 t5) = true := by
  decide +kernel
def t6baaaba := (n t6baaabaa [w23,w38,w55,w73,w189,w205,w313] t6baaabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baaaba : t6baaaba.all (blocked 5 t5) = true := by
  simp only [t6baaaba, ReplayTree.all, n, ht6baaabaa, ht6baaabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baaabba := (n (n (n (n (n z [w23,w38,w55,w84,w105,w192,w205] z) [w23,w38,w55,w84,w105,w195,w205] z) [w23,w38,w55,w84,w105,w205,w238] (n (n z [w23,w38,w55,w84,w105,w205,w263] z) [w23,w38,w55,w84,w105,w205,w313] z)) [w23,w38,w55,w84,w113,w177,w205] (n (n (n z [w23,w38,w55,w84,w121,w177,w205] z) [w23,w38,w55,w84,w177,w205,w313] z) [w23,w38,w55,w84,w205,w313] (n (n z [w23,w38,w55,w85,w105,w177,w205] z) [w23,w38,w55,w87,w105,w173,w205] z))) [w23,w38,w55,w87,w105,w177,w205] (n (n (n (n z [w23,w38,w55,w87,w105,w177,w222] z) [w23,w38,w55,w87,w105,w177,w292] z) [w23,w38,w55,w87,w105,w177,w296] (n (n z [w23,w38,w55,w87,w105,w195,w205] z) [w23,w38,w55,w87,w105,w205,w238] z)) [w23,w38,w55,w87,w105,w205,w263] (n (n (n z [w23,w38,w55,w87,w105,w205,w279] z) [w23,w38,w55,w87,w105,w205,w288] z) [w23,w38,w55,w87,w105,w205,w313] (n z [w23,w38,w55,w87,w121,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baaabba : t6baaabba.all (blocked 5 t5) = true := by
  decide +kernel
def t6baaabbb := (n (n (n (n (n z [w23,w38,w55,w87,w177,w205,w329] z) [w23,w38,w55,w88,w105,w177,w205] z) [w23,w38,w55,w89,w105,w177,w205] (n (n z [w23,w38,w55,w90,w105,w177,w205] z) [w23,w38,w55,w91,w96,w205,w313] z)) [w23,w38,w55,w91,w103,w177,w205] (n (n (n z [w23,w38,w55,w91,w105,w173,w205] z) [w23,w38,w55,w91,w105,w173,w210] z) [w23,w38,w55,w91,w105,w173,w222] (n z [w23,w38,w55,w91,w105,w173,w251] z))) [w23,w38,w55,w91,w105,w173,w296] (n (n (n (n z [w23,w38,w55,w91,w105,w173,w329] z) [w23,w38,w55,w91,w105,w174,w205] z) [w23,w38,w55,w91,w105,w175,w205] (n (n z [w23,w38,w55,w91,w105,w176,w205] z) [w23,w38,w55,w91,w105,w177,w204] z)) [w23,w38,w55,w91,w105,w177,w205] (n (n (n z [w23,w38,w55,w91,w105,w177,w206] z) [w23,w38,w55,w91,w105,w177,w207] z) [w23,w38,w55,w91,w105,w177,w208] (n z [w23,w38,w55,w91,w105,w177,w211] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baaabbb : t6baaabbb.all (blocked 5 t5) = true := by
  decide +kernel
def t6baaabb := (n t6baaabba [w23,w38,w55,w87,w149,w177,w205] t6baaabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baaabb : t6baaabb.all (blocked 5 t5) = true := by
  simp only [t6baaabb, ReplayTree.all, n, ht6baaabba, ht6baaabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baaab := (n t6baaaba [w23,w38,w55,w84,w105,w177,w302] t6baaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baaab : t6baaab.all (blocked 5 t5) = true := by
  simp only [t6baaab, ReplayTree.all, n, ht6baaaba, ht6baaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baaa := (n t6baaaa [w23,w38,w55,w73,w105,w205,w271] t6baaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baaa : t6baaa.all (blocked 5 t5) = true := by
  simp only [t6baaa, ReplayTree.all, n, ht6baaaa, ht6baaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baabaaa := (n (n (n (n (n z [w23,w38,w55,w91,w105,w177,w222] z) [w23,w38,w55,w91,w105,w177,w229] z) [w23,w38,w55,w91,w105,w177,w249] (n (n z [w23,w38,w55,w91,w105,w177,w292] z) [w23,w38,w55,w91,w105,w177,w296] z)) [w23,w38,w55,w91,w105,w177,w307] (n (n (n z [w23,w38,w55,w91,w105,w178,w205] z) [w23,w38,w55,w91,w105,w179,w205] z) [w23,w38,w55,w91,w105,w180,w205] (n (n z [w23,w38,w55,w91,w105,w181,w205] z) [w23,w38,w55,w91,w105,w183,w205] z))) [w23,w38,w55,w91,w105,w189,w205] (n (n (n (n z [w23,w38,w55,w91,w105,w192,w205] z) [w23,w38,w55,w91,w105,w195,w205] z) [w23,w38,w55,w91,w105,w195,w222] (n (n z [w23,w38,w55,w91,w105,w204] z) [w23,w38,w55,w91,w105,w204,w205] z)) [w23,w38,w55,w91,w105,w204,w263] (n (n (n z [w23,w38,w55,w91,w105,w205,w209] z) [w23,w38,w55,w91,w105,w205,w226] z) [w23,w38,w55,w91,w105,w205,w232] (n z [w23,w38,w55,w91,w105,w205,w234] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baabaaa : t6baabaaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6baabaab := (n (n (n (n (n z [w23,w38,w55,w91,w105,w205,w248] z) [w23,w38,w55,w91,w105,w205,w260] z) [w23,w38,w55,w91,w105,w205,w263] (n (n z [w23,w38,w55,w91,w105,w205,w265] z) [w23,w38,w55,w91,w105,w205,w271] z)) [w23,w38,w55,w91,w105,w205,w279] (n (n (n z [w23,w38,w55,w91,w105,w205,w309] z) [w23,w38,w55,w91,w105,w205,w313] z) [w23,w38,w55,w91,w105,w205,w321] (n (n z [w23,w38,w55,w91,w105,w205,w352] z) [w23,w38,w55,w91,w105,w205,w357] z))) [w23,w38,w55,w91,w105,w222,w238] (n (n (n (n z [w23,w38,w55,w91,w105,w222,w263] z) [w23,w38,w55,w91,w105,w263,w296] z) [w23,w38,w55,w91,w105,w296,w313] (n (n z [w23,w38,w55,w91,w106,w177,w205] z) [w23,w38,w55,w91,w107,w205,w313] z)) [w23,w38,w55,w91,w108,w177,w205] (n (n (n z [w23,w38,w55,w91,w110,w177,w205] z) [w23,w38,w55,w91,w113,w177,w205] z) [w23,w38,w55,w91,w121,w173,w205] (n z [w23,w38,w55,w91,w121,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baabaab : t6baabaab.all (blocked 5 t5) = true := by
  decide +kernel
def t6baabaa := (n t6baabaaa [w23,w38,w55,w91,w105,w205,w238] t6baabaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baabaa : t6baabaa.all (blocked 5 t5) = true := by
  simp only [t6baabaa, ReplayTree.all, n, ht6baabaaa, ht6baabaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baababa := (n (n (n (n (n z [w23,w38,w55,w91,w121,w177,w296] z) [w23,w38,w55,w91,w121,w195,w205] z) [w23,w38,w55,w91,w121,w205,w238] (n (n z [w23,w38,w55,w91,w121,w205,w263] z) [w23,w38,w55,w91,w121,w205,w313] z)) [w23,w38,w55,w91,w125,w177,w205] (n (n (n z [w23,w38,w55,w91,w134,w205,w313] z) [w23,w38,w55,w91,w146,w177,w205] z) [w23,w38,w55,w91,w149,w205,w313] (n (n z [w23,w38,w55,w91,w158,w205,w313] z) [w23,w38,w55,w91,w159,w205,w313] z))) [w23,w38,w55,w91,w173,w205,w309] (n (n (n (n z [w23,w38,w55,w91,w177,w205,w309] z) [w23,w38,w55,w91,w177,w296,w313] z) [w23,w38,w55,w91,w205,w296,w313] (n (n z [w23,w38,w55,w91,w205,w309] z) [w23,w38,w55,w91,w205,w313,w329] z)) [w23,w38,w55,w91,w296,w313] (n (n (n z [w23,w38,w55,w92,w105,w177,w205] z) [w23,w38,w55,w95,w105,w177,w205] z) [w23,w38,w55,w98,w105,w177,w205] (n z [w23,w38,w55,w100,w105,w195,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baababa : t6baababa.all (blocked 5 t5) = true := by
  decide +kernel
def t6baababb := (n (n (n (n (n z [w23,w38,w55,w103,w105,w195,w205] z) [w23,w38,w55,w103,w114,w177,w205] z) [w23,w38,w55,w103,w158,w195,w205] (n (n z [w23,w38,w55,w103,w166,w177,w205] z) [w23,w38,w55,w103,w177,w195,w205] z)) [w23,w38,w55,w103,w195,w205] (n (n (n z [w23,w38,w55,w104,w105,w195,w205] z) [w23,w38,w55,w105,w114,w177,w205] z) [w23,w38,w55,w105,w115,w177,w205] (n (n z [w23,w38,w55,w105,w128,w195,w205] z) [w23,w38,w55,w105,w131,w195,w205] z))) [w23,w38,w55,w105,w134,w189,w205] (n (n (n (n z [w23,w38,w55,w105,w134,w192,w205] z) [w23,w38,w55,w105,w134,w195,w205] z) [w23,w38,w55,w105,w134,w195,w222] (n (n z [w23,w38,w55,w105,w134,w205,w248] z) [w23,w38,w55,w105,w134,w205,w271] z)) [w23,w38,w55,w105,w136,w177,w205] (n (n (n z [w23,w38,w55,w105,w139,w177,w205] z) [w23,w38,w55,w105,w142,w177,w205] z) [w23,w38,w55,w105,w144,w173,w205] (n z [w23,w38,w55,w105,w144,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baababb : t6baababb.all (blocked 5 t5) = true := by
  decide +kernel
def t6baabab := (n t6baababa [w23,w38,w55,w102,w105,w177,w205] t6baababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baabab : t6baabab.all (blocked 5 t5) = true := by
  simp only [t6baabab, ReplayTree.all, n, ht6baababa, ht6baababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baaba := (n t6baabaa [w23,w38,w55,w91,w121,w177,w222] t6baabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baaba : t6baaba.all (blocked 5 t5) = true := by
  simp only [t6baaba, ReplayTree.all, n, ht6baabaa, ht6baabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baabbaa := (n (n (n (n (n z [w23,w38,w55,w105,w144,w177,w296] z) [w23,w38,w55,w105,w144,w195,w205] z) [w23,w38,w55,w105,w144,w205,w238] (n (n z [w23,w38,w55,w105,w144,w205,w248] z) [w23,w38,w55,w105,w144,w205,w263] z)) [w23,w38,w55,w105,w144,w205,w313] (n (n (n z [w23,w38,w55,w105,w156,w195,w205] z) [w23,w38,w55,w105,w158,w189,w205] z) [w23,w38,w55,w105,w158,w192,w205] (n (n z [w23,w38,w55,w105,w158,w195,w205] z) [w23,w38,w55,w105,w158,w195,w222] z))) [w23,w38,w55,w105,w158,w205,w248] (n (n (n (n z [w23,w38,w55,w105,w158,w205,w271] z) [w23,w38,w55,w105,w161,w195,w205] z) [w23,w38,w55,w105,w163,w177,w205] (n (n z [w23,w38,w55,w105,w165,w177,w205] z) [w23,w38,w55,w105,w166,w173,w205] z)) [w23,w38,w55,w105,w166,w177,w205] (n (n (n z [w23,w38,w55,w105,w166,w177,w222] z) [w23,w38,w55,w105,w166,w177,w296] z) [w23,w38,w55,w105,w166,w195,w205] (n z [w23,w38,w55,w105,w166,w205,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baabbaa : t6baabbaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6baabbab := (n (n (n (n (n z [w23,w38,w55,w105,w166,w205,w271] z) [w23,w38,w55,w105,w166,w205,w313] z) [w23,w38,w55,w105,w172,w177,w205] (n (n z [w23,w38,w55,w105,w173,w189,w296] z) [w23,w38,w55,w105,w173,w195,w296] z)) [w23,w38,w55,w105,w173,w205,w286] (n (n (n z [w23,w38,w55,w105,w177,w189,w296] z) [w23,w38,w55,w105,w177,w192,w296] z) [w23,w38,w55,w105,w177,w195,w292] (n (n z [w23,w38,w55,w105,w177,w195,w296] z) [w23,w38,w55,w105,w177,w205,w286] z))) [w23,w38,w55,w105,w177,w248,w296] (n (n (n (n z [w23,w38,w55,w105,w177,w271,w296] z) [w23,w38,w55,w105,w177,w289,w296] z) [w23,w38,w55,w105,w189,w205,w278] (n (n z [w23,w38,w55,w105,w189,w205,w286] z) [w23,w38,w55,w105,w189,w205,w296] z)) [w23,w38,w55,w105,w192,w205,w296] (n (n (n z [w23,w38,w55,w105,w192,w296] z) [w23,w38,w55,w105,w195,w201,w296] z) [w23,w38,w55,w105,w195,w205,w278] (n z [w23,w38,w55,w105,w195,w205,w292] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baabbab : t6baabbab.all (blocked 5 t5) = true := by
  decide +kernel
def t6baabba := (n t6baabbaa [w23,w38,w55,w105,w166,w205,w263] t6baabbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baabba : t6baabba.all (blocked 5 t5) = true := by
  simp only [t6baabba, ReplayTree.all, n, ht6baabbaa, ht6baabbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baabbba := (n (n (n (n (n z [w23,w38,w55,w105,w195,w205,w304] z) [w23,w38,w55,w105,w195,w205,w349] z) [w23,w38,w55,w105,w195,w205,w355] (n (n z [w23,w38,w55,w105,w195,w210,w296] z) [w23,w38,w55,w105,w195,w222,w296] z)) [w23,w38,w55,w105,w195,w238,w296] (n (n (n z [w23,w38,w55,w105,w195,w251,w296] z) [w23,w38,w55,w105,w195,w261,w296] z) [w23,w38,w55,w105,w195,w263,w296] (n (n z [w23,w38,w55,w105,w195,w292] z) [w23,w38,w55,w105,w195,w296,w313] z))) [w23,w38,w55,w105,w195,w296,w329] (n (n (n (n z [w23,w38,w55,w105,w205,w248,w296] z) [w23,w38,w55,w105,w205,w271,w296] z) [w23,w38,w55,w105,w263,w271,w296] (n (n z [w23,w38,w55,w121,w134,w195,w205] z) [w23,w38,w55,w121,w144,w177,w205] z)) [w23,w38,w55,w121,w158,w195,w205] (n (n (n z [w23,w38,w55,w121,w166,w177,w205] z) [w23,w38,w55,w158,w166,w205,w313] z) [w23,w38,w55,w158,w195,w205,w313] (n z [w23,w38,w55,w177,w195,w296,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baabbba : t6baabbba.all (blocked 5 t5) = true := by
  decide +kernel
def t6baabbbb := (n (n (n (n (n z [w23,w38,w55,w195,w296,w313] z) [w23,w38,w56,w73,w105,w195,w205] z) [w23,w38,w56,w91,w105,w177,w205] (n (n z [w23,w38,w57,w73,w105,w195,w205] z) [w23,w38,w57,w91,w105,w177,w205] z)) [w23,w38,w58,w73,w105,w195,w205] (n (n (n z [w23,w38,w58,w91,w105,w177,w205] z) [w23,w38,w59,w63,w73,w205,w313] z) [w23,w38,w59,w63,w105,w177,w296] (n z [w23,w38,w60,w69,w105,w177,w205] z))) [w23,w38,w60,w73,w105,w173,w205] (n (n (n (n z [w23,w38,w60,w73,w105,w177,w205] z) [w23,w38,w60,w73,w105,w177,w213] z) [w23,w38,w60,w73,w105,w177,w222] (n (n z [w23,w38,w60,w73,w105,w177,w296] z) [w23,w38,w60,w73,w105,w192,w205] z)) [w23,w38,w60,w73,w105,w195,w205] (n (n (n z [w23,w38,w60,w73,w105,w205,w238] z) [w23,w38,w60,w73,w105,w205,w263] z) [w23,w38,w60,w73,w105,w205,w270] (n z [w23,w38,w60,w73,w105,w205,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baabbbb : t6baabbbb.all (blocked 5 t5) = true := by
  decide +kernel
def t6baabbb := (n t6baabbba [w23,w38,w55,w195,w205,w296,w313] t6baabbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baabbb : t6baabbb.all (blocked 5 t5) = true := by
  simp only [t6baabbb, ReplayTree.all, n, ht6baabbba, ht6baabbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baabb := (n t6baabba [w23,w38,w55,w105,w195,w205,w296] t6baabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baabb : t6baabb.all (blocked 5 t5) = true := by
  simp only [t6baabb, ReplayTree.all, n, ht6baabba, ht6baabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baab := (n t6baaba [w23,w38,w55,w105,w144,w177,w222] t6baabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baab : t6baab.all (blocked 5 t5) = true := by
  simp only [t6baab, ReplayTree.all, n, ht6baaba, ht6baabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baa := (n t6baaa [w23,w38,w55,w91,w105,w177,w213] t6baab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baa : t6baa.all (blocked 5 t5) = true := by
  simp only [t6baa, ReplayTree.all, n, ht6baaa, ht6baab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6babaaaa := (n (n (n (n (n z [w23,w38,w60,w73,w121,w177,w205] z) [w23,w38,w60,w73,w177,w205,w313] z) [w23,w38,w60,w73,w205,w313] (n (n z [w23,w38,w60,w84,w105,w177,w205] z) [w23,w38,w60,w91,w105,w177,w205] z)) [w23,w38,w60,w105,w134,w177,w205] (n (n (n z [w23,w38,w60,w105,w158,w177,w205] z) [w23,w38,w60,w105,w163,w177,w205] z) [w23,w38,w60,w105,w177,w205,w296] (n (n z [w23,w38,w60,w105,w177,w296] z) [w23,w38,w61,w73,w105,w177,w205] z))) [w23,w38,w62,w73,w105,w177,w205] (n (n (n (n z [w23,w38,w63,w65,w73,w205,w313] z) [w23,w38,w63,w65,w105,w177,w296] z) [w23,w38,w63,w69,w105,w173,w205] (n (n z [w23,w38,w63,w69,w105,w177,w205] z) [w23,w38,w63,w69,w105,w177,w222] z)) [w23,w38,w63,w69,w105,w177,w292] (n (n (n z [w23,w38,w63,w69,w105,w195,w205] z) [w23,w38,w63,w69,w105,w205,w238] z) [w23,w38,w63,w69,w105,w205,w263] (n z [w23,w38,w63,w69,w105,w205,w271] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6babaaaa : t6babaaaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6babaaab := (n (n (n (n (n z [w23,w38,w63,w69,w105,w205,w313] z) [w23,w38,w63,w69,w121,w177,w205] z) [w23,w38,w63,w69,w149,w177,w205] (n (n z [w23,w38,w63,w69,w177,w205,w329] z) [w23,w38,w63,w70,w105,w177,w205] z)) [w23,w38,w63,w71,w105,w177,w205] (n (n (n z [w23,w38,w63,w72,w105,w177,w205] z) [w23,w38,w63,w73,w103,w177,w205] z) [w23,w38,w63,w73,w105,w173,w205] (n (n z [w23,w38,w63,w73,w105,w173,w222] z) [w23,w38,w63,w73,w105,w173,w251] z))) [w23,w38,w63,w73,w105,w173,w329] (n (n (n (n z [w23,w38,w63,w73,w105,w174,w205] z) [w23,w38,w63,w73,w105,w175,w205] z) [w23,w38,w63,w73,w105,w176,w205] (n (n z [w23,w38,w63,w73,w105,w177,w204] z) [w23,w38,w63,w73,w105,w177,w205] z)) [w23,w38,w63,w73,w105,w177,w206] (n (n (n z [w23,w38,w63,w73,w105,w177,w207] z) [w23,w38,w63,w73,w105,w177,w211] z) [w23,w38,w63,w73,w105,w177,w213] (n z [w23,w38,w63,w73,w105,w177,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6babaaab : t6babaaab.all (blocked 5 t5) = true := by
  decide +kernel
def t6babaaa := (n t6babaaaa [w23,w38,w63,w69,w105,w205,w279] t6babaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6babaaa : t6babaaa.all (blocked 5 t5) = true := by
  simp only [t6babaaa, ReplayTree.all, n, ht6babaaaa, ht6babaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6babaaba := (n (n (n (n (n z [w23,w38,w63,w73,w105,w177,w249] z) [w23,w38,w63,w73,w105,w177,w292] z) [w23,w38,w63,w73,w105,w178,w205] (n (n z [w23,w38,w63,w73,w105,w179,w205] z) [w23,w38,w63,w73,w105,w180,w205] z)) [w23,w38,w63,w73,w105,w181,w205] (n (n (n z [w23,w38,w63,w73,w105,w183,w205] z) [w23,w38,w63,w73,w105,w189,w205] z) [w23,w38,w63,w73,w105,w192,w205] (n (n z [w23,w38,w63,w73,w105,w195,w205] z) [w23,w38,w63,w73,w105,w195,w222] z))) [w23,w38,w63,w73,w105,w204] (n (n (n (n z [w23,w38,w63,w73,w105,w204,w205] z) [w23,w38,w63,w73,w105,w204,w263] z) [w23,w38,w63,w73,w105,w204,w271] (n (n z [w23,w38,w63,w73,w105,w205,w209] z) [w23,w38,w63,w73,w105,w205,w226] z)) [w23,w38,w63,w73,w105,w205,w232] (n (n (n z [w23,w38,w63,w73,w105,w205,w234] z) [w23,w38,w63,w73,w105,w205,w238] z) [w23,w38,w63,w73,w105,w205,w248] (n z [w23,w38,w63,w73,w105,w205,w260] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6babaaba : t6babaaba.all (blocked 5 t5) = true := by
  decide +kernel
def t6babaabb := (n (n (n (n (n z [w23,w38,w63,w73,w105,w205,w265] z) [w23,w38,w63,w73,w105,w205,w268] z) [w23,w38,w63,w73,w105,w205,w271] (n (n z [w23,w38,w63,w73,w105,w205,w276] z) [w23,w38,w63,w73,w105,w205,w279] z)) [w23,w38,w63,w73,w105,w205,w309] (n (n (n z [w23,w38,w63,w73,w105,w205,w313] z) [w23,w38,w63,w73,w105,w205,w321] z) [w23,w38,w63,w73,w105,w205,w352] (n (n z [w23,w38,w63,w73,w105,w205,w357] z) [w23,w38,w63,w73,w105,w205,w365] z))) [w23,w38,w63,w73,w105,w222,w238] (n (n (n (n z [w23,w38,w63,w73,w105,w222,w263] z) [w23,w38,w63,w73,w105,w222,w271] z) [w23,w38,w63,w73,w105,w263,w296] (n (n z [w23,w38,w63,w73,w106,w177,w205] z) [w23,w38,w63,w73,w107,w205,w313] z)) [w23,w38,w63,w73,w108,w177,w205] (n (n (n z [w23,w38,w63,w73,w110,w177,w205] z) [w23,w38,w63,w73,w113,w177,w205] z) [w23,w38,w63,w73,w121,w173,w205] (n z [w23,w38,w63,w73,w121,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6babaabb : t6babaabb.all (blocked 5 t5) = true := by
  decide +kernel
def t6babaab := (n t6babaaba [w23,w38,w63,w73,w105,w205,w263] t6babaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6babaab : t6babaab.all (blocked 5 t5) = true := by
  simp only [t6babaab, ReplayTree.all, n, ht6babaaba, ht6babaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6babaa := (n t6babaaa [w23,w38,w63,w73,w105,w177,w229] t6babaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6babaa : t6babaa.all (blocked 5 t5) = true := by
  simp only [t6babaa, ReplayTree.all, n, ht6babaaa, ht6babaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bababaa := (n (n (n (n (n z [w23,w38,w63,w73,w121,w195,w205] z) [w23,w38,w63,w73,w121,w205,w238] z) [w23,w38,w63,w73,w121,w205,w263] (n (n z [w23,w38,w63,w73,w121,w205,w271] z) [w23,w38,w63,w73,w121,w205,w313] z)) [w23,w38,w63,w73,w125,w177,w205] (n (n (n z [w23,w38,w63,w73,w146,w177,w205] z) [w23,w38,w63,w73,w149,w205,w313] z) [w23,w38,w63,w73,w158,w205,w313] (n (n z [w23,w38,w63,w73,w159,w205,w313] z) [w23,w38,w63,w73,w173,w205,w309] z))) [w23,w38,w63,w73,w177,w205,w309] (n (n (n (n z [w23,w38,w63,w73,w205,w261,w313] z) [w23,w38,w63,w73,w205,w309] z) [w23,w38,w63,w73,w205,w313,w329] (n (n z [w23,w38,w63,w74,w105,w177,w205] z) [w23,w38,w63,w75,w105,w177,w205] z)) [w23,w38,w63,w76,w105,w177,w205] (n (n (n z [w23,w38,w63,w77,w105,w177,w205] z) [w23,w38,w63,w79,w105,w177,w205] z) [w23,w38,w63,w84,w105,w177,w205] (n z [w23,w38,w63,w87,w105,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bababaa : t6bababaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6bababab := (n (n (n (n (n z [w23,w38,w63,w91,w105,w177,w205] z) [w23,w38,w63,w91,w105,w177,w222] z) [w23,w38,w63,w91,w105,w195,w205] (n (n z [w23,w38,w63,w91,w105,w205,w238] z) [w23,w38,w63,w91,w105,w205,w263] z)) [w23,w38,w63,w91,w105,w205,w271] (n (n (n z [w23,w38,w63,w91,w105,w205,w313] z) [w23,w38,w63,w91,w121,w177,w205] z) [w23,w38,w63,w100,w105,w177,w205] (n (n z [w23,w38,w63,w103,w105,w177,w205] z) [w23,w38,w63,w103,w158,w177,w205] z))) [w23,w38,w63,w103,w166,w177,w205] (n (n (n (n z [w23,w38,w63,w103,w177,w205] z) [w23,w38,w63,w104,w105,w177,w205] z) [w23,w38,w63,w105,w128,w177,w205] (n (n z [w23,w38,w63,w105,w131,w177,w205] z) [w23,w38,w63,w105,w134,w173,w205] z)) [w23,w38,w63,w105,w134,w177,w205] (n (n (n z [w23,w38,w63,w105,w134,w177,w222] z) [w23,w38,w63,w105,w134,w195,w205] z) [w23,w38,w63,w105,w134,w205,w238] (n z [w23,w38,w63,w105,w134,w205,w263] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bababab : t6bababab.all (blocked 5 t5) = true := by
  decide +kernel
def t6bababa := (n t6bababaa [w23,w38,w63,w91,w105,w173,w205] t6bababab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bababa : t6bababa.all (blocked 5 t5) = true := by
  simp only [t6bababa, ReplayTree.all, n, ht6bababaa, ht6bababab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bababba := (n (n (n (n (n z [w23,w38,w63,w105,w134,w205,w313] z) [w23,w38,w63,w105,w144,w177,w205] z) [w23,w38,w63,w105,w156,w177,w205] (n (n z [w23,w38,w63,w105,w158,w173,w205] z) [w23,w38,w63,w105,w158,w177,w205] z)) [w23,w38,w63,w105,w158,w177,w222] (n (n (n z [w23,w38,w63,w105,w158,w195,w205] z) [w23,w38,w63,w105,w158,w205,w238] z) [w23,w38,w63,w105,w158,w205,w263] (n (n z [w23,w38,w63,w105,w158,w205,w271] z) [w23,w38,w63,w105,w158,w205,w313] z))) [w23,w38,w63,w105,w159,w177,w296] (n (n (n (n z [w23,w38,w63,w105,w161,w177,w205] z) [w23,w38,w63,w105,w165,w177,w205] z) [w23,w38,w63,w105,w166,w173,w205] (n (n z [w23,w38,w63,w105,w166,w177,w205] z) [w23,w38,w63,w105,w166,w177,w222] z)) [w23,w38,w63,w105,w166,w195,w205] (n (n (n z [w23,w38,w63,w105,w166,w205,w238] z) [w23,w38,w63,w105,w166,w205,w263] z) [w23,w38,w63,w105,w166,w205,w271] (n z [w23,w38,w63,w105,w166,w205,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bababba : t6bababba.all (blocked 5 t5) = true := by
  decide +kernel
def t6bababbb := (n (n (n (n (n z [w23,w38,w63,w105,w173,w205,w278] z) [w23,w38,w63,w105,w173,w205,w296] z) [w23,w38,w63,w105,w177,w205,w278] (n (n z [w23,w38,w63,w105,w177,w205,w292] z) [w23,w38,w63,w105,w177,w205,w296] z)) [w23,w38,w63,w105,w177,w205,w304] (n (n (n z [w23,w38,w63,w105,w177,w205,w349] z) [w23,w38,w63,w105,w177,w205,w355] z) [w23,w38,w63,w105,w177,w205,w362] (n z [w23,w38,w63,w105,w177,w210,w296] z))) [w23,w38,w63,w105,w177,w222,w296] (n (n (n (n z [w23,w38,w63,w105,w177,w251,w296] z) [w23,w38,w63,w105,w177,w261,w296] z) [w23,w38,w63,w105,w177,w263,w296] (n (n z [w23,w38,w63,w105,w177,w292] z) [w23,w38,w63,w105,w177,w296,w329] z)) [w23,w38,w63,w105,w195,w205,w296] (n (n (n z [w23,w38,w63,w105,w205,w238,w296] z) [w23,w38,w63,w105,w205,w263,w296] z) [w23,w38,w63,w105,w205,w271,w296] (n z [w23,w38,w63,w105,w205,w296,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bababbb : t6bababbb.all (blocked 5 t5) = true := by
  decide +kernel
def t6bababb := (n t6bababba [w23,w38,w63,w105,w172,w177,w205] t6bababbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bababb : t6bababb.all (blocked 5 t5) = true := by
  simp only [t6bababb, ReplayTree.all, n, ht6bababba, ht6bababbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6babab := (n t6bababa [w23,w38,w63,w105,w134,w205,w271] t6bababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6babab : t6babab.all (blocked 5 t5) = true := by
  simp only [t6babab, ReplayTree.all, n, ht6bababa, ht6bababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6baba := (n t6babaa [w23,w38,w63,w73,w121,w177,w222] t6babab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6baba : t6baba.all (blocked 5 t5) = true := by
  simp only [t6baba, ReplayTree.all, n, ht6babaa, ht6babab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6babbaaa := (n (n (n (n (n z [w23,w38,w63,w121,w134,w177,w205] z) [w23,w38,w63,w121,w158,w177,w205] z) [w23,w38,w63,w121,w166,w177,w205] (n (n z [w23,w38,w63,w158,w177,w205,w313] z) [w23,w38,w63,w158,w205,w313] z)) [w23,w38,w64,w73,w105,w177,w205] (n (n (n z [w23,w38,w65,w73,w105,w205,w271] z) [w23,w38,w65,w91,w105,w205,w263] z) [w23,w38,w65,w105,w158,w195,w205] (n (n z [w23,w38,w65,w105,w166,w177,w205] z) [w23,w38,w66,w73,w105,w177,w205] z))) [w23,w38,w67,w73,w105,w205,w271] (n (n (n (n z [w23,w38,w67,w105,w166,w177,w205] z) [w23,w38,w69,w105,w156,w195,w205] z) [w23,w38,w69,w105,w165,w177,w205] (n (n z [w23,w38,w73,w91,w105,w205,w260] z) [w23,w38,w73,w105,w156,w195,w205] z)) [w23,w38,w73,w105,w158,w205,w271] (n (n (n z [w23,w38,w73,w105,w165,w177,w205] z) [w23,w38,w73,w105,w166,w205,w263] z) [w23,w38,w73,w105,w166,w205,w271] (n z [w23,w38,w73,w105,w173,w205,w268] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6babbaaa : t6babbaaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6babbaab := (n (n (n (n (n z [w23,w38,w73,w105,w189,w205,w260] z) [w23,w38,w73,w105,w189,w205,w268] z) [w23,w38,w73,w105,w195,w205,w260] (n (n z [w23,w38,w73,w105,w205,w260,w268] z) [w23,w38,w73,w105,w205,w261,w271] z)) [w23,w38,w73,w105,w205,w268] (n (n (n z [w23,w38,w73,w105,w205,w269,w271] z) [w23,w38,w87,w105,w156,w177,w205] z) [w23,w38,w87,w105,w165,w177,w205] (n (n z [w23,w38,w91,w105,w156,w177,w205] z) [w23,w38,w91,w105,w158,w205,w263] z))) [w23,w38,w91,w105,w166,w205,w263] (n (n (n (n z [w23,w38,w91,w105,w173,w205,w260] z) [w23,w38,w91,w105,w177,w205,w260] z) [w23,w38,w91,w105,w205,w260] (n (n z [w23,w38,w91,w105,w205,w261,w263] z) [w23,w38,w105,w156,w165,w177,w205] z)) [w23,w38,w105,w156,w177,w195,w205] (n (n (n z [w23,w38,w105,w156,w195,w205] z) [w23,w38,w105,w158,w159,w195,w205] z) [w23,w38,w105,w158,w166,w205,w263] (n z [w23,w38,w105,w158,w177,w205,w271] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6babbaab : t6babbaab.all (blocked 5 t5) = true := by
  decide +kernel
def t6babbaa := (n t6babbaaa [w23,w38,w73,w105,w177,w205,w268] t6babbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6babbaa : t6babbaa.all (blocked 5 t5) = true := by
  simp only [t6babbaa, ReplayTree.all, n, ht6babbaaa, ht6babbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6babbaba := (n (n (n (n (n z [w23,w38,w105,w158,w195,w205,w271] z) [w23,w38,w105,w158,w205,w263,w271] z) [w23,w38,w105,w158,w205,w271] (n (n z [w23,w38,w105,w159,w166,w177,w205] z) [w23,w38,w105,w165,w177,w205] z)) [w23,w38,w105,w166,w167,w177,w205] (n (n (n z [w23,w38,w105,w166,w177,w205,w263] z) [w23,w38,w105,w166,w177,w205,w271] z) [w23,w38,w105,w166,w205,w263] (n (n z [w23,w38,w105,w166,w205,w271] z) [w23,w39,w55,w73,w105,w195,w205] z))) [w23,w39,w55,w91,w105,w177,w205] (n (n (n (n z [w23,w39,w63,w73,w105,w177,w205] z) [w23,w40,w55,w73,w105,w195,w205] z) [w23,w40,w55,w91,w105,w177,w205] (n (n z [w23,w41,w55,w73,w105,w195,w205] z) [w23,w41,w55,w91,w105,w177,w205] z)) [w23,w41,w63,w73,w105,w177,w205] (n (n (n z [w23,w42,w55,w73,w105,w195,w205] z) [w23,w42,w55,w91,w105,w177,w205] z) [w23,w43,w55,w73,w105,w205,w238] (n z [w23,w43,w55,w105,w134,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6babbaba : t6babbaba.all (blocked 5 t5) = true := by
  decide +kernel
def t6babbabb := (n (n (n (n (n z [w23,w46,w55,w73,w105,w173,w205] z) [w23,w46,w55,w73,w105,w177,w205] z) [w23,w46,w55,w73,w105,w177,w213] (n (n z [w23,w46,w55,w73,w105,w177,w222] z) [w23,w46,w55,w73,w105,w177,w296] z)) [w23,w46,w55,w73,w105,w192,w205] (n (n (n z [w23,w46,w55,w73,w105,w195,w205] z) [w23,w46,w55,w73,w105,w205,w238] z) [w23,w46,w55,w73,w105,w205,w245] (n z [w23,w46,w55,w73,w105,w205,w263] z))) [w23,w46,w55,w73,w105,w205,w313] (n (n (n (n z [w23,w46,w55,w73,w113,w177,w205] z) [w23,w46,w55,w73,w121,w177,w205] z) [w23,w46,w55,w73,w177,w205,w313] (n (n z [w23,w46,w55,w73,w205,w313] z) [w23,w46,w55,w84,w105,w177,w205] z)) [w23,w46,w55,w91,w105,w177,w205] (n (n (n z [w23,w46,w55,w105,w134,w177,w205] z) [w23,w46,w55,w105,w139,w177,w205] z) [w23,w46,w55,w105,w158,w177,w205] (n z [w23,w46,w55,w105,w177,w205,w296] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6babbabb : t6babbabb.all (blocked 5 t5) = true := by
  decide +kernel
def t6babbab := (n t6babbaba [w23,w46,w55,w69,w105,w177,w205] t6babbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6babbab : t6babbab.all (blocked 5 t5) = true := by
  simp only [t6babbab, ReplayTree.all, n, ht6babbaba, ht6babbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6babba := (n t6babbaa [w23,w38,w105,w158,w195,w205,w263] t6babbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6babba : t6babba.all (blocked 5 t5) = true := by
  simp only [t6babba, ReplayTree.all, n, ht6babbaa, ht6babbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6babbbaa := (n (n (n (n (n z [w23,w46,w60,w73,w105,w177,w205] z) [w23,w46,w63,w73,w105,w177,w205] z) [w23,w47,w50,w55,w73,w205,w313] (n (n z [w23,w47,w50,w55,w105,w177,w296] z) [w23,w47,w55,w73,w105,w205,w248] z)) [w23,w47,w55,w91,w105,w205,w238] (n (n (n z [w23,w47,w55,w105,w134,w195,w205] z) [w23,w47,w55,w105,w144,w177,w205] z) [w23,w47,w63,w73,w105,w205,w238] (n (n z [w23,w47,w63,w105,w134,w177,w205] z) [w23,w48,w55,w73,w105,w177,w205] z))) [w23,w49,w55,w73,w105,w177,w205] (n (n (n (n z [w23,w50,w55,w69,w105,w205,w238] z) [w23,w50,w55,w69,w149,w177,w205] z) [w23,w50,w55,w73,w105,w173,w251] (n (n z [w23,w50,w55,w73,w105,w177,w249] z) [w23,w50,w55,w73,w105,w205,w232] z)) [w23,w50,w55,w73,w105,w205,w234] (n (n (n z [w23,w50,w55,w73,w105,w205,w238] z) [w23,w50,w55,w73,w105,w205,w352] z) [w23,w50,w55,w73,w105,w222,w238] (n z [w23,w50,w55,w73,w121,w205,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6babbbaa : t6babbbaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6babbbab := (n (n (n (n (n z [w23,w50,w55,w73,w146,w177,w205] z) [w23,w50,w55,w73,w149,w205,w313] z) [w23,w50,w55,w73,w205,w238,w313] (n (n z [w23,w50,w55,w73,w205,w251,w313] z) [w23,w50,w55,w73,w205,w313,w352] z)) [w23,w50,w55,w91,w105,w205,w238] (n (n (n z [w23,w50,w55,w105,w128,w177,w205] z) [w23,w50,w55,w105,w131,w177,w205] z) [w23,w50,w55,w105,w134,w173,w205] (n (n z [w23,w50,w55,w105,w134,w177,w205] z) [w23,w50,w55,w105,w134,w177,w222] z))) [w23,w50,w55,w105,w134,w177,w296] (n (n (n (n z [w23,w50,w55,w105,w134,w195,w205] z) [w23,w50,w55,w105,w134,w205,w238] z) [w23,w50,w55,w105,w134,w205,w248] (n (n z [w23,w50,w55,w105,w134,w205,w263] z) [w23,w50,w55,w105,w134,w205,w313] z)) [w23,w50,w55,w105,w144,w205,w238] (n (n (n z [w23,w50,w55,w105,w149,w177,w296] z) [w23,w50,w55,w105,w158,w205,w238] z) [w23,w50,w55,w105,w177,w205,w349] (n z [w23,w50,w55,w105,w177,w238,w296] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6babbbab : t6babbbab.all (blocked 5 t5) = true := by
  decide +kernel
def t6babbba := (n t6babbbaa [w23,w50,w55,w73,w134,w205,w313] t6babbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6babbba : t6babbba.all (blocked 5 t5) = true := by
  simp only [t6babbba, ReplayTree.all, n, ht6babbbaa, ht6babbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6babbbba := (n (n (n (n (n z [w23,w50,w55,w105,w177,w296,w349] z) [w23,w50,w55,w105,w205,w238,w296] z) [w23,w50,w55,w121,w134,w177,w205] (n (n z [w23,w51,w55,w73,w105,w195,w205] z) [w23,w51,w55,w91,w105,w177,w205] z)) [w23,w51,w63,w73,w105,w177,w205] (n (n (n z [w23,w53,w55,w73,w105,w195,w205] z) [w23,w53,w55,w91,w105,w177,w205] z) [w23,w53,w63,w73,w105,w177,w205] (n (n z [w23,w55,w59,w91,w105,w205,w238] z) [w23,w55,w59,w105,w134,w195,w205] z))) [w23,w55,w60,w73,w105,w205,w238] (n (n (n (n z [w23,w55,w60,w105,w134,w177,w205] z) [w23,w55,w63,w69,w105,w205,w238] z) [w23,w55,w63,w73,w105,w205,w234] (n (n z [w23,w55,w63,w73,w105,w205,w238] z) [w23,w55,w63,w73,w105,w222,w238] z)) [w23,w55,w63,w73,w121,w205,w238] (n (n (n z [w23,w55,w63,w73,w134,w205,w313] z) [w23,w55,w63,w73,w205,w238,w313] z) [w23,w55,w63,w91,w105,w205,w238] (n z [w23,w55,w63,w105,w131,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6babbbba : t6babbbba.all (blocked 5 t5) = true := by
  decide +kernel
def t6babbbbb := (n (n (n (n (n z [w23,w55,w63,w105,w134,w177,w205] z) [w23,w55,w63,w105,w134,w177,w222] z) [w23,w55,w63,w105,w134,w177,w296] (n (n z [w23,w55,w63,w105,w134,w195,w205] z) [w23,w55,w63,w105,w134,w205,w238] z)) [w23,w55,w63,w105,w134,w205,w263] (n (n (n z [w23,w55,w63,w105,w134,w205,w271] z) [w23,w55,w63,w105,w134,w205,w313] z) [w23,w55,w63,w105,w158,w205,w238] (n z [w23,w55,w63,w105,w166,w205,w238] z))) [w23,w55,w63,w105,w177,w238,w296] (n (n (n (n z [w23,w55,w63,w105,w205,w238,w296] z) [w23,w55,w63,w121,w134,w177,w205] z) [w23,w55,w65,w91,w105,w205,w238] (n (n z [w23,w55,w65,w105,w134,w195,w205] z) [w23,w55,w68,w73,w105,w205,w238] z)) [w23,w55,w68,w105,w134,w177,w205] (n (n (n z [w23,w55,w69,w87,w105,w205,w238] z) [w23,w55,w69,w91,w105,w205,w238] z) [w23,w55,w69,w105,w131,w195,w205] (n z [w23,w55,w69,w105,w134,w195,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6babbbbb : t6babbbbb.all (blocked 5 t5) = true := by
  decide +kernel
def t6babbbb := (n t6babbbba [w23,w55,w63,w105,w134,w173,w205] t6babbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6babbbb : t6babbbb.all (blocked 5 t5) = true := by
  simp only [t6babbbb, ReplayTree.all, n, ht6babbbba, ht6babbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6babbb := (n t6babbba [w23,w50,w55,w105,w177,w251,w296] t6babbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6babbb : t6babbb.all (blocked 5 t5) = true := by
  simp only [t6babbb, ReplayTree.all, n, ht6babbba, ht6babbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6babb := (n t6babba [w23,w46,w55,w105,w177,w296] t6babbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6babb : t6babb.all (blocked 5 t5) = true := by
  simp only [t6babb, ReplayTree.all, n, ht6babba, ht6babbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bab := (n t6baba [w23,w38,w63,w105,w263,w296] t6babb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bab : t6bab.all (blocked 5 t5) = true := by
  simp only [t6bab, ReplayTree.all, n, ht6baba, ht6babb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6ba := (n t6baa [w23,w38,w60,w73,w113,w177,w205] t6bab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6ba : t6ba.all (blocked 5 t5) = true := by
  simp only [t6ba, ReplayTree.all, n, ht6baa, ht6bab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbaaaaa := (n (n (n (n (n z [w23,w55,w69,w105,w205,w238,w248] z) [w23,w55,w73,w84,w105,w205,w238] z) [w23,w55,w73,w87,w105,w205,w238] (n (n z [w23,w55,w73,w91,w105,w205,w234] z) [w23,w55,w73,w91,w105,w205,w238] z)) [w23,w55,w73,w91,w105,w222,w238] (n (n (n z [w23,w55,w73,w91,w121,w205,w238] z) [w23,w55,w73,w91,w134,w205,w313] z) [w23,w55,w73,w91,w205,w238,w313] (n (n z [w23,w55,w73,w105,w131,w195,w205] z) [w23,w55,w73,w105,w134,w189,w205] z))) [w23,w55,w73,w105,w134,w192,w205] (n (n (n (n z [w23,w55,w73,w105,w134,w195,w205] z) [w23,w55,w73,w105,w134,w195,w222] z) [w23,w55,w73,w105,w134,w205,w248] (n (n z [w23,w55,w73,w105,w134,w205,w271] z) [w23,w55,w73,w105,w139,w177,w205] z)) [w23,w55,w73,w105,w144,w205,w238] (n (n (n z [w23,w55,w73,w105,w149,w205,w248] z) [w23,w55,w73,w105,w166,w205,w238] z) [w23,w55,w73,w105,w177,w205,w245] (n z [w23,w55,w73,w105,w189,w205,w234] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbaaaaa : t6bbaaaaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbaaaab := (n (n (n (n (n z [w23,w55,w73,w105,w192,w205,w238] z) [w23,w55,w73,w105,w192,w205,w245] z) [w23,w55,w73,w105,w195,w205,w234] (n (n z [w23,w55,w73,w105,w195,w205,w238] z) [w23,w55,w73,w105,w195,w205,w340] z)) [w23,w55,w73,w105,w195,w222,w238] (n (n (n z [w23,w55,w73,w105,w195,w238,w296] z) [w23,w55,w73,w105,w205,w234,w244] z) [w23,w55,w73,w105,w205,w238,w245] (n (n z [w23,w55,w73,w105,w205,w238,w248] z) [w23,w55,w73,w105,w205,w238,w271] z))) [w23,w55,w73,w105,w205,w238,w276] (n (n (n (n z [w23,w55,w73,w105,w205,w238,w289] z) [w23,w55,w73,w105,w205,w238,w346] z) [w23,w55,w73,w105,w205,w245] (n (n z [w23,w55,w73,w105,w205,w246,w248] z) [w23,w55,w73,w105,w205,w248,w251] z)) [w23,w55,w73,w105,w205,w248,w253] (n (n (n z [w23,w55,w73,w105,w205,w248,w340] z) [w23,w55,w73,w105,w205,w248,w352] z) [w23,w55,w73,w105,w222,w238,w248] (n z [w23,w55,w73,w121,w134,w195,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbaaaab : t6bbaaaab.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbaaaa := (n t6bbaaaaa [w23,w55,w73,w105,w189,w205,w238] t6bbaaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbaaaa : t6bbaaaa.all (blocked 5 t5) = true := by
  simp only [t6bbaaaa, ReplayTree.all, n, ht6bbaaaaa, ht6bbaaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbaaaba := (n (n (n (n (n z [w23,w55,w73,w121,w205,w238,w248] z) [w23,w55,w73,w134,w144,w205,w313] z) [w23,w55,w73,w134,w195,w205,w313] (n (n z [w23,w55,w73,w195,w205,w238,w313] z) [w23,w55,w73,w205,w238,w248,w313] z)) [w23,w55,w84,w105,w134,w177,w205] (n (n (n z [w23,w55,w84,w105,w139,w177,w205] z) [w23,w55,w84,w105,w177,w205,w238] z) [w23,w55,w84,w105,w205,w238] (n (n z [w23,w55,w87,w105,w131,w177,w205] z) [w23,w55,w87,w105,w134,w177,w205] z))) [w23,w55,w87,w105,w177,w205,w238] (n (n (n (n z [w23,w55,w87,w105,w205,w238] z) [w23,w55,w91,w91,w105,w205,w238] z) [w23,w55,w91,w96,w105,w205,w238] (n (n z [w23,w55,w91,w99,w105,w205,w238] z) [w23,w55,w91,w105,w107,w205,w238] z)) [w23,w55,w91,w105,w116,w205,w238] (n (n (n z [w23,w55,w91,w105,w117,w205,w238] z) [w23,w55,w91,w105,w121,w205,w238] z) [w23,w55,w91,w105,w131,w177,w205] (n z [w23,w55,w91,w105,w134,w173,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbaaaba : t6bbaaaba.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbaaabb := (n (n (n (n (n z [w23,w55,w91,w105,w134,w177,w222] z) [w23,w55,w91,w105,w134,w177,w296] z) [w23,w55,w91,w105,w134,w195,w205] (n (n z [w23,w55,w91,w105,w134,w205,w238] z) [w23,w55,w91,w105,w134,w205,w263] z)) [w23,w55,w91,w105,w134,w205,w313] (n (n (n z [w23,w55,w91,w105,w144,w205,w238] z) [w23,w55,w91,w105,w149,w205,w238] z) [w23,w55,w91,w105,w158,w205,w238] (n (n z [w23,w55,w91,w105,w159,w205,w238] z) [w23,w55,w91,w105,w166,w205,w238] z))) [w23,w55,w91,w105,w173,w205,w234] (n (n (n (n z [w23,w55,w91,w105,w173,w205,w238] z) [w23,w55,w91,w105,w177,w205,w234] z) [w23,w55,w91,w105,w177,w205,w238] (n (n z [w23,w55,w91,w105,w177,w205,w340] z) [w23,w55,w91,w105,w177,w222,w238] z)) [w23,w55,w91,w105,w177,w238,w296] (n (n (n z [w23,w55,w91,w105,w195,w205,w238] z) [w23,w55,w91,w105,w201,w205,w238] z) [w23,w55,w91,w105,w205,w210,w238] (n z [w23,w55,w91,w105,w205,w215,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbaaabb : t6bbaaabb.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbaaab := (n t6bbaaaba [w23,w55,w91,w105,w134,w177,w205] t6bbaaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbaaab : t6bbaaab.all (blocked 5 t5) = true := by
  simp only [t6bbaaab, ReplayTree.all, n, ht6bbaaaba, ht6bbaaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbaaa := (n t6bbaaaa [w23,w55,w73,w121,w195,w205,w238] t6bbaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbaaa : t6bbaaa.all (blocked 5 t5) = true := by
  simp only [t6bbaaa, ReplayTree.all, n, ht6bbaaaa, ht6bbaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbaabaa := (n (n (n (n (n z [w23,w55,w91,w105,w205,w234] z) [w23,w55,w91,w105,w205,w238] z) [w23,w55,w91,w105,w205,w238,w238] (n (n z [w23,w55,w91,w105,w205,w238,w246] z) [w23,w55,w91,w105,w205,w238,w248] z)) [w23,w55,w91,w105,w205,w238,w251] (n (n (n z [w23,w55,w91,w105,w205,w238,w253] z) [w23,w55,w91,w105,w205,w238,w261] z) [w23,w55,w91,w105,w205,w238,w263] (n (n z [w23,w55,w91,w105,w205,w238,w265] z) [w23,w55,w91,w105,w205,w238,w280] z))) [w23,w55,w91,w105,w205,w238,w289] (n (n (n (n z [w23,w55,w91,w105,w205,w238,w296] z) [w23,w55,w91,w105,w205,w238,w304] z) [w23,w55,w91,w105,w205,w238,w313] (n (n z [w23,w55,w91,w105,w205,w238,w329] z) [w23,w55,w91,w105,w205,w238,w340] z)) [w23,w55,w91,w105,w205,w238,w346] (n (n (n z [w23,w55,w91,w105,w205,w238,w352] z) [w23,w55,w91,w105,w222,w238] z) [w23,w55,w91,w121,w134,w177,w205] (n z [w23,w55,w91,w121,w177,w205,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbaabaa : t6bbaabaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbaabab := (n (n (n (n (n z [w23,w55,w91,w134,w177,w205,w313] z) [w23,w55,w91,w134,w205,w313] z) [w23,w55,w96,w105,w134,w195,w205] (n (n z [w23,w55,w105,w107,w134,w195,w205] z) [w23,w55,w105,w116,w134,w195,w205] z)) [w23,w55,w105,w121,w134,w195,w205] (n (n (n z [w23,w55,w105,w131,w142,w177,w205] z) [w23,w55,w105,w131,w177,w195,w205] z) [w23,w55,w105,w131,w195,w205] (n (n z [w23,w55,w105,w134,w134,w195,w205] z) [w23,w55,w105,w134,w139,w177,w205] z))) [w23,w55,w105,w134,w140,w195,w205] (n (n (n (n z [w23,w55,w105,w134,w144,w173,w205] z) [w23,w55,w105,w134,w144,w177,w205] z) [w23,w55,w105,w134,w144,w177,w222] (n (n z [w23,w55,w105,w134,w144,w177,w296] z) [w23,w55,w105,w134,w144,w195,w205] z)) [w23,w55,w105,w134,w144,w205,w238] (n (n (n z [w23,w55,w105,w134,w144,w205,w263] z) [w23,w55,w105,w134,w144,w205,w313] z) [w23,w55,w105,w134,w149,w195,w205] (n z [w23,w55,w105,w134,w150,w195,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbaabab : t6bbaabab.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbaaba := (n t6bbaabaa [w23,w55,w91,w121,w205,w238] t6bbaabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbaaba : t6bbaaba.all (blocked 5 t5) = true := by
  simp only [t6bbaaba, ReplayTree.all, n, ht6bbaabaa, ht6bbaabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbaabba := (n (n (n (n (n z [w23,w55,w105,w134,w159,w195,w205] z) [w23,w55,w105,w134,w161,w195,w205] z) [w23,w55,w105,w134,w166,w177,w205] (n (n z [w23,w55,w105,w134,w172,w177,w205] z) [w23,w55,w105,w134,w173,w189,w205] z)) [w23,w55,w105,w134,w173,w195,w205] (n (n (n z [w23,w55,w105,w134,w177,w189,w205] z) [w23,w55,w105,w134,w177,w192,w205] z) [w23,w55,w105,w134,w177,w195,w205] (n (n z [w23,w55,w105,w134,w177,w195,w222] z) [w23,w55,w105,w134,w177,w195,w296] z))) [w23,w55,w105,w134,w177,w205,w248] (n (n (n (n z [w23,w55,w105,w134,w177,w205,w271] z) [w23,w55,w105,w134,w177,w205,w289] z) [w23,w55,w105,w134,w177,w205,w346] (n (n z [w23,w55,w105,w134,w189,w205] z) [w23,w55,w105,w134,w192,w205] z)) [w23,w55,w105,w134,w195,w195,w205] (n (n (n z [w23,w55,w105,w134,w195,w201,w205] z) [w23,w55,w105,w134,w195,w203,w205] z) [w23,w55,w105,w134,w195,w205] (n z [w23,w55,w105,w134,w195,w205,w210] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbaabba : t6bbaabba.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbaabbb := (n (n (n (n (n z [w23,w55,w105,w134,w195,w205,w218] z) [w23,w55,w105,w134,w195,w205,w222] z) [w23,w55,w105,w134,w195,w205,w238] (n (n z [w23,w55,w105,w134,w195,w205,w248] z) [w23,w55,w105,w134,w195,w205,w251] z)) [w23,w55,w105,w134,w195,w205,w261] (n (n (n z [w23,w55,w105,w134,w195,w205,w263] z) [w23,w55,w105,w134,w195,w205,w271] z) [w23,w55,w105,w134,w195,w205,w280] (n z [w23,w55,w105,w134,w195,w205,w289] z))) [w23,w55,w105,w134,w195,w205,w296] (n (n (n (n z [w23,w55,w105,w134,w195,w205,w313] z) [w23,w55,w105,w134,w195,w205,w321] z) [w23,w55,w105,w134,w195,w205,w329] (n (n z [w23,w55,w105,w134,w195,w205,w340] z) [w23,w55,w105,w134,w195,w205,w346] z)) [w23,w55,w105,w134,w195,w205,w349] (n (n (n z [w23,w55,w105,w134,w195,w222] z) [w23,w55,w105,w134,w205,w238,w248] z) [w23,w55,w105,w134,w205,w248] (n z [w23,w55,w105,w134,w205,w263,w271] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbaabbb : t6bbaabbb.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbaabb := (n t6bbaabba [w23,w55,w105,w134,w195,w205,w215] t6bbaabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbaabb : t6bbaabb.all (blocked 5 t5) = true := by
  simp only [t6bbaabb, ReplayTree.all, n, ht6bbaabba, ht6bbaabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbaab := (n t6bbaaba [w23,w55,w105,w134,w158,w195,w205] t6bbaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbaab : t6bbaab.all (blocked 5 t5) = true := by
  simp only [t6bbaab, ReplayTree.all, n, ht6bbaaba, ht6bbaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbaa := (n t6bbaaa [w23,w55,w91,w105,w205,w222,w238] t6bbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbaa : t6bbaa.all (blocked 5 t5) = true := by
  simp only [t6bbaa, ReplayTree.all, n, ht6bbaaa, ht6bbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbabaaa := (n (n (n (n (n z [w23,w55,w105,w139,w177,w205] z) [w23,w55,w105,w140,w144,w177,w205] z) [w23,w55,w105,w144,w149,w177,w205] (n (n z [w23,w55,w105,w144,w150,w177,w205] z) [w23,w55,w105,w144,w177,w205,w238] z)) [w23,w55,w105,w144,w177,w205,w251] (n (n (n z [w23,w55,w105,w144,w177,w205,w340] z) [w23,w55,w105,w144,w177,w205,w349] z) [w23,w55,w105,w144,w205,w238] (n (n z [w23,w55,w105,w158,w166,w205,w238] z) [w23,w55,w105,w158,w195,w205,w238] z))) [w23,w55,w105,w158,w205,w238,w248] (n (n (n (n z [w23,w55,w105,w166,w177,w205,w238] z) [w23,w55,w105,w166,w205,w238] z) [w23,w55,w105,w177,w195,w238,w296] (n (n z [w23,w55,w105,w177,w238,w248,w296] z) [w23,w55,w105,w195,w205,w238,w296] z)) [w23,w55,w105,w195,w238,w296] (n (n (n z [w23,w55,w105,w205,w238,w248,w296] z) [w23,w55,w121,w134,w144,w177,w205] z) [w23,w55,w121,w134,w177,w195,w205] (n z [w23,w55,w121,w134,w195,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbabaaa : t6bbabaaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbabaab := (n (n (n (n (n z [w23,w59,w63,w105,w134,w177,w205] z) [w23,w60,w73,w105,w134,w177,w205] z) [w23,w60,w73,w105,w177,w205,w238] (n (n z [w23,w60,w73,w105,w205,w238] z) [w23,w60,w105,w134,w177,w205] z)) [w23,w63,w65,w73,w105,w205,w238] (n (n (n z [w23,w63,w65,w105,w134,w177,w205] z) [w23,w63,w69,w105,w131,w177,w205] z) [w23,w63,w73,w105,w131,w177,w205] (n (n z [w23,w63,w73,w105,w134,w205,w238] z) [w23,w63,w73,w105,w134,w205,w263] z))) [w23,w63,w73,w105,w149,w205,w238] (n (n (n (n z [w23,w63,w73,w105,w158,w205,w238] z) [w23,w63,w73,w105,w159,w205,w238] z) [w23,w63,w73,w105,w173,w205,w234] (n (n z [w23,w63,w73,w105,w177,w205,w234] z) [w23,w63,w73,w105,w205,w234] z)) [w23,w63,w73,w105,w205,w238,w251] (n (n (n z [w23,w63,w73,w105,w205,w238,w261] z) [w23,w63,w105,w131,w177,w205] z) [w23,w63,w105,w134,w149,w177,w205] (n z [w23,w63,w105,w134,w159,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbabaab : t6bbabaab.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbabaa := (n t6bbabaaa [w23,w59,w63,w73,w105,w205,w238] t6bbabaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbabaa : t6bbabaa.all (blocked 5 t5) = true := by
  simp only [t6bbabaa, ReplayTree.all, n, ht6bbabaaa, ht6bbabaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbababa := (n (n (n (n (n z [w23,w63,w105,w134,w177,w205,w251] z) [w23,w63,w105,w134,w177,w205,w261] z) [w23,w63,w105,w134,w177,w205,w263] (n (n z [w23,w63,w105,w134,w205,w238] z) [w23,w63,w105,w134,w205,w263] z)) [w23,w63,w105,w158,w177,w205,w238] (n (n (n z [w23,w63,w105,w158,w205,w238] z) [w24,w38,w55,w73,w105,w195,w205] z) [w24,w38,w63,w73,w105,w177,w205] (n (n z [w25,w38,w55,w91,w105,w177,w205] z) [w25,w38,w63,w73,w105,w177,w205] z))) [w26,w38,w55,w73,w105,w177,w222] (n (n (n (n z [w26,w38,w55,w73,w121,w177,w205] z) [w26,w47,w55,w73,w105,w177,w205] z) [w27,w38,w55,w73,w105,w195,w222] (n (n z [w27,w38,w55,w73,w121,w195,w205] z) [w27,w38,w55,w91,w105,w177,w222] z)) [w27,w38,w55,w91,w121,w177,w205] (n (n (n z [w27,w38,w63,w73,w105,w177,w222] z) [w27,w38,w63,w73,w121,w177,w205] z) [w27,w46,w55,w73,w105,w177,w205] (n z [w28,w38,w55,w73,w105,w195,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbababa : t6bbababa.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbababb := (n (n (n (n (n z [w28,w38,w63,w73,w105,w177,w222] z) [w28,w38,w63,w73,w121,w177,w205] z) [w29,w38,w55,w73,w105,w177,w222] (n (n z [w29,w38,w63,w73,w105,w177,w222] z) [w30,w38,w55,w73,w105,w177,w222] z)) [w30,w38,w55,w73,w121,w177,w205] (n (n (n z [w31,w38,w55,w73,w105,w195,w205] z) [w31,w38,w55,w91,w105,w177,w205] z) [w31,w38,w63,w73,w105,w177,w205] (n z [w32,w38,w55,w73,w105,w195,w222] z))) [w32,w38,w55,w91,w121,w177,w205] (n (n (n (n z [w32,w38,w63,w73,w105,w177,w222] z) [w32,w38,w63,w73,w121,w177,w205] z) [w33,w38,w55,w73,w121,w177,w205] (n (n z [w33,w38,w63,w73,w121,w177,w205] z) [w34,w38,w55,w73,w105,w177,w222] z)) [w34,w38,w55,w73,w121,w177,w205] (n (n (n z [w35,w38,w55,w73,w105,w195,w205] z) [w35,w38,w55,w91,w105,w177,w205] z) [w35,w38,w63,w73,w105,w177,w205] (n z [w36,w38,w55,w73,w105,w195,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbababb : t6bbababb.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbabab := (n t6bbababa [w28,w38,w55,w91,w121,w177,w205] t6bbababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbabab : t6bbabab.all (blocked 5 t5) = true := by
  simp only [t6bbabab, ReplayTree.all, n, ht6bbababa, ht6bbababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbaba := (n t6bbabaa [w23,w63,w105,w134,w177,w205,w238] t6bbabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbaba : t6bbaba.all (blocked 5 t5) = true := by
  simp only [t6bbaba, ReplayTree.all, n, ht6bbabaa, ht6bbabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbabbaa := (n (n (n (n (n z [w36,w38,w63,w73,w105,w177,w222] z) [w36,w38,w63,w73,w121,w177,w205] z) [w36,w50,w55,w73,w105,w177,w222] (n (n z [w36,w50,w55,w73,w121,w177,w205] z) [w38,w43,w55,w73,w105,w177,w222] z)) [w38,w43,w55,w73,w121,w177,w205] (n (n (n z [w38,w45,w55,w73,w105,w195,w205] z) [w38,w45,w55,w91,w105,w177,w205] z) [w38,w45,w63,w73,w105,w177,w205] (n (n z [w38,w46,w55,w73,w105,w177,w222] z) [w38,w46,w55,w73,w121,w177,w205] z))) [w38,w47,w55,w73,w105,w195,w222] (n (n (n (n z [w38,w47,w55,w73,w121,w195,w205] z) [w38,w47,w55,w91,w105,w177,w222] z) [w38,w47,w55,w91,w121,w177,w205] (n (n z [w38,w47,w63,w73,w105,w177,w222] z) [w38,w47,w63,w73,w121,w177,w205] z)) [w38,w50,w55,w69,w105,w177,w222] (n (n (n z [w38,w50,w55,w69,w121,w177,w205] z) [w38,w50,w55,w73,w105,w173,w222] z) [w38,w50,w55,w73,w105,w177,w221] (n z [w38,w50,w55,w73,w105,w177,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbabbaa : t6bbabbaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbabbab := (n (n (n (n (n z [w38,w50,w55,w73,w105,w222,w238] z) [w38,w50,w55,w73,w105,w222,w248] z) [w38,w50,w55,w73,w105,w222,w263] (n (n z [w38,w50,w55,w73,w120,w177,w205] z) [w38,w50,w55,w73,w121,w173,w205] z)) [w38,w50,w55,w73,w121,w177,w205] (n (n (n z [w38,w50,w55,w73,w121,w177,w222] z) [w38,w50,w55,w73,w121,w177,w296] z) [w38,w50,w55,w73,w121,w195,w205] (n (n z [w38,w50,w55,w73,w121,w205,w238] z) [w38,w50,w55,w73,w121,w205,w248] z))) [w38,w50,w55,w73,w121,w205,w263] (n (n (n (n z [w38,w50,w55,w73,w121,w205,w313] z) [w38,w50,w55,w73,w177,w222,w313] z) [w38,w50,w55,w73,w205,w222,w313] (n (n z [w38,w50,w55,w91,w105,w177,w222] z) [w38,w50,w55,w91,w121,w177,w205] z)) [w38,w50,w55,w105,w121,w177,w296] (n (n (n z [w38,w50,w55,w105,w134,w177,w222] z) [w38,w50,w55,w105,w144,w177,w222] z) [w38,w50,w55,w105,w158,w177,w222] (n z [w38,w50,w55,w105,w177,w222,w296] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbabbab : t6bbabbab.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbabba := (n t6bbabbaa [w38,w50,w55,w73,w105,w195,w222] t6bbabbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbabba : t6bbabba.all (blocked 5 t5) = true := by
  simp only [t6bbabba, ReplayTree.all, n, ht6bbabbaa, ht6bbabbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbabbba := (n (n (n (n (n z [w38,w50,w55,w121,w144,w177,w205] z) [w38,w50,w55,w121,w158,w177,w205] z) [w38,w50,w63,w73,w105,w177,w222] (n (n z [w38,w50,w63,w73,w121,w177,w205] z) [w38,w55,w59,w73,w105,w195,w222] z)) [w38,w55,w59,w91,w121,w177,w205] (n (n (n z [w38,w55,w60,w73,w105,w177,w222] z) [w38,w55,w60,w73,w121,w177,w205] z) [w38,w55,w63,w69,w105,w177,w222] (n (n z [w38,w55,w63,w69,w121,w177,w205] z) [w38,w55,w63,w73,w105,w173,w222] z))) [w38,w55,w63,w73,w105,w177,w222] (n (n (n (n z [w38,w55,w63,w73,w105,w195,w222] z) [w38,w55,w63,w73,w105,w222,w238] z) [w38,w55,w63,w73,w105,w222,w263] (n (n z [w38,w55,w63,w73,w105,w222,w271] z) [w38,w55,w63,w73,w121,w173,w205] z)) [w38,w55,w63,w73,w121,w177,w205] (n (n (n z [w38,w55,w63,w73,w121,w177,w222] z) [w38,w55,w63,w73,w121,w177,w296] z) [w38,w55,w63,w73,w121,w195,w205] (n z [w38,w55,w63,w73,w121,w205,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbabbba : t6bbabbba.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbabbbb := (n (n (n (n (n z [w38,w55,w63,w73,w121,w205,w271] z) [w38,w55,w63,w73,w121,w205,w313] z) [w38,w55,w63,w73,w177,w222,w313] (n (n z [w38,w55,w63,w73,w205,w222,w313] z) [w38,w55,w63,w91,w105,w177,w222] z)) [w38,w55,w63,w91,w121,w177,w205] (n (n (n z [w38,w55,w63,w105,w121,w177,w296] z) [w38,w55,w63,w105,w134,w177,w222] z) [w38,w55,w63,w105,w158,w177,w222] (n z [w38,w55,w63,w105,w166,w177,w222] z))) [w38,w55,w63,w105,w177,w222,w296] (n (n (n (n z [w38,w55,w63,w121,w134,w177,w205] z) [w38,w55,w63,w121,w158,w177,w205] z) [w38,w55,w63,w121,w166,w177,w205] (n (n z [w38,w55,w65,w73,w105,w192,w205] z) [w38,w55,w65,w73,w105,w195,w222] z)) [w38,w55,w65,w73,w121,w195,w205] (n (n (n z [w38,w55,w65,w84,w105,w177,w205] z) [w38,w55,w65,w91,w105,w177,w222] z) [w38,w55,w65,w91,w121,w177,w205] (n z [w38,w55,w68,w73,w105,w177,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbabbbb : t6bbabbbb.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbabbb := (n t6bbabbba [w38,w55,w63,w73,w121,w205,w263] t6bbabbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbabbb : t6bbabbb.all (blocked 5 t5) = true := by
  simp only [t6bbabbb, ReplayTree.all, n, ht6bbabbba, ht6bbabbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbabb := (n t6bbabba [w38,w50,w55,w121,w134,w177,w205] t6bbabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbabb : t6bbabb.all (blocked 5 t5) = true := by
  simp only [t6bbabb, ReplayTree.all, n, ht6bbabba, ht6bbabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbab := (n t6bbaba [w36,w38,w55,w91,w121,w177,w205] t6bbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbab : t6bbab.all (blocked 5 t5) = true := by
  simp only [t6bbab, ReplayTree.all, n, ht6bbaba, ht6bbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bba := (n t6bbaa [w23,w55,w105,w134,w205,w271] t6bbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bba : t6bba.all (blocked 5 t5) = true := by
  simp only [t6bba, ReplayTree.all, n, ht6bbaa, ht6bbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbbaaaa := (n (n (n (n (n z [w38,w55,w69,w73,w105,w195,w222] z) [w38,w55,w69,w87,w105,w177,w222] z) [w38,w55,w69,w87,w121,w177,w205] (n (n z [w38,w55,w69,w91,w121,w177,w205] z) [w38,w55,w69,w94,w105,w195,w205] z)) [w38,w55,w69,w105,w177,w195,w222] (n (n (n z [w38,w55,w69,w105,w195,w205,w222] z) [w38,w55,w69,w105,w195,w222] z) [w38,w55,w73,w80,w121,w177,w205] (n (n z [w38,w55,w73,w84,w121,w177,w205] z) [w38,w55,w73,w87,w105,w177,w222] z))) [w38,w55,w73,w87,w121,w177,w205] (n (n (n (n z [w38,w55,w73,w91,w105,w195,w222] z) [w38,w55,w73,w91,w121,w173,w205] z) [w38,w55,w73,w91,w121,w177,w205] (n (n z [w38,w55,w73,w91,w121,w177,w222] z) [w38,w55,w73,w91,w121,w177,w296] z)) [w38,w55,w73,w91,w121,w195,w205] (n (n (n z [w38,w55,w73,w91,w121,w205,w238] z) [w38,w55,w73,w91,w121,w205,w263] z) [w38,w55,w73,w91,w121,w205,w313] (n z [w38,w55,w73,w94,w105,w195,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbaaaa : t6bbbaaaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbbaaab := (n (n (n (n (n z [w38,w55,w73,w96,w121,w195,w205] z) [w38,w55,w73,w105,w107,w195,w222] z) [w38,w55,w73,w105,w116,w195,w222] (n (n z [w38,w55,w73,w105,w121,w189,w205] z) [w38,w55,w73,w105,w121,w195,w222] z)) [w38,w55,w73,w105,w134,w195,w222] (n (n (n z [w38,w55,w73,w105,w149,w195,w222] z) [w38,w55,w73,w105,w158,w195,w222] z) [w38,w55,w73,w105,w159,w195,w222] (n (n z [w38,w55,w73,w105,w173,w189,w222] z) [w38,w55,w73,w105,w173,w195,w222] z))) [w38,w55,w73,w105,w177,w184,w222] (n (n (n (n z [w38,w55,w73,w105,w177,w189,w222] z) [w38,w55,w73,w105,w177,w192,w222] z) [w38,w55,w73,w105,w177,w195,w222] (n (n z [w38,w55,w73,w105,w177,w222,w248] z) [w38,w55,w73,w105,w177,w222,w271] z)) [w38,w55,w73,w105,w184,w195,w222] (n (n (n z [w38,w55,w73,w105,w184,w205,w222] z) [w38,w55,w73,w105,w184,w222] z) [w38,w55,w73,w105,w189,w198,w205] (n z [w38,w55,w73,w105,w189,w205,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbaaab : t6bbbaaab.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbbaaa := (n t6bbbaaaa [w38,w55,w73,w96,w105,w195,w222] t6bbbaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbaaa : t6bbbaaa.all (blocked 5 t5) = true := by
  simp only [t6bbbaaa, ReplayTree.all, n, ht6bbbaaaa, ht6bbbaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbbaaba := (n (n (n (n (n z [w38,w55,w73,w105,w192,w205,w222] z) [w38,w55,w73,w105,w192,w222] z) [w38,w55,w73,w105,w195,w195,w222] (n (n z [w38,w55,w73,w105,w195,w198,w205] z) [w38,w55,w73,w105,w195,w201,w222] z)) [w38,w55,w73,w105,w195,w203,w222] (n (n (n z [w38,w55,w73,w105,w195,w205,w222] z) [w38,w55,w73,w105,w195,w210,w222] z) [w38,w55,w73,w105,w195,w215,w222] (n (n z [w38,w55,w73,w105,w195,w218,w222] z) [w38,w55,w73,w105,w195,w222] z))) [w38,w55,w73,w105,w195,w222,w222] (n (n (n (n z [w38,w55,w73,w105,w195,w222,w223] z) [w38,w55,w73,w105,w195,w222,w224] z) [w38,w55,w73,w105,w195,w222,w225] (n (n z [w38,w55,w73,w105,w195,w222,w238] z) [w38,w55,w73,w105,w195,w222,w248] z)) [w38,w55,w73,w105,w195,w222,w251] (n (n (n z [w38,w55,w73,w105,w195,w222,w256] z) [w38,w55,w73,w105,w195,w222,w261] z) [w38,w55,w73,w105,w195,w222,w263] (n z [w38,w55,w73,w105,w195,w222,w271] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbaaba : t6bbbaaba.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbbaabb := (n (n (n (n (n z [w38,w55,w73,w105,w195,w222,w280] z) [w38,w55,w73,w105,w195,w222,w289] z) [w38,w55,w73,w105,w195,w222,w296] (n (n z [w38,w55,w73,w105,w195,w222,w307] z) [w38,w55,w73,w105,w195,w222,w313] z)) [w38,w55,w73,w105,w195,w222,w321] (n (n (n z [w38,w55,w73,w105,w195,w222,w329] z) [w38,w55,w73,w105,w195,w222,w336] z) [w38,w55,w73,w105,w205,w222,w248] (n (n z [w38,w55,w73,w105,w205,w222,w271] z) [w38,w55,w73,w105,w222,w238,w248] z))) [w38,w55,w73,w105,w222,w248] (n (n (n (n z [w38,w55,w73,w105,w222,w263,w271] z) [w38,w55,w73,w105,w222,w271] z) [w38,w55,w73,w121,w144,w177,w205] (n (n z [w38,w55,w73,w121,w166,w177,w205] z) [w38,w55,w73,w121,w173,w189,w205] z)) [w38,w55,w73,w121,w177,w189,w205] (n (n (n z [w38,w55,w73,w121,w177,w195,w222] z) [w38,w55,w73,w121,w189,w205] z) [w38,w55,w73,w121,w195,w205,w215] (n z [w38,w55,w73,w121,w195,w205,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbaabb : t6bbbaabb.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbbaab := (n t6bbbaaba [w38,w55,w73,w105,w195,w222,w273] t6bbbaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbaab : t6bbbaab.all (blocked 5 t5) = true := by
  simp only [t6bbbaab, ReplayTree.all, n, ht6bbbaaba, ht6bbbaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbbaa := (n t6bbbaaa [w38,w55,w73,w105,w189,w222] t6bbbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbaa : t6bbbaa.all (blocked 5 t5) = true := by
  simp only [t6bbbaa, ReplayTree.all, n, ht6bbbaaa, ht6bbbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbbabaa := (n (n (n (n (n z [w38,w55,w73,w177,w195,w222,w313] z) [w38,w55,w73,w195,w205,w222,w313] z) [w38,w55,w73,w195,w222,w313] (n (n z [w38,w55,w80,w91,w121,w177,w205] z) [w38,w55,w80,w105,w121,w177,w205] z)) [w38,w55,w80,w121,w177,w205] (n (n (n z [w38,w55,w84,w105,w121,w177,w205] z) [w38,w55,w84,w121,w177,w205] z) [w38,w55,w87,w94,w105,w177,w205] (n (n z [w38,w55,w87,w105,w121,w177,w205] z) [w38,w55,w87,w105,w177,w205,w222] z))) [w38,w55,w87,w105,w177,w222] (n (n (n (n z [w38,w55,w87,w121,w177,w205] z) [w38,w55,w91,w91,w121,w177,w205] z) [w38,w55,w91,w94,w105,w177,w205] (n (n z [w38,w55,w91,w96,w121,w177,w205] z) [w38,w55,w91,w99,w121,w177,w205] z)) [w38,w55,w91,w105,w116,w177,w222] (n (n (n z [w38,w55,w91,w105,w121,w173,w205] z) [w38,w55,w91,w105,w121,w177,w205] z) [w38,w55,w91,w105,w121,w177,w222] (n z [w38,w55,w91,w105,w121,w177,w296] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbabaa : t6bbbabaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbbabab := (n (n (n (n (n z [w38,w55,w91,w105,w121,w205,w238] z) [w38,w55,w91,w105,w121,w205,w263] z) [w38,w55,w91,w105,w121,w205,w313] (n (n z [w38,w55,w91,w105,w173,w198,w205] z) [w38,w55,w91,w105,w177,w195,w222] z)) [w38,w55,w91,w105,w177,w198,w205] (n (n (n z [w38,w55,w91,w105,w177,w201,w222] z) [w38,w55,w91,w105,w195,w205,w222] z) [w38,w55,w91,w105,w195,w222] (n (n z [w38,w55,w91,w107,w121,w177,w205] z) [w38,w55,w91,w116,w121,w177,w205] z))) [w38,w55,w91,w117,w121,w177,w205] (n (n (n (n z [w38,w55,w91,w121,w121,w177,w205] z) [w38,w55,w91,w121,w122,w177,w205] z) [w38,w55,w91,w121,w123,w177,w205] (n (n z [w38,w55,w91,w121,w124,w177,w205] z) [w38,w55,w91,w121,w134,w177,w205] z)) [w38,w55,w91,w121,w144,w177,w205] (n (n (n z [w38,w55,w91,w121,w149,w177,w205] z) [w38,w55,w91,w121,w154,w177,w205] z) [w38,w55,w91,w121,w158,w177,w205] (n z [w38,w55,w91,w121,w159,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbabab : t6bbbabab.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbbaba := (n t6bbbabaa [w38,w55,w91,w105,w121,w195,w205] t6bbbabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbaba : t6bbbaba.all (blocked 5 t5) = true := by
  simp only [t6bbbaba, ReplayTree.all, n, ht6bbbabaa, ht6bbbabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbbabba := (n (n (n (n (n z [w38,w55,w91,w121,w169,w177,w205] z) [w38,w55,w91,w121,w173,w177,w205] z) [w38,w55,w91,w121,w173,w205] (n (n z [w38,w55,w91,w121,w177,w195,w205] z) [w38,w55,w91,w121,w177,w201,w205] z)) [w38,w55,w91,w121,w177,w205] (n (n (n z [w38,w55,w91,w121,w177,w205,w210] z) [w38,w55,w91,w121,w177,w205,w215] z) [w38,w55,w91,w121,w177,w205,w222] (n (n z [w38,w55,w91,w121,w177,w205,w238] z) [w38,w55,w91,w121,w177,w205,w251] z))) [w38,w55,w91,w121,w177,w205,w261] (n (n (n (n z [w38,w55,w91,w121,w177,w205,w263] z) [w38,w55,w91,w121,w177,w205,w280] z) [w38,w55,w91,w121,w177,w205,w289] (n (n z [w38,w55,w91,w121,w177,w205,w296] z) [w38,w55,w91,w121,w177,w205,w304] z)) [w38,w55,w91,w121,w177,w205,w313] (n (n (n z [w38,w55,w91,w121,w177,w205,w324] z) [w38,w55,w91,w121,w177,w205,w329] z) [w38,w55,w91,w121,w177,w205,w336] (n z [w38,w55,w91,w121,w177,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbabba : t6bbbabba.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbbabbb := (n (n (n (n (n z [w38,w55,w91,w121,w195,w205] z) [w38,w55,w91,w121,w205,w238] z) [w38,w55,w91,w121,w205,w263] (n (n z [w38,w55,w91,w121,w205,w313] z) [w38,w55,w105,w121,w144,w177,w205] z)) [w38,w55,w105,w121,w166,w177,w205] (n (n (n z [w38,w55,w105,w134,w177,w195,w222] z) [w38,w55,w105,w134,w195,w205,w222] z) [w38,w55,w105,w134,w195,w222] (n z [w38,w55,w105,w158,w177,w195,w222] z))) [w38,w55,w105,w158,w195,w205,w222] (n (n (n (n z [w38,w55,w105,w158,w195,w222] z) [w38,w55,w105,w177,w195,w222,w296] z) [w38,w55,w105,w195,w205,w222,w296] (n (n z [w38,w55,w105,w195,w222,w296] z) [w38,w55,w121,w134,w144,w177,w205] z)) [w38,w55,w121,w144,w177,w205] (n (n (n z [w38,w55,w121,w158,w166,w177,w205] z) [w38,w55,w121,w166,w177,w205] z) [w38,w59,w63,w73,w105,w177,w222] (n z [w38,w59,w63,w73,w121,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbabbb : t6bbbabbb.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbbabb := (n t6bbbabba [w38,w55,w91,w121,w177,w296] t6bbbabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbabb : t6bbbabb.all (blocked 5 t5) = true := by
  simp only [t6bbbabb, ReplayTree.all, n, ht6bbbabba, ht6bbbabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbbab := (n t6bbbaba [w38,w55,w91,w121,w166,w177,w205] t6bbbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbab : t6bbbab.all (blocked 5 t5) = true := by
  simp only [t6bbbab, ReplayTree.all, n, ht6bbbaba, ht6bbbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbba := (n t6bbbaa [w38,w55,w73,w121,w195,w222] t6bbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbba : t6bbba.all (blocked 5 t5) = true := by
  simp only [t6bbba, ReplayTree.all, n, ht6bbbaa, ht6bbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbbbaaa := (n (n (n (n (n z [w38,w60,w73,w105,w177,w205,w222] z) [w38,w60,w73,w105,w177,w222] z) [w38,w60,w73,w121,w177,w205] (n (n z [w38,w63,w63,w73,w105,w177,w222] z) [w38,w63,w63,w73,w121,w177,w205] z)) [w38,w63,w65,w73,w105,w177,w222] (n (n (n z [w38,w63,w65,w73,w121,w177,w205] z) [w38,w63,w67,w73,w105,w177,w222] z) [w38,w63,w67,w73,w121,w177,w205] (n (n z [w38,w63,w68,w73,w105,w177,w222] z) [w38,w63,w68,w73,w121,w177,w205] z))) [w38,w63,w69,w73,w105,w177,w222] (n (n (n (n z [w38,w63,w69,w73,w121,w177,w205] z) [w38,w63,w69,w94,w105,w177,w205] z) [w38,w63,w69,w105,w121,w177,w205] (n (n z [w38,w63,w69,w105,w177,w205,w222] z) [w38,w63,w69,w105,w177,w222] z)) [w38,w63,w69,w121,w177,w205] (n (n (n z [w38,w63,w73,w91,w105,w177,w222] z) [w38,w63,w73,w91,w121,w177,w205] z) [w38,w63,w73,w94,w105,w177,w205] (n z [w38,w63,w73,w96,w105,w177,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbbaaa : t6bbbbaaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbbbaab := (n (n (n (n (n z [w38,w63,w73,w105,w107,w177,w222] z) [w38,w63,w73,w105,w116,w177,w222] z) [w38,w63,w73,w105,w121,w173,w205] (n (n z [w38,w63,w73,w105,w121,w177,w205] z) [w38,w63,w73,w105,w121,w177,w222] z)) [w38,w63,w73,w105,w121,w195,w205] (n (n (n z [w38,w63,w73,w105,w121,w205,w238] z) [w38,w63,w73,w105,w121,w205,w263] z) [w38,w63,w73,w105,w121,w205,w271] (n (n z [w38,w63,w73,w105,w121,w205,w313] z) [w38,w63,w73,w105,w134,w177,w222] z))) [w38,w63,w73,w105,w149,w177,w222] (n (n (n (n z [w38,w63,w73,w105,w158,w177,w222] z) [w38,w63,w73,w105,w159,w177,w222] z) [w38,w63,w73,w105,w166,w177,w222] (n (n z [w38,w63,w73,w105,w167,w177,w222] z) [w38,w63,w73,w105,w173,w177,w222] z)) [w38,w63,w73,w105,w173,w198,w205] (n (n (n z [w38,w63,w73,w105,w173,w205,w222] z) [w38,w63,w73,w105,w173,w222] z) [w38,w63,w73,w105,w177,w195,w222] (n z [w38,w63,w73,w105,w177,w198,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbbaab : t6bbbbaab.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbbbaa := (n t6bbbbaaa [w38,w63,w73,w96,w121,w177,w205] t6bbbbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbbaa : t6bbbbaa.all (blocked 5 t5) = true := by
  simp only [t6bbbbaa, ReplayTree.all, n, ht6bbbbaaa, ht6bbbbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbbbaba := (n (n (n (n (n z [w38,w63,w73,w105,w177,w205,w222] z) [w38,w63,w73,w105,w177,w205,w336] z) [w38,w63,w73,w105,w177,w210,w222] (n (n z [w38,w63,w73,w105,w177,w215,w222] z) [w38,w63,w73,w105,w177,w222] z)) [w38,w63,w73,w105,w177,w222,w222] (n (n (n z [w38,w63,w73,w105,w177,w222,w223] z) [w38,w63,w73,w105,w177,w222,w224] z) [w38,w63,w73,w105,w177,w222,w238] (n (n z [w38,w63,w73,w105,w177,w222,w251] z) [w38,w63,w73,w105,w177,w222,w256] z))) [w38,w63,w73,w105,w177,w222,w261] (n (n (n (n z [w38,w63,w73,w105,w177,w222,w263] z) [w38,w63,w73,w105,w177,w222,w269] z) [w38,w63,w73,w105,w177,w222,w271] (n (n z [w38,w63,w73,w105,w177,w222,w273] z) [w38,w63,w73,w105,w177,w222,w275] z)) [w38,w63,w73,w105,w177,w222,w280] (n (n (n z [w38,w63,w73,w105,w177,w222,w296] z) [w38,w63,w73,w105,w177,w222,w307] z) [w38,w63,w73,w105,w177,w222,w313] (n z [w38,w63,w73,w105,w177,w222,w329] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbbaba : t6bbbbaba.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbbbabb := (n (n (n (n (n z [w38,w63,w73,w105,w195,w205,w222] z) [w38,w63,w73,w105,w195,w222] z) [w38,w63,w73,w105,w205,w222,w238] (n (n z [w38,w63,w73,w105,w205,w222,w263] z) [w38,w63,w73,w105,w205,w222,w271] z)) [w38,w63,w73,w105,w205,w222,w313] (n (n (n z [w38,w63,w73,w105,w222,w238] z) [w38,w63,w73,w105,w222,w263] z) [w38,w63,w73,w105,w222,w271] (n z [w38,w63,w73,w107,w121,w177,w205] z))) [w38,w63,w73,w116,w121,w177,w205] (n (n (n (n z [w38,w63,w73,w121,w121,w177,w205] z) [w38,w63,w73,w121,w122,w177,w205] z) [w38,w63,w73,w121,w123,w177,w205] (n (n z [w38,w63,w73,w121,w134,w177,w205] z) [w38,w63,w73,w121,w149,w177,w205] z)) [w38,w63,w73,w121,w154,w177,w205] (n (n (n z [w38,w63,w73,w121,w158,w177,w205] z) [w38,w63,w73,w121,w159,w177,w205] z) [w38,w63,w73,w121,w166,w177,w205] (n z [w38,w63,w73,w121,w167,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbbabb : t6bbbbabb.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbbbab := (n t6bbbbaba [w38,w63,w73,w105,w177,w222,w336] t6bbbbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbbab : t6bbbbab.all (blocked 5 t5) = true := by
  simp only [t6bbbbab, ReplayTree.all, n, ht6bbbbaba, ht6bbbbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbbba := (n t6bbbbaa [w38,w63,w73,w105,w177,w201,w222] t6bbbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbba : t6bbbba.all (blocked 5 t5) = true := by
  simp only [t6bbbba, ReplayTree.all, n, ht6bbbbaa, ht6bbbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbbbbaa := (n (n (n (n (n z [w38,w63,w73,w121,w171,w177,w205] z) [w38,w63,w73,w121,w173,w177,w205] z) [w38,w63,w73,w121,w173,w205] (n (n z [w38,w63,w73,w121,w177,w195,w205] z) [w38,w63,w73,w121,w177,w201,w205] z)) [w38,w63,w73,w121,w177,w205] (n (n (n z [w38,w63,w73,w121,w177,w205,w210] z) [w38,w63,w73,w121,w177,w205,w215] z) [w38,w63,w73,w121,w177,w205,w222] (n (n z [w38,w63,w73,w121,w177,w205,w238] z) [w38,w63,w73,w121,w177,w205,w251] z))) [w38,w63,w73,w121,w177,w205,w261] (n (n (n (n z [w38,w63,w73,w121,w177,w205,w263] z) [w38,w63,w73,w121,w177,w205,w269] z) [w38,w63,w73,w121,w177,w205,w271] (n (n z [w38,w63,w73,w121,w177,w205,w280] z) [w38,w63,w73,w121,w177,w205,w296] z)) [w38,w63,w73,w121,w177,w205,w313] (n (n (n z [w38,w63,w73,w121,w177,w205,w324] z) [w38,w63,w73,w121,w177,w205,w329] z) [w38,w63,w73,w121,w177,w205,w336] (n z [w38,w63,w73,w121,w177,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbbbaa : t6bbbbbaa.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbbbbab := (n (n (n (n (n z [w38,w63,w73,w121,w205,w238] z) [w38,w63,w73,w121,w205,w263] z) [w38,w63,w73,w121,w205,w271] (n (n z [w38,w63,w73,w121,w205,w313] z) [w38,w63,w91,w105,w121,w177,w205] z)) [w38,w63,w91,w105,w177,w205,w222] (n (n (n z [w38,w63,w91,w105,w177,w222] z) [w38,w63,w91,w121,w177,w205] z) [w38,w63,w105,w121,w134,w177,w205] (n (n z [w38,w63,w105,w121,w158,w177,w205] z) [w38,w63,w105,w121,w166,w177,w205] z))) [w38,w63,w105,w121,w177,w205,w296] (n (n (n (n z [w38,w63,w105,w134,w177,w205,w222] z) [w38,w63,w105,w134,w177,w222] z) [w38,w63,w105,w158,w177,w205,w222] (n (n z [w38,w63,w105,w158,w177,w222] z) [w38,w63,w105,w166,w177,w205,w222] z)) [w38,w63,w105,w166,w177,w222] (n (n (n z [w38,w63,w105,w177,w205,w222,w296] z) [w38,w63,w105,w177,w222,w296] z) [w38,w63,w121,w134,w177,w205] (n z [w38,w63,w121,w158,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbbbab : t6bbbbbab.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbbbba := (n t6bbbbbaa [w38,w63,w73,w121,w195,w205] t6bbbbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbbba : t6bbbbba.all (blocked 5 t5) = true := by
  simp only [t6bbbbba, ReplayTree.all, n, ht6bbbbbaa, ht6bbbbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbbbbba := (n (n (n (n (n z [w45,w50,w55,w73,w105,w177,w205] z) [w46,w55,w65,w73,w105,w177,w205] z) [w46,w55,w73,w105,w121,w177,w205] (n (n z [w46,w55,w73,w105,w177,w205,w222] z) [w46,w55,w73,w105,w177,w222] z)) [w46,w55,w73,w121,w177,w205] (n (n (n z [w47,w50,w55,w73,w105,w177,w222] z) [w47,w50,w55,w73,w121,w177,w205] z) [w50,w55,w73,w105,w121,w205,w238] (n (n z [w50,w55,w73,w105,w134,w177,w222] z) [w50,w55,w73,w105,w149,w177,w222] z))) [w50,w55,w73,w105,w177,w222,w238] (n (n (n (n z [w50,w55,w73,w105,w177,w222,w251] z) [w50,w55,w73,w105,w177,w222,w256] z) [w50,w55,w73,w105,w205,w222,w238] (n (n z [w50,w55,w73,w105,w222,w238] z) [w50,w55,w73,w121,w134,w177,w205] z)) [w50,w55,w73,w121,w149,w177,w205] (n (n (n z [w50,w55,w73,w121,w154,w177,w205] z) [w50,w55,w73,w121,w177,w205,w238] z) [w50,w55,w73,w121,w177,w205,w251] (n z [w50,w55,w73,w121,w205,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbbbba : t6bbbbbba.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbbbbbb := (n (n (n (n (n z [w50,w55,w105,w134,w177,w205,w222] z) [w50,w55,w105,w134,w177,w222] z) [w50,w55,w121,w134,w177,w205] (n (n z [w55,w63,w73,w105,w177,w222,w238] z) [w55,w63,w73,w105,w205,w222,w238] z)) [w55,w63,w73,w105,w222,w238] (n (n (n z [w55,w63,w73,w121,w134,w177,w205] z) [w55,w63,w105,w121,w134,w177,w205] z) [w55,w63,w121,w134,w177,w205] (n z [w55,w73,w91,w121,w134,w177,w205] z))) [w55,w73,w105,w177,w195,w222,w238] (n (n (n (n z [w55,w73,w105,w177,w222,w238,w248] z) [w55,w73,w105,w195,w205,w222,w238] z) [w55,w73,w105,w195,w222,w238] (n (n z [w55,w73,w105,w205,w222,w238,w248] z) [w55,w73,w105,w222,w238,w248] z)) [w55,w73,w121,w134,w144,w177,w205] (n (n (n z [w55,w91,w105,w121,w134,w177,w205] z) [w55,w91,w121,w134,w177,w205] z) [w55,w105,w121,w134,w144,w177,w205] (n z [w55,w121,w134,w144,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbbbbb : t6bbbbbbb.all (blocked 5 t5) = true := by
  decide +kernel
def t6bbbbbb := (n t6bbbbbba [w50,w55,w105,w121,w134,w177,w205] t6bbbbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbbbb : t6bbbbbb.all (blocked 5 t5) = true := by
  simp only [t6bbbbbb, ReplayTree.all, n, ht6bbbbbba, ht6bbbbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbbbb := (n t6bbbbba [w38,w63,w121,w166,w177,w205] t6bbbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbbb : t6bbbbb.all (blocked 5 t5) = true := by
  simp only [t6bbbbb, ReplayTree.all, n, ht6bbbbba, ht6bbbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbbb := (n t6bbbba [w38,w63,w73,w121,w169,w177,w205] t6bbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbbb : t6bbbb.all (blocked 5 t5) = true := by
  simp only [t6bbbb, ReplayTree.all, n, ht6bbbba, ht6bbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bbb := (n t6bbba [w38,w60,w73,w105,w121,w177,w205] t6bbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bbb : t6bbb.all (blocked 5 t5) = true := by
  simp only [t6bbb, ReplayTree.all, n, ht6bbba, ht6bbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6bb := (n t6bba [w38,w55,w68,w73,w121,w177,w205] t6bbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6bb : t6bb.all (blocked 5 t5) = true := by
  simp only [t6bb, ReplayTree.all, n, ht6bba, ht6bbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6b := (n t6ba [w23,w55,w69,w105,w195,w205,w238] t6bb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6b : t6b.all (blocked 5 t5) = true := by
  simp only [t6b, ReplayTree.all, n, ht6ba, ht6bb, Bool.true_and, Bool.and_true]
  decide +kernel
def t6 := (n t6a [w23,w38,w50,w55,w105,w177,w296] t6b)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht6 : t6.all (blocked 5 t5) = true := by
  simp only [t6, ReplayTree.all, n, ht6a, ht6b, Bool.true_and, Bool.and_true]
  decide +kernel
lemma s6 : sound 6 t6 := layer_sound s5 ht6
def t7aaaaa := (n (n (n (n (n z [w0,w17,w23,w38,w55,w73,w205,w313] z) [w0,w17,w23,w38,w55,w105,w177,w296] (n z [w0,w17,w23,w55,w73,w105,w205,w238] z)) [w0,w17,w23,w55,w105,w134,w177,w205] (n (n z [w0,w17,w38,w55,w73,w105,w177,w222] z) [w0,w17,w38,w55,w73,w121,w177,w205] (n z [w0,w23,w38,w55,w73,w105,w195,w205] z))) [w0,w23,w38,w55,w91,w105,w177,w205] (n (n (n z [w0,w23,w38,w63,w73,w105,w177,w205] z) [w1,w17,w23,w38,w55,w73,w205,w313] (n z [w1,w17,w23,w38,w55,w105,w177,w296] z)) [w1,w17,w23,w55,w73,w105,w205,w238] (n (n z [w1,w17,w23,w55,w105,w134,w177,w205] z) [w1,w17,w38,w55,w73,w105,w177,w222] (n z [w1,w17,w38,w55,w73,w121,w177,w205] z)))) [w1,w23,w38,w55,w73,w105,w195,w205] (n (n (n (n z [w1,w23,w38,w55,w91,w105,w177,w205] z) [w1,w23,w38,w63,w73,w105,w177,w205] (n z [w2,w17,w23,w38,w55,w73,w205,w313] z)) [w2,w17,w23,w38,w55,w105,w177,w296] (n (n z [w2,w17,w23,w55,w73,w105,w205,w238] z) [w2,w17,w23,w55,w105,w134,w177,w205] (n z [w2,w17,w38,w55,w73,w105,w177,w222] z))) [w2,w17,w38,w55,w73,w121,w177,w205] (n (n (n z [w2,w23,w38,w55,w73,w105,w195,w205] z) [w2,w23,w38,w55,w91,w105,w177,w205] (n z [w2,w23,w38,w63,w73,w105,w177,w205] z)) [w3,w17,w23,w38,w55,w73,w205,w313] (n (n z [w3,w17,w23,w38,w55,w105,w177,w296] z) [w3,w17,w23,w55,w73,w105,w205,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7aaaaa : t7aaaaa.all (blocked 6 t6) = true := by
  decide +kernel
def t7aaaab := (n (n (n (n (n z [w3,w17,w38,w55,w73,w105,w177,w222] z) [w3,w17,w38,w55,w73,w121,w177,w205] (n z [w3,w23,w38,w55,w73,w105,w195,w205] z)) [w3,w23,w38,w55,w91,w105,w177,w205] (n (n z [w3,w23,w38,w63,w73,w105,w177,w205] z) [w4,w17,w23,w38,w55,w73,w205,w313] (n z [w4,w17,w23,w38,w55,w105,w177,w296] z))) [w4,w17,w23,w55,w73,w105,w205,w238] (n (n (n z [w4,w17,w23,w55,w105,w134,w177,w205] z) [w4,w17,w38,w55,w73,w105,w177,w222] (n z [w4,w17,w38,w55,w73,w121,w177,w205] z)) [w4,w23,w38,w55,w73,w105,w195,w205] (n (n z [w4,w23,w38,w55,w91,w105,w177,w205] z) [w4,w23,w38,w63,w73,w105,w177,w205] (n z [w5,w17,w23,w38,w55,w73,w205,w313] z)))) [w5,w17,w23,w38,w55,w105,w177,w296] (n (n (n (n z [w5,w17,w23,w55,w73,w105,w205,w238] z) [w5,w17,w23,w55,w105,w134,w177,w205] (n z [w5,w17,w38,w55,w73,w105,w177,w222] z)) [w5,w17,w38,w55,w73,w121,w177,w205] (n (n z [w5,w23,w38,w55,w73,w105,w195,w205] z) [w5,w23,w38,w55,w91,w105,w177,w205] (n z [w5,w23,w38,w63,w73,w105,w177,w205] z))) [w6,w17,w23,w38,w55,w73,w205,w313] (n (n (n z [w6,w17,w23,w38,w55,w105,w177,w296] z) [w6,w17,w23,w55,w73,w105,w205,w238] (n z [w6,w17,w23,w55,w105,w134,w177,w205] z)) [w6,w17,w38,w55,w73,w105,w177,w222] (n (n z [w6,w17,w38,w55,w73,w121,w177,w205] z) [w6,w23,w38,w55,w73,w105,w195,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7aaaab : t7aaaab.all (blocked 6 t6) = true := by
  decide +kernel
def t7aaaa := (n t7aaaaa [w3,w17,w23,w55,w105,w134,w177,w205] t7aaaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7aaaa : t7aaaa.all (blocked 6 t6) = true := by
  simp only [t7aaaa, ReplayTree.all, n, ht7aaaaa, ht7aaaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aaaba := (n (n (n (n (n z [w6,w23,w38,w63,w73,w105,w177,w205] z) [w7,w17,w23,w38,w55,w73,w205,w313] (n z [w7,w17,w23,w38,w55,w105,w177,w296] z)) [w7,w17,w23,w55,w73,w105,w205,w238] (n (n z [w7,w17,w23,w55,w105,w134,w177,w205] z) [w7,w17,w38,w55,w73,w105,w177,w222] (n z [w7,w17,w38,w55,w73,w121,w177,w205] z))) [w7,w23,w38,w55,w73,w105,w195,w205] (n (n (n z [w7,w23,w38,w55,w91,w105,w177,w205] z) [w7,w23,w38,w63,w73,w105,w177,w205] (n z [w8,w17,w23,w38,w55,w73,w205,w313] z)) [w8,w17,w23,w38,w55,w105,w177,w296] (n (n z [w8,w17,w23,w55,w73,w105,w205,w238] z) [w8,w17,w23,w55,w105,w134,w177,w205] (n z [w8,w17,w38,w55,w73,w105,w177,w222] z)))) [w8,w17,w38,w55,w73,w121,w177,w205] (n (n (n (n z [w8,w23,w38,w55,w73,w105,w195,w205] z) [w8,w23,w38,w55,w91,w105,w177,w205] (n z [w8,w23,w38,w63,w73,w105,w177,w205] z)) [w10,w17,w23,w38,w55,w73,w205,w313] (n (n z [w10,w17,w23,w38,w55,w105,w177,w296] z) [w10,w17,w23,w55,w73,w105,w205,w238] (n z [w10,w17,w23,w55,w105,w134,w177,w205] z))) [w10,w17,w38,w55,w73,w105,w177,w222] (n (n (n z [w10,w17,w38,w55,w73,w121,w177,w205] z) [w10,w23,w38,w55,w73,w105,w195,w205] (n z [w10,w23,w38,w55,w91,w105,w177,w205] z)) [w10,w23,w38,w63,w73,w105,w177,w205] (n (n z [w12,w13,w38,w55,w73,w105,w177,w205] z) [w12,w17,w23,w38,w55,w73,w205,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7aaaba : t7aaaba.all (blocked 6 t6) = true := by
  decide +kernel
def t7aaabb := (n (n (n (n (n z [w12,w17,w23,w55,w73,w105,w205,w238] z) [w12,w17,w23,w55,w105,w134,w177,w205] (n z [w12,w17,w38,w55,w73,w105,w177,w222] z)) [w12,w17,w38,w55,w73,w121,w177,w205] (n (n z [w12,w17,w47,w55,w73,w105,w177,w205] z) [w12,w23,w38,w55,w73,w105,w195,w205] (n z [w12,w23,w38,w55,w91,w105,w177,w205] z))) [w12,w23,w38,w63,w73,w105,w177,w205] (n (n (n z [w13,w17,w23,w38,w55,w73,w205,w313] z) [w13,w17,w23,w38,w55,w105,w177,w296] (n z [w13,w17,w23,w55,w73,w105,w205,w238] z)) [w13,w17,w23,w55,w105,w134,w177,w205] (n (n z [w13,w17,w38,w55,w73,w105,w177,w222] z) [w13,w17,w38,w55,w73,w121,w177,w205] (n z [w13,w23,w38,w55,w69,w105,w177,w205] z)))) [w13,w23,w38,w55,w73,w105,w173,w205] (n (n (n (n z [w13,w23,w38,w55,w73,w105,w177,w205] z) [w13,w23,w38,w55,w73,w105,w177,w213] (n z [w13,w23,w38,w55,w73,w105,w177,w222] z)) [w13,w23,w38,w55,w73,w105,w177,w296] (n (n z [w13,w23,w38,w55,w73,w105,w192,w205] z) [w13,w23,w38,w55,w73,w105,w195,w205] (n z [w13,w23,w38,w55,w73,w105,w205,w238] z))) [w13,w23,w38,w55,w73,w105,w205,w263] (n (n (n z [w13,w23,w38,w55,w73,w105,w205,w313] z) [w13,w23,w38,w55,w73,w113,w177,w205] (n z [w13,w23,w38,w55,w73,w121,w177,w205] z)) [w13,w23,w38,w55,w73,w177,w205,w313] (n (n z [w13,w23,w38,w55,w73,w205,w313] z) [w13,w23,w38,w55,w84,w105,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7aaabb : t7aaabb.all (blocked 6 t6) = true := by
  decide +kernel
def t7aaab := (n t7aaaba [w12,w17,w23,w38,w55,w105,w177,w296] t7aaabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7aaab : t7aaab.all (blocked 6 t6) = true := by
  simp only [t7aaab, ReplayTree.all, n, ht7aaaba, ht7aaabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aaa := (n t7aaaa [w6,w23,w38,w55,w91,w105,w177,w205] t7aaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7aaa : t7aaa.all (blocked 6 t6) = true := by
  simp only [t7aaa, ReplayTree.all, n, ht7aaaa, ht7aaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aabaa := (n (n (n (n (n z [w13,w23,w38,w55,w105,w134,w177,w205] z) [w13,w23,w38,w55,w105,w158,w177,w205] (n z [w13,w23,w38,w55,w105,w177,w205,w296] z)) [w13,w23,w38,w55,w105,w177,w296] (n (n z [w13,w23,w38,w60,w73,w105,w177,w205] z) [w13,w23,w38,w63,w73,w105,w177,w205] (n z [w13,w23,w46,w55,w73,w105,w177,w205] z))) [w13,w23,w55,w73,w105,w134,w177,w205] (n (n (n z [w13,w23,w55,w73,w105,w177,w205,w238] z) [w13,w23,w55,w73,w105,w205,w238] (n z [w13,w23,w55,w105,w134,w177,w205] z)) [w13,w27,w38,w55,w73,w105,w177,w205] (n (n z [w13,w38,w55,w65,w73,w105,w177,w205] z) [w13,w38,w55,w73,w105,w121,w177,w205] (n z [w13,w38,w55,w73,w105,w177,w205,w222] z)))) [w13,w38,w55,w73,w105,w177,w222] (n (n (n (n z [w13,w38,w55,w73,w121,w177,w205] z) [w14,w23,w38,w55,w73,w105,w177,w205] (n z [w15,w23,w38,w55,w73,w105,w177,w205] z)) [w16,w23,w38,w55,w73,w105,w177,w205] (n (n z [w17,w22,w38,w55,w73,w105,w177,w205] z) [w17,w23,w27,w38,w55,w73,w205,w313] (n z [w17,w23,w27,w38,w55,w105,w177,w296] z))) [w17,w23,w27,w55,w73,w105,w205,w238] (n (n (n z [w17,w23,w27,w55,w105,w134,w177,w205] z) [w17,w23,w28,w38,w55,w73,w105,w173] (n z [w17,w23,w28,w38,w55,w73,w205,w313] z)) [w17,w23,w28,w38,w55,w105,w177,w296] (n (n z [w17,w23,w28,w38,w73,w105,w177,w261] z) [w17,w23,w28,w55,w73,w105,w205,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7aabaa : t7aabaa.all (blocked 6 t6) = true := by
  decide +kernel
def t7aabab := (n (n (n (n (n z [w17,w23,w32,w38,w55,w69,w177,w205] z) [w17,w23,w32,w38,w55,w73,w205,w313] (n z [w17,w23,w32,w38,w55,w105,w177,w296] z)) [w17,w23,w32,w38,w73,w159,w177,w205] (n (n z [w17,w23,w32,w55,w73,w105,w205,w238] z) [w17,w23,w32,w55,w105,w134,w177,w205] (n z [w17,w23,w36,w38,w55,w73,w205,w313] z))) [w17,w23,w36,w38,w55,w105,w177,w296] (n (n (n z [w17,w23,w36,w55,w73,w105,w205,w238] z) [w17,w23,w36,w55,w105,w134,w177,w205] (n z [w17,w23,w36,w59,w73,w105,w177,w205] z)) [w17,w23,w37,w55,w73,w105,w177,w205] (n (n z [w17,w23,w38,w47,w55,w73,w205,w313] z) [w17,w23,w38,w47,w55,w105,w177,w296] (n z [w17,w23,w38,w50,w55,w73,w205,w313] z)))) [w17,w23,w38,w50,w55,w105,w177,w296] (n (n (n (n z [w17,w23,w38,w55,w59,w73,w205,w313] z) [w17,w23,w38,w55,w59,w105,w177,w296] (n z [w17,w23,w38,w55,w63,w73,w205,w313] z)) [w17,w23,w38,w55,w63,w105,w177,w296] (n (n z [w17,w23,w38,w55,w65,w73,w205,w313] z) [w17,w23,w38,w55,w65,w105,w177,w296] (n z [w17,w23,w38,w55,w69,w73,w205,w313] z))) [w17,w23,w38,w55,w69,w105,w173,w205] (n (n (n z [w17,w23,w38,w55,w69,w105,w177,w205] z) [w17,w23,w38,w55,w69,w105,w177,w222] (n z [w17,w23,w38,w55,w69,w105,w177,w292] z)) [w17,w23,w38,w55,w69,w105,w177,w296] (n (n z [w17,w23,w38,w55,w69,w105,w195,w205] z) [w17,w23,w38,w55,w69,w105,w205,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7aabab : t7aabab.all (blocked 6 t6) = true := by
  decide +kernel
def t7aaba := (n t7aabaa [w17,w23,w28,w55,w105,w134,w177,w205] t7aabab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7aaba : t7aaba.all (blocked 6 t6) = true := by
  simp only [t7aaba, ReplayTree.all, n, ht7aabaa, ht7aabab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aabba := (n (n (n (n (n z [w17,w23,w38,w55,w69,w105,w205,w279] z) [w17,w23,w38,w55,w69,w105,w205,w313] (n z [w17,w23,w38,w55,w69,w107,w177,w205] z)) [w17,w23,w38,w55,w69,w121,w177,w205] (n (n z [w17,w23,w38,w55,w69,w149,w177,w205] z) [w17,w23,w38,w55,w69,w177,w205,w313] (n z [w17,w23,w38,w55,w69,w177,w205,w329] z))) [w17,w23,w38,w55,w69,w205,w313] (n (n (n z [w17,w23,w38,w55,w70,w105,w177,w205] z) [w17,w23,w38,w55,w71,w105,w177,w205] (n z [w17,w23,w38,w55,w72,w105,w177,w205] z)) [w17,w23,w38,w55,w73,w91,w205,w313] (n (n z [w17,w23,w38,w55,w73,w96,w205,w313] z) [w17,w23,w38,w55,w73,w103,w177,w205] (n z [w17,w23,w38,w55,w73,w105,w173,w205] z)))) [w17,w23,w38,w55,w73,w105,w173,w210] (n (n (n (n z [w17,w23,w38,w55,w73,w105,w173,w222] z) [w17,w23,w38,w55,w73,w105,w173,w251] (n z [w17,w23,w38,w55,w73,w105,w173,w296] z)) [w17,w23,w38,w55,w73,w105,w173,w329] (n (n z [w17,w23,w38,w55,w73,w105,w174,w205] z) [w17,w23,w38,w55,w73,w105,w175,w205] (n z [w17,w23,w38,w55,w73,w105,w176,w205] z))) [w17,w23,w38,w55,w73,w105,w177,w204] (n (n (n z [w17,w23,w38,w55,w73,w105,w177,w205] z) [w17,w23,w38,w55,w73,w105,w177,w206] (n z [w17,w23,w38,w55,w73,w105,w177,w207] z)) [w17,w23,w38,w55,w73,w105,w177,w208] (n (n z [w17,w23,w38,w55,w73,w105,w177,w211] z) [w17,w23,w38,w55,w73,w105,w177,w213] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7aabba : t7aabba.all (blocked 6 t6) = true := by
  decide +kernel
def t7aabbb := (n (n (n (n (n z [w17,w23,w38,w55,w73,w105,w177,w229] z) [w17,w23,w38,w55,w73,w105,w177,w249] (n z [w17,w23,w38,w55,w73,w105,w177,w292] z)) [w17,w23,w38,w55,w73,w105,w177,w296] (n (n z [w17,w23,w38,w55,w73,w105,w177,w307] z) [w17,w23,w38,w55,w73,w105,w178,w205] (n z [w17,w23,w38,w55,w73,w105,w179,w205] z))) [w17,w23,w38,w55,w73,w105,w180,w205] (n (n (n z [w17,w23,w38,w55,w73,w105,w181,w205] z) [w17,w23,w38,w55,w73,w105,w183,w205] (n z [w17,w23,w38,w55,w73,w105,w189,w205] z)) [w17,w23,w38,w55,w73,w105,w192,w205] (n (n z [w17,w23,w38,w55,w73,w105,w195,w205] z) [w17,w23,w38,w55,w73,w105,w195,w222] (n z [w17,w23,w38,w55,w73,w105,w204] z)))) [w17,w23,w38,w55,w73,w105,w204,w205] (n (n (n (n z [w17,w23,w38,w55,w73,w105,w204,w263] z) [w17,w23,w38,w55,w73,w105,w205,w209] (n z [w17,w23,w38,w55,w73,w105,w205,w226] z)) [w17,w23,w38,w55,w73,w105,w205,w232] (n (n z [w17,w23,w38,w55,w73,w105,w205,w234] z) [w17,w23,w38,w55,w73,w105,w205,w238] (n z [w17,w23,w38,w55,w73,w105,w205,w248] z))) [w17,w23,w38,w55,w73,w105,w205,w260] (n (n (n z [w17,w23,w38,w55,w73,w105,w205,w263] z) [w17,w23,w38,w55,w73,w105,w205,w265] (n z [w17,w23,w38,w55,w73,w105,w205,w271] z)) [w17,w23,w38,w55,w73,w105,w205,w279] (n (n z [w17,w23,w38,w55,w73,w105,w205,w309] z) [w17,w23,w38,w55,w73,w105,w205,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7aabbb : t7aabbb.all (blocked 6 t6) = true := by
  decide +kernel
def t7aabb := (n t7aabba [w17,w23,w38,w55,w73,w105,w177,w222] t7aabbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7aabb : t7aabb.all (blocked 6 t6) = true := by
  simp only [t7aabb, ReplayTree.all, n, ht7aabba, ht7aabbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aab := (n t7aaba [w17,w23,w38,w55,w69,w105,w205,w263] t7aabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7aab : t7aab.all (blocked 6 t6) = true := by
  simp only [t7aab, ReplayTree.all, n, ht7aaba, ht7aabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aa := (n t7aaa [w13,w23,w38,w55,w91,w105,w177,w205] t7aab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7aa : t7aa.all (blocked 6 t6) = true := by
  simp only [t7aa, ReplayTree.all, n, ht7aaa, ht7aab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abaaa := (n (n (n (n (n z [w17,w23,w38,w55,w73,w105,w205,w352] z) [w17,w23,w38,w55,w73,w105,w205,w357] (n z [w17,w23,w38,w55,w73,w105,w222,w238] z)) [w17,w23,w38,w55,w73,w105,w222,w263] (n (n z [w17,w23,w38,w55,w73,w105,w263,w296] z) [w17,w23,w38,w55,w73,w105,w296,w313] (n z [w17,w23,w38,w55,w73,w106,w177,w205] z))) [w17,w23,w38,w55,w73,w107,w205,w313] (n (n (n z [w17,w23,w38,w55,w73,w108,w177,w205] z) [w17,w23,w38,w55,w73,w109,w177,w205] (n z [w17,w23,w38,w55,w73,w110,w177,w205] z)) [w17,w23,w38,w55,w73,w113,w177,w205] (n (n z [w17,w23,w38,w55,w73,w116,w205,w313] z) [w17,w23,w38,w55,w73,w121,w173,w205] (n z [w17,w23,w38,w55,w73,w121,w177,w205] z)))) [w17,w23,w38,w55,w73,w121,w177,w222] (n (n (n (n z [w17,w23,w38,w55,w73,w121,w177,w296] z) [w17,w23,w38,w55,w73,w121,w195,w205] (n z [w17,w23,w38,w55,w73,w121,w205,w238] z)) [w17,w23,w38,w55,w73,w121,w205,w263] (n (n z [w17,w23,w38,w55,w73,w121,w205,w313] z) [w17,w23,w38,w55,w73,w125,w177,w205] (n z [w17,w23,w38,w55,w73,w134,w205,w313] z))) [w17,w23,w38,w55,w73,w146,w177,w205] (n (n (n z [w17,w23,w38,w55,w73,w149,w205,w313] z) [w17,w23,w38,w55,w73,w158,w205,w313] (n z [w17,w23,w38,w55,w73,w159,w205,w313] z)) [w17,w23,w38,w55,w73,w173,w205,w309] (n (n z [w17,w23,w38,w55,w73,w173,w205,w313] z) [w17,w23,w38,w55,w73,w177,w205,w309] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7abaaa : t7abaaa.all (blocked 6 t6) = true := by
  decide +kernel
def t7abaab := (n (n (n (n (n z [w17,w23,w38,w55,w73,w177,w205,w324] z) [w17,w23,w38,w55,w73,w177,w222,w313] (n z [w17,w23,w38,w55,w73,w177,w296,w313] z)) [w17,w23,w38,w55,w73,w195,w205,w313] (n (n z [w17,w23,w38,w55,w73,w201,w205,w313] z) [w17,w23,w38,w55,w73,w205,w210,w313] (n z [w17,w23,w38,w55,w73,w205,w215,w313] z))) [w17,w23,w38,w55,w73,w205,w222,w313] (n (n (n z [w17,w23,w38,w55,w73,w205,w238,w313] z) [w17,w23,w38,w55,w73,w205,w251,w313] (n z [w17,w23,w38,w55,w73,w205,w261,w313] z)) [w17,w23,w38,w55,w73,w205,w263,w313] (n (n z [w17,w23,w38,w55,w73,w205,w280,w313] z) [w17,w23,w38,w55,w73,w205,w296,w313] (n z [w17,w23,w38,w55,w73,w205,w309] z)))) [w17,w23,w38,w55,w73,w205,w313] (n (n (n (n z [w17,w23,w38,w55,w73,w205,w313,w313] z) [w17,w23,w38,w55,w73,w205,w313,w314] (n z [w17,w23,w38,w55,w73,w205,w313,w321] z)) [w17,w23,w38,w55,w73,w205,w313,w324] (n (n z [w17,w23,w38,w55,w73,w205,w313,w329] z) [w17,w23,w38,w55,w73,w205,w313,w332] (n z [w17,w23,w38,w55,w73,w205,w313,w352] z))) [w17,w23,w38,w55,w73,w205,w313,w357] (n (n (n z [w17,w23,w38,w55,w73,w296,w313] z) [w17,w23,w38,w55,w74,w105,w177,w205] (n z [w17,w23,w38,w55,w75,w105,w177,w205] z)) [w17,w23,w38,w55,w76,w105,w177,w205] (n (n z [w17,w23,w38,w55,w77,w105,w177,w205] z) [w17,w23,w38,w55,w79,w105,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7abaab : t7abaab.all (blocked 6 t6) = true := by
  decide +kernel
def t7abaa := (n t7abaaa [w17,w23,w38,w55,w73,w177,w205,w313] t7abaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7abaa : t7abaa.all (blocked 6 t6) = true := by
  simp only [t7abaa, ReplayTree.all, n, ht7abaaa, ht7abaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7ababa := (n (n (n (n (n z [w17,w23,w38,w55,w87,w105,w177,w205] z) [w17,w23,w38,w55,w91,w105,w173,w205] (n z [w17,w23,w38,w55,w91,w105,w177,w205] z)) [w17,w23,w38,w55,w91,w105,w177,w222] (n (n z [w17,w23,w38,w55,w91,w105,w177,w296] z) [w17,w23,w38,w55,w91,w105,w195,w205] (n z [w17,w23,w38,w55,w91,w105,w205,w238] z))) [w17,w23,w38,w55,w91,w105,w205,w263] (n (n (n z [w17,w23,w38,w55,w91,w105,w205,w313] z) [w17,w23,w38,w55,w91,w121,w177,w205] (n z [w17,w23,w38,w55,w96,w105,w177,w296] z)) [w17,w23,w38,w55,w100,w105,w177,w205] (n (n z [w17,w23,w38,w55,w103,w105,w177,w205] z) [w17,w23,w38,w55,w103,w158,w177,w205] (n z [w17,w23,w38,w55,w103,w177,w205] z)))) [w17,w23,w38,w55,w104,w105,w177,w205] (n (n (n (n z [w17,w23,w38,w55,w105,w107,w177,w296] z) [w17,w23,w38,w55,w105,w116,w177,w296] (n z [w17,w23,w38,w55,w105,w121,w177,w296] z)) [w17,w23,w38,w55,w105,w128,w177,w205] (n (n z [w17,w23,w38,w55,w105,w131,w177,w205] z) [w17,w23,w38,w55,w105,w134,w173,w205] (n z [w17,w23,w38,w55,w105,w134,w177,w205] z))) [w17,w23,w38,w55,w105,w134,w177,w222] (n (n (n z [w17,w23,w38,w55,w105,w134,w177,w296] z) [w17,w23,w38,w55,w105,w134,w195,w205] (n z [w17,w23,w38,w55,w105,w134,w205,w238] z)) [w17,w23,w38,w55,w105,w134,w205,w263] (n (n z [w17,w23,w38,w55,w105,w134,w205,w313] z) [w17,w23,w38,w55,w105,w144,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7ababa : t7ababa.all (blocked 6 t6) = true := by
  decide +kernel
def t7ababb := (n (n (n (n (n z [w17,w23,w38,w55,w105,w156,w177,w205] z) [w17,w23,w38,w55,w105,w158,w173,w205] (n z [w17,w23,w38,w55,w105,w158,w177,w205] z)) [w17,w23,w38,w55,w105,w158,w177,w222] (n (n z [w17,w23,w38,w55,w105,w158,w177,w296] z) [w17,w23,w38,w55,w105,w158,w195,w205] (n z [w17,w23,w38,w55,w105,w158,w205,w238] z))) [w17,w23,w38,w55,w105,w158,w205,w263] (n (n (n z [w17,w23,w38,w55,w105,w158,w205,w313] z) [w17,w23,w38,w55,w105,w159,w177,w296] (n z [w17,w23,w38,w55,w105,w161,w177,w205] z)) [w17,w23,w38,w55,w105,w166,w177,w205] (n (n z [w17,w23,w38,w55,w105,w173,w177,w296] z) [w17,w23,w38,w55,w105,w173,w205,w278] (n z [w17,w23,w38,w55,w105,w173,w205,w296] z)))) [w17,w23,w38,w55,w105,w173,w296] (n (n (n (n z [w17,w23,w38,w55,w105,w177,w195,w296] z) [w17,w23,w38,w55,w105,w177,w201,w296] (n z [w17,w23,w38,w55,w105,w177,w205,w278] z)) [w17,w23,w38,w55,w105,w177,w205,w292] (n (n z [w17,w23,w38,w55,w105,w177,w205,w296] z) [w17,w23,w38,w55,w105,w177,w205,w304] (n z [w17,w23,w38,w55,w105,w177,w205,w349] z))) [w17,w23,w38,w55,w105,w177,w205,w355] (n (n (n z [w17,w23,w38,w55,w105,w177,w210,w296] z) [w17,w23,w38,w55,w105,w177,w215,w296] (n z [w17,w23,w38,w55,w105,w177,w222,w296] z)) [w17,w23,w38,w55,w105,w177,w238,w296] (n (n z [w17,w23,w38,w55,w105,w177,w251,w296] z) [w17,w23,w38,w55,w105,w177,w261,w296] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7ababb : t7ababb.all (blocked 6 t6) = true := by
  decide +kernel
def t7abab := (n t7ababa [w17,w23,w38,w55,w105,w149,w177,w296] t7ababb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7abab : t7abab.all (blocked 6 t6) = true := by
  simp only [t7abab, ReplayTree.all, n, ht7ababa, ht7ababb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7aba := (n t7abaa [w17,w23,w38,w55,w84,w105,w177,w205] t7abab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7aba : t7aba.all (blocked 6 t6) = true := by
  simp only [t7aba, ReplayTree.all, n, ht7abaa, ht7abab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abbaa := (n (n (n (n (n z [w17,w23,w38,w55,w105,w177,w280,w296] z) [w17,w23,w38,w55,w105,w177,w292] (n z [w17,w23,w38,w55,w105,w177,w296] z)) [w17,w23,w38,w55,w105,w177,w296,w296] (n (n z [w17,w23,w38,w55,w105,w177,w296,w297] z) [w17,w23,w38,w55,w105,w177,w296,w304] (n z [w17,w23,w38,w55,w105,w177,w296,w307] z))) [w17,w23,w38,w55,w105,w177,w296,w313] (n (n (n z [w17,w23,w38,w55,w105,w177,w296,w329] z) [w17,w23,w38,w55,w105,w177,w296,w330] (n z [w17,w23,w38,w55,w105,w177,w296,w349] z)) [w17,w23,w38,w55,w105,w177,w296,w355] (n (n z [w17,w23,w38,w55,w105,w195,w205,w296] z) [w17,w23,w38,w55,w105,w205,w238,w296] (n z [w17,w23,w38,w55,w105,w205,w263,w296] z)))) [w17,w23,w38,w55,w105,w205,w296,w313] (n (n (n (n z [w17,w23,w38,w55,w105,w263,w296] z) [w17,w23,w38,w55,w105,w296,w313] (n z [w17,w23,w38,w55,w121,w134,w177,w205] z)) [w17,w23,w38,w55,w121,w158,w177,w205] (n (n z [w17,w23,w38,w55,w158,w177,w205,w313] z) [w17,w23,w38,w55,w158,w205,w313] (n z [w17,w23,w38,w55,w177,w205,w296,w313] z))) [w17,w23,w38,w55,w177,w296,w313] (n (n (n z [w17,w23,w38,w55,w205,w296,w313] z) [w17,w23,w38,w55,w296,w313] (n z [w17,w23,w38,w56,w73,w105,w177,w205] z)) [w17,w23,w38,w57,w73,w105,w177,w205] (n (n z [w17,w23,w38,w58,w73,w105,w177,w205] z) [w17,w23,w38,w60,w73,w105,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7abbaa : t7abbaa.all (blocked 6 t6) = true := by
  decide +kernel
def t7abbab := (n (n (n (n (n z [w17,w23,w38,w63,w73,w105,w173,w205] z) [w17,w23,w38,w63,w73,w105,w177,w205] (n z [w17,w23,w38,w63,w73,w105,w177,w222] z)) [w17,w23,w38,w63,w73,w105,w195,w205] (n (n z [w17,w23,w38,w63,w73,w105,w205,w238] z) [w17,w23,w38,w63,w73,w105,w205,w263] (n z [w17,w23,w38,w63,w73,w105,w205,w271] z))) [w17,w23,w38,w63,w73,w105,w205,w313] (n (n (n z [w17,w23,w38,w63,w73,w121,w177,w205] z) [w17,w23,w38,w63,w91,w105,w177,w205] (n z [w17,w23,w38,w63,w105,w134,w177,w205] z)) [w17,w23,w38,w63,w105,w158,w177,w205] (n (n z [w17,w23,w38,w63,w105,w166,w177,w205] z) [w17,w23,w38,w63,w105,w177,w205,w296] (n z [w17,w23,w38,w65,w73,w105,w205,w263] z)))) [w17,w23,w38,w65,w105,w158,w177,w205] (n (n (n (n z [w17,w23,w38,w69,w105,w156,w177,w205] z) [w17,w23,w38,w73,w105,w156,w177,w205] (n z [w17,w23,w38,w73,w105,w158,w205,w263] z)) [w17,w23,w38,w73,w105,w173,w205,w260] (n (n z [w17,w23,w38,w73,w105,w177,w205,w260] z) [w17,w23,w38,w73,w105,w205,w260] (n z [w17,w23,w38,w73,w105,w205,w261,w263] z))) [w17,w23,w38,w105,w156,w177,w205] (n (n (n z [w17,w23,w38,w105,w158,w159,w177,w205] z) [w17,w23,w38,w105,w158,w177,w205,w263] (n z [w17,w23,w38,w105,w158,w205,w263] z)) [w17,w23,w39,w55,w73,w105,w177,w205] (n (n z [w17,w23,w40,w55,w73,w105,w177,w205] z) [w17,w23,w41,w55,w73,w105,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7abbab : t7abbab.all (blocked 6 t6) = true := by
  decide +kernel
def t7abba := (n t7abbaa [w17,w23,w38,w63,w69,w105,w177,w205] t7abbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7abba : t7abba.all (blocked 6 t6) = true := by
  simp only [t7abba, ReplayTree.all, n, ht7abbaa, ht7abbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abbba := (n (n (n (n (n z [w17,w23,w46,w55,w73,w105,w177,w205] z) [w17,w23,w47,w55,w73,w105,w205,w238] (n z [w17,w23,w47,w55,w105,w134,w177,w205] z)) [w17,w23,w50,w55,w73,w105,w205,w238] (n (n z [w17,w23,w50,w55,w105,w134,w177,w205] z) [w17,w23,w51,w55,w73,w105,w177,w205] (n z [w17,w23,w53,w55,w73,w105,w177,w205] z))) [w17,w23,w55,w59,w73,w105,w205,w238] (n (n (n z [w17,w23,w55,w59,w105,w134,w177,w205] z) [w17,w23,w55,w63,w73,w105,w205,w238] (n z [w17,w23,w55,w63,w105,w134,w177,w205] z)) [w17,w23,w55,w65,w73,w105,w205,w238] (n (n z [w17,w23,w55,w65,w105,w134,w177,w205] z) [w17,w23,w55,w69,w73,w105,w205,w238] (n z [w17,w23,w55,w69,w105,w131,w177,w205] z)))) [w17,w23,w55,w69,w105,w134,w177,w205] (n (n (n (n z [w17,w23,w55,w69,w105,w177,w205,w238] z) [w17,w23,w55,w69,w105,w205,w238] (n z [w17,w23,w55,w73,w91,w105,w205,w238] z)) [w17,w23,w55,w73,w96,w105,w205,w238] (n (n z [w17,w23,w55,w73,w105,w107,w205,w238] z) [w17,w23,w55,w73,w105,w116,w205,w238] (n z [w17,w23,w55,w73,w105,w121,w205,w238] z))) [w17,w23,w55,w73,w105,w131,w177,w205] (n (n (n z [w17,w23,w55,w73,w105,w134,w173,w205] z) [w17,w23,w55,w73,w105,w134,w177,w205] (n z [w17,w23,w55,w73,w105,w134,w177,w222] z)) [w17,w23,w55,w73,w105,w134,w177,w296] (n (n z [w17,w23,w55,w73,w105,w134,w195,w205] z) [w17,w23,w55,w73,w105,w134,w205,w238] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7abbba : t7abbba.all (blocked 6 t6) = true := by
  decide +kernel
def t7abbbb := (n (n (n (n (n z [w17,w23,w55,w73,w105,w134,w205,w313] z) [w17,w23,w55,w73,w105,w149,w205,w238] (n z [w17,w23,w55,w73,w105,w158,w205,w238] z)) [w17,w23,w55,w73,w105,w159,w205,w238] (n (n z [w17,w23,w55,w73,w105,w173,w205,w234] z) [w17,w23,w55,w73,w105,w173,w205,w238] (n z [w17,w23,w55,w73,w105,w177,w205,w234] z))) [w17,w23,w55,w73,w105,w177,w205,w238] (n (n (n z [w17,w23,w55,w73,w105,w177,w205,w340] z) [w17,w23,w55,w73,w105,w177,w222,w238] (n z [w17,w23,w55,w73,w105,w177,w238,w296] z)) [w17,w23,w55,w73,w105,w195,w205,w238] (n (n z [w17,w23,w55,w73,w105,w201,w205,w238] z) [w17,w23,w55,w73,w105,w205,w210,w238] (n z [w17,w23,w55,w73,w105,w205,w215,w238] z)))) [w17,w23,w55,w73,w105,w205,w222,w238] (n (n (n (n z [w17,w23,w55,w73,w105,w205,w234] z) [w17,w23,w55,w73,w105,w205,w238] (n z [w17,w23,w55,w73,w105,w205,w238,w238] z)) [w17,w23,w55,w73,w105,w205,w238,w246] (n (n z [w17,w23,w55,w73,w105,w205,w238,w248] z) [w17,w23,w55,w73,w105,w205,w238,w251] (n z [w17,w23,w55,w73,w105,w205,w238,w253] z))) [w17,w23,w55,w73,w105,w205,w238,w261] (n (n (n z [w17,w23,w55,w73,w105,w205,w238,w263] z) [w17,w23,w55,w73,w105,w205,w238,w265] (n z [w17,w23,w55,w73,w105,w205,w238,w280] z)) [w17,w23,w55,w73,w105,w205,w238,w296] (n (n z [w17,w23,w55,w73,w105,w205,w238,w313] z) [w17,w23,w55,w73,w105,w205,w238,w329] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7abbbb : t7abbbb.all (blocked 6 t6) = true := by
  decide +kernel
def t7abbb := (n t7abbba [w17,w23,w55,w73,w105,w134,w205,w263] t7abbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7abbb : t7abbb.all (blocked 6 t6) = true := by
  simp only [t7abbb, ReplayTree.all, n, ht7abbba, ht7abbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7abb := (n t7abba [w17,w23,w42,w55,w73,w105,w177,w205] t7abbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7abb : t7abb.all (blocked 6 t6) = true := by
  simp only [t7abb, ReplayTree.all, n, ht7abba, ht7abbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7ab := (n t7aba [w17,w23,w38,w55,w105,w177,w263,w296] t7abb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7ab : t7ab.all (blocked 6 t6) = true := by
  simp only [t7ab, ReplayTree.all, n, ht7aba, ht7abb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7a := (n t7aa [w17,w23,w38,w55,w73,w105,w205,w321] t7ab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7a : t7a.all (blocked 6 t6) = true := by
  simp only [t7a, ReplayTree.all, n, ht7aa, ht7ab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7baaaa := (n (n (n (n (n z [w17,w23,w55,w73,w105,w205,w238,w352] z) [w17,w23,w55,w73,w105,w222,w238] (n z [w17,w23,w55,w73,w121,w134,w177,w205] z)) [w17,w23,w55,w73,w121,w177,w205,w238] (n (n z [w17,w23,w55,w73,w121,w205,w238] z) [w17,w23,w55,w73,w134,w177,w205,w313] (n z [w17,w23,w55,w73,w134,w205,w313] z))) [w17,w23,w55,w73,w177,w205,w238,w313] (n (n (n z [w17,w23,w55,w73,w205,w238,w313] z) [w17,w23,w55,w91,w105,w134,w177,w205] (n z [w17,w23,w55,w91,w105,w177,w205,w238] z)) [w17,w23,w55,w91,w105,w205,w238] (n (n z [w17,w23,w55,w96,w105,w134,w177,w205] z) [w17,w23,w55,w105,w107,w134,w177,w205] (n z [w17,w23,w55,w105,w116,w134,w177,w205] z)))) [w17,w23,w55,w105,w121,w134,w177,w205] (n (n (n (n z [w17,w23,w55,w105,w131,w177,w205] z) [w17,w23,w55,w105,w134,w134,w177,w205] (n z [w17,w23,w55,w105,w134,w140,w177,w205] z)) [w17,w23,w55,w105,w134,w144,w177,w205] (n (n z [w17,w23,w55,w105,w134,w149,w177,w205] z) [w17,w23,w55,w105,w134,w150,w177,w205] (n z [w17,w23,w55,w105,w134,w158,w177,w205] z))) [w17,w23,w55,w105,w134,w159,w177,w205] (n (n (n z [w17,w23,w55,w105,w134,w161,w177,w205] z) [w17,w23,w55,w105,w134,w173,w177,w205] (n z [w17,w23,w55,w105,w134,w173,w205] z)) [w17,w23,w55,w105,w134,w177,w195,w205] (n (n z [w17,w23,w55,w105,w134,w177,w201,w205] z) [w17,w23,w55,w105,w134,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7baaaa : t7baaaa.all (blocked 6 t6) = true := by
  decide +kernel
def t7baaab := (n (n (n (n (n z [w17,w23,w55,w105,w134,w177,w205,w215] z) [w17,w23,w55,w105,w134,w177,w205,w222] (n z [w17,w23,w55,w105,w134,w177,w205,w238] z)) [w17,w23,w55,w105,w134,w177,w205,w251] (n (n z [w17,w23,w55,w105,w134,w177,w205,w261] z) [w17,w23,w55,w105,w134,w177,w205,w263] (n z [w17,w23,w55,w105,w134,w177,w205,w280] z))) [w17,w23,w55,w105,w134,w177,w205,w296] (n (n (n z [w17,w23,w55,w105,w134,w177,w205,w313] z) [w17,w23,w55,w105,w134,w177,w205,w329] (n z [w17,w23,w55,w105,w134,w177,w205,w340] z)) [w17,w23,w55,w105,w134,w177,w205,w349] (n (n z [w17,w23,w55,w105,w134,w177,w222] z) [w17,w23,w55,w105,w134,w177,w296] (n z [w17,w23,w55,w105,w134,w195,w205] z)))) [w17,w23,w55,w105,w134,w205,w238] (n (n (n (n z [w17,w23,w55,w105,w134,w205,w263] z) [w17,w23,w55,w105,w134,w205,w313] (n z [w17,w23,w55,w105,w158,w177,w205,w238] z)) [w17,w23,w55,w105,w158,w205,w238] (n (n z [w17,w23,w55,w105,w177,w205,w238,w296] z) [w17,w23,w55,w105,w177,w238,w296] (n z [w17,w23,w55,w105,w205,w238,w296] z))) [w17,w23,w55,w121,w134,w177,w205] (n (n (n z [w17,w24,w38,w55,w73,w105,w177,w205] z) [w17,w25,w38,w55,w73,w105,w177,w205] (n z [w17,w27,w38,w55,w73,w105,w177,w222] z)) [w17,w27,w38,w55,w73,w121,w177,w205] (n (n z [w17,w28,w38,w55,w73,w105,w177,w222] z) [w17,w28,w38,w55,w73,w121,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7baaab : t7baaab.all (blocked 6 t6) = true := by
  decide +kernel
def t7baaa := (n t7baaaa [w17,w23,w55,w105,w134,w177,w205,w210] t7baaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7baaa : t7baaa.all (blocked 6 t6) = true := by
  simp only [t7baaa, ReplayTree.all, n, ht7baaaa, ht7baaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7baaba := (n (n (n (n (n z [w17,w32,w38,w55,w73,w105,w177,w222] z) [w17,w32,w38,w55,w73,w121,w177,w205] (n z [w17,w35,w38,w55,w73,w105,w177,w205] z)) [w17,w36,w38,w55,w73,w105,w177,w222] (n (n z [w17,w36,w38,w55,w73,w121,w177,w205] z) [w17,w38,w45,w55,w73,w105,w177,w205] (n z [w17,w38,w47,w55,w73,w105,w177,w222] z))) [w17,w38,w47,w55,w73,w121,w177,w205] (n (n (n z [w17,w38,w50,w55,w73,w105,w177,w222] z) [w17,w38,w50,w55,w73,w121,w177,w205] (n z [w17,w38,w55,w59,w73,w105,w177,w222] z)) [w17,w38,w55,w59,w73,w121,w177,w205] (n (n z [w17,w38,w55,w63,w73,w105,w177,w222] z) [w17,w38,w55,w63,w73,w121,w177,w205] (n z [w17,w38,w55,w65,w73,w105,w177,w222] z)))) [w17,w38,w55,w65,w73,w121,w177,w205] (n (n (n (n z [w17,w38,w55,w69,w73,w105,w177,w222] z) [w17,w38,w55,w69,w73,w121,w177,w205] (n z [w17,w38,w55,w69,w94,w105,w177,w205] z)) [w17,w38,w55,w69,w105,w121,w177,w205] (n (n z [w17,w38,w55,w69,w105,w177,w205,w222] z) [w17,w38,w55,w69,w105,w177,w222] (n z [w17,w38,w55,w69,w121,w177,w205] z))) [w17,w38,w55,w73,w91,w105,w177,w222] (n (n (n z [w17,w38,w55,w73,w91,w121,w177,w205] z) [w17,w38,w55,w73,w94,w105,w177,w205] (n z [w17,w38,w55,w73,w96,w105,w177,w222] z)) [w17,w38,w55,w73,w96,w121,w177,w205] (n (n z [w17,w38,w55,w73,w105,w107,w177,w222] z) [w17,w38,w55,w73,w105,w116,w177,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7baaba : t7baaba.all (blocked 6 t6) = true := by
  decide +kernel
def t7baabb := (n (n (n (n (n z [w17,w38,w55,w73,w105,w121,w177,w205] z) [w17,w38,w55,w73,w105,w121,w177,w222] (n z [w17,w38,w55,w73,w105,w121,w177,w296] z)) [w17,w38,w55,w73,w105,w121,w195,w205] (n (n z [w17,w38,w55,w73,w105,w121,w205,w238] z) [w17,w38,w55,w73,w105,w121,w205,w263] (n z [w17,w38,w55,w73,w105,w121,w205,w313] z))) [w17,w38,w55,w73,w105,w134,w177,w222] (n (n (n z [w17,w38,w55,w73,w105,w149,w177,w222] z) [w17,w38,w55,w73,w105,w158,w177,w222] (n z [w17,w38,w55,w73,w105,w159,w177,w222] z)) [w17,w38,w55,w73,w105,w173,w177,w222] (n (n z [w17,w38,w55,w73,w105,w173,w198,w205] z) [w17,w38,w55,w73,w105,w173,w205,w222] (n z [w17,w38,w55,w73,w105,w173,w222] z)))) [w17,w38,w55,w73,w105,w177,w195,w222] (n (n (n (n z [w17,w38,w55,w73,w105,w177,w198,w205] z) [w17,w38,w55,w73,w105,w177,w201,w222] (n z [w17,w38,w55,w73,w105,w177,w205,w222] z)) [w17,w38,w55,w73,w105,w177,w205,w336] (n (n z [w17,w38,w55,w73,w105,w177,w210,w222] z) [w17,w38,w55,w73,w105,w177,w215,w222] (n z [w17,w38,w55,w73,w105,w177,w222] z))) [w17,w38,w55,w73,w105,w177,w222,w222] (n (n (n z [w17,w38,w55,w73,w105,w177,w222,w223] z) [w17,w38,w55,w73,w105,w177,w222,w224] (n z [w17,w38,w55,w73,w105,w177,w222,w238] z)) [w17,w38,w55,w73,w105,w177,w222,w251] (n (n z [w17,w38,w55,w73,w105,w177,w222,w256] z) [w17,w38,w55,w73,w105,w177,w222,w261] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7baabb : t7baabb.all (blocked 6 t6) = true := by
  decide +kernel
def t7baab := (n t7baaba [w17,w38,w55,w73,w105,w121,w173,w205] t7baabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7baab : t7baab.all (blocked 6 t6) = true := by
  simp only [t7baab, ReplayTree.all, n, ht7baaba, ht7baabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7baa := (n t7baaa [w17,w31,w38,w55,w73,w105,w177,w205] t7baab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7baa : t7baa.all (blocked 6 t6) = true := by
  simp only [t7baa, ReplayTree.all, n, ht7baaa, ht7baab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7babaa := (n (n (n (n (n z [w17,w38,w55,w73,w105,w177,w222,w273] z) [w17,w38,w55,w73,w105,w177,w222,w280] (n z [w17,w38,w55,w73,w105,w177,w222,w296] z)) [w17,w38,w55,w73,w105,w177,w222,w307] (n (n z [w17,w38,w55,w73,w105,w177,w222,w313] z) [w17,w38,w55,w73,w105,w177,w222,w329] (n z [w17,w38,w55,w73,w105,w177,w222,w336] z))) [w17,w38,w55,w73,w105,w195,w205,w222] (n (n (n z [w17,w38,w55,w73,w105,w195,w222] z) [w17,w38,w55,w73,w105,w205,w222,w238] (n z [w17,w38,w55,w73,w105,w205,w222,w263] z)) [w17,w38,w55,w73,w105,w205,w222,w313] (n (n z [w17,w38,w55,w73,w105,w222,w238] z) [w17,w38,w55,w73,w105,w222,w263] (n z [w17,w38,w55,w73,w107,w121,w177,w205] z)))) [w17,w38,w55,w73,w116,w121,w177,w205] (n (n (n (n z [w17,w38,w55,w73,w121,w121,w177,w205] z) [w17,w38,w55,w73,w121,w122,w177,w205] (n z [w17,w38,w55,w73,w121,w123,w177,w205] z)) [w17,w38,w55,w73,w121,w134,w177,w205] (n (n z [w17,w38,w55,w73,w121,w149,w177,w205] z) [w17,w38,w55,w73,w121,w154,w177,w205] (n z [w17,w38,w55,w73,w121,w158,w177,w205] z))) [w17,w38,w55,w73,w121,w159,w177,w205] (n (n (n z [w17,w38,w55,w73,w121,w169,w177,w205] z) [w17,w38,w55,w73,w121,w173,w177,w205] (n z [w17,w38,w55,w73,w121,w173,w205] z)) [w17,w38,w55,w73,w121,w177,w195,w205] (n (n z [w17,w38,w55,w73,w121,w177,w201,w205] z) [w17,w38,w55,w73,w121,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7babaa : t7babaa.all (blocked 6 t6) = true := by
  decide +kernel
def t7babab := (n (n (n (n (n z [w17,w38,w55,w73,w121,w177,w205,w215] z) [w17,w38,w55,w73,w121,w177,w205,w222] (n z [w17,w38,w55,w73,w121,w177,w205,w238] z)) [w17,w38,w55,w73,w121,w177,w205,w251] (n (n z [w17,w38,w55,w73,w121,w177,w205,w261] z) [w17,w38,w55,w73,w121,w177,w205,w263] (n z [w17,w38,w55,w73,w121,w177,w205,w280] z))) [w17,w38,w55,w73,w121,w177,w205,w296] (n (n (n z [w17,w38,w55,w73,w121,w177,w205,w313] z) [w17,w38,w55,w73,w121,w177,w205,w324] (n z [w17,w38,w55,w73,w121,w177,w205,w329] z)) [w17,w38,w55,w73,w121,w177,w205,w336] (n (n z [w17,w38,w55,w73,w121,w177,w222] z) [w17,w38,w55,w73,w121,w177,w296] (n z [w17,w38,w55,w73,w121,w195,w205] z)))) [w17,w38,w55,w73,w121,w205,w238] (n (n (n (n z [w17,w38,w55,w73,w121,w205,w263] z) [w17,w38,w55,w73,w121,w205,w313] (n z [w17,w38,w55,w73,w177,w205,w222,w313] z)) [w17,w38,w55,w73,w177,w222,w313] (n (n z [w17,w38,w55,w73,w205,w222,w313] z) [w17,w38,w55,w91,w105,w121,w177,w205] (n z [w17,w38,w55,w91,w105,w177,w205,w222] z))) [w17,w38,w55,w91,w105,w177,w222] (n (n (n z [w17,w38,w55,w91,w121,w177,w205] z) [w17,w38,w55,w105,w121,w134,w177,w205] (n z [w17,w38,w55,w105,w121,w158,w177,w205] z)) [w17,w38,w55,w105,w121,w177,w205,w296] (n (n z [w17,w38,w55,w105,w121,w177,w296] z) [w17,w38,w55,w105,w134,w177,w205,w222] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7babab : t7babab.all (blocked 6 t6) = true := by
  decide +kernel
def t7baba := (n t7babaa [w17,w38,w55,w73,w121,w177,w205,w210] t7babab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7baba : t7baba.all (blocked 6 t6) = true := by
  simp only [t7baba, ReplayTree.all, n, ht7babaa, ht7babab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7babba := (n (n (n (n (n z [w17,w38,w55,w105,w158,w177,w205,w222] z) [w17,w38,w55,w105,w158,w177,w222] (n z [w17,w38,w55,w105,w177,w205,w222,w296] z)) [w17,w38,w55,w105,w177,w222,w296] (n (n z [w17,w38,w55,w121,w134,w177,w205] z) [w17,w38,w55,w121,w158,w177,w205] (n z [w17,w38,w63,w73,w105,w121,w177,w205] z))) [w17,w38,w63,w73,w105,w177,w205,w222] (n (n (n z [w17,w38,w63,w73,w105,w177,w222] z) [w17,w38,w63,w73,w121,w177,w205] (n z [w17,w55,w73,w105,w121,w134,w177,w205] z)) [w17,w55,w73,w105,w177,w205,w222,w238] (n (n z [w17,w55,w73,w105,w177,w222,w238] z) [w17,w55,w73,w105,w205,w222,w238] (n z [w17,w55,w73,w105,w222,w238] z)))) [w17,w55,w73,w121,w134,w177,w205] (n (n (n (n z [w17,w55,w105,w121,w134,w177,w205] z) [w17,w55,w121,w134,w177,w205] (n z [w18,w23,w38,w55,w73,w105,w177,w205] z)) [w19,w23,w38,w55,w73,w105,w177,w205] (n (n z [w20,w23,w38,w55,w73,w105,w177,w205] z) [w21,w23,w38,w55,w73,w105,w177,w205] (n z [w22,w23,w38,w55,w73,w105,w177,w205] z))) [w22,w38,w50,w55,w73,w105,w177,w205] (n (n (n z [w22,w38,w55,w73,w105,w177,w205] z) [w23,w26,w38,w55,w73,w105,w177,w205] (n z [w23,w27,w38,w55,w73,w105,w195,w205] z)) [w23,w27,w38,w55,w91,w105,w177,w205] (n (n z [w23,w27,w38,w63,w73,w105,w177,w205] z) [w23,w28,w38,w55,w73,w105,w195,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7babba : t7babba.all (blocked 6 t6) = true := by
  decide +kernel
def t7babbb := (n (n (n (n (n z [w23,w28,w38,w63,w73,w105,w177,w205] z) [w23,w30,w38,w55,w73,w105,w177,w205] (n z [w23,w32,w38,w55,w73,w105,w195,w205] z)) [w23,w32,w38,w55,w91,w105,w177,w205] (n (n z [w23,w32,w38,w63,w73,w105,w177,w205] z) [w23,w34,w38,w55,w73,w105,w177,w205] (n z [w23,w36,w38,w55,w73,w105,w195,w205] z))) [w23,w36,w38,w55,w91,w105,w177,w205] (n (n (n z [w23,w36,w38,w63,w73,w105,w177,w205] z) [w23,w36,w50,w55,w73,w105,w177,w205] (n z [w23,w38,w43,w55,w73,w105,w177,w205] z)) [w23,w38,w46,w55,w73,w105,w177,w205] (n (n z [w23,w38,w47,w55,w73,w105,w195,w205] z) [w23,w38,w47,w55,w91,w105,w177,w205] (n z [w23,w38,w47,w63,w73,w105,w177,w205] z)))) [w23,w38,w50,w55,w69,w105,w177,w205] (n (n (n (n z [w23,w38,w50,w55,w73,w105,w173,w205] z) [w23,w38,w50,w55,w73,w105,w177,w205] (n z [w23,w38,w50,w55,w73,w105,w177,w222] z)) [w23,w38,w50,w55,w73,w105,w177,w296] (n (n z [w23,w38,w50,w55,w73,w105,w195,w205] z) [w23,w38,w50,w55,w73,w105,w205,w238] (n z [w23,w38,w50,w55,w73,w105,w205,w248] z))) [w23,w38,w50,w55,w73,w105,w205,w263] (n (n (n z [w23,w38,w50,w55,w73,w105,w205,w313] z) [w23,w38,w50,w55,w73,w121,w177,w205] (n z [w23,w38,w50,w55,w73,w177,w205,w313] z)) [w23,w38,w50,w55,w73,w205,w313] (n (n z [w23,w38,w50,w55,w91,w105,w177,w205] z) [w23,w38,w50,w55,w105,w134,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7babbb : t7babbb.all (blocked 6 t6) = true := by
  decide +kernel
def t7babb := (n t7babba [w23,w28,w38,w55,w91,w105,w177,w205] t7babbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7babb : t7babb.all (blocked 6 t6) = true := by
  simp only [t7babb, ReplayTree.all, n, ht7babba, ht7babbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bab := (n t7baba [w17,w38,w55,w105,w134,w177,w222] t7babb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7bab : t7bab.all (blocked 6 t6) = true := by
  simp only [t7bab, ReplayTree.all, n, ht7baba, ht7babb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7ba := (n t7baa [w17,w38,w55,w73,w105,w177,w222,w263] t7bab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7ba : t7ba.all (blocked 6 t6) = true := by
  simp only [t7ba, ReplayTree.all, n, ht7baa, ht7bab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbaaa := (n (n (n (n (n z [w23,w38,w50,w55,w105,w158,w177,w205] z) [w23,w38,w50,w55,w105,w177,w205,w296] (n z [w23,w38,w50,w55,w105,w177,w296] z)) [w23,w38,w50,w63,w73,w105,w177,w205] (n (n z [w23,w38,w55,w59,w73,w105,w195,w205] z) [w23,w38,w55,w59,w91,w105,w177,w205] (n z [w23,w38,w55,w60,w73,w105,w177,w205] z))) [w23,w38,w55,w63,w69,w105,w177,w205] (n (n (n z [w23,w38,w55,w63,w73,w105,w173,w205] z) [w23,w38,w55,w63,w73,w105,w177,w205] (n z [w23,w38,w55,w63,w73,w105,w177,w222] z)) [w23,w38,w55,w63,w73,w105,w177,w296] (n (n z [w23,w38,w55,w63,w73,w105,w195,w205] z) [w23,w38,w55,w63,w73,w105,w205,w238] (n z [w23,w38,w55,w63,w73,w105,w205,w263] z)))) [w23,w38,w55,w63,w73,w105,w205,w271] (n (n (n (n z [w23,w38,w55,w63,w73,w105,w205,w313] z) [w23,w38,w55,w63,w73,w121,w177,w205] (n z [w23,w38,w55,w63,w73,w177,w205,w313] z)) [w23,w38,w55,w63,w73,w205,w313] (n (n z [w23,w38,w55,w63,w91,w105,w177,w205] z) [w23,w38,w55,w63,w105,w134,w177,w205] (n z [w23,w38,w55,w63,w105,w158,w177,w205] z))) [w23,w38,w55,w63,w105,w166,w177,w205] (n (n (n z [w23,w38,w55,w63,w105,w177,w205,w296] z) [w23,w38,w55,w63,w105,w177,w296] (n z [w23,w38,w55,w65,w73,w105,w195,w205] z)) [w23,w38,w55,w65,w91,w105,w177,w205] (n (n z [w23,w38,w55,w68,w73,w105,w177,w205] z) [w23,w38,w55,w69,w73,w105,w195,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7bbaaa : t7bbaaa.all (blocked 6 t6) = true := by
  decide +kernel
def t7bbaab := (n (n (n (n (n z [w23,w38,w55,w69,w91,w105,w177,w205] z) [w23,w38,w55,w69,w105,w177,w195,w205] (n z [w23,w38,w55,w69,w105,w195,w205] z)) [w23,w38,w55,w73,w84,w105,w177,w205] (n (n z [w23,w38,w55,w73,w87,w105,w177,w205] z) [w23,w38,w55,w73,w91,w105,w173,w205] (n z [w23,w38,w55,w73,w91,w105,w177,w205] z))) [w23,w38,w55,w73,w91,w105,w177,w222] (n (n (n z [w23,w38,w55,w73,w91,w105,w177,w296] z) [w23,w38,w55,w73,w91,w105,w195,w205] (n z [w23,w38,w55,w73,w91,w105,w205,w238] z)) [w23,w38,w55,w73,w91,w105,w205,w263] (n (n z [w23,w38,w55,w73,w91,w105,w205,w313] z) [w23,w38,w55,w73,w91,w121,w177,w205] (n z [w23,w38,w55,w73,w91,w177,w205,w313] z)))) [w23,w38,w55,w73,w91,w205,w313] (n (n (n (n z [w23,w38,w55,w73,w96,w105,w195,w205] z) [w23,w38,w55,w73,w105,w107,w195,w205] (n z [w23,w38,w55,w73,w105,w116,w195,w205] z)) [w23,w38,w55,w73,w105,w121,w195,w205] (n (n z [w23,w38,w55,w73,w105,w134,w195,w205] z) [w23,w38,w55,w73,w105,w144,w177,w205] (n z [w23,w38,w55,w73,w105,w149,w195,w205] z))) [w23,w38,w55,w73,w105,w158,w195,w205] (n (n (n z [w23,w38,w55,w73,w105,w159,w195,w205] z) [w23,w38,w55,w73,w105,w166,w177,w205] (n z [w23,w38,w55,w73,w105,w173,w189,w205] z)) [w23,w38,w55,w73,w105,w173,w195,w205] (n (n z [w23,w38,w55,w73,w105,w177,w189,w205] z) [w23,w38,w55,w73,w105,w177,w192,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7bbaab : t7bbaab.all (blocked 6 t6) = true := by
  decide +kernel
def t7bbaa := (n t7bbaaa [w23,w38,w55,w69,w87,w105,w177,w205] t7bbaab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7bbaa : t7bbaa.all (blocked 6 t6) = true := by
  simp only [t7bbaa, ReplayTree.all, n, ht7bbaaa, ht7bbaab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbaba := (n (n (n (n (n z [w23,w38,w55,w73,w105,w177,w195,w222] z) [w23,w38,w55,w73,w105,w177,w195,w296] (n z [w23,w38,w55,w73,w105,w177,w205,w248] z)) [w23,w38,w55,w73,w105,w177,w205,w271] (n (n z [w23,w38,w55,w73,w105,w177,w205,w289] z) [w23,w38,w55,w73,w105,w189,w205] (n z [w23,w38,w55,w73,w105,w192,w205] z))) [w23,w38,w55,w73,w105,w195,w195,w205] (n (n (n z [w23,w38,w55,w73,w105,w195,w201,w205] z) [w23,w38,w55,w73,w105,w195,w203,w205] (n z [w23,w38,w55,w73,w105,w195,w205] z)) [w23,w38,w55,w73,w105,w195,w205,w210] (n (n z [w23,w38,w55,w73,w105,w195,w205,w215] z) [w23,w38,w55,w73,w105,w195,w205,w218] (n z [w23,w38,w55,w73,w105,w195,w205,w222] z)))) [w23,w38,w55,w73,w105,w195,w205,w238] (n (n (n (n z [w23,w38,w55,w73,w105,w195,w205,w248] z) [w23,w38,w55,w73,w105,w195,w205,w251] (n z [w23,w38,w55,w73,w105,w195,w205,w261] z)) [w23,w38,w55,w73,w105,w195,w205,w263] (n (n z [w23,w38,w55,w73,w105,w195,w205,w271] z) [w23,w38,w55,w73,w105,w195,w205,w280] (n z [w23,w38,w55,w73,w105,w195,w205,w289] z))) [w23,w38,w55,w73,w105,w195,w205,w296] (n (n (n z [w23,w38,w55,w73,w105,w195,w205,w313] z) [w23,w38,w55,w73,w105,w195,w205,w321] (n z [w23,w38,w55,w73,w105,w195,w205,w329] z)) [w23,w38,w55,w73,w105,w195,w222] (n (n z [w23,w38,w55,w73,w105,w205,w238,w248] z) [w23,w38,w55,w73,w105,w205,w248] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7bbaba : t7bbaba.all (blocked 6 t6) = true := by
  decide +kernel
def t7bbabb := (n (n (n (n (n z [w23,w38,w55,w73,w105,w205,w271] z) [w23,w38,w55,w73,w121,w177,w195,w205] (n z [w23,w38,w55,w73,w121,w195,w205] z)) [w23,w38,w55,w73,w177,w195,w205,w313] (n (n z [w23,w38,w55,w73,w195,w205,w313] z) [w23,w38,w55,w84,w105,w177,w205] (n z [w23,w38,w55,w87,w105,w177,w205] z))) [w23,w38,w55,w91,w91,w105,w177,w205] (n (n (n z [w23,w38,w55,w91,w96,w105,w177,w205] z) [w23,w38,w55,w91,w99,w105,w177,w205] (n z [w23,w38,w55,w91,w105,w107,w177,w205] z)) [w23,w38,w55,w91,w105,w116,w177,w205] (n (n z [w23,w38,w55,w91,w105,w117,w177,w205] z) [w23,w38,w55,w91,w105,w121,w177,w205] (n z [w23,w38,w55,w91,w105,w134,w177,w205] z)))) [w23,w38,w55,w91,w105,w144,w177,w205] (n (n (n (n z [w23,w38,w55,w91,w105,w149,w177,w205] z) [w23,w38,w55,w91,w105,w158,w177,w205] (n z [w23,w38,w55,w91,w105,w159,w177,w205] z)) [w23,w38,w55,w91,w105,w166,w177,w205] (n (n z [w23,w38,w55,w91,w105,w173,w177,w205] z) [w23,w38,w55,w91,w105,w173,w205] (n z [w23,w38,w55,w91,w105,w177,w195,w205] z))) [w23,w38,w55,w91,w105,w177,w201,w205] (n (n (n z [w23,w38,w55,w91,w105,w177,w205] z) [w23,w38,w55,w91,w105,w177,w205,w210] (n z [w23,w38,w55,w91,w105,w177,w205,w215] z)) [w23,w38,w55,w91,w105,w177,w205,w222] (n (n z [w23,w38,w55,w91,w105,w177,w205,w238] z) [w23,w38,w55,w91,w105,w177,w205,w251] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7bbabb : t7bbabb.all (blocked 6 t6) = true := by
  decide +kernel
def t7bbab := (n t7bbaba [w23,w38,w55,w73,w105,w205,w263,w271] t7bbabb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7bbab : t7bbab.all (blocked 6 t6) = true := by
  simp only [t7bbab, ReplayTree.all, n, ht7bbaba, ht7bbabb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bba := (n t7bbaa [w23,w38,w55,w73,w105,w177,w195,w205] t7bbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7bba : t7bba.all (blocked 6 t6) = true := by
  simp only [t7bba, ReplayTree.all, n, ht7bbaa, ht7bbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbbaa := (n (n (n (n (n z [w23,w38,w55,w91,w105,w177,w205,w263] z) [w23,w38,w55,w91,w105,w177,w205,w280] (n z [w23,w38,w55,w91,w105,w177,w205,w289] z)) [w23,w38,w55,w91,w105,w177,w205,w296] (n (n z [w23,w38,w55,w91,w105,w177,w205,w304] z) [w23,w38,w55,w91,w105,w177,w205,w313] (n z [w23,w38,w55,w91,w105,w177,w205,w329] z))) [w23,w38,w55,w91,w105,w177,w222] (n (n (n z [w23,w38,w55,w91,w105,w177,w296] z) [w23,w38,w55,w91,w105,w195,w205] (n z [w23,w38,w55,w91,w105,w205,w238] z)) [w23,w38,w55,w91,w105,w205,w263] (n (n z [w23,w38,w55,w91,w105,w205,w313] z) [w23,w38,w55,w91,w121,w177,w205] (n z [w23,w38,w55,w105,w134,w144,w177,w205] z)))) [w23,w38,w55,w105,w134,w177,w195,w205] (n (n (n (n z [w23,w38,w55,w105,w134,w195,w205] z) [w23,w38,w55,w105,w144,w177,w205] (n z [w23,w38,w55,w105,w158,w166,w177,w205] z)) [w23,w38,w55,w105,w158,w177,w195,w205] (n (n z [w23,w38,w55,w105,w158,w195,w205] z) [w23,w38,w55,w105,w166,w177,w205] (n z [w23,w38,w55,w105,w177,w195,w205,w296] z))) [w23,w38,w55,w105,w177,w195,w296] (n (n (n z [w23,w38,w55,w105,w195,w205,w296] z) [w23,w38,w59,w63,w73,w105,w177,w205] (n z [w23,w38,w60,w73,w105,w177,w205] z)) [w23,w38,w63,w63,w73,w105,w177,w205] (n (n z [w23,w38,w63,w65,w73,w105,w177,w205] z) [w23,w38,w63,w67,w73,w105,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7bbbaa : t7bbbaa.all (blocked 6 t6) = true := by
  decide +kernel
def t7bbbab := (n (n (n (n (n z [w23,w38,w63,w69,w73,w105,w177,w205] z) [w23,w38,w63,w69,w105,w177,w205] (n z [w23,w38,w63,w73,w91,w105,w177,w205] z)) [w23,w38,w63,w73,w96,w105,w177,w205] (n (n z [w23,w38,w63,w73,w105,w107,w177,w205] z) [w23,w38,w63,w73,w105,w116,w177,w205] (n z [w23,w38,w63,w73,w105,w121,w177,w205] z))) [w23,w38,w63,w73,w105,w134,w177,w205] (n (n (n z [w23,w38,w63,w73,w105,w149,w177,w205] z) [w23,w38,w63,w73,w105,w158,w177,w205] (n z [w23,w38,w63,w73,w105,w159,w177,w205] z)) [w23,w38,w63,w73,w105,w166,w177,w205] (n (n z [w23,w38,w63,w73,w105,w167,w177,w205] z) [w23,w38,w63,w73,w105,w173,w177,w205] (n z [w23,w38,w63,w73,w105,w173,w205] z)))) [w23,w38,w63,w73,w105,w177,w195,w205] (n (n (n (n z [w23,w38,w63,w73,w105,w177,w201,w205] z) [w23,w38,w63,w73,w105,w177,w205] (n z [w23,w38,w63,w73,w105,w177,w205,w210] z)) [w23,w38,w63,w73,w105,w177,w205,w215] (n (n z [w23,w38,w63,w73,w105,w177,w205,w222] z) [w23,w38,w63,w73,w105,w177,w205,w238] (n z [w23,w38,w63,w73,w105,w177,w205,w251] z))) [w23,w38,w63,w73,w105,w177,w205,w261] (n (n (n z [w23,w38,w63,w73,w105,w177,w205,w263] z) [w23,w38,w63,w73,w105,w177,w205,w269] (n z [w23,w38,w63,w73,w105,w177,w205,w271] z)) [w23,w38,w63,w73,w105,w177,w205,w280] (n (n z [w23,w38,w63,w73,w105,w177,w205,w296] z) [w23,w38,w63,w73,w105,w177,w205,w313] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7bbbab : t7bbbab.all (blocked 6 t6) = true := by
  decide +kernel
def t7bbba := (n t7bbbaa [w23,w38,w63,w68,w73,w105,w177,w205] t7bbbab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7bbba : t7bbba.all (blocked 6 t6) = true := by
  simp only [t7bbba, ReplayTree.all, n, ht7bbbaa, ht7bbbab, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbbba := (n (n (n (n (n z [w23,w38,w63,w73,w105,w177,w222] z) [w23,w38,w63,w73,w105,w195,w205] (n z [w23,w38,w63,w73,w105,w205,w238] z)) [w23,w38,w63,w73,w105,w205,w263] (n (n z [w23,w38,w63,w73,w105,w205,w271] z) [w23,w38,w63,w73,w105,w205,w313] (n z [w23,w38,w63,w73,w121,w177,w205] z))) [w23,w38,w63,w91,w105,w177,w205] (n (n (n z [w23,w38,w63,w105,w134,w177,w205] z) [w23,w38,w63,w105,w158,w177,w205] (n z [w23,w38,w63,w105,w166,w177,w205] z)) [w23,w38,w63,w105,w177,w205,w296] (n (n z [w23,w46,w55,w73,w105,w177,w205] z) [w23,w47,w50,w55,w73,w105,w177,w205] (n z [w23,w50,w55,w73,w105,w134,w177,w205] z)))) [w23,w50,w55,w73,w105,w149,w177,w205] (n (n (n (n z [w23,w50,w55,w73,w105,w177,w205,w238] z) [w23,w50,w55,w73,w105,w177,w205,w251] (n z [w23,w50,w55,w73,w105,w205,w238] z)) [w23,w50,w55,w105,w134,w177,w205] (n (n z [w23,w55,w63,w73,w105,w134,w177,w205] z) [w23,w55,w63,w73,w105,w177,w205,w238] (n z [w23,w55,w63,w73,w105,w205,w238] z))) [w23,w55,w63,w105,w134,w177,w205] (n (n (n z [w23,w55,w73,w91,w105,w134,w177,w205] z) [w23,w55,w73,w91,w105,w177,w205,w238] (n z [w23,w55,w73,w91,w105,w205,w238] z)) [w23,w55,w73,w105,w134,w144,w177,w205] (n (n z [w23,w55,w73,w105,w134,w177,w195,w205] z) [w23,w55,w73,w105,w134,w195,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7bbbba : t7bbbba.all (blocked 6 t6) = true := by
  decide +kernel
def t7bbbbb := (n (n (n (n (n z [w23,w55,w73,w105,w177,w205,w238,w248] z) [w23,w55,w73,w105,w195,w205,w238] (n z [w23,w55,w73,w105,w205,w238,w248] z)) [w23,w55,w91,w105,w134,w177,w205] (n (n z [w23,w55,w91,w105,w177,w205,w238] z) [w23,w55,w91,w105,w205,w238] (n z [w23,w55,w105,w134,w144,w177,w205] z))) [w23,w55,w105,w134,w177,w195,w205] (n (n (n z [w23,w55,w105,w134,w195,w205] z) [w38,w50,w55,w73,w105,w121,w177,w205] (n z [w38,w50,w55,w73,w105,w177,w205,w222] z)) [w38,w50,w55,w73,w105,w177,w222] (n (n z [w38,w50,w55,w73,w121,w177,w205] z) [w38,w55,w63,w73,w105,w121,w177,w205] z))) [w38,w55,w63,w73,w105,w177,w205,w222] (n (n (n (n z [w38,w55,w63,w73,w105,w177,w222] z) [w38,w55,w63,w73,w121,w177,w205] (n z [w38,w55,w73,w91,w105,w121,w177,w205] z)) [w38,w55,w73,w91,w121,w177,w205] (n (n z [w38,w55,w73,w105,w177,w195,w205,w222] z) [w38,w55,w73,w105,w177,w195,w222] (n z [w38,w55,w73,w105,w195,w205,w222] z))) [w38,w55,w73,w105,w195,w222] (n (n (n z [w38,w55,w91,w105,w121,w177,w205] z) [w38,w55,w91,w121,w177,w205] (n z [w38,w63,w73,w105,w121,w177,w205] z)) [w38,w63,w73,w105,w177,w205,w222] (n (n z [w38,w63,w73,w105,w177,w222] z) [w38,w63,w73,w121,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7bbbbb : t7bbbbb.all (blocked 6 t6) = true := by
  decide +kernel
def t7bbbb := (n t7bbbba [w23,w55,w73,w105,w177,w195,w205,w238] t7bbbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7bbbb : t7bbbb.all (blocked 6 t6) = true := by
  simp only [t7bbbb, ReplayTree.all, n, ht7bbbba, ht7bbbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bbb := (n t7bbba [w23,w38,w63,w73,w105,w177,w205,w329] t7bbbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7bbb : t7bbb.all (blocked 6 t6) = true := by
  simp only [t7bbb, ReplayTree.all, n, ht7bbba, ht7bbbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7bb := (n t7bba [w23,w38,w55,w91,w105,w177,w205,w261] t7bbb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7bb : t7bb.all (blocked 6 t6) = true := by
  simp only [t7bb, ReplayTree.all, n, ht7bba, ht7bbb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7b := (n t7ba [w23,w38,w50,w55,w105,w144,w177,w205] t7bb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7b : t7b.all (blocked 6 t6) = true := by
  simp only [t7b, ReplayTree.all, n, ht7ba, ht7bb, Bool.true_and, Bool.and_true]
  decide +kernel
def t7 := (n t7a [w17,w23,w55,w73,w105,w205,w238,w340] t7b)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht7 : t7.all (blocked 6 t6) = true := by
  simp only [t7, ReplayTree.all, n, ht7a, ht7b, Bool.true_and, Bool.and_true]
  decide +kernel
lemma s7 : sound 7 t7 := layer_sound s6 ht7
def t8aa := (n (n (n (n (n z [w0,w17,w23,w38,w55,w73,w105,w177,w205] z) [w1,w17,w23,w38,w55,w73,w105,w177,w205] z) [w2,w17,w23,w38,w55,w73,w105,w177,w205] (n z [w3,w17,w23,w38,w55,w73,w105,w177,w205] z)) [w4,w17,w23,w38,w55,w73,w105,w177,w205] (n (n (n z [w5,w17,w23,w38,w55,w73,w105,w177,w205] z) [w6,w17,w23,w38,w55,w73,w105,w177,w205] z) [w7,w17,w23,w38,w55,w73,w105,w177,w205] (n z [w8,w17,w23,w38,w55,w73,w105,w177,w205] z))) [w10,w17,w23,w38,w55,w73,w105,w177,w205] (n (n (n (n z [w12,w17,w23,w38,w55,w73,w105,w177,w205] z) [w13,w17,w23,w38,w55,w73,w105,w177,w205] z) [w13,w23,w38,w55,w73,w105,w177,w205] (n z [w17,w23,w27,w38,w55,w73,w105,w177,w205] z)) [w17,w23,w28,w38,w55,w73,w105,w177,w205] (n (n (n z [w17,w23,w32,w38,w55,w73,w105,w177,w205] z) [w17,w23,w36,w38,w55,w73,w105,w177,w205] z) [w17,w23,w38,w47,w55,w73,w105,w177,w205] (n z [w17,w23,w38,w50,w55,w73,w105,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht8aa : t8aa.all (blocked 7 t7) = true := by
  decide +kernel
def t8ab := (n (n (n (n (n z [w17,w23,w38,w55,w63,w73,w105,w177,w205] z) [w17,w23,w38,w55,w65,w73,w105,w177,w205] z) [w17,w23,w38,w55,w69,w73,w105,w177,w205] (n z [w17,w23,w38,w55,w69,w105,w177,w205] z)) [w17,w23,w38,w55,w73,w91,w105,w177,w205] (n (n (n z [w17,w23,w38,w55,w73,w96,w105,w177,w205] z) [w17,w23,w38,w55,w73,w105,w107,w177,w205] z) [w17,w23,w38,w55,w73,w105,w116,w177,w205] (n z [w17,w23,w38,w55,w73,w105,w121,w177,w205] z))) [w17,w23,w38,w55,w73,w105,w134,w177,w205] (n (n (n (n z [w17,w23,w38,w55,w73,w105,w149,w177,w205] z) [w17,w23,w38,w55,w73,w105,w158,w177,w205] z) [w17,w23,w38,w55,w73,w105,w159,w177,w205] (n z [w17,w23,w38,w55,w73,w105,w173,w177,w205] z)) [w17,w23,w38,w55,w73,w105,w173,w205] (n (n (n z [w17,w23,w38,w55,w73,w105,w177,w195,w205] z) [w17,w23,w38,w55,w73,w105,w177,w201,w205] z) [w17,w23,w38,w55,w73,w105,w177,w205,w210] (n z [w17,w23,w38,w55,w73,w105,w177,w205,w215] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht8ab : t8ab.all (blocked 7 t7) = true := by
  decide +kernel
def t8a := (n t8aa [w17,w23,w38,w55,w59,w73,w105,w177,w205] t8ab)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht8a : t8a.all (blocked 7 t7) = true := by
  simp only [t8a, ReplayTree.all, n, ht8aa, ht8ab, Bool.true_and, Bool.and_true]
  decide +kernel
def t8ba := (n (n (n (n (n z [w17,w23,w38,w55,w73,w105,w177,w205,w238] z) [w17,w23,w38,w55,w73,w105,w177,w205,w251] z) [w17,w23,w38,w55,w73,w105,w177,w205,w261] (n z [w17,w23,w38,w55,w73,w105,w177,w205,w263] z)) [w17,w23,w38,w55,w73,w105,w177,w205,w280] (n (n (n z [w17,w23,w38,w55,w73,w105,w177,w205,w296] z) [w17,w23,w38,w55,w73,w105,w177,w205,w313] z) [w17,w23,w38,w55,w73,w105,w177,w205,w329] (n z [w17,w23,w38,w55,w73,w105,w177,w222] z))) [w17,w23,w38,w55,w73,w105,w177,w296] (n (n (n (n z [w17,w23,w38,w55,w73,w105,w195,w205] z) [w17,w23,w38,w55,w73,w105,w205,w238] z) [w17,w23,w38,w55,w73,w105,w205,w263] (n z [w17,w23,w38,w55,w73,w105,w205,w313] z)) [w17,w23,w38,w55,w73,w121,w177,w205] (n (n (n z [w17,w23,w38,w55,w73,w177,w205,w313] z) [w17,w23,w38,w55,w73,w205,w313] z) [w17,w23,w38,w55,w91,w105,w177,w205] (n z [w17,w23,w38,w55,w105,w134,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht8ba : t8ba.all (blocked 7 t7) = true := by
  decide +kernel
def t8bb := (n (n (n (n (n z [w17,w23,w38,w55,w105,w177,w205,w296] z) [w17,w23,w38,w55,w105,w177,w296] z) [w17,w23,w38,w63,w73,w105,w177,w205] (n z [w17,w23,w55,w73,w105,w134,w177,w205] z)) [w17,w23,w55,w73,w105,w177,w205,w238] (n (n (n z [w17,w23,w55,w73,w105,w205,w238] z) [w17,w23,w55,w105,w134,w177,w205] z) [w17,w38,w55,w73,w105,w121,w177,w205] (n z [w17,w38,w55,w73,w105,w177,w205,w222] z))) [w17,w38,w55,w73,w105,w177,w222] (n (n (n (n z [w17,w38,w55,w73,w121,w177,w205] z) [w23,w38,w50,w55,w73,w105,w177,w205] z) [w23,w38,w55,w63,w73,w105,w177,w205] (n z [w23,w38,w55,w73,w91,w105,w177,w205] z)) [w23,w38,w55,w73,w105,w177,w195,w205] (n (n z [w23,w38,w55,w73,w105,w195,w205] z) [w23,w38,w55,w91,w105,w177,w205] (n z [w23,w38,w63,w73,w105,w177,w205] z))))
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht8bb : t8bb.all (blocked 7 t7) = true := by
  decide +kernel
def t8b := (n t8ba [w17,w23,w38,w55,w105,w158,w177,w205] t8bb)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht8b : t8b.all (blocked 7 t7) = true := by
  simp only [t8b, ReplayTree.all, n, ht8ba, ht8bb, Bool.true_and, Bool.and_true]
  decide +kernel
def t8 := (n t8a [w17,w23,w38,w55,w73,w105,w177,w205,w222] t8b)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht8 : t8.all (blocked 7 t7) = true := by
  simp only [t8, ReplayTree.all, n, ht8a, ht8b, Bool.true_and, Bool.and_true]
  decide +kernel
lemma s8 : sound 8 t8 := layer_sound s7 ht8
def t9 := (n z [w17,w23,w38,w55,w73,w105,w177,w205] z)
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma ht9 : t9.all (blocked 8 t8) = true := by
  decide +kernel
lemma s9 : sound 9 t9 := layer_sound s8 ht9
set_option maxRecDepth 8000 in
set_option maxHeartbeats 4000000 in
lemma initial_cover : inputs.sublists.all (fun l => cuts l != -1 || t9.find (sortedW l)) = true := by
  decide +kernel

lemma no_small (C : Circuit) (hm : Monotone2 C) (hs : C.size ≤ 9)
    (hr : PEqualNP.Represents.Represents A C) : False := by
  obtain ⟨S, hsub, hl⟩ := compress (get_build C hm hr)
  have hl3 : live basicOps goal 9 S := extend_live hs hl
  let l := inputs.filter (fun w => decide (w ∈ S))
  have hlS : l.toFinset = S := by
    ext v
    simp only [l, List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hsub h), h⟩⟩
  have hnd : l.Nodup := inputs_nodup.filter _
  have hr' : live basicOps goal 9 l.toFinset := hlS ▸ hl3
  have hmem : l ∈ inputs.sublists := List.mem_sublists.mpr List.filter_sublist
  have hh := List.all_eq_true.mp initial_cover l hmem
  have hit : t9.find (sortedW l) = true := by simpa [cuts_full hr'] using hh
  have perm := sorted_perm l
  exact s9 _ hit (perm.nodup_iff.mpr hnd) (by simpa only [List.toFinset_eq_of_perm _ _ perm] using hr')

end PEqualNP.Outside.L_meta_23602_aux.Cert

namespace PEqualNP.Outside.L_meta_23602_aux.Helpers

open PEqualNP.CircuitLowerBounds

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

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

lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

end PEqualNP.Outside.L_meta_23602_aux.Helpers

namespace PEqualNP.Outside.L_meta_23602_aux.RepReads

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_23602_aux.Helpers
open PEqualNP.Represents

lemma wiresFrom_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    wiresFrom (gs ++ [g]) x = wiresFrom gs x ++
      [g.op.eval (g.inputs.map fun i => (wiresFrom gs x).getD i false)] := by
  rw [wiresFrom_append]; rfl

lemma getD_snoc (V : List Bool) (e : Bool) (i : ℕ) :
    (V ++ [e]).getD i false = if i = V.length then e else V.getD i false := by
  split_ifs with h
  · subst h; simp
  · rcases Nat.lt_or_gt_of_ne h with h | h
    · exact List.getD_append _ _ _ _ h
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma op_mono (g : Gate) (hop : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (S T : ℕ → Bool) (h : ∀ i, S i = true → T i = true)
    (he : g.op.eval (g.inputs.map S) = true) : g.op.eval (g.inputs.map T) = true := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases hop with hop | hop <;> rw [hop] at he ⊢
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id] at he ⊢
    exact fun i hi => h i (he i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id] at he ⊢
    obtain ⟨i, hi, hv⟩ := he
    exact ⟨i, hi, h i hv⟩

lemma mono (gs : List Gate) (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp))
    (x y : List Bool) (hl : x.length = y.length)
    (h : ∀ i, x.getD i false = true → y.getD i false = true) :
    ∀ i, (wiresFrom gs x).getD i false = true → (wiresFrom gs y).getD i false = true := by
  induction gs using List.reverseRecOn with
  | nil => exact h
  | append_singleton gs g ih =>
    have H := ih fun g' h' => hg g' (List.mem_append_left _ h')
    intro i
    rw [wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc, length_wiresFrom, length_wiresFrom,
      hl]
    split_ifs with hk
    · exact op_mono g (hg g (by simp)) _ _ H
    · exact H i

def inp (N : ℕ) (P : Finset ℕ) : List Bool := List.ofFn fun i : Fin N => decide ((i : ℕ) ∈ P)

lemma inp_getD (N : ℕ) (P : Finset ℕ) (i : ℕ) :
    (inp N P).getD i false = decide (i < N ∧ i ∈ P) := by
  unfold inp
  by_cases h : i < N <;> simp [List.getD_eq_getElem?_getD, h]

lemma oneEach_eq {n m : ℕ} (u : Fin n) (v : Fin m) :
    oneEach u v = inp (n + m) {(u : ℕ), n + (v : ℕ)} := by
  have hu := u.2
  have hv := v.2
  apply List.ext_getElem
  · simp [oneEach, inp]
  · intro i h1 h2
    simp only [oneEach, inp, List.length_append, List.length_ofFn] at h1 h2 ⊢
    by_cases hi : i < n
    · rw [List.getElem_append_left (by simpa using hi)]
      simp only [List.getElem_ofFn, Fin.ext_iff, Finset.mem_insert, Finset.mem_singleton,
        decide_eq_decide]
      omega
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_ofFn, List.length_ofFn, Fin.ext_iff, Finset.mem_insert,
        Finset.mem_singleton, decide_eq_decide]
      omega

def forcedL {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun u => ∃ v, A u v = true ∧ ∃ u', A u' v = false

def forcedR {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun v => ∃ u, A u v = true ∧ ∃ w, A u w = false

end PEqualNP.Outside.L_meta_23602_aux.RepReads

namespace PEqualNP.Outside.L_meta_23602_aux.RepInduced

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_23602_aux.Helpers
open PEqualNP.Represents RepReads

open scoped Classical

section kill
variable (N : ℕ) (Z : Finset ℕ) (gs : List Gate)

def gat (j : ℕ) : Gate := gs.getD j ⟨.and, []⟩

noncomputable def st : ℕ → List Gate × (ℕ → Option ℕ)
  | 0 => ([], fun w => if w < N ∧ w ∉ Z then some w else none)
  | j + 1 =>
    let p := st j
    let g := gat gs j
    if ∃ i ∈ g.inputs, p.2 i = none then
      (p.1, Function.update p.2 (N + j)
        (if g.op = GateOp.and then none else (g.inputs.filterMap p.2).head?))
    else (p.1 ++ [⟨g.op, g.inputs.map fun i => (p.2 i).getD 0⟩],
      Function.update p.2 (N + j) (some (N + p.1.length)))

def Dead (j : ℕ) : Prop := ∃ i ∈ (gat gs j).inputs, (st N Z gs j).2 i = none

lemma st_dead {j : ℕ} (h : Dead N Z gs j) : st N Z gs (j + 1) =
    ((st N Z gs j).1, Function.update (st N Z gs j).2 (N + j)
      (if (gat gs j).op = GateOp.and then none
        else ((gat gs j).inputs.filterMap (st N Z gs j).2).head?)) := by
  rw [st]; exact if_pos h

lemma st_keep {j : ℕ} (h : ¬ Dead N Z gs j) : st N Z gs (j + 1) =
    ((st N Z gs j).1 ++ [⟨(gat gs j).op, (gat gs j).inputs.map fun i =>
      ((st N Z gs j).2 i).getD 0⟩],
      Function.update (st N Z gs j).2 (N + j) (some (N + (st N Z gs j).1.length))) := by
  rw [st]; exact if_neg h

lemma st_ne {j w : ℕ} (h : w ≠ N + j) : (st N Z gs (j + 1)).2 w = (st N Z gs j).2 w := by
  by_cases hd : Dead N Z gs j
  · rw [st_dead N Z gs hd]; exact Function.update_of_ne h _ _
  · rw [st_keep N Z gs hd]; exact Function.update_of_ne h _ _

lemma st_late (j : ℕ) : ∀ w, N + j ≤ w → (st N Z gs j).2 w = none := by
  induction j with
  | zero => intro w h; simp [st, show ¬ w < N by omega]
  | succ j ih => intro w h; rw [st_ne N Z gs (by omega)]; exact ih w (by omega)

lemma st_final {j k w : ℕ} (hjk : j ≤ k) (h : w < N + j) :
    (st N Z gs k).2 w = (st N Z gs j).2 w := by
  induction k, hjk using Nat.le_induction with
  | base => rfl
  | succ k hk ih => rw [st_ne N Z gs (by omega)]; exact ih

lemma st_off {j k w : ℕ} (hjk : j ≤ k) (h : (st N Z gs k).2 w = none) :
    (st N Z gs j).2 w = none := by
  by_cases hw : w < N + j
  · rw [← st_final N Z gs hjk hw]; exact h
  · exact st_late N Z gs j w (by omega)

lemma st_len (j : ℕ) : (st N Z gs j).1.length +
    ((Finset.range j).filter fun i => Dead N Z gs i).card = j := by
  induction j with
  | zero => simp [st]
  | succ j ih =>
    rw [Finset.range_add_one, Finset.filter_insert]
    by_cases hd : Dead N Z gs j
    · rw [if_pos hd, Finset.card_insert_of_notMem (by simp), st_dead N Z gs hd]
      show (st N Z gs j).1.length + _ = _
      omega
    · rw [if_neg hd, st_keep N Z gs hd]
      simp only [List.length_append, List.length_singleton]
      omega

lemma st_lt (j : ℕ) : ∀ w a, (st N Z gs j).2 w = some a → a < N + (st N Z gs j).1.length := by
  induction j with
  | zero =>
    intro w a h
    simp only [st] at h
    split_ifs at h with hw
    · simp only [Option.some.injEq] at h
      simp [st]; omega
  | succ j ih =>
    intro w a h
    by_cases hd : Dead N Z gs j
    · rw [st_dead N Z gs hd] at h ⊢
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self] at h
        split_ifs at h
        have hm := List.mem_of_mem_head? (Option.mem_def.2 h)
        obtain ⟨i, _, hi⟩ := List.mem_filterMap.1 hm
        exact ih i a hi
      · simp only [Function.update_of_ne hw] at h
        exact ih w a h
    · rw [st_keep N Z gs hd] at h ⊢
      simp only [List.length_append, List.length_singleton]
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self, Option.some.injEq] at h
        omega
      · simp only [Function.update_of_ne hw] at h
        have := ih w a h
        omega

variable (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)

include hgs in
lemma gat_ok (j : ℕ) : ((gat gs j).op = GateOp.and ∨ (gat gs j).op = GateOp.or) ∧
    (gat gs j).inputs.length ≤ 2 := by
  by_cases h : j < gs.length
  · have := hgs (gat gs j) (by rw [gat, List.getD_eq_getElem _ _ h]; exact List.getElem_mem h)
    simpa using this
  · rw [gat, List.getD_eq_default _ _ (by omega)]; simp

include hgs in
lemma st_ok (j : ℕ) : ∀ g ∈ (st N Z gs j).1,
    g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction j with
  | zero => simp [st]
  | succ j ih =>
    by_cases hd : Dead N Z gs j
    · rw [st_dead N Z gs hd]; exact ih
    · rw [st_keep N Z gs hd]
      intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact ih g hg
      · rw [List.mem_singleton.1 hg]
        have := gat_ok gs hgs j
        simpa using this

lemma take_succ (j : ℕ) (hj : j < gs.length) : gs.take (j + 1) = gs.take j ++ [gat gs j] := by
  rw [List.take_succ_eq_append_getElem hj, gat, List.getD_eq_getElem _ _ hj]

include hgs in

lemma st_val (P : Finset ℕ) (j : ℕ) (hj : j ≤ gs.length) : ∀ w,
    ((st N Z gs j).2 w = none → (wiresFrom (gs.take j) (inp N (P \ Z))).getD w false = false) ∧
    ∀ a, (st N Z gs j).2 w = some a → (wiresFrom (st N Z gs j).1 (inp N P)).getD a false =
      (wiresFrom (gs.take j) (inp N (P \ Z))).getD w false := by
  induction j with
  | zero =>
    intro w
    simp only [st, List.take_zero, wiresFrom, List.foldl_nil, inp_getD, Finset.mem_sdiff]
    constructor
    · intro h
      split_ifs at h with hw
      simp only [decide_eq_false_iff_not]; tauto
    · intro a h
      split_ifs at h with hw
      simp only [Option.some.injEq] at h
      subst h
      rw [decide_eq_decide]; tauto
  | succ j ih =>
    have H := ih (by omega)
    have hl1 : (wiresFrom (gs.take j) (inp N (P \ Z))).length = N + j := by
      rw [length_wiresFrom, List.length_take]; simp [inp]; omega
    have hl2 : (wiresFrom (st N Z gs j).1 (inp N P)).length = N + (st N Z gs j).1.length := by
      rw [length_wiresFrom]; simp [inp]
    have hok := gat_ok gs hgs j
    rw [take_succ gs j (by omega), wiresFrom_snoc]
    set V := wiresFrom (gs.take j) (inp N (P \ Z)) with hV
    intro w
    rw [getD_snoc, hl1]
    by_cases hd : Dead N Z gs j
    · rw [st_dead N Z gs hd]
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self, if_true]
        obtain ⟨i, hi, hoff⟩ := hd
        have hi0 := (H i).1 hoff
        rcases hok.1 with hop | hop
        · simp only [hop, if_true]
          refine ⟨fun _ => ?_, fun a h => by simp at h⟩
          rw [← Bool.not_eq_true, GateOp.eval, List.all_eq_true]
          intro h
          have := h _ (List.mem_map.2 ⟨i, hi, rfl⟩)
          rw [hi0] at this; simp at this
        · simp only [hop, reduceCtorEq, if_false]
          
          have hlen := hok.2
          constructor
          · intro h
            rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff] at h
            rw [← Bool.not_eq_true, GateOp.eval, List.any_eq_true]
            rintro ⟨b, hb, hb1⟩
            obtain ⟨i', hi', rfl⟩ := List.mem_map.1 hb
            have := (H i').1 (h i' hi')
            rw [this] at hb1; simp at hb1
          · intro a h
            obtain ⟨i', hi', hia⟩ := List.mem_filterMap.1 (List.mem_of_mem_head? (Option.mem_def.2 h))
            rw [(H i').2 a hia, GateOp.eval]
            have hne : i ≠ i' := by rintro rfl; rw [hoff] at hia; simp at hia
            
            have hall : ∀ b ∈ (gat gs j).inputs, b = i ∨ b = i' := by
              intro b hb
              by_contra hn
              push Not at hn
              have h3 : ({i, i', b} : Finset ℕ) ⊆ (gat gs j).inputs.toFinset := by
                intro c hc
                simp only [Finset.mem_insert, Finset.mem_singleton] at hc
                rcases hc with rfl | rfl | rfl <;> simpa
              have := Finset.card_le_card h3
              rw [Finset.card_eq_three.2 ⟨i, i', b, hne, fun e => hn.1 e.symm, fun e => hn.2 e.symm,
                rfl⟩] at this
              have := List.toFinset_card_le (gat gs j).inputs
              omega
            apply Bool.eq_iff_iff.2
            rw [List.any_eq_true]
            constructor
            · intro hv; exact ⟨_, List.mem_map.2 ⟨i', hi', rfl⟩, hv⟩
            · rintro ⟨b, hb, hb1⟩
              obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hb
              rcases hall c hc with rfl | rfl
              · rw [hi0] at hb1; simp at hb1
              · exact hb1
      · simp only [Function.update_of_ne hw, if_neg hw]
        exact H w
    · rw [st_keep N Z gs hd]
      by_cases hw : w = N + j
      · subst hw
        simp only [Function.update_self, if_true]
        refine ⟨fun h => by simp at h, fun a h => ?_⟩
        simp only [Option.some.injEq] at h
        subst h
        rw [wiresFrom_snoc, getD_snoc, hl2, if_pos rfl]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        obtain ⟨b, hb⟩ : ∃ b, (st N Z gs j).2 i = some b := by
          cases h : (st N Z gs j).2 i with
          | none => exact absurd ⟨i, hi, h⟩ hd
          | some b => exact ⟨b, rfl⟩
        simp only [Function.comp_apply, hb, Option.getD_some]
        exact (H i).2 b hb
      · simp only [Function.update_of_ne hw, if_neg hw]
        refine ⟨(H w).1, fun a h => ?_⟩
        have hlt := st_lt N Z gs j w a h
        rw [wiresFrom_snoc, getD_snoc, hl2, if_neg (by omega)]
        exact (H w).2 a h

def Live (o : ℕ) : ℕ → Prop :=
  Relation.ReflTransGen (fun g w => ∃ j < gs.length, g = N + j ∧ w ∈ (gat gs j).inputs) o

lemma live_dep (o : ℕ) (x y : List Bool) (hx : x.length = N) (hy : y.length = N)
    (h : ∀ i, Live N gs o i → x.getD i false = y.getD i false) (j : ℕ) (hj : j ≤ gs.length) :
    ∀ w, Live N gs o w →
      (wiresFrom (gs.take j) x).getD w false = (wiresFrom (gs.take j) y).getD w false := by
  induction j with
  | zero => intro w hw; simpa [wiresFrom] using h w hw
  | succ j ih =>
    intro w hw
    have H := ih (by omega)
    rw [take_succ gs j (by omega), wiresFrom_snoc, wiresFrom_snoc, getD_snoc, getD_snoc,
      length_wiresFrom, length_wiresFrom, hx, hy, List.length_take, Nat.min_eq_left (by omega)]
    split_ifs with hwj
    · congr 1
      apply List.map_congr_left
      intro a ha
      exact H a (hw.tail ⟨j, by omega, hwj, ha⟩)
    · exact H w hw

include hgs in

lemma kill_count (o : ℕ) (Z0 : Finset ℕ) (hZ0 : ∀ i ∈ Z0, i < N ∧ i ∈ Z ∧ Live N gs o i)
    (ho : (st N Z gs gs.length).2 o ≠ none) :
    Z0.card ≤ ((Finset.range gs.length).filter fun i => Dead N Z gs i).card := by
  set k := gs.length with hk
  let K := (Finset.range k).filter fun j => Dead N Z gs j ∧ Live N gs o (N + j)
  let Y := (Finset.range k).filter fun j => (st N Z gs k).2 (N + j) = none ∧ Live N gs o (N + j)
  let Q : Finset (Σ _ : ℕ, ℕ) := K.sigma fun j =>
    (gat gs j).inputs.toFinset.filter fun i => (st N Z gs j).2 i = none
  let W := Z0 ∪ Y.image fun j => N + j
  have hYK : Y ⊆ K := by
    intro j hj
    obtain ⟨hjk, hz, hl⟩ := Finset.mem_filter.1 hj
    refine Finset.mem_filter.2 ⟨hjk, ?_, hl⟩
    by_contra hd
    have hjk' := Finset.mem_range.1 hjk
    rw [st_final N Z gs (show j + 1 ≤ k by omega) (by omega), st_keep N Z gs hd] at hz
    simp at hz
  have hW : W ⊆ Q.image fun q => q.2 := by
    intro w hw
    have hw2 : (st N Z gs k).2 w = none ∧ Live N gs o w := by
      rcases Finset.mem_union.1 hw with h | h
      · obtain ⟨h1, h2, h3⟩ := hZ0 w h
        refine ⟨?_, h3⟩
        rw [st_final N Z gs (Nat.zero_le k) (by omega)]
        simp [st, h2]
      · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 h
        exact (Finset.mem_filter.1 hj).2
    have hne : w ≠ o := fun e => ho (e ▸ hw2.1)
    rcases Relation.ReflTransGen.cases_tail hw2.2 with e | ⟨g, hg, j, hj, rfl, hi⟩
    · exact absurd e hne
    · have hoff := st_off N Z gs (show j ≤ k by omega) hw2.1
      refine Finset.mem_image.2 ⟨⟨j, w⟩, Finset.mem_sigma.2 ⟨?_, ?_⟩, rfl⟩
      · exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hj, ⟨w, hi, hoff⟩, hg⟩
      · exact Finset.mem_filter.2 ⟨List.mem_toFinset.2 hi, hoff⟩
  have hWc : W.card = Z0.card + Y.card := by
    have : Disjoint Z0 (Y.image fun j => N + j) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.1 h2
      have := (hZ0 _ h1).1
      omega
    show (Z0 ∪ Y.image fun j => N + j).card = _
    rw [Finset.card_union_of_disjoint this,
      Finset.card_image_of_injective _ (fun a b h => by simpa using h)]
  have hQ : Q.card ≤ K.card + Y.card := by
    show (K.sigma _).card ≤ _
    rw [Finset.card_sigma]
    calc ∑ j ∈ K, ((gat gs j).inputs.toFinset.filter fun i => (st N Z gs j).2 i = none).card
        ≤ ∑ j ∈ K, (1 + if j ∈ Y then 1 else 0) := by
          apply Finset.sum_le_sum
          intro j hj
          obtain ⟨hjk, hd, hl⟩ := Finset.mem_filter.1 hj
          have hjk' := Finset.mem_range.1 hjk
          have hok := gat_ok gs hgs j
          have hc := List.toFinset_card_le (gat gs j).inputs
          have hf := Finset.card_filter_le (gat gs j).inputs.toFinset
            fun i => (st N Z gs j).2 i = none
          split_ifs with hY
          · omega
          · 
            have hsome : (st N Z gs k).2 (N + j) ≠ none := fun e =>
              hY (Finset.mem_filter.2 ⟨hjk, e, hl⟩)
            rw [st_final N Z gs (show j + 1 ≤ k by omega) (by omega), st_dead N Z gs hd] at hsome
            simp only [Function.update_self] at hsome
            obtain ⟨i, hi, hia⟩ : ∃ i ∈ (gat gs j).inputs, (st N Z gs j).2 i ≠ none := by
              by_contra hn
              push Not at hn
              apply hsome
              split_ifs
              · rfl
              · rw [List.head?_eq_none_iff, List.filterMap_eq_nil_iff]; exact hn
            have hlt : ((gat gs j).inputs.toFinset.filter fun i => (st N Z gs j).2 i = none).card <
                (gat gs j).inputs.toFinset.card :=
              Finset.card_lt_card (Finset.filter_ssubset.2 ⟨i, List.mem_toFinset.2 hi, hia⟩)
            omega
      _ = K.card + Y.card := by
          rw [Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one, Finset.sum_ite_mem,
            Finset.inter_eq_right.2 hYK, Finset.sum_const, smul_eq_mul, mul_one]
  have h1 := Finset.card_le_card hW
  have h2 := Finset.card_image_le (s := Q) (f := fun q => q.2)
  have h3 : K.card ≤ ((Finset.range k).filter fun i => Dead N Z gs i).card :=
    Finset.card_le_card fun j hj => by
      obtain ⟨a, b, _⟩ := Finset.mem_filter.1 hj
      exact Finset.mem_filter.2 ⟨a, b⟩
  omega

include hgs in

lemma kill (o : ℕ) (Z0 : Finset ℕ) (hZ0 : ∀ i ∈ Z0, i < N ∧ i ∈ Z ∧ Live N gs o i)
    (P0 : Finset ℕ) (hP0 : Circuit.eval ⟨gs, o⟩ (inp N (P0 \ Z)) = true) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + Z0.card ≤ gs.length ∧
      ∀ P, D.eval (inp N P) = Circuit.eval ⟨gs, o⟩ (inp N (P \ Z)) := by
  have hv : ∀ P, _ := fun P => st_val N Z gs hgs P gs.length le_rfl o
  simp only [List.take_length] at hv
  have ho : (st N Z gs gs.length).2 o ≠ none := by
    intro e
    have := (hv P0).1 e
    rw [show Circuit.eval ⟨gs, o⟩ (inp N (P0 \ Z)) =
      (wiresFrom gs (inp N (P0 \ Z))).getD o false from rfl, this] at hP0
    exact Bool.noConfusion hP0
  obtain ⟨a, ha⟩ := Option.ne_none_iff_exists'.1 ho
  refine ⟨⟨(st N Z gs gs.length).1, a⟩, st_ok N Z gs hgs _, ?_, fun P => (hv P).2 a ha⟩
  have h1 := kill_count N Z gs hgs o Z0 hZ0 ho
  have h2 := st_len N Z gs gs.length
  show (st N Z gs gs.length).1.length + Z0.card ≤ gs.length
  omega

end kill

lemma induced : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (R : Finset (Fin n)) (K : Finset (Fin m)), (∀ u ∈ R, ∃ v ∈ K, A u v = false) → (∀ v ∈ K, ∃ u ∈ R, A u v = false) → (∃ u ∈ R, ∃ v ∈ K, A u v = true) → PEqualNP.Represents.RepSizeAtMost A s → ∃ s' : ℕ, PEqualNP.Represents.RepSizeAtMost (fun u v => A u v && decide (u ∈ R) && decide (v ∈ K)) s' ∧ s' + ((Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧ ∃ a' : Fin n, A a' b = false)).card + (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin m, A a b' = false)).card) ≤ s + ((R.filter (fun a => ∃ b ∈ K, A a b = true)).card + (K.filter (fun b => ∃ a ∈ R, A a b = true)).card) := by
  intro n m s A R K hR hK ⟨u0, hu0, v0, hv0, h0⟩ ⟨⟨gs, o⟩, hC, hs, hrep⟩
  let BL := R.filter fun a => ∃ b ∈ K, A a b = true
  let BR := K.filter fun b => ∃ a ∈ R, A a b = true
  let Z : Finset ℕ := (Finset.univ.filter fun a : Fin n => a ∉ BL).image (fun a : Fin n => (a : ℕ)) ∪
    (Finset.univ.filter fun b : Fin m => b ∉ BR).image (fun b : Fin m => n + (b : ℕ))
  have hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := hC
  have hop : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := fun g hg => (hC g hg).1
  have hZl : ∀ a : Fin n, (a : ℕ) ∈ Z ↔ a ∉ BL := by
    intro a
    simp only [Z, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨x, hx, e⟩ | ⟨x, _, e⟩)
      · rwa [← Fin.ext e]
      · have := a.2; omega
    · exact fun h => Or.inl ⟨a, h, rfl⟩
  have hZr : ∀ b : Fin m, n + (b : ℕ) ∈ Z ↔ b ∉ BR := by
    intro b
    simp only [Z, Finset.mem_union, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro (⟨x, _, e⟩ | ⟨x, hx, e⟩)
      · have := x.2; omega
      · rwa [← Fin.ext (show (x : ℕ) = b by omega)]
    · exact fun h => Or.inr ⟨b, h, rfl⟩
  have hmono : ∀ P Q : Finset ℕ, P ⊆ Q → Circuit.eval ⟨gs, o⟩ (inp (n + m) P) = true →
      Circuit.eval ⟨gs, o⟩ (inp (n + m) Q) = true := by
    intro P Q hPQ
    refine mono gs hop _ _ (by simp [inp]) (fun i => ?_) _
    rw [inp_getD, inp_getD, decide_eq_true_eq, decide_eq_true_eq]
    exact fun ⟨a, b⟩ => ⟨a, hPQ b⟩
  have hA : ∀ (u : Fin n) (v : Fin m),
      Circuit.eval ⟨gs, o⟩ (inp (n + m) {(u : ℕ), n + (v : ℕ)}) = A u v := by
    intro u v; rw [← oneEach_eq]; exact hrep u v
  have hoff : ∀ P w, ¬ Live (n + m) gs o w →
      Circuit.eval ⟨gs, o⟩ (inp (n + m) P) = Circuit.eval ⟨gs, o⟩ (inp (n + m) (P.erase w)) := by
    intro P w hw
    have := live_dep (n + m) gs o (inp (n + m) P) (inp (n + m) (P.erase w)) (by simp [inp])
      (by simp [inp]) (fun i hi => by
        rw [inp_getD, inp_getD, decide_eq_decide, Finset.mem_erase]
        have : i ≠ w := fun e => hw (e ▸ hi)
        tauto) gs.length le_rfl o Relation.ReflTransGen.refl
    rw [List.take_length] at this
    exact this
  have hL : ∀ u ∈ forcedL A, Live (n + m) gs o (u : ℕ) := by
    intro u hu
    obtain ⟨v, h1, u', h2⟩ := (Finset.mem_filter.1 hu).2
    by_contra hw
    have e := hoff {(u : ℕ), n + (v : ℕ)} u hw
    rw [hA, h1] at e
    have := hmono _ {(u' : ℕ), n + (v : ℕ)} (fun i hi => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto) e.symm
    rw [hA, h2] at this
    exact Bool.noConfusion this
  have hRr : ∀ v ∈ forcedR A, Live (n + m) gs o (n + (v : ℕ)) := by
    intro v hv
    obtain ⟨u, h1, w, h2⟩ := (Finset.mem_filter.1 hv).2
    by_contra hw
    have e := hoff {(u : ℕ), n + (v : ℕ)} (n + v) hw
    rw [hA, h1] at e
    have := hmono _ {(u : ℕ), n + (w : ℕ)} (fun i hi => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto) e.symm
    rw [hA, h2] at this
    exact Bool.noConfusion this
  have hBL : BL ⊆ forcedL A := by
    intro a ha
    obtain ⟨_, b, hb, hab⟩ := Finset.mem_filter.1 ha
    obtain ⟨a', _, ha'⟩ := hK b hb
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, b, hab, a', ha'⟩
  have hBR : BR ⊆ forcedR A := by
    intro b hb
    obtain ⟨_, a, ha, hab⟩ := Finset.mem_filter.1 hb
    obtain ⟨b', _, hb'⟩ := hR a ha
    exact Finset.mem_filter.2 ⟨Finset.mem_univ _, a, hab, b', hb'⟩
  let Z0 : Finset ℕ := (forcedL A \ BL).image (fun a : Fin n => (a : ℕ)) ∪
    (forcedR A \ BR).image (fun b : Fin m => n + (b : ℕ))
  have hZ0 : ∀ i ∈ Z0, i < n + m ∧ i ∈ Z ∧ Live (n + m) gs o i := by
    intro i hi
    rcases Finset.mem_union.1 hi with hi | hi
    · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 ha
      exact ⟨by have := a.2; omega, (hZl a).2 h2, hL a h1⟩
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.1 hi
      obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hb
      exact ⟨by have := b.2; omega, (hZr b).2 h2, hRr b h1⟩
  have hZ0c : Z0.card = (forcedL A \ BL).card + (forcedR A \ BR).card := by
    have hdis : Disjoint ((forcedL A \ BL).image (fun a : Fin n => (a : ℕ)))
        ((forcedR A \ BR).image (fun b : Fin m => n + (b : ℕ))) := by
      rw [Finset.disjoint_left]
      intro i h1 h2
      obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 h1
      obtain ⟨v, _, hv⟩ := Finset.mem_image.1 h2
      have := u.2
      omega
    show (_ ∪ _ : Finset ℕ).card = _
    rw [Finset.card_union_of_disjoint hdis,
      Finset.card_image_of_injective _ (fun a b h => Fin.ext h),
      Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using h))]
  
  have hval : ∀ (u : Fin n) (v : Fin m),
      Circuit.eval ⟨gs, o⟩ (inp (n + m) (({(u : ℕ), n + (v : ℕ)} : Finset ℕ) \ Z)) =
        (A u v && decide (u ∈ R) && decide (v ∈ K)) := by
    intro u v
    by_cases hu : u ∈ BL
    · by_cases hv : v ∈ BR
      · have hu' := (Finset.mem_filter.1 hu).1
        have hv' := (Finset.mem_filter.1 hv).1
        rw [show ({(u : ℕ), n + (v : ℕ)} : Finset ℕ) \ Z = {(u : ℕ), n + (v : ℕ)} from by
          rw [Finset.sdiff_eq_self_iff_disjoint, Finset.disjoint_left]
          intro i hi
          rcases Finset.mem_insert.1 hi with rfl | hi
          · rw [hZl]; exact fun h => h hu
          · rw [Finset.mem_singleton.1 hi, hZr]; exact fun h => h hv, hA]
        simp [hu', hv']
      · 
        have hu' := (Finset.mem_filter.1 hu).1
        obtain ⟨b, hb, hab⟩ := hR u hu'
        have e1 : (A u v && decide (u ∈ R) && decide (v ∈ K)) = false := by
          by_contra hne
          simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hne
          exact hv (Finset.mem_filter.2 ⟨hne.2, u, hne.1.2, hne.1.1⟩)
        rw [e1]
        by_contra hne
        rw [Bool.not_eq_false] at hne
        have := hmono _ {(u : ℕ), n + (b : ℕ)} (fun i hi => by
          obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hi
          rcases Finset.mem_insert.1 h1 with rfl | h1
          · simp
          · rw [Finset.mem_singleton.1 h1] at h2; exact absurd ((hZr v).2 hv) h2) hne
        rw [hA, hab] at this
        exact Bool.noConfusion this
    · 
      have e1 : (A u v && decide (u ∈ R) && decide (v ∈ K)) = false := by
        by_contra hne
        simp only [Bool.not_eq_false, Bool.and_eq_true, decide_eq_true_eq] at hne
        exact hu (Finset.mem_filter.2 ⟨hne.1.2, v, hne.2, hne.1.1⟩)
      rw [e1]
      by_contra hne
      rw [Bool.not_eq_false] at hne
      obtain ⟨b, hb, a, hab⟩ : ∃ b : Fin m, (n + (v : ℕ) ∉ Z → b = v) ∧ ∃ a : Fin n, A a b = false := by
        by_cases hv : v ∈ BR
        · obtain ⟨a, _, ha⟩ := hK v (Finset.mem_filter.1 hv).1
          exact ⟨v, fun _ => rfl, a, ha⟩
        · obtain ⟨a, _, ha⟩ := hK v0 hv0
          exact ⟨v0, fun h => absurd ((hZr v).2 hv) h, a, ha⟩
      have := hmono _ {(a : ℕ), n + (b : ℕ)} (fun i hi => by
        obtain ⟨h1, h2⟩ := Finset.mem_sdiff.1 hi
        rcases Finset.mem_insert.1 h1 with rfl | h1
        · exact absurd ((hZl u).2 hu) h2
        · rw [Finset.mem_singleton.1 h1] at h2 ⊢
          rw [hb h2]; simp) hne
      rw [hA, hab] at this
      exact Bool.noConfusion this
  obtain ⟨D, hD1, hD2, hD3⟩ := kill (n + m) Z gs hgs o Z0 hZ0 {(u0 : ℕ), n + (v0 : ℕ)}
    (by rw [hval]; simp [h0, hu0, hv0])
  refine ⟨D.size, ⟨D, hD1, le_rfl, fun u v => ?_⟩, ?_⟩
  · rw [oneEach_eq, hD3, hval]
  · have c1 := Finset.card_sdiff_add_card_eq_card hBL
    have c2 := Finset.card_sdiff_add_card_eq_card hBR
    have hs' : gs.length ≤ s := hs
    have e1 : (Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧
      ∃ a' : Fin n, A a' b = false)).card = (forcedL A).card := by unfold forcedL; congr
    have e2 : (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧
      ∃ b' : Fin m, A a b' = false)).card = (forcedR A).card := by unfold forcedR; congr
    have e3 : (R.filter (fun a => ∃ b ∈ K, A a b = true)).card = BL.card := by congr
    have e4 : (K.filter (fun b => ∃ a ∈ R, A a b = true)).card = BR.card := by congr
    rw [e1, e2]
    try rw [e3, e4]
    omega

end PEqualNP.Outside.L_meta_23602_aux.RepInduced

namespace PEqualNP.Outside.L_meta_23602_aux.OneNot

open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_23602_aux.Helpers

lemma helper4_getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

lemma helper4_getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

lemma on1_wiresFrom_cons (g : Gate) (gs : List Gate) (w : List Bool) :
    wiresFrom (g :: gs) w =
      wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl

def on1_relabel (r : ℕ → ℕ) (g : Gate) : Gate := { op := g.op, inputs := g.inputs.map r }

lemma on1_relabel_sim_all (r : ℕ → ℕ) (gs : List Gate) : ∀ (v w : List Bool),
    (∀ i, v.getD (r i) false = w.getD i false) →
    (∀ i < w.length, r i < v.length ∨ v.length + gs.length ≤ r i) →
    (∀ k < gs.length, r (w.length + k) = v.length + k) →
    (∀ i, w.length + gs.length ≤ i → v.length + gs.length ≤ r i) →
    ∀ i, (wiresFrom (gs.map (on1_relabel r)) v).getD (r i) false
      = (wiresFrom gs w).getD i false := by
  induction gs with
  | nil => intro v w h1 _ _ _ i; exact h1 i
  | cons g gs ih =>
    intro v w h1 h2 h3 h4
    simp only [List.length_cons] at h2 h3 h4
    have hval : (on1_relabel r g).op.eval
          ((on1_relabel r g).inputs.map fun i => v.getD i false)
        = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      simp only [on1_relabel, List.map_map]
      congr 1
      apply List.map_congr_left
      intro j _
      exact h1 j
    have hr0 : r w.length = v.length := by simpa using h3 0 (by omega)
    have hne : ∀ i, i ≠ w.length → r i ≠ v.length := by
      intro i hi
      by_cases hlt : i < w.length
      · rcases h2 i hlt with h | h <;> omega
      · by_cases hk : i < w.length + (gs.length + 1)
        · have := h3 (i - w.length) (by omega)
          rw [show w.length + (i - w.length) = i by omega] at this
          omega
        · have := h4 i (by omega); omega
    rw [List.map_cons, on1_wiresFrom_cons, on1_wiresFrom_cons, hval]
    apply ih
    · intro i
      by_cases hi : i = w.length
      · subst hi
        rw [hr0, helper4_getD_snoc_eq, helper4_getD_snoc_eq]
      · rw [helper4_getD_snoc_ne _ _ _ _ (hne i hi), helper4_getD_snoc_ne _ _ _ _ hi]
        exact h1 i
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      by_cases hlt : i < w.length
      · rcases h2 i hlt with h | h
        · left; omega
        · right; omega
      · left; have : i = w.length := by omega
        subst this; omega
    · intro k hk
      simp only [List.length_append, List.length_singleton]
      have := h3 (k + 1) (by omega)
      rw [show w.length + 1 + k = w.length + (k + 1) by omega, this]; omega
    · intro i hi
      simp only [List.length_append, List.length_singleton] at hi ⊢
      have := h4 i (by omega); omega

lemma on1_relabel_sim (r : ℕ → ℕ) (gs : List Gate) (v w : List Bool)
    (h1 : ∀ i < w.length, v.getD (r i) false = w.getD i false)
    (h2 : ∀ i < w.length, r i < v.length ∨ v.length + gs.length ≤ r i)
    (h3 : ∀ k < gs.length, r (w.length + k) = v.length + k)
    (h4 : ∀ i, w.length + gs.length ≤ i → v.length + gs.length ≤ r i) (i : ℕ) :
    (wiresFrom (gs.map (on1_relabel r)) v).getD (r i) false
      = (wiresFrom gs w).getD i false := by
  apply on1_relabel_sim_all r gs v w _ h2 h3 h4
  intro j
  by_cases hj : j < w.length
  · exact h1 j hj
  · have hge : v.length ≤ r j := by
      by_cases hk : j < w.length + gs.length
      · have := h3 (j - w.length) (by omega)
        rw [show w.length + (j - w.length) = j by omega] at this
        omega
      · have := h4 j (by omega); omega
    rw [List.getD_eq_default _ _ hge, List.getD_eq_default _ _ (by omega)]

end PEqualNP.Outside.L_meta_23602_aux.OneNot

namespace PEqualNP.Outside.L_meta_23602_aux.Bridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_23602_aux.Helpers
open PEqualNP.Outside.L_meta_23602_aux.OneNot PEqualNP.Represents
def truncateWire (n k gates i : ℕ) : ℕ :=
  if i < n then i else if i < n + k then n + gates else i - k

def truncateCircuit (n k : ℕ) (C : Circuit) : Circuit :=
  ⟨C.gates.map (on1_relabel (truncateWire n k C.gates.length)),
    truncateWire n k C.gates.length C.output⟩

lemma truncate_eval (n k : ℕ) (C : Circuit) (x : List Bool) (hx : x.length = n) :
    (truncateCircuit n k C).eval x = C.eval (x ++ List.replicate k false) := by
  change (wiresFrom (C.gates.map (on1_relabel (truncateWire n k C.gates.length))) x).getD
    (truncateWire n k C.gates.length C.output) false = _
  apply on1_relabel_sim
  · intro i hi
    simp only [List.length_append, List.length_replicate, hx] at hi
    by_cases hn : i < n
    · rw [truncateWire, if_pos hn, List.getD_append _ _ _ _ (by omega)]
    · rw [truncateWire, if_neg hn, if_pos hi,
        List.getD_eq_default _ _ (by omega), List.getD_append_right _ _ _ _ (by omega)]
      simp [List.getD_eq_getElem?_getD]
  · intro i hi
    simp only [List.length_append, List.length_replicate, hx] at hi ⊢
    by_cases hn : i < n
    · left; simpa [truncateWire, hn] using hn
    · right; simp [truncateWire, hn, hi]
  · intro j hj
    simp only [List.length_append, List.length_replicate, hx]
    simp only [truncateWire, if_neg (show ¬ n + k + j < n by omega),
      if_neg (show ¬ n + k + j < n + k by omega)]
    omega
  · intro i hi
    simp only [List.length_append, List.length_replicate, hx] at hi ⊢
    simp only [truncateWire, if_neg (show ¬ i < n by omega),
      if_neg (show ¬ i < n + k by omega)]
    omega

lemma truncate_monotone (n k : ℕ) (C : Circuit) (h : Monotone2 C) :
    Monotone2 (truncateCircuit n k C) := by
  intro g hg
  obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
  have h' := h g' hg'
  simpa [on1_relabel] using h'

lemma truncate_size (n k : ℕ) (C : Circuit) :
    (truncateCircuit n k C).size = C.size := by
  simp [truncateCircuit, Circuit.size]

lemma oneEach46 (u v : Fin 4) :
    oneEach u (⟨v.val, by omega⟩ : Fin 6) = oneEach u v ++ [false, false] := by
  revert u v
  decide

lemma truncate_rep46 {A : Fin 4 → Fin 6 → Bool} {s : ℕ}
    (h : RepSizeAtMost A s) :
    RepSizeAtMost (fun (u v : Fin 4) => A u ⟨v.val, by omega⟩) s := by
  obtain ⟨C, hC, hs, hA⟩ := h
  refine ⟨truncateCircuit 8 2 C, truncate_monotone 8 2 C hC, ?_, ?_⟩
  · simpa [truncate_size] using hs
  · intro u v
    rw [truncate_eval 8 2 C _ (by simp [oneEach])]
    simpa [oneEach46] using hA u ⟨v.val, by omega⟩

def swapWire01 (i : ℕ) : ℕ := if i = 0 then 1 else if i = 1 then 0 else i

def swapCircuit01 (C : Circuit) : Circuit :=
  ⟨C.gates.map (on1_relabel swapWire01), swapWire01 C.output⟩

lemma swap_rep44 {A : Fin 4 → Fin 4 → Bool} {s : ℕ}
    (h : RepSizeAtMost A s) :
    RepSizeAtMost (fun (u v : Fin 4) => A (Equiv.swap 0 1 u) v) s := by
  obtain ⟨C, hC, hs, hA⟩ := h
  refine ⟨swapCircuit01 C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g', hg', rfl⟩ := List.mem_map.mp hg
    simpa [on1_relabel] using hC g' hg'
  · simpa [swapCircuit01, Circuit.size] using hs
  · intro u v
    have hinit : ∀ (a b : Fin 4) (i : Fin 8),
        (oneEach a b).getD (swapWire01 i) false =
          (oneEach (Equiv.swap 0 1 a) b).getD i false := by decide
    calc
      (swapCircuit01 C).eval (oneEach u v) = C.eval (oneEach (Equiv.swap 0 1 u) v) := by
        apply on1_relabel_sim
        · intro i hi
          exact hinit u v ⟨i, by simpa [oneEach] using hi⟩
        · intro i hi
          left
          simp only [oneEach, List.length_append, List.length_ofFn] at hi ⊢
          unfold swapWire01
          split_ifs <;> omega
        · intro j hj
          simp only [oneEach, List.length_append, List.length_ofFn]
          simp [swapWire01, show 8 + j ≠ 1 by omega]
        · intro i hi
          simp only [oneEach, List.length_append, List.length_ofFn] at hi ⊢
          simp only [swapWire01, if_neg (show i ≠ 0 by omega),
            if_neg (show i ≠ 1 by omega)]
          exact hi
      _ = A (Equiv.swap 0 1 u) v := hA _ _

lemma mask46_to4732 {s : ℕ}
    (h : RepSizeAtMost (fun (u : Fin 4) (v : Fin 6) =>
      (271111 : ℕ).testBit (6 * u.val + v.val)) s) :
    RepSizeAtMost (fun (u : Fin 4) (v : Fin 4) =>
      (4732 : ℕ).testBit (4 * u.val + v.val)) s := by
  have h' := swap_rep44 (truncate_rep46 h)
  convert h' using 1
  funext u v
  revert u v
  decide

lemma masked9
    (h : PEqualNP.Represents.RepSizeAtMost
      (fun (u : Fin 4) (v : Fin 6) => (271159 : ℕ).testBit (6 * u.val + v.val)) 11) :
    PEqualNP.Represents.RepSizeAtMost
      (fun (u : Fin 4) (v : Fin 6) => (271111 : ℕ).testBit (6 * u.val + v.val)) 9 := by
  let A : Fin 4 → Fin 6 → Bool :=
    fun u v => (271159 : ℕ).testBit (6 * u.val + v.val)
  let R : Finset (Fin 4) := Finset.univ
  let K : Finset (Fin 6) := {0, 1, 2, 3}
  obtain ⟨s, hs, hb⟩ := PEqualNP.Outside.L_meta_23602_aux.RepInduced.induced 4 6 11 A R K
    (by decide +kernel) (by decide +kernel) (by decide +kernel) h
  have hb' : s + 10 ≤ 11 + 8 := by
    convert hb using 1 <;> congr 1
  have hs9 : s ≤ 9 := by omega
  have heq : (fun u v => A u v && decide (u ∈ R) && decide (v ∈ K)) =
      (fun (u : Fin 4) (v : Fin 6) => (271111 : ℕ).testBit (6 * u.val + v.val)) := by
    decide +kernel
  rw [heq] at hs
  obtain ⟨C, hm, hc, hr⟩ := hs
  exact ⟨C, hm, hc.trans hs9, hr⟩

lemma target_to_core
    (h : PEqualNP.Represents.RepSizeAtMost
      (fun (u : Fin 4) (v : Fin 6) => (271159 : ℕ).testBit (6 * u.val + v.val)) 11) :
    PEqualNP.Represents.RepSizeAtMost
      (fun (u : Fin 4) (v : Fin 4) => (4732 : ℕ).testBit (4 * u.val + v.val)) 9 :=
  mask46_to4732 (masked9 h)

end PEqualNP.Outside.L_meta_23602_aux.Bridge

theorem PEqualNP.Outside.L_meta_23602 :
    ¬ PEqualNP.Represents.RepSizeAtMost
      (fun (u : Fin 4) (v : Fin 6) => (271159 : ℕ).testBit (6 * u.val + v.val)) 11 := by
  intro h
  obtain ⟨C, hm, hs, hr⟩ := PEqualNP.Outside.L_meta_23602_aux.Bridge.target_to_core h
  exact PEqualNP.Outside.L_meta_23602_aux.Cert.no_small C hm hs hr
