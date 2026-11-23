import Mathlib.Tactic.ByContra
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Tauto
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_670_aux.SignedCheck

-- Live-wire compilation and completeness adapted from Lewis Watson, L-meta-515.
namespace Live

variable {α : Type} [DecidableEq α]

-- The ordinary circuit may consult any earlier result.
def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k+1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

-- A live set contains just the wires actually read by the remaining computation.
def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k+1, s => live ops goal k s ∨
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
    (h : live ops goal k s) : s.card ≤ k+1 := by
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

-- Any pair of rows which the output separates must stay separated at each cut.
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

end Live

namespace Live
variable {α : Type} [DecidableEq α] {ops : α → α → Finset α} {goal : α}

theorem first_live {k : ℕ} {s : Finset α} (h : live ops goal (k+1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,tail⟩
      · exact .inl done
      · exact .inr ⟨a,ha,b,hb,hab,z,hz,hn,r,hs,Or.inl tail⟩
    · exact .inr step

end Live

namespace Check

abbrev W := BitVec 128
def neg (x : W) : W := ~~~x
def both (x y : W) : W := x &&& y
def canon (x : W) : W := if x.getLsbD 127 then neg x else x
def ops (x y : W) : List W :=
  [canon (both x y), canon (both x (neg y)), canon (both (neg x) y), canon (both (neg x) (neg y))]
def sep (x : W) := (x ^^^ (x >>> 64)).setWidth 64
def cuts (ws : List W) : BitVec 64 := ws.foldr (fun w v => sep w ||| v) 0
def goal : W := canon (((-1 : BitVec 64) ++ (0 : BitVec 64)))
def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a,rest) :: (singles rest).map (fun (b,bs) => (b,a :: bs))
def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b,bs) => (a,b,bs)) ++
      (pairs rest).map (fun (b,c,bs) => (b,c,a :: bs))

def advance (k : ℕ) (next : List W → Bool) (a b : W) (rest : List W) : Bool :=
  let ds := ops a b
  let base := cuts rest
  let attempt := fun (kept : List W) (covered : BitVec 64) =>
    if kept.length + 1 ≤ k+1 then
      ds.any (fun z => !(a :: b :: rest).contains z && (covered ||| sep z == -1) && next (z :: kept))
    else false
  attempt rest base || attempt (a :: rest) (sep a ||| base) ||
    attempt (b :: rest) (sep b ||| base) || attempt (a :: b :: rest) (sep a ||| (sep b ||| base))

def search : ℕ → List W → Bool
  | 0, ws => ws == [goal]
  | k+1, ws => ws == [goal] || (pairs ws).any (fun (a,b,rest) => advance k (search k) a b rest)

def rawInputs : List W :=
  [0x34de44f28e8221e5345e4472868000e0, 0x8aa21910137e561f8aa01800017e121f, 0x30ce7f8248568ea0104e7f8008160e0, 0x20310a23c73f8f3320210803873e8f03, 0xcbc0b3ccf849f05ccb80b38c7841701c, 0xc013c0f0071ff9f000118090051ff1f, 0xf001c00fff81ffe06001000ffe81ede0, 0xfffe000ffffe0000fefa0006ff2e0000, 0xfffffff0000000009fdee7f000000000]

def inputs := rawInputs.map canon

end Check
namespace Check
variable {α : Type}

theorem pick_one {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a,rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a,rest),hm,rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

theorem pick_two {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a,b,rest) ∈ pairs ws ∨ (b,a,rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b,r),hm,rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r,.inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a,r),hm,rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_, (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a,b,r),hm,rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b,a,r),hm,rfl⟩))
end Check

namespace Check
abbrev basicOps (a b : W) := (ops a b).toFinset
def differs (i : Fin 64) (w : W) : Prop :=
  w.getLsbD i.val ≠ w.getLsbD (64+i.val)

theorem neg_differs (i : Fin 64) (w : W) : differs i (neg w) ↔ differs i w := by
  have lo : i.val < 128 := by omega
  have hi : 64+i.val < 128 := by omega
  simp [neg, differs, hi, lo]

theorem canon_differs (i : Fin 64) (w : W) : differs i (canon w) ↔ differs i w := by
  unfold canon
  split <;> simp [neg_differs]

theorem ops_differs (i : Fin 64) (a b : W) (z : W) (hz : z ∈ basicOps a b)
    (hd : differs i z) : differs i a ∨ differs i b := by
  by_contra! h
  have e₁ : a.getLsbD i.val = a.getLsbD (64+i.val) := by simpa [differs] using h.1
  have e₂ : b.getLsbD i.val = b.getLsbD (64+i.val) := by simpa [differs] using h.2
  have lo : i.val < 128 := by omega
  have hi : 64+i.val < 128 := by omega
  simp [basicOps, ops] at hz
  rcases hz with rfl|rfl|rfl|rfl <;>
    rw [canon_differs] at hd <;>
    simp only [both, neg, differs, BitVec.getLsbD_and, BitVec.getLsbD_not, hi, lo, e₁, e₂] at hd <;> simp_all

theorem goal_differs (i : Fin 64) : differs i goal := by
  rw [goal, canon_differs]
  unfold differs
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
  simp [i.isLt, show ¬64 + i.val < 64 by omega]
  exact BitVec.getElem_allOnes _ _

theorem cuts_spec (ws : List W) (i : Fin 64) :
    (cuts ws).getLsbD i.val = true ↔ ∃ w ∈ ws, differs i w := by
  induction ws with
  | nil => simp [cuts]
  | cons a rest ih =>
    change (sep a ||| cuts rest).getLsbD i.val = true ↔ _
    rw [BitVec.getLsbD_or, Bool.or_eq_true, ih]
    simp [sep, i.isLt, differs]

theorem cuts_full {k : ℕ} {ws : List W} (h : Live.live basicOps goal k ws.toFinset) :
    cuts ws = -1 := by
  apply BitVec.eq_of_getElem_eq
  intro j hj
  have hw := Live.live_separates (differs ⟨j,hj⟩) (goal_differs ⟨j,hj⟩) (ops_differs ⟨j,hj⟩) h
  have hbit := (cuts_spec ws ⟨j,hj⟩).mpr (by simpa using hw)
  change (cuts ws)[j] = (BitVec.allOnes 64)[j]
  rw [BitVec.getElem_allOnes]
  simpa only [BitVec.getLsbD_eq_getElem hj] using hbit

theorem ops_swap (a b : W) : basicOps a b = basicOps b a := by
  ext z
  simp [basicOps, ops, both, BitVec.and_comm]
  grind [BitVec.and_comm]

end Check

namespace Check

def keepChoices (a b : W) (r : List W) := [r, a::r, b::r, a::b::r]

theorem advance_has {k : ℕ} {next : List W → Bool} {a b z : W} {r kept : List W}
    (hz : z ∈ basicOps a b) (hk : kept ∈ keepChoices a b r)
    (hf : z ∉ a :: b :: r) (hn : kept.length+1 ≤ k+1) (hc : cuts (z::kept) = -1) (ht : next (z::kept) = true) :
    advance k next a b r = true := by
  have hh : (ops a b).any (fun w => !(a :: b :: r).contains w && (cuts kept ||| sep w == -1) && next (w :: kept)) := by
    apply List.any_eq_true.mpr
    refine ⟨z, by simpa [basicOps] using hz, ?_⟩
    change sep z ||| cuts kept = -1 at hc
    simp [hf, BitVec.or_comm (cuts kept), hc, ht]
  simp [keepChoices] at hk
  rcases hk with rfl|rfl|rfl|rfl <;>
    simp only [advance, hn, ite_true, cuts, List.foldr_cons] at * <;> simp_all

theorem recover_kept {ws r : List W} {a b : W} {needed : Finset W}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simpa [hp.mem_iff] using (hp.mem_iff (a := v))
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a::b::r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a::r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b::r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
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

theorem search_complete (n : ℕ) (ws : List W) (hn : ws.Nodup)
    (h : Live.live basicOps goal n ws.toFinset) : search n ws = true := by
  induction n generalizing ws with
  | zero => simp [search, singleton_list hn h]
  | succ k ih =>
    rcases Live.first_live h with done | ⟨a,ha,b,hb,hab,z,hz,hout,needed,hs,tail⟩
    · simp [search, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : W} (perm : ws.Perm (a::b::r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          advance k (search k) a b r = true := by
        obtain ⟨kept,hk,hnk,hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z::kept).Nodup := List.nodup_cons.mpr ⟨hznew,hnk⟩
        have hl : Live.live basicOps goal k (z::kept).toFinset := by
          simpa [hfin] using tail
        have hfresh : z ∉ a :: b :: r := by
          intro hz
          exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hz))
        apply advance_has hop hk hfresh _ (cuts_full hl) (ih _ hnd hl)
        have hc := Live.live_card hl
        rw [List.toFinset_card_of_nodup hnd] at hc
        exact hc
      simp only [search, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a,b,r), direct, go hp hs hz⟩
      · exact ⟨(b,a,r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

end Check

namespace Check
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
private def possible (w : List W) (z : W) : Bool :=
  z == 0 || z == (-1) || w.any (fun u => z == u || z == ~~~u ||
    w.any (fun v => z == (u &&& v) || z == (u ||| v)))

private def bit (k : Fin 128) (z : W) := z[k.val]

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

private theorem atom {ws : List W} {x : W} (hx : x = 0 ∨ x ∈ ws) :
    possible ws x ∧ possible ws (~~~x) := by
  rcases hx with rfl | hx
  · simp [possible]
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    grind

private theorem pair {ws : List W} {x y : W} (hx : x = 0 ∨ x ∈ ws) (hy : y = 0 ∨ y ∈ ws) :
    possible ws (x &&& y) ∧ possible ws (x ||| y) := by
  rcases hx with rfl | hx
  · simpa [possible] using (show possible ws 0 ∧ possible ws y from ⟨by simp [possible], (atom hy).1⟩)
  rcases hy with rfl | hy
  · simpa [possible] using (show possible ws 0 ∧ possible ws x from ⟨by simp [possible], (atom (.inr hx)).1⟩)
  · simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true]
    constructor
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inl rfl⟩⟩
    · exact .inr ⟨x, hx, .inr ⟨y, hy, .inr rfl⟩⟩

private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

set_option maxRecDepth 20000 in
private theorem gate_table (w ws : List W) (hw : w ⊆ ws) (g : Gate) (hg : legal g) :
    ∃ z, possible ws z ∧ ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  have mem (i : ℕ) : w.getD i 0 = 0 ∨ w.getD i 0 ∈ ws := (read_wire w i).imp_right (fun h => hw h)
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl | rfl
    · exact ⟨-1, by simp [possible], by simp [step, GateOp.eval, bit]; decide +kernel⟩
    · exact ⟨0, by simp [possible], by simp [step, GateOp.eval, bit]⟩
    · exact ⟨-1, by simp [possible], by simp [step, GateOp.eval, bit]; decide +kernel⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl | rfl
      · exact ⟨_, (atom (mem i)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom (mem i)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, (atom (mem i)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl | rfl
        · exact ⟨_, (pair (mem i) (mem j)).1, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (pair (mem i) (mem j)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩
        · exact ⟨_, (atom (mem i)).2, by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bit]⟩


theorem canon_neg (x : W) : canon (~~~x) = canon x := by
  unfold canon neg
  simp only [BitVec.getLsbD_not, BitVec.not_not]
  cases h : x.getLsbD 127 <;> simp [h]

theorem sign (x : W) : x = canon x ∨ x = neg (canon x) := by
  unfold canon neg
  split <;> simp

theorem signed_both {x y a b : W} (hx : x = a ∨ x = neg a) (hy : y = b ∨ y = neg b) :
    canon (x &&& y) ∈ basicOps a b := by
  rcases hx with rfl|rfl <;> rcases hy with rfl|rfl <;> simp [basicOps, ops, both]

set_option maxRecDepth 20000 in
theorem same_both {x y : W} (eq : canon x = canon y) :
    canon (x &&& y) = canon x ∨ canon (x &&& y) = 0 := by
  have signs : x = y ∨ x = ~~~y := by
    rcases sign x with h|h <;> rcases sign y with j|j <;> rw [eq] at h
    · exact .inl (h.trans j.symm)
    · exact .inr (h.trans (by simpa only [neg, BitVec.not_not] using congrArg (fun v : W => ~~~v) j.symm))
    · exact .inr (h.trans (congrArg neg j.symm))
    · exact .inl (h.trans j.symm)
  rcases signs with rfl|rfl
  · exact .inl (by rw [BitVec.and_self])
  · exact .inr (by rw [BitVec.not_and_self]; decide +kernel)


def represents (available : Finset W) (w : List W) :=
  ∀ u ∈ w, canon u = 0 ∨ canon u ∈ available

set_option maxRecDepth 20000 in
theorem classify {available : Finset W} {ws : List W} (hw : represents available ws)
    {z : W} (hz : possible ws z) :
    canon z = 0 ∨ canon z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ canon z ∈ basicOps a b := by
  simp only [possible, Bool.or_eq_true, beq_iff_eq, List.any_eq_true] at hz
  rcases hz with ((h | h) | ⟨x,hx, (h | h) | ⟨y,hy, hh⟩⟩)
  · subst z; left; decide +kernel
  · subst z; left; decide +kernel
  · subst z; exact (hw _ hx).imp_right Or.inl
  · subst z; rw [canon_neg]; exact (hw _ hx).imp_right Or.inl
  · have andCase (u v : W) (hu : canon u = 0 ∨ canon u ∈ available)
        (hv : canon v = 0 ∨ canon v ∈ available) :
        canon (u &&& v) = 0 ∨ canon (u &&& v) ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ canon (u &&& v) ∈ basicOps a b := by
      have zeroOrFull (t : W) (h : canon t = 0) : t = 0 ∨ t = BitVec.allOnes 128 := by
        rcases sign t with h'|h' <;> rw [h] at h'
        · exact .inl h'
        · exact .inr h'
      rcases hu with h | hu
      · rcases zeroOrFull _ h with rfl|rfl
        · left; exact (congrArg canon (BitVec.zero_and (x := v))).trans (by decide +kernel)
        · rw [BitVec.allOnes_and]; exact hv.imp_right Or.inl
      rcases hv with h | hv
      · rcases zeroOrFull _ h with rfl|rfl
        · left; exact (congrArg canon (BitVec.and_zero (x := u))).trans (by decide +kernel)
        · rw [BitVec.and_allOnes]; exact .inr (.inl hu)
      by_cases h : canon u = canon v
      · rcases same_both h with ht|ht
        · exact .inr (.inl (ht ▸ hu))
        · exact .inl ht
      · exact .inr (.inr ⟨_,hu,_,hv,h,signed_both (sign u) (sign v)⟩)
    rcases hh with rfl|rfl
    · exact andCase x y (hw _ hx) (hw _ hy)
    · rw [← canon_neg (x ||| y), BitVec.not_or]
      exact andCase _ _ (by simpa only [canon_neg] using hw _ hx) (by simpa only [canon_neg] using hw _ hy)

def negGate (g : Gate) : Bool :=
  match g.op with
  | .not => true
  | _ => false

def binaries : List Gate → Nat
  | [] => 0
  | g :: gs => if negGate g then binaries gs else binaries gs + 1

set_option maxRecDepth 20000 in
private theorem not_step (w : List W) (g : Gate) (ng : negGate g = true)
    (av : Finset W) (hw : represents av w) :
    ∃ z, (canon z = 0 ∨ canon z ∈ av) ∧
      ∀ k, step (w.map (bit k)) g = (w ++ [z]).map (bit k) := by
  obtain ⟨op, args⟩ := g
  cases op <;> try {contradiction}
  cases args with
  | nil =>
    exact ⟨-1, Or.inl (by decide +kernel), by simp [step, GateOp.eval, bit]; decide +kernel⟩
  | cons i tail =>
    refine ⟨~~~(w.getD i 0), ?_, ?_⟩
    · rw [canon_neg]
      rcases read_wire w i with h|h
      · rw [h]; left; decide +kernel
      · exact hw _ h
    · intro k
      simp only [step, List.map_cons, read_bit]
      simp [GateOp.eval, bit]

set_option maxRecDepth 20000 in
private theorem compile (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List W) (av : Finset W) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false =
      bit k ((-1 : BitVec 64) ++ (0 : BitVec 64))) :
    Live.build basicOps goal (binaries gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out 0 = ((-1 : BitVec 64) ++ (0 : BitVec 64)) := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz|hm
    · exact False.elim ((by decide +kernel : ((-1 : BitVec 64) ++ (0 : BitVec 64)) ≠ (0 : W)) hz)
    · exact (hw _ hm).resolve_left (by decide +kernel)
  | cons g gs ih =>
    by_cases ng : negGate g = true
    · obtain ⟨z,hz,hstep⟩ := not_step w g ng av hw
      rw [binaries, if_pos ng]
      apply ih (fun g' h => hg g' (by simp [h])) (w ++ [z]) av
      · intro u hu
        rcases List.mem_append.mp hu with old|fresh
        · exact hw _ old
        · exact List.mem_singleton.mp fresh ▸ hz
      · intro k; simpa only [List.foldl_cons,hstep] using he k
    rw [binaries, if_neg ng]
    obtain ⟨z,hz,hstep⟩ := gate_table w w (fun _ h => h) g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false =
        bit k ((-1 : BitVec 64) ++ (0 : BitVec 64)) := by
      intro k; simpa only [List.foldl_cons,hstep] using he k
    have appendOK (h : canon z = 0 ∨ canon z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old|fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h|h|⟨a,ha,b,hb,hab,hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr h)) he')
    · refine Or.inr ⟨a,ha,b,hb,hab,canon z,hop,fn (insert (canon z) av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with hu|hu
      · exact (hw _ hu).imp_right (Finset.mem_insert_of_mem ·)
      · simp_all


def graph (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

def assignment (k : Fin 128) (i : Fin 9) := bit k (rawInputs.getD i.val 0)

set_option maxRecDepth 20000 in
theorem full_inputs {s : Finset W} {k : ℕ} (hs : s ⊆ inputs.toFinset)
    (hr : Live.live basicOps goal k s) : s = inputs.toFinset := by
  apply Finset.Subset.antisymm hs
  intro a ha
  let sites : List (Fin 64) := [0, 10, 1, 4, 6, 7, 9, 20, 43]
  have necessary : inputs.all (fun a => sites.any (fun i => inputs.all (fun b =>
      (b.getLsbD i.val == b.getLsbD (64+i.val)) || b == a))) = true := by decide +kernel
  obtain ⟨i,_,hAll⟩ := List.any_eq_true.mp (List.all_eq_true.mp necessary a (List.mem_toFinset.mp ha))
  have hi (b : W) (hb : b ∈ inputs) (hd : differs i b) : b = a := by
    have hrow := List.all_eq_true.mp hAll b hb
    simp only [Bool.or_eq_true, beq_iff_eq] at hrow
    exact hrow.resolve_left hd
  obtain ⟨b,hb,hd⟩ := Live.live_separates (differs i) (goal_differs i) (ops_differs i) hr
  exact hi b (List.mem_toFinset.mp (hs hb)) hd ▸ hb

theorem input_rows (k : Fin 128) : List.ofFn (assignment k) = rawInputs.map (bit k) := by
  rfl

theorem graph_rows (k : Fin 128) : graph (assignment k) =
    bit k ((-1 : BitVec 64) ++ (0 : BitVec 64)) := by
  let x := fun (i : Nat) => rawInputs.getD i 0
  have ht : (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) ||| (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) ||| (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5) =
       ((-1 : BitVec 64) ++ (0 : BitVec 64)) := by decide +kernel
  rw [← ht]
  simp only [bit, graph, assignment, BitVec.getElem_or, BitVec.getElem_and, BitVec.getElem_not]
  rfl


theorem rows_eval (C : Circuit) (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = graph x) (k : Fin 128) :
    (C.gates.foldl step (rawInputs.map (bit k))).getD C.output false =
      bit k ((-1 : BitVec 64) ++ (0 : BitVec 64)) := by
  rw [← input_rows, ← graph_rows]
  exact he (assignment k)

theorem initial_rep : represents inputs.toFinset rawInputs := by
  intro u hu
  right
  exact List.mem_toFinset.mpr (List.mem_map_of_mem hu)

theorem get_build (C : Circuit) (hg : FanInTwo C)
    (he : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = graph x) :
    Live.build basicOps goal (binaries C.gates) inputs.toFinset :=
  compile C.gates C.output hg rawInputs inputs.toFinset initial_rep (rows_eval C he)

theorem input_live (k : ℕ) (hb : Live.build basicOps goal k inputs.toFinset) :
    Live.live basicOps goal k inputs.toFinset := by
  obtain ⟨S,hsub,hLive⟩ := Live.compress hb
  exact full_inputs hsub hLive ▸ hLive

theorem extend_live {m n : ℕ} (le : m ≤ n) (h : Live.live basicOps goal m inputs.toFinset) :
    Live.live basicOps goal n inputs.toFinset := by
  induction le with
  | refl => exact h
  | step _ ih => exact Or.inl ih

end Check

end PEqualNP.Outside.L_meta_670_aux.SignedCheck
