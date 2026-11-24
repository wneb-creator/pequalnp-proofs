import Mathlib.Data.List.Sublists
import Mathlib.Data.List.Count
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_1417
private def target (t : ℕ) (x : Fin 5 → Bool) : Bool :=
  t.testBit (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)

private def upper (t k : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ),
    (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
    gs.length ≤ k ∧ ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs, o⟩ (List.ofFn x) = target t x

private lemma upper_mono {t a b : ℕ} (h : upper t a) (hle : a ≤ b) : upper t b := by
  obtain ⟨gs, o, hb, hl, hv⟩ := h
  exact ⟨gs, o, hb, hl.trans hle, hv⟩

private def gs0 : List Gate := [⟨.and, [0,2]⟩, ⟨.and, [1,5]⟩, ⟨.or, [1,5]⟩, ⟨.and, [4,7]⟩, ⟨.or, [0,2]⟩, ⟨.and, [3,9]⟩, ⟨.and, [8,10]⟩, ⟨.or, [6,11]⟩]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem upper0 : upper 0xe8808080 8 := by
  refine ⟨gs0, 12, ?_, by decide, ?_⟩
  · simp only [gs0, List.mem_cons, List.not_mem_nil, or_false]
    rintro g (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
  · decide +kernel

private def gs1 : List Gate := [⟨.or, [3,4]⟩, ⟨.or, [2,5]⟩, ⟨.and, [3,4]⟩, ⟨.and, [2,7]⟩, ⟨.and, [1,6]⟩, ⟨.or, [8,9]⟩, ⟨.and, [0,10]⟩]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem upper1 : upper 0xa8888880 7 := by
  refine ⟨gs1, 11, ?_, by decide, ?_⟩
  · simp only [gs1, List.mem_cons, List.not_mem_nil, or_false]
    rintro g (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
  · decide +kernel

private def gs2 : List Gate := [⟨.and, [1,4]⟩, ⟨.or, [2,5]⟩, ⟨.or, [1,3]⟩, ⟨.and, [0,6]⟩, ⟨.and, [7,8]⟩]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem upper2 : upper 0xa888a080 5 := by
  refine ⟨gs2, 9, ?_, by decide, ?_⟩
  · simp only [gs2, List.mem_cons, List.not_mem_nil, or_false]
    rintro g (rfl | rfl | rfl | rfl | rfl) <;> simp
  · decide +kernel

private def gs3 : List Gate := [⟨.and, [2,3]⟩, ⟨.or, [0,1]⟩, ⟨.and, [4,6]⟩, ⟨.and, [0,1]⟩, ⟨.and, [5,7]⟩, ⟨.or, [2,3]⟩, ⟨.and, [8,10]⟩, ⟨.or, [9,11]⟩]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem upper3 : upper 0xe8808880 8 := by
  refine ⟨gs3, 12, ?_, by decide, ?_⟩
  · simp only [gs3, List.mem_cons, List.not_mem_nil, or_false]
    rintro g (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
  · decide +kernel

private def gs4 : List Gate := [⟨.and, [1,4]⟩, ⟨.and, [2,3]⟩, ⟨.and, [5,6]⟩, ⟨.or, [5,6]⟩, ⟨.or, [0,7]⟩, ⟨.and, [8,9]⟩]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem upper4 : upper 0xe888a000 6 := by
  refine ⟨gs4, 10, ?_, by decide, ?_⟩
  · simp only [gs4, List.mem_cons, List.not_mem_nil, or_false]
    rintro g (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
  · decide +kernel

private def gs5 : List Gate := [⟨.and, [3,4]⟩, ⟨.and, [2,5]⟩, ⟨.or, [1,6]⟩, ⟨.and, [0,7]⟩]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem upper5 : upper 0xa8888888 4 := by
  refine ⟨gs5, 8, ?_, by decide, ?_⟩
  · simp only [gs5, List.mem_cons, List.not_mem_nil, or_false]
    rintro g (rfl | rfl | rfl | rfl) <;> simp
  · decide +kernel

private def gs6 : List Gate := [⟨.or, [3,4]⟩, ⟨.and, [2,3]⟩, ⟨.or, [2,5]⟩, ⟨.or, [1,6]⟩, ⟨.and, [0,8]⟩, ⟨.and, [7,9]⟩]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem upper6 : upper 0xa888a880 6 := by
  refine ⟨gs6, 10, ?_, by decide, ?_⟩
  · simp only [gs6, List.mem_cons, List.not_mem_nil, or_false]
    rintro g (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
  · decide +kernel

private def gs7 : List Gate := [⟨.or, [3,4]⟩, ⟨.and, [0,5]⟩, ⟨.or, [1,2]⟩, ⟨.and, [6,7]⟩]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem upper7 : upper 0xa8a8a800 4 := by
  refine ⟨gs7, 8, ?_, by decide, ?_⟩
  · simp only [gs7, List.mem_cons, List.not_mem_nil, or_false]
    rintro g (rfl | rfl | rfl | rfl) <;> simp
  · decide +kernel

private def gs8 : List Gate := [⟨.or, [1,3]⟩, ⟨.and, [2,4]⟩, ⟨.and, [1,3]⟩, ⟨.and, [6,7]⟩, ⟨.or, [2,7]⟩, ⟨.and, [0,9]⟩, ⟨.and, [5,10]⟩, ⟨.or, [8,11]⟩]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem upper8 : upper 0xe880a880 8 := by
  refine ⟨gs8, 12, ?_, by decide, ?_⟩
  · simp only [gs8, List.mem_cons, List.not_mem_nil, or_false]
    rintro g (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
  · decide +kernel

private def gs9 : List Gate := [⟨.or, [3,4]⟩, ⟨.or, [0,1]⟩, ⟨.and, [2,3]⟩, ⟨.and, [4,6]⟩, ⟨.or, [2,5]⟩, ⟨.and, [0,1]⟩, ⟨.and, [9,10]⟩, ⟨.and, [7,8]⟩, ⟨.or, [11,12]⟩]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem upper9 : upper 0xe8888880 9 := by
  refine ⟨gs9, 13, ?_, by decide, ?_⟩
  · simp only [gs9, List.mem_cons, List.not_mem_nil, or_false]
    rintro g (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp
  · decide +kernel

private abbrev Q := BitVec 32

private def norm (w : Q) := if w.getLsbD 0 then ~~~w else w

private def ops (a b : Q) := [a &&& b, a ||| b, a &&& ~~~b, b &&& ~~~a]

private def Trail (t : Q) (s : Finset Q) (n : ℕ) : Prop :=
  ∀ P : Finset Q → ℕ → Prop,
    (∀ k, P {t} k) →
    (∀ {r : Finset Q} {a b c : Q} {k : ℕ}, a ≠ b → c ∉ insert a (insert b r) →
      c ≠ 0 → c ∈ ops a b → P (insert c r) k → P (insert a (insert b r)) (k+1)) →
    P s n

private theorem Trail.done {t : Q} (k : ℕ) : Trail t {t} k :=
  fun _ done _ => done k

private theorem Trail.step {t a b c : Q} {r : Finset Q} {k : ℕ} (hab : a ≠ b)
    (hf : c ∉ insert a (insert b r)) (nz : c ≠ 0) (hc : c ∈ ops a b)
    (h : Trail t (insert c r) k) : Trail t (insert a (insert b r)) (k+1) :=
  fun P done step => step hab hf nz hc (h P done step)

private theorem trail_ind {t : Q} {P : Finset Q → ℕ → Prop} {s n} (h : Trail t s n)
    (done : ∀ k, P {t} k)
    (step : ∀ {r a b c k}, a ≠ b → c ∉ insert a (insert b r) → c ≠ 0 → c ∈ ops a b →
      Trail t (insert c r) k → P (insert c r) k → P (insert a (insert b r)) (k+1)) : P s n :=
  (h (fun r k => Trail t r k ∧ P r k) (fun k => ⟨Trail.done k, done k⟩)
    (fun hab hf nz hc h' => ⟨Trail.step hab hf nz hc h'.1, step hab hf nz hc h'.1 h'.2⟩)).2

private theorem trail_lift {t s n} (h : Trail t s n) : Trail t s (n+1) := by
  apply trail_ind (P := fun s n => Trail t s (n+1)) h
  · intro k; exact Trail.done _
  · intro r a b c k hab hf nz hc _ ih; exact .step hab hf nz hc ih

private theorem trail_mono {t s n m} (h : Trail t s n) (le : n ≤ m) : Trail t s m := by
  induction le with
  | refl => exact h
  | step _ ih => exact trail_lift ih

private theorem trail_card {t s n} (h : Trail t s n) : s.card ≤ n+1 := by
  apply trail_ind (P := fun s n => s.card ≤ n+1) h
  · simp
  · intro r a b c k hab fresh nz hc h ih
    have hn : c ∉ r := fun hh => fresh (by simp [hh])
    rw [Finset.card_insert_of_notMem hn] at ih
    have := Finset.card_insert_le a (insert b r)
    have := Finset.card_insert_le b r
    omega

private theorem trail_sep {t s n} (h : Trail t s n) (i j : ℕ) (hi : i < 32) (hj : j < 32)
    (same : ∀ x ∈ s, x.getLsbD i = x.getLsbD j) : t.getLsbD i = t.getLsbD j := by
  revert same
  apply trail_ind (P := fun s _ => (∀ x ∈ s, x.getLsbD i = x.getLsbD j) → t.getLsbD i = t.getLsbD j) h
  · intro k same; exact same _ (by simp)
  · intro r a b c k hab fresh nz hc h ih same
    apply ih
    have ha := same a (by simp)
    have hb := same b (by simp)
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hxr
    · simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl <;>
        simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, BitVec.getLsbD_not, decide_eq_true hi, decide_eq_true hj, ha, hb]
    · exact same _ (by simp [hxr])

private def jumps : List ℕ := [1, 2, 4, 8, 16]
private def dif (w : Q) (d : ℕ) := (w ^^^ (w >>> d)) &&& (BitVec.allOnes 32 >>> d)
private def unionDif (ws : List Q) (d : ℕ) : Q :=
  ws.foldr (fun w s => dif w d ||| s) 0
private def cover (t : Q) (ws : List Q) : Bool :=
  jumps.all fun d => (dif t d &&& unionDif ws d) == dif t d

private theorem bit_dif {w : Q} {d i : ℕ} (hi : i < 32) :
    (dif w d).getLsbD i = true ↔ i+d < 32 ∧ w.getLsbD i ≠ w.getLsbD (i+d) := by
  simp only [dif, BitVec.getLsbD_and, BitVec.getLsbD_xor, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes, Bool.and_eq_true, decide_eq_true_eq, Nat.add_comm d i]
  cases w.getLsbD i <;> cases w.getLsbD (i + d) <;> simp

private theorem bit_union (ws : List Q) (d i : ℕ) :
    (unionDif ws d).getLsbD i = true ↔ ∃ w ∈ ws, (dif w d).getLsbD i = true := by
  induction ws with
  | nil => simp [unionDif]
  | cons w ws ih =>
    change (dif w d ||| unionDif ws d).getLsbD i = true ↔ _
    simp [ih]

private theorem trail_cover {t : Q} {ws : List Q} {n} (h : Trail t ws.toFinset n) :
    cover t ws = true := by
  apply List.all_eq_true.mpr
  intro d _
  apply beq_iff_eq.mpr
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [BitVec.getLsbD_and]
  cases hd : (dif t d).getLsbD i with
  | false => rfl
  | true =>
    obtain ⟨hj, hne⟩ := (bit_dif hi).mp hd
    have ex : ∃ w ∈ ws, w.getLsbD i ≠ w.getLsbD (i+d) := by
      by_contra! hn
      exact hne (trail_sep h i _ hi hj (by simpa using hn))
    obtain ⟨w, hw, hh⟩ := ex
    rw [(bit_union ws d i).mpr ⟨w, hw, (bit_dif hi).mpr ⟨hj,hh⟩⟩]
    rfl

private def pools (ws : List Q) (a b : Q) : List (List Q) :=
  [ws.filter (fun x => x != a && x != b), ws.filter (· != a), ws.filter (· != b), ws]

private def walk (t : Q) : ℕ → List Q → Bool
  | 0, ws => ws.contains t
  | n+1, ws =>
    ws.length ≤ n+2 && cover t ws &&
    (ws.contains t || ws.any fun a => ws.any fun b => a < b &&
      (pools ws a b).any fun r => r.length ≤ n &&
        (ops a b).any fun c => !(ws.contains c) && c != 0 && walk t n (c :: r))

private theorem pools_find {ws : List Q} {r : Finset Q} {a b : Q}
    (hw : ws.toFinset = insert a (insert b r)) (hn : ws.Nodup) :
    ∃ l ∈ pools ws a b, l.Nodup ∧ l.toFinset = r := by
  have mem (x : Q) : x ∈ ws ↔ x = a ∨ x = b ∨ x ∈ r := by
    rw [← List.mem_toFinset, hw]; simp
  by_cases ha : a ∈ r <;> by_cases hb : b ∈ r
  · exact ⟨ws, by simp [pools], hn, by simpa [ha,hb] using hw⟩
  · refine ⟨ws.filter (· != b), by simp [pools], hn.filter _, ?_⟩
    ext x; simp [mem, ha, hb]; grind
  · refine ⟨ws.filter (· != a), by simp [pools], hn.filter _, ?_⟩
    ext x; simp [mem, ha, hb]; grind
  · refine ⟨ws.filter (fun x => x != a && x != b), by simp [pools], hn.filter _, ?_⟩
    ext x; simp [mem, ha, hb]; grind

private theorem ops_swap {a b c : Q} (h : c ∈ ops a b) : c ∈ ops b a := by
  simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at *
  rw [BitVec.and_comm a b, BitVec.or_comm a b] at h
  tauto


private theorem walk_pair {a b c : Q} {r : Finset Q} {t : Q} {k : ℕ}
    {ws : List Q} (hab : a < b) (hw : ws.toFinset = insert a (insert b r))
    (hn : ws.Nodup) (fresh : c ∉ insert a (insert b r)) (nz : c ≠ 0) (hc : c ∈ ops a b)
    (hdr : Trail t (insert c r) k)
    (ih : ∀ vs : List Q, vs.toFinset = insert c r → vs.Nodup → walk t k vs = true) :
    (ws.any fun a => ws.any fun b => a < b &&
      (pools ws a b).any fun r => r.length ≤ k &&
        (ops a b).any fun c => !(ws.contains c) && c != 0 && walk t k (c :: r)) = true := by
  obtain ⟨l, hl, hnl, hfl⟩ := pools_find hw hn
  have ha : a ∈ ws := by rw [← List.mem_toFinset, hw]; simp
  have hb : b ∈ ws := by rw [← List.mem_toFinset, hw]; simp
  have hnws : c ∉ ws := by simpa [← hw] using fresh
  have hnr : c ∉ r := fun h => fresh (by simp [h])
  have hnlc : c ∉ l := by simpa [← hfl] using hnr
  have hsize := trail_card hdr
  rw [Finset.card_insert_of_notMem hnr, ← hfl, List.toFinset_card_of_nodup hnl] at hsize
  apply List.any_eq_true.mpr
  refine ⟨a, ha, List.any_eq_true.mpr ⟨b, hb, ?_⟩⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨hab, List.any_eq_true.mpr ⟨l, hl, ?_⟩⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨by omega, List.any_eq_true.mpr ⟨c, hc, ?_⟩⟩
  simp [hnws, nz, ih (c :: l) (by simp [hfl]) (List.nodup_cons.mpr ⟨hnlc, hnl⟩)] <;> exact nz

private theorem trail_walk {t s n} (h : Trail t s n) :
    ∀ ws : List Q, ws.toFinset = s → ws.Nodup → walk t n ws = true := by
  apply trail_ind (P := fun s n => ∀ ws : List Q, ws.toFinset = s → ws.Nodup → walk t n ws = true) h
  · intro k
    intro ws hw hn
    have ht : t ∈ ws := by rw [← List.mem_toFinset, hw]; simp
    cases k with
    | zero => simpa [walk] using ht
    | succ k =>
      have hcv := trail_cover (t := t) (n := k+1) (ws := ws) (hw ▸ Trail.done (t := t) (k+1))
      have hc := List.toFinset_card_of_nodup hn
      rw [hw, Finset.card_singleton] at hc
      simp [walk, ht, hcv, show ws.length ≤ k+2 by omega]
  · intro r a b c k hab fresh nz hc h ih
    intro ws hw hn
    have hall := Trail.step hab fresh nz hc h
    have hcv := trail_cover (ws := ws) (hw ▸ hall)
    have hsize := trail_card hall
    rw [← hw, List.toFinset_card_of_nodup hn] at hsize
    simp only [walk, show ws.length ≤ k+2 by omega, decide_true, hcv, Bool.true_and]
    rw [Bool.or_eq_true]
    right
    have hne : a.toNat ≠ b.toNat := fun he => hab (BitVec.eq_of_toNat_eq he)
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact walk_pair hlt hw hn fresh nz hc h ih
    · rw [Finset.insert_comm] at hw fresh
      exact walk_pair hgt hw hn fresh nz (ops_swap hc) h ih


private def readQ (x : Fin 32) (w : Q) := w.getLsbD x.val
private def Basis (gs : List Gate) :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

private theorem read_not (x : Fin 32) (w : Q) : readQ x (~~~w) = !(readQ x w) := by
  simp [readQ, x.isLt]
private theorem read_zero (x : Fin 32) : readQ x 0 = false := by simp [readQ]

private theorem getD_table (x : Fin 32) (ws : List Q) (i : ℕ) :
    (ws.map (readQ x)).getD i false = readQ x (ws.getD i 0) := by
  by_cases hi : i < ws.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    simp [readQ]

private def gateQ (ws : List Q) (g : Gate) : Q :=
  match g.op, g.inputs with
  | .and, [] => ~~~0
  | .and, [i] => ws.getD i 0
  | .and, i :: j :: _ => ws.getD i 0 &&& ws.getD j 0
  | .or, [] => 0
  | .or, [i] => ws.getD i 0
  | .or, i :: j :: _ => ws.getD i 0 ||| ws.getD j 0
  | .not, [] => ~~~0
  | .not, i :: _ => ~~~(ws.getD i 0)
  | _, _ => 0

private theorem read_gateQ (x : Fin 32) (ws : List Q) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    g.op.eval (g.inputs.map fun i => (ws.map (readQ x)).getD i false) =
      readQ x (gateQ ws g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  simp only [getD_table]
  cases op with
  | and =>
    match ins, hlen with
    | [], _ =>
      change true = readQ x (~~~0)
      simp only [read_not, read_zero, Bool.not_false]
    | [i], _ => simp [gateQ, GateOp.eval]
    | [i, j], _ => simp [gateQ, GateOp.eval, readQ, BitVec.getLsbD_and]
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    match ins, hlen with
    | [], _ => simp [gateQ, GateOp.eval, readQ]
    | [i], _ => simp [gateQ, GateOp.eval]
    | [i, j], _ => simp [gateQ, GateOp.eval, readQ, BitVec.getLsbD_or]
    | _ :: _ :: _ :: _, h => simp at h
  | not =>
    cases ins with
    | nil =>
      change true = readQ x (~~~0)
      simp only [read_not, read_zero, Bool.not_false]
    | cons i is =>
      exact (read_not x (ws.getD i 0)).symm
  | mod m => simp at hop
  | maj => simp at hop

private def wireQs (gs : List Gate) (ws : List Q) : List Q :=
  gs.foldl (fun vs g => vs ++ [gateQ vs g]) ws

private theorem read_wireQs (x : Fin 32) (gs : List Gate) (ws : List Q)
    (h : Basis gs) :
    (Circuit.wires ⟨gs, 0⟩ (ws.map (readQ x))) = (wireQs gs ws).map (readQ x) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    have hg := read_gateQ x ws g (h g List.mem_cons_self)
    change Circuit.wires ⟨gs, 0⟩
        (ws.map (readQ x) ++ [g.op.eval (g.inputs.map fun i =>
          (ws.map (readQ x)).getD i false)]) =
      (wireQs gs (ws ++ [gateQ ws g])).map (readQ x)
    rw [hg, ← List.map_singleton, ← List.map_append]
    exact ih _ (fun g' hg' => h g' (List.mem_cons_of_mem _ hg'))

private def flag (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

private def cost (gs : List Gate) := gs.countP (fun g => !flag g)

private def avail (ws : List Q) : Finset Q := insert 0 (ws.map norm).toFinset

private theorem norm_compl (u : Q) : norm (~~~u) = norm u := by
  unfold norm
  cases h : u.getLsbD 0 <;> simp only [BitVec.getLsbD_not, h] <;> simp

private theorem norm_pair (u v : Q) :
    norm (u &&& v) ∈ ops (norm u) (norm v) ∧ norm (u ||| v) ∈ ops (norm u) (norm v) := by
  unfold norm ops
  cases hu : u.getLsbD 0 <;> cases hv : v.getLsbD 0 <;>
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_or, hu, hv] <;> simp [BitVec.not_and, BitVec.not_or, BitVec.and_comm, BitVec.or_comm]

private theorem norm_get (ws : List Q) (i : ℕ) : norm (ws.getD i 0) ∈ avail ws := by
  by_cases hi : i < ws.length
  · rw [List.getD_eq_getElem _ _ hi]
    simp [avail, List.mem_map.mpr ⟨_, List.getElem_mem hi, rfl⟩]
  · rw [List.getD_eq_default _ _ (by omega)]
    simp [avail, norm]

private theorem fresh_pair {s : Finset Q} {c u v : Q} (hc : c ∈ ops u v) (hu : u ∈ s) (hv : v ∈ s)
    (hz : (0 : Q) ∈ s) (hf : c ∉ s) : u ≠ v := by
  rintro rfl
  simp only [ops, BitVec.and_self, BitVec.or_self, BitVec.and_not_self, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  grind

private theorem fresh_gate (ws : List Q) (g : Gate)
    (hg : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hf : norm (gateQ ws g) ∉ avail ws) :
    flag g = false ∧ ∃ a ∈ avail ws, ∃ b ∈ avail ws, a ≠ b ∧ norm (gateQ ws g) ∈ ops a b := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, len⟩ := hg
  have hz : norm 0 ∈ avail ws := by simp [avail, norm]
  have pair (i j : ℕ) {c : Q} (h : c ∈ ops (norm (ws.getD i 0)) (norm (ws.getD j 0)))
      (hn : c ∉ avail ws) :
      ∃ a ∈ avail ws, ∃ b ∈ avail ws, a ≠ b ∧ c ∈ ops a b :=
    ⟨_, norm_get ws i, _, norm_get ws j, fresh_pair h (norm_get ws i) (norm_get ws j)
      (by simp [avail]) hn, h⟩
  cases op with
  | and =>
    refine ⟨rfl, ?_⟩
    match ins, len with
    | [], _ => exact False.elim (hf (by change norm (~~~(0 : Q)) ∈ avail ws; rwa [norm_compl]))
    | [i], _ => exact False.elim (hf (norm_get ws i))
    | [i,j], _ => exact pair i j (norm_pair _ _).1 hf
    | _ :: _ :: _ :: _, h => simp at h
  | or =>
    refine ⟨rfl, ?_⟩
    match ins, len with
    | [], _ => exact False.elim (hf hz)
    | [i], _ => exact False.elim (hf (norm_get ws i))
    | [i,j], _ => exact pair i j (norm_pair _ _).2 hf
    | _ :: _ :: _ :: _, h => simp at h
  | not =>
    exfalso
    apply hf
    cases ins with
    | nil => change norm (~~~(0 : Q)) ∈ avail ws; rwa [norm_compl]
    | cons i is => simpa [gateQ, norm_compl] using norm_get ws i
  | mod m => simp at hop
  | maj => simp at hop

private theorem trail_extract {gs : List Gate} (ws : List Q) (hb : Basis gs) (o : ℕ) :
    ∃ s ⊆ avail ws, Trail (norm ((wireQs gs ws).getD o 0)) s (cost gs) := by
  induction gs generalizing ws with
  | nil => exact ⟨{_}, Finset.singleton_subset_iff.mpr (norm_get ws o), .done _⟩
  | cons g gs ih =>
    let c := norm (gateQ ws g)
    obtain ⟨s, hs, ht⟩ := ih (ws ++ [gateQ ws g]) (fun x hx => hb x (by simp [hx]))
    change ∃ s ⊆ avail ws, Trail (norm ((wireQs gs (ws ++ [gateQ ws g])).getD o 0)) s _
    have he : avail (ws ++ [gateQ ws g]) = insert c (avail ws) := by
      ext x; simp [avail, c]; tauto
    rw [he] at hs
    have hcost : cost gs ≤ cost (g :: gs) := by simp [cost, List.countP_cons]
    by_cases sub : s ⊆ avail ws
    · exact ⟨s, sub, trail_mono ht hcost⟩
    · have hn : c ∉ avail ws := by
        intro hh; rw [Finset.insert_eq_of_mem hh] at hs; exact sub hs
      have hcs : c ∈ s := by
        by_contra h
        apply sub; intro x hx
        exact (Finset.mem_insert.mp (hs hx)).resolve_left (by rintro rfl; exact h hx)
      have hr : s.erase c ⊆ avail ws := by
        intro x hx
        exact (Finset.mem_insert.mp (hs (Finset.mem_of_mem_erase hx))).resolve_left
          (Finset.ne_of_mem_erase hx)
      obtain ⟨hflag, a, ha, b, hbb, hab, hc⟩ := fresh_gate ws g (hb g (by simp)) hn
      have heq : insert c (s.erase c) = s := Finset.insert_erase hcs
      have hsub : insert a (insert b (s.erase c)) ⊆ avail ws := Finset.insert_subset_iff.mpr ⟨ha, Finset.insert_subset_iff.mpr ⟨hbb,hr⟩⟩
      refine ⟨_, hsub, ?_⟩
      rw [show cost (g :: gs) = cost gs + 1 by simp [cost, List.countP_cons, hflag]]
      exact .step hab (fun h => hn (hsub h)) (fun h => hn (h ▸ (by simp [avail])))
        hc (by rwa [heq])


private def inputs : List Q := [0xaaaaaaaa,0xcccccccc,0xf0f0f0f0,0xff00ff00,0xffff0000]
private def initial : List Q := 0 :: inputs
private theorem init_avail : avail inputs = initial.toFinset := by decide +kernel
private def run (t : Q) (k : ℕ) := initial.sublists.any (walk t k)

private theorem input_eval (i : Fin 32) :
    List.ofFn (fun j : Fin 5 => i.val.testBit j.val) = inputs.map (readQ i) := by decide +revert +kernel
private theorem index_eval (i : Fin 32) :
    (∑ j : Fin 5, if i.val.testBit j.val then 2 ^ j.val else 0) = i.val := by decide +revert +kernel

private theorem lower_run {gs : List Gate} (hb : Basis gs) {o t : ℕ}
    (hv : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target t x)
    (n : ℕ) (hc : cost gs ≤ n) : run (norm (BitVec.ofNat 32 t)) n = true := by
  have he : (wireQs gs inputs).getD o 0 = BitVec.ofNat 32 t := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hi
    let f : Fin 5 → Bool := fun j => i.testBit j.val
    have h := hv f
    change (Circuit.wires ⟨gs,0⟩ (List.ofFn f)).getD o false = _ at h
    rw [show List.ofFn f = inputs.map (readQ ⟨i,hi⟩) from input_eval ⟨i,hi⟩,
      read_wireQs _ _ _ hb, getD_table] at h
    change _ = t.testBit (∑ j : Fin 5, if i.testBit j.val then 2 ^ j.val else 0) at h
    rw [index_eval ⟨i,hi⟩] at h
    simpa only [readQ, BitVec.getLsbD_ofNat, decide_eq_true hi, Bool.true_and] using h
  obtain ⟨s, hs, ht⟩ := trail_extract inputs hb o
  rw [he] at ht
  rw [init_avail] at hs
  let ws := initial.filter (· ∈ s)
  have hw : ws.toFinset = s := by ext x; simp [ws]; exact fun a => List.mem_toFinset.mp (hs a)
  have hnd : initial.Nodup := by decide +kernel
  exact List.any_eq_true.mpr ⟨ws, List.mem_sublists.mpr List.filter_sublist,
    trail_walk (trail_mono ht hc) ws hw (hnd.filter _)⟩

private theorem cost_lt {gs : List Gate} (hh : ∃ g ∈ gs, g.op = .not) : cost gs < gs.length := by
  have h : ∃ g ∈ gs, (!flag g) = false := by
    obtain ⟨g,hg,hop⟩ := hh
    exact ⟨g,hg, by simp [flag, hop]⟩
  simpa [cost] using (List.countP_lt_length_iff.mpr h)

private theorem resolve_row {t k : ℕ} {gs : List Gate} {o : ℕ}
    (hup : upper t k) (hex : run (norm (BitVec.ofNat 32 t)) (k-2) = false)
    (hb : Basis gs) (hn : ∃ g ∈ gs, g.op = .not)
    (hv : ∀ x : Fin 5 → Bool, Circuit.eval ⟨gs,o⟩ (List.ofFn x) = target t x) :
    upper t gs.length := by
  apply upper_mono hup
  by_contra! h
  have hcost := cost_lt hn
  have hrun := lower_run hb hv (k-2) (by omega)
  rw [hex] at hrun
  contradiction

private def splitRun (t : Q) (n m j : ℕ) :=
  initial.sublists.any fun ws =>
    ws.length ≤ n+2 && cover t ws &&
    (ws.contains t || ws.any fun a => ws.any fun b => a < b &&
      (pools ws a b).any fun r => r.length ≤ n &&
        (ops a b).any fun c => (c.toNat % m == j) &&
          !(ws.contains c) && c != 0 && walk t n (c :: r))

private theorem partition_run {t : Q} {n m : ℕ} (hm : 0 < m)
    (hh : ∀ j : Fin m, splitRun t n m j.val = false) : run t (n+1) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨ws,hw,hg⟩ := List.any_eq_true.mp h
  simp only [walk, Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq] at hg
  obtain ⟨⟨hl, hv⟩, ht | ⟨a,ha,b,hb,hab,r,hr,hlen,c,hc,⟨hhc,hz⟩,hwalk⟩⟩ := hg
  · have hsplit : splitRun t n m 0 = true := by
      apply List.any_eq_true.mpr
      exact ⟨ws,hw, by simp [hl, hv, List.contains_iff_mem.mp ht]⟩
    have he := hh ⟨0,hm⟩
    change splitRun t n m 0 = false at he
    rw [he] at hsplit
    contradiction
  · let j : Fin m := ⟨c.toNat % m, Nat.mod_lt _ hm⟩
    have hsplit : splitRun t n m j.val = true := by
      apply List.any_eq_true.mpr
      refine ⟨ws,hw,?_⟩
      simp only [Bool.and_eq_true, Bool.or_eq_true, List.any_eq_true, decide_eq_true_eq]
      exact ⟨⟨hl,hv⟩, Or.inr ⟨a,ha,b,hb,hab,r,hr,hlen,c,hc,⟨⟨by simp [j],hhc⟩,hz⟩,hwalk⟩⟩
    rw [hh j] at hsplit
    contradiction


set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case0x0 : splitRun (norm (BitVec.ofNat 32 0xe8808080)) 5 13 0 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case0x1 : splitRun (norm (BitVec.ofNat 32 0xe8808080)) 5 13 1 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case0x2 : splitRun (norm (BitVec.ofNat 32 0xe8808080)) 5 13 2 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case0x3 : splitRun (norm (BitVec.ofNat 32 0xe8808080)) 5 13 3 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case0x4 : splitRun (norm (BitVec.ofNat 32 0xe8808080)) 5 13 4 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case0x5 : splitRun (norm (BitVec.ofNat 32 0xe8808080)) 5 13 5 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case0x6 : splitRun (norm (BitVec.ofNat 32 0xe8808080)) 5 13 6 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case0x7 : splitRun (norm (BitVec.ofNat 32 0xe8808080)) 5 13 7 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case0x8 : splitRun (norm (BitVec.ofNat 32 0xe8808080)) 5 13 8 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case0x9 : splitRun (norm (BitVec.ofNat 32 0xe8808080)) 5 13 9 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case0x10 : splitRun (norm (BitVec.ofNat 32 0xe8808080)) 5 13 10 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case0x11 : splitRun (norm (BitVec.ofNat 32 0xe8808080)) 5 13 11 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case0x12 : splitRun (norm (BitVec.ofNat 32 0xe8808080)) 5 13 12 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem excluded0 : run (norm (BitVec.ofNat 32 0xe8808080)) (8-2) = false := by
  apply partition_run (n := 5) (m := 13) (by decide)
  intro j
  fin_cases j
  · exact case0x0
  · exact case0x1
  · exact case0x2
  · exact case0x3
  · exact case0x4
  · exact case0x5
  · exact case0x6
  · exact case0x7
  · exact case0x8
  · exact case0x9
  · exact case0x10
  · exact case0x11
  · exact case0x12

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem excluded1 : run (norm (BitVec.ofNat 32 0xa8888880)) (7-2) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem excluded2 : run (norm (BitVec.ofNat 32 0xa888a080)) (5-2) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case3x0 : splitRun (norm (BitVec.ofNat 32 0xe8808880)) 5 13 0 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case3x1 : splitRun (norm (BitVec.ofNat 32 0xe8808880)) 5 13 1 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case3x2 : splitRun (norm (BitVec.ofNat 32 0xe8808880)) 5 13 2 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case3x3 : splitRun (norm (BitVec.ofNat 32 0xe8808880)) 5 13 3 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case3x4 : splitRun (norm (BitVec.ofNat 32 0xe8808880)) 5 13 4 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case3x5 : splitRun (norm (BitVec.ofNat 32 0xe8808880)) 5 13 5 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case3x6 : splitRun (norm (BitVec.ofNat 32 0xe8808880)) 5 13 6 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case3x7 : splitRun (norm (BitVec.ofNat 32 0xe8808880)) 5 13 7 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case3x8 : splitRun (norm (BitVec.ofNat 32 0xe8808880)) 5 13 8 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case3x9 : splitRun (norm (BitVec.ofNat 32 0xe8808880)) 5 13 9 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case3x10 : splitRun (norm (BitVec.ofNat 32 0xe8808880)) 5 13 10 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case3x11 : splitRun (norm (BitVec.ofNat 32 0xe8808880)) 5 13 11 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case3x12 : splitRun (norm (BitVec.ofNat 32 0xe8808880)) 5 13 12 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem excluded3 : run (norm (BitVec.ofNat 32 0xe8808880)) (8-2) = false := by
  apply partition_run (n := 5) (m := 13) (by decide)
  intro j
  fin_cases j
  · exact case3x0
  · exact case3x1
  · exact case3x2
  · exact case3x3
  · exact case3x4
  · exact case3x5
  · exact case3x6
  · exact case3x7
  · exact case3x8
  · exact case3x9
  · exact case3x10
  · exact case3x11
  · exact case3x12

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem excluded4 : run (norm (BitVec.ofNat 32 0xe888a000)) (6-2) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem excluded5 : run (norm (BitVec.ofNat 32 0xa8888888)) (4-2) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem excluded6 : run (norm (BitVec.ofNat 32 0xa888a880)) (6-2) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem excluded7 : run (norm (BitVec.ofNat 32 0xa8a8a800)) (4-2) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case8x0 : splitRun (norm (BitVec.ofNat 32 0xe880a880)) 5 13 0 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case8x1 : splitRun (norm (BitVec.ofNat 32 0xe880a880)) 5 13 1 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case8x2 : splitRun (norm (BitVec.ofNat 32 0xe880a880)) 5 13 2 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case8x3 : splitRun (norm (BitVec.ofNat 32 0xe880a880)) 5 13 3 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case8x4 : splitRun (norm (BitVec.ofNat 32 0xe880a880)) 5 13 4 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case8x5 : splitRun (norm (BitVec.ofNat 32 0xe880a880)) 5 13 5 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case8x6 : splitRun (norm (BitVec.ofNat 32 0xe880a880)) 5 13 6 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case8x7 : splitRun (norm (BitVec.ofNat 32 0xe880a880)) 5 13 7 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case8x8 : splitRun (norm (BitVec.ofNat 32 0xe880a880)) 5 13 8 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case8x9 : splitRun (norm (BitVec.ofNat 32 0xe880a880)) 5 13 9 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case8x10 : splitRun (norm (BitVec.ofNat 32 0xe880a880)) 5 13 10 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case8x11 : splitRun (norm (BitVec.ofNat 32 0xe880a880)) 5 13 11 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case8x12 : splitRun (norm (BitVec.ofNat 32 0xe880a880)) 5 13 12 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem excluded8 : run (norm (BitVec.ofNat 32 0xe880a880)) (8-2) = false := by
  apply partition_run (n := 5) (m := 13) (by decide)
  intro j
  fin_cases j
  · exact case8x0
  · exact case8x1
  · exact case8x2
  · exact case8x3
  · exact case8x4
  · exact case8x5
  · exact case8x6
  · exact case8x7
  · exact case8x8
  · exact case8x9
  · exact case8x10
  · exact case8x11
  · exact case8x12

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x0 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 0 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x1 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 1 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x2 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 2 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x3 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 3 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x4 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 4 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x5 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 5 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x6 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 6 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x7 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 7 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x8 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 8 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x9 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 9 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x10 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 10 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x11 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 11 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x12 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 12 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x13 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 13 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x14 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 14 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x15 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 15 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x16 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 16 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x17 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 17 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x18 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 18 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x19 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 19 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x20 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 20 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x21 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 21 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x22 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 22 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x23 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 23 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x24 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 24 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x25 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 25 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x26 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 26 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x27 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 27 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x28 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 28 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x29 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 29 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x30 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 30 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x31 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 31 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x32 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 32 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x33 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 33 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x34 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 34 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x35 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 35 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x36 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 36 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x37 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 37 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x38 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 38 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x39 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 39 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x40 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 40 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x41 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 41 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x42 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 42 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x43 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 43 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x44 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 44 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x45 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 45 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x46 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 46 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x47 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 47 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x48 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 48 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x49 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 49 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x50 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 50 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x51 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 51 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem case9x52 : splitRun (norm (BitVec.ofNat 32 0xe8888880)) 6 53 52 = false := by decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 0 in
private theorem excluded9 : run (norm (BitVec.ofNat 32 0xe8888880)) (9-2) = false := by
  apply partition_run (n := 6) (m := 53) (by decide)
  intro j
  fin_cases j
  · exact case9x0
  · exact case9x1
  · exact case9x2
  · exact case9x3
  · exact case9x4
  · exact case9x5
  · exact case9x6
  · exact case9x7
  · exact case9x8
  · exact case9x9
  · exact case9x10
  · exact case9x11
  · exact case9x12
  · exact case9x13
  · exact case9x14
  · exact case9x15
  · exact case9x16
  · exact case9x17
  · exact case9x18
  · exact case9x19
  · exact case9x20
  · exact case9x21
  · exact case9x22
  · exact case9x23
  · exact case9x24
  · exact case9x25
  · exact case9x26
  · exact case9x27
  · exact case9x28
  · exact case9x29
  · exact case9x30
  · exact case9x31
  · exact case9x32
  · exact case9x33
  · exact case9x34
  · exact case9x35
  · exact case9x36
  · exact case9x37
  · exact case9x38
  · exact case9x39
  · exact case9x40
  · exact case9x41
  · exact case9x42
  · exact case9x43
  · exact case9x44
  · exact case9x45
  · exact case9x46
  · exact case9x47
  · exact case9x48
  · exact case9x49
  · exact case9x50
  · exact case9x51
  · exact case9x52


end PEqualNP.Outside.L_meta_1417

open PEqualNP.Outside.L_meta_1417

theorem PEqualNP.Outside.L_meta_1417 : ∀ T ∈ ({0xe8808080, 0xa8888880, 0xa888a080, 0xe8808880, 0xe888a000, 0xa8888888, 0xa888a880, 0xa8a8a800, 0xe880a880, 0xe8888880} : Finset ℕ), ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (o : ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ i j : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) → (∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, o⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0)) → ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (o' : ℕ), (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧ gates'.length ≤ gates.length ∧ ∀ x : Fin 5 → Bool, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = Nat.testBit T (∑ i : Fin 5, if x i then 2 ^ (i : ℕ) else 0) := by
  intro t ht gs o hb _ hv
  by_cases hn : ∃ g ∈ gs, g.op = .not
  · have basis : Basis gs := by
      intro g hg
      simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hb g hg
    change upper t gs.length
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact resolve_row upper0 excluded0 basis hn hv
    · exact resolve_row upper1 excluded1 basis hn hv
    · exact resolve_row upper2 excluded2 basis hn hv
    · exact resolve_row upper3 excluded3 basis hn hv
    · exact resolve_row upper4 excluded4 basis hn hv
    · exact resolve_row upper5 excluded5 basis hn hv
    · exact resolve_row upper6 excluded6 basis hn hv
    · exact resolve_row upper7 excluded7 basis hn hv
    · exact resolve_row upper8 excluded8 basis hn hv
    · exact resolve_row upper9 excluded9 basis hn hv
  · refine ⟨gs,o, ?_, le_rfl, hv⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := hb g hg
    exact ⟨hop.imp_right (fun h => h.resolve_right (fun hnot => hn ⟨g,hg,hnot⟩)), hlen⟩
