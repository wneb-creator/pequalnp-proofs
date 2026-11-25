import PEqualNP.Defs

-- Adapted from odinfree, PR 16697, brilliant-hq/pequalnp-proofs, Apache-2.0.
namespace PEqualNP.Outside.L_meta_12087_aux
open PEqualNP.CircuitLowerBounds
abbrev Row := Fin 128
abbrev Wire := Row → Bool
def bin (d a b : Nat) : Nat :=
  match d with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)
def flipOp (d : Nat) : Nat :=
  match d with
  | 2 => 3
  | 3 => 2
  | _ => d
lemma bin_comm_flip (d : Nat) (hd : d < 4) (a b : Nat) : bin d a b = bin (flipOp d) b a := by
  interval_cases d <;> simp [bin, flipOp, Nat.and_comm, Nat.or_comm]
lemma flipOp_lt {d : Nat} (hd : d < 4) : flipOp d < 4 := by
  interval_cases d <;> decide
lemma testBit_bin (d a b r : Nat) :
    (bin d a b).testBit r =
      match d with
      | 0 => a.testBit r && b.testBit r
      | 1 => a.testBit r || b.testBit r
      | 2 => a.testBit r && !b.testBit r
      | _ => !a.testBit r && b.testBit r := by
  rcases d with _ | _ | _ | d <;>
    simp [bin, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit r <;> cases b.testBit r <;> rfl
lemma bin_lt (d a b : Nat) (ha : a < 2^128) (hb : b < 2^128) : bin d a b < 2^128 := by
  have h1 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x &&& y) < 2^128 := fun x y hx _ =>
    Nat.lt_of_le_of_lt Nat.and_le_left hx
  have h2 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x ||| y) < 2^128 := fun x y hx hy =>
    Nat.or_lt_two_pow hx hy
  have h3 : ∀ x y : Nat, x < 2^128 → y < 2^128 → (x ^^^ y) < 2^128 := fun x y hx hy =>
    Nat.xor_lt_two_pow hx hy
  rcases d with _ | _ | _ | d
  · exact h1 a b ha hb
  · exact h2 a b ha hb
  · exact h3 a (a &&& b) ha (h1 a b ha hb)
  · exact h3 b (a &&& b) hb (h1 a b ha hb)
lemma bin_bit0 (d a b : Nat) (ha : a.testBit 0 = false) (hb : b.testBit 0 = false) :
    (bin d a b).testBit 0 = false := by
  rw [testBit_bin]
  rcases d with _ | _ | _ | d <;> simp [ha, hb]
def Live (T : Nat) : Nat → Finset Nat → Prop
  | 0, S => S = {T} ∧ T ≠ 0
  | k + 1, S => ∃ (U : Finset Nat) (a b d : Nat),
      d < 4 ∧ S = insert a (insert b U) ∧ a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live T k (insert (bin d a b) U)
lemma live_nonzero {T k S} (h : Live T k S) : ∀ a ∈ S, a ≠ 0 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, hT⟩ := h; simpa using hT
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, ha, hb, _, _, tail⟩ := h
    intro x hx
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact ha
    rcases Finset.mem_insert.mp hx with rfl | hx
    · exact hb
    exact ih tail x (Finset.mem_insert_of_mem hx)
lemma live_size {T k S} (h : Live T k S) : S.card ≤ k + 1 := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; simp
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, hf, tail⟩ := h
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    have ht := ih tail
    rw [Finset.card_insert_of_notMem hu] at ht
    have h1 := Finset.card_insert_le a (insert b U)
    have h2 := Finset.card_insert_le b U
    omega
lemma live_sep {T k S} (h : Live T k S) {r s : Nat} (hd : T.testBit r ≠ T.testBit s) :
    ∃ a ∈ S, a.testBit r ≠ a.testBit s := by
  induction k generalizing S with
  | zero => obtain ⟨rfl, _⟩ := h; exact ⟨T, by simp, hd⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, _, rfl, _, _, _, _, tail⟩ := h
    obtain ⟨v, hv, hvd⟩ := ih tail
    rcases Finset.mem_insert.mp hv with rfl | hv
    · by_cases ha : a.testBit r = a.testBit s
      · refine ⟨b, by simp, fun hb => hvd ?_⟩
        rw [testBit_bin, testBit_bin, ha, hb]
      · exact ⟨a, by simp, ha⟩
    · exact ⟨v, Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hv), hvd⟩
abbrev SWire := Bool × Nat
def swZero : SWire := (false, 0)
def swFlip (a : SWire) : SWire := (!a.1, a.2)
def opIdx (s t : Bool) : Nat := if s then (if t then 1 else 3) else (if t then 2 else 0)
def swMeet (a b : SWire) : SWire := (a.1 && b.1, bin (opIdx a.1 b.1) a.2 b.2)
def swJoin (a b : SWire) : SWire := swFlip (swMeet (swFlip a) (swFlip b))
def swRead (j : Nat) (a : SWire) : Bool := a.1 != a.2.testBit j
lemma swRead_zero (j : Nat) : swRead j swZero = false := by simp [swRead, swZero]
lemma swRead_flip (j : Nat) (a : SWire) : swRead j (swFlip a) = !(swRead j a) := by
  cases a with | mk s v => cases s <;> cases h : v.testBit j <;> simp [swRead, swFlip, h]
lemma swRead_meet (j : Nat) (a b : SWire) : swRead j (swMeet a b) = (swRead j a && swRead j b) := by
  obtain ⟨s, u⟩ := a; obtain ⟨t, v⟩ := b
  cases s <;> cases t <;> cases hu : u.testBit j <;> cases hv : v.testBit j <;>
    simp [swRead, swMeet, opIdx, testBit_bin, hu, hv]
lemma swRead_join (j : Nat) (a b : SWire) : swRead j (swJoin a b) = (swRead j a || swRead j b) := by
  simp only [swJoin, swRead_flip, swRead_meet]
  cases swRead j a <;> cases swRead j b <;> rfl
def swGate (w : List SWire) (g : Gate) : SWire :=
  let arg := fun i => w.getD i swZero
  match g.op, g.inputs with
  | .not, xs => swFlip (arg (xs.headD w.length))
  | .and, [] => swFlip swZero
  | .or, [] => swZero
  | .and, [i] | .or, [i] => arg i
  | .and, i :: j :: _ => swMeet (arg i) (arg j)
  | .or, i :: j :: _ => swJoin (arg i) (arg j)
  | _, _ => swZero
def swExec (gs : List Gate) (w : List SWire) : List SWire :=
  gs.foldl (fun w g => w ++ [swGate w g]) w
def isBin (g : Gate) : Bool := match g.op with | .not => false | _ => true
def reps (w : List SWire) : List Nat := w.map Prod.snd
def simple (w : List SWire) (z : Nat) : Prop := z = 0 ∨ z ∈ reps w
def priced (w : List SWire) (paid : Bool) (z : Nat) : Prop :=
  simple w z ∨ (paid = true ∧ ∃ d < 4, ∃ a ∈ reps w, ∃ b ∈ reps w, a ≠ 0 ∧ b ≠ 0 ∧ a ≠ b ∧ z = bin d a b)
lemma bin_eq_cases (d a b : Nat) (hd : d < 4) (h : a = 0 ∨ b = 0 ∨ a = b) :
    bin d a b = 0 ∨ bin d a b = a ∨ bin d a b = b := by
  rcases h with rfl | rfl | rfl <;> interval_cases d <;> simp [bin]
lemma opIdx_lt (s t : Bool) : opIdx s t < 4 := by cases s <;> cases t <;> decide
lemma get_simple (w : List SWire) (i : Nat) : simple w (w.getD i swZero).2 := by
  simp only [List.getD_eq_getElem?_getD]
  cases eq : w[i]? with
  | none => exact Or.inl rfl
  | some a => exact Or.inr (List.mem_map.mpr ⟨a, List.mem_of_getElem? eq, rfl⟩)
lemma made_priced (w : List SWire) (d : Nat) (a b : SWire) (hd : d < 4)
    (pa : simple w a.2) (pb : simple w b.2) : priced w true (bin d a.2 b.2) := by
  by_cases h : a.2 = 0 ∨ b.2 = 0 ∨ a.2 = b.2
  · rcases bin_eq_cases d a.2 b.2 hd h with e | e | e
    · exact Or.inl (Or.inl e)
    · rw [e]; exact Or.inl pa
    · rw [e]; exact Or.inl pb
  · push Not at h
    exact Or.inr ⟨rfl, d, hd, a.2, pa.resolve_left h.1, b.2, pb.resolve_left h.2.1, h.1, h.2.1, h.2.2, rfl⟩
lemma swGate_priced (w : List SWire) (g : Gate) : priced w (isBin g) (swGate w g).2 := by
  obtain ⟨op, xs⟩ := g
  cases op with
  | and =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made_priced w _ _ _ (opIdx_lt _ _) (get_simple w i) (get_simple w j)
  | or =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact Or.inl (Or.inl rfl)
    · exact Or.inl (get_simple w i)
    · exact made_priced w _ _ _ (opIdx_lt _ _) (get_simple w i) (get_simple w j)
  | not => exact Or.inl (get_simple w _)
  | _ => exact Or.inl (Or.inl rfl)
lemma swGate_lt (w : List SWire) (hw : ∀ u ∈ w, u.2 < 2^128 ∧ u.2.testBit 0 = false) (g : Gate) :
    (swGate w g).2 < 2^128 ∧ (swGate w g).2.testBit 0 = false := by
  have hz : (0 : Nat) < 2^128 ∧ (0 : Nat).testBit 0 = false := ⟨by decide, by decide⟩
  have hg (i : Nat) : (w.getD i swZero).2 < 2^128 ∧ (w.getD i swZero).2.testBit 0 = false := by
    simp only [List.getD_eq_getElem?_getD]
    cases eq : w[i]? with
    | none => exact hz
    | some a => exact hw a (List.mem_of_getElem? eq)
  obtain ⟨op, xs⟩ := g
  cases op with
  | and =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact hz
    · exact hg i
    · exact ⟨bin_lt _ _ _ (hg i).1 (hg j).1, bin_bit0 _ _ _ (hg i).2 (hg j).2⟩
  | or =>
    rcases xs with _ | ⟨i, _ | ⟨j, t⟩⟩
    · exact hz
    · exact hg i
    · exact ⟨bin_lt _ _ _ (hg i).1 (hg j).1, bin_bit0 _ _ _ (hg i).2 (hg j).2⟩
  | not => exact hg (xs.headD w.length)
  | _ => exact hz
lemma swExec_lt (gs : List Gate) (w : List SWire)
    (hw : ∀ u ∈ w, u.2 < 2^128 ∧ u.2.testBit 0 = false) :
    ∀ u ∈ swExec gs w, u.2 < 2^128 ∧ u.2.testBit 0 = false := by
  induction gs generalizing w with
  | nil => exact hw
  | cons g gs ih =>
    apply ih
    intro u hu
    rcases List.mem_append.mp hu with hu | hu
    · exact hw u hu
    · rw [List.mem_singleton.mp hu]; exact swGate_lt w hw g
lemma swRead_get (j : Nat) (w : List SWire) (i : Nat) :
    (w.map (swRead j)).getD i false = swRead j (w.getD i swZero) := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w[i]? <;> simp [swRead_zero]
lemma swGate_read (w : List SWire) (g : Gate)
    (legal : (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) (j : Nat) :
    swRead j (swGate w g) = g.op.eval (g.inputs.map fun i => (w.map (swRead j)).getD i false) := by
  simp_rw [swRead_get]
  obtain ⟨op, xs⟩ := g
  obtain ⟨hop, hlen⟩ := legal
  rcases hop with rfl | rfl | rfl <;>
    rcases xs with _ | ⟨i, _ | ⟨k, _ | ⟨h, rest⟩⟩⟩ <;>
    simp_all [swGate, GateOp.eval, swRead_flip, swRead_meet, swRead_join, swRead_zero]
lemma swExec_read (j : Nat) (gs : List Gate) (w : List SWire)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2) :
    (swExec gs w).map (swRead j) =
      gs.foldl (fun l g => l ++ [g.op.eval (g.inputs.map fun i => l.getD i false)]) (w.map (swRead j)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (swExec gs (w ++ [swGate w g])).map (swRead j) = _
    rw [ih _ (fun v hv => legal v (List.mem_cons_of_mem _ hv))]
    simp [swGate_read w g (legal g List.mem_cons_self) j]
lemma pull_live {T k S w z p} (h : Live T k S) (op : priced w p z)
    (sub : ∀ a ∈ S, a ∈ reps w ++ [z]) :
    ∃ l V, l ≤ k + p.toNat ∧ Live T l V ∧ ∀ a ∈ V, a ∈ reps w := by
  by_cases needed : z ∈ S
  · by_cases avail : z ∈ reps w
    · refine ⟨k, S, by omega, h, fun a ha => ?_⟩
      rcases (by simpa using sub a ha : a ∈ reps w ∨ a = z) with old | rfl
      · exact old
      · exact avail
    · rcases op with easy | ⟨rfl, d, hd, a, ha, b, hb, na, nb, ab, rfl⟩
      · rcases easy with rfl | hm
        · exact (live_nonzero h 0 needed rfl).elim
        · exact (avail hm).elim
      · let U := S.erase (bin d a b)
        have tail : Live T k (insert (bin d a b) U) := by
          simpa [U, Finset.insert_erase needed] using h
        have old (x : Nat) (hx : x ∈ U) : x ∈ reps w := by
          obtain ⟨ne, mem⟩ := Finset.mem_erase.mp hx
          exact (by simpa using sub x mem : x ∈ reps w ∨ x = bin d a b).resolve_right ne
        have fresh : bin d a b ∉ insert a (insert b U) := by
          intro eq
          rcases Finset.mem_insert.mp eq with e | h'
          · exact avail (e.symm ▸ ha)
          rcases Finset.mem_insert.mp h' with e | u
          · exact avail (e.symm ▸ hb)
          · exact avail (old _ u)
        exact ⟨k + 1, insert a (insert b U), by simp,
          ⟨U, a, b, d, hd, rfl, na, nb, ab, fresh, tail⟩, by simpa using And.intro ha (And.intro hb old)⟩
  · exact ⟨k, S, by omega, h, fun a ha => (by simpa [show a ≠ z from fun e => needed (e ▸ ha)] using sub a ha)⟩
lemma extract_live {T} (hT : T ≠ 0) (gs : List Gate) (w : List SWire)
    (found : T ∈ reps (swExec gs w)) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ reps w := by
  induction gs generalizing w with
  | nil => exact ⟨0, {T}, by simp, ⟨rfl, hT⟩, by simpa [swExec] using found⟩
  | cons g gs ih =>
    obtain ⟨k, S, lim, h, sub⟩ := ih (w ++ [swGate w g]) found
    have sub' : ∀ a ∈ S, a ∈ reps w ++ [(swGate w g).2] := by simpa [reps] using sub
    obtain ⟨l, V, cost, hl, raw⟩ := pull_live h (swGate_priced w g) sub'
    refine ⟨l, V, ?_, hl, raw⟩
    rw [List.countP_cons]
    cases e : isBin g <;> simp [e] at cost ⊢ <;> omega
def invW (a : Wire) : Wire := fun r => !(a r)
def comb2 (isOr : Bool) (a b : Wire) : Wire :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb4 (d : Nat) (a b : Wire) : Wire :=
  match d with
  | 0 => comb2 false a b
  | 1 => comb2 true a b
  | 2 => comb2 false a (invW b)
  | _ => comb2 false (invW a) b
def Constant (a : Wire) : Prop := ∃ b : Bool, a = fun _ => b
noncomputable def wcost (a : Wire) : Nat := by classical exact if Constant a then 1 else 0
noncomputable def wmass (xs : List Wire) : Nat := (xs.map wcost).sum
def Avail (pool : List Wire) (v : Wire) : Prop := v ∈ pool ∨ Constant v ∨ invW v ∈ pool
def Supply (pool xs : List Wire) : Prop := ∀ a ∈ xs, Avail pool a
def Reach (roots : List Wire) : Nat → List Wire → Prop
  | 0, b => b = roots
  | p + 1, c => ∃ (op : Bool) (bank : List Wire) (a b : Wire),
      Reach roots p bank ∧ Avail bank a ∧ Avail bank b ∧ c = comb2 op a b :: bank
def kept {α : Type} (save : Bool) (x : α) (xs : List α) : List α := if save then x :: xs else xs
def Run (goal : Wire) : Nat → List Wire → Prop
  | 0, zs => List.Perm [goal] zs
  | s + 1, zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire) (rest : List Wire),
      op < 4 ∧ (a :: b :: rest).Perm zs ∧ Run goal s (comb4 op a b :: kept ka a (kept kb b rest))
lemma invW_inv (a : Wire) : invW (invW a) = a := by funext r; simp [invW]
lemma invW_const {a : Wire} (h : Constant a) : Constant (invW a) := by
  obtain ⟨v, rfl⟩ := h; exact ⟨!v, rfl⟩
lemma wcost_inv (a : Wire) : wcost (invW a) = wcost a := by
  have h : Constant (invW a) ↔ Constant a := ⟨fun hc => invW_inv a ▸ invW_const hc, invW_const⟩
  by_cases hc : Constant a
  · simp [wcost, hc, h.mpr hc]
  · simp [wcost, hc, mt h.mp hc]
lemma avail_inv {bank : List Wire} {a : Wire} (h : Avail bank a) : Avail bank (invW a) := by
  rcases h with h | h | h
  · exact Or.inr (Or.inr (by rwa [invW_inv]))
  · exact Or.inr (Or.inl (invW_const h))
  · exact Or.inl h
lemma avail_cons {bank : List Wire} {v : Wire} (w : Wire) (h : Avail bank v) : Avail (w :: bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (List.mem_cons_of_mem _))
lemma from_const (op : Bool) {a b : Wire} {bank : List Wire} (h : Constant a ∨ Constant b)
    (ha : Avail bank a) (hb : Avail bank b) : Avail bank (comb2 op a b) := by
  rcases h with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> cases op <;> cases v
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using hb
  · simpa [comb2] using hb
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
  · exact Or.inr (Or.inl ⟨false, funext fun _ => by simp [comb2]⟩)
  · simpa [comb2] using ha
  · simpa [comb2] using ha
  · exact Or.inr (Or.inl ⟨true, funext fun _ => by simp [comb2]⟩)
lemma both_const (op : Bool) {a b : Wire} (ha : Constant a) (hb : Constant b) :
    Constant (comb2 op a b) := by
  obtain ⟨v, rfl⟩ := ha; obtain ⟨w, rfl⟩ := hb; cases op <;> exact ⟨_, rfl⟩
lemma extend_comb (roots : List Wire) {p bank a b} (d : Nat) (hd : d < 4)
    (hp : Reach roots p bank) (ha : Avail bank a) (hb : Avail bank b) :
    ∃ q next, Reach roots q next ∧ Avail next (comb4 d a b) ∧
      (∀ v, Avail bank v → Avail next v) ∧ q + wcost a + wcost b ≤ p + 1 + wcost (comb4 d a b) := by
  have hprep : ∃ op x y, comb4 d a b = comb2 op x y ∧ Avail bank x ∧ Avail bank y ∧
      wcost x = wcost a ∧ wcost y = wcost b := by
    interval_cases d
    · exact ⟨false, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨true, a, b, rfl, ha, hb, rfl, rfl⟩
    · exact ⟨false, a, invW b, rfl, ha, avail_inv hb, rfl, wcost_inv b⟩
    · exact ⟨false, invW a, b, rfl, avail_inv ha, hb, wcost_inv a, rfl⟩
  obtain ⟨op, x, y, eq, hx, hy, cx, cy⟩ := hprep
  rw [eq, ← cx, ← cy]
  classical
  by_cases c : Constant x ∨ Constant y
  · refine ⟨p, bank, hp, from_const op c hx hy, fun _ h => h, ?_⟩
    by_cases hcx : Constant x <;> by_cases hcy : Constant y
    · simp [wcost, hcx, hcy, both_const op hcx hcy]
    · simp [wcost, hcx, hcy]
    · simp [wcost, hcx, hcy]
    · exact (c.elim hcx hcy).elim
  · have hcx : ¬Constant x := fun h => c (Or.inl h)
    have hcy : ¬Constant y := fun h => c (Or.inr h)
    exact ⟨p + 1, _, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, Or.inl (by simp),
      fun _ h => avail_cons _ h, by simp [wcost, hcx, hcy]⟩
lemma wmass_kept (a : Wire) (xs : List Wire) (k : Bool) : wmass xs ≤ wmass (kept k a xs) := by
  cases k <;> simp [kept, wmass]
lemma contraction {goal : Wire} (nc : ¬Constant goal) {s ws} (h : Run goal s ws)
    (roots : List Wire) {p bank} (hp : Reach roots p bank) (hs : Supply bank ws) :
    ∃ q next, Reach roots q next ∧ Avail next goal ∧ q + wmass ws ≤ p + s := by
  classical
  induction s generalizing ws p bank with
  | zero =>
    have hmem : goal ∈ ws := h.mem_iff.mp (by simp)
    have hlen : wmass ws = wcost goal := by
      have := (h.map wcost).sum_eq
      simpa [wmass] using this.symm
    exact ⟨p, bank, hp, hs goal hmem, by simp [hlen, wcost, nc]⟩
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have hsa : Avail bank a := hs a (perm.mem_iff.mp (by simp))
    have hsb : Avail bank b := hs b (perm.mem_iff.mp (by simp))
    obtain ⟨r, T, hT, hz, inc, le⟩ := extend_comb roots op hd hp hsa hsb
    have ht : Supply T (comb4 op a b :: kept ka a (kept kb b rest)) := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact hz
      · apply inc; apply hs; apply perm.mem_iff.mp
        cases ka <;> cases kb <;> simp [kept] at hv ⊢ <;> tauto
    obtain ⟨q, W, hW, hv, hl⟩ := ih tail hT ht
    have hm1 := wmass_kept a (kept kb b rest) ka
    have hm2 := wmass_kept b rest kb
    have hp_eq : wmass ws = wcost a + wcost b + wmass rest := by
      have := (perm.map wcost).sum_eq
      simpa [wmass, Nat.add_assoc] using this.symm
    have hcons : wmass (comb4 op a b :: kept ka a (kept kb b rest)) =
        wcost (comb4 op a b) + wmass (kept ka a (kept kb b rest)) := rfl
    rw [hcons] at hl
    exact ⟨q, W, hW, hv, by omega⟩
def restrictW (f : Row → Row) (a : Wire) : Wire := fun r => a (f r)
lemma restrict_run (f : Row → Row) {goal s ws} (h : Run goal s ws) :
    Run (restrictW f goal) s (ws.map (restrictW f)) := by
  induction s generalizing ws with
  | zero => exact h.map _
  | succ s ih =>
    obtain ⟨op, ka, kb, a, b, rest, hd, perm, tail⟩ := h
    have htail := ih tail
    have hk : ∀ (k : Bool) (x : Wire) (l : List Wire),
        (kept k x l).map (restrictW f) = kept k (restrictW f x) (l.map (restrictW f)) := by
      intro k x l; cases k <;> rfl
    have hc : restrictW f (comb4 op a b) = comb4 op (restrictW f a) (restrictW f b) := by
      funext r; rcases op with _ | _ | _ | op <;> rfl
    simp only [List.map_cons, hk, hc] at htail
    exact ⟨op, ka, kb, restrictW f a, restrictW f b, rest.map (restrictW f), hd,
      by simpa using perm.map (restrictW f), htail⟩
def obs (a : Nat) : Wire := fun r => a.testBit r.val
lemma obs_bin (d a b : Nat) : obs (bin d a b) = comb4 d (obs a) (obs b) := by
  funext r
  simp only [obs, testBit_bin, comb4, comb2, invW]
  rcases d with _ | _ | _ | d <;> rfl
lemma kept_nodup {α : Type} (c : Bool) (x : α) (l : List α) (hl : l.Nodup) (hx : x ∉ l) :
    (kept c x l).Nodup := by
  cases c <;> simp [kept, hl, hx]
lemma live_to_run {T k S} (h : Live T k S) (v : List Nat) (nd : v.Nodup) (eqv : v.toFinset = S) :
    Run (obs T) k (v.map obs) := by
  classical
  induction k generalizing S v with
  | zero =>
    obtain ⟨rfl, _⟩ := h
    have hp : [T].Perm v := List.perm_of_nodup_nodup_toFinset_eq (by simp) nd (by simp [eqv])
    exact hp.map obs
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, _, _, hab, fresh, tail⟩ := h
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tl := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm : mid.Nodup := kept_nodup kb b rest hr br
    have am : a ∉ mid := by cases hkb : kb <;> simp [mid, kept, hkb, hab, ar]
    have ntl : tl.Nodup := kept_nodup ka a mid bm am
    have htl : tl.toFinset = U := by
      have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
        cases c <;> simp [kept]
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kf, kf, er]
      ext j
      by_cases ha' : a ∈ U <;> by_cases hb' : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;>
        simp_all [ka, kb]
    have hf : bin d a b ∉ tl := fun hm =>
      fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (htl ▸ List.mem_toFinset.mpr hm)))
    have prog := ih tail (bin d a b :: tl) (List.nodup_cons.mpr ⟨hf, ntl⟩) (by simp [htl])
    have hk : ∀ (c : Bool) (x : Nat) (l : List Nat), (kept c x l).map obs = kept c (obs x) (l.map obs) := by
      intro c x l; cases c <;> rfl
    change Run (obs T) k ((bin d a b :: kept ka a (kept kb b rest)).map obs) at prog
    rw [List.map_cons, hk, hk, obs_bin] at prog
    have perm : (a :: b :: rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab, ar, br, hr]) nd
      ext j
      by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all
    exact ⟨d, ka, kb, obs a, obs b, rest.map obs, hd, by simpa using perm.map obs, prog⟩
def normPack (f : Wire) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).toNat
lemma normPack_lt (f : Wire) : normPack f < 2^128 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).isLt
lemma testBit_normPack (f : Wire) (r : Nat) :
    (normPack f).testBit r = if h : r < 128 then (f ⟨r, h⟩ != f 0) else false := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => f r != f 0))).cast List.length_ofFn).getLsbD r = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  by_cases h : r < 128 <;> simp [h]
lemma normPack_eq_of_obs {a : Nat} (ha : a < 2^128) (h0 : a.testBit 0 = false) :
    normPack (obs a) = a := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 128
  · simp [hr, obs, h0]
  · simp only [hr, dite_false]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma normPack_inv (f : Wire) : normPack (invW f) = normPack f := by
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_normPack]
  by_cases hr : r < 128
  · simp only [hr, dite_true, invW]
    cases f ⟨r, hr⟩ <;> cases f 0 <;> rfl
  · simp [hr]
lemma normPack_const {f : Wire} (h : Constant f) : normPack f = 0 := by
  obtain ⟨b, rfl⟩ := h
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack]
  by_cases hr : r < 128 <;> simp [hr]
lemma normPack_comb2 (op : Bool) (a b : Wire) :
    ∃ d < 4, normPack (comb2 op a b) = bin d (normPack a) (normPack b) := by
  refine ⟨opIdx (if op then !(a 0) else a 0) (if op then !(b 0) else b 0), opIdx_lt _ _, ?_⟩
  apply Nat.eq_of_testBit_eq
  intro r
  rw [testBit_normPack, testBit_bin, testBit_normPack, testBit_normPack]
  by_cases hr : r < 128
  · simp only [hr, dite_true]
    cases op <;> cases ha0 : a 0 <;> cases hb0 : b 0 <;>
      cases har : a ⟨r, hr⟩ <;> cases hbr : b ⟨r, hr⟩ <;>
      simp [comb2, opIdx, ha0, hb0, har, hbr]
  · simp only [hr, dite_false]
    rcases opIdx _ _ with _ | _ | _ | d <;> rfl
lemma avail_normPack {bank : List Wire} {v : Wire} (h : Avail bank v) :
    normPack v = 0 ∨ normPack v ∈ bank.map normPack := by
  rcases h with hm | hc | hi
  · exact Or.inr (List.mem_map_of_mem hm)
  · exact Or.inl (normPack_const hc)
  · exact Or.inr (by rw [← normPack_inv v]; exact List.mem_map_of_mem hi)
lemma reach_to_live_sub {roots : List Wire} {p bank} (h : Reach roots p bank)
    {T k S} (run : Live T k S) (sub : ∀ a ∈ S, a ∈ bank.map normPack) :
    ∃ l V, l ≤ p + k ∧ Live T l V ∧ ∀ a ∈ V, a ∈ roots.map normPack := by
  induction p generalizing bank k S with
  | zero =>
    rcases h with rfl
    exact ⟨k, S, by omega, run, sub⟩
  | succ p ih =>
    obtain ⟨op, prev, a, b, hr, ha, hb, rfl⟩ := h
    obtain ⟨d, hd, eq⟩ := normPack_comb2 op a b
    let w := prev.map (fun f => (false, normPack f))
    have hreps : reps w = prev.map normPack := by simp [w, reps, List.map_map, Function.comp_def]
    have hp : priced w true (normPack (comb2 op a b)) := by
      rw [eq]
      exact made_priced w d (false, normPack a) (false, normPack b) hd
        (by simpa [simple, hreps] using avail_normPack ha)
        (by simpa [simple, hreps] using avail_normPack hb)
    have hsub' : ∀ x ∈ S, x ∈ reps w ++ [normPack (comb2 op a b)] := by
      intro x hx
      rcases List.mem_cons.mp (sub x hx) with rfl | hm
      · simp
      · simp [hreps, hm]
    obtain ⟨k', S', hk', run', sub'⟩ := pull_live run hp hsub'
    obtain ⟨l, V, hl, run'', sub''⟩ := ih hr run' (by simpa [hreps] using sub')
    simp only [Bool.toNat_true] at hk'
    exact ⟨l, V, by omega, run'', sub''⟩
def Lower (roots : List Nat) (T : Nat) (L : Nat) : Prop :=
  ∀ p bank, Reach (roots.map obs) p bank → Avail bank (obs T) → L ≤ p
def Impossible (T : Nat) (cap : Nat) (S : Finset Nat) : Prop :=
  ∀ k ≤ cap, ¬Live T k S
def Essential (T : Nat) (roots : List Nat) (a : Nat) : Prop :=
  ∃ r s : Row, T.testBit r.val ≠ T.testBit s.val ∧ ∀ v ∈ roots, v ≠ a → v.testBit r.val = v.testBit s.val
lemma raw_required {T k S} (h : Live T k S) (roots : List Nat) (a : Nat)
    (sub : ∀ v ∈ S, v ∈ roots) (he : Essential T roots a) : a ∈ S := by
  obtain ⟨r, s, hd, hiso⟩ := he
  obtain ⟨v, hv, hvd⟩ := live_sep h hd
  by_cases veq : v = a
  · exact veq ▸ hv
  · exact (hvd (hiso v (sub v hv) veq)).elim
lemma lower_of_impossible {roots : List Nat} {T L : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
    (ess : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible T L roots.toFinset) : Lower roots T (L + 1) := by
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hnz : normPack (obs T) ≠ 0 := by rwa [hnormT]
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left hnz
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]
    conv_rhs => rw [← List.map_id roots]
    apply List.map_congr_left
    intro a ha'
    exact normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have heq : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    exact ⟨fun ha' => raw_required run roots a sub (ess a ha'), sub a⟩
  by_contra! small
  exact noRun k (by omega) (heq.symm ▸ run)
lemma obs_not_const {T : Nat} (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false) :
    ¬Constant (obs T) := by
  intro hc
  have h := normPack_const hc
  rw [normPack_eq_of_obs hTlt hTb0] at h
  exact hT0 h
def Slice (raw : List Nat) (T d : Nat) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Nat),
    (∀ r : Row, d.testBit (f r).val = true) ∧
    (∀ a ∈ raw, Avail (roots.map obs) (restrictW f (obs a))) ∧
    ¬Constant (restrictW f (obs T)) ∧
    ∀ p bank, Reach (roots.map obs) p bank → Avail bank (restrictW f (obs T)) → L ≤ p
def isConstM (d a : Nat) : Bool := (a &&& d == 0) || (a &&& d == d)
def availM (d : Nat) (pm : List Nat) (a : Nat) : Bool :=
  let m := a &&& d
  m == 0 || m == d || pm.contains m || pm.contains (d ^^^ m)
lemma masked_eq_obs {f : Row → Row} {d a b : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = (b &&& d)) : restrictW f (obs a) = restrictW f (obs b) := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_zero_obs {f : Row → Row} {d a : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = 0) : restrictW f (obs a) = fun _ => false := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_one_obs {f : Row → Row} {d a : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = d) : restrictW f (obs a) = fun _ => true := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simpa [restrictW, obs, Nat.testBit_and, dom r] using h
lemma masked_comp_obs {f : Row → Row} {d a b : Nat} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (eq : (a &&& d) = (d ^^^ (b &&& d))) : restrictW f (obs a) = invW (restrictW f (obs b)) := by
  funext r
  have h := congrArg (fun x => x.testBit (f r).val) eq
  simp only [Nat.testBit_and, Nat.testBit_xor, dom r, Bool.and_true] at h
  simp only [restrictW, obs, invW, h]
  cases b.testBit (f r).val <;> rfl
def poolSupply (f : Row → Row) (bank : List Wire) (pool : List Nat) : Prop :=
  ∀ a ∈ pool, Avail bank (restrictW f (obs a))
lemma availM_sound {f : Row → Row} {d a : Nat} {bank : List Wire} {pool : List Nat}
    (dom : ∀ r : Row, d.testBit (f r).val = true)
    (hs : poolSupply f bank pool)
    (ok : availM d (pool.map (· &&& d)) a = true) :
    Avail bank (restrictW f (obs a)) := by
  simp only [availM, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq, List.mem_map] at ok
  rcases ok with ((h0 | h1) | ⟨v, hv, he⟩) | ⟨v, hv, he⟩
  · exact Or.inr (Or.inl ⟨false, masked_zero_obs dom h0⟩)
  · exact Or.inr (Or.inl ⟨true, masked_one_obs dom h1⟩)
  · exact (masked_eq_obs dom he.symm) ▸ hs v hv
  · have hinv := avail_inv (hs v hv)
    have hcomp : restrictW f (obs a) = invW (restrictW f (obs v)) := by
      have hx : (a &&& d) = d ^^^ (v &&& d) := by
        have := congrArg (d ^^^ ·) he
        simpa [Nat.xor_assoc, Nat.xor_comm, Nat.xor_self] using this.symm
      exact masked_comp_obs dom hx
    exact hcomp ▸ hinv
abbrev Choice := Nat × Nat × Nat
def choiceVal (c : Choice) : Nat := bin c.1 c.2.1 c.2.2
def choiceOK (d : Nat) (pm : List Nat) (c : Choice) : Bool :=
  decide (c.1 < 4) && availM d pm c.2.1 && availM d pm c.2.2
def makePool (d : Nat) (pool : List Nat) : List Choice → Option (List Nat)
  | [] => some pool
  | c :: cs => if choiceOK d (pool.map (· &&& d)) c then makePool d (choiceVal c :: pool) cs else none
lemma pay_choice {f : Row → Row} {d : Nat} {roots bank q} {pool : List Nat}
    (dom : ∀ r : Row, d.testBit (f r).val = true)
    (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (c : Choice) (valid : choiceOK d (pool.map (· &&& d)) c = true) :
    ∃ next, Reach roots (q + 1) next ∧ poolSupply f next (choiceVal c :: pool) := by
  simp only [choiceOK, Bool.and_eq_true, decide_eq_true_eq] at valid
  have ha := availM_sound dom hs valid.1.2
  have hb := availM_sound dom hs valid.2
  have hprep : ∃ op x y, comb4 c.1 (restrictW f (obs c.2.1)) (restrictW f (obs c.2.2)) = comb2 op x y ∧
      Avail bank x ∧ Avail bank y := by
    have hd := valid.1.1
    interval_cases c.1
    · exact ⟨false, _, _, rfl, ha, hb⟩
    · exact ⟨true, _, _, rfl, ha, hb⟩
    · exact ⟨false, _, _, rfl, ha, avail_inv hb⟩
    · exact ⟨false, _, _, rfl, avail_inv ha, hb⟩
  obtain ⟨op, x, y, eq, hx, hy⟩ := hprep
  refine ⟨comb2 op x y :: bank, ⟨op, bank, x, y, hp, hx, hy, rfl⟩, fun v hv => ?_⟩
  rcases List.mem_cons.mp hv with rfl | hv
  · have hcv : restrictW f (obs (choiceVal c)) = comb2 op x y := by
      rw [← eq]; funext r; simp only [choiceVal, restrictW, obs, testBit_bin, comb4, comb2, invW]
      rcases c.1 with _ | _ | _ | d' <;> rfl
    exact hcv ▸ Or.inl (by simp)
  · exact avail_cons _ (hs v hv)
lemma makePool_sound {d : Nat} {f : Row → Row} (dom : ∀ r : Row, d.testBit (f r).val = true)
    {roots bank q pool} (hp : Reach roots q bank) (hs : poolSupply f bank pool)
    (cs : List Choice) {res} (ok : makePool d pool cs = some res) :
    ∃ next, Reach roots (q + cs.length) next ∧ poolSupply f next res := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨bank, hp, hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next, hr, sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out, hr', sh'⟩ := ih hr sh ok
      exact ⟨out, by simpa [Nat.add_assoc, Nat.add_comm 1] using hr', sh'⟩
    next => contradiction
lemma count_constM {d : Nat} {f : Row → Row} (dom : ∀ r : Row, d.testBit (f r).val = true)
    (ws : List Nat) : ws.countP (isConstM d) ≤ wmass ((ws.map obs).map (restrictW f)) := by
  classical
  induction ws with
  | nil => simp [wmass]
  | cons a ws ih =>
    simp only [List.countP_cons, List.map_cons, wmass, List.sum_cons] at ih ⊢
    cases h : isConstM d a
    · simp only [Bool.false_eq_true, ite_false, Nat.add_zero]
      exact ih.trans (Nat.le_add_left _ _)
    · have hc : Constant (restrictW f (obs a)) := by
        simp only [isConstM, Bool.or_eq_true, beq_iff_eq] at h
        rcases h with h0 | h1
        · exact ⟨false, masked_zero_obs dom h0⟩
        · exact ⟨true, masked_one_obs dom h1⟩
      simp only [ite_true, wcost, hc]
      omega
structure BoundPool where
  dom : Nat
  lb : Nat
  paid : Nat
  wires : List Nat
  pm : List Nat
def ValidPool (_raw : List Nat) (T : Nat) (c : BoundPool) : Prop :=
  c.pm = c.wires.map (· &&& c.dom) ∧
  ∃ (f : Row → Row) (roots : List Nat) (bank : List Wire),
    (∀ r : Row, c.dom.testBit (f r).val = true) ∧ ¬Constant (restrictW f (obs T)) ∧
    (∀ q ws, Reach (roots.map obs) q ws → Avail ws (restrictW f (obs T)) → c.lb ≤ q) ∧
    Reach (roots.map obs) c.paid bank ∧ poolSupply f bank c.wires
def materialize (raw : List Nat) (cs : List Choice) (d lb : Nat) : Option BoundPool :=
  (makePool d raw cs).map fun pool => ⟨d, lb, cs.length, pool, pool.map (· &&& d)⟩
lemma materialize_sound {raw T d L cs c} (sl : Slice raw T d L)
    (h : materialize raw cs d L = some c) : ValidPool raw T c := by
  unfold materialize at h
  cases he : makePool d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he, Option.map_some, Option.some.injEq] at h
    subst c
    obtain ⟨f, roots, dom, base, nc, lo⟩ := sl
    obtain ⟨bank, hr, hs⟩ := makePool_sound dom (show Reach (roots.map obs) 0 (roots.map obs) from rfl) base cs he
    exact ⟨rfl, f, roots, bank, dom, nc, lo, by simpa using hr, hs⟩
def scalarPoolCut (c : BoundPool) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let z := choiceVal op
  let extra := !(availM c.dom c.pm z)
  decide (k + c.paid + extra.toNat < c.lb + (z :: rest).countP (isConstM c.dom)) &&
    rest.all (availM c.dom c.pm) && (!extra || choiceOK c.dom c.pm op)
lemma scalarPoolCut_sound {raw T c} (valid : ValidPool raw T c) {k rest op}
    (nd : (choiceVal op :: rest).Nodup) (cut : scalarPoolCut c k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  obtain ⟨hpm, f, roots, bank, dom, nc, lo, hp, hs⟩ := valid
  simp only [scalarPoolCut, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true] at cut
  intro t ht run
  have finish (n : Nat) (out : List Wire) (hr : Reach (roots.map obs) n out)
      (hsup : poolSupply f out (choiceVal op :: rest))
      (hle : n = c.paid + (!(availM c.dom c.pm (choiceVal op))).toNat) : False := by
    have hcov : Supply out (((choiceVal op :: rest).map obs).map (restrictW f)) := by
      intro v hv
      obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
      exact hsup a ha
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction nc (restrict_run f (live_to_run run (choiceVal op :: rest) nd rfl)) (roots.map obs) hr hcov
    have hlo := lo q next hq hav
    have hcm := count_constM dom (choiceVal op :: rest)
    have hineq := cut.1.1
    omega
  cases hav : availM c.dom c.pm (choiceVal op) with
  | true =>
    apply finish c.paid bank hp _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact availM_sound dom hs (hpm ▸ hav)
    · exact availM_sound dom hs (hpm ▸ cut.1.2 a ha)
  | false =>
    have hok : choiceOK c.dom (c.wires.map (· &&& c.dom)) op = true := by
      have h2 := cut.2
      simp only [hav, Bool.not_false, Bool.not_true, Bool.false_eq_true, false_or] at h2
      exact hpm ▸ h2
    obtain ⟨out, hr, hc⟩ := pay_choice dom hp hs op hok
    apply finish (c.paid + 1) out hr _ (by simp [hav])
    intro a ha
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hc (choiceVal op) (by simp)
    · have hpt : poolSupply f out c.wires := fun v hv => hc v (List.mem_cons_of_mem _ hv)
      exact availM_sound dom hpt (hpm ▸ cut.1.2 a ha)
def fixRow (z o : Nat) (r : Row) : Row :=
  ⟨((r.val &&& (127 ^^^ z)) ||| o) % 128, Nat.mod_lt _ (by decide)⟩
def renameW (f : Row → Row) (a : Nat) : Nat :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).toNat
lemma testBit_renameW (f : Row → Row) (a : Nat) (r : Row) :
    (renameW f a).testBit r.val = a.testBit (f r).val := by
  change ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).getLsbD r.val = _
  simp only [BitVec.getLsbD_cast, BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_ofFn, r.isLt, dite_true, Option.getD_some]
lemma renameW_lt (f : Row → Row) (a : Nat) : renameW f a < 2^128 :=
  ((BitVec.ofBoolListLE (List.ofFn (fun r : Row => a.testBit (f r).val))).cast List.length_ofFn).isLt
lemma obs_renameW (f : Row → Row) (a : Nat) : obs (renameW f a) = restrictW f (obs a) := by
  funext r; exact testBit_renameW f a r
lemma renameW_bin (f : Row → Row) (d a b : Nat) :
    renameW f (bin d a b) = bin d (renameW f a) (renameW f b) := by
  apply Nat.eq_of_testBit_eq
  intro r
  by_cases hr : r < 128
  · rw [testBit_renameW f _ ⟨r, hr⟩, testBit_bin, testBit_bin, testBit_renameW f _ ⟨r, hr⟩, testBit_renameW f _ ⟨r, hr⟩]
  · have hlt (x : Nat) : (renameW f x).testBit r = false :=
      Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f x) (Nat.pow_le_pow_right (by decide) (by omega)))
    rw [hlt, testBit_bin, hlt, hlt]
    rcases d with _ | _ | _ | d <;> rfl
lemma renameW_zero (f : Row → Row) : renameW f 0 = 0 := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · simpa using testBit_renameW f 0 ⟨r, hr⟩
  · rw [Nat.zero_testBit]
    exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt f 0) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 128 ≤ r)))
lemma renameW_inj (f : Row → Row) (onto : Function.Surjective f) {a b : Nat}
    (ha : a < 2^128) (hb : b < 2^128) (eq : renameW f a = renameW f b) : a = b := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · obtain ⟨q, hq⟩ := onto ⟨r, hr⟩
    have h := congrArg (fun x => x.testBit q.val) eq
    rw [testBit_renameW, testBit_renameW, hq] at h
    exact h
  · have hge : 128 ≤ r := by omega
    rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide : 0 < 2) hge)),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide : 0 < 2) hge))]
lemma live_renameW {T k S} (h : Live T k S) (hS : ∀ a ∈ S, a < 2^128) (f : Row → Row)
    (onto : Function.Surjective f) : Live (renameW f T) k (S.image (renameW f)) := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl, hT⟩ := h
    have hTlt : T < 2^128 := hS T (by simp)
    refine ⟨by simp, fun hz => hT (renameW_inj f onto hTlt (by decide) (hz.trans (renameW_zero f).symm))⟩
  | succ k ih =>
    obtain ⟨U, a, b, d, hd, rfl, ha, hb, hab, fresh, tail⟩ := h
    have halt : a < 2^128 := hS a (by simp)
    have hblt : b < 2^128 := hS b (by simp)
    have hUlt : ∀ x ∈ U, x < 2^128 := fun x hx => hS x (by simp [hx])
    have hzlt : bin d a b < 2^128 := bin_lt d a b halt hblt
    have htail_lt : ∀ x ∈ insert (bin d a b) U, x < 2^128 := by
      intro x hx; rcases Finset.mem_insert.mp hx with rfl | hx; exact hzlt; exact hUlt x hx
    have nr := ih tail htail_lt
    simp only [Finset.image_insert, renameW_bin] at nr ⊢
    refine ⟨U.image (renameW f), renameW f a, renameW f b, d, hd, rfl,
      fun hz => ha (renameW_inj f onto halt (by decide) (hz.trans (renameW_zero f).symm)),
      fun hz => hb (renameW_inj f onto hblt (by decide) (hz.trans (renameW_zero f).symm)),
      fun heq => hab (renameW_inj f onto halt hblt heq), ?_, nr⟩
    intro hm
    rw [← renameW_bin] at hm
    rcases Finset.mem_insert.mp hm with heq | hm
    · exact fresh (by rw [renameW_inj f onto hzlt halt heq]; simp)
    rcases Finset.mem_insert.mp hm with heq | hm
    · exact fresh (by rw [renameW_inj f onto hzlt hblt heq]; simp)
    obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hm
    exact fresh (by rw [renameW_inj f onto hzlt (hUlt x hx) heq.symm]; simp [hx])
lemma wmass_append (a b : List Wire) : wmass (a ++ b) = wmass a + wmass b := by simp [wmass]
lemma wmass_consts (xs : List Wire) (hc : ∀ x ∈ xs, Constant x) : wmass xs = xs.length := by
  classical
  induction xs with
  | nil => simp [wmass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [wmass, List.map_cons, List.sum_cons, List.length_cons, wcost, ha, ite_true]
    have := ih (fun x hx => hc x (by simp [hx]))
    simp only [wmass] at this
    omega
lemma lower_slice {roots other : List Nat} {T G : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
    (hG0 : G ≠ 0) (hGlt : G < 2^128) (hGb0 : G.testBit 0 = false)
    (f : Row → Row) (eq : renameW f T = G)
    (covered : ∀ a ∈ roots, Avail (other.map obs) (restrictW f (obs a)))
    (singles : Finset Nat) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (restrictW f (obs a)))
    (L : Nat) (prior : Lower other G L) : Lower roots T (L + singles.card) := by
  classical
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left (by rwa [hnormT])
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]; conv_rhs => rw [← List.map_id roots]
    exact List.map_congr_left fun a ha' => normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have subS : singles ⊆ S := fun a hs => raw_required run roots a sub (necessary a hs)
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front, List.nodup_append]
    refine ⟨Finset.nodup_toList _, Finset.nodup_toList _, fun a ha b hb he => ?_⟩
    subst b; exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset = S := by ext a; simp [front, Finset.union_sdiff_of_subset subS]
  have gc : restrictW f (obs T) = obs G := (obs_renameW f T).symm.trans (congrArg obs eq)
  have hsup : Supply (other.map obs) ((front.map obs).map (restrictW f)) := by
    intro v hv
    obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
    exact covered a (sub a (fe ▸ List.mem_toFinset.mpr ha'))
  obtain ⟨q, next, hq, hav, hbound⟩ :=
    contraction (gc ▸ obs_not_const hG0 hGlt hGb0) (restrict_run f (live_to_run run front nd fe))
      (other.map obs) (show Reach (other.map obs) 0 (other.map obs) from rfl) hsup
  have hlo := prior q next hq (gc ▸ hav)
  have hmass : singles.card ≤ wmass ((front.map obs).map (restrictW f)) := by
    simp only [front, List.map_append, wmass_append]
    let xs := (singles.toList.map obs).map (restrictW f)
    have hc : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_, hm', rfl⟩ := List.mem_map.mp hv
      obtain ⟨a, ha', rfl⟩ := List.mem_map.mp hm'
      exact constant a (Finset.mem_toList.mp ha')
    have hlen := wmass_consts xs hc
    simp only [xs, List.length_map, Finset.length_toList] at hlen
    change singles.card ≤ wmass xs + _
    rw [← hlen]
    exact Nat.le_add_right _ _
  have := hbound
  omega
lemma lower_count {roots : List Nat} {T : Nat}
    (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (hR : ∀ a ∈ roots, a < 2^128 ∧ a.testBit 0 = false)
    (singles : Finset Nat) (ess : ∀ a ∈ singles, Essential T roots a) :
    Lower roots T (singles.card - 1) := by
  intro p bank hr ha
  have hnormT : normPack (obs T) = T := normPack_eq_of_obs hTlt hTb0
  have hm : T ∈ bank.map normPack := by
    have h1 := (avail_normPack ha).resolve_left (by rwa [hnormT])
    rwa [hnormT] at h1
  obtain ⟨k, S, hk, run, sub⟩ := reach_to_live_sub hr (T := T) (k := 0) (S := {T}) ⟨rfl, hT0⟩ (by simpa using hm)
  have hmap : (roots.map obs).map normPack = roots := by
    rw [List.map_map]; conv_rhs => rw [← List.map_id roots]
    exact List.map_congr_left fun a ha' => normPack_eq_of_obs (hR a ha').1 (hR a ha').2
  rw [hmap] at sub
  have hsub : singles ⊆ S := fun a ha' => raw_required run roots a sub (ess a ha')
  have hle := (Finset.card_le_card hsub).trans (live_size run)
  omega
def VAR (i : Nat) : Nat :=
  match i with
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | 6 => 0xffffffffffffffff0000000000000000
  | _ => 0
def ALL128 : Nat := 0xffffffffffffffffffffffffffffffff
def swapRow (i j : Nat) (r : Row) : Row :=
  let bi := r.val.testBit i
  let bj := r.val.testBit j
  if bi == bj then r
  else ⟨(r.val ^^^ (1 <<< i) ^^^ (1 <<< j)) % 128, Nat.mod_lt _ (by decide)⟩
def swapWord (i j : Nat) (w : Nat) : Nat :=
  let a := VAR i
  let b := VAR j
  let m10 := a ^^^ (a &&& b)
  let m01 := b ^^^ (a &&& b)
  let msame := ALL128 ^^^ (m10 ||| m01)
  let d := (1 <<< j) - (1 <<< i)
  (w &&& msame) ||| ((w &&& m10) <<< d) ||| ((w &&& m01) >>> d)
def permRow (swaps : List (Nat × Nat)) (r : Row) : Row :=
  swaps.foldl (fun x p => swapRow p.1 p.2 x) r
def permWord (swaps : List (Nat × Nat)) (w : Nat) : Nat :=
  swaps.foldr (fun p x => swapWord p.1 p.2 x) w
lemma swapRow_invol (i j : Nat) (hi : i < 7) (hj : j < 7) (r : Row) :
    swapRow i j (swapRow i j r) = r := by
  revert r
  interval_cases i <;> interval_cases j <;> decide +kernel
lemma swapWord_testBit (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) (hw : w < 2^128) (r : Row) :
    (swapWord i j w).testBit r.val = w.testBit (swapRow i j r).val := by
  have hi : i < 7 := by omega
  have hspec : ∀ r : Row,
      let a := VAR i; let b := VAR j
      let m10 := a ^^^ (a &&& b); let m01 := b ^^^ (a &&& b); let msame := ALL128 ^^^ (m10 ||| m01)
      let d := (1 <<< j) - (1 <<< i)
      (msame.testBit r.val = true → (swapRow i j r).val = r.val ∧ (d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = false) ∧
      (msame.testBit r.val = false →
        (d ≤ r.val ∧ m10.testBit (r.val - d) = true ∧ (swapRow i j r).val = r.val - d ∧ m01.testBit (r.val + d) = false) ∨
        ((d ≤ r.val → m10.testBit (r.val - d) = false) ∧ m01.testBit (r.val + d) = true ∧ (swapRow i j r).val = r.val + d)) := by
    revert r; interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have hr := hspec r
  simp only [swapWord, Nat.testBit_or, Nat.testBit_and, Nat.testBit_shiftLeft, Nat.testBit_shiftRight, Nat.add_comm]
  cases hms : (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))).testBit r.val with
  | true =>
    obtain ⟨heq, h10, h01⟩ := hr.1 hms
    rw [heq]
    by_cases hd : (1 <<< j) - (1 <<< i) ≤ r.val
    · simp [hd, h10 hd, h01]
    · simp [hd, h01]
  | false =>
    rcases hr.2 hms with ⟨hd, h10, heq, h01⟩ | ⟨h10, h01, heq⟩
    · simp [hd, h10, heq, h01]
    · by_cases hd : (1 <<< j) - (1 <<< i) ≤ r.val
      · simp [hd, h10 hd, h01, heq]
      · simp [hd, h01, heq]
lemma swapWord_lt (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) : swapWord i j w < 2^128 := by
  have hi : i < 7 := by omega
  have h1 : (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j)))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h2 : ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  have h3 : ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) < 2^128 := by
    interval_cases i <;> interval_cases j <;> (try omega) <;> decide +kernel
  unfold swapWord
  have e1 : (w &&& (ALL128 ^^^ (VAR i ^^^ (VAR i &&& VAR j) ||| (VAR j ^^^ (VAR i &&& VAR j))))) < 2^128 :=
    Nat.lt_of_le_of_lt Nat.and_le_right h1
  have e2 : ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i))) < 2^128 := by
    have hle : (w &&& (VAR i ^^^ (VAR i &&& VAR j))) ≤ (VAR i ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR i ^^^ (VAR i &&& VAR j))) <<< ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR i ^^^ (VAR i &&& VAR j))) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftLeft_eq _ _
      _ ≤ (VAR i ^^^ (VAR i &&& VAR j)) * 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.mul_le_mul_right _ hle
      _ = ((VAR i ^^^ (VAR i &&& VAR j)) <<< ((1 <<< j) - (1 <<< i))) := (Nat.shiftLeft_eq _ _).symm
      _ < 2^128 := h2
  have e3 : ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i))) < 2^128 := by
    have hle : (w &&& (VAR j ^^^ (VAR i &&& VAR j))) ≤ (VAR j ^^^ (VAR i &&& VAR j)) := Nat.and_le_right
    calc ((w &&& (VAR j ^^^ (VAR i &&& VAR j))) >>> ((1 <<< j) - (1 <<< i)))
        = (w &&& (VAR j ^^^ (VAR i &&& VAR j))) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.shiftRight_eq_div_pow _ _
      _ ≤ (VAR j ^^^ (VAR i &&& VAR j)) / 2 ^ ((1 <<< j) - (1 <<< i)) := Nat.div_le_div_right hle
      _ = ((VAR j ^^^ (VAR i &&& VAR j)) >>> ((1 <<< j) - (1 <<< i))) := (Nat.shiftRight_eq_div_pow _ _).symm
      _ < 2^128 := h3
  exact Nat.or_lt_two_pow (Nat.or_lt_two_pow e1 e2) e3
lemma swapWord_eq_renameW (i j : Nat) (hij : i < j) (hj : j < 7) (w : Nat) (hw : w < 2^128) :
    swapWord i j w = renameW (swapRow i j) w := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · rw [swapWord_testBit i j hij hj w hw ⟨r, hr⟩, ← testBit_renameW (swapRow i j) w ⟨r, hr⟩]
  · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (swapWord_lt i j hij hj w) (Nat.pow_le_pow_right (by decide) (by omega))),
        Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
def swapsValid (swaps : List (Nat × Nat)) : Bool :=
  swaps.all fun p => decide (p.1 < p.2) && decide (p.2 < 7)
lemma permWord_eq_renameW (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (w : Nat) (hw : w < 2^128) : permWord swaps w = renameW (permRow swaps) w := by
  induction swaps generalizing w with
  | nil =>
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · exact (testBit_renameW (permRow []) w ⟨r, hr⟩).symm
    · rw [show permWord [] w = w from rfl,
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hw (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))]
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have ihw := ih hv.2 w hw
    have hlt : permWord ps w < 2^128 := ihw ▸ renameW_lt _ w
    change swapWord p.1 p.2 (permWord ps w) = renameW (permRow (p :: ps)) w
    rw [swapWord_eq_renameW p.1 p.2 hv.1.1 hv.1.2 _ hlt, ihw]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · rw [testBit_renameW _ _ ⟨r, hr⟩, testBit_renameW _ _ (swapRow p.1 p.2 ⟨r, hr⟩), testBit_renameW _ _ ⟨r, hr⟩]
      rfl
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega)))]
lemma permRow_surj (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true) :
    Function.Surjective (permRow swaps) := by
  induction swaps with
  | nil => intro r; exact ⟨r, rfl⟩
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    intro r
    obtain ⟨q, hq⟩ := ih hv.2 r
    refine ⟨swapRow p.1 p.2 q, ?_⟩
    change permRow ps (swapRow p.1 p.2 (swapRow p.1 p.2 q)) = r
    rw [swapRow_invol p.1 p.2 (by omega) hv.1.2, hq]
lemma permRow_rev_cancel (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true) (r : Row) :
    permRow swaps.reverse (permRow swaps r) = r := by
  induction swaps generalizing r with
  | nil => rfl
  | cons p ps ih =>
    simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
        swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
      simp [permRow, List.reverse_cons, List.foldl_append]
    rw [h1, ih hv.2, swapRow_invol p.1 p.2 (by omega) hv.1.2]
lemma rotate_impossible {T n : Nat} {ws : List Nat} (hi : Impossible T n ws.toFinset)
    (swaps : List (Nat × Nat)) (hv : swapsValid swaps = true)
    (hT : T < 2^128) (hfix : permWord swaps T = T)
    (hw : ∀ a ∈ ws, a < 2^128) :
    Impossible T n (ws.map (permWord swaps)).toFinset := by
  intro k hk run
  have hr : ∀ a ∈ (ws.map (permWord swaps)).toFinset, a < 2^128 := by
    intro a ha
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    rw [permWord_eq_renameW swaps hv x (hw x hx)]
    exact renameW_lt _ x
  have hvr : swapsValid swaps.reverse = true := by
    simp only [swapsValid, List.all_reverse]; exact hv
  have hinv_row2 : ∀ r : Row, permRow swaps (permRow swaps.reverse r) = r := by
    intro r; simpa using permRow_rev_cancel swaps.reverse hvr r
  have hinv_word : ∀ x : Nat, x < 2^128 → renameW (permRow swaps.reverse) (permWord swaps x) = x := by
    intro x hx
    rw [permWord_eq_renameW swaps hv x hx]
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hrr : r < 128
    · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega)))]
  have run' := live_renameW run hr (permRow swaps.reverse) (permRow_surj swaps.reverse hvr)
  have hT' : renameW (permRow swaps.reverse) T = T := by
    conv_lhs => rw [← hfix]
    exact hinv_word T hT
  have hS' : (ws.map (permWord swaps)).toFinset.image (renameW (permRow swaps.reverse)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image, List.mem_toFinset, List.mem_map]
    constructor
    · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
      rwa [hinv_word x (hw x hx)]
    · intro ha
      exact ⟨permWord swaps a, ⟨a, ha, rfl⟩, hinv_word a (hw a ha)⟩
  rw [hT', hS'] at run'
  exact hi k hk run'
abbrev Decor := Nat × Nat × Nat
def dbin (d : Nat) (x y : Decor) : Decor := (bin d x.1 y.1, bin d x.2.1 y.2.1, bin d x.2.2 y.2.2)
def dsep (x : Decor) : Nat := x.2.1 ^^^ x.2.2
def projBits (rows : List Nat) (w : Nat) : Nat :=
  rows.foldr (fun r acc => (acc <<< 1) ||| (if w.testBit r then 1 else 0)) 0
lemma testBit_projBits (rows : List Nat) (w i : Nat) :
    (projBits rows w).testBit i = match rows[i]? with | none => false | some r => w.testBit r := by
  induction rows generalizing i with
  | nil => simp [projBits]
  | cons r rs ih =>
    simp only [projBits, List.foldr_cons, Nat.testBit_or, Nat.testBit_shiftLeft]
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Nat.not_le.mpr (by decide : 0 < 1)]
      cases w.testBit r <;> rfl
    | succ i =>
      simp only [List.getElem?_cons_succ, Nat.le_add_left, decide_true, Bool.true_and, Nat.add_sub_cancel]
      have h0 : (if w.testBit r then (1 : Nat) else 0).testBit (i + 1) = false := by
        cases w.testBit r
        · simp
        · exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ i + 1)))
      rw [h0, Bool.or_false]
      exact ih i
lemma projBits_bin (rows : List Nat) (d a b : Nat) :
    projBits rows (bin d a b) = bin d (projBits rows a) (projBits rows b) := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [testBit_projBits, testBit_bin, testBit_projBits, testBit_projBits]
  cases rows[i]? with
  | none => rcases d with _ | _ | _ | d <;> rfl
  | some r => exact testBit_bin d a b r
def faithful (pos neg : List Nat) (x : Decor) : Prop :=
  x.2.1 = projBits pos x.1 ∧ x.2.2 = projBits neg x.1
lemma faithful_bin {pos neg x y} (d : Nat) (hx : faithful pos neg x) (hy : faithful pos neg y) :
    faithful pos neg (dbin d x y) :=
  ⟨by rw [dbin, hx.1, hy.1, projBits_bin], by rw [dbin, hx.2, hy.2, projBits_bin]⟩
def goodPairs (T : Nat) (pos neg : List Nat) : Prop :=
  pos.length = neg.length ∧ ∀ i < pos.length,
    T.testBit (pos.getD i 0) = true ∧ T.testBit (neg.getD i 0) = false
def fullMask (n : Nat) : Nat := (1 <<< n) - 1
abbrev Cov := Nat × Nat × Nat
def addCov (z : Nat) (c : Cov) : Cov :=
  (z ||| c.1, (z ^^^ (z &&& c.1)) ||| (c.2.1 ^^^ (c.2.1 &&& z)),
   (z &&& c.2.1) ||| (c.2.2 ^^^ (c.2.2 &&& z)))
def coverage (v : List Decor) : Cov := v.foldr (fun a c => addCov (dsep a) c) (0, 0, 0)
def takeOne (c : Cov) (a : Nat) : Nat := c.1 ^^^ (c.1 &&& (c.2.1 &&& a))
def takeTwo (c : Cov) (a b : Nat) : Nat :=
  c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
lemma cov_one (c : Cov) (a : Nat) : takeOne (addCov a c) a = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeOne, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases c.1.testBit i <;> cases c.2.1.testBit i <;> rfl
lemma cov_two (c : Cov) (a b : Nat) : takeTwo (addCov a (addCov b c)) a b = c.1 := by
  apply Nat.eq_of_testBit_eq; intro i
  simp only [takeTwo, addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor]
  cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
    cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma addCov_swap (c : Cov) (a b : Nat) : addCov a (addCov b c) = addCov b (addCov a c) := by
  apply Prod.ext
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [addCov, Nat.testBit_or]; cases a.testBit i <;> cases b.testBit i <;> rfl
  · apply Prod.ext <;> apply Nat.eq_of_testBit_eq <;> intro i <;>
      simp only [addCov, Nat.testBit_or, Nat.testBit_and, Nat.testBit_xor] <;>
      cases a.testBit i <;> cases b.testBit i <;> cases c.1.testBit i <;>
      cases c.2.1.testBit i <;> cases c.2.2.testBit i <;> rfl
lemma cov_perm {l r : List Decor} (h : l.Perm r) : coverage l = coverage r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (addCov (dsep a)) ih
  | swap _ _ _ => exact addCov_swap _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2
def delOne (ws : List Decor) (a : Decor) (k : Bool) : List Decor := if k then ws else ws.erase a
def delTwo (ws : List Decor) (a b : Decor) (ka kb : Bool) : List Decor := delOne (delOne ws a ka) b kb
def restCov (c : Cov) (a b : Nat) (ka kb : Bool) : Nat :=
  if ka then (if kb then c.1 else takeOne c b) else if kb then takeOne c a else takeTwo c a b
lemma cov_delOne {ws : List Decor} (a : Decor) (ha : a ∈ ws) (k : Bool) :
    (coverage (delOne ws a k)).1 = if k then (coverage ws).1 else takeOne (coverage ws) (dsep a) := by
  cases k
  · change (coverage (ws.erase a)).1 = _
    rw [cov_perm (List.perm_cons_erase ha)]
    exact (cov_one _ _).symm
  · rfl
lemma cov_delTwo {ws : List Decor} (a b : Decor) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (ka kb : Bool) :
    (coverage (delTwo ws a b ka kb)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb := by
  cases ka <;> cases kb
  · have hbm : b ∈ ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
    have hp : ws.Perm (a :: b :: (ws.erase a).erase b) :=
      (List.perm_cons_erase ha).trans (List.Perm.cons _ (List.perm_cons_erase hbm))
    change (coverage ((ws.erase a).erase b)).1 = takeTwo (coverage ws) _ _
    rw [cov_perm hp]
    exact (cov_two _ _ _).symm
  · exact cov_delOne a ha false
  · exact cov_delOne b hb false
  · rfl
lemma cov_testBit (ws : List Decor) (i : Nat) :
    (coverage ws).1.testBit i = true ↔ ∃ x ∈ ws, (dsep x).testBit i = true := by
  induction ws with
  | nil => simp [coverage]
  | cons a ws ih =>
    change (dsep a ||| (coverage ws).1).testBit i = true ↔ _
    rw [Nat.testBit_or, Bool.or_eq_true, ih]
    simp
lemma cov_required {T k pos neg} {ws : List Decor}
    (gp : goodPairs T pos neg) (hf : ∀ x ∈ ws, faithful pos neg x)
    (h : Live T k (ws.map Prod.fst).toFinset) :
    ((coverage ws).1 &&& fullMask pos.length) = fullMask pos.length := by
  apply Nat.eq_of_testBit_eq; intro i
  rw [Nat.testBit_and]
  have hfm : (fullMask pos.length).testBit i = decide (i < pos.length) := by
    simp [fullMask, Nat.shiftLeft_eq, Nat.testBit_two_pow_sub_one]
  by_cases hi : i < pos.length
  · have ⟨hp, hn⟩ := gp.2 i hi
    have hsep : T.testBit (pos.getD i 0) ≠ T.testBit (neg.getD i 0) := by rw [hp, hn]; decide
    obtain ⟨v, hv, hvd⟩ := live_sep h hsep
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
    have hfx := hf x hx
    have hpi : pos[i]? = some (pos.getD i 0) := by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    have hni : neg[i]? = some (neg.getD i 0) := by
      have hi' : i < neg.length := gp.1 ▸ hi
      simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
    have hbit : (dsep x).testBit i = true := by
      simp only [dsep, Nat.testBit_xor, hfx.1, hfx.2, testBit_projBits, hpi, hni]
      have h12 : x.1.testBit (pos.getD i 0) ≠ x.1.testBit (neg.getD i 0) := by
        rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
        exact hvd
      cases h1 : x.1.testBit (pos.getD i 0) <;> cases h2 : x.1.testBit (neg.getD i 0)
      · exact absurd (h1.trans h2.symm) h12
      · rfl
      · rfl
      · exact absurd (h1.trans h2.symm) h12
    have hc := (cov_testBit ws i).mpr ⟨x, hx, hbit⟩
    simp [hfm, hi, hc]
  · simp [hfm, hi]
def insertNat (a : Nat) : List Nat → List Nat
  | [] => [a]
  | b :: bs => if a ≤ b then a :: b :: bs else b :: insertNat a bs
def sortNats : List Nat → List Nat
  | [] => []
  | a :: bs => insertNat a (sortNats bs)
lemma insertNat_perm (a : Nat) (l : List Nat) : (insertNat a l).Perm (a :: l) := by
  induction l with
  | nil => exact .refl _
  | cons b bs ih =>
    by_cases h : a ≤ b
    · simp [insertNat, h]
    · exact by simpa [insertNat, h] using (List.Perm.cons b ih).trans (.swap a b bs)
lemma sortNats_perm (l : List Nat) : (sortNats l).Perm l := by
  induction l with
  | nil => exact .refl _
  | cons a bs ih => exact (insertNat_perm a (sortNats bs)).trans (.cons a ih)
lemma sortNats_toFinset (l : List Nat) : (sortNats l).toFinset = l.toFinset := by
  ext x; simpa only [List.mem_toFinset] using (sortNats_perm l).mem_iff
def childTwo (ws : List Nat) (a b d : Nat) (ka kb : Bool) : List Nat :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))
lemma erase_toFinset {l : List Nat} (nd : l.Nodup) (a : Nat) :
    (l.erase a).toFinset = l.toFinset.erase a := by
  ext x; simp [nd.mem_erase_iff]
lemma enum_step {T cap : Nat} {ws : List Nat} (nd : ws.Nodup) (out : T ∉ ws)
    (stepOK : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d < 4, ∀ ka kb : Bool,
      a ≠ b → bin d a b ≠ 0 → bin d a b ∉ ws → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible T (cap - 1) (childTwo ws a b d ka kb).toFinset) :
    Impossible T cap ws.toFinset := by
  classical
  intro k hk h
  cases k with
  | zero =>
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  | succ k =>
    obtain ⟨U, a, b, d, hd, he, _, _, hab, hf, tail⟩ := h
    have am : a ∈ ws := List.mem_toFinset.mp (he ▸ Finset.mem_insert_self a _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self b _))
    have fresh : bin d a b ∉ ws := fun hm => hf (he ▸ List.mem_toFinset.mpr hm)
    have hnz : bin d a b ≠ 0 := live_nonzero tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest = (ws.erase a).erase b from rfl, erase_toFinset (nd.erase _) b, erase_toFinset nd a]
    have kf (c : Bool) (x : Nat) (l : List Nat) : (kept c x l).toFinset = if c then insert x l.toFinset else l.toFinset := by
      cases c <;> simp [kept]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kf, kf, er, he]; ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j = a <;> by_cases jb : j = b <;> simp_all [ka, kb]
    have rn : rest.Nodup := (nd.erase _).erase _
    have ar : a ∉ rest := fun h => nd.not_mem_erase (List.mem_of_mem_erase h)
    have br : b ∉ rest := (nd.erase a).not_mem_erase
    have nk := kept_nodup kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept, ar, hab]
    have ndc : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr hm))),
        kept_nodup ka a _ nk ax⟩
    have eqc : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b :: kept ka a (kept kb b rest)).toFinset = _; simp [ke]
    have sc := live_size tail
    have hlen : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [← List.toFinset_card_of_nodup ndc, eqc]; omega
    exact stepOK a am b bm d hd ka kb hab hnz fresh hlen k (by omega) (eqc.symm ▸ tail)
lemma delOne_sub (ws : List Decor) (a : Decor) (k : Bool) : (delOne ws a k).Sublist ws := by
  cases k; exact List.erase_sublist; exact List.Sublist.refl _
lemma delTwo_sub (ws : List Decor) (a b : Decor) (ka kb : Bool) : (delTwo ws a b ka kb).Sublist ws :=
  (delOne_sub _ _ _).trans (delOne_sub _ _ _)
lemma delTwo_len (ws : List Decor) (a b : Decor) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) :
    (delTwo ws a b ka kb).length = ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne ne.symm).mpr hb
  cases ka <;> cases kb <;> simp [delTwo, delOne, List.length_erase_of_mem ha, List.length_erase_of_mem hb, List.length_erase_of_mem hm]
lemma unique_fst {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (eq : a.1 = b.1) : a = b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn, ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | ha' <;> rcases List.mem_cons.mp hb with rfl | hb'
    · rfl
    · exact (hn (eq ▸ List.mem_map_of_mem hb')).elim
    · exact (hn (eq.symm ▸ List.mem_map_of_mem ha')).elim
    · exact ih ht ha' hb'
lemma delTwo_map_toFinset {ws : List Decor} (nd : (ws.map Prod.fst).Nodup) {a b : Decor}
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a.1 ≠ b.1) (d : Nat) (ka kb : Bool) :
    ((dbin d a b).1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset =
      (childTwo (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  have wn : ws.Nodup := nd.of_map
  have dn : (delOne ws a ka).Nodup := wn.sublist (delOne_sub ws a ka)
  have m1 (l : List Decor) (hl : l.Nodup) (x y : Decor) (c : Bool) :
      y ∈ delOne l x c ↔ y ∈ l ∧ (y ≠ x ∨ c = true) := by
    cases c <;> simp [delOne, hl.mem_erase_iff, and_comm]
  have km (v : Nat) : v ∈ (delTwo ws a b ka kb).map Prod.fst ↔
      v ∈ ws.map Prod.fst ∧ (v ≠ a.1 ∨ ka = true) ∧ (v ≠ b.1 ∨ kb = true) := by
    simp only [delTwo, List.mem_map, m1 _ wn, m1 _ dn]
    constructor
    · rintro ⟨w, ⟨⟨hw, h1⟩, h2⟩, rfl⟩
      exact ⟨⟨w, hw, rfl⟩, h1.imp (fun h e => h (unique_fst nd hw ha e)) id,
        h2.imp (fun h e => h (unique_fst nd hw hb e)) id⟩
    · rintro ⟨⟨w, hw, rfl⟩, h1, h2⟩
      exact ⟨w, ⟨⟨hw, h1.imp (fun h e => h (congrArg Prod.fst e)) id⟩,
        h2.imp (fun h e => h (congrArg Prod.fst e)) id⟩, rfl⟩
  have av := List.mem_map_of_mem (f := Prod.fst) ha
  have bv := List.mem_map_of_mem (f := Prod.fst) hb
  have hkeep (c : Bool) (x : Nat) (l : List Nat) (v : Nat) : v ∈ kept c x l ↔ (v = x ∧ c = true) ∨ v ∈ l := by
    cases c <;> simp [kept]
  ext v
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, km, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, dbin]
  by_cases va : v = a.1 <;> by_cases vb : v = b.1 <;> cases ka <;> cases kb <;> simp_all
lemma childTwo_swap (v : List Nat) (nd : v.Nodup) (a b : Nat) (d : Nat) (hd : d < 4) (ka kb : Bool) :
    (childTwo v a b d ka kb).toFinset = (childTwo v b a (flipOp d) kb ka).toFinset := by
  have hkeep (c : Bool) (x : Nat) (l : List Nat) (y : Nat) : y ∈ kept c x l ↔ (y = x ∧ c = true) ∨ y ∈ l := by
    cases c <;> simp [kept]
  ext x
  simp only [childTwo, List.toFinset_cons, Finset.mem_insert, List.mem_toFinset, hkeep,
    (nd.erase _).mem_erase_iff, nd.mem_erase_iff, bin_comm_flip d hd a b]
  tauto
def varsOf (m : Nat) : List Nat :=
  (List.range 7).filterMap fun i => if m.testBit i then some (VAR i) else none
def subcube (z o : Nat) : Nat :=
  (List.range 128).foldr (fun r acc =>
    if (r &&& z == 0) && (r &&& o == o) then acc ||| (1 <<< r) else acc) 0
def fixWord (z o w : Nat) : Nat :=
  (List.range 128).foldr (fun r acc =>
    let fr := ((r &&& (127 ^^^ z)) ||| o) % 128
    if w.testBit fr then acc ||| (1 <<< r) else acc) 0
lemma testBit_foldr_bits (p : Nat → Bool) (l : List Nat) (r : Nat) :
    (l.foldr (fun i acc => if p i then acc ||| (1 <<< i) else acc) 0).testBit r =
      (decide (r ∈ l) && p r) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldr_cons]
    by_cases hpa : p a = true
    · simp only [hpa, ite_true, Nat.testBit_or, ih, Nat.testBit_shiftLeft]
      by_cases hra : r = a
      · subst hra; simp [hpa]
      · have h1 : (decide (a ≤ r) && (1 : Nat).testBit (r - a)) = false := by
          by_cases hle : a ≤ r
          · have hpos : r - a ≠ 0 := by omega
            simp only [hle, decide_true, Bool.true_and]
            exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (by decide : 1 < 2 ^ 1) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 1 ≤ r - a)))
          · simp [hle]
        simp [h1, hra]
    · have hpf : p a = false := Bool.eq_false_iff.mpr hpa
      simp only [hpf, Bool.false_eq_true, ite_false, ih]
      by_cases hra : r = a
      · subst hra; simp [hpf]
      · simp [hra]
lemma fixWord_eq_renameW (z o w : Nat) : fixWord z o w = renameW (fixRow z o) w := by
  apply Nat.eq_of_testBit_eq; intro r
  unfold fixWord
  rw [testBit_foldr_bits]
  by_cases hr : r < 128
  · rw [testBit_renameW (fixRow z o) w ⟨r, hr⟩]
    simp [hr, fixRow]
  · simp only [List.mem_range, hr, decide_false, Bool.false_and]
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ w) (Nat.pow_le_pow_right (by decide) (by omega)))).symm
lemma subcube_fixRow (z o : Nat) (hz : z < 128) (ho : o < 128) (hzo : (z &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow z o r).val = true := by
  unfold subcube
  rw [testBit_foldr_bits]
  have hmem : (fixRow z o r).val ∈ List.range 128 := List.mem_range.mpr (fixRow z o r).isLt
  simp only [hmem, decide_true, Bool.true_and, Bool.and_eq_true, beq_iff_eq]
  have h127 : ((r.val &&& (127 ^^^ z)) ||| o) < 128 := by
    have hr := r.isLt
    have hlt1 : (r.val &&& (127 ^^^ z)) < 128 := Nat.lt_of_le_of_lt Nat.and_le_left hr
    exact Nat.or_lt_two_pow (n := 7) hlt1 ho
  have hval : (fixRow z o r).val = ((r.val &&& (127 ^^^ z)) ||| o) := Nat.mod_eq_of_lt h127
  rw [hval]
  constructor
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor, Nat.zero_testBit]
    have hzi : (z.testBit i && o.testBit i) = false := by
      have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
    by_cases hi : i < 7
    · have h7 : (127 : Nat).testBit i = true := by interval_cases i <;> decide
      cases hzb : z.testBit i <;> cases hob : o.testBit i <;> simp_all [h7]
    · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
      simp [hzf]
  · apply Nat.eq_of_testBit_eq; intro i
    simp only [Nat.testBit_and, Nat.testBit_or]
    cases o.testBit i <;> simp
def checkEss1 (T : Nat) (roots : List Nat) (a r s : Nat) : Bool :=
  decide (r < 128) && decide (s < 128) && (T.testBit r != T.testBit s) &&
    roots.all fun v => v == a || (v.testBit r == v.testBit s)
lemma checkEss1_sound {T roots a r s} (h : checkEss1 T roots a r s = true) : Essential T roots a := by
  simp only [checkEss1, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, List.all_eq_true, Bool.or_eq_true, beq_iff_eq] at h
  exact ⟨⟨r, h.1.1.1⟩, ⟨s, h.1.1.2⟩, h.1.2, fun v hv hne => (h.2 v hv).resolve_left hne⟩
def freeIn (other : List Nat) (w : Nat) : Bool := w == 0 || w == ALL128 || other.contains w
lemma freeIn_sound {other : List Nat} {f : Row → Row} {a : Nat} (ok : freeIn other (renameW f a) = true) :
    Avail (other.map obs) (restrictW f (obs a)) := by
  rw [← obs_renameW]
  simp only [freeIn, Bool.or_eq_true, beq_iff_eq, List.contains_eq_mem, decide_eq_true_eq] at ok
  rcases ok with (h0 | h1) | hm
  · exact Or.inr (Or.inl ⟨false, by rw [h0]; funext r; simp [obs]⟩)
  · exact Or.inr (Or.inl ⟨true, by rw [h1]; funext r; simp only [obs, ALL128]; have := r.isLt; exact Nat.testBit_two_pow_sub_one 128 r.val |> fun e => by simpa [this] using e⟩)
  · exact Or.inl (List.mem_map_of_mem hm)
def checkProper (w : Nat) : Bool := w != 0 && decide (w < 2^128) && !w.testBit 0
lemma checkProper_sound {w : Nat} (h : checkProper w = true) : w ≠ 0 ∧ w < 2^128 ∧ w.testBit 0 = false := by
  simp only [checkProper, Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact ⟨h.1.1, h.1.2, h.2⟩
def checkRoots (rs : List Nat) : Bool := rs.all fun a => decide (a < 2^128) && !a.testBit 0
lemma checkRoots_sound {rs : List Nat} (h : checkRoots rs = true) :
    ∀ a ∈ rs, a < 2^128 ∧ a.testBit 0 = false := by
  simp only [checkRoots, List.all_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h
  exact h
def carryOK (swaps : List (Nat × Nat)) (roots1 : List Nat) (T1 : Nat) (roots2 : List Nat) (T2 : Nat) : Bool :=
  swapsValid swaps && checkProper T1 && checkRoots roots1 && checkProper T2 &&
    (permWord swaps T1 == T2) && roots1.all (fun a => freeIn roots2 (permWord swaps a))
lemma carry_of {swaps roots1 T1 roots2 T2 L} (ok : carryOK swaps roots1 T1 roots2 T2 = true)
    (hL : Lower roots2 T2 L) : Lower roots1 T1 L := by
  simp only [carryOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨hsv, hT1⟩, hR1⟩, hT2⟩, heq⟩, hcov⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT1
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hT2
  have hR1' := checkRoots_sound hR1
  have heq' : renameW (permRow swaps) T1 = T2 := (permWord_eq_renameW swaps hsv T1 p1b).symm.trans heq
  have hcov' : ∀ a ∈ roots1, Avail (roots2.map obs) (restrictW (permRow swaps) (obs a)) := fun a ha =>
    freeIn_sound (permWord_eq_renameW swaps hsv a (hR1' a ha).1 ▸ hcov a ha)
  simpa using lower_slice p1a p1b p1c hR1' p2a p2b p2c (permRow swaps) heq' hcov' ∅ (by simp) (by simp) L hL
def countCheck (roots : List Nat) (T L : Nat) (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots &&
    decide (essPairs.map Prod.fst).Nodup &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2) &&
    decide (L ≤ essPairs.length - 1)
lemma count_of {roots T L essPairs} (ok : countCheck roots T L essPairs = true) :
    Lower roots T L := by
  simp only [countCheck, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨hT, hR⟩, hnd⟩, hess⟩, hle⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hl := lower_count p1 p2 p3 hR' (essPairs.map Prod.fst).toFinset (fun a ha => by
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm))
  have hcard : (essPairs.map Prod.fst).toFinset.card = essPairs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [hcard] at hl
  exact fun p bank hr hav => hle.trans (hl p bank hr hav)
def liftCheck (z o : Nat) (roots : List Nat) (T : Nat) (other : List Nat) (G : Nat)
    (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots && checkProper G &&
    decide (essPairs.map Prod.fst).Nodup &&
    (fixWord z o T == G) &&
    roots.all (fun a => freeIn other (fixWord z o a)) &&
    essPairs.all (fun e => checkEss1 T roots e.1 e.2.1 e.2.2 &&
      (fixWord z o e.1 == 0 || fixWord z o e.1 == ALL128))
lemma lift_of {z o roots T other G essPairs L} (ok : liftCheck z o roots T other G essPairs = true)
    (hL : Lower other G L) : Lower roots T (L + essPairs.length) := by
  simp only [liftCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hT, hR⟩, hG⟩, hnd⟩, heq⟩, hcov⟩, hess⟩ := ok
  have ⟨p1a, p1b, p1c⟩ := checkProper_sound hT
  have ⟨p2a, p2b, p2c⟩ := checkProper_sound hG
  have hR' := checkRoots_sound hR
  have heq' : renameW (fixRow z o) T = G := (fixWord_eq_renameW z o T).symm.trans heq
  have hcov' : ∀ a ∈ roots, Avail (other.map obs) (restrictW (fixRow z o) (obs a)) := fun a ha =>
    freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha)
  have hcard : (essPairs.map Prod.fst).toFinset.card = essPairs.length := by
    rw [List.toFinset_card_of_nodup hnd, List.length_map]
  rw [← hcard]
  apply lower_slice p1a p1b p1c hR' p2a p2b p2c (fixRow z o) heq' hcov' (essPairs.map Prod.fst).toFinset _ _ L hL
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    exact checkEss1_sound (hess (v, r, s) hm).1
  · intro a ha
    obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
    have hc := (hess (v, r, s) hm).2
    simp only [Bool.or_eq_true, beq_iff_eq, fixWord_eq_renameW] at hc
    rw [← obs_renameW]
    rcases hc with h0 | h1
    · exact ⟨false, by rw [h0]; funext r'; simp [obs]⟩
    · exact ⟨true, by rw [h1]; funext r'; simp only [obs, ALL128]; have := r'.isLt; exact Nat.testBit_two_pow_sub_one 128 r'.val |> fun e => by simpa [this] using e⟩
def sliceCheck (z o zDrop : Nat) (raw : List Nat) (T : Nat) (freeRoots : List Nat) (qRoots : List Nat) (qGoal : Nat)
    (qL : Nat) (lEss : List (Nat × Nat × Nat)) (sliceL : Nat) : Bool :=
  let G := fixWord z o T
  decide (z < 128) && decide (o < 128) && ((z &&& o) == 0) &&
    checkProper G && checkRoots freeRoots &&
    raw.all (fun a => freeIn freeRoots (fixWord z o a)) &&
    (if qGoal == 0 then
       decide (lEss.map Prod.fst).Nodup &&
       lEss.all (fun e => checkEss1 G freeRoots e.1 e.2.1 e.2.2) &&
       decide (sliceL ≤ lEss.length - 1)
     else
       liftCheck zDrop 0 freeRoots G qRoots qGoal lEss &&
       decide (sliceL ≤ qL + lEss.length))
lemma slice_of {z o zDrop raw T freeRoots qRoots qGoal qL lEss sliceL}
    (ok : sliceCheck z o zDrop raw T freeRoots qRoots qGoal qL lEss sliceL = true)
    (hPrior : qGoal ≠ 0 → Lower qRoots qGoal qL) :
    Slice raw T (subcube z o) sliceL := by
  simp only [sliceCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨hz, ho⟩, hzo⟩, hGp⟩, hFR⟩, hcov⟩, htail⟩ := ok
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  have hFR' := checkRoots_sound hFR
  refine ⟨fixRow z o, freeRoots, subcube_fixRow z o hz ho hzo,
    fun a ha => freeIn_sound ((fixWord_eq_renameW z o a).symm ▸ hcov a ha),
    by rw [← obs_renameW, ← fixWord_eq_renameW]; exact obs_not_const g0 glt gb0, ?_⟩
  rw [← obs_renameW, ← fixWord_eq_renameW]
  by_cases hq : qGoal = 0
  · simp only [hq, ite_true, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at htail
    have hl := lower_count g0 glt gb0 hFR' (lEss.map Prod.fst).toFinset (fun a ha => by
      obtain ⟨⟨v, r, s⟩, hm, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
      exact checkEss1_sound (htail.1.2 _ hm))
    have hcard : (lEss.map Prod.fst).toFinset.card = lEss.length := by
      rw [List.toFinset_card_of_nodup htail.1.1, List.length_map]
    rw [hcard] at hl
    exact fun p bank hr hav => htail.2.trans (hl p bank hr hav)
  · simp only [hq, ite_false, Bool.and_eq_true, decide_eq_true_eq] at htail
    have hl := lift_of htail.1 (hPrior hq)
    exact fun p bank hr hav => htail.2.trans (hl p bank hr hav)
def goodPairsCheck (T : Nat) (pos neg : List Nat) : Bool :=
  (pos.length == neg.length) &&
    (List.range pos.length).all fun i => T.testBit (pos.getD i 0) && !(T.testBit (neg.getD i 0))
lemma goodPairs_of {T pos neg} (ok : goodPairsCheck T pos neg = true) : goodPairs T pos neg := by
  simp only [goodPairsCheck, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range, Bool.not_eq_true'] at ok
  exact ok
def autosCheck (T : Nat) (autos : List (List (Nat × Nat))) : Bool :=
  autos.all fun sw => swapsValid sw && (permWord sw T == T)
lemma autos_of {T autos} (ok : autosCheck T autos = true) :
    ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T := by
  simp only [autosCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq] at ok
  exact ok
def baseCheck (pos neg : List Nat) (base : List Decor) : Bool :=
  base.all fun x => (x.2.1 == projBits pos x.1) && (x.2.2 == projBits neg x.1) && decide (x.1 < 2^128)
lemma base_of {pos neg base} (ok : baseCheck pos neg base = true) :
    ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128 := by
  simp only [baseCheck, List.all_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at ok
  intro x hx
  have h := ok x hx
  exact ⟨⟨h.1.1, h.1.2⟩, h.2⟩
def forestRootCheck (roots : List Nat) (T : Nat) (essPairs : List (Nat × Nat × Nat)) : Bool :=
  checkProper T && checkRoots roots &&
    roots.all fun a => essPairs.any fun e => (e.1 == a) && checkEss1 T roots e.1 e.2.1 e.2.2
lemma faithful_zero (pos neg : List Nat) : faithful pos neg (0, 0, 0) := by
  constructor
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases pos[i]? <;> simp
  · apply Nat.eq_of_testBit_eq; intro i; rw [testBit_projBits]; cases neg[i]? <;> simp
lemma forall_cons {α : Type} {P : α → Prop} {a : α} {l : List α} (ha : P a) (hl : ∀ x ∈ l, P x) :
    ∀ x ∈ a :: l, P x := by
  intro x hx; rcases List.mem_cons.mp hx with rfl | hx; exact ha; exact hl x hx
abbrev PoolSpec := Nat × List (Nat × Nat × Nat)
abbrev NodeSpec := List Nat × List Nat × List Nat
def evalInput (r : Row) : Fin 7 → Bool := fun i => r.val.testBit i.val
def packInput (x : Fin 7 → Bool) : Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
    16 * (x 4).toNat + 32 * (x 5).toNat + 64 * (x 6).toNat, by
    have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
    have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
    have h6 := Bool.toNat_le (x 6); omega⟩
lemma evalInput_packInput (x : Fin 7 → Bool) : evalInput (packInput x) = x := by
  funext i
  have h : ∀ (b0 b1 b2 b3 b4 b5 b6 : Bool) (j : Fin 7),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat + 64 * b6.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5, b6].getD j.val false) := by decide +kernel
  have hi := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) (x 6) i
  fin_cases i <;> simpa [evalInput, packInput] using hi
lemma var_testBit (i : Fin 7) (r : Row) : (VAR i.val).testBit r.val = r.val.testBit i.val := by
  revert i r; decide +kernel
lemma sw_extract_full (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 127 := by
  let seeds : List SWire := (varsOf 127).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^128 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 127).all (fun a => decide (a < 2^128) && !a.testBit 0) = true := by decide +kernel
    have h1 := List.all_eq_true.mp hall v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact h1
  let final := swExec gs seeds
  let out := final.getD o swZero
  have hfinal_lt : out.2 < 2^128 ∧ out.2.testBit 0 = false := by
    simp only [out, List.getD_eq_getElem?_getD]
    cases eq : final[o]? with
    | none => exact ⟨by decide, by decide⟩
    | some a => exact swExec_lt gs seeds hseeds_lt a (List.mem_of_getElem? eq)
  have hread_seeds (r : Row) : seeds.map (swRead r.val) = List.ofFn (evalInput r) := by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi7 : i < 7 := by simpa using hi2
      have hv : (varsOf 127)[i]? = some (VAR i) := by
        interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput, swRead, Bool.false_bne]
      have hget : (varsOf 127)[i]'(by simpa [seeds] using hi1) = VAR i := by
        have := List.getElem?_eq_some_iff.mp hv; exact this.2
      rw [hget]
      exact var_testBit ⟨i, hi7⟩ r
  have hev (r : Row) : swRead r.val out = T.testBit r.val := by
    have h1 := (swRead_get r.val final o).symm
    rw [show final = swExec gs seeds from rfl, swExec_read r.val gs seeds legal, hread_seeds r] at h1
    exact h1.trans (he r)
  have hout0 : out.1 = false := by
    have h0 := hev 0
    simp only [swRead, Fin.val_zero, hfinal_lt.2, hTb0, Bool.bne_false] at h0
    exact h0
  have hout2 : out.2 = T := by
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · have h := hev ⟨r, hr⟩
      simpa [swRead, hout0] using h
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hfinal_lt.1 (Nat.pow_le_pow_right (by decide) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hTlt (Nat.pow_le_pow_right (by decide) (by omega)))]
  have hfound : T ∈ reps final := by
    rw [← hout2]
    exact (get_simple final o).resolve_left (hout2.symm ▸ hT0)
  obtain ⟨k, S, hk, hlive, hsub⟩ := extract_live hT0 gs seeds hfound
  refine ⟨k, S, hk, hlive, ?_⟩
  simpa [reps, seeds, List.map_map, Function.comp_def] using hsub
lemma replace_of_lower (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (L : Nat) (hLow : Lower (varsOf 127) T L)
    (wit : List Gate) (wo : Nat) (hwLen : wit.length ≤ L + 1)
    (hwMono : ∀ g ∈ wit, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (edgeFn : (Fin 7 → Bool) → Bool)
    (hEdgeT : ∀ r : Row, edgeFn (evalInput r) = T.testBit r.val)
    (hwEvalR : ∀ r : Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput r)) = T.testBit r.val)
    (gates : List Gate) (o : Nat)
    (legal : ∀ g ∈ gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (spec : ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates, o⟩ (List.ofFn x) = edgeFn x) :
    ∃ (gates' : List Gate) (o' : Nat),
      (∀ g ∈ gates', (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gates'.length ≤ gates.length ∧
      ∀ x : Fin 7 → Bool, Circuit.eval ⟨gates', o'⟩ (List.ofFn x) = edgeFn x := by
  have hwEval : ∀ x : Fin 7 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = edgeFn x := by
    intro x
    have hx := evalInput_packInput x
    rw [← hx]
    exact (hwEvalR (packInput x)).trans (hEdgeT (packInput x)).symm
  by_cases hn : ∃ g ∈ gates, g.op = .not
  · have hlt : gates.countP isBin < gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro eq
      obtain ⟨g, hg, hop⟩ := hn
      have bad := List.countP_eq_length.mp eq g hg
      simp [isBin, hop] at bad
    obtain ⟨k, S, hk, hlive, hsub⟩ := sw_extract_full T hT0 hTlt hTb0 gates o legal (fun r => (spec (evalInput r)).trans (hEdgeT r))
    have hnd : S.toList.Nodup := Finset.nodup_toList S
    have hrun := live_to_run hlive S.toList hnd (by simp)
    have hsup : Supply ((varsOf 127).map obs) (S.toList.map obs) := fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 127).map obs)
        (show Reach ((varsOf 127).map obs) 0 ((varsOf 127).map obs) from rfl) hsup
    have hlo := hLow q next hq hav
    refine ⟨wit, wo, hwMono, by omega, hwEval⟩
  · refine ⟨gates, o, ?_, le_rfl, spec⟩
    intro g hg
    obtain ⟨hop, hlen⟩ := legal g hg
    refine ⟨?_, hlen⟩
    rcases hop with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn ⟨g, hg, h⟩).elim
def sliceDirectCheck (z o zDead : Nat) (raw : List Nat) (T : Nat) (qRoots : List Nat) (qGoal : Nat) : Bool :=
  decide (z < 128) && decide (o < 128) && ((z &&& o) == 0) &&
    decide (zDead < 128) && (((z ||| zDead) &&& o) == 0) &&
    checkProper qGoal && checkRoots qRoots &&
    (fixWord (z ||| zDead) o T == qGoal) &&
    raw.all (fun a => freeIn qRoots (fixWord (z ||| zDead) o a))
lemma subcube_fixRow_sup (z o zDead : Nat) (hz : z < 128) (hd : zDead < 128) (ho : o < 128)
    (hzo : ((z ||| zDead) &&& o) = 0) (r : Row) :
    (subcube z o).testBit (fixRow (z ||| zDead) o r).val = true := by
  have hsub := subcube_fixRow (z ||| zDead) o (Nat.or_lt_two_pow (n := 7) hz hd) ho hzo r
  unfold subcube at hsub ⊢
  rw [testBit_foldr_bits] at hsub ⊢
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hsub ⊢
  refine ⟨hsub.1, ?_, hsub.2.2⟩
  apply Nat.eq_of_testBit_eq; intro i
  have h1 := congrArg (fun x => x.testBit i) hsub.2.1
  simp only [Nat.testBit_and, Nat.testBit_or, Nat.zero_testBit] at h1 ⊢
  cases hfa : (fixRow (z ||| zDead) o r).val.testBit i <;> cases hzb : z.testBit i <;> simp_all
lemma slice_direct {z o zDead raw T qRoots qGoal qL}
    (ok : sliceDirectCheck z o zDead raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcube z o) qL := by
  simp only [sliceDirectCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true] at ok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hz, ho⟩, _hzo0⟩, hd⟩, hzo⟩, hGp⟩, hQR⟩, heq⟩, hcov⟩ := ok
  have ⟨g0, glt, gb0⟩ := checkProper_sound hGp
  refine ⟨fixRow (z ||| zDead) o, qRoots, subcube_fixRow_sup z o zDead hz hd ho hzo,
    fun a ha => freeIn_sound ((fixWord_eq_renameW (z ||| zDead) o a).symm ▸ hcov a ha),
    by rw [← obs_renameW, ← fixWord_eq_renameW, heq]; exact obs_not_const g0 glt gb0, ?_⟩
  rw [← obs_renameW, ← fixWord_eq_renameW, heq]
  exact hPrior
def evalInput6 (r : Row) : Fin 6 → Bool := fun i => r.val.testBit i.val
def packInput6 (x : Fin 6 → Bool) : Row :=
  ⟨(x 0).toNat + 2 * (x 1).toNat + 4 * (x 2).toNat + 8 * (x 3).toNat +
    16 * (x 4).toNat + 32 * (x 5).toNat, by
    have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
    have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
    omega⟩
lemma evalInput6_packInput6 (x : Fin 6 → Bool) : evalInput6 (packInput6 x) = x := by
  funext i
  have h : ∀ (b0 b1 b2 b3 b4 b5 : Bool) (j : Fin 6),
      ((b0.toNat + 2 * b1.toNat + 4 * b2.toNat + 8 * b3.toNat +
        16 * b4.toNat + 32 * b5.toNat).testBit j.val) =
        ([b0, b1, b2, b3, b4, b5].getD j.val false) := by decide +kernel
  have hi := h (x 0) (x 1) (x 2) (x 3) (x 4) (x 5) i
  fin_cases i <;> simpa [evalInput6, packInput6] using hi
lemma sum_eq_packInput6 (x : Fin 6 → Bool) :
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) = (packInput6 x).val := by
  simp only [Fin.sum_univ_six, Fin.val_zero, Fin.val_one, Fin.val_two, packInput6]
  cases x 0 <;> cases x 1 <;> cases x 2 <;> cases x 3 <;> cases x 4 <;> cases x 5 <;> decide
lemma testBit_rep64 (T6 : Nat) (hT6 : T6 < 2^64) (r : Row) :
    (T6 ||| (T6 <<< 64)).testBit r.val = T6.testBit (r.val % 64) := by
  have hr := r.isLt
  rw [Nat.testBit_or, Nat.testBit_shiftLeft]
  by_cases h64 : r.val < 64
  · have hn : ¬(64 ≤ r.val) := by omega
    rw [Nat.mod_eq_of_lt h64]
    simp [hn]
  · have hge : 64 ≤ r.val := by omega
    have hmod : r.val % 64 = r.val - 64 := by omega
    rw [hmod]
    have hhi : T6.testBit r.val = false → (T6.testBit r.val || (decide (64 ≤ r.val) && T6.testBit (r.val - 64))) = T6.testBit (r.val - 64) := by
      intro hf; simp [hf, hge]
    have hf : T6.testBit r.val = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hT6 (Nat.pow_le_pow_right (by decide : 0 < 2) hge))
    exact hhi hf
lemma sw_extract_full_6 (T : Nat) (hT0 : T ≠ 0) (hTlt : T < 2^128) (hTb0 : T.testBit 0 = false)
    (gs : List Gate) (o : Nat)
    (legal : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2)
    (he : ∀ r : Row, Circuit.eval ⟨gs, o⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val) :
    ∃ k S, k ≤ gs.countP isBin ∧ Live T k S ∧ ∀ a ∈ S, a ∈ varsOf 63 := by
  let seeds : List SWire := (varsOf 63).map (fun v => (false, v))
  have hseeds_lt : ∀ u ∈ seeds, u.2 < 2^128 ∧ u.2.testBit 0 = false := by
    intro u hu
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hu
    have hall : (varsOf 63).all (fun a => decide (a < 2^128) && !a.testBit 0) = true := by decide +kernel
    have h1 := List.all_eq_true.mp hall v hv
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true'] at h1
    exact h1
  let final := swExec gs seeds
  let out := final.getD o swZero
  have hfinal_lt : out.2 < 2^128 ∧ out.2.testBit 0 = false := by
    simp only [out, List.getD_eq_getElem?_getD]
    cases eq : final[o]? with
    | none => exact ⟨by decide, by decide⟩
    | some a => exact swExec_lt gs seeds hseeds_lt a (List.mem_of_getElem? eq)
  have hread_seeds (r : Row) : seeds.map (swRead r.val) = List.ofFn (evalInput6 r) := by
    apply List.ext_getElem
    · simp only [seeds, List.length_map, List.length_ofFn]; decide
    · intro i hi1 hi2
      have hi6 : i < 6 := by simpa using hi2
      have hv : (varsOf 63)[i]? = some (VAR i) := by interval_cases i <;> decide
      simp only [List.getElem_map, List.getElem_ofFn, seeds, evalInput6, swRead, Bool.false_bne]
      have hget : (varsOf 63)[i]'(by simpa [seeds] using hi1) = VAR i := (List.getElem?_eq_some_iff.mp hv).2
      rw [hget]
      exact var_testBit ⟨i, by omega⟩ r
  have hev (r : Row) : swRead r.val out = T.testBit r.val := by
    have h1 := (swRead_get r.val final o).symm
    rw [show final = swExec gs seeds from rfl, swExec_read r.val gs seeds legal, hread_seeds r] at h1
    exact h1.trans (he r)
  have hout0 : out.1 = false := by
    have h0 := hev 0
    simp only [swRead, Fin.val_zero, hfinal_lt.2, hTb0, Bool.bne_false] at h0
    exact h0
  have hout2 : out.2 = T := by
    apply Nat.eq_of_testBit_eq; intro r
    by_cases hr : r < 128
    · have h := hev ⟨r, hr⟩; simpa [swRead, hout0] using h
    · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hfinal_lt.1 (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
          Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hTlt (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
  have hfound : T ∈ reps final := by
    rw [← hout2]; exact (get_simple final o).resolve_left (hout2.symm ▸ hT0)
  obtain ⟨k, S, hk, hlive, hsub⟩ := extract_live hT0 gs seeds hfound
  refine ⟨k, S, hk, hlive, ?_⟩
  simpa [reps, seeds, List.map_map, Function.comp_def] using hsub
lemma table2_of_lower (T6 : Nat) (hT6lt : T6 < 2^64)
    (hT0 : (T6 ||| (T6 <<< 64)) ≠ 0) (hTlt : (T6 ||| (T6 <<< 64)) < 2^128) (hTb0 : (T6 ||| (T6 <<< 64)).testBit 0 = false)
    (L : Nat) (hLow : Lower (varsOf 63) (T6 ||| (T6 <<< 64)) L)
    (wit : List Gate) (wo : Nat) (hwLen : wit.length ≤ L + 1)
    (hwMono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩)
    (hwEvalR : ∀ r : Row, Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = (T6 ||| (T6 <<< 64)).testBit r.val)
    (s : ℕ)
    (hcs : PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s) :
    ∃ C : Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧
      ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  let T := T6 ||| (T6 <<< 64)
  obtain ⟨C, hfan, hsize, heval⟩ := hcs
  have hlegal : ∀ g ∈ C.gates, (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have ⟨hm, hl⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hm
    exact ⟨hm, hl⟩
  by_cases hn : ∃ g ∈ C.gates, g.op = .not
  · have hlt : C.gates.countP isBin < C.gates.length := by
      apply Nat.lt_of_le_of_ne List.countP_le_length
      intro eq
      obtain ⟨g, hg, hop⟩ := hn
      have bad := List.countP_eq_length.mp eq g hg
      simp [isBin, hop] at bad
    have heR : ∀ r : Row, Circuit.eval ⟨C.gates, C.output⟩ (List.ofFn (evalInput6 r)) = T.testBit r.val := by
      intro r
      have h1 := heval (evalInput6 r)
      have hsum : (∑ i : Fin 6, if evalInput6 r i then 2 ^ (i : ℕ) else 0) = r.val % 64 := by
        rw [sum_eq_packInput6]
        have h : ∀ j : Row, (packInput6 (evalInput6 j)).val = j.val % 64 := by decide +kernel
        exact h r
      dsimp only at h1
      rw [hsum] at h1
      exact h1.trans (testBit_rep64 T6 hT6lt r).symm
    obtain ⟨k, S, hk, hlive, hsub⟩ := sw_extract_full_6 T hT0 hTlt hTb0 C.gates C.output hlegal heR
    have hrun := live_to_run hlive S.toList (Finset.nodup_toList S) (by simp)
    have hsup : Supply ((varsOf 63).map obs) (S.toList.map obs) := fun v hv => by
      obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
      exact Or.inl (List.mem_map_of_mem (hsub a (Finset.mem_toList.mp ha)))
    obtain ⟨q, next, hq, hav, hbound⟩ :=
      contraction (obs_not_const hT0 hTlt hTb0) hrun ((varsOf 63).map obs)
        (show Reach ((varsOf 63).map obs) 0 ((varsOf 63).map obs) from rfl) hsup
    have hlo := hLow q next hq hav
    have hwEval : ∀ x : Fin 6 → Bool, Circuit.eval ⟨wit, wo⟩ (List.ofFn x) = Nat.testBit T6 (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
      intro x
      rw [← evalInput6_packInput6 x, hwEvalR (packInput6 x), testBit_rep64 T6 hT6lt (packInput6 x)]
      rw [evalInput6_packInput6 x, sum_eq_packInput6 x]
      have hlt64 : (packInput6 x).val < 64 := by
        have h0 := Bool.toNat_le (x 0); have h1 := Bool.toNat_le (x 1); have h2 := Bool.toNat_le (x 2)
        have h3 := Bool.toNat_le (x 3); have h4 := Bool.toNat_le (x 4); have h5 := Bool.toNat_le (x 5)
        simp only [packInput6]; omega
      rw [Nat.mod_eq_of_lt hlt64]
    have hcsz : C.size = C.gates.length := rfl
    refine ⟨⟨wit, wo⟩, hwMono, ?_, hwEval⟩
    change wit.length ≤ s
    omega
  · refine ⟨C, ?_, hsize, heval⟩
    intro g hg
    have ⟨hm, hl⟩ := hlegal g hg
    refine ⟨?_, hl⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hm with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact (hn ⟨g, hg, h⟩).elim
inductive BT (α : Type) where
  | empty : BT α
  | leaf : α → BT α
  | node : BT α → BT α → BT α
def btGet {α : Type} (d : α) : BT α → Nat → α
  | .empty, _ => d
  | .leaf x, _ => x
  | .node l r, i => if i &&& 1 == 0 then btGet d l (i >>> 1) else btGet d r (i >>> 1)
def btSet {α : Type} : Nat → BT α → Nat → α → BT α
  | 0, _, _, v => .leaf v
  | d + 1, .empty, i, v =>
    if i &&& 1 == 0 then .node (btSet d .empty (i >>> 1) v) .empty
    else .node .empty (btSet d .empty (i >>> 1) v)
  | d + 1, .leaf x, i, v =>
    if i &&& 1 == 0 then .node (btSet d (.leaf x) (i >>> 1) v) .empty
    else .node .empty (btSet d (.leaf x) (i >>> 1) v)
  | d + 1, .node l r, i, v =>
    if i &&& 1 == 0 then .node (btSet d l (i >>> 1) v) r
    else .node l (btSet d r (i >>> 1) v)
def btUpdate {α : Type} (d0 : α) : Nat → BT α → Nat → (α → α) → BT α
  | 0, .leaf x, _, f => .leaf (f x)
  | 0, _, _, f => .leaf (f d0)
  | d + 1, .empty, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d .empty (i >>> 1) f) .empty
    else .node .empty (btUpdate d0 d .empty (i >>> 1) f)
  | d + 1, .leaf x, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d (.leaf x) (i >>> 1) f) .empty
    else .node .empty (btUpdate d0 d (.leaf x) (i >>> 1) f)
  | d + 1, .node l r, i, f =>
    if i &&& 1 == 0 then .node (btUpdate d0 d l (i >>> 1) f) r
    else .node l (btUpdate d0 d r (i >>> 1) f)
def btAll {α : Type} (P : α → Prop) : BT α → Prop
  | .empty => True
  | .leaf x => P x
  | .node l r => btAll P l ∧ btAll P r
lemma btAll_get {α : Type} {P : α → Prop} {d : α} {t : BT α} (ht : btAll P t) (hd : P d) (i : Nat) :
    P (btGet d t i) := by
  induction t generalizing i with
  | empty => exact hd
  | leaf x => exact ht
  | node l r ihl ihr =>
    unfold btGet
    split
    · exact ihl ht.1 _
    · exact ihr ht.2 _
lemma btAll_set {α : Type} {P : α → Prop} {depth : Nat} {t : BT α} {i : Nat} {v : α}
    (ht : btAll P t) (hv : P v) : btAll P (btSet depth t i v) := by
  induction depth generalizing t i with
  | zero => exact hv
  | succ d ih =>
    cases t with
    | empty =>
      unfold btSet; split
      · exact ⟨ih trivial, trivial⟩
      · exact ⟨trivial, ih trivial⟩
    | leaf x =>
      unfold btSet; split
      · exact ⟨ih ht, trivial⟩
      · exact ⟨trivial, ih ht⟩
    | node l r =>
      unfold btSet; split
      · exact ⟨ih ht.1, ht.2⟩
      · exact ⟨ht.1, ih ht.2⟩
lemma btAll_update {α : Type} {P : α → Prop} {d0 : α} {depth : Nat} {t : BT α} {i : Nat} {f : α → α}
    (ht : btAll P t) (hd0 : P d0) (hf : ∀ x, P x → P (f x)) : btAll P (btUpdate d0 depth t i f) := by
  induction depth generalizing t i with
  | zero =>
    cases t with
    | leaf x => exact hf x ht
    | empty => exact hf d0 hd0
    | node _ _ => exact hf d0 hd0
  | succ d ih =>
    cases t with
    | empty =>
      unfold btUpdate; split
      · exact ⟨ih trivial, trivial⟩
      · exact ⟨trivial, ih trivial⟩
    | leaf x =>
      unfold btUpdate; split
      · exact ⟨ih ht, trivial⟩
      · exact ⟨trivial, ih ht⟩
    | node l r =>
      unfold btUpdate; split
      · exact ⟨ih ht.1, ht.2⟩
      · exact ⟨ht.1, ih ht.2⟩
def btOfList {α : Type} (depth : Nat) (l : List α) : BT α :=
  (l.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) (0, BT.empty)).2
lemma btAll_ofList {α : Type} {P : α → Prop} {depth : Nat} {l : List α}
    (h : ∀ x ∈ l, P x) : btAll P (btOfList depth l) := by
  unfold btOfList
  have hgo : ∀ (xs : List α) (acc : Nat × BT α),
      (∀ x ∈ xs, P x) → btAll P acc.2 →
      btAll P (xs.foldl (fun p x => (p.1 + 1, btSet depth p.2 p.1 x)) acc).2 := by
    intro xs
    induction xs with
    | nil => intro acc _ hacc; exact hacc
    | cons x xs ih =>
      intro acc hx hacc
      exact ih (acc.1 + 1, btSet depth acc.2 acc.1 x)
        (fun y hy => hx y (List.mem_cons_of_mem _ hy))
        (btAll_set hacc (hx x (List.mem_cons_self ..)))
  exact hgo l (0, BT.empty) h trivial
def fastBitMask (z o i : Nat) : Nat :=
  if z.testBit i then ALL128 ^^^ VAR i else if o.testBit i then VAR i else ALL128
def subcubeFast (z o : Nat) : Nat :=
  fastBitMask z o 0 &&& fastBitMask z o 1 &&& fastBitMask z o 2 &&&
  fastBitMask z o 3 &&& fastBitMask z o 4 &&& fastBitMask z o 5 &&& fastBitMask z o 6
lemma fastBitMask_testBit (z o i : Nat) (hi : i < 7) (r : Row) :
    (fastBitMask z o i).testBit r.val =
      (if z.testBit i then !(r.val.testBit i) else if o.testBit i then r.val.testBit i else true) := by
  have hall : ALL128.testBit r.val = true := by
    simp only [ALL128]; have hr := r.isLt; simpa [hr] using Nat.testBit_two_pow_sub_one 128 r.val
  have hvar : (VAR i).testBit r.val = r.val.testBit i := var_testBit ⟨i, hi⟩ r
  unfold fastBitMask
  split
  · simp [Nat.testBit_xor, hall, hvar]
  · split
    · exact hvar
    · exact hall
lemma subcubeFast_eq_subcube (z o : Nat) (hz : z < 128) (ho : o < 128) (hzo : (z &&& o) = 0) :
    subcubeFast z o = subcube z o := by
  apply Nat.eq_of_testBit_eq; intro r
  by_cases hr : r < 128
  · have hsub : (subcube z o).testBit r = ((r &&& z == 0) && (r &&& o == o)) := by
      unfold subcube; rw [testBit_foldr_bits]; simp [hr]
    rw [hsub]
    unfold subcubeFast
    simp only [Nat.testBit_and,
      fastBitMask_testBit z o 0 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 1 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 2 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 3 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 4 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 5 (by decide) ⟨r, hr⟩,
      fastBitMask_testBit z o 6 (by decide) ⟨r, hr⟩]
    have hbit (i : Nat) (hi : i < 7) :
        ((r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i) ↔
          (if z.testBit i then !r.testBit i else if o.testBit i then r.testBit i else true) = true := by
      have hzi : (z.testBit i && o.testBit i) = false := by
        have := congrArg (fun x => x.testBit i) hzo; simpa [Nat.testBit_and] using this
      simp only [Nat.testBit_and]
      cases hz' : z.testBit i <;> cases ho' : o.testBit i <;> cases hr' : r.testBit i <;> simp_all
    have heq_iff : (((r &&& z == 0) && (r &&& o == o)) = true) ↔
        ∀ i < 7, (r &&& z).testBit i = false ∧ (r &&& o).testBit i = o.testBit i := by
      simp only [Bool.and_eq_true, beq_iff_eq]
      constructor
      · rintro ⟨h1, h2⟩ i _; rw [h1, h2, Nat.zero_testBit]; exact ⟨rfl, rfl⟩
      · intro h
        constructor
        · apply Nat.eq_of_testBit_eq; intro i
          rw [Nat.zero_testBit]
          by_cases hi : i < 7
          · exact (h i hi).1
          · have hzf : z.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hz (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
            simp [Nat.testBit_and, hzf]
        · apply Nat.eq_of_testBit_eq; intro i
          by_cases hi : i < 7
          · exact (h i hi).2
          · have hof : o.testBit i = false := Nat.testBit_eq_false_of_lt (lt_of_lt_of_le ho (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 7 ≤ i)))
            simp [Nat.testBit_and, hof]
    apply Bool.eq_iff_iff.mpr
    rw [heq_iff]
    simp only [Bool.and_eq_true]
    constructor
    · intro h i hi
      have := hbit i hi
      interval_cases i <;> tauto
    · intro h
      refine ⟨⟨⟨⟨⟨⟨(hbit 0 (by decide)).mp (h 0 (by decide)), (hbit 1 (by decide)).mp (h 1 (by decide))⟩,
        (hbit 2 (by decide)).mp (h 2 (by decide))⟩, (hbit 3 (by decide)).mp (h 3 (by decide))⟩,
        (hbit 4 (by decide)).mp (h 4 (by decide))⟩, (hbit 5 (by decide)).mp (h 5 (by decide))⟩,
        (hbit 6 (by decide)).mp (h 6 (by decide))⟩
  · have hlt_f (i : Nat) : (fastBitMask z o i).testBit r = false := by
      have hle : 128 ≤ r := by omega
      have ha : ALL128 < 2^128 := by decide
      have hv : VAR i < 2^128 := by
        unfold VAR; rcases i with _ | _ | _ | _ | _ | _ | _ | _
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · decide
        · change (0 : Nat) < 2^128; decide
      have hlt_m : fastBitMask z o i < 2^128 := by
        unfold fastBitMask; split
        · exact Nat.xor_lt_two_pow ha hv
        · split; exact hv; exact ha
      exact Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hlt_m (Nat.pow_le_pow_right (by decide : 0 < 2) hle))
    have hsub : (subcube z o).testBit r = false := by
      unfold subcube; rw [testBit_foldr_bits]; simp [hr]
    rw [hsub]
    unfold subcubeFast
    simp only [Nat.testBit_and, hlt_f]
    rfl
lemma slice_fast_of {z o zDrop raw T freeRoots qRoots qGoal qL lEss sliceL}
    (ok : sliceCheck z o zDrop raw T freeRoots qRoots qGoal qL lEss sliceL = true)
    (hPrior : qGoal ≠ 0 → Lower qRoots qGoal qL) :
    Slice raw T (subcubeFast z o) sliceL := by
  have ok2 := ok
  simp only [sliceCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ok2
  rw [subcubeFast_eq_subcube z o ok2.1.1.1.1.1.1 ok2.1.1.1.1.1.2 ok2.1.1.1.1.2]
  exact slice_of ok hPrior
lemma slice_fast_direct {z o zDead raw T qRoots qGoal qL}
    (ok : sliceDirectCheck z o zDead raw T qRoots qGoal = true)
    (hPrior : Lower qRoots qGoal qL) :
    Slice raw T (subcubeFast z o) qL := by
  have ok2 := ok
  simp only [sliceDirectCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at ok2
  rw [subcubeFast_eq_subcube z o ok2.1.1.1.1.1.1.1.1 ok2.1.1.1.1.1.1.1.2 ok2.1.1.1.1.1.1.2]
  exact slice_direct ok hPrior
def hashWs64 (ws : List Nat) : Nat :=
  (ws.foldl (fun h w => h + (w % 1000003) * 31) 0) &&& 63
def bucketContainsBT (bks : BT (List (List Nat))) (ws : List Nat) : Bool :=
  let s := sortNats ws
  (btGet [] bks (hashWs64 s)).contains s
def closeChildBT (pools : List BoundPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (rest : List Nat) (op : Choice) : Bool :=
  let ws := choiceVal op :: rest
  pools.any (fun c => scalarPoolCut c k rest op) ||
    autos.any (fun sw => bucketContainsBT prevBks (ws.map (permWord sw)))
lemma closeChildBT_sound {raw T pools autos prevBks k rest op}
    (hT : T < 2^128)
    (hPools : ∀ c ∈ pools, ValidPool raw T c)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun b => ∀ xs ∈ b, Impossible T k xs.toFinset) prevBks)
    (nd : (choiceVal op :: rest).Nodup)
    (hlt : ∀ x ∈ choiceVal op :: rest, x < 2^128)
    (h : closeChildBT pools autos prevBks k rest op = true) :
    Impossible T k (choiceVal op :: rest).toFinset := by
  simp only [closeChildBT, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨c, hc, hcut⟩ | ⟨sw, hsw, hhit⟩
  · exact scalarPoolCut_sound (hPools c hc) nd hcut
  · unfold bucketContainsBT at hhit
    have hmem := List.contains_iff_mem.mp hhit
    have hb : ∀ xs ∈ btGet [] prevBks (hashWs64 (sortNats ((choiceVal op :: rest).map (permWord sw)))),
        Impossible T k xs.toFinset :=
      btAll_get hPrev (fun _ hx => (List.not_mem_nil hx).elim) _
    have himp := hb _ hmem
    rw [sortNats_toFinset] at himp
    have ⟨hsv, hfix⟩ := hAutos sw hsw
    have hvr : swapsValid sw.reverse = true := by simp only [swapsValid, List.all_reverse]; exact hsv
    have hinv_row_gen : ∀ (l : List (Nat × Nat)), swapsValid l = true →
        ∀ r : Row, permRow l.reverse (permRow l r) = r := by
      intro l hl
      induction l with
      | nil => intro r; rfl
      | cons p ps ih =>
        simp only [swapsValid, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hl
        intro r
        have h1 : permRow (p :: ps).reverse (permRow (p :: ps) r) =
            swapRow p.1 p.2 (permRow ps.reverse (permRow ps (swapRow p.1 p.2 r))) := by
          simp [permRow, List.reverse_cons, List.foldl_append]
        rw [h1, ih hl.2, swapRow_invol p.1 p.2 (by omega) hl.1.2]
    have hinv_row2 : ∀ r : Row, permRow sw (permRow sw.reverse r) = r := by
      simpa using hinv_row_gen sw.reverse hvr
    have hinv_w : ∀ x : Nat, x < 2^128 → permWord sw.reverse (permWord sw x) = x := by
      intro x hx
      have h1 := permWord_eq_renameW sw hsv x hx
      have h2 := permWord_eq_renameW sw.reverse hvr (permWord sw x) (h1 ▸ renameW_lt _ x)
      rw [h2, h1]
      apply Nat.eq_of_testBit_eq; intro r
      by_cases hrr : r < 128
      · rw [testBit_renameW _ _ ⟨r, hrr⟩, testBit_renameW, hinv_row2]
      · rw [Nat.testBit_eq_false_of_lt (lt_of_lt_of_le (renameW_lt _ _) (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega))),
            Nat.testBit_eq_false_of_lt (lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide : 0 < 2) (by omega)))]
    have hfixr : permWord sw.reverse T = T := by
      have := hinv_w T hT; rwa [hfix] at this
    have hmap_lt : ∀ a ∈ (choiceVal op :: rest).map (permWord sw), a < 2^128 := by
      intro a ha
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
      rw [permWord_eq_renameW sw hsv x (hlt x hx)]
      exact renameW_lt _ x
    have hrot := rotate_impossible himp sw.reverse hvr hT hfixr hmap_lt
    have hback : (((choiceVal op :: rest).map (permWord sw)).map (permWord sw.reverse)) = (choiceVal op :: rest) := by
      rw [List.map_map]
      conv_rhs => rw [← List.map_id (choiceVal op :: rest)]
      exact List.map_congr_left fun x hx => hinv_w x (hlt x hx)
    rwa [hback] at hrot
abbrev FastPool := BoundPool × List Nat × Nat
def prepPool (vals : List Nat) (c : BoundPool) : Option FastPool :=
  let miss := vals.filter (fun w => !availM c.dom c.pm w)
  if miss.length > 2 then none
  else some (c, miss, vals.countP (isConstM c.dom))
def fastPoolCut (fp : FastPool) (k : Nat) (a b d : Nat) (ka kb : Bool) : Bool :=
  let c := fp.1
  let miss := fp.2.1
  let totC := fp.2.2
  if !miss.all (fun m => (!ka && m == a) || (!kb && m == b)) then false
  else
    let dropA := if !ka && isConstM c.dom a then 1 else 0
    let dropB := if !kb && isConstM c.dom b then 1 else 0
    let z := bin d a b
    let cRest := totC - dropA - dropB + (if isConstM c.dom z then 1 else 0)
    let zIn := availM c.dom c.pm z
    let extra := if zIn then 0 else 1
    decide (k + c.paid + extra < c.lb + cRest) && (zIn || choiceOK c.dom c.pm (d, a, b))
lemma countP_erase {α : Type} [BEq α] [LawfulBEq α] (p : α → Bool) {l : List α} {x : α} (hx : x ∈ l) :
    (l.erase x).countP p + (if p x then 1 else 0) = l.countP p := by
  have hp := List.perm_cons_erase hx
  have h1 := List.Perm.countP_eq p hp
  simp only [List.countP_cons] at h1
  omega
lemma countP_delTwo_fst (p : Nat → Bool) {ws : List Decor} {a b : Decor}
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1) (ka kb : Bool) :
    ((delTwo ws a b ka kb).map Prod.fst).countP p =
      (ws.map Prod.fst).countP p - (if !ka && p a.1 then 1 else 0) - (if !kb && p b.1 then 1 else 0) := by
  have hne : a ≠ b := fun e => hab (congrArg Prod.fst e)
  have hmap_erase : ∀ (l : List Decor) (x : Decor), (l.map Prod.fst).Nodup → x ∈ l →
      (l.erase x).map Prod.fst = (l.map Prod.fst).erase x.1 := by
    intro l x hnd hx
    induction l with
    | nil => simp at hx
    | cons y ys ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      by_cases hyx : y = x
      · subst hyx; simp
      · have hne1 : y.1 ≠ x.1 := by
          intro eq; apply hnd.1; rw [eq]
          exact List.mem_map_of_mem ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx))
        have h1 : (y == x) = false := beq_false_of_ne hyx
        have h2 : (y.1 == x.1) = false := beq_false_of_ne hne1
        simp only [List.erase_cons, h1, h2, List.map_cons]
        exact congrArg (y.1 :: ·) (ih hnd.2 ((List.mem_cons.mp hx).resolve_left (Ne.symm hyx)))
  cases ka <;> cases kb
  · have hbm : b ∈ ws.erase a := (List.mem_erase_of_ne hne.symm).mpr hb
    have hnd1 : ((ws.erase a).map Prod.fst).Nodup := ((List.erase_sublist).map Prod.fst).nodup nd
    change (((ws.erase a).erase b).map Prod.fst).countP p = _
    rw [hmap_erase _ b hnd1 hbm, hmap_erase ws a nd ha]
    have ha1 : a.1 ∈ ws.map Prod.fst := List.mem_map_of_mem ha
    have hb1 : b.1 ∈ (ws.map Prod.fst).erase a.1 := (List.mem_erase_of_ne hab.symm).mpr (List.mem_map_of_mem hb)
    have c1 := countP_erase p ha1
    have c2 := countP_erase p hb1
    cases hpa : p a.1 <;> cases hpb : p b.1 <;> simp [hpa, hpb] at c1 c2 ⊢ <;> omega
  · change ((ws.erase a).map Prod.fst).countP p = _
    rw [hmap_erase ws a nd ha]
    have c1 := countP_erase p (List.mem_map_of_mem (f := Prod.fst) ha)
    cases hpa : p a.1 <;> simp [hpa] at c1 ⊢ <;> omega
  · change ((ws.erase b).map Prod.fst).countP p = _
    rw [hmap_erase ws b nd hb]
    have c1 := countP_erase p (List.mem_map_of_mem (f := Prod.fst) hb)
    cases hpb : p b.1 <;> simp [hpb] at c1 ⊢ <;> omega
  · simp [delTwo, delOne]
lemma fastPoolCut_sound {raw T ws a b d ka kb k c fp}
    (hP : ValidPool raw T c) (hprep : prepPool (ws.map Prod.fst) c = some fp)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws) (hab : a.1 ≠ b.1)
    (ndc : (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).Nodup)
    (hcut : fastPoolCut fp k a.1 b.1 d ka kb = true) :
    Impossible T k (bin d a.1 b.1 :: (delTwo ws a b ka kb).map Prod.fst).toFinset := by
  unfold prepPool at hprep
  dsimp only at hprep
  split at hprep
  · simp at hprep
  · simp only [Option.some.injEq] at hprep
    subst hprep
    unfold fastPoolCut at hcut
    dsimp only at hcut
    split at hcut
    · simp at hcut
    · next hmiss =>
      simp only [Bool.not_eq_true', Bool.not_eq_false, List.all_eq_true, List.mem_filter, Bool.not_eq_true'] at hmiss
      have hsub := (delTwo_sub ws a b ka kb).map Prod.fst
      have h_all_avail : ((delTwo ws a b ka kb).map Prod.fst).all (availM c.dom c.pm) = true := by
        rw [List.all_eq_true]; intro w hw
        by_contra hna
        have hnf : availM c.dom c.pm w = false := Bool.eq_false_iff.mpr hna
        have hmem_ws : w ∈ ws.map Prod.fst := hsub.subset hw
        have hm := hmiss w ⟨hmem_ws, hnf⟩
        simp only [Bool.or_eq_true, Bool.and_eq_true, Bool.not_eq_true', beq_iff_eq] at hm
        have hne_ab : a ≠ b := fun e => hab (congrArg Prod.fst e)
        have hnot_in : ∀ (x : Decor) (kx : Bool), kx = false → x ∈ ws → x.1 ∉ (delTwo ws a b ka kb).map Prod.fst → True := fun _ _ _ _ _ => trivial
        have hmem_del : ∀ u ∈ delTwo ws a b ka kb, u.1 = w → (ka = false → u ≠ a) ∧ (kb = false → u ≠ b) := by
          intro u hu _
          constructor
          · intro hka; subst hka
            have hsub1 : (delTwo ws a b false kb).Sublist (ws.erase a) := by
              cases kb <;> simp [delTwo, delOne, List.erase_sublist]
            have hu1 := hsub1.subset hu
            intro heq; subst heq
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            exact List.Nodup.not_mem_erase hnd_ws hu1
          · intro hkb; subst hkb
            have hnd_ws : ws.Nodup := List.Nodup.of_map Prod.fst nd
            have hnd2 : (delOne ws a ka).Nodup := by cases ka; exact hnd_ws.erase a; exact hnd_ws
            have h2 := List.Nodup.not_mem_erase hnd2 (a := b)
            exact fun heq => h2 (heq ▸ hu)
        obtain ⟨u, hu, huw⟩ := List.mem_map.mp hw
        have ⟨hna', hnb'⟩ := hmem_del u hu huw
        rcases hm with ⟨hka, hwa⟩ | ⟨hkb, hwb⟩
        · have hu_eq : u = a := unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) ha (huw.trans hwa)
          exact hna' hka hu_eq
        · have hu_eq : u = b := unique_fst nd ((delTwo_sub ws a b ka kb).subset hu) hb (huw.trans hwb)
          exact hnb' hkb hu_eq
      have hcnt := countP_delTwo_fst (isConstM c.dom) nd ha hb hab ka kb
      apply scalarPoolCut_sound (op := (d, a.1, b.1)) (rest := (delTwo ws a b ka kb).map Prod.fst) hP ndc
      unfold scalarPoolCut
      simp only [choiceVal, h_all_avail, Bool.true_and, Bool.and_true, List.countP_cons,
        Bool.and_eq_true, decide_eq_true_eq] at hcut ⊢
      rw [hcnt]
      rcases hcut with ⟨h1, h2⟩
      refine ⟨?_, ?_⟩
      · cases hz : availM c.dom c.pm (bin d a.1 b.1) <;>
          cases hcz : isConstM c.dom (bin d a.1 b.1) <;>
          simp only [hz, hcz, Bool.not_true, Bool.not_false, Bool.toNat_true, Bool.toNat_false,
            Bool.and_eq_true, Bool.false_eq_true, ite_true, ite_false] at h1 ⊢ <;> omega
      · cases hz : availM c.dom c.pm (bin d a.1 b.1) <;>
          simp only [hz, Bool.not_true, Bool.not_false, Bool.true_or, Bool.false_or] at h2 ⊢ <;>
          exact h2
def evalMoveBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat)))
    (d : Nat) (a b z : Decor) (ka kb : Bool) : Bool :=
  let len := 1 + (n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len > cap then true else
    let rs := restCov cov (dsep a) (dsep b) ka kb
    if ((rs ||| dsep z) &&& fmask) != fmask then true else
    if z.1 == 0 || ws.any (fun v => v.1 == z.1) then true else
    if fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) then true else
      let rest := (delTwo ws a b ka kb).map Prod.fst
      closeChildBT [] autos prevBks (cap - 1) rest (d, a.1, b.1)
def testPairBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (a b : Decor) (d : Nat) : Bool :=
  let z := dbin d a b
  let go := evalMoveBT cap n fmask ws cov fpools autos prevBks d a b z
  go false false && go true false && go false true && go true true
def testAllBT (cap n fmask : Nat) (ws : List Decor) (cov : Cov)
    (fpools : List FastPool) (autos : List (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) : List Decor → Bool
  | [] => true
  | a :: bs =>
    bs.all (fun b => [0, 1, 2, 3].all (testPairBT cap n fmask ws cov fpools autos prevBks a b)) &&
      testAllBT cap n fmask ws cov fpools autos prevBks bs
lemma evalMoveBT_sound {raw T pos neg ws fpools autos prevBks cap a b d ka kb}
    (hT : T < 2^128) (gp : goodPairs T pos neg) (hf : ∀ w ∈ ws, faithful pos neg w)
    (nd : (ws.map Prod.fst).Nodup) (hlt : ∀ w ∈ ws, w.1 < 2^128)
    (ha : a ∈ ws) (hb : b ∈ ws) (ne : a ≠ b) (hcap : 0 < cap) (_hd : d < 4)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (hnz : bin d a.1 b.1 ≠ 0) (hfr : bin d a.1 b.1 ∉ ws.map Prod.fst)
    (test : evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d a b (dbin d a b) ka kb = true) :
    Impossible T (cap - 1) ((dbin d a b :: delTwo ws a b ka kb).map Prod.fst).toFinset := by
  let z := dbin d a b
  let rest := delTwo ws a b ka kb
  let child := (z :: rest).map Prod.fst
  have sub : rest.Sublist ws := delTwo_sub ws a b ka kb
  have ndc : child.Nodup := by
    simp only [child, List.map_cons, List.nodup_cons]
    exact ⟨fun hm => hfr ((sub.map Prod.fst).subset hm), (sub.map Prod.fst).nodup nd⟩
  have hltc : ∀ x ∈ child, x < 2^128 := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact bin_lt d a.1 b.1 (hlt a ha) (hlt b hb)
    · obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hx; exact hlt w (sub.subset hw)
  have hnz_b : (z.1 == 0) = false := beq_false_of_ne hnz
  have hfr_b : (ws.any (fun v => v.1 == z.1)) = false := by
    rw [Bool.eq_false_iff]; intro h; obtain ⟨v, hv, heq⟩ := List.any_eq_true.mp h
    have hvz : v.1 = bin d a.1 b.1 := beq_iff_eq.mp heq
    exact hfr (hvz ▸ List.mem_map_of_mem hv)
  have hleq : 1 + (ws.length - (if ka then 0 else 1) - (if kb then 0 else 1)) = child.length := by
    have hdl := delTwo_len ws a b ka kb ha hb ne
    simp only [child, rest, List.length_map, List.length_cons]
    omega
  intro k hk h
  have hsz := live_size h
  change child.toFinset.card ≤ k + 1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have hlen : child.length ≤ cap := by omega
  have hcov := cov_required gp (ws := z :: rest)
    (fun w hw => by rcases List.mem_cons.mp hw with rfl | hw; exact faithful_bin d (hf a ha) (hf b hb); exact hf w (sub.subset hw)) h
  have hcov_eq : (coverage (z :: rest)).1 = restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z := by
    change dsep z ||| (coverage rest).1 = _
    rw [cov_delTwo a b ha hb ne ka kb, Nat.or_comm]
  rw [hcov_eq] at hcov
  have hcov_b : (((restCov (coverage ws) (dsep a) (dsep b) ka kb ||| dsep z) &&& fullMask pos.length) != fullMask pos.length) = false := by
    simp [hcov]
  unfold evalMoveBT at test
  dsimp only at test
  have hnotgt : ¬(child.length > cap) := by omega
  dsimp only [z] at hcov_b hnz_b hfr_b
  simp only [hleq, hnotgt, ↓reduceIte, hcov_b, hnz_b, hfr_b, Bool.false_or, Bool.false_eq_true] at test
  have hab1 : a.1 ≠ b.1 := fun eq => ne (unique_fst nd ha hb eq)
  by_cases hfp : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = true
  · obtain ⟨fp, hmem, hcut⟩ := List.any_eq_true.mp hfp
    have ⟨hv, hpr⟩ := hPools fp hmem
    exact fastPoolCut_sound hv hpr nd ha hb hab1 ndc hcut k hk h
  · have hfp_f : fpools.any (fun fp => fastPoolCut fp (cap - 1) a.1 b.1 d ka kb) = false := Bool.eq_false_iff.mpr hfp
    simp only [hfp_f, Bool.false_eq_true, ↓reduceIte] at test
    exact closeChildBT_sound (raw := raw) (op := (d, a.1, b.1)) (rest := rest.map Prod.fst) hT (fun _ hm => (List.not_mem_nil hm).elim) hAutos hPrev ndc hltc test k hk h
lemma testAllBT_pair {cap n fmask ws cov fpools autos prevBks l}
    (h : testAllBT cap n fmask ws cov fpools autos prevBks l = true)
    {a b : Decor} (ha : a ∈ l) (hb : b ∈ l) (ne : a ≠ b) :
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks a b d = true) ∨
    (∀ d < 4, testPairBT cap n fmask ws cov fpools autos prevBks b a d = true) := by
  induction l with
  | nil => simp at ha
  | cons w l ih =>
    simp only [testAllBT, Bool.and_eq_true, List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | ha'
    · have bm := (List.mem_cons.mp hb).resolve_left ne.symm
      exact Or.inl fun d hd => h.1 b bm d (by interval_cases d <;> decide)
    · rcases List.mem_cons.mp hb with rfl | hb'
      · exact Or.inr fun d hd => h.1 a ha' d (by interval_cases d <;> decide)
      · exact ih h.2 ha' hb'
lemma nodeBT_sound {raw T pos neg ws fpools autos prevBks cap}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hf : ∀ w ∈ ws, faithful pos neg w) (nd : (ws.map Prod.fst).Nodup)
    (hlt : ∀ w ∈ ws, w.1 < 2^128) (out : T ∉ ws.map Prod.fst)
    (hPools : ∀ fp ∈ fpools, ValidPool raw T fp.1 ∧ prepPool (ws.map Prod.fst) fp.1 = some fp)
    (hAutos : ∀ sw ∈ autos, swapsValid sw = true ∧ permWord sw T = T)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (cap - 1) xs.toFinset) prevBks)
    (checks : cap = 0 ∨ testAllBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks ws = true) :
    Impossible T cap (ws.map Prod.fst).toFinset := by
  rcases checks with rfl | hcheck
  · intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  by_cases h0 : cap = 0
  · subst h0
    intro k hk h
    have hk0 : k = 0 := by omega
    subst hk0
    obtain ⟨hS, _⟩ := h
    exact out (List.mem_toFinset.mp (hS ▸ Finset.mem_singleton_self T))
  have hcap : 0 < cap := by omega
  apply enum_step nd out
  intro a ha b hb d hd ka kb ne hnz hfr _
  obtain ⟨a, haW, rfl⟩ := List.mem_map.mp ha
  obtain ⟨b, hbW, rfl⟩ := List.mem_map.mp hb
  have ab : a ≠ b := fun e => ne (congrArg Prod.fst e)
  have one (x y : Decor) (d' : Nat) (hd' : d' < 4) (hx : x ∈ ws) (hy : y ∈ ws) (nxy : x.1 ≠ y.1)
      (k1 k2 : Bool) (hnz' : bin d' x.1 y.1 ≠ 0) (hfr' : bin d' x.1 y.1 ∉ ws.map Prod.fst)
      (ht : testPairBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks x y d' = true) :
      Impossible T (cap - 1) (childTwo (ws.map Prod.fst) x.1 y.1 d' k1 k2).toFinset := by
    rw [← delTwo_map_toFinset nd hx hy nxy d' k1 k2]
    have hem : evalMoveBT cap ws.length (fullMask pos.length) ws (coverage ws) fpools autos prevBks d' x y (dbin d' x y) k1 k2 = true := by
      simp only [testPairBT, Bool.and_eq_true] at ht
      cases k1 <;> cases k2 <;> first | exact ht.1.1.1 | exact ht.1.2 | exact ht.1.1.2 | exact ht.2
    exact evalMoveBT_sound hT gp hf nd hlt hx hy (fun e => nxy (congrArg Prod.fst e)) hcap hd' hPools hAutos hPrev hnz' hfr' hem
  rcases testAllBT_pair hcheck haW hbW ab with hh | hh
  · exact one a b d hd haW hbW ne ka kb hnz hfr (hh d hd)
  · rw [childTwo_swap _ nd _ _ d hd]
    have hfl := flipOp_lt hd
    exact one b a (flipOp d) hfl hbW haW ne.symm kb ka
      (bin_comm_flip d hd a.1 b.1 ▸ hnz) (bin_comm_flip d hd a.1 b.1 ▸ hfr) (hh _ hfl)
def buildWiresBT (depth : Nat) (base : List Decor) (steps : List (Nat × Nat × Nat)) : BT Decor :=
  let init := (base.length, btOfList depth base)
  (steps.foldl (fun p s =>
    let a := btGet (0, 0, 0) p.2 s.2.1
    let b := btGet (0, 0, 0) p.2 s.2.2
    (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 a b))) init).2
lemma buildWiresBT_faithful {depth pos neg base steps}
    (hbase : ∀ x ∈ base, faithful pos neg x ∧ x.1 < 2^128) :
    btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) (buildWiresBT depth base steps) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  unfold buildWiresBT
  have h0 : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) (btOfList depth base) := btAll_ofList hbase
  have hgo : ∀ (ss : List (Nat × Nat × Nat)) (acc : Nat × BT Decor),
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) acc.2 →
      btAll (fun x => faithful pos neg x ∧ x.1 < 2^128)
        (ss.foldl (fun p s => (p.1 + 1, btSet depth p.2 p.1 (dbin s.1 (btGet (0, 0, 0) p.2 s.2.1) (btGet (0, 0, 0) p.2 s.2.2)))) acc).2 := by
    intro ss
    induction ss with
    | nil => intro acc hacc; exact hacc
    | cons s ss ih =>
      intro acc hacc
      have ha := btAll_get hacc hdef s.2.1
      have hb := btAll_get hacc hdef s.2.2
      exact ih _ (btAll_set hacc ⟨faithful_bin s.1 ha.1 hb.1, bin_lt s.1 _ _ ha.2 hb.2⟩)
  exact hgo steps (base.length, btOfList depth base) h0
def buildPoolsBT (pdepth : Nat) (W : BT Decor) (raw : List Nat) (slices : BT (Option (Nat × Nat)))
    (pspecs : List PoolSpec) : BT (Option BoundPool) :=
  btOfList pdepth (pspecs.map fun (slIdx, chIdxs) =>
    match btGet none slices slIdx with
    | none => none
    | some (dom, lb) =>
      let cs := chIdxs.map fun (op, ia, ib) => (op, (btGet (0, 0, 0) W ia).1, (btGet (0, 0, 0) W ib).1)
      materialize raw cs dom lb)
lemma buildPoolsBT_sound {pdepth} {W : BT Decor} {raw T} {slices : BT (Option (Nat × Nat))} {pspecs : List PoolSpec}
    (hSlices : btAll (fun o => ∀ p, o = some p → Slice raw T p.1 p.2) slices) :
    btAll (fun o => ∀ c, o = some c → ValidPool raw T c) (buildPoolsBT pdepth W raw slices pspecs) := by
  apply btAll_ofList
  intro o ho c hc
  obtain ⟨⟨slIdx, chIdxs⟩, _, hmat⟩ := List.mem_map.mp ho
  dsimp only at hmat
  have hsl := btAll_get (d := none) hSlices (fun _ h => by simp at h) slIdx
  cases heq : btGet none slices slIdx with
  | none => rw [heq] at hmat; exact absurd (hmat.trans hc) (by simp)
  | some sl =>
    rw [heq] at hmat
    exact materialize_sound (hsl sl heq) (hmat.trans hc)
def checkNodeBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (ns : NodeSpec) : Bool :=
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  let vals := ws.map Prod.fst
  let fpools := ns.2.1.filterMap fun pIdx =>
    match btGet none poolTable pIdx with
    | none => none
    | some c => prepPool vals c
  let nodeAutos := ns.2.2.map fun aIdx => btGet [] autosTable aIdx
  decide vals.Nodup && !(vals.contains T) &&
    (k == 0 || testAllBT k ws.length fmask ws (coverage ws) fpools nodeAutos prevBks ws)
def checkNodesBT (W : BT Decor) (T fmask : Nat)
    (poolTable : BT (Option BoundPool)) (autosTable : BT (List (Nat × Nat)))
    (prevBks : BT (List (List Nat))) (k : Nat) (nodes : List NodeSpec) : Bool :=
  nodes.all (checkNodeBT W T fmask poolTable autosTable prevBks k)
lemma checkNodeBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k ns}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (ok : checkNodeBT W T (fullMask pos.length) poolTable autosTable prevBks k ns = true) :
    Impossible T k ((ns.1.map fun idx => (btGet (0, 0, 0) W idx).1).toFinset) := by
  have hdef : faithful pos neg (0, 0, 0) ∧ (0 : Nat) < 2^128 := ⟨faithful_zero pos neg, by decide⟩
  have hget (idx : Nat) : faithful pos neg (btGet (0, 0, 0) W idx) ∧ (btGet (0, 0, 0) W idx).1 < 2^128 :=
    btAll_get hW hdef idx
  unfold checkNodeBT at ok
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', List.contains_eq_mem, Bool.or_eq_true, beq_iff_eq] at ok
  let ws := ns.1.map fun idx => btGet (0, 0, 0) W idx
  have hmap : ws.map Prod.fst = ns.1.map fun idx => (btGet (0, 0, 0) W idx).1 := by simp [ws, List.map_map, Function.comp_def]
  rw [← hmap]
  apply nodeBT_sound hT gp
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).1)
    ok.1.1
    (fun w hw => by obtain ⟨idx, _, rfl⟩ := List.mem_map.mp hw; exact (hget idx).2)
    (of_decide_eq_false ok.1.2)
    (fun fp hfp => by
      obtain ⟨pIdx, _, hmat⟩ := List.mem_filterMap.mp hfp
      cases heq : btGet none poolTable pIdx with
      | none => simp [heq] at hmat
      | some c =>
        simp only [heq] at hmat
        have hvc := btAll_get hPoolTable (fun _ h => by simp at h) pIdx c heq
        have hfp_eq : fp.1 = c := by
          unfold prepPool at hmat
          dsimp only at hmat
          split at hmat
          · simp at hmat
          · simp only [Option.some.injEq] at hmat; rw [← hmat]
        rw [hfp_eq]
        exact ⟨hvc, hmat⟩)
    (fun sw hsw => by
      obtain ⟨aIdx, _, rfl⟩ := List.mem_map.mp hsw
      exact btAll_get hAutos ⟨rfl, rfl⟩ aIdx)
    hPrev ok.2
def nodeValsBT (W : BT Decor) (ns : NodeSpec) : List Nat :=
  sortNats (ns.1.map fun idx => (btGet (0, 0, 0) W idx).1)
def buildBucketsBT (W : BT Decor) (nodes : List NodeSpec) : BT (List (List Nat)) :=
  nodes.foldl (fun acc ns =>
    let xs := nodeValsBT W ns
    btUpdate [] 6 acc (hashWs64 xs) (fun b => if b.contains xs then b else xs :: b)) BT.empty
lemma buildBucketsBT_sound {W : BT Decor} {raw pos neg T poolTable autosTable prevBks k}
    {nodes : List NodeSpec}
    (hT : T < 2^128) (gp : goodPairs T pos neg)
    (hW : btAll (fun x => faithful pos neg x ∧ x.1 < 2^128) W)
    (hPoolTable : btAll (fun o => ∀ c, o = some c → ValidPool raw T c) poolTable)
    (hAutos : btAll (fun sw => swapsValid sw = true ∧ permWord sw T = T) autosTable)
    (hPrev : btAll (fun bk => ∀ xs ∈ bk, Impossible T (k - 1) xs.toFinset) prevBks)
    (hNodes : checkNodesBT W T (fullMask pos.length) poolTable autosTable prevBks k nodes = true) :
    btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (buildBucketsBT W nodes) := by
  have hmem : ∀ ns ∈ nodes, Impossible T k (nodeValsBT W ns).toFinset := fun ns hns => by
    unfold nodeValsBT; rw [sortNats_toFinset]
    exact checkNodeBT_sound hT gp hW hPoolTable hAutos hPrev (List.all_eq_true.mp hNodes ns hns)
  clear hNodes
  unfold buildBucketsBT
  have hinit : btAll (fun bk => ∀ xs ∈ bk, Impossible T k xs.toFinset) (BT.empty : BT (List (List Nat))) := trivial
  generalize (BT.empty : BT (List (List Nat))) = acc at hinit ⊢
  induction nodes generalizing acc with
  | nil => exact hinit
  | cons ns rest ih =>
    apply ih (fun x hx => hmem x (List.mem_cons_of_mem _ hx))
    apply btAll_update hinit (fun _ h => (List.not_mem_nil h).elim)
    intro b hb ys hys
    split at hys
    · exact hb ys hys
    · rcases List.mem_cons.mp hys with rfl | hys'
      · exact hmem ns (List.mem_cons_self ..)
      · exact hb ys hys'
lemma lower_of_forestBT {roots T cap} {topBks : BT (List (List Nat))} {essPairs : List (Nat × Nat × Nat)}
    (ok : forestRootCheck roots T essPairs = true)
    (hTop : btAll (fun bk => ∀ xs ∈ bk, Impossible T cap xs.toFinset) topBks)
    (hRoot : bucketContainsBT topBks roots = true) :
    Lower roots T (cap + 1) := by
  simp only [forestRootCheck, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, beq_iff_eq] at ok
  obtain ⟨⟨hT, hR⟩, hess⟩ := ok
  have ⟨p1, p2, p3⟩ := checkProper_sound hT
  have hR' := checkRoots_sound hR
  have hEss' : ∀ a ∈ roots, Essential T roots a := fun a ha => by
    obtain ⟨⟨v, r, s⟩, _, rfl, he⟩ := hess a ha
    exact checkEss1_sound he
  have hImp : Impossible T cap (sortNats roots).toFinset := by
    unfold bucketContainsBT at hRoot
    exact btAll_get hTop (fun _ h => (List.not_mem_nil h).elim) _ _ (List.contains_iff_mem.mp hRoot)
  rw [sortNats_toFinset] at hImp
  exact lower_of_impossible p1 p2 p3 hR' hEss' hImp
def G_0 : Nat := 0xfcfcc0c0fcfcc0c0fcfcc0c0fcfcc0c0
def R_0 : List Nat := varsOf 22
def pos_0 : List Nat := [6,6,18,18,20,20,6,18,20]
def neg_0 : List Nat := [4,2,16,2,16,4,16,4,2]
def fmask_0 : Nat := fullMask 9
def base_0 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0xcf,0x10a),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x173,0xa1),(0xffff0000ffff0000ffff0000ffff0000,0x1bc,0x54)]
def steps_0 : List (Nat × Nat × Nat) := []
def W_0 : BT Decor := buildWiresBT 2 base_0 steps_0
def autosL_0 : List (List (Nat × Nat)) := []
def autos_0 : BT (List (Nat × Nat)) := btOfList 1 autosL_0
def slicesL_0 : List (Option (Nat × Nat)) := []
def slices_0 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_0
def ps_0 : List PoolSpec := []
def P_0 : BT (Option BoundPool) := buildPoolsBT 1 W_0 R_0 slices_0 ps_0
lemma gp_0 : goodPairs G_0 pos_0 neg_0 := goodPairs_of (by decide +kernel)
lemma base_0_ok : ∀ x ∈ base_0, faithful pos_0 neg_0 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_0_ok : btAll (fun x => faithful pos_0 neg_0 x ∧ x.1 < 2^128) W_0 := buildWiresBT_faithful base_0_ok
set_option maxRecDepth 500000 in
lemma autos_0_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_0 = G_0) autos_0 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_0_ok : btAll (fun o => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) slices_0 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_0 G_0 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_0_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_0 G_0 c) P_0 := buildPoolsBT_sound slices_0_ok
def bk_0_init : BT (List (List Nat)) := BT.empty
lemma bk_0_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 (0 - 1) xs.toFinset) bk_0_init := trivial
def nodes_0_0 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_0_0 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_init 0 nodes_0_0 = true := by decide +kernel
def bk_0_0 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_0
set_option maxRecDepth 500000 in
lemma bk_0_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 0 xs.toFinset) bk_0_0 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_init_ok chk_0_0
def nodes_0_1 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_0_1 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_0 1 nodes_0_1 = true := by decide +kernel
def bk_0_1 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_1
set_option maxRecDepth 500000 in
lemma bk_0_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 1 xs.toFinset) bk_0_1 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_0_ok chk_0_1
def nodes_0_2 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_0_2 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_1 2 nodes_0_2 = true := by decide +kernel
def bk_0_2 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_2
set_option maxRecDepth 500000 in
lemma bk_0_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 2 xs.toFinset) bk_0_2 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_1_ok chk_0_2
def nodes_0_3 : List NodeSpec := [([0,1,2],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_0_3 : checkNodesBT W_0 G_0 fmask_0 P_0 autos_0 bk_0_2 3 nodes_0_3 = true := by decide +kernel
def bk_0_3 : BT (List (List Nat)) := buildBucketsBT W_0 nodes_0_3
set_option maxRecDepth 500000 in
lemma bk_0_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_0 3 xs.toFinset) bk_0_3 :=
  buildBucketsBT_sound (by decide) gp_0 W_0_ok P_0_ok autos_0_ok bk_0_2_ok chk_0_3
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_0_ok : forestRootCheck R_0 G_0 [(VAR 1,6,4),(VAR 2,6,2),(VAR 4,18,2)] = true := by decide +kernel
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_0_in : bucketContainsBT bk_0_3 R_0 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_0 : Lower R_0 G_0 4 := lower_of_forestBT root_0_ok bk_0_3_ok root_0_in
def G_1 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def R_1 : List Nat := varsOf 7
lemma low_1_ok : carryOK [(0,3),(0,4),(0,2),(0,1)] R_1 G_1 R_0 G_0 = true := by decide +kernel
lemma low_1 : Lower R_1 G_1 4 := carry_of low_1_ok low_0
def G_2 : Nat := 0xee88ee88ee88ee88ee88ee88ee88ee88
def R_2 : List Nat := varsOf 11
lemma low_2_ok : carryOK [(3,4),(0,2),(0,1)] R_2 G_2 R_0 G_0 = true := by decide +kernel
lemma low_2 : Lower R_2 G_2 4 := carry_of low_2_ok low_0
def G_3 : Nat := 0xeeee8888eeee8888eeee8888eeee8888
def R_3 : List Nat := varsOf 19
lemma low_3_ok : carryOK [(0,2),(0,1)] R_3 G_3 R_0 G_0 = true := by decide +kernel
lemma low_3 : Lower R_3 G_3 4 := carry_of low_3_ok low_0
def G_4 : Nat := 0xeeeeeeee88888888eeeeeeee88888888
def R_4 : List Nat := varsOf 35
lemma low_4_ok : carryOK [(4,5),(0,2),(0,1)] R_4 G_4 R_0 G_0 = true := by decide +kernel
lemma low_4 : Lower R_4 G_4 4 := carry_of low_4_ok low_0
def G_5 : Nat := 0xfaa0faa0faa0faa0faa0faa0faa0faa0
def R_5 : List Nat := varsOf 13
lemma low_5_ok : carryOK [(3,4),(0,1)] R_5 G_5 R_0 G_0 = true := by decide +kernel
lemma low_5 : Lower R_5 G_5 4 := carry_of low_5_ok low_0
def G_6 : Nat := 0xfafaa0a0fafaa0a0fafaa0a0fafaa0a0
def R_6 : List Nat := varsOf 21
lemma low_6_ok : carryOK [(0,1)] R_6 G_6 R_0 G_0 = true := by decide +kernel
lemma low_6 : Lower R_6 G_6 4 := carry_of low_6_ok low_0
def G_7 : Nat := 0xfafafafaa0a0a0a0fafafafaa0a0a0a0
def R_7 : List Nat := varsOf 37
lemma low_7_ok : carryOK [(4,5),(0,1)] R_7 G_7 R_0 G_0 = true := by decide +kernel
lemma low_7 : Lower R_7 G_7 4 := carry_of low_7_ok low_0
def G_8 : Nat := 0xfcc0fcc0fcc0fcc0fcc0fcc0fcc0fcc0
def R_8 : List Nat := varsOf 14
lemma low_8_ok : carryOK [(3,4)] R_8 G_8 R_0 G_0 = true := by decide +kernel
lemma low_8 : Lower R_8 G_8 4 := carry_of low_8_ok low_0
def G_9 : Nat := 0xfcfcfcfcc0c0c0c0fcfcfcfcc0c0c0c0
def R_9 : List Nat := varsOf 38
lemma low_9_ok : carryOK [(4,5)] R_9 G_9 R_0 G_0 = true := by decide +kernel
lemma low_9 : Lower R_9 G_9 4 := carry_of low_9_ok low_0
def G_10 : Nat := 0xffaaffaaaa00aa00ffaaffaaaa00aa00
def R_10 : List Nat := varsOf 41
lemma low_10_ok : carryOK [(4,5),(2,3),(0,1)] R_10 G_10 R_0 G_0 = true := by decide +kernel
lemma low_10 : Lower R_10 G_10 4 := carry_of low_10_ok low_0
def G_11 : Nat := 0xffccffcccc00cc00ffccffcccc00cc00
def R_11 : List Nat := varsOf 42
lemma low_11_ok : carryOK [(4,5),(2,3)] R_11 G_11 R_0 G_0 = true := by decide +kernel
lemma low_11 : Lower R_11 G_11 4 := carry_of low_11_ok low_0
def G_12 : Nat := 0xfff0fff0f000f000fff0fff0f000f000
def R_12 : List Nat := varsOf 44
lemma low_12_ok : carryOK [(4,5),(1,2),(1,3)] R_12 G_12 R_0 G_0 = true := by decide +kernel
lemma low_12 : Lower R_12 G_12 4 := carry_of low_12_ok low_0
def G_13 : Nat := 0xfc00c000fc00c000fc00c000fc00c000
def R_13 : List Nat := varsOf 30
lemma low_13_ok : liftCheck 0 8 R_13 G_13 R_0 G_0 [(VAR 3,14,6)] = true := by decide +kernel
lemma low_13 : Lower R_13 G_13 5 := lift_of low_13_ok low_0
def G_14 : Nat := 0xfcc0fcc0c000c000fcc0fcc0c000c000
def R_14 : List Nat := varsOf 46
def pos_14 : List Nat := [14,14,14,38,38,38,42,42,42,44,44,44,14,14,14,38,38,38,42,42,42,44,44,44]
def neg_14 : List Nat := [12,10,6,36,34,6,40,34,10,40,36,12,34,36,40,10,12,40,6,12,36,6,10,34]
def fmask_14 : Nat := fullMask 24
def base_14 : List Decor := [(0xcccccccccccccccccccccccccccccccc,0x1ff1ff,0xe491b6),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xe3fe3f,0x3d2c2d),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfc7fc7,0x4bcb43),(0xffffffff00000000ffffffff00000000,0xff8ff8,0x9276d8)]
def steps_14 : List (Nat × Nat × Nat) := [(0,0,1),(0,0,2),(3,4,2),(0,4,2),(0,1,2),(3,7,3)]
def W_14 : BT Decor := buildWiresBT 4 base_14 steps_14
def autosL_14 : List (List (Nat × Nat)) := [[],[(3,5)],[(1,2)],[(3,5),(1,2)],[(2,3)],[(2,5),(2,3)],[(1,2),(1,3)],[(2,5),(1,2),(1,3)],[(2,5),(1,3)]]
def autos_14 : BT (List (Nat × Nat)) := btOfList 4 autosL_14
def slicesL_14 : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,4),some (subcubeFast 0 2,4),some (subcubeFast 0 4,4),some (subcubeFast 0 32,4)]
def slices_14 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_14
def ps_14 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_14 : BT (Option BoundPool) := buildPoolsBT 2 W_14 R_14 slices_14 ps_14
lemma gp_14 : goodPairs G_14 pos_14 neg_14 := goodPairs_of (by decide +kernel)
lemma base_14_ok : ∀ x ∈ base_14, faithful pos_14 neg_14 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_14_ok : btAll (fun x => faithful pos_14 neg_14 x ∧ x.1 < 2^128) W_14 := buildWiresBT_faithful base_14_ok
set_option maxRecDepth 500000 in
lemma autos_14_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_14 = G_14) autos_14 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_14_0_ok : sliceDirectCheck 0 8 0 R_14 G_14 R_9 G_9 = true := by decide +kernel
lemma sl_14_0 : Slice R_14 G_14 (subcubeFast 0 8) 4 := slice_fast_direct sl_14_0_ok low_9
lemma sl_14_1_ok : sliceDirectCheck 0 2 0 R_14 G_14 R_12 G_12 = true := by decide +kernel
lemma sl_14_1 : Slice R_14 G_14 (subcubeFast 0 2) 4 := slice_fast_direct sl_14_1_ok low_12
lemma sl_14_2_ok : sliceDirectCheck 0 4 0 R_14 G_14 R_11 G_11 = true := by decide +kernel
lemma sl_14_2 : Slice R_14 G_14 (subcubeFast 0 4) 4 := slice_fast_direct sl_14_2_ok low_11
lemma sl_14_3_ok : sliceDirectCheck 0 32 0 R_14 G_14 R_8 G_8 = true := by decide +kernel
lemma sl_14_3 : Slice R_14 G_14 (subcubeFast 0 32) 4 := slice_fast_direct sl_14_3_ok low_8
set_option maxRecDepth 500000 in
lemma slices_14_ok : btAll (fun o => ∀ p, o = some p → Slice R_14 G_14 p.1 p.2) slices_14 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_14 G_14 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_14_0) (forall_cons (fun _ h => by cases h; exact sl_14_1) (forall_cons (fun _ h => by cases h; exact sl_14_2) (forall_cons (fun _ h => by cases h; exact sl_14_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_14_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_14 G_14 c) P_14 := buildPoolsBT_sound slices_14_ok
def bk_14_init : BT (List (List Nat)) := BT.empty
lemma bk_14_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 (0 - 1) xs.toFinset) bk_14_init := trivial
def nodes_14_0 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_14_0 : checkNodesBT W_14 G_14 fmask_14 P_14 autos_14 bk_14_init 0 nodes_14_0 = true := by decide +kernel
def bk_14_0 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_0
set_option maxRecDepth 500000 in
lemma bk_14_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 0 xs.toFinset) bk_14_0 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok P_14_ok autos_14_ok bk_14_init_ok chk_14_0
def nodes_14_1 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_14_1 : checkNodesBT W_14 G_14 fmask_14 P_14 autos_14 bk_14_0 1 nodes_14_1 = true := by decide +kernel
def bk_14_1 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_1
set_option maxRecDepth 500000 in
lemma bk_14_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 1 xs.toFinset) bk_14_1 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok P_14_ok autos_14_ok bk_14_0_ok chk_14_1
def nodes_14_2 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_14_2 : checkNodesBT W_14 G_14 fmask_14 P_14 autos_14 bk_14_1 2 nodes_14_2 = true := by decide +kernel
def bk_14_2 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_2
set_option maxRecDepth 500000 in
lemma bk_14_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 2 xs.toFinset) bk_14_2 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok P_14_ok autos_14_ok bk_14_1_ok chk_14_2
def nodes_14_3 : List NodeSpec := [([4,5,8,3],[0,1],[]),([9,0,1,2],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_14_3 : checkNodesBT W_14 G_14 fmask_14 P_14 autos_14 bk_14_2 3 nodes_14_3 = true := by decide +kernel
def bk_14_3 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_3
set_option maxRecDepth 500000 in
lemma bk_14_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 3 xs.toFinset) bk_14_3 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok P_14_ok autos_14_ok bk_14_2_ok chk_14_3
def nodes_14_4 : List NodeSpec := [([4,5,1,2,3],[0,2],[0]),([6,0,1,2,3],[],[]),([7,0,1,2,3],[3],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_14_4 : checkNodesBT W_14 G_14 fmask_14 P_14 autos_14 bk_14_3 4 nodes_14_4 = true := by decide +kernel
def bk_14_4 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_4
set_option maxRecDepth 500000 in
lemma bk_14_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 4 xs.toFinset) bk_14_4 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok P_14_ok autos_14_ok bk_14_3_ok chk_14_4
def nodes_14_5 : List NodeSpec := [([4,0,1,2,3],[2,1,0,3],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_14_5 : checkNodesBT W_14 G_14 fmask_14 P_14 autos_14 bk_14_4 5 nodes_14_5 = true := by decide +kernel
def bk_14_5 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_5
set_option maxRecDepth 500000 in
lemma bk_14_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 5 xs.toFinset) bk_14_5 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok P_14_ok autos_14_ok bk_14_4_ok chk_14_5
def nodes_14_6 : List NodeSpec := [([0,1,2,3],[1,2,0,3],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_14_6 : checkNodesBT W_14 G_14 fmask_14 P_14 autos_14 bk_14_5 6 nodes_14_6 = true := by decide +kernel
def bk_14_6 : BT (List (List Nat)) := buildBucketsBT W_14 nodes_14_6
set_option maxRecDepth 500000 in
lemma bk_14_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_14 6 xs.toFinset) bk_14_6 :=
  buildBucketsBT_sound (by decide) gp_14 W_14_ok P_14_ok autos_14_ok bk_14_5_ok chk_14_6
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_14_ok : forestRootCheck R_14 G_14 [(VAR 1,14,12),(VAR 2,14,10),(VAR 3,14,6),(VAR 5,38,6)] = true := by decide +kernel
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_14_in : bucketContainsBT bk_14_6 R_14 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_14 : Lower R_14 G_14 7 := lower_of_forestBT root_14_ok bk_14_6_ok root_14_in
def G_15 : Nat := 0xfcfcc0c0fcfc0000fcfcc0c0fcfc0000
def R_15 : List Nat := varsOf 54
lemma low_15_ok : liftCheck 0 32 R_15 G_15 R_0 G_0 [(VAR 5,38,6)] = true := by decide +kernel
lemma low_15 : Lower R_15 G_15 5 := lift_of low_15_ok low_0
def G_16 : Nat := 0xfefe8080fefe8080fefe8080fefe8080
def R_16 : List Nat := varsOf 23
def pos_16 : List Nat := [7,7,7,17,17,18,18,19,20,20,21,22,7,17,17,17,18,18,18,20,20,20]
def neg_16 : List Nat := [6,5,3,16,1,16,2,3,16,4,5,6,16,3,5,6,3,5,6,3,5,6]
def fmask_16 : Nat := fullMask 22
def base_16 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xf49f,0x1b6496),(0xcccccccccccccccccccccccccccccccc,0x718e7,0x2da8c5),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x381f07,0x36ce03),(0xffff0000ffff0000ffff0000ffff0000,0x3feff8,0x1128)]
def steps_16 : List (Nat × Nat × Nat) := [(3,0,3),(2,0,3),(1,0,3),(1,0,1),(0,0,3),(2,0,1),(0,0,1),(3,1,6),(0,1,6),(1,8,1),(3,8,1),(3,9,2),(1,9,2),(3,0,1),(3,10,7)]
def W_16 : BT Decor := buildWiresBT 5 base_16 steps_16
def autosL_16 : List (List (Nat × Nat)) := [[],[(1,2)],[(0,1)],[(0,2),(0,1)],[(0,1),(0,2)],[(0,2)]]
def autos_16 : BT (List (Nat × Nat)) := btOfList 3 autosL_16
def slicesL_16 : List (Option (Nat × Nat)) := []
def slices_16 : BT (Option (Nat × Nat)) := btOfList 1 slicesL_16
def ps_16 : List PoolSpec := []
def P_16 : BT (Option BoundPool) := buildPoolsBT 1 W_16 R_16 slices_16 ps_16
lemma gp_16 : goodPairs G_16 pos_16 neg_16 := goodPairs_of (by decide +kernel)
lemma base_16_ok : ∀ x ∈ base_16, faithful pos_16 neg_16 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_16_ok : btAll (fun x => faithful pos_16 neg_16 x ∧ x.1 < 2^128) W_16 := buildWiresBT_faithful base_16_ok
set_option maxRecDepth 500000 in
lemma autos_16_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_16 = G_16) autos_16 := btAll_ofList (autos_of (by decide +kernel))
set_option maxRecDepth 500000 in
lemma slices_16_ok : btAll (fun o => ∀ p, o = some p → Slice R_16 G_16 p.1 p.2) slices_16 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_16 G_16 p.1 p.2) (fun _ h => (List.not_mem_nil h).elim)
set_option maxRecDepth 500000 in
lemma P_16_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_16 G_16 c) P_16 := buildPoolsBT_sound slices_16_ok
def bk_16_init : BT (List (List Nat)) := BT.empty
lemma bk_16_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 (0 - 1) xs.toFinset) bk_16_init := trivial
def nodes_16_0 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_16_0 : checkNodesBT W_16 G_16 fmask_16 P_16 autos_16 bk_16_init 0 nodes_16_0 = true := by decide +kernel
def bk_16_0 : BT (List (List Nat)) := buildBucketsBT W_16 nodes_16_0
set_option maxRecDepth 500000 in
lemma bk_16_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 0 xs.toFinset) bk_16_0 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_init_ok chk_16_0
def nodes_16_1 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_16_1 : checkNodesBT W_16 G_16 fmask_16 P_16 autos_16 bk_16_0 1 nodes_16_1 = true := by decide +kernel
def bk_16_1 : BT (List (List Nat)) := buildBucketsBT W_16 nodes_16_1
set_option maxRecDepth 500000 in
lemma bk_16_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 1 xs.toFinset) bk_16_1 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_0_ok chk_16_1
def nodes_16_2 : List NodeSpec := [([18,2,3],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_16_2 : checkNodesBT W_16 G_16 fmask_16 P_16 autos_16 bk_16_1 2 nodes_16_2 = true := by decide +kernel
def bk_16_2 : BT (List (List Nat)) := buildBucketsBT W_16 nodes_16_2
set_option maxRecDepth 500000 in
lemma bk_16_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 2 xs.toFinset) bk_16_2 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_1_ok chk_16_2
def nodes_16_3 : List NodeSpec := [([5,4,1,2],[],[]),([11,0,2,3],[],[]),([0,12,2,3],[],[]),([0,13,2,3],[],[]),([14,0,2,3],[],[]),([0,1,15,3],[],[]),([0,1,16,3],[],[]),([9,17,2,3],[],[0]),([10,7,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_16_3 : checkNodesBT W_16 G_16 fmask_16 P_16 autos_16 bk_16_2 3 nodes_16_3 = true := by decide +kernel
def bk_16_3 : BT (List (List Nat)) := buildBucketsBT W_16 nodes_16_3
set_option maxRecDepth 500000 in
lemma bk_16_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 3 xs.toFinset) bk_16_3 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_2_ok chk_16_3
def nodes_16_4 : List NodeSpec := [([4,0,1,2,3],[],[0]),([5,0,1,2,3],[],[0]),([0,1,2,3,6],[],[0,1]),([0,1,7,2,3],[],[0]),([8,0,1,2,3],[],[0,1]),([9,0,1,2,3],[],[0]),([10,0,1,2,3],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_16_4 : checkNodesBT W_16 G_16 fmask_16 P_16 autos_16 bk_16_3 4 nodes_16_4 = true := by decide +kernel
def bk_16_4 : BT (List (List Nat)) := buildBucketsBT W_16 nodes_16_4
set_option maxRecDepth 500000 in
lemma bk_16_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 4 xs.toFinset) bk_16_4 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_3_ok chk_16_4
def nodes_16_5 : List NodeSpec := [([0,1,2,3],[],[0,2,1,3,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_16_5 : checkNodesBT W_16 G_16 fmask_16 P_16 autos_16 bk_16_4 5 nodes_16_5 = true := by decide +kernel
def bk_16_5 : BT (List (List Nat)) := buildBucketsBT W_16 nodes_16_5
set_option maxRecDepth 500000 in
lemma bk_16_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_16 5 xs.toFinset) bk_16_5 :=
  buildBucketsBT_sound (by decide) gp_16 W_16_ok P_16_ok autos_16_ok bk_16_4_ok chk_16_5
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_16_ok : forestRootCheck R_16 G_16 [(VAR 0,7,6),(VAR 1,7,5),(VAR 2,7,3),(VAR 4,17,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_16_in : bucketContainsBT bk_16_5 R_16 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_16 : Lower R_16 G_16 6 := lower_of_forestBT root_16_ok bk_16_5_ok root_16_in
def G_17 : Nat := 0xfefee8e8fefee8e8fefee8e8fefee8e8
def R_17 : List Nat := varsOf 23
def pos_17 : List Nat := [3,3,5,5,6,6,17,17,18,18,20,20,3,3,5,5,6,6,17,17,18,18,20,20]
def neg_17 : List Nat := [2,1,4,1,4,2,16,1,16,2,16,4,4,16,2,16,1,16,2,4,1,4,1,2]
def fmask_17 : Nat := fullMask 24
def base_17 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcf0cf,0x51008a),(0xcccccccccccccccccccccccccccccccc,0x333333,0x844221),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xc3cc3c,0x281814),(0xffff0000ffff0000ffff0000ffff0000,0xfc0fc0,0x2a540)]
def steps_17 : List (Nat × Nat × Nat) := [(1,0,1),(2,4,2),(1,4,2),(1,0,2),(2,6,3),(1,1,2)]
def W_17 : BT Decor := buildWiresBT 4 base_17 steps_17
def autosL_17 : List (List (Nat × Nat)) := [[],[(2,4)],[(0,1)],[(2,4),(0,1)],[(1,2)],[(1,4),(1,2)],[(0,1),(0,2)],[(1,4),(0,1),(0,2)],[(1,4),(0,2)]]
def autos_17 : BT (List (Nat × Nat)) := btOfList 4 autosL_17
def slicesL_17 : List (Option (Nat × Nat)) := [some (subcubeFast 2 0,4),some (subcubeFast 1 0,4),some (subcubeFast 16 0,4),some (subcubeFast 4 0,4)]
def slices_17 : BT (Option (Nat × Nat)) := btOfList 2 slicesL_17
def ps_17 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[])]
def P_17 : BT (Option BoundPool) := buildPoolsBT 2 W_17 R_17 slices_17 ps_17
lemma gp_17 : goodPairs G_17 pos_17 neg_17 := goodPairs_of (by decide +kernel)
lemma base_17_ok : ∀ x ∈ base_17, faithful pos_17 neg_17 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_17_ok : btAll (fun x => faithful pos_17 neg_17 x ∧ x.1 < 2^128) W_17 := buildWiresBT_faithful base_17_ok
set_option maxRecDepth 500000 in
lemma autos_17_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_17 = G_17) autos_17 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_17_0_ok : sliceDirectCheck 2 0 0 R_17 G_17 R_6 G_6 = true := by decide +kernel
lemma sl_17_0 : Slice R_17 G_17 (subcubeFast 2 0) 4 := slice_fast_direct sl_17_0_ok low_6
lemma sl_17_1_ok : sliceDirectCheck 1 0 0 R_17 G_17 R_0 G_0 = true := by decide +kernel
lemma sl_17_1 : Slice R_17 G_17 (subcubeFast 1 0) 4 := slice_fast_direct sl_17_1_ok low_0
lemma sl_17_2_ok : sliceDirectCheck 16 0 0 R_17 G_17 R_1 G_1 = true := by decide +kernel
lemma sl_17_2 : Slice R_17 G_17 (subcubeFast 16 0) 4 := slice_fast_direct sl_17_2_ok low_1
lemma sl_17_3_ok : sliceDirectCheck 4 0 0 R_17 G_17 R_3 G_3 = true := by decide +kernel
lemma sl_17_3 : Slice R_17 G_17 (subcubeFast 4 0) 4 := slice_fast_direct sl_17_3_ok low_3
set_option maxRecDepth 500000 in
lemma slices_17_ok : btAll (fun o => ∀ p, o = some p → Slice R_17 G_17 p.1 p.2) slices_17 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_17 G_17 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_17_0) (forall_cons (fun _ h => by cases h; exact sl_17_1) (forall_cons (fun _ h => by cases h; exact sl_17_2) (forall_cons (fun _ h => by cases h; exact sl_17_3) (fun _ h => (List.not_mem_nil h).elim)))))
set_option maxRecDepth 500000 in
lemma P_17_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_17 G_17 c) P_17 := buildPoolsBT_sound slices_17_ok
def bk_17_init : BT (List (List Nat)) := BT.empty
lemma bk_17_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 (0 - 1) xs.toFinset) bk_17_init := trivial
def nodes_17_0 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_17_0 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_init 0 nodes_17_0 = true := by decide +kernel
def bk_17_0 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_0
set_option maxRecDepth 500000 in
lemma bk_17_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 0 xs.toFinset) bk_17_0 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_init_ok chk_17_0
def nodes_17_1 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_17_1 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_0 1 nodes_17_1 = true := by decide +kernel
def bk_17_1 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_1
set_option maxRecDepth 500000 in
lemma bk_17_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 1 xs.toFinset) bk_17_1 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_0_ok chk_17_1
def nodes_17_2 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_17_2 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_1 2 nodes_17_2 = true := by decide +kernel
def bk_17_2 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_2
set_option maxRecDepth 500000 in
lemma bk_17_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 2 xs.toFinset) bk_17_2 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_1_ok chk_17_2
def nodes_17_3 : List NodeSpec := [([8,0,1,2],[],[]),([4,7,9,3],[0,1],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_17_3 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_2 3 nodes_17_3 = true := by decide +kernel
def bk_17_3 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_3
set_option maxRecDepth 500000 in
lemma bk_17_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 3 xs.toFinset) bk_17_3 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_2_ok chk_17_3
def nodes_17_4 : List NodeSpec := [([5,0,1,2,3],[],[]),([0,1,2,6,3],[2],[0]),([1,4,2,7,3],[0,3],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_17_4 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_3 4 nodes_17_4 = true := by decide +kernel
def bk_17_4 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_4
set_option maxRecDepth 500000 in
lemma bk_17_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 4 xs.toFinset) bk_17_4 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_3_ok chk_17_4
def nodes_17_5 : List NodeSpec := [([0,1,4,2,3],[0,1,3,2],[0,1,2,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_17_5 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_4 5 nodes_17_5 = true := by decide +kernel
def bk_17_5 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_5
set_option maxRecDepth 500000 in
lemma bk_17_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 5 xs.toFinset) bk_17_5 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_4_ok chk_17_5
def nodes_17_6 : List NodeSpec := [([0,1,2,3],[0,1,3,2],[0,4,5,6,7,8])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_17_6 : checkNodesBT W_17 G_17 fmask_17 P_17 autos_17 bk_17_5 6 nodes_17_6 = true := by decide +kernel
def bk_17_6 : BT (List (List Nat)) := buildBucketsBT W_17 nodes_17_6
set_option maxRecDepth 500000 in
lemma bk_17_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_17 6 xs.toFinset) bk_17_6 :=
  buildBucketsBT_sound (by decide) gp_17 W_17_ok P_17_ok autos_17_ok bk_17_5_ok chk_17_6
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_17_ok : forestRootCheck R_17 G_17 [(VAR 0,3,2),(VAR 1,3,1),(VAR 2,5,1),(VAR 4,17,1)] = true := by decide +kernel
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_17_in : bucketContainsBT bk_17_6 R_17 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_17 : Lower R_17 G_17 7 := lower_of_forestBT root_17_ok bk_17_6_ok root_17_in
def G_18 : Nat := 0xfff0fff0ff00f000fff0fff0ff00f000
def R_18 : List Nat := varsOf 60
lemma low_18_ok : liftCheck 16 0 R_18 G_18 R_12 G_12 [(VAR 4,24,8)] = true := by decide +kernel
lemma low_18 : Lower R_18 G_18 5 := lift_of low_18_ok low_12
def G_19 : Nat := 0xfffffcfcffffc0c0fffffcfcffffc0c0
def R_19 : List Nat := varsOf 54
lemma low_19_ok : liftCheck 16 0 R_19 G_19 R_9 G_9 [(VAR 4,16,0)] = true := by decide +kernel
lemma low_19 : Lower R_19 G_19 5 := lift_of low_19_ok low_9
def G_20 : Nat := 0xe880e880e880e880e880e880e880e880
def R_20 : List Nat := varsOf 15
lemma low_20_ok : carryOK [(0,4),(0,5),(0,3),(0,2),(0,1)] R_20 G_20 R_14 G_14 = true := by decide +kernel
lemma low_20 : Lower R_20 G_20 7 := carry_of low_20_ok low_14
def G_21 : Nat := 0xe8e8e8e880808080e8e8e8e880808080
def R_21 : List Nat := varsOf 39
lemma low_21_ok : carryOK [(0,3),(0,2),(0,1)] R_21 G_21 R_14 G_14 = true := by decide +kernel
lemma low_21 : Lower R_21 G_21 7 := carry_of low_21_ok low_14
def G_22 : Nat := 0xee008800ee008800ee008800ee008800
def R_22 : List Nat := varsOf 27
lemma low_22_ok : carryOK [(0,2),(0,1)] R_22 G_22 R_13 G_13 = true := by decide +kernel
lemma low_22 : Lower R_22 G_22 5 := carry_of low_22_ok low_13
def G_23 : Nat := 0xee88ee8888008800ee88ee8888008800
def R_23 : List Nat := varsOf 43
lemma low_23_ok : carryOK [(0,2),(0,1)] R_23 G_23 R_14 G_14 = true := by decide +kernel
lemma low_23 : Lower R_23 G_23 7 := carry_of low_23_ok low_14
def G_24 : Nat := 0xeeee8888eeee0000eeee8888eeee0000
def R_24 : List Nat := varsOf 51
lemma low_24_ok : carryOK [(0,2),(0,1)] R_24 G_24 R_15 G_15 = true := by decide +kernel
lemma low_24 : Lower R_24 G_24 5 := carry_of low_24_ok low_15
def G_25 : Nat := 0xfa00a000fa00a000fa00a000fa00a000
def R_25 : List Nat := varsOf 29
lemma low_25_ok : carryOK [(0,1)] R_25 G_25 R_13 G_13 = true := by decide +kernel
lemma low_25 : Lower R_25 G_25 5 := carry_of low_25_ok low_13
def G_26 : Nat := 0xfaa0faa0a000a000faa0faa0a000a000
def R_26 : List Nat := varsOf 45
lemma low_26_ok : carryOK [(0,1)] R_26 G_26 R_14 G_14 = true := by decide +kernel
lemma low_26 : Lower R_26 G_26 7 := carry_of low_26_ok low_14
def G_27 : Nat := 0xfafaa0a0fafa0000fafaa0a0fafa0000
def R_27 : List Nat := varsOf 53
lemma low_27_ok : carryOK [(0,1)] R_27 G_27 R_15 G_15 = true := by decide +kernel
lemma low_27 : Lower R_27 G_27 5 := carry_of low_27_ok low_15
def G_28 : Nat := 0xfe80fe80fe80fe80fe80fe80fe80fe80
def R_28 : List Nat := varsOf 15
lemma low_28_ok : carryOK [(3,4)] R_28 G_28 R_16 G_16 = true := by decide +kernel
lemma low_28 : Lower R_28 G_28 6 := carry_of low_28_ok low_16
def G_29 : Nat := 0xff88ee88ff88ee88ff88ee88ff88ee88
def R_29 : List Nat := varsOf 27
lemma low_29_ok : carryOK [(1,5),(0,2)] R_29 G_29 R_18 G_18 = true := by decide +kernel
lemma low_29 : Lower R_29 G_29 5 := carry_of low_29_ok low_18
def G_30 : Nat := 0xffa0faa0ffa0faa0ffa0faa0ffa0faa0
def R_30 : List Nat := varsOf 29
lemma low_30_ok : carryOK [(1,5),(0,1),(0,2)] R_30 G_30 R_18 G_18 = true := by decide +kernel
lemma low_30 : Lower R_30 G_30 5 := carry_of low_30_ok low_18
def G_31 : Nat := 0xffaaffaaff00aa00ffaaffaaff00aa00
def R_31 : List Nat := varsOf 57
lemma low_31_ok : carryOK [(0,1),(0,2)] R_31 G_31 R_18 G_18 = true := by decide +kernel
lemma low_31 : Lower R_31 G_31 5 := carry_of low_31_ok low_18
def G_32 : Nat := 0xffc0fcc0ffc0fcc0ffc0fcc0ffc0fcc0
def R_32 : List Nat := varsOf 30
lemma low_32_ok : carryOK [(1,5),(1,2)] R_32 G_32 R_18 G_18 = true := by decide +kernel
lemma low_32 : Lower R_32 G_32 5 := carry_of low_32_ok low_18
def G_33 : Nat := 0xffccffccff00cc00ffccffccff00cc00
def R_33 : List Nat := varsOf 58
lemma low_33_ok : carryOK [(1,2)] R_33 G_33 R_18 G_18 = true := by decide +kernel
lemma low_33 : Lower R_33 G_33 5 := carry_of low_33_ok low_18
def G_34 : Nat := 0xffffeeeeffff8888ffffeeeeffff8888
def R_34 : List Nat := varsOf 51
lemma low_34_ok : carryOK [(0,2),(0,1)] R_34 G_34 R_19 G_19 = true := by decide +kernel
lemma low_34 : Lower R_34 G_34 5 := carry_of low_34_ok low_19
def G_35 : Nat := 0xfffffafaffffa0a0fffffafaffffa0a0
def R_35 : List Nat := varsOf 53
lemma low_35_ok : carryOK [(0,1)] R_35 G_35 R_19 G_19 = true := by decide +kernel
lemma low_35 : Lower R_35 G_35 5 := carry_of low_35_ok low_19
def G_36 : Nat := 0xe880e88080008000e880e88080008000
def R_36 : List Nat := varsOf 47
def pos_36 : List Nat := [15,15,15,15,39,39,39,39,43,43,43,43,45,45,45,45,46,46,46,46,15,15,15,15,15,15,39,39,39,39,39,39,43,43,43,43,43,43,45,45,45,45,45,45,46,46,46,46,46,46]
def neg_36 : List Nat := [14,13,11,7,38,37,35,7,42,41,35,11,44,41,37,13,44,42,38,14,35,37,38,41,42,44,11,13,14,41,42,44,7,13,14,37,38,44,7,11,14,35,38,42,7,11,13,35,37,41]
def fmask_36 : Nat := fullMask 50
def base_36 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffff0ffff,0x3f2cb2cb0eeee),(0xcccccccccccccccccccccccccccccccc,0x3f03fffff0fff,0xbfd5555e0ddd),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0x3ffc0fffff0ff,0x1557f9a6dd0bb),(0xff00ff00ff00ff00ff00ff00ff00ff00,0x3ffff03ffff0f,0x269a6ff8bbb07),(0xffffffff00000000ffffffff00000000,0x3fffffc0ffff0,0x38e38e3f77770)]
def steps_36 : List (Nat × Nat × Nat) := [(0,0,1),(0,0,2),(0,5,2),(0,2,3),(3,5,2),(2,5,8),(0,3,4),(0,1,3),(0,1,2),(3,9,3),(0,7,3),(0,0,3),(3,7,3),(0,5,3),(3,16,4),(2,2,11),(3,14,4),(3,15,0),(3,15,4),(0,1,4),(0,14,4),(0,0,4),(0,16,4),(3,10,0),(3,17,4),(0,17,4),(0,2,4),(1,15,4),(0,15,4),(3,33,0),(3,15,1)]
def W_36 : BT Decor := buildWiresBT 6 base_36 steps_36
def autosL_36 : List (List (Nat × Nat)) := [[],[(0,1)],[(0,1),(1,3),(0,5)],[(3,5)],[(0,2),(0,1)],[(0,5),(0,3),(0,2),(0,1)],[(2,3),(2,5)],[(2,3)],[(2,5),(2,3)],[(2,3),(1,2),(1,5)],[(1,2),(1,3)],[(2,5),(1,2),(1,3)],[(2,3),(1,2),(0,1),(0,5)],[(1,2),(0,1),(0,3)],[(2,5),(1,2),(0,1),(0,3)],[(1,5),(0,3)],[(3,5),(0,1)],[(1,5),(1,3),(1,2)],[(1,2)],[(3,5),(0,1),(0,2)],[(2,5),(1,3)],[(2,5),(0,1),(0,3)],[(3,5),(1,2)],[(0,3),(0,2),(0,1)],[(1,3),(1,2)],[(1,2),(0,2),(1,5),(0,3)],[(1,3)],[(1,2),(2,5),(0,1),(0,3)],[(1,2),(2,5),(1,3)],[(1,5),(1,3)],[(2,3),(0,1)],[(2,5),(2,3),(0,1)],[(0,2),(0,3),(0,1)],[(2,5),(0,2),(0,3),(0,1)],[(0,1),(0,3)],[(3,5),(0,2),(0,1)],[(1,3),(0,2)],[(0,1),(1,2),(0,3)],[(0,1),(0,2)],[(1,3),(0,1),(0,2)],[(1,2),(1,5),(0,3)],[(1,5),(1,3),(0,1),(0,2)],[(1,5),(1,3),(0,2)],[(0,1),(0,5),(1,3),(0,2)]]
def autos_36 : BT (List (Nat × Nat)) := btOfList 6 autosL_36
def slicesL_36 : List (Option (Nat × Nat)) := [some (subcubeFast 0 6,4),some (subcubeFast 0 32,7),some (subcubeFast 0 3,4),some (subcubeFast 0 40,4),some (subcubeFast 0 12,4),some (subcubeFast 0 10,4),some (subcubeFast 0 5,4),some (subcubeFast 0 1,7),some (subcubeFast 0 4,7),some (subcubeFast 0 8,7),some (subcubeFast 0 2,7),some (subcubeFast 0 33,4),some (subcubeFast 0 9,4)]
def slices_36 : BT (Option (Nat × Nat)) := btOfList 4 slicesL_36
def ps_36 : List PoolSpec := [(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(1,[(0,0,1),(0,0,2),(0,1,2)]),(7,[]),(8,[(0,0,1),(0,0,3),(0,1,3)]),(7,[(0,5,2),(0,5,3),(0,2,3)]),(9,[]),(7,[(0,5,2),(0,7,3),(3,15,4)]),(1,[(0,0,1),(0,5,2),(3,7,3)]),(7,[(0,2,3),(2,5,8)]),(1,[(0,0,1),(0,0,2)]),(10,[]),(9,[(0,0,1),(0,0,2)]),(8,[(0,0,1),(0,1,3)]),(7,[(0,1,2)]),(8,[]),(9,[(0,0,1),(0,0,2),(0,1,2)]),(1,[(0,0,1),(3,5,2)]),(8,[(0,0,1),(3,9,3)]),(9,[(0,0,1),(3,5,2)]),(11,[]),(7,[(0,5,2),(0,7,3)]),(9,[(0,0,1),(0,5,2)]),(10,[(0,5,2),(0,0,3)]),(8,[(0,0,1),(0,0,3)]),(7,[(0,5,2),(0,2,3)]),(7,[(0,5,2),(3,7,3)]),(1,[(0,0,1),(0,5,2)]),(10,[(0,5,2),(3,7,3)]),(8,[(0,0,1),(3,7,3)]),(7,[(0,5,2),(0,5,3)]),(10,[(0,5,2),(0,7,3)]),(8,[(0,0,1),(0,7,3)]),(10,[(0,0,2)]),(8,[(0,0,1)]),(7,[(0,5,2)]),(10,[(0,5,2)]),(12,[]),(9,[(0,0,1)]),(7,[(0,2,3)]),(10,[(0,2,3)]),(1,[(0,0,1)])]
def P_36 : BT (Option BoundPool) := buildPoolsBT 6 W_36 R_36 slices_36 ps_36
lemma gp_36 : goodPairs G_36 pos_36 neg_36 := goodPairs_of (by decide +kernel)
lemma base_36_ok : ∀ x ∈ base_36, faithful pos_36 neg_36 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_36_ok : btAll (fun x => faithful pos_36 neg_36 x ∧ x.1 < 2^128) W_36 := buildWiresBT_faithful base_36_ok
set_option maxRecDepth 500000 in
lemma autos_36_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_36 = G_36) autos_36 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_36_0_ok : sliceDirectCheck 0 6 0 R_36 G_36 R_10 G_10 = true := by decide +kernel
lemma sl_36_0 : Slice R_36 G_36 (subcubeFast 0 6) 4 := slice_fast_direct sl_36_0_ok low_10
lemma sl_36_1_ok : sliceDirectCheck 0 32 0 R_36 G_36 R_20 G_20 = true := by decide +kernel
lemma sl_36_1 : Slice R_36 G_36 (subcubeFast 0 32) 7 := slice_fast_direct sl_36_1_ok low_20
lemma sl_36_2_ok : sliceDirectCheck 0 3 0 R_36 G_36 R_12 G_12 = true := by decide +kernel
lemma sl_36_2 : Slice R_36 G_36 (subcubeFast 0 3) 4 := slice_fast_direct sl_36_2_ok low_12
lemma sl_36_3_ok : sliceDirectCheck 0 40 0 R_36 G_36 R_1 G_1 = true := by decide +kernel
lemma sl_36_3 : Slice R_36 G_36 (subcubeFast 0 40) 4 := slice_fast_direct sl_36_3_ok low_1
lemma sl_36_4_ok : sliceDirectCheck 0 12 0 R_36 G_36 R_4 G_4 = true := by decide +kernel
lemma sl_36_4 : Slice R_36 G_36 (subcubeFast 0 12) 4 := slice_fast_direct sl_36_4_ok low_4
lemma sl_36_5_ok : sliceDirectCheck 0 10 0 R_36 G_36 R_7 G_7 = true := by decide +kernel
lemma sl_36_5 : Slice R_36 G_36 (subcubeFast 0 10) 4 := slice_fast_direct sl_36_5_ok low_7
lemma sl_36_6_ok : sliceDirectCheck 0 5 0 R_36 G_36 R_11 G_11 = true := by decide +kernel
lemma sl_36_6 : Slice R_36 G_36 (subcubeFast 0 5) 4 := slice_fast_direct sl_36_6_ok low_11
lemma sl_36_7_ok : sliceDirectCheck 0 1 0 R_36 G_36 R_14 G_14 = true := by decide +kernel
lemma sl_36_7 : Slice R_36 G_36 (subcubeFast 0 1) 7 := slice_fast_direct sl_36_7_ok low_14
lemma sl_36_8_ok : sliceDirectCheck 0 4 0 R_36 G_36 R_23 G_23 = true := by decide +kernel
lemma sl_36_8 : Slice R_36 G_36 (subcubeFast 0 4) 7 := slice_fast_direct sl_36_8_ok low_23
lemma sl_36_9_ok : sliceDirectCheck 0 8 0 R_36 G_36 R_21 G_21 = true := by decide +kernel
lemma sl_36_9 : Slice R_36 G_36 (subcubeFast 0 8) 7 := slice_fast_direct sl_36_9_ok low_21
lemma sl_36_10_ok : sliceDirectCheck 0 2 0 R_36 G_36 R_26 G_26 = true := by decide +kernel
lemma sl_36_10 : Slice R_36 G_36 (subcubeFast 0 2) 7 := slice_fast_direct sl_36_10_ok low_26
lemma sl_36_11_ok : sliceDirectCheck 0 33 0 R_36 G_36 R_8 G_8 = true := by decide +kernel
lemma sl_36_11 : Slice R_36 G_36 (subcubeFast 0 33) 4 := slice_fast_direct sl_36_11_ok low_8
lemma sl_36_12_ok : sliceDirectCheck 0 9 0 R_36 G_36 R_9 G_9 = true := by decide +kernel
lemma sl_36_12 : Slice R_36 G_36 (subcubeFast 0 9) 4 := slice_fast_direct sl_36_12_ok low_9
set_option maxRecDepth 500000 in
lemma slices_36_ok : btAll (fun o => ∀ p, o = some p → Slice R_36 G_36 p.1 p.2) slices_36 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_36 G_36 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_36_0) (forall_cons (fun _ h => by cases h; exact sl_36_1) (forall_cons (fun _ h => by cases h; exact sl_36_2) (forall_cons (fun _ h => by cases h; exact sl_36_3) (forall_cons (fun _ h => by cases h; exact sl_36_4) (forall_cons (fun _ h => by cases h; exact sl_36_5) (forall_cons (fun _ h => by cases h; exact sl_36_6) (forall_cons (fun _ h => by cases h; exact sl_36_7) (forall_cons (fun _ h => by cases h; exact sl_36_8) (forall_cons (fun _ h => by cases h; exact sl_36_9) (forall_cons (fun _ h => by cases h; exact sl_36_10) (forall_cons (fun _ h => by cases h; exact sl_36_11) (forall_cons (fun _ h => by cases h; exact sl_36_12) (fun _ h => (List.not_mem_nil h).elim))))))))))))))
set_option maxRecDepth 500000 in
lemma P_36_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_36 G_36 c) P_36 := buildPoolsBT_sound slices_36_ok
def bk_36_init : BT (List (List Nat)) := BT.empty
lemma bk_36_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_36 (0 - 1) xs.toFinset) bk_36_init := trivial
def nodes_36_0 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_36_0 : checkNodesBT W_36 G_36 fmask_36 P_36 autos_36 bk_36_init 0 nodes_36_0 = true := by decide +kernel
def bk_36_0 : BT (List (List Nat)) := buildBucketsBT W_36 nodes_36_0
set_option maxRecDepth 500000 in
lemma bk_36_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_36 0 xs.toFinset) bk_36_0 :=
  buildBucketsBT_sound (by decide) gp_36 W_36_ok P_36_ok autos_36_ok bk_36_init_ok chk_36_0
def nodes_36_1 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_36_1 : checkNodesBT W_36 G_36 fmask_36 P_36 autos_36 bk_36_0 1 nodes_36_1 = true := by decide +kernel
def bk_36_1 : BT (List (List Nat)) := buildBucketsBT W_36 nodes_36_1
set_option maxRecDepth 500000 in
lemma bk_36_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_36 1 xs.toFinset) bk_36_1 :=
  buildBucketsBT_sound (by decide) gp_36 W_36_ok P_36_ok autos_36_ok bk_36_0_ok chk_36_1
def nodes_36_2 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_36_2 : checkNodesBT W_36 G_36 fmask_36 P_36 autos_36 bk_36_1 2 nodes_36_2 = true := by decide +kernel
def bk_36_2 : BT (List (List Nat)) := buildBucketsBT W_36 nodes_36_2
set_option maxRecDepth 500000 in
lemma bk_36_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_36 2 xs.toFinset) bk_36_2 :=
  buildBucketsBT_sound (by decide) gp_36 W_36_ok P_36_ok autos_36_ok bk_36_1_ok chk_36_2
def nodes_36_3 : List NodeSpec := [([20,9,16,24],[],[]),([20,14,26,1],[],[]),([7,27,12,31],[0],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_36_3 : checkNodesBT W_36 G_36 fmask_36 P_36 autos_36 bk_36_2 3 nodes_36_3 = true := by decide +kernel
def bk_36_3 : BT (List (List Nat)) := buildBucketsBT W_36 nodes_36_3
set_option maxRecDepth 500000 in
lemma bk_36_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_36 3 xs.toFinset) bk_36_3 :=
  buildBucketsBT_sound (by decide) gp_36 W_36_ok P_36_ok autos_36_ok bk_36_2_ok chk_36_3
def nodes_36_4 : List NodeSpec := [([5,6,12,31,11],[],[]),([19,9,12,2,4],[],[]),([20,14,0,1,4],[],[0,1]),([14,26,1,2,11],[1],[0]),([9,16,24,2,11],[2],[0]),([14,26,24,2,3],[],[]),([17,26,24,2,3],[],[]),([15,26,24,2,3],[1],[]),([19,7,12,2,4],[],[]),([34,1,2,3,4],[],[]),([7,27,12,2,4],[0],[0]),([20,9,16,1,4],[],[2,3,0]),([7,16,24,2,11],[3],[4]),([22,1,2,3,32],[],[]),([7,16,12,31,4],[],[0,1]),([22,35,2,3,4],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_36_4 : checkNodesBT W_36 G_36 fmask_36 P_36 autos_36 bk_36_3 4 nodes_36_4 = true := by decide +kernel
def bk_36_4 : BT (List (List Nat)) := buildBucketsBT W_36 nodes_36_4
set_option maxRecDepth 500000 in
lemma bk_36_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_36 4 xs.toFinset) bk_36_4 :=
  buildBucketsBT_sound (by decide) gp_36 W_36_ok P_36_ok autos_36_ok bk_36_3_ok chk_36_4
def nodes_36_5 : List NodeSpec := [([15,0,1,2,3,4],[1],[5]),([5,6,13,11,3,4],[4,2,5,6,0,7],[6,7,8,9,10,11,12,13,14]),([19,9,1,2,3,4],[],[0]),([20,9,0,1,3,4],[],[4,15,2,0,3,16]),([21,0,1,2,3,4],[],[]),([7,5,16,1,8,4],[0,6,5,2],[]),([22,5,1,2,3,4],[8],[]),([23,0,1,2,3,4],[],[]),([7,16,1,2,11,4],[3],[17,1,0,4,18]),([7,16,24,2,3,4],[],[3,1,18,19,0]),([9,16,12,2,4],[4,2,9],[3,20,21]),([25,0,1,2,3,4],[],[4]),([19,7,1,2,3,4],[],[0,18]),([14,26,1,2,3,4],[1],[0]),([7,27,1,2,3,4],[0],[0,3,18,22]),([7,18,0,1,8,4],[0,5,10],[]),([17,5,16,1,2,4],[11,6],[]),([17,7,16,1,2,4],[11,6,2],[]),([5,28,1,2,3,4],[8],[]),([9,16,1,2,11,4],[2],[3,21,0]),([23,5,0,1,2,3],[12],[]),([17,26,1,2,3,4],[1,13],[0,18]),([29,0,1,2,3,4],[13],[23]),([23,7,0,1,2,3],[],[]),([30,0,1,2,3,4],[13],[]),([7,5,16,12,2,4],[0,5,6,2],[]),([15,26,1,2,3,4],[1],[0,18,24]),([5,6,12,8,4],[4,2,5,6],[8,11,21,25]),([22,7,1,2,3,4],[8],[24]),([7,16,12,2,4],[11,0,6,2,9],[3,0,1]),([22,15,1,2,3,4],[8],[0,18,24]),([5,6,12,31,3,4],[],[17,26,12,27,25,0]),([14,0,1,2,11,4],[1],[0,1]),([15,0,1,2,3,32],[],[0,1,4,23,5]),([23,0,1,2,3],[],[]),([9,16,24,2,3,4],[],[28,21,0]),([23,15,0,1,2,3],[1],[]),([33,0,1,2,3,4],[],[0,1,4,23,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_36_5 : checkNodesBT W_36 G_36 fmask_36 P_36 autos_36 bk_36_4 5 nodes_36_5 = true := by decide +kernel
def bk_36_5 : BT (List (List Nat)) := buildBucketsBT W_36 nodes_36_5
set_option maxRecDepth 500000 in
lemma bk_36_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_36 5 xs.toFinset) bk_36_5 :=
  buildBucketsBT_sound (by decide) gp_36 W_36_ok P_36_ok autos_36_ok bk_36_4_ok chk_36_5
def nodes_36_6 : List NodeSpec := [([10,5,0,1,2,3,4],[14],[0,1]),([5,6,1,2,11,3,4],[4,2,5,6,15],[6,24,17,9,26,29,0,21,30,31,25,32,33]),([5,6,12,2,3,4],[16,8,2,5,6,17,18],[8,26,10,11,13,34,21,0,30]),([5,6,13,3,4],[19,16,20,2,0,21,7,6],[7,8,10,11,13,14,0]),([9,0,1,2,11,3,4],[2,3,0,22],[0,3,20,21,1,16]),([14,0,1,2,3,4],[5,8,2,23,1,24],[0,1]),([15,5,0,1,2,3,4],[4,25,26],[0,1]),([7,16,1,2,3,4],[11,0,6,2,27,28,29],[0,3,18]),([7,5,0,1,8,3,4],[20,0,6,5,2,27,30],[0,1]),([7,5,16,1,2,3,4],[0,6,5,2],[0]),([17,5,0,1,2,3,4],[20,11,5,0,6,27,31],[23,0,1]),([7,0,1,2,11,3,4],[3,2,0,32],[0,23,5,3,1,16,4,35]),([17,0,1,2,3,4],[0,8,6,2,27,1,31,33,34,13],[23,0,1,4]),([7,18,0,1,2,3,4],[27,20,0,35],[23,4,0]),([15,7,0,1,2,3,4],[11,32,27],[0,1,4,23]),([9,16,1,2,3,4],[4,8,2,29,24],[3,20,0]),([17,7,0,1,2,3,4],[11,0,2,6,27],[23,0,1,4]),([15,0,1,2,3,4],[26,36,37,27,1],[0,1,4,23])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_36_6 : checkNodesBT W_36 G_36 fmask_36 P_36 autos_36 bk_36_5 6 nodes_36_6 = true := by decide +kernel
def bk_36_6 : BT (List (List Nat)) := buildBucketsBT W_36 nodes_36_6
set_option maxRecDepth 500000 in
lemma bk_36_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_36 6 xs.toFinset) bk_36_6 :=
  buildBucketsBT_sound (by decide) gp_36 W_36_ok P_36_ok autos_36_ok bk_36_5_ok chk_36_6
def nodes_36_7 : List NodeSpec := [([5,6,1,2,3,4],[38,20,0,8,2,17,15,6,39],[7,8,10,11,0,3,18,22]),([7,5,0,1,2,3,4],[20,0,6,2,5,25,27,32,40,41,39],[0,3,1,16]),([5,0,1,8,2,3,4],[0,42,4,2,39,43,3,44,45,25],[0,36,4,23,7,8,10,18,24,13,37,38,39,31,25,40]),([9,0,1,2,3,4],[16,0,8,2,39,11,1,22,24],[0,3,1,16]),([7,0,1,2,3,4],[0,6,2,11,27,1,32,40,41,39],[0,3,1,16,4,35])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_36_7 : checkNodesBT W_36 G_36 fmask_36 P_36 autos_36 bk_36_6 7 nodes_36_7 = true := by decide +kernel
def bk_36_7 : BT (List (List Nat)) := buildBucketsBT W_36 nodes_36_7
set_option maxRecDepth 500000 in
lemma bk_36_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_36 7 xs.toFinset) bk_36_7 :=
  buildBucketsBT_sound (by decide) gp_36 W_36_ok P_36_ok autos_36_ok bk_36_6_ok chk_36_7
def nodes_36_8 : List NodeSpec := [([5,0,1,2,3,4],[16,8,20,2,39,11,43,1,46],[0,7,8,1,30,31,6])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_36_8 : checkNodesBT W_36 G_36 fmask_36 P_36 autos_36 bk_36_7 8 nodes_36_8 = true := by decide +kernel
def bk_36_8 : BT (List (List Nat)) := buildBucketsBT W_36 nodes_36_8
set_option maxRecDepth 500000 in
lemma bk_36_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_36 8 xs.toFinset) bk_36_8 :=
  buildBucketsBT_sound (by decide) gp_36 W_36_ok P_36_ok autos_36_ok bk_36_7_ok chk_36_8
def nodes_36_9 : List NodeSpec := [([0,1,2,3,4],[8,16,20,11,1],[0,18,24,17,38,39,41,36,42,43])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_36_9 : checkNodesBT W_36 G_36 fmask_36 P_36 autos_36 bk_36_8 9 nodes_36_9 = true := by decide +kernel
def bk_36_9 : BT (List (List Nat)) := buildBucketsBT W_36 nodes_36_9
set_option maxRecDepth 500000 in
lemma bk_36_9_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_36 9 xs.toFinset) bk_36_9 :=
  buildBucketsBT_sound (by decide) gp_36 W_36_ok P_36_ok autos_36_ok bk_36_8_ok chk_36_9
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_36_ok : forestRootCheck R_36 G_36 [(VAR 0,15,14),(VAR 1,15,13),(VAR 2,15,11),(VAR 3,15,7),(VAR 5,39,7)] = true := by decide +kernel
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_36_in : bucketContainsBT bk_36_9 R_36 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_36 : Lower R_36 G_36 10 := lower_of_forestBT root_36_ok bk_36_9_ok root_36_in
def G_37 : Nat := 0xfc00c000fc000000fc00c000fc000000
def R_37 : List Nat := varsOf 62
lemma low_37_ok : liftCheck 0 8 R_37 G_37 R_15 G_15 [(VAR 3,26,18)] = true := by decide +kernel
lemma low_37 : Lower R_37 G_37 6 := lift_of low_37_ok low_15
def G_38 : Nat := 0xfe008000fe008000fe008000fe008000
def R_38 : List Nat := varsOf 31
lemma low_38_ok : liftCheck 0 8 R_38 G_38 R_16 G_16 [(VAR 3,15,7)] = true := by decide +kernel
lemma low_38 : Lower R_38 G_38 7 := lift_of low_38_ok low_16
def G_39 : Nat := 0xfe80e880fe80e880fe80e880fe80e880
def R_39 : List Nat := varsOf 31
def pos_39 : List Nat := [7,7,7,11,11,11,13,13,13,14,14,14,23,23,23,25,25,25,26,26,26,27,28,28,28,29,30,7,7,7,7,7,7,7,11,11,11,11,11,13,13,13,13,13,14,14,14,14,14,25,25,25,25,25,26,26,26,26,26,28,28,28,28,28]
def neg_39 : List Nat := [6,5,3,10,9,3,12,9,5,12,10,6,22,21,19,24,17,9,24,18,10,19,24,20,12,21,22,9,10,12,19,21,22,24,12,19,21,22,24,10,19,21,22,24,9,19,21,22,24,10,12,19,21,22,9,12,19,21,22,9,10,19,21,22]
def fmask_39 : Nat := fullMask 64
def base_39 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0x3e0ffffa23f1ff,0x6b587318ca2361b6),(0xcccccccccccccccccccccccccccccccc,0x7c1f07ffc3c7e3f,0xb52aa5a954385c2d),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xf801ff83ffc07fc7,0xc6b4c635a7803b43),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xfffffffc07ff8ff8,0x18c718c6395686d8),(0xffff0000ffff0000ffff0000ffff0000,0xfffe000007fff000,0xe739ef7bc6edf000)]
def steps_39 : List (Nat × Nat × Nat) := [(2,0,1),(1,0,1),(0,0,1),(3,0,1),(3,7,6),(3,9,2),(2,9,2),(1,9,2),(0,9,2),(3,13,12)]
def W_39 : BT Decor := buildWiresBT 4 base_39 steps_39
def autosL_39 : List (List (Nat × Nat)) := [[],[(0,1)],[(1,2)],[(0,2),(0,1)],[(0,1),(0,2)],[(0,2)]]
def autos_39 : BT (List (Nat × Nat)) := btOfList 3 autosL_39
def slicesL_39 : List (Option (Nat × Nat)) := [some (subcubeFast 0 16,6),some (subcubeFast 16 2,4),some (subcubeFast 2 8,4),some (subcubeFast 0 2,5),some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 4,5),some (subcubeFast 4 0,5),some (subcubeFast 0 8,7),some (subcubeFast 1 8,4),some (subcubeFast 16 0,7),some (subcubeFast 1 0,5)]
def slices_39 : BT (Option (Nat × Nat)) := btOfList 4 slicesL_39
def ps_39 : List PoolSpec := [(0,[(0,0,1),(1,0,1),(3,7,6)]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(9,[]),(0,[]),(10,[]),(8,[(1,0,1)]),(11,[]),(10,[(0,0,1)])]
def P_39 : BT (Option BoundPool) := buildPoolsBT 4 W_39 R_39 slices_39 ps_39
lemma gp_39 : goodPairs G_39 pos_39 neg_39 := goodPairs_of (by decide +kernel)
lemma base_39_ok : ∀ x ∈ base_39, faithful pos_39 neg_39 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_39_ok : btAll (fun x => faithful pos_39 neg_39 x ∧ x.1 < 2^128) W_39 := buildWiresBT_faithful base_39_ok
set_option maxRecDepth 500000 in
lemma autos_39_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_39 = G_39) autos_39 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_39_0_ok : sliceDirectCheck 0 16 0 R_39 G_39 R_28 G_28 = true := by decide +kernel
lemma sl_39_0 : Slice R_39 G_39 (subcubeFast 0 16) 6 := slice_fast_direct sl_39_0_ok low_28
lemma sl_39_1_ok : sliceDirectCheck 16 2 0 R_39 G_39 R_5 G_5 = true := by decide +kernel
lemma sl_39_1 : Slice R_39 G_39 (subcubeFast 16 2) 4 := slice_fast_direct sl_39_1_ok low_5
lemma sl_39_2_ok : sliceDirectCheck 2 8 0 R_39 G_39 R_6 G_6 = true := by decide +kernel
lemma sl_39_2 : Slice R_39 G_39 (subcubeFast 2 8) 4 := slice_fast_direct sl_39_2_ok low_6
lemma sl_39_3_ok : sliceDirectCheck 0 2 0 R_39 G_39 R_30 G_30 = true := by decide +kernel
lemma sl_39_3 : Slice R_39 G_39 (subcubeFast 0 2) 5 := slice_fast_direct sl_39_3_ok low_30
lemma sl_39_4_ok : sliceDirectCheck 0 1 0 R_39 G_39 R_32 G_32 = true := by decide +kernel
lemma sl_39_4 : Slice R_39 G_39 (subcubeFast 0 1) 5 := slice_fast_direct sl_39_4_ok low_32
lemma sl_39_5_ok : sliceDirectCheck 2 0 0 R_39 G_39 R_25 G_25 = true := by decide +kernel
lemma sl_39_5 : Slice R_39 G_39 (subcubeFast 2 0) 5 := slice_fast_direct sl_39_5_ok low_25
lemma sl_39_6_ok : sliceDirectCheck 0 4 0 R_39 G_39 R_29 G_29 = true := by decide +kernel
lemma sl_39_6 : Slice R_39 G_39 (subcubeFast 0 4) 5 := slice_fast_direct sl_39_6_ok low_29
lemma sl_39_7_ok : sliceDirectCheck 4 0 0 R_39 G_39 R_22 G_22 = true := by decide +kernel
lemma sl_39_7 : Slice R_39 G_39 (subcubeFast 4 0) 5 := slice_fast_direct sl_39_7_ok low_22
lemma sl_39_8_ok : sliceDirectCheck 0 8 0 R_39 G_39 R_17 G_17 = true := by decide +kernel
lemma sl_39_8 : Slice R_39 G_39 (subcubeFast 0 8) 7 := slice_fast_direct sl_39_8_ok low_17
lemma sl_39_9_ok : sliceDirectCheck 1 8 0 R_39 G_39 R_0 G_0 = true := by decide +kernel
lemma sl_39_9 : Slice R_39 G_39 (subcubeFast 1 8) 4 := slice_fast_direct sl_39_9_ok low_0
lemma sl_39_10_ok : sliceDirectCheck 16 0 0 R_39 G_39 R_20 G_20 = true := by decide +kernel
lemma sl_39_10 : Slice R_39 G_39 (subcubeFast 16 0) 7 := slice_fast_direct sl_39_10_ok low_20
lemma sl_39_11_ok : sliceDirectCheck 1 0 0 R_39 G_39 R_13 G_13 = true := by decide +kernel
lemma sl_39_11 : Slice R_39 G_39 (subcubeFast 1 0) 5 := slice_fast_direct sl_39_11_ok low_13
set_option maxRecDepth 500000 in
lemma slices_39_ok : btAll (fun o => ∀ p, o = some p → Slice R_39 G_39 p.1 p.2) slices_39 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_39 G_39 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_39_0) (forall_cons (fun _ h => by cases h; exact sl_39_1) (forall_cons (fun _ h => by cases h; exact sl_39_2) (forall_cons (fun _ h => by cases h; exact sl_39_3) (forall_cons (fun _ h => by cases h; exact sl_39_4) (forall_cons (fun _ h => by cases h; exact sl_39_5) (forall_cons (fun _ h => by cases h; exact sl_39_6) (forall_cons (fun _ h => by cases h; exact sl_39_7) (forall_cons (fun _ h => by cases h; exact sl_39_8) (forall_cons (fun _ h => by cases h; exact sl_39_9) (forall_cons (fun _ h => by cases h; exact sl_39_10) (forall_cons (fun _ h => by cases h; exact sl_39_11) (fun _ h => (List.not_mem_nil h).elim)))))))))))))
set_option maxRecDepth 500000 in
lemma P_39_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_39 G_39 c) P_39 := buildPoolsBT_sound slices_39_ok
def bk_39_init : BT (List (List Nat)) := BT.empty
lemma bk_39_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_39 (0 - 1) xs.toFinset) bk_39_init := trivial
def nodes_39_0 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_39_0 : checkNodesBT W_39 G_39 fmask_39 P_39 autos_39 bk_39_init 0 nodes_39_0 = true := by decide +kernel
def bk_39_0 : BT (List (List Nat)) := buildBucketsBT W_39 nodes_39_0
set_option maxRecDepth 500000 in
lemma bk_39_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_39 0 xs.toFinset) bk_39_0 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok P_39_ok autos_39_ok bk_39_init_ok chk_39_0
def nodes_39_1 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_39_1 : checkNodesBT W_39 G_39 fmask_39 P_39 autos_39 bk_39_0 1 nodes_39_1 = true := by decide +kernel
def bk_39_1 : BT (List (List Nat)) := buildBucketsBT W_39 nodes_39_1
set_option maxRecDepth 500000 in
lemma bk_39_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_39 1 xs.toFinset) bk_39_1 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok P_39_ok autos_39_ok bk_39_0_ok chk_39_1
def nodes_39_2 : List NodeSpec := [([14,3,4],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_39_2 : checkNodesBT W_39 G_39 fmask_39 P_39 autos_39 bk_39_1 2 nodes_39_2 = true := by decide +kernel
def bk_39_2 : BT (List (List Nat)) := buildBucketsBT W_39 nodes_39_2
set_option maxRecDepth 500000 in
lemma bk_39_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_39 2 xs.toFinset) bk_39_2 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok P_39_ok autos_39_ok bk_39_1_ok chk_39_2
def nodes_39_3 : List NodeSpec := [([11,10,3,4],[],[0]),([13,12,3,4],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_39_3 : checkNodesBT W_39 G_39 fmask_39 P_39 autos_39 bk_39_2 3 nodes_39_3 = true := by decide +kernel
def bk_39_3 : BT (List (List Nat)) := buildBucketsBT W_39 nodes_39_3
set_option maxRecDepth 500000 in
lemma bk_39_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_39 3 xs.toFinset) bk_39_3 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok P_39_ok autos_39_ok bk_39_2_ok chk_39_3
def nodes_39_4 : List NodeSpec := [([9,10,2,3,4],[],[0]),([11,9,2,3,4],[],[0]),([9,2,12,3,4],[],[0]),([13,9,2,3,4],[0,1],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_39_4 : checkNodesBT W_39 G_39 fmask_39 P_39 autos_39 bk_39_3 4 nodes_39_4 = true := by decide +kernel
def bk_39_4 : BT (List (List Nat)) := buildBucketsBT W_39 nodes_39_4
set_option maxRecDepth 500000 in
lemma bk_39_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_39 4 xs.toFinset) bk_39_4 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok P_39_ok autos_39_ok bk_39_3_ok chk_39_4
def nodes_39_5 : List NodeSpec := [([9,2,3,4],[2,1],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_39_5 : checkNodesBT W_39 G_39 fmask_39 P_39 autos_39 bk_39_4 5 nodes_39_5 = true := by decide +kernel
def bk_39_5 : BT (List (List Nat)) := buildBucketsBT W_39 nodes_39_5
set_option maxRecDepth 500000 in
lemma bk_39_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_39 5 xs.toFinset) bk_39_5 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok P_39_ok autos_39_ok bk_39_4_ok chk_39_5
def nodes_39_6 : List NodeSpec := [([5,8,2,3,4],[3,4,2,1],[0]),([7,6,2,3,4],[5,4,2,1],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_39_6 : checkNodesBT W_39 G_39 fmask_39 P_39 autos_39 bk_39_5 6 nodes_39_6 = true := by decide +kernel
def bk_39_6 : BT (List (List Nat)) := buildBucketsBT W_39 nodes_39_6
set_option maxRecDepth 500000 in
lemma bk_39_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_39 6 xs.toFinset) bk_39_6 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok P_39_ok autos_39_ok bk_39_5_ok chk_39_6
def nodes_39_7 : List NodeSpec := [([5,0,1,2,3,4],[5,4,3,6,7,8,9,10,11,1],[0]),([0,1,6,2,3,4],[4,5,3,7,6,12,11,10,1],[0]),([7,0,1,2,3,4],[5,3,6,7,8,2,10,11,4,13,1,14],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_39_7 : checkNodesBT W_39 G_39 fmask_39 P_39 autos_39 bk_39_6 7 nodes_39_7 = true := by decide +kernel
def bk_39_7 : BT (List (List Nat)) := buildBucketsBT W_39 nodes_39_7
set_option maxRecDepth 500000 in
lemma bk_39_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_39 7 xs.toFinset) bk_39_7 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok P_39_ok autos_39_ok bk_39_6_ok chk_39_7
def nodes_39_8 : List NodeSpec := [([0,1,2,3,4],[8,11],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_39_8 : checkNodesBT W_39 G_39 fmask_39 P_39 autos_39 bk_39_7 8 nodes_39_8 = true := by decide +kernel
def bk_39_8 : BT (List (List Nat)) := buildBucketsBT W_39 nodes_39_8
set_option maxRecDepth 500000 in
lemma bk_39_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_39 8 xs.toFinset) bk_39_8 :=
  buildBucketsBT_sound (by decide) gp_39 W_39_ok P_39_ok autos_39_ok bk_39_7_ok chk_39_8
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_39_ok : forestRootCheck R_39 G_39 [(VAR 0,7,6),(VAR 1,7,5),(VAR 2,7,3),(VAR 3,11,3),(VAR 4,25,9)] = true := by decide +kernel
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_39_in : bucketContainsBT bk_39_8 R_39 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_39 : Lower R_39 G_39 9 := lower_of_forestBT root_39_ok bk_39_8_ok root_39_in
def G_40 : Nat := 0xfe80fe80fe00fe00fe80fe80fe00fe00
def R_40 : List Nat := varsOf 47
lemma low_40_ok : liftCheck 0 32 R_40 G_40 R_28 G_28 [(VAR 5,39,7)] = true := by decide +kernel
lemma low_40 : Lower R_40 G_40 7 := lift_of low_40_ok low_28
def G_41 : Nat := 0xfefee8e8fefe8080fefee8e8fefe8080
def R_41 : List Nat := varsOf 55
def pos_41 : List Nat := [7,7,7,17,17,18,18,19,20,20,21,22,35,35,35,37,37,37,38,38,38,49,49,50,50,52,52,7,7,7,7,17,17,17,17,17,17,17,18,18,18,18,18,18,18,20,20,20,20,20,20,20,35,35,35,35,37,37,37,37,38,38,38,38]
def neg_41 : List Nat := [6,5,3,16,1,16,2,3,16,4,5,6,34,33,3,36,33,5,36,34,6,48,33,48,34,48,36,33,34,36,48,3,5,6,33,34,36,48,3,5,6,33,34,36,48,3,5,6,33,34,36,48,5,6,36,48,3,6,34,48,3,5,33,48]
def fmask_41 : Nat := fullMask 64
def base_41 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xff0003ff863f49f,0x711162c588436496),(0xcccccccccccccccccccccccccccccccc,0xf0f01fc0799c78e7,0x1722a54a911858c5),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff0fe0007e1f8f07,0x2274c99324168e03),(0xffff0000ffff0000ffff0000ffff0000,0xfffff87e00ff8,0x8888102042a00128),(0xffffffff00000000ffffffff00000000,0xfff0000007fff000,0xcccf1e3c7fedb000)]
def steps_41 : List (Nat × Nat × Nat) := [(2,0,1),(1,0,1),(0,0,1),(3,0,1),(3,7,6),(2,9,2),(1,9,2),(3,9,2),(0,9,2),(3,13,11)]
def W_41 : BT Decor := buildWiresBT 4 base_41 steps_41
def autosL_41 : List (List (Nat × Nat)) := [[],[(0,1)],[(1,2)],[(0,2),(0,1)],[(0,1),(0,2)],[(0,2)]]
def autos_41 : BT (List (Nat × Nat)) := btOfList 3 autosL_41
def slicesL_41 : List (Option (Nat × Nat)) := [some (subcubeFast 2 32,4),some (subcubeFast 32 0,6),some (subcubeFast 16 2,4),some (subcubeFast 0 2,5),some (subcubeFast 0 1,5),some (subcubeFast 2 0,5),some (subcubeFast 0 4,5),some (subcubeFast 4 0,5),some (subcubeFast 0 32,7),some (subcubeFast 1 0,5),some (subcubeFast 1 32,4),some (subcubeFast 16 0,7)]
def slices_41 : BT (Option (Nat × Nat)) := btOfList 4 slicesL_41
def ps_41 : List PoolSpec := [(0,[]),(1,[(0,0,1),(1,0,1),(3,7,6)]),(2,[]),(3,[]),(4,[]),(5,[]),(6,[]),(7,[]),(8,[]),(1,[]),(9,[]),(10,[]),(8,[(1,0,1)]),(11,[(0,0,1)]),(11,[])]
def P_41 : BT (Option BoundPool) := buildPoolsBT 4 W_41 R_41 slices_41 ps_41
lemma gp_41 : goodPairs G_41 pos_41 neg_41 := goodPairs_of (by decide +kernel)
lemma base_41_ok : ∀ x ∈ base_41, faithful pos_41 neg_41 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_41_ok : btAll (fun x => faithful pos_41 neg_41 x ∧ x.1 < 2^128) W_41 := buildWiresBT_faithful base_41_ok
set_option maxRecDepth 500000 in
lemma autos_41_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_41 = G_41) autos_41 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_41_0_ok : sliceDirectCheck 2 32 0 R_41 G_41 R_6 G_6 = true := by decide +kernel
lemma sl_41_0 : Slice R_41 G_41 (subcubeFast 2 32) 4 := slice_fast_direct sl_41_0_ok low_6
lemma sl_41_1_ok : sliceDirectCheck 32 0 0 R_41 G_41 R_16 G_16 = true := by decide +kernel
lemma sl_41_1 : Slice R_41 G_41 (subcubeFast 32 0) 6 := slice_fast_direct sl_41_1_ok low_16
lemma sl_41_2_ok : sliceDirectCheck 16 2 0 R_41 G_41 R_7 G_7 = true := by decide +kernel
lemma sl_41_2 : Slice R_41 G_41 (subcubeFast 16 2) 4 := slice_fast_direct sl_41_2_ok low_7
lemma sl_41_3_ok : sliceDirectCheck 0 2 0 R_41 G_41 R_35 G_35 = true := by decide +kernel
lemma sl_41_3 : Slice R_41 G_41 (subcubeFast 0 2) 5 := slice_fast_direct sl_41_3_ok low_35
lemma sl_41_4_ok : sliceDirectCheck 0 1 0 R_41 G_41 R_19 G_19 = true := by decide +kernel
lemma sl_41_4 : Slice R_41 G_41 (subcubeFast 0 1) 5 := slice_fast_direct sl_41_4_ok low_19
lemma sl_41_5_ok : sliceDirectCheck 2 0 0 R_41 G_41 R_27 G_27 = true := by decide +kernel
lemma sl_41_5 : Slice R_41 G_41 (subcubeFast 2 0) 5 := slice_fast_direct sl_41_5_ok low_27
lemma sl_41_6_ok : sliceDirectCheck 0 4 0 R_41 G_41 R_34 G_34 = true := by decide +kernel
lemma sl_41_6 : Slice R_41 G_41 (subcubeFast 0 4) 5 := slice_fast_direct sl_41_6_ok low_34
lemma sl_41_7_ok : sliceDirectCheck 4 0 0 R_41 G_41 R_24 G_24 = true := by decide +kernel
lemma sl_41_7 : Slice R_41 G_41 (subcubeFast 4 0) 5 := slice_fast_direct sl_41_7_ok low_24
lemma sl_41_8_ok : sliceDirectCheck 0 32 0 R_41 G_41 R_17 G_17 = true := by decide +kernel
lemma sl_41_8 : Slice R_41 G_41 (subcubeFast 0 32) 7 := slice_fast_direct sl_41_8_ok low_17
lemma sl_41_9_ok : sliceDirectCheck 1 0 0 R_41 G_41 R_15 G_15 = true := by decide +kernel
lemma sl_41_9 : Slice R_41 G_41 (subcubeFast 1 0) 5 := slice_fast_direct sl_41_9_ok low_15
lemma sl_41_10_ok : sliceDirectCheck 1 32 0 R_41 G_41 R_0 G_0 = true := by decide +kernel
lemma sl_41_10 : Slice R_41 G_41 (subcubeFast 1 32) 4 := slice_fast_direct sl_41_10_ok low_0
lemma sl_41_11_ok : sliceDirectCheck 16 0 0 R_41 G_41 R_21 G_21 = true := by decide +kernel
lemma sl_41_11 : Slice R_41 G_41 (subcubeFast 16 0) 7 := slice_fast_direct sl_41_11_ok low_21
set_option maxRecDepth 500000 in
lemma slices_41_ok : btAll (fun o => ∀ p, o = some p → Slice R_41 G_41 p.1 p.2) slices_41 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_41 G_41 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_41_0) (forall_cons (fun _ h => by cases h; exact sl_41_1) (forall_cons (fun _ h => by cases h; exact sl_41_2) (forall_cons (fun _ h => by cases h; exact sl_41_3) (forall_cons (fun _ h => by cases h; exact sl_41_4) (forall_cons (fun _ h => by cases h; exact sl_41_5) (forall_cons (fun _ h => by cases h; exact sl_41_6) (forall_cons (fun _ h => by cases h; exact sl_41_7) (forall_cons (fun _ h => by cases h; exact sl_41_8) (forall_cons (fun _ h => by cases h; exact sl_41_9) (forall_cons (fun _ h => by cases h; exact sl_41_10) (forall_cons (fun _ h => by cases h; exact sl_41_11) (fun _ h => (List.not_mem_nil h).elim)))))))))))))
set_option maxRecDepth 500000 in
lemma P_41_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_41 G_41 c) P_41 := buildPoolsBT_sound slices_41_ok
def bk_41_init : BT (List (List Nat)) := BT.empty
lemma bk_41_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 (0 - 1) xs.toFinset) bk_41_init := trivial
def nodes_41_0 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_41_0 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_init 0 nodes_41_0 = true := by decide +kernel
def bk_41_0 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_0
set_option maxRecDepth 500000 in
lemma bk_41_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 0 xs.toFinset) bk_41_0 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_init_ok chk_41_0
def nodes_41_1 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_41_1 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_0 1 nodes_41_1 = true := by decide +kernel
def bk_41_1 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_1
set_option maxRecDepth 500000 in
lemma bk_41_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 1 xs.toFinset) bk_41_1 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_0_ok chk_41_1
def nodes_41_2 : List NodeSpec := [([14,3,4],[],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_41_2 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_1 2 nodes_41_2 = true := by decide +kernel
def bk_41_2 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_2
set_option maxRecDepth 500000 in
lemma bk_41_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 2 xs.toFinset) bk_41_2 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_1_ok chk_41_2
def nodes_41_3 : List NodeSpec := [([10,12,3,4],[],[0]),([13,11,3,4],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_41_3 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_2 3 nodes_41_3 = true := by decide +kernel
def bk_41_3 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_3
set_option maxRecDepth 500000 in
lemma bk_41_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 3 xs.toFinset) bk_41_3 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_2_ok chk_41_3
def nodes_41_4 : List NodeSpec := [([10,9,2,3,4],[0,1],[0]),([9,2,11,3,4],[],[0]),([9,12,2,3,4],[],[0]),([13,9,2,3,4],[],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_41_4 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_3 4 nodes_41_4 = true := by decide +kernel
def bk_41_4 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_4
set_option maxRecDepth 500000 in
lemma bk_41_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 4 xs.toFinset) bk_41_4 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_3_ok chk_41_4
def nodes_41_5 : List NodeSpec := [([9,2,3,4],[2,0],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_41_5 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_4 5 nodes_41_5 = true := by decide +kernel
def bk_41_5 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_5
set_option maxRecDepth 500000 in
lemma bk_41_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 5 xs.toFinset) bk_41_5 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_4_ok chk_41_5
def nodes_41_6 : List NodeSpec := [([5,8,2,3,4],[3,4,2,0],[0]),([7,6,2,3,4],[5,4,2,0],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_41_6 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_5 6 nodes_41_6 = true := by decide +kernel
def bk_41_6 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_6
set_option maxRecDepth 500000 in
lemma bk_41_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 6 xs.toFinset) bk_41_6 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_5_ok chk_41_6
def nodes_41_7 : List NodeSpec := [([5,0,1,2,3,4],[5,4,3,6,7,2,8,9,10,11],[0]),([0,1,6,2,3,4],[4,5,2,7,6,9,8,12],[0]),([7,0,1,2,3,4],[5,3,6,7,13,8,9,4,10,0],[0])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_41_7 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_6 7 nodes_41_7 = true := by decide +kernel
def bk_41_7 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_7
set_option maxRecDepth 500000 in
lemma bk_41_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 7 xs.toFinset) bk_41_7 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_6_ok chk_41_7
def nodes_41_8 : List NodeSpec := [([0,1,2,3,4],[14,8],[0,1,2,3,4,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_41_8 : checkNodesBT W_41 G_41 fmask_41 P_41 autos_41 bk_41_7 8 nodes_41_8 = true := by decide +kernel
def bk_41_8 : BT (List (List Nat)) := buildBucketsBT W_41 nodes_41_8
set_option maxRecDepth 500000 in
lemma bk_41_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_41 8 xs.toFinset) bk_41_8 :=
  buildBucketsBT_sound (by decide) gp_41 W_41_ok P_41_ok autos_41_ok bk_41_7_ok chk_41_8
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_41_ok : forestRootCheck R_41 G_41 [(VAR 0,7,6),(VAR 1,7,5),(VAR 2,7,3),(VAR 4,17,1),(VAR 5,35,3)] = true := by decide +kernel
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_41_in : bucketContainsBT bk_41_8 R_41 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_41 : Lower R_41 G_41 9 := lower_of_forestBT root_41_ok bk_41_8_ok root_41_in
def G_42 : Nat := 0xffc0fcc0ff00c000ffc0fcc0ff00c000
def R_42 : List Nat := varsOf 62
lemma low_42_ok : liftCheck 16 0 R_42 G_42 R_14 G_14 [(VAR 4,24,8)] = true := by decide +kernel
lemma low_42 : Lower R_42 G_42 8 := lift_of low_42_ok low_14
def G_43 : Nat := 0xee008800ee000000ee008800ee000000
def R_43 : List Nat := varsOf 59
lemma low_43_ok : carryOK [(0,2),(0,1)] R_43 G_43 R_37 G_37 = true := by decide +kernel
lemma low_43 : Lower R_43 G_43 6 := carry_of low_43_ok low_37
def G_44 : Nat := 0xfa00a000fa000000fa00a000fa000000
def R_44 : List Nat := varsOf 61
lemma low_44_ok : carryOK [(0,1)] R_44 G_44 R_37 G_37 = true := by decide +kernel
lemma low_44 : Lower R_44 G_44 6 := carry_of low_44_ok low_37
def G_45 : Nat := 0xff88ee88ff008800ff88ee88ff008800
def R_45 : List Nat := varsOf 59
lemma low_45_ok : carryOK [(0,2),(0,1)] R_45 G_45 R_42 G_42 = true := by decide +kernel
lemma low_45 : Lower R_45 G_45 8 := carry_of low_45_ok low_42
def G_46 : Nat := 0xffa0faa0ff00a000ffa0faa0ff00a000
def R_46 : List Nat := varsOf 61
lemma low_46_ok : carryOK [(0,1)] R_46 G_46 R_42 G_42 = true := by decide +kernel
lemma low_46 : Lower R_46 G_46 8 := carry_of low_46_ok low_42
def G_47 : Nat := 0xfe80e880fe008000fe80e880fe008000
def R_47 : List Nat := varsOf 63
def pos_47 : List Nat := [15,15,15,15,25,25,25,26,26,26,27,27,28,28,28,29,29,30,30,31,39,39,39,39,43,43,43,43,45,45,45,45,46,46,46,46,55,55,55,55,57,57,57,58,58,58,59,60,60,60,61,62,15,15,15,15,15,15,15,15,25,25,25,25,25,25,25,25,25,25,25,26,26,26,26,26,26,26,26,26,26,26,28,28,28,28,28,28,28,28,28,28,28,39,39,39,39,39,39,39,39,39,39,39,43,43,43,43,43,43,43,43,45,45,45,45,45,45,45,45,46,46,46,46,46,46,46,46]
def neg_47 : List Nat := [14,13,11,7,24,17,9,24,18,10,19,11,24,20,12,21,13,22,14,23,38,37,35,7,42,41,35,11,44,41,37,13,44,42,38,14,54,53,51,23,56,49,41,56,50,42,51,56,52,44,53,54,23,41,42,44,51,53,54,56,11,13,14,23,41,42,44,51,53,54,56,11,13,14,23,41,42,44,51,53,54,56,11,13,14,23,41,42,44,51,53,54,56,11,13,14,23,41,42,44,51,53,54,56,13,14,23,44,51,53,54,56,11,14,23,42,51,53,54,56,11,13,23,41,51,53,54,56]
def fmask_47 : Nat := fullMask 128
def base_47 : List Decor := [(0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xffffffe000007ffff447f0fff98c7f,0x3f353533666ccd99b33446e0eee98c6e),(0xcccccccccccccccccccccccccccccccc,0xff00ffffe003ff800ff878ff0ffe0f8f,0x555f5655aab556aad55870de0dde0f0d),(0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xffff00fffffc00000fff80fff0fff00f,0x66666f69cd39a734e69f00bdd0bfe00b),(0xff00ff00ff00ff00ff00ff00ff00ff00,0xffffff001fffffffffffff0fff0fffff,0x8b8b8b8ef1de3bc778e2ad0bbb055ad7),(0xffff0000ffff0000ffff0000ffff0000,0x1ffffffff00ffff0000ffff0,0xf4f4f4f11e23c4788f1ddbf0000ab5b0),(0xffffffff00000000ffffffff00000000,0xffffffffe0000000000ffffffff00000,0xf8f8f8fe1fc3f87f0fefff7777700000)]
def steps_47 : List (Nat × Nat × Nat) := [(0,0,5),(3,0,5),(3,0,3),(0,0,3),(2,0,1),(2,3,4),(1,0,1),(0,3,5),(0,0,1),(0,11,5),(3,6,3),(1,6,1),(3,1,5),(3,8,5),(3,8,1),(0,1,5),(0,11,0),(3,7,3),(0,9,5),(3,9,1),(2,9,1),(1,9,1),(0,9,1),(0,2,5),(3,2,3),(1,14,2),(3,14,5),(3,10,2),(3,2,5),(0,1,3),(0,2,3),(2,0,2),(3,10,3),(3,9,5),(0,12,5),(0,12,2),(3,10,5),(0,14,5),(3,14,3),(3,6,1),(0,0,2),(2,11,0),(3,14,2),(0,12,3),(2,14,2),(3,7,1),(0,14,2),(3,0,1),(3,47,3),(3,22,1),(3,51,3),(3,51,2),(3,45,3),(3,45,2),(0,17,2),(3,18,0),(1,18,8),(1,8,21),(3,19,1),(3,18,2),(1,18,9),(2,9,21),(1,9,21),(3,39,1),(1,25,2),(3,9,2),(3,26,2),(3,20,2),(3,26,0),(0,27,5),(3,25,2),(0,27,2),(1,9,2),(3,28,2),(3,28,0),(1,34,10),(1,10,29),(3,36,5),(0,36,5),(2,35,2),(1,10,35),(1,30,10),(3,34,3),(3,50,0),(0,52,3),(0,49,5),(3,38,2),(2,38,2),(3,33,3),(0,33,3),(3,24,1),(3,47,1),(2,11,2),(3,34,12),(1,45,2),(3,30,5),(3,30,12),(2,12,36),(3,40,2),(3,14,12),(0,49,2),(3,41,3),(0,11,2),(2,11,14),(3,34,14),(3,43,0),(2,14,29),(2,14,36),(1,14,29),(1,43,4),(3,30,14),(1,30,14),(3,15,0),(3,21,2),(1,14,36),(3,43,2),(3,52,0),(3,29,3),(3,52,3),(3,14,36),(3,18,9),(3,44,2),(1,34,14),(3,6,2),(2,49,2),(3,32,2),(1,28,2),(2,12,29),(1,10,36),(1,52,4),(0,31,3),(3,48,3),(3,49,2),(3,48,5),(3,42,2),(0,1,2),(0,35,5),(1,8,14),(0,35,2),(0,31,5),(1,40,2),(3,1,54),(1,25,29),(3,24,2),(2,27,29),(3,28,78),(3,15,2),(3,98,1),(2,1,29),(1,98,10),(3,98,3),(3,85,3),(1,10,144),(1,10,129),(3,52,31),(0,82,3),(3,28,12),(3,93,3),(0,78,5),(2,12,84),(3,50,12),(2,0,84),(2,49,29),(3,91,2),(1,10,142),(1,98,14),(3,109,3),(3,109,2),(0,120,5),(3,14,78),(1,10,84),(3,52,12),(3,28,27),(3,105,2),(0,2,115),(0,105,5),(1,105,2),(2,105,2),(3,130,3),(3,105,5),(3,105,3),(3,142,2),(0,105,3),(0,105,2),(3,52,1),(3,43,12),(1,14,84),(3,133,3),(0,132,5),(0,3,135),(1,85,10),(0,114,3),(0,1,54),(3,2,115),(3,98,12),(3,34,49),(1,10,71),(3,147,2),(1,25,129),(3,178,2),(2,178,2),(1,178,2),(0,178,2),(1,10,152),(0,1,156),(3,10,156),(2,12,152),(0,12,156),(0,0,156),(3,14,156),(3,0,156),(2,11,105),(1,105,29),(3,185,2),(0,182,3),(3,186,2),(0,186,2),(0,179,5),(1,105,36),(3,179,3),(3,179,5),(1,34,105),(0,11,105),(1,186,2),(3,181,2),(2,105,36),(0,105,36),(1,30,105),(3,189,5),(3,185,3),(2,191,2),(2,105,29),(1,185,2),(3,181,3),(0,186,5),(2,186,2),(3,198,2),(0,182,5),(3,183,5),(3,186,5),(0,191,2),(3,191,2),(3,189,3),(3,188,5),(3,188,2),(3,183,3),(3,162,2),(3,48,49),(0,162,2),(1,25,149),(0,49,31),(0,14,156),(1,191,2),(3,195,5),(2,162,2),(1,162,2),(1,98,105),(3,222,5),(3,217,2),(3,228,3),(3,228,2),(0,218,3),(1,105,101),(1,105,84),(3,231,5),(1,185,36),(1,15,105),(0,219,3),(3,230,3),(0,230,3),(3,34,186),(1,34,186),(1,186,29),(3,240,2),(0,229,5),(3,249,2),(3,245,2),(1,108,105),(1,34,179),(3,206,5),(2,258,4),(3,29,182),(2,12,173),(1,188,179),(1,30,181),(1,183,179),(2,186,29),(1,30,179),(1,189,186),(0,227,3),(2,191,48),(3,252,5),(1,34,188),(3,205,5),(3,260,5),(1,83,105),(1,48,186),(1,188,29),(3,219,3),(3,36,182),(1,181,36),(2,162,48),(1,30,185),(2,12,180),(3,222,229),(3,232,224),(1,183,223),(1,183,222),(0,291,3),(3,179,251),(3,291,5),(0,291,5),(3,254,261),(3,246,258)]
def W_47 : BT Decor := buildWiresBT 9 base_47 steps_47
def autosL_47 : List (List (Nat × Nat)) := [[(0,1),(0,2)],[],[(0,1)],[(0,2)],[(1,2)],[(0,2),(0,1)]]
def autos_47 : BT (List (Nat × Nat)) := btOfList 3 autosL_47
def slicesL_47 : List (Option (Nat × Nat)) := [some (subcubeFast 0 8,9),some (subcubeFast 0 5,5),some (subcubeFast 0 32,9),some (subcubeFast 16 5,4),some (subcubeFast 0 9,5),some (subcubeFast 0 3,5),some (subcubeFast 1 40,4),some (subcubeFast 16 1,7),some (subcubeFast 16 9,4),some (subcubeFast 0 1,8),some (subcubeFast 32 0,7),some (subcubeFast 32 8,6),some (subcubeFast 1 32,5),some (subcubeFast 16 3,4),some (subcubeFast 2 8,5),some (subcubeFast 1 0,6),some (subcubeFast 16 10,4),some (subcubeFast 16 8,7),some (subcubeFast 4 8,5),some (subcubeFast 0 2,8),some (subcubeFast 0 12,5),some (subcubeFast 2 0,6),some (subcubeFast 16 34,4),some (subcubeFast 0 16,7),some (subcubeFast 16 0,10),some (subcubeFast 0 33,5),some (subcubeFast 0 4,8),some (subcubeFast 0 48,6),some (subcubeFast 2 40,4),some (subcubeFast 4 0,6),some (subcubeFast 0 34,5),some (subcubeFast 0 6,5),some (subcubeFast 16 2,7),some (subcubeFast 16 4,7),some (subcubeFast 0 40,7),some (subcubeFast 2 32,5),some (subcubeFast 0 10,5),some (subcubeFast 16 36,4),some (subcubeFast 1 8,5),some (subcubeFast 16 33,4),some (subcubeFast 0 36,5),some (subcubeFast 16 6,4),some (subcubeFast 4 40,4),some (subcubeFast 4 32,5),some (subcubeFast 16 12,4),some (subcubeFast 16 32,7),some (subcubeFast 16 40,4)]
def slices_47 : BT (Option (Nat × Nat)) := btOfList 6 slicesL_47
def ps_47 : List PoolSpec := [(0,[(0,0,1),(1,0,1),(3,14,12),(0,186,2),(1,186,2),(3,222,229)]),(0,[(0,0,1),(1,0,1),(3,14,12),(0,105,36),(1,105,36),(3,232,224)]),(1,[]),(0,[(0,0,1),(1,0,1),(3,14,12),(2,105,2),(3,105,2),(1,183,222)]),(0,[(0,0,1),(1,0,1),(3,14,12),(0,105,2),(1,105,2),(3,189,182)]),(2,[(0,0,1),(1,0,1),(3,14,12),(0,105,2),(1,105,2),(3,189,182)]),(3,[]),(0,[(0,0,1),(1,0,1),(3,28,12),(0,162,2),(1,162,2),(3,254,261)]),(2,[(0,0,1),(1,0,1),(3,43,12),(0,191,2),(1,191,2),(3,246,258)]),(0,[(0,0,1),(1,0,1),(3,14,12),(2,105,2),(3,105,2),(1,183,179)]),(0,[(0,9,1),(1,9,1),(3,28,27),(2,178,2),(3,178,2)]),(4,[]),(0,[(0,9,1),(1,9,1),(3,28,27),(0,178,2),(1,178,2)]),(5,[]),(6,[]),(7,[]),(0,[(0,0,1),(1,0,1),(3,14,12),(0,186,2),(1,186,2)]),(8,[]),(9,[]),(10,[(0,0,1),(1,0,1),(3,14,12)]),(0,[(0,0,1),(1,0,1),(3,14,12),(2,105,36),(3,105,36)]),(0,[(0,0,1),(1,0,1),(3,14,12),(2,186,2),(3,186,2)]),(11,[(0,0,1),(1,0,1),(3,14,12)]),(12,[]),(13,[]),(0,[(0,0,1),(1,0,1),(3,28,12),(0,162,2),(1,162,2)]),(0,[(0,0,1),(1,0,1),(3,14,12),(0,105,36),(1,105,36)]),(0,[(0,0,1),(1,0,1),(3,14,12),(2,105,2),(3,105,2)]),(2,[(0,0,1),(1,0,1),(3,14,12),(2,105,2),(3,105,2)]),(2,[(0,0,1),(1,0,1),(3,14,12),(2,105,2),(3,105,2),(1,183,179)]),(14,[]),(2,[(0,0,1),(1,0,1),(3,43,12),(2,191,2),(3,191,2)]),(2,[(0,0,1),(1,0,1),(3,14,12),(0,105,2),(1,105,2)]),(2,[(0,0,1),(1,0,1),(3,43,12),(0,191,2),(1,191,2)]),(0,[(0,0,1),(1,0,1),(3,28,12),(2,162,2),(3,162,2)]),(15,[]),(0,[(0,9,1),(1,9,1),(3,28,27),(3,178,2)]),(0,[(0,9,1),(1,9,1),(3,28,27),(2,178,2)]),(0,[(0,9,1),(1,9,1),(3,28,27),(1,178,2)]),(0,[(0,9,1),(1,9,1),(3,28,27),(0,178,2)]),(16,[]),(17,[]),(18,[]),(19,[]),(20,[]),(10,[(0,0,1),(1,0,1)]),(11,[(0,0,1),(1,0,1)]),(21,[]),(22,[]),(23,[(0,0,1),(1,0,1)]),(23,[(0,0,1),(1,0,1),(3,14,12)]),(24,[(0,0,1),(1,0,1),(0,12,3),(0,2,5),(2,49,29)]),(0,[(0,0,1),(1,0,1),(3,14,12),(1,105,2)]),(0,[(0,0,1),(1,0,1),(3,14,12),(3,186,2)]),(0,[(0,0,1),(1,0,1),(3,14,12),(0,186,2)]),(10,[(2,0,1),(3,0,1)]),(2,[(0,0,1),(1,0,1),(3,14,12),(3,105,2)]),(25,[]),(24,[(0,0,1),(1,0,1),(3,14,12),(0,2,3),(3,36,5)]),(0,[(0,0,1),(1,0,1),(3,14,12),(0,105,2),(1,105,2)]),(0,[(0,0,1),(1,0,1),(3,14,12),(3,105,2)]),(24,[(0,0,1),(1,0,1),(3,14,12),(0,2,5),(1,105,29)]),(2,[(0,0,1),(1,0,1),(3,14,12),(1,105,29)]),(0,[(0,0,1),(1,0,1),(3,14,12),(1,105,36)]),(24,[(0,0,1),(1,0,1),(3,14,12),(0,2,5),(3,29,3)]),(24,[(0,0,1),(1,0,1),(3,14,12),(3,105,2),(0,179,3)]),(0,[(0,0,1),(1,0,1),(3,14,12),(1,186,2)]),(2,[(0,0,1),(1,0,1),(3,14,12),(3,181,2)]),(24,[(0,0,1),(1,0,1),(3,14,12),(0,2,3),(0,36,5)]),(0,[(0,0,1),(1,0,1),(3,14,12),(2,105,36)]),(24,[(0,0,1),(1,0,1),(3,14,12),(0,2,3),(1,105,36)]),(0,[(0,0,1),(1,0,1),(3,14,12),(0,105,36)]),(2,[(0,0,1),(1,0,1),(3,14,12),(0,105,2)]),(0,[(0,0,1),(1,0,1),(3,14,12),(2,105,2)]),(24,[(0,0,1),(1,0,1),(3,14,12),(3,105,5),(3,185,3)]),(2,[(0,0,1),(1,0,1),(3,43,12),(2,191,2)]),(2,[(0,0,1),(1,0,1),(3,14,12),(3,185,2)]),(0,[(0,0,1),(1,0,1),(3,14,12),(3,105,36)]),(2,[(0,0,1),(1,0,1),(3,14,12),(1,185,2)]),(2,[(0,0,1),(1,0,1),(3,14,12),(1,34,105)]),(9,[(0,14,2),(1,52,4)]),(24,[(0,0,1),(0,14,2),(1,0,1),(3,14,12)]),(24,[(0,0,1),(1,0,1),(3,14,12),(3,105,3),(0,186,5)]),(24,[(0,0,1),(1,0,1),(3,14,12),(3,105,3),(3,186,2)]),(0,[(0,0,1),(1,0,1),(3,14,12),(2,186,2)]),(0,[(0,0,1),(1,0,1),(3,14,12),(0,105,2)]),(24,[(0,0,1),(1,0,1),(3,14,12),(3,105,2),(0,179,5)]),(24,[(0,0,1),(0,14,3),(3,28,2),(1,0,1),(3,14,12)]),(24,[(0,0,1),(1,0,1),(3,14,12),(3,105,2),(3,105,3)]),(2,[(0,0,1),(1,0,1),(3,14,12),(1,105,2)]),(24,[(0,0,1),(1,0,1),(3,14,12),(3,105,2),(0,2,5)]),(24,[(0,0,1),(1,0,1),(3,14,12),(3,105,5),(0,2,5)]),(24,[(0,0,1),(1,0,1),(3,14,12),(3,105,3),(3,186,5)]),(2,[(0,0,1),(1,0,1),(3,43,12),(0,191,2)]),(24,[(0,0,1),(1,0,1),(3,14,12),(3,105,2),(3,179,5)]),(24,[(0,0,1),(1,0,1),(3,14,12),(3,105,2),(3,179,3)]),(2,[(0,0,1),(1,0,1),(3,14,12),(2,105,2)]),(2,[(0,0,1),(1,0,1),(3,43,12),(3,191,2)]),(0,[(0,0,1),(1,0,1),(3,14,12),(1,30,105)]),(24,[(0,0,1),(0,14,5),(1,0,1),(3,14,12),(0,2,5)]),(24,[(0,0,1),(1,0,1),(3,14,12),(3,105,5),(3,185,2)]),(24,[(0,0,1),(1,0,1),(0,12,3),(0,49,5),(3,91,2)]),(2,[(0,0,1),(1,0,1),(3,43,12)]),(24,[(0,0,1),(0,14,5),(1,0,1),(3,43,12),(0,2,5)]),(9,[(0,14,5),(1,43,4),(0,2,5)]),(24,[(0,0,1),(0,14,5),(3,43,2),(1,0,1),(3,14,12)]),(0,[(0,0,1),(1,0,1),(3,28,12),(3,162,2)]),(26,[]),(0,[(0,0,1),(1,0,1),(3,28,12),(0,162,2)]),(0,[(0,0,1),(1,0,1),(3,14,12),(2,105,2),(3,183,5)]),(23,[]),(27,[]),(11,[(2,11,2)]),(2,[(0,0,1),(1,0,1),(3,43,12),(1,191,2)]),(0,[(0,0,1),(1,0,1),(3,14,12),(3,188,2)]),(0,[(0,0,1),(1,0,1),(3,28,12),(2,162,2)]),(0,[(0,0,1),(1,0,1),(3,28,12),(1,162,2)]),(24,[(0,0,1),(1,0,1),(3,14,12),(3,105,2),(0,2,3)]),(11,[(2,11,0)]),(27,[(3,1,54)]),(10,[]),(28,[]),(29,[]),(26,[(0,0,3),(0,9,5)]),(24,[(0,0,1),(0,14,2),(1,0,1)]),(24,[(0,0,1),(1,0,1),(3,14,12),(0,3,5)]),(2,[(0,0,1),(1,0,1),(3,14,12)]),(11,[(1,9,1)]),(30,[]),(26,[(0,0,3),(0,0,5)]),(11,[]),(9,[(0,14,5),(0,2,5)]),(24,[(0,0,1),(0,14,5),(1,0,1),(0,2,5)]),(24,[]),(2,[]),(31,[]),(2,[(1,0,1),(0,12,3),(0,2,3)]),(32,[]),(33,[]),(34,[]),(11,[(2,0,1)]),(24,[(0,0,1),(1,0,1),(0,12,3),(0,2,3)]),(9,[(0,2,3)]),(10,[(2,0,1)]),(35,[]),(36,[]),(37,[]),(9,[(0,2,5),(1,10,29)]),(38,[]),(39,[]),(23,[(2,0,1),(3,0,1)]),(11,[(2,0,1),(3,0,1)]),(40,[]),(0,[(0,0,1),(1,0,1),(3,14,12)]),(24,[(2,0,1),(3,0,1),(0,2,3),(0,36,5)]),(0,[(0,0,1),(1,0,1),(3,28,12)]),(24,[(0,0,1),(0,14,3),(1,0,1),(3,28,12)]),(41,[]),(42,[]),(19,[(0,0,5),(0,2,5)]),(24,[(2,0,1),(3,10,2),(0,0,5),(0,2,5)]),(43,[]),(9,[(0,2,3),(0,2,5)]),(19,[(0,2,3),(0,2,5)]),(11,[(1,0,1)]),(10,[(1,0,1)]),(2,[(1,0,1),(0,2,3),(2,12,84)]),(0,[(1,0,1),(0,36,5),(2,12,84)]),(24,[(1,0,1),(0,2,3),(0,36,5),(2,12,84)]),(9,[(0,14,2)]),(9,[(0,2,3),(0,36,5)]),(19,[(0,2,3),(0,36,5),(2,0,84)]),(24,[(1,0,1),(0,2,3),(0,36,5),(2,0,84)]),(24,[(1,0,1),(0,12,3),(0,2,5),(2,49,29)]),(44,[]),(24,[(1,0,1),(0,12,3),(0,49,5),(3,91,2)]),(24,[(1,0,1),(0,12,3),(0,49,2),(0,49,5)]),(24,[(0,0,1),(1,0,1),(0,12,3),(0,49,5)]),(0,[(0,0,1),(2,11,2),(1,98,14)]),(10,[(0,0,1)]),(24,[(2,0,1),(3,0,1),(0,2,3),(3,36,5)]),(0,[]),(26,[(0,0,1),(0,14,5),(1,43,4)]),(24,[(0,0,1),(1,14,2),(0,14,5)]),(9,[(0,2,5),(0,3,5)]),(9,[(0,49,2)]),(24,[(0,0,1),(1,0,1),(0,12,3),(0,49,2)]),(9,[(0,2,5),(3,29,3)]),(24,[(0,0,1),(1,0,1),(0,2,5),(3,29,3)]),(24,[(0,0,1),(0,14,5),(0,2,5)]),(24,[(0,0,1),(1,0,1),(0,2,3),(0,36,5)]),(24,[(0,0,1),(0,14,2),(1,0,1),(3,52,12)]),(24,[(0,0,1),(1,0,1),(0,12,3),(0,2,5)]),(0,[(0,9,1),(1,9,1),(3,28,27)]),(24,[(0,0,1),(1,0,1),(3,14,12),(0,2,5)]),(23,[(1,0,1),(0,12,5)]),(9,[(3,105,2)]),(24,[(0,0,1),(1,0,1),(3,14,12),(0,2,3)]),(24,[(0,0,1),(1,0,1),(3,14,12),(3,105,5)]),(24,[(0,0,1),(1,0,1),(3,14,12),(3,105,3)]),(24,[(0,0,1),(1,0,1),(3,14,12),(3,105,2)]),(24,[(0,0,1),(0,14,5),(1,0,1),(3,14,12)]),(24,[(0,0,1),(0,14,5),(1,0,1),(3,43,12)]),(9,[(0,14,5),(3,43,2)]),(24,[(0,0,1),(0,14,5),(3,43,2),(1,0,1)]),(24,[(0,0,1),(3,14,2),(0,14,5)]),(9,[(0,2,5),(2,3,4)]),(24,[(0,0,1),(0,14,3),(1,0,1),(3,14,12)]),(9,[(0,2,5),(3,133,3)]),(19,[(0,2,5),(3,133,3)]),(9,[(0,14,5),(1,43,4)]),(19,[(0,2,5),(0,3,5)]),(0,[(1,0,1),(0,2,5),(2,12,29)]),(9,[(0,14,3),(3,28,2)]),(24,[(0,0,1),(0,14,3),(3,28,2),(1,0,1)]),(26,[(0,0,1),(0,14,3)]),(24,[(0,0,1),(0,14,3),(1,28,2),(0,132,5)]),(9,[(0,2,3),(3,36,5)]),(24,[(0,0,1),(1,0,1),(0,2,3),(3,36,5)]),(27,[(0,1,54)]),(23,[(0,0,1)]),(24,[(2,0,1),(3,0,1),(0,2,5),(3,29,3)]),(24,[(0,0,5),(3,6,1),(3,45,3)]),(26,[(0,0,5),(3,6,1)]),(19,[(0,0,5),(3,45,2)]),(24,[(0,0,5),(3,6,1),(3,45,2)]),(19,[(0,0,5)]),(24,[(3,0,3),(3,8,1),(0,2,5)]),(24,[(0,0,3),(3,1,5),(3,18,2)]),(24,[(0,0,3),(3,1,5),(3,18,0)]),(24,[(0,0,3),(3,9,5),(3,39,1)]),(26,[(0,0,3)]),(11,[(3,9,1)]),(19,[(0,0,3)]),(26,[(0,0,3),(3,9,1)]),(27,[(3,7,1)]),(24,[(0,0,3),(2,9,1),(3,26,2)]),(24,[(0,0,3),(2,9,1),(3,26,0)]),(0,[(1,9,1),(3,2,5)]),(19,[(0,0,3),(3,25,2)]),(19,[(0,0,3),(0,0,5)]),(24,[(0,0,3),(0,9,1),(3,28,2)]),(19,[(0,0,3),(3,28,2)]),(26,[(0,3,5)]),(45,[]),(19,[(0,2,5)]),(24,[(2,0,1),(0,2,3),(0,2,5)]),(24,[(2,0,1),(0,2,3),(3,36,5)]),(26,[(0,36,5)]),(24,[(2,0,1),(0,2,3),(0,36,5)]),(24,[(0,0,3),(3,9,1),(3,2,5)]),(26,[(0,0,5)]),(24,[(2,0,1),(0,0,5),(0,2,5)]),(9,[(0,2,5)]),(24,[(2,0,1),(3,0,1),(0,3,5)]),(2,[(2,0,1),(3,0,1)]),(0,[(2,0,1),(3,0,1)]),(24,[(2,0,1),(3,0,1),(0,2,5)]),(0,[(0,0,1),(1,0,1)]),(19,[(0,2,3)]),(24,[(2,0,1),(3,0,1),(0,2,3)]),(24,[(0,0,1),(2,14,2),(3,50,0)]),(24,[(2,0,1),(3,10,3),(0,2,5)]),(2,[(1,0,1),(0,12,3)]),(24,[(1,0,1),(0,12,3),(0,49,5)]),(24,[(0,0,3),(3,9,1),(0,2,5)]),(9,[(3,10,2),(0,33,3)]),(24,[(2,0,1),(3,10,2),(0,0,3)]),(24,[(0,0,5),(3,6,1),(0,3,5)]),(9,[(0,9,5),(3,24,1)]),(24,[(0,0,3),(0,9,5),(3,24,1)]),(24,[(2,0,1),(3,10,0),(0,2,5)]),(24,[(0,0,1),(0,14,3),(0,2,5)]),(2,[(1,0,1),(0,2,3)]),(0,[(1,0,1),(3,36,5)]),(0,[(1,0,1),(3,30,5)]),(24,[(1,0,1),(0,12,3),(0,2,3)]),(0,[(1,0,1),(0,2,5)]),(24,[(1,0,1),(0,2,3),(0,2,5)]),(0,[(1,0,1),(0,36,5)]),(46,[]),(24,[(1,0,1),(0,2,3),(0,36,5)]),(23,[(2,0,1)]),(24,[(1,0,1),(0,2,3),(3,36,5)]),(24,[(0,0,5),(3,6,1),(0,2,5)]),(24,[(0,0,3),(0,0,5),(3,6,1)]),(24,[(1,0,1),(0,12,5),(0,2,3)]),(24,[(1,0,1),(0,12,3),(0,49,2)]),(9,[(3,10,2),(2,3,4)]),(9,[(0,41,3)]),(26,[(0,0,1),(2,3,4)]),(0,[(0,0,1),(2,11,2)]),(11,[(0,0,1)]),(17,[(0,0,1)]),(33,[(0,0,1)]),(11,[(0,11,2)]),(10,[(3,45,2)]),(24,[(0,0,1),(1,0,1),(0,2,3)]),(24,[(0,0,1),(3,2,5),(3,34,3)]),(26,[(0,0,1)]),(2,[(0,0,1),(1,0,1)]),(24,[(0,0,1),(0,0,3),(0,2,5)]),(26,[(0,0,1),(0,0,3)]),(24,[(0,0,1),(0,2,5)]),(24,[(0,0,1),(3,14,3),(3,2,5)]),(26,[(0,0,1),(3,14,3)]),(0,[(1,0,1),(3,2,5)]),(2,[(1,0,1),(3,34,3)]),(9,[(3,10,2),(0,2,3)]),(24,[(2,0,1),(3,10,2),(0,2,3)]),(24,[(2,0,1),(0,1,3),(0,2,5)]),(24,[(0,0,1),(3,2,3),(3,30,5)]),(19,[(0,14,5),(1,43,4)]),(24,[(0,0,1),(0,2,3),(3,2,5)]),(24,[(2,0,1),(3,10,0),(0,14,3)]),(23,[(1,0,1)]),(2,[(1,0,1),(2,3,4)]),(24,[(0,0,3),(0,1,5),(3,21,2)]),(26,[(0,1,5)]),(9,[(0,1,5),(3,21,2)]),(24,[(0,0,1),(0,14,3),(3,2,5)]),(24,[(0,0,1),(0,2,3),(0,36,5)]),(24,[(0,0,1),(0,14,5)]),(24,[(0,0,1),(0,14,5),(3,43,2)]),(24,[(1,0,1),(0,2,5),(3,29,3)]),(19,[(0,2,5),(3,29,3)]),(24,[(0,0,1),(3,2,3),(0,2,5)]),(24,[(0,0,3),(3,1,5),(3,18,9)]),(24,[(0,0,1),(0,14,3),(3,28,2)]),(24,[(0,0,1),(0,0,5),(0,2,5)]),(9,[(0,1,5)]),(0,[(2,9,1),(3,9,1)]),(24,[(1,0,1),(0,12,3),(0,2,5)]),(27,[(3,6,1)]),(17,[(0,0,5),(3,6,1)]),(24,[(0,0,1),(0,14,3),(1,28,2)]),(9,[(0,2,3),(1,10,36)]),(19,[(0,14,2),(1,52,4)]),(26,[(0,0,1),(0,14,5)]),(9,[(0,14,5)]),(24,[(0,0,1),(0,14,5),(1,0,1)]),(45,[(0,0,1)]),(9,[(0,14,3)]),(24,[(0,0,1),(0,14,3),(1,0,1)]),(0,[(0,9,1),(1,9,1)]),(19,[(0,0,5),(3,6,2)]),(19,[(0,0,3),(0,9,5)]),(9,[(0,3,5)]),(24,[(0,0,1),(1,0,1),(0,3,5)]),(24,[(0,0,1),(3,14,3),(0,2,5)]),(24,[(2,0,1),(3,10,0),(0,2,3)]),(24,[(0,0,1),(3,0,3),(0,2,5)]),(9,[(3,10,2),(0,1,3)]),(9,[(3,10,3)]),(24,[(2,0,1),(3,10,3),(0,0,3)]),(24,[(0,0,1),(0,2,5),(3,29,3)]),(24,[(0,0,1),(3,14,2),(0,0,3)]),(24,[(2,0,1),(0,2,5),(3,29,3)]),(24,[(0,0,1),(0,0,3),(3,2,5)]),(24,[(3,0,3),(0,1,5),(3,21,2)]),(24,[(0,0,1),(1,0,1),(0,2,5)]),(9,[(3,10,2),(0,2,5)]),(24,[(2,0,1),(3,10,2),(0,2,5)]),(24,[(0,0,1),(0,14,2)]),(24,[(0,0,1),(0,2,3),(0,2,5)]),(24,[(2,0,1),(3,10,2),(0,0,5)]),(24,[(1,0,1),(0,2,5),(0,3,5)]),(26,[(0,0,1),(1,52,4)]),(24,[(0,0,1),(0,2,3),(3,36,5)]),(24,[(0,0,5),(0,3,5)]),(24,[(0,0,5),(3,6,3)]),(0,[(3,8,1)]),(24,[(0,0,3),(3,1,5)]),(24,[(0,0,3),(0,1,5)]),(9,[(0,9,5)]),(24,[(0,0,3),(0,9,5)]),(0,[(3,9,1)]),(24,[(0,0,3),(3,9,1)]),(24,[(0,0,3),(2,9,1)]),(0,[(2,9,1)]),(24,[(0,0,5),(0,1,5)]),(0,[(1,9,1)]),(24,[(3,0,3),(0,1,5)]),(24,[(0,0,3),(0,9,1)]),(0,[(0,9,1)]),(19,[(0,3,5)]),(24,[(2,0,1),(0,3,5)]),(2,[(2,0,1)]),(0,[(2,0,1)]),(24,[(2,0,1),(0,2,5)]),(2,[(0,0,1)]),(9,[(3,10,2)]),(0,[(1,0,1)]),(34,[(1,0,1)]),(24,[(1,0,1),(0,3,5)]),(2,[(1,0,1)]),(24,[(0,0,1),(3,14,5)]),(24,[(1,0,1),(0,2,5)]),(9,[(0,1,3)]),(24,[(1,0,1),(0,2,3)]),(24,[(0,0,3),(3,9,5)]),(0,[(0,0,1)]),(9,[(3,10,5)]),(19,[(0,14,5)]),(24,[(0,0,1),(3,14,3)]),(24,[(0,0,1),(3,2,3)]),(17,[(0,0,5)]),(24,[(0,0,1),(0,0,3)]),(24,[(0,0,1),(3,14,2)]),(24,[(0,0,1),(0,2,3)]),(24,[(2,0,1),(0,2,3)]),(24,[(0,0,1),(0,3,5)]),(24,[(0,0,1),(0,14,3)]),(24,[(0,0,5),(3,6,1)]),(2,[(3,6,1)]),(24,[(0,0,1),(3,2,5)]),(19,[(0,14,3)]),(24,[(0,0,1),(2,14,2)]),(24,[(0,0,3),(0,0,5)]),(19,[(0,14,2)]),(24,[(0,0,5)]),(24,[(0,0,3)]),(24,[(0,3,5)]),(24,[(0,0,1)])]
def P_47 : BT (Option BoundPool) := buildPoolsBT 9 W_47 R_47 slices_47 ps_47
lemma gp_47 : goodPairs G_47 pos_47 neg_47 := goodPairs_of (by decide +kernel)
lemma base_47_ok : ∀ x ∈ base_47, faithful pos_47 neg_47 x ∧ x.1 < 2^128 := base_of (by decide +kernel)
set_option maxRecDepth 500000 in
lemma W_47_ok : btAll (fun x => faithful pos_47 neg_47 x ∧ x.1 < 2^128) W_47 := buildWiresBT_faithful base_47_ok
set_option maxRecDepth 500000 in
lemma autos_47_ok : btAll (fun sw => swapsValid sw = true ∧ permWord sw G_47 = G_47) autos_47 := btAll_ofList (autos_of (by decide +kernel))
lemma sl_47_0_ok : sliceDirectCheck 0 8 0 R_47 G_47 R_41 G_41 = true := by decide +kernel
lemma sl_47_0 : Slice R_47 G_47 (subcubeFast 0 8) 9 := slice_fast_direct sl_47_0_ok low_41
lemma sl_47_1_ok : sliceDirectCheck 0 5 0 R_47 G_47 R_33 G_33 = true := by decide +kernel
lemma sl_47_1 : Slice R_47 G_47 (subcubeFast 0 5) 5 := slice_fast_direct sl_47_1_ok low_33
lemma sl_47_2_ok : sliceDirectCheck 0 32 0 R_47 G_47 R_39 G_39 = true := by decide +kernel
lemma sl_47_2 : Slice R_47 G_47 (subcubeFast 0 32) 9 := slice_fast_direct sl_47_2_ok low_39
lemma sl_47_3_ok : sliceDirectCheck 16 5 0 R_47 G_47 R_11 G_11 = true := by decide +kernel
lemma sl_47_3 : Slice R_47 G_47 (subcubeFast 16 5) 4 := slice_fast_direct sl_47_3_ok low_11
lemma sl_47_4_ok : sliceDirectCheck 0 9 0 R_47 G_47 R_19 G_19 = true := by decide +kernel
lemma sl_47_4 : Slice R_47 G_47 (subcubeFast 0 9) 5 := slice_fast_direct sl_47_4_ok low_19
lemma sl_47_5_ok : sliceDirectCheck 0 3 0 R_47 G_47 R_18 G_18 = true := by decide +kernel
lemma sl_47_5 : Slice R_47 G_47 (subcubeFast 0 3) 5 := slice_fast_direct sl_47_5_ok low_18
lemma sl_47_6_ok : sliceDirectCheck 1 40 0 R_47 G_47 R_0 G_0 = true := by decide +kernel
lemma sl_47_6 : Slice R_47 G_47 (subcubeFast 1 40) 4 := slice_fast_direct sl_47_6_ok low_0
lemma sl_47_7_ok : sliceDirectCheck 16 1 0 R_47 G_47 R_14 G_14 = true := by decide +kernel
lemma sl_47_7 : Slice R_47 G_47 (subcubeFast 16 1) 7 := slice_fast_direct sl_47_7_ok low_14
lemma sl_47_8_ok : sliceDirectCheck 16 9 0 R_47 G_47 R_9 G_9 = true := by decide +kernel
lemma sl_47_8 : Slice R_47 G_47 (subcubeFast 16 9) 4 := slice_fast_direct sl_47_8_ok low_9
lemma sl_47_9_ok : sliceDirectCheck 0 1 0 R_47 G_47 R_42 G_42 = true := by decide +kernel
lemma sl_47_9 : Slice R_47 G_47 (subcubeFast 0 1) 8 := slice_fast_direct sl_47_9_ok low_42
lemma sl_47_10_ok : sliceDirectCheck 32 0 0 R_47 G_47 R_38 G_38 = true := by decide +kernel
lemma sl_47_10 : Slice R_47 G_47 (subcubeFast 32 0) 7 := slice_fast_direct sl_47_10_ok low_38
lemma sl_47_11_ok : sliceDirectCheck 32 8 0 R_47 G_47 R_16 G_16 = true := by decide +kernel
lemma sl_47_11 : Slice R_47 G_47 (subcubeFast 32 8) 6 := slice_fast_direct sl_47_11_ok low_16
lemma sl_47_12_ok : sliceDirectCheck 1 32 0 R_47 G_47 R_13 G_13 = true := by decide +kernel
lemma sl_47_12 : Slice R_47 G_47 (subcubeFast 1 32) 5 := slice_fast_direct sl_47_12_ok low_13
lemma sl_47_13_ok : sliceDirectCheck 16 3 0 R_47 G_47 R_12 G_12 = true := by decide +kernel
lemma sl_47_13 : Slice R_47 G_47 (subcubeFast 16 3) 4 := slice_fast_direct sl_47_13_ok low_12
lemma sl_47_14_ok : sliceDirectCheck 2 8 0 R_47 G_47 R_27 G_27 = true := by decide +kernel
lemma sl_47_14 : Slice R_47 G_47 (subcubeFast 2 8) 5 := slice_fast_direct sl_47_14_ok low_27
lemma sl_47_15_ok : sliceDirectCheck 1 0 0 R_47 G_47 R_37 G_37 = true := by decide +kernel
lemma sl_47_15 : Slice R_47 G_47 (subcubeFast 1 0) 6 := slice_fast_direct sl_47_15_ok low_37
lemma sl_47_16_ok : sliceDirectCheck 16 10 0 R_47 G_47 R_7 G_7 = true := by decide +kernel
lemma sl_47_16 : Slice R_47 G_47 (subcubeFast 16 10) 4 := slice_fast_direct sl_47_16_ok low_7
lemma sl_47_17_ok : sliceDirectCheck 16 8 0 R_47 G_47 R_21 G_21 = true := by decide +kernel
lemma sl_47_17 : Slice R_47 G_47 (subcubeFast 16 8) 7 := slice_fast_direct sl_47_17_ok low_21
lemma sl_47_18_ok : sliceDirectCheck 4 8 0 R_47 G_47 R_24 G_24 = true := by decide +kernel
lemma sl_47_18 : Slice R_47 G_47 (subcubeFast 4 8) 5 := slice_fast_direct sl_47_18_ok low_24
lemma sl_47_19_ok : sliceDirectCheck 0 2 0 R_47 G_47 R_46 G_46 = true := by decide +kernel
lemma sl_47_19 : Slice R_47 G_47 (subcubeFast 0 2) 8 := slice_fast_direct sl_47_19_ok low_46
lemma sl_47_20_ok : sliceDirectCheck 0 12 0 R_47 G_47 R_34 G_34 = true := by decide +kernel
lemma sl_47_20 : Slice R_47 G_47 (subcubeFast 0 12) 5 := slice_fast_direct sl_47_20_ok low_34
lemma sl_47_21_ok : sliceDirectCheck 2 0 0 R_47 G_47 R_44 G_44 = true := by decide +kernel
lemma sl_47_21 : Slice R_47 G_47 (subcubeFast 2 0) 6 := slice_fast_direct sl_47_21_ok low_44
lemma sl_47_22_ok : sliceDirectCheck 16 34 0 R_47 G_47 R_5 G_5 = true := by decide +kernel
lemma sl_47_22 : Slice R_47 G_47 (subcubeFast 16 34) 4 := slice_fast_direct sl_47_22_ok low_5
lemma sl_47_23_ok : sliceDirectCheck 0 16 0 R_47 G_47 R_40 G_40 = true := by decide +kernel
lemma sl_47_23 : Slice R_47 G_47 (subcubeFast 0 16) 7 := slice_fast_direct sl_47_23_ok low_40
lemma sl_47_24_ok : sliceDirectCheck 16 0 0 R_47 G_47 R_36 G_36 = true := by decide +kernel
lemma sl_47_24 : Slice R_47 G_47 (subcubeFast 16 0) 10 := slice_fast_direct sl_47_24_ok low_36
lemma sl_47_25_ok : sliceDirectCheck 0 33 0 R_47 G_47 R_32 G_32 = true := by decide +kernel
lemma sl_47_25 : Slice R_47 G_47 (subcubeFast 0 33) 5 := slice_fast_direct sl_47_25_ok low_32
lemma sl_47_26_ok : sliceDirectCheck 0 4 0 R_47 G_47 R_45 G_45 = true := by decide +kernel
lemma sl_47_26 : Slice R_47 G_47 (subcubeFast 0 4) 8 := slice_fast_direct sl_47_26_ok low_45
lemma sl_47_27_ok : sliceDirectCheck 0 48 0 R_47 G_47 R_28 G_28 = true := by decide +kernel
lemma sl_47_27 : Slice R_47 G_47 (subcubeFast 0 48) 6 := slice_fast_direct sl_47_27_ok low_28
lemma sl_47_28_ok : sliceDirectCheck 2 40 0 R_47 G_47 R_6 G_6 = true := by decide +kernel
lemma sl_47_28 : Slice R_47 G_47 (subcubeFast 2 40) 4 := slice_fast_direct sl_47_28_ok low_6
lemma sl_47_29_ok : sliceDirectCheck 4 0 0 R_47 G_47 R_43 G_43 = true := by decide +kernel
lemma sl_47_29 : Slice R_47 G_47 (subcubeFast 4 0) 6 := slice_fast_direct sl_47_29_ok low_43
lemma sl_47_30_ok : sliceDirectCheck 0 34 0 R_47 G_47 R_30 G_30 = true := by decide +kernel
lemma sl_47_30 : Slice R_47 G_47 (subcubeFast 0 34) 5 := slice_fast_direct sl_47_30_ok low_30
lemma sl_47_31_ok : sliceDirectCheck 0 6 0 R_47 G_47 R_31 G_31 = true := by decide +kernel
lemma sl_47_31 : Slice R_47 G_47 (subcubeFast 0 6) 5 := slice_fast_direct sl_47_31_ok low_31
lemma sl_47_32_ok : sliceDirectCheck 16 2 0 R_47 G_47 R_26 G_26 = true := by decide +kernel
lemma sl_47_32 : Slice R_47 G_47 (subcubeFast 16 2) 7 := slice_fast_direct sl_47_32_ok low_26
lemma sl_47_33_ok : sliceDirectCheck 16 4 0 R_47 G_47 R_23 G_23 = true := by decide +kernel
lemma sl_47_33 : Slice R_47 G_47 (subcubeFast 16 4) 7 := slice_fast_direct sl_47_33_ok low_23
lemma sl_47_34_ok : sliceDirectCheck 0 40 0 R_47 G_47 R_17 G_17 = true := by decide +kernel
lemma sl_47_34 : Slice R_47 G_47 (subcubeFast 0 40) 7 := slice_fast_direct sl_47_34_ok low_17
lemma sl_47_35_ok : sliceDirectCheck 2 32 0 R_47 G_47 R_25 G_25 = true := by decide +kernel
lemma sl_47_35 : Slice R_47 G_47 (subcubeFast 2 32) 5 := slice_fast_direct sl_47_35_ok low_25
lemma sl_47_36_ok : sliceDirectCheck 0 10 0 R_47 G_47 R_35 G_35 = true := by decide +kernel
lemma sl_47_36 : Slice R_47 G_47 (subcubeFast 0 10) 5 := slice_fast_direct sl_47_36_ok low_35
lemma sl_47_37_ok : sliceDirectCheck 16 36 0 R_47 G_47 R_2 G_2 = true := by decide +kernel
lemma sl_47_37 : Slice R_47 G_47 (subcubeFast 16 36) 4 := slice_fast_direct sl_47_37_ok low_2
lemma sl_47_38_ok : sliceDirectCheck 1 8 0 R_47 G_47 R_15 G_15 = true := by decide +kernel
lemma sl_47_38 : Slice R_47 G_47 (subcubeFast 1 8) 5 := slice_fast_direct sl_47_38_ok low_15
lemma sl_47_39_ok : sliceDirectCheck 16 33 0 R_47 G_47 R_8 G_8 = true := by decide +kernel
lemma sl_47_39 : Slice R_47 G_47 (subcubeFast 16 33) 4 := slice_fast_direct sl_47_39_ok low_8
lemma sl_47_40_ok : sliceDirectCheck 0 36 0 R_47 G_47 R_29 G_29 = true := by decide +kernel
lemma sl_47_40 : Slice R_47 G_47 (subcubeFast 0 36) 5 := slice_fast_direct sl_47_40_ok low_29
lemma sl_47_41_ok : sliceDirectCheck 16 6 0 R_47 G_47 R_10 G_10 = true := by decide +kernel
lemma sl_47_41 : Slice R_47 G_47 (subcubeFast 16 6) 4 := slice_fast_direct sl_47_41_ok low_10
lemma sl_47_42_ok : sliceDirectCheck 4 40 0 R_47 G_47 R_3 G_3 = true := by decide +kernel
lemma sl_47_42 : Slice R_47 G_47 (subcubeFast 4 40) 4 := slice_fast_direct sl_47_42_ok low_3
lemma sl_47_43_ok : sliceDirectCheck 4 32 0 R_47 G_47 R_22 G_22 = true := by decide +kernel
lemma sl_47_43 : Slice R_47 G_47 (subcubeFast 4 32) 5 := slice_fast_direct sl_47_43_ok low_22
lemma sl_47_44_ok : sliceDirectCheck 16 12 0 R_47 G_47 R_4 G_4 = true := by decide +kernel
lemma sl_47_44 : Slice R_47 G_47 (subcubeFast 16 12) 4 := slice_fast_direct sl_47_44_ok low_4
lemma sl_47_45_ok : sliceDirectCheck 16 32 0 R_47 G_47 R_20 G_20 = true := by decide +kernel
lemma sl_47_45 : Slice R_47 G_47 (subcubeFast 16 32) 7 := slice_fast_direct sl_47_45_ok low_20
lemma sl_47_46_ok : sliceDirectCheck 16 40 0 R_47 G_47 R_1 G_1 = true := by decide +kernel
lemma sl_47_46 : Slice R_47 G_47 (subcubeFast 16 40) 4 := slice_fast_direct sl_47_46_ok low_1
set_option maxRecDepth 500000 in
lemma slices_47_ok : btAll (fun o => ∀ p, o = some p → Slice R_47 G_47 p.1 p.2) slices_47 :=
  btAll_ofList (P := fun (o : Option (Nat × Nat)) => ∀ p, o = some p → Slice R_47 G_47 p.1 p.2) (forall_cons (fun _ h => by cases h; exact sl_47_0) (forall_cons (fun _ h => by cases h; exact sl_47_1) (forall_cons (fun _ h => by cases h; exact sl_47_2) (forall_cons (fun _ h => by cases h; exact sl_47_3) (forall_cons (fun _ h => by cases h; exact sl_47_4) (forall_cons (fun _ h => by cases h; exact sl_47_5) (forall_cons (fun _ h => by cases h; exact sl_47_6) (forall_cons (fun _ h => by cases h; exact sl_47_7) (forall_cons (fun _ h => by cases h; exact sl_47_8) (forall_cons (fun _ h => by cases h; exact sl_47_9) (forall_cons (fun _ h => by cases h; exact sl_47_10) (forall_cons (fun _ h => by cases h; exact sl_47_11) (forall_cons (fun _ h => by cases h; exact sl_47_12) (forall_cons (fun _ h => by cases h; exact sl_47_13) (forall_cons (fun _ h => by cases h; exact sl_47_14) (forall_cons (fun _ h => by cases h; exact sl_47_15) (forall_cons (fun _ h => by cases h; exact sl_47_16) (forall_cons (fun _ h => by cases h; exact sl_47_17) (forall_cons (fun _ h => by cases h; exact sl_47_18) (forall_cons (fun _ h => by cases h; exact sl_47_19) (forall_cons (fun _ h => by cases h; exact sl_47_20) (forall_cons (fun _ h => by cases h; exact sl_47_21) (forall_cons (fun _ h => by cases h; exact sl_47_22) (forall_cons (fun _ h => by cases h; exact sl_47_23) (forall_cons (fun _ h => by cases h; exact sl_47_24) (forall_cons (fun _ h => by cases h; exact sl_47_25) (forall_cons (fun _ h => by cases h; exact sl_47_26) (forall_cons (fun _ h => by cases h; exact sl_47_27) (forall_cons (fun _ h => by cases h; exact sl_47_28) (forall_cons (fun _ h => by cases h; exact sl_47_29) (forall_cons (fun _ h => by cases h; exact sl_47_30) (forall_cons (fun _ h => by cases h; exact sl_47_31) (forall_cons (fun _ h => by cases h; exact sl_47_32) (forall_cons (fun _ h => by cases h; exact sl_47_33) (forall_cons (fun _ h => by cases h; exact sl_47_34) (forall_cons (fun _ h => by cases h; exact sl_47_35) (forall_cons (fun _ h => by cases h; exact sl_47_36) (forall_cons (fun _ h => by cases h; exact sl_47_37) (forall_cons (fun _ h => by cases h; exact sl_47_38) (forall_cons (fun _ h => by cases h; exact sl_47_39) (forall_cons (fun _ h => by cases h; exact sl_47_40) (forall_cons (fun _ h => by cases h; exact sl_47_41) (forall_cons (fun _ h => by cases h; exact sl_47_42) (forall_cons (fun _ h => by cases h; exact sl_47_43) (forall_cons (fun _ h => by cases h; exact sl_47_44) (forall_cons (fun _ h => by cases h; exact sl_47_45) (forall_cons (fun _ h => by cases h; exact sl_47_46) (fun _ h => (List.not_mem_nil h).elim))))))))))))))))))))))))))))))))))))))))))))))))
set_option maxRecDepth 500000 in
lemma P_47_ok : btAll (fun o => ∀ c, o = some c → ValidPool R_47 G_47 c) P_47 := buildPoolsBT_sound slices_47_ok
def bk_47_init : BT (List (List Nat)) := BT.empty
lemma bk_47_init_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_47 (0 - 1) xs.toFinset) bk_47_init := trivial
def nodes_47_0 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_47_0 : checkNodesBT W_47 G_47 fmask_47 P_47 autos_47 bk_47_init 0 nodes_47_0 = true := by decide +kernel
def bk_47_0 : BT (List (List Nat)) := buildBucketsBT W_47 nodes_47_0
set_option maxRecDepth 500000 in
lemma bk_47_0_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_47 0 xs.toFinset) bk_47_0 :=
  buildBucketsBT_sound (by decide) gp_47 W_47_ok P_47_ok autos_47_ok bk_47_init_ok chk_47_0
def nodes_47_1 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_47_1 : checkNodesBT W_47 G_47 fmask_47 P_47 autos_47 bk_47_0 1 nodes_47_1 = true := by decide +kernel
def bk_47_1 : BT (List (List Nat)) := buildBucketsBT W_47 nodes_47_1
set_option maxRecDepth 500000 in
lemma bk_47_1_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_47 1 xs.toFinset) bk_47_1 :=
  buildBucketsBT_sound (by decide) gp_47 W_47_ok P_47_ok autos_47_ok bk_47_0_ok chk_47_1
def nodes_47_2 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_47_2 : checkNodesBT W_47 G_47 fmask_47 P_47 autos_47 bk_47_1 2 nodes_47_2 = true := by decide +kernel
def bk_47_2 : BT (List (List Nat)) := buildBucketsBT W_47 nodes_47_2
set_option maxRecDepth 500000 in
lemma bk_47_2_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_47 2 xs.toFinset) bk_47_2 :=
  buildBucketsBT_sound (by decide) gp_47 W_47_ok P_47_ok autos_47_ok bk_47_1_ok chk_47_2
def nodes_47_3 : List NodeSpec := []
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_47_3 : checkNodesBT W_47 G_47 fmask_47 P_47 autos_47 bk_47_2 3 nodes_47_3 = true := by decide +kernel
def bk_47_3 : BT (List (List Nat)) := buildBucketsBT W_47 nodes_47_3
set_option maxRecDepth 500000 in
lemma bk_47_3_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_47 3 xs.toFinset) bk_47_3 :=
  buildBucketsBT_sound (by decide) gp_47 W_47_ok P_47_ok autos_47_ok bk_47_2_ok chk_47_3
def nodes_47_4 : List NodeSpec := [([310,14,3,4,5],[0],[]),([311,2,3,4,5],[1],[]),([105,310,3,4,5],[0],[]),([11,105,179,156,5],[],[]),([223,291,3,4,5],[],[]),([221,224,3,4,5],[],[]),([226,291,3,4,5],[],[]),([221,105,225,4,5],[],[]),([179,186,280,3,4],[],[]),([179,312,3,4,5],[2],[]),([179,313,3,4,5],[2,3],[]),([225,2,224,4,5],[],[]),([179,278,3,4,5],[],[]),([314,291,3,4,5],[4],[]),([222,291,3,4,5],[],[]),([225,291,3,4,5],[],[]),([225,179,251,4,5],[],[]),([105,222,280,3,4],[],[]),([315,179,3,4,5],[],[]),([11,179,291,3,5],[],[]),([291,13,3,4,5],[5],[]),([316,291,3,4,5],[5],[]),([317,291,3,4,5],[],[]),([315,291,3,4,5],[4],[]),([11,291,3,5],[6],[]),([14,318,3,4,5],[7],[]),([14,319,3,4,5],[8],[]),([179,314,3,4,5],[2,9],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_47_4 : checkNodesBT W_47 G_47 fmask_47 P_47 autos_47 bk_47_3 4 nodes_47_4 = true := by decide +kernel
def bk_47_4 : BT (List (List Nat)) := buildBucketsBT W_47 nodes_47_4
set_option maxRecDepth 500000 in
lemma bk_47_4_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_47 4 xs.toFinset) bk_47_4 :=
  buildBucketsBT_sound (by decide) gp_47 W_47_ok P_47_ok autos_47_ok bk_47_3_ok chk_47_4
def nd_47_5_0 : List NodeSpec := [([206,205,0,3,4,5],[10],[0]),([178,0,2,220,4,5],[11],[]),([208,0,207,3,4,5],[12],[0]),([11,212,14,2,3,5],[],[]),([14,49,36,2,174,4],[13,14],[]),([130,14,250,3,4,5],[],[]),([11,105,14,2,156,5],[],[]),([11,262,14,2,3,5],[15],[]),([11,105,2,172,5],[15],[]),([130,169,14,3,4,5],[],[]),([14,222,229,3,4,5],[16],[1]),([49,36,2,192,4,5],[],[]),([105,263,14,2,3,4],[],[]),([11,14,213,2,156,5],[],[]),([14,185,29,182,3,4],[13],[]),([11,105,262,2,3,5],[],[]),([11,105,264,2,3,5],[],[]),([11,105,2,265,5],[17],[]),([11,105,266,2,3,5],[],[]),([11,105,2,218,3,5],[],[]),([105,2,267,3,4,5],[],[]),([30,105,218,3,4,5],[],[]),([105,2,268,3,4,5],[],[]),([105,36,218,3,4,5],[],[]),([123,105,36,2,4,5],[18,2,19],[]),([105,2,269,3,4,5],[],[]),([231,222,2,3,4,5],[20],[1]),([105,36,2,270,3,4],[],[]),([105,29,224,3,4,5],[],[]),([105,250,36,3,4,5],[13,2],[]),([105,2,271,3,4,5],[11,13],[]),([34,105,224,3,4,5],[],[]),([219,105,2,13,3,4],[],[]),([14,49,2,193,4,5],[],[]),([11,219,105,2,3,5],[],[]),([11,105,272,2,3,5],[],[]),([273,105,2,3,4,5],[],[]),([105,230,36,3,4,5],[11],[]),([105,274,2,3,4,5],[],[]),([105,275,2,3,4,5],[],[]),([105,276,2,3,4,5],[],[]),([105,277,2,3,4,5],[2],[]),([241,221,14,3,4,5],[21],[1]),([227,186,2,3,4,5],[2,11],[]),([105,2,278,3,4,5],[11,22,23],[1]),([279,105,2,3,4,5],[],[]),([241,221,105,3,4,5],[21],[1]),([233,186,2,3,4,5],[18,11,2],[]),([105,186,2,280,3,4],[2],[1]),([105,222,229,3,4,5],[16],[1]),([186,2,224,3,4,5],[18,11],[1]),([235,105,186,2,4,5],[11,19],[]),([188,227,2,3,4,5],[],[]),([281,105,2,3,4,5],[],[]),([34,105,250,3,4,5],[],[]),([105,36,2,174,3,4],[],[]),([105,250,29,3,4,5],[23],[]),([105,282,2,3,4,5],[],[]),([98,11,105,179,3,5],[],[1]),([108,11,105,179,3,5],[24,6],[]),([11,34,105,179,3,5],[],[]),([11,105,283,2,3,5],[],[]),([105,179,284,3,4,5],[2],[]),([11,105,179,2,3,5],[6],[]),([105,179,29,13,3,4],[],[]),([254,14,261,3,4,5],[25],[1]),([237,179,29,3,4,5],[],[]),([178,0,2,285,3,4],[],[]),([221,14,182,3,4,5],[2],[]),([179,29,218,3,4,5],[13],[]),([230,186,2,3,4,5],[],[]),([105,186,2,220,4,5],[11,2],[]),([225,179,186,2,4,5],[11],[]),([105,179,101,3,4,5],[13],[]),([219,186,2,3,4,5],[],[]),([231,179,36,3,4,5],[],[]),([105,79,182,3,4,5],[2],[]),([286,191,14,2,3,5],[],[]),([105,226,179,29,3,4],[],[]),([179,36,224,3,4,5],[13],[]),([179,2,218,3,4,5],[18,19,2],[]),([232,2,224,3,4,5],[26],[1]),([11,105,179,29,3,5],[24],[]),([34,105,225,3,4,5],[],[]),([34,105,222,3,4,5],[],[]),([219,105,182,3,4,5],[2],[]),([105,84,182,3,4,5],[],[]),([105,225,222,2,4,5],[18],[1]),([287,105,29,3,4,5],[2],[]),([222,2,224,3,4,5],[18],[1]),([105,2,224,3,4,5],[],[]),([221,105,222,3,4,5],[18],[1]),([105,179,185,29,3,4],[23,2],[]),([105,233,29,3,4,5],[],[]),([221,105,179,3,4,5],[2],[1]),([11,105,2,156,5],[17,6],[1]),([105,225,186,2,4,5],[11],[1]),([221,179,186,3,4,5],[2],[]),([14,186,2,220,4,5],[11],[]),([34,179,186,3,4,5],[],[]),([188,179,29,3,4,5],[13],[]),([11,288,14,2,3,5],[],[]),([123,105,179,3,4,5],[13],[]),([11,105,2,244,3],[6,24],[]),([179,2,289,3,4,5],[13],[]),([83,105,179,3,4,5],[],[]),([11,183,179,3,5],[6,27],[1]),([183,226,179,3,4,5],[28],[1]),([183,222,179,3,4,5],[27],[1]),([105,290,2,3,4,5],[],[]),([179,291,3,4,5],[2,9,6,29],[1]),([179,251,3,4,5],[27,2,6],[1]),([105,179,36,3,4,5],[13,11],[]),([108,11,105,182,3,5],[6],[]),([105,29,182,13,3,4],[],[]),([292,105,2,3,4,5],[],[]),([221,105,182,3,4,5],[2],[]),([105,29,220,3,4,5],[],[]),([11,105,173,2,3,5],[30],[]),([105,225,179,36,4,5],[11],[]),([48,12,29,2,3,115],[],[]),([191,48,29,2,3,4],[23],[]),([105,121,182,3,4,5],[2],[]),([105,179,293,3,4,5],[2],[]),([179,186,229,3,4,5],[],[1]),([183,179,13,3,4,5],[28],[1]),([236,14,247,3,4,5],[31],[1]),([105,179,88,3,4,5],[],[]),([11,105,29,182,3,5],[],[]),([11,105,230,2,3,5],[],[]),([105,179,84,3,4,5],[13],[]),([189,182,13,3,4,5],[32],[1]),([105,225,29,3,4,5],[],[]),([169,14,49,36,4,5],[],[]),([219,105,179,3,4,5],[2,19],[]),([11,105,227,2,3,5],[],[]),([291,3,4,5],[4,6,5],[1]),([179,186,2,3,4,5],[2,11],[]),([105,2,218,13,3,4],[],[]),([246,14,258,3,4,5],[33],[1]),([105,248,36,2,4,5],[13,2],[]),([11,189,182,3,5],[6,24],[1]),([105,179,29,3,4,5],[13],[]),([186,2,294,3,4,5],[13],[]),([105,225,2,3,4,5],[],[]),([263,14,186,2,3,4],[],[]),([105,295,2,3,4,5],[],[]),([189,2,224,3,4,5],[2],[]),([11,105,152,2,3,5],[],[]),([296,191,2,3,4,5],[23,13],[]),([14,250,49,36,4,5],[],[]),([123,105,182,3,4,5],[],[]),([14,186,2,280,3,4],[2],[]),([105,222,2,3,4,5],[],[]),([105,43,179,29,3,4],[2],[]),([162,297,14,2,3,4],[],[]),([30,105,230,3,4,5],[],[]),([11,105,2,145,3],[6,24],[]),([105,298,2,3,4,5],[],[]),([105,225,36,2,4,5],[18,2],[1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_47_5_0 : checkNodesBT W_47 G_47 fmask_47 P_47 autos_47 bk_47_4 5 nd_47_5_0 = true := by decide +kernel
def nd_47_5_1 : List NodeSpec := [([105,222,29,3,4,5],[23],[]),([225,14,186,2,4,5],[11],[]),([105,121,179,3,4,5],[2],[]),([183,225,179,3,4,5],[2,27],[1]),([178,299,0,2,3,4],[],[]),([221,105,36,3,4,5],[18,2],[1]),([83,105,182,3,4,5],[],[]),([105,227,36,3,4,5],[],[]),([162,14,2,300,3,4],[2],[]),([105,2,218,3,4,5],[],[]),([105,301,2,3,4,5],[],[]),([34,188,179,3,4,5],[],[]),([219,188,2,3,4,5],[],[]),([186,2,302,3,4,5],[],[]),([183,223,179,3,4,5],[],[1]),([105,2,303,3,4,5],[11],[]),([105,43,29,182,3,4],[2],[]),([219,14,182,3,4,5],[2],[]),([189,2,218,3,4,5],[2],[]),([105,28,2,220,4,5],[2],[]),([14,222,49,2,4,5],[],[]),([105,304,2,3,4,5],[],[]),([305,105,36,3,4,5],[2],[]),([105,79,179,3,4,5],[2],[]),([179,2,224,3,4,5],[18,2],[1]),([105,185,29,182,3,4],[13],[]),([219,105,2,3,4,5],[],[]),([221,105,2,3,4,5],[],[]),([105,2,306,3,4,5],[],[]),([307,162,2,3,4,5],[],[]),([179,186,29,3,4,5],[],[1]),([260,14,252,3,4,5],[34],[1]),([105,308,2,3,4,5],[2],[]),([162,14,2,220,4,5],[11],[]),([221,14,49,2,4,5],[],[]),([309,14,2,3,115,5],[],[]),([105,137,36,2,4,5],[18,2],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_47_5_1 : checkNodesBT W_47 G_47 fmask_47 P_47 autos_47 bk_47_4 5 nd_47_5_1 = true := by decide +kernel
def nodes_47_5 : List NodeSpec := nd_47_5_0 ++ nd_47_5_1
set_option maxRecDepth 500000 in
lemma chk_47_5 : checkNodesBT W_47 G_47 fmask_47 P_47 autos_47 bk_47_4 5 nodes_47_5 = true := by
  unfold nodes_47_5 checkNodesBT; simp only [List.all_append, Bool.and_eq_true]
  exact ⟨chk_47_5_0, chk_47_5_1⟩
def bk_47_5 : BT (List (List Nat)) := buildBucketsBT W_47 nodes_47_5
set_option maxRecDepth 500000 in
lemma bk_47_5_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_47 5 xs.toFinset) bk_47_5 :=
  buildBucketsBT_sound (by decide) gp_47 W_47_ok P_47_ok autos_47_ok bk_47_4_ok chk_47_5
def nd_47_6_0 : List NodeSpec := [([11,0,203,1,2,54,5],[],[]),([204,0,1,2,3,4,5],[],[]),([178,205,0,2,3,4,5],[11,35,23,36],[1]),([206,178,0,2,3,4,5],[11,35,23,37],[1]),([178,0,2,207,3,4,5],[35,11,38],[1]),([208,178,0,2,3,4,5],[35,11,39],[1]),([11,0,1,2,209,3,5],[],[]),([11,10,0,210,2,156,5],[],[]),([11,0,1,211,2,156,5],[],[]),([11,10,53,152,2,3,5],[],[1]),([11,10,53,2,156,5],[17,40],[1]),([11,14,0,1,2,156,5],[17],[]),([11,212,0,1,2,3,5],[],[1]),([11,0,1,213,2,156,5],[41,42],[1]),([0,1,49,2,193,4,5],[18,43],[1]),([130,169,0,1,3,4,5],[],[1]),([11,14,214,1,2,156,5],[44,40],[]),([11,215,0,1,2,156,5],[],[]),([11,14,12,2,172,5],[17,30,24],[1]),([11,14,12,173,2,3,5],[30,15],[1]),([123,14,12,36,2,4,5],[18,2,45],[1]),([12,36,2,192,3,4,5],[14,45],[1]),([14,12,36,2,174,3,4],[14,13],[1]),([14,49,88,2,4,5],[13,2,15],[]),([14,201,49,2,3,4,5],[2,6],[]),([14,49,36,29,2,4,5],[2],[]),([14,49,36,29,4,5],[30,14,11,46],[]),([83,14,49,36,2,4,5],[11,2,14,46],[]),([11,216,14,1,2,156,5],[17],[]),([14,49,84,36,2,4,5],[30,14],[1]),([125,14,49,36,2,4,5],[30,13],[]),([14,49,36,2,120,4,5],[13,30,14],[1]),([188,14,49,36,2,4,5],[2,11,30],[1]),([105,137,2,3,4,5],[2,11,13,47,15,24,14],[1]),([188,14,106,2,3,4,5],[2,13,30],[]),([199,14,12,2,3,115,5],[48,47,45,49],[]),([109,11,105,2,3,5],[30,17,24,6,48,14,50],[1]),([217,11,105,14,2,3,5],[30,15,24],[]),([168,14,49,2,3,4,5],[51],[1]),([105,14,2,218,3,4,5],[47,18],[]),([105,36,2,120,3,4,5],[47,11,2,30,14],[1]),([105,14,185,29,2,3,4],[13,23],[1]),([219,105,14,2,3,4,5],[23,2],[1]),([105,2,220,3,4,5],[2,11,52,15,6,19,23],[1]),([221,14,186,2,3,4,5],[11,13,53],[1]),([14,222,186,2,3,4,5],[11,30,54,14],[1]),([34,105,14,179,3,4,5],[13],[]),([105,14,223,2,3,4,5],[47,18],[]),([123,10,53,36,2,4,5],[18,2,55],[1]),([105,14,2,224,3,4,5],[47,18],[]),([105,225,14,2,3,4,5],[11,47],[1]),([105,14,222,2,3,4,5],[47,18,23],[1]),([105,226,179,2,3,4,5],[23,13,2,19,56],[1]),([105,14,2,220,3,4,5],[11,47,52],[1]),([14,185,2,182,3,4,5],[2,13,23],[1]),([14,91,49,36,2,4,5],[2,57,11,46],[1]),([105,227,14,2,3,4,5],[47,18],[]),([105,186,2,182,3,4,5],[13,2,11],[1]),([83,105,2,3,4,5],[13,19,2,11,58,14],[1]),([15,11,105,2,3,5],[48,24,50,6,17,14,22],[1]),([14,179,186,2,3,4,5],[30,11,2,13],[1]),([130,14,91,2,3,4,5],[57],[1]),([108,11,105,2,3,5],[6,24,50,17,48,22],[1]),([105,14,179,36,3,4,5],[13,30],[]),([14,49,2,184,4,5],[13,2,11,15],[]),([228,11,105,2,3,5],[24,17,6,48,22],[1]),([105,29,2,13,3,4],[19,14],[1]),([189,182,3,4,5],[13,2,6,32,59],[1]),([105,225,179,2,3,4,5],[13,2,11,60],[1]),([105,2,218,3,4,5],[19,23,2,11,15,61,62],[1]),([105,36,2,224,3,4,5],[13,2,11,63],[1]),([217,11,105,2,3,5],[24,17,50,6,48,22],[1]),([30,105,29,3,4,5],[2,14,22],[1]),([130,188,14,2,3,4,5],[30,13],[1]),([123,105,2,3,4,5],[13,22,23,2,15,64,14],[1]),([105,2,101,3,4,5],[2,13,19,14,6],[1]),([105,222,2,3,4,5],[15,65,19,23,60],[1]),([14,186,2,229,3,4,5],[2,11,13,66,14],[1]),([105,36,29,2,3,4,5],[14,19,2],[1]),([105,230,2,3,4,5],[23,2,13,11,15,24,67],[1]),([105,84,2,3,4,5],[13,19,14,68],[1]),([231,105,36,2,3,4,5],[2,11,14,13,69],[1]),([30,181,105,2,3,4,5],[2,13,14],[1]),([105,2,224,3,4,5],[63,70,2,19,23],[1]),([11,0,1,33,156,5],[41],[]),([11,105,29,2,3,5],[50,17,48,22,14,24],[1]),([232,105,36,2,3,4,5],[13,71],[1]),([105,233,14,2,3,4,5],[47,18],[]),([105,185,2,13,3,4],[23,13,14,19],[1]),([105,234,2,3,4,5],[2,23,13,22,72,24],[]),([11,183,105,2,3,5],[6,17,50,24,73,14,22],[1]),([30,105,185,2,3,4,5],[2,19,23,14,22],[1]),([235,105,2,3,4,5],[11,23,2,22,15,74,14],[1]),([236,191,14,2,3,4,5],[13,47,23,2,75],[1]),([219,105,185,2,3,4,5],[2,13,23,76,19],[]),([237,105,29,2,3,4,5],[2,23,13,19],[1]),([11,14,12,2,156,5],[17],[1]),([105,29,2,114,3,4,5],[47,2,23],[]),([105,222,36,2,3,4,5],[13,77],[1]),([105,185,2,238,3,4,5],[78,19],[1]),([11,181,105,2,3,5],[24,17,50,6,14],[1]),([105,227,2,3,4,5],[2,79,11,15,6],[1]),([105,2,145,3,4,5],[2,13,14,15,6],[]),([105,239,2,3,4,5],[23,11,13,2,22,15,24],[1]),([34,14,49,36,4,5],[2,30,11,14],[]),([105,2,3,135,5],[24,6,80,30,81,23],[]),([105,240,2,3,4,5],[14,19,2,82],[1]),([221,105,2,3,4,5],[2,11,13,15,83,19,23,53],[1]),([241,105,186,2,3,4,5],[84,2],[1]),([105,186,2,229,3,4,5],[13,11,66,2,14],[1]),([105,222,186,2,3,4,5],[54,2],[1]),([98,11,105,14,2,3,5],[24,30,17,50],[1]),([105,186,185,2,3,4,5],[13,14,19],[1]),([186,185,2,3,4,5],[11,23,13,14,22],[1]),([181,186,2,3,4,5],[13,14],[1]),([14,186,2,182,3,4,5],[2,13,30],[1]),([34,188,105,2,3,4,5],[2,13,14],[1]),([188,185,2,3,4,5],[13,14,22],[1]),([14,49,2,136,4,5],[30,2,15],[]),([105,240,186,2,3,4,5],[14,19],[1]),([48,166,3,4,5],[2,30,13,23],[]),([105,179,2,13,3,4,5],[19,14,2,56],[1]),([11,105,179,2,3,5],[50,17,6,24,60,22,48],[1]),([105,179,2,3,4,5],[2,13,11,15,6,19,23],[1]),([34,105,179,3,4,5],[2,13,6,23],[1]),([105,14,179,29,3,4,5],[13,56],[1]),([105,223,179,2,3,4,5],[23,56,19],[1]),([11,189,105,2,3,5],[24,17,50,85,48,22,6],[1]),([105,223,2,3,4,5],[19,22,86],[1]),([34,105,36,3,4,5],[2,14],[1]),([11,105,14,2,182,3,5],[24,30],[]),([11,0,1,40,2,156],[17],[]),([105,79,2,3,4,5],[2,11,47,30,15,87,23],[1]),([11,242,0,1,2,54,5],[],[]),([105,14,36,182,3,4,5],[13,30],[]),([179,186,2,3,4,5],[2,11,13,60,22,88],[1]),([105,179,36,2,3,4,5],[13,2,11],[1]),([105,14,29,182,3,4,5],[13,89],[1]),([160,12,3,4,5],[2,30,6,23],[]),([105,139,2,3,4,5],[2,57,13,14,15,24,19],[]),([188,179,2,3,4,5],[13,2,11,22,60,24],[1]),([162,48,2,3,4,5],[13,47,11,23,30],[1]),([105,14,2,243,3,4,5],[47,57,19,89],[]),([14,137,12,36,2,4,5],[13,2],[1]),([183,179,3,4,5],[2,27,6,28],[1]),([11,105,2,31,3,5],[50,17,6,24,30,14],[1]),([105,179,29,3,4,5],[2,13,56,90],[1]),([105,2,244,3,4,5],[2,13,19,11,22,6],[]),([11,34,105,2,3,5],[6,17,50,24,14],[1]),([105,179,186,2,3,4,5],[13,2,11],[1]),([105,185,29,2,3,4],[23,13,19,22,2,91],[1]),([105,2,182,13,3,4,5],[2,19,14,89],[1]),([105,245,2,3,4,5],[23,11,14,19,2,92],[1]),([246,191,14,2,3,4,5],[47,13,23,93],[1]),([11,105,2,182,3,5],[6,50,17,24,52,22,48],[1]),([105,36,29,3,4,5],[22,14,2],[1]),([105,179,29,2,3,4,5],[13,2,56,19],[1]),([11,14,12,2,145,3],[6,14],[1]),([105,2,243,3,4,5],[23,89,19,22,6],[]),([105,185,2,182,3,4,5],[13,2,19,23],[1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_47_6_0 : checkNodesBT W_47 G_47 fmask_47 P_47 autos_47 bk_47_5 6 nd_47_6_0 = true := by decide +kernel
def nd_47_6_1 : List NodeSpec := [([189,105,2,13,3,4,5],[13,14,19,72],[1]),([105,29,2,218,3,4,5],[19,13,2,23],[1]),([189,186,2,3,4,5],[13,11,22,2,24,85],[1]),([105,29,182,3,4,5],[13,2,89,6],[1]),([241,14,186,2,3,4,5],[11,30,2,84],[1]),([105,36,182,3,4,5],[13,2,6,11,22,52],[1]),([105,226,2,3,4,5],[23,2,22,56,94],[]),([105,225,2,3,4,5],[11,2,60,13,15,95,19,23],[1]),([11,105,48,2,3,5],[24,17,50,30,48,14],[]),([183,105,2,13,3,4,5],[2,14,19,96],[1]),([105,125,36,2,3,4,5],[47,30],[1]),([105,185,36,2,3,4,5],[14,19,22],[1]),([34,105,186,2,3,4,5],[13,2,14],[1]),([191,14,247,2,3,4,5],[97,57,47,45],[1]),([105,248,2,3,4,5],[2,11,13,85,15,24,19,23],[1]),([105,233,2,3,4,5],[2,98,15,6,19,23],[1]),([189,105,36,2,3,4,5],[13,11,2],[1]),([105,226,14,2,3,4,5],[47,57,56],[]),([105,249,2,3,4,5],[11,23,13,19,2,14,24],[1]),([105,43,29,2,3,4],[57,14,2,99],[1]),([14,250,49,2,3,4,5],[30,24],[1]),([83,105,36,2,3,4,5],[23,11,2,19,14,22],[]),([105,2,251,3,4,5],[2,13,15,6,19,23,73],[1]),([105,43,2,182,3,4,5],[13,2,47,57,6,19],[1]),([30,105,179,3,4,5],[2,13,6,60,22],[1]),([221,105,14,2,3,4,5],[11,2],[1]),([219,105,2,3,4,5],[2,23,19,11,15,100,76],[1]),([105,2,136,3,4,5],[2,13,15,6,14],[]),([169,14,49,2,3,4,5],[57,2,101],[1]),([191,14,29,2,3,4],[23,102,13,14,45,103],[1]),([14,12,29,2,3,115],[23,104,14],[1]),([14,12,180,2,3,115,5],[48],[1]),([11,14,200,2,3,5],[17,49,24],[]),([105,121,2,3,4,5],[2,57,30,15,105,23],[1]),([44,14,106,49,2,4,5],[2,13,30,11],[]),([105,28,179,2,3,4,5],[13,47,2,11],[1]),([162,14,252,2,3,4,5],[106,11,47,23],[1]),([105,88,2,3,4,5],[13,22,2,15,6],[1]),([48,14,49,36,2,4,5],[30,13],[]),([14,253,49,2,3,4,5],[13,24],[]),([11,14,12,152,2,3,5],[15],[1]),([105,28,2,182,3,4,5],[13,2,47,11],[1]),([181,105,36,2,3,4,5],[13,2,14],[1]),([105,43,179,2,3,4,5],[13,47,2,57,6],[1]),([169,0,1,49,36,4,5],[107],[1]),([254,162,14,2,3,4,5],[47,13,108],[1]),([189,105,29,2,3,4,5],[13,23,19,2],[1]),([105,48,29,2,3,4,5],[23,19],[]),([48,12,2,3,115,5],[24,47,30,23],[1]),([130,44,14,49,2,4,5],[30,13,11],[]),([105,2,244,3,4],[2,13,19,109,22,6],[1]),([11,105,185,2,3,5],[50,17,48,22,14,6],[1]),([255,0,1,2,3,4,5],[],[]),([167,1,49,36,2,4,5],[30],[]),([48,0,1,29,2,3,115],[],[1]),([105,84,36,2,3,4,5],[23,14,19],[1]),([14,186,49,2,4,5],[18,11,30,13,15],[1]),([98,11,105,2,3,5],[6,17,24,48,22],[1]),([48,186,2,3,4,5],[13,30,14],[1]),([105,2,145,3,4],[2,13,19,14,22,6],[1]),([105,186,29,2,3,4,5],[13,22,2,23],[1]),([14,256,49,2,3,4,5],[2,6],[]),([188,105,29,2,3,4,5],[13,19,2,23,22],[1]),([14,49,2,145,3,4],[13,2,6,14],[]),([48,43,12,29,2,3,4],[23,2],[1]),([11,257,0,1,2,156,5],[41,110,42,111,112],[]),([191,14,2,258,3,4,5],[2,47,57,113,48,45],[1]),([191,48,2,3,4,5],[13,30,24,23],[1]),([105,245,186,2,3,4,5],[13,11,14,22],[]),([105,177,2,3,4,5],[47,2,30,6,23],[]),([105,250,2,3,4,5],[11,2,13,15,24,19,23,114],[1]),([105,48,36,2,3,4,5],[30],[1]),([259,0,1,2,195,3],[111],[]),([105,179,185,2,3,4,5],[13,56,2,19],[1]),([108,11,105,14,2,3,5],[30,24,6,17],[]),([221,105,186,2,3,4,5],[13,11,2,53],[1]),([30,105,14,179,3,4,5],[2,13],[]),([11,105,14,179,2,3,5],[24,30],[]),([260,162,14,2,3,4,5],[13,47,23,2,115],[1]),([162,14,2,261,3,4,5],[2,47,11,116],[1]),([105,179,36,3,4,5],[2,13,60,22,117],[1]),([177,31,3,4,5],[2,30,6,23],[]),([105,222,179,2,3,4,5],[11,60],[1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_47_6_1 : checkNodesBT W_47 G_47 fmask_47 P_47 autos_47 bk_47_5 6 nd_47_6_1 = true := by decide +kernel
def nodes_47_6 : List NodeSpec := nd_47_6_0 ++ nd_47_6_1
set_option maxRecDepth 500000 in
lemma chk_47_6 : checkNodesBT W_47 G_47 fmask_47 P_47 autos_47 bk_47_5 6 nodes_47_6 = true := by
  unfold nodes_47_6 checkNodesBT; simp only [List.all_append, Bool.and_eq_true]
  exact ⟨chk_47_6_0, chk_47_6_1⟩
def bk_47_6 : BT (List (List Nat)) := buildBucketsBT W_47 nodes_47_6
set_option maxRecDepth 500000 in
lemma bk_47_6_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_47 6 xs.toFinset) bk_47_6 :=
  buildBucketsBT_sound (by decide) gp_47 W_47_ok P_47_ok autos_47_ok bk_47_5_ok chk_47_6
def nd_47_7_0 : List NodeSpec := [([11,147,0,1,2,54,5],[110,15,11,17,40,6,111,118,119],[1,0]),([9,0,1,2,148,3,4,5],[120,43,35,11,121],[]),([25,129,9,1,2,3,4,5],[11,35],[]),([25,149,0,1,2,3,4,5],[47,122,123],[1]),([14,12,2,3,135,5],[47,80,23,30,124,24],[1]),([105,2,13,3,4,5],[13,14,48,125,2,126],[1]),([150,9,0,1,2,3,4,5],[35,11,127,128],[]),([48,28,12,2,3,4,5],[13,47,11,23,2,24,30],[1]),([129,9,1,27,2,3,4,5],[57,121,35,42,129,130],[]),([43,14,12,29,2,3,4],[23,131,2,14,132,13,45],[1]),([149,0,1,27,2,3,4,5],[122,43,121,35,123,120,23],[]),([151,0,1,2,3,4,5],[35,47,43,11,133,110,120,134,17],[]),([48,14,49,2,3,4,5],[2,13,11,30,24,57,14],[1]),([34,0,1,49,36,4,5],[2,135,11,14,136],[1]),([11,10,0,1,152,2,3,5],[137,42,111,130,30],[1]),([11,10,0,153,2,3,5],[110,40,30,138,121,15],[]),([154,9,0,27,2,3,4,5],[35,47,127,128],[]),([11,155,0,1,2,3,5],[110,41,40,30,130,139],[]),([11,0,1,2,82,3,5],[110,41,48,140,14],[]),([14,49,36,2,4,5],[30,11,13,2,141,14,142],[1]),([123,10,0,1,36,2,4,5],[18,2,44,122,139,130,143],[1]),([11,0,1,12,2,156,5],[110,41,17,40,42,138,44,112,111],[1]),([10,0,35,2,157,4,5],[47,135,44,144],[]),([0,35,158,2,3,4,5],[47,135,11,130,145],[]),([6,0,1,2,82,3,4],[23,14,146,147,120],[]),([159,0,1,2,3,4,5],[47,18,43,148,133,110,120,134,57,149],[]),([108,11,10,53,2,3,5],[6,137,40,17,150,48,151],[1]),([11,10,53,29,2,3,5],[150,17,48,151,14,121],[1]),([30,10,53,29,3,4,5],[135,2,14,6],[1]),([160,0,1,3,4,5],[35,47,30,6,24,23],[1]),([10,53,2,101,3,4,5],[135,2,14,15,6],[1]),([10,53,36,29,2,3,4,5],[14,55,2],[1]),([0,1,2,161,3,4,5],[35,18,14,120,43,152,133,110],[]),([10,53,36,29,3,4,5],[14,121,2,151],[1]),([30,105,2,3,4,5],[2,13,153,6,23,14],[1]),([10,53,84,36,2,3,4,5],[23,14,55],[1]),([10,53,84,2,3,4,5],[14,121,55,154],[1]),([162,14,2,3,4,5],[47,18,155,17,156,23],[1]),([0,1,38,2,163,4,5],[135,148,14],[]),([98,11,0,1,33,3,5],[42,148,137,40,157,158],[1]),([6,0,1,33,29,3,4],[23,159,135,14,160,161],[]),([28,0,1,2,164,3,4],[23,11,107,158,152,120,17],[]),([98,11,14,0,1,2,3,5],[110,24,30,148,41,17],[1]),([108,11,14,0,1,2,3,5],[110,24,30,6,17],[]),([133,0,1,36,3,4,5],[122,11,152,162,163,164],[]),([123,0,1,12,36,2,4,5],[152,130,18,2,122,165],[1]),([165,0,1,36,2,3,4,5],[134,18,2,139,152,166,165,167],[]),([14,166,2,3,4,5],[47,18,2,30,23],[1]),([167,1,12,36,2,3,4,5],[30,122,130,148],[1]),([165,0,1,2,3,4,5],[120,18,43,139,152,133,110,165,166,168,167],[]),([105,52,2,3,4,5],[2,13,169,30,24,23,81],[1]),([167,1,12,2,3,4,5],[47,35,170,171,122,148,172,120],[]),([108,11,0,1,40,2,3],[6,17,40,130,48],[]),([168,0,1,49,2,3,4,5],[120,173],[1]),([10,53,29,2,13,3,4],[14,121,2,55],[1]),([0,1,49,36,29,2,4,5],[107,11,152,2],[1]),([11,0,1,12,152,2,3,5],[42,15,174,130,111],[1]),([45,0,59,1,29,2,3,4],[107,57],[]),([83,0,1,49,36,2,4,5],[11,2,44,136,164],[1]),([0,1,49,84,36,2,4,5],[2,135,152,14,136],[1,2]),([0,1,91,49,36,2,4,5],[2,57,11,164],[1]),([123,44,0,1,2,4,5],[120,47,35,122,14,121],[]),([169,0,1,49,2,3,4,5],[134,107,122,57,2,175],[1]),([130,0,1,91,2,3,4,5],[107,57,120],[1]),([0,35,170,2,3,4,5],[139,14,145,47,42,140],[]),([0,1,106,91,2,3,4,5],[120,2,134,57,122,176],[]),([11,14,0,1,152,2,3,5],[42,24,30,174,130,111,148],[1]),([0,35,86,29,2,3,4,5],[145,47,135,130],[]),([14,91,49,2,3,4,5],[30,13,11,14,46,2,57,17,177],[1]),([11,14,0,1,2,156,5],[110,41,17,40,42,138,44,112,111],[1,2]),([105,32,2,3,4,5],[13,14,48,24],[]),([11,171,0,1,2,3,5],[110,41,6,137,15,42,178,130,139],[]),([11,14,0,1,2,172,5],[110,17,30,148,24],[1]),([11,14,0,1,173,2,3,5],[30,17,24,148],[1]),([123,14,0,1,36,2,4,5],[18,2,44,122,130,139,179],[1]),([14,0,1,36,2,174,3,4],[14,44,13],[1]),([83,10,53,2,3,4,5],[43,14,18,121,15,180,55],[1]),([129,14,0,21,1,2,3,4],[135,23,57],[]),([14,49,2,31,3,4,5],[30,2,11,15,6,14],[1]),([14,9,1,2,164,3,4],[130,11,135,23,158],[]),([175,9,1,2,3,4,5],[35,18,181,130,2,11],[]),([98,11,10,53,2,3,5],[6,17,40,48,151],[1]),([10,45,0,29,2,3,4],[23,57,14,149],[]),([108,11,14,12,2,3,5],[6,30,24,17,49,48,46],[1]),([109,11,14,12,2,3,5],[30,17,24,6,48,14,49],[1]),([0,1,2,176,3,4,5],[14,120,18,133,110],[]),([11,34,14,12,2,3,5],[6,17,49,14],[1]),([0,1,2,31,3,115,5],[35,47,182,30,183,110,120,111],[]),([14,12,29,2,13,3,4],[14,184,2,45],[1]),([14,106,49,2,3,4,5],[30,13,11,2,15,17,46,57,185,186],[1]),([123,14,12,2,3,4,5],[47,13,187,23,2,45,15,188,14],[1]),([50,48,12,3,4,5],[47,13,30,23],[1]),([14,12,29,2,114,3,4,5],[23,13,45],[1]),([30,14,12,29,3,4,5],[2,14,6],[1]),([34,10,53,36,3,4,5],[135,2,14],[1]),([14,12,88,2,3,4,5],[14,2,15,6],[1]),([14,12,2,101,3,4,5],[14,2,15,6],[1]),([0,1,49,88,2,4,5],[2,135,120,15],[1]),([83,14,12,36,2,3,4,5],[23,11,2,45,14,46],[1]),([14,0,1,29,2,3,115],[23,144,179,182,130,14,111,189],[1]),([14,12,84,2,3,4,5],[14,170,13,45,190],[1]),([11,0,1,2,114,3,5],[110,41,24,139,138,14],[]),([177,14,2,3,4,5],[47,18,169,13,30,6,191,23],[1]),([11,48,14,12,2,3,5],[24,17,49,30,48,14],[1]),([14,12,36,2,120,3,4,5],[30,13,14],[1]),([130,14,49,2,3,4,5],[2,13,30,11,17,57,46,6],[1]),([14,12,84,36,2,3,4,5],[30,23,14,45],[1]),([34,14,49,2,3,4,5],[2,13,30,11,14,6],[1]),([14,49,29,2,3,4,5],[14,46,11,2,192],[1]),([178,0,2,3,4,5],[35,11,17,23,193],[1]),([105,29,2,3,4,5],[13,19,2,14,48,194,126,22],[1]),([0,1,29,134,3,4,5],[148,14,163,44,174],[]),([11,133,0,1,2,3,5],[110,41,48,164,146,15],[]),([98,11,0,1,40,2,3],[6,17,137,40,48,130,195],[1]),([11,105,14,2,3,5],[24,17,30,14],[1]),([105,14,179,2,3,4,5],[2,13,6,47,196,60,24,56],[1]),([52,12,31,3,4,5],[47,2,30,23],[1]),([14,0,1,180,2,3,115,5],[47,24,35],[1]),([181,105,2,3,4,5],[23,13,2,11,24,126,14],[1]),([105,14,2,182,3,4,5],[2,13,6,47,52,89],[1]),([105,48,2,3,4,5],[13,47,11,24,23,2,30,14],[1]),([183,105,2,3,4,5],[2,13,11,6,126,96,73],[1]),([105,14,29,2,3,4,5],[2,13,14,19,194,126],[1]),([11,105,2,3,5],[17,15,14,153],[1]),([0,1,49,2,184,4,5],[2,135,11,15],[1]),([0,1,2,82,13,3,4],[23,120,134,14,146],[]),([105,14,36,2,3,4,5],[2,13,30,197,14],[1]),([105,185,2,3,4,5],[23,13,14,24,126,19,2,22,198],[1]),([14,186,2,3,4,5],[30,18,153,14,13,17,199],[1]),([105,179,2,3,4,5],[2,13,60,24,56,200],[1]),([10,187,0,35,2,3,4,5],[43,42,47],[]),([188,105,2,3,4,5],[11,13,2,153,24,23,14],[1]),([189,105,2,3,4,5],[2,13,11,24,23,85,72],[1]),([48,43,0,1,29,2,3,4],[152,120,23,2],[1]),([15,11,10,53,2,3,5],[48,40,15,17,150,6,151,14],[1]),([105,43,2,3,4,5],[57,13,30,24,23,2,201],[1]),([25,129,0,1,2,3,4,5],[47,122,35],[1]),([122,190,2,3,4,5],[47,122,35,2,42,23],[]),([14,12,36,29,3,4,5],[14,162,2,46],[1]),([191,14,2,3,4,5],[47,18,102,30,48,202,13],[1]),([15,11,14,12,2,3,5],[48,30,14,17,49,6,46],[1]),([11,10,0,1,2,156,5],[110,41,17,40,138,42,44,111,112],[1]),([34,0,35,86,2,3,4,5],[11,158,135,144],[]),([121,14,12,2,3,4,5],[47,203,30,15,204,23],[1]),([111,14,1,29,2,3,4],[120,23,14,144,48],[]),([48,0,1,2,3,115,5],[35,47,30,48,110,205,120,23],[1]),([105,2,31,3,4,5],[2,13,11,15,6,126,14],[1]),([83,10,53,36,2,3,4,5],[23,11,2,55,14,151],[1]),([44,14,49,2,4,5],[11,30,13,17,14,24],[1]),([188,14,2,3,4,5],[11,13,30,17,24,14],[]),([11,14,12,29,2,3,5],[49,17,48,46,14,206],[1]),([30,105,14,2,3,4,5],[2,13,47,30,6,23,14],[1]),([34,14,12,36,3,4,5],[2,30,14],[1]),([10,53,88,2,3,4,5],[135,2,15,6,14],[1]),([14,137,12,2,3,4,5],[47,2,30,13,15,24,14],[1]),([125,14,12,36,2,3,4,5],[47,30,13],[1]),([105,28,2,3,4,5],[11,13,30,24,23,2,207],[1]),([0,1,36,82,3,4,5],[30,14,135,146],[]),([0,1,36,2,192,3,4,5],[139,44,14,179],[1]),([14,12,2,145,3,4],[13,2,45,14,46,6],[1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_47_7_0 : checkNodesBT W_47 G_47 fmask_47 P_47 autos_47 bk_47_6 7 nd_47_7_0 = true := by decide +kernel
def nd_47_7_1 : List NodeSpec := [([0,1,2,193,3,4,5],[120,18,208,43,209,139,152,133,110,164],[]),([105,36,2,3,4,5],[13,2,153,17,197,14],[1]),([14,12,2,3,115,5],[47,210,30,49,23],[1]),([133,0,1,2,13,3,4],[120,134,2,139,184,211,212,57,146],[]),([79,14,12,2,3,4,5],[47,213,30,15,214,23],[1]),([28,0,1,2,145,3,4],[23,144,107,215,152,120,13,24,14],[]),([28,0,1,2,194,3,4],[23,144,107,215,152,120,14,216],[]),([80,44,1,2,4,5],[35,47,30,40,23],[]),([188,14,49,2,3,4,5],[11,30,13,2,17,57,14,24],[1]),([80,25,2,3,4,5],[47,35,11,17,23],[]),([0,1,49,36,29,4,5],[14,121,162,163,107,11,152,164,136],[1]),([48,14,12,36,2,3,4,5],[30,13],[1]),([0,1,2,195,3,5],[30,42,148,110,111],[1]),([14,12,2,136,3,4,5],[30,2,15,6,14],[1]),([196,0,35,2,3,4,5],[47,43,130,135,145],[]),([83,14,12,2,3,4,5],[47,13,217,11,2,15,218,45,14],[1]),([48,14,12,29,2,3,4,5],[23,45,13],[1]),([0,1,2,197,3,4,5],[35,18,13,139,133,110,120,24,14],[]),([14,137,0,1,36,2,4,5],[13,122,30],[1]),([14,9,1,2,145,3,4],[130,135,2,23,13,14],[]),([11,14,0,1,2,145,3],[14,24],[1]),([14,139,12,2,3,4,5],[47,2,23,13,14,15,24,45],[1]),([105,14,185,2,3,4,5],[57,13,14,48,2,24],[1]),([11,14,12,2,31,3,5],[49,17,6,30,14],[1]),([105,44,2,3,4,5],[13,2,30,17,24,14],[]),([11,0,198,1,2,54,5],[11,17,40,6,118,111,219],[0,1,3]),([48,43,12,2,3,4,5],[13,47,30,24,23,2],[1]),([105,14,186,2,3,4,5],[11,13,24,14,2],[1]),([14,12,2,145,3,4,5],[23,2,14,15,6],[1]),([11,34,10,53,2,3,5],[6,17,150,14],[1]),([199,14,0,1,2,3,115,5],[47,24,179,110,138,220],[1]),([105,2,182,3,4,5],[13,2,52,6,89],[1]),([11,0,1,200,2,3,5],[110,15,6,17,40,130,139],[1]),([0,1,36,2,176,3,4,5],[139,44,14],[]),([0,1,201,49,2,3,4,5],[107,2,6],[1]),([34,105,2,3,4,5],[2,13,11,6,126,14],[1]),([50,105,2,3,4,5],[47,2,11,30,6,23],[1]),([202,0,1,2,3,4,5],[47,18,43,11,133,110,120,134,35,17],[]),([14,12,36,29,2,3,4,5],[14,45,2],[1]),([105,186,2,3,4,5],[11,13,153,24,14,2,199],[1]),([123,10,53,2,3,4,5],[43,14,18,121,55,15,221],[1]),([98,11,14,12,2,3,5],[6,17,24,30,48,46,49],[1]),([34,105,14,2,3,4,5],[2,13,47,11,14,6],[1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_47_7_1 : checkNodesBT W_47 G_47 fmask_47 P_47 autos_47 bk_47_6 7 nd_47_7_1 = true := by decide +kernel
def nodes_47_7 : List NodeSpec := nd_47_7_0 ++ nd_47_7_1
set_option maxRecDepth 500000 in
lemma chk_47_7 : checkNodesBT W_47 G_47 fmask_47 P_47 autos_47 bk_47_6 7 nodes_47_7 = true := by
  unfold nodes_47_7 checkNodesBT; simp only [List.all_append, Bool.and_eq_true]
  exact ⟨chk_47_7_0, chk_47_7_1⟩
def bk_47_7 : BT (List (List Nat)) := buildBucketsBT W_47 nodes_47_7
set_option maxRecDepth 500000 in
lemma bk_47_7_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_47 7 xs.toFinset) bk_47_7 :=
  buildBucketsBT_sound (by decide) gp_47 W_47_ok P_47_ok autos_47_ok bk_47_6_ok chk_47_7
def nd_47_8_0 : List NodeSpec := [([11,0,1,2,54,5],[110,15,11,111],[0,3,1,4]),([11,0,55,1,2,3,5],[110,30,15,41,148,17,138,42,139,130,111],[]),([56,0,1,2,3,4,5],[43,23,18,11,130,122,30,107,133,110,13,17,24],[]),([57,0,1,2,3,4,5],[43,122,18,181,42,110,133,120,47,2,23,13,161],[]),([0,58,1,2,3,4,5],[139,30,18,148,57,122,107,133,110,120,130,149,222,121],[]),([45,0,59,1,2,3,4,5],[47,57,107,223,42,30,149],[1]),([0,59,1,2,3,4,5],[122,18,35,47,57,224,42,149,110,120,225],[]),([6,0,1,60,2,3,4,5],[57,226,120,122,135,158,137,149],[]),([8,61,1,2,3,4,5],[130,57,43,145,13,42,40,24],[]),([62,0,1,2,3,4,5],[43,130,18,57,144,122,107,133,110,13,40,24],[]),([0,1,63,2,3,4,5],[128,120,181,148,122,107,133,110,48,130],[]),([64,0,1,2,3,4,5],[134,47,18,107,122,130,110,133,57,24,149],[]),([20,0,1,29,2,3,4,5],[23,139,2,120,47,152,144,122,14,111,138,15,227],[]),([9,0,65,1,2,3,4,5],[130,122,35,11,135,144,13,137,228,42,121],[]),([61,9,1,2,3,4,5],[35,181,18,42,130,43,121,40,229],[]),([0,66,1,2,3,4,5],[181,130,11,47,134,122,107,133,110,144,17],[]),([67,0,1,2,3,4,5],[35,43,134,107,122,130,110,133,128,48],[]),([0,1,68,2,3,4,5],[128,181,18,11,130,122,107,133,110,48],[]),([51,9,1,2,3,4,5],[23,18,42,30,15],[]),([45,9,0,1,2,3,4,5],[134,47,139,11,57,35,2,42,130,149,128,223],[4]),([69,0,1,2,3,4,5],[47,134,35,107,122,130,110,133,23,17,230],[]),([16,9,0,1,2,4,5],[139,130,35,57,17,149],[0,3]),([34,25,9,0,1,2,3,4,5],[130,158,35,11,135,2,23,121],[]),([25,9,0,1,29,2,3,4,5],[135,139,121,130,231,42,23,11,232,233],[1]),([34,20,0,1,2,3,4,5],[107,47,161,144,2,11,14,6],[]),([25,9,6,1,2,3,4,5],[11,35,129,158,17,130,30,121,232],[1]),([25,24,0,1,2,3,4,5],[128,11,35,123,158,17,120,145,47,234,121,232],[1]),([25,6,0,1,2,3,4,5],[181,47,120,57,11,139,35,2,161,111,15,144,234,17,232],[1]),([11,51,0,1,2,3,5],[110,30,41,15,235,17,138,42,130],[]),([25,0,1,2,70,3,4,5],[47,2,11,234,122,17,144],[]),([26,71,0,1,2,3,4,5],[35,11,2,122,17,23,43,30],[1]),([9,0,1,72,2,3,4,5],[35,43,233,107,135,122,42,236,23],[]),([73,0,1,2,3,4,5],[43,122,18,42,110,133,134,120,47,2,13,161],[]),([74,9,1,2,3,4,5],[35,133,18,42,130,43,30,17,237,23],[]),([34,9,0,1,27,2,3,4,5],[35,11,130,158,23,144,2,238],[]),([9,0,1,27,29,2,3,4,5],[23,144,11,127,128,121,145],[1]),([9,0,1,75,2,3,4],[130,233,11,135,137,17],[4]),([9,0,76,1,2,3,4,5],[11,122,107,42,47,239,17,158,35,30],[]),([9,0,1,77,2,3,4,5],[11,233,122,107,135,137,17,158],[]),([9,6,1,27,2,3,4,5],[11,35,30,121,17,240,158,129,130,139,127,23],[1]),([71,28,0,1,2,3,4,5],[135,11,35,145,47,17,23,2,122],[]),([28,0,1,2,78,3,4,5],[35,11,107,42,17,23,47,145],[1]),([79,9,0,1,2,3,4,5],[43,122,35,107,42,2,11,241,139,130,242,47,23,30],[]),([80,9,1,2,3,4,5],[35,133,181,42,130,47,145,40,23],[1]),([81,0,1,2,3,4,5],[35,135,18,181,161,23,2,158],[]),([10,0,1,29,2,13,3,4],[14,184,152,120,243,42,139,111,244,121,211,2,143],[1]),([0,1,2,82,3,4,5],[23,135,147,152,120,245,181,133,110,146],[1]),([30,10,0,1,29,3,4,5],[107,42,135,14,152,157,130],[1]),([10,0,1,36,29,3,4,5],[14,162,44,122,152,246,139,130,121,163,135,140],[1]),([83,10,0,1,36,2,3,4,5],[130,161,23,11,135,44,143,14,140],[1]),([83,10,0,1,2,3,4,5],[43,120,161,14,47,15,247,143,217,44,121],[1]),([10,0,1,84,36,2,3,4,5],[122,135,44,139,130,142,148,23,14,143],[1]),([10,0,1,84,2,3,4,5],[14,170,143,248,122,249,139,121,18,43],[1]),([34,10,0,35,2,3,4,5],[43,158,135,11,148,145,47,14,157],[1]),([85,10,0,35,2,3,4,5],[47,135,11,148,145,40,144],[1]),([34,25,0,1,2,3,4,5],[107,47,161,144,35,11,121,17,250,234,2,139,23],[]),([0,35,86,2,3,4,5],[11,43,47,145,137,42,130,144],[1]),([87,0,1,2,3,4,5],[35,135,18,181,122,110,133,134,120,42,148,2,40,14,157],[]),([10,6,0,1,29,2,3,4],[120,134,23,2,152,251,161,139,14,111,244,159,18,135,252,253],[1]),([10,45,0,2,3,4,5],[35,57,18,148,48,149],[1]),([10,53,2,13,3,4,5],[14,121,2,48,254,255],[1]),([11,10,53,2,3,5],[137,15,17,14,256],[1]),([10,53,29,2,3,4,5],[245,253,23,55,11,14,151,15,257,2,255],[1]),([10,0,1,88,2,3,4,5],[135,14,130,161,107,157],[1]),([10,0,1,36,29,2,3,4,5],[122,44,152,130,14,143,135],[1]),([14,49,2,3,4,5],[30,258,15,14,11],[1]),([10,53,36,2,3,4,5],[259,142,11,2,15,17,260,23,14,256],[1]),([34,0,1,38,2,3,4,5],[35,11,135,161,145,14,157],[]),([14,89,1,2,3,4,5],[47,133,107,30,261,23,18],[]),([0,1,38,29,2,3,4,5],[14,121,2,43,135,245,120,152,122,138,111,137,262],[]),([90,0,1,2,3,4,5],[47,35,122,42,110,133,134,120,23],[]),([0,1,91,49,2,3,4,5],[11,145,134,57,164,2,17,263,264],[1]),([92,0,1,2,3,4,5],[122,181,35,43,110,133,134,120,145,148,161],[]),([25,0,1,29,2,3,4,5],[139,2,23,120,47,152,144,122,121,111,138,11,232,233,265],[]),([93,0,1,38,2,3,4,5],[35,11,135,122,145,40,23,14],[1]),([30,0,1,33,3,4,5],[35,2,43,135,122,42,148,40,161,157],[]),([94,0,1,2,3,4,5],[35,135,18,122,110,133,134,120,42,148,157,161,14],[]),([0,1,95,2,3,4,5],[148,135,266,47,122,42,40,161,110],[]),([9,0,1,33,2,3,4,5],[35,43,233,11,135,122,2,267,23,42],[]),([45,0,1,2,13,3,4],[134,57,120,42,30,148,121,149,268],[]),([96,0,1,2,3,4,5],[139,47,18,107,122,130,110,133,35,269,270,144],[0]),([34,14,0,1,2,3,4,5],[107,47,161,23,43,2,11,14,6],[]),([14,0,1,29,2,3,4,5],[135,2,120,47,152,23,122,139,14,111,138,253,144,15,271],[]),([11,0,97,1,2,3,5],[110,15,42,30,138,139,130,111],[3]),([8,0,65,1,2,3,4,5],[130,18,122,135,13,24,42],[]),([30,14,0,1,2,3,4,5],[107,47,42,30,35,18,2,6,23,14],[]),([28,0,1,29,2,3,4,5],[23,144,152,120,122,14,111,138,17,272,215],[]),([44,0,1,2,3,4,5],[43,35,181,11,145,18,47,122,30,107,133,110,120,134,17,24,14],[]),([83,0,1,12,36,2,3,4,5],[130,2,161,23,11,44,165,273,274,164],[1]),([98,11,0,1,12,2,3,5],[6,17,137,30,110,48,164,40,112,111],[1]),([0,1,99,2,3,4,5],[2,107,43,135,161,6,158],[]),([45,0,1,2,100,3,4,5],[47,2,57,223,122,44,30,149,120],[]),([0,1,12,2,101,3,4,5],[2,135,120,152,275,138,6],[1]),([0,1,102,2,3,4,5],[2,107,43,135,122,133,110,120,134,42,17,6],[]),([0,1,49,36,2,4,5],[142,259,107,2,11,17,136,276],[1]),([0,1,12,36,29,3,4,5],[14,121,162,163,122,44,152,277,138,278,130,139,2,273,164],[1]),([30,10,53,2,3,4,5],[43,2,135,256,6,23],[1]),([0,1,12,84,2,3,4,5],[14,121,18,170,165,43,273,122,44,279,280,281],[1,2]),([11,34,10,0,1,2,3,5],[157,17,282,280,111,137,158,138,148,14],[1]),([14,0,1,84,36,2,3,4,5],[122,30,44,130,139,23,14,179],[1]),([103,0,1,2,3,4,5],[35,44,18,43,47,110,133,134,120,142,17,135,40,259,174],[]),([0,1,95,38,2,3,4,5],[145,35,11,148,107,135,137,40,14],[]),([83,0,1,12,2,3,4,5],[35,18,47,43,120,217,161,11,2,15,283,165,121,14,44,274,273],[1]),([45,0,1,29,2,3,4],[134,57,120,107,223,130,111,149,144,159,284],[1,2,4]),([104,0,1,2,3,4,5],[134,122,18,43,181,130,110,133,57,128],[]),([11,0,1,40,2,3],[15,137,130,17],[1]),([45,9,1,2,3,4,5],[35,11,30,42,18,57,285,130,121],[4]),([0,1,40,36,2,3,4],[142,130,259,2,15,17,286],[]),([105,2,3,4,5],[153,15,126],[1]),([0,1,106,49,2,3,4,5],[11,145,107,2,15,17,164,57,161,185,287],[1]),([11,0,1,41,2,3,5],[15,137,110,42,41,17,158],[]),([30,0,1,41,3,4,5],[2,43,122,15,107,135,181,130,42,17,161,6],[]),([11,0,1,33,2,3,5],[148,40,288,110,42,137,158],[1]),([0,1,41,36,3,4,5],[142,107,122,43,42,17,135,40,161,181],[]),([107,0,1,2,3,4,5],[107,2,43,122,110,133,134,120,135,42,17,161,6],[]),([0,1,106,2,3,4,5],[289,47,122,43,42,17,135,40,161,110],[]),([98,11,14,0,1,2,3,5],[290,220,24,30,15,148,137,291,14,292,41,293,40,17,112,111],[1]),([108,11,14,0,1,2,3,5],[290,110,30,174,24,148,17,294,220,14,292,293,40,42,295,111],[1]),([109,11,14,0,1,2,3,5],[30,41,17,137,24,290,14,293,220],[1]),([11,14,0,1,2,31,3,5],[30,24,220,17,42,14],[1]),([34,0,1,33,3,4,5],[35,2,43,135,161,23,158],[]),([11,34,14,0,1,2,3,5],[290,17,220,111,280,6,158,14,137,30,121],[1]),([6,0,59,1,2,3,4,5],[57,120,122,161,47,224,158,149,35,144,296],[]),([14,12,36,2,3,4,5],[142,47,30,13,2,297,14,258],[1]),([14,0,1,88,2,3,4,5],[135,2,47,161,130,13,14,298,299],[1]),([110,0,1,2,3,4,5],[47,35,134,122,181,30,110,133,120,161],[]),([111,14,1,2,3,4,5],[47,133,120,18,35,30,48],[1]),([14,0,1,29,2,13,3,4],[14,121,152,120,42,139,111,244,2,179],[1]),([14,12,2,31,3,4,5],[13,2,11,15,6,300,14],[1]),([14,9,1,29,2,3,4,5],[139,23,121,130,42,245,15,301,302],[]),([11,14,0,1,29,2,3,5],[111,280,220,17,303,292,14,121,138,42],[1]),([34,10,0,1,36,3,4,5],[107,161,135,148,14,44,157],[1]),([112,0,1,2,3,4,5],[47,35,107,134,181,30,110,133,152,146],[]),([34,44,0,1,2,3,4,5],[107,13,161,30,35,23,14,17,304,305,2,139,144],[]),([0,1,12,88,2,3,4,5],[2,135,161,130,306,138,6,307],[1]),([0,1,33,36,3,4,5],[148,135,308,107,122,42,40,161,181,309],[]),([113,0,1,2,3,4,5],[47,35,107,181,110,133,134,120,44,23],[]),([34,0,1,12,36,3,4,5],[2,135,107,161,14,273,44,306,138,6,130],[1]),([14,0,1,29,2,114,3,4,5],[23,13,120,179,152],[1]),([0,1,2,114,3,4,5],[23,13,134,152,181,133,110,107,24],[1]),([10,0,35,29,2,3,4,5],[144,14,130,42,145,135,140,310],[1]),([14,0,1,2,101,3,4,5],[135,2,42,47,152,13,14,311,120,121],[1]),([0,1,2,3,115,5],[47,210,35,312,130,110,111],[]),([116,0,1,2,3,4,5],[47,35,181,122,42,110,133,134,120,23],[]),([117,0,1,2,3,4,5],[43,42,18,181,133,110,120,134,30,2,135,13,6,14,24],[]),([34,14,0,1,36,3,4,5],[107,30,161,148,14,299,2,44,313,135],[1]),([28,0,1,2,3,4,5],[47,35,107,122,30,110,133,134,120,17,314,23],[]),([14,0,1,36,29,2,3,4,5],[122,44,152,130,14,179,299],[1]),([15,11,0,1,12,2,3,5],[48,148,15,30,110,17,280,315,6,40,158,174,130,164,316],[1]),([11,118,0,1,2,3,5],[110,130,30,148,137,138,42,111],[0,3]),([119,9,0,1,2,3,4,5],[122,35,11,42,2,139,317,130,47,135,318,319,128,158,30],[4]),([34,28,0,1,2,3,4,5],[107,47,161,23,144,14,17,320,215,120],[]),([14,0,1,84,2,3,4,5],[14,121,13,179,44,122,321,139],[1]),([14,0,1,2,3,115,5],[47,35,130,30,110,322,111,220,23],[1]),([34,0,1,49,2,3,4,5],[2,43,135,11,161,306,6,263],[1]),([0,1,2,120,3,4,5],[30,13,44,181,133,110,120,134,24],[]),([121,0,1,2,3,4,5],[122,18,35,43,47,181,130,110,133,203,323],[]),([34,10,53,2,3,4,5],[43,2,135,11,6,255],[1]),([122,14,1,2,3,4,5],[47,133,35,18,30,122,135,23],[4]),([123,0,1,12,2,3,4,5],[35,18,47,43,152,187,130,23,2,57,165,15,324,121,14,325,122,277],[1])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_47_8_0 : checkNodesBT W_47 G_47 fmask_47 P_47 autos_47 bk_47_7 8 nd_47_8_0 = true := by decide +kernel
def nd_47_8_1 : List NodeSpec := [([30,14,0,1,29,3,4,5],[107,42,14,299,2,152,326,130,135,30,121],[1]),([124,0,1,2,3,4,5],[35,181,42,47,133,110,120,134,30,148,23,14],[]),([125,14,0,1,36,2,3,4,5],[44,47,30,13],[1]),([126,0,1,2,3,4,5],[35,134,47,107,122,130,110,133,144,40,327],[]),([79,0,1,2,3,4,5],[122,18,35,43,47,181,42,110,133,134,120,213,328,23,144],[]),([127,0,1,2,3,4,5],[122,181,35,47,42,110,133,134,120,30,148,161],[]),([14,6,0,1,29,2,3,4],[120,23,134,2,13,152,161,139,14,111,244,144,253,299,329],[2]),([122,52,1,2,3,4,5],[133,35,42,47,23],[1,4]),([37,48,0,1,3,4,5],[35,13,18,148,23],[]),([30,0,1,40,2,3,4],[2,43,135,130,6],[]),([128,0,1,2,3,4,5],[43,23,18,2,144,135,122,161,158,133,110],[]),([14,6,0,21,1,2,3,4],[120,134,43,23,57,13,14,24,330,144],[1,2]),([26,25,0,2,3,4,5],[35,11,17,331,23],[1]),([14,0,1,36,2,120,3,4,5],[30,13,122,14],[1]),([129,14,0,1,2,3,4,5],[134,122,47,135,57,35,11,148,149,2],[1]),([108,11,0,1,12,2,3,5],[6,148,30,137,110,17,174,315,48,164,40,42,295,111],[1]),([10,0,1,2,101,3,4,5],[135,14,107,42,152,157,120],[1]),([0,1,49,29,2,3,4,5],[14,121,2,253,135,245,120,164,11,152,122,138,111,263,332],[1]),([130,0,1,49,2,3,4,5],[2,43,135,122,11,17,57,164,152,6],[1]),([11,45,0,1,2,3,5],[110,30,41,148,149,333,334,130,121,15,138,42],[]),([14,9,1,2,78,3,4,5],[11,35,42,23,30,145,17],[1]),([11,0,1,12,29,2,3,5],[111,280,315,17,48,164,316,14,121,206,42,138],[1]),([131,0,1,2,3,4,5],[122,134,35,47,181,130,110,133,23,144],[]),([79,14,0,1,2,3,4,5],[181,47,107,215,122,35,30,15,328,23],[1]),([28,0,1,2,132,3,4,5],[47,35,215,122,30,335,23],[1]),([25,14,9,2,3,4,5],[35,43,11,17,23],[]),([11,14,0,1,2,3,5],[110,30,41,15,17,14,138,42],[1]),([52,14,12,2,3,4,5],[47,169,13,11,30,124,23,2],[1]),([133,0,1,2,3,4,5],[120,152,18,43,181,110,133,253,245,146],[1]),([11,48,14,0,1,2,3,5],[24,17,220,30,138,14],[1]),([34,14,12,2,3,4,5],[47,2,13,11,6,300,23,14],[1]),([44,14,9,1,2,4,5],[181,30,18,35,13,24,23],[]),([0,1,12,84,36,2,3,4,5],[2,135,122,44,130,139,23,14,273,165,279],[1,2]),([96,9,0,1,2,3,4,5],[134,47,139,43,30,35,2,42,270,130,23],[4,5,0]),([105,14,2,3,4,5],[18,13,30,15,23,153,126,14],[1]),([30,14,12,2,3,4,5],[47,2,13,258,6,23,30,14],[1]),([0,1,2,134,3,4,5],[148,135,336,47,44,40,259,110,120,134,14,174],[1]),([32,14,12,2,3,4,5],[23,13,300,14,48,24],[1]),([11,10,0,1,29,2,3,5],[111,280,282,17,48,140,14,206,138,42,121],[1]),([0,1,2,3,135,5],[47,80,35,337,122,42,110,111],[1]),([43,14,0,1,29,2,3,4],[134,23,144,13,299,14,189,179,338],[1,2]),([14,0,1,2,136,3,4,5],[135,2,30,13,15,24,14],[1]),([137,0,1,2,3,4,5],[35,42,18,47,43,133,110,120,134,30,13,148,24,161,158],[]),([15,11,10,0,1,2,3,5],[48,110,280,40,148,15,282,157,14,174,158,130,140],[1]),([43,14,12,2,3,4,5],[47,339,2,11,30,340,23,300],[1]),([125,0,1,2,3,4,5],[43,122,18,42,110,133,134,120,30,13,161],[]),([48,28,0,1,2,3,4,5],[44,13,47,11,30,24,23,2,122],[1]),([15,11,14,0,1,2,3,5],[14,280,110,30,137,220,290,341,17,174,158,130,40,121,292],[1]),([80,14,1,2,3,4,5],[47,133,35,18,43,145,40,23],[1]),([48,6,0,1,2,3,4,5],[43,122,120,57,161,35,2,139,148,111,15,135,47,24],[]),([121,14,0,1,2,3,4,5],[134,47,107,338,122,35,30,15,323,23],[1]),([98,11,10,0,1,2,3,5],[157,40,110,15,148,48,140,138,111,112,17],[1]),([52,0,1,2,3,4,5],[47,35,122,181,42,110,133,134,120,23],[]),([28,14,12,2,3,4,5],[47,342,2,30,343,23,258],[1]),([28,0,27,2,3,4,5],[35,11,17,344,23],[1]),([138,0,1,2,3,4,5],[181,122,18,43,110,133,134,120,11,145,17],[]),([34,8,14,1,2,3,4,5],[18,2,13,30,14,6],[]),([10,129,0,1,2,3,4,5],[134,43,122,35,57,2,130,148,149,47,345],[1]),([10,25,0,2,3,4,5],[35,11,17,18,23],[]),([30,0,1,12,29,3,4,5],[107,2,14,277,135,130,152,138,6],[1]),([14,139,0,1,2,3,4,5],[120,47,161,23,144,13,14,15,24,179],[1]),([111,0,1,2,3,4,5],[120,134,47,18,35,107,122,181,130,110,133,128,48],[]),([24,0,1,27,2,3,4,5],[35,43,30,144,11,135,17,346,158,123,120,139,127,23],[1]),([44,14,12,2,3,4,5],[11,30,13,18,258,17,24,14],[1]),([140,0,1,2,3,4,5],[122,134,35,43,181,130,110,133,23,128],[]),([52,0,1,31,3,4,5],[47,35,13,30,23],[1]),([44,9,0,1,2,4,5],[35,133,30,181,13,17,24,23],[2]),([45,8,1,2,3,4,5],[57,130,42,30,24,149],[]),([0,1,12,36,29,2,3,4,5],[122,2,44,152,130,273,11,165],[1]),([14,12,2,13,3,4,5],[14,347,2,48,348,300],[1]),([44,0,1,29,2,3,4,5],[135,139,23,2,144,120,13,152,30,122,138,111,14,121,292,349],[1]),([80,0,1,2,3,4,5],[47,18,35,107,122,43,110,133,134,120,145,40,23],[]),([14,46,0,141,1,2,3,4,5],[47,43,122,18,107,35,2,135],[]),([14,9,1,2,31,3,4,5],[44,35,2,13,42,30,15,24,23],[1]),([80,28,1,2,3,4,5],[133,35,47,145,40,23],[1]),([48,14,0,1,36,2,3,4,5],[107,30,13],[1]),([10,0,142,35,2,3,4,5],[47,145,158,130,11,148,14,135,128,40,140],[1]),([79,28,0,1,2,3,4,5],[107,215,35,47,30,17,328,23],[]),([14,0,1,36,2,3,4,5],[135,2,47,122,44,30,350,139,130,142,14],[]),([48,14,9,1,2,3,4,5],[13,35,11,30,24,23],[]),([0,76,1,2,3,4,5],[122,18,35,47,11,239,17,161,2,110,42],[]),([8,14,1,29,2,3,4,5],[14,253,130,42,30,145,121,15,351,2],[]),([71,14,0,1,2,3,4,5],[181,122,47,135,11,35,17,23,2],[]),([11,14,12,2,3,5],[30,17,15,14,258],[1]),([37,0,1,33,3,4,5],[122,35,43,135,148,157,23,18],[]),([0,35,33,2,3,4,5],[148,145,352,42,43,137,158],[]),([48,14,12,2,3,4,5],[2,13,47,11,24,23,30,14],[1]),([9,0,1,38,2,4,5],[35,43,353,11,233,148,17,354,23],[]),([123,14,0,1,2,3,4,5],[47,152,130,13,35,23,2,179,15,355,14,121,122],[1]),([48,9,1,2,3,4,5],[35,11,42,18,130,13,30,356,23],[]),([71,14,9,1,2,3,4,5],[181,35,11,145,30,17,23,42],[]),([104,0,1,40,2,3,4],[57,43,128,120,130,48],[]),([48,43,0,1,2,3,4,5],[152,13,47,130,30,24,23,2,122],[1]),([14,1,143,2,3,4,5],[18,35,30,15,145,14],[]),([14,9,1,2,3,4,5],[35,181,18,42,130,43,30,15,23],[]),([123,10,0,1,2,3,4,5],[43,152,130,14,47,143,15,357,187,42,121,325],[1]),([44,28,0,1,2,4,5],[133,30,35,24,23],[1,2]),([10,71,0,1,2,3,4,5],[181,43,122,35,11,2,17,23,47],[1]),([10,0,144,35,2,3,4,5],[47,145,42,144,11,148,135,40],[1]),([50,48,0,1,3,4,5],[47,13,30,23],[1]),([8,48,1,2,3,4,5],[2,13,42,130,6,14,24],[]),([11,34,0,1,12,2,3,5],[6,17,315,111,280,137,30,138,158,306,316,121,14,130],[1]),([34,14,9,1,2,3,4,5],[35,158,23,30,145,14,15,358,302,2,135],[]),([119,8,0,1,2,3,4,5],[18,122,148,42,2,139,359,130,47,135,319,128,30],[]),([11,48,0,1,2,3,5],[110,42,41,148,24,30,158,15,137],[]),([14,12,29,2,3,4,5],[253,47,23,13,45,2,14,360,300,46],[1]),([0,1,33,29,3,4,5],[23,135,361,161,42,48,245,362],[1]),([43,0,1,2,31,3,4,5],[47,35,107,338,161,44,30,24,120,23],[1]),([52,9,1,2,3,4,5],[35,181,30,42,130,23],[]),([52,0,1,2,3,135,5],[47,35,122,42,133,363,111,23],[]),([108,11,10,0,1,2,3,5],[157,110,174,40,148,15,282,48,140,42,111,295,17],[1]),([14,0,1,2,145,3,4,5],[135,2,23,13,120,152,144,299,14,15,24],[1]),([0,1,40,2,146,3,4],[2,120,135,130,15,48],[]),([50,14,12,2,3,4,5],[47,2,11,30,6,23],[1]),([14,137,0,1,2,3,4,5],[47,30,42,107,13,15,24,14],[1]),([14,9,27,2,3,4,5],[35,11,17,23],[]),([14,0,1,36,29,3,4,5],[14,121,44,122,152,364,130,139,299,292],[1]),([48,14,0,1,29,2,3,4,5],[107,23,179,13,161],[1]),([11,52,0,1,2,3,5],[110,42,41,148,30,363,14],[]),([6,0,1,33,2,3,4,5],[35,43,226,135,122,42,148,365,2,23,120,161],[1]),([48,9,0,1,2,3,4,5],[43,122,35,11,42,2,24,139,130,23],[]),([28,0,1,2,31,3,4,5],[47,35,107,215,42,30,24,23],[1]),([14,0,1,2,145,3,4],[135,2,299,120,23,152,13,130,138,24,179,14,292],[1,2]),([25,0,76,1,2,3,4,5],[47,11,107,234,17,144],[]),([83,14,0,1,36,2,3,4,5],[130,161,23,11,14,44,179,292],[1]),([122,0,1,2,3,4,5],[47,18,35,43,181,148,110,133,134,120,122,2,135,23],[]),([0,1,12,29,2,13,3,4],[14,121,184,211,120,152,42,139,277,244,111,2,165,366],[1]),([14,0,1,2,3,135,5],[47,35,367,122,42,30,110,363,111,23,24],[1]),([83,14,0,1,2,3,4,5],[120,47,161,13,35,11,2,30,14,15,368,179,121,44],[1]),([8,52,1,2,3,4,5],[148,2,42,130,30,14],[])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_47_8_1 : checkNodesBT W_47 G_47 fmask_47 P_47 autos_47 bk_47_7 8 nd_47_8_1 = true := by decide +kernel
def nodes_47_8 : List NodeSpec := nd_47_8_0 ++ nd_47_8_1
set_option maxRecDepth 500000 in
lemma chk_47_8 : checkNodesBT W_47 G_47 fmask_47 P_47 autos_47 bk_47_7 8 nodes_47_8 = true := by
  unfold nodes_47_8 checkNodesBT; simp only [List.all_append, Bool.and_eq_true]
  exact ⟨chk_47_8_0, chk_47_8_1⟩
def bk_47_8 : BT (List (List Nat)) := buildBucketsBT W_47 nodes_47_8
set_option maxRecDepth 500000 in
lemma bk_47_8_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_47 8 xs.toFinset) bk_47_8 :=
  buildBucketsBT_sound (by decide) gp_47 W_47_ok P_47_ok autos_47_ok bk_47_7_ok chk_47_8
def nodes_47_9 : List NodeSpec := [([15,11,0,1,2,3,5],[110,15,137,138,244,139,130],[1,2,5,4,0,3]),([11,7,0,1,2,3,5],[110,15,41,111,17,137,138,139],[1,4,0,3]),([6,0,1,2,13,3,4],[134,120,181,148,347,139,244,369],[1,4,0,3]),([16,0,1,2,3,4,5],[134,139,130,43,107,133,110,148,57,149,370],[2,5,1,0,3]),([6,0,1,17,2,3,4,5],[120,57,130,226,251,15,111,134,48,149],[2,1]),([18,8,0,1,2,3,4,5],[18,43,130,13,2,24,135,139],[1,4]),([0,19,1,2,3,4,5],[134,18,120,43,107,139,110,133,15],[1,4,0,3]),([20,0,1,2,3,4,5],[18,47,107,13,181,133,110,120,134,371,15,144],[0,1,2]),([18,9,0,1,2,3,4,5],[43,35,130,11,18,139,231,372,144,23,145,121,135,13],[1,4,5]),([9,0,21,1,2,3,4,5],[139,120,35,130,11,47,23,43,233,30,318,330,137,111,373,231],[1,4,5]),([7,9,1,2,3,4,5],[18,139,23,11,15],[1,4,0,3]),([22,11,0,1,2,3,5],[110,41,137,138,15,139,130,148,111],[1,4,0,3]),([23,0,1,2,3,4,5],[181,18,130,43,107,133,110,15],[2,5,0,3]),([8,6,1,2,3,4,5],[18,139,130,15],[1,4,0,3]),([24,0,1,2,3,4,5],[120,139,43,107,110,133,35,374,375],[1,4,0,3]),([25,9,0,1,2,3,4,5],[43,11,181,18,35,231,17,139,130,47,233,144,30,376,23],[1,2,4]),([25,0,1,2,3,4,5],[181,47,18,11,107,133,110,17,120,134,144,233,376,377],[2,0,1,4]),([26,9,0,1,2,3,4,5],[35,11,231,148,378,139,130,43,233,135,23,379],[1,5]),([6,0,21,1,2,3,4],[134,120,18,43,130,380,330,226],[4,1,0]),([9,0,1,27,2,3,4,5],[11,233,135,137,17,128,181,18,381,231,130,139,23],[1,2,4]),([8,0,21,1,2,3,4,5],[139,18,120,130,148,47,57,43,13,330,318,111,137,30,2,382],[1,4]),([28,9,0,1,2,3,4,5],[43,35,11,231,148,383,139,130,233,47,23,30,384],[1,2,5]),([10,0,1,2,13,3,4,5],[14,347,243,158,43,139,120,111,41,121,128,385,135,48,386,387],[1]),([11,10,0,1,2,3,5],[110,137,41,148,15,40,14,138,388,139,130],[1]),([10,0,1,29,2,3,4,5],[245,152,120,107,122,139,111,138,253,35,23,387,143,145,14,140,15,389,135],[1]),([30,10,0,1,2,3,4,5],[43,107,2,135,18,35,388,157,23,139,130,148],[1]),([14,0,1,2,31,3,4,5],[135,2,47,299,13,44,138,24,152,30,390,14],[1,5,2]),([32,14,0,1,2,3,4,5],[134,23,18,43,13,120,390,144,14,24],[1]),([10,6,0,1,2,3,4,5],[43,120,35,134,18,251,139,148,15,226,135,23],[1]),([10,9,0,1,2,3,4,5],[43,35,181,18,231,148,15,139,130,233,135,23],[1]),([0,1,33,2,3,4,5],[43,122,18,135,42,391,137,161,181,120,134,158],[1,5]),([14,0,1,2,3,4,5],[43,18,47,107,13,181,133,110,120,134,30,15,23,14],[1,5,2]),([0,1,12,2,13,3,4,5],[14,121,11,347,128,385,158,243,120,139,392,41,111,165,2,393,48,394],[1]),([11,0,1,12,2,3,5],[15,137,110,41,17,316,138,392,130,139],[1]),([34,0,1,12,2,3,4,5],[2,43,135,107,11,6,395,139,120],[1]),([32,0,1,2,3,4,5],[43,120,134,18,107,181,130,110,133,23,13,390,144,24,396],[1]),([0,1,12,29,2,3,4,5],[253,245,120,152,122,139,138,111,57,165,11,277,164,15,397,2,395],[1]),([10,0,35,2,3,4,5],[43,181,130,148,18,145,398,137,14,388],[2,1]),([0,1,12,36,2,3,4,5],[142,259,122,44,107,392,41,399,130,139,2,57,273],[1]),([37,10,0,1,2,3,4,5],[43,107,35,135,145,148,15,23],[1,4]),([24,9,0,1,2,3,4,5],[134,139,35,233,231,375,120,130],[1,4,2,5,0,3]),([0,1,38,2,3,4,5],[43,148,181,353,388,107,133,137,120,14,134],[1]),([39,0,1,2,3,4,5],[181,120,134,43,107,18,110,133,23,11,139,17,400],[1,4,0,3]),([0,1,40,2,3,4],[18,43,120,130,15],[1]),([0,1,41,2,3,4,5],[18,43,122,181,2,133,110,120,134,15,158],[1]),([11,14,0,1,2,3,5],[110,30,41,293,148,15,137,14,138,401,130,139],[1]),([0,1,42,2,3,4,5],[43,120,134,23,402,387,130,107,110,133,137],[1]),([43,0,1,2,3,4,5],[120,107,181,130,110,133,47,339,35,403,322,390],[1,2]),([44,0,1,2,3,4,5],[43,13,181,18,107,30,401,133,110,120,134,148,24,404,14],[1,2]),([34,10,0,1,2,3,4,5],[43,107,2,135,18,35,145,157,387,139,23],[1]),([30,14,0,1,2,3,4,5],[107,47,2,42,13,299,35,401,405,23,135,30,130,139,14],[1,5]),([8,14,1,2,3,4,5],[18,43,401,30,13,130,15,14],[1]),([14,9,0,1,2,3,4,5],[401,43,35,18,231,15,139,130,47,299,23,30,13],[1,2]),([11,6,0,1,2,3,5],[110,130,41,111,15,148,406,139,137,138],[1,4,0,3]),([37,14,0,1,2,3,4,5],[107,47,35,43,18,30,148,15,23,299],[1,2]),([45,6,0,1,2,3,4,5],[43,57,120,251,139,130,111,15,144,226,149],[1]),([30,0,1,12,2,3,4,5],[2,43,135,107,392,6,57,130,139],[1]),([14,46,0,1,2,3,4,5],[47,122,35,43,107,18,42,148,15,23,2,13],[1,5,2]),([14,0,1,29,2,3,4,5],[245,253,120,47,23,13,152,179,122,299,139,14,138,111,303,390,144,292],[1,2]),([39,9,0,1,2,3,4,5],[134,139,130,23,11,17],[0,3]),([14,9,1,2,3,4,5],[35,181,43,18,401,407,130,23,233,30],[1]),([14,12,2,3,4,5],[18,258,15,300],[1]),([47,11,0,1,2,3,5],[110,15,137,138,41,139,130,111],[1,4,0,3]),([9,6,0,1,2,3,4,5],[120,139,35,226,251,15,233,231,130],[1,4,0,3]),([43,14,0,1,2,3,4,5],[134,47,35,299,30,322,23,390,120],[1,2]),([44,14,0,1,2,3,4,5],[181,30,43,18,13,401,24,14],[1,2]),([48,0,1,2,3,4,5],[43,122,18,13,181,42,133,110,24,120,134,161,299,408,158],[5,1,3,2]),([14,0,1,36,2,3,4,5],[259,142,47,122,30,13,44,299,107,401,41,409,130,139,14],[1,5]),([10,0,1,36,2,3,4,5],[259,44,122,107,388,410,139,130,142,35,148,135,23,14],[1]),([0,1,49,2,3,4,5],[18,43,107,11,133,15,120,134,263,392],[1]),([14,0,1,2,13,3,4,5],[14,121,243,158,120,139,111,41,299,411,390],[1]),([28,14,0,1,2,3,4,5],[181,47,35,299,30,412,23,401],[1,2]),([14,6,0,1,2,3,4,5],[120,47,35,134,18,251,139,148,15,43,299,144,13,23],[1,2]),([45,0,1,2,3,4,5],[134,47,18,57,120,107,181,130,30,133,110,149,226,413,414],[0,1,2,4,5]),([34,14,0,1,2,3,4,5],[107,47,2,161,13,299,35,30,415,390,135,23,139,14,144],[1,2]),([28,0,1,2,3,4,5],[35,47,107,401,133,110,412,120,134,23,342,416],[1,2]),([50,14,0,1,2,3,4,5],[47,35,13,30,417,23,107,299],[1,2]),([48,14,0,1,2,3,4,5],[107,13,47,30,24,23,122,299,42,161,14],[1,5,2]),([51,0,1,2,3,4,5],[18,47,107,13,181,133,110,120,134,130,15,23],[0,1,2,5]),([0,1,40,2,3,4,5],[18,134,43,120,107,181,130,110,133,15,395],[1]),([52,14,0,1,2,3,4,5],[107,47,35,13,30,363,23,299,122],[1,2,5]),([9,6,1,2,3,4,5],[139,35,18,418,130],[1,4,0,3]),([10,53,2,3,4,5],[43,18,256,15,255],[1]),([52,0,1,2,3,4,5],[35,47,122,181,42,133,110,363,120,134,23,169,419,161,14],[1,2,5])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_47_9 : checkNodesBT W_47 G_47 fmask_47 P_47 autos_47 bk_47_8 9 nodes_47_9 = true := by decide +kernel
def bk_47_9 : BT (List (List Nat)) := buildBucketsBT W_47 nodes_47_9
set_option maxRecDepth 500000 in
lemma bk_47_9_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_47 9 xs.toFinset) bk_47_9 :=
  buildBucketsBT_sound (by decide) gp_47 W_47_ok P_47_ok autos_47_ok bk_47_8_ok chk_47_9
def nodes_47_10 : List NodeSpec := [([6,0,1,2,3,4,5],[134,120,43,107,181,139,130,133,420,18],[1,4,0,3,2,5]),([7,0,1,2,3,4,5],[134,18,43,107,181,15,139],[1,4,0,3,2,5]),([8,0,1,2,3,4,5],[181,18,43,107,15,134,139],[1,4,0,3]),([9,0,1,2,3,4,5],[181,43,107,18,133,15,421,134,139],[1,4,2,5,0,3]),([10,0,1,2,3,4,5],[43,107,181,137,134,18,388,387],[1,4]),([11,0,1,2,3,5],[41,133,139,181],[1,2,5,4,0,3]),([0,1,12,2,3,4,5],[18,43,107,181,133,15,134,392,395],[1]),([0,1,2,13,3,4,5],[120,18,139,41,422,43,107,134],[1,2,4,5,0,3]),([14,0,1,2,3,4,5],[43,18,107,181,401,133,15,423,134,390],[1,2])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_47_10 : checkNodesBT W_47 G_47 fmask_47 P_47 autos_47 bk_47_9 10 nodes_47_10 = true := by decide +kernel
def bk_47_10 : BT (List (List Nat)) := buildBucketsBT W_47 nodes_47_10
set_option maxRecDepth 500000 in
lemma bk_47_10_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_47 10 xs.toFinset) bk_47_10 :=
  buildBucketsBT_sound (by decide) gp_47 W_47_ok P_47_ok autos_47_ok bk_47_9_ok chk_47_10
def nodes_47_11 : List NodeSpec := [([0,1,2,3,4,5],[181,133,134],[1,2,4,5,0,3])]
set_option maxRecDepth 200000 in
set_option maxHeartbeats 0 in
lemma chk_47_11 : checkNodesBT W_47 G_47 fmask_47 P_47 autos_47 bk_47_10 11 nodes_47_11 = true := by decide +kernel
def bk_47_11 : BT (List (List Nat)) := buildBucketsBT W_47 nodes_47_11
set_option maxRecDepth 500000 in
lemma bk_47_11_ok : btAll (fun bk => ∀ xs ∈ bk, Impossible G_47 11 xs.toFinset) bk_47_11 :=
  buildBucketsBT_sound (by decide) gp_47 W_47_ok P_47_ok autos_47_ok bk_47_10_ok chk_47_11
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_47_ok : forestRootCheck R_47 G_47 [(VAR 0,15,14),(VAR 1,15,13),(VAR 2,15,11),(VAR 3,15,7),(VAR 4,25,9),(VAR 5,39,7)] = true := by decide +kernel
set_option maxRecDepth 500000 in
set_option maxHeartbeats 0 in
lemma root_47_in : bucketContainsBT bk_47_11 R_47 = true := by decide +kernel
set_option maxRecDepth 500000 in
lemma low_47 : Lower R_47 G_47 12 := lower_of_forestBT root_47_ok bk_47_11_ok root_47_in
def wit : List PEqualNP.CircuitLowerBounds.Gate := [
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 5]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [0, 1]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [6, 7]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [0, 1]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [4, 9]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [2, 5]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [8, 10]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [8, 10]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [2, 12]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [9, 11]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.or, [3, 15]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [14, 16]⟩,
  ⟨PEqualNP.CircuitLowerBounds.GateOp.and, [13, 17]⟩
]
def wo : Nat := 18
lemma wit_mono : PEqualNP.MetaComplexity.Monotone2 ⟨wit, wo⟩ := by intro g hg; simp only [wit, List.mem_cons, List.not_mem_nil, or_false] at hg; rcases hg with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma wit_eval : ∀ r : Row, PEqualNP.CircuitLowerBounds.Circuit.eval ⟨wit, wo⟩ (List.ofFn (evalInput6 r)) = ((4269860992 * 2 ^ 32 + 4261445632) ||| ((4269860992 * 2 ^ 32 + 4261445632) <<< 64)).testBit r.val := by decide +kernel
lemma root_eq : G_47 = ((4269860992 * 2 ^ 32 + 4261445632) ||| ((4269860992 * 2 ^ 32 + 4261445632) <<< 64)) := by decide
lemma low_root : Lower (varsOf 63) ((4269860992 * 2 ^ 32 + 4261445632) ||| ((4269860992 * 2 ^ 32 + 4261445632) <<< 64)) 12 := root_eq ▸ low_47
lemma positive : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269860992 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269860992 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  intro s hcs
  exact PEqualNP.Outside.L_meta_12087_aux.table2_of_lower (4269860992 * 2 ^ 32 + 4261445632) (by decide) (by decide) (by decide) (by decide) 12 PEqualNP.Outside.L_meta_12087_aux.low_root PEqualNP.Outside.L_meta_12087_aux.wit PEqualNP.Outside.L_meta_12087_aux.wo (by decide) PEqualNP.Outside.L_meta_12087_aux.wit_mono PEqualNP.Outside.L_meta_12087_aux.wit_eval s hcs

end PEqualNP.Outside.L_meta_12087_aux

theorem PEqualNP.Outside.L_meta_12087 : ¬ (¬ (∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (4269860992 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (4269860992 * 2 ^ 32 + 4261445632) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0))) := by
  intro h
  exact h PEqualNP.Outside.L_meta_12087_aux.positive
