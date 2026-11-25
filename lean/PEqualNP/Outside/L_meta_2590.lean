import PEqualNP.Defs
import Mathlib.Data.Multiset.Basic
import Mathlib.Data.Multiset.AddSub
import Mathlib.Data.BitVec

namespace PEqualNP.Outside.L_meta_2590

namespace Dominance

variable {α : Type}

def Dominates (P N : α → Prop) (a b : α → Bool) : Prop :=
  (∀ x, P x → a x ≤ b x) ∧ (∀ x, N x → b x ≤ a x)

def Correct (P N : α → Prop) (a : α → Bool) : Prop :=
  (∀ x, P x → a x = true) ∧ (∀ x, N x → a x = false)

def meet (a b : α → Bool) : α → Bool := fun x => a x && b x

def join (a b : α → Bool) : α → Bool := fun x => a x || b x

def Step (p : List (α → Bool)) (w : α → Bool) : Prop :=
  ∃ a ∈ p, ∃ b ∈ p, w = meet a b ∨ w = join a b

def Trace (p gs : List (α → Bool)) : Prop :=
  List.rec (motive := fun _ => List (α → Bool) → Prop) (fun _ => True)
    (fun w _ rec q => Step q w ∧ rec (q ++ [w])) gs p

def Covers (P N : α → Prop) (p q : List (α → Bool)) : Prop :=
  ∀ a ∈ p, ∃ b ∈ q, Dominates P N a b

lemma dominates_refl (P N : α → Prop) (a : α → Bool) : Dominates P N a a :=
  ⟨fun _ _ => le_rfl, fun _ _ => le_rfl⟩

lemma dominates_meet {P N : α → Prop} {a b c d : α → Bool}
    (ac : Dominates P N a c) (bd : Dominates P N b d) :
    Dominates P N (meet a b) (meet c d) := by
  exact ⟨fun x hx => inf_le_inf (ac.1 x hx) (bd.1 x hx),
    fun x hx => inf_le_inf (ac.2 x hx) (bd.2 x hx)⟩

lemma dominates_join {P N : α → Prop} {a b c d : α → Bool}
    (ac : Dominates P N a c) (bd : Dominates P N b d) :
    Dominates P N (join a b) (join c d) := by
  exact ⟨fun x hx => sup_le_sup (ac.1 x hx) (bd.1 x hx),
    fun x hx => sup_le_sup (ac.2 x hx) (bd.2 x hx)⟩

lemma dominates_correct {P N : α → Prop} {a b : α → Bool}
    (h : Dominates P N a b) (ha : Correct P N a) : Correct P N b := by
  constructor
  · intro x hx
    have hxb := h.1 x hx
    rw [ha.1 x hx] at hxb
    exact le_antisymm (Bool.le_true _) hxb
  · intro x hx
    have hxb := h.2 x hx
    rw [ha.2 x hx] at hxb
    exact le_antisymm hxb (Bool.false_le _)

lemma trace_append_iff {p u v : List (α → Bool)} :
    Trace p (u ++ v) ↔ Trace p u ∧ Trace (p ++ u) v := by
  induction u generalizing p with
  | nil => simp [Trace]
  | cons w u ih =>
    change (Step p w ∧ Trace (p ++ [w]) (u ++ v)) ↔
      (Step p w ∧ Trace (p ++ [w]) u) ∧ Trace (p ++ w :: u) v
    rw [ih]
    simp only [List.append_assoc, List.singleton_append, and_assoc]

lemma replace_trace {P N : α → Prop} {p q gs : List (α → Bool)}
    (h : Trace p gs) (hc : Covers P N p q) :
    ∃ rest, rest.length = gs.length ∧ Trace q rest ∧
      Covers P N (p ++ gs) (q ++ rest) := by
  induction gs generalizing p q with
  | nil => exact ⟨[], rfl, trivial, by simpa using hc⟩
  | cons w gs ih =>
    have one_step : ∃ w', Step q w' ∧ Dominates P N w w' := by
      obtain ⟨a, ha, b, hb, hw⟩ := h.1
      obtain ⟨c, hcm, hac⟩ := hc a ha
      obtain ⟨d, hdm, hbd⟩ := hc b hb
      rcases hw with rfl | rfl
      · exact ⟨meet c d, ⟨c, hcm, d, hdm, Or.inl rfl⟩, dominates_meet hac hbd⟩
      · exact ⟨join c d, ⟨c, hcm, d, hdm, Or.inr rfl⟩, dominates_join hac hbd⟩
    obtain ⟨w', gen, dom⟩ := one_step
    have extra : Covers P N (p ++ [w]) (q ++ [w']) := by
      intro a ha
      rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨b, hb, hab⟩ := hc _ ha
        exact ⟨b, List.mem_append_left _ hb, hab⟩
      · obtain rfl := List.mem_singleton.mp ha
        exact ⟨w', by simp, dom⟩
    obtain ⟨tail, hlen, htrace, hcover⟩ := ih h.2 extra
    exact ⟨w' :: tail, by simp [hlen], ⟨gen, htrace⟩,
      by simpa [List.append_assoc] using hcover⟩

lemma delete_dominated {P N : α → Prop} {p u gs : List (α → Bool)} {w : α → Bool}
    (ht : Trace p (u ++ w :: gs))
    (hd : ∃ b ∈ p ++ u, Dominates P N w b) :
    ∃ rest, rest.length + 1 = (u ++ w :: gs).length ∧ Trace p rest ∧
      Covers P N (p ++ (u ++ w :: gs)) (p ++ rest) := by
  obtain ⟨b, hb, hwb⟩ := hd
  rw [trace_append_iff] at ht
  have hc : Covers P N ((p ++ u) ++ [w]) (p ++ u) := by
    intro a ha
    rcases List.mem_append.mp ha with ha | ha
    · exact ⟨a, ha, dominates_refl _ _ _⟩
    · obtain rfl := List.mem_singleton.mp ha
      exact ⟨b, hb, hwb⟩
  obtain ⟨tail, hlen, htrace, hcover⟩ := replace_trace ht.2.2 hc
  refine ⟨u ++ tail, ?_, ?_, ?_⟩
  · simp [hlen, Nat.add_assoc]
  · exact trace_append_iff.mpr ⟨ht.1, htrace⟩
  · simpa [List.append_assoc] using hcover

lemma minimal_no_dominated {P N : α → Prop} {p u gs : List (α → Bool)} {w : α → Bool}
    (ht : Trace p (u ++ w :: gs))
    (hout : ∃ f ∈ p ++ (u ++ w :: gs), Correct P N f)
    (hmin : ∀ rest, Trace p rest → (∃ f ∈ p ++ rest, Correct P N f) →
      (u ++ w :: gs).length ≤ rest.length) :
    ¬ ∃ b ∈ p ++ u, Dominates P N w b := by
  intro hd
  obtain ⟨rest, hlen, htrace, hcover⟩ := delete_dominated ht hd
  obtain ⟨f, hf, hfc⟩ := hout
  obtain ⟨f', hf', hff'⟩ := hcover f hf
  have hbound := hmin rest htrace ⟨f', hf', dominates_correct hff' hfc⟩
  omega

lemma trace_indexed {p gs : List (α → Bool)} (h : Trace p gs) (j : Fin gs.length) :
    Step (p ++ gs.take j) (gs.get j) := by
  induction gs generalizing p with
  | nil => exact Fin.elim0 j
  | cons w gs ih =>
    refine Fin.cases ?_ (fun j => ?_) j
    · simpa using h.1
    · simpa [List.append_assoc] using ih h.2 j

lemma split_at {β : Type} (gs : List β) (j : Fin gs.length) :
    gs = gs.take j ++ gs.get j :: gs.drop (j.val + 1) := by
  conv_lhs => rw [← List.take_append_drop j.val gs]
  congr 1
  exact List.drop_eq_getElem_cons j.isLt

lemma smallest_trace {P N : α → Prop} {p gs : List (α → Bool)}
    (htrace : Trace p gs) (hout : ∃ f ∈ p ++ gs, Correct P N f) :
    ∃ rest, rest.length ≤ gs.length ∧ Trace p rest ∧
      (∃ f ∈ p ++ rest, Correct P N f) ∧
      ∀ j : Fin rest.length, ¬ ∃ b ∈ p ++ rest.take j.val,
        Dominates P N (rest.get j) b := by
  classical
  let Solves (t : List (α → Bool)) : Prop :=
    Trace p t ∧ ∃ f ∈ p ++ t, Correct P N f
  let S : ℕ → Prop := fun n => ∃ t, t.length = n ∧ Solves t
  have hn : ∃ n, S n := ⟨gs.length, gs, rfl, htrace, hout⟩
  obtain ⟨rest, len, solves⟩ := Nat.find_spec hn
  have hmin : ∀ t, Solves t → rest.length ≤ t.length := by
    intro t ht
    exact len.trans_le (Nat.find_min' hn ⟨t, rfl, ht⟩)
  refine ⟨rest, hmin gs ⟨htrace, hout⟩, solves.1, solves.2, ?_⟩
  intro j
  have hs := split_at rest j
  apply minimal_no_dominated (u := rest.take j.val) (w := rest.get j)
    (gs := rest.drop (j.val + 1))
  · simpa only [← hs] using solves.1
  · simpa only [← hs] using solves.2
  · intro t ht ho
    simpa only [← hs] using hmin t ⟨ht, ho⟩

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def pin {n : ℕ} (i : Fin n) : (Fin n → Bool) → Bool := fun x => x i

def pins (n : ℕ) : List ((Fin n → Bool) → Bool) := List.ofFn pin

def zero {β : Type} : β → Bool := fun _ => false

def one {β : Type} : β → Bool := fun _ => true

def base (n : ℕ) : List ((Fin n → Bool) → Bool) := zero :: one :: pins n

def symbolicGate (ws : List (α → Bool)) (g : Gate) : α → Bool :=
  fun x => g.op.eval (g.inputs.map fun i => (ws.getD i zero) x)

def symbolic (ws : List (α → Bool)) (gs : List Gate) : List (α → Bool) :=
  List.rec (motive := fun _ => List (α → Bool) → List (α → Bool)) (fun _ => [])
    (fun g _ rec p => symbolicGate p g :: rec (p ++ [symbolicGate p g])) gs ws

lemma getD_mem (ws : List (α → Bool)) (i : ℕ) : ws.getD i zero ∈ zero :: one :: ws := by
  by_cases h : i < ws.length
  · rw [List.getD_eq_getElem _ _ h]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.getElem_mem h))
  · rw [List.getD_eq_default _ _ (by omega)]
    simp

lemma and_eval (xs : List Bool) : GateOp.eval .and xs = xs.all id := rfl
lemma or_eval (xs : List Bool) : GateOp.eval .or xs = xs.any id := rfl

lemma symbolicGate_step (ws : List (α → Bool)) (g : Gate)
    (mono : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    Step (zero :: one :: ws) (symbolicGate ws g) := by
  obtain ⟨op, len⟩ := mono
  change g.op = .and ∨ g.op = .or at op
  have had (b : α → Bool) (hb : b ∈ zero :: one :: ws) (h : symbolicGate ws g = b) :
      Step (zero :: one :: ws) (symbolicGate ws g) := by
    refine ⟨b, hb, b, hb, Or.inl ?_⟩
    rw [h]
    funext x
    simp [meet]
  cases hs : g.inputs with
  | nil =>
      rcases op with op | op
      · exact had one (by simp) (by funext x; simp [symbolicGate, hs, op, and_eval, one])
      · exact had zero (by simp) (by funext x; simp [symbolicGate, hs, op, or_eval, zero])
  | cons i is =>
      cases is with
      | nil =>
          apply had _ (getD_mem ws i)
          funext x
          rcases op with op | op
          · simp [symbolicGate, hs, op, and_eval]
          · simp [symbolicGate, hs, op, or_eval]
      | cons j js =>
          have eq : js = [] := by
            apply List.length_eq_zero_iff.mp
            simp only [hs, List.length_cons] at len
            omega
          subst js
          refine ⟨_, getD_mem ws i, _, getD_mem ws j, ?_⟩
          rcases op with op | op
          · left; funext x; simp [symbolicGate, hs, op, and_eval, meet]
          · right; funext x; simp [symbolicGate, hs, op, or_eval, join]

lemma symbolic_trace (ws : List (α → Bool)) (gs : List Gate)
    (mono : Monotone2 ⟨gs, 0⟩) : Trace (zero :: one :: ws) (symbolic ws gs) := by
  induction gs generalizing ws with
  | nil => trivial
  | cons g gs ih =>
      exact ⟨symbolicGate_step ws g (mono g List.mem_cons_self),
        ih (ws ++ _) (fun a ha => mono a (List.mem_cons_of_mem _ ha))⟩

lemma symbolic_length (ws : List (α → Bool)) (gs : List Gate) :
    (symbolic ws gs).length = gs.length := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    change (symbolic (ws ++ [symbolicGate ws g]) gs).length + 1 = gs.length + 1
    rw [ih]

lemma wires_unfold (C : Circuit) (x : List Bool) :
    C.wires x = C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x := rfl

lemma eval_unfold (C : Circuit) (x : List Bool) :
    C.eval x = (C.wires x).getD C.output false := rfl

lemma eval_symbolic (ws : List (α → Bool)) (gs : List Gate) (x : α) :
    (((⟨gs, 0⟩ : Circuit).wires (ws.map fun a => a x)))
    = (ws ++ symbolic ws gs).map (fun a => a x) := by
  induction gs generalizing ws with
  | nil => simp [wires_unfold, symbolic]
  | cons g gs ih =>
    rw [wires_unfold]
    simp only [List.foldl_cons]
    have he : g.op.eval (g.inputs.map fun i => (ws.map fun a => a x).getD i false)
        = symbolicGate ws g x := by
      unfold symbolicGate
      congr 1
      apply List.map_congr_left
      intro i _
      exact List.getD_map ws zero (fun a => a x)
    rw [he]
    change (⟨gs, 0⟩ : Circuit).wires ((ws.map fun a => a x) ++ [symbolicGate ws g x]) = _
    have eq : (ws.map fun a => a x) ++ [symbolicGate ws g x]
        = (ws ++ [symbolicGate ws g]).map (fun a => a x) := by simp
    rw [eq, ih]
    simp [List.append_assoc, symbolic]

lemma eval_pins {n : ℕ} (x : Fin n → Bool) :
    (pins n).map (fun a => a x) = List.ofFn x := by
  simp only [pins, List.map_ofFn]
  rfl

lemma circuit_trace {n : ℕ} (C : Circuit) (hC : Monotone2 C)
    (f : (Fin n → Bool) → Bool) (hf : ∀ x, C.eval (List.ofFn x) = f x) :
    ∃ gs, gs.length = C.size ∧ Trace (base n) gs ∧ f ∈ base n ++ gs := by
  let gs := symbolic (pins n) C.gates
  refine ⟨gs, symbolic_length _ _, symbolic_trace _ _ hC, ?_⟩
  have eq : f = (pins n ++ gs).getD C.output zero := by
    funext x
    rw [← hf x, eval_unfold, ← eval_pins x]
    change ((⟨C.gates, 0⟩ : Circuit).wires ((pins n).map fun a => a x)).getD C.output false = _
    rw [eval_symbolic]
    exact List.getD_map _ zero (fun a => a x)
  rw [eq]
  exact getD_mem (pins n ++ gs) _

lemma circuit_nondominated_trace {n : ℕ} (P N : (Fin n → Bool) → Prop)
    (C : Circuit) (hC : Monotone2 C)
    (hc : Correct P N (fun x => C.eval (List.ofFn x))) :
    ∃ gs, gs.length ≤ C.size ∧ Trace (base n) gs ∧
      (∃ f ∈ base n ++ gs, Correct P N f) ∧
      ∀ j : Fin gs.length, ¬ ∃ b ∈ base n ++ gs.take j.val,
        Dominates P N (gs.get j) b := by
  obtain ⟨gs, hlen, htrace, hout⟩ := circuit_trace C hC (fun x => C.eval (List.ofFn x)) (fun _ => rfl)
  obtain ⟨rest, hrest, htrace', hout', hdom⟩ := smallest_trace htrace ⟨_, hout, hc⟩
  exact ⟨rest, hlen ▸ hrest, htrace', hout', hdom⟩

lemma step_without_constants {p : List (α → Bool)} {w : α → Bool}
    (h : Step (zero :: one :: p) w) (fresh : w ∉ zero :: one :: p) : Step p w := by
  obtain ⟨a, ha, b, hb, hw⟩ := h
  have lz (b : α → Bool) : meet zero b = zero ∧ join zero b = b := by
    constructor <;> funext x <;> simp [meet, join, zero]
  have lo (b : α → Bool) : meet one b = b ∧ join one b = one := by
    constructor <;> funext x <;> simp [meet, join, one]
  have rz (b : α → Bool) : meet b zero = zero ∧ join b zero = b := by
    constructor <;> funext x <;> simp [meet, join, zero]
  have ro (b : α → Bool) : meet b one = b ∧ join b one = one := by
    constructor <;> funext x <;> simp [meet, join, one]
  rcases List.mem_cons.mp ha with rfl | ha
  · rcases hw with hw | hw
    · exact (fresh ((hw.trans (lz b).1).symm ▸ List.mem_cons_self)).elim
    · exact (fresh ((hw.trans (lz b).2).symm ▸ hb)).elim
  rcases List.mem_cons.mp ha with rfl | ha
  · rcases hw with hw | hw
    · exact (fresh ((hw.trans (lo b).1).symm ▸ hb)).elim
    · exact (fresh ((hw.trans (lo b).2).symm ▸ by simp)).elim
  rcases List.mem_cons.mp hb with rfl | hb
  · rcases hw with hw | hw
    · exact (fresh ((hw.trans (rz a).1).symm ▸ List.mem_cons_self)).elim
    · exact (fresh ((hw.trans (rz a).2).symm ▸ by simp [ha])).elim
  rcases List.mem_cons.mp hb with rfl | hb
  · rcases hw with hw | hw
    · exact (fresh ((hw.trans (ro a).1).symm ▸ by simp [ha])).elim
    · exact (fresh ((hw.trans (ro a).2).symm ▸ by simp)).elim
  exact ⟨a, ha, b, hb, hw⟩

lemma trace_of_indexed {p gs : List (α → Bool)}
    (h : ∀ j : Fin gs.length, Step (p ++ gs.take j) (gs.get j)) : Trace p gs := by
  induction gs generalizing p with
  | nil => trivial
  | cons w gs ih =>
    constructor
    · simpa using h ⟨0, by simp⟩
    · apply ih
      intro j
      simpa [List.append_assoc] using h j.succ

lemma circuit_clean_nondominated_trace {n : ℕ} (P N : (Fin n → Bool) → Prop)
    (C : Circuit) (hC : Monotone2 C)
    (hc : Correct P N (fun x => C.eval (List.ofFn x))) :
    ∃ gs, gs.length ≤ C.size ∧ Trace (pins n) gs ∧
      (∃ f ∈ base n ++ gs, Correct P N f) ∧
      ∀ j : Fin gs.length, ¬ ∃ b ∈ base n ++ gs.take j.val,
        Dominates P N (gs.get j) b := by
  obtain ⟨gs, hlen, htrace, hout, hdom⟩ := circuit_nondominated_trace P N C hC hc
  refine ⟨gs, hlen, trace_of_indexed ?_, hout, hdom⟩
  intro j
  apply step_without_constants
  · simpa [base] using trace_indexed htrace j
  · intro hmem
    apply hdom j
    exact ⟨gs.get j, by simpa [base] using hmem, dominates_refl _ _ _⟩

lemma join_essential_pos {P N : α → Prop} {a b : α → Bool}
    (h : ¬ Dominates P N (join a b) a) :
    ∃ x, P x ∧ a x = false ∧ b x = true := by
  classical
  by_contra hn
  apply h
  constructor
  · intro x hx
    cases ha : a x <;> cases hb : b x <;> simp [join, ha, hb]
    exact (hn ⟨x, hx, ha, hb⟩).elim
  · intro x _
    exact le_sup_left

lemma meet_essential_neg {P N : α → Prop} {a b : α → Bool}
    (h : ¬ Dominates P N (meet a b) a) :
    ∃ x, N x ∧ a x = true ∧ b x = false := by
  classical
  by_contra hn
  apply h
  constructor
  · intro x _
    exact inf_le_left
  · intro x hx
    cases ha : a x <;> cases hb : b x <;> simp [meet, ha, hb]
    exact (hn ⟨x, hx, ha, hb⟩).elim

def rowPins {n : ℕ} (x : α → Fin n → Bool) : List (α → Bool) :=
  List.ofFn fun i r => x r i

def rowBase {n : ℕ} (x : α → Fin n → Bool) : List (α → Bool) :=
  zero :: one :: rowPins x

lemma eval_rowPins {n : ℕ} (x : α → Fin n → Bool) (r : α) :
    (rowPins x).map (fun a => a r) = List.ofFn (x r) := by
  simp only [rowPins, List.map_ofFn]
  rfl

lemma circuit_row_trace {n : ℕ} (x : α → Fin n → Bool)
    (C : Circuit) (hC : Monotone2 C)
    (f : α → Bool) (hf : ∀ r, C.eval (List.ofFn (x r)) = f r) :
    ∃ gs, gs.length = C.size ∧ Trace (rowBase x) gs ∧ f ∈ rowBase x ++ gs := by
  let gs := symbolic (rowPins x) C.gates
  refine ⟨gs, symbolic_length _ _, symbolic_trace _ _ hC, ?_⟩
  have eq : f = (rowPins x ++ gs).getD C.output zero := by
    funext r
    rw [← hf r, eval_unfold, ← eval_rowPins x r]
    change ((⟨C.gates, 0⟩ : Circuit).wires ((rowPins x).map fun a => a r)).getD C.output false = _
    rw [eval_symbolic]
    exact List.getD_map _ zero (fun a => a r)
  rw [eq]
  exact getD_mem (rowPins x ++ gs) _

lemma circuit_row_clean_nondominated_trace {n : ℕ} (x : α → Fin n → Bool)
    (P N : α → Prop) (C : Circuit) (hC : Monotone2 C)
    (hc : Correct P N (fun r => C.eval (List.ofFn (x r)))) :
    ∃ gs, gs.length ≤ C.size ∧ Trace (rowPins x) gs ∧
      (∃ f ∈ rowBase x ++ gs, Correct P N f) ∧
      ∀ j : Fin gs.length, ¬ ∃ b ∈ rowBase x ++ gs.take j.val,
        Dominates P N (gs.get j) b := by
  obtain ⟨gs, hlen, htrace, hout⟩ :=
    circuit_row_trace x C hC (fun r => C.eval (List.ofFn (x r))) (fun _ => rfl)
  obtain ⟨rest, hrest, htrace', hout', hdom⟩ := smallest_trace htrace ⟨_, hout, hc⟩
  refine ⟨rest, hlen ▸ hrest, trace_of_indexed ?_, hout', hdom⟩
  intro j
  apply step_without_constants
  · simpa [rowBase] using trace_indexed htrace' j
  · intro hmem
    apply hdom j
    exact ⟨rest.get j, by simpa [rowBase] using hmem, dominates_refl _ _ _⟩

lemma correct_dominates_all {P N : α → Prop} {b : α → Bool}
    (hb : Correct P N b) (a : α → Bool) : Dominates P N a b := by
  constructor
  · intro x hx
    rw [hb.1 x hx]
    exact Bool.le_true _
  · intro x hx
    rw [hb.2 x hx]
    exact Bool.false_le _

lemma no_correct_prior {P N : α → Prop} {p gs : List (α → Bool)}
    (hdom : ∀ j : Fin gs.length, ¬ ∃ b ∈ p ++ gs.take j.val,
      Dominates P N (gs.get j) b) (j : Fin gs.length) :
    ¬ ∃ f ∈ p ++ gs.take j.val, Correct P N f := by
  rintro ⟨f, hf, hc⟩
  exact hdom j ⟨f, hf, correct_dominates_all hc _⟩

end Dominance

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def LeL (a b : List Bool) : Prop := ∀ i, a.getD i false = true → b.getD i false = true

lemma eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

lemma fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length → LeL a b →
      LeL (gs.foldl step a) (gs.foldl step b) := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · intro i hi
      unfold step at hi ⊢
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [← hl]
        by_cases he : i - a.length = 0
        · rw [he] at hi ⊢
          simp only [List.getD_cons_zero] at hi ⊢
          exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi; simp at hi
lemma circuit_mono (C : Circuit) (hC : Monotone2 C) :
    Monotone (fun x : Fin 10 → Bool => C.eval (List.ofFn x)) := by
  intro a b hab
  have hm := fold_mono C.gates (fun g hg => by
    have h := (hC g hg).1
    simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using h)
    (List.ofFn a) (List.ofFn b) (by simp)
    (by
      intro i hi
      by_cases hil : i < 10
      · rw [List.getD_eq_getElem _ _ (by simpa using hil), List.getElem_ofFn] at hi ⊢
        exact (hab ⟨i, hil⟩) hi
      · rw [List.getD_eq_default _ _ (by simpa using Nat.le_of_not_lt hil)] at hi
        contradiction)
  exact hm C.output

def row (r : Nat) (i : Fin 10) : Bool := r.testBit i

def edgeFn (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def posRows : List Nat := [3, 6, 12, 24, 17, 33, 66, 132, 264, 528, 160, 640, 576, 320, 288]

def negRows : List Nat := [50, 69, 104, 116, 138, 201, 208, 276, 385, 402, 521, 548, 554, 770, 773]

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma boundary_cover : ∀ x : Fin 10 → Bool,
    (edgeFn x = true → ∃ r ∈ posRows, row r ≤ x) ∧
    (edgeFn x = false → ∃ r ∈ negRows, x ≤ row r) := by
  decide

set_option maxRecDepth 100000 in
lemma boundary_values :
    (∀ r ∈ posRows, edgeFn (row r) = true) ∧
    (∀ r ∈ negRows, edgeFn (row r) = false) := by
  decide

lemma boundary_complete (f : (Fin 10 → Bool) → Bool) (hf : Monotone f)
    (hp : ∀ r ∈ posRows, f (row r) = true)
    (hn : ∀ r ∈ negRows, f (row r) = false) : ∀ x, f x = edgeFn x := by
  intro x
  have hc := boundary_cover x
  cases he : edgeFn x with
  | false =>
    obtain ⟨r, hr, hxr⟩ := hc.2 he
    have h := hf hxr
    rw [hn r hr] at h
    exact le_antisymm h (Bool.false_le _)
  | true =>
    obtain ⟨r, hr, hrx⟩ := hc.1 he
    have h := hf hrx
    rw [hp r hr] at h
    exact le_antisymm (Bool.le_true _) h

lemma boundary_iff (C : Circuit) (hC : Monotone2 C) :
    (∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edgeFn x) ↔
      (∀ r ∈ posRows, C.eval (List.ofFn (row r)) = true) ∧
      (∀ r ∈ negRows, C.eval (List.ofFn (row r)) = false) := by
  constructor
  · intro h
    exact ⟨fun r hr => (h (row r)).trans (boundary_values.1 r hr),
      fun r hr => (h (row r)).trans (boundary_values.2 r hr)⟩
  · rintro ⟨hp, hn⟩
    exact boundary_complete _ (circuit_mono C hC) hp hn

def boundaryInput (r : Fin 30) : Fin 10 → Bool :=
  row ((posRows ++ negRows).getD r.val 0)

lemma boundaryInput_value : ∀ r : Fin 30,
    edgeFn (boundaryInput r) = decide (r.val < 15) := by
  decide

lemma circuit_boundary_trace (C : Circuit) (hC : Monotone2 C)
    (hf : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edgeFn x) :
    ∃ gs : List (Fin 30 → Bool), gs.length ≤ C.size ∧
      Dominance.Trace (Dominance.rowPins boundaryInput) gs ∧
      (∃ f ∈ Dominance.rowBase boundaryInput ++ gs,
        Dominance.Correct (fun r => r.val < 15) (fun r => 15 ≤ r.val) f) ∧
      ∀ j : Fin gs.length, ¬ ∃ b ∈ Dominance.rowBase boundaryInput ++ gs.take j.val,
        Dominance.Dominates (fun r => r.val < 15) (fun r => 15 ≤ r.val) (gs.get j) b := by
  apply Dominance.circuit_row_clean_nondominated_trace boundaryInput _ _ C hC
  constructor
  · intro r hr
    change C.eval (List.ofFn (boundaryInput r)) = true
    rw [hf, boundaryInput_value]
    exact decide_eq_true hr
  · intro r hr
    change C.eval (List.ofFn (boundaryInput r)) = false
    rw [hf, boundaryInput_value]
    exact decide_eq_false (by omega)


namespace CausalBarrier

abbrev Wire := Finset (Fin 10) × Bool

def Safe (T : Finset (Fin 10)) (w : Wire) : Prop :=
  w.2 = true → (w.1 ∩ T).Nonempty

def Join (a b : Wire) : Wire := (a.1 ∪ b.1, a.2 || b.2)

def Meet (a b : Wire) : Wire := (a.1 ∩ b.1, a.2 && b.2)

def Separates (T A B : Finset (Fin 10)) : Prop :=
  ¬ ((A ∩ T).Nonempty ∧ (B ∩ T).Nonempty)

lemma safe_join {T : Finset (Fin 10)} {a b : Wire}
    (ha : Safe T a) (hb : Safe T b) : Safe T (Join a b) := by
  intro h
  change a.2 || b.2 = true at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · rcases ha h with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    simpa only [Join, Finset.mem_inter, Finset.mem_union] using
      And.intro (Or.inl (Finset.mem_inter.mp hv).1) (Finset.mem_inter.mp hv).2
  · rcases hb h with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    simpa only [Join, Finset.mem_inter, Finset.mem_union] using
      And.intro (Or.inr (Finset.mem_inter.mp hv).1) (Finset.mem_inter.mp hv).2

lemma safe_meet {T : Finset (Fin 10)} {a b : Wire}
    (ha : Safe T a) (hb : Safe T b) (hs : Separates T a.1 b.1) :
    Safe T (Meet a b) := by
  intro h
  change a.2 && b.2 = true at h
  rcases Bool.and_eq_true_iff.mp h with ⟨ha', hb'⟩
  exact False.elim (hs ⟨ha ha', hb hb'⟩)

def Step (T : Finset (Fin 10)) (pool : List Wire) (w : Wire) : Prop :=
  ∃ a ∈ pool, ∃ b ∈ pool,
    w = Join a b ∨ (Separates T a.1 b.1 ∧ w = Meet a b)

def Trace (T : Finset (Fin 10)) (pool : List Wire) : List Wire → Prop
  | [] => True
  | w :: ws => Step T pool w ∧ Trace T (w :: pool) ws

lemma safe_step {T : Finset (Fin 10)} {pool : List Wire} {w : Wire}
    (hp : ∀ a ∈ pool, Safe T a) (h : Step T pool w) : Safe T w := by
  rcases h with ⟨a, ha, b, hb, h | ⟨hs, h⟩⟩
  · subst w
    exact safe_join (hp a ha) (hp b hb)
  · subst w
    exact safe_meet (hp a ha) (hp b hb) hs

lemma safe_trace {T : Finset (Fin 10)} {pool ws : List Wire}
    (hp : ∀ a ∈ pool, Safe T a) (h : Trace T pool ws) :
    ∀ w ∈ ws, Safe T w := by
  induction ws generalizing pool with
  | nil => simp
  | cons a ws ih =>
      obtain ⟨hs, ht⟩ := h
      have ha := safe_step hp hs
      have hp' : ∀ b ∈ a :: pool, Safe T b := by
        intro b hb
        rcases List.mem_cons.mp hb with rfl | hb
        · exact ha
        · exact hp b hb
      intro w hw
      rcases List.mem_cons.mp hw with rfl | hw
      · exact ha
      · exact ih hp' ht w hw

lemma safe_zero_false {T : Finset (Fin 10)} {w : Wire}
    (h : Safe T w) (hz : w.1 = ∅) : w.2 = false := by
  cases hv : w.2
  · rfl
  · have hn := h hv
    simp [hz] at hn

def OtherSides : List (Finset (Fin 10) × Finset (Fin 10)) :=
  [({0}, {1}), ({0}, {4, 5}), ({1}, {2, 6}), ({2}, {3, 7}), ({6}, {8, 9}),
    (∅, ∅)]

def BarrierSets : List (Finset (Fin 10)) :=
  [{0, 3, 8}, {1, 4, 9}, {2, 5, 8}, {6, 3, 4}]

def DirtyEdges : List (Finset (Fin 10)) :=
  [{3, 4}, {4, 9}, {5, 7}, {7, 9}, {3, 8}, {5, 8}]

def OutsideVertices : Finset (Fin 10) := {0, 1, 2, 6}

def ChosenEdge (v : Fin 10) : Finset (Fin 10) :=
  match v.val with
  | 0 => {3, 8}
  | 1 => {4, 9}
  | 2 => {5, 8}
  | _ => {3, 4}

def ChosenBarrier (v : Fin 10) : Finset (Fin 10) := insert v (ChosenEdge v)

lemma finite_separation :
    ∀ T ∈ BarrierSets, ∀ AB ∈ OtherSides,
      Separates T AB.1 AB.2 ∧ Separates T AB.2 AB.1 := by
  simp [BarrierSets, OtherSides, Separates]

lemma dirty_edge_separation :
    ∀ E ∈ DirtyEdges, ∀ AB ∈ OtherSides,
      Separates E AB.1 AB.2 ∧ Separates E AB.2 AB.1 := by
  simp [DirtyEdges, OtherSides, Separates]

lemma chosen_barrier_valid :
    ∀ v : Fin 10, v ∈ OutsideVertices →
      ChosenBarrier v ∈ BarrierSets ∧ ChosenEdge v ∈ DirtyEdges := by
  decide

lemma safe_mono {E T : Finset (Fin 10)} {w : Wire}
    (hET : E ⊆ T) (h : Safe E w) : Safe T w := by
  intro hv
  obtain ⟨v, hv'⟩ := h hv
  obtain ⟨hve, hvE⟩ := Finset.mem_inter.mp hv'
  exact ⟨v, Finset.mem_inter.mpr ⟨hve, hET hvE⟩⟩

lemma carrier_safe {v : Fin 10} {w : Wire} (h : v ∈ w.1) :
    Safe (ChosenBarrier v) w := by
  intro _
  exact ⟨v, Finset.mem_inter.mpr ⟨h, Finset.mem_insert_self _ _⟩⟩

lemma preexisting_safe {v : Fin 10} {w : Wire} (h : Safe (ChosenEdge v) w) :
    Safe (ChosenBarrier v) w :=
  safe_mono (Finset.subset_insert _ _) h

lemma canonical_meet_step {v : Fin 10} {pool : List Wire} {a b : Wire}
    (hv : v ∈ OutsideVertices) (ha : a ∈ pool) (hb : b ∈ pool)
    (hs : (a.1, b.1) ∈ OtherSides ∨ (b.1, a.1) ∈ OtherSides) :
    Step (ChosenBarrier v) pool (Meet a b) := by
  refine ⟨a, ha, b, hb, Or.inr ⟨?_, rfl⟩⟩
  have hT := (chosen_barrier_valid v hv).1
  rcases hs with hs | hs
  · exact (finite_separation _ hT _ hs).1
  · exact (finite_separation _ hT _ hs).2

lemma zero_output_impossible {T : Finset (Fin 10)} {pool ws : List Wire} {w : Wire}
    (hp : ∀ a ∈ pool, Safe T a) (h : Trace T pool ws)
    (hw : w ∈ ws) (hz : w.1 = ∅) : w.2 ≠ true := by
  rw [safe_zero_false (safe_trace hp h w hw) hz]
  decide

lemma carrier_cut_impossible {v : Fin 10} {pool ws : List Wire} {carrier out : Wire}
    (hp : ∀ a ∈ pool, Safe (ChosenEdge v) a)
    (hc : v ∈ carrier.1)
    (ht : Trace (ChosenBarrier v) (carrier :: pool) ws)
    (ho : out ∈ ws) (hz : out.1 = ∅) : out.2 ≠ true := by
  apply zero_output_impossible (T := ChosenBarrier v) (pool := carrier :: pool) ?_ ht ho hz
  intro a ha
  rcases List.mem_cons.mp ha with rfl | ha
  · exact carrier_safe hc
  · exact preexisting_safe (hp a ha)

def SidePair (i : Fin 6) : Finset (Fin 10) × Finset (Fin 10) :=
  match i.val with
  | 0 => ({0}, {1})
  | 1 => ({0}, {4, 5})
  | 2 => ({1}, {2, 6})
  | 3 => ({2}, {3, 7})
  | 4 => ({6}, {8, 9})
  | _ => ({4, 7, 8}, {3, 5, 9})

def Side (i : Fin 6) (b : Bool) : Finset (Fin 10) :=
  if b then (SidePair i).1 else (SidePair i).2

lemma sides_inter_card :
    ∀ (i j : Fin 6) (a b : Bool), i ≠ j →
      (Side i a ∩ Side j b).card ≤ 1 := by
  decide

lemma singleton_of_two_exits {S : Finset (Fin 10)} {i j : Fin 6} {a b : Bool}
    (hne : S.Nonempty) (hij : i ≠ j)
    (hi : S ⊆ Side i a) (hj : S ⊆ Side j b) : ∃ v, S = {v} := by
  apply Finset.card_eq_one.mp
  apply Nat.le_antisymm
  · exact (Finset.card_le_card (Finset.subset_inter hi hj)).trans
      (sides_inter_card i j a b hij)
  · exact Finset.one_le_card.mpr hne

end CausalBarrier

namespace CausalBarrier

def UniversalEdge (v : Fin 10) : Finset (Fin 10) :=
  match v.val with
  | 0 => {3, 8}
  | 1 => {4, 9}
  | 2 => {5, 8}
  | 3 => {3, 4}
  | 4 => {3, 4}
  | 5 => {5, 7}
  | 6 => {3, 4}
  | 7 => {5, 7}
  | 8 => {3, 8}
  | _ => {4, 9}

def UniversalBarrier (v : Fin 10) : Finset (Fin 10) :=
  insert v (UniversalEdge v)

lemma universal_edge_valid :
    ∀ v : Fin 10, UniversalEdge v ∈ DirtyEdges := by
  decide

lemma all_vertices_separation :
    ∀ (v : Fin 10), ∀ AB ∈ OtherSides,
      Separates (UniversalBarrier v) AB.1 AB.2 ∧
      Separates (UniversalBarrier v) AB.2 AB.1 := by
  intro v
  simp [OtherSides, Separates]
  revert v
  decide

end CausalBarrier

namespace ResourceExclusion

open CausalBarrier

abbrev Resource := Finset (Fin 10) × (Finset (Fin 10) → Bool)

def CrossPairs : List (Finset (Fin 10)) :=
  [{3, 4}, {4, 5}, {4, 9}, {3, 7}, {5, 7}, {7, 9}, {3, 8}, {5, 8}, {8, 9}]

def RSafe (E T : Finset (Fin 10)) (w : Resource) : Prop :=
  w.2 E = true → (w.1 ∩ T).Nonempty

def Ordinary (w : Resource) : Prop := ∀ E ∈ CrossPairs, RSafe E E w

def AllOrdinary (p : Multiset Resource) : Prop := ∀ w ∈ p, Ordinary w

def RJoin (a b : Resource) : Resource :=
  (a.1 ∪ b.1, fun E => a.2 E || b.2 E)

def RMeet (a b : Resource) : Resource :=
  (a.1 ∩ b.1, fun E => a.2 E && b.2 E)

def AllowedSides (a b : Resource) : Prop :=
  (a.1, b.1) ∈ OtherSides ∨ (b.1, a.1) ∈ OtherSides

def Keep (w : Resource) : Multiset Resource :=
  if w.1 = ∅ then 0 else {w}

def Next (a b c : Resource) (rest : Multiset Resource) : Multiset Resource :=
  c ::ₘ (Keep a + Keep b + rest)

def ResourceStep (p q : Multiset Resource) : Prop :=
  (∃ a b c rest, p = a ::ₘ b ::ₘ rest ∧ q = Next a b c rest ∧
    (c = RJoin a b ∨ (AllowedSides a b ∧ c = RMeet a b))) ∨
  (∃ w rest, w.1 ≠ ∅ ∧ p = w ::ₘ rest ∧ q = w ::ₘ w ::ₘ rest) ∨
  (∃ w rest, p = w ::ₘ rest ∧ q = rest)

def Blocked (p : Multiset Resource) : Prop :=
  ∃ E ∈ DirtyEdges, ∃ T : Finset (Fin 10),
    (∀ AB ∈ OtherSides, Separates T AB.1 AB.2 ∧ Separates T AB.2 AB.1) ∧
    ∀ w ∈ p, RSafe E T w

def Exceptional (p : Multiset Resource) : Prop :=
  ∃ d rest, p = d ::ₘ rest ∧ d.1 = ∅ ∧
    (∀ E ∈ CrossPairs, d.2 E = true) ∧ AllOrdinary rest

def Invariant (p : Multiset Resource) : Prop := Blocked p ∨ Exceptional p

def Target (w : Resource) : Prop :=
  w.1 = ∅ ∧ (∀ E ∈ DirtyEdges, w.2 E = true) ∧ w.2 {4, 5} = false

lemma rsafe_join {E T : Finset (Fin 10)} {a b : Resource}
    (ha : RSafe E T a) (hb : RSafe E T b) : RSafe E T (RJoin a b) := by
  exact safe_join (a := (a.1, a.2 E)) (b := (b.1, b.2 E)) ha hb

lemma rsafe_meet {E T : Finset (Fin 10)} {a b : Resource}
    (ha : RSafe E T a) (hb : RSafe E T b) (hs : Separates T a.1 b.1) :
    RSafe E T (RMeet a b) := by
  exact safe_meet (a := (a.1, a.2 E)) (b := (b.1, b.2 E)) ha hb hs

lemma rsafe_zero_false {E T : Finset (Fin 10)} {w : Resource}
    (h : RSafe E T w) (hz : w.1 = ∅) : w.2 E = false :=
  safe_zero_false (w := (w.1, w.2 E)) h hz

lemma cross_separation :
    ∀ E ∈ CrossPairs, ∀ AB ∈ OtherSides,
      Separates E AB.1 AB.2 ∧ Separates E AB.2 AB.1 := by
  simp [CrossPairs, OtherSides, Separates]

lemma dirty_mem_cross : ∀ E ∈ DirtyEdges, E ∈ CrossPairs := by
  simp [DirtyEdges, CrossPairs]

lemma ordinary_join {a b : Resource} (ha : Ordinary a) (hb : Ordinary b) :
    Ordinary (RJoin a b) := by
  intro E hE
  exact rsafe_join (ha E hE) (hb E hE)

lemma ordinary_meet {a b : Resource} (ha : Ordinary a) (hb : Ordinary b)
    (hs : AllowedSides a b) : Ordinary (RMeet a b) := by
  intro E hE
  apply rsafe_meet (ha E hE) (hb E hE)
  rcases hs with hs | hs
  · exact (cross_separation E hE _ hs).1
  · exact (cross_separation E hE _ hs).2

lemma keep_mem {a w : Resource} (h : w ∈ Keep a) : w = a := by
  classical
  by_cases hz : a.1 = ∅
  · simp [Keep, hz] at h
  · simpa [Keep, hz] using h

lemma allOrdinary_next {a b c : Resource} {rest : Multiset Resource}
    (ha : Ordinary a) (hb : Ordinary b) (hc : Ordinary c) (hr : AllOrdinary rest) :
    AllOrdinary (Next a b c rest) := by
  intro w hw
  simp only [Next, Multiset.mem_cons, Multiset.mem_add] at hw
  rcases hw with rfl | (hw | hw) | hw
  · exact hc
  · exact (keep_mem hw) ▸ ha
  · exact (keep_mem hw) ▸ hb
  · exact hr w hw

lemma allOrdinary_blocked {p : Multiset Resource} (hp : AllOrdinary p) : Blocked p := by
  refine ⟨{3, 4}, by simp [DirtyEdges], {3, 4}, ?_, ?_⟩
  · exact cross_separation _ (by simp [CrossPairs])
  · intro w hw
    exact hp w hw _ (by simp [CrossPairs])

lemma blocked_no_target {p : Multiset Resource} (hp : Blocked p)
    {w : Resource} (hw : w ∈ p) : ¬ Target w := by
  obtain ⟨E, hE, T, _, hs⟩ := hp
  rintro ⟨hz, ht, _⟩
  have hf := rsafe_zero_false (hs w hw) hz
  rw [ht E hE] at hf
  contradiction

lemma exceptional_no_target {p : Multiset Resource} (hp : Exceptional p)
    {w : Resource} (hw : w ∈ p) : ¬ Target w := by
  obtain ⟨d, rest, rfl, hd, hdt, hr⟩ := hp
  rcases Multiset.mem_cons.mp hw with rfl | hw
  · rintro ⟨_, _, hf⟩
    have ht := hdt {4, 5} (by simp [CrossPairs])
    rw [hf] at ht
    contradiction
  · exact blocked_no_target (allOrdinary_blocked hr) hw

lemma invariant_no_target {p : Multiset Resource} (hp : Invariant p)
    {w : Resource} (hw : w ∈ p) : ¬ Target w := by
  rcases hp with hp | hp
  · exact blocked_no_target hp hw
  · exact exceptional_no_target hp hw


lemma all_safe_next {E T : Finset (Fin 10)} {a b c : Resource}
    {rest : Multiset Resource}
    (ha : RSafe E T a) (hb : RSafe E T b) (hc : RSafe E T c)
    (hr : ∀ w ∈ rest, RSafe E T w) :
    ∀ w ∈ Next a b c rest, RSafe E T w := by
  intro w hw
  simp only [Next, Multiset.mem_cons, Multiset.mem_add] at hw
  rcases hw with rfl | (hw | hw) | hw
  · exact hc
  · exact (keep_mem hw) ▸ ha
  · exact (keep_mem hw) ▸ hb
  · exact hr w hw

lemma blocked_step {p q : Multiset Resource} (hp : Blocked p)
    (hstep : ResourceStep p q) : Blocked q := by
  obtain ⟨E, hE, T, hT, hs⟩ := hp
  refine ⟨E, hE, T, hT, ?_⟩
  rcases hstep with ⟨a, b, c, rest, rfl, rfl, hc⟩ | ⟨w, rest, _, rfl, rfl⟩ | ⟨w, rest, rfl, rfl⟩
  · have ha := hs a (by simp)
    have hb := hs b (by simp)
    have hr : ∀ w ∈ rest, RSafe E T w := fun w hw => hs w (by simp [hw])
    apply all_safe_next ha hb ?_ hr
    rcases hc with rfl | ⟨hside, rfl⟩
    · exact rsafe_join ha hb
    · apply rsafe_meet ha hb
      rcases hside with hside | hside
      · exact (hT _ hside).1
      · exact (hT _ hside).2
  · intro a ha
    simp only [Multiset.mem_cons, or_self_left] at ha
    exact hs a (Multiset.mem_cons.mpr ha)
  · intro a ha
    exact hs a (by simp [ha])

lemma ordinary_carrier_blocked {c : Resource} {rest : Multiset Resource}
    (hc : c.1.Nonempty) (hr : AllOrdinary rest) : Blocked (c ::ₘ rest) := by
  obtain ⟨v, hv⟩ := hc
  refine ⟨UniversalEdge v, universal_edge_valid v, UniversalBarrier v,
    all_vertices_separation v, ?_⟩
  intro w hw
  rcases Multiset.mem_cons.mp hw with rfl | hw
  · intro _
    exact ⟨v, Finset.mem_inter.mpr ⟨hv, Finset.mem_insert_self _ _⟩⟩
  · intro ht
    obtain ⟨u, hu⟩ := hr w hw _ (dirty_mem_cross _ (universal_edge_valid v)) ht
    obtain ⟨hus, huE⟩ := Finset.mem_inter.mp hu
    exact ⟨u, Finset.mem_inter.mpr ⟨hus, Finset.mem_insert_of_mem huE⟩⟩

lemma keep_ordinary {w : Resource} (h : Ordinary w) : AllOrdinary (Keep w) := by
  intro a ha
  exact (keep_mem ha) ▸ h

lemma allOrdinary_add {p q : Multiset Resource}
    (hp : AllOrdinary p) (hq : AllOrdinary q) : AllOrdinary (p + q) := by
  intro w hw
  rcases Multiset.mem_add.mp hw with hw | hw
  · exact hp w hw
  · exact hq w hw

lemma allOrdinary_cons {w : Resource} {p : Multiset Resource}
    (hw : Ordinary w) (hp : AllOrdinary p) : AllOrdinary (w ::ₘ p) := by
  intro a ha
  rcases Multiset.mem_cons.mp ha with rfl | ha
  · exact hw
  · exact hp a ha

lemma zero_side_of_allowed {a b : Resource} (ha : a.1 = ∅) (hs : AllowedSides a b) :
    b.1 = ∅ := by
  have hzero : ∀ AB ∈ OtherSides,
      (AB.1 = ∅ → AB.2 = ∅) ∧ (AB.2 = ∅ → AB.1 = ∅) := by
    simp [OtherSides]
  rcases hs with hs | hs
  · exact (hzero _ hs).1 ha
  · exact (hzero _ hs).2 ha

lemma exceptional_left_step {d b c : Resource} {rest : Multiset Resource}
    (hd : d.1 = ∅) (hdt : ∀ E ∈ CrossPairs, d.2 E = true)
    (hb : Ordinary b) (hr : AllOrdinary rest)
    (hc : c = RJoin d b ∨ (AllowedSides d b ∧ c = RMeet d b)) :
    Invariant (Next d b c rest) := by
  classical
  rcases hc with rfl | ⟨hs, rfl⟩
  · by_cases hbs : b.1 = ∅
    · right
      refine ⟨RJoin d b, rest, ?_, ?_, ?_, hr⟩
      · simp [Next, Keep, hd, hbs]
      · simp [RJoin, hd, hbs]
      · intro E hE
        simp [RJoin, hdt E hE]
    · left
      have hbp : (RJoin d b).1.Nonempty := by
        simpa [RJoin, hd] using Finset.nonempty_iff_ne_empty.mpr hbs
      have hpool : AllOrdinary (Keep d + Keep b + rest) := by
        simpa [Keep, hd, hbs] using allOrdinary_cons hb hr
      exact ordinary_carrier_blocked hbp hpool
  · left
    have hbs := zero_side_of_allowed hd hs
    have hc : Ordinary (RMeet d b) := by
      intro E hE ht
      have hbf := rsafe_zero_false (hb E hE) hbs
      simp [RMeet, hbf] at ht
    apply allOrdinary_blocked
    simpa [Next, Keep, hd, hbs] using allOrdinary_cons hc hr


lemma next_swap (a b c : Resource) (rest : Multiset Resource) :
    Next a b c rest = Next b a c rest := by
  simp only [Next, add_comm (Keep a) (Keep b)]

lemma rjoin_swap (a b : Resource) : RJoin a b = RJoin b a := by
  apply Prod.ext
  · exact Finset.union_comm _ _
  · funext E
    exact Bool.or_comm _ _

lemma rmeet_swap (a b : Resource) : RMeet a b = RMeet b a := by
  apply Prod.ext
  · exact Finset.inter_comm _ _
  · funext E
    exact Bool.and_comm _ _

lemma ordinary_result {a b c : Resource} (ha : Ordinary a) (hb : Ordinary b)
    (hc : c = RJoin a b ∨ (AllowedSides a b ∧ c = RMeet a b)) : Ordinary c := by
  rcases hc with rfl | ⟨hs, rfl⟩
  · exact ordinary_join ha hb
  · exact ordinary_meet ha hb hs

lemma exceptional_step {p q : Multiset Resource} (hp : Exceptional p)
    (hstep : ResourceStep p q) : Invariant q := by
  classical
  obtain ⟨d, r0, hpd, hd, hdt, hr0⟩ := hp
  rcases hstep with ⟨a, b, c, rest, hpab, rfl, hc⟩ |
    ⟨w, rest, hws, hpw, rfl⟩ | ⟨w, rest, hpw, hqr⟩
  · have heq : d ::ₘ r0 = a ::ₘ b ::ₘ rest := hpd.symm.trans hpab
    by_cases had : a = d
    · subst a
      have hrEq := (Multiset.cons_inj_right d).mp heq
      rw [hrEq] at hr0
      exact exceptional_left_step hd hdt (hr0 b (by simp))
        (fun w hw => hr0 w (by simp [hw])) hc
    · by_cases hbd : b = d
      · subst b
        rw [Multiset.cons_swap a d] at heq
        have hrEq := (Multiset.cons_inj_right d).mp heq
        rw [hrEq] at hr0
        rw [next_swap]
        apply exceptional_left_step hd hdt (hr0 a (by simp))
          (fun w hw => hr0 w (by simp [hw]))
        rcases hc with hc | ⟨hs, hc⟩
        · left
          exact hc.trans (rjoin_swap _ _)
        · right
          exact ⟨Or.symm hs, hc.trans (rmeet_swap _ _)⟩
      · have hdm : d ∈ a ::ₘ b ::ₘ rest := heq ▸ (Multiset.mem_cons_self d r0)
        have hdr : d ∈ rest := by
          simpa [Ne.symm had, Ne.symm hbd] using hdm
        obtain ⟨r, rfl⟩ := Multiset.exists_cons_of_mem hdr
        rw [Multiset.cons_swap b d, Multiset.cons_swap a d] at heq
        have hrEq := (Multiset.cons_inj_right d).mp heq
        rw [hrEq] at hr0
        have ha : Ordinary a := hr0 a (by simp)
        have hb : Ordinary b := hr0 b (by simp)
        have hr : AllOrdinary r := fun w hw => hr0 w (by simp [hw])
        right
        refine ⟨d, Next a b c r, ?_, hd, hdt,
          allOrdinary_next ha hb (ordinary_result ha hb hc) hr⟩
        simp only [Next, Multiset.add_cons]
        exact Multiset.cons_swap _ _ _
  · have heq : d ::ₘ r0 = w ::ₘ rest := hpd.symm.trans hpw
    have hdw : d ≠ w := by
      intro h
      subst w
      exact hws hd
    have hdm : d ∈ w ::ₘ rest := heq ▸ (Multiset.mem_cons_self d r0)
    have hdr : d ∈ rest := by simpa [hdw] using hdm
    obtain ⟨r, rfl⟩ := Multiset.exists_cons_of_mem hdr
    rw [Multiset.cons_swap w d] at heq
    have hrEq := (Multiset.cons_inj_right d).mp heq
    rw [hrEq] at hr0
    right
    refine ⟨d, w ::ₘ w ::ₘ r, ?_, hd, hdt, ?_⟩
    · rw [Multiset.cons_swap w d, Multiset.cons_swap w d]
    · exact allOrdinary_cons (hr0 w (by simp)) hr0
  · rw [hqr]
    have heq : d ::ₘ r0 = w ::ₘ rest := hpd.symm.trans hpw
    by_cases hdw : d = w
    · subst w
      have hrEq := (Multiset.cons_inj_right d).mp heq
      rw [hrEq] at hr0
      exact Or.inl (allOrdinary_blocked hr0)
    · have hdm : d ∈ w ::ₘ rest := heq ▸ (Multiset.mem_cons_self d r0)
      have hdr : d ∈ rest := by simpa [hdw] using hdm
      obtain ⟨r, rfl⟩ := Multiset.exists_cons_of_mem hdr
      rw [Multiset.cons_swap w d] at heq
      have hrEq := (Multiset.cons_inj_right d).mp heq
      rw [hrEq] at hr0
      exact Or.inr ⟨d, r, rfl, hd, hdt, fun a ha => hr0 a (by simp [ha])⟩

lemma invariant_step {p q : Multiset Resource} (hp : Invariant p)
    (hstep : ResourceStep p q) : Invariant q := by
  rcases hp with hp | hp
  · exact Or.inl (blocked_step hp hstep)
  · exact exceptional_step hp hstep

def ResourceTrace (p : Multiset Resource) : List (Multiset Resource) → Prop
  | [] => True
  | q :: qs => ResourceStep p q ∧ ResourceTrace q qs

lemma invariant_trace {p : Multiset Resource} {qs : List (Multiset Resource)}
    (hp : Invariant p) (ht : ResourceTrace p qs) : ∀ q ∈ qs, Invariant q := by
  induction qs generalizing p with
  | nil => simp
  | cons q qs ih =>
      obtain ⟨hs, ht⟩ := ht
      have hq := invariant_step hp hs
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · exact hq
      · exact ih hq ht r hr

lemma canonical_resource_exclusion {d : Resource} {ordinary : Multiset Resource}
    {qs : List (Multiset Resource)} {q : Multiset Resource} {out : Resource}
    (hd : d.1 = ∅) (hdt : ∀ E ∈ CrossPairs, d.2 E = true)
    (ho : AllOrdinary ordinary) (ht : ResourceTrace (d ::ₘ ordinary) qs)
    (hq : q ∈ qs) (hout : out ∈ q) : ¬ Target out := by
  have hi : Invariant (d ::ₘ ordinary) := Or.inr ⟨d, ordinary, rfl, hd, hdt, ho⟩
  exact invariant_no_target (invariant_trace hi ht q hq) hout

end ResourceExclusion


namespace SevenRows

def raw : List (BitVec 7) := [49,73,26,44,98,84]

def base : List (BitVec 7) := [0, 26, 44, 49, 59, 61, 62, 63, 73, 84, 91, 93, 94, 95, 98, 107, 109, 110, 111, 115, 117, 118, 119, 121, 122, 123, 124, 125, 126, 127]

def first : List (BitVec 7) := [0, 1, 2, 4, 8, 9, 10, 12, 16, 17, 18, 20, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 36, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 68, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127]

def small (x : BitVec 7) : Bool := x == 0 || x == 1 || x == 2 || x == 4

def clean (x : BitVec 7) : Bool := x &&& 120 == 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma raw_cert : (raw.all base.contains) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma base_closed_cert :
    (base.all fun a => base.all fun b => base.contains (a ||| b)) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma first_cert :
    (base.all fun a => base.all fun b => first.contains (a &&& b)) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma meet_clean_cert :
    (first.all fun f => base.all fun b => !(clean (f &&& b)) || small (f &&& b)) = true := by decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma base_clean_cert :
    (base.all fun a => !(clean a) || a == 0) = true := by decide +kernel

lemma raw_mem {a : BitVec 7} (ha : a ∈ raw) : a ∈ base := by
  exact List.contains_iff_mem.mp (List.all_eq_true.mp raw_cert a ha)

lemma base_or {a b : BitVec 7} (ha : a ∈ base) (hb : b ∈ base) : a ||| b ∈ base := by
  exact List.contains_iff_mem.mp
    (List.all_eq_true.mp (List.all_eq_true.mp base_closed_cert a ha) b hb)

lemma pair_mem {a b : BitVec 7} (ha : a ∈ base) (hb : b ∈ base) : a &&& b ∈ first := by
  exact List.contains_iff_mem.mp
    (List.all_eq_true.mp (List.all_eq_true.mp first_cert a ha) b hb)

lemma meet_clean_small {f b : BitVec 7} (hf : f ∈ first) (hb : b ∈ base)
    (hc : clean (f &&& b) = true) : small (f &&& b) = true := by
  have h := List.all_eq_true.mp (List.all_eq_true.mp meet_clean_cert f hf) b hb
  simpa only [hc, Bool.not_true, Bool.false_or] using h

lemma base_clean_zero {a : BitVec 7} (ha : a ∈ base) (hc : clean a = true) : a = 0 := by
  have h := List.all_eq_true.mp base_clean_cert a ha
  simpa only [hc, Bool.not_true, Bool.false_or, beq_iff_eq] using h

lemma clean_or {a b : BitVec 7} :
    clean (a ||| b) = true ↔ clean a = true ∧ clean b = true := by
  simp only [clean, beq_iff_eq, BitVec.and_or_distrib_right]
  exact BitVec.or_eq_zero_iff

lemma first_clean_small {f : BitVec 7} (hf : f ∈ first)
    (hc : clean f = true) : small f = true := by
  have he : f &&& (127 : BitVec 7) = f := by
    change f &&& BitVec.allOnes 7 = f
    exact BitVec.and_allOnes
  have hc' : clean (f &&& (127 : BitVec 7)) = true := by simpa only [he] using hc
  have h := meet_clean_small hf (by decide : (127 : BitVec 7) ∈ base) hc'
  simpa only [he] using h

lemma small_or_ne_seven {a b : BitVec 7} (ha : small a = true) (hb : small b = true) :
    a ||| b ≠ 7 := by
  simp only [small, Bool.or_eq_true, beq_iff_eq] at ha hb
  rcases ha with ((rfl | rfl) | rfl) | rfl <;>
    rcases hb with ((rfl | rfl) | rfl) | rfl <;> decide

lemma union_ne_seven {a b : BitVec 7}
    (ha : clean a = true → small a = true) (hb : clean b = true → small b = true) :
    a ||| b ≠ 7 := by
  intro he
  have hc : clean (a ||| b) = true := by rw [he]; decide
  obtain ⟨hca, hcb⟩ := clean_or.mp hc
  exact small_or_ne_seven (ha hca) (hb hcb) he

lemma first_ne_seven {f : BitVec 7} (hf : f ∈ first) : f ≠ 7 := by
  intro he
  have hs := first_clean_small hf (by rw [he]; decide)
  rw [he] at hs
  exact (by decide : small (7 : BitVec 7) ≠ true) hs

def side (a f : BitVec 7) (useFirst : Bool) : BitVec 7 :=
  if useFirst then a ||| f else a

lemma and_both_sides (a b f : BitVec 7) :
    (a ||| f) &&& (b ||| f) = (a &&& b) ||| f := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  simp only [BitVec.getElem_and, BitVec.getElem_or]
  cases a[i] <;> cases b[i] <;> cases f[i] <;> rfl

lemma or_first_sides (a b f : BitVec 7) (u v : Bool) :
    f ||| (side a f u &&& side b f v) = f ||| (a &&& b) := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  cases u <;> cases v <;>
    simp only [side, Bool.false_eq_true, ↓reduceIte,
      BitVec.getElem_and, BitVec.getElem_or] <;>
    cases a[i] <;> cases b[i] <;> cases f[i] <;> rfl

lemma no_two_ands {f a b : BitVec 7} (hf : f ∈ first) (ha : a ∈ base) (hb : b ∈ base)
    (useLeft useRight useOutput : Bool) :
    (if useOutput then f ||| (side a f useLeft &&& side b f useRight)
      else side a f useLeft &&& side b f useRight) ≠ 7 := by
  cases useOutput with
  | true =>
    change f ||| (side a f useLeft &&& side b f useRight) ≠ 7
    rw [or_first_sides]
    exact union_ne_seven (first_clean_small hf) (first_clean_small (pair_mem ha hb))
  | false =>
    change side a f useLeft &&& side b f useRight ≠ 7
    cases useLeft <;> cases useRight
    · exact first_ne_seven (pair_mem ha hb)
    · change a &&& (b ||| f) ≠ 7
      rw [BitVec.and_or_distrib_left, BitVec.and_comm a f]
      exact union_ne_seven (first_clean_small (pair_mem ha hb)) (meet_clean_small hf ha)
    · change (a ||| f) &&& b ≠ 7
      rw [BitVec.and_or_distrib_right]
      exact union_ne_seven (first_clean_small (pair_mem ha hb)) (meet_clean_small hf hb)
    · change (a ||| f) &&& (b ||| f) ≠ 7
      rw [and_both_sides]
      exact union_ne_seven (first_clean_small (pair_mem ha hb)) (first_clean_small hf)

lemma zero_mem_base : (0 : BitVec 7) ∈ base := by decide +kernel

lemma fold_or_mem_base {xs : List (BitVec 7)} {a : BitVec 7}
    (ha : a ∈ base) (hxs : ∀ x ∈ xs, x ∈ base) : xs.foldl (· ||| ·) a ∈ base := by
  induction xs generalizing a with
  | nil => exact ha
  | cons x xs ih =>
    apply ih (base_or ha (hxs x List.mem_cons_self))
    intro y hy
    exact hxs y (List.mem_cons_of_mem x hy)

lemma fold_raw_mem_base {xs : List (BitVec 7)}
    (hxs : ∀ x ∈ xs, x ∈ raw) : xs.foldl (· ||| ·) 0 ∈ base := by
  exact fold_or_mem_base zero_mem_base (fun x hx => raw_mem (hxs x hx))

lemma no_output_two_ands {f a b c : BitVec 7}
    (hf : f ∈ first) (ha : a ∈ base) (hb : b ∈ base) (hc : c ∈ base)
    (useLeft useRight useFirst useSecond : Bool) :
    c ||| (if useSecond then
      (if useFirst then f ||| (side a f useLeft &&& side b f useRight)
        else side a f useLeft &&& side b f useRight)
      else (if useFirst then f else 0)) ≠ 7 := by
  intro he
  have hclean : clean (c ||| (if useSecond then
      (if useFirst then f ||| (side a f useLeft &&& side b f useRight)
        else side a f useLeft &&& side b f useRight)
      else (if useFirst then f else 0))) = true := by rw [he]; decide
  have hz := base_clean_zero hc (clean_or.mp hclean).1
  subst c
  have he' : (if useSecond then
      (if useFirst then f ||| (side a f useLeft &&& side b f useRight)
        else side a f useLeft &&& side b f useRight)
      else (if useFirst then f else 0)) = 7 := by simpa using he
  cases useSecond with
  | true => exact no_two_ands hf ha hb useLeft useRight useFirst he'
  | false =>
    cases useFirst with
    | true => exact first_ne_seven hf he'
    | false => exact (by decide : (0 : BitVec 7) ≠ 7) he'

end SevenRows

end PEqualNP.Outside.L_meta_2590
