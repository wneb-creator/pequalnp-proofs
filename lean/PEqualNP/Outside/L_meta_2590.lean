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


namespace IndexSchedule

open ResourceExclusion

def Pool (W : ℕ → Resource) (ids : Finset ℕ) : Multiset Resource := ids.val.map W

def DropZero (W : ℕ → Resource) (i : ℕ) (ids : Finset ℕ) : Finset ℕ :=
  if (W i).1 = ∅ then ids.erase i else ids

def NextIds (W : ℕ → Resource) (a b out : ℕ) (ids : Finset ℕ) : Finset ℕ :=
  insert out (DropZero W b (DropZero W a ids))

def Available (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ) : ℕ → Finset ℕ
  | 0 => Finset.range start
  | t + 1 => NextIds W (A (start + t)) (B (start + t)) (start + t)
      (Available W start A B t)

lemma drop_subset (W : ℕ → Resource) (i : ℕ) (ids : Finset ℕ) :
    DropZero W i ids ⊆ ids := by
  unfold DropZero
  split
  · exact Finset.erase_subset _ _
  · exact Finset.Subset.refl _

lemma mem_drop {W : ℕ → Resource} {i x : ℕ} {ids : Finset ℕ}
    (hx : x ∈ ids) (hkeep : (W x).1 ≠ ∅ ∨ x ≠ i) : x ∈ DropZero W i ids := by
  unfold DropZero
  split_ifs with hi
  · apply Finset.mem_erase.mpr
    refine ⟨?_, hx⟩
    rcases hkeep with hkeep | hkeep
    · intro hxi
      subst x
      exact hkeep hi
    · exact hkeep
  · exact hx

lemma available_bounded (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ)
    (t : ℕ) : ∀ x ∈ Available W start A B t, x < start + t := by
  induction t with
  | zero => simp [Available]
  | succ t ih =>
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · omega
      · have hx' := drop_subset W _ _ (drop_subset W _ _ hx)
        have hb := ih x hx'
        omega

lemma available_complete (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ)
    (t : ℕ) : ∀ x, x < start + t →
      ((W x).1 ≠ ∅ ∨ ∀ j < t, A (start + j) ≠ x ∧ B (start + j) ≠ x) →
      x ∈ Available W start A B t := by
  induction t with
  | zero => simp [Available]
  | succ t ih =>
      intro x hbound hunused
      by_cases hlast : x = start + t
      · subst x
        exact Finset.mem_insert_self _ _
      · have hold : x < start + t := by omega
        have hprev : (W x).1 ≠ ∅ ∨ ∀ j < t,
            A (start + j) ≠ x ∧ B (start + j) ≠ x := by
          rcases hunused with hp | hu
          · exact Or.inl hp
          · exact Or.inr (fun j hj => hu j (by omega))
        have hmem := ih x hold hprev
        apply Finset.mem_insert_of_mem
        apply mem_drop
        · apply mem_drop hmem
          rcases hunused with hp | hu
          · exact Or.inl hp
          · exact Or.inr (Ne.symm (hu t (by omega)).1)
        · rcases hunused with hp | hu
          · exact Or.inl hp
          · exact Or.inr (Ne.symm (hu t (by omega)).2)

def Reads (A B : ℕ → ℕ) (i x : ℕ) : Prop := A i = x ∨ B i = x

def LinearUpTo (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ i < n, ∀ j < n, ∀ x, (W x).1 = ∅ →
    Reads A B (start + i) x → Reads A B (start + j) x → i = j

lemma source_available {W : ℕ → Resource} {start n t x : ℕ} {A B : ℕ → ℕ}
    (hlin : LinearUpTo W start A B n) (ht : t < n)
    (hx : x < start + t) (hr : Reads A B (start + t) x) :
    x ∈ Available W start A B t := by
  apply available_complete W start A B t x hx
  by_cases hp : (W x).1 = ∅
  · right
    intro j hj
    constructor
    · intro hja
      have heq := hlin t ht j (by omega) x hp hr (Or.inl hja)
      omega
    · intro hjb
      have heq := hlin t ht j (by omega) x hp hr (Or.inr hjb)
      omega
  · exact Or.inl hp

lemma pool_insert {W : ℕ → Resource} {ids : Finset ℕ} {i : ℕ} (hi : i ∉ ids) :
    Pool W (insert i ids) = W i ::ₘ Pool W ids := by
  simp only [Pool, Finset.insert_val_of_notMem hi, Multiset.map_cons]

lemma pool_erase_decomp {W : ℕ → Resource} {ids : Finset ℕ} {i : ℕ} (hi : i ∈ ids) :
    Pool W ids = W i ::ₘ Pool W (ids.erase i) := by
  calc
    Pool W ids = Pool W (insert i (ids.erase i)) := by rw [Finset.insert_erase hi]
    _ = W i ::ₘ Pool W (ids.erase i) := pool_insert (Finset.notMem_erase _ _)

lemma pool_two_decomp {W : ℕ → Resource} {ids : Finset ℕ} {a b : ℕ}
    (ha : a ∈ ids) (hb : b ∈ ids) (hab : a ≠ b) :
    Pool W ids = W a ::ₘ W b ::ₘ Pool W ((ids.erase a).erase b) := by
  rw [pool_erase_decomp ha]
  rw [pool_erase_decomp (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩)]

lemma pool_drop_two {W : ℕ → Resource} {ids : Finset ℕ} {a b : ℕ}
    (ha : a ∈ ids) (hb : b ∈ ids) (hab : a ≠ b) :
    Pool W (DropZero W b (DropZero W a ids)) =
      Keep (W a) + Keep (W b) + Pool W ((ids.erase a).erase b) := by
  classical
  by_cases hza : (W a).1 = ∅ <;> by_cases hzb : (W b).1 = ∅
  · simp [DropZero, Keep, hza, hzb]
  · simp only [DropZero, Keep, hza, hzb, ite_true, ite_false, zero_add]
    exact pool_erase_decomp (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩)
  · simp only [DropZero, Keep, hza, hzb, ite_true, ite_false, add_zero]
    rw [Finset.erase_right_comm]
    exact pool_erase_decomp (Finset.mem_erase.mpr ⟨hab, ha⟩)
  · simp only [DropZero, Keep, hza, hzb, ite_false]
    simpa using pool_two_decomp ha hb hab

lemma index_resource_step {W : ℕ → Resource} {ids : Finset ℕ} {a b out : ℕ}
    (ha : a ∈ ids) (hb : b ∈ ids) (hab : a ≠ b) (hout : out ∉ ids)
    (hg : W out = RJoin (W a) (W b) ∨
      (AllowedSides (W a) (W b) ∧ W out = RMeet (W a) (W b))) :
    ResourceStep (Pool W ids) (Pool W (NextIds W a b out ids)) := by
  left
  refine ⟨W a, W b, W out, Pool W ((ids.erase a).erase b),
    pool_two_decomp ha hb hab, ?_, hg⟩
  have hfresh : out ∉ DropZero W b (DropZero W a ids) := by
    intro h
    exact hout (drop_subset W _ _ (drop_subset W _ _ h))
  rw [NextIds, pool_insert hfresh, pool_drop_two ha hb hab]
  rfl


def ValidUpTo (start : ℕ) (A B : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ t < n, A (start + t) < start + t ∧ B (start + t) < start + t ∧
    A (start + t) ≠ B (start + t)

def CanonicalUpTo (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ t < n,
    W (start + t) = RJoin (W (A (start + t))) (W (B (start + t))) ∨
    (AllowedSides (W (A (start + t))) (W (B (start + t))) ∧
      W (start + t) = RMeet (W (A (start + t))) (W (B (start + t))))

lemma available_step {W : ℕ → Resource} {start n t : ℕ} {A B : ℕ → ℕ}
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo W start A B n) (ht : t < n) :
    ResourceStep (Pool W (Available W start A B t))
      (Pool W (Available W start A B (t + 1))) := by
  obtain ⟨ha, hb, hab⟩ := hv t ht
  have haa := source_available hl ht ha (Or.inl rfl)
  have hba := source_available hl ht hb (Or.inr rfl)
  apply index_resource_step haa hba hab ?_ (hc t ht)
  intro h
  have := available_bounded W start A B t _ h
  omega

lemma program_invariant {W : ℕ → Resource} {start n : ℕ} {A B : ℕ → ℕ}
    (hp : Invariant (Pool W (Finset.range start)))
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo W start A B n) :
    ∀ t ≤ n, Invariant (Pool W (Available W start A B t)) := by
  intro t
  induction t with
  | zero => intro _; exact hp
  | succ t ih =>
      intro ht
      exact invariant_step (ih (by omega)) (available_step hv hl hc (by omega))

lemma pool_mem {W : ℕ → Resource} {ids : Finset ℕ} {i : ℕ} (hi : i ∈ ids) :
    W i ∈ Pool W ids := by
  exact Multiset.mem_map.mpr ⟨i, hi, rfl⟩

lemma canonical_program_exclusion {W : ℕ → Resource} {start n : ℕ} {A B : ℕ → ℕ}
    (hp : Invariant (Pool W (Finset.range start)))
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo W start A B n) :
    ∀ t < n, ¬ Target (W (start + t)) := by
  intro t ht
  have hinv := program_invariant hp hv hl hc (t + 1) (by omega)
  apply invariant_no_target hinv
  apply pool_mem
  exact Finset.mem_insert_self _ _

lemma initial_exceptional {W : ℕ → Resource} {start d : ℕ}
    (hd : d < start) (hz : (W d).1 = ∅)
    (ht : ∀ E ∈ CrossPairs, (W d).2 E = true)
    (ho : ∀ i < start, i ≠ d → Ordinary (W i)) :
    Invariant (Pool W (Finset.range start)) := by
  right
  refine ⟨W d, Pool W ((Finset.range start).erase d),
    pool_erase_decomp (Finset.mem_range.mpr hd), hz, ht, ?_⟩
  intro w hw
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hw
  have hi' : i ∈ (Finset.range start).erase d := hi
  obtain ⟨hid, hir⟩ := Finset.mem_erase.mp hi'
  exact ho i (Finset.mem_range.mp hir) hid

lemma seeded_program_exclusion {W : ℕ → Resource} {start n d : ℕ} {A B : ℕ → ℕ}
    (hd : d < start) (hz : (W d).1 = ∅)
    (ht : ∀ E ∈ CrossPairs, (W d).2 E = true)
    (ho : ∀ i < start, i ≠ d → Ordinary (W i))
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo W start A B n) :
    ∀ t < n, ¬ Target (W (start + t)) :=
  canonical_program_exclusion (initial_exceptional hd hz ht ho) hv hl hc


lemma program_any_wire_exclusion {W : ℕ → Resource} {start n : ℕ} {A B : ℕ → ℕ}
    (hp : Invariant (Pool W (Finset.range start)))
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo W start A B n) :
    ∀ i < start + n, ¬ Target (W i) := by
  intro i hi
  by_cases hold : i < start
  · exact invariant_no_target hp (pool_mem (Finset.mem_range.mpr hold))
  · have ht : i - start < n := by omega
    have heq : start + (i - start) = i := by omega
    simpa only [heq] using canonical_program_exclusion hp hv hl hc (i - start) ht

lemma ordinary_prefix {W : ℕ → Resource} {start n : ℕ} {A B : ℕ → ℕ}
    (hp : ∀ i < start, Ordinary (W i))
    (hv : ValidUpTo start A B n) (hc : CanonicalUpTo W start A B n) :
    ∀ i < start + n, Ordinary (W i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
      intro hi
      by_cases hold : i < start
      · exact hp i hold
      · have ht : i - start < n := by omega
        have heq : start + (i - start) = i := by omega
        obtain ⟨ha, hb, _⟩ := hv (i - start) ht
        rw [heq] at ha hb
        have hca := hc (i - start) ht
        rw [heq] at hca
        exact ordinary_result (ih _ ha (by omega)) (ih _ hb (by omega)) hca

end IndexSchedule

namespace SevenRows.Adapter

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def opt (f : BitVec 7) (u : Bool) : BitVec 7 := if u then f else 0

def span1 (f w : BitVec 7) : Prop := ∃ a ∈ base, ∃ u, w = side a f u

def span2 (f g w : BitVec 7) : Prop :=
  ∃ a ∈ base, ∃ u v, w = (a ||| opt f u) ||| opt g v

def Second (f g : BitVec 7) : Prop :=
  ∃ a ∈ base, ∃ b ∈ base, ∃ u v, g = side a f u &&& side b f v

def Phase : ℕ → List (BitVec 7) → Prop
  | 0, ws => ∀ w ∈ ws, w ∈ base
  | 1, ws => ∃ f ∈ first, ∀ w ∈ ws, span1 f w
  | 2, ws => ∃ f ∈ first, ∃ g, Second f g ∧ ∀ w ∈ ws, span2 f g w
  | _ + 3, _ => False

lemma or0 (a : BitVec 7) : a ||| (0 : BitVec 7) = a := BitVec.or_zero
lemma zeroOr (a : BitVec 7) : (0 : BitVec 7) ||| a = a := BitVec.zero_or
lemma zero_bit (i : ℕ) (hi : i < 7) : (0 : BitVec 7)[i] = false := BitVec.getElem_zero hi

lemma and127 (a : BitVec 7) : a &&& (127 : BitVec 7) = a := by
  change a &&& BitVec.allOnes 7 = a
  exact BitVec.and_allOnes

lemma opt_or (f : BitVec 7) (u v : Bool) : opt f u ||| opt f v = opt f (u || v) := by
  cases u <;> cases v <;> simp [opt]

lemma span1_or {f a b : BitVec 7} (ha : span1 f a) (hb : span1 f b) :
    span1 f (a ||| b) := by
  obtain ⟨a, ha, u, rfl⟩ := ha
  obtain ⟨b, hb, v, rfl⟩ := hb
  refine ⟨a ||| b, base_or ha hb, u || v, ?_⟩
  apply BitVec.eq_of_getElem_eq
  intro i hi
  cases u <;> cases v <;>
    simp only [side, Bool.false_eq_true, ↓reduceIte, Bool.or_false, Bool.or_true, BitVec.getElem_or] <;>
    cases a[i] <;> cases b[i] <;> cases f[i] <;> rfl

lemma span2_or {f g a b : BitVec 7} (ha : span2 f g a) (hb : span2 f g b) :
    span2 f g (a ||| b) := by
  obtain ⟨a, ha, u, v, rfl⟩ := ha
  obtain ⟨b, hb, p, q, rfl⟩ := hb
  refine ⟨a ||| b, base_or ha hb, u || p, v || q, ?_⟩
  apply BitVec.eq_of_getElem_eq
  intro i hi
  cases u <;> cases v <;> cases p <;> cases q <;>
    simp only [opt, Bool.false_eq_true, ↓reduceIte, Bool.or_false, Bool.or_true, BitVec.getElem_or, zero_bit] <;>
    cases a[i] <;> cases b[i] <;> cases f[i] <;> cases g[i] <;> rfl

lemma base_span1 (f : BitVec 7) {w : BitVec 7} (hw : w ∈ base) : span1 f w :=
  ⟨w, hw, false, rfl⟩

lemma first_span1 (f : BitVec 7) : span1 f f := by
  exact ⟨0, zero_mem_base, true, (zeroOr f).symm⟩

lemma span1_span2 (g : BitVec 7) {f w : BitVec 7} (hw : span1 f w) : span2 f g w := by
  obtain ⟨a, ha, u, rfl⟩ := hw
  refine ⟨a, ha, u, false, ?_⟩
  cases u <;> simp [side, opt]

lemma second_span2 (f g : BitVec 7) : span2 f g g := by
  exact ⟨0, zero_mem_base, false, true, by simp [opt]⟩

lemma phase_or {k : ℕ} {ws : List (BitVec 7)} (hp : Phase k ws)
    {a b : BitVec 7} (ha : a ∈ ws) (hb : b ∈ ws) : Phase k (ws ++ [a ||| b]) := by
  cases k with
  | zero =>
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact hp w hw
    · obtain rfl := List.mem_singleton.mp hw
      exact base_or (hp a ha) (hp b hb)
  | succ k => cases k with
    | zero =>
      obtain ⟨f, hf, hw⟩ := hp
      refine ⟨f, hf, ?_⟩
      intro w hm
      rcases List.mem_append.mp hm with hm | hm
      · exact hw w hm
      · obtain rfl := List.mem_singleton.mp hm
        exact span1_or (hw a ha) (hw b hb)
    | succ k => cases k with
      | zero =>
        obtain ⟨f, hf, g, hg, hw⟩ := hp
        refine ⟨f, hf, g, hg, ?_⟩
        intro w hm
        rcases List.mem_append.mp hm with hm | hm
        · exact hw w hm
        · obtain rfl := List.mem_singleton.mp hm
          exact span2_or (hw a ha) (hw b hb)
      | succ k => exact hp.elim

lemma phase_and {k : ℕ} {ws : List (BitVec 7)} (hp : Phase k ws) (hk : k < 2)
    {a b : BitVec 7} (ha : a ∈ ws) (hb : b ∈ ws) : Phase (k + 1) (ws ++ [a &&& b]) := by
  cases k with
  | zero =>
    refine ⟨a &&& b, pair_mem (hp a ha) (hp b hb), ?_⟩
    intro w hw
    rcases List.mem_append.mp hw with hw | hw
    · exact base_span1 _ (hp w hw)
    · obtain rfl := List.mem_singleton.mp hw
      exact first_span1 _
  | succ k =>
    have hk0 : k = 0 := by omega
    subst k
    obtain ⟨f, hf, hw⟩ := hp
    refine ⟨f, hf, a &&& b, ?_, ?_⟩
    · obtain ⟨a', ha', u, haeq⟩ := hw a ha
      obtain ⟨b', hb', v, hbeq⟩ := hw b hb
      exact ⟨a', ha', b', hb', u, v, by rw [haeq, hbeq]⟩
    · intro w hm
      rcases List.mem_append.mp hm with hm | hm
      · exact span1_span2 _ (hw w hm)
      · obtain rfl := List.mem_singleton.mp hm
        exact second_span2 _ _

def maskGate (ws : List (BitVec 7)) (g : Gate) : BitVec 7 :=
  match g.op with
  | .and => (g.inputs.map fun i => ws.getD i 0).foldr (· &&& ·) 127
  | .or => (g.inputs.map fun i => ws.getD i 0).foldr (· ||| ·) 0
  | _ => 0

def maskWires (gs : List Gate) (ws : List (BitVec 7)) : List (BitVec 7) :=
  gs.foldl (fun w g => w ++ [maskGate w g]) ws

def andFlag (g : Gate) : ℕ := match g.op with | .and => 1 | _ => 0

def andCount (gs : List Gate) : ℕ := (gs.map andFlag).sum

lemma mask_getD_mem (ws : List (BitVec 7)) (i : ℕ) : ws.getD i 0 ∈ 0 :: 127 :: ws := by
  by_cases h : i < ws.length
  · rw [List.getD_eq_getElem _ _ h]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.getElem_mem h))
  · rw [List.getD_eq_default _ _ (by omega)]
    simp

lemma and_pair (ws : List (BitVec 7)) (ins : List ℕ) (hlen : ins.length ≤ 2) :
    ∃ a ∈ 0 :: 127 :: ws, ∃ b ∈ 0 :: 127 :: ws,
      (ins.map fun i => ws.getD i 0).foldr (· &&& ·) 127 = a &&& b := by
  cases ins with
  | nil => exact ⟨127, by simp, 127, by simp, rfl⟩
  | cons i ins => cases ins with
    | nil => exact ⟨_, mask_getD_mem ws i, 127, by simp, rfl⟩
    | cons j ins =>
      have he : ins = [] := by apply List.length_eq_zero_iff.mp; simp only [List.length_cons] at hlen; omega
      subst ins
      exact ⟨_, mask_getD_mem ws i, _, mask_getD_mem ws j, by simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, and127]⟩

lemma or_pair (ws : List (BitVec 7)) (ins : List ℕ) (hlen : ins.length ≤ 2) :
    ∃ a ∈ 0 :: 127 :: ws, ∃ b ∈ 0 :: 127 :: ws,
      (ins.map fun i => ws.getD i 0).foldr (· ||| ·) 0 = a ||| b := by
  cases ins with
  | nil => exact ⟨0, by simp, 0, by simp, rfl⟩
  | cons i ins => cases ins with
    | nil => exact ⟨_, mask_getD_mem ws i, 0, by simp, rfl⟩
    | cons j ins =>
      have he : ins = [] := by apply List.length_eq_zero_iff.mp; simp only [List.length_cons] at hlen; omega
      subst ins
      exact ⟨_, mask_getD_mem ws i, _, mask_getD_mem ws j, by simp only [List.map_cons, List.map_nil, List.foldr_cons, List.foldr_nil, or0]⟩

lemma phase_gate {k : ℕ} {ws : List (BitVec 7)} {g : Gate}
    (hp : Phase k (0 :: 127 :: ws))
    (hg : g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (hk : k + andFlag g ≤ 2) :
    Phase (k + andFlag g) (0 :: 127 :: (ws ++ [maskGate ws g])) := by
  obtain ⟨hop, hlen⟩ := hg
  change g.op = .and ∨ g.op = .or at hop
  rcases hop with hop | hop
  · obtain ⟨a, ha, b, hb, he⟩ := and_pair ws g.inputs hlen
    have hflag : andFlag g = 1 := by simp [andFlag, hop]
    rw [hflag]
    have hkl : k < 2 := by omega
    simpa only [List.cons_append, maskGate, hop, he] using phase_and hp hkl ha hb
  · obtain ⟨a, ha, b, hb, he⟩ := or_pair ws g.inputs hlen
    have hflag : andFlag g = 0 := by simp [andFlag, hop]
    rw [hflag, Nat.add_zero]
    simpa only [List.cons_append, maskGate, hop, he] using phase_or hp ha hb

lemma maskWires_phase (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2)
    (k : ℕ) (ws : List (BitVec 7)) (hp : Phase k (0 :: 127 :: ws))
    (hk : k + andCount gs ≤ 2) :
    Phase (k + andCount gs) (0 :: 127 :: maskWires gs ws) := by
  induction gs generalizing k ws with
  | nil => simpa [maskWires, andCount] using hp
  | cons g gs ih =>
    have hc : andCount (g :: gs) = andFlag g + andCount gs := by simp [andCount]
    have hb : k + andFlag g ≤ 2 := by omega
    have hs := phase_gate hp (hgs g List.mem_cons_self) hb
    have ht : k + andFlag g + andCount gs ≤ 2 := by omega
    have h := ih (fun a ha => hgs a (List.mem_cons_of_mem g ha))
      (k + andFlag g) (ws ++ [maskGate ws g]) hs ht
    simpa only [hc, Nat.add_assoc, maskWires, List.foldl_cons] using h


lemma base_ne_seven {w : BitVec 7} (hw : w ∈ base) : w ≠ 7 := by
  intro he
  have hz := base_clean_zero hw (by rw [he]; decide)
  exact (by decide : (0 : BitVec 7) ≠ 7) (hz.symm.trans he)

lemma span1_ne_seven {f w : BitVec 7} (hf : f ∈ first) (hw : span1 f w) : w ≠ 7 := by
  obtain ⟨a, ha, u, rfl⟩ := hw
  cases u with
  | false => exact base_ne_seven ha
  | true =>
    apply union_ne_seven ?_ (first_clean_small hf)
    intro hc
    rw [base_clean_zero ha hc]
    decide

lemma span2_ne_seven {f g w : BitVec 7} (hf : f ∈ first) (hg : Second f g)
    (hw : span2 f g w) : w ≠ 7 := by
  obtain ⟨a, ha, b, hb, u, v, rfl⟩ := hg
  obtain ⟨c, hc, p, q, rfl⟩ := hw
  have h := no_output_two_ands hf ha hb hc u v p q
  cases p <;> cases q <;> simpa [opt, or0, zeroOr, BitVec.or_assoc] using h

lemma phase_ne_seven {k : ℕ} {ws : List (BitVec 7)} (hp : Phase k ws)
    {w : BitVec 7} (hw : w ∈ ws) : w ≠ 7 := by
  cases k with
  | zero => exact base_ne_seven (hp w hw)
  | succ k => cases k with
    | zero =>
      obtain ⟨f, hf, hs⟩ := hp
      exact span1_ne_seven hf (hs w hw)
    | succ k => cases k with
      | zero =>
        obtain ⟨f, hf, g, hg, hs⟩ := hp
        exact span2_ne_seven hf hg (hs w hw)
      | succ k => exact hp.elim

def circuitMask (C : Circuit) (xs : List (BitVec 7)) : BitVec 7 :=
  (maskWires C.gates xs).getD C.output 0

lemma circuit_mask_ne_seven (C : Circuit) (hC : Monotone2 C) (xs : List (BitVec 7))
    (hxs : ∀ x ∈ xs, x ∈ base) (hcount : andCount C.gates ≤ 2) : circuitMask C xs ≠ 7 := by
  have hp : Phase 0 (0 :: 127 :: xs) := by
    intro w hw
    rcases List.mem_cons.mp hw with rfl | hw
    · exact zero_mem_base
    rcases List.mem_cons.mp hw with rfl | hw
    · decide
    · exact hxs w hw
  have h := maskWires_phase C.gates hC 0 xs hp (by simpa using hcount)
  exact phase_ne_seven h (mask_getD_mem _ _)

def row (r : Fin 7) (w : BitVec 7) : Bool := w[r.val]

lemma row_zero (r : Fin 7) : row r 0 = false := zero_bit r.val r.isLt

lemma row127 (r : Fin 7) : row r 127 = true := by
  change (BitVec.allOnes 7)[r.val] = true
  exact BitVec.getElem_allOnes _ _

lemma row_and (r : Fin 7) (a b : BitVec 7) : row r (a &&& b) = (row r a && row r b) :=
  BitVec.getElem_and r.isLt

lemma row_or (r : Fin 7) (a b : BitVec 7) : row r (a ||| b) = (row r a || row r b) :=
  BitVec.getElem_or r.isLt

lemma row_getD (r : Fin 7) (ws : List (BitVec 7)) (i : ℕ) :
    row r (ws.getD i 0) = (ws.map (row r)).getD i false := by
  have h := List.getD_map ws 0 (row r) (n := i)
  rw [row_zero] at h
  exact h.symm

lemma fold_and_row (r : Fin 7) (ws : List (BitVec 7)) :
    row r (ws.foldr (· &&& ·) 127) = (ws.map (row r)).all id := by
  induction ws with
  | nil => exact row127 r
  | cons w ws ih =>
    simp only [List.foldr_cons, row_and, List.map_cons, List.all_cons, id_eq]
    rw [ih]

lemma fold_or_row (r : Fin 7) (ws : List (BitVec 7)) :
    row r (ws.foldr (· ||| ·) 0) = (ws.map (row r)).any id := by
  induction ws with
  | nil => exact row_zero r
  | cons w ws ih =>
    simp only [List.foldr_cons, row_or, List.map_cons, List.any_cons, id_eq]
    rw [ih]

lemma maskGate_row (r : Fin 7) (ws : List (BitVec 7)) (g : Gate)
    (hop : g.op = .and ∨ g.op = .or) :
    row r (maskGate ws g) =
      g.op.eval (g.inputs.map fun i => (ws.map (row r)).getD i false) := by
  rcases hop with hop | hop
  · simp only [maskGate, hop, fold_and_row, GateOp.eval, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact row_getD r ws i
  · simp only [maskGate, hop, fold_or_row, GateOp.eval, List.map_map]
    congr 1
    apply List.map_congr_left
    intro i _
    exact row_getD r ws i

lemma maskWires_rows (r : Fin 7) (gs : List Gate)
    (hgs : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) (xs : List (BitVec 7)) :
    (maskWires gs xs).map (row r) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (xs.map (row r)) := by
  induction gs generalizing xs with
  | nil => rfl
  | cons g gs ih =>
    change (maskWires gs (xs ++ [maskGate xs g])).map (row r) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
        ((xs.map (row r)) ++ [g.op.eval (g.inputs.map fun i => (xs.map (row r)).getD i false)])
    rw [ih (fun a ha => hgs a (List.mem_cons_of_mem g ha))]
    simp only [List.map_append, List.map_singleton, maskGate_row r xs g (hgs g List.mem_cons_self)]

lemma circuit_mask_rows (C : Circuit) (hC : Monotone2 C) (xs : List (BitVec 7)) (r : Fin 7) :
    C.eval (xs.map (row r)) = row r (circuitMask C xs) := by
  have hg : ∀ g ∈ C.gates, g.op = .and ∨ g.op = .or := fun g hg => (hC g hg).1
  change (C.gates.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
    (xs.map (row r))).getD C.output false = row r ((maskWires C.gates xs).getD C.output 0)
  rw [← maskWires_rows r C.gates hg xs]
  exact (row_getD r _ _).symm

lemma circuit_no_two_ands (C : Circuit) (hC : Monotone2 C) (xs : List (BitVec 7))
    (hxs : ∀ x ∈ xs, x ∈ base) (hcount : andCount C.gates ≤ 2) :
    ¬ ∀ r : Fin 7, C.eval (xs.map (row r)) = row r 7 := by
  intro he
  apply circuit_mask_ne_seven C hC xs hxs hcount
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hr := (circuit_mask_rows C hC xs ⟨i, hi⟩).symm.trans (he ⟨i, hi⟩)
  exact hr

lemma circuit_requires_three_ands (C : Circuit) (hC : Monotone2 C) (xs : List (BitVec 7))
    (hxs : ∀ x ∈ xs, x ∈ base)
    (hcomp : ∀ r : Fin 7, C.eval (xs.map (row r)) = row r 7) :
    3 ≤ andCount C.gates := by
  by_contra h
  have hle : andCount C.gates ≤ 2 := by omega
  exact circuit_no_two_ands C hC xs hxs hle hcomp

end SevenRows.Adapter

namespace FiveGroup.CausalBarrier

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
  [({0}, {1, 4, 5}), ({1}, {2, 6}), ({4}, {3, 9}), ({5}, {7, 8}), (∅, ∅)]

def DirtyEdges : List (Finset (Fin 10)) :=
  [{2, 3}, {3, 8}, {6, 8}, {6, 9}, {2, 7}, {7, 9}]

def UniversalEdge (v : Fin 10) : Finset (Fin 10) :=
  match v.val with
  | 0 => {2, 3}
  | 1 => {3, 8}
  | 2 => {2, 3}
  | 3 => {2, 3}
  | 4 => {6, 8}
  | 5 => {6, 9}
  | 6 => {6, 8}
  | 7 => {2, 7}
  | 8 => {3, 8}
  | _ => {6, 9}

def UniversalBarrier (v : Fin 10) : Finset (Fin 10) := insert v (UniversalEdge v)

lemma universal_edge_valid : ∀ v : Fin 10, UniversalEdge v ∈ DirtyEdges := by decide

lemma all_vertices_separation :
    ∀ (v : Fin 10), ∀ AB ∈ OtherSides,
      Separates (UniversalBarrier v) AB.1 AB.2 ∧
      Separates (UniversalBarrier v) AB.2 AB.1 := by
  intro v
  simp [OtherSides, Separates]
  revert v
  decide

end FiveGroup.CausalBarrier

namespace FiveGroup.ResourceExclusion

open CausalBarrier

abbrev Resource := Finset (Fin 10) × (Finset (Fin 10) → Bool)

def CrossPairs : List (Finset (Fin 10)) :=
  [{2, 3}, {3, 8}, {3, 9}, {2, 6}, {6, 8}, {6, 9}, {2, 7}, {7, 8}, {7, 9}]

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
  w.1 = ∅ ∧ (∀ E ∈ DirtyEdges, w.2 E = true) ∧ w.2 {3, 9} = false

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
  refine ⟨{2, 3}, by simp [DirtyEdges], {2, 3}, ?_, ?_⟩
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
    have ht := hdt {3, 9} (by simp [CrossPairs])
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

end FiveGroup.ResourceExclusion

namespace FiveGroup.IndexSchedule

open ResourceExclusion

def Pool (W : ℕ → Resource) (ids : Finset ℕ) : Multiset Resource := ids.val.map W

def DropZero (W : ℕ → Resource) (i : ℕ) (ids : Finset ℕ) : Finset ℕ :=
  if (W i).1 = ∅ then ids.erase i else ids

def NextIds (W : ℕ → Resource) (a b out : ℕ) (ids : Finset ℕ) : Finset ℕ :=
  insert out (DropZero W b (DropZero W a ids))

def Available (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ) : ℕ → Finset ℕ
  | 0 => Finset.range start
  | t + 1 => NextIds W (A (start + t)) (B (start + t)) (start + t)
      (Available W start A B t)

lemma drop_subset (W : ℕ → Resource) (i : ℕ) (ids : Finset ℕ) :
    DropZero W i ids ⊆ ids := by
  unfold DropZero
  split
  · exact Finset.erase_subset _ _
  · exact Finset.Subset.refl _

lemma mem_drop {W : ℕ → Resource} {i x : ℕ} {ids : Finset ℕ}
    (hx : x ∈ ids) (hkeep : (W x).1 ≠ ∅ ∨ x ≠ i) : x ∈ DropZero W i ids := by
  unfold DropZero
  split_ifs with hi
  · apply Finset.mem_erase.mpr
    refine ⟨?_, hx⟩
    rcases hkeep with hkeep | hkeep
    · intro hxi
      subst x
      exact hkeep hi
    · exact hkeep
  · exact hx

lemma available_bounded (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ)
    (t : ℕ) : ∀ x ∈ Available W start A B t, x < start + t := by
  induction t with
  | zero => simp [Available]
  | succ t ih =>
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · omega
      · have hx' := drop_subset W _ _ (drop_subset W _ _ hx)
        have hb := ih x hx'
        omega

lemma available_complete (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ)
    (t : ℕ) : ∀ x, x < start + t →
      ((W x).1 ≠ ∅ ∨ ∀ j < t, A (start + j) ≠ x ∧ B (start + j) ≠ x) →
      x ∈ Available W start A B t := by
  induction t with
  | zero => simp [Available]
  | succ t ih =>
      intro x hbound hunused
      by_cases hlast : x = start + t
      · subst x
        exact Finset.mem_insert_self _ _
      · have hold : x < start + t := by omega
        have hprev : (W x).1 ≠ ∅ ∨ ∀ j < t,
            A (start + j) ≠ x ∧ B (start + j) ≠ x := by
          rcases hunused with hp | hu
          · exact Or.inl hp
          · exact Or.inr (fun j hj => hu j (by omega))
        have hmem := ih x hold hprev
        apply Finset.mem_insert_of_mem
        apply mem_drop
        · apply mem_drop hmem
          rcases hunused with hp | hu
          · exact Or.inl hp
          · exact Or.inr (Ne.symm (hu t (by omega)).1)
        · rcases hunused with hp | hu
          · exact Or.inl hp
          · exact Or.inr (Ne.symm (hu t (by omega)).2)

def Reads (A B : ℕ → ℕ) (i x : ℕ) : Prop := A i = x ∨ B i = x

def LinearUpTo (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ i < n, ∀ j < n, ∀ x, (W x).1 = ∅ →
    Reads A B (start + i) x → Reads A B (start + j) x → i = j

lemma source_available {W : ℕ → Resource} {start n t x : ℕ} {A B : ℕ → ℕ}
    (hlin : LinearUpTo W start A B n) (ht : t < n)
    (hx : x < start + t) (hr : Reads A B (start + t) x) :
    x ∈ Available W start A B t := by
  apply available_complete W start A B t x hx
  by_cases hp : (W x).1 = ∅
  · right
    intro j hj
    constructor
    · intro hja
      have heq := hlin t ht j (by omega) x hp hr (Or.inl hja)
      omega
    · intro hjb
      have heq := hlin t ht j (by omega) x hp hr (Or.inr hjb)
      omega
  · exact Or.inl hp

lemma pool_insert {W : ℕ → Resource} {ids : Finset ℕ} {i : ℕ} (hi : i ∉ ids) :
    Pool W (insert i ids) = W i ::ₘ Pool W ids := by
  simp only [Pool, Finset.insert_val_of_notMem hi, Multiset.map_cons]

lemma pool_erase_decomp {W : ℕ → Resource} {ids : Finset ℕ} {i : ℕ} (hi : i ∈ ids) :
    Pool W ids = W i ::ₘ Pool W (ids.erase i) := by
  calc
    Pool W ids = Pool W (insert i (ids.erase i)) := by rw [Finset.insert_erase hi]
    _ = W i ::ₘ Pool W (ids.erase i) := pool_insert (Finset.notMem_erase _ _)

lemma pool_two_decomp {W : ℕ → Resource} {ids : Finset ℕ} {a b : ℕ}
    (ha : a ∈ ids) (hb : b ∈ ids) (hab : a ≠ b) :
    Pool W ids = W a ::ₘ W b ::ₘ Pool W ((ids.erase a).erase b) := by
  rw [pool_erase_decomp ha]
  rw [pool_erase_decomp (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩)]

lemma pool_drop_two {W : ℕ → Resource} {ids : Finset ℕ} {a b : ℕ}
    (ha : a ∈ ids) (hb : b ∈ ids) (hab : a ≠ b) :
    Pool W (DropZero W b (DropZero W a ids)) =
      Keep (W a) + Keep (W b) + Pool W ((ids.erase a).erase b) := by
  classical
  by_cases hza : (W a).1 = ∅ <;> by_cases hzb : (W b).1 = ∅
  · simp [DropZero, Keep, hza, hzb]
  · simp only [DropZero, Keep, hza, hzb, ite_true, ite_false, zero_add]
    exact pool_erase_decomp (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩)
  · simp only [DropZero, Keep, hza, hzb, ite_true, ite_false, add_zero]
    rw [Finset.erase_right_comm]
    exact pool_erase_decomp (Finset.mem_erase.mpr ⟨hab, ha⟩)
  · simp only [DropZero, Keep, hza, hzb, ite_false]
    simpa using pool_two_decomp ha hb hab

lemma index_resource_step {W : ℕ → Resource} {ids : Finset ℕ} {a b out : ℕ}
    (ha : a ∈ ids) (hb : b ∈ ids) (hab : a ≠ b) (hout : out ∉ ids)
    (hg : W out = RJoin (W a) (W b) ∨
      (AllowedSides (W a) (W b) ∧ W out = RMeet (W a) (W b))) :
    ResourceStep (Pool W ids) (Pool W (NextIds W a b out ids)) := by
  left
  refine ⟨W a, W b, W out, Pool W ((ids.erase a).erase b),
    pool_two_decomp ha hb hab, ?_, hg⟩
  have hfresh : out ∉ DropZero W b (DropZero W a ids) := by
    intro h
    exact hout (drop_subset W _ _ (drop_subset W _ _ h))
  rw [NextIds, pool_insert hfresh, pool_drop_two ha hb hab]
  rfl


def ValidUpTo (start : ℕ) (A B : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ t < n, A (start + t) < start + t ∧ B (start + t) < start + t ∧
    A (start + t) ≠ B (start + t)

def CanonicalUpTo (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ t < n,
    W (start + t) = RJoin (W (A (start + t))) (W (B (start + t))) ∨
    (AllowedSides (W (A (start + t))) (W (B (start + t))) ∧
      W (start + t) = RMeet (W (A (start + t))) (W (B (start + t))))

lemma available_step {W : ℕ → Resource} {start n t : ℕ} {A B : ℕ → ℕ}
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo W start A B n) (ht : t < n) :
    ResourceStep (Pool W (Available W start A B t))
      (Pool W (Available W start A B (t + 1))) := by
  obtain ⟨ha, hb, hab⟩ := hv t ht
  have haa := source_available hl ht ha (Or.inl rfl)
  have hba := source_available hl ht hb (Or.inr rfl)
  apply index_resource_step haa hba hab ?_ (hc t ht)
  intro h
  have := available_bounded W start A B t _ h
  omega

lemma program_invariant {W : ℕ → Resource} {start n : ℕ} {A B : ℕ → ℕ}
    (hp : Invariant (Pool W (Finset.range start)))
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo W start A B n) :
    ∀ t ≤ n, Invariant (Pool W (Available W start A B t)) := by
  intro t
  induction t with
  | zero => intro _; exact hp
  | succ t ih =>
      intro ht
      exact invariant_step (ih (by omega)) (available_step hv hl hc (by omega))

lemma pool_mem {W : ℕ → Resource} {ids : Finset ℕ} {i : ℕ} (hi : i ∈ ids) :
    W i ∈ Pool W ids := by
  exact Multiset.mem_map.mpr ⟨i, hi, rfl⟩

lemma canonical_program_exclusion {W : ℕ → Resource} {start n : ℕ} {A B : ℕ → ℕ}
    (hp : Invariant (Pool W (Finset.range start)))
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo W start A B n) :
    ∀ t < n, ¬ Target (W (start + t)) := by
  intro t ht
  have hinv := program_invariant hp hv hl hc (t + 1) (by omega)
  apply invariant_no_target hinv
  apply pool_mem
  exact Finset.mem_insert_self _ _

lemma initial_exceptional {W : ℕ → Resource} {start d : ℕ}
    (hd : d < start) (hz : (W d).1 = ∅)
    (ht : ∀ E ∈ CrossPairs, (W d).2 E = true)
    (ho : ∀ i < start, i ≠ d → Ordinary (W i)) :
    Invariant (Pool W (Finset.range start)) := by
  right
  refine ⟨W d, Pool W ((Finset.range start).erase d),
    pool_erase_decomp (Finset.mem_range.mpr hd), hz, ht, ?_⟩
  intro w hw
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hw
  have hi' : i ∈ (Finset.range start).erase d := hi
  obtain ⟨hid, hir⟩ := Finset.mem_erase.mp hi'
  exact ho i (Finset.mem_range.mp hir) hid

lemma seeded_program_exclusion {W : ℕ → Resource} {start n d : ℕ} {A B : ℕ → ℕ}
    (hd : d < start) (hz : (W d).1 = ∅)
    (ht : ∀ E ∈ CrossPairs, (W d).2 E = true)
    (ho : ∀ i < start, i ≠ d → Ordinary (W i))
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo W start A B n) :
    ∀ t < n, ¬ Target (W (start + t)) :=
  canonical_program_exclusion (initial_exceptional hd hz ht ho) hv hl hc


lemma program_any_wire_exclusion {W : ℕ → Resource} {start n : ℕ} {A B : ℕ → ℕ}
    (hp : Invariant (Pool W (Finset.range start)))
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo W start A B n) :
    ∀ i < start + n, ¬ Target (W i) := by
  intro i hi
  by_cases hold : i < start
  · exact invariant_no_target hp (pool_mem (Finset.mem_range.mpr hold))
  · have ht : i - start < n := by omega
    have heq : start + (i - start) = i := by omega
    simpa only [heq] using canonical_program_exclusion hp hv hl hc (i - start) ht

lemma ordinary_prefix {W : ℕ → Resource} {start n : ℕ} {A B : ℕ → ℕ}
    (hp : ∀ i < start, Ordinary (W i))
    (hv : ValidUpTo start A B n) (hc : CanonicalUpTo W start A B n) :
    ∀ i < start + n, Ordinary (W i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
      intro hi
      by_cases hold : i < start
      · exact hp i hold
      · have ht : i - start < n := by omega
        have heq : start + (i - start) = i := by omega
        obtain ⟨ha, hb, _⟩ := hv (i - start) ht
        rw [heq] at ha hb
        have hca := hc (i - start) ht
        rw [heq] at hca
        exact ordinary_result (ih _ ha (by omega)) (ih _ hb (by omega)) hca

end FiveGroup.IndexSchedule

namespace S45.CausalBarrier

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
  [({0}, {1, 4, 5}), ({1}, {6}), ({2}, {1, 3, 7}), ({3}, {4, 8}), ({7}, {5, 9}), (∅, ∅)]

def DirtyEdges : List (Finset (Fin 10)) :=
  [{4, 9}, {5, 8}, {6, 8}, {6, 9}]

def UniversalEdge (v : Fin 10) : Finset (Fin 10) :=
  match v.val with
  | 0 => {6, 8}
  | 1 => {4, 9}
  | 2 => {4, 9}
  | 3 => {6, 9}
  | 4 => {4, 9}
  | 5 => {5, 8}
  | 6 => {6, 8}
  | 7 => {6, 8}
  | 8 => {5, 8}
  | _ => {4, 9}

def UniversalBarrier (v : Fin 10) : Finset (Fin 10) := insert v (UniversalEdge v)

lemma universal_edge_valid : ∀ v : Fin 10, UniversalEdge v ∈ DirtyEdges := by decide

lemma all_vertices_separation :
    ∀ (v : Fin 10), ∀ AB ∈ OtherSides,
      Separates (UniversalBarrier v) AB.1 AB.2 ∧
      Separates (UniversalBarrier v) AB.2 AB.1 := by
  intro v
  simp [OtherSides, Separates]
  revert v
  decide

end S45.CausalBarrier

namespace S45.ResourceExclusion

open CausalBarrier

abbrev Resource := Finset (Fin 10) × (Finset (Fin 10) → Bool)

def CrossPairs : List (Finset (Fin 10)) :=
  [{4, 8}, {4, 9}, {5, 8}, {5, 9}, {6, 8}, {6, 9}]

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
  w.1 = ∅ ∧ (∀ E ∈ DirtyEdges, w.2 E = true) ∧ w.2 {4, 8} = false

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
  refine ⟨{4, 9}, by simp [DirtyEdges], {4, 9}, ?_, ?_⟩
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
    have ht := hdt {4, 8} (by simp [CrossPairs])
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

end S45.ResourceExclusion

namespace S45.IndexSchedule

open ResourceExclusion

def Pool (W : ℕ → Resource) (ids : Finset ℕ) : Multiset Resource := ids.val.map W

def DropZero (W : ℕ → Resource) (i : ℕ) (ids : Finset ℕ) : Finset ℕ :=
  if (W i).1 = ∅ then ids.erase i else ids

def NextIds (W : ℕ → Resource) (a b out : ℕ) (ids : Finset ℕ) : Finset ℕ :=
  insert out (DropZero W b (DropZero W a ids))

def Available (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ) : ℕ → Finset ℕ
  | 0 => Finset.range start
  | t + 1 => NextIds W (A (start + t)) (B (start + t)) (start + t)
      (Available W start A B t)

lemma drop_subset (W : ℕ → Resource) (i : ℕ) (ids : Finset ℕ) :
    DropZero W i ids ⊆ ids := by
  unfold DropZero
  split
  · exact Finset.erase_subset _ _
  · exact Finset.Subset.refl _

lemma mem_drop {W : ℕ → Resource} {i x : ℕ} {ids : Finset ℕ}
    (hx : x ∈ ids) (hkeep : (W x).1 ≠ ∅ ∨ x ≠ i) : x ∈ DropZero W i ids := by
  unfold DropZero
  split_ifs with hi
  · apply Finset.mem_erase.mpr
    refine ⟨?_, hx⟩
    rcases hkeep with hkeep | hkeep
    · intro hxi
      subst x
      exact hkeep hi
    · exact hkeep
  · exact hx

lemma available_bounded (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ)
    (t : ℕ) : ∀ x ∈ Available W start A B t, x < start + t := by
  induction t with
  | zero => simp [Available]
  | succ t ih =>
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · omega
      · have hx' := drop_subset W _ _ (drop_subset W _ _ hx)
        have hb := ih x hx'
        omega

lemma available_complete (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ)
    (t : ℕ) : ∀ x, x < start + t →
      ((W x).1 ≠ ∅ ∨ ∀ j < t, A (start + j) ≠ x ∧ B (start + j) ≠ x) →
      x ∈ Available W start A B t := by
  induction t with
  | zero => simp [Available]
  | succ t ih =>
      intro x hbound hunused
      by_cases hlast : x = start + t
      · subst x
        exact Finset.mem_insert_self _ _
      · have hold : x < start + t := by omega
        have hprev : (W x).1 ≠ ∅ ∨ ∀ j < t,
            A (start + j) ≠ x ∧ B (start + j) ≠ x := by
          rcases hunused with hp | hu
          · exact Or.inl hp
          · exact Or.inr (fun j hj => hu j (by omega))
        have hmem := ih x hold hprev
        apply Finset.mem_insert_of_mem
        apply mem_drop
        · apply mem_drop hmem
          rcases hunused with hp | hu
          · exact Or.inl hp
          · exact Or.inr (Ne.symm (hu t (by omega)).1)
        · rcases hunused with hp | hu
          · exact Or.inl hp
          · exact Or.inr (Ne.symm (hu t (by omega)).2)

def Reads (A B : ℕ → ℕ) (i x : ℕ) : Prop := A i = x ∨ B i = x

def LinearUpTo (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ i < n, ∀ j < n, ∀ x, (W x).1 = ∅ →
    Reads A B (start + i) x → Reads A B (start + j) x → i = j

lemma source_available {W : ℕ → Resource} {start n t x : ℕ} {A B : ℕ → ℕ}
    (hlin : LinearUpTo W start A B n) (ht : t < n)
    (hx : x < start + t) (hr : Reads A B (start + t) x) :
    x ∈ Available W start A B t := by
  apply available_complete W start A B t x hx
  by_cases hp : (W x).1 = ∅
  · right
    intro j hj
    constructor
    · intro hja
      have heq := hlin t ht j (by omega) x hp hr (Or.inl hja)
      omega
    · intro hjb
      have heq := hlin t ht j (by omega) x hp hr (Or.inr hjb)
      omega
  · exact Or.inl hp

lemma pool_insert {W : ℕ → Resource} {ids : Finset ℕ} {i : ℕ} (hi : i ∉ ids) :
    Pool W (insert i ids) = W i ::ₘ Pool W ids := by
  simp only [Pool, Finset.insert_val_of_notMem hi, Multiset.map_cons]

lemma pool_erase_decomp {W : ℕ → Resource} {ids : Finset ℕ} {i : ℕ} (hi : i ∈ ids) :
    Pool W ids = W i ::ₘ Pool W (ids.erase i) := by
  calc
    Pool W ids = Pool W (insert i (ids.erase i)) := by rw [Finset.insert_erase hi]
    _ = W i ::ₘ Pool W (ids.erase i) := pool_insert (Finset.notMem_erase _ _)

lemma pool_two_decomp {W : ℕ → Resource} {ids : Finset ℕ} {a b : ℕ}
    (ha : a ∈ ids) (hb : b ∈ ids) (hab : a ≠ b) :
    Pool W ids = W a ::ₘ W b ::ₘ Pool W ((ids.erase a).erase b) := by
  rw [pool_erase_decomp ha]
  rw [pool_erase_decomp (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩)]

lemma pool_drop_two {W : ℕ → Resource} {ids : Finset ℕ} {a b : ℕ}
    (ha : a ∈ ids) (hb : b ∈ ids) (hab : a ≠ b) :
    Pool W (DropZero W b (DropZero W a ids)) =
      Keep (W a) + Keep (W b) + Pool W ((ids.erase a).erase b) := by
  classical
  by_cases hza : (W a).1 = ∅ <;> by_cases hzb : (W b).1 = ∅
  · simp [DropZero, Keep, hza, hzb]
  · simp only [DropZero, Keep, hza, hzb, ite_true, ite_false, zero_add]
    exact pool_erase_decomp (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩)
  · simp only [DropZero, Keep, hza, hzb, ite_true, ite_false, add_zero]
    rw [Finset.erase_right_comm]
    exact pool_erase_decomp (Finset.mem_erase.mpr ⟨hab, ha⟩)
  · simp only [DropZero, Keep, hza, hzb, ite_false]
    simpa using pool_two_decomp ha hb hab

lemma index_resource_step {W : ℕ → Resource} {ids : Finset ℕ} {a b out : ℕ}
    (ha : a ∈ ids) (hb : b ∈ ids) (hab : a ≠ b) (hout : out ∉ ids)
    (hg : W out = RJoin (W a) (W b) ∨
      (AllowedSides (W a) (W b) ∧ W out = RMeet (W a) (W b))) :
    ResourceStep (Pool W ids) (Pool W (NextIds W a b out ids)) := by
  left
  refine ⟨W a, W b, W out, Pool W ((ids.erase a).erase b),
    pool_two_decomp ha hb hab, ?_, hg⟩
  have hfresh : out ∉ DropZero W b (DropZero W a ids) := by
    intro h
    exact hout (drop_subset W _ _ (drop_subset W _ _ h))
  rw [NextIds, pool_insert hfresh, pool_drop_two ha hb hab]
  rfl


def ValidUpTo (start : ℕ) (A B : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ t < n, A (start + t) < start + t ∧ B (start + t) < start + t ∧
    A (start + t) ≠ B (start + t)

def CanonicalUpTo (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ t < n,
    W (start + t) = RJoin (W (A (start + t))) (W (B (start + t))) ∨
    (AllowedSides (W (A (start + t))) (W (B (start + t))) ∧
      W (start + t) = RMeet (W (A (start + t))) (W (B (start + t))))

lemma available_step {W : ℕ → Resource} {start n t : ℕ} {A B : ℕ → ℕ}
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo W start A B n) (ht : t < n) :
    ResourceStep (Pool W (Available W start A B t))
      (Pool W (Available W start A B (t + 1))) := by
  obtain ⟨ha, hb, hab⟩ := hv t ht
  have haa := source_available hl ht ha (Or.inl rfl)
  have hba := source_available hl ht hb (Or.inr rfl)
  apply index_resource_step haa hba hab ?_ (hc t ht)
  intro h
  have := available_bounded W start A B t _ h
  omega

lemma program_invariant {W : ℕ → Resource} {start n : ℕ} {A B : ℕ → ℕ}
    (hp : Invariant (Pool W (Finset.range start)))
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo W start A B n) :
    ∀ t ≤ n, Invariant (Pool W (Available W start A B t)) := by
  intro t
  induction t with
  | zero => intro _; exact hp
  | succ t ih =>
      intro ht
      exact invariant_step (ih (by omega)) (available_step hv hl hc (by omega))

lemma pool_mem {W : ℕ → Resource} {ids : Finset ℕ} {i : ℕ} (hi : i ∈ ids) :
    W i ∈ Pool W ids := by
  exact Multiset.mem_map.mpr ⟨i, hi, rfl⟩

lemma canonical_program_exclusion {W : ℕ → Resource} {start n : ℕ} {A B : ℕ → ℕ}
    (hp : Invariant (Pool W (Finset.range start)))
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo W start A B n) :
    ∀ t < n, ¬ Target (W (start + t)) := by
  intro t ht
  have hinv := program_invariant hp hv hl hc (t + 1) (by omega)
  apply invariant_no_target hinv
  apply pool_mem
  exact Finset.mem_insert_self _ _

lemma initial_exceptional {W : ℕ → Resource} {start d : ℕ}
    (hd : d < start) (hz : (W d).1 = ∅)
    (ht : ∀ E ∈ CrossPairs, (W d).2 E = true)
    (ho : ∀ i < start, i ≠ d → Ordinary (W i)) :
    Invariant (Pool W (Finset.range start)) := by
  right
  refine ⟨W d, Pool W ((Finset.range start).erase d),
    pool_erase_decomp (Finset.mem_range.mpr hd), hz, ht, ?_⟩
  intro w hw
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hw
  have hi' : i ∈ (Finset.range start).erase d := hi
  obtain ⟨hid, hir⟩ := Finset.mem_erase.mp hi'
  exact ho i (Finset.mem_range.mp hir) hid

lemma seeded_program_exclusion {W : ℕ → Resource} {start n d : ℕ} {A B : ℕ → ℕ}
    (hd : d < start) (hz : (W d).1 = ∅)
    (ht : ∀ E ∈ CrossPairs, (W d).2 E = true)
    (ho : ∀ i < start, i ≠ d → Ordinary (W i))
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo W start A B n) :
    ∀ t < n, ¬ Target (W (start + t)) :=
  canonical_program_exclusion (initial_exceptional hd hz ht ho) hv hl hc


lemma program_any_wire_exclusion {W : ℕ → Resource} {start n : ℕ} {A B : ℕ → ℕ}
    (hp : Invariant (Pool W (Finset.range start)))
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo W start A B n) :
    ∀ i < start + n, ¬ Target (W i) := by
  intro i hi
  by_cases hold : i < start
  · exact invariant_no_target hp (pool_mem (Finset.mem_range.mpr hold))
  · have ht : i - start < n := by omega
    have heq : start + (i - start) = i := by omega
    simpa only [heq] using canonical_program_exclusion hp hv hl hc (i - start) ht

lemma ordinary_prefix {W : ℕ → Resource} {start n : ℕ} {A B : ℕ → ℕ}
    (hp : ∀ i < start, Ordinary (W i))
    (hv : ValidUpTo start A B n) (hc : CanonicalUpTo W start A B n) :
    ∀ i < start + n, Ordinary (W i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
      intro hi
      by_cases hold : i < start
      · exact hp i hold
      · have ht : i - start < n := by omega
        have heq : start + (i - start) = i := by omega
        obtain ⟨ha, hb, _⟩ := hv (i - start) ht
        rw [heq] at ha hb
        have hca := hc (i - start) ht
        rw [heq] at hca
        exact ordinary_result (ih _ ha (by omega)) (ih _ hb (by omega)) hca

end S45.IndexSchedule

namespace DAGBridge.DagTools

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gop : Bool → Bool → Bool → Bool
  | true, a, b => a && b
  | false, a, b => a || b

lemma gop_true (a b : Bool) : gop true a b = (a && b) := rfl

lemma gop_false (a b : Bool) : gop false a b = (a || b) := rfl

abbrev Dag := List (Bool × ℕ × ℕ)

def tag (D : Dag) (j : ℕ) : Bool := (D.getD j (false, 0, 0)).1

def opA (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.1

def opB (D : Dag) (j : ℕ) : ℕ := (D.getD j (false, 0, 0)).2.2

def wstep (w : List Bool) (g : Bool × ℕ × ℕ) : List Bool :=
  w ++ [gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false)]

def wl (D : Dag) (w : List Bool) : List Bool := D.foldl wstep w

def val (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) : Bool :=
  (wl D (List.ofFn x)).getD w false

def Strict (n : ℕ) (D : Dag) : Prop :=
  ∀ j, j < D.length → opA D j < n + j ∧ opB D j < n + j ∧ opA D j ≠ opB D j

def readers (D : Dag) (w : ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => opA D j = w ∨ opB D j = w)

def fanout (D : Dag) (w : ℕ) : ℕ := (readers D w).card

def Live (n : ℕ) (D : Dag) : Prop := ∀ w, w + 1 < n + D.length → 1 ≤ fanout D w

def StrictLive (n : ℕ) (D : Dag) : Prop := Strict n D ∧ Live n D ∧ D ≠ []

def outW (n : ℕ) (D : Dag) : ℕ := n + D.length - 1

def single {n : ℕ} (v : Fin n) : Fin n → Bool := fun i => decide (i = v)

def supp (n : ℕ) (D : Dag) (w : ℕ) : Finset (Fin n) :=
  Finset.univ.filter (fun v => val D (single v) w = true)

def surplusOn (D : Dag) (K : Finset ℕ) : ℕ := ∑ w ∈ K, (fanout D w - 1)

def inner (n : ℕ) (D : Dag) : Finset ℕ := Finset.range (n + D.length - 1)

def totalSurplus (n : ℕ) (D : Dag) : ℕ := surplusOn D (inner n D)

def Bplus (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => (supp n D w).Nonempty))

def Bzero (n : ℕ) (D : Dag) : ℕ :=
  surplusOn D ((inner n D).filter (fun w => ¬ (supp n D w).Nonempty))

def branchW (n : ℕ) (D : Dag) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => 2 ≤ fanout D w)

def eligSet (n : ℕ) (D : Dag) : Finset (Fin n) := (branchW n D).biUnion (supp n D)

def ineligSet (n : ℕ) (D : Dag) : Finset (Fin n) := Finset.univ \ eligSet n D

def units (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (inner n D).sigma (fun w => Finset.range (fanout D w - 1))

def unitsPlus (n : ℕ) (D : Dag) : Finset (Σ _ : ℕ, ℕ) :=
  (units n D).filter (fun u => (supp n D u.1).Nonempty)

def arcs (D : Dag) : Finset (ℕ × Bool) := Finset.range D.length ×ˢ Finset.univ

def src (D : Dag) (e : ℕ × Bool) : ℕ := if e.2 = true then opB D e.1 else opA D e.1

def exitArcs (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset (ℕ × Bool) :=
  (arcs D).filter (fun e => src D e ∈ K ∧ n + e.1 ∉ K)

def merges (n : ℕ) (D : Dag) (K : Finset ℕ) : Finset ℕ :=
  (Finset.range D.length).filter (fun j => n + j ∈ K ∧ opA D j ∈ K ∧ opB D j ∈ K)

def sources (n : ℕ) (K : Finset ℕ) : Finset ℕ := K.filter (fun w => w < n)

def carrierT (n : ℕ) (D : Dag) (T : Finset (Fin n)) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => (supp n D w ∩ T).Nonempty)

def carrierDiff (n : ℕ) (D : Dag) (x y : Fin n) : Finset ℕ :=
  (Finset.range (n + D.length)).filter (fun w => x ∈ supp n D w ∧ y ∉ supp n D w)

def PureBranch (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Prop :=
  ∀ v ∈ eligSet n D, 2 ≤ fanout D (b v) ∧ supp n D (b v) = {v}

def reservedUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  (eligSet n D).image (fun v => (⟨b v, 0⟩ : Σ _ : ℕ, ℕ))

def residualUnits (n : ℕ) (D : Dag) (b : Fin n → ℕ) : Finset (Σ _ : ℕ, ℕ) :=
  unitsPlus n D \ reservedUnits n D b

lemma tag_eq (D : Dag) (j : ℕ) (h : j < D.length) : tag D j = (D[j]).1 := by
  simp [tag, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma opA_eq (D : Dag) (j : ℕ) (h : j < D.length) : opA D j = (D[j]).2.1 := by
  simp [opA, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma opB_eq (D : Dag) (j : ℕ) (h : j < D.length) : opB D j = (D[j]).2.2 := by
  simp [opB, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

lemma wl_cons (g : Bool × ℕ × ℕ) (D : Dag) (w : List Bool) :
    wl (g :: D) w = wl D (wstep w g) := rfl

lemma wl_append (D E : Dag) (w : List Bool) : wl (D ++ E) w = wl E (wl D w) := by
  simp [wl, List.foldl_append]

lemma wstep_length (w : List Bool) (g : Bool × ℕ × ℕ) : (wstep w g).length = w.length + 1 := by
  simp [wstep]

lemma wl_length (D : Dag) : ∀ w : List Bool, (wl D w).length = w.length + D.length := by
  induction D with
  | nil => intro w; simp [wl]
  | cons g D ih => intro w; rw [wl_cons, ih, wstep_length]; simp; omega

lemma wstep_getD_lt (w : List Bool) (g : Bool × ℕ × ℕ) (i : ℕ) (h : i < w.length) :
    (wstep w g).getD i false = w.getD i false := by
  simp [wstep, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

lemma wl_getD_lt (D : Dag) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (wl D w).getD i false = w.getD i false := by
  induction D with
  | nil => intro w i _; rfl
  | cons g D ih =>
    intro w i h
    rw [wl_cons, ih _ _ (by rw [wstep_length]; omega), wstep_getD_lt _ _ _ h]

lemma getD_ge (w : List Bool) (i : ℕ) (h : w.length ≤ i) : w.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

lemma wstep_getD_last (w : List Bool) (g : Bool × ℕ × ℕ) :
    (wstep w g).getD w.length false = gop g.1 (w.getD g.2.1 false) (w.getD g.2.2 false) := by
  simp [wstep, List.getD_eq_getElem?_getD]

lemma wl_getD_gate (D : Dag) (w : List Bool) (j : ℕ) (hj : j < D.length) :
    (wl D w).getD (w.length + j) false =
      gop (tag D j) ((wl (D.take j) w).getD (opA D j) false)
        ((wl (D.take j) w).getD (opB D j) false) := by
  have hsplit : D = D.take j ++ D[j] :: D.drop (j + 1) := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  rw [tag_eq D j hj, opA_eq D j hj, opB_eq D j hj]
  conv_lhs => rw [hsplit, wl_append, wl_cons]
  rw [wl_getD_lt _ _ _ (by rw [wstep_length, hlen]; omega), ← hlen, wstep_getD_last]

lemma wl_take_getD (D : Dag) (w : List Bool) (j i : ℕ) (hi : i < w.length + j)
    (hj : j ≤ D.length) :
    (wl (D.take j) w).getD i false = (wl D w).getD i false := by
  have hsplit : D = D.take j ++ D.drop j := by simp
  have hlen : (wl (D.take j) w).length = w.length + j := by
    rw [wl_length, List.length_take]; omega
  conv_rhs => rw [hsplit, wl_append]
  rw [wl_getD_lt (D.drop j) (wl (D.take j) w) i (by rw [hlen]; exact hi)]

lemma val_input (D : Dag) {n : ℕ} (x : Fin n → Bool) (i : ℕ) (h : i < n) :
    val D x i = x ⟨i, h⟩ := by
  unfold val
  rw [wl_getD_lt _ _ _ (by simpa using h)]
  simp [List.getD_eq_getElem?_getD, h]

lemma val_ge (D : Dag) {n : ℕ} (x : Fin n → Bool) (w : ℕ) (h : n + D.length ≤ w) :
    val D x w = false := by
  unfold val
  exact getD_ge _ _ (by rw [wl_length]; simpa using h)

lemma val_take (D : Dag) {n : ℕ} (x : Fin n → Bool) (k w : ℕ) (hw : w < n + k)
    (hk : k ≤ D.length) : val (D.take k) x w = val D x w := by
  unfold val
  exact wl_take_getD D _ k w (by simpa using hw) hk

lemma val_gate {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (j : ℕ)
    (hj : j < D.length) :
    val D x (n + j) = gop (tag D j) (val D x (opA D j)) (val D x (opB D j)) := by
  obtain ⟨ha, hb, -⟩ := hS j hj
  have h := wl_getD_gate D (List.ofFn x) j hj
  simp only [List.length_ofFn] at h
  unfold val
  rw [h, wl_take_getD D _ j _ (by simpa using ha) hj.le,
    wl_take_getD D _ j _ (by simpa using hb) hj.le]

lemma val_unique {n : ℕ} {D : Dag} (hS : Strict n D) (x : Fin n → Bool) (f : ℕ → Bool)
    (hin : ∀ i (h : i < n), f i = x ⟨i, h⟩)
    (hg : ∀ j, j < D.length → f (n + j) = gop (tag D j) (f (opA D j)) (f (opB D j))) :
    ∀ w, w < n + D.length → val D x w = f w := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hn : w < n
    · rw [val_input D x w hn, hin w hn]
    · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
      have hj : j < D.length := by omega
      obtain ⟨ha, hb, -⟩ := hS j hj
      rw [val_gate hS x j hj, hg j hj, ih _ ha (by omega), ih _ hb (by omega)]


variable {n : ℕ} {D : Dag}

lemma mem_supp {v : Fin n} {w : ℕ} : v ∈ supp n D w ↔ val D (single v) w = true := by
  simp [supp]

lemma val_mono (hS : Strict n D) (x y : Fin n → Bool) (hxy : ∀ i, x i = true → y i = true)
    (w : ℕ) : val D x w = true → val D y w = true := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases hn : w < n
    · rw [val_input D x w hn, val_input D y w hn]; exact hxy _
    · by_cases hw : w < n + D.length
      · obtain ⟨j, rfl⟩ : ∃ j, w = n + j := ⟨w - n, by omega⟩
        have hj : j < D.length := by omega
        obtain ⟨ha, hb, -⟩ := hS j hj
        rw [val_gate hS x j hj, val_gate hS y j hj]
        have h1 := ih _ ha
        have h2 := ih _ hb
        cases tag D j <;>
          simp only [gop_true, gop_false, Bool.and_eq_true, Bool.or_eq_true] <;> tauto
      · rw [val_ge D x w (by omega)]; simp

lemma supp_input (D : Dag) (i : Fin n) : supp n D i.val = {i} := by
  ext v
  rw [mem_supp, val_input D (single v) i.val i.isLt]
  simp [single, eq_comm]

lemma supp_ge (D : Dag) (w : ℕ) (h : n + D.length ≤ w) : supp n D w = ∅ := by
  ext v
  simp [mem_supp, val_ge D (single v) w h]

lemma supp_gate (hS : Strict n D) (j : ℕ) (hj : j < D.length) :
    supp n D (n + j) = if tag D j = true then supp n D (opA D j) ∩ supp n D (opB D j)
      else supp n D (opA D j) ∪ supp n D (opB D j) := by
  ext v
  rw [mem_supp, val_gate hS _ j hj]
  cases tag D j <;> simp [mem_supp, gop]

end DAGBridge.DagTools

namespace FiveGroup.DAGBridge

open PEqualNP.Outside.L_meta_2590.DAGBridge.DagTools
open ResourceExclusion IndexSchedule CausalBarrier

def DagResource (D : Dag) (w : ℕ) : Resource :=
  (supp 10 D w, fun E => val D (fun v => decide (v ∈ E)) w)

lemma zero_reader_unique {D : Dag} (hS : Strict 10 D) (hz : Bzero 10 D = 0)
    {j k w : ℕ} (hj : j < D.length) (hk : k < D.length)
    (he : supp 10 D w = ∅)
    (hrj : opA D j = w ∨ opB D j = w)
    (hrk : opA D k = w ∨ opB D k = w) : j = k := by
  have hw : w < 10 + j := by
    obtain ⟨ha, hb, _⟩ := hS j hj
    rcases hrj with h | h <;> omega
  have hinner : w ∈ (inner 10 D).filter (fun u => ¬ (supp 10 D u).Nonempty) := by
    apply Finset.mem_filter.mpr
    constructor
    · simp only [inner, Finset.mem_range]
      omega
    · simp [he]
  have hsum : fanout D w - 1 ≤ Bzero 10 D := by
    unfold Bzero surplusOn
    exact Finset.single_le_sum (f := fun u => fanout D u - 1) (fun _ _ => Nat.zero_le _) hinner
  have hcard : (readers D w).card ≤ 1 := by
    change fanout D w ≤ 1
    omega
  apply Finset.card_le_one.mp hcard j ?_ k ?_
  · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hrj⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hrk⟩

lemma input_ordinary (D : Dag) {i : ℕ} (hi : i < 10) : Ordinary (DagResource D i) := by
  intro E _ ht
  change val D (fun v => decide (v ∈ E)) i = true at ht
  rw [val_input D _ i hi] at ht
  have hm : (⟨i, hi⟩ : Fin 10) ∈ E := of_decide_eq_true ht
  refine ⟨⟨i, hi⟩, Finset.mem_inter.mpr ⟨?_, hm⟩⟩
  change (⟨i, hi⟩ : Fin 10) ∈ supp 10 D i
  rw [supp_input D ⟨i, hi⟩]
  simp

lemma resource_gate {D : Dag} (hS : Strict 10 D) {j : ℕ} (hj : j < D.length) :
    DagResource D (10 + j) =
      if tag D j = true then RMeet (DagResource D (opA D j)) (DagResource D (opB D j))
      else RJoin (DagResource D (opA D j)) (DagResource D (opB D j)) := by
  cases ht : tag D j
  · simp only [Bool.false_eq_true, ite_false]
    apply Prod.ext
    · exact (supp_gate hS j hj).trans (by simp [ht, RJoin, DagResource])
    · funext E
      exact (val_gate hS (fun v => decide (v ∈ E)) j hj).trans (by simp [ht, gop, RJoin, DagResource])
  · simp only [ite_true]
    apply Prod.ext
    · exact (supp_gate hS j hj).trans (by simp [ht, RMeet, DagResource])
    · funext E
      exact (val_gate hS (fun v => decide (v ∈ E)) j hj).trans (by simp [ht, gop, RMeet, DagResource])

lemma support_hit_true {D : Dag} (hS : Strict 10 D) {w : ℕ} {E : Finset (Fin 10)}
    (hh : (supp 10 D w ∩ E).Nonempty) : (DagResource D w).2 E = true := by
  obtain ⟨v, hv⟩ := hh
  obtain ⟨hvs, hvE⟩ := Finset.mem_inter.mp hv
  apply val_mono hS (single v) (fun u => decide (u ∈ E)) ?_ w (mem_supp.mp hvs)
  intro u hu
  have huv : u = v := by simpa [single] using hu
  subst u
  exact decide_eq_true hvE

def DirtyA : Finset (Fin 10) := {3, 6, 7}

def DirtyB : Finset (Fin 10) := {2, 8, 9}

def DirtySides (D : Dag) (g : ℕ) : Prop :=
  (supp 10 D (opA D g) = DirtyA ∧ supp 10 D (opB D g) = DirtyB) ∨
  (supp 10 D (opA D g) = DirtyB ∧ supp 10 D (opB D g) = DirtyA)

lemma cross_hits : ∀ E ∈ CrossPairs,
    (DirtyA ∩ E).Nonempty ∧ (DirtyB ∩ E).Nonempty := by
  simp [CrossPairs, DirtyA, DirtyB]

lemma dirty_seed {D : Dag} (hS : Strict 10 D) {g : ℕ} (hg : g < D.length)
    (ht : tag D g = true) (hs : DirtySides D g) :
    (DagResource D (10 + g)).1 = ∅ ∧
      ∀ E ∈ CrossPairs, (DagResource D (10 + g)).2 E = true := by
  constructor
  · change supp 10 D (10 + g) = ∅
    rw [supp_gate hS g hg, ht]
    simp only [ite_true]
    rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb]
      decide
    · rw [ha, hb]
      decide
  · intro E hE
    change val D (fun v => decide (v ∈ E)) (10 + g) = true
    rw [val_gate hS _ g hg, ht]
    change (DagResource D (opA D g)).2 E && (DagResource D (opB D g)).2 E = true
    have hcross := cross_hits E hE
    rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [support_hit_true hS (by simpa [ha] using hcross.1),
        support_hit_true hS (by simpa [hb] using hcross.2)]
      rfl
    · rw [support_hit_true hS (by simpa [ha] using hcross.2),
        support_hit_true hS (by simpa [hb] using hcross.1)]
      rfl


def Left (D : Dag) (w : ℕ) : ℕ := opA D (w - 10)

def Right (D : Dag) (w : ℕ) : ℕ := opB D (w - 10)

lemma window_valid {D : Dag} (hS : Strict 10 D) {offset count : ℕ}
    (hbound : offset + count ≤ D.length) :
    ValidUpTo (10 + offset) (Left D) (Right D) count := by
  intro t ht
  have hj : offset + t < D.length := by omega
  have hsub : 10 + offset + t - 10 = offset + t := by omega
  obtain ⟨ha, hb, hab⟩ := hS (offset + t) hj
  simp only [Left, Right, hsub]
  exact ⟨by omega, by omega, hab⟩

lemma window_linear {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D = 0)
    {offset count : ℕ} (hbound : offset + count ≤ D.length) :
    LinearUpTo (DagResource D) (10 + offset) (Left D) (Right D) count := by
  intro i hi j hj w he hri hrj
  have his : 10 + offset + i - 10 = offset + i := by omega
  have hjs : 10 + offset + j - 10 = offset + j := by omega
  change supp 10 D w = ∅ at he
  simp only [Reads, Left, Right, his] at hri
  simp only [Reads, Left, Right, hjs] at hrj
  have heq := zero_reader_unique hS hB (by omega : offset + i < D.length)
    (by omega : offset + j < D.length) he hri hrj
  omega

lemma window_canonical {D : Dag} (hS : Strict 10 D) {offset count : ℕ}
    (hbound : offset + count ≤ D.length)
    (hsides : ∀ j, offset ≤ j → j < offset + count → tag D j = true →
      AllowedSides (DagResource D (opA D j)) (DagResource D (opB D j))) :
    CanonicalUpTo (DagResource D) (10 + offset) (Left D) (Right D) count := by
  intro t ht
  have hj : offset + t < D.length := by omega
  have hsub : 10 + offset + t - 10 = offset + t := by omega
  have hout : 10 + offset + t = 10 + (offset + t) := by omega
  simp only [Left, Right, hsub]
  rw [hout]
  have hgate := resource_gate hS hj
  cases ht : tag D (offset + t)
  · left
    simpa only [ht, Bool.false_eq_true, ite_false] using hgate
  · right
    exact ⟨hsides _ (by omega) (by omega) ht, by simpa only [ht, ite_true] using hgate⟩

def OtherAndSides (D : Dag) (g : ℕ) : Prop :=
  ∀ j < D.length, j ≠ g → tag D j = true →
    AllowedSides (DagResource D (opA D j)) (DagResource D (opB D j))

lemma before_seed_ordinary {D : Dag} (hS : Strict 10 D) {g : ℕ}
    (hg : g < D.length) (hsides : OtherAndSides D g) :
    ∀ i < 10 + g, Ordinary (DagResource D i) := by
  apply ordinary_prefix (start := 10) (n := g) (A := Left D) (B := Right D)
  · exact fun i hi => input_ordinary D hi
  · exact window_valid (offset := 0) hS (by omega)
  · apply window_canonical (offset := 0) hS (by omega)
    intro j _ hj ht
    exact hsides j (by omega) (by omega) ht

lemma canonical_dag_exclusion {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D = 0)
    {g : ℕ} (hg : g < D.length) (ht : tag D g = true) (hdirty : DirtySides D g)
    (hsides : OtherAndSides D g) :
    ∀ w < 10 + D.length, ¬ Target (DagResource D w) := by
  obtain ⟨hdz, hdt⟩ := dirty_seed hS hg ht hdirty
  have hbefore := before_seed_ordinary hS hg hsides
  have hinit : Invariant (Pool (DagResource D) (Finset.range (10 + (g + 1)))) := by
    apply initial_exceptional (d := 10 + g) (by omega) hdz hdt
    intro i hi hne
    exact hbefore i (by omega)
  have hcount : g + 1 + (D.length - (g + 1)) ≤ D.length := by omega
  have hvalid := window_valid hS hcount
  have hlinear := window_linear hS hB hcount
  have hcanonical : CanonicalUpTo (DagResource D) (10 + (g + 1)) (Left D) (Right D)
      (D.length - (g + 1)) := by
    apply window_canonical hS hcount
    intro j hlo hhi ht
    exact hsides j (by omega) (by omega) ht
  intro w hw
  exact program_any_wire_exclusion hinit hvalid hlinear hcanonical w (by omega)

end FiveGroup.DAGBridge

namespace S45.DAGBridge

open PEqualNP.Outside.L_meta_2590.DAGBridge.DagTools
open ResourceExclusion IndexSchedule CausalBarrier

def DagResource (D : Dag) (w : ℕ) : Resource :=
  (supp 10 D w, fun E => val D (fun v => decide (v ∈ E)) w)

lemma zero_reader_unique {D : Dag} (hS : Strict 10 D) (hz : Bzero 10 D = 0)
    {j k w : ℕ} (hj : j < D.length) (hk : k < D.length)
    (he : supp 10 D w = ∅)
    (hrj : opA D j = w ∨ opB D j = w)
    (hrk : opA D k = w ∨ opB D k = w) : j = k := by
  have hw : w < 10 + j := by
    obtain ⟨ha, hb, _⟩ := hS j hj
    rcases hrj with h | h <;> omega
  have hinner : w ∈ (inner 10 D).filter (fun u => ¬ (supp 10 D u).Nonempty) := by
    apply Finset.mem_filter.mpr
    constructor
    · simp only [inner, Finset.mem_range]
      omega
    · simp [he]
  have hsum : fanout D w - 1 ≤ Bzero 10 D := by
    unfold Bzero surplusOn
    exact Finset.single_le_sum (f := fun u => fanout D u - 1) (fun _ _ => Nat.zero_le _) hinner
  have hcard : (readers D w).card ≤ 1 := by
    change fanout D w ≤ 1
    omega
  apply Finset.card_le_one.mp hcard j ?_ k ?_
  · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hrj⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hrk⟩

lemma input_ordinary (D : Dag) {i : ℕ} (hi : i < 10) : Ordinary (DagResource D i) := by
  intro E _ ht
  change val D (fun v => decide (v ∈ E)) i = true at ht
  rw [val_input D _ i hi] at ht
  have hm : (⟨i, hi⟩ : Fin 10) ∈ E := of_decide_eq_true ht
  refine ⟨⟨i, hi⟩, Finset.mem_inter.mpr ⟨?_, hm⟩⟩
  change (⟨i, hi⟩ : Fin 10) ∈ supp 10 D i
  rw [supp_input D ⟨i, hi⟩]
  simp

lemma resource_gate {D : Dag} (hS : Strict 10 D) {j : ℕ} (hj : j < D.length) :
    DagResource D (10 + j) =
      if tag D j = true then RMeet (DagResource D (opA D j)) (DagResource D (opB D j))
      else RJoin (DagResource D (opA D j)) (DagResource D (opB D j)) := by
  cases ht : tag D j
  · simp only [Bool.false_eq_true, ite_false]
    apply Prod.ext
    · exact (supp_gate hS j hj).trans (by simp [ht, RJoin, DagResource])
    · funext E
      exact (val_gate hS (fun v => decide (v ∈ E)) j hj).trans (by simp [ht, gop, RJoin, DagResource])
  · simp only [ite_true]
    apply Prod.ext
    · exact (supp_gate hS j hj).trans (by simp [ht, RMeet, DagResource])
    · funext E
      exact (val_gate hS (fun v => decide (v ∈ E)) j hj).trans (by simp [ht, gop, RMeet, DagResource])

lemma support_hit_true {D : Dag} (hS : Strict 10 D) {w : ℕ} {E : Finset (Fin 10)}
    (hh : (supp 10 D w ∩ E).Nonempty) : (DagResource D w).2 E = true := by
  obtain ⟨v, hv⟩ := hh
  obtain ⟨hvs, hvE⟩ := Finset.mem_inter.mp hv
  apply val_mono hS (single v) (fun u => decide (u ∈ E)) ?_ w (mem_supp.mp hvs)
  intro u hu
  have huv : u = v := by simpa [single] using hu
  subst u
  exact decide_eq_true hvE

def DirtyA : Finset (Fin 10) := {4, 5, 6}

def DirtyB : Finset (Fin 10) := {8, 9}

def DirtySides (D : Dag) (g : ℕ) : Prop :=
  (supp 10 D (opA D g) = DirtyA ∧ supp 10 D (opB D g) = DirtyB) ∨
  (supp 10 D (opA D g) = DirtyB ∧ supp 10 D (opB D g) = DirtyA)

lemma cross_hits : ∀ E ∈ CrossPairs,
    (DirtyA ∩ E).Nonempty ∧ (DirtyB ∩ E).Nonempty := by
  simp [CrossPairs, DirtyA, DirtyB]

lemma dirty_seed {D : Dag} (hS : Strict 10 D) {g : ℕ} (hg : g < D.length)
    (ht : tag D g = true) (hs : DirtySides D g) :
    (DagResource D (10 + g)).1 = ∅ ∧
      ∀ E ∈ CrossPairs, (DagResource D (10 + g)).2 E = true := by
  constructor
  · change supp 10 D (10 + g) = ∅
    rw [supp_gate hS g hg, ht]
    simp only [ite_true]
    rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb]
      decide
    · rw [ha, hb]
      decide
  · intro E hE
    change val D (fun v => decide (v ∈ E)) (10 + g) = true
    rw [val_gate hS _ g hg, ht]
    change (DagResource D (opA D g)).2 E && (DagResource D (opB D g)).2 E = true
    have hcross := cross_hits E hE
    rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [support_hit_true hS (by simpa [ha] using hcross.1),
        support_hit_true hS (by simpa [hb] using hcross.2)]
      rfl
    · rw [support_hit_true hS (by simpa [ha] using hcross.2),
        support_hit_true hS (by simpa [hb] using hcross.1)]
      rfl


def Left (D : Dag) (w : ℕ) : ℕ := opA D (w - 10)

def Right (D : Dag) (w : ℕ) : ℕ := opB D (w - 10)

lemma window_valid {D : Dag} (hS : Strict 10 D) {offset count : ℕ}
    (hbound : offset + count ≤ D.length) :
    ValidUpTo (10 + offset) (Left D) (Right D) count := by
  intro t ht
  have hj : offset + t < D.length := by omega
  have hsub : 10 + offset + t - 10 = offset + t := by omega
  obtain ⟨ha, hb, hab⟩ := hS (offset + t) hj
  simp only [Left, Right, hsub]
  exact ⟨by omega, by omega, hab⟩

lemma window_linear {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D = 0)
    {offset count : ℕ} (hbound : offset + count ≤ D.length) :
    LinearUpTo (DagResource D) (10 + offset) (Left D) (Right D) count := by
  intro i hi j hj w he hri hrj
  have his : 10 + offset + i - 10 = offset + i := by omega
  have hjs : 10 + offset + j - 10 = offset + j := by omega
  change supp 10 D w = ∅ at he
  simp only [Reads, Left, Right, his] at hri
  simp only [Reads, Left, Right, hjs] at hrj
  have heq := zero_reader_unique hS hB (by omega : offset + i < D.length)
    (by omega : offset + j < D.length) he hri hrj
  omega

lemma window_canonical {D : Dag} (hS : Strict 10 D) {offset count : ℕ}
    (hbound : offset + count ≤ D.length)
    (hsides : ∀ j, offset ≤ j → j < offset + count → tag D j = true →
      AllowedSides (DagResource D (opA D j)) (DagResource D (opB D j))) :
    CanonicalUpTo (DagResource D) (10 + offset) (Left D) (Right D) count := by
  intro t ht
  have hj : offset + t < D.length := by omega
  have hsub : 10 + offset + t - 10 = offset + t := by omega
  have hout : 10 + offset + t = 10 + (offset + t) := by omega
  simp only [Left, Right, hsub]
  rw [hout]
  have hgate := resource_gate hS hj
  cases ht : tag D (offset + t)
  · left
    simpa only [ht, Bool.false_eq_true, ite_false] using hgate
  · right
    exact ⟨hsides _ (by omega) (by omega) ht, by simpa only [ht, ite_true] using hgate⟩

def OtherAndSides (D : Dag) (g : ℕ) : Prop :=
  ∀ j < D.length, j ≠ g → tag D j = true →
    AllowedSides (DagResource D (opA D j)) (DagResource D (opB D j))

lemma before_seed_ordinary {D : Dag} (hS : Strict 10 D) {g : ℕ}
    (hg : g < D.length) (hsides : OtherAndSides D g) :
    ∀ i < 10 + g, Ordinary (DagResource D i) := by
  apply ordinary_prefix (start := 10) (n := g) (A := Left D) (B := Right D)
  · exact fun i hi => input_ordinary D hi
  · exact window_valid (offset := 0) hS (by omega)
  · apply window_canonical (offset := 0) hS (by omega)
    intro j _ hj ht
    exact hsides j (by omega) (by omega) ht

lemma canonical_dag_exclusion {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D = 0)
    {g : ℕ} (hg : g < D.length) (ht : tag D g = true) (hdirty : DirtySides D g)
    (hsides : OtherAndSides D g) :
    ∀ w < 10 + D.length, ¬ Target (DagResource D w) := by
  obtain ⟨hdz, hdt⟩ := dirty_seed hS hg ht hdirty
  have hbefore := before_seed_ordinary hS hg hsides
  have hinit : Invariant (Pool (DagResource D) (Finset.range (10 + (g + 1)))) := by
    apply initial_exceptional (d := 10 + g) (by omega) hdz hdt
    intro i hi hne
    exact hbefore i (by omega)
  have hcount : g + 1 + (D.length - (g + 1)) ≤ D.length := by omega
  have hvalid := window_valid hS hcount
  have hlinear := window_linear hS hB hcount
  have hcanonical : CanonicalUpTo (DagResource D) (10 + (g + 1)) (Left D) (Right D)
      (D.length - (g + 1)) := by
    apply window_canonical hS hcount
    intro j hlo hhi ht
    exact hsides j (by omega) (by omega) ht
  intro w hw
  exact program_any_wire_exclusion hinit hvalid hlinear hcanonical w (by omega)

end S45.DAGBridge

namespace DAGBridge

open DagTools

lemma petersen_single_false : ∀ v : Fin 10,
    PEqualNP.Outside.L_meta_2590.edgeFn (single v) = false := by
  decide

end DAGBridge

namespace FiveGroup.DAGBridge

open PEqualNP.Outside.L_meta_2590.DAGBridge.DagTools
open PEqualNP.Outside.L_meta_2590.DAGBridge
open ResourceExclusion CausalBarrier

lemma target_of_computes {D : Dag} {w : ℕ}
    (hc : ∀ x : Fin 10 → Bool, val D x w = PEqualNP.Outside.L_meta_2590.edgeFn x) :
    Target (DagResource D w) := by
  refine ⟨?_, ?_, ?_⟩
  · change supp 10 D w = ∅
    ext v
    simp only [Finset.notMem_empty, iff_false]
    intro hv
    have ht := mem_supp.mp hv
    rw [hc, petersen_single_false] at ht
    contradiction
  · intro E hE
    change val D (fun v => decide (v ∈ E)) w = true
    rw [hc]
    have hfinite : ∀ E ∈ DirtyEdges, PEqualNP.Outside.L_meta_2590.edgeFn (fun v => decide (v ∈ E)) = true := by
      simp [DirtyEdges, PEqualNP.Outside.L_meta_2590.edgeFn]
    exact hfinite E hE
  · change val D (fun v => decide (v ∈ ({3, 9} : Finset (Fin 10)))) w = false
    rw [hc]
    decide

lemma petersen_dag_exclusion {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D = 0)
    {g : ℕ} (hg : g < D.length) (ht : tag D g = true) (hdirty : DirtySides D g)
    (hsides : OtherAndSides D g) {w : ℕ} (hw : w < 10 + D.length) :
    ¬ ∀ x : Fin 10 → Bool, val D x w = PEqualNP.Outside.L_meta_2590.edgeFn x := by
  intro hc
  exact canonical_dag_exclusion hS hB hg ht hdirty hsides w hw (target_of_computes hc)

end FiveGroup.DAGBridge

namespace S45.DAGBridge

open PEqualNP.Outside.L_meta_2590.DAGBridge.DagTools
open PEqualNP.Outside.L_meta_2590.DAGBridge
open ResourceExclusion CausalBarrier

lemma target_of_computes {D : Dag} {w : ℕ}
    (hc : ∀ x : Fin 10 → Bool, val D x w = PEqualNP.Outside.L_meta_2590.edgeFn x) :
    Target (DagResource D w) := by
  refine ⟨?_, ?_, ?_⟩
  · change supp 10 D w = ∅
    ext v
    simp only [Finset.notMem_empty, iff_false]
    intro hv
    have ht := mem_supp.mp hv
    rw [hc, petersen_single_false] at ht
    contradiction
  · intro E hE
    change val D (fun v => decide (v ∈ E)) w = true
    rw [hc]
    have hfinite : ∀ E ∈ DirtyEdges, PEqualNP.Outside.L_meta_2590.edgeFn (fun v => decide (v ∈ E)) = true := by
      simp [DirtyEdges, PEqualNP.Outside.L_meta_2590.edgeFn]
    exact hfinite E hE
  · change val D (fun v => decide (v ∈ ({4, 8} : Finset (Fin 10)))) w = false
    rw [hc]
    decide

lemma petersen_dag_exclusion {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D = 0)
    {g : ℕ} (hg : g < D.length) (ht : tag D g = true) (hdirty : DirtySides D g)
    (hsides : OtherAndSides D g) {w : ℕ} (hw : w < 10 + D.length) :
    ¬ ∀ x : Fin 10 → Bool, val D x w = PEqualNP.Outside.L_meta_2590.edgeFn x := by
  intro hc
  exact canonical_dag_exclusion hS hB hg ht hdirty hsides w hw (target_of_computes hc)

end S45.DAGBridge

namespace Generic

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

lemma safe_zero_false {T : Finset (Fin 10)} {w : Wire}
    (h : Safe T w) (hz : w.1 = ∅) : w.2 = false := by
  cases hv : w.2
  · rfl
  · have hn := h hv
    simp [hz] at hn

def OtherSides (C : Bool) : List (Finset (Fin 10) × Finset (Fin 10)) :=
  if C then
    [({0}, {1, 4, 5}), ({1}, {6}), ({2}, {1, 3, 7}), ({3}, {4, 8}), ({7}, {5, 9}), (∅, ∅)]
  else [({0}, {1, 4, 5}), ({1}, {2, 6}), ({4}, {3, 9}), ({5}, {7, 8}), (∅, ∅)]

def DirtyEdges (C : Bool) : List (Finset (Fin 10)) :=
  if C then [{4, 9}, {5, 8}, {6, 8}, {6, 9}]
  else [{2, 3}, {3, 8}, {6, 8}, {6, 9}, {2, 7}, {7, 9}]

def CrossPairs (C : Bool) : List (Finset (Fin 10)) :=
  if C then [{4, 8}, {4, 9}, {5, 8}, {5, 9}, {6, 8}, {6, 9}]
  else [{2, 3}, {3, 8}, {3, 9}, {2, 6}, {6, 8}, {6, 9}, {2, 7}, {7, 8}, {7, 9}]

def Rejected (C : Bool) : Finset (Fin 10) := if C then {4, 8} else {3, 9}

def UniversalEdge (C : Bool) (v : Fin 10) : Finset (Fin 10) :=
  if C then
    match v.val with
    | 0 => {6, 8}
    | 1 => {4, 9}
    | 2 => {4, 9}
    | 3 => {6, 9}
    | 4 => {4, 9}
    | 5 => {5, 8}
    | 6 => {6, 8}
    | 7 => {6, 8}
    | 8 => {5, 8}
    | _ => {4, 9}
  else
    match v.val with
    | 0 => {2, 3}
    | 1 => {3, 8}
    | 2 => {2, 3}
    | 3 => {2, 3}
    | 4 => {6, 8}
    | 5 => {6, 9}
    | 6 => {6, 8}
    | 7 => {2, 7}
    | 8 => {3, 8}
    | _ => {6, 9}

def UniversalBarrier (C : Bool) (v : Fin 10) : Finset (Fin 10) :=
  insert v (UniversalEdge C v)

lemma universal_edge_valid (C : Bool) : ∀ v : Fin 10,
    UniversalEdge C v ∈ DirtyEdges C := by cases C <;> decide

lemma all_vertices_separation (C : Bool) :
    ∀ v : Fin 10, ∀ AB ∈ OtherSides C,
      Separates (UniversalBarrier C v) AB.1 AB.2 ∧
      Separates (UniversalBarrier C v) AB.2 AB.1 := by
  intro v
  cases C <;> simp [OtherSides, Separates] <;> revert v <;> decide

variable {C : Bool}

abbrev Resource := Finset (Fin 10) × (Finset (Fin 10) → Bool)

def RSafe (E T : Finset (Fin 10)) (w : Resource) : Prop :=
  w.2 E = true → (w.1 ∩ T).Nonempty

def Ordinary (C : Bool) (w : Resource) : Prop := ∀ E ∈ CrossPairs C, RSafe E E w

def AllOrdinary (C : Bool) (p : Multiset Resource) : Prop := ∀ w ∈ p, Ordinary C w

def RJoin (a b : Resource) : Resource :=
  (a.1 ∪ b.1, fun E => a.2 E || b.2 E)

def RMeet (a b : Resource) : Resource :=
  (a.1 ∩ b.1, fun E => a.2 E && b.2 E)

def AllowedSides (C : Bool) (a b : Resource) : Prop :=
  (a.1, b.1) ∈ OtherSides C ∨ (b.1, a.1) ∈ OtherSides C

def Keep (w : Resource) : Multiset Resource :=
  if w.1 = ∅ then 0 else {w}

def Next (a b c : Resource) (rest : Multiset Resource) : Multiset Resource :=
  c ::ₘ (Keep a + Keep b + rest)

def ResourceStep (C : Bool) (p q : Multiset Resource) : Prop :=
  (∃ a b c rest, p = a ::ₘ b ::ₘ rest ∧ q = Next a b c rest ∧
    (c = RJoin a b ∨ (AllowedSides C a b ∧ c = RMeet a b))) ∨
  (∃ w rest, w.1 ≠ ∅ ∧ p = w ::ₘ rest ∧ q = w ::ₘ w ::ₘ rest) ∨
  (∃ w rest, p = w ::ₘ rest ∧ q = rest)

def Blocked (C : Bool) (p : Multiset Resource) : Prop :=
  ∃ E ∈ DirtyEdges C, ∃ T : Finset (Fin 10),
    (∀ AB ∈ OtherSides C, Separates T AB.1 AB.2 ∧ Separates T AB.2 AB.1) ∧
    ∀ w ∈ p, RSafe E T w

def Exceptional (C : Bool) (p : Multiset Resource) : Prop :=
  ∃ d rest, p = d ::ₘ rest ∧ d.1 = ∅ ∧
    (∀ E ∈ CrossPairs C, d.2 E = true) ∧ AllOrdinary C rest

def Invariant (C : Bool) (p : Multiset Resource) : Prop := Blocked C p ∨ Exceptional C p

def Target (C : Bool) (w : Resource) : Prop :=
  w.1 = ∅ ∧ (∀ E ∈ DirtyEdges C, w.2 E = true) ∧ w.2 (Rejected C) = false

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
    ∀ E ∈ CrossPairs C, ∀ AB ∈ OtherSides C,
      Separates E AB.1 AB.2 ∧ Separates E AB.2 AB.1 := by
  cases C <;> simp [CrossPairs, OtherSides, Separates]

lemma dirty_mem_cross : ∀ E ∈ DirtyEdges C, E ∈ CrossPairs C := by
  cases C <;> simp [DirtyEdges, CrossPairs]

lemma ordinary_join {a b : Resource} (ha : Ordinary C a) (hb : Ordinary C b) :
    Ordinary C (RJoin a b) := by
  intro E hE
  exact rsafe_join (ha E hE) (hb E hE)

lemma ordinary_meet {a b : Resource} (ha : Ordinary C a) (hb : Ordinary C b)
    (hs : AllowedSides C a b) : Ordinary C (RMeet a b) := by
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
    (ha : Ordinary C a) (hb : Ordinary C b) (hc : Ordinary C c) (hr : AllOrdinary C rest) :
    AllOrdinary C (Next a b c rest) := by
  intro w hw
  simp only [Next, Multiset.mem_cons, Multiset.mem_add] at hw
  rcases hw with rfl | (hw | hw) | hw
  · exact hc
  · exact (keep_mem hw) ▸ ha
  · exact (keep_mem hw) ▸ hb
  · exact hr w hw

lemma allOrdinary_blocked {p : Multiset Resource} (hp : AllOrdinary C p) : Blocked C p := by
  refine ⟨UniversalEdge C 0, universal_edge_valid C 0, UniversalEdge C 0, ?_, ?_⟩
  · exact cross_separation _ (dirty_mem_cross _ (universal_edge_valid C 0))
  · intro w hw
    exact hp w hw _ (dirty_mem_cross _ (universal_edge_valid C 0))

lemma blocked_no_target {p : Multiset Resource} (hp : Blocked C p)
    {w : Resource} (hw : w ∈ p) : ¬ Target C w := by
  obtain ⟨E, hE, T, _, hs⟩ := hp
  rintro ⟨hz, ht, _⟩
  have hf := rsafe_zero_false (hs w hw) hz
  rw [ht E hE] at hf
  contradiction

lemma exceptional_no_target {p : Multiset Resource} (hp : Exceptional C p)
    {w : Resource} (hw : w ∈ p) : ¬ Target C w := by
  obtain ⟨d, rest, rfl, hd, hdt, hr⟩ := hp
  rcases Multiset.mem_cons.mp hw with rfl | hw
  · rintro ⟨_, _, hf⟩
    have ht := hdt (Rejected C) (by cases C <;> simp [CrossPairs, Rejected])
    rw [hf] at ht
    contradiction
  · exact blocked_no_target (allOrdinary_blocked hr) hw

lemma invariant_no_target {p : Multiset Resource} (hp : Invariant C p)
    {w : Resource} (hw : w ∈ p) : ¬ Target C w := by
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

lemma blocked_step {p q : Multiset Resource} (hp : Blocked C p)
    (hstep : ResourceStep C p q) : Blocked C q := by
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
    (hc : c.1.Nonempty) (hr : AllOrdinary C rest) : Blocked C (c ::ₘ rest) := by
  obtain ⟨v, hv⟩ := hc
  refine ⟨UniversalEdge C v, universal_edge_valid C v, UniversalBarrier C v,
    all_vertices_separation C v, ?_⟩
  intro w hw
  rcases Multiset.mem_cons.mp hw with rfl | hw
  · intro _
    exact ⟨v, Finset.mem_inter.mpr ⟨hv, Finset.mem_insert_self _ _⟩⟩
  · intro ht
    obtain ⟨u, hu⟩ := hr w hw _ (dirty_mem_cross _ (universal_edge_valid C v)) ht
    obtain ⟨hus, huE⟩ := Finset.mem_inter.mp hu
    exact ⟨u, Finset.mem_inter.mpr ⟨hus, Finset.mem_insert_of_mem huE⟩⟩

lemma keep_ordinary {w : Resource} (h : Ordinary C w) : AllOrdinary C (Keep w) := by
  intro a ha
  exact (keep_mem ha) ▸ h

lemma allOrdinary_add {p q : Multiset Resource}
    (hp : AllOrdinary C p) (hq : AllOrdinary C q) : AllOrdinary C (p + q) := by
  intro w hw
  rcases Multiset.mem_add.mp hw with hw | hw
  · exact hp w hw
  · exact hq w hw

lemma allOrdinary_cons {w : Resource} {p : Multiset Resource}
    (hw : Ordinary C w) (hp : AllOrdinary C p) : AllOrdinary C (w ::ₘ p) := by
  intro a ha
  rcases Multiset.mem_cons.mp ha with rfl | ha
  · exact hw
  · exact hp a ha

lemma zero_side_of_allowed {a b : Resource} (ha : a.1 = ∅) (hs : AllowedSides C a b) :
    b.1 = ∅ := by
  have hzero : ∀ AB ∈ OtherSides C,
      (AB.1 = ∅ → AB.2 = ∅) ∧ (AB.2 = ∅ → AB.1 = ∅) := by
    cases C <;> simp [OtherSides]
  rcases hs with hs | hs
  · exact (hzero _ hs).1 ha
  · exact (hzero _ hs).2 ha

lemma exceptional_left_step {d b c : Resource} {rest : Multiset Resource}
    (hd : d.1 = ∅) (hdt : ∀ E ∈ CrossPairs C, d.2 E = true)
    (hb : Ordinary C b) (hr : AllOrdinary C rest)
    (hc : c = RJoin d b ∨ (AllowedSides C d b ∧ c = RMeet d b)) :
    Invariant C (Next d b c rest) := by
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
      have hpool : AllOrdinary C (Keep d + Keep b + rest) := by
        simpa [Keep, hd, hbs] using allOrdinary_cons hb hr
      exact ordinary_carrier_blocked hbp hpool
  · left
    have hbs := zero_side_of_allowed hd hs
    have hc : Ordinary C (RMeet d b) := by
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

lemma ordinary_result {a b c : Resource} (ha : Ordinary C a) (hb : Ordinary C b)
    (hc : c = RJoin a b ∨ (AllowedSides C a b ∧ c = RMeet a b)) : Ordinary C c := by
  rcases hc with rfl | ⟨hs, rfl⟩
  · exact ordinary_join ha hb
  · exact ordinary_meet ha hb hs

lemma exceptional_step {p q : Multiset Resource} (hp : Exceptional C p)
    (hstep : ResourceStep C p q) : Invariant C q := by
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
        have ha : Ordinary C a := hr0 a (by simp)
        have hb : Ordinary C b := hr0 b (by simp)
        have hr : AllOrdinary C r := fun w hw => hr0 w (by simp [hw])
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

lemma invariant_step {p q : Multiset Resource} (hp : Invariant C p)
    (hstep : ResourceStep C p q) : Invariant C q := by
  rcases hp with hp | hp
  · exact Or.inl (blocked_step hp hstep)
  · exact exceptional_step hp hstep

def ResourceTrace (C : Bool) (p : Multiset Resource) : List (Multiset Resource) → Prop
  | [] => True
  | q :: qs => ResourceStep C p q ∧ ResourceTrace C q qs

lemma invariant_trace {p : Multiset Resource} {qs : List (Multiset Resource)}
    (hp : Invariant C p) (ht : ResourceTrace C p qs) : ∀ q ∈ qs, Invariant C q := by
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
    (hd : d.1 = ∅) (hdt : ∀ E ∈ CrossPairs C, d.2 E = true)
    (ho : AllOrdinary C ordinary) (ht : ResourceTrace C (d ::ₘ ordinary) qs)
    (hq : q ∈ qs) (hout : out ∈ q) : ¬ Target C out := by
  have hi : Invariant C (d ::ₘ ordinary) := Or.inr ⟨d, ordinary, rfl, hd, hdt, ho⟩
  exact invariant_no_target (invariant_trace hi ht q hq) hout

def Pool (W : ℕ → Resource) (ids : Finset ℕ) : Multiset Resource := ids.val.map W

def DropZero (W : ℕ → Resource) (i : ℕ) (ids : Finset ℕ) : Finset ℕ :=
  if (W i).1 = ∅ then ids.erase i else ids

def NextIds (W : ℕ → Resource) (a b out : ℕ) (ids : Finset ℕ) : Finset ℕ :=
  insert out (DropZero W b (DropZero W a ids))

def Available (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ) : ℕ → Finset ℕ
  | 0 => Finset.range start
  | t + 1 => NextIds W (A (start + t)) (B (start + t)) (start + t)
      (Available W start A B t)

lemma drop_subset (W : ℕ → Resource) (i : ℕ) (ids : Finset ℕ) :
    DropZero W i ids ⊆ ids := by
  unfold DropZero
  split
  · exact Finset.erase_subset _ _
  · exact Finset.Subset.refl _

lemma mem_drop {W : ℕ → Resource} {i x : ℕ} {ids : Finset ℕ}
    (hx : x ∈ ids) (hkeep : (W x).1 ≠ ∅ ∨ x ≠ i) : x ∈ DropZero W i ids := by
  unfold DropZero
  split_ifs with hi
  · apply Finset.mem_erase.mpr
    refine ⟨?_, hx⟩
    rcases hkeep with hkeep | hkeep
    · intro hxi
      subst x
      exact hkeep hi
    · exact hkeep
  · exact hx

lemma available_bounded (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ)
    (t : ℕ) : ∀ x ∈ Available W start A B t, x < start + t := by
  induction t with
  | zero => simp [Available]
  | succ t ih =>
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · omega
      · have hx' := drop_subset W _ _ (drop_subset W _ _ hx)
        have hb := ih x hx'
        omega

lemma available_complete (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ)
    (t : ℕ) : ∀ x, x < start + t →
      ((W x).1 ≠ ∅ ∨ ∀ j < t, A (start + j) ≠ x ∧ B (start + j) ≠ x) →
      x ∈ Available W start A B t := by
  induction t with
  | zero => simp [Available]
  | succ t ih =>
      intro x hbound hunused
      by_cases hlast : x = start + t
      · subst x
        exact Finset.mem_insert_self _ _
      · have hold : x < start + t := by omega
        have hprev : (W x).1 ≠ ∅ ∨ ∀ j < t,
            A (start + j) ≠ x ∧ B (start + j) ≠ x := by
          rcases hunused with hp | hu
          · exact Or.inl hp
          · exact Or.inr (fun j hj => hu j (by omega))
        have hmem := ih x hold hprev
        apply Finset.mem_insert_of_mem
        apply mem_drop
        · apply mem_drop hmem
          rcases hunused with hp | hu
          · exact Or.inl hp
          · exact Or.inr (Ne.symm (hu t (by omega)).1)
        · rcases hunused with hp | hu
          · exact Or.inl hp
          · exact Or.inr (Ne.symm (hu t (by omega)).2)

def Reads (A B : ℕ → ℕ) (i x : ℕ) : Prop := A i = x ∨ B i = x

def LinearUpTo (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ i < n, ∀ j < n, ∀ x, (W x).1 = ∅ →
    Reads A B (start + i) x → Reads A B (start + j) x → i = j

lemma source_available {W : ℕ → Resource} {start n t x : ℕ} {A B : ℕ → ℕ}
    (hlin : LinearUpTo W start A B n) (ht : t < n)
    (hx : x < start + t) (hr : Reads A B (start + t) x) :
    x ∈ Available W start A B t := by
  apply available_complete W start A B t x hx
  by_cases hp : (W x).1 = ∅
  · right
    intro j hj
    constructor
    · intro hja
      have heq := hlin t ht j (by omega) x hp hr (Or.inl hja)
      omega
    · intro hjb
      have heq := hlin t ht j (by omega) x hp hr (Or.inr hjb)
      omega
  · exact Or.inl hp

lemma pool_insert {W : ℕ → Resource} {ids : Finset ℕ} {i : ℕ} (hi : i ∉ ids) :
    Pool W (insert i ids) = W i ::ₘ Pool W ids := by
  simp only [Pool, Finset.insert_val_of_notMem hi, Multiset.map_cons]

lemma pool_erase_decomp {W : ℕ → Resource} {ids : Finset ℕ} {i : ℕ} (hi : i ∈ ids) :
    Pool W ids = W i ::ₘ Pool W (ids.erase i) := by
  calc
    Pool W ids = Pool W (insert i (ids.erase i)) := by rw [Finset.insert_erase hi]
    _ = W i ::ₘ Pool W (ids.erase i) := pool_insert (Finset.notMem_erase _ _)

lemma pool_two_decomp {W : ℕ → Resource} {ids : Finset ℕ} {a b : ℕ}
    (ha : a ∈ ids) (hb : b ∈ ids) (hab : a ≠ b) :
    Pool W ids = W a ::ₘ W b ::ₘ Pool W ((ids.erase a).erase b) := by
  rw [pool_erase_decomp ha]
  rw [pool_erase_decomp (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩)]

lemma pool_drop_two {W : ℕ → Resource} {ids : Finset ℕ} {a b : ℕ}
    (ha : a ∈ ids) (hb : b ∈ ids) (hab : a ≠ b) :
    Pool W (DropZero W b (DropZero W a ids)) =
      Keep (W a) + Keep (W b) + Pool W ((ids.erase a).erase b) := by
  classical
  by_cases hza : (W a).1 = ∅ <;> by_cases hzb : (W b).1 = ∅
  · simp [DropZero, Keep, hza, hzb]
  · simp only [DropZero, Keep, hza, hzb, ite_true, ite_false, zero_add]
    exact pool_erase_decomp (Finset.mem_erase.mpr ⟨Ne.symm hab, hb⟩)
  · simp only [DropZero, Keep, hza, hzb, ite_true, ite_false, add_zero]
    rw [Finset.erase_right_comm]
    exact pool_erase_decomp (Finset.mem_erase.mpr ⟨hab, ha⟩)
  · simp only [DropZero, Keep, hza, hzb, ite_false]
    simpa using pool_two_decomp ha hb hab

lemma index_resource_step {W : ℕ → Resource} {ids : Finset ℕ} {a b out : ℕ}
    (ha : a ∈ ids) (hb : b ∈ ids) (hab : a ≠ b) (hout : out ∉ ids)
    (hg : W out = RJoin (W a) (W b) ∨
      (AllowedSides C (W a) (W b) ∧ W out = RMeet (W a) (W b))) :
    ResourceStep C (Pool W ids) (Pool W (NextIds W a b out ids)) := by
  left
  refine ⟨W a, W b, W out, Pool W ((ids.erase a).erase b),
    pool_two_decomp ha hb hab, ?_, hg⟩
  have hfresh : out ∉ DropZero W b (DropZero W a ids) := by
    intro h
    exact hout (drop_subset W _ _ (drop_subset W _ _ h))
  rw [NextIds, pool_insert hfresh, pool_drop_two ha hb hab]
  rfl


def ValidUpTo (start : ℕ) (A B : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ t < n, A (start + t) < start + t ∧ B (start + t) < start + t ∧
    A (start + t) ≠ B (start + t)

def CanonicalUpTo (C : Bool) (W : ℕ → Resource) (start : ℕ) (A B : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ t < n,
    W (start + t) = RJoin (W (A (start + t))) (W (B (start + t))) ∨
    (AllowedSides C (W (A (start + t))) (W (B (start + t))) ∧
      W (start + t) = RMeet (W (A (start + t))) (W (B (start + t))))

lemma available_step {W : ℕ → Resource} {start n t : ℕ} {A B : ℕ → ℕ}
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo C W start A B n) (ht : t < n) :
    ResourceStep C (Pool W (Available W start A B t))
      (Pool W (Available W start A B (t + 1))) := by
  obtain ⟨ha, hb, hab⟩ := hv t ht
  have haa := source_available hl ht ha (Or.inl rfl)
  have hba := source_available hl ht hb (Or.inr rfl)
  apply index_resource_step haa hba hab ?_ (hc t ht)
  intro h
  have := available_bounded W start A B t _ h
  omega

lemma program_invariant {W : ℕ → Resource} {start n : ℕ} {A B : ℕ → ℕ}
    (hp : Invariant C (Pool W (Finset.range start)))
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo C W start A B n) :
    ∀ t ≤ n, Invariant C (Pool W (Available W start A B t)) := by
  intro t
  induction t with
  | zero => intro _; exact hp
  | succ t ih =>
      intro ht
      exact invariant_step (ih (by omega)) (available_step hv hl hc (by omega))

lemma pool_mem {W : ℕ → Resource} {ids : Finset ℕ} {i : ℕ} (hi : i ∈ ids) :
    W i ∈ Pool W ids := by
  exact Multiset.mem_map.mpr ⟨i, hi, rfl⟩

lemma canonical_program_exclusion {W : ℕ → Resource} {start n : ℕ} {A B : ℕ → ℕ}
    (hp : Invariant C (Pool W (Finset.range start)))
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo C W start A B n) :
    ∀ t < n, ¬ Target C (W (start + t)) := by
  intro t ht
  have hinv := program_invariant hp hv hl hc (t + 1) (by omega)
  apply invariant_no_target hinv
  apply pool_mem
  exact Finset.mem_insert_self _ _

lemma initial_exceptional {W : ℕ → Resource} {start d : ℕ}
    (hd : d < start) (hz : (W d).1 = ∅)
    (ht : ∀ E ∈ CrossPairs C, (W d).2 E = true)
    (ho : ∀ i < start, i ≠ d → Ordinary C (W i)) :
    Invariant C (Pool W (Finset.range start)) := by
  right
  refine ⟨W d, Pool W ((Finset.range start).erase d),
    pool_erase_decomp (Finset.mem_range.mpr hd), hz, ht, ?_⟩
  intro w hw
  obtain ⟨i, hi, rfl⟩ := Multiset.mem_map.mp hw
  have hi' : i ∈ (Finset.range start).erase d := hi
  obtain ⟨hid, hir⟩ := Finset.mem_erase.mp hi'
  exact ho i (Finset.mem_range.mp hir) hid

lemma seeded_program_exclusion {W : ℕ → Resource} {start n d : ℕ} {A B : ℕ → ℕ}
    (hd : d < start) (hz : (W d).1 = ∅)
    (ht : ∀ E ∈ CrossPairs C, (W d).2 E = true)
    (ho : ∀ i < start, i ≠ d → Ordinary C (W i))
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo C W start A B n) :
    ∀ t < n, ¬ Target C (W (start + t)) :=
  canonical_program_exclusion (initial_exceptional hd hz ht ho) hv hl hc


lemma program_any_wire_exclusion {W : ℕ → Resource} {start n : ℕ} {A B : ℕ → ℕ}
    (hp : Invariant C (Pool W (Finset.range start)))
    (hv : ValidUpTo start A B n) (hl : LinearUpTo W start A B n)
    (hc : CanonicalUpTo C W start A B n) :
    ∀ i < start + n, ¬ Target C (W i) := by
  intro i hi
  by_cases hold : i < start
  · exact invariant_no_target hp (pool_mem (Finset.mem_range.mpr hold))
  · have ht : i - start < n := by omega
    have heq : start + (i - start) = i := by omega
    simpa only [heq] using canonical_program_exclusion hp hv hl hc (i - start) ht

lemma ordinary_prefix {W : ℕ → Resource} {start n : ℕ} {A B : ℕ → ℕ}
    (hp : ∀ i < start, Ordinary C (W i))
    (hv : ValidUpTo start A B n) (hc : CanonicalUpTo C W start A B n) :
    ∀ i < start + n, Ordinary C (W i) := by
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
      intro hi
      by_cases hold : i < start
      · exact hp i hold
      · have ht : i - start < n := by omega
        have heq : start + (i - start) = i := by omega
        obtain ⟨ha, hb, _⟩ := hv (i - start) ht
        rw [heq] at ha hb
        have hca := hc (i - start) ht
        rw [heq] at hca
        exact ordinary_result (ih _ ha (by omega)) (ih _ hb (by omega)) hca

end Generic

namespace Generic.DAGBridge

open PEqualNP.Outside.L_meta_2590.DAGBridge.DagTools

variable {C : Bool}

def DagResource (D : Dag) (w : ℕ) : Resource :=
  (supp 10 D w, fun E => val D (fun v => decide (v ∈ E)) w)

lemma zero_reader_unique {D : Dag} (hS : Strict 10 D) (hz : Bzero 10 D = 0)
    {j k w : ℕ} (hj : j < D.length) (hk : k < D.length)
    (he : supp 10 D w = ∅)
    (hrj : opA D j = w ∨ opB D j = w)
    (hrk : opA D k = w ∨ opB D k = w) : j = k := by
  have hw : w < 10 + j := by
    obtain ⟨ha, hb, _⟩ := hS j hj
    rcases hrj with h | h <;> omega
  have hinner : w ∈ (inner 10 D).filter (fun u => ¬ (supp 10 D u).Nonempty) := by
    apply Finset.mem_filter.mpr
    constructor
    · simp only [inner, Finset.mem_range]
      omega
    · simp [he]
  have hsum : fanout D w - 1 ≤ Bzero 10 D := by
    unfold Bzero surplusOn
    exact Finset.single_le_sum (f := fun u => fanout D u - 1) (fun _ _ => Nat.zero_le _) hinner
  have hcard : (readers D w).card ≤ 1 := by
    change fanout D w ≤ 1
    omega
  apply Finset.card_le_one.mp hcard j ?_ k ?_
  · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hrj⟩
  · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hrk⟩

lemma input_ordinary (D : Dag) {i : ℕ} (hi : i < 10) : Ordinary C (DagResource D i) := by
  intro E _ ht
  change val D (fun v => decide (v ∈ E)) i = true at ht
  rw [val_input D _ i hi] at ht
  have hm : (⟨i, hi⟩ : Fin 10) ∈ E := of_decide_eq_true ht
  refine ⟨⟨i, hi⟩, Finset.mem_inter.mpr ⟨?_, hm⟩⟩
  change (⟨i, hi⟩ : Fin 10) ∈ supp 10 D i
  rw [supp_input D ⟨i, hi⟩]
  simp

lemma resource_gate {D : Dag} (hS : Strict 10 D) {j : ℕ} (hj : j < D.length) :
    DagResource D (10 + j) =
      if tag D j = true then RMeet (DagResource D (opA D j)) (DagResource D (opB D j))
      else RJoin (DagResource D (opA D j)) (DagResource D (opB D j)) := by
  cases ht : tag D j
  · simp only [Bool.false_eq_true, ite_false]
    apply Prod.ext
    · exact (supp_gate hS j hj).trans (by simp [ht, RJoin, DagResource])
    · funext E
      exact (val_gate hS (fun v => decide (v ∈ E)) j hj).trans (by simp [ht, gop, RJoin, DagResource])
  · simp only [ite_true]
    apply Prod.ext
    · exact (supp_gate hS j hj).trans (by simp [ht, RMeet, DagResource])
    · funext E
      exact (val_gate hS (fun v => decide (v ∈ E)) j hj).trans (by simp [ht, gop, RMeet, DagResource])

lemma support_hit_true {D : Dag} (hS : Strict 10 D) {w : ℕ} {E : Finset (Fin 10)}
    (hh : (supp 10 D w ∩ E).Nonempty) : (DagResource D w).2 E = true := by
  obtain ⟨v, hv⟩ := hh
  obtain ⟨hvs, hvE⟩ := Finset.mem_inter.mp hv
  apply val_mono hS (single v) (fun u => decide (u ∈ E)) ?_ w (mem_supp.mp hvs)
  intro u hu
  have huv : u = v := by simpa [single] using hu
  subst u
  exact decide_eq_true hvE

def DirtyA (C : Bool) : Finset (Fin 10) :=
  if C then {4, 5, 6} else {3, 6, 7}

def DirtyB (C : Bool) : Finset (Fin 10) :=
  if C then {8, 9} else {2, 8, 9}

def DirtySides (C : Bool) (D : Dag) (g : ℕ) : Prop :=
  (supp 10 D (opA D g) = DirtyA C ∧ supp 10 D (opB D g) = DirtyB C) ∨
  (supp 10 D (opA D g) = DirtyB C ∧ supp 10 D (opB D g) = DirtyA C)

lemma cross_hits : ∀ E ∈ CrossPairs C,
    (DirtyA C ∩ E).Nonempty ∧ (DirtyB C ∩ E).Nonempty := by
  cases C <;> simp [CrossPairs, DirtyA, DirtyB]

lemma dirty_seed {D : Dag} (hS : Strict 10 D) {g : ℕ} (hg : g < D.length)
    (ht : tag D g = true) (hs : DirtySides C D g) :
    (DagResource D (10 + g)).1 = ∅ ∧
      ∀ E ∈ CrossPairs C, (DagResource D (10 + g)).2 E = true := by
  constructor
  · change supp 10 D (10 + g) = ∅
    rw [supp_gate hS g hg, ht]
    simp only [ite_true]
    rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [ha, hb]
      cases C <;> decide
    · rw [ha, hb]
      cases C <;> decide
  · intro E hE
    change val D (fun v => decide (v ∈ E)) (10 + g) = true
    rw [val_gate hS _ g hg, ht]
    change (DagResource D (opA D g)).2 E && (DagResource D (opB D g)).2 E = true
    have hcross := cross_hits E hE
    rcases hs with ⟨ha, hb⟩ | ⟨ha, hb⟩
    · rw [support_hit_true hS (by simpa [ha] using hcross.1),
        support_hit_true hS (by simpa [hb] using hcross.2)]
      rfl
    · rw [support_hit_true hS (by simpa [ha] using hcross.2),
        support_hit_true hS (by simpa [hb] using hcross.1)]
      rfl


def Left (D : Dag) (w : ℕ) : ℕ := opA D (w - 10)

def Right (D : Dag) (w : ℕ) : ℕ := opB D (w - 10)

lemma window_valid {D : Dag} (hS : Strict 10 D) {offset count : ℕ}
    (hbound : offset + count ≤ D.length) :
    ValidUpTo (10 + offset) (Left D) (Right D) count := by
  intro t ht
  have hj : offset + t < D.length := by omega
  have hsub : 10 + offset + t - 10 = offset + t := by omega
  obtain ⟨ha, hb, hab⟩ := hS (offset + t) hj
  simp only [Left, Right, hsub]
  exact ⟨by omega, by omega, hab⟩

lemma window_linear {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D = 0)
    {offset count : ℕ} (hbound : offset + count ≤ D.length) :
    LinearUpTo (DagResource D) (10 + offset) (Left D) (Right D) count := by
  intro i hi j hj w he hri hrj
  have his : 10 + offset + i - 10 = offset + i := by omega
  have hjs : 10 + offset + j - 10 = offset + j := by omega
  change supp 10 D w = ∅ at he
  simp only [Reads, Left, Right, his] at hri
  simp only [Reads, Left, Right, hjs] at hrj
  have heq := zero_reader_unique hS hB (by omega : offset + i < D.length)
    (by omega : offset + j < D.length) he hri hrj
  omega

lemma window_canonical {D : Dag} (hS : Strict 10 D) {offset count : ℕ}
    (hbound : offset + count ≤ D.length)
    (hsides : ∀ j, offset ≤ j → j < offset + count → tag D j = true →
      AllowedSides C (DagResource D (opA D j)) (DagResource D (opB D j))) :
    CanonicalUpTo C (DagResource D) (10 + offset) (Left D) (Right D) count := by
  intro t ht
  have hj : offset + t < D.length := by omega
  have hsub : 10 + offset + t - 10 = offset + t := by omega
  have hout : 10 + offset + t = 10 + (offset + t) := by omega
  simp only [Left, Right, hsub]
  rw [hout]
  have hgate := resource_gate hS hj
  cases ht : tag D (offset + t)
  · left
    simpa only [ht, Bool.false_eq_true, ite_false] using hgate
  · right
    exact ⟨hsides _ (by omega) (by omega) ht, by simpa only [ht, ite_true] using hgate⟩

def OtherAndSides (C : Bool) (D : Dag) (g : ℕ) : Prop :=
  ∀ j < D.length, j ≠ g → tag D j = true →
    AllowedSides C (DagResource D (opA D j)) (DagResource D (opB D j))

lemma before_seed_ordinary {D : Dag} (hS : Strict 10 D) {g : ℕ}
    (hg : g < D.length) (hsides : OtherAndSides C D g) :
    ∀ i < 10 + g, Ordinary C (DagResource D i) := by
  apply ordinary_prefix (start := 10) (n := g) (A := Left D) (B := Right D)
  · exact fun i hi => input_ordinary D hi
  · exact window_valid (offset := 0) hS (by omega)
  · apply window_canonical (offset := 0) hS (by omega)
    intro j _ hj ht
    exact hsides j (by omega) (by omega) ht

lemma canonical_dag_exclusion {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D = 0)
    {g : ℕ} (hg : g < D.length) (ht : tag D g = true) (hdirty : DirtySides C D g)
    (hsides : OtherAndSides C D g) :
    ∀ w < 10 + D.length, ¬ Target C (DagResource D w) := by
  obtain ⟨hdz, hdt⟩ := dirty_seed hS hg ht hdirty
  have hbefore := before_seed_ordinary hS hg hsides
  have hinit : Invariant C (Pool (DagResource D) (Finset.range (10 + (g + 1)))) := by
    apply initial_exceptional (d := 10 + g) (by omega) hdz hdt
    intro i hi hne
    exact hbefore i (by omega)
  have hcount : g + 1 + (D.length - (g + 1)) ≤ D.length := by omega
  have hvalid := window_valid hS hcount
  have hlinear := window_linear hS hB hcount
  have hcanonical : CanonicalUpTo C (DagResource D) (10 + (g + 1)) (Left D) (Right D)
      (D.length - (g + 1)) := by
    apply window_canonical hS hcount
    intro j hlo hhi ht
    exact hsides j (by omega) (by omega) ht
  intro w hw
  exact program_any_wire_exclusion hinit hvalid hlinear hcanonical w (by omega)

end Generic.DAGBridge

namespace Generic.DAGBridge

open PEqualNP.Outside.L_meta_2590.DAGBridge.DagTools
open PEqualNP.Outside.L_meta_2590.DAGBridge
variable {C : Bool}

lemma target_of_computes {D : Dag} {w : ℕ}
    (hc : ∀ x : Fin 10 → Bool, val D x w = PEqualNP.Outside.L_meta_2590.edgeFn x) :
    Target C (DagResource D w) := by
  refine ⟨?_, ?_, ?_⟩
  · change supp 10 D w = ∅
    ext v
    simp only [Finset.notMem_empty, iff_false]
    intro hv
    have ht := mem_supp.mp hv
    rw [hc, petersen_single_false] at ht
    contradiction
  · intro E hE
    change val D (fun v => decide (v ∈ E)) w = true
    rw [hc]
    have hfinite : ∀ E ∈ DirtyEdges C, PEqualNP.Outside.L_meta_2590.edgeFn (fun v => decide (v ∈ E)) = true := by
      cases C <;> simp [DirtyEdges, PEqualNP.Outside.L_meta_2590.edgeFn]
    exact hfinite E hE
  · change val D (fun v => decide (v ∈ Rejected C)) w = false
    rw [hc]
    cases C <;> decide

lemma petersen_dag_exclusion (C : Bool) {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D = 0)
    {g : ℕ} (hg : g < D.length) (ht : tag D g = true) (hdirty : DirtySides C D g)
    (hsides : OtherAndSides C D g) {w : ℕ} (hw : w < 10 + D.length) :
    ¬ ∀ x : Fin 10 → Bool, val D x w = PEqualNP.Outside.L_meta_2590.edgeFn x := by
  intro hc
  exact canonical_dag_exclusion hS hB hg ht hdirty hsides w hw (target_of_computes hc)

end Generic.DAGBridge

namespace ResourceCertificate

def search {α β : Type} [BEq α] (lt : α → α → Bool)
    (xs : Array β) (decode : β → α) (needle : α) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if h : mid < xs.size then
          if decode xs[mid] == needle then true
          else if lt needle (decode xs[mid]) then
            search lt xs decode needle fuel lo mid
          else search lt xs decode needle fuel (mid + 1) hi
        else false
      else false

lemma search_sound {α β : Type} [BEq α] [LawfulBEq α]
    (lt : α → α → Bool) (xs : Array β) (decode : β → α)
    (needle : α) (fuel lo hi : Nat)
    (hsearch : search lt xs decode needle fuel lo hi = true) :
    needle ∈ xs.toList.map decode := by
  induction fuel generalizing lo hi with
  | zero => simp [search] at hsearch
  | succ fuel ih =>
      simp only [search] at hsearch
      split at hsearch
      next hlt =>
        split at hsearch
        next hmid =>
          split at hsearch
          next heq =>
            exact List.mem_map.mpr
              ⟨xs[(lo + hi) / 2], Array.getElem_mem_toList hmid, eq_of_beq heq⟩
          next hne =>
            split at hsearch
            next => exact ih _ _ hsearch
            next => exact ih _ _ hsearch
        next => cases hsearch
      next => cases hsearch

lemma reachable_mem {α : Type} (states : List α) (next : α → List α)
    (contains : α → Bool)
    (hcontains : ∀ s, contains s = true → s ∈ states)
    (hclosed : states.all (fun s => (next s).all contains) = true)
    {start finish : α} (hstart : contains start = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    finish ∈ states := by
  have step : ∀ a ∈ states, ∀ b ∈ next a, b ∈ states := by
    intro a ha b hb
    exact hcontains b (List.all_eq_true.mp (List.all_eq_true.mp hclosed a ha) b hb)
  induction hreach with
  | refl => exact hcontains start hstart
  | @tail b c hab hbc ih => exact step b ih c hbc

lemma reachable_safe {α : Type} (states : List α) (next : α → List α)
    (contains safe : α → Bool)
    (hcontains : ∀ s, contains s = true → s ∈ states)
    (hclosed : states.all (fun s => (next s).all contains) = true)
    (hsafe : states.all safe = true)
    {start finish : α} (hstart : contains start = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    safe finish = true := by
  exact List.all_eq_true.mp hsafe finish
    (reachable_mem states next contains hcontains hclosed hstart hreach)

lemma array_reachable_safe {α β : Type} (codes : Array β) (decode : β → α)
    (next : α → List α) (contains safe : α → Bool)
    (hcontains : ∀ s, contains s = true → s ∈ codes.toList.map decode)
    (hclosed : codes.all (fun c => (next (decode c)).all contains) = true)
    (hsafe : codes.all (fun c => safe (decode c)) = true)
    {start finish : α} (hstart : contains start = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    safe finish = true := by
  apply reachable_safe (codes.toList.map decode) next contains safe hcontains
      ?_ ?_ hstart hreach
  · simpa only [List.all_map, Function.comp_def, Array.all_toList] using hclosed
  · simpa only [List.all_map, Function.comp_def, Array.all_toList] using hsafe

lemma search_reachable_safe {α β : Type} [BEq α] [LawfulBEq α]
    (lt : α → α → Bool) (codes : Array β) (decode : β → α)
    (fuel : Nat) (next : α → List α) (safe : α → Bool)
    (hclosed : codes.all (fun c => (next (decode c)).all
      (fun s => search lt codes decode s fuel 0 codes.size)) = true)
    (hsafe : codes.all (fun c => safe (decode c)) = true)
    {start finish : α}
    (hstart : search lt codes decode start fuel 0 codes.size = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    safe finish = true := by
  exact array_reachable_safe codes decode next
    (fun s => search lt codes decode s fuel 0 codes.size) safe
    (fun s hs => search_sound lt codes decode s fuel 0 codes.size hs)
    hclosed hsafe hstart hreach

end ResourceCertificate

namespace ResourceCertificate

def searchIndex {α : Type} [BEq α] (lt : α → α → Bool)
    (get : Nat → α) (bound : Nat) (needle : α) : Nat → Nat → Nat → Bool
  | 0, _, _ => false
  | fuel + 1, lo, hi =>
      if lo < hi then
        let mid := (lo + hi) / 2
        if mid < bound then
          if get mid == needle then true
          else if lt needle (get mid) then
            searchIndex lt get bound needle fuel lo mid
          else searchIndex lt get bound needle fuel (mid + 1) hi
        else false
      else false

lemma searchIndex_sound {α : Type} [BEq α] [LawfulBEq α]
    (lt : α → α → Bool) (get : Nat → α) (bound : Nat)
    (needle : α) (fuel lo hi : Nat)
    (hsearch : searchIndex lt get bound needle fuel lo hi = true) :
    ∃ i < bound, get i = needle := by
  induction fuel generalizing lo hi with
  | zero => simp [searchIndex] at hsearch
  | succ fuel ih =>
      simp only [searchIndex] at hsearch
      split at hsearch
      next hlt =>
        split at hsearch
        next hmid =>
          split at hsearch
          next heq => exact ⟨(lo + hi) / 2, hmid, eq_of_beq heq⟩
          next hne =>
            split at hsearch
            next => exact ih _ _ hsearch
            next => exact ih _ _ hsearch
        next => cases hsearch
      next => cases hsearch

lemma searchIndex_mem {α : Type} [BEq α] [LawfulBEq α]
    (lt : α → α → Bool) (get : Nat → α) (bound : Nat)
    (needle : α) (fuel lo hi : Nat)
    (hsearch : searchIndex lt get bound needle fuel lo hi = true) :
    needle ∈ (List.range bound).map get := by
  obtain ⟨i, hi, heq⟩ := searchIndex_sound lt get bound needle fuel lo hi hsearch
  exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, heq⟩

lemma index_reachable_safe {α : Type} (get : Nat → α) (bound : Nat)
    (next : α → List α) (contains safe : α → Bool)
    (hcontains : ∀ s, contains s = true → ∃ i < bound, get i = s)
    (hclosed : (List.range bound).all
      (fun i => (next (get i)).all contains) = true)
    (hsafe : (List.range bound).all (fun i => safe (get i)) = true)
    {start finish : α} (hstart : contains start = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    safe finish = true := by
  apply reachable_safe ((List.range bound).map get) next contains safe ?_
      ?_ ?_ hstart hreach
  · intro s hs
    obtain ⟨i, hi, heq⟩ := hcontains s hs
    exact List.mem_map.mpr ⟨i, List.mem_range.mpr hi, heq⟩
  · simpa only [List.all_map, Function.comp_def] using hclosed
  · simpa only [List.all_map, Function.comp_def] using hsafe

lemma searchIndex_reachable_safe {α : Type} [BEq α] [LawfulBEq α]
    (lt : α → α → Bool) (get : Nat → α) (bound fuel : Nat)
    (next : α → List α) (safe : α → Bool)
    (hclosed : (List.range bound).all (fun i => (next (get i)).all
      (fun s => searchIndex lt get bound s fuel 0 bound)) = true)
    (hsafe : (List.range bound).all (fun i => safe (get i)) = true)
    {start finish : α}
    (hstart : searchIndex lt get bound start fuel 0 bound = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    safe finish = true := by
  exact index_reachable_safe get bound next
    (fun s => searchIndex lt get bound s fuel 0 bound) safe
    (fun s hs => searchIndex_sound lt get bound s fuel 0 bound hs)
    hclosed hsafe hstart hreach

end ResourceCertificate

namespace ResourceCertificate

lemma chunked_all (checked : Nat → Bool) (bound width count : Nat)
    (hwidth : 0 < width) (hbound : bound ≤ count * width)
    (hchunks : ∀ k < count, (List.range width).all
      (fun j => if k * width + j < bound then checked (k * width + j) else true) = true) :
    (List.range bound).all checked = true := by
  apply List.all_eq_true.mpr
  intro i hi
  have hibound : i < bound := List.mem_range.mp hi
  have hk : i / width < count :=
    (Nat.div_lt_iff_lt_mul hwidth).mpr (Nat.lt_of_lt_of_le hibound hbound)
  have hj : i % width < width := Nat.mod_lt _ hwidth
  have hsum : i / width * width + i % width = i := by
    rw [Nat.mul_comm, Nat.div_add_mod]
  have h := List.all_eq_true.mp (hchunks (i / width) hk)
    (i % width) (List.mem_range.mpr hj)
  simpa only [hsum, ite_eq_left hibound] using h

lemma all_and_parts {α : Type} (xs : List α) (p q : α → Bool)
    (h : xs.all (fun a => p a && q a) = true) :
    xs.all p = true ∧ xs.all q = true := by
  constructor
  · apply List.all_eq_true.mpr
    intro a ha
    exact (Bool.and_eq_true_iff.mp (List.all_eq_true.mp h a ha)).1
  · apply List.all_eq_true.mpr
    intro a ha
    exact (Bool.and_eq_true_iff.mp (List.all_eq_true.mp h a ha)).2

lemma chunked_index_reachable_safe {α : Type}
    (get : Nat → α) (bound width count : Nat)
    (next : α → List α) (contains safe : α → Bool)
    (hwidth : 0 < width) (hbound : bound ≤ count * width)
    (hcontains : ∀ s, contains s = true → ∃ i < bound, get i = s)
    (hchunks : ∀ k < count, (List.range width).all (fun j =>
      if k * width + j < bound then
        safe (get (k * width + j)) && (next (get (k * width + j))).all contains
      else true) = true)
    {start finish : α} (hstart : contains start = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    safe finish = true := by
  have hall := chunked_all (fun i => safe (get i) && (next (get i)).all contains)
    bound width count hwidth hbound hchunks
  obtain ⟨hsafe, hclosed⟩ := all_and_parts (List.range bound)
    (fun i => safe (get i)) (fun i => (next (get i)).all contains) hall
  exact index_reachable_safe get bound next contains safe hcontains hclosed hsafe hstart hreach

lemma chunked_searchIndex_reachable_safe {α : Type} [BEq α] [LawfulBEq α]
    (lt : α → α → Bool) (get : Nat → α) (bound width count fuel : Nat)
    (next : α → List α) (safe : α → Bool)
    (hwidth : 0 < width) (hbound : bound ≤ count * width)
    (hchunks : ∀ k < count, (List.range width).all (fun j =>
      if k * width + j < bound then
        safe (get (k * width + j)) && (next (get (k * width + j))).all
          (fun s => searchIndex lt get bound s fuel 0 bound)
      else true) = true)
    {start finish : α}
    (hstart : searchIndex lt get bound start fuel 0 bound = true)
    (hreach : Relation.ReflTransGen (fun a b => b ∈ next a) start finish) :
    safe finish = true := by
  exact chunked_index_reachable_safe get bound width count next
    (fun s => searchIndex lt get bound s fuel 0 bound) safe hwidth hbound
    (fun s hs => searchIndex_sound lt get bound s fuel 0 bound hs)
    hchunks hstart hreach

end ResourceCertificate

namespace OnceResource

abbrev State := ℕ × List ℕ × List ℕ × Bool

def values (bits : ℕ) : List ℕ := (List.range 64).filter bits.testBit

def pairMasks (op : ℕ → ℕ → ℕ) (a b : ℕ) : ℕ :=
  (values a).foldl (fun acc x =>
    (values b).foldl (fun acc y => acc ||| (1 <<< op x y)) acc) 0

def mergePools (a b : ℕ) : ℕ := pairMasks (· ||| ·) a b

def addCarrier (pool k : ℕ) : ℕ := pool ||| mergePools pool (1 <<< k)

def live (used loc : ℕ) : Bool :=
  if loc = 0 then !used.testBit 0
  else if loc < 4 then !used.testBit 0 || !used.testBit loc
  else !used.testBit (loc - 3)

def prune (s : State) : State :=
  (s.1, (List.range 7).map (fun i =>
    if live s.1 i then s.2.1.getD i 1 else 1), s.2.2.1, s.2.2.2)

def sortedInsert (k : ℕ) : List ℕ → List ℕ
  | [] => [k]
  | x :: xs => if k ≤ x then k :: x :: xs else x :: sortedInsert k xs

def zeroSort : List ℕ → List ℕ
  | [] => []
  | x :: xs => sortedInsert x (zeroSort xs)

def insertZero (k : ℕ) (zs : List ℕ) : List ℕ := zeroSort (k :: zs)

def basis : ℕ → ℕ | 0 => 0 | 1 => 25 | 2 => 42 | _ => 52

def rightPool (ps : List ℕ) (g : ℕ) : ℕ :=
  if g = 0 then mergePools (mergePools (ps.getD 1 1) (ps.getD 2 1)) (ps.getD 3 1)
  else mergePools (1 <<< basis g) (ps.getD (g + 3) 1)

def groupNext (s : State) : List State :=
  (List.range 4).flatMap fun g =>
    if s.1.testBit g then [] else
    (values (pairMasks (· &&& ·) (s.2.1.getD g 1) (rightPool s.2.1 g))).filterMap
      fun k => if k = 0 then none else
        some (prune (s.1 ||| (1 <<< g), s.2.1, insertZero k s.2.2.1, s.2.2.2))

def forkNext (s : State) : List State :=
  if s.2.2.2 then [] else s.2.2.1.map fun k =>
    prune (s.1, s.2.1, insertZero k s.2.2.1, true)

def liftNext (s : State) : List State :=
  s.2.2.1.flatMap fun k => (List.range 7).filterMap fun loc =>
    if live s.1 loc then
      let old := s.2.1.getD loc 1
      let new := addCarrier old k
      if new = old then none else
        some (prune (s.1, s.2.1.set loc new, s.2.2.1.erase k, s.2.2.2))
    else none

def discardNext (s : State) : List State :=
  s.2.2.1.map fun k => prune (s.1, s.2.1, s.2.2.1.erase k, s.2.2.2)

def combineNext (s : State) : List State :=
  s.2.2.1.flatMap fun a => (s.2.2.1.erase a).flatMap fun b =>
    [a &&& b, a ||| b].filterMap fun k => if k = 0 then none else
      some (prune (s.1, s.2.1, insertZero k ((s.2.2.1.erase a).erase b), s.2.2.2))

def successors (s : State) : List State :=
  groupNext s ++ forkNext s ++ liftNext s ++ discardNext s ++ combineNext s

def initial : State := (0, List.replicate 7 1, [63], false)

def listLess : List ℕ → List ℕ → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => if a = b then listLess as bs else decide (a < b)

def stateLess (a b : State) : Bool :=
  if a.1 ≠ b.1 then decide (a.1 < b.1)
  else if a.2.1 ≠ b.2.1 then listLess a.2.1 b.2.1
  else if a.2.2.1 ≠ b.2.2.1 then listLess a.2.2.1 b.2.2.1
  else !a.2.2.2 && b.2.2.2

def safe (s : State) : Bool := !s.2.2.1.contains 56


def packedPools : ℕ := 5550075420794841839682421912261757993941636734918635287353835331646302001384917001603538493913493631823792626019837084842688813334835066542904526257658335621169341213253049794050696321756558892687041475381189315053184503791994353987801820046268656285365975015728998118936687229540508598351166300768911942419004027196773401855383470572147169717093109669679453487900832609238164485498203160142087429607134546095272390353387070023794634000942519122546976962584219139896778067695287063424926324705158712154477719257348158105594791239634024998823983976224301483618644164084360213625363959207567208917657965951185663104757678436882013427120840514347937826850868403201765988236701044160246496775385866942381236402749727619384291648345593507272413181868622586975018382718974217117031313124632155431208935374738058771196890002690366803945012334492287442282195464127136429306201599982789358238401819849621039888492050605570970544561086533195151289493549299314545316264589625412039586576539742712929455823872028243494476551783966896913651359621665522003527860955181834551831156611424092745246996183443826599642700589287224442478222659843730920982624146386176717091944014542151365613631118019446270348781532851117087865232582478976626818704780699720040055056095855865338193717427172242324768313263251903171786986560552834957222635147286083405120653334150358019071812398821655345379102188653445539484201484689461885535173765567658819691705315195905727822247010708788198388187921258665130020332713828408704110109314745323985998983226977561586623277772598048296633507612145899728661343102893384122301260158560851769050876235162819162077846442005235169927538235350401941505

def poolLookup (i : ℕ) : ℕ := (packedPools >>> (64 * i)) &&& 18446744073709551615

def decode (code : ℕ) : State :=
  (code &&& 15,
    (List.range 7).map (fun i => poolLookup ((code >>> (5 + 7 * i)) &&& 127)),
    (List.range ((code >>> 54) &&& 3)).map (fun i => (code >>> (56 + 6 * i)) &&& 63),
    code.testBit 4)

def block0 : ℕ := 1512413376021155008397119033671109145715756333709387633431784722895437467230522976330459638141602574828987446186332648978037995725262244535022783804707462039437934101745895911591074381224539955571488491355740767866571530311101103357134701510002125751657086747496941724941048617143324439687782858083584379320070485844034804524824795778952481959490754761473508144395248714654774964870043731637794370285391679925367264705245413946966187600253230132943362120152339686218029555972737441777013787225143696451654417334728195805140819189409015057087858652211914283069753185124641822590618466439764548501937710681576399331426629134313183788767926101123484330041747495037500140411307014954870836690905046889597596115625693230601532370512661705411225396597825167836957141411033316208672039134484875169892296336837439766249847851755633112363938396936668963316649733260746426794725522751806113289973446967403789122602946803757712216220647453286431515768805357304647859722639705706438531582958742412852301238884621691622163940947825273767021152634643617795062162422232089423270736338615341968491861092680909595063735333248146382995249734406527068458024637153121240439647295704518638242191087890653300113950193666372919086712566180108178250093208470881717625519697814765563434805284136354035666110447632594411454464

def block1 : ℕ := 1512421767772021180916831768598419910964097214289503585884876586317893129575774942669208032498605137286122851376509911471445410819430077065381619269123382502962425976797962679756239024187747886506357575146886851311488386812605269015069283491120438974441272472705755441445719278447241233619451129771903137274985013532886177310191821825857757676523978464871810568994146002803485095690412334276190011108547696665027704675725437821331665698768808892190207891330537106047808924311479339276398904843913731369147826696311552245196814802894081061526537409981576410253766358009788868272291500420814024261595960769686070912826666996969791825191305344127252817301791962132896334009164344411883916342712845518026333038025159486270255647004344608076019211166557655890433821860396153706701058439818142542781302269113668278600721804302414359222126584953706426975381764227229594703714987062807825426542205112677980659666997601095115852205298197498998290616454043347291222142555794040452520602015138737970792373178550128904115895145577615745781567368231301501924453377291470963554494265003913353481686458807064074177128270936967811530566584154933257404362770095493415074822110689469302624858891674795900488442515823965726914590306644865951645035453022667564640590983155766663977885660291112721837497108224381753716753

def block2 : ℕ := 1867418734768426819568626954826784594506778326402668548746340305880989691521560531405148957924884842886287585204400026871564512141330649245138380670969610136877375206923786268318291363208490058533031860776249440681306062842968486670236169108106195588683027347582609175486627273166345625694949537238785649294094748779863816876449758088987715701170777551002497548321265084457630098771376428647619508188427904470936604500879354529066782487532280853442416509076911562875301956586005336414727087065629902036364859355796777176506890377898019736385839821381593793291332274766000550017504095572327591789974448031609599625321041174356378269433085939497190522495180978647611609732344077998211251194392148695571554739089913028752621767887938283388508252961218479123325185796944182613717635997502665163655294117156957036101105677059510751397067674466378874437499187951315369673626414338068824463096013411460189608153292994410997460879780072913800579204868257230216549421983393259612731397596326633920984560781852429967980146470855195945676775025696583575141937642498162821050343067955671827690734276469828038147411224307744583919388493334538871686292434674509062881418813812096846854333714546982172518102187680651956263366102119837270201113824382062695604205067429270974666949604085380643925338627806597246398205719724050

def block3 : ℕ := 749643155116712503350870887557020507113248882903921053569017967402228577581634204713180424889719677133911448891131382609627985797848580134389155792649552747588077488170010610633920020244245604463875693942453843330297687540377767108984713835678192016610860187200174703193302910476835122660640558832158977465580872197258741261530373609923639068645428601546696027003356771634634539114723496162565764462535155420696991304721844087399803330701678227244419366106310839912170973710427573380466426075524080522011932580338760187448172579428018643829796083155910023271249526562667775813082777742930064500320856442071100884516998647394511381730352375482660858061734821058847727923911085298917742158651053239294378985474226664834797487508321359054185612546332076579435240719845067684143691937702985689863307708823530573738176764584252315467938466568962269858992512266825632717351587259390414858855972348296871044800200207297143335247513186887518914046497733168306709349586823209178919738760065896859882001662190897381846216066406860422616682219264422750761542290972213510153664489501032796871597963779834047840050103011660684866981849429564300899117748939713132537855710763306902730718412001299454783082504184549159286146800858112340049198595863190421417817213415955018476111766001294959673360895254848304696657444883

def block4 : ℕ := 3171567502103354522420315717043062945717715003212321893132170410507435287880842781950781167984462844692526672016377344073902112070910120452005165425541737519229329416135042617097451804039540635768923595842362931763776944375443350304294566552419957589176772686018696924248936257081236548925487858052615228370874781362588692848704819951397014596074527111522870375239982414622599447359450369537426423536135490776731238444205481180000758147193434849699081785140848848455145227897753683187679410882405817056100985763006268792130611133904613312254697709399719265240901138756421521828233236349535217197558118682816516921968926219504511323276284599245758003835494646473400922190833048916737533148406326249214634382909643420483669673066095590417604819527098194558345093579853654470140122112181405546599339258629566924773645598154583256378977915899481884148118524413945563174675611065652793233567026858886631222653284857950260647727005642623190668636385066761108359856511896107785994659435625381291560455456431576987427390241771417451540169042717496165271492849402660793185646102058769203817739618487477175185125633485256178596216262143171167280571333762504182286035071404700011907140027655225988630917950691571401025934093962893248118905328757766406512982561752782836997297162645010712241069873908669214923177906196

def block5 : ℕ := 1867418734779404373269351427027827099569468119418645026977559248956995323641939647930587816638761429643745975904317703179379393981106006142242764022627853140601589893859602054971976407971969331755234953388402040529817061907525174802828323082665443047388164302647504878999461460895658981361789307886089933327622082501743523783239876607994256908301303628686710208448246618333495538090576436530801026055117403318285914997059495528401853983242843058026338165800775196500124811782397205656882128779733070920844152832482906106003666282640897942594985825167510156231609118492236211052447370324221429471131320584868731681701433794537129829194480902810395032607498052114872992949187311737892639771464568351629525977761161296021493824099204033126091402790073634197339137341047600521479074017022008515924276198021953509367199731578229094702440968004708523232409902063815108923192961791180329592915989970052941840778028291985182085404714403136205954482392777886846144544372681937636941330026096030034679793460080193856074573589550883745362053205518957607866210367858198275409249739243080208769812110026358165171665583811106667143894001826321655648880901380209602054786773564534470784132174312950230266325921929210884368589518587005426130128553849991723638370989458502581216956927522490543737356847915767390172122494009365

def block6 : ℕ := 745491273564632704918505366580134915837158405805385048426291073569589112332604850425759687374550779203415880096528357344944352574461605417802111710112212633984917264673015932049467680860731602341276722802386039137556012079069616026864434256776935164172083540510279415783665365314436599335862208116991545627835706813250329336176901219835451253423435465815149270345516870860224456377900743857667841362444686623305741491372241493586952953165394511624435932577302167071760315156269072451035421296494880228331580286698181645471534306640400655571947810934492234587244650812459624783352197809513615444893471123690189732608638846949767441911995401134997765150909688224269995760836486370319712319593096847522575814626322816057640956510660218552547697009833273896666824999292337330469240425815254148526945605526316196137981264015259224596098541407545623469270946185770639106712339633424206411072295753089143409953538226461544668403840628753672934964236177971779196872179721962212248805730998086341368005551920378273394211931074042251397188804115862676972191959612088216314671681048578936419646571167462298649927090543843353095333172552987075626412970643388396807370771008956910804101454892291568824383440108266228508905186974111522648874670024257201377525850856244942713298526536381218391367588713840818537133168971798

def block7 : ℕ := 11915713422597571658398259679164063537842849245383702999985695803433552105528333862736346840000140055686709076837855762745767120638557525011855062102725663892464631549385131486488753020286873072516373320347592636450485222000105145084448183393482689803636558502221233146918753173092335189914680461371440739909154171658930934386307898049767507504912365721500942230478402712092650470310959203007694674480319444836474392386112720278070448379513386824382792300814041742813194418386196372832084841575818308876297600947592632292126416268931974325521525136053364174997386173262352717973376118900860295711456378225796979366732883703711691759472457790345232545172307452156791097934606088835821617781589811223691718318479996579509689843625388513816480557768184542050475671336265609993969621297866173143405366598704807093756390827077111424690131848967767015601167688574770269733072066160876679513651814051918153399689986069196430333447718707069679121132565607736941118286615323496691184792943538686023390310088236155231999841932294204933865285325373154805186032851250751687956816712009036794409082493674916230717284422102665805145067675073370201359507213233587762505896047462317431178029583383170356686596753718566143052730258807318543854179056677346674737138420841521996188444973635671196868790974389752655894

def block8 : ℕ := 57664869012380535164398384148376152888828523593264181162306431694103742790902956926611049391409225035749695345189202781701090282691762428180335062869278121181810636528412277707752690379892295265606053444494824720772990392141553121424928457151465089374530084805624007278720854743840723456157021626819689166392085147771429018712131140952746572967687231069636278916239358264071463659085700404051732033192016922319610030013016739177544121521548325920064800358031986105563832377377323886529067040673260218739365165605580997885541762916043893027726721224578387991256573124586363128582157200347733743199363061367341189367903206713539216762114400566145236174644340816253046056512527898805980292823868620871132884002604851160993392497750151596397032912159015703173171770613386795586742635958202514975847424756411125730888097584870079297848349330799894907962336890117496854611751923868437915314637535472394405682065264054529182184338882145674695049850150280469003603724944955489028014164573868370060285643102940478946634548143288232717205832943892821738757822849373101259867587431996213112051352463147949095218002759165297864648223860369494863873031926835566215261134667283045573710497626237679249764086198675295896668705883083242403711079800354849503393806103476759747881685193138677225718823759290498442313056278

def block9 : ℕ := 1867418734794849476167968261875526025030005732473071807073994105022449827590296841349073352823772808070564471349384468312812309391008153660215004179808711565560339464290061107542712532242010555899432542170995916071708096352788942678272214766721768103325256766175201643702059606686703600954054671261860348520032706400316970323183418031866790499703386437844553157610938655095773200244938345449370972427992692203225467109656807731271032940388532700703253557863035855728394490063095875545353400158712961490774288151366010905074897549690913958467506932822863314637081276729284595957716668268151527145319758784319114245870707046665110881026007921242512354819928985167802420464415195483224036434423667631597794986573731959606938018911949179269571248216749708021627004941486847186761529780603371582548027923629587076749302246980454882220305923903936800772137439921669841069450767065617996907439866769057069210344021522584022510780034421174561000256952884905239093497904598668384762421788640425092016487700876474014515217600988177811389886886986680522612309836496715275485014060429165267038493928415009244490247999677973627783975682874739181919916039402562588187289511896771386288537031137115776978367445380911963701165754408540575037740802745211112668697250755299622376704115754581908085416353298889516845881798218166

def block10 : ℕ := 1524136082451698226347236673764384555952135410671776948665513311429045730603773825105266248799315608841617416811260343586073689926620967639348721414317531963310419500403689115857201391444855180127436473844971288600393237459001286852800789198535191150175508630489336231823684147529578298078460659869678410031434584363229898614206859310105858579349864240198077913128173880646015512783477496560323973087745119126567090408522736587417727046027392433207807021153708265345984105919207906171396121513806525949600829165213295871741266389046551430512732950008959284857232235224910602360243486364986881122044419897482317993175776531867964428388572497576224185530785392282777435629526326138181166877427520322635294108908491502356778533322818448869327429820539652099257019139055143965981912571126195102205813599123922776202918112241927514424712127452429377804346635172537497459889713699796693446709518050671135954782536768146747566453344083485297745764552164680645941404732111578400140241825034654973179516996041937378850926427598174516650045921873202420240054997307117408905790943582499956781861055557831560295744454573414419169842282567310388182073591169000771047777663627002982369325166550220580489948514193049601306998963918918367417916467130036746568358927393145908040226199806519008690784734969829475221527

def block11 : ℕ := 24848259988910963616091038682084544612732743758225699236187537690726033805946095646978613733633898444253917739893724143757763586009765544277517386864237887844914062326796794894665329728676676787260360820649283569501315144014302855716192104484000280166517187494364211926402777298508201467670079250803378158547145468815346658084296521585294404761345492475971597444385226425903360415036959215753945465717614287276832973160543865532991644701600757978882524025153584287918840025616833120220583524800643909780594334837427520057673781030277779061436329821078760517493013952386854090939065669480912382803031761349851218038233668497668135167786300843356798426947155795135323675426552622218699567089816838738893829049771743489062168130827346841482472619187546480178613080025769818273247410168623686465786569724065292676096812659987587324305401342182989372575428051899244560569521881288987175464948607039267405229971895035028613108923227950085073637830907718209718219329313392063628400176122588983050873064192657697831864358885212022900863480786620068961444656932557829979137675292502483986475812434303563071721729590679649262779462798284508753635851083755536658351920224010643850700372954923043734226394886905499053076644170260898278736155301444896738795210252436721569223085362996283690412308065193375226045923352

def block12 : ℕ := 902965695951540155367120609183495779155660719892170792910065421621740127309646154805881211091731981288365125867259277581363535710401782707810086317688132997982368059817307294634721095901367125577347588748084620214271183446913569770871226692317325749200627821023453061089411849983619193631371101585001228969150369590009329695872015628901055713178779291085872939762219975089542074370728990530310923062724776749266305124037036671044990377410179368727929222023663340978375764888398177995393523112342007558783723549786248341299413050868938665315977011908544712940674556845727141827383845704211768560950679970995981996464646209932670366495204519066019356472682032089517313582733326605028192906907467623817711160879764886494759993816554278042117637349705427704700966701829819126626006947682888657753832331196359371111653744803863764554803487370306964136438485477041743623894752726573084016850281673014033906762277688993694971002844800465568141218837366825089606929727930577910059892435838308945420454325688431159981152747360995237149927887337589440470090383472390064932677352374675470824435709153171354515875750021796279198147285659406832590799463226289185678517299167338827707055030265077169990649189262608078380256336021035481353792670471246912448179947452662664627706345063275494946302375206977058654650393

def block13 : ℕ := 479771613211535620054809579853592626053772644631661192984466007109016250621713045919958493019034115680822423704950569677671177330676784737582142276140115840907684653676923913160021079219733670546953133851984635998090808061622717133112102197160712945801574404965368826534255227684651421823923415753955028317604291389603305440038543412124433922800546752374416232373026906280311515748548980788945653188873156774745411185297699855616369307141020259382268594161699037326673103107366792341247650908017542426214408255273970970217133291763751770117853846072661617436058232843457718872983095096620718003712418073215041755194629861407188347457745262022351133728752924509258260960835747092520781300918085949632521006170934619273764937091893959324620211397970290968569610687663851722722401889183722178101237791517733673097577338921903328581134259782562675450196428419675501718461026021555187221886997185003603562956606931000526203297651059355329899265836006771307935377140138190736736059871403855925732400859613007391025569430351734182589131204553116569855113302746786212985104837009080337430263020088502594666257543081722417585437966309762789712736808056219976967817223019106746087513694379398036940899346546124302058930343690112929124826303231148899450098043777395094433166915778331181492271473313042679860051572768794

def block14 : ℕ := 1512416736245209179228117606456171524763589800667964441420499654077392646609196180770121008926168790883306968223265823878036880425369565717985157150156243979713869831533315445445675788361100970666082781154889733529913744209260175124141153840946202565219381514549693076853268277732050008993494180400943883342420427164632555183121912933639468877380550325731235564353533986091743773384398703978258000890258968181642166477631559094223764566914276708006427634385182476252445571836120540373953162565767552410878821400842112896646406250389733478494563388755691459783657956572639748835287426352692748915051488200565263972744916120616156360954632135035946625125893277009645496609103320791206991125563579102841764255574860931495245133582234052372765272529567409873710823143085123694481337358669082283323541209500914562842018588323299173813261565463628313576326917630460814496258731105226522136599111053290218895733789310419280017484416245104915253005750392917783063718370245009394381347009109823380137688512504147372142687258658060612621839459281080140458397850695563242213978259374128407522506927453092618501562966777049063211752045335202593012084792239900994593311608885875458119586504470672016801170336618562545800662788488487281536789224039806306581873476574590418614461292178218537108415397510689941843994

def block15 : ℕ := 1542650260668052648840342215047785875667671249044881515971879739005355442816445242195408199397616816485045173871510353729097731573304679411496442841219816336672133351844394432980805576405347867666045703804079995054031870814407830657835697305646659794142813956677672642791807816990773770781540758192104155766679420082622777584155557370953304832228712362719571595641956628829973668605809083557517673430295210548428985073906387496264960705574458922031746975906975482037911624462363742218033704078658309750491088816893213863528032086807644339688558377203001545976125433662930746688615049265779889828441147627109075864962376509432242077096588547982279924052556195994388186589127292609611860463652524597679038531736822248357624252406422181596367222414241689930004414460606822788506155608137250026751817022746211549988141601414109056318131846019199863430846989947001416625656530022666966286308038550768893365423342850789627140306014343275246160763598607410249378512219250829583422216849167705297700016030034200059778040051096903730955334691789065382971540116555051909954588925746869051720861608061526359178702037003883054320670052868725718065732414657132306904211728263766736931619547440242425419395793614632853003967716233015444252375884145875313448836281583635227233507634485862754539773755814322754913806231769114

def block16 : ℕ := 17569761170633215159706054916731965431804041768756242643614959043771103946471377736763314165333473616115652982848280785467071042407386720605379045182582657645782134699350059178204331840890958428541614800417549912546336507811752596914284440106347130391994313861392161337760319990975264592944770310170522955039614497474279667324784097710786524504360588141531356246975351729917997328501277683129985352898744523570854872588178785483009845098322017580425659608546487615552764322372746311228216101938463121009892062837485263736510078560186099128481525007789556409031352238951397026517432472819769226574862907180679090383505601611001401049646354114849666463196603148193496964621730706085827555375900631898955204351987680860258916111409123497229856258607460378446487123718244648259809178527805013169507997549002089962002728704272741003823043793901687137052477736751148533131755471085153342682462073481897759356240509301804973829694474141783681725874016667467213208010006173871155737953015499467577974668441288586877067890517442948935415185554441756135734243971072836943930504670863785408060415417330783829338774025766142930263371020218723029676655801990000371000512038670965566455154868185436470075415413960555537533137084478267184525945691204337478153531852270281038128337426052669663004357164459323411556167866

def block17 : ℕ := 2011558881662225884772957660384252018656778186235966118757977657550052525016710193657851807137313581217471211640673675954826058263337013525743328263586722629409241397596451248098906990923190967083389664041379669536296228553877298622566478034240492496614043468231823449388078746416982447350817723900863322662907237802113323222824358140013793116722895788874736332850185033411742858831108990641923977275525047275269939407438111660570118295090198726404671576537033621512483071499411246154790713013146621727077617288180204406789789791073626555538121595474039098019992418128924854402667383644028606872824961912929308661186740203504350587098289716237450451096686450102009101474045801851725751456211184048871228623565205834154936111968916421669160999261231618094105077251867548182935202737678538080571760091796923794898925834296364895105667913379171760114017522981438546708087899630717686746277301326508161441760946511450700619729651538551548113970342607938316523441728267346128582799431802334679513750277409024720198005277912286023351386286424234831523422183877897705176620403935592575044871694686599688474020116585355115529689757246579154572645989621236317436400038975689118757460252508592942046677130738741828775528785240721952649988286806271480647221272194784065383617441563660630912150569814813248061467

def block18 : ℕ := 370991266003686666387569751120660689411945182794794562077014579281560099780617629235262655733513064903305322442677540029246385084364213513833723686342913545475831757707428378044634324514586248333874148354063389824975009744192897183433276046197008368552072358478847218395249935639300554525472936338778191248477455092567264201396474558407535439506163956101047378905652050784204540760327583638921302576973809565077835125828473680730099521255756408683507860250361782125032028672754681370518911907052152864828768358004850945891336727291916040783601023776941458221080867866735681987167703951141033499860351322431231188328122296802122855862551122911724667765969607395456777642012387565089160180893095720326301216575652590548508281775971331013186072579330683563640097883747437905032391217660674820052328453122444076032894485872108914381801495587217299032823799490580587720108352659673243440430572104946688056518377287886799979904345850728217431940124342276912432842417602813416769330654134678038329131152866112273654078820033163973020148929926824530764573716335160706440705244570281206516271426122311961623070722879917307460005887701570492524012464777282435655373991148915951748661830946531581151384790213985241089350790927234800245742619059350222991335178470188167178735516690169310996193823467460677861388

def block19 : ℕ := 1527594994905538989978780263876153182074882782064531955095806462838757670892578055801208230264148707732270837839528951605551937497658492223146944201936453393886427460214545038311904062302669926770494861706610921992275062633024659210612737350304711745442061276038590058306858772846593777720353619673618340462068839866180623431651540078360972495558745294761854814436778750008037191169852090267511395490102798903117964283437366601419819045132355568097992063341093771778026311593946348095058986894925416159658146959877770902195028557798150890780136730202252535240815667116669016485455794405016819513996879511908256963086893700223493912525232593288017243952673736165990903474608688241604962515568988005036572444282444801673310576349168300611483107356384554770943157609735863158244229763552645799594950071998823506457339584030960633715999451981065116921719246392416928489519380005436895813891763520603822368618173110733918937963173892861961340940959907441636912323747580958160070191385262285727654296346972170668150077266502473583596030580860490603578064519162031873393660321798566004583936434806004837808724027959158409068486590091523904516089353526849810149478580764423153368202800341729642132020593201978396932391582081324558852885214870346648000978982990301801799838939146331538190569263371015717126172

def block20 : ℕ := 71915807611204239750564829751007135454437231137656733973380657336038444820049237225095551518491640281238736910884350791105732308434188835659807173478657737396510890486873039148584344950280754156406342722134205934681360238421040113217121529421034691311507416812222014952806469413872348066057941942130196933472117040655458946400557362043436798488831403601624790114654999833200187184628023883941454402172215341665975830020573041298978678645847066120101463520792138321136549191058380513907115618354039109087770080396671833608178636491806247945359951438091630971363401807965069650987532859053583956798786408638539410873543275082860577093940043181979688940226735683354295058216215025677365022171965450842172469806310791819123147074893867100458071324288825126026494633896422185373613916450777654304396118734788382510113096887058062261929619035054937986361961785670345418103060597291172852698646702103963457847375770602284345171525663667147639298476980294023736913037106408157572846350521685967438648084397998849359646311876717256848309567555087135770316424869580101552737512972595739899234872519427619904309813424585603487459419320247114869077969437247738149720981781631864790110348487664425037407657779742463808804247737178544108974657634121305232449703577876889305084841637580820529325942090952077813018652

def block21 : ℕ := 172459594835697467567994454365320064941205721408463123330106715116944030881300272768452071869631157066364692165928668563561200201574881525235375280276765997458589728892611395226390921073737405601099116136810740025324126764528332482350059475466291332678755485192301218139554195051032474086869054569055201235628657775424954988192429018397800481120482274146511654248408294722148835835968649691848650457605342280253054013146202158138836099935929597505310724938584512840622019990145475661714722189263607311374668948644970543637481841422752128618593804690579303441494908477312579597053569246381160871640578803325000966108494297867466265607783297472695455805764613553481375903645330507256053968116370902774210701722149651204591978900233516474025588308852525757467527216482728243389684427572412615738860210907089145069208558628672743549587002418161610226239445281868268230513996939144413925860382531123863396706190933935857310319425080761938261754376601408308739231494131329259857097062146364609439114858852251520760659918670770489607948831796654645110060610831471495364626964343211974775083682120901929825575087563638002840647607108894872347927794517148187895681548215491180020680234459804992747340441507363170529582252739231665010665564012931248294438254500626302761854749452297715960036069630069974559621564

def block22 : ℕ := 2211576567990244915563044892292623100847413283878408056588530786805296387019110988414251823096098052636678365271478462760424621057736241498542181227043506530439550894285748078909954036629240226495860586452045042196861393155504269978743200458592733593331425291128877341800460383745728903548038784482874882552390879764370129124799941922738908224880206545693815788743307586797346900576945372953270803659445337211400252981853814417641902759253156108565170780830688331896838313538889856239744787765420593764677797380862160980240895201760615974078492400489373415961466225430398242292621046785484716143242089071481883644642701997323174124238968677558344831799947898327872874182076253983746155733010401925586313629678477099219581891975610991690864570865252773142072913022008064578142152435281294509236130051013433828464560718937647282404319783116163317347598443893935242696926116410836543641722052059825262457121635369084875063151295929758852398010757083141676350146201013716909211090723661075427933890220092292168482175362033457186414916063904601777670490107265991750192737305916374896195249381773890285542345173030982543949346605212271990630373482865387380254603536464059561386131764219262876109752809990914361969982375287912325478530692513094290734278272601386843704131232098811556073830113678024719204381

def block23 : ℕ := 1579163143527846774603748554167868651574771859795479502692824035612859601174075763623710744299752052829880826844597440586385893258365360324723548089228777133980589250107513620919507615911365851125642028333251603028995793138776395868196150968951902442344486433008471767973513938605174363624117974084500687564388754026257785125429737901493547356057235109285167023106846585405667755037271559454048955704430362850369396438474555660509877206088582041802292336968372982970592934344557584852500829088742878403613894322752224763476089698220513209974707895194671987372000067510893078202045596171358943685575861570572161345275224546957402883416234760831683136972366883089600510430608335225853622805472448064146081515415279140056195171881940453359383642718062605190770617089123727996345746206630022364616750661995023825046133720399096476684544349965053877352054018022787531522505474063855452296148152795773593054241441586408070252513504594309324123997243062803713057631192486663773278473001409757412819304425658676051304280794931370521301301440566551450764330972372849965446553339977899166378024194110757625162453004787803138844579172269653363479201240726848191066206867019261483285983493847621127952493234202846670893478171878603454269094562042517642042191430918574465303396426429567384273287824702773638254622

def block24 : ℕ := 193643635076942318148424254040777222715662513888510902308577318307719621267041744794750575919336927141280998449733182048474476911758623566453717433260175181914832833807101093317875504474285217689739977246602086874751197134579847061119198537284690110385968241885645320118671404513076143699671264056385053231770543634100300816700494298139622776644301706145264051990217188919162549845985435112537220771595473420546530000066120111151493303051111929655421944622882550591085438542348796420816527019375071159868928251022443537375939820090682727298667398671920469973713530780955499469148527726990568082029187445166425863994328748180502894537615996667239383592717395846218309758807581630034223356296119000458462393212077653583748064955097488959748489072000312970204293533123701701129006128277358639166437076996247461792566508807976562383251380571389083012820836289996832534138143691091172056986606627053363540062313995124528390073640599710299764212991182644157739205175379867523933622153168628831103749254296458226840144829073914024026955757293069175245525310311490175617170386130194232039092492310582140783381936729678663234594969384222351402326835671170244633024443601794928800898144367943635665985873965713317688659656682287227715913423410468365752016772746002180042052831354733889625100439939358951817246

def block25 : ℕ := 479771611848513298823861096076332564238393504798713128189408901119940414126696647208061377834198204033807987099401052152433127514907367950265836554648724211882692873646662160866541153376477626540870703879138986655555327611342312401001616884131711455412391305505758568315879148092888899007327576605809555280050805237772202535132998950486214859421712697875927306277794304986837866567909907320705229176014769444785830801001981920226600962156184603609771723432940215712914333011445225301487368630514657069800030893593838119009734220348651151851859858165793561702679573832205119591536682648424832068793064527152357969005024680804913671616582781980755744005315105861882521035240373080274014398937490157036586888977870853055919893101508068329452719425765063216811794169830328728696653697838052942951935885410651101058153554909616729603613976190919280906076000556135901525699825399712944529488887002380279148948571449946239810163429783657075123103821209636813220873979286535823464623680417268525956843967612202551993850787448768293924714583103806715540145194494330861891977436578921746137232999979680340859981194698159085443481772783670613241114874210637695493327429149364890686219516898880047568060154010632888127100485033748033545041030679935006300809054070028942524311133737893853985247455882091943765098531352606

def block26 : ℕ := 1247406190567112239913999765276145302279545603314706346005339085157559452303062913604222827616786395321113680295313173408732413381888495233269496216134224056944684525729610630259938121541626946761640496169555597460083534676105559172548456782061313948848234356448988973312639943902176627926033080577974280849185201154579310821715072115525068386885756172383732011168647636876208160782353423248277576926287009782455871874661189867121960410659941372109898234660140118793650371409239810598463305899302548597396544805309019491279215363486078133817801391366170131259347535054886924754663058081989259383388952955871481884779104896770764671149563953544282332266067239295220481264641352695015605695875736654437883408556494081966735115897569588820275523026077893967890239698047875698489653404998409109554328715769189770664163828527402180384298190798643499357709774020117059289604496650447243311169144254802545294568671022379089982305977934851487855985272460884879305488722154468266131343524017651620601753586004394284477367190641944747480532025800981392441384366136879599221355869626440771624417519129822443236190335538341130983958641458396378725862911735672200351559317763167194439149884313267599742665199144164041986897689386609247782441456587681889252928055268294963435194851675838524300254582272568709538642956873758

def block27 : ℕ := 1521220946112062739041093399579873422839828416803746504775689468693484854244230317906859944632279492338858932210511207318398742214243039231097886244729198844844018159962505198004676708973020904330971286125486050384928427825116289490392116699922951893291092518349421145248731596073415805217660752314079547593257332050024288013251813012929319322889179465314294876517864323094432558394681185224667883499472095743751453062321446712242920226574610821065716733666128910212068743374441623080660446961714000225391719959789130197185056692439440655112637458590857848113828099097072061661831792772903715119532916425635998177240378690229046729265882661274971010300509277347905006311831702262785370984134152549876409679216188465762750642812484036619903627142356094807198000205839242774470926750799671210550020172847691337961361215646853132767968333289461050462608594511871132531382502957315972354431215928756028226731643191940585973295939472272918871423963336418755133909885168687780220620362328406732111715988958361934922991308534822919924957421287487315236757549822792281229629369530691984341676488324240111905267812076651723092548107164303989903651547315094181454082907667676885451957329266417703570560054371493167949043600225659056657553807874092010662677222900003525790550070673216503991658416690760995541022

def block28 : ℕ := 1524158046623219737948959655522282124584064490649238478814028228263794479359632138750375708836338222777738668868650150165596472275878628947121045720008464891310227526404162054200907981038515174596300907126842374769724519316698209138066781151696730535820520362015255856502655190553322474358302516619832613778435860700978471788743733038245467906812458611931039528097342536648794428668932123238839699818073575938884162199319424947096721830203114686457873935062231825439069155131905828711615423710377487383409481699870956540114888460123261199152676481188388949511512813340453943749054144074254122022145269203902462531410502678833538902667223990262025333984289609451186722281004169259514965548637564797336745682648204493419602185840929011432081678852490654825470888863370807360613185783748948361306054117080306424420629951993302183685707506072169551312969452192533999047426642973970083514177865514558224293102346263392098062616544972730308042290967542515863967170067495730017395343778376765372788346354725290851226607680511856559767260456475368355656629265476345804111039659150329276902738080711743340436583351188797153970634828168774505141529107167396013837769286136193832549556117417315769792480113239457869635606061645504405012836507599878328760426396799397509208124465335678127364630077553934714245182

def block29 : ℕ := 69186142571782301908701150604262074397210840356204263568686142324637162873492231136393711872899964257237772893178145558636610296233010787399678621837016367623494913422960697590499526053736733611024624565235506026353556418007008231487410858494771286390302832931256704294470045667540614239679827948936169550997980802985580219487583715590984458356129720499406942771726768314682858033029255705462416288535960235359531978551050894625922251301618056759047329571597005351807843259092896477948771830136019469469552806880352676686132703223979753228695169501582368066078680713954349663845190643011389860264773902728422097495778271387600923156670570341246581259410829127475135504067633715008283325440543721250633807074065254604205267480251517000942207515082947475947886034035755536541232858574352667434374509006461497072023024213436091750135749443060703596214653102222807170472135869991623270336098086316886773559465505352874821445541105997114779008782688940398523305060307055450224618111428547621740790538308395821993281676775896994777244397324081253996220324028245066225000580008236341902176422301988399968155994762801368322112002799687137629203902236156819384183828987354583360216254260078474547380210069233649607627987685919078130146707240704984265486718

def blockLookup (k : ℕ) : ℕ := (if k < 15 then (if k < 7 then (if k < 3 then (if k < 1 then block0 else (if k < 2 then block1 else block2)) else (if k < 5 then (if k < 4 then block3 else block4) else (if k < 6 then block5 else block6))) else (if k < 11 then (if k < 9 then (if k < 8 then block7 else block8) else (if k < 10 then block9 else block10)) else (if k < 13 then (if k < 12 then block11 else block12) else (if k < 14 then block13 else block14)))) else (if k < 22 then (if k < 18 then (if k < 16 then block15 else (if k < 17 then block16 else block17)) else (if k < 20 then (if k < 19 then block18 else block19) else (if k < 21 then block20 else block21))) else (if k < 26 then (if k < 24 then (if k < 23 then block22 else block23) else (if k < 25 then block24 else block25)) else (if k < 28 then (if k < 27 then block26 else block27) else (if k < 29 then block28 else block29)))))

def getCode (i : ℕ) : ℕ :=
  (blockLookup (i / 64) >>> (68 * (i % 64))) &&& 295147905179352825855

def getState (i : ℕ) : State := decode (getCode i)

def contains (s : State) : Bool :=
  ResourceCertificate.searchIndex stateLess getState 1917 s 12 0 1917

def checked (i : ℕ) : Bool := safe (getState i) && (successors (getState i)).all contains

def chunkCheck (k : ℕ) : Bool :=
  (List.range 64).all (fun j => if k * 64 + j < 1917 then checked (k * 64 + j) else true)

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk0_closed : chunkCheck 0 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk1_closed : chunkCheck 1 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk2_closed : chunkCheck 2 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk3_closed : chunkCheck 3 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk4_closed : chunkCheck 4 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk5_closed : chunkCheck 5 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk6_closed : chunkCheck 6 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk7_closed : chunkCheck 7 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk8_closed : chunkCheck 8 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk9_closed : chunkCheck 9 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk10_closed : chunkCheck 10 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk11_closed : chunkCheck 11 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk12_closed : chunkCheck 12 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk13_closed : chunkCheck 13 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk14_closed : chunkCheck 14 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk15_closed : chunkCheck 15 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk16_closed : chunkCheck 16 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk17_closed : chunkCheck 17 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk18_closed : chunkCheck 18 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk19_closed : chunkCheck 19 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk20_closed : chunkCheck 20 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk21_closed : chunkCheck 21 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk22_closed : chunkCheck 22 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk23_closed : chunkCheck 23 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk24_closed : chunkCheck 24 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk25_closed : chunkCheck 25 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk26_closed : chunkCheck 26 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk27_closed : chunkCheck 27 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk28_closed : chunkCheck 28 = true := by decide +kernel

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma chunk29_closed : chunkCheck 29 = true := by decide +kernel

lemma all_chunks_checked : (List.range 30).all chunkCheck = true := by
  change ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29] : List ℕ).all chunkCheck = true
  simp only [List.all_cons, List.all_nil, chunk0_closed, chunk1_closed, chunk2_closed, chunk3_closed, chunk4_closed, chunk5_closed, chunk6_closed, chunk7_closed, chunk8_closed, chunk9_closed, chunk10_closed, chunk11_closed, chunk12_closed, chunk13_closed, chunk14_closed, chunk15_closed, chunk16_closed, chunk17_closed, chunk18_closed, chunk19_closed, chunk20_closed, chunk21_closed, chunk22_closed, chunk23_closed, chunk24_closed, chunk25_closed, chunk26_closed, chunk27_closed, chunk28_closed, chunk29_closed, Bool.and_self]

set_option maxRecDepth 4096 in
set_option maxHeartbeats 0 in
lemma initial_contains : contains initial = true := by decide +kernel

lemma reachable_safe {finish : State}
    (hreach : Relation.ReflTransGen (fun a b => b ∈ successors a) initial finish) :
    safe finish = true := by
  apply ResourceCertificate.chunked_searchIndex_reachable_safe stateLess getState
    1917 64 30 12 successors safe (by decide) (by decide) ?_ initial_contains hreach
  intro k hk
  change chunkCheck k = true
  exact List.all_eq_true.mp all_chunks_checked k (List.mem_range.mpr hk)

lemma reachable_no_target {finish : State}
    (hreach : Relation.ReflTransGen (fun a b => b ∈ successors a) initial finish) :
    56 ∉ finish.2.2.1 := by
  simpa [safe] using reachable_safe hreach

end OnceResource

namespace OnceGeometry

def rowSet (r : Fin 6) : Finset (Fin 10) :=
  match r.val with
  | 0 => {2, 6}
  | 1 => {3, 9}
  | 2 => {7, 8}
  | 3 => {2, 3}
  | 4 => {6, 8}
  | _ => {7, 9}

def vertexClass (v : Fin 10) : Fin 7 :=
  match v.val with
  | 0 => 0
  | 1 => 1
  | 4 => 2
  | 5 => 3
  | 2 => 4
  | 6 => 4
  | 3 => 5
  | 9 => 5
  | _ => 6

def port (g : Fin 4) (right : Bool) : Finset (Fin 10) :=
  if right then match g.val with
    | 0 => {1, 4, 5}
    | 1 => {2, 6}
    | 2 => {3, 9}
    | _ => {7, 8}
  else match g.val with
    | 0 => {0}
    | 1 => {1}
    | 2 => {4}
    | _ => {5}

def locations (g : Fin 4) (right : Bool) : Finset (Fin 7) :=
  if right then match g.val with
    | 0 => {1, 2, 3}
    | 1 => {4}
    | 2 => {5}
    | _ => {6}
  else {⟨g.val, by omega⟩}

lemma port_class : ∀ (g : Fin 4) (b : Bool) (v : Fin 10),
    v ∈ port g b ↔ vertexClass v ∈ locations g b := by decide

lemma support_class {S : Finset (Fin 10)} {g : Fin 4} {b : Bool}
    (hS : S ⊆ port g b) {v : Fin 10} (hv : v ∈ S) :
    vertexClass v ∈ locations g b := (port_class g b v).mp (hS hv)

lemma port_locations_live {used : ℕ} (hu : used < 16) {g : Fin 4}
    (hg : used.testBit g.val = false) (b : Bool) {loc : Fin 7}
    (hl : loc ∈ locations g b) : OnceResource.live used loc.val = true := by
  have h : ∀ (u : Fin 16) (g : Fin 4) (b : Bool) (loc : Fin 7),
      u.val.testBit g.val = false → loc ∈ locations g b →
      OnceResource.live u.val loc.val = true := by decide
  exact h ⟨used, hu⟩ g b loc hg hl

def bits (f : Fin 6 → Bool) : BitVec 6 :=
  BitVec.ofBoolListLE [f 0, f 1, f 2, f 3, f 4, f 5]

def mask (f : Fin 6 → Bool) : ℕ := (bits f).toNat

lemma bits_get (f : Fin 6 → Bool) (r : Fin 6) : (bits f).getLsbD r.val = f r := by
  unfold bits
  rw [BitVec.getLsbD_ofBoolListLE]
  fin_cases r <;> rfl

lemma bits_or (f g : Fin 6 → Bool) : bits (fun r => f r || g r) = bits f ||| bits g := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hf := bits_get f ⟨i, hi⟩
  have hg := bits_get g ⟨i, hi⟩
  have hr := bits_get (fun r => f r || g r) ⟨i, hi⟩
  simpa only [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_or] using hr.trans (congrArg₂ (· || ·) hf.symm hg.symm)

lemma bits_and (f g : Fin 6 → Bool) : bits (fun r => f r && g r) = bits f &&& bits g := by
  apply BitVec.eq_of_getElem_eq
  intro i hi
  have hf := bits_get f ⟨i, hi⟩
  have hg := bits_get g ⟨i, hi⟩
  have hr := bits_get (fun r => f r && g r) ⟨i, hi⟩
  simpa only [BitVec.getLsbD_eq_getElem hi, BitVec.getElem_and] using hr.trans (congrArg₂ (· && ·) hf.symm hg.symm)

lemma mask_or (f g : Fin 6 → Bool) : mask (fun r => f r || g r) = mask f ||| mask g := by
  simp [mask, bits_or]

lemma mask_and (f g : Fin 6 → Bool) : mask (fun r => f r && g r) = mask f &&& mask g := by
  simp [mask, bits_and]

lemma mask_lt (f : Fin 6 → Bool) : mask f < 64 := by
  exact (bits f).isLt

lemma mask_testBit (f : Fin 6 → Bool) (r : Fin 6) : (mask f).testBit r.val = f r :=
  bits_get f r

lemma mask_injective : Function.Injective mask := by
  intro f g h
  funext r
  rw [← mask_testBit f r, ← mask_testBit g r, h]

def rawMask (S : Finset (Fin 10)) : ℕ :=
  mask (fun r => decide ((S ∩ rowSet r).Nonempty))

lemma rawMask_port : ∀ (g : Fin 4) (b : Bool),
    rawMask (port g b) = if b then OnceResource.basis g.val else 0 := by decide

lemma petersen_rows : ∀ r : Fin 6,
    edgeFn (fun v => decide (v ∈ rowSet r)) = decide (3 ≤ r.val) := by decide

lemma petersen_mask : mask (fun r => edgeFn (fun v => decide (v ∈ rowSet r))) = 56 := by decide

lemma rawMask_empty : rawMask ∅ = 0 := by decide

lemma rawMask_union (S T : Finset (Fin 10)) : rawMask (S ∪ T) = rawMask S ||| rawMask T := by
  unfold rawMask
  have h : (fun r => decide (((S ∪ T) ∩ rowSet r).Nonempty)) =
      (fun r => decide ((S ∩ rowSet r).Nonempty) || decide ((T ∩ rowSet r).Nonempty)) := by
    funext r
    simp [Finset.union_inter_distrib_right]
  rw [h, mask_or]

end OnceGeometry

namespace OnceGeometry

open PEqualNP.Outside.L_meta_2590.DAGBridge.DagTools

def rowInput (r : Fin 6) : Fin 10 → Bool := fun v => decide (v ∈ rowSet r)

def wireMask (D : Dag) (w : ℕ) : ℕ := mask (fun r => val D (rowInput r) w)

lemma wireMask_lt (D : Dag) (w : ℕ) : wireMask D w < 64 := mask_lt _

lemma wireMask_input (D : Dag) (v : Fin 10) : wireMask D v.val = rawMask {v} := by
  unfold wireMask rawMask
  congr 1
  funext r
  rw [val_input D _ v.val v.isLt]
  simp [rowInput, Finset.Nonempty]

lemma wireMask_gate {D : Dag} (hS : Strict 10 D) {j : ℕ} (hj : j < D.length) :
    wireMask D (10 + j) = if tag D j then
      wireMask D (opA D j) &&& wireMask D (opB D j)
      else wireMask D (opA D j) ||| wireMask D (opB D j) := by
  have hfun : (fun r => val D (rowInput r) (10 + j)) =
      (fun r => gop (tag D j) (val D (rowInput r) (opA D j)) (val D (rowInput r) (opB D j))) := by
    funext r
    exact val_gate hS _ j hj
  unfold wireMask
  rw [hfun]
  cases tag D j <;> simp only [gop, Bool.false_eq_true, ite_false, ite_true, mask_or, mask_and]

lemma support_row_true {D : Dag} (hS : Strict 10 D) {w : ℕ} {r : Fin 6}
    (hh : (supp 10 D w ∩ rowSet r).Nonempty) : val D (rowInput r) w = true := by
  obtain ⟨v, hv⟩ := hh
  obtain ⟨hvs, hvE⟩ := Finset.mem_inter.mp hv
  apply val_mono hS (single v) (rowInput r) ?_ w (mem_supp.mp hvs)
  intro u hu
  have huv : u = v := by simpa [single] using hu
  subst u
  exact decide_eq_true hvE

lemma wireMask_support_lower {D : Dag} (hS : Strict 10 D) (w : ℕ) :
    rawMask (supp 10 D w) &&& wireMask D w = rawMask (supp 10 D w) := by
  unfold rawMask wireMask
  rw [← mask_and]
  congr 1
  funext r
  by_cases hh : (supp 10 D w ∩ rowSet r).Nonempty
  · simp only [decide_eq_true hh, support_row_true hS hh, Bool.and_self]
  · simp [hh]

lemma wireMask_correct {D : Dag} {w : ℕ}
    (hc : ∀ x : Fin 10 → Bool, val D x w = edgeFn x) : wireMask D w = 56 := by
  unfold wireMask
  have hh : (fun r => val D (rowInput r) w) = (fun r => edgeFn (rowInput r)) := by
    funext r
    exact hc _
  rw [hh]
  exact petersen_mask

lemma dirty_row_hits : ∀ r : Fin 6,
    (({3, 6, 7} : Finset (Fin 10)) ∩ rowSet r).Nonempty ∧
    (({2, 8, 9} : Finset (Fin 10)) ∩ rowSet r).Nonempty := by decide

lemma dirty_wire_mask {D : Dag} (hS : Strict 10 D) {j : ℕ} (hj : j < D.length)
    (ht : tag D j = true)
    (ha : supp 10 D (opA D j) = {3, 6, 7})
    (hb : supp 10 D (opB D j) = {2, 8, 9}) : wireMask D (10 + j) = 63 := by
  have hh : (fun r => val D (rowInput r) (10 + j)) = (fun _ => true) := by
    funext r
    rw [val_gate hS _ j hj, ht, gop_true]
    have h1 := support_row_true hS (show (supp 10 D (opA D j) ∩ rowSet r).Nonempty by
      rw [ha]; exact (dirty_row_hits r).1)
    have h2 := support_row_true hS (show (supp 10 D (opB D j) ∩ rowSet r).Nonempty by
      rw [hb]; exact (dirty_row_hits r).2)
    rw [h1, h2]
    rfl
  unfold wireMask
  rw [hh]
  decide

end OnceGeometry


namespace OnceResource

lemma mem_values_iff {bits x : ℕ} : x ∈ values bits ↔ x < 64 ∧ bits.testBit x = true := by
  simp [values]

lemma testBit_singleton_iff {k x : ℕ} : (1 <<< k : ℕ).testBit x = true ↔ k = x := by
  simp [Nat.shiftLeft_eq, Nat.testBit_two_pow]

lemma testBit_fold_or_iff (xs : List ℕ) (f : ℕ → ℕ) (acc z : ℕ) :
    (xs.foldl (fun a x => a ||| f x) acc).testBit z = true ↔
      acc.testBit z = true ∨ ∃ x ∈ xs, (f x).testBit z = true := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih => simp [List.foldl_cons, ih, or_assoc]

lemma testBit_fold_pairs_iff (xs ys : List ℕ) (op : ℕ → ℕ → ℕ) (acc z : ℕ) :
    (xs.foldl (fun acc x => ys.foldl (fun acc y => acc ||| (1 <<< op x y)) acc) acc).testBit z = true ↔
      acc.testBit z = true ∨ ∃ x ∈ xs, ∃ y ∈ ys, op x y = z := by
  induction xs generalizing acc with
  | nil => simp
  | cons x xs ih =>
    simp only [List.foldl_cons, ih, testBit_fold_or_iff, testBit_singleton_iff]
    simp [or_assoc]

lemma mem_pairMasks_iff {op : ℕ → ℕ → ℕ} {a b z : ℕ} :
    z ∈ values (pairMasks op a b) ↔
      z < 64 ∧ ∃ x ∈ values a, ∃ y ∈ values b, op x y = z := by
  simp [mem_values_iff, pairMasks, testBit_fold_pairs_iff]

lemma mem_pairMasks {op : ℕ → ℕ → ℕ} {a b x y : ℕ}
    (hx : x ∈ values a) (hy : y ∈ values b) (hxy : op x y < 64) :
    op x y ∈ values (pairMasks op a b) := by
  exact mem_pairMasks_iff.mpr ⟨hxy, x, hx, y, hy, rfl⟩

lemma mem_singleton_iff {k x : ℕ} :
    x ∈ values (1 <<< k) ↔ x < 64 ∧ k = x := by
  rw [mem_values_iff, testBit_singleton_iff]

lemma mem_singleton {k : ℕ} (hk : k < 64) : k ∈ values (1 <<< k) := by
  exact mem_singleton_iff.mpr ⟨hk, rfl⟩

lemma or_lt_64 {x y : ℕ} (hx : x < 64) (hy : y < 64) : x ||| y < 64 := by
  exact Nat.or_lt_two_pow (n := 6) hx hy

lemma mem_addCarrier_of_mem {p k x : ℕ} (hx : x ∈ values p) :
    x ∈ values (addCarrier p k) := by
  obtain ⟨hxb, hxt⟩ := mem_values_iff.mp hx
  apply mem_values_iff.mpr
  simp [addCarrier, hxb, hxt]

lemma mem_addCarrier_or {p k x : ℕ} (hx : x ∈ values p) (hk : k < 64) :
    x ||| k ∈ values (addCarrier p k) := by
  apply mem_values_iff.mpr
  have hb := or_lt_64 (mem_values_iff.mp hx).1 hk
  have hm := mem_pairMasks (op := (· ||| ·)) hx (mem_singleton hk) hb
  have ht := (mem_values_iff.mp hm).2
  simp [addCarrier, mergePools, hb, ht]

lemma mem_addCarrier_iff {p k z : ℕ} (hk : k < 64) :
    z ∈ values (addCarrier p k) ↔
      z ∈ values p ∨ ∃ x ∈ values p, x ||| k = z := by
  constructor
  · intro hz
    obtain ⟨hzb, hzt⟩ := mem_values_iff.mp hz
    simp only [addCarrier, Nat.testBit_or, Bool.or_eq_true] at hzt
    rcases hzt with hp | hm
    · exact Or.inl (mem_values_iff.mpr ⟨hzb, hp⟩)
    · have hm' : z ∈ values (pairMasks (· ||| ·) p (1 <<< k)) :=
        mem_values_iff.mpr ⟨hzb, hm⟩
      obtain ⟨_, x, hx, y, hy, heq⟩ := mem_pairMasks_iff.mp hm'
      obtain ⟨_, rfl⟩ := mem_singleton_iff.mp hy
      exact Or.inr ⟨x, hx, heq⟩
  · rintro (hz | ⟨x, hx, rfl⟩)
    · exact mem_addCarrier_of_mem hz
    · exact mem_addCarrier_or hx hk

lemma addCarrier_or_closed {p k : ℕ} (hk : k < 64)
    (hclosed : ∀ x ∈ values p, ∀ y ∈ values p, x ||| y ∈ values p) :
    ∀ x ∈ values (addCarrier p k), ∀ y ∈ values (addCarrier p k),
      x ||| y ∈ values (addCarrier p k) := by
  intro x hx y hy
  rcases (mem_addCarrier_iff hk).mp hx with hx | ⟨a, ha, rfl⟩
  · rcases (mem_addCarrier_iff hk).mp hy with hy | ⟨b, hb, rfl⟩
    · exact mem_addCarrier_of_mem (hclosed x hx y hy)
    · rw [← Nat.or_assoc]
      exact mem_addCarrier_or (hclosed x hx b hb) hk
  · rcases (mem_addCarrier_iff hk).mp hy with hy | ⟨b, hb, rfl⟩
    · have heq : (a ||| k) ||| y = (a ||| y) ||| k := by ac_rfl
      rw [heq]
      exact mem_addCarrier_or (hclosed a ha y hy) hk
    · have heq : (a ||| k) ||| (b ||| k) = (a ||| b) ||| (k ||| k) := by ac_rfl
      rw [heq, Nat.or_self]
      exact mem_addCarrier_or (hclosed a ha b hb) hk

lemma addCarrier_zero_and_or_closed {p k : ℕ} (hk : k < 64)
    (hzero : 0 ∈ values p)
    (hclosed : ∀ x ∈ values p, ∀ y ∈ values p, x ||| y ∈ values p) :
    0 ∈ values (addCarrier p k) ∧
      ∀ x ∈ values (addCarrier p k), ∀ y ∈ values (addCarrier p k),
        x ||| y ∈ values (addCarrier p k) := by
  exact ⟨mem_addCarrier_of_mem hzero, addCarrier_or_closed hk hclosed⟩


lemma live_group_of_unused {used g : ℕ} (hg : g < 4)
    (hu : (! (used.testBit g)) = true) : live used g = true := by
  by_cases hzero : g = 0
  · subst g
    simpa [live] using hu
  · simp only [live, ite_eq_right hzero, ite_eq_left hg, hu, Bool.or_true]

lemma live_root_right_of_unused {used loc : ℕ}
    (hlow : 1 ≤ loc) (hhigh : loc < 4) (hu : (! (used.testBit 0)) = true) :
    live used loc = true := by
  have hne : loc ≠ 0 := by omega
  simp only [live, ite_eq_right hne, ite_eq_left hhigh, hu, Bool.true_or]

lemma live_group_right_of_unused {used g : ℕ}
    (hlow : 1 ≤ g) (hu : (! (used.testBit g)) = true) :
    live used (g + 3) = true := by
  have hne : g + 3 ≠ 0 := by omega
  have hnot : ¬g + 3 < 4 := by omega
  simpa [live, hne, hnot] using hu

lemma prune_getD_of_live {s : State} {loc : ℕ}
    (hloc : loc < 7) (hlive : live s.1 loc = true) :
    (prune s).2.1.getD loc 1 = s.2.1.getD loc 1 := by
  simp [prune, List.getD_eq_getElem?_getD, List.getElem?_range hloc, hlive]

lemma prune_group_left {s : State} {g : ℕ}
    (hg : g < 4) (hu : (! (s.1.testBit g)) = true) :
    (prune s).2.1.getD g 1 = s.2.1.getD g 1 := by
  apply prune_getD_of_live (by omega)
  exact live_group_of_unused hg hu

lemma prune_group_right {s : State} {g : ℕ}
    (hg : g < 4) (hu : (! (s.1.testBit g)) = true) :
    rightPool (prune s).2.1 g = rightPool s.2.1 g := by
  by_cases hzero : g = 0
  · subst g
    have h1 := prune_getD_of_live (s := s) (loc := 1) (by decide)
      (live_root_right_of_unused (by decide) (by decide) hu)
    have h2 := prune_getD_of_live (s := s) (loc := 2) (by decide)
      (live_root_right_of_unused (by decide) (by decide) hu)
    have h3 := prune_getD_of_live (s := s) (loc := 3) (by decide)
      (live_root_right_of_unused (by decide) (by decide) hu)
    simp only [rightPool, h1, h2, h3]
  · have hget := prune_getD_of_live (s := s) (loc := g + 3) (by omega)
      (live_group_right_of_unused (by omega) hu)
    simp only [rightPool, ite_eq_right hzero, hget]

lemma prune_group_pairMasks {s : State} {g : ℕ}
    (hg : g < 4) (hu : (! (s.1.testBit g)) = true) :
    pairMasks (· &&& ·) ((prune s).2.1.getD g 1) (rightPool (prune s).2.1 g) =
      pairMasks (· &&& ·) (s.2.1.getD g 1) (rightPool s.2.1 g) := by
  rw [prune_group_left hg hu, prune_group_right hg hu]


lemma sortedInsert_perm (k : ℕ) (xs : List ℕ) :
    List.Perm (sortedInsert k xs) (k :: xs) := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
      simp only [sortedInsert]
      split
      · exact List.Perm.refl _
      · exact (List.Perm.cons x ih).trans (List.Perm.swap _ _ _)

lemma zeroSort_perm (xs : List ℕ) : List.Perm (zeroSort xs) xs := by
  induction xs with
  | nil => exact List.Perm.refl _
  | cons x xs ih =>
      exact (sortedInsert_perm x (zeroSort xs)).trans (List.Perm.cons x ih)

lemma insertZero_perm (k : ℕ) (xs : List ℕ) :
    List.Perm (insertZero k xs) (k :: xs) :=
  zeroSort_perm (k :: xs)

lemma mem_sortedInsert (a k : ℕ) (xs : List ℕ) :
    a ∈ sortedInsert k xs ↔ a = k ∨ a ∈ xs := by
  rw [(sortedInsert_perm k xs).mem_iff, List.mem_cons]

lemma mem_zeroSort (a : ℕ) (xs : List ℕ) :
    a ∈ zeroSort xs ↔ a ∈ xs :=
  (zeroSort_perm xs).mem_iff

lemma mem_insertZero (a k : ℕ) (xs : List ℕ) :
    a ∈ insertZero k xs ↔ a = k ∨ a ∈ xs := by
  rw [(insertZero_perm k xs).mem_iff, List.mem_cons]

lemma sortedInsert_length (k : ℕ) (xs : List ℕ) :
    (sortedInsert k xs).length = xs.length + 1 := by
  simpa only [List.length_cons] using (sortedInsert_perm k xs).length_eq

lemma zeroSort_length (xs : List ℕ) : (zeroSort xs).length = xs.length :=
  (zeroSort_perm xs).length_eq

lemma insertZero_length (k : ℕ) (xs : List ℕ) :
    (insertZero k xs).length = xs.length + 1 := by
  simpa only [List.length_cons] using (insertZero_perm k xs).length_eq


lemma prune_used (s : State) : (prune s).1 = s.1 := rfl

lemma prune_zeros (s : State) : (prune s).2.2.1 = s.2.2.1 := rfl

lemma prune_forked (s : State) : (prune s).2.2.2 = s.2.2.2 := rfl

lemma prune_pool_getD (s : State) (i : ℕ) (hi : i < 7) :
    (prune s).2.1.getD i 1 = if live s.1 i then s.2.1.getD i 1 else 1 := by
  change ((List.range 7).map (fun j =>
    if live s.1 j then s.2.1.getD j 1 else 1)).getD i 1 = _
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map,
    List.getElem?_range hi, Option.map_some, Option.getD_some]

lemma prune_idempotent (s : State) : prune (prune s) = prune s := by
  refine Prod.ext rfl (Prod.ext ?_ rfl)
  change (List.range 7).map (fun i =>
    if live s.1 i then (prune s).2.1.getD i 1 else 1) =
      (List.range 7).map (fun i => if live s.1 i then s.2.1.getD i 1 else 1)
  apply List.map_congr_left
  intro i hi
  rw [prune_pool_getD s i (List.mem_range.mp hi)]
  split <;> rfl

lemma prune_pools_congr (s t : State) (hused : s.1 = t.1)
    (hpools : s.2.1 = t.2.1) : (prune s).2.1 = (prune t).2.1 := by
  change (List.range 7).map (fun i => if live s.1 i then s.2.1.getD i 1 else 1) =
    (List.range 7).map (fun i => if live t.1 i then t.2.1.getD i 1 else 1)
  rw [hused, hpools]


lemma groupNext_mem_successors {s t : State} (h : t ∈ groupNext s) :
    t ∈ successors s := by
  simp only [successors, List.mem_append, h, true_or]

lemma forkNext_mem_successors {s t : State} (h : t ∈ forkNext s) :
    t ∈ successors s := by
  simp only [successors, List.mem_append, h, true_or, or_true]

lemma liftNext_mem_successors {s t : State} (h : t ∈ liftNext s) :
    t ∈ successors s := by
  simp only [successors, List.mem_append, h, true_or, or_true]

lemma discardNext_mem_successors {s t : State} (h : t ∈ discardNext s) :
    t ∈ successors s := by
  simp only [successors, List.mem_append, h, true_or, or_true]

lemma combineNext_mem_successors {s t : State} (h : t ∈ combineNext s) :
    t ∈ successors s := by
  simp only [successors, List.mem_append, h, or_true]

lemma group_successor {s : State} {g k : ℕ}
    (hg : g < 4) (hunused : s.1.testBit g = false)
    (hk : k ∈ values (pairMasks (· &&& ·) (s.2.1.getD g 1) (rightPool s.2.1 g)))
    (hkn : k ≠ 0) :
    prune (s.1 ||| (1 <<< g), s.2.1, insertZero k s.2.2.1, s.2.2.2) ∈ successors s := by
  apply groupNext_mem_successors
  apply List.mem_flatMap.mpr
  refine ⟨g, List.mem_range.mpr hg, ?_⟩
  simp only [hunused, Bool.false_eq_true, ↓reduceIte]
  apply List.mem_filterMap.mpr
  exact ⟨k, hk, by simp [hkn]⟩

lemma fork_successor {s : State} {k : ℕ}
    (hk : k ∈ s.2.2.1) (hf : s.2.2.2 = false) :
    prune (s.1, s.2.1, insertZero k s.2.2.1, true) ∈ successors s := by
  apply forkNext_mem_successors
  simp only [forkNext, hf, Bool.false_eq_true, ↓reduceIte]
  exact List.mem_map.mpr ⟨k, hk, rfl⟩

lemma lift_successor {s : State} {k loc : ℕ}
    (hk : k ∈ s.2.2.1) (hloc : loc < 7) (hlive : live s.1 loc = true)
    (hchange : addCarrier (s.2.1.getD loc 1) k ≠ s.2.1.getD loc 1) :
    prune (s.1, s.2.1.set loc (addCarrier (s.2.1.getD loc 1) k),
      s.2.2.1.erase k, s.2.2.2) ∈ successors s := by
  apply liftNext_mem_successors
  apply List.mem_flatMap.mpr
  refine ⟨k, hk, ?_⟩
  apply List.mem_filterMap.mpr
  exact ⟨loc, List.mem_range.mpr hloc, by simp only [hlive, hchange, ↓reduceIte]⟩

lemma discard_successor {s : State} {k : ℕ} (hk : k ∈ s.2.2.1) :
    prune (s.1, s.2.1, s.2.2.1.erase k, s.2.2.2) ∈ successors s := by
  apply discardNext_mem_successors
  exact List.mem_map.mpr ⟨k, hk, rfl⟩

lemma combine_successor {s : State} {a b k : ℕ}
    (ha : a ∈ s.2.2.1) (hb : b ∈ s.2.2.1.erase a)
    (hk : k = a &&& b ∨ k = a ||| b) (hkn : k ≠ 0) :
    prune (s.1, s.2.1, insertZero k ((s.2.2.1.erase a).erase b), s.2.2.2) ∈ successors s := by
  apply combineNext_mem_successors
  apply List.mem_flatMap.mpr
  refine ⟨a, ha, ?_⟩
  apply List.mem_flatMap.mpr
  refine ⟨b, hb, ?_⟩
  apply List.mem_filterMap.mpr
  refine ⟨k, ?_, by simp [hkn]⟩
  simpa only [List.mem_cons, List.not_mem_nil, or_false] using hk

lemma reachable_of_eq_or_successor {s t : State}
    (h : t = s ∨ t ∈ successors s) :
    Relation.ReflTransGen (fun a b : State => b ∈ successors a) s t := by
  rcases h with rfl | h
  · exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single h


lemma set_getD_self (xs : List ℕ) (i d : ℕ) : xs.set i (xs.getD i d) = xs := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    cases i with
    | zero => rfl
    | succ i => exact congrArg (List.cons x) (ih i)

lemma lift_successor_or_discard {s : State} {k loc : ℕ}
    (hk : k ∈ s.2.2.1) (hloc : loc < 7) (hlive : live s.1 loc = true) :
    prune (s.1, s.2.1.set loc (addCarrier (s.2.1.getD loc 1) k),
      s.2.2.1.erase k, s.2.2.2) ∈ successors s := by
  by_cases hchange : addCarrier (s.2.1.getD loc 1) k = s.2.1.getD loc 1
  · rw [hchange, set_getD_self]
    exact discard_successor hk
  · exact lift_successor hk hloc hlive hchange

lemma lift_reachable {s : State} {k loc : ℕ}
    (hk : k ∈ s.2.2.1) (hloc : loc < 7) (hlive : live s.1 loc = true) :
    Relation.ReflTransGen (fun a b : State => b ∈ successors a) s
      (prune (s.1, s.2.1.set loc (addCarrier (s.2.1.getD loc 1) k),
        s.2.2.1.erase k, s.2.2.2)) :=
  Relation.ReflTransGen.single (lift_successor_or_discard hk hloc hlive)


namespace ZeroTransitions

def token (k : ℕ) : Multiset ℕ := if k = 0 then 0 else {k}

lemma mem_of_zero_eq {zs : List ℕ} {a : ℕ} {rest : Multiset ℕ}
    (hz : (zs : Multiset ℕ) = {a} + rest) : a ∈ zs := by
  change a ∈ (zs : Multiset ℕ)
  rw [hz]
  simp

lemma erase_of_zero_eq {zs : List ℕ} {a : ℕ} {rest : Multiset ℕ}
    (hz : (zs : Multiset ℕ) = {a} + rest) :
    (zs.erase a : Multiset ℕ) = rest := by
  change (zs : Multiset ℕ).erase a = rest
  rw [hz]
  simp

lemma coe_insertZero (k : ℕ) (zs : List ℕ) :
    (insertZero k zs : Multiset ℕ) = {k} + (zs : Multiset ℕ) := by
  change (insertZero k zs : Multiset ℕ) = ((k :: zs : List ℕ) : Multiset ℕ)
  exact Quot.sound (insertZero_perm k zs)

lemma discard_one {s : State} {a : ℕ} {rest : Multiset ℕ}
    (hz : (s.2.2.1 : Multiset ℕ) = {a} + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      (t.2.2.1 : Multiset ℕ) = rest ∧ t.1 = s.1 ∧ t.2.2.2 = s.2.2.2 ∧
      t.2.1 = (prune s).2.1 := by
  refine ⟨prune (s.1, s.2.1, s.2.2.1.erase a, s.2.2.2),
    Relation.ReflTransGen.single (discard_successor (mem_of_zero_eq hz)),
    erase_of_zero_eq hz, rfl, rfl, rfl⟩

lemma discard_two {s : State} {a b : ℕ} {rest : Multiset ℕ}
    (hz : (s.2.2.1 : Multiset ℕ) = {a} + {b} + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      (t.2.2.1 : Multiset ℕ) = rest ∧ t.1 = s.1 ∧ t.2.2.2 = s.2.2.2 ∧
      t.2.1 = (prune s).2.1 := by
  have hz' : (s.2.2.1 : Multiset ℕ) = {a} + ({b} + rest) := by
    simpa only [Multiset.add_assoc] using hz
  have ha := mem_of_zero_eq hz'
  have hz1 := erase_of_zero_eq hz'
  have hb := mem_of_zero_eq hz1
  have hz2 := erase_of_zero_eq hz1
  let t1 : State := prune (s.1, s.2.1, s.2.2.1.erase a, s.2.2.2)
  let t2 : State := prune (s.1, s.2.1, (s.2.2.1.erase a).erase b, s.2.2.2)
  have h1 : t1 ∈ successors s := discard_successor ha
  have h2 : t2 ∈ successors t1 := by
    have hh := discard_successor (s := t1) (k := b) hb
    change prune (prune (s.1, s.2.1, (s.2.2.1.erase a).erase b, s.2.2.2)) ∈
      successors t1 at hh
    rw [prune_idempotent] at hh
    exact hh
  exact ⟨t2, (Relation.ReflTransGen.single h1).trans (Relation.ReflTransGen.single h2),
    hz2, rfl, rfl, rfl⟩

lemma combine_nonzero {s : State} {a b k : ℕ} {rest : Multiset ℕ}
    (hz : (s.2.2.1 : Multiset ℕ) = {a} + {b} + rest)
    (hop : k = a &&& b ∨ k = a ||| b) (hk : k ≠ 0) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      (t.2.2.1 : Multiset ℕ) = {k} + rest ∧ t.1 = s.1 ∧ t.2.2.2 = s.2.2.2 ∧
      t.2.1 = (prune s).2.1 := by
  have hz' : (s.2.2.1 : Multiset ℕ) = {a} + ({b} + rest) := by
    simpa only [Multiset.add_assoc] using hz
  have ha := mem_of_zero_eq hz'
  have hz1 := erase_of_zero_eq hz'
  have hb := mem_of_zero_eq hz1
  have hz2 := erase_of_zero_eq hz1
  refine ⟨prune (s.1, s.2.1, insertZero k ((s.2.2.1.erase a).erase b), s.2.2.2),
    Relation.ReflTransGen.single (combine_successor ha hb hop hk), ?_, rfl, rfl, rfl⟩
  change (insertZero k ((s.2.2.1.erase a).erase b) : Multiset ℕ) = {k} + rest
  rw [coe_insertZero, hz2]

lemma zero_binary {s : State} (a b : ℕ) (isAnd : Bool) (rest : Multiset ℕ)
    (hz : (s.2.2.1 : Multiset ℕ) = token a + token b + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      (t.2.2.1 : Multiset ℕ) = token (if isAnd then a &&& b else a ||| b) + rest ∧
      t.1 = s.1 ∧ t.2.2.2 = s.2.2.2 ∧
      (t.2.1 = s.2.1 ∨ t.2.1 = (prune s).2.1) := by
  by_cases ha : a = 0
  · subst a
    cases isAnd
    · refine ⟨s, Relation.ReflTransGen.refl, ?_, rfl, rfl, Or.inl rfl⟩
      simpa [token] using hz
    · by_cases hb : b = 0
      · subst b
        refine ⟨s, Relation.ReflTransGen.refl, ?_, rfl, rfl, Or.inl rfl⟩
        simpa [token] using hz
      · have hz' : (s.2.2.1 : Multiset ℕ) = {b} + rest := by simpa [token, hb] using hz
        obtain ⟨t, hr, ht, hu, hf, hp⟩ := discard_one hz'
        exact ⟨t, hr, by simpa [token] using ht, hu, hf, Or.inr hp⟩
  · by_cases hb : b = 0
    · subst b
      cases isAnd
      · refine ⟨s, Relation.ReflTransGen.refl, ?_, rfl, rfl, Or.inl rfl⟩
        simpa [token] using hz
      · have hz' : (s.2.2.1 : Multiset ℕ) = {a} + rest := by simpa [token, ha] using hz
        obtain ⟨t, hr, ht, hu, hf, hp⟩ := discard_one hz'
        exact ⟨t, hr, by simpa [token] using ht, hu, hf, Or.inr hp⟩
    · have hz' : (s.2.2.1 : Multiset ℕ) = {a} + {b} + rest := by
        simpa [token, ha, hb] using hz
      let k := if isAnd then a &&& b else a ||| b
      by_cases hk : k = 0
      · obtain ⟨t, hr, ht, hu, hf, hp⟩ := discard_two hz'
        refine ⟨t, hr, ?_, hu, hf, Or.inr hp⟩
        change (t.2.2.1 : Multiset ℕ) = token k + rest
        rw [hk]
        simpa [token] using ht
      · have hop : k = a &&& b ∨ k = a ||| b := by cases isAnd <;> simp [k]
        obtain ⟨t, hr, ht, hu, hf, hp⟩ := combine_nonzero hz' hop hk
        refine ⟨t, hr, ?_, hu, hf, Or.inr hp⟩
        change (t.2.2.1 : Multiset ℕ) = token k + rest
        simpa [token, hk] using ht

end ZeroTransitions


end OnceResource

namespace OncePositive

open OnceResource OnceGeometry

abbrev Pools := Fin 7 → ℕ

def or7 (f : Fin 7 → ℕ) : ℕ :=
  f 0 ||| f 1 ||| f 2 ||| f 3 ||| f 4 ||| f 5 ||| f 6

def PoolsGood (P : Pools) : Prop := ∀ i,
  0 ∈ values (P i) ∧ ∀ a ∈ values (P i), ∀ b ∈ values (P i), a ||| b ∈ values (P i)

def Witness (P : Pools) (L : Finset (Fin 7)) (f : Fin 7 → ℕ) : Prop :=
  ∀ i, f i ∈ values (P i) ∧ (i ∉ L → f i = 0)

def Rep (used : ℕ) (P : Pools) (S : Finset (Fin 10)) (m : ℕ) : Prop :=
  ∀ (g : Fin 4) (b : Bool), used.testBit g.val = false → S ⊆ port g b →
    ∃ f, Witness P (locations g b) f ∧ m = rawMask S ||| or7 f

def liftPool (P : Pools) (loc : Fin 7) (k : ℕ) : Pools :=
  Function.update P loc (addCarrier (P loc) k)

lemma or7_or (f h : Fin 7 → ℕ) :
    or7 (fun i => f i ||| h i) = or7 f ||| or7 h := by
  dsimp only [or7]
  ac_rfl

lemma or7_update (f : Fin 7 → ℕ) (loc : Fin 7) (k : ℕ) :
    or7 (Function.update f loc (f loc ||| k)) = or7 f ||| k := by
  fin_cases loc <;> simp [or7, Function.update]
  all_goals
    generalize f (0 : Fin 7) = x0
    generalize f (1 : Fin 7) = x1
    generalize f (2 : Fin 7) = x2
    generalize f (3 : Fin 7) = x3
    generalize f (4 : Fin 7) = x4
    generalize f (5 : Fin 7) = x5
    generalize f (6 : Fin 7) = x6
    ac_rfl

lemma rep_raw {used : ℕ} {P : Pools} (hp : PoolsGood P) (S : Finset (Fin 10)) :
    Rep used P S (rawMask S) := by
  intro g b _ _
  refine ⟨fun _ => 0, ?_, ?_⟩
  · exact fun i => ⟨(hp i).1, fun _ => rfl⟩
  · simp [or7]

lemma rep_or {used : ℕ} {P : Pools} (hp : PoolsGood P)
    {S T : Finset (Fin 10)} {a b : ℕ} (ha : Rep used P S a) (hb : Rep used P T b) :
    Rep used P (S ∪ T) (a ||| b) := by
  intro g side hu hST
  have hS : S ⊆ port g side := fun v hv => hST (Finset.mem_union_left _ hv)
  have hT : T ⊆ port g side := fun v hv => hST (Finset.mem_union_right _ hv)
  obtain ⟨f, hf, ha⟩ := ha g side hu hS
  obtain ⟨h, hh, hb⟩ := hb g side hu hT
  refine ⟨fun i => f i ||| h i, ?_, ?_⟩
  · intro i
    refine ⟨(hp i).2 _ (hf i).1 _ (hh i).1, ?_⟩
    intro hi
    change f i ||| h i = 0
    rw [(hf i).2 hi, (hh i).2 hi]
    rfl
  · rw [ha, hb, rawMask_union, or7_or]
    ac_rfl

lemma rep_mono {used : ℕ} {P Q : Pools} {S : Finset (Fin 10)} {m : ℕ}
    (hPQ : ∀ i x, x ∈ values (P i) → x ∈ values (Q i))
    (h : Rep used P S m) : Rep used Q S m := by
  intro g b hg hS
  obtain ⟨f, hf, hm⟩ := h g b hg hS
  exact ⟨f, fun i => ⟨hPQ i _ (hf i).1, (hf i).2⟩, hm⟩

lemma liftPool_mono (P : Pools) (loc : Fin 7) (k : ℕ) :
    ∀ i x, x ∈ values (P i) → x ∈ values (liftPool P loc k i) := by
  intro i x hx
  by_cases hi : i = loc
  · subst i
    simpa [liftPool] using mem_addCarrier_of_mem (k := k) hx
  · simpa [liftPool, hi] using hx

lemma poolsGood_lift {P : Pools} (hp : PoolsGood P) (loc : Fin 7) {k : ℕ} (hk : k < 64) :
    PoolsGood (liftPool P loc k) := by
  intro i
  by_cases hi : i = loc
  · subst i
    simpa [liftPool] using addCarrier_zero_and_or_closed hk (hp loc).1 (hp loc).2
  · simpa [liftPool, hi] using hp i

lemma rep_lift {used : ℕ} {P : Pools} {S : Finset (Fin 10)} {m k : ℕ}
    (h : Rep used P S m) (hk : k < 64) {v : Fin 10} (hv : v ∈ S) :
    Rep used (liftPool P (vertexClass v) k) S (m ||| k) := by
  intro g b hg hS
  have hvL := support_class hS hv
  obtain ⟨f, hf, hm⟩ := h g b hg hS
  refine ⟨Function.update f (vertexClass v) (f (vertexClass v) ||| k), ?_, ?_⟩
  · intro i
    by_cases hi : i = vertexClass v
    · subst i
      constructor
      · simpa [liftPool] using mem_addCarrier_or (hf (vertexClass v)).1 hk
      · intro hnot
        exact False.elim (hnot hvL)
    · simpa [liftPool, Function.update_apply, hi] using hf i
  · rw [or7_update, hm]
    ac_rfl

lemma rep_restrict_pools {old new : ℕ} {P Q : Pools} {S : Finset (Fin 10)} {m : ℕ}
    (hgroups : ∀ g : Fin 4, new.testBit g.val = false → old.testBit g.val = false)
    (hzero : ∀ i, 0 ∈ values (Q i))
    (hpools : ∀ (g : Fin 4) (b : Bool), new.testBit g.val = false →
      ∀ i ∈ locations g b, Q i = P i)
    (h : Rep old P S m) : Rep new Q S m := by
  intro g b hg hS
  obtain ⟨f, hf, hm⟩ := h g b (hgroups g hg) hS
  refine ⟨f, ?_, hm⟩
  intro i
  refine ⟨?_, (hf i).2⟩
  by_cases hi : i ∈ locations g b
  · rw [hpools g b hg i hi]
    exact (hf i).1
  · rw [(hf i).2 hi]
    exact hzero i

end OncePositive


namespace OncePositive

open OnceResource OnceGeometry

def rightChoices (P : Pools) (g : Fin 4) : ℕ :=
  match g.val with
  | 0 => mergePools (mergePools (P 1) (P 2)) (P 3)
  | 1 => mergePools (1 <<< 25) (P 4)
  | 2 => mergePools (1 <<< 42) (P 5)
  | _ => mergePools (1 <<< 52) (P 6)

def portChoices (P : Pools) (g : Fin 4) (b : Bool) : ℕ :=
  if b then rightChoices P g else P ⟨g.val, by omega⟩

def poolView (ps : List ℕ) : Pools := fun i => ps.getD i.val 1

lemma portChoices_view (ps : List ℕ) (g : Fin 4) (b : Bool) :
    portChoices (poolView ps) g b =
      if b then rightPool ps g.val else ps.getD g.val 1 := by
  fin_cases g <;> cases b <;> rfl

lemma or7_filtered {L : Finset (Fin 7)} {f : Fin 7 → ℕ}
    (hf : ∀ i, i ∉ L → f i = 0) :
    or7 f = or7 (fun i => if i ∈ L then f i else 0) := by
  congr 1
  funext i
  by_cases hi : i ∈ L
  · simp [hi]
  · simp [hi, hf i hi]

lemma merge_mem {p q a b : ℕ} (ha : a ∈ values p) (hb : b ∈ values q) :
    a ||| b ∈ values (mergePools p q) := by
  exact mem_pairMasks ha hb (or_lt_64 (mem_values_iff.mp ha).1 (mem_values_iff.mp hb).1)

lemma portChoices_membership (P : Pools) (g : Fin 4) (b : Bool) (f : Fin 7 → ℕ)
    (hf : ∀ i, f i ∈ values (P i)) :
    rawMask (port g b) ||| or7 (fun i => if i ∈ locations g b then f i else 0) ∈
      values (portChoices P g b) := by
  rw [rawMask_port]
  fin_cases g <;> cases b
  · simpa [portChoices, locations, or7] using hf 0
  · simpa [portChoices, rightChoices, locations, or7, basis] using
      merge_mem (merge_mem (hf 1) (hf 2)) (hf 3)
  · simpa [portChoices, locations, or7] using hf 1
  · simpa [portChoices, rightChoices, locations, or7, basis] using
      merge_mem (mem_singleton (by decide : 25 < 64)) (hf 4)
  · simpa [portChoices, locations, or7] using hf 2
  · simpa [portChoices, rightChoices, locations, or7, basis] using
      merge_mem (mem_singleton (by decide : 42 < 64)) (hf 5)
  · simpa [portChoices, locations, or7] using hf 3
  · simpa [portChoices, rightChoices, locations, or7, basis] using
      merge_mem (mem_singleton (by decide : 52 < 64)) (hf 6)

lemma rep_port_mem {used : ℕ} {P : Pools} {g : Fin 4} {b : Bool} {m : ℕ}
    (h : Rep used P (port g b) m) (hu : used.testBit g.val = false) :
    m ∈ values (portChoices P g b) := by
  obtain ⟨f, hf, hm⟩ := h g b hu (Finset.Subset.refl _)
  rw [hm, or7_filtered (fun i => (hf i).2)]
  exact portChoices_membership P g b f (fun i => (hf i).1)

lemma group_candidate {used : ℕ} {P : Pools} {g : Fin 4} {a b : ℕ}
    (ha : Rep used P (port g false) a) (hb : Rep used P (port g true) b)
    (hu : used.testBit g.val = false) (hab : a &&& b < 64) :
    a &&& b ∈ values (pairMasks (· &&& ·) (P ⟨g.val, by omega⟩) (rightChoices P g)) := by
  have hleft := rep_port_mem ha hu
  have hright := rep_port_mem hb hu
  exact mem_pairMasks hleft hright hab

end OncePositive


namespace OncePositive

open OnceResource OnceGeometry

lemma poolView_prune (s : State) (i : Fin 7) :
    poolView (prune s).2.1 i = if live s.1 i.val then poolView s.2.1 i else 1 := by
  simp [poolView, prune, List.getD_eq_getElem?_getD]

lemma prune_pools_length (s : State) : (prune s).2.1.length = 7 := by
  simp [prune]

lemma mem_values_one_iff {x : ℕ} : x ∈ values 1 ↔ x = 0 := by
  rw [mem_values_iff, Nat.testBit_one_eq_true_iff_self_eq_zero]
  constructor
  · exact And.right
  · intro h
    subst x
    exact ⟨by decide, rfl⟩

lemma one_pool_good :
    0 ∈ values 1 ∧ ∀ a ∈ values 1, ∀ b ∈ values 1, a ||| b ∈ values 1 := by
  constructor
  · exact mem_values_one_iff.mpr rfl
  · intro a ha b hb
    obtain rfl := mem_values_one_iff.mp ha
    obtain rfl := mem_values_one_iff.mp hb
    exact mem_values_one_iff.mpr rfl

lemma poolsGood_prune {s : State} (hp : PoolsGood (poolView s.2.1)) :
    PoolsGood (poolView (prune s).2.1) := by
  intro i
  rw [poolView_prune]
  split
  · exact hp i
  · exact one_pool_good

lemma rep_prune {s : State} {S : Finset (Fin 10)} {m : ℕ}
    (hu : s.1 < 16) (hp : PoolsGood (poolView s.2.1))
    (h : Rep s.1 (poolView s.2.1) S m) :
    Rep (prune s).1 (poolView (prune s).2.1) S m := by
  apply rep_restrict_pools (fun _ hg => hg) (fun i => (poolsGood_prune hp i).1) ?_ h
  intro g b hg i hi
  rw [poolView_prune, port_locations_live hu hg b hi]
  rfl

lemma unused_of_or_unused {used extra i : ℕ}
    (h : (used ||| extra).testBit i = false) : used.testBit i = false := by
  rw [Nat.testBit_or] at h
  exact (Bool.or_eq_false_iff.mp h).1

lemma mark_used_lt {used : ℕ} (hu : used < 16) (g : Fin 4) :
    used ||| (1 <<< g.val) < 16 := by
  have hg : (1 <<< g.val : ℕ) < 16 := by fin_cases g <;> decide
  exact Nat.or_lt_two_pow (n := 4) hu hg

lemma rep_mark {used : ℕ} {P : Pools} {S : Finset (Fin 10)} {m : ℕ}
    (h : Rep used P S m) (g : Fin 4) : Rep (used ||| (1 <<< g.val)) P S m := by
  intro g' b hg hS
  exact h g' b (unused_of_or_unused hg) hS

lemma rep_mark_prune {used : ℕ} {ps : List ℕ} {S : Finset (Fin 10)} {m : ℕ}
    (hu : used < 16) (hp : PoolsGood (poolView ps)) (h : Rep used (poolView ps) S m)
    (g : Fin 4) (zs : List ℕ) (forked : Bool) :
    Rep (used ||| (1 <<< g.val))
      (poolView (prune (used ||| (1 <<< g.val), ps, zs, forked)).2.1) S m := by
  exact rep_prune (s := (used ||| (1 <<< g.val), ps, zs, forked))
    (mark_used_lt hu g) hp (rep_mark h g)

lemma poolView_set {ps : List ℕ} (hlen : ps.length = 7) (loc : Fin 7) (k : ℕ) :
    poolView (ps.set loc.val (addCarrier (ps.getD loc.val 1) k)) =
      liftPool (poolView ps) loc k := by
  funext i
  by_cases hi : i = loc
  · subst i
    have hb : loc.val < ps.length := by simpa only [hlen] using loc.isLt
    simp [poolView, liftPool, List.getD_eq_getElem?_getD, List.getElem?_set_self hb]
  · have hne : loc.val ≠ i.val := fun h => hi (Fin.ext h.symm)
    simp [poolView, liftPool, hi, List.getD_eq_getElem?_getD, List.getElem?_set_ne hne]

lemma poolsGood_set {ps : List ℕ} (hlen : ps.length = 7)
    (hp : PoolsGood (poolView ps)) (loc : Fin 7) {k : ℕ} (hk : k < 64) :
    PoolsGood (poolView (ps.set loc.val (addCarrier (ps.getD loc.val 1) k))) := by
  rw [poolView_set hlen]
  exact poolsGood_lift hp loc hk

lemma poolView_replicate_one : poolView (List.replicate 7 1) = fun _ => 1 := by
  funext i
  fin_cases i <;> rfl

lemma poolsGood_replicate_one : PoolsGood (poolView (List.replicate 7 1)) := by
  rw [poolView_replicate_one]
  exact fun _ => one_pool_good

end OncePositive



namespace OncePositive
open OnceResource OnceGeometry

lemma rep_of_dead_class {used : ℕ} {P : Pools} {S : Finset (Fin 10)} {v : Fin 10}
    (hu : used < 16) (hv : v ∈ S) (hd : live used (vertexClass v).val = false) (m : ℕ) :
    Rep used P S m := by
  intro g b hg hS
  have hl := port_locations_live hu hg b (support_class hS hv)
  simp [hd] at hl

lemma positive_lift_step {s : State} {S : Finset (Fin 10)} {m k : ℕ}
    (hu : s.1 < 16) (hlen : s.2.1.length = 7) (hp : PoolsGood (poolView s.2.1))
    (h : Rep s.1 (poolView s.2.1) S m) (hs : S.Nonempty)
    (hk : k < 64) (hmem : k ∈ s.2.2.1) :
    ∃ t : State,
      Relation.ReflTransGen (fun a b : State => b ∈ successors a) s t ∧
      t.1 = s.1 ∧ t.2.2.1 = s.2.2.1.erase k ∧ t.2.2.2 = s.2.2.2 ∧
      t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep s.1 (poolView s.2.1) T n → Rep t.1 (poolView t.2.1) T n) ∧
      Rep t.1 (poolView t.2.1) S (m ||| k) := by
  obtain ⟨v, hv⟩ := hs
  by_cases hl : live s.1 (vertexClass v).val = true
  · let q : State := (s.1,
        s.2.1.set (vertexClass v).val (addCarrier (s.2.1.getD (vertexClass v).val 1) k),
        s.2.2.1.erase k, s.2.2.2)
    have hqgood : PoolsGood (poolView q.2.1) := poolsGood_set hlen hp (vertexClass v) hk
    refine ⟨prune q, lift_reachable hmem (vertexClass v).isLt hl, rfl, rfl, rfl,
      prune_pools_length q, poolsGood_prune hqgood, ?_, ?_⟩
    · intro T n hT
      apply rep_prune (s := q) hu hqgood
      change Rep s.1 (poolView (s.2.1.set (vertexClass v).val
        (addCarrier (s.2.1.getD (vertexClass v).val 1) k))) T n
      rw [poolView_set hlen]
      exact rep_mono (liftPool_mono _ _ _) hT
    · apply rep_prune (s := q) hu hqgood
      change Rep s.1 (poolView (s.2.1.set (vertexClass v).val
        (addCarrier (s.2.1.getD (vertexClass v).val 1) k))) S (m ||| k)
      rw [poolView_set hlen]
      exact rep_lift h hk hv
  · have hd : live s.1 (vertexClass v).val = false := Bool.eq_false_of_not_eq_true hl
    let q : State := (s.1, s.2.1, s.2.2.1.erase k, s.2.2.2)
    refine ⟨prune q, Relation.ReflTransGen.single (discard_successor hmem), rfl, rfl, rfl,
      prune_pools_length q, poolsGood_prune hp, ?_, ?_⟩
    · intro T n hT
      exact rep_prune (s := q) hu hp hT
    · exact rep_of_dead_class hu hv hd _

lemma positive_group_step {s : State} {g : Fin 4} {a b : ℕ}
    (hu : s.1 < 16) (hp : PoolsGood (poolView s.2.1))
    (ha : Rep s.1 (poolView s.2.1) (port g false) a)
    (hb : Rep s.1 (poolView s.2.1) (port g true) b)
    (hg : s.1.testBit g.val = false) (hab : a &&& b < 64) (hne : a &&& b ≠ 0) :
    let t := prune (s.1 ||| (1 <<< g.val), s.2.1, insertZero (a &&& b) s.2.2.1, s.2.2.2)
    t ∈ successors s ∧ t.1 < 16 ∧ t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep s.1 (poolView s.2.1) T n → Rep t.1 (poolView t.2.1) T n) := by
  dsimp only
  have hc := group_candidate ha hb hg hab
  have hr : rightChoices (poolView s.2.1) g = rightPool s.2.1 g.val := by
    exact portChoices_view s.2.1 g true
  rw [hr] at hc
  refine ⟨group_successor g.isLt hg hc hne, mark_used_lt hu g,
    prune_pools_length _, poolsGood_prune hp, ?_⟩
  intro T n hT
  exact rep_mark_prune hu hp hT g _ _

end OncePositive


namespace OncePositive

open OnceResource OnceGeometry

lemma frame_preserves {s t : State}
    (hu : s.1 < 16) (hlen : s.2.1.length = 7) (hp : PoolsGood (poolView s.2.1))
    (ht : t.1 = s.1) (hps : t.2.1 = s.2.1 ∨ t.2.1 = (prune s).2.1) :
    t.1 < 16 ∧ t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep s.1 (poolView s.2.1) T n → Rep t.1 (poolView t.2.1) T n) := by
  refine ⟨by simpa only [ht] using hu, ?_⟩
  rcases hps with he | he
  · rw [he, ht]
    exact ⟨hlen, hp, fun _ _ h => h⟩
  · rw [he, ht]
    exact ⟨prune_pools_length s, poolsGood_prune hp, fun _ _ h => rep_prune hu hp h⟩

lemma zero_binary_positive_state {s : State} (a b : ℕ) (isAnd : Bool) (rest : Multiset ℕ)
    (hu : s.1 < 16) (hlen : s.2.1.length = 7) (hp : PoolsGood (poolView s.2.1))
    (hz : (s.2.2.1 : Multiset ℕ) =
      ZeroTransitions.token a + ZeroTransitions.token b + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      t.1 = s.1 ∧ t.2.2.2 = s.2.2.2 ∧
      (t.2.2.1 : Multiset ℕ) =
        ZeroTransitions.token (if isAnd then a &&& b else a ||| b) + rest ∧
      t.1 < 16 ∧ t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep s.1 (poolView s.2.1) T n → Rep t.1 (poolView t.2.1) T n) := by
  obtain ⟨t, hr, hz', ht, hf, hps⟩ := ZeroTransitions.zero_binary a b isAnd rest hz
  exact ⟨t, hr, ht, hf, hz', frame_preserves hu hlen hp ht hps⟩

end OncePositive


namespace OncePositive

open OnceResource OnceGeometry

lemma insertZero_multiset (k : ℕ) (xs : List ℕ) :
    (insertZero k xs : Multiset ℕ) = {k} + (xs : Multiset ℕ) := by
  simpa only [Multiset.singleton_add, Multiset.cons_coe] using
    (Multiset.coe_eq_coe.mpr (insertZero_perm k xs))

lemma fork_state_spec {s t : State} {k : ℕ}
    (hk : k ∈ s.2.2.1) (hf : s.2.2.2 = false) (hu : s.1 < 16)
    (hp : PoolsGood (poolView s.2.1))
    (ht : t = prune (s.1, s.2.1, insertZero k s.2.2.1, true)) :
    t ∈ successors s ∧ t.1 = s.1 ∧ t.2.1.length = 7 ∧
      PoolsGood (poolView t.2.1) ∧
      (∀ (S : Finset (Fin 10)) (m : ℕ), Rep s.1 (poolView s.2.1) S m →
        Rep t.1 (poolView t.2.1) S m) ∧
      (t.2.2.1 : Multiset ℕ) = {k} + (s.2.2.1 : Multiset ℕ) ∧ t.2.2.2 = true := by
  subst t
  refine ⟨fork_successor hk hf, rfl, prune_pools_length _, poolsGood_prune hp, ?_, ?_, rfl⟩
  · intro S m h
    exact rep_prune (s := (s.1, s.2.1, insertZero k s.2.2.1, true)) hu hp h
  · exact insertZero_multiset k s.2.2.1

lemma exists_fork_state {s : State} {k : ℕ}
    (hk : k ∈ s.2.2.1) (hf : s.2.2.2 = false) (hu : s.1 < 16)
    (hp : PoolsGood (poolView s.2.1)) :
    ∃ t : State, t ∈ successors s ∧ t.1 = s.1 ∧ t.2.1.length = 7 ∧
      PoolsGood (poolView t.2.1) ∧
      (∀ (S : Finset (Fin 10)) (m : ℕ), Rep s.1 (poolView s.2.1) S m →
        Rep t.1 (poolView t.2.1) S m) ∧
      (t.2.2.1 : Multiset ℕ) = {k} + (s.2.2.1 : Multiset ℕ) ∧ t.2.2.2 = true := by
  exact ⟨prune (s.1, s.2.1, insertZero k s.2.2.1, true), fork_state_spec hk hf hu hp rfl⟩

end OncePositive


namespace OnceResource.ZeroTransitions

lemma fork_token {s : State} (k : ℕ) (rest : Multiset ℕ)
    (hf : s.2.2.2 = false) (hz : (s.2.2.1 : Multiset ℕ) = token k + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      (t.2.2.1 : Multiset ℕ) = token k + token k + rest ∧
      t.1 = s.1 ∧ t.2.2.2 = decide (k ≠ 0) ∧
      (t.2.1 = s.2.1 ∨ t.2.1 = (prune s).2.1) := by
  by_cases hk : k = 0
  · refine ⟨s, Relation.ReflTransGen.refl, ?_, rfl, ?_, Or.inl rfl⟩
    · simpa [token, hk] using hz
    · simpa [hk] using hf
  · have hz' : (s.2.2.1 : Multiset ℕ) = {k} + rest := by simpa [token, hk] using hz
    have hm := mem_of_zero_eq hz'
    refine ⟨prune (s.1, s.2.1, insertZero k s.2.2.1, true),
      Relation.ReflTransGen.single (fork_successor hm hf), ?_, rfl, ?_, Or.inr rfl⟩
    · change (insertZero k s.2.2.1 : Multiset ℕ) = token k + token k + rest
      rw [coe_insertZero, hz']
      simp [token, hk]
    · simp [prune, hk]

end OnceResource.ZeroTransitions

namespace OncePositive

open OnceResource OnceGeometry

lemma zero_fork_positive_state {s : State} (k : ℕ) (rest : Multiset ℕ)
    (hu : s.1 < 16) (hlen : s.2.1.length = 7) (hp : PoolsGood (poolView s.2.1))
    (hf : s.2.2.2 = false)
    (hz : (s.2.2.1 : Multiset ℕ) = ZeroTransitions.token k + rest) :
    ∃ t : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) s t ∧
      t.1 = s.1 ∧ t.2.2.2 = decide (k ≠ 0) ∧
      (t.2.2.1 : Multiset ℕ) =
        ZeroTransitions.token k + ZeroTransitions.token k + rest ∧
      t.1 < 16 ∧ t.2.1.length = 7 ∧ PoolsGood (poolView t.2.1) ∧
      (∀ T n, Rep s.1 (poolView s.2.1) T n → Rep t.1 (poolView t.2.1) T n) := by
  obtain ⟨t, hr, hz', ht, hf', hps⟩ := ZeroTransitions.fork_token k rest hf hz
  exact ⟨t, hr, ht, hf', hz', frame_preserves hu hlen hp ht hps⟩

end OncePositive


namespace OnceResource.IndexCopies

def Reads (start : ℕ) (A B : ℕ → ℕ) (t x : ℕ) : Prop :=
  A (start + t) = x ∨ B (start + t) = x

def Readers (start : ℕ) (A B : ℕ → ℕ) (t x : ℕ) : Finset ℕ :=
  (Finset.range t).filter (fun j => A (start + j) = x ∨ B (start + j) = x)

def ReadCount (start : ℕ) (A B : ℕ → ℕ) (t x : ℕ) : ℕ :=
  (Readers start A B t x).card

def Capacity (fork x : ℕ) : ℕ := if x = fork then 2 else 1

def Valid (start : ℕ) (A B : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ t < n, A (start + t) < start + t ∧ B (start + t) < start + t ∧
    A (start + t) ≠ B (start + t)

lemma readers_mono {start t n x : ℕ} {A B : ℕ → ℕ} (ht : t ≤ n) :
    Readers start A B t x ⊆ Readers start A B n x := by
  intro j hj
  obtain ⟨hj, hr⟩ := Finset.mem_filter.mp hj
  exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hj) ht), hr⟩

lemma readCount_succ (start : ℕ) (A B : ℕ → ℕ) (t x : ℕ) :
    ReadCount start A B (t + 1) x = ReadCount start A B t x +
      if A (start + t) = x ∨ B (start + t) = x then 1 else 0 := by
  have hnot : t ∉ Readers start A B t x := by simp [Readers]
  unfold ReadCount Readers
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with hr
  · exact Finset.card_insert_of_notMem hnot
  · simp

lemma earlier_readers_lt_capacity {start n t x fork : ℕ} {A B : ℕ → ℕ}
    (ht : t < n) (hr : Reads start A B t x)
    (hcap : ReadCount start A B n x ≤ Capacity fork x) :
    ReadCount start A B t x < Capacity fork x := by
  have hle := Finset.card_le_card (readers_mono (start := start) (A := A) (B := B)
    (x := x) (show t + 1 ≤ n by omega))
  change ReadCount start A B (t + 1) x ≤ ReadCount start A B n x at hle
  rw [readCount_succ] at hle
  change A (start + t) = x ∨ B (start + t) = x at hr
  rw [ite_eq_left hr] at hle
  omega

lemma earlier_readers_fork_le_one {start n t fork : ℕ} {A B : ℕ → ℕ}
    (ht : t < n) (hr : Reads start A B t fork)
    (hcap : ReadCount start A B n fork ≤ 2) :
    ReadCount start A B t fork ≤ 1 := by
  have h := earlier_readers_lt_capacity (fork := fork) ht hr (by simpa [Capacity] using hcap)
  simp [Capacity] at h
  omega

lemma earlier_readers_other_zero {start n t x fork : ℕ} {A B : ℕ → ℕ}
    (hx : x ≠ fork) (ht : t < n) (hr : Reads start A B t x)
    (hcap : ReadCount start A B n x ≤ 1) :
    ReadCount start A B t x = 0 := by
  have h := earlier_readers_lt_capacity (fork := fork) ht hr (by simpa [Capacity, hx] using hcap)
  simp only [Capacity, ite_eq_right hx] at h
  omega

lemma readCount_zero_of_future {start n t x : ℕ} {A B : ℕ → ℕ}
    (hv : Valid start A B n) (ht : t ≤ n) (hx : start + t ≤ x) :
    ReadCount start A B t x = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨hj, hr⟩ := Finset.mem_filter.mp hj
  have hjt := Finset.mem_range.mp hj
  obtain ⟨ha, hb, _⟩ := hv j (by omega)
  rcases hr with hr | hr <;> omega

variable (Z : ℕ → Prop) [DecidablePred Z]

def Copies (fork x : ℕ) : ℕ := if Z x then Capacity fork x else 1

def Drop (i : ℕ) (ids : Multiset ℕ) : Multiset ℕ :=
  if Z i then ids.erase i else ids

def Give (fork out : ℕ) (ids : Multiset ℕ) : Multiset ℕ :=
  out ::ₘ (if Z out ∧ out = fork then out ::ₘ ids else ids)

def Initial (start fork : ℕ) : Multiset ℕ :=
  Multiset.range start + if Z fork ∧ fork < start then {fork} else 0

def Available (start fork : ℕ) (A B : ℕ → ℕ) : ℕ → Multiset ℕ
  | 0 => Initial Z start fork
  | t + 1 => Give Z fork (start + t)
      (Drop Z (B (start + t)) (Drop Z (A (start + t)) (Available start fork A B t)))

lemma count_drop (ids : Multiset ℕ) (i x : ℕ) :
    (Drop Z i ids).count x = ids.count x - if Z x ∧ x = i then 1 else 0 := by
  by_cases hxi : x = i
  · subst x
    by_cases hi : Z i <;> simp [Drop, hi, Multiset.count_erase_self]
  · by_cases hi : Z i <;> simp [Drop, hi, hxi, Multiset.count_erase_of_ne hxi]

lemma count_drop_two (ids : Multiset ℕ) {a b : ℕ} (hab : a ≠ b) (x : ℕ) :
    (Drop Z b (Drop Z a ids)).count x =
      ids.count x - if Z x ∧ (a = x ∨ b = x) then 1 else 0 := by
  rw [count_drop, count_drop]
  by_cases hz : Z x
  · by_cases hxa : x = a
    · subst x
      simp [hz, hab]
    · by_cases hxb : x = b
      · subst x
        simp [hz, hxa, Ne.symm hxa]
      · simp [hz, hxa, hxb, Ne.symm hxa, Ne.symm hxb]
  · simp [hz]

lemma count_give (ids : Multiset ℕ) (fork out x : ℕ) :
    (Give Z fork out ids).count x = ids.count x + if x = out then Copies Z fork out else 0 := by
  by_cases hf : out = fork
  · subst out
    by_cases hx : x = fork
    · subst x
      by_cases hz : Z fork <;> simp [Give, Copies, Capacity, hz, Nat.add_assoc]
    · by_cases hz : Z fork <;> simp [Give, hz, hx]
  · by_cases hx : x = out
    · subst x
      by_cases hz : Z out <;> simp [Give, Copies, Capacity, hz, hf]
    · simp [Give, hf, hx]

lemma count_initial (start fork x : ℕ) :
    (Initial Z start fork).count x = if x < start then Copies Z fork x else 0 := by
  have hrange : (Multiset.range start).count x = if x < start then 1 else 0 := by
    simpa using Multiset.count_eq_of_nodup (a := x) (Multiset.nodup_range start)
  by_cases hx : x < start <;> by_cases hxf : x = fork
  · subst x
    by_cases hz : Z fork <;>
      simp [Initial, Multiset.count_add, hrange, hx, hz, Copies, Capacity]
  · by_cases hz : Z fork ∧ fork < start <;> by_cases hzx : Z x <;>
      simp [Initial, Multiset.count_add, hrange, hx, hz, Copies, Capacity, hxf, hzx]
  · subst x
    simp [Initial, hx]
  · by_cases hz : Z fork ∧ fork < start <;>
      simp [Initial, hx, hz, hxf]

lemma count_available {start fork n : ℕ} {A B : ℕ → ℕ}
    (hv : Valid start A B n) (t : ℕ) (ht : t ≤ n) (x : ℕ) :
    (Available Z start fork A B t).count x =
      if x < start + t then
        if Z x then Capacity fork x - ReadCount start A B t x else 1
      else 0 := by
  induction t with
  | zero => simp [Available, count_initial, Copies, ReadCount, Readers]
  | succ t ih =>
    have ht' : t ≤ n := by omega
    have ih' := ih ht'
    obtain ⟨ha, hb, hab⟩ := hv t (by omega)
    rw [Available, count_give, count_drop_two Z _ hab, ih']
    by_cases hf : x = start + t
    · subst x
      have hrc := readCount_zero_of_future hv ht' (x := start + t) (by omega)
      have hr : ¬(A (start + t) = start + t ∨ B (start + t) = start + t) := by omega
      have hn : start + t < start + (t + 1) := by omega
      simp [readCount_succ, hrc, hr, hn, Copies]
    · by_cases hold : x < start + t
      · have hn : x < start + (t + 1) := by omega
        simp only [ite_eq_left hold, ite_eq_right hf, Nat.add_zero, ite_eq_left hn]
        rw [readCount_succ]
        by_cases hz : Z x
        · by_cases hr : A (start + t) = x ∨ B (start + t) = x <;>
            simp [hz, hr, Nat.sub_sub]
        · simp [hz]
      · have hn : ¬ x < start + (t + 1) := by omega
        have hna : A (start + t) ≠ x := by omega
        have hnb : B (start + t) ≠ x := by omega
        simp [hold, hf, hn, hna, hnb]

lemma source_available {start fork n t x : ℕ} {A B : ℕ → ℕ}
    (hv : Valid start A B n)
    (hcap : ∀ x, Z x → ReadCount start A B n x ≤ Capacity fork x)
    (ht : t < n) (hx : x < start + t) (hr : Reads start A B t x) :
    x ∈ Available Z start fork A B t := by
  apply Multiset.count_pos.mp
  rw [count_available Z hv t (by omega) x, ite_eq_left hx]
  by_cases hz : Z x
  · rw [ite_eq_left hz]
    have hlt := earlier_readers_lt_capacity ht hr (hcap x hz)
    omega
  · simp [hz]

lemma available_bounded {start fork n t x : ℕ} {A B : ℕ → ℕ}
    (hv : Valid start A B n) (ht : t ≤ n)
    (hx : x ∈ Available Z start fork A B t) : x < start + t := by
  have hpos := Multiset.count_pos.mpr hx
  rw [count_available Z hv t ht x] at hpos
  by_contra hnot
  simp [hnot] at hpos

lemma mem_drop_of_ne {ids : Multiset ℕ} {i x : ℕ} (hx : x ∈ ids) (hne : x ≠ i) :
    x ∈ Drop Z i ids := by
  unfold Drop
  split_ifs
  · exact (Multiset.mem_erase_of_ne hne).mpr hx
  · exact hx

lemma sources_available {start fork n t : ℕ} {A B : ℕ → ℕ}
    (hv : Valid start A B n)
    (hcap : ∀ x, Z x → ReadCount start A B n x ≤ Capacity fork x)
    (ht : t < n) :
    A (start + t) ∈ Available Z start fork A B t ∧
      B (start + t) ∈ Drop Z (A (start + t)) (Available Z start fork A B t) := by
  obtain ⟨ha, hb, hab⟩ := hv t ht
  constructor
  · exact source_available Z hv hcap ht ha (Or.inl rfl)
  · apply mem_drop_of_ne Z (source_available Z hv hcap ht hb (Or.inr rfl))
    exact Ne.symm hab

lemma initial_extra_iff (start fork : ℕ) :
    (if Z fork ∧ fork < start then ({fork} : Multiset ℕ) else 0) ≠ 0 ↔
      Z fork ∧ fork < start := by
  split_ifs with h
  · simp [h]
  · simp [h]

lemma creation_extra_unique {start fork t u : ℕ}
    (ht : Z (start + t) ∧ start + t = fork)
    (hu : Z (start + u) ∧ start + u = fork) : t = u := by omega

lemma initial_extra_excludes_creation {start fork t : ℕ}
    (hi : Z fork ∧ fork < start) : ¬(Z (start + t) ∧ start + t = fork) := by omega

lemma extra_before_iff (start fork t : ℕ) :
    (Z fork ∧ fork < start) ∨
      (∃ j < t, Z (start + j) ∧ start + j = fork) ↔
      Z fork ∧ fork < start + t := by
  constructor
  · rintro (hi | ⟨j, hj, hz, heq⟩)
    · exact ⟨hi.1, by omega⟩
    · exact ⟨heq ▸ hz, by omega⟩
  · intro h
    by_cases hi : fork < start
    · exact Or.inl ⟨h.1, hi⟩
    · refine Or.inr ⟨fork - start, by omega, ?_, by omega⟩
      have heq : start + (fork - start) = fork := by omega
      simpa only [heq] using h.1

def ExtraCount (start fork t : ℕ) : ℕ :=
  (if Z fork ∧ fork < start then 1 else 0) +
    ((Finset.range t).filter (fun j => Z (start + j) ∧ start + j = fork)).card

lemma extraCount_le_one (start fork t : ℕ) : ExtraCount Z start fork t ≤ 1 := by
  by_cases hi : Z fork ∧ fork < start
  · have he : (Finset.range t).filter (fun j => Z (start + j) ∧ start + j = fork) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro j hj
      have hj' := (Finset.mem_filter.mp hj).2
      omega
    simp [ExtraCount, hi, he]
  · simp only [ExtraCount, ite_eq_right hi, Nat.zero_add]
    apply Finset.card_le_one.mpr
    intro i hi j hj
    have hi' := (Finset.mem_filter.mp hi).2
    have hj' := (Finset.mem_filter.mp hj).2
    omega

lemma extraCount_pos_iff (start fork t : ℕ) :
    0 < ExtraCount Z start fork t ↔ Z fork ∧ fork < start + t := by
  rw [← extra_before_iff Z start fork t]
  by_cases hi : Z fork ∧ fork < start <;>
    simp [ExtraCount, hi, Nat.add_pos_iff_pos_or_pos, Finset.card_pos, Finset.Nonempty, Finset.mem_filter]

lemma extraCount_eq (start fork t : ℕ) :
    ExtraCount Z start fork t = if Z fork ∧ fork < start + t then 1 else 0 := by
  have hle := extraCount_le_one Z start fork t
  have hpos := extraCount_pos_iff Z start fork t
  split_ifs with h
  · have hp := hpos.mpr h
    omega
  · have hp : ¬0 < ExtraCount Z start fork t := fun hp => h (hpos.mp hp)
    omega

def Retain (x : ℕ) : Multiset ℕ := if Z x then 0 else {x}

lemma two_decomp {ids : Multiset ℕ} {a b : ℕ}
    (ha : a ∈ ids) (hb : b ∈ ids) (hab : a ≠ b) :
    ids = a ::ₘ b ::ₘ ((ids.erase a).erase b) := by
  have hb' := (Multiset.mem_erase_of_ne (Ne.symm hab)).mpr hb
  calc
    ids = a ::ₘ ids.erase a := (Multiset.cons_erase ha).symm
    _ = a ::ₘ b ::ₘ ((ids.erase a).erase b) :=
      congrArg (Multiset.cons a) (Multiset.cons_erase hb').symm

lemma drop_two_decomp {ids : Multiset ℕ} {a b : ℕ}
    (ha : a ∈ ids) (hb : b ∈ ids) (hab : a ≠ b) :
    Drop Z b (Drop Z a ids) =
      Retain Z a + Retain Z b + ((ids.erase a).erase b) := by
  by_cases hza : Z a <;> by_cases hzb : Z b
  · simp [Drop, Retain, hza, hzb]
  · simp only [Drop, Retain, hza, hzb, ↓reduceIte, Multiset.zero_add, Multiset.singleton_add]
    exact (Multiset.cons_erase ((Multiset.mem_erase_of_ne (Ne.symm hab)).mpr hb)).symm
  · simp only [Drop, Retain, hza, hzb, ↓reduceIte, Multiset.add_zero, Multiset.singleton_add]
    rw [Multiset.erase_comm]
    exact (Multiset.cons_erase ((Multiset.mem_erase_of_ne hab).mpr ha)).symm
  · simp only [Drop, Retain, hza, hzb, ↓reduceIte, Multiset.cons_add, Multiset.singleton_add]
    exact two_decomp ha hb hab

lemma available_step_decomp {start fork n t : ℕ} {A B : ℕ → ℕ}
    (hv : Valid start A B n)
    (hcap : ∀ x, Z x → ReadCount start A B n x ≤ Capacity fork x)
    (ht : t < n) :
    ∃ rest : Multiset ℕ,
      Available Z start fork A B t = A (start + t) ::ₘ B (start + t) ::ₘ rest ∧
      Available Z start fork A B (t + 1) =
        (start + t) ::ₘ
          (if Z (start + t) ∧ start + t = fork then
            (start + t) ::ₘ (Retain Z (A (start + t)) + Retain Z (B (start + t)) + rest)
          else Retain Z (A (start + t)) + Retain Z (B (start + t)) + rest) := by
  obtain ⟨ha, hb, hab⟩ := hv t ht
  have haa := source_available Z hv hcap ht ha (Or.inl rfl)
  have hba := source_available Z hv hcap ht hb (Or.inr rfl)
  refine ⟨((Available Z start fork A B t).erase (A (start + t))).erase (B (start + t)),
    two_decomp haa hba hab, ?_⟩
  simp only [Available, Give, drop_two_decomp Z haa hba hab]

end OnceResource.IndexCopies



namespace OnceResource.TokenMap

open IndexCopies

def token (k : ℕ) : Multiset ℕ := if k = 0 then 0 else {k}

def project (Z : ℕ → Prop) [DecidablePred Z] (M : ℕ → ℕ) (ids : Multiset ℕ) : Multiset ℕ :=
  (ids.filter (fun i => Z i ∧ M i ≠ 0)).map M

variable (Z : ℕ → Prop) [DecidablePred Z] (M : ℕ → ℕ)

lemma project_zero : project Z M 0 = 0 := by simp [project]

lemma project_cons (i : ℕ) (ids : Multiset ℕ) :
    project Z M (i ::ₘ ids) = (if Z i then token (M i) else 0) + project Z M ids := by
  by_cases hz : Z i <;> by_cases hm : M i = 0 <;>
    simp [project, hz, hm, token]

lemma project_add (ids rest : Multiset ℕ) :
    project Z M (ids + rest) = project Z M ids + project Z M rest := by
  simp [project]

lemma project_retain (i : ℕ) : project Z M (Retain Z i) = 0 := by
  by_cases hz : Z i <;> simp [Retain, project, hz]

lemma project_mem {i : ℕ} {ids : Multiset ℕ} (hi : i ∈ ids)
    (hz : Z i) (hm : M i ≠ 0) : M i ∈ project Z M ids := by
  exact Multiset.mem_map.mpr ⟨i, Multiset.mem_filter.mpr ⟨hi, hz, hm⟩, rfl⟩

lemma project_drop {i : ℕ} {ids : Multiset ℕ} (hi : i ∈ ids) :
    project Z M (Drop Z i ids) =
      if Z i ∧ M i ≠ 0 then (project Z M ids).erase (M i) else project Z M ids := by
  have heq : ids = i ::ₘ ids.erase i := (Multiset.cons_erase hi).symm
  by_cases hz : Z i
  · by_cases hm : M i = 0
    · simp only [Drop, hz, ↓reduceIte]
      rw [heq, project_cons]
      simp [hz, hm, token]
    · have hp : project Z M ids = M i ::ₘ project Z M (ids.erase i) := by
        rw [heq, project_cons]
        simp [hz, hm, token]
      simp [Drop, hz, hm, hp]
  · simp [Drop, hz]

lemma project_give (fork out : ℕ) (ids : Multiset ℕ) :
    project Z M (Give Z fork out ids) =
      (if Z out then token (M out) else 0) +
      (if Z out ∧ out = fork then token (M out) else 0) + project Z M ids := by
  by_cases hf : out = fork
  · subst out
    by_cases hz : Z fork <;> simp [Give, hz, project_cons, Multiset.add_assoc]
  · by_cases hz : Z out <;> simp [Give, hz, hf, project_cons]

lemma project_step {ids rest : Multiset ℕ} {a b out fork : ℕ}
    (hid : ids = a ::ₘ b ::ₘ rest) (hab : a ≠ b) :
    project Z M (Give Z fork out (Drop Z b (Drop Z a ids))) =
      (if Z out then token (M out) else 0) +
      (if Z out ∧ out = fork then token (M out) else 0) + project Z M rest := by
  rw [project_give]
  have ha : a ∈ ids := by rw [hid]; simp
  have hb : b ∈ ids := by rw [hid]; simp
  rw [drop_two_decomp Z ha hb hab, project_add, project_add, project_retain, project_retain]
  simp only [Multiset.zero_add]
  have herase : (ids.erase a).erase b = rest := by rw [hid]; simp
  rw [herase]

lemma project_initial_one {start seed : ℕ} (hseed : seed < start)
    (hzseed : Z seed) (hmseed : M seed ≠ 0)
    (hother : ∀i<start, Z i → i ≠ seed → M i = 0) :
    project Z M (Multiset.range start) = {M seed} := by
  have hf : (Multiset.range start).filter (fun i => Z i ∧ M i ≠ 0) = {seed} := by
    apply Multiset.ext.mpr
    intro i
    rw [Multiset.count_eq_of_nodup ((Multiset.nodup_range start).filter _)]
    by_cases hi : i = seed
    · subst i
      simp [hseed, hzseed, hmseed]
    · have hn : ¬(i ∈ Multiset.range start ∧ Z i ∧ M i ≠ 0) := by
        rintro ⟨hi', hz, hm⟩
        exact hm (hother i (Multiset.mem_range.mp hi') hz hi)
      simp only [Multiset.mem_range] at hn
      simp [hn, hi]
  simp [project, hf]

lemma project_initial {start seed fork : ℕ} (hseed : seed < start)
    (hzseed : Z seed) (hmseed : M seed ≠ 0)
    (hother : ∀i<start, Z i → i ≠ seed → M i = 0) :
    project Z M (Initial Z start fork) =
      {M seed} + if fork = seed then {M seed} else 0 := by
  rw [Initial, project_add, project_initial_one Z M hseed hzseed hmseed hother]
  congr 1
  by_cases hf : fork = seed
  · subst fork
    simp [hseed, hzseed, hmseed, project, Multiset.filter_singleton]
  · by_cases h : Z fork ∧ fork < start
    · have hm : M fork = 0 := hother fork h.2 h.1 hf
      simp [h, hf, project, hm]
    · simp [h, hf, project]

end OnceResource.TokenMap



namespace OnceSimulation
open OnceResource OnceGeometry OncePositive

def contrib (S : Finset (Fin 10)) (m : ℕ) : Multiset ℕ :=
  if S = ∅ then TokenMap.token m else 0

def Healthy (s : State) : Prop :=
  s.1 < 16 ∧ s.2.1.length = 7 ∧ PoolsGood (poolView s.2.1)

def Preserves (s t : State) : Prop :=
  ∀ T m, Rep s.1 (poolView s.2.1) T m → Rep t.1 (poolView t.2.1) T m

def LocalResult (s q : State) (S : Finset (Fin 10)) (m : ℕ)
    (rest : Multiset ℕ) (group : Option (Fin 4)) : Prop :=
  Relation.ReflTransGen (fun a b : State => b ∈ successors a) s q ∧
  q.2.2.2 = s.2.2.2 ∧ Healthy q ∧
  (q.2.2.1 : Multiset ℕ) = contrib S m + rest ∧ Preserves s q ∧
  (S.Nonempty → Rep q.1 (poolView q.2.1) S m) ∧
  (∀ g : Fin 4, q.1.testBit g.val = true → s.1.testBit g.val = true ∨ group = some g)

lemma lift_token_step {s : State} {S : Finset (Fin 10)} {m k : ℕ} {rest : Multiset ℕ}
    (hs : Healthy s) (hS : S.Nonempty) (hm : Rep s.1 (poolView s.2.1) S m)
    (hk : k < 64) (hz : (s.2.2.1 : Multiset ℕ) = TokenMap.token k + rest) :
    ∃ q, LocalResult s q S (m ||| k) rest none := by
  have hne : S ≠ ∅ := hS.ne_empty
  by_cases hk0 : k = 0
  · subst k
    refine ⟨s, Relation.ReflTransGen.refl, rfl, hs, ?_, (fun _ _ h => h), ?_, ?_⟩
    · simpa [contrib, TokenMap.token, hne] using hz
    · intro _
      simpa using hm
    · exact fun _ h => Or.inl h
  · have hmem : k ∈ s.2.2.1 := by
      have hm' : k ∈ (s.2.2.1 : Multiset ℕ) := by rw [hz]; simp [TokenMap.token, hk0]
      exact hm'
    obtain ⟨q, hr, hu, hqz, hf, hl, hp, hpres, hrep⟩ :=
      positive_lift_step hs.1 hs.2.1 hs.2.2 hm hS hk hmem
    refine ⟨q, hr, hf, ⟨by simpa [hu] using hs.1, hl, hp⟩, ?_, hpres,
      (fun _ => hrep), ?_⟩
    · rw [hqz, ← Multiset.coe_erase, hz]
      simp [contrib, hne, TokenMap.token, hk0]
    · intro g hg
      exact Or.inl (hu ▸ hg)

lemma or_local {s : State} {S T : Finset (Fin 10)} {a b : ℕ} {rest : Multiset ℕ}
    (hs : Healthy s) (ha : S.Nonempty → Rep s.1 (poolView s.2.1) S a)
    (hb : T.Nonempty → Rep s.1 (poolView s.2.1) T b)
    (hab : a < 64 ∧ b < 64)
    (hz : (s.2.2.1 : Multiset ℕ) = contrib S a + contrib T b + rest) :
    ∃ q, LocalResult s q (S ∪ T) (a ||| b) rest none := by
  by_cases hS : S = ∅
  · subst S
    by_cases hT : T = ∅
    · subst T
      have hz' : (s.2.2.1 : Multiset ℕ) =
          ZeroTransitions.token a + ZeroTransitions.token b + rest := by
        simpa [contrib, ZeroTransitions.token, TokenMap.token] using hz
      obtain ⟨q, hr, hu, hf, hqz, hqu, hql, hqp, hpres⟩ :=
        zero_binary_positive_state a b false rest hs.1 hs.2.1 hs.2.2 hz'
      refine ⟨q, hr, hf, ⟨hqu, hql, hqp⟩, ?_, hpres, ?_, ?_⟩
      · simpa [contrib, ZeroTransitions.token, TokenMap.token] using hqz
      · simp
      · intro g hg
        exact Or.inl (hu ▸ hg)
    · have hTn : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
      have hz' : (s.2.2.1 : Multiset ℕ) = TokenMap.token a + rest := by
        simpa [contrib, hT] using hz
      obtain ⟨q, hq⟩ := lift_token_step hs hTn (hb hTn) hab.1 hz'
      refine ⟨q, ?_⟩
      simpa [Nat.or_comm] using hq
  · have hSn : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS
    by_cases hT : T = ∅
    · subst T
      have hz' : (s.2.2.1 : Multiset ℕ) = TokenMap.token b + rest := by
        simpa [contrib, hS] using hz
      obtain ⟨q, hq⟩ := lift_token_step hs hSn (ha hSn) hab.2 hz'
      exact ⟨q, by simpa using hq⟩
    · have hTn : T.Nonempty := Finset.nonempty_iff_ne_empty.mpr hT
      have hST : S ∪ T ≠ ∅ := (hSn.mono Finset.subset_union_left).ne_empty
      refine ⟨s, Relation.ReflTransGen.refl, rfl, hs, ?_, (fun _ _ h => h), ?_, ?_⟩
      · simpa [contrib, hS, hT, hST] using hz
      · intro _
        exact rep_or hs.2.2 (ha hSn) (hb hTn)
      · exact fun _ h => Or.inl h

lemma marked_group {used : ℕ} {g h : Fin 4}
    (ht : (used ||| (1 <<< g.val)).testBit h.val = true) :
    used.testBit h.val = true ∨ g = h := by
  rw [Nat.testBit_or, Bool.or_eq_true] at ht
  rcases ht with ht | ht
  · exact Or.inl ht
  · right
    have hsingle := testBit_singleton_iff.mp ht
    exact Fin.ext hsingle

lemma pure_local {s : State} {g : Fin 4} {a b : ℕ} {rest : Multiset ℕ}
    (hs : Healthy s) (ha : Rep s.1 (poolView s.2.1) (port g false) a)
    (hb : Rep s.1 (poolView s.2.1) (port g true) b)
    (hk : a &&& b < 64) (hunused : s.1.testBit g.val = false)
    (hz : (s.2.2.1 : Multiset ℕ) = rest) :
    ∃ q, LocalResult s q ∅ (a &&& b) rest (some g) := by
  by_cases hk0 : a &&& b = 0
  · refine ⟨s, Relation.ReflTransGen.refl, rfl, hs, ?_, (fun _ _ h => h), ?_, ?_⟩
    · simpa [contrib, TokenMap.token, hk0] using hz
    · simp
    · exact fun _ h => Or.inl h
  · let q := prune (s.1 ||| (1 <<< g.val), s.2.1, insertZero (a &&& b) s.2.2.1, s.2.2.2)
    obtain ⟨hr, hu, hl, hp, hpres⟩ := positive_group_step hs.1 hs.2.2 ha hb hunused hk hk0
    refine ⟨q, Relation.ReflTransGen.single hr, rfl, ⟨hu, hl, hp⟩, ?_, hpres, ?_, ?_⟩
    · change (insertZero (a &&& b) s.2.2.1 : Multiset ℕ) = _
      rw [insertZero_multiset, hz]
      simp [contrib, TokenMap.token, hk0]
    · simp
    · intro h hh
      rcases marked_group hh with hh | hh
      · exact Or.inl hh
      · exact Or.inr (congrArg some hh)

lemma zero_local {s : State} {a b : ℕ} {rest : Multiset ℕ}
    (hs : Healthy s)
    (hz : (s.2.2.1 : Multiset ℕ) = TokenMap.token a + TokenMap.token b + rest) :
    ∃ q, LocalResult s q ∅ (a &&& b) rest none := by
  obtain ⟨q, hr, hu, hf, hqz, hqu, hql, hqp, hpres⟩ :=
    zero_binary_positive_state a b true rest hs.1 hs.2.1 hs.2.2 hz
  refine ⟨q, hr, hf, ⟨hqu, hql, hqp⟩, ?_, hpres, ?_, ?_⟩
  · exact hqz
  · simp
  · intro g hg
    exact Or.inl (hu ▸ hg)

end OnceSimulation



namespace OnceSimulation
open OnceResource OnceGeometry OncePositive

lemma gate_local {s : State} {S T U : Finset (Fin 10)} {a b c : ℕ}
    {rest : Multiset ℕ} (op : Bool) (group : Option (Fin 4))
    (hs : Healthy s) (ha : S.Nonempty → Rep s.1 (poolView s.2.1) S a)
    (hb : T.Nonempty → Rep s.1 (poolView s.2.1) T b)
    (hm : a < 64 ∧ b < 64 ∧ c < 64)
    (hz : (s.2.2.1 : Multiset ℕ) = contrib S a + contrib T b + rest)
    (hunused : ∀g : Fin 4, group = some g → s.1.testBit g.val = false)
    (hsem : if op then
      U = ∅ ∧ c = a &&& b ∧
        (match group with
        | none => S = ∅ ∧ T = ∅
        | some g => (S = port g false ∧ T = port g true) ∨
          (S = port g true ∧ T = port g false))
      else group = none ∧ U = S ∪ T ∧ c = a ||| b) :
    ∃q, LocalResult s q U c rest group := by
  cases op with
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at hsem
    obtain ⟨rfl, rfl, rfl⟩ := hsem
    exact or_local hs ha hb ⟨hm.1, hm.2.1⟩ hz
  | true =>
    simp only [↓reduceIte] at hsem
    obtain ⟨rfl, rfl, hports⟩ := hsem
    cases group with
    | none =>
      obtain ⟨rfl, rfl⟩ := hports
      exact zero_local hs (by simpa [contrib] using hz)
    | some g =>
      have hl : (port g false).Nonempty := by fin_cases g <;> decide
      have hr : (port g true).Nonempty := by fin_cases g <;> decide
      have hu := hunused g rfl
      rcases hports with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hz' : (s.2.2.1 : Multiset ℕ) = rest := by
          simpa [contrib, hl.ne_empty, hr.ne_empty] using hz
        exact pure_local hs (ha hl) (hb hr) hm.2.2 hu hz'
      · have hz' : (s.2.2.1 : Multiset ℕ) = rest := by
          simpa [contrib, hl.ne_empty, hr.ne_empty] using hz
        obtain ⟨q, hq⟩ := pure_local hs (hb hl) (ha hr)
          (by simpa [Nat.and_comm] using hm.2.2) hu hz'
        exact ⟨q, by simpa [Nat.and_comm] using hq⟩

end OnceSimulation


namespace OnceSimulation

open OnceResource OncePositive IndexCopies TokenMap

abbrev Reach (s t : State) : Prop :=
  Relation.ReflTransGen (fun a b : State => b ∈ successors a) s t

def ProgramCallback (S : ℕ → Finset (Fin 10)) (M A B : ℕ → ℕ)
    (G : ℕ → Option (Fin 4)) (start n : ℕ) : Prop :=
  ∀ t < n, ∀ (s : State) (rest : Multiset ℕ),
    Healthy s →
    ((S (A (start + t))).Nonempty →
      Rep s.1 (poolView s.2.1) (S (A (start + t))) (M (A (start + t)))) →
    ((S (B (start + t))).Nonempty →
      Rep s.1 (poolView s.2.1) (S (B (start + t))) (M (B (start + t)))) →
    (s.2.2.1 : Multiset ℕ) =
      contrib (S (A (start + t))) (M (A (start + t))) +
      contrib (S (B (start + t))) (M (B (start + t))) + rest →
    (∀ g : Fin 4, G (start + t) = some g → s.1.testBit g.val = false) →
    ∃ q : State, Reach s q ∧ q.2.2.2 = s.2.2.2 ∧ Healthy q ∧
      (q.2.2.1 : Multiset ℕ) = contrib (S (start + t)) (M (start + t)) + rest ∧
      Preserves s q ∧
      ((S (start + t)).Nonempty →
        Rep q.1 (poolView q.2.1) (S (start + t)) (M (start + t))) ∧
      ∀ g : Fin 4, q.1.testBit g.val = true →
        s.1.testBit g.val = true ∨ G (start + t) = some g

def GroupUnique (G : ℕ → Option (Fin 4)) (start n : ℕ) : Prop :=
  ∀ i < n, ∀ j < n, ∀ g : Fin 4,
    G (start + i) = some g → G (start + j) = some g → i = j

def ProgramInv (S : ℕ → Finset (Fin 10)) (M A B : ℕ → ℕ)
    (G : ℕ → Option (Fin 4)) (start fork t : ℕ) (s : State) : Prop :=
  Healthy s ∧
    (s.2.2.1 : Multiset ℕ) =
      project (fun w => S w = ∅) M (Available (fun w => S w = ∅) start fork A B t) ∧
    (∀ w < start + t, (S w).Nonempty → Rep s.1 (poolView s.2.1) (S w) (M w)) ∧
    s.2.2.2 = decide (S fork = ∅ ∧ M fork ≠ 0 ∧ fork < start + t) ∧
    ∀ g : Fin 4, s.1.testBit g.val = true → ∃ j < t, G (start + j) = some g

lemma preserves_refl (s : State) : Preserves s s := fun _ _ h => h

lemma preserves_trans {s t u : State} (hst : Preserves s t) (htu : Preserves t u) :
    Preserves s u := fun T m h => htu T m (hst T m h)

lemma finish_output_fork (S : ℕ → Finset (Fin 10)) (M : ℕ → ℕ)
    (fork out : ℕ) {q : State} {rest : Multiset ℕ}
    (hq : Healthy q)
    (hflag : q.2.2.2 = decide (S fork = ∅ ∧ M fork ≠ 0 ∧ fork < out))
    (hzero : (q.2.2.1 : Multiset ℕ) = contrib (S out) (M out) + rest) :
    ∃ r : State, Reach q r ∧ r.1 = q.1 ∧ Healthy r ∧ Preserves q r ∧
      (r.2.2.1 : Multiset ℕ) =
        contrib (S out) (M out) + (if S out = ∅ ∧ out = fork then token (M out) else 0) + rest ∧
      r.2.2.2 = decide (S fork = ∅ ∧ M fork ≠ 0 ∧ fork < out + 1) := by
  by_cases hevent : S out = ∅ ∧ out = fork ∧ M out ≠ 0
  · obtain ⟨hz, hout, hm⟩ := hevent
    subst fork
    have hf : q.2.2.2 = false := by simp [hflag]
    have hk : M out ∈ q.2.2.1 := by
      have hk' : M out ∈ (q.2.2.1 : Multiset ℕ) := by
        rw [hzero]
        simp [contrib, hz, token, hm]
      exact hk'
    obtain ⟨r, hr, hused, hlen, hgood, hpres, hzeros, htrue⟩ :=
      exists_fork_state hk hf hq.1 hq.2.2
    refine ⟨r, Relation.ReflTransGen.single hr, hused, ?_, hpres, ?_, ?_⟩
    · exact ⟨hused ▸ hq.1, hlen, hgood⟩
    · rw [hzeros, hzero]
      simp [contrib, hz, token, hm, Multiset.add_assoc]
    · simp [htrue, hz, hm]
  · refine ⟨q, Relation.ReflTransGen.refl, rfl, hq, preserves_refl q, ?_, ?_⟩
    · rw [hzero]
      by_cases hz : S out = ∅
      · by_cases ho : out = fork
        · have hm : M out = 0 := by by_contra hm; exact hevent ⟨hz, ho, hm⟩
          subst fork
          simp [hz, hm, token]
        · simp [ho]
      · simp [hz]
    · rw [hflag]
      congr 1
      apply propext
      constructor
      · rintro ⟨hz, hm, hf⟩
        exact ⟨hz, hm, by omega⟩
      · rintro ⟨hz, hm, hf⟩
        refine ⟨hz, hm, ?_⟩
        have hne : out ≠ fork := by
          intro ho
          exact hevent ⟨ho ▸ hz, ho, ho ▸ hm⟩
        omega

lemma program_inv_step {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 4)} {start fork n t : ℕ} {s : State}
    (hv : Valid start A B n)
    (hcap : ∀ w, S w = ∅ → ReadCount start A B n w ≤ Capacity fork w)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback S M A B G start n)
    (ht : t < n) (hinv : ProgramInv S M A B G start fork t s) :
    ∃ r : State, Reach s r ∧ ProgramInv S M A B G start fork (t + 1) r := by
  obtain ⟨hhealthy, hzeros, hreps, hflag, hused⟩ := hinv
  obtain ⟨ha, hb, hab⟩ := hv t ht
  obtain ⟨rest, hids, _⟩ := available_step_decomp (fun w => S w = ∅) hv hcap ht
  have hzero_input : (s.2.2.1 : Multiset ℕ) =
      contrib (S (A (start + t))) (M (A (start + t))) +
      contrib (S (B (start + t))) (M (B (start + t))) + project (fun w => S w = ∅) M rest := by
    rw [hzeros, hids, project_cons, project_cons]
    simp only [contrib, Multiset.add_assoc]
  have hunused : ∀ g : Fin 4, G (start + t) = some g → s.1.testBit g.val = false := by
    intro g hg
    cases hbit : s.1.testBit g.val with
    | false => rfl
    | true =>
      obtain ⟨j, hj, hjg⟩ := hused g hbit
      have heq := hgroups t ht j (by omega) g hg hjg
      omega
  obtain ⟨q, hreachq, hflagq, hhealthyq, hzeroq, hpresq, hnewq, husedq⟩ :=
    hcallback t ht s (project (fun w => S w = ∅) M rest) hhealthy
      (hreps _ ha) (hreps _ hb) hzero_input hunused
  obtain ⟨r, hreachr, husedr, hhealthyr, hpresr, hzeror, hflagr⟩ :=
    finish_output_fork S M fork (start + t) hhealthyq (hflagq.trans hflag) hzeroq
  refine ⟨r, hreachq.trans hreachr, hhealthyr, ?_, ?_, ?_, ?_⟩
  · rw [Available, project_step (fun w => S w = ∅) M hids hab]
    exact hzeror
  · intro w hw hSw
    by_cases hold : w < start + t
    · exact hpresr _ _ (hpresq _ _ (hreps w hold hSw))
    · have heq : w = start + t := by omega
      subst w
      exact hpresr _ _ (hnewq hSw)
  · simpa only [Nat.add_assoc] using hflagr
  · intro g hg
    rw [husedr] at hg
    rcases husedq g hg with hg | hg
    · obtain ⟨j, hj, hjg⟩ := hused g hg
      exact ⟨j, by omega, hjg⟩
    · exact ⟨t, by omega, hg⟩

lemma program_induction_prefix {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 4)} {start fork n : ℕ} {s₀ : State}
    (hv : Valid start A B n)
    (hcap : ∀ w, S w = ∅ → ReadCount start A B n w ≤ Capacity fork w)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback S M A B G start n)
    (hinit : ProgramInv S M A B G start fork 0 s₀) :
    ∀ t ≤ n, ∃ s : State, Reach s₀ s ∧ ProgramInv S M A B G start fork t s := by
  intro t
  induction t with
  | zero =>
    intro _
    exact ⟨s₀, Relation.ReflTransGen.refl, hinit⟩
  | succ t ih =>
    intro ht
    obtain ⟨s, hreach, hinv⟩ := ih (by omega)
    obtain ⟨r, hstep, hinvr⟩ := program_inv_step hv hcap hgroups hcallback (by omega) hinv
    exact ⟨r, hreach.trans hstep, hinvr⟩

lemma program_induction {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 4)} {start fork n : ℕ} {s₀ : State}
    (hv : Valid start A B n)
    (hcap : ∀ w, S w = ∅ → ReadCount start A B n w ≤ Capacity fork w)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback S M A B G start n)
    (hinit : ProgramInv S M A B G start fork 0 s₀) :
    ∃ s : State, Reach s₀ s ∧ ProgramInv S M A B G start fork n s :=
  program_induction_prefix hv hcap hgroups hcallback hinit n (Nat.le_refl n)

end OnceSimulation



namespace OnceSimulation
open OnceResource OnceGeometry OncePositive

def ProgramSemantics (S : ℕ → Finset (Fin 10)) (M A B : ℕ → ℕ)
    (G : ℕ → Option (Fin 4)) (Op : ℕ → Bool) (start n : ℕ) : Prop :=
  ∀ t < n,
    if Op (start + t) then
      S (start + t) = ∅ ∧ M (start + t) = M (A (start + t)) &&& M (B (start + t)) ∧
        (match G (start + t) with
        | none => S (A (start + t)) = ∅ ∧ S (B (start + t)) = ∅
        | some g =>
          (S (A (start + t)) = port g false ∧ S (B (start + t)) = port g true) ∨
          (S (A (start + t)) = port g true ∧ S (B (start + t)) = port g false))
    else G (start + t) = none ∧
      S (start + t) = S (A (start + t)) ∪ S (B (start + t)) ∧
      M (start + t) = M (A (start + t)) ||| M (B (start + t))

lemma semantic_callback {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 4)} {Op : ℕ → Bool} {start n : ℕ}
    (hm : ∀w, M w < 64) (hsem : ProgramSemantics S M A B G Op start n) :
    ProgramCallback S M A B G start n := by
  intro t ht s rest hs ha hb hz hgroups
  generalize hg : G (start + t) = group at hgroups ⊢
  cases group with
  | none =>
    exact gate_local (Op (start + t)) none hs ha hb
      ⟨hm _, hm _, hm _⟩ hz hgroups (by simpa [hg] using hsem t ht)
  | some g =>
    exact gate_local (Op (start + t)) (some g) hs ha hb
      ⟨hm _, hm _, hm _⟩ hz hgroups (by simpa [hg] using hsem t ht)

end OnceSimulation


namespace OnceSimulation

open OnceResource OnceGeometry OncePositive

lemma initial_state_witness (S : ℕ → Finset (Fin 10)) (M : ℕ → ℕ)
    {start seed fork : ℕ} (hseed : seed < start)
    (hSseed : S seed = ∅) (hMseed : M seed = 63)
    (hother : ∀ w < start, S w = ∅ → w ≠ seed → M w = 0)
    (hpositive : ∀ w < start, (S w).Nonempty → M w = rawMask (S w)) :
    ∃ s : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) initial s ∧
      Healthy s ∧ s.1 = 0 ∧
      (s.2.2.1 : Multiset ℕ) = TokenMap.project (fun w => S w = ∅) M
        (IndexCopies.Initial (fun w => S w = ∅) start fork) ∧
      (∀ w < start, (S w).Nonempty → Rep s.1 (poolView s.2.1) (S w) (M w)) ∧
      s.2.2.2 = decide (S fork = ∅ ∧ M fork ≠ 0 ∧ fork < start) := by
  have hi : Healthy initial := ⟨by decide, rfl, poolsGood_replicate_one⟩
  have hr : ∀ w < start, (S w).Nonempty →
      Rep initial.1 (poolView initial.2.1) (S w) (M w) := by
    intro w hw hS
    rw [hpositive w hw hS]
    exact rep_raw hi.2.2 _
  have hMne : M seed ≠ 0 := by rw [hMseed]; decide
  have hproj := TokenMap.project_initial (fun w => S w = ∅) M
    (fork := fork) hseed hSseed hMne hother
  rw [hMseed] at hproj
  have hflag : (S fork = ∅ ∧ M fork ≠ 0 ∧ fork < start) ↔ fork = seed := by
    constructor
    · rintro ⟨hS, hM, hlt⟩
      by_contra hne
      exact hM (hother fork hlt hS hne)
    · intro heq
      subst fork
      exact ⟨hSseed, hMne, hseed⟩
  by_cases hf : fork = seed
  · have hz : (initial.2.2.1 : Multiset ℕ) = ZeroTransitions.token 63 + 0 := by decide
    obtain ⟨s, hreach, hu, hfork, hzeros, hsused, hslen, hsgood, hpres⟩ :=
      zero_fork_positive_state 63 0 hi.1 hi.2.1 hi.2.2 rfl hz
    refine ⟨s, hreach, ⟨hsused, hslen, hsgood⟩, hu, ?_, ?_, ?_⟩
    · rw [hproj]
      simpa [hf, ZeroTransitions.token] using hzeros
    · intro w hw hS
      exact hpres _ _ (hr w hw hS)
    · rw [decide_eq_true (hflag.mpr hf)]
      simpa using hfork
  · refine ⟨initial, Relation.ReflTransGen.refl, hi, rfl, ?_, hr, ?_⟩
    · rw [hproj]
      simp [initial, hf]
    · simp [initial, hflag, hf]

end OnceSimulation


namespace OnceSimulation

open OnceResource OncePositive OnceGeometry IndexCopies TokenMap

lemma program_target_excluded {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 4)} {start fork n w : ℕ}
    (hsafe : ∀ s : State, Reach initial s → 56 ∉ s.2.2.1)
    (hv : Valid start A B n)
    (hcap : ∀ u, S u = ∅ → ReadCount start A B n u ≤ Capacity fork u)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback S M A B G start n)
    (hinit : ∃ s₀ : State, Reach initial s₀ ∧ ProgramInv S M A B G start fork 0 s₀)
    (hw : w ∈ Available (fun u => S u = ∅) start fork A B n)
    (hSw : S w = ∅) (hMw : M w = 56) : False := by
  obtain ⟨s₀, hreach₀, hinv₀⟩ := hinit
  obtain ⟨s, hreach, hinv⟩ := program_induction hv hcap hgroups hcallback hinv₀
  have hMne : M w ≠ 0 := by omega
  have hmem := project_mem (fun u => S u = ∅) M hw hSw hMne
  rw [hMw] at hmem
  have htarget : 56 ∈ s.2.2.1 := by
    have hm : 56 ∈ (s.2.2.1 : Multiset ℕ) := by
      rw [hinv.2.1]
      exact hmem
    exact hm
  exact hsafe s (hreach₀.trans hreach) htarget

lemma initial_program_inv (S : ℕ → Finset (Fin 10)) (M A B : ℕ → ℕ)
    (G : ℕ → Option (Fin 4)) {start seed fork : ℕ}
    (hseed : seed < start) (hSseed : S seed = ∅) (hMseed : M seed = 63)
    (hother : ∀ w < start, S w = ∅ → w ≠ seed → M w = 0)
    (hpositive : ∀ w < start, (S w).Nonempty → M w = rawMask (S w)) :
    ∃ s : State, Reach initial s ∧ ProgramInv S M A B G start fork 0 s := by
  obtain ⟨s, hreach, hhealthy, hused, hzeros, hreps, hflag⟩ :=
    initial_state_witness S M (fork := fork) hseed hSseed hMseed hother hpositive
  refine ⟨s, hreach, hhealthy, hzeros, ?_, ?_, ?_⟩
  · simpa only [Nat.add_zero] using hreps
  · simpa only [Nat.add_zero] using hflag
  · intro g hg
    simp [hused] at hg

lemma program_target_excluded_seed {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 4)} {start seed fork n w : ℕ}
    (hsafe : ∀ s : State, Reach initial s → 56 ∉ s.2.2.1)
    (hv : Valid start A B n)
    (hcap : ∀ u, S u = ∅ → ReadCount start A B n u ≤ Capacity fork u)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback S M A B G start n)
    (hseed : seed < start) (hSseed : S seed = ∅) (hMseed : M seed = 63)
    (hother : ∀ u < start, S u = ∅ → u ≠ seed → M u = 0)
    (hpositive : ∀ u < start, (S u).Nonempty → M u = rawMask (S u))
    (hw : w ∈ Available (fun u => S u = ∅) start fork A B n)
    (hSw : S w = ∅) (hMw : M w = 56) : False := by
  exact program_target_excluded hsafe hv hcap hgroups hcallback
    (initial_program_inv S M A B G hseed hSseed hMseed hother hpositive) hw hSw hMw

end OnceSimulation


namespace OnceSimulation

open OnceResource OncePositive OnceGeometry IndexCopies TokenMap

lemma program_target_excluded_certified {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 4)} {start fork n w : ℕ}
    (hv : Valid start A B n)
    (hcap : ∀ u, S u = ∅ → ReadCount start A B n u ≤ Capacity fork u)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback S M A B G start n)
    (hinit : ∃ s₀ : State, Reach initial s₀ ∧ ProgramInv S M A B G start fork 0 s₀)
    (hw : w ∈ Available (fun u => S u = ∅) start fork A B n)
    (hSw : S w = ∅) (hMw : M w = 56) : False := by
  exact program_target_excluded (fun _ h => reachable_no_target h)
    hv hcap hgroups hcallback hinit hw hSw hMw

lemma program_target_excluded_seed_certified {S : ℕ → Finset (Fin 10)} {M A B : ℕ → ℕ}
    {G : ℕ → Option (Fin 4)} {start seed fork n w : ℕ}
    (hv : Valid start A B n)
    (hcap : ∀ u, S u = ∅ → ReadCount start A B n u ≤ Capacity fork u)
    (hgroups : GroupUnique G start n) (hcallback : ProgramCallback S M A B G start n)
    (hseed : seed < start) (hSseed : S seed = ∅) (hMseed : M seed = 63)
    (hother : ∀ u < start, S u = ∅ → u ≠ seed → M u = 0)
    (hpositive : ∀ u < start, (S u).Nonempty → M u = rawMask (S u))
    (hw : w ∈ Available (fun u => S u = ∅) start fork A B n)
    (hSw : S w = ∅) (hMw : M w = 56) : False := by
  exact program_target_excluded_seed (fun _ h => reachable_no_target h)
    hv hcap hgroups hcallback hseed hSseed hMseed hother hpositive hw hSw hMw

end OnceSimulation


namespace OnceResourceBudget

open PEqualNP.Outside.L_meta_2590.DAGBridge.DagTools

variable {n : ℕ} {D : Dag}

lemma zero_reader_inner (hS : Strict n D) {j w : ℕ} (hj : j < D.length)
    (he : supp n D w = ∅) (hr : opA D j = w ∨ opB D j = w) :
    w ∈ (inner n D).filter (fun u => ¬(supp n D u).Nonempty) := by
  have hw : w < n + j := by
    obtain ⟨ha, hb, _⟩ := hS j hj
    rcases hr with hr | hr <;> omega
  apply Finset.mem_filter.mpr
  constructor
  · simp only [inner, Finset.mem_range]
    omega
  · simp [he]

lemma zero_branch_inner (hS : Strict n D) {w : ℕ} (he : supp n D w = ∅)
    (hf : 2 ≤ fanout D w) :
    w ∈ (inner n D).filter (fun u => ¬(supp n D u).Nonempty) := by
  have hp : 0 < (readers D w).card := by change 0 < fanout D w; omega
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hp
  obtain ⟨hj, hr⟩ := Finset.mem_filter.mp hj
  exact zero_reader_inner hS (Finset.mem_range.mp hj) he hr

lemma zero_fanout_le_two (hS : Strict n D) (hB : Bzero n D ≤ 1)
    {w : ℕ} (he : supp n D w = ∅) : fanout D w ≤ 2 := by
  by_cases hf : 2 ≤ fanout D w
  · have hsum : fanout D w - 1 ≤ Bzero n D := by
      unfold Bzero surplusOn
      exact Finset.single_le_sum (f := fun u => fanout D u - 1)
        (fun _ _ => Nat.zero_le _) (zero_branch_inner hS he hf)
    omega
  · omega

lemma zero_branch_unique (hS : Strict n D) (hB : Bzero n D ≤ 1)
    {a b : ℕ} (ha : supp n D a = ∅) (hb : supp n D b = ∅)
    (hfa : 2 ≤ fanout D a) (hfb : 2 ≤ fanout D b) : a = b := by
  by_contra hne
  have hsub : ({a, b} : Finset ℕ) ⊆
      (inner n D).filter (fun u => ¬(supp n D u).Nonempty) := by
    intro w hw
    rcases Finset.mem_insert.mp hw with rfl | hw
    · exact zero_branch_inner hS ha hfa
    · have hwb : w = b := Finset.mem_singleton.mp hw
      subst w
      exact zero_branch_inner hS hb hfb
  have hsum := Finset.sum_le_sum_of_subset (f := fun w => fanout D w - 1) hsub
  rw [Finset.sum_pair hne] at hsum
  unfold Bzero surplusOn at hB
  omega

lemma exists_fork_id (hS : Strict n D) (hB : Bzero n D ≤ 1) :
    ∃ fork : ℕ, ∀ w, supp n D w = ∅ →
      fanout D w ≤ if w = fork then 2 else 1 := by
  classical
  by_cases hb : ∃ b, supp n D b = ∅ ∧ 2 ≤ fanout D b
  · obtain ⟨b, hb, hfb⟩ := hb
    refine ⟨b, ?_⟩
    intro w hw
    by_cases hwb : w = b
    · simp only [hwb, ite_true]
      exact zero_fanout_le_two hS hB hb
    · simp only [hwb, ite_false]
      by_contra hbad
      have hwf : 2 ≤ fanout D w := by omega
      exact hwb (zero_branch_unique hS hB hw hb hwf hfb)
  · refine ⟨0, ?_⟩
    intro w hw
    have hf : fanout D w ≤ 1 := by
      by_contra hbad
      exact hb ⟨w, hw, by omega⟩
    split_ifs <;> omega

lemma readers_card_le_cap {fork : ℕ}
    (hcap : ∀ w, supp n D w = ∅ → fanout D w ≤ if w = fork then 2 else 1)
    {w : ℕ} (hw : supp n D w = ∅) :
    (readers D w).card ≤ if w = fork then 2 else 1 := hcap w hw

lemma zero_reader_pair_eq (hS : Strict n D) (hB : Bzero n D ≤ 1)
    {w j k l : ℕ} (hw : supp n D w = ∅)
    (hj : j < D.length) (hk : k < D.length) (hl : l < D.length)
    (rj : opA D j = w ∨ opB D j = w)
    (rk : opA D k = w ∨ opB D k = w)
    (rl : opA D l = w ∨ opB D l = w) : j = k ∨ j = l ∨ k = l := by
  by_contra h
  push Not at h
  have hsub : ({j, k, l} : Finset ℕ) ⊆ readers D w := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, rj⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, rk⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hl, rl⟩
  have hcard := Finset.card_le_card hsub
  have hthree : ({j, k, l} : Finset ℕ).card = 3 := by simp [h.1, h.2.1, h.2.2]
  rw [hthree] at hcard
  have htwo := zero_fanout_le_two hS hB hw
  change (readers D w).card ≤ 2 at htwo
  omega

end OnceResourceBudget


namespace OnceActualSchedule

open DAGBridge.DagTools OnceResource.IndexCopies

def start (g : ℕ) : ℕ := 10 + g + 1

def remaining (D : Dag) (g : ℕ) : ℕ := D.length - g - 1

def sourceA (D : Dag) (w : ℕ) : ℕ := opA D (w - 10)

def sourceB (D : Dag) (w : ℕ) : ℕ := opB D (w - 10)

abbrev Zero (D : Dag) (w : ℕ) : Prop := supp 10 D w = ∅

def ids (D : Dag) (g fork t : ℕ) : Multiset ℕ :=
  Available (Zero D) (start g) fork (sourceA D) (sourceB D) t

lemma continuation_index (g t : ℕ) : start g + t - 10 = g + 1 + t := by
  unfold start
  omega

lemma continuation_valid {D : Dag} (hS : Strict 10 D) (g : ℕ) :
    Valid (start g) (sourceA D) (sourceB D) (remaining D g) := by
  intro t ht
  have hj : g + 1 + t < D.length := by unfold remaining at ht; omega
  have hs := hS (g + 1 + t) hj
  have hout : 10 + (g + 1 + t) = start g + t := by unfold start; omega
  simpa only [sourceA, sourceB, continuation_index, hout] using hs

lemma continuation_readCount_le_fanout (D : Dag) (g w : ℕ) :
    ReadCount (start g) (sourceA D) (sourceB D) (remaining D g) w ≤ fanout D w := by
  unfold ReadCount fanout
  apply Finset.card_le_card_of_injOn (fun j => g + 1 + j)
  · intro j hj
    obtain ⟨hj, hr⟩ := Finset.mem_filter.mp hj
    have hjt := Finset.mem_range.mp hj
    have hjD : g + 1 + j < D.length := by unfold remaining at hjt; omega
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hjD, ?_⟩
    simpa only [sourceA, sourceB, continuation_index] using hr
  · intro i _ j _ heq
    change g + 1 + i = g + 1 + j at heq
    omega

lemma exists_continuation_fork {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D ≤ 1)
    (g : ℕ) :
    ∃ fork : ℕ, ∀ w, Zero D w →
      ReadCount (start g) (sourceA D) (sourceB D) (remaining D g) w ≤ Capacity fork w := by
  obtain ⟨fork, hcap⟩ := OnceResourceBudget.exists_fork_id hS hB
  refine ⟨fork, ?_⟩
  intro w hw
  exact (continuation_readCount_le_fanout D g w).trans (hcap w hw)

lemma actual_sources_available {D : Dag} (hS : Strict 10 D) {g fork t : ℕ}
    (hcap : ∀ w, Zero D w →
      ReadCount (start g) (sourceA D) (sourceB D) (remaining D g) w ≤ Capacity fork w)
    (ht : t < remaining D g) :
    opA D (g + 1 + t) ∈ ids D g fork t ∧
      opB D (g + 1 + t) ∈ Drop (Zero D) (opA D (g + 1 + t)) (ids D g fork t) := by
  have hs := sources_available (Zero D) (continuation_valid hS g) hcap ht
  simpa only [ids, sourceA, sourceB, continuation_index] using hs

lemma actual_available_step_decomp {D : Dag} (hS : Strict 10 D) {g fork t : ℕ}
    (hcap : ∀ w, Zero D w →
      ReadCount (start g) (sourceA D) (sourceB D) (remaining D g) w ≤ Capacity fork w)
    (ht : t < remaining D g) :
    ∃ rest : Multiset ℕ,
      ids D g fork t = opA D (g + 1 + t) ::ₘ opB D (g + 1 + t) ::ₘ rest ∧
      ids D g fork (t + 1) =
        (start g + t) ::ₘ
          (if Zero D (start g + t) ∧ start g + t = fork then
            (start g + t) ::ₘ
              (Retain (Zero D) (opA D (g + 1 + t)) + Retain (Zero D) (opB D (g + 1 + t)) + rest)
          else Retain (Zero D) (opA D (g + 1 + t)) + Retain (Zero D) (opB D (g + 1 + t)) + rest) := by
  have hs := available_step_decomp (Zero D) (continuation_valid hS g) hcap ht
  simpa only [ids, sourceA, sourceB, continuation_index] using hs

lemma actual_id_count {D : Dag} (hS : Strict 10 D) (g fork t w : ℕ)
    (ht : t ≤ remaining D g) :
    (ids D g fork t).count w =
      if w < start g + t then
        if Zero D w then Capacity fork w - ReadCount (start g) (sourceA D) (sourceB D) t w else 1
      else 0 := by
  exact count_available (Zero D) (continuation_valid hS g) t ht w

lemma actual_extra_count (D : Dag) (g fork t : ℕ) :
    ExtraCount (Zero D) (start g) fork t = if Zero D fork ∧ fork < start g + t then 1 else 0 := by
  exact extraCount_eq (Zero D) (start g) fork t

lemma exists_actual_sources {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D ≤ 1) (g : ℕ) :
    ∃ fork : ℕ,
      (∀ w, Zero D w →
        ReadCount (start g) (sourceA D) (sourceB D) (remaining D g) w ≤ Capacity fork w) ∧
      ∀ t < remaining D g,
        opA D (g + 1 + t) ∈ ids D g fork t ∧
          opB D (g + 1 + t) ∈ Drop (Zero D) (opA D (g + 1 + t)) (ids D g fork t) := by
  obtain ⟨fork, hcap⟩ := exists_continuation_fork hS hB g
  exact ⟨fork, hcap, fun _ ht => actual_sources_available hS hcap ht⟩

end OnceActualSchedule


namespace OnceActualSchedule

open DAGBridge.DagTools OnceResource.IndexCopies

lemma final_fanout_zero {D : Dag} (hS : Strict 10 D) : fanout D (outW 10 D) = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro j hj
  obtain ⟨hj, hr⟩ := Finset.mem_filter.mp hj
  have hjD := Finset.mem_range.mp hj
  obtain ⟨ha, hb, _⟩ := hS j hjD
  unfold outW at hr
  rcases hr with hr | hr <;> omega

lemma final_readCount_zero {D : Dag} (hS : Strict 10 D) (g : ℕ) :
    ReadCount (start g) (sourceA D) (sourceB D) (remaining D g) (outW 10 D) = 0 := by
  have hle := continuation_readCount_le_fanout D g (outW 10 D)
  rw [final_fanout_zero hS] at hle
  omega

lemma final_output_count {D : Dag} (hS : Strict 10 D) {g : ℕ}
    (hg : g < D.length) (fork : ℕ) :
    (ids D g fork (remaining D g)).count (outW 10 D) = Copies (Zero D) fork (outW 10 D) := by
  rw [actual_id_count hS g fork (remaining D g) (outW 10 D) (Nat.le_refl _)]
  have hbound : outW 10 D < start g + remaining D g := by
    unfold outW start remaining
    omega
  rw [ite_eq_left hbound, final_readCount_zero hS g]
  simp only [Copies, Nat.sub_zero]

lemma final_output_available {D : Dag} (hS : Strict 10 D) {g : ℕ}
    (hg : g < D.length) (fork : ℕ) :
    outW 10 D ∈ ids D g fork (remaining D g) := by
  apply Multiset.count_pos.mp
  rw [final_output_count hS hg fork]
  unfold Copies Capacity
  split_ifs <;> decide

end OnceActualSchedule


namespace OnceGeometry

open PEqualNP.Outside.L_meta_2590.DAGBridge.DagTools

lemma rowSet_mem_crossPairs : ∀ r : Fin 6,
    rowSet r ∈ FiveGroup.ResourceExclusion.CrossPairs := by decide

lemma wireMask_of_ordinary {D : Dag} (hS : Strict 10 D) {w : ℕ}
    (ho : FiveGroup.ResourceExclusion.Ordinary (FiveGroup.DAGBridge.DagResource D w)) :
    wireMask D w = rawMask (supp 10 D w) := by
  unfold wireMask rawMask
  apply congrArg mask
  funext r
  have hu := ho (rowSet r) (rowSet_mem_crossPairs r)
  change val D (rowInput r) w = true → (supp 10 D w ∩ rowSet r).Nonempty at hu
  by_cases hh : (supp 10 D w ∩ rowSet r).Nonempty
  · rw [support_row_true hS hh, decide_eq_true hh]
  · cases hv : val D (rowInput r) w with
    | false => simp [hh]
    | true => exact False.elim (hh (hu hv))

lemma before_seed_wireMask {D : Dag} (hS : Strict 10 D) {g : ℕ}
    (hg : g < D.length) (hsides : FiveGroup.DAGBridge.OtherAndSides D g)
    {w : ℕ} (hw : w < 10 + g) :
    wireMask D w = rawMask (supp 10 D w) :=
  wireMask_of_ordinary hS (FiveGroup.DAGBridge.before_seed_ordinary hS hg hsides w hw)

lemma before_seed_zero {D : Dag} (hS : Strict 10 D) {g : ℕ}
    (hg : g < D.length) (hsides : FiveGroup.DAGBridge.OtherAndSides D g)
    {w : ℕ} (hw : w < 10 + g) (hz : supp 10 D w = ∅) : wireMask D w = 0 := by
  rw [before_seed_wireMask hS hg hsides hw, hz, rawMask_empty]

lemma dirty_wire_mask_unoriented {D : Dag} (hS : Strict 10 D) {g : ℕ}
    (hg : g < D.length) (ht : tag D g = true)
    (hdirty : FiveGroup.DAGBridge.DirtySides D g) : wireMask D (10 + g) = 63 := by
  have hd := (FiveGroup.DAGBridge.dirty_seed hS hg ht hdirty).2
  have heq : (fun r => val D (rowInput r) (10 + g)) = (fun _ => true) := by
    funext r
    exact hd (rowSet r) (rowSet_mem_crossPairs r)
  unfold wireMask
  rw [heq]
  decide

lemma seed_initial_masks {D : Dag} (hS : Strict 10 D) {g : ℕ}
    (hg : g < D.length) (ht : tag D g = true)
    (hdirty : FiveGroup.DAGBridge.DirtySides D g)
    (hsides : FiveGroup.DAGBridge.OtherAndSides D g) :
    (∀ w < 10 + g, wireMask D w = rawMask (supp 10 D w)) ∧
      wireMask D (10 + g) = 63 := by
  exact ⟨fun _ hw => before_seed_wireMask hS hg hsides hw,
    dirty_wire_mask_unoriented hS hg ht hdirty⟩

end OnceGeometry


namespace OnceSimulation

open OnceResource OnceGeometry OncePositive
open PEqualNP.Outside.L_meta_2590.DAGBridge.DagTools

lemma actual_initial_state {D : Dag} (hS : Strict 10 D) {g fork : ℕ}
    (hg : g < D.length) (ht : tag D g = true)
    (hdirty : FiveGroup.DAGBridge.DirtySides D g)
    (hsides : FiveGroup.DAGBridge.OtherAndSides D g) :
    ∃ s : State,
      Relation.ReflTransGen (fun p q : State => q ∈ successors p) initial s ∧
      Healthy s ∧ s.1 = 0 ∧
      (s.2.2.1 : Multiset ℕ) = TokenMap.project (fun w => supp 10 D w = ∅) (wireMask D)
        (IndexCopies.Initial (fun w => supp 10 D w = ∅) (10 + g + 1) fork) ∧
      (∀ w < 10 + g + 1, (supp 10 D w).Nonempty →
        Rep s.1 (poolView s.2.1) (supp 10 D w) (wireMask D w)) ∧
      s.2.2.2 = decide (supp 10 D fork = ∅ ∧ wireMask D fork ≠ 0 ∧ fork < 10 + g + 1) := by
  have hseed : supp 10 D (10 + g) = ∅ :=
    (FiveGroup.DAGBridge.dirty_seed hS hg ht hdirty).1
  apply initial_state_witness (supp 10 D) (wireMask D) (seed := 10 + g)
    (by omega) hseed (dirty_wire_mask_unoriented hS hg ht hdirty)
  · intro w hw hz hne
    exact before_seed_zero hS hg hsides (by omega) hz
  · intro w hw hpos
    have hne : w ≠ 10 + g := by
      intro heq
      subst w
      exact hpos.ne_empty hseed
    exact before_seed_wireMask hS hg hsides (by omega)

end OnceSimulation


namespace OnceSimulation
open OnceResource OnceGeometry OncePositive OnceActualSchedule
open DAGBridge.DagTools

lemma actual_petersen_exclusion {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D ≤ 1)
    {g : ℕ} (hg : g < D.length) (ht : tag D g = true)
    (hdirty : FiveGroup.DAGBridge.DirtySides D g)
    (hsides : FiveGroup.DAGBridge.OtherAndSides D g)
    {G : ℕ → Option (Fin 4)}
    (hgroups : GroupUnique G (start g) (remaining D g))
    (hsem : ProgramSemantics (supp 10 D) (wireMask D) (sourceA D) (sourceB D) G
      (fun w => tag D (w - 10)) (start g) (remaining D g)) :
    ¬ ∀ x : Fin 10 → Bool, val D x (10 + D.length - 1) = edgeFn x := by
  intro hc
  obtain ⟨fork, hcap⟩ := exists_continuation_fork hS hB g
  obtain ⟨s₀, hr, hh, hu, hz, hp, hf⟩ := actual_initial_state (fork := fork) hS hg ht hdirty hsides
  have hinit : ∃ s₀ : State, Reach initial s₀ ∧
      ProgramInv (supp 10 D) (wireMask D) (sourceA D) (sourceB D) G (start g) fork 0 s₀ := by
    refine ⟨s₀, hr, hh, hz, ?_, ?_, ?_⟩
    · simpa only [start, Nat.add_zero] using hp
    · apply Bool.eq_iff_iff.mpr
      rw [hf]
      simp only [decide_eq_true_eq, start, Nat.add_zero]
      constructor
      · exact fun h => decide_eq_true h
      · exact fun h => of_decide_eq_true h
    · intro k hk
      simp [hu] at hk
  have hout : supp 10 D (10 + D.length - 1) = ∅ :=
    (FiveGroup.DAGBridge.target_of_computes hc).1
  exact program_target_excluded_certified (continuation_valid hS g) hcap hgroups
    (semantic_callback (wireMask_lt D) hsem) hinit
    (final_output_available hS hg fork) hout (wireMask_correct hc)

end OnceSimulation


namespace OnceSimulation
open OnceResource OnceGeometry OncePositive OnceActualSchedule
open DAGBridge.DagTools

lemma actual_target_exclusion {D : Dag} (hS : Strict 10 D) (hB : Bzero 10 D ≤ 1)
    {g : ℕ} (hg : g < D.length) (ht : tag D g = true)
    (hdirty : FiveGroup.DAGBridge.DirtySides D g)
    (hsides : FiveGroup.DAGBridge.OtherAndSides D g)
    {G : ℕ → Option (Fin 4)}
    (hgroups : GroupUnique G (start g) (remaining D g))
    (hsem : ProgramSemantics (supp 10 D) (wireMask D) (sourceA D) (sourceB D) G
      (fun w => tag D (w - 10)) (start g) (remaining D g)) :
    ¬ (supp 10 D (10 + D.length - 1) = ∅ ∧ wireMask D (10 + D.length - 1) = 56) := by
  intro hout
  obtain ⟨fork, hcap⟩ := exists_continuation_fork hS hB g
  obtain ⟨s₀, hr, hh, hu, hz, hp, hf⟩ := actual_initial_state (fork := fork) hS hg ht hdirty hsides
  have hinit : ∃ s₀ : State, Reach initial s₀ ∧
      ProgramInv (supp 10 D) (wireMask D) (sourceA D) (sourceB D) G (start g) fork 0 s₀ := by
    refine ⟨s₀, hr, hh, hz, ?_, ?_, ?_⟩
    · simpa only [start, Nat.add_zero] using hp
    · apply Bool.eq_iff_iff.mpr
      rw [hf]
      simp only [decide_eq_true_eq, start, Nat.add_zero]
      constructor
      · exact fun h => decide_eq_true h
      · exact fun h => of_decide_eq_true h
    · intro k hk
      simp [hu] at hk
  exact program_target_excluded_certified (continuation_valid hS g) hcap hgroups
    (semantic_callback (wireMask_lt D) hsem) hinit
    (final_output_available hS hg fork) hout.1 hout.2

end OnceSimulation

namespace OnceActualLabels
open DAGBridge.DagTools OnceGeometry

def firstFour (g : Fin 4) : Fin 5 := ⟨g.val, by omega⟩

noncomputable def label (gate : Fin 5 → ℕ) (j : ℕ) : Option (Fin 4) :=
  if h : ∃ g : Fin 4, j = gate (firstFour g) then some (Classical.choose h) else none

lemma firstFour_injective : Function.Injective firstFour := by
  intro a b h
  apply Fin.ext
  exact congrArg (fun x : Fin 5 => x.val) h

lemma label_some_iff {gate : Fin 5 → ℕ} (hinj : Function.Injective gate)
    (j : ℕ) (g : Fin 4) : label gate j = some g ↔ j = gate (firstFour g) := by
  classical
  unfold label
  split_ifs with h
  · constructor
    · intro he
      have he' : Classical.choose h = g := Option.some.inj he
      exact he' ▸ Classical.choose_spec h
    · intro he
      have he' : firstFour (Classical.choose h) = firstFour g :=
        hinj ((Classical.choose_spec h).symm.trans he)
      rw [firstFour_injective he']
  · simp only [Option.noConfusion, false_iff]
    intro he
    exact h ⟨g, he⟩

lemma label_none_iff (gate : Fin 5 → ℕ) (j : ℕ) :
    label gate j = none ↔ ∀ g : Fin 4, j ≠ gate (firstFour g) := by
  classical
  unfold label
  split_ifs with h
  · simp only [Option.some_ne_none, false_iff, not_forall, Classical.not_not]
    exact h
  · simp only [true_iff]
    intro g he
    exact h ⟨g, he⟩

lemma label_unique {gate : Fin 5 → ℕ} (hinj : Function.Injective gate)
    {j k : ℕ} {g : Fin 4} (hj : label gate j = some g)
    (hk : label gate k = some g) : j = k :=
  ((label_some_iff hinj j g).mp hj).trans ((label_some_iff hinj k g).mp hk).symm

lemma gate_split (k : Fin 5) : k = 4 ∨ ∃ g : Fin 4, k = firstFour g := by
  by_cases hk : k.val = 4
  · exact Or.inl (Fin.ext hk)
  · refine Or.inr ⟨⟨k.val, by omega⟩, ?_⟩
    rfl

lemma label_semantics {D : Dag} (hS : Strict 10 D) {gate : Fin 5 → ℕ}
    (hinj : Function.Injective gate)
    (hvalid : ∀ k, gate k < D.length ∧ tag D (gate k) = true)
    (hports : ∀ g : Fin 4,
      (supp 10 D (opA D (gate (firstFour g))) = port g false ∧
       supp 10 D (opB D (gate (firstFour g))) = port g true) ∨
      (supp 10 D (opA D (gate (firstFour g))) = port g true ∧
       supp 10 D (opB D (gate (firstFour g))) = port g false))
    (htypes : ∀ j, j < D.length → tag D j = true →
      (∃ k : Fin 5, j = gate k) ∨
      (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅))
    (j : ℕ) (hj : j < D.length) (hdirty : j ≠ gate 4) :
    if tag D j then
      supp 10 D (10+j) = ∅ ∧
      wireMask D (10+j) = wireMask D (opA D j) &&& wireMask D (opB D j) ∧
      (match label gate j with
      | none => supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅
      | some g =>
        (supp 10 D (opA D j) = port g false ∧ supp 10 D (opB D j) = port g true) ∨
        (supp 10 D (opA D j) = port g true ∧ supp 10 D (opB D j) = port g false))
    else label gate j = none ∧
      supp 10 D (10+j) = supp 10 D (opA D j) ∪ supp 10 D (opB D j) ∧
      wireMask D (10+j) = wireMask D (opA D j) ||| wireMask D (opB D j) := by
  classical
  have hm := wireMask_gate hS hj
  have hs := supp_gate hS j hj
  cases ht : tag D j with
  | false =>
    simp only [ht, Bool.false_eq_true, ↓reduceIte] at hm hs ⊢
    refine ⟨(label_none_iff gate j).mpr ?_, hs, hm⟩
    intro g he
    have hh := (hvalid (firstFour g)).2
    rw [← he, ht] at hh
    cases hh
  | true =>
    simp only [ht, ↓reduceIte] at hm hs ⊢
    cases hl : label gate j with
    | none =>
      have hz : supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅ := by
        rcases htypes j hj ht with ⟨k, hk⟩ | hz
        · rcases gate_split k with rfl | ⟨g, rfl⟩
          · exact False.elim (hdirty hk)
          · exact False.elim ((label_none_iff gate j).mp hl g hk)
        · exact hz
      refine ⟨?_, hm, hz⟩
      simpa only [hz.1, Finset.empty_inter] using hs
    | some g =>
      have he := (label_some_iff hinj j g).mp hl
      have hp := hports g
      rw [← he] at hp
      refine ⟨?_, hm, hp⟩
      have hd : port g false ∩ port g true = ∅ := by fin_cases g <;> decide
      rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · simpa only [ha,hb,hd] using hs
      · simpa only [ha,hb,Finset.inter_comm (port g true) (port g false),hd] using hs

end OnceActualLabels

namespace OnceActualLabels
open DAGBridge.DagTools OnceGeometry

lemma actual_other_sides {D : Dag} {gate : Fin 5 → ℕ}
    (hports : ∀ g : Fin 4,
      (supp 10 D (opA D (gate (firstFour g))) = port g false ∧
       supp 10 D (opB D (gate (firstFour g))) = port g true) ∨
      (supp 10 D (opA D (gate (firstFour g))) = port g true ∧
       supp 10 D (opB D (gate (firstFour g))) = port g false))
    (htypes : ∀ j, j < D.length → tag D j = true →
      (∃ k : Fin 5, j = gate k) ∨
      (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅)) :
    FiveGroup.DAGBridge.OtherAndSides D (gate 4) := by
  intro j hj hne ht
  change (supp 10 D (opA D j), supp 10 D (opB D j)) ∈
      FiveGroup.CausalBarrier.OtherSides ∨
    (supp 10 D (opB D j), supp 10 D (opA D j)) ∈
      FiveGroup.CausalBarrier.OtherSides
  rcases htypes j hj ht with ⟨k,hk⟩ | ⟨ha,hb⟩
  · rcases gate_split k with rfl | ⟨g,rfl⟩
    · exact False.elim (hne hk)
    · have hp := hports g
      rw [← hk] at hp
      have hm : (port g false, port g true) ∈ FiveGroup.CausalBarrier.OtherSides := by
        fin_cases g <;> decide
      rcases hp with ⟨ha,hb⟩ | ⟨ha,hb⟩
      · exact Or.inl (by simpa only [ha,hb] using hm)
      · exact Or.inr (by simpa only [ha,hb] using hm)
  · left
    rw [ha,hb]
    decide

end OnceActualLabels

namespace OnceActualLabels
open DAGBridge.DagTools OnceGeometry OnceSimulation OnceActualSchedule

noncomputable def wireLabel (gate : Fin 5 → ℕ) (w : ℕ) : Option (Fin 4) := label gate (w - 10)

lemma actual_group_unique {gate : Fin 5 → ℕ} (hinj : Function.Injective gate) :
    GroupUnique (wireLabel gate) (start (gate 4)) (remaining D (gate 4)) := by
  intro i hi j hj g hgi hgj
  have he := label_unique hinj hgi hgj
  change start (gate 4) + i - 10 = start (gate 4) + j - 10 at he
  unfold start at he
  omega

lemma actual_program_semantics {D : Dag} (hS : Strict 10 D) {gate : Fin 5 → ℕ}
    (hinj : Function.Injective gate)
    (hvalid : ∀ k, gate k < D.length ∧ tag D (gate k) = true)
    (hports : ∀ g : Fin 4,
      (supp 10 D (opA D (gate (firstFour g))) = port g false ∧
       supp 10 D (opB D (gate (firstFour g))) = port g true) ∨
      (supp 10 D (opA D (gate (firstFour g))) = port g true ∧
       supp 10 D (opB D (gate (firstFour g))) = port g false))
    (htypes : ∀ j, j < D.length → tag D j = true →
      (∃ k : Fin 5, j = gate k) ∨
      (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅)) :
    ProgramSemantics (supp 10 D) (wireMask D) (sourceA D) (sourceB D)
      (wireLabel gate) (fun w => tag D (w-10)) (start (gate 4)) (remaining D (gate 4)) := by
  intro t ht
  have hj : gate 4 + 1 + t < D.length := by unfold remaining at ht; omega
  have hn : gate 4 + 1 + t ≠ gate 4 := by omega
  have h := label_semantics hS hinj hvalid hports htypes (gate 4 + 1 + t) hj hn
  have he : start (gate 4) + t = 10 + (gate 4 + 1 + t) := by unfold start; omega
  simpa only [sourceA, sourceB, wireLabel, continuation_index, he, Nat.add_sub_cancel_left] using h

end OnceActualLabels

namespace OnceActualLabels
open DAGBridge.DagTools OnceGeometry OnceSimulation

lemma five_gate_petersen_exclusion {D : Dag} (hS : Strict 10 D)
    (hB : Bzero 10 D ≤ 1) {gate : Fin 5 → ℕ}
    (hinj : Function.Injective gate)
    (hvalid : ∀ k, gate k < D.length ∧ tag D (gate k) = true)
    (hports : ∀ g : Fin 4,
      (supp 10 D (opA D (gate (firstFour g))) = port g false ∧
       supp 10 D (opB D (gate (firstFour g))) = port g true) ∨
      (supp 10 D (opA D (gate (firstFour g))) = port g true ∧
       supp 10 D (opB D (gate (firstFour g))) = port g false))
    (hdirty : FiveGroup.DAGBridge.DirtySides D (gate 4))
    (htypes : ∀ j, j < D.length → tag D j = true →
      (∃ k : Fin 5, j = gate k) ∨
      (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅)) :
    ¬ ∀ x : Fin 10 → Bool, val D x (10 + D.length - 1) = edgeFn x := by
  exact actual_petersen_exclusion hS hB (hvalid 4).1 (hvalid 4).2 hdirty
    (actual_other_sides hports htypes) (actual_group_unique hinj)
    (actual_program_semantics hS hinj hvalid hports htypes)

end OnceActualLabels

namespace OnceActualLabels
open DAGBridge.DagTools OnceGeometry OnceSimulation

lemma five_gate_target_exclusion {D : Dag} (hS : Strict 10 D)
    (hB : Bzero 10 D ≤ 1) {gate : Fin 5 → ℕ}
    (hinj : Function.Injective gate)
    (hvalid : ∀ k, gate k < D.length ∧ tag D (gate k) = true)
    (hports : ∀ g : Fin 4,
      (supp 10 D (opA D (gate (firstFour g))) = port g false ∧
       supp 10 D (opB D (gate (firstFour g))) = port g true) ∨
      (supp 10 D (opA D (gate (firstFour g))) = port g true ∧
       supp 10 D (opB D (gate (firstFour g))) = port g false))
    (hdirty : FiveGroup.DAGBridge.DirtySides D (gate 4))
    (htypes : ∀ j, j < D.length → tag D j = true →
      (∃ k : Fin 5, j = gate k) ∨
      (supp 10 D (opA D j) = ∅ ∧ supp 10 D (opB D j) = ∅)) :
    ¬ (supp 10 D (10 + D.length - 1) = ∅ ∧ wireMask D (10 + D.length - 1) = 56) := by
  exact actual_target_exclusion hS hB (hvalid 4).1 (hvalid 4).2 hdirty
    (actual_other_sides hports htypes) (actual_group_unique hinj)
    (actual_program_semantics hS hinj hvalid hports htypes)

end OnceActualLabels

end PEqualNP.Outside.L_meta_2590
