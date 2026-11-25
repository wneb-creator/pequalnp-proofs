import PEqualNP.Defs

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

end PEqualNP.Outside.L_meta_2590
