import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1904

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def rootsStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def rootsTrace {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl rootsStep (List.ofFn x)

def rootsWire {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (i : ℕ) : Bool :=
  (rootsTrace gs x).getD i false

def rootsVal {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) : Bool :=
  g.op.eval (g.inputs.map (rootsWire gs x))

def rootsPoint {n : ℕ} (u : Fin n) (v : Fin n) : Bool := decide (v = u)

lemma roots_trace_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    rootsTrace (gs ++ [g]) x = rootsTrace gs x ++ [rootsVal gs g x] := by
  simp only [rootsTrace, List.foldl_append, List.foldl_cons, List.foldl_nil]
  rfl

lemma roots_trace_length {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (rootsTrace gs x).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [rootsTrace]
  | append_singleton gs g ih => simp [roots_trace_snoc, ih, Nat.add_assoc]

lemma roots_prefix_tail (w : List Bool) (rest : List Gate) :
    ∃ t, rest.foldl rootsStep w = w ++ t := by
  induction rest generalizing w with
  | nil => exact ⟨[], by simp⟩
  | cons g gs ih =>
    obtain ⟨t, ht⟩ := ih (rootsStep w g)
    exact ⟨_ :: t, by simpa [List.foldl_cons, rootsStep, List.append_assoc] using ht⟩

lemma roots_gate_value {n : ℕ} (pre rest : List Gate) (g : Gate) (x : Fin n → Bool) :
    rootsWire (pre ++ g :: rest) x (n + pre.length) = rootsVal pre g x := by
  have h : rootsTrace (pre ++ g :: rest) x =
      rest.foldl rootsStep (rootsTrace pre x ++ [rootsVal pre g x]) := by
    simp only [rootsTrace, List.foldl_append, List.foldl_cons]
    rfl
  obtain ⟨t, ht⟩ := roots_prefix_tail (rootsTrace pre x ++ [rootsVal pre g x]) rest
  dsimp only [rootsWire]
  rw [h, ht, List.append_assoc]
  have hl := roots_trace_length pre x
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right (by omega),
    ← hl, Nat.sub_self]
  rfl

lemma roots_wire_keep {n : ℕ} (pre : List Gate) (g : Gate) (x : Fin n → Bool)
    (k : ℕ) (hk : k < n + pre.length) :
    rootsWire (pre ++ [g]) x k = rootsWire pre x k := by
  simp only [rootsWire, roots_trace_snoc]
  exact List.getD_append _ _ _ _ (by rwa [roots_trace_length])

lemma roots_wire_access {n : ℕ} (pre : List Gate) (g : Gate) (x : Fin n → Bool)
    (k : ℕ) (hk : ¬ k < n + pre.length) :
    rootsWire (pre ++ [g]) x k =
      [rootsVal pre g x].getD (k - (n + pre.length)) false := by
  dsimp only [rootsWire]
  rw [roots_trace_snoc, List.getD_eq_getElem?_getD,
    List.getElem?_append_right (by rw [roots_trace_length]; omega), roots_trace_length]
  rfl

lemma roots_wire_mono {n : ℕ} (gs : List Gate)
    (ops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    {x y : Fin n → Bool} (h : ∀ u, x u = true → y u = true) (k : ℕ) :
    rootsWire gs x k = true → rootsWire gs y k = true := by
  induction gs using List.reverseRecOn generalizing k with
  | nil =>
    by_cases hk : k < n
    · simpa [rootsWire, rootsTrace, List.getD, hk] using h ⟨k, hk⟩
    · simp [rootsWire, rootsTrace, List.getD, hk]
  | append_singleton pre g ih =>
    have prior := ih (fun a ha => ops a (List.mem_append_left _ ha))
    by_cases hk : k < n + pre.length
    · simpa only [roots_wire_keep pre g x k hk, roots_wire_keep pre g y k hk] using prior k
    · rw [roots_wire_access pre g x k hk, roots_wire_access pre g y k hk]
      cases k - (n + pre.length) with
      | succ j => simp [List.getD]
      | zero =>
        change rootsVal pre g x = true → rootsVal pre g y = true
        rcases ops g (by simp) with ha | ho
        · simp only [rootsVal, ha, GateOp.eval, List.all_map, List.all_eq_true,
            Function.comp_apply, id_eq]
          exact fun p j hj => prior j (p j hj)
        · simp only [rootsVal, ho, GateOp.eval, List.any_map, List.any_eq_true,
            Function.comp_apply, id_eq]
          rintro ⟨j, hj, on⟩
          exact ⟨j, hj, prior j on⟩

lemma roots_wire_provenance {n : ℕ} (C : Circuit) (mono : Monotone2 C)
    (x : Fin n → Bool)
    (zero : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
      rootsWire C.gates x (n + j) = false)
    (pre : List Gate) :
    (∃ rest, C.gates = pre ++ rest) → ∀ k, rootsWire pre x k = true →
      ∃ u, x u = true ∧ rootsWire pre (rootsPoint u) k = true := by
  induction pre using List.reverseRecOn with
  | nil =>
    intro _ k hk
    by_cases h : k < n
    · refine ⟨⟨k, h⟩, ?_, ?_⟩
      · simpa [rootsWire, rootsTrace, List.getD, h] using hk
      · simp [rootsWire, rootsTrace, List.getD, h, rootsPoint]
    · simp [rootsWire, rootsTrace, List.getD, h] at hk
  | append_singleton pre g ih =>
    rintro ⟨rest, split⟩
    have total : C.gates = pre ++ g :: rest := by simpa [List.append_assoc] using split
    have prior := ih ⟨_, total⟩
    have member : g ∈ C.gates := by simp [total]
    intro k hk
    by_cases old : k < n + pre.length
    · rw [roots_wire_keep pre g x k old] at hk
      obtain ⟨u, hu, active⟩ := prior k hk
      exact ⟨u, hu, (roots_wire_keep pre g (rootsPoint u) k old).trans active⟩
    · rw [roots_wire_access pre g x k old] at hk
      cases e : k - (n + pre.length) with
      | succ j => simp [e, List.getD] at hk
      | zero =>
        rw [e] at hk
        change rootsVal pre g x = true at hk
        have shape : g.op = GateOp.and ∨ g.op = GateOp.or := by
          simpa using (mono g member).1
        rcases shape with ha | ho
        · have gate_at : C.gates[pre.length]? = some g := by simp [total]
          have hz := zero pre.length g gate_at ha
          rw [total, roots_gate_value] at hz
          exact False.elim (by rw [hz] at hk; contradiction)
        · have many : ∃ i ∈ g.inputs, rootsWire pre x i = true := by
            simpa [rootsVal, ho, GateOp.eval] using hk
          obtain ⟨i, hi, active⟩ := many
          obtain ⟨u, hu, force⟩ := prior i active
          refine ⟨u, hu, ?_⟩
          rw [roots_wire_access pre g (rootsPoint u) k old, e]
          change rootsVal pre g (rootsPoint u) = true
          simpa [rootsVal, ho, GateOp.eval] using
            (show ∃ j ∈ g.inputs, rootsWire pre (rootsPoint u) j = true from ⟨i, hi, force⟩)

lemma roots_wire_linear {n : ℕ} (C : Circuit) (mono : Monotone2 C)
    (x : Fin n → Bool)
    (zero : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
      rootsWire C.gates x (n + j) = false) (k : ℕ) :
    rootsWire C.gates x k = true ↔
      ∃ u, x u = true ∧ rootsWire C.gates (rootsPoint u) k = true := by
  constructor
  · exact roots_wire_provenance C mono x zero C.gates ⟨[], by simp⟩ k
  · rintro ⟨u, hu, active⟩
    apply roots_wire_mono C.gates (fun g hg => by simpa using (mono g hg).1) _ k active
    intro v hv
    have hvu : v = u := by simpa [rootsPoint] using hv
    simpa [hvu] using hu

def rootsHit {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool) : Prop :=
  ∃ u v, G.Adj u v ∧ x u = true ∧ x v = true

lemma roots_independent_linear {n : ℕ} (C : Circuit) (mono : Monotone2 C)
    (G : SimpleGraph (Fin n))
    (safe : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
      ∀ x : Fin n → Bool, rootsWire C.gates x (n + j) = true → rootsHit G x)
    (x : Fin n → Bool) (independent : ¬ rootsHit G x) (k : ℕ) :
    rootsWire C.gates x k = true ↔
      ∃ u, x u = true ∧ rootsWire C.gates (rootsPoint u) k = true := by
  apply roots_wire_linear C mono x _ k
  intro j g entry op
  apply Bool.eq_false_iff.mpr
  exact fun h => independent (safe j g entry op x h)

lemma roots_rectangle_lower {n : ℕ} (C : Circuit) (mono : Monotone2 C)
    (x : Fin n → Bool) (a b : ℕ)
    (rectangle : ∃ u v, x u = true ∧ x v = true ∧
      rootsWire C.gates (rootsPoint u) a = true ∧
      rootsWire C.gates (rootsPoint v) b = true) :
    rootsVal C.gates ⟨GateOp.and, [a, b]⟩ x = true := by
  obtain ⟨u, v, hu, hv, ha, hb⟩ := rectangle
  have monoC : ∀ g ∈ C.gates, g.op = GateOp.and ∨ g.op = GateOp.or := by
    intro g hg
    simpa using (mono g hg).1
  have wa : rootsWire C.gates x a = true := by
    apply roots_wire_mono C.gates monoC _ a ha
    intro w hw
    have hwu : w = u := by simpa [rootsPoint] using hw
    simpa [hwu] using hu
  have wb : rootsWire C.gates x b = true := by
    apply roots_wire_mono C.gates monoC _ b hb
    intro w hw
    have hwv : w = v := by simpa [rootsPoint] using hw
    simpa [hwv] using hv
  simp [rootsVal, GateOp.eval, wa, wb]

lemma roots_rectangle_exact {n : ℕ} (C : Circuit) (mono : Monotone2 C)
    (G : SimpleGraph (Fin n))
    (safe : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
      ∀ x : Fin n → Bool, rootsWire C.gates x (n + j) = true → rootsHit G x)
    (x : Fin n → Bool) (independent : ¬ rootsHit G x) (a b : ℕ) :
    rootsVal C.gates ⟨GateOp.and, [a, b]⟩ x = true ↔
      ∃ u v, x u = true ∧ x v = true ∧
        rootsWire C.gates (rootsPoint u) a = true ∧
        rootsWire C.gates (rootsPoint v) b = true := by
  constructor
  · intro h
    have hv : rootsWire C.gates x a = true ∧ rootsWire C.gates x b = true := by
      simpa [rootsVal, GateOp.eval] using h
    obtain ⟨u, hu, ha⟩ := (roots_independent_linear C mono G safe x independent a).mp hv.1
    obtain ⟨v, hv, hb⟩ := (roots_independent_linear C mono G safe x independent b).mp hv.2
    exact ⟨u, v, hu, hv, ha, hb⟩
  · exact roots_rectangle_lower C mono x a b

lemma roots_bad_rectangle_decomposition {n : ℕ} (C : Circuit) (mono : Monotone2 C)
    (G : SimpleGraph (Fin n))
    (safe : ∀ j g, C.gates[j]? = some g → g.op = GateOp.and →
      ∀ x : Fin n → Bool, rootsWire C.gates x (n + j) = true → rootsHit G x)
    (x : Fin n → Bool) (a b : ℕ) :
    rootsVal C.gates ⟨GateOp.and, [a, b]⟩ x = true ↔
      (rootsHit G x ∧ rootsVal C.gates ⟨GateOp.and, [a, b]⟩ x = true) ∨
      ∃ u v, ¬ G.Adj u v ∧ x u = true ∧ x v = true ∧
        rootsWire C.gates (rootsPoint u) a = true ∧
        rootsWire C.gates (rootsPoint v) b = true := by
  classical
  constructor
  · intro h
    by_cases hx : rootsHit G x
    · exact Or.inl ⟨hx, h⟩
    · obtain ⟨u, v, hu, hv, ha, hb⟩ := (roots_rectangle_exact C mono G safe x hx a b).mp h
      exact Or.inr ⟨u, v, fun adj => hx ⟨u, v, adj, hu, hv⟩, hu, hv, ha, hb⟩
  · rintro (⟨_, h⟩ | ⟨u, v, _, hu, hv, ha, hb⟩)
    · exact h
    · exact roots_rectangle_lower C mono x a b ⟨u, v, hu, hv, ha, hb⟩

def InputLE {n : ℕ} (x y : Fin n → Bool) : Prop :=
  ∀ a, x a = true → y a = true

def Increasing {n : ℕ} (f : (Fin n → Bool) → Bool) : Prop :=
  ∀ x y, InputLE x y → f x = true → f y = true

def Pair {n : ℕ} (u v : Fin n) : Fin n → Bool :=
  fun a => decide (a = u ∨ a = v)

def AddPair {n : ℕ} (x : Fin n → Bool) (u v : Fin n) : Fin n → Bool :=
  fun a => x a || Pair u v a

lemma hit_pair_iff {n : ℕ} (G : SimpleGraph (Fin n)) (u v : Fin n) :
    rootsHit G (Pair u v) ↔ G.Adj u v := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [Pair, decide_eq_true_eq] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (G.irrefl hab).elim
    · exact hab
    · exact hab.symm
    · exact (G.irrefl hab).elim
  · intro huv
    exact ⟨u, v, huv, by simp [Pair], by simp [Pair]⟩

lemma hit_addPair_iff {n : ℕ} (G : SimpleGraph (Fin n)) (x : Fin n → Bool)
    (u v : Fin n) (hnon : ¬ G.Adj u v) :
    rootsHit G (AddPair x u v) ↔
      rootsHit G x ∨ ∃ w, x w = true ∧ (G.Adj u w ∨ G.Adj v w) := by
  constructor
  · rintro ⟨a, b, hab, ha, hb⟩
    simp only [AddPair, Bool.or_eq_true, Pair, decide_eq_true_eq] at ha hb
    rcases ha with ha | (rfl | rfl)
    · rcases hb with hb | (rfl | rfl)
      · exact Or.inl ⟨a, b, hab, ha, hb⟩
      · exact Or.inr ⟨a, ha, Or.inl hab.symm⟩
      · exact Or.inr ⟨a, ha, Or.inr hab.symm⟩
    · rcases hb with hb | (rfl | rfl)
      · exact Or.inr ⟨b, hb, Or.inl hab⟩
      · exact (G.irrefl hab).elim
      · exact (hnon hab).elim
    · rcases hb with hb | (rfl | rfl)
      · exact Or.inr ⟨b, hb, Or.inr hab⟩
      · exact (hnon hab.symm).elim
      · exact (G.irrefl hab).elim
  · rintro (⟨a, b, hab, ha, hb⟩ | ⟨w, hw, huv | hvw⟩)
    · exact ⟨a, b, hab, by simp [AddPair, ha], by simp [AddPair, hb]⟩
    · exact ⟨u, w, huv, by simp [AddPair, Pair], by simp [AddPair, hw]⟩
    · exact ⟨v, w, hvw, by simp [AddPair, Pair], by simp [AddPair, hw]⟩

lemma blocker_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (f h : (Fin n → Bool) → Bool) (hf : Increasing f) (hh : Increasing h)
    (safe : ∀ x, f x = true → h x = true → rootsHit G x)
    (u v : Fin n) (hnon : ¬ G.Adj u v) (hpair : f (Pair u v) = true) :
    ∀ x, h x = true → rootsHit G x ∨ ∃ w, x w = true ∧ (G.Adj u w ∨ G.Adj v w) := by
  intro x hx
  apply (hit_addPair_iff G x u v hnon).mp
  apply safe
  · apply hf (Pair u v) (AddPair x u v) _ hpair
    intro a ha
    simp [AddPair, ha]
  · apply hh x (AddPair x u v) _ hx
    intro a ha
    simp [AddPair, ha]

lemma independent_blocker_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (f h : (Fin n → Bool) → Bool) (hf : Increasing f) (hh : Increasing h)
    (safe : ∀ x, f x = true → h x = true → rootsHit G x)
    (u v : Fin n) (hnon : ¬ G.Adj u v) (hpair : f (Pair u v) = true)
    (x : Fin n → Bool) (hind : ¬ rootsHit G x) (hx : h x = true) :
    ∃ w, x w = true ∧ (G.Adj u w ∨ G.Adj v w) :=
  (blocker_bound G f h hf hh safe u v hnon hpair x hx).resolve_left hind

lemma unit_blocker_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (f h : (Fin n → Bool) → Bool) (hf : Increasing f) (hh : Increasing h)
    (safe : ∀ x, f x = true → h x = true → rootsHit G x)
    (u v : Fin n) (hnon : ¬ G.Adj u v) (hpair : f (Pair u v) = true)
    (w : Fin n) (hw : h (Pair w w) = true) : G.Adj u w ∨ G.Adj v w := by
  have hind : ¬ rootsHit G (Pair w w) := by
    rw [hit_pair_iff]
    exact G.irrefl
  obtain ⟨a, ha, hadj⟩ :=
    independent_blocker_bound G f h hf hh safe u v hnon hpair (Pair w w) hind hw
  have haw : a = w := by simpa [Pair] using ha
  simpa only [haw] using hadj

lemma two_pairs_cleaner {n : ℕ} (G : SimpleGraph (Fin n))
    (tri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    {a b c d w : Fin n} (hab : G.Adj a b) (hcd : G.Adj c d)
    (hfirst : G.Adj a w ∨ G.Adj d w) (hsecond : G.Adj c w ∨ G.Adj b w) :
    (G.Adj a w ∧ G.Adj c w) ∨ (G.Adj b w ∧ G.Adj d w) := by
  rcases hfirst with haw | hdw <;> rcases hsecond with hcw | hbw
  · exact Or.inl ⟨haw, hcw⟩
  · exact (tri a b w hab hbw haw.symm).elim
  · exact (tri c d w hcd hdw hcw.symm).elim
  · exact Or.inr ⟨hbw, hdw⟩

lemma codegree_le_one {n : ℕ} (G : SimpleGraph (Fin n))
    (square : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d) (a c : Fin n) (hac : a ≠ c) :
    Set.Subsingleton {w | G.Adj a w ∧ G.Adj c w} := by
  intro w hw z hz
  exact (square a w c z hw.1 hw.2.symm hz.2 hz.1.symm).resolve_left hac

lemma two_pairs_blocker_profile {n : ℕ} (G : SimpleGraph (Fin n))
    (tri : ∀ a b c, G.Adj a b → G.Adj b c → ¬ G.Adj c a)
    (square : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (f h : (Fin n → Bool) → Bool) (hf : Increasing f) (hh : Increasing h)
    (safe : ∀ x, f x = true → h x = true → rootsHit G x)
    (a b c d : Fin n) (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (hbd : b ≠ d) (had : ¬ G.Adj a d) (hcb : ¬ G.Adj c b)
    (hpair1 : f (Pair a d) = true) (hpair2 : f (Pair c b) = true) :
    ∀ w x y, h (Pair w w) = true → h (Pair x x) = true → h (Pair y y) = true →
      w = x ∨ w = y ∨ x = y := by
  have classify (w : Fin n) (hw : h (Pair w w) = true) :
      (G.Adj a w ∧ G.Adj c w) ∨ (G.Adj b w ∧ G.Adj d w) :=
    two_pairs_cleaner G tri hab hcd
      (unit_blocker_bound G f h hf hh safe a d had hpair1 w hw)
      (unit_blocker_bound G f h hf hh safe c b hcb hpair2 w hw)
  have hleft := codegree_le_one G square a c hac
  have hright := codegree_le_one G square b d hbd
  intro w x y hw hx hy
  rcases classify w hw with hw | hw <;>
    rcases classify x hx with hx | hx <;>
    rcases classify y hy with hy | hy
  · exact Or.inl (hleft hw hx)
  · exact Or.inl (hleft hw hx)
  · exact Or.inr (Or.inl (hleft hw hy))
  · exact Or.inr (Or.inr (hright hx hy))
  · exact Or.inr (Or.inr (hleft hx hy))
  · exact Or.inr (Or.inl (hright hw hy))
  · exact Or.inl (hright hw hx)
  · exact Or.inl (hright hw hx)

lemma blocker_endpoints_false {n : ℕ} (G : SimpleGraph (Fin n))
    (f h : (Fin n → Bool) → Bool) (hf : Increasing f) (hh : Increasing h)
    (safe : ∀ x, f x = true → h x = true → rootsHit G x)
    (u v : Fin n) (hnon : ¬ G.Adj u v) (hpair : f (Pair u v) = true) :
    h (Pair u u) = false ∧ h (Pair v v) = false := by
  constructor
  · apply Bool.eq_false_iff.mpr
    intro hu
    rcases unit_blocker_bound G f h hf hh safe u v hnon hpair u hu with h | h
    · exact G.irrefl h
    · exact hnon h.symm
  · apply Bool.eq_false_iff.mpr
    intro hv
    rcases unit_blocker_bound G f h hf hh safe u v hnon hpair v hv with h | h
    · exact hnon h
    · exact G.irrefl h

lemma roots_wire_increasing {n : ℕ} (C : Circuit) (mono : Monotone2 C) (k : ℕ) :
    Increasing (fun x : Fin n → Bool => rootsWire C.gates x k) := by
  intro x y h
  exact roots_wire_mono C.gates (fun g hg => by simpa using (mono g hg).1) h k

lemma roots_and_increasing {n : ℕ} (C : Circuit) (mono : Monotone2 C) (a b : ℕ) :
    Increasing (fun x : Fin n → Bool => rootsVal C.gates ⟨GateOp.and, [a, b]⟩ x) := by
  intro x y hxy hx
  have h : rootsWire C.gates x a = true ∧ rootsWire C.gates x b = true := by
    simpa [rootsVal, GateOp.eval] using hx
  have ha := roots_wire_increasing C mono a x y hxy h.1
  have hb := roots_wire_increasing C mono b x y hxy h.2
  simp [rootsVal, GateOp.eval, ha, hb]

lemma roots_and_blocker_bound {n : ℕ} (C : Circuit) (mono : Monotone2 C)
    (G : SimpleGraph (Fin n)) (a b : ℕ) (h : (Fin n → Bool) → Bool)
    (hh : Increasing h)
    (safe : ∀ x, rootsVal C.gates ⟨GateOp.and, [a, b]⟩ x = true →
      h x = true → rootsHit G x)
    (u v : Fin n) (hnon : ¬ G.Adj u v)
    (hu : rootsWire C.gates (rootsPoint u) a = true)
    (hv : rootsWire C.gates (rootsPoint v) b = true) :
    ∀ x, h x = true → rootsHit G x ∨
      ∃ w, x w = true ∧ (G.Adj u w ∨ G.Adj v w) := by
  apply blocker_bound G _ h (roots_and_increasing C mono a b) hh safe u v hnon
  apply roots_rectangle_lower C mono (Pair u v) a b
  exact ⟨u, v, by simp [Pair], by simp [Pair], hu, hv⟩

lemma roots_trace_patch_eq {n : ℕ} (pre post : List Gate) (g d : Gate)
    (x : Fin n → Bool) (h : rootsVal pre g x = rootsVal pre d x) :
    rootsTrace (pre ++ g :: post) x = rootsTrace (pre ++ d :: post) x := by
  simp only [rootsTrace, List.foldl_append, List.foldl_cons]
  change post.foldl rootsStep (rootsTrace pre x ++ [rootsVal pre g x]) =
    post.foldl rootsStep (rootsTrace pre x ++ [rootsVal pre d x])
  rw [h]

lemma roots_mono_prefix (pre post : List Gate) (g : Gate) (out : ℕ)
    (mono : Monotone2 ⟨pre ++ g :: post, out⟩) : Monotone2 ⟨pre, out⟩ := by
  intro d hd
  exact mono d (List.mem_append_left _ hd)

lemma roots_true_context_mono (pre post : List Gate) (g : Gate) (out : ℕ)
    (mono : Monotone2 ⟨pre ++ g :: post, out⟩) :
    Monotone2 ⟨pre ++ ⟨GateOp.and, []⟩ :: post, out⟩ := by
  intro d hd
  simp only [List.mem_append, List.mem_cons] at hd
  rcases hd with hd | rfl | hd
  · exact mono d (List.mem_append_left _ hd)
  · simp
  · exact mono d (List.mem_append_right _ (List.mem_cons_of_mem _ hd))

lemma roots_val_increasing {n : ℕ} (C : Circuit) (mono : Monotone2 C) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or) :
    Increasing (fun x : Fin n → Bool => rootsVal C.gates g x) := by
  intro x y hxy hx
  have hm (i : ℕ) := roots_wire_increasing C mono i x y hxy
  rcases hop with ha | ho
  · simp only [rootsVal, ha, GateOp.eval, List.all_map, List.all_eq_true,
      Function.comp_apply, id_eq] at hx ⊢
    exact fun i hi => hm i (hx i hi)
  · simp only [rootsVal, ho, GateOp.eval, List.any_map, List.any_eq_true,
      Function.comp_apply, id_eq] at hx ⊢
    obtain ⟨i, hi, hix⟩ := hx
    exact ⟨i, hi, hm i hix⟩

lemma roots_true_context_safe {n : ℕ} (G : SimpleGraph (Fin n))
    (pre post : List Gate) (g : Gate) (out : ℕ)
    (sound : ∀ x : Fin n → Bool,
      rootsWire (pre ++ g :: post) x out = true → rootsHit G x) :
    ∀ x : Fin n → Bool, rootsVal pre g x = true →
      rootsWire (pre ++ ⟨GateOp.and, []⟩ :: post) x out = true → rootsHit G x := by
  intro x hx hc
  apply sound x
  have heq : rootsVal pre g x = rootsVal pre ⟨GateOp.and, []⟩ x := by
    simpa [rootsVal, GateOp.eval] using hx
  have ht := roots_trace_patch_eq pre post g ⟨GateOp.and, []⟩ x heq
  simpa only [rootsWire, ht] using hc

lemma roots_context_blocker_bound {n : ℕ} (G : SimpleGraph (Fin n))
    (pre post : List Gate) (g : Gate) (out : ℕ)
    (mono : Monotone2 ⟨pre ++ g :: post, out⟩)
    (sound : ∀ x : Fin n → Bool,
      rootsWire (pre ++ g :: post) x out = true → rootsHit G x)
    (u v : Fin n) (hnon : ¬ G.Adj u v) (hpair : rootsVal pre g (Pair u v) = true) :
    ∀ x : Fin n → Bool,
      rootsWire (pre ++ ⟨GateOp.and, []⟩ :: post) x out = true →
      rootsHit G x ∨ ∃ w, x w = true ∧ (G.Adj u w ∨ G.Adj v w) := by
  have hp := roots_mono_prefix pre post g out mono
  have ht := roots_true_context_mono pre post g out mono
  have hop : g.op = GateOp.and ∨ g.op = GateOp.or := by
    simpa using (mono g (by simp)).1
  exact blocker_bound G _ _
    (roots_val_increasing ⟨pre, out⟩ hp g hop)
    (roots_wire_increasing ⟨pre ++ ⟨GateOp.and, []⟩ :: post, out⟩ ht out)
    (roots_true_context_safe G pre post g out sound) u v hnon hpair

lemma rectangle_filter_dichotomy {n : ℕ} (G : SimpleGraph (Fin n))
    (square : ∀ a b c d, G.Adj a b → G.Adj b c → G.Adj c d → G.Adj d a →
      a = c ∨ b = d)
    (f h : (Fin n → Bool) → Bool) (hf : Increasing f) (hh : Increasing h)
    (safe : ∀ x, f x = true → h x = true → rootsHit G x)
    (a b c d : Fin n) (hab : G.Adj a b) (hcd : G.Adj c d)
    (hac : a ≠ c) (hbd : b ≠ d)
    (had : f (Pair a d) = true) (hcb : f (Pair c b) = true)
    (habh : h (Pair a b) = true) (hcdh : h (Pair c d) = true) :
    (h (Pair a b) = true ∧ h (Pair a a) = false ∧ h (Pair b b) = false) ∨
    (h (Pair c d) = true ∧ h (Pair c c) = false ∧ h (Pair d d) = false) ∨
    ∃ u v, G.Adj u v ∧ h (Pair u u) = true ∧ h (Pair v v) = true := by
  have cross_missing : ¬ G.Adj a d ∨ ¬ G.Adj c b := by
    by_cases hadj : G.Adj a d
    · right
      intro hcbj
      exact (square a b c d hab hcbj.symm hcd hadj.symm).elim hac hbd
    · exact Or.inl hadj
  rcases cross_missing with hnon | hnon
  · obtain ⟨ha, hd⟩ := blocker_endpoints_false G f h hf hh safe a d hnon had
    by_cases hb : h (Pair b b) = true
    · by_cases hc : h (Pair c c) = true
      · right
        right
        refine ⟨b, c, ?_, hb, hc⟩
        apply SimpleGraph.Adj.symm
        apply (hit_pair_iff G c b).mp
        apply safe (Pair c b) hcb
        apply hh (Pair b b) (Pair c b) _ hb
        intro w hw
        have hwb : w = b := by simpa [Pair] using hw
        simp [Pair, hwb]
      · exact Or.inr (Or.inl ⟨hcdh, Bool.eq_false_iff.mpr hc, hd⟩)
    · exact Or.inl ⟨habh, ha, Bool.eq_false_iff.mpr hb⟩
  · obtain ⟨hc, hb⟩ := blocker_endpoints_false G f h hf hh safe c b hnon hcb
    by_cases ha : h (Pair a a) = true
    · by_cases hd : h (Pair d d) = true
      · right
        right
        refine ⟨a, d, ?_, ha, hd⟩
        apply (hit_pair_iff G a d).mp
        apply safe (Pair a d) had
        apply hh (Pair a a) (Pair a d) _ ha
        intro w hw
        have hwa : w = a := by simpa [Pair] using hw
        simp [Pair, hwa]
      · exact Or.inr (Or.inl ⟨hcdh, hc, Bool.eq_false_iff.mpr hd⟩)
    · exact Or.inl ⟨habh, Bool.eq_false_iff.mpr ha, hb⟩

def PairLinear {n : ℕ} (gs : List Gate) (u v : Fin n) : Prop :=
  ∀ k, rootsWire gs (Pair u v) k = true →
    rootsWire gs (rootsPoint u) k = true ∨ rootsWire gs (rootsPoint v) k = true

def PairMerge {n : ℕ} (pre : List Gate) (g : Gate) (u v : Fin n) : Prop :=
  rootsVal pre g (Pair u v) = true ∧
    rootsVal pre g (rootsPoint u) = false ∧ rootsVal pre g (rootsPoint v) = false

def OppositeInputs {n : ℕ} (pre : List Gate) (a b : ℕ) (u v : Fin n) : Prop :=
  (rootsWire pre (rootsPoint u) a = true ∧ rootsWire pre (rootsPoint v) a = false ∧
    rootsWire pre (rootsPoint u) b = false ∧ rootsWire pre (rootsPoint v) b = true) ∨
  (rootsWire pre (rootsPoint v) a = true ∧ rootsWire pre (rootsPoint u) a = false ∧
    rootsWire pre (rootsPoint v) b = false ∧ rootsWire pre (rootsPoint u) b = true)

lemma pair_merge_binary {n : ℕ} (pre : List Gate) (g : Gate) (u v : Fin n)
    (prior : PairLinear pre u v)
    (ops : g.op = GateOp.and ∨ g.op = GateOp.or) (arity : g.inputs.length ≤ 2)
    (merge : PairMerge pre g u v) :
    g.op = GateOp.and ∧ ∃ a b, g.inputs = [a, b] ∧ OppositeInputs pre a b u v := by
  rcases merge with ⟨hp, hu, hv⟩
  rcases ops with ha | ho
  · refine ⟨ha, ?_⟩
    cases ei : g.inputs with
    | nil => simp [rootsVal, ha, GateOp.eval, ei] at hu
    | cons a tail =>
      cases et : tail with
      | nil =>
        have hp' : rootsWire pre (Pair u v) a = true := by
          simpa [rootsVal, ha, GateOp.eval, ei, et] using hp
        rcases prior a hp' with hau | hav
        · simp [rootsVal, ha, GateOp.eval, ei, et, hau] at hu
        · simp [rootsVal, ha, GateOp.eval, ei, et, hav] at hv
      | cons b rest =>
        have hr : rest = [] := by simpa [ei, et] using arity
        subst rest
        refine ⟨a, b, rfl, ?_⟩
        have hp' : rootsWire pre (Pair u v) a = true ∧ rootsWire pre (Pair u v) b = true := by
          simpa [rootsVal, ha, GateOp.eval, ei, et] using hp
        have hA := prior a hp'.1
        have hB := prior b hp'.2
        simp only [rootsVal, ha, GateOp.eval, ei, et, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, id_eq, Bool.and_true] at hu hv
        unfold OppositeInputs
        cases au : rootsWire pre (rootsPoint u) a <;>
          cases av : rootsWire pre (rootsPoint v) a <;>
          cases bu : rootsWire pre (rootsPoint u) b <;>
          cases bv : rootsWire pre (rootsPoint v) b <;> simp_all
  · have someInput : ∃ i ∈ g.inputs, rootsWire pre (Pair u v) i = true := by
      simpa [rootsVal, ho, GateOp.eval] using hp
    obtain ⟨i, hi, hpi⟩ := someInput
    rcases prior i hpi with hui | hvi
    · have hgu : rootsVal pre g (rootsPoint u) = true := by
        simpa [rootsVal, ho, GateOp.eval] using
          (show ∃ k ∈ g.inputs, rootsWire pre (rootsPoint u) k = true from ⟨i, hi, hui⟩)
      rw [hu] at hgu
      contradiction
    · have hgv : rootsVal pre g (rootsPoint v) = true := by
        simpa [rootsVal, ho, GateOp.eval] using
          (show ∃ k ∈ g.inputs, rootsWire pre (rootsPoint v) k = true from ⟨i, hi, hvi⟩)
      rw [hv] at hgv
      contradiction

lemma pair_scan {n : ℕ} (gs : List Gate) (u v : Fin n)
    (mono : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    PairLinear gs u v ∨
      ∃ pre g rest, gs = pre ++ g :: rest ∧ PairLinear pre u v ∧
        PairMerge pre g u v ∧ g.op = GateOp.and ∧
        ∃ a b, g.inputs = [a, b] ∧ OppositeInputs pre a b u v := by
  classical
  induction gs using List.reverseRecOn with
  | nil =>
    left
    intro k hp
    by_cases hk : k < n
    · have hc : (⟨k, hk⟩ : Fin n) = u ∨ (⟨k, hk⟩ : Fin n) = v := by
        simpa [rootsWire, rootsTrace, List.getD, hk, Pair] using hp
      rcases hc with hku | hkv
      · left
        simp [rootsWire, rootsTrace, List.getD, hk, rootsPoint, hku]
      · right
        simp [rootsWire, rootsTrace, List.getD, hk, rootsPoint, hkv]
    · simp [rootsWire, rootsTrace, List.getD, hk] at hp
  | append_singleton pre g ih =>
    have monoPre := fun a ha => mono a (List.mem_append_left _ ha)
    rcases ih monoPre with linear | ⟨pre', g', rest, split, prior, merge, op, a, b, inp, opp⟩
    · by_cases hmerge : PairMerge pre g u v
      · obtain ⟨op, a, b, inp, opp⟩ := pair_merge_binary pre g u v linear
          (mono g (by simp)).1 (mono g (by simp)).2 hmerge
        exact Or.inr ⟨pre, g, [], rfl, linear, hmerge, op, a, b, inp, opp⟩
      · left
        intro k hp
        by_cases hk : k < n + pre.length
        · rw [roots_wire_keep pre g (Pair u v) k hk] at hp
          rcases linear k hp with hu | hv
          · exact Or.inl ((roots_wire_keep pre g (rootsPoint u) k hk).trans hu)
          · exact Or.inr ((roots_wire_keep pre g (rootsPoint v) k hk).trans hv)
        · rw [roots_wire_access pre g (Pair u v) k hk] at hp
          cases e : k - (n + pre.length) with
          | succ j => simp [e, List.getD] at hp
          | zero =>
            rw [e] at hp
            change rootsVal pre g (Pair u v) = true at hp
            have someSingle : rootsVal pre g (rootsPoint u) = true ∨
                rootsVal pre g (rootsPoint v) = true := by
              cases hu : rootsVal pre g (rootsPoint u) <;>
                cases hv : rootsVal pre g (rootsPoint v) <;> simp_all [PairMerge]
            rcases someSingle with hu | hv
            · left
              rw [roots_wire_access pre g (rootsPoint u) k hk, e]
              exact hu
            · right
              rw [roots_wire_access pre g (rootsPoint v) k hk, e]
              exact hv
    · right
      refine ⟨pre', g', rest ++ [g], ?_, prior, merge, op, a, b, inp, opp⟩
      simp [split, List.append_assoc]

lemma exists_first_pair_merge {n : ℕ} (C : Circuit) (mono : Monotone2 C) (u v : Fin n)
    (positive : C.eval (List.ofFn (Pair u v)) = true)
    (singleU : C.eval (List.ofFn (rootsPoint u)) = false)
    (singleV : C.eval (List.ofFn (rootsPoint v)) = false) :
    ∃ pre g rest, C.gates = pre ++ g :: rest ∧ PairLinear pre u v ∧
      PairMerge pre g u v ∧ g.op = GateOp.and ∧
      ∃ a b, g.inputs = [a, b] ∧ OppositeInputs pre a b u v := by
  have ops : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      g.inputs.length ≤ 2 := by
    intro g hg
    simpa using mono g hg
  rcases pair_scan C.gates u v ops with linear | h
  · have hp : rootsWire C.gates (Pair u v) C.output = true := positive
    rcases linear C.output hp with hu | hv
    · change C.eval (List.ofFn (rootsPoint u)) = true at hu
      rw [singleU] at hu
      contradiction
    · change C.eval (List.ofFn (rootsPoint v)) = true at hv
      rw [singleV] at hv
      contradiction
  · exact h

lemma exists_first_pair_merge_after {n : ℕ} (C : Circuit) (mono : Monotone2 C)
    (u v : Fin n) (p : ℕ)
    (positive : C.eval (List.ofFn (Pair u v)) = true)
    (singleU : C.eval (List.ofFn (rootsPoint u)) = false)
    (singleV : C.eval (List.ofFn (rootsPoint v)) = false)
    (before : ∀ j < p, ∀ g, C.gates[j]? = some g →
      ¬ (rootsWire C.gates (Pair u v) (n + j) = true ∧
        rootsWire C.gates (rootsPoint u) (n + j) = false ∧
        rootsWire C.gates (rootsPoint v) (n + j) = false)) :
    ∃ pre g rest, C.gates = pre ++ g :: rest ∧ p ≤ pre.length ∧ PairLinear pre u v ∧
      PairMerge pre g u v ∧ g.op = GateOp.and ∧
      ∃ a b, g.inputs = [a, b] ∧ OppositeInputs pre a b u v := by
  obtain ⟨pre, g, rest, split, prior, merge, op, a, b, inp, opp⟩ :=
    exists_first_pair_merge C mono u v positive singleU singleV
  refine ⟨pre, g, rest, split, ?_, prior, merge, op, a, b, inp, opp⟩
  by_contra tooEarly
  have entry : C.gates[pre.length]? = some g := by simp [split]
  apply before pre.length (by omega) g entry
  simpa only [split, roots_gate_value, PairMerge] using merge

lemma opposite_inputs_distinct {n : ℕ} (pre : List Gate) (a b : ℕ) (u v : Fin n)
    (opposite : OppositeInputs pre a b u v) : a ≠ b := by
  intro h
  subst b
  rcases opposite with ⟨ha, _, hb, _⟩ | ⟨ha, _, hb, _⟩ <;> rw [ha] at hb <;> contradiction

lemma true_wire_in_bounds {n : ℕ} (pre : List Gate) (x : Fin n → Bool) (k : ℕ)
    (active : rootsWire pre x k = true) : k < n + pre.length := by
  by_contra outside
  have hn : (rootsTrace pre x)[k]? = none :=
    List.getElem?_eq_none_iff.mpr (by rw [roots_trace_length]; omega)
  simp [rootsWire, List.getD, hn] at active

lemma opposite_inputs_in_bounds {n : ℕ} (pre : List Gate) (a b : ℕ) (u v : Fin n)
    (opposite : OppositeInputs pre a b u v) : a < n + pre.length ∧ b < n + pre.length := by
  rcases opposite with ⟨ha, _, _, hb⟩ | ⟨ha, _, _, hb⟩
  · exact ⟨true_wire_in_bounds pre (rootsPoint u) a ha,
      true_wire_in_bounds pre (rootsPoint v) b hb⟩
  · exact ⟨true_wire_in_bounds pre (rootsPoint v) a ha,
      true_wire_in_bounds pre (rootsPoint u) b hb⟩

lemma live_merge_binary_inputs {n : ℕ} (pre : List Gate) (g : Gate) (u v : Fin n)
    (prior : ∀ i ∈ g.inputs, rootsWire pre (Pair u v) i = true →
      rootsWire pre (rootsPoint u) i = true ∨ rootsWire pre (rootsPoint v) i = true)
    (ops : g.op = GateOp.and ∨ g.op = GateOp.or) (arity : g.inputs.length ≤ 2)
    (merge : PairMerge pre g u v) :
    g.op = GateOp.and ∧ ∃ a b, g.inputs = [a, b] ∧ OppositeInputs pre a b u v := by
  rcases merge with ⟨hp, hu, hv⟩
  rcases ops with ha | ho
  · refine ⟨ha, ?_⟩
    cases ei : g.inputs with
    | nil => simp [rootsVal, ha, GateOp.eval, ei] at hu
    | cons a tail =>
      cases et : tail with
      | nil =>
        have hp' : rootsWire pre (Pair u v) a = true := by
          simpa [rootsVal, ha, GateOp.eval, ei, et] using hp
        rcases prior a (by simp [ei, et]) hp' with hau | hav
        · simp [rootsVal, ha, GateOp.eval, ei, et, hau] at hu
        · simp [rootsVal, ha, GateOp.eval, ei, et, hav] at hv
      | cons b rest =>
        have hr : rest = [] := by simpa [ei, et] using arity
        subst rest
        refine ⟨a, b, rfl, ?_⟩
        have hp' : rootsWire pre (Pair u v) a = true ∧ rootsWire pre (Pair u v) b = true := by
          simpa [rootsVal, ha, GateOp.eval, ei, et] using hp
        have hA := prior a (by simp [ei, et]) hp'.1
        have hB := prior b (by simp [ei, et]) hp'.2
        simp only [rootsVal, ha, GateOp.eval, ei, et, List.map_cons, List.map_nil,
          List.all_cons, List.all_nil, id_eq, Bool.and_true] at hu hv
        unfold OppositeInputs
        cases au : rootsWire pre (rootsPoint u) a <;>
          cases av : rootsWire pre (rootsPoint v) a <;>
          cases bu : rootsWire pre (rootsPoint u) b <;>
          cases bv : rootsWire pre (rootsPoint v) b <;> simp_all
  · have someInput : ∃ i ∈ g.inputs, rootsWire pre (Pair u v) i = true := by
      simpa [rootsVal, ho, GateOp.eval] using hp
    obtain ⟨i, hi, hpi⟩ := someInput
    rcases prior i hi hpi with hui | hvi
    · have hgu : rootsVal pre g (rootsPoint u) = true := by
        simpa [rootsVal, ho, GateOp.eval] using
          (show ∃ k ∈ g.inputs, rootsWire pre (rootsPoint u) k = true from ⟨i, hi, hui⟩)
      rw [hu] at hgu
      contradiction
    · have hgv : rootsVal pre g (rootsPoint v) = true := by
        simpa [rootsVal, ho, GateOp.eval] using
          (show ∃ k ∈ g.inputs, rootsWire pre (rootsPoint v) k = true from ⟨i, hi, hvi⟩)
      rw [hv] at hgv
      contradiction


lemma live_gate_predecessor_or_merge {n : ℕ} (pre : List Gate) (g : Gate) (u v : Fin n)
    (ops : g.op = GateOp.and ∨ g.op = GateOp.or) (arity : g.inputs.length ≤ 2)
    (merge : PairMerge pre g u v) :
    (∃ i ∈ g.inputs, rootsWire pre (Pair u v) i = true ∧
      rootsWire pre (rootsPoint u) i = false ∧ rootsWire pre (rootsPoint v) i = false) ∨
    (g.op = GateOp.and ∧ ∃ a b, g.inputs = [a, b] ∧ OppositeInputs pre a b u v) := by
  classical
  by_cases h : ∃ i ∈ g.inputs, rootsWire pre (Pair u v) i = true ∧
      rootsWire pre (rootsPoint u) i = false ∧ rootsWire pre (rootsPoint v) i = false
  · exact Or.inl h
  · right
    apply live_merge_binary_inputs pre g u v _ ops arity merge
    intro i hi hp
    cases hu : rootsWire pre (rootsPoint u) i <;>
      cases hv : rootsWire pre (rootsPoint v) i <;> simp_all

lemma live_append_wire {n : ℕ} (pre rest : List Gate) (x : Fin n → Bool) (k : ℕ)
    (hk : k < n + pre.length) : rootsWire (pre ++ rest) x k = rootsWire pre x k := by
  obtain ⟨t, ht⟩ := roots_prefix_tail (rootsTrace pre x) rest
  have he : rootsTrace (pre ++ rest) x = rootsTrace pre x ++ t := by
    simpa only [rootsTrace, List.foldl_append] using ht
  simp only [rootsWire, he]
  exact List.getD_append _ _ _ _ (by rwa [roots_trace_length])

def LivePairWire {n : ℕ} (C : Circuit) (u v : Fin n) (k : ℕ) : Prop :=
  rootsWire C.gates (Pair u v) k = true ∧
    rootsWire C.gates (rootsPoint u) k = false ∧ rootsWire C.gates (rootsPoint v) k = false

def ValidRead (n : ℕ) (C : Circuit) (a b : ℕ) : Prop :=
  ∃ j g, b = n + j ∧ C.gates[j]? = some g ∧ a ∈ g.inputs ∧ a < b

def LiveRead {n : ℕ} (C : Circuit) (u v : Fin n) (a b : ℕ) : Prop :=
  ValidRead n C a b ∧ LivePairWire C u v a ∧ LivePairWire C u v b

def LiveMergeWitness {n : ℕ} (C : Circuit) (u v : Fin n) (k : ℕ) : Prop :=
  ∃ pre g rest, C.gates = pre ++ g :: rest ∧ PairMerge pre g u v ∧
    g.op = GateOp.and ∧
    (∃ a b, g.inputs = [a, b] ∧ OppositeInputs pre a b u v) ∧
    Relation.ReflTransGen (LiveRead C u v) (n + pre.length) k

lemma live_merge_backtrace {n : ℕ} (C : Circuit) (mono : Monotone2 C)
    (u v : Fin n) (k : ℕ) (active : LivePairWire C u v k) : LiveMergeWitness C u v k := by
  classical
  induction k using Nat.strong_induction_on with
  | ind k ih =>
    by_cases input : k < n
    · have keep (x : Fin n → Bool) : rootsWire C.gates x k = rootsWire [] x k := by
        simpa using live_append_wire [] C.gates x k (by simpa using input)
      obtain ⟨hp, hu, hv⟩ := active
      rw [keep] at hp hu hv
      have hp' : (⟨k, input⟩ : Fin n) = u ∨ (⟨k, input⟩ : Fin n) = v := by
        simpa [rootsWire, rootsTrace, List.getD, input, Pair] using hp
      rcases hp' with hku | hkv
      · simp [rootsWire, rootsTrace, List.getD, input, rootsPoint, hku] at hu
      · simp [rootsWire, rootsTrace, List.getD, input, rootsPoint, hkv] at hv
    · have bounded := true_wire_in_bounds C.gates (Pair u v) k active.1
      let j := k - n
      have hj : j < C.gates.length := by dsimp [j]; omega
      let g := C.gates[j]
      let pre := C.gates.take j
      let rest := C.gates.drop (j + 1)
      have split : C.gates = pre ++ g :: rest := by
        exact (List.take_append_drop j C.gates).symm.trans (by rw [List.drop_eq_getElem_cons hj])
      have plen : pre.length = j := by simp [pre, Nat.min_eq_left (Nat.le_of_lt hj)]
      have kgate : k = n + pre.length := by rw [plen]; dsimp [j]; omega
      have value (x : Fin n → Bool) : rootsWire C.gates x k = rootsVal pre g x := by
        rw [kgate, split, roots_gate_value]
      have merge : PairMerge pre g u v := by
        simpa only [LivePairWire, PairMerge, value] using active
      have member : g ∈ C.gates := by simp [split]
      have ops : g.op = GateOp.and ∨ g.op = GateOp.or := by simpa using (mono g member).1
      rcases live_gate_predecessor_or_merge pre g u v ops (mono g member).2 merge with
        ⟨i, hi, hpi, hui, hvi⟩ | ⟨op, a, b, inputs, opposite⟩
      · have ilt : i < n + pre.length := true_wire_in_bounds pre (Pair u v) i hpi
        have keep (x : Fin n → Bool) : rootsWire C.gates x i = rootsWire pre x i := by
          rw [split]
          exact live_append_wire pre (g :: rest) x i ilt
        have alive : LivePairWire C u v i := by
          simpa only [LivePairWire, keep] using And.intro hpi (And.intro hui hvi)
        have read : LiveRead C u v i k := by
          refine ⟨⟨pre.length, g, kgate, ?_, hi, ?_⟩, alive, active⟩
          · simp [split]
          · omega
        obtain ⟨pre', g', rest', split', merge', op', inputs', path⟩ := ih i (by omega) alive
        exact ⟨pre', g', rest', split', merge', op', inputs', path.tail read⟩
      · refine ⟨pre, g, rest, split, merge, op, ⟨a, b, inputs, opposite⟩, ?_⟩
        rw [kgate]

lemma exists_live_pair_merge {n : ℕ} (C : Circuit) (mono : Monotone2 C)
    (u v : Fin n)
    (positive : C.eval (List.ofFn (Pair u v)) = true)
    (singleU : C.eval (List.ofFn (rootsPoint u)) = false)
    (singleV : C.eval (List.ofFn (rootsPoint v)) = false) :
    LiveMergeWitness C u v C.output :=
  live_merge_backtrace C mono u v C.output ⟨positive, singleU, singleV⟩

lemma matching_cross_forces_side {k : ℕ} (hk : 2 ≤ k) (A B : Fin k → Bool)
    (independent : ∀ i, ¬ (A i = true ∧ B i = true))
    (cross : ∀ i j, i ≠ j → B i = true ∨ A j = true) :
    (∀ i, A i = true) ∨ (∀ i, B i = true) := by
  by_cases active : ∃ i, A i = true
  · obtain ⟨i, hi⟩ := active
    left
    intro j
    by_cases hij : i = j
    · simpa only [← hij] using hi
    · exact (cross i j hij).resolve_left (fun hbi => independent i ⟨hi, hbi⟩)
  · right
    intro i
    obtain ⟨j, hij⟩ : ∃ j : Fin k, i ≠ j := by
      by_cases hi : i.val = 0
      · refine ⟨⟨1, by omega⟩, ?_⟩
        intro hij
        have hv := congrArg Fin.val hij
        simp only at hv
        omega
      · refine ⟨⟨0, by omega⟩, ?_⟩
        intro hij
        exact hi (congrArg Fin.val hij)
    exact (cross i j hij).resolve_right (fun haj => active ⟨j, haj⟩)

lemma matching_context_independent {k n : ℕ} (hk : 2 ≤ k)
    (G : SimpleGraph (Fin n)) (a b : Fin k → Fin n)
    (aa : ∀ i j, ¬ G.Adj (a i) (a j))
    (bb : ∀ i j, ¬ G.Adj (b i) (b j))
    (ab : ∀ i j, G.Adj (a i) (b j) ↔ i = j)
    (f h : (Fin n → Bool) → Bool) (hf : Increasing f) (hh : Increasing h)
    (lower : ∀ y, (∃ i, y (a i) = true) → (∃ j, y (b j) = true) → f y = true)
    (safe : ∀ y, f y = true → h y = true → rootsHit G y)
    (x : Fin n → Bool)
    (supported : ∀ v, x v = true → (∃ i, v = a i) ∨ ∃ j, v = b j)
    (independent : ¬ rootsHit G x) (active : h x = true) :
    (∀ i, x (a i) = true) ∨ (∀ i, x (b i) = true) := by
  apply matching_cross_forces_side hk (fun i => x (a i)) (fun i => x (b i))
  · intro i ⟨ha, hb⟩
    exact independent ⟨a i, b i, (ab i i).mpr rfl, ha, hb⟩
  · intro i j hij
    have hnon : ¬ G.Adj (a i) (b j) := fun e => hij ((ab i j).mp e)
    have hpair : f (Pair (a i) (b j)) = true :=
      lower _ ⟨i, by simp [Pair]⟩ ⟨j, by simp [Pair]⟩
    obtain ⟨w, hw, haw | hbw⟩ :=
      independent_blocker_bound G f h hf hh safe (a i) (b j) hnon hpair x independent active
    · rcases supported w hw with ⟨l, rfl⟩ | ⟨l, rfl⟩
      · exact (aa i l haw).elim
      · have hil : i = l := (ab i l).mp haw
        exact Or.inl (by simpa only [hil] using hw)
    · rcases supported w hw with ⟨l, rfl⟩ | ⟨l, rfl⟩
      · have hlj : l = j := (ab l j).mp hbw.symm
        exact Or.inr (by simpa only [hlj] using hw)
      · exact (bb j l hbw).elim

lemma matching_context_supported {k n : ℕ} (hk : 2 ≤ k)
    (G : SimpleGraph (Fin n)) (a b : Fin k → Fin n)
    (aa : ∀ i j, ¬ G.Adj (a i) (a j))
    (bb : ∀ i j, ¬ G.Adj (b i) (b j))
    (ab : ∀ i j, G.Adj (a i) (b j) ↔ i = j)
    (f h : (Fin n → Bool) → Bool) (hf : Increasing f) (hh : Increasing h)
    (lower : ∀ y, (∃ i, y (a i) = true) → (∃ j, y (b j) = true) → f y = true)
    (safe : ∀ y, f y = true → h y = true → rootsHit G y)
    (x : Fin n → Bool)
    (supported : ∀ v, x v = true → (∃ i, v = a i) ∨ ∃ j, v = b j)
    (active : h x = true) :
    rootsHit G x ∨ (∀ i, x (a i) = true) ∨ (∀ i, x (b i) = true) := by
  by_cases hit : rootsHit G x
  · exact Or.inl hit
  · exact Or.inr (matching_context_independent hk G a b aa bb ab f h hf hh lower safe
      x supported hit active)

def matchingSide {k n : ℕ} (a : Fin k → Fin n) : Fin n → Bool :=
  fun v => decide (∃ i, v = a i)

lemma matching_side_le {k n : ℕ} (a : Fin k → Fin n) (x : Fin n → Bool)
    (all : ∀ i, x (a i) = true) : InputLE (matchingSide a) x := by
  intro v hv
  obtain ⟨i, rfl⟩ := of_decide_eq_true hv
  exact all i

lemma matching_independent_side_eq {k n : ℕ} (G : SimpleGraph (Fin n))
    (a b : Fin k → Fin n) (edges : ∀ i, G.Adj (a i) (b i))
    (x : Fin n → Bool)
    (supported : ∀ v, x v = true → (∃ i, v = a i) ∨ ∃ j, v = b j)
    (independent : ¬ rootsHit G x) (all : ∀ i, x (a i) = true) :
    x = matchingSide a := by
  funext v
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hv
    rcases supported v hv with ⟨i, rfl⟩ | ⟨j, rfl⟩
    · exact decide_eq_true ⟨i, rfl⟩
    · exact (independent ⟨a j, b j, edges j, all j, hv⟩).elim
  · exact matching_side_le a x all v

lemma matching_hit_iff {k n : ℕ} (G : SimpleGraph (Fin n)) (a b : Fin k → Fin n)
    (aa : ∀ i j, ¬ G.Adj (a i) (a j))
    (bb : ∀ i j, ¬ G.Adj (b i) (b j))
    (ab : ∀ i j, G.Adj (a i) (b j) ↔ i = j)
    (x : Fin n → Bool)
    (supported : ∀ v, x v = true → (∃ i, v = a i) ∨ ∃ j, v = b j) :
    rootsHit G x ↔ ∃ i, x (a i) = true ∧ x (b i) = true := by
  constructor
  · rintro ⟨u, v, huv, hu, hv⟩
    rcases supported u hu with ⟨i, rfl⟩ | ⟨i, rfl⟩ <;>
      rcases supported v hv with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · exact (aa i j huv).elim
    · have hij := (ab i j).mp huv
      exact ⟨i, hu, by simpa only [hij] using hv⟩
    · have hji := (ab j i).mp huv.symm
      exact ⟨i, by simpa only [hji] using hv, hu⟩
    · exact (bb i j huv).elim
  · rintro ⟨i, ha, hb⟩
    exact ⟨a i, b i, (ab i i).mpr rfl, ha, hb⟩

lemma matching_context_exact {k n : ℕ} (hk : 2 ≤ k)
    (G : SimpleGraph (Fin n)) (a b : Fin k → Fin n)
    (aa : ∀ i j, ¬ G.Adj (a i) (a j))
    (bb : ∀ i j, ¬ G.Adj (b i) (b j))
    (ab : ∀ i j, G.Adj (a i) (b j) ↔ i = j)
    (f h : (Fin n → Bool) → Bool) (hf : Increasing f) (hh : Increasing h)
    (lower : ∀ y, (∃ i, y (a i) = true) → (∃ j, y (b j) = true) → f y = true)
    (safe : ∀ y, f y = true → h y = true → rootsHit G y)
    (edges : ∀ i, h (Pair (a i) (b i)) = true)
    (x : Fin n → Bool)
    (supported : ∀ v, x v = true → (∃ i, v = a i) ∨ ∃ j, v = b j) :
    h x = true ↔ rootsHit G x ∨
      (h (matchingSide a) = true ∧ ∀ i, x (a i) = true) ∨
      (h (matchingSide b) = true ∧ ∀ i, x (b i) = true) := by
  constructor
  · intro hx
    by_cases hit : rootsHit G x
    · exact Or.inl hit
    · rcases matching_context_independent hk G a b aa bb ab f h hf hh lower safe
          x supported hit hx with allA | allB
      · have heq := matching_independent_side_eq G a b (fun i => (ab i i).mpr rfl)
          x supported hit allA
        exact Or.inr (Or.inl ⟨by simpa only [← heq] using hx, allA⟩)
      · have heq := matching_independent_side_eq G b a (fun i => ((ab i i).mpr rfl).symm)
          x (fun v hv => (supported v hv).symm) hit allB
        exact Or.inr (Or.inr ⟨by simpa only [← heq] using hx, allB⟩)
  · rintro (hit | ⟨ha, allA⟩ | ⟨hb, allB⟩)
    · obtain ⟨i, hai, hbi⟩ := (matching_hit_iff G a b aa bb ab x supported).mp hit
      apply hh (Pair (a i) (b i)) x _ (edges i)
      intro v hv
      simp only [Pair, decide_eq_true_eq] at hv
      rcases hv with rfl | rfl
      · exact hai
      · exact hbi
    · exact hh (matchingSide a) x (matching_side_le a x allA) ha
    · exact hh (matchingSide b) x (matching_side_le b x allB) hb

end PEqualNP.Outside.L_meta_1904
