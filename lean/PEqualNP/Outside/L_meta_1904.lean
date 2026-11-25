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

end PEqualNP.Outside.L_meta_1904
