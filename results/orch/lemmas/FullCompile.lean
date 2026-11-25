import PEqualNP.Defs

-- The live-set search and its completeness proof are adapted from
-- lean/PEqualNP/Outside/L_meta_6345.lean in this repository, widened from 64 to 36
-- (true entry, false entry) pairs; the rows, the 10-gate search and the conclusion are new.

namespace PEqualNP.Outside.L_meta_9502.FullCompile

open scoped Classical

section Live

variable {α : Type}

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

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open scoped Classical

variable {ι : Type}
abbrev W (ι : Type) := ι → Bool

def zero : W ι := fun _ => false
def one : W ι := fun _ => true
def band (a b : W ι) : W ι := fun i => a i && b i
def bor (a b : W ι) : W ι := fun i => a i || b i
noncomputable def basicOps (a b : W ι) : Finset (W ι) := {band a b, bor a b}

def possible (ws : List (W ι)) (z : W ι) : Prop :=
  z = zero ∨ z = one ∨ z ∈ ws ∨
  ∃ a ∈ ws, ∃ b ∈ ws, z = band a b ∨ z = bor a b

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def legal (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

lemma read_bit (w : List (W ι)) (i : ℕ) (k : ι) :
    (w.map (fun f => f k)).getD i false = (w.getD i zero) k := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), zero]

lemma read_wire (w : List (W ι)) (i : ℕ) : w.getD i zero = zero ∨ w.getD i zero ∈ w := by
  by_cases h : i < w.length
  · exact Or.inr (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt h)]

lemma atom {ws : List (W ι)} {x : W ι} (hx : x = zero ∨ x ∈ ws) : possible ws x := by
  rcases hx with rfl | hx
  · exact .inl rfl
  · exact .inr (.inr (.inl hx))

lemma band_zero (a : W ι) : band zero a = zero := by ext i; simp [band, zero]
lemma band_one (a : W ι) : band one a = a := by ext i; simp [band, one]
lemma band_zero_right (a : W ι) : band a zero = zero := by ext i; simp [band, zero]
lemma band_one_right (a : W ι) : band a one = a := by ext i; simp [band, one]
lemma band_self (a : W ι) : band a a = a := by ext i; simp [band]
lemma bor_zero (a : W ι) : bor zero a = a := by ext i; simp [bor, zero]
lemma bor_one (a : W ι) : bor one a = one := by ext i; simp [bor, one]
lemma bor_zero_right (a : W ι) : bor a zero = a := by ext i; simp [bor, zero]
lemma bor_one_right (a : W ι) : bor a one = one := by ext i; simp [bor, one]
lemma bor_self (a : W ι) : bor a a = a := by ext i; simp [bor]

lemma pair {ws : List (W ι)} {x y : W ι}
    (hx : x = zero ∨ x ∈ ws) (hy : y = zero ∨ y ∈ ws) :
    possible ws (band x y) ∧ possible ws (bor x y) := by
  rcases hx with rfl | hx
  · exact ⟨.inl (band_zero y), (bor_zero y).symm ▸ atom hy⟩
  rcases hy with rfl | hy
  · exact ⟨.inl (band_zero_right x), (bor_zero_right x).symm ▸ atom (.inr hx)⟩
  · constructor
    · exact .inr (.inr (.inr ⟨x,hx,y,hy,.inl rfl⟩))
    · exact .inr (.inr (.inr ⟨x,hx,y,hy,.inr rfl⟩))

lemma gate_table (w : List (W ι)) (g : Gate) (hg : legal g) :
    ∃ z, possible w z ∧ ∀ k, step (w.map (fun f => f k)) g =
      (w ++ [z]).map (fun f => f k) := by
  obtain ⟨op, args⟩ := g
  obtain ⟨hop, hlen⟩ := hg
  change op = .and ∨ op = .or at hop
  change args.length ≤ 2 at hlen
  cases args with
  | nil =>
    rcases hop with rfl | rfl
    · exact ⟨one, .inr (.inl rfl), by simp [step, GateOp.eval, one]⟩
    · exact ⟨zero, .inl rfl, by simp [step, GateOp.eval, zero]⟩
  | cons i tail =>
    cases tail with
    | nil =>
      rcases hop with rfl | rfl
      · exact ⟨_, atom (read_wire w i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
      · exact ⟨_, atom (read_wire w i),
          by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval]⟩
    | cons j tail =>
      cases tail with
      | cons => simp at hlen
      | nil =>
        rcases hop with rfl | rfl
        · exact ⟨_, (pair (read_wire w i) (read_wire w j)).1,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, band]⟩
        · exact ⟨_, (pair (read_wire w i) (read_wire w j)).2,
            by simp only [step, List.map_cons, List.map_nil, read_bit]; simp [GateOp.eval, bor]⟩

def represents (available : Finset (W ι)) (w : List (W ι)) : Prop :=
  ∀ u ∈ w, u = zero ∨ u = one ∨ u ∈ available

lemma classify {available : Finset (W ι)} {ws : List (W ι)} (hw : represents available ws)
    {z : W ι} (hz : possible ws z) :
    z = zero ∨ z = one ∨ z ∈ available ∨
      ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ z ∈ basicOps a b := by
  have lift {t : W ι} (h : t = zero ∨ t = one ∨ t ∈ available) :
      t = zero ∨ t = one ∨ t ∈ available ∨
        ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧ t ∈ basicOps a b :=
    h.imp_right (Or.imp_right Or.inl)
  rcases hz with h | h | h | ⟨x,hx,y,hy,h|h⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact lift (hw _ h)
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · exact .inl (band_zero y)
    · rw [band_one]; exact lift (hw _ hy)
    rcases hw _ hy with rfl | rfl | hv
    · exact .inl (band_zero_right x)
    · rw [band_one_right]; exact .inr (.inr (.inl hu))
    by_cases h : x = y
    · subst h; rw [band_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x,hu,y,hv,h,by simp [basicOps]⟩))
  · subst z
    rcases hw _ hx with rfl | rfl | hu
    · rw [bor_zero]; exact lift (hw _ hy)
    · exact .inr (.inl (bor_one y))
    rcases hw _ hy with rfl | rfl | hv
    · rw [bor_zero_right]; exact .inr (.inr (.inl hu))
    · exact .inr (.inl (bor_one_right x))
    by_cases h : x = y
    · subst h; rw [bor_self]; exact .inr (.inr (.inl hu))
    · exact .inr (.inr (.inr ⟨x,hu,y,hv,h,by simp [basicOps]⟩))

lemma compile (goal : W ι) (hzero : goal ≠ zero) (hone : goal ≠ one)
    (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List (W ι)) (av : Finset (W ι)) (hw : represents av w)
    (he : ∀ k, (gs.foldl step (w.map (fun f => f k))).getD out false = goal k) :
    build basicOps goal gs.length av := by
  induction gs generalizing w av with
  | nil =>
    have hval : w.getD out zero = goal := by
      funext k
      simpa only [List.foldl_nil, read_bit] using he k
    have hr := read_wire w out
    rw [hval] at hr
    rcases hr with hz | hm
    · exact False.elim (hzero hz)
    · rcases hw _ hm with h | h | h
      · exact False.elim (hzero h)
      · exact False.elim (hone h)
      · exact h
  | cons g gs ih =>
    obtain ⟨z, hz, hstep⟩ := gate_table w g (hg g (by simp))
    have fn := ih (fun g' h => hg g' (by simp [h])) (w ++ [z])
    have he' : ∀ k, (gs.foldl step ((w ++ [z]).map (fun f => f k))).getD out false = goal k := by
      intro k; simpa only [List.foldl_cons, hstep] using he k
    have appendOK (h : z = zero ∨ z = one ∨ z ∈ av) : represents av (w ++ [z]) := by
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · exact hw _ old
      · have eq : u = z := List.mem_singleton.mp fresh
        exact eq ▸ h
    rcases classify hw hz with h | h | h | ⟨a,ha,b,hb,hab,hop⟩
    · exact Or.inl (fn av (appendOK (.inl h)) he')
    · exact Or.inl (fn av (appendOK (.inr (.inl h))) he')
    · exact Or.inl (fn av (appendOK (.inr (.inr h))) he')
    · refine Or.inr ⟨a,ha,b,hb,hab,z,hop,fn (insert z av) ?_ he'⟩
      intro u hu
      rcases List.mem_append.mp hu with old | fresh
      · rcases hw u old with h | h | h
        · exact .inl h
        · exact .inr (.inl h)
        · exact .inr (.inr (Finset.mem_insert_of_mem h))
      · have heq : u = z := List.mem_singleton.mp fresh
        exact .inr (.inr (by simp [heq]))

def input {n : Nat} (i : Fin n) : W (Fin n → Bool) := fun x => x i
noncomputable def inputSet (n : Nat) : Finset (W (Fin n → Bool)) := Finset.univ.image input

def function (n : Nat) (C : Circuit) : W (Fin n → Bool) :=
  fun x => C.eval (List.ofFn x)

lemma circuit_build {n : Nat} (C : Circuit) (hm : Monotone2 C)
    (hz : function n C ≠ zero) (ho : function n C ≠ one) :
    build basicOps (function n C) C.size (inputSet n) := by
  apply compile (function n C) hz ho C.gates C.output hm
    (List.ofFn (fun i : Fin n => input i)) (inputSet n)
  · intro u hu
    right; right
    simp only [List.mem_ofFn] at hu
    obtain ⟨i,rfl⟩ := hu
    exact Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩
  · intro x
    have hx : (List.ofFn (fun i : Fin n => input i)).map (fun f => f x) = List.ofFn x := by
      rw [List.map_ofFn]
      rfl
    rw [hx]
    rfl

lemma circuit_live {n : Nat} (C : Circuit) (hm : Monotone2 C)
    (hz : function n C ≠ zero) (ho : function n C ≠ one) :
    ∃ S ⊆ inputSet n, live basicOps (function n C) C.size S :=
  compress (circuit_build C hm hz ho)

lemma input_injective (n : Nat) : Function.Injective (@input n) := by
  intro i j hij
  by_contra hn
  have h := congrFun hij (fun k => decide (k=i))
  simp [input, Ne.symm hn] at h

lemma inputSet_card (n : Nat) : (inputSet n).card = n := by
  rw [inputSet, Finset.card_image_of_injective _ (input_injective n)]
  simp

lemma ops_differs (x y : ι) (a b z : W ι) (hz : z ∈ basicOps a b)
    (hd : z x ≠ z y) : a x ≠ a y ∨ b x ≠ b y := by
  by_contra h
  push Not at h
  simp only [basicOps, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact hd (by simp [band, h.1, h.2])
  · exact hd (by simp [bor, h.1, h.2])

def Essential {n : Nat} (goal : W (Fin n → Bool)) (i : Fin n) : Prop :=
  ∃ x y, (∀ j, j ≠ i → x j = y j) ∧ goal x ≠ goal y

lemma live_essential {n k : Nat} {goal : W (Fin n → Bool)} {S : Finset (W (Fin n → Bool))}
    (hsub : S ⊆ inputSet n) (hl : live basicOps goal k S)
    (he : ∀ i, Essential goal i) : S = inputSet n := by
  apply Finset.Subset.antisymm hsub
  intro f hf
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hf
  obtain ⟨x,y,hxy,hgoal⟩ := he i
  obtain ⟨w,hw,hd⟩ := live_separates (fun w => w x ≠ w y) hgoal (ops_differs x y) hl
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp (hsub hw)
  have hji : j = i := by
    by_contra hne
    exact hd (hxy j hne)
  simpa [hji] using hw

lemma circuit_live_all {n : Nat} (C : Circuit) (hm : Monotone2 C)
    (hz : function n C ≠ zero) (ho : function n C ≠ one)
    (he : ∀ i, Essential (function n C) i) :
    live basicOps (function n C) C.size (inputSet n) := by
  obtain ⟨S,hS,hl⟩ := circuit_live C hm hz ho
  exact (live_essential hS hl he) ▸ hl

def Regular (x0 x1 : ι) (f : W ι) : Prop := f x0 = false ∧ f x1 = true

lemma ops_regular {x0 x1 : ι} {a b z : W ι}
    (ha : Regular x0 x1 a) (hb : Regular x0 x1 b) (hz : z ∈ basicOps a b) :
    Regular x0 x1 z := by
  rcases ha with ⟨ha0,ha1⟩
  rcases hb with ⟨hb0,hb1⟩
  simp only [basicOps, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl <;> simp [Regular, band, bor, ha0,ha1,hb0,hb1]

lemma inputs_regular {n : Nat} {f : W (Fin n → Bool)} (hf : f ∈ inputSet n) :
    Regular (fun _ => false) (fun _ => true) f := by
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hf
  exact ⟨rfl,rfl⟩

lemma regular_not_zero {x0 x1 : ι} {f : W ι} (hf : Regular x0 x1 f) : f ≠ zero := by
  intro h
  rw [h] at hf
  simp [Regular, zero] at hf

lemma ops_separates (x y : ι) (a b z : W ι) (hz : z ∈ basicOps a b)
    (hd : z x = true ∧ z y = false) :
    (a x = true ∧ a y = false) ∨ (b x = true ∧ b y = false) := by
  simp only [basicOps, Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl <;> simp only [band,bor] at hd <;>
    cases hax : a x <;> cases hay : a y <;> cases hbx : b x <;> cases hby : b y <;> simp_all

def DirectedCut {n : Nat} (goal : W (Fin n → Bool)) (i : Fin n) : Prop :=
  ∃ x y, goal x = true ∧ goal y = false ∧
    ∀ j, x j = true → y j = false → j = i

lemma live_directed {n k : Nat} {goal : W (Fin n → Bool)} {S : Finset (W (Fin n → Bool))}
    (hsub : S ⊆ inputSet n) (hl : live basicOps goal k S)
    (he : ∀ i, DirectedCut goal i) : S = inputSet n := by
  apply Finset.Subset.antisymm hsub
  intro f hf
  obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hf
  obtain ⟨x,y,hx,hy,hcut⟩ := he i
  obtain ⟨w,hw,hd⟩ := live_separates (fun w => w x = true ∧ w y = false)
    ⟨hx,hy⟩ (ops_separates x y) hl
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp (hsub hw)
  have hji := hcut j hd.1 hd.2
  simpa [hji] using hw

lemma circuit_live_directed {n : Nat} (C : Circuit) (hm : Monotone2 C)
    (hz : function n C ≠ zero) (ho : function n C ≠ one)
    (he : ∀ i, DirectedCut (function n C) i) :
    live basicOps (function n C) C.size (inputSet n) := by
  obtain ⟨S,hS,hl⟩ := circuit_live C hm hz ho
  exact (live_directed hS hl he) ▸ hl

def agrees (goal : W ι) (F : (W ι → Bool) → Bool) : Prop :=
  ∀ x, F (fun f => f x) = goal x

lemma agrees_subst {goal : W ι} {F : (W ι → Bool) → Bool} {z a b : W ι}
    (isOr : Bool) (he : z = if isOr then bor a b else band a b)
    (hF : agrees goal F) :
    agrees goal (fun x => F (Function.update x z (if isOr then x a || x b else x a && x b))) := by
  intro x
  have hv : (if isOr then a x || b x else a x && b x) = z x := by
    rw [he]
    cases isOr <;> rfl
  change F (Function.update (fun f => f x) z (if isOr then a x || b x else a x && b x)) = goal x
  rw [hv,Function.update_eq_self]
  exact hF x

end PEqualNP.Outside.L_meta_9502.FullCompile
