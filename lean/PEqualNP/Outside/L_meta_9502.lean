import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_9502

namespace FullCompile

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

end FullCompile

namespace Structural

universe u
variable {α : Type u} [DecidableEq α]

def on (a c : α) : α → Bool := fun i => decide (i = a) || decide (i = c)

lemma on_iff (a c i : α) : on a c i = true ↔ i = a ∨ i = c := by simp [on]

def Dep (F : (α → Bool) → Bool) (N : Finset α) : Prop :=
  ∀ x y : α → Bool, (∀ i ∈ N, x i = y i) → F x = F y

def Free (F : (α → Bool) → Bool) : Prop :=
  F (fun _ => false) = false ∧ ∀ a b c d, F (on a a) = false → F (on b b) = false →
    F (on c c) = false → F (on d d) = false → F (on a c) = true → F (on a d) = true →
    F (on b c) = true → F (on b d) = true

lemma bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all

lemma free_or {F : (α → Bool) → Bool} {N : Finset α} (hd : Dep F N) (hf : Free F) {t p q : α}
    (hp : p ∉ N.erase t) (hq : q ∉ N.erase t) (z : α) (hz : z ∉ N) :
    Free fun x => F (Function.update x t (x p || x q)) := by
  classical
  let r : α → α := fun a => if a = p ∨ a = q then t else if a ∈ N.erase t then a else z
  have key : ∀ a c, F (Function.update (on a c) t (on a c p || on a c q)) = F (on (r a) (r c)) := by
    intro a c
    refine hd _ _ fun i hi => bool_ext ?_
    have hr : ∀ a, (i = t → (i = r a ↔ a = p ∨ a = q)) ∧ (i ≠ t → (i = r a ↔ i = a)) := by
      intro a
      have hiz : i ≠ z := fun h => hz (h ▸ hi)
      constructor
      · intro hit
        simp only [r]
        split_ifs with h1 h2
        · simp [hit, h1]
        · have := Finset.ne_of_mem_erase h2
          simp only [h1, iff_false]; rw [hit]; exact fun h => this h.symm
        · simp [h1, hiz]
      · intro hit
        have hiN : i ∈ N.erase t := Finset.mem_erase.2 ⟨hit, hi⟩
        simp only [r]
        split_ifs with h1 h2
        · simp only [hit, false_iff]
          rintro rfl
          rcases h1 with rfl | rfl
          · exact hp hiN
          · exact hq hiN
        · rfl
        · simp only [hiz, false_iff]
          rintro rfl; exact h2 hiN
    rw [on_iff]
    by_cases hit : i = t
    · rw [(hr a).1 hit, (hr c).1 hit, hit, Function.update_self, Bool.or_eq_true, on_iff, on_iff]
      constructor
      · rintro ((h | h) | (h | h)) <;> simp [h]
      · rintro ((h | h) | (h | h)) <;> simp [h]
    · rw [(hr a).2 hit, (hr c).2 hit, Function.update_of_ne hit, on_iff]
  refine ⟨?_, ?_⟩
  · show F (Function.update (fun _ => false) t (false || false)) = false
    rw [show Function.update (fun _ : α => false) t (false || false) = fun _ => false from by
      funext i; by_cases h : i = t <;> simp [Function.update, h]]
    exact hf.1
  · intro a b c d
    simp only [key]
    exact hf.2 _ _ _ _

lemma free_and_lift {F : (α → Bool) → Bool} {N : Finset α} (hd : Dep F N) {t p q : α}
    (hf : Free (fun x => F (Function.update x t false)))
    (ht : t ∈ N) (hpq : p ≠ q) (hp : p ∉ N.erase t) (hq : q ∉ N.erase t) (z : α) (hz : z ∉ N) :
    Free fun x => F (Function.update x t (x p && x q)) := by
  classical
  have hzF : F (fun _ => false) = false := by
    simpa using hf.1
  let r : α → α := fun a => if a ∈ N.erase t then a else z
  have rt : ∀ a, r a ≠ t := by
    intro a
    simp only [r]
    split_ifs with h
    · exact Finset.ne_of_mem_erase h
    · exact fun hzt => hz (hzt ▸ ht)
  have kill_eq : ∀ a c,
      F (Function.update (on (r a) (r c)) t false) = F (on (r a) (r c)) := by
    intro a c
    congr 1
    funext i
    by_cases hit : i = t
    · subst i
      simp [on, (rt a).symm, (rt c).symm]
    · simp [Function.update_of_ne hit]
  have rp : r p = z := ite_eq_right hp
  have rq : r q = z := ite_eq_right hq
  have hzz : ∀ x, F (on x z) = F (on x x) := fun x => hd _ _ fun i hi => by
    have : i ≠ z := fun h => hz (h ▸ hi)
    simp [on, this]
  have hzz' : ∀ x, F (on z x) = F (on x x) := fun x => hd _ _ fun i hi => by
    have : i ≠ z := fun h => hz (h ▸ hi)
    simp [on, this]
  have hz0 : F (on z z) = false := by
    rw [← hzF]
    exact hd _ _ fun i hi => by
      have : i ≠ z := fun h => hz (h ▸ hi)
      simp [on, this]
  have key : ∀ a c, ¬ (a = p ∧ c = q) → ¬ (a = q ∧ c = p) →
      F (Function.update (on a c) t (on a c p && on a c q)) = F (on (r a) (r c)) := by
    intro a c h1 h2
    refine hd _ _ fun i hi => bool_ext ?_
    have hiz : i ≠ z := fun h => hz (h ▸ hi)
    have hr : ∀ a, i = r a ↔ i ≠ t ∧ i = a := by
      intro a
      simp only [r]
      split_ifs with h
      · constructor
        · intro e; exact ⟨e ▸ Finset.ne_of_mem_erase h, e⟩
        · exact fun e => e.2
      · simp only [hiz, false_iff]
        rintro ⟨e1, rfl⟩
        exact h (Finset.mem_erase.2 ⟨e1, hi⟩)
    rw [on_iff, hr, hr]
    by_cases hit : i = t
    · rw [hit, Function.update_self, Bool.and_eq_true, on_iff, on_iff]
      constructor
      · rintro ⟨e1 | e1, e2 | e2⟩
        · exact absurd (e1.trans e2.symm) hpq
        · exact absurd ⟨e1.symm, e2.symm⟩ h1
        · exact absurd ⟨e2.symm, e1.symm⟩ h2
        · exact absurd (e1.trans e2.symm) hpq
      · rintro (⟨e, _⟩ | ⟨e, _⟩) <;> exact absurd rfl e
    · rw [Function.update_of_ne hit, on_iff]
      simp [hit]
  have kk : ∀ a, F (Function.update (on a a) t (on a a p && on a a q)) = F (on (r a) (r a)) :=
    fun a => key a a (fun h => hpq (h.1.symm.trans h.2)) (fun h => hpq (h.2.symm.trans h.1))
  refine ⟨?_, ?_⟩
  · show F (Function.update (fun _ => false) t (false && false)) = false
    rw [show Function.update (fun _ : α => false) t (false && false) = fun _ => false from by
      funext i; by_cases h : i = t <;> simp [Function.update, h]]
    exact hzF
  · intro a b c d ha hb hc hd' hac had hbc
    beta_reduce at ha hb hc hd' hac had hbc

    have nb : ∀ e f, (e = p ∨ e = q) →
        F (Function.update (on f f) t (on f f p && on f f q)) = false →
        (F (Function.update (on e f) t (on e f p && on e f q)) = true →
          (e = p ∧ f = q) ∨ (e = q ∧ f = p)) ∧
        (F (Function.update (on f e) t (on f e p && on f e q)) = true →
          (f = p ∧ e = q) ∨ (f = q ∧ e = p)) := by
      intro e f he hf0
      have re : r e = z := by rcases he with rfl | rfl <;> assumption
      rw [kk] at hf0
      constructor
      · intro h
        by_contra hn
        rw [key e f (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h)), re, hzz', hf0] at h
        exact Bool.noConfusion h
      · intro h
        by_contra hn
        rw [key f e (fun h => hn (Or.inl h)) (fun h => hn (Or.inr h)), re, hzz, hf0] at h
        exact Bool.noConfusion h
    by_cases hA : a = p ∨ a = q
    · have e1 := (nb a c hA hc).1 hac
      have e2 := (nb a d hA hd').1 had
      have : c = d := by
        rcases e1 with ⟨x, y⟩ | ⟨x, y⟩ <;> rcases e2 with ⟨x', y'⟩ | ⟨x', y'⟩
        · rw [y, y']
        · exact absurd (x.symm.trans x') hpq
        · exact absurd (x'.symm.trans x) hpq
        · rw [y, y']
      rw [← this]; exact hbc
    · by_cases hB : b = p ∨ b = q
      · have e1 := (nb b c hB hc).1 hbc
        have hC : c = p ∨ c = q := by
          rcases e1 with ⟨_, y⟩ | ⟨_, y⟩
          · exact Or.inr y
          · exact Or.inl y
        have e2 := (nb c a hC ha).2 hac
        exact absurd (by rcases e2 with ⟨x, _⟩ | ⟨x, _⟩ <;> simp [x]) hA
      · have n1 : ∀ e, ¬ (a = p ∧ e = q) ∧ ¬ (a = q ∧ e = p) := fun e =>
          ⟨fun h => hA (Or.inl h.1), fun h => hA (Or.inr h.1)⟩
        have n2 : ∀ e, ¬ (b = p ∧ e = q) ∧ ¬ (b = q ∧ e = p) := fun e =>
          ⟨fun h => hB (Or.inl h.1), fun h => hB (Or.inr h.1)⟩
        rw [kk] at ha hb hc hd'
        rw [key _ _ (n1 c).1 (n1 c).2] at hac
        rw [key _ _ (n1 d).1 (n1 d).2] at had
        rw [key _ _ (n2 c).1 (n2 c).2] at hbc
        show F (Function.update (on b d) t (on b d p && on b d q)) = true
        rw [key _ _ (n2 d).1 (n2 d).2]
        have hfree := hf.2 (r a) (r b) (r c) (r d)
        simp only [kill_eq] at hfree
        exact hfree ha hb hc hd' hac had hbc

def kill (E : Finset α) (x : α → Bool) : α → Bool :=
  fun i => if i ∈ E then false else x i

lemma kill_empty (x : α → Bool) : kill ∅ x = x := by
  funext i
  simp [kill]

lemma kill_zero (E : Finset α) : kill E (fun _ => false) = fun _ => false := by
  funext i
  simp [kill]

lemma kill_union (E D : Finset α) (x : α → Bool) :
    kill E (kill D x) = kill (E ∪ D) x := by
  funext i
  by_cases he : i ∈ E <;> by_cases hd : i ∈ D <;> simp [kill, he, hd]

lemma kill_on (E : Finset α) (a b : α) (ha : a ∉ E) (hb : b ∉ E) :
    kill E (on a b) = on a b := by
  funext i
  by_cases hi : i ∈ E
  · have hia : i ≠ a := fun h => ha (h ▸ hi)
    have hib : i ≠ b := fun h => hb (h ▸ hi)
    simp [kill, on, hi, hia, hib]
  · simp [kill, hi]

lemma kill_on_left (E : Finset α) (a b : α) (ha : a ∈ E) :
    kill E (on a b) = kill E (on b b) := by
  funext i
  by_cases hi : i ∈ E
  · simp [kill, hi]
  · have hia : i ≠ a := fun h => hi (h ▸ ha)
    simp [kill, on, hi, hia]

lemma on_comm (a b : α) : on a b = on b a := by
  funext i
  simp [on, Bool.or_comm]

lemma free_kill {F : (α → Bool) → Bool} (hf : Free F) (E : Finset α) :
    Free (fun x => F (kill E x)) := by
  refine ⟨?_, ?_⟩
  · simpa only [kill_zero] using hf.1
  · intro a b c d ha hb hc hd hac had hbc
    beta_reduce at ha hb hc hd hac had hbc ⊢
    have na : a ∉ E := by
      intro h
      rw [kill_on_left E a c h] at hac
      simp only [hc, Bool.false_eq_true] at hac
    have nb : b ∉ E := by
      intro h
      rw [kill_on_left E b c h] at hbc
      simp only [hc, Bool.false_eq_true] at hbc
    have nc : c ∉ E := by
      intro h
      rw [on_comm a c, kill_on_left E c a h] at hac
      simp only [ha, Bool.false_eq_true] at hac
    have nd : d ∉ E := by
      intro h
      rw [on_comm a d, kill_on_left E d a h] at had
      simp only [ha, Bool.false_eq_true] at had
    rw [kill_on E a a na na] at ha
    rw [kill_on E b b nb nb] at hb
    rw [kill_on E c c nc nc] at hc
    rw [kill_on E d d nd nd] at hd
    rw [kill_on E a c na nc] at hac
    rw [kill_on E a d na nd] at had
    rw [kill_on E b c nb nc] at hbc
    rw [kill_on E b d nb nd]
    exact hf.2 a b c d ha hb hc hd hac had hbc

lemma free_kill_mono {F : (α → Bool) → Bool} {E D : Finset α}
    (hf : Free (fun x => F (kill E x))) (hED : E ⊆ D) :
    Free (fun x => F (kill D x)) := by
  have h := free_kill hf D
  simpa only [kill_union, Finset.union_eq_right.mpr hED] using h

lemma dep_kill {F : (α → Bool) → Bool} {N : Finset α} (hd : Dep F N) (E : Finset α) :
    Dep (fun x => F (kill E x)) (N \ E) := by
  intro x y hxy
  apply hd
  intro i hi
  by_cases he : i ∈ E
  · simp [kill, he]
  · simpa only [kill, ite_eq_right he] using hxy i (Finset.mem_sdiff.mpr ⟨hi, he⟩)

lemma kill_update_zero (E : Finset α) (x : α → Bool) (t : α) :
    Function.update (kill E x) t false = kill (insert t E) x := by
  funext i
  by_cases hit : i = t <;> by_cases hi : i ∈ E <;> simp [kill, Function.update, hit, hi]

lemma kill_update_comm (E : Finset α) (x : α → Bool) (t : α) (v : Bool)
    (ht : t ∉ E) :
    Function.update (kill E x) t v = kill E (Function.update x t v) := by
  funext i
  by_cases hit : i = t
  · subst i
    simp [kill, ht]
  · simp only [Function.update_of_ne hit, kill]

lemma free_mask_sub_zero {F : (α → Bool) → Bool} {E D : Finset α}
    (hf : Free (fun x => F (kill E x))) (op : Bool → Bool → Bool) (t p q : α)
    (hED : E ⊆ insert t D)
    (hzero : ∀ x : α → Bool, op (kill D x p) (kill D x q) = false) :
    Free (fun x => F (Function.update (kill D x) t (op (kill D x p) (kill D x q)))) := by
  have heq : (fun x => F (Function.update (kill D x) t (op (kill D x p) (kill D x q)))) =
      fun x => F (kill (insert t D) x) := by
    funext x
    rw [hzero, kill_update_zero]
  rw [heq]
  exact free_kill_mono hf hED

lemma free_mask_or_fresh {F : (α → Bool) → Bool} {N E : Finset α}
    (hd : Dep F N) (hf : Free (fun x => F (kill E x))) {t p q : α}
    (ht : t ∉ E) (hp : p ∉ E) (hq : q ∉ E)
    (hpN : p ∉ N.erase t) (hqN : q ∉ N.erase t) (z : α) (hz : z ∉ N) :
    Free (fun x => F (Function.update (kill E x) t (kill E x p || kill E x q))) := by
  have hp' : p ∉ (N \ E).erase t := by simp only [Finset.mem_erase, Finset.mem_sdiff] at *; tauto
  have hq' : q ∉ (N \ E).erase t := by simp only [Finset.mem_erase, Finset.mem_sdiff] at *; tauto
  have hz' : z ∉ N \ E := fun h => hz (Finset.mem_sdiff.mp h).1
  have h := free_or (dep_kill hd E) hf hp' hq' z hz'
  have heq : (fun x => F (Function.update (kill E x) t (kill E x p || kill E x q))) =
      fun x => F (kill E (Function.update x t (x p || x q))) := by
    funext x
    simp only [kill, ite_eq_right hp, ite_eq_right hq]
    rw [← kill_update_comm E x t _ ht]
  rw [heq]
  exact h

lemma free_mask_and_fresh {F : (α → Bool) → Bool} {N E : Finset α}
    (hd : Dep F N) (hf : Free (fun x => F (kill E x))) {t p q : α}
    (htN : t ∈ N) (hpq : p ≠ q) (hpE : p ∉ E.erase t) (hqE : q ∉ E.erase t)
    (hpN : p ∉ N.erase t) (hqN : q ∉ N.erase t) (z : α) (hz : z ∉ N) :
    Free (fun x => F (Function.update (kill (E.erase t) x) t
      (kill (E.erase t) x p && kill (E.erase t) x q))) := by
  let D := E.erase t
  have htD : t ∉ D := by simp [D]
  have hp' : p ∉ (N \ D).erase t := by simp only [Finset.mem_erase, Finset.mem_sdiff] at *; tauto
  have hq' : q ∉ (N \ D).erase t := by simp only [Finset.mem_erase, Finset.mem_sdiff] at *; tauto
  have ht' : t ∈ N \ D := Finset.mem_sdiff.mpr ⟨htN, htD⟩
  have hz' : z ∉ N \ D := fun h => hz (Finset.mem_sdiff.mp h).1
  have hFD : Free (fun x => F (kill D (Function.update x t false))) := by
    have heq : (fun x => F (kill D (Function.update x t false))) =
        fun x => F (kill (insert t D) x) := by
      funext x
      rw [← kill_update_comm D x t false htD, kill_update_zero]
    rw [heq]
    apply free_kill_mono hf
    intro i hi
    by_cases hit : i = t
    · simp [hit]
    · exact Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨hit, hi⟩)
  have h := free_and_lift (dep_kill hd D) hFD ht' hpq hp' hq' z hz'
  have heq : (fun x => F (Function.update (kill D x) t (kill D x p && kill D x q))) =
      fun x => F (kill D (Function.update x t (x p && x q))) := by
    funext x
    have hpD : p ∉ D := hpE
    have hqD : q ∉ D := hqE
    simp only [kill, ite_eq_right hpD, ite_eq_right hqD]
    rw [← kill_update_comm D x t _ htD]
  change Free (fun x => F (Function.update (kill D x) t (kill D x p && kill D x q)))
  rw [heq]
  exact h

lemma free_mask_or_old_left {F : (α → Bool) → Bool} {N E D : Finset α}
    (hd : Dep F N) (hf : Free (fun x => F (kill E x))) (hED : E ⊆ D)
    {t p q : α} (ht : t ∉ D) (hp : p ∈ D) (hq : q ∉ D)
    (hqN : q ∉ N.erase t) (z : α) (hz : z ∉ N) :
    Free (fun x => F (Function.update (kill D x) t (kill D x p || kill D x q))) := by
  have hq' : q ∉ (N \ D).erase t := by simp only [Finset.mem_erase, Finset.mem_sdiff] at *; tauto
  have hz' : z ∉ N \ D := fun h => hz (Finset.mem_sdiff.mp h).1
  have h := free_or (dep_kill hd D) (free_kill_mono hf hED) hq' hq' z hz'
  have heq : (fun x => F (Function.update (kill D x) t (kill D x p || kill D x q))) =
      fun x => F (kill D (Function.update x t (x q || x q))) := by
    funext x
    simp only [kill, ite_eq_left hp, ite_eq_right hq, Bool.false_or, Bool.or_self]
    rw [← kill_update_comm D x t _ ht]
  rw [heq]
  exact h

lemma free_mask_or_old_right {F : (α → Bool) → Bool} {N E D : Finset α}
    (hd : Dep F N) (hf : Free (fun x => F (kill E x))) (hED : E ⊆ D)
    {t p q : α} (ht : t ∉ D) (hq : q ∈ D) (hp : p ∉ D)
    (hpN : p ∉ N.erase t) (z : α) (hz : z ∉ N) :
    Free (fun x => F (Function.update (kill D x) t (kill D x p || kill D x q))) := by
  simpa only [Bool.or_comm] using free_mask_or_old_left hd hf hED ht hq hp hpN z hz

def ORClass (F : (α → Bool) → Bool) (S : Finset α) : Prop :=
  ∀ a ∈ S, ∀ b ∈ S, ∀ x : α → Bool,
    F (Function.update x a true) = F (Function.update x b true)

def classRest (S : Finset α) (t p q : α) : Finset α :=
  ((S.erase t).erase p).erase q

def classSub (F : (α → Bool) → Bool) (op : Bool → Bool → Bool)
    (t p q : α) : (α → Bool) → Bool :=
  fun x => F (Function.update x t (op (x p) (x q)))

lemma classRest_mem {S : Finset α} {t p q a : α} (ha : a ∈ classRest S t p q) :
    a ∈ S ∧ a ≠ t ∧ a ≠ p ∧ a ≠ q := by
  simpa only [classRest, Finset.mem_erase, and_assoc, and_left_comm, and_comm] using ha

lemma classSub_force (F : (α → Bool) → Bool) (op : Bool → Bool → Bool)
    (t p q a : α) (x : α → Bool) (hat : a ≠ t) (hap : a ≠ p) (haq : a ≠ q) :
    classSub F op t p q (Function.update x a true) =
      F (Function.update (Function.update x t (op (x p) (x q))) a true) := by
  simp only [classSub, Function.update_of_ne hap.symm, Function.update_of_ne haq.symm]
  rw [Function.update_comm hat]

lemma orClass_survive {F : (α → Bool) → Bool} {S : Finset α}
    (hclass : ORClass F S) (op : Bool → Bool → Bool) (t p q : α) :
    ORClass (classSub F op t p q) (classRest S t p q) := by
  intro a ha b hb x
  obtain ⟨ha, hat, hap, haq⟩ := classRest_mem ha
  obtain ⟨hb, hbt, hbp, hbq⟩ := classRest_mem hb
  rw [classSub_force F op t p q a x hat hap haq,
    classSub_force F op t p q b x hbt hbp hbq]
  exact hclass a ha b hb _

lemma orClass_empty (F : (α → Bool) → Bool) : ORClass F ∅ := by
  intro a ha
  simp only [Finset.notMem_empty] at ha

lemma orClass_singleton (F : (α → Bool) → Bool) (a : α) : ORClass F {a} := by
  intro b hb c hc x
  simp only [Finset.mem_singleton] at hb hc
  subst b
  subst c
  rfl

lemma orClass_subset {F : (α → Bool) → Bool} {S T : Finset α}
    (hclass : ORClass F S) (hTS : T ⊆ S) : ORClass F T := by
  exact fun a ha b hb => hclass a (hTS ha) b (hTS hb)

lemma class_ignore {F : (α → Bool) → Bool} {N : Finset α} (hd : Dep F N)
    {a : α} (ha : a ∉ N) (x : α → Bool) (v : Bool) :
    F (Function.update x a v) = F x := by
  apply hd
  intro i hi
  have hia : i ≠ a := by
    intro h
    subst i
    exact ha hi
  exact Function.update_of_ne hia v x

lemma class_or_force_old {F : (α → Bool) → Bool} {S : Finset α}
    (hclass : ORClass F S) {t p q a : α} (ht : t ∈ S)
    (ha : a ∈ classRest S t p q) (x : α → Bool) :
    classSub F (· || ·) t p q (Function.update x a true) =
      F (Function.update x t true) := by
  obtain ⟨ha, hat, hap, haq⟩ := classRest_mem ha
  rw [classSub_force F (· || ·) t p q a x hat hap haq, hclass a ha t ht]
  rw [Function.update_idem]

lemma class_or_force_left {F : (α → Bool) → Bool} {N : Finset α}
    (hd : Dep F N) {t p q : α} (hpt : p ≠ t) (hp : p ∉ N) (x : α → Bool) :
    classSub F (· || ·) t p q (Function.update x p true) =
      F (Function.update x t true) := by
  simp only [classSub, Function.update_self, Bool.true_or]
  rw [Function.update_comm hpt]
  exact class_ignore hd hp _ true

lemma class_or_force_right {F : (α → Bool) → Bool} {N : Finset α}
    (hd : Dep F N) {t p q : α} (hqt : q ≠ t) (hq : q ∉ N) (x : α → Bool) :
    classSub F (· || ·) t p q (Function.update x q true) =
      F (Function.update x t true) := by
  simp only [classSub, Function.update_self, Bool.or_true]
  rw [Function.update_comm hqt]
  exact class_ignore hd hq _ true

lemma orClass_or_inherit {F : (α → Bool) → Bool} {N S B : Finset α}
    (hd : Dep F N) (hclass : ORClass F S) {t p q : α} (ht : t ∈ S)
    (hB : ∀ b ∈ B, (b = p ∨ b = q) ∧ b ≠ t ∧ b ∉ N) :
    ORClass (classSub F (· || ·) t p q) (classRest S t p q ∪ B) := by
  have hforce : ∀ a ∈ classRest S t p q ∪ B, ∀ x : α → Bool,
      classSub F (· || ·) t p q (Function.update x a true) =
        F (Function.update x t true) := by
    intro a ha x
    rcases Finset.mem_union.mp ha with ha | ha
    · exact class_or_force_old hclass ht ha x
    · obtain ⟨ha, hat, haN⟩ := hB a ha
      rcases ha with rfl | rfl
      · exact class_or_force_left hd hat haN x
      · exact class_or_force_right hd hat haN x
  intro a ha b hb x
  exact (hforce a ha x).trans (hforce b hb x).symm

def classFresh (rest : Finset α) (p q : α) : Finset α := {p, q} \ rest

def classReused (rest : Finset α) (p q : α) : Finset α := {p, q} ∩ rest

def classOp (isOr : Bool) (x y : Bool) : Bool := if isOr then x || y else x && y

def classNext (isOr : Bool) (rest : Finset α) (t p q : α) (S : Finset α) : Finset α :=
  classRest S t p q ∪ if isOr = true ∧ t ∈ S then classFresh rest p q else ∅

def classFamilyNext (isOr : Bool) (rest : Finset α) (t p q : α)
    (K : Finset (Finset α)) : Finset (Finset α) :=
  K.image (classNext isOr rest t p q) ∪ (classReused rest p q).image (fun a => {a})

def classUnion (K : Finset (Finset α)) : Finset α := K.biUnion id

lemma classNext_closed {F : (α → Bool) → Bool} {rest S : Finset α} {t p q : α}
    (hd : Dep F (insert t rest)) (hclass : ORClass F S)
    (htp : t ≠ p) (htq : t ≠ q) (isOr : Bool) :
    ORClass (classSub F (classOp isOr) t p q) (classNext isOr rest t p q S) := by
  by_cases h : isOr = true ∧ t ∈ S
  · rcases h with ⟨rfl, ht⟩
    simp only [classNext, ht, and_self, ite_true]
    apply orClass_or_inherit hd hclass ht
    intro b hb
    simp only [classFresh, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton] at hb
    have hbt : b ≠ t := by
      rcases hb.1 with rfl | rfl
      · exact htp.symm
      · exact htq.symm
    exact ⟨hb.1, hbt, by simp [hbt, hb.2]⟩
  · simp only [classNext, h, ite_false, Finset.union_empty]
    exact orClass_survive hclass (classOp isOr) t p q

lemma classFamilyNext_closed {F : (α → Bool) → Bool} {rest : Finset α} {t p q : α}
    {K : Finset (Finset α)} (hd : Dep F (insert t rest))
    (hK : ∀ S ∈ K, ORClass F S) (htp : t ≠ p) (htq : t ≠ q) (isOr : Bool) :
    ∀ S ∈ classFamilyNext isOr rest t p q K,
      ORClass (classSub F (classOp isOr) t p q) S := by
  intro S hS
  rcases Finset.mem_union.mp hS with hS | hS
  · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
    exact classNext_closed hd (hK T hT) htp htq isOr
  · obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp hS
    exact orClass_singleton _ a

lemma classNext_subset {rest S : Finset α} {t p q : α}
    (hS : S ⊆ insert t rest) (isOr : Bool) :
    classNext isOr rest t p q S ⊆ insert p (insert q rest) := by
  intro a ha
  rcases Finset.mem_union.mp ha with ha | ha
  · obtain ⟨ha, hat, _, _⟩ := classRest_mem ha
    have har : a ∈ rest := (Finset.mem_insert.mp (hS ha)).resolve_left hat
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem har)
  · by_cases h : isOr = true ∧ t ∈ S
    · rw [ite_eq_left h] at ha
      simp only [classFresh, Finset.mem_sdiff, Finset.mem_insert,
        Finset.mem_singleton] at ha
      rcases ha.1 with rfl | rfl <;> simp
    · simp only [h, ite_false, Finset.notMem_empty] at ha

lemma classFamilyNext_subset {rest : Finset α} {t p q : α} {K : Finset (Finset α)}
    (hK : ∀ S ∈ K, S ⊆ insert t rest) (isOr : Bool) :
    ∀ S ∈ classFamilyNext isOr rest t p q K, S ⊆ insert p (insert q rest) := by
  intro S hS
  rcases Finset.mem_union.mp hS with hS | hS
  · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
    exact classNext_subset (hK T hT) isOr
  · obtain ⟨a, ha, rfl⟩ := Finset.mem_image.mp hS
    intro b hb
    have hba := Finset.mem_singleton.mp hb
    subst b
    have har : a ∈ rest := (Finset.mem_inter.mp ha).2
    exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem har)

lemma classFamilyNext_card (isOr : Bool) (rest : Finset α) (t p q : α)
    (K : Finset (Finset α)) :
    (classFamilyNext isOr rest t p q K).card ≤ K.card + (classReused rest p q).card := by
  exact (Finset.card_union_le _ _).trans
    (Nat.add_le_add (Finset.card_image_le) (Finset.card_image_le))

lemma classUnion_mem (K : Finset (Finset α)) (a : α) :
    a ∈ classUnion K ↔ ∃ S ∈ K, a ∈ S := by
  simp only [classUnion, Finset.mem_biUnion, id_eq]

lemma classFamilyUnion_mem (isOr : Bool) (rest : Finset α) (t p q a : α)
    (K : Finset (Finset α)) :
    a ∈ classUnion (classFamilyNext isOr rest t p q K) ↔
      (∃ S ∈ K, a ∈ classNext isOr rest t p q S) ∨ a ∈ classReused rest p q := by
  rw [classUnion_mem]
  constructor
  · rintro ⟨S, hS, ha⟩
    rcases Finset.mem_union.mp hS with hS | hS
    · obtain ⟨T, hT, rfl⟩ := Finset.mem_image.mp hS
      exact Or.inl ⟨T, hT, ha⟩
    · obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hS
      have hab := Finset.mem_singleton.mp ha
      subst a
      exact Or.inr hb
  · rintro (⟨S, hS, ha⟩ | ha)
    · exact ⟨_, Finset.mem_union_left _ (Finset.mem_image.mpr ⟨S, hS, rfl⟩), ha⟩
    · exact ⟨{a}, Finset.mem_union_right _ (Finset.mem_image.mpr ⟨a, ha, rfl⟩),
        Finset.mem_singleton_self _⟩

lemma classFamilyNext_union (isOr : Bool) (rest : Finset α) (t p q : α)
    (K : Finset (Finset α)) (hK : ∀ S ∈ K, S ⊆ insert t rest) :
    classUnion (classFamilyNext isOr rest t p q K) =
      ((classUnion K).erase t ∪ classReused rest p q) ∪
        if isOr = true ∧ t ∈ classUnion K then classFresh rest p q else ∅ := by
  ext a
  rw [classFamilyUnion_mem]
  constructor
  · rintro (⟨S, hS, ha⟩ | ha)
    · rcases Finset.mem_union.mp ha with ha | ha
      · obtain ⟨ha, hat, _, _⟩ := classRest_mem ha
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_erase.mpr ⟨hat, (classUnion_mem K a).mpr ⟨S, hS, ha⟩⟩))
      · by_cases h : isOr = true ∧ t ∈ S
        · have h' : isOr = true ∧ t ∈ classUnion K :=
            ⟨h.1, (classUnion_mem K t).mpr ⟨S, hS, h.2⟩⟩
          apply Finset.mem_union_right
          rw [ite_eq_left h']
          rwa [ite_eq_left h] at ha
        · simp only [h, ite_false, Finset.notMem_empty] at ha
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ ha)
  · intro ha
    rcases Finset.mem_union.mp ha with ha | ha
    · rcases Finset.mem_union.mp ha with ha | ha
      · obtain ⟨hat, ha⟩ := Finset.mem_erase.mp ha
        obtain ⟨S, hS, haS⟩ := (classUnion_mem K a).mp ha
        by_cases hapq : a = p ∨ a = q
        · apply Or.inr
          have har : a ∈ rest := (Finset.mem_insert.mp (hK S hS haS)).resolve_left hat
          exact Finset.mem_inter.mpr ⟨by simpa only [Finset.mem_insert,
            Finset.mem_singleton] using hapq, har⟩
        · apply Or.inl
          refine ⟨S, hS, Finset.mem_union_left _ ?_⟩
          have hap : a ≠ p := fun h => hapq (Or.inl h)
          have haq : a ≠ q := fun h => hapq (Or.inr h)
          simp only [classRest, Finset.mem_erase]
          exact ⟨haq, hap, hat, haS⟩
      · exact Or.inr ha
    · by_cases h : isOr = true ∧ t ∈ classUnion K
      · rw [ite_eq_left h] at ha
        obtain ⟨S, hS, htS⟩ := (classUnion_mem K t).mp h.2
        apply Or.inl
        refine ⟨S, hS, Finset.mem_union_right _ ?_⟩
        rw [ite_eq_left ⟨h.1, htS⟩]
        exact ha
      · simp only [h, ite_false, Finset.notMem_empty] at ha

lemma class_partition_card (rest : Finset α) (p q : α) (hpq : p ≠ q) :
    (classFresh rest p q).card + (classReused rest p q).card = 2 := by
  simpa [classFresh, classReused, hpq] using
    Finset.card_sdiff_add_card_inter ({p, q} : Finset α) rest

lemma class_frontier_card (rest : Finset α) (p q : α) :
    (insert p (insert q rest)).card = rest.card + (classFresh rest p q).card := by
  simpa [classFresh, Nat.add_comm] using
    (Finset.card_sdiff_add_card ({p, q} : Finset α) rest).symm

lemma classFamilyNext_growth (isOr : Bool) (rest : Finset α) (t p q : α)
    (K : Finset (Finset α)) (ht : t ∉ rest) (hpq : p ≠ q) :
    (insert p (insert q rest)).card + (classFamilyNext isOr rest t p q K).card ≤
      (insert t rest).card + K.card + 1 := by
  have hfamily := classFamilyNext_card isOr rest t p q K
  have hparts := class_partition_card rest p q hpq
  have hfront := class_frontier_card rest p q
  rw [Finset.card_insert_of_notMem ht]
  omega

def classPair (a b : α) : α → Bool := fun x => decide (x = a) || decide (x = b)

lemma classPair_update (a b : α) :
    classPair a b = Function.update (fun x => decide (x = b)) a true := by
  funext x
  by_cases h : x = a
  · subst x
    simp [classPair]
  · simp [classPair, h]

lemma classPair_comm (a b : α) : classPair a b = classPair b a := by
  funext x
  exact Bool.or_comm _ _

lemma orClass_card_le_two {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : (α → Bool) → Bool) (A : ι → κ → Bool) (left : ι → α) (right : κ → α)
    (hpair : ∀ u v, F (classPair (left u) (right v)) = A u v)
    (hrows : Function.Injective A)
    (hcols : Function.Injective (fun v => fun u => A u v))
    (S : Finset α) (hclass : ORClass F S)
    (hsub : S ⊆ Finset.univ.image left ∪ Finset.univ.image right) : S.card ≤ 2 := by
  classical
  let L := Finset.univ.image left
  let R := Finset.univ.image right
  have hL : (S ∩ L).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨haS, haL⟩ := Finset.mem_inter.mp ha
    obtain ⟨hbS, hbL⟩ := Finset.mem_inter.mp hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp haL
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hbL
    apply congrArg left
    apply hrows
    funext w
    rw [← hpair u w, ← hpair v w, classPair_update, classPair_update]
    exact hclass _ haS _ hbS _
  have hR : (S ∩ R).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    obtain ⟨haS, haR⟩ := Finset.mem_inter.mp ha
    obtain ⟨hbS, hbR⟩ := Finset.mem_inter.mp hb
    obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp haR
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hbR
    apply congrArg right
    apply hcols
    funext w
    change A w u = A w v
    rw [← hpair w u, ← hpair w v, classPair_comm (left w) (right u),
      classPair_comm (left w) (right v), classPair_update, classPair_update]
    exact hclass _ haS _ hbS _
  have hcover : S = (S ∩ L) ∪ (S ∩ R) := by
    ext a
    constructor
    · intro ha
      rcases Finset.mem_union.mp (hsub ha) with hl | hr
      · exact Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨ha, hl⟩)
      · exact Finset.mem_union_right _ (Finset.mem_inter.mpr ⟨ha, hr⟩)
    · intro ha
      rcases Finset.mem_union.mp ha with hl | hr
      · exact (Finset.mem_inter.mp hl).1
      · exact (Finset.mem_inter.mp hr).1
  calc
    S.card = ((S ∩ L) ∪ (S ∩ R)).card := congrArg Finset.card hcover
    _ ≤ (S ∩ L).card + (S ∩ R).card := Finset.card_union_le _ _
    _ ≤ 2 := by omega

lemma orClass_valid_card_le_two {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : (α → Bool) → Bool) (A : ι → κ → Bool) (left : ι → α) (right : κ → α)
    (hpair : ∀ u v, F (classPair (left u) (right v)) = A u v)
    (hrows : Function.Injective A)
    (hcols : Function.Injective (fun v => fun u => A u v))
    (S : Finset α) (hclass : ORClass F S) :
    (S ∩ (Finset.univ.image left ∪ Finset.univ.image right)).card ≤ 2 := by
  apply orClass_card_le_two F A left right hpair hrows hcols
  · exact fun a ha b hb => hclass a (Finset.mem_inter.mp ha).1 b (Finset.mem_inter.mp hb).1
  · exact fun a ha => (Finset.mem_inter.mp ha).2

lemma orClasses_valid_union_card {ι κ : Type*} [Fintype ι] [Fintype κ]
    (F : (α → Bool) → Bool) (A : ι → κ → Bool) (left : ι → α) (right : κ → α)
    (hpair : ∀ u v, F (classPair (left u) (right v)) = A u v)
    (hrows : Function.Injective A)
    (hcols : Function.Injective (fun v => fun u => A u v))
    (K : Finset (Finset α)) (hK : ∀ S ∈ K, ORClass F S) :
    ((K.biUnion id) ∩ (Finset.univ.image left ∪ Finset.univ.image right)).card ≤ 2 * K.card := by
  classical
  let V := Finset.univ.image left ∪ Finset.univ.image right
  have heq : (K.biUnion id) ∩ V = K.biUnion (fun S => S ∩ V) := by
    ext a
    simp only [Finset.mem_inter, Finset.mem_biUnion, id_eq]
    constructor
    · rintro ⟨⟨S, hS, ha⟩, hv⟩
      exact ⟨S, hS, ha, hv⟩
    · rintro ⟨S, hS, ha, hv⟩
      exact ⟨⟨S, hS, ha⟩, hv⟩
  change ((K.biUnion id) ∩ V).card ≤ _
  rw [heq]
  calc
    (K.biUnion (fun S => S ∩ V)).card ≤ ∑ S ∈ K, (S ∩ V).card := Finset.card_biUnion_le
    _ ≤ ∑ _S ∈ K, 2 := Finset.sum_le_sum fun S hS =>
      orClass_valid_card_le_two F A left right hpair hrows hcols S (hK S hS)
    _ = 2 * K.card := by simp [Nat.mul_comm]

def cycle33 (a b : Fin 33) : Bool :=
  decide (∃ i : Fin 11,
    ((a.val = i.val ∨ a.val = 11 + i.val) ∧
      (b.val = (i.val + 1) % 11 ∨ b.val = 22 + i.val)) ∨
    ((b.val = i.val ∨ b.val = 11 + i.val) ∧
      (a.val = (i.val + 1) % 11 ∨ a.val = 22 + i.val)))

def packedP4A (i : Fin 14) : Fin 33 :=
  ⟨([1, 2, 4, 6, 7, 9, 10, 11, 24, 14, 16, 29, 19, 32] : List Nat)[i.val]! % 33,
    Nat.mod_lt _ (by decide)⟩

def packedP4B (i : Fin 14) : Fin 33 :=
  ⟨([22, 13, 25, 27, 18, 30, 21, 23, 12, 26, 28, 17, 31, 20] : List Nat)[i.val]! % 33,
    Nat.mod_lt _ (by decide)⟩

def packedP4C (i : Fin 14) : Fin 33 :=
  ⟨([11, 24, 14, 16, 29, 19, 32, 1, 2, 4, 6, 7, 9, 10] : List Nat)[i.val]! % 33,
    Nat.mod_lt _ (by decide)⟩

def packedP4D (i : Fin 14) : Fin 33 :=
  ⟨([23, 12, 26, 28, 17, 31, 20, 22, 13, 25, 27, 18, 30, 21] : List Nat)[i.val]! % 33,
    Nat.mod_lt _ (by decide)⟩

def packedP4Wire (i : Fin 14) (j : Fin 4) : Fin 66 :=
  if j.val = 0 then ⟨(packedP4A i).val, by omega⟩
  else if j.val = 1 then ⟨(packedP4B i).val, by omega⟩
  else if j.val = 2 then ⟨33 + (packedP4C i).val, by omega⟩
  else ⟨33 + (packedP4D i).val, by omega⟩

lemma packedP4_edges : ∀ i,
    cycle33 (packedP4A i) (packedP4C i) = true ∧
    cycle33 (packedP4A i) (packedP4D i) = true ∧
    cycle33 (packedP4B i) (packedP4C i) = true ∧
    cycle33 (packedP4B i) (packedP4D i) = false := by
  decide +kernel

set_option maxRecDepth 100000 in
set_option maxHeartbeats 10000000 in
lemma packedP4_disjoint : Function.Injective
    (fun p : Fin 14 × Fin 4 => packedP4Wire p.1 p.2) := by
  decide +kernel

lemma packedP4_hitting_size (S : Finset (Fin 66))
    (h : ∀ i : Fin 14, ∃ j : Fin 4, packedP4Wire i j ∈ S) : 14 ≤ S.card := by
  classical
  choose j hj using h
  let f : Fin 14 → {v // v ∈ S} := fun i => ⟨packedP4Wire i (j i), hj i⟩
  have hf : Function.Injective f := by
    intro i k heq
    have hw : packedP4Wire i (j i) = packedP4Wire k (j k) := congrArg Subtype.val heq
    exact congrArg Prod.fst (@packedP4_disjoint (i, j i) (k, j k) hw)
  have hc := Fintype.card_le_of_injective f hf
  simpa using hc

def zeroWires (S : Finset α) (x : α → Bool) : α → Bool :=
  fun i => if i ∈ S then false else x i

lemma zeroWires_on (S : Finset α) {p q : α} (hp : p ∉ S) (hq : q ∉ S) :
    zeroWires S (on p q) = on p q := by
  funext i
  by_cases hi : i ∈ S
  · have hip : i ≠ p := fun h => hp (h ▸ hi)
    have hiq : i ≠ q := fun h => hq (h ▸ hi)
    simp [zeroWires, hi, on, hip, hiq]
  · simp [zeroWires, hi]

def leftWire (a : Fin 33) : Fin 66 := ⟨a.val, by omega⟩
def rightWire (b : Fin 33) : Fin 66 := ⟨33 + b.val, by omega⟩

omit [DecidableEq α] in
lemma packedP4_hitting_size_generic (wire : Fin 66 → α) (hinj : Function.Injective wire)
    (S : Finset α)
    (h : ∀ i : Fin 14, ∃ j : Fin 4, wire (packedP4Wire i j) ∈ S) : 14 ≤ S.card := by
  classical
  choose j hj using h
  let f : Fin 14 → {v // v ∈ S} := fun i => ⟨wire (packedP4Wire i (j i)), hj i⟩
  have hf : Function.Injective f := by
    intro i k heq
    have hw : packedP4Wire i (j i) = packedP4Wire k (j k) :=
      hinj (congrArg Subtype.val heq)
    exact congrArg Prod.fst (@packedP4_disjoint (i, j i) (k, j k) hw)
  have hc := Fintype.card_le_of_injective f hf
  simpa using hc

lemma cycle33_free_deletion_lower_generic
    (wire : Fin 66 → α) (hinj : Function.Injective wire)
    (F : (α → Bool) → Bool)
    (hrep : ∀ a b : Fin 33, F (on (wire (leftWire a)) (wire (rightWire b))) = cycle33 a b)
    (hsingle : ∀ w : Fin 66, F (on (wire w) (wire w)) = false)
    (S : Finset α)
    (hfree : Free (fun x => F (zeroWires S x))) : 14 ≤ S.card := by
  apply packedP4_hitting_size_generic wire hinj S
  intro i
  by_contra h
  have hn : ∀ j : Fin 4, wire (packedP4Wire i j) ∉ S := by simpa using h
  have hbad := hfree.2 (wire (packedP4Wire i 0)) (wire (packedP4Wire i 1))
    (wire (packedP4Wire i 2)) (wire (packedP4Wire i 3))
  simp only [zeroWires_on S (hn 0) (hn 0), zeroWires_on S (hn 1) (hn 1),
    zeroWires_on S (hn 2) (hn 2), zeroWires_on S (hn 3) (hn 3),
    zeroWires_on S (hn 0) (hn 2), zeroWires_on S (hn 0) (hn 3),
    zeroWires_on S (hn 1) (hn 2), zeroWires_on S (hn 1) (hn 3)] at hbad
  obtain ⟨heac, head, hebc, hebd⟩ := packedP4_edges i
  have he1 : F (on (wire (packedP4Wire i 0)) (wire (packedP4Wire i 2))) = true := by
    simpa [packedP4Wire, leftWire, rightWire, heac] using hrep (packedP4A i) (packedP4C i)
  have he2 : F (on (wire (packedP4Wire i 0)) (wire (packedP4Wire i 3))) = true := by
    simpa [packedP4Wire, leftWire, rightWire, head] using hrep (packedP4A i) (packedP4D i)
  have he3 : F (on (wire (packedP4Wire i 1)) (wire (packedP4Wire i 2))) = true := by
    simpa [packedP4Wire, leftWire, rightWire, hebc] using hrep (packedP4B i) (packedP4C i)
  have he4 : F (on (wire (packedP4Wire i 1)) (wire (packedP4Wire i 3))) = false := by
    simpa [packedP4Wire, leftWire, rightWire, hebd] using hrep (packedP4B i) (packedP4D i)
  have hf := hbad (hsingle _) (hsingle _) (hsingle _) (hsingle _) he1 he2 he3
  rw [he4] at hf
  exact Bool.noConfusion hf

end Structural

namespace FullCompile
open scoped Classical
section Budget
variable {α : Type}

noncomputable def oldCount (a b : α) (rest : Finset α) : Nat :=
  (if a ∈ rest then 1 else 0) + (if b ∈ rest then 1 else 0)

lemma card_step {a b z : α} {rest : Finset α} (hab : a ≠ b)
    (hz : z ∉ insert a (insert b rest)) :
    (insert a (insert b rest)).card + oldCount a b rest = (insert z rest).card + 1 := by
  have hzr : z ∉ rest := fun h => hz (by simp [h])
  rw [Finset.card_insert_of_notMem hzr]
  by_cases ha : a ∈ rest <;> by_cases hb : b ∈ rest
  · simp [oldCount,ha,hb]
  · rw [Finset.insert_eq_of_mem (Finset.mem_insert_of_mem ha), Finset.card_insert_of_notMem hb]
    simp [oldCount,ha,hb]
  · rw [Finset.insert_eq_of_mem hb, Finset.card_insert_of_notMem ha]
    simp [oldCount,ha,hb]
  · rw [Finset.card_insert_of_notMem (by simp [hab,ha]), Finset.card_insert_of_notMem hb]
    simp [oldCount,ha,hb]

lemma live_budget_induction {ops : α → α → Finset α} {goal : α}
    (R : α → Prop) (Good : Finset α → Nat → Prop)
    (hops : ∀ a b z, R a → R b → z ∈ ops a b → R z)
    (hbase : R goal → Good {goal} 0)
    (hstep : ∀ a b z rest r, a ≠ b → z ∉ insert a (insert b rest) → z ∈ ops a b →
      (∀ w ∈ insert a (insert b rest), R w) → Good (insert z rest) r →
      Good (insert a (insert b rest)) (r + oldCount a b rest))
    {k : Nat} {S : Finset α} (hR : ∀ w ∈ S, R w) (hl : live ops goal k S) :
    ∃ r, Good S r ∧ S.card + r ≤ k + 1 := by
  induction k generalizing S with
  | zero =>
    change S = {goal} at hl
    subst S
    exact ⟨0,hbase (hR goal (by simp)),by simp⟩
  | succ k ih =>
    rcases hl with hskip | ⟨a,ha,b,hb,hab,z,hz,hout,rest,hS,htail⟩
    · obtain ⟨r,hgood,hbound⟩ := ih hR hskip
      exact ⟨r,hgood,by omega⟩
    · subst S
      have hr : ∀ w ∈ insert z rest, R w := by
        intro w hw
        rcases Finset.mem_insert.mp hw with rfl | hw
        · exact hops a b w (hR a (by simp)) (hR b (by simp)) hz
        · exact hR w (by simp [hw])
      obtain ⟨r,hgood,hbound⟩ := ih hr htail
      refine ⟨r + oldCount a b rest,hstep a b z rest r hab hout hz hR hgood,?_⟩
      have hc := card_step hab hout
      omega

end Budget

end FullCompile
namespace Structural

universe u
variable {α : Type u} [DecidableEq α]

def stepMask (isOr : Bool) (rest E : Finset α) (t p q : α) : Finset α :=
  (E.erase t ∪ ({p, q} ∩ rest)) ∪
    (if isOr = true ∧ t ∈ E then ({p, q} \ rest) else ∅)

lemma free_step {F : (α → Bool) → Bool} {rest E : Finset α} {t p q : α}
    (hd : Dep F (insert t rest)) (hf : Free (fun x => F (kill E x)))
    (hEN : E ⊆ insert t rest) (ht : t ∉ rest)
    (hpq : p ≠ q) (htp : t ≠ p) (htq : t ≠ q)
    (isOr : Bool) (z : α) (hz : z ∉ insert t rest) :
    Free (fun x => F (Function.update (kill (stepMask isOr rest E t p q) x) t
      (if isOr then
        kill (stepMask isOr rest E t p q) x p || kill (stepMask isOr rest E t p q) x q
       else
        kill (stepMask isOr rest E t p q) x p && kill (stepMask isOr rest E t p q) x q))) := by
  have hN : (insert t rest).erase t = rest := by simp [ht]
  have htN : t ∈ insert t rest := Finset.mem_insert_self _ _
  have hErase : E.erase t ⊆ rest := by
    intro a ha
    have haN := hEN (Finset.mem_erase.mp ha).2
    rcases Finset.mem_insert.mp haN with hat | har
    · exact False.elim ((Finset.mem_erase.mp ha).1 hat)
    · exact har
  have hED : ∀ b : Bool, E ⊆ insert t (stepMask b rest E t p q) := by
    intro b a ha
    by_cases hat : a = t
    · simp [hat]
    · exact Finset.mem_insert_of_mem (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hat, ha⟩)))
  have hpOld : ∀ b : Bool, p ∈ rest → p ∈ stepMask b rest E t p q := by
    intro b hp
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_inter.mpr ⟨by simp, hp⟩))
  have hqOld : ∀ b : Bool, q ∈ rest → q ∈ stepMask b rest E t p q := by
    intro b hq
    exact Finset.mem_union_left _ (Finset.mem_union_right _
      (Finset.mem_inter.mpr ⟨by simp, hq⟩))
  have hpFreshE : p ∉ rest → p ∉ E := by
    intro hp hpe
    rcases Finset.mem_insert.mp (hEN hpe) with hpt | hpr
    · exact htp hpt.symm
    · exact hp hpr
  have hqFreshE : q ∉ rest → q ∉ E := by
    intro hq hqe
    rcases Finset.mem_insert.mp (hEN hqe) with hqt | hqr
    · exact htq hqt.symm
    · exact hq hqr
  cases isOr with
  | false =>
    change Free (fun x => F (Function.update (kill (stepMask false rest E t p q) x) t
      (kill (stepMask false rest E t p q) x p && kill (stepMask false rest E t p q) x q)))
    by_cases hp : p ∈ rest
    · apply free_mask_sub_zero hf Bool.and t p q (hED false)
      intro x
      simp [kill, hpOld false hp]
    · by_cases hq : q ∈ rest
      · apply free_mask_sub_zero hf Bool.and t p q (hED false)
        intro x
        simp [kill, hqOld false hq]
      · have hD : stepMask false rest E t p q = E.erase t := by
          simp [stepMask, hp, hq]
        rw [hD]
        exact free_mask_and_fresh hd hf htN hpq
          (fun h => hp (hErase h)) (fun h => hq (hErase h))
          (by simpa only [hN] using hp) (by simpa only [hN] using hq) z hz
  | true =>
    change Free (fun x => F (Function.update (kill (stepMask true rest E t p q) x) t
      (kill (stepMask true rest E t p q) x p || kill (stepMask true rest E t p q) x q)))
    by_cases hte : t ∈ E
    · have hpD : p ∈ stepMask true rest E t p q := by
        by_cases hp : p ∈ rest
        · exact hpOld true hp
        · simp [stepMask, hte, hp]
      have hqD : q ∈ stepMask true rest E t p q := by
        by_cases hq : q ∈ rest
        · exact hqOld true hq
        · simp [stepMask, hte]
      apply free_mask_sub_zero hf Bool.or t p q (hED true)
      intro x
      simp [kill, hpD, hqD]
    · have hES : E ⊆ stepMask true rest E t p q := by
        intro a ha
        exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_erase.mpr ⟨fun hat => hte (hat ▸ ha), ha⟩))
      have htD : t ∉ stepMask true rest E t p q := by
        simp [stepMask, hte, ht, htp, htq]
      by_cases hp : p ∈ rest
      · by_cases hq : q ∈ rest
        · apply free_mask_sub_zero hf Bool.or t p q (hED true)
          intro x
          simp [kill, hpOld true hp, hqOld true hq]
        · have hqD : q ∉ stepMask true rest E t p q := by
            simp [stepMask, hte, hqFreshE hq, hq]
          exact free_mask_or_old_left hd hf hES htD (hpOld true hp) hqD (by simpa only [hN] using hq) z hz
      · by_cases hq : q ∈ rest
        · have hpD : p ∉ stepMask true rest E t p q := by
            simp [stepMask, hte, hpFreshE hp, hp]
          exact free_mask_or_old_right hd hf hES htD (hqOld true hq) hpD (by simpa only [hN] using hp) z hz
        · have hD : stepMask true rest E t p q = E := by
            simp [stepMask, hte, hp, hq]
          rw [hD]
          exact free_mask_or_fresh hd hf hte (hpFreshE hp) (hqFreshE hq) (by simpa only [hN] using hp) (by simpa only [hN] using hq) z hz

end Structural

namespace Backward
open FullCompile Structural
open scoped Classical
variable {ι : Type}

def Good (goal : W ι) (N : Finset (W ι)) (r : Nat) : Prop :=
  ∃ (F : (W ι → Bool) → Bool) (K : Finset (Finset (W ι))),
    Structural.Dep F N ∧ (∀ S ∈ K, S ⊆ N) ∧ (∀ S ∈ K, ORClass F S) ∧
    Structural.Free (fun x => F (Structural.kill (classUnion K) x)) ∧
    agrees goal F ∧ K.card ≤ r

lemma dep_subst {F : (W ι → Bool) → Bool} {rest : Finset (W ι)} {z a b : W ι}
    (hd : Structural.Dep F (insert z rest)) (isOr : Bool) :
    Structural.Dep (classSub F (classOp isOr) z a b) (insert a (insert b rest)) := by
  intro x y hxy
  apply hd
  intro i hi
  by_cases hiz : i = z
  · subst i
    simp only [Function.update_self]
    rw [hxy a (by simp), hxy b (by simp)]
  · rw [Function.update_of_ne hiz, Function.update_of_ne hiz]
    exact hxy i (by simp [(Finset.mem_insert.mp hi).resolve_left hiz])

lemma good_base (goal : W ι) : Good goal {goal} 0 := by
  refine ⟨(fun x => x goal), ∅, ?_, by simp, by simp, ?_, ?_, by simp⟩
  · intro x y hxy
    exact hxy goal (by simp)
  · change Structural.Free (fun x : W ι → Bool => x goal)
    refine ⟨rfl,?_⟩
    intro a b c d ha hb hc hd hac had hbc
    have hga : goal ≠ a := by simpa [Structural.on] using ha
    have hgc : goal ≠ c := by simpa [Structural.on] using hc
    have hh : goal = a ∨ goal = c := by simpa [Structural.on] using hac
    exact False.elim (hh.elim hga hgc)
  · intro x
    rfl

lemma good_step
    (freeStep : ∀ (F : (W ι → Bool) → Bool) (rest : Finset (W ι)) (z a b : W ι)
      (K : Finset (Finset (W ι))) (isOr : Bool),
      Structural.Dep F (insert z rest) → (∀ S ∈ K, S ⊆ insert z rest) →
      Structural.Free (fun x => F (Structural.kill (classUnion K) x)) →
      z ≠ a → z ≠ b → a ≠ b → z ∉ rest → zero ∉ insert z rest →
      Structural.Free (fun x => (classSub F (classOp isOr) z a b)
        (Structural.kill (classUnion (classFamilyNext isOr rest z a b K)) x)))
    {goal : W ι} {x0 x1 : ι} {a b z : W ι} {rest : Finset (W ι)} {r : Nat}
    (hab : a ≠ b) (hout : z ∉ insert a (insert b rest)) (hop : z ∈ basicOps a b)
    (hR : ∀ w ∈ insert a (insert b rest), Regular x0 x1 w)
    (hg : Good goal (insert z rest) r) :
    Good goal (insert a (insert b rest)) (r + oldCount a b rest) := by
  obtain ⟨F,K,hd,hsub,hclasses,hfree,hagree,hcard⟩ := hg
  have hza : z ≠ a := fun h => hout (by simp [h])
  have hzb : z ≠ b := fun h => hout (by simp [h])
  have hzr : z ∉ rest := fun h => hout (by simp [h])
  have hzero : zero ∉ insert z rest := by
    intro h
    have hr : Regular x0 x1 zero := by
      rcases Finset.mem_insert.mp h with hz | hr
      · rw [hz]
        exact ops_regular (hR a (by simp)) (hR b (by simp)) hop
      · exact hR zero (by simp [hr])
    exact regular_not_zero hr rfl
  have main (isOr : Bool) (he : z = if isOr then bor a b else band a b) :
      Good goal (insert a (insert b rest)) (r + oldCount a b rest) := by
    let F' := classSub F (classOp isOr) z a b
    let K' := classFamilyNext isOr rest z a b K
    refine ⟨F',K',dep_subst hd isOr,classFamilyNext_subset hsub isOr,
      classFamilyNext_closed hd hclasses hza hzb isOr,freeStep F rest z a b K isOr hd hsub hfree hza hzb hab hzr hzero,?_,?_⟩
    · intro x
      change F (Function.update (fun f => f x) z (classOp isOr (a x) (b x))) = goal x
      have hv : classOp isOr (a x) (b x) = z x := by
        rw [he]
        cases isOr <;> rfl
      rw [hv,Function.update_eq_self]
      exact hagree x
    · have hbound := classFamilyNext_growth isOr rest z a b K hzr hab
      have hfront := card_step hab hout
      dsimp [K']
      omega
  simp only [basicOps,Finset.mem_insert,Finset.mem_singleton] at hop
  rcases hop with hz | hz
  · exact main false hz
  · exact main true hz

lemma backward_with_step
    (freeStep : ∀ (F : (W ι → Bool) → Bool) (rest : Finset (W ι)) (z a b : W ι)
      (K : Finset (Finset (W ι))) (isOr : Bool),
      Structural.Dep F (insert z rest) → (∀ S ∈ K, S ⊆ insert z rest) →
      Structural.Free (fun x => F (Structural.kill (classUnion K) x)) →
      z ≠ a → z ≠ b → a ≠ b → z ∉ rest → zero ∉ insert z rest →
      Structural.Free (fun x => (classSub F (classOp isOr) z a b)
        (Structural.kill (classUnion (classFamilyNext isOr rest z a b K)) x)))
    {goal : W ι} {x0 x1 : ι} {k : Nat} {N : Finset (W ι)}
    (hR : ∀ w ∈ N, Regular x0 x1 w) (hl : live basicOps goal k N) :
    ∃ (F : (W ι → Bool) → Bool) (K : Finset (Finset (W ι))),
      Structural.Dep F N ∧ (∀ S ∈ K, S ⊆ N) ∧ (∀ S ∈ K, ORClass F S) ∧
      Structural.Free (fun x => F (Structural.kill (classUnion K) x)) ∧
      agrees goal F ∧ N.card + K.card ≤ k+1 := by
  obtain ⟨r,⟨F,K,hd,hsub,hclasses,hfree,hagree,hcard⟩,hbudget⟩ :=
    live_budget_induction (Regular x0 x1) (Good goal)
      (fun a b z ha hb hz => ops_regular ha hb hz)
      (fun _ => good_base goal)
      (fun a b z rest r hab hout hop hR hg => good_step freeStep hab hout hop hR hg) hR hl
  exact ⟨F,K,hd,hsub,hclasses,hfree,hagree,by omega⟩

lemma family_free_step (F : (W ι → Bool) → Bool) (rest : Finset (W ι)) (z a b : W ι)
    (K : Finset (Finset (W ι))) (isOr : Bool)
    (hd : Structural.Dep F (insert z rest)) (hsub : ∀ S ∈ K, S ⊆ insert z rest)
    (hfree : Structural.Free (fun x => F (Structural.kill (classUnion K) x)))
    (hza : z ≠ a) (hzb : z ≠ b) (hab : a ≠ b) (hzr : z ∉ rest)
    (hzero : zero ∉ insert z rest) :
    Structural.Free (fun x => (classSub F (classOp isOr) z a b)
      (Structural.kill (classUnion (classFamilyNext isOr rest z a b K)) x)) := by
  have hEN : classUnion K ⊆ insert z rest := by
    intro w hw
    obtain ⟨S,hS,hwS⟩ := (classUnion_mem K w).mp hw
    exact hsub S hS hwS
  have hmask : classUnion (classFamilyNext isOr rest z a b K) =
      Structural.stepMask isOr rest (classUnion K) z a b := by
    simpa only [Structural.stepMask,classFresh,classReused] using
      classFamilyNext_union isOr rest z a b K hsub
  unfold classSub classOp
  rw [hmask]
  exact Structural.free_step hd hfree hEN hzr hab hza hzb isOr zero hzero

lemma backward {goal : W ι} {x0 x1 : ι} {k : Nat} {N : Finset (W ι)}
    (hR : ∀ w ∈ N, Regular x0 x1 w) (hl : live basicOps goal k N) :
    ∃ (F : (W ι → Bool) → Bool) (K : Finset (Finset (W ι))),
      Structural.Dep F N ∧ (∀ S ∈ K, S ⊆ N) ∧ (∀ S ∈ K, ORClass F S) ∧
      Structural.Free (fun x => F (Structural.kill (classUnion K) x)) ∧
      agrees goal F ∧ N.card + K.card ≤ k+1 :=
  backward_with_step family_free_step hR hl

end Backward

open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
namespace SemanticBridge
open FullCompile Structural

lemma agrees_on {n : Nat} {goal : (Fin n → Bool) → Bool}
    {F : (((Fin n → Bool) → Bool) → Bool) → Bool}
    (hd : Dep F (inputSet n)) (ha : agrees goal F) (i j : Fin n) :
    F (on (input i) (input j)) = goal (on i j) := by
  calc
    F (on (input i) (input j)) = F (fun f => f (on i j)) := by
      apply hd
      intro f hf
      obtain ⟨k,hk,rfl⟩ := Finset.mem_image.mp hf
      change (decide (input k = input i) || decide (input k = input j)) =
        (decide (k = i) || decide (k = j))
      simp only [(input_injective n).eq_iff]
    _ = goal (on i j) := ha _

def leftWire (a : Fin 33) : Fin 66 := ⟨a.val, by omega⟩
def rightWire (b : Fin 33) : Fin 66 := ⟨33+b.val, by omega⟩

lemma oneEach_on (a b : Fin 33) :
    oneEach a b = List.ofFn (on (leftWire a) (rightWire b)) := by
  apply List.ext_getElem
  · simp [oneEach]
  · intro i hi hj
    simp only [oneEach, List.length_append, List.length_ofFn] at hi hj ⊢
    by_cases h : i < 33
    · rw [List.getElem_append_left (by simpa using h)]
      simp only [List.getElem_ofFn, on, Fin.ext_iff, leftWire, rightWire]
      have hn : ¬ i = 33 + b.val := by omega
      simp [hn]
    · rw [List.getElem_append_right (by simp; omega)]
      simp only [List.getElem_ofFn, List.length_ofFn, on, Fin.ext_iff, leftWire, rightWire]
      have hn : ¬ i = a.val := by omega
      simp only [hn, decide_false, Bool.false_or, decide_eq_decide]
      omega

lemma agrees_represents {A : Fin 33 → Fin 33 → Bool} {C : Circuit}
    {F : (((Fin 66 → Bool) → Bool) → Bool) → Bool}
    (hd : Dep F (inputSet 66)) (ha : agrees (function 66 C) F) (hr : Represents A C) :
    ∀ a b : Fin 33, F (on (input (leftWire a)) (input (rightWire b))) = A a b := by
  intro a b
  rw [agrees_on hd ha]
  change C.eval (List.ofFn (on (leftWire a) (rightWire b))) = A a b
  rw [← oneEach_on]
  exact hr a b

lemma agrees_singletons {C : Circuit}
    {F : (((Fin 66 → Bool) → Bool) → Bool) → Bool}
    (hd : Dep F (inputSet 66)) (ha : agrees (function 66 C) F)
    (hs : ∀ i : Fin 66, C.eval (List.ofFn (fun j : Fin 66 => decide (j=i))) = false) :
    ∀ i : Fin 66, F (on (input i) (input i)) = false := by
  intro i
  rw [agrees_on hd ha]
  simpa [function, on] using hs i

def graph (a b : Fin 33) : Bool :=
  decide (∃ i : Fin 11,
    ((a.val = i.val ∨ a.val = 11+i.val) ∧ (b.val = (i.val+1)%11 ∨ b.val = 22+i.val)) ∨
    ((b.val = i.val ∨ b.val = 11+i.val) ∧ (a.val = (i.val+1)%11 ∨ a.val = 22+i.val)))

def neighbor (a : Fin 33) : Fin 33 :=
  if h : a.val < 22 then ⟨22+a.val%11, by omega⟩ else ⟨a.val-22, by omega⟩

lemma graph_neighbor : ∀ a : Fin 33, graph a (neighbor a) = true ∧ graph (neighbor a) a = true := by
  decide +kernel

lemma graph_diagonal : ∀ a : Fin 33, graph a a = false := by
  decide +kernel

lemma directed_left {C : Circuit} (hr : Represents graph C) (a : Fin 33) :
    DirectedCut (function 66 C) (leftWire a) := by
  let b := neighbor a
  refine ⟨on (leftWire a) (rightWire b), on (leftWire b) (rightWire b), ?_, ?_, ?_⟩
  · change C.eval (List.ofFn _) = true
    rw [← oneEach_on, hr]
    exact (graph_neighbor a).1
  · change C.eval (List.ofFn _) = false
    rw [← oneEach_on, hr]
    exact graph_diagonal b
  · intro j hx hy
    simp only [on, Bool.or_eq_true, decide_eq_true_eq] at hx
    rcases hx with h | h
    · exact h
    · subst j
      simp [on] at hy

lemma directed_right {C : Circuit} (hr : Represents graph C) (b : Fin 33) :
    DirectedCut (function 66 C) (rightWire b) := by
  let a := neighbor b
  refine ⟨on (leftWire a) (rightWire b), on (leftWire a) (rightWire a), ?_, ?_, ?_⟩
  · change C.eval (List.ofFn _) = true
    rw [← oneEach_on, hr]
    exact (graph_neighbor b).2
  · change C.eval (List.ofFn _) = false
    rw [← oneEach_on, hr]
    exact graph_diagonal a
  · intro j hx hy
    simp only [on, Bool.or_eq_true, decide_eq_true_eq] at hx
    rcases hx with h | h
    · subst j
      simp [on] at hy
    · exact h

lemma all_directed {C : Circuit} (hr : Represents graph C) :
    ∀ i : Fin 66, DirectedCut (function 66 C) i := by
  intro i
  by_cases h : i.val < 33
  · have hi : i = leftWire ⟨i.val,h⟩ := by apply Fin.ext; rfl
    rw [hi]
    exact directed_left hr _
  · have hh : i.val-33 < 33 := by omega
    have hi : i = rightWire ⟨i.val-33,hh⟩ := by apply Fin.ext; simp [rightWire]; omega
    rw [hi]
    exact directed_right hr _

end SemanticBridge

namespace SingletonBridge

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

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

def graph : Fin 33 → Fin 33 → Bool := (fun a b : Fin 33 => decide (∃ i : Fin 11, ((a.val = i.val ∨ a.val = 11 + i.val) ∧ (b.val = (i.val + 1) % 11 ∨ b.val = 22 + i.val)) ∨ ((b.val = i.val ∨ b.val = 11 + i.val) ∧ (a.val = (i.val + 1) % 11 ∨ a.val = 22 + i.val))))

lemma graph_diag : ∀ u : Fin 33, graph u u = false := by decide +kernel

lemma graph_pos : graph 0 1 = true := by decide +kernel

lemma eval_inp_mono (C : Circuit) (hm : Monotone2 C) {P Q : Finset ℕ}
    (hPQ : P ⊆ Q) : C.eval (inp 66 P) = true → C.eval (inp 66 Q) = true := by
  change (wiresFrom C.gates (inp 66 P)).getD C.output false = true →
    (wiresFrom C.gates (inp 66 Q)).getD C.output false = true
  apply mono C.gates (fun g hg => (hm g hg).1) _ _ (by simp [inp]) _ C.output
  intro i hi
  rw [inp_getD, decide_eq_true_eq] at hi ⊢
  exact ⟨hi.1, hPQ hi.2⟩

lemma singleton_inp_false (C : Circuit) (hm : Monotone2 C)
    (hr : PEqualNP.Represents.Represents graph C) (w : Fin 66) :
    C.eval (inp 66 {(w : ℕ)}) = false := by
  by_contra hn
  have ht : C.eval (inp 66 {(w : ℕ)}) = true := by
    cases h : C.eval (inp 66 {(w : ℕ)}) <;> simp_all
  let u : Fin 33 := ⟨w.val % 33, Nat.mod_lt _ (by decide)⟩
  have hsub : ({(w : ℕ)} : Finset ℕ) ⊆ {(u : ℕ), 33 + (u : ℕ)} := by
    intro i hi
    simp only [Finset.mem_singleton] at hi
    subst i
    simp only [Finset.mem_insert, Finset.mem_singleton]
    have hw := w.isLt
    dsimp [u]
    omega
  have hout := eval_inp_mono C hm hsub ht
  have hz : C.eval (inp 66 {(u : ℕ), 33 + (u : ℕ)}) = false := by
    rw [← oneEach_eq u u]
    exact (hr u u).trans (graph_diag u)
  rw [hz] at hout
  exact Bool.noConfusion hout

lemma singleton_false (C : Circuit) (hm : Monotone2 C)
    (hr : PEqualNP.Represents.Represents graph C) (w : Fin 66) :
    C.eval (List.ofFn (fun i : Fin 66 => decide (i = w))) = false := by
  simpa only [inp, Finset.mem_singleton, Fin.ext_iff] using singleton_inp_false C hm hr w

lemma zero_false (C : Circuit) (hm : Monotone2 C)
    (hr : PEqualNP.Represents.Represents graph C) :
    C.eval (List.ofFn (fun _ : Fin 66 => false)) = false := by
  have hz : C.eval (inp 66 (∅ : Finset ℕ)) = false := by
    by_contra hn
    have ht : C.eval (inp 66 (∅ : Finset ℕ)) = true := by
      cases h : C.eval (inp 66 (∅ : Finset ℕ)) <;> simp_all
    have hout := eval_inp_mono C hm (Finset.empty_subset ({0} : Finset ℕ)) ht
    have hs := singleton_inp_false C hm hr 0
    change C.eval (inp 66 {0}) = false at hs
    rw [hs] at hout
    exact Bool.noConfusion hout
  simpa [inp] using hz

lemma function_ne_zero (C : Circuit) (hr : PEqualNP.Represents.Represents graph C) :
    (fun x : Fin 66 → Bool => C.eval (List.ofFn x)) ≠ (fun _ => false) := by
  intro h
  have hz := congrFun h (fun i : Fin 66 => decide ((i : ℕ) ∈ ({0,34} : Finset ℕ)))
  change C.eval (inp 66 {0,34}) = false at hz
  have hp := hr 0 1
  rw [graph_pos, oneEach_eq] at hp
  change C.eval (inp 66 {0,34}) = true at hp
  rw [hz] at hp
  exact Bool.noConfusion hp

lemma function_ne_one (C : Circuit) (hr : PEqualNP.Represents.Represents graph C) :
    (fun x : Fin 66 → Bool => C.eval (List.ofFn x)) ≠ (fun _ => true) := by
  intro h
  have ho := congrFun h (fun i : Fin 66 => decide ((i : ℕ) ∈ ({0,33} : Finset ℕ)))
  change C.eval (inp 66 {0,33}) = true at ho
  have hn := hr 0 0
  rw [graph_diag, oneEach_eq] at hn
  change C.eval (inp 66 {0,33}) = false at hn
  rw [hn] at ho
  exact Bool.noConfusion ho

end SingletonBridge

namespace Finish
open scoped Classical
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open FullCompile Structural

lemma graph_rows : Function.Injective SemanticBridge.graph := by
  have hsep : ∀ a b : Fin 33, a ≠ b → ∃ c : Fin 33,
      SemanticBridge.graph a c ≠ SemanticBridge.graph b c := by decide +kernel
  intro a b he
  by_contra hn
  obtain ⟨c,hc⟩ := hsep a b hn
  exact hc (congrFun he c)

lemma graph_cols : Function.Injective (fun b => fun a => SemanticBridge.graph a b) := by
  have hsep : ∀ a b : Fin 33, a ≠ b → ∃ c : Fin 33,
      SemanticBridge.graph c a ≠ SemanticBridge.graph c b := by decide +kernel
  intro a b he
  by_contra hn
  obtain ⟨c,hc⟩ := hsep a b hn
  exact hc (congrFun he c)

lemma inputSet_partition : inputSet 66 =
    Finset.univ.image (fun a : Fin 33 => input (SemanticBridge.leftWire a)) ∪
    Finset.univ.image (fun b : Fin 33 => input (SemanticBridge.rightWire b)) := by
  ext f
  constructor
  · intro hf
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hf
    by_cases h : i.val < 33
    · apply Finset.mem_union_left
      refine Finset.mem_image.mpr ⟨⟨i.val,h⟩, Finset.mem_univ _, ?_⟩
      congr 1
    · apply Finset.mem_union_right
      refine Finset.mem_image.mpr ⟨⟨i.val-33,by omega⟩, Finset.mem_univ _, ?_⟩
      congr 1
      apply Fin.ext
      simp only [SemanticBridge.rightWire]
      omega
  · intro hf
    rcases Finset.mem_union.mp hf with hl | hr
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hl
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hr
      exact Finset.mem_image.mpr ⟨_, Finset.mem_univ _, rfl⟩

lemma finish (C : Circuit) (hm : Monotone2 C) (hr : Represents SemanticBridge.graph C)
    (F : (((Fin 66 → Bool) → Bool) → Bool) → Bool)
    (K : Finset (Finset ((Fin 66 → Bool) → Bool)))
    (hd : Dep F (inputSet 66))
    (hsub : ∀ S ∈ K, S ⊆ inputSet 66)
    (hclass : ∀ S ∈ K, ORClass F S)
    (hfree : Free (fun x => F (kill (classUnion K) x)))
    (ha : agrees (function 66 C) F)
    (hbudget : 66 + K.card ≤ C.size + 1) : 72 ≤ C.size := by
  have hpair := SemanticBridge.agrees_represents hd ha hr
  have hsingle := SemanticBridge.agrees_singletons hd ha (SingletonBridge.singleton_false C hm hr)
  have hpacking : 14 ≤ (classUnion K).card := by
    apply cycle33_free_deletion_lower_generic (@input 66) (input_injective 66) F
    · exact hpair
    · exact hsingle
    · exact hfree
  have hunion : classUnion K ⊆ inputSet 66 := by
    intro f hf
    obtain ⟨S,hS,hf⟩ := Finset.mem_biUnion.mp hf
    exact hsub S hS hf
  have hc := orClasses_valid_union_card F SemanticBridge.graph
    (fun a : Fin 33 => input (SemanticBridge.leftWire a))
    (fun b : Fin 33 => input (SemanticBridge.rightWire b))
    hpair graph_rows graph_cols K hclass
  rw [← inputSet_partition] at hc
  change ((classUnion K) ∩ inputSet 66).card ≤ 2 * K.card at hc
  rw [Finset.inter_eq_left.mpr hunion] at hc
  omega

end Finish

end PEqualNP.Outside.L_meta_9502

open PEqualNP.Outside.L_meta_9502

set_option maxRecDepth 10000 in
theorem PEqualNP.Outside.L_meta_9502 :
    ¬ PEqualNP.Represents.RepSizeAtMost (fun a b : Fin 33 => decide (∃ i : Fin 11, ((a.val = i.val ∨ a.val = 11 + i.val) ∧ (b.val = (i.val + 1) % 11 ∨ b.val = 22 + i.val)) ∨ ((b.val = i.val ∨ b.val = 11 + i.val) ∧ (a.val = (i.val + 1) % 11 ∨ a.val = 22 + i.val)))) 71 := by
  intro h
  obtain ⟨C,hm,hs,hr⟩ := h
  change PEqualNP.Represents.Represents SemanticBridge.graph C at hr
  have hz : FullCompile.function 66 C ≠ FullCompile.zero := SingletonBridge.function_ne_zero C hr
  have ho : FullCompile.function 66 C ≠ FullCompile.one := SingletonBridge.function_ne_one C hr
  have hl := FullCompile.circuit_live_directed C hm hz ho (SemanticBridge.all_directed hr)
  have hreg : ∀ w ∈ FullCompile.inputSet 66,
      FullCompile.Regular (fun _ => false) (fun _ => true) w := fun w hw => FullCompile.inputs_regular hw
  obtain ⟨F,K,hd,hsub,hclass,hfree,ha,hbudget⟩ := Backward.backward hreg hl
  rw [FullCompile.inputSet_card] at hbudget
  have hinst : (fun a b : (Fin 66 → Bool) → Bool => Classical.propDecidable (a = b)) =
      (fun a b : (Fin 66 → Bool) → Bool => Fintype.decidablePiFintype a b) := Subsingleton.elim _ _
  rw [hinst] at hclass hfree
  have hbound := Finish.finish C hm hr F K hd hsub hclass hfree ha hbudget
  omega
