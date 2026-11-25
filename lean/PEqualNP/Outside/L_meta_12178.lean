import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_12178

namespace Threshold

def zeroGate (k : Fin 4) (a b : Bool) : Bool :=
  match k.val with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | _ => !a && b

theorem zeroGate_canalizes :
    ∀ k : Fin 4,
      (∃ b c : Bool, ∀ a : Bool, zeroGate k a b = c) ∧
      (∃ a c : Bool, ∀ b : Bool, zeroGate k a b = c) := by
  decide

abbrev Formula (n : Nat) := BinaryTree (Sum (Fin n) Bool)

def formEval {n : Nat} : Formula n → (Fin n → Bool) → Bool
  | .nil, _ => false
  | .node (.inl i) _ _, x => x i
  | .node (.inr false) l r, x => formEval l x || formEval r x
  | .node (.inr true) l r, x => formEval l x && formEval r x

def singleInput {n : Nat} (i : Fin n) : Fin n → Bool :=
  fun j => decide (j = i)

def pairInput {n : Nat} (i j : Fin n) : Fin n → Bool :=
  fun k => decide (k = i ∨ k = j)

def formOcc {n : Nat} : Formula n → Fin n → Nat
  | .nil, _ => 0
  | .node (.inl j) _ _, i => if j = i then 1 else 0
  | .node (.inr _) l r, i => formOcc l i + formOcc r i

def formCut {n : Nat} (l r : Formula n) (i : Fin n) : Option Bool :=
  match formEval l (singleInput i), formEval r (singleInput i) with
  | true, false => some false
  | false, true => some true
  | _, _ => none

def formCuts {n : Nat} : Formula n → List (Fin n → Option Bool)
  | .nil => []
  | .node (.inl _) _ _ => []
  | .node (.inr false) l r => formCuts l ++ formCuts r
  | .node (.inr true) l r => formCut l r :: (formCuts l ++ formCuts r)

def formDegree {n : Nat} (t : Formula n) (i : Fin n) : Nat :=
  (formCuts t).countP fun c => (c i).isSome

theorem form_charge {n : Nat} (t : Formula n) (i : Fin n) :
    formDegree t i + (formEval t (singleInput i)).toNat ≤ formOcc t i := by
  induction t with
  | nil => simp [formDegree, formCuts, formEval, formOcc]
  | node a l r hl hr =>
    cases a with
    | inl j =>
      by_cases h : j = i <;>
        simp [formDegree, formCuts, formEval, formOcc, singleInput, h]
    | inr op =>
      cases op <;>
        cases el : formEval l (singleInput i) <;>
        cases er : formEval r (singleInput i) <;>
        simp [formDegree, formCuts, formEval, formOcc, formCut, el, er,
          List.countP_append] at * <;> omega

theorem form_pair_separator {n : Nat} (t : Formula n) (i j : Fin n)
    (hp : formEval t (pairInput i j) = true)
    (hi : formEval t (singleInput i) = false)
    (hj : formEval t (singleInput j) = false) :
    ∃ c ∈ formCuts t,
      (c i = some false ∧ c j = some true) ∨
      (c i = some true ∧ c j = some false) := by
  induction t with
  | nil => simp [formEval] at hp
  | node a l r hl hr =>
    cases a with
    | inl k =>
      simp [formEval, pairInput] at hp
      simp [formEval, singleInput] at hi hj
      rcases hp with hp | hp
      · exact (hi hp).elim
      · exact (hj hp).elim
    | inr op =>
      cases op with
      | false =>
        simp only [formEval, Bool.or_eq_true] at hp
        simp only [formEval, Bool.or_eq_false_iff] at hi hj
        rcases hp with hp | hp
        · obtain ⟨c, hc, hs⟩ := hl hp hi.1 hj.1
          exact ⟨c, by simp [formCuts, hc], hs⟩
        · obtain ⟨c, hc, hs⟩ := hr hp hi.2 hj.2
          exact ⟨c, by simp [formCuts, hc], hs⟩
      | true =>
        simp only [formEval, Bool.and_eq_true] at hp
        have liftL (hli : formEval l (singleInput i) = false)
            (hlj : formEval l (singleInput j) = false) :
            ∃ c ∈ formCuts (.node (.inr true) l r),
              (c i = some false ∧ c j = some true) ∨
              (c i = some true ∧ c j = some false) := by
          obtain ⟨c, hc, hs⟩ := hl hp.1 hli hlj
          exact ⟨c, by simp [formCuts, hc], hs⟩
        have liftR (hri : formEval r (singleInput i) = false)
            (hrj : formEval r (singleInput j) = false) :
            ∃ c ∈ formCuts (.node (.inr true) l r),
              (c i = some false ∧ c j = some true) ∨
              (c i = some true ∧ c j = some false) := by
          obtain ⟨c, hc, hs⟩ := hr hp.2 hri hrj
          exact ⟨c, by simp [formCuts, hc], hs⟩
        cases eli : formEval l (singleInput i) with
        | false =>
          cases elj : formEval l (singleInput j) with
          | false => exact liftL eli elj
          | true =>
            have erj : formEval r (singleInput j) = false := by
              simpa [formEval, elj] using hj
            cases eri : formEval r (singleInput i) with
            | false => exact liftR eri erj
            | true =>
              refine ⟨formCut l r, by simp [formCuts], Or.inr ?_⟩
              simp [formCut, eli, elj, eri, erj]
        | true =>
          have eri : formEval r (singleInput i) = false := by
            simpa [formEval, eli] using hi
          cases erj : formEval r (singleInput j) with
          | false => exact liftR eri erj
          | true =>
            have elj : formEval l (singleInput j) = false := by
              simpa [formEval, erj] using hj
            refine ⟨formCut l r, by simp [formCuts], Or.inl ?_⟩
            simp [formCut, eli, elj, eri, erj]

open scoped BigOperators

def cCube {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (b : α → Bool) : Finset (α → Bool) :=
  Fintype.piFinset fun a => if a ∈ s then {b a} else Finset.univ

theorem cCubeMember {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (b f : α → Bool) :
    f ∈ cCube s b ↔ ∀ a ∈ s, f a = b a := by
  simp only [cCube, Fintype.mem_piFinset]
  constructor
  · intro h a ha
    simpa only [ite_eq_left ha, Finset.mem_singleton] using h a
  · intro h a
    by_cases ha : a ∈ s
    · simpa only [ite_eq_left ha, Finset.mem_singleton] using h a ha
    · simp only [ite_eq_right ha, Finset.mem_univ]

theorem cCubeCard {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (b : α → Bool) :
    (cCube s b).card = ∏ a : α, if a ∈ s then 1 else 2 := by
  rw [cCube, Fintype.card_piFinset]
  apply Finset.prod_congr rfl
  intro a ha
  by_cases hs : a ∈ s <;> simp [hs]

theorem cCubeVolume {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (b : α → Bool) :
    (cCube s b).card * 2 ^ s.card = 2 ^ Fintype.card α := by
  rw [cCubeCard]
  have hs : (∏ a : α, if a ∈ s then 2 else 1) = 2 ^ s.card := by simp
  rw [← hs, ← Finset.prod_mul_distrib]
  have he : (∏ a : α, (if a ∈ s then 1 else 2) * (if a ∈ s then 2 else 1)) =
      ∏ _a : α, 2 := by
    apply Finset.prod_congr rfl
    intro a ha
    by_cases h : a ∈ s <;> simp [h]
  rw [he]
  simp

theorem cCubeQuarter {α : Type*} [Fintype α] [DecidableEq α]
    (s : Finset α) (b : α → Bool) (hs : s.card ≤ 2) :
    2 ^ Fintype.card α ≤ (cCube s b).card * 4 := by
  have hpow : 2 ^ s.card ≤ 4 := by
    simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hs
  calc
    2 ^ Fintype.card α = (cCube s b).card * 2 ^ s.card := (cCubeVolume s b).symm
    _ ≤ (cCube s b).card * 4 := Nat.mul_le_mul_left _ hpow

theorem cFiveSeparatedImpossible {α : Type*} [Fintype α] [DecidableEq α]
    (s : Fin 5 → Finset α) (b : Fin 5 → α → Bool)
    (small : ∀ i, (s i).card ≤ 2)
    (separates : ∀ i j, i ≠ j → ∃ a, a ∈ s i ∧ a ∈ s j ∧ b i a ≠ b j a) :
    False := by
  classical
  have hd : ((Finset.univ : Finset (Fin 5)) : Set (Fin 5)).PairwiseDisjoint
      (fun i => cCube (s i) (b i)) := by
    intro i hi j hj hij
    apply Finset.disjoint_left.mpr
    intro f hfi hfj
    obtain ⟨a, hai, haj, hab⟩ := separates i j hij
    have hia := (cCubeMember (s i) (b i) f).mp hfi a hai
    have hja := (cCubeMember (s j) (b j) f).mp hfj a haj
    exact hab (hia.symm.trans hja)
  have upper : (∑ i : Fin 5, (cCube (s i) (b i)).card) ≤ 2 ^ Fintype.card α := by
    rw [← Finset.card_biUnion hd]
    have h := Finset.card_le_univ
      ((Finset.univ : Finset (Fin 5)).biUnion fun i => cCube (s i) (b i))
    simpa using h
  have lower : 5 * 2 ^ Fintype.card α ≤
      (∑ i : Fin 5, (cCube (s i) (b i)).card) * 4 := by
    calc
      5 * 2 ^ Fintype.card α = ∑ _i : Fin 5, 2 ^ Fintype.card α := by simp
      _ ≤ ∑ i : Fin 5, (cCube (s i) (b i)).card * 4 := by
        apply Finset.sum_le_sum
        intro i hi
        exact cCubeQuarter (s i) (b i) (small i)
      _ = (∑ i : Fin 5, (cCube (s i) (b i)).card) * 4 :=
        (Finset.sum_mul _ _ _).symm
  have hp : 0 < 2 ^ Fintype.card α := Nat.pow_pos (by decide)
  omega

theorem no_readtwice_five (t : Formula 5)
    (hocc : ∀ i, formOcc t i ≤ 2)
    (hs : ∀ i, formEval t (singleInput i) = false)
    (hp : ∀ i j, i ≠ j → formEval t (pairInput i j) = true) : False := by
  let L := formCuts t
  let s : Fin 5 → Finset (Fin L.length) := fun i =>
    Finset.univ.filter fun k => ((L.get k) i).isSome
  let b : Fin 5 → Fin L.length → Bool := fun i k => ((L.get k) i).getD false
  apply cFiveSeparatedImpossible s b
  · intro i
    have hcard : (s i).card = formDegree t i := by
      simpa [s, formDegree, L, List.ofFn_get] using
        (List.countP_ofFn (List.get L) (fun c => (c i).isSome)).symm
    rw [hcard]
    have hc := form_charge t i
    have ho := hocc i
    omega
  · intro i j hij
    obtain ⟨c, hc, hsep⟩ := form_pair_separator t i j (hp i j hij) (hs i) (hs j)
    obtain ⟨k, hk⟩ := List.mem_iff_get.mp hc
    change (formCuts t)[k.val] = c at hk
    rcases hsep with ⟨hci, hcj⟩ | ⟨hci, hcj⟩
    · refine ⟨k, ?_, ?_, ?_⟩ <;> simp [s, b, L, hk, hci, hcj]
    · refine ⟨k, ?_, ?_, ?_⟩ <;> simp [s, b, L, hk, hci, hcj]

section Generic
variable {α : Type} {β : Type}

def UC (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) : ℕ → (α → Prop) → α → Prop
  | 0, S, f => S f
  | t + 1, S, f => UC G A t S f ∨
      ∃ k a b, A k ∧ S a ∧ S b ∧ UC G A t (fun w => w = G k a b ∨ S w) f

theorem UC_monoS (G : Fin 4 → α → α → α) (A : Fin 4 → Prop) :
    ∀ (t : ℕ) (S S' : α → Prop) (f : α), (∀ w, S w → S' w) → UC G A t S f → UC G A t S' f
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_monoS G A t S S' f h hu)
    · exact Or.inr ⟨k, a, b, hk, h a ha, h b hb,
        UC_monoS G A t _ _ f (fun w hw => hw.imp id (h w)) hu⟩

theorem UC_le {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t t' : ℕ} {S : α → Prop} {f : α}
    (h : t ≤ t') (hu : UC G A t S f) : UC G A t' S f := by
  induction h with
  | refl => exact hu
  | step _ ih => exact Or.inl ih

theorem UC_gate {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} {t : ℕ} {S : α → Prop} {f : α}
    (k : Fin 4) (a b : α) (hk : A k) (ha : S a) (hb : S b)
    (hu : UC G A t (fun w => w = G k a b ∨ S w) f) : UC G A (t + 1) S f :=
  Or.inr ⟨k, a, b, hk, ha, hb, hu⟩

theorem UC_map {G : Fin 4 → α → α → α} {G' : Fin 4 → β → β → β} {A : Fin 4 → Prop} (e : α → β)
    (he : ∀ k a b, e (G k a b) = G' k (e a) (e b)) :
    ∀ (t : ℕ) (S : α → Prop) (S' : β → Prop) (f : α), (∀ w, S w → S' (e w)) →
      UC G A t S f → UC G' A t S' (e f)
  | 0, _, _, f, h, hu => h f hu
  | t + 1, S, S', f, h, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_map e he t S S' f h hu)
    · refine Or.inr ⟨k, e a, e b, hk, h a ha, h b hb, UC_map e he t _ _ f ?_ hu⟩
      intro w hw
      rcases hw with rfl | hw
      · exact Or.inl (he k a b)
      · exact Or.inr (h w hw)

def TR (G : Fin 4 → α → α → α) (C : Fin 4 → α → α → Prop) (ys : List α) (t : ℕ)
    (ws : List α) : Prop :=
  ∀ P : ℕ → List α → Prop, P 0 ys →
    (∀ s xs zs, List.Perm xs zs → P s xs → P s zs) →
    (∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) →
    P t ws

section Run
variable {G : Fin 4 → α → α → α} {C : Fin 4 → α → α → Prop} {ys : List α}

theorem TR.done : TR G C ys 0 ys := fun _ d _ _ => d

theorem TR.perm {s : ℕ} {xs zs : List α} (p : List.Perm xs zs) (h : TR G C ys s xs) :
    TR G C ys s zs := fun P d q st => q s xs zs p (h P d q st)

theorem TR.step {s : ℕ} {a b : α} {r : List α} (k : Fin 4) (u : ℕ) (hc : C k a b)
    (h : TR G C ys s (List.replicate (u + 1) (G k a b) ++ r)) :
    TR G C ys (s + 1) (a :: b :: r) := fun P d q st => st s a b r k u hc (h P d q st)

theorem TR.ind {P : ℕ → List α → Prop} {t : ℕ} {ws : List α} (h : TR G C ys t ws)
    (d : P 0 ys)
    (p : ∀ s xs zs, List.Perm xs zs → TR G C ys s xs → P s xs → P s zs)
    (st : ∀ s a b r (k : Fin 4) (u : ℕ), C k a b →
      TR G C ys s (List.replicate (u + 1) (G k a b) ++ r) →
      P s (List.replicate (u + 1) (G k a b) ++ r) → P (s + 1) (a :: b :: r)) : P t ws :=
  (h (fun s xs => TR G C ys s xs ∧ P s xs) ⟨TR.done, d⟩
    (fun s xs zs hp hx => ⟨TR.perm hp hx.1, p s xs zs hp hx.1 hx.2⟩)
    (fun s a b r k u hc hx => ⟨TR.step k u hc hx.1, st s a b r k u hc hx.1 hx.2⟩)).2

theorem TR.inv {t : ℕ} {ws : List α} (h : TR G C ys t ws) :
    (t = 0 → List.Perm ws ys) ∧
    (∀ s, t = s + 1 → ∃ (k : Fin 4) (u : ℕ) (a b : α) (r : List α), C k a b ∧
      List.Perm ws (a :: b :: r) ∧ TR G C ys s (List.replicate (u + 1) (G k a b) ++ r)) := by
  refine TR.ind (P := fun t ws => (t = 0 → List.Perm ws ys) ∧
    (∀ s, t = s + 1 → ∃ (k : Fin 4) (u : ℕ) (a b : α) (r : List α), C k a b ∧
      List.Perm ws (a :: b :: r) ∧ TR G C ys s (List.replicate (u + 1) (G k a b) ++ r))) h
    ⟨fun _ => List.Perm.refl _, fun s hs => by omega⟩ ?_ ?_
  · intro s xs zs hp _ ih
    refine ⟨fun h0 => hp.symm.trans (ih.1 h0), fun s' hs => ?_⟩
    obtain ⟨k, u, a, b, r, hc, hq, hr⟩ := ih.2 s' hs
    exact ⟨k, u, a, b, r, hc, hp.symm.trans hq, hr⟩
  · intro s a b r k u hc hr _
    refine ⟨fun h0 => by omega, fun s' hs => ?_⟩
    have : s = s' := by omega
    subst this
    exact ⟨k, u, a, b, r, hc, List.Perm.refl _, hr⟩

theorem TR.len {t : ℕ} {ws : List α} (h : TR G C ys t ws) : ws.length ≤ t + ys.length := by
  refine TR.ind (P := fun t ws => ws.length ≤ t + ys.length) h (by simp) ?_ ?_
  · intro s xs zs hp _ ih
    rw [← hp.length_eq]; exact ih
  · intro s a b r k u _ _ ih
    simp only [List.length_append, List.length_replicate, List.length_cons] at ih ⊢
    omega

theorem TR.monoC {C' : Fin 4 → α → α → Prop} (hC : ∀ k a b, C k a b → C' k a b) {t : ℕ}
    {ws : List α} (h : TR G C ys t ws) : TR G C' ys t ws :=
  TR.ind (P := fun t ws => TR G C' ys t ws) h TR.done (fun _ _ _ hp _ ih => TR.perm hp ih)
    (fun _ _ _ _ k u hc _ ih => TR.step k u (hC _ _ _ hc) ih)

end Run

def strictC (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop) (I : α → Prop) :
    Fin 4 → α → α → Prop :=
  fun k a b => A k ∧ I a ∧ I b ∧ a ≠ b ∧ G k a b ≠ a ∧ G k a b ≠ b ∧ G k a b ≠ z

theorem normalize [DecidableEq α] (G : Fin 4 → α → α → α) (z : α) (A : Fin 4 → Prop)
    (I : α → Prop) (hI : ∀ k a b, I a → I b → I (G k a b))
    (hz1 : ∀ k b, G k z b = z ∨ G k z b = b) (hz2 : ∀ k a, G k a z = z ∨ G k a z = a)
    (hd : ∀ k a, G k a a = z ∨ G k a a = a) :
    ∀ (t : ℕ) (S : α → Prop) (f : α), (∀ w, S w → I w) → f ≠ z → UC G A t S f →
      ∃ t', t' ≤ t ∧ ∃ ws : List α, (∀ w ∈ ws, S w ∧ w ≠ z) ∧
        TR G (strictC G z A I) [f] t' ws
  | 0, S, f, _, hf, hu => ⟨0, le_rfl, [f], by simpa using ⟨hu, hf⟩, TR.done⟩
  | t + 1, S, f, hS, hf, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t S f hS hf hu
      exact ⟨t', by omega, ws, hws, hr⟩
    · obtain ⟨t', ht, ws, hws, hr⟩ := normalize G z A I hI hz1 hz2 hd t _ f (by
        rintro w (rfl | hw)
        · exact hI k a b (hS a ha) (hS b hb)
        · exact hS w hw) hf hu
      by_cases hg : S (G k a b)
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact hg
        · exact h
      by_cases hc : G k a b ∈ ws
      · have hgz : G k a b ≠ z := (hws _ hc).2
        have hga : G k a b ≠ a := fun h => hg (by rw [h]; exact ha)
        have hgb : G k a b ≠ b := fun h => hg (by rw [h]; exact hb)
        have hab : a ≠ b := by
          rintro rfl
          rcases hd k a with h | h
          · exact hgz h
          · exact hga h
        have haz : a ≠ z := by
          rintro rfl
          rcases hz1 k b with h | h
          · exact hgz h
          · exact hgb h
        have hbz : b ≠ z := by
          rintro rfl
          rcases hz2 k a with h | h
          · exact hgz h
          · exact hga h
        obtain ⟨u, hu1⟩ : ∃ u, List.count (G k a b) ws = u + 1 :=
          ⟨List.count (G k a b) ws - 1, by have := List.count_pos_iff.2 hc; omega⟩
        have hperm : ws.Perm (List.replicate (u + 1) (G k a b) ++ ws.filter (· ≠ G k a b)) := by
          rw [← hu1, ← List.filter_eq]
          have := List.filter_append_perm (fun x => decide (x = G k a b)) ws
          refine this.symm.trans ?_
          simp
        refine ⟨t' + 1, by omega, a :: b :: ws.filter (· ≠ G k a b), ?_,
          TR.step k u ⟨hk, hS a ha, hS b hb, hab, hga, hgb, hgz⟩ (TR.perm hperm hr)⟩
        intro w hw
        simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq] at hw
        rcases hw with rfl | rfl | ⟨hw, hne⟩
        · exact ⟨ha, haz⟩
        · exact ⟨hb, hbz⟩
        · rcases (hws w hw).1 with h | h
          · exact absurd h hne
          · exact ⟨h, (hws w hw).2⟩
      · refine ⟨t', by omega, ws, fun w hw => ⟨?_, (hws w hw).2⟩, hr⟩
        rcases (hws w hw).1 with rfl | h
        · exact absurd hw hc
        · exact h

theorem TR.map {G : Fin 4 → α → α → α} {G' : Fin 4 → β → β → β} {C : Fin 4 → α → α → Prop}
    {C' : Fin 4 → β → β → Prop} (e : α → β) (he : ∀ k a b, e (G k a b) = G' k (e a) (e b))
    (hC : ∀ k a b, C k a b → C' k (e a) (e b)) {ys : List α} {t : ℕ} {ws : List α}
    (h : TR G C ys t ws) : TR G' C' (ys.map e) t (ws.map e) := by
  refine TR.ind (P := fun t ws => TR G' C' (ys.map e) t (ws.map e)) h TR.done
    (fun _ _ _ hp _ ih => TR.perm (hp.map e) ih) ?_
  intro s a b r k u hc _ ih
  rw [List.map_append, List.map_replicate, he] at ih
  exact TR.step k u (hC _ _ _ hc) ih

theorem TR.rel {G : Fin 4 → α → α → α} {A : Fin 4 → Prop} (R : α → α → Prop)
    (hR : ∀ k a a' b b', R a a' → R b b' → R (G k a b) (G k a' b')) {ys : List α} {t : ℕ}
    {ws : List α} (h : TR G (fun k _ _ => A k) ys t ws) :
    ∀ ws', List.Forall₂ R ws ws' →
      ∃ ys', List.Forall₂ R ys ys' ∧ TR G (fun k _ _ => A k) ys' t ws' := by
  refine TR.ind (P := fun t ws => ∀ ws', List.Forall₂ R ws ws' →
      ∃ ys', List.Forall₂ R ys ys' ∧ TR G (fun k _ _ => A k) ys' t ws') h
    (fun ws' hw => ⟨ws', hw, TR.done⟩) ?_ ?_
  · intro s xs zs hp _ ih zs' hz
    obtain ⟨xs', hx, hp'⟩ := List.perm_comp_forall₂ hp hz
    obtain ⟨ys', hy, hr⟩ := ih xs' hx
    exact ⟨ys', hy, TR.perm hp' hr⟩
  · intro s a b r k u hc _ ih ws' hw
    obtain ⟨a', t1, ha, ht1, rfl⟩ := List.forall₂_cons_left_iff.1 hw
    obtain ⟨b', r', hb, hr', rfl⟩ := List.forall₂_cons_left_iff.1 ht1
    have h1 : List.Forall₂ R (List.replicate (u + 1) (G k a b) ++ r)
        (List.replicate (u + 1) (G k a' b') ++ r') := by
      refine List.rel_append ?_ hr'
      generalize u + 1 = n
      induction n with
      | zero => exact List.Forall₂.nil
      | succ n ih => exact List.Forall₂.cons (hR k a a' b b' ha hb) ih
    obtain ⟨ys', hy, hrun⟩ := ih _ h1
    exact ⟨ys', hy, TR.step k u hc hrun⟩

end Generic

abbrev BF := (Fin 5 → Bool) → Bool

def gF (k : Fin 4) (a b : BF) : BF := fun x => zeroGate k (a x) (b x)

def var (i : Fin 5) : BF := fun x => x i

def gM (k a b : ℕ) : ℕ :=
  match k with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a ^^^ (a &&& b)
  | _ => b ^^^ (a &&& b)

def gN (k : Fin 4) (a b : ℕ) : ℕ := gM k.val a b

theorem gN_testBit (k : Fin 4) (a b i : ℕ) :
    (gN k a b).testBit i = zeroGate k (a.testBit i) (b.testBit i) := by
  fin_cases k <;>
    simp [gN, gM, zeroGate, Nat.testBit_and, Nat.testBit_or, Nat.testBit_xor] <;>
    cases a.testBit i <;> cases b.testBit i <;> rfl

theorem gN_zero_left (k : Fin 4) (b : ℕ) : gN k 0 b = 0 ∨ gN k 0 b = b := by
  fin_cases k <;> simp [gN, gM]

theorem gN_zero_right (k : Fin 4) (a : ℕ) : gN k a 0 = 0 ∨ gN k a 0 = a := by
  fin_cases k <;> simp [gN, gM]

theorem gN_self (k : Fin 4) (a : ℕ) : gN k a a = 0 ∨ gN k a a = a := by
  fin_cases k <;> simp [gN, gM]

theorem gN_lt (k : Fin 4) (a b : ℕ) (ha : a < 1024) (hb : b < 1024) : gN k a b < 1024 := by
  apply Nat.lt_pow_two_of_testBit (n := 10)
  intro i hi
  have hp : (1024 : ℕ) ≤ 2 ^ i :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (show 0 < 2 by norm_num) hi)
  rw [gN_testBit, Nat.testBit_lt_two_pow (lt_of_lt_of_le ha hp),
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hb hp)]
  fin_cases k <;> rfl

def enc {ρ : Type} (w : ρ → Bool) : List ρ → ℕ
  | [] => 0
  | p :: t => Nat.bit (w p) (enc w t)

theorem enc_testBit {ρ : Type} (w : ρ → Bool) : ∀ (l : List ρ) (j : ℕ),
    (enc w l).testBit j = (l.map w).getD j false
  | [], j => by simp [enc]
  | p :: t, 0 => by simp [enc]
  | p :: t, j + 1 => by simp [enc, Nat.testBit_bit_succ, enc_testBit w t j]

theorem enc_gate {ρ : Type} (k : Fin 4) (a b : ρ → Bool) (l : List ρ) :
    enc (fun r => zeroGate k (a r) (b r)) l = gN k (enc a l) (enc b l) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [gN_testBit, enc_testBit, enc_testBit, enc_testBit]
  by_cases h : j < l.length
  · simp [h]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    fin_cases k <;> rfl

theorem enc_gF (k : Fin 4) (a b : BF) (l : List (Fin 5 → Bool)) :
    enc (gF k a b) l = gN k (enc a l) (enc b l) := enc_gate k a b l

theorem enc_lt {ρ : Type} (w : ρ → Bool) (l : List ρ) : enc w l < 2 ^ l.length := by
  apply Nat.lt_pow_two_of_testBit
  intro i hi
  rw [enc_testBit, List.getD_eq_default _ _ (by simp; omega)]

theorem TRN_det {C : Fin 4 → ℕ → ℕ → Prop} {y : ℕ} {s : ℕ} {ws : List ℕ}
    (h : TR gN C [y] s ws) (i j : ℕ) :
    (∀ t ∈ ws, t.testBit i = t.testBit j) → y.testBit i = y.testBit j := by
  refine TR.ind (P := fun _ ws => (∀ t ∈ ws, t.testBit i = t.testBit j) →
    y.testBit i = y.testBit j) h (fun h => h y (by simp)) ?_ ?_
  · intro s xs zs hp _ ih hz
    exact ih fun t ht => hz t (hp.mem_iff.1 ht)
  · intro s a b r k u _ _ ih hz
    apply ih
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · rw [List.eq_of_mem_replicate ht, gN_testBit, gN_testBit, hz a (by simp), hz b (by simp)]
    · exact hz t (by simp [ht])

theorem TRN_zp {C : Fin 4 → ℕ → ℕ → Prop} {y : ℕ} {s : ℕ} {ws : List ℕ}
    (h : TR gN C [y] s ws) (i : ℕ) :
    (∀ t ∈ ws, t.testBit i = false) → y.testBit i = false := by
  refine TR.ind (P := fun _ ws => (∀ t ∈ ws, t.testBit i = false) →
    y.testBit i = false) h (fun h => h y (by simp)) ?_ ?_
  · intro s xs zs hp _ ih hz
    exact ih fun t ht => hz t (hp.mem_iff.1 ht)
  · intro s a b r k u _ _ ih hz
    apply ih
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · rw [List.eq_of_mem_replicate ht, gN_testBit, hz a (by simp), hz b (by simp)]
      fin_cases k <;> rfl
    · exact hz t (by simp [ht])

def sg (p t : ℕ) : ℕ := if t.testBit p then t ^^^ 1023 else t

def covB (f : ℕ → ℕ) (ws : List ℕ) : Bool :=
  ws.foldl (fun acc t => acc ||| f t) 0 &&& 1008 == 1008

def cov (ws : List ℕ) : Bool :=
  covB id ws && covB (sg 0) ws && covB (sg 1) ws && covB (sg 2) ws && covB (sg 3) ws

theorem fold_bit (f : ℕ → ℕ) (i : ℕ) : ∀ (ws : List ℕ) (a : ℕ),
    (ws.foldl (fun acc t => acc ||| f t) a).testBit i =
      (a.testBit i || ws.any fun t => (f t).testBit i)
  | [], a => by simp
  | t :: ws, a => by
    rw [List.foldl_cons, fold_bit f i ws, Nat.testBit_or, List.any_cons, Bool.or_assoc]

theorem covB_iff (f : ℕ → ℕ) (ws : List ℕ) :
    covB f ws = true ↔
      ∀ i, (1008 : ℕ).testBit i = true → ∃ t ∈ ws, (f t).testBit i = true := by
  unfold covB
  rw [beq_iff_eq]
  constructor
  · intro h i hi
    have h1 := congrArg (fun n => n.testBit i) h
    simp only [Nat.testBit_and, hi, Bool.and_true, fold_bit, Nat.zero_testBit, Bool.false_or,
      List.any_eq_true] at h1
    exact h1
  · intro h
    apply Nat.eq_of_testBit_eq
    intro i
    rw [Nat.testBit_and]
    cases hi : (1008 : ℕ).testBit i
    · simp
    · rw [Bool.and_true, fold_bit, Nat.zero_testBit, Bool.false_or, List.any_eq_true]
      exact h i hi

theorem sg_bit (p t i : ℕ) (hi : (1008 : ℕ).testBit i = true) :
    (sg p t).testBit i = (t.testBit i != t.testBit p) := by
  have h1023 : (1023 : ℕ).testBit i = true := by
    have hlt : i < 10 := by
      by_contra hc
      have h2 : (1008 : ℕ) < 2 ^ i :=
        lt_of_lt_of_le (by norm_num) (Nat.pow_le_pow_right (by norm_num) (not_lt.1 hc))
      rw [Nat.testBit_lt_two_pow h2] at hi
      exact Bool.noConfusion hi
    interval_cases i <;> rfl
  have e : (sg p t).testBit i =
      if t.testBit p = true then (t.testBit i ^^ true) else t.testBit i := by
    unfold sg
    split_ifs with h
    · rw [Nat.testBit_xor, h1023]
    · rfl
  rw [e]
  cases t.testBit i <;> cases t.testBit p <;> rfl

theorem TRN_cov {C : Fin 4 → ℕ → ℕ → Prop} {s : ℕ} {ws : List ℕ}
    (h : TR gN C [1008] s ws) : cov ws = true := by
  have hd := TRN_det h
  have hz := TRN_zp h
  have k1 : ∀ i, (1008 : ℕ).testBit i = true → ∃ t ∈ ws, (id t).testBit i = true := by
    intro i hi
    by_contra hc
    have h1 : ∀ t ∈ ws, t.testBit i = false := by
      intro t ht
      by_contra h2
      exact hc ⟨t, ht, by simpa using h2⟩
    rw [hz i h1] at hi
    exact Bool.noConfusion hi
  have k2 : ∀ p, (1008 : ℕ).testBit p = false → ∀ i, (1008 : ℕ).testBit i = true →
      ∃ t ∈ ws, (sg p t).testBit i = true := by
    intro p hp i hi
    by_contra hc
    have h1 : ∀ t ∈ ws, t.testBit i = t.testBit p := by
      intro t ht
      by_contra h2
      refine hc ⟨t, ht, ?_⟩
      rw [sg_bit p t i hi]
      simpa using h2
    rw [hd i p h1, hp] at hi
    exact Bool.noConfusion hi
  simp only [cov, Bool.and_eq_true, covB_iff]
  exact ⟨⟨⟨⟨k1, k2 0 (by decide)⟩, k2 1 (by decide)⟩, k2 2 (by decide)⟩, k2 3 (by decide)⟩

def tryG (g a b : ℕ) (f : ℕ → Bool) : Bool :=
  match g with
  | 0 => false
  | g' + 1 => g' + 1 != a && g' + 1 != b && f (g' + 1)

theorem tryG_iff (g a b : ℕ) (f : ℕ → Bool) :
    tryG g a b f = true ↔ g ≠ 0 ∧ g ≠ a ∧ g ≠ b ∧ f g = true := by
  cases g <;> simp [tryG, and_assoc]

def search : ℕ → List ℕ → Bool
  | 0, ws => decide (ws = [1008])
  | s + 1, ws =>
    decide (ws.length ≤ s + 2) && cov ws &&
      ws.dedup.any fun a => ws.dedup.any fun b => decide (a < b) &&
        [0, 1, 2, 3].any fun k =>
          tryG (gM k a b) a b fun g =>
            (List.range (s + 3 - ws.length)).any fun u =>
              search s (List.replicate (u + 1) g ++ (ws.erase a).erase b)

theorem search_succ (s : ℕ) (ws : List ℕ) :
    search (s + 1) ws = true ↔ ws.length ≤ s + 2 ∧ cov ws = true ∧
      ∃ a ∈ ws, ∃ b ∈ ws, a < b ∧ ∃ k, k < 4 ∧ gM k a b ≠ 0 ∧ gM k a b ≠ a ∧ gM k a b ≠ b ∧
        ∃ u, u < s + 3 - ws.length ∧
          search s (List.replicate (u + 1) (gM k a b) ++ (ws.erase a).erase b) = true := by
  simp only [search, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true, List.mem_dedup,
    tryG_iff, List.mem_range, and_assoc]
  constructor
  · rintro ⟨h1, h2, a, ha, b, hb, hab, k, hk, h3⟩
    refine ⟨h1, h2, a, ha, b, hb, hab, k, ?_, h3⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
    omega
  · rintro ⟨h1, h2, a, ha, b, hb, hab, k, hk, h3⟩
    refine ⟨h1, h2, a, ha, b, hb, hab, k, ?_, h3⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    omega

theorem cov_perm {xs zs : List ℕ} (hp : xs.Perm zs) (h : cov xs = true) : cov zs = true := by
  simp only [cov, Bool.and_eq_true, covB_iff] at h ⊢
  have key : ∀ f : ℕ → ℕ,
      (∀ i, (1008 : ℕ).testBit i = true → ∃ t ∈ xs, (f t).testBit i = true) →
      ∀ i, (1008 : ℕ).testBit i = true → ∃ t ∈ zs, (f t).testBit i = true :=
    fun f hf i hi => let ⟨t, ht, h3⟩ := hf i hi; ⟨t, hp.mem_iff.1 ht, h3⟩
  exact ⟨⟨⟨⟨key _ h.1.1.1.1, key _ h.1.1.1.2⟩, key _ h.1.1.2⟩, key _ h.1.2⟩, key _ h.2⟩

theorem search_perm : ∀ (s : ℕ) (xs zs : List ℕ), xs.Perm zs → search s xs = true →
    search s zs = true
  | 0, xs, zs, hp, h => by
    simp only [search, decide_eq_true_eq] at h ⊢
    subst h
    exact List.perm_singleton.1 hp.symm
  | s + 1, xs, zs, hp, h => by
    rw [search_succ] at h ⊢
    obtain ⟨h1, h2, a, ha, b, hb, hab, k, hk, h3, h4, h5, u, hu, h6⟩ := h
    refine ⟨hp.length_eq ▸ h1, cov_perm hp h2, a, hp.mem_iff.1 ha, b, hp.mem_iff.1 hb, hab, k,
      hk, h3, h4, h5, u, hp.length_eq ▸ hu, ?_⟩
    exact search_perm s _ _ (List.Perm.append_left _ ((hp.erase a).erase b)) h6

theorem gM_swap (k a b : ℕ) (hk : k < 4) :
    ∃ k', k' < 4 ∧ gM k' b a = gM k a b := by
  interval_cases k
  · exact ⟨0, by omega, by simp [gM, Nat.and_comm]⟩
  · exact ⟨1, by omega, by simp [gM, Nat.or_comm]⟩
  · exact ⟨3, by omega, by simp [gM, Nat.and_comm]⟩
  · exact ⟨2, by omega, by simp [gM, Nat.and_comm]⟩

abbrev NR (s : ℕ) (ws : List ℕ) : Prop :=
  TR gN (strictC gN 0 (fun _ => True) fun t => t < 1024) [1008] s ws

theorem run_search {s : ℕ} {ws : List ℕ} (h : NR s ws) : search s ws = true := by
  refine TR.ind (P := fun s ws => search s ws = true) h (by simp [search]) ?_ ?_
  · intro s xs zs hp _ ih
    exact search_perm s xs zs hp ih
  · intro s a b r k u hc hr ih
    have hrun := TR.step k u hc hr
    obtain ⟨-, -, -, hab, hga, hgb, hgz⟩ := hc
    have hlen := TR.len hr
    simp only [List.length_append, List.length_replicate, List.length_singleton] at hlen
    rw [search_succ]
    refine ⟨by have := TR.len hrun; simpa using this, TRN_cov hrun, ?_⟩
    rcases Nat.lt_or_gt_of_ne hab with hlt | hlt
    · refine ⟨a, by simp, b, by simp, hlt, k.val, k.isLt, hgz, hga, hgb, u, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · have : ((a :: b :: r).erase a).erase b = r := by simp
        rw [this]
        exact ih
    · obtain ⟨k', hk', he⟩ := gM_swap k.val a b k.isLt
      have he' : gM k' b a = gN k a b := he
      refine ⟨b, by simp, a, by simp, hlt, k', hk', by rw [he']; exact hgz, by rw [he']; exact hgb,
        by rw [he']; exact hga, u, ?_, ?_⟩
      · simp only [List.length_cons]; omega
      · rw [he']
        have : ((a :: b :: r).erase b).erase a = r := by
          rw [List.erase_cons_tail (by simpa using hab), List.erase_cons_head,
            List.erase_cons_head]
        rw [this]
        exact ih

def bperm (rho : List ℕ) (t : ℕ) : ℕ := enc (fun i => t.testBit i) rho

theorem bperm_gN (rho : List ℕ) (k : Fin 4) (a b : ℕ) :
    bperm rho (gN k a b) = gN k (bperm rho a) (bperm rho b) := by
  unfold bperm
  rw [← enc_gate]
  congr 1
  funext i
  exact gN_testBit k a b i

theorem NR_perm (rho : List ℕ) (hlen : rho.length = 10)
    (hinv : ∀ t, t < 1024 → bperm rho (bperm rho t) = t) (h0 : bperm rho 0 = 0)
    (h1008 : bperm rho 1008 = 1008) {s : ℕ} {ws : List ℕ} (h : NR s ws) :
    NR s (ws.map (bperm rho)) := by
  have hlt : ∀ t, bperm rho t < 1024 := fun t => by
    have := enc_lt (fun i => t.testBit i) rho
    rw [hlen] at this
    exact this
  have hinj : ∀ a b, a < 1024 → b < 1024 → bperm rho a = bperm rho b → a = b := by
    intro a b ha hb he
    rw [← hinv a ha, ← hinv b hb, he]
  have h1 := TR.map (C' := strictC gN 0 (fun _ => True) fun t => t < 1024) (bperm rho)
    (bperm_gN rho) (by
      rintro k a b ⟨hk, ha, hb, hab, hga, hgb, hgz⟩
      have hg := gN_lt k a b ha hb
      refine ⟨hk, hlt a, hlt b, fun e => hab (hinj a b ha hb e), ?_, ?_, ?_⟩
      · rw [← bperm_gN]; exact fun e => hga (hinj _ _ hg ha e)
      · rw [← bperm_gN]; exact fun e => hgb (hinj _ _ hg hb e)
      · rw [← bperm_gN, ← h0]; exact fun e => hgz (hinj _ _ hg (by norm_num) e)) h
  simp only [List.map_cons, List.map_nil, h1008] at h1
  exact h1

def mk (m0 m1 m2 m3 : ℕ) : List ℕ :=
  List.replicate m0 113 ++ List.replicate m1 402 ++ List.replicate m2 676 ++ List.replicate m3 840

theorem mk_perm (ws : List ℕ) (h : ∀ w ∈ ws, w = 113 ∨ w = 402 ∨ w = 676 ∨ w = 840) :
    ws.Perm (mk (ws.count 113) (ws.count 402) (ws.count 676) (ws.count 840)) := by
  rw [List.perm_iff_count]
  intro a
  simp only [mk, List.count_append, List.count_replicate]
  by_cases h0 : a = 113
  · subst h0; simp
  by_cases h1 : a = 402
  · subst h1; simp
  by_cases h2 : a = 676
  · subst h2; simp
  by_cases h3 : a = 840
  · subst h3; simp
  have : a ∉ ws := fun hm => by rcases h a hm with h | h | h | h <;> contradiction
  simp [List.count_eq_zero_of_not_mem this, Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3]

def Good (s m0 m1 m2 m3 : ℕ) : Prop := ∃ ws : List ℕ, ws.Perm (mk m0 m1 m2 m3) ∧ NR s ws

def rho01 : List ℕ := [1, 0, 2, 3, 4, 7, 8, 5, 6, 9]

def rho12 : List ℕ := [0, 2, 1, 3, 5, 4, 6, 7, 9, 8]

def rho23 : List ℕ := [0, 1, 3, 2, 4, 6, 5, 8, 7, 9]

theorem inv01 : ∀ t, t < 1024 → bperm rho01 (bperm rho01 t) = t := by decide +kernel

theorem inv12 : ∀ t, t < 1024 → bperm rho12 (bperm rho12 t) = t := by decide +kernel

theorem inv23 : ∀ t, t < 1024 → bperm rho23 (bperm rho23 t) = t := by decide +kernel

theorem good01 {s m0 m1 m2 m3 : ℕ} (h : Good s m0 m1 m2 m3) : Good s m1 m0 m2 m3 := by
  obtain ⟨ws, hp, hr⟩ := h
  refine ⟨ws.map (bperm rho01), (hp.map _).trans ?_,
    NR_perm rho01 rfl inv01 (by decide) (by decide) hr⟩
  have e1 : bperm rho01 113 = 402 := by decide
  have e2 : bperm rho01 402 = 113 := by decide
  have e3 : bperm rho01 676 = 676 := by decide
  have e4 : bperm rho01 840 = 840 := by decide
  simp only [mk, List.map_append, List.map_replicate, e1, e2, e3, e4]
  rw [List.perm_iff_count]
  intro a
  simp only [List.count_append, List.count_replicate]
  omega

theorem good12 {s m0 m1 m2 m3 : ℕ} (h : Good s m0 m1 m2 m3) : Good s m0 m2 m1 m3 := by
  obtain ⟨ws, hp, hr⟩ := h
  refine ⟨ws.map (bperm rho12), (hp.map _).trans ?_,
    NR_perm rho12 rfl inv12 (by decide) (by decide) hr⟩
  have e1 : bperm rho12 113 = 113 := by decide
  have e2 : bperm rho12 402 = 676 := by decide
  have e3 : bperm rho12 676 = 402 := by decide
  have e4 : bperm rho12 840 = 840 := by decide
  simp only [mk, List.map_append, List.map_replicate, e1, e2, e3, e4]
  rw [List.perm_iff_count]
  intro a
  simp only [List.count_append, List.count_replicate]
  omega

theorem good23 {s m0 m1 m2 m3 : ℕ} (h : Good s m0 m1 m2 m3) : Good s m0 m1 m3 m2 := by
  obtain ⟨ws, hp, hr⟩ := h
  refine ⟨ws.map (bperm rho23), (hp.map _).trans ?_,
    NR_perm rho23 rfl inv23 (by decide) (by decide) hr⟩
  have e1 : bperm rho23 113 = 113 := by decide
  have e2 : bperm rho23 402 = 402 := by decide
  have e3 : bperm rho23 676 = 840 := by decide
  have e4 : bperm rho23 840 = 676 := by decide
  simp only [mk, List.map_append, List.map_replicate, e1, e2, e3, e4]
  rw [List.perm_iff_count]
  intro a
  simp only [List.count_append, List.count_replicate]
  omega

theorem good_sorted (s : ℕ) : ∀ (n m0 m1 m2 m3 : ℕ), m1 + 2 * m2 + 3 * m3 ≤ n →
    Good s m0 m1 m2 m3 →
    ∃ a b c d, d ≤ c ∧ c ≤ b ∧ b ≤ a ∧ a + b + c + d = m0 + m1 + m2 + m3 ∧ Good s a b c d
  | 0, m0, m1, m2, m3, hn, h => ⟨m0, m1, m2, m3, by omega, by omega, by omega, rfl, h⟩
  | n + 1, m0, m1, m2, m3, hn, h => by
    by_cases h1 : m1 ≤ m0
    · by_cases h2 : m2 ≤ m1
      · by_cases h3 : m3 ≤ m2
        · exact ⟨m0, m1, m2, m3, h3, h2, h1, rfl, h⟩
        · obtain ⟨a, b, c, d, q1, q2, q3, q4, q5⟩ :=
            good_sorted s n m0 m1 m3 m2 (by omega) (good23 h)
          exact ⟨a, b, c, d, q1, q2, q3, by omega, q5⟩
      · obtain ⟨a, b, c, d, q1, q2, q3, q4, q5⟩ :=
          good_sorted s n m0 m2 m1 m3 (by omega) (good12 h)
        exact ⟨a, b, c, d, q1, q2, q3, by omega, q5⟩
    · obtain ⟨a, b, c, d, q1, q2, q3, q4, q5⟩ :=
        good_sorted s n m1 m0 m2 m3 (by omega) (good01 h)
      exact ⟨a, b, c, d, q1, q2, q3, by omega, q5⟩

def searchS (s : ℕ) : Bool :=
  (List.range (s + 2)).any fun m0 => (List.range (m0 + 1)).any fun m1 =>
    (List.range (m1 + 1)).any fun m2 => (List.range (m2 + 1)).any fun m3 =>
      search s (mk m0 m1 m2 m3)

theorem run_searchS {s : ℕ} {ws : List ℕ} (h : NR s ws)
    (hw : ∀ w ∈ ws, w = 113 ∨ w = 402 ∨ w = 676 ∨ w = 840) : searchS s = true := by
  have hp := mk_perm ws hw
  have hl := TR.len h
  rw [hp.length_eq] at hl
  simp only [mk, List.length_append, List.length_replicate, List.length_singleton] at hl
  obtain ⟨a, b, c, d, q1, q2, q3, q4, ws', hp', hr'⟩ :=
    good_sorted s _ _ _ _ _ le_rfl ⟨ws, hp, h⟩
  have hs := search_perm s _ _ hp' (run_search hr')
  simp only [searchS, List.any_eq_true, List.mem_range]
  exact ⟨a, by omega, b, by omega, c, by omega, d, by omega, hs⟩

set_option maxRecDepth 100000 in
theorem searchS_false : (List.range 7).all (fun s => !searchS s) = true := by
  decide +kernel

theorem U4 (ι : Fin 4 → Fin 5) (hι : Function.Injective ι) (F : BF)
    (hs : ∀ j, F (singleInput (ι j)) = false)
    (hp : ∀ j j', j ≠ j' → F (pairInput (ι j) (ι j')) = true) :
    ¬ UC gF (fun _ => True) 6 (fun w => ∃ j, w = var (ι j)) F := by
  intro hu
  let rows : List (Fin 5 → Bool) := [singleInput (ι 0), singleInput (ι 1), singleInput (ι 2),
    singleInput (ι 3), pairInput (ι 0) (ι 1), pairInput (ι 0) (ι 2), pairInput (ι 0) (ι 3),
    pairInput (ι 1) (ι 2), pairInput (ι 1) (ι 3), pairInput (ι 2) (ι 3)]
  have hF : enc F rows = 1008 := by
    simp only [rows, enc, hs, hp 0 1 (by decide), hp 0 2 (by decide), hp 0 3 (by decide),
      hp 1 2 (by decide), hp 1 3 (by decide), hp 2 3 (by decide)]
    rfl
  have hv : ∀ j, enc (var (ι j)) rows = 113 ∨ enc (var (ι j)) rows = 402 ∨
      enc (var (ι j)) rows = 676 ∨ enc (var (ι j)) rows = 840 := by
    intro j
    fin_cases j <;>
      simp [rows, enc, var, singleInput, pairInput, hι.eq_iff, Nat.bit]
  have hu2 : UC gN (fun _ => True) 6
      (fun w => w = 113 ∨ w = 402 ∨ w = 676 ∨ w = 840) (enc F rows) :=
    UC_map (fun w => enc w rows) (fun k a b => enc_gF k a b rows) 6 _ _ F
      (by rintro w ⟨j, rfl⟩; exact hv j) hu
  rw [hF] at hu2
  obtain ⟨t', ht, ws, hws, hr⟩ := normalize gN 0 (fun _ => True) (fun t => t < 1024) gN_lt
    gN_zero_left gN_zero_right gN_self 6 _ 1008
    (by rintro w (rfl | rfl | rfl | rfl) <;> norm_num) (by decide) hu2
  have h1 := run_searchS hr fun w hw => (hws w hw).1
  have h2 := searchS_false
  rw [List.all_eq_true] at h2
  have h3 := h2 t' (List.mem_range.2 (by omega))
  rw [h1] at h3
  exact Bool.noConfusion h3

def zF : BF := fun _ => false

def rst (p : Fin 5) (a : BF) : BF := fun x => a (Function.update x p false)

def ThrL (V : Fin 5 → Prop) (F : BF) : Prop :=
  (∀ i, V i → F (singleInput i) = false) ∧
    ∀ i j, V i → V j → i ≠ j → F (pairInput i j) = true

theorem gF_zero_left (k : Fin 4) (b : BF) : gF k zF b = zF ∨ gF k zF b = b := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_zero_right (k : Fin 4) (a : BF) : gF k a zF = zF ∨ gF k a zF = a := by
  fin_cases k
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_self (k : Fin 4) (a : BF) : gF k a a = zF ∨ gF k a a = a := by
  fin_cases k
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inr (funext fun x => by simp [gF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])
  · exact Or.inl (funext fun x => by simp [gF, zF, zeroGate])

theorem gF_zero_zero (k : Fin 4) : gF k zF zF = zF := by
  fin_cases k <;> exact funext fun x => by simp [gF, zF, zeroGate]

theorem upd_single {i p : Fin 5} (h : i ≠ p) :
    Function.update (singleInput i) p false = singleInput i := by
  funext m
  by_cases hm : m = p
  · subst hm; simp [singleInput, Ne.symm h]
  · simp [Function.update_of_ne hm]

theorem upd_pair {i j p : Fin 5} (hi : i ≠ p) (hj : j ≠ p) :
    Function.update (pairInput i j) p false = pairInput i j := by
  funext m
  by_cases hm : m = p
  · subst hm; simp [pairInput, Ne.symm hi, Ne.symm hj]
  · simp [Function.update_of_ne hm]

theorem rst_var_self (p : Fin 5) : rst p (var p) = zF :=
  funext fun x => by simp [rst, var, zF]

theorem rst_var_ne {i p : Fin 5} (h : i ≠ p) : rst p (var i) = var i :=
  funext fun x => by simp [rst, var, Function.update_of_ne h]

theorem var_inj {i j : Fin 5} (h : var i = var j) : i = j := by
  have := congrFun h (singleInput i)
  exact (by simpa [var, singleInput] using this : j = i).symm

theorem TRF_det {C : Fin 4 → BF → BF → Prop} {ys : List BF} {s : ℕ} {ws : List BF}
    (h : TR gF C ys s ws) (x x' : Fin 5 → Bool) :
    (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x' := by
  refine TR.ind (P := fun _ ws => (∀ w ∈ ws, w x = w x') → ∀ y ∈ ys, y x = y x') h
    (fun h => h) ?_ ?_
  · intro s xs zs hp _ ih hz
    exact ih fun t ht => hz t (hp.mem_iff.1 ht)
  · intro s a b r k u _ _ ih hz
    apply ih
    intro t ht
    rcases List.mem_append.1 ht with ht | ht
    · rw [List.eq_of_mem_replicate ht]
      show zeroGate k (a x) (b x) = zeroGate k (a x') (b x')
      rw [hz a (by simp), hz b (by simp)]
    · exact hz t (by simp [ht])

def dcount (p : Fin 5) (ws : List BF) : ℕ := ws.countP fun w => decide (rst p w = zF)

theorem dcount_cons (p : Fin 5) (a : BF) (l : List BF) :
    dcount p (a :: l) = dcount p l + if rst p a = zF then 1 else 0 := by
  simp [dcount, List.countP_cons]

theorem dcount_rep (p : Fin 5) (n : ℕ) (g : BF) (r : List BF) :
    dcount p (List.replicate n g ++ r) = (if rst p g = zF then n else 0) + dcount p r := by
  simp only [dcount, List.countP_append, List.countP_replicate]
  split_ifs <;> simp_all

theorem pot_dead {A : Fin 4 → Prop} (p : Fin 5) {F : BF} (hF : rst p F ≠ zF) {s : ℕ}
    {ws : List BF} (h : TR gF (fun k _ _ => A k) [F] s ws) :
    dcount p ws ≤ s ∧ ∀ S : BF → Prop, (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) →
      UC gF A (s - dcount p ws) S (rst p F) := by
  refine TR.ind (P := fun s ws => dcount p ws ≤ s ∧ ∀ S : BF → Prop,
    (∀ w ∈ ws, rst p w ≠ zF → S (rst p w)) → UC gF A (s - dcount p ws) S (rst p F)) h ?_ ?_ ?_
  · refine ⟨by simp [dcount, hF], fun S hS => ?_⟩
    have : dcount p [F] = 0 := by simp [dcount, hF]
    rw [this]
    exact hS F (by simp) hF
  · intro s xs zs hp _ ih
    have hc : dcount p zs = dcount p xs := (hp.countP_eq _).symm
    rw [hc]
    exact ⟨ih.1, fun S hS => ih.2 S fun w hw => hS w (hp.mem_iff.1 hw)⟩
  · intro s a b r k u hk _ ih
    obtain ⟨ih1, ih2⟩ := ih
    have hg : rst p (gF k a b) = gF k (rst p a) (rst p b) := rfl
    rw [dcount_rep] at ih1 ih2
    rw [dcount_cons, dcount_cons]
    have hmem : ∀ (S : BF → Prop), (∀ w ∈ a :: b :: r, rst p w ≠ zF → S (rst p w)) →
        ∀ w ∈ r, rst p w ≠ zF → S (rst p w) := fun S hS w hw => hS w (by simp [hw])
    by_cases ha : rst p a = zF <;> by_cases hb : rst p b = zF
    · have hgz : rst p (gF k a b) = zF := by rw [hg, ha, hb, gF_zero_zero]
      simp only [hgz, ha, hb, ite_true] at ih1 ih2 ⊢
      refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
      intro w hw hwz
      rcases List.mem_append.1 hw with hw | hw
      · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
      · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hgb : rst p (gF k a b) = rst p b := by
          rcases gF_zero_left k (rst p b) with h | h
          · exact absurd (by rw [hg, ha, h]) hgz
          · rw [hg, ha, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hgb]
          exact hS b (by simp) hb
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · have hga : rst p (gF k a b) = rst p a := by
          rcases gF_zero_right k (rst p a) with h | h
          · exact absurd (by rw [hg, hb, h]) hgz
          · rw [hg, hb, h]
        simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hga]
          exact hS a (by simp) ha
        · exact hmem S hS w hw hwz
    · by_cases hgz : rst p (gF k a b) = zF
      · simp only [hgz, ha, hb, ite_true, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => UC_le (by omega) (ih2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hgz) hwz
        · exact hmem S hS w hw hwz
      · simp only [hgz, ha, hb, ite_false] at ih1 ih2 ⊢
        refine ⟨by omega, fun S hS => ?_⟩
        have h1 := ih2 (fun w => w = gF k (rst p a) (rst p b) ∨ S w) (by
          intro w hw hwz
          rcases List.mem_append.1 hw with hw | hw
          · exact Or.inl (by rw [List.eq_of_mem_replicate hw, hg])
          · exact Or.inr (hmem S hS w hw hwz))
        have h2 := UC_gate k (rst p a) (rst p b) hk (hS a (by simp) ha) (hS b (by simp) hb) h1
        exact UC_le (by omega) h2

theorem ex_third : ∀ p q : Fin 5, ∃ r, r ≠ p ∧ r ≠ q := by decide

theorem thr_rst {F : BF} (hF : ThrL (fun _ => True) F) (p : Fin 5) :
    (∀ j, rst p F (singleInput (p.succAbove j)) = false) ∧
    (∀ j j', j ≠ j' → rst p F (pairInput (p.succAbove j) (p.succAbove j')) = true) := by
  refine ⟨fun j => ?_, fun j j' hj => ?_⟩
  · show F (Function.update (singleInput (p.succAbove j)) p false) = false
    rw [upd_single (Fin.succAbove_ne p j)]
    exact hF.1 _ trivial
  · show F (Function.update (pairInput (p.succAbove j) (p.succAbove j')) p false) = true
    rw [upd_pair (Fin.succAbove_ne p j) (Fin.succAbove_ne p j')]
    exact hF.2 _ _ trivial trivial fun h => hj (Fin.succAbove_right_injective h)

theorem thr_rst_ne {F : BF} (hF : ThrL (fun _ => True) F) (p : Fin 5) : rst p F ≠ zF := by
  intro h
  have := (thr_rst hF p).2 0 1 (by decide)
  rw [h] at this
  exact Bool.noConfusion this

theorem U5T {F : BF} (hF : ThrL (fun _ => True) F) {s : ℕ} {ws : List BF}
    (h : TR gF (fun _ _ _ => True) [F] s ws) (hw : ∀ w ∈ ws, ∃ i, w = var i) : 9 ≤ s := by
  rcases s with _ | s
  · have hp := (TR.inv h).1 rfl
    obtain ⟨i, hi⟩ := hw F (hp.mem_iff.2 (by simp))
    have := hF.1 i trivial
    rw [hi] at this
    simp [var, singleInput] at this
  · obtain ⟨k, u, a, b, r, -, hp, hr⟩ := (TR.inv h).2 s rfl
    obtain ⟨p, rfl⟩ := hw a (hp.mem_iff.2 (by simp))
    obtain ⟨q, rfl⟩ := hw b (hp.mem_iff.2 (by simp))
    have hcnt : dcount p ws = dcount p (var p :: var q :: r) := hp.countP_eq _
    have key : 2 ≤ dcount p ws := by
      rw [hcnt, dcount_cons, dcount_cons]
      by_cases hpq : p = q
      · subst hpq; simp [rst_var_self]
      by_cases hmem : var p ∈ r
      · have : 1 ≤ dcount p r := by
          unfold dcount
          exact List.countP_pos_iff.2 ⟨var p, hmem, by simp [rst_var_self]⟩
        simp only [rst_var_self, ite_true]
        omega
      exfalso
      have hrv : ∀ w ∈ r, ∃ i, i ≠ p ∧ w = var i := by
        intro w hw'
        obtain ⟨i, hi⟩ := hw w (hp.mem_iff.2 (by simp [hw']))
        refine ⟨i, ?_, hi⟩
        rintro rfl
        exact hmem (hi ▸ hw')
      obtain ⟨β, c, hβ⟩ := (zeroGate_canalizes k).1
      cases β
      · obtain ⟨r₀, hr1, hr2⟩ := ex_third p q
        have hd := TRF_det hr (pairInput p r₀) (singleInput r₀) (by
          intro w hw'
          rcases List.mem_append.1 hw' with hw' | hw'
          · rw [List.eq_of_mem_replicate hw']
            have e1 : var q (pairInput p r₀) = false := by
              simp [var, pairInput, Ne.symm hpq, Ne.symm hr2]
            have e2 : var q (singleInput r₀) = false := by simp [var, singleInput, Ne.symm hr2]
            show zeroGate k (var p _) (var q _) = zeroGate k (var p _) (var q _)
            rw [e1, e2, hβ, hβ]
          · obtain ⟨i, hi, rfl⟩ := hrv w hw'
            simp [var, pairInput, singleInput, hi]) F (by simp)
        rw [hF.1 r₀ trivial, hF.2 p r₀ trivial trivial (Ne.symm hr1)] at hd
        exact Bool.noConfusion hd
      · have hd := TRF_det hr (pairInput p q) (singleInput q) (by
          intro w hw'
          rcases List.mem_append.1 hw' with hw' | hw'
          · rw [List.eq_of_mem_replicate hw']
            have e1 : var q (pairInput p q) = true := by simp [var, pairInput]
            have e2 : var q (singleInput q) = true := by simp [var, singleInput]
            show zeroGate k (var p _) (var q _) = zeroGate k (var p _) (var q _)
            rw [e1, e2, hβ, hβ]
          · obtain ⟨i, hi, rfl⟩ := hrv w hw'
            simp [var, pairInput, singleInput, hi]) F (by simp)
        rw [hF.1 q trivial, hF.2 p q trivial trivial hpq] at hd
        exact Bool.noConfusion hd
    obtain ⟨h1, h2⟩ := pot_dead p (thr_rst_ne hF p) h
    have h3 := h2 (fun w => ∃ j, w = var (p.succAbove j)) (by
      intro w hw' hwz
      obtain ⟨i, rfl⟩ := hw w hw'
      by_cases hi : i = p
      · subst hi; exact absurd (rst_var_self i) hwz
      · obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hi
        exact ⟨j, by rw [rst_var_ne hi, hj]⟩)
    by_contra hlt
    exact U4 p.succAbove Fin.succAbove_right_injective (rst p F) (thr_rst hF p).1
      (thr_rst hF p).2 (UC_le (by omega) h3)

theorem thr_ne_zero {F : BF} (hF : ThrL (fun _ => True) F) : F ≠ zF := by
  intro h
  have := hF.2 0 1 trivial trivial (by decide)
  rw [h] at this
  exact Bool.noConfusion this

theorem to_run {A : Fin 4 → Prop} {F : BF} (hF : ThrL (fun _ => True) F) {t : ℕ}
    (hu : UC gF A t (fun w => ∃ i, w = var i) F) :
    ∃ t', t' ≤ t ∧ ∃ ws : List BF, (∀ w ∈ ws, ∃ i, w = var i) ∧
      TR gF (fun k _ _ => A k) [F] t' ws := by
  obtain ⟨t', ht, ws, hws, hr⟩ := normalize gF zF A (fun _ => True) (fun _ _ _ _ _ => trivial)
    gF_zero_left gF_zero_right gF_self t _ F (fun _ _ => trivial) (thr_ne_zero hF) hu
  exact ⟨t', ht, ws, fun w hw => (hws w hw).1, TR.monoC (fun _ _ _ h => h.1) hr⟩

theorem U5 {F : BF} (hF : ThrL (fun _ => True) F) {t : ℕ}
    (hu : UC gF (fun _ => True) t (fun w => ∃ i, w = var i) F) : 9 ≤ t := by
  obtain ⟨t', ht, ws, hws, hr⟩ := to_run hF hu
  have := U5T hF hr hws
  omega

def MonoA : Fin 4 → Prop := fun k => k.val < 2

abbrev MR (ys : List BF) (s : ℕ) (ws : List BF) : Prop := TR gF (fun k _ _ => MonoA k) ys s ws

def outF (ys : List BF) : BF := fun x => ys.any fun y => y x

def otop (x : Fin 5) : BF := fun p => decide (∃ i, i ≠ x ∧ p i = true)

theorem mono_cases (k : Fin 4) (hk : MonoA k) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp_all [MonoA]

theorem gF_and (a b : BF) : gF 0 a b = fun p => a p && b p := rfl

theorem gF_or (a b : BF) : gF 1 a b = fun p => a p || b p := rfl

theorem UC_monoA {α : Type} {G : Fin 4 → α → α → α} {A A' : Fin 4 → Prop}
    (hA : ∀ k, A k → A' k) :
    ∀ (t : ℕ) (S : α → Prop) (f : α), UC G A t S f → UC G A' t S f
  | 0, _, _, hu => hu
  | t + 1, S, f, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (UC_monoA hA t S f hu)
    · exact Or.inr ⟨k, a, b, hA k hk, ha, hb, UC_monoA hA t _ f hu⟩

theorem top_elim (O : BF) :
    ∀ (m : ℕ) (S : BF → Prop) (F : BF), (∀ w, S w → ∀ p, w p = true → O p = true) → F ≠ O →
      UC gF MonoA m (fun w => w = O ∨ S w) F → UC gF MonoA m S F
  | 0, S, F, _, hF, hu => by
    rcases hu with h | h
    · exact absurd h hF
    · exact h
  | m + 1, S, F, hS, hF, hu => by
    rcases hu with hu | ⟨k, a, b, hk, ha, hb, hu⟩
    · exact Or.inl (top_elim O m S F hS hF hu)
    · have hle : ∀ w, (w = O ∨ S w) → ∀ p, w p = true → O p = true := by
        rintro w (rfl | hw) p hp
        · exact hp
        · exact hS w hw p hp
      have free : (gF k a b = O ∨ S (gF k a b)) → UC gF MonoA (m + 1) S F := by
        intro hg
        refine Or.inl (top_elim O m S F hS hF (UC_monoS gF MonoA m _ _ F ?_ hu))
        rintro w (rfl | hw)
        · exact hg
        · exact hw
      by_cases hao : a = O
      · subst hao
        apply free
        rcases mono_cases k hk with rfl | rfl
        · have : gF 0 a b = b := by
            rw [gF_and]
            funext p
            cases hbp : b p
            · simp
            · simp [hle b hb p hbp]
          rw [this]; exact hb
        · have : gF 1 a b = a := by
            rw [gF_or]
            funext p
            cases hbp : b p
            · simp
            · simp [hle b hb p hbp]
          rw [this]; exact Or.inl rfl
      by_cases hbo : b = O
      · subst hbo
        apply free
        rcases mono_cases k hk with rfl | rfl
        · have : gF 0 a b = a := by
            rw [gF_and]
            funext p
            cases hap : a p
            · simp
            · simp [hle a ha p hap]
          rw [this]; exact ha
        · have : gF 1 a b = b := by
            rw [gF_or]
            funext p
            cases hap : a p
            · simp
            · simp [hle a ha p hap]
          rw [this]; exact Or.inl rfl
      have ha' : S a := ha.resolve_left hao
      have hb' : S b := hb.resolve_left hbo
      refine UC_gate k a b hk ha' hb' (top_elim O m _ F ?_ hF (UC_monoS gF MonoA m _ _ F ?_ hu))
      · rintro w (rfl | hw) p hp
        · rcases mono_cases k hk with rfl | rfl
          · rw [gF_and] at hp
            simp only [Bool.and_eq_true] at hp
            exact hS a ha' p hp.1
          · rw [gF_or] at hp
            simp only [Bool.or_eq_true] at hp
            rcases hp with hp | hp
            · exact hS a ha' p hp
            · exact hS b hb' p hp
        · exact hS w hw p hp
      · rintro w (rfl | rfl | hw)
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl rfl
        · exact Or.inr (Or.inr hw)

theorem outF_true (ys : List BF) (p : Fin 5 → Bool) :
    outF ys p = true ↔ ∃ y ∈ ys, y p = true := by
  simp [outF]

theorem outF_congr (ys : List BF) (p p' : Fin 5 → Bool) (h : ∀ y ∈ ys, y p = y p') :
    outF ys p = outF ys p' := by
  rw [Bool.eq_iff_iff, outF_true, outF_true]
  constructor
  · rintro ⟨y, hy, hp⟩; exact ⟨y, hy, by rw [← h y hy]; exact hp⟩
  · rintro ⟨y, hy, hp⟩; exact ⟨y, hy, by rw [h y hy]; exact hp⟩

theorem or_chain : ∀ (ys : List BF) (y : BF), MR [outF (y :: ys)] ys.length (y :: ys)
  | [], y => by
    have : outF [y] = y := funext fun x => by simp [outF]
    rw [this]
    exact TR.done
  | y2 :: rest, y => by
    have h := or_chain rest (gF 1 y y2)
    have e : outF (gF 1 y y2 :: rest) = outF (y :: y2 :: rest) :=
      funext fun x => by simp [outF, gF_or, Bool.or_assoc]
    rw [e] at h
    exact TR.step (r := rest) 1 0 (by simp [MonoA]) h

theorem complete_run (y0 : BF) (yt : List BF) {s : ℕ} {ws : List BF} (h : MR (y0 :: yt) s ws) :
    MR [outF (y0 :: yt)] (s + yt.length) ws := by
  refine TR.ind (P := fun s ws => MR [outF (y0 :: yt)] (s + yt.length) ws) h ?_ ?_ ?_
  · rw [Nat.zero_add]; exact or_chain yt y0
  · intro s xs zs hp _ ih; exact TR.perm hp ih
  · intro s a b r k u hc _ ih
    have e : s + 1 + yt.length = s + yt.length + 1 := by omega
    rw [e]
    exact TR.step k u hc ih

theorem frame (h0 : BF) {ys : List BF} {s : ℕ} {ws : List BF} (h : MR ys s ws) :
    MR (h0 :: ys) s (h0 :: ws) := by
  refine TR.ind (P := fun s ws => MR (h0 :: ys) s (h0 :: ws)) h TR.done ?_ ?_
  · intro s xs zs hp _ ih; exact TR.perm (hp.cons h0) ih
  · intro s a b r k u hc _ ih
    have p1 : (a :: b :: h0 :: r).Perm (h0 :: a :: b :: r) :=
      List.perm_middle (l₁ := [a, b])
    have p2 : (h0 :: (List.replicate (u + 1) (gF k a b) ++ r)).Perm
        (List.replicate (u + 1) (gF k a b) ++ h0 :: r) := List.perm_middle.symm
    exact TR.perm p1 (TR.step k u hc (TR.perm p2 ih))

def XI (x : Fin 5) (w : BF) : Prop := ∀ p b, w (Function.update p x b) = w p

def MonoF (w : BF) : Prop :=
  ∀ p q : Fin 5 → Bool, (∀ i, p i = true → q i = true) → w p = true → w q = true

def InvX (x : Fin 5) (w : BF) : Prop := XI x w ∧ MonoF w ∧ w (fun _ => false) = false

theorem InvX_gate {x : Fin 5} {k : Fin 4} (hk : MonoA k) {a b : BF} (ha : InvX x a)
    (hb : InvX x b) : InvX x (gF k a b) := by
  rcases mono_cases k hk with rfl | rfl
  · refine ⟨fun p v => ?_, fun p q hpq h => ?_, ?_⟩
    · show (a _ && b _) = (a _ && b _)
      rw [ha.1 p v, hb.1 p v]
    · rw [gF_and] at h ⊢
      simp only [Bool.and_eq_true] at h ⊢
      exact ⟨ha.2.1 p q hpq h.1, hb.2.1 p q hpq h.2⟩
    · show (a _ && b _) = false
      rw [ha.2.2]; rfl
  · refine ⟨fun p v => ?_, fun p q hpq h => ?_, ?_⟩
    · show (a _ || b _) = (a _ || b _)
      rw [ha.1 p v, hb.1 p v]
    · rw [gF_or] at h ⊢
      simp only [Bool.or_eq_true] at h ⊢
      exact h.imp (ha.2.1 p q hpq) (hb.2.1 p q hpq)
    · show (a _ || b _) = false
      rw [ha.2.2, hb.2.2]; rfl

theorem InvX_var {x m : Fin 5} (h : m ≠ x) : InvX x (var m) :=
  ⟨fun p v => by simp [var, Function.update_of_ne h], fun p q hpq hp => hpq m hp, rfl⟩

theorem mono_comm {k : Fin 4} (hk : MonoA k) (a b : BF) : gF k a b = gF k b a := by
  rcases mono_cases k hk with rfl | rfl
  · rw [gF_and, gF_and]; funext p; exact Bool.and_comm _ _
  · rw [gF_or, gF_or]; funext p; exact Bool.or_comm _ _

theorem upd_single_true (i x : Fin 5) :
    Function.update (singleInput i) x true = pairInput i x := by
  funext m
  by_cases hm : m = x
  · subst hm; simp [pairInput]
  · simp [singleInput, pairInput, hm]

theorem single_eq_upd (x : Fin 5) :
    singleInput x = Function.update (fun _ => false) x true := by
  funext m
  by_cases hm : m = x
  · subst hm; simp [singleInput]
  · simp [singleInput, hm]

theorem outF_rel (b' : BF) (p : Fin 5 → Bool) (hb : b' p = false) :
    ∀ (ys ys' : List BF), List.Forall₂ (fun w w' => ∀ q, b' q = false → w q = w' q) ys ys' →
      outF ys p = outF ys' p
  | _, _, List.Forall₂.nil => rfl
  | _, _, List.Forall₂.cons h t => by
    have ih := outF_rel b' p hb _ _ t
    simp only [outF, List.any_cons] at ih ⊢
    rw [h p hb, ih]

def SUc (x : Fin 5) (y0 : BF) (yt : List BF) (s : ℕ) (r : List BF) : Prop :=
  ((if otop x ∈ r then 2 else 3) ≤ s + yt.length ∧
    ∀ S : BF → Prop, (∀ w ∈ r, S w) → S (otop x) →
      UC gF MonoA (s + yt.length - (if otop x ∈ r then 2 else 3)) S
        (rst x (outF (y0 :: yt)))) ∨
  ∃ (c : ℕ) (h0 : BF) (ys' : List BF) (s' : ℕ), s = s' + 1 ∧ ys'.length = yt.length + 1 ∧
    ThrL (fun _ => True) (outF (h0 :: ys')) ∧
    MR (h0 :: ys') s' (List.replicate (c + 1) (var x) ++ r)

theorem SU (x : Fin 5) (y0 : BF) (yt : List BF)
    (hF : ThrL (fun _ => True) (outF (y0 :: yt))) :
    ∀ (s : ℕ) (r : List BF), MR (y0 :: yt) s (var x :: r) → (∀ w ∈ r, InvX x w) →
      SUc x y0 yt s r := by
  intro s
  induction s with
  | zero =>
    intro r h _
    exfalso
    have hp := (TR.inv h).1 rfl
    have hm : var x ∈ y0 :: yt := hp.mem_iff.1 (by simp)
    have h1 : outF (y0 :: yt) (singleInput x) = true :=
      (outF_true _ _).2 ⟨var x, hm, by simp [var, singleInput]⟩
    rw [hF.1 x trivial] at h1
    exact Bool.noConfusion h1
  | succ s ih =>
    intro r h hinv
    obtain ⟨k, u, a, b, r₁, hk, hp, hr⟩ := (TR.inv h).2 s rfl
    have consume : ∀ b' : BF, r.Perm (b' :: r₁) → gF k a b = gF k (var x) b' →
        SUc x y0 yt (s + 1) r := by
      intro b' hrp hg
      unfold SUc
      rw [hg] at hr
      have hb' : InvX x b' := hinv b' (hrp.mem_iff.2 (by simp))
      have hr1 : ∀ w ∈ r₁, InvX x w := fun w hw => hinv w (hrp.mem_iff.2 (by simp [hw]))
      have sens : ∀ i, i ≠ x → gF k (var x) b' (pairInput i x) =
          gF k (var x) b' (singleInput i) → False := by
        intro i hi hgg
        have hd := TRF_det hr (pairInput i x) (singleInput i) (by
          intro w hw
          rcases List.mem_append.1 hw with hw | hw
          · rw [List.eq_of_mem_replicate hw]; exact hgg
          · rw [← upd_single_true]
            exact (hr1 w hw).1 _ _)
        have h2 := outF_congr _ _ _ hd
        rw [hF.1 i trivial, hF.2 i x trivial trivial hi] at h2
        exact Bool.noConfusion h2
      have hbx : ∀ i, i ≠ x → b' (pairInput i x) = b' (singleInput i) := fun i _ => by
        rw [← upd_single_true]; exact hb'.1 _ _
      have hv1 : ∀ i, var x (pairInput i x) = true := fun i => by simp [var, pairInput]
      have hv2 : ∀ i, i ≠ x → var x (singleInput i) = false := fun i hi => by
        simp [var, singleInput, Ne.symm hi]
      rcases mono_cases k hk with rfl | rfl
      · left
        have hone : ∀ i, i ≠ x → b' (singleInput i) = true := by
          intro i hi
          by_contra hc
          have hc' : b' (singleInput i) = false := by simpa using hc
          apply sens i hi
          rw [gF_and]
          show (var x _ && b' _) = (var x _ && b' _)
          rw [hbx i hi, hc', hv2 i hi]; simp
        have hbo : b' = otop x := by
          funext p
          rw [← hb'.1 p false]
          by_cases hex : ∃ i, i ≠ x ∧ p i = true
          · obtain ⟨i, hi, hpi⟩ := hex
            have : otop x p = true := by simp only [otop, decide_eq_true_eq]; exact ⟨i, hi, hpi⟩
            rw [this]
            refine hb'.2.1 (singleInput i) _ ?_ (hone i hi)
            intro m hm
            have : m = i := by simpa [singleInput] using hm
            subst this
            rw [Function.update_of_ne hi]; exact hpi
          · have : otop x p = false := by simp only [otop, decide_eq_false_iff_not]; exact hex
            rw [this]
            have hz : Function.update p x false = fun _ => false := by
              funext m
              by_cases hm : m = x
              · subst hm; simp
              · rw [Function.update_of_ne hm]
                by_contra hc
                exact hex ⟨m, hm, by simpa using hc⟩
            rw [hz]; exact hb'.2.2
        have hmem : otop x ∈ r := hrp.mem_iff.2 (by simp [hbo])
        have hdead : rst x (gF 0 (var x) b') = zF := by
          funext p
          show (var x _ && b' _) = false
          simp [var]
        have hc := complete_run y0 yt hr
        obtain ⟨hd1, hd2⟩ := pot_dead x (thr_rst_ne hF x) hc
        rw [dcount_rep] at hd1 hd2
        simp only [hdead, ite_true] at hd1 hd2
        simp only [hmem, ite_true]
        refine ⟨by omega, fun S hS _ => UC_le (by omega) (hd2 S ?_)⟩
        intro w hw hwz
        rcases List.mem_append.1 hw with hw | hw
        · exact absurd (List.eq_of_mem_replicate hw ▸ hdead) hwz
        · have : rst x w = w := funext fun p => (hr1 w hw).1 p false
          rw [this]
          exact hS w (hrp.mem_iff.2 (by simp [hw]))
      · right
        have hzero : ∀ i, b' (singleInput i) = false := by
          intro i
          by_cases hi : i = x
          · subst hi
            rw [single_eq_upd, hb'.1]; exact hb'.2.2
          · by_contra hc
            have hc' : b' (singleInput i) = true := by simpa using hc
            apply sens i hi
            rw [gF_or]
            show (var x _ || b' _) = (var x _ || b' _)
            rw [hbx i hi, hc', hv1 i]; simp
        have hrel : List.Forall₂ (fun w w' => ∀ q, b' q = false → w q = w' q)
            (List.replicate (u + 1) (gF 1 (var x) b') ++ r₁)
            (List.replicate (u + 1) (var x) ++ r₁) := by
          refine List.rel_append ?_ (List.forall₂_same.2 fun _ _ _ _ => rfl)
          generalize u + 1 = n
          induction n with
          | zero => exact List.Forall₂.nil
          | succ n ihn =>
            refine List.Forall₂.cons (fun q hq => ?_) ihn
            show (var x q || b' q) = var x q
            rw [hq]; simp
        obtain ⟨ys', hy, hrun⟩ := TR.rel (A := MonoA)
          (fun w w' => ∀ q, b' q = false → w q = w' q)
          (fun k a a' b b' ha hb q hq => by
            show zeroGate k (a q) (b q) = zeroGate k (a' q) (b' q)
            rw [ha q hq, hb q hq]) hr _ hrel
        refine ⟨u, b', ys', s, rfl, ?_, ⟨fun i _ => ?_, fun i j _ _ hij => ?_⟩, ?_⟩
        · have := hy.length_eq
          simpa using this.symm
        · have e := outF_rel b' (singleInput i) (hzero i) _ _ hy
          have h3 : outF (b' :: ys') (singleInput i) =
              (b' (singleInput i) || outF ys' (singleInput i)) := by simp [outF]
          rw [h3, hzero i, ← e, hF.1 i trivial]; rfl
        · have h3 : outF (b' :: ys') (pairInput i j) =
              (b' (pairInput i j) || outF ys' (pairInput i j)) := by simp [outF]
          rw [h3]
          cases hbp : b' (pairInput i j)
          · have e := outF_rel b' (pairInput i j) hbp _ _ hy
            rw [← e, hF.2 i j trivial trivial hij]; rfl
          · rfl
        · have p1 : (b' :: (List.replicate (u + 1) (var x) ++ r₁)).Perm
              (List.replicate (u + 1) (var x) ++ r) :=
            List.perm_middle.symm.trans (List.Perm.append_left _ hrp.symm)
          exact TR.perm p1 (frame b' hrun)
    by_cases hax : a = var x
    · subst hax
      exact consume b hp.cons_inv rfl
    by_cases hbx : b = var x
    · subst hbx
      have hp' : (var x :: r).Perm (var x :: a :: r₁) := hp.trans (List.Perm.swap _ _ _)
      exact consume a hp'.cons_inv (mono_comm hk a (var x))
    have hx1 : var x ∈ r₁ := by
      have : var x ∈ a :: b :: r₁ := hp.mem_iff.1 (by simp)
      simp only [List.mem_cons] at this
      rcases this with h1 | h1 | h1
      · exact absurd h1.symm hax
      · exact absurd h1.symm hbx
      · exact h1
    obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hx1
    have hr2 : r.Perm (a :: b :: (l₁ ++ l₂)) := by
      have p1 : (a :: b :: (l₁ ++ var x :: l₂)).Perm (var x :: a :: b :: (l₁ ++ l₂)) :=
        List.perm_middle (l₁ := a :: b :: l₁)
      exact (hp.trans p1).cons_inv
    have ha : InvX x a := hinv a (hr2.mem_iff.2 (by simp))
    have hb : InvX x b := hinv b (hr2.mem_iff.2 (by simp))
    have hsub : ∀ w ∈ l₁ ++ l₂, w ∈ r := fun w hw => hr2.mem_iff.2 (by simp [List.mem_append.1 hw])
    have p2 : (List.replicate (u + 1) (gF k a b) ++ (l₁ ++ var x :: l₂)).Perm
        (var x :: (List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂))) := by
      rw [← List.append_assoc, ← List.append_assoc]
      exact List.perm_middle
    have hinv2 : ∀ w ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂), InvX x w := by
      intro w hw
      rcases List.mem_append.1 hw with hw | hw
      · rw [List.eq_of_mem_replicate hw]; exact InvX_gate hk ha hb
      · exact hinv w (hsub w hw)
    have hih := ih _ (TR.perm p2 hr) hinv2
    unfold SUc at hih ⊢
    rcases hih with ⟨hA1, hA2⟩ | ⟨c, h0, ys', s', hs', hl, hthr, hrun⟩
    · left
      by_cases hgo : gF k a b = otop x
      · have hm : otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂) := by
          rw [hgo]; simp
        simp only [hm, ite_true] at hA1 hA2
        refine ⟨by split_ifs <;> omega, fun S hS hSo => ?_⟩
        refine UC_le (by split_ifs <;> omega) (hA2 S ?_ hSo)
        intro w hw
        rcases List.mem_append.1 hw with hw | hw
        · rw [List.eq_of_mem_replicate hw, hgo]; exact hSo
        · exact hS w (hsub w hw)
      · have hiff : otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂) → otop x ∈ r := by
          intro hm
          rcases List.mem_append.1 hm with hm | hm
          · exact absurd (List.eq_of_mem_replicate hm).symm hgo
          · exact hsub _ hm
        have hcc : (if otop x ∈ r then 2 else 3) ≤
            (if otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂) then 2 else 3) := by
          by_cases h1 : otop x ∈ List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂)
          · simp [h1, hiff h1]
          · simp only [h1, ite_false]; split_ifs <;> omega
        refine ⟨by omega, fun S hS hSo => ?_⟩
        have h1 := hA2 (fun w => w = gF k a b ∨ S w) (by
          intro w hw
          rcases List.mem_append.1 hw with hw | hw
          · exact Or.inl (List.eq_of_mem_replicate hw)
          · exact Or.inr (hS w (hsub w hw))) (Or.inr hSo)
        have h2 := UC_gate k a b hk (hS a (hr2.mem_iff.2 (by simp)))
          (hS b (hr2.mem_iff.2 (by simp))) h1
        exact UC_le (by omega) h2
    · right
      refine ⟨c, h0, ys', s' + 1, by omega, hl, hthr, ?_⟩
      have p3 : (List.replicate (c + 1) (var x) ++ r).Perm
          (a :: b :: (List.replicate (c + 1) (var x) ++ (l₁ ++ l₂))) := by
        refine (List.Perm.append_left _ hr2).trans ?_
        exact List.perm_middle.trans (List.Perm.cons a List.perm_middle)
      have p4 : (List.replicate (c + 1) (var x) ++
          (List.replicate (u + 1) (gF k a b) ++ (l₁ ++ l₂))).Perm
          (List.replicate (u + 1) (gF k a b) ++
            (List.replicate (c + 1) (var x) ++ (l₁ ++ l₂))) :=
        List.perm_append_comm_assoc _ _ _
      subst hs'
      exact TR.perm p3.symm (TR.step k u hk (TR.perm p4 hrun))

theorem map_perm_cons {β γ : Type} (f : β → γ) {l : List β} {a : γ} {r : List γ}
    (h : (l.map f).Perm (a :: r)) :
    ∃ x l', l.Perm (x :: l') ∧ f x = a ∧ (l'.map f).Perm r := by
  have ha : a ∈ l.map f := h.mem_iff.2 (by simp)
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 ha
  obtain ⟨l₁, l₂, rfl⟩ := List.append_of_mem hx
  refine ⟨x, l₁ ++ l₂, List.perm_middle, rfl, ?_⟩
  have h1 := (List.perm_middle (a := x) (l₁ := l₁) (l₂ := l₂)).map f
  exact (h1.symm.trans h).cons_inv

def occSum (ts : List (Formula 5)) (i : Fin 5) : ℕ := (ts.map fun t => formOcc t i).sum

theorem occSum_perm {ts ts' : List (Formula 5)} (h : ts.Perm ts') (i : Fin 5) :
    occSum ts i = occSum ts' i := (h.map _).sum_eq

theorem forest {ys : List BF} {s : ℕ} {ws : List BF} (h : MR ys s ws) :
    ∀ ts : List (Formula 5), (ts.map formEval).Perm ws → ws.length = s + ys.length →
      ∃ ts' : List (Formula 5), (ts'.map formEval).Perm ys ∧
        ∀ i, occSum ts' i = occSum ts i := by
  refine TR.ind (P := fun s ws => ∀ ts : List (Formula 5), (ts.map formEval).Perm ws →
    ws.length = s + ys.length → ∃ ts' : List (Formula 5), (ts'.map formEval).Perm ys ∧
      ∀ i, occSum ts' i = occSum ts i) h ?_ ?_ ?_
  · intro ts hts _
    exact ⟨ts, hts, fun _ => rfl⟩
  · intro s xs zs hp _ ih ts hts hlen
    exact ih ts (hts.trans hp.symm) (by rw [hp.length_eq]; exact hlen)
  · intro s a b r k u hk hr ih ts hts hlen
    have hl := TR.len hr
    simp only [List.length_append, List.length_replicate, List.length_cons] at hl hlen
    obtain rfl : u = 0 := by omega
    obtain ⟨ta, ts₁, hp1, rfl, h1⟩ := map_perm_cons formEval hts
    obtain ⟨tb, ts₂, hp2, rfl, h2⟩ := map_perm_cons formEval h1
    have hev : formEval (BinaryTree.node (Sum.inr (decide (k = 0))) ta tb : Formula 5) =
        gF k (formEval ta) (formEval tb) := by
      rcases mono_cases k hk with rfl | rfl
      · funext x; simp [formEval, gF_and]
      · funext x; simp [formEval, gF_or]
    obtain ⟨ts', hy, hocc⟩ := ih (BinaryTree.node (Sum.inr (decide (k = 0))) ta tb :: ts₂)
      (by
        rw [List.map_cons, hev]
        exact h2.cons _)
      (by simp only [List.length_append, List.length_replicate]; omega)
    refine ⟨ts', hy, fun i => ?_⟩
    rw [hocc i, occSum_perm hp1 i]
    have e2 := occSum_perm hp2 i
    simp only [occSum, List.map_cons, List.sum_cons, formOcc] at e2 ⊢
    omega

def orAll : List (Formula 5) → Formula 5
  | [] => BinaryTree.nil
  | t :: l => BinaryTree.node (Sum.inr false) t (orAll l)

theorem orAll_eval : ∀ (l : List (Formula 5)) (p : Fin 5 → Bool),
    formEval (orAll l) p = outF (l.map formEval) p
  | [], p => by simp [orAll, formEval, outF]
  | t :: l, p => by
    have ih := orAll_eval l p
    simp only [orAll, formEval, outF, List.map_cons, List.any_cons] at ih ⊢
    rw [ih]

theorem orAll_occ : ∀ (l : List (Formula 5)) (i : Fin 5), formOcc (orAll l) i = occSum l i
  | [], i => by simp [orAll, formOcc, occSum]
  | t :: l, i => by
    have ih := orAll_occ l i
    simp only [orAll, formOcc, occSum, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih]

def leafF (i : Fin 5) : Formula 5 := BinaryTree.node (Sum.inl i) BinaryTree.nil BinaryTree.nil

theorem leaf_eval (idx : List (Fin 5)) : (idx.map leafF).map formEval = idx.map var := by
  rw [List.map_map]
  apply List.map_congr_left
  intro i _
  funext x
  simp [leafF, formEval, var]

theorem leaf_occ : ∀ (idx : List (Fin 5)) (i : Fin 5), occSum (idx.map leafF) i = idx.count i
  | [], i => by simp [occSum]
  | j :: idx, i => by
    have ih := leaf_occ idx i
    simp only [occSum, List.map_cons, List.sum_cons, leafF, formOcc, List.count_cons] at ih ⊢
    rw [ih]
    by_cases h : j = i
    · simp [h]; omega
    · simp [h]

theorem vars_list : ∀ (ws : List BF), (∀ w ∈ ws, ∃ i, w = var i) →
    ∃ idx : List (Fin 5), ws = idx.map var
  | [], _ => ⟨[], rfl⟩
  | w :: ws, h => by
    obtain ⟨i, rfl⟩ := h w (by simp)
    obtain ⟨idx, rfl⟩ := vars_list ws fun w hw => h w (by simp [hw])
    exact ⟨i :: idx, rfl⟩

theorem len_counts : ∀ (idx : List (Fin 5)),
    idx.length = idx.count 0 + idx.count 1 + idx.count 2 + idx.count 3 + idx.count 4
  | [] => rfl
  | j :: idx => by
    have ih := len_counts idx
    fin_cases j <;> simp <;> omega

theorem outF_perm {ys ys' : List BF} (h : ys.Perm ys') (p : Fin 5 → Bool) :
    outF ys p = outF ys' p := h.any_eq

theorem GS : ∀ (s : ℕ) (y0 : BF) (yt : List BF) (ws : List BF), MR (y0 :: yt) s ws →
    (∀ w ∈ ws, ∃ i, w = var i) → s + yt.length = 9 →
    ThrL (fun _ => True) (outF (y0 :: yt)) → False := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro y0 yt ws h hw hs hF
    have hlen := TR.len h
    obtain ⟨idx, rfl⟩ := vars_list ws hw
    have hpres : ∀ i, i ∈ idx := by
      intro i
      by_contra hi
      obtain ⟨j, hj, -⟩ := ex_third i i
      have hd := TRF_det h (pairInput i j) (singleInput j) (by
        intro w hw'
        obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hw'
        have : m ≠ i := fun e => hi (e ▸ hm)
        simp [var, pairInput, singleInput, this])
      have h2 := outF_congr _ _ _ hd
      rw [hF.1 j trivial, hF.2 i j trivial trivial (Ne.symm hj)] at h2
      exact Bool.noConfusion h2
    simp only [List.length_map, List.length_cons] at hlen
    by_cases hall : ∀ i, 2 ≤ idx.count i
    · have hc := len_counts idx
      have h0 := hall 0
      have h1 := hall 1
      have h2 := hall 2
      have h3 := hall 3
      have h4 := hall 4
      have hle : ∀ i, idx.count i ≤ 2 := by
        intro i
        fin_cases i
        · show idx.count 0 ≤ 2; omega
        · show idx.count 1 ≤ 2; omega
        · show idx.count 2 ≤ 2; omega
        · show idx.count 3 ≤ 2; omega
        · show idx.count 4 ≤ 2; omega
      obtain ⟨ts', hy, hocc⟩ := forest h (idx.map leafF) (by rw [leaf_eval])
        (by simp only [List.length_map, List.length_cons]; omega)
      refine no_readtwice_five (orAll ts') ?_ ?_ ?_
      · intro i; rw [orAll_occ, hocc, leaf_occ]; exact hle i
      · intro i; rw [orAll_eval, outF_perm hy]; exact hF.1 i trivial
      · intro i j hij; rw [orAll_eval, outF_perm hy]; exact hF.2 i j trivial trivial hij
    · obtain ⟨x, hx⟩ := not_forall.1 hall
      have hx1 : idx.count x = 1 := by
        have := List.count_pos_iff.2 (hpres x)
        omega
      have hp : (idx.map var).Perm (var x :: (idx.erase x).map var) :=
        (List.perm_cons_erase (hpres x)).map var
      have hnx : x ∉ idx.erase x := by
        intro hm
        have := List.count_pos_iff.2 hm
        rw [List.count_erase_self] at this
        omega
      have hinv : ∀ w ∈ (idx.erase x).map var, InvX x w := by
        intro w hw'
        obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hw'
        exact InvX_var fun e => hnx (e ▸ hm)
      have hsu := SU x y0 yt hF s _ (TR.perm hp h) hinv
      unfold SUc at hsu
      rcases hsu with ⟨hA1, hA2⟩ | ⟨c, h0, ys', s', hs', hl, hthr, hrun⟩
      · have hno : otop x ∉ (idx.erase x).map var := by
          intro hm
          obtain ⟨m, -, he⟩ := List.mem_map.1 hm
          obtain ⟨j, hj1, hj2⟩ := ex_third m x
          have h5 := congrFun he (singleInput j)
          have h6 : var m (singleInput j) = false := by simp [var, singleInput, Ne.symm hj1]
          have h7 : otop x (singleInput j) = true := by
            simp only [otop, decide_eq_true_eq]
            exact ⟨j, hj2, by simp [singleInput]⟩
          rw [h6, h7] at h5
          exact Bool.noConfusion h5
        simp only [hno, ite_false] at hA1 hA2
        have h6 := hA2 (fun w => w = otop x ∨ ∃ j, w = var (x.succAbove j)) (by
          intro w hw'
          obtain ⟨m, hm, rfl⟩ := List.mem_map.1 hw'
          have hmx : m ≠ x := fun e => hnx (e ▸ hm)
          obtain ⟨j, hj⟩ := Fin.exists_succAbove_eq hmx
          exact Or.inr ⟨j, by rw [hj]⟩) (Or.inl rfl)
        have h7 := top_elim (otop x) _ (fun w => ∃ j, w = var (x.succAbove j)) _ (by
          rintro w ⟨j, rfl⟩ p hp'
          simp only [otop, decide_eq_true_eq]
          exact ⟨x.succAbove j, Fin.succAbove_ne x j, hp'⟩) (by
          intro he
          have h8 := (thr_rst hF x).1 0
          rw [he] at h8
          have h9 : otop x (singleInput (x.succAbove 0)) = true := by
            simp only [otop, decide_eq_true_eq]
            exact ⟨x.succAbove 0, Fin.succAbove_ne x 0, by simp [singleInput]⟩
          rw [h9] at h8
          exact Bool.noConfusion h8) h6
        have h8 := UC_monoA (A' := fun _ => True) (fun _ _ => trivial) _ _ _ h7
        exact U4 x.succAbove Fin.succAbove_right_injective _ (thr_rst hF x).1 (thr_rst hF x).2
          (UC_le (by omega) h8)
      · refine ih s' (by omega) h0 ys' _ hrun ?_ (by omega) hthr
        intro w hw'
        rcases List.mem_append.1 hw' with hw' | hw'
        · exact ⟨x, List.eq_of_mem_replicate hw'⟩
        · obtain ⟨m, -, rfl⟩ := List.mem_map.1 hw'
          exact ⟨m, rfl⟩

theorem M5 {F : BF} (hF : ThrL (fun _ => True) F) :
    ¬ UC gF MonoA 9 (fun w => ∃ i, w = var i) F := by
  intro hu
  obtain ⟨t', ht, ws, hws, hr⟩ := to_run hF hu
  have h9 := U5T hF (TR.monoC (fun _ _ _ _ => trivial) hr) hws
  have ht9 : t' = 9 := by omega
  subst ht9
  have e : outF [F] = F := funext fun x => by simp [outF]
  exact GS 9 F [] ws hr hws rfl (by rw [e]; exact hF)

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def gv (g : Gate) (W : List BF) : BF :=
  fun x => g.op.eval (g.inputs.map fun i => (W.getD i zF) x)

def wiresF : List Gate → List BF → List BF
  | [], W => W
  | g :: gs, W => wiresF gs (W ++ [gv g W])

theorem getD_map_x (W : List BF) (i : ℕ) (x : Fin 5 → Bool) :
    (W.map fun w => w x).getD i false = (W.getD i zF) x := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases W[i]? <;> rfl

theorem wires_eq (x : Fin 5 → Bool) : ∀ (gs : List Gate) (W : List BF),
    gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (W.map fun w => w x) = (wiresF gs W).map fun w => w x
  | [], W => rfl
  | g :: gs, W => by
    simp only [List.foldl_cons, wiresF]
    rw [← wires_eq x gs (W ++ [gv g W])]
    congr 1
    simp only [List.map_append, List.map_cons, List.map_nil, gv, getD_map_x]

theorem getD_mem (W : List BF) (i : ℕ) : W.getD i zF ∈ W ∨ W.getD i zF = zF := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : W[i]? with _ | a
  · exact Or.inr rfl
  · exact Or.inl (List.mem_of_getElem? h)

theorem gate_form (g : Gate) (W : List BF)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) :
    gv g W = zF ∨ gv g W = (fun _ => true) ∨
    (∃ a, (a ∈ W ∨ a = zF) ∧ gv g W = a) ∨
    (∃ a, (a ∈ W ∨ a = zF) ∧ gv g W = fun x => !a x) ∨
    (∃ k a b, MonoA k ∧ (a ∈ W ∨ a = zF) ∧ (b ∈ W ∨ b = zF) ∧ gv g W = gF k a b) := by
  rcases g with ⟨op, ins⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
  rcases ins with _ | ⟨i, _ | ⟨j, _ | ⟨l, rest⟩⟩⟩
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inl (funext fun x => by simp [gv, GateOp.eval]))
    · exact Or.inl (funext fun x => by simp [gv, GateOp.eval, zF])
    · exact Or.inr (Or.inl (funext fun x => by simp [gv, GateOp.eval]))
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩))
    · exact Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩)))
  · rcases hop with rfl | rfl | rfl
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨0, W.getD i zF, W.getD j zF, by simp [MonoA],
        getD_mem W i, getD_mem W j, funext fun x => by simp [gv, GateOp.eval, gF_and]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨1, W.getD i zF, W.getD j zF, by simp [MonoA],
        getD_mem W i, getD_mem W j, funext fun x => by simp [gv, GateOp.eval, gF_or]⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨W.getD i zF, getD_mem W i,
        funext fun x => by simp [gv, GateOp.eval]⟩)))
  · simp at hl

def ori (w : BF) : BF := fun x => xor (w x) (w fun _ => false)

theorem ori_zero : ori zF = zF := funext fun x => by simp [ori, zF]

theorem ori_true : ori (fun _ => true) = zF := funext fun x => by simp [ori, zF]

theorem ori_not (a : BF) : ori (fun x => !a x) = ori a :=
  funext fun x => by
    simp only [ori]
    cases a x <;> cases a (fun _ => false) <;> rfl

theorem ori_zp {w : BF} (h : w (fun _ => false) = false) : ori w = w :=
  funext fun x => by simp [ori, h]

theorem ori_gate (k : Fin 4) (hk : MonoA k) (a b : BF) :
    ∃ k', ori (gF k a b) = gF k' (ori a) (ori b) := by
  rcases mono_cases k hk with rfl | rfl
  · cases hu : a (fun _ => false) <;> cases hv : b (fun _ => false)
    · exact ⟨0, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨2, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨3, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨1, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
  · cases hu : a (fun _ => false) <;> cases hv : b (fun _ => false)
    · exact ⟨1, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨3, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨2, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩
    · exact ⟨0, funext fun x => by
        cases hax : a x <;> cases hbx : b x <;> simp [ori, gF, zeroGate, hu, hv, hax, hbx]⟩

abbrev GOK (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem ori_key (g : Gate) (W : List BF) (S : BF → Prop)
    (hop : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp))
    (hl : g.inputs.length ≤ 2) (hW : ∀ w ∈ W, ori w = zF ∨ S (ori w)) :
    (ori (gv g W) = zF ∨ S (ori (gv g W))) ∨
      ∃ k a b, S a ∧ S b ∧ ori (gv g W) = gF k a b := by
  have hWz : ∀ a, (a ∈ W ∨ a = zF) → ori a = zF ∨ S (ori a) := by
    rintro a (h | rfl)
    · exact hW a h
    · exact Or.inl ori_zero
  rcases gate_form g W hop hl with h | h | ⟨a, ha, h⟩ | ⟨a, ha, h⟩ | ⟨k, a, b, hk, ha, hb, h⟩
  · rw [h]; exact Or.inl (Or.inl ori_zero)
  · rw [h]; exact Or.inl (Or.inl ori_true)
  · rw [h]; exact Or.inl (hWz a ha)
  · rw [h, ori_not]; exact Or.inl (hWz a ha)
  · obtain ⟨k', hk'⟩ := ori_gate k hk a b
    rw [h, hk']
    rcases hWz a ha with ha1 | ha1
    · rw [ha1]
      rcases gF_zero_left k' (ori b) with e | e
      · rw [e]; exact Or.inl (Or.inl rfl)
      · rw [e]; exact Or.inl (hWz b hb)
    rcases hWz b hb with hb1 | hb1
    · rw [hb1]
      rcases gF_zero_right k' (ori a) with e | e
      · rw [e]; exact Or.inl (Or.inl rfl)
      · rw [e]; exact Or.inl (Or.inr ha1)
    exact Or.inr ⟨k', ori a, ori b, ha1, hb1, rfl⟩

theorem trans1 : ∀ (gs : List Gate) (W : List BF) (S : BF → Prop), GOK gs →
    (∀ w ∈ W, ori w = zF ∨ S (ori w)) → ∀ o : ℕ,
    ori ((wiresF gs W).getD o zF) = zF ∨
      UC gF (fun _ => True) gs.length S (ori ((wiresF gs W).getD o zF))
  | [], W, S, _, hW, o => by
    simp only [wiresF]
    rcases getD_mem W o with h | h
    · exact hW _ h
    · rw [h]; exact Or.inl ori_zero
  | g :: gs, W, S, hg, hW, o => by
    simp only [wiresF, List.length_cons]
    have hg1 := hg g (by simp)
    have hrest : GOK gs := fun g' h => hg g' (by simp [h])
    rcases ori_key g W S hg1.1 hg1.2 hW with h | ⟨k, a, b, ha, hb, h⟩
    · have h1 := trans1 gs (W ++ [gv g W]) S hrest (by
        intro w hw
        rcases List.mem_append.1 hw with hw | hw
        · exact hW w hw
        · rw [List.mem_singleton.1 hw]; exact h) o
      exact h1.imp id (UC_le (Nat.le_succ _))
    · have h1 := trans1 gs (W ++ [gv g W]) (fun w => w = gF k a b ∨ S w) hrest (by
        intro w hw
        rcases List.mem_append.1 hw with hw | hw
        · exact (hW w hw).imp id Or.inr
        · rw [List.mem_singleton.1 hw]; exact Or.inr (Or.inl h)) o
      exact h1.imp id (UC_gate k a b trivial ha hb)

theorem gF_zp (k : Fin 4) {a b : BF} (ha : a (fun _ => false) = false)
    (hb : b (fun _ => false) = false) : gF k a b (fun _ => false) = false := by
  show zeroGate k _ _ = false
  rw [ha, hb]
  fin_cases k <;> rfl

def T2c (n : ℕ) (S : BF → Prop) (F : BF) : Prop :=
  ori F = zF ∨ (∃ m, n = m + 1 ∧ UC gF (fun _ => True) m S (ori F)) ∨ UC gF MonoA n S F

theorem trans2 : ∀ (gs : List Gate) (W : List BF) (S : BF → Prop), GOK gs →
    (∀ w, S w → w (fun _ => false) = false) → (∀ w ∈ W, w = zF ∨ S w) → ∀ o : ℕ,
    T2c gs.length S ((wiresF gs W).getD o zF)
  | [], W, S, _, _, hW, o => by
    simp only [wiresF]
    unfold T2c
    rcases getD_mem W o with h | h
    · rcases hW _ h with h1 | h1
      · rw [h1]; exact Or.inl ori_zero
      · exact Or.inr (Or.inr h1)
    · rw [h]; exact Or.inl ori_zero
  | g :: gs, W, S, hg, hS, hW, o => by
    simp only [wiresF, List.length_cons]
    have hg1 := hg g (by simp)
    have hrest : GOK gs := fun g' h => hg g' (by simp [h])
    have hWz : ∀ a, (a ∈ W ∨ a = zF) → a = zF ∨ S a := by
      rintro a (h | rfl)
      · exact hW a h
      · exact Or.inl rfl
    have hWo : ∀ w ∈ W, ori w = zF ∨ S (ori w) := by
      intro w hw
      rcases hW w hw with rfl | h
      · exact Or.inl ori_zero
      · rw [ori_zp (hS w h)]; exact Or.inr h
    have free : (gv g W = zF ∨ S (gv g W)) →
        T2c (gs.length + 1) S ((wiresF gs (W ++ [gv g W])).getD o zF) := fun hfree => by
      have h1 := trans2 gs (W ++ [gv g W]) S hrest hS (by
        intro w hw
        rcases List.mem_append.1 hw with hw | hw
        · exact hW w hw
        · rw [List.mem_singleton.1 hw]; exact hfree) o
      unfold T2c at h1 ⊢
      rcases h1 with h1 | ⟨m, hm, h1⟩ | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨m + 1, by omega, UC_le (Nat.le_succ _) h1⟩)
      · exact Or.inr (Or.inr (UC_le (Nat.le_succ _) h1))
    have nonmono : (ori (gv g W) = zF ∨ S (ori (gv g W))) →
        T2c (gs.length + 1) S ((wiresF gs (W ++ [gv g W])).getD o zF) := fun hn => by
      have h1 := trans1 gs (W ++ [gv g W]) S hrest (by
        intro w hw
        rcases List.mem_append.1 hw with hw | hw
        · exact hWo w hw
        · rw [List.mem_singleton.1 hw]; exact hn) o
      unfold T2c
      rcases h1 with h1 | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨gs.length, rfl, h1⟩)
    rcases gate_form g W hg1.1 hg1.2 with h | h | ⟨a, ha, h⟩ | ⟨a, ha, h⟩ |
      ⟨k, a, b, hk, ha, hb, h⟩
    · exact free (Or.inl h)
    · exact nonmono (by rw [h]; exact Or.inl ori_true)
    · exact free (by rw [h]; exact hWz a ha)
    · refine nonmono ?_
      rw [h, ori_not]
      rcases hWz a ha with rfl | h2
      · exact Or.inl ori_zero
      · rw [ori_zp (hS a h2)]; exact Or.inr h2
    · rcases hWz a ha with rfl | ha1
      · refine free ?_
        rw [h]
        rcases gF_zero_left k b with e | e
        · exact Or.inl e
        · rw [e]; exact hWz b hb
      rcases hWz b hb with rfl | hb1
      · refine free ?_
        rw [h]
        rcases gF_zero_right k a with e | e
        · exact Or.inl e
        · rw [e]; exact Or.inr ha1
      have h1 := trans2 gs (W ++ [gv g W]) (fun w => w = gF k a b ∨ S w) hrest (by
        rintro w (rfl | hw)
        · exact gF_zp k (hS a ha1) (hS b hb1)
        · exact hS w hw) (by
        intro w hw
        rcases List.mem_append.1 hw with hw | hw
        · exact (hW w hw).imp id Or.inr
        · rw [List.mem_singleton.1 hw]; exact Or.inr (Or.inl h)) o
      unfold T2c at h1 ⊢
      rcases h1 with h1 | ⟨m, hm, h1⟩ | h1
      · exact Or.inl h1
      · exact Or.inr (Or.inl ⟨m + 1, by omega, UC_gate k a b trivial ha1 hb1 h1⟩)
      · exact Or.inr (Or.inr (UC_gate k a b hk ha1 hb1 h1))

abbrev T25 : BF := fun x : Fin 5 → Bool => (x 0 && x 1) || (x 0 && x 2) || (x 0 && x 3) ||
  (x 0 && x 4) || (x 1 && x 2) || (x 1 && x 3) || (x 1 && x 4) || (x 2 && x 3) || (x 2 && x 4) ||
  (x 3 && x 4)

theorem T25_thr : ThrL (fun _ => True) T25 := by
  refine ⟨fun i _ => ?_, fun i j _ _ => ?_⟩
  · revert i; decide
  · revert i j; decide

theorem main (t : ℕ) (h : HasCircuitSize 5 T25 t) : 10 ≤ t := by
  obtain ⟨C, hfan, hsize, hev⟩ := h
  by_contra hlt
  have hlen : C.gates.length ≤ 9 := by
    have : C.size = C.gates.length := rfl
    omega
  have hF : (wiresF C.gates (List.ofFn var)).getD C.output zF = T25 := by
    funext x
    rw [← hev x, ← getD_map_x, ← wires_eq]
    simp only [Circuit.eval, Circuit.wires, List.map_ofFn]
    rfl
  have hz : T25 (fun _ => false) = false := rfl
  have h2 := trans2 C.gates (List.ofFn var) (fun w => ∃ i, w = var i) hfan
    (by rintro w ⟨i, rfl⟩; rfl)
    (by
      intro w hw
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hw
      exact Or.inr ⟨i, rfl⟩) C.output
  unfold T2c at h2
  rw [hF, ori_zp hz] at h2
  rcases h2 with h2 | ⟨m, hm, h2⟩ | h2
  · exact thr_ne_zero T25_thr h2
  · have := U5 T25_thr h2
    omega
  · exact M5 T25_thr (UC_le hlen h2)

end Threshold

namespace Dual

open PEqualNP.CircuitLowerBounds

def dualGate (k : ℕ) : Gate → Gate
  | ⟨GateOp.and, l⟩ => if l.all (fun i => decide (i < k)) then ⟨GateOp.or, l⟩ else ⟨GateOp.and, []⟩
  | ⟨GateOp.or, l⟩ => ⟨GateOp.and, l.filter (fun i => decide (i < k))⟩
  | ⟨GateOp.not, l⟩ => if l.headD k < k then ⟨GateOp.not, l⟩ else ⟨GateOp.or, []⟩
  | ⟨GateOp.mod m, l⟩ => ⟨GateOp.mod m, l⟩
  | ⟨GateOp.maj, l⟩ => ⟨GateOp.maj, l⟩

def dualList : ℕ → List Gate → List Gate
  | _, [] => []
  | k, g :: gs => dualGate k g :: dualList (k + 1) gs

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma getD_snoc_lt (L : List Bool) (v : Bool) (j : ℕ) (hj : j < L.length) :
    (L ++ [v]).getD j false = L.getD j false := by
  rw [List.getD_eq_getElem _ _ (by simp; omega), List.getD_eq_getElem _ _ hj,
    List.getElem_append_left hj]

lemma getD_snoc_eq (L : List Bool) (v : Bool) (k : ℕ) (hk : L.length = k) :
    (L ++ [v]).getD k false = v := by
  subst hk
  simp

lemma any_neg (l : List ℕ) (k : ℕ) (W W' : List Bool)
    (hneg : ∀ i < k, W'.getD i false = !(W.getD i false)) (hl : ∀ i ∈ l, i < k) :
    (l.map fun i => W'.getD i false).any id = !((l.map fun i => W.getD i false).all id) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp only [List.map_cons, List.any_cons, List.all_cons, id_eq]
    rw [ih (fun i hi => hl i (List.mem_cons_of_mem _ hi)), hneg a (hl a List.mem_cons_self)]
    cases W.getD a false <;> simp

lemma all_neg (l : List ℕ) (k : ℕ) (W W' : List Bool)
    (hneg : ∀ i < k, W'.getD i false = !(W.getD i false))
    (hbig : ∀ i, k ≤ i → W.getD i false = false) :
    ((l.filter fun i => decide (i < k)).map fun i => W'.getD i false).all id =
      !((l.map fun i => W.getD i false).any id) := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    by_cases ha : a < k
    · rw [List.filter_cons_of_pos (by simpa using ha)]
      simp only [List.map_cons, List.any_cons, List.all_cons, id_eq]
      rw [ih, hneg a ha]
      cases W.getD a false <;> simp
    · rw [List.filter_cons_of_neg (by simpa using ha)]
      simp only [List.map_cons, List.any_cons, id_eq]
      rw [ih, hbig a (by omega)]
      simp

lemma gate_dual (k : ℕ) (g : Gate)
    (hg : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (W W' : List Bool) (hW : W.length = k)
    (hneg : ∀ i < k, W'.getD i false = !(W.getD i false)) :
    (dualGate k g).op.eval ((dualGate k g).inputs.map fun i => W'.getD i false) =
      !(g.op.eval (g.inputs.map fun i => W.getD i false)) := by
  have hbig : ∀ i, k ≤ i → W.getD i false = false := by
    intro i hi
    rw [List.getD_eq_default _ _ (by omega)]
  obtain ⟨op, l⟩ := g
  simp only at hg
  rcases hg with h | h | h <;> subst h
  · by_cases hall : l.all (fun i => decide (i < k)) = true
    · simp only [dualGate, hall, if_true, GateOp.eval]
      apply any_neg l k W W' hneg
      intro i hi
      rw [List.all_eq_true] at hall
      simpa using hall i hi
    · simp only [dualGate, hall, GateOp.eval]
      simp only [Bool.false_eq_true, if_false, List.map_nil, List.all_nil]
      have hex : ∃ i ∈ l, ¬ i < k := by
        simp only [List.all_eq_true, decide_eq_true_eq, not_forall] at hall
        obtain ⟨i, hi, hik⟩ := hall
        exact ⟨i, hi, hik⟩
      obtain ⟨i, hi, hik⟩ := hex
      have hf : (l.map fun i => W.getD i false).all id = false := by
        rw [Bool.eq_false_iff]
        intro hcon
        rw [List.all_eq_true] at hcon
        have h1 := hcon (W.getD i false) (List.mem_map_of_mem hi)
        rw [hbig i (by omega)] at h1
        simp at h1
      rw [hf]
      rfl
  · simp only [dualGate, GateOp.eval]
    exact all_neg l k W W' hneg hbig
  · cases l with
    | nil =>
      simp [dualGate, GateOp.eval]
    | cons a t =>
      by_cases ha : a < k
      · simp only [dualGate, List.headD_cons, ha, if_true, GateOp.eval, List.map_cons]
        rw [hneg a ha]
      · simp only [dualGate, List.headD_cons, ha, if_false, GateOp.eval, List.map_cons]
        rw [hbig a (by omega)]
        rfl

lemma fold_dual (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    ∀ (k : ℕ) (W W' : List Bool), W.length = k → W'.length = k →
      (∀ i < k, W'.getD i false = !(W.getD i false)) →
      ∀ i < k + gs.length,
        ((dualList k gs).foldl step W').getD i false = !((gs.foldl step W).getD i false) := by
  induction gs with
  | nil =>
    intro k W W' hW hW' hneg i hi
    simp only [List.length_nil, Nat.add_zero] at hi
    exact hneg i hi
  | cons g gs ih =>
    intro k W W' hW hW' hneg i hi
    simp only [dualList, List.foldl_cons]
    apply ih (fun g' hg' => hg g' (List.mem_cons_of_mem _ hg')) (k + 1)
    · simp [step, hW]
    · simp [step, hW']
    · intro j hj
      by_cases hjk : j < k
      · rw [step, step, getD_snoc_lt _ _ _ (by omega), getD_snoc_lt _ _ _ (by omega)]
        exact hneg j hjk
      · have hj' : j = k := by omega
        subst hj'
        rw [step, step, getD_snoc_eq _ _ _ hW, getD_snoc_eq _ _ _ hW']
        exact gate_dual j g (hg g List.mem_cons_self) W W' hW hneg
    · simp only [List.length_cons] at hi
      omega

lemma dualList_length : ∀ (k : ℕ) (gs : List Gate), (dualList k gs).length = gs.length
  | _, [] => rfl
  | k, g :: gs => by simp [dualList, dualList_length (k + 1) gs]

lemma mem_dualList : ∀ (gs : List Gate) (k : ℕ) (g' : Gate), g' ∈ dualList k gs →
    ∃ k' : ℕ, ∃ g ∈ gs, g' = dualGate k' g := by
  intro gs
  induction gs with
  | nil =>
    intro k g' h
    simp [dualList] at h
  | cons g gs ih =>
    intro k g' h
    simp only [dualList, List.mem_cons] at h
    rcases h with h | h
    · exact ⟨k, g, List.mem_cons_self, h⟩
    · obtain ⟨k', g0, hg0, he⟩ := ih (k + 1) g' h
      exact ⟨k', g0, List.mem_cons_of_mem _ hg0, he⟩

lemma getElem?_dualList : ∀ (gs : List Gate) (k i : ℕ),
    (dualList k gs)[i]? = (gs[i]?).map (dualGate (k + i)) := by
  intro gs
  induction gs with
  | nil =>
    intro k i
    simp [dualList]
  | cons g gs ih =>
    intro k i
    cases i with
    | zero => simp [dualList]
    | succ i =>
      simp only [dualList, List.getElem?_cons_succ]
      rw [ih (k + 1) i]
      congr 2
      omega

lemma dualGate_ok (k : ℕ) (g : Gate)
    (h : (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2) :
    ((dualGate k g).op = GateOp.and ∨ (dualGate k g).op = GateOp.or ∨
      (dualGate k g).op = GateOp.not) ∧ (dualGate k g).inputs.length ≤ 2 := by
  obtain ⟨op, l⟩ := g
  obtain ⟨hop, hl⟩ := h
  simp only at hop hl
  rcases hop with h | h | h <;> subst h
  · simp only [dualGate]
    split <;> simp [hl]
  · simp only [dualGate]
    refine ⟨by simp, ?_⟩
    exact le_trans (List.length_filter_le _ _) hl
  · simp only [dualGate]
    split <;> simp [hl]

lemma dualGate_not (k : ℕ) (g : Gate) (h : (dualGate k g).op = GateOp.not) :
    g.op = GateOp.not := by
  obtain ⟨op, l⟩ := g
  cases op with
  | and =>
    simp only [dualGate] at h
    split at h <;> simp at h
  | or => simp [dualGate] at h
  | not => rfl
  | mod m => simp [dualGate] at h
  | maj => simp [dualGate] at h

lemma main : ∀ (n : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → ∃ gates' : List PEqualNP.CircuitLowerBounds.Gate, gates'.length = gates.length ∧ (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) ∧ (∀ (i : ℕ) (g' : PEqualNP.CircuitLowerBounds.Gate), gates'[i]? = some g' → g'.op = PEqualNP.CircuitLowerBounds.GateOp.not → ∃ g : PEqualNP.CircuitLowerBounds.Gate, gates[i]? = some g ∧ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ ∀ (w : ℕ) (x : Fin n → Bool), w < n + gates.length → (PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates', 0⟩ (List.ofFn x)).getD w false = !((PEqualNP.CircuitLowerBounds.Circuit.wires ⟨gates, 0⟩ (List.ofFn (fun p : Fin n => !x p))).getD w false) := by
  intro n gates hgates
  refine ⟨dualList n gates, dualList_length n gates, ?_, ?_, ?_⟩
  · intro g' hg'
    obtain ⟨k, g, hg, rfl⟩ := mem_dualList gates n g' hg'
    exact dualGate_ok k g (hgates g hg)
  · intro i g' hi hop
    rw [getElem?_dualList] at hi
    cases hgi : gates[i]? with
    | none => simp [hgi] at hi
    | some g =>
      rw [hgi] at hi
      simp only [Option.map_some, Option.some.injEq] at hi
      subst hi
      exact ⟨g, rfl, dualGate_not _ g hop⟩
  · intro w x hw
    have hneg : ∀ i < n, (List.ofFn x).getD i false =
        !((List.ofFn (fun p : Fin n => !x p)).getD i false) := by
      intro i hi
      rw [List.getD_eq_getElem _ _ (by simpa using hi),
        List.getD_eq_getElem _ _ (by simpa using hi)]
      simp
    exact fold_dual gates (fun g hg => (hgates g hg).1) n (List.ofFn (fun p : Fin n => !x p))
      (List.ofFn x) (by simp) (by simp) hneg w hw

end Dual

namespace Elim

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev BFn (n : ℕ) := (Fin n → Bool) → Bool



def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

theorem getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]

theorem getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp

theorem getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp

def gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅

theorem mem_foldr_union {n : ℕ} (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]

theorem mem_gateSupp {n : ℕ} (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _

def suppsFrom {n : ℕ} (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L

def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}

def Agree {n : ℕ} (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false

theorem agree_wiresFrom {n : ℕ} (x y : Fin n → Bool) (gs : List Gate) :
    ∀ (L : List (Finset (Fin n))) (w w' : List Bool), Agree x y L w w' →
      Agree x y (suppsFrom gs L) (wiresFrom gs w) (wiresFrom gs w') := by
  induction gs with
  | nil => intro L w w' h; exact h
  | cons g gs ih =>
    intro L w w' h
    obtain ⟨h1, h2, h3⟩ := h
    apply ih (L ++ [gateSupp L g])
      (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
    refine ⟨by simp [h1], by simp [h2], ?_⟩
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq] at hj
      rw [h1, getD_snoc_eq, h2, getD_snoc_eq]
      congr 1
      apply List.map_congr_left
      intro a ha
      exact h3 a (fun i hi => hj i ((mem_gateSupp L g i).2 ⟨a, ha, hi⟩))
    · rw [getD_snoc_ne _ _ _ _ hjl] at hj
      rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
      exact h3 j hj

theorem agree_inputs {n : ℕ} (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

def Cnt {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card

theorem cnt_inputs {n : ℕ} : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem cnt_step {n : ℕ} (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
    (h : Cnt t L) : Cnt (t + 1) (L ++ [gateSupp L g]) := by
  intro W
  by_cases hW : L.length ∈ W
  · have hsub : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        ⊆ ((W.erase L.length ∪ g.inputs.toFinset).biUnion fun j => L.getD j ∅) := by
      intro i hi
      rw [Finset.mem_biUnion] at hi ⊢
      obtain ⟨j, hjW, hij⟩ := hi
      by_cases hjl : j = L.length
      · subst hjl
        rw [getD_snoc_eq] at hij
        obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g i).1 hij
        exact ⟨a, Finset.mem_union_right _ (List.mem_toFinset.2 ha), hia⟩
      · rw [getD_snoc_ne _ _ _ _ hjl] at hij
        exact ⟨j, Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hjl, hjW⟩), hij⟩
    have hc1 : (W.erase L.length ∪ g.inputs.toFinset).card ≤ (W.card - 1) + 2 := by
      refine le_trans (Finset.card_union_le _ _) ?_
      rw [Finset.card_erase_of_mem hW]
      exact Nat.add_le_add_left (le_trans (List.toFinset_card_le _) hg) _
    have hWpos : 1 ≤ W.card := Finset.card_pos.2 ⟨_, hW⟩
    have := h (W.erase L.length ∪ g.inputs.toFinset)
    have := Finset.card_le_card hsub
    omega
  · have heq : (W.biUnion fun j => (L ++ [gateSupp L g]).getD j ∅)
        = (W.biUnion fun j => L.getD j ∅) := by
      apply Finset.biUnion_congr rfl
      intro j hj
      exact getD_snoc_ne _ _ _ _ (fun e => hW (e ▸ hj))
    rw [heq]
    have := h W
    omega

theorem cnt_suppsFrom {n : ℕ} (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this

theorem dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : HasCircuitSize n f s) : T.card ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : T ⊆ S := by
    intro i hiT
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i hiT
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS] at hc
  have := Finset.card_le_card hall
  omega

def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g

theorem normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]

def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)

theorem normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
  obtain ⟨op, inputs⟩ := g
  obtain ⟨hop, hlen⟩ := h
  rcases hop with h | h | h
  · have : op = GateOp.and := h
    subst this; exact ⟨⟨Or.inl rfl, hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.or := h
    subst this; exact ⟨⟨Or.inr (Or.inl rfl), hlen⟩, by simp [normGate]⟩
  · have : op = GateOp.not := h
    subst this
    refine ⟨⟨Or.inr (Or.inr rfl), ?_⟩, fun _ => ?_⟩ <;> simp [normGate] <;> omega

theorem wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
    wiresFrom (gs.map normGate) w = wiresFrom gs w := by
  induction gs with
  | nil => intro w; rfl
  | cons g gs ih =>
    intro w
    have s1 : wiresFrom ((g :: gs).map normGate) w = wiresFrom (gs.map normGate)
        (w ++ [(normGate g).op.eval ((normGate g).inputs.map fun i => w.getD i false)]) := rfl
    have s2 : wiresFrom (g :: gs) w
        = wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [s1, s2, normGate_eval, ih]

abbrev Stat := Sum Bool ℕ

def statVal (w : List Bool) : Stat → Bool
  | Sum.inl c => c
  | Sum.inr j => w.getD j false

def statValid (m : ℕ) : Stat → Prop
  | Sum.inl _ => True
  | Sum.inr j => j < m

def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | Sum.inl c :: _ => (none, Sum.inl (!c))
  | Sum.inr j :: _ => (some ⟨GateOp.not, [j]⟩, Sum.inr m)

def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl true)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c && d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inr j else Sum.inl false)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.and, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Sum.inl false)
  | [Sum.inl c] => (none, Sum.inl c)
  | [Sum.inr j] => (none, Sum.inr j)
  | [Sum.inl c, Sum.inl d] => (none, Sum.inl (c || d))
  | [Sum.inl c, Sum.inr j] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inl c] => (none, bif c then Sum.inl true else Sum.inr j)
  | [Sum.inr j, Sum.inr k] => (some ⟨GateOp.or, [j, k]⟩, Sum.inr m)
  | _ => (none, Sum.inl false)

def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Sum.inl false)

def CleanG (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])

theorem cleanG_lt {m : ℕ} {g : Gate} (h : CleanG m g) : ∀ a ∈ g.inputs, a < m := by
  rcases h with ⟨_, j, hj, hin⟩ | ⟨_, j, k, hj, hk, hin⟩
  · intro a ha; simp [hin] at ha; omega
  · intro a ha; simp [hin] at ha; rcases ha with rfl | rfl <;> omega

def CleanL (n : ℕ) (gs : List Gate) : Prop :=
  ∀ p g, gs[p]? = some g → CleanG (n + p) g

theorem simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
    ∀ g ∈ (simplify op m ins).1, Ok g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg <;> (subst hg; simp [Ok])
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;>
      simp [simpNot] at hg <;> (subst hg; simp [Ok])
  · simp at hg
  · simp at hg

theorem simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat)
    (hv : ∀ s ∈ ins, statValid m s) :
    ∀ g ∈ (simplify op m ins).1, CleanG m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    exact Or.inr ⟨Or.inl rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    exact Or.inr ⟨Or.inr rfl, _, _, hv (Sum.inr _) (by simp), hv (Sum.inr _) (by simp), rfl⟩
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    exact Or.inl ⟨rfl, _, hv (Sum.inr _) (by simp), rfl⟩
  · simp at hg
  · simp at hg

theorem simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Sum.inl c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]

theorem simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, statValid w.length s) :
    statValid (w.length + (simplify op w.length ins).1.toList.length) (simplify op w.length ins).2 ∧
    statVal (wiresFrom (simplify op w.length ins).1.toList w) (simplify op w.length ins).2
      = op.eval (ins.map (statVal w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, statValid, statVal, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, statValid, statVal, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, statValid, statVal, GateOp.eval, wiresFrom]

def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)

def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc

theorem elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl

theorem elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]

theorem elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega

theorem elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    rw [elim_cons, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)

theorem toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp

theorem elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ acc.2, Ok g) → ∀ g ∈ (elim n gs acc).2, Ok g := by
  induction gs with
  | nil => intro acc h; exact h
  | cons g gs ih =>
    intro acc h
    apply ih (elimStep n acc g)
    intro g' hg'
    rcases List.mem_append.1 hg' with h1 | h1
    · exact h g' h1
    · exact simplify_ok _ _ _ g' (by simpa using h1)

theorem elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
      omega
    rw [elim_cons, List.length_cons]; omega

theorem elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Sum.inl false) = Sum.inl c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    rw [elim_cons, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length = _
        rw [hnone]; simp
      have := elim_len n gs (elimStep n acc g)
      omega
    · have hex' : ∃ g' ∈ gs, k ∈ g'.inputs := by
        obtain ⟨g', hg', hk'⟩ := hex
        rcases List.mem_cons.1 hg' with rfl | h
        · exact absurd hk' hkg
        · exact ⟨g', h, hk'⟩
      have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
        (by simp [elimStep]; omega)
        (by
          obtain ⟨c, hc⟩ := hc
          refine ⟨c, ?_⟩
          simp only [elimStep]
          rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
        hex'
      have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
        omega
      omega

theorem statValid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, statValid m s → statValid m' s
  | Sum.inl _, _ => trivial
  | Sum.inr _, hj => lt_of_lt_of_le hj h

theorem statVal_append (w t : List Bool) : ∀ s : Stat, statValid w.length s →
    statVal (w ++ t) s = statVal w s
  | Sum.inl _, _ => rfl
  | Sum.inr _, hj => List.getD_append _ _ _ _ hj

def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false)) ∧
    statVal (wiresFrom acc.2 y) (acc.1.getD i (Sum.inl false)) = w.getD i false

theorem inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      Inv n y (wiresFrom gs w) (elim n gs acc) := by
  induction gs with
  | nil => intro w acc _ h; exact h
  | cons g gs ih =>
    intro w acc hok h
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (elimStep n acc g)
      (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    obtain ⟨hl, hi⟩ := h
    set w' := wiresFrom acc.2 y with hw'
    have lw' : w'.length = n + acc.2.length := by rw [hw', length_wiresFrom, hy]
    set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (statVal w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, _⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show statValid (n + (acc.2 ++ r.1.toList).length) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) ∧
      statVal (wiresFrom (acc.2 ++ r.1.toList) y) ((acc.1 ++ [r.2]).getD i (Sum.inl false)) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨statValid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, statVal_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2

theorem elim_clean (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, Ok g) → (∀ i, statValid (n + acc.2.length) (acc.1.getD i (Sum.inl false))) →
    CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro acc _ _ hc; exact hc
  | cons g gs ih =>
    intro acc hok hv hc
    have hstep := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
    apply hstep
    · intro i
      set ins := g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
      have hgok := hok g List.mem_cons_self
      have hs := simplify_sound g.op hgok.1 (List.replicate (n + acc.2.length) false) ins
        (by simpa [hins] using hgok.2)
        (by
          intro s hs
          obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
          simpa using hv a)
      simp only [List.length_replicate] at hs
      show statValid (n + (acc.2 ++ _).length) ((acc.1 ++ [_]).getD i (Sum.inl false))
      rw [List.length_append, ← Nat.add_assoc]
      by_cases hil : i = acc.1.length
      · subst hil; rw [getD_snoc_eq]; exact hs.1
      · rw [getD_snoc_ne _ _ _ _ hil]; exact statValid_mono (by omega) _ (hv i)
    · intro p g' hp
      simp only [elimStep] at hp
      by_cases hlt : p < acc.2.length
      · rw [List.getElem?_append_left hlt] at hp
        exact hc p g' hp
      · rw [List.getElem?_append_right (by omega)] at hp
        set r := simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Sum.inl false)) with hr
        cases ho : r.1 with
        | none => simp [ho] at hp
        | some g0 =>
          rw [ho] at hp
          have hp0 : p - acc.2.length = 0 := by
            have := (List.getElem?_eq_some_iff.1 hp).1
            simp at this; omega
          have hpeq : p = acc.2.length := by omega
          rw [hp0] at hp
          simp at hp
          subst hp
          rw [hpeq]
          exact simplify_clean g.op (n + acc.2.length) _ (by
            intro s hs
            obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
            exact hv a) g0 (by rw [← hr, ho]; rfl)

def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Sum.inr (i : ℕ)) ++ [Sum.inl b]

theorem initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
  getD_snoc_len _ _ _ _ (by simp)

theorem inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => (Sum.inr (i : ℕ) : Stat))).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, statValid, statVal, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩

theorem ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp

theorem supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, n ∉ g.inputs) → (∀ j : ℕ, j ≠ n → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, j ≠ n → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
  induction gs with
  | nil => intro L _ h; exact h
  | cons g gs ih =>
    intro L hno h
    apply ih (L ++ [gateSupp L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
    intro j hj
    by_cases hjl : j = L.length
    · subst hjl
      rw [getD_snoc_eq]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp L g _).1 hmem
      exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj

theorem inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]

theorem inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp

theorem gate_elim_one (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : HasCircuitSize (n + 1) f s) :
    ∃ s', s' + 1 ≤ s ∧ HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  set acc := elim n gs (initStats n b, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool))) acc := by
    intro y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ y : Fin n → Bool,
      statVal (wiresFrom acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | inr j =>
    have hlen : acc.2.length + 1 ≤ s := by
      by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
      · have := elim_len_lt n n gs (initStats n b, []) hnok (by simp [initStats])
          ⟨b, getD_snoc_len _ _ _ _ (by simp)⟩ hread
        rw [← hacc] at this
        have hl : gs.length = C.gates.length := by simp [hgs]
        simp only [List.length_nil, zero_add] at this
        omega
      · exfalso
        push Not at hread
        have hout : C.output ≠ n := by
          intro e
          rw [e, hacc, elim_getD n n _ gs _ (by simp [initStats])] at hst
          have hb : (initStats n b).getD n (Sum.inl false) = Sum.inl b :=
            getD_snoc_len _ _ _ _ (by simp)
          rw [show ((initStats n b, ([] : List Gate))).1 = initStats n b from rfl, hb] at hst
          cases hst
        obtain ⟨x, hx⟩ := hdep
        apply hx
        have hns := supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) C.output hout
        have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
          (agree_inputs _ _)).2.2 C.output (by
            intro k hk
            have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
            simp [Function.update_of_ne this])
        rw [← hevg, ← hevg]
        exact hag
    refine ⟨acc.2.length, hlen, ⟨acc.2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this

def wmap (n m : ℕ) (π : Fin n → Fin m) (w : ℕ) : ℕ :=
  if h : w < n then (π ⟨w, h⟩ : ℕ) else w - n + m

def relGate (n m : ℕ) (π : Fin n → Fin m) (g : Gate) : Gate :=
  ⟨g.op, g.inputs.map (wmap n m π)⟩

def relabel (n m : ℕ) (π : Fin n → Fin m) (C : Circuit) : Circuit :=
  ⟨C.gates.map (relGate n m π), wmap n m π C.output⟩

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def Rel (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) : Prop :=
  n ≤ W.length ∧ W'.length + n = W.length + m ∧
    ∀ w : ℕ, W'.getD (wmap n m π w) false = W.getD w false

theorem rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
    (h : Rel n m π W W') : Rel n m π (step W g) (step W' (relGate n m π g)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have hv : (relGate n m π g).op.eval
      ((relGate n m π g).inputs.map fun i => W'.getD i false)
      = g.op.eval (g.inputs.map fun i => W.getD i false) := by
    simp only [relGate, List.map_map]
    congr 1
    apply List.map_congr_left
    intro a _
    exact h3 a
  refine ⟨by simp [step]; omega, by simp [step]; omega, ?_⟩
  intro w
  simp only [step, hv]
  rcases Nat.lt_trichotomy w W.length with hw | hw | hw
  · have hlt : wmap n m π w < W'.length := by
      unfold wmap
      split
      · have := (π ⟨w, by assumption⟩).2; omega
      · omega
    rw [List.getD_append _ _ _ _ hlt, List.getD_append _ _ _ _ hw]
    exact h3 w
  · have he : wmap n m π w = W'.length := by
      unfold wmap
      split
      · omega
      · omega
    rw [he, hw, getD_snoc_eq, getD_snoc_eq]
  · have hge : W'.length + 1 ≤ wmap n m π w := by
      unfold wmap
      split
      · omega
      · omega
    rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]

theorem rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)

theorem rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
    Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x) := by
  refine ⟨by simp, by simp; omega, ?_⟩
  intro w
  unfold wmap
  split
  · rename_i hw
    rw [List.getD_eq_getElem _ _ (by simp), List.getD_eq_getElem _ _ (by simpa using hw)]
    simp
  · rename_i hw
    rw [List.getD_eq_default _ _ (by simp), List.getD_eq_default _ _ (by simp; omega)]

theorem relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : HasCircuitSize n h s) : HasCircuitSize m (fun x => h (x ∘ π)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := hc
  refine ⟨relabel n m π C, ?_, ?_, ?_⟩
  · intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact ⟨(ok g0 hg0).1, by simpa [relGate] using (ok g0 hg0).2⟩
  · simpa [relabel, Circuit.size] using hsz
  · intro x
    show _ = h (x ∘ π)
    rw [← hev (x ∘ π)]
    have := (rel_fold n m π C.gates _ _ (rel_init n m π x)).2.2 C.output
    exact this

end Elim

namespace Lower

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def target (x : Fin 6 → Bool) : Bool :=
  Nat.testBit (3892346880 * 2 ^ 32 + 2147483648)
    (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)

def permutation : Fin 6 → Fin 6 := ![0, 1, 2, 5, 4, 3]
def shifted (x : Fin 6 → Bool) : Bool := target (x ∘ permutation)
def cofactor (x : Fin 5 → Bool) : Bool := shifted (Fin.snoc x true)

theorem dual_size {n s : ℕ} {f : (Fin n → Bool) → Bool}
    (ht : ∃ x, f x = true) (h : HasCircuitSize n f s) :
    HasCircuitSize n (fun x => !(f (fun i => !x i))) s := by
  obtain ⟨C, hfan, hsize, heval⟩ := h
  have hout : C.output < n + C.gates.length := by
    obtain ⟨x, hx⟩ := ht
    by_contra hn
    have hv : C.eval (List.ofFn x) = false := by
      change (Elim.wiresFrom C.gates (List.ofFn x)).getD C.output false = false
      apply List.getD_eq_default
      rw [Elim.length_wiresFrom]
      simp only [List.length_ofFn]
      omega
    rw [heval x, hx] at hv
    cases hv
  have legal : ∀ g ∈ C.gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
        g.inputs.length ≤ 2 := by
    intro g hg
    exact ⟨by simpa using (hfan g hg).1, (hfan g hg).2⟩
  obtain ⟨gs, hlen, hok, _, hd⟩ := Dual.main n C.gates legal
  refine ⟨⟨gs, C.output⟩, ?_, ?_, ?_⟩
  · intro g hg
    exact ⟨by simpa using (hok g hg).1, (hok g hg).2⟩
  · change gs.length ≤ s
    rw [hlen]
    exact hsize
  · intro x
    have hh := hd C.output x hout
    change Circuit.eval ⟨gs, C.output⟩ (List.ofFn x) =
      !(C.eval (List.ofFn (fun p : Fin n => !x p))) at hh
    rw [heval] at hh
    exact hh

theorem cofactor_dual : (fun x : Fin 5 → Bool => !(cofactor (fun i => !x i))) =
    Threshold.T25 := by
  funext x
  revert x
  decide +kernel

theorem general_lower (s : ℕ) (h : HasCircuitSize 6 target s) : 11 ≤ s := by
  have hs : HasCircuitSize 6 shifted s :=
    Elim.relabel_size permutation target s h
  have hd : ∃ x : Fin 6 → Bool,
      shifted (Function.update x (Fin.last 5) (!x (Fin.last 5))) ≠ shifted x := by
    exact ⟨fun _ => true, by decide +kernel⟩
  have hn : ∃ y y' : Fin 5 → Bool,
      shifted (Fin.snoc y true) ≠ shifted (Fin.snoc y' true) := by
    exact ⟨fun _ => false, fun _ => true, by decide +kernel⟩
  obtain ⟨t, hlt, hc⟩ := Elim.gate_elim_one 5 shifted true s hd hn hs
  change HasCircuitSize 5 cofactor t at hc
  have hh := dual_size (f := cofactor) (s := t)
    ⟨fun _ => true, by decide +kernel⟩ hc
  rw [cofactor_dual] at hh
  have hten := Threshold.main t hh
  omega

end Lower

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def monoEleven : Circuit :=
  ⟨[⟨.and, [0, 1]⟩, ⟨.and, [4, 5]⟩, ⟨.and, [6, 7]⟩,
    ⟨.or, [0, 1]⟩, ⟨.or, [4, 5]⟩, ⟨.and, [6, 10]⟩,
    ⟨.and, [7, 9]⟩, ⟨.or, [11, 12]⟩, ⟨.and, [2, 13]⟩,
    ⟨.or, [8, 14]⟩, ⟨.and, [3, 15]⟩], 16⟩

lemma monoEleven_size : monoEleven.size = 11 := rfl

lemma monoEleven_monotone : Monotone2 monoEleven := by
  simp [Monotone2, monoEleven]

lemma monoEleven_correct : ∀ x : Fin 6 → Bool,
    monoEleven.eval (List.ofFn x) = Lower.target x := by
  decide

lemma monotone_replacement_of_lower_bound
    (hlower : ∀ s, HasCircuitSize 6 Lower.target s → 11 ≤ s) :
    ∀ s, HasCircuitSize 6 Lower.target s →
      ∃ C : Circuit, Monotone2 C ∧ C.size ≤ s ∧
        ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Lower.target x := by
  intro s hs
  exact ⟨monoEleven, monoEleven_monotone,
    monoEleven_size ▸ hlower s hs, monoEleven_correct⟩


end PEqualNP.Outside.L_meta_12178

theorem PEqualNP.Outside.L_meta_12178 : ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize 6 (fun x : Fin 6 → Bool => Nat.testBit (3892346880 * 2 ^ 32 + 2147483648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0)) s → ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧ C.size ≤ s ∧ ∀ x : Fin 6 → Bool, C.eval (List.ofFn x) = Nat.testBit (3892346880 * 2 ^ 32 + 2147483648) (∑ i : Fin 6, if x i then 2 ^ (i : ℕ) else 0) := by
  exact PEqualNP.Outside.L_meta_12178.monotone_replacement_of_lower_bound
    PEqualNP.Outside.L_meta_12178.Lower.general_lower
