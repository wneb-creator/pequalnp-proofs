import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_20924_aux

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


def forcedL {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun u => ∃ v, A u v = true ∧ ∃ u', A u' v = false


def forcedR {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun v => ∃ u, A u v = true ∧ ∃ w, A u w = false

def on (a c : ℕ) : ℕ → Bool := fun i => decide (i = a) || decide (i = c)

lemma on_iff (a c i : ℕ) : on a c i = true ↔ i = a ∨ i = c := by simp [on]


def Dep (F : (ℕ → Bool) → Bool) (N : Finset ℕ) : Prop :=
  ∀ x y : ℕ → Bool, (∀ i ∈ N, x i = y i) → F x = F y


def Free (F : (ℕ → Bool) → Bool) : Prop :=
  F (fun _ => false) = false ∧ ∀ a b c d, F (on a a) = false → F (on b b) = false →
    F (on c c) = false → F (on d d) = false → F (on a c) = true → F (on a d) = true →
    F (on b c) = true → F (on b d) = true

lemma bool_ext {a b : Bool} (h : a = true ↔ b = true) : a = b := by
  cases a <;> cases b <;> simp_all


lemma free_or {F : (ℕ → Bool) → Bool} {N : Finset ℕ} (hd : Dep F N) (hf : Free F) {t p q : ℕ}
    (hp : p ∉ N.erase t) (hq : q ∉ N.erase t) :
    Free fun x => F (Function.update x t (x p || x q)) := by
  classical
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset N
  let r : ℕ → ℕ := fun a => if a = p ∨ a = q then t else if a ∈ N.erase t then a else z
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
    rw [show Function.update (fun _ : ℕ => false) t (false || false) = fun _ => false from by
      funext i; by_cases h : i = t <;> simp [Function.update, h]]
    exact hf.1
  · intro a b c d
    simp only [key]
    exact hf.2 _ _ _ _


lemma free_and {F : (ℕ → Bool) → Bool} {N : Finset ℕ} (hd : Dep F N) (hf : Free F) {t p q : ℕ}
    (hpq : p ≠ q) (hp : p ∉ N.erase t) (hq : q ∉ N.erase t) :
    Free fun x => F (Function.update x t (x p && x q)) := by
  classical
  obtain ⟨z, hz⟩ := Infinite.exists_notMem_finset N
  let r : ℕ → ℕ := fun a => if a ∈ N.erase t then a else z
  have rp : r p = z := if_neg hp
  have rq : r q = z := if_neg hq
  have hzz : ∀ x, F (on x z) = F (on x x) := fun x => hd _ _ fun i hi => by
    have : i ≠ z := fun h => hz (h ▸ hi)
    simp [on, this]
  have hzz' : ∀ x, F (on z x) = F (on x x) := fun x => hd _ _ fun i hi => by
    have : i ≠ z := fun h => hz (h ▸ hi)
    simp [on, this]
  have hz0 : F (on z z) = false := by
    rw [← hf.1]
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
    rw [show Function.update (fun _ : ℕ => false) t (false && false) = fun _ => false from by
      funext i; by_cases h : i = t <;> simp [Function.update, h]]
    exact hf.1
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
        exact hf.2 _ _ _ _ ha hb hc hd' hac had hbc


def run : List Gate → ℕ → (ℕ → Bool) → ℕ → Bool
  | [], _, x => x
  | g :: gs, t, x => run gs (t + 1) (Function.update x t (g.op.eval (g.inputs.map x)))

lemma run_eq (gs : List Gate) : ∀ w : List Bool, ∀ i,
    (wiresFrom gs w).getD i false = run gs w.length (fun j => w.getD j false) i := by
  induction gs with
  | nil => intro w i; rfl
  | cons g gs ih =>
    intro w i
    have e : wiresFrom (g :: gs) w =
        wiresFrom gs (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) := rfl
    rw [e, ih, List.length_append, List.length_singleton, run]
    congr 2
    funext j
    rw [getD_snoc, Function.update_apply]

lemma back (o : ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2) :
    ∀ t, ∃ N : Finset ℕ, N.card ≤ 1 + gs.length ∧ Dep (fun x => run gs t x o) N ∧
      (N.card = 1 + gs.length → Free fun x => run gs t x o) := by
  induction gs with
  | nil =>
    intro t
    refine ⟨{o}, by simp, fun x y h => h o (by simp), fun _ => ⟨rfl, ?_⟩⟩
    intro a b c d ha hb hc hd hac had hbc
    simp only [run, on, Bool.or_self, decide_eq_false_iff_not, Bool.or_eq_true,
      decide_eq_true_eq] at *
    tauto
  | cons g gs ih =>
    intro t
    have hgs := fun g' h => hg g' (List.mem_cons_of_mem _ h)
    have hg0 := hg g (by simp)
    obtain ⟨N, hc, hd, hf⟩ := ih hgs (t + 1)
    by_cases ht : t ∈ N
    · refine ⟨N.erase t ∪ g.inputs.toFinset, ?_, ?_, ?_⟩
      · have h1 := Finset.card_union_le (N.erase t) g.inputs.toFinset
        have h2 := Finset.card_erase_of_mem ht
        have h3 := List.toFinset_card_le g.inputs
        have h4 : 0 < N.card := Finset.card_pos.2 ⟨_, ht⟩
        have := hg0.2
        rw [List.length_cons]; omega
      · intro x y h
        refine hd _ _ fun i hi => ?_
        by_cases hit : i = t
        · subst hit
          simp only [Function.update_self]
          congr 1
          apply List.map_congr_left
          intro a ha
          exact h a (Finset.mem_union_right _ (List.mem_toFinset.2 ha))
        · simp only [Function.update_of_ne hit]
          exact h i (Finset.mem_union_left _ (Finset.mem_erase.2 ⟨hit, hi⟩))
      · intro heq
        rw [List.length_cons] at heq
        have h1 := Finset.card_union_add_card_inter (N.erase t) g.inputs.toFinset
        have h2 := Finset.card_erase_of_mem ht
        have h3 := List.toFinset_card_le g.inputs
        have h4 : 0 < N.card := Finset.card_pos.2 ⟨_, ht⟩
        have h5 := hg0.2
        have hN : N.card = 1 + gs.length := by omega
        have hI : (N.erase t ∩ g.inputs.toFinset).card = 0 := by omega
        have hT : g.inputs.toFinset.card = 2 := by omega
        have hL : g.inputs.length = 2 := by omega
        obtain ⟨p, q, hpq⟩ := List.length_eq_two.1 hL
        rw [hpq] at hT hI
        have hne : p ≠ q := by rintro rfl; simp at hT
        have hI' := Finset.card_eq_zero.1 hI
        have hp : p ∉ N.erase t := fun h => by
          have : p ∈ N.erase t ∩ [p, q].toFinset := Finset.mem_inter.2 ⟨h, by simp⟩
          rw [hI'] at this; simp at this
        have hq : q ∉ N.erase t := fun h => by
          have : q ∈ N.erase t ∩ [p, q].toFinset := Finset.mem_inter.2 ⟨h, by simp⟩
          rw [hI'] at this; simp at this
        have hop := hg0.1
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hop
        rcases hop with hop | hop
        · have := free_and hd (hf hN) hne hp hq
          have e : (fun x => run (g :: gs) t x o) = fun x =>
              (fun x => run gs (t + 1) x o) (Function.update x t (x p && x q)) := by
            funext x; simp [run, hop, hpq, GateOp.eval]
          rw [e]; exact this
        · have := free_or hd (hf hN) hp hq
          have e : (fun x => run (g :: gs) t x o) = fun x =>
              (fun x => run gs (t + 1) x o) (Function.update x t (x p || x q)) := by
            funext x; simp [run, hop, hpq, GateOp.eval]
          rw [e]; exact this
    · refine ⟨N, by rw [List.length_cons]; omega, ?_, ?_⟩
      · intro x y h
        refine hd _ _ fun i hi => ?_
        have hit : i ≠ t := fun e => ht (e ▸ hi)
        simp only [Function.update_of_ne hit]
        exact h i hi
      · intro heq; rw [List.length_cons] at heq; omega

lemma path : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool) (u x : Fin n) (v w : Fin m), A u v = true → A u w = true → A x v = true → A x w = false → (∃ w' : Fin m, A u w' = false) → (∃ u' : Fin n, A u' v = false) → PEqualNP.Represents.RepSizeAtMost A s → (Finset.univ.filter (fun a : Fin n => ∃ b : Fin m, A a b = true ∧ ∃ a' : Fin n, A a' b = false)).card + (Finset.univ.filter (fun b : Fin m => ∃ a : Fin n, A a b = true ∧ ∃ b' : Fin m, A a b' = false)).card ≤ s := by
  intro n m s A u x v w huv huw hxv hxw ⟨w', huw'⟩ ⟨u', hu'v⟩ h
  by_contra hlt
  have hlt' : s + 1 ≤ (forcedL A).card + (forcedR A).card := by
    unfold forcedL forcedR; omega
  obtain ⟨C, hC, hs, hR⟩ := h
  obtain ⟨N, hc, hd, hf⟩ := back C.output C.gates hC (n + m)
  have hsz : C.gates.length ≤ s := hs
  let F : (ℕ → Bool) → Bool := fun x => run C.gates (n + m) x C.output
  have hF : ∀ P : Finset ℕ, C.eval (inp (n + m) P) = F fun i => decide (i < n + m ∧ i ∈ P) := by
    intro P
    show (wiresFrom C.gates (inp (n + m) P)).getD C.output false = _
    rw [run_eq]
    have hl : (inp (n + m) P).length = n + m := by simp [inp]
    rw [hl]
    show run C.gates (n + m) (fun j => (inp (n + m) P).getD j false) C.output = _
    simp only [inp_getD]; rfl
  have hop : ∀ g ∈ C.gates, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) := fun g hg => (hC g hg).1
  have hmono : ∀ P Q : Finset ℕ, P ⊆ Q → C.eval (inp (n + m) P) = true →
      C.eval (inp (n + m) Q) = true := by
    intro P Q hPQ
    refine mono C.gates hop _ _ (by simp [inp]) (fun i => ?_) _
    rw [inp_getD, inp_getD, decide_eq_true_eq, decide_eq_true_eq]
    exact fun ⟨a, b⟩ => ⟨a, hPQ b⟩
  have hA : ∀ (u : Fin n) (v : Fin m), C.eval (inp (n + m) {(u : ℕ), n + (v : ℕ)}) = A u v := by
    intro u v; rw [← oneEach_eq]; exact hR u v
  have hon : ∀ a c, a < n + m → c < n + m → F (on a c) = C.eval (inp (n + m) {a, c}) := by
    intro a c ha hc
    rw [hF]
    congr 1
    funext i
    apply bool_ext
    rw [on_iff, decide_eq_true_eq, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro (rfl | rfl) <;> simp [*]
    · exact fun h => h.2
  have hoff : ∀ P w, w ∉ N → C.eval (inp (n + m) P) = C.eval (inp (n + m) (P.erase w)) := by
    intro P w hw
    rw [hF, hF]
    refine hd _ _ fun i hi => ?_
    have : i ≠ w := fun e => hw (e ▸ hi)
    rw [decide_eq_decide, Finset.mem_erase]
    tauto
  have hL : ∀ u ∈ forcedL A, (u : ℕ) ∈ N := by
    intro u hu
    obtain ⟨v, h1, u', h2⟩ := (Finset.mem_filter.1 hu).2
    by_contra hw
    have e := hoff {(u : ℕ), n + (v : ℕ)} u hw
    rw [hA, h1] at e
    have := hmono _ {(u' : ℕ), n + (v : ℕ)} (fun i hi => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto) e.symm
    rw [hA, h2] at this
    exact Bool.noConfusion this
  have hRr : ∀ v ∈ forcedR A, n + (v : ℕ) ∈ N := by
    intro v hv
    obtain ⟨u, h1, w, h2⟩ := (Finset.mem_filter.1 hv).2
    by_contra hw
    have e := hoff {(u : ℕ), n + (v : ℕ)} (n + v) hw
    rw [hA, h1] at e
    have := hmono _ {(u : ℕ), n + (w : ℕ)} (fun i hi => by
      simp only [Finset.mem_erase, Finset.mem_insert, Finset.mem_singleton] at hi ⊢
      tauto) e.symm
    rw [hA, h2] at this
    exact Bool.noConfusion this
  have hsub : (forcedL A).image (fun u : Fin n => (u : ℕ)) ∪
      (forcedR A).image (fun v : Fin m => n + (v : ℕ)) ⊆ N := by
    intro i hi
    rcases Finset.mem_union.1 hi with hi | hi
    · obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hi; exact hL u hu
    · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hi; exact hRr v hv
  have hdis : Disjoint ((forcedL A).image (fun u : Fin n => (u : ℕ)))
      ((forcedR A).image (fun v : Fin m => n + (v : ℕ))) := by
    rw [Finset.disjoint_left]
    intro i h1 h2
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.1 h1
    obtain ⟨v, _, hv⟩ := Finset.mem_image.1 h2
    have := u.2
    omega
  have hcc := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdis,
    Finset.card_image_of_injective _ (fun a b h => Fin.ext h),
    Finset.card_image_of_injective _ (fun a b h => Fin.ext (by simpa using h))] at hcc
  have hfree := hf (by omega)
  have bu := u.2
  have bx := x.2
  have bv := v.2
  have bw := w.2
  have hrow : ∀ (a : Fin n) (b : Fin m), A a b = false → F (on a a) = false := by
    intro a b hab
    have ba := a.2
    rw [hon _ _ (by omega) (by omega)]
    by_contra hne
    have := hmono {(a : ℕ), (a : ℕ)} {(a : ℕ), n + (b : ℕ)} (fun i hi => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi ⊢; tauto) (by simpa using hne)
    rw [hA, hab] at this
    exact Bool.noConfusion this
  have hcol : ∀ (a : Fin n) (b : Fin m), A a b = false → F (on (n + b) (n + b)) = false := by
    intro a b hab
    have bb := b.2
    rw [hon _ _ (by omega) (by omega)]
    by_contra hne
    have := hmono {n + (b : ℕ), n + (b : ℕ)} {(a : ℕ), n + (b : ℕ)} (fun i hi => by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi ⊢; tauto) (by simpa using hne)
    rw [hA, hab] at this
    exact Bool.noConfusion this
  have hcell : ∀ (a : Fin n) (b : Fin m), F (on a (n + b)) = A a b := by
    intro a b
    have ba := a.2
    have bb := b.2
    rw [hon _ _ (by omega) (by omega), hA]
  have := hfree.2 u x (n + v) (n + w) (hrow u w' huw') (hrow x w hxw) (hcol u' v hu'v)
    (hcol x w hxw) ((hcell u v).trans huv) ((hcell u w).trans huw) ((hcell x v).trans hxv)
  have e := hcell x w
  rw [hxw] at e
  exact Bool.noConfusion (this.symm.trans e)

end PEqualNP.Outside.L_meta_20924_aux

theorem PEqualNP.Outside.L_meta_20924 :
    ¬ PEqualNP.Represents.RepSizeAtMost
      (fun (u : Fin 4) (v : Fin 5) => (39902 : ℕ).testBit (5 * u.val + v.val)) 8 := by
  intro h
  have lower := PEqualNP.Outside.L_meta_20924_aux.path 4 5 8
    (fun (u : Fin 4) (v : Fin 5) => (39902 : ℕ).testBit (5 * u.val + v.val))
    0 2 1 3 (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) ⟨0, by decide +kernel⟩ ⟨3, by decide +kernel⟩ h
  have impossible : ¬ ((Finset.univ.filter (fun a : Fin 4 => ∃ b : Fin 5,
      (39902 : ℕ).testBit (5 * a.val + b.val) = true ∧ ∃ a' : Fin 4,
      (39902 : ℕ).testBit (5 * a'.val + b.val) = false)).card +
      (Finset.univ.filter (fun b : Fin 5 => ∃ a : Fin 4,
      (39902 : ℕ).testBit (5 * a.val + b.val) = true ∧ ∃ b' : Fin 5,
      (39902 : ℕ).testBit (5 * a.val + b'.val) = false)).card ≤ 8) := by
    decide +kernel
  exact impossible lower
