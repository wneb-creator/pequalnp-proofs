import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1378

open PEqualNP.CircuitLowerBounds

private def step (v : List Bool) (g : Gate) : List Bool :=
  v ++ [g.op.eval (g.inputs.map fun i => v.getD i false)]

private lemma length_run (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  induction gs generalizing w with
  | nil => simp
  | cons g gs ih => simp [step, ih, Nat.add_comm, Nat.add_left_comm]

private lemma old (gs : List Gate) (w : List Bool) (k : ℕ) (h : k < w.length) :
    (gs.foldl step w).getD k false = w.getD k false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    rw [List.foldl_cons, ih _ (by simp [step]; omega)]
    rw [List.getD_eq_getElem _ _ (by simp [step]; omega), List.getD_eq_getElem _ _ h]
    exact List.getElem_append_left h

private def V {n : ℕ} (gs : List Gate) (k : ℕ) (x : Fin n → Bool) : Bool :=
  (gs.foldl step (List.ofFn x)).getD k false

private lemma eval_gate {n : ℕ} (gs : List Gate) (j : ℕ) (h : j < gs.length) (x : Fin n → Bool) :
    V gs (n+j) x = gs[j].op.eval
      (gs[j].inputs.map fun k => if k < n+j then V gs k x else false) := by
  unfold V
  let w := (gs.take j).foldl step (List.ofFn x)
  have hw : w.length = n+j := by simp [w, length_run, Nat.min_eq_left (Nat.le_of_lt h)]
  have split : gs = gs.take j ++ gs[j] :: gs.drop (j+1) := by
    conv_lhs => rw [← List.take_append_drop j gs, List.drop_eq_getElem_cons h]
  have fold : gs.foldl step (List.ofFn x) = (gs.drop (j+1)).foldl step (step w gs[j]) := by
    conv_lhs => rw [split, List.foldl_append, List.foldl_cons]
  have old' (k : ℕ) (hk : k < n+j) : (gs.foldl step (List.ofFn x)).getD k false = w.getD k false := by
    conv_lhs => rw [split, List.foldl_append]
    exact old _ w _ (by rw [hw]; exact hk)
  calc
    _ = (step w gs[j]).getD w.length false := by
      rw [fold, old _ _ _ (by simp [step, hw]), hw]
    _ = gs[j].op.eval (gs[j].inputs.map fun k => w.getD k false) := by simp [step]
    _ = _ := by
      congr 1
      apply List.map_congr_left
      intro k _
      by_cases hk : k < n+j
      · rw [ite_eq_left hk, old' k hk]
      · rw [ite_eq_right hk, List.getD_eq_default _ _ (by simpa [hw] using hk)]

private lemma raw {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (k : ℕ) (h : k < n) :
    V gs k x = x ⟨k,h⟩ := by
  unfold V
  rw [old _ _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h)]
  simp

private def point {n : ℕ} (p : Fin n) (v : Fin n) : Bool := decide (v = p)
private def off {n : ℕ} (s : Finset (Fin n)) (v : Fin n) : Bool := decide (v ∉ s)
private def hit {n : ℕ} (s : Finset (Fin n)) (x : Fin n → Bool) : Prop := ∃ v ∈ s, x v = true

private lemma hit_point {n : ℕ} (s : Finset (Fin n)) (p : Fin n) :
    hit s (point p) ↔ p ∈ s := by simp [hit, point]

private lemma hit_off_self {n : ℕ} (s : Finset (Fin n)) : ¬ hit s (off s) := by
  simp [hit, off]

private lemma pair_choice {n : ℕ} (s : Finset (Fin n)) (hs : 3 ≤ s.card)
    (ks : List ℕ) (hk : ks.length ≤ 2) (R : ℕ → Fin n → Prop)
    (h : ∀ p ∈ s, ∃ k ∈ ks, R k p) :
    ∃ k ∈ ks, ∃ p ∈ s, ∃ q ∈ s, p ≠ q ∧ R k p ∧ R k q := by
  obtain ⟨p,hp,q,hq,r,hr,hpq,hpr,hqr⟩ := Finset.two_lt_card.mp hs
  obtain ⟨a,ha,hap⟩ := h p hp
  obtain ⟨b,hb,hbq⟩ := h q hq
  obtain ⟨c,hc,hcr⟩ := h r hr
  have rep : a = b ∨ a = c ∨ b = c := by
    cases ks with
    | nil => simp at ha
    | cons x xs =>
      cases xs with
      | nil => simp_all
      | cons y ys =>
        cases ys with
        | nil => simp only [List.mem_cons] at ha hb hc; grind
        | cons z zs => simp at hk
  rcases rep with rfl | rfl | rfl
  · exact ⟨a,ha,p,hp,q,hq,hpq,hap,hbq⟩
  · exact ⟨a,ha,p,hp,r,hr,hpr,hap,hcr⟩
  · exact ⟨b,hb,q,hq,r,hr,hqr,hbq,hcr⟩

private def role {n m : ℕ} (S : Fin m → Finset (Fin n)) (gs : List Gate) (i : Fin m) (k : ℕ) : Prop :=
  ((∀ x, V gs k x = true → hit (S i) x) ∧
    ∃ p q : Fin n, p ≠ q ∧ V gs k (point p) = true ∧ V gs k (point q) = true) ∨
  ((∀ x, hit (S i) x → V gs k x = true) ∧ V gs k (off (S i)) = false) ∨
  (∀ x, V gs k x = true ↔ ¬ hit (S i) x)

private lemma inter_small {n m : ℕ} (S : Fin m → Finset (Fin n))
    (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1) {i j : Fin m} {p q : Fin n}
    (hpq : p ≠ q) (hp : p ∈ S i) (hq : q ∈ S i) (hp' : p ∈ S j) (hq' : q ∈ S j) : i = j := by
  by_contra hn
  have h1 := h i j hn
  have h2 := Finset.one_lt_card.mpr ⟨p, Finset.mem_inter.mpr ⟨hp,hp'⟩,
    q, Finset.mem_inter.mpr ⟨hq,hq'⟩, hpq⟩
  omega

private lemma diff {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hs : ∀ i, 3 ≤ (S i).card) (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    {i j : Fin m} (hne : i ≠ j) : ∃ p ∈ S i, p ∉ S j := by
  by_contra! hh
  have hi := h i j hne
  rw [Finset.inter_eq_left.mpr hh] at hi
  have := hs i
  omega

private lemma roles_unique {n m : ℕ} (S : Fin m → Finset (Fin n))
    (hs : ∀ i, 3 ≤ (S i).card) (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    {gs : List Gate} {k : ℕ} {i j : Fin m} (a : role S gs i k) (b : role S gs j k) : i = j := by
  by_contra ne
  obtain ⟨p,hp,hpj⟩ := diff S hs h ne
  obtain ⟨q,hq,hqi⟩ := diff S hs h (Ne.symm ne)
  have pi : hit (S i) (point p) := (hit_point _ _).mpr hp
  have qj : hit (S j) (point q) := (hit_point _ _).mpr hq
  have all_hit (a : Fin m) : hit (S a) (fun _ => true) :=
    let ⟨v,hv⟩ := Finset.card_pos.mp (by have := hs a; omega)
    ⟨v,hv,rfl⟩
  have none_hit (a : Fin m) : ¬ hit (S a) (fun _ => false) := by simp [hit]
  rcases a with ⟨a,u,v,huv,hu,hv⟩ | ⟨a,az⟩ | a <;> rcases b with ⟨b,_,_,_,_,_⟩ | ⟨b,bz⟩ | b
  · exact ne (inter_small S h huv ((hit_point _ _).mp (a _ hu)) ((hit_point _ _).mp (a _ hv))
      ((hit_point _ _).mp (b _ hu)) ((hit_point _ _).mp (b _ hv)))
  · exact hqi ((hit_point _ _).mp (a _ (b _ qj)))
  · exact none_hit i (a _ ((b _).mpr (none_hit j)))
  · exact hpj ((hit_point _ _).mp (b _ (a _ pi)))
  · have hhit : hit (S j) (off (S i)) := ⟨q,hq,by simp [off,hqi]⟩
    exact Bool.noConfusion (az.symm.trans (b _ hhit))
  · exact (b _).mp (a _ (all_hit i)) (all_hit j)
  · exact none_hit j (b _ ((a _).mpr (none_hit i)))
  · exact (a _).mp (b _ (all_hit j)) (all_hit i)
  · exact (a _).mp ((b _).mpr (fun hj => hpj ((hit_point _ _).mp hj))) pi


private lemma no_raw {n m : ℕ} (S : Fin m → Finset (Fin n)) (hs : ∀ i, 3 ≤ (S i).card)
    (gs : List Gate) (i : Fin m) (k : ℕ) (hk : k < n) (a : role S gs i k) : False := by
  obtain ⟨u,hu,v,hv,huv⟩ := Finset.one_lt_card.mp (by have := hs i; omega : 1 < (S i).card)
  rcases a with ⟨_,p,q,hpq,hp,hq⟩ | ⟨a,_⟩ | a
  · simp [raw gs _ k hk, point] at hp hq
    exact hpq (hp.symm.trans hq)
  · have up := a (point u) ((hit_point _ _).mpr hu)
    have vp := a (point v) ((hit_point _ _).mpr hv)
    simp [raw gs _ k hk, point] at up vp
    exact huv (up.symm.trans vp)
  · have zero := (a (fun _ => false)).mpr (by simp [hit])
    simp [raw gs _ k hk] at zero

private lemma out_valid {n : ℕ} (gs : List Gate) (o : ℕ) (s : Finset (Fin n))
    (hs : 3 ≤ s.card) (he : ∀ x, V gs o x = true ↔ hit s x) : n ≤ o ∧ o < n+gs.length := by
  obtain ⟨p,hp,q,hq,hpq⟩ := Finset.one_lt_card.mp (by omega : 1 < s.card)
  have ap := (he (point p)).mpr ((hit_point s p).mpr hp)
  have aq := (he (point q)).mpr ((hit_point s q).mpr hq)
  constructor
  · by_contra! h
    simp [raw gs _ o h, point] at ap aq
    exact hpq (ap.symm.trans aq)
  · by_contra! h
    unfold V at ap
    rw [List.getD_eq_default _ _ (by simpa [length_run] using h)] at ap
    contradiction

private lemma parent {n m : ℕ} (S : Fin m → Finset (Fin n)) (hs : ∀ i, 3 ≤ (S i).card)
    (gs : List Gate) (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (i : Fin m) (o : ℕ) (ho : n ≤ o ∧ o < n+gs.length)
    (he : ∀ x, V gs o x = true ↔ hit (S i) x) :
    ∃ k, n ≤ k ∧ k < o ∧ role S gs i k := by
  let j := o - n
  have hj : j < gs.length := by unfold j; omega
  have hjo : n+j = o := by unfold j; omega
  let g := gs[j]
  let R := fun (k : ℕ) (x : Fin n → Bool) => if k < o then V gs k x else false
  have ev (x : Fin n → Bool) : V gs o x = g.op.eval (g.inputs.map fun k => R k x) := by
    have this := eval_gate gs j hj x
    simpa [hjo, g, R] using this
  have hg' := hg g (List.getElem_mem hj)
  have allhit : hit (S i) (fun _ => true) := by
    obtain ⟨p,hp⟩ := Finset.card_pos.mp (by have := hs i; omega : 0 < (S i).card)
    exact ⟨p,hp,rfl⟩
  have emp : ¬ hit (S i) (fun _ => false) := by simp [hit]
  have cond (k : ℕ) (x : Fin n → Bool) (h : R k x = true) : k < o := by
    by_contra! hn
    exact (Nat.not_lt.mpr hn) ((by simpa [R] using h : k < o ∧ V gs k x = true).1)
  suffices ∃ k, k < o ∧ role S gs i k by
    obtain ⟨k,hk,r⟩ := this
    exact ⟨k, Nat.le_of_not_gt (fun h => no_raw S hs gs i k h r), hk, r⟩
  rcases hg'.1 with hop | hop | hop
  · have hh (x : Fin n → Bool) : hit (S i) x ↔ ∀ k ∈ g.inputs, R k x = true := by
      rw [← he, ev, hop]
      simp [GateOp.eval,List.all_eq_true]
    have fail := mt (hh (off (S i))).mpr (hit_off_self (S i))
    push Not at fail
    obtain ⟨k,hk,hno⟩ := fail
    have hlt := cond k _ ((hh _).mp allhit k hk)
    refine ⟨k,hlt,Or.inr (Or.inl ⟨?_,?_⟩)⟩
    · intro x hx
      simpa [R,hlt] using (hh x).mp hx k hk
    · simpa [R,hlt] using hno
  · have hh (x : Fin n → Bool) : hit (S i) x ↔ ∃ k ∈ g.inputs, R k x = true := by
      rw [← he, ev, hop]
      simp [GateOp.eval,List.any_eq_true]
    obtain ⟨k,hk,p,_,q,_,hpq,hp,hq⟩ := pair_choice (S i) (hs i) g.inputs hg'.2
      (fun k p => R k (point p) = true) (fun p hp => (hh _).mp ((hit_point _ _).mpr hp))
    have hlt := cond k _ hp
    refine ⟨k,hlt,Or.inl ⟨?_,p,q,hpq,?_,?_⟩⟩
    · intro x hx
      exact (hh x).mpr ⟨k,hk,by simpa [R,hlt] using hx⟩
    · simpa [R,hlt] using hp
    · simpa [R,hlt] using hq
  · cases hargs : g.inputs with
    | nil =>
      have hz : V gs o (fun _ : Fin n => false) = true := by simp [ev,hop,hargs,GateOp.eval]
      exact (emp ((he _).mp hz)).elim
    | cons k ks =>
      have hh (x : Fin n → Bool) : hit (S i) x ↔ R k x = false := by
        rw [← he, ev, hop]
        simp [GateOp.eval,hargs]
      have hz : R k (fun _ => false) = true := by
        cases h : R k (fun _ => false)
        · exact (emp ((hh _).mpr h)).elim
        · rfl
      have hlt := cond k _ hz
      refine ⟨k,hlt,Or.inr (Or.inr fun x => ?_)⟩
      have heq : hit (S i) x ↔ V gs k x = false := by simpa [R,hlt] using hh x
      cases hx : V gs k x <;> simp_all

private lemma prove {n m : ℕ} (S : Fin m → Finset (Fin n)) (hs : ∀ i, 3 ≤ (S i).card)
    (h : ∀ i j, i ≠ j → (S i ∩ S j).card ≤ 1)
    (gs : List Gate) (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2)
    (out : Fin m → ℕ) (he : ∀ i x, V gs (out i) x = true ↔ hit (S i) x) : 2*m ≤ gs.length := by
  classical
  have valid i := out_valid gs (out i) (S i) (hs i) (he i)
  have outinj : Function.Injective out := by
    intro i j e
    by_contra ne
    obtain ⟨p,hp,hpn⟩ := diff S hs h ne
    have eq := (he i (point p)).mpr ((hit_point _ _).mpr hp)
    rw [e] at eq
    exact hpn ((hit_point _ _).mp ((he _ _).mp eq))
  choose dest hdlo hdhi hdrole using fun i => parent S hs gs hg i (out i) (valid i) (he i)
  have disj (i j : Fin m) : dest i ≠ out j := by
    intro e
    have nij : i ≠ j := by intro a; subst j; have := hdhi i; omega
    rcases hdrole i with ⟨a,_,_,_,_,_⟩ | ⟨a,_⟩ | a
    · obtain ⟨p,hp,hpn⟩ := diff S hs h (Ne.symm nij)
      have hy := (he j (point p)).mpr ((hit_point _ _).mpr hp)
      rw [← e] at hy
      exact hpn ((hit_point _ _).mp (a _ hy))
    · obtain ⟨p,hp,hpn⟩ := diff S hs h nij
      have hy := a (point p) ((hit_point _ _).mpr hp)
      rw [e] at hy
      exact hpn ((hit_point _ _).mp ((he _ _).mp hy))
    · have hy := (a (fun _ => false)).mpr (by simp [hit])
      rw [e] at hy
      simpa [hit] using (he _ _).mp hy
  let F : Fin m ⊕ Fin m → Fin gs.length :=
    Sum.elim (fun i => ⟨out i-n, by have := valid i; omega⟩)
      (fun i => ⟨dest i-n, by have := (valid i).2; have := hdhi i; have := hdlo i; omega⟩)
  have inj : Function.Injective F := by
    intro a b e
    have ev := congrArg Fin.val e
    cases a with
    | inl i =>
      cases b with
      | inl j =>
        change out i - n = out j - n at ev
        have := (valid i).1
        have := (valid j).1
        exact congrArg Sum.inl (outinj (by omega))
      | inr j =>
        change out i - n = dest j - n at ev
        have := (valid i).1
        have := hdlo j
        exact ((disj j i) (by omega)).elim
    | inr i =>
      cases b with
      | inl j =>
        change dest i - n = out j - n at ev
        have := hdlo i
        have := (valid j).1
        exact ((disj i j) (by omega)).elim
      | inr j =>
        change dest i - n = dest j - n at ev
        have := hdlo i
        have := hdlo j
        have q : dest i = dest j := by omega
        exact congrArg Sum.inr (roles_unique S hs h (hdrole i) (q ▸ hdrole j))
  have ans := Fintype.card_le_of_injective F inj
  simpa [two_mul] using ans

end PEqualNP.Outside.L_meta_1378

set_option maxHeartbeats 600000 in
theorem PEqualNP.Outside.L_meta_1378 : ∀ (n m : ℕ) (S : Fin m → Finset (Fin n)), 2 ≤ m → (∀ i : Fin m, 3 ≤ (S i).card) → (∀ i j : Fin m, i ≠ j → (S i ∩ S j).card ≤ 1) → ∀ (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ), (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧ g.inputs.length ≤ 2) → (∀ (w : Fin m) (x : Fin n → Bool), PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = decide (∃ v ∈ S w, x v = true)) → 2 * m ≤ gates.length := by
  intro n m S _ hs h gs out hg he
  apply PEqualNP.Outside.L_meta_1378.prove S hs h gs hg out
  intro i x
  change PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gs,out i⟩ (List.ofFn x) = true ↔ _
  rw [he i x]
  simp [PEqualNP.Outside.L_meta_1378.hit]
