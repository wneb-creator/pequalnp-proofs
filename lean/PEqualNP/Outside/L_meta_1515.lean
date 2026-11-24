import Mathlib
import PEqualNP.Defs

-- Fold and representation lemmas adapted from L_meta_669.lean (Apache-2.0).
namespace PEqualNP.Outside.L_meta_1515

open PEqualNP.CircuitLowerBounds

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma step_len (w : List Bool) (g : Gate) : (step w g).length = w.length + 1 := by
  simp [step]

lemma step_lt (w : List Bool) (g : Gate) (i : ℕ) (hi : i < w.length) :
    (step w g).getD i false = w.getD i false := by
  simp [step, List.getD, List.getElem?_append_left hi]

lemma step_last (w : List Bool) (g : Gate) (k : ℕ) (hk : k = w.length) :
    (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
  subst hk
  simp [step, List.getD]

def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl step (List.ofFn x)

lemma W_len {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  have h : ∀ (gs : List Gate) (w : List Bool), (gs.foldl step w).length = w.length + gs.length := by
    intro gs
    induction gs with
    | nil => intro w; simp
    | cons g gs ih =>
      intro w
      rw [List.foldl_cons, ih, step_len, List.length_cons]
      omega
  rw [W, h]
  simp

lemma W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = step (W gs x) g := by
  simp [W, List.foldl_append]

lemma W_val {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ) :
    (W (gs ++ [g]) x).getD t false =
      if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
      else (W gs x).getD t false := by
  rw [W_snoc]
  by_cases ht : t = n + gs.length
  · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
  · rw [if_neg ht]
    by_cases hlt : t < n + gs.length
    · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
    · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
        List.getD_eq_default _ _ (by rw [W_len]; omega)]

def Rep {n : ℕ} {P : (Fin n → Bool) → Prop} (new : List Gate) (f : (Subtype P) → Bool) : Prop :=
  (∃ c : Bool, ∀ x : Subtype P, f x = c) ∨
    (∃ j : ℕ, j < n + new.length ∧ ∀ x : Subtype P, (W new x.val).getD j false = f x)

def Fan (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2

def Ext (new new' : List Gate) : Prop :=
  new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h

lemma rep_congr {n : ℕ} {P : (Fin n → Bool) → Prop} {new : List Gate} {f g : (Subtype P) → Bool}
    (h : ∀ x, f x = g x) (hf : Rep new f) : Rep new g := by
  obtain rfl : f = g := funext h
  exact hf

lemma rep_mono {n : ℕ} {P : (Fin n → Bool) → Prop} {new new' : List Gate} (he : Ext new new')
    (f : (Subtype P) → Bool) (h : Rep new f) : Rep new' f := by
  rcases he with rfl | ⟨k, rfl, _⟩
  · exact h
  · rcases h with hc | ⟨j, hj, hv⟩
    · exact Or.inl hc
    · have hne : ¬ j = n + new.length := by omega
      refine Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
      rw [W_val, if_neg hne]
      exact hv x

lemma rep_and {n : ℕ} {P : (Fin n → Bool) → Prop} (new : List Gate) (f g : (Subtype P) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext new new' ∧ Rep new' (fun x => f x && g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | false =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
        show (f x && g x) = false
        simp [h1 x]⟩⟩
    | true =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x && g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | false =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
          show (f x && g x) = false
          simp [h2 x]⟩⟩
      | true =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x.val).getD j false = (f x && g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, Or.inl rfl, rfl⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.and, [j, k]⟩]) x.val).getD (n + new.length) false = (f x && g x)
      rw [W_val, if_pos rfl]
      show GateOp.and.eval [(W new x.val).getD j false, (W new x.val).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma rep_or {n : ℕ} {P : (Fin n → Bool) → Prop} (new : List Gate) (f g : (Subtype P) → Bool) (hf : Rep new f)
    (hg : Rep new g) : ∃ new', Ext new new' ∧ Rep new' (fun x => f x || g x) := by
  rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
  · cases c1 with
    | true =>
      exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
        show (f x || g x) = true
        simp [h1 x]⟩⟩
    | false =>
      exact ⟨new, Or.inl rfl, rep_congr (fun x => by
        show g x = (f x || g x)
        simp [h1 x]) hg⟩
  · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
    · cases c2 with
      | true =>
        exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
          show (f x || g x) = true
          simp [h2 x]⟩⟩
      | false =>
        exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
          show (W new x.val).getD j false = (f x || g x)
          rw [hjv x]
          simp [h2 x]⟩⟩
    · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, Or.inr rfl, rfl⟩,
        Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
          fun x => ?_⟩⟩
      show (W (new ++ [⟨GateOp.or, [j, k]⟩]) x.val).getD (n + new.length) false = (f x || g x)
      rw [W_val, if_pos rfl]
      show GateOp.or.eval [(W new x.val).getD j false, (W new x.val).getD k false] = _
      rw [hjv x, hkv x]
      simp [GateOp.eval]

lemma gate_rep {n : ℕ} {P : (Fin n → Bool) → Prop} (old new : List Gate)
    (op : GateOp) (l : List ℕ) (hop : op = GateOp.and ∨ op = GateOp.or) (hlen : l.length ≤ 2)
    (h : ∀ t : ℕ, Rep (P := P) new (fun x => (W old x.val).getD t false)) :
    ∃ new', Ext new new' ∧
      Rep (P := P) new' (fun x => op.eval (l.map fun i => (W old x.val).getD i false)) := by
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by simp [GateOp.eval]⟩⟩
    · exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by simp [GateOp.eval]⟩⟩
  · rcases hop with rfl | rfl
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
    · exact ⟨new, Or.inl rfl, rep_congr (fun x => by simp [GateOp.eval]) (h a)⟩
  · rcases hop with rfl | rfl
    · obtain ⟨new', he, hr⟩ := rep_and new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
    · obtain ⟨new', he, hr⟩ := rep_or new _ _ (h a) (h b)
      exact ⟨new', he, rep_congr (fun x => by simp [GateOp.eval]) hr⟩
  · simp only [List.length_cons] at hlen
    omega

variable {n : ℕ} {P : (Fin n → Bool) → Prop}

abbrev wire (old : List Gate) (t : ℕ) (x : Subtype P) := (W old x.val).getD t false
abbrev value (old : List Gate) (g : Gate) (x : Subtype P) :=
  g.op.eval (g.inputs.map fun i => wire old i x)
abbrev Good (g : Gate) := (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2

lemma reader_free (old new : List Gate) (g : Gate) (z : ℕ) (hg : Good g)
    (hm : z ∈ g.inputs) (hz : ∀ x : Subtype P, wire old z x = false)
    (hr : ∀ t, Rep (P := P) new (wire old t)) : Rep (P := P) new (value old g) := by
  obtain ⟨op,l⟩ := g
  obtain ⟨hop,hl⟩ := hg
  change z ∈ l at hm
  change l.length ≤ 2 at hl
  rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · simp at hm
  · simp at hm; subst a
    rcases hop with e | e <;> change op = _ at e <;> subst op <;>
      exact Or.inl ⟨false, fun x => by simpa [value, GateOp.eval, wire] using hz x⟩
  · simp at hm
    rcases hm with e | e <;> subst_vars <;> rcases hop with e | e <;>
      change op = _ at e <;> subst op
    · exact Or.inl ⟨false, fun x => by have h0 := hz x; simp [wire] at h0; simp [value, wire, GateOp.eval, h0]⟩
    · apply rep_congr _ (hr b); intro x; have h0 := hz x; simp [wire] at h0; simp [value, wire, GateOp.eval, h0]
    · exact Or.inl ⟨false, fun x => by have h0 := hz x; simp [wire] at h0; simp [value, wire, GateOp.eval, h0]⟩
    · apply rep_congr _ (hr a); intro x; have h0 := hz x; simp [wire] at h0; simp [value, wire, GateOp.eval, h0]
  · simp at hl

lemma stable (a b : List Gate) (x : Fin n → Bool) {t : ℕ} (ht : t < n + a.length) :
    (W (a ++ b) x).getD t false = (W a x).getD t false := by
  induction b using List.reverseRecOn with
  | nil => simp
  | append_singleton b g ih =>
    rw [← List.append_assoc, W_val, if_neg (by simp only [List.length_append]; omega), ih]

lemma take_stable (gs : List Gate) (k t : ℕ) (x : Fin n → Bool) (ht : t < n + (gs.take k).length) :
    (W (gs.take k) x).getD t false = (W gs x).getD t false := by
  simpa using (stable (gs.take k) (gs.drop k) x ht).symm

lemma compress (gs : List Gate) (start : ℕ) (hs : start ≤ gs.length)
    (S : Finset (Fin gs.length)) (hp : ∀ g ∈ gs.take start, Good g)
    (hbase : ∀ i ∈ S, start ≤ i.val)
    (action : ∀ (i : Fin gs.length), start ≤ i.val → ∀ new : List Gate,
      (∀ t, Rep (P := P) new (wire (gs.take i.val) t)) →
      ∃ new', Ext new new' ∧ (i ∈ S → new' = new) ∧ Rep (P := P) new' (value (gs.take i.val) (gs.get i))) :
    ∃ new, (∀ g ∈ new, Good g) ∧ gs.take start <+: new ∧ new.length + S.card ≤ gs.length ∧
      ∀ t, Rep (P := P) new (wire gs t) := by
  classical
  let C (k : ℕ) := (S.filter fun i => i.val < k).card
  have aux (k : ℕ) (hk : start ≤ k) (hk' : k ≤ gs.length) :
      ∃ new, (∀ g ∈ new, Good g) ∧ gs.take start <+: new ∧ new.length + C k ≤ k ∧
        ∀ t, Rep (P := P) new (wire (gs.take k) t) := by
    induction k, hk using Nat.le_induction with
    | base =>
      have hem : S.filter (fun i => i.val < start) = ∅ := by
        ext i; simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]; rintro ⟨hi, hh⟩; exact (hh.not_ge (hbase i hi))
      refine ⟨gs.take start, hp, by simp, by simp [C, hem, hs], fun t => ?_⟩
      by_cases ht : t < n + (gs.take start).length
      · exact Or.inr ⟨t, ht, fun _ => rfl⟩
      · exact Or.inl ⟨false, fun x => List.getD_eq_default _ _ (by rw [W_len]; omega)⟩
    | succ k hk ih =>
      let i : Fin gs.length := ⟨k, by omega⟩
      obtain ⟨new, hgood, hpre, hlen, hr⟩ := ih (by omega)
      obtain ⟨new', he, hfree, hv⟩ := action i hk new hr
      have heq : gs.take (k+1) = gs.take k ++ [gs.get i] := by
        exact List.take_succ_eq_append_getElem (by omega)
      refine ⟨new', ?_, ?_, ?_, fun t => ?_⟩
      · rcases he with rfl | ⟨g, rfl, hop, h2⟩
        · exact hgood
        · intro q hq; rcases List.mem_append.mp hq with h | h
          · exact hgood q h
          · simp only [List.mem_singleton] at h; subst q; exact ⟨hop, h2.le⟩
      · rcases he with rfl | ⟨g,rfl,_⟩
        · exact hpre
        · exact hpre.trans ⟨[g], rfl⟩
      · by_cases hi : i ∈ S
        · have eq : S.filter (fun q => q.val < k+1) = insert i (S.filter fun q => q.val < k) := by
            ext q; simp only [Finset.mem_filter, Finset.mem_insert]; constructor
            · rintro ⟨h, hl⟩; by_cases e : q.val = k
              · exact Or.inl (Fin.ext e)
              · exact Or.inr ⟨h, by omega⟩
            · rintro (rfl | ⟨h, hl⟩)
              · exact ⟨hi, Nat.lt_succ_self k⟩
              · exact ⟨h, by omega⟩
          have hc : C (k+1) = C k + 1 := by unfold C; rw [eq, Finset.card_insert_of_notMem (by simp [i])]
          rw [hfree hi, hc]; omega
        · have eq : S.filter (fun q => q.val < k+1) = S.filter (fun q => q.val < k) := by
            ext q; simp only [Finset.mem_filter]; constructor
            · rintro ⟨h, hl⟩; refine ⟨h, ?_⟩; by_contra! hn; exact hi ((show q = i from Fin.ext (by dsimp [i]; omega)) ▸ h)
            · rintro ⟨h, hl⟩; exact ⟨h, by omega⟩
          have hc : C (k+1) = C k := congrArg Finset.card eq
          rw [hc]; rcases he with rfl | ⟨g,rfl,_⟩ <;> simp_all only [List.length_append,List.length_singleton] <;> omega
      · rw [heq]; by_cases ht : t = n + (gs.take k).length
        · exact rep_congr (fun x => by unfold wire; rw [W_val, if_pos ht]) hv
        · exact rep_congr (fun x => by unfold wire; rw [W_val, if_neg ht]) (rep_mono he _ (hr t))
  simpa [C] using aux gs.length hs (le_refl _)

lemma value_eq (gs : List Gate) (i : Fin gs.length) (x : Subtype P) :
    value (gs.take i.val) (gs.get i) x = wire gs (n+i.val) x := by
  have heq : gs.take (i.val+1) = gs.take i.val ++ [gs.get i] := List.take_succ_eq_append_getElem i.isLt
  have hlt : n+i.val < n + (gs.take (i.val+1)).length := by simp [List.length_take, Nat.min_eq_left (Nat.succ_le_of_lt i.isLt)]
  unfold wire
  rw [← take_stable gs (i.val+1) _ x.val hlt, heq, W_val, if_pos (by simp [Nat.min_eq_left i.isLt.le])]

end PEqualNP.Outside.L_meta_1515
open PEqualNP.CircuitLowerBounds PEqualNP.Outside.L_meta_1515
theorem PEqualNP.Outside.L_meta_1515 : ∀ (n m : ℕ) (gates : List PEqualNP.CircuitLowerBounds.Gate) (out : Fin m → ℕ) (j h : Fin gates.length),
    (∀ g ∈ gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.not) ∧
      g.inputs.length ≤ 2) →
    (gates.get j).op = PEqualNP.CircuitLowerBounds.GateOp.not →
    (∀ i : Fin gates.length, (gates.get i).op = PEqualNP.CircuitLowerBounds.GateOp.not → i = j) →
    h < j → (∃ r : List ℕ, (gates.get j).inputs = (n + (h : ℕ)) :: r) →
    (∀ w : Fin m, ∃ x y : Fin n → Bool,
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn y) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x) = true ∧
      PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn y) = false) →
    ∃ (gates' : List PEqualNP.CircuitLowerBounds.Gate) (out' : Fin m → ℕ),
      (∀ g ∈ gates', (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length ≤ 2) ∧
      gates.take (h : ℕ) <+: gates' ∧
      gates'.length + (Finset.univ.filter (fun i : Fin gates.length => j < i ∧ n + (j : ℕ) ∈ (gates.get i).inputs)).card + 2
        ≤ gates.length ∧
      ∀ (w : Fin m) (x : Fin n → Bool),
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, n + (h : ℕ)⟩ (List.ofFn x) = true →
        PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates', out' w⟩ (List.ofFn x) = PEqualNP.CircuitLowerBounds.Circuit.eval ⟨gates, out w⟩ (List.ofFn x)
 := by
  classical
  intro n m gs out j h hb hj hu hh hin hw
  let P (x : Fin n → Bool) := (W gs x).getD (n+h.val) false = true
  let R := Finset.univ.filter (fun i : Fin gs.length => j < i ∧ n+j.val ∈ (gs.get i).inputs)
  let S := insert h (insert j R)
  have hval (x : Subtype P) : wire gs (n+h.val) x = true := x.property
  have earlier (i : Fin gs.length) {a : Fin gs.length} (ha : a < i) (x : Subtype P) :
      wire (gs.take i.val) (n+a.val) x = wire gs (n+a.val) x := by
    apply take_stable; simp [List.length_take, Nat.min_eq_left i.isLt.le]; exact ha
  have jval (x : Subtype P) : wire gs (n+j.val) x = false := by
    obtain ⟨r,hr⟩ := hin
    rw [← value_eq gs j x]; unfold value; rw [hj,hr]; change (!(wire (gs.take j.val) (n+h.val) x)) = false
    rw [earlier j hh, hval]; rfl
  have good (i : Fin gs.length) (hi : i ≠ j) : Good (gs.get i) := by
    obtain ⟨ho,hl⟩ := hb _ (List.get_mem gs i)
    exact ⟨ho.elim Or.inl (fun z => z.elim Or.inr (fun hn => False.elim (hi (hu i hn)))), hl⟩
  have hp : ∀ g ∈ gs.take h.val, Good g := by
    intro g hg
    obtain ⟨i,he⟩ := List.get_of_mem hg
    have il : i.val < h.val := lt_of_lt_of_le i.isLt (by simp)
    let a : Fin gs.length := ⟨i.val, by omega⟩
    have eq : gs.get a = g := by simpa [a, List.get_eq_getElem] using he
    rw [← eq]; apply good; intro e; have := congrArg Fin.val e; dsimp [a] at this; omega
  have base : ∀ i ∈ S, h.val ≤ i.val := by
    intro i hi; simp only [S, Finset.mem_insert, R, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rcases hi with rfl | rfl | ⟨lt,_⟩ <;> omega
  obtain ⟨new,hg,pre,budget,rep⟩ := compress (P := P) gs h.val h.isLt.le S hp base (by
    intro i _ new hr
    by_cases ih : i = h
    · subst i; exact ⟨new, Or.inl rfl, fun _ => rfl, Or.inl ⟨true, fun x => (value_eq gs h x).trans (hval x)⟩⟩
    by_cases ij : i = j
    · subst i; exact ⟨new, Or.inl rfl, fun _ => rfl, Or.inl ⟨false, fun x => (value_eq gs j x).trans (jval x)⟩⟩
    by_cases ir : i ∈ R
    · obtain ⟨lt,hm⟩ := (Finset.mem_filter.mp ir).2
      exact ⟨new, Or.inl rfl, fun _ => rfl, reader_free _ _ _ _ (good i ij) hm (fun x => (earlier i lt x).trans (jval x)) hr⟩
    · obtain ⟨new',he,hv⟩ := gate_rep _ new _ _ (good i ij).1 (good i ij).2 hr
      exact ⟨new',he,by simp [S, ih, ij, ir],hv⟩)
  have card : S.card = R.card + 2 := by
    have hR : h ∉ R := by simp [R, not_lt_of_ge hh.le]
    have jR : j ∉ R := by simp [R]
    simp [S, hR, jR, hh.ne, Nat.add_assoc]
  rw [card] at budget
  have idx (w : Fin m) : ∃ t, ∀ x : Subtype P, wire new t x = wire gs (out w) x := by
    rcases rep (out w) with ⟨c,hc⟩ | ⟨t,_,hv⟩
    · obtain ⟨x,y,hx,hy,ox,oy⟩ := hw w
      have eq := (hc ⟨x,hx⟩).trans (hc ⟨y,hy⟩).symm
      change Circuit.eval ⟨gs,out w⟩ (List.ofFn x) = Circuit.eval ⟨gs,out w⟩ (List.ofFn y) at eq
      simp [ox,oy] at eq
    · exact ⟨t,hv⟩
  choose f hf using idx
  exact ⟨new,f,hg,pre,by simpa [R, Nat.add_assoc] using budget,fun w x hx => hf w ⟨x,hx⟩⟩
