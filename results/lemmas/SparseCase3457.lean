import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_3457.StarCover

open PEqualNP.CircuitLowerBounds

-- A vertex cover circuit: for each cover vertex c (in increasing order) an OR chain of the
-- neighbours of c not already handled, ANDed with c; the AND gates are ORed together.

def wf (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

lemma wf_snoc (gs : List Gate) (g : Gate) (w : List Bool) :
    wf (gs ++ [g]) w = wf gs w ++ [g.op.eval (g.inputs.map fun i => (wf gs w).getD i false)] := by
  simp [wf, List.foldl_append]

def V {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) : List Bool :=
  List.ofFn x ++ fs.map (fun f => f x)

def Sem {n : ℕ} (gs : List Gate) (fs : List ((Fin n → Bool) → Bool)) : Prop :=
  ∀ x : Fin n → Bool, wf gs (List.ofFn x) = V fs x

def Val {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (i : ℕ) (F : (Fin n → Bool) → Bool) : Prop :=
  i < n + fs.length ∧ ∀ x, (V fs x).getD i false = F x

lemma V_append {n : ℕ} (fs fs' : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) :
    V (fs ++ fs') x = V fs x ++ fs'.map (fun f => f x) := by
  simp [V]

lemma V_length {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) :
    (V fs x).length = n + fs.length := by simp [V]

lemma V_read {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (x : Fin n → Bool) (j : ℕ)
    (hj : j < fs.length) : (V fs x).getD (n + j) false = fs.getD j (fun _ => false) x := by
  simp only [V]
  rw [List.getD_append_right _ _ _ _ (by simp)]
  simp [List.getD_eq_getElem?_getD, hj]

lemma val_ext {n : ℕ} {fs : List ((Fin n → Bool) → Bool)} {i : ℕ} {F : (Fin n → Bool) → Bool}
    (h : Val fs i F) (fs' : List ((Fin n → Bool) → Bool)) : Val (fs ++ fs') i F := by
  refine ⟨by have := h.1; simp; omega, fun x => ?_⟩
  rw [V_append, List.getD_append _ _ _ _ (by rw [V_length]; exact h.1)]
  exact h.2 x

lemma val_congr {n : ℕ} {fs : List ((Fin n → Bool) → Bool)} {i : ℕ}
    {F F' : (Fin n → Bool) → Bool} (h : Val fs i F) (e : ∀ x, F x = F' x) : Val fs i F' :=
  ⟨h.1, fun x => by rw [h.2 x, e x]⟩

lemma val_in {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (a : Fin n) :
    Val fs a.val (fun x => x a) := by
  refine ⟨by omega, fun x => ?_⟩
  simp only [V]
  rw [List.getD_append _ _ _ _ (by simp)]
  simp

lemma val_new {n : ℕ} (fs : List ((Fin n → Bool) → Bool)) (f : (Fin n → Bool) → Bool) :
    Val (fs ++ [f]) (n + fs.length) f := by
  refine ⟨by simp, fun x => ?_⟩
  rw [V_read _ _ _ (by simp)]
  rw [List.getD_append_right _ _ _ _ le_rfl]
  simp

lemma sem_snoc {n : ℕ} {gs : List Gate} {fs : List ((Fin n → Bool) → Bool)} (h : Sem gs fs)
    (op : GateOp) (a b : ℕ) (A B : (Fin n → Bool) → Bool) (ha : Val fs a A) (hb : Val fs b B) :
    Sem (gs ++ [⟨op, [a, b]⟩]) (fs ++ [fun x => op.eval [A x, B x]]) := by
  intro x
  rw [wf_snoc, h x, V_append]
  simp only [List.map_cons, List.map_nil, ha.2 x, hb.2 x]

def Mono (gs : List Gate) : Prop :=
  ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2

def Back (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < n + j

def St {n : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Prop) (gs : List Gate)
    (fs : List ((Fin n → Bool) → Bool)) : Prop :=
  Sem gs fs ∧ fs.length = gs.length ∧ Mono gs ∧
  (∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
    ∃ l, P l ∧ ∀ x, fs.getD j (fun _ => false) x = true → x l = true) ∧
  (∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
    ∃ c v : Fin n, G.Adj c v ∧
      fs.getD j (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c v) = true ∧
      ∀ i < j, (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and →
        fs.getD i (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c v) = false) ∧
  Back n gs ∧
  (∀ j < gs.length, (gs.getD j ⟨GateOp.or, []⟩).op = GateOp.and →
    ∀ x : Fin n → Bool, fs.getD j (fun _ => false) x = true →
      ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)

lemma st_nil {n : ℕ} (G : SimpleGraph (Fin n)) (P : Fin n → Prop) : St G P [] [] := by
  refine ⟨fun x => by simp [wf, V], rfl, by simp [Mono], ?_, ?_, ?_, ?_⟩ <;> simp [Back]

lemma st_weak {n : ℕ} {G : SimpleGraph (Fin n)} {P Q : Fin n → Prop} {gs fs}
    (h : St G P gs fs) (hPQ : ∀ l, P l → Q l) : St G Q gs fs := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h3, fun j hj hand => ?_, h5, h6, h7⟩
  obtain ⟨l, hl, hl2⟩ := h4 j hj hand
  exact ⟨l, hPQ l hl, hl2⟩

lemma push {n : ℕ} {G : SimpleGraph (Fin n)} {P : Fin n → Prop} {gs : List Gate}
    {fs : List ((Fin n → Bool) → Bool)} (h : St G P gs fs) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or) (a b : ℕ) (A B : (Fin n → Bool) → Bool)
    (ha : Val fs a A) (hb : Val fs b B)
    (nA : op = GateOp.and → ∃ l, P l ∧ ∀ x, op.eval [A x, B x] = true → x l = true)
    (nB : op = GateOp.and → ∃ c v : Fin n, G.Adj c v ∧
      op.eval [A (PEqualNP.EdgeOwnership.pairInput c v), B (PEqualNP.EdgeOwnership.pairInput c v)]
        = true ∧
      ∀ i < gs.length, (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and →
        fs.getD i (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c v) = false)
    (nClean : op = GateOp.and → ∀ x : Fin n → Bool,
      op.eval [A x, B x] = true → ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) :
    St G P (gs ++ [⟨op, [a, b]⟩]) (fs ++ [fun x => op.eval [A x, B x]]) ∧
      Val (fs ++ [fun x => op.eval [A x, B x]]) (n + fs.length) (fun x => op.eval [A x, B x]) := by
  obtain ⟨hs, hl, hm, hA, hB, hBack, hClean⟩ := h
  refine ⟨⟨sem_snoc hs op a b A B ha hb, by simp [hl], ?_, ?_, ?_, ?_, ?_⟩, val_new _ _⟩
  · intro g hg
    rcases List.mem_append.1 hg with hg | hg
    · exact hm g hg
    · simp only [List.mem_singleton] at hg
      subst hg
      rcases hop with e | e <;> simp [e]
  · intro j hj hand
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [List.getD_append _ _ _ _ hj] at hand
      obtain ⟨l, hl1, hl2⟩ := hA j hj hand
      refine ⟨l, hl1, fun x hx => hl2 x ?_⟩
      rwa [List.getD_append _ _ _ _ (by omega)] at hx
    · subst hj
      rw [List.getD_append_right _ _ _ _ le_rfl] at hand
      simp only [Nat.sub_self, List.getD_cons_zero] at hand
      obtain ⟨l, hl1, hl2⟩ := nA hand
      refine ⟨l, hl1, fun x hx => hl2 x ?_⟩
      rw [← hl, List.getD_append_right _ _ _ _ le_rfl] at hx
      simpa using hx
  · intro j hj hand
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [List.getD_append _ _ _ _ hj] at hand
      obtain ⟨c, v, hadj, h1, h2⟩ := hB j hj hand
      refine ⟨c, v, hadj, ?_, fun i hi hand' => ?_⟩
      · rw [List.getD_append _ _ _ _ (by omega)]; exact h1
      · rw [List.getD_append _ _ _ _ (by omega)] at hand'
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h2 i hi hand'
    · subst hj
      rw [List.getD_append_right _ _ _ _ le_rfl] at hand
      simp only [Nat.sub_self, List.getD_cons_zero] at hand
      obtain ⟨c, v, hadj, h1, h2⟩ := nB hand
      refine ⟨c, v, hadj, ?_, fun i hi hand' => ?_⟩
      · rw [← hl, List.getD_append_right _ _ _ _ le_rfl]
        simpa using h1
      · rw [List.getD_append _ _ _ _ hi] at hand'
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h2 i hi hand'

  · intro j hj i hi
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [List.getD_append _ _ _ _ hj] at hi
      exact hBack j hj i hi
    · subst hj
      rw [List.getD_append_right _ _ _ _ le_rfl] at hi
      simp only [Nat.sub_self, List.getD_cons_zero] at hi
      have hi' : i = a ∨ i = b := by
        simpa only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] using hi
      rcases hi' with rfl | rfl
      · have ha' := ha.1
        omega
      · have hb' := hb.1
        omega
  · intro j hj hand x hx
    rw [List.length_append, List.length_singleton] at hj
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | hj
    · rw [List.getD_append _ _ _ _ hj] at hand
      apply hClean j hj hand x
      rwa [List.getD_append _ _ _ _ (by omega)] at hx
    · subst hj
      rw [List.getD_append_right _ _ _ _ le_rfl] at hand
      simp only [Nat.sub_self, List.getD_cons_zero] at hand
      apply nClean hand x
      rw [← hl, List.getD_append_right _ _ _ _ le_rfl] at hx
      simpa using hx

lemma chain {n : ℕ} {G : SimpleGraph (Fin n)} {P : Fin n → Prop} :
    ∀ (rest : List (Fin n)) (gs : List Gate) (fs : List ((Fin n → Bool) → Bool)) (a : ℕ)
      (A : (Fin n → Bool) → Bool), St G P gs fs → Val fs a A →
      ∃ gs' fs' o, St G P gs' fs' ∧ (∃ fsn, fs' = fs ++ fsn) ∧
        gs'.length = gs.length + rest.length ∧
        Val fs' o (fun x => A x || rest.any (fun w => x w))
  | [], gs, fs, a, A, h, ha => ⟨gs, fs, a, h, ⟨[], by simp⟩, by simp, by simpa using ha⟩
  | w :: rest, gs, fs, a, A, h, ha => by
    obtain ⟨h1, h2⟩ := push h GateOp.or (Or.inr rfl) a w.val A (fun x => x w) ha (val_in fs w)
      (fun e => by simp at e) (fun e => by simp at e) (fun e => by simp at e)
    obtain ⟨gs', fs', o, h3, ⟨fsn, hfs⟩, hlen, hv⟩ := chain rest _ _ _ _ h1 h2
    refine ⟨gs', fs', o, h3, ⟨(fun x => GateOp.or.eval [A x, x w]) :: fsn, by rw [hfs]; simp⟩, ?_, ?_⟩
    · rw [hlen]; simp only [List.length_append, List.length_cons, List.length_nil]; omega
    refine ⟨hv.1, fun x => ?_⟩
    rw [hv.2 x]
    simp [GateOp.eval, Bool.or_assoc]

def N {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) (c : Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter (fun w => G.Adj c w ∧ ¬ (w ∈ C ∧ w < c))

def gad {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) (c : Fin n)
    (x : Fin n → Bool) : Bool :=
  x c && decide (∃ w ∈ N G C c, x w = true)

lemma gad_empty {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    {c : Fin n} (h : N G C c = ∅) (x : Fin n → Bool) : gad G C c x = false := by
  simp [gad, h]

lemma gadget {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    {P : Fin n → Prop} (c : Fin n) (hP : ∀ l, P l → l ∈ C ∧ l < c) (hne : (N G C c).Nonempty)
    (gs : List Gate) (fs : List ((Fin n → Bool) → Bool)) (h : St G P gs fs) :
    ∃ gs' fs' o, St G (fun l => P l ∨ l = c) gs' fs' ∧ (∃ fsn, fs' = fs ++ fsn) ∧
      gs'.length = gs.length + (N G C c).card ∧ Val fs' o (gad G C c) := by
  have hL : (N G C c).toList ≠ [] := by
    rw [Ne, Finset.toList_eq_nil]; exact hne.ne_empty
  obtain ⟨w0, rest, hL⟩ := List.exists_cons_of_ne_nil hL
  have hw0 : w0 ∈ N G C c := by
    rw [← Finset.mem_toList, hL]; exact List.mem_cons_self
  have hcard : (N G C c).card = rest.length + 1 := by
    rw [← Finset.length_toList, hL]; simp
  have key : ∀ x : Fin n → Bool,
      (x w0 || rest.any (fun w => x w)) = decide (∃ w ∈ N G C c, x w = true) := by
    intro x
    have : (x w0 || rest.any (fun w => x w)) = (N G C c).toList.any (fun w => x w) := by
      rw [hL]; simp
    rw [this, Bool.eq_iff_iff]
    simp [List.any_eq_true, Finset.mem_toList]
  obtain ⟨gs1, fs1, o1, h1, ⟨fsn, hfs⟩, hlen1, hv1⟩ :=
    chain rest gs fs w0.val (fun x => x w0) h (val_in fs w0)
  have hlab := h1.2.2.2.1
  have hl1 := h1.2.1
  obtain ⟨h2, hv2⟩ := push (st_weak (Q := fun l => P l ∨ l = c) h1 (fun l hl => Or.inl hl)) GateOp.and (Or.inl rfl) c.val o1
    (fun x => x c) _ (val_in fs1 c) hv1
    (fun _ => ⟨c, Or.inr rfl, fun x hx => by simp [GateOp.eval] at hx; exact hx.1⟩)
    (fun _ => ⟨c, w0, by
        simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hw0; exact hw0.1, by
        simp [GateOp.eval, PEqualNP.EdgeOwnership.pairInput], by
        intro i hi hand
        obtain ⟨l, hl, hl2⟩ := hlab i hi hand
        obtain ⟨hlC, hlc⟩ := hP l hl
        cases hval : fs1.getD i (fun _ => false) (PEqualNP.EdgeOwnership.pairInput c w0) with
        | false => rfl
        | true =>
          exfalso
          have := hl2 _ hval
          simp only [PEqualNP.EdgeOwnership.pairInput, decide_eq_true_eq] at this
          rcases this with rfl | rfl
          · exact lt_irrefl _ hlc
          · simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hw0
            exact hw0.2 ⟨hlC, hlc⟩⟩)
    (fun _ x hx => by
      have hx' : x c = true ∧ (x w0 || rest.any (fun w => x w)) = true := by
        simpa [GateOp.eval] using hx
      have hn : ∃ w ∈ N G C c, x w = true := by
        simpa only [key x, decide_eq_true_eq] using hx'.2
      obtain ⟨w, hw, hxw⟩ := hn
      exact ⟨c, w, (Finset.mem_filter.mp hw).2.1, hx'.1, hxw⟩)
  refine ⟨_, _, n + fs1.length, h2, ⟨fsn ++ [fun x => GateOp.and.eval [x c, x w0 || rest.any fun w => x w]], by rw [hfs]; simp⟩, ?_, ?_⟩
  · simp only [List.length_append, List.length_singleton, hlen1, hcard]; omega
  refine val_congr hv2 (fun x => ?_)
  simp only [GateOp.eval, gad, ← key x]
  simp

lemma build {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (S : Finset (Fin n)) : S ⊆ C →
    ∃ gs fs, St G (fun l => l ∈ S) gs fs ∧
      ((gs = [] ∧ ∀ c ∈ S, N G C c = ∅) ∨
       ∃ o, Val fs o (fun x => decide (∃ c ∈ S, gad G C c x = true)) ∧
         gs.length + 1 ≤ (∑ c ∈ S, (N G C c).card) + S.card) := by
  induction S using Finset.induction_on_max with
  | empty => intro _; exact ⟨[], [], st_nil G _, Or.inl ⟨rfl, by simp⟩⟩
  | insert c S hlt ih =>
    intro hsub
    have hcS : c ∉ S := fun hc => lt_irrefl _ (hlt c hc)
    obtain ⟨gs, fs, h, hcase⟩ := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
    have hP : ∀ l, l ∈ S → l ∈ C ∧ l < c :=
      fun l hl => ⟨hsub (Finset.mem_insert_of_mem hl), hlt l hl⟩
    by_cases hN : N G C c = ∅
    · refine ⟨gs, fs, st_weak h (fun l hl => Finset.mem_insert_of_mem hl), ?_⟩
      rcases hcase with ⟨hg, hall⟩ | ⟨o, hv, hlen⟩
      · left
        refine ⟨hg, ?_⟩
        intro c' hc'
        rcases Finset.mem_insert.1 hc' with rfl | hc'
        · exact hN
        · exact hall c' hc'
      · right
        refine ⟨o, val_congr hv ?_, ?_⟩
        · intro x
          simp [Finset.mem_insert, gad_empty hN]
        · rw [Finset.sum_insert hcS, Finset.card_insert_of_notMem hcS]; omega
    · have hne : (N G C c).Nonempty := Finset.nonempty_iff_ne_empty.2 hN
      obtain ⟨gs1, fs1, o1, h1, ⟨fsn, hfs⟩, hlen1, hv1⟩ := gadget c hP hne gs fs h
      have h1' : St G (fun l => l ∈ insert c S) gs1 fs1 := by
        refine st_weak h1 ?_
        intro l hl
        rcases hl with hl | rfl
        · exact Finset.mem_insert_of_mem hl
        · exact Finset.mem_insert_self _ _
      rcases hcase with ⟨hg, hall⟩ | ⟨o, hv, hlen⟩
      · refine ⟨gs1, fs1, h1', Or.inr ⟨o1, val_congr hv1 ?_, ?_⟩⟩
        · intro x
          have : ¬ ∃ c' ∈ S, gad G C c' x = true := by
            rintro ⟨c', hc', hg'⟩
            rw [gad_empty (hall c' hc')] at hg'
            exact Bool.false_ne_true hg'
          rw [Bool.eq_iff_iff]
          simp only [decide_eq_true_eq, Finset.mem_insert]
          constructor
          · intro hx; exact ⟨c, Or.inl rfl, hx⟩
          · rintro ⟨c', hc' | hc', hx⟩
            · subst hc'; exact hx
            · exact absurd ⟨c', hc', hx⟩ this
        · subst hg
          rw [Finset.sum_insert hcS, Finset.card_insert_of_notMem hcS]
          simp at hlen1
          omega
      · obtain ⟨h2, hv2⟩ := push h1' GateOp.or (Or.inr rfl) o o1 _ _
          (by rw [hfs]; exact val_ext hv fsn) hv1 (fun e => by simp at e) (fun e => by simp at e) (fun e => by simp at e)
        refine ⟨_, _, h2, Or.inr ⟨_, val_congr hv2 ?_, ?_⟩⟩
        · intro x
          rw [Bool.eq_iff_iff]
          simp only [GateOp.eval, List.any_cons, List.any_nil, Bool.or_false, id,
            Bool.or_eq_true, decide_eq_true_eq, Finset.mem_insert]
          constructor
          · rintro (⟨c', hc', hx⟩ | hx)
            · exact ⟨c', Or.inr hc', hx⟩
            · exact ⟨c, Or.inl rfl, hx⟩
          · rintro ⟨c', hc' | hc', hx⟩
            · subst hc'; exact Or.inr hx
            · exact Or.inl ⟨c', hc', hx⟩
        · rw [Finset.sum_insert hcS, Finset.card_insert_of_notMem hcS]
          simp only [List.length_append, List.length_singleton]
          omega

lemma edge_N {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    (hC : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C) {u v : Fin n} (h : G.Adj u v) :
    ∃ c ∈ C, ∃ w ∈ N G C c, (c = u ∧ w = v) ∨ (c = v ∧ w = u) := by
  simp only [N, Finset.mem_filter, Finset.mem_univ, true_and]
  rcases hC u v h with hu | hv
  · by_cases hv' : v ∈ C ∧ v < u
    · refine ⟨v, hv'.1, u, ⟨h.symm, fun hh => lt_asymm hh.2 hv'.2⟩, Or.inr ⟨rfl, rfl⟩⟩
    · exact ⟨u, hu, v, ⟨h, hv'⟩, Or.inl ⟨rfl, rfl⟩⟩
  · by_cases hu' : u ∈ C ∧ u < v
    · exact ⟨u, hu'.1, v, ⟨h, fun hh => lt_asymm hh.2 hu'.2⟩, Or.inl ⟨rfl, rfl⟩⟩
    · exact ⟨v, hv, u, ⟨h.symm, hu'⟩, Or.inr ⟨rfl, rfl⟩⟩

lemma any_gad {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Finset (Fin n)}
    (hC : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C) (x : Fin n → Bool) :
    decide (∃ c ∈ C, gad G C c x = true) = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ x := by
  rw [Bool.eq_iff_iff]
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, gad, decide_eq_true_eq,
    Bool.and_eq_true, Bool.or_eq_true, Finset.notMem_empty, false_and, exists_false,
    false_or]
  constructor
  · rintro ⟨c, -, hc, w, hw, hxw⟩
    simp only [N, Finset.mem_filter, Finset.mem_univ, true_and] at hw
    exact ⟨c, w, hw.1, hc, hxw⟩
  · rintro ⟨u, v, h, hu, hv⟩
    obtain ⟨c, hc, w, hw, ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩⟩ := edge_N hC h
    · exact ⟨c, hc, hu, w, hw, hv⟩
    · exact ⟨c, hc, hv, w, hw, hu⟩

lemma sumN_le {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n)) :
    ∑ c ∈ C, (N G C c).card ≤ G.edgeSet.ncard := by
  rw [← Finset.card_sigma]
  have : G.edgeSet.ncard = G.edgeFinset.card := by
    rw [← SimpleGraph.coe_edgeFinset, Set.ncard_coe_finset]
  rw [this]
  apply Finset.card_le_card_of_injOn (fun p => s(p.1, p.2))
  · intro p hp
    simp only [Finset.mem_coe, Finset.mem_sigma, N, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp
    simp only [Finset.mem_coe, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet]
    exact hp.2.1
  · rintro ⟨c, w⟩ hp ⟨c', w'⟩ hq hpq
    simp only [Finset.mem_coe, Finset.mem_sigma, N, Finset.mem_filter, Finset.mem_univ,
      true_and] at hp hq
    rcases Sym2.eq_iff.1 hpq with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · subst h1; subst h2; rfl
    · exfalso
      subst h1; subst h2
      have e1 : ¬ w < c := fun hl => hp.2.2 ⟨hq.1, hl⟩
      have e2 : ¬ c < w := fun hl => hq.2.2 ⟨hp.1, hl⟩
      have : c = w := le_antisymm (not_lt.1 e1) (not_lt.1 e2)
      subst this
      exact G.irrefl hp.2.1

lemma main (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Finset (Fin n))
    (hC : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G C) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack n D ∧
      PEqualNP.MetaComplexity.circuitFun n D = PEqualNP.MetaComplexity.NestedCover.graphFun G ∅ ∧
      D.size ≤ G.edgeSet.ncard + C.card - 1 ∧
      ∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = GateOp.and →
        ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n + j) false = true →
          ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  have hC' : ∀ u v, G.Adj u v → u ∈ C ∨ v ∈ C := hC
  obtain ⟨gs, fs, ⟨hs, hl, hm, -, -, hBack, hClean⟩, hcase⟩ := build G C C (subset_refl _)
  rcases hcase with ⟨hg, hall⟩ | ⟨o, hv, hlen⟩
  · subst hg
    refine ⟨⟨[], n⟩, by simp [PEqualNP.MetaComplexity.Monotone2], ?_, ?_, by simp [Circuit.size], ?_⟩
    · simp [PEqualNP.MetaComplexity.NestedCover.ReadsBack]
    · funext x
      rw [← any_gad hC' x]
      have : ¬ ∃ c ∈ C, gad G C c x = true := by
        rintro ⟨c', hc', hg'⟩
        rw [gad_empty (hall c' hc')] at hg'
        exact Bool.false_ne_true hg'
      simp only [this, decide_false]
      show (wf [] (List.ofFn x)).getD n false = false
      simp only [wf, List.foldl_nil]
      exact List.getD_eq_default _ _ (by simp)
    · intro j hj
      simp at hj
  · refine ⟨⟨gs, o⟩, hm, hBack, ?_, ?_, ?_⟩
    · funext x
      show (wf gs (List.ofFn x)).getD o false = _
      rw [hs x, hv.2 x]
      exact any_gad hC' x
    · have h1 := sumN_le G C
      show gs.length ≤ _
      omega
    · intro j hj hand x hx
      have hj' : j < gs.length := hj
      apply hClean j hj' hand x
      change (wf gs (List.ofFn x)).getD (n + j) false = true at hx
      rwa [hs x, V_read _ _ _ (by omega)] at hx

lemma clean_off_unit {n : ℕ} (G : SimpleGraph (Fin n)) (D : Circuit)
    (hclean : ∀ j < D.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = GateOp.and →
      ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n + j) false = true →
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) :
    ∀ j < D.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = GateOp.and →
      ∀ t : Fin n,
        (D.wires (List.ofFn (fun k : Fin n => decide (k = t)))).getD (n + j) false = false := by
  intro j hj hand t
  cases hval : (D.wires (List.ofFn (fun k : Fin n => decide (k = t)))).getD (n + j) false with
  | false => rfl
  | true =>
    obtain ⟨u, v, huv, hu, hv⟩ := hclean j hj hand _ hval
    simp only [decide_eq_true_eq] at hu hv
    subst u
    subst v
    exact False.elim (G.irrefl huv)

lemma clean_off_pair {n : ℕ} (G : SimpleGraph (Fin n)) (D : Circuit)
    (hclean : ∀ j < D.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = GateOp.and →
      ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n + j) false = true →
        ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) :
    ∀ j < D.gates.length,
      (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = GateOp.and →
      ∀ a b : Fin n, ¬ G.Adj a b →
        (D.wires (List.ofFn (fun k : Fin n => decide (k = a ∨ k = b)))).getD (n + j) false = false := by
  intro j hj hand a b hab
  cases hval : (D.wires (List.ofFn (fun k : Fin n => decide (k = a ∨ k = b)))).getD (n + j) false with
  | false => rfl
  | true =>
    obtain ⟨u, v, huv, hu, hv⟩ := hclean j hj hand _ hval
    simp only [decide_eq_true_eq] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · exact False.elim (G.irrefl huv)
    · exact False.elim (hab huv)
    · exact False.elim (hab huv.symm)
    · exact False.elim (G.irrefl huv)

lemma left_ne_right {N : ℕ} (p l : Fin N) :
    Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have hv := congrArg Fin.val h
  simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
  omega

def incidenceGraph (N : ℕ) (I : Fin N → Fin N → Prop) : SimpleGraph (Fin (N + N)) where
  Adj u v := (∃ p l : Fin N, I p l ∧ u = Fin.castAdd N p ∧ v = Fin.natAdd N l) ∨
    (∃ p l : Fin N, I p l ∧ u = Fin.natAdd N l ∧ v = Fin.castAdd N p)
  symm := by
    constructor
    intro u v h
    rcases h with ⟨p, l, hI, hp, hl⟩ | ⟨p, l, hI, hl, hp⟩
    · exact Or.inr ⟨p, l, hI, hl, hp⟩
    · exact Or.inl ⟨p, l, hI, hp, hl⟩
  loopless := by
    constructor
    intro u h
    rcases h with ⟨p, l, _, hp, hl⟩ | ⟨p, l, _, hl, hp⟩
    · exact left_ne_right p l (hp.symm.trans hl)
    · exact left_ne_right p l (hp.symm.trans hl)

lemma incidenceGraph_left_right (N : ℕ) (I : Fin N → Fin N → Prop) (p l : Fin N) :
    (incidenceGraph N I).Adj (Fin.castAdd N p) (Fin.natAdd N l) ↔ I p l := by
  constructor
  · intro h
    rcases h with ⟨p', l', hI, hp, hl⟩ | ⟨p', l', _, hp, _⟩
    · have hp' : p = p' := Fin.ext (by simpa only [Fin.val_castAdd] using congrArg Fin.val hp)
      have hl' : l = l' := Fin.ext (by
        have hv := congrArg Fin.val hl
        simp only [Fin.val_natAdd] at hv
        omega)
      subst p'
      subst l'
      exact hI
    · exact False.elim (left_ne_right p l' hp)
  · intro hI
    exact Or.inl ⟨p, l, hI, rfl, rfl⟩

lemma incidence_graphFun (N : ℕ) (I : Fin N → Fin N → Prop)
    [DecidableRel (incidenceGraph N I).Adj] (z : Fin (N + N) → Bool) :
    PEqualNP.MetaComplexity.NestedCover.graphFun (incidenceGraph N I) ∅ z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true := by
  simp only [PEqualNP.MetaComplexity.NestedCover.graphFun, Bool.or_eq_true,
    decide_eq_true_eq, Finset.notMem_empty, false_and, exists_false, false_or]
  constructor
  · rintro ⟨u, v, h, hu, hv⟩
    rcases h with ⟨p, l, hI, rfl, rfl⟩ | ⟨p, l, hI, rfl, rfl⟩
    · exact ⟨p, l, hI, hu, hv⟩
    · exact ⟨p, l, hI, hv, hu⟩
  · rintro ⟨p, l, hI, hp, hl⟩
    exact ⟨Fin.castAdd N p, Fin.natAdd N l, Or.inl ⟨p, l, hI, rfl, rfl⟩, hp, hl⟩

lemma incidence_cover (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (S : Finset (Fin (N + N)))
    (hcover : ∀ p l : Fin N, I p l → Fin.castAdd N p ∈ S ∨ Fin.natAdd N l ∈ S) :
    ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧
      D.size ≤ (incidenceGraph N I).edgeSet.ncard + S.card - 1 ∧
      (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = GateOp.and →
        ∀ p l : Fin N, ¬ I p l →
          (D.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD (N + N + j) false = false) ∧
      (∀ j < D.gates.length, (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = GateOp.and →
        (∀ p : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
        ∀ l : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  classical
  let G := incidenceGraph N I
  have hS : PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S := by
    intro u v h
    rcases h with ⟨p, l, hI, rfl, rfl⟩ | ⟨p, l, hI, rfl, rfl⟩
    · exact hcover p l hI
    · exact (hcover p l hI).symm
  obtain ⟨D, hmono, hback, hfun, hsize, hclean⟩ := main (N + N) G S hS
  refine ⟨D, hmono, hback, hsize, ?_, ?_, ?_⟩
  · intro z
    rw [hfun]
    exact incidence_graphFun N I z
  · intro j hj hand p l hI
    exact clean_off_pair G D hclean j hj hand (Fin.castAdd N p) (Fin.natAdd N l)
      (fun h => hI ((incidenceGraph_left_right N I p l).1 h))
  · intro j hj hand
    constructor
    · intro p
      exact clean_off_unit G D hclean j hj hand (Fin.castAdd N p)
    · intro l
      exact clean_off_unit G D hclean j hj hand (Fin.natAdd N l)

end PEqualNP.Outside.L_meta_3457.StarCover

namespace PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
open PEqualNP.CircuitLowerBounds
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
lemma getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]
lemma final_gates (v : List Bool) (k o0 o1 : ℕ) (hk : k < v.length) (h0 : o0 < v.length)
    (h1 : o1 < v.length) :
    (wiresFrom [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [v.length, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [v.length + 1, v.length + 2]⟩] v).getD (v.length + 3) false
      = ((!(v.getD k false) && v.getD o0 false) || (v.getD k false && v.getD o1 false)) := by
  have A : ∀ (t : List Bool) (i : ℕ), i < v.length → (v ++ t)[i]?.getD false = v[i]?.getD false := by
    intro t i h; rw [List.getElem?_append_left h]
  simp [wiresFrom, GateOp.eval, A _ _ hk, A _ _ h0, A _ _ h1]
def Ok (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2
lemma shannon (k : ℕ) : ∀ (f : (Fin k → Bool) → Bool) (m : ℕ), k ≤ m →
    ∃ (gs : List Gate) (out : ℕ), (∀ g ∈ gs, Ok g) ∧ gs.length + 4 ≤ 5 * 2 ^ k ∧
      out < m + gs.length ∧
      ∀ w : List Bool, w.length = m →
        (wiresFrom gs w).getD out false = f (fun i : Fin k => w.getD i false) := by
  induction k with
  | zero =>
    intro f m _
    refine ⟨[⟨if f (fun i => i.elim0) = true then GateOp.and else GateOp.or, []⟩], m, ?_, by simp,
      by simp, ?_⟩
    · intro g hg
      simp only [List.mem_singleton] at hg
      subst hg
      refine ⟨?_, by simp⟩
      by_cases h : f (fun i => i.elim0) = true <;> simp [h]
    · intro w hw
      have hf : (fun i : Fin 0 => w.getD i false) = (fun i => i.elim0) := Subsingleton.elim _ _
      rw [hf]
      by_cases h : f (fun i => i.elim0) = true <;>
        simp [wiresFrom, h, ← hw, GateOp.eval]
  | succ k ih =>
    intro f m hm
    obtain ⟨gs0, o0, ok0, len0, ho0, ev0⟩ :=
      ih (fun y => f (Fin.snoc y false)) m (by omega)
    obtain ⟨gs1, o1, ok1, len1, ho1, ev1⟩ :=
      ih (fun y => f (Fin.snoc y true)) (m + gs0.length) (by omega)
    let M := m + gs0.length + gs1.length
    refine ⟨gs0 ++ gs1 ++ [⟨GateOp.not, [k]⟩, ⟨GateOp.and, [M, o0]⟩, ⟨GateOp.and, [k, o1]⟩,
      ⟨GateOp.or, [M + 1, M + 2]⟩], M + 3, ?_, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
      rcases hg with (hg | hg) | hg | hg | hg | hg
      · exact ok0 g hg
      · exact ok1 g hg
      all_goals (subst hg; simp [Ok])
    · simp only [List.length_append, List.length_cons, List.length_nil]
      rw [pow_succ]; omega
    · simp only [List.length_append, List.length_cons, List.length_nil]; omega
    · intro w hw
      rw [wiresFrom_append, wiresFrom_append]
      set w1 := wiresFrom gs0 w with hw1
      set w2 := wiresFrom gs1 w1 with hw2
      have l1 : w1.length = m + gs0.length := by rw [hw1, length_wiresFrom, hw]
      have l2 : w2.length = M := by rw [hw2, length_wiresFrom, l1]
      have e0 : w2.getD o0 false = f (Fin.snoc (fun i : Fin k => w.getD i false) false) := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega)]; exact ev0 w hw
      have e1 : w2.getD o1 false = f (Fin.snoc (fun i : Fin k => w.getD i false) true) := by
        rw [ev1 w1 l1]
        congr 2; funext i
        exact getD_wiresFrom _ _ _ (by have := i.isLt; omega)
      have ek : w2.getD k false = w.getD k false := by
        rw [hw2, getD_wiresFrom _ _ _ (by omega), hw1, getD_wiresFrom _ _ _ (by omega)]
      have hx : (fun i : Fin (k + 1) => w.getD i false)
          = Fin.snoc (fun i : Fin k => w.getD i false) (w.getD k false) := by
        funext i
        refine Fin.lastCases ?_ (fun j => ?_) i <;> simp
      rw [hx]
      have hk2 : k < w2.length := by omega
      have h02 : o0 < w2.length := by omega
      have h12 : o1 < w2.length := by omega
      rw [show M = w2.length from l2.symm, final_gates w2 k o0 o1 hk2 h02 h12, ek, e0, e1]
      cases w.getD k false <;> simp
end PEqualNP.Outside.L_meta_3457.SparseLower.Helpers

namespace PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
open PEqualNP.CircuitLowerBounds
variable {n : ℕ}
lemma getD_snoc_ne {α : Type} (L : List α) (S d : α) (j : ℕ) (h : j ≠ L.length) :
    (L ++ [S]).getD j d = L.getD j d := by
  by_cases hj : j < L.length
  · exact List.getD_append _ _ _ _ hj
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
lemma getD_snoc_eq {α : Type} (L : List α) (S d : α) : (L ++ [S]).getD L.length d = S := by
  simp
def gateSupp (L : List (Finset (Fin n))) (g : Gate) : Finset (Fin n) :=
  (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅
lemma mem_foldr_union (l : List ℕ) (F : ℕ → Finset (Fin n)) (i : Fin n) :
    i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l, i ∈ F a := by
  induction l with
  | nil => simp
  | cons b l ih => simp [ih]
lemma mem_gateSupp (L : List (Finset (Fin n))) (g : Gate) (i : Fin n) :
    i ∈ gateSupp L g ↔ ∃ a ∈ g.inputs, i ∈ L.getD a ∅ :=
  mem_foldr_union _ _ _
def suppsFrom (gs : List Gate) (L : List (Finset (Fin n))) : List (Finset (Fin n)) :=
  gs.foldl (fun L g => L ++ [gateSupp L g]) L
def inputSupps (n : ℕ) : List (Finset (Fin n)) := List.ofFn fun i : Fin n => {i}
def Agree (x y : Fin n → Bool) (L : List (Finset (Fin n))) (w w' : List Bool) : Prop :=
  L.length = w.length ∧ w.length = w'.length ∧
    ∀ j : ℕ, (∀ i ∈ L.getD j ∅, x i = y i) → w.getD j false = w'.getD j false
lemma agree_wiresFrom (x y : Fin n → Bool) (gs : List Gate) :
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
lemma agree_inputs (x y : Fin n → Bool) :
    Agree x y (inputSupps n) (List.ofFn x) (List.ofFn y) := by
  refine ⟨by simp [inputSupps], by simp, ?_⟩
  intro j hj
  by_cases hjn : j < n
  · have hx : x ⟨j, hjn⟩ = y ⟨j, hjn⟩ := hj _ (by simp [inputSupps, hjn])
    simp [hjn, hx]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
def Cnt (t : ℕ) (L : List (Finset (Fin n))) : Prop :=
  ∀ W : Finset ℕ, (W.biUnion fun j => L.getD j ∅).card ≤ t + W.card
lemma cnt_inputs : Cnt 0 (inputSupps n) := by
  intro W
  refine le_trans Finset.card_biUnion_le ?_
  rw [zero_add, Finset.card_eq_sum_ones]
  apply Finset.sum_le_sum
  intro j _
  by_cases hjn : j < n
  · simp [inputSupps, hjn]
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp
lemma cnt_step (t : ℕ) (L : List (Finset (Fin n))) (g : Gate) (hg : g.inputs.length ≤ 2)
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
lemma cnt_suppsFrom (gs : List Gate) : ∀ (t : ℕ) (L : List (Finset (Fin n))),
    (∀ g ∈ gs, Ok g) → Cnt t L → Cnt (t + gs.length) (suppsFrom gs L) := by
  induction gs with
  | nil => intro t L _ h; exact h
  | cons g gs ih =>
    intro t L hok h
    have := ih (t + 1) (L ++ [gateSupp L g]) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (cnt_step t L g (hok g List.mem_cons_self).2 h)
    rw [List.length_cons, show t + (gs.length + 1) = t + 1 + gs.length by omega]
    exact this
lemma dep_lower (n : ℕ) (f : (Fin n → Bool) → Bool)
    (hdep : ∀ i : Fin n, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : PEqualNP.MetaComplexity.HasCircuitSize n f s) : n ≤ s + 1 := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set S := (suppsFrom C.gates (inputSupps n)).getD C.output ∅ with hS
  have hall : ∀ i : Fin n, i ∈ S := by
    intro i
    by_contra hi
    obtain ⟨x, hx⟩ := hdep i
    apply hx
    have hag := (agree_wiresFrom (Function.update x i (!x i)) x C.gates _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ i := fun e => hi (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hev, ← hev]
    exact hag
  have hcard : S.card = n := by
    rw [Finset.eq_univ_of_forall hall]; simp
  have hc := cnt_suppsFrom C.gates 0 (inputSupps n) ok cnt_inputs {C.output}
  simp only [Finset.singleton_biUnion, Finset.card_singleton, zero_add] at hc
  rw [← hS, hcard] at hc
  omega
end PEqualNP.Outside.L_meta_3457.SparseLower.Helpers

namespace PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
open PEqualNP.CircuitLowerBounds
def normGate (g : Gate) : Gate :=
  match g.op with
  | GateOp.not => ⟨GateOp.not, g.inputs.take 1⟩
  | _ => g
lemma normGate_eval (g : Gate) (F : ℕ → Bool) :
    (normGate g).op.eval ((normGate g).inputs.map F) = g.op.eval (g.inputs.map F) := by
  obtain ⟨op, inputs⟩ := g
  cases op <;> simp only [normGate]
  cases inputs <;> simp [GateOp.eval]
def NOk (g : Gate) : Prop := Ok g ∧ (g.op = GateOp.not → g.inputs.length ≤ 1)
lemma normGate_nok (g : Gate) (h : Ok g) : NOk (normGate g) := by
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
lemma wiresFrom_norm (gs : List Gate) : ∀ w : List Bool,
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
inductive Stat : Type
  | const (c : Bool)
  | wire (j : ℕ)
def Stat.val (w : List Bool) : Stat → Bool
  | Stat.const c => c
  | Stat.wire j => w.getD j false
def Stat.Valid (m : ℕ) : Stat → Prop
  | Stat.const _ => True
  | Stat.wire j => j < m
def simpNot (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | Stat.const c :: _ => (none, Stat.const (!c))
  | Stat.wire j :: _ => (some ⟨GateOp.not, [j]⟩, Stat.wire m)
def simpAnd (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const true)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c && d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.wire j else Stat.const false)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.and, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)
def simpOr (m : ℕ) : List Stat → Option Gate × Stat
  | [] => (none, Stat.const false)
  | [Stat.const c] => (none, Stat.const c)
  | [Stat.wire j] => (none, Stat.wire j)
  | [Stat.const c, Stat.const d] => (none, Stat.const (c || d))
  | [Stat.const c, Stat.wire j] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.const c] => (none, bif c then Stat.const true else Stat.wire j)
  | [Stat.wire j, Stat.wire k] => (some ⟨GateOp.or, [j, k]⟩, Stat.wire m)
  | _ => (none, Stat.const false)
def simplify (op : GateOp) (m : ℕ) (ins : List Stat) : Option Gate × Stat :=
  match op with
  | GateOp.and => simpAnd m ins
  | GateOp.or => simpOr m ins
  | GateOp.not => simpNot m ins
  | _ => (none, Stat.const false)
lemma simplify_ok (op : GateOp) (m : ℕ) (ins : List Stat) :
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
lemma simplify_count (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (hc : ∃ c, Stat.const c ∈ ins) :
    (simplify op m ins).1 = none := by
  obtain ⟨c, hc⟩ := hc
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpAnd]
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨b, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]
lemma simplify_sound (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not)
    (w : List Bool) (ins : List Stat) (hlen : ins.length ≤ 2)
    (hv : ∀ s ∈ ins, s.Valid w.length) :
    ((simplify op w.length ins).2).Valid (w.length + (simplify op w.length ins).1.toList.length) ∧
    ((simplify op w.length ins).2).val (wiresFrom (simplify op w.length ins).1.toList w)
      = op.eval (ins.map (Stat.val w)) := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpAnd, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨d, l⟩⟩⟩
    · simp [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · cases a <;> cases b <;> (try rename_i c e; cases c) <;> (try cases e) <;>
        simp_all [simplify, simpOr, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · simp [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval]
    · cases a <;> simp_all [simplify, simpNot, Stat.Valid, Stat.val, GateOp.eval, wiresFrom]
def elimStep (n : ℕ) (acc : List Stat × List Gate) (g : Gate) : List Stat × List Gate :=
  (acc.1 ++ [(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2],
    acc.2 ++ (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)
def elim (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) : List Stat × List Gate :=
  gs.foldl (elimStep n) acc
lemma getD_snoc_len {α : Type} (L : List α) (S d : α) (k : ℕ) (h : L.length = k) :
    (L ++ [S]).getD k d = S := by
  subst h; simp
lemma elim_getD (n k : ℕ) (d : Stat) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    k < acc.1.length → (elim n gs acc).1.getD k d = acc.1.getD k d := by
  induction gs with
  | nil => intro acc _; rfl
  | cons g gs ih =>
    intro acc hk
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ih (elimStep n acc g) (by simp [elimStep]; omega)]
    exact getD_snoc_ne _ _ _ _ (by omega)
lemma toList_length_le {α : Type} (o : Option α) : o.toList.length ≤ 1 := by
  cases o <;> simp
lemma elim_ok (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
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
lemma elim_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).2.length ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc; simp [elim]
  | cons g gs ih =>
    intro acc
    have h1 := ih (elimStep n acc g)
    have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
      simp only [elimStep, List.length_append]
      have := toList_length_le (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
      omega
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]; omega
lemma elim_len_lt (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length → (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (∃ g ∈ gs, k ∈ g.inputs) → (elim n gs acc).2.length + 1 ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _ h; obtain ⟨g, hg, _⟩ := h; simp at hg
  | cons g gs ih =>
    intro acc hok hk hc hex
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons]
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
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
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      omega
lemma Stat.valid_mono {m m' : ℕ} (h : m ≤ m') : ∀ s : Stat, s.Valid m → s.Valid m'
  | Stat.const _, _ => trivial
  | Stat.wire _, hj => lt_of_lt_of_le hj h
lemma Stat.val_append (w t : List Bool) : ∀ s : Stat, s.Valid w.length →
    s.val (w ++ t) = s.val w
  | Stat.const _, _ => rfl
  | Stat.wire _, hj => List.getD_append _ _ _ _ hj
def Inv (n : ℕ) (y : List Bool) (w : List Bool) (acc : List Stat × List Gate) : Prop :=
  acc.1.length = w.length ∧ ∀ i : ℕ,
    (acc.1.getD i (Stat.const false)).Valid (n + acc.2.length) ∧
    (acc.1.getD i (Stat.const false)).val (wiresFrom acc.2 y) = w.getD i false
lemma inv_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
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
    set ins := g.inputs.map fun i => acc.1.getD i (Stat.const false) with hins
    have hgok := hok g List.mem_cons_self
    have hs := simplify_sound g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
      (by
        intro s hs
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        rw [lw']; exact (hi a).1)
    rw [lw'] at hs
    set r := simplify g.op (n + acc.2.length) ins with hr
    have hvals : ins.map (Stat.val w') = g.inputs.map fun i => w.getD i false := by
      rw [hins, List.map_map]
      apply List.map_congr_left
      intro a _
      exact (hi a).2
    have hnew : wiresFrom (acc.2 ++ r.1.toList) y = wiresFrom r.1.toList w' := by
      rw [wiresFrom_append]
    obtain ⟨t, ht, htl⟩ := wiresFrom_prefix r.1.toList w'
    refine ⟨by simp [elimStep, hl], ?_⟩
    intro i
    show ((acc.1 ++ [r.2]).getD i (Stat.const false)).Valid (n + (acc.2 ++ r.1.toList).length) ∧
      ((acc.1 ++ [r.2]).getD i (Stat.const false)).val (wiresFrom (acc.2 ++ r.1.toList) y) = _
    rw [hnew, List.length_append, ← Nat.add_assoc]
    by_cases hil : i = acc.1.length
    · subst hil
      rw [getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨hs.1, by rw [hs.2, hvals]⟩
    · rw [getD_snoc_ne _ _ _ _ hil, getD_snoc_ne _ _ _ _ (by omega)]
      refine ⟨Stat.valid_mono (by omega) _ (hi i).1, ?_⟩
      rw [ht, Stat.val_append _ _ _ (by rw [lw']; exact (hi i).1)]
      exact (hi i).2
def initStats (n : ℕ) (b : Bool) : List Stat :=
  List.ofFn (fun i : Fin n => Stat.wire i) ++ [Stat.const b]
lemma inv_init (n : ℕ) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y ++ [b]) (initStats n b, []) := by
  refine ⟨by simp [initStats], ?_⟩
  intro i
  have l1 : (List.ofFn (fun i : Fin n => Stat.wire i)).length = n := by simp
  have l2 : (List.ofFn y).length = n := by simp
  by_cases hin : i = n
  · subst hin
    simp only [initStats]
    rw [getD_snoc_len _ _ _ _ l1, getD_snoc_len _ _ _ _ l2]
    exact ⟨trivial, rfl⟩
  · simp only [initStats]
    rw [getD_snoc_ne _ _ _ _ (by omega), getD_snoc_ne _ _ _ _ (by omega)]
    by_cases hlt : i < n
    · simp [hlt, Stat.Valid, Stat.val, wiresFrom]
    · rw [List.getD_eq_default _ _ (by omega), List.getD_eq_default _ _ (by omega)]
      exact ⟨trivial, rfl⟩
lemma ofFn_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool) = List.ofFn y ++ [b] := by
  rw [List.ofFn_succ']
  simp
lemma supp_noread (n : ℕ) (gs : List Gate) : ∀ L : List (Finset (Fin (n + 1))),
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
lemma inputSupps_getD (m j : ℕ) (h : j < m) :
    (inputSupps m).getD j ∅ = {⟨j, h⟩} := by
  simp [inputSupps, h]
lemma inputSupps_noread (n : ℕ) : ∀ j : ℕ, j ≠ n →
    Fin.last n ∉ (inputSupps (n + 1)).getD j ∅ := by
  intro j hj
  by_cases hlt : j < n + 1
  · have e : (inputSupps (n + 1)).getD j ∅ = {⟨j, hlt⟩} := inputSupps_getD (n + 1) j hlt
    rw [e, Finset.mem_singleton]
    intro e'
    exact hj (by have := congrArg Fin.val e'; simpa using this.symm)
  · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp
lemma gate_elim (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (b : Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : PEqualNP.MetaComplexity.HasCircuitSize (n + 1) f (s + 1)) :
    PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s + 1 := hsz
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
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y))
        = f (Fin.snoc y b) := by
    intro y
    rw [((hinv y).2 C.output).2, hevg]
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) := by
    obtain ⟨y, _, _⟩ := hnc
    exact ((hinv y).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    have hlen : acc.2.length ≤ s := by
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
          have hb : (initStats n b).getD n (Stat.const false) = Stat.const b :=
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
    refine ⟨⟨acc.2, j⟩, elim_ok n gs _ (by simp), hlen, ?_⟩
    intro y
    have := hval y
    rw [hst] at this
    exact this
end PEqualNP.Outside.L_meta_3457.SparseLower.Helpers

namespace PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
open PEqualNP.CircuitLowerBounds
lemma elim_cons (n : ℕ) (g : Gate) (gs : List Gate) (acc : List Stat × List Gate) :
    elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
lemma elim_append (n : ℕ) (pre post : List Gate) (acc : List Stat × List Gate) :
    elim n (pre ++ post) acc = elim n post (elim n pre acc) := by
  simp [elim, List.foldl_append]
lemma elim_fst_len (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (elim n gs acc).1.length = acc.1.length + gs.length := by
  induction gs with
  | nil => intro acc; rfl
  | cons g gs ih =>
    intro acc
    rw [elim_cons, ih]
    simp only [elimStep, List.length_append, List.length_cons, List.length_nil]
    omega
lemma initStats_last (n : ℕ) (b : Bool) :
    (initStats n b).getD n (Stat.const false) = Stat.const b :=
  getD_snoc_len _ _ _ _ (by simp)
lemma simplify_const (op : GateOp) (m : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (hnot : op = GateOp.not → ins.length ≤ 1) (b : Bool)
    (hand : op = GateOp.and → b = false) (hor : op = GateOp.or → b = true)
    (hc : Stat.const b ∈ ins) : ∃ c, (simplify op m ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · have := hand rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpAnd]
  · have := hor rfl
    subst this
    rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩ <;> (try cases a) <;> (try cases d) <;>
      simp_all [simplify, simpOr]
  · have := hnot rfl
    rcases ins with _ | ⟨a, _ | ⟨d, l⟩⟩ <;> (try cases a) <;> simp_all [simplify, simpNot]
lemma elimStep_none (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (c : Bool) (hc : acc.1.getD k (Stat.const false) = Stat.const c) :
    (elimStep n acc g).2.length = acc.2.length := by
  have hnone : (simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
    apply simplify_count
    · exact hg.1.1
    · simpa using hg.1.2
    · intro h; simpa using hg.2 h
    · exact ⟨c, List.mem_map.2 ⟨k, hk, hc⟩⟩
  show (acc.2 ++ (simplify g.op (n + acc.2.length)
    (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
  rw [hnone]; simp
def fixBit (g : Gate) : Bool :=
  match g.op with
  | GateOp.or => true
  | _ => false
lemma elimStep_const (n : ℕ) (acc : List Stat × List Gate) (g : Gate) (hg : NOk g) (k : ℕ)
    (hk : k ∈ g.inputs) (hc : acc.1.getD k (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elimStep n acc g).1.getD acc.1.length (Stat.const false) = Stat.const c := by
  have e : (elimStep n acc g).1.getD acc.1.length (Stat.const false)
      = (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).2 := getD_snoc_eq _ _ _
  rw [e]
  apply simplify_const _ _ _ hg.1.1 (by simpa using hg.1.2) (fun h => by simpa using hg.2 h)
    (fixBit g)
  · intro h; simp [fixBit, h]
  · intro h; simp [fixBit, h]
  · exact List.mem_map.2 ⟨k, hk, hc⟩
lemma suppsFrom_append {n : ℕ} (pre post : List Gate) (L : List (Finset (Fin n))) :
    suppsFrom (pre ++ post) L = suppsFrom post (suppsFrom pre L) := by
  simp [suppsFrom, List.foldl_append]
lemma length_suppsFrom {n : ℕ} (gs : List Gate) : ∀ L : List (Finset (Fin n)),
    (suppsFrom gs L).length = L.length + gs.length := by
  induction gs with
  | nil => intro L; rfl
  | cons g gs ih =>
    intro L
    have h : suppsFrom (g :: gs) L = suppsFrom gs (L ++ [gateSupp L g]) := rfl
    rw [h, ih]
    simp only [List.length_append, List.length_cons, List.length_nil]
    omega
lemma supp_noreadD (n : ℕ) (D : ℕ → Prop) (gs : List Gate) :
    ∀ L : List (Finset (Fin (n + 1))),
    (∀ g ∈ gs, ∀ a ∈ g.inputs, ¬ D a) → (∀ j : ℕ, ¬ D j → Fin.last n ∉ L.getD j ∅) →
    ∀ j : ℕ, ¬ D j → Fin.last n ∉ (suppsFrom gs L).getD j ∅ := by
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
      exact h a (hno g List.mem_cons_self a ha) hia
    · rw [getD_snoc_ne _ _ _ _ hjl]; exact h j hj
lemma two_saved (n : ℕ) (gs : List Gate) (hnok : ∀ g ∈ gs, NOk g) (o : ℕ)
    (hdep : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ b c, (elim n gs (initStats n b, [])).1.getD o (Stat.const false) ≠ Stat.const c) :
    ∃ b, (elim n gs (initStats n b, [])).2.length + 2 ≤ gs.length := by
  have hon : o ≠ n := by
    intro e
    apply hout false false
    rw [e, elim_getD n n _ gs _ (by simp [initStats])]
    exact initStats_last n false
  by_cases hread : ∃ g ∈ gs, n ∈ g.inputs
  swap
  · exfalso
    push Not at hread
    exact supp_noread n gs (inputSupps (n + 1)) hread (inputSupps_noread n) o hon hdep
  obtain ⟨g, hg, hng⟩ := hread
  obtain ⟨pre, post, rfl⟩ := List.append_of_mem hg
  have hgn : NOk g := hnok g hg
  have hpren : ∀ g' ∈ pre, NOk g' := fun g' h => hnok g' (List.mem_append_left _ h)
  have hpostn : ∀ g' ∈ post, NOk g' :=
    fun g' h => hnok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have hsplit : ∀ b, elim n (pre ++ g :: post) (initStats n b, [])
      = elim n post (elimStep n (elim n pre (initStats n b, [])) g) :=
    fun b => by rw [elim_append, elim_cons]
  have hAn : ∀ b, (elim n pre (initStats n b, [])).1.getD n (Stat.const false) = Stat.const b := by
    intro b
    rw [elim_getD n n _ pre _ (by simp [initStats])]
    exact initStats_last n b
  have hAl : ∀ b, (elim n pre (initStats n b, [])).1.length = n + 1 + pre.length := by
    intro b
    rw [elim_fst_len]
    simp [initStats]
  have hA2 : ∀ b, (elim n pre (initStats n b, [])).2.length ≤ 0 + pre.length :=
    fun b => elim_len n pre (initStats n b, [])
  have hB2 := fun b => elimStep_none n (elim n pre (initStats n b, [])) g hgn n hng b (hAn b)
  have hBl : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.length
      = n + 1 + pre.length + 1 := by
    intro b
    simp [elimStep, hAl b]
  have hBn : ∀ b, (elimStep n (elim n pre (initStats n b, [])) g).1.getD n (Stat.const false)
      = Stat.const b := by
    intro b
    show ((elim n pre (initStats n b, [])).1 ++ [_]).getD n _ = _
    rw [getD_snoc_ne _ _ _ _ (by rw [hAl b]; omega)]
    exact hAn b
  have hF := fun b => elim_len n post (elimStep n (elim n pre (initStats n b, [])) g)
  have hlen : (pre ++ g :: post).length = pre.length + post.length + 1 := by
    simp only [List.length_append, List.length_cons]; omega
  by_cases h1 : ∃ g' ∈ pre, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 : (elim n pre (initStats n false, [])).2.length + 1 ≤ 0 + pre.length :=
      elim_len_lt n n pre (initStats n false, []) hpren (by simp [initStats])
        ⟨false, initStats_last n false⟩ h1
    have := hF false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  by_cases h2 : ∃ g' ∈ post, n ∈ g'.inputs
  · refine ⟨false, ?_⟩
    have a1 := elim_len_lt n n post (elimStep n (elim n pre (initStats n false, [])) g) hpostn
      (by rw [hBl]; omega) ⟨false, hBn false⟩ h2
    have := hA2 false
    have := hB2 false
    rw [hsplit, hlen]
    omega
  obtain ⟨c, hc⟩ := elimStep_const n (elim n pre (initStats n (fixBit g), [])) g hgn n hng
    (hAn (fixBit g))
  rw [hAl (fixBit g)] at hc
  refine ⟨fixBit g, ?_⟩
  by_cases h3 : ∃ g' ∈ post, (n + 1 + pre.length) ∈ g'.inputs
  · have a1 := elim_len_lt n (n + 1 + pre.length) post
      (elimStep n (elim n pre (initStats n (fixBit g), [])) g) hpostn
      (by rw [hBl]; omega) ⟨c, hc⟩ h3
    have := hA2 (fixBit g)
    have := hB2 (fixBit g)
    rw [hsplit, hlen]
    omega
  · exfalso
    have hom : o ≠ n + 1 + pre.length := by
      intro e
      apply hout (fixBit g) c
      rw [hsplit, e, elim_getD n _ _ post _ (by rw [hBl]; omega)]
      exact hc
    push Not at h1 h2 h3
    have hs : suppsFrom (pre ++ g :: post) (inputSupps (n + 1))
        = suppsFrom post (suppsFrom pre (inputSupps (n + 1))
          ++ [gateSupp (suppsFrom pre (inputSupps (n + 1))) g]) := by
      rw [suppsFrom_append]; rfl
    rw [hs] at hdep
    have hL := supp_noread n pre (inputSupps (n + 1)) h1 (inputSupps_noread n)
    have hLl : (suppsFrom pre (inputSupps (n + 1))).length = n + 1 + pre.length := by
      rw [length_suppsFrom]
      simp [inputSupps]
    refine supp_noreadD n (fun j => j = n ∨ j = n + 1 + pre.length) post _ ?_ ?_ o
      (by simp [hon, hom]) hdep
    · intro g' hg' a ha hD
      rcases hD with rfl | rfl
      · exact h2 g' hg' ha
      · exact h3 g' hg' ha
    · intro j hj
      have hj' : j ≠ n ∧ j ≠ n + 1 + pre.length := by
        constructor
        · exact fun e => hj (Or.inl e)
        · exact fun e => hj (Or.inr e)
      rw [getD_snoc_ne _ _ _ _ (by rw [hLl]; exact hj'.2)]
      exact hL j hj'.1
lemma gate_elim_two (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x (Fin.last n) (!x (Fin.last n))) ≠ f x)
    (hnc : ∀ b : Bool, ∃ y y' : Fin n → Bool, f (Fin.snoc y b) ≠ f (Fin.snoc y' b))
    (h : PEqualNP.MetaComplexity.HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      PEqualNP.MetaComplexity.HasCircuitSize n (fun y : Fin n → Bool => f (Fin.snoc y b)) s' := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  set gs := C.gates.map normGate with hgs
  have hl : gs.length = C.gates.length := by simp [hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (ok g0 hg0)
  have hevg : ∀ x : Fin (n + 1) → Bool, (wiresFrom gs (List.ofFn x)).getD C.output false = f x := by
    intro x
    rw [hgs, wiresFrom_norm, ← hev x]; rfl
  have hinv : ∀ (b : Bool) (y : Fin n → Bool),
      Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (Fin.snoc y b : Fin (n + 1) → Bool)))
        (elim n gs (initStats n b, [])) := by
    intro b y
    rw [ofFn_snoc]
    exact inv_elim n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (inv_init n b y)
  have hval : ∀ (b : Bool) (y : Fin n → Bool),
      ((elim n gs (initStats n b, [])).1.getD C.output (Stat.const false)).val
        (wiresFrom (elim n gs (initStats n b, [])).2 (List.ofFn y)) = f (Fin.snoc y b) := by
    intro b y
    rw [((hinv b y).2 C.output).2, hevg]
  have hout : ∀ b c,
      (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) ≠ Stat.const c := by
    intro b c hst
    obtain ⟨y, y', hne⟩ := hnc b
    apply hne
    rw [← hval b y, ← hval b y', hst]; rfl
  have hsupp : Fin.last n ∈ (suppsFrom gs (inputSupps (n + 1))).getD C.output ∅ := by
    by_contra hns
    obtain ⟨x, hx⟩ := hdep
    apply hx
    have hag := (agree_wiresFrom (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
      (agree_inputs _ _)).2.2 C.output (by
        intro k hk
        have : k ≠ Fin.last n := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
    rw [← hevg, ← hevg]
    exact hag
  obtain ⟨b, hb⟩ := two_saved n gs hnok C.output hsupp hout
  cases hst : (elim n gs (initStats n b, [])).1.getD C.output (Stat.const false) with
  | const c => exact absurd hst (hout b c)
  | wire j =>
    refine ⟨b, (elim n gs (initStats n b, [])).2.length, by omega,
      ⟨(elim n gs (initStats n b, [])).2, j⟩, elim_ok n gs _ (by simp), le_refl _, ?_⟩
    intro y
    have := hval b y
    rw [hst] at this
    exact this
def par (n : ℕ) (x : Fin n → Bool) : Bool :=
  decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)
lemma par_snoc (n : ℕ) (y : Fin n → Bool) (b : Bool) :
    par (n + 1) (Fin.snoc y b) = xor (par n y) b := by
  unfold par
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_castSucc]
  simp only [Fin.snoc_castSucc, Fin.snoc_last]
  generalize (∑ i : Fin n, if y i = true then 1 else 0) = S
  have h := Nat.mod_two_eq_zero_or_one S
  cases b <;> rcases h with h | h <;> simp [Nat.add_mod, h]
lemma par_lower : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s →
      2 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    have hdep : ∃ x : Fin (n + 1 + 1) → Bool,
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c)
          (Function.update x (Fin.last (n + 1)) (!x (Fin.last (n + 1))))
        ≠ (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) x := by
      refine ⟨Fin.snoc (fun _ => false) false, ?_⟩
      simp only [Fin.snoc_last, Fin.update_snoc_last, par_snoc]
      simp
    have hnc : ∀ b : Bool, ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y b)
        ≠ (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y' b) := by
      intro b
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    obtain ⟨b, s', hs, h'⟩ := gate_elim_two (n + 1) _ s hdep hnc h
    have e : (fun y : Fin (n + 1) → Bool =>
          (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) (Fin.snoc y b))
        = fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) (xor b c) := by
      funext y
      show xor (par (n + 1 + 1) (Fin.snoc y b)) c = _
      rw [par_snoc]
      cases par (n + 1) y <;> cases b <;> cases c <;> rfl
    rw [e] at h'
    have := ih _ _ h'
    omega
lemma parity_lower : ∀ (n s : ℕ),
    PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    2 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : PEqualNP.MetaComplexity.HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have := par_lower n false s h'
    omega
end PEqualNP.Outside.L_meta_3457.SparseLower.Helpers

namespace PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
open PEqualNP.CircuitLowerBounds
def CleanGate (m : ℕ) (g : Gate) : Prop :=
  (g.op = GateOp.not ∧ ∃ j, j < m ∧ g.inputs = [j]) ∨
  ((g.op = GateOp.and ∨ g.op = GateOp.or) ∧ ∃ j k, j < m ∧ k < m ∧ g.inputs = [j, k])
def CleanL (m : ℕ) (gs : List Gate) : Prop :=
  ∀ (p : ℕ) (g : Gate), gs[p]? = some g → CleanGate (m + p) g
lemma CleanGate.nok {m : ℕ} {g : Gate} (h : CleanGate m g) : NOk g := by
  rcases h with ⟨h1, j, _, h2⟩ | ⟨h1 | h1, j, k, _, _, h2⟩
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inr rfl)
    · rw [h2]; simp
    · intro _; rw [h2]; simp
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inl rfl
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
  · refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [h1]; exact Or.inr (Or.inl rfl)
    · rw [h2]; simp
    · intro h; rw [h1] at h; cases h
lemma CleanGate.lt {m : ℕ} {g : Gate} (h : CleanGate m g) : ∀ a ∈ g.inputs, a < m := by
  intro a ha
  rcases h with ⟨_, j, hj, h2⟩ | ⟨_, j, k, hj, hk, h2⟩
  · rw [h2] at ha
    simp at ha
    subst ha; exact hj
  · rw [h2] at ha
    simp at ha
    rcases ha with rfl | rfl
    · exact hj
    · exact hk
lemma clean_nok (m : ℕ) (gs : List Gate) (h : CleanL m gs) : ∀ g ∈ gs, NOk g := by
  intro g hg
  obtain ⟨p, hp⟩ := List.mem_iff_getElem?.1 hg
  exact (h p g hp).nok
lemma simplify_clean (op : GateOp) (m : ℕ) (ins : List Stat) (hv : ∀ s ∈ ins, s.Valid m) :
    ∀ g ∈ (simplify op m ins).1, CleanGate m g := by
  intro g hg
  cases op <;> simp only [simplify] at hg
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpAnd] at hg
    subst hg
    refine Or.inr ⟨Or.inl rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
      simp [simpOr] at hg
    subst hg
    refine Or.inr ⟨Or.inr rfl, _, _, ?_, ?_, rfl⟩
    · exact hv _ List.mem_cons_self
    · exact hv _ (List.mem_cons_of_mem _ List.mem_cons_self)
  · rcases ins with _ | ⟨a, l⟩ <;> (try cases a) <;> simp [simpNot] at hg
    subst hg
    refine Or.inl ⟨rfl, _, ?_, rfl⟩
    exact hv _ List.mem_cons_self
  · simp at hg
  · simp at hg
lemma toList_getElem? {α : Type} (o : Option α) (k : ℕ) (a : α)
    (h : o.toList[k]? = some a) : k = 0 ∧ a ∈ o := by
  cases o with
  | none => simp at h
  | some b =>
    cases k with
    | zero => simp at h; simp [h]
    | succ k => simp at h
lemma clean_elim (n : ℕ) (y : List Bool) (hy : y.length = n) (gs : List Gate) :
    ∀ (w : List Bool) (acc : List Stat × List Gate), (∀ g ∈ gs, Ok g) → Inv n y w acc →
      CleanL n acc.2 → CleanL n (elim n gs acc).2 := by
  induction gs with
  | nil => intro w acc _ _ h; exact h
  | cons g gs ih =>
    intro w acc hok hinv hcl
    have hinv' : Inv n y (wiresFrom [g] w) (elimStep n acc g) :=
      inv_elim n y hy [g] w acc (fun g' hg' => hok g' (by simp at hg'; simp [hg'])) hinv
    refine ih _ (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg')) hinv' ?_
    intro p g' hp
    have hp' : (acc.2 ++ (simplify g.op (n + acc.2.length)
        (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList)[p]? = some g' := hp
    by_cases hlt : p < acc.2.length
    · rw [List.getElem?_append_left hlt] at hp'
      exact hcl p g' hp'
    · rw [List.getElem?_append_right (by omega)] at hp'
      obtain ⟨h0, hmem⟩ := toList_getElem? _ _ _ hp'
      have hpl : p = acc.2.length := by omega
      rw [hpl]
      exact simplify_clean _ _ _ (fun s hs => by
        obtain ⟨a, _, rfl⟩ := List.mem_map.1 hs
        exact (hinv.2 a).1) g' hmem
def HasClean (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ (gs : List Gate) (o : ℕ), CleanL n gs ∧ gs.length ≤ s ∧
    ∀ x : Fin n → Bool, (wiresFrom gs (List.ofFn x)).getD o false = f x
def idStats (n : ℕ) : List Stat := List.ofFn (fun i : Fin n => Stat.wire i)
lemma inv_id (n : ℕ) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn y) (idStats n, []) := by
  refine ⟨by simp [idStats], ?_⟩
  intro i
  by_cases hlt : i < n
  · simp [idStats, hlt, Stat.Valid, Stat.val, wiresFrom]
  · rw [List.getD_eq_default _ _ (by simp [idStats]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩
lemma clean_of (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ)
    (hnc : ∃ y y' : Fin n → Bool, f y ≠ f y') (h : PEqualNP.MetaComplexity.HasCircuitSize n f s) : HasClean n f s := by
  obtain ⟨C, ok, hsz, hev⟩ := h
  have hsz' : C.gates.length ≤ s := hsz
  have hok : ∀ g ∈ C.gates, Ok g := ok
  set acc := elim n C.gates (idStats n, []) with hacc
  have hinv : ∀ y : Fin n → Bool,
      Inv n (List.ofFn y) (wiresFrom C.gates (List.ofFn y)) acc :=
    fun y => inv_elim n _ (by simp) C.gates _ _ hok (inv_id n y)
  have hval : ∀ y : Fin n → Bool,
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn y)) = f y := by
    intro y
    rw [((hinv y).2 C.output).2, ← hev y]; rfl
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]; rfl
  | wire j =>
    refine ⟨acc.2, j, ?_, ?_, ?_⟩
    · exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) C.gates _ _ hok
        (inv_id n _) (by intro p g hp; simp at hp)
    · have := elim_len n C.gates (idStats n, [])
      rw [← hacc] at this
      simp only [List.length_nil, zero_add] at this
      omega
    · intro y
      have := hval y
      rw [hst] at this
      exact this
lemma getD_ofFn {α : Type} (m : ℕ) (F : Fin m → α) (d : α) (j : Fin m) :
    (List.ofFn F).getD j d = F j := by
  simp
def statAt (n : ℕ) (i : Fin (n + 1)) (b : Bool) : List Stat :=
  List.ofFn (Fin.insertNth i (Stat.const b) (fun k : Fin n => Stat.wire k) : Fin (n + 1) → Stat)
lemma statAt_length (n : ℕ) (i : Fin (n + 1)) (b : Bool) : (statAt n i b).length = n + 1 := by
  simp [statAt]
lemma statAt_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) :
    (statAt n i b).getD i (Stat.const false) = Stat.const b := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_same]
lemma statAt_above (n : ℕ) (i : Fin (n + 1)) (b : Bool) (k : Fin n) :
    (statAt n i b).getD (i.succAbove k) (Stat.const false) = Stat.wire k := by
  rw [statAt, getD_ofFn, Fin.insertNth_apply_succAbove]
lemma inv_at (n : ℕ) (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) :
    Inv n (List.ofFn y) (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool))
      (statAt n i b, []) := by
  refine ⟨by simp [statAt], ?_⟩
  have key : ∀ j : Fin (n + 1),
      ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove i j with rfl | ⟨k, rfl⟩
    · rw [statAt_at, getD_ofFn, Fin.insertNth_apply_same]
      exact ⟨trivial, rfl⟩
    · rw [statAt_above, getD_ofFn, Fin.insertNth_apply_succAbove]
      refine ⟨?_, ?_⟩
      · show (k : ℕ) < n + 0
        have := k.isLt
        omega
      · show (List.ofFn y).getD k false = y k
        exact getD_ofFn n y false k
  intro j
  by_cases hlt : j < n + 1
  · exact key ⟨j, hlt⟩
  · show ((statAt n i b).getD j (Stat.const false)).Valid (n + 0) ∧
      ((statAt n i b).getD j (Stat.const false)).val (List.ofFn y)
        = (List.ofFn (Fin.insertNth i b y : Fin (n + 1) → Bool)).getD j false
    rw [List.getD_eq_default _ _ (by rw [statAt_length]; omega),
      List.getD_eq_default _ _ (by simp; omega)]
    exact ⟨trivial, rfl⟩
def stF (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Stat :=
  (elim n gs (statAt n i b, [])).1.getD a (Stat.const false)
lemma stF_self (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b i = Stat.const b := by
  show (elim n gs (statAt n i b, [])).1.getD i (Stat.const false) = _
  rw [elim_getD n i _ gs _ (by
    show (i : ℕ) < (statAt n i b).length
    rw [statAt_length]; exact i.isLt)]
  exact statAt_at n i b
lemma split_at {α : Type} : ∀ (l : List α) (p : ℕ) (g : α), l[p]? = some g →
    ∃ pre post, l = pre ++ g :: post ∧ pre.length = p := by
  intro l
  induction l with
  | nil => intro p g h; simp at h
  | cons x l ih =>
    intro p g h
    cases p with
    | zero =>
      simp at h
      subst h
      exact ⟨[], l, rfl, rfl⟩
    | succ p =>
      simp at h
      obtain ⟨pre, post, rfl, rfl⟩ := ih p g h
      exact ⟨x :: pre, post, rfl, rfl⟩
lemma elim_split_getD (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a ≤ acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elimStep n (elim n pre acc) g).1.getD a d := by
  rw [elim_append, elim_cons, elim_getD n a d post _ (by
    show a < ((elim n pre acc).1 ++ [_]).length
    rw [List.length_append, elim_fst_len, List.length_singleton]; omega)]
lemma elim_split_getD_lt (n : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (acc : List Stat × List Gate) (a : ℕ) (d : Stat) (h : a < acc.1.length + pre.length) :
    (elim n (pre ++ g :: post) acc).1.getD a d = (elim n pre acc).1.getD a d := by
  rw [elim_split_getD n pre g post acc a d (le_of_lt h)]
  show ((elim n pre acc).1 ++ [_]).getD a d = _
  exact getD_snoc_ne _ _ _ _ (by rw [elim_fst_len]; omega)
lemma const_of_read (n : ℕ) (gs : List Gate) (acc : List Stat × List Gate) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hg : NOk g) (a : ℕ) (ha : a ∈ g.inputs)
    (hlt : a < acc.1.length + p)
    (hc : (elim n gs acc).1.getD a (Stat.const false) = Stat.const (fixBit g)) :
    ∃ c, (elim n gs acc).1.getD (acc.1.length + p) (Stat.const false) = Stat.const c := by
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  rw [elim_split_getD_lt n pre g post acc a _ hlt] at hc
  obtain ⟨c, hc'⟩ := elimStep_const n (elim n pre acc) g hg a ha hc
  refine ⟨c, ?_⟩
  rw [elim_split_getD n pre g post acc _ _ (le_refl _)]
  rw [elim_fst_len] at hc'
  exact hc'
lemma elim_count (n : ℕ) (acc : List Stat × List Gate) : ∀ gs : List Gate,
    (∀ g ∈ gs, NOk g) → ∀ S : Finset ℕ,
    (∀ p ∈ S, ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, a < acc.1.length + p ∧
        ∃ c, (elim n gs acc).1.getD a (Stat.const false) = Stat.const c) →
      (elim n gs acc).2.length + S.card ≤ acc.2.length + gs.length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro p hp
      obtain ⟨g, hg, _⟩ := hS p hp
      simp at hg
    subst hE
    simp [elim]
  | append_singleton gs g ih =>
    intro hok S hS
    have hstep : elim n (gs ++ [g]) acc = elimStep n (elim n gs acc) g := by
      rw [elim_append]; rfl
    have hpre : ∀ (a : ℕ) (d : Stat), a < acc.1.length + gs.length →
        (elim n (gs ++ [g]) acc).1.getD a d = (elim n gs acc).1.getD a d :=
      fun a d h => elim_split_getD_lt n gs g [] acc a d h
    have hok' : ∀ g' ∈ gs, NOk g' := fun g' h => hok g' (List.mem_append_left _ h)
    have ih' := ih hok' (S.erase gs.length) (by
      intro p hp
      obtain ⟨hne, hpS⟩ := Finset.mem_erase.1 hp
      obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS p hpS
      have hpl : p < gs.length := by
        obtain ⟨h1, _⟩ := List.getElem?_eq_some_iff.1 hg'
        rw [List.length_append, List.length_singleton] at h1
        omega
      rw [List.getElem?_append_left hpl] at hg'
      rw [hpre a _ (by omega)] at hc
      exact ⟨g', hg', a, ha, hlt, c, hc⟩)
    rw [hstep, List.length_append, List.length_singleton]
    by_cases hin : gs.length ∈ S
    · obtain ⟨g', hg', a, ha, hlt, c, hc⟩ := hS _ hin
      have hgg : g' = g := by
        rw [List.getElem?_concat_length] at hg'
        exact (Option.some.inj hg').symm
      subst hgg
      rw [hpre a _ hlt] at hc
      have h2 := elimStep_none n (elim n gs acc) g' (hok g' (by simp)) a ha c hc
      have hcard := Finset.card_erase_of_mem hin
      have hpos : 1 ≤ S.card := Finset.card_pos.2 ⟨_, hin⟩
      omega
    · have h2 : (elimStep n (elim n gs acc) g).2.length ≤ (elim n gs acc).2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + (elim n gs acc).2.length)
          (g.inputs.map fun i => (elim n gs acc).1.getD i (Stat.const false))).1
        omega
      rw [Finset.erase_eq_of_notMem hin] at ih'
      omega
lemma supp_B (m : ℕ) (i : Fin m) (B : ℕ → Prop) (hi : B i) : ∀ gs : List Gate,
    (∀ p g, gs[p]? = some g → ¬ B (m + p) → ∀ a ∈ g.inputs, ¬ B a) →
    ∀ j, ¬ B j → i ∉ (suppsFrom gs (inputSupps m)).getD j ∅ := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro _ j hj
    show i ∉ (inputSupps m).getD j ∅
    by_cases hlt : j < m
    · rw [inputSupps_getD m j hlt, Finset.mem_singleton]
      intro e
      apply hj
      have e' : (i : ℕ) = j := congrArg Fin.val e
      rw [← e']; exact hi
    · rw [List.getD_eq_default _ _ (by simp [inputSupps]; omega)]; simp
  | append_singleton gs g ih =>
    intro h j hj
    have ih' := ih (fun p g' hp => h p g' (by
      obtain ⟨hpl, _⟩ := List.getElem?_eq_some_iff.1 hp
      rw [List.getElem?_append_left hpl]; exact hp))
    have hs : suppsFrom (gs ++ [g]) (inputSupps m) = suppsFrom gs (inputSupps m)
        ++ [gateSupp (suppsFrom gs (inputSupps m)) g] := by
      rw [suppsFrom_append]; rfl
    have hl : (suppsFrom gs (inputSupps m)).length = m + gs.length := by
      rw [length_suppsFrom]; simp [inputSupps]
    rw [hs]
    by_cases hjl : j = m + gs.length
    · subst hjl
      rw [getD_snoc_len _ _ _ _ hl]
      intro hmem
      obtain ⟨a, ha, hia⟩ := (mem_gateSupp _ g _).1 hmem
      exact ih' a (h gs.length g List.getElem?_concat_length hj a ha) hia
    · rw [getD_snoc_ne _ _ _ _ (by rw [hl]; exact hjl)]
      exact ih' j hj
lemma exists_reader (m : ℕ) (i : Fin m) (B : ℕ → Prop) (hi : B i) (gs : List Gate) (o : ℕ)
    (ho : ¬ B o) (hdep : i ∈ (suppsFrom gs (inputSupps m)).getD o ∅) :
    ∃ p g, gs[p]? = some g ∧ ¬ B (m + p) ∧ ∃ a ∈ g.inputs, B a := by
  by_contra hno
  exact supp_B m i B hi gs
    (fun p g hp hB a ha hBa => hno ⟨p, g, hp, hB, a, ha, hBa⟩) o ho hdep
lemma agree_except (k : ℕ) (gs : List Gate) : ∀ w w' : List Bool,
    (∀ g ∈ gs, k ∉ g.inputs) → w.length = w'.length →
    (∀ j, j ≠ k → w.getD j false = w'.getD j false) →
    ∀ j, j ≠ k → (wiresFrom gs w).getD j false = (wiresFrom gs w').getD j false := by
  induction gs with
  | nil => intro w w' _ _ h; exact h
  | cons g gs ih =>
    intro w w' hno hl h
    have hno' := hno g List.mem_cons_self
    have e : (g.inputs.map fun i => w.getD i false) = g.inputs.map fun i => w'.getD i false :=
      List.map_congr_left (fun a ha => h a (fun e => hno' (e ▸ ha)))
    apply ih (w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
      (w' ++ [g.op.eval (g.inputs.map fun i => w'.getD i false)])
      (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg')) (by simp [hl])
    intro j hj
    by_cases hjl : j = w.length
    · rw [hjl, getD_snoc_eq, hl, getD_snoc_eq, e]
    · rw [getD_snoc_ne _ _ _ _ hjl, getD_snoc_ne _ _ _ _ (by omega)]
      exact h j hj
def RC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (p : ℕ) : Prop :=
  ∃ g, gs[p]? = some g ∧ ∃ a ∈ g.inputs, ∃ c, stF n gs i b a = Stat.const c
lemma three_count (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) {p1, p2, p3} (by
    intro p hp
    have hR : RC n gs i b p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl <;> assumption
    obtain ⟨g, hg, a, ha, c, hc⟩ := hR
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  have hcard : ({p1, p2, p3} : Finset ℕ).card = 3 :=
    Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩
  rw [hcard] at hcount
  simpa using hcount
lemma three_core (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (o : ℕ)
    (hsupp : ∀ i : Fin (n + 1), i ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅)
    (hout : ∀ (i : Fin (n + 1)) (b c : Bool), stF n gs i b o ≠ Stat.const c)
    (g0 : Gate) (h0 : gs[0]? = some g0) (i : Fin (n + 1)) (hi0 : (i : ℕ) ∈ g0.inputs)
    (halt : (∀ c, ∃ b, stF n gs i b (n + 1) = Stat.const c) ∨
      ∃ p' g', p' ≠ 0 ∧ gs[p']? = some g' ∧ (i : ℕ) ∈ g'.inputs) :
    ∃ b, (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hnok := clean_nok _ gs hcl
  have hxi : ∀ b, stF n gs i b i = Stat.const b := stF_self n gs i
  have hrd : ∀ (b : Bool) (p : ℕ) (g : Gate) (a : ℕ), gs[p]? = some g → a ∈ g.inputs →
      stF n gs i b a = Stat.const (fixBit g) → ∃ c, stF n gs i b (n + 1 + p) = Stat.const c := by
    intro b p g a hp ha hc
    have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
    have := const_of_read n gs (statAt n i b, []) p g hp (hnok g (List.mem_of_getElem? hp)) a ha
      (by rw [hL]; exact (hcl p g hp).lt a ha) hc
    rw [hL] at this
    exact this
  have hg0c : ∃ c0, stF n gs i (fixBit g0) (n + 1) = Stat.const c0 :=
    hrd (fixBit g0) 0 g0 i h0 hi0 (hxi _)
  have hox : o ≠ i := fun e => hout i false false (by rw [e]; exact hxi false)
  have ho0 : o ≠ n + 1 := by
    intro e
    obtain ⟨c0, h⟩ := hg0c
    exact hout i (fixBit g0) c0 (by rw [e]; exact h)
  have R0 : ∀ b, RC n gs i b 0 := fun b => ⟨g0, h0, i, hi0, b, hxi b⟩
  obtain ⟨p, g2, hp, hBp, a, ha, hBa⟩ := exists_reader (n + 1) i
    (fun a => a = i ∨ a = n + 1) (Or.inl rfl) gs o
    (fun h => h.elim hox ho0) (hsupp i)
  have hp0 : p ≠ 0 := fun e => hBp (Or.inr (by omega))
  have ha2 : ∃ c, stF n gs i (fixBit g0) a = Stat.const c := by
    rcases hBa with h | h
    · exact ⟨fixBit g0, by rw [h]; exact hxi _⟩
    · rw [h]; exact hg0c
  have third : ∀ (b c2 : Bool), stF n gs i b (n + 1 + p) = Stat.const c2 →
      ∃ p3 g3, gs[p3]? = some g3 ∧ p3 ≠ 0 ∧ p3 ≠ p ∧
        ∃ a3 ∈ g3.inputs, a3 = (i : ℕ) ∨ a3 = n + 1 ∨ a3 = n + 1 + p := by
    intro b c2 hc2
    obtain ⟨p3, g3, hp3, hB3, a3, ha3, hBa3⟩ := exists_reader (n + 1) i
      (fun a => a = i ∨ a = n + 1 ∨ a = n + 1 + p) (Or.inl rfl) gs o
      (fun h => by
        rcases h with h | h | h
        · exact hox h
        · exact ho0 h
        · exact hout i b c2 (by rw [h]; exact hc2)) (hsupp i)
    exact ⟨p3, g3, hp3, fun e => hB3 (Or.inr (Or.inl (by omega))),
      fun e => hB3 (Or.inr (Or.inr (by omega))), a3, ha3, hBa3⟩
  by_cases hc2 : ∃ c, stF n gs i (fixBit g0) (n + 1 + p) = Stat.const c
  · obtain ⟨c2, hc2⟩ := hc2
    obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third (fixBit g0) c2 hc2
    refine ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
      (Ne.symm h3p) (R0 _) ⟨g2, hp, a, ha, ha2⟩ ⟨g3, hp3, a3, ha3, ?_⟩⟩
    rcases hBa3 with h | h | h
    · exact ⟨fixBit g0, by rw [h]; exact hxi _⟩
    · rw [h]; exact hg0c
    · exact ⟨c2, by rw [h]; exact hc2⟩
  · by_cases hx : (i : ℕ) ∈ g2.inputs
    · obtain ⟨c2, hc2'⟩ := hrd (fixBit g2) p g2 i hp hx (hxi _)
      obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third (fixBit g2) c2 hc2'
      rcases hBa3 with h | h | h
      · exact ⟨fixBit g2, three_count n gs hcl i (fixBit g2) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, i, hx, _, hxi _⟩
          ⟨g3, hp3, a3, ha3, fixBit g2, by rw [h]; exact hxi _⟩⟩
      · exact ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, a, ha, ha2⟩
          ⟨g3, hp3, a3, ha3, by rw [h]; exact hg0c⟩⟩
      · exact ⟨fixBit g2, three_count n gs hcl i (fixBit g2) 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, i, hx, _, hxi _⟩
          ⟨g3, hp3, a3, ha3, c2, by rw [h]; exact hc2'⟩⟩
    · have ha' : a = n + 1 := by
        rcases hBa with h | h
        · exact absurd (h ▸ ha) hx
        · exact h
      rw [ha'] at ha
      rcases halt with hG | ⟨p', g', hp'0, hp', hx'⟩
      · obtain ⟨b, hb⟩ := hG (fixBit g2)
        obtain ⟨c2, hc2'⟩ := hrd b p g2 (n + 1) hp ha hb
        obtain ⟨p3, g3, hp3, h30, h3p, a3, ha3, hBa3⟩ := third b c2 hc2'
        refine ⟨b, three_count n gs hcl i b 0 p p3 (Ne.symm hp0) (Ne.symm h30)
          (Ne.symm h3p) (R0 _) ⟨g2, hp, n + 1, ha, _, hb⟩ ⟨g3, hp3, a3, ha3, ?_⟩⟩
        rcases hBa3 with h | h | h
        · exact ⟨b, by rw [h]; exact hxi _⟩
        · exact ⟨fixBit g2, by rw [h]; exact hb⟩
        · exact ⟨c2, by rw [h]; exact hc2'⟩
      · have hpp : p ≠ p' := by
          intro e
          rw [← e, hp] at hp'
          exact hx (Option.some.inj hp' ▸ hx')
        exact ⟨fixBit g0, three_count n gs hcl i (fixBit g0) 0 p p' (Ne.symm hp0)
          (Ne.symm hp'0) hpp (R0 _) ⟨g2, hp, n + 1, ha, hg0c⟩
          ⟨g', hp', i, hx', _, hxi _⟩⟩
lemma stat_first (n : ℕ) (gs : List Gate) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i : Fin (n + 1)) (b : Bool) :
    stF n gs i b (n + 1) = (simplify g0.op n
      (g0.inputs.map fun a => (statAt n i b).getD a (Stat.const false))).2 := by
  obtain ⟨pre, post, rfl, hpre⟩ := split_at gs 0 g0 h0
  have hnil : pre = [] := List.eq_nil_of_length_eq_zero hpre
  subst hnil
  show (elim n ([] ++ g0 :: post) (statAt n i b, [])).1.getD (n + 1) (Stat.const false) = _
  rw [elim_split_getD n [] g0 post _ (n + 1) _ (by
    show n + 1 ≤ (statAt n i b).length + 0
    rw [statAt_length])]
  exact getD_snoc_len (statAt n i b) _ _ _ (statAt_length n i b)
lemma first_any (n : ℕ) (gs : List Gate) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i : Fin (n + 1))
    (hshape : (g0.op = GateOp.not ∧ g0.inputs = [(i : ℕ)]) ∨
      ((g0.op = GateOp.and ∨ g0.op = GateOp.or) ∧ g0.inputs = [(i : ℕ), (i : ℕ)])) :
    ∀ c, ∃ b, stF n gs i b (n + 1) = Stat.const c := by
  intro c
  rcases hshape with ⟨hop, hin⟩ | ⟨hop | hop, hin⟩
  · refine ⟨!c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpNot]
  · refine ⟨c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpAnd]
  · refine ⟨c, ?_⟩
    rw [stat_first n gs g0 h0, hop, hin]
    simp only [List.map_cons, List.map_nil, statAt_at]
    simp [simplify, simpOr]
lemma single_reader (n : ℕ) (gs : List Gate) (o : ℕ) (g0 : Gate) (h0 : gs[0]? = some g0)
    (i k : Fin (n + 1)) (hik : k ≠ i) (hop : g0.op = GateOp.and ∨ g0.op = GateOp.or)
    (hin : g0.inputs = [(i : ℕ), (k : ℕ)]) (hoi : o ≠ i)
    (hno : ∀ p' g', gs[p']? = some g' → p' ≠ 0 → (i : ℕ) ∉ g'.inputs)
    (hdep : ∀ u : Fin (n + 1) → Bool,
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false) : False := by
  obtain ⟨pre, post, rfl, hpre⟩ := split_at gs 0 g0 h0
  have hnil : pre = [] := List.eq_nil_of_length_eq_zero hpre
  subst hnil
  have hno' : ∀ g ∈ post, (i : ℕ) ∉ g.inputs := by
    intro g hg
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno (q + 1) g (by simpa using hq) (by omega)
  let u : Fin (n + 1) → Bool := fun j => if j = k then fixBit g0 else false
  have huk : u k = fixBit g0 := by simp [u]
  have hu'k : Function.update u i (!u i) k = fixBit g0 := by
    rw [Function.update_of_ne hik]; exact huk
  apply hdep u
  show (wiresFrom post (List.ofFn (Function.update u i (!u i)) ++
      [g0.op.eval (g0.inputs.map fun a => (List.ofFn (Function.update u i (!u i))).getD a false)])).getD
        o false
    = (wiresFrom post (List.ofFn u ++
      [g0.op.eval (g0.inputs.map fun a => (List.ofFn u).getD a false)])).getD o false
  apply agree_except i post _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjl : j = n + 1
  · rw [hjl, getD_snoc_len _ _ _ _ (by simp), getD_snoc_len _ _ _ _ (by simp), hin]
    simp only [List.map_cons, List.map_nil, getD_ofFn, huk, hu'k]
    rcases hop with hop | hop
    · have hf : fixBit g0 = false := by simp [fixBit, hop]
      rw [hop, hf]; simp [GateOp.eval]
    · have hf : fixBit g0 = true := by simp [fixBit, hop]
      rw [hop, hf]; simp [GateOp.eval]
  · rw [getD_snoc_ne _ _ _ _ (by simpa using hjl), getD_snoc_ne _ _ _ _ (by simpa using hjl)]
    by_cases hlt : j < n + 1
    · have e1 : (List.ofFn (Function.update u i (!u i))).getD j false
          = Function.update u i (!u i) ⟨j, hlt⟩ := getD_ofFn (n + 1) _ false ⟨j, hlt⟩
      have e2 : (List.ofFn u).getD j false = u ⟨j, hlt⟩ := getD_ofFn (n + 1) _ false ⟨j, hlt⟩
      rw [e1, e2]
      exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
    · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
lemma three_saved (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (o : ℕ)
    (hdep : ∀ (i : Fin (n + 1)) (u : Fin (n + 1) → Bool),
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false)
    (hout : ∀ (i : Fin (n + 1)) (b c : Bool), stF n gs i b o ≠ Stat.const c) :
    ∃ (i : Fin (n + 1)) (b : Bool),
      (elim n gs (statAt n i b, [])).2.length + 3 ≤ gs.length := by
  have hsupp : ∀ i : Fin (n + 1), i ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅ := by
    intro i
    by_contra hns
    refine hdep i (fun _ => false) ?_
    exact (agree_wiresFrom (Function.update (fun _ => false) i (!false)) (fun _ => false) gs _ _ _
      (agree_inputs _ _)).2.2 o (by
        intro k hk
        have : k ≠ i := fun e => hns (e ▸ hk)
        simp [Function.update_of_ne this])
  have hoi : ∀ i : Fin (n + 1), o ≠ i :=
    fun i e => hout i false false (by rw [e]; exact stF_self n gs i false)
  have hg0 : ∃ g0, gs[0]? = some g0 := by
    cases gs with
    | nil =>
      exfalso
      obtain ⟨p, g, hp, _⟩ := exists_reader (n + 1) 0 (fun a => a = ((0 : Fin (n + 1)) : ℕ)) rfl
        [] o (hoi 0) (hsupp 0)
      simp at hp
    | cons g _ => exact ⟨g, rfl⟩
  obtain ⟨g0, h0⟩ := hg0
  rcases hcl 0 g0 h0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
      (by rw [hin]; exact List.mem_cons_self)
      (Or.inl (first_any n gs g0 h0 ⟨j, hj⟩ (Or.inl ⟨hop, hin⟩)))
    exact ⟨⟨j, hj⟩, b, hb⟩
  · by_cases hjk : j = k
    · subst hjk
      obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
        (by rw [hin]; exact List.mem_cons_self)
        (Or.inl (first_any n gs g0 h0 ⟨j, hj⟩ (Or.inr ⟨hop, hin⟩)))
      exact ⟨⟨j, hj⟩, b, hb⟩
    · by_cases hr : ∃ p' g', p' ≠ 0 ∧ gs[p']? = some g' ∧ j ∈ g'.inputs
      · obtain ⟨b, hb⟩ := three_core n gs hcl o hsupp hout g0 h0 ⟨j, hj⟩
          (by rw [hin]; exact List.mem_cons_self) (Or.inr hr)
        exact ⟨⟨j, hj⟩, b, hb⟩
      · exfalso
        exact single_reader n gs o g0 h0 ⟨j, hj⟩ ⟨k, hk⟩
          (fun e => hjk (congrArg Fin.val e).symm) hop hin (hoi ⟨j, hj⟩)
          (fun p' g' hp' hp0 hx => hr ⟨p', g', hp0, hp', hx⟩) (hdep ⟨j, hj⟩)
lemma par_insertNth (n : ℕ) (i : Fin (n + 1)) (y : Fin n → Bool) (b : Bool) :
    par (n + 1) (Fin.insertNth i b y : Fin (n + 1) → Bool) = xor (par n y) b := by
  unfold par
  rw [Finset.card_filter, Finset.card_filter, Fin.sum_univ_succAbove _ i]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove]
  generalize (∑ k : Fin n, if y k = true then 1 else 0) = S
  have h := Nat.mod_two_eq_zero_or_one S
  cases b <;> rcases h with h | h <;> simp [Nat.add_mod, h]
lemma par_flip (n : ℕ) (i : Fin (n + 1)) (u : Fin (n + 1) → Bool) :
    par (n + 1) (Function.update u i (!u i)) = !par (n + 1) u := by
  have key : ∀ (x : Bool) (p : Fin n → Bool),
      par (n + 1) (Function.update (Fin.insertNth i x p : Fin (n + 1) → Bool) i (!x))
        = !par (n + 1) (Fin.insertNth i x p : Fin (n + 1) → Bool) := by
    intro x p
    rw [Fin.update_insertNth, par_insertNth, par_insertNth]
    cases par n p <;> cases x <;> rfl
  have := key (u i) (Fin.removeNth i u)
  rw [Fin.insertNth_self_removeNth] at this
  exact this
lemma clean_step (n : ℕ) (c : Bool) (s : ℕ)
    (h : HasClean (n + 1 + 1) (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) s) :
    ∃ (c' : Bool) (s' : ℕ), s' + 3 ≤ s ∧
      HasClean (n + 1) (fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) c') s' := by
  obtain ⟨gs, o, hcl, hsz, hev⟩ := h
  have hev' : ∀ x : Fin (n + 1 + 1) → Bool,
      (wiresFrom gs (List.ofFn x)).getD o false = xor (par (n + 1 + 1) x) c := hev
  have hok : ∀ g ∈ gs, Ok g := fun g hg => (clean_nok _ gs hcl g hg).1
  have hinv : ∀ (i : Fin (n + 1 + 1)) (b : Bool) (y : Fin (n + 1) → Bool),
      Inv (n + 1) (List.ofFn y)
        (wiresFrom gs (List.ofFn (Fin.insertNth i b y : Fin (n + 1 + 1) → Bool)))
        (elim (n + 1) gs (statAt (n + 1) i b, [])) :=
    fun i b y => inv_elim (n + 1) _ (by simp) gs _ _ hok (inv_at (n + 1) i b y)
  have hval : ∀ (i : Fin (n + 1 + 1)) (b : Bool) (y : Fin (n + 1) → Bool),
      (stF (n + 1) gs i b o).val (wiresFrom (elim (n + 1) gs (statAt (n + 1) i b, [])).2
        (List.ofFn y)) = xor (par (n + 1) y) (xor b c) := by
    intro i b y
    have := ((hinv i b y).2 o).2
    rw [hev', par_insertNth, Bool.xor_assoc] at this
    exact this
  have hout : ∀ (i : Fin (n + 1 + 1)) (b c' : Bool), stF (n + 1) gs i b o ≠ Stat.const c' := by
    intro i b c' hst
    have h1 := hval i b (Fin.snoc (fun _ => false) false)
    have h2 := hval i b (Fin.snoc (fun _ => false) true)
    rw [hst] at h1 h2
    have e := h1.symm.trans h2
    rw [par_snoc, par_snoc] at e
    revert e
    cases par n (fun _ => false) <;> cases b <;> cases c <;> simp
  have hdep : ∀ (i : Fin (n + 1 + 1)) (u : Fin (n + 1 + 1) → Bool),
      (wiresFrom gs (List.ofFn (Function.update u i (!u i)))).getD o false
        ≠ (wiresFrom gs (List.ofFn u)).getD o false := by
    intro i u
    rw [hev', hev', par_flip]
    cases par (n + 1 + 1) u <;> cases c <;> simp
  obtain ⟨i, b, hb⟩ := three_saved (n + 1) gs hcl o hdep hout
  cases hst : stF (n + 1) gs i b o with
  | const c' => exact absurd hst (hout i b c')
  | wire j =>
    refine ⟨xor b c, (elim (n + 1) gs (statAt (n + 1) i b, [])).2.length, by omega,
      (elim (n + 1) gs (statAt (n + 1) i b, [])).2, j, ?_, le_refl _, ?_⟩
    · exact clean_elim (n + 1) (List.ofFn fun _ : Fin (n + 1) => false) (by simp) gs _ _ hok
        (inv_at (n + 1) i b _) (by intro p g hp; simp at hp)
    · intro y
      have := hval i b y
      rw [hst] at this
      exact this
lemma par_lower3 : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasClean (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s → 3 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    obtain ⟨c', s', hs, h'⟩ := clean_step n c s h
    have := ih c' s' h'
    omega
lemma parity_lower3 : ∀ (n s : ℕ),
    PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    3 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : PEqualNP.MetaComplexity.HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have hnc : ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y
          ≠ (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y' := by
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    have := par_lower3 n false s (clean_of (n + 1) _ s hnc h')
    omega
end PEqualNP.Outside.L_meta_3457.SparseLower.Helpers

namespace PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
open PEqualNP.CircuitLowerBounds
def vl {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) : Bool :=
  (wiresFrom gs (List.ofFn u)).getD j false
lemma vl_input {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (j : ℕ) (h : j < k) :
    vl gs u j = u ⟨j, h⟩ := by
  unfold vl
  rw [getD_wiresFrom gs _ j (by simpa using h)]
  exact getD_ofFn k u false ⟨j, h⟩
lemma vl_gate {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) :
    vl gs u (k + p) = g.op.eval (g.inputs.map (vl gs u)) := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hwl : (wiresFrom pre (List.ofFn u)).length = k + pre.length := by
    rw [length_wiresFrom]; simp
  have e : wiresFrom (pre ++ g :: post) (List.ofFn u)
      = wiresFrom post (wiresFrom pre (List.ofFn u) ++
        [g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false)]) := by
    rw [wiresFrom_append]; rfl
  have full : ∀ j, j < k + pre.length →
      (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false
        = (wiresFrom pre (List.ofFn u)).getD j false := by
    intro j hj
    rw [e, getD_wiresFrom _ _ j (by simp [hwl]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
      = g.op.eval (g.inputs.map fun i => (wiresFrom pre (List.ofFn u)).getD i false) := by
    rw [e, getD_wiresFrom _ _ _ (by simp [hwl]), getD_snoc_len _ _ _ _ hwl]
  show (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD (k + pre.length) false
    = g.op.eval (g.inputs.map fun j => (wiresFrom (pre ++ g :: post) (List.ofFn u)).getD j false)
  rw [top]
  congr 1
  apply List.map_congr_left
  intro a ha
  exact (full a (hlt a ha)).symm
lemma vl_congr {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool) (p : ℕ)
    (g : Gate) (hp : gs[p]? = some g) (h : ∀ a ∈ g.inputs, vl gs u a = vl gs u' a) :
    vl gs u (k + p) = vl gs u' (k + p) := by
  rw [vl_gate gs hcl u p g hp, vl_gate gs hcl u' p g hp]
  congr 1
  exact List.map_congr_left h
lemma vl_abs {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (w : ℕ)
    (hw : w ∈ g.inputs) (hv : vl gs u w = fixBit g) : vl gs u (k + p) = fixBit g := by
  rw [vl_gate gs hcl u p g hp]
  rcases hop with h | h
  · have hf : fixBit g = false := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).all id = false
    rw [List.all_eq_false]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩
  · have hf : fixBit g = true := by simp [fixBit, h]
    rw [hf] at hv ⊢
    rw [h]
    show (g.inputs.map (vl gs u)).any id = true
    rw [List.any_eq_true]
    exact ⟨vl gs u w, List.mem_map.2 ⟨w, hw, rfl⟩, by simp [hv]⟩
lemma agree_B {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u u' : Fin k → Bool)
    (B : ℕ → Prop) (L : ℕ) (hin : ∀ j, j < k → ¬ B j → vl gs u j = vl gs u' j)
    (hstep : ∀ p g, gs[p]? = some g → k + p < L → ¬ B (k + p) → (∃ a ∈ g.inputs, B a) →
      (∀ j, j < k + p → ¬ B j → vl gs u j = vl gs u' j) → vl gs u (k + p) = vl gs u' (k + p)) :
    ∀ j, j < L → ¬ B j → vl gs u j = vl gs u' j := by
  intro j
  induction j using Nat.strong_induction_on with
  | _ j ih =>
    intro hjL hB
    by_cases hjk : j < k
    · exact hin j hjk hB
    · obtain ⟨p, rfl⟩ : ∃ p, j = k + p := ⟨j - k, by omega⟩
      cases hp : gs[p]? with
      | none =>
        have hlen : gs.length ≤ p := List.getElem?_eq_none_iff.1 hp
        have h1 : ∀ v : Fin k → Bool, vl gs v (k + p) = false := by
          intro v
          unfold vl
          exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
        rw [h1, h1]
      | some g =>
        by_cases hr : ∃ a ∈ g.inputs, B a
        · exact hstep p g hp hjL hB hr (fun j' hj' hB' => ih j' hj' (by omega) hB')
        · exact vl_congr gs hcl u u' p g hp (fun a ha =>
            ih a ((hcl p g hp).lt a ha) (by have := (hcl p g hp).lt a ha; omega)
              (fun hBa => hr ⟨a, ha, hBa⟩))
lemma takes {k : ℕ} (gs : List Gate)
    (hM1 : ∀ p g, gs[p]? = some g → ∀ c, ¬ ∀ u : Fin k → Bool, vl gs u (k + p) = c)
    (w : ℕ) (hw : w < k + gs.length) (c : Bool) : ∃ u : Fin k → Bool, vl gs u w = c := by
  by_cases hwk : w < k
  · exact ⟨fun _ => c, by rw [vl_input gs _ w hwk]⟩
  · obtain ⟨p, rfl⟩ : ∃ p, w = k + p := ⟨w - k, by omega⟩
    have hpl : p < gs.length := by omega
    by_contra hno
    apply hM1 p gs[p] (List.getElem?_eq_getElem hpl) (!c)
    intro u
    have h := fun h => hno ⟨u, h⟩
    revert h
    cases vl gs u (k + p) <;> cases c <;> simp
lemma gate_eq {gs : List Gate} {p q : ℕ} {g g' : Gate} (h : gs[p]? = some g)
    (h' : gs[q]? = some g') (e : p = q) : g = g' := by
  subst e
  rw [h] at h'
  exact Option.some.inj h'
lemma two_inputs {m : ℕ} {g : Gate} (hg : CleanGate m g) (a b w : ℕ) (ha : a ∈ g.inputs)
    (hb : b ∈ g.inputs) (hab : a ≠ b) (hw : w ∈ g.inputs) : w = a ∨ w = b := by
  rcases hg with ⟨_, j, _, hin⟩ | ⟨_, j, k, _, _, hin⟩ <;> rw [hin] at ha hb hw <;>
    simp at ha hb hw <;> omega
lemma drop_core (k : ℕ) (pre : List Gate) (g : Gate) (post : List Gate)
    (hcl : CleanL k (pre ++ g :: post)) (o : ℕ) (S : Stat)
    (hS : ∀ y : Fin k → Bool, S.Valid (k + (elim k pre (idStats k, [])).2.length) ∧
      S.val (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y))
        = vl (pre ++ g :: post) y (k + pre.length))
    (hnc : ∃ y y' : Fin k → Bool, vl (pre ++ g :: post) y o ≠ vl (pre ++ g :: post) y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ (pre ++ g :: post).length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl (pre ++ g :: post) y o := by
  have hok : ∀ g' ∈ pre ++ g :: post, Ok g' := fun g' hg' => (clean_nok _ _ hcl g' hg').1
  have hokpre : ∀ g' ∈ pre, Ok g' := fun g' h => hok g' (List.mem_append_left _ h)
  have hokpost : ∀ g' ∈ post, Ok g' :=
    fun g' h => hok g' (List.mem_append_right _ (List.mem_cons_of_mem _ h))
  have inv1 : ∀ y : Fin k → Bool, Inv k (List.ofFn y) (wiresFrom pre (List.ofFn y))
      (elim k pre (idStats k, [])) :=
    fun y => inv_elim k _ (by simp) pre _ _ hokpre (inv_id k y)
  have hwl : ∀ y : Fin k → Bool, (wiresFrom pre (List.ofFn y)).length = k + pre.length := by
    intro y; rw [length_wiresFrom]; simp
  have hfull : ∀ y : Fin k → Bool, wiresFrom (pre ++ g :: post) (List.ofFn y)
      = wiresFrom post (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)]) := by
    intro y; rw [wiresFrom_append]; rfl
  have hgv : ∀ y : Fin k → Bool, vl (pre ++ g :: post) y (k + pre.length)
      = g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false) := by
    intro y
    show (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD (k + pre.length) false = _
    rw [hfull, getD_wiresFrom _ _ _ (by simp [hwl y]), getD_snoc_len _ _ _ _ (hwl y)]
  have inv2 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom pre (List.ofFn y) ++
        [g.op.eval (g.inputs.map fun a => (wiresFrom pre (List.ofFn y)).getD a false)])
      ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2) := by
    intro y
    obtain ⟨hl, hi⟩ := inv1 y
    refine ⟨by simp [hl], ?_⟩
    intro a
    show (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).Valid
        (k + (elim k pre (idStats k, [])).2.length) ∧
      (((elim k pre (idStats k, [])).1 ++ [S]).getD a (Stat.const false)).val
        (wiresFrom (elim k pre (idStats k, [])).2 (List.ofFn y)) = _
    by_cases hal : a = (elim k pre (idStats k, [])).1.length
    · rw [hal, getD_snoc_eq, hl, getD_snoc_eq]
      exact ⟨(hS y).1, by rw [(hS y).2, hgv]⟩
    · rw [getD_snoc_ne _ _ _ _ hal, getD_snoc_ne _ _ _ _ (by omega)]
      exact hi a
  have inv3 : ∀ y : Fin k → Bool, Inv k (List.ofFn y)
      (wiresFrom (pre ++ g :: post) (List.ofFn y))
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)) := by
    intro y
    rw [hfull]
    exact inv_elim k _ (by simp) post _ _ hokpost (inv2 y)
  have hc1 : CleanL k (elim k pre (idStats k, [])).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) pre _ _ hokpre (inv_id k _)
      (by intro p g' hp; simp at hp)
  have hc3 : CleanL k
      (elim k post ((elim k pre (idStats k, [])).1 ++ [S], (elim k pre (idStats k, [])).2)).2 :=
    clean_elim k (List.ofFn fun _ : Fin k => false) (by simp) post _ _ hokpost (inv2 _) hc1
  have hlen : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).2.length + 1 ≤ (pre ++ g :: post).length := by
    have h1 : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).2.length
        ≤ (elim k pre (idStats k, [])).2.length + post.length := elim_len k post _
    have h2 : (elim k pre (idStats k, [])).2.length ≤ 0 + pre.length :=
      elim_len k pre (idStats k, [])
    simp only [List.length_append, List.length_cons]
    omega
  have hval : ∀ y : Fin k → Bool,
      ((elim k post ((elim k pre (idStats k, [])).1 ++ [S],
        (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false)).val
        (wiresFrom (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
          (elim k pre (idStats k, [])).2)).2 (List.ofFn y))
      = vl (pre ++ g :: post) y o := fun y => ((inv3 y).2 o).2
  cases hst : (elim k post ((elim k pre (idStats k, [])).1 ++ [S],
      (elim k pre (idStats k, [])).2)).1.getD o (Stat.const false) with
  | const c =>
    exfalso
    obtain ⟨y, y', hne⟩ := hnc
    apply hne
    rw [← hval y, ← hval y', hst]
    rfl
  | wire j =>
    refine ⟨_, j, hc3, hlen, ?_⟩
    intro y
    have h := hval y
    rw [hst] at h
    exact h
lemma drop_alias (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p j : ℕ) (hp : p < gs.length)
    (hj : j < k + p) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = vl gs y j)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  apply drop_core k pre g post hcl o ((elim k pre (idStats k, [])).1.getD j (Stat.const false))
    ?_ hnc
  intro y
  have hokpre : ∀ g' ∈ pre, Ok g' :=
    fun g' h => (clean_nok _ _ hcl g' (List.mem_append_left _ h)).1
  have inv1 := inv_elim k (List.ofFn y) (by simp) pre _ _ hokpre (inv_id k y)
  refine ⟨(inv1.2 j).1, ?_⟩
  rw [(inv1.2 j).2, heq y]
  show (wiresFrom pre (List.ofFn y)).getD j false
    = (wiresFrom (pre ++ g :: post) (List.ofFn y)).getD j false
  rw [wiresFrom_append, getD_wiresFrom (g :: post) (wiresFrom pre (List.ofFn y)) j
    (by rw [length_wiresFrom]; simp; omega)]
lemma drop_const (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (c : Bool)
    (hp : p < gs.length) (heq : ∀ y : Fin k → Bool, vl gs y (k + p) = c)
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hg
  exact drop_core k pre g post hcl o (Stat.const c) (fun y => ⟨trivial, (heq y).symm⟩) hnc
abbrev ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (y : Fin n → Bool) : Fin (n + 1) → Bool :=
  Fin.insertNth i b y
def passG (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) : List Gate :=
  (elim n gs (statAt n i b, [])).2
def IsC (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (a : ℕ) : Prop :=
  ∃ c, stF n gs i b a = Stat.const c
lemma inv_stF (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (y : Fin n → Bool) :
    Inv n (List.ofFn y) (wiresFrom gs (List.ofFn (ins i b y))) (elim n gs (statAt n i b, [])) :=
  inv_elim n _ (by simp) gs _ _ (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b y)
lemma st_val_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j : ℕ) (c : Bool) (h : stF n gs i b j = Stat.const c) (y : Fin n → Bool) :
    vl gs (ins i b y) j = c := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.const c from h] at h1
  exact h1.symm
lemma st_val_wire (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (j q : ℕ) (h : stF n gs i b j = Stat.wire q) (y : Fin n → Bool) :
    vl gs (ins i b y) j = vl (passG n gs i b) y q := by
  have h1 := ((inv_stF n gs hcl i b y).2 j).2
  rw [show (elim n gs (statAt n i b, [])).1.getD j (Stat.const false) = Stat.wire q from h] at h1
  exact h1.symm
lemma st_other (n : ℕ) (gs : List Gate) (i : Fin (n + 1)) (b : Bool) (X : Fin (n + 1))
    (h : X ≠ i) : ∃ k, k < n ∧ stF n gs i b X = Stat.wire k := by
  rcases Fin.eq_self_or_eq_succAbove i X with e | ⟨k, e⟩
  · exact absurd e h
  · refine ⟨k, k.isLt, ?_⟩
    rw [e]
    show (elim n gs (statAt n i b, [])).1.getD (i.succAbove k) (Stat.const false) = _
    rw [elim_getD n _ _ gs _ (by
      show ((i.succAbove k : Fin (n + 1)) : ℕ) < (statAt n i b).length
      rw [statAt_length]; exact (i.succAbove k).isLt)]
    exact statAt_above n i b k
lemma st_gate (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) :
    ∃ t, stF n gs i b (n + 1 + p)
      = (simplify g.op (n + t) (g.inputs.map (stF n gs i b))).2 := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  refine ⟨(elim n pre (statAt n i b, [])).2.length, ?_⟩
  have e1 : stF n (pre ++ g :: post) i b (n + 1 + pre.length)
      = (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false) :=
    elim_split_getD n pre g post _ _ _ (by rw [hL])
  have e2 : (elimStep n (elim n pre (statAt n i b, [])) g).1.getD (n + 1 + pre.length)
        (Stat.const false)
      = (simplify g.op (n + (elim n pre (statAt n i b, [])).2.length)
          (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))).2 :=
    getD_snoc_len _ _ _ _ (by rw [elim_fst_len, hL])
  have e3 : (g.inputs.map fun a => (elim n pre (statAt n i b, [])).1.getD a (Stat.const false))
      = g.inputs.map (stF n (pre ++ g :: post) i b) :=
    List.map_congr_left (fun a ha =>
      (elim_split_getD_lt n pre g post _ a _ (by rw [hL]; exact hlt a ha)).symm)
  rw [e1, e2, e3]
lemma simp_allconst (op : GateOp) (t : ℕ) (ins : List Stat)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (hlen : ins.length ≤ 2)
    (h : ∀ s ∈ ins, ∃ c, s = Stat.const c) : ∃ c, (simplify op t ins).2 = Stat.const c := by
  rcases hop with rfl | rfl | rfl
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, _ | ⟨d, _ | ⟨e, l⟩⟩⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      obtain ⟨c', rfl⟩ := h d (by simp)
      exact ⟨_, rfl⟩
    · simp at hlen
  · rcases ins with _ | ⟨a, l⟩
    · exact ⟨_, rfl⟩
    · obtain ⟨c, rfl⟩ := h a (by simp)
      exact ⟨_, rfl⟩
lemma simp_fresh (g : Gate) (m : ℕ) (hg : CleanGate m g) (t : ℕ) (F : ℕ → Stat)
    (h : ∀ a ∈ g.inputs, ∀ c, F a ≠ Stat.const c) :
    (simplify g.op t (g.inputs.map F)).2 = Stat.wire t := by
  rcases hg with ⟨hop, j, _, hin⟩ | ⟨hop | hop, j, k, _, _, hin⟩
  · have h1 := h j (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q => simp [simplify, simpNot, hF]
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q =>
      cases hF' : F k with
      | const c => exact absurd hF' (h2 c)
      | wire q' => simp [simplify, simpAnd, hF, hF']
  · have h1 := h j (by rw [hin]; simp)
    have h2 := h k (by rw [hin]; simp)
    rw [hop, hin]
    cases hF : F j with
    | const c => exact absurd hF (h1 c)
    | wire q =>
      cases hF' : F k with
      | const c => exact absurd hF' (h2 c)
      | wire q' => simp [simplify, simpOr, hF, hF']
lemma st_allconst (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, IsC n gs i b a) : IsC n gs i b (n + 1 + p) := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  have hn := (hcl p g hp).nok
  obtain ⟨c, hc⟩ := simp_allconst g.op (n + t) (g.inputs.map (stF n gs i b)) hn.1.1
    (by simpa using hn.1.2) (by
      intro s hs
      obtain ⟨a, ha, rfl⟩ := List.mem_map.1 hs
      exact h a ha)
  exact ⟨c, by rw [ht]; exact hc⟩
lemma st_fresh (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (h : ∀ a ∈ g.inputs, ∀ c, stF n gs i b a ≠ Stat.const c) :
    ∃ q, n ≤ q ∧ stF n gs i b (n + 1 + p) = Stat.wire q := by
  obtain ⟨t, ht⟩ := st_gate n gs hcl i b p g hp
  exact ⟨n + t, by omega, by rw [ht]; exact simp_fresh g _ (hcl p g hp) _ _ h⟩
lemma rc_of_const (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (hc : IsC n gs i b (n + 1 + p)) :
    RC n gs i b p := by
  by_contra hno
  obtain ⟨q, _, hq⟩ := st_fresh n gs hcl i b p g hp
    (fun a ha c' hc' => hno ⟨g, hp, a, ha, c', hc'⟩)
  obtain ⟨c, hc⟩ := hc
  rw [hq] at hc
  cases hc
lemma const_read (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs)
    (hc : stF n gs i b a = Stat.const (fixBit g)) : IsC n gs i b (n + 1 + p) := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have h := const_of_read n gs (statAt n i b, []) p g hp ((hcl p g hp).nok) a ha
    (by rw [hL]; exact (hcl p g hp).lt a ha) hc
  rw [hL] at h
  exact h
lemma st_shape (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (b : Bool)
    (p : ℕ) (g : Gate) (hp : gs[p]? = some g) (a : ℕ) (ha : a ∈ g.inputs) (c : Bool)
    (hc : stF n gs i b a = Stat.const c) (hn : ∀ c', stF n gs i b (n + 1 + p) ≠ Stat.const c') :
    (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ c ≠ fixBit g ∧
      ∃ w ∈ g.inputs, ∀ c', stF n gs i b w ≠ Stat.const c' := by
  have hw : ∃ w ∈ g.inputs, ∀ c', stF n gs i b w ≠ Stat.const c' := by
    by_contra hno
    obtain ⟨c', hc'⟩ := st_allconst n gs hcl i b p g hp (fun a' ha' => by
      by_contra h'
      exact hno ⟨a', ha', fun c' hc' => h' ⟨c', hc'⟩⟩)
    exact hn c' hc'
  refine ⟨?_, ?_, hw⟩
  · rcases hcl p g hp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · exfalso
      obtain ⟨w, hw1, hw2⟩ := hw
      have e1 : w = j := by rw [hin] at hw1; simpa using hw1
      have e2 : a = j := by rw [hin] at ha; simpa using ha
      exact hw2 c (by rw [e1, ← e2]; exact hc)
    · exact hop
  · intro e
    obtain ⟨c', hc'⟩ := const_read n gs hcl i b p g hp a ha (by rw [← e]; exact hc)
    exact hn c' hc'
lemma four_count (n : ℕ) (gs : List Gate) (hcl : CleanL (n + 1) gs) (i : Fin (n + 1))
    (b : Bool) (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    (passG n gs i b).length + 4 ≤ gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) {p1, p2, p3, p4} (by
    intro p hp
    have hR : RC n gs i b p := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl | rfl | rfl <;> assumption
    obtain ⟨g, hg, a, ha, c, hc⟩ := hR
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_eq_three.2 ⟨p2, p3, p4, h23, h24, h34, rfl⟩]
  rw [hcard] at hcount
  simpa [passG] using hcount
def Red (n : ℕ) (gs : List Gate) (o : ℕ) : Prop :=
  ∃ (i : Fin (n + 1)) (b : Bool) (gs' : List Gate) (o' : ℕ), CleanL n gs' ∧
    gs'.length + 4 ≤ gs.length ∧ ∀ y : Fin n → Bool, vl gs' y o' = vl gs (ins i b y) o
structure Min (n : ℕ) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL (n + 1) gs
  hdep : ∀ (i : Fin (n + 1)) (u : Fin (n + 1) → Bool),
    vl gs (Function.update u i (!u i)) o ≠ vl gs u o
  hnc : ∀ (i : Fin (n + 1)) (b : Bool), ∃ y y' : Fin n → Bool,
    vl gs (ins i b y) o ≠ vl gs (ins i b y') o
  m1 : ∀ p g, gs[p]? = some g → ∀ c, ¬ ∀ u : Fin (n + 1) → Bool, vl gs u (n + 1 + p) = c
  m2 : ∀ p g, gs[p]? = some g → ∀ j, j < n + 1 + p →
    ¬ ∀ u : Fin (n + 1) → Bool, vl gs u (n + 1 + p) = vl gs u j
  nored : ¬ Red n gs o
section SourceSection1
variable {n : ℕ} {gs : List Gate} {o : ℕ}
lemma Min.out (M : Min n gs o) (i : Fin (n + 1)) (b c : Bool) :
    stF n gs i b o ≠ Stat.const c := by
  intro h
  obtain ⟨y, y', hne⟩ := M.hnc i b
  exact hne ((st_val_const n gs M.hcl i b o c h y).trans
    (st_val_const n gs M.hcl i b o c h y').symm)
lemma Min.pass (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) :
    ∃ j, CleanL n (passG n gs i b) ∧
      ∀ y : Fin n → Bool, vl (passG n gs i b) y j = vl gs (ins i b y) o := by
  cases hst : stF n gs i b o with
  | const c => exact absurd hst (M.out i b c)
  | wire j =>
    refine ⟨j, ?_, fun y => (st_val_wire n gs M.hcl i b o j hst y).symm⟩
    exact clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
      (fun g hg => (clean_nok _ gs M.hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp)
lemma Min.nf4 (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2)
    (h13 : p1 ≠ p3) (h14 : p1 ≠ p4) (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    False := by
  obtain ⟨j, hc, he⟩ := M.pass i b
  exact M.nored ⟨i, b, _, j, hc,
    four_count n gs M.hcl i b p1 p2 p3 p4 h12 h13 h14 h23 h24 h34 h1 h2 h3 h4, he⟩
lemma Min.ndup (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2)
    (h13 : p1 ≠ p3) (h23 : p2 ≠ p3) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2)
    (h3 : RC n gs i b p3) (p j q k : ℕ) (hq : stF n gs i b p = Stat.wire q) (hnq : n ≤ q)
    (hk : stF n gs i b j = Stat.wire k) (hkq : k < q)
    (heq : ∀ y : Fin n → Bool, vl gs (ins i b y) p = vl gs (ins i b y) j) : False := by
  obtain ⟨jo, hc, he⟩ := M.pass i b
  have h3c : (passG n gs i b).length + 3 ≤ gs.length :=
    three_count n gs M.hcl i b p1 p2 p3 h12 h13 h23 h1 h2 h3
  have hqv : q < n + (passG n gs i b).length := by
    have h := ((inv_stF n gs M.hcl i b (fun _ => false)).2 p).1
    rw [show (elim n gs (statAt n i b, [])).1.getD p (Stat.const false) = Stat.wire q from hq]
      at h
    exact h
  have heq1 : ∀ y : Fin n → Bool,
      vl (passG n gs i b) y (n + (q - n)) = vl (passG n gs i b) y k := by
    intro y
    rw [show n + (q - n) = q by omega, ← st_val_wire n gs M.hcl i b p q hq y,
      ← st_val_wire n gs M.hcl i b j k hk y]
    exact heq y
  obtain ⟨y, y', hne⟩ := M.hnc i b
  obtain ⟨gs2, o2, hc2, hl2, he2⟩ := drop_alias n (passG n gs i b) hc jo (q - n) k (by omega)
    (by omega) heq1 ⟨y, y', by rw [he y, he y']; exact hne⟩
  exact M.nored ⟨i, b, gs2, o2, hc2, by omega, fun y => by rw [he2 y, he y]⟩
lemma Min.reader (M : Min n gs o) (i : Fin (n + 1)) (B : ℕ → Prop) (hi : B i) (ho : ¬ B o) :
    ∃ p g, gs[p]? = some g ∧ ¬ B (n + 1 + p) ∧ ∃ a ∈ g.inputs, B a := by
  apply exists_reader (n + 1) i B hi gs o ho
  by_contra hns
  refine M.hdep i (fun _ => false) ?_
  exact (agree_wiresFrom (Function.update (fun _ => false) i (!false)) (fun _ => false) gs _ _ _
    (agree_inputs _ _)).2.2 o (by
      intro k hk
      have : k ≠ i := fun e => hns (e ▸ hk)
      simp [Function.update_of_ne this])
lemma Min.cb (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (B : ℕ → Prop) (hi : B i)
    (hB : ∀ a, B a → IsC n gs i b a) :
    ∃ h1 h2, h1 ≠ h2 ∧ ¬ B (n + 1 + h1) ∧ ¬ B (n + 1 + h2) ∧ RC n gs i b h1 ∧ RC n gs i b h2 := by
  have ho : ¬ B o := fun h => by
    obtain ⟨c, hc⟩ := hB o h
    exact M.out i b c hc
  obtain ⟨h1, g1, hg1, hB1, a1, ha1, hBa1⟩ := M.reader i B hi ho
  have r1 : RC n gs i b h1 := ⟨g1, hg1, a1, ha1, hB a1 hBa1⟩
  by_cases hex : ∃ h2 g2, h2 ≠ h1 ∧ gs[h2]? = some g2 ∧ ¬ B (n + 1 + h2) ∧ ∃ a ∈ g2.inputs, B a
  · obtain ⟨h2, g2, hne, hg2, hB2, a2, ha2, hBa2⟩ := hex
    exact ⟨h1, h2, Ne.symm hne, hB1, hB2, r1, ⟨g2, hg2, a2, ha2, hB a2 hBa2⟩⟩
  by_cases hc1 : IsC n gs i b (n + 1 + h1)
  · obtain ⟨h2, g2, hg2, hB2, a2, ha2, hBa2⟩ := M.reader i (fun a => B a ∨ a = n + 1 + h1)
      (Or.inl hi) (fun h => h.elim ho (fun e => by
        obtain ⟨c, hc⟩ := hc1
        exact M.out i b c (by rw [e]; exact hc)))
    have hB2' : ¬ (B (n + 1 + h2) ∨ n + 1 + h2 = n + 1 + h1) := hB2
    have hBa2' : B a2 ∨ a2 = n + 1 + h1 := hBa2
    refine ⟨h1, h2, fun e => hB2' (Or.inr (by rw [e])), hB1, fun h => hB2' (Or.inl h), r1,
      g2, hg2, a2, ha2, ?_⟩
    rcases hBa2' with h | h
    · exact hB a2 h
    · rw [h]; exact hc1
  · exfalso
    obtain ⟨c1, hc1'⟩ := hB a1 hBa1
    obtain ⟨hop, _, w, hw, hwn⟩ := st_shape n gs M.hcl i b h1 g1 hg1 a1 ha1 c1 hc1'
      (fun c' h => hc1 ⟨c', h⟩)
    have hBw : ¬ B w := fun h => by
      obtain ⟨c, hc⟩ := hB w h
      exact hwn c hc
    have hwlt : w < n + 1 + h1 := (M.hcl h1 g1 hg1).lt w hw
    have hl1 : h1 < gs.length := (List.getElem?_eq_some_iff.1 hg1).1
    obtain ⟨u, hu⟩ := takes gs M.m1 w (by omega) (fixBit g1)
    apply M.hdep i u
    refine agree_B gs M.hcl _ _ B (o + 1) ?_ ?_ o (by omega) ho
    · intro j hj hBj
      rw [vl_input gs _ j hj, vl_input gs _ j hj]
      exact Function.update_of_ne
        (fun e => hBj (by rw [show j = (i : ℕ) from congrArg Fin.val e]; exact hi)) _ _
    · intro p g hp _ hBp hr hear
      obtain ⟨a, ha, hBa⟩ := hr
      have hp1 : p = h1 := by
        by_contra hne
        exact hex ⟨p, g, hne, hp, hBp, a, ha, hBa⟩
      rw [hp1] at hear ⊢
      rw [vl_abs gs M.hcl _ h1 g1 hg1 hop w hw (by rw [hear w hwlt hBw]; exact hu),
        vl_abs gs M.hcl u h1 g1 hg1 hop w hw hu]
lemma Min.one_const (M : Min n gs o) (i : Fin (n + 1)) (b : Bool) (p q : ℕ) (hpq : p ≠ q)
    (gp gq : Gate) (hp : gs[p]? = some gp) (hq : gs[q]? = some gq)
    (cp : IsC n gs i b (n + 1 + p)) (cq : IsC n gs i b (n + 1 + q)) : False := by
  obtain ⟨h1, h2, h12, hB1, hB2, r1, r2⟩ := M.cb i b
    (fun a => a = (i : ℕ) ∨ a = n + 1 + p ∨ a = n + 1 + q) (Or.inl rfl) (by
      intro a ha
      rcases ha with e | e | e
      · rw [e]; exact ⟨b, stF_self n gs i b⟩
      · rw [e]; exact cp
      · rw [e]; exact cq)
  have hB1' : ¬ (n + 1 + h1 = (i : ℕ) ∨ n + 1 + h1 = n + 1 + p ∨ n + 1 + h1 = n + 1 + q) := hB1
  have hB2' : ¬ (n + 1 + h2 = (i : ℕ) ∨ n + 1 + h2 = n + 1 + p ∨ n + 1 + h2 = n + 1 + q) := hB2
  exact M.nf4 i b p q h1 h2 hpq (fun e => hB1' (Or.inr (Or.inl (by rw [e]))))
    (fun e => hB2' (Or.inr (Or.inl (by rw [e])))) (fun e => hB1' (Or.inr (Or.inr (by rw [e]))))
    (fun e => hB2' (Or.inr (Or.inr (by rw [e])))) h12
    (rc_of_const n gs M.hcl i b p gp hp cp) (rc_of_const n gs M.hcl i b q gq hq cq) r1 r2
lemma Min.reader_const (M : Min n gs o) (i : Fin (n + 1)) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (hr : (i : ℕ) ∈ g.inputs) : IsC n gs i (fixBit g) (n + 1 + p) :=
  const_read n gs M.hcl i _ p g hp i hr (stF_self n gs i _)
lemma Min.no_not (M : Min n gs o) (i : Fin (n + 1)) (p : ℕ) (g : Gate) (hp : gs[p]? = some g)
    (hop : g.op = GateOp.not) (hr : (i : ℕ) ∈ g.inputs) : False := by
  have hin : g.inputs = [(i : ℕ)] := by
    rcases M.hcl p g hp with ⟨_, j, _, hin⟩ | ⟨h, _⟩
    · rw [hin] at hr
      have e : (i : ℕ) = j := by simpa using hr
      rw [hin, e]
    · rcases h with h | h <;> rw [hop] at h <;> cases h
  have hN : ∀ b, IsC n gs i b (n + 1 + p) := fun b =>
    st_allconst n gs M.hcl i b p g hp (fun a ha => by
      rw [hin] at ha
      have e : a = (i : ℕ) := by simpa using ha
      rw [e]; exact ⟨b, stF_self n gs i b⟩)
  have hNv : ∀ b, stF n gs i b (n + 1 + p) = Stat.const (!b) := by
    intro b
    obtain ⟨c, hc⟩ := hN b
    have h1 := st_val_const n gs M.hcl i b (n + 1 + p) c hc (fun _ => false)
    have h2 : vl gs (ins i b fun _ => false) (i : ℕ) = b := by
      rw [vl_input gs _ i i.isLt]; simp [ins]
    have h3 : c = !b := by
      rw [← h1, vl_gate gs M.hcl _ p g hp, hop, hin]
      simp [GateOp.eval, h2]
    rw [hc, h3]
  have ho : ¬ (o = (i : ℕ) ∨ o = n + 1 + p) := by
    intro h
    rcases h with e | e
    · exact M.out i false false (by rw [e]; exact stF_self n gs i false)
    · exact M.out i false _ (by rw [e]; exact hNv false)
  obtain ⟨q, gq, hq, hBq, a, ha, hBa⟩ :=
    M.reader i (fun a => a = (i : ℕ) ∨ a = n + 1 + p) (Or.inl rfl) ho
  have hBq' : ¬ (n + 1 + q = (i : ℕ) ∨ n + 1 + q = n + 1 + p) := hBq
  have hBa' : a = (i : ℕ) ∨ a = n + 1 + p := hBa
  have hpq : p ≠ q := fun e => hBq' (Or.inr (by rw [e]))
  have hcq : ∃ b, IsC n gs i b (n + 1 + q) := by
    rcases hBa' with e | e
    · exact ⟨fixBit gq, M.reader_const i q gq hq (e ▸ ha)⟩
    · refine ⟨!fixBit gq, const_read n gs M.hcl i _ q gq hq (n + 1 + p) (e ▸ ha) ?_⟩
      rw [hNv]; simp
  obtain ⟨b0, hb0⟩ := hcq
  exact M.one_const i b0 p q hpq g gq hp hq (hN b0) hb0
lemma Min.forced (M : Min n gs o) (X : Fin (n + 1)) (p q : ℕ) (gp : Gate)
    (hp : gs[p]? = some gp) (hXp : (X : ℕ) ∈ gp.inputs)
    (hR : ∀ p' g', gs[p']? = some g' → (X : ℕ) ∈ g'.inputs → p' = p ∨ p' = q)
    (hqo : o ≠ n + 1 + q) (u : Fin (n + 1) → Bool)
    (hq : vl gs (Function.update u X (!u X)) (n + 1 + q) = vl gs u (n + 1 + q) ∨
      ∀ (p' : ℕ) (g' : Gate), gs[p']? = some g' → (n + 1 + q) ∉ g'.inputs) :
    vl gs u (n + 1 + p) = u X := by
  by_contra hne
  have hX : vl gs u X = u X := vl_input gs u X X.isLt
  have hX' : vl gs (Function.update u X (!u X)) X = !u X := by
    rw [vl_input gs _ X X.isLt]; simp
  have key : vl gs (Function.update u X (!u X)) (n + 1 + p) = vl gs u (n + 1 + p) := by
    rcases M.hcl p gp hp with ⟨hopn, _⟩ | ⟨hop, j, k, _, _, hin⟩
    · exact (M.no_not X p gp hp hopn hXp).elim
    · have e1 : ∀ v : Fin (n + 1) → Bool,
          vl gs v (n + 1 + p) = gp.op.eval [vl gs v j, vl gs v k] := by
        intro v
        rw [vl_gate gs M.hcl v p gp hp, hin]
        rfl
      rw [e1 u] at hne
      rw [e1 u, e1 (Function.update u X (!u X))]
      have hjk : (X : ℕ) = j ∨ (X : ℕ) = k := by rw [hin] at hXp; simpa using hXp
      rcases hjk with e | e
      · rw [← e, hX] at hne
        rw [← e, hX', hX]
        revert hne
        generalize vl gs (Function.update u X (!u X)) k = w'
        generalize vl gs u k = w
        generalize u X = x
        rcases hop with hop | hop <;> rw [hop] <;> cases x <;> cases w <;> cases w' <;>
          simp [GateOp.eval]
      · rw [← e, hX] at hne
        rw [← e, hX', hX]
        revert hne
        generalize vl gs (Function.update u X (!u X)) j = w'
        generalize vl gs u j = w
        generalize u X = x
        rcases hop with hop | hop <;> rw [hop] <;> cases x <;> cases w <;> cases w' <;>
          simp [GateOp.eval]
  apply M.hdep X u
  refine agree_B gs M.hcl _ _ (fun a => a = (X : ℕ) ∨ a = n + 1 + q) (o + 1) ?_ ?_ o (by omega) ?_
  · intro j hj hBj
    have hBj' : ¬ (j = (X : ℕ) ∨ j = n + 1 + q) := hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne (fun e => hBj' (Or.inl (congrArg Fin.val e))) _ _
  · intro p' g' hp' _ hB' hr hear
    have hB'' : ¬ (n + 1 + p' = (X : ℕ) ∨ n + 1 + p' = n + 1 + q) := hB'
    obtain ⟨a, ha, hBa⟩ := hr
    have hBa' : a = (X : ℕ) ∨ a = n + 1 + q := hBa
    by_cases hx : (X : ℕ) ∈ g'.inputs
    · rcases hR p' g' hp' hx with e | e
      · rw [e]; exact key
      · exact absurd (Or.inr (by rw [e])) hB''
    · rcases hq with hq | hq
      · apply vl_congr gs M.hcl _ _ p' g' hp'
        intro a' ha'
        by_cases e1 : a' = n + 1 + q
        · rw [e1]; exact hq
        · exact hear a' ((M.hcl p' g' hp').lt a' ha')
            (fun hb => (hb : a' = (X : ℕ) ∨ a' = n + 1 + q).elim (fun e => hx (e ▸ ha')) e1)
      · rcases hBa' with e | e
        · exact absurd (e ▸ ha) hx
        · exact absurd (e ▸ ha) (hq p' g' hp')
  · exact fun (h : o = (X : ℕ) ∨ o = n + 1 + q) => h.elim
      (fun e => M.out X false false (by rw [e]; exact stF_self n gs X false)) hqo
lemma Min.block2 (M : Min n gs o) (Z : Fin (n + 1)) (B : ℕ → Prop) (hZ : B Z) (ho : ¬ B o)
    (u : Fin (n + 1) → Bool) (ha hb : ℕ) (ga gb : Gate) (hga : gs[ha]? = some ga)
    (hgb : gs[hb]? = some gb)
    (hout : ∀ p' g', gs[p']? = some g' → ¬ B (n + 1 + p') → (∃ a ∈ g'.inputs, B a) →
      p' = ha ∨ p' = hb)
    (hopa : ga.op = GateOp.and ∨ ga.op = GateOp.or) (w : ℕ) (hw : w ∈ ga.inputs) (hBw : ¬ B w)
    (hv : vl gs u w = fixBit ga)
    (hagree : ∀ a ∈ gb.inputs, B a → vl gs (Function.update u Z (!u Z)) a = vl gs u a) :
    False := by
  apply M.hdep Z u
  refine agree_B gs M.hcl _ _ B (o + 1) ?_ ?_ o (by omega) ho
  · intro j hj hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne
      (fun e => hBj (by rw [show j = (Z : ℕ) from congrArg Fin.val e]; exact hZ)) _ _
  · intro p' g' hp' _ hB' hr hear
    rcases hout p' g' hp' hB' hr with e | e
    · rw [e] at hear ⊢
      have hwlt : w < n + 1 + ha := (M.hcl ha ga hga).lt w hw
      rw [vl_abs gs M.hcl _ ha ga hga hopa w hw (by rw [hear w hwlt hBw]; exact hv),
        vl_abs gs M.hcl u ha ga hga hopa w hw hv]
    · rw [e] at hear ⊢
      apply vl_congr gs M.hcl _ _ hb gb hgb
      intro a haa
      by_cases hBa : B a
      · exact hagree a haa hBa
      · exact hear a ((M.hcl hb gb hgb).lt a haa) hBa
lemma Min.before (M : Min n gs o) (Z : Fin (n + 1)) (B : ℕ → Prop) (hZ : B Z)
    (u : Fin (n + 1) → Bool) (w : ℕ) (hBw : ¬ B w)
    (hne : vl gs (Function.update u Z (!u Z)) w ≠ vl gs u w) :
    ∃ p' g', gs[p']? = some g' ∧ n + 1 + p' ≤ w ∧ ¬ B (n + 1 + p') ∧ ∃ a ∈ g'.inputs, B a := by
  by_contra hno
  apply hne
  refine agree_B gs M.hcl _ _ B (w + 1) ?_ ?_ w (by omega) hBw
  · intro j hj hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne
      (fun e => hBj (by rw [show j = (Z : ℕ) from congrArg Fin.val e]; exact hZ)) _ _
  · intro p' g' hp' hlt hB' hr _
    exact (hno ⟨p', g', hp', by omega, hB', hr⟩).elim
lemma Min.second (M : Min n gs o) (X Y : Fin (n + 1)) (hXY : X ≠ Y) (pG : ℕ) (gG : Gate)
    (hG : gs[pG]? = some gG) (hop : gG.op = GateOp.and ∨ gG.op = GateOp.or)
    (hY : (Y : ℕ) ∈ gG.inputs) :
    ∃ r gr, r ≠ pG ∧ gs[r]? = some gr ∧ (X : ℕ) ∈ gr.inputs := by
  by_contra hno
  have hu : ∀ v : Fin (n + 1) → Bool, v Y = fixBit gG → vl gs v (n + 1 + pG) = fixBit gG :=
    fun v hv => vl_abs gs M.hcl v pG gG hG hop Y hY (by rw [vl_input gs v Y Y.isLt]; exact hv)
  apply M.hdep X (fun _ => fixBit gG)
  refine agree_B gs M.hcl _ _ (fun a => a = (X : ℕ)) (o + 1) ?_ ?_ o (by omega) ?_
  · intro j hj hBj
    have hBj' : ¬ (j = (X : ℕ)) := hBj
    rw [vl_input gs _ j hj, vl_input gs _ j hj]
    exact Function.update_of_ne (fun e => hBj' (congrArg Fin.val e)) _ _
  · intro p g hp _ _ hr _
    obtain ⟨a, ha, hBa⟩ := hr
    have hBa' : a = (X : ℕ) := hBa
    have hpG : p = pG := by
      by_contra hne
      exact hno ⟨p, g, hne, hp, hBa' ▸ ha⟩
    rw [hpG]
    rw [hu _ (by rw [Function.update_of_ne hXY.symm]), hu _ rfl]
  · exact fun (e : o = (X : ℕ)) => M.out X false false (by rw [e]; exact stF_self n gs X false)
lemma Min.side (M : Min n gs o) (X Y : Fin (n + 1)) (hXY : X ≠ Y) (pG : ℕ) (gG : Gate)
    (hG : gs[pG]? = some gG) (hop : gG.op = GateOp.and ∨ gG.op = GateOp.or)
    (hX : (X : ℕ) ∈ gG.inputs) (hY : (Y : ℕ) ∈ gG.inputs) :
    ∃ r gr, r ≠ pG ∧ gs[r]? = some gr ∧ (X : ℕ) ∈ gr.inputs ∧
      (∀ p' g', gs[p']? = some g' → (X : ℕ) ∈ g'.inputs → p' = r ∨ p' = pG) ∧
      IsC n gs X (!fixBit gG) (n + 1 + r) ∧ fixBit gr = !fixBit gG ∧
      (gr.op = GateOp.and ∨ gr.op = GateOp.or) ∧ (n + 1 + pG) ∉ gr.inputs := by
  have cG : IsC n gs X (fixBit gG) (n + 1 + pG) := M.reader_const X pG gG hG hX
  obtain ⟨r, gr, hrG, hr, hXr⟩ := M.second X Y hXY pG gG hG hop hY
  have ncr : ¬ IsC n gs X (fixBit gG) (n + 1 + r) :=
    fun h => M.one_const X _ pG r (Ne.symm hrG) gG gr hG hr cG h
  have cr := M.reader_const X r gr hr hXr
  have hfr : fixBit gr = !fixBit gG := by
    by_contra hne
    apply ncr
    have e : fixBit gr = fixBit gG := by
      revert hne
      cases fixBit gr <;> cases fixBit gG <;> simp
    rw [← e]; exact cr
  have cr' : IsC n gs X (!fixBit gG) (n + 1 + r) := by rw [← hfr]; exact cr
  refine ⟨r, gr, hrG, hr, hXr, ?_, cr', hfr, ?_, ?_⟩
  · intro p' g' hp' hx
    by_contra hne
    have h1 : p' ≠ r := fun e => hne (Or.inl e)
    have h2 : p' ≠ pG := fun e => hne (Or.inr e)
    have cp := M.reader_const X p' g' hp' hx
    by_cases e : fixBit g' = fixBit gG
    · rw [e] at cp
      exact M.one_const X _ pG p' (Ne.symm h2) gG g' hG hp' cG cp
    · have e' : fixBit g' = !fixBit gG := by
        revert e
        cases fixBit g' <;> cases fixBit gG <;> simp
      rw [e'] at cp
      exact M.one_const X _ r p' (Ne.symm h1) gr g' hr hp' cr' cp
  · rcases M.hcl r gr hr with ⟨hopn, _⟩ | ⟨h, _⟩
    · exact (M.no_not X r gr hr hopn hXr).elim
    · exact h
  · intro hGr
    obtain ⟨c0, hc0⟩ := cG
    obtain ⟨_, _, w, hw, hwn⟩ := st_shape n gs M.hcl X (fixBit gG) r gr hr (n + 1 + pG) hGr c0 hc0
      (fun c' h => ncr ⟨c', h⟩)
    rcases two_inputs (M.hcl r gr hr) (X : ℕ) (n + 1 + pG) w hXr hGr
      (by have := X.isLt; omega) hw with e | e
    · exact hwn _ (by rw [e]; exact stF_self n gs X _)
    · exact hwn c0 (by rw [e]; exact hc0)
lemma Min.pair_false (M : Min n gs o) (X Y : Fin (n + 1)) (hXY : X ≠ Y) (pG : ℕ) (gG : Gate)
    (hG : gs[pG]? = some gG) (hop : gG.op = GateOp.and ∨ gG.op = GateOp.or)
    (hX : (X : ℕ) ∈ gG.inputs) (hY : (Y : ℕ) ∈ gG.inputs) : False := by
  have hXYn : (X : ℕ) ≠ (Y : ℕ) := fun e => hXY (Fin.ext e)
  obtain ⟨r, gr, hrG, hr, hXr, hRX, crX, hfr, hopr, hGr⟩ := M.side X Y hXY pG gG hG hop hX hY
  obtain ⟨r', gr', hr'G, hr', hYr', hRY, _, _, _, hGr'⟩ :=
    M.side Y X hXY.symm pG gG hG hop hY hX
  have cGX : IsC n gs X (fixBit gG) (n + 1 + pG) := M.reader_const X pG gG hG hX
  have cGY : IsC n gs Y (fixBit gG) (n + 1 + pG) := M.reader_const Y pG gG hG hY
  have hoX : o ≠ (X : ℕ) := fun e => M.out X false false (by rw [e]; exact stF_self n gs X false)
  have hoY : o ≠ (Y : ℕ) := fun e => M.out Y false false (by rw [e]; exact stF_self n gs Y false)
  have hoG : o ≠ n + 1 + pG := fun e => by
    have ⟨c, hc⟩ := cGX
    exact M.out X _ c (by rw [e]; exact hc)
  have hor : o ≠ n + 1 + r := fun e => by
    have ⟨c, hc⟩ := crX
    exact M.out X _ c (by rw [e]; exact hc)
  have hGv : ∀ (Z : Fin (n + 1)) (v : Fin (n + 1) → Bool), (Z : ℕ) ∈ gG.inputs →
      v Z = fixBit gG → vl gs v (n + 1 + pG) = fixBit gG :=
    fun Z v hZ hv => vl_abs gs M.hcl v pG gG hG hop Z hZ (by rw [vl_input gs v Z Z.isLt]; exact hv)
  have hrX : ∀ v : Fin (n + 1) → Bool, v X = fixBit gr → vl gs v (n + 1 + r) = fixBit gr :=
    fun v hv => vl_abs gs M.hcl v r gr hr hopr X hXr (by rw [vl_input gs v X X.isLt]; exact hv)
  have hGin : ∀ w ∈ gG.inputs, w = (X : ℕ) ∨ w = (Y : ℕ) :=
    fun w hw => two_inputs (M.hcl pG gG hG) X Y w hX hY hXYn hw
  have fX : ∀ u : Fin (n + 1) → Bool, u Y = fixBit gG → vl gs u (n + 1 + r) = u X := fun u hu =>
    M.forced X r pG gr hr hXr hRX hoG u (Or.inl (by
      rw [hGv Y _ hY (by rw [Function.update_of_ne hXY.symm]; exact hu), hGv Y u hY hu]))
  have hex1 : ∃ (h1 : ℕ) (g1 : Gate), gs[h1]? = some g1 ∧ (n + 1 + pG) ∈ g1.inputs := by
    by_contra hno
    refine M.m2 r gr hr X (by have := X.isLt; omega) (fun u => ?_)
    rw [vl_input gs u X X.isLt]
    exact M.forced X r pG gr hr hXr hRX hoG u
      (Or.inr (fun p' g' hp' hin => hno ⟨p', g', hp', hin⟩))
  obtain ⟨h1, g1, hg1, hGh1⟩ := hex1
  have h1G : h1 ≠ pG := fun e => by
    have := (M.hcl h1 g1 hg1).lt _ hGh1
    omega
  have h1r : h1 ≠ r := fun e => hGr (gate_eq hg1 hr e ▸ hGh1)
  have h1r' : h1 ≠ r' := fun e => hGr' (gate_eq hg1 hr' e ▸ hGh1)
  by_cases hrr : r = r'
  swap
  · by_cases hrc : RC n gs Y (fixBit gG) r
    · exact M.nf4 Y (fixBit gG) pG r' h1 r (Ne.symm hr'G) (Ne.symm h1G) (Ne.symm hrG)
        (Ne.symm h1r') (Ne.symm hrr) h1r ⟨gG, hG, Y, hY, _, stF_self n gs Y _⟩
        ⟨gr', hr', Y, hYr', _, stF_self n gs Y _⟩ ⟨g1, hg1, _, hGh1, cGY⟩ hrc
    · obtain ⟨q, hnq, hq⟩ := st_fresh n gs M.hcl Y (fixBit gG) r gr hr
        (fun a ha c hc => hrc ⟨gr, hr, a, ha, c, hc⟩)
      obtain ⟨k, hk, hkX⟩ := st_other n gs Y (fixBit gG) X hXY
      refine M.ndup Y (fixBit gG) pG r' h1 (Ne.symm hr'G) (Ne.symm h1G) (Ne.symm h1r')
        ⟨gG, hG, Y, hY, _, stF_self n gs Y _⟩ ⟨gr', hr', Y, hYr', _, stF_self n gs Y _⟩
        ⟨g1, hg1, _, hGh1, cGY⟩ (n + 1 + r) X q k hq hnq hkX (by omega) (fun y => ?_)
      rw [vl_input gs _ X X.isLt]
      exact fX _ (by simp [ins])
  · have hRY' : ∀ p' g', gs[p']? = some g' → (Y : ℕ) ∈ g'.inputs → p' = r ∨ p' = pG := by
      intro p' g' hp' hy
      rw [hrr]; exact hRY p' g' hp' hy
    have hex2 : ∃ (h2 : ℕ) (g2 : Gate), gs[h2]? = some g2 ∧ (n + 1 + r) ∈ g2.inputs := by
      by_contra hno
      refine M.m2 pG gG hG X (by have := X.isLt; omega) (fun u => ?_)
      rw [vl_input gs u X X.isLt]
      exact M.forced X pG r gG hG hX (fun p' g' hp' hx => (hRX p' g' hp' hx).symm) hor u
        (Or.inr (fun p' g' hp' hin => hno ⟨p', g', hp', hin⟩))
    obtain ⟨h2, g2, hg2, hrh2⟩ := hex2
    have hrG' : (n + 1 + r) ∉ gG.inputs := fun h => by
      rcases hGin _ h with e | e
      · have := X.isLt; omega
      · have := Y.isLt; omega
    have h2r : h2 ≠ r := fun e => by
      have := (M.hcl h2 g2 hg2).lt _ hrh2
      omega
    have h2G : h2 ≠ pG := fun e => hrG' (gate_eq hg2 hG e ▸ hrh2)
    have h1u : ∀ p' g', gs[p']? = some g' → (n + 1 + pG) ∈ g'.inputs → p' = h1 := by
      intro p' g' hp' hin
      by_contra hne
      have e1 : p' ≠ pG := fun e => by
        have := (M.hcl p' g' hp').lt _ hin
        omega
      have e2 : p' ≠ r := fun e => hGr (gate_eq hp' hr e ▸ hin)
      exact M.nf4 X (fixBit gG) pG r h1 p' (Ne.symm hrG) (Ne.symm h1G) (Ne.symm e1)
        (Ne.symm h1r) (Ne.symm e2) (Ne.symm hne) ⟨gG, hG, X, hX, _, stF_self n gs X _⟩
        ⟨gr, hr, X, hXr, _, stF_self n gs X _⟩ ⟨g1, hg1, _, hGh1, cGX⟩ ⟨g', hp', _, hin, cGX⟩
    have h2u : ∀ p' g', gs[p']? = some g' → (n + 1 + r) ∈ g'.inputs → p' = h2 := by
      intro p' g' hp' hin
      by_contra hne
      have e1 : p' ≠ pG := fun e => hrG' (gate_eq hp' hG e ▸ hin)
      have e2 : p' ≠ r := fun e => by
        have := (M.hcl p' g' hp').lt _ hin
        omega
      exact M.nf4 X (!fixBit gG) pG r h2 p' (Ne.symm hrG) (Ne.symm h2G) (Ne.symm e1)
        (Ne.symm h2r) (Ne.symm e2) (Ne.symm hne) ⟨gG, hG, X, hX, _, stF_self n gs X _⟩
        ⟨gr, hr, X, hXr, _, stF_self n gs X _⟩ ⟨g2, hg2, _, hrh2, crX⟩ ⟨g', hp', _, hin, crX⟩
    have n1X : ¬ IsC n gs X (fixBit gG) (n + 1 + h1) :=
      fun h => M.one_const X _ pG h1 (Ne.symm h1G) gG g1 hG hg1 cGX h
    have n2X : ¬ IsC n gs X (!fixBit gG) (n + 1 + h2) :=
      fun h => M.one_const X _ r h2 (Ne.symm h2r) gr g2 hr hg2 crX h
    have ⟨cg, hcg⟩ := cGX
    have ⟨cr, hcr⟩ := crX
    obtain ⟨hop1, hf1, w1, hw1, hw1n⟩ := st_shape n gs M.hcl X (fixBit gG) h1 g1 hg1 _ hGh1 cg hcg
      (fun c' h => n1X ⟨c', h⟩)
    obtain ⟨hop2, hf2, w2, hw2, hw2n⟩ := st_shape n gs M.hcl X (!fixBit gG) h2 g2 hg2 _ hrh2 cr
      hcr (fun c' h => n2X ⟨c', h⟩)
    have hcgv : cg = fixBit gG := by
      have h := st_val_const n gs M.hcl X (fixBit gG) (n + 1 + pG) cg hcg (fun _ => false)
      rw [hGv X _ hX (by simp [ins])] at h
      exact h.symm
    have hcrv : cr = fixBit gr := by
      have h := st_val_const n gs M.hcl X (!fixBit gG) (n + 1 + r) cr hcr (fun _ => false)
      rw [hrX _ (by simp [ins, hfr])] at h
      exact h.symm
    have f1 : fixBit g1 = !fixBit gG := by
      rw [hcgv] at hf1
      revert hf1
      cases fixBit g1 <;> cases fixBit gG <;> simp
    have f2 : fixBit g2 = fixBit gG := by
      rw [hcrv, hfr] at hf2
      revert hf2
      cases fixBit g2 <;> cases fixBit gG <;> simp
    have h12 : h1 ≠ h2 := fun e => by
      have e' : g1 = g2 := gate_eq hg1 hg2 e
      rw [e', f2] at f1
      revert f1
      cases fixBit gG <;> simp
    have hr1 : (n + 1 + r) ∉ g1.inputs := fun h => h12 (h2u h1 g1 hg1 h)
    have hG2 : (n + 1 + pG) ∉ g2.inputs := fun h => h12 (h1u h2 g2 hg2 h).symm
    have hX1 : (X : ℕ) ∉ g1.inputs := fun h => (hRX h1 g1 hg1 h).elim h1r h1G
    have hY1 : (Y : ℕ) ∉ g1.inputs := fun h => (hRY' h1 g1 hg1 h).elim h1r h1G
    have hX2 : (X : ℕ) ∉ g2.inputs := fun h => (hRX h2 g2 hg2 h).elim h2r h2G
    have hY2 : (Y : ℕ) ∉ g2.inputs := fun h => (hRY' h2 g2 hg2 h).elim h2r h2G
    have hBw1X : ¬ (w1 = (X : ℕ) ∨ w1 = n + 1 + pG ∨ w1 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hX1 (e ▸ hw1)
      · exact hw1n cg (by rw [e]; exact hcg)
      · exact hr1 (e ▸ hw1)
    have hBw1Y : ¬ (w1 = (Y : ℕ) ∨ w1 = n + 1 + pG ∨ w1 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hY1 (e ▸ hw1)
      · exact hw1n cg (by rw [e]; exact hcg)
      · exact hr1 (e ▸ hw1)
    have hBw2X : ¬ (w2 = (X : ℕ) ∨ w2 = n + 1 + pG ∨ w2 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hX2 (e ▸ hw2)
      · exact hG2 (e ▸ hw2)
      · exact hw2n cr (by rw [e]; exact hcr)
    have hBw2Y : ¬ (w2 = (Y : ℕ) ∨ w2 = n + 1 + pG ∨ w2 = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hY2 (e ▸ hw2)
      · exact hG2 (e ▸ hw2)
      · exact hw2n cr (by rw [e]; exact hcr)
    have hout : ∀ (Z : Fin (n + 1)),
        (∀ p' g', gs[p']? = some g' → (Z : ℕ) ∈ g'.inputs → p' = r ∨ p' = pG) →
        ∀ p' g', gs[p']? = some g' →
          ¬ (n + 1 + p' = (Z : ℕ) ∨ n + 1 + p' = n + 1 + pG ∨ n + 1 + p' = n + 1 + r) →
          (∃ a ∈ g'.inputs, a = (Z : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) →
          p' = h1 ∨ p' = h2 := by
      intro Z hRZ p' g' hp' hB hr
      obtain ⟨a, ha, hBa⟩ := hr
      rcases hBa with e | e | e
      · exfalso
        rcases hRZ p' g' hp' (e ▸ ha) with e' | e'
        · exact hB (Or.inr (Or.inr (by rw [e'])))
        · exact hB (Or.inr (Or.inl (by rw [e'])))
      · exact Or.inl (h1u p' g' hp' (e ▸ ha))
      · exact Or.inr (h2u p' g' hp' (e ▸ ha))
    have hoBY : ¬ (o = (Y : ℕ) ∨ o = n + 1 + pG ∨ o = n + 1 + r) := by
      intro h
      rcases h with e | e | e
      · exact hoY e
      · exact hoG e
      · exact hor e
    have A2 : ∀ u : Fin (n + 1) → Bool, vl gs u w2 = fixBit gG → u X = fixBit gG → False := by
      intro u hv hx
      refine M.block2 Y (fun a => a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl)
        hoBY u h2 h1 g2 g1 hg2 hg1 (fun p' g' hp' hB hr => (hout Y hRY' p' g' hp' hB hr).symm)
        hop2 w2 hw2 hBw2Y (by rw [f2]; exact hv) ?_
      intro a ha hBa
      rcases (hBa : a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) with e | e | e
      · exact absurd (e ▸ ha) hY1
      · rw [e, hGv X _ hX (by rw [Function.update_of_ne hXY]; exact hx), hGv X u hX hx]
      · exact absurd (e ▸ ha) hr1
    have A4 : ∀ u : Fin (n + 1) → Bool, vl gs u w1 = !fixBit gG → u X = !fixBit gG → False := by
      intro u hv hx
      refine M.block2 Y (fun a => a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl)
        hoBY u h1 h2 g1 g2 hg1 hg2 (hout Y hRY') hop1 w1 hw1 hBw1Y (by rw [f1]; exact hv) ?_
      intro a ha hBa
      rcases (hBa : a = (Y : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) with e | e | e
      · exact absurd (e ▸ ha) hY2
      · exact absurd (e ▸ ha) hG2
      · rw [e, hrX _ (by rw [Function.update_of_ne hXY, hfr]; exact hx),
          hrX u (by rw [hfr]; exact hx)]
    have hl1 : h1 < gs.length := (List.getElem?_eq_some_iff.1 hg1).1
    have hl2 : h2 < gs.length := (List.getElem?_eq_some_iff.1 hg2).1
    have hw1lt := (M.hcl h1 g1 hg1).lt w1 hw1
    have hw2lt := (M.hcl h2 g2 hg2).lt w2 hw2
    have lt12 : h1 < h2 := by
      obtain ⟨u, hu⟩ := takes gs M.m1 w2 (by omega) (fixBit gG)
      have hx : u X = !fixBit gG := by
        have h := A2 u hu
        revert h
        cases u X <;> cases fixBit gG <;> simp
      have hne : vl gs (Function.update u X (!u X)) w2 ≠ vl gs u w2 := fun e =>
        A2 _ (by rw [e]; exact hu) (by simp [hx])
      obtain ⟨p', g', hp', hle, hB', hr'⟩ := M.before X
        (fun a => a = (X : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl) u w2 hBw2X hne
      rcases hout X hRX p' g' hp' hB' hr' with e | e
      · rw [e] at hle; omega
      · rw [e] at hle; omega
    have lt21 : h2 < h1 := by
      obtain ⟨u, hu⟩ := takes gs M.m1 w1 (by omega) (!fixBit gG)
      have hx : u X = fixBit gG := by
        have h := A4 u hu
        revert h
        cases u X <;> cases fixBit gG <;> simp
      have hne : vl gs (Function.update u X (!u X)) w1 ≠ vl gs u w1 := fun e =>
        A4 _ (by rw [e]; exact hu) (by simp [hx])
      obtain ⟨p', g', hp', hle, hB', hr'⟩ := M.before X
        (fun a => a = (X : ℕ) ∨ a = n + 1 + pG ∨ a = n + 1 + r) (Or.inl rfl) u w1 hBw1X hne
      rcases hout X hRX p' g' hp' hB' hr' with e | e
      · rw [e] at hle; omega
      · rw [e] at hle; omega
    omega
lemma Min.contra (M : Min n gs o) : False := by
  have hg0 : ∃ g0, gs[0]? = some g0 := by
    cases hgs : gs with
    | nil =>
      exfalso
      obtain ⟨p, g, hp, _⟩ := M.reader 0 (fun a => a = ((0 : Fin (n + 1)) : ℕ)) rfl
        (fun (e : o = ((0 : Fin (n + 1)) : ℕ)) =>
          M.out 0 false false (by rw [e]; exact stF_self n gs 0 false))
      rw [hgs] at hp
      simp at hp
    | cons g _ => exact ⟨g, rfl⟩
  obtain ⟨g0, h0⟩ := hg0
  rcases M.hcl 0 g0 h0 with ⟨hop, j, hj, hin⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · exact M.no_not ⟨j, by omega⟩ 0 g0 h0 hop (by rw [hin]; simp)
  · by_cases hjk : j = k
    · refine M.m2 0 g0 h0 j (by omega) (fun u => ?_)
      rw [vl_gate gs M.hcl u 0 g0 h0, hin, hjk]
      rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval]
    · exact M.pair_false ⟨j, by omega⟩ ⟨k, by omega⟩ (fun e => hjk (congrArg Fin.val e)) 0 g0 h0
        hop (by rw [hin]; simp) (by rw [hin]; simp)
end SourceSection1
lemma par_lower4 : ∀ (n : ℕ) (c : Bool) (s : ℕ),
    HasClean (n + 1) (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) c) s → 4 * n ≤ s := by
  intro n
  induction n with
  | zero => intro c s _; omega
  | succ n ih =>
    intro c s h
    classical
    have hex : ∃ t, HasClean (n + 1 + 1)
        (fun x : Fin (n + 1 + 1) → Bool => xor (par (n + 1 + 1) x) c) t := ⟨s, h⟩
    obtain ⟨gs, o, hcl, hsz, hev⟩ := Nat.find_spec hex
    have hfs : Nat.find hex ≤ s := Nat.find_min' hex h
    have hev' : ∀ x : Fin (n + 1 + 1) → Bool, vl gs x o = xor (par (n + 1 + 1) x) c := hev
    have hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL (n + 1 + 1) gs' →
        (∀ x : Fin (n + 1 + 1) → Bool, vl gs' x o' = xor (par (n + 1 + 1) x) c) →
        gs.length ≤ gs'.length := by
      intro gs' o' hc' he'
      by_contra hlt
      exact Nat.find_min hex (m := gs'.length) (by omega) ⟨gs', o', hc', le_refl _, he'⟩
    suffices 4 * (n + 1) ≤ gs.length by omega
    by_contra hsmall
    have hncf : ∃ y y' : Fin (n + 1 + 1) → Bool, vl gs y o ≠ vl gs y' o := by
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      rw [hev', hev', par_snoc, par_snoc]
      cases par (n + 1) (fun _ => false) <;> cases c <;> simp
    have M : Min (n + 1) gs o :=
      { hcl := hcl
        hdep := by
          intro i u
          rw [hev', hev', par_flip]
          cases par (n + 1 + 1) u <;> cases c <;> simp
        hnc := by
          intro i b
          refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
          rw [hev', hev', par_insertNth, par_insertNth, par_snoc, par_snoc]
          cases par n (fun _ => false) <;> cases b <;> cases c <;> simp
        m1 := by
          intro p g hp c' hall
          have hpl : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
          obtain ⟨gs', o', hc', hl', he'⟩ := drop_const (n + 1 + 1) gs hcl o p c' hpl hall hncf
          have := hmin gs' o' hc' (fun x => by rw [he' x]; exact hev' x)
          omega
        m2 := by
          intro p g hp j hj hall
          have hpl : p < gs.length := (List.getElem?_eq_some_iff.1 hp).1
          obtain ⟨gs', o', hc', hl', he'⟩ :=
            drop_alias (n + 1 + 1) gs hcl o p j hpl hj hall hncf
          have := hmin gs' o' hc' (fun x => by rw [he' x]; exact hev' x)
          omega
        nored := by
          rintro ⟨i, b, gs', o', hc', hl', he'⟩
          have h' : HasClean (n + 1)
              (fun y : Fin (n + 1) → Bool => xor (par (n + 1) y) (xor b c)) gs'.length :=
            ⟨gs', o', hc', le_refl _, fun y => by
              show vl gs' y o' = _
              rw [he' y, hev', par_insertNth, Bool.xor_assoc]⟩
          have := ih _ _ h'
          omega }
    exact M.contra
lemma parity_lower4 : ∀ (n s : ℕ),
    PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool =>
      decide ((Finset.univ.filter fun i : Fin n => x i = true).card % 2 = 1)) s →
    4 * (n - 1) ≤ s := by
  intro n s h
  cases n with
  | zero => omega
  | succ n =>
    have e : (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false)
        = fun x : Fin (n + 1) → Bool =>
          decide ((Finset.univ.filter fun i : Fin (n + 1) => x i = true).card % 2 = 1) := by
      funext x
      simp [par]
    have h' : PEqualNP.MetaComplexity.HasCircuitSize (n + 1)
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) s := by
      rw [e]; exact h
    have hnc : ∃ y y' : Fin (n + 1) → Bool,
        (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y
          ≠ (fun x : Fin (n + 1) → Bool => xor (par (n + 1) x) false) y' := by
      refine ⟨Fin.snoc (fun _ => false) false, Fin.snoc (fun _ => false) true, ?_⟩
      simp only [par_snoc]
      simp
    have := par_lower4 n false s (clean_of (n + 1) _ s hnc h')
    omega
end PEqualNP.Outside.L_meta_3457.SparseLower.Helpers

namespace PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.PermInputs
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
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
lemma rel_step (n m : ℕ) (π : Fin n → Fin m) (W W' : List Bool) (g : Gate)
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
lemma rel_fold (n m : ℕ) (π : Fin n → Fin m) (gs : List Gate) :
    ∀ W W' : List Bool, Rel n m π W W' →
      Rel n m π (gs.foldl step W) ((gs.map (relGate n m π)).foldl step W') := by
  induction gs with
  | nil => intro W W' h; exact h
  | cons g gs ih =>
    intro W W' h
    exact ih _ _ (rel_step n m π W W' g h)
lemma rel_init (n m : ℕ) (π : Fin n → Fin m) (x : Fin m → Bool) :
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
lemma relabel_size {n m : ℕ} (π : Fin n → Fin m) (h : (Fin n → Bool) → Bool) (s : ℕ)
    (hc : PEqualNP.MetaComplexity.HasCircuitSize n h s) : PEqualNP.MetaComplexity.HasCircuitSize m (fun x => h (x ∘ π)) s := by
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
lemma dep_lower_set (n : ℕ) (f : (Fin n → Bool) → Bool) (T : Finset (Fin n))
    (hdep : ∀ i ∈ T, ∃ x : Fin n → Bool, f (Function.update x i (!x i)) ≠ f x)
    (s : ℕ) (h : PEqualNP.MetaComplexity.HasCircuitSize n f s) : T.card ≤ s + 1 := by
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
lemma snoc_swap (n : ℕ) (p : Fin (n + 1)) (x : Fin (n + 1) → Bool) (b : Bool) :
    (Fin.snoc (fun j : Fin n => x (Equiv.swap p (Fin.last n) j.castSucc)) b :
        Fin (n + 1) → Bool) ∘ (Equiv.swap p (Fin.last n))
      = Function.update x p b := by
  funext j
  simp only [Function.comp_apply]
  by_cases hj : j = p
  · subst hj
    rw [Equiv.swap_apply_left, Fin.snoc_last, Function.update_self]
  · have hl : Equiv.swap p (Fin.last n) j ≠ Fin.last n := by
      intro e
      apply hj
      have := congrArg (Equiv.swap p (Fin.last n)) e
      rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at this
    obtain ⟨t, ht⟩ := Fin.exists_castSucc_eq.2 hl
    rw [← ht, Fin.snoc_castSucc, ht, Equiv.swap_apply_self, Function.update_of_ne hj]
lemma gate_elim_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : PEqualNP.MetaComplexity.HasCircuitSize (n + 1) f s) :
    ∃ (b : Bool) (s' : ℕ), s' + 2 ≤ s ∧
      PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s' := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) s := relabel_size (⇑σ) f s h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∀ b : Bool, ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    intro b
    obtain ⟨x, y, hxy⟩ := hnc b
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  obtain ⟨b, s', hs, h'⟩ := gate_elim_two n _ s hdep' hnc' hg
  refine ⟨b, s', hs, ?_⟩
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s' h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''
lemma fix_many {N : ℕ} (T : Finset (Fin N)) (hT : T.Nonempty) :
    ∀ (L : List (Fin N)) (f : (Fin N → Bool) → Bool), L.Nodup → (∀ p ∈ L, p ∉ T) →
    (∀ (a : Fin N → Bool) (pre post : List (Fin N)) (p : Fin N), L = pre ++ p :: post →
      ∃ x : Fin N → Bool, (∀ q ∈ pre, x q = a q) ∧ f (Function.update x p (!x p)) ≠ f x) →
    (∀ (a : Fin N → Bool), ∀ i ∈ T, ∃ x : Fin N → Bool, (∀ q ∈ L, x q = a q) ∧
      f (Function.update x i (!x i)) ≠ f x) →
    ∀ s : ℕ, PEqualNP.MetaComplexity.HasCircuitSize N f s → T.card + 2 * L.length ≤ s + 1 := by
  obtain ⟨i0, hi0⟩ := hT
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by have := i0.2; omega⟩
  intro L
  induction L with
  | nil =>
    intro f _ _ _ hC s h
    have := dep_lower_set (n + 1) f T (fun i hi => by
      obtain ⟨x, _, hx⟩ := hC (fun _ => false) i hi
      exact ⟨x, hx⟩) s h
    simpa using this
  | cons p L ih =>
    intro f hnd hdis hA hC s h
    have hpL : p ∉ L := (List.nodup_cons.1 hnd).1
    have hpT : p ∉ T := hdis p List.mem_cons_self
    have hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x := by
      obtain ⟨x, _, hx⟩ := hA (fun _ => false) [] L p rfl
      exact ⟨x, hx⟩
    have hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
        f (Function.update x p b) ≠ f (Function.update y p b) := by
      intro b
      obtain ⟨x, hxa, hx⟩ := hC (fun _ => b) i0 hi0
      have hxp : x p = b := hxa p List.mem_cons_self
      have hi0p : i0 ≠ p := fun e => hpT (e ▸ hi0)
      refine ⟨Function.update x i0 (!x i0), x, ?_⟩
      have e1 : Function.update (Function.update x i0 (!x i0)) p b
          = Function.update x i0 (!x i0) :=
        Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hi0p), hxp])
      have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
      rw [e1, e2]
      exact hx
    obtain ⟨b, s', hs, h'⟩ := gate_elim_at n f p s hdep hnc h
    have := ih (fun x => f (Function.update x p b)) (List.nodup_cons.1 hnd).2
      (fun q hq => hdis q (List.mem_cons_of_mem _ hq)) ?_ ?_ s' h'
    · simp only [List.length_cons]; omega
    · intro a pre post p' hL
      obtain ⟨x, hxa, hx⟩ := hA (Function.update a p b) (p :: pre) post p' (by rw [hL]; rfl)
      have hxp : x p = b := by
        rw [hxa p List.mem_cons_self, Function.update_self]
      have hp' : p' ≠ p := by
        intro e; apply hpL; rw [← e, hL]; simp
      refine ⟨x, fun q hq => ?_, ?_⟩
      · have hqp : q ≠ p := by
          intro e; apply hpL; rw [← e, hL]; simp [hq]
        rw [hxa q (List.mem_cons_of_mem _ hq), Function.update_of_ne hqp]
      · have e1 : Function.update (Function.update x p' (!x p')) p b
            = Function.update x p' (!x p') :=
          Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hp'), hxp])
        have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
        show f _ ≠ f _
        rw [e1, e2]
        exact hx
    · intro a i hi
      obtain ⟨x, hxa, hx⟩ := hC (Function.update a p b) i hi
      have hxp : x p = b := by
        rw [hxa p List.mem_cons_self, Function.update_self]
      have hip : i ≠ p := fun e => hpT (e ▸ hi)
      refine ⟨x, fun q hq => ?_, ?_⟩
      · have hqp : q ≠ p := fun e => hpL (e ▸ hq)
        rw [hxa q (List.mem_cons_of_mem _ hq), Function.update_of_ne hqp]
      · have e1 : Function.update (Function.update x i (!x i)) p b
            = Function.update x i (!x i) :=
          Function.update_eq_self_iff.2 (by rw [Function.update_of_ne (Ne.symm hip), hxp])
        have e2 : Function.update x p b = x := Function.update_eq_self_iff.2 hxp.symm
        show f _ ≠ f _
        rw [e1, e2]
        exact hx
end PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.PermInputs

namespace PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Forest
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.PermInputs
lemma one_gate_at (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (p : Fin (n + 1)) (b : Bool)
    (s : ℕ)
    (hdep : ∃ x : Fin (n + 1) → Bool, f (Function.update x p (!x p)) ≠ f x)
    (hnc : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x p b) ≠ f (Function.update y p b))
    (h : PEqualNP.MetaComplexity.HasCircuitSize (n + 1) f (s + 1)) :
    PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x => f (Function.update x p b)) s := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap p (Fin.last n) with hσ
  have hg : PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x => f (x ∘ σ)) (s + 1) := relabel_size (⇑σ) f _ h
  have hss : ∀ x : Fin (n + 1) → Bool, (x ∘ σ) ∘ σ = x := by
    intro x; funext j; simp [hσ, Equiv.swap_apply_self]
  have hsl : σ.symm (Fin.last n) = p := by
    rw [hσ, Equiv.symm_swap, Equiv.swap_apply_right]
  have hdep' : ∃ x : Fin (n + 1) → Bool,
      (fun x => f (x ∘ σ)) (Function.update x (Fin.last n) (!x (Fin.last n)))
        ≠ (fun x => f (x ∘ σ)) x := by
    obtain ⟨x0, hx0⟩ := hdep
    refine ⟨x0 ∘ σ, ?_⟩
    simp only
    rw [Function.update_comp_equiv, hsl, hss]
    have : (x0 ∘ ⇑σ) (Fin.last n) = x0 p := by
      simp [hσ, Equiv.swap_apply_right]
    rw [this]
    exact hx0
  have hnc' : ∃ y y' : Fin n → Bool,
      (fun x => f (x ∘ σ)) (Fin.snoc y b) ≠ (fun x => f (x ∘ σ)) (Fin.snoc y' b) := by
    obtain ⟨x, y, hxy⟩ := hnc
    refine ⟨fun j => x (σ j.castSucc), fun j => y (σ j.castSucc), ?_⟩
    simp only
    rw [snoc_swap, snoc_swap]
    exact hxy
  have h' := PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.gate_elim n _ b s hdep' hnc' hg
  have h'' := relabel_size (fun j : Fin n => σ j.castSucc) _ s h'
  have e : (fun x : Fin (n + 1) → Bool =>
      (fun y : Fin n → Bool => (fun x => f (x ∘ σ)) (Fin.snoc y b))
        (x ∘ fun j : Fin n => σ j.castSucc))
      = fun x => f (Function.update x p b) := by
    funext x
    simp only
    exact congrArg f (snoc_swap n p x b)
  rw [e] at h''
  exact h''
end PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Forest

namespace PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
open PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.PermInputs
def Dep {m : ℕ} (f : (Fin m → Bool) → Bool) (p : Fin m) : Prop :=
  ∃ x : Fin m → Bool, f (Function.update x p (!x p)) ≠ f x
abbrev set2 {m : ℕ} (x : Fin m → Bool) (p : Fin m) (a : Bool) (q : Fin m) (b : Bool) :
    Fin m → Bool :=
  Function.update (Function.update x p a) q b
def PairFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) (p q : Fin m) : Prop :=
  ∃ a b : Bool, ∀ x : Fin m → Bool,
    f (set2 x p (!a) q b) = f (set2 x p a q (!b)) ∧
    f (set2 x p a q (!b)) = f (set2 x p (!a) q (!b))
def Drop {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (b : Bool) (k s : ℕ) : Prop :=
  ∃ s' : ℕ, s' + k ≤ s ∧ PEqualNP.MetaComplexity.HasCircuitSize m (fun x => f (Function.update x y b)) s'
def Pays {m : ℕ} (f : (Fin m → Bool) → Bool) (y : Fin m) (s : ℕ) : Prop :=
  (Drop f y false 3 s ∧ Drop f y true 3 s) ∨ (Drop f y false 4 s ∧ Drop f y true 2 s) ∨
    (Drop f y false 2 s ∧ Drop f y true 4 s)
def RestrNC {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p : Fin m, Dep f p → ∀ b : Bool, ∃ x y : Fin m → Bool,
    f (Function.update x p b) ≠ f (Function.update y p b)
def NoFunnel {m : ℕ} (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ p q : Fin m, p ≠ q → Dep f p → Dep f q → ¬ PairFunnel f p q
structure Least (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop where
  hcl : CleanL m gs
  hev : ∀ x : Fin m → Bool, vl gs x o = f x
  hmin : ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → (∀ x : Fin m → Bool, vl gs' x o' = f x) →
    gs.length ≤ gs'.length
def Reads (gs : List Gate) (p w : ℕ) : Prop := ∃ g, gs[p]? = some g ∧ w ∈ g.inputs
lemma dep_nc {m : ℕ} {f : (Fin m → Bool) → Bool} {p : Fin m} (h : Dep f p) :
    ∃ x y : Fin m → Bool, f x ≠ f y := by
  obtain ⟨x, hx⟩ := h
  exact ⟨_, _, hx⟩
lemma Drop.mono {m : ℕ} {f : (Fin m → Bool) → Bool} {y : Fin m} {b : Bool} {k s k' s' : ℕ}
    (h : Drop f y b k s) (hk : k' ≤ k) (hs : s ≤ s') : Drop f y b k' s' := by
  obtain ⟨t, ht, hc⟩ := h
  exact ⟨t, by omega, hc⟩
lemma has_of_clean (k : ℕ) (gs : List Gate) (o : ℕ) (hcl : CleanL k gs) :
    PEqualNP.MetaComplexity.HasCircuitSize k (fun y => vl gs y o) gs.length := by
  refine ⟨⟨gs, o⟩, ?_, le_refl _, fun y => rfl⟩
  intro g hg
  exact (clean_nok k gs hcl g hg).1
lemma reads_lt {k : ℕ} {gs : List Gate} (hcl : CleanL k gs) {q w : ℕ} (h : Reads gs q w) :
    w < k + q := by
  obtain ⟨g, hg, hw⟩ := h
  exact (hcl q g hg).lt w hw
lemma reads_len {gs : List Gate} {q w : ℕ} (h : Reads gs q w) : q < gs.length := by
  obtain ⟨g, hg, _⟩ := h
  exact (List.getElem?_eq_some_iff.1 hg).1
lemma vl_beyond {k : ℕ} (gs : List Gate) (u : Fin k → Bool) (w : ℕ) (h : k + gs.length ≤ w) :
    vl gs u w = false := by
  unfold vl
  exact List.getD_eq_default _ _ (by rw [length_wiresFrom]; simp; omega)
lemma vl_not {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (u : Fin k → Bool) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (j : ℕ) (hop : g.op = GateOp.not) (hin : g.inputs = [j]) :
    vl gs u (k + q) = !vl gs u j := by
  rw [vl_gate gs hcl u q g hq, hop, hin]
  rfl
lemma exists_least (m : ℕ) (f : (Fin m → Bool) → Bool) (s : ℕ)
    (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (h : PEqualNP.MetaComplexity.HasCircuitSize m f s) :
    ∃ (gs : List Gate) (o : ℕ), Least m f gs o ∧ gs.length ≤ s := by
  classical
  have hc := clean_of m f s hnc h
  have hex : ∃ t, HasClean m f t := ⟨s, hc⟩
  obtain ⟨gs, o, hcl, hsz, hev⟩ := Nat.find_spec hex
  have hfs : Nat.find hex ≤ s := Nat.find_min' hex hc
  refine ⟨gs, o, ⟨hcl, hev, ?_⟩, by omega⟩
  intro gs' o' hc' he'
  have := Nat.find_min' hex ⟨gs', o', hc', le_refl _, he'⟩
  omega
lemma drop_dead (k : ℕ) (gs : List Gate) (hcl : CleanL k gs) (o p : ℕ) (hp : p < gs.length)
    (ho : o ≠ k + p) (hno : ∀ q, ¬ Reads gs q (k + p))
    (hnc : ∃ y y' : Fin k → Bool, vl gs y o ≠ vl gs y' o) :
    ∃ gs' o', CleanL k gs' ∧ gs'.length + 1 ≤ gs.length ∧
      ∀ y : Fin k → Bool, vl gs' y o' = vl gs y o := by
  obtain ⟨g, hg⟩ : ∃ g, gs[p]? = some g := ⟨gs[p], List.getElem?_eq_getElem hp⟩
  have hpos : 0 < k + p := by
    rcases hcl p g hg with ⟨_, j, hj, _⟩ | ⟨_, j, _, hj, _, _⟩ <;> omega
  let g0 : Gate := ⟨GateOp.and, [0, 0]⟩
  let gs' := gs.set p g0
  have hlen : gs'.length = gs.length := by simp [gs']
  have hget_p : gs'[p]? = some g0 := by simp [gs', hp]
  have hget_ne : ∀ r, r ≠ p → gs'[r]? = gs[r]? := by
    intro r hr
    simp [gs', Ne.symm hr]
  have hcl' : CleanL k gs' := by
    intro r g' hr'
    by_cases hrp : r = p
    · subst hrp
      rw [hget_p] at hr'
      cases hr'
      exact Or.inr ⟨Or.inl rfl, 0, 0, hpos, hpos, rfl⟩
    · rw [hget_ne r hrp] at hr'
      exact hcl r g' hr'
  have hagree : ∀ y : Fin k → Bool, ∀ w, w ≠ k + p → vl gs' y w = vl gs y w := by
    intro y w
    induction w using Nat.strong_induction_on with
    | _ w ih =>
      intro hw
      by_cases hwk : w < k
      · rw [vl_input gs' y w hwk, vl_input gs y w hwk]
      · obtain ⟨r, rfl⟩ : ∃ r, w = k + r := ⟨w - k, by omega⟩
        have hrp : r ≠ p := fun e => hw (by rw [e])
        cases hr : gs[r]? with
        | none =>
          have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
          rw [vl_beyond gs' y _ (by omega), vl_beyond gs y _ (by omega)]
        | some g' =>
          have hr' : gs'[r]? = some g' := by rw [hget_ne r hrp]; exact hr
          rw [vl_gate gs' hcl' y r g' hr', vl_gate gs hcl y r g' hr]
          congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hno r ⟨g', hr, e ▸ ha⟩)
  have halias : ∀ y : Fin k → Bool, vl gs' y (k + p) = vl gs' y 0 := by
    intro y
    rw [vl_gate gs' hcl' y p g0 hget_p]
    simp [g0, GateOp.eval]
  have hnc' : ∃ y y' : Fin k → Bool, vl gs' y o ≠ vl gs' y' o := by
    obtain ⟨y, y', h⟩ := hnc
    exact ⟨y, y', by rw [hagree y o ho, hagree y' o ho]; exact h⟩
  obtain ⟨gs'', o'', hc'', hl'', he''⟩ :=
    drop_alias k gs' hcl' o p 0 (by omega) hpos halias hnc'
  exact ⟨gs'', o'', hc'', by omega, fun y => by rw [he'' y, hagree y o ho]⟩
section SourceSection2
variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
lemma Least.ncv (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) :
    ∃ y y' : Fin m → Bool, vl gs y o ≠ vl gs y' o := by
  obtain ⟨x, y, h⟩ := hnc
  exact ⟨x, y, by rw [L.hev, L.hev]; exact h⟩
lemma Least.lower (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (s : ℕ)
    (h : PEqualNP.MetaComplexity.HasCircuitSize m f s) : gs.length ≤ s := by
  obtain ⟨gs', o', hc', hl', he'⟩ := clean_of m f s hnc h
  have := L.hmin gs' o' hc' he'
  omega
lemma Least.no_const (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (c : Bool) : ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = c := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_const m gs L.hcl o p c hp hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega
lemma Least.no_alias (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (j : ℕ) (hj : j < m + p) :
    ¬ ∀ u : Fin m → Bool, vl gs u (m + p) = vl gs u j := by
  intro hall
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_alias m gs L.hcl o p j hp hj hall (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega
lemma Least.live (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p : ℕ)
    (hp : p < gs.length) (ho : o ≠ m + p) : ∃ q, p < q ∧ Reads gs q (m + p) := by
  by_contra hno
  have hno' : ∀ q, ¬ Reads gs q (m + p) := by
    intro q hq
    by_cases hpq : p < q
    · exact hno ⟨q, hpq, hq⟩
    · have := reads_lt L.hcl hq
      omega
  obtain ⟨gs', o', hc', hl', he'⟩ := drop_dead m gs L.hcl o p hp ho hno' (L.ncv hnc)
  have := L.hmin gs' o' hc' (fun x => by rw [he' x]; exact L.hev x)
  omega
lemma Least.dep_read (L : Least m f gs o) (i : Fin m) (hd : Dep f i)
    (hnc : ∀ b : Bool, ∃ x y : Fin m → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b)) : ∃ q, Reads gs q i := by
  by_contra hno
  have hno' : ∀ g ∈ gs, (i : ℕ) ∉ g.inputs := by
    intro g hg hi
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno ⟨q, g, hq, hi⟩
  have hoi : o ≠ i := by
    intro e
    obtain ⟨x, y, hxy⟩ := hnc false
    apply hxy
    rw [← L.hev, ← L.hev, e, vl_input gs _ i i.isLt, vl_input gs _ i i.isLt]
    simp
  obtain ⟨x, hx⟩ := hd
  apply hx
  rw [← L.hev, ← L.hev]
  refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjm : j < m
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
        = Function.update x i (!x i) ⟨j, hjm⟩ from getD_ofFn m _ false ⟨j, hjm⟩,
      show (List.ofFn x).getD j false = x ⟨j, hjm⟩ from getD_ofFn m x false ⟨j, hjm⟩]
    exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
end SourceSection2
lemma upd_ins {n : ℕ} (i : Fin (n + 1)) (b : Bool) (x : Fin (n + 1) → Bool) :
    Function.update x i b = ins i b (Fin.removeNth i x) :=
  (Fin.insertNth_removeNth i b x).symm
lemma restr_const {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b c : Bool) (h : stF n gs i b o = Stat.const c) (x : Fin (n + 1) → Bool) :
    f (Function.update x i b) = c := by
  rw [upd_ins, ← hev]
  exact st_val_const n gs hcl i b o c h _
lemma save (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o : ℕ)
    (hcl : CleanL (n + 1) gs) (hev : ∀ x : Fin (n + 1) → Bool, vl gs x o = f x)
    (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length := by
  have hL : (statAt n i b, ([] : List Gate)).1.length = n + 1 := statAt_length n i b
  have hcount := elim_count n (statAt n i b, []) gs (clean_nok _ gs hcl) S (by
    intro p hp
    obtain ⟨g, hg, a, ha, c, hc⟩ := hS p hp
    refine ⟨g, hg, a, ha, ?_, c, hc⟩
    rw [hL]
    exact (hcl p g hg).lt a ha)
  simp only [List.length_nil, zero_add] at hcount
  cases hst : stF n gs i b o with
  | const c =>
    exfalso
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy ((restr_const hcl hev i b c hst x).trans (restr_const hcl hev i b c hst y).symm)
  | wire j =>
    have hc : CleanL n (passG n gs i b) :=
      clean_elim n (List.ofFn fun _ : Fin n => false) (by simp) gs _ _
        (fun g hg => (clean_nok _ gs hcl g hg).1) (inv_at n i b _) (by intro p g hp; simp at hp)
    have h2 := relabel_size (Fin.succAbove i) _ _ (has_of_clean n (passG n gs i b) j hc)
    have e : (fun x : Fin (n + 1) → Bool => f (Function.update x i b))
        = fun x => vl (passG n gs i b) (x ∘ Fin.succAbove i) j := by
      funext x
      rw [upd_ins, ← hev, st_val_wire n gs hcl i b o j hst]
      rfl
    refine ⟨(passG n gs i b).length, hcount, ?_⟩
    rw [e]
    exact h2
section SourceSection3
variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
lemma Least.save (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (S : Finset ℕ) (hS : ∀ p ∈ S, RC n gs i b p) : Drop f i b S.card gs.length :=
  PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Readers.save n f gs o L.hcl L.hev i b hnc S hS
lemma Least.save2 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 : ℕ) (h12 : p1 ≠ p2) (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) :
    Drop f i b 2 gs.length := by
  have := L.save i b hnc {p1, p2} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl <;> assumption)
  rwa [Finset.card_pair h12] at this
lemma Least.save3 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h23 : p2 ≠ p3)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) :
    Drop f i b 3 gs.length := by
  have := L.save i b hnc {p1, p2, p3} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl <;> assumption)
  rwa [Finset.card_eq_three.2 ⟨p1, p2, p3, h12, h13, h23, rfl⟩] at this
lemma Least.save4 (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p1 p2 p3 p4 : ℕ) (h12 : p1 ≠ p2) (h13 : p1 ≠ p3) (h14 : p1 ≠ p4)
    (h23 : p2 ≠ p3) (h24 : p2 ≠ p4) (h34 : p3 ≠ p4)
    (h1 : RC n gs i b p1) (h2 : RC n gs i b p2) (h3 : RC n gs i b p3) (h4 : RC n gs i b p4) :
    Drop f i b 4 gs.length := by
  have := L.save i b hnc {p1, p2, p3, p4} (by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl | rfl | rfl <;> assumption)
  have hcard : ({p1, p2, p3, p4} : Finset ℕ).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [h12, h13, h14]),
      Finset.card_eq_three.2 ⟨p2, p3, p4, h23, h24, h34, rfl⟩]
  rwa [hcard] at this
lemma rc_input {gs : List Gate} {q : ℕ} {i : Fin (n + 1)} (b : Bool) (h : Reads gs q i) :
    RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  exact ⟨g, hg, i, hin, b, stF_self n gs i b⟩
lemma rc_of_reads {gs : List Gate} {q w : ℕ} {i : Fin (n + 1)} {b : Bool} (h : Reads gs q w)
    (hc : IsC n gs i b w) : RC n gs i b q := by
  obtain ⟨g, hg, hin⟩ := h
  obtain ⟨c, hc⟩ := hc
  exact ⟨g, hg, w, hin, c, hc⟩
lemma Least.read_dep (L : Least (n + 1) f gs o) (hnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (i : Fin (n + 1)) (q : ℕ) (hq : Reads gs q i) : Dep f i := by
  by_contra hnd
  have hnd' : ∀ x : Fin (n + 1) → Bool, f (Function.update x i (!x i)) = f x := by
    intro x
    by_contra h
    exact hnd ⟨x, h⟩
  have hfix : ∀ x : Fin (n + 1) → Bool, f (Function.update x i false) = f x := by
    intro x
    by_cases hx : x i = false
    · have e : Function.update x i false = x := by
        rw [← hx]
        exact Function.update_eq_self i x
      rw [e]
    · have e : (!x i) = false := by simpa using hx
      have := hnd' x
      rwa [e] at this
  have hnc' : ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i false) ≠ f (Function.update y i false) := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨x, y, by rw [hfix, hfix]; exact h⟩
  obtain ⟨s', hs', hc⟩ := L.save i false hnc' {q} (by
    intro p hp
    rw [Finset.mem_singleton] at hp
    subst hp
    exact rc_input false hq)
  rw [Finset.card_singleton] at hs'
  have e : (fun x : Fin (n + 1) → Bool => f (Function.update x i false)) = f := funext hfix
  rw [e] at hc
  have := L.lower hnc s' hc
  omega
lemma Least.next (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p : ℕ) (hp : p < gs.length) (hc : IsC n gs i b (n + 1 + p)) :
    ∃ q, p < q ∧ Reads gs q (n + 1 + p) ∧ RC n gs i b q := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  have ho : o ≠ n + 1 + p := by
    intro e
    obtain ⟨c, hc'⟩ := hc
    obtain ⟨x, y, hxy⟩ := hnc
    rw [← e] at hc'
    exact hxy ((restr_const L.hcl L.hev i b c hc' x).trans (restr_const L.hcl L.hev i b c hc' y).symm)
  obtain ⟨q, hpq, hr⟩ := L.live hfnc p hp ho
  exact ⟨q, hpq, hr, rc_of_reads hr hc⟩
end SourceSection3
end PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Readers

namespace PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
lemma gate_cases {k : ℕ} (gs : List Gate) (hcl : CleanL k gs) (q : ℕ) (g : Gate)
    (hq : gs[q]? = some g) (a : ℕ) (ha : a ∈ g.inputs) :
    (g.op = GateOp.not ∧ g.inputs = [a] ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = !vl gs u a) ∨
    ∃ w, (g.inputs = [a, w] ∨ g.inputs = [w, a]) ∧
      ((g.op = GateOp.and ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a && vl gs u w)) ∨
       (g.op = GateOp.or ∧ ∀ u : Fin k → Bool, vl gs u (k + q) = (vl gs u a || vl gs u w))) := by
  rcases hcl q g hq with ⟨hop, j, _, hin⟩ | ⟨hop, j, j', _, _, hin⟩
  · left
    have e : a = j := by rw [hin] at ha; simpa using ha
    subst e
    exact ⟨hop, hin, fun u => vl_not gs hcl u q g hq a hop hin⟩
  · right
    have e : a = j ∨ a = j' := by rw [hin] at ha; simpa using ha
    rcases e with e | e
    · subst e
      refine ⟨j', Or.inl hin, ?_⟩
      rcases hop with hop | hop
      · exact Or.inl ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
      · exact Or.inr ⟨hop, fun u => by rw [vl_gate gs hcl u q g hq, hop, hin]; simp [GateOp.eval]⟩
    · subst e
      refine ⟨j, Or.inr hin, ?_⟩
      rcases hop with hop | hop
      · refine Or.inl ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
          Bool.and_true]
        exact Bool.and_comm _ _
      · refine Or.inr ⟨hop, fun u => ?_⟩
        rw [vl_gate gs hcl u q g hq, hop, hin]
        simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
          Bool.or_false]
        exact Bool.or_comm _ _
section SourceSection4
variable {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
lemma Least.no_tri (L : Least m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (p q a : ℕ)
    (hpa : Reads gs p a) (hqa : Reads gs q a) (hqp : Reads gs q (m + p)) : False := by
  obtain ⟨gp, hgp, hap⟩ := hpa
  obtain ⟨gq, hgq, haq⟩ := hqa
  obtain ⟨gq', hgq', hpq⟩ := hqp
  have e : gq' = gq := by rw [hgq] at hgq'; exact (Option.some.inj hgq').symm
  subst e
  have hlt_a : a < m + p := (L.hcl p gp hgp).lt a hap
  have hlt_p : m + p < m + q := (L.hcl q gq' hgq).lt _ hpq
  have hqlen : q < gs.length := (List.getElem?_eq_some_iff.1 hgq).1
  rcases gate_cases gs L.hcl q gq' hgq a haq with ⟨_, hin, _⟩ | ⟨w, hin, hq⟩
  · rw [hin] at hpq
    simp at hpq
    omega
  · have hw : w = m + p := by
      rcases hin with hin | hin <;> rw [hin] at hpq <;> simp at hpq <;> omega
    subst hw
    rcases gate_cases gs L.hcl p gp hgp a hap with ⟨_, _, hp⟩ | ⟨w', _, hp⟩
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩
      · exact L.no_const hnc q hqlen false (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
      · exact L.no_const hnc q hqlen true (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> rfl)
    · rcases hq with ⟨_, hq⟩ | ⟨_, hq⟩ <;> rcases hp with ⟨_, hp⟩ | ⟨_, hp⟩
      · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen a (by omega) (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
      · exact L.no_alias hnc q hqlen (m + p) hlt_p (fun u => by
          rw [hq u, hp u]; cases vl gs u a <;> cases vl gs u w' <;> rfl)
end SourceSection4
section SourceSection5
variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
lemma isC_reader (hcl : CleanL (n + 1) gs) (i : Fin (n + 1)) (p : ℕ) (gp : Gate)
    (hgp : gs[p]? = some gp) (hip : (i : ℕ) ∈ gp.inputs) (b : Bool)
    (h : gp.op = GateOp.not ∨ b = fixBit gp) : IsC n gs i b (n + 1 + p) := by
  rcases h with h | rfl
  · apply st_allconst n gs hcl i b p gp hgp
    intro a ha
    rcases hcl p gp hgp with ⟨_, j, _, hin⟩ | ⟨hop, _⟩
    · rw [hin] at ha hip
      simp at ha hip
      rw [ha, ← hip]
      exact ⟨b, stF_self n gs i b⟩
    · rcases hop with hop | hop <;> rw [hop] at h <;> cases h
  · exact const_read n gs hcl i _ p gp hgp i hip (stF_self n gs i _)
lemma Least.third (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i)
    (hc : IsC n gs i b (n + 1 + p)) : Drop f i b 3 gs.length := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  obtain ⟨J, hJp, hJr, hJrc⟩ := L.next i b hnc p (reads_len hp) hc
  have hJq : J ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p J i hp hq hJr
  exact L.save3 i b hnc p q J hpq (by omega) (Ne.symm hJq) (rc_input b hp) (rc_input b hq) hJrc
lemma Least.fourth (L : Least (n + 1) f gs o) (i : Fin (n + 1)) (b : Bool)
    (hnc : ∃ x y : Fin (n + 1) → Bool, f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i)
    (hcp : IsC n gs i b (n + 1 + p)) (hcq : IsC n gs i b (n + 1 + q)) :
    Drop f i b 4 gs.length := by
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨x, y, h⟩ := hnc
    exact ⟨_, _, h⟩
  obtain ⟨J1, h1p, h1r, h1rc⟩ := L.next i b hnc p (reads_len hp) hcp
  obtain ⟨J2, h2q, h2r, h2rc⟩ := L.next i b hnc q (reads_len hq) hcq
  have h1q : J1 ≠ q := by
    rintro rfl
    exact L.no_tri hfnc p J1 i hp hq h1r
  have h2p : J2 ≠ p := by
    rintro rfl
    exact L.no_tri hfnc q J2 i hq hp h2r
  by_cases h12 : J1 = J2
  · have h2r' : Reads gs J1 (n + 1 + q) := by rw [h12]; exact h2r
    have h2q' : q < J1 := by rw [h12]; exact h2q
    obtain ⟨gJ, hgJ, hinp⟩ := h1r
    obtain ⟨gJ', hgJ', hinq⟩ := h2r'
    have e : gJ' = gJ := gate_eq hgJ' hgJ rfl
    subst e
    have hcJ : IsC n gs i b (n + 1 + J1) := st_allconst n gs L.hcl i b J1 gJ' hgJ (fun a ha => by
      rcases two_inputs (L.hcl J1 gJ' hgJ) (n + 1 + p) (n + 1 + q) a hinp hinq (by omega) ha
        with e | e
      · rw [e]; exact hcp
      · rw [e]; exact hcq)
    obtain ⟨K, hKJ, _, hKrc⟩ := L.next i b hnc J1 (List.getElem?_eq_some_iff.1 hgJ).1 hcJ
    exact L.save4 i b hnc p q J1 K hpq (by omega) (by omega) (Ne.symm h1q) (by omega) (by omega)
      (rc_input b hp) (rc_input b hq) h1rc hKrc
  · exact L.save4 i b hnc p q J1 J2 hpq (by omega) (Ne.symm h2p) (Ne.symm h1q) (by omega) h12
      (rc_input b hp) (rc_input b hq) h1rc h2rc
lemma Least.two_readers (L : Least (n + 1) f gs o) (i : Fin (n + 1))
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p i) (hq : Reads gs q i) : Pays f i gs.length := by
  obtain ⟨gp, hgp, hip⟩ := hp
  obtain ⟨gq, hgq, hiq⟩ := hq
  have hp : Reads gs p i := ⟨gp, hgp, hip⟩
  have hq : Reads gs q i := ⟨gq, hgq, hiq⟩
  have cp := isC_reader L.hcl i p gp hgp hip
  have cq := isC_reader L.hcl i q gq hgq hiq
  by_cases hnp : gp.op = GateOp.not
  · exact Or.inl ⟨L.third i false (hnc false) p q hpq hp hq (cp false (Or.inl hnp)),
      L.third i true (hnc true) p q hpq hp hq (cp true (Or.inl hnp))⟩
  by_cases hnq : gq.op = GateOp.not
  · exact Or.inl ⟨L.third i false (hnc false) q p (Ne.symm hpq) hq hp (cq false (Or.inl hnq)),
      L.third i true (hnc true) q p (Ne.symm hpq) hq hp (cq true (Or.inl hnq))⟩
  by_cases hfb : fixBit gp = fixBit gq
  · cases hc : fixBit gp
    · exact Or.inr (Or.inl ⟨L.fourth i false (hnc false) p q hpq hp hq
        (cp false (Or.inr hc.symm)) (cq false (Or.inr (by rw [← hfb, hc]))),
        L.save2 i true (hnc true) p q hpq (rc_input true hp) (rc_input true hq)⟩)
    · exact Or.inr (Or.inr ⟨L.save2 i false (hnc false) p q hpq (rc_input false hp)
        (rc_input false hq), L.fourth i true (hnc true) p q hpq hp hq
        (cp true (Or.inr hc.symm)) (cq true (Or.inr (by rw [← hfb, hc])))⟩)
  · have key : ∀ b, Drop f i b 3 gs.length := by
      intro b
      by_cases hb : b = fixBit gp
      · exact L.third i b (hnc b) p q hpq hp hq (cp b (Or.inr hb))
      · have hb' : b = fixBit gq := by
          revert hb hfb
          cases b <;> cases fixBit gp <;> cases fixBit gq <;> simp
        exact L.third i b (hnc b) q p (Ne.symm hpq) hq hp (cq b (Or.inr hb'))
    exact Or.inl ⟨key false, key true⟩
lemma Least.not_two_readers (L : Least (n + 1) f gs o) (i : Fin (n + 1))
    (hnc : ∀ b : Bool, ∃ x y : Fin (n + 1) → Bool,
      f (Function.update x i b) ≠ f (Function.update y i b))
    (r : ℕ) (g : Gate) (hr : gs[r]? = some g) (hop : g.op = GateOp.not)
    (hin : (i : ℕ) ∈ g.inputs) (p q : ℕ) (hpq : p ≠ q) (hp : Reads gs p (n + 1 + r))
    (hq : Reads gs q (n + 1 + r)) : Drop f i false 3 gs.length ∧ Drop f i true 3 gs.length := by
  have key : ∀ b, Drop f i b 3 gs.length := by
    intro b
    have hc := isC_reader L.hcl i r g hr hin b (Or.inl hop)
    have hpr := reads_lt L.hcl hp
    have hqr := reads_lt L.hcl hq
    exact L.save3 i b (hnc b) r p q (by omega) (by omega) hpq (rc_input b ⟨g, hr, hin⟩)
      (rc_of_reads hp hc) (rc_of_reads hq hc)
  exact ⟨key false, key true⟩
end SourceSection5
end PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Readers

namespace PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
lemma lit_contra {m : ℕ} {f : (Fin m → Bool) → Bool} (hnc : RestrNC f) (v : Fin m) (c : Bool)
    (h : ∀ u, f u = xor (u v) c) : False := by
  have hd : Dep f v := ⟨fun _ => false, by rw [h, h]; cases c <;> simp⟩
  obtain ⟨x, y, hxy⟩ := hnc v hd false
  apply hxy
  rw [h, h]
  simp
lemma set2_p {m : ℕ} (x : Fin m → Bool) {p q : Fin m} (h : p ≠ q) (a b : Bool) :
    set2 x p a q b p = a := by
  simp [set2, Function.update_of_ne h]
lemma set2_q {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) :
    set2 x p a q b q = b := by
  simp [set2]
lemma set2_o {m : ℕ} (x : Fin m → Bool) (p q : Fin m) (a b : Bool) (i : Fin m) (hp : i ≠ p)
    (hq : i ≠ q) : set2 x p a q b i = x i := by
  simp [set2, Function.update_of_ne hp, Function.update_of_ne hq]
section SourceSection6
variable {n : ℕ} {f : (Fin (n + 1) → Bool) → Bool} {gs : List Gate} {o : ℕ}
lemma Least.not_input (L : Least (n + 1) f gs o) (hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (t : ℕ) (ht : ∀ r < t, ∀ g, gs[r]? = some g → g.op = GateOp.not) (r : ℕ) (hr : r < t)
    (g : Gate) (hg : gs[r]? = some g) : ∃ v : Fin (n + 1), g.inputs = [(v : ℕ)] := by
  rcases L.hcl r g hg with ⟨hop, j, hj, hin⟩ | ⟨hop, _⟩
  · by_cases hjn : j < n + 1
    · exact ⟨⟨j, hjn⟩, hin⟩
    · exfalso
      obtain ⟨r', rfl⟩ : ∃ r', j = n + 1 + r' := ⟨j - (n + 1), by omega⟩
      have hrl : r < gs.length := (List.getElem?_eq_some_iff.1 hg).1
      obtain ⟨g', hg'⟩ : ∃ g', gs[r']? = some g' :=
        ⟨gs[r'], List.getElem?_eq_getElem (by omega)⟩
      have hop' := ht r' (by omega) g' hg'
      rcases L.hcl r' g' hg' with ⟨_, j', hj', hin'⟩ | ⟨hop2, _⟩
      · exact L.no_alias hfnc r hrl j' (by omega) (fun u => by
          rw [vl_not gs L.hcl u r g hg _ hop hin, vl_not gs L.hcl u r' g' hg' _ hop' hin']
          simp)
      · rcases hop2 with h | h <;> rw [h] at hop' <;> cases hop'
  · rcases hop with h | h <;> rw [ht r hr g hg] at h <;> cases h
lemma Least.lit_wire (L : Least (n + 1) f gs o) (hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y)
    (t : ℕ) (ht : ∀ r < t, ∀ g, gs[r]? = some g → g.op = GateOp.not) (w : ℕ)
    (hw : w < n + 1 + t) (hwl : w < n + 1 + gs.length) :
    ∃ (v : Fin (n + 1)) (c : Bool), (∀ u, vl gs u w = xor (u v) c) ∧
      (w = v ∨ ∃ r g, r < t ∧ w = n + 1 + r ∧ gs[r]? = some g ∧ g.op = GateOp.not ∧
        g.inputs = [(v : ℕ)]) := by
  by_cases hwn : w < n + 1
  · exact ⟨⟨w, hwn⟩, false, fun u => by rw [vl_input gs u w hwn]; simp, Or.inl rfl⟩
  · obtain ⟨r, rfl⟩ : ∃ r, w = n + 1 + r := ⟨w - (n + 1), by omega⟩
    obtain ⟨g, hg⟩ : ∃ g, gs[r]? = some g := ⟨gs[r], List.getElem?_eq_getElem (by omega)⟩
    have hop := ht r (by omega) g hg
    obtain ⟨v, hin⟩ := L.not_input hfnc t ht r (by omega) g hg
    exact ⟨v, true, fun u => by
      rw [vl_not gs L.hcl u r g hg _ hop hin, vl_input gs u v v.isLt]; simp,
      Or.inr ⟨r, g, by omega, rfl, hg, hop, hin⟩⟩
lemma Least.funnel (L : Least (n + 1) f gs o) (hdep : ∃ p, Dep f p) (hnc : RestrNC f)
    (h1 : ∀ (i : Fin (n + 1)) (p q : ℕ), Reads gs p i → Reads gs q i → p = q)
    (h2 : ∀ (i : Fin (n + 1)) (r : ℕ) (g : Gate), gs[r]? = some g → g.op = GateOp.not →
      (i : ℕ) ∈ g.inputs → ∀ p q : ℕ, Reads gs p (n + 1 + r) → Reads gs q (n + 1 + r) → p = q) :
    ∃ p q : Fin (n + 1), p ≠ q ∧ Dep f p ∧ Dep f q ∧ PairFunnel f p q := by
  classical
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨p, hp⟩ := hdep
    exact dep_nc hp
  by_cases hex : ∃ (t : ℕ) (g : Gate), gs[t]? = some g ∧ g.op ≠ GateOp.not
  swap
  · exfalso
    push Not at hex
    have ht : ∀ r < gs.length, ∀ g, gs[r]? = some g → g.op = GateOp.not :=
      fun r _ g hg => hex r g hg
    by_cases hol : o < n + 1 + gs.length
    · obtain ⟨v, c, hv, _⟩ := L.lit_wire hfnc gs.length ht o hol hol
      exact lit_contra hnc v c (fun u => by rw [← L.hev, hv])
    · obtain ⟨x, y, hxy⟩ := hfnc
      apply hxy
      rw [← L.hev, ← L.hev, vl_beyond gs x o (by omega), vl_beyond gs y o (by omega)]
  obtain ⟨g, hg, hgop⟩ := Nat.find_spec hex
  set t := Nat.find hex with htdef
  have ht : ∀ r < t, ∀ g', gs[r]? = some g' → g'.op = GateOp.not := by
    intro r hr g' hg'
    by_contra hne
    exact Nat.find_min hex hr ⟨g', hg', hne⟩
  have htl : t < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  rcases L.hcl t g hg with ⟨hop, _⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · exact absurd hop hgop
  obtain ⟨vj, cj, hvj, hsj⟩ := L.lit_wire hfnc t ht j hj (by omega)
  obtain ⟨vk, ck, hvk, hsk⟩ := L.lit_wire hfnc t ht k hk (by omega)
  have hRj : Reads gs t j := ⟨g, hg, by rw [hin]; simp⟩
  have hRk : Reads gs t k := ⟨g, hg, by rw [hin]; simp⟩
  have hRv : ∀ (w : ℕ) (v : Fin (n + 1)), Reads gs t w →
      (w = v ∨ ∃ r g', r < t ∧ w = n + 1 + r ∧ gs[r]? = some g' ∧ g'.op = GateOp.not ∧
        g'.inputs = [(v : ℕ)]) → ∃ r, Reads gs r v := by
    intro w v hw hs
    rcases hs with e | ⟨r, g', _, _, hg', _, hin'⟩
    · exact ⟨t, by rw [← e]; exact hw⟩
    · exact ⟨r, g', hg', by rw [hin']; simp⟩
  have hopnd : ∀ (w : ℕ) (v : Fin (n + 1)), Reads gs t w →
      (w = v ∨ ∃ r g', r < t ∧ w = n + 1 + r ∧ gs[r]? = some g' ∧ g'.op = GateOp.not ∧
        g'.inputs = [(v : ℕ)]) →
      ∀ p' a, (a = (v : ℕ) ∨ a = w) → Reads gs p' a → n + 1 + p' ≠ w → p' = t := by
    intro w v hw hs p' a ha hr hne
    rcases hs with e | ⟨r, g', _, er, hg', hop', hin'⟩
    · have ha' : a = v := by
        rcases ha with ha | ha
        · exact ha
        · rw [ha, e]
      rw [ha'] at hr
      exact h1 v p' t hr (by rw [← e]; exact hw)
    · have hrv : Reads gs r v := ⟨g', hg', by rw [hin']; simp⟩
      rcases ha with ha | ha
      · rw [ha] at hr
        have := h1 v p' r hr hrv
        exact (hne (by rw [this, er])).elim
      · rw [ha, er] at hr
        rw [er] at hw
        exact h2 v r g' hg' hop' (by rw [hin']; simp) p' t hr hw
  have hvjk : vj ≠ vk := by
    intro e
    have hjk : j ≠ k := by
      intro e'
      subst e'
      exact L.no_alias hfnc t htl j hj (fun u => by
        rw [vl_gate gs L.hcl u t g hg, hin]
        rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval])
    rcases hsj with ej | ⟨r1, g1, hr1, ej, hg1, hop1, hin1⟩ <;>
      rcases hsk with ek | ⟨r2, g2, hr2, ek, hg2, hop2, hin2⟩
    · exact hjk (by rw [ej, ek, e])
    · have := h1 vj t r2 (by rw [← ej]; exact hRj) ⟨g2, hg2, by rw [hin2, ← e]; simp⟩
      omega
    · have := h1 vk t r1 (by rw [← ek]; exact hRk) ⟨g1, hg1, by rw [hin1, e]; simp⟩
      omega
    · have := h1 vj r1 r2 ⟨g1, hg1, by rw [hin1]; simp⟩ ⟨g2, hg2, by rw [hin2, ← e]; simp⟩
      exact hjk (by rw [ej, ek, this])
  obtain ⟨rj, hrj⟩ := hRv j vj hRj hsj
  obtain ⟨rk, hrk⟩ := hRv k vk hRk hsk
  have hdj := L.read_dep hfnc vj rj hrj
  have hdk := L.read_dep hfnc vk rk hrk
  have KC : ∀ u u' : Fin (n + 1) → Bool, (∀ i, i ≠ vj → i ≠ vk → u i = u' i) →
      vl gs u (n + 1 + t) = vl gs u' (n + 1 + t) → f u = f u' := by
    intro u u' hagr hgv
    rw [← L.hev, ← L.hev]
    refine agree_B gs L.hcl u u' (fun a => a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k) (o + 1)
      ?_ ?_ o (by omega) ?_
    · intro a ha hBa
      have hBa' : ¬ (a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k) := hBa
      rw [vl_input gs u a ha, vl_input gs u' a ha]
      apply hagr
      · intro e
        exact hBa' (Or.inl (congrArg Fin.val e))
      · intro e
        exact hBa' (Or.inr (Or.inl (congrArg Fin.val e)))
    · intro p' g' hp' _ hB' hr _
      have hB'' : ¬ (n + 1 + p' = (vj : ℕ) ∨ n + 1 + p' = (vk : ℕ) ∨ n + 1 + p' = j ∨
          n + 1 + p' = k) := hB'
      obtain ⟨a, ha, hBa⟩ := hr
      have hBa' : a = (vj : ℕ) ∨ a = (vk : ℕ) ∨ a = j ∨ a = k := hBa
      have hR : Reads gs p' a := ⟨g', hp', ha⟩
      have hpt : p' = t := by
        rcases hBa' with e | e | e | e
        · exact hopnd j vj hRj hsj p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k vk hRk hsk p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
        · exact hopnd j vj hRj hsj p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k vk hRk hsk p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
      rw [hpt]
      exact hgv
    · intro hB
      have hB' : o = (vj : ℕ) ∨ o = (vk : ℕ) ∨ o = j ∨ o = k := hB
      rcases hB' with e | e | e | e
      · exact lit_contra hnc vj false (fun x => by
          rw [← L.hev, e, vl_input gs x vj vj.isLt]; simp)
      · exact lit_contra hnc vk false (fun x => by
          rw [← L.hev, e, vl_input gs x vk vk.isLt]; simp)
      · exact lit_contra hnc vj cj (fun x => by rw [← L.hev, e, hvj])
      · exact lit_contra hnc vk ck (fun x => by rw [← L.hev, e, hvk])
  have hag : ∀ (x : Fin (n + 1) → Bool) (a b a' b' : Bool), ∀ i, i ≠ vj → i ≠ vk →
      set2 x vj a vk b i = set2 x vj a' vk b' i := by
    intro x a b a' b' i e1 e2
    rw [set2_o x vj vk a b i e1 e2, set2_o x vj vk a' b' i e1 e2]
  have hval : ∀ (x : Fin (n + 1) → Bool) (a b : Bool),
      vl gs (set2 x vj a vk b) (n + 1 + t) = g.op.eval [xor a cj, xor b ck] := by
    intro x a b
    rw [vl_gate gs L.hcl _ t g hg, hin]
    simp only [List.map_cons, List.map_nil]
    rw [hvj, hvk, set2_p x hvjk, set2_q x]
  refine ⟨vj, vk, hvjk, hdj, hdk, ?_⟩
  rcases hop with hop | hop
  · refine ⟨!cj, !ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl
  · refine ⟨cj, ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl
end SourceSection6
end PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Readers

namespace PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Readers
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
lemma fanout_step (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ) (hdep : ∃ p, Dep f p)
    (hnc : RestrNC f) (hnf : NoFunnel f) (h : PEqualNP.MetaComplexity.HasCircuitSize (n + 1) f s) :
    ∃ y : Fin (n + 1), Dep f y ∧ Pays f y s := by
  classical
  have hfnc : ∃ x y : Fin (n + 1) → Bool, f x ≠ f y := by
    obtain ⟨p, hp⟩ := hdep
    exact dep_nc hp
  obtain ⟨gs, o, L, hls⟩ := exists_least (n + 1) f s hfnc h
  have mono : ∀ y, Pays f y gs.length → Pays f y s := by
    intro y hp
    rcases hp with ⟨a, b⟩ | ⟨a, b⟩ | ⟨a, b⟩
    · exact Or.inl ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩
    · exact Or.inr (Or.inl ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩)
    · exact Or.inr (Or.inr ⟨a.mono le_rfl hls, b.mono le_rfl hls⟩)
  by_cases hA : ∃ (i : Fin (n + 1)) (p q : ℕ), p ≠ q ∧ Reads gs p i ∧ Reads gs q i
  · obtain ⟨i, p, q, hpq, hp, hq⟩ := hA
    have hd := L.read_dep hfnc i p hp
    exact ⟨i, hd, mono i (L.two_readers i (hnc i hd) p q hpq hp hq)⟩
  by_cases hB : ∃ (i : Fin (n + 1)) (r : ℕ) (g : Gate), gs[r]? = some g ∧ g.op = GateOp.not ∧
      (i : ℕ) ∈ g.inputs ∧ ∃ p q : ℕ, p ≠ q ∧ Reads gs p (n + 1 + r) ∧ Reads gs q (n + 1 + r)
  · obtain ⟨i, r, g, hr, hop, hin, p, q, hpq, hp, hq⟩ := hB
    have hd := L.read_dep hfnc i r ⟨g, hr, hin⟩
    obtain ⟨d1, d2⟩ := L.not_two_readers i (hnc i hd) r g hr hop hin p q hpq hp hq
    exact ⟨i, hd, mono i (Or.inl ⟨d1, d2⟩)⟩
  exfalso
  obtain ⟨p, q, hpq, hdp, hdq, hf⟩ := L.funnel hdep hnc
    (fun i p q hp hq => by
      by_contra hne
      exact hA ⟨i, p, q, hne, hp, hq⟩)
    (fun i r g hr hop hin p q hp hq => by
      by_contra hne
      exact hB ⟨i, r, g, hr, hop, hin, p, q, hne, hp, hq⟩)
  exact hnf p q hpq hdp hdq hf
lemma fanout_step_3_4 (n : ℕ) (f : (Fin (n + 1) → Bool) → Bool) (s : ℕ) (hdep : ∃ p, Dep f p)
    (hnc : RestrNC f) (hnf : NoFunnel f) (h : PEqualNP.MetaComplexity.HasCircuitSize (n + 1) f s) :
    (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 3 ≤ s ∧
        PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x => f (Function.update x y false)) s') ∨
      (∃ (y : Fin (n + 1)) (s' : ℕ), s' + 4 ≤ s ∧
        PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x => f (Function.update x y true)) s') := by
  obtain ⟨y, _, hp⟩ := fanout_step n f s hdep hnc hnf h
  rcases hp with ⟨⟨s', h1, h2⟩, _⟩ | ⟨⟨s', h1, h2⟩, _⟩ | ⟨_, ⟨s', h1, h2⟩⟩
  · exact Or.inl ⟨y, s', h1, h2⟩
  · exact Or.inl ⟨y, s', by omega, h2⟩
  · exact Or.inr ⟨y, s', h1, h2⟩
lemma noFunnel_of_sep {m : ℕ} (f : (Fin m → Bool) → Bool)
    (h : ∀ p q : Fin m, p ≠ q → Dep f p → Dep f q →
      (∃ x, f (set2 x p true q false) ≠ f (set2 x p false q false)) ∧
      (∃ x, f (set2 x p false q true) ≠ f (set2 x p false q false)) ∧
      (∃ x, f (set2 x p true q false) ≠ f (set2 x p false q true))) : NoFunnel f := by
  intro p q hpq hdp hdq hf
  obtain ⟨a, b, hab⟩ := hf
  obtain ⟨⟨x1, h1⟩, ⟨x2, h2⟩, ⟨x3, h3⟩⟩ := h p q hpq hdp hdq
  cases a <;> cases b
  · exact h3 (hab x3).1
  · exact h1 (hab x1).2.symm
  · exact h2 ((hab x2).1.trans (hab x2).2).symm
  · exact h1 (hab x1).2
end PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Readers

namespace PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
open PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Readers
def rd (N p a w : ℕ) : ℕ := if w < N + p then w else if w = N + p then a else w - 1
def rdel (N p a : ℕ) (gs : List Gate) : List Gate :=
  gs.take p ++ (gs.drop (p + 1)).map fun g => ⟨g.op, g.inputs.map (rd N p a)⟩
def StmtRD : Prop :=
  ∀ (N : ℕ) (gs : List Gate) (p a : ℕ), CleanL N gs → p < gs.length → a < N + p →
    CleanL N (rdel N p a gs) ∧ (rdel N p a gs).length + 1 = gs.length ∧
    (∀ (x : Fin N → Bool) (w : ℕ), w < N + p → vl (rdel N p a gs) x w = vl gs x w) ∧
    (∀ x : Fin N → Bool, vl gs x (N + p) = vl gs x a →
      ∀ w : ℕ, vl (rdel N p a gs) x (rd N p a w) = vl gs x w)
def TailOK (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (j : ℕ) : Prop :=
  ∃ g, gs[j]? = some g ∧ (g.op = GateOp.not ∨
    (g.op = GateOp.or ∧ ∀ x : Fin N → Bool, vl gs x (N + j) = true → F x = true))
def TailGE (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (t : ℕ) : Prop :=
  t ≤ gs.length ∧ ∀ j, gs.length ≤ j + t → j < gs.length → TailOK N F gs j
def StmtLift : Prop :=
  ∀ (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (o p l h : ℕ) (g : Gate),
    Least N F gs o → (∃ x y : Fin N → Bool, F x ≠ F y) →
    gs[p]? = some g → g.op = GateOp.or → (g.inputs = [l, h] ∨ g.inputs = [h, l]) →
    (∀ x : Fin N → Bool, vl gs x h = true → F x = true) →
    Least N F (rdel N p l gs ++ [⟨GateOp.or, [rd N p l o, h]⟩]) (N + (gs.length - 1)) ∧
    (¬ TailOK N F gs p → ∀ t, TailGE N F gs t →
      TailGE N F (rdel N p l gs ++ [⟨GateOp.or, [rd N p l o, h]⟩]) (t + 1))
def StmtXMove : Prop :=
  ∀ (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (o p p' l q h : ℕ) (g g' : Gate),
    Least N F gs o → (∃ x y : Fin N → Bool, F x ≠ F y) → p < p' →
    gs[p]? = some g → g.op = GateOp.and → (g.inputs = [l, h] ∨ g.inputs = [h, l]) →
    gs[p']? = some g' → g'.op = GateOp.and → (g'.inputs = [q, h] ∨ g'.inputs = [h, q]) →
    (∀ x : Fin N → Bool, vl gs x h = false → F x = true) →
    ∃ (gs' : List Gate) (o' : ℕ), Least N F gs' o' ∧
      ∀ t, TailGE N F gs t → TailGE N F gs' (t + 2)
def StmtExch : Prop :=
  ∀ (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) (o h : ℕ) (T : Finset ℕ),
    CleanL N gs → (∀ x : Fin N → Bool, vl gs x o = F x) → (∃ x y : Fin N → Bool, F x ≠ F y) →
    (∀ x : Fin N → Bool, vl gs x h = false → F x = true) →
    (∀ t ∈ T, Reads gs t h ∨ ∃ (r : ℕ) (g : Gate), gs[r]? = some g ∧
      (g.op = GateOp.or ∨ g.op = GateOp.not) ∧ Reads gs r h ∧ Reads gs t (N + r)) →
    ∃ (gs' : List Gate) (o' : ℕ), CleanL N gs' ∧ (∀ x : Fin N → Bool, vl gs' x o' = F x) ∧
      gs'.length + T.card ≤ gs.length + 2
def zeroOn {N : ℕ} (D : Finset (Fin N)) (x : Fin N → Bool) : Fin N → Bool :=
  fun i => if i ∈ D then false else x i
structure DeepHyp {N : ℕ} (F : (Fin N → Bool) → Bool) (D : Finset (Fin N)) : Prop where
  nc : ∀ y ∈ D, ∀ b : Bool, ∃ x x' : Fin N → Bool,
    F (Function.update x y b) ≠ F (Function.update x' y b)
  nf : ∀ y ∈ D, ∀ y' ∈ D, y ≠ y' → ¬ PairFunnel F y y'
  win : ∀ y ∈ D, ∀ x : Fin N → Bool, F (zeroOn D x) = false →
    ∃ x' : Fin N → Bool, (∀ i, i ∉ D → x' i = x i) ∧ x' y = false ∧ F x' = false ∧
      F (Function.update x' y true) = true
  mono : ∀ x : Fin N → Bool, F (zeroOn D x) = true → F x = true
  zero : F (fun _ => false) = false
def IsLit (N : ℕ) (gs : List Gate) (y : Fin N) (l : ℕ) : Prop :=
  l = (y : ℕ) ∨ ∃ pn, l = N + pn ∧ gs[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩
def DFree {N : ℕ} (D : Finset (Fin N)) (gs : List Gate) (h : ℕ) : Prop :=
  ∀ y ∈ D, y ∉ (suppsFrom gs (inputSupps N)).getD h ∅
def OneReader {N : ℕ} (D : Finset (Fin N)) (gs : List Gate) : Prop :=
  (∀ y ∈ D, ∀ p q : ℕ, Reads gs p (y : ℕ) → Reads gs q (y : ℕ) → p = q) ∧
  (∀ y ∈ D, ∀ pn : ℕ, gs[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩ →
    ∀ p q : ℕ, Reads gs p (N + pn) → Reads gs q (N + pn) → p = q)
def Front {N : ℕ} (D : Finset (Fin N)) (gs : List Gate) (p : ℕ) (g : Gate) (y : Fin N)
    (l h : ℕ) : Prop :=
  gs[p]? = some g ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
    (g.inputs = [l, h] ∨ g.inputs = [h, l]) ∧ y ∈ D ∧ IsLit N gs y l ∧ DFree D gs h
def StmtFront : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (gs : List Gate)
    (o : ℕ), DeepHyp F D → D.Nonempty → Least (n + 1) F gs o → OneReader D gs →
    ∃ (p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ), Front D gs p g y l h ∧ o ≠ n + 1 + p
def StmtWin : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (gs : List Gate)
    (o p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ),
    DeepHyp F D → Least (n + 1) F gs o → OneReader D gs → Front D gs p g y l h →
    (g.op = GateOp.or → ∀ x : Fin (n + 1) → Bool, vl gs x h = true → F x = true) ∧
    (g.op = GateOp.and →
      (∀ x : Fin (n + 1) → Bool, vl gs x h = false → F x = true) ∧ n + 1 ≤ h)
def StmtTwo : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (gs : List Gate)
    (o p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ),
    DeepHyp F D → Least (n + 1) F gs o → OneReader D gs → Front D gs p g y l h →
    g.op = GateOp.and → (∃ r, r ≠ p ∧ Reads gs r h) →
    ∃ (r : ℕ) (g' : Gate) (q : ℕ), r ≠ p ∧ gs[r]? = some g' ∧ g'.op = GateOp.and ∧
      (g'.inputs = [q, h] ∨ g'.inputs = [h, q]) ∧
      ∀ t, Reads gs t h → t = p ∨ t = r
def StmtAnd : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o p ph l : ℕ) (g : Gate)
    (y : Fin (n + 1)),
    Least (n + 1) F gs o →
    (∀ b : Bool, ∃ x x' : Fin (n + 1) → Bool,
      F (Function.update x y b) ≠ F (Function.update x' y b)) →
    Dep F y → gs[p]? = some g → g.op = GateOp.and →
    (g.inputs = [l, n + 1 + ph] ∨ g.inputs = [n + 1 + ph, l]) → IsLit (n + 1) gs y l →
    ph < gs.length → (∀ t, Reads gs t (n + 1 + ph) → t = p) →
    o ≠ n + 1 + p → o ≠ n + 1 + ph →
    (l = (y : ℕ) → Drop F y false 3 gs.length) ∧
    (l ≠ (y : ℕ) → Drop F y true 4 gs.length)
def StmtExt : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (s : ℕ),
    DeepHyp F D → D.Nonempty → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) F s →
    ∃ (gs : List Gate) (o : ℕ), Least (n + 1) F gs o ∧ gs.length ≤ s ∧
      (¬ OneReader D gs ∨
        ∃ (p : ℕ) (g : Gate) (y : Fin (n + 1)) (l h : ℕ), Front D gs p g y l h ∧
          g.op = GateOp.and ∧ n + 1 ≤ h ∧ o ≠ n + 1 + p ∧ ∀ t, Reads gs t h → t = p)
def StmtML : Prop :=
  ∀ (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (D : Finset (Fin (n + 1))) (s : ℕ),
    DeepHyp F D → D.Nonempty → PEqualNP.MetaComplexity.HasCircuitSize (n + 1) F s →
    ∃ y ∈ D,
      (∃ s' : ℕ, s' + 3 ≤ s ∧
        PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x => F (Function.update x y false)) s') ∨
      (∃ s' : ℕ, s' + 4 ≤ s ∧
        PEqualNP.MetaComplexity.HasCircuitSize (n + 1) (fun x => F (Function.update x y true)) s')
def StmtLB : Prop :=
  ∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)),
    (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length) →
    (∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard →
      ∀ p : G.Walk u v, 7 ≤ p.length) →
    (∀ i j : Fin n, G.Adj i j → i ∉ A) →
    (A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) →
    (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) →
    PEqualNP.MetaComplexity.HasCircuitSize n
      (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨
        ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) s →
    A.card + G.edgeSet.ncard + k ≤ s + 1
end PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn

namespace PEqualNP.Outside.L_meta_3457.SparseLower.Loc
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
open PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Readers
def NotFree (gs : List Gate) : Prop := ∀ g ∈ gs, g.op ≠ GateOp.not
def HasMonoSize (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ) : Prop :=
  ∃ C : Circuit, FanInTwo C ∧ NotFree C.gates ∧ C.size ≤ s ∧
    ∀ x : Fin n → Bool, C.eval (List.ofFn x) = f x
lemma HasMonoSize.has {n : ℕ} {f : (Fin n → Bool) → Bool} {s : ℕ} (h : HasMonoSize n f s) :
    PEqualNP.MetaComplexity.HasCircuitSize n f s := by
  obtain ⟨C, h1, _, h3, h4⟩ := h
  exact ⟨C, h1, h3, h4⟩
lemma HasMonoSize.mono {n : ℕ} {f : (Fin n → Bool) → Bool} {s s' : ℕ} (h : HasMonoSize n f s)
    (hs : s ≤ s') : HasMonoSize n f s' := by
  obtain ⟨C, h1, h2, h3, h4⟩ := h
  exact ⟨C, h1, h2, le_trans h3 hs, h4⟩
def MClean (m : ℕ) (gs : List Gate) : Prop := CleanL m gs ∧ NotFree gs
def Computes (m : ℕ) (gs : List Gate) (o : ℕ) (f : (Fin m → Bool) → Bool) : Prop :=
  ∀ x : Fin m → Bool, vl gs x o = f x
def LeastIn (Q : List Gate → Prop) (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate)
    (o : ℕ) : Prop :=
  CleanL m gs ∧ Q gs ∧ Computes m gs o f ∧
    ∀ (gs' : List Gate) (o' : ℕ), CleanL m gs' → Q gs' → Computes m gs' o' f →
      gs.length ≤ gs'.length
def MLeast (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ) : Prop :=
  LeastIn NotFree m f gs o
lemma MLeast.clean {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (h : MLeast m f gs o) : MClean m gs := ⟨h.1, h.2.1⟩
noncomputable def RdSet (gs : List Gate) (w : ℕ) : Finset ℕ := by
  classical exact (Finset.range gs.length).filter (fun q => Reads gs q w)
lemma mem_rdSet {gs : List Gate} {w q : ℕ} : q ∈ RdSet gs w ↔ Reads gs q w := by
  classical
  unfold RdSet
  rw [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨reads_len h, h⟩⟩
def pt {m : ℕ} (S : Finset (Fin m)) : Fin m → Bool := fun i => decide (i ∈ S)
def OrRd (gs : List Gate) (q v w : ℕ) : Prop :=
  ∃ g, gs[q]? = some g ∧ g.op = GateOp.or ∧ (g.inputs = [v, w] ∨ g.inputs = [w, v])
def AndRd (gs : List Gate) (q v w : ℕ) : Prop :=
  ∃ g, gs[q]? = some g ∧ g.op = GateOp.and ∧ (g.inputs = [v, w] ∨ g.inputs = [w, v])
def Removable (m : ℕ) (gs : List Gate) (o : ℕ) (P : Set (Fin m → Bool)) (S : Finset ℕ)
    (tgt : ℕ → Option ℕ) : Prop :=
  ∀ p ∈ S, p < gs.length ∧
    ((∃ j, tgt p = some j ∧ j < m + p ∧ ∀ x ∈ P, vl gs x (m + p) = vl gs x j) ∨
      (tgt p = none ∧ o ≠ m + p ∧ (∀ q, Reads gs q (m + p) → q ∈ S) ∧
        ∀ q ∈ S, tgt q ≠ some (m + p)))
end PEqualNP.Outside.L_meta_3457.SparseLower.Loc

namespace PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Forest
open SimpleGraph
lemma exists_longest_path {V : Type*} [Fintype V] (G : SimpleGraph V) [Nonempty V] :
    ∃ (a b : V) (P : G.Walk a b), P.IsPath ∧
      ∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P.length := by
  by_contra hno
  push_neg at hno
  have hk : ∀ k : ℕ, ∃ (a b : V) (P : G.Walk a b), P.IsPath ∧ k ≤ P.length := by
    intro k
    induction k with
    | zero =>
      obtain ⟨v⟩ := ‹Nonempty V›
      exact ⟨v, v, Walk.nil, Walk.IsPath.nil, le_refl _⟩
    | succ k ih =>
      obtain ⟨a, b, P, hP, hk⟩ := ih
      obtain ⟨c, d, Q, hQ, hlt⟩ := hno a b P hP
      exact ⟨c, d, Q, hQ, by omega⟩
  obtain ⟨a, b, P, hP, hle⟩ := hk (Fintype.card V)
  have := hP.length_lt
  omega
lemma forest_good_leaf {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsAcyclic)
    (he : ∃ u v : V, G.Adj u v) :
    ∃ l p : V, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧
      ((∃ q : V, ∀ w, G.Adj p w → w = l ∨ w = q) ∨
        (∃ l' : V, l' ≠ l ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p)) := by
  classical
  obtain ⟨u0, v0, h0⟩ := he
  haveI : Nonempty V := ⟨u0⟩
  obtain ⟨l, z, P, hP, hmax⟩ := exists_longest_path G
  have h1 : 1 ≤ P.length := by
    have := hmax u0 v0 (Walk.cons h0 Walk.nil) (by simp [Walk.cons_isPath_iff, h0.ne])
    simpa using this
  cases P with
  | nil => simp at h1
  | @cons _ p _ hlp P' =>
    rw [Walk.cons_isPath_iff] at hP
    obtain ⟨hP', hlP'⟩ := hP
    have hmax' : ∀ (c d : V) (Q : G.Walk c d), Q.IsPath → Q.length ≤ P'.length + 1 := by
      intro c d Q hQ
      have := hmax c d Q hQ
      simpa using this
    have hPfull : (Walk.cons hlp P').IsPath := (Walk.cons_isPath_iff _ _).2 ⟨hP', hlP'⟩
    have hleaf : ∀ w, G.Adj l w → w = p := by
      intro w hw
      by_cases hm : w ∈ (Walk.cons hlp P').support
      · have := hG.eq_snd_of_adj_start hPfull hw hm
        simpa using this
      · exfalso
        have hQ : (Walk.cons hw.symm (Walk.cons hlp P')).IsPath :=
          (Walk.cons_isPath_iff _ _).2 ⟨hPfull, hm⟩
        have := hmax' _ _ _ hQ
        simp at this
    refine ⟨l, p, hlp, hleaf, ?_⟩
    have hoff : ∀ w, G.Adj p w → w ∉ (Walk.cons hlp P').support →
        ∀ u, G.Adj w u → u = p := by
      intro w hw hwm u hu
      have hwP' : w ∉ P'.support := by
        intro h; exact hwm (by simp [h])
      have hQ : (Walk.cons hw.symm P').IsPath := (Walk.cons_isPath_iff _ _).2 ⟨hP', hwP'⟩
      by_cases hm : u ∈ (Walk.cons hw.symm P').support
      · have := hG.eq_snd_of_adj_start hQ hu hm
        simpa using this
      · exfalso
        have hQ2 : (Walk.cons hu.symm (Walk.cons hw.symm P')).IsPath :=
          (Walk.cons_isPath_iff _ _).2 ⟨hQ, hm⟩
        have := hmax' _ _ _ hQ2
        simp at this
    by_cases hex : ∃ l' : V, l' ≠ l ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p
    · exact Or.inr hex
    · left
      refine ⟨P'.snd, fun w hw => ?_⟩
      by_cases hwl : w = l
      · exact Or.inl hwl
      · right
        by_cases hm : w ∈ P'.support
        · exact hG.eq_snd_of_adj_start hP' hw hm
        · exfalso
          apply hex
          refine ⟨w, hwl, hw, hoff w hw ?_⟩
          simp [hwl, hm]
end PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Forest

namespace PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Forest
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.PermInputs
open SimpleGraph
noncomputable def F {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) :
    Bool :=
  @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)
    (Classical.propDecidable _)
lemma F_true {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (x : Fin n → Bool) :
    F G A x = true ↔
      ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) := by
  unfold F
  exact @decide_eq_true_iff _ (Classical.propDecidable _)
lemma F_eq {n : ℕ} (G G' : SimpleGraph (Fin n)) (A A' : Finset (Fin n)) (x y : Fin n → Bool)
    (h : ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) ↔
      ((∃ a ∈ A', y a = true) ∨ ∃ i j : Fin n, G'.Adj i j ∧ y i = true ∧ y j = true)) :
    F G A x = F G' A' y := by
  rw [Bool.eq_iff_iff, F_true, F_true]
  exact h
lemma F_zero {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) :
    F G A (fun _ => false) = false := by
  rw [Bool.eq_false_iff, ne_eq, F_true]
  simp
lemma F_nc {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (h : A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) :
    ∃ x y : Fin n → Bool, F G A x ≠ F G A y := by
  refine ⟨fun _ => true, fun _ => false, ?_⟩
  rw [F_zero]
  have : F G A (fun _ => true) = true := by
    rw [F_true]
    rcases h with ⟨a, ha⟩ | ⟨i, j, hij⟩
    · exact Or.inl ⟨a, ha, rfl⟩
    · exact Or.inr ⟨i, j, hij, rfl, rfl⟩
  rw [this]
  simp
lemma F_dep {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (u v : Fin n)
    (huv : G.Adj u v) (hv : v ∉ A) :
    ∃ x : Fin n → Bool, F G A (Function.update x u (!x u)) ≠ F G A x := by
  have hne : u ≠ v := huv.ne
  refine ⟨Function.update (fun _ => false) v true, ?_⟩
  have h1 : F G A (Function.update (Function.update (fun _ => false) v true) u
      (!(Function.update (fun _ => false) v true u))) = true := by
    rw [F_true]
    right
    refine ⟨u, v, huv, ?_, ?_⟩
    · simp [Function.update_of_ne hne]
    · simp [Function.update_of_ne hne.symm]
  have h2 : F G A (Function.update (fun _ => false) v true) = false := by
    rw [Bool.eq_false_iff, ne_eq, F_true]
    rintro (⟨a, ha, hx⟩ | ⟨i, j, hij, hi, hj⟩)
    · by_cases hav : a = v
      · exact hv (hav ▸ ha)
      · simp [Function.update_of_ne hav] at hx
    · have hiv : i = v := by
        by_contra h; simp [Function.update_of_ne h] at hi
      have hjv : j = v := by
        by_contra h; simp [Function.update_of_ne h] at hj
      exact hij.ne (hiv.trans hjv.symm)
  rw [h1, h2]
  simp
lemma F_dep_A {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a : Fin n)
    (ha : a ∈ A) :
    ∃ x : Fin n → Bool, F G A (Function.update x a (!x a)) ≠ F G A x := by
  refine ⟨fun _ => false, ?_⟩
  rw [F_zero]
  have : F G A (Function.update (fun _ => false) a (!false)) = true := by
    rw [F_true]
    exact Or.inl ⟨a, ha, by simp⟩
  rw [this]
  simp
lemma restrict_false {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p : Fin n)
    (hlA : l ∉ A) (hleaf : ∀ w, G.Adj l w → w = p) (x : Fin n → Bool) :
    F G A (Function.update x l false) = F (G.deleteEdges {s(l, p)}) A x := by
  apply F_eq
  apply or_congr
  · constructor
    · rintro ⟨a, ha, h⟩
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hal] at h⟩
    · rintro ⟨a, ha, h⟩
      have hal : a ≠ l := fun e => hlA (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hal]⟩
  · constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      have hil : i ≠ l := by rintro rfl; simp at hi
      have hjl : j ≠ l := by rintro rfl; simp at hj
      refine ⟨i, j, ?_, by rwa [Function.update_of_ne hil] at hi,
        by rwa [Function.update_of_ne hjl] at hj⟩
      rw [deleteEdges_adj]
      refine ⟨hij, ?_⟩
      simp [Sym2.eq_iff, hil, hjl]
    · rintro ⟨i, j, hij, hi, hj⟩
      rw [deleteEdges_adj] at hij
      obtain ⟨hij, hne⟩ := hij
      have hil : i ≠ l := by
        rintro rfl
        have := hleaf j hij
        subst this
        exact hne rfl
      have hjl : j ≠ l := by
        rintro rfl
        have := hleaf i hij.symm
        subst this
        exact hne (Sym2.eq_swap)
      exact ⟨i, j, hij, by rwa [Function.update_of_ne hil], by rwa [Function.update_of_ne hjl]⟩
lemma restrict_true {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p q : Fin n)
    (hlA : l ∉ A) (hlp : G.Adj l p) (hleaf : ∀ w, G.Adj l w → w = p)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q) (x : Fin n → Bool) :
    F G A (Function.update x l true) = F (G.deleteEdges {s(p, l), s(p, q)}) (insert p A) x := by
  have hpl : p ≠ l := hlp.ne.symm
  have hA : ∀ a ∈ A, Function.update x l true a = x a := fun a ha =>
    Function.update_of_ne (by rintro rfl; exact hlA ha) _ _
  have hG1 : ∀ i j, (G.deleteEdges {s(p, l), s(p, q)}).Adj i j → i ≠ p ∧ i ≠ l := by
    intro i j hij
    rw [deleteEdges_adj] at hij
    obtain ⟨hij, hne⟩ := hij
    constructor
    · rintro rfl
      rcases hp j hij with rfl | rfl
      · exact hne (by simp)
      · exact hne (by simp)
    · rintro rfl
      have := hleaf j hij
      subst this
      exact hne (by simp [Sym2.eq_swap])
  apply F_eq
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · exact Or.inl ⟨a, Finset.mem_insert_of_mem ha, by rwa [hA a ha] at h⟩
    · by_cases hip : i = p
      · subst hip
        exact Or.inl ⟨i, Finset.mem_insert_self _ _, by rwa [Function.update_of_ne hpl] at hi⟩
      by_cases hjp : j = p
      · subst hjp
        exact Or.inl ⟨j, Finset.mem_insert_self _ _, by rwa [Function.update_of_ne hpl] at hj⟩
      have hil : i ≠ l := by
        rintro rfl; exact hjp (hleaf j hij)
      have hjl : j ≠ l := by
        rintro rfl; exact hip (hleaf i hij.symm)
      right
      refine ⟨i, j, ?_, by rwa [Function.update_of_ne hil] at hi,
        by rwa [Function.update_of_ne hjl] at hj⟩
      rw [deleteEdges_adj]
      refine ⟨hij, ?_⟩
      simp [Sym2.eq_iff, hip, hjp]
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · rcases Finset.mem_insert.1 ha with rfl | ha
      · right
        exact ⟨l, a, hlp, by simp, by rwa [Function.update_of_ne hpl]⟩
      · exact Or.inl ⟨a, ha, by rwa [hA a ha]⟩
    · right
      have hi' := hG1 i j hij
      have hj' := hG1 j i hij.symm
      rw [deleteEdges_adj] at hij
      exact ⟨i, j, hij.1, by rwa [Function.update_of_ne hi'.2],
        by rwa [Function.update_of_ne hj'.2]⟩
def Cov {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) : Prop :=
  ∀ i j, G.Adj i j → i ∈ T ∨ j ∈ T
lemma cov_insert {n : ℕ} (G : SimpleGraph (Fin n)) (S : Set (Sym2 (Fin n))) (p : Fin n)
    (hS : ∀ e ∈ S, p ∈ e) (T : Finset (Fin n)) (hT : Cov (G.deleteEdges S) T) :
    Cov G (insert p T) := by
  intro i j hij
  by_cases he : s(i, j) ∈ S
  · have := hS _ he
    rcases Sym2.mem_iff.1 this with rfl | rfl
    · exact Or.inl (Finset.mem_insert_self _ _)
    · exact Or.inr (Finset.mem_insert_self _ _)
  · rcases hT i j ((deleteEdges_adj).2 ⟨hij, he⟩) with h | h
    · exact Or.inl (Finset.mem_insert_of_mem h)
    · exact Or.inr (Finset.mem_insert_of_mem h)
lemma cov_swap {n : ℕ} (G : SimpleGraph (Fin n)) (l p l' : Fin n) (k : ℕ)
    (hll' : l' ≠ l) (hl'p : G.Adj p l') (hleaf' : ∀ w, G.Adj l' w → w = p)
    (hk : ∀ T, Cov G T → k ≤ T.card) (T : Finset (Fin n))
    (hT : Cov (G.deleteEdges {s(l, p)}) T) : k ≤ T.card := by
  have hS : ∀ e ∈ ({s(l, p)} : Set (Sym2 (Fin n))), p ∈ e := by
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst he
    exact Sym2.mem_mk_right _ _
  by_cases hpT : p ∈ T
  · have := hk _ (cov_insert G _ p hS T hT)
    rwa [Finset.insert_eq_of_mem hpT] at this
  · have hl'T : l' ∈ T := by
      have hpl' : p ≠ l' := hl'p.ne
      rcases hT p l' ((deleteEdges_adj).2 ⟨hl'p, by
          simp [Sym2.eq_iff, hll', hpl'.symm]⟩) with h | h
      · exact absurd h hpT
      · exact h
    have hcov : Cov G (insert p (T.erase l')) := by
      intro i j hij
      by_cases hip : i = p
      · exact Or.inl (hip ▸ Finset.mem_insert_self _ _)
      by_cases hjp : j = p
      · exact Or.inr (hjp ▸ Finset.mem_insert_self _ _)
      have h0 : (G.deleteEdges {s(l, p)}).Adj i j :=
        (deleteEdges_adj).2 ⟨hij, by simp [Sym2.eq_iff, hip, hjp]⟩
      rcases hT i j h0 with h | h
      · have hil' : i ≠ l' := by
          rintro rfl; exact hjp (hleaf' j hij)
        exact Or.inl (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hil', h⟩))
      · have hjl' : j ≠ l' := by
          rintro rfl; exact hip (hleaf' i hij.symm)
        exact Or.inr (Finset.mem_insert_of_mem (Finset.mem_erase.2 ⟨hjl', h⟩))
    have h1 := hk _ hcov
    have h2 := Finset.card_insert_le p (T.erase l')
    have h3 := Finset.card_erase_add_one hl'T
    omega
lemma ncard_del1 {n : ℕ} (G : SimpleGraph (Fin n)) (l p : Fin n) (h : G.Adj l p) :
    (G.deleteEdges {s(l, p)}).edgeSet.ncard + 1 = G.edgeSet.ncard := by
  rw [edgeSet_deleteEdges]
  exact Set.ncard_sdiff_singleton_add_one (G.mem_edgeSet.2 h)
lemma ncard_del2 {n : ℕ} (G : SimpleGraph (Fin n)) (l p q : Fin n) (h : G.Adj l p) :
    G.edgeSet.ncard ≤ (G.deleteEdges {s(p, l), s(p, q)}).edgeSet.ncard + 2 ∧
      (G.deleteEdges {s(p, l), s(p, q)}).edgeSet.ncard < G.edgeSet.ncard := by
  rw [edgeSet_deleteEdges]
  constructor
  · have h1 := Set.ncard_le_ncard_sdiff_add_ncard G.edgeSet ({s(p, l), s(p, q)} : Set (Sym2 (Fin n)))
    have h2 := Set.ncard_insert_le (s(p, l)) ({s(p, q)} : Set (Sym2 (Fin n)))
    rw [Set.ncard_singleton] at h2
    omega
  · have hmem : s(l, p) ∈ G.edgeSet := G.mem_edgeSet.2 h
    have hsub : G.edgeSet \ {s(p, l), s(p, q)} ⊆ G.edgeSet \ {s(l, p)} := by
      intro e he
      refine ⟨he.1, ?_⟩
      intro he'
      apply he.2
      rw [Set.mem_singleton_iff] at he'
      rw [he', Sym2.eq_swap]
      exact Set.mem_insert _ _
    have h1 := Set.ncard_le_ncard hsub
    have h2 := Set.ncard_sdiff_singleton_lt_of_mem hmem
    omega
lemma noedge_ncard {n : ℕ} (G : SimpleGraph (Fin n)) (h : ∀ i j, ¬ G.Adj i j) :
    G.edgeSet.ncard = 0 := by
  have : G.edgeSet = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.2
    intro e
    induction e using Sym2.ind with
    | _ i j => exact fun he => h i j (G.mem_edgeSet.1 he)
  rw [this, Set.ncard_empty]
lemma del_p_adj {n : ℕ} (G : SimpleGraph (Fin n)) (l p q : Fin n)
    (hp : ∀ w, G.Adj p w → w = l ∨ w = q) (i j : Fin n)
    (hij : (G.deleteEdges {s(p, l), s(p, q)}).Adj i j) : i ≠ p := by
  rw [deleteEdges_adj] at hij
  obtain ⟨hij, hne⟩ := hij
  rintro rfl
  rcases hp j hij with rfl | rfl
  · exact hne (by simp)
  · exact hne (by simp)
lemma claimQ : ∀ (m n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (k s : ℕ),
    G.edgeSet.ncard = m → G.IsAcyclic → (∀ i j, G.Adj i j → i ∉ A) →
    (∀ T, Cov G T → k ≤ T.card) → (A.Nonempty ∨ ∃ i j, G.Adj i j) →
    PEqualNP.MetaComplexity.HasCircuitSize n (F G A) s → A.card + m + k ≤ s + 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro n G A k s hm hac hinv hk hne hC
  by_cases hE : ∃ i j, G.Adj i j
  swap
  · push_neg at hE
    have hk0 : k ≤ (∅ : Finset (Fin n)).card := hk ∅ (fun i j h => absurd h (hE i j))
    have hm0 : m = 0 := by rw [← hm]; exact noedge_ncard G hE
    have := dep_lower_set n (F G A) A (fun a ha => F_dep_A G A a ha) s hC
    simp at hk0
    omega
  obtain ⟨l, p, hlp, hleaf, hcase⟩ := forest_good_leaf G hac hE
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := l.2; omega⟩
  have hlA : l ∉ A := hinv l p hlp
  have hpA : p ∉ A := hinv p l hlp.symm
  have hdepl := F_dep G A l p hlp hpA
  have hdepp := F_dep G A p l hlp.symm hlA
  have hs1 : 2 ≤ s + 1 := by
    have := dep_lower_set _ (F G A) {l, p} (by
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hdepl
      · rw [Finset.mem_singleton] at hi
        subst hi
        exact hdepp) s hC
    rwa [Finset.card_pair hlp.ne] at this
  set G0 := G.deleteEdges {s(l, p)} with hG0
  have hm0 : G0.edgeSet.ncard + 1 = m := by rw [← hm]; exact ncard_del1 G l p hlp
  have hac0 : G0.IsAcyclic := hac.anti (deleteEdges_le _)
  have hinv0 : ∀ i j, G0.Adj i j → i ∉ A := fun i j h => hinv i j ((deleteEdges_adj).1 h).1
  have hS0 : ∀ e ∈ ({s(l, p)} : Set (Sym2 (Fin (n' + 1)))), p ∈ e := by
    intro e he
    rw [Set.mem_singleton_iff] at he
    subst he
    exact Sym2.mem_mk_right _ _
  have hrf : (fun x => F G A (Function.update x l false)) = F G0 A :=
    funext (restrict_false G A l p hlA hleaf)
  rcases hcase with ⟨q, hq⟩ | ⟨l', hl'l, hpl', hleaf'⟩
  · set G1 := G.deleteEdges {s(p, l), s(p, q)} with hG1
    by_cases h0 : A.Nonempty ∨ ∃ i j, G0.Adj i j
    · have hrt : (fun x => F G A (Function.update x l true)) = F G1 (insert p A) :=
        funext (restrict_true G A l p q hlA hlp hleaf hq)
      have hnc : ∀ b : Bool, ∃ x y : Fin (n' + 1) → Bool,
          F G A (Function.update x l b) ≠ F G A (Function.update y l b) := by
        intro b
        cases b
        · obtain ⟨x, y, hxy⟩ := F_nc G0 A h0
          refine ⟨x, y, ?_⟩
          have e1 := congrFun hrf x
          have e2 := congrFun hrf y
          rw [e1, e2]; exact hxy
        · obtain ⟨x, y, hxy⟩ := F_nc G1 (insert p A) (Or.inl (Finset.insert_nonempty _ _))
          refine ⟨x, y, ?_⟩
          have e1 := congrFun hrt x
          have e2 := congrFun hrt y
          rw [e1, e2]; exact hxy
      obtain ⟨b, s', hs', hC'⟩ := gate_elim_at n' (F G A) l s hdepl hnc hC
      cases b
      · rw [hrf] at hC'
        have hk0 : ∀ T, Cov G0 T → k - 1 ≤ T.card := fun T hT => by
          have := hk _ (cov_insert G _ p hS0 T hT)
          have := Finset.card_insert_le p T
          omega
        have := ih G0.edgeSet.ncard (by omega) _ G0 A (k - 1) s' rfl hac0 hinv0 hk0 h0 hC'
        omega
      · rw [hrt] at hC'
        have hS1 : ∀ e ∈ ({s(p, l), s(p, q)} : Set (Sym2 (Fin (n' + 1)))), p ∈ e := by
          intro e he
          rcases he with rfl | he
          · exact Sym2.mem_mk_left _ _
          · rw [Set.mem_singleton_iff] at he
            subst he
            exact Sym2.mem_mk_left _ _
        have hk1 : ∀ T, Cov G1 T → k - 1 ≤ T.card := fun T hT => by
          have := hk _ (cov_insert G _ p hS1 T hT)
          have := Finset.card_insert_le p T
          omega
        have hac1 : G1.IsAcyclic := hac.anti (deleteEdges_le _)
        have hinv1 : ∀ i j, G1.Adj i j → i ∉ insert p A := by
          intro i j h hi
          rcases Finset.mem_insert.1 hi with heq | hi
          · exact del_p_adj G l p q hq i j h heq
          · exact hinv i j ((deleteEdges_adj).1 h).1 hi
        obtain ⟨hc1, hc2⟩ := ncard_del2 G l p q hlp
        rw [← hG1] at hc1 hc2
        have := ih G1.edgeSet.ncard (by omega) _ G1 (insert p A) (k - 1) s' rfl hac1 hinv1
          hk1 (Or.inl (Finset.insert_nonempty _ _)) hC'
        rw [Finset.card_insert_of_notMem hpA] at this
        omega
    · push_neg at h0
      obtain ⟨hA0, hG00⟩ := h0
      have hm1 : m = 1 := by
        have := noedge_ncard G0 hG00
        omega
      have hk1 : k ≤ ({p} : Finset (Fin (n' + 1))).card := by
        apply hk
        intro i j hij
        have h1 := hG00 i j
        rw [deleteEdges_adj] at h1
        push_neg at h1
        have h2 := h1 hij
        rw [Set.mem_singleton_iff, Sym2.eq_iff] at h2
        rcases h2 with ⟨_, rfl⟩ | ⟨rfl, _⟩
        · exact Or.inr (Finset.mem_singleton_self _)
        · exact Or.inl (Finset.mem_singleton_self _)
      rw [Finset.card_singleton] at hk1
      subst hA0
      simp only [Finset.card_empty]
      omega
  · obtain ⟨s0, rfl⟩ : ∃ s0, s = s0 + 1 := ⟨s - 1, by omega⟩
    have hpl'0 : G0.Adj p l' := (deleteEdges_adj).2 ⟨hpl', by
      simp [Sym2.eq_iff, hl'l, hpl'.ne.symm]⟩
    have hnc0 : ∃ x y : Fin (n' + 1) → Bool,
        F G A (Function.update x l false) ≠ F G A (Function.update y l false) := by
      obtain ⟨x, y, hxy⟩ := F_nc G0 A (Or.inr ⟨p, l', hpl'0⟩)
      refine ⟨x, y, ?_⟩
      have e1 := congrFun hrf x
      have e2 := congrFun hrf y
      rw [e1, e2]; exact hxy
    have hC' := one_gate_at n' (F G A) l false s0 hdepl hnc0 hC
    rw [hrf] at hC'
    have hk0 : ∀ T, Cov G0 T → k ≤ T.card := cov_swap G l p l' k hl'l hpl' hleaf' hk
    have := ih G0.edgeSet.ncard (by omega) _ G0 A k s0 rfl hac0 hinv0 hk0
      (Or.inr ⟨p, l', hpl'0⟩) hC'
    omega
lemma forest_bound : ∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
    G.IsAcyclic → (∃ i j : Fin n, G.Adj i j) →
    (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) →
    PEqualNP.MetaComplexity.HasCircuitSize n
      (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) s →
    G.edgeFinset.card + k ≤ s + 1 := by
  intro n k s G _ hac hE hk hC
  have hf : (fun x : Fin n → Bool =>
      decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) = F G ∅ := by
    funext x
    rw [Bool.eq_iff_iff, F_true, decide_eq_true_iff]
    simp
  rw [hf] at hC
  have := claimQ _ n G ∅ k s rfl hac (by simp) (fun T hT => hk T hT) (Or.inr hE) hC
  have he : G.edgeFinset.card = G.edgeSet.ncard := by
    rw [← Set.ncard_coe_finset, coe_edgeFinset]
  rw [Finset.card_empty] at this
  omega
end PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Forest

namespace PEqualNP.Outside.L_meta_3457.SparseLower.Loc
open SimpleGraph
open PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Forest
def delV {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) : SimpleGraph (Fin n) :=
  G.deleteEdges {e | ∃ v ∈ X, v ∈ e}
lemma delV_adj {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) (i j : Fin n) :
    (delV G X).Adj i j ↔ G.Adj i j ∧ i ∉ X ∧ j ∉ X := by
  unfold delV
  rw [deleteEdges_adj]
  constructor
  · rintro ⟨h, hn⟩
    refine ⟨h, fun hi => hn ⟨i, hi, Sym2.mem_mk_left _ _⟩, fun hj => hn ⟨j, hj, Sym2.mem_mk_right _ _⟩⟩
  · rintro ⟨h, hi, hj⟩
    refine ⟨h, ?_⟩
    rintro ⟨v, hv, hmem⟩
    rcases Sym2.mem_iff.1 hmem with rfl | rfl
    · exact hi hv
    · exact hj hv
lemma delV_le {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) : delV G X ≤ G :=
  deleteEdges_le _
noncomputable def tau {n : ℕ} (G : SimpleGraph (Fin n)) : ℕ :=
  sInf {k | ∃ T : Finset (Fin n), Cov G T ∧ T.card = k}
lemma tau_attained {n : ℕ} (G : SimpleGraph (Fin n)) :
    ∃ T : Finset (Fin n), Cov G T ∧ T.card = tau G :=
  Nat.sInf_mem (s := {k | ∃ T : Finset (Fin n), Cov G T ∧ T.card = k})
    ⟨_, Finset.univ, fun i _ _ => Or.inl (Finset.mem_univ i), rfl⟩
lemma tau_le {n : ℕ} (G : SimpleGraph (Fin n)) (T : Finset (Fin n)) (h : Cov G T) :
    tau G ≤ T.card :=
  Nat.sInf_le ⟨T, h, rfl⟩
noncomputable def Phi1 {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : ℕ :=
  A.card + G.edgeSet.ncard + tau G
def AFree {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Prop :=
  ∀ i j, G.Adj i j → i ∉ A
def InL {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 9 ≤ p.length) ∧
    ∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard →
      ∀ p : G.Walk u v, 7 ≤ p.length
def Deep {n : ℕ} (G : SimpleGraph (Fin n)) (v : Fin n) : Prop :=
  ∃ u1 u2 c1 c2 : Fin n, u1 ≠ u2 ∧ (∀ w, G.Adj v w ↔ w = u1 ∨ w = u2) ∧
    (∀ w, G.Adj u1 w → w = v ∨ w = c1) ∧ (∀ w, G.Adj u2 w → w = v ∨ w = c2) ∧
    ∃ i j, G.Adj i j ∧ i ≠ v ∧ j ≠ v
structure Run {n : ℕ} (G : SimpleGraph (Fin n)) (a' a s t b b' : Fin n) : Prop where
  nd : [a', a, s, t, b, b'].Nodup
  ha : ∀ w, G.Adj a w ↔ w = a' ∨ w = s
  hs : ∀ w, G.Adj s w ↔ w = a ∨ w = t
  ht : ∀ w, G.Adj t w ↔ w = s ∨ w = b
  hb : ∀ w, G.Adj b w ↔ w = t ∨ w = b'
  ha' : ∃ c, ∀ w, G.Adj a' w → w = a ∨ w = c
  hb' : ∃ c, ∀ w, G.Adj b' w → w = b ∨ w = c
lemma Run.symm {n : ℕ} {G : SimpleGraph (Fin n)} {a' a s t b b' : Fin n}
    (h : Run G a' a s t b b') : Run G b' b t s a a' where
  nd := by
    have := List.nodup_reverse.2 h.nd
    simpa using this
  ha := fun w => (h.hb w).trans Or.comm
  hs := fun w => (h.ht w).trans Or.comm
  ht := fun w => (h.hs w).trans Or.comm
  hb := fun w => (h.ha w).trans Or.comm
  ha' := h.hb'
  hb' := h.ha'
lemma Run.deep_a {n : ℕ} {G : SimpleGraph (Fin n)} {a' a s t b b' : Fin n}
    (h : Run G a' a s t b b') : Deep G a := by
  have nd := h.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at nd
  obtain ⟨c, hc⟩ := h.ha'
  refine ⟨a', s, c, t, nd.1.2.1, h.ha, hc, fun w hw => (h.hs w).1 hw, s, t, (h.hs t).2 (Or.inr rfl), ?_, ?_⟩
  · exact fun e => nd.2.1.1 e.symm
  · exact fun e => nd.2.1.2.1 e.symm
lemma Run.deep_s {n : ℕ} {G : SimpleGraph (Fin n)} {a' a s t b b' : Fin n}
    (h : Run G a' a s t b b') : Deep G s := by
  have nd := h.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at nd
  refine ⟨a, t, a', b, nd.2.1.2.1, h.hs, fun w hw => ((h.ha w).1 hw).symm,
    fun w hw => (h.ht w).1 hw, t, b, (h.ht b).2 (Or.inr rfl), ?_, ?_⟩
  · exact fun e => nd.2.2.1.1 e.symm
  · exact fun e => nd.2.2.1.2.1 e.symm
lemma Run.deep_t {n : ℕ} {G : SimpleGraph (Fin n)} {a' a s t b b' : Fin n}
    (h : Run G a' a s t b b') : Deep G t := h.symm.deep_s
lemma Run.deep_b {n : ℕ} {G : SimpleGraph (Fin n)} {a' a s t b b' : Fin n}
    (h : Run G a' a s t b b') : Deep G b := h.symm.deep_a
def BoundOf {n : ℕ} (Sz : ((Fin n → Bool) → Bool) → ℕ → Prop) (G : SimpleGraph (Fin n))
    (A : Finset (Fin n)) : Prop :=
  ∀ s : ℕ, Sz (F G A) s → Phi1 G A ≤ s + 1
end PEqualNP.Outside.L_meta_3457.SparseLower.Loc

namespace PEqualNP.Outside.L_meta_3457.SparseLower.Loc
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
open PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Readers PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Forest
open SimpleGraph
abbrev Bound {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Prop :=
  BoundOf (HasMonoSize n) G A
def IH {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) : Prop :=
  ∀ (G' : SimpleGraph (Fin n)) (A' : Finset (Fin n)), G' ≤ G → AFree G' A' →
    (G'.edgeSet.ncard < G.edgeSet.ncard ∨ (G' = G ∧ A'.card < A.card)) → Bound G' A'
structure Cex {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ) :
    Prop where
  inv : AFree G A
  ih : IH G A
  least : MLeast n (F G A) gs o
  small : gs.length + 2 ≤ Phi1 G A
structure Ctx {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) : Prop where
  cex : Cex G A gs o
  run : Run G a' a s t b b'
  hA : A = ∅
lemma Ctx.symm {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {gs : List Gate} {o : ℕ}
    {a' a s t b b' : Fin n} (h : Ctx G A gs o a' a s t b b') : Ctx G A gs o b' b t s a a' :=
  ⟨h.cex, h.run.symm, h.hA⟩
structure Fan {n : ℕ} (gs : List Gate) (a s t b : Fin n) (qa qs qt qb : ℕ) : Prop where
  fa : RdSet gs a = {qa}
  fs : RdSet gs s = {qs}
  ft : RdSet gs t = {qt}
  fb : RdSet gs b = {qb}
lemma Fan.symm {n : ℕ} {gs : List Gate} {a s t b : Fin n} {qa qs qt qb : ℕ}
    (h : Fan gs a s t b qa qs qt qb) : Fan gs b t s a qb qt qs qa :=
  ⟨h.fb, h.ft, h.fs, h.fa⟩
def ToolLeast : Prop :=
  ∀ (n : ℕ) (f : (Fin n → Bool) → Bool) (s : ℕ), (∃ x y : Fin n → Bool, f x ≠ f y) →
    HasMonoSize n f s → ∃ (gs : List Gate) (o : ℕ), MLeast n f gs o ∧ gs.length ≤ s
def ToolOfClean : Prop :=
  ∀ (m : ℕ) (gs : List Gate) (o : ℕ), MClean m gs →
    HasMonoSize m (fun x => vl gs x o) gs.length
def ToolRemoval : Prop :=
  ∀ (m : ℕ) (gs : List Gate) (o : ℕ) (P : Set (Fin m → Bool)) (S : Finset ℕ)
    (tgt : ℕ → Option ℕ), CleanL m gs → Removable m gs o P S tgt →
    ∃ (gs' : List Gate) (r : ℕ → ℕ), CleanL m gs' ∧ (NotFree gs → NotFree gs') ∧
      gs'.length + S.card ≤ gs.length ∧ (∀ j, j < m → r j = j) ∧
      ∀ j, j < m + gs.length → (∀ p ∈ S, tgt p = none → j ≠ m + p) →
        r j < m + gs'.length ∧ ∀ x ∈ P, vl gs' x (r j) = vl gs x j
def ToolRestrict : Prop :=
  ∀ (m : ℕ) (gs : List Gate) (o : ℕ) (i : Fin m) (b : Bool), MClean m gs →
    (∃ x y : Fin m → Bool,
      vl gs (Function.update x i b) o ≠ vl gs (Function.update y i b) o) →
    HasMonoSize m (fun x => vl gs (Function.update x i b) o) gs.length
def ToolMono : Prop :=
  ∀ (m : ℕ) (gs : List Gate), MClean m gs → ∀ x y : Fin m → Bool,
    (∀ i, x i = true → y i = true) → ∀ j, vl gs x j = true → vl gs y j = true
def ToolZero : Prop :=
  ∀ (m : ℕ) (gs : List Gate), MClean m gs → ∀ j, m ≤ j → vl gs (fun _ : Fin m => false) j = false
def ToolNoAlias : Prop :=
  ∀ (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ), MLeast m f gs o →
    (∃ x y : Fin m → Bool, f x ≠ f y) → ∀ p, p < gs.length → ∀ j, j < m + p →
      ¬ ∀ x : Fin m → Bool, vl gs x (m + p) = vl gs x j
def ToolLive : Prop :=
  ∀ (m : ℕ) (f : (Fin m → Bool) → Bool) (gs : List Gate) (o : ℕ), MLeast m f gs o →
    (∃ x y : Fin m → Bool, f x ≠ f y) →
      o < m + gs.length ∧ ∀ p, p < gs.length → o ≠ m + p → (RdSet gs (m + p)).Nonempty
def ToolU : Prop :=
  ∀ (m : ℕ) (gs : List Gate) (t : Fin m) (q : ℕ), MClean m gs → RdSet gs t = {q} →
    ∀ p, p < gs.length → vl gs (pt {t}) (m + p) = true →
      p = q ∨ ∃ r ∈ RdSet gs (m + q), vl gs (pt {t}) (m + r) = true
def ToolProp : Prop :=
  ∀ (m : ℕ) (gs : List Gate) (x x' : Fin m → Bool) (D : Set ℕ) (K : ℕ), CleanL m gs →
    (∀ i : Fin m, (i : ℕ) ∉ D → x i = x' i) →
    (∀ p g, gs[p]? = some g → m + p < K → m + p ∉ D →
      (∀ w ∈ g.inputs, w ∉ D) ∨ vl gs x (m + p) = vl gs x' (m + p)) →
    ∀ j, j < K → j ∉ D → vl gs x j = vl gs x' j
def ToolLower : Prop :=
  ∀ (m : ℕ) (gs : List Gate) (o : ℕ) (P : Set (Fin m → Bool)) (z : Fin m) (p W : ℕ),
    MClean m gs → p < gs.length → W < m + p → (∀ x ∈ P, x z = false) →
    (∀ x ∈ P, vl gs x (m + p) = true → vl gs x W = true) →
    (∀ x ∈ P, vl gs x W = true → vl gs x o = true) →
    MClean m (gs.set p ⟨GateOp.and, [(z : ℕ), (z : ℕ)]⟩) ∧
      (∀ x ∈ P, vl gs x o =
        (vl (gs.set p ⟨GateOp.and, [(z : ℕ), (z : ℕ)]⟩) x o || vl gs x W)) ∧
      ∀ (x : Fin m → Bool) (j : ℕ), j < m + p →
        vl (gs.set p ⟨GateOp.and, [(z : ℕ), (z : ℕ)]⟩) x j = vl gs x j
def ToolSnoc : Prop :=
  ∀ (m : ℕ) (gs : List Gate) (j k : ℕ), MClean m gs → j < m + gs.length → k < m + gs.length →
    MClean m (gs ++ [⟨GateOp.or, [j, k]⟩]) ∧ ∀ x : Fin m → Bool,
      vl (gs ++ [⟨GateOp.or, [j, k]⟩]) x (m + gs.length) = (vl gs x j || vl gs x k) ∧
      ∀ i, i < m + gs.length → vl (gs ++ [⟨GateOp.or, [j, k]⟩]) x i = vl gs x i
def ToolLemma1a : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (s t : Fin n) (q w : ℕ), AFree G A → CleanL n gs → Computes n gs o (F G A) →
    RdSet gs s = {q} →
    OrRd gs q s w → G.Adj s t → ∀ z : Fin n → Bool, z t = true → F G A z = false →
      vl gs z w = false
def ToolRes0 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (v : Fin n) (x : Fin n → Bool),
    v ∉ A → F G A (Function.update x v false) = F (delV G {v}) A x
def ToolRes1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (v : Fin n) (N : Finset (Fin n))
    (x : Fin n → Bool), v ∉ A → (∀ w, G.Adj v w ↔ w ∈ N) →
    F G A (Function.update x v true) = F (delV G (insert v N)) (A ∪ N) x
def ToolResA : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a : Fin n) (x : Fin n → Bool),
    AFree G A → a ∈ A → F G A (Function.update x a false) = F G (A.erase a) x
def ToolResPair : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (s t b : Fin n) (x : Fin n → Bool),
    s ≠ t → b ≠ s → s ∉ A → t ∉ A → b ∉ A → (∀ w, G.Adj t w ↔ w = s ∨ w = b) →
    F G A (Function.update (Function.update x t true) s false) =
      F (delV G {s, t, b}) (insert b A) x
def ToolDrop0 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (v u1 u2 : Fin n), G.Adj v u1 →
    (∀ w, G.Adj v w → w = u1 ∨ w = u2) →
    Phi1 G A ≤ Phi1 (delV G {v}) A + 3 ∧ (delV G {v}).edgeSet.ncard < G.edgeSet.ncard
def ToolDrop1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (v u1 u2 c1 c2 : Fin n),
    (∀ w, G.Adj v w ↔ w = u1 ∨ w = u2) → (∀ w, G.Adj u1 w → w = v ∨ w = c1) →
    (∀ w, G.Adj u2 w → w = v ∨ w = c2) → u1 ∉ A → u2 ∉ A →
    Phi1 G A ≤ Phi1 (delV G (insert v {u1, u2})) (A ∪ {u1, u2}) + 4 ∧
      (delV G (insert v {u1, u2})).edgeSet.ncard < G.edgeSet.ncard
def ToolDropPair : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a s t b c : Fin n),
    [s, t, b].Nodup → (∀ w, G.Adj s w → w = a ∨ w = t) → (∀ w, G.Adj t w ↔ w = s ∨ w = b) →
    (∀ w, G.Adj b w → w = t ∨ w = c) → b ∉ A →
    Phi1 G A ≤ Phi1 (delV G {s, t, b}) (insert b A) + 5 ∧
      (delV G {s, t, b}).edgeSet.ncard < G.edgeSet.ncard
def ToolPay0 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (v u1 u2 : Fin n) (gs' : List Gate) (o' : ℕ), Cex G A gs o → G.Adj v u1 →
    (∀ w, G.Adj v w → w = u1 ∨ w = u2) → (A.Nonempty ∨ ∃ i j, G.Adj i j ∧ i ≠ v ∧ j ≠ v) →
    MClean n gs' → gs'.length + 3 ≤ gs.length →
    (∀ x : Fin n → Bool, x v = false → vl gs' x o' = F G A x) → False
def ToolPay1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (v : Fin n) (gs' : List Gate) (o' : ℕ), Cex G A gs o → Deep G v →
    MClean n gs' → gs'.length + 4 ≤ gs.length →
    (∀ x : Fin n → Bool, x v = true → vl gs' x o' = F G A x) → False
def ToolPayPair : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) (gs' : List Gate) (o' : ℕ), Cex G A gs o →
    Run G a' a s t b b' → MClean n gs' → gs'.length + 5 ≤ gs.length →
    (∀ x : Fin n → Bool, x t = true → x s = false → vl gs' x o' = F G A x) → False
def ToolCons : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) (qa qs qt qb ws wt : ℕ), Ctx G A gs o a' a s t b b' →
    Fan gs a s t b qa qs qt qb → OrRd gs qs s ws → OrRd gs qt t wt →
    qs ≠ qt ∧ vl gs (pt {a}) ws = false ∧ vl gs (pt {t}) ws = false ∧
      vl gs (pt {b}) ws = false
def PClosure : Prop :=
  ∀ (n : ℕ) (G G' : SimpleGraph (Fin n)), InL G → G' ≤ G → InL G'
def PStructure : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), InL G → (∃ i j, G.Adj i j) →
    (¬ ∃ l p q, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ ∀ w, G.Adj p w → w = l ∨ w = q) →
    (¬ ∃ l p l', G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ G.Adj p l' ∧ l' ≠ l ∧
      ∀ w, G.Adj l' w → w = p) →
    ∃ a' a s t b b', Run G a' a s t b b'
def PBase : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), (∀ i j, ¬ G.Adj i j) → Bound G A
def PS1 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), AFree G A → IH G A →
    A.Nonempty → (∃ i j, G.Adj i j) → Bound G A
def PLeafLow : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p q : Fin n), AFree G A →
    IH G A → A = ∅ → G.Adj l p → (∀ w, G.Adj l w → w = p) →
    (∀ w, G.Adj p w → w = l ∨ w = q) → Bound G A
def PTwin : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p l' : Fin n), AFree G A →
    IH G A → A = ∅ → G.Adj l p → (∀ w, G.Adj l w → w = p) → G.Adj p l' → l' ≠ l →
    (∀ w, G.Adj l' w → w = p) → Bound G A
def PFanLow : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ) (v : Fin n),
    Cex G A gs o → Deep G v → 1 ≤ (RdSet gs v).card ∧ (RdSet gs v).card ≤ 2
def PFanTwo : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ) (v : Fin n),
    Cex G A gs o → Deep G v → (RdSet gs v).card ≠ 2
def PCellA : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) (qa qs qt qb : ℕ), Ctx G A gs o a' a s t b b' →
    Fan gs a s t b qa qs qt qb → ∃ w, OrRd gs qs s w
def PReadFew : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) (qa qs qt qb ws wt : ℕ), Ctx G A gs o a' a s t b b' →
    Fan gs a s t b qa qs qt qb → OrRd gs qs s ws → OrRd gs qt t wt →
    1 ≤ (RdSet gs (n + qt)).card ∧ (RdSet gs (n + qt)).card ≤ 2
def PReadOneAnd : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) (qa qs qt qb ws wt r : ℕ) (g : Gate), Ctx G A gs o a' a s t b b' →
    Fan gs a s t b qa qs qt qb → OrRd gs qs s ws → OrRd gs qt t wt →
    RdSet gs (n + qt) = {r} → gs[r]? = some g → g.op = GateOp.and → False
def PReadOneOr : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) (qa qs qt qb ws wt r : ℕ) (g : Gate), Ctx G A gs o a' a s t b b' →
    Fan gs a s t b qa qs qt qb → OrRd gs qs s ws → OrRd gs qt t wt →
    RdSet gs (n + qt) = {r} → gs[r]? = some g → g.op = GateOp.or → False
def PReadOne : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) (qa qs qt qb ws wt : ℕ), Ctx G A gs o a' a s t b b' →
    Fan gs a s t b qa qs qt qb → OrRd gs qs s ws → OrRd gs qt t wt →
    (RdSet gs (n + qt)).card ≠ 1
def PReadTwo : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) (qa qs qt qb ws wt : ℕ), Ctx G A gs o a' a s t b b' →
    Fan gs a s t b qa qs qt qb → OrRd gs qs s ws → OrRd gs qt t wt →
    (RdSet gs (n + qt)).card = 2 → ∀ q ∈ RdSet gs (n + qt), vl gs (pt {t}) (n + q) = false
def PLast : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) (qa qs qt qb ws wt : ℕ), Ctx G A gs o a' a s t b b' →
    Fan gs a s t b qa qs qt qb → OrRd gs qs s ws → OrRd gs qt t wt →
    (RdSet gs (n + qs)).card = 2 → (∀ q ∈ RdSet gs (n + qs), vl gs (pt {s}) (n + q) = false) →
    (RdSet gs (n + qt)).card = 2 → (∀ q ∈ RdSet gs (n + qt), vl gs (pt {t}) (n + q) = false) →
    ∃ q, q ∈ RdSet gs (n + qs) ∧ q ∈ RdSet gs (n + qt)
def PFC : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (gs : List Gate) (o : ℕ)
    (a' a s t b b' : Fin n) (qa qs qt qb ws wt q : ℕ), Ctx G A gs o a' a s t b b' →
    Fan gs a s t b qa qs qt qb → OrRd gs qs s ws → OrRd gs qt t wt →
    (RdSet gs (n + qs)).card = 2 → (∀ r ∈ RdSet gs (n + qs), vl gs (pt {s}) (n + r) = false) →
    (RdSet gs (n + qt)).card = 2 → (∀ r ∈ RdSet gs (n + qt), vl gs (pt {t}) (n + r) = false) →
    q ∈ RdSet gs (n + qs) → q ∈ RdSet gs (n + qt) → False
def PStep : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (a' a s t b b' : Fin n),
    AFree G A → IH G A → A = ∅ → Run G a' a s t b b' → Bound G A
lemma fan_of_pieces (hLow : PFanLow) (hTwo : PFanTwo) {n : ℕ} {G : SimpleGraph (Fin n)}
    {A : Finset (Fin n)} {gs : List Gate} {o : ℕ} (v : Fin n) (hc : Cex G A gs o)
    (hd : Deep G v) : ∃ q, RdSet gs v = {q} := by
  have h1 := hLow n G A gs o v hc hd
  have h2 := hTwo n G A gs o v hc hd
  exact Finset.card_eq_one.1 (by omega)
lemma readOne_of_pieces (hAnd : PReadOneAnd) (hOr : PReadOneOr) : PReadOne := by
  intro n G A gs o a' a s t b b' qa qs qt qb ws wt hctx hfan hws hwt hcard
  obtain ⟨r, hr⟩ := Finset.card_eq_one.1 hcard
  have hrm : r ∈ RdSet gs (n + qt) := by rw [hr]; exact Finset.mem_singleton_self r
  obtain ⟨g, hg, _⟩ := mem_rdSet.1 hrm
  have hcl := hctx.cex.least.1 r g hg
  have hnf := hctx.cex.least.2.1 g (List.mem_of_getElem? hg)
  rcases hcl with ⟨h1, _⟩ | ⟨h1 | h1, _⟩
  · exact hnf h1
  · exact hAnd n G A gs o a' a s t b b' qa qs qt qb ws wt r g hctx hfan hws hwt hr hg h1
  · exact hOr n G A gs o a' a s t b b' qa qs qt qb ws wt r g hctx hfan hws hwt hr hg h1
lemma step_of_pieces (hLeast : ToolLeast) (hLow : PFanLow) (hTwo : PFanTwo) (hA : PCellA)
    (hFew : PReadFew) (hAnd : PReadOneAnd) (hOr : PReadOneOr) (hTwoR : PReadTwo) (hLast : PLast)
    (hFC : PFC) : PStep := by
  have hOne : PReadOne := readOne_of_pieces hAnd hOr
  intro n G A a' a s t b b' hinv hih hA0 hrun s0 hC
  by_contra hlt
  have hnc : ∃ x y : Fin n → Bool, F G A x ≠ F G A y :=
    F_nc G A (Or.inr ⟨s, t, (hrun.hs t).2 (Or.inr rfl)⟩)
  obtain ⟨gs, o, hL, hlen⟩ := hLeast n (F G A) s0 hnc hC
  have hc : Cex G A gs o := ⟨hinv, hih, hL, by omega⟩
  have hctx : Ctx G A gs o a' a s t b b' := ⟨hc, hrun, hA0⟩
  obtain ⟨qa, hqa⟩ := fan_of_pieces hLow hTwo a hc hrun.deep_a
  obtain ⟨qs, hqs⟩ := fan_of_pieces hLow hTwo s hc hrun.deep_s
  obtain ⟨qt, hqt⟩ := fan_of_pieces hLow hTwo t hc hrun.deep_t
  obtain ⟨qb, hqb⟩ := fan_of_pieces hLow hTwo b hc hrun.deep_b
  have hfan : Fan gs a s t b qa qs qt qb := ⟨hqa, hqs, hqt, hqb⟩
  obtain ⟨ws, hws⟩ := hA n G A gs o a' a s t b b' qa qs qt qb hctx hfan
  obtain ⟨wt, hwt⟩ := hA n G A gs o b' b t s a a' qb qt qs qa hctx.symm hfan.symm
  have ht1 := hFew n G A gs o a' a s t b b' qa qs qt qb ws wt hctx hfan hws hwt
  have ht2 := hOne n G A gs o a' a s t b b' qa qs qt qb ws wt hctx hfan hws hwt
  have hs1 := hFew n G A gs o b' b t s a a' qb qt qs qa wt ws hctx.symm hfan.symm hwt hws
  have hs2 := hOne n G A gs o b' b t s a a' qb qt qs qa wt ws hctx.symm hfan.symm hwt hws
  have hct : (RdSet gs (n + qt)).card = 2 := by omega
  have hcs : (RdSet gs (n + qs)).card = 2 := by omega
  have hqt2 := hTwoR n G A gs o a' a s t b b' qa qs qt qb ws wt hctx hfan hws hwt hct
  have hqs2 := hTwoR n G A gs o b' b t s a a' qb qt qs qa wt ws hctx.symm hfan.symm hwt hws hcs
  obtain ⟨q, hq1, hq2⟩ :=
    hLast n G A gs o a' a s t b b' qa qs qt qb ws wt hctx hfan hws hwt hcs hqs2 hct hqt2
  exact hFC n G A gs o a' a s t b b' qa qs qt qb ws wt q hctx hfan hws hwt hcs hqs2 hct hqt2
    hq1 hq2
lemma main_of_pieces (hCl : PClosure) (hSt : PStructure) (hB : PBase) (hS1 : PS1)
    (hLL : PLeafLow) (hTw : PTwin) (hStep : PStep) :
    ∀ (n e c : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), G.edgeSet.ncard = e →
      A.card = c → InL G → AFree G A → Bound G A := by
  intro n e
  induction e using Nat.strong_induction_on with
  | _ e ihe =>
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ihc =>
  intro G A he hc hL hinv
  have hih : IH G A := by
    intro G' A' hle hinv' hlt
    rcases hlt with hlt | ⟨hG, hlt⟩
    · exact ihe _ (by rw [← he]; exact hlt) _ G' A' rfl rfl (hCl n G G' hL hle) hinv'
    · rw [hG]
      rw [hG] at hinv'
      exact ihc _ (by rw [← hc]; exact hlt) G A' he rfl hL hinv'
  by_cases hE : ∃ i j, G.Adj i j
  swap
  · exact hB n G A (fun i j h => hE ⟨i, j, h⟩)
  by_cases hA : A.Nonempty
  · exact hS1 n G A hinv hih hA hE
  have hA0 : A = ∅ := Finset.not_nonempty_iff_eq_empty.1 hA
  by_cases h1 : ∃ l p q, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ ∀ w, G.Adj p w → w = l ∨ w = q
  · obtain ⟨l, p, q, h, h', h''⟩ := h1
    exact hLL n G A l p q hinv hih hA0 h h' h''
  by_cases h2 : ∃ l p l', G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ G.Adj p l' ∧ l' ≠ l ∧
      ∀ w, G.Adj l' w → w = p
  · obtain ⟨l, p, l', h, h', h'', h3, h4⟩ := h2
    exact hTw n G A l p l' hinv hih hA0 h h' h'' h3 h4
  obtain ⟨a', a, s, t, b, b', hrun⟩ := hSt n G hL hE h1 h2
  exact hStep n G A a' a s t b b' hinv hih hA0 hrun
def RowStmt : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj], (∀ (v : Fin n) (p : G.Walk v v), p.IsCycle → 9 ≤ p.length) → (∀ (u v : Fin n), u ≠ v → 3 ≤ G.degree u → 3 ≤ G.degree v → ∀ p : G.Walk u v, 7 ≤ p.length) → ∀ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.FanInTwo D → (∀ g ∈ D.gates, g.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not) → PEqualNP.MetaComplexity.circuitFun n D = (fun x : Fin n → Bool => decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) → ∃ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) ∧ G.edgeFinset.card + T.card ≤ D.size + 1
lemma ncard_nbr {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (u : Fin n) :
    (G.neighborSet u).ncard = G.degree u := by
  rw [Set.ncard_eq_toFinset_card']
  rfl
lemma row_of_main
    (h : ∀ (n e c : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), G.edgeSet.ncard = e →
      A.card = c → InL G → AFree G A → Bound G A) : RowStmt := by
  intro n G _ hg hd D hF hN hfun
  have hL : InL G := ⟨hg, fun u v huv hu hv p =>
    hd u v huv (by rwa [ncard_nbr] at hu) (by rwa [ncard_nbr] at hv) p⟩
  have hf : (fun x : Fin n → Bool =>
      decide (∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true)) = F G ∅ := by
    funext x
    rw [Bool.eq_iff_iff, F_true, decide_eq_true_iff]
    simp
  have hM : HasMonoSize n (F G ∅) D.size :=
    ⟨D, hF, hN, le_refl _, fun x => by rw [← hf, ← hfun]; rfl⟩
  have hb := h n _ _ G ∅ rfl rfl hL (fun _ _ _ => by simp) D.size hM
  obtain ⟨T, hT, hTc⟩ := tau_attained G
  refine ⟨T, hT, ?_⟩
  have he : G.edgeFinset.card = G.edgeSet.ncard := by
    rw [← Set.ncard_coe_finset, coe_edgeFinset]
  unfold Phi1 at hb
  rw [Finset.card_empty] at hb
  omega
lemma loc_of_pieces (hCl : PClosure) (hSt : PStructure) (hB : PBase) (hS1 : PS1)
    (hLL : PLeafLow) (hTw : PTwin) (hLeast : ToolLeast) (hLow : PFanLow) (hTwo : PFanTwo)
    (hA : PCellA) (hFew : PReadFew) (hAnd : PReadOneAnd) (hOr : PReadOneOr) (hTwoR : PReadTwo)
    (hLast : PLast) (hFC : PFC) : RowStmt :=
  row_of_main (main_of_pieces hCl hSt hB hS1 hLL hTw
    (step_of_pieces hLeast hLow hTwo hA hFew hAnd hOr hTwoR hLast hFC))
end PEqualNP.Outside.L_meta_3457.SparseLower.Loc

namespace PEqualNP.Outside.L_meta_3457.SparseLower.Loc.Res
open PEqualNP.Outside.L_meta_3457.SparseLower.Loc PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Forest SimpleGraph
lemma ToolRes0_proof : ToolRes0 := by
  intro n G A v x hv
  apply F_eq
  apply or_congr
  · constructor
    · rintro ⟨a, ha, h⟩
      have hav : a ≠ v := fun e => hv (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hav] at h⟩
    · rintro ⟨a, ha, h⟩
      have hav : a ≠ v := fun e => hv (e ▸ ha)
      exact ⟨a, ha, by rwa [Function.update_of_ne hav]⟩
  · constructor
    · rintro ⟨i, j, hij, hi, hj⟩
      have hiv : i ≠ v := by rintro rfl; simp at hi
      have hjv : j ≠ v := by rintro rfl; simp at hj
      refine ⟨i, j, (delV_adj G {v} i j).2 ⟨hij, by simpa using hiv, by simpa using hjv⟩,
        by rwa [Function.update_of_ne hiv] at hi, by rwa [Function.update_of_ne hjv] at hj⟩
    · rintro ⟨i, j, hij, hi, hj⟩
      obtain ⟨hij, hiv, hjv⟩ := (delV_adj G {v} i j).1 hij
      have hiv' : i ≠ v := by simpa using hiv
      have hjv' : j ≠ v := by simpa using hjv
      exact ⟨i, j, hij, by rwa [Function.update_of_ne hiv'], by rwa [Function.update_of_ne hjv']⟩
lemma ToolRes1_proof : ToolRes1 := by
  intro n G A v N x hv hN
  apply F_eq
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · have hav : a ≠ v := fun e => hv (e ▸ ha)
      exact Or.inl ⟨a, Finset.mem_union_left _ ha, by rwa [Function.update_of_ne hav] at h⟩
    · by_cases hiv : i = v
      · subst hiv
        exact Or.inl ⟨j, Finset.mem_union_right _ ((hN j).1 hij),
          by rwa [Function.update_of_ne hij.ne.symm] at hj⟩
      by_cases hjv : j = v
      · subst hjv
        exact Or.inl ⟨i, Finset.mem_union_right _ ((hN i).1 hij.symm),
          by rwa [Function.update_of_ne hij.ne] at hi⟩
      rw [Function.update_of_ne hiv] at hi
      rw [Function.update_of_ne hjv] at hj
      by_cases hiN : i ∈ N
      · exact Or.inl ⟨i, Finset.mem_union_right _ hiN, hi⟩
      by_cases hjN : j ∈ N
      · exact Or.inl ⟨j, Finset.mem_union_right _ hjN, hj⟩
      exact Or.inr ⟨i, j, (delV_adj G _ i j).2 ⟨hij, by simp [hiv, hiN], by simp [hjv, hjN]⟩,
        hi, hj⟩
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · rcases Finset.mem_union.1 ha with ha | ha
      · have hav : a ≠ v := fun e => hv (e ▸ ha)
        exact Or.inl ⟨a, ha, by rwa [Function.update_of_ne hav]⟩
      · have hva := (hN a).2 ha
        exact Or.inr ⟨v, a, hva, by simp, by rwa [Function.update_of_ne hva.ne.symm]⟩
    · obtain ⟨hij, hi', hj'⟩ := (delV_adj G _ i j).1 hij
      simp only [Finset.mem_insert, not_or] at hi' hj'
      exact Or.inr ⟨i, j, hij, by rwa [Function.update_of_ne hi'.1],
        by rwa [Function.update_of_ne hj'.1]⟩
lemma ToolResA_proof : ToolResA := by
  intro n G A a x hfree ha
  apply F_eq
  apply or_congr
  · constructor
    · rintro ⟨a', ha', h⟩
      have hne : a' ≠ a := by rintro rfl; simp at h
      exact ⟨a', Finset.mem_erase.2 ⟨hne, ha'⟩, by rwa [Function.update_of_ne hne] at h⟩
    · rintro ⟨a', ha', h⟩
      obtain ⟨hne, ha'⟩ := Finset.mem_erase.1 ha'
      exact ⟨a', ha', by rwa [Function.update_of_ne hne]⟩
  · have hi : ∀ i j, G.Adj i j → i ≠ a := fun i j hij e => hfree i j hij (e ▸ ha)
    constructor
    · rintro ⟨i, j, hij, h1, h2⟩
      exact ⟨i, j, hij, by rwa [Function.update_of_ne (hi i j hij)] at h1,
        by rwa [Function.update_of_ne (hi j i hij.symm)] at h2⟩
    · rintro ⟨i, j, hij, h1, h2⟩
      exact ⟨i, j, hij, by rwa [Function.update_of_ne (hi i j hij)],
        by rwa [Function.update_of_ne (hi j i hij.symm)]⟩
lemma ToolResPair_proof : ToolResPair := by
  intro n G A s t b x hst hbs hsA htA hbA ht
  have htb : G.Adj t b := (ht b).2 (Or.inr rfl)
  have hbt : b ≠ t := htb.ne.symm
  have hys : Function.update (Function.update x t true) s false s = false := by simp
  have hyt : Function.update (Function.update x t true) s false t = true := by
    rw [Function.update_of_ne hst.symm]; simp
  have hy : ∀ w, w ≠ s → w ≠ t → Function.update (Function.update x t true) s false w = x w := by
    intro w h1 h2
    rw [Function.update_of_ne h1, Function.update_of_ne h2]
  apply F_eq
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · have h1 : a ≠ s := fun e => hsA (e ▸ ha)
      have h2 : a ≠ t := fun e => htA (e ▸ ha)
      exact Or.inl ⟨a, Finset.mem_insert_of_mem ha, by rwa [hy a h1 h2] at h⟩
    · have his : i ≠ s := by rintro rfl; rw [hys] at hi; exact absurd hi (by simp)
      have hjs : j ≠ s := by rintro rfl; rw [hys] at hj; exact absurd hj (by simp)
      have hxb : (Function.update (Function.update x t true) s false b = true) → x b = true :=
        fun h => by rwa [hy b hbs hbt] at h
      by_cases hit : i = t
      · subst hit
        rcases (ht j).1 hij with rfl | rfl
        · exact absurd rfl hjs
        · exact Or.inl ⟨j, Finset.mem_insert_self _ _, hxb hj⟩
      by_cases hjt : j = t
      · subst hjt
        rcases (ht i).1 hij.symm with rfl | rfl
        · exact absurd rfl his
        · exact Or.inl ⟨i, Finset.mem_insert_self _ _, hxb hi⟩
      rw [hy i his hit] at hi
      rw [hy j hjs hjt] at hj
      by_cases hib : i = b
      · subst hib; exact Or.inl ⟨i, Finset.mem_insert_self _ _, hi⟩
      by_cases hjb : j = b
      · subst hjb; exact Or.inl ⟨j, Finset.mem_insert_self _ _, hj⟩
      exact Or.inr ⟨i, j, (delV_adj G _ i j).2 ⟨hij, by simp [his, hit, hib],
        by simp [hjs, hjt, hjb]⟩, hi, hj⟩
  · rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · rcases Finset.mem_insert.1 ha with rfl | ha
      · exact Or.inr ⟨t, a, htb, hyt, by rwa [hy a hbs hbt]⟩
      · have h1 : a ≠ s := fun e => hsA (e ▸ ha)
        have h2 : a ≠ t := fun e => htA (e ▸ ha)
        exact Or.inl ⟨a, ha, by rwa [hy a h1 h2]⟩
    · obtain ⟨hij, hi', hj'⟩ := (delV_adj G _ i j).1 hij
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hi' hj'
      exact Or.inr ⟨i, j, hij, by rwa [hy i hi'.1 hi'.2.1], by rwa [hy j hj'.1 hj'.2.1]⟩
lemma edges_le {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n))
    (S : Finset (Sym2 (Fin n))) (h : ∀ i j, G.Adj i j → i ∈ X → s(i, j) ∈ S) :
    G.edgeSet.ncard ≤ (delV G X).edgeSet.ncard + S.card := by
  have hsub : G.edgeSet ⊆ (delV G X).edgeSet ∪ (S : Set (Sym2 (Fin n))) := by
    intro e he
    induction e using Sym2.ind with
    | _ i j =>
      have hij : G.Adj i j := G.mem_edgeSet.1 he
      by_cases hi : i ∈ X
      · exact Or.inr (Finset.mem_coe.2 (h i j hij hi))
      by_cases hj : j ∈ X
      · have := h j i hij.symm hj
        rw [Sym2.eq_swap] at this
        exact Or.inr (Finset.mem_coe.2 this)
      exact Or.inl ((delV G X).mem_edgeSet.2 ((delV_adj G X i j).2 ⟨hij, hi, hj⟩))
  calc G.edgeSet.ncard ≤ ((delV G X).edgeSet ∪ (S : Set (Sym2 (Fin n)))).ncard :=
        Set.ncard_le_ncard hsub
    _ ≤ (delV G X).edgeSet.ncard + (S : Set (Sym2 (Fin n))).ncard := Set.ncard_union_le _ _
    _ = (delV G X).edgeSet.ncard + S.card := by rw [Set.ncard_coe_finset]
lemma edges_lt {n : ℕ} (G : SimpleGraph (Fin n)) (X : Finset (Fin n)) (i j : Fin n)
    (hij : G.Adj i j) (hi : i ∈ X) : (delV G X).edgeSet.ncard < G.edgeSet.ncard := by
  refine Set.ncard_lt_ncard ?_ (Set.toFinite _)
  rw [Set.ssubset_iff_of_subset (edgeSet_subset_edgeSet.2 (delV_le G X))]
  refine ⟨s(i, j), G.mem_edgeSet.2 hij, fun hmem => ?_⟩
  exact ((delV_adj G X i j).1 ((delV G X).mem_edgeSet.1 hmem)).2.1 hi
lemma tau_delV {n : ℕ} (G : SimpleGraph (Fin n)) (X Y : Finset (Fin n))
    (h : ∀ i j, G.Adj i j → i ∈ X → i ∈ Y ∨ j ∈ Y) :
    tau G ≤ tau (delV G X) + Y.card := by
  obtain ⟨T, hT, hc⟩ := tau_attained (delV G X)
  have hcov : Cov G (T ∪ Y) := by
    intro i j hij
    by_cases hi : i ∈ X
    · rcases h i j hij hi with h' | h'
      · exact Or.inl (Finset.mem_union_right _ h')
      · exact Or.inr (Finset.mem_union_right _ h')
    by_cases hj : j ∈ X
    · rcases h j i hij.symm hj with h' | h'
      · exact Or.inr (Finset.mem_union_right _ h')
      · exact Or.inl (Finset.mem_union_right _ h')
    rcases hT i j ((delV_adj G X i j).2 ⟨hij, hi, hj⟩) with h' | h'
    · exact Or.inl (Finset.mem_union_left _ h')
    · exact Or.inr (Finset.mem_union_left _ h')
  calc tau G ≤ (T ∪ Y).card := tau_le G _ hcov
    _ ≤ T.card + Y.card := Finset.card_union_le _ _
    _ = tau (delV G X) + Y.card := by rw [hc]
lemma card_le_two' {α : Type*} [DecidableEq α] (a b : α) : ({a, b} : Finset α).card ≤ 2 :=
  (Finset.card_insert_le _ _).trans (by simp)
lemma card_le_four' {α : Type*} [DecidableEq α] (a b c d : α) :
    ({a, b, c, d} : Finset α).card ≤ 4 := by
  refine (Finset.card_insert_le _ _).trans ?_
  refine Nat.succ_le_succ ((Finset.card_insert_le _ _).trans ?_)
  exact Nat.succ_le_succ (card_le_two' c d)
lemma ToolDrop0_proof : ToolDrop0 := by
  intro n G A v u1 u2 h1 hv
  refine ⟨?_, edges_lt G {v} v u1 h1 (Finset.mem_singleton_self v)⟩
  have hE := edges_le G {v} {s(v, u1), s(v, u2)} (by
    intro i j hij hi
    rw [Finset.mem_singleton] at hi
    subst hi
    rcases hv j hij with rfl | rfl <;> simp)
  have hT := tau_delV G {v} {v} (fun i j _ hi => Or.inl hi)
  have hS := card_le_two' (s(v, u1)) (s(v, u2))
  rw [Finset.card_singleton] at hT
  unfold Phi1
  omega
lemma ToolDrop1_proof : ToolDrop1 := by
  intro n G A v u1 u2 c1 c2 hv h1 h2 hu1 hu2
  have hvu1 : G.Adj v u1 := (hv u1).2 (Or.inl rfl)
  refine ⟨?_, edges_lt G _ v u1 hvu1 (Finset.mem_insert_self _ _)⟩
  have hE := edges_le G (insert v {u1, u2}) {s(v, u1), s(v, u2), s(u1, c1), s(u2, c2)} (by
    intro i j hij hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · rcases (hv j).1 hij with rfl | rfl <;> simp
    · rcases h1 j hij with rfl | rfl <;> simp [Sym2.eq_swap]
    · rcases h2 j hij with rfl | rfl <;> simp [Sym2.eq_swap])
  have hT := tau_delV G (insert v {u1, u2}) {u1, u2} (by
    intro i j hij hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · rcases (hv j).1 hij with rfl | rfl <;> simp
    · simp
    · simp)
  have hS := card_le_four' (s(v, u1)) (s(v, u2)) (s(u1, c1)) (s(u2, c2))
  have hdis : A ∩ {u1, u2} = ∅ := by
    ext w
    simp only [Finset.mem_inter, Finset.mem_insert, Finset.mem_singleton,
      Finset.notMem_empty, iff_false, not_and]
    rintro hw (rfl | rfl)
    · exact hu1 hw
    · exact hu2 hw
  have hA := Finset.card_union_add_card_inter A {u1, u2}
  rw [hdis, Finset.card_empty] at hA
  unfold Phi1
  omega
lemma ToolDropPair_proof : ToolDropPair := by
  intro n G A a s t b c _ hs ht hb hbA
  have hts : G.Adj t s := (ht s).2 (Or.inl rfl)
  refine ⟨?_, edges_lt G _ t s hts (by simp)⟩
  have hE := edges_le G {s, t, b} {s(s, a), s(s, t), s(t, b), s(b, c)} (by
    intro i j hij hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · rcases hs j hij with rfl | rfl <;> simp
    · rcases (ht j).1 hij with rfl | rfl <;> simp [Sym2.eq_swap]
    · rcases hb j hij with rfl | rfl <;> simp [Sym2.eq_swap])
  have hT := tau_delV G {s, t, b} {s, b} (by
    intro i j hij hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · simp
    · rcases (ht j).1 hij with rfl | rfl <;> simp
    · simp)
  have hS := card_le_four' (s(s, a)) (s(s, t)) (s(t, b)) (s(b, c))
  have hY := card_le_two' s b
  have hA := Finset.card_insert_of_notMem hbA
  unfold Phi1
  omega
end PEqualNP.Outside.L_meta_3457.SparseLower.Loc.Res

namespace PEqualNP.Outside.L_meta_3457.SparseLower.Loc.Free
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
open PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Readers PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Forest
open PEqualNP.Outside.L_meta_3457.SparseLower.Loc
open SimpleGraph
lemma vl_bin {m : ℕ} {gs : List Gate} (hcl : CleanL m gs) (hnf : NotFree gs) {p : ℕ} {g : Gate}
    (hp : gs[p]? = some g) : ∃ j k, j < m + p ∧ k < m + p ∧ g.inputs = [j, k] ∧
      ((∀ x : Fin m → Bool, vl gs x (m + p) = (vl gs x j && vl gs x k)) ∨
        (∀ x : Fin m → Bool, vl gs x (m + p) = (vl gs x j || vl gs x k))) := by
  rcases hcl p g hp with ⟨hnot, _⟩ | ⟨hop, j, k, hj, hk, hin⟩
  · exact absurd hnot (hnf g (List.mem_of_getElem? hp))
  refine ⟨j, k, hj, hk, hin, ?_⟩
  rcases hop with hop | hop
  · left
    intro x
    rw [vl_gate gs hcl x p g hp, hop, hin]
    simp [GateOp.eval]
  · right
    intro x
    rw [vl_gate gs hcl x p g hp, hop, hin]
    simp [GateOp.eval]
lemma alias_of_rd {m : ℕ} {gs : List Gate} (hcl : CleanL m gs) (hnf : NotFree gs) {p w : ℕ}
    (hr : Reads gs p w) (P : Set (Fin m → Bool)) (c : Bool) (hc : ∀ x ∈ P, vl gs x w = c) :
    ∃ t, t < m + p ∧ ∀ x ∈ P, vl gs x (m + p) = vl gs x t := by
  obtain ⟨g, hg, hw⟩ := hr
  obtain ⟨j, k, hj, hk, hin, hv⟩ := vl_bin hcl hnf hg
  rw [hin] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl <;> rcases hv with hv | hv <;> cases c
  · exact ⟨w, hj, fun x hx => by rw [hv, hc x hx]; simp⟩
  · exact ⟨k, hk, fun x hx => by rw [hv, hc x hx]; simp⟩
  · exact ⟨k, hk, fun x hx => by rw [hv, hc x hx]; simp⟩
  · exact ⟨w, hj, fun x hx => by rw [hv, hc x hx]; simp⟩
  · exact ⟨w, hk, fun x hx => by rw [hv, hc x hx]; simp⟩
  · exact ⟨j, hj, fun x hx => by rw [hv, hc x hx]; simp⟩
  · exact ⟨j, hj, fun x hx => by rw [hv, hc x hx]; simp⟩
  · exact ⟨w, hk, fun x hx => by rw [hv, hc x hx]; simp⟩
lemma abs_rd {m : ℕ} {gs : List Gate} (hcl : CleanL m gs) (hnf : NotFree gs) {p w : ℕ}
    (hr : Reads gs p w) : ∃ c : Bool, ∀ x : Fin m → Bool, vl gs x w = c → vl gs x (m + p) = c := by
  obtain ⟨g, hg, hw⟩ := hr
  obtain ⟨j, k, _, _, hin, hv⟩ := vl_bin hcl hnf hg
  rw [hin] at hw
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hv with hv | hv
  · refine ⟨false, fun x hx => ?_⟩
    rw [hv]
    rcases hw with rfl | rfl <;> simp [hx]
  · refine ⟨true, fun x hx => ?_⟩
    rw [hv]
    rcases hw with rfl | rfl <;> simp [hx]
lemma out_lt {m : ℕ} {gs : List Gate} {o : ℕ} {f : (Fin m → Bool) → Bool}
    (hev : Computes m gs o f) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) : o < m + gs.length := by
  by_contra h
  obtain ⟨x, y, hxy⟩ := hnc
  apply hxy
  rw [← hev x, ← hev y, vl_beyond gs x o (by omega), vl_beyond gs y o (by omega)]
lemma out_ne {m : ℕ} {gs : List Gate} {o : ℕ} {f : (Fin m → Bool) → Bool}
    (hev : Computes m gs o f) (i : Fin m) (x : Fin m → Bool) (h : f x ≠ x i) : o ≠ (i : ℕ) := by
  intro e
  apply h
  rw [← hev x, e, vl_input gs x i i.isLt]
lemma read_of_dep {m : ℕ} {gs : List Gate} {o : ℕ} {f : (Fin m → Bool) → Bool}
    (hev : Computes m gs o f) (i : Fin m)
    (hd : ∃ x : Fin m → Bool, f (Function.update x i (!x i)) ≠ f x) (hoi : o ≠ (i : ℕ)) :
    ∃ q, Reads gs q i := by
  by_contra hno
  have hno' : ∀ g ∈ gs, (i : ℕ) ∉ g.inputs := by
    intro g hg hi
    obtain ⟨q, hq⟩ := List.mem_iff_getElem?.1 hg
    exact hno ⟨q, g, hq, hi⟩
  obtain ⟨x, hx⟩ := hd
  apply hx
  rw [← hev, ← hev]
  refine agree_except i gs _ _ hno' (by simp) ?_ o hoi
  intro j hj
  by_cases hjm : j < m
  · rw [show (List.ofFn (Function.update x i (!x i))).getD j false
        = Function.update x i (!x i) ⟨j, hjm⟩ from getD_ofFn m _ false ⟨j, hjm⟩,
      show (List.ofFn x).getD j false = x ⟨j, hjm⟩ from getD_ofFn m x false ⟨j, hjm⟩]
    exact Function.update_of_ne (fun e => hj (congrArg Fin.val e)) _ _
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
lemma live (hRem : ToolRemoval) {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hL : MLeast m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) {p : ℕ} (hp : p < gs.length)
    (ho : o ≠ m + p) : ∃ q, Reads gs q (m + p) := by
  by_contra hno
  have hrem : Removable m gs o Set.univ {p} (fun _ => none) := by
    intro p' hp'
    rw [Finset.mem_singleton] at hp'
    subst hp'
    refine ⟨hp, Or.inr ⟨rfl, ho, fun q hq => absurd ⟨q, hq⟩ hno, fun _ _ => by simp⟩⟩
  obtain ⟨gs', r, hcl', hnf', hlen, _, hval⟩ := hRem m gs o Set.univ {p} _ hL.1 hrem
  have hol := out_lt hL.2.2.1 hnc
  obtain ⟨_, hv⟩ := hval o hol (fun p' hp' _ => by
    rw [Finset.mem_singleton] at hp'
    subst hp'
    exact ho)
  have := hL.2.2.2 gs' (r o) hcl' (hnf' hL.2.1) (fun x => by
    rw [hv x (Set.mem_univ x)]
    exact hL.2.2.1 x)
  rw [Finset.card_singleton] at hlen
  omega
lemma elimAl (hRem : ToolRemoval) {m : ℕ} {f : (Fin m → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hL : MLeast m f gs o) (hnc : ∃ x y : Fin m → Bool, f x ≠ f y) (P : Set (Fin m → Bool))
    (S : Finset ℕ) (tgt : ℕ → ℕ)
    (hS : ∀ p ∈ S, p < gs.length ∧ tgt p < m + p ∧ ∀ x ∈ P, vl gs x (m + p) = vl gs x (tgt p)) :
    ∃ (gs' : List Gate) (o' : ℕ), MClean m gs' ∧ gs'.length + S.card ≤ gs.length ∧
      ∀ x ∈ P, vl gs' x o' = f x := by
  have hrem : Removable m gs o P S (fun p => some (tgt p)) := by
    intro p hp
    obtain ⟨h1, h2, h3⟩ := hS p hp
    exact ⟨h1, Or.inl ⟨tgt p, rfl, h2, h3⟩⟩
  obtain ⟨gs', r, hcl', hnf', hlen, _, hval⟩ := hRem m gs o P S _ hL.1 hrem
  obtain ⟨_, hv⟩ := hval o (out_lt hL.2.2.1 hnc) (fun p _ h => by simp at h)
  exact ⟨gs', r o, ⟨hcl', hnf' hL.2.1⟩, hlen, fun x hx => by rw [hv x hx]; exact hL.2.2.1 x⟩
lemma afree_del {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} (h : AFree G A)
    (X : Finset (Fin n)) : AFree (delV G X) A :=
  fun i j hij => h i j ((delV_adj G X i j).1 hij).1
lemma payR (hR : ToolRestrict) {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)}
    (hih : IH G A) {G' : SimpleGraph (Fin n)} {A' : Finset (Fin n)} (hle : G' ≤ G)
    (hfree : AFree G' A')
    (hlt : G'.edgeSet.ncard < G.edgeSet.ncard ∨ (G' = G ∧ A'.card < A.card)) (i : Fin n)
    (b : Bool) (hres : ∀ x, F G A (Function.update x i b) = F G' A' x)
    (hnc : A'.Nonempty ∨ ∃ i j, G'.Adj i j) {gs' : List Gate} {o' : ℕ} (hcl : MClean n gs')
    (hcomp : ∀ x : Fin n → Bool, x i = b → vl gs' x o' = F G A x) :
    Phi1 G' A' ≤ gs'.length + 1 := by
  have hf : ∀ x, vl gs' (Function.update x i b) o' = F G' A' x := by
    intro x
    rw [hcomp _ (by simp), hres]
  have hnc' : ∃ x y : Fin n → Bool,
      vl gs' (Function.update x i b) o' ≠ vl gs' (Function.update y i b) o' := by
    obtain ⟨x, y, h⟩ := F_nc G' A' hnc
    exact ⟨x, y, by rw [hf, hf]; exact h⟩
  have hM := hR n gs' o' i b hcl hnc'
  have e : (fun x => vl gs' (Function.update x i b) o') = F G' A' := funext hf
  rw [e] at hM
  exact hih G' A' hle hfree hlt _ hM
lemma pt_eq {m : ℕ} (S : Finset (Fin m)) (i : Fin m) : pt S i = decide (i ∈ S) := rfl
lemma ToolPay0_proof (hR : ToolRestrict) (hRes0 : ToolRes0) (hD0 : ToolDrop0) : ToolPay0 := by
  intro n G A gs o v u1 u2 gs' o' hc hvu hN hne hcl hlen hcomp
  have hvA : v ∉ A := hc.inv v u1 hvu
  have h0 := hD0 n G A v u1 u2 hvu hN
  have hnc : A.Nonempty ∨ ∃ i j, (delV G {v}).Adj i j := by
    rcases hne with h | ⟨i, j, h, hi, hj⟩
    · exact Or.inl h
    · exact Or.inr ⟨i, j, (delV_adj G {v} i j).2 ⟨h, by simpa using hi, by simpa using hj⟩⟩
  have := payR hR hc.ih (delV_le G {v}) (afree_del hc.inv {v}) (Or.inl h0.2) v false
    (fun x => hRes0 n G A v x hvA) hnc hcl hcomp
  have := hc.small
  omega
lemma ToolPay1_proof (hR : ToolRestrict) (hRes1 : ToolRes1) (hD1 : ToolDrop1) : ToolPay1 := by
  intro n G A gs o v gs' o' hc hd hcl hlen hcomp
  obtain ⟨u1, u2, c1, c2, _, hN, h1, h2, _⟩ := hd
  have hvu : G.Adj v u1 := (hN u1).2 (Or.inl rfl)
  have hvA : v ∉ A := hc.inv v u1 hvu
  have hu1 : u1 ∉ A := hc.inv u1 v hvu.symm
  have hu2 : u2 ∉ A := hc.inv u2 v ((hN u2).2 (Or.inr rfl)).symm
  have hN' : ∀ w, G.Adj v w ↔ w ∈ ({u1, u2} : Finset (Fin n)) := by
    intro w
    rw [hN]
    simp
  have h0 := hD1 n G A v u1 u2 c1 c2 hN h1 h2 hu1 hu2
  have hfree : AFree (delV G (insert v {u1, u2})) (A ∪ {u1, u2}) := by
    intro i j hij hi
    rw [delV_adj] at hij
    rw [Finset.mem_union] at hi
    rcases hi with hi | hi
    · exact hc.inv i j hij.1 hi
    · exact hij.2.1 (Finset.mem_insert_of_mem hi)
  have := payR hR hc.ih (delV_le G _) hfree (Or.inl h0.2) v true
    (fun x => hRes1 n G A v {u1, u2} x hvA hN') (Or.inl ⟨u1, by simp⟩) hcl hcomp
  have := hc.small
  omega
lemma ToolPayPair_proof (hR : ToolRestrict) (hLeast : ToolLeast) (hResP : ToolResPair)
    (hDP : ToolDropPair) : ToolPayPair := by
  intro n G A gs o a' a s t b b' gs' o' hc hrun hcl hlen hcomp
  have nd := hrun.nd
  have hst : s ≠ t := by rintro rfl; simp at nd
  have hbs : b ≠ s := by rintro rfl; simp at nd
  have hstb : [s, t, b].Nodup := by
    simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true] at nd ⊢
    tauto
  have hadj_st : G.Adj s t := (hrun.hs t).2 (Or.inr rfl)
  have hadj_tb : G.Adj t b := (hrun.ht b).2 (Or.inr rfl)
  have hsA : s ∉ A := hc.inv s t hadj_st
  have htA : t ∉ A := hc.inv t s hadj_st.symm
  have hbA : b ∉ A := hc.inv b t hadj_tb.symm
  have h0 := hDP n G A a s t b b' hstb (fun w hw => (hrun.hs w).1 hw) hrun.ht
    (fun w hw => (hrun.hb w).1 hw) hbA
  set G2 := delV G {s, t, b} with hG2
  have hfree : AFree G2 (insert b A) := by
    intro i j hij hi
    rw [hG2, delV_adj] at hij
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact hij.2.1 (by simp)
    · exact hc.inv i j hij.1 hi
  have hkey : ∀ x, vl gs' (Function.update (Function.update x s false) t true) o' =
      F G2 (insert b A) x := by
    intro x
    rw [hcomp _ (by simp) (by rw [Function.update_of_ne hst]; simp),
      Function.update_comm hst]
    exact hResP n G A s t b x hst hbs hsA htA hbA hrun.ht
  obtain ⟨x0, y0, hxy⟩ := F_nc G2 (insert b A) (Or.inl (Finset.insert_nonempty _ _))
  have hnc1 : ∃ x y : Fin n → Bool,
      vl gs' (Function.update x t true) o' ≠ vl gs' (Function.update y t true) o' :=
    ⟨Function.update x0 s false, Function.update y0 s false, by rw [hkey, hkey]; exact hxy⟩
  have hM1 := hR n gs' o' t true hcl hnc1
  obtain ⟨x1, y1, hxy1⟩ := hnc1
  obtain ⟨gs2, o2, hL2, hlen2⟩ := hLeast n _ _ ⟨x1, y1, hxy1⟩ hM1
  have hev2 : ∀ x, vl gs2 (Function.update x s false) o2 = F G2 (insert b A) x := by
    intro x
    rw [hL2.2.2.1]
    exact hkey x
  have hnc2 : ∃ x y : Fin n → Bool,
      vl gs2 (Function.update x s false) o2 ≠ vl gs2 (Function.update y s false) o2 :=
    ⟨x0, y0, by rw [hev2, hev2]; exact hxy⟩
  have hM2 := hR n gs2 o2 s false hL2.clean hnc2
  have e : (fun x => vl gs2 (Function.update x s false) o2) = F G2 (insert b A) := funext hev2
  rw [e] at hM2
  have := hc.ih G2 (insert b A) (delV_le G _) hfree (Or.inl h0.2) _ hM2
  have := hc.small
  omega
lemma PBase_proof : PBase := by
  intro n G A hE s hM
  have hdep := PermInputs.dep_lower_set n (F G A) A (fun a ha => F_dep_A G A a ha) s hM.has
  have he := noedge_ncard G hE
  have ht := tau_le G ∅ (fun i j h => absurd h (hE i j))
  rw [Finset.card_empty] at ht
  unfold Phi1
  omega
lemma PS1_proof (hLeast : ToolLeast) (hRem : ToolRemoval) (hR : ToolRestrict)
    (hResA : ToolResA) : PS1 := by
  intro n G A hinv hih hA hE s hM
  by_contra hlt
  have hnc := F_nc G A (Or.inl hA)
  obtain ⟨gs, o, hL, hlen⟩ := hLeast n (F G A) s hnc hM
  obtain ⟨a, ha⟩ := hA
  obtain ⟨i, j, hij⟩ := hE
  have hia : i ≠ a := fun e => hinv i j hij (e ▸ ha)
  have hja : j ≠ a := fun e => hinv j i hij.symm (e ▸ ha)
  have hoa : o ≠ (a : ℕ) := out_ne hL.2.2.1 a (pt {i, j}) (by
    rw [pt_eq]
    have : F G A (pt {i, j}) = true := by
      rw [F_true]
      exact Or.inr ⟨i, j, hij, by simp [pt], by simp [pt]⟩
    rw [this]
    simp [hia.symm, hja.symm])
  obtain ⟨q, hq⟩ := read_of_dep hL.2.2.1 a (F_dep_A G A a ha) hoa
  obtain ⟨t, ht, hal⟩ := alias_of_rd hL.1 hL.2.1 hq {x | x a = false} false (fun x hx => by
    rw [vl_input gs x a a.isLt]
    exact hx)
  obtain ⟨gs', o', hcl', hlen', hcomp⟩ := elimAl hRem hL hnc {x | x a = false} {q} (fun _ => t)
    (fun p hp => by
      rw [Finset.mem_singleton] at hp
      subst hp
      exact ⟨reads_len hq, ht, hal⟩)
  have hfree : AFree G (A.erase a) := fun i j h hi => hinv i j h (Finset.mem_of_mem_erase hi)
  have := payR hR hih (le_refl G) hfree (Or.inr ⟨rfl, Finset.card_erase_lt_of_mem ha⟩) a false
    (fun x => hResA n G A a x hinv ha) (Or.inr ⟨i, j, hij⟩) hcl' (fun x hx => hcomp x hx)
  rw [Finset.card_singleton] at hlen'
  have hc := Finset.card_erase_add_one ha
  unfold Phi1 at this hlt
  omega
lemma del_leaf {n : ℕ} (G : SimpleGraph (Fin n)) (l p : Fin n)
    (hleaf : ∀ w, G.Adj l w → w = p) : delV G {l} = G.deleteEdges {s(l, p)} := by
  ext i j
  rw [delV_adj, deleteEdges_adj]
  simp only [Finset.mem_singleton, Set.mem_singleton_iff, Sym2.eq_iff]
  constructor
  · rintro ⟨h, hi, hj⟩
    refine ⟨h, ?_⟩
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hi rfl
    · exact hj rfl
  · rintro ⟨h, hne⟩
    refine ⟨h, ?_, ?_⟩
    · rintro rfl
      exact hne (Or.inl ⟨rfl, hleaf j h⟩)
    · rintro rfl
      exact hne (Or.inr ⟨hleaf i h.symm, rfl⟩)
lemma del_leaf2 {n : ℕ} (G : SimpleGraph (Fin n)) (l p q : Fin n)
    (hleaf : ∀ w, G.Adj l w → w = p) (hp : ∀ w, G.Adj p w → w = l ∨ w = q) :
    delV G (insert l {p}) = G.deleteEdges {s(p, l), s(p, q)} := by
  ext i j
  rw [delV_adj, deleteEdges_adj]
  constructor
  · rintro ⟨h, hi, hj⟩
    refine ⟨h, fun he => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff] at he
    rcases he with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) | (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> simp at hi hj
  · rintro ⟨h, hne⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Sym2.eq_iff, not_or] at hne
    refine ⟨h, ?_, ?_⟩ <;> simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    · refine ⟨fun e => ?_, fun e => ?_⟩
      · subst e
        have := hleaf j h
        subst this
        simp at hne
      · subst e
        rcases hp j h with rfl | rfl <;> simp at hne
    · refine ⟨fun e => ?_, fun e => ?_⟩
      · subst e
        have := hleaf i h.symm
        subst this
        simp at hne
      · subst e
        rcases hp i h.symm with rfl | rfl <;> simp at hne
lemma drop_leaf0 {n : ℕ} (G : SimpleGraph (Fin n)) (l p : Fin n) (hlp : G.Adj l p)
    (hleaf : ∀ w, G.Adj l w → w = p) :
    Phi1 G ∅ ≤ Phi1 (delV G {l}) ∅ + 2 ∧ (delV G {l}).edgeSet.ncard < G.edgeSet.ncard := by
  rw [del_leaf G l p hleaf]
  have he := ncard_del1 G l p hlp
  obtain ⟨T, hT, hTc⟩ := tau_attained (G.deleteEdges {s(l, p)})
  have hc := tau_le G _ (cov_insert G _ p (fun e he => by
    rw [Set.mem_singleton_iff] at he
    subst he
    exact Sym2.mem_mk_right _ _) T hT)
  have := Finset.card_insert_le p T
  unfold Phi1
  constructor <;> omega
lemma drop_leaf1 {n : ℕ} (G : SimpleGraph (Fin n)) (l p q : Fin n) (hlp : G.Adj l p)
    (hleaf : ∀ w, G.Adj l w → w = p) (hp : ∀ w, G.Adj p w → w = l ∨ w = q) :
    Phi1 G ∅ ≤ Phi1 (delV G (insert l {p})) (∅ ∪ {p}) + 2 ∧
      (delV G (insert l {p})).edgeSet.ncard < G.edgeSet.ncard := by
  rw [del_leaf2 G l p q hleaf hp]
  obtain ⟨he1, he2⟩ := ncard_del2 G l p q hlp
  obtain ⟨T, hT, hTc⟩ := tau_attained (G.deleteEdges {s(p, l), s(p, q)})
  have hc := tau_le G _ (cov_insert G _ p (fun e he => by
    rcases he with rfl | he
    · exact Sym2.mem_mk_left _ _
    · rw [Set.mem_singleton_iff] at he
      subst he
      exact Sym2.mem_mk_left _ _) T hT)
  have := Finset.card_insert_le p T
  unfold Phi1
  simp only [Finset.empty_union, Finset.card_singleton, Finset.card_empty]
  constructor <;> omega
lemma PTwin_proof (hLeast : ToolLeast) (hRem : ToolRemoval) (hR : ToolRestrict)
    (hRes0 : ToolRes0) : PTwin := by
  intro n G A l p l' hinv hih hA0 hlp hleaf hpl' hl'l hleaf' s hM
  subst hA0
  by_contra hlt
  have hnc := F_nc G ∅ (Or.inr ⟨l, p, hlp⟩)
  obtain ⟨gs, o, hL, hlen⟩ := hLeast n (F G ∅) s hnc hM
  have hpl : p ≠ l := hlp.ne.symm
  have hpl'0 : (delV G {l}).Adj p l' := (delV_adj G {l} p l').2 ⟨hpl', by simpa using hpl,
    by simpa using hl'l⟩
  have hol : o ≠ (l : ℕ) := out_ne hL.2.2.1 l (pt {p, l'}) (by
    rw [pt_eq]
    have : F G ∅ (pt {p, l'}) = true := by
      rw [F_true]
      exact Or.inr ⟨p, l', hpl', by simp [pt], by simp [pt]⟩
    rw [this]
    simp [hpl.symm, hl'l.symm])
  obtain ⟨q, hq⟩ := read_of_dep hL.2.2.1 l (F_dep G ∅ l p hlp (by simp)) hol
  obtain ⟨t, ht, hal⟩ := alias_of_rd hL.1 hL.2.1 hq {x | x l = false} false (fun x hx => by
    rw [vl_input gs x l l.isLt]
    exact hx)
  obtain ⟨gs', o', hcl', hlen', hcomp⟩ := elimAl hRem hL hnc {x | x l = false} {q} (fun _ => t)
    (fun p hp => by
      rw [Finset.mem_singleton] at hp
      subst hp
      exact ⟨reads_len hq, ht, hal⟩)
  have hdel := del_leaf G l p hleaf
  have he := ncard_del1 G l p hlp
  rw [← hdel] at he
  have := payR hR hih (delV_le G {l}) (afree_del hinv {l}) (Or.inl (by omega)) l false
    (fun x => hRes0 n G ∅ l x (by simp)) (Or.inr ⟨p, l', hpl'0⟩) hcl' (fun x hx => hcomp x hx)
  have htau : tau G ≤ tau (delV G {l}) := by
    obtain ⟨T, hT, hTc⟩ := tau_attained (delV G {l})
    rw [← hTc]
    rw [hdel] at hT
    exact cov_swap G l p l' (tau G) hl'l hpl' hleaf' (fun T h => tau_le G T h) T hT
  rw [Finset.card_singleton] at hlen'
  unfold Phi1 at this hlt
  omega
lemma PLeafLow_proof (hLeast : ToolLeast) (hRem : ToolRemoval) (hR : ToolRestrict)
    (hRes0 : ToolRes0) (hRes1 : ToolRes1) : PLeafLow := by
  intro n G A l p q hinv hih hA0 hlp hleaf hp s hM
  subst hA0
  by_contra hlt
  have hpl : p ≠ l := hlp.ne.symm
  obtain ⟨d0, d0e⟩ := drop_leaf0 G l p hlp hleaf
  obtain ⟨d1, d1e⟩ := drop_leaf1 G l p q hlp hleaf hp
  by_cases hE0 : ∃ i j, (delV G {l}).Adj i j
  swap
  ·
    have hE0' : ∀ i j, ¬ (delV G {l}).Adj i j := fun i j h => hE0 ⟨i, j, h⟩
    have he := noedge_ncard _ hE0'
    have ht := tau_le (delV G {l}) ∅ (fun i j h => absurd h (hE0' i j))
    have hdep := PermInputs.dep_lower_set n (F G ∅) {l, p} (by
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact F_dep G ∅ i p hlp (by simp)
      · rw [Finset.mem_singleton] at hi
        subst hi
        exact F_dep G ∅ i l hlp.symm (by simp)) s hM.has
    rw [Finset.card_pair hlp.ne] at hdep
    unfold Phi1 at d0 hlt
    rw [Finset.card_empty] at ht d0 hlt
    omega
  obtain ⟨i, j, hij⟩ := hE0
  obtain ⟨hijG, hil, hjl⟩ := (delV_adj G {l} i j).1 hij
  have hil' : i ≠ l := by simpa using hil
  have hjl' : j ≠ l := by simpa using hjl
  have hnc := F_nc G ∅ (Or.inr ⟨l, p, hlp⟩)
  obtain ⟨gs, o, hL, hlen⟩ := hLeast n (F G ∅) s hnc hM
  have hFij : F G ∅ (pt {i, j}) = true := by
    rw [F_true]
    exact Or.inr ⟨i, j, hijG, by simp [pt], by simp [pt]⟩
  have hFl : F G ∅ (pt {l}) = false := by
    rw [Bool.eq_false_iff, ne_eq, F_true]
    rintro (⟨a, ha, _⟩ | ⟨a, b, hab, ha, hb⟩)
    · simp at ha
    · simp [pt] at ha hb
      subst ha
      subst hb
      exact hab.ne rfl
  have hptl : pt {i, j} l = false := by
    rw [pt_eq]
    simp [hil'.symm, hjl'.symm]
  have hol : o ≠ (l : ℕ) := out_ne hL.2.2.1 l (pt {i, j}) (by rw [hFij, hptl]; simp)
  have key : ∀ (c : Bool) (S : Finset ℕ) (tgt : ℕ → ℕ), 2 ≤ S.card →
      (∀ r ∈ S, r < gs.length ∧ tgt r < n + r ∧
        ∀ x ∈ {x : Fin n → Bool | x l = c}, vl gs x (n + r) = vl gs x (tgt r)) → False := by
    intro c S tgt hS2 hS
    obtain ⟨gs', o', hcl', hlen', hcomp⟩ := elimAl hRem hL hnc _ S tgt hS
    cases c
    · have := payR hR hih (delV_le G {l}) (afree_del hinv {l}) (Or.inl d0e) l false
        (fun x => hRes0 n G ∅ l x (by simp)) (Or.inr ⟨i, j, hij⟩) hcl'
        (fun x hx => hcomp x hx)
      omega
    · have hN : ∀ w, G.Adj l w ↔ w ∈ ({p} : Finset (Fin n)) := by
        intro w
        rw [Finset.mem_singleton]
        exact ⟨hleaf w, fun h => h ▸ hlp⟩
      have hfree : AFree (delV G (insert l {p})) (∅ ∪ {p}) := by
        intro a b hab ha
        rw [delV_adj] at hab
        rw [Finset.empty_union] at ha
        exact hab.2.1 (Finset.mem_insert_of_mem ha)
      have := payR hR hih (delV_le G _) hfree (Or.inl d1e) l true
        (fun x => hRes1 n G ∅ l {p} x (by simp) hN) (Or.inl ⟨p, by simp⟩) hcl'
        (fun x hx => hcomp x hx)
      omega
  obtain ⟨r, hr⟩ := read_of_dep hL.2.2.1 l (F_dep G ∅ l p hlp (by simp)) hol
  by_cases h2 : ∃ r', r' ≠ r ∧ Reads gs r' l
  ·
    obtain ⟨r', hr'r, hr'⟩ := h2
    have hc0 : ∀ x ∈ {x : Fin n → Bool | x l = false}, vl gs x l = false := fun x hx => by
      rw [vl_input gs x l l.isLt]
      exact hx
    obtain ⟨t, ht, hal⟩ := alias_of_rd hL.1 hL.2.1 hr _ false hc0
    obtain ⟨t', ht', hal'⟩ := alias_of_rd hL.1 hL.2.1 hr' _ false hc0
    refine key false {r, r'} (fun z => if z = r then t else t') (by
      rw [Finset.card_pair hr'r.symm]) ?_
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · exact ⟨reads_len hr, by simp [ht], fun x hx => by simp [hal x hx]⟩
    · rw [Finset.mem_singleton] at hz
      subst hz
      exact ⟨reads_len hr', by simp [hr'r, ht'], fun x hx => by simp [hr'r, hal' x hx]⟩
  ·
    obtain ⟨c, hcst⟩ := abs_rd hL.1 hL.2.1 hr
    have hcst' : ∀ x : Fin n → Bool, x l = c → vl gs x (n + r) = c := fun x hx =>
      hcst x (by rw [vl_input gs x l l.isLt]; exact hx)
    have hor : o ≠ n + r := by
      intro e
      cases c
      · have := hcst' (pt {i, j}) hptl
        rw [← e, hL.2.2.1, hFij] at this
        exact Bool.noConfusion this
      · have := hcst' (pt {l}) (by simp [pt])
        rw [← e, hL.2.2.1, hFl] at this
        exact Bool.noConfusion this
    obtain ⟨r2, hr2⟩ := live hRem hL hnc (reads_len hr) hor
    have hr2r : r2 ≠ r := by
      intro e
      have := reads_lt hL.1 hr2
      omega
    obtain ⟨t2, ht2, hal2⟩ := alias_of_rd hL.1 hL.2.1 hr2 {x | x l = c} c
      (fun x hx => hcst' x hx)
    refine key c {r, r2} (fun z => if z = r then (l : ℕ) else t2) (by
      rw [Finset.card_pair hr2r.symm]) ?_
    intro z hz
    rcases Finset.mem_insert.1 hz with rfl | hz
    · refine ⟨reads_len hr, by simp; omega, fun x hx => ?_⟩
      simp only [ite_true]
      rw [hcst' x hx, vl_input gs x l l.isLt]
      exact hx.symm
    · rw [Finset.mem_singleton] at hz
      subst hz
      exact ⟨reads_len hr2, by simp [hr2r, ht2], fun x hx => by simp [hr2r, hal2 x hx]⟩
end PEqualNP.Outside.L_meta_3457.SparseLower.Loc.Free

namespace PEqualNP.Outside.L_meta_3457.SparseLower.Loc.Struct
open SimpleGraph
open PEqualNP.Outside.L_meta_3457.SparseLower.Loc
variable {n : ℕ}
def Two (G : SimpleGraph (Fin n)) (w : Fin n) : Prop :=
  ∃ a b, a ≠ b ∧ ∀ x, G.Adj w x ↔ x = a ∨ x = b
lemma classify (G : SimpleGraph (Fin n)) (w : Fin n) :
    Two G w ∨ 3 ≤ (G.neighborSet w).ncard ∨ ∃ a, ∀ x, G.Adj w x → x = a := by
  rcases Nat.lt_or_ge (G.neighborSet w).ncard 3 with h | h
  · obtain h0 | h1 | h2 : (G.neighborSet w).ncard = 0 ∨ (G.neighborSet w).ncard = 1 ∨
        (G.neighborSet w).ncard = 2 := by omega
    · right; right
      refine ⟨w, fun x hx => ?_⟩
      rw [Set.ncard_eq_zero] at h0
      have : x ∈ G.neighborSet w := hx
      rw [h0] at this
      exact absurd this (Set.notMem_empty x)
    · right; right
      obtain ⟨a, ha⟩ := Set.ncard_eq_one.1 h1
      refine ⟨a, fun x hx => ?_⟩
      have : x ∈ G.neighborSet w := hx
      rw [ha] at this
      exact this
    · left
      obtain ⟨a, b, hab, he⟩ := Set.ncard_eq_two.1 h2
      refine ⟨a, b, hab, fun x => ?_⟩
      have : x ∈ G.neighborSet w ↔ x ∈ ({a, b} : Set (Fin n)) := by rw [he]
      simpa using this
  · right; left; exact h
lemma two_adj {G : SimpleGraph (Fin n)} {w m1 m2 : Fin n} (hw : Two G w) (h1 : G.Adj w m1)
    (h2 : G.Adj w m2) (hne : m1 ≠ m2) : ∀ x, G.Adj w x ↔ x = m1 ∨ x = m2 := by
  obtain ⟨a, b, hab, h⟩ := hw
  have e1 := (h m1).1 h1
  have e2 := (h m2).1 h2
  intro x
  constructor
  · intro hx
    rcases (h x).1 hx with rfl | rfl <;> rcases e1 with rfl | rfl <;>
      rcases e2 with rfl | rfl <;> simp_all
  · rintro (rfl | rfl) <;> assumption
lemma two_other {G : SimpleGraph (Fin n)} {w m : Fin n} (hw : Two G w) (hm : G.Adj w m) :
    ∃ c, c ≠ m ∧ G.Adj w c ∧ ∀ x, G.Adj w x ↔ x = m ∨ x = c := by
  obtain ⟨a, b, hab, h⟩ := hw
  rcases (h m).1 hm with rfl | rfl
  · exact ⟨b, hab.symm, (h b).2 (Or.inr rfl), h⟩
  · exact ⟨a, hab, (h a).2 (Or.inl rfl), fun x => (h x).trans Or.comm⟩
lemma two_three {G : SimpleGraph (Fin n)} {w p q r : Fin n} (hw : Two G w) (hp : G.Adj w p)
    (hq : G.Adj w q) (hr : G.Adj w r) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : False := by
  have := (two_adj hw hp hq hpq r).1 hr
  rcases this with rfl | rfl
  · exact hpr rfl
  · exact hqr rfl
structure Good (G : SimpleGraph (Fin n)) (u x : Fin n) (q : G.Walk x u) : Prop where
  path : q.IsPath
  pos : 1 ≤ q.length
  two : ∀ i, i < q.length → Two G (q.getVert i)
lemma exists_max (G : SimpleGraph (Fin n)) (u : Fin n)
    (h : ∃ x, ∃ q : G.Walk x u, Good G u x q) :
    ∃ x, ∃ q : G.Walk x u, Good G u x q ∧
      ∀ y (r : G.Walk y u), Good G u y r → r.length ≤ q.length := by
  classical
  let P : ℕ → Prop := fun k => ∃ x, ∃ q : G.Walk x u, Good G u x q ∧ q.length = k
  have hb : ∀ k, P k → k ≤ n := by
    rintro k ⟨x, q, hq, rfl⟩
    have := hq.path.length_lt
    rw [Fintype.card_fin] at this
    omega
  obtain ⟨x, q, hq⟩ := h
  have hP : P (Nat.findGreatest P n) :=
    Nat.findGreatest_spec (hb _ ⟨x, q, hq, rfl⟩) ⟨x, q, hq, rfl⟩
  obtain ⟨y, r, hr, hrl⟩ := hP
  refine ⟨y, r, hr, fun z s hs => ?_⟩
  rw [hrl]
  exact Nat.le_findGreatest (hb _ ⟨z, s, hs, rfl⟩) ⟨z, s, hs, rfl⟩
lemma gv_ne {G : SimpleGraph (Fin n)} {x u : Fin n} {q : G.Walk x u} (hq : q.IsPath) {i j : ℕ}
    (hi : i ≤ q.length) (hj : j ≤ q.length) (hij : i ≠ j) : q.getVert i ≠ q.getVert j :=
  fun h => hij (hq.getVert_injOn (Set.mem_setOf.2 hi) (Set.mem_setOf.2 hj) h)
lemma thread (G : SimpleGraph (Fin n)) (hL : InL G)
    (h1 : ¬ ∃ l p q, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ ∀ w, G.Adj p w → w = l ∨ w = q)
    (u v : Fin n) (hvu : G.Adj v u) (hv : Two G v)
    (hbr : 3 ≤ (G.neighborSet u).ncard ∨ ∀ w, ¬ 3 ≤ (G.neighborSet w).ncard) :
    ∃ x, ∃ q : G.Walk x u, Good G u x q ∧ 6 ≤ q.length := by
  have h0 : Good G u v (Walk.cons hvu Walk.nil) := by
    refine ⟨?_, by simp, fun i hi => ?_⟩
    · rw [Walk.cons_isPath_iff]
      exact ⟨Walk.IsPath.nil, by simpa using hvu.ne⟩
    · simp at hi
      subst hi
      simpa using hv
  obtain ⟨x, q, hq, hmax⟩ := exists_max G u ⟨v, _, h0⟩
  refine ⟨x, q, hq, ?_⟩
  by_contra hlt
  push_neg at hlt
  have hk := hq.pos
  have hxy : G.Adj x (q.getVert 1) := by
    simpa using q.adj_getVert_succ (i := 0) (by omega)
  have hx : Two G x := by simpa using hq.two 0 (by omega)
  obtain ⟨z, hzy, hxz, hxN⟩ := two_other hx hxy
  have hxu : x ≠ u := by
    have := gv_ne hq.path (i := 0) (j := q.length) (by omega) le_rfl (by omega)
    simpa using this
  by_cases hzu : z = u
  · subst hzu
    have hux : G.Adj z x := hxz.symm
    have hne : s(z, x) ∉ q.edges := by
      intro hmem
      have hy1 := hzy
      have hp := hq.path
      clear hmax h0 hxN hlt hk hq
      cases q with
      | nil => exact hxu rfl
      | @cons _ y' _ h q' =>
        simp only [Walk.edges_cons, List.mem_cons] at hmem
        rw [Walk.cons_isPath_iff] at hp
        simp only [Walk.getVert_cons_succ, Walk.getVert_zero] at hy1
        rcases hmem with he | he
        · rcases Sym2.eq_iff.1 he with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact hxu h1.symm
          · exact hy1 h1
        · exact hp.2 (q'.snd_mem_support_of_mem_edges he)
    have hc : (Walk.cons hux q).IsCycle := (Walk.cons_isCycle_iff q hux).2 ⟨hq.path, hne⟩
    have := hL.1 z _ hc
    simp only [Walk.length_cons] at this
    omega
  · rcases classify G z with hz | hz | ⟨a, ha⟩
    · by_cases hzs : z ∈ q.support
      · obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.1 hzs
        have hi0 : i ≠ 0 := by
          rintro rfl
          simp only [Walk.getVert_zero] at hi
          exact hxz.ne hi
        have hi1 : i ≠ 1 := by
          rintro rfl
          exact hzy hi.symm
        have hik : i ≠ q.length := by
          rintro rfl
          rw [Walk.getVert_length] at hi
          exact hzu hi.symm
        have hA : G.Adj z (q.getVert (i - 1)) := by
          have := q.adj_getVert_succ (i := i - 1) (by omega)
          rw [show i - 1 + 1 = i by omega, hi] at this
          exact this.symm
        have hB : G.Adj z (q.getVert (i + 1)) := by
          have := q.adj_getVert_succ (i := i) (by omega)
          rw [hi] at this
          exact this
        have hC : G.Adj z (q.getVert 0) := by
          rw [Walk.getVert_zero]
          exact hxz.symm
        exact two_three hz hA hB hC (gv_ne hq.path (by omega) (by omega) (by omega))
          (gv_ne hq.path (by omega) (by omega) (by omega))
          (gv_ne hq.path (by omega) (by omega) (by omega))
      · have hg : Good G u z (Walk.cons hxz.symm q) := by
          refine ⟨(Walk.cons_isPath_iff _ _).2 ⟨hq.path, hzs⟩, by simp, fun i hi => ?_⟩
          rcases i with _ | j
          · simpa using hz
          · rw [Walk.getVert_cons_succ]
            simp only [Walk.length_cons] at hi
            exact hq.two j (by omega)
        have := hmax z _ hg
        simp only [Walk.length_cons] at this
        omega
    · rcases hbr with hu | hno
      · have := hL.2 z u hzu hz hu (Walk.cons hxz.symm q)
        simp only [Walk.length_cons] at this
        omega
      · exact hno z hz
    · have hax : x = a := ha x hxz.symm
      exact h1 ⟨z, x, q.getVert 1, hxz.symm, fun w hw => (ha w hw).trans hax.symm,
        fun w hw => ((hxN w).1 hw).symm⟩
lemma run_of_thread {G : SimpleGraph (Fin n)} {x u : Fin n} {q : G.Walk x u}
    (hq : Good G u x q) (h6 : 6 ≤ q.length) : ∃ a' a s t b b', Run G a' a s t b b' := by
  have adj : ∀ j, j < 6 → G.Adj (q.getVert j) (q.getVert (j + 1)) :=
    fun j hj => q.adj_getVert_succ (by omega)
  have ne : ∀ i j, i ≤ 6 → j ≤ 6 → i ≠ j → q.getVert i ≠ q.getVert j :=
    fun i j hi hj hij => gv_ne hq.path (by omega) (by omega) hij
  have two : ∀ j, j ≤ 5 → Two G (q.getVert j) := fun j hj => hq.two j (by omega)
  refine ⟨q.getVert 0, q.getVert 1, q.getVert 2, q.getVert 3, q.getVert 4, q.getVert 5,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
      List.nodup_nil, and_true]
    refine ⟨⟨ne 0 1 ?_ ?_ ?_, ne 0 2 ?_ ?_ ?_, ne 0 3 ?_ ?_ ?_, ne 0 4 ?_ ?_ ?_, ne 0 5 ?_ ?_ ?_⟩,
      ⟨ne 1 2 ?_ ?_ ?_, ne 1 3 ?_ ?_ ?_, ne 1 4 ?_ ?_ ?_, ne 1 5 ?_ ?_ ?_⟩,
      ⟨ne 2 3 ?_ ?_ ?_, ne 2 4 ?_ ?_ ?_, ne 2 5 ?_ ?_ ?_⟩,
      ⟨ne 3 4 ?_ ?_ ?_, ne 3 5 ?_ ?_ ?_⟩, ⟨ne 4 5 ?_ ?_ ?_, fun h => h⟩⟩ <;> omega
  · exact two_adj (two 1 (by omega)) (adj 0 (by omega)).symm (adj 1 (by omega))
      (ne 0 2 (by omega) (by omega) (by omega))
  · exact two_adj (two 2 (by omega)) (adj 1 (by omega)).symm (adj 2 (by omega))
      (ne 1 3 (by omega) (by omega) (by omega))
  · exact two_adj (two 3 (by omega)) (adj 2 (by omega)).symm (adj 3 (by omega))
      (ne 2 4 (by omega) (by omega) (by omega))
  · exact two_adj (two 4 (by omega)) (adj 3 (by omega)).symm (adj 4 (by omega))
      (ne 3 5 (by omega) (by omega) (by omega))
  · obtain ⟨c, -, -, hc⟩ := two_other (two 0 (by omega)) (adj 0 (by omega))
    exact ⟨c, fun w hw => (hc w).1 hw⟩
  · obtain ⟨c, -, -, hc⟩ := two_other (two 5 (by omega)) (adj 4 (by omega)).symm
    exact ⟨c, fun w hw => (hc w).1 hw⟩
lemma PClosure_proof : PClosure := by
  intro n G G' hL hle
  refine ⟨fun v p hp => ?_, fun u v huv hu hv p => ?_⟩
  · have := hL.1 v (p.mapLe hle) (hp.mapLe hle)
    rwa [Walk.length_mapLe] at this
  · have hsub : ∀ w, G'.neighborSet w ⊆ G.neighborSet w := fun w y hy => hle hy
    have := hL.2 u v huv (le_trans hu (Set.ncard_le_ncard (hsub u)))
      (le_trans hv (Set.ncard_le_ncard (hsub v))) (p.mapLe hle)
    rwa [Walk.length_mapLe] at this
lemma PStructure_proof : PStructure := by
  intro n G hL ⟨i, j, hij⟩ h1 h2
  by_cases hb : ∃ u, 3 ≤ (G.neighborSet u).ncard
  · obtain ⟨u, hu⟩ := hb
    obtain ⟨m1, m2, -, hm1, hm2, -, hm12, -, -⟩ :=
      (Set.two_lt_ncard_iff (s := G.neighborSet u)).1 (by omega)
    have hm1 : G.Adj u m1 := hm1
    have hm2 : G.Adj u m2 := hm2
    have cl : ∀ m, G.Adj u m → Two G m ∨ ∀ w, G.Adj m w → w = u := by
      intro m hm
      rcases classify G m with h | h | ⟨a, ha⟩
      · exact Or.inl h
      · have := hL.2 u m hm.ne hu h (Walk.cons hm Walk.nil)
        simp at this
      · have hau : u = a := ha u hm.symm
        exact Or.inr fun w hw => (ha w hw).trans hau.symm
    have hv : ∃ v, G.Adj u v ∧ Two G v := by
      rcases cl m1 hm1 with h | h
      · exact ⟨m1, hm1, h⟩
      rcases cl m2 hm2 with h' | h'
      · exact ⟨m2, hm2, h'⟩
      exact absurd ⟨m1, u, m2, hm1.symm, h, hm2, hm12.symm, h'⟩ h2
    obtain ⟨v, huv, hv⟩ := hv
    obtain ⟨x, q, hq, h6⟩ := thread G hL h1 u v huv.symm hv (Or.inl hu)
    exact run_of_thread hq h6
  · push_neg at hb
    have nb : ∀ w, ¬ 3 ≤ (G.neighborSet w).ncard := fun w h => by have := hb w; omega
    have go : ∀ u v, G.Adj v u → Two G v → ∃ a' a s t b b', Run G a' a s t b b' := by
      intro u v hvu hv
      obtain ⟨x, q, hq, h6⟩ := thread G hL h1 u v hvu hv (Or.inr nb)
      exact run_of_thread hq h6
    rcases classify G j with hj | hj | ⟨a, ha⟩
    · exact go i j hij.symm hj
    · exact absurd hj (nb j)
    rcases classify G i with hi | hi | ⟨b, hb'⟩
    · exact go j i hij hi
    · exact absurd hi (nb i)
    have hai : i = a := ha i hij.symm
    exact absurd ⟨i, j, i, hij, fun w hw => (hb' w hw).trans (hb' j hij).symm,
      fun w hw => Or.inl ((ha w hw).trans hai.symm)⟩ h1
end PEqualNP.Outside.L_meta_3457.SparseLower.Loc.Struct

namespace PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
open PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Readers PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Forest
open PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.PermInputs
open PEqualNP.Outside.L_meta_3457.SparseLower.Loc
open SimpleGraph
def T7 {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length) ∧
    ∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard →
      ∀ p : G.Walk u v, 7 ≤ p.length
def GoodLeaf {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∃ l p : Fin n, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧
    ((∃ q, ∀ w, G.Adj p w → w = l ∨ w = q) ∨ (∃ l', l' ≠ l ∧ G.Adj p l' ∧ ∀ w, G.Adj l' w → w = p))
def Hered (P : (n : ℕ) → SimpleGraph (Fin n) → Prop) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (X : Finset (Fin n)), P n G → P n (delV G X)
def Dich (P : (n : ℕ) → SimpleGraph (Fin n) → Prop) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), P n G → (∃ i j, G.Adj i j) →
    GoodLeaf G ∨ ∃ a' a s t b b' : Fin n, Run G a' a s t b b'
def StmtG1 : Prop := Hered (fun _ G => T7 G)
def StmtG3 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin (n + 1))) (A : Finset (Fin (n + 1)))
    (a' a s t b b' : Fin (n + 1)), AFree G A → Run G a' a s t b b' →
    DeepHyp (F G A) {a, s, t, b} ∧ 2 ≤ ({a, s, t, b} : Finset (Fin (n + 1))).card
def StmtG4 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)), T7 G → (∃ i j, G.Adj i j) →
    (¬ ∃ l p q, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ ∀ w, G.Adj p w → w = l ∨ w = q) →
    (¬ ∃ l p l', G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ G.Adj p l' ∧ l' ≠ l ∧
      ∀ w, G.Adj l' w → w = p) →
    ∃ a' a s t b b', Run G a' a s t b b'
def IHV {n : ℕ} (G : SimpleGraph (Fin n)) : Prop :=
  ∀ (X A' : Finset (Fin n)), AFree (delV G X) A' →
    (delV G X).edgeSet.ncard < G.edgeSet.ncard → BoundOf (PEqualNP.MetaComplexity.HasCircuitSize n) (delV G X) A'
def StmtG6 : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), AFree G A → IHV G → GoodLeaf G →
    BoundOf (PEqualNP.MetaComplexity.HasCircuitSize n) G A
def StmtA1 (P : (n : ℕ) → SimpleGraph (Fin n) → Prop) : Prop :=
  ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), P n G → AFree G A →
    BoundOf (PEqualNP.MetaComplexity.HasCircuitSize n) G A
lemma stmtG1 : StmtG1 := by
  intro n G X hL
  have hle := delV_le G X
  refine ⟨fun v p hp => ?_, fun u v huv hu hv p => ?_⟩
  · have := hL.1 v (p.mapLe hle) (hp.mapLe hle)
    rwa [Walk.length_mapLe] at this
  · have hsub : ∀ w, (delV G X).neighborSet w ⊆ G.neighborSet w := fun w y hy => hle hy
    have := hL.2 u v huv (le_trans hu (Set.ncard_le_ncard (hsub u)))
      (le_trans hv (Set.ncard_le_ncard (hsub v))) (p.mapLe hle)
    rwa [Walk.length_mapLe] at this
lemma F_false_of {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {z : Fin n → Bool}
    (S : Finset (Fin n)) (hz : ∀ i, z i = true → i ∈ S) (hA : ∀ a ∈ A, a ∉ S)
    (hE : ∀ i j, G.Adj i j → i ∈ S → j ∉ S) : F G A z = false := by
  rw [Bool.eq_false_iff, ne_eq, F_true]
  rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
  · exact hA a ha (hz a h)
  · exact hE i j hij (hz i hi) (hz j hj)
lemma F_true_of {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {z : Fin n → Bool}
    (i j : Fin n) (hij : G.Adj i j) (hi : z i = true) (hj : z j = true) : F G A z = true :=
  (F_true G A z).2 (Or.inr ⟨i, j, hij, hi, hj⟩)
lemma F_mono {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} {z x : Fin n → Bool}
    (h : ∀ i, z i = true → x i = true) (hz : F G A z = true) : F G A x = true := by
  rw [F_true] at hz ⊢
  rcases hz with ⟨a, ha, h'⟩ | ⟨i, j, hij, hi, hj⟩
  · exact Or.inl ⟨a, ha, h a h'⟩
  · exact Or.inr ⟨i, j, hij, h i hi, h j hj⟩
lemma nc_of {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} (hinv : AFree G A)
    {y i j c : Fin n} (hij : G.Adj i j) (hi : i ≠ y) (hj : j ≠ y) (hyc : G.Adj y c) (b : Bool) :
    ∃ x x' : Fin n → Bool, F G A (Function.update x y b) ≠ F G A (Function.update x' y b) := by
  have hyA : y ∉ A := hinv y c hyc
  refine ⟨fun _ => true, fun _ => false, ?_⟩
  rw [F_true_of i j hij (by simp [Function.update_of_ne hi]) (by simp [Function.update_of_ne hj]),
    F_false_of {y} (fun k hk => by
      by_cases hk' : k = y
      · simp [hk']
      · simp [Function.update_of_ne hk'] at hk)
    (fun a ha h => by rw [Finset.mem_singleton] at h; exact hyA (h ▸ ha))
    (fun k l h hk hl => by
      rw [Finset.mem_singleton] at hk hl
      exact h.ne (hk.trans hl.symm))]
  simp
lemma nf_of {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} (hinv : AFree G A)
    {y y' c c' u1 u2 : Fin n} (hyy : y ≠ y') (hyc : G.Adj y c) (hcy' : c ≠ y')
    (hy' : ∀ w, G.Adj y' w → w = u1 ∨ w = u2) (hc1 : c ≠ u1) (hc2 : c ≠ u2)
    (hyc' : G.Adj y' c') (hc'y : c' ≠ y) : ¬ PairFunnel (F G A) y y' := by
  have hcA : c ∉ A := hinv c y hyc.symm
  have hy'A : y' ∉ A := hinv y' c' hyc'
  have hc'A : c' ∉ A := hinv c' y' hyc'.symm
  have hcy : c ≠ y := hyc.ne.symm
  have hc'y' : c' ≠ y' := hyc'.ne.symm
  have hncy' : ¬ G.Adj c y' := fun h => by
    rcases hy' c h.symm with h | h
    · exact hc1 h
    · exact hc2 h
  have f1 : ∀ d : Fin n, d ∉ A → ∀ z : Fin n → Bool, (∀ i, z i = true → i = d) →
      F G A z = false := fun d hd z hz =>
    F_false_of {d} (fun i hi => by rw [Finset.mem_singleton]; exact hz i hi)
      (fun a ha h => by rw [Finset.mem_singleton] at h; exact hd (h ▸ ha))
      (fun i j h hi hj => by
        rw [Finset.mem_singleton] at hi hj
        exact h.ne (hi.trans hj.symm))
  have T1 : F G A (set2 (pt {c}) y true y' false) = true :=
    F_true_of y c hyc (by simp [set2, hyy])
      (by simp [set2, pt, hcy, hcy'])
  have T2 : F G A (set2 (pt {c'}) y false y' true) = true :=
    F_true_of y' c' hyc' (by simp [set2])
      (by simp [set2, pt, hc'y, hc'y'])
  have Z1 : F G A (set2 (pt {c}) y false y' false) = false := f1 c hcA _ (fun i hi => by
    simp only [set2, Function.update_apply, pt] at hi
    split_ifs at hi <;> simp_all)
  have Z2 : F G A (set2 (pt {c'}) y false y' false) = false := f1 c' hc'A _ (fun i hi => by
    simp only [set2, Function.update_apply, pt] at hi
    split_ifs at hi <;> simp_all)
  have Z3 : F G A (set2 (pt {c}) y false y' true) = false := by
    refine F_false_of {c, y'} (fun i hi => ?_) (fun a ha h => ?_) (fun i j h hi hj => ?_)
    · simp only [set2, Function.update_apply, pt] at hi
      split_ifs at hi <;> simp_all
    · rw [Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · exact hcA (h ▸ ha)
      · exact hy'A (h ▸ ha)
    · rw [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
      · exact h.ne rfl
      · exact hncy' h
      · exact hncy' h.symm
      · exact h.ne rfl
  have h1 : ∃ x, F G A (set2 x y true y' false) ≠ F G A (set2 x y false y' false) :=
    ⟨pt {c}, by rw [T1, Z1]; simp⟩
  have h2 : ∃ x, F G A (set2 x y false y' true) ≠ F G A (set2 x y false y' false) :=
    ⟨pt {c'}, by rw [T2, Z2]; simp⟩
  have h3 : ∃ x, F G A (set2 x y true y' false) ≠ F G A (set2 x y false y' true) :=
    ⟨pt {c}, by rw [T1, Z3]; simp⟩
  obtain ⟨x1, h1⟩ := h1
  obtain ⟨x2, h2⟩ := h2
  obtain ⟨x3, h3⟩ := h3
  rintro ⟨a, b, hab⟩
  cases a <;> cases b
  · exact h3 (hab x3).1
  · exact h1 (hab x1).2.symm
  · exact h2 ((hab x2).1.trans (hab x2).2).symm
  · exact h1 (hab x1).2
lemma win_of {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} (hinv : AFree G A)
    {D : Finset (Fin n)} {y c : Fin n} (hy : y ∈ D) (hc : c ∈ D) (hyc : G.Adj y c)
    (hcD : ∀ w, G.Adj c w → w ∈ D) (x : Fin n → Bool) (hx : F G A (zeroOn D x) = false) :
    ∃ x' : Fin n → Bool, (∀ i, i ∉ D → x' i = x i) ∧ x' y = false ∧ F G A x' = false ∧
      F G A (Function.update x' y true) = true := by
  have hcA : c ∉ A := hinv c y hyc.symm
  have hz : ∀ i, i ≠ c → Function.update (zeroOn D x) c true i = zeroOn D x i :=
    fun i hi => Function.update_of_ne hi _ _
  have hbad : ∀ P : Prop, F G A (zeroOn D x) = true → P := fun P h => by
    rw [hx] at h; exact absurd h (by simp)
  refine ⟨Function.update (zeroOn D x) c true, fun i hi => ?_, ?_, ?_, ?_⟩
  · rw [hz i (fun h => hi (h ▸ hc))]
    simp [zeroOn, hi]
  · rw [hz y hyc.ne]
    simp [zeroOn, hy]
  · rw [Bool.eq_false_iff, ne_eq, F_true]
    rintro (⟨a, ha, h⟩ | ⟨i, j, hij, hi, hj⟩)
    · have hac : a ≠ c := fun e => hcA (e ▸ ha)
      rw [hz a hac] at h
      exact hbad _ ((F_true G A _).2 (Or.inl ⟨a, ha, h⟩))
    · by_cases hic : i = c
      · subst hic
        have hjc : j ≠ i := hij.ne.symm
        rw [hz j hjc] at hj
        simp [zeroOn, hcD j hij] at hj
      by_cases hjc : j = c
      · subst hjc
        rw [hz i hic] at hi
        simp [zeroOn, hcD i hij.symm] at hi
      rw [hz i hic] at hi
      rw [hz j hjc] at hj
      exact hbad _ ((F_true G A _).2 (Or.inr ⟨i, j, hij, hi, hj⟩))
  · exact F_true_of y c hyc (by simp)
      (by rw [Function.update_of_ne hyc.ne.symm]; simp)
lemma stmtG3 : StmtG3 := by
  intro n G A a' a s t b b' hinv hr
  have nd := hr.nd
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, or_false, not_or,
    List.nodup_nil, and_true] at nd
  obtain ⟨⟨h01, h02, h03, h04, h05⟩, ⟨h12, h13, h14, h15⟩, ⟨h23, h24, h25⟩, ⟨h34, h35⟩, h45⟩ := nd
  have haa' : G.Adj a a' := (hr.ha a').2 (Or.inl rfl)
  have has : G.Adj a s := (hr.ha s).2 (Or.inr rfl)
  have hsa : G.Adj s a := (hr.hs a).2 (Or.inl rfl)
  have hst : G.Adj s t := (hr.hs t).2 (Or.inr rfl)
  have hts : G.Adj t s := (hr.ht s).2 (Or.inl rfl)
  have htb : G.Adj t b := (hr.ht b).2 (Or.inr rfl)
  have hbt : G.Adj b t := (hr.hb t).2 (Or.inl rfl)
  have hbb' : G.Adj b b' := (hr.hb b').2 (Or.inr rfl)
  have ha1 : ∀ w, G.Adj a w → w = a' ∨ w = s := fun w h => (hr.ha w).1 h
  have hs1 : ∀ w, G.Adj s w → w = a ∨ w = t := fun w h => (hr.hs w).1 h
  have ht1 : ∀ w, G.Adj t w → w = s ∨ w = b := fun w h => (hr.ht w).1 h
  have hb1 : ∀ w, G.Adj b w → w = t ∨ w = b' := fun w h => (hr.hb w).1 h
  have mem : ∀ w, w = a ∨ w = s ∨ w = t ∨ w = b → w ∈ ({a, s, t, b} : Finset (Fin (n + 1))) := by
    intro w hw
    simp only [Finset.mem_insert, Finset.mem_singleton]
    exact hw
  refine ⟨⟨?_, ?_, ?_, ?_, F_zero G A⟩, ?_⟩
  · intro y hy bv
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    rcases hy with h | h | h | h <;> rw [h]
    · exact nc_of hinv hst (Ne.symm h12) (Ne.symm h13) has bv
    · exact nc_of hinv htb (Ne.symm h23) (Ne.symm h24) hst bv
    · exact nc_of hinv has h13 h23 hts bv
    · exact nc_of hinv has h14 h24 hbt bv
  · intro y hy y' hy' hne
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy hy'
    rcases hy with h | h | h | h <;> rcases hy' with h' | h' | h' | h' <;> rw [h, h'] at hne ⊢
    · exact absurd rfl hne
    · exact nf_of hinv hne haa' h02 hs1 h01 h03 hst (Ne.symm h13)
    · exact nf_of hinv hne haa' h03 ht1 h02 h04 htb (Ne.symm h14)
    · exact nf_of hinv hne haa' h04 hb1 h03 h05 hbb' (Ne.symm h15)
    · exact nf_of hinv hne hst (Ne.symm h13) ha1 (Ne.symm h03) (Ne.symm h23) haa' h02
    · exact absurd rfl hne
    · exact nf_of hinv hne hsa h13 ht1 h12 h14 htb (Ne.symm h24)
    · exact nf_of hinv hne hsa h14 hb1 h13 h15 hbb' (Ne.symm h25)
    · exact nf_of hinv hne htb (Ne.symm h14) ha1 (Ne.symm h04) (Ne.symm h24) haa' h03
    · exact nf_of hinv hne htb (Ne.symm h24) hs1 (Ne.symm h14) (Ne.symm h34) hsa h13
    · exact absurd rfl hne
    · exact nf_of hinv hne hts h24 hb1 h23 h25 hbb' (Ne.symm h35)
    · exact nf_of hinv hne hbb' (Ne.symm h15) ha1 (Ne.symm h05) (Ne.symm h25) haa' h04
    · exact nf_of hinv hne hbb' (Ne.symm h25) hs1 (Ne.symm h15) (Ne.symm h35) hsa h14
    · exact nf_of hinv hne hbb' (Ne.symm h35) ht1 (Ne.symm h25) (Ne.symm h45.1) hts h24
    · exact absurd rfl hne
  · intro y hy x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    have nb : ∀ (w u v : Fin (n + 1)), (w = u ∨ w = v) → (u = a ∨ u = s ∨ u = t ∨ u = b) →
        (v = a ∨ v = s ∨ v = t ∨ v = b) → w ∈ ({a, s, t, b} : Finset (Fin (n + 1))) := by
      intro w u v hw hu hv
      rcases hw with rfl | rfl
      · exact mem _ hu
      · exact mem _ hv
    rcases hy with h | h | h | h <;> rw [h]
    · exact win_of hinv (mem a (by simp)) (mem s (by simp)) has
        (fun w hw => nb w a t (hs1 w hw) (by simp) (by simp)) x hx
    · exact win_of hinv (mem s (by simp)) (mem t (by simp)) hst
        (fun w hw => nb w s b (ht1 w hw) (by simp) (by simp)) x hx
    · exact win_of hinv (mem t (by simp)) (mem s (by simp)) hts
        (fun w hw => nb w a t (hs1 w hw) (by simp) (by simp)) x hx
    · exact win_of hinv (mem b (by simp)) (mem t (by simp)) hbt
        (fun w hw => nb w s b (ht1 w hw) (by simp) (by simp)) x hx
  · intro x hx
    refine F_mono (fun i h => ?_) hx
    unfold zeroOn at h
    split_ifs at h <;> simp_all
  · have hsub : ({a, s} : Finset (Fin (n + 1))) ⊆ {a, s, t, b} := by
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
      tauto
    have := Finset.card_le_card hsub
    rw [Finset.card_pair h12] at this
    exact this
section G4
open PEqualNP.Outside.L_meta_3457.SparseLower.Loc.Struct
lemma thread7 {n : ℕ} (G : SimpleGraph (Fin n)) (hL : T7 G)
    (h1 : ¬ ∃ l p q, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ ∀ w, G.Adj p w → w = l ∨ w = q)
    (u v : Fin n) (hvu : G.Adj v u) (hv : Two G v)
    (hbr : 3 ≤ (G.neighborSet u).ncard ∨ ∀ w, ¬ 3 ≤ (G.neighborSet w).ncard) :
    ∃ x, ∃ q : G.Walk x u, Good G u x q ∧ 6 ≤ q.length := by
  have h0 : Good G u v (Walk.cons hvu Walk.nil) := by
    refine ⟨?_, by simp, fun i hi => ?_⟩
    · rw [Walk.cons_isPath_iff]
      exact ⟨Walk.IsPath.nil, by simpa using hvu.ne⟩
    · simp at hi
      subst hi
      simpa using hv
  obtain ⟨x, q, hq, hmax⟩ := exists_max G u ⟨v, _, h0⟩
  refine ⟨x, q, hq, ?_⟩
  by_contra hlt
  push Not at hlt
  have hk := hq.pos
  have hxy : G.Adj x (q.getVert 1) := by
    simpa using q.adj_getVert_succ (i := 0) (by omega)
  have hx : Two G x := by simpa using hq.two 0 (by omega)
  obtain ⟨z, hzy, hxz, hxN⟩ := two_other hx hxy
  have hxu : x ≠ u := by
    have := gv_ne hq.path (i := 0) (j := q.length) (by omega) le_rfl (by omega)
    simpa using this
  by_cases hzu : z = u
  · subst hzu
    have hux : G.Adj z x := hxz.symm
    have hne : s(z, x) ∉ q.edges := by
      intro hmem
      have hy1 := hzy
      have hp := hq.path
      clear hmax h0 hxN hlt hk hq
      cases q with
      | nil => exact hxu rfl
      | @cons _ y' _ h q' =>
        simp only [Walk.edges_cons, List.mem_cons] at hmem
        rw [Walk.cons_isPath_iff] at hp
        simp only [Walk.getVert_cons_succ, Walk.getVert_zero] at hy1
        rcases hmem with he | he
        · rcases Sym2.eq_iff.1 he with ⟨h1, _⟩ | ⟨h1, _⟩
          · exact hxu h1.symm
          · exact hy1 h1
        · exact hp.2 (q'.snd_mem_support_of_mem_edges he)
    have hc : (Walk.cons hux q).IsCycle := (Walk.cons_isCycle_iff q hux).2 ⟨hq.path, hne⟩
    have := hL.1 z _ hc
    simp only [Walk.length_cons] at this
    omega
  · rcases classify G z with hz | hz | ⟨a, ha⟩
    · by_cases hzs : z ∈ q.support
      · obtain ⟨i, hi, hil⟩ := Walk.mem_support_iff_exists_getVert.1 hzs
        have hi0 : i ≠ 0 := by
          rintro rfl
          simp only [Walk.getVert_zero] at hi
          exact hxz.ne hi
        have hi1 : i ≠ 1 := by
          rintro rfl
          exact hzy hi.symm
        have hik : i ≠ q.length := by
          rintro rfl
          rw [Walk.getVert_length] at hi
          exact hzu hi.symm
        have hA : G.Adj z (q.getVert (i - 1)) := by
          have := q.adj_getVert_succ (i := i - 1) (by omega)
          rw [show i - 1 + 1 = i by omega, hi] at this
          exact this.symm
        have hB : G.Adj z (q.getVert (i + 1)) := by
          have := q.adj_getVert_succ (i := i) (by omega)
          rw [hi] at this
          exact this
        have hC : G.Adj z (q.getVert 0) := by
          rw [Walk.getVert_zero]
          exact hxz.symm
        exact two_three hz hA hB hC (gv_ne hq.path (by omega) (by omega) (by omega))
          (gv_ne hq.path (by omega) (by omega) (by omega))
          (gv_ne hq.path (by omega) (by omega) (by omega))
      · have hg : Good G u z (Walk.cons hxz.symm q) := by
          refine ⟨(Walk.cons_isPath_iff _ _).2 ⟨hq.path, hzs⟩, by simp, fun i hi => ?_⟩
          rcases i with _ | j
          · simpa using hz
          · rw [Walk.getVert_cons_succ]
            simp only [Walk.length_cons] at hi
            exact hq.two j (by omega)
        have := hmax z _ hg
        simp only [Walk.length_cons] at this
        omega
    · rcases hbr with hu | hno
      · have := hL.2 z u hzu hz hu (Walk.cons hxz.symm q)
        simp only [Walk.length_cons] at this
        omega
      · exact hno z hz
    · have hax : x = a := ha x hxz.symm
      exact h1 ⟨z, x, q.getVert 1, hxz.symm, fun w hw => (ha w hw).trans hax.symm,
        fun w hw => ((hxN w).1 hw).symm⟩
lemma stmtG4 : StmtG4 := by
  intro n G hL ⟨i, j, hij⟩ h1 h2
  by_cases hb : ∃ u, 3 ≤ (G.neighborSet u).ncard
  · obtain ⟨u, hu⟩ := hb
    obtain ⟨m1, m2, -, hm1, hm2, -, hm12, -, -⟩ :=
      (Set.two_lt_ncard_iff (s := G.neighborSet u)).1 (by omega)
    have hm1 : G.Adj u m1 := hm1
    have hm2 : G.Adj u m2 := hm2
    have cl : ∀ m, G.Adj u m → Two G m ∨ ∀ w, G.Adj m w → w = u := by
      intro m hm
      rcases classify G m with h | h | ⟨a, ha⟩
      · exact Or.inl h
      · have := hL.2 u m hm.ne hu h (Walk.cons hm Walk.nil)
        simp at this
      · have hau : u = a := ha u hm.symm
        exact Or.inr fun w hw => (ha w hw).trans hau.symm
    have hv : ∃ v, G.Adj u v ∧ Two G v := by
      rcases cl m1 hm1 with h | h
      · exact ⟨m1, hm1, h⟩
      rcases cl m2 hm2 with h' | h'
      · exact ⟨m2, hm2, h'⟩
      exact absurd ⟨m1, u, m2, hm1.symm, h, hm2, hm12.symm, h'⟩ h2
    obtain ⟨v, huv, hv⟩ := hv
    obtain ⟨x, q, hq, h6⟩ := thread7 G hL h1 u v huv.symm hv (Or.inl hu)
    exact run_of_thread hq h6
  · push Not at hb
    have nb : ∀ w, ¬ 3 ≤ (G.neighborSet w).ncard := fun w h => by have := hb w; omega
    have go : ∀ u v, G.Adj v u → Two G v → ∃ a' a s t b b', Run G a' a s t b b' := by
      intro u v hvu hv
      obtain ⟨x, q, hq, h6⟩ := thread7 G hL h1 u v hvu hv (Or.inr nb)
      exact run_of_thread hq h6
    rcases classify G j with hj | hj | ⟨a, ha⟩
    · exact go i j hij.symm hj
    · exact absurd hj (nb j)
    rcases classify G i with hi | hi | ⟨b, hb'⟩
    · exact go j i hij hi
    · exact absurd hi (nb i)
    have hai : i = a := ha i hij.symm
    exact absurd ⟨i, j, i, hij, fun w hw => (hb' w hw).trans (hb' j hij).symm,
      fun w hw => Or.inl ((ha w hw).trans hai.symm)⟩ h1
end G4
lemma afree_delV {n : ℕ} {G : SimpleGraph (Fin n)} {A : Finset (Fin n)} (h : AFree G A)
    (X : Finset (Fin n)) : AFree (delV G X) A :=
  fun i j hij => h i j ((delV_adj G X i j).1 hij).1
lemma leaf_drop0 {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p : Fin n)
    (hlp : G.Adj l p) (hleaf : ∀ w, G.Adj l w → w = p) :
    Phi1 G A ≤ Phi1 (delV G {l}) A + 2 ∧
      (delV G {l}).edgeSet.ncard + 1 = G.edgeSet.ncard := by
  rw [Free.del_leaf G l p hleaf]
  have he := ncard_del1 G l p hlp
  obtain ⟨T, hT, hTc⟩ := tau_attained (G.deleteEdges {s(l, p)})
  have hc := tau_le G _ (cov_insert G _ p (fun e he => by
    rw [Set.mem_singleton_iff] at he
    subst he
    exact Sym2.mem_mk_right _ _) T hT)
  have := Finset.card_insert_le p T
  unfold Phi1
  constructor <;> omega
lemma leaf_drop1 {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n)) (l p q : Fin n)
    (hlp : G.Adj l p) (hleaf : ∀ w, G.Adj l w → w = p) (hp : ∀ w, G.Adj p w → w = l ∨ w = q)
    (hpA : p ∉ A) :
    Phi1 G A ≤ Phi1 (delV G (insert l {p})) (A ∪ {p}) + 2 ∧
      (delV G (insert l {p})).edgeSet.ncard < G.edgeSet.ncard := by
  rw [Free.del_leaf2 G l p q hleaf hp]
  obtain ⟨he1, he2⟩ := ncard_del2 G l p q hlp
  obtain ⟨T, hT, hTc⟩ := tau_attained (G.deleteEdges {s(p, l), s(p, q)})
  have hc := tau_le G _ (cov_insert G _ p (fun e he => by
    rcases he with rfl | he
    · exact Sym2.mem_mk_left _ _
    · rw [Set.mem_singleton_iff] at he
      subst he
      exact Sym2.mem_mk_left _ _) T hT)
  have := Finset.card_insert_le p T
  have hAp : (A ∪ {p}).card = A.card + 1 := by
    rw [Finset.union_comm, ← Finset.insert_eq, Finset.card_insert_of_notMem hpA]
  unfold Phi1
  rw [hAp]
  constructor <;> omega
lemma stmtG6 : StmtG6 := by
  intro n G A hinv hih hgood s hC
  obtain ⟨l, p, hlp, hleaf, hcase⟩ := hgood
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := l.2; omega⟩
  have hlA : l ∉ A := hinv l p hlp
  have hpA : p ∉ A := hinv p l hlp.symm
  have hpl : p ≠ l := hlp.ne.symm
  have hdepl := F_dep G A l p hlp hpA
  have hdepp := F_dep G A p l hlp.symm hlA
  have hs1 : 2 ≤ s + 1 := by
    have := dep_lower_set _ (F G A) {l, p} (by
      intro i hi
      rcases Finset.mem_insert.1 hi with rfl | hi
      · exact hdepl
      · rw [Finset.mem_singleton] at hi
        subst hi
        exact hdepp) s hC
    rwa [Finset.card_pair hlp.ne] at this
  obtain ⟨d0, e0⟩ := leaf_drop0 G A l p hlp hleaf
  have hrf : (fun x => F G A (Function.update x l false)) = F (delV G {l}) A :=
    funext fun x => Res.ToolRes0_proof _ G A l x hlA
  rcases hcase with ⟨q, hq⟩ | ⟨l', hl'l, hpl', hleaf'⟩
  · obtain ⟨d1, e1⟩ := leaf_drop1 G A l p q hlp hleaf hq hpA
    by_cases h0 : A.Nonempty ∨ ∃ i j, (delV G {l}).Adj i j
    · have hrt : (fun x => F G A (Function.update x l true)) = F (delV G (insert l {p})) (A ∪ {p}) :=
        funext fun x => Res.ToolRes1_proof _ G A l {p} x hlA (fun w => by
          rw [Finset.mem_singleton]
          exact ⟨hleaf w, fun h => h ▸ hlp⟩)
      have hnc : ∀ b : Bool, ∃ x y : Fin (n' + 1) → Bool,
          F G A (Function.update x l b) ≠ F G A (Function.update y l b) := by
        intro b
        cases b
        · obtain ⟨x, y, hxy⟩ := F_nc (delV G {l}) A h0
          refine ⟨x, y, ?_⟩
          rw [congrFun hrf x, congrFun hrf y]; exact hxy
        · obtain ⟨x, y, hxy⟩ := F_nc (delV G (insert l {p})) (A ∪ {p}) (Or.inl ⟨p, by simp⟩)
          refine ⟨x, y, ?_⟩
          rw [congrFun hrt x, congrFun hrt y]; exact hxy
      obtain ⟨b, s', hs', hC'⟩ := gate_elim_at n' (F G A) l s hdepl hnc hC
      cases b
      · rw [hrf] at hC'
        have := hih {l} A (afree_delV hinv {l}) (by omega) s' hC'
        omega
      · rw [hrt] at hC'
        have hinv1 : AFree (delV G (insert l {p})) (A ∪ {p}) := by
          intro i j h hi
          obtain ⟨hij, hi1, -⟩ := (delV_adj G _ i j).1 h
          rcases Finset.mem_union.1 hi with hi | hi
          · exact hinv i j hij hi
          · exact hi1 (by rw [Finset.mem_singleton] at hi; simp [hi])
        have := hih (insert l {p}) (A ∪ {p}) hinv1 e1 s' hC'
        omega
    · push Not at h0
      obtain ⟨hA0, hG00⟩ := h0
      have he := noedge_ncard (delV G {l}) hG00
      have ht := tau_le (delV G {l}) ∅ (fun i j h => absurd h (hG00 i j))
      subst hA0
      unfold Phi1 at d0 ⊢
      rw [Finset.card_empty] at ht d0 ⊢
      omega
  · obtain ⟨s0, rfl⟩ : ∃ s0, s = s0 + 1 := ⟨s - 1, by omega⟩
    have hpl'0 : (delV G {l}).Adj p l' := (delV_adj G {l} p l').2 ⟨hpl', by simpa using hpl,
      by simpa using hl'l⟩
    have hnc0 : ∃ x y : Fin (n' + 1) → Bool,
        F G A (Function.update x l false) ≠ F G A (Function.update y l false) := by
      obtain ⟨x, y, hxy⟩ := F_nc (delV G {l}) A (Or.inr ⟨p, l', hpl'0⟩)
      refine ⟨x, y, ?_⟩
      rw [congrFun hrf x, congrFun hrf y]; exact hxy
    have hC' := one_gate_at n' (F G A) l false s0 hdepl hnc0 hC
    rw [hrf] at hC'
    have htau : tau G ≤ tau (delV G {l}) := by
      obtain ⟨T, hT, hTc⟩ := tau_attained (delV G {l})
      rw [← hTc]
      rw [Free.del_leaf G l p hleaf] at hT
      exact cov_swap G l p l' (tau G) hl'l hpl' hleaf' (fun T h => tau_le G T h) T hT
    have := hih {l} A (afree_delV hinv {l}) (by omega) s0 hC'
    unfold Phi1 at this ⊢
    omega
lemma deep_mem {n : ℕ} {G : SimpleGraph (Fin n)} {a' a s t b b' : Fin n}
    (hr : Run G a' a s t b b') (y : Fin n) (hy : y ∈ ({a, s, t, b} : Finset (Fin n))) :
    Deep G y := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with rfl | rfl | rfl | rfl
  · exact hr.deep_a
  · exact hr.deep_s
  · exact hr.deep_t
  · exact hr.deep_b
lemma deep_step (hG3 : StmtG3) (hML : StmtML) (hR0 : ToolRes0) (hR1 : ToolRes1)
    (hD0 : ToolDrop0) (hD1 : ToolDrop1) {n : ℕ} (G : SimpleGraph (Fin n)) (A : Finset (Fin n))
    (a' a s t b b' : Fin n) (hinv : AFree G A) (hih : IHV G) (hr : Run G a' a s t b b') :
    BoundOf (PEqualNP.MetaComplexity.HasCircuitSize n) G A := by
  intro s0 hC
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := a.2; omega⟩
  obtain ⟨hD, h2⟩ := hG3 n' G A a' a s t b b' hinv hr
  have hne : ({a, s, t, b} : Finset (Fin (n' + 1))).Nonempty := Finset.card_pos.1 (by omega)
  obtain ⟨y, hy, hpay⟩ := hML n' (F G A) _ s0 hD hne hC
  obtain ⟨u1, u2, c1, c2, hu12, hN, h1, h2', -⟩ := deep_mem hr y hy
  have hyu1 : G.Adj y u1 := (hN u1).2 (Or.inl rfl)
  have hyu2 : G.Adj y u2 := (hN u2).2 (Or.inr rfl)
  have hyA : y ∉ A := hinv y u1 hyu1
  rcases hpay with ⟨s', hs', hC'⟩ | ⟨s', hs', hC'⟩
  · have hf : (fun x => F G A (Function.update x y false)) = F (delV G {y}) A :=
      funext fun x => hR0 _ G A y x hyA
    rw [hf] at hC'
    obtain ⟨d, e⟩ := hD0 _ G A y u1 u2 hyu1 (fun w h => (hN w).1 h)
    have := hih {y} A (afree_delV hinv {y}) e s' hC'
    omega
  · have hf : (fun x => F G A (Function.update x y true)) =
        F (delV G (insert y {u1, u2})) (A ∪ {u1, u2}) :=
      funext fun x => hR1 _ G A y {u1, u2} x hyA (fun w => by
        rw [hN w]; simp)
    rw [hf] at hC'
    have hu1A : u1 ∉ A := hinv u1 y hyu1.symm
    have hu2A : u2 ∉ A := hinv u2 y hyu2.symm
    obtain ⟨d, e⟩ := hD1 _ G A y u1 u2 c1 c2 hN h1 h2' hu1A hu2A
    have hinv1 : AFree (delV G (insert y {u1, u2})) (A ∪ {u1, u2}) := by
      intro i j h hi
      obtain ⟨hij, hi1, -⟩ := (delV_adj G _ i j).1 h
      rcases Finset.mem_union.1 hi with hi | hi
      · exact hinv i j hij hi
      · exact hi1 (Finset.mem_insert_of_mem hi)
    have := hih _ _ hinv1 e s' hC'
    omega
lemma a1_of_pieces {P : (n : ℕ) → SimpleGraph (Fin n) → Prop} (hH : Hered P) (hDi : Dich P)
    (hG3 : StmtG3) (hG6 : StmtG6) (hML : StmtML) (hR0 : ToolRes0) (hR1 : ToolRes1)
    (hD0 : ToolDrop0) (hD1 : ToolDrop1) : StmtA1 P := by
  suffices key : ∀ (e n : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)),
      G.edgeSet.ncard = e → P n G → AFree G A → BoundOf (PEqualNP.MetaComplexity.HasCircuitSize n) G A from
    fun n G A hP hinv => key _ n G A rfl hP hinv
  intro e
  induction e using Nat.strong_induction_on with
  | _ e ihe =>
  intro n G A he hP hinv
  have hih : IHV G := fun X A' hinv' hlt =>
    ihe _ (he ▸ hlt) n (delV G X) A' rfl (hH n G X hP) hinv'
  by_cases hE : ∃ i j, G.Adj i j
  swap
  · intro s hC
    have hE' : ∀ i j, ¬ G.Adj i j := fun i j h => hE ⟨i, j, h⟩
    have hdep := dep_lower_set n (F G A) A (fun a ha => F_dep_A G A a ha) s hC
    have h0 := noedge_ncard G hE'
    have ht := tau_le G ∅ (fun i j h => absurd h (hE' i j))
    rw [Finset.card_empty] at ht
    unfold Phi1
    omega
  rcases hDi n G hP hE with hg | ⟨a', a, s, t, b, b', hr⟩
  · exact hG6 n G A hinv hih hg
  · exact deep_step hG3 hML hR0 hR1 hD0 hD1 G A a' a s t b b' hinv hih hr
lemma dich_of_g4 (hG4 : StmtG4) : Dich (fun _ G => T7 G) := by
  intro n G hT hE
  by_cases h1 : ∃ l p q, G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ ∀ w, G.Adj p w → w = l ∨ w = q
  · obtain ⟨l, p, q, h, h', h''⟩ := h1
    exact Or.inl ⟨l, p, h, h', Or.inl ⟨q, h''⟩⟩
  by_cases h2 : ∃ l p l', G.Adj l p ∧ (∀ w, G.Adj l w → w = p) ∧ G.Adj p l' ∧ l' ≠ l ∧
      ∀ w, G.Adj l' w → w = p
  · obtain ⟨l, p, l', h, h', h'', h3, h4⟩ := h2
    exact Or.inl ⟨l, p, h, h', Or.inr ⟨l', h3, h'', h4⟩⟩
  exact Or.inr (hG4 n G hT hE h1 h2)
lemma lb_of_a1 (h : StmtA1 (fun _ G => T7 G)) : StmtLB := by
  intro n k s G A hcyc hdist hinv _ hk hC
  have hb := h n G A ⟨hcyc, hdist⟩ hinv s hC
  obtain ⟨T, hT, hTc⟩ := tau_attained G
  have := hk T hT
  unfold Phi1 at hb
  omega
lemma lb_of_pieces (hG3 : StmtG3) (hG4 : StmtG4) (hML : StmtML) : StmtLB :=
  lb_of_a1 (a1_of_pieces stmtG1 (dich_of_g4 hG4) hG3 stmtG6 hML Res.ToolRes0_proof
    Res.ToolRes1_proof Res.ToolDrop0_proof Res.ToolDrop1_proof)
lemma lb_of_ml (hML : StmtML) : StmtLB := lb_of_pieces stmtG3 stmtG4 hML
end PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn

namespace PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
open PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Readers
lemma rdel_length (N p a : ℕ) (gs : List Gate) (hp : p < gs.length) :
    (rdel N p a gs).length + 1 = gs.length := by
  simp [rdel]; omega
lemma rdel_get_lt (N p a : ℕ) (gs : List Gate) (hp : p < gs.length) (j : ℕ) (hj : j < p) :
    (rdel N p a gs)[j]? = gs[j]? := by
  unfold rdel
  rw [List.getElem?_append_left (by simp; omega), List.getElem?_take_of_lt hj]
lemma rdel_get_ge (N p a : ℕ) (gs : List Gate) (hp : p < gs.length) (j : ℕ) (hj : p ≤ j) :
    (rdel N p a gs)[j]? =
      (gs[j + 1]?).map fun g => (⟨g.op, g.inputs.map (rd N p a)⟩ : Gate) := by
  unfold rdel
  rw [List.getElem?_append_right (by simp; omega)]
  simp only [List.length_take, List.getElem?_map, List.getElem?_drop]
  congr 2
  omega
lemma vl_append_lt {N : ℕ} (gs gs' : List Gate) (x : Fin N → Bool) (w : ℕ)
    (hw : w < N + gs.length) : vl (gs ++ gs') x w = vl gs x w := by
  unfold vl
  rw [wiresFrom_append, getD_wiresFrom _ _ w (by rw [length_wiresFrom]; simp; omega)]
lemma rd_lt (N p a w : ℕ) (hw : w < N + p) : rd N p a w = w := by
  simp [rd, hw]
lemma rd_eq (N p a : ℕ) : rd N p a (N + p) = a := by
  simp [rd]
lemma rd_gt (N p a w : ℕ) (hw : N + p < w) : rd N p a w = w - 1 := by
  unfold rd
  split_ifs <;> omega
lemma rdel_clean (N p a : ℕ) (gs : List Gate) (hcl : CleanL N gs) (hp : p < gs.length)
    (ha : a < N + p) : CleanL N (rdel N p a gs) := by
  intro j g hj
  by_cases hjp : j < p
  · rw [rdel_get_lt N p a gs hp j hjp] at hj
    exact hcl j g hj
  · rw [rdel_get_ge N p a gs hp j (by omega)] at hj
    obtain ⟨g0, hg0, rfl⟩ := Option.map_eq_some_iff.1 hj
    have hc := hcl (j + 1) g0 hg0
    have hmap : ∀ i, i < N + (j + 1) → rd N p a i < N + j := by
      intro i hi
      unfold rd
      split_ifs <;> omega
    rcases hc with ⟨h1, i, hi, h2⟩ | ⟨h1, i, k, hi, hk, h2⟩
    · exact Or.inl ⟨h1, rd N p a i, hmap i hi, by simp [h2]⟩
    · exact Or.inr ⟨h1, rd N p a i, rd N p a k, hmap i hi, hmap k hk, by simp [h2]⟩
lemma rdel_prefix (N p a : ℕ) (gs : List Gate) (hcl : CleanL N gs) (hp : p < gs.length)
    (ha : a < N + p) (x : Fin N → Bool) :
    ∀ w : ℕ, w < N + p → vl (rdel N p a gs) x w = vl gs x w := by
  have hcl' := rdel_clean N p a gs hcl hp ha
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwN : w < N
    · rw [vl_input _ x w hwN, vl_input _ x w hwN]
    · obtain ⟨j, rfl⟩ : ∃ j, w = N + j := ⟨w - N, by omega⟩
      have hj : j < p := by omega
      obtain ⟨g, hg⟩ : ∃ g, gs[j]? = some g := ⟨gs[j], List.getElem?_eq_getElem (by omega)⟩
      have hg' : (rdel N p a gs)[j]? = some g := by rw [rdel_get_lt N p a gs hp j hj, hg]
      rw [vl_gate _ hcl' x j g hg', vl_gate _ hcl x j g hg]
      congr 1
      apply List.map_congr_left
      intro i hi
      exact ih i ((hcl j g hg).lt i hi) (by have := (hcl j g hg).lt i hi; omega)
lemma rdel_all (N p a : ℕ) (gs : List Gate) (hcl : CleanL N gs) (hp : p < gs.length)
    (ha : a < N + p) (x : Fin N → Bool) (hx : vl gs x (N + p) = vl gs x a) :
    ∀ w : ℕ, vl (rdel N p a gs) x (rd N p a w) = vl gs x w := by
  have hcl' := rdel_clean N p a gs hcl hp ha
  have hlen := rdel_length N p a gs hp
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rcases lt_trichotomy w (N + p) with hw | rfl | hw
    · rw [rd_lt N p a w hw]
      exact rdel_prefix N p a gs hcl hp ha x w hw
    · rw [rd_eq, hx]
      exact rdel_prefix N p a gs hcl hp ha x a ha
    · rw [rd_gt N p a w hw]
      obtain ⟨j, rfl⟩ : ∃ j, w = N + (j + 1) := ⟨w - N - 1, by omega⟩
      have e : N + (j + 1) - 1 = N + j := by omega
      rw [e]
      by_cases hjl : j + 1 < gs.length
      · obtain ⟨g, hg⟩ : ∃ g, gs[j + 1]? = some g := ⟨gs[j + 1], List.getElem?_eq_getElem hjl⟩
        have hg' : (rdel N p a gs)[j]? = some ⟨g.op, g.inputs.map (rd N p a)⟩ := by
          rw [rdel_get_ge N p a gs hp j (by omega), hg]; rfl
        rw [vl_gate _ hcl' x j _ hg', vl_gate _ hcl x (j + 1) g hg]
        simp only [List.map_map]
        congr 1
        apply List.map_congr_left
        intro i hi
        exact ih i ((hcl (j + 1) g hg).lt i hi)
      · rw [vl_beyond _ x _ (by omega), vl_beyond _ x _ (by omega)]
lemma stmtRD : StmtRD := by
  intro N gs p a hcl hp ha
  exact ⟨rdel_clean N p a gs hcl hp ha, rdel_length N p a gs hp,
    fun x w hw => rdel_prefix N p a gs hcl hp ha x w hw,
    fun x hx w => rdel_all N p a gs hcl hp ha x hx w⟩
lemma TailGE.zero (N : ℕ) (F : (Fin N → Bool) → Bool) (gs : List Gate) : TailGE N F gs 0 :=
  ⟨Nat.zero_le _, fun j h1 h2 => absurd h2 (by omega)⟩
lemma TailGE.mono {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {t t' : ℕ}
    (h : TailGE N F gs t) (ht : t' ≤ t) : TailGE N F gs t' :=
  ⟨le_trans ht h.1, fun j h1 h2 => h.2 j (by omega) h2⟩
lemma TailGE.le {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {t : ℕ}
    (h : TailGE N F gs t) : t ≤ gs.length := h.1
lemma TailGE.lt_of_not {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {t p : ℕ}
    (h : TailGE N F gs t) (hp : p < gs.length) (hn : ¬ TailOK N F gs p) : p + t < gs.length := by
  by_contra hc
  exact hn (h.2 p (by omega) hp)
lemma tailGE_rdel_app (N : ℕ) (F : (Fin N → Bool) → Bool) (gs new : List Gate) (p a t : ℕ)
    (S : (Fin N → Bool) → Prop) (hcl : CleanL N gs) (hp : p < gs.length) (ha : a < N + p)
    (ht : TailGE N F gs t) (hpt : p + t < gs.length)
    (hS : ∀ x, S x → vl gs x (N + p) = vl gs x a) (hF : ∀ x, ¬ S x → F x = true)
    (hnew : ∀ i, i < new.length → TailOK N F (rdel N p a gs ++ new) (gs.length - 1 + i)) :
    TailGE N F (rdel N p a gs ++ new) (t + new.length) := by
  have hlen := rdel_length N p a gs hp
  have hl' : (rdel N p a gs ++ new).length = gs.length - 1 + new.length := by
    simp; omega
  refine ⟨by rw [hl']; omega, ?_⟩
  intro j h1 h2
  rw [hl'] at h1 h2
  by_cases hj : gs.length - 1 ≤ j
  · have := hnew (j - (gs.length - 1)) (by omega)
    rwa [show gs.length - 1 + (j - (gs.length - 1)) = j by omega] at this
  · have hok := ht.2 (j + 1) (by omega) (by omega)
    obtain ⟨g, hg, hop⟩ := hok
    have hj' : (rdel N p a gs ++ new)[j]? = some ⟨g.op, g.inputs.map (rd N p a)⟩ := by
      rw [List.getElem?_append_left (by omega), rdel_get_ge N p a gs hp j (by omega), hg]; rfl
    refine ⟨_, hj', ?_⟩
    rcases hop with hop | ⟨hop, hbel⟩
    · exact Or.inl hop
    · refine Or.inr ⟨hop, fun x hx => ?_⟩
      by_cases hSx : S x
      · apply hbel x
        rw [← rdel_all N p a gs hcl hp ha x (hS x hSx) (N + (j + 1)),
          rd_gt N p a _ (by omega), show N + (j + 1) - 1 = N + j by omega,
          ← vl_append_lt (rdel N p a gs) new x (N + j) (by omega)]
        exact hx
      · exact hF x hSx
lemma least_of {N : ℕ} {F : (Fin N → Bool) → Bool} {gs gs0 : List Gate} {o o0 : ℕ}
    (h0 : Least N F gs0 o0) (hcl : CleanL N gs) (hev : ∀ x, vl gs x o = F x)
    (hle : gs.length ≤ gs0.length) : Least N F gs o :=
  ⟨hcl, hev, fun gs' o' hc he => le_trans hle (h0.hmin gs' o' hc he)⟩
end PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn

namespace PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
open PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Readers
lemma deepHyp_nc {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (hD : DeepHyp F D) (hne : D.Nonempty) : ∃ x y : Fin N → Bool, F x ≠ F y := by
  obtain ⟨y, hy⟩ := hne
  obtain ⟨x, x', h⟩ := hD.nc y hy false
  exact ⟨_, _, h⟩
lemma deepHyp_dep {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)}
    (hD : DeepHyp F D) {y : Fin N} (hy : y ∈ D) : Dep F y := by
  have h0 : F (zeroOn D (fun _ => false)) = false := by
    have : zeroOn D (fun _ : Fin N => false) = fun _ => false := by
      funext i; simp [zeroOn]
    rw [this]; exact hD.zero
  obtain ⟨x', -, hx'y, hF, hF'⟩ := hD.win y hy _ h0
  refine ⟨x', ?_⟩
  rw [hx'y, hF, show (!false) = true from rfl, hF']
  simp
lemma least_len {N : ℕ} {F : (Fin N → Bool) → Bool} {gs gs' : List Gate} {o o' : ℕ}
    (L : Least N F gs o) (L' : Least N F gs' o') : gs.length = gs'.length :=
  le_antisymm (L.hmin gs' o' L'.hcl L'.hev) (L'.hmin gs o L.hcl L.hev)
lemma vl_bin {N : ℕ} (gs : List Gate) (hcl : CleanL N gs) (x : Fin N → Bool) (p l h : ℕ)
    (g : Gate) (hg : gs[p]? = some g) (hin : g.inputs = [l, h] ∨ g.inputs = [h, l]) :
    (g.op = GateOp.or → vl gs x (N + p) = (vl gs x l || vl gs x h)) ∧
    (g.op = GateOp.and → vl gs x (N + p) = (vl gs x l && vl gs x h)) := by
  rw [vl_gate gs hcl x p g hg]
  constructor <;> intro hop <;> rw [hop] <;>
    rcases hin with e | e <;> rw [e] <;> simp [GateOp.eval, Bool.or_comm, Bool.and_comm]
lemma not_tailOK_or {n : ℕ} {F : (Fin (n + 1) → Bool) → Bool} {D : Finset (Fin (n + 1))}
    {gs : List Gate} {o p : ℕ} {g : Gate} {y : Fin (n + 1)} {l h : ℕ}
    (hD : DeepHyp F D) (L : Least (n + 1) F gs o) (hf : Front D gs p g y l h)
    (hop : g.op = GateOp.or) : ¬ TailOK (n + 1) F gs p := by
  obtain ⟨hg, -, hin, hy, hlit, -⟩ := hf
  rintro ⟨g', hg', hop' | ⟨-, hbel⟩⟩
  · rw [hg] at hg'; cases hg'; rw [hop] at hop'; cases hop'
  · rw [hg] at hg'; cases hg'
    have key : ∀ b : Bool, (∀ x : Fin (n + 1) → Bool, x y = b → vl gs x l = true) → False := by
      intro b hb
      obtain ⟨x, x', hne⟩ := hD.nc y hy b
      have : ∀ z : Fin (n + 1) → Bool, F (Function.update z y b) = true := by
        intro z
        apply hbel
        rw [(vl_bin gs L.hcl _ p l h g hg hin).1 hop, hb _ (by simp)]
        rfl
      exact hne (by rw [this, this])
    rcases hlit with rfl | ⟨pn, rfl, hpn⟩
    · apply key true
      intro x hx
      rw [vl_input gs x y y.isLt]
      simpa using hx
    · apply key false
      intro x hx
      rw [vl_not gs L.hcl x pn _ hpn y rfl rfl, vl_input gs x y y.isLt]
      simpa using hx
lemma stmtExt (hLift : StmtLift) (hX : StmtXMove) (hFront : StmtFront) (hWin : StmtWin)
    (hTwo : StmtTwo) : StmtExt := by
  classical
  intro n F D s hD hne hs
  have hnc := deepHyp_nc hD hne
  obtain ⟨gs0, o0, L0, hl0⟩ := exists_least (n + 1) F s hnc hs
  let P : ℕ → Prop := fun t => ∃ (gs : List Gate) (o : ℕ), Least (n + 1) F gs o ∧
    TailGE (n + 1) F gs t
  have hP0 : P 0 := ⟨gs0, o0, L0, TailGE.zero _ _ _⟩
  have hbound : ∀ t, P t → t ≤ gs0.length := by
    rintro t ⟨gs, o, L, ht⟩
    exact (least_len L L0) ▸ ht.le
  set M := Nat.findGreatest P gs0.length with hM
  obtain ⟨gs, o, L, ht⟩ : P M := Nat.findGreatest_spec (Nat.zero_le _) hP0
  have hmax : ∀ t, P t → t ≤ M := fun t h => Nat.le_findGreatest (hbound t h) h
  refine ⟨gs, o, L, by rw [least_len L L0]; exact hl0, ?_⟩
  by_contra hstop
  push Not at hstop
  obtain ⟨hone, hnoand⟩ := hstop
  obtain ⟨p, g, y, l, h, hf, hop⟩ := hFront n F D gs o hD hne L hone
  have hw := hWin n F D gs o p g y l h hD L hone hf
  obtain ⟨hg, hor, hin, -, -, -⟩ := id hf
  rcases hor with hand | hor
  ·
    obtain ⟨hbel, hhN⟩ := hw.2 hand
    obtain ⟨t, htr, htp⟩ := hnoand p g y l h hf hand hhN hop
    obtain ⟨r, g', q, hrp, hg', hand', hin', -⟩ :=
      hTwo n F D gs o p g y l h hD L hone hf hand ⟨t, htp, htr⟩
    obtain ⟨gs', o', L', ht'⟩ : P (M + 2) := by
      rcases lt_or_gt_of_ne hrp with hlt | hlt
      · obtain ⟨gs', o', L', ht'⟩ :=
          hX (n + 1) F gs o r p q l h g' g L hnc hlt hg' hand' hin' hg hand hin hbel
        exact ⟨gs', o', L', ht' M ht⟩
      · obtain ⟨gs', o', L', ht'⟩ :=
          hX (n + 1) F gs o p r l q h g g' L hnc hlt hg hand hin hg' hand' hin' hbel
        exact ⟨gs', o', L', ht' M ht⟩
    have := hmax _ ⟨gs', o', L', ht'⟩
    omega
  ·
    have hbel := hw.1 hor
    obtain ⟨L', ht'⟩ := hLift (n + 1) F gs o p l h g L hnc hg hor hin hbel
    have := hmax _ ⟨_, _, L', ht' (not_tailOK_or hD L hf hor) M ht⟩
    omega
lemma stmtML (hAnd : StmtAnd) (hExt : StmtExt) : StmtML := by
  intro n F D s hD hne hs
  have hnc := deepHyp_nc hD hne
  obtain ⟨gs, o, L, hls, halt⟩ := hExt n F D s hD hne hs
  rcases halt with hone | ⟨p, g, y, l, h, hf, hand, hhN, hop, honly⟩
  · simp only [OneReader, not_and_or] at hone
    push Not at hone
    rcases hone with ⟨y, hy, p, q, hp, hq, hpq⟩ | ⟨y, hy, pn, hpn, p, q, hp, hq, hpq⟩
    · refine ⟨y, hy, ?_⟩
      rcases L.two_readers y (hD.nc y hy) p q hpq hp hq with
        ⟨h3, -⟩ | ⟨h4, -⟩ | ⟨-, h4⟩
      · exact Or.inl (h3.mono le_rfl hls)
      · exact Or.inl (h4.mono (by omega) hls)
      · exact Or.inr (h4.mono le_rfl hls)
    · refine ⟨y, hy, Or.inl ?_⟩
      exact (L.not_two_readers y (hD.nc y hy) pn _ hpn rfl (by simp) p q hpq hp hq).1.mono
        le_rfl hls
  · obtain ⟨hg, -, hin, hy, hlit, hfree⟩ := hf
    refine ⟨y, hy, ?_⟩
    have hrd : Reads gs p h := ⟨g, hg, by rcases hin with e | e <;> rw [e] <;> simp⟩
    have hhlt := reads_lt L.hcl hrd
    have hplt := reads_len hrd
    have hdep := deepHyp_dep hD hy
    have hoh : o ≠ h := by
      rintro rfl
      obtain ⟨x, hx⟩ := hdep
      apply hx
      rw [← L.hev, ← L.hev]
      exact (agree_wiresFrom (Function.update x y (!x y)) x gs _ _ _
        (agree_inputs _ _)).2.2 o (by
          intro k hk
          have : k ≠ y := fun e => hfree y hy (e ▸ hk)
          simp [Function.update_of_ne this])
    obtain ⟨ph, rfl⟩ : ∃ ph, h = n + 1 + ph := ⟨h - (n + 1), by omega⟩
    have hA := hAnd n F gs o p ph l g y L (hD.nc y hy) hdep hg hand hin hlit (by omega)
      honly hop hoh
    by_cases hl : l = (y : ℕ)
    · exact Or.inl ((hA.1 hl).mono le_rfl hls)
    · exact Or.inr ((hA.2 hl).mono le_rfl hls)
end PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn

namespace PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.TableSearch
open PEqualNP.CircuitLowerBounds
def gt (M : ℕ) : GateOp → List ℕ → ℕ
  | GateOp.and, [] => M
  | GateOp.and, [a] => a
  | GateOp.and, a :: b :: _ => a &&& b
  | GateOp.or, [] => 0
  | GateOp.or, [a] => a
  | GateOp.or, a :: b :: _ => a ||| b
  | GateOp.not, [] => M
  | GateOp.not, a :: _ => M ^^^ a
  | _, _ => 0
def tstep (M : ℕ) (T : List ℕ) (g : Gate) : List ℕ :=
  T ++ [gt M g.op (g.inputs.map fun i => T.getD i 0)]
def tabs (M : ℕ) (T0 : List ℕ) (gs : List Gate) : List ℕ :=
  gs.foldl (tstep M) T0
def GOk (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧ g.inputs.length ≤ 2
lemma gt_testBit (M p : ℕ) (hM : M.testBit p = true) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (l : List ℕ)
    (hl : l.length ≤ 2) :
    (gt M op l).testBit p = op.eval (l.map fun t => t.testBit p) := by
  match l, hl with
  | [], _ => rcases hop with h | h | h <;> subst h <;> simp [gt, GateOp.eval, hM]
  | [a], _ => rcases hop with h | h | h <;> subst h <;> simp [gt, GateOp.eval, Nat.testBit_xor, hM]
  | [a, b], _ =>
    rcases hop with h | h | h <;> subst h <;>
      simp [gt, GateOp.eval, Nat.testBit_xor, Nat.testBit_land, Nat.testBit_lor, hM]
lemma getD_map_testBit (T : List ℕ) (p i : ℕ) :
    (T.map fun t => t.testBit p).getD i false = (T.getD i 0).testBit p := by
  rw [show false = (0 : ℕ).testBit p by simp, List.getD_map]
lemma wires_tabs (M p : ℕ) (hM : M.testBit p = true) :
    ∀ (gs : List Gate) (T0 : List ℕ), (∀ g ∈ gs, GOk g) →
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)])
          (T0.map fun t => t.testBit p)
        = (tabs M T0 gs).map fun t => t.testBit p := by
  intro gs
  induction gs with
  | nil => intro T0 _; rfl
  | cons g gs ih =>
    intro T0 hok
    have hg := hok g (by simp)
    have e : (T0.map fun t => t.testBit p) ++
        [g.op.eval (g.inputs.map fun i => (T0.map fun t => t.testBit p).getD i false)]
        = (tstep M T0 g).map fun t => t.testBit p := by
      simp only [tstep, List.map_append, List.map_cons, List.map_nil]
      congr 2
      rw [gt_testBit M p hM g.op hg.1 _ (by simpa using hg.2), List.map_map]
      congr 1
      apply List.map_congr_left
      intro i _
      exact getD_map_testBit T0 p i
    simp only [List.foldl_cons]
    rw [e]
    exact ih _ (fun g' hg' => hok g' (by simp [hg']))
def cands (M : ℕ) (S : List ℕ) : List ℕ :=
  M :: 0 :: ((0 :: S).map (fun a => M ^^^ a) ++ (0 :: S) ++
    ((0 :: S).flatMap fun a => (0 :: S).map fun b => a &&& b) ++
    ((0 :: S).flatMap fun a => (0 :: S).map fun b => a ||| b))
def nub : List ℕ → List ℕ
  | [] => []
  | a :: l => if (nub l).contains a then nub l else a :: nub l
lemma mem_nub (x : ℕ) : ∀ l : List ℕ, x ∈ nub l ↔ x ∈ l := by
  intro l
  induction l with
  | nil => simp [nub]
  | cons a l ih =>
    simp only [nub]
    split
    · rename_i h
      simp only [List.contains_iff_mem] at h
      rw [ih, List.mem_cons]
      constructor
      · exact Or.inr
      · rintro (rfl | h') <;> [exact (ih.1 h); exact h']
    · simp [ih]
def next (M : ℕ) (S : List ℕ) : List ℕ :=
  nub ((cands M S).filter fun t => !(S.contains t))
def reach (M : ℕ) (good : ℕ → Bool) : ℕ → List ℕ → Bool
  | 0, S => (0 :: S).any good
  | k + 1, S => (0 :: S).any good || (next M S).any fun t => reach M good k (S ++ [t])
lemma cands_mono (M : ℕ) (S S' : List ℕ) (h : ∀ x, x ∈ S → x ∈ S') (t : ℕ)
    (ht : t ∈ cands M S) : t ∈ cands M S' := by
  have h0 : ∀ x, x ∈ (0 :: S) → x ∈ (0 :: S') := by
    intro x hx
    rcases List.mem_cons.1 hx with hx | hx
    · simp [hx]
    · exact List.mem_cons_of_mem _ (h x hx)
  simp only [cands, List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap] at ht
  simp only [cands, List.mem_cons, List.mem_append, List.mem_map, List.mem_flatMap]
  rcases ht with ht | ht | ((⟨a, ha, e⟩ | ht) | ⟨a, ha, b, hb, e⟩) | ⟨a, ha, b, hb, e⟩
  · exact Or.inl ht
  · exact Or.inr (Or.inl ht)
  · refine Or.inr (Or.inr (Or.inl (Or.inl (Or.inl ⟨a, ?_, e⟩))))
    have := h0 a (by simpa using ha); simpa using this
  · refine Or.inr (Or.inr (Or.inl (Or.inl (Or.inr ?_))))
    have := h0 t (by simpa using ht); simpa using this
  · refine Or.inr (Or.inr (Or.inl (Or.inr ⟨a, ?_, b, ?_, e⟩)))
    · have := h0 a (by simpa using ha); simpa using this
    · have := h0 b (by simpa using hb); simpa using this
  · refine Or.inr (Or.inr (Or.inr ⟨a, ?_, b, ?_, e⟩))
    · have := h0 a (by simpa using ha); simpa using this
    · have := h0 b (by simpa using hb); simpa using this
lemma mem_next (M : ℕ) (S : List ℕ) (t : ℕ) : t ∈ next M S ↔ t ∈ cands M S ∧ t ∉ S := by
  simp [next, mem_nub]
lemma any_congr_mem (l l' : List ℕ) (f f' : ℕ → Bool) (hl : ∀ x, x ∈ l ↔ x ∈ l')
    (hf : ∀ x, f x = f' x) : l.any f = l'.any f' := by
  rw [Bool.eq_iff_iff, List.any_eq_true, List.any_eq_true]
  constructor
  · rintro ⟨x, hx, e⟩; exact ⟨x, (hl x).1 hx, by rw [← hf]; exact e⟩
  · rintro ⟨x, hx, e⟩; exact ⟨x, (hl x).2 hx, by rw [hf]; exact e⟩
lemma reach_congr (M : ℕ) (good : ℕ → Bool) : ∀ (k : ℕ) (S S' : List ℕ),
    (∀ x, x ∈ S ↔ x ∈ S') → reach M good k S = reach M good k S' := by
  intro k
  induction k with
  | zero =>
    intro S S' h
    simp only [reach]
    exact any_congr_mem _ _ _ _ (by intro x; simp [h]) (fun _ => rfl)
  | succ k ih =>
    intro S S' h
    simp only [reach]
    congr 1
    · exact any_congr_mem _ _ _ _ (by intro x; simp [h]) (fun _ => rfl)
    · apply any_congr_mem
      · intro x
        rw [mem_next, mem_next]
        exact ⟨fun ⟨a, b⟩ => ⟨cands_mono M S S' (fun y => (h y).1) x a, by rwa [← h]⟩,
          fun ⟨a, b⟩ => ⟨cands_mono M S' S (fun y => (h y).2) x a, by rwa [h]⟩⟩
      · intro t
        exact ih _ _ (by intro x; simp [h])
lemma reach_of_zero (M : ℕ) (good : ℕ → Bool) (S : List ℕ) (h : reach M good 0 S = true) :
    ∀ k, reach M good k S = true := by
  intro k
  cases k with
  | zero => exact h
  | succ k => simp only [reach] at h ⊢; simp [h]
lemma reach_succ (M : ℕ) (good : ℕ → Bool) (k : ℕ) (S : List ℕ) :
    reach M good (k + 1) S
      = ((0 :: S).any good || (next M S).any fun t => reach M good k (S ++ [t])) := rfl
lemma reach_mono (M : ℕ) (good : ℕ → Bool) : ∀ (k : ℕ) (S : List ℕ),
    reach M good k S = true → reach M good (k + 1) S = true := by
  intro k
  induction k with
  | zero => intro S h; exact reach_of_zero M good S h 1
  | succ k ih =>
    intro S h
    rw [reach_succ M good k S] at h
    rw [reach_succ M good (k + 1) S]
    simp only [Bool.or_eq_true, List.any_eq_true] at h ⊢
    rcases h with h | ⟨t, ht, e⟩
    · exact Or.inl h
    · exact Or.inr ⟨t, ht, ih _ e⟩
lemma getD_mem_zero (S : List ℕ) (o : ℕ) : S.getD o 0 ∈ (0 :: S) := by
  rw [List.getD_eq_getElem?_getD]
  cases hs : S[o]? with
  | none => simp
  | some v => exact List.mem_cons_of_mem _ (List.mem_of_getElem? hs)
lemma mem_cands_not (M : ℕ) (S : List ℕ) (a : ℕ) (ha : a ∈ (0 :: S)) :
    M ^^^ a ∈ cands M S :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_left _ (List.mem_map_of_mem ha)))))
lemma mem_cands_copy (M : ℕ) (S : List ℕ) (a : ℕ) (ha : a ∈ (0 :: S)) : a ∈ cands M S :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
    (List.mem_append_left _ (List.mem_append_right _ ha))))
lemma mem_cands_and (M : ℕ) (S : List ℕ) (a b : ℕ) (ha : a ∈ (0 :: S)) (hb : b ∈ (0 :: S)) :
    a &&& b ∈ cands M S :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_left _
    (List.mem_append_right _ (List.mem_flatMap.2 ⟨a, ha, List.mem_map_of_mem hb⟩))))
lemma mem_cands_or (M : ℕ) (S : List ℕ) (a b : ℕ) (ha : a ∈ (0 :: S)) (hb : b ∈ (0 :: S)) :
    a ||| b ∈ cands M S :=
  List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_append_right _
    (List.mem_flatMap.2 ⟨a, ha, List.mem_map_of_mem hb⟩)))
lemma gt_mem (M : ℕ) (S : List ℕ) (g : Gate) (hg : GOk g) :
    gt M g.op (g.inputs.map fun i => S.getD i 0) ∈ cands M S := by
  obtain ⟨hop, hl⟩ := hg
  have hm : ∀ i, S.getD i 0 ∈ (0 :: S) := getD_mem_zero S
  generalize g.inputs = ins at hl ⊢
  match ins, hl with
  | [], _ =>
    rcases hop with h | h | h <;> rw [h] <;> simp [gt, cands]
  | [i], _ =>
    rcases hop with h | h | h <;> rw [h] <;> simp only [gt, List.map_cons, List.map_nil]
    · exact mem_cands_copy M S _ (hm i)
    · exact mem_cands_copy M S _ (hm i)
    · exact mem_cands_not M S _ (hm i)
  | [i, j], _ =>
    rcases hop with h | h | h <;> rw [h] <;> simp only [gt, List.map_cons, List.map_nil]
    · exact mem_cands_and M S _ _ (hm i) (hm j)
    · exact mem_cands_or M S _ _ (hm i) (hm j)
    · exact mem_cands_not M S _ (hm i)
lemma reach_sound (M : ℕ) (good : ℕ → Bool) : ∀ (gs : List Gate) (k : ℕ) (S : List ℕ)
    (o : ℕ), gs.length ≤ k → (∀ g ∈ gs, GOk g) → good ((tabs M S gs).getD o 0) = true →
    reach M good k S = true := by
  intro gs
  induction gs with
  | nil =>
    intro k S o _ _ hgood
    apply reach_of_zero
    simp only [reach, List.any_eq_true]
    exact ⟨_, getD_mem_zero S o, hgood⟩
  | cons g gs ih =>
    intro k S o hk hok hgood
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by simp at hk; omega⟩
    have hg := hok g (by simp)
    set t := gt M g.op (g.inputs.map fun i => S.getD i 0) with ht
    have h1 : reach M good k' (S ++ [t]) = true :=
      ih k' (S ++ [t]) o (by simpa using hk) (fun g' hg' => hok g' (by simp [hg'])) hgood
    by_cases hin : t ∈ S
    · have e : reach M good k' (S ++ [t]) = reach M good k' S :=
        reach_congr M good k' _ _ (by intro x; simp only [List.mem_append, List.mem_singleton]
                                      constructor
                                      · rintro (h | rfl) <;> assumption
                                      · exact Or.inl)
      exact reach_mono M good k' S (e ▸ h1)
    · simp only [reach, Bool.or_eq_true, List.any_eq_true]
      exact Or.inr ⟨t, (mem_next M S t).2 ⟨gt_mem M S g hg, hin⟩, h1⟩
lemma mod_eq_of_testBit (B t tgt : ℕ) (htgt : tgt < 2 ^ B)
    (h : ∀ p, p < B → t.testBit p = tgt.testBit p) : t % 2 ^ B = tgt := by
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.testBit_mod_two_pow]
  by_cases hi : i < B
  · simp [hi, h i hi]
  · simp only [hi, decide_false, Bool.false_and]
    symm
    apply Nat.testBit_eq_false_of_lt
    exact lt_of_lt_of_le htgt (Nat.pow_le_pow_right (by norm_num) (by omega))
lemma lower_of_search (n B : ℕ) (f : (Fin n → Bool) → Bool) (T0 : List ℕ) (tgt k : ℕ)
    (htgt : tgt < 2 ^ B)
    (hpt : ∀ p, p < B → ∃ x : Fin n → Bool, List.ofFn x = T0.map (fun t => t.testBit p) ∧
      f x = tgt.testBit p)
    (hsearch : reach (2 ^ B - 1) (fun t => t % 2 ^ B == tgt) k T0 = false) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize n f k := by
  rintro ⟨C, hC, hsize, hev⟩
  have hok : ∀ g ∈ C.gates, GOk g := by
    intro g hg
    obtain ⟨h1, h2⟩ := hC g hg
    refine ⟨?_, h2⟩
    simpa [Set.mem_insert_iff] using h1
  have hgood : (fun t => t % 2 ^ B == tgt) ((tabs (2 ^ B - 1) T0 C.gates).getD C.output 0)
      = true := by
    simp only [beq_iff_eq]
    apply mod_eq_of_testBit B _ tgt htgt
    intro p hp
    obtain ⟨x, hx, hfx⟩ := hpt p hp
    have hM : (2 ^ B - 1).testBit p = true := by
      rw [Nat.testBit_two_pow_sub_one]; simpa using hp
    have := hev x
    rw [hfx] at this
    rw [← this, Circuit.eval, Circuit.wires, hx, wires_tabs _ p hM _ _ hok,
      getD_map_testBit]
  have := reach_sound (2 ^ B - 1) (fun t => t % 2 ^ B == tgt) C.gates k T0 C.output hsize hok hgood
  rw [hsearch] at this
  exact absurd this (by decide)
end PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.TableSearch

namespace PEqualNP.Outside.L_meta_3457.SparseLower.Exchange
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
def StmtExchange : Prop :=
  ∀ (n : ℕ) (C : Circuit) (h : ℕ), FanInTwo C →
    (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = false →
      circuitFun n C x = true) →
    ∃ D : Circuit, FanInTwo D ∧ circuitFun n D = circuitFun n C ∧
      D.size + C.gates.zipIdx.countP (fun p => decide (h < n + p.2) &&
        (match p.1.op with
         | GateOp.not => p.1.inputs.take 1
         | _ => p.1.inputs).contains h) ≤ C.size + 2
def StmtTwoReaders : Prop :=
  ∀ (n : ℕ) (C : Circuit) (h : ℕ), IsMinimalCircuit n C →
    (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = false →
      circuitFun n C x = true) →
    C.gates.zipIdx.countP (fun p => decide (h < n + p.2) &&
        (match p.1.op with
         | GateOp.not => p.1.inputs.take 1
         | _ => p.1.inputs).contains h) ≤ 2
def StmtExchangeShape : Prop :=
  ∀ (n : ℕ) (C : Circuit) (h : ℕ), FanInTwo C →
    (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = false →
      circuitFun n C x = true) →
    ∃ (D : Circuit) (k : ℕ) (σ : ℕ → ℕ) (o : ℕ),
      FanInTwo D ∧ circuitFun n D = circuitFun n C ∧
      k + C.gates.zipIdx.countP (fun p => decide (h < n + p.2) &&
        (match p.1.op with
         | GateOp.not => p.1.inputs.take 1
         | _ => p.1.inputs).contains h) = C.size ∧
      D.gates.length = k + 2 ∧ D.output = n + k + 1 ∧
      D.gates[k]? = some ⟨GateOp.not, [h]⟩ ∧
      D.gates[k + 1]? = some ⟨GateOp.or, [o, n + k]⟩ ∧
      StrictMono σ ∧
      (∀ i, i < k → ∃ g gD, C.gates[σ i]? = some g ∧ D.gates[i]? = some gD ∧
        gD.op = g.op ∧
        ¬ (decide (h < n + σ i) &&
          (match g.op with
           | GateOp.not => g.inputs.take 1
           | _ => g.inputs).contains h) = true ∧
        ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true →
          (D.wires (List.ofFn x)).getD (n + i) false =
            (C.wires (List.ofFn x)).getD (n + σ i) false)
lemma twoReaders_of_exchange (hE : StmtExchange) : StmtTwoReaders := by
  intro n C h hmin hcov
  obtain ⟨D, hD, hfun, hsize⟩ := hE n C h hmin.1 hcov
  have := hmin.2 D hD hfun
  omega
def nand3C : Circuit :=
  ⟨[⟨GateOp.and, [0, 1]⟩, ⟨GateOp.and, [2, 3]⟩, ⟨GateOp.not, [4]⟩], 5⟩
lemma nand3C_hyp :
    FanInTwo nand3C ∧
    (∀ x : Fin 3 → Bool, (nand3C.wires (List.ofFn x)).getD 3 false = false →
      circuitFun 3 nand3C x = true) ∧
    nand3C.gates.zipIdx.countP (fun p => decide (3 < 3 + p.2) &&
        (match p.1.op with
         | GateOp.not => p.1.inputs.take 1
         | _ => p.1.inputs).contains 3) = 1 ∧
    3 ≠ nand3C.output ∧
    (∃ x y : Fin 3 → Bool, circuitFun 3 nand3C x ≠ circuitFun 3 nand3C y) ∧
    (∃ x : Fin 3 → Bool, circuitFun 3 nand3C x ≠ !(nand3C.wires (List.ofFn x)).getD 3 false) := by
  refine ⟨?_, by decide, by decide, by decide, ⟨fun _ => true, fun _ => false, by decide⟩,
    ⟨fun i => decide (i ≠ 2), by decide⟩⟩
  intro g hg
  simp only [nand3C, List.mem_cons, List.mem_nil_iff, or_false] at hg
  rcases hg with rfl | rfl | rfl <;> simp
open PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.TableSearch in
lemma nand3C_minimal : IsMinimalCircuit 3 nand3C := by
  have hlow : ¬ PEqualNP.MetaComplexity.HasCircuitSize 3 (circuitFun 3 nand3C) 2 := by
    apply lower_of_search 3 8 _ [170, 204, 240] 127 2 (by norm_num) _ (by decide +kernel)
    have key : ∀ p, p < 8 → (List.ofFn fun i : Fin 3 => p.testBit i)
        = [170, 204, 240].map (fun t : ℕ => t.testBit p) ∧
        circuitFun 3 nand3C (fun i => p.testBit i) = Nat.testBit 127 p := by decide
    exact fun p hp => ⟨_, key p hp⟩
  refine ⟨nand3C_hyp.1, fun D hD hfun => ?_⟩
  by_contra hlt
  exact hlow ⟨D, hD, by simp [nand3C, Circuit.size] at hlt ⊢; omega,
    fun x => congrFun hfun x⟩
def n4C : Circuit :=
  ⟨[⟨GateOp.and, [0, 4]⟩, ⟨GateOp.and, [1, 4]⟩, ⟨GateOp.not, [5]⟩, ⟨GateOp.not, [6]⟩,
    ⟨GateOp.or, [7, 2]⟩, ⟨GateOp.or, [8, 3]⟩, ⟨GateOp.and, [9, 10]⟩], 11⟩
lemma n4C_hyp :
    (∀ x : Fin 5 → Bool, (n4C.wires (List.ofFn x)).getD 4 false = false →
      circuitFun 5 n4C x = true) ∧
    n4C.gates.zipIdx.countP (fun p => decide (4 < 5 + p.2) &&
        (match p.1.op with
         | GateOp.not => p.1.inputs.take 1
         | _ => p.1.inputs).contains 4) = 2 := by
  refine ⟨?_, by decide⟩
  decide +kernel
def StmtTwoReadersSyntactic : Prop :=
  ∀ (n : ℕ) (C : Circuit) (h : ℕ), IsMinimalCircuit n C →
    (∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = false →
      circuitFun n C x = true) →
    (C.gates.filter fun g => g.inputs.contains h).length ≤ 2
def synC : Circuit :=
  ⟨[⟨GateOp.not, [1, 2]⟩, ⟨GateOp.or, [0, 3]⟩, ⟨GateOp.and, [2, 4]⟩, ⟨GateOp.not, [5, 2]⟩], 6⟩
open PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.TableSearch in
lemma synC_minimal : IsMinimalCircuit 3 synC := by
  have hlow : ¬ PEqualNP.MetaComplexity.HasCircuitSize 3 (circuitFun 3 synC) 3 := by
    apply lower_of_search 3 8 _ [170, 204, 240] 79 3 (by norm_num) _ (by decide +kernel)
    have key : ∀ p, p < 8 → (List.ofFn fun i : Fin 3 => p.testBit i)
        = [170, 204, 240].map (fun t : ℕ => t.testBit p) ∧
        circuitFun 3 synC (fun i => p.testBit i) = Nat.testBit 79 p := by decide
    exact fun p hp => ⟨_, key p hp⟩
  refine ⟨?_, fun D hD hfun => ?_⟩
  · intro g hg
    simp only [synC, List.mem_cons, List.mem_nil_iff, or_false] at hg
    rcases hg with rfl | rfl | rfl | rfl <;> simp
  · by_contra hlt
    exact hlow ⟨D, hD, by simp [synC, Circuit.size] at hlt ⊢; omega,
      fun x => congrFun hfun x⟩
lemma not_twoReadersSyntactic : ¬ StmtTwoReadersSyntactic := by
  intro hS
  have := hS 3 synC 2 synC_minimal (by decide)
  revert this
  decide
lemma synC_semantic :
    synC.gates.zipIdx.countP (fun p => decide (2 < 3 + p.2) &&
        (match p.1.op with
         | GateOp.not => p.1.inputs.take 1
         | _ => p.1.inputs).contains 2) = 1 := by
  decide
end PEqualNP.Outside.L_meta_3457.SparseLower.Exchange

namespace PEqualNP.Outside.L_meta_3457.SparseLower.Exchange
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
lemma elim_prefix (n : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    ∃ t : List Gate, (elim n gs acc).2 = acc.2 ++ t := by
  induction gs with
  | nil => intro acc; exact ⟨[], by simp [elim]⟩
  | cons g gs ih =>
    intro acc
    obtain ⟨t, ht⟩ := ih (elimStep n acc g)
    refine ⟨(simplify g.op (n + acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList ++ t, ?_⟩
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, ht]
    simp [elimStep]
lemma elim_count (n k : ℕ) (gs : List Gate) : ∀ acc : List Stat × List Gate,
    (∀ g ∈ gs, NOk g) → k < acc.1.length →
    (∃ c, acc.1.getD k (Stat.const false) = Stat.const c) →
    (elim n gs acc).2.length + gs.countP (fun g => g.inputs.contains k)
      ≤ acc.2.length + gs.length := by
  induction gs with
  | nil => intro acc _ _ _; simp [elim]
  | cons g gs ih =>
    intro acc hok hk hc
    have h3 : elim n (g :: gs) acc = elim n gs (elimStep n acc g) := rfl
    rw [h3, List.length_cons, List.countP_cons]
    have h1 := ih (elimStep n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
      (by simp [elimStep]; omega)
      (by
        obtain ⟨c, hc⟩ := hc
        refine ⟨c, ?_⟩
        simp only [elimStep]
        rw [getD_snoc_ne _ _ _ _ (by omega)]; exact hc)
    by_cases hkg : k ∈ g.inputs
    · obtain ⟨c, hc⟩ := hc
      have hnok := hok g List.mem_cons_self
      have hnone : (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1 = none := by
        apply simplify_count
        · exact hnok.1.1
        · simpa using hnok.1.2
        · intro h; simpa using hnok.2 h
        · exact ⟨c, List.mem_map.2 ⟨k, hkg, hc⟩⟩
      have h2 : (elimStep n acc g).2.length = acc.2.length := by
        show (acc.2 ++ (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1.toList).length = _
        rw [hnone]; simp
      have hct : g.inputs.contains k = true := by simpa using hkg
      simp only [hct, ↓reduceIte]
      omega
    · have h2 : (elimStep n acc g).2.length ≤ acc.2.length + 1 := by
        simp only [elimStep, List.length_append]
        have := toList_length_le (simplify g.op (n + acc.2.length)
          (g.inputs.map fun i => acc.1.getD i (Stat.const false))).1
        omega
      have hct : g.inputs.contains k = false := by simpa using hkg
      simp only [hct, Bool.false_eq_true, ↓reduceIte]
      omega
lemma countP_zipIdx_le (n h : ℕ) (f : Gate → Bool) : ∀ (l : List Gate) (m : ℕ),
    (l.zipIdx m).countP (fun p => decide (h < n + p.2) && f p.1)
      ≤ (l.drop (h + 1 - n - m)).countP f := by
  intro l
  induction l with
  | nil => intro m; simp
  | cons a l ih =>
    intro m
    rw [List.zipIdx_cons, List.countP_cons]
    have := ih (m + 1)
    by_cases hd : h + 1 - n - m = 0
    · rw [hd, List.drop_zero, List.countP_cons]
      have e : h + 1 - n - (m + 1) = 0 := by omega
      rw [e, List.drop_zero] at this
      have hlt : h < n + m := by omega
      by_cases hfa : f a = true <;> simp [hlt, hfa] <;> omega
    · obtain ⟨d, hd'⟩ : ∃ d, h + 1 - n - m = d + 1 := ⟨h + 1 - n - m - 1, by omega⟩
      rw [hd', List.drop_succ_cons]
      have e : h + 1 - n - (m + 1) = d := by omega
      rw [e] at this
      have hlt : ¬ h < n + m := by omega
      simp [hlt]
      exact this
lemma eff_eq (g : Gate) :
    (match g.op with
     | GateOp.not => g.inputs.take 1
     | _ => g.inputs) = (normGate g).inputs := by
  obtain ⟨op, ins⟩ := g
  cases op <;> rfl
def startStats (m h : ℕ) : List Stat :=
  (List.range m).map fun i => if i = h then Stat.const true else Stat.wire i
lemma startStats_getD (m h i : ℕ) :
    (startStats m h).getD i (Stat.const false) =
      if i < m then (if i = h then Stat.const true else Stat.wire i) else Stat.const false := by
  unfold startStats
  by_cases hi : i < m
  · simp [hi]
  · rw [List.getD_eq_default _ _ (by simp; omega)]; simp [hi]
lemma inv_start (n h : ℕ) (pre : List Gate) (y : List Bool) (hy : y.length = n)
    (hh : (wiresFrom pre y).getD h false = true) :
    Inv n y (wiresFrom pre y) (startStats (n + pre.length) h, pre) := by
  have lw : (wiresFrom pre y).length = n + pre.length := by rw [length_wiresFrom, hy]
  refine ⟨by simp [startStats, lw], ?_⟩
  intro i
  rw [startStats_getD]
  by_cases hi : i < n + pre.length
  · by_cases hih : i = h
    · subst hih; simp only [hi, ite_true]; exact ⟨trivial, hh.symm⟩
    · simp only [hi, hih, ite_true, ite_false]; exact ⟨hi, rfl⟩
  · simp only [hi, ite_false]
    exact ⟨trivial, by rw [List.getD_eq_default _ _ (by omega)]; rfl⟩
lemma exchange_core (n : ℕ) (C : Circuit) (h : ℕ) (f : Gate → Bool)
    (hf : ∀ g, f g = (normGate g).inputs.contains h) (hC : FanInTwo C)
    (hcov : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = false →
      circuitFun n C x = true) :
    ∃ D : Circuit, FanInTwo D ∧ circuitFun n D = circuitFun n C ∧
      D.size + C.gates.zipIdx.countP (fun p => decide (h < n + p.2) && f p.1)
        ≤ C.size + 2 := by
  set r := C.gates.zipIdx.countP (fun p => decide (h < n + p.2) && f p.1) with hr
  have hrle : r ≤ (C.gates.drop (h + 1 - n)).countP
      (fun g => (normGate g).inputs.contains h) := by
    have := countP_zipIdx_le n h f C.gates 0
    simp only [Nat.sub_zero] at this
    rw [hr]
    refine le_trans this (le_of_eq ?_)
    apply List.countP_congr
    intro g _
    rw [hf]
  have hrs : r ≤ C.gates.length := by
    refine le_trans hrle (le_trans (List.countP_le_length) ?_)
    simp
  have hconst : (∀ x : Fin n → Bool, circuitFun n C x = true) →
      ∃ D : Circuit, FanInTwo D ∧ circuitFun n D = circuitFun n C ∧ D.size + r ≤ C.size + 2 := by
    intro hT
    refine ⟨⟨[⟨GateOp.and, []⟩], n⟩, ?_, ?_, ?_⟩
    · intro g hg
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
      subst hg; simp
    · funext x
      rw [hT x]
      show (wiresFrom [⟨GateOp.and, []⟩] (List.ofFn x)).getD n false = true
      simp [wiresFrom, GateOp.eval]
    · simp only [Circuit.size, List.length_cons, List.length_nil]
      omega
  by_cases hex : ∃ x0 : Fin n → Bool, (C.wires (List.ofFn x0)).getD h false = true
  swap
  · apply hconst
    intro x
    apply hcov x
    push Not at hex
    simpa using hex x
  obtain ⟨x0, hx0⟩ := hex
  have hhs : h < n + C.size := by
    by_contra hlt
    rw [List.getD_eq_default _ _ (by
      rw [wires_eq, length_wiresFrom]; simp [Circuit.size] at hlt ⊢; omega)] at hx0
    cases hx0
  set k := h + 1 - n with hk
  have hks : k ≤ C.gates.length := by simp [Circuit.size] at hhs; omega
  have hhk : h < n + k := by omega
  set gs := C.gates.map normGate with hgs
  set pre := gs.take k with hpre
  set post := gs.drop k with hpost
  have hlpre : pre.length = k := by simp [hpre, hgs]; omega
  have hlpost : post.length = C.gates.length - k := by simp [hpost, hgs]
  have hnok : ∀ g ∈ gs, NOk g := by
    intro g hg
    obtain ⟨g0, hg0, rfl⟩ := List.mem_map.1 hg
    exact normGate_nok g0 (hC g0 hg0)
  have hnokpost : ∀ g ∈ post, NOk g := fun g hg => hnok g (List.mem_of_mem_drop hg)
  have hokpre : ∀ g ∈ pre, Ok g := fun g hg => (hnok g (List.mem_of_mem_take hg)).1
  have hwC : ∀ y : List Bool, C.wires y = wiresFrom post (wiresFrom pre y) := by
    intro y
    rw [← wiresFrom_append, hpre, hpost, List.take_append_drop, hgs, wiresFrom_norm]; rfl
  have hyl : ∀ x : Fin n → Bool, (List.ofFn x).length = n := by simp
  have hwh : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false
      = (wiresFrom pre (List.ofFn x)).getD h false := by
    intro x
    rw [hwC, getD_wiresFrom _ _ _ (by rw [length_wiresFrom, hyl, hlpre]; exact hhk)]
  set acc := elim n post (startStats (n + pre.length) h, pre) with hacc
  have hinv : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true →
      Inv n (List.ofFn x) (C.wires (List.ofFn x)) acc := by
    intro x hx
    rw [hwC, hacc]
    exact inv_elim n _ (hyl x) post _ _ (fun g hg => (hnokpost g hg).1)
      (inv_start n h pre _ (hyl x) (by rw [← hwh]; exact hx))
  obtain ⟨t, ht⟩ := elim_prefix n post (startStats (n + pre.length) h, pre)
  rw [← hacc] at ht
  have hcount := elim_count n h post (startStats (n + pre.length) h, pre) hnokpost
    (by simp [startStats]; omega)
    ⟨true, by rw [startStats_getD]; simp [hhk, hlpre]⟩
  rw [← hacc] at hcount
  have hR : post.countP (fun g => g.inputs.contains h)
      = (C.gates.drop k).countP (fun g => (normGate g).inputs.contains h) := by
    rw [hpost, hgs, ← List.map_drop, List.countP_map]; rfl
  have hLk : acc.2.length = k + t.length := by rw [ht]; simp [hlpre]
  have hsize : acc.2.length + r ≤ C.gates.length := by
    change acc.2.length + post.countP (fun g => g.inputs.contains h)
      ≤ pre.length + post.length at hcount
    rw [hlpre, hlpost, hR] at hcount
    omega
  have hwhA : ∀ x : Fin n → Bool, (wiresFrom acc.2 (List.ofFn x)).getD h false
      = (C.wires (List.ofFn x)).getD h false := by
    intro x
    rw [ht, wiresFrom_append, hwh,
      getD_wiresFrom _ _ _ (by rw [length_wiresFrom, hyl, hlpre]; exact hhk)]
  have hval : ∀ x : Fin n → Bool, (C.wires (List.ofFn x)).getD h false = true →
      (acc.1.getD C.output (Stat.const false)).val (wiresFrom acc.2 (List.ofFn x))
        = circuitFun n C x := by
    intro x hx
    exact ((hinv x hx).2 C.output).2
  have hvalid : (acc.1.getD C.output (Stat.const false)).Valid (n + acc.2.length) :=
    ((hinv x0 hx0).2 C.output).1
  cases hst : acc.1.getD C.output (Stat.const false) with
  | const c =>
    cases c with
    | true =>
      apply hconst
      intro x
      by_cases hx : (C.wires (List.ofFn x)).getD h false = true
      · rw [← hval x hx, hst]; rfl
      · exact hcov x (by simpa using hx)
    | false =>
      refine ⟨⟨pre ++ [⟨GateOp.not, [h]⟩], n + k⟩, ?_, ?_, ?_⟩
      · intro g hg
        rcases List.mem_append.1 hg with hg | hg
        · exact hokpre g hg
        · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
          subst hg; simp
      · funext x
        show (wiresFrom (pre ++ [⟨GateOp.not, [h]⟩]) (List.ofFn x)).getD (n + k) false = _
        rw [wiresFrom_append]
        have hl : (wiresFrom pre (List.ofFn x)).length = n + k := by
          rw [length_wiresFrom, hyl, hlpre]
        show ((wiresFrom pre (List.ofFn x)) ++ [GateOp.not.eval
          ([h].map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]).getD (n + k) false = _
        rw [getD_snoc_len _ _ _ _ hl]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
        rw [← hwh]
        by_cases hx : (C.wires (List.ofFn x)).getD h false = true
        · rw [hx, ← hval x hx, hst]; rfl
        · rw [hcov x (by simpa using hx)]; simpa using hx
      · simp only [Circuit.size, List.length_append, List.length_cons, List.length_nil, hlpre]
        omega
  | wire j =>
    rw [hst] at hvalid
    have hj : j < n + acc.2.length := hvalid
    set L := acc.2.length with hL
    refine ⟨⟨acc.2 ++ [⟨GateOp.not, [h]⟩, ⟨GateOp.or, [j, n + L]⟩], n + L + 1⟩, ?_, ?_, ?_⟩
    · intro g hg
      rcases List.mem_append.1 hg with hg | hg
      · exact elim_ok n post _ hokpre g hg
      · simp only [List.mem_cons, List.mem_nil_iff, or_false] at hg
        rcases hg with rfl | rfl <;> simp
    · funext x
      show (wiresFrom (acc.2 ++ [⟨GateOp.not, [h]⟩, ⟨GateOp.or, [j, n + L]⟩])
        (List.ofFn x)).getD (n + L + 1) false = _
      rw [wiresFrom_append]
      set W := wiresFrom acc.2 (List.ofFn x) with hW
      have hl : W.length = n + L := by rw [hW, length_wiresFrom, hyl]
      set W' := W ++ [GateOp.not.eval ([h].map fun i => W.getD i false)] with hW'
      have hl' : W'.length = n + L + 1 := by simp [hW', hl]
      show (W' ++ [GateOp.or.eval ([j, n + L].map fun i => W'.getD i false)]).getD
        (n + L + 1) false = _
      rw [getD_snoc_len _ _ _ _ hl']
      have e1 : W'.getD j false = W.getD j false := List.getD_append _ _ _ _ (by omega)
      have e2 : W'.getD (n + L) false = !(W.getD h false) := by
        rw [hW', getD_snoc_len _ _ _ _ hl]; simp [GateOp.eval]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
        id, Bool.or_false, e1, e2]
      rw [hW, hwhA]
      by_cases hx : (C.wires (List.ofFn x)).getD h false = true
      · rw [hx, ← hval x hx, hst]; simp [Stat.val]
      · have hx' : (C.wires (List.ofFn x)).getD h false = false := by simpa using hx
        rw [hcov x hx', hx']; simp
    · simp only [Circuit.size, List.length_append, List.length_cons, List.length_nil]
      omega
lemma exchange' : StmtExchange := by
  intro n C h hC hcov
  exact exchange_core n C h (fun g => (match g.op with
         | GateOp.not => g.inputs.take 1
         | _ => g.inputs).contains h)
    (fun g => by obtain ⟨op, ins⟩ := g; cases op <;> rfl) hC hcov
lemma twoReaders' : StmtTwoReaders := twoReaders_of_exchange exchange'
end PEqualNP.Outside.L_meta_3457.SparseLower.Exchange

namespace PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
open PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Readers
lemma exch_startStats_length (m h : ℕ) : (Exchange.startStats m h).length = m := by
  simp [Exchange.startStats]
lemma exch_clean_take (N k : ℕ) (gs : List Gate) (hcl : CleanL N gs) :
    CleanL N (gs.take k) := by
  intro p g hp
  rw [List.getElem?_take] at hp
  by_cases hpk : p < k
  · rw [if_pos hpk] at hp; exact hcl p g hp
  · rw [if_neg hpk] at hp; cases hp
lemma exch_const_reader (N : ℕ) (post : List Gate) (acc : List Stat × List Gate)
    (hok : ∀ g ∈ post, NOk g) (h q : ℕ) (g : Gate) (hq : post[q]? = some g)
    (hop : g.op = GateOp.or ∨ g.op = GateOp.not) (hh : h ∈ g.inputs) (hlt : h < acc.1.length)
    (hst : acc.1.getD h (Stat.const false) = Stat.const true) :
    ∃ c, (elim N post acc).1.getD (acc.1.length + q) (Stat.const false) = Stat.const c := by
  obtain ⟨pre, post', rfl, rfl⟩ := split_at post q g hq
  rw [elim_split_getD N pre g post' acc _ _ (le_refl _)]
  have hgok : NOk g := hok g (by simp)
  have hl : (elim N pre acc).1.length = acc.1.length + pre.length := elim_fst_len N pre acc
  simp only [elimStep]
  rw [getD_snoc_len _ _ _ _ hl]
  apply simplify_const _ _ _ hgok.1.1 (by simpa using hgok.1.2)
    (fun h' => by simpa using hgok.2 h') true
  · intro h'; rcases hop with h2 | h2 <;> rw [h2] at h' <;> cases h'
  · intro _; rfl
  · refine List.mem_map.2 ⟨h, hh, ?_⟩
    rw [elim_getD N h _ pre acc hlt]; exact hst
lemma stmtExch : StmtExch := by
  intro N F gs o h T hcl hev hnc hcov hT
  have hyl : ∀ x : Fin N → Bool, (List.ofFn x).length = N := by simp
  have hnotT : ¬ ∀ x : Fin N → Bool, F x = true := by
    intro hT'
    obtain ⟨x, y, hxy⟩ := hnc
    exact hxy (by rw [hT' x, hT' y])
  have hex : ∃ x0 : Fin N → Bool, vl gs x0 h = true := by
    by_contra hne
    push Not at hne
    exact hnotT fun x => hcov x (by simpa using hne x)
  obtain ⟨x0, hx0⟩ := hex
  have hhs : h < N + gs.length := by
    by_contra hlt
    rw [vl_beyond gs x0 h (by omega)] at hx0
    cases hx0
  set k := h + 1 - N with hk
  have hks : k ≤ gs.length := by omega
  have hhk : h < N + k := by omega
  set pre := gs.take k with hpre
  set post := gs.drop k with hpost
  have hlpre : pre.length = k := by simp [hpre]; omega
  have hlpost : post.length = gs.length - k := by simp [hpost]
  have hnok : ∀ g ∈ gs, NOk g := clean_nok N gs hcl
  have hnokpost : ∀ g ∈ post, NOk g := fun g hg => hnok g (List.mem_of_mem_drop hg)
  have hclpre : CleanL N pre := exch_clean_take N k gs hcl
  have hwg : ∀ y : List Bool, wiresFrom gs y = wiresFrom post (wiresFrom pre y) := by
    intro y
    rw [← wiresFrom_append, hpre, hpost, List.take_append_drop]
  have hwh : ∀ x : Fin N → Bool, vl gs x h = (wiresFrom pre (List.ofFn x)).getD h false := by
    intro x
    show (wiresFrom gs (List.ofFn x)).getD h false = _
    rw [hwg, getD_wiresFrom _ _ _ (by rw [length_wiresFrom, hyl, hlpre]; exact hhk)]
  set acc0 : List Stat × List Gate := (Exchange.startStats (N + pre.length) h, pre) with hacc0
  have hl0 : acc0.1.length = N + k := by
    rw [hacc0, exch_startStats_length, hlpre]
  set acc := elim N post acc0 with hacc
  have hinv : ∀ x : Fin N → Bool, vl gs x h = true →
      Inv N (List.ofFn x) (wiresFrom gs (List.ofFn x)) acc := by
    intro x hx
    rw [hwg, hacc]
    exact inv_elim N _ (hyl x) post _ _ (fun g hg => (hnokpost g hg).1)
      (Exchange.inv_start N h pre _ (hyl x) (by rw [← hwh]; exact hx))
  obtain ⟨tl, htl⟩ := Exchange.elim_prefix N post acc0
  rw [← hacc] at htl
  have hLk : acc.2.length = k + tl.length := by rw [htl]; simp [hacc0, hlpre]
  have hclacc : CleanL N acc.2 :=
    clean_elim N (List.ofFn x0) (hyl x0) post _ _ (fun g hg => (hnokpost g hg).1)
      (Exchange.inv_start N h pre _ (hyl x0) (by rw [← hwh]; exact hx0)) hclpre
  have hsth0 : acc0.1.getD h (Stat.const false) = Stat.const true := by
    rw [hacc0, Exchange.startStats_getD]; simp [hlpre, hhk]
  have hsth : acc.1.getD h (Stat.const false) = Stat.const true := by
    rw [hacc, elim_getD N h _ post acc0 (by omega)]; exact hsth0
  have hTk : ∀ t ∈ T, k ≤ t := by
    intro t ht
    rcases hT t ht with hr | ⟨r, g, _, _, hrh, htr⟩
    · have := reads_lt hcl hr; omega
    · have := reads_lt hcl hrh; have := reads_lt hcl htr; omega
  have hcount := Helpers.elim_count N acc0 post hnokpost (T.image fun t => t - k) (by
    intro p hp
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hp
    have htk := hTk t ht
    have hpt : post[t - k]? = gs[t]? := by
      rw [hpost, List.getElem?_drop]; congr 1; omega
    rcases hT t ht with ⟨g, hg, hhg⟩ | ⟨r, g', hg', hop, hrh, ⟨g, hg, hrg⟩⟩
    · refine ⟨g, by rw [hpt]; exact hg, h, hhg, ?_, true, ?_⟩
      · have := (hcl t g hg).lt h hhg; omega
      · rw [← hacc]; exact hsth
    · refine ⟨g, by rw [hpt]; exact hg, N + r, hrg, ?_, ?_⟩
      · have := (hcl t g hg).lt _ hrg; omega
      · have hrk : k ≤ r := by have := reads_lt hcl hrh; omega
        obtain ⟨g'', hg'', hhg''⟩ := hrh
        rw [hg'] at hg''
        cases hg''
        have hpr : post[r - k]? = some g' := by
          rw [hpost, List.getElem?_drop]
          have e : k + (r - k) = r := by omega
          rw [e]; exact hg'
        obtain ⟨c, hc⟩ := exch_const_reader N post acc0 hnokpost h (r - k) g' hpr hop hhg''
          (by omega) hsth0
        refine ⟨c, ?_⟩
        have e : acc0.1.length + (r - k) = N + r := by omega
        rw [e] at hc; exact hc)
  have hcard : (T.image fun t => t - k).card = T.card := by
    apply Finset.card_image_of_injOn
    intro a ha b hb hab
    have := hTk a ha; have := hTk b hb
    simp only at hab; omega
  rw [hcard, ← hacc] at hcount
  have hsize : acc.2.length + T.card ≤ gs.length := by
    have : acc0.2.length = k := by simp [hacc0, hlpre]
    omega
  have hwhA : ∀ x : Fin N → Bool, (wiresFrom acc.2 (List.ofFn x)).getD h false = vl gs x h := by
    intro x
    rw [htl, wiresFrom_append, hwh, getD_wiresFrom _ _ _ (by
      rw [length_wiresFrom, hyl]; simp [hacc0, hlpre]; exact hhk)]
  have hval : ∀ x : Fin N → Bool, vl gs x h = true →
      (acc.1.getD o (Stat.const false)).val (wiresFrom acc.2 (List.ofFn x)) = F x := by
    intro x hx
    rw [((hinv x hx).2 o).2, ← hev x]; rfl
  have hvalid : (acc.1.getD o (Stat.const false)).Valid (N + acc.2.length) :=
    ((hinv x0 hx0).2 o).1
  cases hst : acc.1.getD o (Stat.const false) with
  | const c =>
    cases c with
    | true =>
      exfalso
      apply hnotT
      intro x
      by_cases hx : vl gs x h = true
      · rw [← hval x hx, hst]; rfl
      · exact hcov x (by simpa using hx)
    | false =>
      refine ⟨pre ++ [⟨GateOp.not, [h]⟩], N + k, ?_, ?_, ?_⟩
      · intro p g hp
        by_cases hlt : p < pre.length
        · rw [List.getElem?_append_left hlt] at hp; exact hclpre p g hp
        · rw [List.getElem?_append_right (by omega)] at hp
          have hp0 : p - pre.length = 0 := by
            by_contra hne
            rw [List.getElem?_singleton, if_neg hne] at hp; cases hp
          rw [hp0, List.getElem?_singleton, if_pos rfl] at hp
          cases hp
          have hpl : p = k := by omega
          rw [hpl]
          exact Or.inl ⟨rfl, h, by omega, rfl⟩
      · intro x
        show (wiresFrom (pre ++ [⟨GateOp.not, [h]⟩]) (List.ofFn x)).getD (N + k) false = _
        rw [wiresFrom_append]
        have hl : (wiresFrom pre (List.ofFn x)).length = N + k := by
          rw [length_wiresFrom, hyl, hlpre]
        show ((wiresFrom pre (List.ofFn x)) ++ [GateOp.not.eval
          ([h].map fun i => (wiresFrom pre (List.ofFn x)).getD i false)]).getD (N + k) false = _
        rw [getD_snoc_len _ _ _ _ hl]
        simp only [List.map_cons, List.map_nil, GateOp.eval, List.headD_cons]
        rw [← hwh]
        by_cases hx : vl gs x h = true
        · rw [hx, ← hval x hx, hst]; rfl
        · rw [hcov x (by simpa using hx)]; simpa using hx
      · simp only [List.length_append, List.length_cons, List.length_nil, hlpre]
        omega
  | wire j =>
    rw [hst] at hvalid
    have hj : j < N + acc.2.length := hvalid
    set L := acc.2.length with hL
    refine ⟨acc.2 ++ [⟨GateOp.not, [h]⟩, ⟨GateOp.or, [j, N + L]⟩], N + L + 1, ?_, ?_, ?_⟩
    · intro p g hp
      by_cases hlt : p < L
      · rw [List.getElem?_append_left hlt] at hp; exact hclacc p g hp
      · rw [List.getElem?_append_right (by omega)] at hp
        by_cases h0 : p - L = 0
        · rw [h0] at hp
          simp only [List.getElem?_cons_zero, Option.some.injEq] at hp
          subst hp
          have hpl : p = L := by omega
          rw [hpl]
          exact Or.inl ⟨rfl, h, by omega, rfl⟩
        · by_cases h1 : p - L = 1
          · rw [h1] at hp
            simp only [List.getElem?_cons_succ, List.getElem?_cons_zero,
              Option.some.injEq] at hp
            subst hp
            have hpl : p = L + 1 := by omega
            rw [hpl]
            exact Or.inr ⟨Or.inr rfl, j, N + L, by omega, by omega, rfl⟩
          · obtain ⟨d, hd⟩ : ∃ d, p - L = d + 2 := ⟨p - L - 2, by omega⟩
            rw [hd] at hp
            simp at hp
    · intro x
      show (wiresFrom (acc.2 ++ [⟨GateOp.not, [h]⟩, ⟨GateOp.or, [j, N + L]⟩])
        (List.ofFn x)).getD (N + L + 1) false = _
      rw [wiresFrom_append]
      set W := wiresFrom acc.2 (List.ofFn x) with hW
      have hl : W.length = N + L := by rw [hW, length_wiresFrom, hyl]
      set W' := W ++ [GateOp.not.eval ([h].map fun i => W.getD i false)] with hW'
      have hl' : W'.length = N + L + 1 := by simp [hW', hl]
      show (W' ++ [GateOp.or.eval ([j, N + L].map fun i => W'.getD i false)]).getD
        (N + L + 1) false = _
      rw [getD_snoc_len _ _ _ _ hl']
      have e1 : W'.getD j false = W.getD j false := List.getD_append _ _ _ _ (by omega)
      have e2 : W'.getD (N + L) false = !(W.getD h false) := by
        rw [hW', getD_snoc_len _ _ _ _ hl]; simp [GateOp.eval]
      simp only [List.map_cons, List.map_nil, GateOp.eval, List.any_cons, List.any_nil,
        id, Bool.or_false, e1, e2]
      rw [hW, hwhA]
      by_cases hx : vl gs x h = true
      · rw [hx, ← hval x hx, hst]; simp [Stat.val]
      · have hx' : vl gs x h = false := by simpa using hx
        rw [hcov x hx', hx']; simp
    · simp only [List.length_append, List.length_cons, List.length_nil]
      omega
end PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn

namespace PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
open PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Readers
lemma out_lt_of_nc {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hev : ∀ x, vl gs x o = F x) (hnc : ∃ x y : Fin N → Bool, F x ≠ F y) :
    o < N + gs.length := by
  by_contra hc
  obtain ⟨x, y, hxy⟩ := hnc
  apply hxy
  rw [← hev x, ← hev y, vl_beyond _ x o (by omega), vl_beyond _ y o (by omega)]
lemma stmtLift : StmtLift := by
  intro N F gs o p l h g hle hnc hg hop hin hbel
  have hcl := hle.hcl
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  have hlen := rdel_length N p l gs hp
  have ho := out_lt_of_nc hle.hev hnc
  have hlh : l < N + p ∧ h < N + p := by
    rcases hcl p g hg with ⟨h1, _⟩ | ⟨_, j, k, hj, hk, h2⟩
    · rw [hop] at h1; cases h1
    · rcases hin with e | e <;> rw [e] at h2 <;> simp at h2 <;> omega
  obtain ⟨hl, hh⟩ := hlh
  have hS : ∀ x : Fin N → Bool, vl gs x h = false → vl gs x (N + p) = vl gs x l := by
    intro x hx
    rw [vl_gate _ hcl x p g hg, hop]
    rcases hin with e | e <;> rw [e] <;> simp [hx, GateOp.eval]
  have hro : rd N p l o < N + (gs.length - 1) := by
    unfold rd; split_ifs <;> omega
  set gs2 := rdel N p l gs ++ [⟨GateOp.or, [rd N p l o, h]⟩] with hgs2
  have hcl' := rdel_clean N p l gs hcl hp hl
  have hcl2 : CleanL N gs2 := by
    intro j g' hj
    by_cases hj' : j < (rdel N p l gs).length
    · rw [hgs2, List.getElem?_append_left hj'] at hj
      exact hcl' j g' hj
    · rw [hgs2, List.getElem?_append_right (by omega)] at hj
      obtain ⟨e1, e2⟩ := List.getElem?_eq_some_iff.1 hj
      simp at e1
      have ej : j = (rdel N p l gs).length := by omega
      subst ej
      simp at e2
      subst e2
      exact Or.inr ⟨Or.inr rfl, rd N p l o, h, by omega, by omega, rfl⟩
  have hlast : (gs2)[gs.length - 1]? = some ⟨GateOp.or, [rd N p l o, h]⟩ := by
    rw [hgs2, List.getElem?_append_right (by omega)]
    rw [show gs.length - 1 - (rdel N p l gs).length = 0 by omega]; rfl
  have hval : ∀ x : Fin N → Bool, vl gs2 x (N + (gs.length - 1)) = F x := by
    intro x
    rw [vl_gate _ hcl2 x _ _ hlast]
    have e1 : vl gs2 x (rd N p l o) = vl (rdel N p l gs) x (rd N p l o) :=
      vl_append_lt _ _ x _ (by omega)
    have e2 : vl gs2 x h = vl gs x h := by
      rw [vl_append_lt _ _ x _ (by omega), rdel_prefix N p l gs hcl hp hl x h hh]
    simp only [List.map, GateOp.eval, e1, e2]
    cases hx : vl gs x h
    · rw [rdel_all N p l gs hcl hp hl x (hS x hx) o, hle.hev x]; simp
    · rw [hbel x hx]; simp
  refine ⟨least_of hle hcl2 hval (by simp [hgs2]; omega), ?_⟩
  intro hnt t ht
  have hpt := ht.lt_of_not hp hnt
  have := tailGE_rdel_app N F gs [⟨GateOp.or, [rd N p l o, h]⟩] p l t
    (fun x : Fin N → Bool => vl gs x h = false) hcl hp hl ht hpt hS
    (fun x hx => hbel x (by simpa using hx)) ?_
  · simpa using this
  · intro i hi
    simp at hi
    subst hi
    refine ⟨_, by simpa using hlast, Or.inr ⟨rfl, fun x hx => ?_⟩⟩
    rw [← hval x]; simpa using hx
end PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn

namespace PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
open PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Readers
lemma not_tailOK_and {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {j : ℕ} {g : Gate}
    (hg : gs[j]? = some g) (hop : g.op = GateOp.and) : ¬ TailOK N F gs j := by
  rintro ⟨g0, hg0, h | ⟨h, _⟩⟩ <;>
  · rw [hg] at hg0
    cases hg0
    rw [hop] at h
    cases h
lemma vl_and_true {N : ℕ} (gs : List Gate) (hcl : CleanL N gs) (x : Fin N → Bool) (p l h : ℕ)
    (g : Gate) (hg : gs[p]? = some g) (hop : g.op = GateOp.and)
    (hin : g.inputs = [l, h] ∨ g.inputs = [h, l]) (hx : vl gs x h = true) :
    vl gs x (N + p) = vl gs x l := by
  rw [vl_gate gs hcl x p g hg, hop]
  rcases hin with hi | hi <;> rw [hi] <;> simp [GateOp.eval, hx]
lemma stmtXMove : StmtXMove := by
  intro N F gs o p p' l q h g g' hL hnc hpp hg hop hin hg' hop' hin' hbel
  have hcl := hL.hcl
  have hp's : p' < gs.length := (List.getElem?_eq_some_iff.1 hg').1
  have hl : l < N + p := (hcl p g hg).lt l (by rcases hin with hi | hi <;> simp [hi])
  have hh : h < N + p := (hcl p g hg).lt h (by rcases hin with hi | hi <;> simp [hi])
  have hq : q < N + p' := (hcl p' g' hg').lt q (by rcases hin' with hi | hi <;> simp [hi])
  have ho : o < N + gs.length := by
    by_contra hc
    obtain ⟨x, y, hxy⟩ := hnc
    apply hxy
    rw [← hL.hev x, ← hL.hev y, vl_beyond _ x o (by omega), vl_beyond _ y o (by omega)]
  have hcl1 := rdel_clean N p' q gs hcl hp's hq
  have hlen1 := rdel_length N p' q gs hp's
  have hp1 : p < (rdel N p' q gs).length := by omega
  have hg1 : (rdel N p' q gs)[p]? = some g := by rw [rdel_get_lt N p' q gs hp's p hpp, hg]
  have hcl2 := rdel_clean N p l (rdel N p' q gs) hcl1 hp1 hl
  have hlen2 := rdel_length N p l (rdel N p' q gs) hp1
  have ho2 : rd N p l (rd N p' q o) < N + (rdel N p l (rdel N p' q gs)).length := by
    unfold rd
    split_ifs <;> omega
  have hh2 : h < N + (rdel N p l (rdel N p' q gs)).length := by omega
  have hgood : ∀ x : Fin N → Bool, vl gs x h = true →
      vl (rdel N p l (rdel N p' q gs)) x (rd N p l (rd N p' q o)) = F x ∧
      vl (rdel N p l (rdel N p' q gs)) x h = true := by
    intro x hx
    have hx1 := vl_and_true gs hcl x p' q h g' hg' hop' hin' hx
    have hx2 : vl (rdel N p' q gs) x (N + p) = vl (rdel N p' q gs) x l := by
      rw [rdel_prefix N p' q gs hcl hp's hq x (N + p) (by omega),
        rdel_prefix N p' q gs hcl hp's hq x l (by omega)]
      exact vl_and_true gs hcl x p l h g hg hop hin hx
    refine ⟨?_, ?_⟩
    · rw [rdel_all N p l _ hcl1 hp1 hl x hx2, rdel_all N p' q gs hcl hp's hq x hx1, hL.hev x]
    · rw [rdel_prefix N p l _ hcl1 hp1 hl x h hh,
        rdel_prefix N p' q gs hcl hp's hq x h (by omega), hx]
  set gs2 := rdel N p l (rdel N p' q gs) with hgs2
  set o2 := rd N p l (rd N p' q o) with ho2def
  set new : List Gate := [⟨GateOp.not, [h]⟩, ⟨GateOp.or, [o2, N + gs2.length]⟩] with hnew
  have hget0 : (gs2 ++ new)[gs2.length]? = some ⟨GateOp.not, [h]⟩ := by simp [hnew]
  have hget1 : (gs2 ++ new)[gs2.length + 1]? = some ⟨GateOp.or, [o2, N + gs2.length]⟩ := by
    simp [hnew]
  have hclA : CleanL N (gs2 ++ new) := by
    intro j g0 hj
    by_cases hj2 : j < gs2.length
    · rw [List.getElem?_append_left hj2] at hj
      exact hcl2 j g0 hj
    · rw [List.getElem?_append_right (by omega)] at hj
      have hjl : j - gs2.length < 2 := by
        have := (List.getElem?_eq_some_iff.1 hj).1
        simpa [hnew] using this
      rcases (by omega : j - gs2.length = 0 ∨ j - gs2.length = 1) with e | e
      · rw [e] at hj
        simp [hnew] at hj
        subst hj
        exact Or.inl ⟨rfl, h, by omega, rfl⟩
      · rw [e] at hj
        simp [hnew] at hj
        subst hj
        exact Or.inr ⟨Or.inr rfl, o2, N + gs2.length, by omega, by omega, rfl⟩
  have hvtop : ∀ x : Fin N → Bool, vl (gs2 ++ new) x (N + (gs2.length + 1)) = F x := by
    intro x
    have h0 : vl (gs2 ++ new) x (N + gs2.length) = !vl gs2 x h := by
      rw [vl_gate _ hclA x _ _ hget0]
      simp [GateOp.eval, vl_append_lt gs2 new x h hh2]
    rw [vl_gate _ hclA x _ _ hget1]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
      Bool.or_false]
    rw [h0, vl_append_lt gs2 new x o2 ho2]
    by_cases hx : vl gs x h = true
    · obtain ⟨e1, e2⟩ := hgood x hx
      rw [e1, e2]
      simp
    · have hF := hbel x (by simpa using hx)
      have e2 : vl gs2 x h = vl gs x h := by
        rw [hgs2, rdel_prefix N p l _ hcl1 hp1 hl x h hh,
          rdel_prefix N p' q gs hcl hp's hq x h (by omega)]
      rw [hF, e2]
      simp [hx]
  have hlenA : (gs2 ++ new).length = gs.length := by simp [hnew]; omega
  refine ⟨gs2 ++ new, N + (gs2.length + 1),
    least_of hL hclA hvtop (le_of_eq hlenA), ?_⟩
  intro t ht
  have hpt' : p' + t < gs.length := ht.lt_of_not hp's (not_tailOK_and hg' hop')
  have hF : ∀ x : Fin N → Bool, ¬ (vl gs x h = true) → F x = true :=
    fun x hx => hbel x (by simpa using hx)
  have ht1 : TailGE N F (rdel N p' q gs) t := by
    have := tailGE_rdel_app N F gs [] p' q t (fun x => vl gs x h = true) hcl hp's hq ht hpt'
      (fun x hx => vl_and_true gs hcl x p' q h g' hg' hop' hin' hx) hF
      (fun i hi => absurd hi (by simp))
    simpa using this
  have hS2 : ∀ x : Fin N → Bool, vl gs x h = true →
      vl (rdel N p' q gs) x (N + p) = vl (rdel N p' q gs) x l := by
    intro x hx
    rw [rdel_prefix N p' q gs hcl hp's hq x (N + p) (by omega),
      rdel_prefix N p' q gs hcl hp's hq x l (by omega)]
    exact vl_and_true gs hcl x p l h g hg hop hin hx
  have hlen2' : gs2.length = (rdel N p' q gs).length - 1 := by omega
  have := tailGE_rdel_app N F (rdel N p' q gs) new p l t (fun x => vl gs x h = true) hcl1 hp1 hl
    ht1 (by omega) hS2 hF (by
      intro i hi
      have hi2 : i < 2 := by simpa [hnew] using hi
      rw [← hlen2']
      rcases (by omega : i = 0 ∨ i = 1) with rfl | rfl
      · exact ⟨_, by simpa using hget0, Or.inl rfl⟩
      · refine ⟨_, hget1, Or.inr ⟨rfl, fun x hx => ?_⟩⟩
        rw [show N + (gs2.length + 1) = N + (gs2.length + 1) from rfl, hvtop x] at hx
        exact hx)
  simpa [hnew] using this
end PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn

namespace PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
open PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Readers
def andSwap (gs : List Gate) (ph : ℕ) {N : ℕ} (y : Fin N) : List Gate :=
  gs.set ph ⟨GateOp.not, [(y : ℕ)]⟩
lemma andSwap_length (gs : List Gate) (ph : ℕ) {N : ℕ} (y : Fin N) :
    (andSwap gs ph y).length = gs.length := by
  simp [andSwap]
lemma andSwap_get_ne (gs : List Gate) (ph : ℕ) {N : ℕ} (y : Fin N) (r : ℕ) (hr : r ≠ ph) :
    (andSwap gs ph y)[r]? = gs[r]? := by
  simp [andSwap, Ne.symm hr]
lemma andSwap_get_eq (gs : List Gate) (ph : ℕ) {N : ℕ} (y : Fin N) (hph : ph < gs.length) :
    (andSwap gs ph y)[ph]? = some ⟨GateOp.not, [(y : ℕ)]⟩ := by
  simp [andSwap, hph]
lemma andSwap_clean {N : ℕ} (gs : List Gate) (ph : ℕ) (y : Fin N) (hcl : CleanL N gs)
    (hph : ph < gs.length) : CleanL N (andSwap gs ph y) := by
  intro r g' hr'
  by_cases hrp : r = ph
  · subst hrp
    rw [andSwap_get_eq gs r y hph] at hr'
    cases hr'
    exact Or.inl ⟨rfl, y, by omega, rfl⟩
  · rw [andSwap_get_ne gs ph y r hrp] at hr'
    exact hcl r g' hr'
lemma andSwap_agree {N : ℕ} (gs : List Gate) (hcl : CleanL N gs) (p ph l : ℕ) (g : Gate)
    (y : Fin N) (hph : ph < gs.length) (hgp : gs[p]? = some g) (hop : g.op = GateOp.and)
    (hin : g.inputs = [l, N + ph] ∨ g.inputs = [N + ph, l]) (hlne : l ≠ N + ph)
    (hone : ∀ t, Reads gs t (N + ph) → t = p) (x : Fin N → Bool) (hlx : vl gs x l = false) :
    ∀ w, w ≠ N + ph → vl (andSwap gs ph y) x w = vl gs x w := by
  have hcl' := andSwap_clean gs ph y hcl hph
  have hlen := andSwap_length gs ph y
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    intro hw
    by_cases hwk : w < N
    · rw [vl_input _ x w hwk, vl_input gs x w hwk]
    · obtain ⟨r, rfl⟩ : ∃ r, w = N + r := ⟨w - N, by omega⟩
      have hrp : r ≠ ph := fun e => hw (by rw [e])
      cases hr : gs[r]? with
      | none =>
        have hl : gs.length ≤ r := List.getElem?_eq_none_iff.1 hr
        rw [vl_beyond _ x _ (by omega), vl_beyond gs x _ (by omega)]
      | some g' =>
        have hr' : (andSwap gs ph y)[r]? = some g' := by
          rw [andSwap_get_ne gs ph y r hrp]; exact hr
        rw [vl_gate _ hcl' x r g' hr', vl_gate gs hcl x r g' hr]
        by_cases hrp' : r = p
        · subst hrp'
          rw [hgp] at hr
          cases hr
          have hllt : l < N + r := (hcl r g hgp).lt l (by rcases hin with h | h <;> simp [h])
          have hl' : vl (andSwap gs ph y) x l = false := by rw [ih l hllt hlne]; exact hlx
          rw [hop]
          rcases hin with h | h <;> rw [h] <;> simp [GateOp.eval, hl', hlx]
        · congr 1
          apply List.map_congr_left
          intro a ha
          have hlt := (hcl r g' hr).lt a ha
          exact ih a hlt (fun e => hrp' (hone r ⟨g', hr, e ▸ ha⟩))
lemma andUpd_self {N : ℕ} (x : Fin N → Bool) (y : Fin N) (b : Bool) :
    Function.update x y b y = b := Function.update_self y b x
lemma and_core (n : ℕ) (F : (Fin (n + 1) → Bool) → Bool) (gs : List Gate) (o p ph l : ℕ)
    (g : Gate) (y : Fin (n + 1)) (L : Least (n + 1) F gs o) (b : Bool)
    (hnc : ∃ x x' : Fin (n + 1) → Bool,
      F (Function.update x y b) ≠ F (Function.update x' y b))
    (hgp : gs[p]? = some g) (hop : g.op = GateOp.and)
    (hin : g.inputs = [l, n + 1 + ph] ∨ g.inputs = [n + 1 + ph, l]) (hlne : l ≠ n + 1 + ph)
    (hph : ph < gs.length) (hone : ∀ t, Reads gs t (n + 1 + ph) → t = p)
    (ho2 : o ≠ n + 1 + ph)
    (hlx : ∀ x : Fin (n + 1) → Bool, x y = b → vl gs x l = false)
    (S : Finset ℕ) (hS : ∀ q ∈ S, RC n (andSwap gs ph y) y b q) :
    Drop F y b S.card gs.length := by
  have hcl' := andSwap_clean gs ph y L.hcl hph
  have hag : ∀ x : Fin (n + 1) → Bool,
      vl (andSwap gs ph y) (Function.update x y b) o = F (Function.update x y b) := by
    intro x
    rw [andSwap_agree gs L.hcl p ph l g y hph hgp hop hin hlne hone _
      (hlx _ (andUpd_self x y b)) o ho2, L.hev]
  have hnc' : ∃ x x' : Fin (n + 1) → Bool,
      vl (andSwap gs ph y) (Function.update x y b) o
        ≠ vl (andSwap gs ph y) (Function.update x' y b) o := by
    obtain ⟨x, x', h⟩ := hnc
    exact ⟨x, x', by rw [hag, hag]; exact h⟩
  obtain ⟨s', hs', hc⟩ := save n (fun x => vl (andSwap gs ph y) x o) (andSwap gs ph y) o hcl'
    (fun _ => rfl) y b hnc' S hS
  refine ⟨s', by rw [andSwap_length] at hs'; exact hs', ?_⟩
  have e : (fun x : Fin (n + 1) → Bool => F (Function.update x y b))
      = fun x => (fun x => vl (andSwap gs ph y) x o) (Function.update x y b) := by
    funext x
    exact (hag x).symm
  rw [e]
  exact hc
lemma stmtAnd : StmtAnd := by
  intro n F gs o p ph l g y L hnc _hdep hgp hop hin hlit hph hone ho1 ho2
  have hfnc : ∃ x x' : Fin (n + 1) → Bool, F x ≠ F x' := by
    obtain ⟨x, x', h⟩ := hnc false
    exact ⟨_, _, h⟩
  have hlmem : l ∈ g.inputs := by rcases hin with h | h <;> simp [h]
  have hhmem : n + 1 + ph ∈ g.inputs := by rcases hin with h | h <;> simp [h]
  have hp : p < gs.length := (List.getElem?_eq_some_iff.1 hgp).1
  have hphp : n + 1 + ph < n + 1 + p := (L.hcl p g hgp).lt _ hhmem
  have hllt : l < n + 1 + p := (L.hcl p g hgp).lt _ hlmem
  have hlne : l ≠ n + 1 + ph := by
    intro e
    apply L.no_alias hfnc p hp (n + 1 + ph) hphp
    intro u
    rw [vl_gate gs L.hcl u p g hgp, hop]
    rcases hin with h | h <;> rw [h, ← e] <;> simp [GateOp.eval]
  have hcl' := andSwap_clean gs ph y L.hcl hph
  have hgp' : (andSwap gs ph y)[p]? = some g := by
    rw [andSwap_get_ne gs ph y p (by omega)]; exact hgp
  obtain ⟨S, hpS, hSr⟩ := L.live hfnc p hp ho1
  have hSr' : Reads (andSwap gs ph y) S (n + 1 + p) := by
    obtain ⟨g', hg', hm⟩ := hSr
    exact ⟨g', by rw [andSwap_get_ne gs ph y S (by omega)]; exact hg', hm⟩
  have hphR : Reads (andSwap gs ph y) ph y := ⟨_, andSwap_get_eq gs ph y hph, by simp⟩
  have hpR : Reads (andSwap gs ph y) p l := ⟨g, hgp', hlmem⟩
  refine ⟨fun hly => ?_, fun hly => ?_⟩
  ·
    subst hly
    have hlx : ∀ x : Fin (n + 1) → Bool, x y = false → vl gs x y = false := by
      intro x hx
      rw [vl_input gs x y y.isLt]
      exact hx
    have hcp : IsC n (andSwap gs ph y) y false (n + 1 + p) :=
      isC_reader hcl' y p g hgp' hlmem false (Or.inr (by simp [fixBit, hop]))
    have h3 := and_core n F gs o p ph y g y L false (hnc false) hgp hop hin hlne hph hone ho2 hlx
      {ph, p, S} (by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact rc_input false hphR
        · exact rc_input false hpR
        · exact rc_of_reads hSr' hcp)
    rwa [Finset.card_eq_three.2 ⟨ph, p, S, by omega, by omega, by omega, rfl⟩] at h3
  ·
    rcases hlit with e | ⟨pn, rfl, hpn⟩
    · exact absurd e hly
    have hpnp : pn < p := by omega
    have hpnph : pn ≠ ph := fun e => hlne (by rw [e])
    have hpn' : (andSwap gs ph y)[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩ := by
      rw [andSwap_get_ne gs ph y pn hpnph]; exact hpn
    have hlx : ∀ x : Fin (n + 1) → Bool, x y = true → vl gs x (n + 1 + pn) = false := by
      intro x hx
      rw [vl_not gs L.hcl x pn _ hpn (y : ℕ) rfl rfl, vl_input gs x y y.isLt]
      simp [hx]
    have hpnR : Reads (andSwap gs ph y) pn y := ⟨_, hpn', by simp⟩
    obtain ⟨c, hc⟩ := isC_reader hcl' y pn _ hpn' (by simp) true (Or.inl rfl)
    have hc0 : c = false := by
      have h1 := st_val_const n _ hcl' y true _ c hc (fun _ => false)
      rw [vl_not _ hcl' _ pn _ hpn' (y : ℕ) rfl rfl, vl_input _ _ y y.isLt] at h1
      simp [ins] at h1
      exact h1
    subst hc0
    have hcp : IsC n (andSwap gs ph y) y true (n + 1 + p) :=
      const_read n _ hcl' y true p g hgp' (n + 1 + pn) hlmem (by simp [hc, fixBit, hop])
    have h4 := and_core n F gs o p ph (n + 1 + pn) g y L true (hnc true) hgp hop hin hlne hph
      hone ho2 hlx {ph, pn, p, S} (by
        intro q hq
        simp only [Finset.mem_insert, Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl | rfl
        · exact rc_input true hphR
        · exact rc_input true hpnR
        · exact rc_of_reads hpR ⟨false, hc⟩
        · exact rc_of_reads hSr' hcp)
    have hcard : ({ph, pn, p, S} : Finset ℕ).card = 4 := by
      rw [Finset.card_insert_of_notMem (by simp; omega),
        Finset.card_eq_three.2 ⟨pn, p, S, by omega, by omega, by omega, rfl⟩]
    rwa [hcard] at h4
end PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn

namespace PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
open PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Readers
lemma vl_dfree {N : ℕ} {D : Finset (Fin N)} {gs : List Gate} {h : ℕ} (hD : DFree D gs h)
    (u u' : Fin N → Bool) (hu : ∀ i, i ∉ D → u i = u' i) : vl gs u h = vl gs u' h := by
  unfold vl
  exact (agree_wiresFrom u u' gs _ _ _ (agree_inputs _ _)).2.2 h (fun i hi =>
    hu i (fun hiD => hD i hiD hi))
lemma out_ne_lit {N : ℕ} {F : (Fin N → Bool) → Bool} {gs : List Gate} {o : ℕ}
    (hcl : CleanL N gs) (hev : ∀ x : Fin N → Bool, vl gs x o = F x) (y : Fin N)
    (hnc : ∀ b : Bool, ∃ x x' : Fin N → Bool,
      F (Function.update x y b) ≠ F (Function.update x' y b))
    (l : ℕ) (hl : IsLit N gs y l) : o ≠ l := by
  intro e
  subst e
  obtain ⟨x, x', hne⟩ := hnc false
  apply hne
  rw [← hev, ← hev]
  rcases hl with e | ⟨pn, e, hpn⟩
  · rw [e, vl_input _ _ _ y.isLt, vl_input _ _ _ y.isLt]
    simp
  · rw [e, vl_not gs hcl _ pn _ hpn (y : ℕ) rfl rfl, vl_not gs hcl _ pn _ hpn (y : ℕ) rfl rfl,
      vl_input _ _ _ y.isLt, vl_input _ _ _ y.isLt]
    simp
lemma win_core {N : ℕ} {F : (Fin N → Bool) → Bool} {D : Finset (Fin N)} {gs : List Gate}
    {o p : ℕ} {g : Gate} {y : Fin N} {l h : ℕ} (H : DeepHyp F D) (hcl : CleanL N gs)
    (hev : ∀ x : Fin N → Bool, vl gs x o = F x) (hO : OneReader D gs)
    (hF : Front D gs p g y l h) : ∀ x : Fin N → Bool, vl gs x h = fixBit g → F x = true := by
  obtain ⟨hp, hop, hin, hy, hl, hD⟩ := hF
  intro x hx
  cases hFx : F x with
  | true => rfl
  | false =>
  exfalso
  have hz : F (zeroOn D x) = false := by
    cases e : F (zeroOn D x) with
    | false => rfl
    | true => rw [H.mono x e] at hFx; cases hFx
  obtain ⟨x', hx'D, _, hF0, hF1⟩ := H.win y hy x hz
  have hagr : ∀ i, i ∉ D → x i = Function.update x' y true i := by
    intro i hi
    have hiy : i ≠ y := fun e => hi (e ▸ hy)
    rw [Function.update_of_ne hiy, hx'D i hi]
  have hagr' : ∀ i, i ∉ D → x i = x' i := fun i hi => (hx'D i hi).symm
  have hlmem : l ∈ g.inputs := by rcases hin with e | e <;> simp [e]
  have hhmem : h ∈ g.inputs := by rcases hin with e | e <;> simp [e]
  have hc1 : vl gs x' (N + p) = fixBit g :=
    vl_abs gs hcl x' p g hp hop h hhmem (by rw [← vl_dfree hD x x' hagr']; exact hx)
  have hc2 : vl gs (Function.update x' y true) (N + p) = fixBit g :=
    vl_abs gs hcl _ p g hp hop h hhmem (by rw [← vl_dfree hD x _ hagr]; exact hx)
  have hol : o ≠ l := out_ne_lit hcl hev y (H.nc y hy) l hl
  have hoy : o ≠ (y : ℕ) := out_ne_lit hcl hev y (H.nc y hy) y (Or.inl rfl)
  have key := agree_B gs hcl x' (Function.update x' y true) (fun j => j = (y : ℕ) ∨ j = l)
    (o + 1)
    (by
      intro j hj hB
      rw [vl_input _ _ _ hj, vl_input _ _ _ hj]
      have hne : (⟨j, hj⟩ : Fin N) ≠ y := fun e => hB (Or.inl (by rw [← e]))
      rw [Function.update_of_ne hne])
    (by
      intro q g' hq _ hBq hBa _
      obtain ⟨a, ha, hBa⟩ := hBa
      have hreads : Reads gs q a := ⟨g', hq, ha⟩
      have hqp : q = p := by
        rcases hl with el | ⟨pn, el, hpn⟩
        · have hay : a = (y : ℕ) := by
            rcases hBa with e | e
            · exact e
            · rw [e, el]
          exact hO.1 y hy q p (hay ▸ hreads) ⟨g, hp, el ▸ hlmem⟩
        · rcases hBa with e | e
          · exfalso
            have hq' := hO.1 y hy q pn (e ▸ hreads) ⟨_, hpn, by simp⟩
            apply hBq
            right
            rw [el, hq']
          · exact hO.2 y hy pn hpn q p (by rw [← el, ← e]; exact hreads)
              ⟨g, hp, el ▸ hlmem⟩
      rw [hqp, hc1, hc2])
    o (by omega) (by rintro (e | e) <;> contradiction)
  rw [hev, hev, hF0, hF1] at key
  cases key
lemma stmtWin : StmtWin := by
  intro n F D gs o p g y l h H L hO hF
  have core := win_core H L.hcl L.hev hO hF
  refine ⟨fun e x hx => core x (by simp [fixBit, e, hx]),
    fun e => ⟨fun x hx => core x (by simp [fixBit, e, hx]), ?_⟩⟩
  by_contra hge
  have hlt : h < n + 1 := by omega
  have h0 := core (fun _ => false) (by rw [vl_input _ _ _ hlt]; simp [fixBit, e])
  rw [H.zero] at h0
  cases h0
end PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn

namespace PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
open PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Readers
lemma vl_update_of_not_supp {N : ℕ} (gs : List Gate) (h : ℕ) (y : Fin N)
    (hy : y ∉ (suppsFrom gs (inputSupps N)).getD h ∅) (x : Fin N → Bool) (b : Bool) :
    vl gs (Function.update x y b) h = vl gs x h := by
  have A := agree_wiresFrom (Function.update x y b) x gs _ _ _
    (agree_inputs (Function.update x y b) x)
  refine A.2.2 h ?_
  intro i hi
  have hiy : i ≠ y := fun e => hy (e ▸ hi)
  exact Function.update_of_ne hiy b x
lemma stmtTwo : StmtExch → StmtWin → StmtTwo := by
  intro hEx hWin n F D gs o p g y l h hD L hOne hF hand hsec
  obtain ⟨hgp, _, hin, hyD, hlit, hfree⟩ := hF
  have hcl := L.hcl
  have hnc : ∃ x x' : Fin (n + 1) → Bool, F x ≠ F x' := by
    obtain ⟨x, x', hx⟩ := hD.nc y hyD false
    exact ⟨_, _, hx⟩
  obtain ⟨-, hW⟩ := hWin n F D gs o p g y l h hD L hOne ⟨hgp, Or.inl hand, hin, hyD, hlit, hfree⟩
  obtain ⟨hcov, hhN⟩ := hW hand
  have hT : ∀ T : Finset ℕ, (∀ t ∈ T, Reads gs t h ∨ ∃ (r : ℕ) (g : Gate), gs[r]? = some g ∧
      (g.op = GateOp.or ∨ g.op = GateOp.not) ∧ Reads gs r h ∧ Reads gs t (n + 1 + r)) →
      T.card ≤ 2 := by
    intro T hTm
    obtain ⟨gs', o', hc', he', hlen⟩ := hEx (n + 1) F gs o h T hcl L.hev hnc hcov hTm
    have := L.hmin gs' o' hc' he'
    omega
  have hpread : Reads gs p h := ⟨g, hgp, by rcases hin with e | e <;> rw [e] <;> simp⟩
  obtain ⟨r, hrp, hrr⟩ := hsec
  have hall : ∀ t, Reads gs t h → t = p ∨ t = r := by
    intro t ht
    by_contra hne
    push_neg at hne
    have := hT {p, r, t} (by
      intro u hu
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu
      rcases hu with rfl | rfl | rfl
      · exact Or.inl hpread
      · exact Or.inl hrr
      · exact Or.inl ht)
    rw [Finset.card_insert_of_notMem (by simp [hrp.symm, hne.1.symm]),
      Finset.card_insert_of_notMem (by simp [hne.2.symm]), Finset.card_singleton] at this
    omega
  obtain ⟨gr, hgr, hhr⟩ := hrr
  have hrlen : r < gs.length := (List.getElem?_eq_some_iff.1 hgr).1
  have hhlt : h < n + 1 + r := reads_lt hcl ⟨gr, hgr, hhr⟩
  rcases hcl r gr hgr with ⟨hnot, j, _, hjin⟩ | ⟨hop, j, k, _, _, hjk⟩
  ·
    exfalso
    have hj : j = h := by rw [hjin] at hhr; simp at hhr; exact hhr.symm
    rw [hj] at hjin
    by_cases ho : o = n + 1 + r
    ·
      have h0 : F (zeroOn D (fun _ => false)) = false := by
        have : zeroOn D (fun _ : Fin (n + 1) => false) = fun _ => false := by
          funext i; simp [zeroOn]
        rw [this]; exact hD.zero
      obtain ⟨x', _, hx'y, hFx', hFx''⟩ := hD.win y hyD _ h0
      have e1 := L.hev x'
      have e2 := L.hev (Function.update x' y true)
      rw [ho, vl_not gs hcl _ r gr hgr h hnot hjin] at e1 e2
      rw [vl_update_of_not_supp gs h y (hfree y hyD) x' true] at e2
      have : F x' = F (Function.update x' y true) := by rw [← e1, ← e2]
      rw [this, hFx''] at hFx'
      exact Bool.noConfusion hFx'
    · obtain ⟨t, hrt, htr⟩ := L.live hnc r hrlen ho
      have htp : t ≠ p := by
        rintro rfl
        obtain ⟨g2, hg2, hmem⟩ := htr
        have := gate_eq hgp hg2 rfl
        subst this
        have hm : n + 1 + r = l ∨ n + 1 + r = h := by
          rcases hin with e | e <;> rw [e] at hmem <;> simp at hmem <;> omega
        rcases hm with e | e
        · rcases hlit with e' | ⟨pn, e', hpn⟩
          · have := y.isLt; omega
          · have hrpn : r = pn := by omega
            subst hrpn
            have := gate_eq hgr hpn rfl
            rw [this] at hjin
            simp at hjin
            have := y.isLt; omega
        · omega
      have := hT {p, r, t} (by
        intro u hu
        simp only [Finset.mem_insert, Finset.mem_singleton] at hu
        rcases hu with rfl | rfl | rfl
        · exact Or.inl hpread
        · exact Or.inl ⟨gr, hgr, hhr⟩
        · exact Or.inr ⟨r, gr, hgr, Or.inr hnot, ⟨gr, hgr, hhr⟩, htr⟩)
      rw [Finset.card_insert_of_notMem (by simp [hrp.symm, htp.symm]),
        Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton] at this
      omega
  · rcases hop with hop | hop
    ·
      refine ⟨r, gr, (if j = h then k else j), hrp, hgr, hop, ?_, hall⟩
      rw [hjk] at hhr ⊢
      by_cases hjh : j = h
      · subst hjh; right; simp
      · left
        simp at hhr ⊢
        omega
    ·
      exfalso
      by_cases ho : o = n + 1 + r
      ·
        apply hnc.elim
        intro x hx
        obtain ⟨x', hxx'⟩ := hx
        have key : ∀ z : Fin (n + 1) → Bool, F z = true := by
          intro z
          cases hz : vl gs z h
          · exact hcov z hz
          · rw [← L.hev z, ho, vl_gate gs hcl z r gr hgr, hop, hjk]
            rw [hjk] at hhr
            simp at hhr
            rcases hhr with e | e <;> subst e <;> simp [GateOp.eval, hz]
        exact hxx' (by rw [key x, key x'])
      · obtain ⟨t, hrt, htr⟩ := L.live hnc r hrlen ho
        have htp : t ≠ p := by
          rintro rfl
          obtain ⟨g2, hg2, hmem⟩ := htr
          have := gate_eq hgp hg2 rfl
          subst this
          have hm : n + 1 + r = l ∨ n + 1 + r = h := by
            rcases hin with e | e <;> rw [e] at hmem <;> simp at hmem <;> omega
          rcases hm with e | e
          · rcases hlit with e' | ⟨pn, e', hpn⟩
            · have := y.isLt; omega
            · have hrpn : r = pn := by omega
              subst hrpn
              have := gate_eq hgr hpn rfl
              rw [this] at hop
              exact GateOp.noConfusion hop
          · omega
        have := hT {p, r, t} (by
          intro u hu
          simp only [Finset.mem_insert, Finset.mem_singleton] at hu
          rcases hu with rfl | rfl | rfl
          · exact Or.inl hpread
          · exact Or.inl ⟨gr, hgr, hhr⟩
          · exact Or.inr ⟨r, gr, hgr, Or.inl hop, ⟨gr, hgr, hhr⟩, htr⟩)
        rw [Finset.card_insert_of_notMem (by simp [hrp.symm, htp.symm]),
          Finset.card_insert_of_notMem (by simp; omega), Finset.card_singleton] at this
        omega
end PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn

namespace PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn
lemma ml_of_front (hFront : StmtFront) : StmtML :=
  stmtML stmtAnd (stmtExt stmtLift stmtXMove hFront stmtWin (stmtTwo stmtExch stmtWin))
lemma lb_of_front (hFront : StmtFront) : StmtLB := lb_of_ml (ml_of_front hFront)
end PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn

namespace PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Outside.L_meta_3457.SparseLower.Helpers
open PEqualNP.Outside.L_meta_3457.SparseLower.Helpers.Readers
lemma front_suppsFrom_prefix {m : ℕ} (gs : List Gate) :
    ∀ L : List (Finset (Fin m)), ∃ T, suppsFrom gs L = L ++ T := by
  induction gs with
  | nil => intro L; exact ⟨[], by simp [suppsFrom]⟩
  | cons g gs ih =>
    intro L
    obtain ⟨T, hT⟩ := ih (L ++ [gateSupp L g])
    exact ⟨[gateSupp L g] ++ T, by
      show suppsFrom gs (L ++ [gateSupp L g]) = _
      rw [hT, List.append_assoc]⟩
lemma front_supp_input {m : ℕ} (gs : List Gate) (i : ℕ) (hi : i < m) :
    (suppsFrom gs (inputSupps m)).getD i ∅ = {(⟨i, hi⟩ : Fin m)} := by
  obtain ⟨T, hT⟩ := front_suppsFrom_prefix gs (inputSupps m)
  rw [hT, List.getD_append _ _ _ _ (by simp [inputSupps]; exact hi)]
  simp [inputSupps, hi]
lemma front_supp_beyond {m : ℕ} (gs : List Gate) (w : ℕ) (hw : m + gs.length ≤ w) :
    (suppsFrom gs (inputSupps m)).getD w ∅ = ∅ :=
  List.getD_eq_default _ _ (by rw [length_suppsFrom]; simp [inputSupps]; omega)
lemma front_supp_gate {m : ℕ} (gs : List Gate) (hcl : CleanL m gs) (p : ℕ) (g : Gate)
    (hp : gs[p]? = some g) (i : Fin m) :
    i ∈ (suppsFrom gs (inputSupps m)).getD (m + p) ∅ ↔
      ∃ a ∈ g.inputs, i ∈ (suppsFrom gs (inputSupps m)).getD a ∅ := by
  have hlt := (hcl p g hp).lt
  obtain ⟨pre, post, rfl, rfl⟩ := split_at gs p g hp
  set L0 := suppsFrom pre (inputSupps m) with hL0
  have hl0 : L0.length = m + pre.length := by rw [hL0, length_suppsFrom]; simp [inputSupps]
  have e : suppsFrom (pre ++ g :: post) (inputSupps m)
      = suppsFrom post (L0 ++ [gateSupp L0 g]) := by
    rw [suppsFrom_append]; rfl
  obtain ⟨T, hT⟩ := front_suppsFrom_prefix post (L0 ++ [gateSupp L0 g])
  have full : ∀ j, j < m + pre.length →
      (suppsFrom (pre ++ g :: post) (inputSupps m)).getD j ∅ = L0.getD j ∅ := by
    intro j hj
    rw [e, hT, List.getD_append _ _ _ _ (by simp [hl0]; omega), getD_snoc_ne _ _ _ _ (by omega)]
  have top : (suppsFrom (pre ++ g :: post) (inputSupps m)).getD (m + pre.length) ∅
      = gateSupp L0 g := by
    rw [e, hT, List.getD_append _ _ _ _ (by simp [hl0]), ← hl0, getD_snoc_eq]
  rw [top, mem_gateSupp]
  constructor
  · rintro ⟨a, ha, hia⟩
    exact ⟨a, ha, by rw [full a (hlt a ha)]; exact hia⟩
  · rintro ⟨a, ha, hia⟩
    exact ⟨a, ha, by rw [← full a (hlt a ha)]; exact hia⟩
section SourceSection7
variable {n : ℕ} {F : (Fin (n + 1) → Bool) → Bool} {D : Finset (Fin (n + 1))} {gs : List Gate}
  {o : ℕ}
lemma front_nlit (DH : DeepHyp F D) {y : Fin (n + 1)} (hy : y ∈ D) (c : Bool) :
    ¬ ∀ u, F u = xor (u y) c := by
  intro h
  obtain ⟨x, x', hx⟩ := DH.nc y hy false
  apply hx
  rw [h, h]
  simp
lemma front_fnc (DH : DeepHyp F D) {y : Fin (n + 1)} (hy : y ∈ D) :
    ∃ x x' : Fin (n + 1) → Bool, F x ≠ F x' := by
  obtain ⟨x, x', hx⟩ := DH.nc y hy false
  exact ⟨_, _, hx⟩
lemma front_dep (DH : DeepHyp F D) (L : Least (n + 1) F gs o) {y : Fin (n + 1)} (hy : y ∈ D) :
    y ∈ (suppsFrom gs (inputSupps (n + 1))).getD o ∅ := by
  have hz : zeroOn D (fun _ : Fin (n + 1) => false) = fun _ => false := by
    funext i; simp [zeroOn]
  obtain ⟨x', -, -, hF0, hF1⟩ := DH.win y hy (fun _ => false) (by rw [hz]; exact DH.zero)
  by_contra hno
  have hag := (agree_wiresFrom (Function.update x' y true) x' gs _ _ _
    (agree_inputs _ _)).2.2 o (by
      intro k hk
      have : k ≠ y := fun e => hno (e ▸ hk)
      simp [Function.update_of_ne this])
  have e : F (Function.update x' y true) = F x' := by
    rw [← L.hev, ← L.hev]
    exact hag
  rw [hF0, hF1] at e
  cases e
lemma front_dlit (L : Least (n + 1) F gs o) (hfnc : ∃ x x' : Fin (n + 1) → Bool, F x ≠ F x')
    (p0 : ℕ) (hmin : ∀ r < p0, ∀ g, gs[r]? = some g → (g.op = GateOp.and ∨ g.op = GateOp.or) →
      ∀ i ∈ D, i ∉ (suppsFrom gs (inputSupps (n + 1))).getD (n + 1 + r) ∅) :
    ∀ w, w < n + 1 + p0 → (∃ i ∈ D, i ∈ (suppsFrom gs (inputSupps (n + 1))).getD w ∅) →
      ∃ y ∈ D, ∃ c : Bool, (∀ u, vl gs u w = xor (u y) c) ∧
        (w = y ∨ ∃ pn, pn < p0 ∧ w = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩) := by
  intro w
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    rintro hw ⟨i, hi, his⟩
    by_cases hwn : w < n + 1
    · rw [front_supp_input gs w hwn, Finset.mem_singleton] at his
      subst his
      exact ⟨⟨w, hwn⟩, hi, false, fun u => by rw [vl_input gs u w hwn]; simp, Or.inl rfl⟩
    · obtain ⟨r, rfl⟩ : ∃ r, w = n + 1 + r := ⟨w - (n + 1), by omega⟩
      cases hg : gs[r]? with
      | none =>
        have hlen : gs.length ≤ r := List.getElem?_eq_none_iff.1 hg
        rw [front_supp_beyond gs _ (by omega)] at his
        simp at his
      | some g =>
        have hrl : r < gs.length := (List.getElem?_eq_some_iff.1 hg).1
        rcases L.hcl r g hg with ⟨hop, j, hj, hin⟩ | ⟨hop, _⟩
        · obtain ⟨a, ha, hia⟩ := (front_supp_gate gs L.hcl r g hg i).1 his
          rw [hin, List.mem_singleton] at ha
          subst ha
          obtain ⟨y, hy, c, hv, hs⟩ := ih a (by omega) (by omega) ⟨i, hi, hia⟩
          rcases hs with e | ⟨pn, hpn, e, hgpn⟩
          · have hge : g = ⟨GateOp.not, [(y : ℕ)]⟩ := by
              cases g
              simp only at hop hin
              rw [hop, hin, e]
            refine ⟨y, hy, !c, fun u => ?_, Or.inr ⟨r, by omega, rfl, by rw [← hge]; exact hg⟩⟩
            rw [vl_not gs L.hcl u r g hg a hop hin, hv]
            cases u y <;> cases c <;> rfl
          · exfalso
            have hpl : pn < gs.length := (List.getElem?_eq_some_iff.1 hgpn).1
            refine L.no_alias hfnc r hrl y (by have := y.isLt; omega) (fun u => ?_)
            rw [vl_not gs L.hcl u r g hg a hop hin, e,
              vl_not gs L.hcl u pn _ hgpn (y : ℕ) rfl rfl, vl_input gs u y y.isLt]
            simp
        · exact absurd his (hmin r (by omega) g hg hop i hi)
lemma front_out (DH : DeepHyp F D) (L : Least (n + 1) F gs o) (p : ℕ) (g : Gate)
    (hg : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (l : ℕ)
    (hl : l ∈ g.inputs) {y : Fin (n + 1)} (hy : y ∈ D) (c : Bool)
    (hv : ∀ u, vl gs u l = xor (u y) c) : o ≠ n + 1 + p := by
  intro e
  obtain ⟨x, x', hx⟩ := DH.nc y hy (xor (fixBit g) c)
  have hc : ∀ z : Fin (n + 1) → Bool, F (Function.update z y (xor (fixBit g) c)) = fixBit g := by
    intro z
    rw [← L.hev, e]
    refine vl_abs gs L.hcl _ p g hg hop l hl ?_
    rw [hv]
    simp
  exact hx (by rw [hc, hc])
lemma front_two (DH : DeepHyp F D) (L : Least (n + 1) F gs o) (OR : OneReader D gs) (p : ℕ)
    (g : Gate) (hg : gs[p]? = some g) (hop : g.op = GateOp.and ∨ g.op = GateOp.or) (j k : ℕ)
    (hin : g.inputs = [j, k]) (hj : j < n + 1 + p) (hk : k < n + 1 + p)
    (yj : Fin (n + 1)) (hyj : yj ∈ D) (cj : Bool) (hvj : ∀ u, vl gs u j = xor (u yj) cj)
    (hsj : j = yj ∨ ∃ pn, pn < p ∧ j = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(yj : ℕ)]⟩)
    (yk : Fin (n + 1)) (hyk : yk ∈ D) (ck : Bool) (hvk : ∀ u, vl gs u k = xor (u yk) ck)
    (hsk : k = yk ∨ ∃ pn, pn < p ∧ k = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(yk : ℕ)]⟩) :
    False := by
  have hfnc := front_fnc DH hyj
  have htl : p < gs.length := (List.getElem?_eq_some_iff.1 hg).1
  have hRj : Reads gs p j := ⟨g, hg, by rw [hin]; simp⟩
  have hRk : Reads gs p k := ⟨g, hg, by rw [hin]; simp⟩
  have hopnd : ∀ (w : ℕ) (v : Fin (n + 1)), v ∈ D → Reads gs p w →
      (w = v ∨ ∃ pn, pn < p ∧ w = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(v : ℕ)]⟩) →
      ∀ p' a, (a = (v : ℕ) ∨ a = w) → Reads gs p' a → n + 1 + p' ≠ w → p' = p := by
    intro w v hv hw hs p' a ha hr hne
    rcases hs with e | ⟨r, _, er, hg'⟩
    · have ha' : a = v := by
        rcases ha with ha | ha
        · exact ha
        · rw [ha, e]
      rw [ha'] at hr
      exact OR.1 v hv p' p hr (by rw [← e]; exact hw)
    · have hrv : Reads gs r v := ⟨_, hg', by simp⟩
      rcases ha with ha | ha
      · rw [ha] at hr
        have := OR.1 v hv p' r hr hrv
        exact (hne (by rw [this, er])).elim
      · rw [ha, er] at hr
        rw [er] at hw
        exact OR.2 v hv r hg' p' p hr hw
  have hvjk : yj ≠ yk := by
    intro e
    have hjk : j ≠ k := by
      intro e'
      subst e'
      exact L.no_alias hfnc p htl j hj (fun u => by
        rw [vl_gate gs L.hcl u p g hg, hin]
        rcases hop with h | h <;> rw [h] <;> simp [GateOp.eval])
    rcases hsj with ej | ⟨r1, hr1, ej, hg1⟩ <;> rcases hsk with ek | ⟨r2, hr2, ek, hg2⟩
    · exact hjk (by rw [ej, ek, e])
    · have := OR.1 yj hyj p r2 (by rw [← ej]; exact hRj) ⟨_, hg2, by rw [← e]; simp⟩
      omega
    · have := OR.1 yk hyk p r1 (by rw [← ek]; exact hRk) ⟨_, hg1, by rw [e]; simp⟩
      omega
    · have := OR.1 yj hyj r1 r2 ⟨_, hg1, by simp⟩ ⟨_, hg2, by rw [← e]; simp⟩
      exact hjk (by rw [ej, ek, this])
  have KC : ∀ u u' : Fin (n + 1) → Bool, (∀ i, i ≠ yj → i ≠ yk → u i = u' i) →
      vl gs u (n + 1 + p) = vl gs u' (n + 1 + p) → F u = F u' := by
    intro u u' hagr hgv
    rw [← L.hev, ← L.hev]
    refine agree_B gs L.hcl u u' (fun a => a = (yj : ℕ) ∨ a = (yk : ℕ) ∨ a = j ∨ a = k) (o + 1)
      ?_ ?_ o (by omega) ?_
    · intro a ha hBa
      have hBa' : ¬ (a = (yj : ℕ) ∨ a = (yk : ℕ) ∨ a = j ∨ a = k) := hBa
      rw [vl_input gs u a ha, vl_input gs u' a ha]
      apply hagr
      · intro e
        exact hBa' (Or.inl (congrArg Fin.val e))
      · intro e
        exact hBa' (Or.inr (Or.inl (congrArg Fin.val e)))
    · intro p' g' hp' _ hB' hr _
      have hB'' : ¬ (n + 1 + p' = (yj : ℕ) ∨ n + 1 + p' = (yk : ℕ) ∨ n + 1 + p' = j ∨
          n + 1 + p' = k) := hB'
      obtain ⟨a, ha, hBa⟩ := hr
      have hBa' : a = (yj : ℕ) ∨ a = (yk : ℕ) ∨ a = j ∨ a = k := hBa
      have hR : Reads gs p' a := ⟨g', hp', ha⟩
      have hpt : p' = p := by
        rcases hBa' with e | e | e | e
        · exact hopnd j yj hyj hRj hsj p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k yk hyk hRk hsk p' a (Or.inl e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
        · exact hopnd j yj hyj hRj hsj p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inl e'))))
        · exact hopnd k yk hyk hRk hsk p' a (Or.inr e) hR
            (fun e' => hB'' (Or.inr (Or.inr (Or.inr e'))))
      rw [hpt]
      exact hgv
    · intro hB
      have hB' : o = (yj : ℕ) ∨ o = (yk : ℕ) ∨ o = j ∨ o = k := hB
      rcases hB' with e | e | e | e
      · exact front_nlit DH hyj false (fun x => by
          rw [← L.hev, e, vl_input gs x yj yj.isLt]; simp)
      · exact front_nlit DH hyk false (fun x => by
          rw [← L.hev, e, vl_input gs x yk yk.isLt]; simp)
      · exact front_nlit DH hyj cj (fun x => by rw [← L.hev, e, hvj])
      · exact front_nlit DH hyk ck (fun x => by rw [← L.hev, e, hvk])
  have hag : ∀ (x : Fin (n + 1) → Bool) (a b a' b' : Bool), ∀ i, i ≠ yj → i ≠ yk →
      set2 x yj a yk b i = set2 x yj a' yk b' i := by
    intro x a b a' b' i e1 e2
    rw [set2_o x yj yk a b i e1 e2, set2_o x yj yk a' b' i e1 e2]
  have hval : ∀ (x : Fin (n + 1) → Bool) (a b : Bool),
      vl gs (set2 x yj a yk b) (n + 1 + p) = g.op.eval [xor a cj, xor b ck] := by
    intro x a b
    rw [vl_gate gs L.hcl _ p g hg, hin]
    simp only [List.map_cons, List.map_nil]
    rw [hvj, hvk, set2_p x hvjk, set2_q x]
  apply DH.nf yj hyj yk hyk hvjk
  rcases hop with hop | hop
  · refine ⟨!cj, !ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl
  · refine ⟨cj, ck, fun x => ⟨KC _ _ (hag x _ _ _ _) ?_, KC _ _ (hag x _ _ _ _) ?_⟩⟩ <;>
      rw [hval, hval, hop] <;> cases cj <;> cases ck <;> rfl
end SourceSection7
lemma stmtFront : StmtFront := by
  intro n F D gs o DH hD L OR
  classical
  obtain ⟨y0, hy0⟩ := hD
  have hfnc := front_fnc DH hy0
  by_cases hex : ∃ p g, gs[p]? = some g ∧ (g.op = GateOp.and ∨ g.op = GateOp.or) ∧
      ∃ i ∈ D, i ∈ (suppsFrom gs (inputSupps (n + 1))).getD (n + 1 + p) ∅
  · obtain ⟨g, hg, hop, i, hi, his⟩ := Nat.find_spec hex
    set p := Nat.find hex with hpdef
    have hmin : ∀ r < p, ∀ g', gs[r]? = some g' → (g'.op = GateOp.and ∨ g'.op = GateOp.or) →
        ∀ i ∈ D, i ∉ (suppsFrom gs (inputSupps (n + 1))).getD (n + 1 + r) ∅ :=
      fun r hr g' hg' hop' i hi his => Nat.find_min hex hr ⟨g', hg', hop', i, hi, his⟩
    rcases L.hcl p g hg with ⟨hop2, _⟩ | ⟨_, j, k, hj, hk, hin⟩
    · rcases hop with h | h <;> rw [h] at hop2 <;> cases hop2
    obtain ⟨a, ha, hia⟩ := (front_supp_gate gs L.hcl p g hg i).1 his
    rw [hin] at ha
    have hlitof : ∀ (w : ℕ) (y : Fin (n + 1)),
        (w = y ∨ ∃ pn, pn < p ∧ w = n + 1 + pn ∧ gs[pn]? = some ⟨GateOp.not, [(y : ℕ)]⟩) →
        IsLit (n + 1) gs y w := by
      rintro w y (e | ⟨pn, _, e, hpn⟩)
      · exact Or.inl e
      · exact Or.inr ⟨pn, e, hpn⟩
    by_cases mj : ∃ i ∈ D, i ∈ (suppsFrom gs (inputSupps (n + 1))).getD j ∅ <;>
      by_cases mk : ∃ i ∈ D, i ∈ (suppsFrom gs (inputSupps (n + 1))).getD k ∅
    · exfalso
      obtain ⟨yj, hyj, cj, hvj, hsj⟩ := front_dlit L hfnc p hmin j hj mj
      obtain ⟨yk, hyk, ck, hvk, hsk⟩ := front_dlit L hfnc p hmin k hk mk
      exact front_two DH L OR p g hg hop j k hin hj hk yj hyj cj hvj hsj yk hyk ck hvk hsk
    · obtain ⟨y, hy, c, hv, hs⟩ := front_dlit L hfnc p hmin j hj mj
      refine ⟨p, g, y, j, k, ⟨hg, hop, Or.inl hin, hy, hlitof j y hs,
        fun y' hy' hm => mk ⟨y', hy', hm⟩⟩,
        front_out DH L p g hg hop j (by rw [hin]; simp) hy c hv⟩
    · obtain ⟨y, hy, c, hv, hs⟩ := front_dlit L hfnc p hmin k hk mk
      refine ⟨p, g, y, k, j, ⟨hg, hop, Or.inr hin, hy, hlitof k y hs,
        fun y' hy' hm => mj ⟨y', hy', hm⟩⟩,
        front_out DH L p g hg hop k (by rw [hin]; simp) hy c hv⟩
    · exfalso
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl
      · exact mj ⟨i, hi, hia⟩
      · exact mk ⟨i, hi, hia⟩
  · exfalso
    have hmin : ∀ r < gs.length, ∀ g', gs[r]? = some g' →
        (g'.op = GateOp.and ∨ g'.op = GateOp.or) →
        ∀ i ∈ D, i ∉ (suppsFrom gs (inputSupps (n + 1))).getD (n + 1 + r) ∅ :=
      fun r _ g' hg' hop' i hi his => hex ⟨r, g', hg', hop', i, hi, his⟩
    by_cases hol : o < n + 1 + gs.length
    · obtain ⟨y, hy, c, hv, _⟩ := front_dlit L hfnc gs.length hmin o hol
        ⟨y0, hy0, front_dep DH L hy0⟩
      exact front_nlit DH hy c (fun u => by rw [← L.hev, hv])
    · obtain ⟨x, x', hxx⟩ := hfnc
      apply hxx
      rw [← L.hev, ← L.hev, vl_beyond gs x o (by omega), vl_beyond gs x' o (by omega)]
end PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn

namespace PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn
lemma stmtML_final : StmtML := ml_of_front stmtFront
lemma stmtLB_final : StmtLB := lb_of_front stmtFront
end PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn

namespace PEqualNP.Outside.L_meta_3457.SparseLower
lemma lower : ∀ (n k s : ℕ) (G : SimpleGraph (Fin n)) (A : Finset (Fin n)), (∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length) → (∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard → 3 ≤ (G.neighborSet v).ncard → ∀ p : G.Walk u v, 7 ≤ p.length) → (∀ i j : Fin n, G.Adj i j → i ∉ A) → (A.Nonempty ∨ ∃ i j : Fin n, G.Adj i j) → (∀ T : Finset (Fin n), (∀ i j : Fin n, G.Adj i j → i ∈ T ∨ j ∈ T) → k ≤ T.card) → PEqualNP.MetaComplexity.HasCircuitSize n (fun x : Fin n → Bool => @decide ((∃ a ∈ A, x a = true) ∨ ∃ i j : Fin n, G.Adj i j ∧ x i = true ∧ x j = true) (Classical.propDecidable _)) s → A.card + G.edgeSet.ncard + k ≤ s + 1 :=
  PEqualNP.Outside.L_meta_3457.SparseLower.EdgeFn.stmtLB_final
end PEqualNP.Outside.L_meta_3457.SparseLower

namespace PEqualNP.Outside.L_meta_3457.SparseCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma minimumCover (n : ℕ) (G : SimpleGraph (Fin n)) :
    ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧
      ∀ T : Finset (Fin n), CoverPromise.IsVertexCover G T → S.card ≤ T.card := by
  classical
  have hex : ∃ t : ℕ, ∃ S : Finset (Fin n), CoverPromise.IsVertexCover G S ∧ S.card = t := by
    refine ⟨(Finset.univ : Finset (Fin n)).card, Finset.univ, ?_, rfl⟩
    intro u v _
    exact Or.inl (Finset.mem_univ u)
  obtain ⟨S, hS, hcard⟩ := Nat.find_spec hex
  refine ⟨S, hS, ?_⟩
  intro T hT
  rw [hcard]
  exact Nat.find_min' hex ⟨T, hT, rfl⟩

lemma sparse_graph (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (hcyc : ∀ (v : Fin n) (c : G.Walk v v), c.IsCycle → 7 ≤ c.length)
    (hdist : ∀ u v : Fin n, u ≠ v → 3 ≤ (G.neighborSet u).ncard →
      3 ≤ (G.neighborSet v).ncard → ∀ p : G.Walk u v, 7 ≤ p.length)
    (hmono : Monotone2 C) (hfun : circuitFun n C = NestedCover.graphFun G ∅) :
    ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack n D ∧ D.size ≤ C.size ∧
      circuitFun n D = NestedCover.graphFun G ∅ ∧
      ∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        ∀ x : Fin n → Bool, (D.wires (List.ofFn x)).getD (n + j) false = true →
          ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true := by
  classical
  obtain ⟨S, hS, hmin⟩ := minimumCover n G
  have hbound : G.edgeSet.ncard + S.card ≤ C.size + 1 := by
    by_cases hE : ∃ u v : Fin n, G.Adj u v
    · have hsize : PEqualNP.MetaComplexity.HasCircuitSize n
          (fun x : Fin n → Bool => @decide ((∃ a ∈ (∅ : Finset (Fin n)), x a = true) ∨
            ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true) (Classical.propDecidable _)) C.size := by
        refine ⟨C, ?_, le_rfl, ?_⟩
        · intro g hg
          obtain ⟨hop, harity⟩ := hmono g hg
          refine ⟨?_, harity⟩
          rcases hop with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · intro x
          change circuitFun n C x = _
          rw [hfun]
          simp [NestedCover.graphFun]
      have h := PEqualNP.Outside.L_meta_3457.SparseLower.lower n S.card C.size G ∅ hcyc hdist
        (fun _ _ _ => Finset.notMem_empty _) (Or.inr hE) hmin hsize
      simpa only [Finset.card_empty, zero_add] using h
    · have hS0 : S.card ≤ (∅ : Finset (Fin n)).card := by
        refine hmin ∅ ?_
        intro u v huv
        exact False.elim (hE ⟨u, v, huv⟩)
      have he : G.edgeSet = ∅ := by
        ext e
        refine e.ind ?_
        intro u v
        simp only [SimpleGraph.mem_edgeSet, Set.mem_empty_iff_false, iff_false]
        intro huv
        exact hE ⟨u, v, huv⟩
      rw [he, Set.ncard_empty]
      simp only [Finset.card_empty] at hS0
      omega
  obtain ⟨D, hD, hback, hDf, hsize, hclean⟩ :=
    PEqualNP.Outside.L_meta_3457.StarCover.main n G S hS
  refine ⟨D, hD, hback, ?_, hDf, hclean⟩
  omega

lemma sparse_incidence (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : Circuit)
    (hcyc : ∀ (v : Fin (N + N)) (c : (PEqualNP.Outside.L_meta_3457.StarCover.incidenceGraph N I).Walk v v),
      c.IsCycle → 7 ≤ c.length)
    (hdist : ∀ u v : Fin (N + N), u ≠ v →
      3 ≤ ((PEqualNP.Outside.L_meta_3457.StarCover.incidenceGraph N I).neighborSet u).ncard →
      3 ≤ ((PEqualNP.Outside.L_meta_3457.StarCover.incidenceGraph N I).neighborSet v).ncard →
      ∀ p : (PEqualNP.Outside.L_meta_3457.StarCover.incidenceGraph N I).Walk u v, 7 ≤ p.length)
    (hmono : Monotone2 C)
    (hfun : ∀ z : Fin (N + N) → Bool, circuitFun (N + N) C z = true ↔
      ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) :
    ∃ D : Circuit, Monotone2 D ∧ NestedCover.ReadsBack (N + N) D ∧ D.size ≤ C.size ∧
      (∀ z : Fin (N + N) → Bool, circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        ∀ p l : Fin N, ¬ I p l →
          (D.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.castAdd N p ∨ k = Fin.natAdd N l)))).getD (N + N + j) false = false) ∧
      (∀ j < D.gates.length, (NestedCover.gateAt D j).op = GateOp.and →
        (∀ p : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
        ∀ l : Fin N, (D.wires (List.ofFn (fun k : Fin (N + N) => decide (k = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  classical
  let G := PEqualNP.Outside.L_meta_3457.StarCover.incidenceGraph N I
  have hG : circuitFun (N + N) C = NestedCover.graphFun G ∅ := by
    funext z
    apply Bool.eq_iff_iff.mpr
    exact (hfun z).trans (PEqualNP.Outside.L_meta_3457.StarCover.incidence_graphFun N I z).symm
  obtain ⟨D, hD, hback, hsize, hDf, hclean⟩ := sparse_graph (N + N) G C hcyc hdist hmono hG
  refine ⟨D, hD, hback, hsize, ?_, ?_, ?_⟩
  · intro z
    rw [hDf]
    exact PEqualNP.Outside.L_meta_3457.StarCover.incidence_graphFun N I z
  · intro j hj hand p l hI
    exact PEqualNP.Outside.L_meta_3457.StarCover.clean_off_pair G D hclean j hj hand
      (Fin.castAdd N p) (Fin.natAdd N l)
      (fun h => hI ((PEqualNP.Outside.L_meta_3457.StarCover.incidenceGraph_left_right N I p l).1 h))
  · intro j hj hand
    constructor
    · intro p
      exact PEqualNP.Outside.L_meta_3457.StarCover.clean_off_unit G D hclean j hj hand (Fin.castAdd N p)
    · intro l
      exact PEqualNP.Outside.L_meta_3457.StarCover.clean_off_unit G D hclean j hj hand (Fin.natAdd N l)

end PEqualNP.Outside.L_meta_3457.SparseCase
