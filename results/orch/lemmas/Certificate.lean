import PEqualNP.Outside.L_meta_1024

namespace PEqualNP.Outside.L_meta_1024_aux.FalsePruning

open PEqualNP.CircuitLowerBounds

abbrev Entry := ℕ × Finset (Fin 13)

def emptyEntry : Entry := (0, ∅)

def hit (S : Finset (Fin 13)) (x : Fin 13 → Bool) : Bool :=
  decide (∃ p ∈ S, x p = true)

lemma hit_empty (x : Fin 13 → Bool) : hit ∅ x = false := by simp [hit]

lemma hit_union (S T : Finset (Fin 13)) (x : Fin 13 → Bool) :
    hit (S ∪ T) x = (hit S x || hit T x) := by
  apply Bool.eq_iff_iff.mpr
  simp [hit, Finset.mem_union, or_and_right, exists_or]

def readEntry (es : List Entry) (i : ℕ) : Entry := es.getD i emptyEntry

def selected (e : ℕ → Entry) (ins : List ℕ) : List ℕ :=
  match ins with
  | [] => []
  | [a] => [a]
  | a :: b :: _ => if (e a).1 ≤ (e b).1 then [a] else [b]

def profile (e : ℕ → Entry) (g : Gate) : Entry :=
  match g.op with
  | GateOp.and => match g.inputs with
    | [] => (5, ∅)
    | [a] => e a
    | a :: b :: _ => if (e a).1 ≤ (e b).1 then e a else e b
  | _ =>
    (min 5 ((g.inputs.map fun i => (e i).1).sum),
      g.inputs.foldr (fun i S => (e i).2 ∪ S) ∅)

def rewritten (e : ℕ → Entry) (g : Gate) : Gate :=
  match g.op with
  | GateOp.and => match g.inputs with
    | [] => g
    | _ :: _ => ⟨GateOp.or, selected e g.inputs⟩
  | _ => g

lemma gate_spec (e : ℕ → Entry) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x : Fin 13 → Bool) (old new : ℕ → Bool)
    (hdom : ∀ i, old i = true → new i = true)
    (he : ∀ i, (e i).1 ≤ 4 → (e i).2.card ≤ (e i).1 ∧ new i = hit (e i).2 x) :
    ((rewritten e g).op = GateOp.and ∨ (rewritten e g).op = GateOp.or) ∧
    (rewritten e g).inputs.length ≤ 2 ∧
    (g.op.eval (g.inputs.map old) = true →
      (rewritten e g).op.eval ((rewritten e g).inputs.map new) = true) ∧
    ((profile e g).1 ≤ 4 →
      (profile e g).2.card ≤ (profile e g).1 ∧
      (rewritten e g).op.eval ((rewritten e g).inputs.map new) = hit (profile e g).2 x) := by
  rcases g with ⟨op, ins⟩
  rcases hg with ⟨hop, hlen⟩
  simp only at hop hlen ⊢
  rcases hop with rfl | rfl
  · match ins, hlen with
    | [], _ => simp [rewritten, profile, GateOp.eval]
    | [a], _ =>
      simpa [rewritten, selected, profile, GateOp.eval] using
        (show (GateOp.or = GateOp.and ∨ GateOp.or = GateOp.or) ∧
          1 ≤ 2 ∧ (old a = true → new a = true) ∧
          ((e a).1 ≤ 4 → (e a).2.card ≤ (e a).1 ∧ new a = hit (e a).2 x) from
          ⟨Or.inr rfl, by omega, hdom a, he a⟩)
    | [a, b], _ =>
      by_cases hab : (e a).1 ≤ (e b).1
      · simp only [rewritten, profile, selected, if_pos hab]
        refine ⟨by simp, by simp, ?_, ?_⟩
        · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
          intro hh
          have hboth : old a = true ∧ old b = true := by simpa using hh
          exact hdom a hboth.1
        · simpa [GateOp.eval] using he a
      · simp only [rewritten, profile, selected, if_neg hab]
        refine ⟨by simp, by simp, ?_, ?_⟩
        · simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons,
            List.all_nil, List.any_cons, List.any_nil, id_eq, Bool.and_true, Bool.or_false]
          intro hh
          have hboth : old a = true ∧ old b = true := by simpa using hh
          exact hdom b hboth.2
        · simpa [GateOp.eval] using he b
    | _ :: _ :: _ :: _, hh => simp at hh
  · match ins, hlen with
    | [], _ => simp [rewritten, profile, GateOp.eval, hit_empty]
    | [a], _ =>
      simp only [rewritten, profile,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        List.foldr_cons, List.foldr_nil, Finset.union_empty]
      refine ⟨by simp, by simp, ?_, ?_⟩
      · simpa [GateOp.eval] using hdom a
      · intro hc
        have ha : (e a).1 ≤ 4 := by omega
        have hm : min 5 (e a).1 = (e a).1 := Nat.min_eq_right (by omega)
        rw [hm]
        simpa [GateOp.eval] using he a ha
    | [a, b], _ =>
      simp only [rewritten, profile,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, Nat.add_zero,
        List.foldr_cons, List.foldr_nil, Finset.union_empty]
      refine ⟨by simp, by simp, ?_, ?_⟩
      · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
          List.any_nil, id_eq, Bool.or_false, Bool.or_eq_true]
        exact Or.imp (hdom a) (hdom b)
      · intro hc
        have hab : (e a).1 + (e b).1 ≤ 4 := by omega
        have ha := he a (by omega)
        have hb := he b (by omega)
        have hm : min 5 ((e a).1 + (e b).1) = (e a).1 + (e b).1 :=
          Nat.min_eq_right (by omega)
        refine ⟨?_, ?_⟩
        · rw [hm]
          exact (Finset.card_union_le _ _).trans (Nat.add_le_add ha.1 hb.1)
        · simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons,
            List.any_nil, id_eq, Bool.or_false, ha.2, hb.2, hit_union]
    | _ :: _ :: _ :: _, hh => simp at hh

structure State where
  entries : List Entry
  gates : List Gate

def initial : State := ⟨List.ofFn (fun p : Fin 13 => (1, {p})), []⟩

def step (s : State) (g : Gate) : State :=
  ⟨s.entries ++ [profile (readEntry s.entries) g],
    s.gates ++ [rewritten (readEntry s.entries) g]⟩

def build (gs : List Gate) : State := gs.foldl step initial

def cost (gs : List Gate) (o : ℕ) : ℕ := (readEntry (build gs).entries o).1

lemma read_append (es : List Entry) (e : Entry) (i : ℕ) :
    readEntry (es ++ [e]) i = if i = es.length then e else readEntry es i := by
  unfold readEntry
  rcases lt_trichotomy i es.length with h | h | h
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_left h]
  · rw [if_pos h]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_append_right (by omega)]
    simp [h]
  · rw [if_neg (by omega)]
    simp only [List.getD_eq_getElem?_getD]
    rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by omega)]

lemma build_snoc (gs : List Gate) (g : Gate) : build (gs ++ [g]) = step (build gs) g := by
  simp [build, List.foldl_append]

lemma build_lengths (gs : List Gate) :
    (build gs).entries.length = 13 + gs.length ∧ (build gs).gates.length = gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [build, initial]
  | append_singleton gs g ih =>
    rw [build_snoc]
    simp only [step, List.length_append, List.length_cons, List.length_nil]
    omega

lemma rewritten_allowed (e : ℕ → Entry) (g : Gate)
    (hg : (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ((rewritten e g).op = GateOp.and ∨ (rewritten e g).op = GateOp.or) ∧
      (rewritten e g).inputs.length ≤ 2 := by
  rcases g with ⟨op, ins⟩
  rcases hg with ⟨hop, hlen⟩
  simp only at hop hlen ⊢
  rcases hop with rfl | rfl
  · match ins, hlen with
    | [], _ => simp [rewritten]
    | [a], _ => simp [rewritten, selected]
    | [a,b], _ =>
      by_cases h : (e a).1 ≤ (e b).1 <;> simp [rewritten, selected, h]
    | _ :: _ :: _ :: _, hh => simp at hh
  · simpa [rewritten] using hlen

lemma build_allowed (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ g ∈ (build gs).gates,
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
  induction gs using List.reverseRecOn with
  | nil => simp [build, initial]
  | append_singleton gs g ih =>
    rw [build_snoc]
    intro a ha
    simp only [step, List.mem_append, List.mem_singleton] at ha
    rcases ha with ha | rfl
    · exact ih (fun b hb => hg b (by simp [hb])) a ha
    · exact rewritten_allowed _ g (hg g (by simp))

lemma wire_spec (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (x : Fin 13 → Bool) (i : ℕ) :
    (Global.val gs x i = true → Global.val (build gs).gates x i = true) ∧
    ((readEntry (build gs).entries i).1 ≤ 4 →
      (readEntry (build gs).entries i).2.card ≤ (readEntry (build gs).entries i).1 ∧
      Global.val (build gs).gates x i = hit (readEntry (build gs).entries i).2 x) := by
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    by_cases hi : i < 13
    · have hr : readEntry initial.entries i = (1, {⟨i, hi⟩}) := by
        simp only [readEntry, initial, List.getD_eq_getElem?_getD,
          List.getElem?_ofFn, hi, ↓reduceDIte, Option.getD_some]
      change (Global.val [] x i = true → Global.val [] x i = true) ∧ _
      simp only [build, List.foldl_nil, hr]
      simp [initial, Global.val_nil, hi, hit]
    · simp [build, initial, readEntry, emptyEntry, Global.val_nil, hit,
        Nat.le_of_not_lt hi, hi]
  | append_singleton gs g ih =>
    have hgs : ∀ a ∈ gs,
        (a.op = GateOp.and ∨ a.op = GateOp.or) ∧ a.inputs.length ≤ 2 := by
      intro a ha
      exact hg a (by simp [ha])
    have hi := ih hgs
    have hs := gate_spec (readEntry (build gs).entries) g (hg g (by simp)) x
      (Global.val gs x) (Global.val (build gs).gates x)
      (fun j => (hi j).1) (fun j => (hi j).2)
    simp only [build_snoc, step, read_append, Global.val_snoc,
      (build_lengths gs).1, (build_lengths gs).2]
    by_cases he : i = 13 + gs.length
    · simp only [if_pos he]
      exact ⟨hs.2.2.1, hs.2.2.2⟩
    · simp only [if_neg he]
      exact hi i

lemma support_eq_line (w : Fin 13) (f : (Fin 13 → Bool) → Bool)
    (hcorrect : ∀ x, Support.Band x → f x = Support.target w x)
    (S : Finset (Fin 13)) (hS : S.card ≤ 4)
    (hdom : ∀ x, f x = true → hit S x = true) : S = Support.line w := by
  classical
  have hsub : Support.line w ⊆ S := by
    intro p hp
    by_contra hn
    obtain ⟨T, hST, hT, hpT⟩ := Minterms.avoid_extension S p hn (by omega)
    have hb : Support.Band (Support.fromZeros T) := by
      right
      rw [Support.zeroSet_fromZeros, hT]
    have ht : Support.target w (Support.fromZeros T) = true := by
      simp only [Support.target, decide_eq_true_eq]
      exact ⟨p, hp, by simp [Support.fromZeros, hpT]⟩
    have hh := hdom (Support.fromZeros T) ((hcorrect _ hb).trans ht)
    simp only [hit, decide_eq_true_eq] at hh
    obtain ⟨q, hq, hxq⟩ := hh
    have hqT := hST hq
    simp [Support.fromZeros, hqT] at hxq
  apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
  rw [Clamp.line_card]
  exact hS

lemma low_cost_bound (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x)
    (hcost : ∀ w, cost gs (out w) ≤ 4) : 39 ≤ gs.length := by
  have hglob : ∀ (w : Fin 13) (x : Fin 13 → Bool),
      Circuit.eval ⟨(build gs).gates, out w⟩ (List.ofFn x) =
        decide (∃ p ∈ Global.line w, x p = true) := by
    intro w x
    let S := (readEntry (build gs).entries (out w)).2
    have hc : (readEntry (build gs).entries (out w)).1 ≤ 4 := hcost w
    have hw := wire_spec gs hg x (out w)
    have hcard : S.card ≤ 4 := (hw.2 hc).1.trans hc
    have hdom : ∀ y, Circuit.eval ⟨gs, out w⟩ (List.ofFn y) = true → hit S y = true := by
      intro y hy
      have hh := wire_spec gs hg y (out w)
      exact (hh.2 hc).2.symm.trans (hh.1 hy)
    have hline := support_eq_line w (fun y => Circuit.eval ⟨gs, out w⟩ (List.ofFn y))
      (hcorrect w) S hcard hdom
    change Global.val (build gs).gates x (out w) = Support.target w x
    rw [(hw.2 hc).2]
    change hit S x = Support.target w x
    rw [hline]
    rfl
  have hb := Global.global_bound (build gs).gates out (build_allowed gs hg) hglob
  simpa only [(build_lengths gs).2] using hb

lemma some_large_cost (gs : List Gate) (out : Fin 13 → ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hcorrect : ∀ (w : Fin 13) (x : Fin 13 → Bool), Support.Band x →
      Circuit.eval ⟨gs, out w⟩ (List.ofFn x) = Support.target w x)
    (hsmall : gs.length < 39) : ∃ w, 5 ≤ cost gs (out w) := by
  by_contra! hn
  have hc : ∀ w, cost gs (out w) ≤ 4 := fun w => by have h := hn w; omega
  have hb := low_cost_bound gs out hg hcorrect hc
  omega

end PEqualNP.Outside.L_meta_1024_aux.FalsePruning

namespace PEqualNP.Outside.L_meta_1024_aux.Certificate

open PEqualNP.CircuitLowerBounds
open FalsePruning

abbrev entry (gs : List Gate) (i : ℕ) : Entry := readEntry (build gs).entries i

lemma entry_snoc (gs : List Gate) (g : Gate) (i : ℕ) :
    entry (gs ++ [g]) i =
      if i = 13 + gs.length then profile (entry gs) g else entry gs i := by
  simp only [entry, build_snoc, FalsePruning.step, read_append, (build_lengths gs).1]

lemma entry_beyond (gs : List Gate) (i : ℕ) (hi : 13 + gs.length ≤ i) :
    entry gs i = emptyEntry := by
  unfold entry readEntry
  apply List.getD_eq_default
  simpa only [(build_lengths gs).1] using hi

lemma positive_valid (gs : List Gate) (i : ℕ) (hi : 0 < (entry gs i).1) :
    i < 13 + gs.length := by
  by_contra hn
  rw [entry_beyond gs i (by omega)] at hi
  simp [emptyEntry] at hi

lemma support_bound (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (i : ℕ) (hc : (entry gs i).1 ≤ 4) : (entry gs i).2.card ≤ (entry gs i).1 :=
  ((wire_spec gs hg (fun _ => false) i).2 hc).1

lemma certificate_false (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (i : ℕ) (hc : (entry gs i).1 ≤ 4) (x : Fin 13 → Bool)
    (hx : ∀ p ∈ (entry gs i).2, x p = false) : Global.val gs x i = false := by
  cases hv : Global.val gs x i
  · rfl
  · have hs := wire_spec gs hg x i
    have ht := (hs.2 hc).2.symm.trans (hs.1 hv)
    simp only [hit, decide_eq_true_eq] at ht
    obtain ⟨p, hp, hpt⟩ := ht
    rw [hx p hp] at hpt
    exact Bool.noConfusion hpt

def Cert (gs : List Gate) (i : ℕ) (Q : Finset ℕ) : Prop :=
  Q ⊆ Finset.Ico 13 (13 + gs.length) ∧
  ∀ q ∈ Q, q ≤ i ∧ (entry gs q).2 ⊆ (entry gs i).2 ∧ 2 ≤ (entry gs q).2.card ∧
    ∀ x : Fin 13 → Bool, Global.val gs x q = false →
      (∀ p ∈ (entry gs i).2 \ (entry gs q).2, x p = false) → Global.val gs x i = false

lemma cert_empty (gs : List Gate) (i : ℕ) : Cert gs i ∅ := by simp [Cert]

lemma cert_old (gs : List Gate) (g : Gate) (i : ℕ) (Q : Finset ℕ)
    (hQ : Cert gs i Q) (hi : i ≠ 13 + gs.length) : Cert (gs ++ [g]) i Q := by
  refine ⟨?_, ?_⟩
  · intro q hq
    have h := hQ.1 hq
    simp only [Finset.mem_Ico, List.length_append, List.length_cons, List.length_nil] at h ⊢
    omega
  · intro q hq
    have hqrange := hQ.1 hq
    have hqn : q ≠ 13 + gs.length := by simp only [Finset.mem_Ico] at hqrange; omega
    have hh := hQ.2 q hq
    simp only [entry_snoc, hi, hqn, ite_false, Global.val_snoc]
    exact hh

lemma cert_inherit (gs : List Gate) (g : Gate) (j : ℕ) (Q : Finset ℕ)
    (hQ : Cert gs j Q) (hj : j < 13 + gs.length)
    (hsub : (entry gs j).2 ⊆ (entry (gs ++ [g]) (13 + gs.length)).2)
    (hstep : ∀ x : Fin 13 → Bool, Global.val gs x j = false →
      (∀ p ∈ (entry (gs ++ [g]) (13 + gs.length)).2 \ (entry gs j).2, x p = false) →
      Global.val (gs ++ [g]) x (13 + gs.length) = false) :
    Cert (gs ++ [g]) (13 + gs.length) Q := by
  refine ⟨?_, ?_⟩
  · intro q hq
    have h := hQ.1 hq
    simp only [Finset.mem_Ico, List.length_append, List.length_cons, List.length_nil] at h ⊢
    omega
  · intro q hq
    obtain ⟨hqi, hqs, hqc, hctx⟩ := hQ.2 q hq
    have hqn : q ≠ 13 + gs.length := by omega
    have heq : entry (gs ++ [g]) q = entry gs q := by simp [entry_snoc, hqn]
    refine ⟨by omega, ?_, ?_, ?_⟩
    · simpa only [heq] using hqs.trans hsub
    · simpa only [heq] using hqc
    · intro x hx hzero
      have hxq : Global.val gs x q = false := by
        simpa only [Global.val_snoc, hqn, ite_false] using hx
      apply hstep x
      · apply hctx x hxq
        intro p hp
        apply hzero p
        rw [heq]
        exact Finset.mem_sdiff.mpr ⟨hsub (Finset.mem_sdiff.mp hp).1,
          (Finset.mem_sdiff.mp hp).2⟩
      · intro p hp
        apply hzero p
        rw [heq]
        obtain ⟨hpin, hpnot⟩ := Finset.mem_sdiff.mp hp
        exact Finset.mem_sdiff.mpr ⟨hpin, fun h => hpnot (hqs h)⟩

lemma cert_union (gs : List Gate) (i : ℕ) (A B : Finset ℕ)
    (hA : Cert gs i A) (hB : Cert gs i B) : Cert gs i (A ∪ B) := by
  refine ⟨Finset.union_subset hA.1 hB.1, ?_⟩
  intro q hq
  rcases Finset.mem_union.mp hq with hq | hq
  · exact hA.2 q hq
  · exact hB.2 q hq

lemma cert_insert (gs : List Gate) (g : Gate) (Q : Finset ℕ)
    (hQ : Cert (gs ++ [g]) (13 + gs.length) Q)
    (hc : 2 ≤ (entry (gs ++ [g]) (13 + gs.length)).2.card) :
    Cert (gs ++ [g]) (13 + gs.length) (insert (13 + gs.length) Q) := by
  refine ⟨?_, ?_⟩
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · simp only [Finset.mem_Ico, List.length_append, List.length_cons, List.length_nil]
      omega
    · exact hQ.1 hq
  · intro q hq
    rcases Finset.mem_insert.mp hq with rfl | hq
    · exact ⟨le_rfl, Finset.Subset.refl _, hc, fun x hx _ => hx⟩
    · exact hQ.2 q hq

lemma cert_disjoint (gs : List Gate) (a b : ℕ) (A B : Finset ℕ)
    (hA : Cert gs a A) (hB : Cert gs b B)
    (hd : Disjoint (entry gs a).2 (entry gs b).2) : Disjoint A B := by
  apply Finset.disjoint_left.mpr
  intro q hqa hqb
  have ha := hA.2 q hqa
  have hb := hB.2 q hqb
  obtain ⟨p, hp⟩ := Finset.card_pos.mp (show 0 < (entry gs q).2.card by omega)
  exact Finset.disjoint_left.mp hd (ha.2.1 hp) (hb.2.1 hp)

lemma and_false (g : Gate) (hop : g.op = GateOp.and) (f : ℕ → Bool)
    (j : ℕ) (hj : j ∈ g.inputs) (hf : f j = false) :
    g.op.eval (g.inputs.map f) = false := by
  cases hv : g.op.eval (g.inputs.map f)
  · rfl
  · simp only [hop, GateOp.eval, List.all_eq_true, id_eq] at hv
    have ht := hv (f j) (List.mem_map.mpr ⟨j, hj, rfl⟩)
    rw [hf] at ht
    exact Bool.noConfusion ht

lemma inherit_and (gs : List Gate) (g : Gate) (j : ℕ) (Q : Finset ℕ)
    (hop : g.op = GateOp.and) (hj : j ∈ g.inputs)
    (hQ : Cert gs j Q) (hvalid : j < 13 + gs.length)
    (he : entry (gs ++ [g]) (13 + gs.length) = entry gs j) :
    Cert (gs ++ [g]) (13 + gs.length) Q := by
  apply cert_inherit gs g j Q hQ hvalid
  · rw [he]
  · intro x hx _
    simp only [Global.val_snoc, ite_true]
    exact and_false g hop (Global.val gs x) j hj hx

lemma sharp_union (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (a b : ℕ) (hc : (entry gs a).1 + (entry gs b).1 ≤ 4)
    (hs : ((entry gs a).2 ∪ (entry gs b).2).card = (entry gs a).1 + (entry gs b).1) :
    (entry gs a).2.card = (entry gs a).1 ∧ (entry gs b).2.card = (entry gs b).1 ∧
      Disjoint (entry gs a).2 (entry gs b).2 := by
  have ha := support_bound gs hg a (by omega)
  have hb := support_bound gs hg b (by omega)
  have hu := Finset.card_union_le (entry gs a).2 (entry gs b).2
  have he := Finset.card_union_add_card_inter (entry gs a).2 (entry gs b).2
  refine ⟨by omega, by omega, ?_⟩
  apply Finset.disjoint_iff_inter_eq_empty.mpr
  apply Finset.card_eq_zero.mp
  omega

lemma inherit_or_left (gs : List Gate) (a b : ℕ) (Q : Finset ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hQ : Cert gs a Q) (ha : a < 13 + gs.length)
    (hb : (entry gs b).1 ≤ 4)
    (hd : Disjoint (entry gs a).2 (entry gs b).2) :
    Cert (gs ++ [⟨GateOp.or, [a,b]⟩]) (13 + gs.length) Q := by
  have he : (entry (gs ++ [⟨GateOp.or, [a,b]⟩]) (13 + gs.length)).2 =
      (entry gs a).2 ∪ (entry gs b).2 := by simp [entry_snoc, profile]
  apply cert_inherit gs _ a Q hQ ha
  · rw [he]
    exact Finset.subset_union_left
  · intro x hxa hzero
    have hxb : Global.val gs x b = false := by
      apply certificate_false gs hg b hb x
      intro p hp
      apply hzero p
      rw [he]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hp,
        fun h => Finset.disjoint_left.mp hd h hp⟩
    simp [Global.val_snoc, GateOp.eval, hxa, hxb]

lemma inherit_or_right (gs : List Gate) (a b : ℕ) (Q : Finset ℕ)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (hQ : Cert gs b Q) (hb : b < 13 + gs.length)
    (ha : (entry gs a).1 ≤ 4)
    (hd : Disjoint (entry gs a).2 (entry gs b).2) :
    Cert (gs ++ [⟨GateOp.or, [a,b]⟩]) (13 + gs.length) Q := by
  have he : (entry (gs ++ [⟨GateOp.or, [a,b]⟩]) (13 + gs.length)).2 =
      (entry gs a).2 ∪ (entry gs b).2 := by simp [entry_snoc, profile]
  apply cert_inherit gs _ b Q hQ hb
  · rw [he]
    exact Finset.subset_union_right
  · intro x hxb hzero
    have hxa : Global.val gs x a = false := by
      apply certificate_false gs hg a ha x
      intro p hp
      apply hzero p
      rw [he]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_left _ hp,
        fun h => Finset.disjoint_left.mp hd hp h⟩
    simp [Global.val_snoc, GateOp.eval, hxa, hxb]

lemma entry_nil (i : ℕ) : entry [] i =
    if h : i < 13 then (1, {⟨i,h⟩}) else emptyEntry := by
  by_cases hi : i < 13
  · simp only [entry, build, List.foldl_nil, readEntry, initial,
      List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi, dite_true, Option.getD_some]
  · simp [entry, build, initial, readEntry, emptyEntry, hi]

lemma extract (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (i : ℕ) (hc : (entry gs i).1 ≤ 4) (hs : (entry gs i).2.card = (entry gs i).1) :
    ∃ Q : Finset ℕ, (entry gs i).1 ≤ Q.card + 1 ∧ Cert gs i Q := by
  induction gs using List.reverseRecOn generalizing i with
  | nil =>
    refine ⟨∅, ?_, cert_empty _ _⟩
    by_cases hi : i < 13 <;> simp [entry_nil, hi, emptyEntry]
  | append_singleton gs g ih =>
    have hgs : ∀ a ∈ gs, (a.op = GateOp.and ∨ a.op = GateOp.or) ∧ a.inputs.length ≤ 2 := by
      intro a ha
      exact hg a (by simp [ha])
    by_cases hsmall : (entry (gs ++ [g]) i).1 ≤ 1
    · exact ⟨∅, by simpa using hsmall, cert_empty _ _⟩
    by_cases hi : i = 13 + gs.length
    · subst i
      have hgate := hg g (by simp)
      rcases g with ⟨op, ins⟩
      rcases hgate with ⟨hop, hlen⟩
      simp only at hop hlen
      rcases hop with rfl | rfl
      · have take_parent (j : ℕ) (hj : j ∈ ins)
            (he : entry (gs ++ [⟨GateOp.and, ins⟩]) (13 + gs.length) = entry gs j) :
            ∃ Q : Finset ℕ,
              (entry (gs ++ [⟨GateOp.and, ins⟩]) (13 + gs.length)).1 ≤ Q.card + 1 ∧
              Cert (gs ++ [⟨GateOp.and, ins⟩]) (13 + gs.length) Q := by
          have hcj : (entry gs j).1 ≤ 4 := he ▸ hc
          have hsj : (entry gs j).2.card = (entry gs j).1 := he ▸ hs
          obtain ⟨Q, hcount, hQ⟩ := ih hgs j hcj hsj
          have hjpos : 0 < (entry gs j).1 := by rw [he] at hsmall; omega
          exact ⟨Q, by simpa only [he] using hcount,
            inherit_and gs _ j Q rfl hj hQ (positive_valid gs j hjpos) he⟩
        rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
        · simp [entry_snoc, profile] at hc
        ·
          apply take_parent a (by simp)
          simp [entry_snoc, profile]
        ·
          by_cases hab : (entry gs a).1 ≤ (entry gs b).1
          · apply take_parent a (by simp)
            simp [entry_snoc, profile, hab]
          · apply take_parent b (by simp)
            simp [entry_snoc, profile, hab]
        · simp at hlen
      · rcases ins with _ | ⟨a, _ | ⟨b, _ | ⟨c, tl⟩⟩⟩
        · simp [entry_snoc, profile] at hsmall
        ·
          have he0 : entry (gs ++ [⟨GateOp.or, [a]⟩]) (13 + gs.length) =
              (min 5 (entry gs a).1, (entry gs a).2) := by simp [entry_snoc, profile]
          rw [he0] at hc hs hsmall
          have ha : (entry gs a).1 ≤ 4 := by omega
          have hm : min 5 (entry gs a).1 = (entry gs a).1 := Nat.min_eq_right (by omega)
          have he : entry (gs ++ [⟨GateOp.or, [a]⟩]) (13 + gs.length) = entry gs a := by
            rw [he0, hm]
          obtain ⟨Q, hcount, hQ⟩ := ih hgs a ha (by simpa only [hm] using hs)
          refine ⟨Q, by simpa only [he] using hcount, ?_⟩
          apply cert_inherit gs _ a Q hQ (positive_valid gs a (by omega))
          · rw [he]
          · intro x hx _
            simp [Global.val_snoc, GateOp.eval, hx]
        ·
          have he : entry (gs ++ [⟨GateOp.or, [a,b]⟩]) (13 + gs.length) =
              (min 5 ((entry gs a).1 + (entry gs b).1), (entry gs a).2 ∪ (entry gs b).2) := by
            simp [entry_snoc, profile]
          rw [he] at hc hs hsmall
          have hab : (entry gs a).1 + (entry gs b).1 ≤ 4 := by omega
          have hm : min 5 ((entry gs a).1 + (entry gs b).1) =
              (entry gs a).1 + (entry gs b).1 := Nat.min_eq_right (by omega)
          have hUnion : ((entry gs a).2 ∪ (entry gs b).2).card =
              (entry gs a).1 + (entry gs b).1 := by simpa only [hm] using hs
          obtain ⟨hsa, hsb, hd⟩ := sharp_union gs hgs a b hab hUnion
          obtain ⟨A, hca, hA⟩ := ih hgs a (by omega) hsa
          obtain ⟨B, hcb, hB⟩ := ih hgs b (by omega) hsb
          by_cases ha0 : (entry gs a).1 = 0
          · refine ⟨B, ?_, inherit_or_right gs a b B hgs hB
                (positive_valid gs b (by omega)) (by omega) hd⟩
            rw [he]
            change min 5 ((entry gs a).1 + (entry gs b).1) ≤ B.card + 1
            rw [hm, ha0, Nat.zero_add]
            exact hcb
          by_cases hb0 : (entry gs b).1 = 0
          · refine ⟨A, ?_, inherit_or_left gs a b A hgs hA
                (positive_valid gs a (by omega)) (by omega) hd⟩
            rw [he]
            change min 5 ((entry gs a).1 + (entry gs b).1) ≤ A.card + 1
            rw [hm, hb0, Nat.add_zero]
            exact hca
          have hIA := inherit_or_left gs a b A hgs hA
            (positive_valid gs a (by omega)) (by omega) hd
          have hIB := inherit_or_right gs a b B hgs hB
            (positive_valid gs b (by omega)) (by omega) hd
          have hdisj := cert_disjoint gs a b A B hA hB hd
          have hn : 13 + gs.length ∉ A ∪ B := by
            intro hh
            rcases Finset.mem_union.mp hh with hh | hh
            · have hr := hA.1 hh
              simp at hr
            · have hr := hB.1 hh
              simp at hr
          refine ⟨insert (13 + gs.length) (A ∪ B), ?_,
            cert_insert gs _ _ (cert_union _ _ _ _ hIA hIB) ?_⟩
          · rw [Finset.card_insert_of_notMem hn, Finset.card_union_of_disjoint hdisj, he]
            simp only [Prod.fst, hm]
            omega
          · rw [he]
            simp only [Prod.snd]
            rw [hUnion]
            omega
        · simp at hlen
    · have he : entry (gs ++ [g]) i = entry gs i := by simp [entry_snoc, hi]
      obtain ⟨Q, hcount, hQ⟩ := ih hgs i (he ▸ hc) (he ▸ hs)
      exact ⟨Q, by simpa only [he] using hcount, cert_old gs g i Q hQ hi⟩

lemma global_line_card (w : Fin 13) : (Global.line w).card = 4 := Clamp.line_card w

lemma line_profile (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) (o : ℕ)
    (hcorrect : ∀ x, Support.Band x → Global.val gs x o = Support.target w x)
    (hc : (entry gs o).1 ≤ 4) : (entry gs o).2 = Global.line w ∧ (entry gs o).1 = 4 := by
  have hcard := support_bound gs hg o hc
  have hline : (entry gs o).2 = Global.line w := by
    apply support_eq_line w (fun x => Global.val gs x o) hcorrect _ (hcard.trans hc)
    intro x hx
    have h := wire_spec gs hg x o
    exact (h.2 hc).2.symm.trans (h.1 hx)
  refine ⟨hline, ?_⟩
  rw [hline, global_line_card] at hcard
  omega

lemma three_contexts (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (w : Fin 13) (o : ℕ)
    (hcorrect : ∀ x, Support.Band x → Global.val gs x o = Support.target w x)
    (hc : (entry gs o).1 ≤ 4) :
    ∃ Q : Finset ℕ, 3 ≤ Q.card ∧ Q ⊆ Finset.Ico 13 (13 + gs.length) ∧
      ∀ q ∈ Q, ∃ C : Finset (Fin 13), C ⊆ Global.line w ∧ C.card ≤ 2 ∧
        ∀ x : Fin 13 → Bool, Global.val gs x q = false →
          (∀ p ∈ C, x p = false) → Global.val gs x o = false := by
  obtain ⟨hline, hcost⟩ := line_profile gs hg w o hcorrect hc
  have hsharp : (entry gs o).2.card = (entry gs o).1 := by rw [hline, hcost, global_line_card]
  obtain ⟨Q, hcount, hQ⟩ := extract gs hg o hc hsharp
  refine ⟨Q, by omega, hQ.1, ?_⟩
  intro q hq
  obtain ⟨hqo, hsub, hcard, hctx⟩ := hQ.2 q hq
  refine ⟨(entry gs o).2 \ (entry gs q).2, ?_, ?_, hctx⟩
  · rw [hline]
    exact Finset.sdiff_subset
  · rw [Finset.card_sdiff_of_subset hsub, hline, global_line_card]
    omega

end PEqualNP.Outside.L_meta_1024_aux.Certificate
