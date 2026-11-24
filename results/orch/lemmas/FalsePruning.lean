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
