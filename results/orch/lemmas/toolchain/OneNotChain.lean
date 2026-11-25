import Mathlib.Tactic
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1890_aux.OneNotChain

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl step x := rfl

theorem fold_prefix (gs : List Gate) : ∀ w : List Bool,
    ∃ t : List Bool, gs.foldl step w = w ++ t ∧ t.length = gs.length := by
  induction gs with
  | nil => intro w; exact ⟨[], by simp, rfl⟩
  | cons g gs ih =>
    intro w
    obtain ⟨t, ht, hl⟩ := ih (step w g)
    refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false) :: t, ?_, by simp [hl]⟩
    rw [List.foldl_cons, ht]; simp [step]

theorem fold_length (gs : List Gate) (w : List Bool) :
    (gs.foldl step w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := fold_prefix gs w
  rw [ht]; simp [hl]

def LeL (a b : List Bool) : Prop := ∀ i, a.getD i false = true → b.getD i false = true

theorem eval_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) (l : List ℕ)
    (f f' : ℕ → Bool) (h : ∀ i, f i = true → f' i = true) :
    op.eval (l.map f) = true → op.eval (l.map f') = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_eq_true, List.mem_map, id]
    intro H x hx
    obtain ⟨i, hi, rfl⟩ := hx
    exact h i (H (f i) ⟨i, hi, rfl⟩)
  · simp only [GateOp.eval, List.any_eq_true, List.mem_map, id]
    rintro ⟨x, ⟨i, hi, rfl⟩, hx⟩
    exact ⟨f' i, ⟨i, hi, rfl⟩, h i hx⟩

theorem fold_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or) :
    ∀ a b : List Bool, a.length = b.length → LeL a b →
      LeL (gs.foldl step a) (gs.foldl step b) := by
  induction gs with
  | nil => intro a b _ h; exact h
  | cons g gs ih =>
    intro a b hl h
    rw [List.foldl_cons, List.foldl_cons]
    apply ih (fun g' hg' => hgs g' (List.mem_cons_of_mem _ hg'))
    · simp [step, hl]
    · intro i hi
      unfold step at hi ⊢
      by_cases hia : i < a.length
      · rw [List.getD_append _ _ _ _ hia] at hi
        rw [List.getD_append _ _ _ _ (by omega)]
        exact h i hi
      · rw [List.getD_append_right _ _ _ _ (by omega)] at hi
        rw [List.getD_append_right _ _ _ _ (by omega)]
        rw [← hl]
        by_cases he : i - a.length = 0
        · rw [he] at hi ⊢
          simp only [List.getD_cons_zero] at hi ⊢
          exact eval_mono g.op (hgs g List.mem_cons_self) _ _ _ (fun k => h k) hi
        · obtain ⟨m, hm⟩ : ∃ m, i - a.length = m + 1 := ⟨i - a.length - 1, by omega⟩
          rw [hm] at hi; simp at hi

def isNot (g : Gate) : Bool := match g.op with | .not => true | _ => false

theorem isNot_iff (g : Gate) : isNot g = true ↔ g.op = .not := by
  rcases g with ⟨op,ins⟩; cases op <;> simp [isNot]

theorem leInputs {n} (x y : Fin n → Bool) (h : ∀ i, x i = true → y i = true) :
    LeL (List.ofFn x) (List.ofFn y) := by
  intro i hi
  by_cases hlt : i < n
  · rw [List.getD_eq_getElem _ _ (by simpa using hlt),List.getElem_ofFn] at hi ⊢
    exact h ⟨i,hlt⟩ hi
  · rw [List.getD_eq_default _ _ (by simp; omega)] at hi
    contradiction

theorem leSnoc {a b : List Bool} (hl : a.length = b.length) (h : LeL a b)
    {u v : Bool} (hz : u = true → v = true) : LeL (a++[u]) (b++[v]) := by
  intro i hi
  by_cases lt : i < a.length
  · rw [List.getD_append _ _ _ _ lt] at hi
    rw [List.getD_append _ _ _ _ (by omega)]
    exact h i hi
  · rw [List.getD_append_right _ _ _ _ (by omega)] at hi ⊢
    rw [← hl]
    cases j : i-a.length with
    | zero => simp [j] at hi; simpa using hz hi
    | succ k => simp [j] at hi

theorem remove_only_not {α : Type*} (C : Circuit) (f : α → Bool)
    (e : α → List Bool) (z t : α)
    (hlen : ∀ x, (e x).length = (e z).length)
    (bounds : ∀ x, LeL (e z) (e x) ∧ LeL (e x) (e t))
    (hf : FanInTwo C) (hc : C.gates.countP isNot ≤ 1)
    (hzero : f z = false) (hone : f t = true)
    (hcomp : ∀ x, C.eval (e x) = !(f x)) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 ≤ C.size ∧
      ∀ x, D.eval (e x) = f x := by
  classical
  have endpoint0 : C.eval (e z) = true := by rw [hcomp,hzero]; rfl
  have endpoint1 : C.eval (e t) = false := by rw [hcomp,hone]; rfl
  have ao (g : Gate) (hg : g ∈ C.gates) (hn : g.op ≠ .not) :
      g.op = .and ∨ g.op = .or := by
    rcases (hf g hg).1 with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exact False.elim (hn h)
  by_cases hex : ∃ g ∈ C.gates, g.op = .not
  · obtain ⟨g,hg,hop⟩ := hex
    obtain ⟨pre,post,heq,_⟩ := List.eq_append_cons_of_mem hg
    have hgnot : isNot g = true := (isNot_iff g).mpr hop
    rw [heq,List.countP_append,List.countP_cons,hgnot] at hc
    simp only [↓reduceIte] at hc
    have hpre (q) (hq : q ∈ pre) : q.op = .and ∨ q.op = .or := by
      apply ao q (by simp [heq,hq])
      intro h; exact (List.countP_eq_zero.mp (show pre.countP isNot = 0 by omega) q hq)
        ((isNot_iff q).mpr h)
    have hpost (q) (hq : q ∈ post) : q.op = .and ∨ q.op = .or := by
      apply ao q (by simp [heq,hq])
      intro h; exact (List.countP_eq_zero.mp (show post.countP isNot = 0 by omega) q hq)
        ((isNot_iff q).mpr h)
    let P := fun x : α => pre.foldl step (e x)
    let r := g.inputs.headD ((e z).length+pre.length)
    let H := fun (x : α) (b : Bool) => (post.foldl step (P x ++ [b])).getD C.output false
    have hgate (x) : g.op.eval (g.inputs.map fun i => (P x).getD i false) =
        !((P x).getD r false) := by
      rw [hop]; dsimp only [r]
      cases e : g.inputs with
      | nil => rw [List.getD_eq_default _ _ (by simp [P,fold_length,hlen])]; rfl
      | cons i l => rfl
    have val (x) : C.eval (e x) = H x (!((P x).getD r false)) := by
      change (C.gates.foldl step (e x)).getD C.output false = _
      rw [heq,List.foldl_append,List.foldl_cons]
      change (post.foldl step (P x ++ [_])).getD C.output false = _
      rw [hgate]
    have mono (x y : α) (i j : Bool)
        (xy : LeL (e x) (e y)) (ij : i = true → j = true) :
        H x i = true → H y j = true := by
      have hl : (P x).length = (P y).length := by simp [P,fold_length,hlen]
      have hp : LeL (P x) (P y) := fold_mono pre hpre _ _
        ((hlen x).trans (hlen y).symm) xy
      exact fold_mono post hpost _ _ (by simp [hl]) (leSnoc hl hp ij) C.output
    rw [val] at endpoint0 endpoint1
    have proj (x : α) (b : Bool) : H x b = b := by
      cases b
      · cases hx : H x false with
        | false => rfl
        | true =>
          have h := mono x t false (!((P t).getD r false)) (bounds x).2 (by simp) hx
          rw [endpoint1] at h
          contradiction
      · exact mono z x _ true (bounds x).1 (by simp) endpoint0
    refine ⟨⟨pre,r⟩,fun q hq => ⟨hpre q hq, (hf q (by simp [heq,hq])).2⟩,?_,?_⟩
    · simp [Circuit.size,heq]
    · intro x
      have h := hcomp x
      rw [val,proj] at h
      change (P x).getD r false = f x
      simpa only [Bool.not_not] using congrArg Bool.not h
  · have hm (q) (hq : q ∈ C.gates) := ao q hq (fun h => hex ⟨q,hq,h⟩)
    have h := fold_mono C.gates hm (e z) (e t) ((hlen z).trans (hlen t).symm)
      (bounds z).2 C.output endpoint0
    change C.eval (e t) = true at h
    rw [endpoint1] at h
    contradiction

theorem leL_refl (a : List Bool) : LeL a a := fun _ h => h

theorem leL_trans {a b c : List Bool} (hab : LeL a b) (hbc : LeL b c) : LeL a c :=
  fun i h => hbc i (hab i h)

theorem no_four_chain (C : Circuit) (e : Fin 4 → List Bool)
    (hlen : ∀ i, (e i).length = (e 0).length)
    (h01 : LeL (e 0) (e 1)) (h12 : LeL (e 1) (e 2)) (h23 : LeL (e 2) (e 3))
    (hf : FanInTwo C) (hc : C.gates.countP (fun g => g.op.eval [false]) ≤ 1)
    (h0 : C.eval (e 0) = true) (h1 : C.eval (e 1) = false)
    (h2 : C.eval (e 2) = true) (h3 : C.eval (e 3) = false) : False := by
  have hpred : C.gates.countP (fun g => g.op.eval [false]) = C.gates.countP isNot := by
    apply List.countP_congr
    intro g hg
    have hallowed : g.op = .and ∨ g.op = .or ∨ g.op = .not := by
      simpa using (hf g hg).1
    rcases hallowed with hop | hop | hop <;> simp [isNot, hop, GateOp.eval]
  rw [hpred] at hc
  have bounds (i : Fin 4) : LeL (e 0) (e i) ∧ LeL (e i) (e 3) := by
    fin_cases i
    · exact ⟨leL_refl _, leL_trans h01 (leL_trans h12 h23)⟩
    · exact ⟨h01, leL_trans h12 h23⟩
    · exact ⟨leL_trans h01 h12, h23⟩
    · exact ⟨leL_trans h01 (leL_trans h12 h23), leL_refl _⟩
  obtain ⟨D, hD, _, heval⟩ := remove_only_not C (fun i => !(C.eval (e i))) e 0 3
    hlen bounds hf hc (by simp [h0]) (by simp [h3]) (by intro i; simp)
  have hd1 : D.eval (e 1) = true := by rw [heval, h1]; rfl
  have hd2 : D.eval (e 2) = false := by rw [heval, h2]; rfl
  have hmono := fold_mono D.gates (fun g hg => (hD g hg).1) (e 1) (e 2)
    ((hlen 1).trans (hlen 2).symm) h12 D.output hd1
  change D.eval (e 2) = true at hmono
  rw [hd2] at hmono
  contradiction

end PEqualNP.Outside.L_meta_1890_aux.OneNotChain
