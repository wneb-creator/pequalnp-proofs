import Mathlib.Tactic
import PEqualNP.Defs


namespace PEqualNP.Outside.L_meta_1890_aux.OneNot

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

lemma seeded_input_bounds (p : Fin 10 → Fin 10) (x : Fin 10 → Bool) :
    LeL (List.ofFn ((fun _ => false) ∘ p) ++ [false && false])
      (List.ofFn (x ∘ p) ++ [x 0 && x 2]) ∧
    LeL (List.ofFn (x ∘ p) ++ [x 0 && x 2])
      (List.ofFn ((fun _ => true) ∘ p) ++ [true && true]) := by
  constructor
  · exact leSnoc (by simp) (leInputs _ _ (by simp)) (by simp)
  · exact leSnoc (by simp) (leInputs _ _ (by simp)) (by simp)

lemma seeded_complement_collapse (C : Circuit) (p : Fin 10 → Fin 10)
    (f : (Fin 10 → Bool) → Bool)
    (hf : FanInTwo C) (hc : C.gates.countP isNot ≤ 1)
    (hzero : f (fun _ => false) = false) (hone : f (fun _ => true) = true)
    (hcomp : ∀ x, C.eval (List.ofFn (x ∘ p) ++ [x 0 && x 2]) = !(f x)) :
    ∃ D : Circuit, Monotone2 D ∧ D.size + 1 ≤ C.size ∧
      ∀ x, D.eval (List.ofFn (x ∘ p) ++ [x 0 && x 2]) = f x := by
  exact remove_only_not C f
    (fun x => List.ofFn (x ∘ p) ++ [x 0 && x 2])
    (fun _ => false) (fun _ => true) (by intro x; simp)
    (seeded_input_bounds p) hf hc hzero hone hcomp

end PEqualNP.Outside.L_meta_1890_aux.OneNot


namespace PEqualNP.Outside.L_meta_1890_aux.SeedErase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edges : List (Fin 10 × Fin 10) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),
   (3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

def target (x : Fin 10 → Bool) : Bool :=
  edges.any fun e => x e.1 && x e.2

def onPair (e : Fin 10 × Fin 10) (i : Fin 10) : Bool :=
  decide (i = e.1 ∨ i = e.2)

lemma pair_target (e : Fin 10 × Fin 10) (he : e ∈ edges) :
    target (onPair e) = true := by
  apply List.any_eq_true.mpr
  exact ⟨e, he, by simp [onPair]⟩

lemma pair_seed : ∀ e ∈ edges, (onPair e 0 && onPair e 2) = false := by
  decide

lemma find_pair (x : Fin 10 → Bool) (h : target x = true) :
    ∃ e ∈ edges, ∀ i, onPair e i = true → x i = true := by
  obtain ⟨e, he, hv⟩ := List.any_eq_true.mp h
  simp only [Bool.and_eq_true] at hv
  refine ⟨e, he, ?_⟩
  intro i hi
  simp only [onPair, decide_eq_true_eq] at hi
  rcases hi with rfl | rfl
  · exact hv.1
  · exact hv.2

lemma erase_seed (H : (Fin 10 → Bool) → Bool → Bool)
    (mono : ∀ x y b c, (∀ i, x i = true → y i = true) →
      (b = true → c = true) → H x b = true → H y c = true)
    (correct : ∀ x, H x (x 0 && x 2) = target x) :
    ∀ x, H x false = target x := by
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    rw [← correct x]
    exact mono x x false (x 0 && x 2) (fun _ => id) (by simp) hx
  · intro hx
    obtain ⟨e, he, sub⟩ := find_pair x hx
    have hp : H (onPair e) false = true := by
      rw [← pair_seed e he, correct, pair_target e he]
    exact mono (onPair e) x false false sub (by simp) hp

lemma gate_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (l : List Nat) (f g : Nat → Bool)
    (h : ∀ i ∈ l, f i = true → g i = true) :
    op.eval (l.map f) = true → op.eval (l.map g) = true := by
  rcases hop with rfl | rfl
  · intro ht
    change (l.map f).all id = true at ht
    change (l.map g).all id = true
    rw [List.all_eq_true] at ht ⊢
    intro b hb
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact h i hi (ht _ (List.mem_map_of_mem hi))
  · intro ht
    change (l.map f).any id = true at ht
    change (l.map g).any id = true
    rw [List.any_eq_true] at ht ⊢
    obtain ⟨b, hb, ht⟩ := ht
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hb
    exact ⟨g i, List.mem_map_of_mem hi, h i hi ht⟩

lemma eval_mono (C : Circuit) (hc : Monotone2 C) (x y : List Bool)
    (len : x.length = y.length)
    (sub : ∀ i, x.getD i false = true → y.getD i false = true) :
    C.eval x = true → C.eval y = true := by
  have run (gs : List Gate) (legal : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
      (x y : List Bool) (len : x.length = y.length)
      (sub : ∀ i, x.getD i false = true → y.getD i false = true) :
      ∀ i, ((⟨gs,0⟩ : Circuit).wires x).getD i false = true →
        ((⟨gs,0⟩ : Circuit).wires y).getD i false = true := by
    induction gs generalizing x y with
    | nil => exact sub
    | cons g gs ih =>
      let a := g.op.eval (g.inputs.map fun i => x.getD i false)
      let b := g.op.eval (g.inputs.map fun i => y.getD i false)
      have ab : a = true → b = true :=
        gate_mono g.op (legal g List.mem_cons_self) g.inputs _ _ (fun i _ => sub i)
      change ∀ i, ((⟨gs,0⟩ : Circuit).wires (x ++ [a])).getD i false = true →
        ((⟨gs,0⟩ : Circuit).wires (y ++ [b])).getD i false = true
      apply ih (fun g hg => legal g (List.mem_cons_of_mem _ hg)) _ _ (by simp [len])
      intro i
      by_cases hi : i < x.length
      · rw [List.getD_append _ _ _ _ hi,
          List.getD_append _ _ _ _ (by omega)]
        exact sub i
      · rw [List.getD_append_right _ _ _ _ (by omega),
          List.getD_append_right _ _ _ _ (by omega), len]
        cases k : i - y.length with
        | zero => simpa using ab
        | succ j => simp
  exact run C.gates (fun g hg => by simpa using (hc g hg).1) x y len sub C.output

lemma circuit_erase_seed (C : Circuit) (hc : Monotone2 C) (p : Fin 10 → Fin 10)
    (correct : ∀ x : Fin 10 → Bool,
      C.eval (List.ofFn (x ∘ p) ++ [x 0 && x 2]) = target x) :
    ∀ x : Fin 10 → Bool, C.eval (List.ofFn (x ∘ p) ++ [false]) = target x := by
  apply erase_seed (fun x b => C.eval (List.ofFn (x ∘ p) ++ [b])) _ correct
  intro x y b c sub bc
  apply eval_mono C hc _ _ (by simp)
  intro i
  by_cases hi : i < 10
  · rw [List.getD_append _ _ _ _ (by simpa using hi),
      List.getD_append _ _ _ _ (by simpa using hi)]
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi,
      ↓reduceDIte, Option.getD_some, Function.comp_apply] using sub (p ⟨i,hi⟩)
  · rw [List.getD_append_right _ _ _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_ofFn]
    cases k : i - 10 with
    | zero => simpa using bc
    | succ j => simp

end PEqualNP.Outside.L_meta_1890_aux.SeedErase


namespace PEqualNP.Outside.L_meta_1890_aux.Restrict

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

lemma lLC {α:Type _} {a : α} {l:List α}:(a::l).length=l.length+1:=List.length_cons
lemma lLA {α:Type _} {l1 l2:List α}:(l1++l2).length=l1.length+l2.length:=List.length_append
lemma fUN {α:Type _} [DecidableEq α] {β : α->Sort _} {f:∀ a,β a} {a b : α} {v : β a} (h:b≠a):Function.update f a v b=f b:=Function.update_of_ne h v f
lemma fUS {α:Type _} [DecidableEq α] {β : α->Sort _} {f:∀ a,β a} {a : α} {v : β a}:Function.update f a v a=v:=Function.update_self a v f
lemma nAA (a b d:Nat):a+b+d=a+(b+d):=Nat.add_assoc a b d
lemma lMMp {α β γ:Type _} {g : β->γ} {f : α->β} {l:List α}:(l.map f).map g=l.map (g ∘ f):=List.map_map
lemma lGD {α:Type _} (l:List α) (d : α) {i:Nat} (h:l.length<=i):l.getD i d=d:=List.getD_eq_default l d h
def q3 (gs:List Gate) (w:List Bool):List Bool :=
 gs.foldl (fun w g => w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) w
lemma zd (gs gs':List Gate) (w:List Bool) :
   q3 (gs++gs') w=q3 gs' (q3 gs w):=by
 simp [q3,List.foldl_append]
lemma y1 (gs:List Gate):∀ w:List Bool,
   ∃ t:List Bool,q3 gs w=w++t/\t.length=gs.length:=by
 induction gs with
 | nil => intro w;exact ⟨[],by simp [q3],rfl⟩
 | cons g gs ih =>
   intro w
   obtain ⟨t,ht,hl⟩:=ih (w++[g.op.eval (g.inputs.map fun i => w.getD i false)])
   refine ⟨g.op.eval (g.inputs.map fun i => w.getD i false)::t,?_,by simp [hl]⟩
   have:q3 (g::gs) w
       = q3 gs (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]):=rfl
   rw [this,ht];simp
lemma qu (gs:List Gate) (w:List Bool) :
   (q3 gs w).length=w.length+gs.length:=by
 obtain ⟨t,ht,hl⟩:=y1 gs w
 rw [ht];simp [hl]
def Ok (g:Gate):Prop :=
 g.op ∈ ({GateOp.and,GateOp.or,GateOp.not}:Set GateOp)/\g.inputs.length<=2
lemma q8 {α:Type} (L:List α) (S d : α) (j : ℕ) (h:j≠L.length) :
   (L++[S]).getD j d=L.getD j d:=by
 by_cases hj:j < L.length
 . exact List.getD_append _ _ _ _ hj
 . rw [lGD _ _ (by simp;omega),lGD _ _ (by omega)]
lemma z0 {α:Type} (L:List α) (S d : α):(L++[S]).getD L.length d=S:=by
 simp
lemma z2 {α:Type} (L:List α) (S d : α) (k : ℕ) (h:L.length=k) :
   (L++[S]).getD k d=S:=by
 subst h;simp
def yb {n : ℕ} (L:List (Finset (Fin n))) (g:Gate):Finset (Fin n) :=
 (g.inputs.map fun a => L.getD a ∅).foldr (· ∪ ·) ∅
lemma q71 {n : ℕ} (l:List ℕ) (F : ℕ->Finset (Fin n)) (i:Fin n) :
   i ∈ (l.map F).foldr (· ∪ ·) ∅ ↔ ∃ a ∈ l,i ∈ F a:=by
 induction l with
 | nil => simp
 | cons b l ih => simp [ih]
lemma kf {n : ℕ} (L:List (Finset (Fin n))) (g:Gate) (i:Fin n) :
   i ∈ yb L g ↔ ∃ a ∈ g.inputs,i ∈ L.getD a ∅ :=
 q71 _ _ _
def zb {n : ℕ} (gs:List Gate) (L:List (Finset (Fin n))):List (Finset (Fin n)) :=
 gs.foldl (fun L g => L++[yb L g]) L
def qr (n : ℕ):List (Finset (Fin n)):=List.ofFn fun i:Fin n => {i}
def q207 {n : ℕ} (x y:Fin n->Bool) (L:List (Finset (Fin n))) (w w':List Bool):Prop :=
 L.length=w.length/\w.length=w'.length /\
   ∀ j : ℕ,(∀ i ∈ L.getD j ∅,x i=y i)->w.getD j false=w'.getD j false
lemma k6 {n : ℕ} (x y:Fin n->Bool) (gs:List Gate) :
   ∀ (L:List (Finset (Fin n))) (w w':List Bool),q207 x y L w w' ->
     q207 x y (zb gs L) (q3 gs w) (q3 gs w'):=by
 induction gs with
 | nil => intro L w w' h;exact h
 | cons g gs ih =>
   intro L w w' h
   obtain ⟨h1,h2,h3⟩:=h
   apply ih (L++[yb L g])
     (w++[g.op.eval (g.inputs.map fun i => w.getD i false)])
     (w'++[g.op.eval (g.inputs.map fun i => w'.getD i false)])
   refine ⟨by simp [h1],by simp [h2],?_⟩
   intro j hj
   by_cases hjl:j=L.length
   . subst hjl
     rw [z0] at hj
     rw [h1,z0,h2,z0]
     congr 1
     apply List.map_congr_left
     intro a ha
     exact h3 a (fun i hi => hj i ((kf L g i).2 ⟨a,ha,hi⟩))
   . rw [q8 _ _ _ _ hjl] at hj
     rw [q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)]
     exact h3 j hj
lemma j4 {n : ℕ} (x y:Fin n->Bool) :
   q207 x y (qr n) (List.ofFn x) (List.ofFn y):=by
 refine ⟨by simp [qr],by simp,?_⟩
 intro j hj
 by_cases hjn:j < n
 . have hx:x ⟨j,hjn⟩=y ⟨j,hjn⟩:=hj _ (by simp [qr,hjn])
   simp [hjn,hx]
 . rw [lGD _ _ (by simp;omega),lGD _ _ (by simp;omega)]
def vg (g:Gate):Gate :=
 match g.op with
 | GateOp.not => ⟨GateOp.not,g.inputs.take 1⟩
 | _ => g
lemma q107 (g:Gate) (F : ℕ->Bool) :
   (vg g).op.eval ((vg g).inputs.map F)=g.op.eval (g.inputs.map F):=by
 obtain ⟨op,inputs⟩:=g
 cases op <;> simp only [vg]
 cases inputs <;> simp [GateOp.eval]
def NOk (g:Gate):Prop:=Ok g/\(g.op=GateOp.not->g.inputs.length<=1)
lemma q45 (g:Gate) (h:Ok g):NOk (vg g):=by
 obtain ⟨op,inputs⟩:=g
 obtain ⟨hop,hlen⟩:=h
 rcases hop with h | h | h
 . have:op=GateOp.and:=h
   subst this;exact ⟨⟨Or.inl rfl,hlen⟩,by simp [vg]⟩
 . have:op=GateOp.or:=h
   subst this;exact ⟨⟨Or.inr (Or.inl rfl),hlen⟩,by simp [vg]⟩
 . have:op=GateOp.not:=h
   subst this
   refine ⟨⟨Or.inr (Or.inr rfl),?_⟩,fun _ => ?_⟩ <;> simp [vg]
lemma jd (gs:List Gate):∀ w:List Bool,
   q3 (gs.map vg) w=q3 gs w:=by
 induction gs with
 | nil => intro w;rfl
 | cons g gs ih =>
   intro w
   have s1:q3 ((g::gs).map vg) w=q3 (gs.map vg)
       (w++[(vg g).op.eval ((vg g).inputs.map fun i => w.getD i false)]):=rfl
   have s2:q3 (g::gs) w
       = q3 gs (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]):=rfl
   rw [s1,s2,q107,ih]
abbrev Stat:=Sum Bool ℕ
def ze (w:List Bool):Stat->Bool
 | Sum.inl c => c
 | Sum.inr j => w.getD j false
def qn (m : ℕ):Stat->Prop
 | Sum.inl _ => True
 | Sum.inr j => j < m
def wr (m : ℕ):List Stat->Option Gate × Stat
 | [] => (none,Sum.inl true)
 | Sum.inl c::_ => (none,Sum.inl (!c))
 | Sum.inr j::_ => (some ⟨GateOp.not,[j]⟩,Sum.inr m)
def ko (m : ℕ):List Stat->Option Gate × Stat
 | [] => (none,Sum.inl true)
 | [Sum.inl c] => (none,Sum.inl c)
 | [Sum.inr j] => (none,Sum.inr j)
 | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c&&d))
 | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inr j else Sum.inl false)
 | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inr j else Sum.inl false)
 | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.and,[j,k]⟩,Sum.inr m)
 | _ => (none,Sum.inl false)
def ji (m : ℕ):List Stat->Option Gate × Stat
 | [] => (none,Sum.inl false)
 | [Sum.inl c] => (none,Sum.inl c)
 | [Sum.inr j] => (none,Sum.inr j)
 | [Sum.inl c,Sum.inl d] => (none,Sum.inl (c||d))
 | [Sum.inl c,Sum.inr j] => (none,bif c then Sum.inl true else Sum.inr j)
 | [Sum.inr j,Sum.inl c] => (none,bif c then Sum.inl true else Sum.inr j)
 | [Sum.inr j,Sum.inr k] => (some ⟨GateOp.or,[j,k]⟩,Sum.inr m)
 | _ => (none,Sum.inl false)
def qg (op:GateOp) (m : ℕ) (ins:List Stat):Option Gate × Stat :=
 match op with
 | GateOp.and => ko m ins
 | GateOp.or => ji m ins
 | GateOp.not => wr m ins
 | _ => (none,Sum.inl false)
lemma q151 (op:GateOp) (m : ℕ) (ins:List Stat) :
   ∀ g ∈ (qg op m ins).1,Ok g:=by
 intro g hg
 cases op <;> simp only [qg] at hg
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp [ko] at hg <;> (subst hg; simp [Ok])
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨c,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp [ji] at hg <;> (subst hg; simp [Ok])
 . rcases ins with _ | ⟨a,l⟩ <;> (try cases a) <;>
     simp [wr] at hg <;> (subst hg; simp [Ok])
 . simp at hg
 . simp at hg
lemma jh (op:GateOp) (m : ℕ) (ins:List Stat)
   (hop:op=GateOp.and\/op=GateOp.or\/op=GateOp.not) (hlen:ins.length<=2)
   (hnot:op=GateOp.not->ins.length<=1) (hc:∃ c,Sum.inl c ∈ ins) :
   (qg op m ins).1=none:=by
 obtain ⟨c,hc⟩:=hc
 rcases hop with rfl | rfl | rfl
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp_all [qg,ko]
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩ <;> (try cases a) <;> (try cases b) <;>
     simp_all [qg,ji]
 . have:=hnot rfl
   rcases ins with _ | ⟨a,_ | ⟨b,l⟩⟩ <;> (try cases a) <;> simp_all [qg,wr]
lemma kn (op:GateOp) (hop:op=GateOp.and\/op=GateOp.or\/op=GateOp.not)
   (w:List Bool) (ins:List Stat) (hlen:ins.length<=2)
   (hv:∀ s ∈ ins,qn w.length s) :
   qn (w.length+(qg op w.length ins).1.toList.length) (qg op w.length ins).2 /\
   ze (q3 (qg op w.length ins).1.toList w) (qg op w.length ins).2
     = op.eval (ins.map (ze w)):=by
 rcases hop with rfl | rfl | rfl
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
   . simp [qg,ko,qn,ze,GateOp.eval]
   . cases a <;> simp_all [qg,ko,qn,ze,GateOp.eval,q3]
   . cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
       simp_all [qg,ko,qn,ze,GateOp.eval,q3]
   . simp at hlen
 . rcases ins with _ | ⟨a,_ | ⟨b,_ | ⟨d,l⟩⟩⟩
   . simp [qg,ji,qn,ze,GateOp.eval]
   . cases a <;> simp_all [qg,ji,qn,ze,GateOp.eval,q3]
   . cases a <;> cases b <;> (rename_i c e; cases c) <;> cases e <;>
       simp_all [qg,ji,qn,ze,GateOp.eval,q3]
   . simp at hlen
 . rcases ins with _ | ⟨a,l⟩
   . simp [qg,wr,qn,ze,GateOp.eval]
   . cases a <;> simp_all [qg,wr,qn,ze,GateOp.eval,q3]
def qa (n : ℕ) (acc:List Stat × List Gate) (g:Gate):List Stat × List Gate :=
 (acc.1++[(qg g.op (n+acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).2],
   acc.2++(qg g.op (n+acc.2.length)
     (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList)
def elim (n : ℕ) (gs:List Gate) (acc:List Stat × List Gate):List Stat × List Gate :=
 gs.foldl (qa n) acc
lemma k4 (n : ℕ) (g:Gate) (gs:List Gate) (acc:List Stat × List Gate) :
   elim n (g::gs) acc=elim n gs (qa n acc g):=rfl
lemma jz (n : ℕ) (pre post:List Gate) (acc:List Stat × List Gate) :
   elim n (pre++post) acc=elim n post (elim n pre acc):=by
 simp [elim,List.foldl_append]
lemma q50 (n : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (elim n gs acc).1.length=acc.1.length+gs.length:=by
 induction gs with
 | nil => intro acc;rfl
 | cons g gs ih =>
   intro acc
   rw [k4,ih]
   simp only [qa,lLA,lLC,List.length_nil]
   omega
lemma wy (n k : ℕ) (d:Stat) (gs:List Gate):∀ acc:List Stat × List Gate,
   k < acc.1.length->(elim n gs acc).1.getD k d=acc.1.getD k d:=by
 induction gs with
 | nil => intro acc _;rfl
 | cons g gs ih =>
   intro acc hk
   rw [k4,ih (qa n acc g) (by simp [qa];omega)]
   exact q8 _ _ _ _ (by omega)
lemma y2 {α:Type} (o:Option α):o.toList.length<=1:=by
 cases o <;> simp
lemma q156 (n : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (∀ g ∈ acc.2,Ok g)->∀ g ∈ (elim n gs acc).2,Ok g:=by
 induction gs with
 | nil => intro acc h;exact h
 | cons g gs ih =>
   intro acc h
   apply ih (qa n acc g)
   intro g' hg'
   rcases List.mem_append.1 hg' with h1 | h1
   . exact h g' h1
   . exact q151 _ _ _ g' (by simpa using h1)
lemma q29 (n : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (elim n gs acc).2.length<=acc.2.length+gs.length:=by
 induction gs with
 | nil => intro acc;simp [elim]
 | cons g gs ih =>
   intro acc
   have h1:=ih (qa n acc g)
   have h2:(qa n acc g).2.length<=acc.2.length+1:=by
     simp only [qa,lLA]
     have:=y2 (qg g.op (n+acc.2.length)
       (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
     omega
   rw [k4,lLC];omega
lemma zt (n k : ℕ) (gs:List Gate):∀ acc:List Stat × List Gate,
   (∀ g ∈ gs,NOk g)->k < acc.1.length->(∃ c,acc.1.getD k (Sum.inl false)=Sum.inl c) ->
   (∃ g ∈ gs,k ∈ g.inputs)->(elim n gs acc).2.length+1<=acc.2.length+gs.length:=by
 induction gs with
 | nil => intro acc _ _ _ h;obtain ⟨g,hg,_⟩:=h;simp at hg
 | cons g gs ih =>
   intro acc hok hk hc hex
   rw [k4,lLC]
   by_cases hkg:k ∈ g.inputs
   . obtain ⟨c,hc⟩:=hc
     have hnok:=hok g List.mem_cons_self
     have hnone:(qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1=none:=by
       apply jh
       . exact hnok.1.1
       . simpa using hnok.1.2
       . intro h;simpa using hnok.2 h
       . exact ⟨c,List.mem_map.2 ⟨k,hkg,hc⟩⟩
     have h2:(qa n acc g).2.length=acc.2.length:=by
       show (acc.2++(qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1.toList).length=_
       rw [hnone];simp
     have:=q29 n gs (qa n acc g)
     omega
   . have hex':∃ g' ∈ gs,k ∈ g'.inputs:=by
       obtain ⟨g',hg',hk'⟩:=hex
       rcases List.mem_cons.1 hg' with rfl | h
       . exact absurd hk' hkg
       . exact ⟨g',h,hk'⟩
     have h1:=ih (qa n acc g) (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
       (by simp [qa];omega)
       (by
         obtain ⟨c,hc⟩:=hc
         refine ⟨c,?_⟩
         simp only [qa]
         rw [q8 _ _ _ _ (by omega)];exact hc)
       hex'
     have h2:(qa n acc g).2.length<=acc.2.length+1:=by
       simp only [qa,lLA]
       have:=y2 (qg g.op (n+acc.2.length)
         (g.inputs.map fun i => acc.1.getD i (Sum.inl false))).1
       omega
     omega
lemma km {m m' : ℕ} (h:m<=m'):∀ s:Stat,qn m s->qn m' s
 | Sum.inl _,_ => trivial
 | Sum.inr _,hj => lt_of_lt_of_le hj h
lemma jg (w t:List Bool):∀ s:Stat,qn w.length s ->
   ze (w++t) s=ze w s
 | Sum.inl _,_ => rfl
 | Sum.inr _,hj => List.getD_append _ _ _ _ hj
def Inv (n : ℕ) (y:List Bool) (w:List Bool) (acc:List Stat × List Gate):Prop :=
 acc.1.length=w.length/\∀ i : ℕ,
   qn (n+acc.2.length) (acc.1.getD i (Sum.inl false)) /\
   ze (q3 acc.2 y) (acc.1.getD i (Sum.inl false))=w.getD i false
lemma j7 (n : ℕ) (y:List Bool) (hy:y.length=n) (gs:List Gate) :
   ∀ (w:List Bool) (acc:List Stat × List Gate),(∀ g ∈ gs,Ok g)->Inv n y w acc ->
     Inv n y (q3 gs w) (elim n gs acc):=by
 induction gs with
 | nil => intro w acc _ h;exact h
 | cons g gs ih =>
   intro w acc hok h
   apply ih (w++[g.op.eval (g.inputs.map fun i => w.getD i false)]) (qa n acc g)
     (fun g' hg' => hok g' (List.mem_cons_of_mem _ hg'))
   obtain ⟨hl,hi⟩:=h
   set w':=q3 acc.2 y with hw'
   have lw':w'.length=n+acc.2.length:=by rw [hw',qu,hy]
   set ins:=g.inputs.map fun i => acc.1.getD i (Sum.inl false) with hins
   have hgok:=hok g List.mem_cons_self
   have hs:=kn g.op hgok.1 w' ins (by simpa [hins] using hgok.2)
     (by
       intro s hs
       obtain ⟨a,_,rfl⟩:=List.mem_map.1 hs
       rw [lw'];exact (hi a).1)
   rw [lw'] at hs
   set r:=qg g.op (n+acc.2.length) ins with hr
   have hvals:ins.map (ze w')=g.inputs.map fun i => w.getD i false:=by
     rw [hins,lMMp]
     apply List.map_congr_left
     intro a _
     exact (hi a).2
   have hnew:q3 (acc.2++r.1.toList) y=q3 r.1.toList w':=by
     rw [zd]
   obtain ⟨t,ht,_⟩:=y1 r.1.toList w'
   refine ⟨by simp [qa,hl],?_⟩
   intro i
   show qn (n+(acc.2++r.1.toList).length) ((acc.1++[r.2]).getD i (Sum.inl false)) /\
     ze (q3 (acc.2++r.1.toList) y) ((acc.1++[r.2]).getD i (Sum.inl false))=_
   rw [hnew,lLA,← nAA]
   by_cases hil:i=acc.1.length
   . subst hil
     rw [z0,hl,z0]
     exact ⟨hs.1,by rw [hs.2,hvals]⟩
   . rw [q8 _ _ _ _ hil,q8 _ _ _ _ (by omega)]
     refine ⟨km (by omega) _ (hi i).1,?_⟩
     rw [ht,jg _ _ _ (by rw [lw'];exact (hi i).1)]
     exact (hi i).2
def qd (n : ℕ) (b:Bool):List Stat :=
 List.ofFn (fun i:Fin n => Sum.inr (i : ℕ))++[Sum.inl b]
lemma kp (n : ℕ) (b:Bool) :
   (qd n b).getD n (Sum.inl false)=Sum.inl b :=
 z2 _ _ _ _ (by simp)
lemma q159 (n : ℕ) (b:Bool) (y:Fin n->Bool) :
   Inv n (List.ofFn y) (List.ofFn y++[b]) (qd n b,[]):=by
 refine ⟨by simp [qd],?_⟩
 intro i
 have l1:(List.ofFn (fun i:Fin n => (Sum.inr (i : ℕ):Stat))).length=n:=by simp
 have l2:(List.ofFn y).length=n:=by simp
 by_cases hin:i=n
 . subst hin
   simp only [qd]
   rw [z2 _ _ _ _ l1,z2 _ _ _ _ l2]
   exact ⟨trivial,rfl⟩
 . simp only [qd]
   rw [q8 _ _ _ _ (by omega),q8 _ _ _ _ (by omega)]
   by_cases hlt:i < n
   . simp [hlt,qn,ze,q3]
   . rw [lGD _ _ (by omega),lGD _ _ (by omega)]
     exact ⟨trivial,rfl⟩
lemma q134 (n : ℕ) (y:Fin n->Bool) (b:Bool) :
   List.ofFn (Fin.snoc y b:Fin (n+1)->Bool)=List.ofFn y++[b]:=by
 rw [List.ofFn_succ']
 simp
lemma jr (n : ℕ) (gs:List Gate):∀ L:List (Finset (Fin (n+1))),
   (∀ g ∈ gs,n ∉ g.inputs)->(∀ j : ℕ,j≠n->Fin.last n ∉ L.getD j ∅) ->
   ∀ j : ℕ,j≠n->Fin.last n ∉ (zb gs L).getD j ∅:=by
 induction gs with
 | nil => intro L _ h;exact h
 | cons g gs ih =>
   intro L hno h
   apply ih (L++[yb L g]) (fun g' hg' => hno g' (List.mem_cons_of_mem _ hg'))
   intro j hj
   by_cases hjl:j=L.length
   . subst hjl
     rw [z0]
     intro hmem
     obtain ⟨a,ha,hia⟩:=(kf L g _).1 hmem
     exact h a (fun e => hno g List.mem_cons_self (e ▸ ha)) hia
   . rw [q8 _ _ _ _ hjl];exact h j hj
lemma q74 (m j : ℕ) (h:j < m) :
   (qr m).getD j ∅={⟨j,h⟩}:=by
 simp [qr,h]
lemma yi (n : ℕ):∀ j : ℕ,j≠n ->
   Fin.last n ∉ (qr (n+1)).getD j ∅:=by
 intro j hj
 by_cases hlt:j < n+1
 . have e:(qr (n+1)).getD j ∅={⟨j,hlt⟩}:=q74 (n+1) j hlt
   rw [e,Finset.mem_singleton]
   intro e'
   exact hj (by have:=congrArg Fin.val e';simpa using this.symm)
 . rw [lGD _ _ (by simp [qr];omega)];simp
lemma q115 (n : ℕ) (f:(Fin (n+1)->Bool)->Bool) (b:Bool) (s : ℕ)
   (hdep:∃ x:Fin (n+1)->Bool,f (Function.update x (Fin.last n) (!x (Fin.last n)))≠f x)
   (hnc:∃ y y':Fin n->Bool,f (Fin.snoc y b)≠f (Fin.snoc y' b))
   (h:HasCircuitSize (n+1) f s) :
   ∃ s',s'+1<=s/\HasCircuitSize n (fun y:Fin n->Bool => f (Fin.snoc y b)) s':=by
 obtain ⟨C,ok,hsz,hev⟩:=h
 have hsz':C.gates.length<=s:=hsz
 set gs:=C.gates.map vg with hgs
 have hnok:∀ g ∈ gs,NOk g:=by
   intro g hg
   obtain ⟨g0,hg0,rfl⟩:=List.mem_map.1 hg
   exact q45 g0 (ok g0 hg0)
 have hevg:∀ x:Fin (n+1)->Bool,(q3 gs (List.ofFn x)).getD C.output false=f x:=by
   intro x
   rw [hgs,jd,← hev x];rfl
 set acc:=elim n gs (qd n b,[]) with hacc
 have hinv:∀ y:Fin n->Bool,
     Inv n (List.ofFn y) (q3 gs (List.ofFn (Fin.snoc y b:Fin (n+1)->Bool))) acc:=by
   intro y
   rw [q134]
   exact j7 n _ (by simp) gs _ _ (fun g hg => (hnok g hg).1) (q159 n b y)
 have hval:∀ y:Fin n->Bool,
     ze (q3 acc.2 (List.ofFn y)) (acc.1.getD C.output (Sum.inl false))
       = f (Fin.snoc y b):=by
   intro y
   rw [((hinv y).2 C.output).2,hevg]
 cases hst:acc.1.getD C.output (Sum.inl false) with
 | inl c =>
   exfalso
   obtain ⟨y,y',hne⟩:=hnc
   apply hne
   rw [← hval y,← hval y',hst];rfl
 | inr j =>
   have hlen:acc.2.length+1<=s:=by
     by_cases hread:∃ g ∈ gs,n ∈ g.inputs
     . have:=zt n n gs (qd n b,[]) hnok (by simp [qd])
         ⟨b,z2 _ _ _ _ (by simp)⟩ hread
       rw [← hacc] at this
       have hl:gs.length=C.gates.length:=by simp [hgs]
       simp only [List.length_nil,zero_add] at this
       omega
     . exfalso
       push Not at hread
       have hout:C.output≠n:=by
         intro e
         rw [e,hacc,wy n n _ gs _ (by simp [qd])] at hst
         have hb:(qd n b).getD n (Sum.inl false)=Sum.inl b :=
           z2 _ _ _ _ (by simp)
         rw [show ((qd n b,([]:List Gate))).1=qd n b from rfl,hb] at hst
         cases hst
       obtain ⟨x,hx⟩:=hdep
       apply hx
       have hns:=jr n gs (qr (n+1)) hread (yi n) C.output hout
       have hag:=(k6 (Function.update x (Fin.last n) (!x (Fin.last n))) x gs _ _ _
         (j4 _ _)).2.2 C.output (by
           intro k hk
           have:k≠Fin.last n:=fun e => hns (e ▸ hk)
           simp [fUN this])
       rw [← hevg,← hevg]
       exact hag
   refine ⟨acc.2.length,hlen,⟨acc.2,j⟩,q156 n gs _ (by simp),le_refl _,?_⟩
   intro y
   have:=hval y
   rw [hst] at this
   exact this
def wmap (n m : ℕ) (π:Fin n->Fin m) (w : ℕ) : ℕ :=
 if h:w < n then (π ⟨w,h⟩ : ℕ) else w - n+m
def jt (n m : ℕ) (π:Fin n->Fin m) (g:Gate):Gate :=
 ⟨g.op,g.inputs.map (wmap n m π)⟩
def q174 (n m : ℕ) (π:Fin n->Fin m) (C:Circuit):Circuit :=
 ⟨C.gates.map (jt n m π),wmap n m π C.output⟩
def step (w:List Bool) (g:Gate):List Bool :=
 w++[g.op.eval (g.inputs.map fun i => w.getD i false)]
def Rel (n m : ℕ) (π:Fin n->Fin m) (W W':List Bool):Prop :=
 n<=W.length/\W'.length+n=W.length+m /\
   ∀ w : ℕ,W'.getD (wmap n m π w) false=W.getD w false
lemma q182 (n m : ℕ) (π:Fin n->Fin m) (W W':List Bool) (g:Gate)
   (h:Rel n m π W W'):Rel n m π (step W g) (step W' (jt n m π g)):=by
 obtain ⟨h1,h2,h3⟩:=h
 have hv:(jt n m π g).op.eval
     ((jt n m π g).inputs.map fun i => W'.getD i false)
     = g.op.eval (g.inputs.map fun i => W.getD i false):=by
   simp only [jt,lMMp]
   congr 1
   apply List.map_congr_left
   intro a _
   exact h3 a
 refine ⟨by simp [step];omega,by simp [step];omega,?_⟩
 intro w
 simp only [step,hv]
 rcases Nat.lt_trichotomy w W.length with hw | hw | hw
 . have hlt:wmap n m π w < W'.length:=by
     unfold wmap
     split
     . have:=(π ⟨w,by assumption⟩).2;omega
     . omega
   rw [List.getD_append _ _ _ _ hlt,List.getD_append _ _ _ _ hw]
   exact h3 w
 . have he:wmap n m π w=W'.length:=by
     unfold wmap
     split
     . omega
     . omega
   rw [he,hw,z0,z0]
 . have hge:W'.length+1<=wmap n m π w:=by
     unfold wmap
     split
     . omega
     . omega
   rw [lGD _ _ (by simp;omega),lGD _ _ (by simp;omega)]
lemma q184 (n m : ℕ) (π:Fin n->Fin m) (gs:List Gate) :
   ∀ W W':List Bool,Rel n m π W W' ->
     Rel n m π (gs.foldl step W) ((gs.map (jt n m π)).foldl step W'):=by
 induction gs with
 | nil => intro W W' h;exact h
 | cons g gs ih =>
   intro W W' h
   exact ih _ _ (q182 n m π W W' g h)
lemma q183 (n m : ℕ) (π:Fin n->Fin m) (x:Fin m->Bool) :
   Rel n m π (List.ofFn (x ∘ π)) (List.ofFn x):=by
 refine ⟨by simp,by simp;omega,?_⟩
 intro w
 unfold wmap
 split
 . rename_i hw
   rw [List.getD_eq_getElem _ _ (by simp),List.getD_eq_getElem _ _ (by simpa using hw)]
   simp
 . rename_i hw
   rw [lGD _ _ (by simp),lGD _ _ (by simp;omega)]
lemma yn {n m : ℕ} (π:Fin n->Fin m) (h:(Fin n->Bool)->Bool) (s : ℕ)
   (hc:HasCircuitSize n h s):HasCircuitSize m (fun x => h (x ∘ π)) s:=by
 obtain ⟨C,ok,hsz,hev⟩:=hc
 refine ⟨q174 n m π C,?_,?_,?_⟩
 . intro g hg
   obtain ⟨g0,hg0,rfl⟩:=List.mem_map.1 hg
   exact ⟨(ok g0 hg0).1,by simpa [jt] using (ok g0 hg0).2⟩
 . simpa [q174,Circuit.size] using hsz
 . intro x
   show _=h (x ∘ π)
   rw [← hev (x ∘ π)]
   have:=(q184 n m π C.gates _ _ (q183 n m π x)).2.2 C.output
   exact this

end PEqualNP.Outside.L_meta_1890_aux.Restrict

namespace PEqualNP.Outside.L_meta_1890_aux.ClosedCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1890_aux

def minor (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) ||
  (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) ||
  (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) ||
  (x 5 && x 7) || (x 6 && x 8) || (x 8 && x 5)

lemma target_zero : SeedErase.target (fun _ => false) = false := by decide
lemma target_one : SeedErase.target (fun _ => true) = true := by decide

lemma target_restrict (x : Fin 9 → Bool) :
    SeedErase.target (Fin.snoc x false) = minor x := by
  simp [SeedErase.target, SeedErase.edges, minor, Fin.snoc, Bool.or_assoc]
  rfl

lemma plain_lower
    (lower : ¬ HasCircuitSize 9 minor 15)
    (s : Nat) (h : HasCircuitSize 10 SeedErase.target s) : 17 ≤ s := by
  obtain ⟨s', hs, C, hc, hsize, he⟩ := Restrict.q115 9 SeedErase.target false s
    (by exact ⟨fun i => decide (i = 4), by decide⟩)
    (by exact ⟨fun _ => false, fun i => decide (i = 0 ∨ i = 1), by decide⟩) h
  by_contra hn
  apply lower
  refine ⟨C, hc, by omega, ?_⟩
  intro x
  exact (he x).trans (target_restrict x)

lemma drop_false {n : Nat} (C : Circuit) (hc : FanInTwo C)
    (nonconstant : ∃ x y : Fin n → Bool,
      C.eval (List.ofFn x ++ [false]) ≠ C.eval (List.ofFn y ++ [false])) :
    ∃ D : Circuit, FanInTwo D ∧ D.size ≤ C.size ∧
      ∀ x : Fin n → Bool, D.eval (List.ofFn x) = C.eval (List.ofFn x ++ [false]) := by
  let acc := Restrict.elim n C.gates (Restrict.qd n false, [])
  have hinv (y : Fin n → Bool) : Restrict.Inv n (List.ofFn y)
      (Restrict.q3 C.gates (List.ofFn y ++ [false])) acc :=
    Restrict.j7 n _ (by simp) C.gates _ _ hc (Restrict.q159 n false y)
  have hval (y : Fin n → Bool) :
      Restrict.ze (Restrict.q3 acc.2 (List.ofFn y))
        (acc.1.getD C.output (Sum.inl false)) = C.eval (List.ofFn y ++ [false]) :=
    ((hinv y).2 C.output).2
  cases hst : acc.1.getD C.output (Sum.inl false) with
  | inl c =>
    obtain ⟨x,y,hxy⟩ := nonconstant
    apply False.elim
    apply hxy
    rw [← hval x, ← hval y, hst]
    rfl
  | inr j =>
    refine ⟨⟨acc.2,j⟩, Restrict.q156 n C.gates _ (by simp), ?_, ?_⟩
    · simpa [Circuit.size] using Restrict.q29 n C.gates (Restrict.qd n false, [])
    · intro x
      have h := hval x
      rw [hst] at h
      exact h

lemma seeded_monotone_lower
    (lower : ¬ HasCircuitSize 9 minor 15)
    (C : Circuit) (p : Fin 10 → Fin 10) (hc : Monotone2 C)
    (he : ∀ x, C.eval (List.ofFn (x ∘ p) ++ [x 0 && x 2]) = SeedErase.target x) :
    17 ≤ C.size := by
  have fixed := SeedErase.circuit_erase_seed C hc p he
  have hzero : C.eval (List.ofFn (fun _ : Fin 10 => false) ++ [false]) = false := by
    simpa only [Function.comp_def] using (fixed (fun _ => false)).trans target_zero
  have hone : C.eval (List.ofFn (fun _ : Fin 10 => true) ++ [false]) = true := by
    simpa only [Function.comp_def] using (fixed (fun _ => true)).trans target_one
  obtain ⟨D, hd, hs, eval⟩ := drop_false C
    (fun g hg => ⟨(hc g hg).1.imp_right Or.inl, (hc g hg).2⟩)
    ⟨fun _ => false, fun _ => true, by rw [hzero, hone]; decide⟩
  have remap := Restrict.yn p (fun y => D.eval (List.ofFn y)) C.size
    ⟨D,hd,hs,fun _ => rfl⟩
  have eq : (fun x => D.eval (List.ofFn (x ∘ p))) = SeedErase.target := by
    funext x
    rw [eval, fixed]
  rw [eq] at remap
  exact plain_lower lower C.size remap

lemma no_terminal_not_two
    (lower : ¬ HasCircuitSize 9 minor 15)
    (gs : List Gate) (i : Nat) (p : Fin 10 → Fin 10)
    (fan : FanInTwo (⟨gs ++ [⟨.not,[i]⟩], 11 + gs.length⟩ : Circuit))
    (size : gs.length + 1 ≤ 18)
    (count : (gs ++ [(⟨.not,[i]⟩ : Gate)]).countP OneNot.isNot ≤ 2) :
    ¬ ∀ x : Fin 10 → Bool,
      (⟨gs ++ [⟨.not,[i]⟩], 11 + gs.length⟩ : Circuit).eval
        (List.ofFn (x ∘ p) ++ [x 0 && x 2]) = SeedErase.target x := by
  intro computes
  let C : Circuit := ⟨gs,i⟩
  have count' : C.gates.countP OneNot.isNot ≤ 1 := by
    simp only [List.countP_append, List.countP_cons, List.countP_nil, OneNot.isNot,
      ↓reduceIte, Nat.zero_add] at count
    exact Nat.le_of_add_le_add_right count
  have fan' : FanInTwo C := fun g hg => fan g (List.mem_append_left _ hg)
  have comp (x : Fin 10 → Bool) :
      C.eval (List.ofFn (x ∘ p) ++ [x 0 && x 2]) = !(SeedErase.target x) := by
    have h := computes x
    change (Restrict.q3 (gs ++ [⟨.not,[i]⟩]) _).getD (11 + gs.length) false = _ at h
    rw [Restrict.zd] at h
    change ((_ ++ [!((Restrict.q3 gs _).getD i false)]).getD (11 + gs.length) false) = _ at h
    rw [Restrict.z2 _ _ _ _ (by simp [Restrict.qu])] at h
    simpa [C, Circuit.eval, Circuit.wires, Restrict.q3] using congrArg Bool.not h
  obtain ⟨D,hd,hs,he⟩ := OneNot.seeded_complement_collapse C p SeedErase.target
    fan' count' target_zero target_one comp
  have bound := seeded_monotone_lower lower D p hd he
  change D.size + 1 ≤ gs.length at hs
  omega

end PEqualNP.Outside.L_meta_1890_aux.ClosedCase
namespace PEqualNP.Outside.L_meta_1890_aux.GraphSeed

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1890_aux

def onPair {n : Nat} (e : Fin n × Fin n) (i : Fin n) : Bool :=
  decide (i = e.1 ∨ i = e.2)

def edgeFun {n : Nat} (es : List (Fin n × Fin n)) (x : Fin n → Bool) : Bool :=
  es.any fun e => x e.1 && x e.2

lemma erase {n : Nat} (es : List (Fin n × Fin n))
    (seed : (Fin n → Bool) → Bool)
    (vanish : ∀ e ∈ es, seed (onPair e) = false)
    (H : (Fin n → Bool) → Bool → Bool)
    (mono : ∀ x y b c, (∀ i, x i = true → y i = true) →
      (b = true → c = true) → H x b = true → H y c = true)
    (correct : ∀ x, H x (seed x) = edgeFun es x) :
    ∀ x, H x false = edgeFun es x := by
  intro x
  apply Bool.eq_iff_iff.mpr
  constructor
  · intro hx
    rw [← correct x]
    exact mono x x false (seed x) (fun _ => id) (by simp) hx
  · intro hx
    obtain ⟨e, he, hv⟩ := List.any_eq_true.mp hx
    simp only [Bool.and_eq_true] at hv
    have pair : edgeFun es (onPair e) = true :=
      List.any_eq_true.mpr ⟨e,he,by simp [onPair]⟩
    have h : H (onPair e) false = true := by rw [← vanish e he, correct, pair]
    apply mono (onPair e) x false false _ (by simp) h
    intro i hi
    simp only [onPair, decide_eq_true_eq] at hi
    rcases hi with rfl | rfl
    · exact hv.1
    · exact hv.2

lemma circuit_erase {n m : Nat} (es : List (Fin n × Fin n))
    (seed : (Fin n → Bool) → Bool)
    (vanish : ∀ e ∈ es, seed (onPair e) = false)
    (C : Circuit) (hc : Monotone2 C) (p : Fin m → Fin n)
    (correct : ∀ x : Fin n → Bool,
      C.eval (List.ofFn (x ∘ p) ++ [seed x]) = edgeFun es x) :
    ∀ x : Fin n → Bool, C.eval (List.ofFn (x ∘ p) ++ [false]) = edgeFun es x := by
  apply erase es seed vanish (fun x b => C.eval (List.ofFn (x ∘ p) ++ [b])) _ correct
  intro x y b c sub bc
  apply SeedErase.eval_mono C hc _ _ (by simp)
  intro i
  by_cases hi : i < m
  · rw [List.getD_append _ _ _ _ (by simpa using hi),
      List.getD_append _ _ _ _ (by simpa using hi)]
    simpa only [List.getD_eq_getElem?_getD, List.getElem?_ofFn, hi,
      ↓reduceDIte, Option.getD_some, Function.comp_apply] using sub (p ⟨i,hi⟩)
  · rw [List.getD_append_right _ _ _ _ (by simp; omega),
      List.getD_append_right _ _ _ _ (by simp; omega)]
    simp only [List.length_ofFn]
    cases k : i - m with
    | zero => simpa using bc
    | succ j => simp

end PEqualNP.Outside.L_meta_1890_aux.GraphSeed

namespace PEqualNP.Outside.L_meta_1890_aux.MinorMap

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1890_aux

def perm (v i : Fin 10) : Fin 10 :=
  (![
    ![9,4,0,1,6,7,3,5,2,8],
    ![4,9,6,1,0,3,7,8,2,5],
    ![0,4,9,6,1,5,3,7,8,2],
    ![1,0,4,9,6,2,5,3,7,8],
    ![4,0,1,6,9,3,5,2,8,7],
    ![4,0,1,2,3,9,5,6,7,8],
    ![0,4,3,2,1,5,9,8,7,6],
    ![1,0,4,3,2,6,5,9,8,7],
    ![2,1,0,4,3,7,6,5,9,8],
    ![0,1,2,3,4,5,6,7,8,9]] : Fin 10 → Fin 10 → Fin 10) v i

lemma send (v : Fin 10) : perm v v = 9 := by
  fin_cases v <;> rfl

set_option maxHeartbeats 2000000 in
lemma target_perm (v : Fin 10) (x : Fin 10 → Bool) :
    SeedErase.target (x ∘ perm v) = SeedErase.target x := by
  fin_cases v <;> simp [perm, SeedErase.target, SeedErase.edges, Function.comp_apply,
    Bool.or_assoc, Bool.or_comm, Bool.or_left_comm, Bool.and_comm]

def lift (v : Fin 10) (y : Fin 9 → Bool) : Fin 10 → Bool :=
  (Fin.snoc y false) ∘ perm v

def seed (v : Fin 10) (y : Fin 9 → Bool) : Bool := lift v y 0 && lift v y 2

def es : List (Fin 9 × Fin 9) :=
  [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(5,7),(6,8),(8,5)]

lemma edge_eq (y : Fin 9 → Bool) : GraphSeed.edgeFun es y = ClosedCase.minor y := by
  simp [GraphSeed.edgeFun, es, ClosedCase.minor, Bool.or_assoc]

lemma target_lift (v : Fin 10) (y : Fin 9 → Bool) :
    SeedErase.target (lift v y) = ClosedCase.minor y := by
  rw [lift, target_perm, ClosedCase.target_restrict]

lemma seed_vanish : ∀ v : Fin 10, ∀ e ∈ es, seed v (GraphSeed.onPair e) = false := by
  decide

lemma extend_mono (x y : Fin 9 → Bool) (h : ∀ i, x i = true → y i = true) :
    ∀ i : Fin 10, (Fin.snoc x false : Fin 10 → Bool) i = true →
      (Fin.snoc y false : Fin 10 → Bool) i = true := by
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simp
  · simpa only [Fin.snoc_castSucc] using h j

lemma seed_mono (v : Fin 10) (x y : Fin 9 → Bool)
    (h : ∀ i, x i = true → y i = true) : seed v x = true → seed v y = true := by
  simp only [seed, lift, Function.comp_apply, Bool.and_eq_true]
  exact fun hxy => ⟨extend_mono x y h _ hxy.1, extend_mono x y h _ hxy.2⟩

lemma family_bounds (v : Fin 10) (x : Fin 9 → Bool) :
    OneNot.LeL (List.ofFn (fun _ : Fin 9 => false) ++ [seed v (fun _ => false)])
      (List.ofFn x ++ [seed v x]) ∧
    OneNot.LeL (List.ofFn x ++ [seed v x])
      (List.ofFn (fun _ : Fin 9 => true) ++ [seed v (fun _ => true)]) := by
  constructor
  · exact OneNot.leSnoc (by simp) (OneNot.leInputs _ _ (by simp)) (seed_mono v _ _ (by simp))
  · exact OneNot.leSnoc (by simp) (OneNot.leInputs _ _ (by simp)) (seed_mono v _ _ (by simp))

def rawStat (v : Fin 10) (j : Fin 10) : Restrict.Stat :=
  if perm v j = 9 then Sum.inl false else Sum.inr (perm v j).val

def initial (v : Fin 10) (p : Fin 10 → Fin 10) : List Restrict.Stat :=
  List.ofFn (rawStat v ∘ p) ++ [Sum.inr 9]

lemma raw_value (v j : Fin 10) (y : Fin 9 → Bool) :
    Restrict.ze (List.ofFn y ++ [seed v y]) (rawStat v j) = lift v y j := by
  unfold rawStat
  split_ifs with h
  · simp [Restrict.ze, lift, h, Fin.snoc, Function.comp_apply]
  · have hn : (perm v j).val ≠ 9 := by
      intro hn
      apply h
      exact Fin.ext hn
    have lt : (perm v j).val < 9 := by have := (perm v j).isLt; omega
    have eq : (⟨(perm v j).val, lt⟩ : Fin 9).castSucc = perm v j := Fin.ext rfl
    change (List.ofFn y ++ [seed v y]).getD (perm v j).val false =
      (Fin.snoc y false : Fin 10 → Bool) (perm v j)
    rw [List.getD_append _ _ _ _ (by simpa using lt),
      List.getD_eq_getElem _ _ (by simpa using lt), List.getElem_ofFn, ← eq, Fin.snoc_castSucc]

lemma raw_valid (v j : Fin 10) : Restrict.qn 10 (rawStat v j) := by
  unfold rawStat
  split <;> simp [Restrict.qn, (perm v j).isLt]

lemma initial_valid (v : Fin 10) (p : Fin 10 → Fin 10) (y : Fin 9 → Bool) :
    Restrict.Inv 10 (List.ofFn y ++ [seed v y])
      (List.ofFn (lift v y ∘ p) ++ [seed v y]) (initial v p, []) := by
  constructor
  · simp [initial]
  · intro i
    by_cases hi : i < 10
    · simp only [initial, Restrict.q3, List.foldl_nil, List.length_nil, Nat.add_zero]
      rw [List.getD_append _ _ _ _ (by simpa using hi),
        List.getD_append _ _ _ _ (by simpa using hi),
        List.getD_eq_getElem _ _ (by simpa using hi),
        List.getD_eq_getElem _ _ (by simpa using hi), List.getElem_ofFn, List.getElem_ofFn]
      exact ⟨raw_valid _ _, raw_value _ _ _⟩
    · simp only [initial, Restrict.q3, List.foldl_nil, List.length_nil, Nat.add_zero]
      rw [List.getD_append_right _ _ _ _ (by simp; omega),
        List.getD_append_right _ _ _ _ (by simp; omega)]
      simp only [List.length_ofFn]
      cases eq : i - 10 with
      | zero =>
        simp only [List.getD_cons_zero]
        constructor
        · exact Nat.lt_succ_self 9
        · change (List.ofFn y ++ [seed v y]).getD 9 false = seed v y
          exact Restrict.z2 _ _ _ _ (by simp)
      | succ k => simp [Restrict.qn, Restrict.ze]

lemma raw_constant (a : Fin 10) (p : Fin 10 → Fin 10) :
    (initial (p a) p).getD a.val (Sum.inl false) = Sum.inl false := by
  unfold initial
  rw [List.getD_append _ _ _ _ (by simpa [initial] using a.isLt)]
  simp [initial, rawStat, send]

end PEqualNP.Outside.L_meta_1890_aux.MinorMap

namespace PEqualNP.Outside.L_meta_1890_aux.Restrict

def isN (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

lemma qg_op (op : GateOp) (m : Nat) (ins : List Stat) (g : Gate)
    (h : g ∈ (qg op m ins).1.toList) : g.op = op := by
  cases op <;> simp only [qg] at h
  · unfold ko at h
    split at h <;> simp_all
  · unfold ji at h
    split at h <;> simp_all
  · unfold wr at h
    split at h <;> simp_all
  · simp at h
  · simp at h

lemma qg_notcount (op : GateOp) (m : Nat) (ins : List Stat) :
    (qg op m ins).1.toList.countP isN ≤ if isN ⟨op,[]⟩ then 1 else 0 := by
  cases h : (qg op m ins).1 with
  | none => simp
  | some g =>
    have hop := qg_op op m ins g (by simp [h])
    cases op <;> simp [h, isN, hop]

lemma elim_notcount (n : Nat) (gs : List Gate) (acc : List Stat × List Gate) :
    (elim n gs acc).2.countP isN ≤ acc.2.countP isN + gs.countP isN := by
  induction gs generalizing acc with
  | nil => simp [elim]
  | cons g gs ih =>
    have h := ih (qa n acc g)
    have stepbound := qg_notcount g.op (n+acc.2.length)
      (g.inputs.map fun i => acc.1.getD i (Sum.inl false))
    have same : isN ⟨g.op,[]⟩ = isN g := rfl
    rw [same] at stepbound
    have hs : (qa n acc g).2.countP isN ≤ acc.2.countP isN +
        (if isN g then 1 else 0) := by
      simpa only [qa, List.countP_append] using Nat.add_le_add_left stepbound (acc.2.countP isN)
    calc
      (elim n (g :: gs) acc).2.countP isN ≤ (qa n acc g).2.countP isN + gs.countP isN := h
      _ ≤ (acc.2.countP isN + (if isN g then 1 else 0)) + gs.countP isN :=
        Nat.add_le_add_right hs _
      _ = acc.2.countP isN + (g :: gs).countP isN := by
        rw [List.countP_cons]
        split <;> omega

lemma constant_not_step (n k : Nat) (acc : List Stat × List Gate) (b : Bool)
    (g : Gate) (tail : List Nat) (hop : g.op = .not)
    (pins : g.inputs = k :: tail) (constant : acc.1.getD k (Sum.inl false) = Sum.inl b) :
    (qa n acc g).2 = acc.2 := by
  simp only [qa, hop, pins, List.map_cons, constant, qg, wr]
  simp

lemma elim_constant_not_saves (n k : Nat) (pre post : List Gate)
    (acc : List Stat × List Gate) (b : Bool) (g : Gate) (tail : List Nat)
    (hop : g.op = .not) (pins : g.inputs = k :: tail)
    (hk : k < acc.1.length) (constant : acc.1.getD k (Sum.inl false) = Sum.inl b) :
    (elim n (pre ++ g :: post) acc).2.length + 1 ≤ acc.2.length + (pre ++ g :: post).length ∧
    (elim n (pre ++ g :: post) acc).2.countP isN + 1 ≤
      acc.2.countP isN + (pre ++ g :: post).countP isN := by
  have held : (elim n pre acc).1.getD k (Sum.inl false) = Sum.inl b :=
    (wy n k _ pre acc hk).trans constant
  have eq := constant_not_step n k (elim n pre acc) b g tail hop pins held
  have beforeSize := q29 n pre acc
  have afterSize := q29 n post (qa n (elim n pre acc) g)
  have beforeCount := elim_notcount n pre acc
  have afterCount := elim_notcount n post (qa n (elim n pre acc) g)
  rw [eq] at afterSize afterCount
  rw [jz, k4]
  simp only [List.length_append, List.length_cons, List.countP_append,
    List.countP_cons, isN, hop, ↓reduceIte]
  constructor <;> omega

end PEqualNP.Outside.L_meta_1890_aux.Restrict

namespace PEqualNP.Outside.L_meta_1890_aux.RawNotCase

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_1890_aux

lemma no_complement_raw_not
    (lower : ¬ HasCircuitSize 9 ClosedCase.minor 15)
    (pre post : List Gate) (g : Gate) (a : Fin 10) (tail : List Nat)
    (out : Nat) (p : Fin 10 → Fin 10)
    (hop : g.op = .not) (pins : g.inputs = a.val :: tail)
    (fan : FanInTwo (⟨pre ++ g :: post, out⟩ : Circuit))
    (size : (pre ++ g :: post).length ≤ 17)
    (count : (pre ++ g :: post).countP Restrict.isN ≤ 2) :
    ¬ ∀ x : Fin 10 → Bool,
      (⟨pre ++ g :: post, out⟩ : Circuit).eval
        (List.ofFn (x ∘ p) ++ [x 0 && x 2]) = !(SeedErase.target x) := by
  intro correct
  let v := p a
  let init := (MinorMap.initial v p, ([] : List Gate))
  let acc := Restrict.elim 10 (pre ++ g :: post) init
  let e := fun y : Fin 9 → Bool => List.ofFn y ++ [MinorMap.seed v y]
  have saves := Restrict.elim_constant_not_saves 10 a.val pre post init false g tail
    hop pins (by simpa [init, MinorMap.initial] using a.isLt) (MinorMap.raw_constant a p)
  have hinv (y : Fin 9 → Bool) : Restrict.Inv 10 (e y)
      (Restrict.q3 (pre ++ g :: post)
        (List.ofFn (MinorMap.lift v y ∘ p) ++ [MinorMap.seed v y])) acc :=
    Restrict.j7 10 _ (by simp [e]) _ _ _ fan (MinorMap.initial_valid v p y)
  have hval (y : Fin 9 → Bool) :
      Restrict.ze (Restrict.q3 acc.2 (e y))
        (acc.1.getD out (Sum.inl false)) = !(ClosedCase.minor y) := by
    rw [((hinv y).2 out).2]
    have h := correct (MinorMap.lift v y)
    rw [MinorMap.target_lift] at h
    exact h
  cases hst : acc.1.getD out (Sum.inl false) with
  | inl b =>
    have h0 := hval (fun _ => false)
    have h1 := hval (fun _ => true)
    rw [hst] at h0 h1
    simp only [Restrict.ze, ClosedCase.minor, Bool.false_and, Bool.false_or,
      Bool.true_and, Bool.true_or, Bool.not_false, Bool.not_true] at h0 h1
    exact Bool.noConfusion (h0.symm.trans h1)
  | inr j =>
    let D : Circuit := ⟨acc.2,j⟩
    have hd : FanInTwo D := Restrict.q156 10 _ init (by simp [init])
    have ds : D.size ≤ 16 := by
      change acc.2.length ≤ 16
      change acc.2.length + 1 ≤ 0 + (pre ++ g :: post).length at saves
      omega
    have dn : D.gates.countP OneNot.isNot ≤ 1 := by
      change acc.2.countP Restrict.isN ≤ 1
      have h := saves.2
      change acc.2.countP Restrict.isN + 1 ≤ 0 + (pre ++ g :: post).countP Restrict.isN at h
      omega
    have deval (y : Fin 9 → Bool) : D.eval (e y) = !(ClosedCase.minor y) := by
      have h := hval y
      rw [hst] at h
      exact h
    obtain ⟨E, hm, hs, he⟩ := OneNot.remove_only_not D ClosedCase.minor e
      (fun _ => false) (fun _ => true) (by intro y; simp [e])
      (MinorMap.family_bounds v) hd dn (by decide) (by decide) deval
    have fixed : ∀ y : Fin 9 → Bool,
        E.eval (List.ofFn y ++ [false]) = ClosedCase.minor y := by
      have good : ∀ y : Fin 9 → Bool,
          E.eval (List.ofFn (y ∘ id) ++ [MinorMap.seed v y]) = GraphSeed.edgeFun MinorMap.es y := by
        intro y
        rw [MinorMap.edge_eq]
        exact he y
      have f := GraphSeed.circuit_erase MinorMap.es (MinorMap.seed v)
        (MinorMap.seed_vanish v) E hm id good
      intro y
      simpa only [Function.comp_id, MinorMap.edge_eq] using f y
    have h0 := fixed (fun _ => false)
    have h1 := fixed (fun _ => true)
    obtain ⟨F,hf,hfs,hfe⟩ := ClosedCase.drop_false E
      (fun g hg => ⟨(hm g hg).1.imp_right Or.inl, (hm g hg).2⟩)
      ⟨fun _ => false, fun _ => true, by rw [h0,h1]; decide⟩
    apply lower
    refine ⟨F,hf,by omega,?_⟩
    intro y
    rw [hfe,fixed]

end PEqualNP.Outside.L_meta_1890_aux.RawNotCase
