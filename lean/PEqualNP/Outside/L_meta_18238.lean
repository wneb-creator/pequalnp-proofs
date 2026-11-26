import PEqualNP.Defs
import Mathlib.Data.List.GetD

namespace PEqualNP.Outside.L_meta_18238
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private def old (x : Fin 10 → Bool) := List.ofFn x ++ [!x 0]
private def small (x : Fin 10 → Bool) := List.ofFn (fun i : Fin 9 => x i.succ)
private def idx (i : ℕ) := if i < 10 then i-1 else i-2
private def move (g : Gate) : Gate := ⟨g.op, g.inputs.map idx⟩
private def step (w : List Bool) (g : Gate) :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
private def run (gs : List Gate) (w : List Bool) := gs.foldl step w
private def fixable (g : Gate) : Prop :=
  (g.op = .not → g.inputs.head? ≠ some 0 ∧ g.inputs.head? ≠ some 10) ∧
  (g.op ≠ .not → 0 ∉ g.inputs ∧ 10 ∉ g.inputs)

private lemma readZero (x : Fin 10 → Bool) (s : List Bool) :
    (old x ++ s).getD 0 false = x 0 := by
  simp [old, List.getD_eq_getElem?_getD]
private lemma readTen (x : Fin 10 → Bool) (s : List Bool) :
    (old x ++ s).getD 10 false = !x 0 := by
  simp [old, List.getD_eq_getElem?_getD]

private lemma readMove (x : Fin 10 → Bool) (s : List Bool) (i : ℕ) (h0 : i ≠ 0) (h10 : i ≠ 10) :
    (old x ++ s).getD i false = (small x ++ s).getD (idx i) false := by
  by_cases h : i < 11
  · interval_cases i <;> simp_all [old, small, idx, List.getD_eq_getElem?_getD]
  · rw [List.getD_append_right _ _ _ _ (by simp [old]; omega),
        List.getD_append_right _ _ _ _ (by simp [small, idx]; split <;> omega)]
    congr 1
    simp [old, small, idx, show ¬i < 10 by omega]
    omega

private lemma ordinary (x : Fin 10 → Bool) (s : List Bool) (g : Gate) (h : fixable g) :
    g.op.eval (g.inputs.map fun i => (old x ++ s).getD i false) =
      (move g).op.eval ((move g).inputs.map fun i => (small x ++ s).getD i false) := by
  change _ = g.op.eval ((g.inputs.map idx).map _)
  rw [List.map_map]
  by_cases hn : g.op = .not
  · obtain ⟨h0,h10⟩ := h.1 hn
    cases hg : g.inputs with
    | nil => simp [hg,hn]
    | cons i rest =>
      simp only [hg, List.head?_cons, ne_eq, Option.some.injEq] at h0 h10
      simp [hn, GateOp.eval, Function.comp_apply, -List.getD_eq_getElem?_getD, readMove x s i h0 h10]
  · obtain ⟨h0,h10⟩ := h.2 hn
    apply congrArg g.op.eval
    apply List.map_congr_left
    intro i hi
    apply readMove
    · rintro rfl; exact h0 hi
    · rintro rfl; exact h10 hi

private lemma segment (x : Fin 10 → Bool) (gs : List Gate) (s : List Bool)
    (good : ∀ g ∈ gs, fixable g) :
    ∃ t, run gs (old x ++ s) = old x ++ t ∧ run (gs.map move) (small x ++ s) = small x ++ t := by
  induction gs generalizing s with
  | nil => exact ⟨s,rfl,rfl⟩
  | cons g gs ih =>
    have ev := ordinary x s g (good _ List.mem_cons_self)
    let v := g.op.eval (g.inputs.map fun i => (old x ++ s).getD i false)
    have ho : step (old x ++ s) g = old x ++ (s ++ [v]) := by simp [step,v,List.append_assoc]
    have hs : step (small x ++ s) (move g) = small x ++ (s ++ [v]) := by
      simp [step, v, ev, List.append_assoc]
    change ∃ t, run gs (step (old x ++ s) g) = _ ∧ run (gs.map move) (step (small x ++ s) (move g)) = _
    rw [ho,hs]
    exact ih _ (fun k hk => good k (List.mem_cons_of_mem _ hk))

private def mix (x : Fin 10 → Bool) (b : Bool) (q : Bool ⊕ ℕ) (w : List Bool) :=
  let a := q.elim id (fun i => w.getD i false)
  if b = true then x 0 || a else !x 0 && a

private def other (b : Bool) (i : ℕ) : Bool ⊕ ℕ :=
  if i = 0 then .inl false else if i = 10 then .inl true else .inr (idx i)

private lemma mate (x : Fin 10 → Bool) (s : List Bool) (b : Bool) (i : ℕ) :
    mix x b (other b i) (small x ++ s) =
      if b = true then x 0 || (old x ++ s).getD i false else !x 0 && (old x ++ s).getD i false := by
  by_cases h0 : i = 0
  · subst i; rw [readZero]; cases b <;> cases h : x 0 <;> simp [mix,other,h]
  by_cases ht : i = 10
  · subst i; rw [readTen]; cases b <;> cases h : x 0 <;> simp [mix,other,h]
  rw [readMove x s i h0 ht]
  simp [mix,other,h0,ht]

private lemma marked (g : Gate) (b : Bool) (ho : g.op = if b then .or else .and)
    (hp : (if b then 0 else 10) ∈ g.inputs) (hl : g.inputs.length ≤ 2) :
    ∃ q, ∀ (x : Fin 10 → Bool) (s : List Bool),
      g.op.eval (g.inputs.map fun i => (old x ++ s).getD i false) = mix x b q (small x ++ s) := by
  cases hh : g.inputs with
  | nil => simp [hh] at hp
  | cons i rest =>
    cases hr : rest with
    | nil =>
      rw [hh,hr] at hp
      simp only [List.mem_singleton] at hp
      refine ⟨.inl (!b), ?_⟩
      intro x s
      subst i
      cases b <;> simp_all [GateOp.eval,mix,-List.getD_eq_getElem?_getD,readZero,readTen]
    | cons j tail =>
      rw [hh,hr] at hl hp
      obtain rfl : tail = [] := List.eq_nil_iff_length_eq_zero.mpr (by simp only [List.length_cons] at hl; omega)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
      rcases hp with hi | hj
      · refine ⟨other b j, ?_⟩
        intro x s
        rw [mate,ho]
        subst i
        cases b <;> simp_all [GateOp.eval,-List.getD_eq_getElem?_getD,readZero,readTen]
      · refine ⟨other b i, ?_⟩
        intro x s
        rw [mate,ho]
        subst j
        cases b <;> simp_all [GateOp.eval,-List.getD_eq_getElem?_getD,readZero,readTen,Bool.or_comm,Bool.and_comm]

private lemma splitTwo (l : List Gate) (i j : ℕ) (hi : i < l.length) (hj : j < l.length)
    (hlt : i < j) (clean : ∀ k (hk : k < l.length), k ≠ i → k ≠ j → fixable l[k]) :
    ∃ a b c : List Gate, l = a ++ l[i] :: (b ++ l[j] :: c) ∧
      (∀ g ∈ a, fixable g) ∧ (∀ g ∈ b, fixable g) ∧ (∀ g ∈ c, fixable g) := by
  let a := l.take i
  let b := (l.drop (i+1)).take (j-(i+1))
  let c := l.drop (j+1)
  have ja : i+1+(j-(i+1)) = j := by omega
  have jb : j-(i+1)+(i+1) = j := by omega
  have hmid : j-(i+1) < (l.drop (i+1)).length := by simp; omega
  have hfront := List.take_append_drop i l
  rw [List.drop_eq_getElem_cons hi] at hfront
  have hback := List.take_append_drop (j-(i+1)) (l.drop (i+1))
  rw [List.drop_eq_getElem_cons hmid, List.getElem_drop, List.drop_drop] at hback
  have ix : i+1+(j-(i+1)+1) = j+1 := by omega
  simp only [ja,ix] at hback
  refine ⟨a,b,c,?_,?_,?_,?_⟩
  · dsimp only [a,b,c]
    exact hfront.symm.trans (congrArg (fun t => l.take i ++ l[i] :: t) hback.symm)
  · intro g hg
    obtain ⟨k,hk,rfl⟩ := List.mem_iff_getElem.mp hg
    have hk' : k < i := by simpa [a, Nat.min_eq_left (Nat.le_of_lt hi)] using hk
    simpa [a] using clean k (by omega) (by omega) (by omega)
  · intro g hg
    obtain ⟨k,hk,rfl⟩ := List.mem_iff_getElem.mp hg
    have hk' : k < j-(i+1) := by dsimp [b] at hk; simp at hk; omega
    simpa [b] using clean (i+1+k) (by omega) (by omega) (by omega)
  · intro g hg
    obtain ⟨k,hk,rfl⟩ := List.mem_iff_getElem.mp hg
    have hk' : k < l.length-(j+1) := by simpa [c] using hk
    simpa [c] using clean (j+1+k) (by omega) (by omega) (by omega)

private def result (C : Circuit) : Prop :=
  ∃ (A B D : Circuit) (f : Bool) (p q : Bool ⊕ ℕ),
    (∀ U ∈ [A,B,D], FanInTwo U) ∧ A.size+B.size+D.size+2 ≤ C.size ∧
    ∀ x : Fin 10 → Bool,
      let a := A.wires (small x)
      let b := B.wires (a ++ [mix x f p a])
      C.eval (old x) = D.eval (b ++ [mix x (!f) q b])

private lemma enough (C : Circuit) (a b c : List Gate) (g h : Gate)
    (pieces : C.gates = a ++ g :: (b ++ h :: c)) :
    a.length+b.length+c.length+2 = C.size := by
  simp [Circuit.size,pieces]
  omega

private lemma runAppend (gs : List Gate) (w : List Bool) : ∃ s, run gs w = w ++ s := by
  induction gs generalizing w with
  | nil => exact ⟨[],by simp [run]⟩
  | cons g gs ih =>
    obtain ⟨s, hs⟩ := ih (step w g)
    exact ⟨_,hs.trans (List.append_assoc _ _ _)⟩

private lemma rawOutput (C : Circuit) (hsize : 2 ≤ C.size) (f : Bool)
    (hout : C.output = if f then 0 else 10) : result C := by
  let empty : Circuit := ⟨[],0⟩
  let out : Circuit := ⟨[],9⟩
  refine ⟨empty, empty, out, f, .inl (!f), .inl false, ?_, hsize, ?_⟩
  · simp [empty, out, FanInTwo]
  intro x
  obtain ⟨s,hs⟩ := runAppend C.gates (old x)
  change (run C.gates (old x)).getD C.output false = _
  rw [hs,hout]
  cases f <;> simp [empty,out,Circuit.eval,Circuit.wires,mix,small,old,List.getD_eq_getElem?_getD]

private lemma stitch (C : Circuit) (hf : FanInTwo C) (f : Bool) (a b c : List Gate) (g h : Gate)
    (pieces : C.gates = a ++ g :: (b ++ h :: c))
    (ha : ∀ k ∈ a, fixable k) (hb : ∀ k ∈ b, fixable k) (hc : ∀ k ∈ c, fixable k)
    (p q : Bool ⊕ ℕ)
    (hp : ∀ x s, g.op.eval (g.inputs.map fun i => (old x ++ s).getD i false) =
      mix x f p (small x ++ s))
    (hq : ∀ x s, h.op.eval (h.inputs.map fun i => (old x ++ s).getD i false) =
      mix x (!f) q (small x ++ s)) : result C := by
  have hl := enough C a b c g h pieces
  by_cases h0 : C.output = 0
  · exact rawOutput C (by omega) true h0
  by_cases ht : C.output = 10
  · exact rawOutput C (by omega) false ht
  let A : Circuit := ⟨a.map move,0⟩
  let B : Circuit := ⟨b.map move,0⟩
  let D : Circuit := ⟨c.map move,idx C.output⟩
  refine ⟨A,B,D,f,p,q,?_,?_,?_⟩
  · have fan (gs : List Gate) (o : ℕ) (inc : ∀ k ∈ gs, k ∈ C.gates) :
        FanInTwo (⟨gs.map move,o⟩ : Circuit) := by
      intro k hk
      obtain ⟨k',hk',rfl⟩ := List.mem_map.mp hk
      simpa [move] using hf k' (inc k' hk')
    intro U hU
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hU
    rcases hU with rfl | rfl | rfl
    · exact fan a _ (fun k hk => by simp [pieces,hk])
    · exact fan b _ (fun k hk => by simp [pieces,hk])
    · exact fan c _ (fun k hk => by simp [pieces,hk])
  · simpa [A,B,D,Circuit.size] using hl.le
  intro x
  obtain ⟨t1, h1, h1'⟩ := segment x a [] ha
  simp only [List.append_nil] at h1 h1'
  let m1 := mix x f p (small x ++ t1)
  let s1 := t1 ++ [m1]
  have sg : step (old x ++ t1) g = old x ++ s1 := by
    rw [step,hp]; simp [s1,m1,List.append_assoc]
  obtain ⟨t2, h2, h2'⟩ := segment x b s1 hb
  let m2 := mix x (!f) q (small x ++ t2)
  let s2 := t2 ++ [m2]
  have sh : step (old x ++ t2) h = old x ++ s2 := by
    rw [step,hq]; simp [s2,m2,List.append_assoc]
  obtain ⟨t3, h3, h3'⟩ := segment x c s2 hc
  have original : C.wires (old x) = old x ++ t3 := by
    change run C.gates _ = _
    rw [pieces]
    change (a ++ g :: (b ++ h :: c)).foldl step _ = _
    simp only [List.foldl_append,List.foldl_cons]
    change run c (step (run b (step (run a (old x)) g)) h) = _
    rw [h1,sg,h2,sh,h3]
  change (C.wires (old x)).getD C.output false = _
  rw [original, readMove x t3 _ h0 ht]
  change _ = (run (c.map move) ((run (b.map move) ((run (a.map move) (small x)) ++
    [mix x f p (run (a.map move) (small x))])) ++
    [mix x (!f) q (run (b.map move) ((run (a.map move) (small x)) ++
    [mix x f p (run (a.map move) (small x))]))])).getD (idx C.output) false
  rw [h1']
  change _ = (run (c.map move) ((run (b.map move) ((small x ++ t1) ++ [m1])) ++
    [mix x (!f) q (run (b.map move) ((small x ++ t1) ++ [m1]))])).getD _ _
  rw [List.append_assoc, h2']
  change _ = (run (c.map move) ((small x ++ t2) ++ [m2])).getD _ _
  rw [List.append_assoc, h3']

private lemma ordered (C : Circuit) (hf : FanInTwo C) (u v : Fin C.gates.length)
    (huv : u.val < v.val) (f : Bool)
    (uop : (C.gates.get u).op = if f then .or else .and)
    (up : (if f then 0 else 10) ∈ (C.gates.get u).inputs)
    (vop : (C.gates.get v).op = if !f then .or else .and)
    (vp : (if !f then 0 else 10) ∈ (C.gates.get v).inputs)
    (clean : ∀ k : Fin C.gates.length, k ≠ u → k ≠ v → fixable (C.gates.get k)) : result C := by
  obtain ⟨a,b,c,hlist,ha,hb,hc⟩ := splitTwo C.gates u.val v.val u.isLt v.isLt huv
    (fun k hk hi hj => clean ⟨k,hk⟩ (fun e => hi (congrArg Fin.val e))
      (fun e => hj (congrArg Fin.val e)))
  obtain ⟨p,hp⟩ := marked _ f uop up (hf _ (List.get_mem ..)).2
  obtain ⟨q,hq⟩ := marked _ (!f) vop vp (hf _ (List.get_mem ..)).2
  exact stitch C hf f a b c _ _ hlist ha hb hc p q hp hq

end PEqualNP.Outside.L_meta_18238
open PEqualNP.Outside.L_meta_18238 PEqualNP.CircuitLowerBounds
theorem PEqualNP.Outside.L_meta_18238 : ∀ (x1 : PEqualNP.CircuitLowerBounds.Circuit) (x2 x3 : Fin x1.gates.length),   PEqualNP.MetaComplexity.FanInTwo x1 →     (x1.gates.get x2).op = PEqualNP.CircuitLowerBounds.GateOp.or →       (0 : ℕ) ∈ (x1.gates.get x2).inputs →         (x1.gates.get x3).op = PEqualNP.CircuitLowerBounds.GateOp.and →           (10 : ℕ) ∈ (x1.gates.get x3).inputs →             (∀ (x9 : Fin x1.gates.length),                 x9 ≠ x2 →                   x9 ≠ x3 →                     have x12 : PEqualNP.CircuitLowerBounds.Gate := x1.gates.get x9;                     (x12.op = PEqualNP.CircuitLowerBounds.GateOp.not → x12.inputs.head? ≠ Option.some (0 : ℕ) ∧ x12.inputs.head? ≠ Option.some (10 : ℕ)) ∧ (x12.op ≠ PEqualNP.CircuitLowerBounds.GateOp.not → (0 : ℕ) ∉ x12.inputs ∧ (10 : ℕ) ∉ x12.inputs)) →               ∃ (x10 : PEqualNP.CircuitLowerBounds.Circuit) (x11 : PEqualNP.CircuitLowerBounds.Circuit) (x12 : PEqualNP.CircuitLowerBounds.Circuit) (x13 : Bool) (x14 : Bool ⊕ ℕ) (x15 : Bool ⊕ ℕ),                 (∀ x16 ∈ [x10, x11, x12], PEqualNP.MetaComplexity.FanInTwo x16) ∧                   x10.size + x11.size + x12.size + (2 : ℕ) ≤ x1.size ∧                     ∀ (x16 : Fin (10 : ℕ) → Bool),                       have x17 : Bool → Bool ⊕ ℕ → List Bool → Bool := fun (x17 : Bool) (x18 : Bool ⊕ ℕ) (x19 : List Bool) =>                         have x20 : Bool := Sum.elim id (fun (x20 : ℕ) => x19.getD x20 Bool.false) x18;                         if x17 = Bool.true then x16 (0 : Fin (10 : ℕ)) || x20 else !x16 (0 : Fin (10 : ℕ)) && x20;                       have x18 : List Bool := x10.wires (List.ofFn fun (x18 : Fin (9 : ℕ)) => x16 x18.succ);                       have x19 : List Bool := x11.wires (x18 ++ [x17 x13 x14 x18]);                       x1.eval (List.ofFn x16 ++ [!x16 (0 : Fin (10 : ℕ))]) = x12.eval (x19 ++ [x17 (!x13) x15 x19]) := by
  intro C u v hf hu hp hv hq clean
  change result C
  by_cases h : u.val < v.val
  · exact ordered C hf u v h true hu hp hv hq clean
  · have hne : u.val ≠ v.val := by
      intro he
      have e := Fin.ext he
      subst v
      rw [hu] at hv
      contradiction
    exact ordered C hf v u (by omega) false hv hq hu hp (fun k hk hj => clean k hj hk)
