import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_17613_aux

open PEqualNP.CircuitLowerBounds

def F (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

lemma wires_eq (C : Circuit) (x : List Bool) : C.wires x = C.gates.foldl F x := rfl

lemma len_foldl (gs : List Gate) : ∀ w : List Bool, (gs.foldl F w).length = w.length + gs.length := by
  induction gs with
  | nil => intro w; simp
  | cons g gs ih => intro w; simp only [List.foldl_cons, ih, F]; simp; omega

lemma getD_F (w : List Bool) (g : Gate) (i : ℕ) : (F w g).getD i false =
    if i < w.length then w.getD i false
    else if i = w.length then g.op.eval (g.inputs.map fun i => w.getD i false) else false := by
  unfold F
  split_ifs with h1 h2
  · exact List.getD_append _ _ _ _ h1
  · subst h2; rw [List.getD_append_right _ _ _ _ (le_refl _)]; simp
  · rw [List.getD_eq_default _ _ (by simp; omega)]

lemma pref (gs : List Gate) : ∀ (w : List Bool) (i : ℕ), i < w.length →
    (gs.foldl F w).getD i false = w.getD i false := by
  induction gs with
  | nil => intros; rfl
  | cons g gs ih =>
    intro w i h
    rw [List.foldl_cons, ih _ i (by simp [F]; omega), getD_F, if_pos h]

lemma gateval (gs : List Gate) : ∀ (w : List Bool) (k : ℕ) (hk : k < gs.length),
    (gs.foldl F w).getD (w.length + k) false =
      (gs[k]).op.eval ((gs[k]).inputs.map fun i =>
        if i < w.length + k then (gs.foldl F w).getD i false else false) := by
  induction gs with
  | nil => intro w k hk; simp at hk
  | cons g gs ih =>
    intro w k hk
    cases k with
    | zero =>
      simp only [List.foldl_cons, List.getElem_cons_zero, Nat.add_zero]
      rw [pref gs (F w g) w.length (by simp [F]), getD_F, if_neg (lt_irrefl _), if_pos rfl]
      congr 1
      apply List.map_congr_left
      intro i _
      split_ifs with h
      · rw [pref gs (F w g) i (by simp [F]; omega), getD_F, if_pos h]
      · rw [List.getD_eq_default _ _ (by omega)]
    | succ k =>
      simp only [List.foldl_cons, List.getElem_cons_succ]
      have h1 := ih (F w g) k (by simpa using hk)
      have hl : (F w g).length = w.length + 1 := by simp [F]
      rw [hl] at h1
      rw [show w.length + (k + 1) = w.length + 1 + k by omega, h1]

open PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

variable {n : Nat}

abbrev bits (n : Nat) := Fin n → Bool

def v (c : Circuit) (x : bits n) (i : Nat) := (c.wires (List.ofFn x)).getD i false

theorem inp (c : Circuit) (x : bits n) (i : Nat) (h : i < n) :
    v c x i = x ⟨i,h⟩ := by
  unfold v
  rw [wires_eq, pref _ _ _ (by simpa using h), List.getD_eq_getElem _ _ (by simpa using h)]
  simp only [List.getElem_ofFn]

theorem outOf (c : Circuit) (x : bits n) (i : Nat) (h : n + c.size ≤ i) :
    v c x i = false := by
  apply List.getD_eq_default
  simpa [wires_eq,len_foldl,Circuit.size] using h

def atG (c : Circuit) (j : Nat) := gateAt c j

def good (n : Nat) (g : Gate) : Prop :=
  (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2 ∧ ∀ i ∈ g.inputs, i < n

theorem at_eq (c : Circuit) {j : Nat} (h : j < c.size) : atG c j = c.gates[j]'h :=
  List.getD_eq_getElem _ _ h

theorem shape (c : Circuit) : IsAO2 n c ↔ ∀ j < c.size, good (n+j) (atG c j) := by
  constructor
  · rintro ⟨ao,back,len⟩ j hj
    exact ⟨ao _ (at_eq c hj ▸ List.getElem_mem hj), len _ (at_eq c hj ▸ List.getElem_mem hj), back j hj⟩
  · intro h
    refine ⟨?_,fun j hj => (h j hj).2.2,?_⟩
    · intro g hg
      obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
      simpa only [at_eq c hj] using (h j hj).1
    · intro g hg
      obtain ⟨j,hj,rfl⟩ := List.mem_iff_getElem.mp hg
      simpa only [at_eq c hj] using (h j hj).2.1

theorem at_value (c : Circuit) (ao : IsAO2 n c) (x : bits n) {j : Nat} (hj : j<c.size) :
    v c x (n+j) = (atG c j).op.eval ((atG c j).inputs.map (v c x)) := by
  have h := gateval c.gates (List.ofFn x) j hj
  simp only [List.length_ofFn, ← wires_eq, ← at_eq c hj] at h
  rw [show v c x (n+j) = _ from h]
  congr 1
  apply List.map_congr_left
  intro i hi
  simp [v, ((shape c).mp ao j hj).2.2 i hi]

lemma split_gates (gs : List Gate) (j : ℕ) (hj : j < gs.length) :
    ∃ (pre post : List Gate) (gj : Gate),
      gs = pre ++ gj :: post ∧ pre.length = j ∧ gs[j]'hj = gj := by
  refine ⟨gs.take j, gs.drop (j + 1), gs[j]'hj, ?_, by simp; omega, rfl⟩
  rw [List.cons_getElem_drop_succ, List.take_append_drop]

lemma gateAt_eq (C : Circuit) (k : ℕ) (hk : k < C.gates.length) : gateAt C k = C.gates[k] := by
  simp [gateAt, List.getD_eq_getElem?_getD, hk]

open PEqualNP.EdgeOwnership in
lemma coneFold_length (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) :
    (gs.foldl (coneStep n) cs).length = cs.length + gs.length := by
  induction gs generalizing cs with
  | nil => simp
  | cons g gs ih =>
    rw [List.foldl_cons, ih]
    simp [coneStep]
    omega

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_last (n : ℕ) (cs : List (List ℕ)) (g : Gate) :
    (coneStep n cs g).getD cs.length [] =
      (g.inputs.filter (fun w => decide (n ≤ w ∧ w < n + cs.length))).flatMap
        (fun w => (w - n) :: cs.getD (w - n) []) := by
  simp [coneStep, List.getD_eq_getElem?_getD]

open PEqualNP.EdgeOwnership in
lemma coneStep_getD_lt (n : ℕ) (cs : List (List ℕ)) (g : Gate) (m : ℕ) (hm : m < cs.length) :
    (coneStep n cs g).getD m [] = cs.getD m [] := by
  simp [coneStep, List.getD_eq_getElem?_getD, List.getElem?_append_left hm]

open PEqualNP.EdgeOwnership in
lemma coneFold_getD_lt (n : ℕ) (gs : List Gate) (cs : List (List ℕ)) (k : ℕ)
    (hk : k < cs.length) :
    (gs.foldl (coneStep n) cs).getD k [] = cs.getD k [] := by
  induction gs generalizing cs with
  | nil => rfl
  | cons g gs ih =>
    simp only [List.foldl_cons]
    rw [ih (coneStep n cs g) (by simp [coneStep]; omega)]
    exact coneStep_getD_lt n cs g k hk

open PEqualNP.EdgeOwnership in
lemma inCone_iff (n : ℕ) (C : Circuit) (i k : ℕ) (hk : k < C.gates.length) :
    InCone n C i k ↔ ∃ w ∈ (gateAt C k).inputs, n ≤ w ∧ w < n + k ∧
      (i = w - n ∨ InCone n C i (w - n)) := by
  obtain ⟨pre, post, gk, hgs, hpre_len, hgk⟩ := split_gates C.gates k hk
  have hga : gateAt C k = gk := by rw [gateAt_eq C k hk]; exact hgk
  rw [hga]
  have hc : cones n C = post.foldl (coneStep n) (coneStep n (pre.foldl (coneStep n) []) gk) := by
    simp only [cones]
    rw [hgs, List.foldl_append, List.foldl_cons]
  have hl0 : (pre.foldl (coneStep n) []).length = k := by
    rw [coneFold_length]; simp [hpre_len]
  have hl1 : (coneStep n (pre.foldl (coneStep n) []) gk).length = k + 1 := by
    simp [coneStep, hl0]
  have h1 : (cones n C).getD k [] =
      (gk.inputs.filter (fun w => decide (n ≤ w ∧ w < n + k))).flatMap
        (fun w => (w - n) :: (pre.foldl (coneStep n) []).getD (w - n) []) := by
    rw [hc, coneFold_getD_lt n post _ k (by omega)]
    have h := coneStep_getD_last n (pre.foldl (coneStep n) []) gk
    rw [hl0] at h
    exact h
  have h2 : ∀ m, m < k → (cones n C).getD m [] = (pre.foldl (coneStep n) []).getD m [] := by
    intro m hm
    rw [hc, coneFold_getD_lt n post _ m (by omega)]
    exact coneStep_getD_lt n _ gk m (by omega)
  unfold InCone
  rw [h1]
  simp only [List.mem_flatMap, List.mem_filter, decide_eq_true_eq, List.mem_cons]
  constructor
  · rintro ⟨w, ⟨hw, hn, hlt⟩, h⟩
    refine ⟨w, hw, hn, hlt, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [h2 (w - n) (by omega)]
      exact h
  · rintro ⟨w, hw, hn, hlt, h⟩
    refine ⟨w, ⟨hw, hn, hlt⟩, ?_⟩
    rcases h with h | h
    · exact Or.inl h
    · right
      rw [← h2 (w - n) (by omega)]
      exact h
open PEqualNP.EdgeOwnership

def direct (n : Nat) (c : Circuit) (i j : Fin c.size) : Prop := n + i.val ∈ (atG c j).inputs

theorem cone (c : Circuit) (ao : IsAO2 n c) (i j : Fin c.size) :
    InCone n c i j ↔ ∃ l : Fin c.size, direct n c l j ∧ (i = l ∨ InCone n c i l) := by
  rw [inCone_iff _ _ _ _ j.isLt]
  constructor
  · rintro ⟨w,hm,hw,hw',hh⟩
    let l : Fin c.size := ⟨w-n,by have := j.isLt; omega⟩
    refine ⟨l,?_,hh.imp (fun h => Fin.ext h) id⟩
    change n+(w-n) ∈ (atG c j).inputs
    rwa [Nat.add_sub_of_le hw]
  · rintro ⟨l,hm,hh⟩
    have h := ((shape c).mp ao j j.isLt).2.2 _ hm
    refine ⟨n+l.val,hm,by omega,h,?_⟩
    simpa only [Nat.add_sub_cancel_left] using hh.imp (fun e => congrArg Fin.val e) id

def ren {m : Nat} (n : Nat) (p : Equiv.Perm (Fin m)) (w : Nat) : Nat :=
  if w<n then w else if h : w-n<m then n+(p ⟨w-n,h⟩).val else w

@[simp] theorem ren_input {m : Nat} (p : Equiv.Perm (Fin m)) {w : Nat} (h : w<n) :
    ren n p w = w := by simp [ren,h]

@[simp] theorem ren_gate {m : Nat} (p : Equiv.Perm (Fin m)) (j : Fin m) :
    ren n p (n+j.val) = n+(p j).val := by simp [ren,j.isLt]

theorem invren {m : Nat} (p : Equiv.Perm (Fin m)) (w : Nat) : ren n p.symm (ren n p w) = w := by
  by_cases h : w<n
  · simp [h]
  by_cases bound : w<n+m
  · let j : Fin m := ⟨w-n,by omega⟩
    have e : w=n+j.val := by dsimp [j]; omega
    rw [e,ren_gate,ren_gate,p.symm_apply_apply]
  · have hx : ¬ w-n<m := by omega
    simp [ren,h,hx]

def mk (n : Nat) (c : Circuit) (p : Equiv.Perm (Fin c.size)) (j : Fin c.size) : Gate :=
  let g := atG c (p.symm j)
  ⟨g.op,g.inputs.map (ren n p)⟩

def permute (n : Nat) (c : Circuit) (p : Equiv.Perm (Fin c.size)) : Circuit :=
  ⟨List.ofFn (mk n c p),ren n p c.output⟩

@[simp] theorem card (c : Circuit) (p : Equiv.Perm (Fin c.size)) : (permute n c p).size = c.size := by
  exact List.length_ofFn

theorem gate (c : Circuit) (p : Equiv.Perm (Fin c.size)) (j : Fin c.size) :
    atG (permute n c p) (p j) = ⟨(atG c j).op,(atG c j).inputs.map (ren n p)⟩ := by
  rw [at_eq _ (by simpa only [card] using (p j).isLt)]
  simp only [permute,List.getElem_ofFn,mk,Fin.eta,p.symm_apply_apply]

def order (n : Nat) (c : Circuit) (p : Equiv.Perm (Fin c.size)) :=
  ∀ a b : Fin c.size, InCone n c a b → p a < p b

theorem newModel (c : Circuit) (p : Equiv.Perm (Fin c.size)) (ao : IsAO2 n c) (top : order n c p) :
    IsAO2 n (permute n c p) := by
  apply (shape _).mpr
  intro m hm
  rw [card] at hm
  let j := p.symm ⟨m,hm⟩
  have key : p j = ⟨m,hm⟩ := p.apply_symm_apply _
  have eq : m = (p j).val := (congrArg Fin.val key).symm
  rw [eq,gate]
  obtain ⟨op,len,back⟩ := (shape c).mp ao j j.isLt
  refine ⟨op,by simpa using len,?_⟩
  intro w hw
  obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hw
  by_cases embed : a<n
  · rw [ren_input _ embed]; omega
  · have := back a ha
    let l : Fin c.size := ⟨a-n,by have := j.isLt; omega⟩
    have w_eq : a=n+l.val := by dsimp [l]; omega
    have edge : direct n c l j := by unfold direct; rwa [← w_eq]
    have lt := top l j ((cone c ao l j).mpr ⟨l,edge,Or.inl rfl⟩)
    rw [w_eq,ren_gate]
    exact Nat.add_lt_add_left lt n

theorem wireEq (c : Circuit) (p : Equiv.Perm (Fin c.size)) (ao : IsAO2 n c)
    (top : order n c p) (x : bits n) (w : Nat) :
    v (permute n c p) x (ren n p w) = v c x w := by
  induction w using Nat.strong_induction_on with
  | ind w ih =>
    by_cases hw : w<n
    · rw [ren_input _ hw,inp _ _ _ hw,inp _ _ _ hw]
    by_cases hb : w<n+c.size
    · let j : Fin c.size := ⟨w-n,by omega⟩
      have eq : w=n+j.val := by dsimp [j]; omega
      rw [eq,ren_gate,at_value _ (newModel c p ao top) x (by simpa only [card] using (p j).isLt),
        at_value _ ao x j.isLt,gate]
      simp only [List.map_map]
      congr 1
      apply List.map_congr_left
      intro i hi
      have h := ((shape c).mp ao j j.isLt).2.2 _ hi
      exact ih i (by omega)
    · have h : ¬w-n<c.size := by omega
      rw [show ren n p w = w by simp [ren,hw,h], outOf _ _ _ (by rw [card]; omega),
        outOf _ _ _ (by omega)]

def idx (n : Nat) (c : Circuit) (p : Equiv.Perm (Fin c.size)) :
    Fin c.size ≃ Fin (permute n c p).size := p.trans (finCongr (card c p).symm)

theorem edgeEq (c : Circuit) (p : Equiv.Perm (Fin c.size)) (i j : Fin c.size) :
    direct n (permute n c p) (idx n c p i) (idx n c p j) ↔ direct n c i j := by
  change n+(p i).val ∈ (atG (permute n c p) (p j)).inputs ↔ _
  rw [gate]
  change n+(p i).val ∈ (atG c j).inputs.map (ren n p) ↔ _
  rw [← ren_gate p i,List.mem_map]
  constructor
  · rintro ⟨w,hw,h⟩
    have e := congrArg (ren n p.symm) h
    rw [invren,invren] at e
    unfold direct
    rwa [← e]
  · intro h
    exact ⟨_,h,rfl⟩

theorem coneEq (c : Circuit) (p : Equiv.Perm (Fin c.size)) (ao : IsAO2 n c) (top : order n c p)
    (i j : Fin c.size) :
    InCone n (permute n c p) (idx n c p i) (idx n c p j) ↔ InCone n c i j := by
  let q := idx n c p
  let d := permute n c p
  have go : ∀ m, ∀ jm : m<c.size, InCone n d (q i) (q ⟨m,jm⟩) ↔ InCone n c i m := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro jm
      let b : Fin c.size := ⟨m,jm⟩
      change InCone n d (q i) (q b) ↔ InCone n c i b
      rw [cone d (newModel c p ao top),cone c ao]
      constructor
      · rintro ⟨a,ha,hh⟩
        obtain ⟨l,rfl⟩ := q.surjective a
        have e := (edgeEq c p l b).mp ha
        have hlt := ((shape c).mp ao b jm).2.2 _ e
        have less : l.val<m := Nat.lt_of_add_lt_add_left hlt
        exact ⟨l,e,hh.imp (fun h => q.injective h) (ih l less l.isLt).mp⟩
      · rintro ⟨l,hl,hh⟩
        have hlt := ((shape c).mp ao b jm).2.2 _ hl
        have less : l.val<m := Nat.lt_of_add_lt_add_left hlt
        exact ⟨q l,(edgeEq c p l b).mpr hl,hh.imp (congrArg q) (ih l less l.isLt).mpr⟩
  exact go j j.isLt

end PEqualNP.Outside.L_meta_17613_aux

open PEqualNP.Outside.L_meta_17613_aux in
theorem PEqualNP.Outside.L_meta_17613 : ∀ (x1 : ℕ) (x2 : PEqualNP.CircuitLowerBounds.Circuit) (x3 : Equiv.Perm (Fin x2.size)), PEqualNP.TopForm.IsAO2 x1 x2 → (∀ (x5 x6 : Fin x2.size), PEqualNP.EdgeOwnership.InCone x1 x2 ↑x5 ↑x6 → x3 x5 < x3 x6) → ∃ (x6 : PEqualNP.CircuitLowerBounds.Circuit), x6.size = x2.size ∧ PEqualNP.TopForm.IsAO2 x1 x6 ∧ (∀ (x7 : Fin x1 → Bool), PEqualNP.MetaComplexity.circuitFun x1 x6 x7 = PEqualNP.MetaComplexity.circuitFun x1 x2 x7) ∧ (∀ (x7 : Fin x2.size), (PEqualNP.MetaComplexity.NestedCover.gateAt x6 ↑(x3 x7)).op = (PEqualNP.MetaComplexity.NestedCover.gateAt x2 ↑x7).op) ∧ (∀ (x7 : Fin x2.size) (x8 : Fin x1 → Bool), PEqualNP.EdgeOwnership.gateVal x1 x6 (↑(x3 x7)) x8 = PEqualNP.EdgeOwnership.gateVal x1 x2 (↑x7) x8) ∧ ∀ (x7 x8 : Fin x2.size), PEqualNP.EdgeOwnership.InCone x1 x6 ↑(x3 x7) ↑(x3 x8) ↔ PEqualNP.EdgeOwnership.InCone x1 x2 ↑x7 ↑x8 := by
  intro n c p ao top
  refine ⟨permute n c p,card c p,newModel c p ao top,fun x => wireEq c p ao top x _,?_,?_,coneEq c p ao top⟩
  · intro j
    change (atG _ _).op = (atG _ _).op
    rw [gate]
  · intro j x
    have h := wireEq c p ao top x (n+j.val)
    rwa [ren_gate] at h
