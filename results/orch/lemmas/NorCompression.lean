import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592.NorCompression
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def ren (i : Nat) : Nat := if i < 10 then i else i - 1

def gate (g : Gate) : Gate := ⟨g.op,g.inputs.map ren⟩

def old (i j : Fin 10) (gs : List Gate) (out : Nat) : Circuit :=
  ⟨[⟨.not,[i.val]⟩,⟨.not,[j.val]⟩,⟨.and,[10,11]⟩] ++ gs,out⟩

def new (i j : Fin 10) (gs : List Gate) (out : Nat) : Circuit :=
  ⟨[⟨.or,[i.val,j.val]⟩,⟨.not,[10]⟩] ++ gs.map gate,ren out⟩

lemma ren_low (i : Nat) (hi : i < 10) : ren i = i := by simp [ren,hi]
lemma ren_high (i : Nat) (hi : 10 ≤ i) : ren i = i-1 := by simp [ren,Nat.not_lt.mpr hi]

lemma relation_append (a b : List Bool) (v : Bool) (hb : 12 ≤ b.length)
    (hlen : a.length = b.length + 1)
    (rel : ∀ t, t ≠ 10 → t ≠ 11 → b.getD (ren t) false = a.getD t false) :
    ∀ t, t ≠ 10 → t ≠ 11 →
      (b ++ [v]).getD (ren t) false = (a ++ [v]).getD t false := by
  intro t ht10 ht11
  rcases lt_trichotomy t a.length with ht | rfl | ht
  · have hr : ren t < b.length := by
      unfold ren
      split_ifs <;> omega
    rw [List.getD_append _ _ _ _ hr,List.getD_append _ _ _ _ ht]
    exact rel t ht10 ht11
  · have hr : ren a.length = b.length := by rw [ren_high _ (by omega)]; omega
    rw [hr]
    simp [List.getD_eq_getElem?_getD]
  · have hr : b.length < ren t := by
      rw [ren_high _ (by omega)]
      omega
    rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]

def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun t => w.getD t false)]

lemma fold_relation (gs : List Gate)
    (unused : ∀ g ∈ gs, ∀ t ∈ g.inputs, t ≠ 10 ∧ t ≠ 11)
    (a b : List Bool) (hb : 12 ≤ b.length) (hlen : a.length = b.length+1)
    (rel : ∀ t, t ≠ 10 → t ≠ 11 → b.getD (ren t) false = a.getD t false) :
    ∀ t, t ≠ 10 → t ≠ 11 →
      ((gs.map gate).foldl step b).getD (ren t) false =
      (gs.foldl step a).getD t false := by
  induction gs generalizing a b with
  | nil => exact rel
  | cons g gs ih =>
    simp only [List.map_cons,List.foldl_cons]
    have hv : (gate g).op.eval ((gate g).inputs.map fun t => b.getD t false) =
        g.op.eval (g.inputs.map fun t => a.getD t false) := by
      simp only [gate,List.map_map]
      congr 1
      apply List.map_congr_left
      intro t ht
      obtain ⟨h10,h11⟩ := unused g (by simp) t ht
      exact rel t h10 h11
    apply ih (fun g hg => unused g (List.mem_cons_of_mem _ hg))
    · simp [step]
      omega
    · simp [step,hlen]
    · simp only [step,hv]
      exact relation_append a b _ hb hlen rel

lemma initial_relation (i j : Fin 10) (x : Fin 10 → Bool) :
    ∀ t, t ≠ 10 → t ≠ 11 →
      (List.ofFn x ++ [x i || x j,!(x i || x j)]).getD (ren t) false =
      (List.ofFn x ++ [!x i,!x j,!x i && !x j]).getD t false := by
  intro t h10 h11
  by_cases ht : t < 10
  · rw [ren_low _ ht,List.getD_append _ _ _ _ (by simpa using ht),
      List.getD_append _ _ _ _ (by simpa using ht)]
  · by_cases he : t = 12
    · subst t
      simp [ren,List.getD_eq_getElem?_getD,Bool.not_or]
    · have ht' : 13 ≤ t := by omega
      have hr : 12 ≤ ren t := by rw [ren_high _ (by omega)];omega
      rw [List.getD_eq_default _ _ (by simp;omega),List.getD_eq_default _ _ (by simp;omega)]

lemma read_initial (x : Fin 10 → Bool) (i : Fin 10) :
    (List.ofFn x).getD i.val false = x i := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp

lemma read_low (x : Fin 10 → Bool) (xs : List Bool) (i : Fin 10) :
    (List.ofFn x ++ xs).getD i.val false = x i := by
  rw [List.getD_append _ _ _ _ (by simp)]
  exact read_initial x i

lemma read_extra (x : Fin 10 → Bool) (xs : List Bool) (k : Nat) :
    (List.ofFn x ++ xs).getD (10+k) false = xs.getD k false := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by simp)]
  simp

lemma old_prefix (i j : Fin 10) (x : Fin 10 → Bool) :
    [⟨.not,[i.val]⟩,⟨.not,[j.val]⟩,⟨.and,[10,11]⟩].foldl step (List.ofFn x) =
      List.ofFn x ++ [!x i,!x j,!x i && !x j] := by
  simp only [List.foldl_cons,List.foldl_nil,step,List.map_cons,List.map_nil,GateOp.eval,
    read_initial,read_low,List.append_assoc]
  rw [read_extra x _ 0,read_extra x _ 1]
  simp

lemma new_prefix (i j : Fin 10) (x : Fin 10 → Bool) :
    [⟨.or,[i.val,j.val]⟩,⟨.not,[10]⟩].foldl step (List.ofFn x) =
      List.ofFn x ++ [x i || x j,!(x i || x j)] := by
  simp only [List.foldl_cons,List.foldl_nil,step,List.map_cons,List.map_nil,GateOp.eval,
    read_initial,List.append_assoc]
  rw [read_extra x _ 0]
  simp

lemma eval_equal (i j : Fin 10) (gs : List Gate) (out : Nat)
    (unused : ∀ g ∈ gs, ∀ t ∈ g.inputs, t ≠ 10 ∧ t ≠ 11)
    (hout10 : out ≠ 10) (hout11 : out ≠ 11) (x : Fin 10 → Bool) :
    (new i j gs out).eval (List.ofFn x) = (old i j gs out).eval (List.ofFn x) := by
  have h := fold_relation gs unused
    (List.ofFn x ++ [!x i,!x j,!x i && !x j])
    (List.ofFn x ++ [x i || x j,!(x i || x j)])
    (by simp) (by simp) (initial_relation i j x) out hout10 hout11
  change ((([⟨.or,[i.val,j.val]⟩,⟨.not,[10]⟩] : List Gate) ++ gs.map gate).foldl step (List.ofFn x)).getD
      (ren out) false =
    ((([⟨.not,[i.val]⟩,⟨.not,[j.val]⟩,⟨.and,[10,11]⟩] : List Gate) ++ gs).foldl step (List.ofFn x)).getD out false
  rw [List.foldl_append,List.foldl_append,new_prefix,old_prefix]
  exact h

lemma size_equal (i j : Fin 10) (gs : List Gate) (out : Nat) :
    (new i j gs out).size + 1 = (old i j gs out).size := by
  simp [new,old,Circuit.size]

lemma notCount_equal (i j : Fin 10) (gs : List Gate) (out : Nat) :
    PEqualNP.NotBracket.notCount (new i j gs out) + 1 =
      PEqualNP.NotBracket.notCount (old i j gs out) := by
  classical
  simp only [new,old,PEqualNP.NotBracket.notCount,List.filter_append,List.filter_map]
  simp [Function.comp_def,gate]
  apply congrArg List.length
  apply List.filter_congr
  intro g hg
  rcases g with ⟨op,inputs⟩
  cases op <;> rfl

lemma fanInTwo (i j : Fin 10) (gs : List Gate) (out : Nat)
    (hf : FanInTwo (old i j gs out)) : FanInTwo (new i j gs out) := by
  intro g hg
  simp only [new,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hg
  rcases hg with (rfl | rfl) | hm
  · simp
  · simp
  · obtain ⟨g,hg,rfl⟩ := List.mem_map.mp hm
    have h := hf g (by simp [old,hg])
    simpa [gate] using h

end PEqualNP.Outside.L_meta_2592.NorCompression
