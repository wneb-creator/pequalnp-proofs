import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1031.FreshCore.Groups

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

def run (gs : List Gate) (x : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) x

theorem run_snoc (gs : List Gate) (g : Gate) (x : List Bool) :
    run (gs ++ [g]) x = run gs x ++ [g.op.eval (g.inputs.map fun i => (run gs x).getD i false)] := by
  simp [run, List.foldl_append]

theorem run_length (gs : List Gate) (x : List Bool) : (run gs x).length = x.length + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [run]
  | append_singleton gs g ih => rw [run_snoc]; simp [ih]; omega

theorem getD_lt (l : List Bool) (b : Bool) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t false = l.getD t false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at (l : List Bool) (b : Bool) : (l ++ [b]).getD l.length false = b := by
  simp [List.getD_eq_getElem?_getD]

theorem getD_ltz {α : Type} (z : α) (l : List α) (b : α) (t : ℕ) (h : t < l.length) :
    (l ++ [b]).getD t z = l.getD t z := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_at' {α : Type} (z : α) (l : List α) (b : α) : (l ++ [b]).getD l.length z = b := by
  simp [List.getD_eq_getElem?_getD]

theorem run_prefix (gs hs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length + gs.length) :
    (run (gs ++ hs) x).getD i false = (run gs x).getD i false := by
  induction hs using List.reverseRecOn with
  | nil => simp
  | append_singleton hs g ih =>
    rw [← List.append_assoc, run_snoc, getD_ltz false _ _ _ (by
      rw [run_length, List.length_append]; omega), ih]

theorem run_input (gs : List Gate) (x : List Bool) (i : ℕ) (hi : i < x.length) :
    (run gs x).getD i false = x.getD i false := by
  have := run_prefix [] gs x i (by simpa using hi)
  simpa [run] using this

theorem run_gate (gs : List Gate) (x : List Bool) : ∀ (j : ℕ) (hj : j < gs.length),
    (run gs x).getD (x.length + j) false = gs[j].op.eval (gs[j].inputs.map fun i =>
      if i < x.length + j then (run gs x).getD i false else false) := by
  induction gs using List.reverseRecOn with
  | nil => intro j hj; simp at hj
  | append_singleton gs g ih =>
    intro j hj
    have hlen : (run gs x).length = x.length + gs.length := run_length gs x
    have same : ∀ (k : ℕ), k ≤ gs.length → ∀ l : List ℕ,
        (l.map fun i => if i < x.length + k then (run (gs ++ [g]) x).getD i false else false) =
        l.map fun i => if i < x.length + k then (run gs x).getD i false else false := by
      intro k hk l
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · exact run_prefix gs [g] x i (by omega)
      · rfl
    rcases Nat.lt_or_ge j gs.length with h | h
    · rw [List.getElem_append_left h, same j (by omega), run_prefix gs [g] x _ (by omega)]
      exact ih j h
    · have hjj : j = gs.length := by simp at hj; omega
      subst hjj
      have hg : (gs ++ [g])[gs.length] = g := by simp
      rw [hg, same _ le_rfl, run_snoc, ← hlen, getD_at']
      congr 1
      refine List.map_congr_left fun i _ => ?_
      split_ifs with h
      · rfl
      · exact List.getD_eq_default _ _ (by omega)



def Ok (n : ℕ) (gs : List Gate) : Prop :=
  ∀ j (hj : j < gs.length), ∃ o s t, gs[j] = ⟨o, [s, t]⟩ ∧ (o = GateOp.and ∨ o = GateOp.or) ∧
    s < n + j ∧ t < n + j

theorem ok_snoc {n : ℕ} {gs : List Gate} (h : Ok n gs) {o : GateOp} {s t : ℕ}
    (ho : o = GateOp.and ∨ o = GateOp.or) (hs : s < n + gs.length) (ht : t < n + gs.length) :
    Ok n (gs ++ [⟨o, [s, t]⟩]) := by
  intro j hj
  by_cases hlt : j < gs.length
  · rw [List.getElem_append_left hlt]; exact h j hlt
  · have : j = gs.length := by simp at hj; omega
    subst this
    exact ⟨o, s, t, by simp, ho, hs, ht⟩

open Classical in
noncomputable def dc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) : ℕ :=
  ((Finset.range gs.length).filter fun i => (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧
    ∃ x : Fin n → Bool, (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false).card

open Classical in
theorem dc_snoc (n : ℕ) (F : (Fin n → Bool) → Bool) (gs : List Gate) (g : Gate) :
    dc n F (gs ++ [g]) ≤ dc n F gs + if g.op = GateOp.and ∧
      ∃ x : Fin n → Bool, (run (gs ++ [g]) (List.ofFn x)).getD (n + gs.length) false = true ∧
        F x = false then 1 else 0 := by
  unfold dc
  rw [List.length_append, List.length_singleton, Finset.range_add_one, Finset.filter_insert]
  have e : (gs ++ [g]).getD gs.length ⟨GateOp.or, []⟩ = g := by
    simp [List.getD_eq_getElem?_getD]
  rw [e]
  have h1 : ((Finset.range gs.length).filter fun i =>
      ((gs ++ [g]).getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run (gs ++ [g]) (List.ofFn x)).getD (n + i) false = true ∧ F x = false) =
      (Finset.range gs.length).filter fun i =>
      (gs.getD i ⟨GateOp.or, []⟩).op = GateOp.and ∧ ∃ x : Fin n → Bool,
        (run gs (List.ofFn x)).getD (n + i) false = true ∧ F x = false := by
    refine Finset.filter_congr fun i hi => ?_
    have hi' := Finset.mem_range.1 hi
    rw [getD_ltz _ _ _ _ hi']
    refine and_congr_right fun _ => exists_congr fun x => ?_
    rw [run_prefix gs [g] _ _ (by simp; omega)]
  rw [h1]
  split_ifs with h
  · exact (Finset.card_insert_le _ _)
  · simp

def ov (gs : List Gate) (x : List Bool) (o : Option ℕ) : Bool :=
  match o with
  | none => false
  | some w => (run gs x).getD w false

theorem ov_ext (gs hs : List Gate) (x : List Bool) (o : Option ℕ)
    (h : ∀ w, o = some w → w < x.length + gs.length) : ov (gs ++ hs) x o = ov gs x o := by
  cases o with
  | none => rfl
  | some w => exact run_prefix gs hs x w (h w rfl)

theorem ov_new (gs : List Gate) (n : ℕ) (x : List Bool) (hx : x.length = n) (o : GateOp) (s t : ℕ)
    (_hs : s < n + gs.length) (_ht : t < n + gs.length) :
    ov (gs ++ [⟨o, [s, t]⟩]) x (some (n + gs.length)) =
      o.eval [(run gs x).getD s false, (run gs x).getD t false] := by
  unfold ov
  simp only
  rw [run_snoc]
  have : n + gs.length = (run gs x).length := by rw [run_length, hx]
  rw [this, getD_at]
  rfl

lemma append_raw {n : ℕ} (x : Fin n → Bool) (v : Fin n) :
    (List.ofFn x).getD v.val false = x v := by
  simp [List.getD_eq_getElem?_getD]

lemma append_literal {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (v : Fin n) :
    ov gs (List.ofFn x) (some v.val) = x v := by
  change (run gs (List.ofFn x)).getD v.val false = x v
  rw [run_input _ _ _ (by simp), append_raw]

def atWire {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : ℕ) : Bool :=
  (run gs (List.ofFn x)).getD w false

lemma atWire_prior {n : ℕ} (gs tail : List Gate) (x : Fin n → Bool) {w : ℕ}
    (hw : w < n + gs.length) : atWire (gs++tail) x w = atWire gs x w :=
  run_prefix gs tail _ w (by simpa using hw)

lemma atWire_raw {n : ℕ} (gs : List Gate) (x : Fin n → Bool) (w : Fin n) :
    atWire gs x w = x w := append_literal gs x w

lemma append_combine {n : ℕ} (F : (Fin n → Bool) → Bool) (gs : List Gate) (hgs : Ok n gs)
    (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or) {u v : ℕ}
    (hu : u < n+gs.length) (hv : v < n+gs.length)
    (hsafe : op = GateOp.and → ∀ x, op.eval [atWire gs x u, atWire gs x v] = true → F x = true) :
    ∃ (g : Gate) (w : ℕ), Ok n (gs++[g]) ∧ dc n F (gs++[g]) ≤ dc n F gs ∧
      w < n+(gs++[g]).length ∧
      ∀ x : Fin n → Bool, atWire (gs++[g]) x w = op.eval [atWire gs x u,atWire gs x v] := by
  classical
  let g : Gate := ⟨op,[u,v]⟩
  have he (x : Fin n → Bool) : atWire (gs++[g]) x (n+gs.length) =
      op.eval [atWire gs x u,atWire gs x v] :=
    ov_new gs n _ (by simp) op u v hu hv
  refine ⟨g,n+gs.length,ok_snoc hgs hop hu hv,?_,by simp,he⟩
  have hd := dc_snoc n F gs g
  rw [ite_eq_right (by
    rintro ⟨hand,x,hx,hf⟩
    exact Bool.noConfusion ((hsafe hand x ((he x).symm.trans hx)).symm.trans hf))] at hd
  simpa using hd

lemma any_mem_congr {α : Type*} (l : List α) {p q : α → Bool} (h : ∀ a ∈ l, p a = q a) :
    l.any p = l.any q := by
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true]
  exact exists_congr fun a => and_congr_right fun ha => by rw [h a ha]

lemma append_wires_or {n : ℕ} (F : (Fin n → Bool) → Bool) (tail : List ℕ)
    (gs : List Gate) (hgs : Ok n gs) (u : ℕ) (hu : u < n+gs.length)
    (hvalid : ∀ v ∈ tail, v < n+gs.length) :
    ∃ (more : List Gate) (w : ℕ), Ok n (gs++more) ∧ more.length = tail.length ∧
      dc n F (gs++more) ≤ dc n F gs ∧ w < n+(gs++more).length ∧
      ∀ x : Fin n → Bool, atWire (gs++more) x w =
        (atWire gs x u || tail.any (atWire gs x)) := by
  induction tail generalizing gs u with
  | nil =>
    exact ⟨[],u,by simpa using hgs,rfl,by simp,by simpa using hu,by simp⟩
  | cons v vs ih =>
    have hv := hvalid v (by simp)
    obtain ⟨g,w,hok,hdc,hw,he⟩ := append_combine F gs hgs GateOp.or (Or.inr rfl) hu hv
      (by simp)
    have hv' (z : ℕ) (hz : z ∈ vs) : z < n+(gs++[g]).length := by
      have := hvalid z (List.mem_cons_of_mem _ hz)
      simp
      omega
    obtain ⟨more,z,hok',hlen,hdc',hz,he'⟩ := ih (gs++[g]) hok w hw hv'
    refine ⟨g::more,z,by simpa using hok',by simpa using hlen,?_,by simpa using hz,?_⟩
    · simpa using hdc'.trans hdc
    · intro x
      have hlist : vs.any (atWire (gs++[g]) x) = vs.any (atWire gs x) := by
        apply any_mem_congr
        intro a ha
        exact atWire_prior gs [g] x (hvalid a (List.mem_cons_of_mem _ ha))
      have hh := he' x
      rw [hlist,he x] at hh
      simpa [GateOp.eval, Bool.or_assoc] using hh

def groupBlock {n : ℕ} (gs : List Gate) (b c : Fin n) (x : Fin n → Bool) (p : ℕ × ℕ) : Bool :=
  (atWire gs x p.1 && atWire gs x p.2) && (x b || x c)

lemma block_split (A B b c : Bool) (hA : c = true → A = true) (hB : b = true → B = true) :
    ((A && B) && (b || c)) = ((b && A) || (c && B)) := by
  cases A <;> cases B <;> cases b <;> cases c <;> simp_all

lemma group_split {n : ℕ} (gs : List Gate) (b c : Fin n) (p : List (ℕ × ℕ))
    (hc : ∀ t ∈ p, ∀ x, x c=true → atWire gs x t.1=true)
    (hb : ∀ t ∈ p, ∀ x, x b=true → atWire gs x t.2=true) (x : Fin n → Bool) :
    p.any (groupBlock gs b c x) =
      ((x b && p.any (fun t => atWire gs x t.1)) || (x c && p.any (fun t => atWire gs x t.2))) := by
  rw [Bool.eq_iff_iff]
  simp only [List.any_eq_true,Bool.or_eq_true,Bool.and_eq_true]
  constructor
  · rintro ⟨t,ht,h⟩
    rw [groupBlock,block_split _ _ _ _ (hc t ht x) (hb t ht x)] at h
    simp only [Bool.or_eq_true,Bool.and_eq_true] at h
    rcases h with ⟨h,h'⟩ | ⟨h,h'⟩
    · exact Or.inl ⟨h,t,ht,h'⟩
    · exact Or.inr ⟨h,t,ht,h'⟩
  · rintro (⟨h,t,ht,h'⟩ | ⟨h,t,ht,h'⟩)
    · exact ⟨t,ht,by simp [groupBlock,h,h',hb t ht x h]⟩
    · exact ⟨t,ht,by simp [groupBlock,h,h',hc t ht x h]⟩

lemma append_two_stars {n : ℕ} (F : (Fin n → Bool) → Bool) (gs : List Gate) (hgs : Ok n gs)
    (b c : Fin n) (u v : ℕ) (hu : u < n+gs.length) (hv : v < n+gs.length)
    (hs : ∀ x : Fin n → Bool,
      ((x b && atWire gs x u) || (x c && atWire gs x v)) = true → F x=true) :
    ∃ (more : List Gate) (w : ℕ), Ok n (gs++more) ∧ more.length = 3 ∧
      dc n F (gs++more) ≤ dc n F gs ∧ w < n+(gs++more).length ∧
      ∀ x : Fin n → Bool, atWire (gs++more) x w =
        ((x b && atWire gs x u) || (x c && atWire gs x v)) := by
  have hb : b.val < n+gs.length := by have := b.isLt; omega
  obtain ⟨g,z,hg,hd,hz,he⟩ := append_combine F gs hgs GateOp.and (Or.inl rfl) hb hu (by
    intro _ x hx
    apply hs
    have hbx : (x b && atWire gs x u) = true := by simpa [GateOp.eval,atWire_raw] using hx
    simp [hbx])
  have hc : c.val < n+(gs++[g]).length := by have := c.isLt; omega
  have hv' : v < n+(gs++[g]).length := by simp; omega
  obtain ⟨g',z',hg',hd',hz',he'⟩ := append_combine F (gs++[g]) hg GateOp.and (Or.inl rfl)
    hc hv' (by
      intro _ x hx
      apply hs
      have hcx : (x c && atWire gs x v) = true := by
        simpa [GateOp.eval,atWire_raw,atWire_prior gs [g] x hv] using hx
      simp [hcx])
  have hz'' : z < n+((gs++[g])++[g']).length := by simp at hz ⊢; omega
  obtain ⟨g'',w,hg'',hd'',hw,he''⟩ := append_combine F ((gs++[g])++[g']) hg' GateOp.or
    (Or.inr rfl) hz'' hz' (by simp)
  refine ⟨[g,g',g''],w,by simpa using hg'',rfl,by simpa using hd''.trans (hd'.trans hd),
    by simpa using hw,?_⟩
  intro x
  have h := he'' x
  rw [atWire_prior (gs++[g]) [g'] x hz,he x,he' x,atWire_prior gs [g] x hv] at h
  simpa [GateOp.eval,atWire_raw] using h

lemma collect_two_stars {n : ℕ} (F : (Fin n → Bool) → Bool) (gs : List Gate) (hgs : Ok n gs)
    (b c : Fin n) (p : ℕ × ℕ) (ps : List (ℕ × ℕ))
    (hbnd : ∀ t ∈ p::ps, t.1 < n+gs.length ∧ t.2 < n+gs.length)
    (hsound : ∀ x : Fin n → Bool, ((x b && (p::ps).any (fun t => atWire gs x t.1)) ||
      (x c && (p::ps).any (fun t => atWire gs x t.2))) = true → F x = true) :
    ∃ (more : List Gate) (w : ℕ), Ok n (gs++more) ∧ more.length = 2*(p::ps).length+1 ∧
      dc n F (gs++more) ≤ dc n F gs ∧ w < n+(gs++more).length ∧
      ∀ x : Fin n → Bool, atWire (gs++more) x w =
        ((x b && (p::ps).any (fun t => atWire gs x t.1)) || (x c && (p::ps).any (fun t => atWire gs x t.2))) := by

  have hp := hbnd p (by simp)
  have ht (t) (h : t ∈ ps) := hbnd t (List.mem_cons_of_mem _ h)
  obtain ⟨h,u,ok,hlen,hd,hu,he⟩ := append_wires_or F (ps.map Prod.fst) gs hgs p.1 hp.1 (by
    intro w hw
    obtain ⟨t,hm,rfl⟩ := List.mem_map.mp hw
    exact (ht t hm).1)
  have hp' : p.2 < n+(gs++h).length := by simp; omega
  obtain ⟨h',v,ok',hlen',hd',hv,he'⟩ := append_wires_or F (ps.map Prod.snd) (gs++h) ok p.2 hp' (by
    intro w hw
    obtain ⟨t,hm,rfl⟩ := List.mem_map.mp hw
    have := (ht t hm).2
    simp
    omega)
  let H := (gs++h)++h'
  have hu' : u < n+H.length := by dsimp [H]; simp at hu ⊢; omega
  have hleft (x : Fin n → Bool) : atWire H x u = (p::ps).any (fun t => atWire gs x t.1) := by
    rw [show atWire H x u = _ from atWire_prior (gs++h) h' x hu, he x]
    simp [List.any_map,Function.comp_def]
  have hright (x : Fin n → Bool) : atWire H x v = (p::ps).any (fun t => atWire gs x t.2) := by
    rw [show atWire H x v = _ from he' x, atWire_prior gs h x hp.2]
    simp only [List.any_map, Function.comp_def, List.any_cons]
    congr 1
    apply any_mem_congr
    intro t hm
    exact atWire_prior gs h x (ht t hm).2
  have hs (x : Fin n → Bool) :
      ((x b && atWire H x u) || (x c && atWire H x v)) =
        ((x b && (p::ps).any (fun t => atWire gs x t.1)) || (x c && (p::ps).any (fun t => atWire gs x t.2))) := by
    rw [hleft,hright]
  obtain ⟨h'',w,ok'',hlen'',hd'',hw,he''⟩ := append_two_stars F H ok' b c u v hu' hv
    (fun x hx => hsound x ((hs x).symm.trans hx))
  refine ⟨h++h'++h'',w,?_,?_,?_,?_,?_⟩
  · simpa only [H,List.append_assoc] using ok''
  · simp only [List.length_append,List.length_map,List.length_cons] at *
    omega
  · simpa only [H,List.append_assoc] using hd''.trans (hd'.trans hd)
  · simpa only [H,List.append_assoc] using hw
  · intro x
    simpa only [H,List.append_assoc] using (he'' x).trans (hs x)

lemma common_bridge_group {n : ℕ} (F : (Fin n → Bool) → Bool) (gs : List Gate) (hgs : Ok n gs)
    (b c : Fin n) (p : ℕ × ℕ) (ps : List (ℕ × ℕ))
    (hbnd : ∀ t ∈ p::ps, t.1 < n+gs.length ∧ t.2 < n+gs.length)
    (hc : ∀ t ∈ p::ps, ∀ x, x c=true → atWire gs x t.1=true)
    (hb : ∀ t ∈ p::ps, ∀ x, x b=true → atWire gs x t.2=true)
    (hsound : ∀ x, (p::ps).any (groupBlock gs b c x) = true → F x = true) :
    ∃ (more : List Gate) (w : ℕ), Ok n (gs++more) ∧ more.length = 2*(p::ps).length+1 ∧
      dc n F (gs++more) ≤ dc n F gs ∧ w < n+(gs++more).length ∧
      ∀ x : Fin n → Bool, atWire (gs++more) x w = (p::ps).any (groupBlock gs b c x) := by

  have h (x : Fin n → Bool) := group_split gs b c (p::ps) hc hb x
  obtain ⟨more,w,hok,hlen,hd,hw,he⟩ := collect_two_stars F gs hgs b c p ps hbnd
    (fun x hx => hsound x ((h x).trans hx))
  exact ⟨more,w,hok,hlen,hd,hw,fun x => (he x).trans (h x).symm⟩

def pairPart {n : ℕ} (gs : List Gate) (b c : Fin n) (x : Fin n → Bool) (t : ℕ × ℕ) : Bool :=
  (x b && atWire gs x t.1) || (x c && atWire gs x t.2)

lemma parts_split {n : ℕ} (gs : List Gate) (b c : Fin n) (p : List (ℕ × ℕ)) (x : Fin n → Bool) :
    p.any (pairPart gs b c x) =
      ((x b && p.any (fun t => atWire gs x t.1)) || (x c && p.any (fun t => atWire gs x t.2))) := by
  rw [Bool.eq_iff_iff]
  simp only [pairPart, List.any_eq_true,Bool.or_eq_true,Bool.and_eq_true]
  aesop

lemma collect_on_tests {n : ℕ} (F : (Fin n → Bool) → Bool) (gs : List Gate) (hgs : Ok n gs)
    (b c : Fin n) (p : ℕ × ℕ) (ps : List (ℕ × ℕ))
    (hbnd : ∀ t ∈ p::ps, t.1 < n+gs.length ∧ t.2 < n+gs.length)
    (test : (Fin n → Bool) → Prop) (contribution : (Fin n → Bool) → (ℕ × ℕ) → Bool)
    (hcover : ∀ t ∈ p::ps, ∀ x, test x → contribution x t = pairPart gs b c x t)
    (hsafe : ∀ t ∈ p::ps, ∀ x, pairPart gs b c x t = true → F x=true) :
    ∃ (more : List Gate) (w : ℕ), Ok n (gs++more) ∧ more.length = 2*(p::ps).length+1 ∧
      dc n F (gs++more) ≤ dc n F gs ∧ w < n+(gs++more).length ∧
      (∀ x : Fin n → Bool, atWire (gs++more) x w = true → F x = true) ∧
      ∀ x : Fin n → Bool, test x → atWire (gs++more) x w = (p::ps).any (contribution x) := by
  have hs (x) (h : (p::ps).any (pairPart gs b c x) = true) : F x=true := by
    obtain ⟨t,ht,he⟩ := List.any_eq_true.mp h
    exact hsafe t ht x he
  obtain ⟨more,w,hok,hlen,hd,hw,he⟩ := collect_two_stars F gs hgs b c p ps hbnd
    (fun x hx => hs x ((parts_split gs b c (p::ps) x).trans hx))
  have heq (x) := (he x).trans (parts_split gs b c (p::ps) x).symm
  refine ⟨more,w,hok,hlen,hd,hw,fun x hx => hs x ((heq x).symm.trans hx),?_⟩
  intro x ht
  rw [heq]
  exact any_mem_congr _ (fun t h => (hcover t h x ht).symm)

lemma collect_on_tests_or {n : ℕ} (F : (Fin n → Bool) → Bool) (gs : List Gate) (hgs : Ok n gs)
    (b c : Fin n) (p : ℕ × ℕ) (ps : List (ℕ × ℕ))
    (hbnd : ∀ t ∈ p::ps, t.1 < n+gs.length ∧ t.2 < n+gs.length)
    (test : (Fin n → Bool) → Prop) (contribution : (Fin n → Bool) → (ℕ × ℕ) → Bool)
    (hcover : ∀ t ∈ p::ps, ∀ x, test x → contribution x t = pairPart gs b c x t)
    (hsafe : ∀ t ∈ p::ps, ∀ x, pairPart gs b c x t = true → F x=true)
    (old : ℕ) (ho : old < n+gs.length) (hold : ∀ x, atWire gs x old=true → F x=true) :
    ∃ (more : List Gate) (w : ℕ), Ok n (gs++more) ∧ more.length = 2*(p::ps).length+2 ∧
      dc n F (gs++more) ≤ dc n F gs ∧ w < n+(gs++more).length ∧
      (∀ x : Fin n → Bool, atWire (gs++more) x w = true → F x = true) ∧
      ∀ x : Fin n → Bool, test x → atWire (gs++more) x w =
        (atWire gs x old || (p::ps).any (contribution x)) := by
  obtain ⟨h,u,hok,hlen,hd,hu,hguard,he⟩ := collect_on_tests F gs hgs b c p ps hbnd
    test contribution hcover hsafe
  have ho' : old < n+(gs++h).length := by simp; omega
  obtain ⟨g,w,hok',hd',hw,he'⟩ := append_combine F (gs++h) hok GateOp.or (Or.inr rfl)
    ho' hu (by simp)
  have hval (x : Fin n → Bool) : atWire ((gs++h)++[g]) x w = (atWire gs x old || atWire (gs++h) x u) := by
    simpa [GateOp.eval, atWire_prior gs h x ho] using he' x
  refine ⟨h++[g],w,by simpa only [List.append_assoc] using hok',?_,
    by simpa only [List.append_assoc] using hd'.trans hd,
    by simpa only [List.append_assoc] using hw,?_,?_⟩
  · simp only [List.length_append,List.length_singleton,hlen]
  · intro x hx
    rw [← List.append_assoc,hval] at hx
    simp only [Bool.or_eq_true] at hx
    rcases hx with hx | hx
    · exact hold x hx
    · exact hguard x hx
  · intro x hx
    rw [← List.append_assoc,hval,he x hx]

lemma bridge_group_releasable {k p q : ℕ} (hk : 0 < k) (hslots : 2 ≤ p+q) :
    2*k+1 ≤ 2*k-1+p+q := by omega

lemma bridge_group_shared_middle {k : ℕ} (hk : 2 ≤ k) : 2*k+1 ≤ 3*k-1 := by omega

lemma bridge_group_private_middle {k : ℕ} (hk : 0 < k) : 2*k+1 ≤ 3*k := by omega

end PEqualNP.Outside.L_meta_1031.FreshCore.Groups
