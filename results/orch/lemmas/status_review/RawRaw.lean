import Mathlib.Data.Fin.VecNotation
import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_1890.RawRaw

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def edge (x : Fin 10 → Bool) : Bool :=
  x 0 && x 1 || x 1 && x 2 || x 2 && x 3 || x 3 && x 4 || x 4 && x 0 ||
  x 0 && x 5 || x 1 && x 6 || x 2 && x 7 || x 3 && x 8 || x 4 && x 9 ||
  x 5 && x 7 || x 7 && x 9 || x 9 && x 6 || x 6 && x 8 || x 8 && x 5

def wiresFrom (gs : List Gate) (w : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w

theorem wires_eq (C : Circuit) (x : List Bool) : C.wires x = wiresFrom C.gates x := rfl

theorem wiresFrom_append (gs gs' : List Gate) (w : List Bool) :
    wiresFrom (gs ++ gs') w = wiresFrom gs' (wiresFrom gs w) := by
  simp [wiresFrom, List.foldl_append]

theorem wiresFrom_prefix (gs : List Gate) : ∀ w : List Bool,
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

theorem length_wiresFrom (gs : List Gate) (w : List Bool) :
    (wiresFrom gs w).length = w.length + gs.length := by
  obtain ⟨t, ht, hl⟩ := wiresFrom_prefix gs w
  rw [ht]; simp [hl]

theorem getD_wiresFrom (gs : List Gate) (w : List Bool) (i : ℕ) (h : i < w.length) :
    (wiresFrom gs w).getD i false = w.getD i false := by
  obtain ⟨t, ht, _⟩ := wiresFrom_prefix gs w
  rw [ht, List.getD_append _ _ _ _ h]

def pins (g : Gate) := g.inputs.take (bif g.op.eval [false] then 1 else 2)
def reads (v : Nat) (g : Gate) := (pins g).contains v
def mark {n : Nat} (S : Finset (Fin n)) (v : Fin n) := decide (v ∈ S)
def atBank (g : Gate) (z : List Bool) := g.op.eval (g.inputs.map fun k => z.getD k false)

lemma read_only {v : Nat} {gs : List Gate} {a b : Gate}
    (le : (gs.filter (reads v)).length ≤ 1) (ha : a ∈ gs.filter (reads v))
    (hb : b ∈ gs) (read : v ∈ pins b) : b = a := by
  have both : b ∈ gs.filter (reads v) := List.mem_filter.mpr ⟨hb,List.contains_iff_mem.mpr read⟩
  generalize gs.filter (reads v) = ls at le ha both
  cases ls with
  | nil => simp at ha
  | cons c t =>
    have e : t = [] := by simpa using le
    subst t
    simpa using (List.mem_singleton.mp both).trans (List.mem_singleton.mp ha).symm

lemma raw {n} (x : Fin n → Bool) (tail : List Bool) (i : Fin n) :
    (List.ofFn x ++ tail).getD i.val false = x i := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_append,i.isLt]

lemma same_pin {n} (x y : Fin n → Bool) (tail : List Bool) (i : Nat)
    (h : ∀ j : Fin n, i=j.val → x j=y j) :
    (List.ofFn x ++ tail).getD i false = (List.ofFn y ++ tail).getD i false := by
  by_cases b : i<n
  · let j : Fin n := ⟨i,b⟩
    exact (raw x tail j).trans ((h j rfl).trans (raw y tail j).symm)
  · simp [List.getD_eq_getElem?_getD,List.getElem?_append,b]

lemma eval_from_pins (g : Gate) (z w : List Bool)
    (fan : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (agree : ∀ i ∈ pins g, z.getD i false = w.getD i false) : atBank g z = atBank g w := by
  obtain ⟨op,ins⟩ := g
  rcases fan with ⟨opok,arity⟩
  change op = .and ∨ op = .or ∨ op = .not at opok
  change ins.length ≤ 2 at arity
  rcases opok with rfl|rfl|rfl <;> cases ins with
  | nil => rfl
  | cons a tail =>
    cases tail with
    | nil =>
      have ha := agree a (by simp [pins,GateOp.eval])
      simp [atBank,GateOp.eval,List.getD_eq_getElem?_getD] at ha ⊢ <;> simp [ha]
    | cons b t =>
      have empty : t=[] := by simpa using arity
      subst t
      have ha := agree a (by simp [pins,GateOp.eval])
      simp [atBank,GateOp.eval,List.getD_eq_getElem?_getD] at ha ⊢
      rw [ha]
      all_goals
        have hb := agree b (by simp [pins,GateOp.eval])
        simp only [List.getD_eq_getElem?_getD] at hb
        rw [hb]

lemma parallel_wires {n} (x y : Fin n → Bool) (gs : List Gate)
    (step : ∀ g ∈ gs, ∀ rest, atBank g (List.ofFn x ++ rest) = atBank g (List.ofFn y ++ rest))
    (t : List Bool) : ∃ suffix, (Circuit.mk gs 0).wires (List.ofFn x ++ t) = List.ofFn x ++ suffix ∧
      (Circuit.mk gs 0).wires (List.ofFn y ++ t) = List.ofFn y ++ suffix := by
  induction gs generalizing t with
  | nil => exact ⟨t,rfl,rfl⟩
  | cons g gs ih =>
    have eq := step g (by simp) t
    obtain ⟨s,hx,hy⟩ := ih (fun a ha => step a (List.mem_cons_of_mem _ ha)) (t++[atBank g (List.ofFn x ++ t)])
    refine ⟨s,?_,?_⟩
    · change (Circuit.mk gs 0).wires ((List.ofFn x ++ t) ++ [atBank g _]) = _
      simpa only [List.append_assoc] using hx
    · change (Circuit.mk gs 0).wires ((List.ofFn y ++ t) ++ [atBank g _]) = _
      rw [←eq]
      simpa only [List.append_assoc] using hy

lemma lockstep {n} (C : Circuit) (fan : FanInTwo C) (g : Gate) (x y : Fin n → Bool)
    (out : n ≤ C.output)
    (reader : ∀ i : Fin n, x i ≠ y i → ∀ q ∈ C.gates, i.val ∈ pins q → q = g)
    (agree : ∀ tail, atBank g (List.ofFn x ++ tail) = atBank g (List.ofFn y ++ tail)) :
    C.eval (List.ofFn x) = C.eval (List.ofFn y) := by
  have step (q) (mem : q ∈ C.gates) (tail) :
      atBank q (List.ofFn x ++ tail)=atBank q (List.ofFn y ++ tail) := by
    by_cases eq : q=g
    · exact eq ▸ agree tail
    apply eval_from_pins _ _ _ (fan _ mem)
    intro i hi
    apply same_pin
    rintro j rfl
    by_contra different
    exact eq (reader j different q mem hi)
  obtain ⟨s,hx,hy⟩ := parallel_wires x y _ step []
  simp only [List.append_nil] at hx hy
  change ((Circuit.mk C.gates 0).wires (List.ofFn x)).getD _ false =
    ((Circuit.mk C.gates 0).wires (List.ofFn y)).getD _ false
  rw [hx,hy]
  exact same_pin x y s C.output (fun j h => by have := j.isLt; omega)

lemma pair_eval (u v : Fin n) (g : Gate) (ord : g.inputs.Perm [u.val,v.val]) (join : Bool)
    (op : g.op = if join then .or else .and) (x : Fin n → Bool) (t : List Bool) :
    atBank g (List.ofFn x ++ t) = if join then x u || x v else x u && x v := by
  rcases List.perm_pair.mp ord with e|e <;> cases join <;>
    simp only [Bool.false_eq_true,ite_false,ite_true] at op ⊢ <;>
    simp only [atBank,e,op,List.map_cons,List.map_nil,raw,GateOp.eval] <;>
    simp [Bool.and_comm,Bool.or_comm]

lemma singleton_off : ∀ v : Fin 10, edge (mark {v}) = false := by
  decide +kernel

lemma witness : ∀ u v : Fin 10, u ≠ v → ∃ r : Fin 10,
    r ≠ u ∧ r ≠ v ∧
    edge (mark {r}) = false ∧ edge (mark (insert u {r})) = true ∧
    edge (mark {v,r}) = false ∧ edge (mark (insert u {v,r})) = true := by
  decide +kernel

lemma not_raw_output (C : Circuit) (correct : circuitFun 10 C = edge) :
    10 ≤ C.output := by
  by_contra! small
  let k : Fin 10 := ⟨C.output, small⟩
  have projected (x : Fin 10 → Bool) : edge x = x k := by
    rw [←correct]
    change (wiresFrom C.gates (List.ofFn x)).getD k.val false = _
    rw [getD_wiresFrom _ _ _ (by simp)]
    simpa only [List.append_nil] using raw x [] k
  have no := singleton_off k
  rw [projected] at no
  simp [mark] at no

lemma inserts_differ (S : Finset (Fin 10)) (u i : Fin 10)
    (diff : mark S i ≠ mark (insert u S) i) : i = u := by
  by_contra ne
  exact diff (by simp [mark, ne])

lemma rawraw_repeat (C : Circuit) (fan : FanInTwo C)
    (correct : circuitFun 10 C = edge) (g : Gate) (mem : g ∈ C.gates)
    (u v : Fin 10) (uv : u ≠ v) (ord : g.inputs.Perm [u.val,v.val])
    (op : g.op = .and ∨ g.op = .or) :
    2 ≤ (C.gates.filter (reads u.val)).length := by
  by_contra! few
  have few' : (C.gates.filter (reads u.val)).length ≤ 1 := by omega
  have pin : u.val ∈ pins g := by
    rcases List.perm_pair.mp ord with e|e <;>
      rcases op with hop|hop <;> simp [pins,e,hop,GateOp.eval]
  have gm : g ∈ C.gates.filter (reads u.val) :=
    List.mem_filter.mpr ⟨mem,List.contains_iff_mem.mpr pin⟩
  have out := not_raw_output C correct
  obtain ⟨r,ru,rv,off,yes,off',yes'⟩ := witness u v uv
  have only_u (S : Finset (Fin 10)) (i : Fin 10)
      (diff : mark S i ≠ mark (insert u S) i) :
      ∀ q ∈ C.gates, i.val ∈ pins q → q=g := by
    obtain rfl := inserts_differ S u i diff
    exact fun q h hr => read_only few' gm h hr
  have deny (S : Finset (Fin 10))
      (same : ∀ t, atBank g (List.ofFn (mark S) ++ t) =
        atBank g (List.ofFn (mark (insert u S)) ++ t))
      (no : edge (mark S) = false) (yes : edge (mark (insert u S)) = true) : False := by
    have eq := lockstep C fan g (mark S) (mark (insert u S)) out (only_u S) same
    change circuitFun 10 C (mark S) = circuitFun 10 C (mark (insert u S)) at eq
    rw [correct,no,yes] at eq
    exact Bool.false_ne_true eq
  rcases op with hop|hop
  · apply deny {r} ?_ off yes
    intro t
    rw [pair_eval u v g ord false hop,pair_eval u v g ord false hop]
    simp [mark,rv.symm,uv.symm]
  · apply deny {v,r} ?_ off' yes'
    intro t
    rw [pair_eval u v g ord true hop,pair_eval u v g ord true hop]
    simp [mark]

end PEqualNP.Outside.L_meta_1890.RawRaw
