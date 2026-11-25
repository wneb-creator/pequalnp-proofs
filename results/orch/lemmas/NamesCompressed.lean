import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

namespace PEqualNP.Outside.L_meta_2373

def edge (x : Fin 10 → Bool) : Bool :=
    x 0 && x 1 ||
    x 1 && x 2 ||
    x 2 && x 3 ||
    x 3 && x 4 ||
    x 4 && x 0 ||
    x 0 && x 5 ||
    x 1 && x 6 ||
    x 2 && x 7 ||
    x 3 && x 8 ||
    x 4 && x 9 ||
    x 5 && x 7 ||
    x 7 && x 9 ||
    x 9 && x 6 ||
    x 6 && x 8 ||
    x 8 && x 5

lemma five_cycle_cover_weight (a b c d e : Nat)
    (hab : 1 ≤ a + b) (hbc : 1 ≤ b + c) (hcd : 1 ≤ c + d)
    (hde : 1 ≤ d + e) (hea : 1 ≤ e + a) : 3 ≤ a + b + c + d + e := by
  omega

lemma petersen_cover_weight (w : Fin 10 → Nat)
    (h01 : 1 ≤ w 0 + w 1) (h12 : 1 ≤ w 1 + w 2)
    (h23 : 1 ≤ w 2 + w 3) (h34 : 1 ≤ w 3 + w 4)
    (h40 : 1 ≤ w 4 + w 0) (h57 : 1 ≤ w 5 + w 7)
    (h79 : 1 ≤ w 7 + w 9) (h96 : 1 ≤ w 9 + w 6)
    (h68 : 1 ≤ w 6 + w 8) (h85 : 1 ≤ w 8 + w 5) :
    6 ≤ w 0 + w 1 + w 2 + w 3 + w 4 + w 5 + w 6 + w 7 + w 8 + w 9 := by
  have ho := five_cycle_cover_weight (w 0) (w 1) (w 2) (w 3) (w 4)
    h01 h12 h23 h34 h40
  have hi := five_cycle_cover_weight (w 5) (w 7) (w 9) (w 6) (w 8)
    h57 h79 h96 h68 h85
  omega


def petersenEdges : Finset (Fin 10 × Fin 10) :=
  {(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6), (2, 7),
    (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)}

lemma vertex_cover_size (s : Finset (Fin 10))
    (h : ∀ e ∈ petersenEdges, e.1 ∈ s ∨ e.2 ∈ s) : 6 ≤ s.card := by
  let w : Fin 10 → Nat := fun i => if i ∈ s then 1 else 0
  have hw (a b : Fin 10) (hab : (a, b) ∈ petersenEdges) : 1 ≤ w a + w b := by
    rcases h (a, b) hab with ha | hb
    · simp [w, ha]
    · simp [w, hb]
  have hh := petersen_cover_weight w
    (hw 0 1 (by decide)) (hw 1 2 (by decide)) (hw 2 3 (by decide))
    (hw 3 4 (by decide)) (hw 4 0 (by decide)) (hw 5 7 (by decide))
    (hw 7 9 (by decide)) (hw 9 6 (by decide)) (hw 6 8 (by decide))
    (hw 8 5 (by decide))
  have hsum : (∑ i : Fin 10, w i) = s.card := by
    simp [w]
  have hsum' : w 0 + w 1 + w 2 + w 3 + w 4 + w 5 + w 6 + w 7 + w 8 + w 9 =
      s.card := by
    simpa [Fin.sum_univ_succ, Nat.add_assoc] using hsum
  omega

lemma minimum_vertex_cover :
    ∃ s : Finset (Fin 10), s.card = 6 ∧
      ∀ e ∈ petersenEdges, e.1 ∈ s ∨ e.2 ∈ s := by
  exact ⟨{1, 3, 4, 5, 6, 7}, by decide, by decide⟩

lemma independent_set_size (s : Finset (Fin 10))
    (h : ∀ e ∈ petersenEdges, ¬ (e.1 ∈ s ∧ e.2 ∈ s)) : s.card ≤ 4 := by
  have hc : 6 ≤ sᶜ.card := vertex_cover_size sᶜ (by
    intro e he
    simpa only [Finset.mem_compl, not_and_or] using h e he)
  have hsum : sᶜ.card + s.card = 10 := by
    simpa only [Fintype.card_fin] using Finset.card_compl_add_card s
  omega

lemma edge_eq_false_iff (x : Fin 10 → Bool) :
    edge x = false ↔ ∀ e ∈ petersenEdges, x e.1 = false ∨ x e.2 = false := by
  simp only [edge, Bool.or_eq_false_iff, Bool.and_eq_false_iff]
  simp only [petersenEdges, Finset.forall_mem_insert, Finset.mem_singleton, forall_eq]
  simp only [and_assoc]

lemma false_input_support_size (x : Fin 10 → Bool) (hx : edge x = false) :
    (Finset.univ.filter fun i => x i = true).card ≤ 4 := by
  apply independent_set_size
  intro e he hab
  have hz := (edge_eq_false_iff x).mp hx e he
  rcases hz with hz | hz
  · have ht := (Finset.mem_filter.mp hab.1).2
    simp_all
  · have ht := (Finset.mem_filter.mp hab.2).2
    simp_all


end PEqualNP.Outside.L_meta_2373


namespace PEqualNP.Outside.L_meta_2373.NineSigned

open PEqualNP.CircuitLowerBounds

abbrev Sig := BitVec 512


def zero : Sig := 0


def one : Sig := BitVec.allOnes 512


def neg (a : Sig) : Sig := ~~~a


def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b


def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one


def q0I (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)


def q3a (d : Nat) := if d=2 then 3 else if d=3 then 2 else d


theorem q0L {u d} (h : q0I u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))


theorem q17 {u d} (h : q0I u d) (a b : Sig) : bin d a b = bin (q3a d) b a := by
  rcases q0L h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,q3a,BitVec.and_comm,BitVec.or_comm]


theorem q3b {u d} (h : q0I u d) : q0I u (q3a d) ∧ q3a (q3a d)=d := by
  rcases q0L h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩ 
  all_goals simp_all [q3a,q0I]


def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), q0I u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)


theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩


theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : q0I u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩


theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : q0I u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)


private lemma qaV {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩


private lemma qaW {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega


def bit (i : Fin 512) (a : Sig) : Bool := a.getLsbD i.val


private lemma qaN (i) : bit i zero = false := by simp [bit,zero]


private lemma qaM (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp


private lemma qaL (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]


private lemma qaK (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]


theorem q19 {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩


def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a


theorem q6X (a : Sig) : nrm false a = a := rfl


theorem q6W (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,qaL]


theorem q6Y {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]


theorem q6M (a : Sig) : neg (neg a) = a := by simp [neg]


theorem q70 (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,qaL,q6M]


theorem q7E {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])


theorem q7F {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact q7E h
  · exact h


def q7z (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b


theorem q1e (i) (d : Bool) (a b : Sig) : bit i (q7z d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [q7z,bit]


theorem q71 (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (q7z d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply q19
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,q1e,ha,hb,qaK,qaL,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,qaL,q1e]


def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (q7z false) one
  | .or => xs.foldr (q7z true) zero
  | .not => neg (xs.headD zero)
  | _ => zero


def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w


def q7W (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v


def q0f (u : Bool) (w : List Sig) (v : Sig) : Prop := q7W w (nrm u v)


private lemma qaI (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply q19 <;> intro i <;>
    simp [qaK,qaN,qaM]


private lemma qaX : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]


private lemma qaY {w : List Sig} {a : Sig} (h : q7W w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)


def qay (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, q0I u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b


private lemma qaJ {u w a b} (d : Nat) (hd : q0I u d) (ha : q7W w a) (hb : q7W w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    q7W w (bin d a b) ∨ qay u w (bin d a b) := by
  have rz : q7W w zero := Or.inr (fun h => h.1 rfl)
  have ro : q7W w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := qaI a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := qaI b
  by_cases he : a=b
  · subst b
    left
    rcases q0L hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases qaY ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases q0L hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases q0L hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases qaY hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases q0L hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases q0L hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩


theorem q6V (a : Sig) : nrm true a ≠ one := by
  intro h
  have := q6W a
  rw [h,qaM] at this
  exact Bool.noConfusion this


theorem q7A {u w a b} (d : Bool) (ha : q0f u w a) (hb : q0f u w b) :
    q0f u w (q7z d a b) ∨ qay u w (nrm u (q7z d a b)) := by
  cases u
  · have e : q7z d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := qaJ (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold q0f
    simp only [q6X] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := q71 d a b
    unfold q0f
    rw [eq]
    exact qaJ e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨q6V a,q6V b⟩)


theorem q7U {u w} {v : Sig} (h : v=zero ∨ v=one) : q0f u w v := by
  refine Or.inr fun hp => ?_
  have := q7F hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl


private lemma qaU {u} (w : List Sig) (i : Nat) : q0f u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact q7U (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))


theorem q7V {w a} (h : q0f true w a) : q0f true w (neg a) := by
  unfold q0f
  rwa [q70]


def q5f (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false


private lemma qaT (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → q5f g=false) :
    q0f u (w.map (nrm u)) (gv w g) ∨ (q5f g=false ∧ qay u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : q0f u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (q7z d) (if d then zero else one)) ∨
      qay u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (q7z d) (if d then zero else one))) := by
    have unit (v : Sig) : q7z d v (if d then zero else one) = v := by
      apply q19
      intro i
      cases d <;> simp [q1e,qaN,qaM]
    cases l with
    | nil => exact Or.inl (q7U (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (qaU w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact q7A d (qaU w i) (qaU w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [q5f])
    left
    cases l with
    | nil => exact q7U (Or.inr (by simp [gv,qaX]))
    | cons i l => exact q7V (qaU w i)


private lemma qaZ {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : q7W w z ∨ (c=1 ∧ qay u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := qaV h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha


private lemma qaS {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, q5f g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !q5f g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := qaT u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : q7W (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if q5f g then 0 else 1)=1 ∧ qay u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := qaZ ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : q5f g <;> simp [hn] at hl ⊢ <;> omega


private lemma qaH (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (qaN _).symm
  | some a => rfl


private lemma qb0 (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [qaH]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact qaM _
    | cons a l ih =>
      change bit i (q7z false _ _) = (_ && _)
      rw [q1e]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact qaN _
    | cons a l ih =>
      change bit i (q7z true _ _) = (_ || _)
      rw [q1e]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [qaL,qaN]
    | cons a l => exact qaL _ _


private lemma qaR (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,qb0 i g w (hg g (by simp))]


abbrev Wire (R : Type) := R → Bool


def inv {R} (a : Wire R) : Wire R := fun r => !(a r)


def q1V {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r


def q1S {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then q1V false a b else if d=1 then q1V true a b else
    if d=2 then q1V false a (inv b) else q1V false (inv a) b


def q04 {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b


noncomputable def q2d {R} (a : Wire R) : Nat := by
  classical exact if q04 a then 1 else 0


noncomputable def q6r {R} (xs : List (Wire R)) : Nat := (xs.map q2d).sum


def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ q04 v ∨ (u=true ∧ inv v ∈ pool)


def q9L {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a


def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=q1V op a b :: bank


theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl


theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (q1V op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩


theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (q1V op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)


def q5i {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs


def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), q0I u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (q1S op a b :: q5i ka a (q5i kb b rest))


theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _


theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩


theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : q0I u op) (ka kb : Bool)
    (h : Run u goal s (q1S op a b :: q5i ka a (q5i kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩


theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : q0I u op) (ka kb : Bool) (h : Run u goal s (q1S op a b :: q5i ka a (q5i kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))


theorem q6t {R} (a : Wire R) (xs) : q6r (a::xs)=q2d a + q6r xs := by
  simp [q6r]


theorem q6v {R} (a : Wire R) (xs) (k : Bool) : q6r xs ≤ q6r (q5i k a xs) := by
  cases k <;> simp [q5i,q6t]


theorem q5c {R} {a : Wire R} (h : q04 a) : q04 (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩


theorem q5d {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]


theorem q2e {R} (a : Wire R) : q2d (inv a)=q2d a := by
  have : q04 (inv a) ↔ q04 a := ⟨fun h => q5d a ▸ q5c h,q5c⟩
  by_cases h : q04 a
  · simp only [q2d,if_pos h,if_pos (this.mpr h)]
  · simp only [q2d,if_neg h,if_neg (fun x => h (this.mp x))]


theorem q0S {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(q5d a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (q5c h))
  · exact Or.inl h


theorem q1n {R} {a b : Wire R} (op) (h : q04 a) (g : q04 b) :
    q04 (q1V op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩


theorem q3r {R u} (op) {a b : Wire R} {bank}
    (h : q04 a ∨ q04 b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (q1V op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [q1V]⟩)
    · simpa [q1V] using hb
    · simpa [q1V] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [q1V]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [q1V]⟩)
    · simpa [q1V] using ha
    · simpa [q1V] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [q1V]⟩)


theorem q0V {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))


theorem q2V {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (q1V op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+q2d a+q2d b ≤ p+1+q2d (q1V op a b) := by
  classical
  by_cases c : q04 a ∨ q04 b
  · refine ⟨p,bank,hp,q3r op c ha hb,fun _ h => h,?_⟩
    by_cases ca : q04 a <;> by_cases cb : q04 b
    · simp [q2d,ca,cb,q1n op ca cb]
    · simp [q2d,ca,cb]
    · simp [q2d,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬q04 a := fun h => c (Or.inl h)
    have cb : ¬q04 b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => q0V _ h,
      by simp [q2d,ca,cb]⟩


theorem q1U {R u} {bank : List (Wire R)} {d a b} (hd : q0I u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, q1S d a b=q1V op x y ∧ Available u bank x ∧ Available u bank y ∧ q2d x=q2d a ∧ q2d y=q2d b := by
  rcases q0L hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,q0S hu hb,rfl,q2e b⟩
  · exact ⟨false,inv a,b,rfl,q0S hu ha,hb,q2e a,rfl⟩


theorem q2T {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : q0I u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (q1S d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+q2d a+q2d b ≤ p+1+q2d (q1S d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := q1U hd ha hb
  rw [e,←cx,←cy]
  exact q2V roots op hp hx hy


theorem q6z {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ q5i k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [q5i]


theorem q23 {R u} {goal : Wire R} (nc : ¬q04 goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : q9L u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+q6r ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [q6r,q2d,nc]⟩
  | perm eq _ ih =>
    have hsub : q9L u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [q6r,←(eq.map q2d).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := q2T roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : q9L u T (q1S op a b :: q5i ka a (q5i kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases q6z hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (q6z hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := q6v a (q5i kb b rest) ka
    have hlen' := q6v b rest kb
    rw [q6t] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [q6t,q6t]
    omega


def q7Z {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)


theorem q81 {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (q5i k a ws).map (q7Z rows) =
    q5i k (q7Z rows a) (ws.map (q7Z rows)) := by
  cases k <;> simp [q5i]


theorem q80 {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    q7Z rows (q1S d a b) = q1S d (q7Z rows a) (q7Z rows b) := by
  unfold q1S
  split_ifs <;> rfl


theorem q82 {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (q7Z rows goal) s (ws.map (q7Z rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,q81,q80] at ih ⊢
    exact Run.two op hd ka kb ih


theorem q7B {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬q04 (q7Z rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : q9L u bank (ws.map (q7Z rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (q7Z rows goal) → L ≤ q) :
    L + q6r (ws.map (q7Z rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := q23 nc (q82 rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 512


def observe (a : Sig) : Wire Row := fun r => bit r a


def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)


theorem q1h (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]


theorem q9T (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact q1h (observe v) ⟨j,hj⟩


theorem q75 (f : Wire Row) : observe (table f) = f := by
  funext r
  exact q1h f r


theorem q73 (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact qaL _ _


theorem q72 (d : Nat) (a b : Sig) :
    observe (bin d a b) = q1S d (observe a) (observe b) := by
  funext r
  simp only [observe,qaK,q1S]
  split_ifs <;> rfl


theorem q6j {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (q5i d a l).map f = q5i d (f a) (l.map f) := by cases d <;> rfl


theorem q5l {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (q5i k a l).Nodup := by cases k <;> simp [q5i,hn,ha]


theorem q5k (k : Bool) (a : Sig) (l : List Sig) :
    (q5i k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [q5i]


theorem q5S {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := q5i kb b rest
    let tail := q5i ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := q5l kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,q5i,h,hab,ar]
    have nd := q5l ka a mid bm am
    have ht : tail.toFinset = U := by
      change (q5i ka a (q5i kb b rest)).toFinset = U
      rw [q5k,q5k,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::q5i ka a (q5i kb b rest)).map observe) at progress
    rw [List.map_cons,q6j,q6j,q72] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)


theorem q9S (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←q9T (neg (table f)),q73,q75]


theorem q9U (d : Bool) (f g : Wire Row) :
    table (q1V d f g) = q7z d (table f) (table g) := by
  apply q19
  intro r
  rw [q1h,q1e,q1h,q1h]
  cases d <;> rfl


theorem q0W {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    q0f u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply q7U
    cases b
    · exact Or.inl (q19 fun i => (q1h _ i).trans (qaN i).symm)
    · exact Or.inr (q19 fun i => (q1h _ i).trans (qaM i).symm)
  · have := q9S a
    refine Or.inl ?_
    rw [←q70,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)


theorem q7N {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,q9U] at sub
    have rep := q7A d (q0W ha) (q0W hb)
    obtain ⟨k',S',hk,run',sub'⟩ := qaZ (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩


def q7q (a : Sig) : Bool := !(bit 0 a)


theorem q6Z {u} {w : List Sig} (h : w.all q7q=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact q6Y (by simpa [q7q] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]


theorem q7M {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : q7q T=true) (nR : roots.all q7q=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := q0W hit
  rw [q9T] at hm
  unfold q0f at hm
  rw [q6Y (by simpa [q7q] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := q7N h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,q9T]
  rw [e,q6Z nR] at hs
  exact hs


theorem q5U {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [qaK,qaK,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩


theorem q7L {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := q5U h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))


def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000]


def graph : Sig := 0xfffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8


def q8d (r : Row) (j : Fin 9) := bit r (inputs.getD j.val zero)


def q2I (x : Fin 9 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) ||
  (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 5 && x 7) ||
  (x 6 && x 8) || (x 8 && x 5)


theorem q2J : ∀ r : Row, bit r graph = q2I (q8d r) := by decide +kernel


theorem graph_proper : proper graph := by unfold proper; decide +kernel


theorem input_list : List.ofFn (fun j : Fin 9 => inputs.getD j.val zero) = inputs := rfl


theorem q8e (r : Row) : List.ofFn (q8d r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl


theorem q9R (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (q8d r))).getD i false := by
  rw [←qaH,qaR _ _ _ (fun g hg => (h g hg).1),q8e]
  rfl


def q7Q (f : Row → Row) (a : Sig) := table fun r => bit (f r) a


theorem q1f (f : Row → Row) (a : Sig) (r : Row) :
    bit r (q7Q f a) = bit (f r) a := q1h _ _


theorem q74 (f : Row → Row) (a : Sig) :
    observe (q7Q f a) = q7Z f (observe a) := by funext r; exact q1f f a r


theorem q7R (f : Row → Row) (d : Nat) (a b : Sig) :
    q7Q f (bin d a b) = bin d (q7Q f a) (q7Q f b) := by
  apply q19
  intro r
  simp only [q1f,qaK]


theorem q7T (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (q7Q f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [q1f,q1f,hr] at he
  exact he


theorem q7S (f : Row → Row) : q7Q f zero = zero ∧ q7Q f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (q1f f zero ⟨j,hj⟩).trans ((qaN _).trans (qaN ⟨j,hj⟩).symm)
  · exact (q1f f one ⟨j,hj⟩).trans ((qaM _).trans (qaM ⟨j,hj⟩).symm)


theorem q5T {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (q7Q f T) k (S.image (q7Q f)) := by
  have inj := q7T f onto
  obtain ⟨fz,fo⟩ := q7S f
  have pp (v) (p : proper v) : proper (q7Q f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : q7Q f (bin d a b) ∉ (insert a (insert b U)).image (q7Q f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,q7R] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih


theorem q6A {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [qaK] at hp hn
      subst none
      rcases q0L hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩


def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p


def q08 (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S


def q07 (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v


theorem q6b {u roots T L} (hp : proper T) (nT : q7q T=true) (nR : roots.all q7q=true)
    (essential : ∀ a ∈ roots, q07 T roots a)
    (noRun : q08 u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := q7M hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact q7L run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)


theorem observe_proper {v : Sig} (hv : proper v) : ¬q04 (observe v) := by
  rintro ⟨b,h⟩
  have hr : q0f false [] v := by
    apply q7U
    cases b
    · exact Or.inl (q19 fun i => (congrFun h i).trans (qaN i).symm)
    · exact Or.inr (q19 fun i => (congrFun h i).trans (qaM i).symm)
  have hr' : q7W [] v := hr
  exact (hr'.resolve_left (by simp)) hv


theorem q6s {R} (a b : List (Wire R)) : q6r (a++b) = q6r a + q6r b := by
  simp [q6r]


theorem q6u {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, q04 x) :
    q6r xs = xs.length := by
  induction xs with
  | nil => simp [q6r]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [q6t,List.length_cons,q2d,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega


theorem q6d {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : q7q T=true) (nR : roots.all q7q=true) (pG : proper G)
    (r : Row → Row) (eq : q7Q r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (q7Q r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, q07 T roots a)
    (constant : ∀ a ∈ singles, q04 (observe (q7Q r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := q7M pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact q7L run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := q5S run front nd fe
  have gc : q7Z r (observe T) = observe G := (q74 _ _).symm.trans (congrArg observe eq)
  have supp : q9L u (other.map observe) ((front.map observe).map (q7Z r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←q74]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := q7B r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ q6r ((front.map observe).map (q7Z r)) := by
    simp only [front,List.map_append,q6s]
    let xs := (singles.toList.map observe).map (q7Z r)
    have only : ∀ v ∈ xs, q04 v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←q74]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := q6u xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ q6r xs + _
    rw [sz]
    omega
  omega


def q1H (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: q5i ka a (q5i kb b ((ws.erase a).erase b))


theorem q2M {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]


theorem q2L {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, q0I u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (q1H ws a b d ka kb).length ≤ cap →
      q08 u T (cap-1) (q1H ws a b d ka kb).toFinset) :
    q08 u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := qaV tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,q2M (hn.erase _) b,
        q2M hn a]
    have ke : (q5i ka a (q5i kb b rest)).toFinset = U := by
      rw [q5k,q5k,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := q5l kb b rest rn br
    have ax : a ∉ q5i kb b rest := by cases kb <;> simp [q5i,ar,hab]
    have nd : (q1H ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,q5l ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (q1H ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::q5i ka a (q5i kb b rest)).toFinset = _
      simp [ke]
    have sc := qaW tail
    have len : (q1H ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)


def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w


def q1R {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2


def q2m {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => q1R oriented (sig a) ||| q2m oriented sig ws


theorem q2n {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (q2m oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (q1R oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [q2m]
  | cons a ws ih =>
    simp only [q2m,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]


theorem q2j {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    q2m oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (q2n (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := q5U h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [q1R,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := q6A h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [q1R,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]


theorem q2i {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    q2m (!u) sig ws = BitVec.allOnes n := by
  apply q2j h rfl correct
  simp


def q0h (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (q7Z f (observe a))) ∧
    ¬q04 (q7Z f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (q7Z f (observe T)) → L ≤ p


def q6m (d a : Sig) := a &&& d


def q0T (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := q6m d a
  m == zero || m == d || (pool.map (q6m d)).any (fun v => v==m) ||
    (u && (let c := q6m d (neg a); (pool.map (q6m d)).any (fun v => v==c)))


theorem q6o {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : q6m d a = q6m d b) :
    q7Z f (observe a) = q7Z f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,q6m,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h


theorem q6q {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : q6m d a = zero) : q7Z f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [qaN] at he
  simpa only [bit,q6m,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he


theorem q6p {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : q6m d a = d) : q7Z f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,q6m,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he


def q7u (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (q7Z f (observe a))


theorem q0U {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : q7u u f bank pool)
    (check : q0T u d pool a = true) : Available u bank (q7Z f (observe a)) := by
  simp only [q0T,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,q6q dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,q6p dom ho⟩)
  · exact q6o dom he ▸ supplyB v hv
  · have h := q0S hu (q6o dom he ▸ supplyB v hv)
    rw [q73] at h
    have e : inv (q7Z f (inv (observe a))) = q7Z f (observe a) := by
      funext r
      simp [inv,q7Z]
    rwa [e] at h


abbrev q02 := Nat × Sig × Sig


def q1K (c : q02) := bin c.1 c.2.1 c.2.2


def q0J (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))


theorem q0K {u d} (h : q0J u d=true) : q0I u d := by
  simpa [q0J,q0I] using h


def q1J (u : Bool) (d : Sig) (pool : List Sig) (c : q02) :=
  q0J u c.1 && (q0T u d pool c.2.1 && q0T u d pool c.2.2)


theorem q7l {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : q7u u f bank pool)
    (c : q02) (valid : q1J u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ q7u u f next (q1K c :: pool) := by
  simp only [q1J,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := q1U (q0K valid.1) (q0U dom hs valid.2.1)
    (q0U dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [q1K,q72,q80,e]
    exact Or.inl (by simp)
  · exact q0V _ (hs _ hm)


def q6g (u : Bool) (d : Sig) (pool : List Sig) : List q02 → Option (List Sig)
  | [] => some pool
  | c::cs => if q1J u d pool c then q6g u d (q1K c::pool) cs else none


theorem q6h {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : q7u u f bank pool)
    (cs : List q02) {result} (ok : q6g u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ q7u u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [q6g] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := q7l dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction


def q5e (d a : Sig) := q6m d a == zero || q6m d a == d


theorem q2f {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (q5e d) ≤ q6r ((ws.map observe).map (q7Z f)) := by
  classical
  induction ws with
  | nil => simp [q6r]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,q6t]
    cases h : q5e d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : q04 (q7Z f (observe a)) := by
        have hh : q6m d a = zero ∨ q6m d a = d := by simpa only [q5e,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,q6q dom hz⟩
        · exact ⟨true,q6p dom ho⟩
      simpa [q2d,hc,Nat.add_comm] using Nat.succ_le_succ ih


def q7s (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (q5e d)) && ws.all (q0T u d pool)


theorem q7t {u raw T d L} (slice : q0h u raw T d L) (cs : List q02)
    {pool ws cap} (built : q6g u d raw cs = some pool)
    (nd : ws.Nodup) (cut : q7s u d L cap cs.length pool ws = true) :
    q08 u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := q6h dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [q7s,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : q9L u bank ((ws.map observe).map (q7Z f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact q0U dom hs (List.all_eq_true.mp all a ha)
  have b := q7B f (q5S h ws nd rfl) nc hr coveredS lo
  have massLo := q2f dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega


abbrev Move := Sig × Sig × Row


def q9A (d r : Row) : Row :=
  if h : r.val < 512-d.val then ⟨d.val+r.val,by omega⟩ else ⟨r.val-(512-d.val),by omega⟩


def q0X (d : Row) : Row := Fin.ofNat 512 (512-d.val)


def q88 (m : Move) (r : Row) : Row :=
  if bit r m.1 then q9A m.2.2 r else if bit r m.2.1 then q9A (q0X m.2.2) r else r


def mux (m a b : Sig) := (m &&& a) ||| (~~~m &&& b)


def qaB (m : Move) (a : Sig) :=
  mux m.1 (a.rotateRight m.2.2.val) (mux m.2.1 (a.rotateRight (q0X m.2.2).val) a)


theorem q1g (d r : Row) (a : Sig) : bit r (a.rotateRight d.val) = bit (q9A d r) a := by
  unfold bit
  rw [BitVec.getLsbD_rotateRight_of_lt d.isLt]
  by_cases h : r.val < 512-d.val <;> simp [q9A,h,r.isLt]


theorem q1m (p x y : Bool) : (p && x || !p && y) = (if p then x else y) := by cases p <;> simp


theorem q1d (r : Row) (m a b : Sig) :
    bit r (mux m a b) = if bit r m then bit r a else bit r b := by
  simp only [bit,mux,BitVec.getLsbD_and,BitVec.getLsbD_or,BitVec.getLsbD_not,r.isLt,
    decide_true,Bool.true_and]
  exact q1m _ _ _


theorem q1b (r : Row) (m : Move) (a : Sig) : bit r (qaB m a) = bit (q88 m r) a := by
  simp only [qaB,q1d,q1g,q88]
  cases bit r m.1 <;> cases bit r m.2.1 <;> rfl


def q6F (ms : List Move) (r : Row) := ms.foldl (fun j m => q88 m j) r


def q6G (ms : List Move) (a : Sig) := ms.foldr qaB a


theorem q1c (ms : List Move) (a : Sig) (r : Row) :
    bit r (q6G ms a) = bit (q6F ms r) a := by
  induction ms generalizing r with
  | nil => rfl
  | cons m ms ih => exact (q1b r m _).trans (ih _)


theorem q6H (ms : List Move) (a : Sig) : q6G ms a = q7Q (q6F ms) a := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact (q1c ms a ⟨j,hj⟩).trans (q1f _ _ ⟨j,hj⟩).symm


def freeWord (roots : List Sig) (w : Sig) := w==zero || w==one || roots.contains w


theorem freeWord_ok {u roots w} (ok : freeWord roots w = true) :
    Available u (roots.map observe) (observe w) := by
  simp only [freeWord,Bool.or_eq_true,beq_iff_eq,List.contains_eq_mem,decide_eq_true_eq] at ok
  rcases ok with (rfl | rfl) | hm
  · exact Or.inr (Or.inl ⟨false,funext qaN⟩)
  · exact Or.inr (Or.inl ⟨true,funext qaM⟩)
  · exact Or.inl (List.mem_map_of_mem hm)


def q1F (ms : List Move) (raw : List Sig) (T : Sig) (base : List Sig) (G : Sig) :=
  q6G ms T == G && raw.all (fun a => freeWord base (q6G ms a))


theorem q6i {u ms raw T base G} (ok : q1F ms raw T base G = true) :
    q7Q (q6F ms) T = G ∧
    ∀ a ∈ raw, Available u (base.map observe) (observe (q7Q (q6F ms) a)) := by
  simp only [q1F,Bool.and_eq_true,beq_iff_eq,List.all_eq_true,q6H] at ok
  exact ⟨ok.1,fun a ha => freeWord_ok (ok.2 a ha)⟩


theorem q6c {u ms raw T base G L} (ok : q1F ms raw T base G = true)
    (pT : proper T) (nT : q7q T=true) (nR : raw.all q7q=true) (pG : proper G)
    (hL : Lower u base G L) : Lower u raw T L := by
  obtain ⟨eq,supp⟩ := q6i ok
  simpa using q6d pT nT nR pG (q6F ms) eq supp ∅ (by simp) (by simp) L hL


theorem q9E {u ms raw T base G L d} (ok : q1F ms raw T base G = true)
    (all : q6G ms d = one) (properG : proper G) (hL : Lower u base G L) :
    q0h u raw T d L := by
  obtain ⟨eq,supp⟩ := q6i ok
  have obs : q7Z (q6F ms) (observe T) = observe G :=
    (q74 _ _).symm.trans (congrArg observe eq)
  refine ⟨q6F ms,base,?_,?_,?_,?_⟩
  · intro r
    rw [←q1c,all,qaM]
  · intro a ha
    rw [←q74]
    exact supp a ha
  · rw [obs]
    exact observe_proper properG
  · rw [obs]
    exact hL


def qaz (T : Sig) (roots : List Sig) (a : Sig) (rs : Row × Row) :=
  (bit rs.1 T != bit rs.2 T) &&
  roots.all (fun w => w == a || bit rs.1 w == bit rs.2 w)


theorem qaA {T roots a rs} (ok : qaz T roots a rs = true) : q07 T roots a := by
  simp only [qaz,Bool.and_eq_true,bne_iff_ne,List.all_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
  exact ⟨rs.1,rs.2,ok.1,fun w hw hne => (ok.2 w hw).resolve_left hne⟩


def q1D (T : Sig) (raw : List Sig) (xs : List (Sig × Row × Row)) :=
  q7q T && raw.all q7q && xs.all (fun a => qaz T raw a.1 a.2)


theorem q2O {T raw xs} (ok : q1D T raw xs = true) :
    ∀ a ∈ (xs.map Prod.fst).toFinset, q07 T raw a := by
  simp only [q1D,Bool.and_eq_true] at ok
  intro a ha
  obtain ⟨⟨a,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  exact qaA (List.all_eq_true.mp ok.2 _ hm)


theorem q2P {T raw xs} (ok : q1D T raw xs = true) :
    q7q T=true ∧ raw.all q7q=true := by
  simp only [q1D,Bool.and_eq_true] at ok
  exact ok.1


theorem q6a {u raw T} (properT : proper T) (xs : List (Sig × Row × Row))
    (ok : q1D T raw xs = true) :
    Lower u raw T ((xs.map Prod.fst).toFinset.card-1) := by
  intro p bank hr hit
  obtain ⟨k,S,hk,run,sub⟩ := q7M properT (q2P ok).1 (q2P ok).2 hr hit
  have le : (xs.map Prod.fst).toFinset.card ≤ S.card := by
    apply Finset.card_le_card
    intro a ha
    obtain ⟨r,s,hd,iso⟩ := q2O ok a ha
    exact q7L run raw a sub r s hd iso
  have bound := qaW run
  omega


def q1E (ms : List Move) (T : Sig) (raw : List Sig) (base : List Sig) (G : Sig)
    (xs : List (Sig × Row × Row)) :=
  q1F ms raw T base G && q1D T raw xs &&
    xs.all (fun a => q6G ms a.1 == zero || q6G ms a.1 == one)


theorem lift_ok {u ms T raw base G xs L} (ok : q1E ms T raw base G xs = true)
    (properT : proper T) (properG : proper G) (low : Lower u base G L) :
    Lower u raw T (L+(xs.map Prod.fst).toFinset.card) := by
  simp only [q1E,Bool.and_eq_true] at ok
  obtain ⟨eq,supp⟩ := q6i ok.1.1
  apply q6d properT (q2P ok.1.2).1 (q2P ok.1.2).2 properG _ eq supp _ (q2O ok.1.2) _ L low
  intro a ha
  obtain ⟨⟨v,r,s⟩,hm,rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp ha)
  have hh := List.all_eq_true.mp ok.2 _ hm
  simp only [Bool.or_eq_true,beq_iff_eq,q6H] at hh
  rcases hh with h | h
  · rw [h]
    exact ⟨false,funext qaN⟩
  · rw [h]
    exact ⟨true,funext qaM⟩


def q8k (m : Nat) : List (Nat × Sig) :=
  (List.range 9).filterMap fun i => if m.testBit i then some (i,inputs.getD i zero) else none


def vars (m : Nat) := (q8k m).map Prod.snd


def qab (t : Nat) : Sig := bin (t/81) (inputs.getD (t/9 % 9) zero) (inputs.getD (t % 9) zero)


def varsX (m : Nat) : List Sig := if m<512 then vars m else vars m ++ [qab (m/512-1)]


def qat (m j : Nat) := if m.testBit j then inputs.getD j zero else zero


def graphGoal (m : Nat) : Sig :=
  let x := qat m
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)


def q2o : Nat → Nat
  | 0 => 0xff
  | 1 => 0x55
  | 2 => 0x33
  | 3 => 0x11
  | 4 => 0xf
  | 5 => 0x5
  | 6 => 0x3
  | _ => 0x1


def q2p : Nat → Nat
  | 0 => 0x101010101010101
  | 1 => 0x1000100010001
  | 2 => 0x10100000101
  | 3 => 0x100000001
  | 4 => 0x1010101
  | 5 => 0x10001
  | 6 => 0x101
  | _ => 0x1


def q2q : Nat → Nat
  | 0 => 0x10000000000000001000000000000000100000000000000010000000000000001000000000000000100000000000000010000000000000001
  | 1 => 0x1000000000000000000000000000000010000000000000000000000000000000100000000000000000000000000000001
  | 2 => 0x100000000000000010000000000000000000000000000000000000000000000010000000000000001
  | 3 => 0x10000000000000000000000000000000000000000000000000000000000000001
  | 4 => 0x1000000000000000100000000000000010000000000000001
  | 5 => 0x100000000000000000000000000000001
  | 6 => 0x10000000000000001
  | _ => 0x1


def q9K (z o : Nat) : Sig :=
  let fixed := z ||| o
  if z &&& o != 0 then zero else
    BitVec.ofNat 512 ((q2o (fixed &&& 7)*q2p ((fixed >>> 3) &&& 7)*q2q ((fixed >>> 6) &&& 7)) <<< o)


def q37 (z o : Nat) : List Move :=
  (List.range 9).filterMap fun j =>
    let x := inputs.getD j zero
    let step := Fin.ofNat 512 (1 <<< j)
    if z.testBit j then some (zero,x,step)
    else if o.testBit j then some (~~~x,zero,step) else none


def q9O (v : Nat) : Move :=
  let i := v &&& 15
  let j := v >>> 4
  let a := inputs.getD i zero
  let b := inputs.getD j zero
  let d := (1 <<< j)-(1 <<< i)
  (a &&& ~~~b,b &&& ~~~a,Fin.ofNat 512 d)


def q9M (t : Nat) (mask : Nat) : List (Sig × Row × Row) :=
  (q8k mask).map fun (i,a) =>
    let r := if t/81==2 && i==t/9 % 9 then 1 <<< (t % 9) else if t/81==2 && i==t % 9 then 1 <<< (t/9 % 9) else 0
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))


def q53 (m hints : Nat) : List (Sig × Row × Row) :=
  (q8k m).map fun (i,a) =>
    let r := 1 <<< ((hints >>> (4*i)) &&& 15)
    (a,Fin.ofNat 512 r,Fin.ofNat 512 (r ||| (1 <<< i)))


def q7C (T : Sig) := T != zero && T != one


theorem q7G (T : Sig) (h : q7C T = true) : proper T := by
  simpa only [q7C,proper,Bool.and_eq_true,bne_iff_ne] using h


abbrev q03 := Nat × Nat × Nat × Nat × Nat


def q1P (m z o : Nat) := m ^^^ (m &&& (z ||| o))


def q1y (m : Nat) : Sig := graphGoal m


def q7J (m : Nat) (c : q03) : Nat := m % 512+512*(c.1/512)


def q1O (m : Nat) (c : q03) (prior : Nat → Nat) : Bool :=
  let (z,o,q,s,L) := c
  let ms := q37 z o
  let raw := q7J m c
  let free := q1P raw (z % 512) o
  let G := q6G ms (q1y m)
  let xs := q9M (z/512+80) s
  let count := (xs.map Prod.fst).toFinset.card
  q7C G && q1F ms (varsX raw) (q1y m) (varsX free) G &&
    (q6G ms (q9K z o)==one) &&
    (if q=0 then q1D G (varsX free) xs && decide (L ≤ count-1)
     else q7C (graphGoal q) &&
       q1E (q37 (q1P free q 0) 0) G (varsX free) (varsX q) (graphGoal q) xs &&
       decide (L ≤ prior q+count))


theorem q1Q {u} {m : Nat} (c : q03) (prior : Nat → Nat)
    (valid : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (ok : q1O m c prior = true) : q0h u (varsX (q7J m c)) (q1y m) (q9K c.1 c.2.1) c.2.2.2.2 := by
  revert ok
  obtain ⟨z,o,q,s,L⟩ := c
  intro ok
  let ms := q37 z o
  let raw := q7J m (z,o,q,s,L)
  let free := q1P raw (z % 512) o
  let G := q6G ms (q1y m)
  let xs := q9M (z/512+80) s
  change (((q7C G && q1F ms (varsX raw) (q1y m) (varsX free) G) &&
    (q6G ms (q9K z o)==one)) && _) = true at ok
  simp only [Bool.and_eq_true,beq_iff_eq] at ok
  apply q9E ok.1.1.2 ok.1.2 (q7G _ ok.1.1.1)
  intro p bank hr ha
  have hh := ok.2
  by_cases hq : q=0
  · simp only [q1O,hq,if_true,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (q6a (q7G _ ok.1.1.1) xs hh.1 p bank hr ha)
  · simp only [q1O,hq,if_false,Bool.and_eq_true,decide_eq_true_eq] at hh
    exact hh.2.trans (lift_ok hh.1.2 (q7G _ ok.1.1.1) (q7G _ hh.1.1) (valid q) p bank hr ha)


def q1u (old rep : Nat) (swaps : List Nat) :=
  (q7C (graphGoal old) && q7q (graphGoal old) && (varsX old).all q7q) && q7C (graphGoal rep) &&
    q1F (swaps.map q9O) (varsX old) (graphGoal old) (varsX rep) (graphGoal rep)


theorem q1v {u old rep L swaps} (ok : q1u old rep swaps = true)
    (h : Lower u (varsX rep) (graphGoal rep) L) : Lower u (varsX old) (graphGoal old) L := by
  simp only [q1u,Bool.and_eq_true] at ok
  exact q6c ok.2 (q7G _ ok.1.1.1.1) ok.1.1.1.2 ok.1.1.2 (q7G _ ok.1.2) h


def q1o (entries : List (Nat × Nat)) (q : Nat) :=
  ((entries.find? (fun a => a.1 == q)).map Prod.snd).getD 0


theorem q15 {u} (entries : List (Nat × Nat))
    (sound : ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2) (q : Nat) :
    Lower u (varsX q) (graphGoal q) (q1o entries q) := by
  unfold q1o
  cases h : entries.find? (fun a => a.1 == q) with
  | none => exact fun _ _ _ _ => Nat.zero_le _
  | some e =>
    have he := List.mem_of_find?_eq_some h
    have hit : (fun a : Nat × Nat => a.1 == q) e = true := List.find?_some (p:=fun a : Nat × Nat => a.1 == q) (a:=e) h
    have eq : e.1=q := beq_iff_eq.mp hit
    simpa only [Option.map_some,Option.getD_some,eq] using sound e he


abbrev BoundPool := Sig × Nat × Nat × List Sig


def BoundPool.domain (c : BoundPool) : Sig := c.1


def BoundPool.bound (c : BoundPool) : Nat := c.2.1


def BoundPool.paid (c : BoundPool) : Nat := c.2.2.1


def BoundPool.wires (c : BoundPool) : List Sig := c.2.2.2


def q0j (u : Bool) (raw : List Sig) (T : Sig) (c : BoundPool) :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)),
    (∀ r, bit (f r) c.domain = true) ∧ ¬q04 (q7Z f (observe T)) ∧
    (∀ q ws, Reach u (roots.map observe) q ws → Available u ws (q7Z f (observe T)) → c.bound ≤ q) ∧
    Reach u (roots.map observe) c.paid bank ∧ q7u u f bank c.wires ∧ True


theorem q1t {u raw T d lb} (h : q0h u raw T d lb) (cs : List q02) {ws}
    (build : q6g u d raw cs = some ws) : q0j u raw T ⟨d,lb,cs.length,ws⟩ := by
  obtain ⟨f,roots,dom,sup,nc,prior⟩ := h
  obtain ⟨bank,hr,hs⟩ := q6h dom (Reach.start (roots:=roots.map observe)) sup cs build
  exact ⟨f,roots,bank,dom,nc,prior,by simpa [BoundPool.paid] using hr,hs,trivial⟩


theorem qas {u raw T c} (valid : q0j u raw T c) (k : Nat) (rest : List Sig)
    (choice : q02) (paid : Bool)
    (known : ∀ a ∈ rest, q0T u c.domain c.wires a = true)
    (buy : if paid then q1J u c.domain c.wires choice = true
       else q0T u c.domain c.wires (q1K choice) = true)
    (bound : k+c.paid+paid.toNat <
      c.bound+(q1K choice :: rest).countP (q5e c.domain))
    (nd : (q1K choice :: rest).Nodup) :
    q08 u T k (q1K choice :: rest).toFinset := by
  intro t ht run
  obtain ⟨f,roots,bank,dom,nc,lo,hp,hs,_⟩ := valid
  let ws := q1K choice::rest
  have done (n : Nat) (out : List (Wire Row)) (reach : Reach u (roots.map observe) n out)
      (zs : q7u u f out (q1K choice::rest)) (le : n = c.paid+paid.toNat) : False := by
    have covered : q9L u out ((ws.map observe).map (q7Z f)) := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
      exact zs _ ha
    have b := q7B f (q5S run ws nd rfl) nc reach covered lo
    have cm := q2f dom ws
    change k+c.paid+paid.toNat < c.bound+ws.countP (q5e c.domain) at bound
    omega
  cases paid with
  | false =>
    apply done _ _ hp _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact q0U dom hs buy
    · exact q0U dom hs (known _ hm)
  | true =>
    obtain ⟨out,hr,hc⟩ := q7l dom hp hs choice buy
    apply done _ _ hr _ rfl
    intro a h
    rcases List.mem_cons.mp h with rfl | hm
    · exact hc _ (by simp)
    · have point : ∀ v ∈ c.wires, Available u out (q7Z f (observe v)) :=
        fun v hu => hc v (List.mem_cons_of_mem _ hu)
      exact q0U dom point (known _ hm)


def q8f (u : Bool) (c : BoundPool) (k : Nat) (rest : List Sig) (op : q02) :=
  let z := q1K op
  let extra := !(q0T u c.domain c.wires z)
  ((k+c.paid+extra.toNat < c.bound+(z::rest).countP (q5e c.domain)) &&
    rest.all (q0T u c.domain c.wires)) && (!extra || q1J u c.domain c.wires op)


theorem q8g {u raw T c} (valid : q0j u raw T c) {k rest op}
    (nd : (q1K op::rest).Nodup) (cut : q8f u c k rest op = true) :
    q08 u T k (q1K op::rest).toFinset := by
  let extra := !(q0T u c.domain c.wires (q1K op))
  apply qas valid k rest op extra _ _ _ nd
  · simp only [q8f,Bool.and_eq_true,List.all_eq_true] at cut
    exact cut.1.2
  · simp only [q8f,Bool.and_eq_true,Bool.or_eq_true] at cut
    cases he : q0T u c.domain c.wires (q1K op) <;> simp_all [extra]
  · simp only [q8f,Bool.and_eq_true,decide_eq_true_eq] at cut
    exact cut.1.1


def q6w (u : Bool) (raw : List Sig) (cs : List q02) (d : Sig) (lb : Nat) : Option BoundPool :=
  (q6g u d raw cs).map (fun pool => ⟨d,lb,cs.length,pool⟩)


theorem q6x {u raw T d L cs c} (slice : q0h u raw T d L)
    (h : q6w u raw cs d L = some c) : q0j u raw T c := by
  unfold q6w at h
  cases he : q6g u d raw cs with
  | none => simp [he] at h
  | some pool =>
    simp only [he,Option.map_some,Option.some.injEq] at h
    subst c
    exact q1t slice cs he


abbrev q01 := BitVec 152


abbrev q0g := q01 × q01


abbrev q06 := Sig × q0g


def q76 {n : Nat} (r : Fin n → Row) (v : Sig) : BitVec n :=
  (BitVec.ofBoolListLE (List.ofFn (fun i => bit (r i) v))).cast List.length_ofFn


theorem q78 {n : Nat} (r : Fin n → Row) (v : Sig) (i : Fin n) :
    (q76 r v).getLsbD i.val = bit (r i) v := by
  simp only [q76,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [i.isLt]


def q7j (r s : Fin 152 → Row) (a : Sig) : q0g := (q76 r a,q76 s a)


def q7D (T : Sig) (r s : Fin 152 → Row) :=
  ∀ i, bit (r i) T = true ∧ bit (s i) T = false


theorem q7k {T r s} (h : q7D T r s) : Sep T 152 r s (q7j r s) := by
  exact ⟨h,fun a i => ⟨q78 _ _ _,q78 _ _ _⟩⟩


def q2W (r s : Fin 152 → Row) (x : q06) := x.2 = q7j r s x.1


def bv {n : Nat} (d : Nat) (a b : BitVec n) : BitVec n :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b


def q2u (d : Nat) (x y : q06) : q06 := (bin d x.1 y.1,bv d x.2.1 y.2.1,bv d x.2.2 y.2.2)


theorem q77 {n : Nat} (r : Fin n → Row) (d : Nat) (a b : Sig) :
    q76 r (bin d a b) = bv d (q76 r a) (q76 r b) := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have h := q78 r (bin d a b) ⟨j,hj⟩
  rw [qaK,←q78 r a ⟨j,hj⟩,←q78 r b ⟨j,hj⟩] at h
  rw [h]
  unfold bv
  split_ifs <;> simp [hj]


theorem q2X {r s x y} (d) (hx : q2W r s x) (hy : q2W r s y) :
    q2W r s (q2u d x y) := by
  change x.2 = _ at hx
  change y.2 = _ at hy
  simp only [q2W,q2u,q7j,q77,hx,hy]


def q2z : q06 := (zero,0,0)


theorem q2Y (r s) : q2W r s q2z := by
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · change (0 : q01).getLsbD j = (q76 r zero).getLsbD j
    rw [show (q76 r zero).getLsbD j = bit (r ⟨j,hj⟩) zero from q78 _ _ ⟨j,hj⟩,qaN]
    simp
  · change (0 : q01).getLsbD j = (q76 s zero).getLsbD j
    rw [show (q76 s zero).getLsbD j = bit (s ⟨j,hj⟩) zero from q78 _ _ ⟨j,hj⟩,qaN]
    simp


theorem q2Z {r s ws} (all : ∀ v ∈ ws, q2W r s v) (i : Nat) :
    q2W r s (List.getD ws i q2z) := by
  simp only [List.getD_eq_getElem?_getD]
  cases e : ws[i]? with
  | none => exact q2Y _ _
  | some v => exact all _ (List.mem_of_getElem? e)


def q2v (n : Nat) (bits : Nat) (ws : List q06) : List q06 :=
  match n with
  | 0 => ws
  | k+1 =>
    let a := ws.getD (bits &&& 15) q2z
    let b := ws.getD ((bits >>> 4) &&& 15) q2z
    q2v k (bits >>> 10) (ws++[q2u ((bits >>> 8) &&& 3) a b])


theorem q2y (n bits) (ws) (r s) (base : ∀ v ∈ ws, q2W r s v) :
    ∀ v ∈ q2v n bits ws, q2W r s v := by
  induction n generalizing ws bits with
  | zero => exact base
  | succ n ih =>
    apply ih
    intro v hv
    rcases List.mem_append.mp hv with hw | hz
    · exact base _ hw
    · obtain rfl := List.mem_singleton.mp hz
      exact q2X _ (q2Z base _) (q2Z base _)


def q0P (cols : Nat → q01) (i : Fin 152) : Row :=
  (BitVec.ofBoolListLE (List.ofFn (fun j : Fin 9 => (cols j.val).getLsbD i.val))).toFin.cast
    (by simp [List.length_ofFn])


theorem q24 : ∀ r : Row, bit r (inputs.getD 0 zero) = r.val.testBit 0 := by decide +kernel


theorem q25 : ∀ r : Row, bit r (inputs.getD 1 zero) = r.val.testBit 1 := by decide +kernel


theorem q26 : ∀ r : Row, bit r (inputs.getD 2 zero) = r.val.testBit 2 := by decide +kernel


theorem q27 : ∀ r : Row, bit r (inputs.getD 3 zero) = r.val.testBit 3 := by decide +kernel


theorem q28 : ∀ r : Row, bit r (inputs.getD 4 zero) = r.val.testBit 4 := by decide +kernel


theorem q29 : ∀ r : Row, bit r (inputs.getD 5 zero) = r.val.testBit 5 := by decide +kernel


theorem q2a : ∀ r : Row, bit r (inputs.getD 6 zero) = r.val.testBit 6 := by decide +kernel


theorem q2b : ∀ r : Row, bit r (inputs.getD 7 zero) = r.val.testBit 7 := by decide +kernel


theorem q2c : ∀ r : Row, bit r (inputs.getD 8 zero) = r.val.testBit 8 := by decide +kernel


theorem q5b : ∀ (j : Fin 9) (r : Row),
    bit r (inputs.getD j.val zero) = r.val.testBit j.val := by
  intro j r
  fin_cases j
  · exact q24 r
  · exact q25 r
  · exact q26 r
  · exact q27 r
  · exact q28 r
  · exact q29 r
  · exact q2a r
  · exact q2b r
  · exact q2c r


theorem q0Q (cols : Nat → q01) (i : Fin 152) (j : Fin 9) :
    bit (q0P cols i) (inputs.getD j.val zero) = (cols j.val).getLsbD i.val := by
  rw [q5b]
  change (BitVec.ofBoolListLE (List.ofFn (fun h : Fin 9 => (cols h.val).getLsbD i.val))).getLsbD j.val = _
  simp only [BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]
  simp [j.isLt]


def q7I (m : Nat) (p q : Nat → q01) : List q06 :=
  (q8k m).map (fun (j,a) => (a,p j,q j))


theorem q8l {m j a} (h : (j,a) ∈ q8k m) :
    j<9 ∧ a=inputs.getD j zero := by
  obtain ⟨v,hv,hh⟩ := List.mem_filterMap.mp h
  simp only [List.mem_range] at hv
  split at hh
  next =>
    cases hh
    exact ⟨hv,rfl⟩
  next => contradiction


theorem q7K (m) (p q : Nat → q01) :
    ∀ a ∈ q7I m p q, q2W (q0P p) (q0P q) a := by
  intro a ha
  obtain ⟨⟨j,v⟩,hv,rfl⟩ := List.mem_map.mp ha
  obtain ⟨hj,rfl⟩ := q8l hv
  apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi
  · exact (q0Q p ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (q78 _ _ ⟨i,hi⟩).symm
  · exact (q0Q q ⟨i,hi⟩ ⟨j,hj⟩).symm.trans (q78 _ _ ⟨i,hi⟩).symm


def q5L (m : Nat) (v : Nat → q01) : q01 :=
  let x := fun j => if m.testBit j then v j else 0
  (x 0 &&& x 1) ||| (x 1 &&& x 2) ||| (x 2 &&& x 3) ||| (x 3 &&& x 4) |||
    (x 4 &&& x 0) ||| (x 0 &&& x 5) ||| (x 1 &&& x 6) ||| (x 2 &&& x 7) |||
    (x 3 &&& x 8) ||| (x 5 &&& x 7) ||| (x 6 &&& x 8) ||| (x 8 &&& x 5)


theorem q1i (m : Nat) (v : Nat → q01) (i : Fin 152) (j : Fin 9) :
    bit (q0P v i) (qat m j.val) =
    ((if m.testBit j.val then v j.val else 0) : q01).getLsbD i.val := by
  by_cases hh : m.testBit j.val = true
  · simpa [qat,hh] using q0Q v i j
  · simp [qat,hh,qaN]


theorem q1a (m : Nat) (v : Nat → q01) (i : Fin 152) :
    bit (q0P v i) (graphGoal m) = (q5L m v).getLsbD i.val := by
  have pos (j : Nat) (hj : j<9) : (qat m j).getLsbD (q0P v i).val = ((if m.testBit j then v j else 0) : q01).getLsbD i.val := q1i m v i ⟨j,hj⟩
  simp only [bit,graphGoal,q5L,BitVec.getLsbD_and,BitVec.getLsbD_or]
  simp only [pos 0 (by decide),pos 1 (by decide),pos 2 (by decide),pos 3 (by decide),pos 4 (by decide),pos 5 (by decide),pos 6 (by decide),pos 7 (by decide),pos 8 (by decide)]


abbrev Cov := q01 × q01 × q01


def q0l (z : q01) (c : Cov) : Cov :=
  (z ||| c.1, (z &&& ~~~c.1) ||| (c.2.1 &&& ~~~z),
   (z &&& c.2.1) ||| (c.2.2 &&& ~~~z))


def q2l (d : Bool) (v : List q06) : Cov :=
  v.foldr (fun a c => q0l (q1R d a.2) c) (0,0,0)


def qa1 (c : Cov) (a : q01) : q01 := c.1 &&& ~~~(c.2.1 &&& a)


def qa4 (c : Cov) (a b : q01) : q01 :=
  c.1 &&& ~~~((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b)))


private theorem qaO (c : Cov) (a : q01) : qa1 (q0l a c) a=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [qa1,q0l,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases c.1.getLsbD i <;> cases c.2.1.getLsbD i <;> rfl


private theorem qaQ (c : Cov) (a b : q01) : qa4 (q0l a (q0l b c)) a b=c.1 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [qa4,q0l,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
    cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl


private theorem qaG (c : Cov) (a b : q01) : q0l a (q0l b c)=q0l b (q0l a c) := by
  apply Prod.ext
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi
    simp only [q0l,BitVec.getLsbD_or]
    cases a.getLsbD i <;> cases b.getLsbD i <;> rfl
  · apply Prod.ext <;> apply BitVec.eq_of_getLsbD_eq <;> intro i hi <;>
      simp only [q0l,BitVec.getLsbD_or,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and] <;>
      cases a.getLsbD i <;> cases b.getLsbD i <;> cases c.1.getLsbD i <;>
      cases c.2.1.getLsbD i <;> cases c.2.2.getLsbD i <;> rfl


private theorem qaP (d : Bool) {l r : List q06} (h : l.Perm r) : q2l d l=q2l d r := by
  induction h with
  | nil => rfl
  | cons a _ ih => exact congrArg (q0l (q1R d a.2)) ih
  | swap a b t => exact qaG _ _ _
  | trans _ _ h1 h2 => exact h1.trans h2


theorem q2g (d : Bool) (v : List q06) {r s} (good : ∀ a ∈ v, q2W r s a) :
    (q2l d v).1 = q2m d (q7j r s) (v.map Prod.fst) := by
  induction v with
  | nil => rfl
  | cons a v ih =>
    change (q1R d a.2 ||| (q2l d v).1) = q1R d (q7j r s a.1) ||| _
    rw [show a.2=q7j r s a.1 from good _ (by simp),ih (fun a ha => good a (by simp [ha]))]


def q2A (ws : List q06) (a : q06) (keep : Bool) :=
  if keep then ws else ws.erase a


def q2D (ws : List q06) (a b : q06) (ka kb : Bool) :=
  q2A (q2A ws a ka) b kb


theorem q2B {ws : List q06} (a : q06) (ha : a ∈ ws) :
    ws.Perm (a::ws.erase a) := List.perm_cons_erase ha


theorem q2h {ws : List q06} (d : Bool) (a : q06) (ha : a ∈ ws) (keep : Bool) :
    (q2l d (q2A ws a keep)).1 =
      (if keep then (q2l d ws).1 else qa1 (q2l d ws) (q1R d a.2)) := by
  cases keep
  · change (q2l d (ws.erase a)).1 = qa1 (q2l d ws) _
    rw [qaP d (q2B a ha)]
    exact (qaO _ _).symm
  · rfl


theorem q2E {ws : List q06} (a b : q06) (ha : a ∈ ws) (hb : b ∈ ws) (hne : a≠b) :
    ws.Perm (a::b::(ws.erase a).erase b) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm hne)).mpr hb
  exact (q2B a ha).trans (List.Perm.cons _ (q2B b hm))


theorem q2k {ws : List q06} (d : Bool) (a b : q06) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a ≠ b) (ka kb : Bool) :
    (q2l d (q2D ws a b ka kb)).1 =
      (if ka then (if kb then (q2l d ws).1 else qa1 (q2l d ws) (q1R d b.2))
       else if kb then qa1 (q2l d ws) (q1R d a.2)
       else qa4 (q2l d ws) (q1R d a.2) (q1R d b.2)) := by
  cases ka <;> cases kb
  · change (q2l d ((ws.erase a).erase b)).1 = qa4 (q2l d ws) _ _
    rw [qaP d (q2E a b ha hb ne)]
    exact (qaQ _ _ _).symm
  · exact q2h d a ha false
  · exact q2h d b hb false
  · rfl


def q8b (a b : List Sig) := (a.all (fun x => b.contains x)) && (b.all (fun x => a.contains x))


theorem q8c {xs ys} (h : q8b xs ys = true) : xs.toFinset=ys.toFinset := by
  simp only [q8b,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq] at h
  ext a
  simp only [List.mem_toFinset]
  exact ⟨h.1 a,h.2 a⟩


def q5p (v : Sig) :=
  let n := v.toNat % 2305843009213693951
  (n*(n+971)) % 2305843009213693951


def q5n (xs : List Sig) := xs.foldl (fun v x => v+q5p x) 0


def q1M (u : Bool) (pools : List BoundPool) (links : Nat → List (List Sig)) (k : Nat)
    (rest : List Sig) (op : q02) :=
  let ws := q1K op::rest
  (links (q5n ws)).any (q8b ws) || pools.any (fun p => q8f u p k rest op)


theorem q1N {u raw T pools links k rest op}
    (pValid : ∀ p ∈ pools, q0j u raw T p)
    (lValid : ∀ tag xs, xs ∈ links tag → q08 u T k (List.toFinset xs))
    (nd : (q1K op :: rest).Nodup)
    (h : q1M u pools links k rest op = true) :
    q08 u T k (q1K op :: rest).toFinset := by
  simp only [q1M,Bool.or_eq_true,List.any_eq_true] at h
  rcases h with ⟨xs,hx,ok⟩ | ⟨p,hp,ok⟩
  · rw [q8c ok]
    exact lValid _ _ hx
  · exact q8g (pValid _ hp) nd ok


abbrev q05 := Cov × Bool


def q7v (u : Bool) (ws : List q06) : q05 := (q2l (!u) ws,u)


def q7Y (v : Cov) (a b : q01) (ka kb : Bool) :=
  if ka then (if kb then v.1 else qa1 v b) else if kb then qa1 v a else qa4 v a b


theorem q2C (ws : List q06) (a : q06) (k : Bool) : (q2A ws a k).Sublist ws := by
  cases k
  · exact List.erase_sublist
  · exact List.Sublist.refl _


theorem q5h (ws : List q06) (a b : q06) (ka kb : Bool) :
    (q2D ws a b ka kb).Sublist ws := (q2C _ _ _).trans (q2C _ _ _)


theorem q5K (ws : List q06) (a b : q06) (ka kb : Bool) (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) :
    (q2D ws a b ka kb).length =
      ws.length - (if ka then 0 else 1) - (if kb then 0 else 1) := by
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  cases ka <;> cases kb <;> simp [q2D,q2A,List.length_erase_of_mem ha,List.length_erase_of_mem hb,List.length_erase_of_mem hm]


def q6D (op : Nat) (a b : q06) : q02 := (op,a.1,b.1)


abbrev q0b := Nat × Nat × List q06 × q05 × List BoundPool × (Nat → List (List Sig))


def q2Q (c : q0b) (op : Nat) (a b z : q06) (ka kb : Bool) :=
  let (cap,n,ws,cov,pools,links) := c
  let len := 1+(n - (if ka then 0 else 1) - (if kb then 0 else 1))
  if len>cap then true else
    let d := !cov.2
    let rs := q7Y cov.1 (q1R d a.2) (q1R d b.2) ka kb
    if (rs ||| q1R d z.2) != BitVec.allOnes 152 then true else
    if !q7C z.1 || ws.any (fun v => v.1==z.1) then true else
      let rest := (q2D ws a b ka kb).map Prod.fst
      q1M cov.2 pools links (cap-1) rest (q6D op a b)


def q6C (ws : List q06) (op : Nat) (a b : q06) (ka kb : Bool) :=
  (q2u op a b).1 :: (q2D ws a b ka kb).map Prod.fst


theorem q2R {u raw T r s ws pools links cap a b op ka kb}
    (pairs : q7D T r s) (faith : ∀ w ∈ ws, q2W r s w)
    (nd : (ws.map Prod.fst).Nodup) (ha : a ∈ ws) (hb : b ∈ ws)
    (ne : a≠b) (hcap : 0<cap)
    (pv : ∀ p ∈ pools, q0j u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → q08 u T (cap-1) (List.toFinset xs))
    (pro : proper (q2u op a b).1) (fresh : (q2u op a b).1 ∉ ws.map Prod.fst)
    (test : q2Q (cap,ws.length,ws,q7v u ws,pools,links) op a b (q2u op a b) ka kb = true) :
    q08 u T (cap-1) (q6C ws op a b ka kb).toFinset := by
  let z := q2u op a b
  let rest := q2D ws a b ka kb
  let child := z.1 :: rest.map Prod.fst
  have sub : rest.Sublist ws := q5h _ _ _ _ _
  have ndc : child.Nodup := List.nodup_cons.mpr ⟨fun hm => fresh ((sub.map _).subset hm),
    nd.sublist (sub.map _)⟩
  have fr : ws.any (fun v => v.1==z.1) = false := by
    apply Bool.eq_false_iff.mpr
    intro hh
    obtain ⟨x,hx,he⟩ := List.any_eq_true.mp hh
    exact fresh (beq_iff_eq.mp he ▸ List.mem_map_of_mem hx)
  have pp : q7C z.1 = true := by simpa [q7C,proper] using pro
  have leq : 1+(ws.length-(if ka then 0 else 1)-(if kb then 0 else 1)) = child.length := by
    change _ = (z.1::rest.map Prod.fst).length
    rw [List.length_cons,List.length_map,q5K _ _ _ _ _ ha hb ne,Nat.add_comm 1]
  intro k hk h
  have hsz := qaW h
  change child.toFinset.card ≤ k+1 at hsz
  rw [List.toFinset_card_of_nodup ndc] at hsz
  have len : child.length ≤ cap := by omega
  unfold q2Q at test
  change (if 1+(ws.length-_ - _) > cap then true else _) = true at test
  rw [leq,if_neg (by omega)] at test
  have sep := q2i h (q7k pairs)
  let d := !u
  have g : (q2l d rest).1 = q2m d (q7j r s) (rest.map Prod.fst) :=
    q2g _ _ (fun v hv => faith _ (sub.subset hv))
  have rz : (q2l d rest).1 = q7Y (q2l d ws) (q1R d a.2) (q1R d b.2) ka kb :=
    q2k d a b ha hb ne ka kb
  have hf := q2X op (faith _ ha) (faith _ hb)
  change q1R d (q7j r s z.1) ||| q2m d (q7j r s) (rest.map Prod.fst) = _ at sep
  change z.2 = q7j r s z.1 at hf
  rw [←hf,←g,rz,BitVec.or_comm] at sep
  have be : ((q7Y (q2l (!u) ws) (q1R (!u) a.2) (q1R (!u) b.2) ka kb ||| q1R (!u) z.2) != BitVec.allOnes 152) = false := by
    simpa using sep
  change (if (q7Y (q2l (!u) ws) (q1R (!u) a.2) (q1R (!u) b.2) ka kb ||| q1R (!u) z.2) != BitVec.allOnes 152 then true else if !q7C z.1 || ws.any (fun v => v.1==z.1) then true else _) = true at test
  rw [be,pp,fr] at test
  exact q1N (op:=q6D op a b) (rest:=rest.map Prod.fst) pv lv ndc test k hk h


def qa7 (ctx : q0b) (a b : q06) (op : Nat) :=
  let z := q2u op a b
  let attempt := q2Q ctx op a b z
  attempt false false && attempt true false && attempt false true && attempt true true


def q7a (u : Bool) : List Nat := if u then [0,1,2,3] else [0,1]


theorem q7b {u d} (h : q0I u d) : d ∈ q7a u := by
  rcases q0L h with rfl | rfl | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · cases u <;> simp [q7a]
  · cases u <;> simp [q7a]
  · simp [q7a]
  · simp [q7a]


def qa9 (ctx : q0b) (a : q06) (bs : List q06) :=
    bs.all (fun b => (q7a ctx.2.2.2.1.2).all (qa7 ctx a b))


def qa6 (ctx : q0b) : List q06 → Bool
  | [] => true
  | a::bs => qa9 ctx a bs && qa6 ctx bs


theorem q0n {ctx ws} (h : qa6 ctx ws=true) {a b : q06} (ha : a∈ws) (hb : b∈ws)
    (ne : a≠b) : (∀ d, q0I ctx.2.2.2.1.2 d → qa7 ctx a b d=true) ∨
      (∀ d, q0I ctx.2.2.2.1.2 d → qa7 ctx b a d=true) := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    simp only [qa6,Bool.and_eq_true,qa9,List.all_eq_true] at h
    rcases List.mem_cons.mp ha with rfl | haTail
    · have bm := (List.mem_cons.mp hb).resolve_left (Ne.symm ne)
      exact Or.inl fun d hd => h.1 b bm d (q7b hd)
    · rcases List.mem_cons.mp hb with rfl | hbTail
      · exact Or.inr fun d hd => h.1 a haTail d (q7b hd)
      · exact ih h.2 haTail hbTail


theorem qa8 {ctx a b d} (h : qa7 ctx a b d = true) (ka kb : Bool) :
    q2Q ctx d a b (q2u d a b) ka kb = true := by
  simp only [qa7,Bool.and_eq_true] at h
  cases ka <;> cases kb <;> first | exact h.1.1.1 | exact h.1.2 | exact h.1.1.2 | exact h.2


theorem q5g {v : List Sig} {w : Sig} (a : Sig) (k : Bool) :
    w ∈ q5i k a v ↔ (w=a ∧ k=true) ∨ w∈v := by cases k <;> simp [q5i]


theorem q6y {v : List q06} (nd : v.Nodup) (a w : q06) (k : Bool) :
    w ∈ q2A v a k ↔ w∈v ∧ (w≠a ∨ k=true) := by
  cases k <;> simp [q2A,nd.mem_erase_iff,and_comm]


theorem qad {ws : List q06} (nd : (ws.map Prod.fst).Nodup) {a b : q06}
    (ha : a∈ws) (hb : b∈ws) (eq : a.1=b.1) : a=b := by
  induction ws with
  | nil => simp at ha
  | cons w ws ih =>
    obtain ⟨hn,ht⟩ := List.nodup_cons.mp nd
    rcases List.mem_cons.mp ha with rfl | haTail <;> rcases List.mem_cons.mp hb with rfl | hbTail
    · rfl
    · exact False.elim (hn (eq ▸ List.mem_map_of_mem hbTail))
    · exact False.elim (hn (eq.symm ▸ List.mem_map_of_mem haTail))
    · exact ih ht haTail hbTail


theorem q5m {ws : List q06} (nd : (ws.map Prod.fst).Nodup) {a b : q06}
    (ha : a ∈ ws) (hb : b ∈ ws) (ka kb : Bool) (v : Sig) :
    v ∈ (q2D ws a b ka kb).map Prod.fst ↔
    v ∈ ws.map Prod.fst ∧ (v≠a.1 ∨ ka=true) ∧ (v≠b.1 ∨ kb=true) := by
  have wn := nd.of_map
  have dn := wn.sublist (q2C ws a ka)
  simp only [q2D,List.mem_map,q6y wn,q6y dn]
  constructor
  · rintro ⟨w,hw,rfl⟩
    exact ⟨⟨_,hw.1.1,rfl⟩,hw.1.2.imp (fun ne eq => ne (qad nd hw.1.1 ha eq)) id,
          hw.2.imp (fun ne eq => ne (qad nd hw.1.1 hb eq)) id⟩
  · rintro ⟨⟨w,hm,rfl⟩,h1,h2⟩
    exact ⟨w,⟨⟨hm,h1.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,
        h2.imp (fun ne eq => ne (congrArg Prod.fst eq)) id⟩,rfl⟩


theorem q18 {ws : List q06} (nd : (ws.map Prod.fst).Nodup) {a b : q06}
    (ha : a∈ws) (hb : b∈ws) (ne : a.1≠b.1) (d : Nat) (ka kb : Bool) :
    (q6C ws d a b ka kb).toFinset =
      (q1H (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
  ext v
  have av := List.mem_map_of_mem (f:=Prod.fst) ha
  have bv' := List.mem_map_of_mem (f:=Prod.fst) hb
  simp only [q6C,q1H,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    q5m nd ha hb,q5g,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,q2u]
  by_cases va : v=a.1 <;> by_cases vb : v=b.1 <;> cases ka <;> cases kb <;> simp_all


theorem q1I {u} (v : List Sig) (nd : v.Nodup) (a b : Sig) (d : Nat) (hd : q0I u d) (ka kb : Bool) :
    (q1H v a b d ka kb).toFinset = (q1H v b a (q3a d) kb ka).toFinset := by
  ext x
  simp only [q1H,List.toFinset_cons,Finset.mem_insert,List.mem_toFinset,
    q5g,(nd.erase _).mem_erase_iff,nd.mem_erase_iff,q17 hd a b]
  tauto


theorem q6U {u raw T r s ws pools links cap}
    (pairs : q7D T r s) (faith : ∀ w ∈ ws, q2W r s w)
    (nd : (ws.map Prod.fst).Nodup) (out : T ∉ ws.map Prod.fst)
    (pv : ∀ p ∈ pools, q0j u raw T p)
    (lv : ∀ tag xs, xs ∈ links tag → q08 u T (cap-1) (List.toFinset xs))
    (checks : qa6 (cap,ws.length,ws,q7v u ws,pools,links) ws = true) :
    q08 u T cap (ws.map Prod.fst).toFinset := by
  by_cases hc : cap=0
  · intro k hk h
    have ke : k=0 := by omega
    subst k
    generalize he : (ws.map Prod.fst).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact out (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  have hc' : 0<cap := by omega
  apply q2L nd out
  intro a ha b hb d hd ka kb ne fresh pro len
  obtain ⟨a,haW,rfl⟩ := List.mem_map.mp ha
  obtain ⟨b,hbW,rfl⟩ := List.mem_map.mp hb
  have ab : a≠b := fun e => ne (congrArg Prod.fst e)
  have one (a b : q06) (d : Nat) (aa : a∈ws) (bb : b∈ws) (ne' : a.1≠b.1) (ka kb : Bool)
      (pr : proper (bin d a.1 b.1)) (fr : bin d a.1 b.1 ∉ ws.map Prod.fst)
      (test : qa7 (cap,ws.length,ws,q7v u ws,pools,links) a b d = true) :
      q08 u T (cap-1) (q1H (ws.map Prod.fst) a.1 b.1 d ka kb).toFinset := by
    rw [←q18 nd aa bb ne']
    exact q2R pairs faith nd aa bb (fun e => ne' (congrArg Prod.fst e)) hc' pv lv
      pr fr (qa8 test ka kb)
  rcases q0n checks haW hbW ab with hh | hh
  · exact one a b d haW hbW ne ka kb pro fresh (hh d hd)
  · rw [q1I _ nd _ _ d hd]
    exact one b a (q3a d) hbW haW (Ne.symm ne) kb ka (q17 hd a.1 b.1 ▸ pro)
      (q17 hd a.1 b.1 ▸ fresh) (hh _ (q3b hd).1)


theorem q0m (r s : Row) (h : ∀ a ∈ inputs, bit r a = bit s a) : r=s := by
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j<9
  · let i : Fin 9 := ⟨j,hj⟩
    have hm : inputs.getD i.val zero ∈ inputs := by
      rw [← input_list]
      exact List.mem_ofFn.mpr ⟨i,rfl⟩
    exact (q5b i r).symm.trans ((h _ hm).trans (q5b i s))
  · have le : 512 ≤ 2^j := by
      change 2^9 ≤ 2^j
      exact Nat.pow_le_pow_right (by decide) (by omega)
    exact (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le r.isLt le)).trans
      (Nat.testBit_eq_false_of_lt (lt_of_lt_of_le s.isLt le)).symm


def q1X (p q : List Move) := inputs.all (fun a => q6G p (q6G q a) == a)


theorem q1Y {p q} (h : q1X p q = true) (r : Row) :
    q6F q (q6F p r) = r := by
  apply q0m
  intro a ha
  rw [←q1c,←q1c]
  have eq := beq_iff_eq.mp (List.all_eq_true.mp h a ha)
  rw [eq]


def q0R (T : Sig) (p : List Move) :=
  (q6G p T == T) && q1X p p.reverse && q1X p.reverse p


theorem q84 {u T n} {ws : List Sig} (hi : q08 u T n ws.toFinset)
    (p : List Move) (ok : q0R T p = true) : q08 u T n (ws.map (q6G p.reverse)).toFinset := by
  simp only [q0R,Bool.and_eq_true,beq_iff_eq] at ok
  have onto : Function.Surjective (q6F p) := fun r => ⟨q6F p.reverse r,q1Y ok.2 r⟩
  intro k hk h
  have run := q5T h (q6F p) onto
  have goal : q7Q (q6F p) T = T := (q6H p T).symm.trans ok.1.1
  have inv (x : Sig) : q7Q (q6F p) (q6G p.reverse x) = x := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    change bit ⟨j,hj⟩ _ = bit ⟨j,hj⟩ _
    rw [q1f,q1c,q1Y ok.1.2]
  have back : (ws.map (q6G p.reverse)).toFinset.image (q7Q (q6F p)) = ws.toFinset := by
    ext a
    simp only [Finset.mem_image,List.mem_toFinset,List.mem_map]
    constructor
    · rintro ⟨v,⟨w,hw,rfl⟩,rfl⟩
      simpa only [inv] using hw
    · intro ha
      exact ⟨_,⟨a,ha,rfl⟩,inv a⟩
  rw [goal,back] at run
  exact hi k hk run


abbrev q0e := Nat × Nat × Nat × Nat × Nat × Nat × Nat × (Nat → Nat)


def q2K : q0e := (0,0,0,0,0,0,0,fun _ => 0)


def q7c (word : Nat → Nat) (pos len : Nat) :=
  let i := pos/8192
  let shift := pos % 8192
  let lo := word i >>> shift
  if shift+len ≤ 8192 then lo &&& ((1 <<< len)-1)
  else (lo ||| (word (i+1) <<< (8192-shift))) &&& ((1 <<< len)-1)


def q5W (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := q7c data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := q7c data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 16 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


def q5V (nb slots sw vw iw pw : Nat) (data : Nat → Nat) (h : Nat) : Option (Nat × Nat) :=
  let a := h % nb
  let sh := q7c data (a*sw) sw
  let row := (h/nb+sh) % slots
  let word := q7c data (nb*sw+row*vw) vw
  if (word >>> (iw+pw)) == h/(nb*slots) % 4 then
    some (word &&& ((1 <<< iw)-1),(word >>> iw) &&& ((1 <<< pw)-1))
  else none


abbrev Forest := Nat × Nat × (Nat → q01 × q01) × List q03 × List (List Nat) ×
  (Nat → q0e) × (Nat → Nat → Option (Nat × Nat))


def Forest.mask (g : Forest) : Nat := g.1


def Forest.mode (g : Forest) : Bool := !(g.1.testBit 10)


def Forest.samples (g : Forest) : Nat → q01 × q01 := g.2.2.1


def Forest.cols (g : Forest) : List q03 := g.2.2.2.1


def Forest.autos (g : Forest) : List (List Nat) := g.2.2.2.2.1


def Forest.levels (g : Forest) : Nat → q0e := g.2.2.2.2.2.1


def Forest.index (g : Forest) : Nat → Nat → Option (Nat × Nat) := g.2.2.2.2.2.2


def qaw (g : Forest) :=
  let ws := q7I g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)
  ws


theorem qax (g : Forest) : ∀ a ∈ qaw g,
    q2W (q0P fun j => (g.samples j).1) (q0P fun j => (g.samples j).2) a := by
  exact q7K g.mask (fun j => (g.samples j).1) (fun j => (g.samples j).2)


def qa5 (g : Forest) := q1y g.mask


def q1z (m : Nat) (v : Nat → q01) :=
  q5L m v


theorem q1A (m : Nat) (v : Nat → q01) (i : Fin 152) :
    bit (q0P v i) (q1y m) = (q1z m v).getLsbD i.val := by
  exact q1a m v i


theorem q1B {m : Nat} {p q : Nat → q01}
    (hp : q1z m p = BitVec.allOnes 152) (hq : q1z m q = 0) :
    q7D (q1y m) (q0P p) (q0P q) := by
  intro i
  simp only [q1A,hp,hq,BitVec.getLsbD_allOnes,i.isLt,decide_true,BitVec.getLsbD_zero]
  simp


def q8h {α : Type} (bits : Nat) : List α → List α
  | [] => []
  | w::ws => if bits &&& 1 == 1 then w::q8h (bits >>> 1) ws else q8h (bits >>> 1) ws


theorem q8j {α : Type} (bits : Nat) (ws : List α) : (q8h bits ws).Sublist ws := by
  induction ws generalizing bits with
  | nil => exact List.Sublist.slnil
  | cons a ws ih =>
    unfold q8h
    split
    · exact List.Sublist.cons₂ _ (ih _)
    · exact List.Sublist.cons _ (ih _)


def q7w (d : Nat) := 10*(d-1)


def q2H (d flags : Nat) := flags % 16 + (if d=0 then 0 else 10) + flags/16


def q2G (d raw dict : Nat) :=
  (dict % 65536)*q7w d + (dict/65536)*(raw+d)


def q3p (tab : q0e) (raw i : Nat) : Nat :=
  let (_,d,_,dict,flags,_,marker,word) := tab
  let width := 10*d+raw+d
  if marker<1024 then q7c word (i*width) width else
    let off := q2G d raw dict+i*q2H d flags
    let pre := q7c word off (flags % 16)
    let lastBits := if d=0 then 0 else 10
    let last := q7c word (off+flags % 16) lastBits
    let mask := q7c word (off+flags % 16+lastBits) (flags/16)
    let base := (dict % 65536)*q7w d
    q7c word (pre*q7w d) (q7w d) |||
      (last <<< q7w d) ||| (q7c word (base+mask*(raw+d)) (raw+d) <<< (10*d))


def q9J (_g : Forest) (depth : Nat) := depth


def q7O (g : Forest) (k i : Nat) : Nat × List q06 × List q06 :=
  let raw := qaw g
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*q9J g depth
  let width := len+raw.length+depth
  let recp := q3p (g.levels k) raw.length i
  let stored := recp &&& ((1 <<< len)-1)
  let ops := stored
  let bank := q2v depth ops raw
  (ops,bank,q8h (recp >>> len) bank)


def q50 (x pos width : Nat) := (x >>> pos) &&& ((1 <<< width)-1)


def q1L (bank : List q06) (ops paid : Nat) : Nat → List q02
  | 0 => []
  | n+1 =>
    let more := q1L bank (ops >>> 10) (paid >>> 1) n
    if paid &&& 1 == 0 then more else
      (q50 ops 8 2,(bank.getD (ops &&& 15) q2z).1,
        (bank.getD (q50 ops 4 4) q2z).1) :: more


def q1r (g : Forest) (ops d : Nat) (bank : List q06) (idx paid : Nat) : Option BoundPool :=
  (g.cols[idx]?).bind fun ci =>
    q6w g.mode (varsX (q7J g.mask ci)) (q1L bank ops paid d) (q9K ci.1 ci.2.1) ci.2.2.2.2


theorem q1s (g : Forest)
    (cols : ∀ ci ∈ g.cols, q0h g.mode (varsX (q7J g.mask ci)) (qa5 g) (q9K ci.1 ci.2.1) ci.2.2.2.2)
    {i ops depth bank paid c} (h : q1r g ops depth bank i paid = some c) :
    q0j g.mode (vars g.mask) (qa5 g) c := by
  unfold q1r at h
  cases e : g.cols[i]? with
  | none => simp [e] at h
  | some ci =>
    simp only [e,Option.bind_some] at h
    apply q6x _ h
    exact cols ci (List.mem_of_getElem? e)


def q51 (data : Nat → Nat) (w v : Nat) : Nat → Nat → List (Nat × Nat)
  | 0,_ => []
  | n+1,pos =>
    let x := q7c data pos (w+v)
    (x &&& ((1 <<< w)-1),x >>> w) :: q51 data w v n (pos+w+v)


def q3e {α : Type} : Nat → (Nat → α) → α
  | 0, next => next 0
  | n+1, next => next (n+1)


def q7P (data : Nat → Nat) (dict cw d gapBits : Nat) :
    Nat → Nat → Nat → List (Nat × Nat)
  | 0,_,_ => []
  | left+1,st,first =>
    q3e st fun pos => q3e first fun base =>
    q3e (q7c data pos 32) fun head =>
    q3e (Nat.log2 (head ^^^ (head+1))) fun ones =>
    q3e (base+(ones <<< gapBits)+q7c data (pos+ones+1) gapBits) fun key =>
    q3e (q7c data (dict+key*(cw+d)) (cw+d)) fun pair =>
      (pair &&& ((1 <<< cw)-1),pair >>> cw) ::
        q7P data dict cw d gapBits left (pos+ones+1+gapBits) (key+1)


def promoteHints {α : Type} (a b : Nat) (xs : List α) : List α :=
  let rec collect : List α → Nat → List α → List α → List α → List α
    | [],_,first,second,other => first ++ second ++ other.reverse
    | x::tail,i,first,second,other =>
      if i=a then collect tail (i+1) [x] second other
      else if i=b then collect tail (i+1) first [x] other
      else collect tail (i+1) first second (x::other)
  collect xs 0 [] [] []


def q3o (tab : q0e) (raw i : Nat) : List (Nat × Nat) :=
  let (num,d,cw,dict,flags,ow,marker,data) := tab
  if marker<1024 then
    let start := num*(10*d+raw+d)
    let pos := start+num*ow+q7c data (start+i*ow) ow
    q51 data cw d (q7c data pos 5) (pos+5+marker)
  else
    let off := q2G d raw dict + num*q2H d flags
    let pairs := off+num*ow
    let priority := decide (4096≤marker)
    let pos := pairs+(marker-(if priority then 4096 else 1024))*(cw+d)+q7c data (off+i*ow) ow
    let n := q7c data pos 5
    let gap := q7c data (pos+5) 3
    if !priority || decide (n≤1) then q7P data pairs cw d gap n (pos+8) 0 else
      let width := (n-1).log2+1
      let a := q7c data (pos+8) width
      let b := if n=2 then 1-a else q7c data (pos+8+width) width
      let extra := if n=2 then width else 2*width
      let xs := q7P data pairs cw d gap n (pos+8+extra) 0
      promoteHints a b xs


def q9I (g : Forest) (k i : Nat) := (q7O g k i).2.2.map Prod.fst


def q5P (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Sig) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).map fun perm => (q9I g k pair.1).map (q6G (perm.map q9O).reverse)


theorem q5Q (g : Forest) (k : Nat)
    (names : ∀ x ∈ g.autos, q0R (qa5 g) (x.map q9O) = true)
    (earlier : ∀ i < (g.levels k).1, q08 g.mode (qa5 g) k (q9I g k i).toFinset)
    {pair out} (h : q5P g k pair = some out) :
    q08 g.mode (qa5 g) k out.toFinset := by
  unfold q5P at h
  split at h
  · contradiction
  next valid =>
    cases e : g.autos[pair.2]? with
    | none => simp [e] at h
    | some perm =>
      simp only [e,Option.map_some,Option.some.injEq] at h
      subst out
      exact q84 (earlier _ (by omega)) _ (names _ (List.mem_of_getElem? e))


def q6S (g : Forest) (k i : Nat) :=
  let raw := qaw g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := q7O g k i
  let values := ws.map Prod.fst
  let rules := (q3o (g.levels k) raw.length i).filterMap (fun (a,b) => q1r g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (q5P g (k-1))).toList
  decide values.Nodup && !(values.contains (qa5 g)) &&
    (if k=0 then true else qa6 (k,ws.length,ws,q7v g.mode ws,rules,ls) ws)


theorem q6T (g : Forest) (k i : Nat)
    (samples : q7D (qa5 g) (q0P fun j => (g.samples j).1) (q0P fun j => (g.samples j).2))
    (cols : ∀ ci ∈ g.cols, q0h g.mode (varsX (q7J g.mask ci)) (qa5 g) (q9K ci.1 ci.2.1) ci.2.2.2.2)
    (names : ∀ x ∈ g.autos, q0R (qa5 g) (x.map q9O) = true)
    (prior : k>0 → ∀ j < (g.levels (k-1)).1, q08 g.mode (qa5 g) (k-1) (q9I g (k-1) j).toFinset)
    (checked : q6S g k i = true) : q08 g.mode (qa5 g) k (q9I g k i).toFinset := by
  simp only [q6S,Bool.and_eq_true,decide_eq_true_eq,Bool.not_eq_true',List.contains_eq_mem] at checked
  have hN := checked.1.1
  have hT : qa5 g ∉ q9I g k i := by simpa [q9I] using checked.1.2
  by_cases h0 : k=0
  · subst k
    intro t lo h
    have ht : t=0 := by omega
    subst t
    generalize he : (q9I g 0 i).toFinset = S at h
    obtain ⟨hS,_⟩ := h
    exact hT (List.mem_toFinset.mp (by rw [he,hS]; exact Finset.mem_singleton_self _))
  apply q6U (raw:=vars g.mask) samples _ hN hT _ _ (by simpa only [h0,if_false] using checked.2)
  · intro v hv
    apply q2y _ _ _ _ _ (qax g) v
    exact (q8j _ _).subset hv
  · intro p hp
    obtain ⟨⟨a,b⟩,_,h⟩ := List.mem_filterMap.mp hp
    exact q1s g cols h
  · intro tag xs hx
    have e : ((g.index k tag).bind (q5P g (k-1)))=some xs := by simpa using hx
    obtain ⟨pair,_,h⟩ := Option.bind_eq_some_iff.mp e
    exact q5Q g _ names (prior (by omega)) h


def q1j (g : Forest) (k start : Nat) : Nat → Bool
  | 0 => true
  | n+1 => q6S g k (start+n) && q1j g k start n


theorem q1k {g k start n} (h : q1j g k start n=true) (j : Nat) (lo : start≤j) (hi : j<start+n) :
    q6S g k j=true := by
  induction n with
  | zero => omega
  | succ n ih =>
    simp only [q1j,Bool.and_eq_true] at h
    by_cases eq : j=start+n
    · simpa [eq] using h.1
    · exact ih h.2 (by omega)


theorem q1l {g k start a b} (h : q1j g k start a=true)
    (h' : q1j g k (start+a) b=true) : q1j g k start (a+b)=true := by
  induction b with
  | zero => simpa using h
  | succ b ih =>
    simp only [q1j,Bool.and_eq_true] at h'
    simp only [Nat.add_succ,q1j,Bool.and_eq_true]
    exact ⟨by simpa [Nat.add_assoc] using h'.1,ih h'.2⟩


def q1G (g : Forest) (top : Nat) :=
  ∀ k ≤ top, q1j g k 0 (g.levels k).1 = true


def q54 (g : Forest) (prior : Nat → Nat) :=
  (q1z g.mask (fun j => (g.samples j).1) == BitVec.allOnes 152) &&
  (q1z g.mask (fun j => (g.samples j).2) == 0) &&
  g.cols.all (fun c => q1O g.mask c prior) &&
  g.autos.all (fun p => q0R (qa5 g) (p.map q9O))


theorem q3q (g : Forest) (top : Nat) (prior : Nat → Nat)
    (lower : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geometry : q54 g prior = true) (rows : q1G g top) :
    ∀ k ≤ top, ∀ i < (g.levels k).1, q08 g.mode (qa5 g) k (q9I g k i).toFinset := by
  simp only [q54,Bool.and_eq_true,List.all_eq_true,beq_iff_eq] at geometry
  intro k
  induction k with
  | zero =>
    intro hk i hi
    apply q6T g 0 i (q1B geometry.1.1.1 geometry.1.1.2)
      (fun x hx => q1Q _ prior lower (geometry.1.2 x hx)) geometry.2 (by omega)
    exact q1k (rows 0 hk) i (by omega) (by omega)
  | succ k ih =>
    intro hk i hi
    apply q6T g _ i (q1B geometry.1.1.1 geometry.1.1.2)
      (fun x hx => q1Q _ prior lower (geometry.1.2 x hx)) geometry.2
      (fun _ => by simpa using ih (by omega))
    exact q1k (rows _ hk) i (by omega) (by omega)


def q5a (g : Forest) (k i : Nat) (ws : List Sig) :=
  decide (i < (g.levels k).1) && q8b (q9I g k i) ws


theorem q83 {g top prior k i ws} (low : ∀ q, Lower g.mode (varsX q) (graphGoal q) (prior q))
    (geom : q54 g prior = true) (blocks : q1G g top) (le : k ≤ top)
    (idx : q5a g k i ws = true) : q08 g.mode (qa5 g) k ws.toFinset := by
  simp only [q5a,Bool.and_eq_true,decide_eq_true_eq] at idx
  rw [←q8c idx.2]
  exact q3q g top prior low geom blocks _ le i idx.1


def q09 (u : Bool) (entries : List (Nat × Nat)) := ∀ e ∈ entries, Lower u (varsX e.1) (graphGoal e.1) e.2


def q2S (old : List (Nat × Nat)) (L : Nat) (carries : List (Nat × List Nat)) :=
  carries.map (fun v => (v.1,L)) ++ old


theorem q2U {u old L m carries} (previous : q09 u old)
    (main : Lower u (varsX m) (graphGoal m) L)
    (ok : carries.all (fun v => q1u v.1 m v.2) = true) :
    q09 u (q2S old L carries) := by
  intro e he
  rcases List.mem_append.mp he with hx | h
  · obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hx
    exact q1v (List.all_eq_true.mp ok _ hv) main
  · exact previous e h


theorem q0Y : q09 true [] := by simp [q09]


def q5D (v : Nat) (upper : Nat) := 2^153*upper+v


def q1W {α : Type} (f : α → q01) : List α → Nat
  | [] => 0
  | x::xs => q5D (f x).toNat (q1W f xs)


def qaf : Nat → Nat
  | 0 => 0
  | n+1 => q5D 1 (qaf n)


theorem q5E (x : q01) : x.toNat < 2^153 :=
  lt_trans x.isLt (by decide +kernel)


theorem q7n (a b : q01) (u v : Nat) :
    q5D a.toNat u &&& q5D b.toNat v = q5D (a &&& b).toNat (u &&& v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [q5D,Nat.testBit_and,Nat.testBit_two_pow_mul_add _ (q5E _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_and,Nat.testBit_and]


theorem q7o (a b : q01) (u v : Nat) :
    q5D a.toNat u ||| q5D b.toNat v = q5D (a ||| b).toNat (u ||| v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [q5D,Nat.testBit_or,Nat.testBit_two_pow_mul_add _ (q5E _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_or,Nat.testBit_or]


theorem q7p (a b : q01) (u v : Nat) :
    q5D a.toNat u ^^^ q5D b.toNat v = q5D (a ^^^ b).toNat (u ^^^ v) := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [q5D,Nat.testBit_xor,Nat.testBit_two_pow_mul_add _ (q5E _)]
  by_cases h : i<153 <;> simp only [h,ite_true,ite_false,BitVec.toNat_xor,Nat.testBit_xor]


theorem q5H {α} (f g : α → q01) (xs) :
    q1W f xs &&& q1W g xs = q1W (fun x => f x &&& g x) xs := by
  induction xs with
  | nil => simp [q1W]
  | cons a xs ih => simp only [q1W,q7n,ih]


theorem q5I {α} (f g : α → q01) (xs) :
    q1W f xs ||| q1W g xs = q1W (fun x => f x ||| g x) xs := by
  induction xs with
  | nil => simp [q1W]
  | cons a xs ih => simp only [q1W,q7o,ih]


theorem q5J {α} (f g : α → q01) (xs) :
    q1W f xs ^^^ q1W g xs = q1W (fun x => f x ^^^ g x) xs := by
  induction xs with
  | nil => simp [q1W]
  | cons a xs ih => simp only [q1W,q7p,ih]


def q3t (r packed : Nat) := ((packed+r) >>> 152) &&& r


theorem qae (n i : Nat) (hi : i<n) : (qaf n).testBit (153*i) = true := by
  induction n generalizing i with
  | zero => omega
  | succ n ih =>
    rw [qaf,q5D,Nat.testBit_two_pow_mul_add _ (by decide +kernel : 1 < 2^153)]
    cases i with
    | zero => simp
    | succ i =>
      have di : 153*(i+1)-153=153*i := by omega
      have ge : ¬153*(i+1)<153 := by omega
      simp only [ge,ite_false,di]
      exact ih _ (by omega)


set_option maxRecDepth 8192 in
theorem q55 (a : q01) : (a.toNat+1).testBit 152 = (a==BitVec.allOnes 152) := by
  by_cases h : a=BitVec.allOnes 152
  · subst a
    decide +kernel
  · have lim := a.isLt
    have ne : a.toNat ≠ 2^152-1 := by
      intro eq
      apply h
      apply BitVec.eq_of_toNat_eq
      simpa only [BitVec.toNat_allOnes] using eq
    have lt : a.toNat+1<2^152 := by omega
    rw [Nat.testBit_eq_false_of_lt lt]
    exact (beq_eq_false_iff_ne.mpr h).symm


set_option maxRecDepth 8192 in
theorem q6k {α} (f : α → q01) (xs : List α) (i : Nat) (hi : i<xs.length) :
    (q3t (qaf xs.length) (q1W f xs)).testBit (153*i) =
      (f xs[i]==BitVec.allOnes 152) := by
  simp only [q3t,Nat.testBit_and,Nat.testBit_shiftRight,qae _ _ hi,Bool.and_true]
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    simp only [q1W,List.length_cons,qaf,q5D]
    have sum (u v x : Nat) : 2^153*u+x+(2^153*v+1)=2^153*(u+v)+(x+1) := by omega
    rw [sum,Nat.testBit_two_pow_mul_add _ (show (f a).toNat+1<2^153 from by have := (f a).isLt; omega)]
    have hi' : i < xs.length+1 := hi
    cases i with
    | zero => simpa using q55 (f a)
    | succ i =>
      have ge : ¬153*(i+1)+152<153 := by omega
      have di : 153*(i+1)+152-153=153*i+152 := by omega
      simp only [ge,ite_false,di,List.getElem_cons_succ]
      apply ih i (by omega)


abbrev q0d := Nat × Nat


abbrev q0c := Nat × Nat × Nat


def q7g {α} (s : α → q0g) (xs : List α) : q0d :=
  (q1W (fun x => (s x).1) xs,q1W (fun x => (s x).2) xs)


def q7e {α} (c : α → Cov) (xs : List α) : q0c :=
  (q1W (fun x => (c x).1) xs,q1W (fun x => (c x).2.1) xs,
   q1W (fun x => (c x).2.2) xs)


def q7d (d : Bool) (a : q0d) :=
  if d then a.1 ^^^ (a.1 &&& a.2) else a.1 ^^^ a.2


theorem qaD (a b : q01) : a ^^^ (a &&& b) = a &&& ~~~b := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_xor,BitVec.getLsbD_and,BitVec.getLsbD_not,hi,decide_true,Bool.true_and]
  cases a.getLsbD i <;> cases b.getLsbD i <;> rfl


theorem q7h {α} (s : α → q0g) (xs : List α) (d : Bool) :
    q7d d (q7g s xs) = q1W (fun x => q1R d (s x)) xs := by
  cases d <;> simp only [q7d,q7g,q1R,Bool.false_eq_true,ite_false,ite_true,q5H,q5J,qaD]


def q7f (op : Nat) (a b : q0d) : q0d :=
  if op=0 then (a.1 &&& b.1,a.2 &&& b.2) else if op=1 then (a.1 ||| b.1,a.2 ||| b.2)
  else if op=2 then (a.1 ^^^ (a.1 &&& b.1),a.2 ^^^ (a.2 &&& b.2))
  else (b.1 ^^^ (b.1 &&& a.1),b.2 ^^^ (b.2 &&& a.2))


theorem q7i {α} (a b : α → q06) (xs : List α) (op : Nat) :
    q7f op (q7g (fun x => (a x).2) xs) (q7g (fun x => (b x).2) xs) =
    q7g (fun x => (q2u op (a x) (b x)).2) xs := by
  by_cases h0 : op=0
  · simp only [q7f,h0,ite_true,q7g,q5H,q2u,bv]
  by_cases h1 : op=1
  · simp [q7f,h1,q7g,q5I,q2u,bv]
  by_cases h2 : op=2
  · simp [q7f,h2,q7g,q5H,q5J,qaD,q2u,bv]
  · have e (x y : q01) : ~~~x &&& y = y &&& ~~~x := BitVec.and_comm _ _
    simp only [q7f,h0,h1,h2,ite_false,q7g,q5H,q5J,qaD,q2u,bv,e]


def qa2 (c : q0c) (a b : Nat) (ka kb : Bool) :=
  let without1 := fun w => c.1 ^^^ (c.1 &&& (c.2.1 &&& w))
  let without2 := c.1 ^^^ (c.1 &&& ((c.2.1 &&& (a ||| b)) ||| (c.2.2 &&& (a &&& b))))
  if ka then (if kb then c.1 else without1 b)
  else if kb then without1 a else without2


theorem qa3 {α} (c : α → Cov) (a b : α → q01) (xs : List α) (ka kb : Bool) :
    qa2 (q7e c xs) (q1W a xs) (q1W b xs) ka kb =
    q1W (fun x => q7Y (c x) (a x) (b x) ka kb) xs := by
  cases ka <;> cases kb <;>
    simp only [qa2,q7e,q5H,q5I,q5J,qaD,q7Y,qa1,qa4,
      Bool.false_eq_true,ite_false,ite_true]


def q21 (c : q0b) (i : Nat) := c.2.2.1.getD i q2z


def q1C (c : q0b) (i j op : Nat) (ka kb : Bool) :=
  let a := q21 c i
  let b := q21 c j
  q2Q c op a b (q2u op a b) ka kb


def q1T (c : q0b) (d ka kb : Bool) (op i j : Nat) :=
  let a := q21 c i
  let b := q21 c j
  q7Y c.2.2.2.1.1 (q1R d a.2) (q1R d b.2) ka kb |||
    q1R d (q2u op a b).2


def q79 {α : Type} (f : α → Bool) (mask : Nat) : List α → Bool
  | [] => true
  | x::xs => if mask=0 then true else
    ((mask &&& 1 == 0) || f x) && q79 f (mask >>> 153) xs


theorem q6l {α} (f : α → Bool) (mask : Nat) (xs : List α) (i : Nat) (hi : i<xs.length)
    (bitOn : mask.testBit (153*i)=true) (ok : q79 f mask xs=true) : f xs[i]=true := by
  induction xs generalizing mask i with
  | nil => simp at hi
  | cons x xs ih =>
    have ne : mask≠0 := by intro e; simp [e] at bitOn
    simp only [q79,ne,ite_false,Bool.and_eq_true,Bool.or_eq_true,beq_iff_eq] at ok
    cases i with
    | zero =>
      have nonzero : mask &&& 1 ≠ 0 := by
        intro he
        have at0 := congrArg (fun n : Nat => n.testBit 0) he
        simp only [Nat.testBit_and] at at0
        change mask.testBit 0=true at bitOn
        simp [bitOn] at at0
      exact ok.1.resolve_left nonzero
    | succ i =>
      apply ih (mask:=mask >>> 153) (i:=i) (by simpa using hi) _ ok.2
      simpa only [Nat.testBit_shiftRight,Nat.mul_succ,Nat.add_comm] using bitOn


abbrev q00 := Nat × Nat × Nat × List q0d × q0c


def q6e (k n : Nat) (xs : List q0b) : q00 :=
  (k,n,qaf xs.length,(List.range n).map (fun i => q7g (fun c => (q21 c i).2) xs),
    q7e (fun c => c.2.2.2.1.1) xs)


def q5F (b : q00) (i : Nat) := b.2.2.2.1.getD i (0,0)


theorem q5G (k n) (xs) {i : Nat} (h : i<n) :
    q5F (q6e k n xs) i = q7g (fun c => (q21 c i).2) xs := by
  simp [q5F,q6e,List.getD_eq_getElem?_getD,List.getElem?_map,List.getElem?_range,h]


theorem q6n (d x : Sig) : q6m d (neg x) = d ^^^ q6m d x := by
  apply q19
  intro r
  simp only [q6m,neg,bit,BitVec.getLsbD_and,BitVec.getLsbD_not,BitVec.getLsbD_xor,r.isLt,decide_true,Bool.true_and]
  cases d.getLsbD r.val <;> cases x.getLsbD r.val <;> rfl


def q1Z (p : q06 → Bool) (a : q06) (keep : Bool) :=
  if keep then 0 else (p a).toNat


theorem q5X (p : q06 → Bool) (ws : List q06) (a : q06) (keep : Bool) :
    ws.countP p ≤ (q2A ws a keep).countP p + q1Z p a keep := by
  cases keep
  · simp only [q2A,Bool.false_eq_true,ite_false,q1Z,List.countP_erase]
    split
    next h => simp [h.2]; omega
    next => omega
  · simp [q2A,q1Z]


theorem q5j (p : q06 → Bool) (ws : List q06) (a b : q06) (ka kb : Bool) :
    ws.countP p - q1Z p a ka - q1Z p b kb ≤
    (q2D ws a b ka kb).countP p := by
  have h1 := q5X p ws a ka
  have h2 := q5X p (q2A ws a ka) b kb
  simp only [q2D]
  omega


noncomputable def q3c {β : Type} (n : Nat) (f : Nat → β) : β := Nat.rec (f 0) (fun k _ => f (Nat.succ k)) n


theorem q3n {β : Type} (n : Nat) (f : Nat → β) : q3c n f = f n := by cases n <;> rfl


noncomputable def q3h {α β : Type} (f : α → Nat) (l : List α) : (List Nat → β) → β :=
  List.rec (fun k => k []) (fun a _ ih k => q3c (f a) fun x => ih fun xs => k (x::xs)) l


theorem q3i {α β : Type} (f : α → Nat) (l : List α) (k : List Nat → β) : q3h f l k = k (l.map f) := by
  induction l generalizing k with
  | nil => rfl
  | cons a l ih =>
    change q3c (f a) (fun x => q3h f l fun xs => k (x::xs)) = _
    rw [q3n,ih]
    rfl


def q6Q (d : Nat) (a : Sig) : Nat := Nat.land a.toNat d


noncomputable def q0M (m : Nat) (l : List Nat) : Bool := List.rec false (fun v _ ih => or (Nat.beq m v) ih) l


def q6K (d m : Nat) : Bool := or (Nat.beq m 0) (Nat.beq m d)


noncomputable def q6I (u : Bool) (d : Nat) (pm : List Nat) (m : Nat) : Bool :=
  or (or (q6K d m) (q0M m pm)) (and u (q0M (Nat.xor d m) pm))


theorem q6R (d a : Sig) : q6Q d.toNat a = (q6m d a).toNat := (BitVec.toNat_and _ _).symm


theorem q16 (a b : Sig) : Nat.beq a.toNat b.toNat = (a==b) := by
  rw [Bool.eq_iff_iff,Nat.beq_eq,beq_iff_eq]
  exact BitVec.toNat_inj


theorem q6L (d a : Sig) : q6K d.toNat (q6Q d.toNat a) = q5e d a := by
  rw [q6R]
  have e : Nat.beq (q6m d a).toNat 0 = (q6m d a == zero) := by
    have z0 : zero.toNat=0 := by simp [zero]
    rw [←q16,z0]
  rw [q6K,e,q16]
  rfl


theorem q0N (x d : Sig) (pool : List Sig) : q0M x.toNat (pool.map (q6Q d.toNat)) = (pool.map (q6m d)).any (fun v => v==x) := by
  induction pool with
  | nil => rfl
  | cons a l ih =>
    change or (Nat.beq x.toNat (q6Q d.toNat a)) (q0M x.toNat (l.map (q6Q d.toNat))) = _
    rw [ih,q6R,q16,List.map_cons,List.any_cons,Bool.beq_comm]


theorem q6J (u : Bool) (d a : Sig) (pool : List Sig) :
    q6I u d.toNat (pool.map (q6Q d.toNat)) (q6Q d.toNat a) = q0T u d pool a := by
  have x : Nat.xor d.toNat (q6m d a).toNat = (q6m d (neg a)).toNat := by
    rw [q6n]
    exact (BitVec.toNat_xor _ _).symm
  rw [q6I,q6L,q6R,x,q0N,q0N]
  simp only [q0T,q5e]


def qac (u : Bool) (p : BoundPool) (w : q06) : Nat := cond (q0T u p.domain p.wires w.1) 0 1


def q9F (u : Bool) (p : BoundPool) (ws : List q06) (k : Nat) (a b : q06) (op : Nat) (ka kb : Bool) : Bool :=
  let const := fun w : q06 => q5e p.domain w.1
  let z := bin op a.1 b.1
  let cm := ws.countP const - q1Z const a ka - q1Z const b kb + (q5e p.domain z).toNat
  (((ws.map (qac u p)).sum == cond ka 0 (qac u p a) + cond kb 0 (qac u p b)) &&
    decide (k+p.paid+(!q0T u p.domain p.wires z).toNat < p.bound+cm)) &&
    (q0T u p.domain p.wires z || (q0T u p.domain p.wires a.1 && q0T u p.domain p.wires b.1))


def zN (op x y : Nat) : Nat := cond (Nat.beq op 0) (Nat.land x y) (cond (Nat.beq op 1) (Nat.lor x y)
  (cond (Nat.beq op 2) (Nat.xor x (Nat.land x y)) (Nat.xor y (Nat.land x y))))


theorem qaE (op : Nat) (d a b : Sig) : zN op (q6Q d.toNat a) (q6Q d.toNat b) = q6Q d.toNat (bin op a b) := by
  have tn (x y : Sig) : Nat.land x.toNat y.toNat = (x &&& y).toNat := (BitVec.toNat_and x y).symm
  have tx (x y : Sig) : Nat.xor x.toNat y.toNat = (x ^^^ y).toNat := (BitVec.toNat_xor x y).symm
  have tor (x y : Sig) : Nat.lor x.toNat y.toNat = (x ||| y).toNat := (BitVec.toNat_or x y).symm
  simp only [q6R]
  unfold zN
  by_cases h0 : op=0
  · subst h0
    change Nat.land _ _ = _
    rw [tn]
    congr 1
    apply q19
    intro r
    simp only [q6m,bin,bit,ite_true,BitVec.getLsbD_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  by_cases h1 : op=1
  · subst h1
    change Nat.lor _ _ = _
    rw [tor]
    congr 1
    apply q19
    intro r
    simp only [q6m,bin,bit,Nat.one_ne_zero,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_or]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e0 : Nat.beq op 0=false := Bool.eq_false_iff.mpr (fun h => h0 (Nat.eq_of_beq_eq_true h))
  have e1 : Nat.beq op 1=false := Bool.eq_false_iff.mpr (fun h => h1 (Nat.eq_of_beq_eq_true h))
  by_cases h2 : op=2
  · subst h2
    change Nat.xor _ (Nat.land _ _) = _
    rw [tn,tx]
    congr 1
    apply q19
    intro r
    simp only [q6m,bin,bit,OfNat.ofNat_ne_zero,OfNat.ofNat_ne_one,ite_true,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
    cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl
  have e2 : Nat.beq op 2=false := Bool.eq_false_iff.mpr (fun h => h2 (Nat.eq_of_beq_eq_true h))
  rw [e0,e1,e2]
  change Nat.xor _ (Nat.land _ _) = _
  rw [tn,tx]
  congr 1
  apply q19
  intro r
  simp only [q6m,bin,bit,h0,h1,h2,ite_false,BitVec.getLsbD_and,BitVec.getLsbD_xor,BitVec.getLsbD_not,r.isLt,decide_true,Bool.true_and]
  cases a.getLsbD r.val <;> cases b.getLsbD r.val <;> cases d.getLsbD r.val <;> rfl


def q6O (d x : Nat) (keep : Bool) : Nat := cond keep 0 (cond (q6K d x) 1 0)


theorem q6P (d : Sig) (a : q06) (keep : Bool) :
    q6O d.toNat (q6Q d.toNat a.1) keep = q1Z (fun w : q06 => q5e d w.1) a keep := by
  rw [q6O,q6L,q1Z]
  cases keep
  · cases q5e d a.1 <;> rfl
  · rfl


abbrev QS := Nat × Nat × Nat × Nat × Nat × List Nat × List Nat × Bool


noncomputable def q7H (u : Bool) (k : Nat) (ws : List q06) (p : BoundPool) : QS :=
  let d := p.domain.toNat
  let ms := ws.map (fun w : q06 => q6Q d w.1)
  (d,ms.countP (q6K d),p.bound,Nat.add k p.paid,(ms.map fun m => cond (q6I u d (p.wires.map (q6Q d)) m) 0 1).sum,ms,p.wires.map (q6Q d),u)


noncomputable def q3d {β : Type} (b : Bool) (f : Bool → β) : β := Bool.rec (f false) (f true) b


noncomputable def q3j {β : Type} (u : Bool) (k : Nat) (ws : List q06) (p : BoundPool) (f : QS → β) : β :=
  q3c p.domain.toNat fun d => q3h (q6Q d) p.wires fun pm => q3h (fun w : q06 => q6Q d w.1) ws fun ms =>
  q3c (ms.countP (q6K d)) fun c => q3c p.bound fun l => q3c (Nat.add k p.paid) fun t =>
  q3c (ms.map fun m => cond (q6I u d pm m) 0 1).sum fun v => q3d u fun u => f (d,c,l,t,v,ms,pm,u)


theorem q3k {β : Type} (u k ws p) (f : QS → β) : q3j u k ws p f = f (q7H u k ws p) := by
  have e (b : Bool) (f : Bool → β) : q3d b f = f b := by cases b <;> rfl
  simp only [q3j,q3n,q3i,e]
  rfl


noncomputable def q3l {β : Type} (u : Bool) (k : Nat) (ws : List q06) (ps : List BoundPool) : (List QS → β) → β :=
  List.rec (fun f => f []) (fun p _ ih f => q3j u k ws p fun q => ih fun qs => f (q::qs)) ps


theorem q3m {β : Type} (u k ws ps) (f : List QS → β) : q3l u k ws ps f = f (ps.map (q7H u k ws)) := by
  induction ps generalizing f with
  | nil => rfl
  | cons p ps ih =>
    change q3j u k ws p (fun q => q3l u k ws ps fun qs => f (q::qs)) = _
    rw [q3k,ih]
    rfl


def kwN (v : Nat) : Nat :=
  let n := v % 2305843009213693951
  (n*(n+971)) % 2305843009213693951


abbrev q0a := q0b × Nat × Nat × List QS × List Nat × Nat


noncomputable def q5C (c : q0b) : q0a :=
  let ws := c.2.2.1.map (fun w : q06 => w.1.toNat)
  (c,c.2.2.1.length,cond c.2.2.2.1.2 4 2,c.2.2.2.2.1.map (q7H c.2.2.2.1.2 (c.1-1) c.2.2.1),ws,(ws.map kwN).sum)


noncomputable def q3f {β : Type} (cs : List q0b) : (List q0a → β) → β :=
  List.rec (fun f => f []) (fun c _ ih f => q3c c.2.2.1.length fun n => q3c (cond c.2.2.2.1.2 4 2) fun l =>
    q3h (fun w : q06 => w.1.toNat) c.2.2.1 fun ws => q3c (ws.map kwN).sum fun t =>
    q3l c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => ih fun ys => f ((c,n,l,qs,ws,t)::ys)) cs


theorem q3g {β : Type} (cs) (f : List q0a → β) : q3f cs f = f (cs.map q5C) := by
  induction cs generalizing f with
  | nil => rfl
  | cons c cs ih =>
    change q3c c.2.2.1.length (fun n => q3c (cond c.2.2.2.1.2 4 2) fun l =>
      q3h (fun w : q06 => w.1.toNat) c.2.2.1 fun ws => q3c (ws.map kwN).sum fun t =>
      q3l c.2.2.2.1.2 (c.1-1) c.2.2.1 c.2.2.2.2.1 fun qs => q3f cs fun ys => f ((c,n,l,qs,ws,t)::ys)) = _
    rw [q3n,q3n,q3i,q3n,q3m,ih]
    rfl


noncomputable def q32 (s : QS) (i j op : Nat) (ka kb : Bool) : Bool :=
  q3c (s.2.2.2.2.2.1.getD i 0) fun x => q3c (s.2.2.2.2.2.1.getD j 0) fun y =>
  let av := q6I s.2.2.2.2.2.2.2 s.1 s.2.2.2.2.2.2.1
  let hi := Nat.add s.2.2.1 (Nat.sub (Nat.sub s.2.1 (q6O s.1 x ka)) (q6O s.1 y kb))
  let lo := s.2.2.2.1
  and (Nat.beq s.2.2.2.2.1 (Nat.add (cond ka 0 (cond (av x) 0 1)) (cond kb 0 (cond (av y) 0 1))))
  (cond (Nat.ble (Nat.succ lo) hi)
    (q3c (zN op x y) fun z => or (av z) (and (Nat.ble (Nat.add lo 2) hi) (and (av x) (av y))))
    (cond (Nat.ble lo hi) (q6K s.1 (zN op x y)) false))


theorem q9G {d : Nat} (ws : List q06) (i : Nat) (hd : q6Q d zero=0) :
    (ws.map (fun w : q06 => q6Q d w.1)).getD i 0 = q6Q d (ws.getD i q2z).1 := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none => exact hd.symm
  | some v => rfl


theorem q36 {u k p ws i j op ka kb} (h : q32 (q7H u k ws p) i j op ka kb=true) :
    q9F u p ws k (ws.getD i q2z) (ws.getD j q2z) op ka kb=true := by
  have z0 : q6Q p.domain.toNat zero=0 := by
    have : zero.toNat=0 := by simp [zero]
    simp [q6Q,this]
  have su : (((ws.map (fun w : q06 => q6Q p.domain.toNat w.1)).map fun m => cond (q6I u p.domain.toNat (p.wires.map (q6Q p.domain.toNat)) m) 0 1).sum) =
      (ws.map (qac u p)).sum := by
    rw [List.map_map]
    refine congrArg List.sum (List.map_congr_left ?_)
    intro w _
    change cond (q6I u p.domain.toNat (p.wires.map (q6Q p.domain.toNat)) (q6Q p.domain.toNat w.1)) 0 1 = _
    rw [q6J]
    rfl
  simp only [q32,q7H,q3n,q9G _ _ z0,su,List.countP_map,Function.comp_def,q6L] at h
  generalize ws.getD i q2z=a at h ⊢
  generalize ws.getD j q2z=b at h ⊢
  replace h : and (Nat.beq (ws.map (qac u p)).sum (Nat.add (cond ka 0 (cond ((q6I u p.domain.toNat (p.wires.map (q6Q p.domain.toNat))) (q6Q p.domain.toNat a.1)) 0 1)) (cond kb 0 (cond ((q6I u p.domain.toNat (p.wires.map (q6Q p.domain.toNat))) (q6Q p.domain.toNat b.1)) 0 1))))
   (cond (Nat.ble (Nat.succ (Nat.add k p.paid)) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : q06 => q5e p.domain w.1)) (q6O p.domain.toNat (q6Q p.domain.toNat a.1) ka)) (q6O p.domain.toNat (q6Q p.domain.toNat b.1) kb))))
    (or ((q6I u p.domain.toNat (p.wires.map (q6Q p.domain.toNat))) (zN op (q6Q p.domain.toNat a.1) (q6Q p.domain.toNat b.1))) (and (Nat.ble (Nat.add (Nat.add k p.paid) 2) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : q06 => q5e p.domain w.1)) (q6O p.domain.toNat (q6Q p.domain.toNat a.1) ka)) (q6O p.domain.toNat (q6Q p.domain.toNat b.1) kb)))) (and ((q6I u p.domain.toNat (p.wires.map (q6Q p.domain.toNat))) (q6Q p.domain.toNat a.1)) ((q6I u p.domain.toNat (p.wires.map (q6Q p.domain.toNat))) (q6Q p.domain.toNat b.1)))))
    (cond (Nat.ble (Nat.add k p.paid) (Nat.add p.bound (Nat.sub (Nat.sub (ws.countP (fun w : q06 => q5e p.domain w.1)) (q6O p.domain.toNat (q6Q p.domain.toNat a.1) ka)) (q6O p.domain.toNat (q6Q p.domain.toNat b.1) kb)))) (q6K p.domain.toNat (zN op (q6Q p.domain.toNat a.1) (q6Q p.domain.toNat b.1))) false)) = true := h
  rw [qaE,q6L,q6J,q6J,q6J,q6P,q6P] at h
  have ca : q5e p.domain (bin op a.1 b.1)=true → q0T u p.domain p.wires (bin op a.1 b.1)=true := by
    intro zc
    simp only [q0T,q5e,Bool.or_eq_true] at zc ⊢
    exact Or.inl (Or.inl zc)
  simp only [Nat.add_eq,Nat.sub_eq,Nat.succ_eq_add_one,Bool.and_eq_true,Nat.beq_eq] at h
  obtain ⟨hu,h⟩ := h
  simp only [q9F,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq]
  refine ⟨⟨hu,?_⟩,?_⟩
  all_goals
    generalize ws.countP (fun w => q5e p.domain w.1) - q1Z (fun w : q06 => q5e p.domain w.1) a ka -
      q1Z (fun w : q06 => q5e p.domain w.1) b kb = c at h ⊢
    generalize q5e p.domain (bin op a.1 b.1)=r at h ca ⊢
    generalize q0T u p.domain p.wires (bin op a.1 b.1)=q at h ca ⊢
    cases h1 : Nat.ble (k+p.paid+1) (p.bound+c)
    · rw [h1] at h
      cases h2 : Nat.ble (k+p.paid) (p.bound+c)
      · simp [h2] at h
      · have := Nat.ble_eq.mp h2
        simp only [h2,cond_true,cond_false] at h
        subst h
        rw [ca rfl]
        simp <;> omega
    · rw [h1] at h
      have l1 := Nat.ble_eq.mp h1
      simp only [cond_true,Bool.or_eq_true,Bool.and_eq_true,Nat.ble_eq] at h
      rcases h with rfl | ⟨l2,ha,hb⟩
      · simp <;> omega
      · first
        | (have : (!q).toNat ≤ 1 := Bool.toNat_le _
           omega)
        | simp [ha,hb]


theorem q0O (m : Nat) (l : List Nat) : q0M m l=true ↔ m ∈ l := by
  induction l with
  | nil => simp [q0M]
  | cons a l ih =>
    change or (Nat.beq m a) (q0M m l)=true ↔ _
    rw [Bool.or_eq_true,ih,Nat.beq_eq,List.mem_cons]


noncomputable def q5M (fl : Nat → Option (List Nat)) (l : q0a) (i j op : Nat) (ka kb : Bool) : Bool :=
  q3c (l.2.2.2.2.1.getD i 0) fun x => q3c (l.2.2.2.2.1.getD j 0) fun y => q3c (zN op x y) fun z =>
  Option.rec false (fun ys => q3h (fun v => v) ys fun ys =>
    and (q0M z ys) (and (l.2.2.2.2.1.all fun v => or (and (not ka) (Nat.beq v x)) (or (and (not kb) (Nat.beq v y)) (q0M v ys)))
      (ys.all fun v => or (Nat.beq v z) (and (and (or ka (not (Nat.beq v x))) (or kb (not (Nat.beq v y)))) (q0M v l.2.2.2.2.1)))))
    (fl (Nat.add (kwN z) (Nat.sub (Nat.sub l.2.2.2.2.2 (cond ka 0 (kwN x))) (cond kb 0 (kwN y)))))


theorem q5o (xs : List Sig) : q5n xs = (xs.map q5p).sum := by
  have go (a : Nat) : xs.foldl (fun v x => v+q5p x) a = a+(xs.map q5p).sum := by
    induction xs generalizing a with
    | nil => rfl
    | cons x xs ih => rw [List.foldl_cons,ih,List.map_cons,List.sum_cons,Nat.add_assoc]
  exact (go 0).trans (Nat.zero_add _)


theorem q2F (f : q06 → Nat) {ws : List q06} {a b : q06} (ha : a ∈ ws) (hb : b ∈ ws) (ne : a≠b) (ka kb : Bool) :
    ((q2D ws a b ka kb).map f).sum = (ws.map f).sum - (cond ka 0 (f a)) - (cond kb 0 (f b)) := by
  have er {l : List q06} {x : q06} (hx : x ∈ l) : (l.map f).sum = f x + ((l.erase x).map f).sum := by
    have := ((List.perm_cons_erase hx).map f).sum_eq
    rwa [List.map_cons,List.sum_cons] at this
  have hm : b ∈ ws.erase a := (List.mem_erase_of_ne (Ne.symm ne)).mpr hb
  have e1 := er ha
  have e2 := er hb
  have e3 := er hm
  cases ka <;> cases kb <;> simp only [q2D,q2A,Bool.false_eq_true,ite_true,ite_false,cond_true,cond_false] <;> omega


theorem q33 {u p k ws a b op ka kb} (ha : a∈ws) (hb : b∈ws) (ne : a≠b) (al : q0J u op=true)
    (h : q9F u p ws k a b op ka kb=true) :
    q8f u p k ((q2D ws a b ka kb).map Prod.fst) (q6D op a b)=true := by
  let const := fun w : q06 => q5e p.domain w.1
  let z := bin op a.1 b.1
  let rest := q2D ws a b ka kb
  have ck := q5j const ws a b ka kb
  change ws.countP const - q1Z const a ka - q1Z const b kb ≤ rest.countP const at ck
  simp only [q9F,Bool.and_eq_true,beq_iff_eq,decide_eq_true_eq] at h
  obtain ⟨⟨hu,hc⟩,hz⟩ := h
  have sum := q2F (qac u p) ha hb ne ka kb
  rw [hu] at sum
  have zs : ((q2D ws a b ka kb).map (qac u p)).sum=0 := by omega
  have hs : (rest.map Prod.fst).all (q0T u p.domain p.wires)=true := by
    apply List.all_eq_true.mpr
    intro _ hm
    obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hm
    have v := List.sum_eq_zero_iff.mp zs _ (List.mem_map_of_mem hw)
    cases e : q0T u p.domain p.wires w.1
    · simp [qac,e] at v
    · rfl
  have opOK : (!(!q0T u p.domain p.wires z) || q1J u p.domain p.wires (q6D op a b))=true := by
    simp only [Bool.or_eq_true,Bool.and_eq_true] at hz
    rcases hz with hz | ⟨x,y⟩
    · simp [z,hz]
    · simp [q1J,q6D,x,y,al]
  change k+p.paid+(!q0T u p.domain p.wires z).toNat < p.bound+(ws.countP const - q1Z const a ka -
        q1Z const b kb+(q5e p.domain z).toNat) at hc
  dsimp only [rest] at hs
  have ez : q1K (q6D op a b)=z := rfl
  simp only [q8f,ez,hs,opOK,Bool.and_true,decide_eq_true_eq,List.countP_cons,
      List.countP_map,Function.comp_def]
  change k+p.paid+(!q0T u p.domain p.wires z).toNat <
      p.bound+(rest.countP const + if q5e p.domain z then 1 else 0)
  cases hc' : q5e p.domain z <;> simp [hc'] at hc ⊢ <;> omega


theorem qaF (op : Nat) (a b : Sig) : zN op a.toNat b.toNat = (bin op a b).toNat := by
  have e (v : Sig) : q6Q one.toNat v = v.toNat := by
    rw [q6R]
    congr 1
    exact BitVec.and_allOnes
  have := qaE op one a b
  rwa [e,e,e] at this


theorem q52 (ws : List q06) (i : Nat) :
    (ws.map (fun w : q06 => w.1.toNat)).getD i 0 = (ws.getD i q2z).1.toNat := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases ws[i]? with
  | none =>
    have z0 : zero.toNat=0 := by simp [zero]
    exact z0.symm
  | some v => rfl


theorem qav {c : q0b} {i j} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) : (q21 c i).1 ≠ (q21 c j).1 := by
  have gi : q21 c i = c.2.2.1[i] := by simp [q21,List.getD_eq_getElem?_getD,hi]
  have gj : q21 c j = c.2.2.1[j] := by simp [q21,List.getD_eq_getElem?_getD,hj]
  rw [gi,gj]
  intro e
  apply hij
  apply (List.Nodup.getElem_inj_iff nd (hi:=by simpa using hi) (hj:=by simpa using hj)).mp
  simpa using e


theorem q5N {c : q0b} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (hi : i<c.2.2.1.length) (hj : j<c.2.2.1.length) (hij : i≠j) (h : q5M fl (q5C c) i j op ka kb=true) :
    (c.2.2.2.2.2 (q5n (q1K (q6D op (q21 c i) (q21 c j)) ::
      (q2D c.2.2.1 (q21 c i) (q21 c j) ka kb).map Prod.fst))).any (q8b
      (q1K (q6D op (q21 c i) (q21 c j)) ::
      (q2D c.2.2.1 (q21 c i) (q21 c j) ka kb).map Prod.fst))=true := by
  have mem (t) (ht : t<c.2.2.1.length) : q21 c t ∈ c.2.2.1 := by
    simp [q21,List.getD_eq_getElem?_getD,ht]
  have hne := qav nd hi hj hij
  have ha := mem i hi
  have hb := mem j hj
  have hab : q21 c i ≠ q21 c j := fun e => hne (congrArg Prod.fst e)
  have kv (v : Sig) := q5m nd ha hb ka kb v
  have sum := q2F (fun w : q06 => q5p w.1) ha hb hab ka kb
  have wi : q21 c i = c.2.2.1.getD i q2z := rfl
  have wj : q21 c j = c.2.2.1.getD j q2z := rfl
  simp only [q5M,q5C,q3n,q52,←wi,←wj,qaF] at h
  generalize q21 c i=a at *
  generalize q21 c j=b at *
  change Option.rec false _ (fl (q5p (bin op a.1 b.1)+(((c.2.2.1.map (fun w : q06 => w.1.toNat)).map kwN).sum -
    (cond ka 0 (q5p a.1)) - (cond kb 0 (q5p b.1)))))=true at h
  have tot : ((c.2.2.1.map (fun w : q06 => w.1.toNat)).map kwN).sum = (c.2.2.1.map (fun w : q06 => q5p w.1)).sum := by
    rw [List.map_map]
    rfl
  rw [tot,←sum] at h
  have tag : q5n (q1K (q6D op a b) :: (q2D c.2.2.1 a b ka kb).map Prod.fst) =
      q5p (bin op a.1 b.1)+((q2D c.2.2.1 a b ka kb).map (fun w : q06 => q5p w.1)).sum := by
    rw [q5o,List.map_cons,List.sum_cons,List.map_map]
    rfl
  rw [←tag] at h
  generalize q5n (q1K (q6D op a b) :: (q2D c.2.2.1 a b ka kb).map Prod.fst)=t at h ⊢
  cases hf : fl t with
  | none => simp [hf] at h
  | some ys =>
    obtain ⟨xs,hx,rfl⟩ := hfl t ys hf
    rw [hf] at h
    simp only [q3i,List.map_id',Bool.and_eq_true,List.all_eq_true,Bool.or_eq_true,q0O,Nat.beq_eq,Bool.not_eq_true'] at h
    obtain ⟨h1,h2,h3⟩ := h
    have back {v : Sig} (hv : v.toNat ∈ xs.map BitVec.toNat) : v ∈ xs := by
      obtain ⟨w,hw,e⟩ := List.mem_map.mp hv
      exact BitVec.toNat_inj.mp e ▸ hw
    apply List.any_eq_true.mpr
    refine ⟨xs,hx,?_⟩
    simp only [q8b,Bool.and_eq_true,List.all_eq_true,List.contains_eq_mem,decide_eq_true_eq]
    constructor
    · intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact back h1
      · obtain ⟨hw,va,vb⟩ := (kv v).mp hv
        obtain ⟨w,hm,rfl⟩ := List.mem_map.mp hw
        rcases h2 _ (List.mem_map_of_mem hm) with ⟨x,y⟩ | ⟨x,y⟩ | x
        · rcases va with va | va
          · exact absurd (BitVec.toNat_inj.mp y) va
          · simp [va] at x
        · rcases vb with vb | vb
          · exact absurd (BitVec.toNat_inj.mp y) vb
          · simp [vb] at x
        · exact back x
    · intro v hv
      rcases h3 _ (List.mem_map_of_mem hv) with x | ⟨⟨x,y⟩,m⟩
      · exact List.mem_cons.mpr (Or.inl (BitVec.toNat_inj.mp x))
      · refine List.mem_cons_of_mem _ ((kv v).mpr ⟨?_,?_,?_⟩)
        · obtain ⟨w,hw,e⟩ := List.mem_map.mp m
          exact BitVec.toNat_inj.mp e ▸ List.mem_map_of_mem hw
        · rcases x with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x
        · rcases y with x | x
          · exact Or.inr x
          · refine Or.inl fun e => ?_
            subst e
            simp at x


noncomputable def q30 (fl : Nat → Option (List Nat)) (l : q0a) (i j op : Nat) (ka kb : Bool) : Bool :=
  or (and (and (Nat.ble (Nat.succ i) l.2.1) (and (Nat.ble (Nat.succ j) l.2.1) (and (Nat.ble (Nat.succ op) l.2.2.1) (not (Nat.beq i j)))))
    (or (l.2.2.2.1.any fun s => q32 s i j op ka kb) (q5M fl l i j op ka kb))) (q1C l.1 i j op ka kb)


theorem q31 {c : q0b} {fl i j op ka kb} (nd : (c.2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ xs ∈ c.2.2.2.2.2 tag, ys=xs.map BitVec.toNat)
    (h : q30 fl (q5C c) i j op ka kb=true) :
    q1C c i j op ka kb=true := by
  simp only [q30,Bool.or_eq_true,Bool.and_eq_true] at h
  rcases h with ⟨⟨hi,hj,ho,hn⟩,h | h⟩ | h
  · have hi := Nat.ble_eq.mp hi
    have hj := Nat.ble_eq.mp hj
    have ho := Nat.ble_eq.mp ho
    change Nat.succ i ≤ c.2.2.1.length at hi
    change Nat.succ j ≤ c.2.2.1.length at hj
    change Nat.succ op ≤ cond c.2.2.2.1.2 4 2 at ho
    have al : q0J c.2.2.2.1.2 op=true := by
      cases hu : c.2.2.2.1.2 <;> simp [hu] at ho <;> simp [q0J] <;> omega
    have mem (t) (ht : t<c.2.2.1.length) : q21 c t ∈ c.2.2.1 := by
      simp [q21,List.getD_eq_getElem?_getD,ht]
    obtain ⟨_,hm,ok⟩ := List.any_eq_true.mp h
    obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    have hne := qav nd hi hj (fun e => by simp [e] at hn)
    have closed := q33 (mem i hi) (mem j hj) (fun e => hne (congrArg Prod.fst e)) al (q36 ok)
    have cut : c.2.2.2.2.1.any (fun p => q8f c.2.2.2.1.2 p (c.1-1)
        ((q2D c.2.2.1 (q21 c i) (q21 c j) ka kb).map Prod.fst)
        (q6D op (q21 c i) (q21 c j)))=true :=
      List.any_eq_true.mpr ⟨p,hp,closed⟩
    simp only [q1C,q2Q,q1M,cut,Bool.or_true]
    repeat' split
    all_goals rfl
  · have cut := q5N nd hfl (Nat.ble_eq.mp hi) (Nat.ble_eq.mp hj) (fun e => by simp [e] at hn) h
    simp only [q1C,q2Q,q1M,cut,Bool.true_or]
    repeat' split
    all_goals rfl
  · exact h


def q9N (v t : Nat) : Nat := cond (Nat.beq t (v &&& 15)) (v >>> 4) (cond (Nat.beq t (v >>> 4)) (v &&& 15) t)


def qar (v : Nat) : Bool := and (Nat.ble ((v &&& 15)+1) (v >>> 4)) (Nat.ble ((v >>> 4)+1) 9)


set_option maxRecDepth 8192 in
theorem q9Q : ∀ v : Fin 144, qar v.val=true → ∀ t : Fin 9, q9N v.val t.val<9 ∧
    qaB (q9O v.val) (inputs.getD t.val zero) = inputs.getD (q9N v.val t.val) zero := by decide +kernel


theorem q9P {v t : Nat} (hv : qar v=true) (ht : t<9) : q9N v t<9 ∧
    qaB (q9O v) (inputs.getD t zero) = inputs.getD (q9N v t) zero := by
  have lt : v<144 := by
    simp only [qar,Bool.and_eq_true,Nat.ble_eq,Nat.shiftRight_eq_div_pow] at hv
    omega
  exact q9Q ⟨v,lt⟩ hv ⟨t,ht⟩


def q57 (perm : List Nat) (t : Nat) : Nat := perm.foldl (fun t v => q9N v t) t


theorem q58 {perm : List Nat} (ok : perm.all qar=true) {t : Nat} (ht : t<9) :
    q6G (perm.map q9O).reverse (inputs.getD t zero) = inputs.getD (q57 perm t) zero := by
  rw [q6G,List.foldr_reverse,List.foldl_map]
  induction perm generalizing t with
  | nil => rfl
  | cons v perm ih =>
    simp only [List.all_cons,Bool.and_eq_true] at ok
    obtain ⟨lt,e⟩ := q9P ok.1 ht
    rw [List.foldl_cons,e,ih ok.2 lt]
    rfl


noncomputable def q2w : Nat → Nat → List Nat → List Nat
  | 0,_,ws => ws
  | n+1,bits,ws => q3c (zN ((bits >>> 8) &&& 3) (ws.getD (bits &&& 15) 0) (ws.getD ((bits >>> 4) &&& 15) 0))
      fun z => q2w n (bits >>> 10) (ws++[z])


theorem q2x (F : Sig → Nat) (F0 : F zero=0) (Fb : ∀ op a b, F (bin op a b)=zN op (F a) (F b))
    (n bits : Nat) (ds : List q06) :
    (q2v n bits ds).map (fun w => F w.1) = q2w n bits (ds.map fun w => F w.1) := by
  have gd (ds : List q06) (i : Nat) : (ds.map fun w => F w.1).getD i 0 = F (ds.getD i q2z).1 := by
    simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
    cases ds[i]? with
    | none => exact F0.symm
    | some v => rfl
  induction n generalizing bits ds with
  | zero => rfl
  | succ n ih =>
    rw [q2w,q3n,q2v,ih,gd,gd,←Fb,List.map_append]
    rfl


theorem q8i {α β : Type} (f : α → β) (bits : Nat) (ws : List α) :
    (q8h bits ws).map f = q8h bits (ws.map f) := by
  induction ws generalizing bits with
  | nil => rfl
  | cons w ws ih =>
    rw [List.map_cons,q8h,q8h]
    split
    · rw [List.map_cons,ih]
    · exact ih _


noncomputable def q34 (g : Forest) (k i : Nat) (perm : List Nat) : List Nat :=
  let raw := (q8k g.mask).map fun e => (inputs.getD (q57 perm e.1) zero).toNat
  let (_,depth,_,_,_,_,_,data) := g.levels k
  let len := 10*depth
  q3c (q3p (g.levels k) (q8k g.mask).length i) fun rec =>
  q8h (rec >>> len) (q2w depth (rec &&& ((1 <<< len)-1)) raw)


theorem q35 (g : Forest) (k i : Nat) {perm : List Nat} (ok : perm.all qar=true) :
    q34 g k i perm = ((q9I g k i).map (q6G (perm.map q9O).reverse)).map BitVec.toNat := by
  let ms := (perm.map q9O).reverse
  let F (a : Sig) : Nat := (q6G ms a).toNat
  have F0 : F zero=0 := by
    change (q6G ms zero).toNat=0
    rw [q6H,(q7S _).1]
    simp [zero]
  have Fb (op a b) : F (bin op a b)=zN op (F a) (F b) := by
    change (q6G ms (bin op a b)).toNat = zN op (q6G ms a).toNat (q6G ms b).toNat
    rw [qaF,q6H,q7R,q6H,q6H]
  have raw : (qaw g).map (fun w => F w.1) = (q8k g.mask).map fun e => (inputs.getD (q57 perm e.1) zero).toNat := by
    simp only [qaw,q7I,List.map_map]
    apply List.map_congr_left
    rintro ⟨j,a⟩ hm
    obtain ⟨hj,rfl⟩ := q8l hm
    exact congrArg BitVec.toNat (q58 ok hj)
  have len : (qaw g).length = (q8k g.mask).length := by simp [qaw,q7I]
  unfold q34 q9I q7O
  rcases g.levels k with ⟨a,depth,b,c,d,e,f,data⟩
  simp only [q3n,q9J,len]
  rw [List.map_map,List.map_map,q8i,←raw,←q2x F F0 Fb]
  rfl


noncomputable def q5O (g : Forest) (k : Nat) (pair : Nat × Nat) : Option (List Nat) :=
  if pair.1 ≥ (g.levels k).1 then none else
    (g.autos[pair.2]?).bind fun perm => cond (perm.all qar) (some (q34 g k pair.1 perm)) none


noncomputable def q38 (g : Forest) (k : Nat) : Nat → Option (List Nat) := fun tag => (g.index k tag).bind (q5O g (k-1))


noncomputable def q0Z (fl : Nat → Option (List Nat)) (u : Bool) (b : q00) (xs : List q0a) (i j op : Nat) (ka kb : Bool) :=
  let (k,n,r,_,cov) := b
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  if len>k then true else
    let a := q5F b i
    let b' := q5F b j
    let z := q7f op a b'
    let mask := q3t r (qa2 cov (q7d (!u) a) (q7d (!u) b') ka kb ||| q7d (!u) z)
    q79 (fun c => q30 fl c i j op ka kb) mask xs


theorem q10 {fl u} (k n) (xs : List q0b) {i j op : Nat} {ka kb}
    (hi : i<n) (hj : j<n) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (pass : q0Z fl u (q6e k n xs) (xs.map q5C) i j op ka kb=true) :
    q1C xs[q] i j op ka kb=true := by
  let len := 1+(n-(if ka then 0 else 1)-(if kb then 0 else 1))
  have eval : q1C xs[q] i j op ka kb =
      if len>k then true else if q1T xs[q] (!u) ka kb op i j != BitVec.allOnes 152 then true
      else if !q7C (q2u op (q21 xs[q] i) (q21 xs[q] j)).1 ||
        xs[q].2.2.1.any (fun v => v.1==(q2u op (q21 xs[q] i) (q21 xs[q] j)).1)
      then true else q1M u xs[q].2.2.2.2.1 xs[q].2.2.2.2.2 (k-1)
        ((q2D xs[q].2.2.1 (q21 xs[q] i) (q21 xs[q] j) ka kb).map Prod.fst)
        (q6D op (q21 xs[q] i) (q21 xs[q] j)) := by
    simp only [q1C,q2Q,budget,arity,mode,len,q1T] <;> rfl
  by_cases small : len>k
  · simp [eval,small]
  · let r := qaf xs.length
    let a := q5F (q6e k n xs) i
    let b := q5F (q6e k n xs) j
    let cov := q7e (fun c : q0b => c.2.2.2.1.1) xs
    change (if len>k then true else q79 _ (q3t r
       (qa2 cov (q7d (!u) a) (q7d (!u) b) ka kb |||
        q7d (!u) (q7f op a b))) (xs.map q5C)) = true at pass
    rw [if_neg small] at pass
    have ca : a = _ := q5G k n xs hi
    have cb : b = _ := q5G k n xs hj
    dsimp only [r,cov] at pass
    rw [ca,cb,q7i,q7h,q7h,q7h,qa3,q5I] at pass
    by_cases hit : q1T xs[q] (!u) ka kb op i j = BitVec.allOnes 152
    · apply q31 nd hfl
      have m := q6l _ _ _ q (by simpa using hq) (by
        rw [q6k _ _ _ hq]
        exact beq_iff_eq.mpr hit) pass
      simpa only [List.getElem_map] using m
    · rw [eval,if_neg small,if_pos (bne_iff_ne.mpr hit)]


noncomputable def q11 (fl : Nat → Option (List Nat)) (u : Bool) (b : q00) (xs : List q0a) (i j op : Nat) :=
  let f := q0Z fl u b xs i j op
  f false false && f true false && f false true && f true true


noncomputable def q12 (fl : Nat → Option (List Nat)) (u : Bool) (b : q00) (xs : List q0a) (i : Nat) (js : List Nat) :=
    js.all (fun j => (q7a u).all (q11 fl u b xs i j))


noncomputable def q13 (fl : Nat → Option (List Nat)) (u : Bool) (b : q00) (xs : List q0a) : List Nat → Bool
  | [] => true
  | i::js => q12 fl u b xs i js && q13 fl u b xs js


theorem q14 {fl u} (k n) (xs : List q0b) {q : Nat} (hq : q<xs.length)
    (budget : xs[q].1=k) (arity : xs[q].2.1=n) (mode : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (js : List Nat)
    (bounds : ∀ j ∈ js, j<n) (allRows : q13 fl u (q6e k n xs) (xs.map q5C) js=true) :
    qa6 xs[q] (js.map (q21 xs[q])) = true := by
  induction js with
  | nil => rfl
  | cons i js ih =>
    simp only [q13,Bool.and_eq_true,q12,List.all_eq_true] at allRows
    simp only [List.map_cons,qa6,qa9,Bool.and_eq_true,List.all_eq_true,List.mem_map]
    have hi := bounds i List.mem_cons_self
    refine ⟨?_,ih (fun j hj => bounds j (List.mem_cons_of_mem _ hj)) allRows.2⟩
    rintro _ ⟨j,hj,rfl⟩ op hop
    have hj' := bounds j (List.mem_cons_of_mem _ hj)
    rw [mode] at hop
    have pass := allRows.1 j hj op hop
    have check := @q10 fl u k n xs i j op
    simp only [q11,Bool.and_eq_true] at pass
    simp only [qa7,Bool.and_eq_true]
    exact ⟨⟨⟨check hi hj' hq budget arity mode nd hfl pass.1.1.1,check hi hj' hq budget arity mode nd hfl pass.1.1.2⟩,
      check hi hj' hq budget arity mode nd hfl pass.1.2⟩,check hi hj' hq budget arity mode nd hfl pass.2⟩


noncomputable def q89 (fl : Nat → Option (List Nat)) (u : Bool) (k n : Nat) (xs : List q0b) :=
    q13 fl u (q6e k n xs) (xs.map q5C) (List.range n)


theorem q8a {fl u k n} {xs : List q0b} {q} (hq : q<xs.length)
    (hb : xs[q].1=k) (ha : xs[q].2.1=n) (hm : xs[q].2.2.2.1.2=u) (nd : (xs[q].2.2.1.map Prod.fst).Nodup)
    (hfl : ∀ tag ys, fl tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat)
    (hn : xs[q].2.2.1.length=n)
    (pass : q89 fl u k n xs=true) : qa6 xs[q] xs[q].2.2.1=true := by
  have all := q14 k n xs hq hb ha hm nd hfl (List.range n) (fun _ => List.mem_range.mp) pass
  have eq : (List.range n).map (q21 xs[q]) = xs[q].2.2.1 := by
    apply List.ext_getElem
    · simp [hn]
    · intro i h1 h2
      simp [q21,List.getD_eq_getElem?_getD,h2]
  rwa [eq] at all


def q20 (g : Forest) (k i : Nat) : q0b :=
  let raw := qaw g
  let (num,depth,cw,iw,pw,offw,lw,data) := g.levels k
  let (ops,bank,ws) := q7O g k i
  let rules := (q3o (g.levels k) raw.length i).filterMap (fun (a,b) => q1r g ops depth bank a b)
  let ls := fun tag => ((g.index k tag).bind (q5P g (k-1))).toList
  (k,ws.length,ws,q7v g.mode ws,rules,ls)


theorem q39 (g : Forest) (k i tag : Nat) (ys) (h : q38 g k tag=some ys) :
    ∃ xs ∈ (q20 g k i).2.2.2.2.2 tag, ys=xs.map BitVec.toNat := by
  change ∃ xs ∈ ((g.index k tag).bind (q5P g (k-1))).toList, _
  unfold q38 at h
  cases hp : g.index k tag with
  | none => simp [hp] at h
  | some pair =>
    simp only [hp,Option.bind_some,q5O] at h
    simp only [Option.bind_some,q5P]
    split at h
    · contradiction
    next v =>
      cases ha : g.autos[pair.2]? with
      | none => simp [ha] at h
      | some perm =>
        simp only [ha,Option.bind_some] at h
        cases hv : perm.all qar with
        | false => simp [hv] at h
        | true =>
          simp only [hv,cond_true,Option.some.injEq] at h
          refine ⟨(q9I g (k-1) pair.1).map (q6G (perm.map q9O).reverse),?_,?_⟩
          · simp [v]
          · exact h.symm.trans (q35 g _ _ hv)


def q7x (T : Sig) (c : q0b) :=
  let ws := c.2.2.1.map Prod.fst
  decide ws.Nodup && !(ws.contains T)


theorem q3s (g : Forest) (k i : Nat) :
    q6S g k i = (q7x (qa5 g) (q20 g k i) &&
      (if k=0 then true else qa6 (q20 g k i) (q20 g k i).2.2.1)) := rfl


theorem q6f {g k start n} (h : ∀ (i : Nat), start ≤ i → i < start + n → q6S g k i = true) :
    q1j g k start n=true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [q1j,Bool.and_eq_true]
    exact ⟨h _ (by omega) (by omega),ih (fun i le lt => h i le (by omega))⟩


def q22 (g : Forest) (k start n : Nat) :=
  ((List.range n).map (start+·)).map (q20 g k)


def q56 (g : Forest) (k start n ar : Nat) :=
  (q22 g k start n).all (fun c => c.2.1==ar && q7x (qa5 g) c)


noncomputable def q85 (g : Forest) (k start n ar lo len : Nat) :=
  let xs := q22 g k start n
  let b := q6e k ar xs
  q3f xs fun ys => (List.range len).all (fun d =>
    let i := lo+d
    q12 (q38 g k) g.mode b ys i (List.range' (i+1) (ar-(i+1))))


theorem q86 {g k start n ar lo len} (h : q85 g k start n ar lo len=true)
    (i : Nat) (l : lo ≤ i) (r : i < lo+len) :
    q12 (q38 g k) g.mode (q6e k ar (q22 g k start n)) ((q22 g k start n).map q5C)
      i (List.range' (i+1) (ar-(i+1)))=true := by
  simp only [q85,q3g] at h
  have ha := List.all_eq_true.mp h (i-lo) (List.mem_range.mpr (by omega))
  simpa only [Nat.add_sub_of_le l] using ha


theorem q87 {g k start n ar lo a b}
    (h : q85 g k start n ar lo a=true) (t : q85 g k start n ar (lo+a) b=true) :
    q85 g k start n ar lo (a+b)=true := by
  simp only [q85,q3g]
  apply List.all_eq_true.mpr
  intro j hj
  have jlt := List.mem_range.mp hj
  by_cases first : j<a
  · exact q86 h (lo+j) (by omega) (by omega)
  · exact q86 t (lo+j) (by omega) (by omega)


theorem q2t {g k start n ar} (h : q85 g k start n ar 0 ar=true) :
    q89 (q38 g k) g.mode k ar (q22 g k start n)=true := by
  let xs := q22 g k start n
  have go (lo num : Nat) (eq : lo+num=ar) :
      q13 (q38 g k) g.mode (q6e k ar xs) (xs.map q5C) (List.range' lo num)=true := by
    induction num generalizing lo with
    | zero => rfl
    | succ num ih =>
      simp only [List.range'_succ,q13,Bool.and_eq_true]
      refine ⟨?_,ih (lo+1) (by omega)⟩
      have ok := q86 h lo (by omega) (by omega)
      simpa only [show ar-(lo+1)=num by omega] using ok
  unfold q89
  rw [List.range_eq_range']
  exact go 0 ar (by omega)


theorem q2s {g k start n ar} (hd : q56 g k start n ar=true)
    (h : q85 g k start n ar 0 ar=true) : q1j g k start n=true := by
  apply q6f
  intro i lo hi
  let xs := q22 g k start n
  have hm : q20 g k i ∈ xs := by
    apply List.mem_map.mpr
    exact ⟨i,List.mem_map.mpr ⟨i-start,List.mem_range.mpr (by omega),by omega⟩,rfl⟩
  obtain ⟨q,hq,e⟩ := List.getElem_of_mem hm
  have one := List.all_eq_true.mp hd _ hm
  simp only [Bool.and_eq_true,beq_iff_eq] at one
  have hb : xs[q].1=k := by rw [e]; rfl
  have ha : xs[q].2.1=ar := e ▸ one.1
  have nd : (xs[q].2.2.1.map Prod.fst).Nodup := by
    have p := one.2
    simp only [q7x,Bool.and_eq_true,decide_eq_true_eq] at p
    rw [e]
    exact p.1
  have hfl : ∀ tag ys, q38 g k tag=some ys → ∃ zs ∈ xs[q].2.2.2.2.2 tag, ys=zs.map BitVec.toNat := by
    rw [e]
    exact fun tag ys h => q39 g k i tag ys h
  have hm : xs[q].2.2.2.1.2=g.mode := by rw [e]; rfl
  have hn : xs[q].2.2.1.length=ar := by rw [e]; exact one.1
  rw [q3s,Bool.and_eq_true]
  refine ⟨one.2,?_⟩
  split
  · rfl
  · exact e ▸ q8a hq hb ha hm nd hfl hn (q2t h)


def q1p (g : Forest) (k start n ar lo num : Nat) : Nat → Prop
  | 0 => q85 g k start n ar lo num=true
  | d+1 => q1p g k start n ar lo (num/2) d ∧ q1p g k start n ar (lo+num/2) (num-num/2) d


theorem q1q {g k start n ar lo num d} (h : q1p g k start n ar lo num d) :
    q85 g k start n ar lo num=true := by
  induction d generalizing lo num with
  | zero => exact h
  | succ d ih =>
    have v := q87 (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self num 2)] using v


def q1w (g : Forest) (k start n ar rows : Nat) : Nat → Prop
  | 0 => q56 g k start n ar=true ∧ q1p g k start n ar 0 ar rows
  | d+1 => q1w g k start (n/2) ar rows d ∧ q1w g k (start+n/2) (n-n/2) ar rows d


theorem q1x {g k start n ar rows d} (h : q1w g k start n ar rows d) :
    q1j g k start n=true := by
  induction d generalizing start n with
  | zero => exact q2s h.1 (q1q h.2)
  | succ d ih =>
    have v := q1l (ih h.1) (ih h.2)
    simpa only [Nat.add_sub_of_le (Nat.div_le_self n 2)] using v


def q5R {α} (f : α → Bool) (xs : List α) : Nat → Prop
  | 0 => xs.all f=true
  | d+1 => q5R f (xs.take (xs.length/2)) d ∧ q5R f (xs.drop (xs.length/2)) d


theorem q7m {α f xs d} (h : @q5R α f xs d) : xs.all f=true := by
  induction d generalizing xs with
  | zero => exact h
  | succ d ih =>
    have ap : ((xs.take (xs.length/2)) ++ (xs.drop (xs.length/2))).all f=true := by
      simp only [List.all_append,ih h.1,ih h.2,Bool.and_self]
    simpa only [List.take_append_drop] using ap


theorem q2r {u} {m cap : Nat} {prior : Nat → Nat} {ws : List Sig}
    (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q)) (ci : q03)
    (ok : q1O m ci prior = true)
    (cut : (decide ws.Nodup && q7s u (q9K ci.1 ci.2.1) ci.2.2.2.2 cap 0 (varsX (q7J m ci)) ws)=true) :
    q08 u (graphGoal m) cap ws.toFinset := by
  simp only [Bool.and_eq_true,decide_eq_true_eq] at cut
  exact q7t (q1Q ci prior low ok) [] rfl cut.1 cut.2


theorem q59 {u} {g : Forest} {m cap i : Nat} {prior : Nat → Nat} {ws : List Sig}
    (hm : g.mask=m) (hu : g.mode=u) (low : ∀ q, Lower u (varsX q) (graphGoal q) (prior q))
    (geom : q54 g prior = true) (blocks : q1G g cap)
    (idx : q5a g cap i ws = true) : q08 u (graphGoal m) cap ws.toFinset := by
  subst hm
  subst hu
  exact q83 low geom blocks (Nat.le_refl _) idx


def q2N (m hints : Nat) : Bool :=
  let xs := q53 m hints
  q7C (graphGoal m) && q1D (graphGoal m) (vars m) xs && (xs.map Prod.fst == vars m)


theorem q7r {u} {m hints cap : Nat} (ok : q2N m hints = true)
    (a : q08 u (graphGoal m) cap (vars m).toFinset) : Lower u (vars m) (graphGoal m) (cap+1) := by
  simp only [q2N,Bool.and_eq_true,beq_iff_eq] at ok
  apply q6b (q7G _ ok.1.1) (q2P ok.1.2).1 (q2P ok.1.2).2 _ a
  intro v hv
  apply q2O ok.1.2 v
  rw [ok.2]
  exact List.mem_toFinset.mpr hv


def q3H (i : Nat) : Nat := 0xf


def q3J : q0e := (1,0,1,0,0,0,0,q3H)


def q3L : Array (q01 × q01) := #[(0xfffffffffffffffffffffffffffffffffffff3,0x62),(0xffffffffffffffffffffffffffffffffffffbf,0xffffffffffffffffffffffffffffffffffff99),(0x4c,0x4),(0x70,0x70),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]


def q3G : List q03 := []


def q3F : List (List Nat) := [[],[48,33]]


def q3K : Nat → q0e
  | 3 => q3J
  | _ => q2K


def q3I : Nat → Nat → Option (Nat × Nat)
  | _ => fun _ => none


def g15 : Forest := ⟨15,3,fun j => q3L[j]?.getD (0,0),q3G,q3F,q3K,q3I⟩


set_option maxHeartbeats 0 in
theorem q4V : q54 g15 (q1o []) = true := by
  simp only [q54,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,q7m (d:=0) ?_⟩,q7m (d:=0) ?_⟩
  all_goals simp only [q5R]
  all_goals repeat' apply And.intro
  all_goals decide +kernel


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8o : q1j g15 3 0 1=true := by decide +kernel


theorem q0q : q1j g15 3 0 1=true := q8o


theorem q9W : q1G g15 3 := by
  intro k hk
  interval_cases k
  · exact (rfl : q1j g15 0 0 0 = true)
  · exact (rfl : q1j g15 1 0 0 = true)
  · exact (rfl : q1j g15 2 0 0 = true)
  · exact q0q


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q60 : Lower true (vars 15) (graphGoal 15) 4 := q7r (hints:=8449) (by decide +kernel) (q59 (g:=g15) (i:=0) rfl rfl (q15 [] q0Y) q4V q9W (by decide +kernel))


def q5s := q2S [] 4 [(15,[]),(23,[64,48,32,16]),(27,[66,16]),(29,[50,65]),(30,[50,33,16,64]),(39,[80,64,48,32,16]),(57,[32,82,64,16]),(78,[96,80,64]),(83,[99,83,64,32,16]),(99,[48,96,83,64,32,16]),(135,[115,99,83,67]),(156,[112,96,48,50,33,81,64]),(163,[115,50,98,83,66,16]),(165,[114,33,97,82,50,65]),(166,[114,98,83,33,16,64]),(172,[114,50,99,48,33,81,64]),(177,[115,99,82,64,16]),(198,[115,96,83,64]),(281,[131,115,99,50,82,65]),(291,[131,115,50,98,83,66,16]),(300,[130,114,98,49,32,81,64]),(305,[131,115,99,82,64,16]),(312,[130,114,49,98,81,64]),(323,[131,115,98,83,66]),(326,[131,115,98,83,32,64]),(330,[130,114,97,82,16,64]),(332,[130,50,115,98,49,32,81,64]),(344,[130,50,115,49,98,81,64]),(353,[130,33,113,99,82,65]),(354,[130,33,50,113,99,82,16,64]),(396,[48,128,115,96,50,33,81,64]),(424,[129,33,115,48,98,81,64]),(480,[32,50,128,115,98,81,64])]


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qai : q09 true q5s := q2U (m:=15) q0Y q60 (by decide +kernel)


def q4o (i : Nat) : Nat := 0x11a20bf


def q4u : q0e := (1,0,3,0,0,0,0,q4o)


def q4q (i : Nat) : Nat := 0x30be670208000065000016357504004755c084


def q4n (i : Nat) : Nat := 0x40828fd20fd10


def q4t : q0e := (2,1,3,0,0,3,0,q4n)


def q4p (i : Nat) : Nat := 0x300


def q4m (i : Nat) : Nat := 0x5dd4520


def q4s : q0e := (1,2,3,0,0,0,0,q4m)


def q4w : Array (q01 × q01) := #[(0x2e44,0x2c52),(0x5a8a,0x5208),(0xffffffffffffffffffffffffffffffffffb4f7,0xffffffffffffffffffffffffffffffffffa0c7),(0xffffffffffffffffffffffffffffffffffcf79,0x4f30),(0x718c,0x108c),(0x0,0x0),(0x0,0x0),(0x0,0x0),(0x0,0x0)]


def q4l : List q03 := [(1,0,30,0,4),(16,0,15,0,4),(8,0,23,0,4),(4,0,27,0,4),(2,0,29,0,4)]


def q4k : List (List Nat) := [[],[65,50],[16,66],[16,32,48,64],[32,67],[32,49,64,16],[48,33],[48,65,32,33],[64,16,33,50],[64,49]]


def q4v : Nat → q0e
  | 6 => q4u
  | 5 => q4t
  | 4 => q4s
  | _ => q2K


def q4r : Nat → Nat → Option (Nat × Nat)
  | 6 => q5W 5 15 3 9 1 4 q4q
  | 5 => q5W 1 3 1 9 1 4 q4p
  | _ => fun _ => none


def g31 : Forest := ⟨31,6,fun j => q4w[j]?.getD (0,0),q4l,q4k,q4v,q4r⟩


set_option maxHeartbeats 0 in
theorem q4Y : q54 g31 (q1o q5s) = true := by
  simp only [q54,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,q7m (d:=0) ?_⟩,q7m (d:=1) ?_⟩
  all_goals simp only [q5R]
  all_goals repeat' apply And.intro
  all_goals decide +kernel


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8G : q1j g31 6 0 1=true := by decide +kernel


theorem q0B : q1j g31 6 0 1=true := q8G


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8F : q1j g31 5 0 2=true := by decide +kernel


theorem q0A : q1j g31 5 0 2=true := q8F


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8E : q1j g31 4 0 1=true := by decide +kernel


theorem q0z : q1j g31 4 0 1=true := q8E


theorem q9Z : q1G g31 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : q1j g31 0 0 0 = true)
  · exact (rfl : q1j g31 1 0 0 = true)
  · exact (rfl : q1j g31 2 0 0 = true)
  · exact (rfl : q1j g31 3 0 0 = true)
  · exact q0z
  · exact q0A
  · exact q0B


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q65 : Lower true (vars 31) (graphGoal 31) 7 := q7r (hints:=8449) (by decide +kernel) (q59 (g:=g31) (i:=0) rfl rfl (q15 q5s qai) q4Y q9Z (by decide +kernel))


def q5x := q2S q5s 7 [(31,[]),(167,[115,67,100,83]),(313,[131,115,65,50,98,81]),(334,[131,115,100,50,33,16,80]),(355,[131,50,66,116,99,82]),(428,[130,50,116,49,32,97,80])]


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qam : q09 true q5x := q2U (m:=31) qai q65 (by decide +kernel)


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q67 : Lower true (vars 47) (graphGoal 47) 5 := q7r (hints:=8449) (by decide +kernel) (q2r (prior:=q1o q5x) (q15 q5x qam) (8,0,39,0,4) (by decide +kernel) (by decide +kernel))


def q5z := q2S q5x 5 [(61,[50,65]),(91,[101,66,16]),(94,[101,50,33,16,64]),(181,[114,81,98,50,65]),(227,[83,82,114,99,66,16]),(230,[83,114,99,33,16,64])]


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qao : q09 true q5z := q2U (m:=47) qam q67 (by decide +kernel)


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q68 : Lower true (vars 55) (graphGoal 55) 5 := q7r (hints:=257) (by decide +kernel) (q2r (prior:=q1o q5z) (q15 q5z qao) (16,0,39,0,4) (by decide +kernel) (by decide +kernel))


def q5A := q2S q5z 5 [(55,[]),(59,[50,65]),(103,[82,98,66,16])]


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qap : q09 true q5A := q2U (m:=55) qao q68 (by decide +kernel)


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q69 : Lower true (vars 63) (graphGoal 63) 8 := q7r (hints:=8449) (by decide +kernel) (q2r (prior:=q1o q5A) (q15 q5A qap) (32,0,31,0,7) (by decide +kernel) (by decide +kernel))


def q5B := q2S q5A 8 [(63,[]),(95,[101,66,16]),(159,[117,101,67,32]),(359,[131,67,116,99,82,16]),(377,[128,81,67,112,97,32]),(462,[83,133,115,67,32,96]),(483,[83,80,132,115,96,32,16]),(492,[80,84,132,49,113,96])]


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qaq : q09 true q5B := q2U (m:=63) qap q69 (by decide +kernel)


def q3y (i : Nat) : Nat := 0x7213f


def q3C : q0e := (1,0,2,0,0,0,0,q3y)


def q3z (i : Nat) : Nat := 0x8000


def q3x (i : Nat) : Nat := 0x17e51


def q3B : q0e := (1,1,2,0,0,0,0,q3x)


def q3E : Array (q01 × q01) := #[(0xffffffffffffffffffffffffffffffffffed93,0x2d12),(0xffffffffffffffffffffffffffffffffff9467,0xffffffffffffffffffffffffffffffffff9025),(0x6e38,0x6618),(0x1bd8,0x19c0),(0x0,0x0),(0x63e4,0x42e4),(0x7e44,0x6e40),(0x0,0x0),(0x0,0x0)]


def q3w : List q03 := [(1,32,78,0,4),(12,0,99,0,4),(96,0,15,0,4),(0,8,99,4,5)]


def q3v : List (List Nat) := [[],[32,83]]


def q3D : Nat → q0e
  | 6 => q3C
  | 5 => q3B
  | _ => q2K


def q3A : Nat → Nat → Option (Nat × Nat)
  | 6 => q5W 1 3 1 6 1 1 q3z
  | _ => fun _ => none


def q3u : Forest := ⟨111,6,fun j => q3E[j]?.getD (0,0),q3w,q3v,q3D,q3A⟩


set_option maxHeartbeats 0 in
theorem q4U : q54 q3u (q1o q5B) = true := by
  simp only [q54,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,q7m (d:=0) ?_⟩,q7m (d:=0) ?_⟩
  all_goals simp only [q5R]
  all_goals repeat' apply And.intro
  all_goals decide +kernel


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8n : q1j q3u 6 0 1=true := by decide +kernel


theorem q0p : q1j q3u 6 0 1=true := q8n


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8m : q1j q3u 5 0 1=true := by decide +kernel


theorem q0o : q1j q3u 5 0 1=true := q8m


theorem q9V : q1G q3u 6 := by
  intro k hk
  interval_cases k
  · exact (rfl : q1j q3u 0 0 0 = true)
  · exact (rfl : q1j q3u 1 0 0 = true)
  · exact (rfl : q1j q3u 2 0 0 = true)
  · exact (rfl : q1j q3u 3 0 0 = true)
  · exact (rfl : q1j q3u 4 0 0 = true)
  · exact q0o
  · exact q0p


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q5Y : Lower true (vars 111) (graphGoal 111) 7 := q7r (hints:=16785665) (by decide +kernel) (q59 (g:=q3u) (i:=0) rfl rfl (q15 q5B qaq) q4U q9V (by decide +kernel))


def q5q := q2S q5B 7 [(111,[]),(123,[101,66,16]),(187,[117,80,66,96,16]),(190,[114,83,48,33,97,64]),(215,[115,83,67]),(222,[101,117,50,33,16,64]),(238,[83,114,99,33,16,64]),(243,[82,98,115,66,16]),(311,[131,115,99,67,82,16]),(318,[128,112,96,49,64]),(343,[131,115,83,67,98]),(349,[128,80,117,32,16,98,65,48]),(365,[129,113,82,65,48]),(378,[129,33,97,81,16,114,49,64]),(437,[134,81,114,50,65]),(455,[83,133,115,67,32,96]),(476,[82,50,133,98,49,32,113,64]),(485,[80,81,129,114,50,65,96]),(490,[81,33,80,128,97,114,49,64]),(497,[98,99,81,131,114,65]),(504,[49,50,83,48,130,113,64])]


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qag : q09 true q5q := q2U (m:=111) qaq q5Y (by decide +kernel)


def q3R (i : Nat) : Nat := 0x163441bf


def q3X : q0e := (1,0,3,0,0,0,0,q3R)


def q3T (i : Nat) : Nat := 0x42f9f28c08140000000020f801630c00d0


def q3Q (i : Nat) : Nat := 0x420a3fa41fd10


def q3W : q0e := (2,1,3,0,0,3,0,q3Q)


def q3S (i : Nat) : Nat := 0x18000


def q3P (i : Nat) : Nat := 0xb7d8d20


def q3V : q0e := (1,2,3,0,0,0,0,q3P)


def q3Z : Array (q01 × q01) := #[(0xfffffffffffffffffffffffffffffffff55417,0xfffffffffffffffffffffffffffffffff46453),(0x0,0x0),(0xfffffffffffffffffffffffffffffffffc60f7,0x44076),(0xfffffffffffffffffffffffffffffffff0bbcb,0xfffffffffffffffffffffffffffffffff03a89),(0xf8724,0xb8124),(0x21bb8,0x1ba0),(0x0,0x0),(0xbec28,0xba408),(0x0,0x0)]


def q3O : List q03 := [(160,0,29,0,4),(24,0,165,0,4),(132,0,57,0,4),(33,0,156,0,4),(17,0,172,0,4),(12,0,177,0,4)]


def q3N : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116],[48,82],[48,82,112,66],[64,114,50,48,80],[64,114,83],[80,50,116],[80,50,66,32,114],[112,66,48,82],[112,66]]


def q3Y : Nat → q0e
  | 7 => q3X
  | 6 => q3W
  | 5 => q3V
  | _ => q2K


def q3U : Nat → Nat → Option (Nat × Nat)
  | 7 => q5W 9 13 2 9 1 4 q3T
  | 6 => q5W 1 3 1 9 1 4 q3S
  | _ => fun _ => none


def q3M : Forest := ⟨189,7,fun j => q3Z[j]?.getD (0,0),q3O,q3N,q3Y,q3U⟩


set_option maxHeartbeats 0 in
theorem q4W : q54 q3M (q1o q5q) = true := by
  simp only [q54,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,q7m (d:=1) ?_⟩,q7m (d:=2) ?_⟩
  all_goals simp only [q5R]
  all_goals repeat' apply And.intro
  all_goals decide +kernel


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8r : q1j q3M 7 0 1=true := by decide +kernel


theorem q0t : q1j q3M 7 0 1=true := q8r


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8q : q1j q3M 6 0 2=true := by decide +kernel


theorem q0s : q1j q3M 6 0 2=true := q8q


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8p : q1j q3M 5 0 1=true := by decide +kernel


theorem q0r : q1j q3M 5 0 1=true := q8p


theorem q9X : q1G q3M 7 := by
  intro k hk
  interval_cases k
  · exact (rfl : q1j q3M 0 0 0 = true)
  · exact (rfl : q1j q3M 1 0 0 = true)
  · exact (rfl : q1j q3M 2 0 0 = true)
  · exact (rfl : q1j q3M 3 0 0 = true)
  · exact (rfl : q1j q3M 4 0 0 = true)
  · exact q0r
  · exact q0s
  · exact q0t


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q61 : Lower true (vars 189) (graphGoal 189) 8 := q7r (hints:=536879876) (by decide +kernel) (q59 (g:=q3M) (i:=0) rfl rfl (q15 q5q qag) q4W q9X (by decide +kernel))


def q5t := q2S q5q 8 [(189,[]),(303,[135,50,65]),(347,[130,50,98,82,115,33,65]),(486,[115,83,82,130,99,66,16])]


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem valid189 : q09 true q5t := q2U (m:=189) qag q61 (by decide +kernel)


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q5Z : Lower true (vars 127) (graphGoal 127) 9 := q7r (hints:=16785665) (by decide +kernel) (q2r (prior:=q1o q5t) (q15 q5t valid189) (32,0,95,0,8) (by decide +kernel) (by decide +kernel))


def q5r := q2S q5t 9 [(127,[]),(382,[128,100,49,112]),(478,[99,132,84,48,33,112]),(508,[48,84,100,49,129,112])]


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qah : q09 true q5r := q2U (m:=127) valid189 q5Z (by decide +kernel)


def q43 (i : Nat) : Nat := 0x8201ff


def q4d : q0e := (1,0,5,0,0,0,0,q43)


def q48 (i : Nat) : Nat := 0x99090000b500000001a152f05d5c000e4006080015749fa60141c73802b0a68137976081bca199eaaa3d961388c0f3a0002328c00084a05000089c2a


def q47 (i : Nat) : Nat := 0x288616180c48a1166c008c818588a2e004e68c2c214019ce18588b2410102944c300431c508936018138408051218b0c0328614b0a030139610c0803944862a8614888704038c28424018278d600745a25b53e43cce27c5e0bc00ff483fe30ff4c3fd10ff54ffe10ff903fe20ff4c7fc20ff58ffd40


def q4h : q0e := (12,1,5,0,0,10,0,q47)


def q4b (i : Nat) : Nat := 0x140000000000000198cb0000a04e08a520001a51c20000531e80b64388d00078963d80a7524800343b41a670800007a7cc632d75239502d607286400000000060840000002a100028a67e35dbbd50001a6c315cd7a0d113ac27000121800052568158594ec000682af90000f6880000010b6fab800321ac31374a97c0018068243a2b09f06ef8c8000c984c7fad8000732e29d36fd3c9ba4660000003c50a43a2e72f0000037c5c484413000060966343d567081fd24000161fd8fb857db1616c2d70bc0001da504981c000a8cb68709baa54393350153817e93b2ee08a0b35c971e4812648c40cf0c890074a5b901b85c19b060f0f30f9c6d46f822909e468ae58b600010460007b00142a8dc0d2c800031c60005ad28d4a60000000000000046100000000000000005978000750c07fc419a5a33000612dc38451b04000033fe570000002d76000244c429f180a5d34b0ba1360001a731afd48a565b2f860060014b1d8111aaaac600056d800000000026c2da68678cd5b803ae00010d91906c6000000173ec82c4200058c80000000001b509c9847ce37e90001c466a9e954000000c99484d7ca82a800f93447182024f80000c48dc000596030083ad05a1c75006c10817410814060062c35820051841c00801071c96460c20000020c70c01c908b0c0000080000041016


def q46 (j : Nat) : Nat := 0x1f80354899e077b024a9159a24b911ac077e0465c892708574212ef090d670221e053c214e043b8235cc808a67d091c046f022c0a32623f7049522d15433a6477b08ce033e84719314e04222c097484381b79046f2083ea431f521b80ae446e02b90c91ffb0022ff500273ff780227d009160ad1a2b008a388648213e1129ec123701bbc02b6031f108e812788527a1372fef00a370177821af58220f98488d80ed11b79e031029f81224fe00116e08ea457911b013808784866ffa009e7c49103fc0098ee0495c8319f848269f5444bf2292df046e02b7ba00a2fc6c027b211cfe48667a04ad80ec912592247ef00ae68147aaa443fce6009d00860143e0495227c608ef0062ec24c9e99123806bc62448287a25ec8251c78110a11258898fc215345209610e8c3700843000414019102020c60a121c5c5ec5844fc4543ec3542cc25c1bc12409bfebf43e8be1bd8bcf3c73b9bae3a7b9eb9838f383b7d373369b6035934fb46b3ab3432bb24b1b311b072fcaf62edae72dc2ce2bf2b02a2294a8da83a7ca70a66a5ea54a4d24423c233a2aa192102069fa9ed9e61de9d29cd1c09b21aa1a399a99498e18397416815a14f94493712b11e91590f1000f10e88dd8d18ca0c08b70ab8a209508407d87606b86505b85104203883182501880d00042a470a82c2e250b1c428051315c2a4b0980c2c730b01c220f0b9942c37098142e430883428431b894240f098cc2a090881424370b12c240d090ac4e43090cc6e650994426530b0d44651090d4242f0b98c2a490b0242c570b1542c490b02c2408c3891ae246b94ba4107b92b6e24e8849aeb66b881ee82a983aa6486b951ae707b831ae0c6bad364307b893a2047b92324287b8ba6e867bb19ae0e6bb51ee2a7b909ae2c6ba49aed66b9c9ae607b8b1ee088a159ae50e9811ee4ea9821eea8c98c2a60c6b921ae086b8b9ee467bb29ee62e9849ae346b8d9ee647baa9ee0e6b993a4146b8caa64e6ba41eea67b89b2a286b959ae4e7bb216e242b9c86e87ffff7f7efefbfdf6ef6f902308821058d53501314c12044020


def q4g : q0e := (113,2,5,589836,68,12,1057,q46)


def q4a (i : Nat) : Nat := 0x38d5055793c3679268754bc6188000001bef920589c626a6500070140c8d5de5f1d7a21d0344d98ee800183ee488000001119701a189f7ac18d073c41c5a460f2f6dbb0d3e90a06b82f5bcc02928e3aa852e880000109c34616429775d57a00841de8968c753cd4f7779436ba625de899899071c11166c07285d4158b1c40cba3819701ff1ed4e0000001d75e386545f25c03c4e3ccfe7905e2217770000000a100005011f8991186d800000144100008f313025a433c0cd88dae660be94000121c0000002c88000000655b0af52342fd8c3fbe11d039049a5a1e7325180004d4e9a308f4f4000000ef1802b07e014cea170acb800000009b4c4008e61bc79a059a0f70fccb137f85b2554dc0000000f21e93d1260001258003490000000000283ab340000000b1c0000000003185023a5319608aa0001913478000000000000000046621400000000000005b0dc8e000000426e6c726f99d415a6c3045000127023e070c8d80b889403631ef964fdd2196b35879ca860c0656093c9b66e604e1a08c20003c8494d7228964094caf59a8139a149ac000c151050440002c01002420821110471482078810951470800420470000020001001c02830c50400010400800405400402040000c00080070800c100000d0040151000c0040141188000004000


def q45 (i : Nat) : Nat := 0x23042421610002c21610208008384100000005848830400208084004181081508808200a81105842c340108081882c400010401610060400004128800006508824200028421410000c0162410800007085060424a100000220d0042c200002c20410018408210b0d0840000384082c412109080006109020848e84200508408200000000601881c2121000008bf14a22c388670ba10c1480f009fabe87c6f79ecbd479ef09d6ba8736e39c4b7c6ded69a6b48666c998cb0c5febe972ae05b6b3964abc56eaa952aa0536a1940a7c4ee9892aa504969191ca2c44e8890ea083f67d8f89ec3be748e29b83666b8d49a432e628be9782e65b8b095429e5089e9302464588890c20e3e8728d8196318608bc15e248428800f61b83085c0ae148268480860b81081401e02802800df4815ca209fd879c9109fd82dc163df5215c620aff8654931ff38148230fe92054930df7715c5209fd82dd530b7f8558140bf7815c520bbf844c1209ff815c163df771501209ff815c1539fd81dc163fe92048630df920dc530ff210dc5209fd825c640f755154131bf78148131df7815ca10df7815ca40ddf714c163bf7815cd209fd8798a409ff815ca20fd5514c131df97244220bf9809c910dbf74549309ff805c5639fd81dd930ded20dc963cfd764c620df4815ca40bf9808ca10b7f85581319fd82dc530df9205c630ff210481319fd80dc5539fd81dd530bbd849c910bf58158e109ff805c963aff8654940ddf714c963df7715cd209fd80dd9319fd82dc563df551dc131ddd215ce20df7714c120fe92050910df5315ca10df783dc5209fd825c630ded52dc931dbd425d640df610dd9319ff815cd20bf78148163df5515c1319fd82dc540ddf764c1319fd878ca109fd81dcd209fd80dc5639ff815ca40dbd54dc940ff110dc520dbf7458130ded215ca30df5615d210bbf844c110ff081482309fd82dd1109fd82dd540df471dcd20df77144120bbf845cd20dbd425c640bf7814ca10ff3714c120bdf8350910bf78148153df7215d210bf78158131fe52048531bf78154131ded7248640cfd764ca209ff815c963bbf845cd10df583dc520edd6358130df4715cd20df771dcd20ddf714c153ff0714c120fd5314ca109f7815c5209f7815cd209bf845c1539ef825c5639bf845c1639bf845ce10fe120c861097f855da408fd86dd5319bf845cd209bf845c1319f7815ca409f581dc163


def q4f : q0e := (116,3,5,0,0,11,0,q45)


def q49 (i : Nat) : Nat := 0x30450ac641c0062400b2c00a0c8100000001c50000042a883a


def q44 (i : Nat) : Nat := 0xdf2b688de6543ca1408fb4c102b944193f85dd1604c23ef22c16eaa062fe1b7454930cdbc26e2982411f79161e6290336f0838ae69056de5183dc5208fb4c0e2b9a419b784dc5734823ef22c16ea9847de4582dd110


def q4e : q0e := (12,4,5,0,0,6,0,q44)


def q4j : Array (q01 × q01) := #[(0xfffffffffffffffda8e81df4649a4aea03f353,0x1a8209cc44085084a802052),(0xfffffffffffffffe550627bdd1589ea381610f,0xfffffffffffffffe550c023b884896b1415109),(0xb876f0435535c500a8ea8c,0x2872300045166108a00a84),(0x2669d0fd182653b341a80c0,0x2428c0bdd82211a84129140),(0x1554172223bd2f53d4f48e0,0x15416022395ae5314d4aa0),(0x253ba08288d622045549630,0x2509e022805626105509220),(0x0,0x0),(0x38f01c59fba0814d3746c20,0x18701c597ba0892d2056500),(0x0,0x0)]


def q42 : List q03 := [(160,0,31,0,7),(24,0,167,0,7),(2,0,189,0,8),(19,0,172,0,4),(0,16,166,9,6),(4,0,187,0,7),(1,0,190,0,7),(36,128,27,0,4),(136,0,55,0,5),(129,32,30,0,4),(9,16,166,0,4),(20,8,163,0,4),(14,0,177,0,4),(35,0,156,0,4),(56,0,135,0,4),(26,0,165,0,4),(134,0,57,0,4),(162,0,29,0,4),(152,0,39,0,4),(25,0,166,0,4),(168,0,23,0,4)]


def q41 : List (List Nat) := [[],[115,84],[32,67,117],[32,83,116]]


def q4i : Nat → q0e
  | 10 => q4d
  | 9 => q4h
  | 8 => q4g
  | 7 => q4f
  | 6 => q4e
  | _ => q2K


def q4c : Nat → Nat → Option (Nat × Nat)
  | 10 => q5W 16 41 5 10 4 2 q48
  | 9 => q5W 67 277 6 13 7 2 q4b
  | 8 => q5W 100 251 6 13 7 2 q4a
  | 7 => q5W 4 19 2 10 4 2 q49
  | _ => fun _ => none


def q40 : Forest := ⟨191,10,fun j => q4j[j]?.getD (0,0),q42,q41,q4i,q4c⟩


set_option maxHeartbeats 0 in
theorem q4X : q54 q40 (q1o q5r) = true := by
  simp only [q54,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,q7m (d:=3) ?_⟩,q7m (d:=0) ?_⟩
  all_goals simp only [q5R]
  all_goals repeat' apply And.intro
  all_goals decide +kernel


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8s : q1j q40 10 0 1=true := by decide +kernel


theorem q0u : q1j q40 10 0 1=true := q8s


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8D : q1j q40 9 0 12=true := by
  apply q1x (ar:=8) (rows:=0) (d:=2)
  simp only [q1w,q1p,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel


theorem q0y : q1j q40 9 0 12=true := q8D


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8y : q1j q40 8 0 3=true := by decide +kernel


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8A : q1j q40 8 3 36=true := by
  apply q1x (ar:=8) (rows:=0) (d:=3)
  simp only [q1w,q1p,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8B : q1j q40 8 39 31=true := by
  apply q1x (ar:=8) (rows:=0) (d:=3)
  simp only [q1w,q1p,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8C : q1j q40 8 70 36=true := by
  apply q1x (ar:=9) (rows:=0) (d:=3)
  simp only [q1w,q1p,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8z : q1j q40 8 106 7=true := by
  apply q1x (ar:=9) (rows:=0) (d:=1)
  simp only [q1w,q1p,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel


theorem q0x : q1j q40 8 0 113=true := (@q1l q40 8 0 106 7 (@q1l q40 8 0 70 36 (@q1l q40 8 0 39 31 (@q1l q40 8 0 3 36 q8y q8A) q8B) q8C) q8z)


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8u : q1j q40 7 0 13=true := by
  apply q1x (ar:=7) (rows:=0) (d:=2)
  simp only [q1w,q1p,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8v : q1j q40 7 13 36=true := by
  apply q1x (ar:=8) (rows:=0) (d:=3)
  simp only [q1w,q1p,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8w : q1j q40 7 49 36=true := by
  apply q1x (ar:=8) (rows:=0) (d:=3)
  simp only [q1w,q1p,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8x : q1j q40 7 85 31=true := by
  apply q1x (ar:=8) (rows:=0) (d:=3)
  simp only [q1w,q1p,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel


theorem q0w : q1j q40 7 0 116=true := (@q1l q40 7 0 85 31 (@q1l q40 7 0 49 36 (@q1l q40 7 0 13 36 q8u q8v) q8w) q8x)


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8t : q1j q40 6 0 12=true := by
  apply q1x (ar:=7) (rows:=0) (d:=2)
  simp only [q1w,q1p,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel


theorem q0v : q1j q40 6 0 12=true := q8t


theorem q9Y : q1G q40 10 := by
  intro k hk
  interval_cases k
  · exact (rfl : q1j q40 0 0 0 = true)
  · exact (rfl : q1j q40 1 0 0 = true)
  · exact (rfl : q1j q40 2 0 0 = true)
  · exact (rfl : q1j q40 3 0 0 = true)
  · exact (rfl : q1j q40 4 0 0 = true)
  · exact (rfl : q1j q40 5 0 0 = true)
  · exact q0v
  · exact q0w
  · exact q0x
  · exact q0y
  · exact q0u


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q62 : Lower true (vars 191) (graphGoal 191) 11 := q7r (hints:=536879361) (by decide +kernel) (q59 (g:=q40) (i:=0) rfl rfl (q15 q5r qah) q4X q9Y (by decide +kernel))


def q5u := q2S q5r 11 [(191,[]),(319,[135,50,65]),(351,[133,117,101,33,48]),(367,[128,16,64,100,80,113,33,48]),(379,[130,50,81,115,98,65]),(431,[113,129,97,82,32,65,48]),(445,[129,82,97,48]),(487,[115,83,82,130,99,66,16]),(494,[64,132,49,96])]


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qaj : q09 true q5u := q2U (m:=191) qah q62 (by decide +kernel)


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q63 : Lower true (vars 251) (graphGoal 251) 8 := q7r (hints:=1358970881) (by decide +kernel) (q2r (prior:=q1o q5u) (q15 q5u qaj) (128,0,123,0,7) (by decide +kernel) (by decide +kernel))


def q5v := q2S q5u 8 [(251,[])]


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qak : q09 true q5v := q2U (m:=251) qaj q63 (by decide +kernel)


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q64 : Lower true (vars 255) (graphGoal 255) 12 := q7r (hints:=553656577) (by decide +kernel) (q2r (prior:=q1o q5v) (q15 q5v qak) (64,0,191,0,11) (by decide +kernel) (by decide +kernel))


def q5w := q2S q5v 12 [(255,[]),(479,[118,133,33,48]),(503,[115,82,98,131,66,16]),(507,[99,81,115,130,65]),(509,[82,129,48])]


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qal : q09 true q5w := q2U (m:=255) qak q64 (by decide +kernel)


def q4C (i : Nat) : Nat := 0x1840804ff


def q4O : q0e := (1,0,6,0,0,0,0,q4C)


def q4I (i : Nat) : Nat := 0x2e190000e44028954b00129713b90021c5c400a24a286e030000000000d800006790000005048cec0c584c000029410000109


def q4B (i : Nat) : Nat := 0x1c1800c080840a80c160880850c1604287044044070d0e04282102a03050f061043070d0a08508680361365e17803fe087fc30ffa61ff443ff187fe10


def q4N : q0e := (6,1,6,0,0,9,0,q4B)


def q4H (i : Nat) : Nat := 0x605ec8c0000001117d3d8e632bfc434126a560a0c97cd1c2e0006879dce0130002029832241d31f89848e70800000000019dd990a81d83401050198b41ca520a2f40adbada290270002212000f0240555b3c62d0c010b44640b0000000000a02000000274e000193000140ac0e19590854ad62490de02102d21d6156142944000d8a4082dc48550007f7944400014100014220513068000058000991281875380f661504984eda4b2e787cc39625232a002653d245061c2fea2000000680400000024e94b1850b1ad217010100600b00017050301c050070e260404451400410


def q4A (j : Nat) : Nat := 0x2ff45022545810b0ebed2a0a0caa9a4a646170118bba1216fab28127d3e208a4fd3025756808373fd0139d909a4f77fc6205153e0263c3e095f7f520157b044d77c804c7e9c8080acf700959fa41af7f15139e7a243e4b049e3e72549ef82c4149a9b213cd771046be348414dff0820a1d72484df882050f8046fdd00eb5019eb3818801d311052ae460a7bcd01029a02900f738439afc1100200b730408c90182a2e28830c2c20863024850e8b0a261b081c11808f861e128c0d842217820e140a0933257c918e31461a4187eaf6de1ba2708d81a3b2d618bd16c2b1532a053124b45a834f71d2366648b895627049c860f91c23445d09f1081b43084b06209c0e800eb8beb9aeb83eb98e398eb9cf41aeb8df389e982e39ce41af982fc0bf40bf38de98ce98df39cf18dec0beb89e389fc1af98cec1ae40bfb8dbc23cb858c1a8c0d8c188c1d8c0c8c098c3dcb839c0b8c1c9c1a54180c316c156c104c183c23ffffefbeffbeef7bbebf8c2104c1100c010


def q4M : q0e := (47,2,6,524294,51,11,1060,q4A)


def q4G (i : Nat) : Nat := 0x71198115833604b01a0000606e88fc000242d7c1fb0faad280000000907200000000000000000011a60000c095e07a03c80000000207200b0000f0374218000083d74340000000000010fe000191d800038c8000000000050001a19c0000000f0d80002417105f0001002bc08ec1b0001e12c0000000f0e7e92d81a6801000081e2997c07b60460002f86e047b093591c0b42863642440b4814a40900000001016701f80992cbb0308000c10b416439d943b147aae0000000140000000051cc437e4b4604d43368120000516302b9f1000004067d0c8043000061b56b100000c580000000783f104c0003fbb80009070d07382c4f54000000014a410460001715080ea8740833a5880002404721a41d7010e870e0a6000041e7802d68a0000000000000016605c32d9336823a9a000d7e20d86d416e10a400828f5440c813b83e60a220d8fa1581020e4099e8197842301210c9aa808357404e01fd304041e1023c6482e6b2cf063e21e71a6056370a003201825400056b139c293c35f0f8311d9031132ca772115827b06218a0203561cf86910f5a5f4b8b233b382b58ee49dec3300d7802d8c0502fd10109b0c0a907ee0a0fc274022d3a10d5060b108505d001d3c31732301838cca1790204071480aad97c1b8000509cd0a402a9482901e3171c30000064ac78e80004854e040ddec841106f32a0420d715820cb2810092535383b24a5005e83218280109ecf40006a47e0540003c1d6c17800c84f7001b077b0900001c268000e088000143b221e2f0000390d00040c17340800211f04000c3852005c082b04030102880201024c3d0e17000f0511410100573e04001200070500016400040b010407000d00010204010004000a010e07000000003720


def q4F (j : Nat) : Nat := (if j<1 then 0x90c4083f321d6cc55f504646019c44204dfc10cf28937f0432053910ce223b02400980bbc34c65818045e5f095406f016f31822b00f789912c221f5c0114f24249ce0e08c5fc120656c06b2083990d70859f22264171411812e90b633045ad93564ac98ac1927756b1df4473c74045ae40c7bc4213fdaa08c1dec4c97b82425ed04f3d690c2f0864391ec72208d390a7d7c922807c0191010fa1911e02bfb8240e4c43990d011c06bd692267e463b811dee091ec041cc873e3c9046de215e623de216f1097a08640ab2623f9804abea9226f20245bf630932fde02207c2399086b88877f60496e239ac50c021f5491180a7108bc843247a20643ec231f50022efe0c114fda0958225a38918c18c308840c70fd088c0683056b01e8ec1e8cc2c288d0b416286c21c0109148e1a828738784a282029c20384833040b05c2684e0814120e020441e0b05549d41d33d27d1c513d084fe4f74f14e5cdecd84d14ca4c34bccb4cab49f497c8747fc77c70c66c60c57c51442437c2fc26c1ec1440dc02bf9beb3e4bddbd73cc3c23b73b1ba83a139739238c37fb78b73b6635fb58b4ab44338331322317307af72efae7ade2d5ac72bcab6aae2a129328a280a74a6ba5d251a49237a29a1f211a061fb9f29e39dc1cc9be1b89ac1a519918f98618097996c96115894e14513b92b1229191109080fd8f80ef0e18d48c70b88aa8a109788d88187906e06905c05604e04083302901a80c00049718e4c0b36e11290e6d2997424c0b9261cf970e52b97315cb95261d8532e4ab97614cb9ca65cf532e6a997744cc1735c271330008982c5cc02266041130937948c5c8c8266017b0528b970cfc91846550c2628b983612c82e3e58513308c2711a9cabe265d58302aba833c4cc325e51382e23159451dc19c266176322389989d3c83c2e5cc7ce6137946d3c830e65c3372688b976da48ace60cf232a4259095ec14c2662673060a5900054c162a612172f0bd97886cb3afa462c1268bd9189c4b86f5cc2173103d8201fb9848644e7b050369159bc8acde1134322bd78445bc222c61857b271159411bc2251e61f1f2d03d829e140aac6188772e19f924dcc19226608830280998704cb8c2e6194b213c5837e0c0bc2e5c62f2853784553c8182661d7306eb784512c83aca4477f2460998808ca9a4654e3f24c3a970dec13d8cc513f24f0b9815f4bc574c555b0f009973ddc194de1106b22b0998943c9180e51b07291ff6febfbff77deefdbff7f6fddf7bdf77ebfcff7feff5fdbf77def7ddfb7f3fe7dcefdc6309c6308c63061e3060e3060a30606305c6305c2304c630cc6109ce1060e10606105ce104c6101ce10e1130e0530a0530605305c5305c13020530e0d10cc110a0d1060d105cd104c11020d109c43061830604305c4301c43060c10608105cc101cc10 else 0x23fc480cb7845bfa208a1e04c73d81137085d8158ef1090e22602dc5c887112c08e223888e2258134029f023bd8325d2859f446065d28576447019d81200235c08603afc001907c8877046f6022e212f4)


def q4R : q0e := (136,3,6,1638440,86,12,1083,q4F)


def q4K (i : Nat) : Nat := 0xa16f054972c28000915083d009e0b000184b4aa00070df9a0000000103800000000040895c7d1f430452c83b41000000066c401a931403589000181590e60c4006e970739878c268f4319a8a1e8a227410f80515a000677800202f029915b907440e6c7f8b08b068a9c416408c84be1fb32f040001432000000000000000000001daa0990d58b4800e1d917e01640581811720991cb65f653999ed0240cf0c80400004d08a6610820084081054000400010000a42100804


def q4E (i : Nat) : Nat := 0xa10200000e0858408185082e10440a10000c840000161001e1030a10000000000504000000000141001e10108102819120810282002820c8400001e10283e0edf5ba3ccdeebb539ac5dcadb68acd529f4a9dcda4f2289c3a13047fbe9eaf070b71aed266b2186be57aa93696439b8be50258f05a28118781e00dafe5b845c530cefe1f944c110aef69c91e1130afb68f7360810cefe119720530cef5c79460e30cfb61f924c610adfe9587e0d10cef5c79460e10cdb655821cc10f745c5315c1308fdea581205308efe91985c1308fb689981cc10caf619941c4308fbe89985cd108bf69a985c530afa6829760a30cafe5b845c530ccfe119520530cdb655829c630cfa609901cc10cebe539260d10aebe8991e1130af66809760c10cbbe59825c6308fb68b9161e308efe91989ce108bfe999760430af36889760c10ceb651828c6308efe91985ce108fb6a582dc6308bfe9b985c4308bfe99985c630c9f655869c430cebe139260530ad76949760c108bf6a3965c430acf69491e11308f7ea58320d10cfa609908c630af9a869760a30add6967160430aeb6929760a30af96869760a308ef6a784a0530ceb651821cc108dfe9597e0530aebe919360a30ccfe57845c130cee611901cc108fb6a3924c630


def q4Q : q0e := (53,4,6,0,0,9,0,q4E)


def q4J (i : Nat) : Nat := 0x834601a000


def q4D (i : Nat) : Nat := 0xa295fdb2e3ca3070852bfb65c79460e30


def q4P : q0e := (2,5,6,0,0,3,0,q4D)


def q4T : Array (q01 × q01) := #[(0xffffffffffffffd8fd630dda8e8aa61c90014d,0xffffffffffffffd8d42304082801a102900145),(0x2762dfc636db2d3474067090,0x2120d82a34960818c4045090),(0x3ec100918c681557416c0816,0x1ec100818829154701680800),(0x19cee55353e34c9ba0a86e6,0xeea5424062a80ba0284c6),(0x3721940b48c0c06e80091ef8,0x2721140b40c0c04e00091a38),(0x30e98f28487160298718700,0x30a98f08487160298418600),(0xffffffffffffffcace0a51892172a62383f801,0xace02d1892132a62281a800),(0x0,0x0),(0xfffffffffffffffc3135226350618b47fd9801,0xfffffffffffffff43105024250c159053c1001)]


def q4z : List q03 := [(32,0,351,0,11),(64,0,319,0,11),(4,0,379,0,11),(16,0,367,0,11),(49,0,334,0,7),(70,0,313,0,7),(256,0,127,0,9),(24,0,359,0,8),(28,0,355,0,7),(83,0,300,0,4),(276,8,99,0,4),(69,2,312,0,4),(260,0,123,0,7),(2,1,332,48,6),(57,0,326,0,4),(50,1,332,0,4),(65,0,318,0,7),(104,256,23,0,4),(39,0,344,0,4),(300,0,83,0,4),(29,0,354,0,4),(5,0,378,0,7),(321,32,30,0,4),(262,64,57,0,4),(352,0,31,0,7),(74,4,305,0,4),(305,0,78,0,4),(80,0,303,0,8),(290,64,29,0,4),(72,0,311,0,7),(328,0,55,0,5),(18,0,365,0,7),(273,32,78,0,4),(41,16,326,0,4),(26,4,353,0,4),(51,0,332,0,4),(36,0,347,0,8),(344,0,39,0,4)]


def q4y : List (List Nat) := [[],[98,131,84],[16,66,101],[16,82,131,100],[48,129,82],[48,129,98,16,66,84],[128,49,100],[128,49,66,16,82,98]]


def q4S : Nat → q0e
  | 12 => q4O
  | 11 => q4N
  | 10 => q4M
  | 9 => q4R
  | 8 => q4Q
  | 7 => q4P
  | _ => q2K


def q4L : Nat → Nat → Option (Nat × Nat)
  | 12 => q5W 8 37 4 10 3 3 q4I
  | 11 => q5W 48 123 4 13 6 3 q4H
  | 10 => q5W 79 299 8 15 8 3 q4G
  | 9 => q5W 39 99 5 13 6 3 q4K
  | 8 => q5W 1 5 1 8 1 3 q4J
  | _ => fun _ => none


def q4x : Forest := ⟨383,12,fun j => q4T[j]?.getD (0,0),q4z,q4y,q4S,q4L⟩


set_option maxHeartbeats 0 in
theorem q4Z : q54 q4x (q1o q5w) = true := by
  simp only [q54,Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,q7m (d:=3) ?_⟩,q7m (d:=1) ?_⟩
  all_goals simp only [q5R]
  all_goals repeat' apply And.intro
  all_goals decide +kernel


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8L : q1j q4x 12 0 1=true := by decide +kernel


theorem q0E : q1j q4x 12 0 1=true := q8L


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8K : q1j q4x 11 0 6=true := by
  apply q1x (ar:=9) (rows:=0) (d:=1)
  simp only [q1w,q1p,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel


theorem q0D : q1j q4x 11 0 6=true := q8K


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8H : q1j q4x 10 0 6=true := by
  apply q1x (ar:=8) (rows:=0) (d:=1)
  simp only [q1w,q1p,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8J : q1j q4x 10 6 13=true := by
  apply q1x (ar:=9) (rows:=0) (d:=2)
  simp only [q1w,q1p,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8I : q1j q4x 10 19 28=true := by
  apply q1x (ar:=10) (rows:=0) (d:=3)
  simp only [q1w,q1p,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel


theorem q0C : q1j q4x 10 0 47=true := (@q1l q4x 10 0 19 28 (@q1l q4x 10 0 6 13 q8H q8J) q8I)


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8Q : q1j q4x 9 0 3=true := by decide +kernel


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8T : q1j q4x 9 3 36=true := by
  apply q1x (ar:=9) (rows:=0) (d:=3)
  simp only [q1w,q1p,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8U : q1j q4x 9 39 36=true := by
  apply q1x (ar:=9) (rows:=0) (d:=3)
  simp only [q1w,q1p,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8V : q1j q4x 9 75 36=true := by
  apply q1x (ar:=9) (rows:=0) (d:=3)
  simp only [q1w,q1p,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8R : q1j q4x 9 111 8=true := by
  apply q1x (ar:=9) (rows:=0) (d:=1)
  simp only [q1w,q1p,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8S : q1j q4x 9 119 17=true := by
  apply q1x (ar:=10) (rows:=0) (d:=2)
  simp only [q1w,q1p,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel


theorem q0H : q1j q4x 9 0 136=true := (@q1l q4x 9 0 119 17 (@q1l q4x 9 0 111 8 (@q1l q4x 9 0 75 36 (@q1l q4x 9 0 39 36 (@q1l q4x 9 0 3 36 q8Q q8T) q8U) q8V) q8R) q8S)


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8N : q1j q4x 8 0 36=true := by
  apply q1x (ar:=8) (rows:=0) (d:=3)
  simp only [q1w,q1p,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8O : q1j q4x 8 36 8=true := by
  apply q1x (ar:=8) (rows:=0) (d:=1)
  simp only [q1w,q1p,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8P : q1j q4x 8 44 9=true := by
  apply q1x (ar:=9) (rows:=0) (d:=1)
  simp only [q1w,q1p,Nat.reduceDiv,Nat.reduceSub,Nat.reduceAdd]
  repeat' apply And.intro
  all_goals decide +kernel


theorem q0G : q1j q4x 8 0 53=true := (@q1l q4x 8 0 44 9 (@q1l q4x 8 0 36 8 q8N q8O) q8P)


set_option maxHeartbeats 0 in
set_option maxRecDepth 16384 in
theorem q8M : q1j q4x 7 0 2=true := by decide +kernel


theorem q0F : q1j q4x 7 0 2=true := q8M


theorem qa0 : q1G q4x 12 := by
  intro k hk
  interval_cases k
  · exact (rfl : q1j q4x 0 0 0 = true)
  · exact (rfl : q1j q4x 1 0 0 = true)
  · exact (rfl : q1j q4x 2 0 0 = true)
  · exact (rfl : q1j q4x 3 0 0 = true)
  · exact (rfl : q1j q4x 4 0 0 = true)
  · exact (rfl : q1j q4x 5 0 0 = true)
  · exact (rfl : q1j q4x 6 0 0 = true)
  · exact q0F
  · exact q0G
  · exact q0H
  · exact q0C
  · exact q0D
  · exact q0E


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem q66 : Lower true (vars 383) (graphGoal 383) 13 := q7r (hints:=12901687553) (by decide +kernel) (q59 (g:=q4x) (i:=0) rfl rfl (q15 q5w qal) q4Z qa0 (by decide +kernel))


def q5y := q2S q5w 13 [(383,[]),(447,[98,118,81,130,50,65]),(495,[116,83,32])]


set_option maxRecDepth 16384 in
set_option maxHeartbeats 0 in
theorem qan : q09 true q5y := q2U (m:=383) qal q66 (by decide +kernel)


def qaC : List (List Nat) := [[],[81,130,118],[16,82,131,100],[16,32,48,128,100,80,116],[32,83,116],[32,49,128,81,116,100],[48,33,133,118],[48,129,82],[80,16,33,50,116,131,100],[80,129,50,116],[128,49,100],[128,81,32,49,100,116]]


def q6N (i : Fin 9) : Nat := [4,2,1,2,3,0,1,2,3].getD i.val 0


def q0k (i : Fin 9) : Row := Fin.ofNat 512 (1 <<< q6N i)


def q7y (i : Fin 9) : Row := Fin.ofNat 512 ((1 <<< i.val) ||| (1 <<< q6N i))


set_option maxHeartbeats 1000000 in
theorem q7X :
    (∀ i : Fin 9, bit (q0k i) graph ≠ bit (q7y i) graph) ∧
    (∀ i j : Fin 9, i ≠ j →
      bit (q0k i) (inputs.getD j.val zero) =
      bit (q7y i) (inputs.getD j.val zero)) := by decide +kernel


abbrev q0i := Nat × Nat × Nat × List Nat


def q6B (rows : List q0i) (base : List (Nat × Nat)) :=
  rows.map (fun e => (e.1,e.2.1)) ++ base


def qaa (base : List (Nat × Nat)) (e : q0i) :=
  (q1o base e.2.2.1 == e.2.1) && q1u e.1 e.2.2.1 e.2.2.2


theorem q6E {u base rows} (h : q09 u base)
    (cert : rows.all (qaa base) = true) : q09 u (q6B rows base) := by
  intro e he
  rcases List.mem_append.mp he with hm | hb
  · obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hm
    have hh := List.all_eq_true.mp cert r hr
    simp only [qaa,Bool.and_eq_true,beq_iff_eq] at hh
    exact q1v hh.2 (hh.1 ▸ q15 base h r.2.2.1)
  · exact h e hb


def q9D : List q0i := [(151,5,94,[48,33,133,118]),(173,5,61,[32,83,116]),(185,5,91,[81,130,118]),(188,5,91,[32,49,128,81,116,100]),(247,9,478,[48,33,133,118]),(339,5,91,[16,82,131,100]),(346,5,91,[128,49,100]),(369,5,94,[16,82,131,100]),(422,5,61,[32,49,128,81,116,100]),(440,5,94,[81,130,118]),(454,5,91,[16,32,48,128,100,80,116]),(460,5,94,[16,32,48,128,100,80,116]),(482,5,91,[128,81,32,49,100,116]),(484,5,91,[80,129,50,116])]


def q9H := q6B q9D q5y


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem qau : q09 true q9H := by
  apply q6E qan
  apply q7m (d:=6)
  simp only [q5R]
  repeat' apply And.intro
  all_goals decide +kernel


def moA : List (List Nat) := qaC


def sgY : Array (q01 × q01) := #[(0xf4e2669a6837f027081c0f22055df808222736,0x40209409843f007000c0720001df800000733),(0x601c324b069010597803f9010a2609fbe0181f,0x2080a02e269000187801f800000000fbe0180c),(0x250f0dd0188027ef8024025e13c1fd105e4930,0x22808d1092003e78000000e03c1fd001e4031),(0xc9c0d906874040901240ffc4fc1e1027e41fc0,0xc0c0010ec000000000007fc0fc1e0003e01fc0),(0x1028d4b1279c83fa01f1902f20e021fc806260,0x1028d4b1279c03f801f1800f00e001fc006000),(0x86910025492109002481248fff0841ffff8000,0x9100a343a000000000000fff0001ffff8000),(0x81412a020041fe000ffffffe01001009,0x814120000001fe000ffffffe00000001),(0x28004905ffc0481fffff04000804208c000,0x28004905ffc0001fffff000000000000000),(0x3a518020b05fffffff08400880910680110480,0x20aa0103c5ffffffe00000000000000000000)]


def sgC : List q03 := [(64,0,447,0,13),(128,0,383,0,13),(256,0,255,0,12),(32,0,479,0,12),(4,0,507,0,12),(8,0,503,0,12),(2,0,509,0,12),(17,0,494,0,11),(7,0,504,0,7),(16,0,495,0,13),(3,0,508,0,9),(32,1,460,18,7),(16,2,424,69,7),(9,16,486,0,8),(0,32,94,385,8),(16,4,353,138,7),(4,8,227,272,7),(0,8,227,276,8),(2,1,460,48,7),(256,8,227,20,7),(14,0,497,0,7),(8,4,369,130,7),(5,2,440,64,6),(16,256,135,104,7),(10,4,369,128,6),(258,64,189,0,8),(34,1,460,16,6),(28,0,483,0,8),(0,16,486,9,10),(260,8,227,16,6),(0,64,189,258,10),(9,0,486,0,8),(36,128,347,0,8),(260,0,251,0,8),(35,0,476,0,7),(256,32,94,129,7),(4,2,440,65,7),(0,128,347,36,10),(56,0,455,0,7),(32,256,151,72,7),(1,32,94,384,7),(40,256,151,64,6),(11,16,484,0,5),(15,16,480,0,4),(36,0,347,0,8),(2,4,369,136,7),(258,0,189,0,8),(64,1,396,50,7),(268,0,243,0,7),(8,256,151,96,7),(13,16,482,0,5),(33,0,478,0,9),(11,0,484,0,5),(134,0,377,0,8),(13,0,482,0,5),(8,16,486,1,9),(273,0,238,0,7),(264,0,247,0,9),(44,128,339,0,5),(1,16,486,8,9),(352,0,159,0,8),(289,0,222,0,7),(2,16,484,9,7),(39,128,344,0,4),(256,64,189,2,9),(128,32,94,257,7),(3,128,344,36,6),(20,8,227,256,6),(48,1,460,2,6),(32,128,347,4,9),(37,128,346,0,5),(259,64,188,0,5),(265,16,230,0,5),(2,64,189,256,9),(4,128,347,32,9),(16,8,227,260,7),(296,0,215,0,7),(64,2,440,5,7),(64,256,151,40,7),(72,256,151,32,6),(96,256,151,8,6),(257,32,94,128,6),(41,16,454,0,5),(44,0,339,0,5),(69,2,440,0,5),(266,64,181,0,5),(19,0,492,0,8),(49,0,462,0,8),(152,0,359,0,8),(128,1,332,50,7),(256,16,230,9,7),(4,16,482,9,7),(8,128,339,36,7),(16,64,173,258,7),(6,16,480,9,6),(136,4,369,2,6),(272,8,227,4,6),(384,32,94,1,6),(73,0,422,0,5),(262,64,185,0,5),(265,0,230,0,5),(274,0,173,0,5),(274,64,173,0,5),(276,8,227,0,5),(292,128,91,0,5),(39,0,344,0,4)]


def sgA := moA


def q98 (j : Nat) : Nat := 0x1000090fd30b281002edebeda1759cedd17588f587f42ef25c4befc9513fe9b94549814c153549814c120f055354930483a454d524c120325535493048198edda54c910


def q99 (j : Nat) : Nat := 0xd41b34204741039105268403991050687dc08000035a0a59104010c882ef4310000067a320057a1640060818013810000ee00cc600000e06504339883a8461d12300009020000d6071810004e6200037d944cd86b6100008d840000000001b6100007a21b040cbc70497c248c00000000022c200001d6090174194188a0ae1220a46f606496407a0b20804d9158ddc05c25881835e27c1360287f60f012425a06a0fa0547940142720dc000300bc023e00267e0487c048166021c94099e01470075e040680a3a00058063b2e8f8dddf68d834bcf32dc971dc22f3baed6b06b9a667a9ca619664a90a3a87e1783e007d1e072db66b9a5669926297c5b9665494a4b9204490a408f43b0e4370d4330be2d89d2307317054130440f03409c1f05c0089cbc22727089a9c0af06e8ba6b91e9ac6f94ae2e9aa8ba6a4771681fc89d1e9a42bc4899e9a22bc4848f2205ba67d16a5e45a9744f2dc10cb6d8e61a77b665eed987fb65e854d72dc658b71959bb7524e61431c64e8f052a0c949c2e5183b542a54903db8214ea0787a71d7e9c757a71daed063fb814f6e4427c40cf6602a18306960c009cbc46f1af0bcbb46f1ad19c6a05f1e705cb981f2e50dcb8cdf0529fa44a366101bc63c6f18e4ba5353e94c43b62c072ca03cb24ee9c797c703ff0ff63fd2ff0bf6afd63deaf3d39afe5bf7f4deeb7b6debb5fcd7b75ebd6f757ed5bf3afcdbf1efc77b1ddc6ff1afc5ff16fbf4afbabedadedb7aecfda7be9afa5be1ff87f61ef86fe17fea79460530e9b94605306eb94605306cb94605306a794605306d79260530ec59260530e519260530e515260530e63a464d20657a464d20aa7a6605206a7a6605206d79360520ea791605206cf916052064f916052054f9160520ed193605206dba154d206d8a954d206a4a954d20661a54c520edd954c120e91814c12054d814c120549814c120ec5534c1202e5534c120e91524c120e61524c12054d524c120605514c120605314c1206a3a464d10663a464d10ec5a564d10ec1a564d10ed1a960d10aa7a7549106a7a754910e9f9354910ed19354910ec99354910e9d9354910e9d835491064d8254910edda54c91054d52481105495148110


def q9f (j : Nat) : Nat := 0xbb000000000000000000000000800000000000c300000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001000000000000000000000000c500000000000044020000000000000000000000000000000000000000


def q93 (j : Nat) : Nat := (if j<2 then (if j<1 then 0x9c72fd9472fd9462fd9454fd24567d9c42dd9c42fd94459cc4421dbc32dd9c325db4258cc422dd8c183d24185d24069cc4089c9c01bdcbf1a5cbf2ddabe83d23e2cdabe8ac0be01dabd01d93d3fdb3c01dabc01d9bc01dc3b01dabb00dd3a00dab900d93900dc3800d93841d43741d2b740d43740d2b740cc3741d23600dc3600dab663d2354fd23511db3419d8b41bd83419d8b31bd83319d8b241d23215d9b100d9b000dc2f00daaf06daae42d42e42cc2e11db2d19d8ad13da2c19d8ac11db2b17d92b13da2a17d92a00dd2914d9a941da2815d9a801d92845d82800daa706d8a708d82700dca600dca500dd2400dd2300dd220cdc2216d9223fdb2101d9a117d92143d8a107d8a145d82109d82101dd1e13da1e08d81c3b5c9b3b549b3adc9b3ad49b00dc9a3bd39900dd1916d91803db9709d81701dd1513da1517d9153bd39500dc9200dd1100dd1014d99016d91001da8f41da0f17d90f43d88f01dc8e03db8e00dd0d32da8b8ea90b2fd90933d88921db8833d88829da0733d88725db062fd90633d88663da0529da0569d9052fd90571db8169c98168c9817ca9818ed9003dd37778a9c07aa900ffe7febff1ff6ffa7fcbfddfeaff37f7bfb7fdafec7f4bf7dfaffbdfdebbfddfdefdf7ebbeddefef776ffb7ddbdebff3fb9fbbfddfdefeb7ddbbfdd7edff3ff9fecfee7bf37f9afcbfe3feffd7fdbfe5feeff57f6bf7dfbaf7f7bebbfddfadfd5ffaff57f6bf75f7af7d6feaff4ff9ffcffa7fb3bf9bfc7fda1e51306a3914c1a5e453068b914c3a264530e81914c39464530e51814c39260530aa5814c1a960530649814c1526053068f98481a8e4d206979348198e4d206a391481a3e452064f9148153e4520e8598483a06612068598483a864d20e91934839864d20661934819564d2064d91483a960520e9981483a360520e4d814839160520aa581481a96052066181481936052054d81483a154d20aa553481a954d2068553480a954d20e9531483954c520aa531481a94c52069531480a94c520e9130483a14c120e6130483934c1206a130481a54c12068530481984c12065530481814c12054d30481524c12054530481314c1206a393441a8e491068f9244183e4910ea193443a564d10e9193443a264d10e8193441a864d1069593441a264d1066193443a864910e8d92443a1649106a192441a364910661924419364910aa583441a960d10ea582443a560910e8d824439560910e4d82442a9609106a582441a56091065582441936091054d82443a954910e9d52443a354910e4d52442a9549106a552441a35491064d52441835491060952443a54c910e5532442a94c9106a532441a54c91065532441854c910e852044393481106a120441a54811068d20441984811064d20441854811060d204415348110549204415148110 else 0x732dcb87285c74710dc116f71bb66df5b536ca1b036b45ab66a01a5968f5a0d67ed9df66e99a3661595664798f4633d8ae6209858608d8025f457a65e217765d657325c316f65b0969a599962a58355f057415ae562156b553151d53f54e152f94a751d945250713f74f713bf4e613744d493294bf52e54b212ad4a3125648b51fe47251a045e914744610e242e5083417104740c8fff3f08f8a3db4f3f3c20ef03b40eaa3a44e753974e423880deb3740da73604d4e34b0d0d33bccdc3338cbb32b0c993200c6d3178c1e2ff4bd12eb8b7f2da4b342c30ae42ab0a7d2940a2a27c89d526e0993259894024948f423748b4223885e20d48061f547be1e307621c906f11b406af1a1065118645ea16a457d152051113dc4de12e848d11ac44e109c3ef0ee439d0df835c0cf03170b7c2ba0a50275096422d07ec1d706d41990584142046c0fb033c08c011c00075d37764dd7764d97764d4f761d37647d2f61cdaf635d8f34dd37365ca7365ca720bdaf01ddaee1ddc6a0adae61cdae447d4620adade47d2dd1cdadd6cd9dc34d9dc6cc9dc6ca9dc2bda584dd3584dd3571d5cd61cdcd60adc5626db5646d4d647d4d51cd8d51dd8d41ddcd31c5cd326db5246d4d20adc511cdc500bdc4d46cc4d36dac937dc436fcc4377db4237dac287d24293c8c28ca9c290a9428dd8c18c5cc191cc406fcc3f92c0bf1ddaba46d2ba0adab954c1ae1dd9ab2ada270ad9a734d8a70ad9a647caa50adaa546caa51cdaa30bd9a135d8a123dba06fd81f37d81f1dda9e2bda1e0b5d1d0a5d1d0ad99c48d99b0adc1a1cdc1931d91649d3961ddc1565da152bda156bd91531d91547d4155bd39549d39549d3941cdc947fda9373d39353d1936bc9936ac9937ea9930adc121cdc111cda900bdc0e49db8e23db8e53d90e31d90e47cc0e46cc0e1ddc0d6fd80d37d80d47d40d46d40d46d48c92c28b92c18b92a98b6ec28a37d9866ec28537d98437da8337dc0236dc0280c2828cc18290c18192c18013dc7e13dafe13d97e40d47e40d17e01dafd01d97d01dc7c01d97c01dc7b01dafb41ca7a63ca7908dc7941d47841d2f841d4f74bd377415d7740dd7740d4f73fd37600dd7618d8f513da7419d8f401daf101d8f13ed37101daf001d8f001dc6f3bdbef0fdbef01d8ef01d9ed01dc6c01daec41da6c13da6c13da6b00dd6a00d9e951d16859cc6808d8e811db6741cc6541cae540cc6540cae510db6439d46313da6108d8603f5cdf3f54df3edcdf3ed4df00dcde3fd35d00dd5d0cdc5d43d4dc5dd35c56dc5c18d9dc56cc5c0cdc5b00d9db18d8db05db5a19d8da09d85a1fd85900dcd604db5600dc5514d9d515d9d400dcd108d85100dd5014d9d000dc4f00dacf14d9cf18d8cf19d8ce01dccd00dacc63cc4b62cc4b50a94a5edb4924db4983d2482cdac866cc482dd) else (if j<3 then 0xe4f6b20c7814441e1d451138b15a449c588f812716293ca51271623e05bff5e71e80004a953c8a9a459fe26100b479e6c1468ddfe98200ad9b491435fc749640392497af884632975f8851b2afaf290a0039a51fd71c00842adff313009a3afbd610a12bf3ea1000028954ab2c268c98892a9c0f0851b7fad640688f4f8ea51944788225cff6e4d44ab3473423dfe8544ea32fad612a1519571c001acf5f62000d6605b93ea1350bdc7f08e8ac6680ed451ff856c045b31974f00c6525f0db9a2b510b34dff2e9900732a9f140522a7f109d90bafb884e335ff2e9900232acebae2880030691fea3ac8568fd970d6e7a102216adfa19c03247bffe3b1a012155ffe6d8900252b6bc70151f280b4f7b0644e3f5c110354753c24268c7184688b5dfa10c26dcde451942361eeffc76340242bd9a58445fa11a890defd632456194b267895c699402c5f94242721d9f8398d0833e0f4ca2f61ce66484fa463668a5188b850fff406a0a99b9dd8706123ec50d6484fa463001dd5c92462875fa106881d3cc04d95de4e660f9d02d806a1403c230fe348813b497c71e746e180115a803d3f84143b0039b52ae0b416c330642372809290150513122a37602c251018081260a1089e1382084285c1b0a061841b60087104c0430a60c3018430c178271890642646040760887c15857876a103085f137c0a19a0ac14c964251ca0e483c178550746e42c82b12478800810a72041d03c09747c8fe890a013c5704da07218528aca04c180699c06aa7bc2051141607024831134264c806060a0306d04052a15c230a828109c0f8341a0f94c844086e19c4a0805c0841b01b814470208380584248550d07a09ac001fb0809e06804d02015c2d0a05e0d00e81460e0730302205a0c5c10250500934000ae0b6180d01e030059c060702a08f41b83b0404e04002b0b60c01812d0ba180b80bd05c134201002203fc4f0601003007707f01e07383cd6b329cbe72d9caef29dc9fb258c8a3200c7971ccc6cb19ec5f7157c50f12fc3e70d6c313097c1d7056c0a300fbfd2fe0bf42fbabe12f70bd66f42bc8eef1bb6eeabba6ee7eb9bae52b8eee1bb7eedd8b722da6b626d6bb556d37b466cffb3aacd5b302ca4b246c80b17ac48b0cec1db022becaf1abaaae2eb76ad82b47acdeb27ac22af1ab72aa2aa36a66a946a33a8729f4a75a9aea63296ba53a92aa40a8d5a2f6886a1fa866a17a84ea0ba826a0467fa9f9a7d19ec27979e1e7779d467299c4a7029bca6dd9b066919a2668199ca66a997664c98f662e987e61097e25e097625d096be59095b2542946a4e492a2472910e40b8f563b88e8a3828db63588cae2f28b3629e899e22d87fa1d786ca188852e11c83a20ab81c20338021ff57ee9f867d81f3b7c35ef37b65ea779c5e427859df17721d8b75d5d4a747dce6 else (if j<4 then 0x120c1a341832eea18f40f0481e622cf3147d30b1c7162e5e0c5daa6d462e8c16b960addc822f8b105b2931f31e2d03091f4c2c66f41a20f5cb056ee415cc87088e848e84de83441a3d1822f8b10000d7fe0b4030fae582bb91eba5485f162b2b9a20f6a5d13d539230d2581e050698af46a2cbe065e6c2607cba5919287107cc3265908a71b8211496d9b0356085e1d8c205392c0e83170e00319d4401338329be1106005f16207c904196c45f16202ee9251c8c930a570657040cf9f2d8462055d24a407c904474247434cc828fa616306347f5199850000170201341a9e0fb81f703ee07dc0f2de6170de61000049d5f1a8c58d5cc1909f50742057e27916ca00067ae3483f35e880031a4d7e5a7400002a348f8fda2000c4927fa87b018ca77e4f06c002512b7e751b000234997203419bd3054d87ccc96c38257cc163f340008a17a195aff4882ed00003e078400ff468018cd4fc40240002a1c13f84e5a4415683f924e00485231d0e24518dfa104f0879fc7c4d13c7ff83800001cda4feb2e002a152bf5dd120064377f863800001cda63f947000004234d7fd238000009da6bf82e045b2d76625fff8a9a8010693bfe68a0010892b76f84104d7dbc0b89dbe96a401c6611e990c47a64355fb658009926f9ff61b00842aef9f4d0046cc4fc0c00270a6eed00d841538591a239bfaa01878003a23df9821f88b204a8e3f40e40111d9d3e611a801d0e1d3dc9321b12de90404b67b00d42c317c8d8052180efcd2101c864ffdefc441133adbde1081209ffa4bab00c683fafc208ca33e18a04eb33be4401a123ff2c38919663f0dc499e1fb34a041b3c9d86a41a4b789425dff314003c483580f5e4060e9f2f1044eb7a4139c034833cce3d8106534ff0922420630fbad6b019238cdad08d1a6d68468bbf43320648fbe30a811a3afd6124801cd2adb793a4dbf34500028495d2eb004a8f49c4a931ac065c3e66358fdf0a6127cb780b13dd37444ff08082c270c17c808034845b7c03c02ace14b7eb8a50042d2ce1c6839e52e227759543227b7930c95db3930b2c3750a0e67ac4a2772f5b142166d3a76245d3cdd448cf961ac87ac88d1f90808c450d0d1b12d089fd25511813b40738a28d9503f331d3c6e20fae91206d2039f503424f284428a985de38366eb4305c4a66dd8dc2a78dc41a07e9634c3d17326fe31a8000e69371f10085298f63d64814cebfcea40007349bbc4804294afeb6050137fcba6401cca8fbbc48032950ffd1a8000e69371f10085295ff83500009d256bf5c3a04db0e095f3053dc7fd8402d239f062d190001711afc8c93000150f2e406835fefec00511e7fc50e00041a491d4d123e41341d9fb6c164f3ec1439e096445ec1435c12c891f5813322631e5e80071a27da1225de240214a57f5b02809bfe5d3200e6559f else 0x35dc301da928e045843494f16eb6ec185024fe49088a5271834836ff1a18d5bbe2838d254cc8afa7e714205ee1ae601d2ed91b4e9d275ba9632bc6d10d6a886186c4e59c62a382b6c7d210d508db298808feae8ea0386ef8e342c91a3133e3416a2e172f7304a3ec1072c8427d312ac42d0d73093d3331d32c11b117a0f0400031fe5d4543734c133e58267cb0505e2b99012fa25142286a75208df895ef70614d88a93ca2c66c44401e8c6c7a68a281a0a8fca33668daf580cd1cee0b43ea26c98f0a483b480ca0f51782068d)))


def q9a (j : Nat) : Nat := 0xc00610b72b813515482944203880e207a351422c16800008701a0004eaa05fa2f400a0d0001237c1e000361303240f8000132821414a8a707e017956201f74b02a99f60b903701281ee061047806088800275c000000010617800281ccc88717bb381380b008934101d001005000081def00044000000489c03ba2d4058000151040c198025a80bbd408a4b3060008802a03b04d19900060af06a00cc1b40350218034a1e8e8001889ca0606606e59780a800000083e0002094028024807ec5f04100a8c0605800103100000009828e7428a14542800e000810e6819a12007908005916


def q94 (j : Nat) : Nat := (if j<1 then 0xbe0f07e2408e0381a80a9c2a5fe94ca46e8dba2ba88ca17e8189fa27c09e6a7589cda7169baa6b89a1a65c98e660f97ae5bd960654c949250193424af923646390f24158f8e3b48dd23388c3e2df8ada28889a223388221d4869e17f850211583a20b5822a0358019fd97ea1f7a7d41f287c1dedd7ac5e73791de257805dd576c5d86753dd127359c9f71c1c397011bd86e69b646c79ae06ab1a91699da2b67fd9bf668d980652d90f634d8ab61c185060557ee5e997895d857435c8d6f65b316a159e965358915ed570559555bd542549d5035351492518541a4f4938a4d5532c4bd12bb49a1234481d1d0467115f44c90fa433908140f900b3f60fae3e10f3f3bd4eca3a64e7038b8e0b378cda43594d26337cca03180c262fccbb02db8b2a2bb0aac2a1ca4728149ec26e097b252091c23e08b521e08341ff07cf1e747841cfc70b1b646a019e464418345cb165455914b851513784b51208442101c3d20e743660d083130b982c70a8827d08d4206073018e053c12a042c0e0028c06c00e0000d3533d3253d2a53d2a70d2a6dd326cd2a6cd742bd552bd352bd342bd152bd3065d3524d7523d74a3d7463d3523d34a3d3463d32a3d3263d2a63d3462d3262d3062d34a1d32a1d30a147514474b447454cf41473314732b4732549f29377253755337353373472434727351143511734b1434b17331173510435107347043470733107327072a704746f7742f4742fcf40f7342f4750e474ae9f48e4742e7730e772ae7330e732ae7330d7326d4752c8f4cc4746c7726cc722c7552c7352c4352c7b30c4742b7552b7352b474aa772aa7552a7352a434aacb40acf309cf2a9cf229cb509cb4a9cb429cb309cb2a9cb229cb029caa29730677750647506774a6474a69f4867744647446cf40673506734a67344673306735057346573305732a573265755247352447523474a347463772a377263755237352343523732a37326347522874e2474627726275522735224352273262b3042474a1772a17552173521434a1732a1cb500cb4a0cb460cb300cb2a0cb260cb0a0cb060caa605b43613515134b5134553f4145f2945f293534d2234d2134721343213511134b11343113510134701742f3f40f4f30f2f48e274cc6722c1552c1552b1152b1552a1152a974893f4296f309a72696b309a2a69aaa49a262913508134a81344813507134a71346717506174a65f4862f486174466f4063f406175051746567425374251352417523135231f4e213521bf4206f2606b260aaa40baa20034d20f486fffffeffdffcffbffaff6feffeefbff7feffdffdfedfddefdbfcffbffbfebfdbefbbfb7f9ff9ef9bfe5130e45306453060530e6120e4d20e45206612064d20645206052054d204c5204c120e4d10e491064d106491060d1060910549104c91048110 else (if j<2 then 0x8542afd71e6b0001ba52f32a1711238ebf7ff5900019256fc84a20ef8022451fe210c4033a489fdf9a32a01aa54ff9d546c4023a546f1303b14a434fce22a254693f9219251fbcaa48401349667f570b89f3fe98dc21988015dac77dd6892bf5c0388c3f133a274386132019fe5cc0e147f0fb81c46c3c7ae0468c7d61fab89efc9a20b945f7db09027299ff02a48006894bfea2802c8f3f1be002a8f332078ea32ff5c000511f31a0b1ccefe85a2d7961c802b662e4de5e45900215ab33f9a10046cf3f5cf8161c2400c93b7e7ff8030db40189377fffed4918b201a5317fcd41f4058903e67a02346effdd5880035684d3f9680000a344ebcffc1a9230090027505fe3cdf4015486fe2d5648b317a7c7e7088e67a4e4bc4488f684f0a1f860910bb4d70cb40095997f1baf9001e124b0f3eb22d957d7a4fb3604da00e4a1bff38138f3400992e312f6b400634373e862800568c0fc300699718c9f10a85d5deeeeb0c48001272fbb11e3d8c1a00849c7eff1005ca03a05d3c32ccf9e768b04664ff587950000099a7bba7b4b248f21b23238fe78c0c0200744b1fcf181804008e963f9e303008011d2c03ff113dcd30024b5c7c21267d400396acf8d1467d400396a9848fac4401492e381f10c01e3467fe3c48a0600786a4f3db1cfb1801e1a80bff70c70808185a833c3f1c202021698fcf40c02000536a3f3c00d13affff8a5820029a52f5febf0288010696741a0795af234006349def9a522a0049a61ff5b0e10922aec71c001c669fc002245ef98f9680cc00ced41dff8c0c0601769affd2450c0400826a5e56be300052495cfea000d23bbeb80000550c741a070ed79f8310000093597c32d02012b3cf88830004c923f903a5200784abfa7006451bf1534b4087499fc385c000d095b5fbe3dc202053a5df9f409c004e591fad02c44010cd23bf0a80751ce8340ebcac7cba0151247d99402c8fbf106d20159247ff1fca10401892a7caff00280212547e4fed141d8ae7f43fc6c01c91b1d78104024929b3fb454233f510c01a33cae7f000891df7a0d039fce00289cfe700144ebfea7fef0202002499313ffd00551d7958f1e400634a0fcfe7b0990a05a47dfc294020039a61fce00689df7a0d0387c5d40892a1f8e27406004925cf63660c00324b8ffb4301831671de3fc09801849c2604080631a2204f21b47e02200ae11603224341a6060f8671591c138c0820861304246e198d455064bc0e2891284041452a649e150060104911c46c0e81204844240e12031e183648017096800a0b9214370e9330fc334103b20d03c09020b82f08d0726d800782d0702c6041b8350d0cb05044266103000c020901f2082782805e118603e83280220ac99060290582a069894281007607e14210301502a8604813a11850500dc128260b82a170660c0 else 0x6793eb688648959a83db84618641099a63c740e409a479934f3f3214290c86effccaac81b307b7ad10a01a00b4fa2e200b4216d680b684ce5ebac8ab347f659b6ea4ab9476bced6888f666748473d1c6577aa891a102bc9cbc82839626a2f0aef5902b0fa5903fcca8341971d13a6892886c51cd17aeaa181e5210518597053a3085c82bba533230d968c235503e7852cdde12e1054384cd36f5eb152d5087ad577bd96597053a3080979abed48861dedce22cd713188a3e3bdc0e231cdb982328bd93305e50bffd5a740f240ff5b6202548eed6ff3ec60018698388e3e6cc0174a8bdfe00ea3484bdfe00f242e7f00051187dfe60016476edd4664dfcfa9e00112433962690c854a571ef6d0d675fe78800aa3edfa000b23d7fdb183000027699fce2e13a8dd40871d0b66dffb7e8002c913f9e1c2751a7ffff8deb89168800e69c7ee43840a0a674f18005c900eac208342861fe3c000d51f7ef000354795fae01c46087df3b2574eb8c98cac0186ad82cd9fc363b400013b4b393d9885c2bead62e10f8ad85013bfde0002a8f34efe348b35f7810311c08e9b3a901543f65f0da0488095a64ff23f0c000592b3ffa38440073457cb1ac01d66af973090005ed03ffd2f00016486e9100d0b669f32a37d4001152d3fccc050014686f84bf5c048000d5abbf949be800056699ff97e8802e480f2ccc78c64f8))


def q9b (j : Nat) : Nat := (if j<1 then 0x931828049fe42bc283841e02d972182e205d00b1c0aa0a6ea580092e0644ad55c4d284a03880fc040b33d80010027941c054eef74e2c00016b94095ca329413025e03495f80002ab801520a3400000002022117f049800000001c8a0000006842901a8000160d000001b7817007c6f400001003c03420dd023d028903294fe8079a28da44e527413c0003b160029d8ee000346776bd00e3912003ea0464207ad0400060e5416684f00006894c0f5dcc4233613e02400001b206136c1c182f488ce07302ae84a8449c0e81eab21f70a1e00c406c85a910be431803e824b68c8000096f913938c80cf8213c08c000494341268052054609952d40001b86406c1a0e52540002f4121438564241a148e880911406ce16e001c2214031e01c9d4c224a004a0495e9715160310e5f028881b40a2cc23003785603a0828c42a685a462f003781758258077e0d0c04a80ec000212c403100ce81ad7204892829841aa14ac05f01f1080e067c2c80002b116525c81a0001028211d42b4903204fa0400001dc8d30040ec829b5c90057a0ff415a1c1209de111d2cb821609be13f418d02db210887f081d82de203a16101e98441048813d89ef5c2b2904c7fc9b95c26681370b41c801fd0b780bcc9bb8168000012182ca22a3202000089c2a0110914172402dbd604516008000b831caa3062d0a0a256e76d2d6d000883470ad800000004813064c2869025a27d47ee900c0c20003020c0b2e5eea204000014e01e6911d097cf72ca579504000507700015c654578803000103e407380000100015b3172af9000000027a8e0b48a0600020666b002e2a857cb0c6052d941d370058c039c13a01200869530e0bcbd7776c6100025c03c04104146c1c4a51945ac8c5019704c922c972c81f601e7074800040993d1001fc0f251aa043c779494c5cf1113409a2027c143316d062e8ac0230825e20bae8e00950156034c076ee1004571a0ee8dd2801cf677c68a7e621dc3d779c112021da1ef0b3294280bc820c000085841e3985c441e08d95f5029c01ee00641b9008d270495f02d181830ab0948c2e0043105cf56c01fca0170420124480621e388d416d087e53cf047c0d6805c911840ae4f3e96c82286822130ae662bdb02e806e0156002db9380005176000aa22a139807c988e08b8135822635b962e02401130900028132a04800181b0341038078101800004502617008408a480700004040484c1607191205e731200418002280d404b0409016b9100841608070800008040082a20068497e8d02c84020e0b0dc0208010f4441c0a8186687148001608028a04411148088e3c0500c0a120501474200301c1c1604804642b010193a000180812011500c0e0b148183a0a0001c024604800120e080241c2f00884fa73060a400040f0000000000f80407010100048 else 0x403d05cc06901278235042c000484dc1120146043a0d5414a141a409c08280cd01614b420434a1d02534a4c0e1023f047000040c0c176b1e000d251881cd0313008642381fa836b7b5805942d981bd1410162c1ee221e0ae8138500e82c308de546029383d404e60fa002f83b409980004159853f57faca104fe80c8b0cc10480a7011c23e609b40e4023a09d2057c20c837d061a4fb82ce097502fe128405a2044000002b806b810b03bc0eb01a700c6027c12bee283a9407b457082a081ab44f015e0000325c066801941bd95b3b8892fa6c82002a07741084059a213082a119229b15c4026e52a52bd038c4a38f57828e520e01360ce029782fda7c467c4022a31d28a683900013a05022402ac28494020432114c0d682b80004003404982e345f609a510c00022920c9442800003094d32692c880740ae216b4024258a05f481402c1b36c0a88000c18484c60756081800e8116b11971a5ad6022c0270c6200009a6203c612dc22d31e800064b841b1829207e0000c0e8d2f706ba070ae0500a30aa60750194bd5a0aaa0c100600221091a0a3884f00840a6407b80400c5a40b6945c494805506414f6eac601500004098d83a82d6046403a412000030850000c)


def q95 (j : Nat) : Nat := 0x1fffd8340260acff0e695c049961e62b073fe4c016141fe7000114a5dffad88930b3f9cc984002f0b5f5c41d0287ff9b1146197fcf3084026557f2fd08004a1607ffb22804a15b7b883a0517e79a0c051961fdc2650006565f397220392bbf61c200251597fd3800c50edf80c0eff6c42184bff980a812ec02a04ada80c20de782b849387810f730d4217a60040a67f00a40b4fe2128147eb4e000c520b0ec3464260a09054395c884403f158243e1c0206832990b06214830d81a0a35038350906c32190589c24110a0ac28220f82c1e07012b63b45b865015ebb9d6f2d318c2e255ca292b2243e6708cc1782a44b0870f119c2d04a87309e0b00046468c0d3986726ce458cc31936322c6058a9b131632646488c1918222a444c85ca47918f309e4d3c8a5985a609e4c3c905930b2434801ca5fffff7efbff7bd3048110


def q9c (j : Nat) : Nat := 0x1094021e25e00490cc0ace241c14ea5b890b0ce4298000832c095c012604024e007811fbc0910205b0dd801f0a44000d42547e00014030212032800b034c2060d69b5a0978268000589140600032b100000008b2fab200000d44af1255010873a14ad051c028000026d08c410505f9d0109981104a6820c000503b250000000011fe0bcc294000ed6f05e09290c28180030000322b4242b4a41aa2b0c2ea7d4022f478c4e5a20593801e405309f8093a598e09050c08508880140cf9295bc51242010000306f00020d39f3f5a0920010940d604c428a0699e1e4afdecb10bd28f0bdc27b098d509009404f13fa5010270228017034b02d9ddf0b980f506d5a1002f59430be0003422c1f4000c18a016412b4aec95213a40de0d7c914476ed246bd0001b4ee82a4970a300bb402d77dc325956447b07e14b50c4011743002ce01510d9356c9641b30000275003b59d524c05490b97a20b00000c1d6076c1ba08280060a802d30396b1e0860c2200d989b485810d07942c164b8acb05943010c6c1fea5f9d044770c0804d45f10960001420c82701d0001008c170000aa40908d8fc028000107880fb04800e30d1d09800000030cd824800000030258184000413c00040fdb5fdc93bc8919f64d03057cb84be2bf000208eeb12a58806831e000204641f107429dc019ab2c19d5285bbd4060349029e24d01b106580e97d05e2327701c109d40f0bc719240bf015eb5841c976351230ae11e868503428830003a7581ae789415b479000002c40ec1499af201ca1432490214b50c226728d01c05a000249e00d903102acb6000000a0c08f02ac23c447c2db0b2a1610290124498d847b4f8329073c16263a000104e621b7d6534a0550002bc4107c080000205d493c0001d8848f49da077800c00000000001e0800082b1071c4910228b0c000cd437cddcfd08d000277548e624000030b1c4b4000012eb5501a00000001040c2a42440293000c2840000d4852f0b58000c14a0c3418f0aa804706641ee0af00030a341930c700016b2896a15000000ad82e301bc0aead600cc09c59280000322067c80c000409800659300b7290607aca0a1a0d2a400f96464968033020ac28686035702e02d568382479c15f4d68149990c50104002921771400253a01a1039b3e122e323b18a5010342351a2a03110000063202613702520603112a0e1a181d0665130005003b161e3d02160e02040c03200f01000009006d0c0e08010c0201130201070600011f08024b0509070c1c03010b1c0102002c


def q96 (j : Nat) : Nat := 0xe802012c810082004024341410281a1a16120a0e06001f36804c120443ff


def q9d (j : Nat) : Nat := 0x13ae07e26ca224c0000042410606e07dcc000000001c68540000090200000000c2e001030000000000000000130d6300090c000000000000000000000088c000000083f40000000000127e00caa0700000089a002370009ba000000000000000000000100e08c3c0848f4000000000020800000000000000c19ad500c0b000000000000011480009a00107400000000003448000000000000000185000000000000000000005bc000008348ac2280000084c002050008640b00800125c0061bc05038a780041200205000000c0c000000000000000000000397000d961100c44362122d0052001005


def q97 (j : Nat) : Nat := 0x10090e08185081808013ff


def q9e (j : Nat) : Nat := 0xc1009de4c0000284000045004a5c00c9005500000000000000000000000000000000000000000000008d0000000000d40000008c00000000009200


def q9h : Nat → q0e
  | 8 => (6,6,7,327686,51,6,4097,q98)
  | 9 => (69,5,7,2818098,102,10,4151,q99)
  | 10 => (373,4,7,4849791,119,14,4299,q93)
  | 11 => (216,3,7,1769495,85,14,4244,q94)
  | 12 => (30,2,7,327683,50,11,4144,q95)
  | 13 => (3,1,7,65537,0,6,4109,q96)
  | 14 => (1,0,7,65537,0,0,4105,q97)
  | _ => q2K


def q9g : Nat → Nat → Option (Nat × Nat)
  | 9 => q5V 1 113 0 8 3 3 q9f
  | 10 => q5V 26 127 7 13 7 4 q9a
  | 11 => q5V 159 691 9 15 9 4 q9b
  | 12 => q5V 102 467 8 14 8 4 q9c
  | 13 => q5V 16 163 4 11 5 4 q9d
  | 14 => q5V 3 59 0 8 2 4 q9e
  | _ => fun _ => none


def sg : Forest := ⟨511,14,fun i => sgY[i]?.getD (0,0),sgC,sgA,q9h,q9g⟩


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q9B : q54 sg (q1o q9H) = true := by
  simp only [q54, Bool.and_eq_true]
  refine ⟨⟨⟨by decide +kernel,by decide +kernel⟩,q7m (d:=6) ?_⟩,q7m (d:=3) ?_⟩
  all_goals simp only [q5R]
  all_goals repeat' apply And.intro
  all_goals decide +kernel


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q9w : q1j sg 8 0 6 = true := by
  apply q1x (ar:=9) (rows:=0) (d:=0)
  simp only [q1w,q1p]
  repeat' apply And.intro
  all_goals decide +kernel


theorem q91 : q1j sg 8 0 6 = true := q9w


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q9x : q1j sg 9 0 21 = true := by
  apply q1x (ar:=9) (rows:=0) (d:=2)
  simp only [q1w,q1p]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q9y : q1j sg 9 21 48 = true := by
  apply q1x (ar:=10) (rows:=0) (d:=3)
  simp only [q1w,q1p]
  repeat' apply And.intro
  all_goals decide +kernel


theorem q92 : q1j sg 9 0 69 = true := (@q1l sg 9 0 21 48 q9x q9y)


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q9i : q1j sg 10 0 3 = true := by
  apply q1x (ar:=9) (rows:=0) (d:=0)
  simp only [q1w,q1p]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q9l : q1j sg 10 3 128 = true := by
  apply q1x (ar:=10) (rows:=0) (d:=4)
  simp only [q1w,q1p]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q9j : q1j sg 10 131 111 = true := by
  apply q1x (ar:=10) (rows:=0) (d:=4)
  simp only [q1w,q1p]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q9k : q1j sg 10 242 128 = true := by
  apply q1x (ar:=11) (rows:=0) (d:=4)
  simp only [q1w,q1p]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q9m : q1j sg 10 370 3 = true := by
  apply q1x (ar:=11) (rows:=0) (d:=0)
  simp only [q1w,q1p]
  repeat' apply And.intro
  all_goals decide +kernel


theorem q8W : q1j sg 10 0 373 = true := (@q1l sg 10 0 131 242 (@q1l sg 10 0 3 128 q9i q9l) (@q1l sg 10 131 111 131 q9j (@q1l sg 10 242 128 3 q9k q9m)))


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q9n : q1j sg 11 0 2 = true := by
  apply q1x (ar:=9) (rows:=0) (d:=0)
  simp only [q1w,q1p]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q9p : q1j sg 11 2 62 = true := by
  apply q1x (ar:=10) (rows:=0) (d:=3)
  simp only [q1w,q1p]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q9q : q1j sg 11 64 123 = true := by
  apply q1x (ar:=11) (rows:=0) (d:=4)
  simp only [q1w,q1p]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q9o : q1j sg 11 187 29 = true := by
  apply q1x (ar:=12) (rows:=0) (d:=2)
  simp only [q1w,q1p]
  repeat' apply And.intro
  all_goals decide +kernel


theorem q8X : q1j sg 11 0 216 = true := (@q1l sg 11 0 64 152 (@q1l sg 11 0 2 62 q9n q9p) (@q1l sg 11 64 123 29 q9q q9o))


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q9r : q1j sg 12 0 1 = true := by
  apply q1x (ar:=9) (rows:=0) (d:=0)
  simp only [q1w,q1p]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q9s : q1j sg 12 1 12 = true := by
  apply q1x (ar:=10) (rows:=0) (d:=1)
  simp only [q1w,q1p]
  repeat' apply And.intro
  all_goals decide +kernel


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q9t : q1j sg 12 13 17 = true := by
  apply q1x (ar:=11) (rows:=0) (d:=1)
  simp only [q1w,q1p]
  repeat' apply And.intro
  all_goals decide +kernel


theorem q8Y : q1j sg 12 0 30 = true := (@q1l sg 12 0 1 29 q9r (@q1l sg 12 1 12 17 q9s q9t))


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q9u : q1j sg 13 0 3 = true := by
  apply q1x (ar:=10) (rows:=0) (d:=0)
  simp only [q1w,q1p]
  repeat' apply And.intro
  all_goals decide +kernel


theorem q8Z : q1j sg 13 0 3 = true := q9u


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q9v : q1j sg 14 0 1 = true := by
  apply q1x (ar:=9) (rows:=0) (d:=0)
  simp only [q1w,q1p]
  repeat' apply And.intro
  all_goals decide +kernel


theorem q90 : q1j sg 14 0 1 = true := q9v


set_option maxHeartbeats 0 in
theorem q9z : q1G sg 14 := by
  intro k hk
  interval_cases k
  · exact (rfl : q1j sg 0 0 0 = true)
  · exact (rfl : q1j sg 1 0 0 = true)
  · exact (rfl : q1j sg 2 0 0 = true)
  · exact (rfl : q1j sg 3 0 0 = true)
  · exact (rfl : q1j sg 4 0 0 = true)
  · exact (rfl : q1j sg 5 0 0 = true)
  · exact (rfl : q1j sg 6 0 0 = true)
  · exact (rfl : q1j sg 7 0 0 = true)
  · exact q91
  · exact q92
  · exact q8W
  · exact q8X
  · exact q8Y
  · exact q8Z
  · exact q90


set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
theorem q9C : q08 true graph 14 inputs.toFinset := by
  rw [show graph = qa5 sg by decide +kernel]
  exact q83 (g:=sg) (top:=14) (i:=0) (q15 q9H qau) q9B q9z (by decide) (by decide +kernel)


lemma nine_binary_lower (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 9 → Bool, C.eval (List.ofFn x) = q2I x) :
    15 ≤ C.gates.countP (fun g => !q5f g) := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (q9R C legal C.output r).trans ((computes (q8d r)).trans (q2J r).symm)
  have out := qaU (u := true) (execute C.gates inputs) C.output
  rw [goalEq] at out
  unfold q0f at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [q6Y pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := qaS (u := true) C.gates inputs legal (by simp) graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : inputs.all q7q = true := by decide +kernel
  rw [q6Z ns] at sub
  have idx (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 9, inputs.getD i.val zero = a := by
    rw [← input_list] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = inputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply q7L run inputs (inputs.getD i.val zero) sub (q0k i) (q7y i)
        (q7X.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      exact q7X.2 i j (fun hij =>
        hn (congrArg (fun t : Fin 9 => inputs.getD t.val zero) hij.symm))
  by_contra h
  have small : k ≤ 14 := by omega
  exact q9C k small (eq ▸ run)


lemma nine_reach_lower : Lower true inputs graph 15 := by
  apply q6b graph_proper (by decide +kernel) (by decide +kernel) ?_ q9C
  intro a ha
  have idx (v : Sig) (hv : v ∈ inputs) : ∃ i : Fin 9, inputs.getD i.val zero = v := by
    rw [← input_list] at hv
    exact List.mem_ofFn.mp hv
  obtain ⟨i, rfl⟩ := idx a ha
  refine ⟨q0k i, q7y i, q7X.1 i, ?_⟩
  intro v hv hn
  obtain ⟨j, rfl⟩ := idx v hv
  exact q7X.2 i j (fun hij =>
    hn (congrArg (fun t : Fin 9 => inputs.getD t.val zero) hij.symm))


end PEqualNP.Outside.L_meta_2373.NineSigned



namespace PEqualNP.Outside.L_meta_2373.Live1024
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 1024
def zero : Sig := 0
def one : Sig := BitVec.allOnes 1024
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
theorem allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
theorem bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
theorem flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩ 
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
theorem Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
theorem Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
theorem Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
    (stop : ∀ (hp : proper target), motive 0 {target} (Live.stop hp))
    (binary : ∀ {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
      (ha : proper a) (hb : proper b) (hab : a ≠ b)
      (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)),
      motive k (insert (bin d a b) U) tail →
      motive (k+1) (insert a (insert b U)) (Live.binary hd ha hb hab hfresh tail))
    {k : Nat} {S : Finset Sig} (h : Live u target k S) : motive k S h := by
  induction k generalizing S with
  | zero =>
    obtain ⟨rfl,hp⟩ := h
    exact stop hp
  | succ k ih =>
    obtain ⟨U,a,b,d,hd,rfl,ha,hb,hab,hf,tail⟩ := h
    exact binary hd ha hb hab hf tail (ih tail)

private lemma live_proper {u target k S} (h : Live u target k S) : ∀ a ∈ S, proper a := by
  induction h using Live.ind with
  | stop hp => simpa using hp
  | binary hd ha hb hab hf _ ih =>
    simp only [Finset.forall_mem_insert]
    exact ⟨ha,hb,fun a h => ih a (Finset.mem_insert_of_mem h)⟩

private lemma live_size {u target k S} (h : Live u target k S) : S.card ≤ k+1 := by
  induction h using Live.ind with
  | stop hp => simp
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have hu : bin d a b ∉ U := fun hm => hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hm))
    rw [Finset.card_insert_of_notMem hu] at ih
    have h1 := Finset.card_insert_le (a := a) (s := insert b U)
    have h2 := Finset.card_insert_le (a := b) (s := U)
    omega

def bit (i : Fin 1024) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
theorem bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
theorem nrm_false (a : Sig) : nrm false a = a := rfl
theorem nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
theorem nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
theorem neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
theorem nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
theorem proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
theorem proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
theorem bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
theorem nrm_prime (d : Bool) (a b : Sig) :
    ∃ e, e<4 ∧ nrm true (prime d a b) = bin e (nrm true a) (nrm true b) := by
  refine ⟨if d then (if bit 0 a then (if bit 0 b then 0 else 2) else (if bit 0 b then 3 else 1))
    else (if bit 0 a then (if bit 0 b then 1 else 3) else (if bit 0 b then 2 else 0)),?_,?_⟩
  · split_ifs <;> omega
  · apply bit_ext
    intro i
    cases d <;> cases ha : bit 0 a <;> cases hb : bit 0 b <;>
      simp only [nrm,bit_prime,ha,hb,bit_bin,bit_neg,Bool.true_and,Bool.false_and,Bool.and_true,Bool.and_false,Bool.false_or,
        Bool.or_false,Bool.true_or,Bool.or_true,Bool.false_eq_true,ite_true,ite_false] <;>
      cases hx : bit i a <;> cases hy : bit i b <;> simp [hx,hy,bit_neg,bit_prime]

def gv (w : List Sig) (g : Gate) : Sig :=
  let xs := g.inputs.map (fun i => w.getD i zero)
  match g.op with
  | .and => xs.foldr (prime false) one
  | .or => xs.foldr (prime true) zero
  | .not => neg (xs.headD zero)
  | _ => zero

def execute (gs : List Gate) (w : List Sig) : List Sig :=
  gs.foldl (fun l g => l ++ [gv l g]) w

def represented (w : List Sig) (v : Sig) : Prop := v ∈ w ∨ ¬proper v
def Repr (u : Bool) (w : List Sig) (v : Sig) : Prop := represented w (nrm u v)

private lemma bin_laws (a : Sig) :
    bin 0 a one = a ∧ bin 1 a zero = a ∧
    bin 0 a zero = zero ∧ bin 1 a one = one ∧
    bin 0 a a = a ∧ bin 1 a a = a ∧ bin 2 a a = zero ∧ bin 3 a a = zero ∧ bin 2 a zero = a ∧
    bin 3 zero a = a ∧ bin 2 zero a = zero ∧ bin 3 a zero = zero ∧ bin 0 zero a = zero ∧ bin 1 zero a = a ∧
    bin 0 one a = a ∧ bin 1 one a = one := by
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> apply bit_ext <;> intro i <;>
    simp [bit_bin,bit_zero,bit_one]

private lemma neg_laws : neg zero = one ∧ neg one = zero := by simp [neg,zero,one]

private lemma operand_cases {w : List Sig} {a : Sig} (h : represented w a) :
    a = zero ∨ a = one ∨ a ∈ w ∧ proper a := by
  by_cases hz : a = zero
  · exact Or.inl hz
  by_cases ho : a = one
  · exact Or.inr (Or.inl ho)
  exact Or.inr (Or.inr ⟨h.resolve_right (fun x => x ⟨hz,ho⟩),hz,ho⟩)

def witness (u : Bool) (w : List Sig) (z : Sig) : Prop :=
  ∃ d a b, allowed u d ∧ a ∈ w ∧ b ∈ w ∧ proper a ∧ proper b ∧ a ≠ b ∧ z = bin d a b

private lemma bin_rep {u w a b} (d : Nat) (hd : allowed u d) (ha : represented w a) (hb : represented w b)
    (no : u=true → a ≠ one ∧ b ≠ one) :
    represented w (bin d a b) ∨ witness u w (bin d a b) := by
  have rz : represented w zero := Or.inr (fun h => h.1 rfl)
  have ro : represented w one := Or.inr (fun h => h.2 rfl)
  obtain ⟨a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13,a14,a15,a16⟩ := bin_laws a
  obtain ⟨b1,b2,b3,b4,b5,b6,b7,b8,b9,b10,b11,b12,b13,b14,b15,b16⟩ := bin_laws b
  by_cases he : a=b
  · subst b
    left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a5.symm ▸ ha
    · exact a6.symm ▸ ha
    · exact a7.symm ▸ rz
    · exact a8.symm ▸ rz
  rcases operand_cases ha with rfl | rfl | ⟨ham,hap⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact b13.symm ▸ rz
    · exact b14.symm ▸ hb
    · exact b11.symm ▸ rz
    · exact b10.symm ▸ hb
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact b15.symm ▸ hb
    · exact b16.symm ▸ ro
    · exact absurd rfl (no hu).1
    · exact absurd rfl (no hu).1
  rcases operand_cases hb with rfl | rfl | ⟨hbm,hbp⟩
  · left
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩
    · exact a3.symm ▸ rz
    · exact a2.symm ▸ ha
    · exact a9.symm ▸ ha
    · exact a12.symm ▸ rz
  · left
    rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
    · exact a1.symm ▸ ha
    · exact a4.symm ▸ ro
    · exact absurd rfl (no hu).2
    · exact absurd rfl (no hu).2
  exact Or.inr ⟨d,a,b,hd,ham,hbm,hap,hbp,he,rfl⟩

theorem norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
theorem prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
    Repr u w (prime d a b) ∨ witness u w (nrm u (prime d a b)) := by
  cases u
  · have e : prime d a b = bin (if d then 1 else 0) a b := by cases d <;> rfl
    have h := bin_rep (u:=false) (if d then 1 else 0) (Or.inl (by split <;> omega)) ha hb (by simp)
    unfold Repr
    simp only [nrm_false] at h ⊢
    rwa [e]
  · obtain ⟨e,he,eq⟩ := nrm_prime d a b
    unfold Repr
    rw [eq]
    exact bin_rep e (Or.inr ⟨rfl,he⟩) ha hb (fun _ => ⟨norm_ne_one a,norm_ne_one b⟩)
theorem repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
private lemma get_rep {u} (w : List Sig) (i : Nat) : Repr u (w.map (nrm u)) (w.getD i zero) := by
  simp only [List.getD_eq_getElem?_getD]
  cases h : w[i]? with
  | none => exact repr_const (Or.inl rfl)
  | some a => exact Or.inl (List.mem_map_of_mem (List.mem_of_getElem? h))
theorem repr_neg {w a} (h : Repr true w a) : Repr true w (neg a) := by
  unfold Repr
  rwa [nrm_neg]

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false
private lemma gate_rep (u : Bool) (w : List Sig) (g : Gate)
    (h : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → isNot g=false) :
    Repr u (w.map (nrm u)) (gv w g) ∨ (isNot g=false ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at h
  obtain ⟨ho,hl⟩ := h
  have prim (d : Bool) : Repr u (w.map (nrm u)) ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one)) ∨
      witness u (w.map (nrm u)) (nrm u ((l.map (fun i => w.getD i zero)).foldr (prime d) (if d then zero else one))) := by
    have unit (v : Sig) : prime d v (if d then zero else one) = v := by
      apply bit_ext
      intro i
      cases d <;> simp [bit_prime,bit_zero,bit_one]
    cases l with
    | nil => exact Or.inl (repr_const (by cases d <;> simp))
    | cons i l =>
      cases l with
      | nil =>
        simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
        exact Or.inl (get_rep w i)
      | cons j l =>
        cases l with
        | cons a l => simp at hl
        | nil =>
          simp only [List.map_cons,List.map_nil,List.foldr_cons,List.foldr_nil,unit]
          exact prime_rep d (get_rep w i) (get_rep w j)
  rcases ho with rfl | rfl | rfl
  · exact (prim false).imp id (fun h => ⟨rfl,h⟩)
  · exact (prim true).imp id (fun h => ⟨rfl,h⟩)
  · cases u
    · exact absurd (mono rfl) (by simp [isNot])
    left
    cases l with
    | nil => exact repr_const (Or.inr (by simp [gv,neg_laws]))
    | cons i l => exact repr_neg (get_rep w i)

private lemma pull_gate {u target} {w : List Sig} {z : Sig} {k S c} (h : Live u target k S)
    (hz : represented w z ∨ (c=1 ∧ witness u w z)) (sub : ∀ a ∈ S, a ∈ w++[z]) :
    ∃ k' S', k' ≤ k+c ∧ Live u target k' S' ∧ ∀ a ∈ S', a ∈ w := by
  by_cases hm : z ∈ S
  · by_cases hw : z ∈ w
    · refine ⟨k,S,by omega,h,?_⟩
      intro a ha
      have hu : a ∈ w ∨ a = z := by simpa using sub a ha
      rcases hu with hu | rfl
      · exact hu
      · exact hw
    · have hp := live_proper h z hm
      rcases hz with hr | ⟨rfl,d,a,b,hd,ha,hb,pa,pb,hab,eq⟩
      · exact False.elim ((hr.resolve_left hw) hp)
      · subst z
        let U := S.erase (bin d a b)
        have ht : Live u target k (insert (bin d a b) U) := by simpa [U,Finset.insert_erase hm] using h
        have hu : ∀ v ∈ U, v ∈ w := by
          intro v hv
          obtain ⟨hne,hm⟩ := Finset.mem_erase.mp hv
          simpa [hne] using sub v hm
        have hf : bin d a b ∉ insert a (insert b U) := by
          intro hh
          rcases Finset.mem_insert.mp hh with eq | u
          · exact hw (eq.symm ▸ ha)
          rcases Finset.mem_insert.mp u with eq | u
          · exact hw (eq.symm ▸ hb)
          · exact hw (hu _ u)
        exact ⟨_,_,Nat.le_refl _,Live.binary hd pa pb hab hf ht,by simpa using And.intro ha (And.intro hb hu)⟩
  · refine ⟨k,S,by omega,h,?_⟩
    intro a ha
    have hn : a ≠ z := fun hh => hm (hh ▸ ha)
    simpa [hn] using sub a ha

private lemma extract {u target} (gs : List Gate) (w : List Sig)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp) ∧ g.inputs.length≤2)
    (mono : u=false → ∀ g ∈ gs, isNot g=false)
    (hp : proper target) (hout : target ∈ (execute gs w).map (nrm u)) :
    ∃ k S, k ≤ gs.countP (fun g => !isNot g) ∧ Live u target k S ∧ ∀ a ∈ S, a ∈ w.map (nrm u) := by
  induction gs generalizing w with
  | nil => exact ⟨0,{target},by simp,Live.stop hp,by simpa [execute] using hout⟩
  | cons g gs ih =>
    obtain ⟨k,S,hk,ht,hs⟩ := ih (w++[gv w g]) (fun a ha => legal a (by simp [ha]))
      (fun hu a ha => mono hu a (by simp [ha])) hout
    have rep := gate_rep u w g (legal g (by simp)) (fun hu => mono hu g (by simp))
    rw [List.map_append] at hs
    have rep' : represented (w.map (nrm u)) (nrm u (gv w g)) ∨
        ((if isNot g then 0 else 1)=1 ∧ witness u (w.map (nrm u)) (nrm u (gv w g))) :=
      rep.imp id (fun h => ⟨by simp [h.1],h.2⟩)
    obtain ⟨l,T,hl,hu,hT⟩ := pull_gate ht rep' hs
    refine ⟨l,T,?_,hu,hT⟩
    rw [List.countP_cons]
    cases hn : isNot g <;> simp [hn] at hl ⊢ <;> omega

private lemma b_read (i) (w : List Sig) (j : Nat) :
    (w.map (bit i)).getD j false = bit i (w.getD j zero) := by
  simp only [List.getD_eq_getElem?_getD,List.getElem?_map]
  cases w[j]? with
  | none => exact (bit_zero _).symm
  | some a => rfl

private lemma run_bit (i) (g : Gate) (w : List Sig)
    (hg : g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    bit i (gv w g) = g.op.eval (g.inputs.map fun j => (w.map (bit i)).getD j false) := by
  obtain ⟨o,l⟩ := g
  simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hg
  simp only [b_read]
  rcases hg with rfl | rfl | rfl
  · induction l with
    | nil => exact bit_one _
    | cons a l ih =>
      change bit i (prime false _ _) = (_ && _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) && x) ih
  · induction l with
    | nil => exact bit_zero _
    | cons a l ih =>
      change bit i (prime true _ _) = (_ || _)
      rw [bit_prime]; exact congrArg (fun x => bit i (w.getD a zero) || x) ih
  · cases l with
    | nil =>
      change bit i (neg zero) = !false
      rw [bit_neg,bit_zero]
    | cons a l => exact bit_neg _ _

private lemma execute_bits (gs : List Gate) (i) (w : List Sig)
    (hg : ∀ g ∈ gs, g.op ∈ ({GateOp.and,GateOp.or,GateOp.not} : Set GateOp)) :
    (execute gs w).map (bit i) =
    gs.foldl (fun (l : List Bool) g => l++[g.op.eval (g.inputs.map fun j => l.getD j false)]) (w.map (bit i)) := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (execute gs (w++[gv w g])).map _ = _
    rw [ih _ (fun a ha => hg a (by simp [ha]))]
    simp only [List.foldl_cons,List.map_append,List.map_singleton,run_bit i g w (hg g (by simp))]

abbrev Wire (R : Type) := R → Bool

def inv {R} (a : Wire R) : Wire R := fun r => !(a r)

def combine {R} (isOr : Bool) (a b : Wire R) : Wire R :=
  if isOr then fun r => a r || b r else fun r => a r && b r
def comb {R} (d : Nat) (a b : Wire R) : Wire R :=
  if d=0 then combine false a b else if d=1 then combine true a b else
    if d=2 then combine false a (inv b) else combine false (inv a) b

def Constant {R} (a : Wire R) : Prop := ∃ b : Bool, a = fun _ => b

noncomputable def cost {R} (a : Wire R) : Nat := by
  classical exact if Constant a then 1 else 0

noncomputable def mass {R} (xs : List (Wire R)) : Nat := (xs.map cost).sum

def Available {R} (u : Bool) (pool : List (Wire R)) (v : Wire R) : Prop :=
  v ∈ pool ∨ Constant v ∨ (u=true ∧ inv v ∈ pool)

def supply {R} (u : Bool) (pool xs : List (Wire R)) := ∀ a ∈ xs, Available u pool a

def Reach {R} (u : Bool) (roots : List (Wire R)) : Nat → List (Wire R) → Prop
  | 0,b => b=roots
  | p+1,c => ∃ (op : Bool) (bank : List (Wire R)) (a b : Wire R), Reach u roots p bank ∧ Available u bank a ∧
      Available u bank b ∧ c=combine op a b :: bank
theorem Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
theorem Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
theorem Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
    (start : motive 0 roots Reach.start)
    (two : ∀ {p bank a b} (op : Bool) (h : Reach u roots p bank) (ha : Available u bank a)
      (hb : Available u bank b), motive p bank h →
      motive (p+1) (combine op a b :: bank) (Reach.two op h ha hb))
    {p bank} (h : Reach u roots p bank) : motive p bank h := by
  induction p generalizing bank with
  | zero =>
    obtain rfl := h
    exact start
  | succ p ih =>
    obtain ⟨op,bank,a,b,h,ha,hb,rfl⟩ := h
    exact two op h ha hb (ih h)

def kept {α : Type} (save : Bool) (x : α) (xs : List α) := if save then x::xs else xs

def Run {R} (u : Bool) (goal : Wire R) : Nat → List (Wire R) → Prop
  | 0,zs => List.Perm [goal] zs
  | s+1,zs => ∃ (op : Nat) (ka kb : Bool) (a b : Wire R) (rest : List (Wire R)), allowed u op ∧ (a::b::rest).Perm zs ∧
      Run u goal s (comb op a b :: kept ka a (kept kb b rest))
theorem Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
theorem Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
theorem Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
theorem Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
    (stop : motive 0 [goal] Run.stop)
    (perm : ∀ {s xs zs} (p : List.Perm xs zs) (h : Run u goal s xs), motive s xs h → motive s zs (Run.perm p h))
    (two : ∀ {s a b rest} (op : Nat) (hd : allowed u op) (ka kb : Bool) (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))),
      motive s _ h → motive (s+1) (a::b::rest) (Run.two op hd ka kb h))
    {s ws} (h : Run u goal s ws) : motive s ws h := by
  induction s generalizing ws with
  | zero => exact perm h Run.stop stop
  | succ s ih =>
    obtain ⟨op,ka,kb,a,b,rest,hd,p,h⟩ := h
    exact perm p (Run.two op hd ka kb h) (two op hd ka kb h (ih h))

theorem mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

theorem mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

theorem inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

theorem inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
theorem cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
theorem avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
theorem both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

theorem from_constant {R u} (op) {a b : Wire R} {bank}
    (h : Constant a ∨ Constant b) (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (combine op a b) := by
  rcases h with ⟨v,rfl⟩ | ⟨v,rfl⟩
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using hb
    · simpa [combine] using hb
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)
  · cases op <;> cases v
    · exact Or.inr (Or.inl ⟨false, by funext x; simp [combine]⟩)
    · simpa [combine] using ha
    · simpa [combine] using ha
    · exact Or.inr (Or.inl ⟨true, by funext x; simp [combine]⟩)

theorem available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

theorem extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (combine op a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (combine op a b) := by
  classical
  by_cases c : Constant a ∨ Constant b
  · refine ⟨p,bank,hp,from_constant op c ha hb,fun _ h => h,?_⟩
    by_cases ca : Constant a <;> by_cases cb : Constant b
    · simp [cost,ca,cb,both_constant op ca cb]
    · simp [cost,ca,cb]
    · simp [cost,ca,cb]
    · exact False.elim (c.elim ca cb)
  · have ca : ¬Constant a := fun h => c (Or.inl h)
    have cb : ¬Constant b := fun h => c (Or.inr h)
    exact ⟨p+1,_,Reach.two op hp ha hb,Or.inl (by simp),fun _ h => available_cons _ h,
      by simp [cost,ca,cb]⟩
theorem comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
theorem extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

theorem mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

theorem contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
    (h : Run u goal s ws) (roots : List (Wire R)) {p bank}
    (hp : Reach u roots p bank) (hs : supply u bank ws) :
    ∃ q next, Reach u roots q next ∧ Available u next goal ∧ q+mass ws ≤ p+s := by
  classical
  induction h using Run.ind generalizing p bank with
  | stop =>
    exact ⟨p,bank,hp,hs _ (by simp),by simp [mass,cost,nc]⟩
  | perm eq _ ih =>
    have hsub : supply u bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q,W,hW,hv,hl⟩ := ih hp hsub
    exact ⟨q,W,hW,hv,by simpa only [mass,←(eq.map cost).sum_eq] using hl⟩
  | @two s a b rest op hd ka kb _ ih =>
    obtain ⟨r,T,hT,hz,inc,le⟩ := extend_comb roots op hd hp (hs a (by simp)) (hs b (by simp))
    have ht : supply u T (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v h
      rcases List.mem_cons.mp h with rfl | hh
      · exact hz
      · apply inc v
        apply hs
        rcases mem_kept hh with rfl | hh
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hh))
    obtain ⟨q,W,hW,hv,hl⟩ := ih hT ht
    have hlen := mass_kept a (kept kb b rest) ka
    have hlen' := mass_kept b rest kb
    rw [mass_cons] at hl
    refine ⟨q,W,hW,hv,?_⟩
    rw [mass_cons,mass_cons]
    omega

def restrictRows {R S : Type} (rows : S → R) (a : Wire R) : Wire S :=
  fun r => a (rows r)

theorem restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

theorem restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
theorem restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

theorem projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 1024
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

theorem bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

theorem table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

theorem observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

theorem obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

theorem obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

theorem map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

theorem kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

theorem kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

theorem list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
    (hv : v.Nodup) (eqv : v.toFinset = S) : Run u (observe T) k (v.map observe) := by
  classical
  induction h using Live.ind generalizing v with
  | stop hp =>
    have eq : [T].Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp) hv
      simpa [eqv]
    exact Run.perm (eq.map _) Run.stop
  | @binary k U a b d hd ha hb hab fresh _ ih =>
    let rest := ((U.erase a).erase b).toList
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let mid := kept kb b rest
    let tail := kept ka a mid
    have er : rest.toFinset = (U.erase a).erase b := by simp [rest]
    have ar : a ∉ rest := by simp [rest]
    have br : b ∉ rest := by simp [rest]
    have hr : rest.Nodup := Finset.nodup_toList _
    have bm := kept_nd kb b rest hr br
    have am : a ∉ mid := by cases h : kb <;> simp [mid,kept,h,hab,ar]
    have nd := kept_nd ka a mid bm am
    have ht : tail.toFinset = U := by
      change (kept ka a (kept kb b rest)).toFinset = U
      rw [kept_fin,kept_fin,er]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases aj : j=a <;>
        by_cases bj : j=b <;> simp_all [ka,kb]
    have hf : bin d a b ∉ tail := by
      intro hz
      exact fresh (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ht ▸ List.mem_toFinset.mpr hz)))
    have progress := ih (bin d a b::tail) (List.nodup_cons.mpr ⟨hf,nd⟩) (by simp [ht])
    change Run _ _ _ ((bin d a b::kept ka a (kept kb b rest)).map observe) at progress
    rw [List.map_cons,map_kept,map_kept,obs_bin] at progress
    have perm : (a::b::rest).Perm v := by
      apply List.perm_of_nodup_nodup_toFinset_eq (by simp [hab,ar,br,hr]) hv
      ext j
      by_cases ja : j=a <;> by_cases jb : j=b <;> simp_all [er]
    exact Run.perm (perm.map _) (Run.two d hd ka kb progress)


theorem table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

theorem table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

theorem available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
    Repr u ((bank.map table).map (nrm u)) (table a) := by
  rcases h with hm | ⟨b,rfl⟩ | ⟨rfl,hm⟩
  · exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hm))
  · apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (bit_table _ i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (bit_table _ i).trans (bit_one i).symm)
  · have := table_inv a
    refine Or.inl ?_
    rw [←nrm_neg,←this]
    exact List.mem_map_of_mem (List.mem_map_of_mem hm)

theorem reach_live_sub {u} {roots : List (Wire Row)} {p bank}
    (h : Reach u roots p bank) {T k S} (run : Live u T k S)
    (sub : ∀ a ∈ S, a ∈ (bank.map table).map (nrm u)) :
    ∃ l V, l ≤ p+k ∧ Live u T l V ∧ ∀ a ∈ V, a ∈ (roots.map table).map (nrm u) := by
  induction h using Reach.ind generalizing k S with
  | start => exact ⟨k,S,by omega,run,sub⟩
  | @two p bank a b d h ha hb ih =>
    rw [List.map_cons,List.map_cons,table_prime] at sub
    have rep := prime_rep d (available_rep ha) (available_rep hb)
    obtain ⟨k',S',hk,run',sub'⟩ := pull_gate (c:=1) run (rep.imp id (fun h => ⟨rfl,h⟩))
      (fun a hm => by simpa [or_comm] using sub a hm)
    obtain ⟨l,V,hl,hr,hs⟩ := ih run' sub'
    exact ⟨l,V,by omega,hr,hs⟩

def plainWord (a : Sig) : Bool := !(bit 0 a)
theorem nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
theorem reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (h : Reach u (roots.map observe) p bank) (hit : Available u bank (observe T)) :
    ∃ k S, k ≤ p ∧ Live u T k S ∧ ∀ a ∈ S, a ∈ roots := by
  have hm := available_rep hit
  rw [table_observe] at hm
  unfold Repr at hm
  rw [nrm_id (by simpa [plainWord] using nT)] at hm
  have mem := hm.resolve_right (fun hn => hn hp)
  obtain ⟨l,V,hl,hr,hs⟩ := reach_live_sub h (Live.stop hp) (by simpa using mem)
  refine ⟨l,V,by omega,hr,?_⟩
  have e : (roots.map observe).map table = roots := by simp [List.map_map,Function.comp_def,table_observe]
  rw [e,nrm_map nR] at hs
  exact hs

theorem live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
    (diff : bit r T ≠ bit s T) : ∃ a ∈ S, bit r a ≠ bit s a := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,diff⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hd⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · by_cases aeq : bit r a = bit s a
      · refine ⟨b,by simp,?_⟩
        intro beq
        exact hd (by rw [bit_bin,bit_bin,aeq,beq])
      · exact ⟨a,by simp,aeq⟩
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hd⟩

theorem raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def inputs : List Sig := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa,
  0xcccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccccc,
  0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0,
  0xff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00ff00,
  0xffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000ffff0000,
  0xffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000ffffffff00000000,
  0xffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000ffffffffffffffff0000000000000000,
  0xffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000ffffffffffffffffffffffffffffffff00000000000000000000000000000000,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff0000000000000000000000000000000000000000000000000000000000000000,
  0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000]
def graph : Sig := 0xffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffc8fffffffffffffffffffffffffffffffffffffffffffffffffffffaeafffff8c8fffffffffffffffffffffffffffafff8ffffffffffffffffffffffffffeaffc8fffffffffffefcfcfffffffffffaf8f8ffeefeeeffeefcccffeafaeaffeaf8c8
def sample (r : Row) (j : Fin 10) := bit r (inputs.getD j.val zero)
def edge (x : Fin 10 → Bool) : Bool :=
  (x 0 && x 1) || (x 1 && x 2) || (x 2 && x 3) || (x 3 && x 4) || (x 4 && x 0) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 9 && x 6) || (x 6 && x 8) || (x 8 && x 5)
theorem edge_table : ∀ r : Row, bit r graph = edge (sample r) := by decide +kernel
theorem graph_proper : proper graph := by unfold proper; decide +kernel
theorem input_list : List.ofFn (fun j : Fin 10 => inputs.getD j.val zero) = inputs := rfl
theorem sampled (r : Row) : List.ofFn (sample r) = inputs.map (bit r) := by
  rw [←input_list]
  rw [List.map_ofFn]
  rfl

theorem table_eval (C : Circuit) (h : PEqualNP.MetaComplexity.FanInTwo C)
    (i : Nat) (r : Row) : bit r ((execute C.gates inputs).getD i zero) =
      (C.wires (List.ofFn (sample r))).getD i false := by
  rw [←b_read,execute_bits _ _ _ (fun g hg => (h g hg).1),sampled]
  rfl

def rename (f : Row → Row) (a : Sig) := table fun r => bit (f r) a
theorem bit_rename (f : Row → Row) (a : Sig) (r : Row) :
    bit r (rename f a) = bit (f r) a := bit_table _ _
theorem observe_rename (f : Row → Row) (a : Sig) :
    observe (rename f a) = restrictRows f (observe a) := by funext r; exact bit_rename f a r
theorem rename_bin (f : Row → Row) (d : Nat) (a b : Sig) :
    rename f (bin d a b) = bin d (rename f a) (rename f b) := by
  apply bit_ext
  intro r
  simp only [bit_rename,bit_bin]

theorem rename_inj (f : Row → Row) (onto : Function.Surjective f) :
    Function.Injective (rename f) := by
  intro a b h
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  obtain ⟨r,hr⟩ := onto ⟨j,hj⟩
  have he := congrArg (bit r) h
  change bit ⟨j,hj⟩ a = bit ⟨j,hj⟩ b
  rw [bit_rename,bit_rename,hr] at he
  exact he
theorem rename_constants (f : Row → Row) : rename f zero = zero ∧ rename f one = one := by
  constructor <;> apply BitVec.eq_of_getLsbD_eq <;> intro j hj
  · exact (bit_rename f zero ⟨j,hj⟩).trans ((bit_zero _).trans (bit_zero ⟨j,hj⟩).symm)
  · exact (bit_rename f one ⟨j,hj⟩).trans ((bit_one _).trans (bit_one ⟨j,hj⟩).symm)
theorem live_rename {u T k S} (h : Live u T k S) (f : Row → Row) (onto : Function.Surjective f) :
    Live u (rename f T) k (S.image (rename f)) := by
  have inj := rename_inj f onto
  obtain ⟨fz,fo⟩ := rename_constants f
  have pp (v) (p : proper v) : proper (rename f v) :=
    ⟨fun e => p.1 (inj (e.trans fz.symm)),fun e => p.2 (inj (e.trans fo.symm))⟩
  induction h using Live.ind with
  | stop hp => simpa using Live.stop (pp _ hp)
  | @binary k U a b d hd ha hb hab hf _ ih =>
    have fresh : rename f (bin d a b) ∉ (insert a (insert b U)).image (rename f) := by
      intro hm
      obtain ⟨v,hv,eq⟩ := Finset.mem_image.mp hm
      exact hf (inj eq ▸ hv)
    simp only [Finset.image_insert,rename_bin] at fresh ih ⊢
    exact Live.binary hd (pp _ ha) (pp _ hb) (fun hh => hab (inj hh)) fresh ih

theorem mono_row_difference {u T k S} (h : Live u T k S) (none : u=false) {r s : Row}
    (pos : bit r T = true) (negRow : bit s T = false) :
    ∃ a ∈ S, bit r a = true ∧ bit s a = false := by
  induction h using Live.ind with
  | stop hp => exact ⟨_,by simp,pos,negRow⟩
  | @binary k U a b d hd ha hb hab hf _ ih =>
    obtain ⟨v,hv,hp,hn⟩ := ih
    rcases Finset.mem_insert.mp hv with rfl | hu
    · rw [bit_bin] at hp hn
      subst none
      rcases allowed_four hd with rfl | rfl | ⟨h,_⟩ | ⟨h,_⟩
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · cases p : bit r a <;> cases q : bit s a <;> cases u : bit r b <;> cases z : bit s b <;> simp_all
      · exact Bool.noConfusion h
      · exact Bool.noConfusion h
    · exact ⟨v,Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hu),hp,hn⟩

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p
theorem reach_up {R u} {roots : List (Wire R)} {p bank} (h : Reach false roots p bank) : Reach u roots p bank := by
  have up {bank : List (Wire R)} {a} (h : Available false bank a) : Available u bank a :=
    h.imp id (Or.imp id (fun h => Bool.noConfusion h.1))
  induction h using Reach.ind with
  | start => exact Reach.start
  | two op h ha hb ih => exact Reach.two op ih (up ha) (up hb)
theorem lower_down {u roots T L} (h : Lower true roots T L) : Lower u roots T L := by
  cases u
  · exact fun p bank hr ha => h p bank (reach_up hr) (ha.imp id (Or.imp id (fun h => Bool.noConfusion h.1)))
  · exact h

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

theorem lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
    (essential : ∀ a ∈ roots, Essential T roots a)
    (noRun : Impossible u T L roots.toFinset) : Lower u roots T (L+1) := by
  intro p bank h ha
  obtain ⟨k,S,hk,run,hs⟩ := reach_live hp nT nR h ha
  have he : roots.toFinset = S := by
    ext a
    rw [List.mem_toFinset]
    refine ⟨fun hm => ?_,hs a⟩
    obtain ⟨r,s,hd,iso⟩ := essential _ hm
    exact raw_required run roots a hs r s hd iso
  by_contra! small
  exact noRun k (by omega) (he.symm ▸ run)

theorem observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv

theorem mass_append {R} (a b : List (Wire R)) : mass (a++b) = mass a + mass b := by
  simp [mass]
theorem mass_constants {R} (xs : List (Wire R)) (hc : ∀ x ∈ xs, Constant x) :
    mass xs = xs.length := by
  induction xs with
  | nil => simp [mass]
  | cons a xs ih =>
    have ha := hc a (by simp)
    simp only [mass_cons,List.length_cons,cost,if_pos ha,ih (fun x hx => hc x (by simp [hx]))]
    omega

theorem lower_slice {u} {roots other : List Sig} {T G : Sig} (pT : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true) (pG : proper G)
    (r : Row → Row) (eq : rename r T = G)
    (covered : ∀ a ∈ roots, Available u (other.map observe) (observe (rename r a)))
    (singles : Finset Sig) (necessary : ∀ a ∈ singles, Essential T roots a)
    (constant : ∀ a ∈ singles, Constant (observe (rename r a)))
    (L : Nat) (prior : Lower u other G L) : Lower u roots T (L + singles.card) := by
  classical
  intro p bank hh ha
  obtain ⟨k,S,hk,run,sub⟩ := reach_live pT nT nR hh ha
  have subS : singles ⊆ S := by
    intro a hs
    obtain ⟨i,j,hd,hiso⟩ := necessary a hs
    exact raw_required run roots a sub i j hd hiso
  let front := singles.toList ++ (S \ singles).toList
  have nd : front.Nodup := by
    simp only [front,List.nodup_append]
    refine ⟨Finset.nodup_toList _,Finset.nodup_toList _,?_⟩
    intro a ha b hb he
    subst b
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hb)).2 (Finset.mem_toList.mp ha)
  have fe : front.toFinset=S := by ext a; simp [front,Finset.union_sdiff_of_subset subS]
  have run' := list_run run front nd fe
  have gc : restrictRows r (observe T) = observe G := (observe_rename _ _).symm.trans (congrArg observe eq)
  have supp : supply u (other.map observe) ((front.map observe).map (restrictRows r)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
    rw [←observe_rename]
    exact covered a (sub _ (fe ▸ List.mem_toFinset.mpr hmem))
  have bound := projected_bound r run' (gc ▸ observe_proper pG) Reach.start supp
    (L:=L) (gc ▸ prior)
  have massLo : singles.card ≤ mass ((front.map observe).map (restrictRows r)) := by
    simp only [front,List.map_append,mass_append]
    let xs := (singles.toList.map observe).map (restrictRows r)
    have only : ∀ v ∈ xs, Constant v := by
      intro v hv
      obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
      obtain ⟨a,hmem,rfl⟩ := List.mem_map.mp hm
      rw [←observe_rename]
      exact constant _ (Finset.mem_toList.mp hmem)
    have sz := mass_constants xs only
    simp only [xs,List.length_map,Finset.length_toList] at sz
    change singles.card ≤ mass xs + _
    rw [sz]
    omega
  omega



def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

theorem erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

theorem enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
    (twoStep : ∀ a ∈ ws, ∀ b ∈ ws, ∀ d, allowed u d → ∀ ka kb, a ≠ b → bin d a b ∉ ws →
      proper (bin d a b) → (childTwo ws a b d ka kb).length ≤ cap →
      Impossible u T (cap-1) (childTwo ws a b d ka kb).toFinset) :
    Impossible u T cap ws.toFinset := by
  classical
  intro k hk h
  generalize he : ws.toFinset = S at h
  induction h using Live.ind with
  | stop hp =>
    have mem : T ∈ ws.toFinset := he.symm ▸ Finset.mem_singleton_self _
    exact out (List.mem_toFinset.mp mem)
  | @binary k U a b d hd ha hb hab hf tail _ =>
    have am : a ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_self _ _)
    have bm : b ∈ ws := List.mem_toFinset.mp (he.symm ▸ Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have fresh : bin d a b ∉ ws := fun h => hf (he ▸ List.mem_toFinset.mpr h)
    have hz := live_proper tail _ (Finset.mem_insert_self _ _)
    let ka := decide (a ∈ U)
    let kb := decide (b ∈ U)
    let rest := (ws.erase a).erase b
    have er : rest.toFinset = (ws.toFinset.erase a).erase b := by
      rw [show rest=(ws.erase a).erase b by rfl,erase_fin (hn.erase _) b,
        erase_fin hn a]
    have ke : (kept ka a (kept kb b rest)).toFinset = U := by
      rw [kept_fin,kept_fin,er,he]
      ext j
      by_cases aa : a ∈ U <;> by_cases bb : b ∈ U <;> by_cases ja : j=a <;>
        by_cases jb : j=b <;> simp_all [ka,kb]
    have rn : rest.Nodup := (hn.erase _).erase _
    have ar : a ∉ rest := fun h => (hn.not_mem_erase) (List.mem_of_mem_erase h)
    have br : b ∉ rest := (hn.erase a).not_mem_erase
    have nk := kept_nd kb b rest rn br
    have ax : a ∉ kept kb b rest := by cases kb <;> simp [kept,ar,hab]
    have nd : (childTwo ws a b d ka kb).Nodup := by
      refine List.nodup_cons.mpr ⟨?_,kept_nd ka a _ nk ax⟩
      intro h
      exact hf (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (ke ▸ List.mem_toFinset.mpr h)))
    have eq : (childTwo ws a b d ka kb).toFinset = insert (bin d a b) U := by
      change (bin d a b::kept ka a (kept kb b rest)).toFinset = _
      simp [ke]
    have sc := live_size tail
    have len : (childTwo ws a b d ka kb).length ≤ cap := by
      rw [←List.toFinset_card_of_nodup nd,eq]
      omega
    exact twoStep a am b bm d hd ka kb hab fresh hz len k (by omega) (eq.symm ▸ tail)

def Sep (T : Sig) (width : Nat) (pos negRow : Fin width → Row)
    (asig : Sig → BitVec width × BitVec width) : Prop :=
  (∀ i, bit (pos i) T = true ∧ bit (negRow i) T = false) ∧
  ∀ w i, (asig w).1.getLsbD i.val = bit (pos i) w ∧
    (asig w).2.getLsbD i.val = bit (negRow i) w

def column {n} (oriented : Bool) (s : BitVec n × BitVec n) : BitVec n :=
  if oriented then s.1 &&& ~~~s.2 else s.1 ^^^ s.2

def covered {n} (oriented : Bool) (sig : Sig → BitVec n × BitVec n) : List Sig → BitVec n
  | [] => 0
  | a::ws => column oriented (sig a) ||| covered oriented sig ws

theorem covered_bit {n : Nat} {oriented : Bool} {sig : Sig → BitVec n × BitVec n} {ws : List Sig} {i : Fin n} :
    (covered oriented sig ws).getLsbD i.val = true ↔
    ∃ a ∈ ws, (column oriented (sig a)).getLsbD i.val = true := by
  induction ws with
  | nil => simp [covered]
  | cons a ws ih =>
    simp only [covered,BitVec.getLsbD_or,Bool.or_eq_true,ih,List.mem_cons,exists_eq_or_imp]

theorem cover_sound {u T k S} (h : Live u T k S) {ws : List Sig} (he : ws.toFinset=S)
    {width : Nat} {r s : Fin width → Row} {sig} (correct : Sep T width r s sig)
    (oriented : Bool) (zeroNot : oriented=true → u=false) :
    covered oriented sig ws = BitVec.allOnes width := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  let i : Fin width := ⟨j,hj⟩
  have yes := (correct.1 i).1
  have no := (correct.1 i).2
  rw [BitVec.getLsbD_allOnes]; simp only [hj,decide_true]
  apply (covered_bit (i:=i)).mpr
  cases oriented with
  | false =>
    obtain ⟨a,ha,hd⟩ := live_row_difference h (show bit (r i) T ≠ bit (s i) T by simp [yes,no])
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,Bool.false_eq_true,ite_false,BitVec.getLsbD_xor,(correct.2 a i).1,(correct.2 a i).2]
    cases hx : bit (r i) a <;> cases hy : bit (s i) a <;> simp_all
  | true =>
    obtain ⟨a,ha,hp,hn⟩ := mono_row_difference h (zeroNot rfl) yes no
    refine ⟨a,List.mem_toFinset.mp (he.symm ▸ ha),?_⟩
    simp only [column,ite_true,BitVec.getLsbD_and,BitVec.getLsbD_not,i.isLt,decide_true,
      Bool.true_and,(correct.2 a i).1,(correct.2 a i).2,hp,hn,Bool.not_false,Bool.and_self]

theorem cover_required {u T ws k} (h : Live u T k (List.toFinset ws)) {n : Nat} {r s : Fin n → Row} {sig}
    (correct : Sep T n r s sig) :
    covered (!u) sig ws = BitVec.allOnes n := by
  apply cover_sound h rfl correct
  simp

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p

def masked (d a : Sig) := a &&& d
def availableB (u : Bool) (d : Sig) (pool : List Sig) (a : Sig) :=
  let m := masked d a
  m == zero || m == d || (pool.map (masked d)).any (fun v => v==m) ||
    (u && (let c := masked d (neg a); (pool.map (masked d)).any (fun v => v==c)))

theorem masked_eq {f : Row → Row} {d a b : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = masked d b) :
    restrictRows f (observe a) = restrictRows f (observe b) := by
  funext r
  have h := congrArg (bit (f r)) eq
  change bit (f r) a = bit (f r) b
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using h

theorem masked_zero {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = zero) : restrictRows f (observe a) = fun _ => false := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = false
  rw [bit_zero] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

theorem masked_one {f : Row → Row} {d a : Sig} (dom : ∀ r, bit (f r) d = true)
    (eq : masked d a = d) : restrictRows f (observe a) = fun _ => true := by
  funext r
  have he := congrArg (bit (f r)) eq
  change bit (f r) a = true
  rw [dom r] at he
  simpa only [bit,masked,BitVec.getLsbD_and,show d.getLsbD (f r).val = true from dom r,
    Bool.and_true] using he

def poolSupply (u : Bool) (f : Row → Row) (bank : List (Wire Row)) (pool : List Sig) :=
  ∀ a ∈ pool, Available u bank (restrictRows f (observe a))

theorem availableB_sound {u} {f : Row → Row} {d a : Sig} {bank pool}
    (dom : ∀ r, bit (f r) d = true) (supplyB : poolSupply u f bank pool)
    (check : availableB u d pool a = true) : Available u bank (restrictRows f (observe a)) := by
  simp only [availableB,List.any_map,Function.comp_def,Bool.or_eq_true,Bool.and_eq_true,beq_iff_eq,List.any_eq_true] at check
  rcases check with ((hz | ho) | ⟨v,hv,he⟩) | ⟨hu,v,hv,he⟩
  · exact Or.inr (Or.inl ⟨false,masked_zero dom hz⟩)
  · exact Or.inr (Or.inl ⟨true,masked_one dom ho⟩)
  · exact masked_eq dom he ▸ supplyB v hv
  · have h := avail_inv hu (masked_eq dom he ▸ supplyB v hv)
    rw [obs_neg] at h
    have e : inv (restrictRows f (inv (observe a))) = restrictRows f (observe a) := by
      funext r
      simp [inv,restrictRows]
    rwa [e] at h

abbrev Choice := Nat × Sig × Sig
def choiceVal (c : Choice) := bin c.1 c.2.1 c.2.2
def allowedB (u : Bool) (d : Nat) := decide (d<2) || (u && decide (d<4))
theorem allowedB_ok {u d} (h : allowedB u d=true) : allowed u d := by
  simpa [allowedB,allowed] using h
def choiceOK (u : Bool) (d : Sig) (pool : List Sig) (c : Choice) :=
  allowedB u c.1 && (availableB u d pool c.2.1 && availableB u d pool c.2.2)

theorem pay_choice {u} {f : Row → Row} {d : Sig} {roots bank pool q}
    (dom : ∀ r, bit (f r) d = true) (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (c : Choice) (valid : choiceOK u d pool c = true) :
    ∃ next, Reach u roots (q+1) next ∧ poolSupply u f next (choiceVal c :: pool) := by
  simp only [choiceOK,Bool.and_eq_true] at valid
  obtain ⟨op,x,y,e,hx,hy,_,_⟩ := comb_prime (allowedB_ok valid.1) (availableB_sound dom hs valid.2.1)
    (availableB_sound dom hs valid.2.2)
  refine ⟨_,Reach.two op hp hx hy,?_⟩
  intro a hm
  rcases List.mem_cons.mp hm with rfl | hm
  · rw [choiceVal,obs_bin,restrict_comb,e]
    exact Or.inl (by simp)
  · exact available_cons _ (hs _ hm)

def makePool (u : Bool) (d : Sig) (pool : List Sig) : List Choice → Option (List Sig)
  | [] => some pool
  | c::cs => if choiceOK u d pool c then makePool u d (choiceVal c::pool) cs else none

theorem makePool_sound {u} {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    {roots bank q pool} (hp : Reach u roots q bank) (hs : poolSupply u f bank pool)
    (cs : List Choice) {result} (ok : makePool u d pool cs = some result) :
    ∃ next, Reach u roots (q+cs.length) next ∧ poolSupply u f next result := by
  induction cs generalizing bank q pool with
  | nil => cases ok; exact ⟨_,hp,hs⟩
  | cons c cs ih =>
    simp only [makePool] at ok
    split at ok
    next h =>
      obtain ⟨next,hr,sh⟩ := pay_choice dom hp hs c h
      obtain ⟨out,hr',sh'⟩ := ih hr sh ok
      exact ⟨out,by simpa [Nat.add_assoc,Nat.add_comm 1] using hr',sh'⟩
    next => contradiction

def isMaskedConstant (d a : Sig) := masked d a == zero || masked d a == d
theorem count_constants {d : Sig} {f : Row → Row} (dom : ∀ r, bit (f r) d = true)
    (ws : List Sig) : ws.countP (isMaskedConstant d) ≤ mass ((ws.map observe).map (restrictRows f)) := by
  classical
  induction ws with
  | nil => simp [mass]
  | cons a ws ih =>
    simp only [List.countP_cons,List.map_cons,mass_cons]
    cases h : isMaskedConstant d a
    · simpa using (Nat.le_add_left _ _ |> ih.trans)
    · have hc : Constant (restrictRows f (observe a)) := by
        have hh : masked d a = zero ∨ masked d a = d := by simpa only [isMaskedConstant,Bool.or_eq_true,beq_iff_eq] using h
        rcases hh with hz | ho
        · exact ⟨false,masked_zero dom hz⟩
        · exact ⟨true,masked_one dom ho⟩
      simpa [cost,hc,Nat.add_comm] using Nat.succ_le_succ ih

def poolCut (u : Bool) (d : Sig) (L k p : Nat) (pool ws : List Sig) :=
  decide (k+p < L+ws.countP (isMaskedConstant d)) && ws.all (availableB u d pool)

theorem poolCut_sound {u raw T d L} (slice : Slice u raw T d L) (cs : List Choice)
    {pool ws cap} (built : makePool u d raw cs = some pool)
    (nd : ws.Nodup) (cut : poolCut u d L cap cs.length pool ws = true) :
    Impossible u T cap ws.toFinset := by
  intro k hk h
  obtain ⟨f,roots,dom,base,nc,lo⟩ := slice
  obtain ⟨bank,hr,hs⟩ := makePool_sound dom (Reach.start (roots:=roots.map observe)) base cs built
  simp only [poolCut,Bool.and_eq_true,decide_eq_true_eq] at cut
  obtain ⟨ineq,all⟩ := cut
  have coveredS : supply u bank ((ws.map observe).map (restrictRows f)) := by
    intro v hv
    obtain ⟨_,hm,rfl⟩ := List.mem_map.mp hv
    obtain ⟨a,ha,rfl⟩ := List.mem_map.mp hm
    exact availableB_sound dom hs (List.all_eq_true.mp all a ha)
  have b := projected_bound f (list_run h ws nd rfl) nc hr coveredS lo
  have massLo := count_constants dom ws
  have hu := ineq
  simp only [Nat.zero_add] at b
  omega



def neighbor (i : Fin 10) : Nat := [1,0,1,2,0,0,1,2,3,4].getD i.val 0
def absentRow (i : Fin 10) : Row := Fin.ofNat 1024 (1 <<< neighbor i)
def presentRow (i : Fin 10) : Row := Fin.ofNat 1024 ((1 <<< i.val) ||| (1 <<< neighbor i))

set_option maxHeartbeats 1000000 in
theorem requiredInputs :
    (∀ i : Fin 10, bit (absentRow i) graph ≠ bit (presentRow i) graph) ∧
    (∀ i j : Fin 10, i ≠ j →
      bit (absentRow i) (inputs.getD j.val zero) =
      bit (presentRow i) (inputs.getD j.val zero)) := by decide +kernel


theorem twoRoots (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = edge) (small : C.size ≤ 19) :
    ∃ (u : Bool) (k : Nat), k ≤ (if u then 18 else 19) ∧ Live u graph k inputs.toFinset := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j,hj⟩
    exact (table_eval C legal C.output r).trans ((congrFun computes (sample r)).trans (edge_table r).symm)
  have len : C.gates.length ≤ 19 := small
  have mode : ∃ u : Bool, (u=false → ∀ g ∈ C.gates, isNot g=false) ∧ C.gates.countP (fun g => !isNot g) ≤ (if u then 18 else 19) := by
    by_cases hn : ∀ g ∈ C.gates, isNot g=false
    · refine ⟨false,fun _ => hn,?_⟩
      have := List.countP_le_length (p:=fun g => !isNot g) (l:=C.gates)
      simp only [Bool.false_eq_true,ite_false]
      omega
    · refine ⟨true,by simp,?_⟩
      push Not at hn
      obtain ⟨g,hg,hx⟩ := hn
      have lt : C.gates.countP (fun g => !isNot g) < C.gates.length := by
        rcases Nat.lt_or_ge (C.gates.countP (fun g => !isNot g)) C.gates.length with h | h
        · exact h
        · have eq := List.countP_eq_length.mp (Nat.le_antisymm List.countP_le_length h) g hg
          simp only [Bool.not_eq_true'] at eq
          exact absurd eq hx
      simp only [ite_true]
      omega
  obtain ⟨u,mono,count⟩ := mode

  have out := get_rep (u:=u) (execute C.gates inputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k,S,hk,run,sub⟩ := extract C.gates inputs legal mono graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : inputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 10, inputs.getD i.val zero = a := by
    rw [←input_list] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = inputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i,rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run inputs (inputs.getD i.val zero) sub (absentRow i) (presentRow i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j,rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨u,k,hk.trans count,eq ▸ run⟩

theorem directSplit
    (m : ∀ k, k ≤ 19 → ¬Live false graph k inputs.toFinset)
    (s : ∀ k, k ≤ 18 → ¬Live true graph k inputs.toFinset) :
    ¬ PEqualNP.MetaComplexity.HasCircuitSize 10 edge 19 := by
  rintro ⟨C,legal,small,computes⟩
  obtain ⟨mode,k,hk,run⟩ := twoRoots C legal (funext computes) small
  cases mode
  · exact m k hk run
  · exact s k hk run


theorem circuit_live (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = edge) (u : Bool)
    (mono : u = false → ∀ g ∈ C.gates, isNot g = false) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live u graph k inputs.toFinset := by
  have goalEq : (execute C.gates inputs).getD C.output zero = graph := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let r : Row := ⟨j, hj⟩
    exact (table_eval C legal C.output r).trans
      ((congrFun computes (sample r)).trans (edge_table r).symm)
  have out := get_rep (u := u) (execute C.gates inputs) C.output
  rw [goalEq] at out
  unfold Repr at out
  have pg : bit 0 graph = false := by decide +kernel
  rw [nrm_id pg] at out
  obtain ⟨k, S, hk, run, sub⟩ := extract C.gates inputs legal mono graph_proper
    (out.resolve_right (fun h => h graph_proper))
  have ns : inputs.all plainWord = true := by decide +kernel
  rw [nrm_map ns] at sub
  have idx (a : Sig) (ha : a ∈ inputs) : ∃ i : Fin 10, inputs.getD i.val zero = a := by
    rw [← input_list] at ha
    exact List.mem_ofFn.mp ha
  have eq : S = inputs.toFinset := by
    ext a
    constructor
    · exact fun h => List.mem_toFinset.mpr (sub a h)
    · intro ha
      obtain ⟨i, rfl⟩ := idx a (List.mem_toFinset.mp ha)
      apply raw_required run inputs (inputs.getD i.val zero) sub (absentRow i) (presentRow i)
        (requiredInputs.1 i)
      intro v hv hn
      obtain ⟨j, rfl⟩ := idx v hv
      apply requiredInputs.2 i j
      rintro rfl
      exact hn rfl
  exact ⟨k, hk, eq ▸ run⟩

theorem circuit_live_signed (C : Circuit) (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = edge) :
    ∃ k, k ≤ C.gates.countP (fun g => !isNot g) ∧ Live true graph k inputs.toFinset :=
  circuit_live C legal computes true (by simp)

end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.LiftSeventeen

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

abbrev input (i : Fin 10) : Live1024.Sig := Live1024.inputs.getD i.val Live1024.zero

def projected (rows : NineSigned.Row → Live1024.Row) (a : Live1024.Sig) :=
  Live1024.restrictRows rows (Live1024.observe a)

lemma input_index (a : Live1024.Sig) (ha : a ∈ Live1024.inputs) :
    ∃ i : Fin 10, input i = a := by
  rw [← Live1024.input_list] at ha
  exact List.mem_ofFn.mp ha

lemma reach_bridge {q : Nat} {bank : List (Live1024.Wire NineSigned.Row)}
    (h : Live1024.Reach true (NineSigned.inputs.map NineSigned.observe) q bank) :
    NineSigned.Reach true (NineSigned.inputs.map NineSigned.observe) q bank := by
  induction h using Live1024.Reach.ind with
  | start => rfl
  | two op h ha hb ih => exact NineSigned.Reach.two op ih ha hb

lemma projected_bin (rows : NineSigned.Row → Live1024.Row) (d : Nat)
    (a b : Live1024.Sig) : projected rows (Live1024.bin d a b) =
      Live1024.comb d (projected rows a) (projected rows b) := by
  unfold projected
  rw [Live1024.obs_bin, Live1024.restrict_comb]

lemma mass_positive {R : Type} {w : Live1024.Wire R} {ws : List (Live1024.Wire R)}
    (hw : w ∈ ws) (hc : Live1024.Constant w) : 1 ≤ Live1024.mass ws := by
  induction ws with
  | nil => simp at hw
  | cons v vs ih =>
    rw [Live1024.mass_cons]
    rcases List.mem_cons.mp hw with rfl | mem
    · simp only [Live1024.cost, if_pos hc]
      omega
    · have bound := ih mem
      omega

lemma projected_tail_lower (rows : NineSigned.Row → Live1024.Row)
    (goal : projected rows Live1024.graph = NineSigned.observe NineSigned.graph)
    (S : Finset Live1024.Sig) (k : Nat) (run : Live1024.Live true Live1024.graph k S)
    (covered : ∀ a ∈ S, Live1024.Available true (NineSigned.inputs.map NineSigned.observe)
      (projected rows a))
    (constant : ∃ a ∈ S, Live1024.Constant (projected rows a)) : 16 ≤ k := by
  have trace := Live1024.list_run run S.toList (Finset.nodup_toList S) (by simp)
  have nc : ¬ Live1024.Constant (Live1024.restrictRows rows (Live1024.observe Live1024.graph)) := by
    change ¬ Live1024.Constant (projected rows Live1024.graph)
    rw [goal]
    exact NineSigned.observe_proper NineSigned.graph_proper
  have supply : Live1024.supply true (NineSigned.inputs.map NineSigned.observe)
      ((S.toList.map Live1024.observe).map (Live1024.restrictRows rows)) := by
    intro v hv
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    exact covered a (Finset.mem_toList.mp ha)
  have prior (q : Nat) (bank : List (Live1024.Wire NineSigned.Row))
      (h : Live1024.Reach true (NineSigned.inputs.map NineSigned.observe) q bank)
      (hv : Live1024.Available true bank
        (Live1024.restrictRows rows (Live1024.observe Live1024.graph))) : 15 ≤ q := by
    change Live1024.Available true bank (projected rows Live1024.graph) at hv
    rw [goal] at hv
    exact NineSigned.nine_reach_lower q bank (reach_bridge h) hv
  have bound := Live1024.projected_bound rows trace nc Live1024.Reach.start supply prior
  obtain ⟨a, ha, hc⟩ := constant
  have mem : projected rows a ∈
      ((S.toList.map Live1024.observe).map (Live1024.restrictRows rows)) :=
    List.mem_map.mpr ⟨Live1024.observe a,
      List.mem_map.mpr ⟨a, Finset.mem_toList.mpr ha, rfl⟩, rfl⟩
  have mass := mass_positive mem hc
  omega

lemma live_lower
    (rows : Fin 10 → NineSigned.Row → Live1024.Row)
    (goal : ∀ i, projected (rows i) Live1024.graph = NineSigned.observe NineSigned.graph)
    (fixed : ∀ i, projected (rows i) (input i) = (fun _ => false))
    (covered : ∀ i j, Live1024.Available true (NineSigned.inputs.map NineSigned.observe)
      (projected (rows i) (input j)))
    (noOr : ∀ a b : Fin 10, a ≠ b → ∃ r s : Live1024.Row,
      (∀ i, i ≠ a → i ≠ b → Live1024.bit r (input i) = Live1024.bit s (input i)) ∧
      Live1024.bit r (Live1024.bin 1 (input a) (input b)) =
        Live1024.bit s (Live1024.bin 1 (input a) (input b)) ∧
      Live1024.bit r Live1024.graph ≠ Live1024.bit s Live1024.graph)
    {k : Nat} (run : Live1024.Live true Live1024.graph k Live1024.inputs.toFinset) : 17 ≤ k := by
  cases k with
  | zero =>
    obtain ⟨eq, _⟩ := run
    have count : Live1024.inputs.toFinset.card = 10 := by decide +kernel
    have h := congrArg Finset.card eq
    rw [count, Finset.card_singleton] at h
    omega
  | succ k =>
    obtain ⟨U, a, b, d, hd, eq, ha, hb, hab, fresh, tail⟩ := run
    have ma : a ∈ Live1024.inputs := List.mem_toFinset.mp (by rw [eq]; simp)
    have mb : b ∈ Live1024.inputs := List.mem_toFinset.mp (by rw [eq]; simp)
    have sub (w : Live1024.Sig) (hw : w ∈ U) : w ∈ Live1024.inputs :=
      List.mem_toFinset.mp (by rw [eq]; simp [hw])
    obtain ⟨i, rfl⟩ := input_index a ma
    obtain ⟨j, rfl⟩ := input_index b mb
    have ij : i ≠ j := by rintro rfl; exact hab rfl
    have finish (p : Fin 10)
        (new : Live1024.Available true (NineSigned.inputs.map NineSigned.observe)
          (projected (rows p) (Live1024.bin d (input i) (input j))))
        (constant : ∃ w ∈ insert (Live1024.bin d (input i) (input j)) U,
          Live1024.Constant (projected (rows p) w)) : 17 ≤ k + 1 := by
      have lower := projected_tail_lower (rows p) (goal p)
        (insert (Live1024.bin d (input i) (input j)) U) k tail (fun w hw => by
          rcases Finset.mem_insert.mp hw with rfl | old
          · exact new
          · obtain ⟨t, rfl⟩ := input_index w (sub w old)
            exact covered p t) constant
      omega
    rcases Live1024.allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
    · have hz : projected (rows i) (Live1024.bin 0 (input i) (input j)) = (fun _ => false) := by
        rw [projected_bin, fixed i]
        funext r
        simp [Live1024.comb, Live1024.combine]
      exact finish i (Or.inr (Or.inl ⟨false, hz⟩))
        ⟨_, Finset.mem_insert_self _ _, ⟨false, hz⟩⟩
    · have retained : input i ∈ U ∨ input j ∈ U := by
        by_contra missing
        push Not at missing
        obtain ⟨r, s, oldSame, newSame, different⟩ := noOr i j ij
        obtain ⟨w, hw, diff⟩ := Live1024.live_row_difference tail different
        rcases Finset.mem_insert.mp hw with rfl | old
        · exact diff newSame
        · obtain ⟨t, rfl⟩ := input_index w (sub w old)
          have hi : t ≠ i := by rintro rfl; exact missing.1 old
          have hj : t ≠ j := by rintro rfl; exact missing.2 old
          exact diff (oldSame t hi hj)
      rcases retained with hi | hj
      · have hz : projected (rows i) (Live1024.bin 1 (input i) (input j)) =
            projected (rows i) (input j) := by
          rw [projected_bin, fixed i]
          funext r
          simp [Live1024.comb, Live1024.combine]
        apply finish i (hz.symm ▸ covered i j)
        exact ⟨input i, Finset.mem_insert_of_mem hi, ⟨false, fixed i⟩⟩
      · have hz : projected (rows j) (Live1024.bin 1 (input i) (input j)) =
            projected (rows j) (input i) := by
          rw [projected_bin, fixed j]
          funext r
          simp [Live1024.comb, Live1024.combine]
        apply finish j (hz.symm ▸ covered j i)
        exact ⟨input j, Finset.mem_insert_of_mem hj, ⟨false, fixed j⟩⟩
    · have hz : projected (rows i) (Live1024.bin 2 (input i) (input j)) = (fun _ => false) := by
        rw [projected_bin, fixed i]
        funext r
        simp [Live1024.comb, Live1024.combine]
      exact finish i (Or.inr (Or.inl ⟨false, hz⟩))
        ⟨_, Finset.mem_insert_self _ _, ⟨false, hz⟩⟩
    · have hz : projected (rows j) (Live1024.bin 3 (input i) (input j)) = (fun _ => false) := by
        rw [projected_bin, fixed j]
        funext r
        simp [Live1024.comb, Live1024.combine, Live1024.inv]
      exact finish j (Or.inr (Or.inl ⟨false, hz⟩))
        ⟨_, Finset.mem_insert_self _ _, ⟨false, hz⟩⟩

end PEqualNP.Outside.L_meta_2373.LiftSeventeen


namespace PEqualNP.Outside.L_meta_2373

def relabel (v : Fin 10) : Fin 10 → Fin 10 :=
  ![![2, 3, 8, 6, 1, 7, 4, 5, 9, 0],
    ![3, 4, 9, 7, 2, 8, 0, 6, 5, 1],
    ![0, 4, 9, 6, 1, 5, 3, 7, 8, 2],
    ![0, 1, 6, 9, 4, 5, 2, 8, 7, 3],
    ![1, 2, 7, 5, 0, 6, 3, 9, 8, 4],
    ![1, 2, 3, 4, 0, 6, 7, 8, 9, 5],
    ![0, 4, 3, 2, 1, 5, 9, 8, 7, 6],
    ![0, 1, 6, 8, 5, 4, 2, 9, 3, 7],
    ![0, 1, 2, 7, 5, 4, 6, 3, 9, 8],
    ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9]] v

lemma relabel_bijective : ∀ v : Fin 10, Function.Bijective (relabel v) := by
  intro v
  fin_cases v <;> decide

lemma relabel_last : ∀ v : Fin 10, relabel v 9 = v := by
  decide

def rowMap (v : Fin 10) (r : Fin 512) : Fin 1024 :=
  Fin.ofNat 1024 (∑ i : Fin 9,
    if r.val.testBit i.val then 2 ^ (relabel v i.castSucc).val else 0)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma rowMap_graph : ∀ (v : Fin 10) (r : Fin 512),
    Live1024.observe Live1024.graph (rowMap v r) = NineSigned.observe NineSigned.graph r := by
  intro v
  fin_cases v <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma rowMap_missing : ∀ (v : Fin 10) (r : Fin 512),
    Live1024.observe (Live1024.inputs.getD v.val Live1024.zero) (rowMap v r) = false := by
  intro v
  fin_cases v <;> decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 50000000 in
lemma rowMap_input : ∀ (v : Fin 10) (j : Fin 9) (r : Fin 512),
    Live1024.observe (Live1024.inputs.getD (relabel v j.castSucc).val Live1024.zero)
      (rowMap v r) = NineSigned.observe (NineSigned.inputs.getD j.val NineSigned.zero) r := by
  intro v j
  fin_cases v <;> fin_cases j <;> decide +kernel


lemma rowMap_available_of
    (missing : ∀ (v : Fin 10) (r : Fin 512),
      Live1024.observe (Live1024.inputs.getD v.val Live1024.zero) (rowMap v r) = false)
    (remaining : ∀ (v : Fin 10) (j : Fin 9) (r : Fin 512),
      Live1024.observe (Live1024.inputs.getD (relabel v j.castSucc).val Live1024.zero)
        (rowMap v r) = NineSigned.observe (NineSigned.inputs.getD j.val NineSigned.zero) r)
    (v i : Fin 10) :
    Live1024.Available true (NineSigned.inputs.map NineSigned.observe)
      (fun r => Live1024.observe (Live1024.inputs.getD i.val Live1024.zero) (rowMap v r)) := by
  by_cases hi : i = v
  · subst i
    exact Or.inr (Or.inl ⟨false, funext (missing v)⟩)
  · obtain ⟨j, hj⟩ := (relabel_bijective v).2 i
    have hne : j ≠ (9 : Fin 10) := by
      intro h
      subst j
      exact hi (hj.symm.trans (relabel_last v))
    have hjlt : j.val < 9 := by
      have hlt := j.isLt
      have hn : j.val ≠ 9 := fun h => hne (Fin.ext h)
      omega
    let k : Fin 9 := ⟨j.val, hjlt⟩
    have hk : relabel v k.castSucc = i := hj
    have heq :
        (fun r => Live1024.observe (Live1024.inputs.getD i.val Live1024.zero) (rowMap v r)) =
          NineSigned.observe (NineSigned.inputs.getD k.val NineSigned.zero) := by
      funext r
      rw [← hk]
      exact remaining v k r
    apply Or.inl
    rw [heq]
    apply List.mem_map.mpr
    refine ⟨NineSigned.inputs.getD k.val NineSigned.zero, ?_, rfl⟩
    have hm : NineSigned.inputs.getD k.val NineSigned.zero ∈
        List.ofFn (fun j : Fin 9 => NineSigned.inputs.getD j.val NineSigned.zero) :=
      List.mem_ofFn.mpr ⟨k, rfl⟩
    rw [NineSigned.input_list] at hm
    exact hm

end PEqualNP.Outside.L_meta_2373

namespace PEqualNP.Outside.L_meta_2373.Live1024

def pairRow (a c : Fin 10) : Row :=
  Fin.ofNat 1024 ((1 <<< a.val) ||| (1 <<< c.val))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma or_separator_rows : ∀ a b : Fin 10, a ≠ b → ∃ c : Fin 10,
    (∀ i : Fin 10, i ≠ a → i ≠ b →
      bit (pairRow a c) (inputs.getD i.val zero) =
        bit (pairRow b c) (inputs.getD i.val zero)) ∧
    bit (pairRow a c) (bin 1 (inputs.getD a.val zero) (inputs.getD b.val zero)) =
      bit (pairRow b c) (bin 1 (inputs.getD a.val zero) (inputs.getD b.val zero)) ∧
    bit (pairRow a c) graph ≠ bit (pairRow b c) graph := by
  decide +kernel

lemma no_or_identification_rows : ∀ a b : Fin 10, a ≠ b →
    ∃ r s : Row,
      (∀ i : Fin 10, i ≠ a → i ≠ b →
        bit r (inputs.getD i.val zero) = bit s (inputs.getD i.val zero)) ∧
      bit r (bin 1 (inputs.getD a.val zero) (inputs.getD b.val zero)) =
        bit s (bin 1 (inputs.getD a.val zero) (inputs.getD b.val zero)) ∧
      bit r graph ≠ bit s graph := by
  intro a b hab
  obtain ⟨c, hc⟩ := or_separator_rows a b hab
  exact ⟨pairRow a c, pairRow b c, hc⟩


end PEqualNP.Outside.L_meta_2373.Live1024

namespace PEqualNP.Outside.L_meta_2373.LiftSeventeen

lemma live_lower_seventeen {k : Nat}
    (run : Live1024.Live true Live1024.graph k Live1024.inputs.toFinset) : 17 ≤ k := by
  apply live_lower rowMap (fun i => funext (rowMap_graph i))
    (fun i => funext (rowMap_missing i))
    (fun i j => rowMap_available_of rowMap_missing rowMap_input i j)
    Live1024.no_or_identification_rows run

theorem circuit_binary_lower (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = Live1024.edge) :
    17 ≤ C.gates.countP (fun g => !Live1024.isNot g) := by
  obtain ⟨k, hk, run⟩ := Live1024.circuit_live_signed C legal computes
  have lower := live_lower_seventeen run
  omega


end PEqualNP.Outside.L_meta_2373.LiftSeventeen

namespace PEqualNP.Outside.L_meta_2373.LiftSeventeen

lemma binary_not_partition (gs : List PEqualNP.CircuitLowerBounds.Gate) :
    gs.countP (fun g => !Live1024.isNot g) + gs.countP Live1024.isNot = gs.length := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    cases h : Live1024.isNot g <;> simp [List.countP_cons, h] at * <;> omega

lemma notCount_eq_countP (C : PEqualNP.CircuitLowerBounds.Circuit) :
    PEqualNP.NotBracket.notCount C = C.gates.countP Live1024.isNot := by
  unfold PEqualNP.NotBracket.notCount
  rw [List.countP_eq_length_filter]
  congr 1
  apply List.filter_congr
  intro g _
  unfold Live1024.isNot
  cases g.op <;> rfl

lemma circuit_not_budget_from_binary (C : PEqualNP.CircuitLowerBounds.Circuit)
    (lower : 17 ≤ C.gates.countP (fun g => !Live1024.isNot g)) :
    17 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  have total := binary_not_partition C.gates
  rw [notCount_eq_countP]
  change 17 + C.gates.countP Live1024.isNot ≤ C.gates.length
  omega

end PEqualNP.Outside.L_meta_2373.LiftSeventeen

namespace PEqualNP.Outside.L_meta_2373.LiftSeventeen

theorem circuit_not_budget (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = Live1024.edge) :
    17 + PEqualNP.NotBracket.notCount C ≤ C.size :=
  circuit_not_budget_from_binary C (circuit_binary_lower C legal computes)

theorem three_not_exclusion (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (small : C.size ≤ 19) (many : 3 ≤ PEqualNP.NotBracket.notCount C) :
    PEqualNP.MetaComplexity.circuitFun 10 C ≠ Live1024.edge := by
  intro computes
  have bound := circuit_not_budget C legal computes
  omega


end PEqualNP.Outside.L_meta_2373.LiftSeventeen

namespace PEqualNP.Outside.L_meta_2373

lemma petersen_not_budget_seventeen (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : ∀ x : Fin 10 → Bool, C.eval (List.ofFn x) = edge x) :
    17 + PEqualNP.NotBracket.notCount C ≤ C.size := by
  apply LiftSeventeen.circuit_not_budget C legal
  funext x
  exact computes x

lemma petersen_three_not_exclusion (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (small : C.size ≤ 19) (many : 3 ≤ PEqualNP.NotBracket.notCount C) :
    ∃ x : Fin 10 → Bool, C.eval (List.ofFn x) ≠ edge x := by
  by_contra! computes
  have bound := petersen_not_budget_seventeen C legal computes
  omega

end PEqualNP.Outside.L_meta_2373

namespace PEqualNP.Outside.L_meta_2373.LiftSeventeen

lemma mass_two {A R : Type} (f : A → Live1024.Wire R) {a b : A} {xs : List A}
    (ha : a ∈ xs) (hb : b ∈ xs) (hne : a ≠ b)
    (ca : Live1024.Constant (f a)) (cb : Live1024.Constant (f b)) :
    2 ≤ Live1024.mass (xs.map f) := by
  induction xs with
  | nil => simp at ha
  | cons x xs ih =>
    rw [List.map_cons, Live1024.mass_cons]
    rcases List.mem_cons.mp ha with rfl | hatail
    · have hb' : b ∈ xs := (List.mem_cons.mp hb).resolve_left (Ne.symm hne)
      have bound : 1 ≤ Live1024.mass (xs.map f) :=
        mass_positive (List.mem_map.mpr ⟨b, hb', rfl⟩) cb
      simp only [Live1024.cost, if_pos ca]
      omega
    · rcases List.mem_cons.mp hb with rfl | hbtail
      · have bound : 1 ≤ Live1024.mass (xs.map f) :=
          mass_positive (List.mem_map.mpr ⟨a, hatail, rfl⟩) ca
        simp only [Live1024.cost, if_pos cb]
        omega
      · have bound := ih hatail hbtail
        omega

lemma projected_tail_lower_two (rows : NineSigned.Row → Live1024.Row)
    (goal : projected rows Live1024.graph = NineSigned.observe NineSigned.graph)
    (S : Finset Live1024.Sig) (k : Nat) (run : Live1024.Live true Live1024.graph k S)
    (covered : ∀ a ∈ S, Live1024.Available true (NineSigned.inputs.map NineSigned.observe)
      (projected rows a))
    (constants : ∃ a ∈ S, ∃ b ∈ S, a ≠ b ∧
      Live1024.Constant (projected rows a) ∧ Live1024.Constant (projected rows b)) : 17 ≤ k := by
  have trace := Live1024.list_run run S.toList (Finset.nodup_toList S) (by simp)
  have nc : ¬ Live1024.Constant (Live1024.restrictRows rows (Live1024.observe Live1024.graph)) := by
    change ¬ Live1024.Constant (projected rows Live1024.graph)
    rw [goal]
    exact NineSigned.observe_proper NineSigned.graph_proper
  have supply : Live1024.supply true (NineSigned.inputs.map NineSigned.observe)
      ((S.toList.map Live1024.observe).map (Live1024.restrictRows rows)) := by
    intro v hv
    obtain ⟨_, hm, rfl⟩ := List.mem_map.mp hv
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    exact covered a (Finset.mem_toList.mp ha)
  have prior (q : Nat) (bank : List (Live1024.Wire NineSigned.Row))
      (h : Live1024.Reach true (NineSigned.inputs.map NineSigned.observe) q bank)
      (hv : Live1024.Available true bank
        (Live1024.restrictRows rows (Live1024.observe Live1024.graph))) : 15 ≤ q := by
    change Live1024.Available true bank (projected rows Live1024.graph) at hv
    rw [goal] at hv
    exact NineSigned.nine_reach_lower q bank (reach_bridge h) hv
  have bound := Live1024.projected_bound rows trace nc Live1024.Reach.start supply prior
  obtain ⟨a, ha, b, hb, hne, ca, cb⟩ := constants
  have mass := mass_two (projected rows) (Finset.mem_toList.mpr ha)
    (Finset.mem_toList.mpr hb) hne ca cb
  have eq : ((S.toList.map Live1024.observe).map (Live1024.restrictRows rows)) =
      S.toList.map (projected rows) := by simp [List.map_map, projected, Function.comp_def]
  rw [eq] at bound
  omega

lemma first_non_or_lower
    (rows : Fin 10 → NineSigned.Row → Live1024.Row)
    (goal : ∀ i, projected (rows i) Live1024.graph = NineSigned.observe NineSigned.graph)
    (fixed : ∀ i, projected (rows i) (input i) = (fun _ => false))
    (covered : ∀ i j, Live1024.Available true (NineSigned.inputs.map NineSigned.observe)
      (projected (rows i) (input j)))
    (i j : Fin 10) (U : Finset Live1024.Sig) (d k : Nat)
    (sub : ∀ w ∈ U, w ∈ Live1024.inputs)
    (hd : Live1024.allowed true d) (nonOr : d ≠ 1)
    (fresh : Live1024.bin d (input i) (input j) ∉ insert (input i) (insert (input j) U))
    (tail : Live1024.Live true Live1024.graph k (insert (Live1024.bin d (input i) (input j)) U))
    (retained : input i ∈ U ∧ input j ∈ U) : 18 ≤ k + 1 := by
  have finish (p : Fin 10) (hp : input p ∈ U)
      (hz : projected (rows p) (Live1024.bin d (input i) (input j)) = (fun _ => false)) :
      18 ≤ k + 1 := by
    have neq : Live1024.bin d (input i) (input j) ≠ input p := by
      intro heq
      exact fresh (heq ▸ Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hp))
    have lower := projected_tail_lower_two (rows p) (goal p)
      (insert (Live1024.bin d (input i) (input j)) U) k tail
      (fun w hw => by
        rcases Finset.mem_insert.mp hw with rfl | old
        · exact Or.inr (Or.inl ⟨false, hz⟩)
        · obtain ⟨t, rfl⟩ := input_index w (sub w old)
          exact covered p t)
      ⟨Live1024.bin d (input i) (input j), Finset.mem_insert_self _ _,
        input p, Finset.mem_insert_of_mem hp, neq, ⟨false, hz⟩, ⟨false, fixed p⟩⟩
    omega
  rcases Live1024.allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · apply finish i retained.1
    rw [projected_bin, fixed i]
    funext r
    simp [Live1024.comb, Live1024.combine]
  · exact False.elim (nonOr rfl)
  · apply finish i retained.1
    rw [projected_bin, fixed i]
    funext r
    simp [Live1024.comb, Live1024.combine]
  · apply finish j retained.2
    rw [projected_bin, fixed j]
    funext r
    simp [Live1024.comb, Live1024.combine, Live1024.inv]

end PEqualNP.Outside.L_meta_2373.LiftSeventeen

namespace PEqualNP.Outside.L_meta_2373

def pairInput (a c : Fin 10) (i : Fin 10) : Bool := decide (i = a ∨ i = c)


def singleInput (c i : Fin 10) : Bool := decide (i = c)

def tripleInput (a b c i : Fin 10) : Bool := decide (i = a ∨ i = b ∨ i = c)

lemma singleton_no_edge : ∀ c : Fin 10, edge (singleInput c) = false := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma zero_separator : ∀ a b : Fin 10, a ≠ b → ∃ c : Fin 10,
    c ≠ a ∧ c ≠ b ∧ edge (pairInput a c) = true := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma one_separator : ∀ a b : Fin 10, a ≠ b → ∃ c : Fin 10,
    c ≠ a ∧ edge (pairInput b c) = false ∧ edge (tripleInput a b c) = true := by
  decide +kernel

lemma conditional_influence (a b : Fin 10) (hab : a ≠ b) (t : Bool) :
    ∃ x y : Fin 10 → Bool,
      (∀ i, i ≠ a → x i = y i) ∧ x b = t ∧ y b = t ∧
      x a = false ∧ y a = true ∧ edge x ≠ edge y := by
  cases t
  · obtain ⟨c, hca, hcb, he⟩ := zero_separator a b hab
    refine ⟨singleInput c, pairInput a c, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hia
      simp [singleInput, pairInput, hia]
    · simp [singleInput, Ne.symm hcb]
    · simp [pairInput, Ne.symm hab, Ne.symm hcb]
    · simp [singleInput, Ne.symm hca]
    · simp [pairInput]
    · rw [singleton_no_edge, he]
      decide
  · obtain ⟨c, hca, he0, he1⟩ := one_separator a b hab
    refine ⟨pairInput b c, tripleInput a b c, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hia
      simp [pairInput, tripleInput, hia]
    · simp [pairInput]
    · simp [tripleInput]
    · simp [pairInput, hab, Ne.symm hca]
    · simp [tripleInput]
    · rw [he0, he1]
      decide

def boolBin (d : Nat) (a b : Bool) : Bool :=
  if d = 0 then a && b else if d = 1 then a || b else
    if d = 2 then a && !b else !a && b

lemma no_binary_identification_left (d : Nat) (hd : d < 4) (a b : Fin 10)
    (hab : a ≠ b) : ∃ x y : Fin 10 → Bool,
      (∀ i, i ≠ a → x i = y i) ∧
      boolBin d (x a) (x b) = boolBin d (y a) (y b) ∧ edge x ≠ edge y := by
  obtain ⟨x, y, same, xb, yb, xa, ya, different⟩ :=
    conditional_influence a b hab (decide (d = 1 ∨ d = 2))
  refine ⟨x, y, same, ?_, different⟩
  have hcases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;> simp_all [boolBin]



namespace Live1024

def singleRow (c : Fin 10) : Row := Fin.ofNat 1024 (1 <<< c.val)

def tripleRow (a b c : Fin 10) : Row :=
  Fin.ofNat 1024 ((1 <<< a.val) ||| (1 <<< b.val) ||| (1 <<< c.val))

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma singleRow_input : ∀ c i : Fin 10,
    bit (singleRow c) (inputs.getD i.val zero) = singleInput c i := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma pairRow_input : ∀ a c i : Fin 10,
    bit (pairRow a c) (inputs.getD i.val zero) = pairInput a c i := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tripleRow_input : ∀ a b c i : Fin 10,
    bit (tripleRow a b c) (inputs.getD i.val zero) = tripleInput a b c i := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma singleRow_graph : ∀ c : Fin 10,
    bit (singleRow c) graph = PEqualNP.Outside.L_meta_2373.edge (singleInput c) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma pairRow_graph : ∀ a c : Fin 10,
    bit (pairRow a c) graph = PEqualNP.Outside.L_meta_2373.edge (pairInput a c) := by
  decide +kernel

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma tripleRow_graph : ∀ a b c : Fin 10,
    bit (tripleRow a b c) graph = PEqualNP.Outside.L_meta_2373.edge (tripleInput a b c) := by
  decide +kernel

lemma conditional_influence_rows (a b : Fin 10) (hab : a ≠ b) (t : Bool) :
    ∃ r s : Row,
      (∀ i : Fin 10, i ≠ a →
        bit r (inputs.getD i.val zero) = bit s (inputs.getD i.val zero)) ∧
      bit r (inputs.getD b.val zero) = t ∧ bit s (inputs.getD b.val zero) = t ∧
      bit r graph ≠ bit s graph := by
  cases t
  · obtain ⟨c, hca, hcb, he⟩ := zero_separator a b hab
    refine ⟨singleRow c, pairRow a c, ?_, ?_, ?_, ?_⟩
    · intro i hia
      rw [singleRow_input, pairRow_input]
      simp [singleInput, pairInput, hia]
    · rw [singleRow_input]
      simp [singleInput, Ne.symm hcb]
    · rw [pairRow_input]
      simp [pairInput, Ne.symm hab, Ne.symm hcb]
    · rw [singleRow_graph, pairRow_graph, singleton_no_edge, he]
      decide
  · obtain ⟨c, hca, he0, he1⟩ := one_separator a b hab
    refine ⟨pairRow b c, tripleRow a b c, ?_, ?_, ?_, ?_⟩
    · intro i hia
      rw [pairRow_input, tripleRow_input]
      simp [pairInput, tripleInput, hia]
    · rw [pairRow_input]
      simp [pairInput]
    · rw [tripleRow_input]
      simp [tripleInput]
    · rw [pairRow_graph, tripleRow_graph, he0, he1]
      decide

lemma bit_bin_eq_boolBin (r : Row) (d : Nat) (a b : Sig) :
    bit r (bin d a b) = boolBin d (bit r a) (bit r b) := by
  unfold bin boolBin
  split_ifs <;> simp [bit, r.isLt]

lemma no_binary_identification_left_rows (d : Nat) (hd : d < 4) (a b : Fin 10)
    (hab : a ≠ b) : ∃ r s : Row,
      (∀ i : Fin 10, i ≠ a →
        bit r (inputs.getD i.val zero) = bit s (inputs.getD i.val zero)) ∧
      bit r (bin d (inputs.getD a.val zero) (inputs.getD b.val zero)) =
        bit s (bin d (inputs.getD a.val zero) (inputs.getD b.val zero)) ∧
      bit r graph ≠ bit s graph := by
  obtain ⟨r, s, same, xb, yb, different⟩ :=
    conditional_influence_rows a b hab (decide (d = 1 ∨ d = 2))
  refine ⟨r, s, same, ?_, different⟩
  rw [bit_bin_eq_boolBin, bit_bin_eq_boolBin]
  have hcases : d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 := by omega
  rcases hcases with rfl | rfl | rfl | rfl <;> simp_all [boolBin]



abbrev inputColumn (i : Fin 10) : Sig := inputs.getD i.val zero

lemma first_binary_operands_retained (a b : Fin 10) (hab : a ≠ b)
    (U : Finset Sig) (d k : Nat)
    (pool : inputs.toFinset = insert (inputColumn a) (insert (inputColumn b) U))
    (legal : allowed true d)
    (tail : Live true graph k (insert (bin d (inputColumn a) (inputColumn b)) U)) :
    inputColumn a ∈ U ∧ inputColumn b ∈ U := by
  have sub (w : Sig) (hw : w ∈ U) : w ∈ inputs :=
    List.mem_toFinset.mp (by rw [pool]; simp [hw])
  have index (w : Sig) (hw : w ∈ U) : ∃ i : Fin 10, inputColumn i = w := by
    have hi := sub w hw
    rw [← input_list] at hi
    exact List.mem_ofFn.mp hi
  have retain (p q : Fin 10) (hpq : p ≠ q) (e : Nat) (he : e < 4)
      (run : Live true graph k (insert (bin e (inputColumn p) (inputColumn q)) U)) :
      inputColumn p ∈ U := by
    by_contra missing
    obtain ⟨r, s, oldSame, newSame, different⟩ :=
      no_binary_identification_left_rows e he p q hpq
    obtain ⟨w, hw, diff⟩ := live_row_difference run different
    rcases Finset.mem_insert.mp hw with rfl | old
    · exact diff newSame
    · obtain ⟨i, rfl⟩ := index w old
      have hne : i ≠ p := by
        rintro rfl
        exact missing old
      exact diff (oldSame i hne)
  have four : d < 4 := by
    rcases legal with h | ⟨_, h⟩ <;> omega
  have flipped : flipOp d < 4 := by
    rcases (flip_flip legal).1 with h | ⟨_, h⟩ <;> omega
  refine ⟨retain a b hab d four tail, ?_⟩
  apply retain b a hab.symm (flipOp d) flipped
  rw [← bin_flip legal (inputColumn a) (inputColumn b)]
  exact tail

end Live1024

end PEqualNP.Outside.L_meta_2373

namespace PEqualNP.Outside.L_meta_2373.LiftSeventeen

lemma first_non_or_lower_eighteen
    (i j : Fin 10) (U : Finset Live1024.Sig) (d k : Nat) (ij : i ≠ j)
    (pool : Live1024.inputs.toFinset = insert (input i) (insert (input j) U))
    (hd : Live1024.allowed true d) (nonOr : d ≠ 1)
    (fresh : Live1024.bin d (input i) (input j) ∉ insert (input i) (insert (input j) U))
    (tail : Live1024.Live true Live1024.graph k (insert (Live1024.bin d (input i) (input j)) U)) :
    18 ≤ k + 1 := by
  apply first_non_or_lower rowMap (fun i => funext (rowMap_graph i))
    (fun i => funext (rowMap_missing i))
    (fun i j => rowMap_available_of rowMap_missing rowMap_input i j) i j U d k
    (fun w hw => List.mem_toFinset.mp (by rw [pool]; simp [hw])) hd nonOr fresh tail
  exact Live1024.first_binary_operands_retained i j ij U d k pool hd tail

lemma short_live_starts_or {n : Nat}
    (run : Live1024.Live true Live1024.graph n Live1024.inputs.toFinset) (small : n ≤ 17) :
    ∃ (k : Nat) (U : Finset Live1024.Sig) (i j : Fin 10),
      n = k + 1 ∧ i ≠ j ∧
      Live1024.inputs.toFinset = insert (input i) (insert (input j) U) ∧
      input i ∈ U ∧ input j ∈ U ∧
      Live1024.bin 1 (input i) (input j) ∉ insert (input i) (insert (input j) U) ∧
      Live1024.Live true Live1024.graph k (insert (Live1024.bin 1 (input i) (input j)) U) := by
  cases n with
  | zero =>
    have lower := live_lower_seventeen run
    omega
  | succ k =>
    obtain ⟨U, a, b, d, hd, pool, ha, hb, hab, fresh, tail⟩ := run
    have ma : a ∈ Live1024.inputs := List.mem_toFinset.mp (by rw [pool]; simp)
    have mb : b ∈ Live1024.inputs := List.mem_toFinset.mp (by rw [pool]; simp)
    obtain ⟨i, rfl⟩ := input_index a ma
    obtain ⟨j, rfl⟩ := input_index b mb
    have ij : i ≠ j := by rintro rfl; exact hab rfl
    have op : d = 1 := by
      by_contra hn
      have bound := first_non_or_lower_eighteen i j U d k ij pool hd hn fresh tail
      omega
    subst d
    have retained := Live1024.first_binary_operands_retained i j ij U 1 k pool hd tail
    exact ⟨k, U, i, j, rfl, ij, pool, retained.1, retained.2, fresh, tail⟩

end PEqualNP.Outside.L_meta_2373.LiftSeventeen

namespace PEqualNP.Outside.L_meta_2373.LiftSeventeen

lemma two_not_starts_or (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = Live1024.edge)
    (small : C.size ≤ 19) (many : 2 ≤ PEqualNP.NotBracket.notCount C) :
    ∃ (U : Finset Live1024.Sig) (i j : Fin 10), i ≠ j ∧
      Live1024.inputs.toFinset = insert (input i) (insert (input j) U) ∧
      input i ∈ U ∧ input j ∈ U ∧
      Live1024.bin 1 (input i) (input j) ∉ insert (input i) (insert (input j) U) ∧
      Live1024.Live true Live1024.graph 16 (insert (Live1024.bin 1 (input i) (input j)) U) := by
  obtain ⟨k, hk, run⟩ := Live1024.circuit_live_signed C legal computes
  have lower := live_lower_seventeen run
  have total := binary_not_partition C.gates
  rw [notCount_eq_countP] at many
  change C.gates.length ≤ 19 at small
  have bound : k ≤ 17 := by omega
  obtain ⟨l, U, i, j, kl, ij, pool, hi, hj, fresh, tail⟩ := short_live_starts_or run bound
  have eq : l = 16 := by omega
  exact ⟨U, i, j, ij, pool, hi, hj, fresh, eq ▸ tail⟩

end PEqualNP.Outside.L_meta_2373.LiftSeventeen

namespace PEqualNP.Outside.L_meta_2373.LiftSeventeen

lemma signed_seventeen_or_roots
    (run : Live1024.Live true Live1024.graph 17 Live1024.inputs.toFinset) :
    ∃ i j : Fin 10, i ≠ j ∧
      Live1024.Live true Live1024.graph 16
        (insert (Live1024.bin 1 (input i) (input j)) Live1024.inputs.toFinset) := by
  obtain ⟨k, U, i, j, hk, ij, pool, hi, hj, fresh, tail⟩ := short_live_starts_or run (by omega)
  have keq : k = 16 := by omega
  have ueq : U = Live1024.inputs.toFinset := by
    rw [pool, Finset.insert_eq_of_mem hj, Finset.insert_eq_of_mem hi]
  exact ⟨i, j, ij, keq ▸ ueq ▸ tail⟩

lemma two_not_or_roots (C : PEqualNP.CircuitLowerBounds.Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (computes : PEqualNP.MetaComplexity.circuitFun 10 C = Live1024.edge)
    (small : C.size ≤ 19) (many : 2 ≤ PEqualNP.NotBracket.notCount C) :
    ∃ i j : Fin 10, i ≠ j ∧
      Live1024.Live true Live1024.graph 16
        (insert (Live1024.bin 1 (input i) (input j)) Live1024.inputs.toFinset) := by
  obtain ⟨U, i, j, ij, pool, hi, hj, fresh, tail⟩ := two_not_starts_or C legal computes small many
  have ueq : U = Live1024.inputs.toFinset := by
    rw [pool, Finset.insert_eq_of_mem hj, Finset.insert_eq_of_mem hi]
  exact ⟨i, j, ij, ueq ▸ tail⟩

end PEqualNP.Outside.L_meta_2373.LiftSeventeen


open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
namespace PEqualNP.Outside.L_meta_2373

def glued (g : Gate) (C : Circuit) (u v : Nat) : Circuit :=
  ⟨g :: (C.gates ++ [⟨GateOp.or, [u, v]⟩]), 11 + C.size⟩

lemma wires_length (C : Circuit) (xs : List Bool) :
    (C.wires xs).length = xs.length + C.size := by
  rcases C with ⟨gs, out⟩
  induction gs generalizing xs with
  | nil => simp [Circuit.wires, Circuit.size]
  | cons g gs ih =>
    change (Circuit.wires ⟨gs, out⟩
      (xs ++ [g.op.eval (g.inputs.map fun i => xs.getD i false)])).length = _
    rw [ih]
    simp [Circuit.size]
    omega

lemma glued_fan (g : Gate) (C : Circuit) (u v : Nat)
    (hg : FanInTwo ⟨[g], 0⟩) (hC : FanInTwo C) : FanInTwo (glued g C u v) := by
  intro gate hgate
  have hfirst := hg g (by simp)
  simp only [glued, List.mem_cons, List.mem_append, List.not_mem_nil, or_false] at hgate
  rcases hgate with rfl | hgate | rfl
  · exact hfirst
  · exact hC gate hgate
  · simp

lemma glued_size (g : Gate) (C : Circuit) (u v : Nat) :
    (glued g C u v).size = C.size + 2 := by
  simp [glued, Circuit.size]

lemma glued_eval (g : Gate) (C : Circuit) (u v : Nat) (x : Fin 10 → Bool) :
    (glued g C u v).eval (List.ofFn x) =
      ((C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false ||
        (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false) := by
  let w := C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))
  have hw : w.length = 11 + C.size := by
    simp [w, wires_length, Circuit.size]
  simp only [glued, Circuit.eval, Circuit.wires, List.foldl_cons, List.foldl_append,
    List.foldl_nil, List.map_cons, List.map_nil, GateOp.eval, List.any_cons,
    List.any_nil, id_eq, Bool.or_false]
  change (w ++ [(w.getD u false || w.getD v false)]).getD (11 + C.size) false = _
  rw [← hw]
  simp [w, Circuit.wires, GateOp.eval]

lemma cover_gives_circuit (g : Gate) (C : Circuit) (u v : Nat)
    (hg : FanInTwo ⟨[g], 0⟩) (hC : FanInTwo C) (hs : C.size ≤ 17)
    (cover : ∀ x : Fin 10 → Bool, edge x =
      ((C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false ||
       (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false)) :
    HasCircuitSize 10 edge 19 := by
  refine ⟨glued g C u v, glued_fan g C u v hg hC, ?_, ?_⟩
  · rw [glued_size]
    omega
  · intro x
    rw [glued_eval, ← cover x]

lemma missed_of_no_circuit (g : Gate) (C : Circuit) (u v : Nat)
    (hg : FanInTwo ⟨[g], 0⟩) (hC : FanInTwo C) (hs : C.size ≤ 17)
    (lower : ¬ HasCircuitSize 10 edge 19)
    (sound : ∀ x : Fin 10 → Bool, edge x = false →
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false = false ∧
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false = false) :
    ∃ x : Fin 10 → Bool, edge x = true ∧
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false = false ∧
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false = false := by
  classical
  by_contra missing
  apply lower
  apply cover_gives_circuit g C u v hg hC hs
  intro x
  have hx := sound x
  have hm : ¬ (edge x = true ∧
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false = false ∧
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false = false) :=
    fun h => missing ⟨x, h⟩
  cases he : edge x <;>
    cases hu : (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false <;>
    cases hv : (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false <;>
    simp_all

lemma missed_or_few_nots (g : Gate) (C : Circuit) (u v : Nat)
    (hg : FanInTwo ⟨[g], 0⟩) (hC : FanInTwo C) (hs : C.size ≤ 17)
    (sound : ∀ x : Fin 10 → Bool, edge x = false →
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false = false ∧
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false = false) :
    (∃ x : Fin 10 → Bool, edge x = true ∧
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false = false ∧
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false = false) ∨
      PEqualNP.NotBracket.notCount (glued g C u v) ≤ 2 := by
  classical
  by_cases missing : ∃ x : Fin 10 → Bool, edge x = true ∧
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false = false ∧
      (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false = false
  · exact Or.inl missing
  apply Or.inr
  have cover : ∀ x : Fin 10 → Bool, edge x =
      ((C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false ||
       (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false) := by
    intro x
    have hx := sound x
    have hm : ¬ (edge x = true ∧
        (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false = false ∧
        (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false = false) :=
      fun h => missing ⟨x, h⟩
    cases he : edge x <;>
      cases hu : (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD u false <;>
      cases hv : (C.wires ((⟨[g], 0⟩ : Circuit).wires (List.ofFn x))).getD v false <;>
      simp_all
  have bound := petersen_not_budget_seventeen (glued g C u v)
    (glued_fan g C u v hg hC) (by
      intro x
      rw [glued_eval, ← cover x])
  have size := glued_size g C u v
  omega

end PEqualNP.Outside.L_meta_2373
