import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_2592_aux.SignedFloor
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

lemma from_constant_comb {R u} {bank : List (Wire R)} {d a b}
    (hd : allowed u d) (hc : Constant a ∨ Constant b)
    (ha : Available u bank a) (hb : Available u bank b) :
    Available u bank (comb d a b) := by
  rcases allowed_four hd with rfl | rfl | ⟨hu, rfl⟩ | ⟨hu, rfl⟩
  · exact from_constant false hc ha hb
  · exact from_constant true hc ha hb
  · exact from_constant false (hc.imp id inv_constant) ha (avail_inv hu hb)
  · exact from_constant false (hc.imp inv_constant id) (avail_inv hu ha) hb

lemma mass_retained_constant {R} (z a b : Wire R) (rest : List (Wire R))
    (ka kb : Bool) (hc : (Constant a ∧ ka = true) ∨ (Constant b ∧ kb = true)) :
    1 ≤ mass (z :: kept ka a (kept kb b rest)) := by
  classical
  rcases hc with ⟨ha, rfl⟩ | ⟨hb, rfl⟩
  · simp [kept, mass_cons, cost, ha]
    omega
  · have hk := mass_kept a (kept true b rest) ka
    simp only [kept, ite_true, mass_cons] at hk ⊢
    have hcost : cost b = 1 := by simp [cost, hb]
    omega

lemma projected_bound_retained {R S : Type} {u} (rows : S → R)
    {goal : Wire R} {s d ka kb a b rest} (hd : allowed u d)
    (tail : Run u goal s (comb d a b :: kept ka a (kept kb b rest)))
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank)
    (hs : supply u bank ((a :: b :: rest).map (restrictRows rows)))
    (hc : (Constant (restrictRows rows a) ∧ ka = true) ∨
      (Constant (restrictRows rows b) ∧ kb = true))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + 2 ≤ p + (s + 1) := by
  have hca : Constant (restrictRows rows a) ∨ Constant (restrictRows rows b) :=
    hc.elim (fun h => Or.inl h.1) (fun h => Or.inr h.1)
  have havA := hs (restrictRows rows a) (by simp)
  have havB := hs (restrictRows rows b) (by simp)
  have havG := from_constant_comb hd hca havA havB
  have hsTail : supply u bank
      ((comb d a b :: kept ka a (kept kb b rest)).map (restrictRows rows)) := by
    simp only [List.map_cons, restrict_kept, restrict_comb]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact havG
    · rcases mem_kept hv with rfl | hv
      · exact havA
      · rcases mem_kept hv with rfl | hv
        · exact havB
        · exact hs v (by simp [hv])
  have bound := projected_bound rows tail nc hp hsTail hl
  have charged : 1 ≤ mass
      ((comb d a b :: kept ka a (kept kb b rest)).map (restrictRows rows)) := by
    simp only [List.map_cons, restrict_kept, restrict_comb]
    exact mass_retained_constant _ _ _ _ _ _ hc
  omega



open PEqualNP.CircuitLowerBounds

def isNot (g : Gate) : Bool := match g.op with
  | .not => true
  | _ => false

def wireRead {R} (ws : List (Wire R)) (i : Nat) : Wire R := ws.getD i (fun _ => false)

def wireGate {R} (ws : List (Wire R)) (g : Gate) : Wire R :=
  fun r => g.op.eval (g.inputs.map (fun i => wireRead ws i r))

def wireExecute {R} (gs : List Gate) (ws : List (Wire R)) : List (Wire R) :=
  gs.foldl (fun ws g => ws ++ [wireGate ws g]) ws

def binaryReads (j : Nat) (g : Gate) : Bool := !isNot g && g.inputs.contains j

lemma wireRead_available {R} {bank ws : List (Wire R)} (hs : supply true bank ws) (i : Nat) :
    Available true bank (wireRead ws i) := by
  unfold wireRead
  rw [List.getD_eq_getElem?_getD]
  cases h : ws[i]? with
  | none => exact Or.inr (Or.inl ⟨false, rfl⟩)
  | some a => exact hs a (List.mem_of_getElem? h)

lemma wireGate_two {R} (ws : List (Wire R)) (i j : Nat) (op : Bool) :
    wireGate ws ⟨if op then .or else .and, [i, j]⟩ =
      combine op (wireRead ws i) (wireRead ws j) := by
  funext r
  cases op <;> simp [wireGate, GateOp.eval, combine]

lemma wireGate_one {R} (ws : List (Wire R)) (i : Nat) (op : Bool) :
    wireGate ws ⟨if op then .or else .and, [i]⟩ = wireRead ws i := by
  funext r
  cases op <;> simp [wireGate, GateOp.eval]

lemma wireGate_not {R} (ws : List (Wire R)) (is : List Nat) :
    wireGate ws ⟨.not, is⟩ = inv (wireRead ws (is.headD ws.length)) := by
  cases is with
  | nil =>
    funext r
    simp [wireGate, GateOp.eval, inv, wireRead]
  | cons i is => rfl

lemma wireGate_paid {R} {roots bank ws : List (Wire R)} {p j} (g : Gate)
    (legal : g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hp : Reach true roots p bank) (hs : supply true bank ws)
    (hc : Constant (wireRead ws j)) :
    ∃ q next, Reach true roots q next ∧ Available true next (wireGate ws g) ∧
      (∀ v, Available true bank v → Available true next v) ∧
      q + (if binaryReads j g then 1 else 0) ≤ p + (if isNot g then 0 else 1) := by
  classical
  obtain ⟨op, is⟩ := g
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at legal
  have bin (op : Bool) :
      ∃ q next, Reach true roots q next ∧
        Available true next (wireGate ws ⟨if op then .or else .and, is⟩) ∧
        (∀ v, Available true bank v → Available true next v) ∧
        q + (if is.contains j then 1 else 0) ≤ p + 1 := by
    cases is with
    | nil =>
      refine ⟨p, bank, hp, Or.inr (Or.inl ?_), fun _ h => h, by simp⟩
      cases op
      · exact ⟨true, rfl⟩
      · exact ⟨false, rfl⟩
    | cons a is =>
      cases is with
      | nil =>
        refine ⟨p, bank, hp, ?_, fun _ h => h, ?_⟩
        · rw [wireGate_one]
          exact wireRead_available hs a
        · split <;> omega
      | cons b is =>
        have hn : is = [] := by
          have hlen := legal.2
          change (a :: b :: is).length ≤ 2 at hlen
          simp only [List.length_cons] at hlen
          exact List.eq_nil_of_length_eq_zero (by omega)
        subst is
        have ha := wireRead_available hs a
        have hb := wireRead_available hs b
        by_cases hit : j ∈ [a, b]
        · have hconst : Constant (wireRead ws a) ∨ Constant (wireRead ws b) := by
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hit
            rcases hit with rfl | rfl
            · exact Or.inl hc
            · exact Or.inr hc
          refine ⟨p, bank, hp, ?_, fun _ h => h, ?_⟩
          · rw [wireGate_two]
            exact from_constant op hconst ha hb
          · simp [hit]
        · refine ⟨p + 1, combine op (wireRead ws a) (wireRead ws b) :: bank,
            Reach.two op hp ha hb, ?_, fun _ h => available_cons _ h, ?_⟩
          · rw [wireGate_two]
            exact Or.inl (by simp)
          · simp [hit]
  rcases legal.1 with rfl | rfl | rfl
  · simpa [isNot, binaryReads] using bin false
  · simpa [isNot, binaryReads] using bin true
  · refine ⟨p, bank, hp, ?_, fun _ h => h, ?_⟩
    · rw [wireGate_not]
      exact avail_inv rfl (wireRead_available hs _)
    · simp [isNot, binaryReads]

lemma execute_read_count {R} {roots bank ws : List (Wire R)} {p j} (gs : List Gate)
    (legal : ∀ g ∈ gs, g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧
      g.inputs.length ≤ 2)
    (hp : Reach true roots p bank) (hs : supply true bank ws)
    (hj : j < ws.length) (hc : Constant (wireRead ws j)) :
    ∃ q next, Reach true roots q next ∧ supply true next (wireExecute gs ws) ∧
      q + gs.countP (binaryReads j) ≤ p + gs.countP (fun g => !isNot g) := by
  induction gs generalizing p bank ws with
  | nil => exact ⟨p, bank, hp, hs, by simp⟩
  | cons g gs ih =>
    obtain ⟨r, mid, hr, hg, inc, hbound⟩ := wireGate_paid g (legal g (by simp)) hp hs hc
    have hsNext : supply true mid (ws ++ [wireGate ws g]) := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact inc v (hs v hv)
      · simpa using List.mem_singleton.mp hv ▸ hg
    have hcNext : Constant (wireRead (ws ++ [wireGate ws g]) j) := by
      unfold wireRead
      rw [List.getD_append _ _ _ _ hj]
      exact hc
    obtain ⟨q, next, hq, hnext, htail⟩ := ih
      (fun h hh => legal h (by simp [hh])) hr hsNext (by simp; omega) hcNext
    refine ⟨q, next, hq, hnext, ?_⟩
    simp only [List.countP_cons] at htail ⊢
    cases hn : isNot g <;> cases hb : binaryReads j g <;> simp [hn, hb] at hbound ⊢ <;> omega

lemma wireRead_values {R} (ws : List (Wire R)) (r : R) (i : Nat) :
    wireRead ws i r = (ws.map (fun w => w r)).getD i false := by
  simp only [wireRead, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases ws[i]? <;> rfl

lemma wireGate_values {R} (ws : List (Wire R)) (r : R) (g : Gate) :
    wireGate ws g r = g.op.eval (g.inputs.map (fun i =>
      (ws.map (fun w => w r)).getD i false)) := by
  simp only [wireGate, wireRead_values]

lemma wireExecute_values {R} (gs : List Gate) (ws : List (Wire R)) (r : R) :
    (wireExecute gs ws).map (fun w => w r) =
      gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))])
        (ws.map (fun w => w r)) := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih =>
    rw [wireExecute, List.foldl_cons]
    change (wireExecute gs (ws ++ [wireGate ws g])).map (fun w => w r) = _
    rw [ih]
    simp only [List.map_append, List.map_cons, List.map_nil, wireGate_values, List.foldl_cons]

lemma circuit_read_lower {R} {roots bank ws : List (Wire R)} {p j L} (C : Circuit)
    (legal : PEqualNP.MetaComplexity.FanInTwo C)
    (hp : Reach true roots p bank) (hs : supply true bank ws)
    (hj : j < ws.length) (hc : Constant (wireRead ws j))
    {goal : Wire R} (computes : ∀ r, C.eval (ws.map (fun w => w r)) = goal r)
    (hl : ∀ q bs, Reach true roots q bs → Available true bs goal → L ≤ q) :
    L + C.gates.countP (binaryReads j) ≤ p + C.gates.countP (fun g => !isNot g) := by
  obtain ⟨q, next, hq, hsNext, hbound⟩ := execute_read_count C.gates legal hp hs hj hc
  have hread := wireRead_available hsNext C.output
  have he : wireRead (wireExecute C.gates ws) C.output = goal := by
    funext r
    rw [wireRead_values, wireExecute_values]
    exact computes r
  rw [he] at hread
  have hlow := hl q next hq hread
  omega


end PEqualNP.Outside.L_meta_2592_aux.SignedFloor
