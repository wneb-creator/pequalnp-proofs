import PEqualNP.Defs
namespace PEqualNP.Outside.L_meta_2592
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
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


namespace MonoContraction

lemma mixed_collapse {R : Type} [Preorder R] [OrderTop R] (a b : Wire R)
    (hb : Monotone b) (hm : Monotone (combine false a (inv b))) :
    b = (fun _ => false) ∨ combine false a (inv b) = (fun _ => false) := by
  cases htop : b ⊤ with
  | false =>
    apply Or.inl
    funext x
    apply Bool.eq_false_of_le_false
    simpa only [htop] using hb (show x ≤ ⊤ from le_top)
  | true =>
    apply Or.inr
    funext x
    apply Bool.eq_false_of_le_false
    simpa [combine, inv, htop] using hm (show x ≤ ⊤ from le_top)

lemma cost_le_one {R} (a : Wire R) : cost a ≤ 1 := by
  classical
  unfold cost
  split <;> omega

lemma extend_mixed {R : Type} [Preorder R] [OrderTop R]
    (roots : List (Wire R)) {p bank} (hp : Reach false roots p bank)
    {a b : Wire R} (ha : Available false bank a) (hb : Available false bank b)
    (mb : Monotone b) (mz : Monotone (combine false a (inv b))) :
    ∃ q next, Reach false roots q next ∧ Available false next (combine false a (inv b)) ∧
      (∀ v, Available false bank v → Available false next v) ∧
      q + cost a + cost b ≤ p + 1 + cost (combine false a (inv b)) := by
  classical
  rcases mixed_collapse a b mb mz with bz | zz
  · have same : combine false a (inv b) = a := by
      rw [bz]
      funext x
      simp [combine, inv]
    have cb : Constant b := ⟨false, bz⟩
    refine ⟨p, bank, hp, same.symm ▸ ha, fun _ h => h, ?_⟩
    rw [same]
    simp only [cost, if_pos cb]
    omega
  · have cz : Constant (combine false a (inv b)) := ⟨false, zz⟩
    refine ⟨p, bank, hp, Or.inr (Or.inl cz), fun _ h => h, ?_⟩
    have ca := cost_le_one a
    have cb := cost_le_one b
    rw [show cost (combine false a (inv b)) = 1 by simp only [cost, if_pos cz]]
    omega

lemma extend_mono_comb {R : Type} [Preorder R] [OrderTop R]
    (roots : List (Wire R)) (d : Nat) (hd : allowed true d) {p bank}
    (hp : Reach false roots p bank) {a b : Wire R}
    (ha : Available false bank a) (hb : Available false bank b)
    (ma : Monotone a) (mb : Monotone b) (mz : Monotone (comb d a b)) :
    ∃ q next, Reach false roots q next ∧ Available false next (comb d a b) ∧
      (∀ v, Available false bank v → Available false next v) ∧
      q + cost a + cost b ≤ p + 1 + cost (comb d a b) := by
  rcases allowed_four hd with rfl | rfl | ⟨_, rfl⟩ | ⟨_, rfl⟩
  · simpa [comb] using extend_two roots false hp ha hb
  · simpa [comb] using extend_two roots true hp ha hb
  · simpa [comb] using
      extend_mixed roots hp ha hb mb (by simpa [comb] using mz)
  · have same : comb 3 a b = combine false b (inv a) := by
      funext x
      simp [comb, combine, inv, Bool.and_comm]
    obtain ⟨q, next, reach, avail, inc, bound⟩ :=
      extend_mixed roots hp hb ha ma (same ▸ mz)
    refine ⟨q, next, reach, same.symm ▸ avail, inc, ?_⟩
    rw [same]
    omega

inductive MonoRun {R : Type} [Preorder R] (goal : Wire R) : Nat → List (Wire R) → Prop
  | stop : MonoRun goal 0 [goal]
  | perm {s xs zs} (p : xs.Perm zs) (h : MonoRun goal s xs) : MonoRun goal s zs
  | two {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat)
      (hd : allowed true op) (ka kb : Bool)
      (ma : Monotone a) (mb : Monotone b) (mz : Monotone (comb op a b))
      (tail : MonoRun goal s (comb op a b :: kept ka a (kept kb b rest))) :
      MonoRun goal (s + 1) (a :: b :: rest)

lemma MonoRun.forget {R : Type} [Preorder R] {goal : Wire R} {s ws}
    (h : MonoRun goal s ws) : Run true goal s ws := by
  induction h with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm p ih
  | two op hd ka kb _ _ _ _ ih => exact Run.two op hd ka kb ih

lemma contraction_mono {R : Type} [Preorder R] [OrderTop R]
    {goal : Wire R} (nc : ¬ Constant goal) {s ws} (h : MonoRun goal s ws)
    (roots : List (Wire R)) {p bank} (hp : Reach false roots p bank)
    (hs : supply false bank ws) :
    ∃ q next, Reach false roots q next ∧ Available false next goal ∧
      q + mass ws ≤ p + s := by
  classical
  induction h generalizing p bank with
  | stop => exact ⟨p, bank, hp, hs _ (by simp), by simp [mass, cost, nc]⟩
  | perm eq _ ih =>
    have sub : supply false bank _ := fun v hv => hs v (eq.mem_iff.mp hv)
    obtain ⟨q, next, reach, avail, bound⟩ := ih hp sub
    exact ⟨q, next, reach, avail, by simpa only [mass, ← (eq.map cost).sum_eq] using bound⟩
  | @two s a b rest op hd ka kb ma mb mz _ ih =>
    obtain ⟨r, next, reach, avail, inc, bound⟩ :=
      extend_mono_comb roots op hd hp (hs a (by simp)) (hs b (by simp)) ma mb mz
    have supplyNext : supply false next (comb op a b :: kept ka a (kept kb b rest)) := by
      intro v hv
      rcases List.mem_cons.mp hv with rfl | hv
      · exact avail
      · apply inc v
        apply hs
        rcases mem_kept hv with rfl | hv
        · simp
        · exact List.mem_cons_of_mem _ (List.mem_cons.mpr (mem_kept hv))
    obtain ⟨q, last, lastReach, goalAvail, lastBound⟩ := ih reach supplyNext
    have m1 := mass_kept a (kept kb b rest) ka
    have m2 := mass_kept b rest kb
    rw [mass_cons] at lastBound
    refine ⟨q, last, lastReach, goalAvail, ?_⟩
    rw [mass_cons, mass_cons]
    omega

lemma mono_bound {R : Type} [Preorder R] [OrderTop R]
    {goal : Wire R} {s ws} (h : MonoRun goal s ws) (nc : ¬ Constant goal)
    {roots : List (Wire R)} {p bank L} (hp : Reach false roots p bank)
    (hs : supply false bank ws)
    (lower : ∀ q bs, Reach false roots q bs → Available false bs goal → L ≤ q) :
    L + mass ws ≤ p + s := by
  obtain ⟨q, bs, reach, avail, bound⟩ := contraction_mono nc h roots hp hs
  have := lower q bs reach avail
  omega

end MonoContraction
end PEqualNP.Outside.L_meta_2592
