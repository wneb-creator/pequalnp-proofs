import PEqualNP.Defs

namespace PEqualNP.Outside.L_meta_10760

section Live

variable {α : Type} [DecidableEq α]

def build (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, available => goal ∈ available
  | k + 1, available => build ops goal k available ∨
    ∃ a ∈ available, ∃ b ∈ available, a ≠ b ∧
      ∃ z ∈ ops a b, build ops goal k (insert z available)

def live (ops : α → α → Finset α) (goal : α) : ℕ → Finset α → Prop
  | 0, s => s = {goal}
  | k + 1, s => live ops goal k s ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest)

lemma compress {ops : α → α → Finset α} {goal : α} {k : ℕ} {available : Finset α}
    (h : build ops goal k available) : ∃ s ⊆ available, live ops goal k s := by
  induction k generalizing available with
  | zero =>
    exact ⟨{goal}, Finset.singleton_subset_iff.mpr h, rfl⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨s, hs, hrun⟩ := ih skip
      exact ⟨s, hs, Or.inl hrun⟩
    · obtain ⟨t, ht, hrun⟩ := ih tail
      by_cases sub : t ⊆ available
      · exact ⟨t, sub, Or.inl hrun⟩
      · have hzmem : z ∈ t := by
          by_contra hn
          apply sub
          intro u hu
          rcases Finset.mem_insert.mp (ht hu) with rfl | ok
          · exact False.elim (hn hu)
          · exact ok
        have hzout : z ∉ available := by
          intro hh
          exact sub ((Finset.insert_eq_of_mem hh) ▸ ht)
        let rest := t.erase z
        have hrest : rest ⊆ available := by
          intro u hu
          have hu' := Finset.mem_erase.mp hu
          exact (Finset.mem_insert.mp (ht hu'.2)).resolve_left hu'.1
        let s := insert a (insert b rest)
        have hs : s ⊆ available := Finset.insert_subset ha (Finset.insert_subset hb hrest)
        refine ⟨s, hs, Or.inr ⟨a, by simp [s], b, by simp [s], hab, z, hz,
          fun h => hzout (hs h), rest, rfl, ?_⟩⟩
        simpa [rest, Finset.insert_erase hzmem] using hrun

lemma live_card {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal k s) : s.card ≤ k + 1 := by
  induction k generalizing s with
  | zero => change s = {goal} at h; simp [h]
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact (ih skip).trans (by omega)
    · have hzrest : z ∉ rest := fun hm => hout (by simp [hm])
      have htail := ih tail
      rw [Finset.card_insert_of_notMem hzrest] at htail
      have h₁ := Finset.card_insert_le a (insert b rest)
      have h₂ := Finset.card_insert_le b rest
      omega

lemma live_separates {ops : α → α → Finset α} {goal : α} (D : α → Prop)
    (hd : D goal) (hops : ∀ a b, ∀ z ∈ ops a b, D z → D a ∨ D b)
    {k : ℕ} {s : Finset α} (h : live ops goal k s) : ∃ w ∈ s, D w := by
  induction k generalizing s with
  | zero => change s = {goal} at h; exact ⟨goal, by simp [h], hd⟩
  | succ k ih =>
    rcases h with skip | ⟨a, ha, b, hb, hab, z, hz, hout, rest, rfl, tail⟩
    · exact ih skip
    · obtain ⟨w, hw, hD⟩ := ih tail
      rcases Finset.mem_insert.mp hw with rfl | hw
      · rcases hops a b w hz hD with h | h
        · exact ⟨a, ha, h⟩
        · exact ⟨b, hb, h⟩
      · exact ⟨w, by simp [hw], hD⟩

lemma first_live {ops : α → α → Finset α} {goal : α} {k : ℕ} {s : Finset α}
    (h : live ops goal (k + 1) s) :
    s = {goal} ∨
    ∃ a ∈ s, ∃ b ∈ s, a ≠ b ∧ ∃ z ∈ ops a b, z ∉ s ∧
      ∃ rest : Finset α, s = insert a (insert b rest) ∧ live ops goal k (insert z rest) := by
  induction k with
  | zero => exact h
  | succ k ih =>
    rcases h with skip | step
    · rcases ih skip with done | ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, tail⟩
      · exact .inl done
      · exact .inr ⟨a, ha, b, hb, hab, z, hz, hn, r, hs, Or.inl tail⟩
    · exact .inr step

end Live

variable {width : Nat}

def ops (x y : BitVec width) : List (BitVec width) :=
  [x &&& y, x ||| y, x &&& ~~~y, y &&& ~~~x]

abbrev basicOps (a b : BitVec width) : Finset (BitVec width) := (ops a b).toFinset

def uniqueSep {width : Nat} (S : Finset (BitVec width)) (a : BitVec width)
    (p q : Fin width) : Prop :=
  a[p.val] ≠ a[q.val] ∧ ∀ w ∈ S, w ≠ a → w[p.val] = w[q.val]

def criticalPair {width : Nat} (target : BitVec width) (S : Finset (BitVec width))
    (a b : BitVec width) : Prop :=
  a ∈ S ∧ b ∈ S ∧ a ≠ b ∧ ∃ p q ra rb sa sb : Fin width,
    target[p.val] = true ∧ target[q.val] = false ∧
    target[ra.val] = false ∧ target[rb.val] = false ∧
    target[sa.val] = true ∧ target[sb.val] = true ∧
    uniqueSep S a p ra ∧ uniqueSep S b p rb ∧
    uniqueSep S a sa q ∧ uniqueSep S b sb q ∧
    a[p.val] = a[sa.val] ∧ b[p.val] = b[sb.val]


lemma ops_equal_bits {width : Nat} {a b z : BitVec width} {p q : Fin width}
    (hz : z ∈ basicOps a b) (ha : a[p.val] = a[q.val])
    (hb : b[p.val] = b[q.val]) : z[p.val] = z[q.val] := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons,
    List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> simp [ha, hb]

lemma live_target_separates {width k : Nat} {target g : BitVec width}
    {S : Finset (BitVec width)} (run : live basicOps g k S)
    (hg : g = target ∨ g = ~~~target) {p q : Fin width}
    (different : target[p.val] ≠ target[q.val]) :
    ∃ w ∈ S, w[p.val] ≠ w[q.val] := by
  apply live_separates (fun w : BitVec width => w[p.val] ≠ w[q.val]) ?_ ?_ run
  · rcases hg with rfl | rfl
    · exact different
    · simpa using different
  · intro a b z hz hd
    by_cases ha : a[p.val] = a[q.val]
    · right
      intro hb
      exact hd (ops_equal_bits hz ha hb)
    · exact Or.inl ha

lemma uniqueSep_step {width k : Nat} {target g a b z c : BitVec width}
    {U : Finset (BitVec width)} {p q : Fin width}
    (hz : z ∈ basicOps a b) (run : live basicOps g k (insert z U))
    (hg : g = target ∨ g = ~~~target)
    (different : target[p.val] ≠ target[q.val])
    (ha : c = a → a ∉ U) (hb : c = b → b ∉ U)
    (hs : uniqueSep (insert a (insert b U)) c p q) :
    uniqueSep (insert z U) (if c = a ∨ c = b then z else c) p q := by
  by_cases hc : c = a ∨ c = b
  · rw [ite_eq_left hc]
    have hcU : c ∉ U := by
      rcases hc with rfl | rfl
      · exact ha rfl
      · exact hb rfl
    have hU : ∀ w ∈ U, w[p.val] = w[q.val] := by
      intro w hw
      apply hs.2 w (by simp [hw])
      intro eq
      exact hcU (eq ▸ hw)
    constructor
    · obtain ⟨w, hw, hd⟩ := live_target_separates run hg different
      rcases Finset.mem_insert.mp hw with rfl | hw
      · exact hd
      · exact False.elim (hd (hU w hw))
    · intro w hw hne
      exact hU w ((Finset.mem_insert.mp hw).resolve_left hne)
  · rw [ite_eq_right hc]
    refine ⟨hs.1, ?_⟩
    intro w hw hne
    rcases Finset.mem_insert.mp hw with rfl | hw
    · apply ops_equal_bits hz
      · exact hs.2 a (by simp) (fun eq => hc (.inl eq.symm))
      · exact hs.2 b (by simp) (fun eq => hc (.inr eq.symm))
    · exact hs.2 w (by simp [hw]) hne

namespace ChromGate

def eval (d : Fin 4) (a b : Bool) : Bool :=
  match d.val with
  | 0 => a && b
  | 1 => a || b
  | 2 => a && !b
  | _ => b && !a

lemma left_transport : ∀ (d : Fin 4)
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Bool),
    b₀ = b₁ → b₂ = b₃ →
    eval d a₀ b₀ ≠ eval d a₁ b₁ →
    eval d a₂ b₂ ≠ eval d a₃ b₃ →
    a₀ = a₂ → eval d a₀ b₀ = eval d a₂ b₂ := by
  decide

lemma right_transport : ∀ (d : Fin 4)
    (a₀ a₁ a₂ a₃ b₀ b₁ b₂ b₃ : Bool),
    a₀ = a₁ → a₂ = a₃ →
    eval d a₀ b₀ ≠ eval d a₁ b₁ →
    eval d a₂ b₂ ≠ eval d a₃ b₃ →
    b₀ = b₂ → eval d a₀ b₀ = eval d a₂ b₂ := by
  decide

lemma rectangle_false : ∀ (d : Fin 4) (a b c e : Bool),
    eval d a b ≠ eval d c b →
    eval d a b ≠ eval d a e →
    eval d c e ≠ eval d a e →
    eval d c e ≠ eval d c b → False := by
  decide

lemma sensitive_corner_unique : ∀ (d : Fin 4) (a b c e : Bool),
    eval d a b ≠ eval d (!a) b →
    eval d a b ≠ eval d a (!b) →
    eval d c e ≠ eval d (!c) e →
    eval d c e ≠ eval d c (!e) → a = c ∧ b = e := by
  decide

lemma opposite_corners_false : ∀ (d : Fin 4) (a b : Bool),
    eval d a b ≠ eval d (!a) b →
    eval d a b ≠ eval d a (!b) →
    eval d (!a) (!b) ≠ eval d a (!b) →
    eval d (!a) (!b) ≠ eval d (!a) b → False := by
  decide

def word {width : Nat} (d : Fin 4) (a b : BitVec width) : BitVec width :=
  match d.val with
  | 0 => a &&& b
  | 1 => a ||| b
  | 2 => a &&& ~~~b
  | _ => b &&& ~~~a

lemma word_get {width : Nat} (d : Fin 4) (a b : BitVec width) (p : Fin width) :
    (word d a b)[p.val] = eval d a[p.val] b[p.val] := by
  fin_cases d <;> simp [word, eval]

lemma of_basicOps {width : Nat} {a b z : BitVec width}
    (hz : z ∈ basicOps a b) : ∃ d : Fin 4, z = word d a b := by
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil,
    or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · exact ⟨3, rfl⟩

end ChromGate

namespace ChromGeneric

variable {α : Type} [DecidableEq α]

lemma retained_card {a b z : α} {rest : Finset α}
    (hab : a ≠ b) (hz : z ∉ insert a (insert b rest)) :
    (insert a (insert b rest)).card +
        ((if a ∈ rest then 1 else 0) + (if b ∈ rest then 1 else 0)) =
      (insert z rest).card + 1 := by
  have hzr : z ∉ rest := fun h => hz (by simp [h])
  rw [Finset.card_insert_of_notMem hzr]
  by_cases ha : a ∈ rest <;> by_cases hb : b ∈ rest
  · simp [ha, hb]
  · have ha' : a ∈ insert b rest := by simp [ha]
    simp [Finset.insert_eq_of_mem ha', Finset.card_insert_of_notMem hb, ha, hb]
  · have ha' : a ∉ insert b rest := by simp [hab, ha]
    simp [Finset.card_insert_of_notMem ha', Finset.insert_eq_of_mem hb, ha, hb]
  · have ha' : a ∉ insert b rest := by simp [hab, ha]
    simp [Finset.card_insert_of_notMem ha', Finset.card_insert_of_notMem hb, ha, hb]

def collapse (a b z c : α) : α := if c = a ∨ c = b then z else c

lemma collapse_mem {a b z c : α} {rest : Finset α}
    (hc : c ∈ insert a (insert b rest)) :
    collapse a b z c ∈ insert z rest := by
  unfold collapse
  split_ifs with h
  · simp
  · simp only [Finset.mem_insert] at hc ⊢
    exact Or.inr ((hc.resolve_left (fun hca => h (Or.inl hca))).resolve_left
      (fun hcb => h (Or.inr hcb)))


lemma extend_coloring {edge : Finset α → α → α → Prop}
    (irrefl : ∀ S c, ¬ edge S c c)
    {a b z : α} {U : Finset α} (hab : a ≠ b)
    (hnew : z ∉ insert a (insert b U))
    (transport : ∀ c ∈ insert a (insert b U), ∀ d ∈ insert a (insert b U),
      edge (insert a (insert b U)) c d →
      (c = a → a ∉ U) → (c = b → b ∉ U) →
      (d = a → a ∉ U) → (d = b → b ∉ U) →
      edge (insert z U) (collapse a b z c) (collapse a b z d))
    {x : Nat} {f : α → Nat}
    (fbound : ∀ c ∈ insert z U, f c ≤ x)
    (fproper : ∀ c ∈ insert z U, ∀ d ∈ insert z U,
      edge (insert z U) c d → f c ≠ f d) :
    ∃ g : α → Nat,
      (∀ c ∈ insert a (insert b U),
        g c ≤ x + ((if a ∈ U then 1 else 0) + (if b ∈ U then 1 else 0))) ∧
      ∀ c ∈ insert a (insert b U), ∀ d ∈ insert a (insert b U),
        edge (insert a (insert b U)) c d → g c ≠ g d := by
  let base : α → Nat := fun c => f (collapse a b z c)
  have hbase : ∀ c ∈ insert a (insert b U), base c ≤ x := by
    intro c hc
    exact fbound _ (collapse_mem hc)
  have hproper : ∀ c ∈ insert a (insert b U), ∀ d ∈ insert a (insert b U),
      edge (insert a (insert b U)) c d →
      ¬ (c = a ∧ a ∈ U) → ¬ (c = b ∧ b ∈ U) →
      ¬ (d = a ∧ a ∈ U) → ¬ (d = b ∧ b ∈ U) → base c ≠ base d := by
    intro c hc d hd he hca hcb hda hdb
    apply fproper _ (collapse_mem hc) _ (collapse_mem hd)
    apply transport c hc d hd he
    · intro h hmem; exact hca ⟨h, hmem⟩
    · intro h hmem; exact hcb ⟨h, hmem⟩
    · intro h hmem; exact hda ⟨h, hmem⟩
    · intro h hmem; exact hdb ⟨h, hmem⟩
  let g : α → Nat := fun c =>
    if c = a ∧ a ∈ U then x + 1
    else if c = b ∧ b ∈ U then x + 1 + (if a ∈ U then 1 else 0)
    else base c
  refine ⟨g, ?_, ?_⟩
  · intro c hc
    have hh := hbase c hc
    dsimp only [g]
    by_cases ha : a ∈ U <;> by_cases hb : b ∈ U
    all_goals simp only [ha, hb, and_true, and_false, ite_true, ite_false]
    all_goals first | omega | (split_ifs <;> omega)
  · intro c hc d hd he heq
    have hcBound := hbase c hc
    have hdBound := hbase d hd
    have hcd : c ≠ d := by
      intro h
      subst d
      exact irrefl _ _ he
    by_cases hca : c = a ∧ a ∈ U
    · by_cases hda : d = a ∧ a ∈ U
      · exact hcd (hca.1.trans hda.1.symm)
      · by_cases hdb : d = b ∧ b ∈ U
        · simp only [g, ite_eq_left hca, ite_eq_right hda, ite_eq_left hdb, ite_eq_left hca.2] at heq
          omega
        · simp only [g, ite_eq_left hca, ite_eq_right hda, ite_eq_right hdb] at heq
          omega
    · by_cases hcb : c = b ∧ b ∈ U
      · by_cases hda : d = a ∧ a ∈ U
        · simp only [g, ite_eq_right hca, ite_eq_left hcb, ite_eq_left hda, ite_eq_left hda.2] at heq
          omega
        · by_cases hdb : d = b ∧ b ∈ U
          · exact hcd (hcb.1.trans hdb.1.symm)
          · simp only [g, ite_eq_right hca, ite_eq_left hcb, ite_eq_right hda, ite_eq_right hdb] at heq
            split_ifs at heq <;> omega
      · by_cases hda : d = a ∧ a ∈ U
        · simp only [g, ite_eq_right hca, ite_eq_right hcb, ite_eq_left hda] at heq
          omega
        · by_cases hdb : d = b ∧ b ∈ U
          · simp only [g, ite_eq_right hca, ite_eq_right hcb, ite_eq_right hda, ite_eq_left hdb] at heq
            split_ifs at heq <;> omega
          · exact hproper c hc d hd he hca hcb hda hdb
              (by simpa only [g, ite_eq_right hca, ite_eq_right hcb, ite_eq_right hda, ite_eq_right hdb] using heq)

lemma live_coloring {ops : α → α → Finset α} {goal : α}
    (edge : Finset α → α → α → Prop)
    (irrefl : ∀ S c, ¬ edge S c c)
    (transport : ∀ (k : Nat) (a b z : α) (U : Finset α),
      a ≠ b → z ∉ insert a (insert b U) → z ∈ ops a b →
      live ops goal k (insert z U) →
      ∀ c ∈ insert a (insert b U), ∀ d ∈ insert a (insert b U),
      edge (insert a (insert b U)) c d →
      (c = a → a ∉ U) → (c = b → b ∉ U) →
      (d = a → a ∉ U) → (d = b → b ∉ U) →
      edge (insert z U) (collapse a b z c) (collapse a b z d))
    {k : Nat} {S : Finset α} (hlive : live ops goal k S) :
    ∃ x : Nat, ∃ f : α → Nat, S.card + x ≤ k + 1 ∧
      (∀ c ∈ S, f c ≤ x) ∧
      ∀ c ∈ S, ∀ d ∈ S, edge S c d → f c ≠ f d := by
  induction k generalizing S with
  | zero =>
    change S = {goal} at hlive
    subst S
    refine ⟨0, fun _ => 0, by simp, by simp, ?_⟩
    intro c hc d hd he
    simp only [Finset.mem_singleton] at hc hd
    subst c
    subst d
    exact False.elim (irrefl _ _ he)
  | succ k ih =>
    rcases hlive with hskip | ⟨a, ha, b, hb, hab, z, hz, hnew, U, rfl, htail⟩
    · obtain ⟨x, f, hcard, hbound, hproper⟩ := ih hskip
      exact ⟨x, f, by omega, hbound, hproper⟩
    · obtain ⟨x, f, hcard, hbound, hproper⟩ := ih htail
      obtain ⟨g, gbound, gproper⟩ := extend_coloring irrefl hab hnew
        (transport k a b z U hab hnew hz htail) hbound hproper
      refine ⟨x + ((if a ∈ U then 1 else 0) + (if b ∈ U then 1 else 0)),
        g, ?_, gbound, gproper⟩
      have hcount := retained_card hab hnew
      omega

end ChromGeneric

namespace ChromRelation

variable {width : Nat}

def moved (a b z c : BitVec width) : BitVec width :=
  if c = a ∨ c = b then z else c

lemma moved_mem {a b z c : BitVec width} {U : Finset (BitVec width)}
    (hc : c ∈ insert a (insert b U)) : moved a b z c ∈ insert z U := by
  unfold moved
  split_ifs with h
  · exact Finset.mem_insert_self ..
  · rcases Finset.mem_insert.mp hc with rfl | hc
    · exact False.elim (h (.inl rfl))
    · rcases Finset.mem_insert.mp hc with rfl | hc
      · exact False.elim (h (.inr rfl))
      · exact Finset.mem_insert_of_mem hc

lemma moved_ne {a b z c d : BitVec width} {U : Finset (BitVec width)}
    (hc : c ∈ insert a (insert b U)) (hd : d ∈ insert a (insert b U))
    (hz : z ∉ insert a (insert b U)) (hne : c ≠ d)
    (notboth : ¬ ((c = a ∨ c = b) ∧ (d = a ∨ d = b))) :
    moved a b z c ≠ moved a b z d := by
  unfold moved
  split_ifs with h₁ h₂ h₂
  · exact False.elim (notboth ⟨h₁, h₂⟩)
  · intro eq
    exact hz (eq ▸ hd)
  · intro eq
    exact hz (eq ▸ hc)
  · exact hne

lemma criticalPair_symm {target : BitVec width} {S : Finset (BitVec width)}
    {a b : BitVec width} (h : criticalPair target S a b) : criticalPair target S b a := by
  obtain ⟨ha, hb, hab, p, q, ra, rb, sa, sb, hp, hq, hra, hrb, hsa, hsb,
    u₁, u₂, u₃, u₄, phase₁, phase₂⟩ := h
  exact ⟨hb, ha, hab.symm, p, q, rb, ra, sb, sa, hp, hq, hrb, hra, hsb, hsa,
    u₂, u₁, u₄, u₃, phase₂, phase₁⟩

lemma bool_other_eq {x y z : Bool} (hy : x ≠ y) (hz : x ≠ z) : y = z := by
  cases x <;> cases y <;> cases z <;> simp_all

lemma moved_phase {a b z c : BitVec width} {U : Finset (BitVec width)}
    {p r s q : Fin width} (hab : a ≠ b) (hz : z ∈ basicOps a b)
    (u₁ : uniqueSep (insert a (insert b U)) c p r)
    (u₂ : uniqueSep (insert a (insert b U)) c s q)
    (v₁ : uniqueSep (insert z U) (moved a b z c) p r)
    (v₂ : uniqueSep (insert z U) (moved a b z c) s q)
    (phase : c[p.val] = c[s.val]) :
    (moved a b z c)[p.val] = (moved a b z c)[s.val] := by
  by_cases hc : c = a ∨ c = b
  · simp only [moved, ite_eq_left hc] at v₁ v₂ ⊢
    obtain ⟨d, rfl⟩ := ChromGate.of_basicOps hz
    rcases hc with rfl | rfl
    · have e₁ := u₁.2 b (by simp) hab.symm
      have e₂ := u₂.2 b (by simp) hab.symm
      have d₁ := v₁.1
      have d₂ := v₂.1
      simp only [ChromGate.word_get] at d₁ d₂ ⊢
      exact ChromGate.left_transport d _ _ _ _ _ _ _ _ e₁ e₂ d₁ d₂ phase
    · have e₁ := u₁.2 a (by simp) hab
      have e₂ := u₂.2 a (by simp) hab
      have d₁ := v₁.1
      have d₂ := v₂.1
      simp only [ChromGate.word_get] at d₁ d₂ ⊢
      exact ChromGate.right_transport d _ _ _ _ _ _ _ _ e₁ e₂ d₁ d₂ phase
  · simpa only [moved, ite_eq_right hc] using phase

lemma criticalPair_noCollapse {k : Nat} {target g a b z : BitVec width}
    {U : Finset (BitVec width)} (hz : z ∈ basicOps a b)
    (run : live basicOps g k (insert z U)) (hg : g = target ∨ g = ~~~target)
    (ha : a ∉ U) (hb : b ∉ U)
    (h : criticalPair target (insert a (insert b U)) a b) : False := by
  obtain ⟨_, _, hab, p, q, ra, rb, sa, sb, hp, hq, hra, hrb, hsa, hsb,
    u₁, u₂, u₃, u₄, phase₁, phase₂⟩ := h
  have v₁ : z[p.val] ≠ z[ra.val] := by
    simpa using (uniqueSep_step hz run hg (by simp [hp, hra])
      (fun _ => ha) (fun _ => hb) u₁).1
  have v₂ : z[p.val] ≠ z[rb.val] := by
    simpa using (uniqueSep_step hz run hg (by simp [hp, hrb])
      (fun _ => ha) (fun _ => hb) u₂).1
  have v₃ : z[sa.val] ≠ z[q.val] := by
    simpa using (uniqueSep_step hz run hg (by simp [hsa, hq])
      (fun _ => ha) (fun _ => hb) u₃).1
  have v₄ : z[sb.val] ≠ z[q.val] := by
    simpa using (uniqueSep_step hz run hg (by simp [hsb, hq])
      (fun _ => ha) (fun _ => hb) u₄).1
  have ara : a[ra.val] = a[q.val] := bool_other_eq u₁.1 (phase₁ ▸ u₃.1)
  have brb : b[rb.val] = b[q.val] := bool_other_eq u₂.1 (phase₂ ▸ u₄.1)
  have bra := u₁.2 b (by simp) hab.symm
  have arb := u₂.2 a (by simp) hab
  have bsa := u₃.2 b (by simp) hab.symm
  have asb := u₄.2 a (by simp) hab
  obtain ⟨d, hzword⟩ := ChromGate.of_basicOps hz
  have d₁ : ChromGate.eval d a[p.val] b[p.val] ≠ ChromGate.eval d a[q.val] b[p.val] := by
    simpa only [hzword, ChromGate.word_get, ara, ← bra] using v₁
  have d₂ : ChromGate.eval d a[p.val] b[p.val] ≠ ChromGate.eval d a[p.val] b[q.val] := by
    simpa only [hzword, ChromGate.word_get, brb, ← arb] using v₂
  have d₃ : ChromGate.eval d a[q.val] b[q.val] ≠ ChromGate.eval d a[p.val] b[q.val] := by
    simpa only [hzword, ChromGate.word_get, ← phase₁, bsa] using v₃.symm
  have d₄ : ChromGate.eval d a[q.val] b[q.val] ≠ ChromGate.eval d a[q.val] b[p.val] := by
    simpa only [hzword, ChromGate.word_get, ← phase₂, asb] using v₄.symm
  exact ChromGate.rectangle_false d _ _ _ _ d₁ d₂ d₃ d₄

lemma criticalPair_step {k : Nat} {target g a b z c d : BitVec width}
    {U : Finset (BitVec width)} (hab : a ≠ b) (hz : z ∈ basicOps a b)
    (fresh : z ∉ insert a (insert b U))
    (run : live basicOps g k (insert z U)) (hg : g = target ∨ g = ~~~target)
    (hca : c = a → a ∉ U) (hcb : c = b → b ∉ U)
    (hda : d = a → a ∉ U) (hdb : d = b → b ∉ U)
    (h : criticalPair target (insert a (insert b U)) c d) :
    criticalPair target (insert z U)
      (if c = a ∨ c = b then z else c) (if d = a ∨ d = b then z else d) := by
  have notboth : ¬ ((c = a ∨ c = b) ∧ (d = a ∨ d = b)) := by
    rintro ⟨hc, hd⟩
    rcases hc with rfl | rfl <;> rcases hd with rfl | rfl
    · exact h.2.2.1 rfl
    · exact criticalPair_noCollapse hz run hg (hca rfl) (hdb rfl) h
    · exact criticalPair_noCollapse hz run hg (hda rfl) (hcb rfl) (criticalPair_symm h)
    · exact h.2.2.1 rfl
  obtain ⟨hc, hd, hcd, p, q, ra, rb, sa, sb, hp, hq, hra, hrb, hsa, hsb,
    u₁, u₂, u₃, u₄, phase₁, phase₂⟩ := h
  have v₁ := uniqueSep_step hz run hg (by simp [hp, hra]) hca hcb u₁
  have v₂ := uniqueSep_step hz run hg (by simp [hp, hrb]) hda hdb u₂
  have v₃ := uniqueSep_step hz run hg (by simp [hsa, hq]) hca hcb u₃
  have v₄ := uniqueSep_step hz run hg (by simp [hsb, hq]) hda hdb u₄
  change criticalPair target (insert z U) (moved a b z c) (moved a b z d)
  exact ⟨moved_mem hc, moved_mem hd, moved_ne hc hd fresh hcd notboth,
    p, q, ra, rb, sa, sb, hp, hq, hra, hrb, hsa, hsb, v₁, v₂, v₃, v₄,
    moved_phase hab hz u₁ u₃ v₁ v₃ phase₁,
    moved_phase hab hz u₂ u₄ v₂ v₄ phase₂⟩

end ChromRelation

lemma live_criticalPair_coloring {width k : Nat} {target g : BitVec width}
    {S : Finset (BitVec width)} (run : live basicOps g k S)
    (hg : g = target ∨ g = ~~~target) :
    ∃ color : BitVec width → Nat,
      (∀ a ∈ S, color a < k + 2 - S.card) ∧
      ∀ a b, criticalPair target S a b → color a ≠ color b := by
  have irrefl : ∀ U c, ¬ criticalPair target U c c := by
    intro U c h
    exact h.2.2.1 rfl
  obtain ⟨x, color, hcard, hbound, hproper⟩ :=
    ChromGeneric.live_coloring (criticalPair target) irrefl
      (by
        intro n a b z U hab fresh hz tail c hc d hd edge hca hcb hda hdb
        exact ChromRelation.criticalPair_step hab hz fresh tail hg
          hca hcb hda hdb edge) run
  refine ⟨color, ?_, ?_⟩
  · intro a ha
    have := hbound a ha
    omega
  · intro a b edge
    exact hproper a edge.1 b edge.2.1 edge

def canonical (w : BitVec width) : BitVec width :=
  if w.toNat ≤ (~~~w).toNat then w else ~~~w

lemma canonical_of_msb_false {w : BitVec width} (h : w.msb = false) :
    canonical w = w := by
  have bound := BitVec.msb_eq_false_iff_two_mul_lt.mp h
  have order : w.toNat ≤ (~~~w).toNat := by
    rw [BitVec.toNat_not]
    omega
  simp only [canonical, if_pos order]

lemma canonical_msb_false (w : BitVec width) : (canonical w).msb = false := by
  unfold canonical
  split_ifs with order
  · apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    rw [BitVec.toNat_not] at order
    have bound := w.isLt
    omega
  · apply BitVec.msb_eq_false_iff_two_mul_lt.mpr
    rw [BitVec.toNat_not] at order ⊢
    have bound := w.isLt
    omega

lemma ops_msb_false {a b w : BitVec width} (ha : a.msb = false)
    (hb : b.msb = false) (hw : w ∈ ops a b) : w.msb = false := by
  simp only [ops, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl <;> simp [ha, hb]

lemma canonical_ops {a b : BitVec width} (ha : a.msb = false)
    (hb : b.msb = false) : (ops a b).map canonical = ops a b := by
  have one (w : BitVec width) (hw : w ∈ ops a b) : canonical w = w :=
    canonical_of_msb_false (ops_msb_false ha hb hw)
  simpa only [List.map_id'] using List.map_congr_left one

open PEqualNP.CircuitLowerBounds

def holds (av : Finset (BitVec width)) (z : (BitVec width)) : Prop :=
  z = 0 ∨ z = ~~~0 ∨ ∃ a ∈ av, z = a ∨ z = ~~~a

lemma holds_insert {av : Finset (BitVec width)} {z a : (BitVec width)} (h : holds av z) : holds (insert a av) z := by
  rcases h with h|h|⟨u,hu,he⟩
  · exact .inl h
  · exact .inr (.inl h)
  · exact .inr (.inr ⟨u,Finset.mem_insert_of_mem hu,he⟩)

lemma holds_not {av : Finset (BitVec width)} {z : (BitVec width)} (h : holds av z) : holds av (~~~z) := by
  rcases h with rfl|rfl|⟨a,ha,he⟩
  · exact .inr (.inl rfl)
  · exact .inl BitVec.not_not
  · rcases he with he|he <;> rw [he]
    · exact .inr (.inr ⟨a, ha, .inr rfl⟩)
    · exact .inr (.inr ⟨a, ha, .inl BitVec.not_not⟩)

def reachable (av : Finset (BitVec width)) (z : (BitVec width)) : Prop :=
  holds av z ∨ ∃ a ∈ av, ∃ b ∈ av, a ≠ b ∧ ∃ w ∈ basicOps a b, holds (insert w av) z

lemma reachable_not {av : Finset (BitVec width)} {z : (BitVec width)} (h : reachable av z) : reachable av (~~~z) := by
  rcases h with h|⟨a,ha,b,hb,ne,w,hop,hw⟩
  · exact .inl (holds_not h)
  · exact .inr ⟨a,ha,b,hb,ne,w,hop,holds_not hw⟩

set_option maxRecDepth 5000 in
lemma and_reach {av : Finset (BitVec width)} {x y : (BitVec width)} (hx : holds av x) (hy : holds av y) :
    reachable av (x &&& y) := by
  have const : holds av (0 : (BitVec width)) := .inl rfl
  have oldx := hx
  rcases hx with rfl|rfl|⟨a,ha,ea⟩
  · rw [show (0 : (BitVec width)) &&& y = 0 from BitVec.zero_and]; exact .inl const
  · have he : (~~~(0 : BitVec width)) &&& y = y := by
      apply BitVec.eq_of_getLsbD_eq
      intro i
      simp
    rw [he]
    exact .inl hy
  rcases hy with rfl|rfl|⟨b,hb,eb⟩
  · rw [show x &&& (0 : (BitVec width)) = 0 from BitVec.and_zero]; exact .inl const
  · have he : x &&& ~~~(0 : BitVec width) = x := by
      apply BitVec.eq_of_getLsbD_eq
      intro i
      simp
    rw [he]
    exact .inl oldx
  by_cases h : a = b
  · subst b
    rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb] <;>
      simp only [BitVec.and_self, BitVec.and_not_self, BitVec.not_and_self] <;>
      first | exact .inl const | exact .inl (.inr (.inr ⟨a,ha,.inl rfl⟩)) |
        exact .inl (.inr (.inr ⟨a,ha,.inr rfl⟩))
  have add (w : (BitVec width)) (hw : w ∈ basicOps a b) (z : (BitVec width)) (hz : z = w ∨ z = ~~~w) :
      reachable av z :=
    .inr ⟨a,ha,b,hb,h,w,hw,.inr (.inr ⟨w,Finset.mem_insert_self ..,hz⟩)⟩
  rcases ea with ea|ea <;> rcases eb with eb|eb <;> rw [ea,eb]
  · exact add _ (by simp [basicOps,ops] : a &&& b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : a &&& ~~~b ∈ basicOps a b) _ (.inl rfl)
  · exact add _ (by simp [basicOps,ops] : b &&& ~~~a ∈ basicOps a b) _ (.inl (BitVec.and_comm ..))
  · exact add _ (by simp [basicOps,ops] : a ||| b ∈ basicOps a b) _ (.inr BitVec.not_or.symm)

lemma or_reach {av : Finset (BitVec width)} {x y : (BitVec width)} (hx : holds av x) (hy : holds av y) :
    reachable av (x ||| y) := by
  simpa only [BitVec.not_and, BitVec.not_not] using reachable_not (and_reach (holds_not hx) (holds_not hy))

private def bit (k : Fin width) (z : (BitVec width)) : Bool := z[k.val]
private def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

private lemma read_bit (w : List (BitVec width)) (i : ℕ) (k : Fin width) :
    (w.map (bit k)).getD i false = bit k (w.getD i 0) := by
  by_cases h : i < w.length
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem h]
  · simp [List.getD_eq_getElem?_getD, List.getElem?_map,
      List.getElem?_eq_none (Nat.le_of_not_gt h), bit]

def legal (g : Gate) : Prop := (g.op = .and ∨ g.op = .or ∨ g.op = .not) ∧ g.inputs.length ≤ 2

def action (w : List (BitVec width)) (g : Gate) : (BitVec width) := match g.op with
  | .not => ~~~(g.inputs.head?.map (fun i => w.getD i 0)).getD 0
  | .and => (g.inputs.map fun i => w.getD i 0).foldr (· &&& ·) (~~~0)
  | .or => (g.inputs.map fun i => w.getD i 0).foldr (· ||| ·) 0
  | _ => 0

lemma evalAnd (xs : List Bool) : GateOp.and.eval xs = xs.all id := rfl
lemma evalOr (xs : List Bool) : GateOp.or.eval xs = xs.any id := rfl
lemma evalNot (xs : List Bool) : GateOp.not.eval xs = !(xs.headD false) := rfl

set_option maxRecDepth 5000 in
lemma action_spec (w : List (BitVec width)) (g : Gate) (hg : legal g) (k : Fin width) :
    step (w.map (bit k)) g = (w ++ [action w g]).map (bit k) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals have bit0 : (0 : (BitVec width))[k.val] = false := by change (0 : BitVec width)[k.val] = false; simp
  all_goals rcases hop with rfl|rfl|rfl <;>
    simp only [step, List.map_cons,List.map_nil,read_bit,List.map_append] <;>
    simp only [action, evalAnd, evalOr, evalNot, List.foldr_cons,List.foldr_nil,List.head?_cons,List.head?_nil,
      List.headD_cons,List.headD_nil,Option.map_some,Option.map_none,Option.getD_some,Option.getD_none,
      List.all_cons,List.all_nil,List.any_cons,List.any_nil,List.map_cons,List.map_nil,id_eq,
      Bool.and_true,Bool.or_false, bit,BitVec.getElem_and,BitVec.getElem_or,BitVec.getElem_not,
      BitVec.getElem_zero,bit0,Bool.not_false] <;> rfl

def isBinary (g : Gate) : Bool := match g.op with
  | .not => false
  | _ => true
def binaryCost (gs : List Gate) := (gs.filter isBinary).length

lemma available_read {av : Finset (BitVec width)} {w : List (BitVec width)} (hw : ∀ u ∈ w, holds av u) (i : ℕ) :
    holds av (w.getD i 0) := by
  by_cases h : i < w.length
  · exact hw _ (by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h])
  · rw [List.getD_eq_default _ _ (Nat.le_of_not_gt h)]
    exact .inl rfl

set_option maxRecDepth 5000 in
lemma gate_reach (w : List (BitVec width)) (av : Finset (BitVec width)) (hw : ∀ u ∈ w, holds av u)
    (g : Gate) (hg : legal g) :
    if isBinary g then reachable av (action w g) else holds av (action w g) := by
  obtain ⟨op,args⟩ := g
  obtain ⟨hop,cap⟩ := hg
  change op = .and ∨ op = .or ∨ op = .not at hop
  change args.length ≤ 2 at cap
  rcases args with _|⟨i,_|⟨j,_|⟨u,tail⟩⟩⟩ <;> try simp at cap
  all_goals rcases hop with rfl|rfl|rfl <;> simp only [isBinary,Bool.false_eq_true,ite_false,ite_true,
    action,List.head?_nil,List.head?_cons,List.map_nil,List.map_cons,List.foldr_nil,List.foldr_cons,
    Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
    show ∀ x : (BitVec width), x ||| (0 : (BitVec width)) = x from fun x => BitVec.or_zero,
    show ∀ x : (BitVec width), x &&& ~~~0 = x from fun x => by simp]
  all_goals first
    | exact .inl (.inl rfl)
    | exact .inl (.inr (.inl rfl))
    | exact .inr (.inl rfl)
    | exact .inl (available_read hw _)
    | exact holds_not (available_read hw _)
    | exact and_reach (available_read hw _) (available_read hw _)
    | exact or_reach (available_read hw _) (available_read hw _)

set_option maxRecDepth 4000 in
lemma compile {goal : BitVec width} (nonzero : goal ≠ 0) (nonones : goal ≠ ~~~0) (gs : List Gate) (out : ℕ) (hg : ∀ g ∈ gs, legal g)
    (w : List (BitVec width)) (av : Finset (BitVec width)) (hw : ∀ u ∈ w, holds av u)
    (he : ∀ k, (gs.foldl step (w.map (bit k))).getD out false = bit k goal) :
    ∃ t, (t = goal ∨ t = ~~~goal) ∧ build basicOps t (binaryCost gs) av := by
  induction gs generalizing w av with
  | nil =>
    have hv : w.getD out 0 = goal := by
      apply BitVec.eq_of_getElem_eq
      intro i hi
      simpa only [List.foldl_nil, read_bit, bit] using he ⟨i,hi⟩
    have h := hv ▸ available_read hw out
    rcases h with zero|ones|⟨t,ht,eq|eq⟩
    · exact False.elim (nonzero zero)
    · exact False.elim (nonones ones)
    · exact ⟨t, .inl eq.symm, ht⟩
    · exact ⟨t, .inr (by rw [eq, BitVec.not_not]), ht⟩
  | cons g gs ih =>
    let z := action w g
    have stepOK := action_spec w g (hg g (by simp))
    have nextEval : ∀ k, (gs.foldl step ((w ++ [z]).map (bit k))).getD out false = bit k goal := by
      intro k; simpa only [List.foldl_cons, stepOK] using he k
    have tail := ih (fun t ht => hg t (by simp [ht])) (w ++ [z])
    have cont (A : Finset (BitVec width)) (hold : ∀ u ∈ w, holds A u) (new : holds A z) :=
      tail A (by
        intro u hu
        rcases List.mem_append.mp hu with hu|hu
        · exact hold u hu
        · exact (List.mem_singleton.mp hu) ▸ new) nextEval
    have stepClass := gate_reach w av hw g (hg g (by simp))
    cases neg : isBinary g
    · simp only [neg,Bool.false_eq_true,ite_false] at stepClass
      simpa [binaryCost,neg] using cont av hw stepClass
    · simp only [neg,ite_true] at stepClass
      have len : binaryCost (g::gs) = binaryCost gs+1 := by simp [binaryCost,neg]
      rw [len]
      rcases stepClass with existing|⟨a,ha,b,hb,ne,new,op,rep⟩
      · obtain ⟨t,ht,run⟩ := cont av hw existing
        exact ⟨t,ht,Or.inl run⟩
      · obtain ⟨t,ht,run⟩ := cont (insert new av) (fun u hu => holds_insert (hw u hu)) rep
        exact ⟨t,ht,Or.inr ⟨a,ha,b,hb,ne,new,op,run⟩⟩

lemma bound_from_samples {inputCount budget : Nat} {goal : BitVec width}
    (nonzero : goal ≠ 0) (nonones : goal ≠ ~~~0)
    (target : (Fin inputCount → Bool) → Bool) (ins : List (BitVec width))
    (roots : Finset (BitVec width)) (represented : ∀ u ∈ ins, holds roots u)
    (inputLength : ins.length = inputCount)
    (row : ∀ j : Fin width,
      target (fun i => (ins.getD i.val 0)[j.val]) = goal[j.val])
    (rejection : ∀ z, z = goal ∨ z = ~~~goal →
      ¬ build basicOps z budget roots)
    (gs : List Gate) (out : Nat) (legalGates : ∀ g ∈ gs, legal g)
    (computes : ∀ x : Fin inputCount → Bool,
      Circuit.eval ⟨gs, out⟩ (List.ofFn x) = target x) :
    budget < binaryCost gs := by
  by_contra! low
  have evaluate (k : Fin width) :
      (gs.foldl step (ins.map (bit k))).getD out false = bit k goal := by
    let x (i : Fin inputCount) : Bool := bit k (ins.getD i.val 0)
    have same : List.ofFn x = ins.map (bit k) := by
      apply List.ext_getElem
      · simp [inputLength]
      · intro i hi hj
        have hlt : i < ins.length := by simpa using hj
        simp only [List.getElem_ofFn, List.getElem_map, x,
          List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
    change Circuit.eval ⟨gs, out⟩ (ins.map (bit k)) = bit k goal
    rw [← same, computes]
    exact row k
  obtain ⟨z, hz, run⟩ := compile nonzero nonones gs out legalGates ins roots
    represented evaluate
  have lift {a b : Nat} (h : a ≤ b) (hr : build basicOps z a roots) :
      build basicOps z b roots := by
    induction h with
    | refl => exact hr
    | step _ ih => exact Or.inl ih
  exact rejection z hz (lift low run)

lemma replace_from_samples {inputCount replacementSize : Nat} {goal : BitVec width}
    (nonzero : goal ≠ 0) (nonones : goal ≠ ~~~0)
    (target : (Fin inputCount → Bool) → Bool) (ins : List (BitVec width))
    (roots : Finset (BitVec width)) (represented : ∀ u ∈ ins, holds roots u)
    (inputLength : ins.length = inputCount)
    (row : ∀ j : Fin width,
      target (fun i => (ins.getD i.val 0)[j.val]) = goal[j.val])
    (rejection : ∀ z, z = goal ∨ z = ~~~goal →
      ¬ build basicOps z (replacementSize - 2) roots)
    (upper : ∃ (gs : List Gate) (out : Nat),
      (∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      gs.length = replacementSize ∧
      ∀ x : Fin inputCount → Bool, Circuit.eval ⟨gs, out⟩ (List.ofFn x) = target x)
    (gs : List Gate) (out : Nat) (legalGates : ∀ g ∈ gs, legal g)
    (computes : ∀ x : Fin inputCount → Bool,
      Circuit.eval ⟨gs, out⟩ (List.ofFn x) = target x) :
    ∃ (ds : List Gate) (newOut : Nat),
      (∀ g ∈ ds, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2) ∧
      ds.length ≤ gs.length ∧
      ∀ x : Fin inputCount → Bool, Circuit.eval ⟨ds, newOut⟩ (List.ofFn x) = target x := by
  by_cases present : ∃ g ∈ gs, g.op = .not
  · obtain ⟨g, member, op⟩ := present
    have cut : binaryCost gs < gs.length :=
      (List.length_filter_lt_length_iff_exists (p := isBinary)).mpr
        ⟨g, member, by simp [isBinary, op]⟩
    have lower := bound_from_samples nonzero nonones target ins roots represented inputLength row rejection
      gs out legalGates computes
    obtain ⟨ds, newOut, ok, size, evaluates⟩ := upper
    exact ⟨ds, newOut, ok, by omega, evaluates⟩
  · refine ⟨gs, out, ?_, le_rfl, computes⟩
    intro g member
    obtain ⟨op, arity⟩ := legalGates g member
    exact ⟨op.elim Or.inl (fun h => h.elim Or.inr
      (fun eq => (present ⟨g, member, eq⟩).elim)), arity⟩


lemma signedRootsTransport {width n : Nat} {g : BitVec width}
    (nonzero : g ≠ 0) (nonones : g ≠ ~~~0)
    {s t : Finset (BitVec width)}
    (represented : ∀ x ∈ s, holds t x)
    (run : build basicOps g n s) :
    ∃ g', (g' = g ∨ g' = ~~~g) ∧ build basicOps g' n t := by
  induction n generalizing s t with
  | zero =>
    have hg : holds t g := represented g run
    rcases hg with hzero | hones | ⟨a, ha, h | h⟩
    · exact False.elim (nonzero hzero)
    · exact False.elim (nonones hones)
    · exact ⟨a, .inl h.symm, ha⟩
    · exact ⟨a, .inr (by rw [h, BitVec.not_not]), ha⟩
  | succ n ih =>
    rcases run with skip | ⟨a, ha, b, hb, hab, z, hz, tail⟩
    · obtain ⟨g', he, hg'⟩ := ih represented skip
      exact ⟨g', he, Or.inl hg'⟩
    · have za : holds t a := represented a ha
      have zb : holds t b := represented b hb
      have reach : reachable t z := by
        simp only [basicOps, ops, List.mem_toFinset, List.mem_cons,
          List.not_mem_nil, or_false] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact and_reach za zb
        · exact or_reach za zb
        · exact and_reach za (holds_not zb)
        · exact and_reach zb (holds_not za)
      rcases reach with old | ⟨a', ha', b', hb', ne, w, hw, added⟩
      · have rep : ∀ x ∈ insert z s, holds t x := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact old
          · exact represented x hx
        obtain ⟨g', he, hg'⟩ := ih rep tail
        exact ⟨g', he, Or.inl hg'⟩
      · have rep : ∀ x ∈ insert z s, holds (insert w t) x := by
          intro x hx
          rcases Finset.mem_insert.mp hx with rfl | hx
          · exact added
          · exact holds_insert (represented x hx)
        obtain ⟨g', he, hg'⟩ := ih rep tail
        exact ⟨g', he, Or.inr ⟨a', ha', b', hb', ne, w, hw, hg'⟩⟩


namespace SearchKernel

open PEqualNP.Outside.L_meta_10760

variable {width : Nat}

def singles {α : Type} : List α → List (α × List α)
  | [] => []
  | a :: rest => (a, rest) :: (singles rest).map (fun (b, bs) => (b, a :: bs))

def pairs {α : Type} : List α → List (α × α × List α)
  | [] => []
  | a :: rest => (singles rest).map (fun (b, bs) => (a, b, bs)) ++
      (pairs rest).map (fun (b, c, bs) => (b, c, a :: bs))

set_option maxRecDepth 100000 in
lemma pick_one {α : Type} {a : α} {ws : List α} (h : a ∈ ws) :
    ∃ rest, (a, rest) ∈ singles ws ∧ ws.Perm (a :: rest) := by
  induction ws with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with e | h
    · subst x; exact ⟨xs, by simp [singles], .refl _⟩
    · obtain ⟨rest, hm, hp⟩ := ih h
      refine ⟨x :: rest, List.mem_cons_of_mem _ (List.mem_map.mpr ⟨(a, rest), hm, rfl⟩), ?_⟩
      exact (hp.cons x).trans (.swap _ _ _)

set_option maxRecDepth 100000 in
lemma pick_two {α : Type} {a b : α} {ws : List α} (ha : a ∈ ws) (hb : b ∈ ws) (hne : a ≠ b) :
    ∃ rest, ((a, b, rest) ∈ pairs ws ∨ (b, a, rest) ∈ pairs ws) ∧
      ws.Perm (a :: b :: rest) := by
  induction ws with
  | nil => simp at ha
  | cons x xs ih =>
    rcases List.mem_cons.mp ha with h | ha
    · subst x
      obtain ⟨r, hm, hp⟩ := pick_one ((List.mem_cons.mp hb).resolve_left (Ne.symm hne))
      exact ⟨r, .inl (List.mem_append_left _ (List.mem_map.mpr ⟨(b, r), hm, rfl⟩)), hp.cons a⟩
    · rcases List.mem_cons.mp hb with h | hb
      · subst x
        obtain ⟨r, hm, hp⟩ := pick_one (ws := xs) (a := a) (by assumption)
        exact ⟨r, .inr (List.mem_append_left _ (List.mem_map.mpr ⟨(a, r), hm, rfl⟩)),
          (hp.cons b).trans (.swap _ _ _)⟩
      · obtain ⟨r, hm, hp⟩ := ih ha hb
        refine ⟨x :: r, ?_,
          (hp.cons x).trans ((List.Perm.swap _ _ _).trans ((List.Perm.swap _ _ _).cons a))⟩
        rcases hm with hm | hm
        · exact .inl (List.mem_append_right _ (List.mem_map.mpr ⟨(a, b, r), hm, rfl⟩))
        · exact .inr (List.mem_append_right _ (List.mem_map.mpr ⟨(b, a, r), hm, rfl⟩))

lemma ops_swap (a b : (BitVec width)) : basicOps a b = basicOps b a := by
  ext z
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false]
  rw [BitVec.and_comm a b, BitVec.or_comm a b]
  tauto

def keepChoices (a b : (BitVec width)) (r : List (BitVec width)) : List (List (BitVec width)) := [r, a :: r, b :: r, a :: b :: r]

set_option maxRecDepth 100000 in
lemma recover_kept {ws r : List (BitVec width)} {a b : (BitVec width)} {needed : Finset (BitVec width)}
    (hp : ws.Perm (a :: b :: r)) (hn : ws.Nodup)
    (hs : ws.toFinset = insert a (insert b needed)) :
    ∃ kept ∈ keepChoices a b r, kept.Nodup ∧ kept.toFinset = needed := by
  have habr := hp.nodup_iff.mp hn
  have hbase : ws.toFinset = insert a (insert b r.toFinset) := by
    ext v
    simp [hp.mem_iff]
  have henne : ∀ v, v ∈ r ↔ v ∈ needed ∧ v ≠ a ∧ v ≠ b := by
    intro v
    have he : (v ∈ insert a (insert b r.toFinset)) ↔ v ∈ insert a (insert b needed) := by
      rw [← hbase, ← hs]
    simp only [Finset.mem_insert, List.mem_toFinset] at he
    simp only [List.nodup_cons, List.mem_cons, not_or] at habr
    grind
  by_cases ha : a ∈ needed <;> by_cases hb : b ∈ needed
  · refine ⟨a :: b :: r, by simp [keepChoices], habr, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨a :: r, by simp [keepChoices], ?_, ?_⟩
    · simp_all [List.nodup_cons]
    · ext v; simp [henne]; grind
  · refine ⟨b :: r, by simp [keepChoices], (List.nodup_cons.mp habr).2, ?_⟩
    ext v; simp [henne]; grind
  · refine ⟨r, by simp [keepChoices], (List.nodup_cons.mp (List.nodup_cons.mp habr).2).2, ?_⟩
    ext v; simp [henne]; grind

set_option maxRecDepth 100000 in
lemma singleton_list {goal : (BitVec width)} {ws : List (BitVec width)} (hn : ws.Nodup) (hs : ws.toFinset = {goal}) : ws = [goal] := by
  have hc := List.toFinset_card_of_nodup hn
  rw [hs] at hc
  cases ws with
  | nil => simp at hc
  | cons w ws =>
    cases ws with
    | nil => simpa using hs
    | cons => simp at hc

def rowClass (j : Fin width) (w : BitVec width) : BitVec width :=
  if w[j.val] then w else ~~~w

def survivors (goal : BitVec width) (j : Fin width) (ws : List (BitVec width)) : BitVec width :=
  ws.foldr (fun w r => rowClass j w &&& r) goal

def separates (goal : BitVec width) (rows : List (Fin width))
    (ws : List (BitVec width)) : Bool :=
  rows.all (fun j => goal[j.val] || (survivors goal j ws == 0))

lemma rowClass_bit (i j : Fin width) (w : BitVec width) :
    (rowClass j w)[i.val] = true ↔ w[i.val] = w[j.val] := by
  unfold rowClass
  split <;> simp_all

lemma survivors_bit (goal : BitVec width) (i j : Fin width) (ws : List (BitVec width)) :
    (survivors goal j ws)[i.val] = true ↔
      goal[i.val] = true ∧ ∀ w ∈ ws, w[i.val] = w[j.val] := by
  induction ws with
  | nil => simp [survivors]
  | cons w ws ih =>
    simp only [survivors, List.foldr_cons, BitVec.getElem_and, Bool.and_eq_true]
    change (rowClass j w)[i.val] = true ∧ (survivors goal j ws)[i.val] = true ↔ _
    rw [rowClass_bit, ih]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

lemma ops_separate (i j : Fin width) (a b z : BitVec width) (hz : z ∈ basicOps a b)
    (hd : z[i.val] ≠ z[j.val]) : a[i.val] ≠ a[j.val] ∨ b[i.val] ≠ b[j.val] := by
  by_contra h
  push Not at h
  simp only [basicOps, ops, List.mem_toFinset, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl <;> apply hd <;>
    simp only [BitVec.getElem_and, BitVec.getElem_or, BitVec.getElem_not, h.1, h.2]

lemma separates_complete {goal g : BitVec width} (hg : g = goal ∨ g = ~~~goal)
    (rows : List (Fin width))
    {k : Nat} {ws : List (BitVec width)} (h : live basicOps g k ws.toFinset) :
    separates goal rows ws = true := by
  rw [separates, List.all_eq_true]
  intro j hj
  cases he : goal[j.val] with
  | true => simp [he]
  | false =>
    simp only [he, Bool.false_or, beq_iff_eq]
    apply BitVec.eq_of_getElem_eq
    intro i hi
    have zi : (0 : BitVec width)[i] = false := by simp
    rw [zi]
    cases hs : (survivors goal j ws)[i] with
    | false => rfl
    | true =>
      obtain ⟨hgoal, hagree⟩ := (survivors_bit goal ⟨i,hi⟩ j ws).mp hs
      have diff : g[i] ≠ g[j.val] := by
        rcases hg with rfl | rfl <;> simp [hgoal, he]
      obtain ⟨w, hw, hd⟩ := live_separates (fun w : BitVec width => w[i] ≠ w[j.val])
        diff (ops_separate ⟨i,hi⟩ j) h
      exact False.elim (hd (hagree w (List.mem_toFinset.mp hw)))


def dispatch (goal : BitVec width) (rows : List (Fin width)) (extra : Nat)
    (next : Nat → List (BitVec width) → Bool) (a b : BitVec width)
    (r : List (BitVec width)) : Bool :=
  (ops a b).any fun z => !(a :: b :: r).contains z &&
    (keepChoices a b r).any fun kept =>
    decide (kept.length ≤ extra + r.length) && separates goal rows (z :: kept) &&
      next (extra + r.length - kept.length) (z :: kept)

def optimized (goal : BitVec width) (rows : List (Fin width)) : Nat → Nat → List (BitVec width) → Bool
  | 0, _, ws => (ws == [goal] || ws == [~~~goal])
  | k + 1, extra, ws => (ws == [goal] || ws == [~~~goal]) ||
    (pairs ws).any (fun (a, b, r) => dispatch goal rows extra (optimized goal rows k) a b r)

lemma dispatch_complete {goal : BitVec width} {rows : List (Fin width)} {k extra : Nat} {a b z : BitVec width}
    {r kept : List (BitVec width)} (next : Nat → List (BitVec width) → Bool)
    (hz : z ∈ basicOps a b) (hnew : z ∉ a :: b :: r) (hk : kept ∈ keepChoices a b r)
    (he : extra + r.length = k) (hn : kept.length ≤ k)
    (hc : separates goal rows (z :: kept) = true)
    (ht : next (k - kept.length) (z :: kept) = true) :
    dispatch goal rows extra next a b r = true := by
  apply List.any_eq_true.mpr
  refine ⟨z, List.mem_toFinset.mp hz, ?_⟩
  rw [Bool.and_eq_true]
  refine ⟨by simpa using hnew, ?_⟩
  apply List.any_eq_true.mpr
  refine ⟨kept, hk, ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨⟨by omega, hc⟩, by simpa only [he] using ht⟩

set_option maxRecDepth 100000 in
lemma optimized_complete {goal g : (BitVec width)} (hg : g = goal ∨ g = ~~~goal) (rows : List (Fin width)) (n : ℕ) (ws : List (BitVec width)) (extra : ℕ) (hn : ws.Nodup)
    (room : extra + ws.length = n + 1) (h : live basicOps g n ws.toFinset) :
    optimized goal rows n extra ws = true := by
  induction n generalizing ws extra with
  | zero => rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn h]
  | succ k ih =>
    rcases first_live h with done | ⟨a, ha, b, hb, hab, z, hz, hout, needed, hs, tail⟩
    · rcases hg with rfl | rfl <;> simp [optimized, singleton_list hn done]
    · obtain ⟨r, hm, hp⟩ := pick_two (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
      have go {a b : (BitVec width)} (perm : ws.Perm (a :: b :: r))
          (hset : ws.toFinset = insert a (insert b needed)) (hop : z ∈ basicOps a b) :
          dispatch goal rows extra (optimized goal rows k) a b r = true := by
        obtain ⟨kept, hk, hnk, hfin⟩ := recover_kept perm hn hset
        have hznew : z ∉ kept := by
          intro hu
          apply hout
          rw [hset]
          exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (hfin ▸ (List.mem_toFinset.mpr hu)))
        have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hznew, hnk⟩
        have hl : live basicOps g k (z :: kept).toFinset := by
          simpa [hfin] using tail
        have hc := live_card hl
        rw [List.toFinset_card_of_nodup hnd, List.length_cons] at hc
        have len := perm.length_eq
        simp only [List.length_cons] at len
        apply dispatch_complete (k := k) (extra := extra) (optimized goal rows k) hop (by
          intro hz
          exact hout (List.mem_toFinset.mpr (perm.mem_iff.mpr hz))) hk (by omega) (by omega) (separates_complete hg rows hl)
        apply ih _ _ hnd _ hl
        simp; omega
      simp only [optimized, Bool.or_eq_true, List.any_eq_true]
      right
      rcases hm with direct | swap
      · exact ⟨(a, b, r), direct, go hp hs hz⟩
      · exact ⟨(b, a, r), swap, go (hp.trans (.swap _ _ _)) (by rw [hs, Finset.insert_comm]) (ops_swap a b ▸ hz)⟩

def falseRows (goal : BitVec width) : List (Fin width) :=
  (List.finRange width).filter (fun j => !goal[j.val])

def search (goal : BitVec width) (n : ℕ) (inputs : List (BitVec width)) : Bool :=
  let rows := falseRows goal
  inputs.sublists.any fun ws =>
    decide (ws.length ≤ n+1) && separates goal rows ws && optimized goal rows n (n+1-ws.length) ws

set_option maxRecDepth 100000 in
lemma search_complete {goal g : (BitVec width)} (hg : g = goal ∨ g = ~~~goal) (n : ℕ) (inputs : List (BitVec width))
    (hn : inputs.Nodup) (h : build basicOps g n inputs.toFinset) : search goal n inputs = true := by
  classical
  obtain ⟨s,hs,hl⟩ := compress h
  let ws := inputs.filter (· ∈ s)
  have eq : ws.toFinset = s := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq, and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hs hw)
  have hnd : ws.Nodup := hn.filter _
  have hl' : live basicOps g n ws.toFinset := eq.symm ▸ hl
  have sz := live_card hl'
  rw [List.toFinset_card_of_nodup hnd] at sz
  exact List.any_eq_true.mpr ⟨ws,List.mem_sublists.mpr (List.filter_sublist ..),
    by simp [sz, separates_complete hg (falseRows goal) hl', optimized_complete hg (falseRows goal) n ws _ hnd (by omega : n+1-ws.length+ws.length=n+1) hl']⟩

lemma no_build {goal g : BitVec width} (hg : g = goal ∨ g = ~~~goal)
    (n : Nat) (inputs : List (BitVec width)) (hn : inputs.Nodup)
    (rejected : search goal n inputs = false) :
    ¬ build basicOps g n inputs.toFinset := by
  intro h
  have found := search_complete hg n inputs hn h
  rw [rejected] at found
  contradiction

end SearchKernel

namespace PNMasks

def lowMasks : List Nat := [
  59923104495410530257643506359634157787265899298076885757810027052577558601833654377569492440802512007040037959957131119219596589604805540830949143546491374792589297808288495092100739867082031373151027650695001922946050227447487627157971036846942412387783503561528766079982415312826572101611785443208074712405,
  35953862697246318154586103815780494672359539578846131454686016231546535161100192626541695464481507204224022775974278671531757953762883324498569486127894824875553578684973097055260443920249218823890616590417001153767630136468492576294782622108165447432670102136917259647989449187695943260967071265924844827443,
  10574665499190093574878265828170733727164570464366509251378240068101922106205939007806381018965149177712947875286552550450517045224377448381932201802322007316339287848521499133900130564779182007026651938357941515814008863667203698910230182972989837480197088863799194014114543878734100959107962137036719066895,
  699491492164325255925799685131916238761858746670158199507510043415302240488330595847114697752558505918755306925569623959761827894219519931878783776807292312753960674804924067222965835024303868169078143782431929061627045456585458682777872025450689638767900819784382483423919244896808234649164810621105930495,
  2743020179230535281946541939345750848555742525508196244463891865018732560317087494586393599377565894397365059124943060525486210366883083181910179450378780297812958991483673120165741788626975511839923752263378027203536180819116878732226270817108308850929253867045887029310881577406346282326553799069597695,
  41855804958468253215416862131907979778454107725009450118155365586182407620204276291770907358880301160328046586258184810029483623519757063820280685745923183539846145986816692000600865017772938381340388341514537443249396336985068988168808660090905282896115730467361995897392102061092763730264872452095,
  9745314011399999079825087856739523064552525976596965881551925397018201298194122315297074087275581256833590487601395744005744951780045343217449061696331431509203394542567385587901876228620663761300800549174547043425925390537456083938846363324592488964804017437595582105683670264434074320895,
  528294531135665246352339784916516606517294807943820813192811729538211400001472535897918181471736777028254044331895631613250787768007518677792952317086889741124906620767309129894662251090542585738100845990744019557890744873615362666431441255911497635040213580733791338495,
  1552518092300708935148979488462502555256886017116696611139052038026050952686363478522948466231546903925489524851003593840350987650737090830000565511011107708019742339038878425693560262461319812044393910951468561638530421117939613695,
  13407807929942597099574024998205846127479365820592393377723561443721764030073546976801874298166903427690031858186486050853753882811946569946433649006084095]

def lowMask (i : Nat) : Nat := lowMasks[i]?.getD 0

set_option maxRecDepth 10000 in
set_option maxHeartbeats 10000000 in
lemma lowMask_bits : ∀ (i : Fin 10) (x : Fin 1024),
    (lowMask i.val).testBit x.val = !(x.val.testBit i.val) := by
  decide +kernel

set_option maxRecDepth 10000 in
lemma lowMask_bound : ∀ i : Fin 10, lowMask i.val < 2^1024 := by
  decide

end PNMasks

namespace PnProjection

def delBit (i x : Nat) : Nat :=
  x % 2^i + (x / 2^(i+1)) * 2^i

def insBit (i : Nat) (b : Bool) (y : Nat) : Nat :=
  y % 2^i + (if b then 2^i else 0) + (y / 2^i) * 2^(i+1)

lemma testBit_delBit (i x j : Nat) :
    (delBit i x).testBit j = x.testBit (if j < i then j else j+1) := by
  have form : delBit i x = 2^i * (x / 2^(i+1)) + x % 2^i := by
    simp [delBit, Nat.add_comm, Nat.mul_comm]
  rw [form, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _))]
  by_cases h : j < i
  · simp [h]
  · simp only [h, ite_false, Nat.testBit_div_two_pow]
    congr 1
    omega

lemma testBit_cons (b : Bool) (x j : Nat) :
    (2*x + b.toNat).testBit j = if j = 0 then b else x.testBit (j-1) := by
  have hb : b.toNat < 2^1 := by cases b <;> decide
  change (2^1*x + b.toNat).testBit j = _
  rw [Nat.testBit_two_pow_mul_add _ hb]
  by_cases h : j = 0
  · subst j
    cases b <;> simp
  · have hj : ¬ j < 1 := by omega
    simp [h, hj]

lemma insBit_form (i : Nat) (b : Bool) (y : Nat) :
    insBit i b y = 2^i * (2*(y / 2^i) + b.toNat) + y % 2^i := by
  cases b <;> simp [insBit, Nat.pow_succ] <;> ring

lemma testBit_insBit (i : Nat) (b : Bool) (y j : Nat) :
    (insBit i b y).testBit j =
      if j < i then y.testBit j else if j = i then b else y.testBit (j-1) := by
  rw [insBit_form, Nat.testBit_two_pow_mul_add _ (Nat.mod_lt _ (Nat.two_pow_pos _))]
  by_cases h : j < i
  · simp [h]
  · simp only [h, ite_false, testBit_cons, Nat.testBit_div_two_pow]
    by_cases e : j = i
    · subst j
      simp
    · have he : j-i ≠ 0 := by omega
      simp only [e, he, ite_false]
      congr 1
      omega

lemma delBit_insBit (i : Nat) (b : Bool) (y : Nat) :
    delBit i (insBit i b y) = y := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_delBit]
  by_cases h : j < i
  · simp [h, testBit_insBit]
  · have hlt : ¬ j+1 < i := by omega
    have hne : j+1 ≠ i := by omega
    simp [h, testBit_insBit, hlt, hne]

lemma insBit_delBit (i x : Nat) :
    insBit i (x.testBit i) (delBit i x) = x := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_insBit]
  by_cases h : j < i
  · simp [h, testBit_delBit]
  · by_cases e : j = i
    · simp [h, e]
    · have hlt : ¬ j-1 < i := by omega
      have back : j-1+1 = j := by omega
      simp [h, e, testBit_delBit, hlt, back]

lemma delBit_eq_iff (i x y : Nat) :
    delBit i x = y ↔ x = insBit i false y ∨ x = insBit i true y := by
  constructor
  · intro h
    have inverse := insBit_delBit i x
    rw [h] at inverse
    cases bit : x.testBit i
    · exact Or.inl (by simpa [bit] using inverse.symm)
    · exact Or.inr (by simpa [bit] using inverse.symm)
  · rintro (rfl | rfl) <;> exact delBit_insBit ..

lemma insBit_false_ne_true (i y : Nat) : insBit i false y ≠ insBit i true y := by
  intro h
  have bit := congrArg (fun x : Nat => x.testBit i) h
  simpa [testBit_insBit] using bit

lemma delBit_lt {i x m : Nat} (hi : i < m) (hx : x < 2^m) :
    delBit i x < 2^(m-1) := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [testBit_delBit, if_neg (by omega : ¬ (j < i))]
  apply Nat.testBit_lt_two_pow
  exact lt_of_lt_of_le hx (Nat.pow_le_pow_right (by decide) (by omega))

lemma insBit_lt {i y m : Nat} (hi : i ≤ m) (hy : y < 2^m) (b : Bool) :
    insBit i b y < 2^(m+1) := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  rw [testBit_insBit, if_neg (by omega : ¬ (j < i)), if_neg (by omega : j ≠ i)]
  apply Nat.testBit_lt_two_pow
  exact lt_of_lt_of_le hy (Nat.pow_le_pow_right (by decide) (by omega))

end PnProjection

namespace PnProjection

lemma insBit_adjacent (i : Nat) (b c : Bool) (y : Nat) :
    insBit (i+1) c (insBit i b y) = insBit i b (insBit i c y) := by
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases h : j < i
  · have h' : j < i+1 := by omega
    simp [testBit_insBit, h, h']
  · by_cases e : j = i
    · subst j
      simp [testBit_insBit]
    · by_cases e' : j = i+1
      · subst j
        simp [testBit_insBit]
      · have h' : ¬ (j < i+1) := by omega
        have hs : ¬ (j-1 < i) := by omega
        have hse : j-1 ≠ i := by omega
        simp [testBit_insBit, h, h', e, e', hs, hse]

lemma insBit_true_add_false (i y : Nat) :
    insBit i true y = insBit i false y + 2^i := by
  simp [insBit]
  omega

lemma hole_swap_insert (i : Nat) (b : Bool) (y : Nat) :
    insBit i false (insBit i b y) =
      insBit (i+1) false (insBit i b y) + (if b then 2^i else 0) := by
  cases b
  · simpa using (insBit_adjacent i false false y).symm
  · simp only [Bool.true_eq, ite_true]
    calc
      insBit i false (insBit i true y) = insBit (i+1) true (insBit i false y) :=
        (insBit_adjacent i false true y).symm
      _ = insBit (i+1) false (insBit i false y) + 2^(i+1) := insBit_true_add_false ..
      _ = insBit i false (insBit i false y) + 2^(i+1) := by rw [insBit_adjacent]
      _ = (insBit i false (insBit i false y) + 2^i) + 2^i := by rw [Nat.pow_succ]; omega
      _ = insBit i true (insBit i false y) + 2^i := by rw [insBit_true_add_false]
      _ = insBit (i+1) false (insBit i true y) + 2^i := by rw [insBit_adjacent]

lemma hole_swap (i y : Nat) :
    insBit i false y = insBit (i+1) false y + (if y.testBit i then 2^i else 0) := by
  have h := hole_swap_insert i (y.testBit i) (delBit i y)
  simpa only [insBit_delBit] using h

lemma hole_move {i x : Nat} (hole : x.testBit (i+1) = false) :
    insBit i false (delBit (i+1) x) = x + (if x.testBit i then 2^i else 0) := by
  have back : insBit (i+1) false (delBit (i+1) x) = x := by
    simpa [hole] using insBit_delBit (i+1) x
  have bit : (delBit (i+1) x).testBit i = x.testBit i := by simp [testBit_delBit]
  rw [hole_swap, back, bit]

lemma hole_move_false {i x : Nat} (hole : x.testBit (i+1) = false)
    (bit : x.testBit i = false) : delBit i x = delBit (i+1) x := by
  have move := hole_move hole
  simp only [bit, Bool.false_eq_true, ite_false, Nat.add_zero] at move
  calc
    delBit i x = delBit i (insBit i false (delBit (i+1) x)) := congrArg (delBit i) move.symm
    _ = delBit (i+1) x := delBit_insBit ..

lemma hole_move_true {i x : Nat} (hole : x.testBit (i+1) = false)
    (bit : x.testBit i = true) : delBit i (x+2^i) = delBit (i+1) x := by
  have move := hole_move hole
  simp only [bit, ite_true] at move
  rw [← move, delBit_insBit]

lemma add_pow_bit_false {i x : Nat} (bit : x.testBit i = false) :
    (x+2^i).testBit i = true := by
  rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, bit]
  rfl

lemma add_pow_bit_true {i x : Nat} (bit : x.testBit i = true) :
    (x+2^i).testBit i = false := by
  rw [Nat.add_comm, Nat.testBit_two_pow_add_eq, bit]
  rfl

lemma hole_move_add {i x : Nat} (hole : x.testBit (i+1) = false) :
    x+2^i = insBit i (!(x.testBit i)) (delBit (i+1) x) := by
  have move := hole_move hole
  cases bit : x.testBit i
  · simp only [bit, Bool.false_eq_true, ite_false, Nat.add_zero] at move
    simp only [Bool.not_false]
    rw [insBit_true_add_false, move]
  · simp only [bit, ite_true] at move
    exact move.symm

lemma hole_add_lt {i x m : Nat} (hi : i+1 < m) (hx : x < 2^m)
    (hole : x.testBit (i+1) = false) : x+2^i < 2^m := by
  rw [hole_move_add hole]
  have bound := insBit_lt (by omega : i ≤ m-1) (delBit_lt hi hx) (!(x.testBit i))
  simpa only [show m-1+1 = m by omega] using bound

lemma hole_move_1024 (j : Nat) (hj : j < 9) (x : Nat) (hx : x < 1024)
    (hole : x.testBit (j+1) = false) :
    x+2^j < 1024 ∧
    (x+2^j).testBit j = !(x.testBit j) ∧
    (if x.testBit j then delBit j (x+2^j) else delBit j x) = delBit (j+1) x := by
  refine ⟨hole_add_lt (m := 10) (by omega) hx hole, ?_, ?_⟩
  · simpa only [Nat.add_comm] using Nat.testBit_two_pow_add_eq x j
  · cases bit : x.testBit j
    · simpa only [Bool.false_eq_true, ite_false] using hole_move_false hole bit
    · simpa only [ite_true] using hole_move_true hole bit

end PnProjection

namespace PnProjection

def bitmapStage (mask shift S : Nat) : Nat :=
  (S ||| (S >>> shift)) &&& mask

lemma testBit_bitmapStage (mask shift S y : Nat) :
    (bitmapStage mask shift S).testBit y =
      ((S.testBit y || S.testBit (y + shift)) && mask.testBit y) := by
  simp [bitmapStage, Nat.testBit_shiftRight, Nat.add_comm]

def packBits : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n + 1, f => 2 * packBits n (fun y => f (y + 1)) + (f 0).toNat

lemma testBit_packBits (n : Nat) (f : Nat → Bool) (y : Nat) :
    (packBits n f).testBit y = if y < n then f y else false := by
  induction n generalizing f y with
  | zero => simp [packBits]
  | succ n ih =>
    rw [packBits]
    have hb : (f 0).toNat < 2^1 := by cases f 0 <;> decide
    change (2^1 * packBits n (fun y => f (y+1)) + (f 0).toNat).testBit y = _
    rw [Nat.testBit_two_pow_mul_add _ hb]
    cases y with
    | zero => cases h : f 0 <;> simp [h]
    | succ y => simpa [ih]

lemma packBits_lt (n : Nat) (f : Nat → Bool) : packBits n f < 2^n := by
  apply Nat.lt_pow_two_of_testBit
  intro j hj
  simp [testBit_packBits, Nat.not_lt.mpr hj]

def dropBitmapSimple (m i S : Nat) : Nat :=
  packBits (2^(m-1)) (fun y =>
    S.testBit (insBit i false y) || S.testBit (insBit i true y))

lemma testBit_dropBitmapSimple (m i S y : Nat) :
    (dropBitmapSimple m i S).testBit y =
      if y < 2^(m-1) then
        S.testBit (insBit i false y) || S.testBit (insBit i true y)
      else false := by
  exact testBit_packBits ..

lemma dropBitmapSimple_lt (m i S : Nat) : dropBitmapSimple m i S < 2^(2^(m-1)) :=
  packBits_lt ..

lemma testBit_dropBitmapSimple_iff (m i S y : Nat) :
    (dropBitmapSimple m i S).testBit y = true ↔
      y < 2^(m-1) ∧ ∃ x, S.testBit x = true ∧ delBit i x = y := by
  rw [testBit_dropBitmapSimple]
  by_cases hy : y < 2^(m-1)
  · simp only [hy, if_pos, true_and, Bool.or_eq_true]
    constructor
    · rintro (hf | ht)
      · exact ⟨insBit i false y, hf, delBit_insBit ..⟩
      · exact ⟨insBit i true y, ht, delBit_insBit ..⟩
    · rintro ⟨x, hx, hxy⟩
      rcases (delBit_eq_iff i x y).mp hxy with rfl | rfl
      · exact Or.inl hx
      · exact Or.inr hx
  · simp [hy]

lemma testBit_dropBitmapSimple_image {m i S : Nat} (hi : i < m)
    (hS : S < 2^(2^m)) (y : Nat) :
    (dropBitmapSimple m i S).testBit y = true ↔
      ∃ x, S.testBit x = true ∧ delBit i x = y := by
  rw [testBit_dropBitmapSimple_iff]
  constructor
  · exact And.right
  · rintro ⟨x, hx, rfl⟩
    refine ⟨delBit_lt hi ?_, x, hx, rfl⟩
    by_contra hn
    have hz : S.testBit x = false := Nat.testBit_lt_two_pow
      (lt_of_lt_of_le hS (Nat.pow_le_pow_right (by decide) (by omega)))
    simp [hx] at hz

def deletePattern (i S y : Nat) : Bool :=
  S.testBit (insBit i false y) || S.testBit (insBit i true y)

def MaskSpec (j mask : Nat) : Prop :=
  ∀ x, mask.testBit x = if x < 1024 then !(x.testBit j) else false

def HoleSpec (j T : Nat) (f : Nat → Bool) : Prop :=
  ∀ x, T.testBit x =
    if x < 1024 then if x.testBit j then false else f (delBit j x) else false

lemma lowMask_spec {j : Nat} (hj : j < 10) :
    MaskSpec j (PNMasks.lowMask j) := by
  intro x
  by_cases hx : x < 1024
  · exact (PNMasks.lowMask_bits ⟨j, hj⟩ ⟨x, hx⟩).trans (by simp [hx])
  · simp only [hx, if_false]
    exact Nat.testBit_lt_two_pow (lt_of_lt_of_le
      (PNMasks.lowMask_bound ⟨j, hj⟩)
      (Nat.pow_le_pow_right (by decide) (by omega)))

lemma insBit_true_eq_false_add (i y : Nat) :
    insBit i true y = insBit i false y + 2^i := by
  simp only [insBit, Bool.false_eq_true, if_false, if_true]
  omega

lemma bitmapStage_first (i S mask : Nat) (hm : MaskSpec i mask) :
    HoleSpec i (bitmapStage mask (2^i) S) (deletePattern i S) := by
  intro x
  rw [testBit_bitmapStage, hm]
  by_cases hx : x < 1024
  · simp only [hx, if_pos]
    cases hb : x.testBit i with
    | true => simp [hb]
    | false =>
      have he : insBit i false (delBit i x) = x := by
        simpa [hb] using insBit_delBit i x
      simp [hb, deletePattern, insBit_true_eq_false_add, he]
  · simp [hx]

lemma bitmapStage_move_aux (j T mask : Nat) (f : Nat → Bool)
    (hm : MaskSpec (j+1) mask) (hT : HoleSpec j T f)
    (move : ∀ x, x < 1024 → x.testBit (j+1) = false →
      x + 2^j < 1024 ∧
      (x + 2^j).testBit j = !(x.testBit j) ∧
      (if x.testBit j then delBit j (x + 2^j) else delBit j x) = delBit (j+1) x) :
    HoleSpec (j+1) (bitmapStage mask (2^j) T) f := by
  intro x
  rw [testBit_bitmapStage, hm]
  by_cases hx : x < 1024
  · simp only [hx, if_pos]
    cases hh : x.testBit (j+1) with
    | true => simp [hh]
    | false =>
      rcases move x hx hh with ⟨hxshift, hflip, hdel⟩
      rw [hT x, hT (x + 2^j)]
      cases hb : x.testBit j <;> simp_all
  · simp [hx]

def compressHoles (mask : Nat → Nat) : Nat → Nat → Nat → Nat
  | 0, _, T => T
  | n+1, j, T => compressHoles mask n (j+1) (bitmapStage (mask (j+1)) (2^j) T)

lemma compressHoles_spec_aux (mask : Nat → Nat) (f : Nat → Bool)
    (step : ∀ j T, j < 9 → HoleSpec j T f →
      HoleSpec (j+1) (bitmapStage (mask (j+1)) (2^j) T) f)
    (n j T : Nat) (hj : j + n ≤ 9) (hT : HoleSpec j T f) :
    HoleSpec (j+n) (compressHoles mask n j T) f := by
  induction n generalizing j T with
  | zero => simpa [compressHoles] using hT
  | succ n ih =>
    have hnext := step j T (by omega) hT
    have hrest := ih (j+1) _ (by omega) hnext
    simpa [compressHoles, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hrest

lemma holeSpec_final {T : Nat} {f : Nat → Bool} (h : HoleSpec 9 T f) :
    T = packBits 512 f := by
  apply Nat.eq_of_testBit_eq
  intro x
  rw [h, testBit_packBits]
  by_cases hx : x < 512
  · have hbit : x.testBit 9 = false := Nat.testBit_lt_two_pow (by omega)
    have hdel : delBit 9 x = x := by
      simp [delBit, Nat.mod_eq_of_lt hx, Nat.div_eq_of_lt (show x < 1024 by omega)]
    simp [hx, show x < 1024 by omega, hbit, hdel]
  · by_cases hxx : x < 1024
    · have hbit : x.testBit 9 = true :=
        Nat.testBit_of_two_pow_le_and_two_pow_add_one_gt (by omega) (by omega)
      simp [hx, hxx, hbit]
    · simp [hx, hxx]

def dropBitmap (i S : Nat) : Nat :=
  compressHoles PNMasks.lowMask (9-i) i
    (bitmapStage (PNMasks.lowMask i) (2^i) S)

lemma dropBitmap_eq_simple_aux {i : Nat} (hi : i < 10) (S : Nat)
    (move : ∀ j x, j < 9 → x < 1024 → x.testBit (j+1) = false →
      x + 2^j < 1024 ∧
      (x + 2^j).testBit j = !(x.testBit j) ∧
      (if x.testBit j then delBit j (x + 2^j) else delBit j x) = delBit (j+1) x) :
    dropBitmap i S = dropBitmapSimple 10 i S := by
  have hfirst := bitmapStage_first i S (PNMasks.lowMask i) (lowMask_spec hi)
  have hfull := compressHoles_spec_aux PNMasks.lowMask (deletePattern i S)
    (fun j T hj hT => bitmapStage_move_aux j T _ _ (lowMask_spec (by omega)) hT
      (fun x hx hh => move j x hj hx hh))
    (9-i) i _ (by omega) hfirst
  have hi9 : i + (9-i) = 9 := by omega
  rw [hi9] at hfull
  exact holeSpec_final hfull

lemma dropBitmap_eq_simple {i : Nat} (hi : i < 10) (S : Nat) :
    dropBitmap i S = dropBitmapSimple 10 i S := by
  exact dropBitmap_eq_simple_aux hi S (fun j x hj hx hh => hole_move_1024 j hj x hx hh)

lemma testBit_dropBitmap {i : Nat} (hi : i < 10) (S y : Nat) :
    (dropBitmap i S).testBit y =
      if y < 512 then
        S.testBit (insBit i false y) || S.testBit (insBit i true y)
      else false := by
  rw [dropBitmap_eq_simple hi S]
  exact testBit_dropBitmapSimple 10 i S y

lemma testBit_dropBitmap_image {i S : Nat} (hi : i < 10) (hS : S < 2^1024) (y : Nat) :
    (dropBitmap i S).testBit y = true ↔
      ∃ x, S.testBit x = true ∧ delBit i x = y := by
  rw [dropBitmap_eq_simple hi S]
  exact testBit_dropBitmapSimple_image hi hS y

lemma dropBitmap_lt {m i S : Nat} (hi : i < m) (hm : m ≤ 10) (hS : S < 2^(2^m)) :
    dropBitmap i S < 2^(2^(m-1)) := by
  have hi10 : i < 10 := by omega
  have hS1024 : S < 2^1024 := lt_of_lt_of_le hS
    (Nat.pow_le_pow_right (by decide) (by exact Nat.pow_le_pow_right (by decide) hm))
  apply Nat.lt_pow_two_of_testBit
  intro y hy
  cases hb : (dropBitmap i S).testBit y with
  | false => rfl
  | true =>
    rcases (testBit_dropBitmap_image hi10 hS1024 y).mp hb with ⟨x, hx, hxy⟩
    have hxb : x < 2^m := by
      by_contra hn
      have hz : S.testBit x = false := Nat.testBit_lt_two_pow
        (lt_of_lt_of_le hS (Nat.pow_le_pow_right (by decide) (by omega)))
      simp [hx] at hz
    have hlt := delBit_lt hi hxb
    omega

end PnProjection

namespace PnProjection

lemma compressHoles_eq_foldl (mask : Nat → Nat) (n j S : Nat) :
    compressHoles mask n j S =
      (List.range n).foldl (fun T offset =>
        bitmapStage (mask (j + offset + 1)) (2^(j + offset)) T) S := by
  induction n generalizing j S with
  | zero => rfl
  | succ n ih =>
    rw [compressHoles, ih, List.range_succ_eq_map, List.foldl_cons, List.foldl_map]
    simp only [Nat.add_zero, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

def projectPatternBits (i S : Nat) : Nat :=
  let d := 1 <<< i
  let T := (S &&& PNMasks.lowMask i) ||| ((S >>> d) &&& PNMasks.lowMask i)
  (List.range (9-i)).foldl (fun T offset =>
    let j := i + 1 + offset
    (T ||| (T >>> (1 <<< (j-1)))) &&& PNMasks.lowMask j) T

lemma mask_distribute (S d mask : Nat) :
    (S &&& mask) ||| ((S >>> d) &&& mask) = bitmapStage mask d S := by
  apply Nat.eq_of_testBit_eq
  intro x
  simp only [bitmapStage, Nat.testBit_or, Nat.testBit_and]
  cases S.testBit x <;> cases (S >>> d).testBit x <;> cases mask.testBit x <;> rfl

lemma projectPatternBits_eq_dropBitmap (i S : Nat) :
    projectPatternBits i S = dropBitmap i S := by
  unfold projectPatternBits dropBitmap
  rw [compressHoles_eq_foldl]
  simp only [Nat.one_shiftLeft, mask_distribute]
  congr 1
  funext T offset
  dsimp only [bitmapStage]
  rw [show i + 1 + offset - 1 = i + offset by omega,
    show i + 1 + offset = i + offset + 1 by omega]

lemma lowMask_getBang : ∀ i : Fin 10,
    PNMasks.lowMask i.val = PNMasks.lowMasks[i.val]! := by
  decide

end PnProjection

namespace PNPlanes

def allPatterns : Nat := 2^1024 - 1

def highMask (i : Nat) : Nat := PNMasks.lowMask i <<< (1 <<< i)

set_option maxRecDepth 10000 in
lemma highMask_eq : ∀ i : Fin 10,
    highMask i.val = allPatterns ^^^ PNMasks.lowMask i.val := by
  decide +kernel

lemma highMask_bits (i : Fin 10) (x : Fin 1024) :
    (highMask i.val).testBit x.val = x.val.testBit i.val := by
  rw [highMask_eq i]
  simp [Nat.testBit_xor, allPatterns, x.isLt, PNMasks.lowMask_bits]

def gateMask (i j : Nat) (d : Fin 4) : Nat :=
  match d.val with
  | 0 => highMask i &&& highMask j
  | 1 => highMask i ||| highMask j
  | 2 => highMask i &&& PNMasks.lowMask j
  | _ => highMask j &&& PNMasks.lowMask i

lemma gateMask_bits (i j : Fin 10) (d : Fin 4) (x : Fin 1024) :
    (gateMask i.val j.val d).testBit x.val =
      ChromGate.eval d (x.val.testBit i.val) (x.val.testBit j.val) := by
  fin_cases d <;> simp [gateMask, ChromGate.eval, Nat.testBit_and, Nat.testBit_or,
    highMask_bits, PNMasks.lowMask_bits]

def planeOne (s gate : Nat) : Nat := s &&& gate
def planeZero (s gate : Nat) : Nat := s &&& (allPatterns ^^^ gate)

lemma planeOne_le (s gate : Nat) : planeOne s gate ≤ s := Nat.and_le_left
lemma planeZero_le (s gate : Nat) : planeZero s gate ≤ s := Nat.and_le_left

lemma testBit_planeOne (s gate x : Nat) :
    (planeOne s gate).testBit x = (s.testBit x && gate.testBit x) := by
  simp [planeOne, Nat.testBit_and]

lemma testBit_planeZero {s : Nat} (hs : s < 2^1024) (gate x : Nat) :
    (planeZero s gate).testBit x = (s.testBit x && !(gate.testBit x)) := by
  by_cases hx : x < 1024
  · simp [planeZero, allPatterns, Nat.testBit_and, Nat.testBit_xor, hx]
  · have powle : 2^1024 ≤ 2^x := Nat.pow_le_pow_of_le (by decide) (by omega)
    have no : s.testBit x = false := Nat.testBit_lt_two_pow (hs.trans_le powle)
    simp [planeZero, Nat.testBit_and, no]

lemma planeZero_eq_xor {s : Nat} (hs : s < 2^1024) (gate : Nat) :
    planeZero s gate = s ^^^ (s &&& gate) := by
  apply Nat.eq_of_testBit_eq
  intro x
  rw [testBit_planeZero hs, Nat.testBit_xor, Nat.testBit_and]
  cases s.testBit x <;> cases gate.testBit x <;> rfl

end PNPlanes

namespace PnProjection

def joinPlanes (q a b : Nat) : Nat := a ||| (b <<< q)

def appendPlanes (n a b : Nat) : Nat := joinPlanes (2^n) a b

lemma bitIndex_lt {x q y : Nat} (bound : x < 2^q) (bit : x.testBit y = true) : y < q := by
  by_contra! h
  have zero := Nat.testBit_lt_two_pow (lt_of_lt_of_le bound (Nat.pow_le_pow_right (by decide) h))
  rw [zero] at bit
  contradiction

lemma testBit_joinPlanes (q a b x : Nat) :
    (joinPlanes q a b).testBit x = (a.testBit x || (decide (q ≤ x) && b.testBit (x-q))) := by
  simp [joinPlanes, Nat.testBit_shiftLeft]

lemma joinPlanes_image {q a b x : Nat} (ha : a < 2^q) (hb : b < 2^q) :
    (joinPlanes q a b).testBit x = true ↔
      (∃ y < q, a.testBit y = true ∧ x = y) ∨
      (∃ y < q, b.testBit y = true ∧ x = y+q) := by
  rw [testBit_joinPlanes, Bool.or_eq_true]
  constructor
  · rintro (h | h)
    · exact Or.inl ⟨x, bitIndex_lt ha h, h, rfl⟩
    · have h' : q ≤ x ∧ b.testBit (x-q) = true := by
        simpa only [Bool.and_eq_true, decide_eq_true_eq] using h
      obtain ⟨hle', hbit⟩ := h'
      exact Or.inr ⟨x-q, bitIndex_lt hb hbit, hbit, by omega⟩
  · rintro (⟨y, hy, hbit, rfl⟩ | ⟨y, hy, hbit, rfl⟩)
    · exact Or.inl hbit
    · exact Or.inr (by simp [hbit])

lemma joinPlanes_lt {q a b : Nat} (ha : a < 2^q) (hb : b < 2^q) :
    joinPlanes q a b < 2^(2*q) := by
  apply Nat.lt_pow_two_of_testBit
  intro x hx
  rw [testBit_joinPlanes]
  have za : a.testBit x = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le ha (Nat.pow_le_pow_right (by decide) (by omega)))
  have zb : b.testBit (x-q) = false :=
    Nat.testBit_lt_two_pow (lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega)))
  simp [za, zb]

lemma insBit_top (n : Nat) (flag : Bool) {y : Nat} (hy : y < 2^n) :
    insBit n flag y = y + (if flag then 2^n else 0) := by
  simp [insBit, Nat.mod_eq_of_lt hy, Nat.div_eq_of_lt hy]

lemma appendPlanes_image {n a b x : Nat} (ha : a < 2^(2^n)) (hb : b < 2^(2^n)) :
    (appendPlanes n a b).testBit x = true ↔
      ∃ (flag : Bool) (y : Nat), y < 2^n ∧
        (if flag then b else a).testBit y = true ∧ x = insBit n flag y := by
  rw [appendPlanes, joinPlanes_image ha hb]
  constructor
  · rintro (⟨y, hy, hbit, eq⟩ | ⟨y, hy, hbit, eq⟩)
    · exact ⟨false, y, hy, hbit, by simpa [insBit_top n false hy] using eq⟩
    · exact ⟨true, y, hy, hbit, by simpa [insBit_top n true hy] using eq⟩
  · rintro ⟨flag, y, hy, hbit, eq⟩
    cases flag
    · exact Or.inl ⟨y, hy, hbit, by simpa [insBit_top n false hy] using eq⟩
    · exact Or.inr ⟨y, hy, hbit, by simpa [insBit_top n true hy] using eq⟩

lemma appendPlanes_image_unbounded {n a b x : Nat}
    (ha : a < 2^(2^n)) (hb : b < 2^(2^n)) :
    (appendPlanes n a b).testBit x = true ↔
      ∃ (flag : Bool) (y : Nat),
        (if flag then b else a).testBit y = true ∧ x = insBit n flag y := by
  rw [appendPlanes_image ha hb]
  constructor
  · rintro ⟨flag, y, hy, hbit, eq⟩
    exact ⟨flag, y, hbit, eq⟩
  · rintro ⟨flag, y, hbit, eq⟩
    refine ⟨flag, y, ?_, hbit, eq⟩
    cases flag
    · exact bitIndex_lt ha hbit
    · exact bitIndex_lt hb hbit

lemma appendPlanes_image_sum {n a b x : Nat}
    (ha : a < 2^(2^n)) (hb : b < 2^(2^n)) :
    (appendPlanes n a b).testBit x = true ↔
      ∃ (flag : Bool) (y : Nat), y < 2^n ∧
        (if flag then b else a).testBit y = true ∧ x = y + (if flag then 2^n else 0) := by
  rw [appendPlanes_image ha hb]
  constructor
  · rintro ⟨flag, y, hy, hbit, eq⟩
    exact ⟨flag, y, hy, hbit, by simpa only [insBit_top n flag hy] using eq⟩
  · rintro ⟨flag, y, hy, hbit, eq⟩
    exact ⟨flag, y, hy, hbit, by simpa only [insBit_top n flag hy] using eq⟩

lemma appendPlanes_lt {n a b : Nat} (ha : a < 2^(2^n)) (hb : b < 2^(2^n)) :
    appendPlanes n a b < 2^(2^(n+1)) := by
  simpa only [appendPlanes, Nat.pow_succ, Nat.mul_comm (2^n) 2] using joinPlanes_lt ha hb

end PnProjection

namespace PnTransition

open PnProjection
open PNPlanes

def keepSize (keep : Fin 4) : Nat :=
  if keep.val == 0 then 0 else if keep.val == 3 then 2 else 1

def dropPattern (i j : Nat) (keep : Fin 4) (x : Nat) : Nat :=
  let x := if keep.val &&& 2 == 0 then delBit j x else x
  if keep.val &&& 1 == 0 then delBit i x else x

def projectDropped (i j : Nat) (keep : Fin 4) (S : Nat) : Nat :=
  let S := if keep.val &&& 2 == 0 then dropBitmap j S else S
  if keep.val &&& 1 == 0 then dropBitmap i S else S

lemma bound_1024 {m S : Nat} (hm : m ≤ 10) (hS : S < 2^(2^m)) : S < 2^1024 :=
  lt_of_lt_of_le hS (Nat.pow_le_pow_right (by decide)
    (by exact Nat.pow_le_pow_right (by decide) hm))

lemma projectDropped_image {m i j S : Nat} (hij : i < j) (hj : j < m) (hm : m ≤ 10)
    (hS : S < 2^(2^m)) (keep : Fin 4) (y : Nat) :
    (projectDropped i j keep S).testBit y = true ↔
      ∃ x, S.testBit x = true ∧ dropPattern i j keep x = y := by
  have hS1024 := bound_1024 hm hS
  have hi10 : i < 10 := by omega
  have hj10 : j < 10 := by omega
  have hdrop := dropBitmap_lt hj hm hS
  have hdrop1024 := bound_1024 (by omega : m-1 ≤ 10) hdrop
  fin_cases keep
  · simp only [projectDropped, dropPattern, Fin.val_zero, Nat.zero_and, beq_self_eq_true, ite_true]
    rw [testBit_dropBitmap_image hi10 hdrop1024]
    simp only [testBit_dropBitmap_image hj10 hS1024]
    constructor
    · rintro ⟨u, ⟨x, hx, hxu⟩, huy⟩
      exact ⟨x, hx, by simpa [hxu] using huy⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨delBit j x, ⟨x, hx, rfl⟩, hxy⟩
  · simpa [projectDropped, dropPattern] using testBit_dropBitmap_image hj10 hS1024 y
  · simpa [projectDropped, dropPattern] using testBit_dropBitmap_image hi10 hS1024 y
  · simp [projectDropped, dropPattern]

lemma projectDropped_lt {m i j S : Nat} (hij : i < j) (hj : j < m) (hm : m ≤ 10)
    (hS : S < 2^(2^m)) (keep : Fin 4) :
    projectDropped i j keep S < 2^(2^(m-2+keepSize keep)) := by
  have htwo : 2 ≤ m := by omega
  have hm1 : m-2+1 = m-1 := by omega
  have hm2 : m-2+2 = m := by omega
  fin_cases keep
  · simpa [projectDropped, keepSize, Nat.sub_sub] using
      dropBitmap_lt (by omega : i < m-1) (by omega : m-1 ≤ 10) (dropBitmap_lt hj hm hS)
  · simpa [projectDropped, keepSize, hm1] using dropBitmap_lt hj hm hS
  · simpa [projectDropped, keepSize, hm1] using dropBitmap_lt (by omega : i < m) hm hS
  · simpa [projectDropped, keepSize, hm2] using hS

lemma dropPattern_lt {m i j x : Nat} (hij : i < j) (hj : j < m)
    (hx : x < 2^m) (keep : Fin 4) :
    dropPattern i j keep x < 2^(m-2+keepSize keep) := by
  have htwo : 2 ≤ m := by omega
  have hm1 : m-2+1 = m-1 := by omega
  have hm2 : m-2+2 = m := by omega
  fin_cases keep
  · simpa [dropPattern, keepSize, Nat.sub_sub] using
      delBit_lt (by omega : i < m-1) (delBit_lt hj hx)
  · simpa [dropPattern, keepSize, hm1] using delBit_lt hj hx
  · simpa [dropPattern, keepSize, hm1] using delBit_lt (by omega : i < m) hx
  · simpa [dropPattern, keepSize, hm2] using hx

def transitionSet (m i j : Nat) (keep : Fin 4) (gate S : Nat) : Nat :=
  let zero := projectDropped i j keep (planeZero S gate)
  let one := projectDropped i j keep (planeOne S gate)
  zero ||| (one <<< (1 <<< (m-2+keepSize keep)))

lemma transitionSet_eq_appendPlanes (m i j : Nat) (keep : Fin 4) (gate S : Nat) :
    transitionSet m i j keep gate S =
      appendPlanes (m-2+keepSize keep)
        (projectDropped i j keep (planeZero S gate))
        (projectDropped i j keep (planeOne S gate)) := by
  simp [transitionSet, appendPlanes, joinPlanes, Nat.shiftLeft_eq]

lemma transitionSet_image {m i j S : Nat} (hij : i < j) (hj : j < m) (hm : m ≤ 10)
    (hS : S < 2^(2^m)) (keep : Fin 4) (gate y : Nat) :
    (transitionSet m i j keep gate S).testBit y = true ↔
      ∃ x, S.testBit x = true ∧
        y = dropPattern i j keep x + (if gate.testBit x then 2^(m-2+keepSize keep) else 0) := by
  have hS1024 := bound_1024 hm hS
  have hzero : planeZero S gate < 2^(2^m) := lt_of_le_of_lt (planeZero_le S gate) hS
  have hone : planeOne S gate < 2^(2^m) := lt_of_le_of_lt (planeOne_le S gate) hS
  rw [transitionSet_eq_appendPlanes, appendPlanes,
    joinPlanes_image (projectDropped_lt hij hj hm hzero keep) (projectDropped_lt hij hj hm hone keep)]
  constructor
  · rintro (⟨u, hu, hbit, hy⟩ | ⟨u, hu, hbit, hy⟩)
    · rcases (projectDropped_image hij hj hm hzero keep u).mp hbit with ⟨x, hx, hxu⟩
      rw [testBit_planeZero hS1024] at hx
      have hpair : S.testBit x = true ∧ gate.testBit x = false := by
        simpa using hx
      obtain ⟨hxS, hg⟩ := hpair
      exact ⟨x, hxS, by simpa [hg, hxu] using hy⟩
    · rcases (projectDropped_image hij hj hm hone keep u).mp hbit with ⟨x, hx, hxu⟩
      rw [testBit_planeOne] at hx
      have hpair : S.testBit x = true ∧ gate.testBit x = true := by
        simpa only [Bool.and_eq_true] using hx
      obtain ⟨hxS, hxgate⟩ := hpair
      exact ⟨x, hxS, by simpa [hxgate, hxu] using hy⟩
  · rintro ⟨x, hxS, hy⟩
    have hxb := bitIndex_lt hS hxS
    have hdrop := dropPattern_lt hij hj hxb keep
    cases hg : gate.testBit x with
    | false =>
      have hbit : (planeZero S gate).testBit x = true := by
        simp [testBit_planeZero hS1024, hxS, hg]
      exact Or.inl ⟨dropPattern i j keep x, hdrop,
        (projectDropped_image hij hj hm hzero keep _).mpr ⟨x, hbit, rfl⟩,
        by simpa [hg] using hy⟩
    | true =>
      have hbit : (planeOne S gate).testBit x = true := by
        simp [testBit_planeOne, hxS, hg]
      exact Or.inr ⟨dropPattern i j keep x, hdrop,
        (projectDropped_image hij hj hm hone keep _).mpr ⟨x, hbit, rfl⟩,
        by simpa [hg] using hy⟩

lemma transitionSet_lt {m i j S : Nat} (hij : i < j) (hj : j < m) (hm : m ≤ 10)
    (hS : S < 2^(2^m)) (keep : Fin 4) (gate : Nat) :
    transitionSet m i j keep gate S < 2^(2^(m-1+keepSize keep)) := by
  have hzero : planeZero S gate < 2^(2^m) := lt_of_le_of_lt (planeZero_le S gate) hS
  have hone : planeOne S gate < 2^(2^m) := lt_of_le_of_lt (planeOne_le S gate) hS
  rw [transitionSet_eq_appendPlanes]
  have h := appendPlanes_lt (projectDropped_lt hij hj hm hzero keep)
    (projectDropped_lt hij hj hm hone keep)
  have he : m-2+keepSize keep+1 = m-1+keepSize keep := by omega
  simpa [he] using h

lemma transitionSet_gate_image {m i j S : Nat} (hij : i < j) (hj : j < m) (hm : m ≤ 10)
    (hS : S < 2^(2^m)) (keep d : Fin 4) (y : Nat) :
    (transitionSet m i j keep (gateMask i j d) S).testBit y = true ↔
      ∃ x, S.testBit x = true ∧ y = dropPattern i j keep x +
        (if ChromGate.eval d (x.testBit i) (x.testBit j) then 2^(m-2+keepSize keep) else 0) := by
  rw [transitionSet_image hij hj hm hS]
  have hS1024 := bound_1024 hm hS
  constructor <;> rintro ⟨x, hx, hy⟩
  · have hg := gateMask_bits ⟨i, by omega⟩ ⟨j, by omega⟩ d ⟨x, bitIndex_lt hS1024 hx⟩
    exact ⟨x, hx, by simpa only [hg] using hy⟩
  · have hg := gateMask_bits ⟨i, by omega⟩ ⟨j, by omega⟩ d ⟨x, bitIndex_lt hS1024 hx⟩
    exact ⟨x, hx, by simpa only [hg] using hy⟩

end PnTransition

namespace PNQuotient

variable {Q : Type} {width : Nat}

def liveState (rep : Nat → Q → List (BitVec width) → Prop) (goal : BitVec width)
    (k : Nat) (s : Q) : Prop :=
  ∃ ws, ws.Nodup ∧ rep k s ws ∧ live basicOps goal k ws.toFinset

def search (done : Q → Bool) (admissible : Nat → Q → Bool)
    (children : Nat → Q → List Q) : Nat → Q → Bool
  | 0, s => done s
  | k + 1, s => done s ||
      (admissible (k + 1) s && (children (k + 1) s).any (search done admissible children k))

lemma kept_front {a b : BitVec width} {r kept : List (BitVec width)}
    (hk : kept ∈ SearchKernel.keepChoices a b r) :
    ∃ front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width))),
      kept = front ++ r := by
  simp only [SearchKernel.keepChoices, List.mem_cons, List.not_mem_nil, or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl
  · exact ⟨[], by simp, rfl⟩
  · exact ⟨[a], by simp, rfl⟩
  · exact ⟨[b], by simp, rfl⟩
  · exact ⟨[a,b], by simp, rfl⟩

lemma liveState_step {rep : Nat → Q → List (BitVec width) → Prop} {goal : BitVec width}
    {done : Q → Bool} {children : Nat → Q → List Q}
    (finish : ∀ k s, rep k s [goal] → done s = true)
    (cover : ∀ (k : Nat) (s : Q) (ws : List (BitVec width))
      (a b z : BitVec width) (r front : List (BitVec width)),
      ws.Nodup → rep (k + 1) s ws → (a, b, r) ∈ SearchKernel.pairs ws →
      front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width))) →
      z ∈ basicOps a b → z ∉ ws.toFinset →
      live basicOps goal k (z :: (front ++ r)).toFinset →
      ∃ t ∈ children (k + 1) s, ∃ ys, rep k t ys ∧ ys.Perm (z :: (front ++ r)))
    {k : Nat} {s : Q} (hs : liveState rep goal (k + 1) s) :
    done s = true ∨ ∃ t ∈ children (k + 1) s, liveState rep goal k t := by
  obtain ⟨ws, hn, hrep, hrun⟩ := hs
  rcases first_live hrun with hstop | ⟨a, ha, b, hb, hab, z, hz, hnew, U, hset, tail⟩
  · left
    exact finish (k + 1) s ((SearchKernel.singleton_list hn hstop) ▸ hrep)
  · right
    obtain ⟨r, hm, hp⟩ := SearchKernel.pick_two
      (List.mem_toFinset.mp ha) (List.mem_toFinset.mp hb) hab
    have go {a b : BitVec width} (hpair : (a, b, r) ∈ SearchKernel.pairs ws)
        (perm : ws.Perm (a :: b :: r))
        (hset : ws.toFinset = insert a (insert b U)) (hop : z ∈ basicOps a b) :
        ∃ t ∈ children (k + 1) s, liveState rep goal k t := by
      obtain ⟨kept, hk, hnk, hfin⟩ := SearchKernel.recover_kept perm hn hset
      have hzkept : z ∉ kept := by
        intro hzmem
        apply hnew
        rw [hset]
        exact Finset.mem_insert_of_mem (Finset.mem_insert_of_mem
          (hfin ▸ List.mem_toFinset.mpr hzmem))
      have hnd : (z :: kept).Nodup := List.nodup_cons.mpr ⟨hzkept, hnk⟩
      have hl : live basicOps goal k (z :: kept).toFinset := by
        simpa only [List.toFinset_cons, hfin] using tail
      obtain ⟨front, hfront, rfl⟩ := kept_front hk
      obtain ⟨t, ht, ys, htrep, hperm⟩ := cover k s ws a b z r front hn hrep hpair hfront hop hnew hl
      have heq : ys.toFinset = (z :: (front ++ r)).toFinset := by
        ext w
        simp only [List.mem_toFinset]
        exact hperm.mem_iff
      exact ⟨t, ht, ys, hperm.nodup_iff.mpr hnd, htrep, heq.symm ▸ hl⟩
    rcases hm with direct | swap
    · exact go direct hp hset hz
    · exact go swap (hp.trans (.swap _ _ _)) (by rw [hset, Finset.insert_comm])
        (SearchKernel.ops_swap a b ▸ hz)

lemma search_complete {rep : Nat → Q → List (BitVec width) → Prop} {goal : BitVec width}
    {done : Q → Bool} {admissible : Nat → Q → Bool} {children : Nat → Q → List Q}
    (finish : ∀ k s, rep k s [goal] → done s = true)
    (step : ∀ k s, liveState rep goal (k + 1) s →
      done s = true ∨ ∃ t ∈ children (k + 1) s, liveState rep goal k t)
    (allowed : ∀ k s, liveState rep goal (k + 1) s → admissible (k + 1) s = true)
    {k : Nat} {s : Q} (hs : liveState rep goal k s) :
    search done admissible children k s = true := by
  induction k generalizing s with
  | zero =>
    obtain ⟨ws, hn, hrep, hrun⟩ := hs
    exact finish 0 s ((SearchKernel.singleton_list hn hrun) ▸ hrep)
  | succ k ih =>
    rcases step k s hs with hdone | ⟨t, ht, htail⟩
    · simp only [search, hdone, Bool.true_or]
    · simp only [search, Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true]
      exact Or.inr ⟨allowed k s hs, t, ht, ih htail⟩

lemma rejected_no_liveState {rep : Nat → Q → List (BitVec width) → Prop} {goal : BitVec width}
    {done : Q → Bool} {admissible : Nat → Q → Bool} {children : Nat → Q → List Q}
    (finish : ∀ k s, rep k s [goal] → done s = true)
    (step : ∀ k s, liveState rep goal (k + 1) s →
      done s = true ∨ ∃ t ∈ children (k + 1) s, liveState rep goal k t)
    (allowed : ∀ k s, liveState rep goal (k + 1) s → admissible (k + 1) s = true)
    {k : Nat} {s : Q} (rejected : search done admissible children k s = false) :
    ¬ liveState rep goal k s := by
  intro hs
  have found := search_complete finish step allowed hs
  rw [rejected] at found
  contradiction

lemma build_represented_sublist {rep : Nat → Q → List (BitVec width) → Prop}
    {goal : BitVec width} {k : Nat} {inputs : List (BitVec width)}
    (hn : inputs.Nodup)
    (represented : ∀ ws, ws.Sublist inputs → ∃ s, rep k s ws)
    (run : build basicOps goal k inputs.toFinset) :
    ∃ s, liveState rep goal k s := by
  classical
  obtain ⟨S, hS, hlive⟩ := compress run
  let ws := inputs.filter (· ∈ S)
  have hfin : ws.toFinset = S := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq,
      and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hS hw)
  obtain ⟨s, hs⟩ := represented ws (List.filter_sublist ..)
  exact ⟨s, ws, hn.filter _, hs, hfin.symm ▸ hlive⟩

lemma live_length_cap {goal : BitVec width} {k cap : Nat} {ws : List (BitVec width)}
    (hn : ws.Nodup) (run : live basicOps goal k ws.toFinset)
    (room : ws.length + k < 2 * cap) : ws.length ≤ cap := by
  have hc := live_card run
  rw [List.toFinset_card_of_nodup hn] at hc
  omega

lemma child_length_budget {a b z : BitVec width} {ws r front : List (BitVec width)}
    {k bound : Nat} (hp : ws.Perm (a :: b :: r))
    (hf : front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width))))
    (room : ws.length + (k + 1) ≤ bound) :
    (z :: (front ++ r)).length + k ≤ bound := by
  have plen := hp.length_eq
  have flen : front.length ≤ 2 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
    rcases hf with rfl | rfl | rfl | rfl <;> simp
  simp only [List.length_cons, List.length_append] at plen ⊢
  omega

lemma build_represented_roots {rep : Nat → Q → List (BitVec width) → Prop}
    {goal : BitVec width} {k : Nat} {inputs : List (BitVec width)} {roots : List Q}
    (hn : inputs.Nodup)
    (represented : ∀ ws, ws.Sublist inputs → ws.Nodup →
      live basicOps goal k ws.toFinset →
      ∃ s ∈ roots, ∃ ys, rep k s ys ∧ ys.Perm ws)
    (run : build basicOps goal k inputs.toFinset) :
    ∃ s ∈ roots, liveState rep goal k s := by
  classical
  obtain ⟨S, hS, hlive⟩ := compress run
  let ws := inputs.filter (· ∈ S)
  have hfin : ws.toFinset = S := by
    ext w
    simp only [ws, List.mem_toFinset, List.mem_filter, decide_eq_true_eq,
      and_iff_right_iff_imp]
    exact fun hw => List.mem_toFinset.mp (hS hw)
  have hnd : ws.Nodup := hn.filter _
  have hrun : live basicOps goal k ws.toFinset := hfin.symm ▸ hlive
  obtain ⟨s, hs, ys, hrep, hp⟩ := represented ws (List.filter_sublist ..) hnd hrun
  have heq : ys.toFinset = ws.toFinset := by
    ext w
    simp only [List.mem_toFinset]
    exact hp.mem_iff
  exact ⟨s, hs, ys, hp.nodup_iff.mpr hnd, hrep, heq.symm ▸ hrun⟩

lemma rejected_roots_no_build {rep : Nat → Q → List (BitVec width) → Prop}
    {goal : BitVec width} {k : Nat} {inputs : List (BitVec width)} {roots : List Q}
    {done : Q → Bool} {admissible : Nat → Q → Bool} {children : Nat → Q → List Q}
    (hn : inputs.Nodup)
    (finish : ∀ k s, rep k s [goal] → done s = true)
    (step : ∀ k s, liveState rep goal (k + 1) s →
      done s = true ∨ ∃ t ∈ children (k + 1) s, liveState rep goal k t)
    (allowed : ∀ k s, liveState rep goal (k + 1) s → admissible (k + 1) s = true)
    (represented : ∀ ws, ws.Sublist inputs → ws.Nodup →
      live basicOps goal k ws.toFinset →
      ∃ s ∈ roots, ∃ ys, rep k s ys ∧ ys.Perm ws)
    (rejected : ∀ s ∈ roots, search done admissible children k s = false) :
    ¬ build basicOps goal k inputs.toFinset := by
  intro run
  obtain ⟨s, hs, hlive⟩ := build_represented_roots hn represented run
  exact rejected_no_liveState finish step allowed (rejected s hs) hlive

end PNQuotient



namespace PNFrontier

open PnProjection PnTransition

variable {width : Nat}

def rowCode (ws : List (BitVec width)) (r : Fin width) : Nat :=
  (BitVec.ofBoolListLE (ws.map fun w => w[r.val])).toNat

lemma testBit_rowCode (ws : List (BitVec width)) (r : Fin width) (i : Nat) :
    (rowCode ws r).testBit i = ((ws[i]?).map fun w => w[r.val]).getD false := by
  change (BitVec.ofBoolListLE (ws.map fun w => w[r.val])).getLsbD i = _
  rw [BitVec.getLsbD_ofBoolListLE, List.getD_eq_getElem?_getD, List.getElem?_map]

lemma rowCode_testBit (ws : List (BitVec width)) (r : Fin width) (i : Nat)
    (hi : i < ws.length) : (rowCode ws r).testBit i = ws[i][r.val] := by
  simp [testBit_rowCode, hi]

lemma rowCode_lt (ws : List (BitVec width)) (r : Fin width) : rowCode ws r < 2^ws.length := by
  simpa only [rowCode, List.length_map] using
    (BitVec.ofBoolListLE (ws.map fun w => w[r.val])).isLt

lemma rowCode_eraseIdx (ws : List (BitVec width)) (r : Fin width) (i : Nat) :
    rowCode (ws.eraseIdx i) r = delBit i (rowCode ws r) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_rowCode, testBit_delBit, testBit_rowCode, List.getElem?_eraseIdx]
  by_cases h : j < i <;> simp [h]

lemma rowCode_append_insBit (ws : List (BitVec width)) (z : BitVec width) (r : Fin width) :
    rowCode (ws ++ [z]) r = insBit ws.length z[r.val] (rowCode ws r) := by
  apply Nat.eq_of_testBit_eq
  intro j
  rw [testBit_rowCode, testBit_insBit, List.getElem?_append]
  by_cases h : j < ws.length
  · simp [h, testBit_rowCode]
  · by_cases e : j = ws.length
    · simp [e]
    · have hs : ws.length ≤ j-1 := by omega
      have hz : j-ws.length ≠ 0 := by omega
      simp [h, e, testBit_rowCode, List.getElem?_eq_none hs, hz]

lemma rowCode_append_singleton (ws : List (BitVec width)) (z : BitVec width) (r : Fin width) :
    rowCode (ws ++ [z]) r = rowCode ws r + (if z[r.val] then 2^ws.length else 0) := by
  rw [rowCode_append_insBit, insBit_top _ _ (rowCode_lt ws r)]

def keptFront (i j : Nat) (keep : Fin 4) (ws : List (BitVec width)) : List (BitVec width) :=
  let ws := if keep.val &&& 2 == 0 then ws.eraseIdx j else ws
  if keep.val &&& 1 == 0 then ws.eraseIdx i else ws

lemma rowCode_keptFront (i j : Nat) (keep : Fin 4) (ws : List (BitVec width)) (r : Fin width) :
    rowCode (keptFront i j keep ws) r = dropPattern i j keep (rowCode ws r) := by
  unfold keptFront dropPattern
  split_ifs <;> simp only [rowCode_eraseIdx]

lemma keptFront_length {i j : Nat} (keep : Fin 4) (ws : List (BitVec width))
    (hij : i < j) (hj : j < ws.length) :
    (keptFront i j keep ws).length = ws.length-2+keepSize keep := by
  have hi : i < ws.length := by omega
  have hi' : i < (ws.eraseIdx j).length := by
    rw [List.length_eraseIdx_of_lt hj]
    omega
  fin_cases keep <;>
    simp [keptFront, keepSize, List.length_eraseIdx_of_lt hj,
      List.length_eraseIdx_of_lt hi, List.length_eraseIdx_of_lt hi'] <;> omega

lemma keptFront_sublist (i j : Nat) (keep : Fin 4) (ws : List (BitVec width)) :
    (keptFront i j keep ws).Sublist ws := by
  unfold keptFront
  split_ifs <;>
    first
    | exact (List.eraseIdx_sublist _ _).trans (List.eraseIdx_sublist _ _)
    | exact List.eraseIdx_sublist _ _
    | exact List.Sublist.refl _

lemma keptFront_mem {i j : Nat} {keep : Fin 4} {ws : List (BitVec width)} {w : BitVec width}
    (hw : w ∈ keptFront i j keep ws) : w ∈ ws := by
  unfold keptFront at hw
  split_ifs at hw <;>
    first
    | exact List.mem_of_mem_eraseIdx (List.mem_of_mem_eraseIdx hw)
    | exact List.mem_of_mem_eraseIdx hw
    | exact hw

end PNFrontier

namespace PNSelectors

lemma singles_index {α : Type} {ws r : List α} {a : α}
    (h : (a,r) ∈ SearchKernel.singles ws) :
    ∃ i, i < ws.length ∧ ws[i]? = some a ∧ r = ws.eraseIdx i ∧
      ws.Perm (a :: r) := by
  induction ws generalizing a r with
  | nil => simp [SearchKernel.singles] at h
  | cons x xs ih =>
    simp only [SearchKernel.singles, List.mem_cons, List.mem_map] at h
    rcases h with he | ⟨⟨a,r⟩, hm, he⟩
    · cases he
      exact ⟨0, by simp, rfl, rfl, .refl _⟩
    · cases he
      obtain ⟨i, hi, hv, hr, hp⟩ := ih hm
      refine ⟨i+1, by simpa using hi, by simpa using hv, ?_, ?_⟩
      · simp [hr]
      · exact (hp.cons x).trans (.swap _ _ _)

lemma pairs_indices {α : Type} {ws r : List α} {a b : α}
    (h : (a,b,r) ∈ SearchKernel.pairs ws) :
    ∃ i j, i < j ∧ j < ws.length ∧ ws[i]? = some a ∧ ws[j]? = some b ∧
      r = (ws.eraseIdx j).eraseIdx i ∧ ws.Perm (a :: b :: r) := by
  induction ws generalizing a b r with
  | nil => simp [SearchKernel.pairs] at h
  | cons x xs ih =>
    simp only [SearchKernel.pairs, List.mem_append, List.mem_map] at h
    rcases h with ⟨⟨b,r⟩, hm, he⟩ | ⟨⟨a,b,r⟩, hm, he⟩
    · cases he
      obtain ⟨j, hj, hv, hr, hp⟩ := singles_index hm
      refine ⟨0, j+1, by omega, by simpa using hj, rfl,
        by simpa using hv, ?_, hp.cons x⟩
      simp [hr]
    · cases he
      obtain ⟨i, j, hij, hj, hiVal, hjVal, hr, hp⟩ := ih hm
      refine ⟨i+1, j+1, by omega, by simpa using hj,
        by simpa using hiVal, by simpa using hjVal, ?_, ?_⟩
      · simp [hr]
      · exact (hp.cons x).trans ((List.Perm.swap _ _ _).trans
          ((List.Perm.swap _ _ _).cons a))

lemma perm_cons_eraseIdx {α : Type} {ws : List α} {i : Nat} {a : α}
    (h : ws[i]? = some a) : ws.Perm (a :: ws.eraseIdx i) := by
  induction ws generalizing i with
  | nil => simp at h
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst x
      exact .refl _
    | succ i =>
      have hp := ih (by simpa using h)
      simpa using (hp.cons x).trans (.swap _ _ _)

lemma pairs_retention_indices {α : Type} {ws r : List α} {a b : α}
    (h : (a,b,r) ∈ SearchKernel.pairs ws) :
    ∃ i j, i < j ∧ j < ws.length ∧ ws[i]? = some a ∧ ws[j]? = some b ∧
      (ws.eraseIdx j).eraseIdx i = r ∧
      (ws.eraseIdx j).Perm (a :: r) ∧
      (ws.eraseIdx i).Perm (b :: r) ∧ ws.Perm (a :: b :: r) := by
  obtain ⟨i, j, hij, hj, hiVal, hjVal, hr, hp⟩ := pairs_indices h
  refine ⟨i, j, hij, hj, hiVal, hjVal, hr.symm, ?_, ?_, hp⟩
  · have hb := perm_cons_eraseIdx hjVal
    have hab : ws.Perm (b :: a :: r) := hp.trans (.swap _ _ _)
    exact (List.perm_cons b).mp (hb.symm.trans hab)
  · have ha := perm_cons_eraseIdx hiVal
    exact (List.perm_cons a).mp (ha.symm.trans hp)

lemma pairs_keptFront_indices {width : Nat}
    {ws r front : List (BitVec width)} {a b : BitVec width}
    (h : (a,b,r) ∈ SearchKernel.pairs ws)
    (hf : front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width)))) :
    ∃ i j, ∃ keep : Fin 4,
      i < j ∧ j < ws.length ∧ ws[i]? = some a ∧ ws[j]? = some b ∧
      (PNFrontier.keptFront i j keep ws).Perm (front ++ r) := by
  obtain ⟨i, j, hij, hj, ha, hb, hnone, honlyA, honlyB, hboth⟩ := pairs_retention_indices h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with rfl | rfl | rfl | rfl
  · refine ⟨i, j, 0, hij, hj, ha, hb, ?_⟩
    simpa [PNFrontier.keptFront, hnone] using (List.Perm.refl r)
  · refine ⟨i, j, 1, hij, hj, ha, hb, ?_⟩
    simpa [PNFrontier.keptFront] using honlyA
  · refine ⟨i, j, 2, hij, hj, ha, hb, ?_⟩
    simpa [PNFrontier.keptFront] using honlyB
  · refine ⟨i, j, 3, hij, hj, ha, hb, ?_⟩
    simpa [PNFrontier.keptFront] using hboth

end PNSelectors

namespace PNConcrete

open PnTransition PNPlanes


def Rep {width : Nat} (target : BitVec width) (anchor : Fin width)
    (k : Nat) (state : Nat × Nat × Nat) (ws : List (BitVec width)) : Prop :=
  ws.length = state.1 ∧ state.1 + k ≤ 19 ∧ state.1 ≤ 10 ∧
    (∀ w ∈ ws, w[anchor.val] = false) ∧
    ∀ value : Bool, ∀ x : Nat,
      (if value then state.2.1 else state.2.2).testBit x = true ↔
        ∃ r : Fin width, target[r.val] = value ∧ PNFrontier.rowCode ws r = x

lemma bitmap_bound {ρ : Type} {m S : Nat} {code : ρ → Nat} {label : ρ → Prop}
    (bounded : ∀ r, code r < 2^m)
    (represented : ∀ x, S.testBit x = true ↔ ∃ r, label r ∧ code r = x) :
    S < 2^(2^m) := by
  apply Nat.lt_pow_two_of_testBit
  intro x hx
  cases hb : S.testBit x with
  | false => rfl
  | true =>
    obtain ⟨r, hr, he⟩ := (represented x).mp hb
    have hc := bounded r
    omega

lemma transitionSet_exact {ρ : Type} {m i j S : Nat}
    (hij : i < j) (hj : j < m) (hm : m ≤ 10) (hS : S < 2^(2^m))
    (keep gate : Fin 4) {code childCode : ρ → Nat} {label : ρ → Prop}
    (represented : ∀ x, S.testBit x = true ↔ ∃ r, label r ∧ code r = x)
    (rows : ∀ r, childCode r = dropPattern i j keep (code r) +
      (if ChromGate.eval gate ((code r).testBit i) ((code r).testBit j)
        then 2^(m-2+keepSize keep) else 0)) :
    ∀ y, (transitionSet m i j keep (gateMask i j gate) S).testBit y = true ↔
      ∃ r, label r ∧ childCode r = y := by
  intro y
  rw [transitionSet_gate_image hij hj hm hS]
  constructor
  · rintro ⟨x, hx, hy⟩
    obtain ⟨r, hr, hcode⟩ := (represented x).mp hx
    subst x
    exact ⟨r, hr, (rows r).trans hy.symm⟩
  · rintro ⟨r, hr, hy⟩
    refine ⟨code r, (represented (code r)).mpr ⟨r, hr, rfl⟩, ?_⟩
    exact hy.symm.trans (rows r)

def childState (m P N i j : Nat) (keep gate : Fin 4) : Nat × Nat × Nat :=
  (m - 1 + keepSize keep,
    transitionSet m i j keep (gateMask i j gate) P,
    transitionSet m i j keep (gateMask i j gate) N)

def childFront {width : Nat} (ws : List (BitVec width)) (i j : Nat)
    (keep gate : Fin 4) (a b : BitVec width) : List (BitVec width) :=
  PNFrontier.keptFront i j keep ws ++ [ChromGate.word gate a b]

lemma childFront_rows {width : Nat} (ws : List (BitVec width)) (i j : Nat)
    (keep gate : Fin 4) (a b : BitVec width)
    (hij : i < j) (hj : j < ws.length)
    (ha : ws[i]? = some a) (hb : ws[j]? = some b) (r : Fin width) :
    PNFrontier.rowCode (childFront ws i j keep gate a b) r =
      dropPattern i j keep (PNFrontier.rowCode ws r) +
        (if ChromGate.eval gate ((PNFrontier.rowCode ws r).testBit i)
          ((PNFrontier.rowCode ws r).testBit j)
          then 2^(ws.length-2+keepSize keep) else 0) := by
  rw [childFront, PNFrontier.rowCode_append_singleton,
    PNFrontier.rowCode_keptFront, PNFrontier.keptFront_length keep ws hij hj,
    ChromGate.word_get, PNFrontier.testBit_rowCode, PNFrontier.testBit_rowCode,
    ha, hb]
  rfl

lemma childFront_nodup {width : Nat} {ws : List (BitVec width)} {i j : Nat}
    {keep gate : Fin 4} {a b : BitVec width} (hn : ws.Nodup)
    (fresh : ChromGate.word gate a b ∉ ws.toFinset) :
    (childFront ws i j keep gate a b).Nodup := by
  rw [childFront, List.nodup_append]
  refine ⟨hn.sublist (PNFrontier.keptFront_sublist i j keep ws), by simp, ?_⟩
  intro w hw v hv hwv
  have he := List.mem_singleton.mp hv
  subst v
  subst w
  exact fresh (List.mem_toFinset.mpr (PNFrontier.keptFront_mem hw))

lemma rep_transition {width k m P N i j : Nat}
    {target goal a b : BitVec width} {anchor : Fin width} {ws : List (BitVec width)}
    (keep gate : Fin 4) (hn : ws.Nodup) (rep : Rep target anchor (k + 1) (m,P,N) ws)
    (hij : i < j) (hj : j < m) (ha : ws[i]? = some a) (hb : ws[j]? = some b)
    (hamem : a ∈ ws) (hbmem : b ∈ ws)
    (fresh : ChromGate.word gate a b ∉ ws.toFinset)
    (tail : live basicOps goal k (childFront ws i j keep gate a b).toFinset) :
    Rep target anchor k (childState m P N i j keep gate)
      (childFront ws i j keep gate a b) := by
  obtain ⟨hlen, hroom, hcap, hzero, hexact⟩ := rep
  have hjw : j < ws.length := by omega
  have hm2 : 2 ≤ m := by omega
  have hsize : keepSize keep ≤ 2 := by
    fin_cases keep <;> decide
  have childlen : (childFront ws i j keep gate a b).length = m-1+keepSize keep := by
    simp only [childFront, List.length_append, List.length_singleton,
      PNFrontier.keptFront_length keep ws hij hjw, hlen]
    omega
  have childroom : (m-1+keepSize keep) + k ≤ 19 := by omega
  have childcap : m-1+keepSize keep ≤ 10 := by
    have hc := live_card tail
    rw [List.toFinset_card_of_nodup (childFront_nodup hn fresh), childlen] at hc
    omega
  refine ⟨childlen, childroom, childcap, ?_, ?_⟩
  · intro w hw
    rcases List.mem_append.mp hw with hold | hnew
    · exact hzero w (PNFrontier.keptFront_mem hold)
    · have he := List.mem_singleton.mp hnew
      subst w
      rw [ChromGate.word_get, hzero a hamem, hzero b hbmem]
      fin_cases gate <;> rfl
  · intro value y
    have bound : (if value then P else N) < 2^(2^m) := by
      apply bitmap_bound (code := PNFrontier.rowCode ws) (label := fun r => target[r.val] = value)
      · intro r
        simpa only [hlen] using PNFrontier.rowCode_lt ws r
      · exact hexact value
    have he := transitionSet_exact hij hj hcap bound keep gate
      (represented := hexact value)
      (rows := fun r => by
        simpa only [hlen] using childFront_rows ws i j keep gate a b hij hjw ha hb r) y
    cases value <;> exact he

end PNConcrete

namespace PNConcrete

lemma transitionCover {width k m P N : Nat}
    {target goal a b z : BitVec width} {anchor : Fin width}
    {ws r front : List (BitVec width)}
    (hn : ws.Nodup) (rep : Rep target anchor (k+1) (m,P,N) ws)
    (hpair : (a,b,r) ∈ SearchKernel.pairs ws)
    (hfront : front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width))))
    (hz : z ∈ basicOps a b) (fresh : z ∉ ws.toFinset)
    (tail : live basicOps goal k (z :: (front ++ r)).toFinset) :
    ∃ i j, ∃ keep gate : Fin 4, i < j ∧ j < m ∧
      ∃ ys, Rep target anchor k (childState m P N i j keep gate) ys ∧
        ys.Perm (z :: (front ++ r)) := by
  obtain ⟨i, j, keep, hij, hj, ha, hb, hp⟩ := PNSelectors.pairs_keptFront_indices hpair hfront
  obtain ⟨gate, rfl⟩ := ChromGate.of_basicOps hz
  have hperm : (childFront ws i j keep gate a b).Perm
      (ChromGate.word gate a b :: (front ++ r)) := by
    change (PNFrontier.keptFront i j keep ws ++ [ChromGate.word gate a b]).Perm _
    exact List.perm_append_comm.trans (hp.cons _)
  have heq : (childFront ws i j keep gate a b).toFinset =
      (ChromGate.word gate a b :: (front ++ r)).toFinset := by
    ext w
    simp only [List.mem_toFinset]
    exact hperm.mem_iff
  have htail : live basicOps goal k (childFront ws i j keep gate a b).toFinset :=
    heq.symm ▸ tail
  have hamem : a ∈ ws := (PNSelectors.perm_cons_eraseIdx ha).mem_iff.mpr (by simp)
  have hbmem : b ∈ ws := (PNSelectors.perm_cons_eraseIdx hb).mem_iff.mpr (by simp)
  have hjm : j < m := by have hlen := rep.1; omega
  exact ⟨i, j, keep, gate, hij, hjm, childFront ws i j keep gate a b,
    rep_transition keep gate hn rep hij hjm ha hb hamem hbmem fresh htail, hperm⟩

def coordinateChildren (state : Nat × Nat × Nat) : List (Nat × Nat × Nat) :=
  (List.range state.1).flatMap fun j =>
    (List.range j).flatMap fun i =>
      (List.finRange 4).flatMap fun gate =>
        (List.finRange 4).map fun keep =>
          childState state.1 state.2.1 state.2.2 i j keep gate

lemma childState_mem {m P N i j : Nat} (keep gate : Fin 4)
    (hij : i < j) (hj : j < m) :
    childState m P N i j keep gate ∈ coordinateChildren (m,P,N) := by
  simp only [coordinateChildren, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨j, hj, i, hij, gate, by simp, keep, by simp, rfl⟩

lemma coordinateCover {width k : Nat}
    {target goal a b z : BitVec width} {anchor : Fin width}
    {state : Nat × Nat × Nat} {ws r front : List (BitVec width)}
    (hn : ws.Nodup) (rep : Rep target anchor (k+1) state ws)
    (hpair : (a,b,r) ∈ SearchKernel.pairs ws)
    (hfront : front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width))))
    (hz : z ∈ basicOps a b) (fresh : z ∉ ws.toFinset)
    (tail : live basicOps goal k (z :: (front ++ r)).toFinset) :
    ∃ child ∈ coordinateChildren state,
      ∃ ys, Rep target anchor k child ys ∧ ys.Perm (z :: (front ++ r)) := by
  obtain ⟨m, P, N⟩ := state
  obtain ⟨i, j, keep, gate, hij, hj, ys, hrep, hp⟩ :=
    transitionCover hn rep hpair hfront hz fresh tail
  exact ⟨childState m P N i j keep gate, childState_mem keep gate hij hj, ys, hrep, hp⟩

lemma coordinate_liveState_step {width : Nat} {target goal : BitVec width}
    {anchor : Fin width} {done : (Nat × Nat × Nat) → Bool}
    (finish : ∀ k s, Rep target anchor k s [goal] → done s = true)
    (k : Nat) (s : Nat × Nat × Nat)
    (run : PNQuotient.liveState (Rep target anchor) goal (k+1) s) :
    done s = true ∨ ∃ t ∈ coordinateChildren s,
      PNQuotient.liveState (Rep target anchor) goal k t := by
  apply PNQuotient.liveState_step (children := fun _ => coordinateChildren) finish ?_ run
  intro k s ws a b z r front hn hrep hpair hfront hz fresh tail
  exact coordinateCover hn hrep hpair hfront hz fresh tail

lemma coordinate_search_complete {width : Nat} {target goal : BitVec width}
    {anchor : Fin width} {done : (Nat × Nat × Nat) → Bool}
    {admissible : Nat → (Nat × Nat × Nat) → Bool}
    (finish : ∀ k s, Rep target anchor k s [goal] → done s = true)
    (allowed : ∀ k s, PNQuotient.liveState (Rep target anchor) goal (k+1) s →
      admissible (k+1) s = true)
    {k : Nat} {s : Nat × Nat × Nat}
    (run : PNQuotient.liveState (Rep target anchor) goal k s) :
    PNQuotient.search done admissible (fun _ => coordinateChildren) k s = true :=
  PNQuotient.search_complete finish (coordinate_liveState_step finish) allowed run

end PNConcrete

namespace PNConcrete

lemma rowCode_singleton {width : Nat} (w : BitVec width) (r : Fin width) :
    PNFrontier.rowCode [w] r = if w[r.val] then 1 else 0 := by
  change (BitVec.ofBoolListLE [w[r.val]]).toNat = if w[r.val] then 1 else 0
  cases w[r.val] <;> rfl

lemma mask_empty_of_rows {ρ : Type} {S mask : Nat} {code : ρ → Nat} {label : ρ → Prop}
    (represented : ∀ x, S.testBit x = true ↔ ∃ r, label r ∧ code r = x)
    (excluded : ∀ r, label r → mask.testBit (code r) = false) : S &&& mask = 0 := by
  apply Nat.eq_of_testBit_eq
  intro x
  rw [Nat.testBit_and, show (0 : Nat).testBit x = false by simp]
  cases hx : S.testBit x with
  | false => rfl
  | true =>
    change mask.testBit x = false
    obtain ⟨r, hr, he⟩ := (represented x).mp hx
    rw [← he]
    exact excluded r hr

def solved (n positive negative : Nat) : Bool :=
  (List.range n).any fun i =>
    ((positive &&& PNMasks.lowMask i == 0) && (negative &&& PNPlanes.highMask i == 0)) ||
      ((positive &&& PNPlanes.highMask i == 0) && (negative &&& PNMasks.lowMask i == 0))

lemma solved_singleton {width k : Nat} {target goal : BitVec width} {anchor : Fin width}
    {state : Nat × Nat × Nat} (goal_eq : goal = target ∨ goal = ~~~target)
    (rep : Rep target anchor k state [goal]) :
    solved state.1 state.2.1 state.2.2 = true := by
  obtain ⟨m, P, N⟩ := state
  obtain ⟨hlen, hroom, hcap, hzero, hexact⟩ := rep
  have hm : m = 1 := by simpa using hlen.symm
  subst m
  unfold solved
  apply List.any_eq_true.mpr
  refine ⟨0, by simp, ?_⟩
  simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq]
  have low1 : (PNMasks.lowMask 0).testBit 1 = false := by
    simpa using PNMasks.lowMask_bits (0 : Fin 10) (1 : Fin 1024)
  have high0 : (PNPlanes.highMask 0).testBit 0 = false := by
    simpa using PNPlanes.highMask_bits (0 : Fin 10) (0 : Fin 1024)
  rcases goal_eq with rfl | rfl
  · left
    constructor
    · apply mask_empty_of_rows (hexact true)
      intro r hr
      rw [rowCode_singleton, hr]
      exact low1
    · apply mask_empty_of_rows (hexact false)
      intro r hr
      rw [rowCode_singleton, hr]
      exact high0
  · right
    constructor
    · apply mask_empty_of_rows (hexact true)
      intro r hr
      rw [rowCode_singleton, BitVec.getElem_not, hr]
      exact high0
    · apply mask_empty_of_rows (hexact false)
      intro r hr
      rw [rowCode_singleton, BitVec.getElem_not, hr]
      exact low1

end PNConcrete

namespace PNGuards

open PNConcrete PNFrontier PNPlanes

lemma rep_active {width k m P N : Nat} {target : BitVec width} {anchor : Fin width}
    {ws : List (BitVec width)} (rep : Rep target anchor k (m,P,N) ws) (r : Fin width) :
    (P ||| N).testBit (rowCode ws r) = true := by
  have represented := rep.2.2.2.2 (target[r.val]) (rowCode ws r)
  have hbit := represented.mpr ⟨r, rfl, rfl⟩
  rw [Nat.testBit_or]
  cases h : target[r.val] with
  | false =>
    have hn : N.testBit (rowCode ws r) = true := by simpa [h] using hbit
    simp [hn]
  | true =>
    have hp : P.testBit (rowCode ws r) = true := by simpa [h] using hbit
    simp [hp]

lemma rowCode_eq_bits {width : Nat} {ws : List (BitVec width)} {p q : Fin width}
    (he : rowCode ws p = rowCode ws q) {w : BitVec width} (hw : w ∈ ws) :
    w[p.val] = w[q.val] := by
  obtain ⟨i, hi, hwi⟩ := List.getElem_of_mem hw
  have hb := congrArg (fun x : Nat => x.testBit i) he
  simpa only [rowCode_testBit ws p i hi, rowCode_testBit ws q i hi, hwi] using hb

lemma rep_disjoint {width k m P N : Nat} {target g : BitVec width} {anchor : Fin width}
    {ws : List (BitVec width)} (rep : Rep target anchor k (m,P,N) ws)
    (run : live basicOps g k ws.toFinset) (hg : g = target ∨ g = ~~~target) :
    P &&& N = 0 := by
  apply Nat.eq_of_testBit_eq
  intro x
  rw [Nat.testBit_and, Nat.zero_testBit]
  cases hp : P.testBit x with
  | false => simp
  | true =>
    cases hn : N.testBit x with
    | false => simp
    | true =>
      obtain ⟨p, htp, hcp⟩ := (rep.2.2.2.2 true x).mp hp
      obtain ⟨q, htq, hcq⟩ := (rep.2.2.2.2 false x).mp hn
      have htarget : target[p.val] ≠ target[q.val] := by simp [htp, htq]
      obtain ⟨w, hw, hdiff⟩ := live_target_separates run hg htarget
      exact False.elim (hdiff (rowCode_eq_bits (hcp.trans hcq.symm) (List.mem_toFinset.mp hw)))

def redundant (n active gate : Nat) : Bool :=
  (List.range n).any fun i =>
    active &&& (gate ^^^ (PNMasks.lowMasks[i]! <<< (1 <<< i))) == 0

lemma redundant_eq_true {m active gate : Nat} :
    redundant m active gate = true ↔
      ∃ i, i < m ∧ active &&& (gate ^^^ (PNMasks.lowMasks[i]! <<< (1 <<< i))) = 0 := by
  simp [redundant, List.any_eq_true]

lemma lookup_bound {α : Type} {ws : List α} {i : Nat} {a : α}
    (ha : ws[i]? = some a) : i < ws.length := by
  by_contra hi
  have hn : ws[i]? = none := List.getElem?_eq_none (by omega)
  rw [hn] at ha
  contradiction

lemma rep_fresh_nonredundant {width k m P N i j : Nat}
    {target a b : BitVec width} {anchor : Fin width} {ws : List (BitVec width)}
    (rep : Rep target anchor k (m,P,N) ws) (op : Fin 4)
    (ha : ws[i]? = some a) (hb : ws[j]? = some b)
    (fresh : ChromGate.word op a b ∉ ws.toFinset) :
    redundant m (P ||| N) (gateMask i j op) = false := by
  apply Bool.eq_false_iff.mpr
  intro hred
  obtain ⟨v, hv, hzero⟩ := redundant_eq_true.mp hred
  have hlen := rep.1
  have hcap := rep.2.2.1
  have hi : i < 10 := by have := lookup_bound ha; omega
  have hj : j < 10 := by have := lookup_bound hb; omega
  have hv10 : v < 10 := by omega
  have hvw : v < ws.length := by omega
  let w := ws[v]'hvw
  have hword : ChromGate.word op a b = w := by
    apply BitVec.eq_of_getLsbD_eq
    intro r hr
    let row : Fin width := ⟨r, hr⟩
    have hcode : rowCode ws row < 1024 := lt_of_lt_of_le (rowCode_lt ws row)
      (by simpa only [hlen] using Nat.pow_le_pow_right (by decide : 1 ≤ 2) hcap)
    have heq := congrArg (fun x : Nat => x.testBit (rowCode ws row)) hzero
    have hlookup : PNMasks.lowMasks[v]! <<< (1 <<< v) = highMask v := by
      rw [← PnProjection.lowMask_getBang ⟨v, hv10⟩]
      rfl
    rw [hlookup, Nat.testBit_and, Nat.testBit_xor, Nat.zero_testBit,
      rep_active rep row, gateMask_bits ⟨i, hi⟩ ⟨j, hj⟩ op ⟨rowCode ws row, hcode⟩,
      highMask_bits ⟨v, hv10⟩ ⟨rowCode ws row, hcode⟩] at heq
    have hgate : ChromGate.eval op ((rowCode ws row).testBit i) ((rowCode ws row).testBit j) =
        (rowCode ws row).testBit v := by
      simpa using heq
    change (ChromGate.word op a b)[row.val] = w[row.val]
    rw [ChromGate.word_get]
    simpa [testBit_rowCode, ha, hb, w, hvw] using hgate
  apply fresh
  rw [hword]
  exact List.mem_toFinset.mpr (List.getElem_mem hvw)

end PNGuards

namespace PNConcrete

open PnTransition

lemma keepSize_le_of_live_length {width k m : Nat} {keep : Fin 4}
    {goal : BitVec width} {ys : List (BitVec width)}
    (hn : ys.Nodup) (hlen : ys.length = m - 1 + keepSize keep)
    (run : live basicOps goal k ys.toFinset) :
    keepSize keep ≤ k + 2 - m := by
  have hc := live_card run
  rw [List.toFinset_card_of_nodup hn, hlen] at hc
  omega

lemma represented_child_keepSize_le {width k m P N i j : Nat} {keep gate : Fin 4}
    {target goal : BitVec width} {anchor : Fin width} {ys : List (BitVec width)}
    (hn : ys.Nodup) (rep : Rep target anchor k (childState m P N i j keep gate) ys)
    (run : live basicOps goal k ys.toFinset) :
    keepSize keep ≤ k + 2 - m :=
  keepSize_le_of_live_length hn rep.1 run

lemma selected_child_nodup {width : Nat} {ws r front : List (BitVec width)}
    {a b z : BitVec width} (hn : ws.Nodup)
    (hpair : (a,b,r) ∈ SearchKernel.pairs ws)
    (hfront : front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width))))
    (fresh : z ∉ ws.toFinset) : (z :: (front ++ r)).Nodup := by
  obtain ⟨i,j,keep,_,_,_,_,hp⟩ := PNSelectors.pairs_keptFront_indices hpair hfront
  have hkept := hn.sublist (PNFrontier.keptFront_sublist i j keep ws)
  refine List.nodup_cons.mpr ⟨?_, hp.nodup_iff.mp hkept⟩
  intro hz
  exact fresh (List.mem_toFinset.mpr (PNFrontier.keptFront_mem (hp.mem_iff.mpr hz)))

lemma transitionCover_sizeBound {width k m P N : Nat}
    {target goal a b z : BitVec width} {anchor : Fin width}
    {ws r front : List (BitVec width)}
    (hn : ws.Nodup) (rep : Rep target anchor (k+1) (m,P,N) ws)
    (hpair : (a,b,r) ∈ SearchKernel.pairs ws)
    (hfront : front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width))))
    (hz : z ∈ basicOps a b) (fresh : z ∉ ws.toFinset)
    (tail : live basicOps goal k (z :: (front ++ r)).toFinset) :
    ∃ i j, ∃ keep gate : Fin 4, i < j ∧ j < m ∧ keepSize keep ≤ k+2-m ∧
      ∃ ys, Rep target anchor k (childState m P N i j keep gate) ys ∧
        ys.Perm (z :: (front ++ r)) := by
  obtain ⟨i,j,keep,gate,hij,hj,ys,hrep,hp⟩ :=
    transitionCover hn rep hpair hfront hz fresh tail
  have hny : ys.Nodup := hp.nodup_iff.mpr (selected_child_nodup hn hpair hfront fresh)
  have heq : ys.toFinset = (z :: (front ++ r)).toFinset := by
    ext w
    simp only [List.mem_toFinset]
    exact hp.mem_iff
  have hrun : live basicOps goal k ys.toFinset := heq.symm ▸ tail
  exact ⟨i,j,keep,gate,hij,hj,represented_child_keepSize_le hny hrep hrun,ys,hrep,hp⟩

def sizeCoordinateChildren (budget : Nat) (state : Nat × Nat × Nat) :
    List (Nat × Nat × Nat) :=
  (List.range state.1).flatMap fun j =>
    (List.range j).flatMap fun i =>
      (List.finRange 4).flatMap fun gate =>
        ((List.finRange 4).filter fun keep => decide (keepSize keep ≤ budget+1-state.1)).map
          fun keep => childState state.1 state.2.1 state.2.2 i j keep gate

lemma childState_mem_size {budget m P N i j : Nat} (keep gate : Fin 4)
    (hij : i < j) (hj : j < m) (hkeep : keepSize keep ≤ budget+1-m) :
    childState m P N i j keep gate ∈ sizeCoordinateChildren budget (m,P,N) := by
  simp only [sizeCoordinateChildren, List.mem_flatMap, List.mem_map,
    List.mem_filter, List.mem_range, decide_eq_true_eq]
  exact ⟨j,hj,i,hij,gate,by simp,keep,⟨by simp,hkeep⟩,rfl⟩

lemma sizeCoordinateCover {width k : Nat}
    {target goal a b z : BitVec width} {anchor : Fin width}
    {state : Nat × Nat × Nat} {ws r front : List (BitVec width)}
    (hn : ws.Nodup) (rep : Rep target anchor (k+1) state ws)
    (hpair : (a,b,r) ∈ SearchKernel.pairs ws)
    (hfront : front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width))))
    (hz : z ∈ basicOps a b) (fresh : z ∉ ws.toFinset)
    (tail : live basicOps goal k (z :: (front ++ r)).toFinset) :
    ∃ child ∈ sizeCoordinateChildren (k+1) state,
      ∃ ys, Rep target anchor k child ys ∧ ys.Perm (z :: (front ++ r)) := by
  obtain ⟨m,P,N⟩ := state
  obtain ⟨i,j,keep,gate,hij,hj,hkeep,ys,hrep,hp⟩ :=
    transitionCover_sizeBound hn rep hpair hfront hz fresh tail
  exact ⟨childState m P N i j keep gate,
    childState_mem_size keep gate hij hj (by simpa [Nat.add_assoc] using hkeep),ys,hrep,hp⟩

end PNConcrete


namespace PNGraphEdges

def phaseMask (i : Nat) (b : Bool) : Nat :=
  if b then PNPlanes.highMask i else PNMasks.lowMask i

lemma phaseMask_bits (i : Fin 10) (x : Fin 1024) (b : Bool) :
    (phaseMask i.val b).testBit x.val = (x.val.testBit i.val == b) := by
  cases b <;> simp [phaseMask, PNPlanes.highMask_bits, PNMasks.lowMask_bits]

lemma bit_bound {S x : Nat} (hS : S < 2^1024) (hbit : S.testBit x = true) :
    x < 1024 := by
  by_contra h
  have hp : 2^1024 ≤ 2^x := Nat.pow_le_pow_right (by decide) (by omega)
  have hf := Nat.testBit_lt_two_pow (show S < 2^x by omega)
  simp only [hbit] at hf
  exact Bool.noConfusion hf

def maskWitness (P N : Nat) (flip : Nat → Nat → Nat) (i j : Nat) : Prop :=
  ∃ p q,
    (P &&& flip i N).testBit p = true ∧ (P &&& flip j N).testBit p = true ∧
    (N &&& flip i P).testBit q = true ∧ (N &&& flip j P).testBit q = true ∧
    p.testBit i ≠ q.testBit i ∧ p.testBit j ≠ q.testBit j

lemma quadrant_witness (P N : Nat) (flip : Nat → Nat → Nat) (i j : Fin 10)
    (hP : P < 2^1024) (hN : N < 2^1024) (a b : Bool)
    (hp : ((P &&& flip i.val N) &&& (P &&& flip j.val N)) &&&
      phaseMask i.val a &&& phaseMask j.val b ≠ 0)
    (hq : ((N &&& flip i.val P) &&& (N &&& flip j.val P)) &&&
      phaseMask i.val (!a) &&& phaseMask j.val (!b) ≠ 0) :
    maskWitness P N flip i.val j.val := by
  obtain ⟨p, hp⟩ := Nat.exists_testBit_of_ne_zero hp
  obtain ⟨q, hq⟩ := Nat.exists_testBit_of_ne_zero hq
  simp only [Nat.testBit_and, Bool.and_eq_true] at hp hq
  have pb := bit_bound hP hp.1.1.1.1
  have qb := bit_bound hN hq.1.1.1.1
  have pa := hp.1.2
  have pbb := hp.2
  have qa := hq.1.2
  have qbb := hq.2
  rw [phaseMask_bits i ⟨p,pb⟩ a] at pa
  rw [phaseMask_bits j ⟨p,pb⟩ b] at pbb
  rw [phaseMask_bits i ⟨q,qb⟩ (!a)] at qa
  rw [phaseMask_bits j ⟨q,qb⟩ (!b)] at qbb
  simp only [beq_iff_eq] at pa pbb qa qbb
  refine ⟨p,q,?_,?_,?_,?_,?_,?_⟩
  · simpa only [Nat.testBit_and, Bool.and_eq_true] using hp.1.1.1
  · simpa only [Nat.testBit_and, Bool.and_eq_true] using hp.1.1.2
  · simpa only [Nat.testBit_and, Bool.and_eq_true] using hq.1.1.1
  · simpa only [Nat.testBit_and, Bool.and_eq_true] using hq.1.1.2
  · rw [pa, qa]; cases a <;> decide
  · rw [pbb, qbb]; cases b <;> decide

def vertex (P N : Nat) (flip : Nat → Nat → Nat) (i : Nat) :
    Nat × Nat × Nat × Nat × Nat :=
  (i,PNMasks.lowMask i,PNPlanes.highMask i,P &&& flip i N,N &&& flip i P)

def edgeBoolFast (vi vj : Nat × Nat × Nat × Nat × Nat) : Bool :=
  let (_,li,hi,pi,ni) := vi
  let (_,lj,hj,pj,nj) := vj
  let cp := pi &&& pj
  let cn := ni &&& nj
  (!(cp &&& li &&& lj == 0) && !(cn &&& hi &&& hj == 0)) ||
  (!(cp &&& hi &&& lj == 0) && !(cn &&& li &&& hj == 0)) ||
  (!(cp &&& li &&& hj == 0) && !(cn &&& hi &&& lj == 0)) ||
  (!(cp &&& hi &&& hj == 0) && !(cn &&& li &&& lj == 0))

lemma edgeBoolFast_witness (P N : Nat) (flip : Nat → Nat → Nat) (i j : Fin 10)
    (hP : P < 2^1024) (hN : N < 2^1024)
    (h : edgeBoolFast (vertex P N flip i.val) (vertex P N flip j.val) = true) :
    maskWitness P N flip i.val j.val := by
  simp only [edgeBoolFast, vertex, Bool.or_eq_true, Bool.and_eq_true,
    Bool.not_eq_true', beq_eq_false_iff_ne] at h
  rcases h with ((⟨hp,hq⟩ | ⟨hp,hq⟩) | ⟨hp,hq⟩) | ⟨hp,hq⟩
  · exact quadrant_witness P N flip i j hP hN false false hp hq
  · exact quadrant_witness P N flip i j hP hN true false hp hq
  · exact quadrant_witness P N flip i j hP hN false true hp hq
  · exact quadrant_witness P N flip i j hP hN true true hp hq

end PNGraphEdges


namespace PNConcrete

open PnTransition PNPlanes

lemma transitionCover_guards {width k m P N : Nat}
    {target goal a b z : BitVec width} {anchor : Fin width}
    {ws r front : List (BitVec width)}
    (hg : goal = target ∨ goal = ~~~target)
    (hn : ws.Nodup) (rep : Rep target anchor (k+1) (m,P,N) ws)
    (hpair : (a,b,r) ∈ SearchKernel.pairs ws)
    (hfront : front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width))))
    (hz : z ∈ basicOps a b) (fresh : z ∉ ws.toFinset)
    (tail : live basicOps goal k (z :: (front ++ r)).toFinset) :
    ∃ i j, ∃ keep gate : Fin 4, i < j ∧ j < m ∧
      PNGuards.redundant m (P ||| N) (gateMask i j gate) = false ∧
      keepSize keep ≤ k+2-m ∧
      (childState m P N i j keep gate).2.1 &&&
        (childState m P N i j keep gate).2.2 = 0 ∧
      ∃ ys, Rep target anchor k (childState m P N i j keep gate) ys ∧
        ys.Perm (z :: (front ++ r)) := by
  obtain ⟨i,j,keep,hij,hj,ha,hb,hp⟩ := PNSelectors.pairs_keptFront_indices hpair hfront
  obtain ⟨gate,rfl⟩ := ChromGate.of_basicOps hz
  have hperm : (childFront ws i j keep gate a b).Perm
      (ChromGate.word gate a b :: (front ++ r)) := by
    change (PNFrontier.keptFront i j keep ws ++ [ChromGate.word gate a b]).Perm _
    exact List.perm_append_comm.trans (hp.cons _)
  have heq : (childFront ws i j keep gate a b).toFinset =
      (ChromGate.word gate a b :: (front ++ r)).toFinset := by
    ext w
    simp only [List.mem_toFinset]
    exact hperm.mem_iff
  have htail : live basicOps goal k (childFront ws i j keep gate a b).toFinset :=
    heq.symm ▸ tail
  have hamem : a ∈ ws := (PNSelectors.perm_cons_eraseIdx ha).mem_iff.mpr (by simp)
  have hbmem : b ∈ ws := (PNSelectors.perm_cons_eraseIdx hb).mem_iff.mpr (by simp)
  have hjm : j < m := by have hlen := rep.1; omega
  have hrep := rep_transition keep gate hn rep hij hjm ha hb hamem hbmem fresh htail
  have hkeep := represented_child_keepSize_le (childFront_nodup hn fresh) hrep htail
  have hdisjoint := PNGuards.rep_disjoint hrep htail hg
  exact ⟨i,j,keep,gate,hij,hjm,PNGuards.rep_fresh_nonredundant rep gate ha hb fresh,
    hkeep,hdisjoint,childFront ws i j keep gate a b,hrep,hperm⟩

def filteredChildren (budget : Nat) (state : Nat × Nat × Nat) : List (Nat × Nat × Nat) :=
  (List.range state.1).flatMap fun j =>
    (List.range j).flatMap fun i =>
      (List.finRange 4).flatMap fun gate =>
        if PNGuards.redundant state.1 (state.2.1 ||| state.2.2) (gateMask i j gate) then [] else
          (((List.finRange 4).filter fun keep => decide (keepSize keep ≤ budget+1-state.1)).map
            fun keep => childState state.1 state.2.1 state.2.2 i j keep gate).filter
              fun child => child.2.1 &&& child.2.2 == 0

lemma childState_mem_filtered {budget m P N i j : Nat} (keep gate : Fin 4)
    (hij : i < j) (hj : j < m)
    (hred : PNGuards.redundant m (P ||| N) (gateMask i j gate) = false)
    (hkeep : keepSize keep ≤ budget+1-m)
    (hdisjoint : (childState m P N i j keep gate).2.1 &&&
      (childState m P N i j keep gate).2.2 = 0) :
    childState m P N i j keep gate ∈ filteredChildren budget (m,P,N) := by
  apply List.mem_flatMap.mpr
  refine ⟨j, by simp [hj], List.mem_flatMap.mpr ?_⟩
  refine ⟨i, by simp [hij], List.mem_flatMap.mpr ?_⟩
  refine ⟨gate, by simp, ?_⟩
  simp only [hred, Bool.false_eq_true, ite_false, List.mem_filter, List.mem_map,
    decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨keep,⟨by simp,hkeep⟩,rfl⟩,hdisjoint⟩

lemma filteredCoordinateCover {width k : Nat}
    {target goal a b z : BitVec width} {anchor : Fin width}
    {state : Nat × Nat × Nat} {ws r front : List (BitVec width)}
    (hg : goal = target ∨ goal = ~~~target)
    (hn : ws.Nodup) (rep : Rep target anchor (k+1) state ws)
    (hpair : (a,b,r) ∈ SearchKernel.pairs ws)
    (hfront : front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width))))
    (hz : z ∈ basicOps a b) (fresh : z ∉ ws.toFinset)
    (tail : live basicOps goal k (z :: (front ++ r)).toFinset) :
    ∃ child ∈ filteredChildren (k+1) state,
      ∃ ys, Rep target anchor k child ys ∧ ys.Perm (z :: (front ++ r)) := by
  obtain ⟨m,P,N⟩ := state
  obtain ⟨i,j,keep,gate,hij,hj,hred,hkeep,hdisjoint,ys,hrep,hp⟩ :=
    transitionCover_guards hg hn rep hpair hfront hz fresh tail
  exact ⟨childState m P N i j keep gate,
    childState_mem_filtered keep gate hij hj hred
      (by simpa [Nat.add_assoc] using hkeep) hdisjoint,ys,hrep,hp⟩

lemma filtered_liveState_step {width : Nat} {target goal : BitVec width}
    {anchor : Fin width} (hg : goal = target ∨ goal = ~~~target)
    (k : Nat) (s : Nat × Nat × Nat)
    (run : PNQuotient.liveState (Rep target anchor) goal (k+1) s) :
    solved s.1 s.2.1 s.2.2 = true ∨ ∃ t ∈ filteredChildren (k+1) s,
      PNQuotient.liveState (Rep target anchor) goal k t := by
  apply PNQuotient.liveState_step (children := filteredChildren)
    (fun _ _ hrep => solved_singleton hg hrep) ?_ run
  intro k s ws a b z r front hn hrep hpair hfront hz fresh tail
  exact filteredCoordinateCover hg hn hrep hpair hfront hz fresh tail

lemma filtered_search_complete {width : Nat} {target goal : BitVec width}
    {anchor : Fin width} {admissible : Nat → (Nat × Nat × Nat) → Bool}
    (hg : goal = target ∨ goal = ~~~target)
    (allowed : ∀ k s, PNQuotient.liveState (Rep target anchor) goal (k+1) s →
      admissible (k+1) s = true)
    {k : Nat} {s : Nat × Nat × Nat}
    (run : PNQuotient.liveState (Rep target anchor) goal k s) :
    PNQuotient.search (fun state => solved state.1 state.2.1 state.2.2)
      admissible filteredChildren k s = true :=
  PNQuotient.search_complete (fun _ _ hrep => solved_singleton hg hrep)
    (filtered_liveState_step hg) allowed run

end PNConcrete


namespace NatFlip

lemma xor_pow_of_testBit_false {r i : Nat} (hr : r.testBit i = false) :
    r ^^^ 2 ^ i = r + 2 ^ i := by
  have hpow : 0 < 2 ^ i := Nat.two_pow_pos i
  have hbit : (r / 2 ^ i).testBit 0 = false := by
    simpa only [Nat.testBit_div_two_pow, Nat.zero_add] using hr
  have heven : Even (r / 2 ^ i) :=
    Nat.even_iff.mpr (Nat.mod_two_eq_zero_iff_testBit_zero.mpr hbit)
  have hdiv : (r ^^^ 2 ^ i) / 2 ^ i = r / 2 ^ i + 1 := by
    rw [Nat.xor_div_two_pow, Nat.div_self hpow, Nat.xor_one_of_even heven]
  have hmod : (r ^^^ 2 ^ i) % 2 ^ i = r % 2 ^ i := by
    rw [Nat.xor_mod_two_pow, Nat.mod_self, Nat.xor_zero]
  calc
    r ^^^ 2 ^ i = (r ^^^ 2 ^ i) % 2 ^ i + 2 ^ i * ((r ^^^ 2 ^ i) / 2 ^ i) :=
      (Nat.mod_add_div _ _).symm
    _ = r % 2 ^ i + 2 ^ i * (r / 2 ^ i + 1) := by rw [hmod, hdiv]
    _ = r + 2 ^ i := by
      rw [Nat.mul_add, Nat.mul_one, ← Nat.add_assoc, Nat.mod_add_div]

lemma xor_pow_of_testBit_true {r i : Nat} (hr : r.testBit i = true) :
    r ^^^ 2 ^ i = r - 2 ^ i := by
  have hbit : (r ^^^ 2 ^ i).testBit i = false := by
    simp [Nat.testBit_xor, hr]
  have h := xor_pow_of_testBit_false hbit
  rw [Nat.xor_xor_cancel_right] at h
  omega

lemma testBit_sub_pow {r i : Nat} (h : 2 ^ i ≤ r) :
    (r - 2 ^ i).testBit i = !r.testBit i := by
  have hflip := Nat.testBit_two_pow_add_eq (r - 2 ^ i) i
  rw [Nat.add_sub_of_le h] at hflip
  simpa using (congrArg Bool.not hflip).symm

def flipCoordinate (B mask i : Nat) : Nat :=
  ((B &&& mask) <<< (2 ^ i)) ||| ((B >>> (2 ^ i)) &&& mask)

lemma flipCoordinate_testBit (B mask i N r : Nat)
    (hmask : ∀ t < N, mask.testBit t = !t.testBit i)
    (hr : r < N) :
    (flipCoordinate B mask i).testBit r = B.testBit (r ^^^ 2 ^ i) := by
  simp only [flipCoordinate, Nat.testBit_or, Nat.testBit_shiftLeft,
    Nat.testBit_shiftRight, Nat.testBit_and]
  have hm := hmask r hr
  cases hbit : r.testBit i with
  | false =>
    rw [xor_pow_of_testBit_false hbit]
    by_cases hle : 2 ^ i ≤ r
    · have hs : r - 2 ^ i < N := (Nat.sub_le r _).trans_lt hr
      have hms := hmask (r - 2 ^ i) hs
      have hsub := testBit_sub_pow hle
      simp [hle, hm, hms, hsub, hbit, Nat.add_comm]
    · simp [hle, hm, hbit, Nat.add_comm]
  | true =>
    rw [xor_pow_of_testBit_true hbit]
    have hle : 2 ^ i ≤ r := Nat.ge_two_pow_of_testBit hbit
    have hs : r - 2 ^ i < N := (Nat.sub_le r _).trans_lt hr
    have hms := hmask (r - 2 ^ i) hs
    have hsub := testBit_sub_pow hle
    simp [hle, hm, hms, hsub, hbit]

lemma flipCoordinate_testBit_of_mask (B mask m i r : Nat)
    (hmask : ∀ t, mask.testBit t = decide (t < 2 ^ m ∧ t.testBit i = false))
    (hr : r < 2 ^ m) :
    (flipCoordinate B mask i).testBit r = B.testBit (r ^^^ 2 ^ i) := by
  apply flipCoordinate_testBit B mask i (2 ^ m) r ?_ hr
  intro t ht
  simp [hmask, ht]

end NatFlip

namespace PNFlip

def flipPatternBits (i B : Nat) : Nat :=
  let mask := PNMasks.lowMasks[i]!
  let shift := 1 <<< i
  ((B &&& mask) <<< shift) ||| ((B >>> shift) &&& mask)

lemma flipPatternBits_testBit (i : Fin 10) (r : Fin 1024) (B : Nat) :
    (flipPatternBits i.val B).testBit r.val = B.testBit (r.val ^^^ 2^i.val) := by
  unfold flipPatternBits
  rw [← PnProjection.lowMask_getBang i, Nat.one_shiftLeft]
  apply NatFlip.flipCoordinate_testBit B (PNMasks.lowMask i.val) i.val 1024 r.val ?_ r.isLt
  intro t ht
  exact PNMasks.lowMask_bits i ⟨t,ht⟩

lemma flipPatternBits_testBit_bounded {m i r : Nat} (hm : m ≤ 10) (hi : i < m)
    (hr : r < 2^m) (B : Nat) :
    (flipPatternBits i B).testBit r = B.testBit (r ^^^ 2^i) := by
  have hi10 : i < 10 := by omega
  have hr1024 : r < 1024 := lt_of_lt_of_le hr
    (by exact Nat.pow_le_pow_right (by decide) hm)
  exact flipPatternBits_testBit ⟨i,hi10⟩ ⟨r,hr1024⟩ B

end PNFlip



namespace BitmapCollision

def collisionMask (flip : Nat → Nat) (domainBits P N G : Nat) : Nat :=
  (P &&& flip N) &&& (domainBits ^^^ (G ^^^ flip G))

lemma collisionMask_testBit (flip delta : Nat → Nat) (domainBits P N G p : Nat)
    (hflip : ∀ B, (flip B).testBit p = B.testBit (delta p))
    (hdomain : domainBits.testBit p = true) :
    (collisionMask flip domainBits P N G).testBit p = true ↔
      P.testBit p = true ∧ N.testBit (delta p) = true ∧
        G.testBit p = G.testBit (delta p) := by
  simp only [collisionMask, Nat.testBit_and, Nat.testBit_xor, hflip, hdomain]
  cases P.testBit p <;> cases N.testBit (delta p) <;>
    cases G.testBit p <;> cases G.testBit (delta p) <;> decide

lemma collisionMask_ne_zero_iff (flip delta : Nat → Nat) (domainBits P N G : Nat)
    (hflip : ∀ B q, P.testBit q = true → (flip B).testBit q = B.testBit (delta q))
    (hsupport : ∀ p, P.testBit p = true → domainBits.testBit p = true) :
    collisionMask flip domainBits P N G ≠ 0 ↔
      ∃ p, P.testBit p = true ∧ N.testBit (delta p) = true ∧
        G.testBit p = G.testBit (delta p) := by
  constructor
  · intro hnonzero
    obtain ⟨p, hp⟩ := Nat.exists_testBit_of_ne_zero hnonzero
    have hP : P.testBit p = true := by
      have h := hp
      simp only [collisionMask, Nat.testBit_and, Bool.and_eq_true] at h
      exact h.1.1
    exact ⟨p, (collisionMask_testBit flip delta domainBits P N G p
      (fun B => hflip B p hP) (hsupport p hP)).mp hp⟩
  · rintro ⟨p, hp, hn, hg⟩ hzero
    have h := (collisionMask_testBit flip delta domainBits P N G p
      (fun B => hflip B p hp) (hsupport p hp)).mpr ⟨hp, hn, hg⟩
    simp only [hzero, Nat.zero_testBit, Bool.false_eq_true] at h

lemma selfMask_ne_zero_iff (flip delta : Nat → Nat) (P N G : Nat)
    (hflip : ∀ B q, P.testBit q = true → (flip B).testBit q = B.testBit (delta q)) :
    collisionMask flip P P N G ≠ 0 ↔
      ∃ p, P.testBit p = true ∧ N.testBit (delta p) = true ∧
        G.testBit p = G.testBit (delta p) :=
  collisionMask_ne_zero_iff flip delta P P N G hflip (fun _ hp => hp)

lemma projected_overlap_of_collision
    (flip delta f : Nat → Nat) (domainBits P N G projectedP projectedN : Nat)
    (hflip : ∀ B q, P.testBit q = true → (flip B).testBit q = B.testBit (delta q))
    (hsupport : ∀ p, P.testBit p = true → domainBits.testBit p = true)
    (himageP : ∀ q, projectedP.testBit q = true ↔
      ∃ p, P.testBit p = true ∧ f p = q)
    (himageN : ∀ q, projectedN.testBit q = true ↔
      ∃ p, N.testBit p = true ∧ f p = q)
    (hmap : ∀ p, P.testBit p = true → N.testBit (delta p) = true →
      G.testBit p = G.testBit (delta p) → f p = f (delta p))
    (hnonzero : collisionMask flip domainBits P N G ≠ 0) :
    projectedP &&& projectedN ≠ 0 := by
  obtain ⟨p, hp, hn, hg⟩ :=
    (collisionMask_ne_zero_iff flip delta domainBits P N G hflip hsupport).mp hnonzero
  have hP : projectedP.testBit (f p) = true :=
    (himageP (f p)).mpr ⟨p, hp, rfl⟩
  have hN : projectedN.testBit (f p) = true :=
    (himageN (f p)).mpr ⟨delta p, hn, (hmap p hp hn hg).symm⟩
  intro hzero
  have hbit : (projectedP &&& projectedN).testBit (f p) = true := by
    simp only [Nat.testBit_and, hP, hN, Bool.and_self]
  simp only [hzero, Nat.zero_testBit, Bool.false_eq_true] at hbit

lemma projected_overlap_of_selfMask
    (flip delta f : Nat → Nat) (P N G projectedP projectedN : Nat)
    (hflip : ∀ B q, P.testBit q = true → (flip B).testBit q = B.testBit (delta q))
    (himageP : ∀ q, projectedP.testBit q = true ↔
      ∃ p, P.testBit p = true ∧ f p = q)
    (himageN : ∀ q, projectedN.testBit q = true ↔
      ∃ p, N.testBit p = true ∧ f p = q)
    (hmap : ∀ p, P.testBit p = true → N.testBit (delta p) = true →
      G.testBit p = G.testBit (delta p) → f p = f (delta p))
    (hnonzero : collisionMask flip P P N G ≠ 0) :
    projectedP &&& projectedN ≠ 0 :=
  projected_overlap_of_collision flip delta f P P N G projectedP projectedN
    hflip (fun _ hp => hp) himageP himageN hmap hnonzero

end BitmapCollision

namespace PNDropFlip

open PnProjection PnTransition

lemma delBit_xor_self (i x : Nat) : delBit i (x ^^^ 2^i) = delBit i x := by
  apply Nat.eq_of_testBit_eq
  intro k
  rw [testBit_delBit, Nat.testBit_xor, testBit_delBit, Nat.testBit_two_pow]
  have hne : i ≠ (if k < i then k else k+1) := by
    split_ifs <;> omega
  simp [hne]

lemma delBit_xor_below {i j : Nat} (hij : i < j) (x : Nat) :
    delBit j (x ^^^ 2^i) = (delBit j x) ^^^ 2^i := by
  apply Nat.eq_of_testBit_eq
  intro k
  simp only [testBit_delBit, Nat.testBit_xor, Nat.testBit_two_pow]
  by_cases hk : k < j
  · simp [hk]
  · have hne : i ≠ k := by omega
    have hne' : i ≠ k+1 := by omega
    simp [hk, hne, hne']

lemma dropPattern_xor_left {i j : Nat} (hij : i < j) (keep : Fin 4)
    (hdrop : keep.val &&& 1 = 0) (x : Nat) :
    dropPattern i j keep (x ^^^ 2^i) = dropPattern i j keep x := by
  by_cases hk : keep.val &&& 2 = 0
  · simp [dropPattern, hdrop, hk, delBit_xor_below hij, delBit_xor_self]
  · simp [dropPattern, hdrop, hk, delBit_xor_self]

lemma dropPattern_xor_right (i j : Nat) (keep : Fin 4)
    (hdrop : keep.val &&& 2 = 0) (x : Nat) :
    dropPattern i j keep (x ^^^ 2^j) = dropPattern i j keep x := by
  simp [dropPattern, hdrop, delBit_xor_self]

lemma dropPattern_xor_both {i j : Nat} (hij : i < j) (x : Nat) :
    dropPattern i j (0 : Fin 4) ((x ^^^ 2^i) ^^^ 2^j) = dropPattern i j 0 x := by
  rw [dropPattern_xor_right i j 0 (by decide), dropPattern_xor_left hij 0 (by decide)]

lemma dropPattern_xor_both_mask {i j : Nat} (hij : i < j) (x : Nat) :
    dropPattern i j (0 : Fin 4) (x ^^^ (2^i ^^^ 2^j)) = dropPattern i j 0 x := by
  rw [← Nat.xor_assoc]
  exact dropPattern_xor_both hij x

end PNDropFlip

namespace PNFlipRows

lemma xor_power_bound {m i r : Nat} (hi : i < m) (hr : r < 2^m) :
    r ^^^ 2^i < 2^m :=
  Nat.xor_lt_two_pow hr (Nat.pow_lt_pow_right (by decide) hi)

lemma flipPatternBits_twice_testBit {m i j r : Nat} (hm : m ≤ 10)
    (hi : i < m) (hj : j < m) (hr : r < 2^m) (B : Nat) :
    (PNFlip.flipPatternBits i (PNFlip.flipPatternBits j B)).testBit r =
      B.testBit ((r ^^^ 2^i) ^^^ 2^j) := by
  rw [PNFlip.flipPatternBits_testBit_bounded hm hi hr,
    PNFlip.flipPatternBits_testBit_bounded hm hj (xor_power_bound hi hr)]

lemma gateMask_testBit_bounded {m i j r : Nat} (hm : m ≤ 10)
    (hi : i < m) (hj : j < m) (hr : r < 2^m) (op : Fin 4) :
    (PNPlanes.gateMask i j op).testBit r =
      ChromGate.eval op (r.testBit i) (r.testBit j) := by
  have hr1024 : r < 1024 := lt_of_lt_of_le hr
    (by exact Nat.pow_le_pow_right (by decide) hm)
  exact PNPlanes.gateMask_bits ⟨i, by omega⟩ ⟨j, by omega⟩ op ⟨r, hr1024⟩

lemma gateMask_xor_left {m i j r : Nat} (hm : m ≤ 10)
    (hij : i < j) (hj : j < m) (hr : r < 2^m) (op : Fin 4) :
    (PNPlanes.gateMask i j op).testBit (r ^^^ 2^i) =
      ChromGate.eval op (!(r.testBit i)) (r.testBit j) := by
  rw [gateMask_testBit_bounded hm (by omega) hj (xor_power_bound (by omega) hr)]
  simp [Nat.testBit_xor, Nat.ne_of_lt hij]

lemma gateMask_xor_right {m i j r : Nat} (hm : m ≤ 10)
    (hij : i < j) (hj : j < m) (hr : r < 2^m) (op : Fin 4) :
    (PNPlanes.gateMask i j op).testBit (r ^^^ 2^j) =
      ChromGate.eval op (r.testBit i) (!(r.testBit j)) := by
  rw [gateMask_testBit_bounded hm (by omega) hj (xor_power_bound hj hr)]
  simp [Nat.testBit_xor, Nat.ne_of_gt hij]

lemma gateMask_xor_both {m i j r : Nat} (hm : m ≤ 10)
    (hij : i < j) (hj : j < m) (hr : r < 2^m) (op : Fin 4) :
    (PNPlanes.gateMask i j op).testBit ((r ^^^ 2^i) ^^^ 2^j) =
      ChromGate.eval op (!(r.testBit i)) (!(r.testBit j)) := by
  rw [gateMask_testBit_bounded hm (by omega) hj
    (xor_power_bound hj (xor_power_bound (by omega) hr))]
  simp [Nat.testBit_xor, Nat.ne_of_lt hij, Nat.ne_of_gt hij]

lemma gateMask_xor_both_mask {m i j r : Nat} (hm : m ≤ 10)
    (hij : i < j) (hj : j < m) (hr : r < 2^m) (op : Fin 4) :
    (PNPlanes.gateMask i j op).testBit (r ^^^ (2^i ^^^ 2^j)) =
      ChromGate.eval op (!(r.testBit i)) (!(r.testBit j)) := by
  rw [← Nat.xor_assoc]
  exact gateMask_xor_both hm hij hj hr op

end PNFlipRows

namespace PNGateSpecs

open PNPlanes

def gateSpec (i j : Nat) (d : Fin 4) : Nat × Nat × Nat × Nat :=
  let li := PNMasks.lowMask i
  let lj := PNMasks.lowMask j
  let hi := highMask i
  let hj := highMask j
  let different := hi ^^^ hj
  let same := allPatterns ^^^ different
  match d.val with
  | 0 => (hi &&& hj, lj, li, different)
  | 1 => (hi ||| hj, hj, hi, different)
  | 2 => (hi &&& lj, hj, li, same)
  | _ => (hj &&& li, lj, hi, same)

lemma gateSpec_gate (i j : Nat) (d : Fin 4) :
    (gateSpec i j d).1 = gateMask i j d := by
  fin_cases d <;> rfl

lemma allPatterns_bits (x : Fin 1024) : allPatterns.testBit x.val = true := by
  simp [allPatterns, x.isLt]

lemma gateSpec_samei_bits (i j : Fin 10) (x : Fin 1024) (d : Fin 4) :
    (gateSpec i.val j.val d).2.1.testBit x.val =
      decide (ChromGate.eval d (x.val.testBit i.val) (x.val.testBit j.val) =
        ChromGate.eval d (!(x.val.testBit i.val)) (x.val.testBit j.val)) := by
  fin_cases d <;>
    simp only [gateSpec, ChromGate.eval, highMask_bits, PNMasks.lowMask_bits] <;>
    cases x.val.testBit i.val <;> cases x.val.testBit j.val <;> rfl

lemma gateSpec_samej_bits (i j : Fin 10) (x : Fin 1024) (d : Fin 4) :
    (gateSpec i.val j.val d).2.2.1.testBit x.val =
      decide (ChromGate.eval d (x.val.testBit i.val) (x.val.testBit j.val) =
        ChromGate.eval d (x.val.testBit i.val) (!(x.val.testBit j.val))) := by
  fin_cases d <;>
    simp only [gateSpec, ChromGate.eval, highMask_bits, PNMasks.lowMask_bits] <;>
    cases x.val.testBit i.val <;> cases x.val.testBit j.val <;> rfl

lemma gateSpec_sameij_bits (i j : Fin 10) (x : Fin 1024) (d : Fin 4) :
    (gateSpec i.val j.val d).2.2.2.testBit x.val =
      decide (ChromGate.eval d (x.val.testBit i.val) (x.val.testBit j.val) =
        ChromGate.eval d (!(x.val.testBit i.val)) (!(x.val.testBit j.val))) := by
  fin_cases d <;>
    simp only [gateSpec, ChromGate.eval, Nat.testBit_xor, highMask_bits, allPatterns_bits] <;>
    cases x.val.testBit i.val <;> cases x.val.testBit j.val <;> rfl

end PNGateSpecs

namespace PNKeepLogic

def validKeep (keep ci cj cij samei samej sameij : Nat) : Bool :=
  if keep == 3 then true
  else if keep == 1 then cj &&& samej == 0
  else if keep == 2 then ci &&& samei == 0
  else ci &&& samei == 0 && cj &&& samej == 0 && cij &&& sameij == 0

lemma validKeep_of_checks (keep : Fin 4) (ci cj cij samei samej sameij : Nat)
    (hleft : keep.val &&& 1 = 0 → ci &&& samei = 0)
    (hright : keep.val &&& 2 = 0 → cj &&& samej = 0)
    (hboth : keep.val = 0 → cij &&& sameij = 0) :
    validKeep keep.val ci cj cij samei samej sameij = true := by
  fin_cases keep <;> simp_all [validKeep]

end PNKeepLogic

namespace PNPreCollision

open PnTransition

lemma transition_overlap_of_collision {m i j P N : Nat}
    (hij : i < j) (hj : j < m) (hm : m ≤ 10)
    (hP : P < 2^(2^m)) (hN : N < 2^(2^m)) (keep : Fin 4) (G domainBits : Nat)
    (flip delta : Nat → Nat)
    (hflip : ∀ B p, P.testBit p = true → (flip B).testBit p = B.testBit (delta p))
    (hsupport : ∀ p, P.testBit p = true → domainBits.testBit p = true)
    (hdrop : ∀ p, P.testBit p = true → N.testBit (delta p) = true →
      G.testBit p = G.testBit (delta p) →
      dropPattern i j keep p = dropPattern i j keep (delta p))
    (hbad : BitmapCollision.collisionMask flip domainBits P N G ≠ 0) :
    transitionSet m i j keep G P &&& transitionSet m i j keep G N ≠ 0 := by
  apply BitmapCollision.projected_overlap_of_collision flip delta
    (fun p => dropPattern i j keep p + (if G.testBit p then 2^(m-2+keepSize keep) else 0))
    domainBits P N G _ _ hflip hsupport ?_ ?_ ?_ hbad
  · intro y
    rw [transitionSet_image hij hj hm hP]
    apply exists_congr
    intro p
    exact and_congr_right (fun _ => eq_comm)
  · intro y
    rw [transitionSet_image hij hj hm hN]
    apply exists_congr
    intro p
    exact and_congr_right (fun _ => eq_comm)
  · intro p hp hn hg
    rw [hdrop p hp hn hg, hg]

lemma transition_overlap_of_selfMask {m i j P N : Nat}
    (hij : i < j) (hj : j < m) (hm : m ≤ 10)
    (hP : P < 2^(2^m)) (hN : N < 2^(2^m)) (keep : Fin 4) (G : Nat)
    (flip delta : Nat → Nat)
    (hflip : ∀ B p, P.testBit p = true → (flip B).testBit p = B.testBit (delta p))
    (hdrop : ∀ p, dropPattern i j keep p = dropPattern i j keep (delta p))
    (hbad : BitmapCollision.collisionMask flip P P N G ≠ 0) :
    transitionSet m i j keep G P &&& transitionSet m i j keep G N ≠ 0 :=
  transition_overlap_of_collision hij hj hm hP hN keep G P flip delta hflip
    (fun _ hp => hp) (fun p _ _ _ => hdrop p) hbad

lemma sameMask_zero_of_disjoint {m i j P N : Nat}
    (hij : i < j) (hj : j < m) (hm : m ≤ 10)
    (hP : P < 2^(2^m)) (hN : N < 2^(2^m)) (keep : Fin 4) (G sameMask : Nat)
    (flip delta : Nat → Nat)
    (hflip : ∀ B p, P.testBit p = true → (flip B).testBit p = B.testBit (delta p))
    (hsame : ∀ p, P.testBit p = true → sameMask.testBit p = true →
      G.testBit p = G.testBit (delta p))
    (hdrop : ∀ p, dropPattern i j keep p = dropPattern i j keep (delta p))
    (hdisjoint : transitionSet m i j keep G P &&& transitionSet m i j keep G N = 0) :
    (P &&& flip N) &&& sameMask = 0 := by
  by_contra hbad
  obtain ⟨p, hp⟩ := Nat.exists_testBit_of_ne_zero hbad
  simp only [Nat.testBit_and, Bool.and_eq_true] at hp
  have hNbit : N.testBit (delta p) = true := by
    rw [← hflip N p hp.1.1]
    exact hp.1.2
  have hcollision : BitmapCollision.collisionMask flip P P N G ≠ 0 :=
    (BitmapCollision.selfMask_ne_zero_iff flip delta P N G hflip).mpr
      ⟨p, hp.1.1, hNbit, hsame p hp.1.1 hp.2⟩
  exact transition_overlap_of_selfMask hij hj hm hP hN keep G flip delta hflip hdrop
    hcollision hdisjoint

end PNPreCollision

namespace PNPrecheck

open PnTransition PNPlanes PNFlip PNFlipRows PNGateSpecs

def precheck (i j : Nat) (keep op : Fin 4) (P N : Nat) : Bool :=
  let spec := gateSpec i j op
  let fi := flipPatternBits i N
  let fj := flipPatternBits j N
  PNKeepLogic.validKeep keep.val (P &&& fi) (P &&& fj)
    (P &&& flipPatternBits i fj) spec.2.1 spec.2.2.1 spec.2.2.2

lemma validKeep_of_disjoint {m i j P N : Nat}
    (hij : i < j) (hj : j < m) (hm : m ≤ 10)
    (hP : P < 2^(2^m)) (hN : N < 2^(2^m)) (keep op : Fin 4)
    (hdisjoint : transitionSet m i j keep (gateMask i j op) P &&&
      transitionSet m i j keep (gateMask i j op) N = 0) :
    precheck i j keep op P N = true := by
  have hi : i < m := by omega
  have hi10 : i < 10 := by omega
  have hj10 : j < 10 := by omega
  have pbound (p : Nat) (hp : P.testBit p = true) : p < 2^m :=
    PnProjection.bitIndex_lt hP hp
  have p1024 (p : Nat) (hp : P.testBit p = true) : p < 1024 :=
    lt_of_lt_of_le (pbound p hp) (by exact Nat.pow_le_pow_right (by decide) hm)
  unfold precheck
  apply PNKeepLogic.validKeep_of_checks
  · intro hdrop
    apply PNPreCollision.sameMask_zero_of_disjoint hij hj hm hP hN keep
      (gateMask i j op) (gateSpec i j op).2.1 (flipPatternBits i)
      (fun p => p ^^^ 2^i) ?_ ?_ ?_ hdisjoint
    · intro B p hp
      exact flipPatternBits_testBit_bounded hm hi (pbound p hp) B
    · intro p hp hs
      rw [gateSpec_samei_bits ⟨i,hi10⟩ ⟨j,hj10⟩ ⟨p,p1024 p hp⟩ op] at hs
      rw [gateMask_testBit_bounded hm hi hj (pbound p hp),
        gateMask_xor_left hm hij hj (pbound p hp)]
      exact of_decide_eq_true hs
    · intro p
      exact (PNDropFlip.dropPattern_xor_left hij keep hdrop p).symm
  · intro hdrop
    apply PNPreCollision.sameMask_zero_of_disjoint hij hj hm hP hN keep
      (gateMask i j op) (gateSpec i j op).2.2.1 (flipPatternBits j)
      (fun p => p ^^^ 2^j) ?_ ?_ ?_ hdisjoint
    · intro B p hp
      exact flipPatternBits_testBit_bounded hm hj (pbound p hp) B
    · intro p hp hs
      rw [gateSpec_samej_bits ⟨i,hi10⟩ ⟨j,hj10⟩ ⟨p,p1024 p hp⟩ op] at hs
      rw [gateMask_testBit_bounded hm hi hj (pbound p hp),
        gateMask_xor_right hm hij hj (pbound p hp)]
      exact of_decide_eq_true hs
    · intro p
      exact (PNDropFlip.dropPattern_xor_right i j keep hdrop p).symm
  · intro hzero
    have he : keep = (0 : Fin 4) := Fin.ext hzero
    subst keep
    apply PNPreCollision.sameMask_zero_of_disjoint hij hj hm hP hN 0
      (gateMask i j op) (gateSpec i j op).2.2.2
      (fun B => flipPatternBits i (flipPatternBits j B))
      (fun p => (p ^^^ 2^i) ^^^ 2^j) ?_ ?_ ?_ hdisjoint
    · intro B p hp
      exact flipPatternBits_twice_testBit hm hi hj (pbound p hp) B
    · intro p hp hs
      rw [gateSpec_sameij_bits ⟨i,hi10⟩ ⟨j,hj10⟩ ⟨p,p1024 p hp⟩ op] at hs
      rw [gateMask_testBit_bounded hm hi hj (pbound p hp),
        gateMask_xor_both hm hij hj (pbound p hp)]
      exact of_decide_eq_true hs
    · intro p
      exact (PNDropFlip.dropPattern_xor_both hij p).symm

end PNPrecheck

namespace PNConcrete

open PnTransition PNPlanes PNFlip PNKeepLogic PNGateSpecs

def keepCheck (i j P N : Nat) (keep gate : Fin 4) : Bool :=
  let spec := gateSpec i j gate
  validKeep keep.val (P &&& flipPatternBits i N) (P &&& flipPatternBits j N)
    (P &&& flipPatternBits i (flipPatternBits j N)) spec.2.1 spec.2.2.1 spec.2.2.2

def precheckedChildren (budget : Nat) (state : Nat × Nat × Nat) : List (Nat × Nat × Nat) :=
  (List.range state.1).flatMap fun j =>
    (List.range j).flatMap fun i =>
      let fi := flipPatternBits i state.2.2
      let fj := flipPatternBits j state.2.2
      let ci := state.2.1 &&& fi
      let cj := state.2.1 &&& fj
      let cij := state.2.1 &&& flipPatternBits i fj
      (List.finRange 4).flatMap fun gate =>
        let spec := gateSpec i j gate
        if PNGuards.redundant state.1 (state.2.1 ||| state.2.2) (gateMask i j gate) then [] else
          (((List.finRange 4).filter fun keep =>
            decide (keepSize keep ≤ budget+1-state.1) &&
              validKeep keep.val ci cj cij spec.2.1 spec.2.2.1 spec.2.2.2).map
            fun keep => childState state.1 state.2.1 state.2.2 i j keep gate).filter
              fun child => child.2.1 &&& child.2.2 == 0

lemma childState_mem_prechecked {budget m P N i j : Nat} (keep gate : Fin 4)
    (hij : i < j) (hj : j < m)
    (hred : PNGuards.redundant m (P ||| N) (gateMask i j gate) = false)
    (hkeep : keepSize keep ≤ budget+1-m)
    (hpre : keepCheck i j P N keep gate = true)
    (hdisjoint : (childState m P N i j keep gate).2.1 &&&
      (childState m P N i j keep gate).2.2 = 0) :
    childState m P N i j keep gate ∈ precheckedChildren budget (m,P,N) := by
  apply List.mem_flatMap.mpr
  refine ⟨j, by simp [hj], List.mem_flatMap.mpr ?_⟩
  refine ⟨i, by simp [hij], List.mem_flatMap.mpr ?_⟩
  refine ⟨gate, by simp, ?_⟩
  simp only [hred, Bool.false_eq_true, ite_false, List.mem_filter, List.mem_map,
    Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  exact ⟨⟨keep,⟨by simp,⟨hkeep,hpre⟩⟩,rfl⟩,hdisjoint⟩

lemma rep_bitmap_bound {width k m P N : Nat} {target : BitVec width} {anchor : Fin width}
    {ws : List (BitVec width)} (rep : Rep target anchor k (m,P,N) ws) (value : Bool) :
    (if value then P else N) < 2^(2^m) := by
  apply bitmap_bound (code := PNFrontier.rowCode ws) (label := fun r => target[r.val] = value)
  · intro r
    simpa only [rep.1] using PNFrontier.rowCode_lt ws r
  · exact rep.2.2.2.2 value

lemma precheckedCoordinateCover {width k : Nat}
    {target goal a b z : BitVec width} {anchor : Fin width}
    {state : Nat × Nat × Nat} {ws r front : List (BitVec width)}
    (hg : goal = target ∨ goal = ~~~target)
    (hn : ws.Nodup) (rep : Rep target anchor (k+1) state ws)
    (hpair : (a,b,r) ∈ SearchKernel.pairs ws)
    (hfront : front ∈ ([[], [a], [b], [a,b]] : List (List (BitVec width))))
    (hz : z ∈ basicOps a b) (fresh : z ∉ ws.toFinset)
    (tail : live basicOps goal k (z :: (front ++ r)).toFinset) :
    ∃ child ∈ precheckedChildren (k+1) state,
      ∃ ys, Rep target anchor k child ys ∧ ys.Perm (z :: (front ++ r)) := by
  obtain ⟨m,P,N⟩ := state
  obtain ⟨i,j,keep,gate,hij,hj,hred,hkeep,hdisjoint,ys,hrep,hp⟩ :=
    transitionCover_guards hg hn rep hpair hfront hz fresh tail
  have hpre := PNPrecheck.validKeep_of_disjoint hij hj rep.2.2.1
    (rep_bitmap_bound rep true) (rep_bitmap_bound rep false) keep gate hdisjoint
  exact ⟨childState m P N i j keep gate,
    childState_mem_prechecked keep gate hij hj hred
      (by simpa [Nat.add_assoc] using hkeep) hpre hdisjoint,ys,hrep,hp⟩

lemma prechecked_liveState_step {width : Nat} {target goal : BitVec width}
    {anchor : Fin width} (hg : goal = target ∨ goal = ~~~target)
    (k : Nat) (s : Nat × Nat × Nat)
    (run : PNQuotient.liveState (Rep target anchor) goal (k+1) s) :
    solved s.1 s.2.1 s.2.2 = true ∨ ∃ t ∈ precheckedChildren (k+1) s,
      PNQuotient.liveState (Rep target anchor) goal k t := by
  apply PNQuotient.liveState_step (children := precheckedChildren)
    (fun _ _ hrep => solved_singleton hg hrep) ?_ run
  intro k s ws a b z r front hn hrep hpair hfront hz fresh tail
  exact precheckedCoordinateCover hg hn hrep hpair hfront hz fresh tail

lemma prechecked_search_complete {width : Nat} {target goal : BitVec width}
    {anchor : Fin width} {admissible : Nat → (Nat × Nat × Nat) → Bool}
    (hg : goal = target ∨ goal = ~~~target)
    (allowed : ∀ k s, PNQuotient.liveState (Rep target anchor) goal (k+1) s →
      admissible (k+1) s = true)
    {k : Nat} {s : Nat × Nat × Nat}
    (run : PNQuotient.liveState (Rep target anchor) goal k s) :
    PNQuotient.search (fun state => solved state.1 state.2.1 state.2.2)
      admissible precheckedChildren k s = true :=
  PNQuotient.search_complete (fun _ _ hrep => solved_singleton hg hrep)
    (prechecked_liveState_step hg) allowed run

end PNConcrete


namespace PNConcrete

lemma precheckedChildren_mono {b k : Nat} (hbk : b ≤ k) (state : Nat × Nat × Nat) :
    ∀ child, child ∈ precheckedChildren b state → child ∈ precheckedChildren k state := by
  intro child hchild
  simp only [precheckedChildren, List.mem_flatMap] at hchild ⊢
  obtain ⟨j, hj, i, hi, gate, hgate, hchild⟩ := hchild
  refine ⟨j, hj, i, hi, gate, hgate, ?_⟩
  split_ifs at hchild with hred
  · cases hchild
  · simp only [hred, Bool.false_eq_true, ite_false]
    simp only [List.mem_filter, List.mem_map, Bool.and_eq_true, decide_eq_true_eq] at hchild ⊢
    obtain ⟨⟨keep, ⟨hkeep, hbound, hpre⟩, heq⟩, hdisjoint⟩ := hchild
    exact ⟨⟨keep, ⟨hkeep, by omega, hpre⟩, heq⟩, hdisjoint⟩

lemma filteredChildren_mono {b k : Nat} (hbk : b ≤ k) (state : Nat × Nat × Nat) :
    ∀ child, child ∈ filteredChildren b state → child ∈ filteredChildren k state := by
  intro child hchild
  simp only [filteredChildren, List.mem_flatMap] at hchild ⊢
  obtain ⟨j, hj, i, hi, gate, hgate, hchild⟩ := hchild
  refine ⟨j, hj, i, hi, gate, hgate, ?_⟩
  split_ifs at hchild with hred
  · cases hchild
  · simp only [hred, Bool.false_eq_true, ite_false]
    simp only [List.mem_filter, List.mem_map, decide_eq_true_eq] at hchild ⊢
    obtain ⟨⟨keep, ⟨hkeep, hbound⟩, heq⟩, hdisjoint⟩ := hchild
    exact ⟨⟨keep, ⟨hkeep, by omega⟩, heq⟩, hdisjoint⟩

end PNConcrete



-- Extracted from the independently checked, compacted L_meta_10538 certificate.
namespace RestrictionSixProof
open PEqualNP.CircuitLowerBounds
abbrev Sig := BitVec 128
def zero : Sig := 0
def one : Sig := BitVec.allOnes 128
def neg (a : Sig) : Sig := ~~~a
def bin (d : Nat) (a b : Sig) : Sig :=
  if d=0 then a &&& b else if d=1 then a ||| b else if d=2 then a &&& ~~~b else ~~~a &&& b
def proper (a : Sig) : Prop := a ≠ zero ∧ a ≠ one
def allowed (u : Bool) (d : Nat) : Prop := d<2 ∨ (u=true ∧ d<4)
def flipOp (d : Nat) := if d=2 then 3 else if d=3 then 2 else d
lemma allowed_four {u d} (h : allowed u d) : d=0 ∨ d=1 ∨ (u=true ∧ d=2) ∨ (u=true ∧ d=3) := by
  rcases h with h | ⟨h,j⟩
  · omega
  · have : d=0 ∨ d=1 ∨ d=2 ∨ d=3 := by omega
    rcases this with h1 | h1 | h1 | h1
    · exact Or.inl h1
    · exact Or.inr (Or.inl h1)
    · exact Or.inr (Or.inr (Or.inl ⟨h,h1⟩))
    · exact Or.inr (Or.inr (Or.inr ⟨h,h1⟩))
lemma bin_flip {u d} (h : allowed u d) (a b : Sig) : bin d a b = bin (flipOp d) b a := by
  rcases allowed_four h with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;> simp [bin,flipOp,BitVec.and_comm,BitVec.or_comm]
lemma flip_flip {u d} (h : allowed u d) : allowed u (flipOp d) ∧ flipOp (flipOp d)=d := by
  rcases allowed_four h with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  all_goals simp_all [flipOp,allowed]

def Live (u : Bool) (target : Sig) : Nat → Finset Sig → Prop
  | 0,S => S={target} ∧ proper target
  | k+1,S => ∃ (U : Finset Sig) (a b : Sig) (d : Nat), allowed u d ∧ S=insert a (insert b U) ∧
      proper a ∧ proper b ∧ a ≠ b ∧
      bin d a b ∉ insert a (insert b U) ∧ Live u target k (insert (bin d a b) U)
lemma Live.stop {u} {target : Sig} (hp : proper target) : Live u target 0 {target} := ⟨rfl,hp⟩
lemma Live.binary {u} {target : Sig} {k : Nat} {U : Finset Sig} {a b : Sig} {d : Nat} (hd : allowed u d)
    (ha : proper a) (hb : proper b) (hab : a ≠ b)
    (hfresh : bin d a b ∉ insert a (insert b U)) (tail : Live u target k (insert (bin d a b) U)) :
    Live u target (k+1) (insert a (insert b U)) :=
  ⟨U,a,b,d,hd,rfl,ha,hb,hab,hfresh,tail⟩
lemma Live.ind {u} {target : Sig} {motive : ∀ (k : Nat) (S : Finset Sig), Live u target k S → Prop}
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

def bit (i : Fin 128) (a : Sig) : Bool := a.getLsbD i.val
private lemma bit_zero (i) : bit i zero = false := by simp [bit,zero]
private lemma bit_one (i) : bit i one = true := by unfold bit one; rw [BitVec.getLsbD_allOnes]; simp
private lemma bit_neg (i) (a : Sig) : bit i (neg a) = !(bit i a) := by simp [bit,neg,i.isLt]
private lemma bit_bin (i d) (a b : Sig) : bit i (bin d a b) =
    (if d=0 then bit i a && bit i b else if d=1 then bit i a || bit i b else
      if d=2 then bit i a && !(bit i b) else !(bit i a) && bit i b) := by
  unfold bin
  split_ifs <;> simp [bit]
lemma bit_ext {a b : Sig} (h : ∀ i, bit i a = bit i b) : a=b :=
  BitVec.eq_of_getLsbD_eq fun j hj => h ⟨j,hj⟩

def nrm (u : Bool) (a : Sig) : Sig := if u && bit 0 a then neg a else a
lemma nrm_false (a : Sig) : nrm false a = a := rfl
lemma nrm_bit (a : Sig) : bit 0 (nrm true a) = false := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg]
lemma nrm_id {u} {a : Sig} (h : bit 0 a = false) : nrm u a = a := by simp [nrm,h]
lemma neg_neg' (a : Sig) : neg (neg a) = a := by simp [neg]
lemma nrm_neg (a : Sig) : nrm true (neg a) = nrm true a := by
  cases h : bit 0 a <;> simp [nrm,h,bit_neg,neg_neg']
lemma proper_neg {a : Sig} (h : proper (neg a)) : proper a := by
  refine ⟨?_,?_⟩
  · rintro rfl
    exact h.2 (by simp [neg,zero,one])
  · rintro rfl
    exact h.1 (by simp [neg,zero,one])
lemma proper_nrm {u} {a : Sig} (h : proper (nrm u a)) : proper a := by
  unfold nrm at h
  split at h
  · exact proper_neg h
  · exact h
def prime (d : Bool) (a b : Sig) := if d then a ||| b else a &&& b
lemma bit_prime (i) (d : Bool) (a b : Sig) : bit i (prime d a b) =
    (if d then bit i a || bit i b else bit i a && bit i b) := by cases d <;> simp [prime,bit]
lemma nrm_prime (d : Bool) (a b : Sig) :
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

lemma norm_ne_one (a : Sig) : nrm true a ≠ one := by
  intro h
  have := nrm_bit a
  rw [h,bit_one] at this
  exact Bool.noConfusion this
lemma prime_rep {u w a b} (d : Bool) (ha : Repr u w a) (hb : Repr u w b) :
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
lemma repr_const {u w} {v : Sig} (h : v=zero ∨ v=one) : Repr u w v := by
  refine Or.inr fun hp => ?_
  have := proper_nrm hp
  rcases h with rfl | rfl
  · exact this.1 rfl
  · exact this.2 rfl
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
lemma Reach.start {R u} {roots : List (Wire R)} : Reach u roots 0 roots := rfl
lemma Reach.two {R u} {roots : List (Wire R)} {p bank a b} (op : Bool) (h : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) : Reach u roots (p+1) (combine op a b :: bank) :=
  ⟨op,bank,a,b,h,ha,hb,rfl⟩
lemma Reach.ind {R u} {roots : List (Wire R)} {motive : ∀ p bank, Reach u roots p bank → Prop}
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
lemma Run.stop {R u} {goal : Wire R} : Run u goal 0 [goal] := List.Perm.refl _
lemma Run.perm {R u} {goal : Wire R} {s : Nat} {xs zs : List (Wire R)} (p : xs.Perm zs)
    (h : Run u goal s xs) : Run u goal s zs := by
  cases s with
  | zero => exact List.Perm.trans h p
  | succ s =>
    obtain ⟨op,ka,kb,a,b,rest,hd,q,h⟩ := h
    exact ⟨op,ka,kb,a,b,rest,hd,q.trans p,h⟩
lemma Run.two {R u} {goal : Wire R} {s : Nat} {a b : Wire R} {rest : List (Wire R)} (op : Nat) (hd : allowed u op) (ka kb : Bool)
    (h : Run u goal s (comb op a b :: kept ka a (kept kb b rest))) : Run u goal (s+1) (a::b::rest) :=
  ⟨op,ka,kb,a,b,rest,hd,List.Perm.refl _,h⟩
lemma Run.ind {R u} {goal : Wire R} {motive : ∀ s ws, Run u goal s ws → Prop}
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

lemma mass_cons {R} (a : Wire R) (xs) : mass (a::xs)=cost a + mass xs := by
  simp [mass]

lemma mass_kept {R} (a : Wire R) (xs) (k : Bool) : mass xs ≤ mass (kept k a xs) := by
  cases k <;> simp [kept,mass_cons]

lemma inv_constant {R} {a : Wire R} (h : Constant a) : Constant (inv a) := by
  obtain ⟨v,rfl⟩ := h
  exact ⟨!v,rfl⟩

lemma inv_inv' {R} (a : Wire R) : inv (inv a)=a := by
  funext r
  simp [inv]
lemma cost_inv {R} (a : Wire R) : cost (inv a)=cost a := by
  have : Constant (inv a) ↔ Constant a := ⟨fun h => inv_inv' a ▸ inv_constant h,inv_constant⟩
  by_cases h : Constant a
  · simp only [cost,if_pos h,if_pos (this.mpr h)]
  · simp only [cost,if_neg h,if_neg (fun x => h (this.mp x))]
lemma avail_inv {R u} {bank : List (Wire R)} {a} (hu : u=true) (h : Available u bank a) : Available u bank (inv a) := by
  rcases h with h | h | ⟨_,h⟩
  · exact Or.inr (Or.inr ⟨hu,(inv_inv' a).symm ▸ h⟩)
  · exact Or.inr (Or.inl (inv_constant h))
  · exact Or.inl h
lemma both_constant {R} {a b : Wire R} (op) (h : Constant a) (g : Constant b) :
    Constant (combine op a b) := by
  obtain ⟨v,rfl⟩ := h
  obtain ⟨w,rfl⟩ := g
  cases op <;> exact ⟨_,rfl⟩

lemma from_constant {R u} (op) {a b : Wire R} {bank}
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

lemma available_cons {R u} {bank v} (w : Wire R) (h : Available u bank v) :
    Available u (w::bank) v :=
  h.imp (List.mem_cons_of_mem _) (Or.imp id (And.imp id (List.mem_cons_of_mem _)))

lemma extend_two {R u} (roots : List (Wire R)) {p bank a b} (op) (hp : Reach u roots p bank)
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
lemma comb_prime {R u} {bank : List (Wire R)} {d a b} (hd : allowed u d) (ha : Available u bank a) (hb : Available u bank b) :
    ∃ op x y, comb d a b=combine op x y ∧ Available u bank x ∧ Available u bank y ∧ cost x=cost a ∧ cost y=cost b := by
  rcases allowed_four hd with rfl | rfl | ⟨hu,rfl⟩ | ⟨hu,rfl⟩
  · exact ⟨false,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨true,a,b,rfl,ha,hb,rfl,rfl⟩
  · exact ⟨false,a,inv b,rfl,ha,avail_inv hu hb,rfl,cost_inv b⟩
  · exact ⟨false,inv a,b,rfl,avail_inv hu ha,hb,cost_inv a,rfl⟩
lemma extend_comb {R u} (roots : List (Wire R)) {p bank a b} (d) (hd : allowed u d) (hp : Reach u roots p bank)
    (ha : Available u bank a) (hb : Available u bank b) :
    ∃ q next, Reach u roots q next ∧ Available u next (comb d a b) ∧
        (∀ v, Available u bank v → Available u next v) ∧
        q+cost a+cost b ≤ p+1+cost (comb d a b) := by
  obtain ⟨op,x,y,e,hx,hy,cx,cy⟩ := comb_prime hd ha hb
  rw [e,←cx,←cy]
  exact extend_two roots op hp hx hy

lemma mem_kept {α : Type} {k : Bool} {x a : α} {xs} (h : x ∈ kept k a xs) :
    x=a ∨ x∈xs := by cases k <;> simp_all [kept]

lemma contraction {R u} {goal : Wire R} (nc : ¬Constant goal) {s ws}
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

lemma restrict_kept {R S : Type} (rows : S → R) (k : Bool) (a : Wire R) (ws) :
    (kept k a ws).map (restrictRows rows) =
    kept k (restrictRows rows a) (ws.map (restrictRows rows)) := by
  cases k <;> simp [kept]

lemma restrict_comb {R S : Type} (rows : S → R) (d) (a b : Wire R) :
    restrictRows rows (comb d a b) = comb d (restrictRows rows a) (restrictRows rows b) := by
  unfold comb
  split_ifs <;> rfl
lemma restrict_run {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws) :
    Run u (restrictRows rows goal) s (ws.map (restrictRows rows)) := by
  induction h using Run.ind with
  | stop => exact Run.stop
  | perm p _ ih => exact Run.perm (p.map _) ih
  | two op hd ka kb _ ih =>
    simp only [List.map_cons,restrict_kept,restrict_comb] at ih ⊢
    exact Run.two op hd ka kb ih

lemma projected_bound {R S : Type} {u} (rows : S → R) {goal s ws} (h : Run u goal s ws)
    (nc : ¬Constant (restrictRows rows goal)) {roots : List (Wire S)} {p bank L}
    (hp : Reach u roots p bank) (hs : supply u bank (ws.map (restrictRows rows)))
    (hl : ∀ q bs, Reach u roots q bs → Available u bs (restrictRows rows goal) → L ≤ q) :
    L + mass (ws.map (restrictRows rows)) ≤ p+s := by
  obtain ⟨q,bs,hq,ht,hle⟩ := contraction nc (restrict_run rows h) roots hp hs
  have hqle := hl q bs hq ht
  omega


abbrev Row := Fin 128
def observe (a : Sig) : Wire Row := fun r => bit r a
def table (f : Wire Row) : Sig :=
  (BitVec.ofBoolListLE (List.ofFn f)).cast (List.length_ofFn)

lemma bit_table (f : Wire Row) (r : Row) : bit r (table f) = f r := by
  simp only [bit,table,BitVec.getLsbD_cast,BitVec.getLsbD_ofBoolListLE,List.getD_eq_getElem?_getD,List.getElem?_ofFn]; simp [r.isLt]

lemma table_observe (v : Sig) : table (observe v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  exact bit_table (observe v) ⟨j,hj⟩

lemma observe_table (f : Wire Row) : observe (table f) = f := by
  funext r
  exact bit_table f r

lemma obs_neg (a : Sig) : observe (neg a) = inv (observe a) := by
  funext r
  exact bit_neg _ _

lemma obs_bin (d : Nat) (a b : Sig) :
    observe (bin d a b) = comb d (observe a) (observe b) := by
  funext r
  simp only [observe,bit_bin,comb]
  split_ifs <;> rfl

lemma map_kept {α β : Type} (f : α → β) (d : Bool) (a : α) (l : List α) :
    (kept d a l).map f = kept d (f a) (l.map f) := by cases d <;> rfl

lemma kept_nd {α : Type} (k : Bool) (a : α) (l : List α)
    (hn : l.Nodup) (ha : a ∉ l) : (kept k a l).Nodup := by cases k <;> simp [kept,hn,ha]

lemma kept_fin (k : Bool) (a : Sig) (l : List Sig) :
    (kept k a l).toFinset = if k then insert a l.toFinset else l.toFinset := by
  cases k <;> simp [kept]

lemma list_run {u} {T : Sig} {k S} (h : Live u T k S) (v : List Sig)
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


lemma table_inv (f : Wire Row) : table (inv f) = neg (table f) := by
  rw [←table_observe (neg (table f)),obs_neg,observe_table]

lemma table_prime (d : Bool) (f g : Wire Row) :
    table (combine d f g) = prime d (table f) (table g) := by
  apply bit_ext
  intro r
  rw [bit_table,bit_prime,bit_table,bit_table]
  cases d <;> rfl

lemma available_rep {u} {bank : List (Wire Row)} {a} (h : Available u bank a) :
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

lemma reach_live_sub {u} {roots : List (Wire Row)} {p bank}
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
lemma nrm_map {u} {w : List Sig} (h : w.all plainWord=true) : w.map (nrm u)=w := by
  have e : w.map (nrm u) = w.map id := by
    apply List.map_congr_left
    intro a ha
    exact nrm_id (by simpa [plainWord] using List.all_eq_true.mp h a ha)
  rw [e,List.map_id]
lemma reach_live {u} {roots : List Sig} {p bank T} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
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

lemma live_row_difference {u T k S} (h : Live u T k S) {r s : Row}
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

lemma raw_required {u T k S} (h : Live u T k S) (roots : List Sig) (a : Sig)
    (sub : ∀ v ∈ S, v ∈ roots) (r s : Row) (diff : bit r T ≠ bit s T)
    (isolated : ∀ v ∈ roots, v ≠ a → bit r v = bit s v) : a ∈ S := by
  obtain ⟨v,hv,hd⟩ := live_row_difference h diff
  by_cases veq : v=a
  · simpa [veq] using hv
  · exact False.elim (hd (isolated v (sub v hv) veq))

def Lower (u : Bool) (roots : List Sig) (T : Sig) (L : Nat) : Prop :=
  ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (observe T) → L ≤ p

def Impossible (u : Bool) (T : Sig) (cap : Nat) (S : Finset Sig) : Prop :=
  ∀ k, k ≤ cap → ¬Live u T k S

def Essential (T : Sig) (roots : List Sig) (a : Sig) : Prop :=
  ∃ r s : Row, bit r T ≠ bit s T ∧ ∀ v ∈ roots, v ≠ a → bit r v = bit s v

lemma lower_impossible {u roots T L} (hp : proper T) (nT : plainWord T=true) (nR : roots.all plainWord=true)
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

lemma observe_proper {v : Sig} (hv : proper v) : ¬Constant (observe v) := by
  rintro ⟨b,h⟩
  have hr : Repr false [] v := by
    apply repr_const
    cases b
    · exact Or.inl (bit_ext fun i => (congrFun h i).trans (bit_zero i).symm)
    · exact Or.inr (bit_ext fun i => (congrFun h i).trans (bit_one i).symm)
  have hr' : represented [] v := hr
  exact (hr'.resolve_left (by simp)) hv



def childTwo (ws : List Sig) (a b : Sig) (d : Nat) (ka kb : Bool) : List Sig :=
  bin d a b :: kept ka a (kept kb b ((ws.erase a).erase b))

lemma erase_fin {l : List Sig} (h : l.Nodup) (a : Sig) : (l.erase a).toFinset = l.toFinset.erase a := by
  ext x
  simp [h.mem_erase_iff]

lemma enum_step {u} {T : Sig} {cap : Nat} {ws : List Sig} (hn : ws.Nodup) (out : T ∉ ws)
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

def Slice (u : Bool) (raw : List Sig) (T d : Sig) (L : Nat) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig), (∀ r, bit (f r) d = true) ∧
    (∀ a ∈ raw, Available u (roots.map observe) (restrictRows f (observe a))) ∧
    ¬Constant (restrictRows f (observe T)) ∧
    ∀ p bank, Reach u (roots.map observe) p bank → Available u bank (restrictRows f (observe T)) → L ≤ p
def W (a : Nat) : Sig := BitVec.ofNat 128 a
def full : Nat := 0xffffffffffffffffffffffffffffffff
def xN : Nat → Nat
  | 0 => 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
  | 1 => 0xcccccccccccccccccccccccccccccccc
  | 2 => 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
  | 3 => 0xff00ff00ff00ff00ff00ff00ff00ff00
  | 4 => 0xffff0000ffff0000ffff0000ffff0000
  | 5 => 0xffffffff00000000ffffffff00000000
  | _ => 0xffffffffffffffff0000000000000000
def nb (o a b : Nat) : Nat :=
  bif Nat.beq o 0 then Nat.land a b else bif Nat.beq o 1 then Nat.lor a b else
    bif Nat.beq o 2 then Nat.xor a (Nat.land a b) else Nat.xor b (Nat.land a b)
lemma bit_W (r : Row) (a : Nat) : bit r (W a) = a.testBit r.val := by
  unfold bit W
  rw [BitVec.getLsbD_ofNat]
  simp [r.isLt]
lemma tb_land (a b i : Nat) : (Nat.land a b).testBit i = (a.testBit i && b.testBit i) := Nat.testBit_and ..
lemma tb_lor (a b i : Nat) : (Nat.lor a b).testBit i = (a.testBit i || b.testBit i) := Nat.testBit_or ..
lemma tb_xor (a b i : Nat) : (Nat.xor a b).testBit i = (a.testBit i ^^ b.testBit i) := Nat.testBit_xor ..
lemma nbeq {a b : Nat} (h : a ≠ b) : Nat.beq a b = false := by
  cases e : Nat.beq a b
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true e) h
lemma W_nb (o a b : Nat) : W (nb o a b) = bin o (W a) (W b) := by
  apply bit_ext
  intro r
  rw [bit_bin,bit_W,bit_W,bit_W]
  by_cases h0 : o = 0
  · subst h0
    exact tb_land a b _
  by_cases h1 : o = 1
  · subst h1
    exact tb_lor a b _
  by_cases h2 : o = 2
  · subst h2
    change (Nat.xor a (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
  · unfold nb
    rw [nbeq h0,nbeq h1,nbeq h2,if_neg h0,if_neg h1,if_neg h2]
    change (Nat.xor b (Nat.land a b)).testBit r.val = _
    rw [tb_xor,tb_land]
    cases a.testBit r.val <;> cases b.testBit r.val <;> rfl
lemma bin_four (o : Nat) : ∃ e, e < 4 ∧ ∀ a b, bin o a b = bin e a b := by
  by_cases h : o < 4
  · exact ⟨o,h,fun _ _ => rfl⟩
  · refine ⟨3,by omega,fun a b => ?_⟩
    have h0 : o ≠ 0 := by omega
    have h1 : o ≠ 1 := by omega
    have h2 : o ≠ 2 := by omega
    simp [bin,h0,h1,h2]
lemma W_full : W full = one := by
  apply bit_ext
  intro r
  rw [bit_W,bit_one]
  revert r
  decide +kernel
lemma W_inj {a b : Nat} (ha : a < 2^128) (hb : b < 2^128) (h : W a = W b) : a = b := by
  have := congrArg BitVec.toNat h
  simpa only [W,BitVec.toNat_ofNat,Nat.mod_eq_of_lt ha,Nat.mod_eq_of_lt hb] using this

def rootsW (R : List Nat) : List Sig := R.map fun i => W (xN i)
def LowN (R : List Nat) (T L : Nat) : Prop := Lower true (rootsW R) (W T) L
abbrev SliceD := Nat × Nat × List Nat
def SliceN (R : List Nat) (T : Nat) (s : SliceD) : Prop :=
  Slice true (rootsW R) (W T) (W s.1) s.2.1 ∧ ∀ v ∈ s.2.2, v ∈ R

def baseOK (T : Nat) (R : List Nat) (E : List (Nat × Nat × Nat)) : Bool :=
  decide (T < 2^128) && !(T.testBit 0) && (E.map Prod.fst == R) && !R.isEmpty && decide (rootsW R).Nodup &&
  R.all (fun i => !((xN i).testBit 0)) &&
  E.all (fun e => decide (e.2.1 < 128) && decide (e.2.2 < 128) && (T.testBit e.2.1 != T.testBit e.2.2) &&
    R.all (fun i => i == e.1 || (xN i).testBit e.2.1 == (xN i).testBit e.2.2))

def BaseP (T : Nat) (R : List Nat) : Prop :=
  T < 2^128 ∧ plainWord (W T) = true ∧ (rootsW R).Nodup ∧
  (rootsW R).all plainWord = true ∧
  (∀ a ∈ rootsW R, Essential (W T) (rootsW R) a) ∧ proper (W T)
namespace BaseP
lemma lt {T R} (h : BaseP T R) : T < 2^128 := h.1
lemma plain {T R} (h : BaseP T R) : plainWord (W T) = true := h.2.1
lemma nodup {T R} (h : BaseP T R) : (rootsW R).Nodup := h.2.2.1
lemma plainR {T R} (h : BaseP T R) : (rootsW R).all plainWord = true := h.2.2.2.1
lemma ess {T R} (h : BaseP T R) : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := h.2.2.2.2.1
lemma prop {T R} (h : BaseP T R) : proper (W T) := h.2.2.2.2.2
end BaseP

lemma baseOK_ok {T R E} (h : baseOK T R E = true) : BaseP T R := by
  simp only [baseOK,Bool.and_eq_true,decide_eq_true_eq,beq_iff_eq,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨hT,h0⟩,hE⟩,hne⟩,nd⟩,pr⟩,he⟩ := h
  have ess : ∀ a ∈ rootsW R, Essential (W T) (rootsW R) a := by
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rw [←hE] at hi
    obtain ⟨e,hem,rfl⟩ := List.mem_map.mp hi
    obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := he e hem
    refine ⟨⟨e.2.1,h1⟩,⟨e.2.2,h2⟩,?_,?_⟩
    · rw [bit_W,bit_W]
      simpa using h3
    · intro v hv hne
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv
      rw [bit_W,bit_W]
      have := h4 j hj
      simp only [Bool.or_eq_true,beq_iff_eq] at this
      rcases this with rfl | this
      · exact absurd rfl hne
      · exact this
  refine ⟨hT,?_,nd,?_,ess,?_⟩
  · have : bit 0 (W T) = false := (bit_W 0 T).trans h0
    simp [plainWord,this]
  · rw [List.all_eq_true]
    intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    have : bit 0 (W (xN i)) = false := (bit_W 0 _).trans (by simpa using pr i hi)
    simp [plainWord,this]
  · cases R with
    | nil => simp at hne
    | cons i R =>
      obtain ⟨r,s,hd,_⟩ := ess (W (xN i)) (by simp [rootsW])
      constructor
      · intro hh
        rw [hh,bit_zero,bit_zero] at hd
        exact hd rfl
      · intro hh
        rw [hh,bit_one,bit_one] at hd
        exact hd rfl

lemma lowOf {T R E K} (hB : baseOK T R E = true) (h : Impossible true (W T) K (rootsW R).toFinset) :
    LowN R T (K+1) := by
  have b := baseOK_ok hB
  exact lower_impossible b.prop b.plain b.plainR b.ess h
lemma lowCount {T R E K} (hB : baseOK T R E = true) (h : K + 2 ≤ R.length) : LowN R T (K+1) := by
  apply lowOf hB
  intro k hk run
  have b := baseOK_ok hB
  have := live_size run
  rw [List.toFinset_card_of_nodup b.nodup,rootsW,List.length_map] at this
  omega

def rowOf : List Nat → Nat → Nat → Nat
  | [],w,_ => w
  | v::vs,w,r => rowOf vs (w + ((r % 2) <<< v)) (r / 2)
def sliceChk (R : List Nat) (T : Nat) (R' : List Nat) (G d : Nat) (vs : List Nat) (w : Nat) : Bool :=
  vs.all (fun v => R.contains v) &&
  (List.range 128).all (fun r => let q := rowOf vs w r
    Nat.blt q 128 && d.testBit q && (T.testBit q == G.testBit r)) &&
  R.all (fun i => (List.range 128).all (fun r => !((xN i).testBit (rowOf vs w r))) ||
    (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r)) ||
    R'.any (fun j => (List.range 128).all (fun r => (xN i).testBit (rowOf vs w r) == (xN j).testBit r)))

lemma mkSlice {R T E R' G E' d L vs w} (_hB : baseOK T R E = true) (hB' : baseOK G R' E' = true)
    (hL : LowN R' G L) (h : sliceChk R T R' G d vs w = true) : SliceN R T (d,L,vs) := by
  have b' := baseOK_ok hB'
  simp only [sliceChk,Bool.and_eq_true,List.all_eq_true,List.mem_range,Bool.or_eq_true,beq_iff_eq,
    Bool.not_eq_true',List.any_eq_true,Nat.blt_eq,List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨⟨hv,hr⟩,hR⟩ := h
  let f : Row → Row := fun r => ⟨rowOf vs w r.val,(hr r.val r.isLt).1.1⟩
  have fe (r : Row) (a : Nat) : bit (f r) (W a) = a.testBit (rowOf vs w r.val) := bit_W _ _
  have obs : restrictRows f (observe (W T)) = observe (W G) := by
    funext r
    change bit (f r) (W T) = bit r (W G)
    rw [fe,bit_W]
    exact (hr r.val r.isLt).2
  refine ⟨⟨f,rootsW R',?_,?_,?_,?_⟩,hv⟩
  · intro r
    rw [fe]
    exact (hr r.val r.isLt).1.2
  · intro a ha
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    rcases hR i hi with (h | h) | ⟨j,hj,h⟩
    · refine Or.inr (Or.inl ⟨false,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · refine Or.inr (Or.inl ⟨true,funext fun r => ?_⟩)
      exact (fe r _).trans (h r.val r.isLt)
    · have e : restrictRows f (observe (W (xN i))) = observe (W (xN j)) := by
        funext r
        exact (fe r _).trans ((h r.val r.isLt).trans (bit_W r _).symm)
      rw [e]
      exact Or.inl (List.mem_map_of_mem (List.mem_map_of_mem hj))
  · rw [obs]
    exact observe_proper b'.prop
  · rw [obs]
    exact hL

def av (d : Nat) (P : List Nat) (v : Nat) : Bool :=
  let m := Nat.land v d
  Nat.beq m 0 || Nat.beq m d || P.any (fun x => Nat.beq x m || Nat.beq x (Nat.xor d m))
def cn (d v : Nat) : Nat :=
  let m := Nat.land v d
  bif Nat.beq m 0 || Nat.beq m d then 1 else 0
def sumc (d : Nat) : List Nat → Nat
  | [] => 0
  | v::l => Nat.add (cn d v) (sumc d l)
def mkPool (P : List Nat) : List (Nat × Nat × Nat) → List Nat
  | [] => P
  | c::cs => mkPool (P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)]) cs
def initPool (d : Nat) (vs : List Nat) : List Nat := vs.map fun v => Nat.land (xN v) d

abbrev RF (f : Row → Row) (v : Nat) : Wire Row := restrictRows f (observe (W v))
def PS (f : Row → Row) (bank : List (Wire Row)) (P : List Nat) : Prop :=
  ∀ v ∈ P, Available true bank (RF f v)
lemma rf_apply (f : Row → Row) (v : Nat) (r : Row) : RF f v r = v.testBit (f r).val := bit_W _ _
lemma rf_land {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) :
    RF f (Nat.land v d) = RF f v := by
  funext r
  have h := dom r
  rw [bit_W] at h
  rw [rf_apply,rf_apply]
  have : (Nat.land v d).testBit (f r).val = (v.testBit (f r).val && d.testBit (f r).val) := Nat.testBit_and ..
  rw [this,h,Bool.and_true]
lemma rf_zero {f : Row → Row} : RF f 0 = fun _ => false := by
  funext r
  rw [rf_apply]
  exact Nat.zero_testBit _
lemma rf_dom {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) : RF f d = fun _ => true := by
  funext r
  exact dom r
lemma rf_xor {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (m : Nat) :
    RF f (Nat.xor d m) = inv (RF f m) := by
  funext r
  have h := dom r
  rw [bit_W] at h
  change RF f (Nat.xor d m) r = !(RF f m r)
  rw [rf_apply,rf_apply]
  have : (Nat.xor d m).testBit (f r).val = ((d.testBit (f r).val) ^^ (m.testBit (f r).val)) := Nat.testBit_xor ..
  rw [this,h,Bool.true_xor]
lemma cn_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (v : Nat) : cn d v ≤ cost (RF f v) := by
  change (bif (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d) then 1 else 0) ≤ _
  cases h : (Nat.beq (Nat.land v d) 0 || Nat.beq (Nat.land v d) d)
  · exact Nat.zero_le _
  · have c : Constant (RF f v) := by
      rw [←rf_land dom v]
      rw [Bool.or_eq_true] at h
      rcases h with h | h
      · rw [Nat.eq_of_beq_eq_true h,rf_zero]
        exact ⟨false,rfl⟩
      · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
        exact ⟨true,rfl⟩
    rw [cost,if_pos c]
    exact Nat.le_refl 1
lemma av_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) {bank P v} (hP : PS f bank P)
    (h : av d P v = true) : Available true bank (RF f v) := by
  simp only [av,Bool.or_eq_true,List.any_eq_true] at h
  rw [←rf_land dom v]
  rcases h with (h | h) | ⟨x,hx,h | h⟩
  · rw [Nat.eq_of_beq_eq_true h,rf_zero]
    exact Or.inr (Or.inl ⟨false,rfl⟩)
  · rw [Nat.eq_of_beq_eq_true h,rf_dom dom]
    exact Or.inr (Or.inl ⟨true,rfl⟩)
  · rw [←Nat.eq_of_beq_eq_true h]
    exact hP x hx
  · have e := hP x hx
    rw [Nat.eq_of_beq_eq_true h,rf_xor dom] at e
    have e' := avail_inv rfl e
    rwa [inv_inv'] at e'
lemma pay_nb {f : Row → Row} {roots bank p P} (o a b : Nat) (hr : Reach true roots p bank) (hP : PS f bank P)
    (ha : Available true bank (RF f a)) (hb : Available true bank (RF f b)) :
    ∃ next, Reach true roots (p+1) next ∧ PS f next P ∧ Available true next (RF f (nb o a b)) ∧
      ∀ v, Available true bank v → Available true next v := by
  obtain ⟨e,he,heq⟩ := bin_four o
  have hn : RF f (nb o a b) = comb e (RF f a) (RF f b) := by
    unfold RF
    rw [W_nb,heq,obs_bin,restrict_comb]
  obtain ⟨op,x,y,e1,hx,hy,_,_⟩ := comb_prime (d:=e) (Or.inr ⟨rfl,he⟩) ha hb
  refine ⟨_,Reach.two op hr hx hy,fun v hv => available_cons _ (hP v hv),?_,fun v hv => available_cons _ hv⟩
  rw [hn,e1]
  exact Or.inl (by simp)
lemma getD_ps {f : Row → Row} {bank P} (hP : PS f bank P) (i : Nat) : Available true bank (RF f (P.getD i 0)) := by
  rw [List.getD_eq_getElem?_getD]
  cases h : P[i]? with
  | none => exact Or.inr (Or.inl ⟨false,rf_zero⟩)
  | some a => exact hP a (List.mem_of_getElem? h)
lemma mkPool_ok {f : Row → Row} {roots} (cs : List (Nat × Nat × Nat)) {bank p P} (hr : Reach true roots p bank)
    (hP : PS f bank P) : ∃ next, Reach true roots (p+cs.length) next ∧ PS f next (mkPool P cs) := by
  induction cs generalizing bank p P with
  | nil => exact ⟨bank,hr,hP⟩
  | cons c cs ih =>
    obtain ⟨next,h1,h2,h3,_⟩ := pay_nb c.1 _ _ hr hP (getD_ps hP c.2.1) (getD_ps hP c.2.2)
    have : PS f next (P ++ [nb c.1 (P.getD c.2.1 0) (P.getD c.2.2 0)]) := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact h2 v hv
      · rw [List.mem_singleton.mp hv]
        exact h3
    obtain ⟨out,o1,o2⟩ := ih h1 this
    exact ⟨out,by rw [List.length_cons,show p+(cs.length+1) = p+1+cs.length by omega]; exact o1,o2⟩

abbrev CutV := Nat × Nat × Nat × List Nat
def keepB (d : Nat) (P : List Nat) (ka : Bool) (a : Nat) : Bool := bif ka then av d P a else true
def keepC (d : Nat) (ka : Bool) (a : Nat) : Nat := bif ka then cn d a else 0
def cutEval (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (c : CutV) : Bool :=
  rest.all (av c.1 c.2.2.2) && keepB c.1 c.2.2.2 ka a && keepB c.1 c.2.2.2 kb b &&
  (bif av c.1 c.2.2.2 z then
    Nat.blt (Nat.add k c.2.2.1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b))))
  else av c.1 c.2.2.2 a && av c.1 c.2.2.2 b &&
    Nat.blt (Nat.add (Nat.add k c.2.2.1) 1) (Nat.add c.2.1 (Nat.add (Nat.add (sumc c.1 rest) (cn c.1 z)) (Nat.add (keepC c.1 ka a) (keepC c.1 kb b)))))
def sepEval (rest : List Nat) (a b z : Nat) (ka kb : Bool) (p : Nat × Nat) : Bool :=
  let e := fun v => (Nat.testBit v p.1 == Nat.testBit v p.2)
  e z && (!ka || e a) && (!kb || e b) && rest.all e
def sepOK (T : Nat) (p : Nat × Nat) : Bool := Nat.blt p.1 128 && Nat.blt p.2 128 && (T.testBit p.1 != T.testBit p.2)

def kidW (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Sig :=
  W z :: kept ka (W a) (kept kb (W b) (rest.map W))
lemma sumc_ok {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (l : List Nat) :
    sumc d l ≤ mass (l.map (RF f)) := by
  induction l with
  | nil => simp [sumc]
  | cons v l ih =>
    rw [List.map_cons,mass_cons]
    exact Nat.add_le_add (cn_ok dom v) ih
lemma mass_keep {f : Row → Row} {d : Nat} (dom : ∀ r, bit (f r) (W d) = true) (ka : Bool) (a : Nat) (l : List (Wire Row)) :
    keepC d ka a + mass l ≤ mass (kept ka (RF f a) l) := by
  cases ka
  · simp [keepC,kept]
  · rw [kept,if_pos rfl,mass_cons]
    exact Nat.add_le_add_right (cn_ok dom a) _
lemma kid_map (f : Row → Row) (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidW rest a b z ka kb).map observe).map (restrictRows f) =
      RF f z :: kept ka (RF f a) (kept kb (RF f b) (rest.map (RF f))) := by
  cases ka <;> cases kb <;> simp [kidW,kept,List.map_map,Function.comp_def,RF]

def CutP (R : List Nat) (T : Nat) (c : CutV) : Prop :=
  ∃ (f : Row → Row) (roots : List Sig) (bank : List (Wire Row)), (∀ r, bit (f r) (W c.1) = true) ∧
    ¬Constant (restrictRows f (observe (W T))) ∧ Reach true (roots.map observe) c.2.2.1 bank ∧ PS f bank c.2.2.2 ∧
    ∀ p bank, Reach true (roots.map observe) p bank → Available true bank (restrictRows f (observe (W T))) → c.2.1 ≤ p

lemma cut_sound {R T c k rest a b o ka kb} (hc : CutP R T c)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : cutEval k rest a b (nb o a b) ka kb c = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  obtain ⟨f,roots,bank,dom,nc,hr,hP,lo⟩ := hc
  simp only [cutEval,Bool.and_eq_true,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  have key : ∃ q bank', Reach true (roots.map observe) q bank' ∧ PS f bank' c.2.2.2 ∧ Available true bank' (RF f (nb o a b)) ∧
      k + q < c.2.1 + ((sumc c.1 rest + cn c.1 (nb o a b)) + (keepC c.1 ka a + keepC c.1 kb b)) := by
    cases hz : av c.1 c.2.2.2 (nb o a b)
    · rw [hz,cond_false,Bool.and_eq_true,Bool.and_eq_true,Nat.blt_eq] at h4
      obtain ⟨next,n1,n2,n3,_⟩ := pay_nb o a b hr hP (av_ok dom hP h4.1.1) (av_ok dom hP h4.1.2)
      refine ⟨_,next,n1,n2,n3,?_⟩
      have := h4.2
      exact this
    · rw [hz,cond_true,Nat.blt_eq] at h4
      exact ⟨_,bank,hr,hP,av_ok dom hP hz,h4⟩
  obtain ⟨q,bank',r1,r2,r3,r4⟩ := key
  intro k' hk run
  have supp : supply true bank' (((kidW rest a b (nb o a b) ka kb).map observe).map (restrictRows f)) := by
    rw [kid_map]
    intro v hv
    rcases List.mem_cons.mp hv with rfl | hv
    · exact r3
    have kb' : ∀ v ∈ kept kb (RF f b) (rest.map (RF f)), Available true bank' v := by
      intro v hv
      cases kb
      · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
        exact av_ok dom r2 (h1 x hx)
      · rcases List.mem_cons.mp hv with rfl | hv
        · exact av_ok dom r2 h3
        · obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hv
          exact av_ok dom r2 (h1 x hx)
    cases ka
    · exact kb' v hv
    · rcases List.mem_cons.mp hv with rfl | hv
      · exact av_ok dom r2 h2
      · exact kb' v hv
  have bound := projected_bound f (list_run run _ nd rfl) nc r1 supp lo
  rw [kid_map,mass_cons] at bound
  have m1 := mass_keep dom ka a (kept kb (RF f b) (rest.map (RF f)))
  have m2 := mass_keep dom kb b (rest.map (RF f))
  have m3 := sumc_ok dom rest
  have m4 := cn_ok dom (nb o a b)
  omega

lemma sep_sound {T k rest a b o ka kb p} (hT : sepOK T p = true)
    (h : sepEval rest a b (nb o a b) ka kb p = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  simp only [sepOK,Bool.and_eq_true,Nat.blt_eq,bne_iff_ne] at hT
  obtain ⟨⟨p1,p2⟩,hd⟩ := hT
  simp only [sepEval,Bool.and_eq_true,Bool.or_eq_true,Bool.not_eq_true',beq_iff_eq,List.all_eq_true] at h
  obtain ⟨⟨⟨h1,h2⟩,h3⟩,h4⟩ := h
  intro k' _ run
  obtain ⟨v,hv,hne⟩ := live_row_difference run (r:=⟨p.1,p1⟩) (s:=⟨p.2,p2⟩) (by rw [bit_W,bit_W]; exact hd)
  apply hne
  rw [List.mem_toFinset] at hv
  rcases List.mem_cons.mp hv with rfl | hv
  · rw [bit_W,bit_W]; exact h1
  rcases mem_kept hv with rfl | hv'
  · cases ka
    · cases kb
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        rw [←e,bit_W,bit_W]; exact h4 x hx
      · rcases List.mem_cons.mp hv with e | hv
        · rw [e,bit_W,bit_W]; exact h3.resolve_left (by simp)
        · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
          rw [←e,bit_W,bit_W]; exact h4 x hx
    · rw [bit_W,bit_W]; exact h2.resolve_left (by simp)
  · cases kb
    · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv'
      rw [←e,bit_W,bit_W]; exact h4 x hx
    · rcases List.mem_cons.mp hv' with e | hv
      · rw [e,bit_W,bit_W]; exact h3.resolve_left (by simp)
      · obtain ⟨x,hx,e⟩ := List.mem_map.mp hv
        rw [←e,bit_W,bit_W]; exact h4 x hx

abbrev StD := List Nat × List (Nat × List (Nat × Nat × Nat)) × List (Nat × Nat) × List (List Nat)
def dupD (l : List StD) : List StD := l.map fun st => (st.1.map (Nat.mul 0x10000000000000001),st.2)
def picks : List Nat → List (Nat × List Nat)
  | [] => []
  | x::xs => (x,xs) :: (picks xs).map fun p => (p.1,x::p.2)
def pairs : List Nat → List (Nat × Nat × List Nat)
  | [] => []
  | x::xs => ((picks xs).map fun p => (x,p.1,p.2)) ++ (pairs xs).map fun p => (p.1,p.2.1,x::p.2.2)
lemma picks_ok {l : List Nat} {a : Nat} (h : a ∈ l) : ∃ p ∈ picks l, p.1 = a ∧ (a::p.2).Perm l := by
  induction l with
  | nil => cases h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | h
    · exact ⟨(a,xs),by simp [picks],rfl,List.Perm.refl _⟩
    · obtain ⟨p,hp,rfl,q⟩ := ih h
      refine ⟨(p.1,x::p.2),?_,rfl,?_⟩
      · simp only [picks,List.mem_cons,List.mem_map]
        exact Or.inr ⟨p,hp,rfl⟩
      · exact (List.Perm.swap x p.1 p.2).trans (q.cons x)
lemma pairs_ok {l : List Nat} {a b : Nat} (ha : a ∈ l) (hb : b ∈ l) (hab : a ≠ b) :
    ∃ p ∈ pairs l, (p.1::p.2.1::p.2.2).Perm l ∧ ((p.1 = a ∧ p.2.1 = b) ∨ (p.1 = b ∧ p.2.1 = a)) := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    have first (c : Nat) (hc : c ∈ xs) : ∃ p ∈ pairs (x::xs), (p.1::p.2.1::p.2.2).Perm (x::xs) ∧ p.1 = x ∧ p.2.1 = c := by
      obtain ⟨p,hp,rfl,q⟩ := picks_ok hc
      refine ⟨(x,p.1,p.2),?_,q.cons x,rfl,rfl⟩
      simp only [pairs,List.mem_append,List.mem_map]
      exact Or.inl ⟨p,hp,rfl⟩
    rcases List.mem_cons.mp ha with rfl | ha2
    · rcases List.mem_cons.mp hb with rfl | hb
      · exact absurd rfl hab
      · obtain ⟨p,h1,h2,h3,h4⟩ := first b hb
        exact ⟨p,h1,h2,Or.inl ⟨h3,h4⟩⟩
    · rcases List.mem_cons.mp hb with e | hb
      · subst e
        obtain ⟨p,h1,h2,h3,h4⟩ := first a ha2
        exact ⟨p,h1,h2,Or.inr ⟨h3,h4⟩⟩
      · obtain ⟨p,hp,q,e⟩ := ih ha2 hb
        refine ⟨(p.1,p.2.1,x::p.2.2),?_,?_,e⟩
        · simp only [pairs,List.mem_append,List.mem_map]
          exact Or.inr ⟨p,hp,rfl⟩
        · exact ((List.Perm.swap x p.2.1 p.2.2).cons p.1).trans ((List.Perm.swap x p.1 _).trans (q.cons x))

def mem1 (z : Nat) (l : List Nat) : Bool := l.any fun x => Nat.beq x z
def beqL : List Nat → List Nat → Bool
  | [],[] => true
  | x::xs,y::ys => Nat.beq x y && beqL xs ys
  | _,_ => false
lemma beqL_ok {a b : List Nat} (h : beqL a b = true) : a = b := by
  induction a generalizing b with
  | nil => cases b with
    | nil => rfl
    | cons => simp [beqL] at h
  | cons x xs ih => cases b with
    | nil => simp [beqL] at h
    | cons y ys =>
      simp only [beqL,Bool.and_eq_true] at h
      rw [Nat.eq_of_beq_eq_true h.1,ih h.2]
def ins (z : Nat) : List Nat → List Nat
  | [] => [z]
  | x::xs => bif Nat.ble z x then z::x::xs else x :: ins z xs
lemma mem_ins {z v : Nat} {l : List Nat} : v ∈ ins z l ↔ v = z ∨ v ∈ l := by
  induction l with
  | nil => simp [ins]
  | cons x xs ih =>
    unfold ins
    cases Nat.ble z x
    · simp only [cond_false,List.mem_cons,ih]
      tauto
    · simp
def kidN (rest : List Nat) (a b z : Nat) (ka kb : Bool) : List Nat :=
  ins z (bif ka then ins a (bif kb then ins b rest else rest) else bif kb then ins b rest else rest)
lemma kid_fin (rest : List Nat) (a b z : Nat) (ka kb : Bool) :
    ((kidN rest a b z ka kb).map W).toFinset = (kidW rest a b z ka kb).toFinset := by
  ext v
  cases ka <;> cases kb <;> simp [kidN,kidW,kept,mem_ins] <;> aesop

def keeps : List (Bool × Bool) := [(true,true),(true,false),(false,true),(false,false)]
def bl (b : Bool) : Nat := bif b then 1 else 0
def mkCut (Z : List SliceD) (c : Nat × List (Nat × Nat × Nat)) : CutV :=
  let s := Z.getD c.1 (0,0,[])
  (s.1,s.2.1,c.2.length,mkPool (initPool s.1 s.2.2) c.2)
def hintOK (k : Nat) (cuts : List CutV) (seps : List (Nat × Nat)) (rest : List Nat) (a b z : Nat) (ka kb : Bool) (i : Nat) : Bool :=
  bif Nat.blt i 1000 then (match cuts[i]? with
    | some c => cutEval k rest a b z ka kb c
    | none => false)
  else (match seps[i-1000]? with
    | some q => sepEval rest a b z ka kb q
    | none => false)
def kidOK (k : Nat) (next : List (List Nat)) (cuts : List CutV) (seps : List (Nat × Nat)) (rest : List Nat) (hints : List Nat)
    (a b z : Nat) (kk : Bool × Bool) : Bool :=
  Nat.blt k (Nat.add (Nat.add rest.length (Nat.add (bl kk.1) (bl kk.2))) 0) ||
  hints.any (hintOK k cuts seps rest a b z kk.1 kk.2) ||
  next.any (beqL (kidN rest a b z kk.1 kk.2))
def pairOK (k : Nat) (next : List (List Nat)) (cuts : List CutV) (seps : List (Nat × Nat)) (s : List Nat)
    (p : Nat × Nat × List Nat) (hints : List Nat) : Bool :=
  [0,1,2,3].all fun o =>
    let z := nb o p.1 p.2.1
    mem1 z s || Nat.beq z 0 || Nat.beq z full ||
      keeps.all (kidOK k next cuts seps p.2.2 hints p.1 p.2.1 z)
def allZip (f : Nat × Nat × List Nat → List Nat → Bool) : List (Nat × Nat × List Nat) → List (List Nat) → Bool
  | [],_ => true
  | p::ps,[] => f p [] && allZip f ps []
  | p::ps,h::hs => f p h && allZip f ps hs
lemma allZip_ok {f ps hs} (h : allZip f ps hs = true) : ∀ p ∈ ps, ∃ x, f p x = true := by
  induction ps generalizing hs with
  | nil => intro p hp; cases hp
  | cons q ps ih =>
    intro p hp
    cases hs with
    | nil =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
    | cons x hs =>
      simp only [allZip,Bool.and_eq_true] at h
      rcases List.mem_cons.mp hp with rfl | hp
      · exact ⟨_,h.1⟩
      · exact ih h.2 p hp
def asc : List Nat → Bool
  | [] => true
  | [x] => Nat.blt x (2^128)
  | x::y::l => Nat.blt x y && asc (y::l)
lemma asc_ok {l : List Nat} (h : asc l = true) : l.Pairwise (· < ·) ∧ ∀ x ∈ l, x < 2^128 := by
  induction l with
  | nil => simp
  | cons x l ih =>
    cases l with
    | nil =>
      simp only [asc,Nat.blt_eq] at h
      simpa using h
    | cons y l =>
      simp only [asc,Bool.and_eq_true,Nat.blt_eq] at h
      obtain ⟨i1,i2⟩ := ih h.2
      have hy := List.pairwise_cons.mp i1
      refine ⟨List.pairwise_cons.mpr ⟨?_,i1⟩,?_⟩
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1
        · exact h.1.trans (hy.1 v hv)
      · intro v hv
        rcases List.mem_cons.mp hv with rfl | hv
        · exact h.1.trans (i2 y (by simp))
        · exact i2 v hv
lemma asc_nodup {l : List Nat} (h : asc l = true) : l.Nodup ∧ (l.map W).Nodup := by
  obtain ⟨h1,h2⟩ := asc_ok h
  have nd : l.Nodup := h1.imp (fun h => Nat.ne_of_lt h)
  refine ⟨nd,?_⟩
  refine nd.map_on ?_
  intro x hx y hy e
  exact W_inj (h2 x hx) (h2 y hy) e
def stOK (T : Nat) (Z : List SliceD) (k : Nat) (next : List (List Nat)) (st : StD) : Bool :=
  asc st.1 && !(mem1 T st.1) && st.2.2.1.all (sepOK T) && st.2.1.all (fun c => Nat.blt c.1 Z.length) &&
  allZip (pairOK k next (st.2.1.map (mkCut Z)) st.2.2.1 st.1) (pairs st.1) st.2.2.2
def levelOK (T : Nat) (Z : List SliceD) (k : Nat) (next : List (List Nat)) (D : List StD) : Bool :=
  D.all (stOK T Z k next)
def LevelN (R : List Nat) (T k : Nat) (D : List StD) : Prop :=
  ∀ st ∈ D, Impossible true (W T) k (st.1.map W).toFinset

lemma stStep {R T E Z k next st} (hB : baseOK T R E = true) (hZ : ∀ s ∈ Z, SliceN R T s)
    (hn : ∀ s ∈ next, Impossible true (W T) k (s.map W).toFinset)
    (h : stOK T Z k next st = true) : Impossible true (W T) (k+1) (st.1.map W).toFinset := by
  have b := baseOK_ok hB
  simp only [stOK,Bool.and_eq_true,Bool.not_eq_true',List.all_eq_true] at h
  obtain ⟨⟨⟨⟨ha,hT⟩,hs⟩,hcut⟩,hz⟩ := h
  obtain ⟨nd,ndW⟩ := asc_nodup ha
  have lt := (asc_ok ha).2
  have hTm : W T ∉ st.1.map W := by
    intro hm
    obtain ⟨x,hx,e⟩ := List.mem_map.mp hm
    have := W_inj (lt x hx) b.lt e
    subst this
    have : mem1 x st.1 = true := List.any_eq_true.mpr ⟨x,hx,Nat.beq_refl x⟩
    rw [hT] at this
    exact Bool.noConfusion this
  have good : ∀ c ∈ st.2.1.map (mkCut Z), CutP R T c := by
    intro c hc
    obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hc
    have hi : q.1 < Z.length := by simpa only [Nat.blt_eq] using hcut q hq
    have hm : Z.getD q.1 (0,0,[]) ∈ Z := by
      rw [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem hi]
      exact List.getElem_mem hi
    obtain ⟨⟨f,roots,dom,base,nc,lo⟩,hv⟩ := hZ _ hm
    have ps : PS f (roots.map observe) (initPool (Z.getD q.1 (0,0,[])).1 (Z.getD q.1 (0,0,[])).2.2) := by
      intro v hv'
      obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hv'
      rw [rf_land dom]
      exact base _ (List.mem_map_of_mem (hv j hj))
    obtain ⟨bank,b1,b2⟩ := mkPool_ok q.2 (Reach.start (u:=true) (roots:=roots.map observe)) ps
    refine ⟨f,roots,bank,dom,nc,?_,b2,lo⟩
    simpa [mkCut] using b1
  apply enum_step ndW hTm
  intro a' ha' b' hb' d hd ka kb hab fresh hprop hlen
  obtain ⟨a,ham,rfl⟩ := List.mem_map.mp ha'
  obtain ⟨c,hcm,rfl⟩ := List.mem_map.mp hb'
  have hac : a ≠ c := fun h => hab (by rw [h])
  have hd4 : d < 4 := by
    rcases hd with h | ⟨_,h⟩ <;> omega
  obtain ⟨p,hp,perm,ho⟩ := pairs_ok ham hcm hac
  obtain ⟨x,hx⟩ := allZip_ok hz p hp
  -- one unordered pair serves both orders
  have core : ∀ (o : Nat) (ja jb : Bool), o < 4 → W (nb o p.1 p.2.1) = bin d (W a) (W c) →
      (p.2.2.length + (bl ja + bl jb) ≤ k) →
      Impossible true (W T) k (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).toFinset := by
    intro o ja jb ho4 hW hl
    have hf := List.all_eq_true.mp hx o (by
      have : o = 0 ∨ o = 1 ∨ o = 2 ∨ o = 3 := by omega
      simpa using this)
    simp only [Bool.or_eq_true] at hf
    have pm (v : Nat) : v ∈ st.1 ↔ v = p.1 ∨ v = p.2.1 ∨ v ∈ p.2.2 := by
      rw [←perm.mem_iff]
      simp
    rcases hf with ((hf | hf) | hf) | hf
    · exfalso
      obtain ⟨y,hy,e⟩ := List.any_eq_true.mp hf
      apply fresh
      rw [←hW,←Nat.eq_of_beq_eq_true e]
      exact List.mem_map_of_mem hy
    · exfalso
      apply hprop.1
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      rfl
    · exfalso
      apply hprop.2
      rw [←hW,Nat.eq_of_beq_eq_true hf]
      exact W_full
    have hk := List.all_eq_true.mp hf (ja,jb) (by cases ja <;> cases jb <;> simp [keeps])
    simp only [kidOK,Bool.or_eq_true] at hk
    have ndp : ((p.1::p.2.1::p.2.2).map W).Nodup := (perm.map W).nodup_iff.mpr ndW
    simp only [List.map_cons,List.nodup_cons,List.mem_cons,not_or] at ndp
    have nk : (kidW p.2.2 p.1 p.2.1 (nb o p.1 p.2.1) ja jb).Nodup := by
      have n1 := kept_nd jb (W p.2.1) _ ndp.2.2 ndp.2.1
      have n2 : W p.1 ∉ kept jb (W p.2.1) (p.2.2.map W) := by
        cases jb
        · exact ndp.1.2
        · simp only [kept,if_true,List.mem_cons,not_or]
          exact ndp.1
      refine List.nodup_cons.mpr ⟨?_,kept_nd ja _ _ n1 n2⟩
      intro hm
      apply fresh
      rw [←hW]
      have sub : W (nb o p.1 p.2.1) ∈ (p.1::p.2.1::p.2.2).map W := by
        rcases mem_kept hm with h | h
        · rw [h]; simp
        · rcases mem_kept h with h | h
          · rw [h]; simp
          · simp [h]
      exact (perm.map W).mem_iff.mp sub
    rcases hk with (hk | hk) | hk
    · exfalso
      rw [Nat.blt_eq] at hk
      have : k < p.2.2.length + (bl ja + bl jb) + 0 := hk
      omega
    · obtain ⟨i,_,hi⟩ := List.any_eq_true.mp hk
      unfold hintOK at hi
      cases hb : Nat.blt i 1000
      · rw [hb,cond_false] at hi
        cases hg : st.2.2.1[i-1000]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact sep_sound (hs q (List.mem_of_getElem? hg)) hi
      · rw [hb,cond_true] at hi
        cases hg : (st.2.1.map (mkCut Z))[i]? with
        | none => rw [hg] at hi; exact Bool.noConfusion hi
        | some q =>
          rw [hg] at hi
          exact cut_sound (good q (List.mem_of_getElem? hg)) nk hi
    · obtain ⟨s,hs',e⟩ := List.any_eq_true.mp hk
      rw [←kid_fin]
      rw [beqL_ok e]
      exact hn s hs'
  have rp : (((st.1.map W).erase (W a)).erase (W c)).Perm (p.2.2.map W) := by
    have e : (W a :: W c :: p.2.2.map W).Perm (st.1.map W) := by
      rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact perm.map W
      · exact (List.Perm.swap _ _ _).trans (perm.map W)
    have e1 := e.erase (W a)
    rw [List.erase_cons_head] at e1
    have e2 := e1.erase (W c)
    rw [List.erase_cons_head] at e2
    exact e2.symm
  have lenr : (((st.1.map W).erase (W a)).erase (W c)).length = p.2.2.length := by
    rw [rp.length_eq,List.length_map]
  have fits : p.2.2.length + (bl ka + bl kb) ≤ k := by
    have h := hlen
    unfold childTwo at h
    cases ka <;> cases kb <;> simp [kept,lenr] at h <;> simp [bl] <;> omega
  rw [Nat.add_sub_cancel]
  rcases ho with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
  · have r := core d ka kb hd4 (W_nb _ _ _) fits
    have e : (childTwo (st.1.map W) (W p.1) (W p.2.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb d p.1 p.2.1) ka kb).toFinset := by
      unfold childTwo kidW
      rw [W_nb]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff]
    rw [e]
    exact r
  · have hfl := flip_flip hd
    have f4 : flipOp d < 4 := by
      rcases hfl.1 with h | ⟨_,h⟩ <;> omega
    have r := core (flipOp d) kb ka f4 (by rw [W_nb]; exact (bin_flip hd _ _).symm) (by omega)
    have e : (childTwo (st.1.map W) (W p.2.1) (W p.1) d ka kb).toFinset = (kidW p.2.2 p.1 p.2.1 (nb (flipOp d) p.1 p.2.1) kb ka).toFinset := by
      unfold childTwo kidW
      rw [W_nb,bin_flip hd]
      ext v
      cases ka <;> cases kb <;> simp [kept,rp.mem_iff] <;> tauto
    rw [e]
    exact r

lemma levelStep {R T E Z k D' D} (hB : baseOK T R E = true) (hZ : ∀ s ∈ Z, SliceN R T s)
    (hI : LevelN R T k D') (h : levelOK T Z k (D'.map Prod.fst) D = true) : LevelN R T (k+1) D := by
  intro st hst
  refine stStep hB hZ ?_ (List.all_eq_true.mp h st hst)
  intro s hs
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp hs
  exact hI q hq
lemma chunks {T : Nat} {Z : List SliceD} {k : Nat} {next : List (List Nat)} (c : Nat) (D : List StD) (n : Nat) (hc : 0 < c)
    (hl : Nat.ble D.length (n*c) = true)
    (h : ∀ i, i < n → levelOK T Z k next ((D.drop (i*c)).take c) = true) : levelOK T Z k next D = true := by
  rw [levelOK,List.all_eq_true]
  intro x hx
  obtain ⟨j,hj,rfl⟩ := List.getElem_of_mem hx
  have hl' := Nat.le_of_ble_eq_true hl
  have hi : j / c < n := by
    rw [Nat.div_lt_iff_lt_mul hc]
    omega
  refine List.all_eq_true.mp (h _ hi) _ ?_
  have hm : j / c * c + j % c = j := by rw [Nat.mul_comm]; exact Nat.div_add_mod j c
  have hmod := Nat.mod_lt j hc
  refine List.mem_of_getElem? (i := j % c) ?_
  rw [List.getElem?_take_of_lt hmod,List.getElem?_drop,hm]
  exact List.getElem?_eq_getElem hj
lemma lowSearch {R T E K D} (hB : baseOK T R E = true) (hI : LevelN R T K D)
    (h : (D.map Prod.fst).contains (R.map xN) = true) : LowN R T (K+1) := by
  apply lowOf hB
  simp only [List.contains_eq_mem,decide_eq_true_eq] at h
  obtain ⟨q,hq,e⟩ := List.mem_map.mp h
  have := hI q hq
  rw [e] at this
  simpa only [rootsW,List.map_map,Function.comp_def] using this
abbrev c0 : Nat := 0xcccccccccccccccc
abbrev c1 : Nat := 0xaaaaaaaaaaaaaaaa
abbrev c2 : Nat := 0xf0f0f0f0f0f0f0f0
abbrev c3 : Nat := 0xff00ff00ff00ff00
abbrev c5 : Nat := 0xffff0000ffff0000
abbrev c6 : Nat := 0xfafafafafafafafa
abbrev c7 : Nat := 0xffffff00ffffff00
abbrev c8 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0
abbrev c9 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff00
abbrev c10 : Nat := 0xffff0000ffff0000ffff0000ffff0000
abbrev c11 : Nat := 0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa
abbrev c12 : Nat := 0xcccccccccccccccccccccccccccccccc
abbrev c14 : Nat := 0xffaaffaaffaaffaa
abbrev c16 : Nat := 0xfff0fff0fff0fff0
abbrev c17 : Nat := 0xffffaaaaffffaaaa
abbrev c18 : Nat := 0xffccffccffccffcc
abbrev c19 : Nat := 0xfcfcfcfcfcfcfcfc
abbrev c20 : Nat := 0xfffff0f0fffff0f0
abbrev c21 : Nat := 0xeeeeeeeeeeeeeeee
abbrev c23 : Nat := 0xff00ff00ff00ff00ff00ff00ff00ff
abbrev c24 : Nat := 0x33333333333333333333333333333333
abbrev c25 : Nat := 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f
abbrev c27 : Nat := 0xfa00fa00fa00fa
abbrev c28 : Nat := 0x55555555555555555555555555555555
abbrev c31 : Nat := 0xffff0000ffff0000ffff0000ffff
abbrev c32 : Nat := 0x5555000055550000555500005555
abbrev c35 : Nat := 0x3030303030303030303030303030303
abbrev c36 : Nat := 0x550055005500550055005500550055
abbrev c40 : Nat := 0xcccc0000cccc0000cccc0000cccc
abbrev c41 : Nat := 0x30003000300030003000300030003
abbrev c42 : Nat := 0xcccc0000cccc0000cccc0000cccc0000
abbrev c44 : Nat := 0x3333000033330000333300003333
abbrev c46 : Nat := 0xeeeeeeeeeeeeeeeeeeeeeeeeeeeeeeee
abbrev c47 : Nat := 0x30303030303030303030303030303030
abbrev c48 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a0
abbrev c53 : Nat := 0xf0f00000f0f00000f0f00000f0f0
abbrev c54 : Nat := 0xcc000000cc000000cc000000cc
abbrev c55 : Nat := 0xf0f00000f0f00000f0f00000f0f00000
abbrev c56 : Nat := 0xfc00fc00fc00fc
abbrev c58 : Nat := 0xf000f000f000f000f000f000f000f
abbrev c61 : Nat := 0xcc00cc00cc00cc00cc00cc00cc00cc00
abbrev c65 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa
abbrev c69 : Nat := 0x88888888888888888888888888888888
abbrev c70 : Nat := 0xf0c0f0c0f0c0f0c
abbrev c72 : Nat := 0xffffccccffffcccc
abbrev c74 : Nat := 0xf000f000f000f000f000f000f000f0
abbrev c75 : Nat := 0x5555550055555500
abbrev c81 : Nat := 0xa0a0a0a0a0a0a0a0a0a0a0a0a0a0a0a
abbrev c82 : Nat := 0xaa00aa00aa00aa00aa00aa00aa00aa00
abbrev c83 : Nat := 0x33003300330033003300330033003300
abbrev c110 : Nat := 0x1111000011110000111100001111
abbrev c111 : Nat := 0xc0c0c0c0c0c0c0c0c0c0c0c0c0c0c0c
abbrev c112 : Nat := 0x50005000500050005000500050005
abbrev c113 : Nat := 0xaaaa0000aaaa0000aaaa0000aaaa
abbrev c114 : Nat := 0x55000000550000005500000055
abbrev l0 : List Nat := [0, 1, 2, 3, 4]
abbrev l2 : List Nat := [0,1,1000,1001,1002]
abbrev l3 : List Nat := [c1,c0,c2,c3,c5]
abbrev l4 : List Nat := [0,1,1000,2,3,1001,1002]
abbrev l5 : List Nat := [c1,c0,c2,c3]
abbrev l7 : List Nat := [c1,c0,c2,c19,c3,c5]
def d0 : Nat := c69
def d1 : List Nat := [0, 1]
def d2 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3)]
lemma d3 : baseOK d0 d1 d2 = true := by decide +kernel
lemma d4 : LowN d1 d0 1 := lowCount d3 (by decide +kernel)
def d5 : Nat := c46
def d6 : List Nat := [0, 1]
def d7 : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2)]
lemma d8 : baseOK d5 d6 d7 = true := by decide +kernel
lemma d9 : LowN d6 d5 1 := lowCount d8 (by decide +kernel)
def d10 : Nat := 0xeaeaeaeaeaeaeaeaeaeaeaeaeaeaeaea
def d11 : List Nat := [0, 1, 2]
def d12 : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6)]
lemma d13 : baseOK d10 d11 d12 = true := by decide +kernel
lemma d14 : LowN d11 d10 2 := lowCount d13 (by decide +kernel)
def d15 : Nat := 0xa8a8a8a8a8a8a8a8a8a8a8a8a8a8a8a8
def d16 : List Nat := [0, 1, 2]
def d17 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
lemma d18 : baseOK d15 d16 d17 = true := by decide +kernel
lemma d19 : LowN d16 d15 2 := lowCount d18 (by decide +kernel)
def d20 : Nat := 0xeac8eac8eac8eac8eac8eac8eac8eac8
def d21 : List Nat := [0, 1, 2, 3]
def d22 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9)]
lemma d23 : baseOK d20 d21 d22 = true := by decide +kernel
lemma d24 : SliceN d21 d20 (c35,1,[0, 3]) := mkSlice (w:=0) d23 d3 d4 (by decide +kernel)
lemma d25 : SliceN d21 d20 (c81,1,[1, 3]) := mkSlice (w:=1) d23 d8 d9 (by decide +kernel)
lemma d26 : SliceN d21 d20 (c36,1,[1, 2]) := mkSlice (w:=0) d23 d3 d4 (by decide +kernel)
lemma d27 : SliceN d21 d20 (c8,2,[1, 0, 3]) := mkSlice (w:=4) d23 d13 d14 (by decide +kernel)
lemma d28 : SliceN d21 d20 (c23,2,[1, 0, 2]) := mkSlice (w:=0) d23 d18 d19 (by decide +kernel)
lemma d29 : SliceN d21 d20 (c9,2,[0, 1, 2]) := mkSlice (w:=8) d23 d13 d14 (by decide +kernel)
def d30 : List SliceD := [(c35,1,[0, 3]),(c81,1,[1, 3]),(c36,1,[1, 2]),(c8,2,[1, 0, 3]),(c23,2,[1, 0, 2]),(c9,2,[0, 1, 2])]
lemma d31 : ∀ s ∈ d30, SliceN d21 d20 s := by
  unfold d30
  simp only [List.forall_mem_cons]
  exact ⟨d24,d25,d26,d27,d28,d29,by simp⟩
def d32 : List StD := dupD [
 (l5,[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])],[],[[0,1,2],[0,3],[4,1,5],[1,3],[0,5,2],[0,3]])]
def d33 : List StD := []
lemma d34 : LevelN d21 d20 2 d33 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d35 : levelOK d20 d30 2 (d33.map Prod.fst) ((d32.drop (0*8)).take 8) = true := by decide +kernel
lemma d36 : LevelN d21 d20 3 d32 := levelStep d23 d31 d34 (chunks 8 d32 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d35
  ))
lemma d37 : LowN d21 d20 4 := lowSearch d23 d36 (by decide +kernel)
def d38 : Nat := 0xe8e8e8e8e8e8e8e8e8e8e8e8e8e8e8e8
def d39 : List Nat := [0, 1, 2]
def d40 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5)]
lemma d41 : baseOK d38 d39 d40 = true := by decide +kernel
lemma d42 : SliceN d39 d38 (c24,1,[0, 2]) := mkSlice (w:=0) d41 d3 d4 (by decide +kernel)
lemma d43 : SliceN d39 d38 (c28,1,[1, 2]) := mkSlice (w:=0) d41 d3 d4 (by decide +kernel)
lemma d44 : SliceN d39 d38 (c12,1,[0, 2]) := mkSlice (w:=2) d41 d8 d9 (by decide +kernel)
lemma d45 : SliceN d39 d38 (c11,1,[1, 2]) := mkSlice (w:=1) d41 d8 d9 (by decide +kernel)
lemma d46 : SliceN d39 d38 (c25,1,[0, 1]) := mkSlice (w:=0) d41 d3 d4 (by decide +kernel)
lemma d47 : SliceN d39 d38 (c8,1,[0, 1]) := mkSlice (w:=4) d41 d8 d9 (by decide +kernel)
def d48 : List SliceD := [(c24,1,[0, 2]),(c28,1,[1, 2]),(c12,1,[0, 2]),(c11,1,[1, 2]),(c25,1,[0, 1]),(c8,1,[0, 1])]
lemma d49 : ∀ s ∈ d48, SliceN d39 d38 s := by
  unfold d48
  simp only [List.forall_mem_cons]
  exact ⟨d42,d43,d44,d45,d46,d47,by simp⟩
def d50 : List StD := dupD [
 ([c1,c0,c2],[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])],[(4,5),(1,3),(0,3),(2,3),(2,6),(1,5)],[l4,[4,1,1003,5,3,1000],[4,0,1001,5,2,1004,1005]])]
def d51 : List StD := []
lemma d52 : LevelN d39 d38 2 d51 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d53 : levelOK d38 d48 2 (d51.map Prod.fst) ((d50.drop (0*8)).take 8) = true := by decide +kernel
lemma d54 : LevelN d39 d38 3 d50 := levelStep d41 d49 d52 (chunks 8 d50 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d53
  ))
lemma d55 : LowN d39 d38 4 := lowSearch d41 d54 (by decide +kernel)
def d56 : Nat := 0xeae8eae8eae8eae8eae8eae8eae8eae8
def d57 : List Nat := [0, 1, 2, 3]
def d58 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
lemma d59 : baseOK d56 d57 d58 = true := by decide +kernel
lemma d60 : SliceN d57 d56 (c23,4,[0, 1, 2]) := mkSlice (w:=0) d59 d41 d55 (by decide +kernel)
def d61 : List SliceD := [(c23,4,[0, 1, 2])]
lemma d62 : ∀ s ∈ d61, SliceN d57 d56 s := by
  unfold d61
  simp only [List.forall_mem_cons]
  exact ⟨d60,by simp⟩
def d63 : List StD := dupD [
 (l5,[(0,[])],[],[[0],[0],[0],[0],[0],[0]])]
def d64 : List StD := []
lemma d65 : LevelN d57 d56 3 d64 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d66 : levelOK d56 d61 3 (d64.map Prod.fst) ((d63.drop (0*8)).take 8) = true := by decide +kernel
lemma d67 : LevelN d57 d56 4 d63 := levelStep d59 d62 d65 (chunks 8 d63 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d66
  ))
lemma d68 : LowN d57 d56 5 := lowSearch d59 d67 (by decide +kernel)
def d69 : Nat := 0xeee8eee8eee8eee8eee8eee8eee8eee8
def d70 : List Nat := [0, 1, 2, 3]
def d71 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9)]
lemma d72 : baseOK d69 d70 d71 = true := by decide +kernel
lemma d73 : SliceN d70 d69 (c25,4,[0, 1, 3]) := mkSlice (w:=0) d72 d41 d55 (by decide +kernel)
def d74 : List SliceD := [(c25,4,[0, 1, 3])]
lemma d75 : ∀ s ∈ d74, SliceN d70 d69 s := by
  unfold d74
  simp only [List.forall_mem_cons]
  exact ⟨d73,by simp⟩
def d76 : List StD := dupD [
 (l5,[(0,[])],[],[[0],[0],[0],[0],[0],[0]])]
def d77 : List StD := []
lemma d78 : LevelN d70 d69 3 d77 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d79 : levelOK d69 d74 3 (d77.map Prod.fst) ((d76.drop (0*8)).take 8) = true := by decide +kernel
lemma d80 : LevelN d70 d69 4 d76 := levelStep d72 d75 d78 (chunks 8 d76 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d79
  ))
lemma d81 : LowN d70 d69 5 := lowSearch d72 d80 (by decide +kernel)
def d82 : Nat := 0xfeeafeeafeeafeeafeeafeeafeeafeea
def d83 : List Nat := [0, 1, 2, 3]
def d84 : List (Nat × Nat × Nat) := [(0,0,1),(1,4,6),(2,2,6),(3,2,10)]
lemma d85 : baseOK d82 d83 d84 = true := by decide +kernel
lemma d86 : SliceN d83 d82 (c28,4,[1, 2, 3]) := mkSlice (w:=0) d85 d41 d55 (by decide +kernel)
def d87 : List SliceD := [(c28,4,[1, 2, 3])]
lemma d88 : ∀ s ∈ d87, SliceN d83 d82 s := by
  unfold d87
  simp only [List.forall_mem_cons]
  exact ⟨d86,by simp⟩
def d89 : List StD := dupD [
 (l5,[(0,[])],[],[[0],[0],[0],[0],[0],[0]])]
def d90 : List StD := []
lemma d91 : LevelN d83 d82 3 d90 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d92 : levelOK d82 d87 3 (d90.map Prod.fst) ((d89.drop (0*8)).take 8) = true := by decide +kernel
lemma d93 : LevelN d83 d82 4 d89 := levelStep d85 d88 d91 (chunks 8 d89 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d92
  ))
lemma d94 : LowN d83 d82 5 := lowSearch d85 d93 (by decide +kernel)
def d95 : Nat := 0xfefefefefefefefefefefefefefefefe
def d96 : List Nat := [0, 1, 2]
def d97 : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,0,4)]
lemma d98 : baseOK d95 d96 d97 = true := by decide +kernel
lemma d99 : LowN d96 d95 2 := lowCount d98 (by decide +kernel)
def d100 : Nat := 0xfeeefeeefeeefeeefeeefeeefeeefeee
def d101 : List Nat := [0, 1, 2, 3]
def d102 : List (Nat × Nat × Nat) := [(0,0,1),(1,0,2),(2,8,12),(3,4,12)]
lemma d103 : baseOK d100 d101 d102 = true := by decide +kernel
lemma d104 : LowN d101 d100 3 := lowCount d103 (by decide +kernel)
def d105 : Nat := 0xfeeafce8feeafce8feeafce8feeafce8
def d106 : List Nat := l0
def d107 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,2,10),(4,1,17)]
lemma d108 : baseOK d105 d106 d107 = true := by decide +kernel
lemma d109 : SliceN d106 d105 (c24,4,[0, 2, 3, 4]) := mkSlice (w:=0) d108 d23 d37 (by decide +kernel)
lemma d110 : SliceN d106 d105 (c32,4,[1, 2, 3]) := mkSlice (w:=0) d108 d41 d55 (by decide +kernel)
lemma d111 : SliceN d106 d105 (c25,4,[0, 1, 3, 4]) := mkSlice (w:=0) d108 d23 d37 (by decide +kernel)
lemma d112 : SliceN d106 d105 (c23,5,[0, 1, 2, 4]) := mkSlice (w:=0) d108 d59 d68 (by decide +kernel)
lemma d113 : SliceN d106 d105 (c31,5,[1, 2, 0, 3]) := mkSlice (w:=0) d108 d72 d81 (by decide +kernel)
lemma d114 : SliceN d106 d105 (c10,5,[0, 1, 2, 3]) := mkSlice (w:=16) d108 d85 d94 (by decide +kernel)
lemma d115 : SliceN d106 d105 (c40,2,[0, 2, 3]) := mkSlice (w:=2) d108 d98 d99 (by decide +kernel)
lemma d116 : SliceN d106 d105 (c53,2,[0, 1, 3]) := mkSlice (w:=4) d108 d98 d99 (by decide +kernel)
lemma d117 : SliceN d106 d105 (c41,1,[0, 4]) := mkSlice (w:=0) d108 d3 d4 (by decide +kernel)
lemma d118 : SliceN d106 d105 (0x3000300030003000300030003000300,1,[0, 4]) := mkSlice (w:=8) d108 d3 d4 (by decide +kernel)
lemma d119 : SliceN d106 d105 (c54,1,[0, 2]) := mkSlice (w:=2) d108 d8 d9 (by decide +kernel)
lemma d120 : SliceN d106 d105 (c9,3,[1, 2, 0, 4]) := mkSlice (w:=8) d108 d103 d104 (by decide +kernel)
lemma d121 : SliceN d106 d105 (c82,2,[1, 2, 4]) := mkSlice (w:=9) d108 d98 d99 (by decide +kernel)
lemma d122 : SliceN d106 d105 (c42,2,[0, 2, 3]) := mkSlice (w:=18) d108 d98 d99 (by decide +kernel)
lemma d123 : SliceN d106 d105 (c55,2,[0, 1, 3]) := mkSlice (w:=20) d108 d98 d99 (by decide +kernel)
def d124 : List SliceD := [(c24,4,[0, 2, 3, 4]),(c32,4,[1, 2, 3]),(c25,4,[0, 1, 3, 4]),(c23,5,[0, 1, 2, 4]),(c31,5,[1, 2, 0, 3]),(c10,5,[0, 1, 2, 3]),(c40,2,[0, 2, 3]),(c53,2,[0, 1, 3]),(c41,1,[0, 4]),(0x3000300030003000300030003000300,1,[0, 4]),(c54,1,[0, 2]),(c9,3,[1, 2, 0, 4]),(c82,2,[1, 2, 4]),(c42,2,[0, 2, 3]),(c55,2,[0, 1, 3])]
lemma d125 : ∀ s ∈ d124, SliceN d106 d105 s := by
  unfold d124
  simp only [List.forall_mem_cons]
  exact ⟨d109,d110,d111,d112,d113,d114,d115,d116,d117,d118,d119,d120,d121,d122,d123,by simp⟩
def d126 : List StD := dupD [
 (l3,[(0,[]),(1,[]),(2,[]),(3,[]),(4,[]),(5,[])],[(2,3),(0,3),(4,5),(17,24),(1,3),(4,6),(2,6),(2,10),(0,10),(4,12)],[[0,1,1000,1001],[1,1002,2,1000],[1,3,1003],[1,4,5],[0,2,1004,1005,1006],[0,3,1007,1008],[0,1,5],[2,3,1009,1007],[1,5],[1,3,5]])]
def d127 : List StD := dupD [
 (l7,[(0,[]),(6,[]),(2,[]),(7,[]),(1,[]),(8,[]),(9,[]),(5,[(1,1,2)]),(3,[])],[],[[0,1],[2,3],[4,1,5],[5,6],[1,7],[0,1],[2],[0,1],[0,7,3],[0],[2,3],[1,7],[8,1],[4,7],[1,6,5]])]
def d128 : List StD := dupD [
 ([c56,c1,c0,c2,c5],[(1,[]),(10,[]),(11,[]),(3,[(1,1,2)]),(5,[]),(0,[(2,1,2)]),(2,[(2,1,2)]),(7,[]),(12,[]),(13,[]),(14,[])],[],[[0,1,2],[2,3],[2,1],[0,4],[5,1],[6,7],[1,8,9],[5,1],[5,10,7],[1,9]])]
def d129 : List StD := []
lemma d130 : LevelN d106 d105 3 d129 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d131 : levelOK d105 d124 3 (d129.map Prod.fst) ((d128.drop (0*8)).take 8) = true := by decide +kernel
lemma d132 : LevelN d106 d105 4 d128 := levelStep d108 d125 d130 (chunks 8 d128 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d131
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d133 : levelOK d105 d124 4 (d128.map Prod.fst) ((d127.drop (0*8)).take 8) = true := by decide +kernel
lemma d134 : LevelN d106 d105 5 d127 := levelStep d108 d125 d132 (chunks 8 d127 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d133
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d135 : levelOK d105 d124 5 (d127.map Prod.fst) ((d126.drop (0*8)).take 8) = true := by decide +kernel
lemma d136 : LevelN d106 d105 6 d126 := levelStep d108 d125 d134 (chunks 8 d126 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d135
  ))
lemma d137 : LowN d106 d105 7 := lowSearch d108 d136 (by decide +kernel)
def d138 : Nat := 0xfeeefac8feeefac8feeefac8feeefac8
def d139 : List Nat := l0
def d140 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,1,9),(4,1,17)]
lemma d141 : baseOK d138 d139 d140 = true := by decide +kernel
lemma d142 : SliceN d139 d138 (c25,5,[0, 1, 4, 3]) := mkSlice (w:=0) d141 d59 d68 (by decide +kernel)
def d143 : List SliceD := [(c25,5,[0, 1, 4, 3])]
lemma d144 : ∀ s ∈ d143, SliceN d139 d138 s := by
  unfold d143
  simp only [List.forall_mem_cons]
  exact ⟨d142,by simp⟩
def d145 : List StD := dupD [
 (l3,[(0,[])],[],[[0],[0],[0],[0],[0],[0],[0],[0],[0],[0]])]
def d146 : List StD := []
lemma d147 : LevelN d139 d138 4 d146 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d148 : levelOK d138 d143 4 (d146.map Prod.fst) ((d145.drop (0*8)).take 8) = true := by decide +kernel
lemma d149 : LevelN d139 d138 5 d145 := levelStep d141 d144 d147 (chunks 8 d145 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d148
  ))
lemma d150 : LowN d139 d138 6 := lowSearch d141 d149 (by decide +kernel)
def d151 : Nat := 0xfeeefae8feeefae8feeefae8feeefae8
def d152 : List Nat := l0
def d153 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,1,5),(3,1,9),(4,1,17)]
lemma d154 : baseOK d151 d152 d153 = true := by decide +kernel
lemma d155 : SliceN d152 d151 (c24,5,[0, 2, 3, 4]) := mkSlice (w:=0) d154 d59 d68 (by decide +kernel)
lemma d156 : SliceN d152 d151 (c28,4,[1, 2, 3, 4]) := mkSlice (w:=0) d154 d23 d37 (by decide +kernel)
lemma d157 : SliceN d152 d151 (c25,5,[0, 1, 4, 3]) := mkSlice (w:=0) d154 d59 d68 (by decide +kernel)
lemma d158 : SliceN d152 d151 (c23,5,[0, 1, 2, 4]) := mkSlice (w:=0) d154 d72 d81 (by decide +kernel)
lemma d159 : SliceN d152 d151 (c31,5,[0, 2, 1, 3]) := mkSlice (w:=0) d154 d72 d81 (by decide +kernel)
def d160 : List SliceD := [(c24,5,[0, 2, 3, 4]),(c28,4,[1, 2, 3, 4]),(c25,5,[0, 1, 4, 3]),(c23,5,[0, 1, 2, 4]),(c31,5,[0, 2, 1, 3])]
lemma d161 : ∀ s ∈ d160, SliceN d152 d151 s := by
  unfold d160
  simp only [List.forall_mem_cons]
  exact ⟨d155,d156,d157,d158,d159,by simp⟩
def d162 : List StD := dupD [
 (l3,[(0,[]),(1,[]),(2,[]),(3,[]),(4,[])],[(1,3),(0,3),(1,5),(0,5),(1,9),(0,9),(1,17),(0,17),(2,6),(18,24),(2,18),(6,10),(12,24),(10,18)],[[0,1000,1,1001],[1,2,1002,1003],[1,3,1004,1005],[1,4,1006,1007],[0,2,1008],[0,3,1009],[0,4,1010],[2,3,1011],[2,4,1012],[3,4,1013]])]
def d163 : List StD := []
lemma d164 : LevelN d152 d151 5 d163 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d165 : levelOK d151 d160 5 (d163.map Prod.fst) ((d162.drop (0*8)).take 8) = true := by decide +kernel
lemma d166 : LevelN d152 d151 6 d162 := levelStep d154 d161 d164 (chunks 8 d162 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d165
  ))
lemma d167 : LowN d152 d151 7 := lowSearch d154 d166 (by decide +kernel)
def d216 : Nat := 0xeac0eac0eac0eac0eac0eac0eac0eac0
def d217 : List Nat := [0, 1, 2, 3]
def d218 : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9)]
lemma d219 : baseOK d216 d217 d218 = true := by decide +kernel
lemma d220 : LowN d217 d216 3 := lowCount d219 (by decide +kernel)
def d221 : Nat := 0xfeeafcc8feeafcc8feeafcc8feeafcc8
def d222 : List Nat := l0
def d223 : List (Nat × Nat × Nat) := [(0,2,3),(1,1,3),(2,2,6),(3,2,10),(4,1,17)]
lemma d224 : baseOK d221 d222 d223 = true := by decide +kernel
lemma d225 : SliceN d222 d221 (c32,4,[1, 2, 3]) := mkSlice (w:=0) d224 d41 d55 (by decide +kernel)
lemma d226 : SliceN d222 d221 (c25,4,[0, 1, 3, 4]) := mkSlice (w:=0) d224 d23 d37 (by decide +kernel)
lemma d227 : SliceN d222 d221 (c23,4,[0, 1, 2, 4]) := mkSlice (w:=0) d224 d23 d37 (by decide +kernel)
lemma d228 : SliceN d222 d221 (c31,5,[1, 2, 3, 0]) := mkSlice (w:=0) d224 d59 d68 (by decide +kernel)
lemma d229 : SliceN d222 d221 (c10,5,[0, 1, 2, 3]) := mkSlice (w:=16) d224 d85 d94 (by decide +kernel)
lemma d230 : SliceN d222 d221 (c40,2,[0, 2, 3]) := mkSlice (w:=2) d224 d98 d99 (by decide +kernel)
lemma d231 : SliceN d222 d221 (c47,2,[3, 0, 4]) := mkSlice (w:=4) d224 d13 d14 (by decide +kernel)
lemma d232 : SliceN d222 d221 (c41,1,[0, 4]) := mkSlice (w:=0) d224 d3 d4 (by decide +kernel)
lemma d233 : SliceN d222 d221 (c48,2,[1, 3, 4]) := mkSlice (w:=5) d224 d98 d99 (by decide +kernel)
lemma d234 : SliceN d222 d221 (0xc0c00000c0c00000c0c00000c0c,1,[0, 3]) := mkSlice (w:=2) d224 d8 d9 (by decide +kernel)
lemma d235 : SliceN d222 d221 (c24,3,[0, 2, 3, 4]) := mkSlice (w:=0) d224 d219 d220 (by decide +kernel)
lemma d236 : SliceN d222 d221 (c82,2,[1, 2, 4]) := mkSlice (w:=9) d224 d98 d99 (by decide +kernel)
lemma d237 : SliceN d222 d221 (c9,3,[1, 2, 0, 4]) := mkSlice (w:=8) d224 d103 d104 (by decide +kernel)
lemma d238 : SliceN d222 d221 (c83,2,[2, 0, 4]) := mkSlice (w:=8) d224 d13 d14 (by decide +kernel)
lemma d239 : SliceN d222 d221 (c54,1,[0, 2]) := mkSlice (w:=2) d224 d8 d9 (by decide +kernel)
lemma d240 : SliceN d222 d221 (c58,2,[0, 1, 4]) := mkSlice (w:=0) d224 d18 d19 (by decide +kernel)
lemma d241 : SliceN d222 d221 (c42,2,[0, 2, 3]) := mkSlice (w:=18) d224 d98 d99 (by decide +kernel)
lemma d242 : SliceN d222 d221 (c55,2,[0, 1, 3]) := mkSlice (w:=20) d224 d98 d99 (by decide +kernel)
lemma d243 : SliceN d222 d221 (0x5050000050500000505000005050,1,[1, 3]) := mkSlice (w:=4) d224 d8 d9 (by decide +kernel)
lemma d244 : SliceN d222 d221 (c11,3,[1, 4, 3, 2]) := mkSlice (w:=1) d224 d103 d104 (by decide +kernel)
def d245 : List SliceD := [(c32,4,[1, 2, 3]),(c25,4,[0, 1, 3, 4]),(c23,4,[0, 1, 2, 4]),(c31,5,[1, 2, 3, 0]),(c10,5,[0, 1, 2, 3]),(c40,2,[0, 2, 3]),(c47,2,[3, 0, 4]),(c41,1,[0, 4]),(c48,2,[1, 3, 4]),(0xc0c00000c0c00000c0c00000c0c,1,[0, 3]),(c24,3,[0, 2, 3, 4]),(c82,2,[1, 2, 4]),(c9,3,[1, 2, 0, 4]),(c83,2,[2, 0, 4]),(c54,1,[0, 2]),(c58,2,[0, 1, 4]),(c42,2,[0, 2, 3]),(c55,2,[0, 1, 3]),(0x5050000050500000505000005050,1,[1, 3]),(c11,3,[1, 4, 3, 2])]
lemma d246 : ∀ s ∈ d245, SliceN d222 d221 s := by
  unfold d245
  simp only [List.forall_mem_cons]
  exact ⟨d225,d226,d227,d228,d229,d230,d231,d232,d233,d234,d235,d236,d237,d238,d239,d240,d241,d242,d243,d244,by simp⟩
def d247 : List StD := dupD [
 (l3,[(0,[]),(1,[]),(2,[]),(3,[]),(4,[])],[(2,3),(16,17),(20,21),(24,25),(8,12),(4,6),(2,6),(4,12),(8,10),(2,10)],[[0,1000,1001],[0,1002,1,1000],[0,1003,2,1000],[0,3,4],[1,1004,1005,1006],[2,1007,1008,1009],[0,4],[1,2,1006,1004,1007],[0,4],[0,4]])]
def d248 : List StD := dupD [
 (l7,[(0,[(1,0,1)]),(5,[]),(6,[]),(1,[]),(7,[]),(8,[]),(4,[(1,1,2)]),(3,[(2,0,1)]),(2,[])],[],[[0,1,2],[0,2,3],[0,1,4],[0,5],[1,5,6],[3,5],[3],[2,1],[0,6],[7],[3,2],[0,2,3],[8,1],[0,2,4],[0,6]]),
 ([0xc0c0c0c0c0c0c0c,c1,c0,c2,c3,c5],[(0,[]),(9,[]),(10,[]),(3,[(0,0,1)]),(3,[(1,0,1)]),(4,[]),(6,[]),(0,[(2,0,1)]),(8,[]),(4,[(2,1,2)]),(1,[])],[],[[0,1,2],[3],[4],[2,1],[0,5],[2,1],[1,6],[7,8],[1,8,9],[2,8,10],[2,1],[2,9,7],[1,6],[7,6,9],[1,9]]),
 ([c1,c0,c2,c3,c18,c5],[(0,[(1,0,2)]),(5,[]),(7,[]),(11,[]),(12,[]),(4,[(1,1,3)]),(13,[]),(2,[]),(1,[]),(3,[(2,0,2)])],[],[[0,1,2],[0,3],[0,4,2],[0,1,2],[1,3,5],[6,1],[7,3],[7],[0,5],[7,3],[8,1],[0,5],[9],[0,3,2],[0,3,2]]),
 ([0xcc00cc00cc00cc,c1,c0,c2,c3,c5],[(0,[]),(14,[]),(6,[]),(3,[(0,0,2)]),(1,[]),(10,[]),(3,[(1,0,2)]),(4,[]),(0,[(2,0,2)]),(7,[]),(12,[]),(4,[(2,1,3)]),(2,[])],[],[[0,1,2],[3],[4,1,5],[6],[0,7],[2,1],[8,2,9],[1,10],[1,11],[5,1],[2,10,12],[2,11,8],[1,2,10],[1,2,9],[8,10,9]]),
 ([c1,c0,c2,c3,c16,c5],[(0,[(1,1,2)]),(8,[]),(6,[]),(1,[]),(7,[]),(3,[(1,1,2)]),(4,[(1,2,3)]),(12,[]),(2,[]),(15,[])],[],[[0,1],[0,2,3],[0,1],[0,2,4],[5,1,6],[3,1],[2,7,8],[9,1],[0,6],[3,1],[8],[0,1,3],[3],[0,6],[0,1,4]])]
def d249 : List StD := dupD [
 ([c56,c1,c0,c2,c5],[(0,[]),(8,[]),(3,[(2,0,2)]),(1,[]),(3,[(0,0,2)]),(4,[]),(7,[]),(5,[]),(6,[]),(16,[]),(1,[(2,1,2)]),(17,[]),(18,[])],[],[[0,1],[2,3,4],[3,1],[0,5],[6,1,7],[6,8],[7,1,9],[10,1],[6,11,12],[6,1]]),
 ([c70,c1,c0,c3,c5],[(7,[]),(19,[]),(0,[]),(3,[(2,0,1)]),(5,[]),(3,[(0,0,1)]),(3,[(3,1,2)]),(12,[]),(3,[(0,1,2)]),(4,[]),(8,[]),(17,[]),(6,[]),(18,[])],[],[[0,1,2],[3,4,5],[6,7,8],[0,9,2],[0,4],[0,7],[4,10,11],[12,4],[0,11,13],[0,7]])]
def d250 : List StD := []
lemma d251 : LevelN d222 d221 3 d250 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d252 : levelOK d221 d245 3 (d250.map Prod.fst) ((d249.drop (0*8)).take 8) = true := by decide +kernel
lemma d253 : LevelN d222 d221 4 d249 := levelStep d224 d246 d251 (chunks 8 d249 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d252
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d254 : levelOK d221 d245 4 (d249.map Prod.fst) ((d248.drop (0*8)).take 8) = true := by decide +kernel
lemma d255 : LevelN d222 d221 5 d248 := levelStep d224 d246 d253 (chunks 8 d248 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d254
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d256 : levelOK d221 d245 5 (d248.map Prod.fst) ((d247.drop (0*8)).take 8) = true := by decide +kernel
lemma d257 : LevelN d222 d221 6 d247 := levelStep d224 d246 d255 (chunks 8 d247 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d256
  ))
lemma d258 : LowN d222 d221 7 := lowSearch d224 d257 (by decide +kernel)
def d384 : Nat := 0xfeeefac0feeefac0feeefac0feeefac0
def d385 : List Nat := l0
def d386 : List (Nat × Nat × Nat) := [(0,8,9),(1,4,6),(2,2,6),(3,1,9),(4,1,17)]
lemma d387 : baseOK d384 d385 d386 = true := by decide +kernel
lemma d388 : SliceN d385 d384 (c28,4,[1, 2, 3, 4]) := mkSlice (w:=0) d387 d23 d37 (by decide +kernel)
lemma d389 : SliceN d385 d384 (c24,4,[0, 3, 2, 4]) := mkSlice (w:=0) d387 d23 d37 (by decide +kernel)
lemma d390 : SliceN d385 d384 (c25,4,[0, 4, 1, 3]) := mkSlice (w:=0) d387 d23 d37 (by decide +kernel)
lemma d391 : SliceN d385 d384 (c23,4,[1, 4, 0, 2]) := mkSlice (w:=0) d387 d23 d37 (by decide +kernel)
lemma d392 : SliceN d385 d384 (c31,4,[2, 3, 0, 1]) := mkSlice (w:=0) d387 d23 d37 (by decide +kernel)
lemma d393 : SliceN d385 d384 (c11,3,[3, 4, 1, 2]) := mkSlice (w:=1) d387 d103 d104 (by decide +kernel)
lemma d394 : SliceN d385 d384 (c12,3,[2, 4, 3, 0]) := mkSlice (w:=2) d387 d103 d104 (by decide +kernel)
lemma d395 : SliceN d385 d384 (c110,1,[2, 3]) := mkSlice (w:=0) d387 d3 d4 (by decide +kernel)
lemma d396 : SliceN d385 d384 (c111,2,[4, 3, 0]) := mkSlice (w:=2) d387 d13 d14 (by decide +kernel)
lemma d397 : SliceN d385 d384 (c48,2,[1, 3, 4]) := mkSlice (w:=5) d387 d98 d99 (by decide +kernel)
lemma d398 : SliceN d385 d384 (c61,2,[0, 2, 4]) := mkSlice (w:=10) d387 d98 d99 (by decide +kernel)
lemma d399 : SliceN d385 d384 (c65,2,[4, 2, 1]) := mkSlice (w:=1) d387 d13 d14 (by decide +kernel)
lemma d400 : SliceN d385 d384 (c8,3,[1, 3, 0, 4]) := mkSlice (w:=4) d387 d103 d104 (by decide +kernel)
lemma d401 : SliceN d385 d384 (c112,1,[1, 4]) := mkSlice (w:=0) d387 d3 d4 (by decide +kernel)
lemma d402 : SliceN d385 d384 (c69,2,[2, 3, 4]) := mkSlice (w:=3) d387 d98 d99 (by decide +kernel)
lemma d403 : SliceN d385 d384 (c47,2,[3, 0, 4]) := mkSlice (w:=4) d387 d13 d14 (by decide +kernel)
lemma d404 : SliceN d385 d384 (c55,2,[0, 1, 3]) := mkSlice (w:=20) d387 d98 d99 (by decide +kernel)
lemma d405 : SliceN d385 d384 (c113,2,[3, 2, 1]) := mkSlice (w:=1) d387 d13 d14 (by decide +kernel)
lemma d406 : SliceN d385 d384 (c9,3,[0, 2, 1, 4]) := mkSlice (w:=8) d387 d103 d104 (by decide +kernel)
lemma d407 : SliceN d385 d384 (0xff000000ff000000ff000000ff000000,2,[0, 1, 2]) := mkSlice (w:=24) d387 d98 d99 (by decide +kernel)
lemma d408 : SliceN d385 d384 (c36,2,[1, 2, 4]) := mkSlice (w:=0) d387 d18 d19 (by decide +kernel)
lemma d409 : SliceN d385 d384 (c32,2,[2, 1, 3]) := mkSlice (w:=0) d387 d18 d19 (by decide +kernel)
lemma d410 : SliceN d385 d384 (c10,3,[0, 1, 2, 3]) := mkSlice (w:=16) d387 d103 d104 (by decide +kernel)
lemma d411 : SliceN d385 d384 (c35,2,[0, 3, 4]) := mkSlice (w:=0) d387 d18 d19 (by decide +kernel)
lemma d412 : SliceN d385 d384 (c74,2,[1, 0, 4]) := mkSlice (w:=4) d387 d13 d14 (by decide +kernel)
lemma d413 : SliceN d385 d384 (c40,2,[2, 0, 3]) := mkSlice (w:=2) d387 d13 d14 (by decide +kernel)
lemma d414 : SliceN d385 d384 (0x55005500550055005500550055005500,2,[2, 1, 4]) := mkSlice (w:=8) d387 d13 d14 (by decide +kernel)
lemma d415 : SliceN d385 d384 (c41,1,[0, 4]) := mkSlice (w:=0) d387 d3 d4 (by decide +kernel)
lemma d416 : SliceN d385 d384 (c44,2,[3, 2, 0]) := mkSlice (w:=0) d387 d18 d19 (by decide +kernel)
lemma d417 : SliceN d385 d384 (0x55550000555500005555000055550000,2,[1, 2, 3]) := mkSlice (w:=16) d387 d13 d14 (by decide +kernel)
lemma d418 : SliceN d385 d384 (0x303000003030000030300000303,1,[0, 3]) := mkSlice (w:=0) d387 d3 d4 (by decide +kernel)
lemma d419 : SliceN d385 d384 (0x33330000333300003333000033330000,2,[0, 2, 3]) := mkSlice (w:=16) d387 d13 d14 (by decide +kernel)
lemma d420 : SliceN d385 d384 (0xf000f000f000f000f000f000f000f00,2,[0, 1, 4]) := mkSlice (w:=8) d387 d13 d14 (by decide +kernel)
lemma d421 : SliceN d385 d384 (c114,1,[1, 2]) := mkSlice (w:=0) d387 d3 d4 (by decide +kernel)
def d422 : List SliceD := [(c28,4,[1, 2, 3, 4]),(c24,4,[0, 3, 2, 4]),(c25,4,[0, 4, 1, 3]),(c23,4,[1, 4, 0, 2]),(c31,4,[2, 3, 0, 1]),(c11,3,[3, 4, 1, 2]),(c12,3,[2, 4, 3, 0]),(c110,1,[2, 3]),(c111,2,[4, 3, 0]),(c48,2,[1, 3, 4]),(c61,2,[0, 2, 4]),(c65,2,[4, 2, 1]),(c8,3,[1, 3, 0, 4]),(c112,1,[1, 4]),(c69,2,[2, 3, 4]),(c47,2,[3, 0, 4]),(c55,2,[0, 1, 3]),(c113,2,[3, 2, 1]),(c9,3,[0, 2, 1, 4]),(0xff000000ff000000ff000000ff000000,2,[0, 1, 2]),(c36,2,[1, 2, 4]),(c32,2,[2, 1, 3]),(c10,3,[0, 1, 2, 3]),(c35,2,[0, 3, 4]),(c74,2,[1, 0, 4]),(c40,2,[2, 0, 3]),(0x55005500550055005500550055005500,2,[2, 1, 4]),(c41,1,[0, 4]),(c44,2,[3, 2, 0]),(0x55550000555500005555000055550000,2,[1, 2, 3]),(0x303000003030000030300000303,1,[0, 3]),(0x33330000333300003333000033330000,2,[0, 2, 3]),(0xf000f000f000f000f000f000f000f00,2,[0, 1, 4]),(c114,1,[1, 2])]
lemma d423 : ∀ s ∈ d422, SliceN d385 d384 s := by
  unfold d422
  simp only [List.forall_mem_cons]
  exact ⟨d388,d389,d390,d391,d392,d393,d394,d395,d396,d397,d398,d399,d400,d401,d402,d403,d404,d405,d406,d407,d408,d409,d410,d411,d412,d413,d414,d415,d416,d417,d418,d419,d420,d421,by simp⟩
def d424 : List StD := dupD [
 (l3,[(0,[]),(1,[]),(2,[]),(3,[]),(4,[])],[(4,6),(10,11),(5,7),(20,21),(3,7),(1,9),(1,17),(8,12),(24,26),(3,11),(2,18),(4,12),(24,28),(5,21),(20,28),(10,26)],[l2,[0,2,1001,1003,1004],[0,3,1003,1001,1005],[0,4,1001,1003,1006],[1,2,1007,1000,1004],[1,3,1000,1008,1009],[1,4,1000,1008,1010],[2,3,1004,1007,1011],[2,4,1004,1012,1013],[3,4,1005,1014,1015]])]
def d425 : List StD := dupD [
 ([c1,c0,c21,c2,c3,c5],[(0,[]),(1,[]),(5,[]),(6,[]),(2,[]),(7,[]),(4,[]),(8,[]),(9,[]),(10,[]),(11,[])],[],[[0,1],[1],[0,2],[0,2],[0,2],[0],[1,3],[1,3],[1,3],[4,2,5],[5,2],[6,2],[7,8],[5,8,7],[5,9,10]]),
 ([c1,c0,c2,c6,c3,c5],[(0,[]),(5,[]),(2,[]),(12,[]),(1,[]),(13,[]),(14,[]),(15,[]),(3,[]),(16,[]),(17,[])],[],[[0,1],[0,1],[2],[0,1],[0,1],[2,3],[4,1,5],[5,6,7],[7,6],[0],[2,3],[2,3],[8,1],[5,1],[5,9,10]]),
 ([c1,c0,c2,c3,c14,c5],[(0,[]),(5,[]),(3,[]),(13,[]),(14,[]),(9,[]),(18,[]),(17,[]),(19,[]),(2,[]),(20,[])],[],[[0,1],[0,1],[0,1],[2],[0,1],[3,4,5],[2,4,6],[3,1],[7,4,8],[2,5,6],[9,1,10],[3,5],[0],[2,6],[3,1]]),
 ([c1,c0,c2,c3,c5,c17],[(0,[]),(5,[]),(4,[]),(7,[]),(9,[]),(14,[]),(19,[]),(1,[]),(21,[]),(11,[]),(22,[])],[],[[0,1],[0,1],[0,1],[0,1],[2],[3,4,5],[3,5],[2,5,6],[7,1,8],[9,4,6],[2,4,6],[3,1],[2,10],[3,1],[0]]),
 (l7,[(1,[]),(9,[]),(6,[]),(2,[]),(14,[]),(12,[]),(0,[]),(23,[]),(24,[]),(10,[]),(25,[]),(16,[])],[],[[0,1,2],[3,4,5],[6,2,7],[8,1,9],[10,1,11],[0,2],[3],[0,2],[0,2],[0],[3,1],[3,1],[7,1],[7,1],[8,9]]),
 ([c1,c0,c2,c3,c18,c5],[(1,[]),(6,[]),(8,[]),(14,[]),(26,[]),(3,[]),(19,[]),(0,[]),(27,[]),(2,[]),(25,[])],[],[[0,1],[2,3,4],[5,3,6],[7,1,8],[4,3],[0,1],[0,1],[5],[0,1],[2,4,5],[9,1],[2,6,10],[0],[5,4],[8,1]]),
 ([c1,c0,c2,c3,c5,c72],[(1,[]),(6,[]),(8,[]),(14,[]),(16,[]),(7,[]),(25,[]),(0,[]),(28,[]),(4,[]),(19,[])],[],[[0,1],[2,3,4],[5,3],[6,3,4],[7,1,8],[0,1],[0,1],[0,1],[9],[2,4],[2,10,5],[5,1],[5,4],[5,1],[0]]),
 ([c1,c0,c2,c3,c16,c5],[(26,[]),(9,[]),(16,[]),(2,[]),(3,[]),(19,[]),(0,[]),(27,[]),(1,[]),(13,[]),(10,[])],[],[[0,1],[0,2,3],[4,1,5],[6,2,7],[0,1],[3,1],[4,0],[8,0,9],[7,2,10],[3,1],[4],[3,1],[3],[4,0],[7,0]]),
 ([c1,c0,c2,c3,c5,c20],[(15,[]),(9,[]),(29,[]),(2,[]),(4,[]),(19,[]),(0,[]),(30,[]),(24,[]),(1,[])],[],[[0,1,2],[2,0,3],[2,1],[4,1,5],[6,0,7],[3,1],[0,5,8],[0,2,4],[9,1],[3,0],[3,0],[4],[4,2],[7,0],[3]]),
 ([c1,c0,c2,c3,c5,c7],[(26,[]),(10,[]),(31,[]),(16,[]),(32,[]),(3,[]),(4,[]),(0,[]),(1,[]),(33,[])],[],[[0,1,2],[0,3,4],[5,1],[0,2,6],[7,1],[2,1],[2,0,5],[6,1,3],[8,0,9],[5,0],[4,2,6],[9,0],[5,0],[6],[5]])]
def d426 : List StD := dupD [
 ([0xeeee0000eeee,c1,c0,c2,c3],[(0,[]),(1,[]),(19,[]),(9,[]),(2,[]),(3,[]),(10,[]),(0,[(2,0,3)]),(16,[]),(14,[]),(1,[(2,0,3)]),(8,[])],[],[[0,1],[1,0],[2,3,4],[5,6],[7,3],[7,8,9],[7,2,3],[10,3,6],[10,2,9],[11,2,3]]),
 ([c27,c1,c0,c2,c5],[(0,[]),(2,[]),(19,[]),(14,[]),(1,[]),(10,[]),(16,[]),(4,[]),(0,[(2,1,2)]),(9,[]),(2,[(2,0,3)]),(15,[])],[],[[0,1],[2,3,4],[1,0],[5,6,7],[8,5,9],[8,3],[8,2,3],[10,3,6],[11,2,3],[10,2,9]]),
 ([c70,c1,c0,c3,c5],[(0,[]),(14,[]),(0,[(2,0,1)]),(0,[(0,0,1)]),(0,[(3,1,2)]),(19,[]),(0,[(0,1,2)]),(9,[]),(4,[]),(1,[(2,1,2)]),(10,[]),(3,[(2,0,3)]),(26,[])],[],[[0,1],[2,1,3],[4,5,6],[7,5,8],[9,7,10],[11,1,5],[12,1],[9,1],[9,1],[11,10]]),
 ([0x3333303033333030,c1,c2,c3,c5],[(0,[]),(9,[]),(0,[(3,0,1)]),(0,[(0,0,1)]),(3,[]),(19,[]),(0,[(3,0,3)]),(0,[(0,0,3)]),(2,[(2,1,2)]),(16,[]),(24,[]),(4,[(2,0,3)])],[],[[0,1],[2,1,3],[4,5],[6,5,7],[8,9],[10,1,5],[11,1,5],[8,1],[8,1],[10,9,11]]),
 ([c75,c0,c2,c3,c5],[(1,[]),(10,[]),(2,[]),(16,[]),(0,[]),(32,[]),(3,[(2,1,2)]),(4,[(2,1,2)]),(19,[])],[],[[0,1],[2,3],[4,1],[4,3],[5,1,3],[6,5],[7,1,3],[6,1],[5,8,7],[6,1]])]
def d427 : List StD := []
lemma d428 : LevelN d385 d384 3 d427 := by intro s h; cases h
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d429 : levelOK d384 d422 3 (d427.map Prod.fst) ((d426.drop (0*8)).take 8) = true := by decide +kernel
lemma d430 : LevelN d385 d384 4 d426 := levelStep d387 d423 d428 (chunks 8 d426 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d429
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d431 : levelOK d384 d422 4 (d426.map Prod.fst) ((d425.drop (0*8)).take 8) = true := by decide +kernel
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d432 : levelOK d384 d422 4 (d426.map Prod.fst) ((d425.drop (1*8)).take 8) = true := by decide +kernel
lemma d433 : LevelN d385 d384 5 d425 := levelStep d387 d423 d430 (chunks 8 d425 2 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d431
  · exact d432
  ))
set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
lemma d434 : levelOK d384 d422 5 (d425.map Prod.fst) ((d424.drop (0*8)).take 8) = true := by decide +kernel
lemma d435 : LevelN d385 d384 6 d424 := levelStep d387 d423 d433 (chunks 8 d424 1 (by omega) (by decide +kernel) (by
  intro i hi
  interval_cases i
  · exact d434
  ))
lemma d436 : LowN d385 d384 7 := lowSearch d387 d435 (by decide +kernel)
def postedEdgeFun (x : Fin 7 → Bool) : Bool :=
  decide (∃ i < ([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).length / 2,
    (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i) 0) false = true ∧
    (List.ofFn x).getD (([0, 2, 1, 3, 0, 4, 1, 4, 2, 4, 0, 5, 1, 5, 3, 5, 0, 6, 2, 6, 3, 6, 5, 6] : List ℕ).getD (2 * i + 1) 0) false = true)

def originalGWord : Nat := 0xfffffffffffefffafffeffeefefeeca0
def originalGRoots : List Nat := [0, 1, 2, 3, 4, 5, 6]
def originalGEssential : List (Nat × Nat × Nat) := [(0,4,5),(1,8,10),(2,1,5),(3,2,10),(4,1,17),(5,1,33),(6,1,65)]

lemma originalG_baseOK : baseOK originalGWord originalGRoots originalGEssential = true := by
  decide

lemma originalG_posted_table : ∀ r : Fin 128,
    postedEdgeFun (fun i => r.val.testBit i.val) = originalGWord.testBit r.val := by
  decide


end RestrictionSixProof

namespace RestrictionSixProof

def programCut (s : SliceD) (cs : List (Nat × Nat × Nat)) : CutV :=
  (s.1, s.2.1, cs.length, mkPool (initPool s.1 s.2.2) cs)

lemma programCut_sound {R T s} (hs : SliceN R T s)
    (cs : List (Nat × Nat × Nat)) : CutP R T (programCut s cs) := by
  obtain ⟨⟨f, roots, dom, base, nc, lo⟩, hv⟩ := hs
  have ps : PS f (roots.map observe) (initPool s.1 s.2.2) := by
    intro v hv'
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp hv'
    rw [rf_land dom]
    exact base _ (List.mem_map_of_mem (hv j hj))
  obtain ⟨bank, hb, hp⟩ :=
    mkPool_ok cs (Reach.start (u := true) (roots := roots.map observe)) ps
  refine ⟨f, roots, bank, dom, nc, ?_, hp, lo⟩
  simpa [programCut] using hb

lemma guessCut_sound {R T s k rest a b o ka kb}
    (hs : SliceN R T s) (cs : List (Nat × Nat × Nat))
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : cutEval k rest a b (nb o a b) ka kb (programCut s cs) = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset :=
  cut_sound (programCut_sound hs cs) nd h

def guessCuts (Z : List SliceD) (guess : SliceD → List (Nat × Nat × Nat))
    (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool) : Bool :=
  Z.any fun s => cutEval k rest a b z ka kb (programCut s (guess s))

lemma guessCuts_sound {R T Z k rest a b o ka kb}
    (hZ : ∀ s ∈ Z, SliceN R T s)
    (guess : SliceD → List (Nat × Nat × Nat))
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : guessCuts Z guess k rest a b (nb o a b) ka kb = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset := by
  obtain ⟨s, hs, hc⟩ := List.any_eq_true.mp h
  exact guessCut_sound (hZ s hs) (guess s) nd hc

end RestrictionSixProof

namespace AutoPool

def full : Nat := 0xffffffffffffffffffffffffffffffff

def inputs : List Nat := [0xaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaaa, 0xcccccccccccccccccccccccccccccccc, 0xf0f0f0f0f0f0f0f0f0f0f0f0f0f0f0f0, 0xff00ff00ff00ff00ff00ff00ff00ff00, 0xffff0000ffff0000ffff0000ffff0000, 0xffffffff00000000ffffffff00000000, 0xffffffffffffffff0000000000000000]

def var (v : Nat) : Nat := inputs.getD v 0

def low (v : Nat) : Nat := full ^^^ var v

def flip (w v : Nat) : Nat :=
  ((w &&& low v) <<< (1 <<< v)) ||| ((w >>> (1 <<< v)) &&& low v)

def table : Nat := 0xa0601a00aa05000a07a0800000660921900000000000090600060b000000000000000c0860c00000050a00080c00001900000021b000000000000c0721c00000011a00000041c00900000000000000000000000000080b41b005000000000905000000000000000000000c0500000000000000000000000000000000000000031a00000b00080900000000000700031900000000000000000070a01b000000419000000000008709000000000000000000000c06b0601c00cb0500080a41a000

def op (o a b : Nat) : Nat :=
  if o == 0 then a &&& b else if o == 1 then a ||| b
  else if o == 2 then a ^^^ (a &&& b) else b ^^^ (a &&& b)

def poolRun : List Nat → List (Nat × Nat × Nat) → List Nat
  | pool, [] => pool
  | pool, (o,a,b) :: cs => poolRun
      (pool ++ [op o (pool.getD a 0) (pool.getD b 0)]) cs

def available (d : Nat) (pool : List Nat) (raw : Nat) : Bool :=
  let w := raw &&& d
  w == 0 || w == d || pool.any (fun a => w == (a &&& d) || w == (a &&& d ^^^ d))

def truth (anchor : Nat) (support : List Nat) (w : Nat) : Nat :=
  (List.range 8).foldl (fun bits r =>
    let pos := (support.zipIdx).foldl (fun pos (v,i) =>
      if r.testBit i then pos ||| (1 <<< v) else pos) anchor
    if w.testBit pos then bits ||| (1 <<< r) else bits) 0

def guessOne (d : Nat) (vs pool : List Nat) (raw : Nat) : List (Nat × Nat × Nat) :=
  if available d pool raw then [] else
  let anchor := Nat.log2 (d ^^^ (d - 1))
  let masked := raw &&& d
  let w := if masked.testBit anchor then masked ^^^ d else masked
  let support := vs.filter (fun v => (w ^^^ flip w v) &&& d != 0)
  if support.length < 2 || 3 < support.length then [] else
  let code := (table >>> (12 * (truth anchor support w / 2))) &&& 4095
  if code == 0 then [] else
  let c := (code &&& 255) - 1
  let o := c % 4
  let a := vs.idxOf (support.getD ((c / 4) % 4) 0)
  let b := vs.idxOf (support.getD (c / 16) 0)
  if code < 256 then [(o,a,b)] else
  let c' := code / 256 - 1
  [(o,a,b), (c' % 4, pool.length, vs.idxOf (support.getD (c' / 4) 0))]

def guessAux (d : Nat) (vs : List Nat) : List Nat → List Nat → List (Nat × Nat × Nat)
  | _, [] => []
  | pool, w :: ws =>
    let program := guessOne d vs pool w
    program ++ guessAux d vs (poolRun pool program) ws

def guess (d : Nat) (vs ws : List Nat) : List (Nat × Nat × Nat) :=
  guessAux d vs (vs.map (fun v => var v &&& d)) ws

end AutoPool

namespace RestrictionSixProof

def autoCuts (Z : List SliceD) (ws : List Nat)
    (k : Nat) (rest : List Nat) (a b z : Nat) (ka kb : Bool) : Bool :=
  guessCuts Z (fun s => AutoPool.guess s.1 s.2.2 ws) k rest a b z ka kb

lemma autoCut_sound {R T s k rest a b o ka kb}
    (hs : SliceN R T s) (ws : List Nat)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : cutEval k rest a b (nb o a b) ka kb
      (programCut s (AutoPool.guess s.1 s.2.2 ws)) = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset :=
  guessCut_sound hs (AutoPool.guess s.1 s.2.2 ws) nd h

lemma autoCuts_sound {R T Z k rest a b o ka kb}
    (hZ : ∀ s ∈ Z, SliceN R T s) (ws : List Nat)
    (nd : (kidW rest a b (nb o a b) ka kb).Nodup)
    (h : autoCuts Z ws k rest a b (nb o a b) ka kb = true) :
    Impossible true (W T) k (kidW rest a b (nb o a b) ka kb).toFinset :=
  guessCuts_sound hZ (fun s => AutoPool.guess s.1 s.2.2 ws) nd h

end RestrictionSixProof

namespace SmallMissingFive

open RestrictionSixProof

def roots : List Nat := [0,1,2,3,4]
def witnesses : List (Nat × Nat × Nat) := [(0,8,9),(1,8,10),(2,16,20),(3,1,9),(4,1,17)]
def target31 : Nat := 0xfefeee00fefeee00fefeee00fefeee00
def target47 : Nat := 0xfffaee00fffaee00fffaee00fffaee00
def slice31 : SliceD := (0x55555555555555555555555555555555,4,[1,4,2,3])
def slice47 : SliceD := (0x33333333333333333333333333333333,5,[4,0,3,2])
def rest : List Nat := [1,2,3,4].map xN

lemma initial_eq : kidW rest (xN 0) (xN 0) (nb 0 (xN 0) (xN 0)) false false = rootsW roots := by
  decide +kernel

lemma lowOfInitialCut {T E K s}
    (hb : baseOK T roots E = true) (hs : SliceN roots T s)
    (hcut : cutEval K rest (xN 0) (xN 0) (nb 0 (xN 0) (xN 0)) false false
      (programCut s []) = true) : LowN roots T (K+1) := by
  apply lowOf hb
  have hn : (kidW rest (xN 0) (xN 0) (nb 0 (xN 0) (xN 0)) false false).Nodup := by
    rw [initial_eq]
    exact (baseOK_ok hb).nodup
  have hi := guessCut_sound hs [] hn hcut
  rw [initial_eq] at hi
  exact hi

lemma base31 : baseOK target31 roots witnesses = true := by decide +kernel
lemma base47 : baseOK target47 roots witnesses = true := by decide +kernel

lemma slice31_sound : SliceN roots target31 slice31 :=
  mkSlice (w := 0) base31 d23 d37 (by decide +kernel)

lemma slice47_sound : SliceN roots target47 slice47 :=
  mkSlice (w := 0) base47 d59 d68 (by decide +kernel)

lemma low31 : LowN roots target31 5 :=
  lowOfInitialCut base31 slice31_sound (by decide +kernel)

lemma low47 : LowN roots target47 6 :=
  lowOfInitialCut base47 slice47_sound (by decide +kernel)

end SmallMissingFive

end PEqualNP.Outside.L_meta_10760


namespace PEqualNP.Outside.L_meta_10760.RestrictionSixProof

lemma live_to_basic {u target k S} (h : Live u target k S) :
    live basicOps target k S := by
  induction h using Live.ind with
  | stop hp => rfl
  | @binary k U a b d hd ha hb hab hf tail ih =>
    refine Or.inr ⟨a, by simp, b, by simp, hab, bin d a b, ?_, hf, U, rfl, ih⟩
    rcases allowed_four hd with rfl | rfl | ⟨_,rfl⟩ | ⟨_,rfl⟩ <;>
      simp [basicOps, ops, bin, BitVec.and_comm]

lemma live_critical_coloring {u : Bool} {k : Nat} {target g : Sig} {S : Finset Sig}
    (run : Live u g k S) (hg : g = target ∨ g = ~~~target) :
    ∃ color : Sig → Nat,
      (∀ a ∈ S, color a < k + 2 - S.card) ∧
      ∀ a b, criticalPair target S a b → color a ≠ color b :=
  live_criticalPair_coloring (live_to_basic run) hg

end PEqualNP.Outside.L_meta_10760.RestrictionSixProof


namespace PEqualNP.Outside.L_meta_10760.RestrictionSixProof

lemma impossible_of_criticalEdge {u : Bool} {target a b : Sig} {cap : Nat}
    {S : Finset Sig} (edge : criticalPair target S a b)
    (bound : cap + 2 - S.card ≤ 1) : Impossible u target cap S := by
  intro k hk run
  obtain ⟨color, hc, he⟩ := live_critical_coloring run (Or.inl rfl)
  have ha := hc a edge.1
  have hb := hc b edge.2.1
  have hab := he a b edge
  omega

lemma impossible_of_criticalTriangle {u : Bool} {target a b c : Sig} {cap : Nat}
    {S : Finset Sig} (ab : criticalPair target S a b)
    (ac : criticalPair target S a c) (bc : criticalPair target S b c)
    (bound : cap + 2 - S.card ≤ 2) : Impossible u target cap S := by
  intro k hk run
  obtain ⟨color, hc, he⟩ := live_critical_coloring run (Or.inl rfl)
  have ha := hc a ab.1
  have hb := hc b ab.2.1
  have hcc := hc c ac.2.1
  have hab := he a b ab
  have hac := he a c ac
  have hbc := he b c bc
  omega

lemma impossible_of_criticalK4 {u : Bool} {target a b c d : Sig} {cap : Nat}
    {S : Finset Sig} (ab : criticalPair target S a b)
    (ac : criticalPair target S a c) (ad : criticalPair target S a d)
    (bc : criticalPair target S b c) (bd : criticalPair target S b d)
    (cd : criticalPair target S c d)
    (bound : cap + 2 - S.card ≤ 3) : Impossible u target cap S := by
  intro k hk run
  obtain ⟨color, hc, he⟩ := live_critical_coloring run (Or.inl rfl)
  have ha := hc a ab.1
  have hb := hc b ab.2.1
  have hcc := hc c ac.2.1
  have hd := hc d ad.2.1
  have hab := he a b ab
  have hac := he a c ac
  have had := he a d ad
  have hbc := he b c bc
  have hbd := he b d bd
  have hcd := he c d cd
  omega

end PEqualNP.Outside.L_meta_10760.RestrictionSixProof


namespace PEqualNP.Outside.L_meta_10760

lemma live_clique_card_bound {width k : Nat} {target g : BitVec width}
    {S C : Finset (BitVec width)} (run : live basicOps g k S)
    (hg : g = target ∨ g = ~~~target) (sub : C ⊆ S)
    (clique : ∀ c ∈ C, ∀ d ∈ C, c ≠ d → criticalPair target S c d) :
    C.card + S.card ≤ k + 2 := by
  induction k generalizing S C with
  | zero =>
    change S = {g} at run
    subst S
    have := Finset.card_le_card sub
    simpa using Nat.add_le_add_right this 1
  | succ k ih =>
    rcases run with skip | ⟨a, ha, b, hb, hab, z, hz, fresh, U, rfl, tail⟩
    · have := ih skip sub clique
      omega
    · let V := if a ∈ U then C.erase a else C
      let W := if b ∈ U then V.erase b else V
      have hWC : W ⊆ C := by
        intro c hc
        by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U <;>
          simp only [W, V, haU, hbU, ite_true, ite_false, Finset.mem_erase] at hc <;>
          tauto
      have hna : ∀ c ∈ W, c = a → a ∉ U := by
        intro c hc eq hm
        subst c
        by_cases hbU : b ∈ U <;> simp [W, V, hm, hbU] at hc
      have hnb : ∀ c ∈ W, c = b → b ∉ U := by
        intro c hc eq hm
        subst c
        simp [W, hm] at hc
      have step : ∀ c ∈ W, ∀ d ∈ W, c ≠ d →
          criticalPair target (insert z U)
            (ChromRelation.moved a b z c) (ChromRelation.moved a b z d) := by
        intro c hc d hd hcd
        exact ChromRelation.criticalPair_step hab hz fresh tail hg
          (hna c hc) (hnb c hc) (hna d hd) (hnb d hd)
          (clique c (hWC hc) d (hWC hd) hcd)
      let D := W.image (ChromRelation.moved a b z)
      have hD : D ⊆ insert z U := by
        intro c hc
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hc
        exact ChromRelation.moved_mem (sub (hWC hw))
      have hclique : ∀ c ∈ D, ∀ d ∈ D, c ≠ d →
          criticalPair target (insert z U) c d := by
        intro c hc d hd hcd
        obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hc
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hd
        exact step w hw v hv (fun eq => hcd (congrArg _ eq))
      have hcard : D.card = W.card := by
        apply Finset.card_image_of_injOn
        intro c hc d hd eq
        by_contra hne
        exact (step c hc d hd hne).2.2.1 eq
      have loss : C.card ≤ W.card +
          ((if a ∈ U then 1 else 0) + (if b ∈ U then 1 else 0)) := by
        have h₁ := Finset.pred_card_le_card_erase (s := C) (a := a)
        have h₂ := Finset.pred_card_le_card_erase (s := C) (a := b)
        have h₃ := Finset.pred_card_le_card_erase (s := C.erase a) (a := b)
        by_cases haU : a ∈ U <;> by_cases hbU : b ∈ U <;>
          simp only [W, V, haU, hbU, ite_true, ite_false] <;> omega
      have bound := ih tail hD hclique
      have count := ChromGeneric.retained_card hab fresh
      omega

namespace RestrictionSixProof

lemma impossible_of_criticalClique {u : Bool} {target : Sig} {cap : Nat}
    {S C : Finset Sig} (sub : C ⊆ S)
    (clique : ∀ c ∈ C, ∀ d ∈ C, c ≠ d → criticalPair target S c d)
    (bound : cap + 2 - S.card < C.card) : Impossible u target cap S := by
  intro k hk run
  have := live_clique_card_bound (live_to_basic run) (Or.inl rfl) sub clique
  omega

end RestrictionSixProof

end PEqualNP.Outside.L_meta_10760
