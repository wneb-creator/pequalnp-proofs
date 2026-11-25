import PEqualNP.Outside.L_meta_2592

namespace PEqualNP.Outside.L_meta_2592
namespace SharedOrThird

open Floor17

def orPin (a b : Fin 10) : Extended.Sig := Extended.bin 1 (pin a) (pin b)
def gate (a b c : Fin 10) : Extended.Sig := Extended.bin 0 (orPin a b) (orPin a c)

def rowData : List (ℕ × ℕ) := [(0,0),(512,640),(768,800),(544,800),(512,576),(512,528),(520,524),(544,545),(768,776),(516,518),(128,640),(0,0),(128,160),(192,448),(384,448),(129,145),(128,132),(144,145),(384,392),(192,194),(96,608),(32,160),(0,0),(32,288),(544,608),(544,560),(40,44),(32,33),(48,56),(96,98),(384,896),(768,896),(256,288),(0,0),(256,320),(768,784),(384,388),(272,273),(256,264),(260,262),(64,576),(96,224),(192,224),(64,320),(0,0),(65,81),(192,196),(96,97),(80,88),(64,66),(16,528),(48,176),(144,176),(48,304),(272,336),(0,0),(144,148),(16,17),(16,24),(80,82),(68,580),(4,132),(260,292),(36,292),(516,580),(516,532),(0,0),(36,37),(4,12),(4,6),(129,641),(513,641),(1,33),(65,321),(513,577),(1,17),(129,133),(0,0),(257,265),(1,3),(136,648),(520,648),(136,168),(8,264),(520,584),(8,24),(8,12),(40,41),(0,0),(72,74),(130,642),(514,642),(130,162),(34,290),(2,66),(514,530),(2,6),(2,3),(258,266),(0,0)]

def rows (a b : Fin 10) : Extended.Row × Extended.Row :=
  let r := rowData.getD (a.val * 10 + b.val) (0,0)
  (Fin.ofNat 1024 r.1,Fin.ofNat 1024 r.2)

set_option maxRecDepth 32768 in
set_option maxHeartbeats 0 in
lemma witness : ∀ a b : Fin 10, a ≠ b →
    let r := (rows a b).1
    let s := (rows a b).2
    Extended.bit r Extended.target ≠ Extended.bit s Extended.target ∧
    Extended.bit r (orPin a b) = Extended.bit s (orPin a b) ∧
    ∀ i : Fin 10, i ≠ b → Extended.bit r (pin i) = Extended.bit s (pin i) := by
  decide +kernel

lemma or_same {a c b : Fin 10} {r s : Extended.Row}
    (hba : b ≠ a) (hbc : b ≠ c)
    (same : ∀ i : Fin 10, i ≠ b → Extended.bit r (pin i) = Extended.bit s (pin i)) :
    Extended.bit r (orPin a c) = Extended.bit s (orPin a c) := by
  have h := congrArg₂ Bool.or (same a (Ne.symm hba)) (same c (Ne.symm hbc))
  simpa [orPin,Extended.bin,Extended.bit] using h

lemma retain {a b c : Fin 10} {k : Nat} {U : Finset Extended.Sig}
    (hba : b ≠ a) (hbc : b ≠ c)
    (raw : ∀ w ∈ U, w ∈ Extended.pins ∨ w = orPin a b ∨ w = orPin a c)
    (run : Extended.Live true Extended.target k (insert (gate a b c) U)) : pin b ∈ U := by
  classical
  by_contra missing
  obtain ⟨targetDifferent,firstSame,pinSame⟩ := witness a b (Ne.symm hba)
  have secondSame := or_same hba hbc pinSame
  have gateSame : Extended.bit (rows a b).1 (gate a b c) =
      Extended.bit (rows a b).2 (gate a b c) := by
    have h := congrArg₂ Bool.and firstSame secondSame
    simpa [gate,Extended.bin,Extended.bit] using h
  obtain ⟨w,hw,different⟩ := Extended.live_row_difference run targetDifferent
  rcases Finset.mem_insert.mp hw with rfl|hw
  · exact different gateSame
  · rcases raw w hw with hp|rfl|rfl
    · obtain ⟨i,rfl⟩ := pinComplete w hp
      have hib : i ≠ b := by intro h; subst i; exact missing hw
      exact different (pinSame i hib)
    · exact different firstSame
    · exact different secondSame

lemma pin_mem (i : Fin 10) : pin i ∈ Extended.pins := by
  rw [pinList]
  exact List.mem_ofFn.mpr ⟨i,rfl⟩

lemma or_project (a b c : Fin 10) :
    restrictRows (projection c) (Extended.observe (orPin a b)) =
      combine true (restrictRows (projection c) (Extended.observe (pin a)))
        (restrictRows (projection c) (Extended.observe (pin b))) := by
  rw [orPin,Extended.obs_bin,restrict_comb]
  rfl

lemma leaf_projection (a b : Fin 10) :
    restrictRows (projection b) (Extended.observe (orPin a b)) =
      restrictRows (projection b) (Extended.observe (pin a)) := by
  rw [or_project,pin_zero_wire]
  funext r
  simp [combine]

lemma gate_projection (a b c : Fin 10) :
    restrictRows (projection b) (Extended.observe (gate a b c)) =
      restrictRows (projection b) (Extended.observe (pin a)) := by
  rw [gate,Extended.obs_bin,restrict_comb,leaf_projection,or_project]
  funext r
  cases h : restrictRows (projection b) (Extended.observe (pin a)) r <;>
    simp [comb,combine,h]

lemma available_cons {R : Type} {u : Bool} {roots : List (Wire R)}
    {v : Wire R} (h : Available u roots v) (w : Wire R) : Available u (w :: roots) v := by
  rcases h with h|h|⟨hu,h⟩
  · exact Or.inl (List.mem_cons_of_mem w h)
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr ⟨hu,List.mem_cons_of_mem w h⟩)

lemma tail_bound {a b c : Fin 10} {k : Nat} {U : Finset Extended.Sig}
    (hba : b ≠ a) (hbc : b ≠ c)
    (raw : ∀ w ∈ U, w ∈ Extended.pins ∨ w = orPin a b ∨ w = orPin a c)
    (fresh : gate a b c ∉ U)
    (run : Extended.Live true Extended.target k (insert (gate a b c) U)) : 15 ≤ k := by
  classical
  let ws := gate a b c :: U.toList
  have nd : ws.Nodup :=
    List.nodup_cons.mpr ⟨by simpa using fresh,Finset.nodup_toList U⟩
  have eqS : ws.toFinset = insert (gate a b c) U := by simp [ws]
  have hrun := Extended.list_run run ws nd eqS
  have same : restrictRows (projection b) (Extended.observe Extended.target) = observe graph := by
    rw [Floor17.observe_projected,projectionGoal]
  let q := restrictRows (projection b) (Extended.observe (orPin a c))
  let roots := inputs.map observe
  have reachQ : Reach true roots 1 (q :: roots) := by
    have h := Reach.two true (u := true) (Reach.start (roots := roots))
      (projected_available b (pin a) (pin_mem a))
      (projected_available b (pin c) (pin_mem c))
    simpa [q,or_project] using h
  have supplyQ : supply true (q :: roots)
      ((ws.map Extended.observe).map (restrictRows (projection b))) := by
    intro w hw
    obtain ⟨_,hmem,rfl⟩ := List.mem_map.mp hw
    obtain ⟨z,hz,rfl⟩ := List.mem_map.mp hmem
    change z ∈ gate a b c :: U.toList at hz
    rcases List.mem_cons.mp hz with rfl|hz
    · rw [gate_projection]
      exact available_cons (projected_available b (pin a) (pin_mem a)) q
    · rcases raw z (by simpa using hz) with hp|rfl|rfl
      · exact available_cons (projected_available b z hp) q
      · rw [leaf_projection]
        exact available_cons (projected_available b (pin a) (pin_mem a)) q
      · exact Or.inl (by simp [q])
  have lower := projected_bound (projection b) hrun (same ▸ observe_proper graph_proper)
    reachQ supplyQ (L := 15) (same ▸ nineFloor)
  have keep := retain hba hbc raw run
  have pinMem : restrictRows (projection b) (Extended.observe (pin b)) ∈
      ((ws.map Extended.observe).map (restrictRows (projection b))) :=
    List.mem_map.mpr ⟨_,List.mem_map.mpr ⟨_,by simp [ws,keep],rfl⟩,rfl⟩
  have charge := mass_one pinMem (show Constant
      (restrictRows (projection b) (Extended.observe (pin b))) from ⟨false,pin_zero_wire b⟩)
  omega

lemma prefix_bound {a b c : Fin 10} {k : Nat} {U : Finset Extended.Sig}
    (hba : b ≠ a) (hbc : b ≠ c)
    (raw : ∀ w ∈ U, w ∈ Extended.pins ∨ w = orPin a b ∨ w = orPin a c)
    (fresh : gate a b c ∉ U)
    (run : Extended.Live true Extended.target k (insert (gate a b c) U)) : 18 ≤ k + 3 := by
  have bound := tail_bound hba hbc raw fresh run
  omega

end SharedOrThird
end PEqualNP.Outside.L_meta_2592
