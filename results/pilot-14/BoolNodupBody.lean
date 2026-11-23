namespace PEqualNP.Outside.L_meta_670_aux.BoolNodup

open LiveCheck

def check : List Sig → Bool
  | [] => true
  | a :: v => !(v.contains a) && check v

lemma check_eq_true (v : List Sig) : check v = true ↔ v.Nodup := by
  induction v with
  | nil => simp [check]
  | cons a v ih => simp [check,ih,List.nodup_cons]

lemma sound {v : List Sig} (h : check v = true) : v.Nodup :=
  (check_eq_true v).mp h

end PEqualNP.Outside.L_meta_670_aux.BoolNodup
