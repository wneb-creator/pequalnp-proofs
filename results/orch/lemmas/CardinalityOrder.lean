import CountTransport

namespace PEqualNP.Outside.L_meta_2592_aux.Certificate.LinkN

lemma atMostOne_clauseOrder : fNotAtMost 10 19 1 =
    (List.range 19).flatMap (fun a =>
      ((List.range 19).filter (fun b => decide (a < b))).map (fun b =>
        [2110 * a + 9, 2110 * b + 9])) := by
  decide +kernel

lemma atMostTwo_clauseOrder : fNotAtMost 10 19 2 =
    (List.range 19).flatMap (fun a =>
      ((List.range 19).filter (fun b => decide (a < b))).flatMap (fun b =>
        ((List.range 19).filter (fun c => decide (b < c))).map (fun c =>
          [2110 * a + 9, 2110 * b + 9, 2110 * c + 9]))) := by
  decide +kernel

end PEqualNP.Outside.L_meta_2592_aux.Certificate.LinkN
