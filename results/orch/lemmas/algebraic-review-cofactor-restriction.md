Independent review by algebraic_route

Source: structural-cofactor-slack-next.lean
SHA256: 411e53a60d058eba7c2d7ce30016a2f00d07126995fee461c73c5205ef640930

PASS on the new restriction-wrapper source. The original cof_restrict and cof_restrict_graph constructions are retained, with a final universal strict-slack consequence proved using the same cof_Inv witness. All prior semantic, strictness, liveness, budget, and protected-input conclusions remain unchanged. The graph wrapper derives essentiality from sem_Gr and passes through the same cofactor circuit. This does not assert every lost unit is absent from cof_kept; the strict-slack alternative is precisely retained. Cached compilation succeeded according to the author; standalone full-source build is still pending at review time. No forbidden trust or format markers occur in the new tails.
