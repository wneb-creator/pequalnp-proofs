# Fano circuit searches

These searches have not found a counterexample. SAT witnesses are independently checked on all Boolean inputs. UNSAT reports refer to the encoded normalized circuit model and are not Lean certificates.

`fano_unread_sat.py` adds an exact squarefree proof-state condition for a fixed incident edge. Its three small controls passed; the encoding was independently reviewed. The `--solver` flag chooses a CaDiCaL executable. `--edge-stabilizer` uses the verified16-element stabilizer ofedge{0,7}; `--ordered` is optional and was omitted in the current fixed-edge search.

Current fixed-edge program SHA256: 852e1b47934b75410b0107e21af7935fc2039291bfeec5a0b43df4781e7b51b3
