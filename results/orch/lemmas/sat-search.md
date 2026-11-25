# SAT counterexample search for L-meta-2592

CaDiCaL was built from the public arminbiere/cadical repository under task scratch. A C++ incremental CEGIS encoder models 19 binary AND/OR or unary NOT gates, exact-one wire selectors, acyclic references to earlier wires, output at the last gate, at least one NOT, and all gates live. A witness is evaluated independently on all 1024 inputs.

The 20-gate known monotone witness supplied by the counterexample agent passes the encoding with all selectors fixed and passes the independent 1024-input check. Generic 20-gate synthesis was undecided after 60 seconds; that is not a lower bound.

For the 19-gate four-error candidate (18 live monotone gates plus one dead NOT), a neighborhood with at most four changed gate triples is UNSAT in 2 seconds on 72 selected assignments. This is only a restricted computational result and is not Lean checked. A six-change neighborhood and a general first-gate-NOT-input shard remain in progress. Variants relocating the dead NOT to each slot have been generated.

Files in scratch: synth.cpp, seed952.txt, seed952-notpos0.txt through seed952-notpos18.txt, planted20.stdout, repair952-budget4.stdout, repair952-budget6.stdout, search19-notinput.stdout. All stdout/stderr is retained.

2026-11-25T13:59:21.054773+00:00 Pivoted to six-input, five-output synthesis. Let (a,b,c,d,e,f) map to Petersen inputs(0,2,6,4,7,8). Targets are A=b∨d∨f, B=a∨b∨c, C=a∨e∨f, D=d∨c∨e, and N constrained only by D∧N=(a∧d)∨(b∧e)∨(c∧f). An11-gate vector circuit with aNOT yields a19-gate Petersen circuit after8outer gates. The11-gate SAT instance has all64inputs and exactlyoneNOT; firstOR(a,b) is one symmetry shard only. A planted13-gate full-vector circuit passed independent checking. Previous relocatedNOT four-change repairs: slots3–17 UNSAT, slots0–2 undecided after30s. No Lean claims arise from these computational searches.

2026-11-25T14:02:01.248821+00:00 The11-gate conditional-vector oneNOT firstOR(a,b) shard returned UNSAT after60seconds. The corresponding unrestricted-firstgate instance is running with900second budget. Neither result is a checked Lean theorem. CaDiCaL source commit: e4d9bd93af444c6575a908a24da2c4130cb2a1c7. Conditional encoder SHA256:5fa373443a737db6cd65ae8c506d89038881956b80c3ae11a10286398b814f4b.
