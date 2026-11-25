L-meta-2590 monotone restriction strengthening

The posted target is the20-gate lower bound for monotone Petersen circuits, with constants, unary gates and invalid/default-false wires permitted by Monotone2. The new result being assembled is a partial bound: every such circuit needs at least18 gates. A normalized live computation whose first binary operation is AND needs at least19. Neither is the full target.

Construction:

- L_meta_4332 contains monoRoot, a checked impossibility certificate for a15-gate monotone computation of the nine-variable Petersen vertex-deletion cofactor. Its inputs and graph truth table are byte-identical to the cofactor used by L_meta_6581 and our previous Binary17 extension.
- Removing only signed-root-specific tables and unused final circuit wrappers yields MonoBase.lean,479175bytes/6622lines. The exact source ranges are recorded in generate_mono_base.py. The source includes the bridge nineMonoFloor : Lower false inputs graph16.
- The old ten-input Extended model and projection geometry can therefore be reused unchanged. Monotone circuit extraction uses mode false, while still allowing empty/unary AND/OR and default-false invalid wires.
- Peel the first binary gate, with operands v,u. Finite witnesses force the original pin v to remain necessary even when that first output is available. Projecting v=false makes every supplied root an original cofactor pin or a constant. The sixteen-gate cofactor bound plus one constant-root charge gives17 suffix gates, hence18 total.
- If the first normalized binary gate is AND, both v and its fresh output project to zero. Two distinct original roots supply two constant charges, yielding18 suffix gates and19 total.

Files:

- lemmas/MonoBase.lean: pruned actual certificate; export was interrupted on the lease HTTP410 stop instruction. Session72077 exited130. It did not complete verification.
- lemmas/MonoExtension.lean: new extractor and charging lemmas.
- lemmas/Mono18.lean: full proposed concatenation,519562bytes/7398lines, SHA256 ca145c55fe4e69cd551725a543318b389e73a4e3cc93299a3f015819b020e26f.
- generate_mono_extension.py: creates the extension test and full concatenation, enforcing the524288-byte limit and forbidden-text checks.

Checks completed:

- partial_lean checked nineMonoFloorOfCert against the old exported model, without adding axioms.
- MonoRealizeCheck.lean passed Lean, checking the fresh monotone circuit extraction including all gate arities allowed by Monotone2.
- MonoExtensionConditional.lean passed Lean with an explicit16-gate cofactor-floor hypothesis. It checks the whole40KB extension, including all geometry and both new bounds. Only inherited linter warnings remain.
- status_check independently reviewed the full proposed source and found no semantic or format issue. The review confirmed byte-identical cofactor tables, the mode-false extraction, permitted projected roots, and the one/two constant charges.

Remaining checks: the actual MonoBase certificate export and a final concatenated source export. Both are UNVERIFIED because root stopped the task after renewal returned HTTP410 at15:22 UTC. The full20-gate claim is still unproved. No further2590 proof work was performed after the stop instruction.

Complete logs are preserved in mono-base-interrupted.stdout/.stderr, mono-realize-checked.stdout/.stderr, and mono-extension-conditional-checked.stdout/.stderr. The two successful scratch test sources are also copied into lemmas/. No claim is made that the full519562-byte assembly compiled.

Possible route beyond the partial: every Petersen vertex-deletion cofactor needs16 gates, so exhibiting a restriction eliminating four original gates would prove20. Fresh_proof owns the first-OR / small-fanout analysis. partial_lean checked that a raw edge minterm AND a monotone function is either unchanged or false on every pair input; this may force raw edge wires to have only OR readers in a minimal productive circuit. A third constant charge or an independent fourth deleted gate is still needed beyond the straightforward first-AND proof.
