# UNCHECKED final actual one/any-center plane wrapper

UniqueAnyCenterPlaneWrapper.lean is a 107-line namespace fragment, not a standalone checked Lean file. It has never been assembled with all dependencies and compiled. Its provisional independent source review is included, but that review is not a successful Lean build and does not establish a new lower bound. It is deliberately excluded from the checked snapshot list.

The generic UniqueAnyProductBudget backend did subsequently compile successfully; that checked result and its complete failed/successful build logs are preserved separately. Its successful build does not check this actual wrapper. No combined actual one/any build was launched, so there is no failed or held combined-build stdout log to preserve.

The intended wrapper composes actual minimum-junk connector and paired-reader facts with the generic backend and private-edge contrapositive. The listed dependencies are the intended frozen input set; assembly completeness and all elaboration remain unchecked. Reuse the repository pinned Lean/Mathlib environment and the documented declaration assembler, handle its known exact duplicate indented-definition limitation, and run a full build before calling the actual wrapper checked.

Dependency hashes:

- results/orch/lemmas/PlaneTwoJunkPrivate.lean: 23c37958d3660f05d2c98d94ea12d55e4bbc4caa5c3a6023e3498b2875b997b2
- results/orch/lemmas/UniqueCenterActual.lean: 2bcd0b0667c187830e919a17669b6dd9708164204f86c14e3e0d239a696eb8b3
- results/orch/lemmas/FirstLayerTwoCenters.lean: c3f7a73cfab134d0fe89c810d962079850c21bd3fcda7e5a997c6b3385e1cc7b
- results/orch/lemmas/FirstLayerReader.lean: 57e4373519f908afb588c7d7df109a403773014b83d3b2c567b827cabfef5b99
- results/orch/lemmas/UniqueAnyProductBudget.lean: 92a54582f63794dfb2aaf764b8a74b7fd5e690b4f9a293bf9c276512da429e33
