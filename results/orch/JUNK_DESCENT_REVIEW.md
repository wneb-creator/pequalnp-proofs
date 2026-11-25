Independent root review: dirty-gate descent
Result: PASS. Both new extensions read in full.
JunkDrop.lean 64lines SHA256 aac3fea5b0b8a1855c3f4b68eaddd63be6483854b15617a6247d640df0a1fcca
JunkRestore.lean 100lines SHA256 62e325053c061d20d92646ec3d83446808e38e5486afbec6906cc90c175625c9
Both extension bodies are present verbatim in compiled assembly SHA256 6426666212b23af8e0772a5238c3ce21861aed0ba8adb98ab3dc70fafad202ef
The alias semantic relation and forced-value monotonicity send every retained dirty gate to an original dirty gate. Strict origin order provides injection; the selected gate is excluded.
Restoration preserves old gate values and adds only one AND. Its OR path to the correctly computed graph output makes that new AND productive, so no dirty gate is added.
The result strictly decreases junk cardinality for the explicit restoration whenever q is dirty and the restored circuit is AO2 and computes the graph function. It does not establish that every dirty gate admits such a semantic repair.
Author compilation exit0; complete junk-drop-build.log and junk-restore-build.log saved.
