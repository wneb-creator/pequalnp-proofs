# Profile-normalized bounded-cost preparation

Completed, independently approved research preparation only. No63-gate
witness or Lean proof is present. The running K16 query uses its earlier
unchanged source; this distinct variant has not had a long target run.

Source dd56f6421182cbbd2c3f19e335711b2e59eab4f785be78ad7b523f133864c6fb
adds only nonzero positive profiles for active records and direct primary
edge ANDs for singleton profiles. The supplied argument/tests show these
changes preserve positive values, decrease negative values, and never
increase the independent-OR membership cost. No operand disjointness or
first-AND incident-edge anchor is imposed. The rejected anchor and its
overlap obstruction are documented separately.

The positive native control decodes64 gates and passes all756 boundary
rows; fixing that same star at budget63 returns external UNSAT. The nested
63-gate warm model still misses six positive rows and has0 false
positives. The full native-model/phase audit is preserved, alongside all
complete stdout/stderr logs. These controls do not prove a target result.

Raw CNFs are omitted. CNF-REGENERATION.json provides exact source/CNF
identities and portable emit-only argv; create REGEN first. The source
creates its output directory. Native use also needs its named CaDiCaL.
