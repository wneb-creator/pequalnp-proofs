# CaDiCaL persistence capability

Read2026-11-25. Installed binary reports version2.1.2. Its saved complete help documents `-o` for simplified DIMACS output, `-e` for the reconstruction/extension stack, and compressed output when the filename ends in`.gz`.

The matching public header says the DIMACS export contains current irredundant clauses and derived units, excluding redundant clauses and the reconstruction stack. Consequently this export preserves some simplification work but is not a complete CDCL search checkpoint. The documented CLI offers no input option for restoring the extension stack. A SAT assignment of the simplified formula must not be decoded as an assignment of the original formula without reconstruction and independent validation.

Source: https://github.com/arminbiere/cadical/blob/rel-2.1.2/src/cadical.hpp, `write_dimacs` and `write_extension` declarations. The installed complete help is preserved in the earlier search archive.

The selected next run is one continuous3600-second solve of the original, hash-verified CNF. Optional exports preserve useful artifacts at normal termination, while the ordinary SAT model still comes from the original solver and uses its own reconstruction. No claim of resumability is made. The current900-second process is unchanged.
