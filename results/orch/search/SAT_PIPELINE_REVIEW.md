# Independent SAT pipeline review

Reviewer: `/root/toolchain`. Scope: the current OR-count searches for the theta graph, Fano incidence graph, and C6 positive control. These checks support experimental search coverage; they do not constitute a Lean lower-bound proof or a checked UNSAT certificate.

Reviewed scripts (SHA256):

- `augment-raw-pairs.py`: `72f4ec6535ef93aa822e6d0d059e5e9a20adc8c419241f8b92f3922407764d6d`
- `smt-to-cnf.py`: `555b8dcb810fdaad90d3321793eaa08af22f7e49349300e145056ecd9e18b3ff`
- `first-or-orbits.py`: `09fcd336d1c04ae1719766164e17dbedba6eb969274e64bf2243d54f1c9b351b`
- `validate-free-model.py`: `b480dca97246d65f09b6668a749f6ae330328c3021481aadbd21f0c2bafe5f08`
- Base generator `freegate-synth.py`: `e9fbd256ff307da27127d864a5b514e6c14d58a6ec9ca8ae1e0d6c3649be4fba`

No soundness/completeness defect found in the added constraints for these inputs. A conjunction operand containing two raw inputs that are not an edge vanishes on every positive edge assignment. The existing positive-exclusive witness constraint therefore already excludes it. The added raw-pair clauses are redundant in this setting.

Adjacent independent-gate ordering can be imposed by choosing a lexicographically minimal topological gate ordering. It composes with first-OR graph symmetry: minimize the whole sequence of gate truth vectors over graph automorphisms and topological orders. Such a sequence satisfies both families of constraints. Swapping an OR gate's two operands restores their existing numeric ordering without changing any gate value. The boundary rows are invariant under the verified graph automorphisms. A first-gate operand with a positive witness must be either a singleton raw input or one edge conjunction, exactly the candidate terms considered by the orbit script.

The CNF converter parses the assertion set, removes solver options and check commands, and applies `simplify`, `bit-blast`, then `tseitin-cnf`. It requires one subgoal and emits that goal's DIMACS. These tactics preserve satisfiability for these quantifier-free bit-vector inputs. Source, SMT, and CNF hashes in all three metadata chains were independently checked and matched.

The C6 positive control has five counted OR gates. Its SAT assignment independently satisfies all 2,963 emitted CNF clauses, with zero false clauses and zero unassigned variables. The decoded circuit's separate exhaustive validator reports agreement on all 64 Boolean assignments. The symmetry metadata contains 12 C6 automorphisms and 8 canonical first-OR pairs; theta has 12 and 18, and Fano has 336 and 8.

The scripts expect the supplied graph and dimensions to match the underlying OR query. The orbit script verifies this for the current composed pipeline, including the first gate being `bvor`, the exact boundary row set, and the output truth vector. This review does not license these augmentation rules for arbitrary SMT input or AND-mode queries.
