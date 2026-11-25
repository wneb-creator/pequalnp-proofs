Algebra of the 18-gate near-circuit

Let Y1 = x1 OR x3 OR x7, Y2 = x0 OR x3 OR x9, Y3 = x0 OR x7 OR x8, and Y4 = x1 OR x8 OR x9. Let S be the OR of x2 AND Y1, x4 AND Y2, x5 AND Y3, and x6 AND Y4. Let M = (x0 AND x1) OR (x3 AND x8) OR (x7 AND x9), and Q = Y1 AND Y2 AND Y3 AND Y4.

The Petersen function is S OR M. The near-circuit is S OR Q. Its 18 gates arise by sharing the eight gates that build the four Y signals and factoring the x2 branch as Y1 AND (x2 OR (Y2 AND Y3 AND Y4)). Both identities were checked on all 1,024 inputs. The four false positives are precisely the four three-element neighbor sets that define the Y signals; each is a maximal independent set.

Set x2 = x4 = x5 = x6 = false. Then S vanishes and the remaining problem is to replace Q by the three-edge matching function M. Among the existing wires, every wire true on all four errors is also true on every matching input. Consequently, taking its NOT as a conjunctive mask removes the whole matching function and requires another branch to restore it. There is no existing nonzero wire whose restricted function implies M. Exhausting one new AND/OR gate over existing wires yields only three nonzero functions that imply M: the three individual matching edges. No such one-gate rescue supplies the entire M.

There is also an immediate monotonicity obstruction to an unmodified star rescue: if a positive mask predicate is true on an error triple, it stays true when more of the six matching variables are set. The star branches remain false on this entire six-variable restriction. A true matching extension would therefore remain suppressed. A successful restructuring must introduce a positive rescue branch that survives when all four center variables are false; the existing star branches cannot supply it.

These computations rule out simple local masking ideas, not arbitrary 19-gate circuits. The finite computations and exact wire indices are in near-symbolic-analysis.json. The script also checks ordered input-pair symmetry: 120 automorphisms, one orbit of 30 ordered edge pairs, and one orbit of 60 ordered nonedge pairs. None of this file's reasoning has yet been formalized in Lean.
