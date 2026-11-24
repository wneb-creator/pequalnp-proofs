# Mixed complement routing obstructions

Both examples below are scalar-verified auxiliary circuits, not Lean results or counterexamples to the39-gate gap. They are nonminimal: removing the shared router and keeping the direct line ORs gives the39-gate baseline. They show why constant-freeness alone does not turn certificate supports into one fixed support per wire.

Use lines L={0,1,3,9} and M={1,2,4,10}. Their common outside set X={5,6,7,8,11,12}; write A=M\L={2,4,10}=a1+A2 and B=L\M={0,3,9}=b1+B2, taking a1=2,b1=0. Set u=a1 OR AND(B2), v=AND(A2) OR b1.

The first shared gate is AND(X) AND u AND v. Its minterms have sizes8,9,9,10; the two9-point complements both first appear at the same final AND gate. The8-point cross term meets both lines, so the shared signal is band-positive and bounded by both target ORs on the band. Adding it to those two direct line outputs and retaining the other11 direct outputs gives52 gates. Every gate is nonconstant on the band, but the shared signal is false on all seven-true inputs. Independent8192-bit validation passed.

The stronger shared gate is (AND(X) OR (a1 AND b1)) AND u AND v. Its minterms have sizes2,9,9,10. The two9-point complements again first appear at one AND gate, now wire25. The full embedding has54 gates, with every gate true on some seven-true row and false on some eight-true row. This satisfies the stronger endpoint guard but remains nonminimal. Its scalar verifier checks all3003 band outputs, every gate's endpoint witnesses, all shared minterms and earliest certificate positions.

The OR-preparation nodes route different certificate supports for different owners. Any proof of a mixed-circuit lower bound must charge that routing, use minimum-count/private-node surgery, or supply another justified normalization. The pure-support parent graph cannot be used unchanged.
