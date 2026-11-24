The seven-input graph has a,b,c,A,B,C,h mapped to0,2,4,9,5,8,10.
Its nine edges are AB,AC,BC,aA,bB,cC,ha,hb,hc.
Their complement in the full graph consists exactly of
14,18,36,37,67,6-10,79.

Those seven remaining edges have the nine-gate expression

    6*(3 OR7 OR10) OR 7*(3 OR9) OR 1*(4 OR8).

The three products cost3,2,2 gates respectively; two final ORs cost2.
Therefore ANY exact11-gate circuit for the seven-input graph gives a
full21-gate circuit by adjoining these nine gates and one final OR.
No exposed h-star or other internal interface is required. Any accidental
sharing with the local gadget only lowers this upper bound.

This corrects the conservative earlier wording in gadget7_contributors.py
and its archived result, which said a local11 result did not automatically
lift. It does lift using this improved residual cover. The seven-input
11-gate circuit remains unknown. The retained12-gate local control lifts
to a scalar-checked22-gate whole circuit, not a21-gate witness or Lean proof.
