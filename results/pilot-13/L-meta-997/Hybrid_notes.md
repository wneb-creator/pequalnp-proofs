# Hybrid route, 2026-11-23

For a positive circuit with the unique NOT frozen to a switch, write
A_g(x)=C1_g(x), B_g(x)=C0_g(Y union x), H_g=A_g AND B_g.
The proposed selected outputs are H_i=C1_i for meeting sets and H_j=OR(T_j)
for disjoint sets. AND propagates H with one gate. OR requires the two
cross terms A_u AND B_v and A_v AND B_u in addition to H_u OR H_v.

## Safe relaxation

Exact intermediate hybrid functions are unnecessary. It suffices to build
monotone output functions below H that retain every true singleton.
For heavy outputs this forces equality with OR(T); for light outputs it
preserves correctness below k. Any intermediate hybrid with at most one
true singleton may be replaced by that input, or by false when it has none.
This replacement is a lower bound and preserves singleton values.

For distinct linear owners S and T, a light-private/heavy-private gate has
hybrid singleton support contained in S intersection T, hence at most one.
An individual cross term with such differently owned factors likewise has
at most one singleton. Replacing the cross term removes its AND but may
still need an extra OR to join that input; it is not automatically free
as a whole binary-circuit operation.

## Concrete barrier to a purely local rewrite

Let h=y1 AND y2 AND y3 and z=NOT h. Define

u=a OR (z AND p),
v=b OR (h AND p),
w=u OR v.

The original w is OR(a,b,p). Take heavy output OR(w,t,r), with
T={a,b,p,t,r}, and meeting output y1 OR v, with S={y1,b}.
These are exact linear OR outputs, S intersection T={b}, and |Y|=3.
At w the hybrid predecessors have singleton supports of size at most one:
H_u=a and H_v=b OR (h AND p). But H_w=OR(a,b,p).
One binary monotone gate over any earlier hybrid wires cannot have three
true singleton inputs, so it cannot implement H_w. Gate w is not a refund
gate: both of its window supports are {a,b,p}, properly inside T and not S.
Therefore local rewriting with extra gates allowed only at refund nodes
fails. Earlier gates must be repurposed or removed. This is not a
counterexample to the posted total gate bound.

The example also shows why insisting on H at every node is too strict:
using A_u=OR(a,p), which is globally T-sound, makes the final linear output
easy. Owner-relative interpolants may exceed H internally while remaining
sound for their intended heavy output.

## Verified general obstruction

Read on 2026-11-23 from:
https://github.com/c1emon/pequalnp-proofs/blob/L-meta-1035/lean/PEqualNP/Outside/L_meta_1035.lean

The supplied five-input counterexample uses NOT directly on input zero.
Its nineteen gates compute seventeen monotone outputs, and the file proves
that nineteen monotone gates cannot compute the same outputs. For Y={0},
the hybrid equals each original monotone output: at x0=0, A=f<=B; at x0=1,
B=f<=A. Thus universal size-preserving hybrid conversion is false.
The linear-output hypothesis must be used globally.

## Remaining plausible resource

Keep the light private regions of heavy owners as well as the meeting
owners. Gates private to heavy T in the light window cannot be private to
a meeting S. They can pay for cofactor extraction when unused by the heavy
forest; same-owner overlaps instead provide anchors. Cross-owner overlap
can lose heavy singleton information in H, but A=T at the heavy output
forces this information to reappear through other paths. No injection or
global capacity argument for that compensation has been proved yet.
