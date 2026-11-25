# L-meta-2583 normal-form route

Active gap switched from 2592 after HTTP410; all old work remains frozen.

## Exact obstruction

ReadK.IsReadK 1 means each prime implicant has some proof tree reading each variable at most once. It does not require a globally read-once formula. For projective-plane incidence, prime implicants are the point-line incident pairs. The canonical circuit ORs the N line stars, with N(q+2)-1 gates.

Existing L_meta_7684 constructs the canonical star-cover circuit and verifies read1. Existing L_meta_7639, or the more general L_meta_6369, proves the sharp edge-plus-cover lower bound for an already-read1 circuit. Thus the target normalization is as strong as proving the unrestricted sharp lower bound.

## Checked descendant structure

- L_meta_1499 has actual circuit deletion/redirection constructors V1 and V2. V2 removes an internal gate, redirects its readers to an earlier operand, and appends an OR with an earlier implicant gate. V2_out and V2_AO2 preserve function and exact size.
- L_meta_3653 eliminates a unique dirty AND that accepts a singleton, assuming lift fixed point and no AND input is already below the target.
- L_meta_3700 handles the unique dirty AND with no singleton accepted.
- L_meta_8933 proves the sharp bound if no dirty AND accepts two distinct edges both lacking read1 parses.
- L_meta_3444 and L_meta_3446 refute naive budget counts for maximal core cones. A core-overlap counting argument needs additional structure.

## Concrete helper

results/orch/lemmas/OrLift2583.lean extracts the minimal semantic and redirect infrastructure from L_meta_1499 into namespace PEqualNP.Outside.L_meta_2583_aux.OrLift and adds explicit IsAO2 wrappers:

1. lift_or_implicant: an OR reading an earlier gate whose value implies the output can be deleted and that implicant ORed at the output, preserving function and exact size.
2. delete_and_above_implicant: an AND reading such an implicant can be deleted, preserving function and saving exactly one gate.

The wrappers concern actual circuits. They do not claim that iterating the OR lift yields read1. The remaining issue is a terminal block whose internal dirty ANDs overlap on multiple edges.

## Failed shortcuts

Truncating every wire to its degree-two component is not a size-preserving operation. The singleton component of an AND can implement set intersection, e.g. (a OR b) AND (a OR c) accepts singleton a while also carrying a quadratic term bc. Removing repeated leaves independently in each parse would destroy circuit sharing.

## Normalization progress

- OrLift2583.lean compiled at SHA256 5d8f2c04974fba8e0753ba7dc6b57f2dff01c6144991d12b38a8ad167a132f2b; 477 lines, independently reviewed. The OR-lift theorem describes the explicit V2 circuit, so it carries actual structural content. Also proves that every reader of an implicant gate in a least circuit is an OR.
- OrLiftFixed2583.lean compiled at SHA256 c6f9a8796832ba3038065e6b1e0db463a9dacb5299e846e84cb257daabc6a2e9; 585 lines, independently reviewed. Shows all retained wire values can only decrease under OR hoisting, then injects newly dirty OR gates into the old dirty OR gates excluding the deleted gate. Hence the dirty-OR count strictly decreases.
- NormalForm2583.lean adds the finite-measure minimization: any correct IsAO2 circuit computing a nonzero graph function has a no-larger least circuit which is Core.IsLiftFixedPoint. Draft statically reviewed, first compile queued. This proves the sketch preprocessing for arbitrary graphs, without any four-cycle assumption. It does not prove read1 or a sharp lower bound for the terminal cores.

The search agent can soundly restrict a size-optimal witness to have no below-target operand feeding AND and no mixed clean/dirty OR. Do not additionally assume internal AND gates reject singleton inputs; that stronger claim is unproved.

The unrestricted Fano lower bound27 was located in helper ao27 of existing L_meta_7997. The lower-bound agent reports that it fundamentally relies on finite Fano adjacency cases and residual-unit rigidity, rather than an immediately reusable all-q argument.
