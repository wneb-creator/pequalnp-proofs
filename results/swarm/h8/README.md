# Helper 8 research artifacts for L-meta-2373

These are research artifacts, not a proof of the posted gap. No pull request is
opened by this helper. The eventual proof submission must contain only the
required Lean file.

The native program explores the `Live` contraction model from the checked
`L_meta_670.lean` definitions. Its initial set is all nine H9 input signatures
and the signature `x4 OR x6`. The targets are:

- monotone mode: no live computation using at most 15 further binary gates;
- signed mode: no live computation using at most 14 further binary gates,
  with complements available freely.

Both native searches close. This has **not** been replayed as a complete Lean
certificate. Translating it into a bound for arbitrary circuits with that
first gate also needs an extraction argument, raw-input necessity in the
presence of the extra OR, and handling an unused extra OR. These artifacts
do not establish the full 10-input, 19-gate bound.

`generate.py` reads the pinned, checked L670 source already in this repository.
It emits exact 512-bit signatures, projection pools, 12 H9 automorphisms, and
decoded prior certificate states. It performs no network requests. Its small
Python `probe` function is an independent monotone reference implementation.

`probe.cpp` uses full-signature state equality modulo those automorphisms.
Monotone mode uses all 144 boundary pairs and both monotone/signed prior bounds.
Signed mode uses only signed prior bounds and the original 152 signed sample
pairs. An optional exact 512-row collision check strengthens signed pruning.
Prefix operations used to supply a projection pool are charged individually.
Different histories of the same semantic state may have different pools;
keeping one history weakens pruning and does not strengthen a bound.

`factor-cut.hpp` applies only to monotone states with at most one shared
intermediate, as justified by the existing `oneShare`, `kwCross`, `hornRule`,
and `parityRule` lemmas. It extracts forced rectangle owners, parity constraints,
and Horn implications. Its native UNSAT test still needs the associated Lean
semantic replay. All 18,324 emitted factor cuts were independently replayed in
Python. The separate Lean helper contains a small general kernel checker for
such propositional cores, rather than a proof of every native state.

To reproduce from the repository root, choose a scratch output directory and
run these commands with that directory as the working directory for each
native executable:

```sh
python3 results/swarm/h8/generate.py --out-dir /tmp/oec/pnp-swarm-2373-8/replay
python3 results/swarm/h8/generate.py --signed --out-dir /tmp/oec/pnp-swarm-2373-8/replay
g++ -O3 -std=c++20 -I /tmp/oec/pnp-swarm-2373-8/replay results/swarm/h8/probe.cpp -o /tmp/oec/pnp-swarm-2373-8/replay/mono
g++ -O3 -std=c++20 -DSIGNED_MODE -I /tmp/oec/pnp-swarm-2373-8/replay results/swarm/h8/probe.cpp -o /tmp/oec/pnp-swarm-2373-8/replay/signed
```

Inside that scratch directory, `./mono 15 1 1` runs the monotone query;
`./signed 14 1 0 0` runs the signed query using the original samples;
`./signed 14 1 0 1` adds exact row collisions. The numeric arguments are depth,
whether all paid-prefix subsets are considered, whether monotone factor cuts
are enabled, and whether signed full-row collisions are enabled. An optional
fifth argument is the prior-state binary file path. Complete stdout/stderr
should be redirected to files. Sample complete stdout is included here;
timings depend on the machine and concurrent proof builds.

The Lean helper's seven-row result is separate: an explicit 18-gate near-miss
prefix cannot be repaired by any three appended fan-in-two AND/OR/NOT gates,
even with arbitrary output selection, constants, and forward/default reads.
It does not exclude rewiring the prefix.
