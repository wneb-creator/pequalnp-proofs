Finite synthesis attempts for L-meta-11929

These searches were stopped after the parent reported a Lean-checked refutation of the posted negative statement. Neither eight-gate search found a model. Both reached their 30-second limit and are UNKNOWN; they prove no lower bound.

synthesize.py encodes backward binary AND/OR gates and optionally one unary NOT gate on all 128 inputs. The operation and operand selectors are shared across input assignments. Dead gates and arbitrary gate output selection are allowed. The one-NOT run requires exactly one NOT; the monotone run forbids all NOTs. Constants, unary AND/OR, and forward references are omitted, so a standalone UNSAT claim would also need a normalization argument to cover the full posted syntax.

The pinned nine-gate monotone positive control passed. decode.py independently evaluated its circuit on all 128 assignments and checked every encoded gate value. Source, metadata, complete solver logs, and decoded positive-control data are preserved here. No satisfying eight-gate model or Lean lower-bound claim is supplied by these searches.
