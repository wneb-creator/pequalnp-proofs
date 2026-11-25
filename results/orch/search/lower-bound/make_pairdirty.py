from pathlib import Path

source = Path('/tmp/oec/pequalnp-pilot-70/circuit-search/synthesize.py').read_text()
changes = [
    ("canon=[226,", "small_false_start = len(rows)\nrows.extend([0] + [1 << i for i in range(14)] + [(1 << i) | (1 << j) for i in range(14) for j in range(i + 1, 14) if not target((1 << i) | (1 << j))])\ncanon=[226,"),
    ("structure=[]\n", "structure=[]\ndirty_flags=[]\n"),
    (" if not args.allow_trivial:\n", " dirty=var();dirty_flags.append(dirty)\n clause(-dirty,-op)\n clause(-dirty,*out[small_false_start:])\n for x in out[small_false_start:]:clause(op,-x,dirty)\n if not args.allow_trivial:\n"),
    ("if not args.no_liveness:\n", "dummy=var()\nexactly_one([dummy]+dirty_flags)\n\nif not args.no_liveness:\n"),
    ("'prefix':args.prefix}))", "'prefix':args.prefix,'dirty_flags':dirty_flags,'small_false_start':small_false_start}))"),
]
for before, after in changes:
    assert source.count(before) == 1, before
    source = source.replace(before, after)
Path('/tmp/oec/pequalnp-pilot-70/lower-bound/pairdirty_synthesize.py').write_text(source)
