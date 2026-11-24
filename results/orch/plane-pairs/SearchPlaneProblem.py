import json
from pathlib import Path

DATA=json.loads(Path(__file__).with_suffix('.json').read_text())
N=42
POINTS=21
EDGES=[tuple(e) for e in DATA['edges']]
NEIGHBORS=[tuple(v if u==a else u for u,v in EDGES if a in (u,v)) for a in range(N)]
POSITIVES={(1<<u)|(1<<v) for u,v in EDGES}
NEGATIVES=set(DATA['maximal_negatives'])
RAW_NEGATIVES=NEGATIVES
TESTS=sorted(POSITIVES)+sorted(NEGATIVES)
INPUT_MASKS=[sum(1<<t for t,x in enumerate(TESTS) if x>>j&1) for j in range(N)]
TARGET=(1<<len(POSITIVES))-1
ALL_TESTS=(1<<len(TESTS))-1
AUTOMORPHISMS=[tuple(a) for a in DATA['multipliers']]

def bits(mask):
    while mask:
        low=mask & -mask
        yield low.bit_length()-1
        mask-=low
