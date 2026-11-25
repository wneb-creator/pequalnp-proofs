from pathlib import Path
import json, re

HERE = Path(__file__).resolve().parent

def check(name, n=None, edges=None, marks=()):
    d = json.loads((HERE / name).read_text())
    n = d.get("n", n)
    edges = d.get("edges", edges)
    gs = d["gates"]
    out = d["output"]
    assert 0 <= out < n + len(gs)
    for j, (op, a, b) in enumerate(gs):
        assert op in ("and", "or") and 0 <= a < n+j and 0 <= b < n+j and a != b
    def values(row):
        w = [bool(row >> i & 1) for i in range(n)]
        for op, a, b in gs:
            w.append(w[a] and w[b] if op == "and" else w[a] or w[b])
        return w
    def trace(base, source):
        w = values(1 << base)
        v = [i == source for i in range(n)]
        for op, a, b in gs:
            v.append((w[a] and v[b]) or (v[a] and w[b]) if op == "and" else v[a] or v[b])
        return v[out]
    if n <= 11:
        rows = list(range(1 << n))
    else:
        assert n == 26
        negatives = []
        for left in range(1 << 13):
            right = sum(1 << j for j in range(13) if not any(left >> i & 1 and (i,j+13) in edges for i in range(13)))
            closed_left = sum(1 << i for i in range(13) if not any(right >> j & 1 and (i,j+13) in edges for j in range(13)))
            if closed_left == left:
                negatives.append(left | (right << 13))
        assert len(negatives) == 704
        rows = negatives + [(1 << a) | (1 << b) for a,b in edges]
    for row in rows:
        expected = any(row >> a & 1 and row >> b & 1 for a,b in edges)
        assert values(row)[out] == bool(expected), (name, row)
    for a,b in marks:
        assert not trace(a,b) and not trace(b,a), (name, a,b)
    print(json.dumps(dict(file=name, gates=len(gs), checked_rows=len(rows), double_edges=list(marks), status="PASS")))

for p in sorted(HERE.glob("*.witness.json")):
    m = re.search(r"-double-(\d+)-(\d+)", p.name)
    check(p.name, marks=[tuple(map(int,m.groups()))] if m else [])
for name in ["polarized-225.json", "polarized-227.json", "mixed-027.json"]:
    d = json.loads((HERE/name).read_text())
    check(name, marks=d["double_edges"])
check("tree10-double12-witness.json", marks=[(1,7)])
edges = [(i,j+13) for i in range(13) for j in range(13) if (i-j)%13 in [0,1,3,9]]
check("plane65-witness.json", n=26, edges=edges, marks=[(0,13)])
