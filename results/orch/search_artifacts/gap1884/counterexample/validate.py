import argparse
import json
from pathlib import Path

EDGES = [(0,1),(1,2),(2,3),(3,4),(4,0),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(9,6),(6,8),(8,5)]

def check(path):
    c = json.loads(Path(path).read_text())
    assert c['physical_inputs'] == 11
    assert c['input_map'] == list(range(10)) and c['free_unary'] == 'not'
    bad = []
    for row in range(1024):
        w = [bool(row >> i & 1) for i in range(10)] + [not bool(row & 1)]
        for j, (op, a, b) in enumerate(c['gates']):
            assert op in range(5) and a >= 0 and b >= 0
            # getD on any unavailable wire gives false, exactly as Circuit.wires.
            aa = w[a] if a < len(w) else False
            bb = w[b] if b < len(w) else False
            w.append(aa and bb if op == 0 else aa or bb if op == 1 else not aa if op == 2 else op == 3)
        value = w[c['output']] if c['output'] < len(w) else False
        target = any((row >> a & 1) and (row >> b & 1) for a, b in EDGES)
        if value != target:
            bad.append(row)
    return {'circuit': str(path), 'gates': len(c['gates']), 'full_rows': 1024, 'wrong_rows': len(bad), 'bad_rows': bad,
            'is_posted_counterexample': len(c['gates']) <= 18 and not bad,
            'input_map': c['input_map'], 'free_unary': c['free_unary'],
            'gate_interpretation': '0 AND[a,b]; 1 OR[a,b]; 2 NOT[a]; 3 AND[]; 4 OR[]; unavailable reads false'}

if __name__ == '__main__':
    p = argparse.ArgumentParser()
    p.add_argument('circuits', nargs='+')
    p.add_argument('--output', required=True)
    args = p.parse_args()
    results = [check(path) for path in args.circuits]
    Path(args.output).write_text(json.dumps(results, indent=2) + '\n')
    for r in results:
        print(r['circuit'], 'gates', r['gates'], 'wrong', r['wrong_rows'], 'counterexample', r['is_posted_counterexample'])
