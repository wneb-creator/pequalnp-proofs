from pathlib import Path
import ast
import hashlib
import itertools
import json
import re
from functools import lru_cache

ROOT = Path('/tmp/oec/pequalnp-pilot-87')
source_path = ROOT / 'library_route/copy_search_first_allrect.cpp'
baseline_path = ROOT / 'library_route/copy_search_first_trim.cpp'
data_path = ROOT / 'finite_invariants/rectangle-all-certificates.json'
source = source_path.read_text()
data = json.loads(data_path.read_text())


def initializer(pattern):
    text = re.search(pattern, source, re.S).group(1)
    return ast.literal_eval(text.replace('{', '[').replace('}', ']'))


certs = initializer(r'static const Cert certs\[\] =\s*(\{.*?\});')
positive = initializer(r'static const int rectPos\[13\]\[21\]=(\{.*?\});')
negative = initializer(r'static const int rectNeg\[13\]\[21\]=(\{.*?\});')
totals = initializer(r'static const long long rectTotals\[13\]=(\{.*?\});')
assert len(certs) == len(data) == len(positive) == len(negative) == len(totals) == 13
edges = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 0), (0, 5), (1, 6),
         (2, 7), (3, 8), (4, 9), (5, 7), (7, 9), (9, 6), (6, 8), (8, 5)]


def graph(row):
    return any((row >> a & 1) and (row >> b & 1) for a, b in edges)


for i, (nr, nc, weights) in enumerate(certs):
    expected = data[i]
    assert weights == expected['weights']
    assert nr == len(weights) == len(positive[i])
    assert nc == len(weights[0]) == len(negative[i])
    assert all(len(row) == nc for row in weights)
    assert positive[i] == expected['positive_rows']
    assert negative[i] == expected['negative_rows']
    assert all(graph(row) for row in positive[i])
    assert all(not graph(row) for row in negative[i])
    assert totals[i] == expected['total'] == sum(map(sum, weights))


@lru_cache(None)
def cost(certificate, word):
    weights = certs[certificate][2]
    rows = [i for i, r in enumerate(positive[certificate]) if word >> r & 1]
    cols = [j for j, r in enumerate(negative[certificate]) if not (word >> r & 1)]
    if not rows or not cols:
        return 0
    # Enumerate subsets by cardinality and direct summation, independently of
    # the C++ Gray-code updates and transposed-storage implementation.
    if len(rows) <= len(cols):
        small, large = rows, cols
        weight = lambda i, j: weights[i][j]
    else:
        small, large = cols, rows
        weight = lambda i, j: weights[j][i]
    best = 0
    for size in range(1, len(small) + 1):
        for subset in itertools.combinations(small, size):
            value = sum(max(0, sum(weight(i, j) for i in subset)) for j in large)
            best = max(best, value)
    return best


matches = re.findall(
    r'\{vector<Word>ws=(\{.*?\});vector<array<long long,13>>expected=(\{.*?\});vector<int>state;',
    source, re.S)
assert len(matches) == 4
comparisons = 0
bank_results = []
for words_text, expected_text in matches:
    words = []
    for limbs_text in re.findall(r'Word\{\{([^}]+)\}\}', words_text):
        limbs = [int(x.removesuffix('ull')) for x in limbs_text.split(',')]
        assert len(limbs) == 16 and all(0 <= x < 2**64 for x in limbs)
        words.append(sum(value << (64 * i) for i, value in enumerate(limbs)))
    expected = ast.literal_eval(expected_text.replace('{', '[').replace('}', ']'))
    assert len(words) == len(expected)
    actual = [[cost(c, word) for c in range(13)] for word in words]
    assert actual == expected
    sums = [sum(row[c] for row in actual) for c in range(13)]
    cuts = [c for c in range(13) if sums[c] < totals[c]]
    assert cuts
    comparisons += len(words) * 13
    bank_results.append({'root_occurrences': len(words), 'distinct_roots': len(set(words)),
                         'cut_matrices': cuts, 'cost_sums': sums})

assert comparisons == 936
assert 'if(!signedmode&&deficit==0&&rectangle_cut(state))return false;' in source
report = {
    'source_sha256': hashlib.sha256(source_path.read_bytes()).hexdigest(),
    'baseline_sha256': hashlib.sha256(baseline_path.read_bytes()).hexdigest(),
    'data_sha256': hashlib.sha256(data_path.read_bytes()).hexdigest(),
    'matrices_checked': 13,
    'all_literal_weights_rows_and_totals_match': True,
    'all_positive_negative_samples_match_exact_petersen': True,
    'independent_root_cost_comparisons': comparisons,
    'unique_costs_evaluated': cost.cache_info().misses,
    'bank_results': bank_results,
    'limitation': 'Finite oracle audit only; no complete search or new Lean certificate is claimed.',
}
destination = ROOT / 'status_review/audit-allrect-oracle.json'
destination.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps(report, indent=2))
