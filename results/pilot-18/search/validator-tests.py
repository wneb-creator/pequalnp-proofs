"""Standard-library tests; all fixtures and outputs stay in reviewer scratch."""
import hashlib
import importlib.util
import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.dont_write_bytecode = True
ROOT = Path('/tmp/oec/pequalnp-pilot-18/lean-setup')
SCRIPT = ROOT / 'validate_sat_candidate.py'
TEST_ROOT = ROOT / 'validator-tests'
TEST_ROOT.mkdir(exist_ok=True)
spec = importlib.util.spec_from_file_location('candidate_validator', SCRIPT)
v = importlib.util.module_from_spec(spec)
spec.loader.exec_module(v)
BASE = json.loads((TEST_ROOT / 'real/fixed-cover22.validated.original.json').read_text())


def save_json(path, value):
    path.write_text(json.dumps(value) + '\n')


def write_model(path, assignment, *, literals=None, status='SATISFIABLE', terminated=True):
    if literals is None:
        literals = [i if assignment[i] else -i for i in sorted(assignment)]
    lines = ['c Synthetic full signed witness']
    if status is not None:
        lines.append('s ' + status)
    words = list(map(str, literals)) + (['0'] if terminated else [])
    lines.extend('v ' + ' '.join(words[i:i + 23]) for i in range(0, len(words), 23))
    path.write_text('\n'.join(lines) + '\n')


def fixture(directory, gates=None, output=None, **options):
    if gates is None:
        gates = BASE['gates']
    if output is None:
        output = BASE['output']
    assignment = {}

    def var(value):
        i = len(assignment) + 1
        assignment[i] = bool(value)
        return i

    ops, lefts, rights = [], [], []
    for g, (op, a, b) in enumerate(gates):
        ops.append(var(op == 'and'))
        lefts.append([var(i == a) for i in range(13 + g)])
        rights.append([var(i == b) for i in range(13 + g)])
    selectors = [var(i == output) for i in range(13 + len(gates))]
    meta = dict(size=len(gates), first_junk=-1, second_junk=False,
                variables=len(assignment), clauses=len(assignment),
                ops=ops, lefts=lefts, rights=rights, output_selectors=selectors,
                last_output=False, live=False, prefix_sort=False, prefix_lex=False,
                productive_prefix=False)
    meta.update(options)
    path = directory / 'case.cnf'
    lines = [f"p cnf {meta['variables']} {meta['clauses']}"]
    lines.extend(f'{i if value else -i} 0' for i, value in assignment.items())
    path.write_text('\n'.join(lines) + '\n')
    meta['sha256'] = hashlib.sha256(path.read_bytes()).hexdigest()
    save_json(path.with_suffix('.json'), meta)
    model = directory / 'model.stdout'
    write_model(model, assignment)
    return path, model, meta, assignment


def update_meta(cnf, **options):
    path = cnf.with_suffix('.json')
    meta = json.loads(path.read_text())
    meta.update(options)
    save_json(path, meta)
    return meta


def rewrite_cnf(cnf, text, **options):
    cnf.write_text(text)
    return update_meta(cnf, sha256=hashlib.sha256(cnf.read_bytes()).hexdigest(), **options)


def prepend(extra):
    shift = len(extra)
    gates = [list(g) for g in extra]
    gates.extend([op, a if a < 13 else a + shift, b if b < 13 else b + shift]
                 for op, a, b in BASE['gates'])
    return gates, BASE['output'] + shift


def lex_sorted_baseline():
    gates, mapping, pending = [], {i: i for i in range(13)}, set(range(17))
    while pending:
        choices = []
        for i in pending:
            op, a, b = BASE['gates'][i]
            if a in mapping and b in mapping:
                left, right = sorted((mapping[a], mapping[b]))
                choices.append(((right, left, 0 if op == 'and' else 1), i))
        _, i = min(choices)
        op, a, b = BASE['gates'][i]
        gates.append([op, *sorted((mapping[a], mapping[b]))])
        mapping[13 + i] = 12 + len(gates)
        pending.remove(i)
    for i in range(17, len(BASE['gates'])):
        op, a, b = BASE['gates'][i]
        gates.append([op, mapping[a], mapping[b]])
        mapping[13 + i] = 12 + len(gates)
    return gates, mapping[BASE['output']]


class ValidatorTests(unittest.TestCase):
    def setUp(self):
        self.directory = Path(tempfile.mkdtemp(prefix=self._testMethodName + '-', dir=TEST_ROOT))

    def reject(self, cnf, model, pattern):
        with self.assertRaisesRegex(v.ValidationError, pattern):
            v.audit(cnf, model)

    def test_verified_v2_real_model_and_artifacts(self):
        cnf = TEST_ROOT / 'real/fixed-cover22.cnf'
        model = TEST_ROOT / 'real/fixed-cover22-v2.stdout'
        report = v.validate(cnf, model)
        self.assertEqual(report['assigned_variables'], 4800)
        self.assertEqual(report['clauses_checked'], 99415)
        self.assertEqual(report['normalized_gate_count'], 22)
        self.assertFalse(report['meets_posted_gate_limit'])
        original = json.loads(Path(report['artifacts']['original_candidate']).read_text())
        normalized = json.loads(Path(report['artifacts']['normalized_candidate']).read_text())
        self.assertEqual(original['output'], 34)
        self.assertEqual(normalized['output'], 32)
        self.assertEqual(normalized['gate_wire_offset'], 11)
        self.assertNotIn('virtual_false', normalized)

    def test_full_negative_literals_and_consistent_duplicates(self):
        cnf, model, _, a = fixture(self.directory)
        literals = [i if value else -i for i, value in a.items()]
        self.assertTrue(any(x < 0 for x in literals))
        write_model(model, a, literals=literals + [literals[0]])
        _, _, report = v.audit(cnf, model)
        self.assertEqual(report['consistent_duplicate_model_literals'], 1)

    def test_reject_conflicting_model(self):
        cnf, model, _, a = fixture(self.directory)
        literals = [i if value else -i for i, value in a.items()]
        write_model(model, a, literals=literals + [-literals[0]])
        self.reject(cnf, model, 'conflicting signs')

    def test_reject_missing_out_of_range_and_unterminated_models(self):
        cnf, model, _, a = fixture(self.directory)
        literals = [i if value else -i for i, value in a.items()]
        for changed, message in ((literals[:-1], 'incomplete model'),
                                 (literals + [len(a) + 1], 'outside the DIMACS range')):
            with self.subTest(message=message):
                write_model(model, a, literals=changed)
                self.reject(cnf, model, message)
        write_model(model, a, terminated=False)
        self.reject(cnf, model, 'zero-terminated')
        write_model(model, a)
        with model.open('a') as stream:
            stream.write('v 1 0\n')
        self.reject(cnf, model, 'after the final zero')

    def test_reject_bad_missing_and_duplicate_status(self):
        cnf, model, _, a = fixture(self.directory)
        for status in (None, 'UNSATISFIABLE', 'UNKNOWN'):
            with self.subTest(status=status):
                write_model(model, a, status=status)
                self.reject(cnf, model, 'SATISFIABLE')
        write_model(model, a)
        with model.open('a') as stream:
            stream.write('s SATISFIABLE\n')
        self.reject(cnf, model, 'multiple solver status')

    def test_reject_cnf_hash_and_metadata_shape(self):
        cnf, model, _, _ = fixture(self.directory)
        update_meta(cnf, sha256='0' * 64)
        self.reject(cnf, model, 'SHA-256')
        update_meta(cnf, sha256=hashlib.sha256(cnf.read_bytes()).hexdigest(), variables=True)
        self.reject(cnf, model, 'nonnegative integer')

    def test_check_last_clause_and_signed_tautology(self):
        cnf, model, meta, a = fixture(self.directory)
        literal = 1 if a[1] else -1
        lines = cnf.read_text().splitlines()
        lines[0] = f"p cnf {meta['variables']} {meta['clauses'] + 1}"
        rewrite_cnf(cnf, '\n'.join(lines + [f'{literal} {-literal} 0']) + '\n', clauses=meta['clauses'] + 1)
        v.audit(cnf, model)
        rewrite_cnf(cnf, '\n'.join(lines + [f'{-literal} 0']) + '\n')
        self.reject(cnf, model, f"clause {meta['clauses'] + 1} is not satisfied")

    def test_dimacs_comments_multiline_and_multiple_clauses(self):
        cnf, model, _, _ = fixture(self.directory)
        lines = cnf.read_text().splitlines()
        third = lines[3].split()
        rewritten = ['c leading comment', lines[0], lines[1] + ' ' + lines[2],
                     third[0], 'c inside a multiline clause', '0', *lines[4:]]
        rewrite_cnf(cnf, '\n'.join(rewritten) + '\n')
        v.audit(cnf, model)

    def test_reject_header_mismatch_and_unterminated_clause(self):
        cnf, model, meta, _ = fixture(self.directory)
        original = cnf.read_text()
        rewrite_cnf(cnf, original.replace(f"p cnf {meta['variables']}", f"p cnf {meta['variables'] + 1}", 1))
        self.reject(cnf, model, 'header disagrees')
        rewrite_cnf(cnf, original.rsplit(' 0', 1)[0] + '\n')
        self.reject(cnf, model, 'unterminated final CNF')

    def test_reject_invalid_and_empty_clause(self):
        cnf, model, meta, _ = fixture(self.directory)
        lines = cnf.read_text().splitlines()
        lines[1] = f"{meta['variables'] + 1} 0"
        rewrite_cnf(cnf, '\n'.join(lines) + '\n')
        self.reject(cnf, model, 'CNF literal.*outside')
        lines[1] = '0'
        rewrite_cnf(cnf, '\n'.join(lines) + '\n')
        self.reject(cnf, model, 'clause 1 is not satisfied')

    def test_reject_selector_domain_and_ambiguity(self):
        cnf, model, meta, a = fixture(self.directory)
        lefts = [x[:] for x in meta['lefts']]
        lefts[0].pop()
        update_meta(cnf, lefts=lefts)
        self.reject(cnf, model, 'source-domain size')
        lefts = [x[:] for x in meta['lefts']]
        selected = next(x for x in lefts[0] if a[x])
        lefts[0][0] = selected
        update_meta(cnf, lefts=lefts)
        self.reject(cnf, model, 'repeats a selector')
        lefts = [x[:] for x in meta['lefts']]
        other_true = next(x for x, value in a.items() if value and x not in lefts[0])
        lefts[0][0] = other_true
        update_meta(cnf, lefts=lefts)
        self.reject(cnf, model, 'exactly one wire')

    def test_junk_default_true_and_tail7_override(self):
        cnf, model, _, _ = fixture(self.directory, first_junk=17, second_junk=True)
        self.reject(cnf, model, 'first junk AND')
        update_meta(cnf, enforce_junk=False)
        original, _, report = v.audit(cnf, model)
        self.assertEqual(original['junk'], [])
        self.assertFalse(report['requested_constraints']['enforce_junk'])

    def test_second_junk_requirement(self):
        gates, output = prepend([['and', 0, 0]])
        cnf, model, _, _ = fixture(self.directory, gates, output, first_junk=0, second_junk=True)
        self.reject(cnf, model, 'second junk AND')
        update_meta(cnf, second_junk=False)
        self.assertEqual(v.audit(cnf, model)[0]['junk'], [0])

    def test_last_output_live_and_last_operation(self):
        cnf, model, _, _ = fixture(self.directory, last_output=True, live=True, last_op='or')
        v.audit(cnf, model)
        update_meta(cnf, last_op='and')
        self.reject(cnf, model, 'last operation')
        update_meta(cnf, live=False, last_output=False, last_op='or')
        self.reject(cnf, model, 'last_op requires')
        gates, output = prepend([['or', 0, 0]])
        cnf, model, _, _ = fixture(self.directory, gates, output, live=True)
        self.reject(cnf, model, 'does not reach its output')
        cnf, model, _, _ = fixture(self.directory, BASE['gates'] + [['or', 0, 0]],
                                    BASE['output'], last_output=True)
        self.reject(cnf, model, 'not the final gate')

    def test_sorted_lex_live_productive_positive(self):
        gates, output = lex_sorted_baseline()
        cnf, model, _, _ = fixture(self.directory, gates, output, first_junk=17,
                                    enforce_junk=False, prefix_sort=True, prefix_lex=True,
                                    productive_prefix=True, live=True, last_output=True)
        v.audit(cnf, model)

    def test_reject_prefix_sort(self):
        cnf, model, _, _ = fixture(self.directory, first_junk=17, enforce_junk=False, prefix_sort=True)
        self.reject(cnf, model, 'maximum sources are not sorted')

    def test_reject_lex_left_and_operation_order(self):
        examples = [[['or', 1, 2], ['or', 0, 2]], [['or', 0, 9], ['and', 0, 9]]]
        for extra in examples:
            with self.subTest(extra=extra):
                gates, output = prepend(extra)
                cnf, model, _, _ = fixture(self.directory, gates, output, first_junk=2,
                                            enforce_junk=False, prefix_sort=True, prefix_lex=True)
                self.reject(cnf, model, 'lexicographically')

    def test_reject_unproductive_and_duplicate_prefix(self):
        gates, output = prepend([['and', 0, 11]])
        cnf, model, _, _ = fixture(self.directory, gates, output, first_junk=1,
                                    enforce_junk=False, productive_prefix=True)
        self.reject(cnf, model, 'empty singleton support')
        gates, output = prepend([['or', 0, 0], ['or', 0, 0]])
        cnf, model, _, _ = fixture(self.directory, gates, output, first_junk=2,
                                    enforce_junk=False, prefix_distinct=True)
        self.reject(cnf, model, 'repeats a gate description')

    def test_suffix_shape(self):
        cnf, model, _, _ = fixture(self.directory, first_junk=17, enforce_junk=False, suffix_shape='OOOOO')
        v.audit(cnf, model)
        update_meta(cnf, suffix_shape='AOOOO')
        self.reject(cnf, model, 'suffix operation shape')

    def test_prefix_clean_even_when_junk_enforcement_disabled(self):
        gates, output = prepend([['and', 0, 0]])
        cnf, model, _, _ = fixture(self.directory, gates, output, first_junk=1,
                                    enforce_junk=False)
        self.reject(cnf, model, 'prefix AND is true on a negative')
        update_meta(cnf, first_junk=0)
        report = v.audit(cnf, model)[2]
        self.assertEqual(report['requested_constraints']['prefix_clean_and_gates_checked'], 0)
        gates, output = prepend([['and', 0, 9]])
        cnf, model, _, _ = fixture(self.directory, gates, output, first_junk=1,
                                    enforce_junk=False)
        checks = v.audit(cnf, model)[2]['requested_constraints']
        self.assertEqual(checks['prefix_clean_check'], 'passed')
        self.assertEqual(checks['prefix_clean_and_gates_checked'], 1)

    def test_prefix_dominance_positive_and_skip_unclean_earlier_wires(self):
        examples = [([['and', 0, 9], ['and', 1, 4]], 1),
                    ([['or', 0, 0], ['and', 0, 9]], 0),
                    ([['or', 12, 12], ['and', 0, 9]], 0)]
        for extra, pairs in examples:
            with self.subTest(extra=extra):
                gates, output = prepend(extra)
                cnf, model, _, _ = fixture(self.directory, gates, output, first_junk=len(extra),
                                            enforce_junk=False, prefix_dominance=True)
                checks = v.audit(cnf, model)[2]['requested_constraints']
                self.assertEqual(checks['prefix_dominance_pairs_checked'], pairs)

    def test_prefix_dominance_reject_and_or_and_minimal_edge_failures(self):
        examples = [([['and', 0, 9], ['and', 0, 9]], 1, 13),
                    ([['and', 0, 9], ['and', 0, 10], ['or', 13, 14],
                      ['or', 9, 10], ['and', 0, 16]], 4, 15),
                    ([['or', 11, 11], ['and', 0, 9], ['and', 1, 14]], 2, 13)]
        for extra, g, b in examples:
            with self.subTest(extra=extra):
                gates, output = prepend(extra)
                cnf, model, _, _ = fixture(self.directory, gates, output, first_junk=len(extra),
                                            enforce_junk=False, prefix_dominance=True)
                self.reject(cnf, model, f'AND {g} lacks a minimal-edge witness.*wire {b}')

    def test_prefix_copy_chain_positive_including_gate_zero(self):
        examples = [([['or', 0, 9], ['or', 13, 13], ['or', 14, 14]], 2),
                    ([['or', 12, 12], ['or', 13, 13]], 2),
                    ([['or', 0, 9], ['and', 1, 4]], 0)]
        for extra, copies in examples:
            with self.subTest(extra=extra):
                gates, output = prepend(extra)
                cnf, model, _, _ = fixture(self.directory, gates, output, first_junk=len(extra),
                                            enforce_junk=False, prefix_copy_chain=True)
                checks = v.audit(cnf, model)[2]['requested_constraints']
                self.assertEqual(checks['prefix_copy_chain_gates_checked'], copies)

    def test_prefix_copy_chain_reject_wrong_source_or_interruption(self):
        examples = [([['or', 0, 9], ['or', 0, 0]], 'does not copy the previous'),
                    ([['or', 0, 0], ['or', 0, 9]], 'interrupted'),
                    ([['or', 0, 0], ['and', 0, 9]], 'interrupted'),
                    ([['or', 0, 0], ['or', 13, 13], ['or', 13, 13]], 'does not copy the previous')]
        for extra, message in examples:
            with self.subTest(extra=extra):
                gates, output = prepend(extra)
                cnf, model, _, _ = fixture(self.directory, gates, output, first_junk=len(extra),
                                            enforce_junk=False, prefix_copy_chain=True)
                self.reject(cnf, model, message)

    def test_new_prefix_flags_need_boundary_and_boolean_values(self):
        for name in ('prefix_dominance', 'prefix_copy_chain'):
            with self.subTest(flag=name):
                cnf, model, _, _ = fixture(self.directory, **{name: True})
                self.reject(cnf, model, 'nonnegative first_junk boundary')
                update_meta(cnf, **{name: 1})
                self.reject(cnf, model, f'{name} must be Boolean')

    def test_all_constant_normalization_and_target_rejection(self):
        for op in ('and', 'or'):
            for a in (False, True):
                for b in (False, True):
                    with self.subTest(op=op, a=a, b=b):
                        gates = [[op, 12 if a else 11, 12 if b else 11]]
                        result = v.normalize_circuit(gates, 13)
                        self.assertEqual(result['constant_output'], (a and b) if op == 'and' else (a or b))
                        self.assertEqual(result['gates'], [])
                        cnf, model, _, _ = fixture(self.directory, gates, 13)
                        self.reject(cnf, model, 'original circuit disagrees')

    def test_identity_alias_chain_and_boolean_integer_separation(self):
        cases = [([['and', 0, 12]], 13), ([['or', 0, 11]], 13),
                 ([['and', 0, 0]], 13), ([['or', 0, 0]], 13),
                 ([['and', 0, 12], ['or', 11, 13], ['and', 14, 14]], 15)]
        for gates, output in cases:
            with self.subTest(gates=gates):
                result = v.normalize_circuit(gates, output)
                self.assertEqual(result['output'], 0)
                self.assertNotIn('constant_output', result)
                self.assertEqual(result['gates'], [])

    def test_absorption_and_dead_subgraph(self):
        gates = [['and', 0, 1], ['or', 12, 13], ['and', 2, 14]]
        result = v.normalize_circuit(gates, 15)
        self.assertEqual(result['output'], 2)
        self.assertEqual(result['gates'], [])
        self.assertEqual(result['normalization']['dead_gates_pruned'], 1)

    def test_constant_alias_gadgets_around_exact_target(self):
        gates, mapping = [], {11: 11, 12: 12}
        for i in range(11):
            gates.append(['and', i, 12])
            mapping[i] = 12 + len(gates)
        gates.extend([['and', 12, 12], ['or', 11, 11], ['and', 11, 12], ['or', 11, 12]])
        for i, (op, a, b) in enumerate(BASE['gates']):
            gates.append([op, mapping[a], mapping[b]])
            mapping[13 + i] = 12 + len(gates)
        output = mapping[BASE['output']]
        for op, other in (('or', 11), ('and', 12)):
            gates.append([op, output, other])
            output = 12 + len(gates)
        gates.append(['or', output, output])
        output = 12 + len(gates)
        gates.append(['and', 0, 1])
        cnf, model, _, _ = fixture(self.directory, gates, output, enforce_junk=False)
        original, normalized, _ = v.audit(cnf, model)
        self.assertEqual(original['size'], 41)
        self.assertEqual(normalized['size'], 22)
        self.assertEqual(normalized['output'], 32)
        self.assertEqual(normalized['normalization']['constant_folded_gates'], 4)
        self.assertEqual(normalized['normalization']['identity_or_alias_gates'], 14)
        self.assertEqual(normalized['normalization']['dead_gates_pruned'], 1)
        for i, (_, a, b) in enumerate(normalized['gates']):
            self.assertLess(a, 11 + i)
            self.assertLess(b, 11 + i)

    def test_cli_failure_saves_no_candidate_even_under_optimized_python(self):
        cnf, model, _, _ = fixture(self.directory)
        update_meta(cnf, sha256='0' * 64)
        result = subprocess.run([sys.executable, '-O', str(SCRIPT), str(cnf), str(model)],
                                cwd=ROOT, capture_output=True, text=True, timeout=10)
        self.assertEqual(result.returncode, 1)
        self.assertIn('SHA-256', result.stderr)
        self.assertEqual(result.stdout, '')
        self.assertFalse(cnf.with_suffix('.validated.original.json').exists())
        self.assertFalse(cnf.with_suffix('.validated.normalized.json').exists())


if __name__ == '__main__':
    unittest.main(verbosity=2)
