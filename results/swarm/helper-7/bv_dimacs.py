"""Scratch QF_BV -> bit-blast -> tseitin-cnf export and checked SAT readback.

No simplify/solve-eqs/model-elimination tactic is used. Tseitin CNF is existentially
equisatisfiable with the source. The exact Z3 goal model converter recovers all
original assertions/Boolean selectors; every SAT readback then checks the full
AO2 truth table. An UNSAT report inherits the source's restricted-family scope
and is external solver evidence, without a Lean or checked proof certificate.
"""
import argparse
import ctypes as C
import ctypes.util
import hashlib
import json
from pathlib import Path

import free_or_and_query as query


def digest(data):
    return hashlib.sha256(data.encode()).hexdigest()


class BitBlast:
    """Keep the source, goal model converter, and CNF atom ASTs in one context."""
    def __init__(self, source, selector_names):
        path = ctypes.util.find_library('z3')
        if path is None:
            raise RuntimeError('local libz3 is unavailable')
        self.lib = C.CDLL(path)
        P, U, I, B, S = C.c_void_p, C.c_uint, C.c_int, C.c_bool, C.c_char_p
        self.functions = {}
        signatures = {
            'mk_config': (P, []), 'del_config': (None, [P]),
            'mk_context': (P, [P]), 'del_context': (None, [P]),
            'get_full_version': (S, []),
            'parse_smtlib2_string': (P, [P, S, U, C.POINTER(P), C.POINTER(P), U, C.POINTER(P), C.POINTER(P)]),
            'ast_vector_inc_ref': (None, [P, P]), 'ast_vector_dec_ref': (None, [P, P]),
            'ast_vector_size': (U, [P, P]), 'ast_vector_get': (P, [P, P, U]),
            'mk_goal': (P, [P, B, B, B]), 'goal_inc_ref': (None, [P, P]),
            'goal_dec_ref': (None, [P, P]), 'goal_assert': (None, [P, P, P]),
            'goal_size': (U, [P, P]), 'goal_formula': (P, [P, P, U]),
            'mk_tactic': (P, [P, S]), 'tactic_inc_ref': (None, [P, P]),
            'tactic_dec_ref': (None, [P, P]), 'tactic_and_then': (P, [P, P, P]),
            'tactic_apply': (P, [P, P, P]), 'apply_result_inc_ref': (None, [P, P]),
            'apply_result_dec_ref': (None, [P, P]), 'apply_result_get_num_subgoals': (U, [P, P]),
            'apply_result_get_subgoal': (P, [P, P, U]),
            'get_ast_kind': (I, [P, P]), 'get_ast_id': (U, [P, P]),
            'to_app': (P, [P, P]), 'get_app_decl': (P, [P, P]),
            'get_app_num_args': (U, [P, P]), 'get_app_arg': (P, [P, P, U]),
            'get_decl_kind': (I, [P, P]), 'get_decl_name': (P, [P, P]),
            'get_symbol_kind': (I, [P, P]), 'get_symbol_string': (S, [P, P]),
            'get_symbol_int': (I, [P, P]), 'get_sort': (P, [P, P]),
            'get_sort_kind': (I, [P, P]), 'get_bool_value': (I, [P, P]),
            'mk_string_symbol': (P, [P, S]), 'mk_bool_sort': (P, [P]),
            'mk_const': (P, [P, P, P]), 'mk_true': (P, [P]), 'mk_false': (P, [P]),
            'mk_model': (P, [P]), 'model_inc_ref': (None, [P, P]),
            'model_dec_ref': (None, [P, P]), 'add_const_interp': (None, [P, P, P, P]),
            'goal_convert_model': (P, [P, P, P]),
            'model_eval': (B, [P, P, P, B, C.POINTER(P)]),
        }
        for name, (result, args) in signatures.items():
            function = getattr(self.lib, 'Z3_' + name)
            function.restype, function.argtypes = result, args
            self.functions[name] = function
        self.cleanup = []
        config = self.f('mk_config')
        self.context = self.f('mk_context', config)
        self.f('del_config', config)
        self.source, self.selector_names = source, list(selector_names)
        self.version = self.f('get_full_version').decode()
        c = self.context
        vector = self.f('parse_smtlib2_string', c, source.encode(), 0, None, None, 0, None, None)
        self.hold('ast_vector', vector)
        self.assertions = [self.f('ast_vector_get', c, vector, i)
                           for i in range(self.f('ast_vector_size', c, vector))]
        initial = self.f('mk_goal', c, True, False, False)
        self.hold('goal', initial)
        for assertion in self.assertions:
            self.f('goal_assert', c, initial, assertion)
        first = self.f('mk_tactic', c, b'bit-blast')
        self.hold('tactic', first)
        second = self.f('mk_tactic', c, b'tseitin-cnf')
        self.hold('tactic', second)
        composed = self.f('tactic_and_then', c, first, second)
        self.hold('tactic', composed)
        result = self.f('tactic_apply', c, composed, initial)
        self.hold('apply_result', result)
        count = self.f('apply_result_get_num_subgoals', c, result)
        if count != 1:
            raise RuntimeError(f'expected one CNF subgoal, got {count}; refusing ambiguous export')
        self.goal = self.f('apply_result_get_subgoal', c, result, 0)
        self.hold('goal', self.goal)
        self.atoms, self.atom_ids, self.names, self.clauses = [], {}, [], []
        for i in range(self.f('goal_size', c, self.goal)):
            formula = self.f('goal_formula', c, self.goal, i)
            args = self.children(formula) if self.kind(formula) == 262 else [formula]
            clause, tautology = [], False
            for arg in args:
                sign = 1
                if self.kind(arg) == 265:
                    assert len(self.children(arg)) == 1
                    sign, arg = -1, self.children(arg)[0]
                constant = self.f('get_bool_value', c, arg)
                if constant:
                    if (constant == 1) == (sign == 1):
                        tautology = True
                        break
                    continue
                if self.children(arg) or self.f('get_sort_kind', c, self.f('get_sort', c, arg)) != 1:
                    raise RuntimeError('bit-blast/tseitin output contains a non-Boolean-atom literal')
                ast_id = self.f('get_ast_id', c, arg)
                if ast_id not in self.atom_ids:
                    self.atom_ids[ast_id] = len(self.atoms) + 1
                    self.atoms.append(arg)
                    self.names.append(self.name(arg))
                clause.append(sign * self.atom_ids[ast_id])
            if not tautology:
                self.clauses.append(clause)
        self.selector_asts = {}
        self.selector_ids = {}
        sort = self.f('mk_bool_sort', c)
        for name in self.selector_names:
            symbol = self.f('mk_string_symbol', c, name.encode())
            ast = self.f('mk_const', c, symbol, sort)
            self.selector_asts[name] = ast
            self.selector_ids[name] = self.atom_ids.get(self.f('get_ast_id', c, ast))
        self.dimacs = f'p cnf {len(self.atoms)} {len(self.clauses)}\n'
        self.dimacs += ''.join(' '.join(map(str, clause)) + (' ' if clause else '') + '0\n'
                               for clause in self.clauses)

    def f(self, name, *args):
        return self.functions[name](*args)

    def hold(self, kind, value):
        if not value:
            raise RuntimeError(f'Z3 returned null {kind}')
        self.f(kind + '_inc_ref', self.context, value)
        self.cleanup.append((kind, value))

    def close(self):
        if getattr(self, 'context', None):
            for kind, value in reversed(self.cleanup):
                self.f(kind + '_dec_ref', self.context, value)
            self.f('del_context', self.context)
            self.context = None

    def __enter__(self):
        return self

    def __exit__(self, *_):
        self.close()

    def kind(self, ast):
        if self.f('get_ast_kind', self.context, ast) != 1:
            raise RuntimeError('CNF formula is not an application')
        app = self.f('to_app', self.context, ast)
        return self.f('get_decl_kind', self.context, self.f('get_app_decl', self.context, app))

    def children(self, ast):
        if self.f('get_ast_kind', self.context, ast) != 1:
            raise RuntimeError('CNF literal is not an application')
        app = self.f('to_app', self.context, ast)
        return [self.f('get_app_arg', self.context, app, i)
                for i in range(self.f('get_app_num_args', self.context, app))]

    def name(self, ast):
        c = self.context
        symbol = self.f('get_decl_name', c, self.f('get_app_decl', c, self.f('to_app', c, ast)))
        return (self.f('get_symbol_string', c, symbol).decode()
                if self.f('get_symbol_kind', c, symbol) == 1
                else str(self.f('get_symbol_int', c, symbol)))

    def readback(self, assignment):
        if set(assignment) != set(range(1, len(self.atoms) + 1)):
            raise ValueError('SAT assignment must cover exactly all DIMACS variables')
        for index, clause in enumerate(self.clauses):
            if not any(assignment[abs(literal)] == (literal > 0) for literal in clause):
                raise ValueError(f'SAT assignment falsifies CNF clause {index}')
        c = self.context
        model = self.f('mk_model', c)
        self.hold('model', model)
        for number, atom in enumerate(self.atoms, 1):
            app = self.f('to_app', c, atom)
            value = self.f('mk_true' if assignment[number] else 'mk_false', c)
            self.f('add_const_interp', c, model, self.f('get_app_decl', c, app), value)
        recovered = self.f('goal_convert_model', c, self.goal, model)
        self.hold('model', recovered)

        def evaluate(ast):
            value = C.c_void_p()
            if not self.f('model_eval', c, recovered, ast, True, C.byref(value)):
                raise RuntimeError('Z3 could not evaluate recovered original expression')
            truth = self.f('get_bool_value', c, value)
            if truth == 0:
                raise RuntimeError('recovered original Boolean expression is not Boolean-valued')
            return truth == 1

        for i, assertion in enumerate(self.assertions):
            if not evaluate(assertion):
                raise ValueError(f'converted model falsifies original SMT assertion {i}')
        return {name: evaluate(ast) for name, ast in self.selector_asts.items()}


def parse_solution(text, variables):
    statuses, assignment = [], {}
    for line in text.splitlines():
        if line.startswith('s '):
            statuses.append(line[2:].strip())
        elif line.startswith('v '):
            for token in line[2:].split():
                literal = int(token)
                if literal == 0:
                    continue
                if not 1 <= abs(literal) <= variables:
                    raise ValueError('SAT output contains an out-of-range variable')
                if abs(literal) in assignment and assignment[abs(literal)] != (literal > 0):
                    raise ValueError('SAT output contains conflicting assignments')
                assignment[abs(literal)] = literal > 0
    if len(statuses) != 1:
        raise ValueError('expected exactly one solver status line')
    if statuses[0] not in ['SATISFIABLE', 'UNSATISFIABLE', 'UNKNOWN']:
        raise ValueError('unrecognized solver status')
    if statuses[0] == 'SATISFIABLE' and set(assignment) != set(range(1, variables + 1)):
        raise ValueError('SAT output omits required DIMACS variables')
    return statuses[0], assignment


def export(source, metadata, directory):
    directory = Path(directory)
    directory.mkdir(parents=True, exist_ok=False)
    # Retain exact source even if transformation fails.
    (directory / 'query.smt2').write_text(source)
    metadata_text = json.dumps(metadata, indent=2) + '\n'
    (directory / 'query.json').write_text(metadata_text)
    with BitBlast(source, metadata['selectors']) as encoded:
        (directory / 'query.cnf').write_text(encoded.dimacs)
        report = {
            'z3_version': encoded.version, 'tactics': ['bit-blast', 'tseitin-cnf'],
            'variables': len(encoded.atoms), 'clauses': len(encoded.clauses),
            'original_assertions': len(encoded.assertions),
            'selector_variables': encoded.selector_ids,
            'atom_names': {str(i): name for i, name in enumerate(encoded.names, 1)},
            'smt_sha256': digest(source), 'cnf_sha256': digest(encoded.dimacs),
            'metadata_sha256': digest(metadata_text),
            'scope': metadata['scope'], 'private_or_cap': metadata['private_or_cap'],
            'and_cap': metadata['and_cap'],
            'proof_certificate': None,
            'model_readback': 'rebuild exact transformation; verify CNF digest; convert goal model; check all original assertions; reconstruct full truth table',
        }
    (directory / 'export.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


def decode(directory, output):
    directory, output = Path(directory), Path(output)
    source = (directory / 'query.smt2').read_text()
    metadata_text = (directory / 'query.json').read_text()
    metadata = json.loads(metadata_text)
    report = json.loads((directory / 'export.json').read_text())
    if digest(metadata_text) != report['metadata_sha256']:
        raise ValueError('query metadata changed after export')
    if digest(source) != report['smt_sha256']:
        raise ValueError('source SMT changed after export')
    if digest((directory / 'query.cnf').read_text()) != report['cnf_sha256']:
        raise ValueError('DIMACS changed after export')
    status, assignment = parse_solution(output.read_text(), report['variables'])
    result = {'status': status, 'scope': metadata['scope'], 'proof_certificate': None,
              'and_cap': metadata['and_cap'], 'private_or_cap': metadata['private_or_cap'],
              'and_kraft': bool(metadata.get('and_kraft', False)),
              'and_kraft_full': bool(metadata.get('and_kraft_full', False)),
              'smt_sha256': report['smt_sha256'], 'cnf_sha256': report['cnf_sha256'],
              'solver_output_sha256': digest(output.read_text())}
    if status == 'SATISFIABLE':
        with BitBlast(source, metadata['selectors']) as encoded:
            if encoded.version != report['z3_version'] or digest(encoded.dimacs) != report['cnf_sha256']:
                raise ValueError('recreated Z3 transformation differs from exported CNF')
            values = encoded.readback(assignment)
            result['selectors'] = values
            result['circuit'] = query.reconstruct(metadata, values)
            result['CNF_clauses_checked'] = len(encoded.clauses)
            result['SMT_assertions_checked'] = len(encoded.assertions)
    return result


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    sub = parser.add_subparsers(dest='command', required=True)
    ex = sub.add_parser('export')
    ex.add_argument('--fixture', type=Path, required=True)
    ex.add_argument('--and-cap', type=int, required=True)
    ex.add_argument('--private-or-cap', type=int)
    ex.add_argument('--and-kraft', action='store_true')
    ex.add_argument('--and-kraft-full', action='store_true')
    ex.add_argument('--timeout-ms', type=int, default=1200000)
    ex.add_argument('--outdir', type=Path, required=True)
    ex.add_argument('--source-smt', type=Path,
                    help='require exact byte equality with this existing SMT before exporting it')
    dec = sub.add_parser('decode')
    dec.add_argument('--directory', type=Path, required=True)
    dec.add_argument('--solver-output', type=Path, required=True)
    dec.add_argument('--result-out', type=Path, required=True)
    args = parser.parse_args()
    if args.command == 'export':
        fixture = json.loads(args.fixture.read_text())
        if not fixture['edges']:
            parser.error('--fixture requires a graph with at least one edge')
        source, meta = query.generate(fixture['n'], fixture['edges'], args.and_cap,
                                      args.timeout_ms, args.private_or_cap,
                                      args.and_kraft, args.and_kraft_full)
        if args.source_smt is not None:
            existing = args.source_smt.read_text()
            if existing != source:
                parser.error('--source-smt differs from the query generated with these options')
            source = existing
        report = export(source, meta, args.outdir)
        print(json.dumps({k: v for k, v in report.items() if k not in ['atom_names', 'selector_variables']}, indent=2))
    else:
        result = decode(args.directory, args.solver_output)
        args.result_out.write_text(json.dumps(result, indent=2) + '\n')
        print(json.dumps({k: v for k, v in result.items() if k not in ['selectors', 'circuit']}, indent=2))


if __name__ == '__main__':
    main()
