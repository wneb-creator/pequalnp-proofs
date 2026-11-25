"""Bounded 4-by-4 experiments; retain diagnostics and delete only hashed CNFs."""
import argparse
import hashlib
import json
import shutil
from pathlib import Path
from types import SimpleNamespace

import serve_sat


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument('--output-dir', required=True)
    parser.add_argument('--cycle8-base', required=True)
    parser.add_argument('--seconds', type=int, default=10)
    args = parser.parse_args()
    root = Path(__file__).resolve().parent
    output = Path(args.output_dir)
    output.mkdir(parents=True, exist_ok=True)
    manifest = json.loads((root / 'case_manifest_4x4.json').read_text())
    cached_base = Path(args.cycle8_base)
    cached_path = cached_base.with_suffix('.result.json')
    cached = json.loads(cached_path.read_text()) if cached_path.exists() else None
    results = []
    # Larger non-cycle graphs first; each individual solve remains bounded.
    cases = sorted(manifest['classes'], key=lambda c: (-c['counterexample_gates'], c['mask']))
    for case in cases:
        base = output / f"case_{case['mask']}"
        reuse = cached is not None and (
            cached['p'], cached['l'], cached['edges'], cached['gates']) == (
            case['p'], case['l'], case['edges'], case['counterexample_gates'])
        if reuse:
            result = dict(cached)
            result['reused_from'] = str(cached_path)
            base.with_suffix('.result.json').write_text(json.dumps(result, indent=2) + '\n')
            for suffix in ['.solver.stdout', '.solver.stderr']:
                shutil.copyfile(cached_base.with_suffix(suffix), base.with_suffix(suffix))
        else:
            result = serve_sat.main(SimpleNamespace(
                graph=str(root / 'cases4' / f"graph_{case['mask']}.json"),
                gates=case['counterexample_gates'], seconds=args.seconds, output=str(base),
                output_before_last=False, generate_only=False))
        summary = {
            'mask': case['mask'], 'gates': case['counterexample_gates'],
            'status': result['status'], 'seconds': result['seconds'], 'reused': reuse,
            'counterexample': result.get('counterexample', False)}
        cnf = base.with_suffix('.cnf')
        if cnf.exists():
            data = cnf.read_bytes()
            summary['regenerable_cnf'] = {
                'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest(),
                'disposition': 'deleted after solving; regenerate from case and frozen encoder'}
            cnf.unlink()
        results.append(summary)
        report = {
            'results': results, 'classes_completed': len(results),
            'classes_total': len(cases), 'labeled_cases_in_scope': manifest['labeled_count'],
            'claim': 'Finite SAT experiments only; UNSAT is solver evidence, not a Lean certificate.'}
        (output / 'SUMMARY.json').write_text(json.dumps(report, indent=2) + '\n')
        print(json.dumps(summary), flush=True)
        if summary['counterexample']:
            break


if __name__ == '__main__':
    main()
