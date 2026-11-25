"""Run the bounded 3-by-3 census, preserving complete solver and driver diagnostics."""
import argparse
import json
import shutil
from pathlib import Path
from types import SimpleNamespace
import serve_sat

parser = argparse.ArgumentParser()
parser.add_argument('--output-dir', required=True)
parser.add_argument('--control-dir', required=True)
parser.add_argument('--seconds', type=int, default=10)
args = parser.parse_args()
root = Path(__file__).resolve().parent
output = Path(args.output_dir)
output.mkdir(parents=True, exist_ok=True)
controls = Path(args.control_dir)
manifest = json.loads((root / 'case_manifest.json').read_text())
results = []
for case in manifest['classes']:
    base = output / f"case_{case['mask']}"
    cached = controls / 'cycle6_7.result.json'
    reuse = None
    if cached.exists():
        candidate = json.loads(cached.read_text())
        if (candidate['p'], candidate['l'], candidate['edges'], candidate['gates']) == (
                case['p'], case['l'], case['edges'], case['counterexample_gates']):
            reuse = candidate
    if reuse is not None:
        result = reuse
        result['reused_from'] = str(cached)
        base.with_suffix('.result.json').write_text(json.dumps(result, indent=2) + '\n')
        for suffix in ['.solver.stdout', '.solver.stderr']:
            shutil.copyfile(controls / ('cycle6_7' + suffix), base.with_suffix(suffix))
    else:
        result = serve_sat.main(SimpleNamespace(graph=str(root / 'cases' / f"graph_{case['mask']}.json"),
            gates=case['counterexample_gates'], seconds=args.seconds, output=str(base),
            output_before_last=False, generate_only=False))
    summary = {'mask': case['mask'], 'gates': case['counterexample_gates'],
               'status': result['status'], 'seconds': result['seconds'], 'reused': reuse is not None,
               'counterexample': result.get('counterexample', False)}
    print(json.dumps(summary), flush=True)
    results.append(summary)
    if summary['counterexample']:
        break
report = {'results': results, 'classes_completed': len(results), 'classes_total': len(manifest['classes']),
          'labeled_cases_in_scope': manifest['labeled_count'],
          'claim': 'Finite SAT experiments only; not a Lean certificate and not a proof for general graphs.'}
(output / 'SUMMARY.json').write_text(json.dumps(report, indent=2) + '\n')
