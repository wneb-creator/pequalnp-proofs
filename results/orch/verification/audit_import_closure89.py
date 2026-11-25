from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json
import re

BASE = Path('/workspace/pequalnp-proofs/results/orch')
LEMMA = BASE / 'lemmas'
EXCLUDED = 'Live1024Terminal0Closure'
LATER = {'RectangleBank13338', 'RectangleBank13338Cut'}
LEGACY_REVIEWS = {
    'Bridge': 'review-bridge.txt',
    'FiniteInvariants': 'review-finite-search.txt',
    'Live1024Tight': 'review-live1024-tight.txt',
    'NoOrIdentification': 'review-no-or-identification.txt',
    'NoOrRows': 'review-no-or-rows.txt',
}


def digest(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


old = json.loads((LEMMA / 'REBUILD-MANIFEST.json').read_text())
reports = {p.name: p for p in BASE.glob('review-*.txt')}
texts = {n: p.read_text() for n, p in reports.items()}
paths = {p.stem: p for p in LEMMA.glob('*.lean') if p.stem not in LATER}
assert len(paths) == 89, ('census changed', len(paths))
selected = set(paths) - {EXCLUDED}
entries = {}
missing = []
for name, path in sorted(paths.items()):
    source = path.read_text()
    sha = digest(path)
    imports = [x for line in source.splitlines() if line.startswith('import ')
               for x in line.split()[1:]]
    local = [x for x in imports if not x.startswith(('PEqualNP', 'Mathlib'))]
    missing.extend((name, x) for x in local if x not in selected)
    log = path.with_suffix('.compile.txt')
    assert log.exists(), name
    log_text = log.read_text()
    error_lines = [line for line in log_text.splitlines()
                   if re.search(r'(^|\s)error(?:\([^)]*\))?:', line)]
    assert not error_lines, (name, error_lines)
    exact_reviews = sorted(n for n, t in texts.items() if sha in t)
    legacy = LEGACY_REVIEWS.get(name)
    if legacy:
        assert legacy in texts and 'PASS' in texts[legacy], name
        assert old['modules'][name]['sha256'] == sha, name
    if name != EXCLUDED:
        assert exact_reviews or legacy, ('no independent review', name)
    for review in exact_reviews:
        assert 'PASS' in texts[review] or 'pass' in texts[review], review
    status = 'reviewed_component_with_preserved_compilation_log'
    if name == EXCLUDED:
        status = 'excluded_obsolete_prototype'
    entries[name] = {
        'source': 'lemmas/' + path.name,
        'bytes': path.stat().st_size,
        'sha256': sha,
        'imports': imports,
        'local_dependencies': local,
        'selected_for_current_closure': name in selected,
        'status': status,
        'compile_log': {
            'path': 'lemmas/' + log.name,
            'bytes': log.stat().st_size,
            'sha256': digest(log),
            'error_lines': error_lines,
            'warning_count': len(re.findall(r'(?m)^.*: warning:', log_text)),
        },
        'independent_review_exact_hash': [
            {'path': n, 'sha256': digest(reports[n])} for n in exact_reviews
        ],
        'legacy_review_pinned_by_previous_manifest': None if not legacy else {
            'path': legacy,
            'sha256': digest(reports[legacy]),
            'unchanged_previous_manifest_source_sha256': old['modules'][name]['sha256'],
        },
    }

assert not missing, missing
order = []
visiting = set()
done = set()


def visit(name):
    if name in done:
        return
    assert name not in visiting, ('dependency cycle', name)
    visiting.add(name)
    for dep in entries[name]['local_dependencies']:
        visit(dep)
    visiting.remove(name)
    done.add(name)
    order.append(name)


for name in sorted(selected):
    visit(name)
old_changed = [n for n, x in old['modules'].items()
               if entries[n]['sha256'] != x['sha256']]
assert not old_changed, old_changed
report = {
    'audited_utc': datetime.now(timezone.utc).isoformat(),
    'scope': 'Frozen 89-source census, including one explicitly excluded obsolete source.',
    'rebuilds_performed': False,
    'source_count': len(entries),
    'selected_component_count': len(selected),
    'historical_snapshot_unchanged': True,
    'historical_manifest_sha256': digest(LEMMA / 'REBUILD-MANIFEST.json'),
    'historical_rebuild_instructions_sha256': digest(LEMMA / 'REBUILD.md'),
    'missing_local_imports': missing,
    'local_dependency_topological_order': order,
    'modules': entries,
    'historical_target_exception': old['historical_context'],
    'explicit_exclusions': {
        EXCLUDED: 'Obsolete, intentionally unpushed, global resource options; use Live1024Terminal0.',
    },
    'later_additions_outside_this_census': sorted(LATER),
    'limitations': [
        'No Lean build was rerun for this import-closure audit.',
        'Compilation logs and immutable independent reviews are evidence of the original checks; no-error logs alone do not encode process exit status.',
        'NamesCompressed compiler exit0 was confirmed by its build owner for session54243; its immutable source/full log match the archived build and a newer .olean exists.',
        'The exact posted L-meta-2373 theorem remains unproved. Conditional lemmas, draft-named infrastructure, finite substate exclusions, and formula cases remain components only.',
        'Scratch work and files introduced after this fixed census are not certified or promised by this manifest.',
        'GapBridge needs its historical PetersenSeventeenFull target context, as documented in the unchanged REBUILD.md.',
    ],
}
destination = BASE / 'review-import-closure-89.json'
destination.write_text(json.dumps(report, indent=2) + '\n')
print(json.dumps({
    'source_count': len(entries),
    'selected_component_count': len(selected),
    'missing_import_count': len(missing),
    'cycle_count': 0,
    'manifest': str(destination),
    'manifest_sha256': digest(destination),
}, indent=2))
