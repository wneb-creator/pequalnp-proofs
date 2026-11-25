#!/usr/bin/env python3
"""Conservative reversible custom-identifier compression.

Only source-declared ASCII names absent from every imported constant name
component may change. Imported fields, source keywords, structural declarations,
and the posted theorem namespace are protected. The complete source is renamed
consistently, so local shadowing is alpha-renamed with its declaration.
Every result still requires Lean replay.
"""
import argparse
import collections
import itertools
import json
import re
import string
from pathlib import Path

IDENT = re.compile(r"(?<![\w'\u2032])([A-Za-z_][\w'\u2032]*)(?![\w'\u2032])")
DECL = re.compile(r"^(?:(?:private|protected|noncomputable)\s+)*(theorem|lemma|def|abbrev|structure|inductive)\s+([^\s:(]+)", re.M)
PROTECTED = {'PEqualNP', 'Outside', 'L_meta_670'}
ASCII_NAME = re.compile(r'[A-Za-z_][A-Za-z0-9_]*\Z')

def erase_comments(source):
    # Preserve positions and line breaks; no string literals are allowed in the
    # proof inputs. Reject strings rather than treating them as identifiers.
    out = list(source)
    i = 0
    depth = 0
    while i < len(source):
        if source.startswith('/-', i):
            depth += 1
            out[i:i+2] = '  '
            i += 2
        elif depth and source.startswith('-/', i):
            depth -= 1
            out[i:i+2] = '  '
            i += 2
        elif depth:
            if source[i] != '\n':
                out[i] = ' '
            i += 1
        elif source.startswith('--', i):
            stop = source.find('\n', i)
            if stop < 0:
                stop = len(source)
            out[i:stop] = ' ' * (stop-i)
            i = stop
        else:
            if source[i] in '"«»':
                raise ValueError('strings or escaped identifiers require a lexer-aware pass')
            i += 1
    if depth:
        raise ValueError('unclosed comment')
    return ''.join(out)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source', type=Path)
    parser.add_argument('output', type=Path)
    parser.add_argument('--imported-names', required=True, type=Path)
    parser.add_argument('--manifest', required=True, type=Path)
    args = parser.parse_args()
    source = args.source.read_text()
    clean = erase_comments(source)
    imported = set(IDENT.findall(args.imported_names.read_text()))
    existing = set(IDENT.findall(clean))
    import_lines = [line for line in source.splitlines() if line.startswith('import ')]
    protected = PROTECTED | set(IDENT.findall('\n'.join(import_lines)))
    structural = set()
    declared = set()
    for kind, full in DECL.findall(clean):
        name = full.split('.')[-1]
        if kind in ('structure', 'inductive'):
            structural.add(name)
        elif ASCII_NAME.fullmatch(name):
            declared.add(name)
    for full in re.findall(r'^namespace ([A-Za-z_][A-Za-z0-9_.]*)\s*$', clean, re.M):
        declared.update(full.split('.'))
    frequency = collections.Counter(IDENT.findall(clean))
    eligible = declared - imported - structural - protected
    eligible = {name for name in eligible if len(name) > 3}
    names = sorted(eligible, key=lambda n: (-frequency[n], -len(n), n))
    reserved = existing | imported | protected
    alphabet = string.ascii_letters + string.digits
    fresh = ('Z' + ''.join(suffix) for n in range(2, 5)
             for suffix in itertools.product(alphabet, repeat=n))
    mapping = {}
    for name in names:
        target = next(s for s in fresh if s not in reserved)
        if len(target) < len(name):
            mapping[name] = target
            reserved.add(target)
    # Work only on real identifier spans; comments retain their exact contents.
    spans = [(m.start(1), m.end(1), mapping[m.group(1)])
             for m in IDENT.finditer(clean) if m.group(1) in mapping]
    chunks = []
    prev = 0
    for start, end, target in spans:
        chunks.extend([source[prev:start], target])
        prev = end
    chunks.append(source[prev:])
    result = ''.join(chunks)
    assert import_lines == [line for line in result.splitlines() if line.startswith('import ')]
    target = 'theorem PEqualNP.Outside.L_meta_670'
    assert source.count(target) == result.count(target), 'posted theorem name changed'
    reverse = {new: old for old, new in mapping.items()}
    # All new names were absent from the original source, including comments.
    # Verify restoration after replacing only actual identifiers.
    cleaned_result = erase_comments(result)
    restore = []
    prev = 0
    for m in IDENT.finditer(cleaned_result):
        if m.group(1) in reverse:
            restore.extend([result[prev:m.start(1)], reverse[m.group(1)]])
            prev = m.end(1)
    restore.append(result[prev:])
    assert ''.join(restore) == source, 'rename was not exactly reversible'
    args.output.write_text(result)
    report = {
        'source': str(args.source), 'output': str(args.output),
        'before_bytes': len(source.encode()), 'after_bytes': len(result.encode()),
        'saved_bytes': len(source.encode())-len(result.encode()),
        'imported_components': len(imported),
        'renamed_identifiers': len(mapping), 'renamed_occurrences': len(spans),
        'mapping': mapping,
        'protected_import_collisions': sorted(declared & imported),
    }
    args.manifest.write_text(json.dumps(report, indent=2))
    print(json.dumps({k:v for k,v in report.items()
                      if k not in ('mapping','protected_import_collisions')}, indent=2))

if __name__ == '__main__':
    main()
