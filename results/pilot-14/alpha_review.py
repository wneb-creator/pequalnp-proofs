from pathlib import Path
import hashlib
import json
import re

root = Path('/tmp/oec/pequalnp-pilot-14')
record = json.loads((root / 'assembly-alpha/renaming.json').read_text())
source = (root / 'assembly-slim-certified/Candidate.lean').read_text()
own = 'PEqualNP.Outside.L_meta_670_aux'

def uncomment(text):
    out = []
    i = 0
    depth = 0
    while i < len(text):
        if text[i:i+2] == '/-':
            depth += 1
            out.extend('  ')
            i += 2
        elif depth and text[i:i+2] == '-/':
            depth -= 1
            out.extend('  ')
            i += 2
        elif not depth and text[i:i+2] == '--':
            while i < len(text) and text[i] != '\n':
                out.append(' ')
                i += 1
        else:
            c = text[i]
            out.append(c if not depth or c == '\n' else ' ')
            i += 1
    assert depth == 0
    return ''.join(out)

identifier = re.compile(r"(?<![\w'])[A-Za-z_][A-Za-z0-9_']*(?![\w'])")
tokens = re.compile(r"[A-Za-z_][A-Za-z0-9_']*|[0-9]+|[^\s]")

def rows(text):
    frames = []
    current = ''
    result = []
    for no, line in enumerate(uncomment(text).splitlines(), 1):
        words = line.strip().split()
        if not words:
            continue
        if words[0] == 'namespace':
            assert len(words) == 2
            old = current
            name = words[1]
            current = name if name.startswith('PEqualNP.') else '.'.join(x for x in [current,name] if x)
            frames.append(('namespace', old, current))
            continue
        if words[0] in ('section', 'mutual'):
            frames.append((words[0], current, words[1] if len(words) > 1 else ''))
            result.append((current, tuple(tokens.findall(line))))
            continue
        if words[0] == 'end':
            assert frames, (no, line)
            kind, old, full = frames.pop()
            if kind == 'namespace':
                if len(words) > 1:
                    assert full == words[1] or full.endswith('.' + words[1]), (no,line,full)
                current = old
            else:
                result.append((current, tuple(tokens.findall(line))))
            continue
        result.append((current, tuple(tokens.findall(line))))
    assert not frames
    return result

source_rows = rows(source)
source_tokens = set(identifier.findall(uncomment(source)))
assert hashlib.sha256(source.encode()).hexdigest() == record['source_sha256']
findings = {'source_bytes': len(source.encode()), 'source_sha256': record['source_sha256'], 'variants': {}}

for variant, mapping in [
    ('Namespaces', record['namespaces']),
    ('Candidate', record['namespaces'] | record['helpers'])
]:
    assert len(mapping) == len(set(mapping.values()))
    assert not set(mapping.values()) & source_tokens
    inverse = {new: old for old,new in mapping.items()}
    candidate = (root / 'assembly-alpha' / (variant + '.lean')).read_text()
    restored = identifier.sub(lambda match: inverse.get(match[0],match[0]), candidate)
    candidate_rows = rows(restored)
    if source_rows != candidate_rows:
        mismatches = [(i,a,b) for i,(a,b) in enumerate(zip(source_rows,candidate_rows)) if a != b]
        raise AssertionError((variant,len(source_rows),len(candidate_rows),mismatches[:2]))
    digest = hashlib.sha256(candidate.encode()).hexdigest()
    assert digest == record['variants'][variant]['sha256']
    findings['variants'][variant] = {
        'bytes': len(candidate.encode()),
        'sha256': digest,
        'renamed_identifiers': len(mapping),
        'token_and_namespace_rows_equal': True,
        'semantic_rows': len(candidate_rows),
        'saved_bytes': len(source.encode()) - len(candidate.encode())
    }

helpers = set(record['helpers'])
own_namespaces = set(record['namespaces'])
foreign = set()
for match in re.finditer(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)+', uncomment(source)):
    parts = match[0].split('.')
    for index, part in enumerate(parts):
        if part in helpers and index > 0 and not any(p in own_namespaces for p in parts[:index]):
            foreign.add(match[0])
findings['qualified_external_renamed_helpers'] = sorted(foreign)
assert not foreign
findings['verdict'] = 'PASS: exact source-token alpha map and namespace scope preservation; compile pending'
(root / 'toolchain/alpha-independent-audit.json').write_text(json.dumps(findings,indent=2) + '\n')
print(json.dumps(findings,indent=2))
