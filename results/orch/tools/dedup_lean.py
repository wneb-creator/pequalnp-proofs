import argparse
import hashlib
import json
import pathlib
import re

parser = argparse.ArgumentParser()
parser.add_argument('source', type=pathlib.Path)
parser.add_argument('output', type=pathlib.Path)
parser.add_argument('--report', type=pathlib.Path, required=True)
a = parser.parse_args()
src = a.source.read_text()
# Root commands are distinguished from tactic lines by column zero.
command = re.compile(r'^(?:import\b|namespace\b|end\b|(?:noncomputable\s+)?section\b|open\b|variable\b|set_option\b|(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive)\b)', re.M)
decl = re.compile(r'^(?P<mods>(?:(?:private|protected|noncomputable)\s+)*)(?P<kind>theorem|lemma|def|abbrev|structure|inductive)\s+(?P<name>[A-Za-z_][\w\.]*)')
ident = re.compile(r'[A-Za-z_][\w\u2080-\u209f\u00b9\u00b2\u00b3\u2070-\u207f\u2032]*(?:\.[A-Za-z_][\w\u2080-\u209f\u00b9\u00b2\u00b3\u2070-\u207f\u2032]*)*')
starts = [m.start() for m in command.finditer(src)] + [len(src)]
ns = []
frames = []
opens = []
variables = []
known = {}
by_short = {}
seen = {}
output = [src[:starts[0]]]
records = []
pending_local_open = False

def strip_comments(s):
    out = []; i = 0; depth = 0
    while i < len(s):
        if s.startswith('/-', i): depth += 1; i += 2
        elif depth and s.startswith('-/', i): depth -= 1; i += 2
        elif depth: i += 1
        elif s.startswith('--', i):
            j = s.find('\n', i); i = len(s) if j < 0 else j
        else: out.append(s[i]); i += 1
    return ''.join(out)

def full_name(name):
    if name.startswith('PEqualNP.'):
        return name
    return '.'.join(ns + [name])

def find_names(token):
    if token in known: return [token]
    for k in range(len(ns), -1, -1):
        v = '.'.join(ns[:k] + [token])
        if v in known: return [v]
    for op in reversed(opens):
        v = op + '.' + token
        if v in known: return [v]
    # Dot notation may mention a theorem through its receiver rather than its namespace.
    if '.' in token:
        tail = token.rsplit('.', 1)[1]
        candidates = by_short.get(tail, [])
        for k in range(len(ns), 0, -1):
            prefix = '.'.join(ns[:k]) + '.'
            good = [v for v in candidates if v.startswith(prefix)]
            if good: return good
    return []

for start, end in zip(starts, starts[1:]):
    block = src[start:end]
    line = block.splitlines()[0]
    m = decl.match(block)
    if line.startswith('namespace '):
        name = line[len('namespace '):].strip()
        frames.append((len(ns), len(opens), len(variables)))
        ns.extend(name.split('.'))
        output.append(block); continue
    if line.startswith('section') or line.startswith('noncomputable section'):
        frames.append((len(ns), len(opens), len(variables)))
        output.append(block); continue
    if line.startswith('end'):
        if frames:
            n, o, v = frames.pop(); del ns[n:]; del opens[o:]; del variables[v:]
        output.append(block); continue
    if line.startswith('open '):
        if line.rstrip().endswith(' in'):
            pending_local_open = True
        else:
            for name in line[5:].split():
                if re.fullmatch(r'[A-Za-z_][\w.]*', name): opens.append(name)
        output.append(block); continue
    if line.startswith('variable '):
        variables.append(strip_comments(block).strip())
        output.append(block); continue
    if not m:
        output.append(block); continue
    name = m.group('name'); full = full_name(name)
    kind = m.group('kind')
    deps = set()
    body = strip_comments(block[m.end():])
    def replace_ref(match):
        tok = match.group()
        if tok == name or tok == full: return '__SELF__'
        candidates = find_names(tok)
        if not candidates: return tok
        hs = sorted(set(known[v] for v in candidates))
        deps.update(candidates)
        return '__DEP_' + '_'.join(hs) + '__'
    normalized = ident.sub(replace_ref, body)
    normalized = re.sub(r'\s+', ' ', normalized).strip()
    context = ident.sub(replace_ref, '\n'.join(variables))
    # A definition and a theorem can have identical text yet different reducibility;
    # preserve the declaration class. Private/public differences do not change meaning.
    key = hashlib.sha256((kind + '\n' + context + '\n' + normalized).encode()).hexdigest()
    earlier = seen.get(key)
    eligible = kind in ('theorem','lemma','def','abbrev') and not pending_local_open
    eligible = eligible and full != 'PEqualNP.Outside.L_meta_670'
    if earlier and eligible:
        modifiers = m.group('mods')
        alias = modifiers + 'abbrev ' + name + ' := @' + earlier + '\n\n'
        # Aliases smaller than their source are the only useful replacements.
        if len(alias) < len(block):
            output.append(alias)
            records.append({'name': full,'alias': earlier,'saved_bytes': len(block.encode())-len(alias.encode())})
        else: output.append(block)
    else:
        output.append(block)
        if eligible: seen.setdefault(key, full)
    known[full] = key
    by_short.setdefault(name.rsplit('.',1)[-1], []).append(full)
    pending_local_open = False
result = ''.join(output)
a.output.write_text(result)
report = {'source':str(a.source),'output':str(a.output),'before_bytes':len(src.encode()),'after_bytes':len(result.encode()),'aliases':records}
a.report.write_text(json.dumps(report, indent=2))
print(json.dumps({k:v for k,v in report.items() if k!='aliases'}))
print('aliases:', len(records))
