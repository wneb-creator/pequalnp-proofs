import argparse
import pathlib
import re

parser = argparse.ArgumentParser()
parser.add_argument('source', type=pathlib.Path)
parser.add_argument('output', type=pathlib.Path)
args = parser.parse_args()
command = re.compile(r'^(?:import\b|namespace\b|end\b|(?:noncomputable\s+)?section\b|open\b|variable\b|set_option\b|(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive)\b)', re.M)
declaration = re.compile(r'^(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive)\s+([A-Za-z_][\w.]*)')
def blocks(source):
    starts = [m.start() for m in command.finditer(source)] + [len(source)]
    return [source[a:b] for a,b in zip(starts,starts[1:])]

template = pathlib.Path('/workspace/pequalnp-proofs/lean/PEqualNP/Outside/L_meta_1676.lean').read_text()
families = {k: '' for k in ['BoundPool','IndexTree','Forest']}
for block in blocks(template):
    match = declaration.match(block)
    if match:
        for name in families:
            if match[1] == name or match[1].startswith(name + '.'):
                families[name] += block

source = args.source.read_text()
output = []
namespace = []
frames = []
replaced = set()
counts = {k:0 for k in families}
for block in blocks(source):
    line = block.splitlines()[0]
    if line.startswith('namespace '):
        frames.append(len(namespace))
        namespace.extend(line[10:].strip().split('.'))
    elif line.startswith('section') or line.startswith('noncomputable section'):
        frames.append(len(namespace))
    elif line.startswith('end'):
        if frames:
            del namespace[frames.pop():]
    match = declaration.match(block)
    target = None
    for n in ['2444','1676','1678']:
        if 'C' + n in namespace or 'L_meta_' + n in namespace:
            target = n
            break
    if match and target:
        family = next((name for name in families if match[1] == name or match[1].startswith(name + '.')), None)
        if family and (family == 'BoundPool' or target in ['2444','1676']):
            key = (tuple(namespace),family)
            if key not in replaced:
                output.append(families[family])
                replaced.add(key)
                counts[family] += 1
            continue
    output.append(block)
text = ''.join(output)
args.output.write_text(text)
print('records standardized', counts, 'bytes', len(source.encode()), '->', len(text.encode()))
