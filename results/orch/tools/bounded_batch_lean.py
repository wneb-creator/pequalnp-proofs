import argparse
import json
import re
from collections import defaultdict
from pathlib import Path

ap = argparse.ArgumentParser()
ap.add_argument('source', type=Path)
ap.add_argument('output', type=Path)
ap.add_argument('--helpers', type=Path, required=True)
ap.add_argument('--report', type=Path, required=True)
ap.add_argument('--group-size', type=int, default=4)
a = ap.parse_args()
assert 1 <= a.group_size <= 8
src = a.source.read_text()
command = re.compile(r'^(?:import\b|namespace\b|end\b|(?:noncomputable\s+)?section\b|open\b|include\b|omit\b|variable\b|set_option\b|@\[|(?:(?:private|protected|noncomputable)\s+)*(?:theorem|lemma|def|abbrev|structure|inductive)\b)', re.M)
starts = [m.start() for m in command.finditer(src)] + [len(src)]
units = []
ns = []
frames = []
block_re = re.compile(r'^(?:theorem|lemma)\s+(\w+)\s*:\s*block\s+(\w+)\s+(\d+)\s+(\d+)\s+(\d+)\s*=\s*true\s*:=')
cell_re = re.compile(r':=\s*by\s+apply\s+cellsBlock\s+\(ar\s*:=\s*(\d+)\)\s+\(rows\s*:=\s*(\d+)\)\s+\(d\s*:=\s*(\d+)\)')
levels = defaultdict(list)
for start, end in zip(starts, starts[1:]):
    text = src[start:end]
    line = text.splitlines()[0]
    idx = len(units)
    units.append({'text': text, 'ns': tuple(ns)})
    m = block_re.match(text)
    if m:
        name, forest, k, pos, count = m.groups()
        record = dict(idx=idx, name=name, forest=forest, k=int(k), pos=int(pos), count=int(count))
        cell = cell_re.search(text)
        if cell:
            record['cell'] = tuple(map(int, cell.groups()))
        levels[(tuple(ns), forest, int(k))].append(record)
    if line.startswith('namespace '):
        frames.append(len(ns))
        ns.extend(line[10:].strip().split('.'))
    elif line.startswith(('section', 'noncomputable section')):
        frames.append(len(ns))
    elif line.startswith('end') and frames:
        del ns[frames.pop():]

wrapper = '''lemma pilotBlockBatched (g : Forest) (k start : Nat)
    (chunks : List (Nat × Nat × Nat × Nat))
    (h : FiniteChunk.proofChunks (fun (pos n : Nat) (w : Nat × Nat × Nat) =>
      cells g k pos n w.1 w.2.1 w.2.2) start chunks) :
    block g k start (FiniteChunk.chunkSize chunks) = true := by
  exact FiniteChunk.proofChunks_sound (fun pos n => block g k pos n = true)
    (fun (pos n : Nat) (w : Nat × Nat × Nat) => cells g k pos n w.1 w.2.1 w.2.2)
    (fun _ => rfl) (fun pos x y => @block_merge g k pos x y)
    (fun pos n w => @cellsBlock g k pos n w.1 w.2.1 w.2.2) chunks start h

'''
removals = set()
replacements = {}
stats = []
rejected = []
wrapped = set()
for key, records in levels.items():
    leaves = sorted([r for r in records if 'cell' in r], key=lambda r: r['pos'])
    if len(leaves) < 2:
        continue
    pos = 0
    for leaf in leaves:
        if leaf['pos'] != pos:
            break
        pos += leaf['count']
    else:
        anchors = [r for r in records if r['pos'] == 0 and r['count'] == pos]
        if len(anchors) != 1:
            rejected.append([list(key[0]), key[1], key[2], 'ambiguous anchor'])
            continue
        anchor = anchors[0]
        own_idxs = {r['idx'] for r in records}
        removed_names = {r['name'] for r in records if r['idx'] != anchor['idx']}
        refs = []
        if removed_names:
            ref_re = re.compile(r'\b(?:' + '|'.join(map(re.escape, removed_names)) + r')\b')
            refs = [i for i, u in enumerate(units) if i not in own_idxs and u['ns'] == key[0] and ref_re.search(u['text'])]
        if refs:
            rejected.append([list(key[0]), key[1], key[2], 'external intermediate reference'])
            continue
        # A non-cell declaration must only combine sub-blocks; never discard a
        # separate corner or fallback computation hidden in this level.
        if any('cell' not in r and 'block_merge' not in units[r['idx']]['text'] for r in records):
            rejected.append([list(key[0]), key[1], key[2], 'non-cell leaf'])
            continue
        if any(r['idx'] > anchor['idx'] for r in records):
            rejected.append([list(key[0]), key[1], key[2], 'anchor precedes leaves'])
            continue
        generated = ''
        if key[0] not in wrapped:
            generated += wrapper
            wrapped.add(key[0])
        groups = []
        for gi in range(0, len(leaves), a.group_size):
            group = leaves[gi:gi+a.group_size]
            tag = 'pilotB_' + anchor['name'] + '_' + str(gi // a.group_size)
            data = tag + '_data'
            values = ','.join('(' + ','.join(map(str, (r['count'], *r['cell']))) + ')' for r in group)
            count = sum(r['count'] for r in group)
            start = group[0]['pos']
            generated += 'def ' + data + ' : List (Nat × Nat × Nat × Nat) := [' + values + ']\n'
            generated += 'set_option maxRecDepth 16384 in\nset_option maxHeartbeats 0 in\n'
            generated += 'theorem ' + tag + ' : block ' + key[1] + ' ' + str(key[2]) + ' ' + str(start) + ' ' + str(count) + ' = true := by\n'
            generated += '  apply pilotBlockBatched ' + key[1] + ' ' + str(key[2]) + ' ' + str(start) + ' ' + data + '\n'
            generated += '  simp only [' + data + ', FiniteChunk.proofChunks, cells, boxes, Nat.reduceDiv, Nat.reduceSub, Nat.reduceAdd, and_true]\n'
            generated += "  repeat' apply And.intro\n  all_goals decide +kernel\n\n"
            groups.append((tag, start, count))
        proof = groups[-1][0]
        suffix_count = groups[-1][2]
        for tag, start, count in reversed(groups[:-1]):
            proof = '(@block_merge ' + key[1] + ' ' + str(key[2]) + ' ' + str(start) + ' ' + str(count) + ' ' + str(suffix_count) + ' ' + tag + ' ' + proof + ')'
            suffix_count += count
        generated += 'theorem ' + anchor['name'] + ' : block ' + key[1] + ' ' + str(key[2]) + ' 0 ' + str(pos) + ' = true := by\n  exact ' + proof + '\n\n'
        replacements[anchor['idx']] = generated
        removals.update(own_idxs - {anchor['idx']})
        stats.append(dict(namespace='.'.join(key[0]), forest=key[1], level=key[2], leaves=len(leaves), groups=len(groups), anchor=anchor['name']))
        continue
    rejected.append([list(key[0]), key[1], key[2], 'noncontiguous cells'])

out = [src[:starts[0]]]
pending = []
for idx, u in enumerate(units):
    text = u['text']
    if text.startswith('set_option '):
        pending.append(text)
        continue
    if idx in removals or idx in replacements:
        pending = []
        if idx in replacements:
            out.append(replacements[idx])
        continue
    out.extend(pending)
    pending = []
    out.append(text)
out.extend(pending)
result = ''.join(out)
helpers = '\n'.join(line for line in a.helpers.read_text().splitlines() if not line.startswith('import ')) + '\n'
imports = re.match(r'(?:import [^\n]+\n)+', result)
assert imports
result = result[:imports.end()] + '\n' + helpers + result[imports.end():]
a.output.write_text(result)
report = dict(before_bytes=len(src.encode()), after_bytes=len(result.encode()), removed_declarations=len(removals), levels=stats, rejected=rejected)
a.report.write_text(json.dumps(report, indent=2))
print(json.dumps({k:v for k,v in report.items() if k not in ['levels', 'rejected']}))
print('levels', len(stats), 'rejected', len(rejected))
