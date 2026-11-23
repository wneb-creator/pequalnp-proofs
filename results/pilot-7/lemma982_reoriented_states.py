import collections
import functools
import json
from pathlib import Path

from lemma982_checkpoint_pack import step
from lemma982_fullstate_size import huffman
from lemma982_invariant_keys import tables, transformed

ROOT = Path('/tmp/oec/pequalnp-pilot-7')


def reorient(d):
    n, k = d['n'], d['K']
    perms = d['vertex_perms']
    lookup_perm = {tuple(p): i for i, p in enumerate(perms)}
    ts = tables(n, perms)
    word_mask = (1 << (1 << n))-1
    positions = [0] * (1 << n)
    for i, row in enumerate(d['paired_rows']): positions[row] |= 1 << i
    encode_tables = []
    for j in range((1 << n)//8):
        tab = [0]*256
        for v in range(1, 256):
            low = v & -v
            tab[v] = tab[v-low] | positions[j*8+low.bit_length()-1]
        encode_tables.append(tab)
    @functools.cache
    def encode(w): return transformed(w, encode_tables)
    @functools.cache
    def image(w, g): return transformed(w, ts[g])
    words = [int(w, 16) for w in d['full_truth_words_hex']]
    originals = [[[words[j] for j in row] for row in layer] for layer in d['states']]
    cap = len(originals)-1
    states = [[] for _ in originals]
    recipes = [[] for _ in originals]
    # Each item is (old state index, orientation, list of truth words).
    states[cap] = [(0, 0, originals[cap][0])]
    for s in range(cap-1, -1, -1):
        first = {}
        for pi, (oldparent, orient, parent) in enumerate(states[s+1]):
            origparent = originals[s+1][oldparent]
            positions_new = {word: i for i, word in enumerate(parent)}
            for entry in d['advice'][s+1][oldparent]:
                tag, payload = entry % 1024, entry//1024-1
                oldchild, sym = payload//64, payload % 64
                if oldchild in first: continue
                if tag < 48:
                    a = positions_new[image(origparent[tag//4], orient)]
                    newtag = 4*a+tag%4
                else:
                    t, flags = divmod(tag-48, 8)
                    b = 0
                    while (b+1)*(b+2)//2 <= t: b += 1
                    a = t-b*(b+1)//2
                    pa = positions_new[image(origparent[a], orient)]
                    pb = positions_new[image(origparent[b], orient)]
                    conj = flags//4
                    ka, kb = bool(flags & 2), bool(flags & 1)
                    if pa > pb: pa, pb, ka, kb = pb, pa, kb, ka
                    newtag = 48+8*(pb*(pb+1)//2+pa)+4*conj+2*ka+kb
                generated = sorted(step(word_mask, parent, newtag), key=encode)
                inv = perms[d['inverse_perms'][sym]]
                po = perms[orient]
                child_orient = lookup_perm[tuple(po[inv[i]] for i in range(n))]
                check = sorted((image(w, child_orient) for w in originals[s][oldchild]), key=encode)
                assert generated == check, (d['case'], s, oldchild)
                first[oldchild] = (pi, newtag, child_orient, generated)
        order = sorted(first, key=lambda j: tuple(encode(w) for w in first[j][3]))
        for oldchild in order:
            parent, tag, orient, generated = first[oldchild]
            recipes[s].append((parent, tag))
            states[s].append((oldchild, orient, generated))
        keys = [tuple(encode(w) for w in item[2]) for item in states[s]]
        assert keys == sorted(keys) and len(set(keys)) == len(keys)
    return states, recipes


def main():
    all_data = []
    paths = sorted(ROOT.glob('root982-core*-data.json'))
    for c in [0,8]:
        if not (ROOT/f'root982-core{c}-data.json').is_file():
            paths.append(ROOT/f'term-context-982-seed{c}-reduced-data.json')
    for p in paths:
        d = json.loads(p.read_text())
        states, recipes = reorient(d)
        raw_bits = 0
        parent_bits = 0
        count = 0
        tags = []
        for s, layer in enumerate(recipes):
            if not layer: continue
            pw = max(0, (len(states[s+1])-1).bit_length())
            tw = max(tag.bit_length() for _, tag in layer)
            raw_bits += (pw+tw)*len(layer)
            parent_bits += pw*len(layer)
            count += len(layer)
            tags.extend(tag for _, tag in layer)
        out = dict(case=d['case'], K=d['K'], cap=len(states)-1,
            counts=list(map(len, states)), recipes=recipes,
            original_indices=[[item[0] for item in layer] for layer in states],
            orientations=[[item[1] for item in layer] for layer in states],
            full_truth_states=[[list(map(hex,item[2])) for item in layer] for layer in states],
            every_recipe_uses_identity_symmetry=True,
            states_sorted_lexicographically_by_paired_encoding=True,
            every_generated_state_matches_original_orbit=True)
        (ROOT/f'lemma982-reoriented-core{d["case"]}.json').write_text(json.dumps(out,separators=(',',':'))+'\n')
        summary = dict(case=d['case'], states=sum(map(len,states)), raw_recipe_hex_bytes=(raw_bits+3)//4,
                       parent_bits=parent_bits, tags=tags)
        all_data.append(summary)
        print(json.dumps({k:v for k,v in summary.items() if k!='tags'}),flush=True)
    lengths = huffman(collections.Counter(t for d in all_data for t in d['tags']))
    total = sum(d['parent_bits']+sum(lengths[t] for t in d['tags']) for d in all_data)
    report = dict(cores=[{k:v for k,v in d.items() if k!='tags'} for d in all_data],
                  raw_recipe_hex_bytes=sum(d['raw_recipe_hex_bytes'] for d in all_data),
                  fixed_parent_huffman_tag_hex_bytes=(total+3)//4,
                  huffman_tag_code_lengths=dict(lengths),
                  huffman_blocks_and_codebook_not_included=True)
    (ROOT/'lemma982-reoriented-size-report.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k not in ('cores','huffman_tag_code_lengths')}),flush=True)


if __name__ == '__main__': main()
