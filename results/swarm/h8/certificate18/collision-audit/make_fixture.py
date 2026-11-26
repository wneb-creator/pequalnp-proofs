"""Extract the small portable audit fixture from the frozen native inputs."""
from pathlib import Path
import argparse
import hashlib
import json
import re

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--source-root', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
root = args.source_root
names = {
    'pairs': 'cert18/emitter/compression/supported/GlobalCollisionData.lean',
    'target': 'signedfull/no670/probe-data.hpp',
    'wires': 'cert18/emitter/supported/wires.bin',
    'states': 'cert18/emitter/supported/states.json',
    'row_mapping': 'signedfull/delivery/native-extended-row-permutation.json',
    'original_audit': 'cert18/emitter/audit_packed_collision.py',
    'original_report': 'cert18/emitter/supported/packed-collision-native-audit.json',
}
inputs = {name: (root / relative).read_bytes() for name, relative in names.items()}
source = inputs['pairs'].decode()
packed = int(re.search(r'def collisionPairCodes : Nat := (0x[0-9a-fA-F]+)', source).group(1), 0)
pairs = [((packed >> (20*i)) & 1023, (packed >> (20*i+10)) & 1023) for i in range(419)]
header = inputs['target'].decode()
body = re.search(r'const Word target=\{\{(.*?)\}\};', header).group(1)
words = [int(x, 16) for x in re.findall(r'0x([0-9a-fA-F]+)', body)]
assert len(words) == 16
target = sum(w << (64*i) for i, w in enumerate(words))
slots = [9, 7, 5, 8, 6, 4, 2, 0, 3, 1]
row_map = [sum(((r >> i) & 1) << slots[i] for i in range(10)) for r in range(1024)]
assert sorted(row_map) == list(range(1024))
mapping = json.loads(inputs['row_mapping'])
assert mapping['pin_bit_positions'] == slots
assert mapping['standard_to_extended'] == row_map
assert all(mapping['extended_to_standard'][row_map[r]] == r for r in range(1024))
def extended(w):
    return sum(((w >> r) & 1) << row_map[r] for r in range(1024))
wire_data = inputs['wires']
assert len(wire_data) % 144 == 0
native = [int.from_bytes(wire_data[i:i+128], 'little') for i in range(0, len(wire_data), 144)]
states = json.loads(inputs['states'])
selected = [0, 52, 292, 522, 5229]
nodes = []
for i in selected:
    state = states[i]
    assert state['id'] == i
    nodes.append({
        'node': i,
        'depth': state['depth'],
        'cap': 17 - state['depth'],
        'native_wire_ids': state['ws'],
        'bank_extended_hex': [format(extended(native[w]), '0256x') for w in state['ws']],
    })
original_report = json.loads(inputs['original_report'])
assert [x['node'] for x in original_report['nodes']] == selected
fixture = {
    'schema': 'packed-collision-fixture-v1',
    'word_bits': 1024,
    'signature_bits': 419,
    'target_extended_hex': format(extended(target), '0256x'),
    'pairs_extended': pairs,
    'nodes': nodes,
    'expected_node_results': original_report['nodes'],
    'provenance': {
        'source_inputs': {
            name: {'relative_path': names[name], 'bytes': len(data), 'sha256': hashlib.sha256(data).hexdigest()}
            for name, data in inputs.items()
        },
        'row_convention': 'Bit r of a word is its value on row r; signatures put pair i at bit i.',
        'standard_to_extended_pin_bit_positions': slots,
        'row_mapping_formula': 'E(r) = sum(((r >> i) & 1) << slots[i] for i in range(10))',
        'word_mapping_formula': 'Extended(w)[E(r)] = native(w)[r]',
        'row_mapping_verified_against_all_1024_entries_and_inverse': True,
        'native_wire_record': '144 bytes: 128 little-endian truth bytes followed by four int32 origin fields',
        'native_word_order': 'The 16 uint64 limbs are little-endian in the 1024-bit word.',
        'pair_source_encoding': 'GlobalCollisionData.collisionPairCodes: r in low10, s in next10, pair0 in low20 bits.',
        'source_root_required_for_extraction_only': True,
    },
}
args.output.write_text(json.dumps(fixture, indent=2) + '\n')
print(json.dumps({'nodes': len(nodes), 'pairs': len(pairs), 'fixture_bytes': args.output.stat().st_size,
                  'sha256': hashlib.sha256(args.output.read_bytes()).hexdigest()}))
