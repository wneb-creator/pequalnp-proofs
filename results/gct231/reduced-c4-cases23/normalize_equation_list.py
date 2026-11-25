"""Normalize a reviewed string-equation list without changing its mathematics."""
import argparse
import hashlib
import json
from pathlib import Path

parser = argparse.ArgumentParser()
parser.add_argument('source', type=Path)
parser.add_argument('output', type=Path)
args = parser.parse_args()
source = json.loads(args.source.read_text())
assert 'variables' in source and isinstance(source['variables'], list)
assert all(isinstance(equation, str) for equation in source['equations'])
normalized = {'unknowns': source['variables'],
              'equations': [{'coefficient': equation} for equation in source['equations']],
              'normalized_from': str(args.source),
              'normalized_source_sha256': hashlib.sha256(args.source.read_bytes()).hexdigest(),
              'scope': source.get('scope', 'Exact equation-list representation change only.')}
args.output.write_text(json.dumps(normalized, indent=2) + '\n')
print('Normalized exact ordered equation list:', len(normalized['unknowns']),
      'variables,', len(normalized['equations']), 'equations')
print('Source SHA256:', normalized['normalized_source_sha256'])
print('Normalized SHA256:', hashlib.sha256(args.output.read_bytes()).hexdigest())
