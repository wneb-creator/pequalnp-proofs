from pathlib import Path
import argparse, hashlib, json, re, resource

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
job = Path(__file__).resolve().parent
parser = argparse.ArgumentParser(description='Check and generate a Lean proof candidate for L-meta-3773.')
parser.add_argument('--candidate', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
parser.add_argument('--template', type=Path, default=job / 'Meta3773Control64Fast.lean')
parser.add_argument('--statement', type=Path, default=job / 'meta3773-statement.txt')
parser.add_argument('--words', type=Path, default=job / 'meta3773-input-words.json')
parser.add_argument('--and-is-one', action='store_true')
parser.add_argument('--control64', action='store_true', help='Positive-control mode only; generates a different auxiliary theorem with bound64.')
args = parser.parse_args()
protected = {path.resolve() for path in (args.candidate, args.template, args.statement, args.words, Path(__file__))}
if args.output.resolve() in protected:
    raise ValueError('The output must be distinct from every generator input and the generator itself.')

def pinned(path, expected):
    raw = path.read_bytes()
    if hashlib.sha256(raw).hexdigest() != expected:
        raise ValueError('Reviewed component hash changed: ' + path.name)
    return raw.decode()

source = pinned(args.template, 'd7ef078f0fddf3efe61c6af689f9fb6fc82c6d113f40fb0c39b572b8c698e05f')
statement = pinned(args.statement, '96c725c1f7c452c1e544b1b5903494636b67cd531d63c097bc1f54a11da2ed41').strip()
data = json.loads(pinned(args.words, 'ab8ec671f022fd9928769319c498ea7acf3bc7c43f3c9fda89ef6bede896f0e1'))
candidate_raw = args.candidate.read_bytes()
candidate = json.loads(candidate_raw)
if candidate.get('input_count', candidate.get('inputs', 26)) != 26:
    raise ValueError('A complete26-input circuit is required.')
gates = []
for k, gate in enumerate(candidate['gates']):
    if not isinstance(gate, list) or len(gate) != 3:
        raise ValueError('A gate must have exactly opcode and two input indices.')
    op, a, b = gate
    if type(op) not in (int, bool) or op not in (0, 1):
        raise ValueError('Only binary AND/OR opcodes0 and1 are supported.')
    if type(a) is not int or type(b) is not int or not (0 <= a < 26 + k and 0 <= b < 26 + k):
        raise ValueError('A gate operand is not a prior wire.')
    gates.append([1 - int(op) if args.and_is_one else int(op), a, b])
bound = 64 if args.control64 else 63
if not 1 <= len(gates) <= bound:
    raise ValueError('Gate count exceeds the requested bound: ' + str(len(gates)))
output = candidate.get('output', candidate.get('outputs', [25 + len(gates)])[0])
if type(output) is not int or output != 25 + len(gates):
    raise ValueError('Normalize the circuit so its output is the last gate.')
allowed = {(0, 0, 13), (1, 0, 1), (1, 0, 13), (1, 2, 13)}
if tuple(gates[0]) not in allowed:
    op, a, b = gates[0]
    if (op, b, a) not in allowed:
        raise ValueError('Normalize the allowed first gate before generating a proof.')
    gates[0] = [op, b, a]
if data['row_count'] != 808 or data['positive_count'] != 52 or len(data['words']) != 26:
    raise ValueError('Unexpected packed test schema.')
values = list(map(int, data['words']))
for op, a, b in gates:
    values.append(values[a] | values[b] if op else values[a] & values[b])
if values[output] != (1 << 52) - 1:
    raise ValueError('The circuit does not pass every exact808-row packed test.')

def gate_text():
    return '  [' + ',\n   '.join('(' + ('true' if op else 'false') + ',' + str(a) + ',' + str(b) + ')' for op, a, b in gates) + ']\n'

for name in ('gates64', 'controlGates64'):
    pattern = r'(def ' + name + r' : List \(Bool × (?:Nat|ℕ) × (?:Nat|ℕ)\) :=\n)  \[.*?\]\n'
    source, count = re.subn(pattern, lambda m: m[1] + gate_text(), source, count=1, flags=re.S)
    if count != 1:
        raise ValueError('Expected exactly one gate definition: ' + name)
head = '(' + ('true' if gates[0][0] else 'false') + ',' + str(gates[0][1]) + ',' + str(gates[0][2]) + ')'
old = '  refine ⟨controlGates64,(true,0,1),?_,?_,?_,?_⟩'
if source.count(old) != 1 or source.count('gs.length ≤ 64') != 1:
    raise ValueError('The reviewed witness assembly layout changed.')
source = source.replace(old, '  refine ⟨controlGates64,' + head + ',?_,?_,?_,?_⟩')
source = source.replace('gs.length ≤ 64', 'gs.length ≤ ' + str(bound))
marker = 'theorem PEqualNP.Outside.L_meta_3773_aux.control64 :'
if source.count(marker) != 1:
    raise ValueError('The reviewed final theorem layout changed.')
source = source[:source.index(marker)]
for old, new in (('gates64', 'witnessGates'), ('controlGates64', 'witnessGates'), ('replay808', 'witness_replay'), ('control_search64', 'witness_search')):
    source = re.sub(r'\b' + old + r'\b', new, source)
if args.control64:
    if statement.count('(63 : ℕ)') != 1:
        raise ValueError('The control theorem bound cannot be identified.')
    statement = statement.replace('(63 : ℕ)', '(64 : ℕ)')
    theorem = 'PEqualNP.Outside.L_meta_3773_aux.generated_control64'
else:
    theorem = 'PEqualNP.Outside.L_meta_3773'
source += 'theorem ' + theorem + ' :\n    ' + statement + ' := by\n'
source += '  exact PEqualNP.Outside.L_meta_3773_aux.Packed.of_search_bound ' + str(bound) + '\n'
source += '    PEqualNP.Outside.L_meta_3773_aux.Packed.witness_search\n'
if any(bad in source for bad in ('_root_', 'sorry', 'native_decide', 'axiom', '"', '@[')):
    raise ValueError('A prohibited source construct was encountered.')
if any(line.rstrip() != line for line in source.splitlines()):
    raise ValueError('Trailing source whitespace was encountered.')
args.output.write_text(source)
print(json.dumps({'scope': 'Generated Lean candidate; a fresh Lean build and local checker are still required.', 'bound': bound, 'gates': len(gates), 'head': gates[0], 'rows': 808, 'candidate_sha256': hashlib.sha256(candidate_raw).hexdigest(), 'source_sha256': hashlib.sha256(source.encode()).hexdigest(), 'theorem': theorem}))
