from pathlib import Path
import json
import hashlib
import resource

resource.setrlimit(resource.RLIMIT_CORE, (0, 0))

job = Path('/tmp/oec/pequalnp-pilot-79')
source = job / 'three-plane-diagonal-anchor-integer-moment.json'
binding = hashlib.sha256(source.read_bytes()).hexdigest()
data = json.loads(source.read_text())
matrix = data['integer_matrix']
prime = 5
size = len(matrix)
augmented = [[entry % prime for entry in row] + [int(i == j) for j in range(size)]
    for i, row in enumerate(matrix)]
for i in range(size):
    pivot = next(j for j in range(i, size) if augmented[j][i] != 0)
    augmented[i], augmented[pivot] = augmented[pivot], augmented[i]
    inverse = pow(augmented[i][i], -1, prime)
    augmented[i] = [entry * inverse % prime for entry in augmented[i]]
    for j in range(size):
        if i != j:
            factor = augmented[j][i]
            augmented[j] = [(left - factor * right) % prime
                for left, right in zip(augmented[j], augmented[i])]
inverse = [row[size:] for row in augmented]
assert all(sum(matrix[i][k] * inverse[k][j] for k in range(size)) % prime == int(i == j)
    for i in range(size) for j in range(size))
assert hashlib.sha256(source.read_bytes()).hexdigest() == binding
out = {'prime': prime, 'integer_matrix': matrix, 'modular_inverse': inverse,
    'modular_determinant': data['integer_determinant'] % prime,
    'product_verified': True, 'integer_moment_sha256': binding}
(job / 'three-plane-diagonal-anchor-modular-inverse-5.json').write_text(json.dumps(out) + '\n')
print(json.dumps({'prime': prime, 'determinant_mod': out['modular_determinant'], 'product_verified': True}))
