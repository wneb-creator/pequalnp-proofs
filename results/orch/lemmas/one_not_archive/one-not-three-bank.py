from pathlib import Path
import json
import itertools

HERE = Path(__file__).resolve().parent
data = json.loads((HERE / 'one-not-residual-result.json').read_text())
bank = [(int(table), expression) for table, expression in data['bank'].items()]
target = data['target']
found = []
checked = 0
for k in range(1, 4):
    for inputs in itertools.combinations(bank, k):
        checked += 1
        classes = {}
        determines = True
        for assignment in range(64):
            pattern = sum(((table >> assignment) & 1) << i
                          for i, (table, _) in enumerate(inputs))
            value = (target >> assignment) & 1
            if pattern in classes and classes[pattern] != value:
                determines = False
                break
            classes[pattern] = value
        if determines:
            found.append([expression for _, expression in inputs])
result = {'subsets_tested': checked, 'determining_subsets': found}
print(json.dumps(result))
(HERE / 'one-not-three-bank-result.json').write_text(json.dumps(result, indent=2) + '\n')
