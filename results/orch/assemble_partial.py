from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
NAMES = [
    'StarLibrary.lean', 'StarGeometry.lean', 'StarNormalForm.lean',
    'StarSandwich.lean', 'StarCover.lean', 'CriticalRestriction.lean',
    'PivotalNecessary.lean', 'PivotalUnique.lean', 'TwoLeafRepair.lean',
    'MatchingExchange.lean', 'BackwardNormalize.lean', 'ExternalRepair.lean',
    'FourVertexGeometry.lean', 'DoubleStarGeometry.lean', 'RectangleRepair.body',
    'StarCounterexample.lean', 'PivotalStarLimitation.lean', 'PrivateSupportLimitation.lean',
]
parts = []
for name in NAMES:
    source = (ROOT / 'results/orch/lemmas' / name).read_text()
    parts.append('\n'.join(line for line in source.splitlines()
                           if not line.startswith('import ')).strip())
source = 'import PEqualNP.Defs\n\n' + '\n\n'.join(parts) + '\n'
(ROOT / 'lean/PEqualNP/Outside/L_meta_2448.lean').write_text(source)
print('Partial helper file only; posted theorem absent. Lines:', len(source.splitlines()))
