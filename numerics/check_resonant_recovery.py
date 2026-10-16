"""Check the recovered matrix program against seven manuscript table entries."""
import json
import math
from pathlib import Path

import resonant_audit_original
import resonant_matrix

root = Path(__file__).resolve().parent.parent
dataset = [tuple(map(float, line.split())) for line in
           (root / 'data/mtheta_data.dat').read_text().splitlines()[1:] if line.strip()]
table = [((1, 0), 1.5849625), ((1, -1), 1.2924813),
         ((3, 1), 1.1702210), ((4, 1), 1.1981591),
         ((5, 1), 1.2073297), ((5, 2), 1.1680358), ((7, 1), 1.1694128)]
results = []
for pair, expected in table:
    original = resonant_audit_original.compute(*pair)
    result = resonant_matrix.compute(*pair)
    assert all(original[key] == result[key] for key in original)
    assert len(result['transition_targets']) == result['states']
    assert all(len(row) <= 3 for row in result['transition_targets'])
    assert all(0 <= target < result['states'] for row in result['transition_targets'] for target in row)
    estimate = (result['dim_lower'] + result['dim_upper']) / 2
    assert abs(estimate - expected) < 5.1e-8
    record = {key: value for key, value in result.items()
              if key not in ('state_vectors', 'transition_targets')}
    nearest = min(dataset, key=lambda row: abs(row[0] - result['theta']))
    if abs(nearest[0] - result['theta']) < 1e-4:
        error = abs(estimate - nearest[1])
        assert error < 1e-6
        record.update(dataset_theta=nearest[0], dataset_dimension=nearest[1], absolute_error=error)
    results.append(record)
assert abs(results[0]['dim_lower'] - math.log2(3)) < 1e-10
assert abs(results[1]['dim_lower'] - math.log2(6)/2) < 1e-10
output = {'scope': 'Seven table cases; not a full regeneration of the 218-row dataset. Floating-point results are not certified enclosures.', 'results': results}
(root / 'numerics/resonant_recovery_checks.json').write_text(json.dumps(output, indent=2) + '\n', encoding='utf-8')
print('PASS: seven table cases, unchanged numerical results, matrix shape/indices and available matching blue points.')
