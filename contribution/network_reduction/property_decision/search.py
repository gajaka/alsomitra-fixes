"""Deterministic exact-rational witness search; Lean checks the chosen results."""
from fractions import Fraction as F
import itertools
import json
from pathlib import Path
import re

HERE = Path(__file__).resolve().parent
NETWORK = HERE.parent


def layers(model):
    source = (NETWORK / (model + '.lean')).read_text()
    line = re.search(r'^def originalRationals .*$', source, re.M).group()
    values = [F(int(n), int(d)) for n, d in re.findall(r'mkRat \((-?\d+)\) (\d+)', line)]
    if len(values) != 75:
        raise ValueError('Unexpected original parameter count')
    result = []
    offset = 0
    for ins, outs in [(6, 6), (6, 4), (4, 1)]:
        weights = [values[offset+j*ins:offset+(j+1)*ins] for j in range(outs)]
        offset += ins*outs
        biases = values[offset:offset+outs]
        offset += outs
        result.append((weights, biases))
    return result


def evaluate(network, xs):
    for weights, biases in network:
        xs = [max(F(0), sum((w*x for w, x in zip(row, xs)), b))
              for row, b in zip(weights, biases)]
    return xs[0]


def displacement(xs):
    return (F('41.232296222734604')*xs[4]+F('0.482420778264618') +
            F('45.878638794593570')*xs[5]-F('41.681405266088724'))


def search():
    report = {'scope': 'Finite exact search, not universal verification',
              'margin': '2', 'models': {}}
    for model in ['Baseline', 'Adversarial']:
        found = {}
        count = 0
        net = layers(model)
        for grid in [[F(1,4), F(1,2), F(3,4)], [F(1,8), F(7,8)]]:
            for point in itertools.product(grid, repeat=6):
                count += 1
                d = displacement(point)
                value = evaluate(net, point)
                label = 'Above' if d >= 2 and value < F(1,2) else (
                    'Below' if d <= -2 and value > F(1,2) else None)
                if label and label not in found:
                    found[label] = {'input': list(map(str, point)),
                                    'output_exact': str(value), 'output_approx': float(value),
                                    'displacement_exact': str(d), 'displacement_approx': float(d),
                                    'threshold_gap_exact': str(abs(value-F(1,2)))}
                if len(found) == 2:
                    break
            if len(found) == 2:
                break
        if len(found) != 2:
            raise ValueError('No witness for every requested property: ' + model)
        report['models'][model] = {'candidates_evaluated': count, 'witnesses': found}
    return report


if __name__ == '__main__':
    print(json.dumps(search(), indent=2))
