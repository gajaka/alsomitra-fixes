"""Finite ONNX Runtime replay of the formally checked interior witnesses."""
import argparse
from fractions import Fraction as F
import hashlib
import json
from pathlib import Path
import platform
import subprocess

import numpy as np
import onnx
from onnx import numpy_helper
import onnxruntime as ort

HERE = Path(__file__).resolve().parent
CONTRIBUTION = HERE.parent.parent
ROOT = CONTRIBUTION.parent
PIN = 'e9f6f1c52e0e5349455d2b4f69c2015567d3037f'
FILENAMES = {'Baseline': 'final_base_model_norm.onnx',
             'Adversarial': 'final_adversarial_model_0.005.onnx'}


def require(condition, message):
    if not condition:
        raise ValueError(message)


def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--search', type=Path, required=True)
    parser.add_argument('--output', type=Path, required=True)
    parser.add_argument('--upstream', type=Path, required=True)
    args = parser.parse_args()
    search = json.loads(args.search.read_text())
    prior = json.loads((CONTRIBUTION / 'results/network_reduction_verification.json').read_text())
    require(prior['status'] == 'PASS', 'Previous checkpoint binding must pass')
    report = {'status': 'PASS', 'scope': 'Eight finite executions, not universal float32 refinement',
              'versions': {'numpy': np.__version__, 'onnx': onnx.__version__,
                           'onnxruntime': ort.__version__, 'platform': platform.platform()},
              'search_sha256': sha(args.search), 'models': {}, 'execution_count': 0}
    for model, filename in FILENAMES.items():
        rows = {}
        for variant in ['original', 'reduced']:
            path = (args.upstream / 'python_training/models' / filename if variant == 'original'
                    else CONTRIBUTION / '.build/network_reduction' / (model + '.onnx'))
            binding = prior['generation']['models'][model]
            require(sha(path) == binding[variant + '_sha256'], 'Changed ONNX artifact')
            if variant == 'original':
                blob = subprocess.check_output(['git', 'show', PIN + ':python_training/models/' + filename],
                                               cwd=args.upstream)
                require(blob == path.read_bytes(), 'ONNX differs from pinned Git blob')
            graph = onnx.load(path)
            onnx.checker.check_model(graph)
            require([n.op_type for n in graph.graph.node] == ['Gemm', 'Relu']*3,
                    'Unexpected network graph')
            arrays = {t.name: numpy_helper.to_array(t) for t in graph.graph.initializer}
            flat = []
            for i in range(3):
                node = graph.graph.node[2*i]
                w, b = [arrays[n] for n in node.input[1:]]
                flat.extend(w.T.flatten().view(np.uint32).tolist())
                flat.extend(b.view(np.uint32).tolist())
            require(flat == binding[variant + '_parameter_bits'], 'Parameter bits changed')
            options = ort.SessionOptions()
            options.intra_op_num_threads = options.inter_op_num_threads = 1
            options.graph_optimization_level = ort.GraphOptimizationLevel.ORT_DISABLE_ALL
            session = ort.InferenceSession(str(path), sess_options=options, providers=['CPUExecutionProvider'])
            observations = {}
            for label, witness in search['models'][model]['witnesses'].items():
                exact = list(map(F, witness['input']))
                x = np.asarray([[float(v) for v in exact]], dtype=np.float32)
                require([F(float(v)) for v in x[0]] == exact, 'Input rounding changed the witness')
                y = session.run(None, {session.get_inputs()[0].name: x})[0]
                require(y.shape == (1, 1) and y.dtype == np.float32 and np.isfinite(y).all(),
                        'Unexpected output')
                value = float(y[0,0])
                violation = value < 0.5 if label == 'Above' else value > 0.5
                require(violation, 'Runtime did not reproduce the violation')
                observations[label] = {'input_words': x.view(np.uint32).tolist()[0],
                    'output': value, 'output_word': int(y.view(np.uint32)[0,0]),
                    'violation_observed': violation,
                    'absolute_difference_from_real': str(abs(F(value)-F(witness['output_exact'])))}
                report['execution_count'] += 1
            rows[variant] = {'path': str(path), 'sha256': sha(path),
                             'parameter_bits_match': True, 'observations': observations}
        report['models'][model] = rows
    args.output.write_text(json.dumps(report, indent=2)+'\n')
    print('PASS: eight original/reduced ONNX executions reproduce the violations')


if __name__ == '__main__':
    main()
